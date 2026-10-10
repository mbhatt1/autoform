"""Contracts between the stages of the natural-language autoformalizer.

    repository ──model──────► Translation over AI-written, validated Lean models  (default)
               │                + LeanModel per function (level L0)
               └─translate──► Translation (deep: Joern → Core, `runFunc`)          (--deep)
               ──describe───► EnglishSpec per function     (untrusted)
               ──formalize──► Statement per English property (untrusted, must elaborate)
               ──check──────► CheckResult: bounded kernel + real-runtime evidence
               ──prove──────► ProofResult (kernel re-checked)
               ──emit───────► EmitResult: pytest tests in the target project's tests/autoform_generated/
               ──refine─────► L1: model = deep translation, kernel-checked   (--deep-too)
               ──report─────► report.json / report.md

Every stage reads and writes plain JSON files in one run directory, named below, so a
stage can be rerun, cached or replaced independently. Nothing produced by a language
model is trusted: statements are about the translated program (`runFunc`), their truth
is decided by the Lean kernel, and their plausibility is tested on real executions.
"""
from __future__ import annotations

import json
import re
from dataclasses import asdict, dataclass, field
from pathlib import Path

FILES = {
    'translation': 'translation.json',
    'english': 'english.json',
    'statements': 'statements.json',
    'checks': 'checks.json',
    'proofs': 'proofs.json',
    'emit': 'emit.json',                           # emitted pytest tests, per statement (emit.EmitResult)
    'report': 'report.json',
    'models': 'models.json',
    'deep_translation': 'deep-translation.json',   # --deep-too: the deep Translation
    'refine': 'refine.json',                       # L1 results (refine.L1Result)
    # judge stages (autoform.nl.judge / autoform.nl.repair); only with --judge
    'selection': 'selection.json',                 # ranked, budgeted English properties
    'adjudication': 'adjudication.json',           # counterexample classes, repairs, lineage
    'budget': 'budget.json',                       # skips for budget, per stage
    'decisions': 'decisions.jsonl',                # every judge decision + verifier outcome
    'jevbench': 'jevbench.jsonl',                  # decisions labeled by verifier outcomes
}
JUDGE_FILES = ('selection', 'adjudication', 'budget', 'decisions', 'jevbench')


@dataclass
class Param:
    name: str
    sort: str                 # int | bool | str | float | any  (from the translation)
    integer_type: str = ''    # C/Java widths when known


@dataclass
class FunctionInfo:
    name: str                 # qualified name in the Lean program, e.g. "pkg/mod.py:<module>.f"
    source_name: str          # e.g. "f"
    file: str                 # path relative to the source root
    line: int | None
    params: list              # [Param]
    returns: str              # sort
    hole_free: bool
    holes: list               # hole labels inside the body
    call_closed: bool         # every callee translated (or contracted)
    needs_init: bool          # reads module-level state: must run from the initialized heap
    source: str               # the function's source text
    doc: str = ''
    tests: list = field(default_factory=list)   # [{"location", "text"}] lines calling it
    callers: list = field(default_factory=list)  # qualified names
    # --- model path (autoform.nl.model); defaults describe a plain function ---
    kind: str = 'function'    # function | static | method | property | constructor
    receiver: str = ''        # class of the receiver / constructed object ("pkg.mod.Cls")
    mutates: bool = False     # a method whose model returns the receiver's new state
    samples: list = field(default_factory=list)  # validated input points (pyvalues tags), for check domains
    lean_types: list = field(default_factory=list)  # Lean type of each param in the model (for binders)


@dataclass
class Translation:
    """What the translate stage guarantees to later stages."""
    module: str               # Lean module suffix: Autoform.Generated.<module>
    language: str             # python | c | ...
    lean_root: str            # Lean project dir (lake root) holding the built module
    source_root: str
    source_revision: str      # git sha or tree digest
    ast: str                  # path to the Core AST JSON
    program_const: str        # e.g. "Autoform.Generated.<module>.program"
    init_const: str | None    # Lean term of type `Heap × Ref` with initialized globals, if any
    call_template: str        # Lean term template, see below
    fuel: int
    functions: list           # [FunctionInfo]
    notes: list = field(default_factory=list)
    # call_template: a Lean expression with placeholders {name} (Lean string literal) and
    # {args} (a Lean `List Val` literal) whose type is `EResult`, e.g.
    #   'runFunc Autoform.Generated.M.program 1000 {name} {args}'
    # or an initialized-state form built on `init_const`. Statements must use it.
    # A model Translation (autoform.nl.model) uses 'Autoform.NLModel.M.call {name} {args}';
    # `lean_imports` derives the modules a Lean file must import from the template.


ENTRY_MODULE = re.compile(r'\b(Autoform\.(?:NLModel|NL)\.[A-Za-z0-9_]+)\.call[FH]?\b')


def lean_imports(translation) -> list:
    """The Lean modules a file stating facts about `translation`'s call_template must import.

    An AI model translation names its module in the template (`Autoform.NLModel.<M>.call`)
    and needs nothing else (there is no `Autoform.Generated.<M>` for it); a deep translation
    needs `Autoform.Generated.<module>` plus any initialized entry module its template names
    (`Autoform.NL.<M>.callF`), and any further modules listed under `modules`."""
    tr = asdict(translation) if hasattr(translation, '__dataclass_fields__') else translation
    mods = list(dict.fromkeys(ENTRY_MODULE.findall(tr.get('call_template') or '')))
    if not any(m.startswith('Autoform.NLModel.') for m in mods) and tr.get('module'):
        mods.insert(0, f"Autoform.Generated.{tr['module']}")
    for m in tr.get('modules') or []:
        extra = m if m.startswith('Autoform.') else f'Autoform.Generated.{m}'
        if extra not in mods:
            mods.append(extra)
    return mods


@dataclass
class EnglishProperty:
    id: str                   # stable within the function, e.g. "p1"
    text: str                 # one testable sentence
    kind: str                 # postcondition | precondition | exception | invariant | example
    evidence: list = field(default_factory=list)  # ["docstring", "tests/test_x.py:12", ...]


@dataclass
class EnglishSpec:
    function: str             # FunctionInfo.name
    summary: str
    properties: list          # [EnglishProperty]
    model: str = ''           # which LLM produced it


@dataclass
class Statement:
    """A Lean proposition about the translated function, in a checkable shape.

    lean_prop is the full proposition, e.g.
      ∀ (a b : Int), <pre> → match <call> with | .val (.int r) => r = a + b | _ => False
    binders/pre/post give the SAME statement in pieces so the check stage can evaluate it
    on concrete inputs:
      binders: [{"name": "a", "type": "Int", "val": ".int a"}]    (val: how it is passed)
      pre:  Lean `Bool` expression over binder names ("true" if none)
      post: Lean `Bool` expression over binder names and `r : EResult`
    """
    id: str                   # "<function-sanitized>__<property id>"
    function: str
    property: str             # EnglishProperty.id
    english: str
    lean_prop: str
    binders: list
    pre: str
    post: str
    elaborates: bool = False
    elaboration_log: str = ''
    attempts: int = 0
    # '' : r is the function's result; 'post' : a method statement about the receiver after
    # the call, `r` is `call "<function>#post" args` = `.val (.tuple [result, receiver'])`
    entry: str = ''
    # llm.prompt_key of the formalize prompt that produced this statement (its first attempt);
    # the emit stage writes it into every emitted test's docstring
    prompt_hash: str = ''


def call_name(statement) -> str:
    """The dispatcher name a statement's call uses (see Statement.entry)."""
    st = statement if isinstance(statement, dict) else asdict(statement)
    return st['function'] + ('#post' if st.get('entry') == 'post' else '')


def lean_opens(translation) -> str:
    """`open` line for the Val helpers (vField, vGet, ...) an AI model module exports to
    statements; '' for a deep translation."""
    tr = asdict(translation) if hasattr(translation, '__dataclass_fields__') else translation
    mods = [m for m in ENTRY_MODULE.findall(tr.get('call_template') or '') if m.startswith('Autoform.NLModel.')]
    return f'open {mods[0]} ({" ".join(VAL_HELPERS)})\n' if mods else ''


def model_namespace(translation) -> str:
    """`Autoform.NLModel.<M>` for an AI model translation (its structures' dObj_/eObj_ live
    there); '' for a deep translation."""
    tr = asdict(translation) if hasattr(translation, '__dataclass_fields__') else translation
    mods = [m for m in ENTRY_MODULE.findall(tr.get('call_template') or '') if m.startswith('Autoform.NLModel.')]
    return mods[0] if mods else ''


VAL_HELPERS = ('vField', 'vGet', 'vHas', 'vLen', 'vKeys', 'vElems')


@dataclass
class CheckResult:
    statement: str            # Statement.id
    status: str               # BOUNDED_HOLDS | REFUTED_MODEL | REFUTED_RUNTIME | UNCHECKABLE | ERROR
    domain_size: int = 0
    counterexample: dict | None = None   # {"inputs": {...}, "model": "...", "runtime": "..."}
    runtime_agrees: bool | None = None   # statement's post evaluated on real CPython outputs
    kernel_bounded_proof: bool = False
    detail: str = ''


@dataclass
class ProofResult:
    statement: str
    status: str               # PROVED | FAILED | SKIPPED
    proof: str = ''
    certificate: str | None = None
    axioms: list = field(default_factory=list)
    seconds: float = 0.0
    cost_usd: float = 0.0
    reason: str = ''


@dataclass
class EmitResult:
    """What the emit stage did with one statement (autoform.nl.emit).

    A statement that survived the check stage (BOUNDED_HOLDS, CPython agreed) and, when a
    judge ran, adjudication, becomes pytest tests in the target project: one per concrete
    domain point whose real outcome satisfies pre and post (asserting that outcome), and one
    `hypothesis` property when every binder is Int/Nat/Bool/String and the Python form of
    pre/post agreed with Lean on every concrete point. Every emitted test is run under the
    real interpreter; a failure is recorded here, never dropped."""
    statement: str
    status: str               # EMITTED | NOT_EMITTED | FAILING (emitted, at least one test failed or errored)
    reason: str = ''          # why nothing was emitted
    tests: list = field(default_factory=list)   # [{"name", "file", "kind": concrete|hypothesis, "point", "result", "detail"}]
    points: int = 0           # domain points of the check stage
    points_tested: int = 0    # with an encodable real outcome, pre and post true in Lean: emitted
    points_deduplicated: int = 0    # argument tuples the existing suite already produced (not emitted)
    points_outside_pre: int = 0     # pre false in Lean (vacuous, not emitted)
    points_unencodable: int = 0     # no faithful CPython outcome (timeout, unencodable value)
    hypothesis: str = ''      # 'emitted' or why the property test was not written


@dataclass
class LeanModel:
    """An AI-written Lean model of one function, validated against the real code.

    The model stage emits a Lean module (e.g. Autoform/NLModel/<M>.lean) with a plain Lean
    `def` per function and a dispatcher `call : String → List Val → EResult` that decodes
    arguments, runs the def and encodes the result (a raised exception is
    `.exn (.str "<ExceptionClass>")`). It then writes a `Translation` whose call_template is
    `Autoform.NLModel.<M>.call {name} {args}`, so formalize/check/prove run unchanged.

    Trust levels (reported, never merged):
      L0  proofs are about this model; the model agreed with the real code on every one of
          `tests_run` inputs and with an independent second translation;
      L1  additionally proved equal to the deep (Joern → Core) translation of the function.
    """
    function: str             # FunctionInfo.name
    lean_name: str            # the plain def, e.g. "Autoform.NLModel.M.add"
    lean_source: str          # the def(s) as written into the module
    signature: str            # Lean type of the plain def
    status: str               # VALIDATED | DISAGREES | UNTESTABLE | FAILED
    tests_run: int = 0
    disagreements: list = field(default_factory=list)  # [{"inputs", "model", "runtime"}]
    second_translation: str = 'not_run'                # agrees | disagrees | not_run
    repairs: int = 0
    level: str = 'none'       # none | L0 | L1
    notes: str = ''


def entry_imports(translation) -> str:
    """`import` lines for the entry modules a call_template names beyond the generated
    module: `Autoform.NL.<M>` (initialized entry) or `Autoform.NLModel.<M>` (AI model)."""
    import re
    tmpl = (translation or {}).get('call_template', '') if isinstance(translation, dict) else \
        getattr(translation, 'call_template', '')
    mods = dict.fromkeys(re.findall(r'\b(Autoform\.(?:NLModel|NL)\.[A-Za-z0-9_]+)\.call[FH]?\b', tmpl or ''))
    return ''.join(f'import {m}\n' for m in mods)


def dump(obj, path: Path):
    def conv(o):
        if hasattr(o, '__dataclass_fields__'):
            return asdict(o)
        raise TypeError(type(o))
    Path(path).write_text(json.dumps(obj, indent=1, default=conv, ensure_ascii=False))


def load(path: Path):
    return json.loads(Path(path).read_text())
