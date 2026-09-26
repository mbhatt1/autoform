"""Compile suspended Python generator frames to ordinary Core heap operations.

This is a translation pass, not a host-language generator used by the interpreter.
Every resume runs the same fuel-bounded, kernel-reducible Core semantics as other code.
The source body remains available for coverage analysis; frame helper functions are
auxiliary definitions, excluded from the population of source functions.
"""
if __package__:
    from .ast_tools import rewrite_json, walk
else:
    from ast_tools import rewrite_json, walk


def node(kind, **fields):
    return {"k": kind, **fields}


def seq(*statements):
    out = node("skip")
    for statement in reversed(statements):
        out = node("seq", a=statement, b=out)
    return out


def name(value):
    return node("name", v=value)


def string(value):
    return node("str", v=value)


def integer(value):
    return node("int", v=str(value))


def field(value):
    return node("field", a=name("self"), f=value)


def set_field(key, value):
    return node("setField", r=name("self"), f=key, v=value)


def compare(a, b):
    return node("binop", op="==", a=a, b=b)


def raise_class(value):
    return node("raise", e=node("unop", op="py:exception:" + value,
                               a=node("tupleE", items=[])))


def transform(value, rewrite):
    """Postorder JSON rewrite without using the Python stack for long seq chains."""
    return rewrite_json(value, lambda original, copied: rewrite(copied))


class UnsupportedGenerator(ValueError):
    pass


class FrameCompiler:
    def __init__(self, function):
        self.function = dict(function)
        self.source_body = function["body"]
        metadata = function["generator"]
        self.locals = set(metadata["locals"])
        self.captures = metadata["captures"]
        self.parameters = metadata["parameters"]
        self.locals.update(self.parameters)
        self.cls = "<generator>"
        self.resume_name = "<generator>." + function["name"] + ".<resume>"
        self.nodes = {}
        self.counter = 0
        self.depth = 0
        for item in walk(self.source_body):
            kind = item.get("k")
            if kind in ("assign", "forIn", "tryCatch"):
                self.locals.add(item["x"])
            if kind == "yieldS" and item.get("target"):
                self.locals.add(item["target"])
            if kind in ("closure", "classClosure"):
                raise UnsupportedGenerator("generator:closure-frame")
        if metadata.get("async"):
            raise UnsupportedGenerator("generator:async")
        if self.captures:
            # A suspended free variable must keep the enclosing cell, not a snapshot.
            raise UnsupportedGenerator("generator:free-variable-cells")

    def fresh_local(self):
        value = "<generator-temp>" + str(len(self.locals))
        self.locals.add(value)
        return value

    def local_set(self, key, value):
        return node("setIndex", r=field("<locals>"), i=string(key), v=value)

    def expression(self, value):
        def rewrite(item):
            if item.get("k") == "name" and item["v"] in self.locals:
                result = node("mcall", recv=name("self"), m="__read_local__", args=[string(item["v"])])
                if "pythonTruthCache" in item:
                    result["pythonTruthCache"] = item["pythonTruthCache"]
                return result
            if item.get("k") == "call" and item["f"] in self.locals:
                return node("callV", f=self.expression(name(item["f"])), args=item["args"])
            if item.get("k") in ("yieldS", "yieldFromS"):
                raise UnsupportedGenerator("generator:yield-expression-shape")
            return item
        return transform(value, rewrite)

    def statement(self, value):
        if value["k"] == "assign":
            return self.local_set(value["x"], self.expression(value["e"]))
        if value["k"] == "del" and value["x"] in self.locals:
            return seq(node("exprS", e=self.expression(name(value["x"]))),
                       node("delIndex", a=field("<locals>"), i=string(value["x"])))
        return self.expression(value)

    def reserve(self):
        self.counter += 1
        if self.counter > 4096:
            raise UnsupportedGenerator("generator:control-graph-size")
        return self.counter

    def goto(self, target):
        return set_field("<pc>", integer(target))

    def put(self, body, exceptional, index=None):
        index = self.reserve() if index is None else index
        self.nodes[index] = node("tryCatch", body=body, x="<caught>",
                                 handler=seq(set_field("<exception>", name("<caught>")),
                                             self.goto(exceptional)))
        return index

    def compile(self, statement, normal, breaking, continuing, returning, exceptional):
        self.depth += 1
        try:
            if self.depth > 128:
                raise UnsupportedGenerator("generator:control-graph-depth")
            return self.compile_node(statement, normal, breaking, continuing, returning, exceptional)
        finally:
            self.depth -= 1

    def compile_node(self, statement, normal, breaking, continuing, returning, exceptional):
        kind = statement["k"]
        if kind == "seq":
            pending = [statement]
            statements = []
            while pending:
                item = pending.pop()
                if item["k"] == "seq":
                    pending.extend((item["b"], item["a"]))
                else:
                    statements.append(item)
            for item in reversed(statements):
                normal = self.compile(item, normal, breaking, continuing, returning, exceptional)
            return normal
        if kind == "skip":
            return normal
        if kind == "ifte":
            yes = self.compile(statement["t"], normal, breaking, continuing, returning, exceptional)
            no = self.compile(statement["e"], normal, breaking, continuing, returning, exceptional)
            return self.put(node("ifte", c=self.expression(statement["c"]),
                                 t=self.goto(yes), e=self.goto(no)), exceptional)
        if kind == "loop":
            head = self.reserve()
            body = self.compile(statement["body"], head, normal, head, returning, exceptional)
            return self.put(node("ifte", c=self.expression(statement["c"]),
                                 t=self.goto(body), e=self.goto(normal)), exceptional, head)
        if kind == "brk":
            return breaking
        if kind == "cont":
            return continuing
        if kind == "ret":
            return self.put(seq(set_field("<return>", self.expression(statement["e"])),
                                self.goto(returning)), exceptional)
        if kind == "yieldS":
            resume = normal
            if statement.get("target"):
                resume = self.put(seq(self.local_set(statement["target"], field("<sent>")),
                                      self.goto(normal)), exceptional)
            # Evaluate the yielded value before changing the saved continuation.
            return self.put(seq(node("assign", x="<yielded>", e=self.expression(statement["e"])),
                                self.goto(resume), set_field("<handler>", integer(exceptional)),
                                set_field("<state>", integer(1)), node("ret", e=name("<yielded>"))), exceptional)
        if kind == "tryCatch":
            handler = self.compile(statement["handler"], normal, breaking, continuing, returning, exceptional)
            bind = self.put(seq(self.local_set(statement["x"], field("<exception>")), self.goto(handler)), exceptional)
            return self.compile(statement["body"], normal, breaking, continuing, returning, bind)
        if kind == "tryFinally":
            final = statement["fin"]
            def cleanup(target):
                return self.compile(final, target, breaking, continuing, returning, exceptional)
            saved = self.fresh_local()
            restore = self.put(seq(set_field("<exception>", self.expression(name(saved))),
                                   self.goto(exceptional)), exceptional)
            unwind = cleanup(restore)
            exceptional_final = self.put(seq(self.local_set(saved, field("<exception>")),
                                              self.goto(unwind)), exceptional)
            return self.compile(statement["body"], cleanup(normal), cleanup(breaking),
                                cleanup(continuing), cleanup(returning), exceptional_final)
        if kind == "forIn":
            iterator = self.fresh_local()
            head = self.reserve()
            body = self.compile(statement["body"], head, normal, head, returning, exceptional)
            exhausted = self.put(node("ifte", c=compare(field("<exception>"), string("StopIteration")),
                                      t=self.goto(normal), e=self.goto(exceptional)), exceptional)
            self.put(seq(self.local_set(statement["x"], node("call", f="<python-next>", args=[self.expression(name(iterator))])),
                         self.goto(body)), exhausted, head)
            source = self.expression(statement["e"])
            initial = source if statement.get("iteratorReady") else node("call", f="<python-iter>", args=[source])
            return self.put(seq(self.local_set(iterator, initial),
                                self.goto(head)), exceptional)
        if kind in ("yieldFromS", "breakBlock"):
            raise UnsupportedGenerator("generator:" + kind)
        return self.put(seq(self.statement(statement), self.goto(normal)), exceptional)

    def helper(self, method, body, parameters=(), vararg=None, kwarg=None):
        value = {"name": "<autoform>." + self.cls + "." + method,
                 "file": "", "sourceOwner": "<generator-runtime>",
                 "params": list(parameters), "body": body,
                 "pythonSignature": {"isMethod": True, "positionalOnly": list(parameters),
                                     "keywordOnly": [], "required": list(parameters)}}
        if vararg:
            value["vararg"] = vararg
            value["params"].append(vararg)
        if kwarg:
            value["kwarg"] = kwarg
            value["params"].append(kwarg)
        return value

    def finish(self):
        completed, failed, escaped = -1, -2, -3
        entry = self.compile(self.source_body, completed, escaped, escaped, completed, failed)
        # Terminals are outside the per-instruction catches. An unexpected
        # StopIteration from the body becomes RuntimeError (PEP 479).
        complete = seq(set_field("<state>", integer(3)),
                       node("ifte", c=compare(field("<return>"), node("unit")),
                            t=raise_class("StopIteration"),
                            e=node("holeS", label="generator:return-value")))
        fail = seq(set_field("<state>", integer(3)),
                   node("ifte", c=compare(field("<exception>"), string("StopIteration")),
                        t=raise_class("RuntimeError"), e=node("raise", e=field("<exception>"))))
        terminal = node("ifte", c=compare(field("<pc>"), integer(completed)), t=complete,
                        e=node("ifte", c=compare(field("<pc>"), integer(failed)), t=fail,
                               e=node("holeS", label="generator:invalid-continuation")))
        dispatch = terminal
        for index in sorted(self.nodes, reverse=True):
            dispatch = node("ifte", c=compare(field("<pc>"), integer(index)), t=self.nodes[index], e=dispatch)
        run = seq(set_field("<sent>", name("value")), set_field("<state>", integer(2)),
                  node("loop", c=node("bool", v=True), body=dispatch))
        resume = node("ifte", c=compare(field("<state>"), integer(3)), t=raise_class("StopIteration"),
                      e=node("ifte", c=compare(field("<state>"), integer(2)), t=raise_class("ValueError"),
                             e=node("ifte", c=node("binop", op="&&", a=compare(field("<state>"), integer(0)),
                                                   b=node("binop", op="!=", a=name("value"), b=node("unit"))),
                                    t=raise_class("TypeError"), e=run)))
        read_local = node("tryCatch", body=node("ret", e=node("index", a=field("<locals>"), b=name("key"))),
                          x="<lookup-error>", handler=node("ifte", c=compare(name("<lookup-error>"), string("KeyError")),
                              t=raise_class("UnboundLocalError"), e=node("raise", e=name("<lookup-error>"))))
        # Share protocol methods across all frames. Duplicating them per source
        # function makes the interpreter's method lookup and kernel proofs quadratic
        # in the number of generators. Only the resume body is function-specific.
        resume_function = self.helper("<resume>", resume, ("self", "value"))
        resume_function.update(name=self.resume_name, sourceOwner=self.function["name"])
        resume_function["pythonSignature"]["isMethod"] = False
        helpers = [self.helper("__init__", node("skip")), self.helper("__iter__", node("ret", e=name("self"))),
                   self.helper("__read_local__", read_local, ("key",)),
                   self.helper("__next__", node("ret", e=node("callV", f=field("<resume>"), args=[name("self"), node("unit")]))),
                   self.helper("send", node("ret", e=node("callV", f=field("<resume>"), args=[name("self"), name("value")])), ("value",)),
                   self.helper("close", node("holeS", label="generator:close")),
                   self.helper("throw", node("holeS", label="generator:throw"), vararg="args", kwarg="kwargs"),
                   resume_function]
        frame = "<generator-frame>"
        def initialize(key, value):
            return node("setField", r=name(frame), f=key, v=value)
        initial_names = sorted(set(self.parameters + self.captures))
        self.function["body"] = seq(node("assign", x=frame, e=node("alloc", cls=self.cls, args=[])),
            initialize("<locals>", node("dictE", pairs=[[string(key), name(key)] for key in initial_names])),
            initialize("<resume>", node("fnref", v=self.resume_name)),
            initialize("<pc>", integer(entry)), initialize("<state>", integer(0)),
            initialize("<return>", node("unit")), node("ret", e=name(frame)))
        self.function["generatorHelpers"] = helpers
        # This source view is used only for coverage, never to execute a yield as a return.
        def source_view(value):
            if value.get("k") == "yieldS":
                return node("exprS", e=value["e"])
            if value.get("k") == "ret" and value["e"].get("k") != "unit":
                return seq(node("exprS", e=value["e"]),
                           node("holeS", label="generator:return-value"))
            return value
        self.function["analysisBody"] = transform(self.source_body, source_view)
        return self.function


def lower_expressions(function):
    """Turn generator expressions into auxiliary factories without eager consumption.

    The first iterator is made as the factory argument, in the enclosing environment.
    Its frame starts with that iterator already prepared, so resumption does not call
    __iter__ a second time. Free variables still require cells and are refused.
    """
    factories, analysis = [], []

    def rewrite(value):
        if value.get("k") != "genExpr":
            return value
        metadata = value.get("generator")
        if not isinstance(metadata, dict):
            return node("hole", label="genexpr:source-metadata")
        if metadata.get("captures"):
            return node("hole", label="genexpr:free-variable-cells")
        if metadata.get("async"):
            return node("hole", label="genexpr:async")
        source = value.get("body", {})
        if source.get("k") != "forIn":
            return node("hole", label="genexpr:outer-loop-shape")
        sink = value.get("sink")
        yields = 0

        def suspend(item):
            nonlocal yields
            expression = item.get("e", {})
            if (item.get("k") == "exprS" and expression.get("k") == "mcall"
                    and expression.get("m") == "append"
                    and expression.get("recv") == name(sink)
                    and len(expression.get("args", [])) == 1):
                yields += 1
                return node("yieldS", e=expression["args"][0])
            return item

        body = transform(source, suspend)
        if yields != 1 or any(item == name(sink) for item in walk(body)):
            return node("hole", label="genexpr:yield-shape")
        iterator = "<genexpr-iterator>"
        body.update(e=name(iterator), iteratorReady=True)
        factory_name = function["name"] + ".<genexpr>" + str(len(factories))
        factory = {"name": factory_name, "file": function.get("file", ""),
                   "sourceOwner": function["name"], "params": [iterator],
                   "body": body, "generator": {**metadata, "parameters": [iterator]},
                   "pythonSignature": {"isMethod": False, "positionalOnly": [iterator],
                                       "keywordOnly": [], "required": [iterator]}}
        try:
            compiled = FrameCompiler(factory).finish()
        except UnsupportedGenerator as error:
            return node("hole", label=str(error))
        factories.extend(compiled.pop("generatorHelpers"))
        factories.append(compiled)
        analysis.append(compiled["analysisBody"])
        return node("call", f=factory_name,
                    args=[node("call", f="<python-iter>", args=[source["e"]])])

    if not any(item.get("k") == "genExpr" for item in walk(function["body"])):
        return function, [], []
    return {**function, "body": transform(function["body"], rewrite)}, factories, analysis


def lower_generators(functions):
    lowered = []
    helpers = {}
    for function in functions:
        function, expression_helpers, expression_analysis = lower_expressions(function)
        if not function.get("generator"):
            if any(item.get("k") in ("yieldS", "yieldFromS") for item in walk(function["body"])):
                function = dict(function)
                function["body"] = node("holeS", label="generator:missing-metadata")
        elif function["body"].get("k") != "holeS":
            try:
                function = FrameCompiler(function).finish()
            except UnsupportedGenerator as error:
                function = {**function, "body": node("holeS", label=str(error))}
        candidates = expression_helpers + function.get("generatorHelpers", [])
        if candidates:
            function = dict(function)
            unique_helpers = []
            for helper in candidates:
                previous = helpers.get(helper["name"])
                if previous is None:
                    helpers[helper["name"]] = helper
                    unique_helpers.append(helper)
                elif previous != helper:
                    raise ValueError("conflicting generator helper: " + helper["name"])
            function["generatorHelpers"] = unique_helpers
        if expression_analysis:
            function = {**function, "analysisBody": seq(
                function.get("analysisBody", function["body"]), *expression_analysis)}
        lowered.append(function)
    return lowered


def analysis_functions(functions):
    """Source population with the same analyzed bodies as the rendered Lean ledger.

    Input is the exported AST, before lowering. Helpers stay outside the population;
    lowering refusals and suspended body operations remain visible to coverage tools.
    This view is for analysis and source-runtime sampling, never execution/rendering.
    """
    return [{**function, "body": function.get("analysisBody", function["body"])}
            for function in lower_generators(functions)]
