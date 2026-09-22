"""Compile suspended Python generator frames to ordinary Core heap operations.

This is a translation pass, not a host-language generator used by the interpreter.
Every resume runs the same fuel-bounded, kernel-reducible Core semantics as other code.
The source body remains available for coverage analysis; frame helper functions are
auxiliary definitions, excluded from the population of source functions.
"""
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


def walk(value):
    pending = [value]
    while pending:
        current = pending.pop()
        if isinstance(current, dict):
            yield current
            pending.extend(current.values())
        elif isinstance(current, list):
            pending.extend(current)


def transform(value, rewrite):
    """Postorder JSON rewrite without using the Python stack for long seq chains."""
    root = [None]
    pending = [(value, root, 0, False)]
    while pending:
        current, parent, key, done = pending.pop()
        if done:
            parent[key] = rewrite(parent[key])
        elif isinstance(current, dict):
            copied = {}
            parent[key] = copied
            pending.append((None, parent, key, True))
            pending.extend((item, copied, name, False) for name, item in reversed(list(current.items())))
        elif isinstance(current, list):
            copied = [None] * len(current)
            parent[key] = copied
            pending.extend((item, copied, i, False) for i, item in reversed(list(enumerate(current))))
        else:
            parent[key] = current
    return root[0]


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
                return node("mcall", recv=name("self"), m="__read_local__", args=[string(item["v"])])
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
            self.put(seq(self.local_set(statement["x"], node("call", f="next", args=[self.expression(name(iterator))])),
                         self.goto(body)), exhausted, head)
            return self.put(seq(self.local_set(iterator, node("call", f="iter", args=[self.expression(statement["e"])])),
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


def lower_generators(functions):
    lowered = []
    helpers = {}
    for function in functions:
        if not function.get("generator"):
            if any(item.get("k") in ("yieldS", "yieldFromS") for item in walk(function["body"])):
                function = dict(function)
                function["body"] = node("holeS", label="generator:missing-metadata")
            lowered.append(function)
            continue
        if function["body"].get("k") == "holeS":
            lowered.append(function)
            continue
        try:
            compiled = FrameCompiler(function).finish()
            unique_helpers = []
            for helper in compiled["generatorHelpers"]:
                previous = helpers.get(helper["name"])
                if previous is None:
                    helpers[helper["name"]] = helper
                    unique_helpers.append(helper)
                elif previous != helper:
                    raise ValueError("conflicting generator helper: " + helper["name"])
            compiled["generatorHelpers"] = unique_helpers
            lowered.append(compiled)
        except UnsupportedGenerator as error:
            refused = dict(function)
            refused["body"] = node("holeS", label=str(error))
            lowered.append(refused)
    return lowered
