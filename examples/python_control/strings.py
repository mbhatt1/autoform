"""`str` methods, membership and `list(iterable)`, end to end (tests/test_python_str_methods.py).

Every subject takes one string and returns a value the native comparison can print
(int, bool, str, or a list/tuple of them).
"""


def classify(uri):
    lowered = (uri or "").lower()
    if not lowered.startswith("s3://"):
        return "local"
    if "overrides" in lowered:
        return "override"
    if "data-sources" in lowered:
        return "live"
    return "other"


def lead_nodes(node):
    if ":" not in node:
        return 0
    level, location = node.split(":", 1)
    return len(level.upper()) * 100 + len(location)


def words(text):
    parts = text.split()
    parts.append("end")
    return "-".join(parts)


def fields(text):
    return text.strip().split(",")


def cleaned(text):
    return text.strip(" .").replace("a", "o").rstrip("x")


def suffix(text):
    return (text.endswith(("x", "yz")), text.lstrip().startswith(""), "" in text)


def copied(text):
    chars = list(text)
    alias = list(chars)
    alias.append("!")
    return (len(chars), len(alias), "".join(alias))


def shortfall(text):
    supply = list([len(text), 1, 2])
    supply[0] = supply[0] + 1
    total = 0
    for t in range(3):
        total += supply[t]
        if total > 5:
            return t
    return -1


def member(text):
    keys = {"a": 1, "b": 2}
    return (text in keys, text in ["x", "a"], text[:1] in "abc")


def payload_method(text):
    try:
        raise KeyError(text)
    except KeyError as error:
        return error.lower()
