import pymona

from pymona.strings import (
    Alphabet,
    Context,
    append,
    contains,
    cut_last,
    ends_in,
    ite,
    replace_at,
    starts_with,
    str_empty,
    str_eq,
    str_prefix,
    substr,
)


def test_empty() -> None:
    context = Context.default()
    s = context.var("s")

    formula = pymona.m_not(str_empty(s))

    solver = context.solver()

    assert solver.check(formula)
    model = solver.model()
    assert model is not None
    assert model[s] != ""


def test_literal_eq() -> None:
    context = Context.default()
    s = context.var("s")

    formula = str_eq(s, "101")

    solver = context.solver()

    assert solver.check(formula)
    model = solver.model()
    assert model is not None
    assert model[s] == "101"


def test_var_eq() -> None:
    context = Context.default()
    s1 = context.var("s1")
    s2 = context.var("s2")

    formula = pymona.m_and(str_eq(s1, s2), pymona.m_not(str_empty(s1)))

    solver = context.solver()

    assert solver.check(formula)
    model = solver.model()
    assert model is not None
    assert model[s1] != ""
    assert model[s1] == model[s2]


def test_start_with_ends_in_contains() -> None:
    alphabet = Alphabet(("0", "1", "2"))
    context = Context(alphabet)
    s = context.var("s")

    formula = pymona.m_and(starts_with("0")(s), ends_in("1")(s), contains("2")(s))
    solver = context.solver()
    assert solver.check(formula)
    model = solver.model()
    assert model is not None

    assert model[s].startswith("0")
    assert model[s].endswith("1")
    assert "2" in model[s]


def test_str_prefix() -> None:
    context = Context.default()
    s = context.var("s")

    formula = pymona.m_and(str_prefix("101", s), pymona.m_not(str_eq("101", s)))

    solver = context.solver()

    assert solver.check(formula)
    model = solver.model()
    assert model is not None
    assert model[s].startswith("101") and model[s] != "101"


def test_concat() -> None:
    context = Context.default()
    s1 = context.var("s1")
    s2 = context.var("s2")

    formula = pymona.m_and(
        str_eq(s1, "101"),
        str_eq(s2, append(s1, "100")),
    )

    solver = context.solver()
    assert solver.check(formula)
    model = solver.model()
    assert model is not None
    assert model[s2] == "101100"


def test_cut_last() -> None:
    context = Context.default()
    s1 = context.var("s1")
    s2 = context.var("s2")

    formula = pymona.m_and(
        str_eq(s1, "101"),
        str_eq(s2, cut_last(s1)),
    )
    solver = context.solver()
    assert solver.check(formula)
    model = solver.model()
    assert model is not None
    assert model[s2] == "10"


def test_ite() -> None:
    b = pymona.BoolIdent("b")
    b2 = pymona.BoolIdent("b2")
    context = Context.default()
    s = context.var("s")

    formula = pymona.m_and(
        pymona.m_not(b),
        b2,
        str_eq(s, ite(b, context.literal("101"), context.literal("010"))),
    )
    solver = context.solver()
    assert solver.check(formula)
    model = solver.model()
    assert model is not None
    assert not model[b]
    assert model[b2]
    assert model[s] == "010"


def test_replace_at() -> None:
    context = Context.default()
    s = context.var("s")
    formula = str_eq(s, replace_at(context.literal("101"), "10", 1))

    solver = context.solver()
    assert solver.check(formula)
    model = solver.model()
    assert model is not None
    assert model[s] == "110"


def test_substr() -> None:
    context = Context.default()
    s = context.var("s")
    formula = str_eq(s, substr(context.literal("1011"), 1, 2))

    solver = context.solver()
    assert solver.check(formula)
    model = solver.model()
    assert model is not None
    assert model[s] == "01"
