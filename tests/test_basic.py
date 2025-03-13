import pymona


def test_basic() -> None:
    b1 = pymona.BoolIdent("b1")
    b2 = pymona.BoolIdent("b2")
    formula = pymona.m_and(b1, pymona.m_not(b2))
    model = pymona.solve(formula)
    assert model is not None
    assert model["b1"]
    assert not model["b2"]


def test_ints() -> None:
    x = pymona.ElementIdent("x")
    y = pymona.ElementIdent("y")
    z = pymona.ElementIdent("z")
    formula = pymona.m_and(
        x < y,
        y < z,
        z < 10,
        x > 4,
    )
    model = pymona.solve(formula)
    assert model is not None
    x_val = model["x"]
    y_val = model["y"]
    z_val = model["z"]

    assert isinstance(x_val, int)
    assert isinstance(y_val, int)
    assert isinstance(z_val, int)

    assert x_val < y_val < z_val
    assert x_val > 4
    assert z_val < 10


def test_predicate() -> None:
    a = pymona.ElementIdent("a")
    b = pymona.ElementIdent("b")
    c = pymona.ElementIdent("c")
    x = pymona.ElementIdent("x")
    y = pymona.ElementIdent("y")
    s = pymona.SetIdent("s")

    a_between_b_and_c = pymona.m_and(
        b < a,
        a < c
    )

    pred = pymona.pred("a_between_b_and_c", (a, b), a_between_b_and_c)

    model = pymona.solve(pymona.m_and(
        pred(x, y),
        c < 7,
        pymona.lt(5, c),
        pymona.lt(20, a),
        a < b,
        pymona.m_in(x, s),
        pymona.m_in(y, s),
    ))

    assert model is not None

    c_val = model["c"]
    x_val = model["x"]
    y_val = model["y"]
    s_val = model["s"]

    assert isinstance(c_val, int)
    assert isinstance(x_val, int)
    assert isinstance(y_val, int)
    assert isinstance(s_val, set)

    assert y_val < x_val < c_val
    assert x_val in s_val
    assert y_val in s_val


def test_addition() -> None:
    x = pymona.ElementIdent("x")
    model = pymona.solve(x + 5 > 10)
    assert model is not None
    x_val = model["x"]
    assert isinstance(x_val, int)
    assert x_val > 5


def test_eq() -> None:
    x = pymona.ElementIdent("x")
    model = pymona.solve(pymona.eq(x, 5))
    assert model is not None
    x_val = model["x"]
    assert isinstance(x_val, int)
    assert x_val == 5
