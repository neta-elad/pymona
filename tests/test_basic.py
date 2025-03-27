import pymona


def test_basic() -> None:
    b1 = pymona.BoolIdent("b1")
    b2 = pymona.BoolIdent("b2")
    formula = pymona.m_and(b1, pymona.m_not(b2))
    model = pymona.solve(formula)
    assert model is not None
    assert model[b1]
    assert not model[b2]


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
    assert model[x] < model[y] < model[z]
    assert model[x] > 4
    assert model[z] < 10


def test_predicate() -> None:
    a = pymona.ElementIdent("a")
    b = pymona.ElementIdent("b")
    c = pymona.ElementIdent("c")
    x = pymona.ElementIdent("x")
    y = pymona.ElementIdent("y")
    s = pymona.SetIdent("s")

    a_between_b_and_c = pymona.m_and(b < a, a < c)

    pred = pymona.pred("a_between_b_and_c", (a, b), a_between_b_and_c)

    formula = pymona.m_and(
        pred(x, y),
        c < 7,
        pymona.lt(5, c),
        pymona.lt(20, a),
        a < b,
        pymona.m_in(x, s),
        s(y),
    )

    model = pymona.solve(formula)

    assert model is not None

    assert model[y] < model[x] < model[c]
    assert model[x] in model[s]
    assert model[y] in model[s]


def test_sub() -> None:
    s1 = pymona.SetIdent("s1")
    s2 = pymona.SetIdent("s2")
    model = pymona.solve(
        pymona.m_and(
            pymona.m_in(0, s1),
            s2 <= s1,
        )
    )

    assert model is not None
    assert 0 in model[s1]
    assert model[s2] <= model[s1]


def test_addition() -> None:
    x = pymona.ElementIdent("x")
    y = pymona.ElementIdent("y")
    model = pymona.solve(pymona.m_and(5 + x > y - 3, y > 13, x < y))
    assert model is not None
    assert model[x] > 5


def test_eq() -> None:
    x = pymona.ElementIdent("x")
    model = pymona.solve(pymona.eq(x, 5))
    assert model is not None
    assert model[x] == 5


def test_set() -> None:
    s = pymona.SetIdent("s")
    model = pymona.solve(pymona.eq(s, pymona.m_set(1, 2, 3)))
    assert model is not None
    assert {1, 2, 3} == model[s]


def test_min_max() -> None:
    x = pymona.ElementIdent("x")
    y = pymona.ElementIdent("y")
    z = pymona.ElementIdent("z")
    a = pymona.ElementIdent("a")
    s = pymona.SetIdent("s")
    model = pymona.solve(
        pymona.m_and(
            pymona.eq(x, pymona.min(1, a, 4)),
            pymona.eq(y, pymona.max(1, a, 4)),
            pymona.eq(a, pymona.max(6)),
            s(x),
            s(y),
            pymona.eq(z, pymona.max(s)),
        )
    )
    assert model is not None
    assert model[x] == 1
    assert model[y] == 6
    assert model[z] == model[y]


def test_int() -> None:
    assert pymona.solve(pymona.eq(pymona.m_int(5), pymona.ElementInt(5))) is not None
