from weakref import WeakValueDictionary

import pymona


def test_basic() -> None:
    b1 = pymona.BoolIdent("b1")
    b2 = pymona.BoolIdent("b2")
    formula = pymona.m_and(b1, pymona.m_not(b2))
    model = pymona.solve(formula)
    assert model is not None
    assert model[b1]
    assert not model[b2]
    assert model.bools == {"b1": True, "b2": False}


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
    assert model.ints == {"x": model[x], "y": model[y], "z": model[z]}


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
    assert model.sets == {"s": model[s]}


def test_pred_decorator() -> None:
    c = pymona.ElementIdent("c")
    x = pymona.ElementIdent("x")
    y = pymona.ElementIdent("y")

    @pymona.to_pred
    def a_between_b_and_c2(
        a: pymona.ElementRef, b: pymona.ElementRef
    ) -> pymona.BoolRef:
        return pymona.m_and(b < a, a < c)

    formula = pymona.m_and(3 < c, c < 7, a_between_b_and_c2(x, y), 0 < y)

    model = pymona.solve(formula)

    assert model is not None

    assert model[y] < model[x] < model[c]


def test_weak_pred_cache() -> None:
    x = pymona.ElementIdent("x")
    y = pymona.ElementIdent("y")
    cache: WeakValueDictionary[str, pymona.PredRef] = WeakValueDictionary()
    cache["pred"] = pymona.pred("pred", (x, y), x < y)
    assert len(cache) == 0


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


def test_set_operations() -> None:
    p = pymona.SetIdent("p")
    q = pymona.SetIdent("q")

    assert (model := pymona.solve(pymona.eq(p - q, pymona.m_set(2, 3)))) is not None
    assert model[p] - model[q] == {2, 3}

    assert (model := pymona.solve(pymona.eq(p & q, pymona.m_set(2, 3)))) is not None
    assert model[p] & model[q] == {2, 3}

    formula = pymona.m_and(
        pymona.m_not(pymona.is_empty(p)),
        pymona.m_not(pymona.is_empty(q)),
        pymona.neq(p, q),
        pymona.eq(p | q, pymona.m_set(2, 3)),
    )
    assert (model := pymona.solve(formula)) is not None
    assert model[p] | model[q] == {2, 3}
