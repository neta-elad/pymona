from typing import cast

import z3

from pymona.strings.z3_api import (
    PyMONAZ3Solver,
    get_alphabet,
    z3_cut_last,
    z3_ends_in,
    z3_replace_at,
    z3_starts_with,
)


def test_append() -> None:
    string = "100"
    appended_string = "101"

    val = z3.StringVal(string)
    test = z3.String("test")
    solver = PyMONAZ3Solver()
    solver.add(test == val + z3.StringVal(appended_string))
    solver.add(z3.Implies(val != test, z3.Bool("different")))

    assert solver.check() == z3.sat
    model = solver.model()
    assert model is not None

    assert model.eval_expr("test").eq(z3.StringVal(string + appended_string))
    assert model.eval_bool("different")


def test_substr() -> None:
    string = "10010"
    test = z3.String("test")
    test2 = z3.String("test2")
    solver = PyMONAZ3Solver()
    solver.add(test == z3.SubSeq(z3.StringVal(string), z3.IntVal(1), z3.IntVal(3)))
    solver.add(test2 == z3.SubSeq(z3.StringVal(string), z3.IntVal(1), z3.IntVal(100)))
    assert solver.check() == z3.sat
    model = solver.model()
    assert model is not None

    assert model.eval_expr("test").eq(z3.StringVal("001"))
    assert model.eval_expr("test2").eq(z3.StringVal("0010"))


def test_formula() -> None:
    solver = PyMONAZ3Solver()
    add_l = z3.Bool("add_l")
    add_r = z3.Bool("add_r")
    solver.add(z3.Xor(add_l, add_r))
    t, s = z3.Strings("t s")
    x = z3.String("x")
    y = z3.String("y")
    z = z3.String("z")
    val = z3.StringVal("0101")
    solver.add(
        z3.ForAll(
            x,
            z3.ForAll(
                y,
                z3.ForAll(
                    z,
                    z3.Implies(
                        z3.And(z3.PrefixOf(x, y), z3.PrefixOf(y, z)), z3.PrefixOf(x, z)
                    ),
                ),
            ),
        )
    )
    solver.add(
        z3.ForAll(
            s,
            z3.Exists(
                t,
                z3.And(
                    z3.Implies(add_l, t == s + "0"),
                    z3.Implies(add_r, t == s + "1"),
                ),
            ),
        )
    )
    solver.add(
        z3.And(
            z3.Implies(add_l, x == val + "0"),
            z3.Implies(add_r, x == val + "1"),
        )
    )
    solver.add(
        z3.And(
            z3.Implies(add_l, y == x + "0"),
            z3.Implies(add_r, y == x + "1"),
        )
    )
    solver.add(x == z3.StringVal("01010"))
    assert solver.check() == z3.sat
    model = solver.model()
    assert model is not None
    assert model.model.bools["add_l"]
    assert not model.model.bools["add_r"]
    assert model.model.strings["y"] == "010100"


def test_regex() -> None:
    regex = z3.Concat(
        z3.Re("1"),
        z3.Intersect(z3.Complement(z3.Plus(z3.Re("0"))), z3.Complement(z3.Re(""))),
    )

    solver = PyMONAZ3Solver()

    s = z3.String("s")
    assert solver.check(z3.InRe(s, regex)) == z3.sat

    formula = z3.Not(
        z3.ForAll(s, z3.Implies(z3.InRe(s, regex), z3.InRe(s + "0", regex)))
    )
    assert solver.check(formula) == z3.unsat


def test_string_regex() -> None:
    expected_string = "1010"
    regex = z3.Re(expected_string)
    solver = PyMONAZ3Solver()

    s = z3.String("s")
    assert solver.check(z3.InRe(s, regex)) == z3.sat
    model = solver.model()
    assert model is not None
    assert model.eval_expr("s").as_string() == expected_string


def test_special_case_regex() -> None:
    s = z3.String("s")
    solver = PyMONAZ3Solver()
    solver.add(z3.InRe(s, z3.Complement(z3.Plus(z3.Re("1")))))
    solver.add(z3.InRe(s, z3.Plus(z3.Re("0"))))
    assert solver.check() == z3.sat


def test_ends_in() -> None:
    solver = PyMONAZ3Solver()
    formula1 = cast(z3.BoolRef, z3_ends_in(z3.StringVal("0100"), z3.StringVal("0")))
    assert solver.check(formula1) == z3.sat

    formula2 = cast(z3.BoolRef, z3_ends_in(z3.StringVal("0100"), z3.StringVal("1")))
    assert solver.check(formula2) == z3.unsat


def test_starts_with() -> None:
    solver = PyMONAZ3Solver()
    formula1 = cast(z3.BoolRef, z3_starts_with(z3.StringVal("0100"), z3.StringVal("0")))
    assert solver.check(formula1) == z3.sat

    formula2 = cast(z3.BoolRef, z3_starts_with(z3.StringVal("0100"), z3.StringVal("1")))
    assert solver.check(formula2) == z3.unsat


def test_cut_last() -> None:
    solver = PyMONAZ3Solver()
    assert solver.check(z3_cut_last(z3.StringVal("")) != z3.StringVal("")) == z3.unsat
    assert solver.check(z3_cut_last(z3.StringVal("1")) != z3.StringVal("")) == z3.unsat
    assert (
        solver.check(z3_cut_last(z3.StringVal("10")) != z3.StringVal("1")) == z3.unsat
    )


def test_contains() -> None:
    solver = PyMONAZ3Solver()
    assert solver.check(z3.Contains(z3.StringVal("11"), z3.StringVal("0"))) == z3.unsat
    assert (
        solver.check(z3.Not(z3.Contains(z3.StringVal("101"), z3.StringVal("1"))))
        == z3.unsat
    )


def test_if() -> None:
    s = z3.String("s")
    b = z3.Bool("b")

    solver = PyMONAZ3Solver()
    solver.add(s == z3.If(b, z3.StringVal("100"), z3.StringVal("001")))
    assert solver.check() == z3.sat
    model = solver.model()
    assert model is not None
    assert model.eval_expr("s").as_string() in {"100", "001"}

    solver.add(b)
    assert solver.check() == z3.sat
    model = solver.model()
    assert model is not None
    assert model.eval_expr("s").as_string() == "100"


def test_replace_at() -> None:
    s = z3.String("s")
    solver = PyMONAZ3Solver()
    assert (
        solver.check(
            s == z3_replace_at(z3.StringVal("101"), z3.StringVal("1"), z3.IntVal(1))
        )
        == z3.sat
    )
    model = solver.model()
    assert model is not None
    assert model.eval_expr("s").as_string() == "111"


def test_get_alphabet() -> None:
    s = z3.String("s")
    formula = z3.InRe(z3.Concat(s, z3.StringVal("101")), z3.Star(z3.Re("03")))
    assert set(get_alphabet(formula).letters) == {"0", "1", "3"}
