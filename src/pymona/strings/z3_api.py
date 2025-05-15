from dataclasses import dataclass, field
from functools import cached_property
from typing import Self, overload

import pymona

try:
    import z3
except ImportError:
    print(
        "In order to use PyMONA's Z3 API, install PyMONA with the [z3] optional dependency:"
    )
    print("pip install pymona[z3]")
    raise

from . import str_prefix
from ._base import Alphabet, String
from ._bipredicates import append, cut_last, replace_at, str_eq, substr
from ._core import Context, Model, StringITE, exists, forall
from ._predicates import contains, ends_in, starts_with, str_empty
from ._regex import (
    Complement,
    Concat,
    Intersect,
    Option,
    Plus,
    Regex,
    Star,
    Union,
    Word,
    epsilon,
)

z3_cut_last = z3.Function("cut_last", z3.StringSort(), z3.StringSort())
z3_starts_with = z3.Function(
    "starts_with", z3.StringSort(), z3.StringSort(), z3.BoolSort()
)
z3_ends_in = z3.Function("ends_in", z3.StringSort(), z3.StringSort(), z3.BoolSort())
z3_replace_at = z3.Function(
    "replace_at", z3.StringSort(), z3.StringSort(), z3.IntSort(), z3.StringSort()
)


def get_alphabet(expr: z3.ExprRef | str) -> Alphabet:
    if isinstance(expr, str):
        return Alphabet(tuple(set(expr)))

    result: set[str] = set()

    def do_get_alphabet(e: z3.ExprRef) -> None:
        if z3.is_string_value(e):
            result.update(set(e.as_string()))
        else:
            for child in e.children():
                do_get_alphabet(child)

    do_get_alphabet(expr)
    return Alphabet(tuple(result))


@overload
def from_z3(formula: z3.BoolRef, /) -> pymona.BoolRef: ...
@overload
def from_z3(string: z3.SeqRef | str, /) -> String: ...
@overload
def from_z3(regex: z3.ReRef, /) -> Regex: ...


def from_z3(
    expr: z3.BoolRef | z3.SeqRef | str | z3.ReRef,
) -> pymona.BoolRef | String | Regex:
    converter = _Converter(get_alphabet(expr))
    if isinstance(expr, str) or z3.is_string(expr):
        return converter.convert_string(expr)
    elif z3.is_bool(expr):
        return converter.convert_formula(expr)
    elif z3.is_re(expr):
        return converter.convert_regex(expr)
    else:
        assert False, f"Bad expr {expr}"


def _letter(expr: z3.ExprRef) -> str:
    assert z3.is_string_value(expr)
    value = expr.as_string()

    assert len(value) == 1
    return value


@dataclass
class _Converter:
    alphabet: Alphabet

    @cached_property
    def context(self) -> Context:
        return Context(self.alphabet)

    def convert_formula(
        self, formula: z3.ExprRef, bound_variables: frozenset[str] = frozenset()
    ) -> pymona.BoolRef:
        if z3.is_eq(formula):
            left, right = formula.children()
            if z3.is_bool(left):
                assert z3.is_bool(right)
                left_formula = self.convert_formula(left, bound_variables)
                right_formula = self.convert_formula(right, bound_variables)
                return pymona.iff(left_formula, right_formula)
            else:
                left_expr = self.convert_string(left, bound_variables)
                right_expr = self.convert_string(right, bound_variables)
                return str_eq(left_expr, right_expr)
        elif z3.is_distinct(formula):
            left, right = formula.children()
            if z3.is_bool(left):
                raise NotImplementedError("niff construction")
            else:
                left_expr = self.convert_string(left, bound_variables)
                right_expr = self.convert_string(right, bound_variables)
                return pymona.m_not(str_eq(left_expr, right_expr))
        elif z3.is_and(formula):
            return pymona.m_and(
                *(
                    self.convert_formula(child, bound_variables)
                    for child in formula.children()
                ),
            )
        elif z3.is_or(formula):
            return pymona.m_or(
                *(
                    self.convert_formula(child, bound_variables)
                    for child in formula.children()
                ),
            )
        elif z3.is_implies(formula):
            left_formula, right_formula = (
                self.convert_formula(child, bound_variables)
                for child in formula.children()
            )
            return pymona.implies(left_formula, right_formula)
        elif z3.is_quantifier(formula):
            bounding_vars = [
                z3.Const(formula.var_name(i), formula.var_sort(i))
                for i in range(formula.num_vars())
            ]
            substituted_body = z3.substitute_vars(
                formula.body(), *reversed(bounding_vars)
            )  # Z3 uses vars in reverse order
            result = bounding_vars, substituted_body
            variables, body = result
            var_names = [str(var) for var in variables]
            mona_vars = list(map(self.context.unvalidated_var, var_names))
            converted_body = self.convert_formula(
                body, bound_variables | frozenset(var_names)
            )
            if formula.is_forall():
                return forall(mona_vars, converted_body)
            else:
                return exists(mona_vars, converted_body)
        elif formula.decl().name() == "xor":
            left_formula, right_formula = (
                self.convert_formula(child, bound_variables)
                for child in formula.children()
            )
            return pymona.m_or(
                pymona.m_and(left_formula, pymona.m_not(right_formula)),
                pymona.m_and(pymona.m_not(left_formula), right_formula),
            )
        elif z3.is_not(formula):
            child = self.convert_formula(formula.children()[0], bound_variables)
            return pymona.m_not(child)
        elif z3.is_true(formula):
            return pymona.true()
        elif z3.is_false(formula):
            return pymona.false()
        elif z3.is_const(formula):
            return pymona.BoolIdent(formula.decl().name())
        elif formula.decl().name() == "str.prefixof":
            prefix, string = (
                self.convert_string(child, bound_variables)
                for child in formula.children()
            )
            return str_prefix(prefix, string)
        elif formula.decl().name() == "str.in_re":
            left, right = formula.children()
            string = self.convert_string(left, bound_variables)
            regex = self.convert_regex(right)
            return regex(string)
        elif formula.decl().name() == "str.empty":
            (string,) = (
                self.convert_string(child, bound_variables)
                for child in formula.children()
            )
            return str_empty(string)
        elif formula.decl().name() == "str.contains":
            left, right = formula.children()
            assert z3.is_string_value(right)
            letter = _letter(right)
            string = self.convert_string(left, bound_variables)
            return contains(letter)(string)
        elif z3.is_app(formula) and formula.decl().eq(z3_ends_in):
            left, right = formula.children()
            letter = _letter(right)
            return ends_in(letter)(self.convert_string(left, bound_variables))
        elif z3.is_app(formula) and formula.decl().eq(z3_starts_with):
            left, right = formula.children()
            letter = _letter(right)
            return starts_with(letter)(self.convert_string(left, bound_variables))

        raise NotImplementedError(f"{formula.decl().name()}")

    def convert_string(
        self, string: z3.ExprRef | str, bound_variables: frozenset[str] = frozenset()
    ) -> String:
        if isinstance(string, str):
            return self.context.literal(string)

        assert z3.is_string(string), f"Non-string expression {string}"
        value = string.as_string()
        if z3.is_string_value(string):
            return self.context.literal(value)
        elif z3.is_const(string):
            if value in bound_variables:
                return self.context.unvalidated_var(value)
            return self.context.var(value)
        elif z3.is_app(string) and string.decl().name() == "str.++":
            left, right = string.children()
            left_expr = self.convert_string(left, bound_variables)
            if z3.is_string_value(right):
                value = right.as_string()
                return append(left_expr, value)
        elif z3.is_app(string) and string.decl().name() == "str.substr":
            string, start, length = string.children()
            if not (z3.is_int_value(start) and z3.is_int_value(length)):
                raise NotImplementedError(
                    f"Only constant substring expression are supported, got: {start}, {length}"
                )
            term = self.convert_string(string, bound_variables)

            return substr(term, start.as_long(), length.as_long())
        elif z3.is_app(string) and string.decl().eq(z3_cut_last):
            (string,) = string.children()
            term = self.convert_string(string, bound_variables)
            return cut_last(term)
        elif z3.is_app(string) and string.decl().eq(z3_replace_at):
            (string, replacement, at) = string.children()
            assert z3.is_string_value(replacement)
            word = replacement.as_string()
            assert z3.is_int_value(at)
            at_int = at.as_long()
            term = self.convert_string(string, bound_variables)
            return replace_at(term, word, at_int)
        elif string.decl().name() == "if":
            condition, if_true, if_false = string.children()
            assert z3.is_bool(condition)
            true_term = self.convert_string(if_true, bound_variables)
            false_term = self.convert_string(if_false, bound_variables)
            formula = self.convert_formula(condition, bound_variables)
            return StringITE(self.alphabet, formula, true_term, false_term)

        raise NotImplementedError(
            f"Function application {string.decl().name()}: {string}"
        )

    def convert_regex(self, regex: z3.ExprRef) -> Regex:
        if regex.decl().name() == "str.to_re":
            child = regex.children()[0]
            assert z3.is_string(child)
            string = child.as_string()

            if len(string) == 0:
                return epsilon
            else:
                return Word(string)
        elif regex.decl().name() == "re.+":
            base = self.convert_regex(regex.children()[0])
            return Plus(base)
        elif regex.decl().name() == "re.*":
            base = self.convert_regex(regex.children()[0])
            return Star(base)
        elif regex.decl().name() == "re.opt":
            base = self.convert_regex(regex.children()[0])
            return Option(base)
        elif regex.decl().name() == "re.comp":
            base = self.convert_regex(regex.children()[0])
            return Complement(base)
        elif regex.decl().name() == "re.inter":
            operands = tuple(self.convert_regex(child) for child in regex.children())
            return Intersect(operands)
        elif regex.decl().name() == "re.union":
            operands = tuple(self.convert_regex(child) for child in regex.children())
            return Union(operands)
        elif regex.decl().name() == "re.++":
            left, right = (self.convert_regex(child) for child in regex.children())
            return Concat(left, right)
        raise NotImplementedError(f"Unsupported regex {regex}")


@dataclass
class PyMONAZ3Model:
    model: Model

    @classmethod
    def parse(cls, model: Model | None) -> Self | None:
        if model is None:
            return None
        return cls(model)

    def eval_bool(self, item: str) -> bool:
        return self.model.bools[item]

    def eval_expr(self, item: str) -> z3.SeqRef:
        return z3.StringVal(self.model.strings[item])


@dataclass
class PyMONAZ3Solver:
    assertions: list[z3.BoolRef] = field(init=False, default_factory=list)
    last_model: PyMONAZ3Model | None = field(init=False, default=None)

    def add(self, assertion: z3.BoolRef) -> None:
        self.assertions.append(assertion)

    def check(self, *assertions: z3.BoolRef) -> z3.CheckSatResult:
        z3_formula = z3.And(*self.assertions, *assertions)
        alphabet = get_alphabet(z3_formula)
        formula = from_z3(z3_formula)

        context = Context(alphabet)
        solver = context.solver()

        result = solver.check(formula)

        if result:
            self.last_model = PyMONAZ3Model.parse(solver.model())
            return z3.sat

        return z3.unsat

    def model(self) -> PyMONAZ3Model | None:
        return self.last_model
