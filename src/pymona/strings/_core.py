import io
from collections import defaultdict
from collections.abc import Callable
from dataclasses import dataclass, field
from functools import cached_property
from typing import ClassVar, Self, overload, override

import pymona

from ._base import (
    Alphabet,
    AlphabetSets,
    AlphabetVars,
    GroundPredicate,
    String,
    StringGroundTerm,
)
from ._multiton import Multiton
from ._predicates import str_valid

type GroundBiPredicate = Callable[[StringGroundTerm, StringGroundTerm], pymona.BoolRef]


@dataclass(eq=True, frozen=True)
class Context(Multiton):
    alphabet: Alphabet
    vars: "set[StringVar]" = field(default_factory=set, init=False, compare=False)

    @classmethod
    def default(cls) -> Self:
        return cls(Alphabet.default())

    def var(self, name: str) -> "StringVar":
        var = self.unvalidated_var(name)
        self.vars.add(var)
        return var

    def unvalidated_var(self, name: str) -> "StringVar":
        return StringVar(self.alphabet, name, self)

    def literal(self, literal: str) -> "StringLiteral":
        return StringLiteral(self.alphabet, literal)

    def solver(self) -> "Solver":
        return Solver(self)


@dataclass
class Model:
    strings: dict[str, str] = field(default_factory=dict)
    bools: dict[str, bool] = field(default_factory=dict)

    @overload
    def __getitem__(self, item: "StringVar") -> str: ...

    @overload
    def __getitem__(self, item: pymona.BoolIdent) -> bool: ...

    def __getitem__(self, item: "StringVar | pymona.BoolIdent") -> str | bool:
        if isinstance(item, StringVar):
            return self.strings[item.name]
        return self.bools.get(str(item), False)

    @classmethod
    def parse(
        cls,
        alphabet: Alphabet,
        model: pymona.Model | None,
    ) -> Self | None:
        if model is None:
            return None
        strings = {}
        letters: dict[str, dict[str, set[int]]] = defaultdict(dict)
        ends: dict[str, int] = {
            var[4:]: value
            for var, value in model.ints.items()
            if var.startswith("end_")
        }

        for var, value in model.sets.items():
            for letter in alphabet:
                if var.startswith(f"X_{letter}_"):
                    name = var[4:]
                    letters[name][letter] = value

        for name, end in ends.items():
            buffer = io.StringIO()
            for i in range(end):
                found = False
                for letter in alphabet:
                    if i in letters[name][letter]:
                        assert (
                            not found
                        ), f"Invalid string for {name} (contradicting letters)"
                        buffer.write(letter)
                        found = True
                assert found, f"Invalid string for {name} (missing letters)"
            strings[name] = buffer.getvalue()

        return cls(strings, dict(model.bools))


@dataclass
class Solver:
    context: Context
    assertions: list[pymona.BoolRef] = field(init=False, default_factory=list)
    last_model: Model | None = field(init=False, default=None)

    def check(
        self, assertions: pymona.BoolRef | list[pymona.BoolRef] | None = None
    ) -> bool:
        if assertions is None:
            assertions = []
        elif not isinstance(assertions, list):
            assertions = [assertions]

        validations = [str_valid(var) for var in self.context.vars]

        formula = pymona.m_and(*validations, *assertions, *self.assertions)

        self.last_model = Model.parse(self.context.alphabet, pymona.solve(formula))

        return self.last_model is not None

    def model(self) -> Model | None:
        return self.last_model


@dataclass(eq=True, frozen=True)
class StringVar(StringGroundTerm):
    name: str
    context: Context

    @cached_property
    def vars(self) -> AlphabetVars:
        return self.alphabet.to_vars("X", self.name)

    @cached_property
    def sets(self) -> AlphabetSets:
        return self.vars

    @cached_property
    def end_var(self) -> pymona.ElementIdent:
        return pymona.ElementIdent(f"end_{self.name}")

    @cached_property
    def end(self) -> pymona.ElementRef:
        return self.end_var


@dataclass(eq=True, frozen=True)
class StringLiteral(StringGroundTerm):
    literal: str

    def __post_init__(self) -> None:
        assert set(self.literal) <= set(iter(self.alphabet))

    @cached_property
    def sets(self) -> AlphabetSets:
        letters: dict[str, set[int]] = defaultdict(set)

        for i in range(len(self.literal)):
            letters[self.literal[i]].add(i)

        return {letter: pymona.m_set(*letters[letter]) for letter in self.alphabet}

    @cached_property
    def end(self) -> pymona.ElementRef:
        return pymona.m_int(len(self.literal))


@dataclass(frozen=True)
class StringFunctionApplication(String):
    term: String
    application: GroundBiPredicate

    counter: ClassVar[int] = 0

    @classmethod
    def next_var(cls, context: Context) -> StringVar:
        cls.counter += 1
        return context.unvalidated_var(f"_fun_{cls.counter}")

    @override
    def apply(self, predicate: GroundPredicate) -> pymona.BoolRef:
        this_var = self.next_var(Context(self.alphabet))
        return exists(
            [this_var],
            self.term.apply(
                lambda var: pymona.m_and(
                    self.application(var, this_var),
                    predicate(this_var),
                )
            ),
        )


@dataclass(frozen=True)
class StringITE(String):
    condition: pymona.BoolRef
    if_true: String
    if_false: String

    @override
    def apply(self, predicate: GroundPredicate) -> pymona.BoolRef:
        return pymona.m_and(
            pymona.implies(self.condition, self.if_true.apply(predicate)),
            pymona.implies(
                pymona.m_not(self.condition), self.if_false.apply(predicate)
            ),
        )


def ite(condition: pymona.BoolRef, if_true: String, if_false: String) -> String:
    assert if_true.alphabet == if_false.alphabet
    return StringITE(if_true.alphabet, condition, if_true, if_false)


def exists(
    variables: StringVar | list[StringVar], body: pymona.BoolRef
) -> pymona.BoolRef:
    if not isinstance(variables, list):
        variables = [variables]

    first_order_vars, second_order_vars, validations = _prepare_for_quantifier(
        variables
    )

    return pymona.exists2(
        second_order_vars,
        pymona.exists1(
            first_order_vars,
            pymona.m_and(body, *validations),
        ),
    )


def forall(
    variables: StringVar | list[StringVar], body: pymona.BoolRef
) -> pymona.BoolRef:
    if not isinstance(variables, list):
        variables = [variables]

    first_order_vars, second_order_vars, validations = _prepare_for_quantifier(
        variables
    )

    return pymona.forall2(
        second_order_vars,
        pymona.forall1(
            first_order_vars, pymona.implies(pymona.m_and(*validations), body)
        ),
    )


def _prepare_for_quantifier(variables: list[StringVar]) -> tuple[
    list[pymona.ElementIdent],
    list[pymona.SetIdent],
    list[pymona.BoolRef],
]:
    first_order_vars = []
    second_order_vars: list[pymona.SetIdent] = []
    validations = []
    for var in variables:
        first_order_vars.append(var.end_var)
        second_order_vars.extend(var.vars.values())
        validations.append(str_valid(var))

    return first_order_vars, second_order_vars, validations
