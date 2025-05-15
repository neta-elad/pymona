from abc import ABC, abstractmethod
from collections.abc import Callable, Mapping
from dataclasses import dataclass
from typing import Iterator, Protocol, Self, overload, override

import pymona

from ._multiton import Multiton

type Letter = str
type AlphabetSets = Mapping[Letter, pymona.SetRef]
type AlphabetVars = Mapping[Letter, pymona.SetIdent]


@dataclass(eq=True, frozen=True)
class Alphabet(Multiton):
    letters: tuple[Letter, ...]

    def __post_init__(self) -> None:
        if any(len(letter) != 1 for letter in self.letters):
            raise ValueError("Alphabet may only contain single letters")

    @classmethod
    def default(cls) -> Self:
        return cls(("0", "1"))

    def __iter__(self) -> Iterator[Letter]:
        return iter(self.letters)

    def to_vars(self, prefix: str, suffix: str = "") -> AlphabetVars:
        return {
            letter: pymona.SetIdent(f"{prefix}_{letter}_{suffix}")
            for letter in self.letters
        }


type GroundPredicate = Callable[["StringGroundTerm"], pymona.BoolRef]


@dataclass(eq=True, frozen=True)
class String(ABC):
    alphabet: Alphabet

    @abstractmethod
    def apply(self, predicate: GroundPredicate) -> pymona.BoolRef: ...


type Predicate = Callable[[String], pymona.BoolRef]


class BiPredicate(Protocol):
    @overload
    def __call__(self, string1: String, string2: String | str) -> pymona.BoolRef: ...

    @overload
    def __call__(self, string1: String | str, string2: String) -> pymona.BoolRef: ...

    @overload
    def __call__(self, string: String) -> String: ...


@dataclass(eq=True, frozen=True)
class StringGroundTerm(String, ABC):
    @property
    @abstractmethod
    def sets(self) -> AlphabetSets: ...

    @property
    @abstractmethod
    def end(self) -> pymona.ElementRef: ...

    @override
    def apply(self, predicate: GroundPredicate) -> pymona.BoolRef:
        return predicate(self)
