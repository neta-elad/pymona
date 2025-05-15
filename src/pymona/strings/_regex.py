from abc import ABC, abstractmethod
from collections.abc import Callable
from dataclasses import dataclass
from functools import cached_property
from typing import ClassVar
from weakref import WeakValueDictionary

import pymona

from ._base import Alphabet, AlphabetSets, String

type _MatcherInternal = Callable[
    [pymona.ElementRef, pymona.ElementRef, AlphabetSets],
    pymona.BoolRef,
]


@dataclass(eq=True, frozen=True)
class _PredRefMatcher:
    pred: pymona.PredRef

    def __call__(
        self, start: pymona.ElementRef, end: pymona.ElementRef, sets: AlphabetSets
    ) -> pymona.BoolRef:
        return self.pred(start, end, *sets.values())


@dataclass(eq=True, frozen=True)
class _CachedRegex:
    name: str
    body: _MatcherInternal
    cache: ClassVar[WeakValueDictionary[tuple[str, Alphabet], _MatcherInternal]] = (
        WeakValueDictionary()
    )

    def __call__(self, alphabet: Alphabet) -> _MatcherInternal:
        key = (self.name, alphabet)
        if key in self.cache:
            return self.cache[key]

        start = pymona.ElementIdent("start")
        end = pymona.ElementIdent("end")
        x_vars = alphabet.to_vars("X")
        alphabet_name = "_".join(alphabet)
        matcher = _PredRefMatcher(
            pymona.pred(
                f"match_{alphabet_name}_{self.name}",
                [start, end] + list(x_vars.values()),
                self.body(start, end, x_vars),
            )
        )
        self.cache[key] = matcher
        return matcher


@dataclass(eq=True, frozen=True)
class Regex(ABC):
    @property
    @abstractmethod
    def name(self) -> str: ...

    @abstractmethod
    def body(
        self, start: pymona.ElementRef, end: pymona.ElementRef, sets: AlphabetSets
    ) -> pymona.BoolRef: ...

    @cached_property
    def cached(self) -> _CachedRegex:
        return _CachedRegex(self.name, self.body)

    def __call__(self, string: String) -> pymona.BoolRef:
        return self.call_cached(string)

    def call_raw(self, string: String) -> pymona.BoolRef:
        return string.apply(lambda s: self.body(pymona.m_int(0), s.end, s.sets))

    def call_cached(self, string: String) -> pymona.BoolRef:
        return string.apply(
            lambda s: self.cached(string.alphabet)(pymona.m_int(0), s.end, s.sets)
        )

    def call_cached_internal(
        self, start: pymona.ElementRef, end: pymona.ElementRef, sets: AlphabetSets
    ) -> pymona.BoolRef:
        alphabet = Alphabet(tuple(sets.keys()))
        return self.cached(alphabet)(start, end, sets)


@dataclass(eq=True, frozen=True)
class _Epsilon(Regex):
    @cached_property
    def name(self) -> str:
        return "@epsilon@"

    def body(
        self, start: pymona.ElementRef, end: pymona.ElementRef, sets: AlphabetSets
    ) -> pymona.BoolRef:
        return pymona.eq(start, end)

    def __call__(self, string: String) -> pymona.BoolRef:
        return string.apply(lambda s: pymona.eq(s.end, 0))


epsilon = _Epsilon()


@dataclass(eq=True, frozen=True)
class Word(Regex):
    word: str

    @cached_property
    def name(self) -> str:
        return self.word

    def body(
        self, start: pymona.ElementRef, end: pymona.ElementRef, sets: AlphabetSets
    ) -> pymona.BoolRef:
        return pymona.m_and(
            pymona.eq(start + len(self.word), end),
            *(sets[letter](start + i) for (i, letter) in enumerate(self.word)),
        )


@dataclass(eq=True, frozen=True)
class Concat(Regex):  # todo: unbounded concat with 2nd order quantification
    left: Regex
    right: Regex

    @cached_property
    def name(self) -> str:
        return f"@concat_{self.left.name}_{self.right.name}@"

    def body(
        self, start: pymona.ElementRef, end: pymona.ElementRef, sets: AlphabetSets
    ) -> pymona.BoolRef:
        _mid = pymona.ElementIdent("_mid")
        return pymona.exists1(
            _mid,
            pymona.m_and(
                self.left.call_cached_internal(start, _mid, sets),
                self.right.call_cached_internal(_mid, end, sets),
            ),
        )


def _letter(regex: Regex) -> str | None:
    if isinstance(regex, Word) and len(regex.word) == 1:
        return regex.word
    return None


@dataclass(eq=True, frozen=True)
class Plus(Regex):
    base: Regex

    @cached_property
    def name(self) -> str:
        return f"{self.base.name}@plus@"

    def body(
        self, start: pymona.ElementRef, end: pymona.ElementRef, sets: AlphabetSets
    ) -> pymona.BoolRef:
        _indices = pymona.SetIdent("_indices")
        _x = pymona.ElementIdent("_x")
        _y = pymona.ElementIdent("_y")
        return pymona.exists2(
            _indices,
            pymona.m_and(
                _in_seq(_indices, start, end),
                _indices(start),
                pymona.forall1(
                    (_x, _y),
                    pymona.implies(
                        pymona.m_and(
                            _indices(_x),
                            _successor_in_set(_indices, _x, end, _y),
                        ),
                        self.base.call_cached_internal(_x, _y, sets),
                    ),
                ),
            ),
        )

    def __call__(self, string: String) -> pymona.BoolRef:
        if (base_letter := _letter(self.base)) is not None:
            return string.apply(
                lambda s: pymona.m_and(
                    s.end > 0,
                    *(
                        pymona.is_empty(letter_set)
                        for letter, letter_set in s.sets.items()
                        if letter != base_letter
                    ),
                )
            )

        return super().__call__(string)


@dataclass(eq=True, frozen=True)
class Star(Regex):
    base: Regex

    @cached_property
    def name(self) -> str:
        return f"{self.base.name}@star@"

    @cached_property
    def _plus(self) -> Plus:
        return Plus(self.base)

    def body(
        self, start: pymona.ElementRef, end: pymona.ElementRef, sets: AlphabetSets
    ) -> pymona.BoolRef:
        return pymona.m_or(pymona.eq(start, end), self._plus.body(start, end, sets))

    def __call__(self, string: String) -> pymona.BoolRef:
        if (base_letter := _letter(self.base)) is not None:
            return string.apply(
                lambda s: pymona.m_and(
                    *(
                        pymona.is_empty(letter_set)
                        for letter, letter_set in s.sets.items()
                        if letter != base_letter
                    )
                )
            )

        return super().__call__(string)


@dataclass(eq=True, frozen=True)
class Option(Regex):
    base: Regex

    @cached_property
    def name(self) -> str:
        return f"{self.base.name}@option@"

    def body(
        self, start: pymona.ElementRef, end: pymona.ElementRef, sets: AlphabetSets
    ) -> pymona.BoolRef:
        return pymona.m_or(
            pymona.eq(start, end), self.base.call_cached_internal(start, end, sets)
        )


@dataclass(eq=True, frozen=True)
class Complement(Regex):
    base: Regex

    @cached_property
    def name(self) -> str:
        return f"@complement_{self.base.name}@"

    def body(
        self, start: pymona.ElementRef, end: pymona.ElementRef, sets: AlphabetSets
    ) -> pymona.BoolRef:
        return pymona.m_not(self.base.call_cached_internal(start, end, sets))

    def __call__(self, string: String) -> pymona.BoolRef:
        return pymona.m_not(self.base(string))  # todo: good optimization?


@dataclass(eq=True, frozen=True)
class Intersect(Regex):
    regexes: tuple[Regex, ...]

    @cached_property
    def name(self) -> str:
        return f"@intersect_{"_".join(regex.name for regex in self.regexes)}@"

    def body(
        self, start: pymona.ElementRef, end: pymona.ElementRef, sets: AlphabetSets
    ) -> pymona.BoolRef:
        return pymona.m_and(
            *(regex.call_cached_internal(start, end, sets) for regex in self.regexes)
        )


@dataclass(eq=True, frozen=True)
class Union(Regex):
    regexes: tuple[Regex, ...]

    @cached_property
    def name(self) -> str:
        return f"@union_{"_".join(regex.name for regex in self.regexes)}@"

    def body(
        self, start: pymona.ElementRef, end: pymona.ElementRef, sets: AlphabetSets
    ) -> pymona.BoolRef:
        return pymona.m_or(
            *(regex.call_cached_internal(start, end, sets) for regex in self.regexes)
        )


@pymona.to_pred
def _in_seq(
    elements: pymona.SetRef, start: pymona.ElementRef, end: pymona.ElementRef
) -> pymona.BoolRef:
    _x = pymona.ElementIdent("_x")
    return pymona.forall1(
        _x, pymona.implies(elements(_x), pymona.m_and(start <= _x, _x < end))
    )


@pymona.to_pred
def _successor_in_set(
    elements: pymona.SetRef,
    current: pymona.ElementRef,
    end: pymona.ElementRef,
    succ: pymona.ElementRef,
) -> pymona.BoolRef:
    _x = pymona.ElementIdent("_x")
    return pymona.m_or(
        pymona.m_and(
            pymona.eq(succ, end),
            pymona.forall1(_x, pymona.implies(elements(_x), _x <= current)),
        ),
        pymona.m_and(
            succ < end,
            succ > current,
            elements(succ),
            pymona.forall1(
                _x, pymona.implies(pymona.m_and(elements(_x), _x > current), _x >= succ)
            ),
        ),
    )
