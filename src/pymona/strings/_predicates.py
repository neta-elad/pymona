from collections.abc import Callable
from functools import wraps
from typing import overload
from weakref import WeakValueDictionary

import pymona

from ._base import Alphabet, AlphabetSets, Predicate, String

_x = pymona.ElementIdent("_x")

type _PredicateInternal = Callable[[pymona.ElementRef, AlphabetSets], pymona.BoolRef]

_unary_pred_cache: WeakValueDictionary[tuple[Alphabet, str, str], pymona.PredRef] = (
    WeakValueDictionary()
)


def _unary_pred_ref(
    alphabet: Alphabet, internal: _PredicateInternal, suffix: str
) -> pymona.PredRef:
    alphabet_name = "_".join(alphabet)
    name = internal.__name__
    key = (alphabet, name, suffix)

    if key in _unary_pred_cache:
        return _unary_pred_cache[key]

    end = pymona.ElementIdent("end")
    x_vars = alphabet.to_vars("X")
    pred = pymona.pred(
        f"{alphabet_name}_{name}_{suffix}",
        [end] + list(x_vars.values()),
        internal(end, x_vars),
    )
    _unary_pred_cache[key] = pred

    return pred


@overload
def _unary_predicate(internal: _PredicateInternal, /) -> Predicate: ...


@overload
def _unary_predicate(*, suffix: str) -> Callable[[_PredicateInternal], Predicate]: ...


def _unary_predicate(
    internal: _PredicateInternal | None = None, /, *, suffix: str = ""
) -> Callable[[_PredicateInternal], Predicate] | Predicate:
    def wrapper(actual_internal: _PredicateInternal) -> Predicate:
        @wraps(actual_internal)
        def wrapped_internal(string: String) -> pymona.BoolRef:
            return string.apply(
                lambda s: _unary_pred_ref(string.alphabet, actual_internal, suffix)(
                    s.end, *s.sets.values()
                )
            )

        return wrapped_internal

    if internal is not None:
        return wrapper(internal)
    else:
        return wrapper


@_unary_predicate
def str_valid(end: pymona.ElementRef, sets: AlphabetSets) -> pymona.BoolRef:
    return pymona.forall1(
        _x,
        pymona.m_and(
            pymona.iff(
                _x < end,
                pymona.m_or(*(s(_x) for s in sets.values())),
            ),
            *(
                pymona.m_not(pymona.m_and(s1(_x), s2(_x)))
                for l1, s1 in sets.items()
                for l2, s2 in sets.items()
                if l1 != l2
            ),
        ),
    )


@_unary_predicate
def str_empty(end: pymona.ElementRef, sets: AlphabetSets) -> pymona.BoolRef:
    return pymona.m_and(
        pymona.eq(end, 0),
        *(pymona.is_empty(var) for var in sets.values()),
    )


def ends_in(letter: str) -> Predicate:
    @_unary_predicate(suffix=letter)
    def ends_in(end: pymona.ElementRef, sets: AlphabetSets) -> pymona.BoolRef:
        assert letter in sets.keys()
        return pymona.m_and(
            end > 0,
            sets[letter](end - 1),
        )

    return ends_in


def starts_with(letter: str) -> Predicate:
    @_unary_predicate(suffix=letter)
    def starts_with(end: pymona.ElementRef, sets: AlphabetSets) -> pymona.BoolRef:
        assert letter in sets.keys()
        return pymona.m_and(
            end > 0,
            sets[letter](0),
        )

    return starts_with


def contains(letter: str) -> Predicate:
    @_unary_predicate(suffix=letter)
    def contains(end: pymona.ElementRef, sets: AlphabetSets) -> pymona.BoolRef:
        assert letter in sets.keys()
        return pymona.exists1(_x, sets[letter](_x))

    return contains
