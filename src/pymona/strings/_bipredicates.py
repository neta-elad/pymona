from collections.abc import Callable
from functools import wraps
from typing import Protocol, overload
from weakref import WeakValueDictionary

import pymona

from ._base import Alphabet, AlphabetSets, BiPredicate, String, StringGroundTerm
from ._core import Context, StringFunctionApplication

type _BiPredicateInternal = Callable[
    [pymona.ElementRef, AlphabetSets, pymona.ElementRef, AlphabetSets], pymona.BoolRef
]
_binary_pred_cache: WeakValueDictionary[tuple[Alphabet, str, str], pymona.PredRef] = (
    WeakValueDictionary()
)

_x = pymona.ElementIdent("_x")


def _binary_pred_ref(
    alphabet: Alphabet, internal: _BiPredicateInternal, suffix: str
) -> pymona.PredRef:
    alphabet_name = "_".join(alphabet)
    name = internal.__name__
    key = (alphabet, name, suffix)

    if key in _binary_pred_cache:
        return _binary_pred_cache[key]

    end1 = pymona.ElementIdent("end1")
    x1_vars = alphabet.to_vars("X1")
    end2 = pymona.ElementIdent("end2")
    x2_vars = alphabet.to_vars("X2")
    pred = pymona.pred(
        f"{alphabet_name}_{name}_{suffix}",
        [end1] + list(x1_vars.values()) + [end2] + list(x2_vars.values()),
        internal(end1, x1_vars, end2, x2_vars),
    )
    _binary_pred_cache[key] = pred
    return pred


@overload
def _binary_predicate(internal: _BiPredicateInternal, /) -> BiPredicate: ...


@overload
def _binary_predicate(
    *, suffix: str
) -> Callable[[_BiPredicateInternal], BiPredicate]: ...


def _binary_predicate(
    internal: _BiPredicateInternal | None = None, /, *, suffix: str = ""
) -> Callable[[_BiPredicateInternal], BiPredicate] | BiPredicate:
    def wrapper(actual_internal: _BiPredicateInternal) -> BiPredicate:
        def do_internal(
            string1: StringGroundTerm, string2: StringGroundTerm
        ) -> pymona.BoolRef:
            return _binary_pred_ref(string1.alphabet, actual_internal, suffix)(
                string1.end, *string1.sets.values(), string2.end, *string2.sets.values()
            )

        @wraps(actual_internal)
        def wrapped_internal(
            string1: String | str, string2: String | str | None = None
        ) -> pymona.BoolRef | String:
            if string2 is None:
                assert not isinstance(string1, str)
                return StringFunctionApplication(string1.alphabet, string1, do_internal)

            if isinstance(string1, str):
                assert not isinstance(string2, str)
                context = Context(string2.alphabet)
                string1 = context.literal(string1)
            elif isinstance(string2, str):
                assert not isinstance(string1, str)
                context = Context(string1.alphabet)
                string2 = context.literal(string2)

            assert string1.alphabet == string2.alphabet
            return string1.apply(
                lambda s1: string2.apply(lambda s2: do_internal(s1, s2))
            )

        return wrapped_internal  # type: ignore

    if internal is not None:
        return wrapper(internal)
    else:
        return wrapper


@_binary_predicate
def str_prefix(
    end1: pymona.ElementRef,
    sets1: AlphabetSets,
    end2: pymona.ElementRef,
    sets2: AlphabetSets,
) -> pymona.BoolRef:
    return pymona.m_and(
        end1 <= end2,
        *(var1 <= var2 for var1, var2 in zip(sets1.values(), sets2.values())),
    )


@_binary_predicate
def str_eq(
    end1: pymona.ElementRef,
    sets1: AlphabetSets,
    end2: pymona.ElementRef,
    sets2: AlphabetSets,
) -> pymona.BoolRef:
    return pymona.m_and(
        pymona.eq(end1, end2),
        *(
            pymona.eq(var1, var2)
            for (var1, var2) in zip(sets1.values(), sets2.values())
        ),
    )


class StringFunction[**P](Protocol):
    def __call__(self, string: String, *args: P.args, **kwargs: P.kwargs) -> String: ...


def _str_function[**P](fun: Callable[P, BiPredicate]) -> StringFunction[P]:
    @wraps(fun)
    def wrapped(string: String, *args: P.args, **kwargs: P.kwargs) -> String:
        return fun(*args, **kwargs)(string)

    return wrapped


@_str_function
def append(word: str) -> BiPredicate:
    @_binary_predicate(suffix=word)
    def append(
        end1: pymona.ElementRef,
        sets1: AlphabetSets,
        end2: pymona.ElementRef,
        sets2: AlphabetSets,
    ) -> pymona.BoolRef:
        return pymona.m_and(
            pymona.eq(end2, end1 + len(word)),
            *(sets2[letter](end1 + i) for i, letter in enumerate(word)),
            *(var1 <= var2 for var1, var2 in zip(sets1.values(), sets2.values())),
        )

    return append


@_str_function
def cut_last() -> BiPredicate:
    @_binary_predicate
    def cut_last(
        end1: pymona.ElementRef,
        sets1: AlphabetSets,
        end2: pymona.ElementRef,
        sets2: AlphabetSets,
    ) -> pymona.BoolRef:
        return pymona.m_or(
            pymona.m_and(pymona.eq(end1, 0), pymona.eq(end2, 0)),
            pymona.m_and(
                pymona.eq(end2, end1 - 1),
                *(var2 <= var1 for var1, var2 in zip(sets1.values(), sets2.values())),
            ),
        )

    return cut_last


@_str_function
def replace_at(word: str, start: int = 0) -> BiPredicate:
    @_binary_predicate(suffix=f"{word}_{start}")
    def replace_at(
        end1: pymona.ElementRef,
        sets1: AlphabetSets,
        end2: pymona.ElementRef,
        sets2: AlphabetSets,
    ) -> pymona.BoolRef:
        return pymona.m_and(
            pymona.eq(end2, end1),
            start + len(word) <= end2,
            *(sets2[letter](start + i) for i, letter in enumerate(word)),
            pymona.forall1(
                _x,
                pymona.implies(
                    pymona.m_or(_x < start, _x >= start + len(word)),
                    pymona.m_and(
                        *(
                            pymona.iff(var1(_x), var2(_x))
                            for var1, var2 in zip(sets1.values(), sets2.values())
                        )
                    ),
                ),
            ),
        )

    return replace_at


@_str_function
def substr(start: int, length: int | None) -> BiPredicate:
    @_binary_predicate(suffix=f"{start}_{length}")
    def substr(
        end1: pymona.ElementRef,
        sets1: AlphabetSets,
        end2: pymona.ElementRef,
        sets2: AlphabetSets,
    ) -> pymona.BoolRef:
        end1_expr = end1
        end2_expr = end1 - start
        if length is not None:
            end1_expr = pymona.min(end1_expr, start + length)
            end2_expr = pymona.min(end2_expr, length)

        return pymona.m_and(
            pymona.eq(end2, end2_expr),
            pymona.forall1(
                _x,
                pymona.implies(
                    pymona.m_and(_x >= start, _x < end1_expr),
                    pymona.m_and(
                        *(
                            pymona.implies(var1(_x), var2(_x - start))
                            for var1, var2 in zip(sets1.values(), sets2.values())
                        )
                    ),
                ),
            ),
        )

    return substr
