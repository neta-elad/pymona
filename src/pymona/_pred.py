from collections.abc import Callable
from inspect import signature, Parameter

from ._pymona import (
    BoolRef,
    pred,
    BoolIdent,
    ElementIdent,
    SetIdent,
    ElementRef,
    SetRef,
)


type TypedPred[**P] = Callable[P, BoolRef]


def to_pred[**P](fun: TypedPred[P]) -> TypedPred[P]:
    name = fun.__name__
    args: list[BoolIdent | ElementIdent | SetIdent] = []

    for param in signature(fun).parameters.values():
        assert (
            param.kind == Parameter.POSITIONAL_ONLY
            or param.kind == Parameter.POSITIONAL_OR_KEYWORD
        )
        if issubclass(param.annotation, BoolRef):
            args.append(BoolIdent(param.name))
        elif issubclass(param.annotation, ElementRef):
            args.append(ElementIdent(param.name))
        elif issubclass(param.annotation, SetRef):
            args.append(SetIdent(param.name))
        else:
            assert False, f"Bad parameter {param}"

    return pred(name, args, fun(*args))  # type: ignore
