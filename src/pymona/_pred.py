from collections.abc import Callable
from dataclasses import dataclass
from inspect import signature, Parameter

from ._pymona import (
    BoolRef,
    pred,
    BoolIdent,
    ElementIdent,
    SetIdent,
    ElementRef,
    SetRef,
    PredRef,
)


type TypedPred[**P] = Callable[P, BoolRef]


@dataclass
class LazyPred[**P]:
    fun: TypedPred[P]
    pred_ref: PredRef | None = None

    def __call__(self, *args: P.args, **kwargs: P.kwargs) -> BoolRef:
        return self.fun(*args, **kwargs)  # type: ignore
        if self.pred_ref is None:
            self.pred_ref = self.build()

        return self.pred_ref(*args, **kwargs)  # type: ignore

    def build(self) -> PredRef:
        name = self.fun.__name__
        args: list[BoolIdent | ElementIdent | SetIdent] = []

        for param in signature(self.fun).parameters.values():
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

        return pred(name, args, self.fun(*args))  # type: ignore


def to_pred[**P](fun: TypedPred[P]) -> TypedPred[P]:
    return LazyPred(fun)
