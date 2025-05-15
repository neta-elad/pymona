from typing import Any

_multitons: dict[int, dict[int, Any]] = {}


class MultitonMeta(type):
    def __init__[
        T
    ](cls: type[T], name: str, bases: tuple[type, ...], dct: dict[str, Any]) -> None:
        super().__init__(name, bases, dct)  # type: ignore
        _multitons[id(cls)] = {}

    def __call__[T](cls: type[T], *args: Any, **kwargs: Any) -> T:
        key = hash((args, frozenset(kwargs.items())))
        if key not in _multitons[id(cls)]:
            instance = super().__call__(*args, **kwargs)  # type: ignore
            _multitons[id(cls)][key] = instance
        return _multitons[id(cls)][key]  # type: ignore


class Multiton(metaclass=MultitonMeta): ...
