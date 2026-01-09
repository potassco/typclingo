"""
A parser for type specifications.
"""

import re
from typing import NoReturn

from .spec import (
    FunctionCons,
    Predicate,
    Program,
    Type,
    TypeCons,
    TypeDef,
    TypeRelation,
    TypeSpec,
    UnionCons,
)

__all__ = ["Parser"]


class Parser:
    """
    A parser for type specifications.
    """

    _value: str
    _pos: int

    def __init__(self, value: str):
        self._value = value
        self._pos = 0

    def location(self) -> tuple[int, int]:
        """
        Get the current location (line, column).
        """
        start = self._value.rfind("\n", 0, self._pos)
        line = self._value.count("\n", 0, start + 1) + 1
        col = self._pos - start + 1
        return line, col

    def error(self, message: str) -> NoReturn:
        """
        Raise a parsing error with the given message and current location.
        """
        l, c = self.location()
        raise ValueError(f"{l}:{c}: {message}")

    def gobble(self) -> None:
        """
        Gobble whitespace.
        """
        while self._pos < len(self._value) and self._value[self._pos].isspace():
            self._pos += 1

    def consume(self, x: str, gobble: bool = True) -> None:
        """
        Consume the given string `x`.

        When `gobble` is true, whitespace is gobbled before consuming.
        """
        if gobble:
            self.gobble()
        if not self._value[self._pos :].startswith(x):
            self.error(f"expected '{x}'")
        self._pos += len(x)

    def branch(self, x: str, gobble: bool = True) -> bool:
        """
        Branch on the given string `x`.

        When `gobble` is true, whitespace is gobbled before branching.
        """
        if gobble:
            self.gobble()
        if self._value[self._pos :].startswith(x):
            self._pos += len(x)
            return True
        return False

    def branch_uid(self) -> str | None:
        """
        Branch on an upper case identifier.
        """
        self.gobble()
        if m := re.match(r"[A-Z][a-zA-Z0-9_]*", self._value[self._pos :]):
            uid = m.group(0)
            self._pos += len(uid)
            return uid
        return None

    def uid(self) -> str:
        """
        Parse an upper case identifier.
        """
        if m := self.branch_uid():
            return m
        self.error("expected upper case identifier")

    def branch_lid(self) -> str | None:
        """
        Branch on a lower case identifier.
        """
        self.gobble()
        if m := re.match(r"[a-z][a-zA-Z0-9_]*", self._value[self._pos :]):
            uid = m.group(0)
            self._pos += len(uid)
            return uid
        return None

    def lid(self) -> str:
        """
        Parse a lower case identifier.
        """
        if m := self.branch_lid():
            return m
        self.error("expected lower case identifier")

    def parse_type(self) -> Type:
        """
        Parse a type.
        """
        if self.branch("("):
            lhs = self.parse_type()
            self.consume(")")
        elif name := self.branch_uid():
            lhs = TypeCons(name)
        else:
            name = self.lid()
            args = []
            if self.branch("("):
                if not self.branch(")"):
                    args.append(self.parse_type())
                    while self.branch(","):
                        args.append(self.parse_type())
                self.consume(")")
            lhs = FunctionCons(name, args)

        if self.branch("|"):
            rhs = self.parse_type()
            return UnionCons([lhs, rhs])
        return lhs

    def parse_type_def(self) -> TypeDef:
        """
        Parse a type definition.
        """
        lhs = self.uid()
        if self.branch(":="):
            rel = TypeRelation.EQUAL
        elif self.branch("<:"):
            rel = TypeRelation.SUBTYPE
        else:
            raise ValueError("Expected ':=' or '<:'")

        rhs = self.parse_type()

        self.consume(".")
        return TypeDef(lhs, rel, rhs)

    def _pred(self) -> tuple[str, list[Type]]:
        """
        Parse a predicate type annotation.
        """
        name = self.lid()
        args = []
        if self.branch("("):
            if not self.branch(")"):
                args.append(self.parse_type())
                while self.branch(","):
                    args.append(self.parse_type())
            self.consume(")")
        self.consume(".")
        return name, args

    def parse_pred(self) -> Predicate:
        """
        Parse a predicate type annotation.
        """
        return Predicate(*self._pred())

    def parse_prog(self) -> Program:
        """
        Parse a program type annotation.
        """
        return Program(*self._pred())

    def parse(self, spec: TypeSpec) -> None:
        """
        Parse a type specification.
        """
        self.consume("%*?", gobble=False)
        while True:
            if self.branch("type"):
                spec.add_type_def(self.parse_type_def())
            elif self.branch("pred"):
                spec.add_pred(self.parse_pred())
            elif self.branch("prog"):
                spec.add_prog(self.parse_prog())
            elif self.branch("func"):
                raise NotImplementedError("Function type annotations are not implemented yet")
            else:
                self.consume("*%", gobble=True)
                break
