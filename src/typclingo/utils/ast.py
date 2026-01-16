"""
Utilities for typclingo.
"""

from functools import singledispatch
from typing import Any

from clingo import ast

__all__ = ["get_global"]


@singledispatch
def _get_global(stm: Any, variables: set[str]) -> None:
    stm.visit(_get_global, variables)


@_get_global.register(ast.TermVariable)
@_get_global.register(ast.TheoryTermVariable)
def _(term: Any, variables: set[str]) -> None:
    variables.add(term.name)


@_get_global.register(ast.HeadDisjunction)
@_get_global.register(ast.BodyConditionalLiteral)
@_get_global.register(ast.StatementOptimize)
def _(lit: Any, variables: set[str]) -> None:
    assert lit and variables is not None


@_get_global.register(ast.BodyAggregate)
@_get_global.register(ast.BodySetAggregate)
@_get_global.register(ast.HeadAggregate)
@_get_global.register(ast.HeadSetAggregate)
def _(lit: Any, variables: set[str]) -> None:
    if lit.left:
        _get_global(lit.left, variables)
    if lit.right:
        _get_global(lit.right, variables)


@_get_global.register(ast.HeadTheoryAtom)
@_get_global.register(ast.BodyTheoryAtom)
def _(lit: Any, variables: set[str]) -> None:
    _get_global(lit.name, variables)
    if lit.right:
        _get_global(lit.right, variables)


def get_global(stm: ast.Statement) -> set[str]:
    """
    Get the global variables in the given statement.
    """
    variables: set[str] = set()
    _get_global(stm, variables)
    return variables
