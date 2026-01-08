"""
Main application module for TypeClingo.
"""

from clingo.core import Library
from clingo import ast

from .spec import TypeSpec
from .parser import Parser
from .checker.clingo import check_stm

__all__ = ["TypeClingo"]


class TypeClingo:
    """
    The main type clingo class.
    """

    spec: TypeSpec
    stms: list[ast.Statement]

    def __init__(self) -> None:
        self.spec = TypeSpec()
        self.stms = []

    def _stm(self, stm: ast.Statement) -> None:
        """
        Callback for processing statements.
        """
        if isinstance(stm, ast.StatementComment):
            if stm.comment_type == ast.CommentType.Block and stm.value.startswith(
                "%*?"
            ):
                Parser(stm.value).parse(self.spec)
        else:
            self.stms.append(stm)

    def run(self) -> None:
        """
        Run typecling on input files.
        """
        lib = Library()
        ast.parse_files(lib, [], self._stm)
        self.spec.check()

        print("*** Extracted Type Specification ***")
        print(self.spec)

        for rule in self.stms:
            check_stm(self.spec, rule)
