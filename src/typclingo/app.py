"""
Main application module for TypeClingo.
"""

from clingo import ast
from clingo.core import Library

from .checker.clingo import ParamHolder, check_stm
from .parser import Parser
from .spec import TypeSpec

__all__ = ["TypeClingo"]


class TypeClingo:
    """
    The main type clingo class.
    """

    spec: TypeSpec
    stms: list[ast.Statement]
    consts: list[ast.StatementConst]

    def __init__(self) -> None:
        self.spec = TypeSpec()
        self.stms = []
        self.consts = []

    def _stm(self, stm: ast.Statement) -> None:
        """
        Callback for processing statements.
        """
        if isinstance(stm, ast.StatementConst):
            self.consts.append(stm)
        elif isinstance(stm, ast.StatementComment):
            if stm.comment_type == ast.CommentType.Block and stm.value.startswith("%*?"):
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

        params = ParamHolder(self.spec, self.consts)

        for rule in self.stms:
            check_stm(self.spec, params, rule)
