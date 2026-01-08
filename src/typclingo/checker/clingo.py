"""
This module implements a type checker for Answer Set Programming (ASP) that
supports subtyping, sum types, and automatic type reconstruction. The type
system is based on a lattice structure, allowing users to define types with
subtyping relationships, sum types, and specify disjoint types. Recursive types
are intentionally not supported to keep type checking tractable and efficient.

Key Features:
- **Subtyping and Lattice Structure:** Types can be organized in a lattice,
  supporting both subtyping and disjointness. This allows for expressive type
  specifications and precise detection of type errors.
- **Sum Types:** Users can define sum types enabling explicit unions of types
  for flexible modeling.
- **No Recursive Types:** Recursive types (such as lists or trees) are not
  supported, as they significantly increase the complexity of type checking.
- **Type Inference:** The checker reconstructs types for variables
  automatically, minimizing the need for explicit type annotations.
- **Meet-Based Checking:** Instead of requiring exact type matches, the checker
  only requires that types "meet" (i.e., have a greatest lower bound in the
  lattice). If the meet of types is undefined (e.g., for disjoint types), the
  checker warns about potential bugs.
- **User Guidance:** By annotating predicates with types and specifying
  disjointness, users receive helpful warnings about suspicious variable usage,
  improving program reliability without restricting ASP's expressive power.

Further Reading:
The paper "The simple essence of algebraic subtyping: principal type inference
with subtyping made easy (functional pearl)" might give userful background how
reconstruction with subtyping and recursive types can be achieved.

TODO:
- Better diagnostics and more info about computed types.
  - Maybe compute union of predicate rules and give a summary of types used at
    the end.
- Support for more term and statement types.
- Better support for pools.
"""

from sys import stderr
from typing import Iterable

from clingo import ast
from clingo.symbol import SymbolType

from ..spec import (
    FunctionCons,
    Type,
    TypeCons,
    TypeSpec,
    TypeVar,
    UnionCons,
)
from ..utils.ast import get_global
from .core import TypeChecker

__all__ = ["check_stm"]


class ClingoChecker(TypeChecker):
    type_map: dict[str, TypeVar]
    glob: set[str]
    scope: int
    params: dict[str, Type]

    def __init__(self, spec: TypeSpec, glob: set[str], params: dict[str, Type]):
        super().__init__(spec)
        self.type_map = {}
        self.glob = glob
        self.params = params
        self.scope = 0

    def add_variable(self, name: str) -> Type:
        """
        Add a variable to the type self.

        This either returns an existing type variable for the given name or
        adds a new one. In case of anonymous variables "_", we simply use the
        most general type "Symbol".
        """
        if name == "_":
            return TypeCons("Symbol")
        if name not in self.glob:
            name = f"{name}@{self.scope}"
        return self.type_map.setdefault(name, TypeVar(name))

    def add_term(self, term: ast.Term, protect_pred: bool = False) -> Type:
        """
        Compute the type of a term.

        This function introduces type variablen and records constraints over
        them. The constraints can then be solved to obtain concrete types for
        the type variables.
        """
        if isinstance(term, ast.TermVariable):
            return self.add_variable(term.name)
        if isinstance(term, ast.TermAbsolute):
            for arg in term.pool:
                self.constraints.append((self.add_term(arg), TypeCons("Number")))
            return TypeCons("Number")
        if isinstance(term, ast.TermBinaryOperation):
            num = TypeCons("Number")
            lhs = self.add_term(term.left)
            rhs = self.add_term(term.right)
            self.constraints.append((lhs, num))
            self.constraints.append((rhs, num))
            return num
        if isinstance(term, ast.TermUnaryOperation):
            num = TypeCons("Number")
            rhs = self.add_term(term.right)
            if term.operator_type == ast.UnaryOperator.Negation:
                self.constraints.append((rhs, num))
                return num
            fun = TypeCons("Function")
            typ = UnionCons([num, fun])
            # TODO: maybe specialize for isinstance(term.right, TermFunction)
            self.constraints.append((rhs, typ))
            return typ
        if isinstance(term, ast.TermFunction):
            if term.external:
                # TODO:
                # - external functions need type annotations
                # - we can inject the return type of the function and add
                #   constraints for the arguments
                raise NotImplementedError("external functions are not supported yet")
            # NOTE:
            # - using the pool here is not the most useful way to implement this
            # - it might be better to unpool beforhand to ensure that each
            #   alternative is meaningful
            opts: list[Type] = []
            for args in term.pool:
                t_args: list[Type] = []
                for x in args.arguments:
                    if isinstance(x, ast.Projection):
                        t_args.append(TypeCons("Symbol"))
                    else:
                        t_args.append(self.add_term(x))
                if not protect_pred and not t_args and term.name in self.params:
                    opts.append(self.params[term.name])
                else:
                    opts.append(FunctionCons(term.name, t_args))
            return self.simplify_type(UnionCons(opts))
        if isinstance(term, ast.TermSymbolic):
            sym = term.symbol
            if sym.type == SymbolType.Number:
                return TypeCons("Number")
            if sym.type == SymbolType.String:
                return TypeCons("String")
            if sym.type == SymbolType.Infimum:
                return TypeCons("Infimum")
            if sym.type == SymbolType.Supremum:
                return TypeCons("Supremum")
            if sym.type == SymbolType.Tuple:
                raise NotImplementedError("tuple symbols are not supported yet")
            assert sym.type == SymbolType.Function
            if len(sym.arguments):
                # TODO:
                # - easy to implement
                raise NotImplementedError("only constants are supported for now")
            if not protect_pred and sym.name in self.params:
                return self.params[sym.name]
            return FunctionCons(sym.name, [])

        assert isinstance(term, (ast.TermFormatString, ast.TermTuple))
        # TODO:
        # - implement format strings and tuples
        # - maybe represent tuples as functions with an empty name
        raise NotImplementedError(f"unhandled term: {term}")

    def add_lit(self, lit: ast.Literal) -> None:
        """
        Add a literal to the type self.
        """
        if isinstance(lit, ast.LiteralBoolean):
            # nothing to type here
            pass
        elif isinstance(lit, ast.LiteralSymbolic):
            atom = lit.atom
            if isinstance(atom, ast.TermFunction):
                t_atom = self.add_term(atom, True)
                opts: list[Type] = []
                # NOTE: the same as in add_term applies here
                for args in atom.pool:
                    arity = len(args.arguments)
                    if pred := self.spec.get_pred(atom.name, arity):
                        opts.append(FunctionCons(pred.name, pred.args))
                    else:
                        opts.append(FunctionCons(atom.name, [TypeCons("Symbol")] * arity))
                t_pred = self.simplify_type(UnionCons(opts))
                self.constraints.append((t_atom, t_pred))
            else:
                stderr.write("Warning: symbolic terms and classically negated atoms are not yet supported\n")
        else:
            assert isinstance(lit, ast.LiteralComparison)
            t_lhs = self.add_term(lit.left)
            for guard in lit.right:
                t_rhs = self.add_term(guard.term)
                self.constraints.append((t_lhs, t_rhs))
                t_lhs = t_rhs

    def add_guards(
        self,
        aggr: ast.BodySetAggregate | ast.BodyAggregate | ast.HeadAggregate | ast.HeadSetAggregate,
        fun: ast.AggregateFunction,
    ) -> None:
        """
        Add guards for an aggregate to the type self.
        """
        t_guard = TypeCons("Number")
        if fun in (
            ast.AggregateFunction.Count,
            ast.AggregateFunction.Sum,
            ast.AggregateFunction.Sump,
        ):
            t_guard = TypeCons("Symbol")
        if lhs := aggr.left:
            self.constraints.append((self.add_term(lhs.term), t_guard))
        if rhs := aggr.right:
            self.constraints.append((self.add_term(rhs.term), t_guard))

    def add_saggr(self, aggr: ast.BodySetAggregate | ast.HeadSetAggregate) -> None:
        """
        Add a set aggregate to the type self.
        """
        self.add_guards(aggr, ast.AggregateFunction.Count)
        for elem in aggr.elements:
            self.add_lit(elem.literal)
            for lit in elem.condition:
                self.add_lit(lit)
            self.scope += 1

    def add_blit(self, blit: ast.BodyLiteral) -> None:
        """
        Add a body literal to the type self.
        """
        if isinstance(blit, ast.BodyConditionalLiteral):
            self.add_lit(blit.literal)
            for lit in blit.condition:
                self.add_lit(lit)
            self.scope += 1
        elif isinstance(blit, ast.BodySetAggregate):
            self.add_saggr(blit)
        elif isinstance(blit, ast.BodyAggregate):
            self.add_guards(blit, blit.function)
            for elem in blit.elements:
                for term in elem.tuple:
                    self.constraints.append((self.add_term(term), TypeCons("Symbol")))
                for lit in elem.condition:
                    self.add_lit(lit)
                self.scope += 1
        elif isinstance(blit, ast.BodySimpleLiteral):
            self.add_lit(blit.literal)
        else:
            assert isinstance(blit, ast.BodyTheoryAtom)
            stderr.write("Warning: theory atoms are not yet supported\n")

    def add_hlit(self, hlit: ast.HeadLiteral) -> None:
        """
        Add a head literal to the type self.
        """
        if isinstance(hlit, ast.HeadSimpleLiteral):
            self.add_lit(hlit.literal)
        elif isinstance(hlit, ast.HeadDisjunction):
            for delem in hlit.elements:
                if isinstance(delem, ast.HeadConditionalLiteral):
                    self.add_lit(delem.literal)
                    for lit in delem.condition:
                        self.add_lit(lit)
                    self.scope += 1
                else:
                    self.add_lit(delem)
        elif isinstance(hlit, ast.HeadAggregate):
            self.add_guards(hlit, hlit.function)
            for helem in hlit.elements:
                for term in helem.tuple:
                    self.constraints.append((self.add_term(term), TypeCons("Symbol")))
                self.add_lit(helem.literal)
                for lit in helem.condition:
                    self.add_lit(lit)
                self.scope += 1
        elif isinstance(hlit, ast.HeadSetAggregate):
            self.add_saggr(hlit)
        else:
            isinstance(hlit, ast.HeadTheoryAtom)
            stderr.write("Warning: theory atoms are not yet supported\n")


class ParamHolder:
    """
    Simple holder for program and constant parameters.
    """

    prog_params: dict[str, Type]

    def __init__(self, spec: TypeSpec, consts: list[ast.StatementConst]):
        self.prog_params = {}
        self.const_params = {}

        # extract relevant constant parameters
        params: dict[str, tuple[ast.Term, int]] = {}
        for const in consts:
            if const.name in params:
                p = params[const.name][1]
                if p == const.precedence:
                    stderr.write("Error: conflicting constant parameter definitions\n")
                elif p < const.precedence:
                    params[const.name] = (const.value, const.precedence)
            else:
                params[const.name] = (const.value, const.precedence)

        # compute types for constant parameters
        tvars: dict[str, Type] = {}
        for name in params:
            tvars[name] = TypeVar(name)
        checker = ClingoChecker(spec, set(), tvars)
        for name, (value, _) in params.items():
            checker.constraints.append((tvars[name], checker.add_term(value)))
        checker.solve()
        if tvars:
            print("***** Checking const statements ******")
            for name, typ in tvars.items():
                typ = checker.simplify_type(checker.expand_type(typ))
                print(f"{name} : {typ}")
                self.const_params[name] = typ

    def set_prog(self, params: Iterable[tuple[str, Type]]) -> None:
        """
        Set current program parameters.
        """
        self.prog_params.clear()
        self.prog_params.update(params)

    def get_params(self) -> dict[str, Type]:
        """
        Get all parameters.
        """
        params = self.const_params.copy()
        params.update(self.prog_params)
        return params


def check_stm(spec: TypeSpec, params: ParamHolder, stm: ast.Statement) -> None:
    """
    Add a statement to the type self.
    """
    if isinstance(
        stm,
        (
            ast.StatementShowSignature,
            ast.StatementShowNothing,
            ast.StatementProjectSignature,
            ast.StatementConst,
        ),
    ):
        # nothing to check here
        pass
    elif isinstance(stm, ast.StatementProgram):
        if prog := spec.get_prog(stm.name, len(stm.arguments)):
            params.set_prog(zip(stm.arguments, prog.args))
        else:
            params.set_prog(zip(stm.arguments, [TypeCons("Symbol")] * len(stm.arguments)))
    elif isinstance(stm, ast.StatementShow):
        print("***** Checking show statement ******")
        glob = get_global(stm)
        checker = ClingoChecker(spec, glob, params.get_params())
        checker.constraints.append((checker.add_term(stm.term), TypeCons("Symbol")))
        for blit in stm.body:
            checker.add_blit(blit)
        checker.solve()
        print(f"{stm}")
        print("inferred types:")
        for name, typ in checker.type_map.items():
            print(f"  {name} : {checker.simplify_type(checker.expand_type(typ))}")

    elif isinstance(stm, ast.StatementRule):
        print("********** Checking rule ***********")
        glob = get_global(stm)
        checker = ClingoChecker(spec, glob, params.get_params())
        checker.add_hlit(stm.head)
        for blit in stm.body:
            checker.add_blit(blit)
        checker.solve()
        print(f"{stm}")
        print("inferred types:")
        for name, typ in checker.type_map.items():
            print(f"  {name} : {checker.simplify_type(checker.expand_type(typ))}")
    else:
        # TODO: it should be simple to add more statement types here
        stderr.write("Warning: only a limited set of statements is supported\n")
