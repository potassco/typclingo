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

from clingo.symbol import SymbolType
from clingo import ast

from ..utils.ast import get_global
from ..spec import (
    TypeSpec,
    Type,
    FunctionCons,
    TypeCons,
    UnionCons,
)
from .core import TypeChecker

__all__ = ["check_stm"]


def add_term(checker: TypeChecker, term: ast.Term) -> Type:
    """
    Compute the type of a term.

    This function introduces type variablen and records constraints over
    them. The constraints can then be solved to obtain concrete types for
    the type variables.
    """
    if isinstance(term, ast.TermVariable):
        return checker.add_variable(term.name)
    if isinstance(term, ast.TermAbsolute):
        for arg in term.pool:
            checker.constraints.append((add_term(checker, arg), TypeCons("Number")))
        return TypeCons("Number")
    if isinstance(term, ast.TermBinaryOperation):
        num = TypeCons("Number")
        lhs = add_term(checker, term.left)
        rhs = add_term(checker, term.right)
        checker.constraints.append((lhs, num))
        checker.constraints.append((rhs, num))
        return num
    if isinstance(term, ast.TermUnaryOperation):
        num = TypeCons("Number")
        rhs = add_term(checker, term.right)
        if term.operator_type == ast.UnaryOperator.Negation:
            checker.constraints.append((rhs, num))
            return num
        fun = TypeCons("Function")
        typ = UnionCons([num, fun])
        # TODO: maybe specialize for isinstance(term.right, TermFunction)
        checker.constraints.append((rhs, typ))
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
                    t_args.append(add_term(checker, x))
            opts.append(FunctionCons(term.name, t_args))
        return checker.simplify_type(UnionCons(opts))
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
        return FunctionCons(sym.name, [])

    assert isinstance(term, (ast.TermFormatString, ast.TermTuple))
    # TODO:
    # - implement format strings and tuples
    # - maybe represent tuples as functions with an empty name
    raise NotImplementedError(f"unhandled term: {term}")


def add_lit(checker: TypeChecker, lit: ast.Literal) -> None:
    """
    Add a literal to the type checker.
    """
    if isinstance(lit, ast.LiteralBoolean):
        # nothing to type here
        pass
    elif isinstance(lit, ast.LiteralSymbolic):
        atom = lit.atom
        if isinstance(atom, ast.TermFunction):
            t_atom = add_term(checker, atom)
            opts: list[Type] = []
            # NOTE: the same as in add_term applies here
            for args in atom.pool:
                arity = len(args.arguments)
                if pred := checker.spec.get_pred(atom.name, arity):
                    opts.append(FunctionCons(pred.name, pred.args))
                else:
                    opts.append(FunctionCons(atom.name, [TypeCons("Symbol")] * arity))
            t_pred = checker.simplify_type(UnionCons(opts))
            checker.constraints.append((t_atom, t_pred))
        else:
            stderr.write(
                "Warning: symbolic terms and classically negated atoms are not yet supported\n"
            )
    else:
        assert isinstance(lit, ast.LiteralComparison)
        t_lhs = add_term(checker, lit.left)
        for guard in lit.right:
            t_rhs = add_term(checker, guard.term)
            checker.constraints.append((t_lhs, t_rhs))
            t_lhs = t_rhs


def add_guards(
    checker: TypeChecker,
    aggr: ast.BodySetAggregate
    | ast.BodyAggregate
    | ast.HeadAggregate
    | ast.HeadSetAggregate,
    fun: ast.AggregateFunction,
) -> None:
    """
    Add guards for an aggregate to the type checker.
    """
    t_guard = TypeCons("Number")
    if fun in (
        ast.AggregateFunction.Count,
        ast.AggregateFunction.Sum,
        ast.AggregateFunction.Sump,
    ):
        t_guard = TypeCons("Symbol")
    if lhs := aggr.left:
        checker.constraints.append((add_term(checker, lhs.term), t_guard))
    if rhs := aggr.right:
        checker.constraints.append((add_term(checker, rhs.term), t_guard))


def add_saggr(
    checker: TypeChecker, aggr: ast.BodySetAggregate | ast.HeadSetAggregate
) -> None:
    """
    Add a set aggregate to the type checker.
    """
    add_guards(checker, aggr, ast.AggregateFunction.Count)
    for elem in aggr.elements:
        add_lit(checker, elem.literal)
        for lit in elem.condition:
            add_lit(checker, lit)
        checker.scope += 1


def add_blit(checker: TypeChecker, blit: ast.BodyLiteral) -> None:
    """
    Add a body literal to the type checker.
    """
    if isinstance(blit, ast.BodyConditionalLiteral):
        add_lit(checker, blit.literal)
        for lit in blit.condition:
            add_lit(checker, lit)
        checker.scope += 1
    elif isinstance(blit, ast.BodySetAggregate):
        add_saggr(checker, blit)
    elif isinstance(blit, ast.BodyAggregate):
        add_guards(checker, blit, blit.function)
        for elem in blit.elements:
            for term in elem.tuple:
                checker.constraints.append(
                    (add_term(checker, term), TypeCons("Symbol"))
                )
            for lit in elem.condition:
                add_lit(checker, lit)
            checker.scope += 1
    elif isinstance(blit, ast.BodySimpleLiteral):
        add_lit(checker, blit.literal)
    else:
        assert isinstance(blit, ast.BodyTheoryAtom)
        stderr.write("Warning: theory atoms are not yet supported\n")


def add_hlit(checker: TypeChecker, hlit: ast.HeadLiteral) -> None:
    """
    Add a head literal to the type checker.
    """
    if isinstance(hlit, ast.HeadSimpleLiteral):
        add_lit(checker, hlit.literal)
    elif isinstance(hlit, ast.HeadDisjunction):
        for delem in hlit.elements:
            if isinstance(delem, ast.HeadConditionalLiteral):
                add_lit(checker, delem.literal)
                for lit in delem.condition:
                    add_lit(checker, lit)
                checker.scope += 1
            else:
                add_lit(checker, delem)
    elif isinstance(hlit, ast.HeadAggregate):
        add_guards(checker, hlit, hlit.function)
        for helem in hlit.elements:
            for term in helem.tuple:
                checker.constraints.append(
                    (add_term(checker, term), TypeCons("Symbol"))
                )
            add_lit(checker, helem.literal)
            for lit in helem.condition:
                add_lit(checker, lit)
            checker.scope += 1
    elif isinstance(hlit, ast.HeadSetAggregate):
        add_saggr(checker, hlit)
    else:
        isinstance(hlit, ast.HeadTheoryAtom)
        stderr.write("Warning: theory atoms are not yet supported\n")


def check_stm(spec: TypeSpec, stm: ast.Statement) -> None:
    """
    Add a statement to the type checker.
    """
    if isinstance(
        stm,
        (
            ast.StatementShowSignature,
            ast.StatementShowNothing,
            ast.StatementProjectSignature,
        ),
    ):
        # nothing to checke here
        pass
    elif isinstance(stm, ast.StatementProgram):
        if stm.arguments:
            # TODO: program statements are more tricky to handle
            # - need to extend type specification
            # - when mapping terms to types, program parameters need to be
            #   considered
            stderr.write("Warning: program statements are not yet supported\n")
    elif isinstance(stm, ast.StatementShow):
        print("***** Checking show statement ******")
        glob = get_global(stm)
        checker = TypeChecker(spec, glob)
        checker.constraints.append((add_term(checker, stm.term), TypeCons("Symbol")))
        for blit in stm.body:
            add_blit(checker, blit)
        checker.solve()
        print(f"  {stm}")
        print("  inferred types:")
        for name, typ in checker.type_map.items():
            print(f"    {name} : {checker.simplify_type(checker.expand_type(typ))}")

    elif isinstance(stm, ast.StatementRule):
        print("********** Checking rule ***********")
        glob = get_global(stm)
        checker = TypeChecker(spec, glob)
        add_hlit(checker, stm.head)
        for blit in stm.body:
            add_blit(checker, blit)
        checker.solve()
        print(f"  {stm}")
        print("  inferred types:")
        for name, typ in checker.type_map.items():
            print(f"    {name} : {checker.simplify_type(checker.expand_type(typ))}")
    else:
        # TODO: it should be simple to add more statement types here
        stderr.write("Warning: only a limited set of statements is supported\n")
