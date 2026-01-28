"""
This module implements a type checker for Answer Set Programming that supports
subtyping, sum types, and automatic type reconstruction. The type system is
based on a lattice structure, allowing users to define types with subtyping
relationships, sum types, and specify disjoint types. Recursive types are
intentionally not supported to keep type checking tractable and efficient.

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

import logging
from functools import singledispatchmethod

from ..spec import (
    BOT,
    FUNCTION,
    INFIMUM,
    NUMBER,
    STRING,
    SUPREMUM,
    SYMBOL,
    TOP,
    TUPLE,
    FunctionCons,
    Type,
    TypeCons,
    TypeRelation,
    TypeSpec,
    TypeVar,
    UnionCons,
)

__all__ = ["TypeChecker"]
logger = logging.getLogger(__name__)


def func_type(fun: FunctionCons):
    """
    Get the general type of a function term.
    """
    return TUPLE if fun.name == "" else FUNCTION


class TypeChecker:
    """
    A type checker for ASP programs.

    The type checker uses a type specification to check types of previously
    added constraints.
    """

    constraints: list[tuple[Type, Type]]
    spec: TypeSpec
    env: dict[str, Type]

    def __init__(self, spec: TypeSpec):
        self.constraints = []
        self.spec = spec
        self.env = {}

    def simplify_type(self, x: Type) -> Type:
        """
        Flatten a type by merging nested unions.
        """
        if isinstance(x, UnionCons):
            opts: list[Type] = []
            for y in x.opts:
                y = self.simplify_type(y)
                if isinstance(y, UnionCons):
                    opts.extend(y.opts)
                else:
                    opts.append(y)

            n = len(opts)
            while n > 0:
                nxt = []
                for y in opts[1:]:
                    if not self.subtype(y, opts[0], {}):
                        nxt.append(y)
                    else:
                        n -= 1
                nxt.append(opts[0])
                n -= 1
                opts = nxt

            if len(opts) == 1:
                return opts[0]
            return UnionCons(opts)

        if isinstance(x, FunctionCons):
            res = FunctionCons(x.name, [self.simplify_type(a) for a in x.args])
            return res if all(a != BOT for a in res.args) else BOT

        return x

    def expand_type(self, t: Type) -> Type:
        """
        Expand type variables in the given type using the environment.
        """
        if isinstance(t, TypeVar):
            return self.expand_type(self.env.get(t.name, SYMBOL))
        if isinstance(t, UnionCons):
            return UnionCons([self.expand_type(x) for x in t.opts])
        if isinstance(t, FunctionCons):
            return FunctionCons(t.name, [self.expand_type(x) for x in t.args])
        return t

    @singledispatchmethod
    def subtype(self, lhs: Type, rhs: Type, env: dict[str, Type]) -> bool:
        """
        Check whether lhs is a subtype of rhs.

        Note that types are never considered subtypes of type variables here,
        as type variables might be refined later.

        A type var can however be a subtype of another type if it is associated
        with a subtype of that type in the environment.
        """
        if lhs == rhs:
            return True

        if isinstance(rhs, TypeVar):
            return False

        if isinstance(lhs, TypeVar):
            return self.subtype(env.get(lhs.name, SYMBOL), rhs, env)

        if isinstance(rhs, UnionCons):
            return any(self.subtype(lhs, x, env) for x in rhs.opts)

        if isinstance(lhs, UnionCons):
            return all(self.subtype(x, rhs, env) for x in lhs.opts)

        if isinstance(lhs, FunctionCons) and isinstance(rhs, TypeCons):
            if rhs in (TOP, func_type(lhs)):
                return True
            td = self.spec.get_type_def(rhs.name)
            return td.rel == TypeRelation.EQUAL and self.subtype(lhs, td.type, env)

        if isinstance(lhs, FunctionCons) and isinstance(rhs, FunctionCons):
            return (
                lhs.name == rhs.name
                and len(lhs.args) == len(rhs.args)
                and all(self.subtype(x, y, env) for x, y in zip(lhs.args, rhs.args))
            )

        assert isinstance(lhs, TypeCons)

        # unfold lhs type definition
        td_lhs = self.spec.get_type_def(lhs.name)
        if lhs != TOP:
            # check transitively first
            if self.subtype(td_lhs.type, rhs, env):
                return True

            # if lhs is equal to its type definition, we already checked
            # everything
            if td_lhs.rel == TypeRelation.EQUAL:
                return False

        assert lhs == TOP or td_lhs.rel == TypeRelation.SUBTYPE

        if isinstance(rhs, TypeCons):
            if rhs in (TOP, lhs):
                return True
            td_rhs = self.spec.get_type_def(rhs.name)
            return td_rhs.rel == TypeRelation.EQUAL and self.subtype(lhs, td_rhs.type, env)

        assert isinstance(rhs, (UnionCons, FunctionCons))
        return isinstance(rhs, UnionCons) and any(self.subtype(lhs, x, env) for x in rhs.opts)

    def reachable_supertype(self, lhs: Type, rhs: TypeCons) -> bool:
        """
        Check if we can reach rhs by unfolding type definitions in lhs.
        """
        if rhs in (TOP, SYMBOL):
            return True

        if lhs == TOP:
            return False

        if isinstance(lhs, TypeCons):
            if lhs == rhs:
                return True
            td_lhs = self.spec.get_type_def(lhs.name)
            return self.reachable_supertype(td_lhs.type, rhs)

        if isinstance(lhs, UnionCons):
            return any(self.reachable_supertype(x, rhs) for x in lhs.opts)

        if isinstance(lhs, FunctionCons):
            return rhs == func_type(lhs)

        assert False

    def meet(self, lhs: Type, rhs: Type, env: dict[str, Type]) -> Type:
        """
        Compute the meet of two types.

        This works a bit like the type unification algorithm, but instead of
        requiring types to be equal, we only require that they have a meet. The
        algorithms refines type variables (initially assumed to be Symbol)
        while it proceeds.

        For example, the constraints [$X=Symbol, $X=Number] are satisfiable
        with $X=Number. The type variable X is refined when computing the meet
        of Symbol and Number.
        """
        if logger.isEnabledFor(logging.DEBUG):
            slhs = str(lhs)
            srhs = str(rhs)
        else:
            slhs = srhs = ""

        def debug(res: Type) -> Type:
            logger.debug("    %s ⊓ %s = %s", slhs, srhs, res)
            return res

        if isinstance(rhs, TypeCons):
            td = self.spec.get_type_def(rhs.name)
            if rhs == TOP:
                return debug(lhs)
            if td.rel == TypeRelation.EQUAL:
                return debug(self.meet(lhs, td.type, env))

        if isinstance(lhs, TypeCons):
            td = self.spec.get_type_def(lhs.name)
            if lhs == TOP:
                return debug(rhs)
            if td.rel == TypeRelation.EQUAL:
                return debug(self.meet(td.type, rhs, env))

        if isinstance(rhs, UnionCons):
            opts = []
            sub = []
            for opt in rhs.opts:
                sub.append(env.copy())
                opts.append(self.simplify_type(self.meet(opt, lhs, sub[-1])))
                if opts[-1] == BOT:
                    opts.pop()
                    sub.pop()

            # merge subenvironments
            for subenv in sub:
                for name, new in subenv.items():
                    old = env.get(name, None)
                    if old is None:
                        env[name] = new
                    elif old != new:
                        env[name] = self.simplify_type(UnionCons([old, new]))

            return debug(self.simplify_type(UnionCons(opts)))

        if isinstance(rhs, TypeVar):
            t_rhs = env.get(rhs.name, SYMBOL)
            res = self.meet(lhs, t_rhs, env)
            env[rhs.name] = res
            return debug(res)

        if isinstance(lhs, (TypeVar, UnionCons)):
            return self.meet(rhs, lhs, env)

        if isinstance(rhs, TypeCons):
            td_rhs = self.spec.get_type_def(rhs.name)
            assert td_rhs.rel != TypeRelation.EQUAL
            if isinstance(lhs, TypeCons):
                td_lhs = self.spec.get_type_def(lhs.name)
                assert td_lhs.rel != TypeRelation.EQUAL
                if self.reachable_supertype(rhs, lhs):
                    return debug(rhs)
                if self.reachable_supertype(lhs, rhs):
                    return debug(lhs)
                return BOT
            assert isinstance(lhs, FunctionCons)

            if rhs in (SYMBOL, func_type(lhs), TOP):
                return debug(lhs)
            if rhs in (NUMBER, STRING, INFIMUM, SUPREMUM, TUPLE, FUNCTION, TUPLE):
                return debug(BOT)
            if self.meet(lhs, td_rhs.type, env) != BOT:
                return debug(rhs)
            return debug(BOT)

        if isinstance(lhs, TypeCons):
            return self.meet(rhs, lhs, env)

        assert isinstance(lhs, FunctionCons) and isinstance(rhs, FunctionCons)
        if lhs.name != rhs.name or len(lhs.args) != len(rhs.args):
            return debug(BOT)
        args = [self.meet(a, b, env) for a, b in zip(lhs.args, rhs.args)]
        if any(a == BOT for a in args):
            return debug(BOT)
        return debug(FunctionCons(lhs.name, args))

    def solve(self) -> bool:
        """
        Solve previously recorded type constraints.

        Can be used incrementally after adding constraints.
        """
        res = True
        for lhs, rhs in self.constraints:
            logger.debug("  solving type constraint: %s ⊓ %s", lhs, rhs)
            if self.simplify_type(self.meet(lhs, rhs, self.env)) == BOT:
                res = False
                logger.error("unsolvable type constraints: %s = %s", lhs, rhs)

        return res
