"""
Type specification for typclingo.
"""

from dataclasses import dataclass, field
from enum import Enum
from functools import singledispatch

__all__ = [
    "BOT",
    "External",
    "FunctionCons",
    "Predicate",
    "Program",
    "Type",
    "TypeCons",
    "TypeDef",
    "TypeRelation",
    "TypeSpec",
    "TypeVar",
    "UnionCons",
]


@dataclass
class TypeCons:
    """
    A type constructor.

    A type constructor is just a name. It has to be defined by a type
    definition, which defines the relation of the type constructor to other
    types.

    The following type constructors are predefined:
    - Top: The internal top type (supertype of all types; defined cyclically)
    - Infimum: The type of the #inf symbol (suptype of Top)
    - Supremum: The type of the #sup symbol (suptype of Top)
    - Number: The type of all numbers (suptype of Top)
    - String: The type of all strings (suptype of Top)
    - Tuple: The type of all tuples (suptype of Top)
    - Function: The type of all functions (includes constants; subtype of Top).
    - Symbol: The type of all symbols (the union of the above types).

    # TODO
    More inbuild subtypes might be introduced in the future, e.g., for natural
    numbers, signed/unsigned functions, etc.
    """

    name: str

    def __str__(self) -> str:
        return self.name


@dataclass
class TypeVar:
    """
    A type variable for an unknown type.

    This is a placeholder for a type that is not yet known. Type variables can
    express that two or more variables are of the same unknown type. Any
    unconstrained type variable can be instantiated to any type: after type
    checking, they can be replaced by TypeCons("Symbol").
    """

    name: str

    def __str__(self) -> str:
        return f"${self.name}"


@dataclass
class FunctionCons:
    """
    A function type constructor.

    A function type constructor has a name and zero or more type arguments. It
    must be associated with a type constructor via a type definition.

    # TODO
    Maybe nesting of constructors shoudl be allowed here to write more compact
    types? Currently, types definitions have to be flat but nesting types can
    of course be represented via multiple definitions.
    """

    name: str
    args: list["Type"]

    def __str__(self) -> str:
        if self.args:
            return f"{self.name}(" + ",".join(str(a) for a in self.args) + ")"
        return f"{self.name}"


@dataclass
class UnionCons:
    """
    A union type constructor.

    A union type constructor represents the union of multiple type
    constructors.
    """

    opts: list["Type"]

    def __str__(self) -> str:
        return "(" + " | ".join(str(o) for o in self.opts) + ")"


BOT = UnionCons([])

type Type = TypeCons | FunctionCons | UnionCons | TypeVar


class TypeRelation(Enum):
    """
    A type relation.

    Eihter equality or subtyping.
    """

    EQUAL = 1
    SUBTYPE = 2

    def __str__(self) -> str:
        return ":=" if self == TypeRelation.EQUAL else "<:"


@dataclass
class TypeDef:
    """
    A type definition.

    A type has a name, a relation (either equality or subtyping), and
    a list of constructors (either type constructors or function constructors).
    """

    name: str
    rel: TypeRelation
    type: Type

    def __str__(self) -> str:
        return f"type {self.name} {self.rel} {self.type}."


@dataclass
class Predicate:
    """
    Type annotation for a predicate.

    A predicate has a name and zero or more type arguments.
    """

    name: str
    args: list[Type]

    def __str__(self) -> str:
        if self.args:
            return f"pred {self.name}(" + ",".join(str(a) for a in self.args) + ")."
        return f"pred {self.name}."


@dataclass
class External:
    """
    Type annotation for an external function.

    An external function has a name, zero or more type arguments, and a result
    type.
    """

    name: str
    args: list[Type]
    result: Type

    def __str__(self) -> str:
        return f"func {self.name}({','.join(str(a) for a in self.args)}) -> {str(self.result)}."


@dataclass
class Program:
    """
    Type annotation for a program part.

    A program part has a name and zero or more type arguments.
    """

    name: str
    args: list[Type]

    def __str__(self) -> str:
        if self.args:
            return f"prog {self.name}(" + ",".join(str(a) for a in self.args) + ")."
        return f"prog {self.name}."


class Graph:
    """
    A simple directed graph to check for cycles.
    """

    edges: dict[str, set[str]]

    def __init__(self) -> None:
        self.edges = {}

    def add_edge(self, src: str, dst: str) -> None:
        """
        Add a directed edge from src to dst.
        """
        self.edges.setdefault(src, set()).add(dst)

    def check_acyclic(self) -> None:
        """
        Check that the graph is acyclic.

        This could be refined to provide all types involved in the cycle.
        """
        visited = set()
        stack = set()

        def visit(node: str) -> None:
            if node in stack:
                raise ValueError(f"Cycle detected in type definitions at '{node}'")
            if node not in visited:
                stack.add(node)
                for neighbor in self.edges.get(node, []):
                    visit(neighbor)
                stack.remove(node)
                visited.add(node)

        for node in self.edges:
            visit(node)


@dataclass
class TypeSpec:
    """
    A type specification.
    """

    @staticmethod
    def _default_types() -> dict[str, TypeDef]:
        # NOTE: cyclic definition are intentional here
        top = TypeDef("Top", TypeRelation.SUBTYPE, TypeCons("Top"))
        num = TypeDef("Number", TypeRelation.SUBTYPE, TypeCons("Top"))
        fun = TypeDef("Function", TypeRelation.SUBTYPE, TypeCons("Top"))
        tup = TypeDef("Tuple", TypeRelation.SUBTYPE, TypeCons("Top"))
        inf = TypeDef("Infimum", TypeRelation.SUBTYPE, TypeCons("Top"))
        sup = TypeDef("Supremum", TypeRelation.SUBTYPE, TypeCons("Top"))
        string = TypeDef("String", TypeRelation.SUBTYPE, TypeCons("Top"))
        sym = TypeDef(
            "Symbol",
            TypeRelation.EQUAL,
            UnionCons(
                [
                    TypeCons("Number"),
                    TypeCons("Function"),
                    TypeCons("Tuple"),
                    TypeCons("Infimum"),
                    TypeCons("Supremum"),
                    TypeCons("String"),
                ]
            ),
        )
        return {
            top.name: top,
            sym.name: sym,
            num.name: num,
            fun.name: fun,
            tup.name: tup,
            inf.name: inf,
            sup.name: sup,
            string.name: string,
        }

    _types: dict[str, TypeDef] = field(default_factory=_default_types)
    _preds: dict[tuple[str, int], Predicate] = field(default_factory=dict)
    _progs: dict[tuple[str, int], Program] = field(default_factory=dict)
    _funcs: dict[tuple[str, int], External] = field(default_factory=dict)

    def add_type_def(self, td: TypeDef) -> None:
        """
        Add a type definition.
        """
        if td.name in self._types:
            raise ValueError(f"Type '{td.name}' already defined")
        self._types[td.name] = td

    def add_pred(self, pred: Predicate) -> None:
        """
        Add a predicate type annotation.
        """
        signature = (pred.name, len(pred.args))
        if signature in self._preds:
            raise ValueError(f"Predicate '{pred.name}/{len(pred.args)}' already defined")
        self._preds[signature] = pred

    def add_prog(self, prog: Program) -> None:
        """
        Add a program type annotation.
        """
        signature = (prog.name, len(prog.args))
        if signature in self._progs:
            raise ValueError(f"Program '{prog.name}/{len(prog.args)}' already defined")
        self._progs[signature] = prog

    def add_func(self, func: External) -> None:
        """
        Add an external function type annotation.
        """
        signature = (func.name, len(func.args))
        if signature in self._progs:
            raise ValueError(f"External function '{func.name}/{len(func.args)}' already defined")
        self._funcs[signature] = func

    def get_type_def(self, name: str) -> TypeDef:
        """
        Get the type definition for the given name.
        """
        if name not in self._types:
            raise ValueError(f"Type '{name}' not defined")
        return self._types[name]

    def get_pred(self, name: str, arity: int) -> Predicate | None:
        """
        Get the predicate type annotation for the given name and arity.
        """
        return self._preds.get((name, arity), None)

    def get_prog(self, name: str, arity: int) -> Program | None:
        """
        Get the program type annotation for the given name and arity.
        """
        return self._progs.get((name, arity), None)

    def get_func(self, name: str, arity: int) -> External | None:
        """
        Get the external function type annotation for the given name and arity.
        """
        return self._funcs.get((name, arity), None)

    def check(self) -> None:
        """
        Check the type specification for consistency.
        """

        graph = Graph()
        parent = "Top"

        @singledispatch
        def dispatch(t: Type) -> None:
            print(f"type: {t}, {type(t)}")
            assert t
            raise NotImplementedError()

        @dispatch.register
        def _(t: TypeCons) -> None:
            if t.name not in self._types:
                raise ValueError(f"Type '{t.name}' not defined")
            # we skip symbol here because they are cyclically defined
            if parent != "Top":
                graph.add_edge(parent, t.name)

        @dispatch.register
        def _(t: UnionCons) -> None:
            for x in t.opts:
                dispatch(x)

        @dispatch.register
        def _(t: FunctionCons) -> None:
            for x in t.args:
                dispatch(x)

        for td in self._types.values():
            parent = td.name
            dispatch(td.type)

        graph.check_acyclic()

        for pd in self._preds.values():
            # this avoids adding edges for predicates
            parent = "Top"
            for x in pd.args:
                dispatch(x)

    def __str__(self) -> str:
        return "\n".join(
            str(t) for t in list(self._types.values()) + list(self._progs.values()) + list(self._preds.values())
        )
