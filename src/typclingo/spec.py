"""
Type specification for typclingo.
"""

from dataclasses import dataclass, field
from enum import Enum
from functools import singledispatch

__all__ = [
    "BOT",
    "TOP",
    "SYMBOL",
    "FUNCTION",
    "INFIMUM",
    "SUPREMUM",
    "NUMBER",
    "STRING",
    "TUPLE",
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
    A function or tuple type constructor.

    A function type constructor has a name and zero or more type arguments. It
    must be associated with a type constructor via a type definition.

    Tuples are also represented as function type constructors with an empty
    name.
    """

    name: str
    args: list["Type"]

    def __str__(self) -> str:
        if self.name == "" and len(self.args) == 1:
            return f"({self.args[0]},)"
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
TOP = TypeCons("Top")
SYMBOL = TypeCons("Symbol")
FUNCTION = TypeCons("Function")
INFIMUM = TypeCons("Infimum")
SUPREMUM = TypeCons("Supremum")
NUMBER = TypeCons("Number")
STRING = TypeCons("String")
TUPLE = TypeCons("Tuple")

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


@dataclass
class TypeSpec:
    """
    A type specification.
    """

    @staticmethod
    def _default_types() -> dict[str, TypeDef]:
        # NOTE: cyclic definition are intentional here
        top = TypeDef(TOP.name, TypeRelation.SUBTYPE, TOP)
        num = TypeDef(NUMBER.name, TypeRelation.SUBTYPE, TOP)
        fun = TypeDef(FUNCTION.name, TypeRelation.SUBTYPE, TOP)
        tup = TypeDef(TUPLE.name, TypeRelation.SUBTYPE, TOP)
        inf = TypeDef(INFIMUM.name, TypeRelation.SUBTYPE, TOP)
        sup = TypeDef(SUPREMUM.name, TypeRelation.SUBTYPE, TOP)
        string = TypeDef(STRING.name, TypeRelation.SUBTYPE, TOP)
        sym = TypeDef(
            SYMBOL.name,
            TypeRelation.EQUAL,
            UnionCons([NUMBER, FUNCTION, TUPLE, INFIMUM, SUPREMUM, STRING]),
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
    _preds: dict[tuple[str, int], list[Predicate]] = field(default_factory=dict)
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
        self._preds.setdefault(signature, []).append(pred)

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

    def get_preds(self, name: str, arity: int) -> list[Predicate]:
        """
        Get the predicate type annotations for the given name and arity.
        """
        return self._preds.get((name, arity), [])

    def get_pred_type(self, name: str, arity: int) -> Type:
        """
        Get the predicate type annotation for the given name and arity.
        """
        opts: list[Type] = []
        for pred in self.get_preds(name, arity):
            opts.append(FunctionCons(pred.name, pred.args))
        if not opts:
            opts.append(FunctionCons(name, [SYMBOL] * arity))
        if len(opts) == 1:
            return opts[0]
        return UnionCons(opts)

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

    def _is_inhabited(self, name: str, visited: set[str]) -> bool:
        """
        Check if a type has a base case (is inhabited).

        A type is uninhabited if it only contains recursive references with no
        base case to construct a value.
        """
        if name in visited:
            return False
        visited.add(name)
        td = self.get_type_def(name)
        if td.rel == TypeRelation.SUBTYPE:
            return True
        return self._has_base_case(td.type, name, visited)

    def _has_base_case(self, t: Type, type_name: str, visited: set[str]) -> bool:
        """
        Check if a type expression contains a base case.
        """
        if isinstance(t, FunctionCons):
            if len(t.args) == 0 and t.name != type_name:
                return True
            return any(self._has_base_case(arg, type_name, visited) for arg in t.args)

        if isinstance(t, UnionCons):
            return any(self._has_base_case(opt, type_name, visited) for opt in t.opts)

        if isinstance(t, TypeCons):
            if t.name == type_name:
                return False
            return self._is_inhabited(t.name, visited)

        return False

    def check(self) -> None:
        """
        Check the type specification for consistency.
        """

        @singledispatch
        def dispatch(t: Type) -> None:
            assert t
            raise NotImplementedError()

        @dispatch.register
        def _(t: TypeCons) -> None:
            if t.name not in self._types:
                raise ValueError(f"Type '{t.name}' not defined")

        @dispatch.register
        def _(t: UnionCons) -> None:
            for x in t.opts:
                dispatch(x)

        @dispatch.register
        def _(t: FunctionCons) -> None:
            for x in t.args:
                dispatch(x)

        for td in self._types.values():
            dispatch(td.type)

        for name in self._types:
            if not self._is_inhabited(name, set()):
                raise ValueError(f"Type '{name}' is uninhabited (no base case)")

        for pds in self._preds.values():
            for pd in pds:
                for x in pd.args:
                    dispatch(x)

    def __str__(self) -> str:
        return "\n".join(
            str(t)
            for t in list(self._types.values())
            + list(self._progs.values())
            + list(pd for pds in self._preds.values() for pd in pds)
        )
