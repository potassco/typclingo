%*?
type Element <: Symbol.

func gather(Element) -> Number.
func sort() -> t(Number,Element).

pred p(Element).
pred gather(Number).
*%

#script (python)

from clingo.core import Library
from clingo.symbol import Number, Symbol, Tuple_

SYMBOLS = set()

def gather(lib: Library, x: Symbol) -> Symbol:
    SYMBOLS.add(x)
    return Number(lib, 1)

def sort(lib: Library) -> list[Symbol]:
    return [Tuple_(lib, [Number(lib, i + 1), x]) for i, x in enumerate(sorted(SYMBOLS))]

#end.

p(1).
p(a).
p(b).
p(s(f)).

gather(1).
gather(@gather(X)) :- p(X).

enumerate(X,N) :- gather(1), t(X,N) = @sort().
