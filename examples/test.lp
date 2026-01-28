%*?
type F <: f(Number).
type N <: Number.
type M <: Number.
pred p(F).
pred q(N).
pred r(M).
pred f(Function,Number).
prog q(Number).
*%
q(1).
p(f(1)).
:- q(X), r(X).

#program q(k).

#const n = f(g).
#const m = f(1-2,n).

f(k,m).
p(f"{X}") :- X=p.
