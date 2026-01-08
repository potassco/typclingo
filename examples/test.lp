%*?
type F <: f(Number).
type N <: Number.
type M <: Number.
pred p(F).
pred q(N).
pred r(M).
*%
q(1).
p(f(1)).
:- q(X), r(X).
