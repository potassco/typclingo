%*?
type WeightedLiteralTupleId <: Number.
type LiteralTupleId <: Number.
type AtomTupleId <: Number.

type Literal <: Number.
type Weight <: Number.
type Body := normal(LiteralTupleId) | sum(WeightedLiteralTupleId,Weight).
type Head := disjunction(AtomTupleId) | choice(AtomTupleId).

pred atom_tuple(AtomTupleId,Literal).
pred literal_tuple(LiteralTupleId,Literal).
pred weighted_literal_tuple(WeightedLiteralTupleId,Literal,Weight).
pred rule(Head,Body).
pred hide(Symbol).
pred output(Symbol,LiteralTupleId).

pred conjunction(LiteralTupleId).
pred body(Body).
pred hold(Literal).
*%

conjunction(B) :- literal_tuple(B),
        hold(L) : literal_tuple(B, L), L > 0;
    not hold(L) : literal_tuple(B,-L), L > 0.

body(normal(B)) :- rule(_,normal(B)), conjunction(B).
body(sum(B,G))  :- rule(_,sum(B,G)),
    #sum { W,L :     hold(L), weighted_literal_tuple(B, L,W), L > 0 ;
           W,L : not hold(L), weighted_literal_tuple(B,-L,W), L > 0 } >= G.

  hold(A) : atom_tuple(H,A)   :- rule(disjunction(H),B), body(B).
{ hold(A) : atom_tuple(H,A) } :- rule(     choice(H),B), body(B).

#show.
#show T : output(T,B), conjunction(B), not hide(T).
