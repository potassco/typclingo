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

atom_tuple(0).
atom_tuple(0,1).
literal_tuple(0).
rule(disjunction(0),normal(0)).
atom_tuple(1).
atom_tuple(1,3).
atom_tuple(1,4).
rule(disjunction(1),normal(0)).
atom_tuple(2).
atom_tuple(2,3).
literal_tuple(1).
literal_tuple(1,4).
rule(disjunction(2),normal(1)).
atom_tuple(3).
atom_tuple(3,4).
literal_tuple(2).
literal_tuple(2,3).
rule(disjunction(3),normal(2)).
atom_tuple(4).
atom_tuple(4,5).
literal_tuple(3).
literal_tuple(3,3).
literal_tuple(3,4).
rule(disjunction(4),normal(3)).
output(a,3).
output(b,4).
output(c,5).

#defined atom_tuple/1.
#defined atom_tuple/2.
#defined literal_tuple/1.
#defined literal_tuple/2.
#defined weighted_literal_tuple/1.
#defined weighted_literal_tuple/3.
#defined rule/2.
#defined hide/1.
#defined output/2.

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
