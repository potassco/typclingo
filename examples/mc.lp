%*?
type Bank <: left | right.
type Group <: mis | can.
type Time <: Number.
type Fluent <: num(Group,Bank) | boat.
type Action <: move(Value,Value).
type Amount <: Number.
type Value <: Amount | Bank.

pred group(Group).
pred bank(Bank).
pred opposite(Bank,Bank).
pred action(Action).

pred holds(Fluent,Value,Time).
pred occurs(Action,Time).
pred moved(Group,Value,Time).

prog step(Time).
prog check(Time).
*%

#include <incmode>.

#program base.

% Some types
group(mis;can).
bank(left;right).
opposite(left,right;right,left).
action(move(M,C)) :- M>=0, C>=0, 1<=M+C<=2.

% Initial state
holds(num(G,left),3,0) :- group(G).
holds(num(G,right),0,0) :- group(G).
holds(boat,left,0).

#program step(t).

% Action generation
1 {occurs(A,t) : action(A) } 1.

% Auxiliary (action attributes)
moved(mis,M,t) :- occurs(move(M,C),t).
moved(can,C,t) :- occurs(move(M,C),t).

% Executability axioms
:- moved(G,N,t), holds(boat,B,t-1), holds(num(G,B),M,t-1), N>M.

% Effect axioms
holds(num(G,B),M+N,t) :- holds(num(G,B),M,t-1), holds(boat,B,t), moved(G,N,t).
holds(num(G,B),M-N,t) :- holds(num(G,B),M,t-1), holds(boat,B,t-1), moved(G,N,t).
holds(boat,B1,t)      :- holds(boat,B,t-1), opposite(B,B1).

% Missionaries not outnumbered by cannibals
:- holds(num(mis,B),M,t), holds(num(can,B),C,t), C>M>0.

#program check(t).

:- not holds(num(mis,right),3,t), query(t).
:- not holds(num(can,right),3,t), query(t).

#show occurs/2.
