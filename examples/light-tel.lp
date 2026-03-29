%*?
type Light := l1.
type Atom := red(Light) | green(Light) | push(Light).

type Tel := Atom | initial | next(Tel) | eventually(Tel) | until(Tel, Tel).

pred next(Tel).
pred eventually(Tel).
pred until(Tel, Tel).
*%

light(l1).
red(L) :- not green(L), light(L).
next(eventually(green(L))) :- push(L).
next(push(l1)) :- initial.

#external green(L): push(L).
#external initial .
#external push(l1).
