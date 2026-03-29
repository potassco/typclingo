%*?
type Light := l1.
type Atom := red(Light) | green(Light) | push(Light).

type Interval := i(Number, Number).
type Mel := Atom | initial | next(Mel) | next(Interval, Mel) | eventually(Interval, Mel).

pred next(Mel).
pred next(Interval, Mel).
pred eventually(Interval, Mel).
*%

light(l1).
red(L) :- not green(L), light(L).
next(eventually(i(5,10), green(L))) :- push(L).
next(push(l1)) :- initial.

#external green(L): push(L).
#external initial .
#external push(l1).
