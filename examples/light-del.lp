%*?
type Light := l1.
type Atom := red(Light) | green(Light) | push(Light).

type Tel := Atom | initial | final | next(Tel) | eventually(Tel).
type Path := step | test(Del) | star(Path) | choice(Path, Path) | seq(Path, Path).
type Del := Tel | always(Path, Del) | eventually(Path, Del).

pred next(Tel).
pred eventually(Tel).
pred eventually(Path, Del).
pred always(Path, Del).
*%

light(l1).
red(L) :- not green(L), light(L).
next(eventually(green(L))) :- push(L).
next(push(l1)) :- initial.

:- initial, not eventually(star(seq(test(green(L)), test(red(L)))), final), light(L).

#external green(L): push(L).
#external initial .
#external push(l1).
