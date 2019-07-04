fof(peano1,axiom,member(z,nat)).
fof(peano2,axiom,(! [X] : (member(X,nat) => member(s(X),nat)))).
fof(peano5,axiom,(! [P] : (member(z,P) => ((! [X] : (member(X,nat) => (member(X,P) => member(s(X),P)))) => (! [X] : (member(X,nat) => member(X,P))))))).
fof(addz,axiom,(! [X] : (member(X,nat) => (a(X,z) = X)))).
fof(adds,axiom,(! [X] : (member(X,nat) => (! [Y] : (member(Y,nat) => (a(X,s(Y)) = s(a(X,Y)))))))).
fof(addnat,conjecture,(! [X] : (member(X,nat) => (! [Y] : (member(Y,nat) => member(a(X,Y),nat)))))).
