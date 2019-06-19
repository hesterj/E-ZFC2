fof(d3_tarski, axiom,  (! [A,B] : (r1_tarski(A,B) <=> (! [C] : (r2_hidden(C,A) => r2_hidden(C,B)))))).
fof(sepinst, axiom, (? [U] : (! [Z] : (r2_hidden(Z,U) <=> (r2_hidden(Z,a) & ~r2_hidden(Z,g(Z))))))).
fof(surjcantor2,conjecture,(~(! [Y] : (r1_tarski(Y,a) => (? [X] : (r2_hidden(X,a) & (g(X) = Y))))))).



