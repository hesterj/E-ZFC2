fof(t2_tarski, axiom,  (! [A] :  (! [B] :  ~ ( (r2_hidden(A, B) &  (! [C] :  ~ ( (r2_hidden(C, B) &  (! [D] :  ~ ( (r2_hidden(D, B) & r2_hidden(D, C)) ) ) ) ) ) ) ) ) ) ).
fof(d3_tarski, axiom,  (! [A] :  (! [B] :  (r1_tarski(A, B) <=>  (! [C] :  (r2_hidden(C, A) => r2_hidden(C, B)) ) ) ) ) ).
fof(d2_ordinal1, axiom,  (! [A] :  (v1_ordinal1(A) <=>  (! [B] :  (r2_hidden(B, A) => r1_tarski(B, A)) ) ) ) ).
fof(t51_classes1, axiom,  (! [A] : v1_ordinal1(k5_classes1(A))) ).
fof(t52_classes1, axiom,  (! [A] : r1_tarski(A, k5_classes1(A))) ).

% fof(sep_inst, axiom, (? [C] : (! [X] : (r2_hidden(X,C) <=> (r2_hidden(X,k5_classes1(a)) & ~p(X)))))).
fof(epsind_hyp, axiom, (! [X] : ((! [Y] : (r2_hidden(Y,X) => p(Y))) => p(X)))).
fof(epsind_concl, conjecture, p(a)).
