#include('Axioms/zfc.ax').

#cnf(c0,negated_conjecture,(phi(X))).

#cnf(c0,negated_conjecture,(phi(X)|chi(X)|block(Y))).
#cnf(c0,negated_conjecture,(phi(X)|block(Y))).
#cnf(c1,negated_conjecture,(~block(Y))).

cnf(c0,negated_conjecture,(phi(X)|block(a))).
cnf(c1,negated_conjecture,(~block(a))).

#cnf(c11,negated_conjecture, (member(a,X)|phi(X))).
#cnf(c12,negated_conjecture, (~member(a,X)|phi(X))).
#cnf(c2,negated_conjecture, (~member(a,X)|member(X,X))).
#cnf(c3,negated_conjecture, (~member(a,X)|~member(X,X))).

