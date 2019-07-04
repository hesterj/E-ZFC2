thf(r2_hidden_type,type,(r2_hidden: $i>$i>$o)).
thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
thf(k5_classes1_type, type, k5_classes1: $i > $i).

% regularity
thf(t2_tarski, axiom,  (! [A: $i] :  (! [B: $i] :  ~ ( ( ( (r2_hidden @ A)  @ B)  &  (! [C: $i] :  ~ ( ( ( (r2_hidden @ C)  @ B)  &  (! [D: $i] :  ~ ( ( ( (r2_hidden @ D)  @ B)  &  ( (r2_hidden @ D)  @ C) ) ) ) ) ) ) ) ) ) ) , file(tarski, t2_tarski)).

% definition of subset
thf(d3_tarski, axiom,  (! [A: $i] :  (! [B: $i] :  ( ( (r1_tarski @ A)  @ B)  <=>  (! [C: $i] :  ( ( (r2_hidden @ C)  @ A)  =>  ( (r2_hidden @ C)  @ B) ) ) ) ) ) , file(tarski, d3_tarski)).

% definition of epsilon-transitive
thf(d2_ordinal1, axiom,  (! [A: $i] :  ( (v1_ordinal1 @ A)  <=>  (! [B: $i] :  ( ( (r2_hidden @ B)  @ A)  =>  ( (r1_tarski @ B)  @ A) ) ) ) ) , file(ordinal1, d2_ordinal1)).

% the_transitive-closure_of properties (not the defn, which is unnecessarily complicated)
thf(t51_classes1, axiom,  (! [A: $i] :  (v1_ordinal1 @  (k5_classes1 @ A) ) ) , file(classes1, t51_classes1)).
thf(t52_classes1, axiom,  (! [A: $i] :  ( (r1_tarski @ A)  @  (k5_classes1 @ A) ) ) , file(classes1, t52_classes1)).

% From this, we should be able to prove epsilon induction for an arbitrary predicate.
thf(ptp, type, (p : ($i > $o))).
   thf(atp, type, (a : $i)).

% separation instance
thf(s1_xboole_0_inst, axiom, (? [C: $i] :  (! [D: $i] :  ( ( (r2_hidden @ D)  @ C)  <=>  ( ( (r2_hidden @ D)  @ (k5_classes1 @ a))  &  (~ (p @ D) ) ) ) ) ) , file(xboole_0, s1_xboole_0)).

thf(epsind_hyp, axiom, (! [X:$i] : ((! [Y:$i] : ((r2_hidden@Y@X) => (p@Y))) => (p@X)))).
thf(epsind_concl, conjecture, (p @ a)).
