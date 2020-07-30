tff(nat, type, nat: $tType).
tff(o, type, o: nat).
tff(s, type, s: nat > nat).
tff(plus, type, plus: (nat*nat)>nat).
tff(times, type, times: (nat*nat)>nat).
tff(fact, type, fact: nat > nat).
tff(inf, type, inf: (nat*nat)>$o).

tff(plus_def, axiom, ![X:nat, Y:nat]: plus(s(X), Y) = s(plus(X, Y))).
tff(plus_def0, axiom, ![Y:nat]: plus(o, Y) = Y). 
tff(times_def, axiom, ![X:nat, Y:nat]: times(s(X), Y) = plus(times(X, Y), Y)).
tff(times_def0, axiom, ![Y:nat]: times(o, Y) = o).
tff(fact_def, axiom, ![X:nat]: fact(s(X)) = times(fact(X), s(X))).
tff(fact_def0, axiom, fact(o) = s(o)).
tff(inf_def, axiom, ![X:nat, Y:nat]: (inf(s(X), s(Y)) <=> inf(X,Y))).
tff(inf_def0, axiom, ![Y:nat]: inf(o, s(Y))).

tff(goal, conjecture, inf(fact(s(s(s(s(s(s(s(o)))))))), s(fact(s(s(s(s(s(s(s(o))))))))))).

