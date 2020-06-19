

tff(set, type, set: $tType > $tType).

tff(mem, type, mem: !>[A : $tType]: ((A * set(A)) > $o)).

tff(included, type, included: !>[A : $tType]: ((set(A) * set(A)) > $o)).

tff(included_def, axiom, ![A : $tType]: ![S:set(A), T:set(A)]:
  (included(A, S, T) <=> ![X:A]: (mem(A, X, S) => mem(A, X, T)))).

tff(goal, conjecture, ![A : $tType]: ![S : set(A)]: included(A, S, S)).

