% Copyright 2012-2015 Consortium of the BWare ANR Project (ANR-12-INSE-0010)
%	  	    <http://bware.lri.fr/>
% Copyright 2012-2015 Cedric (CPR Team)
%	  	    David DELAHAYE
%	  	    <david.delahaye@cnam.fr>
% Copyright 2012-2015 LRI (VALS team)
%	  	    Sylvain CONCHON
%	  	    <sylvain.conchon@lri.fr>
% Copyright 2012-2015 Inria (Gallium, Deducteam)
%	  	    Damien DOLIGEZ
%	  	    <damien.doligez@inria.fr>
% Copyright 2012-2015 Mitsubishi Electric R&D Centre Europe
%	  	    David MENTRE
%	  	    <d.mentre@fr.merce.mee.com>
% Copyright 2012-2015 ClearSy
%	  	    Thierry LECOMTE
%	  	    <thierry.lecomte@clearsy.com>
% Copyright 2012-2015 OCamlPro
%	  	    Fabrice LE FESSANT
%		    <fabrice.le_fessant@ocamlpro.com>
%
% This file is a free software.
%
% This software is governed by the CeCILL-B license under French law and 
% abiding by the rules of distribution of free software.  
% You can use, modify and/or redistribute the software under the terms of the 
% CeCILL-B license as circulated by CEA, CNRS and INRIA at the following URL 
% "http://www.cecill.info". 
%
% As a counterpart to the access to the source code and rights to copy,
% modify and redistribute granted by the license, users are provided only
% with a limited warranty and the software's author, the holder of the
% economic rights, and the successive licensors have only limited liability. 
%
% In this respect, the user's attention is drawn to the risks associated
% with loading, using, modifying and/or developing or reproducing the
% software by the user in light of its specific status of free software,
% that may mean that it is complicated to manipulate, and that also
% therefore means that it is reserved for developers and experienced
% professionals having in-depth computer knowledge. Users are therefore
% encouraged to load and test the software's suitability as regards their
% requirements in conditions enabling the security of their systems and/or 
% data to be ensured and, more generally, to use and operate it in the 
% same conditions as regards security. 
%
% The fact that you are presently reading this means that you have had
% knowledge of the CeCILL-B license and that you accept its terms.
%
% ------------------------------------------------------------------------------

tff(bool, type, bool: $tType).

tff(true, type, true: bool).

tff(false, type, false: bool).

tff(match_bool, type, match_bool: !>[A : $tType]: ((bool * A * A) > A)).

tff(match_bool_True, axiom, ![A : $tType]: ![Z:A, Z1:A]: (match_bool(A, true,
  Z, Z1) = Z)).

tff(match_bool_False, axiom, ![A : $tType]: ![Z:A, Z1:A]:
  (match_bool(A, false, Z, Z1) = Z1)).

tff(true_False, axiom, ~ (true = false)).

tff(bool_inversion, axiom, ![U:bool]: ((U = true) | (U = false))).

tff(andb, type, andb: (bool * bool) > bool).

tff(andb_def, axiom, ![Y:bool]: ((andb(true, Y) = Y) & (andb(false,
  Y) = false))).

tff(orb, type, orb: (bool * bool) > bool).

tff(orb_def, axiom, ![Y:bool]: ((orb(true, Y) = true) & (orb(false,
  Y) = Y))).

tff(xorb, type, xorb: (bool * bool) > bool).

tff(xorb_def, axiom, (((xorb(true, true) = false) & (xorb(false,
  true) = true)) & ((xorb(true, false) = true) & (xorb(false,
  false) = false)))).

tff(notb, type, notb: bool > bool).

tff(notb_def, axiom, ((notb(true) = false) & (notb(false) = true))).

tff(implb, type, implb: (bool * bool) > bool).

tff(implb_def, axiom, ![X:bool]: ((implb(X, true) = true) & ((implb(true,
  false) = false) & (implb(false, false) = true)))).

tff(compatOrderMult, axiom, ![X:$int, Y:$int, Z:$int]: ($lesseq(X,Y)
  => ($lesseq(0,Z) => $lesseq($product(X,Z),$product(Y,Z))))).

tff(abs, type, abs: $int > $int).

tff(abs_def, axiom, ![X:$int]: (($lesseq(0,X) => (abs(X) = X)) & (~
  $lesseq(0,X) => (abs(X) = $uminus(X))))).

tff(abs_le, axiom, ![X:$int, Y:$int]: ($lesseq(abs(X),Y)
  <=> ($lesseq($uminus(Y),X) & $lesseq(X,Y)))).

tff(abs_pos, axiom, ![X:$int]: $lesseq(0,abs(X))).

tff(div, type, div: ($int * $int) > $int).

tff(mod, type, mod: ($int * $int) > $int).

tff(div_mod, axiom, ![X:$int, Y:$int]: (~ (Y = 0)
  => (X = $sum($product(Y,div(X, Y)),mod(X, Y))))).

tff(div_bound, axiom, ![X:$int, Y:$int]: (($lesseq(0,X) & $less(0,Y))
  => ($lesseq(0,div(X, Y)) & $lesseq(div(X, Y),X)))).

tff(mod_bound, axiom, ![X:$int, Y:$int]: (~ (Y = 0)
  => ($less($uminus(abs(Y)),mod(X, Y)) & $less(mod(X, Y),abs(Y))))).

tff(div_sign_pos, axiom, ![X:$int, Y:$int]: (($lesseq(0,X) & $less(0,Y))
  => $lesseq(0,div(X, Y)))).

tff(div_sign_neg, axiom, ![X:$int, Y:$int]: (($lesseq(X,0) & $less(0,Y))
  => $lesseq(div(X, Y),0))).

tff(mod_sign_pos, axiom, ![X:$int, Y:$int]: (($lesseq(0,X) & ~ (Y = 0))
  => $lesseq(0,mod(X, Y)))).

tff(mod_sign_neg, axiom, ![X:$int, Y:$int]: (($lesseq(X,0) & ~ (Y = 0))
  => $lesseq(mod(X, Y),0))).

tff(rounds_toward_zero, axiom, ![X:$int, Y:$int]: (~ (Y = 0)
  => $lesseq(abs($product(div(X, Y),Y)),abs(X)))).

tff(div_1, axiom, ![X:$int]: (div(X, 1) = X)).

tff(mod_1, axiom, ![X:$int]: (mod(X, 1) = 0)).

tff(div_inf, axiom, ![X:$int, Y:$int]: (($lesseq(0,X) & $less(X,Y))
  => (div(X, Y) = 0))).

tff(mod_inf, axiom, ![X:$int, Y:$int]: (($lesseq(0,X) & $less(X,Y))
  => (mod(X, Y) = X))).

tff(div_mult, axiom, ![X:$int, Y:$int, Z:$int]: (($less(0,X) & ($lesseq(0,Y)
  & $lesseq(0,Z))) => (div($sum($product(X,Y),Z), X) = $sum(Y,div(Z, X))))).

tff(mod_mult, axiom, ![X:$int, Y:$int, Z:$int]: (($less(0,X) & ($lesseq(0,Y)
  & $lesseq(0,Z))) => (mod($sum($product(X,Y),Z), X) = mod(Z, X)))).

tff(set, type, set: $tType > $tType).

tff(mem, type, mem: !>[A : $tType]: ((A * set(A)) > $o)).

tff(infix_eqeq, type, infix_eqeq: !>[A : $tType]: ((set(A) * set(A)) > $o)).

tff(infix_eqeq_def, axiom, ![A : $tType]: ![S:set(A), T:set(A)]:
  (infix_eqeq(A, S, T) <=> ![X:A]: (mem(A, X, S) <=> mem(A, X, T)))).

tff(power, type, power: !>[A : $tType]: (set(A) > set(set(A)))).

tff(non_empty_power, type, non_empty_power: !>[A : $tType]: (set(A) >
  set(set(A)))).

tff(subset, type, subset: !>[A : $tType]: ((set(A) * set(A)) > $o)).

tff(subset_def, axiom, ![A : $tType]: ![S:set(A), T:set(A)]: (subset(A, S, T)
  <=> mem(set(A), S, power(A, T)))).

tff(subsetnoteq, type, subsetnoteq: !>[A : $tType]: ((set(A) * set(A)) >
  $o)).

tff(subsetnoteq_def, axiom, ![A : $tType]: ![S:set(A), T:set(A)]:
  (subsetnoteq(A, S, T) <=> (subset(A, S, T) & ~ infix_eqeq(A, S, T)))).

tff(empty, type, empty: !>[A : $tType]: set(A)).

tff(is_empty, type, is_empty: !>[A : $tType]: (set(A) > $o)).

tff(is_empty_def, axiom, ![A : $tType]: ![S:set(A)]: (is_empty(A, S) <=> ![X:
  A]: ~ mem(A, X, S))).

tff(empty_def1, axiom, ![A : $tType]: is_empty(A, empty(A))).

tff(empty1, axiom, ![A : $tType]: ![X:A]: ~ mem(A, X, empty(A))).

tff(add, type, add: !>[A : $tType]: ((A * set(A)) > set(A))).

tff(add_def1, axiom, ![A : $tType]: ![X:A, Y:A]: ![S:set(A)]: (mem(A, X,
  add(A, Y, S)) <=> ((X = Y) | mem(A, X, S)))).

tff(singleton, type, singleton: !>[A : $tType]: (A > set(A))).

tff(mem_singleton, axiom, ![A : $tType]: ![X:A, Y:A]: (mem(A, X,
  singleton(A, Y)) <=> (X = Y))).

tff(remove, type, remove: !>[A : $tType]: ((A * set(A)) > set(A))).

tff(remove_def1, axiom, ![A : $tType]: ![X:A, Y:A, S:set(A)]: (mem(A, X,
  remove(A, Y, S)) <=> (~ (X = Y) & mem(A, X, S)))).

tff(all, type, all: !>[A : $tType]: set(A)).

tff(all_def, axiom, ![A : $tType]: ![X:A]: mem(A, X, all(A))).

tff(union, type, union: !>[A : $tType]: ((set(A) * set(A)) > set(A))).

tff(mem_union, axiom, ![A : $tType]: ![S:set(A), T:set(A), X:A]: (mem(A, X,
  union(A, S, T)) <=> (mem(A, X, S) | mem(A, X, T)))).

tff(inter, type, inter: !>[A : $tType]: ((set(A) * set(A)) > set(A))).

tff(mem_inter, axiom, ![A : $tType]: ![S:set(A), T:set(A), X:A]: (mem(A, X,
  inter(A, S, T)) <=> (mem(A, X, S) & mem(A, X, T)))).

tff(diff, type, diff: !>[A : $tType]: ((set(A) * set(A)) > set(A))).

tff(mem_diff, axiom, ![A : $tType]: ![S:set(A), T:set(A), X:A]: (mem(A, X,
  diff(A, S, T)) <=> (mem(A, X, S) & ~ mem(A, X, T)))).

tff(b_bool, type, b_bool: set(bool)).

tff(mem_b_bool, axiom, ![X:bool]: mem(bool, X, b_bool)).

tff(integer, type, integer: set($int)).

tff(mem_integer, axiom, ![X:$int]: mem($int, X, integer)).

tff(natural, type, natural: set($int)).

tff(mem_natural, axiom, ![X:$int]: (mem($int, X, natural) <=> $lesseq(0,X))).

tff(natural1, type, natural1: set($int)).

tff(mem_natural1, axiom, ![X:$int]: (mem($int, X, natural1) <=> $less(0,X))).

tff(nat, type, nat: set($int)).

tff(mem_nat, axiom, ![X:$int]: (mem($int, X, nat) <=> ($lesseq(0,X)
  & $lesseq(X,2147483647)))).

tff(nat1, type, nat1: set($int)).

tff(mem_nat1, axiom, ![X:$int]: (mem($int, X, nat1) <=> ($less(0,X)
  & $lesseq(X,2147483647)))).

tff(bounded_int, type, bounded_int: set($int)).

tff(mem_bounded_int, axiom, ![X:$int]: (mem($int, X, bounded_int)
  <=> ($lesseq($uminus(2147483647),X) & $lesseq(X,2147483647)))).

tff(mk, type, mk: ($int * $int) > set($int)).

tff(mem_interval, axiom, ![X:$int, A:$int, B:$int]: (mem($int, X, mk(A, B))
  <=> ($lesseq(A,X) & $lesseq(X,B)))).

tff(tuple2, type, tuple2: ($tType * $tType) > $tType).

tff(tuple21, type, tuple21: !>[A : $tType, A1 : $tType]: ((A1 * A) >
  tuple2(A1, A))).

tff(tuple2_proj_1, type, tuple2_proj_1: !>[A : $tType, A1 : $tType]:
  (tuple2(A1, A) > A1)).

tff(tuple2_proj_1_def, axiom, ![A : $tType, A1 : $tType]: ![U:A1, U1:A]:
  (tuple2_proj_1(A, A1, tuple21(A, A1, U, U1)) = U)).

tff(tuple2_proj_2, type, tuple2_proj_2: !>[A : $tType, A1 : $tType]:
  (tuple2(A1, A) > A)).

tff(tuple2_proj_2_def, axiom, ![A : $tType, A1 : $tType]: ![U:A1, U1:A]:
  (tuple2_proj_2(A, A1, tuple21(A, A1, U, U1)) = U1)).

tff(tuple2_inversion, axiom, ![A : $tType, A1 : $tType]: ![U:tuple2(A1, A)]:
  (U = tuple21(A, A1, tuple2_proj_1(A, A1, U), tuple2_proj_2(A, A1, U)))).

tff(times, type, times: !>[A : $tType, B : $tType]: ((set(A) * set(B)) >
  set(tuple2(A, B)))).

tff(mem_times, axiom, ![A : $tType, B : $tType]: ![S:set(A), T:set(B), X:A,
  Y:B]: (mem(tuple2(A, B), tuple21(B, A, X, Y), times(A, B, S, T))
  <=> (mem(A, X, S) & mem(B, Y, T)))).

tff(mem_power, axiom, ![A : $tType]: ![S:set(A), T:set(A)]: (mem(set(A), S,
  power(A, T)) <=> ![X:A]: (mem(A, X, S) => mem(A, X, T)))).

tff(mem_non_empty_power, axiom, ![A : $tType]: ![S:set(A), T:set(A)]:
  (mem(set(A), S, non_empty_power(A, T)) <=> (![X:A]: (mem(A, X, S)
  => mem(A, X, T)) & ~ infix_eqeq(A, S, empty(A))))).

tff(choose, type, choose: !>[A : $tType]: (set(A) > A)).

tff(relation, type, relation: !>[A : $tType, B : $tType]: ((set(A) *
  set(B)) > set(set(tuple2(A, B))))).

tff(mem_relation, axiom, ![A : $tType, B : $tType]: ![U:set(A), V:set(B), R:
  set(tuple2(A, B))]: (mem(set(tuple2(A, B)), R, relation(A, B, U, V))
  <=> ![X:A, Y:B]: (mem(tuple2(A, B), tuple21(B, A, X, Y), R) => (mem(A, X,
  U) & mem(B, Y, V))))).

tff(inverse, type, inverse: !>[A : $tType, B : $tType]: (set(tuple2(A, B)) >
  set(tuple2(B, A)))).

tff(mem_inverse, axiom, ![A : $tType, B : $tType]: ![P:set(tuple2(A, B)), X:
  B, Y:A]: (mem(tuple2(B, A), tuple21(A, B, X, Y), inverse(A, B, P))
  <=> mem(tuple2(A, B), tuple21(B, A, Y, X), P))).

tff(dom, type, dom: !>[A : $tType, B : $tType]: (set(tuple2(A, B)) >
  set(A))).

tff(mem_dom, axiom, ![A : $tType, B : $tType]: ![P:set(tuple2(A, B)), X:A]:
  (mem(A, X, dom(A, B, P)) <=> ?[B1:B]: mem(tuple2(A, B), tuple21(B, A, X,
  B1), P))).

tff(ran, type, ran: !>[A : $tType, B : $tType]: (set(tuple2(A, B)) >
  set(B))).

tff(mem_ran, axiom, ![A : $tType, B : $tType]: ![P:set(tuple2(A, B)), X:B]:
  (mem(B, X, ran(A, B, P)) <=> ?[A1:A]: mem(tuple2(A, B), tuple21(B, A, A1,
  X), P))).

tff(semicolon, type, semicolon: !>[A : $tType, B : $tType, C : $tType]:
  ((set(tuple2(A, B)) * set(tuple2(B, C))) > set(tuple2(A, C)))).

tff(mem_semicolon, axiom, ![A : $tType, B : $tType, C : $tType]: ![P:
  set(tuple2(A, B)), Q:set(tuple2(B, C)), X:A, Y:C]:
  (mem(tuple2(A, C), tuple21(C, A, X, Y), semicolon(A, B, C, P, Q)) <=> ?[B1:
  B]: (mem(tuple2(A, B), tuple21(B, A, X, B1), P)
  & mem(tuple2(B, C), tuple21(C, B, B1, Y), Q)))).

tff(semicolon_back, type, semicolon_back: !>[A : $tType, B : $tType,
  C : $tType]: ((set(tuple2(B, C)) * set(tuple2(A, B))) >
  set(tuple2(A, C)))).

tff(semicolon_back1, axiom, ![A : $tType, B : $tType, C : $tType]: ![P:
  set(tuple2(A, B)), Q:set(tuple2(B, C))]: (semicolon_back(A, B, C, Q,
  P) = semicolon(A, B, C, P, Q))).

tff(id, type, id: !>[A : $tType]: (set(A) > set(tuple2(A, A)))).

tff(mem_id, axiom, ![A : $tType]: ![U:set(A), X:A, Y:A]:
  (mem(tuple2(A, A), tuple21(A, A, X, Y), id(A, U)) <=> (mem(A, X, U)
  & (X = Y)))).

tff(domain_restriction, type, domain_restriction: !>[A : $tType, B : $tType]:
  ((set(A) * set(tuple2(A, B))) > set(tuple2(A, B)))).

tff(mem_domain_restriction, axiom, ![A : $tType, B : $tType]: ![P:
  set(tuple2(A, B)), S:set(A), X:A, Y:B]: (mem(tuple2(A, B), tuple21(B, A, X,
  Y), domain_restriction(A, B, S, P)) <=> (mem(tuple2(A, B), tuple21(B, A, X,
  Y), P) & mem(A, X, S)))).

tff(range_restriction, type, range_restriction: !>[A : $tType, B : $tType]:
  ((set(tuple2(A, B)) * set(B)) > set(tuple2(A, B)))).

tff(mem_range_restriction, axiom, ![A : $tType, B : $tType]: ![P:
  set(tuple2(A, B)), T:set(B), X:A, Y:B]: (mem(tuple2(A, B), tuple21(B, A, X,
  Y), range_restriction(A, B, P, T)) <=> (mem(tuple2(A, B), tuple21(B, A, X,
  Y), P) & mem(B, Y, T)))).

tff(domain_substraction, type, domain_substraction: !>[A : $tType,
  B : $tType]: ((set(A) * set(tuple2(A, B))) > set(tuple2(A, B)))).

tff(mem_domain_substraction, axiom, ![A : $tType, B : $tType]: ![P:
  set(tuple2(A, B)), S:set(A), X:A, Y:B]: (mem(tuple2(A, B), tuple21(B, A, X,
  Y), domain_substraction(A, B, S, P)) <=> (mem(tuple2(A, B), tuple21(B,
  A, X, Y), P) & ~ mem(A, X, S)))).

tff(range_substraction, type, range_substraction: !>[A : $tType, B : $tType]:
  ((set(tuple2(A, B)) * set(B)) > set(tuple2(A, B)))).

tff(mem_range_substraction, axiom, ![A : $tType, B : $tType]: ![P:
  set(tuple2(A, B)), T:set(B), X:A, Y:B]: (mem(tuple2(A, B), tuple21(B, A, X,
  Y), range_substraction(A, B, P, T)) <=> (mem(tuple2(A, B), tuple21(B, A, X,
  Y), P) & ~ mem(B, Y, T)))).

tff(image, type, image: !>[A : $tType, B : $tType]: ((set(tuple2(A, B)) *
  set(A)) > set(B))).

tff(mem_image, axiom, ![A : $tType, B : $tType]: ![P:set(tuple2(A, B)), W:
  set(A), X:B]: (mem(B, X, image(A, B, P, W)) <=> ?[A1:A]: (mem(A, A1, W)
  & mem(tuple2(A, B), tuple21(B, A, A1, X), P)))).

tff(infix_lspl, type, infix_lspl: !>[A : $tType, B : $tType]:
  ((set(tuple2(A, B)) * set(tuple2(A, B))) > set(tuple2(A, B)))).

tff(mem_overriding, axiom, ![A : $tType, B : $tType]: ![Q:set(tuple2(A, B)),
  P:set(tuple2(A, B)), X:A, Y:B]: (mem(tuple2(A, B), tuple21(B, A, X, Y),
  infix_lspl(A, B, Q, P)) <=> ((mem(tuple2(A, B), tuple21(B, A, X, Y), Q) & ~
  mem(A, X, dom(A, B, P))) | mem(tuple2(A, B), tuple21(B, A, X, Y), P)))).

tff(direct_product, type, direct_product: !>[A : $tType, B : $tType,
  C : $tType]: ((set(tuple2(A, B)) * set(tuple2(A, C))) >
  set(tuple2(A, tuple2(B, C))))).

tff(mem_direct_product, axiom, ![A : $tType, B : $tType, C : $tType]: ![F:
  set(tuple2(A, B)), G:set(tuple2(A, C)), X:A, Y:B, Z:C]:
  (mem(tuple2(A, tuple2(B, C)), tuple21(tuple2(B, C), A, X, tuple21(C, B, Y,
  Z)), direct_product(A, B, C, F, G)) <=> (mem(tuple2(A, B), tuple21(B, A, X,
  Y), F) & mem(tuple2(A, C), tuple21(C, A, X, Z), G)))).

tff(prj1, type, prj1: !>[A : $tType, B : $tType]: (tuple2(set(A), set(B)) >
  set(tuple2(tuple2(A, B), A)))).

tff(mem_proj_op_1, axiom, ![A : $tType, B : $tType]: ![S:set(A), T:set(B), X:
  A, Y:B, Z:A]: (mem(tuple2(tuple2(A, B), A), tuple21(A,
  tuple2(A, B), tuple21(B, A, X, Y), Z), prj1(A, B, tuple21(set(B),
  set(A), S, T))) <=> (mem(tuple2(tuple2(A, B), A), tuple21(A,
  tuple2(A, B), tuple21(B, A, X, Y), Z), times(tuple2(A, B), A, times(A,
  B, S, T), S)) & (Z = X)))).

tff(prj2, type, prj2: !>[A : $tType, B : $tType]: (tuple2(set(A), set(B)) >
  set(tuple2(tuple2(A, B), B)))).

tff(mem_proj_op_2, axiom, ![A : $tType, B : $tType]: ![S:set(A), T:set(B), X:
  A, Y:B, Z:B]: (mem(tuple2(tuple2(A, B), B), tuple21(B,
  tuple2(A, B), tuple21(B, A, X, Y), Z), prj2(A, B, tuple21(set(B),
  set(A), S, T))) <=> (mem(tuple2(tuple2(A, B), B), tuple21(B,
  tuple2(A, B), tuple21(B, A, X, Y), Z), times(tuple2(A, B), B, times(A,
  B, S, T), T)) & (Z = Y)))).

tff(parallel_product, type, parallel_product: !>[A : $tType, B : $tType,
  C : $tType, D : $tType]: ((set(tuple2(A, B)) * set(tuple2(C, D))) >
  set(tuple2(tuple2(A, C), tuple2(B, D))))).

tff(mem_parallel_product, axiom, ![A : $tType, B : $tType, C : $tType,
  D : $tType]: ![H:set(tuple2(A, B)), K:set(tuple2(C, D)), X:A, Y:C, Z:B, W:
  D]: (mem(tuple2(tuple2(A, C), tuple2(B, D)), tuple21(tuple2(B, D),
  tuple2(A, C), tuple21(C, A, X, Y), tuple21(D, B, Z, W)),
  parallel_product(A, B, C, D, H, K)) <=> (mem(tuple2(A, B), tuple21(B, A, X,
  Z), H) & mem(tuple2(C, D), tuple21(D, C, Y, W), K)))).

tff(infix_plmngt, type, infix_plmngt: !>[A : $tType, B : $tType]: ((set(A) *
  set(B)) > set(set(tuple2(A, B))))).

tff(mem_partial_function_set, axiom, ![A : $tType, B : $tType]: ![S:set(A),
  T:set(B), F:set(tuple2(A, B))]: (mem(set(tuple2(A, B)), F, infix_plmngt(A,
  B, S, T)) <=> (mem(set(tuple2(A, B)), F, relation(A, B, S, T)) & ![X:A, Y1:
  B, Y2:B]: ((mem(tuple2(A, B), tuple21(B, A, X, Y1), F)
  & mem(tuple2(A, B), tuple21(B, A, X, Y2), F)) => (Y1 = Y2))))).

tff(infix_mnmngt, type, infix_mnmngt: !>[A : $tType, B : $tType]: ((set(A) *
  set(B)) > set(set(tuple2(A, B))))).

tff(mem_total_function_set, axiom, ![A : $tType, B : $tType]: ![S:set(A), T:
  set(B), X:set(tuple2(A, B))]: (mem(set(tuple2(A, B)), X, infix_mnmngt(A,
  B, S, T)) <=> (mem(set(tuple2(A, B)), X, infix_plmngt(A, B, S, T))
  & infix_eqeq(A, dom(A, B, X), S)))).

tff(infix_gtplgt, type, infix_gtplgt: !>[A : $tType, B : $tType]: ((set(A) *
  set(B)) > set(set(tuple2(A, B))))).

tff(mem_partial_injection_set, axiom, ![A : $tType, B : $tType]: ![S:
  set(A), T:set(B), X:set(tuple2(A, B))]: (mem(set(tuple2(A, B)), X,
  infix_gtplgt(A, B, S, T)) <=> (mem(set(tuple2(A, B)), X, infix_plmngt(A,
  B, S, T)) & mem(set(tuple2(B, A)), inverse(A, B, X), infix_plmngt(B, A, T,
  S))))).

tff(infix_gtmngt, type, infix_gtmngt: !>[A : $tType, B : $tType]: ((set(A) *
  set(B)) > set(set(tuple2(A, B))))).

tff(mem_total_injection_set, axiom, ![A : $tType, B : $tType]: ![S:set(A), T:
  set(B), X:set(tuple2(A, B))]: (mem(set(tuple2(A, B)), X, infix_gtmngt(A,
  B, S, T)) <=> (mem(set(tuple2(A, B)), X, infix_gtplgt(A, B, S, T))
  & mem(set(tuple2(A, B)), X, infix_mnmngt(A, B, S, T))))).

tff(infix_plmngtgt, type, infix_plmngtgt: !>[A : $tType, B : $tType]:
  ((set(A) * set(B)) > set(set(tuple2(A, B))))).

tff(mem_partial_surjection_set, axiom, ![A : $tType, B : $tType]: ![S:
  set(A), T:set(B), X:set(tuple2(A, B))]: (mem(set(tuple2(A, B)), X,
  infix_plmngtgt(A, B, S, T)) <=> (mem(set(tuple2(A, B)), X, infix_plmngt(A,
  B, S, T)) & infix_eqeq(B, ran(A, B, X), T)))).

tff(infix_mnmngtgt, type, infix_mnmngtgt: !>[A : $tType, B : $tType]:
  ((set(A) * set(B)) > set(set(tuple2(A, B))))).

tff(mem_total_surjection_set, axiom, ![A : $tType, B : $tType]: ![S:set(A),
  T:set(B), X:set(tuple2(A, B))]: (mem(set(tuple2(A, B)), X,
  infix_mnmngtgt(A, B, S, T)) <=> (mem(set(tuple2(A, B)), X,
  infix_plmngtgt(A, B, S, T)) & mem(set(tuple2(A, B)), X, infix_mnmngt(A,
  B, S, T))))).

tff(infix_gtplgtgt, type, infix_gtplgtgt: !>[A : $tType, B : $tType]:
  ((set(A) * set(B)) > set(set(tuple2(A, B))))).

tff(mem_partial_bijection_set, axiom, ![A : $tType, B : $tType]: ![S:
  set(A), T:set(B), X:set(tuple2(A, B))]: (mem(set(tuple2(A, B)), X,
  infix_gtplgtgt(A, B, S, T)) <=> (mem(set(tuple2(A, B)), X, infix_gtplgt(A,
  B, S, T)) & mem(set(tuple2(A, B)), X, infix_plmngtgt(A, B, S, T))))).

tff(infix_gtmngtgt, type, infix_gtmngtgt: !>[A : $tType, B : $tType]:
  ((set(A) * set(B)) > set(set(tuple2(A, B))))).

tff(mem_total_bijection_set, axiom, ![A : $tType, B : $tType]: ![S:set(A), T:
  set(B), X:set(tuple2(A, B))]: (mem(set(tuple2(A, B)), X, infix_gtmngtgt(A,
  B, S, T)) <=> (mem(set(tuple2(A, B)), X, infix_gtmngt(A, B, S, T))
  & mem(set(tuple2(A, B)), X, infix_mnmngtgt(A, B, S, T))))).

tff(apply, type, apply: !>[A : $tType, B : $tType]: ((set(tuple2(A, B)) *
  A) > B)).

tff(apply_def0, axiom, ![A : $tType, B : $tType]: ![F:set(tuple2(A, B)), S:
  set(A), T:set(B), A1:A]: ((mem(set(tuple2(A, B)), F, infix_plmngt(A, B, S,
  T)) & mem(A, A1, dom(A, B, F))) => mem(tuple2(A, B), tuple21(B, A, A1,
  apply(A, B, F, A1)), F))).

tff(apply_def2, axiom, ![A : $tType, B : $tType]: ![F:set(tuple2(A, B)), S:
  set(A), T:set(B), A1:A, B1:B]: ((mem(set(tuple2(A, B)), F, infix_plmngt(A,
  B, S, T)) & mem(tuple2(A, B), tuple21(B, A, A1, B1), F)) => (apply(A, B, F,
  A1) = B1))).

tff(seq_length, type, seq_length: !>[A : $tType]: (($int * set(A)) >
  set(set(tuple2($int, A))))).

tff(seq_length_def, axiom, ![A : $tType]: ![N:$int, S:set(A)]:
  (seq_length(A, N, S) = infix_mnmngt($int, A, mk(1, N), S))).

tff(size, type, size: !>[A : $tType]: (set(tuple2($int, A)) > $int)).

tff(size_def, axiom, ![A : $tType]: ![N:$int, S:set(A), R:
  set(tuple2($int, A))]: (($lesseq(0,N) & mem(set(tuple2($int, A)), R,
  seq_length(A, N, S))) => (size(A, R) = N))).

tff(seq, type, seq: !>[A : $tType]: (set(A) > set(set(tuple2($int, A))))).

tff(seq_def, axiom, ![A : $tType]: ![S:set(A), R:set(tuple2($int, A))]:
  (mem(set(tuple2($int, A)), R, seq(A, S)) <=> ($lesseq(0,size(A, R))
  & mem(set(tuple2($int, A)), R, seq_length(A, size(A, R), S))))).

tff(seq1, type, seq1: !>[A : $tType]: (set(A) > set(set(tuple2($int, A))))).

tff(iseq, type, iseq: !>[A : $tType]: (set(A) > set(set(tuple2($int, A))))).

tff(iseq1, type, iseq1: !>[A : $tType]: (set(A) >
  set(set(tuple2($int, A))))).

tff(perm, type, perm: !>[A : $tType]: (set(A) > set(set(tuple2($int, A))))).

tff(insert_in_front, type, insert_in_front: !>[A : $tType]: ((A *
  set(tuple2($int, A))) > set(tuple2($int, A)))).

tff(insert_at_tail, type, insert_at_tail: !>[A : $tType]:
  ((set(tuple2($int, A)) * A) > set(tuple2($int, A)))).

tff(tail, type, tail: !>[A : $tType]: (set(tuple2($int, A)) >
  set(tuple2($int, A)))).

tff(last, type, last: !>[A : $tType]: (set(tuple2($int, A)) > A)).

tff(first, type, first: !>[A : $tType]: (set(tuple2($int, A)) > A)).

tff(front, type, front: !>[A : $tType]: (set(tuple2($int, A)) >
  set(tuple2($int, A)))).

tff(concatenation, type, concatenation: !>[A : $tType]:
  ((set(tuple2($int, A)) * set(tuple2($int, A))) > set(tuple2($int, A)))).

tff(conc, type, conc: !>[A : $tType]:
  (set(tuple2($int, set(tuple2($int, A)))) > set(tuple2($int, A)))).

tff(is_finite_subset, type, is_finite_subset: !>[A : $tType]: ((set(A) *
  set(A) * $int) > $o)).

tff(empty2, axiom, ![A : $tType]: ![S:set(A)]: is_finite_subset(A, empty(A),
  S, 0)).

tff(add_mem, axiom, ![A : $tType]: ![X:A, S1:set(A), S2:set(A), C:$int]:
  (is_finite_subset(A, S1, S2, C) => (mem(A, X, S2) => (mem(A, X, S1)
  => is_finite_subset(A, add(A, X, S1), S2, C))))).

tff(add_notmem, axiom, ![A : $tType]: ![X:A, S1:set(A), S2:set(A), C:$int]:
  (is_finite_subset(A, S1, S2, C) => (mem(A, X, S2) => (~ mem(A, X, S1)
  => is_finite_subset(A, add(A, X, S1), S2, $sum(C,1)))))).

tff(is_finite_subset_inversion, axiom, ![A : $tType]: ![Z:set(A), Z1:
  set(A), Z2:$int]: (is_finite_subset(A, Z, Z1, Z2) => ((?[S:set(A)]:
  (((Z = empty(A)) & (Z1 = S)) & (Z2 = 0)) | ?[X:A, S1:set(A), S2:set(A), C:
  $int]: (is_finite_subset(A, S1, S2, C) & (mem(A, X, S2) & (mem(A, X, S1)
  & (((Z = add(A, X, S1)) & (Z1 = S2)) & (Z2 = C)))))) | ?[X:A, S1:set(A),
  S2:set(A), C:$int]: (is_finite_subset(A, S1, S2, C) & (mem(A, X, S2) & (~
  mem(A, X, S1) & (((Z = add(A, X, S1)) & (Z1 = S2))
  & (Z2 = $sum(C,1))))))))).

tff(finite_subsets, type, finite_subsets: !>[A : $tType]: (set(A) >
  set(set(A)))).

tff(finite_subsets_def, axiom, ![A : $tType]: ![S:set(A), X:set(A)]:
  (mem(set(A), X, finite_subsets(A, S)) <=> ?[C:$int]: is_finite_subset(A, X,
  S, C))).

tff(non_empty_finite_subsets, type, non_empty_finite_subsets: !>[A : $tType]:
  (set(A) > set(set(A)))).

tff(non_empty_finite_subsets_def, axiom, ![A : $tType]: ![S:set(A), X:
  set(A)]: (mem(set(A), X, non_empty_finite_subsets(A, S)) <=> ?[C:$int]:
  (is_finite_subset(A, X, S, C) & ~ infix_eqeq(A, X, empty(A))))).

tff(card, type, card: !>[A : $tType]: (set(A) > $int)).

tff(card_def, axiom, ![A : $tType]: ![S:set(A), X:set(A), C:$int]:
  (is_finite_subset(A, X, S, C) => (card(A, X) = C))).

tff(min, type, min: set($int) > $int).

tff(min_belongs, axiom, ![S:set($int)]: ((subset($int, S, natural) & ~
  infix_eqeq($int, S, empty($int))) => mem($int, min(S), S))).

tff(min_is_min, axiom, ![S:set($int), X:$int]: ((subset($int, S, natural)
  & mem($int, X, S)) => $lesseq(min(S),X))).

tff(max, type, max: set($int) > $int).

tff(max_belongs, axiom, ![S:set($int)]: (mem(set($int), S,
  non_empty_finite_subsets($int, natural)) => mem($int, max(S), S))).

tff(max_is_max, axiom, ![S:set($int), X:$int]: ((mem(set($int), S,
  finite_subsets($int, natural)) & mem($int, X, S)) => $lesseq(X,max(S)))).

tff(iterate, type, iterate: !>[A : $tType]:
  (tuple2(set(tuple2(A, A)), $int) > set(tuple2(A, A)))).

tff(iterate_def, axiom, ![A : $tType]: ![A1:set(tuple2(A, A)), B:$int]:
  (((B = 0) => (iterate(A, tuple21($int, set(tuple2(A, A)), A1,
  B)) = id(A, dom(A, A, A1)))) & (~ (B = 0) => (iterate(A, tuple21($int,
  set(tuple2(A, A)), A1, B)) = semicolon(A, A, A, iterate(A, tuple21($int,
  set(tuple2(A, A)), A1, $difference(B,1))), A1))))).

tff(closure, type, closure: !>[A : $tType]: (set(tuple2(A, A)) >
  set(tuple2(A, A)))).

tff(closure_def, axiom, ![A : $tType]: ![A1:set(tuple2(A, A)), U:
  tuple2(A, A)]: (mem(tuple2(A, A), U, closure(A, A1)) <=> ?[X:$int]:
  ($lesseq(0,X) & mem(tuple2(A, A), U, iterate(A, tuple21($int,
  set(tuple2(A, A)), A1, X)))))).

tff(closure1, type, closure1: !>[A : $tType]: (set(tuple2(A, A)) >
  set(tuple2(A, A)))).

tff(closure1_def, axiom, ![A : $tType]: ![A1:set(tuple2(A, A)), U:
  tuple2(A, A)]: (mem(tuple2(A, A), U, closure1(A, A1)) <=> ?[X:$int]:
  ($less(0,X) & mem(tuple2(A, A), U, iterate(A, tuple21($int,
  set(tuple2(A, A)), A1, X)))))).

tff(generalized_union, type, generalized_union: !>[A : $tType]:
  (set(set(A)) > set(A))).

tff(generalized_union_def, axiom, ![A : $tType]: ![A1:set(set(A)), X:A]:
  (mem(A, X, generalized_union(A, A1)) <=> ?[B:set(A)]: (mem(set(A), B, A1)
  & mem(A, X, B)))).

tff(uninterpreted_type, type, uninterpreted_type: $tType).

tff(enum_aa, type, enum_aa: $tType).

tff(e_bb, type, e_bb: enum_aa).

tff(e_cc, type, e_cc: enum_aa).

tff(e_dd, type, e_dd: enum_aa).

tff(e_ee, type, e_ee: enum_aa).

tff(e_ff, type, e_ff: enum_aa).

tff(e_gg, type, e_gg: enum_aa).

tff(e_hh, type, e_hh: enum_aa).

tff(e_ii, type, e_ii: enum_aa).

tff(match_enum_aa, type, match_enum_aa: !>[A : $tType]: ((enum_aa * A * A *
  A * A * A * A * A * A) > A)).

tff(match_enum_aa_E_bb, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A, Z3:A, Z4:A,
  Z5:A, Z6:A, Z7:A]: (match_enum_aa(A, e_bb, Z, Z1, Z2, Z3, Z4, Z5, Z6,
  Z7) = Z)).

tff(match_enum_aa_E_cc, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A, Z3:A, Z4:A,
  Z5:A, Z6:A, Z7:A]: (match_enum_aa(A, e_cc, Z, Z1, Z2, Z3, Z4, Z5, Z6,
  Z7) = Z1)).

tff(match_enum_aa_E_dd, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A, Z3:A, Z4:A,
  Z5:A, Z6:A, Z7:A]: (match_enum_aa(A, e_dd, Z, Z1, Z2, Z3, Z4, Z5, Z6,
  Z7) = Z2)).

tff(match_enum_aa_E_ee, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A, Z3:A, Z4:A,
  Z5:A, Z6:A, Z7:A]: (match_enum_aa(A, e_ee, Z, Z1, Z2, Z3, Z4, Z5, Z6,
  Z7) = Z3)).

tff(match_enum_aa_E_ff, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A, Z3:A, Z4:A,
  Z5:A, Z6:A, Z7:A]: (match_enum_aa(A, e_ff, Z, Z1, Z2, Z3, Z4, Z5, Z6,
  Z7) = Z4)).

tff(match_enum_aa_E_gg, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A, Z3:A, Z4:A,
  Z5:A, Z6:A, Z7:A]: (match_enum_aa(A, e_gg, Z, Z1, Z2, Z3, Z4, Z5, Z6,
  Z7) = Z5)).

tff(match_enum_aa_E_hh, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A, Z3:A, Z4:A,
  Z5:A, Z6:A, Z7:A]: (match_enum_aa(A, e_hh, Z, Z1, Z2, Z3, Z4, Z5, Z6,
  Z7) = Z6)).

tff(match_enum_aa_E_ii, axiom, ![A : $tType]: ![Z:A, Z1:A, Z2:A, Z3:A, Z4:A,
  Z5:A, Z6:A, Z7:A]: (match_enum_aa(A, e_ii, Z, Z1, Z2, Z3, Z4, Z5, Z6,
  Z7) = Z7)).

tff(e_bb_E_cc, axiom, ~ (e_bb = e_cc)).

tff(e_bb_E_dd, axiom, ~ (e_bb = e_dd)).

tff(e_bb_E_ee, axiom, ~ (e_bb = e_ee)).

tff(e_bb_E_ff, axiom, ~ (e_bb = e_ff)).

tff(e_bb_E_gg, axiom, ~ (e_bb = e_gg)).

tff(e_bb_E_hh, axiom, ~ (e_bb = e_hh)).

tff(e_bb_E_ii, axiom, ~ (e_bb = e_ii)).

tff(e_cc_E_dd, axiom, ~ (e_cc = e_dd)).

tff(e_cc_E_ee, axiom, ~ (e_cc = e_ee)).

tff(e_cc_E_ff, axiom, ~ (e_cc = e_ff)).

tff(e_cc_E_gg, axiom, ~ (e_cc = e_gg)).

tff(e_cc_E_hh, axiom, ~ (e_cc = e_hh)).

tff(e_cc_E_ii, axiom, ~ (e_cc = e_ii)).

tff(e_dd_E_ee, axiom, ~ (e_dd = e_ee)).

tff(e_dd_E_ff, axiom, ~ (e_dd = e_ff)).

tff(e_dd_E_gg, axiom, ~ (e_dd = e_gg)).

tff(e_dd_E_hh, axiom, ~ (e_dd = e_hh)).

tff(e_dd_E_ii, axiom, ~ (e_dd = e_ii)).

tff(e_ee_E_ff, axiom, ~ (e_ee = e_ff)).

tff(e_ee_E_gg, axiom, ~ (e_ee = e_gg)).

tff(e_ee_E_hh, axiom, ~ (e_ee = e_hh)).

tff(e_ee_E_ii, axiom, ~ (e_ee = e_ii)).

tff(e_ff_E_gg, axiom, ~ (e_ff = e_gg)).

tff(e_ff_E_hh, axiom, ~ (e_ff = e_hh)).

tff(e_ff_E_ii, axiom, ~ (e_ff = e_ii)).

tff(e_gg_E_hh, axiom, ~ (e_gg = e_hh)).

tff(e_gg_E_ii, axiom, ~ (e_gg = e_ii)).

tff(e_hh_E_ii, axiom, ~ (e_hh = e_ii)).

tff(enum_aa_inversion, axiom, ![U:enum_aa]: ((((((((U = e_bb) | (U = e_cc))
  | (U = e_dd)) | (U = e_ee)) | (U = e_ff)) | (U = e_gg)) | (U = e_hh))
  | (U = e_ii))).

tff(set_enum_aa, type, set_enum_aa: set(enum_aa)).

tff(set_enum_aa_axiom, axiom, ![X:enum_aa]: mem(enum_aa, X, set_enum_aa)).

tff(f1, type, f1: (bool * $int * $int * $int * $int * $int * bool * enum_aa *
  bool * bool * bool * bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f1_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f1(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo,
  V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa)
  <=> (((((((((((((((((((((((((((((((((((((((((((($true & (V_bbpp = 0))
  & (V_bbqq = 1)) & mem($int, V_bbii, integer)) & $lesseq(0,V_bbii))
  & $lesseq(V_bbii,2147483647)) & mem($int, V_bbkk, integer))
  & $lesseq(0,V_bbkk)) & $lesseq(V_bbkk,2147483647)) & mem($int, V_bbgg,
  integer)) & $lesseq(0,V_bbgg)) & $lesseq(V_bbgg,2147483647))
  & mem($int, V_bbll, integer)) & $lesseq(0,V_bbll))
  & $lesseq(V_bbll,2147483647)) & $lesseq(1,V_bbll)) & $lesseq(V_bbll,254))
  & (V_bbll = V_bbkk)) & mem($int, V_bbjj, integer)) & $lesseq(0,V_bbjj))
  & $lesseq(V_bbjj,2147483647)) & $lesseq(1,V_bbjj)) & $lesseq(V_bbjj,254))
  & (V_bbjj = V_bbkk)) & mem($int, V_bbff, integer)) & $lesseq(0,V_bbff))
  & $lesseq(V_bbff,2147483647)) & $lesseq(1,V_bbff))
  & $lesseq($sum(V_bbff,1),2147483647)) & (V_bbff = V_bbgg))
  & mem($int, V_bbhh, integer)) & $lesseq(0,V_bbhh))
  & $lesseq(V_bbhh,2147483647)) & $lesseq(2,V_bbhh)) & (V_bbhh = V_bbii))
  & $lesseq($sum(V_bbhh,V_bbjj),253))
  & $lesseq($sum($sum(V_bbhh,V_bbll),V_bbjj),251)) & mem($int, V_bbmm,
  integer)) & $lesseq(0,V_bbmm)) & $lesseq(V_bbmm,2147483647))
  & $lesseq(1,V_bbmm)) & $lesseq($sum(V_bbmm,1),254)) & (V_bbmm = V_bbii))
  & $true) & $true))).

tff(f4, type, f4: (bool * $int * $int * $int * $int * $int * bool * enum_aa *
  bool * bool * bool * bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f4_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f4(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo,
  V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa)
  <=> ((((((((((((((((((((((((((((((((((((((((((($true & mem($int, V_uu,
  mk(0, 255))) & mem($int, V_vv, mk(0, 255))) & mem($int, V_ww, mk(0, 255)))
  & mem($int, V_xx, mk(0, 255))) & mem($int, V_yy, integer))
  & $lesseq(0,V_yy)) & $lesseq(V_yy,2147483647)) & $true) & $true) & $true)
  & $true) & $true) & mem($int, V_bbnn, integer)) & $lesseq(0,V_bbnn))
  & mem($int, V_bboo, integer)) & $lesseq(0,V_bboo)) & (mem(enum_aa, V_bbdd,
  union(enum_aa, singleton(enum_aa, e_cc), singleton(enum_aa, e_dd)))
  => (V_vv = 0))) & ((V_bbdd = e_ee) => $lesseq(V_vv,V_bbll)))
  & (mem(enum_aa, V_bbdd,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff))) => (V_ww = 0))) & (mem(enum_aa, V_bbdd,
  union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff)), singleton(enum_aa, e_gg)),
  singleton(enum_aa, e_hh))) => (V_yy = 0))) & (mem(enum_aa, V_bbdd,
  union(enum_aa, singleton(enum_aa, e_gg), singleton(enum_aa, e_hh)))
  => $lesseq(V_ww,$sum($sum(V_bbhh,V_bbjj),1)))) & ((V_bbdd = e_hh)
  => ((($difference($difference(V_bbnn,1),V_bboo) = V_xx)
  & $lesseq(V_ww,$sum(V_xx,V_bbjj))) & $lesseq(V_xx,$difference(V_bbhh,1)))))
  & ((V_bbdd = e_ii)
  => (($difference($difference($difference(V_bbnn,V_bboo),V_bbhh),1) = V_yy)
  & $lesseq(V_yy,V_bbff)))) & ((V_bbdd = e_cc) => $lesseq(V_uu,V_bbmm)))
  & ((V_bbdd = e_ff) => $lesseq(V_vv,$sum(V_bbll,1))))
  & (mem(enum_aa, V_bbdd,
  union(enum_aa, union(enum_aa, union(enum_aa, singleton(enum_aa, e_cc),
  singleton(enum_aa, e_dd)), singleton(enum_aa, e_ee)),
  singleton(enum_aa, e_ff))) => (V_xx = 0))) & ((V_bbdd = e_gg)
  => $lesseq(V_xx,1))) & ((V_bbdd = e_gg)
  => ($difference(V_bbnn,V_bboo) = V_xx))) & (mem(enum_aa, V_bbdd,
  union(enum_aa, singleton(enum_aa, e_gg), singleton(enum_aa, e_hh)))
  => ($lesseq(V_ww,$sum($sum(V_bbhh,V_bbjj),1))
  & $lesseq(V_vv,$sum($sum(V_bbll,V_ww),2))))) & ((V_bbdd = e_hh)
  => ((($difference($difference(V_bbnn,1),V_bboo) = V_xx)
  & $lesseq(V_ww,$sum(V_xx,V_bbjj))) & $lesseq(V_xx,V_bbhh)))) & $true)
  & $true) & ((V_bbee = true) <=> (V_bbdd = e_ii))) & (V_jj = V_uu))
  & (V_kk = V_vv)) & (V_ll = V_ww)) & (V_mm = V_xx)) & (V_nn = V_yy))
  & (V_oo = V_zz)) & (V_pp = V_bbaa)) & (V_qq = V_bbbb)) & (V_rr = V_bbcc))
  & (V_ss = V_bbdd)))).

tff(f5, type, f5: (bool * $int * $int * $int * $int * $int * bool * enum_aa *
  bool * bool * bool * bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f5_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f5(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo,
  V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_ii)) & ~ (V_bbdd = e_hh)) & ~ (V_bbdd = e_gg)) & ~
  (V_bbdd = e_ff)) & ~ (V_bbdd = e_ee)) & ~ (V_bbdd = e_dd))
  & (V_bbdd = e_cc)))).

tff(f7, type, f7: (bool * $int * $int * $int * $int * $int * bool * enum_aa *
  bool * bool * bool * bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f7_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f7(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo,
  V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> mem($int, $sum(V_uu,1), integer))).

tff(f8, type, f8: (bool * $int * $int * $int * $int * $int * bool * enum_aa *
  bool * bool * bool * bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f8_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f8(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo,
  V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> $lesseq($sum(V_uu,1),2147483647))).

tff(f9, type, f9: (bool * $int * $int * $int * $int * $int * bool * enum_aa *
  bool * bool * bool * bool * $int * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f9_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f9(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo,
  V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> $lesseq($uminus(2147483647),$sum(V_uu,1)))).

tff(f13, type, f13: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f13_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f13(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ii)) & ~
  (V_bbdd = e_hh)) & ~ (V_bbdd = e_gg)) & ~ (V_bbdd = e_ff))
  & (V_bbdd = e_ee)))).

tff(f14, type, f14: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f14_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f14(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> mem($int, $sum(V_vv,1), integer))).

tff(f15, type, f15: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f15_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f15(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> $lesseq($sum(V_vv,1),2147483647))).

tff(f16, type, f16: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f16_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f16(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> $lesseq($uminus(2147483647),$sum(V_vv,1)))).

tff(f20, type, f20: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f20_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f20(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ee)) & ~
  (V_bbdd = e_ff)) & ~ (V_bbdd = e_ii)) & ~ (V_bbdd = e_hh))
  & (V_bbdd = e_gg)))).

tff(f21, type, f21: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f21_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f21(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> mem($int, $sum(V_ww,1), integer))).

tff(f22, type, f22: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f22_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f22(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> $lesseq($sum(V_ww,1),2147483647))).

tff(f23, type, f23: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f23_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f23(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> $lesseq($uminus(2147483647),$sum(V_ww,1)))).

tff(f27, type, f27: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f27_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f27(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ee)) & ~
  (V_bbdd = e_ff)) & ~ (V_bbdd = e_gg)) & ~ (V_bbdd = e_ii))
  & (V_bbdd = e_hh)))).

tff(f28, type, f28: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f28_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f28(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> mem($int, $sum(V_xx,1), integer))).

tff(f29, type, f29: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f29_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f29(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> $lesseq($sum(V_xx,1),2147483647))).

tff(f30, type, f30: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f30_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f30(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> $lesseq($uminus(2147483647),$sum(V_xx,1)))).

tff(f34, type, f34: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f34_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f34(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ee)) & ~
  (V_bbdd = e_ff)) & ~ (V_bbdd = e_gg)) & ~ (V_bbdd = e_hh))
  & (V_bbdd = e_ii)))).

tff(f35, type, f35: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f35_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f35(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> mem($int, $sum(V_yy,1), integer))).

tff(f36, type, f36: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f36_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f36(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> $lesseq($sum(V_yy,1),2147483647))).

tff(f37, type, f37: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f37_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f37(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> $lesseq($uminus(2147483647),$sum(V_yy,1)))).

tff(f39, type, f39: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f39_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f39(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((($true & ~ (V_bbdd = e_ii)) & ~
  (V_bbdd = e_hh)) & ~ (V_bbdd = e_gg)) & ~ (V_bbdd = e_ff)) & ~
  (V_bbdd = e_ee)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_cc))
  & (V_bbdd = e_bb)) & (V_zz = true)) & (V_bbaa = true)) & (V_bbbb = false))
  & (V_bbcc = false)))).

tff(f42, type, f42: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f42_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f42(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((V_bbee = true) <=> (e_cc = e_ii)))).

tff(f43, type, f43: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f43_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f43(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_bbdd = e_ii)) & ~
  (V_bbdd = e_hh)) & ~ (V_bbdd = e_gg)) & ~ (V_bbdd = e_ff)) & ~
  (V_bbdd = e_ee)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_cc)) & ~
  ((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = false))
  & (V_bbcc = false))) & (V_bbdd = e_bb)) & (V_bbcc = false))
  & (V_zz = true)) & (V_bbaa = true)) & (V_bbbb = false)))).

tff(f46, type, f46: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f46_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f46(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((($true & ~ (V_bbdd = e_ii)) & ~
  (V_bbdd = e_hh)) & ~ (V_bbdd = e_gg)) & ~ (V_bbdd = e_ff)) & ~
  (V_bbdd = e_ee)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_cc)) & ~
  ((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = false))
  & (V_bbcc = false))) & (V_bbdd = e_bb)))).

tff(f47, type, f47: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f47_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f47(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_ii)) & ~ (V_bbdd = e_hh)) & ~ (V_bbdd = e_gg)) & ~
  (V_bbdd = e_ff)) & ~ (V_bbdd = e_ee)) & ~ (V_bbdd = e_dd))
  & (V_bbdd = e_cc)) & (V_zz = false)))).

tff(f48, type, f48: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f48_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f48(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> mem($int, $sum(V_uu,1), mk(0, 255)))).

tff(f49, type, f49: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f49_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f49(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((V_bbee = true) <=> (e_bb = e_ii)))).

tff(f50, type, f50: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f50_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f50(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_ii)) & ~ (V_bbdd = e_hh)) & ~ (V_bbdd = e_gg)) & ~
  (V_bbdd = e_ff)) & ~ (V_bbdd = e_ee)) & ~ (V_bbdd = e_dd))
  & (V_bbdd = e_cc)) & (V_bbaa = false)))).

tff(f51, type, f51: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f51_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f51(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_ii)) & ~ (V_bbdd = e_hh)) & ~ (V_bbdd = e_gg)) & ~
  (V_bbdd = e_ff)) & ~ (V_bbdd = e_ee)) & ~ (V_bbdd = e_dd))
  & (V_bbdd = e_cc)) & (V_bbbb = true)))).

tff(f52, type, f52: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f52_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f52(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_ii)) & ~ (V_bbdd = e_hh)) & ~ (V_bbdd = e_gg)) & ~
  (V_bbdd = e_ff)) & ~ (V_bbdd = e_ee)) & ~ (V_bbdd = e_dd))
  & (V_bbdd = e_cc)) & (V_bbcc = true)))).

tff(f53, type, f53: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f53_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f53(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((((((((($true & ~ (V_bbdd = e_bb))
  & ~ (V_bbdd = e_ii)) & ~ (V_bbdd = e_hh)) & ~ (V_bbdd = e_gg)) & ~
  (V_bbdd = e_ff)) & ~ (V_bbdd = e_ee)) & ~ (V_bbdd = e_dd)) & ~
  (V_zz = false)) & ~ (V_bbaa = false)) & ~ (V_bbbb = true)) & ~
  (V_bbcc = true)) & $lesseq(V_bbii,$sum(V_uu,1))) & (V_bbdd = e_cc))
  & (V_zz = true)) & (V_bbaa = true)) & (V_bbbb = false)) & (V_bbcc = false))
  & ~ (((($lesseq(V_bbmm,$sum(V_uu,1)) & (V_zz = true)) & (V_bbaa = true))
  & (V_bbbb = false)) & (V_bbcc = false))))).

tff(f55, type, f55: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f55_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f55(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_ii)) & ~ (V_bbdd = e_hh)) & ~ (V_bbdd = e_gg)) & ~
  (V_bbdd = e_ff)) & ~ (V_bbdd = e_ee)) & ~ (V_bbdd = e_dd)) & ~
  (V_zz = false)) & ~ (V_bbaa = false)) & ~ (V_bbbb = true)) & ~
  (V_bbcc = true)) & $lesseq(V_bbii,$sum(V_uu,1))) & (V_bbdd = e_cc))
  & (V_zz = true)) & (V_bbaa = true)) & (V_bbbb = false))
  & (V_bbcc = false)))).

tff(f56, type, f56: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f56_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f56(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((V_bbee = true) <=> (e_dd = e_ii)))).

tff(f57, type, f57: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f57_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f57(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((((((((($true & ~ (V_bbdd = e_bb))
  & ~ (V_bbdd = e_ii)) & ~ (V_bbdd = e_hh)) & ~ (V_bbdd = e_gg)) & ~
  (V_bbdd = e_ff)) & ~ (V_bbdd = e_ee)) & ~ (V_bbdd = e_dd)) & ~
  (V_zz = false)) & ~ (V_bbaa = false)) & ~ (V_bbbb = true)) & ~
  (V_bbcc = true)) & ~ (((($lesseq(V_bbii,$sum(V_uu,1)) & (V_zz = true))
  & (V_bbaa = true)) & (V_bbbb = false)) & (V_bbcc = false)))
  & (V_bbdd = e_cc)) & $lesseq(V_bbmm,$sum(V_uu,1))) & (V_zz = true))
  & (V_bbaa = true)) & (V_bbbb = false)) & (V_bbcc = false)))).

tff(f59, type, f59: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f59_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f59(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_ii)) & ~ (V_bbdd = e_hh)) & ~ (V_bbdd = e_gg)) & ~
  (V_bbdd = e_ff)) & ~ (V_bbdd = e_ee)) & ~ (V_bbdd = e_dd)) & ~
  (V_zz = false)) & ~ (V_bbaa = false)) & ~ (V_bbbb = true)) & ~
  (V_bbcc = true)) & ~ (((($lesseq(V_bbii,$sum(V_uu,1)) & (V_zz = true))
  & (V_bbaa = true)) & (V_bbbb = false)) & (V_bbcc = false)))
  & (V_bbdd = e_cc)))).

tff(f60, type, f60: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f60_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f60(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_ii)) & ~ (V_bbdd = e_hh)) & ~
  (V_bbdd = e_gg)) & ~ (V_bbdd = e_ff)) & ~ (V_bbdd = e_ee))
  & (V_bbdd = e_dd)) & (V_bbbb = true)) & (V_bbaa = true))
  & (V_bbcc = false)) & (V_zz = false)))).

tff(f62, type, f62: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f62_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f62(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = true)) & (V_bbcc = false)) | (((((V_zz = true)
  & (V_bbaa = true)) & (V_bbbb = false)) & (V_bbcc = false))
  & ((e_gg = V_bbdd) & (1 = V_xx)))) | (((((V_zz = true) & (V_bbaa = true))
  & (V_bbbb = true)) & (V_bbcc = false)) & (1 = V_xx))) | ((((((V_zz = false)
  & (V_bbaa = true)) & (V_bbbb = false)) & (V_bbcc = false)) & (e_gg = e_ee))
  & (1 = V_xx))) | (((((((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = true)) => ~ (V_bbcc = false)) & ((((V_zz = true)
  & (V_bbaa = true)) & (V_bbbb = false)) => ~ (V_bbcc = false)))
  & ((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = true)) => ~
  (V_bbcc = false))) & ((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = false)) => ~ (V_bbcc = false))) & (e_gg = e_bb))
  & (1 = V_xx))))).

tff(f65, type, f65: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f65_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f65(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((V_bbee = true) <=> (e_gg = e_ii)))).

tff(f66, type, f66: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f66_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f66(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_ii)) & ~ (V_bbdd = e_hh)) & ~
  (V_bbdd = e_gg)) & ~ (V_bbdd = e_ff)) & ~ (V_bbdd = e_ee)) & ~
  (V_zz = false)) & (V_bbdd = e_dd)) & (V_bbbb = true)) & (V_bbaa = true))
  & (V_bbcc = false)))).

tff(f68, type, f68: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f68_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f68(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = true)) & (V_bbcc = false)) & (V_xx = 1)) | (((((V_zz = true)
  & (V_bbaa = true)) & (V_bbbb = false)) & (V_bbcc = false))
  & (e_gg = V_bbdd))) | ((((V_zz = true) & (V_bbaa = true))
  & (V_bbbb = true)) & (V_bbcc = false))) | (((((V_zz = false)
  & (V_bbaa = true)) & (V_bbbb = false)) & (V_bbcc = false))
  & (e_gg = e_ee))) | ((((((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = true)) => ~ (V_bbcc = false)) & ((((V_zz = true)
  & (V_bbaa = true)) & (V_bbbb = false)) => ~ (V_bbcc = false)))
  & ((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = true)) => ~
  (V_bbcc = false))) & ((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = false)) => ~ (V_bbcc = false))) & (e_gg = e_bb))))).

tff(f69, type, f69: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f69_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f69(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_ii)) & ~ (V_bbdd = e_hh)) & ~
  (V_bbdd = e_gg)) & ~ (V_bbdd = e_ff)) & ~ (V_bbdd = e_ee)) & ~
  (((V_bbbb = true) & (V_bbaa = true)) & (V_bbcc = false)))
  & (V_bbdd = e_dd)) & (V_bbbb = false)) & (V_zz = false)) & (V_bbaa = true))
  & (V_bbcc = false)))).

tff(f71, type, f71: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f71_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f71(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = true)) & (V_bbcc = false)) & ((e_ee = e_gg) & (V_xx = 1)))
  | (((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = false))
  & (V_bbcc = false)) & (e_ee = V_bbdd))) | (((((V_zz = true)
  & (V_bbaa = true)) & (V_bbbb = true)) & (V_bbcc = false)) & (e_ee = e_gg)))
  | ((((V_zz = false) & (V_bbaa = true)) & (V_bbbb = false))
  & (V_bbcc = false))) | ((((((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = true)) => ~ (V_bbcc = false)) & ((((V_zz = true)
  & (V_bbaa = true)) & (V_bbbb = false)) => ~ (V_bbcc = false)))
  & ((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = true)) => ~
  (V_bbcc = false))) & ((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = false)) => ~ (V_bbcc = false))) & (e_ee = e_bb))))).

tff(f72, type, f72: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f72_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f72(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((V_bbee = true) <=> (e_ee = e_ii)))).

tff(f73, type, f73: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f73_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f73(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_ii)) & ~ (V_bbdd = e_hh)) & ~
  (V_bbdd = e_gg)) & ~ (V_bbdd = e_ff)) & ~ (V_bbdd = e_ee)) & ~
  (((V_bbbb = true) & (V_bbaa = true)) & (V_bbcc = false))) & ~
  ((((V_bbbb = false) & (V_zz = false)) & (V_bbaa = true))
  & (V_bbcc = false))) & (V_bbdd = e_dd)) & (V_bbcc = true)) & (V_zz = true))
  & (V_bbbb = false)))).

tff(f74, type, f74: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f74_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f74(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = true)) & (V_bbcc = false)) & ((e_bb = e_gg) & (V_xx = 1)))
  | (((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = false))
  & (V_bbcc = false)) & (e_bb = V_bbdd))) | (((((V_zz = true)
  & (V_bbaa = true)) & (V_bbbb = true)) & (V_bbcc = false)) & (e_bb = e_gg)))
  | (((((V_zz = false) & (V_bbaa = true)) & (V_bbbb = false))
  & (V_bbcc = false)) & (e_bb = e_ee))) | (((((((V_zz = false)
  & (V_bbaa = true)) & (V_bbbb = true)) => ~ (V_bbcc = false))
  & ((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = false)) => ~
  (V_bbcc = false))) & ((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = true))
  => ~ (V_bbcc = false))) & ((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = false)) => ~ (V_bbcc = false)))))).

tff(f75, type, f75: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f75_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f75(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_ii)) & ~ (V_bbdd = e_hh)) & ~
  (V_bbdd = e_gg)) & ~ (V_bbdd = e_ff)) & ~ (V_bbdd = e_ee)) & ~
  (((V_bbbb = true) & (V_bbaa = true)) & (V_bbcc = false))) & ~
  ((((V_bbbb = false) & (V_zz = false)) & (V_bbaa = true))
  & (V_bbcc = false))) & ~ (((V_bbcc = true) & (V_zz = true))
  & (V_bbbb = false))) & (V_bbdd = e_dd)) & (V_bbcc = false))
  & (V_bbaa = false)) & (V_zz = true)) & (V_bbbb = false)))).

tff(f76, type, f76: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f76_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f76(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_ii)) & ~ (V_bbdd = e_hh)) & ~
  (V_bbdd = e_gg)) & ~ (V_bbdd = e_ff)) & ~ (V_bbdd = e_ee)) & ~
  (((V_bbbb = true) & (V_bbaa = true)) & (V_bbcc = false))) & ~
  ((((V_bbbb = false) & (V_zz = false)) & (V_bbaa = true))
  & (V_bbcc = false))) & ~ (((V_bbcc = true) & (V_zz = true))
  & (V_bbbb = false))) & ~ ((((V_bbcc = false) & (V_bbaa = false))
  & (V_zz = true)) & (V_bbbb = false))) & (V_bbdd = e_dd))
  & (V_zz = false)))).

tff(f77, type, f77: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f77_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f77(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_ii)) & ~ (V_bbdd = e_hh)) & ~
  (V_bbdd = e_gg)) & ~ (V_bbdd = e_ff)) & ~ (V_bbdd = e_ee)) & ~
  (((V_bbbb = true) & (V_bbaa = true)) & (V_bbcc = false))) & ~
  ((((V_bbbb = false) & (V_zz = false)) & (V_bbaa = true))
  & (V_bbcc = false))) & ~ (((V_bbcc = true) & (V_zz = true))
  & (V_bbbb = false))) & ~ ((((V_bbcc = false) & (V_bbaa = false))
  & (V_zz = true)) & (V_bbbb = false))) & (V_bbdd = e_dd))
  & (V_bbaa = false)))).

tff(f78, type, f78: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f78_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f78(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_ii)) & ~ (V_bbdd = e_hh)) & ~
  (V_bbdd = e_gg)) & ~ (V_bbdd = e_ff)) & ~ (V_bbdd = e_ee)) & ~
  (((V_bbbb = true) & (V_bbaa = true)) & (V_bbcc = false))) & ~
  ((((V_bbbb = false) & (V_zz = false)) & (V_bbaa = true))
  & (V_bbcc = false))) & ~ (((V_bbcc = true) & (V_zz = true))
  & (V_bbbb = false))) & ~ ((((V_bbcc = false) & (V_bbaa = false))
  & (V_zz = true)) & (V_bbbb = false))) & (V_bbdd = e_dd))
  & (V_bbbb = true)))).

tff(f79, type, f79: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f79_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f79(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_ii)) & ~ (V_bbdd = e_hh)) & ~
  (V_bbdd = e_gg)) & ~ (V_bbdd = e_ff)) & ~ (V_bbdd = e_ee)) & ~
  (((V_bbbb = true) & (V_bbaa = true)) & (V_bbcc = false))) & ~
  ((((V_bbbb = false) & (V_zz = false)) & (V_bbaa = true))
  & (V_bbcc = false))) & ~ (((V_bbcc = true) & (V_zz = true))
  & (V_bbbb = false))) & ~ ((((V_bbcc = false) & (V_bbaa = false))
  & (V_zz = true)) & (V_bbbb = false))) & (V_bbdd = e_dd))
  & (V_bbcc = true)))).

tff(f80, type, f80: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f80_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f80(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_ii)) & ~ (V_bbdd = e_hh)) & ~
  (V_bbdd = e_gg)) & ~ (V_bbdd = e_ff)) & ~ (V_bbdd = e_ee)) & ~
  (((V_bbbb = true) & (V_bbaa = true)) & (V_bbcc = false))) & ~
  ((((V_bbbb = false) & (V_zz = false)) & (V_bbaa = true))
  & (V_bbcc = false))) & ~ (((V_bbcc = true) & (V_zz = true))
  & (V_bbbb = false))) & ~ ((((V_bbcc = false) & (V_bbaa = false))
  & (V_zz = true)) & (V_bbbb = false))) & ~ (V_zz = false)) & ~
  (V_bbaa = false)) & ~ (V_bbbb = true)) & ~ (V_bbcc = true))
  & (V_bbdd = e_dd)))).

tff(f81, type, f81: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f81_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f81(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = true)) & (V_bbcc = false)) & ((V_bbdd = e_gg) & (V_xx = 1)))
  | ((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = false))
  & (V_bbcc = false))) | (((((V_zz = true) & (V_bbaa = true))
  & (V_bbbb = true)) & (V_bbcc = false)) & (V_bbdd = e_gg)))
  | (((((V_zz = false) & (V_bbaa = true)) & (V_bbbb = false))
  & (V_bbcc = false)) & (V_bbdd = e_ee))) | ((((((((V_zz = false)
  & (V_bbaa = true)) & (V_bbbb = true)) => ~ (V_bbcc = false))
  & ((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = false)) => ~
  (V_bbcc = false))) & ((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = true))
  => ~ (V_bbcc = false))) & ((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = false)) => ~ (V_bbcc = false))) & (V_bbdd = e_bb))))).

tff(f82, type, f82: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f82_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f82(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ii)) & ~
  (V_bbdd = e_hh)) & ~ (V_bbdd = e_gg)) & ~ (V_bbdd = e_ff))
  & (V_bbdd = e_ee)) & (V_bbaa = false)))).

tff(f83, type, f83: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f83_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f83(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = true)) & (V_bbcc = false)) & ((e_bb = e_gg) & (V_xx = 1)))
  | (((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = false))
  & (V_bbcc = false)) & (($lesseq($sum($sum(V_vv,1),1),V_bbll)
  & (e_bb = e_ee)) | ~ $lesseq($sum($sum(V_vv,1),1),V_bbll))))
  | (((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = true))
  & (V_bbcc = false)) & (e_bb = e_gg))) | (((((V_zz = false)
  & (V_bbaa = true)) & (V_bbbb = false)) & (V_bbcc = false))
  & (($lesseq($sum($sum(V_vv,1),1),V_bbll) & (e_bb = e_ee)) | (~
  $lesseq($sum($sum(V_vv,1),1),V_bbll) & (e_bb = e_ff)))))
  | (((((((V_zz = false) & (V_bbaa = true)) & (V_bbbb = true)) => ~
  (V_bbcc = false)) & ((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = false))
  => ~ (V_bbcc = false))) & ((((V_zz = true) & (V_bbaa = true))
  & (V_bbbb = true)) => ~ (V_bbcc = false))) & ((((V_zz = false)
  & (V_bbaa = true)) & (V_bbbb = false)) => ~ (V_bbcc = false)))))).

tff(f85, type, f85: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f85_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f85(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> mem($int, $sum(V_vv,1), mk(0, 255)))).

tff(f86, type, f86: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f86_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f86(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ii)) & ~
  (V_bbdd = e_hh)) & ~ (V_bbdd = e_gg)) & ~ (V_bbdd = e_ff))
  & (V_bbdd = e_ee)) & (V_bbcc = true)))).

tff(f87, type, f87: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f87_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f87(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ii)) & ~
  (V_bbdd = e_hh)) & ~ (V_bbdd = e_gg)) & ~ (V_bbdd = e_ff)) & ~
  (V_bbaa = false)) & ~ (V_bbcc = true)) & (V_bbdd = e_ee))
  & (V_bbbb = true)) & (V_zz = false)))).

tff(f89, type, f89: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f89_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f89(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = true)) & (V_bbcc = false)) | ((((((V_zz = true)
  & (V_bbaa = true)) & (V_bbbb = false)) & (V_bbcc = false))
  & (($lesseq($sum($sum(V_vv,1),1),V_bbll) & (e_gg = e_ee)) | (~
  $lesseq($sum($sum(V_vv,1),1),V_bbll) & (e_gg = e_bb)))) & (1 = V_xx)))
  | (((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = true))
  & (V_bbcc = false)) & (1 = V_xx))) | ((((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = false)) & (V_bbcc = false))
  & (($lesseq($sum($sum(V_vv,1),1),V_bbll) & (e_gg = e_ee)) | (~
  $lesseq($sum($sum(V_vv,1),1),V_bbll) & (e_gg = e_ff)))) & (1 = V_xx)))
  | (((((((((V_zz = false) & (V_bbaa = true)) & (V_bbbb = true)) => ~
  (V_bbcc = false)) & ((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = false))
  => ~ (V_bbcc = false))) & ((((V_zz = true) & (V_bbaa = true))
  & (V_bbbb = true)) => ~ (V_bbcc = false))) & ((((V_zz = false)
  & (V_bbaa = true)) & (V_bbbb = false)) => ~ (V_bbcc = false)))
  & (e_gg = e_bb)) & (1 = V_xx))))).

tff(f90, type, f90: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f90_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f90(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ii)) & ~
  (V_bbdd = e_hh)) & ~ (V_bbdd = e_gg)) & ~ (V_bbdd = e_ff)) & ~
  (V_bbaa = false)) & ~ (V_bbcc = true)) & ~ (V_zz = false))
  & (V_bbdd = e_ee)) & (V_bbbb = true)))).

tff(f91, type, f91: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f91_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f91(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = true)) & (V_bbcc = false)) & (V_xx = 1)) | (((((V_zz = true)
  & (V_bbaa = true)) & (V_bbbb = false)) & (V_bbcc = false))
  & (($lesseq($sum($sum(V_vv,1),1),V_bbll) & (e_gg = e_ee)) | (~
  $lesseq($sum($sum(V_vv,1),1),V_bbll) & (e_gg = e_bb))))) | ((((V_zz = true)
  & (V_bbaa = true)) & (V_bbbb = true)) & (V_bbcc = false)))
  | (((((V_zz = false) & (V_bbaa = true)) & (V_bbbb = false))
  & (V_bbcc = false)) & (($lesseq($sum($sum(V_vv,1),1),V_bbll)
  & (e_gg = e_ee)) | (~ $lesseq($sum($sum(V_vv,1),1),V_bbll)
  & (e_gg = e_ff))))) | ((((((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = true)) => ~ (V_bbcc = false)) & ((((V_zz = true)
  & (V_bbaa = true)) & (V_bbbb = false)) => ~ (V_bbcc = false)))
  & ((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = true)) => ~
  (V_bbcc = false))) & ((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = false)) => ~ (V_bbcc = false))) & (e_gg = e_bb))))).

tff(f92, type, f92: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f92_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f92(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ii)) & ~
  (V_bbdd = e_hh)) & ~ (V_bbdd = e_gg)) & ~ (V_bbdd = e_ff)) & ~
  (V_bbaa = false)) & ~ (V_bbcc = true)) & ~ (V_bbbb = true))
  & $lesseq(V_bbkk,$sum(V_vv,1))) & (V_bbdd = e_ee)) & (V_bbbb = false))
  & (V_zz = false)))).

tff(f93, type, f93: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f93_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f93(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = true)) & (V_bbcc = false)) & ((e_ff = e_gg) & (V_xx = 1)))
  | (((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = false))
  & (V_bbcc = false)) & (($lesseq($sum($sum(V_vv,1),1),V_bbll)
  & (e_ff = e_ee)) | (~ $lesseq($sum($sum(V_vv,1),1),V_bbll)
  & (e_ff = e_bb))))) | (((((V_zz = true) & (V_bbaa = true))
  & (V_bbbb = true)) & (V_bbcc = false)) & (e_ff = e_gg)))
  | (((((V_zz = false) & (V_bbaa = true)) & (V_bbbb = false))
  & (V_bbcc = false)) & (($lesseq($sum($sum(V_vv,1),1),V_bbll)
  & (e_ff = e_ee)) | ~ $lesseq($sum($sum(V_vv,1),1),V_bbll))))
  | ((((((((V_zz = false) & (V_bbaa = true)) & (V_bbbb = true)) => ~
  (V_bbcc = false)) & ((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = false))
  => ~ (V_bbcc = false))) & ((((V_zz = true) & (V_bbaa = true))
  & (V_bbbb = true)) => ~ (V_bbcc = false))) & ((((V_zz = false)
  & (V_bbaa = true)) & (V_bbbb = false)) => ~ (V_bbcc = false)))
  & (e_ff = e_bb))))).

tff(f94, type, f94: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f94_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f94(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((V_bbee = true) <=> (e_ff = e_ii)))).

tff(f95, type, f95: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f95_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f95(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ii)) & ~
  (V_bbdd = e_hh)) & ~ (V_bbdd = e_gg)) & ~ (V_bbdd = e_ff)) & ~
  (V_bbaa = false)) & ~ (V_bbcc = true)) & ~ (V_bbbb = true))
  & $lesseq(V_bbkk,$sum(V_vv,1))) & ~ ((V_bbbb = false) & (V_zz = false)))
  & (V_bbdd = e_ee)) & (V_zz = true)))).

tff(f96, type, f96: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f96_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f96(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ii)) & ~
  (V_bbdd = e_hh)) & ~ (V_bbdd = e_gg)) & ~ (V_bbdd = e_ff)) & ~
  (V_bbaa = false)) & ~ (V_bbcc = true)) & ~ (V_bbbb = true))
  & $lesseq(V_bbkk,$sum(V_vv,1))) & ~ ((V_bbbb = false) & (V_zz = false)))
  & ~ (V_zz = true)) & (V_bbdd = e_ee)))).

tff(f97, type, f97: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f97_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f97(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = true)) & (V_bbcc = false)) & ((V_bbdd = e_gg) & (V_xx = 1)))
  | (((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = false))
  & (V_bbcc = false)) & (($lesseq($sum($sum(V_vv,1),1),V_bbll)
  & (V_bbdd = e_ee)) | (~ $lesseq($sum($sum(V_vv,1),1),V_bbll)
  & (V_bbdd = e_bb))))) | (((((V_zz = true) & (V_bbaa = true))
  & (V_bbbb = true)) & (V_bbcc = false)) & (V_bbdd = e_gg)))
  | (((((V_zz = false) & (V_bbaa = true)) & (V_bbbb = false))
  & (V_bbcc = false)) & (($lesseq($sum($sum(V_vv,1),1),V_bbll)
  & (V_bbdd = e_ee)) | (~ $lesseq($sum($sum(V_vv,1),1),V_bbll)
  & (V_bbdd = e_ff))))) | ((((((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = true)) => ~ (V_bbcc = false)) & ((((V_zz = true)
  & (V_bbaa = true)) & (V_bbbb = false)) => ~ (V_bbcc = false)))
  & ((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = true)) => ~
  (V_bbcc = false))) & ((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = false)) => ~ (V_bbcc = false))) & (V_bbdd = e_bb))))).

tff(f98, type, f98: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f98_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f98(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ii)) & ~
  (V_bbdd = e_hh)) & ~ (V_bbdd = e_gg)) & ~ (V_bbdd = e_ff)) & ~
  (V_bbaa = false)) & ~ (V_bbcc = true)) & ~ (V_bbbb = true)) & ~
  $lesseq(V_bbkk,$sum(V_vv,1))) & (V_bbdd = e_ee)))).

tff(f99, type, f99: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f99_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f99(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ee)) & ~
  (V_bbdd = e_ii)) & ~ (V_bbdd = e_hh)) & ~ (V_bbdd = e_gg))
  & (V_bbdd = e_ff)) & (V_bbaa = false)))).

tff(f100, type, f100: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f100_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f100(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = true)) & (V_bbcc = false)) & ((e_bb = e_gg) & (V_xx = 1)))
  | ((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = false))
  & (V_bbcc = false))) | ((((V_zz = true) & (V_bbaa = true))
  & (V_bbbb = true)) & (V_bbcc = false))) | (((((V_zz = false)
  & (V_bbaa = true)) & (V_bbbb = false)) & (V_bbcc = false))
  & (e_bb = V_bbdd))) | (((((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = true)) => ~ (V_bbcc = false)) & ((((V_zz = true)
  & (V_bbaa = true)) & (V_bbbb = false)) => ~ (V_bbcc = false)))
  & ((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = true)) => ~
  (V_bbcc = false))) & ((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = false)) => ~ (V_bbcc = false)))))).

tff(f101, type, f101: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f101_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f101(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ee)) & ~
  (V_bbdd = e_ii)) & ~ (V_bbdd = e_hh)) & ~ (V_bbdd = e_gg))
  & (V_bbdd = e_ff)) & (V_bbcc = true)))).

tff(f102, type, f102: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f102_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f102(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ee)) & ~
  (V_bbdd = e_ii)) & ~ (V_bbdd = e_hh)) & ~ (V_bbdd = e_gg)) & ~
  (V_bbaa = false)) & ~ (V_bbcc = true)) & (V_bbdd = e_ff))
  & (V_zz = true)))).

tff(f103, type, f103: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f103_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f103(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ee)) & ~
  (V_bbdd = e_ii)) & ~ (V_bbdd = e_hh)) & ~ (V_bbdd = e_gg)) & ~
  (V_bbaa = false)) & ~ (V_bbcc = true)) & ~ (V_zz = true))
  & (V_bbdd = e_ff)) & (V_zz = false)) & (V_bbbb = true)))).

tff(f104, type, f104: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f104_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f104(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = true)) & (V_bbcc = false)) | ((((((V_zz = true)
  & (V_bbaa = true)) & (V_bbbb = false)) & (V_bbcc = false)) & (e_gg = e_bb))
  & (1 = V_xx))) | ((((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = true))
  & (V_bbcc = false)) & (e_gg = e_bb)) & (1 = V_xx))) | (((((V_zz = false)
  & (V_bbaa = true)) & (V_bbbb = false)) & (V_bbcc = false))
  & ((e_gg = V_bbdd) & (1 = V_xx)))) | (((((((((V_zz = false)
  & (V_bbaa = true)) & (V_bbbb = true)) => ~ (V_bbcc = false))
  & ((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = false)) => ~
  (V_bbcc = false))) & ((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = true))
  => ~ (V_bbcc = false))) & ((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = false)) => ~ (V_bbcc = false))) & (e_gg = e_bb))
  & (1 = V_xx))))).

tff(f105, type, f105: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f105_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f105(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ee)) & ~
  (V_bbdd = e_ii)) & ~ (V_bbdd = e_hh)) & ~ (V_bbdd = e_gg)) & ~
  (V_bbaa = false)) & ~ (V_bbcc = true)) & ~ (V_zz = true)) & ~
  ((V_zz = false) & (V_bbbb = true))) & (V_bbdd = e_ff)))).

tff(f106, type, f106: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f106_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f106(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = true)) & (V_bbcc = false)) & ((V_bbdd = e_gg) & (V_xx = 1)))
  | (((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = false))
  & (V_bbcc = false)) & (V_bbdd = e_bb))) | (((((V_zz = true)
  & (V_bbaa = true)) & (V_bbbb = true)) & (V_bbcc = false))
  & (V_bbdd = e_bb))) | ((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = false)) & (V_bbcc = false))) | ((((((((V_zz = false)
  & (V_bbaa = true)) & (V_bbbb = true)) => ~ (V_bbcc = false))
  & ((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = false)) => ~
  (V_bbcc = false))) & ((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = true))
  => ~ (V_bbcc = false))) & ((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = false)) => ~ (V_bbcc = false))) & (V_bbdd = e_bb))))).

tff(f107, type, f107: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f107_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f107(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ee)) & ~
  (V_bbdd = e_ff)) & ~ (V_bbdd = e_ii)) & ~ (V_bbdd = e_hh))
  & (V_bbdd = e_gg)) & (V_bbaa = false)))).

tff(f109, type, f109: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f109_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f109(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> mem($int, $sum(V_ww,1), mk(0, 255)))).

tff(f110, type, f110: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f110_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f110(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ee)) & ~
  (V_bbdd = e_ff)) & ~ (V_bbdd = e_ii)) & ~ (V_bbdd = e_hh))
  & (V_bbdd = e_gg)) & (V_bbcc = true)))).

tff(f111, type, f111: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f111_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f111(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ee)) & ~
  (V_bbdd = e_ff)) & ~ (V_bbdd = e_ii)) & ~ (V_bbdd = e_hh)) & ~
  (V_bbaa = false)) & ~ (V_bbcc = true)) & $lesseq(V_bbkk,$sum(V_vv,1)))
  & (V_bbdd = e_gg)) & (V_zz = true)))).

tff(f112, type, f112: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f112_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f112(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ee)) & ~
  (V_bbdd = e_ff)) & ~ (V_bbdd = e_ii)) & ~ (V_bbdd = e_hh)) & ~
  (V_bbaa = false)) & ~ (V_bbcc = true)) & ~ ($lesseq(V_bbkk,$sum(V_vv,1))
  & (V_zz = true))) & $lesseq(V_bbkk,$sum(V_ww,1))) & (V_bbdd = e_gg)))).

tff(f113, type, f113: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f113_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f113(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ee)) & ~
  (V_bbdd = e_ff)) & ~ (V_bbdd = e_ii)) & ~ (V_bbdd = e_hh)) & ~
  (V_bbaa = false)) & ~ (V_bbcc = true)) & ~ ($lesseq(V_bbkk,$sum(V_vv,1))
  & (V_zz = true))) & ~ $lesseq(V_bbkk,$sum(V_ww,1))) & (V_bbdd = e_gg))
  & (V_zz = false)) & (V_bbbb = true)))).

tff(f115, type, f115: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f115_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f115(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((e_hh = e_bb) | (((((((((V_zz = false)
  & (V_bbaa = true)) & (V_bbbb = true)) & (V_bbcc = false))
  & ($lesseq($sum(V_ww,1),V_bbjj) | (~ $lesseq($sum(V_ww,1),V_bbjj)
  & (e_hh = e_bb)))) | (((((V_zz = true) & (V_bbaa = true))
  & (V_bbbb = false)) & (V_bbcc = false)) & (($lesseq($sum(V_ww,1),V_bbjj)
  & ((e_hh = e_gg) & (V_xx = 0))) | (~ $lesseq($sum(V_ww,1),V_bbjj)
  & (e_hh = e_bb))))) | (((((V_zz = true) & (V_bbaa = true))
  & (V_bbbb = true)) & (V_bbcc = false)) & (($lesseq($sum(V_ww,1),V_bbjj)
  & ((e_hh = e_gg) & (V_xx = 0))) | (~ $lesseq($sum(V_ww,1),V_bbjj)
  & (e_hh = e_bb))))) | (((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = false)) & (V_bbcc = false)) & (($lesseq($sum(V_ww,1),V_bbjj)
  & ((e_hh = e_gg) & (V_xx = 0))) | (~ $lesseq($sum(V_ww,1),V_bbjj)
  & (e_hh = e_bb))))) | ((((((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = true)) => ~ (V_bbcc = false)) & ((((V_zz = true)
  & (V_bbaa = true)) & (V_bbbb = false)) => ~ (V_bbcc = false)))
  & ((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = true)) => ~
  (V_bbcc = false))) & ((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = false)) => ~ (V_bbcc = false))) & (e_hh = e_bb)))))).

tff(f116, type, f116: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f116_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f116(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((V_bbee = true) <=> (e_hh = e_ii)))).

tff(f117, type, f117: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f117_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f117(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ee)) & ~
  (V_bbdd = e_ff)) & ~ (V_bbdd = e_ii)) & ~ (V_bbdd = e_hh)) & ~
  (V_bbaa = false)) & ~ (V_bbcc = true)) & ~ ($lesseq(V_bbkk,$sum(V_vv,1))
  & (V_zz = true))) & ~ $lesseq(V_bbkk,$sum(V_ww,1))) & ~ ((V_zz = false)
  & (V_bbbb = true))) & (V_bbdd = e_gg)))).

tff(f118, type, f118: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f118_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f118(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((V_bbdd = e_bb) & (0 = V_xx))
  | ((((((((((V_zz = false) & (V_bbaa = true)) & (V_bbbb = true))
  & (V_bbcc = false)) & (($lesseq($sum(V_ww,1),V_bbjj) & (V_bbdd = e_hh))
  | (~ $lesseq($sum(V_ww,1),V_bbjj) & (V_bbdd = e_bb)))) & (0 = V_xx))
  | (((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = false))
  & (V_bbcc = false)) & (($lesseq($sum(V_ww,1),V_bbjj) & (V_bbdd = e_gg))
  | ((~ $lesseq($sum(V_ww,1),V_bbjj) & (V_bbdd = e_bb)) & (0 = V_xx)))))
  | (((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = true))
  & (V_bbcc = false)) & (($lesseq($sum(V_ww,1),V_bbjj) & (V_bbdd = e_gg))
  | ((~ $lesseq($sum(V_ww,1),V_bbjj) & (V_bbdd = e_bb)) & (0 = V_xx)))))
  | (((((V_zz = false) & (V_bbaa = true)) & (V_bbbb = false))
  & (V_bbcc = false)) & (($lesseq($sum(V_ww,1),V_bbjj) & (V_bbdd = e_gg))
  | ((~ $lesseq($sum(V_ww,1),V_bbjj) & (V_bbdd = e_bb)) & (0 = V_xx)))))
  | (((((((((V_zz = false) & (V_bbaa = true)) & (V_bbbb = true)) => ~
  (V_bbcc = false)) & ((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = false))
  => ~ (V_bbcc = false))) & ((((V_zz = true) & (V_bbaa = true))
  & (V_bbbb = true)) => ~ (V_bbcc = false))) & ((((V_zz = false)
  & (V_bbaa = true)) & (V_bbbb = false)) => ~ (V_bbcc = false)))
  & (V_bbdd = e_bb)) & (0 = V_xx)))))).

tff(f119, type, f119: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f119_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f119(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ee)) & ~
  (V_bbdd = e_ff)) & ~ (V_bbdd = e_gg)) & ~ (V_bbdd = e_ii))
  & (V_bbdd = e_hh)) & (V_bbaa = false)))).

tff(f121, type, f121: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f121_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f121(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = true)) & (V_bbcc = false))
  & (($lesseq($sum($sum(V_xx,1),1),V_bbhh) & (e_bb = V_bbdd)) | (~
  $lesseq($sum($sum(V_xx,1),1),V_bbhh) & ((V_yy = 0) & (e_bb = e_ii)))))
  | (((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = false))
  & (V_bbcc = false)) & ((e_bb = e_gg) & ($sum(V_xx,1) = 0))))
  | (((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = true))
  & (V_bbcc = false)) & ((e_bb = e_gg) & ($sum(V_xx,1) = 0))))
  | (((((V_zz = false) & (V_bbaa = true)) & (V_bbbb = false))
  & (V_bbcc = false)) & ((e_bb = e_gg) & ($sum(V_xx,1) = 0))))
  | (((((((V_zz = false) & (V_bbaa = true)) & (V_bbbb = true)) => ~
  (V_bbcc = false)) & ((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = false))
  => ~ (V_bbcc = false))) & ((((V_zz = true) & (V_bbaa = true))
  & (V_bbbb = true)) => ~ (V_bbcc = false))) & ((((V_zz = false)
  & (V_bbaa = true)) & (V_bbbb = false)) => ~ (V_bbcc = false)))))).

tff(f122, type, f122: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f122_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f122(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> mem($int, $sum(V_xx,1), mk(0, 255)))).

tff(f123, type, f123: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f123_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f123(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ee)) & ~
  (V_bbdd = e_ff)) & ~ (V_bbdd = e_gg)) & ~ (V_bbdd = e_ii))
  & (V_bbdd = e_hh)) & (V_bbcc = true)))).

tff(f124, type, f124: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f124_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f124(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ee)) & ~
  (V_bbdd = e_ff)) & ~ (V_bbdd = e_gg)) & ~ (V_bbdd = e_ii)) & ~
  (V_bbaa = false)) & ~ (V_bbcc = true)) & (V_bbdd = e_hh))
  & (V_bbbb = false)))).

tff(f126, type, f126: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f126_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f126(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = true)) & (V_bbcc = false)) & ((0 = $sum(V_xx,1))
  & (($lesseq($sum($sum(V_xx,1),1),V_bbhh) & (e_gg = V_bbdd)) | (~
  $lesseq($sum($sum(V_xx,1),1),V_bbhh) & ((V_yy = 0) & (e_gg = e_ii))))))
  | ((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = false))
  & (V_bbcc = false))) | ((((V_zz = true) & (V_bbaa = true))
  & (V_bbbb = true)) & (V_bbcc = false))) | ((((V_zz = false)
  & (V_bbaa = true)) & (V_bbbb = false)) & (V_bbcc = false)))
  | ((((((((V_zz = false) & (V_bbaa = true)) & (V_bbbb = true)) => ~
  (V_bbcc = false)) & ((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = false))
  => ~ (V_bbcc = false))) & ((((V_zz = true) & (V_bbaa = true))
  & (V_bbbb = true)) => ~ (V_bbcc = false))) & ((((V_zz = false)
  & (V_bbaa = true)) & (V_bbbb = false)) => ~ (V_bbcc = false)))
  & ((0 = $sum(V_xx,1)) & (e_gg = e_bb)))))).

tff(f127, type, f127: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f127_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f127(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ee)) & ~
  (V_bbdd = e_ff)) & ~ (V_bbdd = e_gg)) & ~ (V_bbdd = e_ii)) & ~
  (V_bbaa = false)) & ~ (V_bbcc = true)) & (V_bbdd = e_hh))
  & (V_zz = true)))).

tff(f128, type, f128: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f128_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f128(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ee)) & ~
  (V_bbdd = e_ff)) & ~ (V_bbdd = e_gg)) & ~ (V_bbdd = e_ii)) & ~
  (V_bbaa = false)) & ~ (V_bbcc = true)) & ~ (V_bbbb = false)) & ~
  (V_zz = true)) & $lesseq(V_bbii,$sum(V_xx,1))) & (V_bbdd = e_hh)))).

tff(f130, type, f130: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f130_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f130(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = true)) & (V_bbcc = false))
  & (($lesseq($sum($sum(V_xx,1),1),V_bbhh) & ((0 = V_yy) & (e_ii = V_bbdd)))
  | ~ $lesseq($sum($sum(V_xx,1),1),V_bbhh))) | ((((((V_zz = true)
  & (V_bbaa = true)) & (V_bbbb = false)) & (V_bbcc = false)) & ((e_ii = e_gg)
  & ($sum(V_xx,1) = 0))) & (0 = V_yy))) | ((((((V_zz = true)
  & (V_bbaa = true)) & (V_bbbb = true)) & (V_bbcc = false)) & ((e_ii = e_gg)
  & ($sum(V_xx,1) = 0))) & (0 = V_yy))) | ((((((V_zz = false)
  & (V_bbaa = true)) & (V_bbbb = false)) & (V_bbcc = false)) & ((e_ii = e_gg)
  & ($sum(V_xx,1) = 0))) & (0 = V_yy))) | (((((((((V_zz = false)
  & (V_bbaa = true)) & (V_bbbb = true)) => ~ (V_bbcc = false))
  & ((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = false)) => ~
  (V_bbcc = false))) & ((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = true))
  => ~ (V_bbcc = false))) & ((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = false)) => ~ (V_bbcc = false))) & (e_ii = e_bb))
  & (0 = V_yy))))).

tff(f131, type, f131: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f131_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f131(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ee)) & ~
  (V_bbdd = e_ff)) & ~ (V_bbdd = e_gg)) & ~ (V_bbdd = e_ii)) & ~
  (V_bbaa = false)) & ~ (V_bbcc = true)) & ~ (V_bbbb = false)) & ~
  (V_zz = true)) & ~ $lesseq(V_bbii,$sum(V_xx,1))) & (V_bbdd = e_hh)))).

tff(f133, type, f133: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f133_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f133(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = true)) & (V_bbcc = false))
  & ($lesseq($sum($sum(V_xx,1),1),V_bbhh) | (~
  $lesseq($sum($sum(V_xx,1),1),V_bbhh) & ((V_yy = 0) & (V_bbdd = e_ii)))))
  | (((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = false))
  & (V_bbcc = false)) & ((V_bbdd = e_gg) & ($sum(V_xx,1) = 0))))
  | (((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = true))
  & (V_bbcc = false)) & ((V_bbdd = e_gg) & ($sum(V_xx,1) = 0))))
  | (((((V_zz = false) & (V_bbaa = true)) & (V_bbbb = false))
  & (V_bbcc = false)) & ((V_bbdd = e_gg) & ($sum(V_xx,1) = 0))))
  | ((((((((V_zz = false) & (V_bbaa = true)) & (V_bbbb = true)) => ~
  (V_bbcc = false)) & ((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = false))
  => ~ (V_bbcc = false))) & ((((V_zz = true) & (V_bbaa = true))
  & (V_bbbb = true)) => ~ (V_bbcc = false))) & ((((V_zz = false)
  & (V_bbaa = true)) & (V_bbbb = false)) => ~ (V_bbcc = false)))
  & (V_bbdd = e_bb))))).

tff(f134, type, f134: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f134_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f134(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ee)) & ~
  (V_bbdd = e_ff)) & ~ (V_bbdd = e_gg)) & ~ (V_bbdd = e_hh))
  & (V_bbdd = e_ii)) & (V_bbaa = false)))).

tff(f135, type, f135: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f135_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f135(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = true)) & (V_bbcc = false)) & (($lesseq($sum(V_yy,2),V_bbff)
  & (e_bb = V_bbdd)) | ~ $lesseq($sum(V_yy,2),V_bbff))) | ((((V_zz = true)
  & (V_bbaa = true)) & (V_bbbb = false)) & (V_bbcc = false)))
  | ((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = true))
  & (V_bbcc = false))) | ((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = false)) & (V_bbcc = false))) | (((((((V_zz = false)
  & (V_bbaa = true)) & (V_bbbb = true)) => ~ (V_bbcc = false))
  & ((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = false)) => ~
  (V_bbcc = false))) & ((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = true))
  => ~ (V_bbcc = false))) & ((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = false)) => ~ (V_bbcc = false)))))).

tff(f137, type, f137: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f137_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f137(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> $lesseq(0,$sum(V_yy,1)))).

tff(f138, type, f138: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f138_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f138(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ee)) & ~
  (V_bbdd = e_ff)) & ~ (V_bbdd = e_gg)) & ~ (V_bbdd = e_hh))
  & (V_bbdd = e_ii)) & (V_bbcc = true)))).

tff(f139, type, f139: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f139_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f139(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ee)) & ~
  (V_bbdd = e_ff)) & ~ (V_bbdd = e_gg)) & ~ (V_bbdd = e_hh))
  & (V_bbdd = e_ii)) & (V_bbbb = false)))).

tff(f140, type, f140: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f140_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f140(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ee)) & ~
  (V_bbdd = e_ff)) & ~ (V_bbdd = e_gg)) & ~ (V_bbdd = e_hh))
  & (V_bbdd = e_ii)) & (V_zz = true)))).

tff(f141, type, f141: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f141_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f141(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ee)) & ~
  (V_bbdd = e_ff)) & ~ (V_bbdd = e_gg)) & ~ (V_bbdd = e_hh))
  & $lesseq(V_bbgg,$sum(V_yy,1))) & (V_bbdd = e_ii)))).

tff(f142, type, f142: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f142_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f142(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ((((((((((((($true & ~ (V_bbdd = e_bb)) & ~
  (V_bbdd = e_cc)) & ~ (V_bbdd = e_dd)) & ~ (V_bbdd = e_ee)) & ~
  (V_bbdd = e_ff)) & ~ (V_bbdd = e_gg)) & ~ (V_bbdd = e_hh)) & ~
  (V_bbaa = false)) & ~ (V_bbcc = true)) & ~ (V_bbbb = false)) & ~
  (V_zz = true)) & ~ $lesseq(V_bbgg,$sum(V_yy,1))) & (V_bbdd = e_ii)))).

tff(f144, type, f144: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f144_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f144(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> (((((((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = true)) & (V_bbcc = false)) & ($lesseq($sum(V_yy,2),V_bbff) | (~
  $lesseq($sum(V_yy,2),V_bbff) & (V_bbdd = e_bb)))) | (((((V_zz = true)
  & (V_bbaa = true)) & (V_bbbb = false)) & (V_bbcc = false))
  & (V_bbdd = e_bb))) | (((((V_zz = true) & (V_bbaa = true))
  & (V_bbbb = true)) & (V_bbcc = false)) & (V_bbdd = e_bb)))
  | (((((V_zz = false) & (V_bbaa = true)) & (V_bbbb = false))
  & (V_bbcc = false)) & (V_bbdd = e_bb))) | ((((((((V_zz = false)
  & (V_bbaa = true)) & (V_bbbb = true)) => ~ (V_bbcc = false))
  & ((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = false)) => ~
  (V_bbcc = false))) & ((((V_zz = true) & (V_bbaa = true)) & (V_bbbb = true))
  => ~ (V_bbcc = false))) & ((((V_zz = false) & (V_bbaa = true))
  & (V_bbbb = false)) => ~ (V_bbcc = false))) & (V_bbdd = e_bb))))).

tff(f145, type, f145: (bool * $int * $int * $int * $int * $int * bool *
  enum_aa * bool * bool * bool * bool * $int * $int * $int * $int * $int *
  $int * $int * $int * $int * $int * $int * $int * $int * $int * $int *
  $int * $int * bool * enum_aa * bool * bool * bool) > $o).

tff(f145_def, axiom, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:$int,
  V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool, V_oo:
  bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:$int,
  V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int, V_bbkk:
  $int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:$int,
  V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  (f145(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) <=> ($true & (V_bbee = true)))).

tff(bbss_179, conjecture, ![V_zz:bool, V_yy:$int, V_xx:$int, V_ww:$int, V_vv:
  $int, V_uu:$int, V_tt:bool, V_ss:enum_aa, V_rr:bool, V_qq:bool, V_pp:bool,
  V_oo:bool, V_nn:$int, V_mm:$int, V_ll:$int, V_kk:$int, V_jj:$int, V_bbqq:
  $int, V_bbpp:$int, V_bboo:$int, V_bbnn:$int, V_bbmm:$int, V_bbll:$int,
  V_bbkk:$int, V_bbjj:$int, V_bbii:$int, V_bbhh:$int, V_bbgg:$int, V_bbff:
  $int, V_bbee:bool, V_bbdd:enum_aa, V_bbcc:bool, V_bbbb:bool, V_bbaa:bool]:
  ((f1(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp,
  V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm,
  V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd,
  V_bbcc, V_bbbb, V_bbaa) & (f4(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu, V_tt,
  V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp,
  V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg,
  V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) & ($true & (f140(V_zz,
  V_yy, V_xx, V_ww, V_vv, V_uu, V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn,
  V_mm, V_ll, V_kk, V_jj, V_bbqq, V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll,
  V_bbkk, V_bbjj, V_bbii, V_bbhh, V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc,
  V_bbbb, V_bbaa) & $true)))) => (f137(V_zz, V_yy, V_xx, V_ww, V_vv, V_uu,
  V_tt, V_ss, V_rr, V_qq, V_pp, V_oo, V_nn, V_mm, V_ll, V_kk, V_jj, V_bbqq,
  V_bbpp, V_bboo, V_bbnn, V_bbmm, V_bbll, V_bbkk, V_bbjj, V_bbii, V_bbhh,
  V_bbgg, V_bbff, V_bbee, V_bbdd, V_bbcc, V_bbbb, V_bbaa) & $true))).
