(*  Copyright 2003 INRIA  *)
Version.add "$Id$";;

open Expr;;
open Phrase;;


module Smap = Map.Make(String);;

type rule = bool option * expr * expr;;
type rule_matches = rule list;;
type dec_tree = DecTree of rule_matches * dec_tree Smap.t list;;

exception Bad_Rewrite_Rule of string * expr;;

let rec ( @@ ) l l' = match l with 
  | [] -> l'
  | t::q -> let q' = (q@@l') in if List.mem t q' then q' else t::q'
;;

let ( % ) f g = fun x -> f (g x);;

let rec ( <<? ) l l' = match l with [] -> true | t::q -> (List.mem t l') && (q <<? l');;

let rec ( /| ) l l' = match l with [] -> [] | t::q -> if List.mem t l' then t::(q /| l') else q /| l';;

let nnot = function Enot (e, _) -> e | e -> enot e;;

let rec ( --> ) e1 e2 = match e1 with
        | Enot (e, _) -> e --> (nnot e2)
        | _ -> (None, e1, e2);;

let rec ( -->+ ) e1 e2 = match e1 with
        | Enot (e, _) -> e -->- (nnot e2)
        | _ -> (Some(true), e1, e2)
and ( -->- ) e1 e2 = match e1 with
        | Enot (e, _) -> e -->+ (nnot e2)
        | _ -> (Some(false), e1, e2);;


let ( <<| ) tree rule = let rec aux tree = function
        | Eapp(Evar(s, _), args, _) -> Smap.update s (function
    | None -> Some (DecTree([rule], List.map (aux Smap.empty) args))
    | Some (DecTree(matches, args')) -> Some (DecTree (rule::matches, List.map2 aux args' args))
  ) tree
  | Evar _ -> Smap.update "" (function
    | None -> Some (DecTree ([rule], []))
    | Some (DecTree (matches, args)) -> Some (DecTree (rule::matches, args))
  ) tree
  | _ -> failwith "add_rule"
  in let (_, r1, _) = rule in tree := aux !tree r1
;;

let ( !! ) = function
  | None -> None
  | Some e -> Some (not e)
;;

let ( *< ) a b = match b with None -> true | Some true | Some false -> a = b;; 

type tbl = (string, rule) Hashtbl.t;;
type poltbl = (string, rule) Hashtbl.t;;
let tbl_term = ref (Hashtbl.create 42);;
let tbl_prop = ref (Hashtbl.create 42);;
let op = ref (Hashtbl.create 42);;
let rule_freq = Hashtbl.create 42;;


let pexp = Print.expr_soft (Print.Chan stdout);;

let sign pol = match pol with Some p -> if p then "+" else "-" | _ -> "";;

let debug_rule ?(i=1) (pol, e1, e2) =
        Log.debug i "%a -->%s %a\n" Print.pp_expr e1 (sign pol) Print.pp_expr e2; 
;;

let rules = ref [];;

let rec is_lit = function
  | Evar _ | Eapp _ -> true
  | Enot (e, _) -> is_lit e 
  | _ -> false
;;

let rec lit_pol = function
  | Evar _ | Eapp _ -> true
  | Enot(e, _) -> not (lit_pol e)
  | _ -> assert false
;;

let rec get_hash = let rec aux b = function
  | Eapp (Evar(sym, _), args, _) -> sym
  | Enot (t1, _) -> aux (not b) t1
  | _ -> ""
  in aux true
;;
let propTree = ref Smap.empty;;
let termTree = ref Smap.empty;;

let rec matching_rules pol tree expr = 
        let fmt l = List.filter (fun (pol',_,_) -> pol *< pol') l in
        (match Smap.find_opt "" tree with
    | None -> []
    | Some(DecTree(matches, _)) -> fmt matches) @@ begin
            let s = get_hash expr in
            match Smap.find_opt s tree with 
      | None -> []
      | Some (DecTree (matches, args)) -> (match expr with
        | Eapp(_, args', _) -> List.fold_left2 (fun acc tree expr ->
                        acc /| (matching_rules pol tree expr)
                        ) matches args args'
        | _ -> [])
    end
;;

let rec fv_from_name s expr = match expr with
  | Emeta (e, _) -> fv_from_name s e
  | Evar (s', _) -> if s = s' (*&& get_type expr <> type_type*) then Some expr else None
  | Eapp (e1, args, _) -> let rec aux = function
    | [] -> None | t::q -> let f = fv_from_name s t in if f = None then aux q else f in  aux (e1::args)
  | Enot (e, _) -> (fv_from_name s e)
  | Eand(e1, e2, _) | Eor(e1, e2, _) | Eimply(e1, e2, _) | Eequiv(e1, e2, _) -> 
    let a = fv_from_name s e1 in if a = None then fv_from_name s e2 else a
  | Eall(e1, e2, _) | Eex(e1, e2, _) -> fv_from_name s e2 
  | _ -> None
;;

exception ApplyRule;;

let rec apply_rule (pol, r1, r2) e =
  let rec pole = function Enot(e,_) -> not (pole e) | _ -> true in 
  let rec aux b acc e1 e2 = match e1, e2 with
    | _, Enot(e2', _) -> aux (!! b) acc e1 e2'
    | Eapp (v, args, _), Eapp(v', args', _) when get_name v = get_name v' ->
      List.fold_left2 (aux b) acc args args'
    | Evar _, _ -> if b=pol then (
      if List.mem_assq e1 acc then (
        if not (equal (List.assq e1 acc) e2) then raise ApplyRule else acc
        ) else (e1, e2)::acc) else raise ApplyRule
    | _ -> raise ApplyRule
  in let f_map map = let types, vars = List.partition (fun (x,_) -> get_type x = type_type) map in
    types@@vars
  in 
  try let map = f_map (aux (match pol with Some _ -> Some true | _ -> pol) [] r1 e) in
  (if pole e then (fun x -> x) else enot) (try 
    substitute map r2
  with _ -> debug_rule ~i:(-1) (pol, r1, r2); debug_rule ~i:(-1) (None, e, r2); raise (Ill_typed_substitution map))
    with ApplyRule -> e 

;;


(*let not_cyclic t1 t2 = true (*TODO*)*)
let get_rwrt_terms =
  let rec prof = function
     | Eapp(_, [], _) -> 1
     | Evar _ -> 0
     | Eapp(_, t::args, _) -> 
        1+List.fold_left (fun a b -> max a (prof b)) (prof t) args in
  let rec aux vars = function
  | Eapp (Evar ("=", _), [t1; t2], _) ->
    let aux' t1 t2 = if is_lit t1 
      && (get_fv t2) <<? (get_fv t1) 
      && (get_fv t1) <<? vars
      && (prof t2 <= prof t1)
    then [t1 --> t2] else []
    in  (aux' t1 t2) (*@ (aux' t2 t1)*)
  | Eall(Evar(s,_), e, _) -> aux (s::vars) e
  | Eand(e1, e2, _) -> (aux vars e1)@(aux vars e2)
  | _ -> [] in aux []
;;


let rec nnf e = match e with 
  | Evar _ | Eapp _ -> e
  | Enot(e', _) -> begin match e' with 
    | Enot (e'', _) -> nnf e''
    | Evar _ | Eapp _ -> e
    | Eand (e1, e2, _) -> eor (nnf (enot e1), nnf (enot e2))
    | Eor (e1, e2, _) -> eand (nnf (enot e1), nnf (enot e2))
    | Eall (e1, e2, _) -> eex (e1, nnf (enot e2))
    | Eex (e1, e2, _) -> eall (e1, nnf (enot e2))
    | Etrue -> efalse
    | Efalse -> etrue
    | _ -> e
    end
  | Eand (e1, e2, _) -> eand (nnf e1, nnf e2)
  | Eor (e1, e2, _) -> eor (nnf e1, nnf e2)
  | Eimply (e1, e2, _) -> eimply (nnf e1, nnf e2)
  | Eequiv (e1, e2, _) -> eequiv(nnf e1, nnf e2)


  | Eall (e1, e2, _) -> eall(e1, nnf e2)
  | Eex (e1, e2, _) -> eex(e1, nnf e2)
  | _ -> e
;;

let rec miniscoping expr = let mini = miniscoping in
    let pall v e = if List.mem (get_name v) (get_fv e) then eall(v,e) else e in
    let pex v e = if List.mem (get_name v) (get_fv e) then eex(v,e) else e in
    let auxQ e a b = (function
            | Eand _ -> eand
            | Eor _ -> eor
            | Eall _ -> fun (x, y) -> pall x y
            | Eex _ -> fun (x, y) -> pex x y
            | _ -> assert false) e (a,b)
    in
    match expr with 
    | Emeta _  | Evar _  | Eapp _ | Enot _ -> expr
    | Eand(e1, e2, _) -> eand(mini e1, mini e2)
    | Eor(e1, e2, _) -> eor(mini e1, mini e2)
    | Eex(e1, Eor(e1', e2', _), _) -> eor(pex (mini e1) (mini e1'), pex (mini e1) (mini e2'))
    | Eall(e1, Eand(e1', e2', _), _) -> eand(pall (mini e1) (mini e1'), pall (mini e1) (mini e2'))
    | Eall(e1, e2, _) | Eex(e1, e2, _) -> let q = auxQ expr in (
            match e2 with 
                | Eand (e1', e2', _) | Eor (e1', e2', _) -> 
                        let o = auxQ e2 in
                        o (mini (q e1 e1')) (mini (q e1 e2'))
                | _ -> q e1 (mini e2)
    )
    | e -> e
;;
let rec replace_var s r expr = 
  if not (List.mem s (get_fv expr)) then expr else
  match expr with
  | Evar (s', _) -> if s = s' then r else expr 
  | Emeta (e, _) -> emeta (replace_var s r e)
  | Eapp (e, args, _) -> eapp(e, List.map (replace_var s r) args)
  | Enot (e, _) -> enot(replace_var s r e)
  | Eand(e1, e2, _) -> eand(replace_var s r e1, replace_var s r e2)
  | Eor(e1, e2, _) -> eor(replace_var s r e1, replace_var s r e2)
  | Eimply(e1, e2, _) -> eimply(replace_var s r e1, replace_var s r e2)
  | Eequiv(e1, e2, _) -> eequiv(replace_var s r e1, replace_var s r e2)
  | Eall(Evar (s', _), _, _) | Eex(Evar (s', _), _, _) when s' = s -> expr
  | Eall(e1, e2, _) -> eall(e1, replace_var s r e2) 
  | Eex(e1, e2, _) -> eex(e1, replace_var s r e2)
  | _ -> expr
;;



let skolem expr = 
  let rec aux vars expr = match expr with
    | Emeta _  | Evar _  | Eapp _ -> expr
    | Enot (e, _) -> expr
    | Eand(e1, e2, _) -> eand(aux vars e1, aux vars e2)
    | Eor(e1, e2, _) -> eor(aux vars e1, aux vars e2)
    | Eimply(e1, e2, _) -> expr
    | Eequiv(e1, e2, _) -> expr
    | Eall(e1, e2, _) -> eall (e1, aux (e1::vars) e2) 
    | Eex(v, e2, _) -> 
      let args, types = List.partition (fun x -> get_type x<>type_type) vars in
      let t = earrow(List.map get_type args) (get_type v) in
      let t = List.fold_left (fun acc x -> eall(x, acc)) t types in
      let args = (List.rev types) @ args in 
      let s = get_name v in 
      aux vars (replace_var s (eapp(tvar (newname()) t, args)) e2)
    | e -> e in aux (List.filter_map (fun s -> fv_from_name s expr) (get_fv expr)) expr
;;

let get_rwrt_from_def = function
  | DefReal (name, id, ty, args, body, _) ->
     (name, eeq (eapp (tvar id ty, args)) body)
  | DefPseudo (_, id, ty, args, body) ->
     ("pseudoDef_"^id, eeq (eapp (tvar id ty, args)) body)
  | DefRec _ -> assert false   (* This case has been filtered out in add_phrase *)
;;


let id x = x;;
let format = (if !Globals.skolem then skolem else id) % (if !Globals.miniscoping then miniscoping else id)% nnf;;

let rec exp_to_rules ex = match ex with
  | Emeta (e, _) -> []
  | Eapp (Evar("=",_),_,_) -> []
  | Evar _  | Eapp _ -> [ex -->- etrue]

  | Earrow (args, e, _) -> []

  | Enot (e, _) -> (exp_to_rules (eimply(e, efalse)))
  | Eand (e1, e2, _) -> (exp_to_rules e1)@(exp_to_rules e2)
  | Eor (e1, e2, _) -> []
  | Eimply (e1, e2, _) ->  
    (if is_lit e1 && (get_fv e2 <<? get_fv e1) then [e1 -->+ (format e2)] else []) @@
    (if is_lit e2 && (get_fv e1 <<? get_fv e2) then [e2 -->- nnf (nnot (format (nnot e1)))] else [])
  | Eequiv (e1, e2, _) -> (exp_to_rules (eimply(e1, e2))) @@ (exp_to_rules (eimply(e2, e1)))
 
  | Etrue | Efalse -> []

  | Eall (e1, e2, _) -> exp_to_rules e2
  | Eex (e1, e2, _) -> []
  | Etau (e1, e2, _) -> []
  | Elam (e1, e2, _) -> []
;;
let applicable = let rec aux pol tree = function
        | Enot(e, _) -> aux (!!pol) tree e
        | e -> matching_rules pol !tree e
in aux
;;

let rsort = List.sort (fun r1 r2 -> Hashtbl.find rule_freq r2 - Hashtbl.find rule_freq r1);;
let rec norm_term t =
  let rec aux rules t =
    match rules with
      | [] -> t
      | r :: tl ->
        aux tl (apply_rule r t)
  in
  let rules = applicable None termTree t in
  let new_t = aux rules t in
  if not (Expr.equal t new_t)
  then
    begin
      Log.debug 1 "rewrite term";
      Log.debug 1 "## %a --> %a" Print.pp_expr t Print.pp_expr new_t;
      norm_term new_t
    end
  else
    begin
      match t with
      | Eapp (f, args, _) -> 
	eapp (f, (List.map norm_term args))
      | Enot (t1, _) ->
	enot (norm_term t1)
      | Eand (t1, t2, _) ->
	eand (norm_term t1, norm_term t2)
      | Eor (t1, t2, _) ->
	eor (norm_term t1, norm_term t2)
      | Eimply (t1, t2, _) ->
	eimply (norm_term t1, norm_term t2)
      | Eequiv (t1, t2, _) ->
	eequiv (norm_term t1, norm_term t2)

      | _ -> t
    end

;;
let rec profondeur = function
    | Eall (_, e, _) | Eex (_, e, _)  | Enot (e, _) -> 1 + profondeur e
    | Eand (e1, e2, _) | Eor (e1, e2, _) | Eimply (e1, e2, _) | Eequiv (e1, e2, _) -> 1 + max (profondeur e1) (profondeur e2)
    | _ -> 0;;
  
let shuffle l = let (_, res) = List.split (List.sort (fun (a, _) (b, _) -> a - b) (List.map (fun x -> Random.bits(), x) l)) in res;;

let rec normalize_fm p = let applicable p = rsort (applicable (Some true) propTree p) in 
        if not (is_lit p) then p else 
        let rec aux l p = let p' = norm_term p in if List.exists (equal p') l then p else let p'' = aux (p'::l) p' in p'' in 
        let p = aux [p] p in
        let rules = applicable p in
        let rec aux p = function 
        | [] -> p
        | t::q -> let p' = apply_rule t p in  if equal p p' then aux p q 
        else begin 
                Hashtbl.replace rule_freq t ((Hashtbl.find rule_freq t)+1);
                debug_rule t;
                p'
        end
        in let res = aux p rules in 
        if equal res p then p else let p' = aux res (applicable res) in if equal p p' then nnf p else nnf p'
;;

let normalize_list l =
        List.map (fun x -> let p = normalize_fm x in if not(equal x p) then debug_rule (None, x, p); p) l;;

let _add_rwrt_term s e = let l = get_rwrt_terms e in
  List.iter (debug_rule ~i:(1)) l;
  List.iter (fun r -> termTree <<| r; Hashtbl.add rule_freq r 0) l; 
  List.length l > 0;;
let _add_rwrt_prop s e = let rules = (exp_to_rules e) in
List.iter (fun r -> propTree <<| r; Hashtbl.add rule_freq r 0) rules; List.length rules > 0
;;

let add_rwrt_term s e = let _ = _add_rwrt_term s e in ();;
let add_rwrt_prop s e = let _ = _add_rwrt_prop s e in ();;
;;

let rec add_phrase phrase =
  match phrase with
  | Rew (name, body, flag)
       when (flag = 2) || (flag = 1)
    -> add_rwrt_term name body; add_rwrt_prop name body; phrase
  | Hyp (name, body, flag)
       (*when (flag = 2) || (flag = 1) || (flag = 12) || (flag = 11) *)
    -> if (!Globals.modulo_heuri) then 
            let b = _add_rwrt_term name body in
            let b' = _add_rwrt_prop name body in
            (if (b||b') then Rew(name, body, if b then 0 else 1)  else phrase)
        else phrase
  | Def (DefRec _) ->
     (* Recursive definitions are not turned into rewrite-rules (yet) *)
     phrase 
  | Def d ->
     let (name, body) = get_rwrt_from_def d in
     add_rwrt_term name body;
     phrase
  |  _ -> phrase
;;

let select_rwrt_rules phrases =
  let i = if !Globals.debug_rwrt then -1 else 1 in 
  Log.debug i "====================";
  Log.debug i "Select Rewrite Rules";
  let res = List.map add_phrase phrases in 
  Log.debug i "--------------term rwrt rules:";
  Smap.iter (fun k (DecTree(t,_)) -> List.iter (debug_rule ~i:i) t) !termTree;
  Log.debug i "--------------prop rwrt rules:";
  Smap.iter (fun k (DecTree(t,_)) -> List.iter (debug_rule ~i:i) t) !propTree;
  Log.debug i "\n====================";
  res
;;
