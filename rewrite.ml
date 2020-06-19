(*  Copyright 2003 INRIA  *)
Version.add "$Id$";;



open Expr;;
open Phrase;;


type rwrt_tbl = (string, expr * expr) Hashtbl.t;;
type rwrt_tbls = rwrt_tbl * rwrt_tbl;;
let tbl_term = ref (Hashtbl.create 42);;
let tbl_prop = ref (Hashtbl.create 42);;
exception Bad_Rewrite_Rule of string * expr;;


type rwrt_rule = Positive of expr * expr | Negative of expr * expr;;
let pexp = Print.expr_soft (Print.Chan stdout);;
let print_rule r = let sign = match r with Positive _ -> "+" | _ -> "-" in
  match r with Positive(e1, e2) | Negative(e1, e2) -> 
    print_endline "Rewrite rule :"; pexp e1; print_string (" --->"^sign^" "); pexp e2; print_endline ""
;;

let rec ( @@ ) l = function 
  | [] -> l
  | t::q -> let q' = (l@@q) in if List.mem t q' then q' else t::q'
;;
let ( % ) f g = fun x -> f (g x);;
let rec is_lit = function
  | Evar _ | Eapp (Evar _, _, _) -> true
  | Enot (e, _) -> is_lit e 
  | _ -> false;;

let rec pos_rul e1 e2 = match e1 with 
  | Enot(e1', _) -> begin match e2 with 
    | Enot(e2', _) -> neg_rul e1' e2'
    | _ -> neg_rul e1' (enot e2) end
  | _ -> Positive(e1, e2) 
and neg_rul e1 e2 = match e1 with 
  | Enot(e1', _) -> begin match e2 with 
    | Enot(e2', _) -> pos_rul e1' e2'
    | _ -> pos_rul e1' (enot e2) end
  | _ -> Negative(e1, e2) 
;;

let rec format e = match e with 
  | Evar _ | Eapp _ -> e
  | Enot(e', _) -> begin match e' with 
    | Enot (e'', _) -> format e''
    | Evar _ | Eapp _ -> e
    | Eand (e1, e2, _) -> eor (format (enot e1), format (enot e2))
    | Eor (e1, e2, _) -> eand (format (enot e1), format (enot e2))
    | Eall (e1, e2, _) -> eex (e1, format (enot e2))
    | Eex (e1, e2, _) -> eall (e1, format (enot e2))
    | _ -> e
    end
  | Eand (e1, e2, _) -> eand (format e1, format e2)
  | Eor (e1, e2, _) -> eor (format e1, format e2)
  | Eimply (e1, e2, _) -> eimply (format e1, format e2)
  | Eequiv (e1, e2, _) -> eequiv(format e1, format e2)


  | Eall (e1, e2, _) -> eall(e1, format e2)
  | Eex (e1, e2, _) -> eex(e1, format e2)
  | _ -> e
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
let rec fv_from_name s expr = match expr with
  | Emeta (e, _) -> fv_from_name s e
  | Evar (s', _) -> if s = s' then Some expr else None
  | Eapp (e1, args, _) -> let rec aux = function
    | [] -> None | t::q -> let f = fv_from_name s t in if f = None then aux q else f in  aux (e1::args)
  | Enot (e, _) -> (fv_from_name s e)
  | Eand(e1, e2, _) | Eor(e1, e2, _) | Eimply(e1, e2, _) | Eequiv(e1, e2, _) -> 
    let a = fv_from_name s e1 in if a = None then fv_from_name s e2 else a
  | Eall(e1, e2, _) | Eex(e1, e2, _) -> fv_from_name s e2 (*TODO Fix*)
  | _ -> None;;
let skolem expr = 
  let rec aux vars expr = match expr with
    | Emeta (e, _) -> emeta (aux vars e)
    | Evar _  | Eapp _ -> expr
    | Enot (e, _) -> enot(aux vars e)
    | Eand(e1, e2, _) -> eand(aux vars e1, aux vars e2)
    | Eor(e1, e2, _) -> eor(aux vars e1, aux vars e2)
    | Eimply(e1, e2, _) -> eimply(aux vars e1, aux vars e2)
    | Eequiv(e1, e2, _) -> eequiv(aux vars e1, aux vars e2)
    | Eall(e1, e2, _) -> aux (e1::vars) e2 
    | Eex(v, e2, _) -> let t = earrow(List.map get_type vars) (get_type v) in begin 
      match v with Evar(s,_) -> aux vars (replace_var s (eapp(tvar (newname()) t, vars)) e2)
      | _ -> failwith "skolem_aux" end
    | e -> e in aux (List.map (fun s -> Option.get (fv_from_name s expr)) (get_fv expr)) expr;;
 
let rec hyp_to_rwrt_rules hyp = match hyp with
  | Emeta (e, _) -> []
  | Evar _  | Eapp _ -> [Positive(hyp, etrue); Negative(hyp, etrue)]

  | Earrow (args, e, _) -> []

  | Enot (e, _) -> (hyp_to_rwrt_rules (eimply(e, efalse)))
  | Eand (e1, e2, _) -> []
  | Eor (e1, e2, _) -> []
  | Eimply (e1, e2, _) -> let e1, e2 = if (is_lit e1) then e1, e2 else e2, e1 in 
    (if is_lit e1 then [pos_rul ((skolem % format) e1)  ((skolem % format) e2)]@@[pos_rul ((skolem % format) (enot e1))  ((skolem % format) (enot e2))] else [])
  | Eequiv (e1, e2, _) -> (hyp_to_rwrt_rules (eimply(e1, e2)))@@(hyp_to_rwrt_rules (eimply(e2, e1)))
  | Etrue | Efalse -> []

  | Eall (e1, e2, _) -> hyp_to_rwrt_rules e2
  | Eex (e1, e2, _) -> []
  | Etau (e1, e2, _) -> []
  | Elam (e1, e2, _) -> []
  | _ -> []
;;
let normalize_fm p = p;;
let normalize_list l = List.map normalize_fm l;;
let add_rwrt_term a b = ();;
let add_rwrt_prop a b = ();;

let rec select_rwrt_rules_aux accu phrase =
  match phrase with
  | Rew (name, body, flag, sign)
       when (flag = 2) || (flag = 1)
    -> raise (Bad_Rewrite_Rule (name, body))
  | Hyp (name, body, flag)
       when (flag = 2) || (flag = 1) (*|| (flag = 12) || (flag = 11) *)
    ->  let rwrt = hyp_to_rwrt_rules body in 
      List.iter print_rule rwrt;
       phrase :: accu;
  | Def (DefRec _) ->
     (* Recursive definitions are not turned into rewrite-rules (yet) *)
     phrase :: accu
  | Def d ->
     (*let (name, body) = get_rwrt_from_def d in
     add_rwrt_term name body;*)
     phrase :: accu
  |  _ -> phrase :: accu
;;

let select_rwrt_rules phrases =
  Log.debug 1 "====================";
  Log.debug 1 "Select Rewrite Rules";
  (*List.iter (Print.phrase (Print.Chan stdout)) phrases; *)
  List.rev (List.fold_left select_rwrt_rules_aux [] phrases)
;;
