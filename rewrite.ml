(*  Copyright 2003 INRIA  *)
Version.add "$Id$";;



open Expr;;
open Phrase;;


type rwrt_tbl = (string, expr * expr) Hashtbl.t;;
type rwrt_tbls = rwrt_tbl * rwrt_tbl;;
let tbl_term = ref (Hashtbl.create 42);;
let tbl_prop = ref (Hashtbl.create 42);;
exception Bad_Rewrite_Rule of string * expr;;

type rwrt_rule = bool * expr * expr;;
let pexp = Print.expr_soft (Print.Chan stdout);;
let print_rule r = let sign = match r with b,_,_ -> if b then "+" else "-" in
  match r with (_, e1, e2) -> 
    print_endline "Rewrite rule :"; pexp e1; print_string (" --->"^sign^" "); pexp e2; print_endline ""
;;

let rules = ref [];;

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
  | _ -> (true, e1, e2) 
and neg_rul e1 e2 = match e1 with 
  | Enot(e1', _) -> begin match e2 with 
    | Enot(e2', _) -> pos_rul e1' e2'
    | _ -> pos_rul e1' (enot e2) end
  | _ -> (false, e1, e2) 
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
  | Eall(e1, e2, _) | Eex(e1, e2, _) -> fv_from_name s e2 
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

(* new assoc and mem_assoc functions
   with the Expr.equal equality
   replacing =
*)

let rec assoc_expr x = function
  | [] -> raise Not_found
  | (a,b)::l -> if (Expr.equal a x) then b else assoc_expr x l
;;

let rec mem_assoc_expr x = function
  | [] -> false
  | (a, b)::l -> (Expr.equal a x) || mem_assoc_expr x l
;;

let rec mem_expr x = function
  | [] -> false
  | a :: l -> (Expr.equal a x) || mem_expr x l
;;  

exception Unif_failed;;

let rec unif_aux l e1 e2 =
  match e1, e2 with
    | Evar (_, _), _ ->
      if  not(mem_assoc_expr e1 l) then (e1, e2)::l
      else if (Expr.equal (assoc_expr e1 l) e2) then l
      else raise Unif_failed

    | Eapp (Evar (s1, _), args1, _), Eapp (Evar(s2, _), args2, _) when (s1 = s2)
         -> (try
	      List.fold_left2 unif_aux l args1 args2
	     with
	       | Invalid_argument _ -> raise Unif_failed)

    | Enot (x1, _), Enot (y1, _)
      -> unif_aux l x1 y1
    | Eand (x1, x2, _), Eand (y1, y2, _)
      -> List.fold_left2 unif_aux l [x1;x2] [y1;y2]
    | Eor (x1, x2, _), Eor (y1, y2, _)
      -> List.fold_left2 unif_aux l [x1;x2] [y1;y2]
    | Eimply (x1, x2, _), Eimply (y1, y2, _)
      -> List.fold_left2 unif_aux l [x1;x2] [y1;y2]
    | Eequiv (x1, x2, _), Eequiv (y1, y2, _)
      -> List.fold_left2 unif_aux l [x1;x2] [y1;y2]

    | _, _ when (Expr.equal e1 e2) -> (e1, e2)::l
    | _, _ -> raise Unif_failed
;;

let unif t1 t2 = unif_aux [] t1 t2;;        


let apply_rule r = let (pol, _, _) = r in
        let e1,e2 = match r with (true, e1, e2) | (false, e1, e2) -> e1, e2 in
        let rec aux b e = match e with
                | Eapp _ | Evar _ -> if pol = b then try substitute (unif e1 e) e2 with Unif_failed -> e else e
                | Emeta _ -> e

                | Earrow _ -> e

                | Enot (e', _) -> enot (aux (not b) e')
                | Eand (e1', e2', _) ->   eand (aux b e1', aux b e2')
                | Eor (e1', e2', _) ->    eor (aux b e1', aux b e2')

                | Eimply (e1', e2', _) -> eimply (aux (not b) e1', aux b e2')

                | Eequiv (e1', e2', _) -> eequiv (aux b (eimply (e1', e2')), aux b (eimply (e2', e1')))

                | Etrue  | Efalse -> e 

                | Eall (v, e', _) ->  if equal v e1 then e else eall (v, aux b e')
                | Eex (v, e', _) -> if equal v e1 then e else eex (v, aux b e')
                | Etau _ -> e
                | Elam _ -> e
        in aux true
;;


let rec hyp_to_rwrt_rules hyp = match hyp with
  | Emeta (e, _) -> []
  | Evar _  | Eapp _ -> [(true, hyp, etrue); (false, hyp, etrue)]

  | Earrow (args, e, _) -> []

  | Enot (e, _) -> (hyp_to_rwrt_rules (eimply(e, efalse)))
  | Eand (e1, e2, _) -> []
  | Eor (e1, e2, _) -> []
  | Eimply (e1, e2, _) -> if not (is_lit e1) then (if is_lit e2 then hyp_to_rwrt_rules (eimply (enot e2, enot e1)) else []) else 
    (if is_lit e1 then [pos_rul ((skolem % format) e1)  ((skolem % format) e2)]@@[pos_rul ((skolem % format) (enot e1))  ((skolem % format) (enot e2))] else [])
  | Eequiv (e1, e2, _) -> (hyp_to_rwrt_rules (eimply(e1, e2)))@@(hyp_to_rwrt_rules (eimply(e2, e1)))
  | Etrue | Efalse -> []

  | Eall (e1, e2, _) -> hyp_to_rwrt_rules e2
  | Eex (e1, e2, _) -> []
  | Etau (e1, e2, _) -> []
  | Elam (e1, e2, _) -> []
  | _ -> []
;;
let rec normalize_fm p =  
        let rec aux = function 
        | [] -> p
        | t::q -> let p' = apply_rule t (aux q) in  p'
        in let res = aux !rules in (*if not (equal p res) then begin print_string "\nForme normale de "; Print.expr (Print.Chan stdout) p; print_string " :\n"; Print.expr (Print.Chan stdout) res; end; *)res
;;

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
    ->  let rwrt = hyp_to_rwrt_rules body in rules := !rules @@ rwrt; 
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
