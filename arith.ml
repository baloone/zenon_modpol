
open Expr

let equal x y = Expr.compare x y = 0

(* Types manipulation *)
let get_type = function
    | Etrue | Efalse -> "$o"
    | Etau (_, t, _, _) -> t
    | e -> begin match priv_type e with
        | None -> Namespace.univ_name
        | Some s -> s
    end

let is_int e = get_type e = "$int"
let is_rat e = get_type e = "$rat"

(* Manipulation of expressions/formulas *)
exception NotaFormula

let is_z v = Z.equal (Q.den v) Z.one
let is_q v = not (Z.equal (Q.den v) Z.zero || is_z v)
let floor v =
    try
         Q.of_bigint (Z.ediv (Q.num v) (Q.den v))
    with Division_by_zero -> v
let ceil v = Q.neg (floor (Q.neg v))

let comp_neg = function
    | "$less" -> "$greatereq"
    | "$lesseq" -> "$greater"
    | "$greater" -> "$lesseq"
    | "$greatereq" -> "$less"
    | "$is_int" -> "$not_is_int"
    | "$is_rat" -> "$not_is_rat"
    | _ -> assert false

(* Combine types *)
let ctype t t' = match t, t' with
    | "$int", "$int" -> "$int"
    | "$int", "$rat" | "$rat", "$int" | "$rat", "$rat" -> "$rat"
    | _ -> "$real"
let etype e e' = ctype (get_type e) (get_type e')

let mk_app t s l = add_type t (eapp (s, l))

let const s =
    if is_z (Q.of_string s) then
        mk_app "$int" s []
    else
        mk_app "$rat" s []

let sum a b = mk_app (etype a b) "$sum" [a; b]
let diff a b = mk_app (etype a b) "$difference" [a; b]
let uminus a = mk_app (get_type a) "$uminus" [a]
let mul a b = mk_app (etype a b) "$product" [a; b]
let minus_one e = mk_app (get_type e) "$difference" [e; const "1"]
let plus_one e = mk_app (get_type e) "$sum" [e; const "1"]

let eeq a b = mk_app "$o" "$eq_num" [a; b]
let less a b = mk_app "$o" "$less" [a; b]
let lesseq a b = mk_app "$o" "$lesseq" [a; b]
let greater a b = mk_app "$o" "$greater" [a; b]
let greatereq a b = mk_app "$o" "$greatereq" [a; b]

let rec find_coef x = function
    | [] -> raise Not_found
    | (c, y) :: r -> if equal x y then c else find_coef x r

let rec fadd_aux (c, x) = function
    | [] -> [(c, x)]
    | (c', y) :: r ->
            if equal x y then
                (Q.add c c', x) :: r
            else
                (c', y) :: (fadd_aux (c, x) r)

let fadd a b = List.fold_left (fun e c -> fadd_aux c e) a b
let fdiff a b = fadd a (List.map (fun (c, x) -> (Q.neg c, x)) b)
let fmul c a = List.map (fun (c', x) -> (Q.mul c c', x)) a

let rec sanitize = function
    | [] -> []
    | (c, _) as a :: r -> if Q.equal Q.zero c then (sanitize r) else a :: (sanitize r)

let normalize a b =
    let rec pop_const = function
        | [] -> (Q.zero, [])
        | (c, x) :: r ->
                if equal etrue x then
                    (Q.neg c), r
                else
                    let c', r' = pop_const r in
                    c', (c, x) :: r'
    in
    let coef e =
        if e = [] then
            Q.one
        else
            let k = Q.of_bigint (List.fold_left (fun k c -> if Q.is_real c then Z.lcm k (Q.den c) else k) Z.one e) in
            let aux = (fun g c -> Z.gcd g (Q.to_bigint (Q.mul c k))) in
            Q.div k (Q.of_bigint (List.fold_left aux (Q.to_bigint (Q.mul (List.hd e) k)) (List.tl e)))
    in
    let f = fdiff a b in
    let c, e = pop_const f in
    let e = sanitize e in
    let k = Q.abs (coef (List.map fst e)) in
    Q.mul c k, (List.map (fun (c, x) -> (Q.mul c k, x)) e)

let of_cexpr e = match e with
    | Eapp (s, [], _) when is_int e || is_rat e ->
            begin try
                Q.of_string s
            with Invalid_argument _ ->
                raise Exit
            end
    | _ -> raise NotaFormula

let rec of_nexpr = function
    | Eapp (v, [], _) as e ->
        begin try [of_cexpr e, etrue] with Exit -> [Q.one, e] end
    | Evar (v, _) as a when is_int a || is_rat a -> [Q.one, a]
    | Etau (_, ("$int"|"$rat"), _, _) as a -> [Q.one, a]
    | Eapp ("$uminus", [a], _) -> fdiff [Q.zero, etrue] (of_nexpr a)
    | Eapp ("$sum", [a; b], _) -> fadd (of_nexpr a) (of_nexpr b)
    | Eapp ("$difference", [a; b], _) -> fdiff (of_nexpr a) (of_nexpr b)
    | Eapp ("$product", [Eapp (_, [], _) as e; a], _)
    | Eapp ("$product", [a; Eapp (_, [], _) as e], _) ->
            begin try
                fmul (of_cexpr e) (of_nexpr a)
            with Exit ->
                raise NotaFormula
            end
    | _ -> raise NotaFormula

let of_bexpr = function
    | Eapp (("$less"|"$lesseq"|"$greater"|"$greatereq"|"$eq_num") as s, [a; b], _ ) ->
            let a', b' = of_nexpr a, of_nexpr b in
            let c, e = normalize a' b' in
            (e, s, c)
    | Eapp (("$is_int"|"$is_rat"|"$not_is_int"|"$not_is_rat") as s, [a], _) ->
            let a' = of_nexpr a in
            let c, e = normalize [Q.zero, etrue] a' in
            (e, s, c)
    | _ -> raise NotaFormula

let to_nexpr_aux (c, x) = if Q.equal Q.one c then x else mul (const (Q.to_string c)) x

let to_nexpr = function
    | [] -> const "0"
    | (c, x) :: r -> List.fold_left
        (fun e (c', x') -> if Q.sign c' < 0 then diff e (to_nexpr_aux (Q.neg c', x')) else sum e (to_nexpr_aux (c', x')))
                          (if Q.sign c < 0 then uminus (to_nexpr_aux (Q.neg c, x)) else to_nexpr_aux (c, x)) r

let to_bexpr (e, s, c) = mk_app "$o" s [to_nexpr e; const (Q.to_string c)]

let expr_norm e = try to_bexpr (of_bexpr e) with NotaFormula -> e

