
open Expr
open Node
open Mlproof
module LL = Llproof
module M = Map.Make(struct type t= Expr.t let compare = Expr.compare end)
module S = Simplex.Make(struct type t = Expr.t let compare = Expr.compare end)

open Arith

(* Expression/Types manipulation *)
let equal = Expr.equal

(* Nodes generated by the extension *)
let mk_node_const c e g = (* e is a trivially false comparison of constants *)
    Node {
        nconc = [e];
        nrule = Ext ("arith", "const", [const (Q.to_string c); e]);
        nprio = Prop;
        ngoal = g;
        nbranches = [| |];
    }

let mk_node_eq a b e g = (* e : a = b *)
    let a, b =
        try
            let expr, _, c = of_bexpr (lesseq a b) in
            to_nexpr expr, const (Q.to_string c)
        with NotaFormula -> a, b
    in
    Node {
        nconc = [e];
        nrule = Ext ("arith", "eq", [a; b; e]);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [expr_norm (lesseq a b); expr_norm (greatereq a b)] |];
    }

let mk_node_neq a b e g = (* e : a != b *)
    let a, b =
        try
            let expr, _, c = of_bexpr (lesseq a b) in
            to_nexpr expr, const (Q.to_string c)
        with NotaFormula -> a, b
    in
    Node {
        nconc = [e];
        nrule = Ext ("arith", "neq", [a; b; e]);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [expr_norm (less a b)]; [expr_norm (greater a b)] |];
    }

let mk_node_tighten s x c e g =
    Node {
        nconc = [e];
        nrule = Ext ("arith", "tighten_" ^ s, [x; const c; e]);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [mk_bop s x (const c)] |];
    }

let mk_node_var e1 e2 e g = (* e1 : v = expr, e2 : v {comp} const, e : expr {comp} const *)
    Node {
        nconc = [e];
        nrule = Ext ("arith", "var", [e1; e2; e]);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [e1; e2] |];
    }

let mk_node_neg s a e g = (* e : ~ {s} b *)
    Node {
        nconc = [e];
        nrule = Ext ("arith", "neg1_" ^ s, [a; e]);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [mk_ubop (comp_neg s) a] |];
    }

let mk_node_neg2 s a b e g = (* e : ~ a {s} b *)
    Node {
        nconc = [e];
        nrule = Ext ("arith", "neg2_" ^ s, [a; b; e]);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [mk_bop (comp_neg s) a b ] |];
    }

let mk_node_int_lt a b e g = (* e : a < b, => a <= b - 1 *)
    Node {
        nconc = [e];
        nrule = Ext ("arith", "int_lt", [a; b; e]);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [expr_norm (lesseq a (minus_one b))] |];
    }

let mk_node_int_gt a b e g = (* e : a > b, => a >= b + 1 *)
    Node {
        nconc = [e];
        nrule = Ext ("arith", "int_gt", [a; b; e]);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [expr_norm (greatereq a (plus_one b))] |];
    }

let mk_node_branch v e e' g =
    Node {
        nconc = [];
        nrule = Ext ("arith", "simplex_branch", [e; e']);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [e]; [e']; |];
    }

let mk_node_lin e l g =
    Node {
        nconc = l;
        nrule = Ext ("arith", "simplex_lin", e :: l);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [e] |];
    }

let mk_node_sim e b res g =
    Node {
        nconc = e :: b;
        nrule = Ext("arith", "simplex_bound", res :: e :: b);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [res] |];
    }

let mk_node_conflict e e' g =
    Node {
        nconc = [e; e'];
        nrule = Ext("arith", "conflict", [e; e']);
        nprio = Prop;
        ngoal = g;
        nbranches = [| |];
    }

let mk_node_fm x e e' f g =
    Node {
        nconc = [e; e'];
        nrule = Ext("arith", "FM", [x; e; e'; f]);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [f] |];
    }

let mk_node_inst e v g = match e with
  | Eall (e', t, p, _) ->
          let term = coerce t v in
          let n = Expr.substitute [(e', term)] p in
          Node {
              nconc = [e];
              nrule = Ext("arith", "All", [e; term]);
              nprio = Inst e;
              ngoal = g;
              nbranches = [| [n] |];
          }
  | Eex (e', t, p, _) ->
          let term = coerce t v in
          let n = Expr.substitute [(e', term)] (enot p) in
          let ne = enot e in
          Node {
              nconc = [ne];
              nrule = Ext("arith", "NotEx", [ne; term]);
              nprio = Inst e;
              ngoal = g;
              nbranches = [| [n] |];
          }
  | _ -> assert false

let mk_node_switch e a n =
    let new_branch k =
        let a' = eapp (tvar (newname ()) (get_type a), []) in
        let b = to_nexpr [(Q.of_int n), a'; (Q.of_int k), etrue] in
        [ Typetptp.mk_equal a b;
          Expr.substitute_expr (a, b) e]
    in
    let n = {
        nconc = [e];
        nrule = Ext("arith", "switch", [e; a; const (Q.to_string (Q.of_int n))]);
        nprio = Prop;
        ngoal = 0;
        nbranches = Array.init n new_branch;
    }
    in (fun g -> Node { n with ngoal = g})

(* Helper around the simplex module *)
type simplex_state = {
    core : S.t;
    ignore : expr list;
    bindings : (expr * expr * expr option * expr option) list;
}

let simplex_empty = {
    core = S.empty;
    ignore = [];
    bindings = [];
}

let simplex_copy s = {
    core = S.copy s.core;
    ignore = s.ignore;
    bindings = s.bindings;
}

let simplex_print b s =
    let fmt = Format.formatter_of_buffer b in
    let print_var fmt e = Format.fprintf fmt "%s" (Print.sexpr e) in
    Format.fprintf fmt "%a@." (S.print_debug print_var) s.core;
    Log.pp_list ~sep:"\n" (fun b (e, def, inf, upp) ->
        Printf.bprintf b "%a \t\t %a \t\t%a"
        (Log.pp_opt Print.pp_expr) inf
        (Log.pp_opt Print.pp_expr) upp
        Print.pp_expr def) b s.bindings

let bounds_of_comp s c = match s with
    | "$lesseq" -> (Q.minus_inf, c)
    | "$greatereq" -> (c, Q.inf)
    | _ -> (Q.minus_inf, Q.inf)

let low_binding c' c d' d f low high =
    if Q.gt (Q.div c' c) (Q.div d' d) then
        f, high
    else
        low, high

let high_binding c' c d' d f low high =
    if Q.lt (Q.div c' c) (Q.div d' d) then
        low, f
    else
        low, high

let new_bindings low high f = function
    | [c, x], "$lesseq", c' ->
            if Q.sign c <= -1 then begin match low with
                | None -> f, high
                | Some expr -> begin match (of_bexpr expr) with
                        | [d, y], "$greatereq", d' when Q.sign d >= 0 ->
                                low_binding c' c d' d f low high
                        | [d, y], "$lesseq", d' when Q.sign d <= -1 ->
                                low_binding c' c d' d f low high
                        | _ -> assert false
                        end
            end else begin match high with
                | None -> low, f
                | Some expr -> begin match (of_bexpr expr) with
                        | [d, y], "$lesseq", d' when Q.sign d >= 0 ->
                                high_binding c' c d' d f low high
                        | [d, y], "$greatereq", d' when Q.sign d <= -1 ->
                                high_binding c' c d' d f low high
                        | _ -> assert false
                        end
            end
    | [c, x], "$greatereq", c' ->
            if Q.sign c >= 0 then begin match low with
                | None -> f, high
                | Some expr -> begin match (of_bexpr expr) with
                        | [d, y], "$greatereq", d' when Q.sign d >= 0 ->
                                low_binding c' c d' d f low high
                        | [d, y], "$lesseq", d' when Q.sign d <= -1 ->
                                low_binding c' c d' d f low high
                        | _ -> assert false
                        end
            end else begin match high with
                | None -> low, f
                | Some expr -> begin match (of_bexpr expr) with
                        | [d, y], "$lesseq", d' when Q.sign d >= 0 ->
                                high_binding c' c d' d f low high
                        | [d, y], "$greatereq", d' when Q.sign d <= -1 ->
                                high_binding c' c d' d f low high
                        | _ -> assert false
                        end
            end
    | _ -> low, high

let translate_bound e r = match e with
    | None -> r ()
    | Some e -> begin match (of_bexpr e) with
        | [c, x], _, c' -> Q.div c' c
        | _ -> assert false
    end

let pop_option = function | Some a -> a | None -> assert false

let bound_of_expr is_high e bounds =
    if e <> [] && (List.for_all (fun (c,_) -> Q.equal Q.zero c) e) then
        [], Q.zero
    else begin
        assert (not (List.exists (fun (c,_) -> Q.equal Q.zero c) e));
        let xor a b = (a && not b) || (not a && b) in
        let rec aux = function
            | [] -> raise Exit
            | [c, x] ->
                    let v, _, einf, eupp = List.find (fun (y, _, _, _) -> equal x y) bounds in
                    if xor is_high (Q.sign c >= 0) then begin
                        [pop_option einf], Q.mul c (translate_bound einf (fun () -> raise Exit))
                    end else begin
                        [pop_option eupp], Q.mul c (translate_bound eupp (fun () -> raise Exit))
                    end
            | (c, x) :: r ->
                    let l, b = aux r in
                    let _, _, einf, eupp = List.find (fun (y, _, _, _) -> equal x y) bounds in
                    if xor is_high (Q.sign c >= 0) then
                        (pop_option einf) :: l, Q.add b (Q.mul c (translate_bound einf (fun () -> raise Exit)))
                    else
                        (pop_option eupp) :: l, Q.add b (Q.mul c (translate_bound eupp (fun () -> raise Exit)))
        in
        try aux e with Exit -> [], if is_high then Q.inf else Q.minus_inf
    end


let bounds_of_clin v expr bounds =
    let _, _, einf, eupp = List.find (fun (y, _, _, _) -> equal y v) bounds in
    let inf = translate_bound einf (fun () -> Q.minus_inf) in
    let upp = translate_bound eupp (fun () -> Q.inf) in
    let l_bounds, low = bound_of_expr false expr bounds in
    let h_bounds, high = bound_of_expr true expr bounds in
    if Q.gt low upp then
        l_bounds, greatereq v (const (Q.to_string low)), pop_option eupp
    else if Q.lt high inf then
        h_bounds, lesseq v (const (Q.to_string high)), pop_option einf
    else if Q.gt inf upp then
        [], pop_option einf, pop_option eupp
    else
        assert false

let add_binding t x f (e, s, c) =
    let l1, l2 = List.partition (fun (y, _, _, _) -> equal x y) t.bindings in
    let _, def, low, high =
        if List.length l1 = 0 then begin x, x, None, None end
        else if List.length l1 = 1 then begin List.hd l1 end
        else assert false in
    let low, high = new_bindings low high (Some f) (e, s, c) in
    { t with bindings = (x, def, low, high) :: l2 }

let simplex_add t f (e, s, c) =
    match e with
    | []  -> assert false
    | [(c', x)] ->
            let b = Q.div c (Q.abs c') in
            let (inf, upp) = bounds_of_comp s b in
            let (inf, upp) = if Q.sign c' <= -1 then (Q.neg upp, Q.neg inf) else (inf, upp) in
            Log.debug 7 "arith -- new bounds : %s <= %a <= %s" (Q.to_string inf) Print.pp_expr x (Q.to_string upp);
            (add_binding {t with core = S.add_bounds t.core (x, inf, upp)} x f (e, s, c)), []
    | _ ->
            let expr = to_nexpr e in
            let v = tvar (newname ()) (get_type expr) in
            let e1 = Typetptp.mk_equal v expr in
            let e2 = mk_bop s v (const (Q.to_string c)) in
            Log.debug 7 "arith -- new variable : %a == %a" Print.pp_expr v Print.pp_expr expr;
            { core = S.add_eq t.core (v, e);
              ignore = e1 :: t.ignore;
              bindings = (v, e1, None, None) :: t.bindings;
            }, [f, mk_node_var e2 e1 f] (* The order (e2 before e1) is actually VERY important here !! *)

exception Internal_error
let nodes_of_tree s f t =
    let rec aux s f t = match !t with
    | None -> raise Internal_error
    | Some S.Branch (v, k, c, c') ->
            Log.debug 7 "arith -- branching: %a <= %s" Print.pp_expr v (Z.to_string k);
            let k = const (Z.to_string k) in
            let under = expr_norm (lesseq v k) in
            let above = expr_norm (greatereq v (plus_one k)) in
            (f, mk_node_branch v under above) :: (
                (aux (add_binding s v under (of_bexpr under)) under c) @
                (aux (add_binding s v above (of_bexpr above)) above c'))
    | Some S.Explanation (v, expr) ->
            let is_zero = expr <> [] && List.for_all (fun (c, _) -> Q.equal Q.zero c) expr in
            let expr = if is_zero then expr else sanitize expr in
            Log.debug 7 "arith -- simplex: %a = %a" Print.pp_expr v Print.pp_expr (to_nexpr expr);
            let l = v :: (List.map snd expr) in
            let relevant = List.map (fun (_, z, _, _) -> z)
                (List.filter (fun (y, y', _, _) -> not (equal y y') && List.exists (fun x -> equal x y) l) s.bindings) in
            let clin = expr_norm (Typetptp.mk_equal (to_nexpr expr) v) in
            let bounds, nb, conflict = bounds_of_clin v expr s.bindings in
            if bounds = [] && not is_zero then
                [f, mk_node_conflict nb conflict]
            else
                [f, mk_node_lin clin relevant;
                 clin, mk_node_sim clin bounds nb;
                 nb, mk_node_conflict nb conflict]
    in
    aux s f t

let simplex_solve s e =
    let f = S.nsolve_incr s.core is_int in
    match f () with
    | None -> false, [] (* TODO: rerun f, or try other method ? *)
    | Some S.Solution _ -> false, []
    | Some S.Unsatisfiable cert ->
            Log.debug 5 "arith -- found unsat explanation.";
            Log.debug 10 "arith -- Simplex state :\n%a" simplex_print s;
            true, nodes_of_tree s e cert

(* Instanciation ordering (and substituting) *)

let subst_of_inst n = match (n 0) with
    | Node n -> begin match n.nrule with
        | Ext("arith", "All", [Eall(_) as e; v]) -> (e, v)
        | Ext("arith", "NotEx", [Enot(Eex(_) as e, _); v]) -> (e, v)
        | _ -> assert false
        end
    | Stop -> assert false

let subst_inst_rule subst = function
    | Ext("arith", "All", [e; v]) ->
            Ext("arith", "All", [substitute_meta subst e; v])
    | Ext("arith", "NotEx", [e; v]) ->
            Ext("arith", "NotEx", [substitute_meta subst e; v])
    | _ -> assert false

let subst_inst_aux subst n i =
    match n 0 with
    | Node n -> Node { n with
        nconc = List.map (substitute_meta subst) n.nconc;
        nrule = subst_inst_rule subst n.nrule;
        ngoal = i;
        nbranches = Array.map (List.map (substitute_meta subst)) n.nbranches;
        }
    | Stop -> assert false

let subst_inst (e, n) (e', n') =
    let meta, v = subst_of_inst n in
    let subst = meta, v in
    let e''= substitute_meta subst e' in
    (e'', subst_inst_aux subst n')

let order_inst l =
    let l = List.sort (fun (e, _) (e', _) -> Pervasives.compare (Expr.size e) (Expr.size e')) l in
    let l = List.fold_left (fun acc x -> x :: (List.map (subst_inst x) acc)) [] l in
    l

(* Internal state *)
type state = {
    mutable global : ((int -> Node.node_item) list) M.t;
    mutable solved : bool;
    stack : (expr * simplex_state * ((expr * (int -> Node.node_item)) list)) Stack.t;
}

let empty_state = {
    global = M.empty;
    solved = false;
    stack = Stack.create ();
}

let st_solved st = st.solved <- true

let st_pop st =
    ignore (Stack.pop st.stack);
    Log.debug 7 "arith -- state stack pop (%i left)" (Stack.length st.stack);
    st.solved <- false

let st_head st =
    try
        let _, r, _ = Stack.top st.stack in
        simplex_copy r
    with Stack.Empty -> simplex_empty

let st_push st x =
    Stack.push x st.stack;
    Log.debug 7 "arith -- state stack push (%i left)" (Stack.length st.stack)

let st_is_head st e =
    try
        let e', _, _ = Stack.top st.stack in
        equal e e'
    with Stack.Empty -> false

(* Internal state management *)
exception Found of (int -> node_item)

let is_coherent e = function
    | Stop -> true
    | Node n -> List.for_all (fun e' -> equal e e' || Index.member e') n.nconc

let ignore_expr, add_expr, remove_expr, todo, add_todo, set_global =
    let st = empty_state in
    let is_new e =
        try Stack.iter (fun (e', _, l) ->
            if (List.exists (fun (e', _) -> equal e e') l) then raise Exit) st.stack;
        true
        with Exit -> false

    and ignore_expr e =
        try
            Stack.iter (fun (_, t, l) ->
                if List.exists (equal e) t.ignore then raise Exit;
                if List.exists (fun (y, _) -> equal e y) l then raise Exit)
            st.stack;
            false
        with Exit -> true
    in

    let add e = (* try and compute a solution *)
        if is_new e && not st.solved && not (ignore_expr e) then begin
            try
                let (f, s, c) = of_bexpr e in
                if not (fis_tau f) then raise NotaFormula;
                let t = st_head st in
                if f <> [] then begin
                    let t', res = simplex_add t e (f, s, c) in
                    let b, res' = simplex_solve t' e in
                    let res'' = res @ res' in
                    st_push st (e, t', res'');
                    if b then st_solved st
                end
            with NotaFormula -> ()
        end
    in

    let rec remove e = if st_is_head st e then begin st_pop st; remove e end in

    let add_todo e n = st_push st (e, (st_head st), List.map (fun m -> e, m) n)

    and todo e g =
        let res = ref [] in
        let aux (e', n) = if equal e e' then res := (n g) :: !res in
        M.iter (fun x l -> List.iter (fun n -> aux (x, n)) l) st.global;
        begin match !res with
        | [] -> Stack.iter (fun (_,_,l) -> List.iter aux l) st.stack
        | l -> res := List.rev !res
        end;
        List.filter (is_coherent e) !res

    and set_global l =
        let res = ref false in
        let f (e, l) =
            try
                let l' = M.find e st.global in
                if (List.map (fun n -> n 0) l) <> (List.map (fun n -> n 0) l') then begin
                    res := true;
                    Log.debug 9 "arith -- Got %i match for %a (previously : %i)"
                    (List.length l) Print.pp_expr e (List.length l');
                    st.global <- M.add e l st.global
                end
            with Not_found ->
                res := true;
                Log.debug 9 "arith -- Got %i match for %a (previously : 0)"
                (List.length l) Print.pp_expr e;
                st.global <- M.add e l st.global
        in
        List.iter f l;
        !res
    in
    ignore_expr, add, remove, todo, add_todo, set_global

(* Fourier-Motzkin *)
type fm_state = (Expr.t list * Expr.t list) M.t

let fm_empty = M.empty

let fm_get st x = try M.find x st with Not_found -> [], []

let fm_lower s c = match s with
    | "$less" | "$lesseq" -> Q.sign c < 0
    | "$greater" | "$greatereq" -> Q.sign c > 0
    | _ -> assert false

let fm_deduce_aux x e f =
    let (be, se, ce) = of_bexpr e in
    let (bf, sf, cf) = of_bexpr f in
    let cex = find_coef x be in
    let cfx = find_coef x bf in
    match se, sf with
    | "$less", "$less" | "$lesseq", "$less" | "$less", "$lesseq" ->
            assert (Q.sign cex < 0 && Q.sign cfx > 0);
            let t = fdiff
                (fmul cfx (fdiff be [(cex, x);(ce, etrue)]))
                (fmul cex (fdiff bf [(cfx, x);(cf, etrue)])) in
            let b, a = normalize t [Q.zero, etrue] in
            let g = expr_norm (to_bexpr (a, "$less", b)) in
            [mk_node_fm x e f g]
    | "$greater", "$greater" | "$greatereq", "$greater" | "$greater", "$greatereq" ->
            assert (Q.sign cex > 0 && Q.sign cfx < 0);
            let t = fdiff
                (fmul cfx (fdiff be [cex, x; ce, etrue]))
                (fmul cfx (fdiff be [cex, x; ce, etrue])) in
            let b, a = normalize t [Q.zero, etrue] in
            let g = expr_norm (to_bexpr (a, "$less", b)) in
            [mk_node_fm x e f g]
    | "less", "$greater" | "$lesseq", "$greater" | "$less", "$greatereq" ->
            assert (Q.sign cex < 0 && Q.sign cfx < 0);
            let t = fadd
                (fmul cfx (fdiff [cex, x; ce, etrue] be))
                (fmul cex (fdiff [cfx, x; cf, etrue] bf)) in
            let b, a = normalize t [Q.zero, etrue] in
            let g = expr_norm (to_bexpr (a, "$less", b)) in
            [mk_node_fm x e f g]
    | "$greater", "$less" | "$greatereq", "$less" | "$greater", "$lesseq" ->
            assert (Q.sign cex > 0 && Q.sign cfx > 0);
            let t = fdiff
                (fmul cfx (fdiff [cex, x; ce, etrue] be))
                (fmul cex (fdiff [cfx, x; cf, etrue] bf)) in
            let b, a = normalize t [Q.zero, etrue] in
            let g = expr_norm (to_bexpr (a, "$less", b)) in
            [mk_node_fm x e f g]
    | _ ->
            []


let fm_deduce1 x e l = List.concat (List.map (fm_deduce_aux x e) l)
let fm_deduce2 x e l = List.concat (List.map (fun e' -> fm_deduce_aux x e' e) l)

let fm_add_aux st (s, c, x) e =
    if fm_lower s c then begin
        let low, high = fm_get st x in
        let res = fm_deduce1 x e high in
        M.add x (e :: low, high) st, res
    end else begin
        let low, high = fm_get st x in
        let res = fm_deduce2 x e low in
        M.add x (low, e :: high) st, res
    end

let fm_add st e =
    let (b, s, _) = of_bexpr e in
    let aux (acc, l) (c, x) =
        if is_rat x then
            let st', l' = fm_add_aux st (s, c, x) e in
            (st', (l @ l'))
        else
            (acc, l)
    in
    List.fold_left aux (st, []) b

let fm_add_expr, fm_rm_expr =
    let st = ref fm_empty in
    let add e = match e with
        | Eapp (Evar(("$less"|"$lesseq"|"$greater"|"$greatereq"),_), [a; b], _) when is_rat a || is_rat b ->
                begin try
                    let st', res = fm_add !st e in
                    if res <> [] then add_todo e res;
                    st := st'
                with NotaFormula -> () end
        | _ -> ()
    in
    let rm e =
        st := M.map (fun (l, l') ->
            List.filter (fun e'' -> not (equal e e'')) l,
            List.filter (fun e'' -> not (equal e e'')) l') !st
    in
    add, rm

(* ML -> LL translation *)
let ssub s j = try String.sub s 0 j with Invalid_argument _ -> ""
let esub s j = try String.sub s j (String.length s - j) with Invalid_argument _ -> ""

let tr_rule f = function
    | Ext("arith", "const", [c; e]) ->
            LL.Rextension ("arith", "const", [f c], [f e], [[]])
    | Ext("arith", "eq", [a; b; e]) ->
            LL.Rextension("arith", "eq", [f a; f b], [f e], [[f (expr_norm (lesseq a b)); f (expr_norm (greatereq a b))]])
    | Ext("arith", "neq", [a; b; e]) ->
            LL.Rextension("arith", "neq", [f a; f b], [f e], [[f (expr_norm (less a b))];[f (expr_norm (greater a b))]])
    | Ext("arith", s, [x; c; e]) when ssub s 8 = "tighten_" ->
            LL.Rextension("arith", s, [f x; f c], [f e], [[f (mk_bop (esub s 8) x c)]])
    | Ext("arith", "var", [e1;e2;e]) ->
            LL.Rextension("arith", "var", [f e1;f e2], [f e], [[f e1;f e2]])
    | Ext("arith", s, [a; e]) when ssub s 5 = "neg1_" ->
            LL.Rextension("arith", s, [f a], [f e], [[f (mk_ubop (comp_neg (esub s 5)) a)]])
    | Ext("arith", s, [a; b; e]) when ssub s 5 = "neg2_" ->
            LL.Rextension("arith", s, [f a;f b], [f e], [[f (mk_bop (comp_neg (esub s 5)) a b)]])
    | Ext("arith", "int_lt", [a; b; e]) ->
            LL.Rextension("arith", "int_lt", [f a;f b], [f e], [[f (expr_norm (lesseq a (minus_one b)))]])
    | Ext("arith", "int_gt", [a; b; e]) ->
            LL.Rextension("arith", "int_gt", [f a;f b], [f e], [[f (expr_norm (greatereq a (plus_one b)))]])
    | Ext("arith", "simplex_branch", [e;e']) ->
            LL.Rextension("arith", "simplex_branch", [f e;f e'], [], [[f e];[f e']])
    | Ext("arith", "simplex_lin", e :: l) ->
            LL.Rextension("arith", "simplex_lin", List.map f (e :: l), List.map f l, [[f e]])
    | Ext("arith", "simplex_bound", res :: e :: b) ->
            LL.Rextension("arith", "simplex_bound", List.map f (e :: b), List.map f (e :: b), [[f res]])
    | Ext("arith", "conflict", [e;e']) ->
            LL.Rextension("arith", "conflict", [f e;f e'], [f e;f e'], [[]])
    | Ext("arith", "FM", [x;e;e';e'']) ->
            LL.Rextension("arith", "FM", [f x;f e;f e';f e''], [f e;f e'], [[f e'']])
    | Ext("arith", "All", [p; t]) ->
            LL.Rall (f p, f t)
    | Ext("arith", "NotEx", [Enot(p, _); t]) ->
            LL.Rnotex (f p, f t)
    | Ext("arith", s, _) ->
            Log.debug 0 "arith -- Unknow rule : '%s'" s;
            raise Exit
    | _ -> assert false

(* TODO: add nodes for expr normalization ? *)
let mltoll f p hyps =
    let subproofs, subextras = List.split (Array.to_list hyps) in
    let extras = Expr.diff (List.concat subextras) p.mlconc in
    let nn = {
        LL.conc = List.map f (extras @ p.mlconc);
        LL.rule = tr_rule f p.mlrule;
        LL.hyps = subproofs;
    } in
    (nn, extras)


(* LL -> Coq translation *)
let get_bind = function
    | Eapp(Evar("=", _), [Evar(s, _) as s'; e], _) -> s, is_int s', e
    | _ -> assert false

let get_branch = function
    | Eapp(Evar("$lesseq", _), [e; Evar(c, _)], _) -> e, c
    | _ -> assert false

let neg_comp_lemma = function
    | "$less" -> "lt"
    | "$lesseq" -> "leq"
    | "$greater" -> "gt"
    | "$greatereq" -> "geq"
    | _ -> assert false

let ll_p oc r =
    let pr fmt = Printf.fprintf oc fmt in
    match r with
    | LL.Rextension("arith", s, args, l, ll) ->
            pr "(* ARITH -- '%s' : " s;
            List.iter (fun e -> pr "%a : '%s', " Lltocoq.p_expr e
                (match Expr.get_type e with None -> "" | Some t -> Type.to_string t)) args;
            pr "\n * ->";
            List.iter (fun e -> pr "%a, " Lltocoq.p_expr e) l;
            List.iter (fun l ->
                pr "\n * |- ";
                List.iter (fun e -> pr "%a, " Lltocoq.p_expr e) l;
                ) ll;
            pr "*)\n"
    | _ -> assert false

let lltocoq oc r =
    let pr fmt = Printf.fprintf oc fmt in
    if Log.get_debug () >= 0 then ll_p oc r;
    match r with
    | LL.Rextension("arith", "const", _, [e], _) ->
            pr "arith_simpl %s.\n" (Coqterm.getname e)
    | LL.Rextension("arith", "eq", [a; b], [e], [[less; greater]]) ->
            pr "apply (arith_refut _ _ (arith_eq %a %a)); [ intros (%s, %s) | arith_simpl %s ].\n"
            Lltocoq.pp_expr (coqify_to_q a) Lltocoq.pp_expr (coqify_to_q b) (Coqterm.getname less) (Coqterm.getname greater) (Coqterm.getname e)
    | LL.Rextension("arith", "neq", [a; b], [e], [[less]; [greater]]) ->
            pr "apply (arith_refut _ _ (arith_neq %a %a)); [ intros [ %s | %s ] | arith_simpl %s ].\n"
            Lltocoq.pp_expr (coqify_to_q a) Lltocoq.pp_expr (coqify_to_q b) (Coqterm.getname less) (Coqterm.getname greater) (Coqterm.getname e)
    | LL.Rextension("arith", "tighten_$lesseq", [x; c], [e], [[e']]) ->
            pr "pose proof (arith_tight_leq _ _ %s) as %s; unfold Qfloor, Zdiv in %s; simpl in %s.\n"
            (Coqterm.getname e) (Coqterm.getname e') (Coqterm.getname e') (Coqterm.getname e')
    | LL.Rextension("arith", "tighten_$greatereq", [x; c], [e], [[e']]) ->
            pr "pose proof (arith_tight_geq _ _ %s) as %s; unfold Qceiling, Zdiv in %s; simpl in %s.\n"
            (Coqterm.getname e) (Coqterm.getname e') (Coqterm.getname e') (Coqterm.getname e')
    | LL.Rextension("arith", s, [a; b], [e], [[f]]) when ssub s 5 = "neg2_" ->
            pr "apply (arith_refut _ _ (arith_neg_%s %a %a)); [zenon_intro %s | arith_simpl %s].\n"
            (neg_comp_lemma (esub s 5)) Lltocoq.pp_expr (coqify_to_q a) Lltocoq.pp_expr (coqify_to_q b) (Coqterm.getname f) (Coqterm.getname e)
    | LL.Rextension("arith", "int_lt", [a; b], [e], [[f]]) ->
            pr "cut %a; [ zenon_intro %s | arith_simpl %s ].\n" Lltocoq.p_expr f (Coqterm.getname f) (Coqterm.getname e)
    | LL.Rextension("arith", "int_gt", [a; b], [e], [[f]]) ->
            pr "cut %a; [ zenon_intro %s | arith_simpl %s ].\n" Lltocoq.p_expr f (Coqterm.getname f) (Coqterm.getname e)
    | LL.Rextension("arith", "var", _, [e], [[e1; e2]]) ->
            let v, b, expr = get_bind e2 in
            pr "pose (%s := %a).\n" v Lltocoq.pp_expr (coqify_term expr);
            pr "  pose proof (%s %s) as %s; change %s with %a in %s at 2.\n"
                (if b then "Z.eq_refl" else "Qeq_refl")
                v (Coqterm.getname e2) v Lltocoq.pp_expr (coqify_term expr) (Coqterm.getname e2);
            pr "  cut %a; [zenon_intro %s | subst %s; arith_simpl %s ].\n" Lltocoq.p_expr e1 (Coqterm.getname e1) v (Coqterm.getname e)
    | LL.Rextension("arith", "simplex_branch", _, _, [[e]; [f]]) ->
            let expr, c = get_branch e in
            pr "destruct (arith_branch %a %s) as [ %s | %s ]; [ | simpl in %s ].\n"
            Lltocoq.pp_expr (coqify_term expr) c (Coqterm.getname e) (Coqterm.getname f) (Coqterm.getname f)
    | LL.Rextension("arith", "simplex_lin", _, l, [[e]]) ->
            pr "cut %a; [ zenon_intro %s | %aarith_unfold; omega ].\n" Lltocoq.p_expr e (Coqterm.getname e)
            (fun oc -> List.iter (fun e -> let s, _, _ = get_bind e in Printf.fprintf oc "subst %s; " s)) l
    | LL.Rextension("arith", "simplex_bound", _, l, [[e]]) ->
            pr "cut %a; [ zenon_intro %s | %aarith_unfold; omega ].\n" Lltocoq.p_expr e (Coqterm.getname e)
            (fun oc -> List.iter (fun e -> Printf.fprintf oc "arith_unfold_in %s; " (Coqterm.getname e))) l
    | LL.Rextension("arith", "conflict", [e; e'], _, _) ->
            pr "arith_trans_simpl %s %s.\n" (Coqterm.getname e) (Coqterm.getname e')
    | LL.Rextension("arith", "FM", x :: _, [e; e'], [[f]]) ->
            pr "cut %a; [ zenon_intro %s | arith_trans %s %s Arith_tmp; arith_simpl Arith_tmp ].\n"
            Lltocoq.p_expr f (Coqterm.getname f) (Coqterm.getname e) (Coqterm.getname e')
    | LL.Rextension("arith", s, _, _, _) ->
            pr "(* TODO unknown rule %s *)\n" s
    | _ -> pr "(* Don't know what to do *)"

(* Constants *)
let const_node e = (* comparison of constants *)
    let (f, s, c) = of_bexpr e in
    assert (f = []);
    begin match s with
    | "$less" when Q.geq Q.zero c -> add_todo e [mk_node_const c e]
    | "$lesseq" when Q.gt Q.zero c -> add_todo e [mk_node_const c e]
    | "$greater" when Q.leq Q.zero c -> add_todo e [mk_node_const c e]
    | "$greatereq" when Q.lt Q.zero c -> add_todo e [mk_node_const c e]
    | "=" when not (Q.equal Q.zero c) -> add_todo e [mk_node_const c e]
    | "$is_int" when not (is_z c) -> add_todo e [mk_node_const c e]
    | "$not_is_int" when is_z c -> add_todo e [mk_node_const c e]
    | "$not_is_rat" -> add_todo e [mk_node_const c e]
    | _ -> ()
    end

let is_const e = try let (f, _, _) = of_bexpr e in f = [] with NotaFormula -> false

(* Extension functions *)
let add_formula e =
    fm_add_expr e;
    match e with
    | _ when ignore_expr e -> ()
    | Enot (Eapp (Evar("=",_), [a; b], _), _) when is_num a && is_num b ->
            add_todo e [mk_node_neq a b e]
    | Enot (Eapp (Evar(("$less"|"$lesseq"|"$greater"|"$greatereq") as s,_), [a; b], _), _) ->
            add_todo e [mk_node_neg2 s a b e]
    | Enot (Eapp (Evar(("$is_int"|"$is_rat") as s,_), [a], _), _) ->
            add_todo e [mk_node_neg s a e]
    | _ when is_const e ->
            const_node e
    | Eapp (Evar("=",_), [a; b], _) when is_num a && is_num b ->
            add_todo e [mk_node_eq a b e]
    | Eapp (Evar("$less",_), [a; b], _) when is_int a && is_int b ->
            add_todo e [mk_node_int_lt a b e]
    | Eapp (Evar("$greater",_), [a; b], _) when is_int a && is_int b ->
            add_todo e [mk_node_int_gt a b e]
    | _ -> begin try
            begin match (of_bexpr e) with
            | [(c', x)], ("$less"|"$lesseq"), c when is_int x && is_q (Q.div c c') ->
                    let c'' = Q.div c c' in
                    if Q.sign c' <= -1 then
                        add_todo e [mk_node_tighten "$greatereq" x (Q.to_string (ceil c'')) e]
                    else
                        add_todo e [mk_node_tighten "$lesseq" x (Q.to_string (floor c'')) e]
            | [(c', x)], ("$greater"|"$greatereq"), c when is_int x && is_q (Q.div c c') ->
                    let c'' = Q.div c c' in
                    if Q.sign c' <= -1 then
                        add_todo e [mk_node_tighten "$lesseq" x (Q.to_string (floor c'')) e]
                    else
                        add_todo e [mk_node_tighten "$greatereq" x (Q.to_string (ceil c'')) e]
            | _ -> add_expr e
            end with
            | NotaFormula -> ()
    end

let remove_formula e =
    remove_expr e;
    fm_rm_expr e

let rec iter_open p =
    match ct_from_ml p with
    | None ->
            Log.debug 5 "arith -- no choice left";
            false
    | Some t ->
        begin match solve_tree t with
        | Unsat -> begin try
            Log.debug 5 "arith -- switching to next instanciation ";
            iter_open (next_inst p)
            with EndReached -> false end
        | Abstract s ->
                Log.debug 5 "arith -- found a solution.";
                List.iter (fun (x, v) -> Log.debug 6 "arith -- %a <- %a" Print.pp_expr x Print.pp_expr v) s;
                let global = List.fold_left (fun acc (e, v) -> match e with
                    | Emeta(Eall(_) as e', _) ->
                            (e', mk_node_inst e' v) :: acc
                    | Emeta(Eex(_) as e', _) ->
                            (enot e', mk_node_inst e' v) :: acc
                    | _ -> assert false) [] s in
                set_global (List.map (fun (e, x) -> e, [x]) (order_inst global))
        | Case (e, a, n) ->
                try
                    set_global [e, [mk_node_switch e a (Z.to_int n); (fun _ -> Stop)]]
                with Z.Overflow ->
                    assert false
        end

let newnodes e g _ =
    let res = todo e g in
    res

let make_inst term g = assert false

let to_llproof = mltoll

let declare_context_coq oc =
    let pr fmt = Printf.fprintf oc fmt in
    pr "Require Import ZArith.\n";
    pr "Require Import Omega.\n";
    pr "Require Import QArith.\n";
    pr "Require Import zenon_arith.\n";
    List.iter (fun (s, t) ->
        pr "Parameter %s : %s.\n" s (Type.to_string t))
        (Typetptp.get_defined ());
    ()

let p_rule_coq = lltocoq

let predef () =
    [ "$less"; "$lesseq"; "$greater"; "$greatereq";
      "$sum"; "$difference"; "$product"; "$uminus";
      "$is_int"; "$not_is_int"; "$is_rat"; "$not_is_rat";
    ] @ (List.map fst (Typetptp.get_defined ()))
;;

Extension.register {
  Extension.name = "arith";
  Extension.newnodes = newnodes;
  Extension.make_inst = make_inst;
  Extension.add_formula = add_formula;
  Extension.remove_formula = remove_formula;
  Extension.iter_open = iter_open;
  Extension.preprocess = (fun x -> x);
  Extension.add_phrase = (fun _ -> ());
  Extension.postprocess = (fun x -> x);
  Extension.to_llproof = to_llproof;
  Extension.declare_context_coq = declare_context_coq;
  Extension.p_rule_coq = p_rule_coq;
  Extension.predef = predef;
};;

