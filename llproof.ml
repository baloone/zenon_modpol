(*  Copyright 2004 INRIA  *)
Misc.version "$Id: llproof.ml,v 1.2 2004-04-08 22:51:45 doligez Exp $";;

open Expr;;

type binop =
  | And
  | Or
  | Imply
  | Equiv
  (* ... *)
;;

(*
  Format des regles:

  H1 ... Hn
  --------- regle
      C

  H1, ... Hn, C sont des listes de propositions

  Un noeud de preuve donne la conclusion (conc), la regle (rule), et
  les sous-noeuds (hyps = [hyp_1 ... hyp_n]).
  Le noeud est valide si conc contient tous les elements de C,
  et si, pour tout i, hyp_i est inclus dans conc + Hi

  informellement, une liste P1 ... Pn represente le sequent
       P1 ... Pn |- False
  ou encore la proposition  P1 -> ... -> Pn -> False

  Un arbre valide represente la preuve de la conclusion de sa racine.
*)

type rule =
  | Rfalse
    (*
       ----- Rfalse
       False
     *)
  | Rnottrue
    (*
       --------- Rnottrue
       Neg(True)
     *)
  | Raxiom of expr
    (*
       --------- Raxiom p
       p, Neg(p)
     *)

  | Rnoteq of expr
    (*
       --------------- Rnoteq t
       Neg(Equal(t,t))
     *)

  | Rnotnot of expr
    (*
            p
       ----------- Rnotnot p
       Neg(Neg(p))
     *)

  | Rconnect of binop * expr * expr
    (*
              p,q
       ---------------- Rconnect (And, p, q)
       Connect(And,p,q)

       p             q
       --------------- Rconnect (Or, p, q)
       Connect(Or,p,q)

       Neg(p)           q
       ------------------ Rconnect (Imply, p, q)
       Connect(Imply,p,q)

       p,q      Neg(p),Neg(q)
       ---------------------- Rconnect (Equiv, p, q)
         Connect(Equiv,p,q)
     *)

  | Rnotconnect of binop * expr * expr
    (*
       Neg(p)         Neg(q)
       --------------------- Rnotconnect (And, p, q)
       Neg(Connect(And,p,q))

          Neg(p),Neg(q)
       -------------------- Rnotconnect (Or, p, q)
       Neg(Connect(Or,p,q))

               p,Neg(q)
       ----------------------- Rnotconnect (Imply, p, q)
       Neg(Connect(Imply,p,q))

       p,Neg(q)       Neg(p),q
       ----------------------- Rnotconnect (Equiv, p, q)
       Neg(Connect(Equiv,p,q))
     *)

  | Rex of expr * string
    (*
             P{z}
       -------------------- Rex (Exists (x, ty, P{x}), z)
       Exists (x, ty, P{x})

       (z n'a pas d'autre occurrence dans l'hypothese)
     *)

  | Rall of expr * expr
    (*
           P{t}
       ----------------- Rall (All (x, ty, P{x}))
       All (x, ty, P{x})
     *)

  | Rnotex of expr * expr
    (*
              Neg(P{t})
       -------------------------- Rnotex (Exists (x, ty, P{x}))
       Neg (Exists (x, ty, P{x}))
     *)

  | Rnotall of expr * string
    (*
             Neg(P{z})
       ----------------------- Rnotall (All (x, ty, P{x}), z)
       Neg (All (x, ty, P{x}))

       (z n'a pas d'autre occurrence dans l'hypothese)
     *)

  | Rpnotp of expr * expr
    (* 
       Neg(Equal(t1,u1))   ...     Neg(Equal(tn,un))
       --------------------------------------------- RR
       Papply(P,[t1...tn]), Neg(Papply(P,[u1...un]))   

       RR = Rpnotp (Papply (P, [t1...tn]), Papply (P, [u1...un]))
     *)

  | Rnotequal of expr * expr
    (*
             Neg(Equal(t1,u1))  ...  Neg(Equal(tn,un))
       ---------------------------------------------------- RR
        Neg(Equal(Fapply(F,[t1...tn]),Fapply(F,[u1...un])))

       RR = Rnotequal (Fapply(F,[t1...tn]), Fapply(F,[u1...un]))
     *)

  | Requalnotequal of expr * expr * expr * expr
    (*
       Neg(Equal(t1,t3)),Neg(Equal(t2,t3))
                                      Neg(Equal(t2,t4)),Neg(Equal(t1,t4))
       ------------------------------------------------------------------ RR
                        Equal(t1,t2), Neg(Equal(t3,t4))

       RR = Requalnotequal (t1, t2, t3, t4)
     *)
  | Rlemma of string * string list
    (*
       ----------- Rlemma (name, args)
            C

       Si C est la conclusion de la preuve associee a "name" dans la
       liste de preuves.  Les arguments "args" correspondent aux
       parametres de "name".
     *)
  | Rdefinition
    (*
          H
         --- Rdefinition
          C
       Si H et C sont delta-beta convertibles avec les definitions
       donnees en argument au prouveur.
    *)
;;

type prooftree = {
  conc : expr list;
  rule : rule;
  hyps : prooftree list;
};;

type lemma = {
  name : string;                    (* nom du lemme *)
  params : (string * string) list;  (* parametres, avec leurs types *)
  proof : prooftree;                (* preuve *)
};;

type proof = lemma list;;
