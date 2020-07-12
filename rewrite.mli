(*  Copyright 2003 INRIA  *)
(*  $Id: modnorm.mli,v 1.00 2013-04_05 15:19:00 halmagrand Exp $  *)

open Expr;;
open Print;;



val normalize_fm : expr -> expr;;

val normalize_list : expr list -> expr list;;



val add_rwrt_term : string -> expr -> unit;;
val add_rwrt_prop : string -> expr -> unit;;



type rule = (bool option) * expr * expr;;
type tbl = (string, rule) Hashtbl.t;;
type poltbl = (string, rule) Hashtbl.t;;

val tbl_term : ((string, expr * expr) Hashtbl.t) ref;;
val tbl_prop : ((string, bool * expr * expr) Hashtbl.t) ref;;
