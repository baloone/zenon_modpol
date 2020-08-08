(*  Copyright 2003 INRIA  *)
(*  $Id: modnorm.mli,v 1.00 2013-04_05 15:19:00 halmagrand Exp $  *)

open Expr;;
open Print;;



val normalize_fm : expr -> expr;;

val normalize_list : expr list -> expr list;;



val add_rwrt_term : string -> expr -> unit;;
val add_rwrt_prop : string -> expr -> unit;;

val used_rules: (bool option * expr * expr) list ref;;
