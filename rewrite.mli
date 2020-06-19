(*  Copyright 2003 INRIA  *)
(*  $Id: modnorm.mli,v 1.00 2013-04_05 15:19:00 halmagrand Exp $  *)

open Expr;;
open Print;;



val normalize_fm : expr -> expr;;

val normalize_list : expr list -> expr list;;



val add_rwrt_term : string -> expr -> unit;;
val add_rwrt_prop : string -> expr -> unit;;

val select_rwrt_rules : Phrase.phrase list -> Phrase.phrase list;;


type rwrt_tbl = (string, expr * expr) Hashtbl.t;;
type rwrt_tbls = rwrt_tbl * rwrt_tbl;;

val tbl_term : rwrt_tbl ref;;
val tbl_prop : rwrt_tbl ref;;
