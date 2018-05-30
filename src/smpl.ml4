(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmp" i*)
(* Written for LVC by Sigurd Schneider (2016-2017) *)

open Util
open Names
open Ltac_plugin
open Tacexpr
open Misctypes
open Tacintern
open Tacinterp
open Libobject
open Stdarg
open Extraargs
open Pp
open Tacarg
open Genarg
open Ltac_plugin
open Pcoq.Prim
open Taccoerce

DECLARE PLUGIN "smpl_plugin"

module StringMap = Map.Make(String)

type smpl_db_entry = {
  priority : int;
  tactic : Tacexpr.glob_tactic_expr;
  require_progress : bool option
}

type smpl_db = {
  queue : smpl_db_entry list;
  progress_default : bool
}

let smpl_dbs = ref (StringMap.empty : smpl_db StringMap.t)

(*** Summary ***)

let init    () = smpl_dbs := StringMap.empty
let freeze   _ = !smpl_dbs
let unfreeze t = smpl_dbs := t

let _ = Summary.declare_summary "smpl"
	{ Summary.freeze_function   = freeze;
	  Summary.unfreeze_function = unfreeze;
	  Summary.init_function     = init }

(*** Database actions ***)

let intern_smpl_create name db =
 try let _ = StringMap.find name (!smpl_dbs) in
     CErrors.user_err (~hdr:"Smpl") (str "Smpl Database " ++ str name ++ str " already exists.")
 with Not_found -> smpl_dbs := StringMap.add name db (!smpl_dbs)

let rec insert e l =
  match l with
  | e'::l ->
     if e.priority < e'.priority then
       e::e'::l
     else
       e'::insert e l
  | [] -> [e]

let intern_smpl_add entry name =
  try let db = StringMap.find name (!smpl_dbs) in
      let db' = { db with queue = insert entry db.queue } in
      smpl_dbs := StringMap.add name db' (!smpl_dbs)
  with Not_found -> CErrors.user_err (~hdr:"Smpl") (str "Unknown Smpl Database " ++ str name ++ str ".")

type smpl_action =
  | CreateDb of string * smpl_db
  | AddTac of string * smpl_db_entry

(*** Library interface ***)
(* This code handles loading through Require (Import) *)

let load_smpl_action _ (_, act) =
  match act with
  | CreateDb (db_name, db) ->
     intern_smpl_create db_name db
  | AddTac (db_name, entry) -> intern_smpl_add entry db_name

let cache_smpl_action (kn, act) =
  load_smpl_action 1 (kn, act)

let subst_smpl_db_entry subst entry =
  let tac' = Tacsubst.subst_tactic subst entry.tactic in
  if tac'==entry.tactic then entry else {entry with tactic = tac'}

let subst_smpl_db subst db =
  { db with queue = List.map (subst_smpl_db_entry subst) db.queue}

let subst_smpl_action (subst,act) =
  match act with
  | CreateDb (db_name, db) ->
     CreateDb (db_name, subst_smpl_db subst db)
  | AddTac (db, entry) ->
     AddTac (db, subst_smpl_db_entry subst entry)

let classify_smpl_action act = Substitute act

let inSmpl : smpl_action -> obj =
  declare_object {(default_object "SMPL") with
                   cache_function = cache_smpl_action;
		   load_function = load_smpl_action;
		   subst_function = subst_smpl_action;
		   classify_function = classify_smpl_action; }

(*** Interface ***)

let smpl_add n_opt tac req_progress_opt db_name =
  let n = match n_opt with
    | Some n -> n
    | None -> 100 in
  let act = AddTac (db_name, {priority = n; tactic = tac; require_progress = req_progress_opt }) in
  Lib.add_anonymous_leaf (inSmpl act)

let smpl_create db_name db =
  let act = CreateDb (db_name, db) in
  Lib.add_anonymous_leaf (inSmpl act)

(*** Printing ***)

let pr_progress b =
  str "(" ++ (if b then str "" else str "no") ++ str "progress)"

let smpl_print_entry e =
  let env =
    try
      let (_, env) = Pfedit.get_current_context () in
      env
    with e when CErrors.noncritical e -> Global.env ()
  in let msg = str "Priority " ++ Pp.int e.priority ++ str " "
	       ++ (match e.require_progress with
		   | Some b -> pr_progress b
		   | _ -> str "")
	       ++ str ": "
	       ++ Pptactic.pr_glob_tactic env e.tactic
  in Feedback.msg_info msg

let smpl_db_exists db_name =
  try let db = StringMap.find db_name (!smpl_dbs) in db
  with Not_found -> CErrors.user_err (~hdr:"Smpl")
				     (str "Unknown Smpl Database " ++ str db_name ++ str ".")

let smpl_print db_name =
  try let db = StringMap.find db_name (!smpl_dbs) in
      let _ = Feedback.msg_info (str "Printing Smpl DB " ++ str db_name ++
				   str " "  ++ pr_progress db.progress_default ++ str ".") in
      let _ = Feedback.msg_info (str "Tactics in priority order:") in
      List.iter smpl_print_entry db.queue; ()
  with Not_found -> CErrors.user_err (~hdr:"Smpl")
				     (str "Unknown Smpl Database " ++ str db_name ++ str ".")

let smpl_print_dbs () =
  let _ = Feedback.msg_info (str "Smpl DBs:") in
  StringMap.iter (fun key entry -> Feedback.msg_info (str key)) (!smpl_dbs)

(*** Appling the tactic ***)

let call_tac_prepare_args m args =
  let fold arg (i, vars, lfun) =
    let id = Id.of_string ("x" ^ string_of_int i) in
    let x = Reference (ArgVar (Loc.tag id)) in
    (succ i, x :: vars, Id.Map.add id (Value.of_uconstr arg) lfun)
  in
  let (_, args, lfun) = List.fold_right fold args (0, [], m) in
  (args, lfun)

let call_tac glob_tac args =
  let (args, bindings) = call_tac_prepare_args Id.Map.empty args in
  let cont = Id.of_string "cont" in
  Tacinterp.val_interp (default_ist ()) glob_tac
    (fun glob_tac_val ->
     let tac = TacCall (Loc.tag ((ArgVar (Loc.tag cont)), args)) in
     let ist = { lfun = Id.Map.add cont glob_tac_val bindings;
		 extra = TacStore.empty; } in
     Tacinterp.eval_tactic_ist ist (TacArg (Loc.tag tac)))

let smpl_tac_entry entry args =
  call_tac entry.tactic args

let bool_unopt opt def =
  match opt with
  | Some b -> b
  | _ -> def

let mk_smpl_tac db_name db args =
  let rec f l =
    match l with
    | e::l -> if bool_unopt e.require_progress db.progress_default then
		Tacticals.New.tclORELSE (smpl_tac_entry e args) (f l)
	      else
		Tacticals.New.tclORELSE0 (smpl_tac_entry e args) (f l)
    | _ -> Tacticals.New.tclFAIL 0 (str "smpl " ++ str db_name ++ str ": no tactic applies")
  in f db.queue

let smpl_tac db_name args =
  try let db = StringMap.find db_name (!smpl_dbs) in
      mk_smpl_tac db_name db args
  with Not_found -> Tacticals.New.tclFAIL 0 (str "smpl: db " ++ str db_name ++ str " not found")

(*** Syntax Extensions ***)

let pr_smpl_opts opts =
  prlist (fun s -> spc () ++ str s) opts

VERNAC ARGUMENT EXTEND smpl_opts
  PRINTED BY pr_smpl_opts
| [ "[" ne_preident_list(l) "]" ] -> [ l ]
| [ ] -> [ [] ]
END

let pr_smpldb _prc _prlc _prt s = str s

ARGUMENT EXTEND smpldb
  TYPED AS preident
  PRINTED BY pr_smpldb
| [ preident(i) ] -> [ let _ = smpl_db_exists i in i ]
END


let rec is_opt_set opt opts =
  match opts with
  | o::opts -> if String.compare o opt == 0 then Some true
	       else if String.compare o (String.concat "" ["no"; opt]) == 0 then Some false
	       else is_opt_set opt opts
  | [] -> None

VERNAC COMMAND EXTEND SmplCreate CLASSIFIED AS SIDEFF
   | [ "Smpl" "Create" preident(db) smpl_opts(opts) ] ->
      [ smpl_create db { queue = [];
			 progress_default = bool_unopt (is_opt_set "progress" opts) false } ]
END

VERNAC COMMAND EXTEND SmplAdd CLASSIFIED AS SIDEFF
   | [ "Smpl" "Add" natural_opt(n) smpl_opts(opts) tactic(tac) ":" preident (db) ] ->
      [ smpl_add n (glob_tactic tac) (is_opt_set "progress" opts) db ]
END

VERNAC COMMAND EXTEND SmplPrint CLASSIFIED AS QUERY
   | [ "Smpl" "Print" preident(db) ] ->
      [ smpl_print db ]
END

VERNAC COMMAND EXTEND SmplPrintAll CLASSIFIED AS QUERY
   | [ "Smpl" "Databases" ] ->
      [ smpl_print_dbs () ]
END

TACTIC EXTEND smpl
   | [ "smpl" smpldb(db) uconstr_list(args) ] -> [ smpl_tac db args ]
END
