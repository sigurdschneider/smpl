Declare ML Module "smpl".

(** Smpl provides extendable tactics that are applied in order until the first succeeds. *)
Smpl Create len.

Ltac len_simpl := smpl len; repeat (smpl len).

Require Import List.

Notation "f ⊝ L" := (List.map f L) (at level 50, L at level 50, left associativity).

(* This adds the tactic at priority 100. *)
Ltac len_simpl_app :=
  match goal with
  | [ |- context [ length (?L ++ ?L') ] ] => rewrite (@app_length _ L L')
  | [ H : context [ length (?L ++ ?L') ] |- _ ] => rewrite (@app_length _ L L') in H
  end.

Smpl Add len_simpl_app : len.

Smpl Print len.

(* Specifying an optional priority can be used to insert tactics at a certain position. *)

Ltac len_simpl_map :=
  match goal with
  | [ |- context [ length (?f ⊝ ?L) ] ] => rewrite (@map_length _ _ f L)
  | [ H : context [ length (?f ⊝ ?L) ] |- _ ] => rewrite (@map_length _ _ f L) in H
  end.

Smpl Add 99 len_simpl_map : len.

Smpl Print len.

(* At this point [len simpl] behaves like [ first [ len_simpl_map | len_simpl_app ] ] *)

Hint Extern 0 => len_simpl.

Goal (forall X (f:X->X) L L', length (f ⊝ (L ++ L')) = length (f ⊝ L ++ f ⊝ L')).
  eauto.
Qed.

(* smpl works across modules, like eauto databases.
   This means the tactic [len_simpl] can be modularily
   extended with additional simplification tactics. *)

(** Each smpl database can be configured to require progress
of the tactic. The default is to not require progress. *)

Smpl Create noprogress.

Smpl Print noprogress.

(** The default can be overwritten for individual tactics
with the options [progress] and [noprogress] *)

Smpl Add [progress] idtac : noprogress.

Smpl Print noprogress.

Goal True.
Proof.
  Smpl Print noprogress.
	Fail smpl noprogress.
	first [ idtac ].
	Fail progress first [ idtac ].
	Smpl Add (assert True by auto) : noprogress.
	smpl noprogress.
	assumption.
Qed.
