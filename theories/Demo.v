Require Import Smpl.

(** Smpl provides extendable tactics that are applied in order until the first succeeds. *)
Smpl Create len.

(** Example: We define a tactic that will simplify expressions involving List.length.
    Note that repeat will succeed if [smpl len] fails, hence we use the folloing definition: *)
Ltac len_simpl := smpl len; repeat (smpl len).

(**
Smpl fails at parsing if an undeclared databases is used in tactics.
This is possible, because a tactic can only use a database if it has been
created with the command [Smpl Create] before.
The following tactic, for example, will fail: [smpl foo]
 *)

Goal False.
  (** Application of an empty database alyways fails. *)
  Fail smpl len.
Abort.

Require Import List.

Ltac len_simpl_app :=
  match goal with
  | [ |- context [ length (?L ++ ?L') ] ] => rewrite (@app_length _ L L')
  | [ H : context [ length (?L ++ ?L') ] |- _ ] => rewrite (@app_length _ L L') in H
  end.

(* This adds the tactic at priority 100. *)
Smpl Add len_simpl_app : len.

Smpl Print len.

(* Specifying an optional priority can be used to insert tactics at a certain position. *)
Notation "f ⊝ L" := (List.map f L) (at level 50, L at level 50, left associativity).

Ltac len_simpl_map :=
  match goal with
  | [ |- context [ length (?f ⊝ ?L) ] ] => rewrite (@map_length _ _ f L)
  | [ H : context [ length (?f ⊝ ?L) ] |- _ ] => rewrite (@map_length _ _ f L) in H
  end.

Smpl Add 99 len_simpl_map : len.

Smpl Print len.

(* At this point, [len simpl] behaves like [ first [ len_simpl_map | len_simpl_app ] ] *)

Hint Extern 0 => len_simpl : core.

Goal (forall X (f:X->X) L L', length (f ⊝ (L ++ L')) = length (f ⊝ L ++ f ⊝ L')).
  eauto.
  Restart.
  intros. len_simpl. reflexivity.
Qed.

(** smpl works across modules, like eauto databases.
   This means the tactic [len_simpl] can be modularily
   extended with additional simplification tactics.
 *)

(* Like Ltac, smpl does not work across sections: *)
Section Foo.
  Ltac bar := idtac.
  Goal False.
    bar.
  Abort.
  (* This database won't be available outside of the section *)
  Smpl Create foo.

  (* This addition won't survive the section "End". *)
  Smpl Add 101 bar : len.
  Smpl Print len.
End Foo.

Goal False.
  (* Ltac definition [bar] not available  *)
  Fail bar.
Abort.

(* Note that the tactic [bar] is not in len anymore,
   because its definition did not survive the section. *)
Smpl Print len.


(** Each smpl database can be configured to wrap added tactics with
a call to the tactic [progress]. The default is to not wrap with [progress].
This is a convenience feature. *)

Smpl Create example1.
Smpl Create example2 [noprogress].
Smpl Create example3 [progress].

Smpl Print example1.
Smpl Print example2.
Smpl Print example3.

(** The default can be overwritten for individual tactics
with the options [progress] and [noprogress] *)

Smpl Add [progress] idtac : example1.
Smpl Add idtac : example2.
Smpl Add idtac : example3.

Smpl Print example1.
Smpl Print example2.
Smpl Print example3.

Goal True.
Proof.
  Smpl Print example1.
  (** The following tactic application fails, because no progress is made *)
	Fail smpl example1.
  (** The following tactic application succeeds, because progress is not required *)
  smpl example2.
  (* Note that creating new hypotheses constitutes progress: *)
	Smpl Add (assert True by auto) : example1.
	smpl example1.
	assumption.
Qed.


(** Smpl can also works with tactics that take arguments. *)

Smpl Create smpl_with_arg.

Smpl Print smpl_with_arg.

Ltac cont x f := idtac x; idtac f;
               match type of f with
               | ?X -> ?Y => apply f; eapply x
               end.

(* Just at tactic functions to the database. *)

Smpl Add cont : smpl_with_arg.

Smpl Print smpl_with_arg.

Goal (forall (T U : Type) (x:T) (f : T -> U), U).
  intros A B x f.
  (* smpl fails if the argument number does not match *)
  Fail smpl smpl_with_arg.
  Fail smpl smpl_with_arg A.
  smpl smpl_with_arg x f.
Qed.
