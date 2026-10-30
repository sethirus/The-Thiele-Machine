(* Neutral completeness does not force mark silence for its chosen window. *)
From Coq Require Import List Bool Arith Lia.
Import ListNotations.
Require Minimal.ThieleComplete Minimal.NeutralComplete.
Module T := Minimal.ThieleComplete.
Module N := Minimal.NeutralComplete.

Inductive move := Compute (i : T.cm_instr) | Mark.
Definition state := (T.cm_conf * bool * nat)%type.
Definition step (s : state) (i : move) : state :=
  let '(x,r,l) := s in
  match i with
  | Compute b => (T.cm_exec b x,r,l)
  | Mark => (T.cm_exec (T.CINC T.RA) x, r || Nat.eqb (fst (snd x)) 0,S l)
  end.
Definition price (i : move) := match i with Compute _ => 0 | Mark => 1 end.
Definition machine := T.mk_machine state move step price (fun s => snd (fst s)).
Definition window (s : state) := fst (fst s).
Definition load (a b : nat) : state := ((1,(a,b)),false,0).

Definition base : T.universal_base machine.
Proof.
  refine (T.mk_ub machine window (fun _ => True) Compute load _ _ _).
  - reflexivity.
  - intros; exact I.
  - intros [[x r] l] i _; split; [reflexivity|exact I].
Defined.

Definition interface : N.neutral_interface machine :=
  N.mk_ni machine base (fun i => match i with Compute _ => true | Mark => false end)
    (fun s => snd s).

Theorem complete_with_changing_mark : N.neutral_complete_with interface.
Proof.
  split.
  - split; [reflexivity|]. split.
    + intros [[x r] l] [i|] H; [reflexivity|discriminate].
    + intros [[x r] l] [i|] Hr; cbn in *; [exact Hr|rewrite Hr; reflexivity].
  - split; [intros a b; reflexivity|]. split.
    + split; [intros [i|]; reflexivity|]. intros [[x r] l] [i|]; cbn; lia.
    + exists [Mark],0,0,1,0; split; reflexivity.
Qed.

Theorem chosen_window_is_not_mark_silent :
  window (step (load 0 0) Mark) <> window (load 0 0).
Proof. discriminate. Qed.

(* The claim is about this window, not every possible projection. *)
Theorem neutral_interface_does_not_imply_vertical_silence :
  N.neutral_complete_with interface /\
  ~ (forall s, window (step s Mark) = window s).
Proof.
  split; [apply complete_with_changing_mark|].
  intro H; apply chosen_window_is_not_mark_silent; apply H.
Qed.

Print Assumptions complete_with_changing_mark.
Print Assumptions chosen_window_is_not_mark_silent.
Print Assumptions neutral_interface_does_not_imply_vertical_silence.
