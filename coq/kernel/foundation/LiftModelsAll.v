(** LiftModelsAll: the classic bases, all at once.

    The vendored library proves that seven models compute the same relations
    (Synthetic/Models_Equivalent.v): Turing machines, binary stack machines,
    Minsky machines, FRACTRAN, mu-recursive functions, the weak call-by-value
    lambda calculus L, and alternate Minsky machines (MMA).

    A machine on numbers [lift_num_machine g] has numbers for states and for
    moves, and the step function g.  Its step is realized in a model when the
    step relation, as a relation of two numbers and a result, is computable in
    that model.  [lift_num_models_agree]: if the step is computable in one of the
    seven models it is computable in all seven.

    [lift_ex_machine] of LiftExec.v is a numeric machine with a universal base whose
    step is computable in L by extraction, hence in all seven models
    [lift_ex_in_all_models].  The earned layer over it is Thiele-complete
    [lift_ex_thiele_complete], so there is a Thiele-complete machine whose every
    base move is one run to completion of a Turing machine, one run of a
    mu-recursive algorithm, one evaluation of an L term, one Minsky machine run
    (and so on for each model), on the number codes.

    [lift_numeric_base]: for every numeric machine with a universal base,
    whichever of the seven models its step is computable in, the lifted machine
    is Thiele-complete and its base step is computable in each model.        *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.L Require Import L.
From Undecidability.TM Require Import TM.
From Undecidability.StackMachines Require Import BSM.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.FRACTRAN Require Import FRACTRAN.
From Undecidability.H10 Require Import H10.
From Undecidability.MuRec Require Import MuRec.
From Undecidability.Synthetic Require Import Models_Equivalent.
From Undecidability.MinskyMachines.Reductions Require Import L_computable_to_MMA_computable.
Require Minimal.ThieleComplete.
Module T := Minimal.ThieleComplete.
From Minimal Require Import LiftCore.
From Kernel Require Import LiftExec LiftRAM LiftModels.

(** * Seven models compute the same relations *)

Definition lift_in_all_models {k} (R : Vector.t nat k -> nat -> Prop) : Prop :=
  L_computable R /\ MMA_computable R /\ TM_computable R /\ BSM_computable R /\
  MM_computable R /\ FRACTRAN_computable R /\ MuRec_computable R.

(** Computable in L is computable in all seven. *)
Theorem lift_L_in_all_models : forall {k} (R : Vector.t nat k -> nat -> Prop),
  L_computable R -> lift_in_all_models R.
Proof.
  intros k R HL.
  destruct (equivalence R) as [H1 [H2 [H3 [H4 [H5 [H6 [H7 H8]]]]]]].
  assert (HM : MMA_computable R) by (apply H7; exact HL).
  assert (HT : TM_computable R) by (apply H8; exact HM).
  assert (HB : BSM_computable R) by (apply H1; exact HT).
  assert (HMM : MM_computable R) by (apply H2; exact HB).
  assert (HF : FRACTRAN_computable R) by (apply H3; exact HMM).
  assert (HMu : MuRec_computable R) by (apply H5; apply H4; exact HF).
  repeat split; assumption.
Qed.

(** Computable in any one of the seven is computable in all seven. *)
Theorem lift_num_models_agree : forall {k} (R : Vector.t nat k -> nat -> Prop),
  (L_computable R \/ MMA_computable R \/ TM_computable R \/ BSM_computable R \/
   MM_computable R \/ FRACTRAN_computable R \/ MuRec_computable R) ->
  lift_in_all_models R.
Proof.
  intros k R H.
  destruct (equivalence R) as [H1 [H2 [H3 [H4 [H5 [H6 H78]]]]]].
  destruct H78 as [H7 H8].
  apply lift_L_in_all_models.
  destruct H as [HL | [HM | [HT | [HB | [HMM | [HF | HMu]]]]]].
  - exact HL.
  - apply H6, H5, H4, H3, H2, H1, H8. exact HM.
  - apply H6, H5, H4, H3, H2, H1. exact HT.
  - apply H6, H5, H4, H3, H2. exact HB.
  - apply H6, H5, H4, H3. exact HMM.
  - apply H6, H5, H4. exact HF.
  - apply H6. exact HMu.
Qed.

(** * Numeric machines *)

Definition lift_num_machine (g : nat -> nat -> nat) : T.machine :=
  T.mk_machine nat nat g (fun _ => 0) (fun _ => false).

Definition lift_num_rel (g : nat -> nat -> nat) (v : Vector.t nat 2) (m : nat) : Prop :=
  m = g (Vector.hd v) (Vector.hd (Vector.tl v)).

(** The machine on numbers of LiftExec.v is realized in every model. *)
Theorem lift_ex_in_all_models : lift_in_all_models lift_ex_rel.
Proof. apply lift_L_in_all_models. exact lift_ex_L_computable. Qed.

(** Every numeric machine with a universal base lifts, and its base step is
    computable in all seven models as soon as it is in one. *)
Theorem lift_numeric_base : forall g (U : T.universal_base (lift_num_machine g)),
  T.thiele_complete (lift_machine (lift_num_machine g) (lift_window_lang (lift_num_machine g) U) 16) /\
  ((L_computable (lift_num_rel g) \/ MMA_computable (lift_num_rel g) \/ TM_computable (lift_num_rel g) \/
    BSM_computable (lift_num_rel g) \/ MM_computable (lift_num_rel g) \/
    FRACTRAN_computable (lift_num_rel g) \/ MuRec_computable (lift_num_rel g)) ->
   lift_in_all_models (lift_num_rel g)).
Proof.
  intros g U. split.
  - apply lift_window_thiele_complete. lia.
  - apply lift_num_models_agree.
Qed.

Theorem lift_classic_bases :
  inhabited (T.universal_base lift_ex_machine) /\ lift_in_all_models lift_ex_rel /\
  T.thiele_complete (lift_machine lift_ex_machine (lift_window_lang lift_ex_machine lift_ex_base) 16) /\
  T.thiele_complete (lift_machine lift_ram_machine (lift_window_lang lift_ram_machine lift_ram_base) 16).
Proof.
  split; [exact (inhabits lift_ex_base) |]. split; [exact lift_ex_in_all_models |].
  split; [exact lift_ex_thiele_complete | exact lift_ram_thiele_complete].
Qed.

Print Assumptions lift_L_in_all_models.
Print Assumptions lift_num_models_agree.
Print Assumptions lift_ex_in_all_models.
Print Assumptions lift_numeric_base.
Print Assumptions lift_classic_bases.
