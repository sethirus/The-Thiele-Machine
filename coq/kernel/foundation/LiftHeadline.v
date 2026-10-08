(** LiftHeadline: model independence, in both directions.

    DOWN (existing, PresentedUniversal.v).  Every computably presented Thiele
    machine, on any base, runs on the one fixed universal machine U_P on the
    Minsky host: the host halts exactly when the driver halts, at every
    matching point the host's register decodes to the machine's state, the
    host flag is the machine's latch, and the host ledger is the machine's
    ledger plus a surcharge of at most 2; the host flag rises exactly when
    the machine's reading is ever yes.  "Computably presented" means that four
    mu-recursive algorithms compute the machine's driver, step, cost and
    reading on the number codes of its states and moves.

    [lift_presented_from_computable] says exactly what that premise is: the four
    code-level relations are computable in the mu-recursive model.  By
    LiftModelsAll.v it makes no difference which of the seven models of the
    vendored library the relations are computable in.
    [lift_computable_runs_on_U] puts the two together: four relations computable
    in any one of Turing machines, binary stack machines, Minsky machines,
    FRACTRAN, mu-recursive functions, L or MMA give a presentation, so U_P
    runs the machine.

    UP (this development).  Every universal base, on any machine, in any
    model, carries a Thiele-complete machine, by adding the earned layer
    [lift_thiele_complete, lift_window_thiele_complete, lift_lax_thiele_complete],
    and the base moves of every Thiele-complete machine are a universal base
    [lift_reduct_universal].  The classic bases: the machine on numbers
    [lift_ex_machine] has its step computable in all seven models, and a
    random-access machine is a base step by step
    [lift_classic_bases].  A universal base needs infinitely many moves
    [lift_ub_not_finitely_branching].

    BOTH.  [lift_model_independence] is the pair together with its premises.

    MINIMALITY.  One counter has decidable halting, two have undecidable
    halting: [lift_oc_halts_dec], [lift_cm_halting_undecidable], [lift_no_oc_translation].

    No axioms and no unfinished proofs.                                                  *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.MuRec Require Import MuRec.
From Undecidability.MuRec.Util Require Import recalg ra_sem_eq.
From Undecidability.L Require Import L.
From Undecidability.TM Require Import TM.
From Undecidability.StackMachines Require Import BSM.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.FRACTRAN Require Import FRACTRAN.
From Undecidability.Synthetic Require Import Undecidability.
From Kernel Require Import AxCore.
From Kernel Require Import AxComplete.
From Kernel Require Import Presentation PresentedUniversal.
Require Import Minimal.Presented.
Require Minimal.ThieleComplete.
Module T := Minimal.ThieleComplete.
From Minimal Require Import LiftCore LiftConverse LiftOneCounter.
From Kernel Require Import LiftAxis LiftExec LiftRAM LiftModels LiftModelsAll.

(** * The premise of DOWN is computability on codes, in any model *)

Section Bridge.

Variable Mp : presented_machine.

Local Notation st := (T.cs_state (pm_sys Mp)).
Local Notation mv := (T.cs_instr (pm_sys Mp)).
Local Notation cstep := (T.cs_step (pm_sys Mp)).
Local Notation ccost := (T.cs_cost (pm_sys Mp)).

(** The four relations on codes that a presentation computes. *)
Definition lift_pm_next_rel (v : Vector.t nat 1) (m : nat) : Prop :=
  exists s : st, Vector.hd v = pm_scode Mp s /\ m = cg_next_val Mp s.

Definition lift_pm_step_rel (v : Vector.t nat 2) (m : nat) : Prop :=
  exists (s : st) (i : mv), Vector.hd v = pm_scode Mp s /\
    Vector.hd (Vector.tl v) = pm_icode Mp i /\ m = pm_scode Mp (cstep s i).

Definition lift_pm_cost_rel (v : Vector.t nat 1) (m : nat) : Prop :=
  exists i : mv, Vector.hd v = pm_icode Mp i /\ m = ccost i.

Definition lift_pm_read_rel (v : Vector.t nat 1) (m : nat) : Prop :=
  m = cg_read_val Mp (Vector.hd v).

(** Computable in the mu-recursive model is a presentation. *)
Theorem lift_presented_from_computable :
  MuRec_computable lift_pm_next_rel -> MuRec_computable lift_pm_step_rel ->
  MuRec_computable lift_pm_cost_rel -> MuRec_computable lift_pm_read_rel ->
  cg_computably_presented Mp.
Proof.
  intros [f1 H1] [f2 H2] [f3 H3] [f4 H4]. apply inhabits.
  refine (cg_mk_presentation Mp f1 f2 f3 f4 _ _ _ _).
  - intro s. apply ra_bs_correct. apply H1. exists s. split; reflexivity.
  - intros s i. apply ra_bs_correct. apply H2. exists s, i.
    split; [reflexivity | split; reflexivity].
  - intro i. apply ra_bs_correct. apply H3. exists i. split; reflexivity.
  - intro v. apply ra_bs_correct. apply H4. reflexivity.
Qed.

(** The five facts of PresentedUniversal.v that say U_P runs the machine,
    read off the theorems themselves. *)
Definition lift_runs_on_U (pc : cg_presentation Mp) (s0 : st) : Prop :=
  ltac:(let a := type of (presented_universal_halting Mp pc s0) in
        let b := type of (presented_universal_points Mp pc s0) in
        let c := type of (presented_universal_halt_point Mp pc s0) in
        let d := type of (presented_universal_flag_iff Mp pc s0) in
        let e := type of (presented_universal_surcharge_le_two Mp pc s0) in
        exact (a /\ b /\ c /\ d /\ e)).

Theorem lift_presented_runs_on_U : forall pc s0, lift_runs_on_U pc s0.
Proof.
  intros pc s0. unfold lift_runs_on_U.
  exact (conj (presented_universal_halting Mp pc s0)
         (conj (presented_universal_points Mp pc s0)
         (conj (presented_universal_halt_point Mp pc s0)
         (conj (presented_universal_flag_iff Mp pc s0)
               (presented_universal_surcharge_le_two Mp pc s0))))).
Qed.

(** Four code-level relations computable in any one of the seven models give a
    presentation, and U_P runs the machine. *)
Theorem lift_computable_runs_on_U :
  (L_computable lift_pm_next_rel \/ MMA_computable lift_pm_next_rel \/ TM_computable lift_pm_next_rel \/
   BSM_computable lift_pm_next_rel \/ MM_computable lift_pm_next_rel \/
   FRACTRAN_computable lift_pm_next_rel \/ MuRec_computable lift_pm_next_rel) ->
  (L_computable lift_pm_step_rel \/ MMA_computable lift_pm_step_rel \/ TM_computable lift_pm_step_rel \/
   BSM_computable lift_pm_step_rel \/ MM_computable lift_pm_step_rel \/
   FRACTRAN_computable lift_pm_step_rel \/ MuRec_computable lift_pm_step_rel) ->
  (L_computable lift_pm_cost_rel \/ MMA_computable lift_pm_cost_rel \/ TM_computable lift_pm_cost_rel \/
   BSM_computable lift_pm_cost_rel \/ MM_computable lift_pm_cost_rel \/
   FRACTRAN_computable lift_pm_cost_rel \/ MuRec_computable lift_pm_cost_rel) ->
  (L_computable lift_pm_read_rel \/ MMA_computable lift_pm_read_rel \/ TM_computable lift_pm_read_rel \/
   BSM_computable lift_pm_read_rel \/ MM_computable lift_pm_read_rel \/
   FRACTRAN_computable lift_pm_read_rel \/ MuRec_computable lift_pm_read_rel) ->
  exists pc : cg_presentation Mp, forall s0, lift_runs_on_U pc s0.
Proof.
  intros Hn Hs Hc Hr.
  destruct (lift_num_models_agree Hn) as [_ [_ [_ [_ [_ [_ Hn']]]]]].
  destruct (lift_num_models_agree Hs) as [_ [_ [_ [_ [_ [_ Hs']]]]]].
  destruct (lift_num_models_agree Hc) as [_ [_ [_ [_ [_ [_ Hc']]]]]].
  destruct (lift_num_models_agree Hr) as [_ [_ [_ [_ [_ [_ Hr']]]]]].
  destruct (lift_presented_from_computable Hn' Hs' Hc' Hr') as [pc].
  exists pc. intro s0. apply lift_presented_runs_on_U.
Qed.

End Bridge.

(** * The headline pair *)

Theorem lift_model_independence :
  (* UP: every universal base, on any machine, lifts to a Thiele-complete machine
     (cap 1 or more), at the point and on every axis with joins *)
  (forall M0 (U : T.universal_base M0) cap, 0 < cap ->
     T.thiele_complete (lift_machine M0 (lift_window_lang M0 U) cap)) /\
  (forall (A : Type) (P : BPre A) (AX : lift_axis P) M0 (U : T.universal_base M0) cap
          (pts : nat -> A) k0, 0 < cap -> ~ bp_le P (pts k0) (lift_la_floor AX) ->
     ax_thiele_complete
       (lift_lax_machine AX M0 (lift_window_lang_pts M0 U) cap (fun ck => pts (snd ck)))) /\
  (* UP, converse: the base moves of every Thiele-complete machine form a universal base *)
  (forall M, T.thiele_complete M ->
     exists I : T.thiele_interface M, T.thiele_complete_with I /\
       inhabited (T.universal_base (lift_reduct M I))) /\
  (* a universal base needs infinitely many moves *)
  (forall M0 (U : T.universal_base M0), ~ lift_finitely_branching M0) /\
  (* no base with finite branching, or whose step ignores the state, ever lifts *)
  (forall M0 LG cap, lift_finitely_branching M0 ->
     ~ T.thiele_complete (lift_machine M0 LG cap)) /\
  (forall M0 LG cap, lift_stateless M0 -> ~ T.thiele_complete (lift_machine M0 LG cap)) /\
  (* the classic bases *)
  (inhabited (T.universal_base lift_ex_machine) /\ lift_in_all_models lift_ex_rel /\
   T.thiele_complete (lift_machine lift_ex_machine (lift_window_lang lift_ex_machine lift_ex_base) 16) /\
   T.thiele_complete (lift_machine lift_ram_machine (lift_window_lang lift_ram_machine lift_ram_base) 16)) /\
  (* DOWN: a computably presented machine runs on U_P; computable in any one model suffices *)
  (forall (Mp : presented_machine) (pc : cg_presentation Mp) s0, lift_runs_on_U pc s0) /\
  (* MINIMALITY: one counter is decidable, two are not *)
  (forall P x, lift_oc_halts P x \/ ~ lift_oc_halts P x) /\ undecidable lift_CM_HALTING.
Proof.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).

  - intros M0 U cap Hcap. apply lift_window_thiele_complete. exact Hcap.
  - intros A P AX M0 U cap pts k0 Hcap Hp.
    exact (lift_lax_window_thiele_complete AX M0 U cap pts k0 Hcap Hp).
  - exact lift_reduct_universal.
  - exact lift_ub_not_finitely_branching.
  - exact lift_finite_branching_not_complete.
  - exact lift_stateless_not_complete.
  - exact lift_classic_bases.
  - intros Mp pc s0. apply lift_presented_runs_on_U.
  - refine (conj _ lift_cm_halting_undecidable). intros P x.
    destruct (lift_oc_halts_dec P x) as [h | h]; [left | right]; exact h.
Qed.

Print Assumptions lift_presented_from_computable.
Print Assumptions lift_computable_runs_on_U.
Print Assumptions lift_model_independence.
