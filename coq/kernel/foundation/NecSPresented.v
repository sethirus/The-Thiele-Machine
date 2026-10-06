(** NecSPresented.v: "One host runs every computably presented Thiele
    machine" and "Exact, within two, and no better" pushed to the limit.

    - "Computably presented" is exactly Church's thesis for one- and
      two-argument functions: every presented machine is computably
      presented if and only if every function nat -> nat and every
      function nat -> nat -> nat is computed by a recursive algorithm.
      Coq does not prove that thesis (the informative excluded middle, a
      standard axiom consistent with Coq, gives a halting decider, which a
      diagonal argument shows no recursive algorithm computes), and an
      explicit machine without a presentation would refute it. So the
      hypothesis is settled as an exact trade with Church's thesis, which
      is the most a proof inside Coq can say about it.
    - "The reading starts at no" is necessary for "within two": the demo
      machine started at a state where the reading is yes has surcharge 3,
      and no host time with the host flag equal to the latch has a ledger
      within two of the machine's.
    - "Within two" is attained: a computably presented machine whose
      reading flips with a move of cost 1 has surcharge exactly 2, and at
      every host time where the host flag is up the host ledger is at least
      the machine's ledger plus 2. So two cannot be lowered to one.
    - "Every first raise costs at least 3" is exactly the condition for a
      zero surcharge at every step (an iff).
    - "No better" is an iff: some run of the host machine from a clean
      start, under some program, ends with its flag equal to M's latch and
      its ledger grown by exactly M's ledger if and only if the latch is
      down or the ledger is at least 3.                                   *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import utils pos vec.
From Undecidability.MuRec.Util Require Import recalg.
Require Minimal.ThieleComplete.
Require Import Minimal.Presented Kernel.Presentation.
Require Import Kernel.UniversalPCodes Kernel.UniversalPBridge Kernel.UniversalPLayout
  Kernel.UniversalPRun.
Require Import Kernel.PresentedUniversal Kernel.PresentedDemo.
Module T := Minimal.ThieleComplete.

Local Notation hstate := (@M.pu_state pu_hprop).
Local Notation hrun_l := (M.pu_run pu_hprop_eqb pu_heval).

(* ================================================================= *)
(* 1. Computably presented is Church's thesis.                        *)
(* ================================================================= *)

Definition nec_s_CT1 : Prop :=
  forall f : nat -> nat, exists r : recalg 1, forall v, ra_rel r (v ## vec_nil) (f v).
Definition nec_s_CT2 : Prop :=
  forall g : nat -> nat -> nat,
    exists r : recalg 2, forall v w, ra_rel r (v ## w ## vec_nil) (g v w).

Lemma nec_s_never_toll : forall (step : nat -> nat -> nat) (cost : nat -> nat) s i,
  (fun _ : nat => false) s = false -> (fun _ : nat => false) (step s i) = true -> cost i >= 1.
Proof. intros. discriminate. Qed.

(* A machine whose cost is f: its presentation computes f. *)
Definition nec_s_cost_machine (f : nat -> nat) : presented_machine :=
  mk_presented
    (T.mk_cert_system nat nat (fun s _ => s) f (fun _ => false)
       (nec_s_never_toll (fun s _ => s) f))
    (fun _ => None) (fun s => s) (fun v => Some v) (fun i => i) (fun v => Some v)
    (fun s => eq_refl) (fun i => eq_refl).

(* A machine whose step is g: its presentation computes g. *)
Definition nec_s_step_machine (g : nat -> nat -> nat) : presented_machine :=
  mk_presented
    (T.mk_cert_system nat nat g (fun _ => 0) (fun _ => false)
       (nec_s_never_toll g (fun _ => 0)))
    (fun _ => None) (fun s => s) (fun v => Some v) (fun i => i) (fun v => Some v)
    (fun s => eq_refl) (fun i => eq_refl).

Theorem nec_s_presented_all_iff_ct :
  (forall Mp : presented_machine, cg_computably_presented Mp) <-> (nec_s_CT1 /\ nec_s_CT2).
Proof.
  split.
  - intro H. split.
    + intro f. destruct (H (nec_s_cost_machine f)) as [pc].
      exists (cg_cost_ra pc). intro v. exact (cg_cost_spec pc v).
    + intro g. destruct (H (nec_s_step_machine g)) as [pc].
      exists (cg_step_ra pc). intros v w. exact (cg_step_spec pc v w).
  - intros [H1 H2] Mp.
    destruct (H1 (fun v => match pm_sdec Mp v with
                           | Some s => cg_next_val Mp s | None => 0 end)) as [rn Hn].
    destruct (H2 (fun v w => match pm_sdec Mp v, pm_idec Mp w with
                             | Some s, Some i => pm_scode Mp (T.cs_step (pm_sys Mp) s i)
                             | _, _ => 0 end)) as [rs Hs].
    destruct (H1 (fun w => match pm_idec Mp w with
                           | Some i => T.cs_cost (pm_sys Mp) i | None => 0 end)) as [rc Hc].
    destruct (H1 (cg_read_val Mp)) as [rr Hr].
    constructor. refine (cg_mk_presentation Mp rn rs rc rr _ _ _ Hr).
    + intro s. pose proof (Hn (pm_scode Mp s)) as E. rewrite pm_sdec_scode in E. exact E.
    + intros s i. pose proof (Hs (pm_scode Mp s) (pm_icode Mp i)) as E.
      rewrite pm_sdec_scode, pm_idec_icode in E. exact E.
    + intro i. pose proof (Hc (pm_icode Mp i)) as E. rewrite pm_idec_icode in E. exact E.
Qed.

(* ================================================================= *)
(* 2. The host's floor from its loaded start.                         *)
(* ================================================================= *)

Lemma nec_s_host_at_floor : forall Mp pc s0 t,
  M.cert (pu_host_at Mp pc s0 t) = true -> M.mu (pu_host_at Mp pc s0 t) >= 3.
Proof.
  intros Mp pc s0 t Hc.
  unfold pu_host_at, pu_hrun in *. fold (pu_host_start Mp pc s0) in *.
  rewrite (M.pu_multi_run_prog_trace pu_hprop_eqb pu_heval) in *.
  destruct (M.pu_multi_certified_run_min_cost pu_hprop_eqb pu_hprop_eqb_eq pu_heval
              (pu_host_start Mp pc s0) _ (M.pu_multi_start_clean _) Hc) as [_ H3].
  exact H3.
Qed.

(* ================================================================= *)
(* 3. "The reading starts at no" is needed for "within two".          *)
(* ================================================================= *)

Theorem nec_s_within_two_needs_no_start :
  T.cs_cert (pm_sys pu_demo) 3 = true /\
  mlatch pu_demo 3 0 = true /\ mledger pu_demo 3 0 = 0 /\ surcharge pu_demo 3 0 = 3 /\
  ~ (exists t,
       M.cert (pu_host_at pu_demo pu_demo_pc 3 t) = mlatch pu_demo 3 0 /\
       M.mu (pu_host_at pu_demo pu_demo_pc 3 t) <= mledger pu_demo 3 0 + 2).
Proof.
  split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
  split; [reflexivity |].
  intros [t [Hc Hm]]. change (mlatch pu_demo 3 0) with true in Hc.
  change (mledger pu_demo 3 0) with 0 in Hm.
  pose proof (nec_s_host_at_floor pu_demo pu_demo_pc 3 t Hc). lia.
Qed.

(* ================================================================= *)
(* 4. "Within two" is attained.                                       *)
(* ================================================================= *)

(* The flip machine: states are numbers, one move adds 1 and costs 1, the
   reading is yes exactly from 1 on. *)
Lemma nec_s_flip_toll : forall (s : nat) (i : unit),
  Nat.leb 1 s = false -> Nat.leb 1 (S s) = true -> 1 >= 1.
Proof. intros. lia. Qed.

Definition nec_s_flip_sys : T.CertificationSystem :=
  T.mk_cert_system nat unit (fun s _ => S s) (fun _ => 1) (fun s => Nat.leb 1 s) nec_s_flip_toll.

Definition nec_s_flip : presented_machine :=
  mk_presented nec_s_flip_sys (fun _ => Some tt) (fun s => s) (fun v => Some v)
    (fun _ => 0) (fun _ => Some tt) (fun s => eq_refl) pu_demo_idec.

Definition nec_s_flip_cost_ra : recalg 1 := ra_comp (ra_cst 1) vec_nil.

Lemma nec_s_flip_read_spec : forall v,
  ra_rel pu_ra_sg (v ## vec_nil) (cg_read_val nec_s_flip v).
Proof.
  intro v. replace (cg_read_val nec_s_flip v) with (if Nat.eqb v 0 then 0 else 1).
  - apply pu_ra_sg_spec.
  - unfold cg_read_val. simpl. rewrite Nat.eqb_refl. destruct v; reflexivity.
Qed.

Definition nec_s_flip_pc : cg_presentation nec_s_flip.
Proof.
  refine (cg_mk_presentation nec_s_flip pu_demo_next_ra pu_demo_step_ra nec_s_flip_cost_ra
            pu_ra_sg _ _ _ nec_s_flip_read_spec).
  - intro s. apply pu_ra_cst1.
  - intros s i. apply (pu_ra_comp _ _ _ _ _ _ (s ## vec_nil)).
    + rewrite ra_rel_fix_succ. reflexivity.
    + intro p. analyse pos p. apply (pu_ra_proj0 1 (s ## 0 ## vec_nil)).
  - intro i. apply pu_ra_cst1.
Defined.

Theorem nec_s_within_two_attained :
  mledger nec_s_flip 0 1 = 1 /\ mlatch nec_s_flip 0 1 = true /\
  surcharge nec_s_flip 0 1 = 2 /\
  (exists t,
     pu_decode nec_s_flip (hv (pu_host_at nec_s_flip nec_s_flip_pc 0 t) pu_RB) = Some 1 /\
     M.mu (pu_host_at nec_s_flip nec_s_flip_pc 0 t) = mledger nec_s_flip 0 1 + 2 /\
     M.cert (pu_host_at nec_s_flip nec_s_flip_pc 0 t) = true) /\
  (forall t, M.cert (pu_host_at nec_s_flip nec_s_flip_pc 0 t) = mlatch nec_s_flip 0 1 ->
     M.mu (pu_host_at nec_s_flip nec_s_flip_pc 0 t) >= mledger nec_s_flip 0 1 + 2).
Proof.
  split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |]. split.
  - destruct (presented_universal_points nec_s_flip nec_s_flip_pc 0 1
                (fun m _ => ltac:(discriminate))) as (t & Hd & Hm & Hc).
    exists t. split; [exact Hd |]. split; [exact Hm | exact Hc].
  - intros t Hc. change (mlatch nec_s_flip 0 1) with true in Hc.
    change (mledger nec_s_flip 0 1) with 1.
    pose proof (nec_s_host_at_floor nec_s_flip nec_s_flip_pc 0 t Hc). lia.
Qed.

(* ================================================================= *)
(* 5. A zero surcharge at every step exactly when every first raise   *)
(*    costs at least 3.                                               *)
(* ================================================================= *)

Lemma nec_s_first_raise_latch : forall Mp n s i,
  first_raise Mp s n = Some i -> mlatch Mp s n = true.
Proof.
  intros Mp. induction n as [| n IH]; intros s i H; simpl in H.
  - destruct (T.cs_cert (pm_sys Mp) s); discriminate.
  - simpl. destruct (T.cs_cert (pm_sys Mp) s) eqn:Hs; [reflexivity |]. simpl.
    destruct (pm_next Mp s) as [j |]; [| discriminate].
    destruct (T.cs_cert (pm_sys Mp) (T.cs_step (pm_sys Mp) s j)) eqn:Hr.
    + destruct n; simpl; rewrite Hr; reflexivity.
    + exact (IH _ _ H).
Qed.

Theorem nec_s_surcharge_zero_iff : forall Mp s0,
  T.cs_cert (pm_sys Mp) s0 = false ->
  ((forall n, surcharge Mp s0 n = 0) <->
   (forall n i, first_raise Mp s0 n = Some i -> T.cs_cost (pm_sys Mp) i >= 3)).
Proof.
  intros Mp s0 H0. split.
  - intros H n i Hf. specialize (H n). unfold surcharge, raise_cost in H.
    rewrite (nec_s_first_raise_latch Mp n s0 i Hf), Hf in H. lia.
  - intros Hc n. unfold surcharge. destruct (mlatch Mp s0 n) eqn:Hl; [| reflexivity].
    destruct (presented_first_raise_spec Mp n s0 H0 Hl) as (m & i & _ & _ & _ & _ & Hf).
    unfold raise_cost. rewrite Hf. pose proof (Hc n i Hf). lia.
Qed.

(* ================================================================= *)
(* 6. "No better" is an iff.                                          *)
(* ================================================================= *)

Lemma nec_s_pays : forall L (s : hstate),
  M.cert (hrun_l (repeat M.PAY L) s) = M.cert s /\
  M.mu (hrun_l (repeat M.PAY L) s) = M.mu s + L.
Proof.
  induction L as [| L IH]; intro s; simpl; [split; [reflexivity | lia] |].
  destruct (IH (M.pu_exec pu_hprop_eqb pu_heval s M.PAY)) as [Hc Hm]. rewrite Hc, Hm. simpl.
  rewrite orb_false_r. split; [reflexivity | lia].
Qed.

Theorem nec_s_exact_host_iff_bool : forall (b : bool) (L : nat),
  (exists (h0 : hstate) tr, M.pu_clean_start h0 /\
     M.cert (hrun_l tr h0) = b /\ M.mu (hrun_l tr h0) = M.mu h0 + L) <->
  (b = false \/ 3 <= L).
Proof.
  intros b L. split.
  - intros [h0 [tr [H0 [Hc Hm]]]]. destruct b; [right | left; reflexivity].
    destruct (M.pu_multi_certified_run_min_cost pu_hprop_eqb pu_hprop_eqb_eq pu_heval
                h0 tr H0 Hc) as [_ H3]. lia.
  - intros [-> | HL].
    + exists (M.pu_start (fun _ => 0)), (repeat M.PAY L).
      split; [apply M.pu_multi_start_clean |].
      destruct (nec_s_pays L (M.pu_start (fun _ => 0))) as [Hc Hm]. auto.
    + destruct b.
      * destruct (M.pu_multi_chain_certifies pu_hprop_eqb pu_hprop_eqb_eq pu_heval pu_hholds
                    pu_heval_iff PSlot 0 (fun _ => 1) pu_hholds_one) as [Hc Hm].
        rewrite (M.pu_multi_run_prog_trace pu_hprop_eqb pu_heval) in Hc, Hm.
        exists (M.pu_start (fun _ : M.pu_reg => 1)),
          (M.pu_trace_of pu_hprop_eqb pu_heval 4 (M.pu_chain PSlot 0) (M.pu_start (fun _ : M.pu_reg => 1))
           ++ repeat M.PAY (L - 3)).
        split; [apply M.pu_multi_start_clean |].
        rewrite (M.pu_multi_run_app pu_hprop_eqb pu_heval).
        match goal with |- context [hrun_l (repeat M.PAY (L - 3)) ?x] =>
          destruct (nec_s_pays (L - 3) x) as [Hc' Hm'] end.
        rewrite Hc', Hm', Hc, Hm. split; [reflexivity |]. simpl. lia.
      * exists (M.pu_start (fun _ => 0)), (repeat M.PAY L).
        split; [apply M.pu_multi_start_clean |].
        destruct (nec_s_pays L (M.pu_start (fun _ => 0))) as [Hc Hm]. auto.
Qed.

Corollary nec_s_exact_host_iff : forall (Mp : presented_machine) (s0 : T.cs_state (pm_sys Mp)) n,
  (exists (h0 : hstate) tr, M.pu_clean_start h0 /\
     M.cert (hrun_l tr h0) = mlatch Mp s0 n /\
     M.mu (hrun_l tr h0) = M.mu h0 + mledger Mp s0 n) <->
  (mlatch Mp s0 n = false \/ 3 <= mledger Mp s0 n).
Proof. intros. apply nec_s_exact_host_iff_bool. Qed.

Print Assumptions nec_s_presented_all_iff_ct.
Print Assumptions nec_s_host_at_floor.
Print Assumptions nec_s_within_two_needs_no_start.
Print Assumptions nec_s_within_two_attained.
Print Assumptions nec_s_surcharge_zero_iff.
Print Assumptions nec_s_exact_host_iff_bool.
Print Assumptions nec_s_exact_host_iff.

(* ================================================================= *)
(* 7. PAY must be read as a record move.                              *)
(* ================================================================= *)

(* Under any reading of the priced host that meets the exact toll clause,
   PAY is not a base move: it costs 1 and base moves cost 0. Reading it as
   a check that never passes is one admissible record reading. *)
Theorem nec_s_pay_is_record_move : forall I : T.thiele_interface pu_host_machine,
  T.exact_toll_clause I -> T.ti_kind I M.PAY <> T.KBase.
Proof.
  intros I [Hc _] Hk. specialize (Hc M.PAY). unfold T.record_move in Hc.
  rewrite Hk in Hc. discriminate Hc.
Qed.

Print Assumptions nec_s_pay_is_record_move.
