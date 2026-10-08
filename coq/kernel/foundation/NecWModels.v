(** NecWModels: the outside models pushed to their limits (storage gas,
    gas schedules, the logical payment, the quote, proof-carrying code).

    - Storage. From a fresh (cold) slot, every run that leaves the slot
      nonzero has net charge at least 22100, and storing 1 attains it; so
      the book's 20000 improves to 22100 for a fresh slot. The 20000 is the
      exact bound over every empty slot, cold or warm: an empty warm slot
      written once has net charge exactly 20000.
    - Gas schedules. A one-step run is free exactly when the step is
      uncharged; the flip premises of the "no floor" clause and the
      "does not commit" premise of the overcharge clause are needed (the
      exact toy schedule has an uncharged non-committing step and a charged
      committing one). No overcharge holds exactly when every step costs at
      most its flip indicator, and the quantitative floor exactly when every
      flip costs at least one.
    - The logical payment. The duplicate-free condition is not needed: a
      list that names every state is enough. Finiteness, permanence and the
      flip are each needed.
    - The quote. A Boolean question about the platform is decided by the
      quote exactly when it is a function of the PCR digest.
    - Proof-carrying code. The verification condition holds exactly when a
      certificate exists, and the memory limit is tight: with limit L the
      checker accepts READ a; HALT exactly when a < L. *)

From Coq Require Import List Bool Arith.PeanoNat Lia ZArith.
Import ListNotations.
From Kernel Require Import EVMStorageGas.
From Kernel Require Import CommitmentPredicateAdequacy GasMetering.
From Kernel Require Import PermanentCertification PermanentRecordPricing PricingPhysicsTarget PricingPhysicsAudit.
From Kernel Require Import TPMQuoteGap.
From Kernel Require Import NeculaPCCTarget NeculaPCC.
Close Scope Z_scope.
Open Scope nat_scope.

(* ================================================================= *)
(** * 1. Storage gas                                                  *)
(* ================================================================= *)

Section Storage.

Local Open Scope Z_scope.

Lemma nec_w_warm_empty_invariant : forall news r,
  original r = 0 -> warm r = true ->
  net r >= 2100 + (if current r =? 0 then 0 else 20000) ->
  net (run_stores r news) >= 2100 + (if current (run_stores r news) =? 0 then 0 else 20000).
Proof.
  induction news as [| v news IH]; intros r Horig Hwarm Hinv; [exact Hinv |].
  simpl. apply IH; [simpl; exact Horig | reflexivity |].
  revert Hinv. unfold net, store. simpl.
  unfold sstore_gas, sstore_refund, STORAGE_SET, COLD_STORAGE_WRITE,
    COLD_STORAGE_ACCESS, WARM_ACCESS, REFUND_STORAGE_CLEAR.
  rewrite Horig, Hwarm.
  destruct (Z.eqb_spec (current r) 0) as [Hc | Hc];
    destruct (Z.eqb_spec 0 (current r)) as [Hc' | Hc'];
    destruct (Z.eqb_spec (current r) v) as [Hv | Hv];
    destruct (Z.eqb_spec v 0) as [Hv0 | Hv0];
    destruct (Z.eqb_spec 0 v) as [Hv0' | Hv0'];
    simpl; lia.
Qed.

Theorem nec_w_sstore_fresh_bound_exact :
  (forall news, current (run_stores fresh_slot news) <> 0 ->
     net (run_stores fresh_slot news) >= 22100) /\
  net (run_stores fresh_slot [1]) = 22100.
Proof.
  split; [| vm_compute; reflexivity].
  intros [| v news] Hne; [simpl in Hne; contradiction |].
  simpl. pose proof (nec_w_warm_empty_invariant news (store fresh_slot v) eq_refl eq_refl) as H.
  assert (H0 : net (store fresh_slot v) >= 2100 + (if current (store fresh_slot v) =? 0 then 0 else 20000)).
  { unfold net, store, fresh_slot. simpl.
    unfold sstore_gas, sstore_refund, STORAGE_SET, COLD_STORAGE_WRITE,
      COLD_STORAGE_ACCESS, WARM_ACCESS, REFUND_STORAGE_CLEAR.
    destruct (Z.eqb_spec v 0) as [Hv | Hv]; destruct (Z.eqb_spec 0 v) as [Hv' | Hv'];
      simpl; lia. }
  specialize (H H0). simpl in Hne.
  destruct (Z.eqb_spec (current (run_stores (store fresh_slot v) news)) 0) as [E | E];
    [contradiction | lia].
Qed.

Definition nec_w_warm_empty : SlotRun :=
  {| original := 0; current := 0; warm := true; gas := 0; refund := 0 |}.

Theorem nec_w_sstore_empty_bound_exact :
  (forall r news, original r = 0 -> current r = 0 -> net r >= 0 ->
     current (run_stores r news) <> 0 -> net (run_stores r news) >= STORAGE_SET) /\
  net (run_stores nec_w_warm_empty [1]) = 20000.
Proof.
  split; [| vm_compute; reflexivity].
  intros r news Ho Hc Hn Hne.
  assert (H0 : net r >= (if current r =? 0 then 0 else STORAGE_SET)) by (rewrite Hc; exact Hn).
  pose proof (empty_slot_invariant news r Ho H0) as H.
  destruct (Z.eqb_spec (current (run_stores r news)) 0); [contradiction | exact H].
Qed.

End Storage.

(* ================================================================= *)
(** * 2. Gas schedules                                                *)
(* ================================================================= *)

Theorem nec_w_one_step_free_iff_uncharged :
  forall (G : GasSchedule) s i, lps_total_cost G [i] s = 0 <-> lps_charge G s i = false.
Proof.
  intros G s i. simpl. split.
  - intros H. destruct (lps_charge G s i) eqn:E; [| reflexivity].
    pose proof (lps_charged_costs G s i E). lia.
  - intros H. rewrite (lps_uncharged_free G s i H). reflexivity.
Qed.

Lemma nec_w_toy_universal_floor : universal_certification_floor toy_gas_schedule.
Proof.
  intros trace s0 H0 H1.
  destruct toy_gas_schedule_is_exact as [Hq _].
  pose proof (Hq trace s0). pose proof (certifying_trace_has_cert_flip toy_gas_schedule trace s0 H0 H1).
  lia.
Qed.

(** The flip premises of the "no floor" clause are needed, and so is the
    "does not commit" premise of the overcharge clause: the exact toy
    schedule has an uncharged step that does not commit and a charged step
    that does, and keeps both its floor and its ceiling. *)
Theorem nec_w_gas_clause_premises_needed :
  universal_certification_floor toy_gas_schedule /\
  no_overcharge_for_commitments toy_gas_schedule /\
  lps_charge toy_gas_schedule false OpCompute = false /\
  lps_cert toy_gas_schedule (lps_step toy_gas_schedule false OpCompute) = false /\
  lps_charge toy_gas_schedule false OpCommit = true /\
  cert_flip_local toy_gas_schedule false OpCommit = true.
Proof.
  split; [exact nec_w_toy_universal_floor |].
  split; [exact (proj2 toy_gas_schedule_is_exact) |].
  repeat split; reflexivity.
Qed.

Theorem nec_w_no_overcharge_iff_pointwise :
  forall G : GasSchedule,
    no_overcharge_for_commitments G <->
    forall s i, lps_cost G s i <= (if cert_flip_local G s i then 1 else 0).
Proof.
  intros G. split.
  - intros H s i. specialize (H [i] s). simpl in H. lia.
  - intros H trace. induction trace as [| i rest IH]; intros s; simpl; [lia |].
    specialize (H s i). specialize (IH (lps_step G s i)). lia.
Qed.

Theorem nec_w_quantitative_floor_iff_pointwise :
  forall G : GasSchedule,
    quantitative_certification_floor G <->
    forall s i, cert_flip_local G s i = true -> lps_cost G s i >= 1.
Proof.
  intros G. split.
  - intros H s i Hf. specialize (H [i] s). simpl in H. rewrite Hf in H. lia.
  - intros H trace. induction trace as [| i rest IH]; intros s; simpl; [lia |].
    specialize (IH (lps_step G s i)).
    destruct (cert_flip_local G s i) eqn:E; [specialize (H s i E) |]; lia.
Qed.

(* ================================================================= *)
(** * 3. The logical payment                                          *)
(* ================================================================= *)

Lemma nec_w_nn_forall_in : forall (A : Type) (P : A -> Prop) (l : list A),
  (forall x, ~ ~ P x) -> ~ ~ (forall x, In x l -> P x).
Proof.
  intros A P l Hp. induction l as [| a l IH]; intros H.
  - apply H. intros x [].
  - apply (Hp a). intro Ha. apply IH. intro Hl. apply H.
    intros x [<- | Hx]; [exact Ha | exact (Hl x Hx)].
Qed.

Lemma nec_w_nn_pairwise_dec : forall (A : Type) (l : list A),
  ~ ~ (forall x y, In x l -> In y l -> x = y \/ x <> y).
Proof.
  intros A l H.
  apply (nec_w_nn_forall_in A (fun x => forall y, In y l -> x = y \/ x <> y) l).
  - intros x. apply (nec_w_nn_forall_in A (fun y => x = y \/ x <> y) l). intros y. tauto.
  - intros Hall. apply H. intros x y Hx Hy. exact (Hall x Hx y Hy).
Qed.

Lemma nec_w_in_dec : forall (A : Type) (a : A) (l : list A),
  (forall y, In y l -> a = y \/ a <> y) -> In a l \/ ~ In a l.
Proof.
  intros A a l. induction l as [| b l IH]; intros H; [right; intros [] |].
  destruct (H b (or_introl eq_refl)) as [-> | Hne]; [left; left; reflexivity |].
  destruct (IH (fun y Hy => H y (or_intror Hy))) as [Hin | Hnin].
  - left. right. exact Hin.
  - right. intros [E | Hin]; [exact (Hne (eq_sym E)) | exact (Hnin Hin)].
Qed.

Lemma nec_w_nodup_cover : forall (A : Type) (l : list A),
  (forall x y, In x l -> In y l -> x = y \/ x <> y) ->
  exists l', NoDup l' /\ forall x, In x l <-> In x l'.
Proof.
  intros A l. induction l as [| a l IH]; intros H.
  - exists []. split; [constructor | tauto].
  - destruct (IH (fun x y Hx Hy => H x y (or_intror Hx) (or_intror Hy))) as [l' [Hnd Hiff]].
    destruct (nec_w_in_dec A a l') as [Hin | Hnin].
    + intros y Hy. apply H; [left; reflexivity | right; apply Hiff; exact Hy].
    + exists l'. split; [exact Hnd |]. intros x. split.
      * intros [<- | Hx]; [exact Hin | apply Hiff; exact Hx].
      * intros Hx. right. apply Hiff. exact Hx.
    + exists (a :: l'). split; [constructor; assumption |]. intros x. split.
      * intros [<- | Hx]; [left; reflexivity | right; apply Hiff; exact Hx].
      * intros [<- | Hx]; [left; reflexivity | right; apply Hiff; exact Hx].
Qed.

(** The duplicate-free condition is not needed: a list naming every state
    is enough. *)
Theorem nec_w_logical_payment_cover_list :
  forall (S I : Type) (step : S -> I -> S) (cert : S -> bool) (all : list S) s i,
    (forall t, In t all) ->
    permanent_at step cert i ->
    cert s = false -> cert (step s i) = true -> ~ step_injective step i.
Proof.
  intros S I step cert all s i Hcov Hperm H0 H1 Hinj.
  apply (nec_w_nn_pairwise_dec S all). intros Hdec.
  destruct (nec_w_nodup_cover S all Hdec) as [l' [Hnd Hiff]].
  apply (permanent_at_flip_is_not_injective S I step cert l' s i); try assumption.
  split; [exact Hnd | intros t; apply Hiff; apply Hcov].
Qed.

(** Finiteness, permanence and the flip are each needed. *)
Theorem nec_w_logical_payment_premises_needed :
  (permanent_at (fun (n : nat) (_ : unit) => S n) (fun n => negb (Nat.eqb n 0)) tt /\
   step_injective (fun (n : nat) (_ : unit) => S n) tt /\
   (fun n => negb (Nat.eqb n 0)) 0 = false /\ (fun n => negb (Nat.eqb n 0)) 1 = true) /\
  (finite_states [true; false] /\
   step_injective (fun (b : bool) (_ : unit) => negb b) tt /\
   ~ permanent_at (fun (b : bool) (_ : unit) => negb b) (fun b => b) tt) /\
  (finite_states [true; false] /\
   permanent_at (fun (b : bool) (_ : unit) => b) (fun b => b) tt /\
   step_injective (fun (b : bool) (_ : unit) => b) tt /\
   ~ exists s, (fun b : bool => b) s = false /\ (fun b : bool => b) ((fun (b : bool) (_ : unit) => b) s tt) = true).
Proof.
  split; [| split].
  - split; [intros n _; reflexivity |]. split; [intros a b E; injection E; auto |].
    split; reflexivity.
  - split; [split; [repeat constructor; simpl; intuition discriminate | intros []; simpl; auto] |].
    split; [intros a b E; destruct a, b; simpl in E; congruence |].
    intros H. specialize (H true eq_refl). discriminate.
  - split; [split; [repeat constructor; simpl; intuition discriminate | intros []; simpl; auto] |].
    split; [intros s H; exact H |]. split; [intros a b E; exact E |].
    intros [s [H0 H1]]. congruence.
Qed.

(* ================================================================= *)
(** * 4. The quote                                                    *)
(* ================================================================= *)

Theorem nec_w_quote_decides_iff_digest :
  forall (H : nat -> nat -> nat) (digest : nat -> nat) (nonce : nat) (Phi : Platform -> bool),
    (exists decide : Quote -> bool, forall p, decide (quote H digest nonce p) = Phi p) <->
    (exists claim : nat -> bool, forall p, Phi p = claim (digest (pcr_of_log H (measured_log p)))).
Proof.
  intros H digest nonce Phi. split.
  - intros [decide Hd].
    exists (fun d => decide {| quote_pcr_digest := d; quote_nonce := nonce |}).
    intros p. rewrite <- Hd. reflexivity.
  - intros [claim Hc]. destruct (quote_decides_measured_claims H digest nonce claim) as [decide Hd].
    exists decide. intros p. rewrite Hd, Hc. reflexivity.
Qed.

(* ================================================================= *)
(** * 5. Proof-carrying code                                          *)
(* ================================================================= *)

Theorem nec_w_vc_iff_certificate :
  forall L prog, verification_condition L prog <-> inhabited (PCCProof L prog).
Proof.
  intros L prog. split.
  - intros H. induction H as [| i rest Hi _ IH]; [constructor; constructor |].
    destruct IH as [c]. constructor. exact (PCCStep L i rest Hi c).
  - intros [c]. exact (pcc_certificate_implies_vc L prog c).
Qed.

Theorem nec_w_pcc_limit_tight :
  forall L a, check_program L [PRead a; PHalt] = true <-> a < L.
Proof.
  intros L a. simpl. rewrite andb_true_r, Nat.ltb_lt. reflexivity.
Qed.

Print Assumptions nec_w_sstore_fresh_bound_exact.
Print Assumptions nec_w_sstore_empty_bound_exact.
Print Assumptions nec_w_one_step_free_iff_uncharged.
Print Assumptions nec_w_gas_clause_premises_needed.
Print Assumptions nec_w_no_overcharge_iff_pointwise.
Print Assumptions nec_w_quantitative_floor_iff_pointwise.
Print Assumptions nec_w_logical_payment_cover_list.
Print Assumptions nec_w_logical_payment_premises_needed.
Print Assumptions nec_w_quote_decides_iff_digest.
Print Assumptions nec_w_vc_iff_certificate.
Print Assumptions nec_w_pcc_limit_tight.
