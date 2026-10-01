(** Concrete instances for the permanent-certification entropy and pricing
    theorems.

    One two-state machine satisfies every hypothesis of the distribution and
    pricing theorems: a bit that one instruction sets, with the bit as the
    certification record. Each theorem is applied to it, so none of those
    hypotheses is vacuous, and the shadow-price theorem is applied to the VM's
    own collision with a price that meets the floor. *)

From Coq Require Import List Bool Arith.PeanoNat Lia Reals Lra.
Import ListNotations.
From Kernel Require Import VMState VMStep SimulationProof.
From Kernel Require Import UniversalCertificationCost PermanentCertification.
From Kernel Require Import PermanentRecordPricing PermanentCertificationEntropy.
From Kernel Require Import ProjectionNonExistence ShadowPricing.

(** * The reset machine *)

Definition reset_step (b : bool) (_ : unit) : bool := true.
Definition reset_cert (b : bool) : bool := b.
Definition reset_all : list bool := [false; true].
Definition reset_flips : list bool := [false].
Definition reset_cost (_ : unit) : nat := 1.
Definition reset_uniform : bool -> R := uniform_on bool_dec reset_all.

Lemma reset_finite : finite_states reset_all.
Proof.
  split.
  - constructor; [simpl; intros [H | []]; discriminate | constructor; [intros [] | constructor]].
  - intros [|]; simpl; auto.
Qed.

Lemma reset_permanent : permanent reset_step reset_cert.
Proof. intros s i _. reflexivity. Qed.

Lemma reset_flip_list : flip_list reset_step reset_cert tt reset_flips.
Proof.
  split.
  - constructor; [intros [] | constructor].
  - intros t [<- | []]. split; reflexivity.
Qed.

Lemma reset_certified : certified_states bool reset_cert reset_all = [true].
Proof. reflexivity. Qed.

Lemma reset_uniform_value : forall b, reset_uniform b = / 2.
Proof.
  intros [|]; unfold reset_uniform, uniform_on, in_b;
    destruct (in_dec bool_dec _ reset_all) as [_ | H];
    [simpl; field | exfalso; apply H; simpl; auto
    | simpl; field | exfalso; apply H; simpl; auto].
Qed.

Lemma reset_uniform_distribution : distribution reset_all reset_uniform.
Proof.
  split.
  - intro b. rewrite reset_uniform_value. lra.
  - unfold rsum, reset_all. simpl. rewrite !reset_uniform_value. field.
Qed.

Lemma reset_uniform_positive : forall b, 0 < reset_uniform b.
Proof. intro b. rewrite reset_uniform_value. lra. Qed.

Lemma reset_uniform_support :
  forall x, In x reset_all -> 0 < reset_uniform x ->
    In x (certified_states bool reset_cert reset_all ++ reset_flips).
Proof. intros [|] _ _; rewrite reset_certified; simpl; auto. Qed.

(** * Distribution theorems on the reset machine *)

Theorem reset_step_entropy_ceiling :
  entropy reset_all (push bool_dec reset_all (fun s => reset_step s tt) reset_uniform)
    <= log2 (INR (length (certified_states bool reset_cert reset_all))).
Proof.
  apply (permanent_step_entropy_ceiling bool unit reset_step reset_cert bool_dec
           reset_all tt reset_flips).
  - exact reset_finite.
  - exact reset_permanent.
  - exact reset_flip_list.
  - simpl. lia.
  - exact reset_uniform_distribution.
  - exact reset_uniform_support.
Qed.

Theorem reset_step_entropy_drop :
  entropy reset_all reset_uniform
    - entropy reset_all (push bool_dec reset_all (fun s => reset_step s tt) reset_uniform)
  >= entropy reset_all reset_uniform
     - log2 (INR (length (certified_states bool reset_cert reset_all))).
Proof.
  apply (permanent_step_entropy_drop bool unit reset_step reset_cert bool_dec
           reset_all tt reset_flips).
  - exact reset_finite.
  - exact reset_permanent.
  - exact reset_flip_list.
  - simpl. lia.
  - exact reset_uniform_distribution.
  - exact reset_uniform_support.
Qed.

Theorem reset_flip_entropy_drop_positive :
  entropy reset_all reset_uniform
    - entropy reset_all (push bool_dec reset_all (fun t => reset_step t tt) reset_uniform)
  > 0.
Proof.
  apply (permanent_flip_full_support_entropy_drop_positive bool unit reset_step
           reset_cert bool_dec reset_all tt false).
  - exact reset_finite.
  - exact reset_permanent.
  - reflexivity.
  - reflexivity.
  - exact reset_uniform_distribution.
  - intros x _. apply reset_uniform_positive.
Qed.

(** * Compression pricing on the reset machine *)

Lemma bool_nodup_length : forall D : list bool, NoDup D -> (length D <= 2)%nat.
Proof.
  intros D HD.
  change 2%nat with (length reset_all).
  apply NoDup_incl_length; [exact HD |].
  intros [|] _; simpl; auto.
Qed.

Lemma reset_image_size : forall i D,
  D <> [] -> image_size reset_step bool_dec i D = 1%nat.
Proof.
  intros i D HD. unfold image_size, reset_step.
  destruct D as [| d D]; [contradiction |]. clear HD.
  induction D as [| e D IH]; [reflexivity |].
  simpl in *. destruct (in_dec bool_dec true (map (fun _ => true) D)) as [Hin | Hnot].
  - destruct (in_dec bool_dec true (true :: map (fun _ => true) D)); [exact IH | ].
    exfalso. simpl in *. tauto.
  - destruct D as [| f D]; [reflexivity | simpl in Hnot; tauto].
Qed.

Lemma reset_compression_priced : compression_priced reset_step reset_cost bool_dec.
Proof.
  intros i D HD.
  pose proof (bool_nodup_length D HD) as Hlen.
  destruct D as [| d D']; [simpl; lia |].
  rewrite reset_image_size by discriminate.
  unfold reset_cost. simpl in *. lia.
Qed.

Theorem reset_compression_bound :
  (length reset_flips + length (certified_states bool reset_cert reset_all)
     <= 2 ^ reset_cost tt * length (certified_states bool reset_cert reset_all))%nat.
Proof.
  apply (permanent_flips_compression_bound bool unit reset_step reset_cert
           reset_cost bool_dec reset_all tt reset_flips).
  - exact reset_finite.
  - exact reset_permanent.
  - exact reset_compression_priced.
  - exact (proj1 reset_flip_list).
  - exact (proj2 reset_flip_list).
Qed.

Theorem reset_log_bound :
  (Nat.log2_up (length (certified_states bool reset_cert reset_all) + length reset_flips)
     <= reset_cost tt + Nat.log2_up (length (certified_states bool reset_cert reset_all)))%nat.
Proof.
  apply (permanent_flips_log_bound bool unit reset_step reset_cert reset_cost
           bool_dec reset_all false tt reset_flips).
  - exact reset_finite.
  - exact reset_permanent.
  - exact reset_compression_priced.
  - reflexivity.
  - exact (proj1 reset_flip_list).
  - exact (proj2 reset_flip_list).
Qed.

Theorem reset_a2_from_compression : a2_holds reset_step reset_cert reset_cost.
Proof.
  exact (a2_from_compression_price_and_permanence bool unit reset_step reset_cert
           reset_cost bool_dec reset_all reset_finite reset_permanent
           reset_compression_priced).
Qed.

Theorem reset_compression_trace_floor :
  forall trace s0,
    reset_cert s0 = false ->
    reset_cert (cs_run (certification_system_from_compression_price
                          bool unit reset_step reset_cert reset_cost bool_dec reset_all
                          reset_finite reset_permanent reset_compression_priced)
                       trace s0) = true ->
    (cs_total_cost (certification_system_from_compression_price
                      bool unit reset_step reset_cert reset_cost bool_dec reset_all
                      reset_finite reset_permanent reset_compression_priced)
                   trace >= 1)%nat.
Proof.
  intros trace s0. apply compression_priced_trace_floor.
Qed.

(** * Entropy pricing on the reset machine *)

Lemma log2_two : log2 (INR 2) = 1.
Proof.
  unfold log2. simpl INR. replace (1 + 1) with 2 by lra.
  assert (Hln : 0 < ln 2).
  { rewrite <- ln_1. apply ln_increasing; lra. }
  field. lra.
Qed.

(** After the reset every state is [true], so the pushed distribution has
    no entropy. *)
Lemma reset_push_entropy_zero : forall p,
  distribution reset_all p ->
  entropy reset_all (push bool_dec reset_all (fun s => reset_step s tt) p) = 0.
Proof.
  intros p [_ Hsum].
  unfold rsum, reset_all in Hsum. simpl in Hsum.
  unfold entropy, push, rsum, reset_all, reset_step, surprisal_term. simpl.
  replace (p false + (p true + 0)) with 1 by lra.
  replace (0 + (0 + 0)) with 0 by lra.
  destruct (Rlt_dec 0 0) as [H0 | _]; [lra |].
  destruct (Rlt_dec 0 1) as [_ | H1]; [| lra].
  unfold log2. rewrite ln_1. field.
  rewrite <- ln_1. apply Rgt_not_eq. apply ln_increasing; lra.
Qed.

Lemma reset_entropy_priced : entropy_priced reset_step bool_dec reset_all reset_cost.
Proof.
  intros i p Hp. destruct i.
  rewrite reset_push_entropy_zero by exact Hp.
  pose proof (entropy_le_log_support reset_all reset_all p
                (proj1 reset_finite) Hp (fun a Ha _ => Ha) ltac:(simpl; lia)) as Hle.
  simpl length in Hle. rewrite log2_two in Hle.
  unfold reset_cost. simpl INR. lra.
Qed.

Theorem reset_a2_from_entropy : a2_holds reset_step reset_cert reset_cost.
Proof.
  exact (a2_from_entropy_price_and_permanence bool unit reset_step reset_cert
           bool_dec reset_all reset_cost reset_finite reset_permanent
           reset_entropy_priced).
Qed.

Theorem reset_entropy_trace_floor :
  forall trace s0,
    reset_cert s0 = false ->
    reset_cert (cs_run (certification_system_from_entropy_price
                          bool unit reset_step reset_cert reset_cost bool_dec reset_all
                          reset_finite reset_permanent reset_entropy_priced)
                       trace s0) = true ->
    (cs_total_cost (certification_system_from_entropy_price
                      bool unit reset_step reset_cert reset_cost bool_dec reset_all
                      reset_finite reset_permanent reset_entropy_priced)
                   trace >= 1)%nat.
Proof.
  intros trace s0. apply entropy_priced_trace_floor.
Qed.

(** * Shadow pricing on the VM *)

(** The constant price one meets the floor, and on the VM's bare observable
    collision it charges a step that does not certify. *)
Theorem vm_constant_shadow_price_overcharges :
  exists s i,
    flips vm_apply vm_cert s i = false /\
    (shadow_cost vm_apply bare_observable (fun _ _ => 1%nat) s i >= 1)%nat.
Proof.
  apply (shadow_floor_overcharges _ _ _ vm_apply vm_cert bare_observable
           vm_bare_observable_collision).
  intros s i _. unfold shadow_cost. lia.
Qed.

Print Assumptions reset_step_entropy_ceiling.
Print Assumptions reset_step_entropy_drop.
Print Assumptions reset_flip_entropy_drop_positive.
Print Assumptions reset_compression_bound.
Print Assumptions reset_log_bound.
Print Assumptions reset_a2_from_compression.
Print Assumptions reset_compression_trace_floor.
Print Assumptions reset_a2_from_entropy.
Print Assumptions reset_entropy_trace_floor.
Print Assumptions vm_constant_shadow_price_overcharges.
