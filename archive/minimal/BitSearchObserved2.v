(** BitSearchObserved2.v: the n-bit search member, read two more ways.

    BitSearchMember2.v proves the n-bit search entitlement for the program
    that asks k questions, commits and certifies. This file runs the same
    member through the two other forms of EntitlementMore2.v.

      1. The partition form. The covering by fibres that the member supplies
         is in fact a partition by the unasked bits: each survivor's
         observation class holds exactly the 2^k values that share its
         unasked bits [ent2_search_partition].
      2. The observational form. Leave off the COMMIT and the CERTIFY. The
         questions alone narrow 2^(k+m) values to 2^m, the record stays
         down, and the ledger's rise is exactly k: one unit per bit, with
         nothing paid for a certificate that was never raised
         [ent2_search_observed]. The two extra moves of the full program are
         the price of the record, not of the narrowing.

    Dependencies: ThieleComplete.v, EntitlementSmall.v, EntitlementMore2.v,
    MultiThiele2.v, BitSearch2.v, BitSearchMember2.v. No axioms and no
    unfinished proofs.                                                             *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Minimal.ThieleComplete.
Require Import Minimal.EntitlementSmall.
Require Import Minimal.EntitlementMore2.
Require Import Minimal.MultiThiele2.
Require Import Minimal.BitSearch2.
Require Import Minimal.BitSearchMember2.
Require Minimal.EarnedCore.
Require Minimal.EarnedMulti.
Module E := Minimal.EarnedCore.
Module M := Minimal.EarnedMulti.

Local Notation mrun := (M.run E.prop_eqb E.eval).
Local Notation minstr := (@M.instr E.prop).

(* ================================================================= *)
(* 1. The partition form.                                             *)
(* ================================================================= *)

(* No more than 2^k of the (k+m)-bit values share given unasked bits. *)
Lemma ent2_suffix_class : forall k m t,
  length (filter (fun w => ent_bools_eqb (skipn k w) (skipn k t)) (ent_all_bools (k + m)))
    <= 2 ^ k.
Proof.
  intros k m t.
  set (F := filter (fun w => ent_bools_eqb (skipn k w) (skipn k t)) (ent_all_bools (k + m))).
  assert (HF : NoDup F) by (apply NoDup_filter, ent2_nodup_all_bits).
  assert (Hincl : incl F (map (fun w' => w' ++ skipn k t) (ent_all_bools k))).
  { intros w Hw. apply filter_In in Hw as [Hw1 Hw2]. apply ent_bools_eqb_eq in Hw2.
    apply ent2_in_all_bits in Hw1. apply in_map_iff.
    exists (firstn k w). split.
    - rewrite <- Hw2. apply firstn_skipn.
    - apply ent2_in_all_bits. rewrite firstn_length. lia. }
  pose proof (NoDup_incl_length HF Hincl) as H. rewrite map_length, ent_all_bools_length in H.
  exact H.
Qed.

(* The member's covering is a partition by the unasked bits. *)
Theorem ent2_search_partition : forall ans m,
  ent2_partition ent_bools_eqb (fun x => skipn (length ans) x) (ent_complete (length ans))
    (ent2_prior (length ans + m)) (ent2_post ans m).
Proof.
  intros ans m. split.
  - intros x Hx. unfold ent2_prior in Hx. apply ent2_in_all_bits in Hx.
    exists (ans ++ skipn (length ans) x). split.
    + apply ent2_in_post. exists (skipn (length ans) x). split; [| reflexivity].
      rewrite skipn_length. lia.
    + rewrite ent2_skipn_app_len. reflexivity.
  - intros t _. unfold ent2_obs_fibre, ent2_prior. rewrite ent_complete_leaves.
    apply ent2_suffix_class.
Qed.

(* So the member meets the partition form of the bound: the index-bit drop
   is at most the tree's depth. *)
Corollary ent2_search_partition_bits : forall ans m, ans <> [] ->
  Nat.log2_up (length (ent2_prior (length ans + m))) - Nat.log2_up (length (ent2_post ans m))
    <= length ans.
Proof.
  intros ans m Hne.
  pose proof (ent2_partition_bits ent_bools_eqb ent_bools_eqb_eq
                (fun x => skipn (length ans) x) (ent_complete (length ans))
                (ent2_prior (length ans + m)) (ent2_post ans m)
                ltac:(rewrite ent2_post_length; apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia)
                (ent2_search_partition ans m)) as H.
  rewrite ent_complete_depth in H. exact H.
Qed.

(* ================================================================= *)
(* 2. The observational form.                                         *)
(* ================================================================= *)

(* The questions alone: no COMMIT, no CERTIFY. The record stays down, the
   narrowing is the same, and the ledger's rise is k, one per bit. *)
Theorem ent2_search_observed : forall (ans u : list bool),
  ans <> [] -> length ans <= 16 ->
  ent_strictly_stronger
    (ent_member ent_bools_eqb (ent2_agree ans) (ent2_post ans (length u)))
    (ent_member ent_bools_eqb (ent2_agree ans) (ent2_prior (length ans + length u))) /\
  Nat.log2_up (length (ent2_prior (length ans + length u))) -
    Nat.log2_up (length (ent2_post ans (length u))) = length ans /\
  record_moves ent2_minterface (ent2_checks ans 0) = length ans /\
  M.mu (mrun (ent2_checks ans 0) (ent2_world (ans ++ u))) -
    M.mu (ent2_world (ans ++ u)) = length ans /\
  M.cert (mrun (ent2_checks ans 0) (ent2_world (ans ++ u))) = false /\
  ~ earned_chain ent2_minterface (ent2_world (ans ++ u)) (ent2_checks ans 0).
Proof.
  intros ans u Hne Hle.
  set (s0 := ent2_world (ans ++ u)).
  set (tr := ent2_checks ans 0).
  assert (Hrm : record_moves ent2_minterface tr = length ans) by apply ent2_record_moves_checks.
  assert (Hdec : ent2_decode tr = map (fun _ => true) ans).
  { unfold ent2_decode, tr. rewrite ent2_filter_checks.
    apply ent2_map_true, ent2_checks_length. }
  destruct (ent2_checks_pass ans 0 s0 eq_refl
              ltac:(unfold s0; exact (ent2_okb_prefix ans u))
              ltac:(unfold s0; simpl; lia))
    as [_ [_ [_ [Hc [_ [Hmu _]]]]]].
  assert (Hcert : M.cert (mrun tr s0) = false) by (unfold tr; rewrite Hc; reflexivity).
  assert (Haccept : ent_member ent_bools_eqb (ent2_agree ans) (ent2_post ans (length u))
                      (ent2_decode tr) = true).
  { unfold ent_member. apply existsb_exists.
    exists (ans ++ repeat false (length u)). split.
    - apply ent2_in_post. exists (repeat false (length u)). split; [apply repeat_length | reflexivity].
    - apply ent_bools_eqb_eq. rewrite ent2_agree_app, Hdec. reflexivity. }
  pose proof ent2_mmachine_complete as HC. pose proof HC as [_ [_ [Htoll _]]].
  destruct (ent2_observed_representation ent2_mmachine ent2_minterface (list bool) (list bool)
              s0 tr ent2_decode (ent2_agree ans) (fun x => skipn (length ans) x) ent_bools_eqb
              (ent2_prior (length ans + length u)) (ent2_post ans (length u))
              (ent_complete (length ans)) Htoll ent_bools_eqb_eq
              (ent2_narrowing ans (length u) Hne) (ex_intro _ _ (ent2_witness ans (length u) Hne))
              Haccept ltac:(rewrite ent_complete_depth, Hrm; lia)
              ltac:(rewrite ent2_post_length; apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia)
              (ent2_reduction ans (length u)))
    as [C1 [C4 C5]].
  assert (Hbits : Nat.log2_up (length (ent2_prior (length ans + length u))) -
                  Nat.log2_up (length (ent2_post ans (length u))) = length ans).
  { rewrite ent2_prior_length, ent2_post_length, !Nat.log2_up_pow2 by lia. lia. }
  assert (Hm0 : M.mu s0 = 0) by reflexivity.
  split; [exact C1 |]. split; [exact Hbits |]. split; [exact Hrm |].
  fold tr in Hmu.
  split; [rewrite Hmu, Hm0; lia |]. split; [exact Hcert |].
  intro Hch. apply (proj2 (ent2_upgrade_iff ent2_mmachine ent2_minterface HC s0 tr
                             (M.multi_start_clean _))) in Hch.
  change (M.cert (run ent2_mmachine tr s0) = true) in Hch.
  rewrite ent2_run_mmachine in Hch. rewrite Hcert in Hch. discriminate.
Qed.

(* ================================================================= *)
(* Assumption audit.                                                  *)
(* ================================================================= *)

Print Assumptions ent2_suffix_class.
Print Assumptions ent2_search_partition.
Print Assumptions ent2_search_partition_bits.
Print Assumptions ent2_search_observed.
