(** ReceiptIntegrity: predicates for receipt arithmetic and chaining

  This file defines the minimum integrity conditions for a receipt: the
  claimed post-state μ must equal pre-state μ plus the instruction cost,
  and the μ values must stay inside the chosen natural-number range. The
  point is narrow and operational. A valid value of these predicates
  establishes those stated equalities and bounds; it does not authenticate
  an externally supplied history.

  A receipt with an inconsistent μ increment is rejected by
  receipt_mu_consistent. A receipt outside the selected range is rejected by
  receipt_mu_in_range. The key equalities are not left informal; they are
  built directly into the predicates and their boolean checkers.

  *)

From Coq Require Import List Bool Arith.PeanoNat Lia Ring.
Import ListNotations.

Require Import Kernel.VMState.
Require Import Kernel.VMStep.

Module ReceiptIntegrity.

(** Receipt structure
    
    A receipt records:
    - The instruction
    - The pre-state and post-state μ values
    - Abstract pre-state and post-state hash fields
    
    The key arithmetic property is that the instruction's scheduled cost
    agrees with the recorded μ increment.
    *)

(** Abstract state-hash field. This development compares the stored natural
    numbers for equality; it does not define a cryptographic hash function. *)
Definition state_hash := nat.

(** μ Range Constants (Q16.16 Fixed Point)
    
    CRITICAL: μ values must fit in 32-bit Q16.16 fixed-point format.
    Hardware uses 32-bit registers; Python must enforce the same bounds.
    
    Q16_MAX = 2^31 - 1 = 2147483647
    Q16_MIN = -2^31   = -2147483648 (but as nat, we use 0)
    
    For Coq nat, we only have non-negative values, so:
    - mu_max = Q16_MAX as the upper bound
    - mu is valid if 0 ≤ mu ≤ mu_max
    *)

(** We define mu_max as 2^31 - 1 using Nat.pow to avoid large literal issues *)
Definition mu_max : nat := Nat.pow 2 31 - 1.

(** μ range predicate: is the value within valid Q16.16 bounds? *)
Definition mu_in_range (mu : nat) : Prop := mu <= mu_max.

Definition mu_in_range_b (mu : nat) : bool := Nat.leb mu mu_max.

Lemma mu_in_range_b_correct :
  forall mu, mu_in_range_b mu = true <-> mu_in_range mu.
Proof.
  intros mu.
  unfold mu_in_range_b, mu_in_range.
  rewrite Nat.leb_le.
  reflexivity.
Qed.

Record Receipt := {
  receipt_step : nat;
  receipt_instruction : vm_instruction;
  receipt_pre_mu : nat;
  receipt_post_mu : nat;
  receipt_pre_state_hash : state_hash;
  receipt_post_state_hash : state_hash;
}.

(** Instruction cost consistency
    
    The receipt's instruction cost is the value computed by
    instruction_cost.
    
    We expose that value through instruction_mu_delta and use it as the
    verification criterion for the receipt arithmetic.
    *)

Definition instruction_mu_delta (instr : vm_instruction) : nat :=
  instruction_cost instr.

(** Receipt validity predicate
    
    The arithmetic predicate requires:
    1. post_mu = pre_mu + instruction_cost(instruction)
    
    The separate receipt_valid_for_step predicate below adds an explicit
    VMState transition witness when those states are available.
    *)

Definition receipt_mu_consistent (r : Receipt) : Prop :=
  r.(receipt_post_mu) = r.(receipt_pre_mu) + instruction_mu_delta r.(receipt_instruction).

(** Boolean version for decidable checking *)
Definition receipt_mu_consistent_b (r : Receipt) : bool :=
  Nat.eqb r.(receipt_post_mu) (r.(receipt_pre_mu) + instruction_mu_delta r.(receipt_instruction)).

Lemma receipt_mu_consistent_b_correct :
  forall r, receipt_mu_consistent_b r = true <-> receipt_mu_consistent r.
Proof.
  intros r.
  unfold receipt_mu_consistent_b, receipt_mu_consistent.
  rewrite Nat.eqb_eq.
  reflexivity.
Qed.

(** μ range validity
    
    Both pre_mu and post_mu must be in the selected range. This is a
    representation predicate for the chosen bound; it is not a proof about
    a separate implementation's arithmetic or transport layer.
    *)

Definition receipt_mu_in_range (r : Receipt) : Prop :=
  mu_in_range r.(receipt_pre_mu) /\ mu_in_range r.(receipt_post_mu).

Definition receipt_mu_in_range_b (r : Receipt) : bool :=
  mu_in_range_b r.(receipt_pre_mu) && mu_in_range_b r.(receipt_post_mu).

Lemma receipt_mu_in_range_b_correct :
  forall r, receipt_mu_in_range_b r = true <-> receipt_mu_in_range r.
Proof.
  intros r.
  unfold receipt_mu_in_range_b, receipt_mu_in_range.
  rewrite Bool.andb_true_iff.
  rewrite mu_in_range_b_correct.
  rewrite mu_in_range_b_correct.
  reflexivity.
Qed.

(** Complete Receipt Validity (with range check)
    
    A receipt is valid iff:
    1. μ arithmetic is consistent (receipt_mu_consistent)
    2. μ values are in valid range (receipt_mu_in_range)
    *)

Definition receipt_fully_valid (r : Receipt) : Prop :=
  receipt_mu_consistent r /\ receipt_mu_in_range r.

Definition receipt_fully_valid_b (r : Receipt) : bool :=
  receipt_mu_consistent_b r && receipt_mu_in_range_b r.

Lemma receipt_fully_valid_b_correct :
  forall r, receipt_fully_valid_b r = true <-> receipt_fully_valid r.
Proof.
  intros r.
  unfold receipt_fully_valid_b, receipt_fully_valid.
  rewrite Bool.andb_true_iff.
  rewrite receipt_mu_consistent_b_correct.
  rewrite receipt_mu_in_range_b_correct.
  reflexivity.
Qed.

(** Receipt validity for a supplied VM step
    
    This predicate combines μ arithmetic with a supplied VM step witness.
    
    The transition condition requires witnessing that vm_step holds.
    *)

Definition receipt_valid_for_step (r : Receipt) (s_pre s_post : VMState) : Prop :=
  receipt_mu_consistent r /\
  s_pre.(vm_mu) = r.(receipt_pre_mu) /\
  s_post.(vm_mu) = r.(receipt_post_mu) /\
  vm_step s_pre r.(receipt_instruction) s_post.

(** Receipt Chain Validity
    
    A chain of receipts is valid iff:
    1. Each receipt is individually valid
    2. Consecutive receipts chain correctly (post_mu of n = pre_mu of n+1)
    3. Consecutive receipts have matching state hashes (post_hash of n = pre_hash of n+1)
    4. The chain starts from a known initial state
    *)

(** μ-chain links: post_mu of r1 = pre_mu of r2 *)
Definition chain_links_mu (rs : list Receipt) : Prop :=
  forall i r1 r2,
    nth_error rs i = Some r1 ->
    nth_error rs (S i) = Some r2 ->
    r1.(receipt_post_mu) = r2.(receipt_pre_mu).

(** State-hash-field chain links: post field of r1 = pre field of r2.
    This is an equality condition on the stored fields. It is not a
    cryptographic authentication or collision-resistance claim. *)
Definition chain_links_hash (rs : list Receipt) : Prop :=
  forall i r1 r2,
    nth_error rs i = Some r1 ->
    nth_error rs (S i) = Some r2 ->
    r1.(receipt_post_state_hash) = r2.(receipt_pre_state_hash).

(** Complete chain links: both μ AND hash must match *)
Definition chain_links (rs : list Receipt) : Prop :=
  chain_links_mu rs /\ chain_links_hash rs.

Fixpoint chain_links_b (rs : list Receipt) : bool :=
  match rs with
  | [] => true
  | [_] => true
  | r1 :: (r2 :: rest as tail) =>
      Nat.eqb r1.(receipt_post_mu) r2.(receipt_pre_mu) &&
      Nat.eqb r1.(receipt_post_state_hash) r2.(receipt_pre_state_hash) &&
      chain_links_b tail
  end.

Definition chain_all_consistent (rs : list Receipt) : Prop :=
  Forall receipt_mu_consistent rs.

(** All receipts have μ values in valid range *)
Definition chain_all_in_range (rs : list Receipt) : Prop :=
  Forall receipt_mu_in_range rs.

Fixpoint chain_all_consistent_b (rs : list Receipt) : bool :=
  match rs with
  | [] => true
  | r :: rest => receipt_mu_consistent_b r && chain_all_consistent_b rest
  end.

Fixpoint chain_all_in_range_b (rs : list Receipt) : bool :=
  match rs with
  | [] => true
  | r :: rest => receipt_mu_in_range_b r && chain_all_in_range_b rest
  end.

(** Full validity includes both consistency and range *)
Definition chain_all_valid (rs : list Receipt) : Prop :=
  chain_all_consistent rs /\ chain_all_in_range rs.

Fixpoint chain_all_valid_b (rs : list Receipt) : bool :=
  match rs with
  | [] => true
  | r :: rest => receipt_fully_valid_b r && chain_all_valid_b rest
  end.

Definition receipt_chain_valid (rs : list Receipt) (initial_mu : nat) : Prop :=
  chain_all_consistent rs /\
  chain_all_in_range rs /\
  chain_links rs /\
  (match rs with
   | [] => True
   | r :: _ => r.(receipt_pre_mu) = initial_mu
   end).

(** Boolean version for runtime checking *)
Definition receipt_chain_valid_b (rs : list Receipt) (initial_mu : nat) : bool :=
  chain_all_valid_b rs &&
  chain_links_b rs &&
  match rs with
  | [] => true
  | r :: _ => Nat.eqb r.(receipt_pre_mu) initial_mu
  end.

(** Main theorem: a valid receipt chain fixes the ledger sum
    
    If a receipt chain is valid starting from initial_mu,
    then the final_mu equals the sum of all instruction costs.
    
    This is a schedule-relative arithmetic theorem: the final recorded μ
    equals the initial μ plus the sum of the instruction costs in the chain.
    It does not establish that an external party generated the chain by
    executing the instructions.
    *)

Fixpoint chain_total_cost (rs : list Receipt) : nat :=
  match rs with
  | [] => 0
  | r :: rest => instruction_mu_delta r.(receipt_instruction) + chain_total_cost rest
  end.

Definition chain_final_mu (rs : list Receipt) (initial_mu : nat) : nat :=
  initial_mu + chain_total_cost rs.

(** Head-extraction definitions for chain_links. They project the
    [i = 0] specialisation out of the universally-quantified
    [chain_links_*] predicates. Expressed as [Definition] with explicit
    proof terms — not derivations. *)
Definition chain_links_mu_head
  (r1 r2 : Receipt) (rest : list Receipt)
  (Hlinks : chain_links_mu (r1 :: r2 :: rest)) :
  r1.(receipt_post_mu) = r2.(receipt_pre_mu) :=
  Hlinks 0 r1 r2 eq_refl eq_refl.

Definition chain_links_hash_head
  (r1 r2 : Receipt) (rest : list Receipt)
  (Hlinks : chain_links_hash (r1 :: r2 :: rest)) :
  r1.(receipt_post_state_hash) = r2.(receipt_pre_state_hash) :=
  Hlinks 0 r1 r2 eq_refl eq_refl.

Lemma chain_links_head :
  forall r1 r2 rest,
    chain_links (r1 :: r2 :: rest) ->
    r1.(receipt_post_mu) = r2.(receipt_pre_mu).
Proof.
  intros r1 r2 rest [Hmu _].
  apply (chain_links_mu_head r1 r2 rest). exact Hmu.
Qed.

Lemma chain_links_mu_tail :
  forall r rest,
    chain_links_mu (r :: rest) ->
    chain_links_mu rest.
Proof.
  intros r rest Hlinks.
  unfold chain_links_mu in *.
  intros i r1 r2 H1 H2.
  apply (Hlinks (S i) r1 r2); assumption.
Qed.

Lemma chain_links_hash_tail :
  forall r rest,
    chain_links_hash (r :: rest) ->
    chain_links_hash rest.
Proof.
  intros r rest Hlinks.
  unfold chain_links_hash in *.
  intros i r1 r2 H1 H2.
  apply (Hlinks (S i) r1 r2); assumption.
Qed.

Lemma chain_links_tail :
  forall r rest,
    chain_links (r :: rest) ->
    chain_links rest.
Proof.
  intros r rest [Hmu Hhash].
  split.
  - apply (chain_links_mu_tail r rest). exact Hmu.
  - apply (chain_links_hash_tail r rest). exact Hhash.
Qed.

(** Head-projection definition for chain_all_consistent (which is
    [Forall ...]). Pure extraction; no derivation. *)
Definition chain_all_consistent_head
  (r : Receipt) (rest : list Receipt)
  (Hconsistent : chain_all_consistent (r :: rest)) :
  receipt_mu_consistent r :=
  match Hconsistent in Forall _ l return
    match l with
    | [] => True
    | x :: _ => receipt_mu_consistent x
    end
  with
  | Forall_nil _ => I
  | Forall_cons _ Hr _ => Hr
  end.

Lemma chain_all_consistent_tail :
  forall r rest,
    chain_all_consistent (r :: rest) ->
    chain_all_consistent rest.
Proof.
  intros r rest Hconsistent.
  unfold chain_all_consistent in *.
  inversion Hconsistent. assumption.
Qed.

Lemma chain_final_mu_correct :
  forall rs initial_mu,
    receipt_chain_valid rs initial_mu ->
    match rs with
    | [] => True
    | _ => 
        let last_r := nth (length rs - 1) rs {| receipt_step := 0; 
                                                 receipt_instruction := instr_halt 0;
                                                 receipt_pre_mu := 0;
                                                 receipt_post_mu := 0;
                                                 receipt_pre_state_hash := 0;
                                                 receipt_post_state_hash := 0 |} in
        last_r.(receipt_post_mu) = chain_final_mu rs initial_mu
    end.
Proof.
  intros rs initial_mu Hvalid.
  destruct rs as [|r rest]; [trivial|].
  unfold receipt_chain_valid in Hvalid.
  destruct Hvalid as [Hconsistent [Hinrange [Hlinks Hstart]]].
  (* We need to prove for a non-empty list starting with r *)
  (* The proof proceeds by strong induction on list length *)
  revert r initial_mu Hconsistent Hinrange Hlinks Hstart.
  induction rest as [|r2 rest' IHrest].
  - (* Single element chain [r] *)
    intros r initial_mu Hconsistent Hinrange Hlinks Hstart.
    simpl. (* Goal: receipt_post_mu r = initial_mu + instruction_mu_delta (receipt_instruction r) *)
    unfold chain_final_mu. simpl.
    pose proof (chain_all_consistent_head r [] Hconsistent) as Hrc.
    unfold receipt_mu_consistent in Hrc.
    (* Hrc: receipt_post_mu r = receipt_pre_mu r + instruction_mu_delta ... *)
    (* Hstart: receipt_pre_mu r = initial_mu *)
    lia.
  - (* Chain r :: r2 :: rest' *)
    intros r initial_mu Hconsistent Hinrange Hlinks Hstart.
    simpl.
    unfold chain_final_mu. simpl.
    pose proof (chain_all_consistent_head r (r2 :: rest') Hconsistent) as Hrc.
    unfold receipt_mu_consistent in Hrc.
    (* Extract mu-link from the conjunction *)
    destruct Hlinks as [Hlinks_mu Hlinks_hash].
    pose proof (chain_links_mu_head r r2 rest' Hlinks_mu) as Hlink12.
    pose proof (chain_all_consistent_tail r (r2 :: rest') Hconsistent) as Htail_consistent.
    (* Extract range info for tail *)
    assert (Htail_inrange : chain_all_in_range (r2 :: rest')).
    { unfold chain_all_in_range in *. inversion Hinrange. assumption. }
    (* Rebuild chain_links for tail *)
    assert (Htail_links : chain_links (r2 :: rest')).
    { split.
      - apply (chain_links_mu_tail r (r2 :: rest')). exact Hlinks_mu.
      - apply (chain_links_hash_tail r (r2 :: rest')). exact Hlinks_hash. }
    assert (Hlink12_sym : receipt_pre_mu r2 = receipt_post_mu r) by (symmetry; exact Hlink12).
    specialize (IHrest r2 r.(receipt_post_mu) Htail_consistent Htail_inrange Htail_links Hlink12_sym).
    simpl in IHrest.
    unfold chain_final_mu in IHrest.
    (* IHrest now establishes the tail property *)
    assert (Hlen_eq: length rest' - 0 = length rest') by lia.
    rewrite Hlen_eq in IHrest.
    (* Hrc: post(r) = pre(r) + delta(r), Hstart: pre(r) = initial *)
    assert (Hpost: receipt_post_mu r = initial_mu + instruction_mu_delta (receipt_instruction r)).
    { rewrite Hrc. rewrite Hstart. reflexivity. }
    rewrite Hpost in IHrest.
    (* Now IHrest has: nth ... = (initial + delta(r)) + (delta(r2) + cost(rest')) *)
    (* Goal has: nth ... = initial + (delta(r) + (delta(r2) + cost(rest'))) *)
    (* These are equal by Nat.add_assoc *)
    rewrite <- Nat.add_assoc in IHrest.
    exact IHrest.
Qed.

(** Receipt Validation Soundness

    If receipt_chain_valid holds, then the claimed μ equals the sum of the
    instruction costs in the chain.

    SCOPE. This is soundness of the validation predicate, not unforgeability.
    Any chain that *passes* receipt_chain_valid has final μ equal to the summed
    costs, because receipt_mu_consistent enforces the equality stepwise. That
    is what makes the checker meaningful.

    It is not a security property. There is no adversary model here, no
    computational hardness assumption, and no claim that a colliding chain is
    infeasible to produce; an adversary free to choose the chain can simply
    emit a consistent one. Unforgeability would additionally require the hash
    chain to be collision-resistant, which is a cryptographic assumption this
    development neither makes nor needs.

    The exact boundary is the predicate above: a chain satisfying
    [receipt_chain_valid] must have the stated final ledger equal to the
    stepwise cost sum. This theorem does not provide unforgeability or a
    cryptographic adversary model.
    *)

Theorem valid_chain_mu_equals_computation :
  forall rs initial_mu,
    receipt_chain_valid rs initial_mu ->
    forall claimed_final_mu,
      (* If someone claims final_mu *)
      (match rs with
       | [] => claimed_final_mu = initial_mu
       | _ => 
           let last_r := nth (length rs - 1) rs {| receipt_step := 0; 
                                                    receipt_instruction := instr_halt 0;
                                                    receipt_pre_mu := 0;
                                                    receipt_post_mu := 0;
                                                    receipt_pre_state_hash := 0;
                                                    receipt_post_state_hash := 0 |} in
           claimed_final_mu = last_r.(receipt_post_mu)
       end) ->
      (* Then it equals the computed sum *)
      claimed_final_mu = chain_final_mu rs initial_mu.
Proof.
  intros rs initial_mu Hvalid claimed_final_mu Hclaim.
  destruct rs as [|r rest].
  - (* Empty chain *)
    simpl in Hclaim.
    unfold chain_final_mu. simpl.
    rewrite Nat.add_0_r.
    exact Hclaim.
  - (* Non-empty chain - use chain_final_mu_correct *)
    pose proof (chain_final_mu_correct (r :: rest) initial_mu Hvalid) as Hfinal.
    simpl in Hfinal.
    simpl in Hclaim.
    rewrite Hclaim.
    exact Hfinal.
Qed.

(** Inconsistent-increment detection
    
    Any receipt with mu_delta ≠ instruction_cost is INVALID.
    
    A receipt whose supplied increment differs from the instruction's
    scheduled cost cannot satisfy receipt_mu_consistent.
    *)

Definition is_forged_receipt (r : Receipt) (claimed_mu_delta : nat) : Prop :=
  claimed_mu_delta <> instruction_mu_delta r.(receipt_instruction).

Theorem forged_receipt_fails_validation :
  forall r claimed_mu_delta,
    is_forged_receipt r claimed_mu_delta ->
    (* If someone tries to forge with wrong mu_delta *)
    r.(receipt_post_mu) = r.(receipt_pre_mu) + claimed_mu_delta ->
    claimed_mu_delta <> instruction_mu_delta r.(receipt_instruction) ->
    (* Then receipt_mu_consistent is FALSE *)
    ~ receipt_mu_consistent r.
Proof.
  intros r claimed_mu_delta _ Hpost Hneq.
  unfold receipt_mu_consistent.
  intro Hconsistent.
  rewrite Hpost in Hconsistent.
  apply Nat.add_cancel_l in Hconsistent.
  contradiction.
Qed.

(** Out-of-range receipt detection
    
    Any receipt with μ values outside the selected range is invalid under
    receipt_mu_in_range.
    *)

Definition is_overflow_receipt (r : Receipt) : Prop :=
  r.(receipt_pre_mu) > mu_max \/ r.(receipt_post_mu) > mu_max.

Theorem overflow_receipt_fails_range_check :
  forall r,
    is_overflow_receipt r ->
    ~ receipt_mu_in_range r.
Proof.
  intros r Hoverflow.
  unfold receipt_mu_in_range, mu_in_range.
  intro Hrange.
  destruct Hrange as [Hpre Hpost].
  destruct Hoverflow as [Hpre_over | Hpost_over]; lia.
Qed.

Theorem overflow_receipt_fails_full_validation :
  forall r,
    is_overflow_receipt r ->
    ~ receipt_fully_valid r.
Proof.
  intros r Hoverflow.
  unfold receipt_fully_valid.
  intro Hvalid.
  destruct Hvalid as [_ Hrange].
  exact (overflow_receipt_fails_range_check r Hoverflow Hrange).
Qed.

(** Implementation boundary note

    An implementation that uses these predicates must require
    receipt_mu_consistent_b for an individual receipt and
    receipt_chain_valid_b for a chain. Those checks cover the formal
    arithmetic and link conditions defined here. Signature validation,
    authenticated state hashing, and any hardware transport contract are
    separate interfaces and are not defined in this module.
    *)

End ReceiptIntegrity.
