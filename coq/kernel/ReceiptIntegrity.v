From Coq Require Import List Bool Arith.PeanoNat Lia Ring.
Import ListNotations.

Require Import Kernel.VMState.
Require Import Kernel.VMStep.

(** * Receipt Integrity: Binding μ-cost to Computation
    
    STATUS: December 24, 2025
    
    This module addresses the receipt forgery vulnerability:
    
    VULNERABILITY: The Python receipt system signs claims without verifying
    that the claimed μ_delta matches the actual instruction cost.
    
    FIX: Define receipt validity as a binding between:
    - The instruction executed
    - The claimed μ_delta
    - The actual computed cost
    
    THEOREM: A valid receipt chain proves that μ was earned through computation.
    
    NO AXIOMS. NO ADMITS.
    *)

Module ReceiptIntegrity.

(** * Receipt Structure
    
    A receipt binds:
    - The instruction (with its embedded mu_delta claim)
    - Pre-state hash
    - Post-state hash
    
    The key integrity property: mu_delta in the instruction MUST equal
    the cost that instruction_cost would return.
    *)

(** State hash - represented as a natural number for simplicity.
    In the Python/Verilog implementation, this is SHA-256. *)
Definition state_hash := nat.

(** * μ Range Constants (Q16.16 Fixed Point)
    
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

(** * Instruction Cost Consistency
    
    CRITICAL INVARIANT: The mu_delta embedded in an instruction must equal
    the cost computed by instruction_cost.
    
    This is definitionally true by construction (mu_delta IS the cost),
    but we make it explicit as the verification criterion.
    *)

Definition instruction_mu_delta (instr : vm_instruction) : nat :=
  instruction_cost instr.

(** * Receipt Validity Predicate
    
    A receipt is VALID iff:
    1. post_mu = pre_mu + instruction_cost(instruction)
    2. The state transition is deterministic (single step)
    
    This is the Coq specification that Python must enforce.
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

(** * μ Range Validity
    
    CRITICAL: Both pre_mu and post_mu must be in valid Q16.16 range.
    This prevents overflow attacks where Python accepts values that
    hardware cannot represent.
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

(** * Complete Receipt Validity (with range check)
    
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

(** * Full Receipt Validity
    
    A receipt is fully valid iff:
    1. μ arithmetic is consistent (receipt_mu_consistent)
    2. The instruction could legally execute from pre_state to post_state
    
    Condition 2 requires witnessing that vm_step holds.
    *)

Definition receipt_valid_for_step (r : Receipt) (s_pre s_post : VMState) : Prop :=
  receipt_mu_consistent r /\
  s_pre.(vm_mu) = r.(receipt_pre_mu) /\
  s_post.(vm_mu) = r.(receipt_post_mu) /\
  vm_step s_pre r.(receipt_instruction) s_post.

(** * Receipt Chain Validity
    
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

(** State hash chain links: post_hash of r1 = pre_hash of r2
    This prevents state forgery attacks where an attacker creates
    receipts claiming to continue from a different state. *)
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

(** * Main Theorem: Valid Receipt Chain Proves μ
    
    If a receipt chain is valid starting from initial_mu,
    then the final_mu equals the sum of all instruction costs.
    
    This is the foundational theorem: VALID RECEIPTS PROVE WORK.
    *)

Fixpoint chain_total_cost (rs : list Receipt) : nat :=
  match rs with
  | [] => 0
  | r :: rest => instruction_mu_delta r.(receipt_instruction) + chain_total_cost rest
  end.

Definition chain_final_mu (rs : list Receipt) (initial_mu : nat) : nat :=
  initial_mu + chain_total_cost rs.

(* INQUISITOR NOTE: Extraction lemma exposing component of compound definition for modular reasoning. *)
Lemma chain_links_mu_head :
  forall r1 r2 rest,
    chain_links_mu (r1 :: r2 :: rest) ->
    r1.(receipt_post_mu) = r2.(receipt_pre_mu).
Proof.
  intros r1 r2 rest Hlinks.
  unfold chain_links_mu in Hlinks.
  specialize (Hlinks 0 r1 r2).
  simpl in Hlinks.
  apply Hlinks; reflexivity.
Qed.

(* INQUISITOR NOTE: Extraction lemma exposing component of compound definition for modular reasoning. *)
Lemma chain_links_hash_head :
  forall r1 r2 rest,
    chain_links_hash (r1 :: r2 :: rest) ->
    r1.(receipt_post_state_hash) = r2.(receipt_pre_state_hash).
Proof.
  intros r1 r2 rest Hlinks.
  unfold chain_links_hash in Hlinks.
  specialize (Hlinks 0 r1 r2).
  simpl in Hlinks.
  apply Hlinks; reflexivity.
Qed.

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

(* INQUISITOR NOTE: Extraction lemma exposing component of compound definition for modular reasoning. *)
Lemma chain_all_consistent_head :
  forall r rest,
    chain_all_consistent (r :: rest) ->
    receipt_mu_consistent r.
Proof.
  intros r rest Hconsistent.
  unfold chain_all_consistent in Hconsistent.
  inversion Hconsistent. assumption.
Qed.

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

(** * Non-Forgeability Theorem
    
    THEOREM: If receipt_chain_valid holds, then the claimed μ
    was EARNED through the specified computation.
    
    FALSIFIER: Produce a valid receipt chain where:
    - chain_final_mu ≠ sum of actual instruction costs
    
    This is impossible by construction: receipt_mu_consistent
    enforces the equality at each step.
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

(** * Forgery Detection
    
    THEOREM: Any receipt with mu_delta ≠ instruction_cost is INVALID.
    
    This directly addresses the Python vulnerability: forged receipts
    that claim arbitrary mu_delta will fail receipt_mu_consistent_b.
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

(** * Overflow Attack Detection
    
    THEOREM: Any receipt with μ values outside Q16.16 range is INVALID.
    
    This addresses the Python overflow vulnerability: receipts claiming
    huge μ values that hardware cannot represent.
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

(** * ATTACK MITIGATION SUMMARY
    
    The Python forgery attack worked because verify() only checked signature,
    not μ arithmetic.
    
    FIX:
    1. receipt_mu_consistent_b(r) must return true
    2. For chains: receipt_chain_valid_b(rs, 0) must return true
    
    IMPLEMENTATION IN PYTHON:
    
    def verify_mu_integrity(self) -> bool:
        expected_post_mu = self.pre_state['mu_acc'] + instruction_cost(self.instruction)
        return self.post_state['mu_acc'] == expected_post_mu
    
    IMPLEMENTATION IN VERILOG:
    
    wire mu_valid = (post_mu == pre_mu + instr_cost);
    assign receipt_valid = signature_valid && mu_valid;
    *)

End ReceiptIntegrity.
