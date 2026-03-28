(** * PrimeAxiom: State-based No Free Insight on the Kernel VM

    WHY THIS FILE EXISTS:
    No Free Insight is the central economic law of the Thiele Machine:
    certification cannot be obtained without paying mu-cost. This file
    proves that law directly on the kernel VM by case-splitting over all
    40 instructions.

    THE KEY THEOREM: vm_certified = true implies vm_mu > 0.

    This is the state-based formulation of No Free Insight:
    CERTIFY is the ONLY instruction that sets vm_certified to true,
    and it charges S delta_mu (at least 1). Therefore, reaching a
    certified state requires paying at least 1 unit of mu.

    The multi-step theorem kernel_certified_implies_positive_mu extends
    this to arbitrary-fuel execution via run_vm: starting uncertified
    with mu=0, if execution ever reaches vm_certified=true then mu > 0.

    FALSIFICATION:
    Add an instruction that sets vm_certified to true without charging
    at least S 0 = 1 unit of mu. The single_step theorem would then fail
    its case split, and the multi-step induction would collapse.
    Alternatively, find a run_vm trace that reaches certified=true with
    mu=0 -- this would directly contradict kernel_certified_implies_positive_mu.
*)

From Coq Require Import List Arith.PeanoNat Lia.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof.

(** vm_apply preserves vm_certified for all instructions except instr_certify. *)
Lemma vm_apply_certified :
  forall s instr,
    (vm_apply s instr).(vm_certified) =
    match instr with
    | instr_certify _ => true
    | _ => s.(vm_certified)
    end.
Proof.
  intros s instr.
  destruct instr; simpl;
  repeat match goal with
  | |- context [match ?x with _ => _ end] => destruct x
  end;
  simpl; unfold advance_state, advance_state_reveal,
    advance_state_rm, jump_state, jump_state_rm; simpl;
  reflexivity.
Qed.

(** vm_apply never decreases mu. *)
Lemma vm_apply_mu_nondecreasing :
  forall s instr,
    s.(vm_mu) <= (vm_apply s instr).(vm_mu).
Proof.
  intros s instr.
  destruct instr; simpl;
  repeat match goal with
  | |- context [match ?x with _ => _ end] => destruct x
  end;
  simpl; unfold advance_state, advance_state_reveal,
    advance_state_rm, jump_state, jump_state_rm, apply_cost; simpl;
  lia.
Qed.

(** run_vm never decreases mu. *)
Lemma run_vm_mu_nondecreasing :
  forall fuel program s,
    s.(vm_mu) <= (run_vm fuel program s).(vm_mu).
Proof.
  induction fuel as [|fuel' IH]; intros program s.
  - simpl. lia.
  - simpl. destruct (nth_error program (vm_pc s)) as [instr|].
    + specialize (IH program (vm_apply s instr)).
      pose proof (vm_apply_mu_nondecreasing s instr). lia.
    + lia.
Qed.

(** CERTIFY charges S delta_mu: the resulting mu equals old mu + S delta_mu. *)
Lemma certify_charges_positive :
  forall s delta_mu,
    (vm_apply s (instr_certify delta_mu)).(vm_mu) = s.(vm_mu) + S delta_mu.
Proof.
  intros s delta_mu. simpl. reflexivity.
Qed.

(** Single-step version: if we start uncertified with mu=0 and
    one instruction makes us certified, then mu > 0 afterward. *)
Theorem single_step_certified_implies_positive_mu :
  forall s instr,
    s.(vm_certified) = false ->
    s.(vm_mu) = 0 ->
    (vm_apply s instr).(vm_certified) = true ->
    0 < (vm_apply s instr).(vm_mu).
Proof.
  intros s instr Huncert Hmu0 Hcert.
  rewrite vm_apply_certified in Hcert.
  destruct instr; simpl in Hcert; try (rewrite Huncert in Hcert; discriminate).
  (* Only instr_certify n survives *)
  destruct s; simpl in *; subst; lia.
Qed.

(** Multi-step version over run_vm: if execution starts uncertified with mu=0
    and reaches a certified state, then mu > 0 at that point.

    Strategy: induction on fuel. At each step, either the instruction certifies
    (and we use single_step + monotonicity) or it doesn't (and we recurse).
    The key observation: non-certify instructions preserve vm_certified=false
    (by vm_apply_certified) and vm_mu >= 0 (all costs are nat). *)
Theorem kernel_certified_implies_positive_mu :
  forall fuel program s0,
    s0.(vm_certified) = false ->
    s0.(vm_mu) = 0 ->
    (run_vm fuel program s0).(vm_certified) = true ->
    0 < (run_vm fuel program s0).(vm_mu).
Proof.
  induction fuel as [|fuel' IH]; intros program s0 Huncert Hmu0 Hcert.
  - simpl in Hcert. rewrite Huncert in Hcert. discriminate.
  - simpl in *.
    destruct (nth_error program (vm_pc s0)) as [instr|] eqn:Hlook.
    + set (s1 := vm_apply s0 instr) in *.
      destruct (Bool.bool_dec s1.(vm_certified) true) as [Hcert1|Hcert1].
      * (* s1 is certified — single_step gives mu > 0, monotonicity gives final mu > 0 *)
        assert (Hmu1 : 0 < s1.(vm_mu)).
        { apply (single_step_certified_implies_positive_mu s0 instr Huncert Hmu0 Hcert1). }
        pose proof (run_vm_mu_nondecreasing fuel' program s1). lia.
      * (* s1 not certified — need s1.certified=false and s1.mu=0 for IH *)
        apply Bool.not_true_iff_false in Hcert1.
        assert (Hmu1 : s0.(vm_mu) <= s1.(vm_mu)).
        { unfold s1. apply vm_apply_mu_nondecreasing. }
        assert (Hmu1eq : s1.(vm_mu) = 0 \/ 0 < s1.(vm_mu)) by lia.
        destruct Hmu1eq as [Hmu1z | Hmu1pos].
        -- apply (IH program s1 Hcert1 Hmu1z Hcert).
        -- pose proof (run_vm_mu_nondecreasing fuel' program s1). lia.
    + rewrite Huncert in Hcert. discriminate.
Qed.
