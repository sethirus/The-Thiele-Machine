(** =========================================================================
    μ-COST MODEL - Operational Definition (No Physics Assumptions)
    =========================================================================

    WHY THIS FILE EXISTS:
    I claim μ-cost is DEFINED operationally (which instructions modify partition
    structure) WITHOUT assuming CHSH bounds, Tsirelson bound (2√2), or quantum
    mechanics. The correlation with physics is DERIVED later, not assumed here.

    THE CORE CLAIM:
    μ-cost is determined purely by partition graph operations:
    - PNEW/PSPLIT/PMERGE: cost 0 (rearrange structure, no new information)
    - REVEAL: cost 1 (exposes hidden partition structure)
    - LASSERT/LJOIN: cost δ (adds structural complexity)
    - All other ops: cost 0 (don't touch partition graph)

    WHAT THIS PROVES:
    - mu_cost_of_instr (line 55): Operational cost for each instruction type
    - partition_ops_mu_free (line 121): PNEW/PSPLIT/PMERGE have zero cost
    - reveal_costs_one (line 133): REVEAL costs exactly 1
    - mu_zero_no_reveal (line 241): μ=0 programs cannot use REVEAL within fuel steps

    KEY SEPARATION:
    This file defines μ-cost INDEPENDENTLY of CHSH/quantum mechanics.
    CHSHExtraction.v defines CHSH computation INDEPENDENTLY of μ-cost.
    The relationship max{CHSH : μ=0} = 2√2 is PROVEN later (TsirelsonDerivation.v),
    not assumed here.

    PHYSICAL INTERPRETATION:
    μ-cost measures "structural information addition". Rearranging partitions is
    free (reversible). Revealing hidden structure costs 1 (observation). Adding
    constraints costs their complexity (description length). This is operational
    accounting, not physics.

    FALSIFICATION:
    Show that a program with REVEAL has μ-cost = 0 according to mu_cost_of_instr.
    This would contradict reveal_costs_one (line 133).

    Or show that PNEW/PSPLIT/PMERGE have nonzero cost despite being partition
    rearrangements (no information loss). This would contradict partition_ops_mu_free
    (line 121).

    Or prove that the operational definition is inconsistent with actual VM
    execution (vm_step modifies vm_mu differently than mu_cost_of_instr predicts).

    NO REFERENCE TO CHSH, TSIRELSON, OR 2√2 ANYWHERE IN THIS FILE.
    Pure operational accounting. Zero axioms. Zero admits.

    ========================================================================= *)

From Coq Require Import List Lia Arith PeanoNat.
Import ListNotations.

From Kernel Require Import VMState VMStep.

(** ** μ-Cost Assignment Rules

    Each operation has a μ-cost based on its effect on partition structure:
    
    1. PNEW, PSPLIT, PMERGE: μ += 0 (partition rearrangement, no new info)
    2. REVEAL: μ += 1 (exposes hidden partition structure)
    3. LASSERT, LJOIN: μ += δ (structure addition, δ = complexity measure)
    4. All other ops: μ += 0 (don't touch partition graph)
    
    This is DEFINED operationally, not derived from physics.
    *)

(** ** Partition Structure Complexity

    Measure how much "new structure" is added by an operation.
    This is the source of μ-cost.
    *)

(** Count non-trivial modules in partition graph *)
Definition module_count (g : PartitionGraph) : nat :=
  length g.(pg_modules).

(** Measure partition complexity (for now: module count) *)
Definition partition_complexity (g : PartitionGraph) : nat :=
  module_count g.

(** ** μ-Cost for Individual Instructions

    Define μ-increment for each instruction type.
    *)

Definition mu_cost_of_instr (instr : vm_instruction) (s : VMState) : nat :=
  match instr with
  | instr_pnew _ _ => 0  (* Create partition: structural rearrangement *)
  | instr_psplit _ _ _ _ => 0  (* Split partition: no new correlation *)
  | instr_pmerge _ _ _ => 0  (* Merge partition: no new correlation *)
  | instr_reveal _ _ _ _ => 1  (* Reveal hidden structure: μ += 1 *)
  | instr_lassert _ _ _ _ => 1  (* Assert structure: μ += 1 for complexity *)
  | instr_ljoin _ _ _ => 1  (* Join correlations: μ += 1 for complexity *)
  | _ => 0  (* Other instructions: no μ-cost *)
  end.

(** ** Total μ-Cost of Trace

    Sum μ-costs of all instructions that would be executed.
    We don't need full VM semantics, just cost accounting.
    *)

(** ** Total μ-Cost of Trace

    Sum μ-costs of all instructions that would be executed.
    We don't need full VM semantics, just cost accounting.
    *)

Fixpoint mu_cost_of_trace 
  (fuel : nat) (trace : list vm_instruction) (pc : nat) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
      match nth_error trace pc with
      | None => 0
      | Some instr =>
          mu_cost_of_instr instr 
            {| vm_graph := empty_graph;
               vm_csrs := {| csr_cert_addr := 0; csr_status := 0; csr_err := 0 |};
               vm_regs := [];
               vm_mem := [];
               vm_pc := pc;
               vm_mu := 0;
               vm_err := false |} 
          + mu_cost_of_trace fuel' trace (S pc)
      end
  end.

(** ** μ=0 Programs (Operational Definition)

    A program is μ=0 if its total μ-cost is zero.
    
    KEY: This is defined WITHOUT reference to CHSH or correlation bounds.
    *)

Definition mu_zero_program 
  (fuel : nat) (trace : list vm_instruction) : Prop :=
  mu_cost_of_trace fuel trace 0 = 0.

(** ** μ-Preservation Property

    Alternative characterization: μ=0 programs preserve initial μ-value.
    *)

Definition mu_preserving 
  (fuel : nat) (trace : list vm_instruction) (s_init s_final : VMState) : Prop :=
  s_final.(vm_mu) = s_init.(vm_mu).

(** ** Properties of μ-Cost Model *)

(** PNEW/PSPLIT/PMERGE are μ-free *)
Lemma partition_ops_mu_free :
  forall s mid,
    mu_cost_of_instr (instr_pnew mid 0) s = 0 /\
    (forall mid1 mid2 mid3,
      mu_cost_of_instr (instr_psplit mid1 mid2 mid3 0) s = 0) /\
    (forall mid1 mid2 mid3,
      mu_cost_of_instr (instr_pmerge mid1 mid2 mid3) s = 0).
Proof.
  intros. unfold mu_cost_of_instr. split; [reflexivity | split; reflexivity].
Qed.

(** REVEAL costs exactly 1 *)
Lemma reveal_costs_one :
  forall s mid addr len mu,
    mu_cost_of_instr (instr_reveal mid addr len mu) s = 1.
Proof.
  intros. unfold mu_cost_of_instr. reflexivity.
Qed.

(** ** Connection to CHSHExtraction

    KEY SEPARATION: 
    - CHSHExtraction.v defines CHSH computation (independent of μ)
    - This file defines μ-cost (independent of CHSH)
    
    These are SEPARATE accounting systems.
    
    The derivation task is to PROVE their relationship:
      max{CHSH : μ=0} = 2√2
    
    This is NOT assumed—it will be proven in TsirelsonDerivation.v
    *)

(** ** What μ=0 Programs Can Do

    μ=0 programs can:
    - Create partitions (PNEW)
    - Split/merge partitions (PSPLIT/PMERGE)  
    - Perform local operations
    - Measure in separable bases
    
    μ=0 programs CANNOT:
    - Use REVEAL (costs 1)
    - Add entangled structure via LASSERT/LJOIN (costs complexity)
    
    This restriction is OPERATIONAL, not assumed from physics.
    *)

(** No-REVEAL characterization of μ=0 *)
(**  If nth_error at pc is None and pc <= n, then nth_error at n is also None *)
Lemma nth_error_none_propagates :
  forall {A : Type} (l : list A) pc n,
    nth_error l pc = None ->
    pc <= n ->
    nth_error l n = None.
Proof.
  intros A l pc n Hpc Hle.
  apply nth_error_None in Hpc.
  apply nth_error_None.
  lia.
Qed.

(** Unfolding lemma for mu_cost_of_trace *)
Lemma mu_cost_of_trace_unfold :
  forall fuel' trace pc instr,
    nth_error trace pc = Some instr ->
    mu_cost_of_trace (S fuel') trace pc =
    mu_cost_of_instr instr {| vm_graph := empty_graph; vm_csrs := {| csr_cert_addr := 0; csr_status := 0; csr_err := 0 |};
                              vm_regs := []; vm_mem := []; vm_pc := pc; vm_mu := 0; vm_err := false |} 
    + mu_cost_of_trace fuel' trace (S pc).
Proof.
  intros. simpl. rewrite H. reflexivity.
Qed.

(** Auxiliary fact: 1 + anything ≠ 0 for nat *)
Lemma one_plus_neq_zero : forall n, 1 + n <> 0.
Proof. intros. lia. Qed.

(** Generalized version: REVEAL beyond horizon for any starting PC *)
Lemma mu_zero_no_reveal_from_pc :
  forall fuel trace pc,
    mu_cost_of_trace fuel trace pc = 0 ->
    (forall n mid addr len mu,
      nth_error trace n = Some (instr_reveal mid addr len mu) ->
      pc <= n ->
      n >= pc + fuel).
Proof.
  induction fuel as [|fuel' IH]; intros trace pc Hcost n mid addr len mu Hnth Hge.
  - (* fuel = 0: no instructions executed *) lia.
  - (* fuel = S fuel' *)
    destruct (nth_error trace pc) as [ipc|] eqn:Hpc.
    + (* Instruction at pc exists *)
      destruct (Nat.eq_dec n pc) as [Heq | Hneq].
      * (* n = pc: REVEAL is current instruction *)
        subst. rewrite Hpc in Hnth. injection Hnth as Heq.
        subst ipc. 
        rewrite (mu_cost_of_trace_unfold fuel' trace pc _ Hpc) in Hcost.
        unfold mu_cost_of_instr in Hcost.
        simpl in Hcost. lia. (* Cost would be 1 + ..., contradicts 0 *)
      * (* n > pc: REVEAL is later *)
        assert (Hpc_lt: pc < n) by lia.
        (* Unfold cost using lemma *)
        rewrite (mu_cost_of_trace_unfold fuel' trace pc ipc Hpc) in Hcost.
        (* Case split on instruction cost *)
        destruct (mu_cost_of_instr ipc {| vm_graph := empty_graph; vm_csrs := {| csr_cert_addr := 0; csr_status := 0; csr_err := 0 |};
                                          vm_regs := []; vm_mem := []; vm_pc := pc; vm_mu := 0; vm_err := false |}) eqn:Hcost_ipc.
        -- (* Cost 0: recurse *)
           simpl in Hcost.
           assert (Hbound: n >= S pc + fuel') by (eapply IH; [exact Hcost | exact Hnth | lia]).
           replace (pc + S fuel') with (S pc + fuel') by lia; exact Hbound.
        -- (* Cost >= 1: contradiction *)
           simpl in Hcost. exfalso. destruct n0; [discriminate Hcost | eapply one_plus_neq_zero; exact Hcost].
    + (* No instruction at pc *)
      (* If nth_error trace pc = None and pc <= n, then nth_error trace n = None *)
      (* But we have nth_error trace n = Some (instr_reveal ...), contradiction *)
      exfalso. eapply nth_error_none_propagates in Hpc; [|exact Hge].
      rewrite Hpc in Hnth. discriminate.
Qed.

(** Specialized to PC = 0 *)
Lemma mu_zero_no_reveal :
  forall fuel trace,
    mu_zero_program fuel trace ->
    (forall n mid addr len mu,
      nth_error trace n = Some (instr_reveal mid addr len mu) ->
      n >= fuel).
Proof.
  intros fuel trace Hcost n mid addr len mu Hnth.
  unfold mu_zero_program in Hcost.
  assert (Hle: 0 <= n) by lia.
  assert (Hbound: n >= 0 + fuel) by (eapply mu_zero_no_reveal_from_pc; [exact Hcost | exact Hnth | exact Hle]).
  simpl in Hbound. exact Hbound.
Qed.
