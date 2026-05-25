(**
    MuCostModel: operational μ-cost ledger.

    I define μ-cost by asking one concrete question: which instructions modify
    partition structure? This file does NOT assume CHSH bounds, the Tsirelson
    bound (2√2), or quantum mechanics. The physics bridge has to earn that
    connection later.

    μ-cost is determined here by the same operational ledger as VMStep:
    [instruction_cost].  Older versions used a one-unit abstraction for
    revelation-class operations; that hid the bit accounting.  This file now
    delegates to the actual cost table, including payload bits for EMIT and
    explicit bit counts for REVEAL/READ_PORT.

    mu_cost_of_instr: operational cost for each instruction type.
    partition_ops_mu_free: PNEW/PSPLIT/PMERGE with delta 0 have zero cost.
    REVEAL always costs at least 1 by the cost table for [mu_cost_of_instr].
    mu_zero_no_reveal: μ=0 programs cannot use REVEAL within fuel steps.

    This file defines μ-cost independently of CHSH/quantum mechanics.
    CHSHExtraction.v defines CHSH computation independently of μ-cost. The
    relationship between μ=0 traces and CHSH-style bounds belongs to the
    algebraic bridge files, not to this operational cost definition.

    This is just the operational accounting layer. It defines the ledger and
    leaves the stronger physics interpretation to later bridge files.

    To falsify: show a program with REVEAL has μ-cost = 0 (contradicts the
    REVEAL line in [mu_cost_of_instr]), or show PNEW/PSPLIT/PMERGE with
    delta 0 have nonzero cost (contradicts partition_ops_mu_free), or show
    this operational definition is inconsistent with actual VM execution.
    *)

From Coq Require Import List Lia Arith PeanoNat.
Import ListNotations.

From Kernel Require Import VMState VMStep.

(** ** μ-cost assignment rules

    Each operation pays according to the executable VM cost table:
    
    1. PNEW, PSPLIT, PMERGE: μ += delta; canonical zero-cost uses delta 0.
    2. EMIT: μ += payload_bit_length payload + S delta.
    3. REVEAL/READ_PORT: μ += bits + S delta.
    4. LASSERT: μ += flen * 8 + S delta.
    5. LJOIN/CERTIFY/MORPH_ASSERT: μ += S delta.
    6. Other local ops: μ += delta.
    
    This is defined operationally. Physical readings must be added elsewhere.
    *)

(** ** Partition structure complexity

    Count the partition structure an operation adds. Right now the measure is
    module count, so any stronger interpretation has to be proven elsewhere.
    *)

(** Count the modules in the partition graph. *)
Definition module_count (g : PartitionGraph) : nat :=
  length g.(pg_modules).

(** For now, partition complexity is exactly module count. *)
Definition partition_complexity (g : PartitionGraph) : nat :=
  module_count g.

(** ** μ-cost for individual instructions

    The match below is the accounting rule. If a constructor changes cost, the
    proofs below are the first things that should break.
    *)

Definition mu_cost_of_instr (instr : vm_instruction) (_s : VMState) : nat :=
  instruction_cost instr.

(** ** Total μ-cost of a trace

    Add the costs for the instructions reached by the program counter. This is
    only the ledger, not the full VM semantics.
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
               vm_csrs := {| csr_cert_addr := 0; csr_status := 0; csr_err := 0; csr_heap_base := 0 |};
               vm_regs := [];
               vm_mem := [];
               vm_pc := pc;
               vm_mu := 0;
               vm_mu_tensor := vm_mu_tensor_default;
               vm_err := false;
               vm_logic_acc := 0;
               vm_mstatus := 0;
               vm_witness := witness_counts_zero;
               vm_certified := false |}
          + mu_cost_of_trace fuel' trace (S pc)
      end
  end.

(** ** μ=0 programs

    A program is μ=0 if its total μ-cost is zero.
    
    This definition does NOT mention CHSH or correlation bounds.
    *)

Definition mu_zero_program 
  (fuel : nat) (trace : list vm_instruction) : Prop :=
  mu_cost_of_trace fuel trace 0 = 0.

(** ** μ-preservation

    This is the state-level version: final μ equals initial μ.
    *)

Definition mu_preserving 
  (fuel : nat) (trace : list vm_instruction) (s_init s_final : VMState) : Prop :=
  s_final.(vm_mu) = s_init.(vm_mu).

(** ** Properties of the μ ledger *)

(** PNEW, PSPLIT, and PMERGE cost zero by definition. *)
Lemma partition_ops_mu_free :
  forall s mid,
    mu_cost_of_instr (instr_pnew mid 0) s = 0 /\
    (forall mid1 mid2 mid3,
      mu_cost_of_instr (instr_psplit mid1 mid2 mid3 0) s = 0) /\
    (forall mid1 mid2 cost,
      cost = 0 ->
      mu_cost_of_instr (instr_pmerge mid1 mid2 cost) s = 0).
Proof.
  intros. unfold mu_cost_of_instr. split; [reflexivity | split; intros; subst; reflexivity].
Qed.

(* [mu_cost_of_instr (instr_reveal _ _ _ _) _] reduces to a closed nat that is
   at least [1] by the [Definition] table for [mu_cost_of_instr]. The
   standalone helper [reveal_cost_positive] had no callers and only restated
   that table entry; consumers can [unfold mu_cost_of_instr; simpl; lia]
   directly. *)

(** ** CHSH stays outside this file

    The separation is the point:
    - CHSHExtraction.v defines CHSH computation (independent of μ)
    - This file defines μ-cost (independent of CHSH)
    
    These are SEPARATE accounting systems.
    
    Any bridge theorem relating μ=0 traces to CHSH-style bounds must cite both
    systems explicitly. This file does not assume such a theorem.
    *)

(** ** What μ=0 programs can do

    μ=0 programs can:
    - Create partitions (PNEW)
    - Split/merge partitions (PSPLIT/PMERGE)  
    - Perform local operations
    - Execute other zero-cost local instructions represented by this ledger
    
    μ=0 programs CANNOT:
    - Use REVEAL (bits + S delta)
    - Use LASSERT/LJOIN/CERTIFY within the zero-cost prefix (each has an S delta floor)
    
    This restriction is OPERATIONAL, not assumed from physics.
    *)

(** If the trace is already empty at pc, every later lookup is empty too. *)
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

(** One-step unfold for [mu_cost_of_trace]. *)
Lemma mu_cost_of_trace_unfold :
  forall fuel' trace pc instr,
    nth_error trace pc = Some instr ->
    mu_cost_of_trace (S fuel') trace pc =
    mu_cost_of_instr instr {| vm_graph := empty_graph; vm_csrs := {| csr_cert_addr := 0; csr_status := 0; csr_err := 0; csr_heap_base := 0 |};
                              vm_regs := []; vm_mem := []; vm_pc := pc; vm_mu := 0; vm_mu_tensor := vm_mu_tensor_default; vm_err := false; vm_logic_acc := 0; vm_mstatus := 0; vm_witness := witness_counts_zero; vm_certified := false |}
    + mu_cost_of_trace fuel' trace (S pc).
Proof.
  intros. simpl. rewrite H. reflexivity.
Qed.

(** One plus any natural number is not zero. *)
Lemma one_plus_neq_zero : forall n, 1 + n <> 0.
Proof. intros. lia. Qed.

(** A μ=0 trace cannot execute REVEAL before the fuel runs out. *)
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
        destruct (mu_cost_of_instr ipc {| vm_graph := empty_graph; vm_csrs := {| csr_cert_addr := 0; csr_status := 0; csr_err := 0; csr_heap_base := 0 |};
                                          vm_regs := []; vm_mem := []; vm_pc := pc; vm_mu := 0; vm_mu_tensor := vm_mu_tensor_default; vm_err := false; vm_logic_acc := 0; vm_mstatus := 0; vm_witness := witness_counts_zero; vm_certified := false |}) eqn:Hcost_ipc.
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

(** The same no-REVEAL bound specialized to PC zero. *)
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
