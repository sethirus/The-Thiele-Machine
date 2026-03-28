(** * ThieleTraceProjection: Formal projection from Thiele traces to classical traces

    WHY THIS FILE EXISTS:
    The Thiele Machine carries structure a classical Turing machine cannot see:
    witness counters, partition graphs, certification flags, CSR registers,
    and the mu-tensor. This file formalizes the forgetful map that drops all
    of that, projecting every Thiele state onto what a classical observer
    would record (pc, mu, registers, memory).

    THREE THEOREMS:

    1. projection_collapses_witness_structure
       Two VMStates that agree on pc/mu/regs/mem project identically,
       regardless of witness counters, partition graph, or certification bit.

    2. distinct_certified_traces_same_classical
       There exist two distinct certified Thiele traces (differing in witness
       counts) that produce identical classical traces under the projection.
       The projection is genuinely many-to-one.

    3. projection_not_injective (corollary)
       The forgetful map is not injective: different Thiele states are
       observationally indistinguishable to a classical observer.

    WHAT THIS IS NOT:
    This is not a claim about computational power (both models are
    Turing-complete). It is a claim about information structure: the
    Thiele machine carries richer state than classical computation, and
    that state is not recoverable from the classical projection.

    NO AXIOMS. NO ADMITS. All proofs are constructive.
*)

From Coq Require Import List Bool Arith.PeanoNat.
Import ListNotations.

From Kernel Require Import VMState.

(* ================================================================= *)
(** ** I.  Classical snapshot: what a Turing-style observer can see  *)
(* ================================================================= *)

(** A classical observer has access to the computational core only:
    the program counter, the mu-cost ledger, the register file, and
    the data memory.

    NOT in the classical view:
      - vm_graph      (partition graph — semantic, not syntactic)
      - vm_csrs       (control/status registers)
      - vm_mu_tensor  (per-module metric tensor)
      - vm_err        (error flag)
      - vm_logic_acc  (logic engine accumulator)
      - vm_mstatus    (machine mode)
      - vm_witness    (CHSH trial witness counters)
      - vm_certified  (state-based certification flag)  *)

Record ClassicalSnapshot := mkClassicalSnapshot {
  cs_pc   : nat;
  cs_mu   : nat;
  cs_regs : list nat;
  cs_mem  : list nat
}.

(* ================================================================= *)
(** ** II.  The forgetful projection                                 *)
(* ================================================================= *)

(** project_state: drop all Thiele-specific structure. *)
Definition project_state (s : VMState) : ClassicalSnapshot :=
  {| cs_pc   := s.(vm_pc);
     cs_mu   := s.(vm_mu);
     cs_regs := s.(vm_regs);
     cs_mem  := s.(vm_mem) |}.

(** A Thiele trace is a sequence of machine state snapshots.
    Its classical shadow is the pointwise projection. *)
Definition ThieleTrace    := list VMState.
Definition ClassicalTrace := list ClassicalSnapshot.

Definition project_trace (t : ThieleTrace) : ClassicalTrace :=
  List.map project_state t.

(* ================================================================= *)
(** ** III.  Theorem 1: Projection collapses witness structure       *)
(* ================================================================= *)

(** [projection_collapses_witness_structure]: formal specification.

    Two states that agree on all classical fields project identically,
    even if they differ arbitrarily in witness counters, partition
    graphs, certification bits, or any other Thiele-only state. *)
Theorem projection_collapses_witness_structure :
  forall s1 s2 : VMState,
    s1.(vm_pc)   = s2.(vm_pc)   ->
    s1.(vm_mu)   = s2.(vm_mu)   ->
    s1.(vm_regs) = s2.(vm_regs) ->
    s1.(vm_mem)  = s2.(vm_mem)  ->
    project_state s1 = project_state s2.
Proof.
  intros s1 s2 Hpc Hmu Hregs Hmem.
  unfold project_state.
  f_equal; assumption.
Qed.

(** Lifted to traces: pointwise classical agreement implies trace equality. *)
Lemma project_trace_pointwise :
  forall t1 t2 : ThieleTrace,
    List.length t1 = List.length t2 ->
    (forall i s1 s2,
        nth_error t1 i = Some s1 ->
        nth_error t2 i = Some s2 ->
        project_state s1 = project_state s2) ->
    project_trace t1 = project_trace t2.
Proof.
  intros t1.
  induction t1 as [| s1 t1' IH]; intros t2 Hlen Hagree.
  - simpl in Hlen.
    symmetry in Hlen.
    apply length_zero_iff_nil in Hlen.
    subst. reflexivity.
  - destruct t2 as [| s2 t2'].
    + simpl in Hlen. discriminate.
    + simpl in Hlen. injection Hlen as Hlen'.
      simpl. f_equal.
      * exact (Hagree 0 s1 s2 eq_refl eq_refl).
      * apply IH; [exact Hlen' |].
        intros i si1 si2 Hi1 Hi2.
        exact (Hagree (S i) si1 si2 Hi1 Hi2).
Qed.

(* ================================================================= *)
(** ** IV.  Constructive witnesses for non-injectivity               *)
(* ================================================================= *)

Definition example_csr : CSRState :=
  {| csr_cert_addr := 0; csr_status := 0; csr_err := 0; csr_heap_base := 0 |}.

(** trace_witness_A: certified state with CHSH witness counters
    (wc_same_00 = 3, wc_diff_00 = 1). *)
Definition trace_witness_A : VMState :=
  {| vm_graph     := empty_graph;
     vm_csrs      := example_csr;
     vm_regs      := [42; 0; 0; 0];
     vm_mem       := [0; 0; 0; 0];
     vm_pc        := 10;
     vm_mu        := 5;
     vm_mu_tensor := vm_mu_tensor_default;
     vm_err       := false;
     vm_logic_acc := 0;
     vm_mstatus   := 0;
     vm_witness   := {| wc_same_00 := 3; wc_diff_00 := 1;
                        wc_same_01 := 0; wc_diff_01 := 0;
                        wc_same_10 := 0; wc_diff_10 := 0;
                        wc_same_11 := 0; wc_diff_11 := 0 |};
     vm_certified := true |}.

(** trace_witness_B: certified state with DIFFERENT witness counters
    (wc_same_00 = 5, wc_diff_00 = 2), but identical classical fields. *)
Definition trace_witness_B : VMState :=
  {| vm_graph     := empty_graph;
     vm_csrs      := example_csr;
     vm_regs      := [42; 0; 0; 0];
     vm_mem       := [0; 0; 0; 0];
     vm_pc        := 10;
     vm_mu        := 5;
     vm_mu_tensor := vm_mu_tensor_default;
     vm_err       := false;
     vm_logic_acc := 0;
     vm_mstatus   := 0;
     vm_witness   := {| wc_same_00 := 5; wc_diff_00 := 2;
                        wc_same_01 := 0; wc_diff_01 := 0;
                        wc_same_10 := 0; wc_diff_10 := 0;
                        wc_same_11 := 0; wc_diff_11 := 0 |};
     vm_certified := true |}.

(** Observable function that reads wc_same_00 — this distinguishes A from B. *)
Definition read_wc_same_00 (s : VMState) : nat :=
  wc_same_00 (vm_witness s).

(* INQUISITOR NOTE: Base lemma — computational normalization. *)
Lemma read_wc_A : read_wc_same_00 trace_witness_A = 3.
Proof. reflexivity. Qed.

(* INQUISITOR NOTE: Base lemma — computational normalization. *)
Lemma read_wc_B : read_wc_same_00 trace_witness_B = 5.
Proof. reflexivity. Qed.

(** trace_witness_A and trace_witness_B are distinct states. *)
Lemma witnesses_A_B_distinct : trace_witness_A <> trace_witness_B.
Proof.
  intro Heq.
  assert (H : read_wc_same_00 trace_witness_A = read_wc_same_00 trace_witness_B)
    by (rewrite Heq; reflexivity).
  rewrite read_wc_A, read_wc_B in H.
  discriminate.
Qed.

(** [project_A_eq_B]: formal specification.
    Despite distinct witness counters, A and B project identically. *)
Lemma project_A_eq_B :
  project_state trace_witness_A = project_state trace_witness_B.
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** V.  Theorem 2: Distinct certified traces, same classical trace *)
(* ================================================================= *)

(** [distinct_certified_traces_same_classical]: formal specification.

    The projection is genuinely many-to-one on certified traces.
    The two witnesses carry different CHSH trial histories (different
    quantum witness evidence) but are indistinguishable to a classical
    observer. *)
Theorem distinct_certified_traces_same_classical :
  exists t1 t2 : ThieleTrace,
    t1 <> t2 /\
    (forall s, In s t1 -> s.(vm_certified) = true) /\
    (forall s, In s t2 -> s.(vm_certified) = true) /\
    project_trace t1 = project_trace t2.
Proof.
  exists [trace_witness_A], [trace_witness_B].
  refine (conj _ (conj _ (conj _ _))).
  - (* t1 <> t2: the witness states are distinct *)
    intro Heq.
    apply witnesses_A_B_distinct.
    congruence.
  - (* all states in t1 are certified *)
    intros s Hs.
    apply List.in_inv in Hs.
    destruct Hs as [Heq | Hnil].
    + rewrite <- Heq. reflexivity.
    + exfalso; exact Hnil.
  - (* all states in t2 are certified *)
    intros s Hs.
    apply List.in_inv in Hs.
    destruct Hs as [Heq | Hnil].
    + rewrite <- Heq. reflexivity.
    + exfalso; exact Hnil.
  - (* project_trace t1 = project_trace t2 *)
    simpl.
    rewrite project_A_eq_B.
    reflexivity.
Qed.

(** [projection_not_injective]: formal specification.

    The forgetful map from Thiele states to classical snapshots is not
    injective. Structurally distinct Thiele states can be classically
    indistinguishable. *)
Corollary projection_not_injective :
  exists s1 s2 : VMState,
    s1 <> s2 /\
    project_state s1 = project_state s2.
Proof.
  exists trace_witness_A, trace_witness_B.
  exact (conj witnesses_A_B_distinct project_A_eq_B).
Qed.
