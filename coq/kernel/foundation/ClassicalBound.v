(** ClassicalBound: a zero-cost VM trace whose tally reaches CHSH = 2.

  Local strategies top out at CHSH = 2. [MinorConstraints] proves the
  ceiling for factorizable boxes ([local_box_CHSH_bound]). This file
  supplies the other half: a concrete VM trace, every instruction charged
  zero, whose recorded tally has CHSH exactly 2 ([classical_bound_achieved]).
  Constructive proof: an actual executable trace that achieves it.

  The strategy is fixed and local. Alice answers a function of her setting
  and a shared bit; Bob answers a function of his. With the shared bit at
  zero both always answer 0, so every setting pair records "same", each
  correlator is 1, and S = 1 + 1 + 1 - 1 = 2.

  What this does not say. It does not say a zero-cost trace can never
  record a tally above 2. [CHSH_TRIAL] records whatever outcomes the
  program supplies, so a zero-cost trace can write any tally at all. The
  ceiling of 2 is about what local play earns, and the step that commits to
  a tally is the priced one.

  To break this file: find a nonzero mu_delta in [classical_achieving_trace],
  or run the VM and get a tally other than 2. *)

From Coq Require Import List QArith Qabs Lia.
Import ListNotations.
Local Open Scope Q_scope.

From Kernel Require Import VMState VMStep CHSHExtraction MuCostModel.
From Kernel Require Import SimulationProof CHSHStatisticalBridge.

(** classical_chsh_value: The target - exactly 2.
  Bell's classical bound (1964): local hidden variable models, where Alice's
  output depends only on (x, shared randomness) and Bob's only on
  (y, shared randomness), can achieve at most CHSH=2. This file shows that
  maximum is attainable.
*)
Definition classical_chsh_value : Q := 2%Q.

(** shared_random_bit: The classical correlation source.
  Alice and Bob share a random bit before the experiment: pure classical
  correlation, no μ-cost, no structural operations. There are 4 equivalent
  optimal strategies (one per shared bit value). I fix it to 0 to show one
  of them. The bit is fixed at the start; a(x, shared) and b(y, shared) are
  DETERMINISTIC functions from there. No entanglement, no spooky action.
*)
(* SAFE: shared_random_bit is intentionally zero for the deterministic classical scenario. *)

Definition shared_random_bit : nat := 0%nat.

(** alice_classical_output: Alice's deterministic strategy.
  LOCAL function: depends only on (x, shared), not on Bob's input y or
  output b. That's what "classical" means. With shared=0: x=0 → 0, x=1 → 0.
  This is one of the optimal deterministic strategies: if Alice and Bob both
  output 0 most of the time, they maximize E00, E01, E10 and minimize E11,
  giving S = E00 + E01 + E10 - E11 = 2. Factorizability: a depends only on
  (x, shared), not on y; Alice and Bob are statistically independent given
  the shared randomness.
*)
Definition alice_classical_output (x : nat) (shared : nat) : nat :=
  match x, shared with
  | 0%nat, 0%nat => 0%nat
  | 0%nat, 1%nat => 1%nat
  | 1%nat, 0%nat => 0%nat
  | 1%nat, 1%nat => 1%nat
  | _, _ => 0%nat
  end.

(** bob_classical_output: Bob's deterministic strategy.
  LOCAL function: depends only on (y, shared), not on Alice's input x.
  With shared=0: y=0 → 0, y=1 → 0. Mirrors Alice's strategy. Both output 0
  for both inputs when shared=0, so all four (x,y) pairs give matching outputs:
  E00 = E01 = E10 = E11 = +1 → S = 1+1+1-1 = 2. That's the classical bound. ✓
  b depends only on (y, shared), independent of Alice's side given shared.
*)
Definition bob_classical_output (y : nat) (shared : nat) : nat :=
  match y, shared with
  | 0%nat, 0%nat => 0%nat
  | 0%nat, 1%nat => 1%nat
  | 1%nat, 0%nat => 0%nat
  | 1%nat, 1%nat => 0%nat
  | _, _ => 0%nat
  end.

(** classical_achieving_trace: the executable witness.
    PNEW and PSPLIT set up two modules, then four CHSH_TRIAL steps record
    one trial per setting pair. Every instruction carries mu_delta = 0.
    The schedule charges these instructions exactly their mu_delta, so the
    trace costs nothing; that is a fact about the schedule, not a claim
    that recording outcomes is free in any physical sense.

    All four trials record (a = 0, b = 0), so every pair agrees:
    E00 = E01 = E10 = E11 = 1 and S = 1 + 1 + 1 - 1 = 2.
    [classical_trace_tally] checks that by running the VM.

    Execute this trace. Compute CHSH from the receipts. If it's not 2 or
    mu is not 0, the claim fails. The execution is deterministic; there is
    no randomness in the VM. *)
Definition classical_achieving_trace : list vm_instruction := [
  (* Step 1: Create partition structure *)
  instr_pnew [0%nat] 0%nat;                    (* Create module *)
  instr_psplit 0%nat [1%nat] [2%nat] 0%nat;    (* Split into modules for Alice/Bob *)

  (* Step 2: Run CHSH trials with classical strategy *)
  (* Each trial: x y a b mu_delta *)
  instr_chsh_trial 0%nat 0%nat (alice_classical_output 0%nat shared_random_bit) (bob_classical_output 0%nat shared_random_bit) 0%nat;
  instr_chsh_trial 0%nat 1%nat (alice_classical_output 0%nat shared_random_bit) (bob_classical_output 1%nat shared_random_bit) 0%nat;
  instr_chsh_trial 1%nat 0%nat (alice_classical_output 1%nat shared_random_bit) (bob_classical_output 0%nat shared_random_bit) 0%nat;
  instr_chsh_trial 1%nat 1%nat (alice_classical_output 1%nat shared_random_bit) (bob_classical_output 1%nat shared_random_bit) 0%nat
].

(** ** Initial State Setup *)

Definition init_state_for_classical : VMState :=
  {| vm_regs := repeat 0%nat 32;
     vm_mem := [];
     vm_csrs := {| csr_cert_addr := 0%nat; csr_status := 0%nat; csr_err := 0%nat; csr_heap_base := 0 |};
     vm_pc := 0%nat;
     vm_graph := empty_graph;
     vm_mu := 0%nat;
     vm_mu_tensor := vm_mu_tensor_default;
     vm_err := false;
     vm_logic_acc := 0;
     vm_mstatus := 0;
     vm_witness := witness_counts_zero;
     vm_certified := false |}.

(** classical_program_mu_zero: every instruction declares mu_delta = 0, so
    the summed charge is 0. *)
Lemma classical_program_mu_zero :
  mu_cost_of_trace 10 classical_achieving_trace 0 = 0%nat.
Proof.
  unfold mu_cost_of_trace.
  simpl. reflexivity.
Qed.

(** The tally the trace records, run instruction by instruction from the
    starting state. *)
Definition classical_final_state : VMState :=
  fold_left vm_apply classical_achieving_trace init_state_for_classical.

Lemma classical_trace_tally :
  chsh_stat_from_wc (vm_witness classical_final_state) == 2.
Proof. vm_compute. reflexivity. Qed.

(** classical_bound_achieved: a zero-cost trace whose recorded tally has
    CHSH exactly 2. *)
Theorem classical_bound_achieved :
  exists (fuel : nat) (trace : list vm_instruction),
    mu_cost_of_trace fuel trace 0 = 0%nat /\
    fuel = 10%nat /\ trace = classical_achieving_trace /\
    chsh_stat_from_wc (vm_witness (fold_left vm_apply trace init_state_for_classical)) == 2.
Proof.
  exists 10%nat, classical_achieving_trace.
  split; [apply classical_program_mu_zero |].
  split; [reflexivity |].
  split; [reflexivity | exact classical_trace_tally].
Qed.
