(** Executable access to the proposed program encoding.

    The round trip in VMSubstrateEncoded is an external Coq decoder. It does
    not imply that a VM program can read the encoded input. Every executable
    opcode commutes with replacement of vm_logic_acc, as does every run.

    Consequently no fixed VM program, started from vm_encode_concrete p,
    can report even p's final certification bit for every p through an output
    observation independent of the retained input accumulator. This includes
    outputs read from registers, memory, graph, PC, or certification fields.
    Reading the code and evaluating it in an external output decoder is a
    different contract. The result does not rule out a different executable
    encoding or an extended instruction set.
*)
From Coq Require Import List.
From Kernel Require Import VMState VMStep SimulationProof.
Definition with_logic_acc (s : VMState) (n : nat) : VMState :=
 {| vm_graph := s.(vm_graph); vm_csrs := s.(vm_csrs);
 vm_regs := s.(vm_regs); vm_mem := s.(vm_mem); vm_pc := s.(vm_pc);
 vm_mu := s.(vm_mu); vm_mu_tensor := s.(vm_mu_tensor); vm_err := s.(vm_err);
 vm_logic_acc := n; vm_mstatus := s.(vm_mstatus); vm_witness := s.(vm_witness);
 vm_certified := s.(vm_certified) |}.
Lemma vm_apply_logic_acc_commutes : forall s i n,
 vm_apply (with_logic_acc s n) i = with_logic_acc (vm_apply s i) n.
Proof.
 intros s i n. destruct i; cbn [vm_apply with_logic_acc]; try reflexivity.
 all: cbn [read_reg read_mem with_logic_acc vm_graph vm_csrs vm_regs vm_mem vm_pc vm_mu vm_mu_tensor vm_err vm_logic_acc vm_mstatus vm_witness vm_certified].
 all: repeat match goal with
 | |- context [match ?x with _ => _ end] => destruct x eqn:?; try reflexivity
 end.
 all: unfold read_reg, with_logic_acc in *; cbn in *; congruence.
Qed.

Lemma run_vm_logic_acc_commutes : forall fuel p s n,
 run_vm fuel p (with_logic_acc s n) = with_logic_acc (run_vm fuel p s) n.
Proof.
 induction fuel as [|fuel IH]; intros p s n; [reflexivity|].
 cbn [run_vm with_logic_acc vm_pc].
 destruct (nth_error p (vm_pc s)) as [i|] eqn:E; [|reflexivity].
 rewrite vm_apply_logic_acc_commutes. apply IH.
Qed.
From Kernel Require Import VMSubstrateEncoded VMUnboundedExec MuInitiality.
Import ListNotations.
Definition halts_observes (p : list vm_instruction) (s : VMState)
    (observe : VMState -> bool) (b : bool) : Prop :=
 exists fuel, halted p (run_vm fuel p s) /\ observe (run_vm fuel p s) = b.
Lemma halts_observes_logic : forall p s observe b n,
 (forall t v, observe (with_logic_acc t v) = observe t) ->
 (halts_observes p (with_logic_acc s n) observe b <-> halts_observes p s observe b).
Proof.
 intros p s observe b n H. unfold halts_observes.
 split; intros [fuel [Hhalt Hobs]]; exists fuel;
 rewrite run_vm_logic_acc_commutes in *; unfold halted in *;
 cbn [with_logic_acc vm_pc] in *; rewrite H in *; auto.
Qed.
Theorem no_logic_acc_encoded_interpreter : forall interpreter observe,
 (forall t v, observe (with_logic_acc t v) = observe t) ->
 ~ (forall p b,
    halts_observes interpreter (vm_encode_concrete p) observe b <->
    halts_observes p init_state vm_certified b).
Proof.
 intros interpreter observe Hobs Hspec.
 assert (Hyes : halts_observes [instr_certify 0] init_state vm_certified true).
 { exists 1. split; vm_compute; auto. }
 apply (proj2 (Hspec [instr_certify 0] true)) in Hyes.
 change (halts_observes interpreter
   (with_logic_acc init_state (VMInstructionEncoding.program_to_nat [instr_certify 0])) observe true) in Hyes.
 apply (proj1 (halts_observes_logic _ _ _ _ _ Hobs)) in Hyes.
 assert (Hnil : halts_observes interpreter (vm_encode_concrete []) observe true).
 { change (halts_observes interpreter
      (with_logic_acc init_state (VMInstructionEncoding.program_to_nat [])) observe true).
   apply (proj2 (halts_observes_logic _ _ _ _ _ Hobs)). exact Hyes. }
 apply (proj1 (Hspec [] true)) in Hnil.
 destruct Hnil as [fuel [_ Hbad]].
 destruct fuel; discriminate Hbad.
Qed.
