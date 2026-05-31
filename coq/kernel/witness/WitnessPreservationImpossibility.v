(** WitnessPreservationImpossibility: No classical function can decide certification

    ThieleTraceProjection.v shows that distinct Thiele states project to the
    same classical snapshot. This file draws the consequence: the witness
    structure and certification status CANNOT be recovered from the classical
    projection. Any encoding that preserves certification must carry information
    that is not present in the classical view.

    TWO THEOREMS:

    1. no_classical_certification_decider
       There is no function from ClassicalTraces to booleans that correctly
       decides whether the originating Thiele trace was certified.
       (Classical information is provably insufficient.)

    2. certification_sound_encoding_not_classical
       Any encoding enc : VMState → list bool that is "certification-sound"
       (it distinguishes certified from uncertified states) cannot factor
       through the classical projection. In other words: the encoding must
       explicitly carry information that the classical projection drops.
       This is the formal "information cannot be recovered for free" theorem.

    WHAT THIS IS NOT:
    This is not a complexity result. It does not say that certified behavior
    is hard to compute — it says the information required to decide it is
    not present in the classical projection at all.

*)

From Coq Require Import List Bool Arith.PeanoNat.
Import ListNotations.

From Kernel Require Import VMState.
From Kernel Require Import ThieleTraceProjection.

(** ** I.  A third witness: same classical view, opposite certification *)

(** trace_witness_C: UNCERTIFIED state with the SAME classical fields
    as trace_witness_A (same pc=10, mu=5, regs, mem).

    This is the key witness: A is certified, C is not, but their
    classical projections are identical. *)
Definition trace_witness_C : VMState :=
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
     vm_certified := false |}.  (* <--- differs from A *)

(** project_state A = project_state C  (same classical fields). *)
Lemma project_A_eq_C :
  project_state trace_witness_A = project_state trace_witness_C.
Proof. reflexivity. Qed.

(** A and C differ in certification status. *)
Lemma cert_A_ne_cert_C :
  trace_witness_A.(vm_certified) <> trace_witness_C.(vm_certified).
Proof. discriminate. Qed.

(** ** II.  The certification decider and its domain                 *)

(** A default state for the empty-trace case. *)
Definition default_vmstate : VMState :=
  {| vm_graph     := empty_graph;
     vm_csrs      := example_csr;
     vm_regs      := [];
     vm_mem       := [];
     vm_pc        := 0;
     vm_mu        := 0;
     vm_mu_tensor := [];
     vm_err       := false;
     vm_logic_acc := 0;
     vm_mstatus   := 0;
     vm_witness   := witness_counts_zero;
     vm_certified := false |}.

(** last_state: the final state of a Thiele trace. *)
Definition last_state (t : ThieleTrace) : VMState :=
  List.last t default_vmstate.

(** certification_decider: read the vm_certified bit of the final state.
    This is the ground-truth certification status of a trace. *)
Definition certification_decider (t : ThieleTrace) : bool :=
  (last_state t).(vm_certified).

Lemma cert_decider_A : certification_decider [trace_witness_A] = true.
Proof. reflexivity. Qed.

Lemma cert_decider_C : certification_decider [trace_witness_C] = false.
Proof. reflexivity. Qed.

(** The two traces are classically identical. *)
Lemma proj_trace_A_eq_C :
  project_trace [trace_witness_A] = project_trace [trace_witness_C].
Proof.
  simpl.
  rewrite project_A_eq_C.
  reflexivity.
Qed.

(** ** III.  Theorem 1: No classical certification decider           *)

(** There is no function f : ClassicalTrace → bool such that
    f (project_trace t) = certification_decider t for all Thiele traces t.

    Proof idea: suppose such f exists. Apply it to [trace_witness_A] and
    [trace_witness_C]. Both have the same classical trace (by proj_trace_A_eq_C),
    so f gives the same boolean for both. But certification_decider gives true
    for A and false for C. Contradiction. *)
Theorem no_classical_certification_decider :
  ~ exists f : ClassicalTrace -> bool,
      forall t : ThieleTrace,
        f (project_trace t) = certification_decider t.
Proof.
  intros [f Hf].
  (* Apply the hypothesis to both witnesses *)
  pose proof (Hf [trace_witness_A]) as HA.
  pose proof (Hf [trace_witness_C]) as HC.
  (* Rewrite using the shared classical trace *)
  rewrite proj_trace_A_eq_C in HA.
  (* Now HA : f (project_trace [C]) = certification_decider [A] = true *)
  (* And  HC : f (project_trace [C]) = certification_decider [C] = false *)
  rewrite cert_decider_A in HA.
  rewrite cert_decider_C in HC.
  (* HA : f ... = true   and   HC : f ... = false   — contradiction *)
  congruence.
Qed.

(** ** IV.  Theorem 2: Preservation impossibility for encodings      *)

(** certification_sound: an encoding that distinguishes certified states
    from uncertified states.

    Formally: if two states differ in vm_certified, their encodings differ.
    This is the minimal requirement for any encoding that "preserves
    certification semantics." *)
Definition certification_sound (enc : VMState -> list bool) : Prop :=
  forall s1 s2 : VMState,
    s1.(vm_certified) <> s2.(vm_certified) ->
    enc s1 <> enc s2.

(** factors_classically: the encoding depends only on classical fields.

    Formally: enc factors through project_state — there exists a function
    on ClassicalSnapshots that produces the same result as enc. *)
Definition factors_classically (enc : VMState -> list bool) : Prop :=
  exists f : ClassicalSnapshot -> list bool,
    forall s : VMState, enc s = f (project_state s).

(** Any certification-sound encoding cannot factor through the classical
    projection — it must carry bits the classical projection drops.

    That is the formal statement that there's no recovering certification
    information for free: any encoding supporting certification detection
    has to store extra information beyond pc/mu/regs/mem.

    Proof idea: suppose enc is certification-sound and factors classically
    through f. Then enc trace_witness_A = f (project_state A) and
         enc trace_witness_C = f (project_state C).
    Since project_state A = project_state C (project_A_eq_C),
    we get enc trace_witness_A = enc trace_witness_C.
    But A and C have different vm_certified (cert_A_ne_cert_C), so
    certification-soundness requires enc A ≠ enc C. Contradiction. *)
Theorem certification_sound_encoding_not_classical :
  forall enc : VMState -> list bool,
    certification_sound enc ->
    ~ factors_classically enc.
Proof.
  intros enc Hsound [f Hfactor].
  (* enc must distinguish A from C (different certification) *)
  assert (Hne : enc trace_witness_A <> enc trace_witness_C)
    by exact (Hsound _ _ cert_A_ne_cert_C).
  (* But enc factors classically *)
  rewrite (Hfactor trace_witness_A) in Hne.
  rewrite (Hfactor trace_witness_C) in Hne.
  (* The classical projections are equal *)
  rewrite project_A_eq_C in Hne.
  (* Therefore enc A = enc C — contradicting Hne *)
  exact (Hne eq_refl).
Qed.

(** Corollary: A stronger statement.
    There is no pair (classical_enc, decision_bit_extractor) that jointly
    certifies a classical snapshot as encoding certification status. *)
Corollary no_certification_preserving_classical_encoder :
  ~ exists (enc : VMState -> list bool)
           (read_cert_bit : ClassicalSnapshot -> bool),
      certification_sound enc /\
      factors_classically enc /\
      (forall s : VMState,
          read_cert_bit (project_state s) = s.(vm_certified)).
Proof.
  intros [enc [read_cert_bit [Hsound [Hfactor Hread]]]].
  (* enc is certification-sound and factors classically — impossible *)
  exact (certification_sound_encoding_not_classical enc Hsound Hfactor).
Qed.
