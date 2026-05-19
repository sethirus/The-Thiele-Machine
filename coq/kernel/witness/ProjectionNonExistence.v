(** ProjectionNonExistence: structural fields are not derivable functions of
    the bare classical projection.

    Status of this file
    -------------------
    [BlindnessRepresentation.v] establishes that [forget : VMState -> TMSnapshot]
    has multi-element fibers and exhibits witness pairs where Thiele-only fields
    (vm_certified, vm_witness, vm_csrs) differ even though the forget images
    agree.  Those are EXISTENCE statements (there exist two such states).

    This file flips them into NON-EXISTENCE statements about functions: no
    function on the bare classical projection can recover the dropped fields.
    The corollaries package these as the three "Turing-equivalent signatures
    cannot host this Thiele content" statements the monograph relies on:

    (A) The A2 axiom (cert-flip costs at least 1) cannot be stated as a
        constraint that quantifies over the bare projection alone: the
        cs_cert : cs_state -> bool field that A2 references is irrecoverable
        from forget.

    (B) The cost-ledger observability separation (two states with identical
        bare-classical observables but different mu) is not a theorem of any
        predicate language whose terms only see (pc, regs, mem): mu is not a
        function of the bare classical observable.

    (C) The structural-axis undecidability diagonal lives on csr_cert_addr
        reachability.  csr_cert_addr is not a function of forget, so any
        predicate on TMSnapshot that purports to match the diagonal must
        already smuggle in the Thiele-only field.

    NONE OF THESE PROOFS ASSERT THAT TURING MACHINES CANNOT COMPUTE.  They
    assert that specific *statements* the Thiele substrate makes about its own
    cert/mu/cert_addr axis cannot be re-expressed as statements about the bare
    classical projection alone, because the projection's fibers collapse the
    distinctions those statements depend on.

    NO COQ AXIOMS.  NO ADMITS.  All proofs are constructive, using the witness
    pairs already established in [BlindnessRepresentation.v].
*)

From Coq Require Import List Bool Arith.PeanoNat.
Import ListNotations.

From Kernel Require Import VMState.
From Kernel Require Import ThieleTraceProjection.
From Kernel Require Import BlindnessRepresentation.

(** ** Section 1: a stricter projection that drops mu.

    [forget] keeps four fields including [vm_mu].  For the cost-ledger
    separation result, we need a projection that drops [vm_mu] too: the
    "bare TM observable" the standard complexity-theory cost model sees.
*)

Record BareTMObservable := mkBareTMObservable {
  bto_pc   : nat;
  bto_regs : list nat;
  bto_mem  : list nat
}.

Definition bare_observable (s : VMState) : BareTMObservable :=
  {| bto_pc   := s.(vm_pc);
     bto_regs := s.(vm_regs);
     bto_mem  := s.(vm_mem) |}.

(** Two Thiele states differing only in [vm_mu] have the same bare observable. *)
Definition mu_separation_witness_zero : VMState :=
  {| vm_graph     := empty_graph;
     vm_csrs      := example_csr;
     vm_regs      := [42; 0; 0; 0];
     vm_mem       := [0; 0; 0; 0];
     vm_pc        := 10;
     vm_mu        := 0;
     vm_mu_tensor := vm_mu_tensor_default;
     vm_err       := false;
     vm_logic_acc := 0;
     vm_mstatus   := 0;
     vm_witness   := witness_counts_zero;
     vm_certified := false |}.

Definition mu_separation_witness_one : VMState :=
  {| vm_graph     := empty_graph;
     vm_csrs      := example_csr;
     vm_regs      := [42; 0; 0; 0];
     vm_mem       := [0; 0; 0; 0];
     vm_pc        := 10;
     vm_mu        := 1;
     vm_mu_tensor := vm_mu_tensor_default;
     vm_err       := false;
     vm_logic_acc := 0;
     vm_mstatus   := 0;
     vm_witness   := witness_counts_zero;
     vm_certified := false |}.

Lemma mu_separation_bare_observable_agrees :
  bare_observable mu_separation_witness_zero
  = bare_observable mu_separation_witness_one.
Proof. reflexivity. Qed.

Lemma mu_separation_mu_differs :
  vm_mu mu_separation_witness_zero <> vm_mu mu_separation_witness_one.
Proof. simpl. discriminate. Qed.

(** Two Thiele states differing only in [csr_cert_addr] have the same forget. *)
Definition cert_addr_witness_zero : VMState :=
  {| vm_graph     := empty_graph;
     vm_csrs      := {| csr_cert_addr := 0;
                        csr_status    := 0;
                        csr_err       := 0;
                        csr_heap_base := 0 |};
     vm_regs      := [42; 0; 0; 0];
     vm_mem       := [0; 0; 0; 0];
     vm_pc        := 10;
     vm_mu        := 5;
     vm_mu_tensor := vm_mu_tensor_default;
     vm_err       := false;
     vm_logic_acc := 0;
     vm_mstatus   := 0;
     vm_witness   := witness_counts_zero;
     vm_certified := false |}.

Definition cert_addr_witness_one : VMState :=
  {| vm_graph     := empty_graph;
     vm_csrs      := {| csr_cert_addr := 1;
                        csr_status    := 0;
                        csr_err       := 0;
                        csr_heap_base := 0 |};
     vm_regs      := [42; 0; 0; 0];
     vm_mem       := [0; 0; 0; 0];
     vm_pc        := 10;
     vm_mu        := 5;
     vm_mu_tensor := vm_mu_tensor_default;
     vm_err       := false;
     vm_logic_acc := 0;
     vm_mstatus   := 0;
     vm_witness   := witness_counts_zero;
     vm_certified := false |}.

Lemma cert_addr_witnesses_forget_agree :
  forget cert_addr_witness_zero = forget cert_addr_witness_one.
Proof. reflexivity. Qed.

Lemma cert_addr_witnesses_cert_addr_differs :
  (vm_csrs cert_addr_witness_zero).(csr_cert_addr)
  <> (vm_csrs cert_addr_witness_one).(csr_cert_addr).
Proof. simpl. discriminate. Qed.

(** ** Section 2: the three field-irrecoverability theorems.

    These are the "no function on the projection recovers the dropped field"
    statements that ground the monograph's non-existence corollaries.
*)

(** *** Theorem 1: vm_certified is not a function of the forget image.

    There is no boolean-valued function on TMSnapshot that, when composed with
    forget, agrees with vm_certified on every VMState.
*)
Theorem cert_not_function_of_forget :
  ~ exists phi : TMSnapshot -> bool,
      forall s : VMState, phi (forget s) = s.(vm_certified).
Proof.
  intros [phi Hphi].
  (* trace_witness_A is certified, forget_witness_uncert is uncertified, *)
  (* and they share the same forget image.                                *)
  pose proof (Hphi trace_witness_A) as Hcert_A.
  pose proof (Hphi forget_witness_uncert) as Hcert_uncert.
  (* forget_witness_uncert and trace_witness_A have equal forget images. *)
  assert (Heq : forget trace_witness_A = forget forget_witness_uncert)
    by reflexivity.
  (* Hence phi takes the same value on both: *)
  rewrite Heq in Hcert_A.
  (* phi (forget forget_witness_uncert) is both true and false. *)
  rewrite Hcert_uncert in Hcert_A.
  (* Hcert_A : false = vm_certified trace_witness_A *)
  (* vm_certified trace_witness_A is true by direct inspection of the record. *)
  simpl in Hcert_A.
  discriminate Hcert_A.
Qed.

(** *** Theorem 2: vm_mu is not a function of the bare classical observable.

    There is no nat-valued function on BareTMObservable that, when composed
    with bare_observable, agrees with vm_mu on every VMState.

    This is the formal content of "the cost-ledger separation is not derivable
    in the projected model": mu-distinguishing predicates on the projected
    model do not exist.
*)
Theorem mu_not_function_of_bare_observable :
  ~ exists phi : BareTMObservable -> nat,
      forall s : VMState, phi (bare_observable s) = s.(vm_mu).
Proof.
  intros [phi Hphi].
  pose proof (Hphi mu_separation_witness_zero) as Hmu_zero.
  pose proof (Hphi mu_separation_witness_one)  as Hmu_one.
  rewrite mu_separation_bare_observable_agrees in Hmu_zero.
  rewrite Hmu_one in Hmu_zero.
  simpl in Hmu_zero.
  discriminate Hmu_zero.
Qed.

(** *** Theorem 3: csr_cert_addr is not a function of the forget image.

    The structural-axis diagonal lives on csr_cert_addr reachability.  The
    diagonal predicate cannot be re-expressed as a predicate on TMSnapshot
    because the field it references is not a function of the projection.
*)
Theorem cert_addr_not_function_of_forget :
  ~ exists phi : TMSnapshot -> nat,
      forall s : VMState, phi (forget s) = (vm_csrs s).(csr_cert_addr).
Proof.
  intros [phi Hphi].
  pose proof (Hphi cert_addr_witness_zero) as Hca_zero.
  pose proof (Hphi cert_addr_witness_one)  as Hca_one.
  rewrite cert_addr_witnesses_forget_agree in Hca_zero.
  rewrite Hca_one in Hca_zero.
  simpl in Hca_zero.
  discriminate Hca_zero.
Qed.

(** ** Section 3: the three non-existence corollaries the monograph names.

    Each corollary turns one of the field-irrecoverability theorems above into
    the monograph-grade "Turing-equivalent signature cannot host this Thiele
    content" statement: there is no way to phrase the Thiele-side predicate as
    a predicate that quantifies over the bare classical projection alone.

    These corollaries do NOT claim:
      - that A2 is unstatable in Coq (it is: see CertificationSystem in
        UniversalCertificationCost.v);
      - that no extended Turing model can satisfy A2 (it can: package the
        Turing state plus a cost simulator into a CertificationSystem record);
      - that Turing machines compute fewer functions (they do not; see
        thiele_simulates_turing in ProperSubsumption.v).

    They claim only the irrecoverability: when the cert/mu/cert_addr axes are
    projected away, the Thiele-side predicate cannot be reconstructed as a
    predicate on the surviving fields.
*)

(** *** Corollary A: no A2-content predicate lives on the bare projection.

    A2 is the constraint cs_cert s = false -> cs_cert (step s i) = true ->
    cost i >= 1.  It quantifies over a cert predicate on substrate states.  If
    we attempt to phrase that constraint with a cert predicate that is a
    function of the bare TM observable alone, the cert function cannot agree
    with vm_certified on Thiele states -- by [cert_not_function_of_forget].
*)
Corollary no_classical_a2_cert_predicate :
  forall phi : TMSnapshot -> bool,
    ~ (forall s : VMState, phi (forget s) = s.(vm_certified)).
Proof.
  intros phi Hphi.
  apply cert_not_function_of_forget.
  exists phi. exact Hphi.
Qed.

(** *** Corollary B: no mu-separation predicate lives on the bare projection.

    The cost-ledger separation says: there exist Thiele states with identical
    bare-classical observables but different mu values.  Any predicate on the
    bare projection that purports to detect that separation must be able to
    extract mu from the projection -- which is impossible by
    [mu_not_function_of_bare_observable].
*)
Corollary no_classical_mu_separation_predicate :
  forall phi : BareTMObservable -> nat,
    ~ (forall s : VMState, phi (bare_observable s) = s.(vm_mu)).
Proof.
  intros phi Hphi.
  apply mu_not_function_of_bare_observable.
  exists phi. exact Hphi.
Qed.

(** *** Corollary C: no cert_addr-reachability predicate lives on the bare projection.

    The structural-axis diagonal in StructuralUndecidability.v references the
    csr_cert_addr channel.  Any analog of that diagonal on TMSnapshot must
    extract csr_cert_addr from forget -- which is impossible by
    [cert_addr_not_function_of_forget].
*)
Corollary no_classical_cert_addr_predicate :
  forall phi : TMSnapshot -> nat,
    ~ (forall s : VMState, phi (forget s) = (vm_csrs s).(csr_cert_addr)).
Proof.
  intros phi Hphi.
  apply cert_addr_not_function_of_forget.
  exists phi. exact Hphi.
Qed.

(** ** Section 4: the combined non-existence statement.

    A single packaged theorem that names all three irrecoverabilities and the
    irrecoverable fields they pin down.  This is the form the monograph cites
    as "the Thiele content the bare projection structurally cannot carry."
*)

Theorem thiele_content_irrecoverable_from_bare_projection :
  (~ exists phi : TMSnapshot -> bool,
       forall s : VMState, phi (forget s) = s.(vm_certified))
  /\
  (~ exists phi : BareTMObservable -> nat,
       forall s : VMState, phi (bare_observable s) = s.(vm_mu))
  /\
  (~ exists phi : TMSnapshot -> nat,
       forall s : VMState, phi (forget s) = (vm_csrs s).(csr_cert_addr)).
Proof.
  split; [| split].
  - exact cert_not_function_of_forget.
  - exact mu_not_function_of_bare_observable.
  - exact cert_addr_not_function_of_forget.
Qed.
