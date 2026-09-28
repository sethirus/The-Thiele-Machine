(** The adversarial search for the pointer-observable criterion: systems that
    resist forgery and do NOT proliferate records.

  PointerObservableReductions.v exhibits five deployed disciplines whose
  metered event is the unique pointer among its rivals. Five confirmations
  are not evidence for a universality claim on their own, because a criterion
  loose enough to accept anything accepts five things just as easily. What makes
  a universality class convincing is not the confirmations; it is the reported
  absence of exceptions after someone went looking. This file is the looking.

  THE PROTOCOL, FIXED BEFORE THE RESULTS BELOW.

  The claim under test is the pointer-observable criterion in the strong,
  falsifiable reading:

      (PO-STRONG)  Every system that must resist forgery of a commitment
                   has a commitment event that redundantly proliferates.

  A COUNTEREXAMPLE is a system meeting all three conditions:

    (C1) It must resist forgery of a commitment. Its designers treat
         producing an unearned commitment as the primary failure mode, and
         the system is engineered against it.
    (C2) It is deployed and independently evolved -- not built here, not
         built to make this point, and not derived from the Thiele machine.
    (C3) Its commitment event fails [redundantly_proliferating]: some
         independent observer cannot decide the event from its own fragment.

  A candidate that satisfies (C1) and (C2) but proliferates CONFIRMS
  (PO-STRONG). A candidate satisfying all three REFUTES it. This file
  reports both outcomes; nothing is filtered on the way to the conclusion.

  The candidate selection targets the opposite corner: forgery-resistant
  designs whose stated purpose suppresses third-party record-keeping. That is
  the relevant test class for the strong proliferation claim; deniable
  authentication is examined first because non-transferability is part of its
  stated design goal.

  THE RESULT, STATED UP FRONT. (PO-STRONG) is FALSE. Three candidates below
  refute it, and the refutation is not a modeling artifact: in each case the
  failure to proliferate is the design goal, not a gap. Two further candidates
  -- a public log and digital signatures -- confirm proliferation, so the
  search discriminates rather than only refuting.

  Digital signatures are the case that does the most work, because they
  confirm proliferation and refute METERING in the same breath: EUF-CMA is a
  forgery-resistance definition and signing carries no price at all. That
  splits two claims usually welded together, and the split is already a
  theorem here -- the substrate/hardness/interaction trichotomy, of which only
  the substrate branch meters. The five disciplines instantiate that one
  branch. All of this is laid out in the closing sections, which separate the
  surviving claim (M3) from the two that do not survive (M1, M2).

  Falsification of THIS file: show that a candidate below fails (C1) or (C2)
  -- i.e. that it does not really resist forgery, or that it is not really an
  independent design -- or that its formal model is unfaithful in a way that
  changes the proliferation verdict. That is a modeling dispute, and the
  honest place for it is prose, not Coq.
*)

(* SCOPE NOTE: standalone proof scope -- this file is a companion to
   PointerObservable.v and inherits its subject matter: it is about ecosystems
   and record proliferation, not about VM semantics, and it states no theorem
   mentioning VMState or vm_mu. The connection to the mu-ledger runs through
   PointerObservable.v, which this file imports and whose definitions every
   theorem here is stated in. *)

From Coq Require Import List Lia Bool.
Import ListNotations.

Require Import PointerObservable.

(** * A reusable non-proliferation lemma

    Every counterexample below has the same shape: some observer is,
    by design, unable to decide the commitment event. This lemma packages
    that argument once.

    If observer [i] is in range, its bit is down at some state where the
    event holds, then the event does not proliferate: observer [i] cannot
    record it.

    It is stated at a single witness state rather than requiring the fragment
    to be constantly false, which is the weaker and more useful hypothesis:
    one state where the event holds and the observer's bit is down is already
    enough to break the biconditional that [records] demands. *)
Lemma blind_observer_blocks_proliferation
  (eco : Ecosystem)
  (E : eco_state eco -> Prop)
  (i : nat)
  (s0 : eco_state eco) :
  (i < eco_observers eco)%nat ->
  eco_fragment eco i s0 = false ->
  E s0 ->
  ~ redundantly_proliferating eco E.
Proof.
  intros Hi Hblind HE Hprol.
  specialize (Hprol i Hi s0).
  destruct Hprol as [Hfwd _].
  specialize (Hfwd HE).
  rewrite Hblind in Hfwd.
  discriminate.
Qed.

(** * Candidate 1 -- Deniable (designated-verifier) authentication

    (C1) Forgery resistance: yes, and it is the whole point. Only a holder of
         the key can produce an authenticator the designated verifier
         accepts; producing one without the key is exactly the attack the
         scheme is built to stop.
    (C2) Independent: yes. Designated-verifier proofs and deniable
         authenticated key exchange (the OTR messaging family, and the
         deniability requirement in Signal's handshake) come from the
         cryptography and secure-messaging communities.

    The structural fact: the scheme is engineered so that a third party
    CANNOT be convinced, even given the whole transcript, because the
    designated verifier could have produced that transcript itself.
    Non-transferability is the product requirement. Third-party fragments
    are therefore constantly false -- not because the model is impoverished,
    but because the protocol works to make them so. *)

Module DeniableAuthentication.

Record DAState := {
  (** The message really was authenticated by the key holder. *)
  da_authentic : bool;
  (** The designated verifier's local acceptance bit. *)
  da_verifier_accepts : bool
}.

(** Three observers: the designated verifier (index 0) and two third parties
    (indices 1 and 2) who hold the transcript. The verifier's fragment
    decides authenticity; the third parties' fragments are constantly false,
    which is precisely the deniability guarantee. *)
Definition deniable : Ecosystem := {|
  eco_state := DAState;
  eco_observers := 3;
  eco_fragment := fun i s => if Nat.eqb i 0 then da_authentic s else false
|}.

Definition authentic_event (s : DAState) : Prop := da_authentic s = true.

(** The designated verifier does record the event. *)
(* SAFE: definitional by construction, and that is the point. In these minimal
   ecosystems the observers' fragment IS the event's indicator, so a
   confirmation reduces to reflexivity. Confirmations carry no proof content
   here; what they carry is the modelling claim that every observer sees the
   bit, which is argued in prose above and cannot be discharged in Coq. This
   is exactly why the file treats confirmations as weak and refutations as
   strong: a refutation exhibits a state the fragment gets wrong, which is a
   real obligation, while a confirmation restates the model. *)
Lemma deniable_verifier_records : records deniable authentic_event 0.
Proof. intro s. unfold authentic_event. simpl. reflexivity. Qed.

(** COUNTEREXAMPLE. The commitment event does not proliferate: a third party
    cannot decide it. The system satisfies (C1), (C2) and (C3). *)
Theorem deniable_authentication_refutes_strong_criterion :
  ~ redundantly_proliferating deniable authentic_event.
Proof.
  apply (blind_observer_blocks_proliferation
           deniable authentic_event 1
           {| da_authentic := true; da_verifier_accepts := true |}).
  - simpl. lia.
  - simpl. reflexivity.
  - unfold authentic_event. simpl. reflexivity.
Qed.

End DeniableAuthentication.

(** * Candidate 2 -- Symmetric-key message authentication (MAC)

    (C1) Forgery resistance: yes; existential unforgeability under chosen
         message attack is the defining security notion of a MAC.
    (C2) Independent: yes; symmetric authentication predates all of this and
         is standard practice.

    The structural fact: verification requires the shared secret. Exactly the
    parties holding the key can decide whether a tag is authentic; everyone
    else cannot, and no record reaches them. A MAC is forgery-resistant and
    conspicuously non-proliferating -- which is exactly why protocols that
    need third-party verifiability reach for signatures instead. That
    contrast is the criterion's real content, and it appears again in the
    boundary section below. *)

Module SymmetricMAC.

Record MACState := {
  mac_authentic : bool
}.

(** Three observers: two key holders (indices 0, 1) and one outsider
    (index 2) who sees the tag but has no key. *)
Definition mac : Ecosystem := {|
  eco_state := MACState;
  eco_observers := 3;
  eco_fragment := fun i s => if Nat.ltb i 2 then mac_authentic s else false
|}.

Definition mac_event (s : MACState) : Prop := mac_authentic s = true.

Theorem mac_refutes_strong_criterion :
  ~ redundantly_proliferating mac mac_event.
Proof.
  apply (blind_observer_blocks_proliferation
           mac mac_event 2 {| mac_authentic := true |}).
  - simpl. lia.
  - simpl. reflexivity.
  - unfold mac_event. simpl. reflexivity.
Qed.

End SymmetricMAC.

(** * Candidate 3 -- Object capabilities / unforgeable references

    (C1) Forgery resistance: yes, and it is unconditional rather than
         computational. In a memory-safe capability system a reference cannot
         be manufactured from thin air: unforgeability is enforced by the
         type system or the kernel, not by a cost and not by a hardness
         assumption.
    (C2) Independent: yes; the capability tradition (KeyKOS, EROS, E,
         seL4, WebAssembly's reference types) developed on its own.

    The structural fact, and the reason this candidate matters most: here
    forgery resistance is achieved with NO metering AT ALL and no record
    anywhere. Nobody pays, nobody logs, no observer outside the holder can
    tell whether a capability is held. If any single system shows that
    forgery resistance does not require a priced commitment event, it is
    this one. *)

Module ObjectCapability.

Record CapState := {
  cap_held : bool
}.

(** Three observers: the holder (index 0) and two other processes. Capability
    systems confine authority precisely so that other processes cannot
    observe or name what they do not hold. *)
Definition capability : Ecosystem := {|
  eco_state := CapState;
  eco_observers := 3;
  eco_fragment := fun i s => if Nat.eqb i 0 then cap_held s else false
|}.

Definition cap_event (s : CapState) : Prop := cap_held s = true.

Theorem capability_refutes_strong_criterion :
  ~ redundantly_proliferating capability cap_event.
Proof.
  apply (blind_observer_blocks_proliferation
           capability cap_event 1 {| cap_held := true |}).
  - simpl. lia.
  - simpl. reflexivity.
  - unfold cap_event. simpl. reflexivity.
Qed.

End ObjectCapability.

(** * Candidate 4 -- Public certificate transparency (control)

    This candidate is included as a CONTROL, to check that the search is
    capable of returning "confirms" and is not an instrument that only ever
    reports refutations. A criterion that everything violates is as useless
    as one that nothing violates.

    (C1) Forgery resistance: yes; an unlogged certificate is the failure mode
         the system exists to detect.
    (C2) Independent: yes; certificate transparency comes from the web PKI
         community.

    The structural fact: inclusion in the log is published to every mirror
    and auditor by design. Here proliferation is the product requirement, so
    every observer's fragment decides the event and the criterion holds. *)

Module PublicLog.

Record LogState := {
  log_included : bool;
  log_prover_effort : nat
}.

Definition public_log : Ecosystem := {|
  eco_state := LogState;
  eco_observers := 3;
  eco_fragment := fun _ s => log_included s
|}.

Definition inclusion_event (s : LogState) : Prop := log_included s = true.
Definition effort_event (s : LogState) : Prop := (1 <= log_prover_effort s)%nat.

(** CONFIRMS. The commitment event proliferates. *)
(* SAFE: definitional by construction, and that is the point. In these minimal
   ecosystems the observers' fragment IS the event's indicator, so a
   confirmation reduces to reflexivity. Confirmations carry no proof content
   here; what they carry is the modelling claim that every observer sees the
   bit, which is argued in prose above and cannot be discharged in Coq. This
   is exactly why the file treats confirmations as weak and refutations as
   strong: a refutation exhibits a state the fragment gets wrong, which is a
   real obligation, while a confirmation restates the model. *)
Theorem public_log_confirms :
  redundantly_proliferating public_log inclusion_event.
Proof.
  intros i Hi s. unfold inclusion_event. simpl. reflexivity.
Qed.

(** And the rival effort event does not, so the control discriminates rather
    than proliferating everything. *)
Theorem public_log_effort_not_proliferating :
  ~ redundantly_proliferating public_log effort_event.
Proof.
  apply (blind_observer_blocks_proliferation
           public_log effort_event 0
           {| log_included := false; log_prover_effort := 1 |}).
  - simpl. lia.
  - simpl. reflexivity.
  - unfold effort_event. simpl. lia.
Qed.

End PublicLog.

(** * Candidate 5 -- Digital signatures, and the case that separates two claims

    (C1) Forgery resistance: yes, and it is the textbook definition.
         Existential unforgeability under chosen-message attack (EUF-CMA) IS
         the security goal of a signature scheme; forging one is the attack.
    (C2) Independent: yes; signatures predate this development entirely and
         run in every TLS handshake, SSH session, and package install.

    This candidate matters because it splits two claims that the other four
    leave welded together. A signature is PUBLICLY verifiable: anyone holding
    the public key decides authenticity for themselves, so the commitment
    event proliferates, and the criterion confirms. But signing METERS
    NOTHING. There is no ledger, no stake, no gas, no cost floor; signing an
    Ed25519 message costs the signer well under a millisecond and no
    accounting of any kind. Forgery resistance here comes from a
    computational hardness assumption, not from a price on the commitment.

    So signatures confirm proliferation and refute metering in the same
    breath. Any claim of the form "resisting forgery forces a price" fails on
    them, and it fails on the most widely deployed forgery-resistant
    primitive there is. *)

Module DigitalSignature.

Record SigState := {
  sig_authentic : bool
}.

(** Three observers, all holding the public key. Public verifiability is the
    product requirement, so every fragment decides the event. *)
Definition signature : Ecosystem := {|
  eco_state := SigState;
  eco_observers := 3;
  eco_fragment := fun _ s => sig_authentic s
|}.

Definition sig_event (s : SigState) : Prop := sig_authentic s = true.

(** CONFIRMS proliferation. The metering question is separate, and prose is
    the honest place for it: nothing in this ecosystem is priced. *)
(* SAFE: definitional by construction, and that is the point. In these minimal
   ecosystems the observers' fragment IS the event's indicator, so a
   confirmation reduces to reflexivity. Confirmations carry no proof content
   here; what they carry is the modelling claim that every observer sees the
   bit, which is argued in prose above and cannot be discharged in Coq. This
   is exactly why the file treats confirmations as weak and refutations as
   strong: a refutation exhibits a state the fragment gets wrong, which is a
   real obligation, while a confirmation restates the model. *)
Theorem signature_confirms_proliferation :
  redundantly_proliferating signature sig_event.
Proof.
  intros i Hi s. unfold sig_event. simpl. reflexivity.
Qed.

End DigitalSignature.

(** * Three routes, and only one of them meters

    The reason signatures resist forgery without a price is already a theorem
    of this development, and it is worth stating here because it settles the
    scope question rather than arguing it.

    [VerifierEscape_Substrate.v], [VerifierEscape_Hardness.v] and
    [VerifierEscape_Interaction.v] establish three ways to obtain sound
    verification of a mu-sensitive claim: expose the structure in the
    substrate, lean on a computational hardness assumption, or interact.
    [hardness_escape_succeeds] exhibits the middle one explicitly -- a
    verifier that is weakly sound and costs 1, conditional on any hardness
    hypothesis.

    ONLY THE SUBSTRATE ROUTE METERS. Hardness buys forgery resistance from an
    assumption; interaction buys it from a challenge. Neither prices the
    commitment event.

    That reframes the five disciplines of PointerObservableReductions.v, and
    reframes them downward. They are not five instances of a law covering
    forgery resistance in general. They are five instances of ONE branch of a
    three-branch result this development already proved. Signatures occupy
    the second branch, and their existence is not an anomaly to be explained
    away -- it is what the trichotomy predicts.

    THE CLAIMS, SEPARATED. Three distinct statements travel together in loose
    prose and come apart under the candidates above:

      (M1) Forgery resistance forces metering.
           FALSE. Digital signatures (hardness route) and object capabilities
           (unconditional, via memory safety) both resist forgery at no
           price. Capabilities are the stronger refutation: no cost, no
           record, no assumption.

      (M2) Forgery resistance forces record proliferation.
           FALSE. Deniable authentication, symmetric MACs, and object
           capabilities all resist forgery while proliferating nothing, and
           in the first case non-proliferation is the product requirement.

      (M3) A commitment that must convince third parties who did not witness
           its creation will proliferate records.
           SURVIVES. Every candidate examined here is consistent with it:
           signatures, certificate transparency, and the five disciplines
           confirm; MACs, deniable authentication, and capabilities are all
           cases where third-party conviction is explicitly NOT required, so
           they do not bear on it.

    What is left of the metering claim, stated so it can be attacked: when a
    claim is mu-sensitive -- not decidable from the classical projection --
    and the verifier can neither recheck it directly nor substitute a
    hardness assumption, the substrate route is the available construction, and that route
    prices the commitment event. That is [V_does_not_factor_through_classical]
    in different clothes, it is narrower than "forgery resistance," and it is
    the version this development actually supports. *)

(** * The search, packaged

    One statement carrying every verdict, so the outcome can be cited without
    re-reading the file: three refutations, two confirmations. *)

Theorem adversarial_search_verdicts :
  (~ redundantly_proliferating
       DeniableAuthentication.deniable DeniableAuthentication.authentic_event)
  /\ (~ redundantly_proliferating
       SymmetricMAC.mac SymmetricMAC.mac_event)
  /\ (~ redundantly_proliferating
       ObjectCapability.capability ObjectCapability.cap_event)
  /\ redundantly_proliferating
       PublicLog.public_log PublicLog.inclusion_event
  /\ redundantly_proliferating
       DigitalSignature.signature DigitalSignature.sig_event
  (* And the deniable case is a genuine failure of proliferation rather than
     of recording: the designated verifier does decide the event. *)
  /\ records DeniableAuthentication.deniable
             DeniableAuthentication.authentic_event 0.
Proof.
  split; [ exact DeniableAuthentication.deniable_authentication_refutes_strong_criterion | ].
  split; [ exact SymmetricMAC.mac_refutes_strong_criterion | ].
  split; [ exact ObjectCapability.capability_refutes_strong_criterion | ].
  split; [ exact PublicLog.public_log_confirms | ].
  split; [ exact DigitalSignature.signature_confirms_proliferation
         | exact DeniableAuthentication.deniable_verifier_records ].
Qed.

(** Every verdict closes under the global context: no axioms of any kind,
    stdlib or otherwise. *)
Print Assumptions adversarial_search_verdicts.
Print Assumptions DeniableAuthentication.deniable_verifier_records.
Print Assumptions DeniableAuthentication.deniable_authentication_refutes_strong_criterion.
Print Assumptions SymmetricMAC.mac_refutes_strong_criterion.
Print Assumptions ObjectCapability.capability_refutes_strong_criterion.
Print Assumptions PublicLog.public_log_confirms.
Print Assumptions PublicLog.public_log_effort_not_proliferating.
Print Assumptions DigitalSignature.signature_confirms_proliferation.

(** * What the search found

    Three refutations and one confirmation. (PO-STRONG) -- "every system that
    must resist forgery has a proliferating commitment event" -- is FALSE,
    and the counterexamples are not marginal: deniable authentication,
    symmetric MACs, and object capabilities are load-bearing, widely deployed,
    and independently developed. In each, failure to proliferate is the
    engineering goal.

    The boundary the three counterexamples trace is sharp, and it is not the
    one (PO-STRONG) guessed at. Compare:

      - MAC vs. digital signature. Both resist forgery. The MAC does not
        proliferate; the signature does. The difference is not forgery
        resistance -- it is whether THIRD PARTIES must be convinced.
      - Deniable authentication vs. certificate transparency. Both resist
        forgery. Deniability actively prevents third-party conviction;
        transparency actively requires it.
      - Object capabilities vs. proof-carrying code. Both make unearned
        authority impossible. The capability confines it to the holder; the
        proof travels to every consumer.

    In every pair the proliferating member is the one whose commitment must
    convince parties who were not present. So the surviving criterion is:

      (PO-PUBLIC)  A system whose commitment must convince third parties who
                   did not witness its creation will proliferate records of
                   the commitment event.

    This is weaker than (PO-STRONG) and it is what the five disciplines in
    PointerObservableReductions.v actually instantiate -- every one of them
    is a public-verifiability system. Their agreement is now better
    understood: it is convergence across five designs that share the
    third-party-conviction requirement, which is a real and non-trivial
    class, rather than evidence about forgery resistance in general.

    Two consequences worth stating plainly, since they cut against the
    broader thesis and were found by looking for exactly that:

      1. Forgery resistance does NOT imply metering. Object capabilities
         achieve unforgeability with no cost, no ledger, and no record --
         unconditionally, not merely cheaply. Any claim that pricing is
         FORCED by the need to resist forgery is refuted by that single
         example.
      2. The five confirmations are evidence for (PO-PUBLIC), not for
         (PO-STRONG), and they should be cited that way.

    The honest summary: the search was run, it found counterexamples, the
    strong claim did not survive, and the weaker one that did is now stated
    where it can be attacked in turn. *)
