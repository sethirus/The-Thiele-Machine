(** ProofCarryingVerifier: interactive proof-carrying verification against
    the interaction-escape kernel and the mu hierarchy floor.

    Proof-carrying code and interactive/ZK protocols both replace "trust the
    bare transcript" with "engage in rounds that carry the missing
    structure". This file casts the round structure as the kernel's
    interaction escape and prices the verification events it certifies.

    Core instantiations: [interactive_escape_succeeds] — transcripts
    extended with interaction rounds admit a sound, complete, unit-cost
    verifier for the mu-dependent claim. [level_k_certification_cost_floor]
    — level-k certification costs at least k mu in any proof system the
    kernel's trace semantics covers: k certification events cannot be had
    for fewer than k units.

    WHAT THE FLOOR BOUNDS, EXACTLY: certification events. It does not bound
    gate counts, SNARK verifier circuit size, prover time, or proof length.
    A succinct verifier compresses everything except the number of
    certification commitments it makes.

    FALSIFIER: a level-k certified trace with total mu cost < k — its Coq
    construction breaks [level_k_certification_cost_floor]; or a sound and
    complete zero-round bare verifier, which breaks the escape's premise via
    [bare_setting_no_sound_complete_verifier].

    This file does not model zero-knowledge (the hiding property), soundness
    amplification, or any specific proof system's encoding. *)

From Coq Require Import List Arith.PeanoNat Lia Bool.
Import ListNotations.

Require Import VerifierModel.
Require Import VerifierImpossibility.
Require Import VerifierEscape_Interaction.
From Kernel Require Import MuHierarchyTheorem.

(** Kernel state and cost vocabulary used by the statements below: [vm_mu]
    lives in [VMState]; [init_state] and [trace_mu_cost] anchor the
    hierarchy floor in Main 3. *)
From Kernel Require Import VMState MuInitiality MuComplexity.

(* ====================================================================== *)
(** * Vocabulary

    Three terms of proof-carrying-code / interactive-proof jargon, glossed
    once so the development reads plainly.

    ROUND.  One challenge/response exchange between verifier and prover.
    The kernel's interaction model ([VerifierEscape_Interaction]) is the
    minimal one: a single round with a fixed challenge ("declare your μ"),
    so a round's content is one nat. The rounds are the interaction that
    carries the missing structure — exactly the structure the classical
    projection of the run discards.

    PCC CERTIFICATE.  In proof-carrying code, the producer ships a proof
    object alongside the code, and the consumer checks the proof instead
    of re-deriving the property. Here the certificate IS the transcript
    enrichment: the prover's round response, carried next to the classical
    run log. Checking it is one unit of work; re-deriving μ from the bare
    log is impossible at any cost (Main 2).

    PROOF SCRIPT.  In Main 3, the prover's instruction trace — the run
    that earns a certification entitlement, whose μ-ledger the hierarchy
    floor prices. *)

(* ====================================================================== *)
(** * The proof-carrying transcript

    A bare transcript is the classical observation log of the prover's
    run — what a consumer who only watches execution would see. A
    proof-carrying transcript pairs that log with the carried
    certificate. The wrapper is a record rather than a raw pair so the
    two components keep their roles: [pcc_run] is what a re-executing
    consumer could reproduce, [pcc_certificate] is what only the prover
    can supply. *)

Record ProofCarryingTranscript := mk_pcc_transcript {
  pcc_run         : BareTranscript;  (** the classical run log *)
  pcc_certificate : nat              (** the carried proof object: the
                                         prover's round response *)
}.

(** Projection into the kernel's interaction model: a proof-carrying
    transcript presents its certificate as the round response. *)
Definition pcc_rounds (p : ProofCarryingTranscript) : InteractiveTranscript :=
  (pcc_run p, pcc_certificate p).

(** Stripping the rounds: forgetting the certificate lands exactly in the
    bare setting of [VerifierModel] — the setting of Main 2. *)
Definition pcc_strip (p : ProofCarryingTranscript) : BareTranscript :=
  pcc_run p.

(** Lifting: attach a certificate to a bare run log. *)
Definition pcc_attach (t : BareTranscript) (cert : nat)
  : ProofCarryingTranscript :=
  mk_pcc_transcript t cert.

(** Lift/projection round trips: the wrapper adds the certificate and
    nothing else. [pcc_rounds] after [pcc_attach] recovers the kernel's
    interactive transcript on the nose, and stripping an attached
    certificate recovers the bare log. *)
Lemma pcc_rounds_attach :
  forall (t : BareTranscript) (cert : nat),
    pcc_rounds (pcc_attach t cert) = (t, cert).
Proof. reflexivity. Qed.

Lemma pcc_attach_rounds :
  forall p : ProofCarryingTranscript,
    pcc_attach (pcc_run p) (pcc_certificate p) = p.
Proof. intros [t cert]. reflexivity. Qed.

Lemma pcc_strip_attach :
  forall (t : BareTranscript) (cert : nat),
    pcc_strip (pcc_attach t cert) = t.
Proof. reflexivity. Qed.

(** Honest explanation across the wrapper: state [s] explains the
    proof-carrying transcript [p] when it explains [p]'s rounds in the
    kernel's sense — the carried certificate equals the state's actual μ.
    This is the PCC honesty condition: the shipped proof object is about
    the run it ships with. *)
Definition pcc_explains (s : VMState) (p : ProofCarryingTranscript) : Prop :=
  interactive_explains s (pcc_rounds p).

(** The lift lemma for explanations: any kernel-level interactive
    explanation transfers to the wrapper of its own components, so every
    interactive transcript the kernel reasons about is the image of a
    proof-carrying one. Together with [pcc_rounds_attach] this says the
    wrapper changes vocabulary, not content. *)
Lemma pcc_explains_lift :
  forall (s : VMState) (t : InteractiveTranscript),
    interactive_explains s t ->
    pcc_explains s (pcc_attach (fst t) (snd t)).
Proof.
  intros s [t r] H. exact H.
Qed.

(* ====================================================================== *)
(** * Why the certificate is the missing structure

    Two short structural facts that locate exactly what the enrichment
    buys. They are the semantic content behind Mains 1 and 2; neither is
    a headline on its own.

    First: the certificate pins μ. Any two states that honestly explain
    the same proof-carrying transcript agree on μ, because both must
    match the one carried certificate. *)
Lemma certificate_pins_mu :
  forall (s1 s2 : VMState) (p : ProofCarryingTranscript),
    pcc_explains s1 p ->
    pcc_explains s2 p ->
    vm_mu s1 = vm_mu s2.
Proof.
  intros s1 s2 p H1 H2.
  unfold pcc_explains, interactive_explains, honest_response in *.
  congruence.
Qed.

(** Second: the bare run log does not pin μ. The kernel's projection
    collision exhibits two states that explain the same bare transcript
    while disagreeing on μ — μ = 1 against μ = 0 on one shared log. This
    is the precise structure [pcc_certificate] restores, and the reason
    Main 2 cannot be escaped by reading the log harder. *)
Lemma bare_transcript_does_not_pin_mu :
  exists (s1 s2 : VMState) (t : BareTranscript),
    mu_collision_explains s1 t /\
    mu_collision_explains s2 t /\
    vm_mu s1 <> vm_mu s2.
Proof.
  exists NecessityOfMuLedger.po1_state_A,
         NecessityOfMuLedger.po1_state_B,
         NecessityOfMuLedger.po1_strict_trace_A.
  split; [| split].
  - exact witness_A_explains_shared.
  - exact witness_B_explains_shared.
  - rewrite NecessityOfMuLedger.po1_cond4_trace_A_mu_paid.
    rewrite NecessityOfMuLedger.po1_cond5_trace_B_mu_zero.
    discriminate.
Qed.

(* ====================================================================== *)
(** * Main 1: rounds make the μ-claim verifiable at unit cost.

    [proof_rounds_escape]: over proof-carrying transcripts there is a
    checker and a cost function such that the checker is sound (every
    honest explanation of an accepted transcript has μ = 1), complete
    (every honest μ = 1 run's transcript is accepted), and the cost is
    one unit on every transcript — the verifier checks the certificate,
    it does not re-run the code.

    HONESTY NOTE: this is the kernel's [interactive_escape_succeeds]
    instantiated through the wrapper — the witness checker reads only
    [pcc_certificate], via [pcc_rounds]. The contribution of the
    statement is the proof-carrying reading and its placement against
    Main 2; the mathematics of the escape is the kernel's.

    FALSIFICATION: a proof of the negation — no sound, complete,
    unit-cost checker over [ProofCarryingTranscript] — would contradict
    the witness constructed here, hence break
    [interactive_escape_succeeds] in the kernel. *)
Theorem proof_rounds_escape :
  exists (check : ProofCarryingTranscript -> bool)
         (check_cost : ProofCarryingTranscript -> nat),
    (forall p, check p = true ->
       forall s, pcc_explains s p -> vm_mu s = 1) /\
    (forall s p,
       vm_mu s = 1 ->
       pcc_explains s p ->
       check p = true) /\
    (forall p, check_cost p = 1).
Proof.
  destruct interactive_escape_succeeds as
    [decide [cost [Hsound [Hcomplete Hunit]]]].
  exists (fun p => decide (pcc_rounds p)),
         (fun p => cost (pcc_rounds p)).
  split; [| split].
  - intros p Haccept s Hexplain.
    exact (Hsound (pcc_rounds p) Haccept s Hexplain).
  - intros s p Hmu Hexplain.
    exact (Hcomplete s (pcc_rounds p) Hmu Hexplain).
  - intro p. exact (Hunit (pcc_rounds p)).
Qed.

(* ====================================================================== *)
(** * Main 2: with the rounds stripped, no verifier exists at any cost.

    [bare_pcc_impossible]: over bare transcripts — the image of
    [pcc_strip], the consumer who watches only the classical run log —
    no checker is simultaneously sound and complete for the same μ = 1
    claim, against the kernel's collision explanation relation. The cost
    function is quantified but unconstrained: the impossibility is not a
    budget statement, it holds for verifiers of unbounded cost, because
    the bare log does not determine μ ([bare_transcript_does_not_pin_mu]).

    HONESTY NOTE: the mathematical content is exactly the kernel's
    [bare_setting_no_sound_complete_verifier]; this proof only repacks
    the function pair into the kernel's [BareVerifier] record and applies
    that theorem. The statement exists so the bare and proof-carrying
    settings face each other in one vocabulary: same claim, same prover
    states, presence or absence of the carried certificate.

    FALSIFICATION: constructing such a checker pair in Coq would
    contradict [bare_setting_no_sound_complete_verifier] and with it the
    projection collision of the μ-ledger kernel. *)
Theorem bare_pcc_impossible :
  ~ exists (check : BareTranscript -> bool)
           (check_cost : BareTranscript -> nat),
      (forall t, check t = true ->
         forall s, mu_collision_explains s t -> vm_mu s = 1) /\
      (forall s t,
         vm_mu s = 1 ->
         mu_collision_explains s t ->
         check t = true).
Proof.
  intros [check [check_cost [Hsound Hcomplete]]].
  apply bare_setting_no_sound_complete_verifier.
  exists (mk_bv check check_cost).
  split.
  - exact Hsound.
  - exact Hcomplete.
Qed.

(* ====================================================================== *)
(** * Main 3: what level-k certification costs the prover.

    [certifies_k_claims k fuel proof_script] says the prover's run earns
    a level-k certification entitlement: executed under [fuel] steps from
    [init_state], the proof script ends certified and its executed
    instruction log contains a certification commitment of declared level
    at least k. This is definitionally the kernel's [level_k_certified];
    the alias exists so the floor below reads in proof-system vocabulary. *)
Definition certifies_k_claims (k fuel : nat) proof_script : Prop :=
  level_k_certified k fuel proof_script.

(** [level_k_verification_floor]: a run that earns a level-k
    certification entitlement pays at least k μ. Level-k certification
    events cannot be had for fewer than k units, in any proof system the
    kernel's trace semantics covers.

    WHAT THE FLOOR BOUNDS, EXACTLY: certification events — the μ-ledger
    total of the prover run whose executed log contains the level-k
    commitment. Each certification commitment is priced on the ledger,
    and the ledger sum cannot fall under the declared level.

    WHAT IT DOES NOT BOUND: gate counts, SNARK verifier circuit size,
    prover time, proof length. A succinct verifier may compress all of
    those — Main 1's checker runs at one unit regardless of the run it
    certifies. The only quantity the floor pins is the number of
    certification commitments paid for, and that is also the only
    quantity it needs: it is the part no compression touches.

    HONESTY NOTE: this is the kernel's
    [level_k_certification_cost_floor] by exact application, since
    [certifies_k_claims] is a definitional alias of [level_k_certified].

    FALSIFICATION: a Coq construction of a level-k certified proof
    script with total μ-cost below k breaks
    [level_k_certification_cost_floor] and the μ-hierarchy with it. *)
(* INQUISITOR NOTE: alias for level_k_certification_cost_floor — deliberate re-export pricing certification events in proof-system vocabulary; the tightness witness and pinning lemmas are this file's own content. *)
Theorem level_k_verification_floor :
  forall k fuel proof_script,
    certifies_k_claims k fuel proof_script ->
    trace_mu_cost fuel proof_script init_state >= k.
Proof.
  exact level_k_certification_cost_floor.
Qed.

(** The floor is tight, so Main 3 is not a vacuous bound: for every
    k >= 1 there is a proof script earning the level-k entitlement at
    cost exactly k — the kernel's one-instruction witness
    [certify_to_level], read here as the minimal honest prover. *)
Corollary level_k_verification_floor_tight :
  forall k, k >= 1 ->
    exists fuel proof_script,
      certifies_k_claims k fuel proof_script /\
      trace_mu_cost fuel proof_script init_state = k.
Proof.
  intros k Hk.
  exists 1, (certify_to_level k).
  split.
  - exact (certify_to_level_has_level k Hk).
  - exact (certify_to_level_cost k Hk).
Qed.

Print Assumptions proof_rounds_escape.
Print Assumptions bare_pcc_impossible.
Print Assumptions level_k_verification_floor.
Print Assumptions level_k_verification_floor_tight.
Print Assumptions certificate_pins_mu.
Print Assumptions bare_transcript_does_not_pin_mu.
