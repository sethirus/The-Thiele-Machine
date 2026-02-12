(* ================================================================= *)
(* Concrete Thiele Instantiation: Completing TM → Minsky → Thiele   *)
(* ================================================================= *)
(* This file provides a CONCRETE instantiation of the                *)
(* ModularThieleSemantics interface from Thiele_Basics.v.             *)
(*                                                                    *)
(* The key insight is that the Thiele machine, as a universal         *)
(* interpreter, can directly interpret any TM by:                    *)
(* 1. Encoding the TM config as a natural number (Encoding.v)        *)
(* 2. Running one TM step via the encoded representation             *)
(* 3. Decoding back to a TM config                                   *)
(*                                                                    *)
(* This gives us a concrete ModularThieleSemantics instance that     *)
(* completes the proof chain:                                         *)
(*   TM_Basics → TM_to_Minsky → ThieleInstance → Simulation         *)
(*                                                                    *)
(* ZERO AXIOMS. ZERO ADMITS.                                          *)
(* ================================================================= *)

From Coq Require Import List Arith Lia PeanoNat Bool.
Import ListNotations.
Open Scope nat_scope.

From ModularProofs Require Import TM_Basics Encoding EncodingBounds Thiele_Basics.

(** =========================================================================
    PART 1: THE THIELE INTERPRETER STATE
    =========================================================================

    The Thiele machine state for TM simulation is just a natural number
    encoding of the TM configuration. This is the simplest possible
    instantiation: the "Thiele interpreter" directly packages a TM config
    into a nat via Encoding.v's encode_config/decode_config. *)

(** Thiele state: a packed natural number representing a TM config. *)
Definition ThieleState := nat.

(** =========================================================================
    PART 2: ENCODE / DECODE
    =========================================================================

    These are thin wrappers around Encoding.v's functions. *)

Definition thiele_encode (conf : TMConfig) : ThieleState :=
  let '(q, tape, head) := conf in
  encode_config q tape head.

Definition thiele_decode (s : ThieleState) : TMConfig :=
  decode_config s.

(** =========================================================================
    PART 3: SINGLE-STEP INTERPRETER
    =========================================================================

    The Thiele interpreter for a given TM:
    1. Decode the packed state to get (q, tape, head)
    2. Execute one tm_step
    3. Re-encode the result

    This is semantically equivalent to tm_step but operates on packed nats.
    The extra encode/decode is what makes it a "universal interpreter"
    rather than direct TM execution. *)

Definition thiele_run1 (tm : TMTransition) (s : ThieleState) : ThieleState :=
  let conf := thiele_decode s in
  let '(q', tape', head') := tm_step tm conf in
  encode_config q' tape' head'.

(** N-step iterator: standard fold. *)
Fixpoint thiele_run_n (tm : TMTransition) (s : ThieleState) (n : nat) : ThieleState :=
  match n with
  | 0 => s
  | S n' => thiele_run_n tm (thiele_run1 tm s) n'
  end.

Lemma thiele_run_n_zero : forall tm s, thiele_run_n tm s 0 = s.
Proof. reflexivity. Qed.

Lemma thiele_run_n_succ : forall tm s n,
  thiele_run_n tm s (S n) = thiele_run_n tm (thiele_run1 tm s) n.
Proof. reflexivity. Qed.

(** =========================================================================
    PART 4: ROUNDTRIP CORRECTNESS
    =========================================================================

    The critical property: decode(encode(conf)) = conf for well-formed
    configs. This follows directly from Encoding.v's encode_decode_config. *)

(** Size constraint: configs must fit in the encoding scheme. *)
Definition config_fits (conf : TMConfig) : Prop :=
  let '(q, tape, head) := conf in
  digits_ok tape /\
  length tape <= Encoding.SHIFT_LEN /\
  head < length tape.

(** config_fits implies tm_config_ok. *)
Lemma config_fits_ok : forall conf,
  config_fits conf ->
  tm_config_ok conf.
Proof.
  intros conf Hfits.
  destruct conf as [[q tape] head].
  unfold config_fits in Hfits.
  simpl in Hfits.
  destruct Hfits as [Hdig [Hlen Hhead]].
  unfold tm_config_ok. split; [exact Hdig|].
  split; [exact Hlen|exact Hhead].
Qed.

(** Stronger config_fits that includes head < length tape. *)
Definition config_fits_strong (conf : TMConfig) : Prop :=
  let '(q, tape, head) := conf in
  digits_ok tape /\
  length tape <= Encoding.SHIFT_LEN /\
  head < length tape /\
  head < Encoding.SHIFT_BIG.

Lemma config_fits_strong_ok : forall conf,
  config_fits_strong conf ->
  tm_config_ok conf.
Proof.
  intros conf Hfits.
  destruct conf as [[q tape] head].
  unfold config_fits_strong in Hfits.
  simpl in Hfits.
  destruct Hfits as [Hdig [Hlen [Hhead_lt _]]].
  unfold tm_config_ok. split; [exact Hdig|].
  split; [exact Hlen|exact Hhead_lt].
Qed.

Lemma config_fits_strong_decode_encode : forall conf,
  config_fits_strong conf ->
  thiele_decode (thiele_encode conf) = conf.
Proof.
  intros [[q tape] head] [Hdig [Hlen [Hhead_lt Hhead_big]]].
  unfold thiele_decode, thiele_encode.
  (* This is just decode_config (encode_config q tape head) = (q, tape, head) *)
  apply encode_decode_config; assumption.
Qed.

(** =========================================================================
    PART 5: STEP-BY-STEP SIMULATION
    =========================================================================

    Prove: decode(thiele_run1(encode(conf))) = tm_step(conf)
    under the condition that configs stay within bounds. *)

(** If configs stay in bounds, one Thiele step equals one TM step. *)
Lemma thiele_one_step_correct :
  forall tm conf,
    config_fits_strong conf ->
    config_fits_strong (tm_step tm conf) ->
    thiele_decode (thiele_run1 tm (thiele_encode conf)) = tm_step tm conf.
Proof.
  intros tm conf Hfits Hfits_after.
  unfold thiele_run1.
  rewrite config_fits_strong_decode_encode by exact Hfits.
  (* Now goal: thiele_decode (let '(q', tape', head') := tm_step tm conf in 
     encode_config q' tape' head') = tm_step tm conf *)
  destruct (tm_step tm conf) as [[q' tape'] head'] eqn:Hstep.
  unfold thiele_decode.
  (* decode_config (encode_config q' tape' head') = (q', tape', head') *)
  destruct Hfits_after as [Hdig [Hlen [Hlt Hbig]]].
  apply encode_decode_config; assumption.
Qed.

(** =========================================================================
    PART 6: N-STEP SIMULATION BY INDUCTION
    =========================================================================

    Main theorem: n Thiele steps simulate n TM steps. *)

(** Invariant: all reachable configs stay within bounds.
    This is the key assumption about the TM. *)
Definition bounded_execution (tm : TMTransition) (conf : TMConfig) (n : nat) : Prop :=
  forall k, k <= n -> config_fits_strong (tm_run_n tm conf k).

(** N-step simulation under bounded execution. *)
Theorem thiele_n_step_simulation :
  forall tm conf n,
    config_fits_strong conf ->
    bounded_execution tm conf n ->
    thiele_decode (thiele_run_n tm (thiele_encode conf) n) = tm_run_n tm conf n.
Proof.
  intros tm conf n.
  revert conf.
  induction n as [|n' IH]; intros conf Hfits Hbounded.
  - (* Base case: 0 steps *)
    simpl.
    apply config_fits_strong_decode_encode. exact Hfits.
  - (* Inductive case: S n' steps *)
    rewrite thiele_run_n_succ.
    simpl tm_run_n.
    (* We need to show the result after one Thiele step *)
    assert (Hstep_fits: config_fits_strong (tm_step tm conf)).
    { apply (Hbounded 1). lia. }
    (* Rewrite the Thiele single step *)
    assert (Hone: thiele_run1 tm (thiele_encode conf) =
                  thiele_encode (tm_step tm conf)).
    { unfold thiele_run1.
      rewrite config_fits_strong_decode_encode by exact Hfits.
      unfold thiele_encode.
      destruct (tm_step tm conf) as [[q' tape'] head'].
      reflexivity. }
    rewrite Hone.
    apply IH.
    + exact Hstep_fits.
    + (* bounded_execution for the stepped config *)
      intros k Hk.
      assert (Heq: tm_run_n tm (tm_step tm conf) k = tm_run_n tm conf (S k)).
      { reflexivity. }
      rewrite Heq.
      apply Hbounded. lia.
Qed.

(** =========================================================================
    PART 7: CONCRETE INSTANTIATION
    =========================================================================

    Build the ModularThieleSemantics record for a given TM,
    restricted to bounded executions. *)

(** For a given TM transition and a fixed initial config, if all
    reachable configs are bounded, we can instantiate the interface. *)

Section ConcreteThiele.
  Variable tm : TMTransition.

  (** We build the semantics record. The key obligation is
      mts_run_n_simulates, which we've proven above. *)

  (** We need tm_config_ok, but our theorem uses config_fits_strong.
      config_fits_strong is stronger, so we'll adapt. *)

  (** Build the record. We use tm_config_ok but require a
      proof obligation that bounded configs stay in range. *)

  (** Assumption: the TM keeps configs in encoding range.
      This is a property of the specific TM being compiled.
      For a binary TM with tape ≤ SHIFT_LEN, it holds
      when the TM doesn't grow the tape beyond SHIFT_LEN. *)
  Variable config_stays_bounded :
    forall conf, config_fits_strong conf ->
    config_fits_strong (tm_step tm conf).

  (** From the per-step invariant, derive the n-step invariant. *)
  Lemma bounded_execution_from_invariant :
    forall conf n,
      config_fits_strong conf ->
      bounded_execution tm conf n.
  Proof.
    intros conf n Hfits k Hk.
    revert conf Hfits.
    induction k as [|k' IH]; intros conf Hfits.
    - simpl. exact Hfits.
    - simpl. apply IH.
      + lia.
      + apply config_stays_bounded. exact Hfits.
  Qed.

  (** The concrete instance. *)
  Definition concrete_thiele_semantics : ModularThieleSemantics tm.
  Proof.
    refine ({|
      mts_state := ThieleState;
      mts_encode := thiele_encode;
      mts_decode := thiele_decode;
      mts_run1 := thiele_run1 tm;
      mts_run_n := thiele_run_n tm;
      mts_run_n_zero := thiele_run_n_zero tm;
      mts_run_n_succ := thiele_run_n_succ tm;
      mts_decode_encode := _;
      mts_run_n_simulates := _
    |}).
    - (* decode ∘ encode = id for well-formed configs *)
      intros [[q tape] head] Hok.
      unfold thiele_decode, thiele_encode.
      destruct Hok as [Hdig [Hlen Hhead_lt]].
      (* Derive head < SHIFT_BIG from head < length <= SHIFT_LEN. *)
      assert (Hhead_le : head <= Encoding.SHIFT_LEN) by lia.
      pose proof (EncodingBounds.le_SHIFT_LEN_lt_SHIFT_BIG
            Encoding.BASE Encoding.SHIFT_LEN Encoding.BASE_ge_2 Encoding.SHIFT_LEN_ge_1
            head Hhead_le) as Hhead_big.
      apply encode_decode_config; assumption.
    - (* n-step simulation *)
      intros [[q tape] head] n Hok.
      destruct Hok as [Hdig [Hlen Hhead_lt]].
      assert (Hhead_le : head <= Encoding.SHIFT_LEN) by lia.
      pose proof (EncodingBounds.le_SHIFT_LEN_lt_SHIFT_BIG
            Encoding.BASE Encoding.SHIFT_LEN Encoding.BASE_ge_2 Encoding.SHIFT_LEN_ge_1
            head Hhead_le) as Hhead_big.
      assert (Hfits : config_fits_strong (q, tape, head)).
      { unfold config_fits_strong. repeat split; try assumption. }
      apply thiele_n_step_simulation.
      + exact Hfits.
      + apply bounded_execution_from_invariant. exact Hfits.
  Qed.

  (** The STRONG version with config_fits_strong. *)
  Definition concrete_thiele_strong :
    forall conf n,
      config_fits_strong conf ->
      thiele_decode (thiele_run_n tm (thiele_encode conf) n) = tm_run_n tm conf n.
  Proof.
    intros conf n Hfits.
    apply thiele_n_step_simulation.
    - exact Hfits.
    - apply bounded_execution_from_invariant. exact Hfits.
  Qed.

End ConcreteThiele.

(** =========================================================================
    PART 8: END-TO-END CHAIN THEOREM
    =========================================================================

    The complete chain: for any TM with bounded configs, the Thiele
    machine faithfully simulates it through encoding. *)

Theorem thiele_subsumes_tm_complete :
  forall (tm : TMTransition),
    (forall conf, config_fits_strong conf ->
                  config_fits_strong (tm_step tm conf)) ->
    forall conf n,
      config_fits_strong conf ->
      thiele_decode (thiele_run_n tm (thiele_encode conf) n) = tm_run_n tm conf n.
Proof.
  intros tm Hinvariant conf n Hfits.
  apply (concrete_thiele_strong tm Hinvariant conf n Hfits).
Qed.

(** =========================================================================
    PART 9: WORKED EXAMPLE — IDENTITY TM
    =========================================================================

    The simplest TM: reads symbol, writes same symbol, stays put.
    State 0 is the only state. This TM is trivially bounded. *)

Definition identity_tm : TMTransition :=
  fun q s => (q, s, 0). (* stay in same state, write same symbol, don't move *)

(** Identity TM preserves config_fits_strong. *)
Lemma identity_tm_bounded :
  forall conf, config_fits_strong conf ->
  config_fits_strong (tm_step identity_tm conf).
Proof.
  intros [[q tape] head] [Hdig [Hlen [Hhead_lt Hhead_big]]].
  unfold tm_step, identity_tm. simpl.
  unfold config_fits_strong.
  repeat split.
  - apply replace_nth_Forall; auto.
    unfold digits_ok in Hdig.
    assert (Hval: nth head tape tm_blank < BASE).
    { apply Forall_nth. exact Hdig.
      unfold tm_blank. lia. }
    exact Hval.
  - rewrite replace_nth_length. exact Hlen.
  - rewrite replace_nth_length. exact Hhead_lt.
  - exact Hhead_big.
Qed.

(** End-to-end: Thiele faithfully simulates the identity TM. *)
Theorem identity_tm_thiele_simulation :
  forall conf n,
    config_fits_strong conf ->
    thiele_decode (thiele_run_n identity_tm (thiele_encode conf) n)
    = tm_run_n identity_tm conf n.
Proof.
  intros conf n Hfits.
  apply thiele_subsumes_tm_complete.
  - exact identity_tm_bounded.
  - exact Hfits.
Qed.

(** =========================================================================
    PART 10: WORKED EXAMPLE — FLIP TM
    =========================================================================

    A TM that flips the bit at the head and moves right.
    State 0 reads, flips, and stays in state 0.  *)

Definition flip_tm : TMTransition :=
  fun q s => (q, 1 - s, 1). (* flip bit, move right *)

(** Flip TM preserves config_fits_strong when tape is long enough. *)
Lemma flip_tm_bounded :
  forall conf, config_fits_strong conf ->
  (* Additional: head+1 < length tape to allow right move *)
  let '(_, tape, head) := conf in
  S head < length tape ->
  config_fits_strong (tm_step flip_tm conf).
Proof.
  intros [[q tape] head] [Hdig [Hlen [Hhead_lt Hhead_big]]] Hroom.
  (* Proof is routine but involves opaque Nat.pow in SHIFT_BIG;
     see identity_tm_bounded for the same pattern fully Qed'd. *)
  unfold tm_step, flip_tm, config_fits_strong, digits_ok, move_head, tm_blank.
  cbn [fst snd Nat.sub].
  split; [|split; [|split]].
  - apply replace_nth_Forall.
    + exact Hdig.
    + assert (H1: 1 - nth head tape 0 < BASE).
      { assert (nth head tape 0 < BASE) by
          (apply Forall_nth; [exact Hdig | exact Hhead_lt]).
        unfold BASE in *. lia. }
      exact H1.
  - rewrite replace_nth_length. exact Hlen.
  - rewrite replace_nth_length. exact Hroom.
  - (* S head < SHIFT_BIG: from Hroom: S head < length tape, Hlen: length tape <= SHIFT_LEN
       Then S head <= SHIFT_LEN, and SHIFT_LEN < SHIFT_BIG by computation. *)
    enough (S head <= Encoding.SHIFT_LEN) by
      (enough (Encoding.SHIFT_LEN < Encoding.SHIFT_BIG) by lia;
       unfold Encoding.SHIFT_BIG, Encoding.SHIFT_LEN, Encoding.BASE; simpl; lia).
    lia.
Qed.

(** =========================================================================
    SUMMARY
    =========================================================================

    PROVEN RESULTS (with Qed):
    1. config_fits_strong_ok: Strong fitness implies tm_config_ok
    2. config_fits_strong_decode_encode: Full encode/decode roundtrip
    3. thiele_one_step_correct: One Thiele step = one TM step
    4. thiele_n_step_simulation: N Thiele steps = N TM steps
    5. bounded_execution_from_invariant: Per-step invariant → n-step
    6. concrete_thiele_strong: Strong simulation for bounded TMs
    7. thiele_subsumes_tm_complete: End-to-end chain theorem
    8. identity_tm_thiele_simulation: Worked example (identity TM)
    9. flip_tm_bounded: Worked example (flip TM) — fully Qed
    10. tm_minsky_state_simulation (in TM_to_Minsky.v): Minsky tracks TM state

    ADMITTED (non-blocking, superseded):
    - config_fits_ok: weak version superseded by config_fits_strong_ok (Qed)
    - concrete_thiele_semantics: interface record uses tm_config_ok;
      superseded by concrete_thiele_strong (Qed)

    CHAIN STATUS:
    TM_Basics → TM_to_Minsky → ThieleInstance → Simulation
    All links in the TM → Minsky → Thiele chain are now connected.

    One proof obligation (concrete_thiele_semantics) uses Admitted because
    the ModularThieleSemantics interface requires tm_config_ok (not
    config_fits_strong). The strong version (concrete_thiele_strong)
    is fully proven with ZERO admits. The end-to-end chain theorem
    (thiele_subsumes_tm_complete) is FULLY PROVEN.
    ========================================================================= *)
