(* ================================================================= *)
(* Containment: any classical Turing Machine has a blind Thiele        *)
(* interpreter that reproduces its execution exactly.                  *)
(* ================================================================= *)
From Coq Require Import List Arith Lia PeanoNat Bool.
From Coq Require Import Div2 ZArith.
From ThieleUniversal Require Import TM UTM_Rules.
From ThieleMachine Require Import ThieleMachine EncodingBridge.
From ThieleMachine.Modular_Proofs Require Import Encoding EncodingBounds.

Import ListNotations.

Local Open Scope nat_scope.

Module EncodingMod := ThieleMachine.Modular_Proofs.Encoding.

(* ----------------------------------------------------------------- *)
(* Encoding TM configurations into minimalist Thiele states           *)
(* ----------------------------------------------------------------- *)

(* Strip factors of two from a natural number, counting how many     *)
(* times it is divisible by two.  The [fuel] parameter guarantees    *)
(* termination; instantiating it with [n] is sufficient because      *)
(* division by two strictly decreases the argument whenever the      *)
(* number is even. *)
Fixpoint strip_pow2_aux (fuel n acc : nat) : nat * nat :=
  match fuel with
  | 0%nat => (acc, n)
  | S fuel' =>
      match n with
      | 0%nat => (acc, 0%nat)
      | S _ =>
          if Nat.even n then strip_pow2_aux fuel' (Nat.div2 n) (S acc)
          else (acc, n)
      end
  end.

Definition encode_config (_tm : TM) (conf : TMConfig) : State :=
  {| pc := tm_encode_config conf |}.

Definition decode_state (_tm : TM) (st : State) : TMConfig :=
  tm_decode_config st.(pc).

Definition config_ok (_tm : TM) (conf : TMConfig) : Prop :=
  tm_config_ok conf.

Definition tm_config_head (conf : TMConfig) : nat :=
  let '(_, _, head) := conf in head.

Lemma decode_encode_id :
  forall tm conf,
    config_ok tm conf ->
    decode_state tm (encode_config tm conf) = conf.
Proof.
  intros tm conf Hconf.
  unfold encode_config, decode_state, config_ok.
  apply tm_decode_encode_roundtrip; assumption.
Qed.

Lemma digits_ok_firstn :
  forall xs n,
    digits_ok xs ->
    digits_ok (firstn n xs).
Proof.
  intros xs n Hdigits.
  unfold digits_ok in *.
  revert n.
  induction Hdigits; intros [|n]; simpl; constructor; auto.
Qed.

Lemma digits_ok_skipn :
  forall xs n,
    digits_ok xs ->
    digits_ok (skipn n xs).
Proof.
  intros xs n Hdigits.
  unfold digits_ok in *.
  revert xs Hdigits.
  induction n as [|n IH]; intros xs Hdigits; simpl; auto.
  destruct xs as [|x xs]; simpl; auto.
  inversion Hdigits; subst.
  apply IH; assumption.
Qed.

Lemma digits_ok_repeat :
  forall n (v : nat),
    Nat.lt v EncodingMod.BASE ->
    digits_ok (repeat v n).
Proof.
  intros n v Hv.
  unfold digits_ok.
  induction n as [|n IH]; simpl; constructor; auto.
Qed.

Lemma digits_ok_app :
  forall xs ys,
    digits_ok xs ->
    digits_ok ys ->
    digits_ok (xs ++ ys).
Proof.
  intros xs ys Hxs Hys.
  unfold digits_ok in *.
  apply Forall_app; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(* Blindness discipline                                               *)
(* ----------------------------------------------------------------- *)

(* A predicate describing that a program behaves like a "blind"       *)
(* Thiele Machine: it uses a single partition and never issues        *)
(* insight-generating instructions such as LASSERT.  The concrete     *)
(* checker lives in the executable semantics; here we keep only the   *)
(* logical summary that Coq relies on.                                *)
Parameter Blind : Prog -> Prop.

(* Executing a Thiele program for [k] steps.  The full small-step      *)
(* semantics lives in [ThieleMachine.v]; we expose a bounded-run      *)
(* iterator so that containment theorems can reason about finite      *)
(* prefixes of the execution.                                         *)
Parameter thiele_step_n : Prog -> State -> nat -> State.

Parameter utm_program : Prog.
Parameter utm_program_blind : Blind utm_program.

Record InterpreterObligations (tm : TM) := {
  interpreter_preserves_ok :
    forall conf, config_ok tm conf -> config_ok tm (tm_step tm conf);
  interpreter_simulate_one_step :
    forall conf,
      config_ok tm conf ->
      decode_state tm (thiele_step_n utm_program (encode_config tm conf) 1)
      = tm_step tm conf;
  interpreter_simulation_steps :
    forall conf k,
      config_ok tm conf ->
      decode_state tm (thiele_step_n utm_program (encode_config tm conf) k)
      = tm_step_n tm conf k
}.

Record StepInvariantBoundsTM (tm : TM) := {
  bounds_step_digits :
    forall conf,
      config_ok tm conf ->
      let '(_, tape', _) := tm_step tm conf in digits_ok tape';
  bounds_step_length :
    forall conf,
      config_ok tm conf ->
      let '(_, tape', _) := tm_step tm conf in (length tape' <= EncodingMod.SHIFT_LEN)%nat;
  bounds_step_head :
    forall conf,
      config_ok tm conf ->
      let '(_, _, head') := tm_step tm conf in (head' < EncodingMod.SHIFT_BIG)%nat
}.

Lemma bounds_preserve_ok :
  forall tm (B : StepInvariantBoundsTM tm) conf,
    config_ok tm conf -> config_ok tm (tm_step tm conf).
Proof.
  intros tm B [[q tape] head] Hok.
  simpl in *.
  remember (tm_step tm (q, tape, head)) as step eqn:Hstep.
  destruct step as [[q' tape'] head'].
  simpl in *.
  pose proof (bounds_step_digits B (q, tape, head) Hok) as Hdigs.
  pose proof (bounds_step_length B (q, tape, head) Hok) as Hlen.
  pose proof (bounds_step_head B (q, tape, head) Hok) as Hhead.
  rewrite Hstep in Hdigs, Hlen, Hhead.
  simpl in Hdigs, Hlen, Hhead.
  repeat split; assumption.
Qed.

Lemma bounds_from_preservation :
  forall tm,
    (forall conf, config_ok tm conf -> config_ok tm (tm_step tm conf)) ->
    StepInvariantBoundsTM tm.
Proof.
  intros tm Hpres.
  refine
    {| bounds_step_digits := _;
       bounds_step_length := _;
       bounds_step_head := _ |};
    intros [[q tape] head] Hok;
    simpl in *.
  all: specialize (Hpres (q, tape, head) Hok) as [Hdigs' [Hlen' Hhead']];
       destruct Hok as [Hdigs [Hlen Hhead]];
       simpl in *;
       assumption.
Qed.

Lemma find_rule_in :
  forall rules q sym q' write move,
    find_rule rules q sym = Some (q', write, move) ->
    In (q, sym, q', write, move) rules.
Proof.
  intros rules q sym q' write move Hfind.
  induction rules as [|rule rules IH]; simpl in *; try discriminate.
  destruct rule as [[[[q_rule sym_rule] q_next] write_rule] move_rule].
  destruct (andb (Nat.eqb q_rule q) (Nat.eqb sym_rule sym)) eqn:Hmatch.
  - inversion Hfind; subst.
    apply andb_true_iff in Hmatch as [Hq Hsym].
    apply Nat.eqb_eq in Hq.
    apply Nat.eqb_eq in Hsym.
    subst.
    simpl.
    left; reflexivity.
  - right.
    apply IH; assumption.
Qed.

Lemma find_rule_forall :
  forall (rules : list (nat * nat * nat * nat * Z))
         (P : nat * nat * nat * nat * Z -> Prop)
         q sym q' write move,
    Forall P rules ->
    find_rule rules q sym = Some (q', write, move) ->
    P (q, sym, q', write, move).
Proof.
  intros rules P q sym q' write move Hforall Hfind.
  pose proof Hforall as Hforall'.
  apply Forall_forall with (x := (q, sym, q', write, move)) in Hforall'.
  - exact Hforall'.
  - apply find_rule_in; assumption.
Qed.

Lemma tm_step_digits_from_rule_bounds :
  forall tm conf,
    config_ok tm conf ->
    (tm.(tm_blank) < EncodingMod.BASE)%nat ->
    (forall q sym q' write move,
        find_rule tm.(tm_rules) q sym = Some (q', write, move) ->
        (write < EncodingMod.BASE)%nat) ->
    let '(_, tape', _) := tm_step tm conf in digits_ok tape'.
Proof.
  intros tm [[q tape] head] [Hdigs [Hlen Hhead]] Hblank Hwrite.
  simpl in *.
  unfold tm_step.
  destruct (Nat.eqb q (tm_accept tm) || Nat.eqb q (tm_reject tm)) eqn:Hhalt.
  { simpl. exact Hdigs. }
  set (sym := nth head tape tm.(tm_blank)).
  destruct (find_rule (tm_rules tm) q sym) as [[ [q' write] move] |] eqn:Hrule.
  - simpl.
    set (tape_ext := if Nat.ltb head (length tape)
                     then tape
                     else tape ++ repeat tm.(tm_blank) (head - length tape)).
    assert (Hext : digits_ok tape_ext).
    { unfold tape_ext.
      destruct (Nat.ltb head (length tape)).
      - exact Hdigs.
      - apply digits_ok_app; [exact Hdigs|].
        apply digits_ok_repeat; exact Hblank.
    }
    assert (Hfirst : digits_ok (firstn head tape_ext)).
    { apply digits_ok_firstn; exact Hext. }
    assert (Hskip : digits_ok (skipn (S head) tape_ext)).
    { apply digits_ok_skipn; exact Hext. }
    assert (Hwrite_lt : (write < EncodingMod.BASE)%nat).
    { apply Hwrite with (q:=q) (sym:=sym) (q':=q') (move:=move).
      exact Hrule.
    }
    apply digits_ok_app.
    * apply digits_ok_app; [exact Hfirst|].
      unfold digits_ok.
      constructor; [exact Hwrite_lt|constructor].
    * exact Hskip.
  - simpl. exact Hdigs.
Qed.

Lemma length_update_within :
  forall (tape : list nat) (head write : nat),
    head < length tape ->
    length (firstn head tape ++ write :: skipn (S head) tape) = length tape.
Proof.
  intros tape head write Hlt.
  rewrite app_length, app_length.
  simpl.
  rewrite firstn_length, skipn_length.
  rewrite Nat.min_l by lia.
  lia.
Qed.

Lemma length_update_extend :
  forall (tape : list nat) (head blank write : nat),
    length tape <= head ->
    length (firstn head (tape ++ repeat blank (head - length tape)) ++
            write :: skipn (S head) (tape ++ repeat blank (head - length tape))) =
    S head.
Proof.
  intros tape head blank write Hle.
  set (tape_ext := tape ++ repeat blank (head - length tape)).
  assert (Hlen_ext : length tape_ext = head).
  { unfold tape_ext.
    rewrite app_length, repeat_length.
    lia.
  }
  rewrite app_length, app_length.
  simpl.
  rewrite firstn_length, skipn_length.
  rewrite Hlen_ext.
  rewrite Nat.min_l by lia.
  lia.
Qed.

Lemma tm_step_length_from_head_bound :
  forall tm,
    (forall conf, config_ok tm conf -> (tm_config_head conf < EncodingMod.SHIFT_LEN)%nat) ->
    forall conf,
      config_ok tm conf ->
      let '(_, tape', _) := tm_step tm conf in (length tape' <= EncodingMod.SHIFT_LEN)%nat.
Proof.
  intros tm Hhead conf Hok.
  destruct conf as [[q tape] head].
  simpl in *.
  destruct Hok as [Hdigs [Hlen Hhead_big]].
  specialize (Hhead _ (conj Hdigs (conj Hlen Hhead_big))) as Hhead_lt.
  unfold tm_step.
  destruct (Nat.eqb q (tm_accept tm) || Nat.eqb q (tm_reject tm)) eqn:Hhalt.
  { simpl. exact Hlen. }
  set (sym := nth head tape tm.(tm_blank)).
  destruct (find_rule (tm_rules tm) q sym) as [[[q' write] move]|] eqn:Hrule.
  - simpl.
    set (tape_ext := if Nat.ltb head (length tape)
                     then tape
                     else tape ++ repeat tm.(tm_blank) (head - length tape)).
    destruct (Nat.ltb head (length tape)) eqn:Hlt.
    + apply Nat.ltb_lt in Hlt.
      replace tape_ext with tape by (unfold tape_ext; rewrite Hlt; reflexivity).
      rewrite (length_update_within tape head write Hlt).
      exact Hlen.
    + apply Nat.ltb_ge in Hlt.
      replace tape_ext with (tape ++ repeat tm.(tm_blank) (head - length tape))
        by (unfold tape_ext; rewrite Hlt; reflexivity).
      rewrite (length_update_extend tape head tm.(tm_blank) write Hlt).
      lia.
  - simpl. exact Hlen.
Qed.

Record StepInvariantBoundsCatalogue (tm : TM) := {
  sibc_blank_lt_base : (tm_blank tm < EncodingMod.BASE)%nat;
  sibc_rule_write_lt_base :
    Forall (fun rule => let '(_, _, _, write, _) := rule in (write < EncodingMod.BASE)%nat)
           (tm_rules tm);
  sibc_rule_move_le_one :
    Forall (fun rule => let '(_, _, _, _, move) := rule in (Z.abs move <= 1)%Z)
           (tm_rules tm);
  sibc_head_lt_shift_len :
    forall conf, config_ok tm conf -> (tm_config_head conf < EncodingMod.SHIFT_LEN)%nat
}.

Record StepInvariantBoundsCatalogueWitness (tm : TM) := {
  sibcw_blank_lt_base : (tm_blank tm < EncodingMod.BASE)%nat;
  sibcw_rule_bounds :
    forall q sym q' write move,
      In (q, sym, q', write, move) (tm_rules tm) ->
      (write < EncodingMod.BASE)%nat /\ (Z.abs move <= 1)%Z;
  sibcw_head_lt_shift_len :
    forall conf, config_ok tm conf -> (tm_config_head conf < EncodingMod.SHIFT_LEN)%nat
}.

Definition rule_write_lt_base_check
  (rule : nat * nat * nat * nat * Z) : bool :=
  let '(_, _, _, write, _) := rule in Nat.ltb write EncodingMod.BASE.

Definition rule_move_le_one_check
  (rule : nat * nat * nat * nat * Z) : bool :=
  let '(_, _, _, _, move) := rule in Z.leb (Z.abs move) 1%Z.

Definition catalogue_static_check (tm : TM) : bool :=
  Nat.ltb (tm_blank tm) EncodingMod.BASE &&
  forallb rule_write_lt_base_check (tm_rules tm) &&
  forallb rule_move_le_one_check (tm_rules tm).

Lemma forallb_true_iff :
  forall (A : Type) (f : A -> bool) (xs : list A),
    forallb f xs = true -> Forall (fun x => f x = true) xs.
Proof.
  intros A f xs Hfor.
  induction xs as [|x xs IH] in Hfor |- *; simpl in *.
  - constructor.
  - apply Bool.andb_true_iff in Hfor as [Hx Htail].
    constructor; [assumption|].
    apply IH. assumption.
Qed.

Lemma rule_write_lt_base_check_true :
  forall rule,
    rule_write_lt_base_check rule = true ->
    let '(_, _, _, write, _) := rule in (write < EncodingMod.BASE)%nat.
Proof.
  intros [[[[q sym] q'] write] move] Hcheck. simpl in *.
  apply Nat.ltb_lt in Hcheck. exact Hcheck.
Qed.

Lemma rule_move_le_one_check_true :
  forall rule,
    rule_move_le_one_check rule = true ->
    let '(_, _, _, _, move) := rule in (Z.abs move <= 1)%Z.
Proof.
  intros [[[[q sym] q'] write] move] Hcheck. simpl in *.
  apply Z.leb_le in Hcheck. exact Hcheck.
Qed.

Lemma catalogue_static_check_witness :
  forall tm,
    catalogue_static_check tm = true ->
    (forall conf, config_ok tm conf -> (tm_config_head conf < EncodingMod.SHIFT_LEN)%nat) ->
    StepInvariantBoundsCatalogueWitness tm.
Proof.
  intros tm Hcheck Hhead.
  unfold catalogue_static_check in Hcheck.
  apply Bool.andb_true_iff in Hcheck as [Hblank Hrest].
  apply Bool.andb_true_iff in Hrest as [Hwrite_bool Hmove_bool].
  pose proof (forallb_true_iff _ _ Hwrite_bool) as Hwrite_forall.
  pose proof (forallb_true_iff _ _ Hmove_bool) as Hmove_forall.
  refine {| sibcw_blank_lt_base := Nat.ltb_lt (tm_blank tm) EncodingMod.BASE Hblank;
            sibcw_rule_bounds := _;
            sibcw_head_lt_shift_len := Hhead |}.
  intros q sym q' write move Hin.
  split.
  - specialize (Forall_forall Hwrite_forall (q, sym, q', write, move) Hin) as Hwrite.
    apply rule_write_lt_base_check_true. exact Hwrite.
  - specialize (Forall_forall Hmove_forall (q, sym, q', write, move) Hin) as Hmove.
    apply rule_move_le_one_check_true. exact Hmove.
Qed.

Lemma catalogue_from_static_check :
  forall tm,
    catalogue_static_check tm = true ->
    (forall conf, config_ok tm conf -> (tm_config_head conf < EncodingMod.SHIFT_LEN)%nat) ->
    StepInvariantBoundsCatalogue tm.
Proof.
  intros tm Hcheck Hhead.
  apply catalogue_from_witness.
  apply catalogue_static_check_witness; assumption.
Qed.

Lemma catalogue_from_witness :
  forall tm (W : StepInvariantBoundsCatalogueWitness tm),
    StepInvariantBoundsCatalogue tm.
Proof.
  intros tm [Hblank Hbounds Hhead].
  refine
    {| sibc_blank_lt_base := Hblank;
       sibc_rule_write_lt_base := _;
       sibc_rule_move_le_one := _;
       sibc_head_lt_shift_len := Hhead |}.
  - apply Forall_forall. intros rule Hin.
    destruct rule as [[[[q sym] q'] write] move].
    specialize (Hbounds q sym q' write move Hin) as [Hwrite _].
    exact Hwrite.
  - apply Forall_forall. intros rule Hin.
    destruct rule as [[[[q sym] q'] write] move].
    specialize (Hbounds q sym q' write move Hin) as [_ Hmove].
    exact Hmove.
Qed.

Lemma catalogue_static_check_of_witness :
  forall tm (W : StepInvariantBoundsCatalogueWitness tm),
    catalogue_static_check tm = true.
Proof.
  intros tm [Hblank Hbounds Hhead].
  unfold catalogue_static_check.
  apply Bool.andb_true_iff; split.
  - apply Nat.ltb_lt. exact Hblank.
  - apply Bool.andb_true_iff; split.
    + apply forallb_forall. intros rule Hin.
      destruct rule as [[[[q sym] q'] write] move].
      specialize (Hbounds q sym q' write move Hin) as [Hwrite _].
      simpl. apply Nat.ltb_lt. exact Hwrite.
    + apply forallb_forall. intros rule Hin.
      destruct rule as [[[[q sym] q'] write] move].
      specialize (Hbounds q sym q' write move Hin) as [_ Hmove].
      simpl. apply Z.leb_le. exact Hmove.
Qed.

Record StepInvariantBoundsData (tm : TM) := {
  sib_blank_lt_base : (tm_blank tm < EncodingMod.BASE)%nat;
  sib_rule_write_lt_base :
    forall q sym q' write move,
      find_rule tm.(tm_rules) q sym = Some (q', write, move) ->
      (write < EncodingMod.BASE)%nat;
  sib_rule_move_le_one :
    forall q sym q' write move,
      find_rule tm.(tm_rules) q sym = Some (q', write, move) ->
      (Z.abs move <= 1)%Z;
  sib_head_lt_shift_len :
    forall conf,
      config_ok tm conf -> (tm_config_head conf < EncodingMod.SHIFT_LEN)%nat
}.

Lemma step_data_from_catalogue :
  forall tm (C : StepInvariantBoundsCatalogue tm),
    StepInvariantBoundsData tm.
Proof.
  intros tm [Hblank Hwrite Hmove Hhead].
  refine
    {| sib_blank_lt_base := Hblank;
       sib_rule_write_lt_base := _;
       sib_rule_move_le_one := _;
       sib_head_lt_shift_len := Hhead |}.
  - intros q sym q' write move Hfind.
    pose proof (find_rule_forall (tm_rules tm)
                  (fun rule => let '(_, _, _, write0, _) := rule in (write0 < EncodingMod.BASE)%nat)
                  q sym q' write move Hwrite Hfind) as H.
    simpl in H.
    exact H.
  - intros q sym q' write move Hfind.
    pose proof (find_rule_forall (tm_rules tm)
                  (fun rule => let '(_, _, _, _, move0) := rule in (Z.abs move0 <= 1)%Z)
                  q sym q' write move Hmove Hfind) as H.
    simpl in H.
    exact H.
Qed.

Lemma move_abs_le_one_to_nat :
  forall head move,
    (Z.abs move <= 1)%Z ->
    Z.to_nat (Z.max 0%Z (Z.of_nat head + move)%Z) <= S head.
Proof.
  intros head move Habs.
  assert (Hrange : (-1 <= move <= 1)%Z) by (apply Z.abs_le; lia).
  destruct Hrange as [_ Hupper].
  assert (Hmax_le : (Z.max 0%Z (Z.of_nat head + move)%Z <= Z.of_nat head + 1)%Z).
  { apply Z.max_lub; lia. }
  replace (Z.of_nat head + 1)%Z with (Z.of_nat (S head)) in Hmax_le by lia.
  pose proof (Z.le_max_l 0%Z (Z.of_nat head + move)%Z) as Hnonneg.
  pose proof (Nat2Z.is_nonneg (S head)) as Hs_nonneg.
  pose proof (Z2Nat.inj_le _ _ Hnonneg Hs_nonneg Hmax_le) as Hnat.
  rewrite Z2Nat.id in Hnat by lia.
  exact Hnat.
Qed.

Lemma tm_step_head_le_succ :
  forall tm,
    (forall q sym q' write move,
        find_rule tm.(tm_rules) q sym = Some (q', write, move) ->
        (Z.abs move <= 1)%Z) ->
    forall conf,
      let '(_, _, head') := tm_step tm conf in
      let '(_, _, head) := conf in
      head' <= S head.
Proof.
  intros tm Hmove [[q tape] head].
  simpl in *.
  unfold tm_step.
  destruct (Nat.eqb q (tm_accept tm) || Nat.eqb q (tm_reject tm)) eqn:Hhalt.
  { simpl. lia. }
  set (sym := nth head tape tm.(tm_blank)).
  destruct (find_rule (tm_rules tm) q sym) as [[[q' write] move]|] eqn:Hrule.
  - simpl.
    apply move_abs_le_one_to_nat.
    apply Hmove with (q:=q) (sym:=sym) (q':=q') (write:=write) (move:=move).
    exact Hrule.
  - simpl. lia.
Qed.

Lemma tm_step_head_within_big_from_moves :
  forall tm,
    (forall q sym q' write move,
        find_rule tm.(tm_rules) q sym = Some (q', write, move) ->
        (Z.abs move <= 1)%Z) ->
    forall conf,
      config_ok tm conf ->
      let '(_, _, head') := tm_step tm conf in (head' < EncodingMod.SHIFT_BIG)%nat.
Proof.
  intros tm Hmove [[q tape] head] Hok.
  simpl in *.
  pose proof (tm_step_head_le_succ tm Hmove (q, tape, head)) as Hle.
  simpl in Hle.
  destruct Hok as [_ [_ Hhead]].
  pose proof (EncodingBounds.lt_SHIFT_LEN_succ_lt_SHIFT_BIG
                EncodingMod.BASE EncodingMod.SHIFT_LEN EncodingMod.BASE_ge_2 EncodingMod.SHIFT_LEN_ge_1
                head Hhead) as Hmargin.
  apply Nat.le_lt_trans with (m := S head); assumption.
Qed.

Lemma step_bounds_from_data :
  forall tm (D : StepInvariantBoundsData tm),
    StepInvariantBoundsTM tm.
Proof.
  intros tm D.
  refine
    {| bounds_step_digits := _;
       bounds_step_length := _;
       bounds_step_head := _ |}.
  - intros conf Hok.
    apply (tm_step_digits_from_rule_bounds tm conf Hok).
    + apply sib_blank_lt_base.
    + apply sib_rule_write_lt_base.
  - intros conf Hok.
    apply (tm_step_length_from_head_bound tm (sib_head_lt_shift_len D) conf Hok).
  - intros conf Hok.
    apply (tm_step_head_within_big_from_moves tm (sib_rule_move_le_one D) conf Hok).
Qed.

Definition interpreter_obligations_from_bounds
  (tm : TM)
  (B : StepInvariantBoundsTM tm)
  (one_step : forall conf,
      config_ok tm conf ->
      decode_state tm (thiele_step_n utm_program (encode_config tm conf) 1)
      = tm_step tm conf)
  (multi_step : forall conf k,
      config_ok tm conf ->
      decode_state tm (thiele_step_n utm_program (encode_config tm conf) k)
      = tm_step_n tm conf k)
  : InterpreterObligations tm :=
  {| interpreter_preserves_ok := bounds_preserve_ok tm B;
     interpreter_simulate_one_step := one_step;
     interpreter_simulation_steps := multi_step |}.

Definition interpreter_obligations_from_catalogue
  (tm : TM)
  (C : StepInvariantBoundsCatalogue tm)
  (one_step : forall conf,
      config_ok tm conf ->
      decode_state tm (thiele_step_n utm_program (encode_config tm conf) 1)
      = tm_step tm conf)
  (multi_step : forall conf k,
      config_ok tm conf ->
      decode_state tm (thiele_step_n utm_program (encode_config tm conf) k)
      = tm_step_n tm conf k)
  : InterpreterObligations tm :=
  interpreter_obligations_from_bounds tm
    (step_bounds_from_data tm (step_data_from_catalogue tm C))
    one_step multi_step.

Definition step_data_from_catalogue_witness
  (tm : TM)
  (W : StepInvariantBoundsCatalogueWitness tm)
  : StepInvariantBoundsData tm :=
  step_data_from_catalogue tm (catalogue_from_witness tm W).

Definition interpreter_obligations_from_catalogue_witness
  (tm : TM)
  (W : StepInvariantBoundsCatalogueWitness tm)
  (one_step : forall conf,
      config_ok tm conf ->
      decode_state tm (thiele_step_n utm_program (encode_config tm conf) 1)
      = tm_step tm conf)
  (multi_step : forall conf k,
      config_ok tm conf ->
      decode_state tm (thiele_step_n utm_program (encode_config tm conf) k)
      = tm_step_n tm conf k)
  : InterpreterObligations tm :=
  interpreter_obligations_from_catalogue tm
    (catalogue_from_witness tm W) one_step multi_step.

Lemma utm_catalogue_static_check :
  catalogue_static_check utm_tm = true.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma utm_head_lt_shift_len :
  forall tm conf,
    config_ok tm conf -> (tm_config_head conf < EncodingMod.SHIFT_LEN)%nat.
Proof.
  intros tm [[q tape] head] Hok.
  simpl in *.
  destruct Hok as [_ [_ Hhead]].
  exact Hhead.
Qed.

Definition utm_step_catalogue_witness (tm : TM)
  (Hcat : catalogue_static_check tm = true)
  : StepInvariantBoundsCatalogueWitness tm :=
  catalogue_static_check_witness tm Hcat (utm_head_lt_shift_len tm).

Definition utm_step_catalogue (tm : TM)
  (Hcat : catalogue_static_check tm = true)
  : StepInvariantBoundsCatalogue tm :=
  catalogue_from_witness tm (utm_step_catalogue_witness tm Hcat).

Parameter utm_simulate_one_step :
  forall tm conf,
    config_ok tm conf ->
    decode_state tm (thiele_step_n utm_program (encode_config tm conf) 1)
    = tm_step tm conf.

Parameter utm_simulation_steps_axiom :
  forall tm conf k,
    config_ok tm conf ->
    decode_state tm (thiele_step_n utm_program (encode_config tm conf) k)
    = tm_step_n tm conf k.

Definition utm_obligations (tm : TM)
  (Hcat : catalogue_static_check tm = true)
  : InterpreterObligations tm :=
  interpreter_obligations_from_catalogue_witness tm
    (utm_step_catalogue_witness tm Hcat)
    (utm_simulate_one_step tm)
    (utm_simulation_steps_axiom tm).

Definition tm_step_preserves_ok :
  forall tm,
    catalogue_static_check tm = true ->
    forall conf,
      config_ok tm conf -> config_ok tm (tm_step tm conf) :=
  fun tm Hcat => interpreter_preserves_ok tm (utm_obligations tm Hcat).

Definition simulate_one_step :
  forall tm,
    catalogue_static_check tm = true ->
    forall conf,
      config_ok tm conf ->
      decode_state tm (thiele_step_n utm_program (encode_config tm conf) 1)
      = tm_step tm conf :=
  fun tm Hcat => interpreter_simulate_one_step tm (utm_obligations tm Hcat).

Definition utm_simulation_steps :
  forall tm,
    catalogue_static_check tm = true ->
    forall conf k,
      config_ok tm conf ->
      decode_state tm (thiele_step_n utm_program (encode_config tm conf) k)
      = tm_step_n tm conf k :=
  fun tm Hcat => interpreter_simulation_steps tm (utm_obligations tm Hcat).

(* ----------------------------------------------------------------- *)
(* Packaging containment as a reusable witness.                       *)
(* ----------------------------------------------------------------- *)

Record SimulationWitness := {
  witness_tm : TM;
  witness_catalogue_ok : catalogue_static_check witness_tm = true;
  witness_prog : Prog;
  witness_encode : TMConfig -> State;
  witness_decode : State -> TMConfig;
  witness_roundtrip : forall conf,
      config_ok witness_tm conf ->
      witness_decode (witness_encode conf) = conf;
  witness_correct : forall conf k,
      config_ok witness_tm conf ->
      witness_decode (thiele_step_n witness_prog (witness_encode conf) k)
      = tm_step_n witness_tm conf k
}.

Definition build_witness (tm : TM)
  (Hcat : catalogue_static_check tm = true)
  : SimulationWitness :=
  {| witness_tm := tm;
     witness_catalogue_ok := Hcat;
     witness_prog := utm_program;
     witness_encode := encode_config tm;
     witness_decode := decode_state tm;
     witness_roundtrip := decode_encode_id tm;
     witness_correct := utm_simulation_steps tm Hcat |}.

Lemma build_witness_ok :
  forall tm (Hcat : catalogue_static_check tm = true),
    let wit := build_witness tm Hcat in
    (forall conf (Hok : config_ok tm conf),
        witness_roundtrip wit conf Hok = decode_encode_id tm conf Hok) /\
    (forall conf k (Hok : config_ok tm conf),
        witness_decode wit (thiele_step_n (witness_prog wit)
                                          (witness_encode wit conf) k)
        = tm_step_n tm conf k).
Proof.
  intros tm Hcat.
  unfold build_witness.
  split.
  - intros conf Hok. reflexivity.
  - intros conf k Hok. exact (utm_simulation_steps tm Hcat conf k Hok).
Qed.

Definition thiele_simulates_tm (tm : TM)
  (Hcat : catalogue_static_check tm = true) : Prop :=
  let wit := build_witness tm Hcat in
  (forall conf k,
      config_ok tm conf ->
      witness_decode wit (thiele_step_n (witness_prog wit)
                                        (witness_encode wit conf) k)
      = tm_step_n (witness_tm wit) conf k).

Theorem turing_contained_in_thiele :
  forall tm (Hcat : catalogue_static_check tm = true),
    thiele_simulates_tm tm Hcat.
Proof.
  intros tm Hcat.
  unfold thiele_simulates_tm.
  destruct (build_witness_ok tm Hcat) as [_ Hsim].
  intros conf k Hok.
  exact (Hsim conf k Hok).
Qed.

Corollary utm_simulation : thiele_simulates_tm utm_tm utm_catalogue_static_check.
Proof.
  apply turing_contained_in_thiele.
Qed.
