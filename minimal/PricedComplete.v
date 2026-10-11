(** PricedComplete.v: the machine of EarnedPriced.v is Thiele-complete.

    ThieleComplete.v defines thiele_complete for any machine: a reading of
    its moves as base moves and three record moves, CHECK (claim), COMMIT
    (claim) and CERTIFY, meeting four clauses (universal base, earned
    record, exact toll, non-vacuity). This file uses that definition
    unchanged.

    The only question PAY raises is how to read it. The exact-toll clause
    requires every move to cost 0 if it is a base move and 1 otherwise, and
    PAY costs 1, so PAY cannot be read as a base move. It is read as a CHECK
    of the empty claim: the claims are option (prop * ctr), a real claim is
    Some (p, c), and PAY is KCheck None. The empty claim means nothing
    (its meaning is False) and its check never passes, so PAY can never
    begin an earned chain; it is a record move only in that it pays the
    record-move price of 1. Reading PAY as a CERTIFY would call a move that
    never raises the record the raiser, and reading it as a COMMIT of the
    empty claim would serve equally well; the CHECK reading is the one that
    says plainly what PAY is, a paid move that establishes nothing.

    What is proved (every result closed under the global context):

      1. The machine of EarnedPriced.v pays the toll for any property
         language, so it is a CertificationSystem [priced_toll,
         priced_cert_system].
      2. For any property language with an exact checker and a property
         true of one counter value and false of another, it is
         Thiele-complete [priced_thiele_complete].
      3. The sorted-list instance and the counter-language instance are
         Thiele-complete [priced_sorted_thiele_complete,
         priced_core_thiele_complete].

    Dependencies: Coq standard library, EarnedCore.v, EarnedGeneric.v,
    EarnedPriced.v and ThieleComplete.v. No axioms, no Admitted.            *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose, as in
   ThieleComplete.v: this file imports nothing outside the standard library
   and the minimal files, so it re-checks from a clean checkout. *)

From Coq Require Import List Arith Lia Bool.
From Coq Require Import Sorting.Sorted.
Import ListNotations.
Require Minimal.EarnedGeneric.
Require Minimal.EarnedPriced.
Require Minimal.ThieleComplete.
Module G := Minimal.EarnedGeneric.
Module P := Minimal.EarnedPriced.
Module T := Minimal.ThieleComplete.

Section PricedInstance.

Context {prop : Type}.
Variable prop_eqb : prop -> prop -> bool.
Hypothesis prop_eqb_eq : forall p q, prop_eqb p q = true <-> p = q.
Variable eval : prop -> nat -> bool.
Variable holds : prop -> nat -> Prop.
Hypothesis eval_iff : forall p v, eval p v = true <-> holds p v.

Definition priced_machine : T.machine :=
  T.mk_machine (@G.state prop) (@P.pr_instr prop) (P.pr_exec prop_eqb eval)
    (@P.pr_cost prop) (@G.cert prop).

Lemma priced_run_eq : forall tr s,
  T.run priced_machine tr s = P.pr_run prop_eqb eval tr s.
Proof. induction tr; intros; simpl; auto. Qed.

(* The toll holds with no assumption on the property language. *)
Theorem priced_toll : T.thiele_machine priced_machine.
Proof. intros s m H0 H1. exact (P.pr_a2 prop_eqb eval s m H0 H1). Qed.

Definition priced_cert_system : T.CertificationSystem :=
  T.as_cert_system priced_machine priced_toll.

(* Each two-counter instruction is the machine's own INC or DEC, the same
   moves as in EarnedGeneric.v. *)
Definition priced_compile (i : T.cm_instr) : @P.pr_instr prop :=
  P.pr_embed (T.generic_compile i).

Lemma priced_sim : forall (s : @G.state prop) i, G.err (G.core_of s) = false ->
  T.generic_window (P.pr_exec prop_eqb eval s (priced_compile i))
    = T.cm_exec i (T.generic_window s) /\
  G.err (G.core_of (P.pr_exec prop_eqb eval s (priced_compile i))) = false.
Proof.
  intros s i He. unfold priced_compile. rewrite P.pr_exec_embed.
  exact (T.generic_sim prop_eqb eval s i He).
Qed.

Definition priced_base : T.universal_base priced_machine :=
  T.mk_ub priced_machine T.generic_window (fun s => G.err (G.core_of s) = false)
    priced_compile G.start (fun a b => eq_refl) (fun a b => eq_refl) priced_sim.

(* How the moves read. PAY is a check of the empty claim None. *)
Definition priced_kind (i : @P.pr_instr prop) : T.kind (option (prop * G.ctr)) :=
  match i with
  | P.CHECK p c => T.KCheck (Some (p, c))
  | P.COMMIT p c => T.KCommit (Some (p, c))
  | P.CERTIFY => T.KCertify
  | P.PAY => T.KCheck None
  | _ => T.KBase
  end.

(* A claim Some (p, c) means p holds of counter c; the empty claim means
   nothing. *)
Definition priced_meaning (oc : option (prop * G.ctr)) (s : @G.state prop) : Prop :=
  match oc with
  | Some (p, c) => holds p (G.val (G.core_of s) c)
  | None => False
  end.

(* The checker is CHECK's own test; the empty claim never passes. *)
Definition priced_check (s : @G.state prop) (oc : option (prop * G.ctr)) : bool :=
  match oc with
  | Some (p, c) => G.check_ok eval (G.core_of s) p c
  | None => false
  end.

(* What Some (p, c) is about is unchanged when counter c's version and
   value are; the empty claim is about nothing. *)
Definition priced_same (oc : option (prop * G.ctr)) (s t : @G.state prop) : Prop :=
  match oc with
  | Some (_, c) => G.ver (G.core_of s) c = G.ver (G.core_of t) c /\
                   G.val (G.core_of s) c = G.val (G.core_of t) c
  | None => True
  end.

Definition priced_interface : T.thiele_interface priced_machine :=
  T.mk_ti priced_machine priced_base (option (prop * G.ctr)) priced_kind
    priced_meaning priced_check priced_same G.clean_start (@G.mu prop).

(* PAY reads as a check that never passes, of a claim that never holds. *)
Theorem priced_pay_reads_as_failed_check : forall s,
  priced_kind P.PAY = T.KCheck None /\ priced_check s None = false /\
  ~ priced_meaning None s.
Proof. intros s. split; [reflexivity | split; [reflexivity | intro H; exact H]]. Qed.

Lemma priced_chain_holds : forall s0 tr,
  G.clean_start s0 -> G.cert (P.pr_run prop_eqb eval tr s0) = true ->
  T.earned_chain priced_interface s0 tr.
Proof.
  intros s0 tr H0 H1. pose proof H0 as [_ [Hch Hc0]].
  destruct (P.pr_cert_first prop_eqb eval s0 tr Hc0 H1)
    as [pre [post [Htr [Hpre Hok]]]].
  pose proof Hok as Hset. unfold G.certify_ok in Hset.
  apply andb_true_iff in Hset as [_ Hset].
  destruct (G.chan (G.core_of (P.pr_run prop_eqb eval pre s0))) as [f |] eqn:Hf;
    [| discriminate].
  destruct (P.pr_chan_origin prop_eqb eval s0 pre f Hch Hf)
    as [preC [p [c [mid2 [HpreC [Hcm _]]]]]].
  destruct (P.pr_earned_commitment_provenance prop_eqb prop_eqb_eq eval
              s0 preC p c H0 Hcm)
    as [pre1 [mid1 [Hpre1 [Hck [_ [_ [_ Hun]]]]]]].
  assert (Hlist : pre1 ++ P.CHECK p c :: mid1 ++ P.COMMIT p c :: mid2 = pre)
    by (rewrite HpreC, Hpre1; T.list_eq).
  exists pre1, (Some (p, c)), (P.CHECK p c), mid1, (P.COMMIT p c), mid2, P.CERTIFY, post.
  split; [rewrite Htr, <- Hlist; T.list_eq |].
  split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
  split; [rewrite priced_run_eq; exact Hck |].
  split.
  { intros t1 t2 Hm. rewrite !priced_run_eq. simpl.
    replace (pre1 ++ P.CHECK p c :: t1) with ((pre1 ++ [P.CHECK p c]) ++ t1)
      by (rewrite <- app_assoc; reflexivity).
    rewrite P.pr_run_app.
    destruct (P.pr_untouched_prefix prop_eqb eval _ _ _ Hun t1 t2 Hm) as [Hv Hw].
    rewrite Hv, Hw, P.pr_run_snoc, P.pr_base_blind, P.pr_ver_check, P.pr_val_check.
    split; reflexivity. }
  assert (Hl2 : pre1 ++ P.CHECK p c :: mid1 ++ P.COMMIT p c :: mid2 ++ [P.CERTIFY]
                = pre ++ [P.CERTIFY]) by (rewrite <- Hlist; T.list_eq).
  assert (Hup : G.cert (P.pr_run prop_eqb eval (pre ++ [P.CERTIFY]) s0) = true)
    by (rewrite P.pr_run_snoc; simpl; rewrite Hpre; exact Hok).
  rewrite <- Hl2 in Hup. rewrite <- Hlist in Hpre.
  split; rewrite priced_run_eq; assumption.
Qed.

(* The bare chain on (p, A) certifies from start a b exactly when p holds
   of a: it is a PAY-free run, so it is EarnedGeneric's chain. *)
Lemma priced_chain_iff : forall p a b,
  G.cert (P.pr_run prop_eqb eval [P.CHECK p G.CA; P.COMMIT p G.CA; P.CERTIFY]
            (G.start a b)) = true <-> holds p a.
Proof.
  intros p a b.
  change [P.CHECK p G.CA; P.COMMIT p G.CA; P.CERTIFY]
    with (map P.pr_embed [G.CHECK p G.CA; G.COMMIT p G.CA; G.CERTIFY]).
  rewrite P.pr_run_embed.
  exact (T.generic_chain_iff prop_eqb prop_eqb_eq eval holds eval_iff p a b).
Qed.

Lemma priced_thiele_complete_with : forall p v w,
  holds p v -> ~ holds p w -> T.thiele_complete_with priced_interface.
Proof.
  intros p0 v w Hv Hw. split; [| split; [| split]].
  - split; [intros [[|] | [|] j]; reflexivity |].
    split; [intros a b; apply G.generic_start_clean |]. split.
    + intros s m Hk. destruct m; simpl in Hk; try discriminate; simpl;
        apply orb_false_r.
    + intros s m H. apply P.pr_cert_permanent, H.
  - split; [intros s [_ [_ H]]; exact H |]. split.
    + intros s0 tr H0 H1. apply priced_chain_holds; [exact H0 |].
      rewrite <- priced_run_eq. exact H1.
    + split.
      * intros s [[p c] |] H; simpl in *; [| discriminate].
        unfold G.check_ok in H.
        apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [_ H].
        apply eval_iff, H.
      * intros [[p c] |] s t Hsame H; simpl in *; [| exact H].
        destruct Hsame as [_ Hsame]. rewrite <- Hsame. exact H.
  - split; [intros []; reflexivity | intros s m; reflexivity].
  - exists (Some (p0, G.CA)), (P.CHECK p0 G.CA), (P.COMMIT p0 G.CA), P.CERTIFY.
    split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
    split; [| split; [exists v, 0; exact Hv | exists w, 0; exact Hw]].
    intros a b. unfold T.load. simpl T.ti_meaning. rewrite priced_run_eq.
    apply priced_chain_iff.
Qed.

(* The meaning and subject of a claim are fixed independently of CHECK. *)
Definition priced_claim_eqb (x y : option (prop * G.ctr)) : bool :=
  match x, y with
  | None, None => true
  | Some a, Some b => T.generic_claim_eqb prop_eqb a b
  | _, _ => false
  end.

Lemma priced_claim_eqb_spec : forall x y, priced_claim_eqb x y = true <-> x = y.
Proof.
  intros [x |] [y |]; simpl; try (split; congruence).
  rewrite (T.generic_claim_eqb_spec prop_eqb prop_eqb_eq).
  split; congruence.
Qed.

Lemma priced_same_keeps : forall c s t,
  priced_same c s t -> priced_meaning c s -> priced_meaning c t.
Proof.
  intros [[p c] |] s t H Hm; simpl in *; [| exact Hm].
  destruct H as [_ Hv]. rewrite <- Hv. exact Hm.
Qed.

Definition priced_language : T.claim_language priced_machine :=
  T.mk_cl priced_machine (option (prop * G.ctr)) priced_claim_eqb priced_claim_eqb_spec
    priced_meaning priced_same priced_same_keeps.

Theorem priced_thiele_complete_over :
  (exists p v w, holds p v /\ ~ holds p w) ->
  T.thiele_complete_over priced_machine priced_language.
Proof.
  intros [p [v [w [Hv Hw]]]].
  apply (T.thiele_complete_with_over _ priced_interface
    priced_claim_eqb priced_claim_eqb_spec priced_same_keeps).
  exact (priced_thiele_complete_with p v w Hv Hw).
Qed.

End PricedInstance.

(* The machine of EarnedPriced.v over any property language with an exact
   checker, in which some property is true of one value and false of
   another, is Thiele-complete, with PAY read as a check of the empty
   claim. *)
Theorem priced_thiele_complete :
  forall (prop : Type) (prop_eqb : prop -> prop -> bool)
         (eval : prop -> nat -> bool) (holds : prop -> nat -> Prop),
  (forall p q, prop_eqb p q = true <-> p = q) ->
  (forall p v, eval p v = true <-> holds p v) ->
  (exists p v w, holds p v /\ ~ holds p w) ->
  T.thiele_complete (priced_machine prop_eqb eval).
Proof.
  intros prop prop_eqb eval holds Heq Hiff [p [v [w [Hv Hw]]]].
  exists (priced_interface prop_eqb eval holds).
  exact (priced_thiele_complete_with prop_eqb Heq eval holds Hiff p v w Hv Hw).
Qed.

(* With "this counter is a sorted list": 18 decodes to [1; 2], sorted, and
   20 decodes to [2; 1], not sorted. *)
Theorem priced_sorted_thiele_complete :
  T.thiele_complete (priced_machine G.sprop_eqb G.seval).
Proof.
  apply (priced_thiele_complete _ _ _ G.sholds G.sprop_eqb_eq G.seval_iff).
  exists G.PSorted, 18, 20. split.
  - simpl. apply G.sortedb_iff. vm_compute. reflexivity.
  - simpl. intro H. apply G.sortedb_iff in H. vm_compute in H. discriminate H.
Qed.

(* With the counter language of EarnedCore.v: "the counter is 0" holds of
   0 and not of 1. *)
Theorem priced_core_thiele_complete :
  T.thiele_complete (priced_machine G.cprop_eqb G.ceval).
Proof.
  apply (priced_thiele_complete _ _ _ G.cholds G.cprop_eqb_eq G.ceval_iff).
  exists G.PZero, 0, 1. split; simpl; [reflexivity | discriminate].
Qed.

(* ================================================================= *)
(* Assumption audit. Every line must print                            *)
(* "Closed under the global context".                                 *)
(* ================================================================= *)

Theorem priced_sorted_thiele_complete_over :
  T.thiele_complete_over (priced_machine G.sprop_eqb G.seval)
    (priced_language G.sprop_eqb G.sprop_eqb_eq G.seval G.sholds).
Proof.
  apply (priced_thiele_complete_over G.sprop_eqb G.sprop_eqb_eq G.seval
    G.sholds G.seval_iff).
  exists G.PSorted, 18, 20. split.
  - simpl. apply G.sortedb_iff. vm_compute. reflexivity.
  - simpl. intro H. apply G.sortedb_iff in H. vm_compute in H. discriminate H.
Qed.

Theorem priced_core_thiele_complete_over :
  T.thiele_complete_over (priced_machine G.cprop_eqb G.ceval)
    (priced_language G.cprop_eqb G.cprop_eqb_eq G.ceval G.cholds).
Proof.
  apply (priced_thiele_complete_over G.cprop_eqb G.cprop_eqb_eq G.ceval
    G.cholds G.ceval_iff).
  exists G.PZero, 0, 1. split; simpl; [reflexivity | discriminate].
Qed.

Print Assumptions priced_thiele_complete_over.
Print Assumptions priced_sorted_thiele_complete_over.
Print Assumptions priced_core_thiele_complete_over.
Print Assumptions priced_toll.
Print Assumptions priced_cert_system.
Print Assumptions priced_pay_reads_as_failed_check.
Print Assumptions priced_chain_iff.
Print Assumptions priced_thiele_complete.
Print Assumptions priced_sorted_thiele_complete.
Print Assumptions priced_core_thiele_complete.
