(** RecordMerge.v: the room argument's merge, found on the small machine
    itself, and a merge price the small machine's own price list meets.

    The room argument of Section 4 needs finiteness for one thing: to force
    the step that raises a permanent flag to merge two states. On the small
    machine of EarnedCore.v no counting is needed, because the merge can be
    exhibited. CERTIFY sends a state with the flag down and the same state
    with the flag up to one state, and COMMIT overwrites the channel, so two
    states that differ only in what the channel holds land on one state.
    FragmentSmall.v proves the CERTIFY merge [frag_small_certify_merges];
    this file adds the COMMIT merge and the consequence for every price
    list, with no finiteness premise anywhere.

    Then it makes the merge premise and clause (c) of Thiele-complete agree.
    Full merge pricing fails on the small machine, because a free DEC merges
    two full states [frag_small_not_merge_priced]. Record-layer merge
    pricing asks less: a move that sends two different states with the same
    two-counter configuration (line, A, B), the window of clause (a), to one
    state costs at least 1. Everything outside the window (versions, fact
    table, channel, trap latch, ledger, flag) is the record layer. A base
    move never merges two such states, so the small machine's own prices,
    base moves free and each record move 1, meet the premise; and every
    price list that meets it charges the flag-raising step.

    What is proved (every result closed under the global context):

      1. COMMIT merges: for every claim, two states that differ only in
         their channel land on one state [rm_commit_merges].
      2. Every merge-priced schedule, for the small machine's own step,
         charges CERTIFY and COMMIT at least 1 and obeys the toll, so the
         small machine with that schedule is a certification system; no
         finiteness is assumed [rm_merge_price_charges_record_moves,
         rm_toll_from_any_merge_price, rm_cert_system_from_merge_price].
      3. Record-layer merge pricing is implied by merge pricing
         [rm_merge_price_gives_record_price]. CERTIFY and COMMIT are
         record-layer merges [rm_certify_record_merge,
         rm_commit_record_merge]. No base move (INC, DEC, HALT) is one
         [rm_base_moves_no_record_merge], so the small machine's own price
         list meets the premise [rm_small_record_priced], while full merge
         pricing fails for it [frag_small_not_merge_priced].
      4. Every price list that meets record-layer merge pricing charges the
         flag-raising step at least 1: the toll, with no finiteness premise
         [rm_toll_from_record_price, rm_cert_system_from_record_price]. A
         price list with base moves free and record moves at 1 meets it,
         and it is the small machine's own [rm_record_price_and_exact_toll].

    Dependencies: Coq standard library, EarnedCore.v, ThieleComplete.v and
    FragmentSmall.v. No axioms, no Admitted.                               *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Minimal.ThieleComplete.
Require Import Minimal.FragmentSmall.
Require Minimal.EarnedCore.
Module E := Minimal.EarnedCore.

(* ================================================================= *)
(* 1. COMMIT merges.                                                  *)
(* ================================================================= *)

Lemma rm_fact_eqb_refl : forall f, E.fact_eqb f f = true.
Proof. intro f. apply E.fact_eqb_eq. reflexivity. Qed.

(* A core at line 1 with the claim about version 0 in its table and the
   given channel. *)
Definition rm_core (p : E.prop) (c : E.ctr) (ch : option E.fact) : E.core :=
  E.mkcore 0 0 0 0 1 [E.mkfact p c 0] ch false.

Lemma rm_commit_lands : forall p c ch,
  E.exec (E.mkst (rm_core p c ch) 0 false) (E.COMMIT p c) =
  E.mkst (E.commit_to (rm_core p c ch) (E.mkfact p c 0)) 1 false.
Proof.
  intros p c ch. unfold E.exec, E.cexec. simpl.
  assert (Hok : E.commit_ok (rm_core p c ch) p c = true).
  { unfold E.commit_ok, E.claim. simpl.
    replace (E.ver (rm_core p c ch) c) with 0 by (destruct c; reflexivity).
    rewrite rm_fact_eqb_refl. reflexivity. }
  rewrite Hok.
  replace (E.claim (rm_core p c ch) p c) with (E.mkfact p c 0)
    by (unfold E.claim; destruct c; reflexivity).
  reflexivity.
Qed.

Theorem rm_commit_merges : forall p c,
  ~ frag_injective E.state E.instr E.exec (E.COMMIT p c).
Proof.
  intros p c Hinj.
  assert (H : E.exec (E.mkst (rm_core p c None) 0 false) (E.COMMIT p c)
            = E.exec (E.mkst (rm_core p c (Some (E.mkfact p c 0))) 0 false) (E.COMMIT p c))
    by (rewrite !rm_commit_lands; reflexivity).
  apply Hinj in H. inversion H.
Qed.

(* ================================================================= *)
(* 2. Every merge-priced schedule charges the record moves.           *)
(* ================================================================= *)

Theorem rm_merge_price_charges_record_moves : forall cost' : E.instr -> nat,
  frag_merges_priced E.state E.instr E.exec cost' ->
  cost' E.CERTIFY >= 1 /\ forall p c, cost' (E.COMMIT p c) >= 1.
Proof.
  intros cost' H. split.
  - apply H, frag_small_certify_merges.
  - intros p c. apply H, rm_commit_merges.
Qed.

(* The toll, for any price list that charges every merge of the small
   machine's own step. Nothing is assumed about finiteness. *)
Theorem rm_toll_from_any_merge_price : forall cost' : E.instr -> nat,
  frag_merges_priced E.state E.instr E.exec cost' ->
  frag_toll E.state E.instr E.exec E.cert cost'.
Proof.
  intros cost' H s i H0 H1.
  destruct (E.only_certify_certifies s i H0 H1) as [-> _].
  apply (proj1 (rm_merge_price_charges_record_moves cost' H)).
Qed.

Definition rm_cert_system_from_merge_price (cost' : E.instr -> nat)
  (H : frag_merges_priced E.state E.instr E.exec cost') : CertificationSystem :=
  mk_cert_system E.state E.instr E.exec cost' E.cert
    (rm_toll_from_any_merge_price cost' H).

(* ================================================================= *)
(* 3. Record-layer merge pricing.                                     *)
(* ================================================================= *)

Section RecordLayer.

Variables (St Mv B : Type).
Variable step : St -> Mv -> St.
Variable cost : Mv -> nat.
(* The base part of a state; everything else is the record layer. *)
Variable base : St -> B.

(* A record-layer merge: two different states with the same base part
   land on one state. *)
Definition record_merge (m : Mv) : Prop :=
  exists a b, a <> b /\ base a = base b /\ step a m = step b m.

(* Record-layer merge pricing. *)
Definition record_merges_priced : Prop :=
  forall m, record_merge m -> cost m >= 1.

(* A record-layer merge is a merge, so merge pricing implies the
   record-layer premise. *)
Theorem rm_merge_price_gives_record_price :
  frag_merges_priced St Mv step cost -> record_merges_priced.
Proof.
  intros H m [a [b [Hab [_ Heq]]]]. apply H. intro Hinj. apply Hab, Hinj, Heq.
Qed.

End RecordLayer.

Arguments record_merge {St Mv B} step base m.
Arguments record_merges_priced {St Mv B} step cost base.

(* On the small machine the base part is the two-counter configuration,
   the window of clause (a): line, A, B. *)
Definition rm_base (s : E.state) : E.mconf := E.window (E.core_of s).

(* The flag pair: the same core, flag down and flag up. *)
Theorem rm_certify_record_merge : record_merge E.exec rm_base E.CERTIFY.
Proof.
  exists (E.mkst frag_k0 0 false), (E.mkst frag_k0 0 true).
  split; [intro H; inversion H |]. split; reflexivity.
Qed.

(* The channel pair: the same counters and line, the channel empty and
   full. *)
Theorem rm_commit_record_merge : forall p c,
  record_merge E.exec rm_base (E.COMMIT p c).
Proof.
  intros p c.
  exists (E.mkst (rm_core p c None) 0 false),
         (E.mkst (rm_core p c (Some (E.mkfact p c 0))) 0 false).
  split; [intro H; inversion H |]. split; [reflexivity |].
  rewrite !rm_commit_lands. reflexivity.
Qed.

Definition rm_is_base (i : E.instr) : bool :=
  match i with E.INC _ | E.DEC _ _ | E.HALT => true | _ => false end.

(* A base move keeps the trap latch, the table and the channel, and on a
   live state moves the version of the counter it writes by one. *)
Lemma rm_base_core : forall k i, rm_is_base i = true ->
  E.err (E.cexec k i) = E.err k /\ E.facts (E.cexec k i) = E.facts k /\
  E.chan (E.cexec k i) = E.chan k.
Proof.
  intros [a b va vb pc fs ch er] i Hi. unfold E.cexec. simpl.
  destruct er; [simpl; auto |].
  destruct i as [[|] | [|] j | | | |]; try discriminate; simpl; auto.
  - destruct a; simpl; auto.
  - destruct b; simpl; auto.
Qed.

Lemma rm_core_eq : forall k1 k2,
  E.ca k1 = E.ca k2 -> E.cb k1 = E.cb k2 -> E.va k1 = E.va k2 -> E.vb k1 = E.vb k2 ->
  E.pc k1 = E.pc k2 -> E.facts k1 = E.facts k2 -> E.chan k1 = E.chan k2 ->
  E.err k1 = E.err k2 -> k1 = k2.
Proof.
  intros [] [] ? ? ? ? ? ? ? ?; simpl in *; subst; reflexivity.
Qed.

(* No base move merges two states with the same configuration. *)
Theorem rm_base_moves_no_record_merge : forall i,
  rm_is_base i = true -> ~ record_merge E.exec rm_base i.
Proof.
  intros i Hi [[k1 m1 r1] [[k2 m2 r2] [Hne [Hb Heq]]]].
  apply Hne. unfold rm_base, E.window in Hb. simpl in Hb.
  injection Hb as Hpc Hca Hcb.
  unfold E.exec in Heq. simpl in Heq. injection Heq as Hk Hm Hr.
  assert (Hc0 : E.cost i = 0) by (destruct i; try discriminate; reflexivity).
  assert (Hf0 : E.fires k1 i = false /\ E.fires k2 i = false)
    by (destruct i; try discriminate; split; reflexivity).
  rewrite Hc0 in Hm. destruct Hf0 as [Hf1 Hf2]. rewrite Hf1, Hf2, !orb_false_r in Hr.
  assert (Hm' : m1 = m2) by lia. subst m2 r2.
  destruct (rm_base_core k1 i Hi) as [He1 [Hfa1 Hch1]].
  destruct (rm_base_core k2 i Hi) as [He2 [Hfa2 Hch2]].
  assert (Hee : E.err k1 = E.err k2) by (rewrite <- He1, <- He2, Hk; reflexivity).
  assert (Hfa : E.facts k1 = E.facts k2) by (rewrite <- Hfa1, <- Hfa2, Hk; reflexivity).
  assert (Hch : E.chan k1 = E.chan k2) by (rewrite <- Hch1, <- Hch2, Hk; reflexivity).
  f_equal.
  destruct k1 as [a1 b1 va1 vb1 pc1 fs1 ch1 er1].
  destruct k2 as [a2 b2 va2 vb2 pc2 fs2 ch2 er2].
  simpl in *. subst a2 b2 pc2 fs2 ch2 er2.
  unfold E.cexec in Hk. simpl in Hk.
  destruct er1.
  - (* both trapped: nothing moves *)
    exact Hk.
  - destruct i as [[|] | [|] j | | | |]; try discriminate; simpl in Hk.
    + injection Hk as Hv. subst. reflexivity.
    + injection Hk as Hv. subst. reflexivity.
    + destruct a1; simpl in Hk; injection Hk; intros; subst; reflexivity.
    + destruct b1; simpl in Hk; injection Hk; intros; subst; reflexivity.
    + exact Hk.
Qed.

(* The small machine's own prices meet the record-layer premise. *)
Theorem rm_small_record_priced : record_merges_priced E.exec E.cost rm_base.
Proof.
  intros i Hm. destruct i eqn:Hi; simpl; try lia;
    exfalso; apply (rm_base_moves_no_record_merge i); subst; auto.
Qed.

(* ================================================================= *)
(* 4. The toll from record-layer merge pricing, no finiteness.        *)
(* ================================================================= *)

Theorem rm_toll_from_record_price : forall cost' : E.instr -> nat,
  record_merges_priced E.exec cost' rm_base ->
  frag_toll E.state E.instr E.exec E.cert cost'.
Proof.
  intros cost' H s i H0 H1.
  destruct (E.only_certify_certifies s i H0 H1) as [-> _].
  apply H, rm_certify_record_merge.
Qed.

Definition rm_cert_system_from_record_price (cost' : E.instr -> nat)
  (H : record_merges_priced E.exec cost' rm_base) : CertificationSystem :=
  mk_cert_system E.state E.instr E.exec cost' E.cert (rm_toll_from_record_price cost' H).

(* Clause (c)'s price list (base moves 0, record moves 1) is the small
   machine's own; it meets the record-layer premise, every price list that
   meets the premise obeys the toll, and full merge pricing still fails. *)
Theorem rm_record_price_and_exact_toll :
  (forall i, E.cost i = if rm_is_base i then 0 else 1) /\
  record_merges_priced E.exec E.cost rm_base /\
  (forall cost' : E.instr -> nat, record_merges_priced E.exec cost' rm_base ->
     frag_toll E.state E.instr E.exec E.cert cost') /\
  ~ frag_merges_priced E.state E.instr E.exec E.cost.
Proof.
  split; [intros []; reflexivity |].
  split; [exact rm_small_record_priced |].
  split; [exact rm_toll_from_record_price | exact frag_small_not_merge_priced].
Qed.

(* ================================================================= *)
(* Assumption audit. Every line must print                            *)
(* "Closed under the global context".                                 *)
(* ================================================================= *)

Print Assumptions rm_commit_merges.
Print Assumptions rm_merge_price_charges_record_moves.
Print Assumptions rm_toll_from_any_merge_price.
Print Assumptions rm_cert_system_from_merge_price.
Print Assumptions rm_merge_price_gives_record_price.
Print Assumptions rm_certify_record_merge.
Print Assumptions rm_commit_record_merge.
Print Assumptions rm_base_moves_no_record_merge.
Print Assumptions rm_small_record_priced.
Print Assumptions rm_toll_from_record_price.
Print Assumptions rm_cert_system_from_record_price.
Print Assumptions rm_record_price_and_exact_toll.
