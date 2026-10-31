(** CasperFFG: accountable safety for Casper FFG.

    This is a transcription of [Core/AccountableSafety.v] from the Casper
    verification team's casper-proofs, commit
    d8fe05df57e59909bf5c3392579e66ac1b78dab8
    (https://github.com/runtimeverification/casper-proofs), itself based on
    Yoichi Hirai's CasperOneMessage.thy. The definitions follow the original
    one for one. The proofs are rewritten for the Coq standard library,
    without mathcomp or CoqHammer.

    Two choices differ from the original, and neither weakens it. Validator
    sets are predicates rather than finite sets; no proof uses finiteness,
    so the statement covers the finite case. The two assumptions of the
    original section (quorum intersection, at most one parent per hash) are
    fields of [CasperSetting], so every theorem states them as premises.

    Accountable safety: if two blocks on different branches are both
    finalized, then a set of validators in the second quorum class (the
    "1/3" sets) has broken a slashing condition.

    Copyright (c) 2018 Casper verification team. All Rights Reserved.
    University of Illinois/NCSA Open Source License.
    Copyright (c) 2009-2015 University of Illinois at Urbana-Champaign.
    All rights reserved.
    Developed by: The University of Texas at Austin; Runtime Verification, Inc.
    Permission is hereby granted, free of charge, to any person obtaining a
    copy of this software and associated documentation files (the
    "Software"), to deal with the Software without restriction, including
    without limitation the rights to use, copy, modify, merge, publish,
    distribute, sublicense, and/or sell copies of the Software, and to
    permit persons to whom the Software is furnished to do so, subject to
    the following conditions: Redistributions of source code must retain the
    above copyright notice, this list of conditions and the following
    disclaimers. Redistributions in binary form must reproduce the above
    copyright notice, this list of conditions and the following disclaimers
    in the documentation and/or other materials provided with the
    distribution. Neither the names of the Casper verification team, The
    University of Texas at Austin, Runtime Verification, Inc., nor the names
    of its contributors may be used to endorse or promote products derived
    from this Software without specific prior written permission.
    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
    OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
    MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN
    NO EVENT SHALL THE CONTRIBUTORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
    CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT
    OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR
    THE USE OR OTHER DEALINGS WITH THE SOFTWARE. *)

(* SCOPE NOTE: standalone proof scope. This is a model of the Casper FFG
   specification, ported from its authors' proof. It imports no machine
   semantics on purpose: it is compared with the record axis in prose and
   in CasperRecordReading, not built from a machine. *)

From Coq Require Import Arith.PeanoNat Lia Relations.

(** The static setting: validators, hashes, the two quorum classes and their
    intersection property, and the block tree. *)
Record CasperSetting : Type := {
  Validator : Type;
  Hash : Type;
  (** All sets containing "2/3" of all validators or more. *)
  quorum_1 : (Validator -> Prop) -> Prop;
  (** All sets containing "1/3" of all validators or more. *)
  quorum_2 : (Validator -> Prop) -> Prop;
  quorums_intersection : forall q1 q2, quorum_1 q1 -> quorum_1 q2 ->
    exists q3, quorum_2 q3 /\ (forall n, q3 n -> q1 n) /\ (forall n, q3 n -> q2 n);
  (** [hash_parent h1 h2]: h1 is the parent of h2. *)
  hash_parent : Hash -> Hash -> Prop;
  genesis : Hash;
  hash_at_most_one_parent : forall h1 h2 h3,
    hash_parent h2 h1 -> hash_parent h3 h1 -> h2 = h3
}.

Section CasperOneMessage.

Variable C : CasperSetting.

(** The global state records the votes cast by validators: target hash,
    target epoch (distance from genesis), and source epoch. *)
Record State : Type := mkSt {
  vote_msg : Validator C -> Hash C -> nat -> nat -> bool
}.

Definition hash_ancestor (h1 h2 : Hash C) : Prop :=
  clos_refl_trans_1n _ (hash_parent C) h1 h2.

Lemma hash_ancestor_base : forall h1 h2, hash_parent C h1 h2 -> hash_ancestor h1 h2.
Proof. intros h1 h2 H. econstructor; [exact H | constructor]. Qed.

Lemma hash_ancestor_concat : forall h1 h2 h3,
  hash_ancestor h2 h3 -> hash_ancestor h1 h2 -> hash_ancestor h1 h3.
Proof.
  intros h1 h2 h3 H23 H12. induction H12 as [| x y z Hxy _ IH]; [exact H23 |].
  econstructor; [exact Hxy | exact (IH H23)].
Qed.

Lemma hash_ancestor_other : forall h1 h2 p,
  hash_ancestor h1 h2 -> ~ hash_ancestor p h2 -> ~ hash_ancestor p h1.
Proof. intros h1 h2 p H12 Hp2 Hp1. apply Hp2. exact (hash_ancestor_concat _ _ _ H12 Hp1). Qed.

(** The first hash is an ancestor of the second at the indicated distance. *)
Inductive nth_ancestor : nat -> Hash C -> Hash C -> Prop :=
| nth_ancestor_0 : forall h1, nth_ancestor 0 h1 h1
| nth_ancestor_nth : forall n h1 h2 h3,
    nth_ancestor n h1 h2 -> hash_parent C h2 h3 -> nth_ancestor (S n) h1 h3.

Lemma nth_ancestor_ancestor : forall n h1 h2, nth_ancestor n h1 h2 -> hash_ancestor h1 h2.
Proof.
  intros n h1 h2 H. induction H as [h | n h1 h2 h3 _ IH Hp]; [constructor |].
  exact (hash_ancestor_concat _ _ _ (hash_ancestor_base _ _ Hp) IH).
Qed.

(** "2/3" or more of validators have voted for a justified link. *)
Definition justified_link (s : State) (q : Validator C -> Prop)
    (parent : Hash C) (pre : nat) (new : Hash C) (now : nat) : Prop :=
  quorum_1 C q /\
  (forall n, q n -> vote_msg s n new now pre = true) /\
  nth_ancestor (now - pre) parent new /\
  now > pre.

Lemma justified_means_ancestor : forall s q parent pre new now,
  justified_link s q parent pre new now -> hash_ancestor parent new.
Proof. intros s q parent pre new now [_ [_ [Hn _]]]. exact (nth_ancestor_ancestor _ _ _ Hn). Qed.

(** The genesis block is justified, and blocks reachable by a justified link
    are justified. *)
Inductive justified : State -> Hash C -> nat -> Prop :=
| orig : forall s, justified s (genesis C) 0
| follow : forall s parent pre q new now,
    justified s parent pre ->
    justified_link s q parent pre new now ->
    justified s new now.

(** Finalized blocks are justified and have a justified link to a child. *)
Definition finalized (s : State) (q : Validator C -> Prop) (h : Hash C) (v : nat)
    (child : Hash C) : Prop :=
  hash_parent C h child /\ justified s h v /\ justified_link s q h v child (S v).

(** Blocks on different branches are both finalized. *)
Definition finalization_fork (s : State) : Prop :=
  exists h1 h2 q1 q2 v1 v2 c1 c2,
    finalized s q1 h1 v1 c1 /\
    finalized s q2 h2 v2 c2 /\
    ~ hash_ancestor h2 h1 /\ ~ hash_ancestor h1 h2 /\ h1 <> h2.

(** Validator slashing conditions. *)
Definition slashed_dbl_vote (s : State) (n : Validator C) : Prop :=
  exists h1 h2, h1 <> h2 /\ exists v s1 s2,
    vote_msg s n h1 v s1 = true /\ vote_msg s n h2 v s2 = true.

Definition slashed_surround (s : State) (n : Validator C) : Prop :=
  exists h1 h2 v1 v2 s1 s2,
    vote_msg s n h1 v1 s1 = true /\
    vote_msg s n h2 v2 s2 = true /\
    v1 > v2 /\ s2 > s1.

Definition slashed (s : State) (n : Validator C) : Prop :=
  slashed_dbl_vote s n \/ slashed_surround s n.

(** "1/3" or more of validators are slashed. *)
Definition quorum_slashed (s : State) : Prop :=
  exists q, quorum_2 C q /\ forall n, q n -> slashed s n.

(** * Proofs *)

Lemma link_epochs : forall s q h2 v2 h1 v1,
  justified_link s q h2 v2 h1 v1 -> v1 > v2.
Proof. intros s q h2 v2 h1 v1 [_ [_ [_ H]]]. exact H. Qed.

(** Two quorum_1 sets whose members each cast one of two votes leave a
    quorum_2 set of validators who cast both. *)
Lemma both_votes : forall (q1 q2 : Validator C -> Prop) (P1 P2 : Validator C -> Prop),
  quorum_1 C q1 -> quorum_1 C q2 ->
  (forall n, q1 n -> P1 n) -> (forall n, q2 n -> P2 n) ->
  exists q, quorum_2 C q /\ forall n, q n -> P1 n /\ P2 n.
Proof.
  intros q1 q2 P1 P2 Hq1 Hq2 H1 H2.
  destruct (quorums_intersection C q1 q2 Hq1 Hq2) as [q [Hq [Hin1 Hin2]]].
  exists q. split; [exact Hq |]. intros n Hn. split; [apply H1, Hin1 | apply H2, Hin2]; exact Hn.
Qed.

(** A link into the epoch just after a finalization, on another branch, is a
    double vote by a quorum_2 set. *)
Lemma dbl_vote_case : forall s q1 q2 h2 v2 h1 h3 v3 c3,
  justified_link s q1 h2 v2 h1 (S v3) ->
  finalized s q2 h3 v3 c3 ->
  ~ hash_ancestor h3 h1 ->
  quorum_slashed s.
Proof.
  intros s q1 q2 h2 v2 h1 h3 v3 c3 [Hq1 [Hv1 _]] [Hp [_ [Hq2 [Hv2 _]]]] Hh.
  destruct (both_votes q1 q2 _ _ Hq1 Hq2 Hv1 Hv2) as [q [Hq Hboth]].
  exists q. split; [exact Hq |]. intros n Hn. left.
  destruct (Hboth n Hn) as [Ha Hb].
  exists h1, c3. split.
  - intros ->. apply Hh. exact (hash_ancestor_base _ _ Hp).
  - exists (S v3), v2, v3. split; assumption.
Qed.

(** A link that jumps over a finalization, on another branch, is a surround
    vote by a quorum_2 set. *)
Lemma surround_case : forall s q1 q2 h2 v2 h1 v1 h3 v3 c3,
  justified_link s q1 h2 v2 h1 v1 ->
  finalized s q2 h3 v3 c3 ->
  S v3 < v1 -> v2 < v3 ->
  quorum_slashed s.
Proof.
  intros s q1 q2 h2 v2 h1 v1 h3 v3 c3 [Hq1 [Hv1 _]] [_ [_ [Hq2 [Hv2 _]]]] Hlt Hlt'.
  destruct (both_votes q1 q2 _ _ Hq1 Hq2 Hv1 Hv2) as [q [Hq Hboth]].
  exists q. split; [exact Hq |]. intros n Hn. right.
  destruct (Hboth n Hn) as [Ha Hb].
  exists h1, c3, v1, (S v3), v2, v3. repeat split; assumption.
Qed.

Lemma crossing_link_slashes : forall s q1 q2 h2 v2 h1 h3 v1 v3 c3,
  justified_link s q1 h2 v2 h1 v1 ->
  finalized s q2 h3 v3 c3 ->
  v1 > v3 ->
  ~ hash_ancestor h3 h1 ->
  v2 < v3 ->
  quorum_slashed s.
Proof.
  intros s q1 q2 h2 v2 h1 h3 v1 v3 c3 Hj Hf Hv Hh Hv'.
  destruct (Nat.eq_dec v1 (S v3)) as [-> | Hne].
  - exact (dbl_vote_case s q1 q2 h2 v2 h1 h3 v3 c3 Hj Hf Hh).
  - apply (surround_case s q1 q2 h2 v2 h1 v1 h3 v3 c3 Hj Hf); lia.
Qed.

(** Distinct targets of two justified links into the same epoch give a
    quorum_2 set of double voters.  Stating the constructive implication
    directly avoids deciding equality on the abstract hash type. *)
Lemma same_epoch_distinct_slashes : forall s q q1 parent1 pre1 h1 v1 parent pre new now,
  justified_link s q parent pre new now ->
  justified_link s q1 parent1 pre1 h1 v1 ->
  now = v1 ->
  h1 <> new ->
  quorum_slashed s.
Proof.
  intros s q q1 parent1 pre1 h1 v1 parent pre new now
    [Hq [Hv _]] [Hq1 [Hv1 _]] -> Hne.
  destruct (both_votes q q1 _ _ Hq Hq1 Hv Hv1) as [q2 [Hq2 Hboth]].
  exists q2. split; [exact Hq2 |]. intros n Hn. left.
  destruct (Hboth n Hn) as [Ha Hb].
  exists new, h1. split; [intro H; apply Hne; symmetry; exact H |].
  exists v1, pre, pre1. split; assumption.
Qed.

(** Two distinct justified blocks at one epoch constructively expose a
    double-voting quorum. *)
Lemma distinct_justified_same_epoch_slashes : forall s h1 h2 v,
  justified s h1 v ->
  justified s h2 v ->
  h1 <> h2 ->
  quorum_slashed s.
Proof.
  intros s h1 h2 v Hj1 Hj2 Hneq.
  inversion Hj1 as [s1 | s1 parent1 pre1 q1 new1 now1 Hjp1 Hlink1]; subst;
    inversion Hj2 as [s2 | s2 parent2 pre2 q2 new2 now2 Hjp2 Hlink2]; subst.
  - exfalso. apply Hneq. reflexivity.
  - pose proof (link_epochs _ _ _ _ _ _ Hlink2). lia.
  - pose proof (link_epochs _ _ _ _ _ _ Hlink1). lia.
  - exact (same_epoch_distinct_slashes _ _ _ _ _ _ _ _ _ _ _
      Hlink1 Hlink2 eq_refl (fun Heq => Hneq (eq_sym Heq))).
Qed.

Lemma distinct_justified_epochs : forall s h1 v1 h2 v2,
  justified s h2 v2 ->
  justified s h1 v1 ->
  ~ quorum_slashed s ->
  h1 <> h2 ->
  v2 <> v1.
Proof.
  intros s h1 v1 h2 v2 Hj2 Hj1 Hs Hneq Heq. subst v2.
  apply Hs. exact (distinct_justified_same_epoch_slashes _ _ _ _ Hj2 Hj1
    (fun Heq => Hneq (eq_sym Heq))).
Qed.

Lemma finalized_epoch_distinct : forall s q2 h2 v2 xa parent pre,
  finalized s q2 h2 v2 xa ->
  ~ quorum_slashed s ->
  justified s parent pre ->
  parent <> h2 ->
  v2 <> pre.
Proof.
  intros s q2 h2 v2 xa parent pre [_ [Hj _]] Hs Hjp Hne.
  exact (distinct_justified_epochs s parent pre h2 v2 Hj Hjp Hs Hne).
Qed.

(** A justified block on another branch, above a finalized block, means a
    quorum_2 set is slashed. Strong induction on the epoch gap. *)
Lemma non_equal_case_ind : forall s q2 h2 v2 xa,
  finalized s q2 h2 v2 xa ->
  forall k v1 h1, v1 - v2 = k ->
  justified s h1 v1 ->
  ~ hash_ancestor h2 h1 ->
  h1 <> h2 ->
  v1 > v2 ->
  quorum_slashed s.
Proof.
  intros s q2 h2 v2 xa Hf k.
  induction k as [k IH] using (well_founded_induction Wf_nat.lt_wf).
  intros v1 h1 Hk Hj Hh Hh' Hv.
  destruct Hj as [s0 | s0 parent pre q new now Hjp Hlink]; [lia |].
  assert (Hp : ~ hash_ancestor h2 parent)
    by exact (hash_ancestor_other _ _ _ (justified_means_ancestor _ _ _ _ _ _ Hlink) Hh).
  assert (Hpe : parent <> h2) by (intros ->; apply Hp; constructor).
  pose proof (link_epochs _ _ _ _ _ _ Hlink) as Hpre.
  destruct (Nat.lt_trichotomy v2 pre) as [Hlt | [Heq | Hgt]].
  - apply (IH (pre - v2)) with (v1 := pre) (h1 := parent); try assumption; lia.
  - subst pre. exact (distinct_justified_same_epoch_slashes _ _ _ _
      Hjp (proj1 (proj2 Hf)) Hpe).
  - exact (crossing_link_slashes _ _ _ _ _ _ _ _ _ _ Hlink Hf Hv Hh Hgt).
Qed.

Lemma non_equal_case : forall s q1 q2 h1 v1 x h2 v2 xa,
  finalized s q1 h1 v1 x ->
  finalized s q2 h2 v2 xa ->
  ~ hash_ancestor h2 h1 ->
  h1 <> h2 ->
  v1 > v2 ->
  quorum_slashed s.
Proof.
  intros s q1 q2 h1 v1 x h2 v2 xa [_ [Hj _]] Hf2 Hh Hne Hv.
  exact (non_equal_case_ind s q2 h2 v2 xa Hf2 (v1 - v2) v1 h1 eq_refl Hj Hh Hne Hv).
Qed.

Lemma equal_case : forall s q1 h1 v1 x q2 h2 xa,
  finalized s q1 h1 v1 x ->
  finalized s q2 h2 v1 xa ->
  h1 <> h2 ->
  quorum_slashed s.
Proof.
  intros s q1 h1 v1 x q2 h2 xa [Hp1 [_ [Hq1 [Hv1 _]]]] [Hp2 [_ [Hq2 [Hv2 _]]]] Hh.
  destruct (both_votes q1 q2 _ _ Hq1 Hq2 Hv1 Hv2) as [q [Hq Hboth]].
  exists q. split; [exact Hq |]. intros n Hn. left.
  destruct (Hboth n Hn) as [Ha Hb].
  exists x, xa. split.
  - intros ->. apply Hh. exact (hash_at_most_one_parent C _ _ _ Hp1 Hp2).
  - exists (S v1), v1, v1. split; assumption.
Qed.

Lemma safety' : forall s q1 h1 v1 x q2 h2 v2 xa,
  finalized s q1 h1 v1 x ->
  finalized s q2 h2 v2 xa ->
  ~ hash_ancestor h2 h1 ->
  ~ hash_ancestor h1 h2 ->
  h1 <> h2 ->
  quorum_slashed s.
Proof.
  intros s q1 h1 v1 x q2 h2 v2 xa Hf Hf' Hh Hh' Hn.
  destruct (Nat.lt_trichotomy v1 v2) as [Hlt | [-> | Hgt]].
  - apply (non_equal_case s q2 q1 h2 v2 xa h1 v1 x Hf' Hf Hh'); [intro H; apply Hn; symmetry; exact H | exact Hlt].
  - exact (equal_case s q1 h1 v2 x q2 h2 xa Hf Hf' Hn).
  - exact (non_equal_case s q1 q2 h1 v1 x h2 v2 xa Hf Hf' Hh Hn Hgt).
Qed.

Theorem accountable_safety : forall s, finalization_fork s -> quorum_slashed s.
Proof.
  intros s [h1 [h2 [q1 [q2 [v1 [v2 [c1 [c2 [Hf1 [Hf2 [Hh [Hh' Hn]]]]]]]]]]]].
  exact (safety' s q1 h1 v1 c1 q2 h2 v2 c2 Hf1 Hf2 Hh Hh' Hn).
Qed.

End CasperOneMessage.

(** The setting's assumptions can hold: one validator whose singleton set is
    in both quorum classes, and a chain of hashes numbered from genesis. *)
Definition chain_setting : CasperSetting := {|
  Validator := unit;
  Hash := nat;
  quorum_1 := fun q => q tt;
  quorum_2 := fun q => q tt;
  quorums_intersection := fun q1 q2 H1 H2 =>
    ex_intro _ (fun n => q1 n /\ q2 n)
      (conj (conj H1 H2) (conj (fun n H => proj1 H) (fun n H => proj2 H)));
  hash_parent := fun h1 h2 => h2 = S h1;
  genesis := 0;
  hash_at_most_one_parent := fun h1 h2 h3 H2 H3 =>
    eq_add_S _ _ (eq_trans (eq_sym H2) H3)
|}.

Print Assumptions accountable_safety.
