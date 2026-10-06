(** NecEEnt.v: which hypotheses of structural entitlement carry weight.

    The book's Theorem "Structural entitlement, over any certification
    system" (ent_cs_entitlement) and its machine form "Structural
    entitlement represented" (ent_representation) list their premises. This
    file settles each one:

    - Four of them can be dropped with nothing lost: the strictness half of
      (H1) and "w is not in the posterior" (both follow from the
      distinguishing rival), the decoder premise (H3), and |Omega'| > 0
      (forced by the covering once the prior has a member, and harmless
      when it has none). The stronger statements are
      nec_e_cs_entitlement_stronger and nec_e_representation_stronger.
    - Every other premise is needed: for each one there is a run of the
      small machine (read as a certification system for ent-cs) meeting
      all the other premises with the conclusion false.
    - The bound is attained: for every k >= 1 a run with bill exactly k
      narrows by exactly k index bits, and from a clean start, for every
      k >= 3, a certified run with exactly k record moves narrows by
      exactly k bits. Below 3 nothing certifies from a clean start
      (certificate_costs_three).
    - A tree is as wide as two to its depth exactly when it is the
      complete tree of that depth.

    Dependencies: ThieleComplete.v, EntitlementSmall.v, EntitlementMore2.v,
    EarnedCore.v. No axioms.                                              *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Minimal.ThieleComplete Minimal.EntitlementSmall Minimal.EntitlementMore2.
Require Minimal.EarnedCore.
Module E := Minimal.EarnedCore.

(* ================================================================= *)
(* 1. The arithmetic without |Omega'| > 0.                            *)
(* ================================================================= *)

Lemma nec_e_cover_bits_any : forall a b l,
  a <= l * b -> Nat.log2_up a - Nat.log2_up b <= Nat.log2_up l.
Proof.
  intros a b l H. destruct b as [| b].
  - rewrite Nat.mul_0_r in H. assert (a = 0) by lia. subst a. simpl. lia.
  - apply ent_cover_bits; [lia | exact H].
Qed.

(* Paid narrowing, counted, with no positivity premise. *)
Theorem nec_e_cs_count_any : forall (C : CertificationSystem) {X : Type}
    (tr : list (cs_instr C)) (prior post : list X) (T : ent_tree),
  length prior <= ent_leaves T * length post ->
  ent_depth T <= ent_cs_paid C tr ->
  Nat.log2_up (length prior) - Nat.log2_up (length post) <= ent_cs_bill C tr.
Proof.
  intros C X tr prior post T Hcov Hpaid.
  pose proof (nec_e_cover_bits_any _ _ _ Hcov).
  pose proof (ent_log2_leaves_le_depth T). pose proof (ent_cs_paid_le_bill C tr). lia.
Qed.

(* The weighted form, with no positivity premise. *)
Theorem nec_e_weighted_bits_any : forall {X : Type} (T : ent_tree) (prior post : list (X * nat)),
  ent2_wcovers T prior post ->
  Nat.log2_up (ent2_mass prior) - Nat.log2_up (ent2_mass post) <= ent_depth T.
Proof.
  intros X T prior post Hc.
  pose proof (nec_e_cover_bits_any _ _ _ Hc). pose proof (ent_log2_leaves_le_depth T). lia.
Qed.

(* The fibre covering forces a non-empty posterior once the prior has a
   member. *)
Lemma nec_e_reduction_post_pos : forall {X O : Type} (r : X -> O) T (prior post : list X) w,
  In w prior -> ent_reduction r T prior post -> 0 < length post.
Proof.
  intros X O r T prior post w Hw [F [Hass _]].
  destruct (Hass w Hw) as [t [Ht _]]. destruct post; [destruct Ht | simpl; lia].
Qed.

(* ================================================================= *)
(* 2. ent-cs: the stronger statement.                                  *)
(* ================================================================= *)

(* Structural entitlement on a certification system with four premises
   fewer: no strictness half of (H1), no "w not in the posterior", no
   decoder premise (H3), no |Omega'| > 0. *)
Theorem nec_e_cs_entitlement_stronger :
  forall (C : CertificationSystem) {X O : Type} (tr : list (cs_instr C)) (s : cs_state C)
         (obs : X -> O) (eqb : O -> O -> bool) (prior post : list X) (T : ent_tree),
    (forall o1 o2, eqb o1 o2 = true <-> o1 = o2) ->
    incl post prior ->
    (exists w, In w prior /\ ent_distinguishes obs w post) ->
    cs_cert C s = false ->
    cs_cert C (ent_cs_run C tr s) = true ->
    length prior <= ent_leaves T * length post ->
    ent_depth T <= ent_cs_paid C tr ->
    ent_strictly_stronger (ent_member eqb obs post) (ent_member eqb obs prior) /\
    (exists pre i rest, tr = pre ++ i :: rest /\
       cs_cert C (ent_cs_run C pre s) = false /\
       cs_cert C (cs_step C (ent_cs_run C pre s) i) = true /\ cs_cost C i >= 1) /\
    Nat.log2_up (length prior) - Nat.log2_up (length post) <= ent_cs_bill C tr.
Proof.
  intros C X O tr s obs eqb prior post T Heq Hincl [w [Hw Hd]] H0 H1 Hcov Hp.
  split; [apply (ent_narrowing_strengthens eqb obs prior post w Heq Hincl Hw Hd) |].
  split; [apply ent_cs_raising_step; assumption |].
  apply (nec_e_cs_count_any C tr prior post T Hcov Hp).
Qed.

(* The book's statement is a corollary. *)
Corollary nec_e_cs_entitlement_from_stronger :
  forall (C : CertificationSystem) {X O : Type} (tr : list (cs_instr C)) (s : cs_state C)
         (d : list (cs_instr C) -> O) (obs : X -> O) (eqb : O -> O -> bool)
         (prior post : list X) (T : ent_tree),
    (forall o1 o2, eqb o1 o2 = true <-> o1 = o2) ->
    ent_strict_sublist post prior ->
    (exists w, In w prior /\ ~ In w post /\ ent_distinguishes obs w post) ->
    cs_cert C s = false ->
    cs_cert C (ent_cs_run C tr s) = true ->
    ent_member eqb obs post (d tr) = true ->
    0 < length post ->
    length prior <= ent_leaves T * length post ->
    ent_depth T <= ent_cs_paid C tr ->
    ent_strictly_stronger (ent_member eqb obs post) (ent_member eqb obs prior) /\
    (exists pre i rest, tr = pre ++ i :: rest /\
       cs_cert C (ent_cs_run C pre s) = false /\
       cs_cert C (cs_step C (ent_cs_run C pre s) i) = true /\ cs_cost C i >= 1) /\
    Nat.log2_up (length prior) - Nat.log2_up (length post) <= ent_cs_bill C tr.
Proof.
  intros C X O tr s d obs eqb prior post T Heq [Hincl _] [w [Hw [_ Hd]]] H0 H1 _ _ Hcov Hp.
  apply (nec_e_cs_entitlement_stronger C tr s obs eqb prior post T Heq Hincl
           (ex_intro _ w (conj Hw Hd)) H0 H1 Hcov Hp).
Qed.

(* ================================================================= *)
(* 3. The small machine as a certification system, and its data.      *)
(* ================================================================= *)

Definition nec_e_ecs : CertificationSystem := as_cert_system earned_machine E.a2.

Lemma nec_e_ecs_run : forall tr s, ent_cs_run nec_e_ecs tr s = E.run tr s.
Proof. induction tr as [| i tr IH]; intro s; simpl; [reflexivity | apply IH]. Qed.

(* The three-move chain on "A is 0". *)
Definition nec_e_chain : list E.instr := [E.CHECK E.PZero E.CA; E.COMMIT E.PZero E.CA; E.CERTIFY].

(* The two-rival narrowing used below: prior [0; 1], posterior [0]. *)
Definition nec_e_pr2 : list nat := [0; 1].
Definition nec_e_po1 : list nat := [0].

(* The sixteen-rival narrowing: prior 0..15, posterior [0], 4 index bits. *)
Definition nec_e_pr16 : list nat := seq 0 16.

Lemma nec_e_bits16 : Nat.log2_up (length nec_e_pr16) - Nat.log2_up (length nec_e_po1) = 4.
Proof. vm_compute. reflexivity. Qed.

Ltac nec_e_splits := repeat match goal with |- _ /\ _ => split end.

(* Two tests are not strictly stronger when they agree everywhere. *)
Lemma nec_e_not_strict_if_equal : forall {O : Type} (P Q : O -> bool),
  (forall o, P o = Q o) -> ~ ent_strictly_stronger P Q.
Proof.
  intros O P Q H [_ [o [H1 H2]]]. rewrite H in H1. congruence.
Qed.

(* The fibre covering of 0..15 by the single survivor 0, read through a
   constant representative observation, with the complete tree of depth 4. *)
Lemma nec_e_red16 : ent_reduction (fun _ : nat => 0) (ent_complete 4) nec_e_pr16 nec_e_po1.
Proof.
  exists (fun _ => nec_e_pr16). split; [| split].
  - intros x Hx. exists 0. split; [left; reflexivity | split; [exact Hx | reflexivity]].
  - vm_compute. lia.
  - intros t _. vm_compute. lia.
Qed.

Lemma nec_e_red2 : ent_reduction (fun _ : nat => 0) (ent_complete 1) nec_e_pr2 nec_e_po1.
Proof.
  exists (fun _ => nec_e_pr2). split; [| split].
  - intros x Hx. exists 0. split; [left; reflexivity | split; [exact Hx | reflexivity]].
  - vm_compute. lia.
  - intros t _. vm_compute. lia.
Qed.

Lemma nec_e_w16 : exists w, In w nec_e_pr16 /\ ~ In w nec_e_po1 /\
  ent_distinguishes (fun x : nat => x) w nec_e_po1.
Proof.
  exists 1. split; [unfold nec_e_pr16; simpl; auto |].
  split; [simpl; intros [H | []]; discriminate | intros t [<- | []]; discriminate].
Qed.

Lemma nec_e_w2 : exists w, In w nec_e_pr2 /\ ~ In w nec_e_po1 /\
  ent_distinguishes (fun x : nat => x) w nec_e_po1.
Proof.
  exists 1. split; [simpl; auto |].
  split; [simpl; intros [H | []]; discriminate | intros t [<- | []]; discriminate].
Qed.

Lemma nec_e_sub16 : ent_strict_sublist nec_e_po1 nec_e_pr16.
Proof.
  split; [intros x [<- | []]; unfold nec_e_pr16; simpl; auto |].
  exists 1. split; [unfold nec_e_pr16; simpl; auto | simpl; intros [H | []]; discriminate].
Qed.

Lemma nec_e_sub2 : ent_strict_sublist nec_e_po1 nec_e_pr2.
Proof.
  split; [intros x [<- | []]; simpl; auto |].
  exists 1. split; [simpl; auto | simpl; intros [H | []]; discriminate].
Qed.

(* ================================================================= *)
(* 4. ent-cs: each remaining premise is needed.                        *)
(* ================================================================= *)

(* The equality test must be sound: with a test that says yes to
   everything, every other premise holds and conclusion (1) fails. *)
Theorem nec_e_cs_needs_eqb_sound :
  let eqb := fun _ _ : nat => true in
  (forall o, eqb o o = true) /\
  ent_strict_sublist nec_e_po1 nec_e_pr2 /\
  (exists w, In w nec_e_pr2 /\ ~ In w nec_e_po1 /\ ent_distinguishes (fun x => x) w nec_e_po1) /\
  cs_cert nec_e_ecs (E.start 0 0) = false /\
  cs_cert nec_e_ecs (ent_cs_run nec_e_ecs nec_e_chain (E.start 0 0)) = true /\
  ent_member eqb (fun x => x) nec_e_po1 0 = true /\
  0 < length nec_e_po1 /\
  length nec_e_pr2 <= ent_leaves (ent_complete 1) * length nec_e_po1 /\
  ent_depth (ent_complete 1) <= ent_cs_paid nec_e_ecs nec_e_chain /\
  ~ ent_strictly_stronger (ent_member eqb (fun x => x) nec_e_po1)
                          (ent_member eqb (fun x => x) nec_e_pr2).
Proof.
  intro eqb. nec_e_splits.
  - intro o. reflexivity.
  - exact nec_e_sub2.
  - exact nec_e_w2.
  - reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - simpl. lia.
  - vm_compute. lia.
  - vm_compute. lia.
  - apply nec_e_not_strict_if_equal. intro o. reflexivity.
Qed.

(* The equality test must say yes on equal observations: a sound test
   that is reflexive only at 0 meets every other premise (the decoder
   reads 0) and conclusion (1) fails. *)
Theorem nec_e_cs_needs_eqb_refl :
  let eqb := fun a b : nat => Nat.eqb a b && Nat.eqb a 0 in
  (forall o1 o2, eqb o1 o2 = true -> o1 = o2) /\
  ent_strict_sublist nec_e_po1 nec_e_pr2 /\
  (exists w, In w nec_e_pr2 /\ ~ In w nec_e_po1 /\ ent_distinguishes (fun x => x) w nec_e_po1) /\
  cs_cert nec_e_ecs (E.start 0 0) = false /\
  cs_cert nec_e_ecs (ent_cs_run nec_e_ecs nec_e_chain (E.start 0 0)) = true /\
  ent_member eqb (fun x => x) nec_e_po1 0 = true /\
  0 < length nec_e_po1 /\
  length nec_e_pr2 <= ent_leaves (ent_complete 1) * length nec_e_po1 /\
  ent_depth (ent_complete 1) <= ent_cs_paid nec_e_ecs nec_e_chain /\
  ~ ent_strictly_stronger (ent_member eqb (fun x => x) nec_e_po1)
                          (ent_member eqb (fun x => x) nec_e_pr2).
Proof.
  intro eqb. nec_e_splits.
  - intros o1 o2 H. unfold eqb in H. apply andb_true_iff in H as [H _].
    apply Nat.eqb_eq, H.
  - exact nec_e_sub2.
  - exact nec_e_w2.
  - reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - simpl. lia.
  - vm_compute. lia.
  - vm_compute. lia.
  - apply nec_e_not_strict_if_equal. intro o. unfold ent_member, eqb. simpl.
    destruct o as [| [| o]]; reflexivity.
Qed.

(* The posterior must sit inside the prior: a posterior [2] outside the
   prior [0; 1] meets every other premise and conclusion (1) fails. *)
Theorem nec_e_cs_needs_inclusion :
  ~ incl [2] nec_e_pr2 /\
  (exists x, In x nec_e_pr2 /\ ~ In x [2]) /\
  (exists w, In w nec_e_pr2 /\ ~ In w [2] /\ ent_distinguishes (fun x : nat => x) w [2]) /\
  cs_cert nec_e_ecs (E.start 0 0) = false /\
  cs_cert nec_e_ecs (ent_cs_run nec_e_ecs nec_e_chain (E.start 0 0)) = true /\
  ent_member Nat.eqb (fun x => x) [2] 2 = true /\
  length nec_e_pr2 <= ent_leaves (ent_complete 1) * length [2] /\
  ent_depth (ent_complete 1) <= ent_cs_paid nec_e_ecs nec_e_chain /\
  ~ ent_strictly_stronger (ent_member Nat.eqb (fun x => x) [2])
                          (ent_member Nat.eqb (fun x => x) nec_e_pr2).
Proof.
  nec_e_splits.
  - intro H. specialize (H 2 (or_introl eq_refl)). simpl in H. lia.
  - exists 0. simpl. split; [auto | intros [H | []]; discriminate].
  - exists 0. split; [simpl; auto |]. split; [simpl; intros [H | []]; discriminate |].
    intros t [<- | []]. discriminate.
  - reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - vm_compute. lia.
  - vm_compute. lia.
  - intros [Hs _]. specialize (Hs 2 eq_refl). discriminate Hs.
Qed.

(* The distinguishing rival is needed: with an observation that reads the
   same of every rival, every other premise holds and conclusion (1)
   fails. *)
Theorem nec_e_cs_needs_distinguishing :
  ent_strict_sublist nec_e_po1 nec_e_pr2 /\
  ~ (exists w, In w nec_e_pr2 /\ ent_distinguishes (fun _ : nat => 0) w nec_e_po1) /\
  cs_cert nec_e_ecs (E.start 0 0) = false /\
  cs_cert nec_e_ecs (ent_cs_run nec_e_ecs nec_e_chain (E.start 0 0)) = true /\
  ent_member Nat.eqb (fun _ : nat => 0) nec_e_po1 0 = true /\
  length nec_e_pr2 <= ent_leaves (ent_complete 1) * length nec_e_po1 /\
  ent_depth (ent_complete 1) <= ent_cs_paid nec_e_ecs nec_e_chain /\
  ~ ent_strictly_stronger (ent_member Nat.eqb (fun _ : nat => 0) nec_e_po1)
                          (ent_member Nat.eqb (fun _ : nat => 0) nec_e_pr2).
Proof.
  nec_e_splits.
  - exact nec_e_sub2.
  - intros [w [_ Hd]]. apply (Hd 0 (or_introl eq_refl)). reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - vm_compute. lia.
  - vm_compute. lia.
  - apply nec_e_not_strict_if_equal. intro o. unfold ent_member. simpl.
    destruct o; reflexivity.
Qed.

(* The covering is needed: sixteen rivals narrowed to one by the
   three-move chain, a tree of depth 0, every other premise met, and the
   bill 3 is below the 4 index bits. *)
Theorem nec_e_cs_needs_covering :
  ent_strict_sublist nec_e_po1 nec_e_pr16 /\
  (exists w, In w nec_e_pr16 /\ ~ In w nec_e_po1 /\ ent_distinguishes (fun x : nat => x) w nec_e_po1) /\
  cs_cert nec_e_ecs (E.start 0 0) = false /\
  cs_cert nec_e_ecs (ent_cs_run nec_e_ecs nec_e_chain (E.start 0 0)) = true /\
  ent_member Nat.eqb (fun x => x) nec_e_po1 0 = true /\
  0 < length nec_e_po1 /\
  ~ (length nec_e_pr16 <= ent_leaves ent_leaf * length nec_e_po1) /\
  ent_depth ent_leaf <= ent_cs_paid nec_e_ecs nec_e_chain /\
  ent_cs_bill nec_e_ecs nec_e_chain = 3 /\
  ~ (Nat.log2_up (length nec_e_pr16) - Nat.log2_up (length nec_e_po1)
       <= ent_cs_bill nec_e_ecs nec_e_chain).
Proof.
  nec_e_splits.
  - exact nec_e_sub16.
  - exact nec_e_w16.
  - reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - simpl. lia.
  - vm_compute. lia.
  - vm_compute. lia.
  - vm_compute. reflexivity.
  - vm_compute. lia.
Qed.

(* The paid steps are needed: the covering by the complete tree of depth
   4 holds, every other premise is met, and the run has only 3 paid
   steps; the bill 3 is below the 4 index bits. *)
Theorem nec_e_cs_needs_paid_depth :
  ent_strict_sublist nec_e_po1 nec_e_pr16 /\
  (exists w, In w nec_e_pr16 /\ ~ In w nec_e_po1 /\ ent_distinguishes (fun x : nat => x) w nec_e_po1) /\
  cs_cert nec_e_ecs (E.start 0 0) = false /\
  cs_cert nec_e_ecs (ent_cs_run nec_e_ecs nec_e_chain (E.start 0 0)) = true /\
  ent_member Nat.eqb (fun x => x) nec_e_po1 0 = true /\
  0 < length nec_e_po1 /\
  length nec_e_pr16 <= ent_leaves (ent_complete 4) * length nec_e_po1 /\
  ent_cs_paid nec_e_ecs nec_e_chain < ent_depth (ent_complete 4) /\
  ~ (Nat.log2_up (length nec_e_pr16) - Nat.log2_up (length nec_e_po1)
       <= ent_cs_bill nec_e_ecs nec_e_chain).
Proof.
  nec_e_splits.
  - exact nec_e_sub16.
  - exact nec_e_w16.
  - reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - simpl. lia.
  - vm_compute. lia.
  - vm_compute. lia.
  - vm_compute. lia.
Qed.

(* The state the chain leaves: the record is up. *)
Definition nec_e_up : E.state := E.run nec_e_chain (E.start 0 0).

(* The start must read no: from a state already reading yes, the chain
   meets every other premise, ends reading yes, and no step of it takes
   the reading from no to yes, so conclusion (2) fails. *)
Theorem nec_e_cs_needs_start_no :
  cs_cert nec_e_ecs nec_e_up = true /\
  cs_cert nec_e_ecs (ent_cs_run nec_e_ecs nec_e_chain nec_e_up) = true /\
  ent_depth (ent_complete 1) <= ent_cs_paid nec_e_ecs nec_e_chain /\
  ~ (exists pre i rest, nec_e_chain = pre ++ i :: rest /\
       cs_cert nec_e_ecs (ent_cs_run nec_e_ecs pre nec_e_up) = false /\
       cs_cert nec_e_ecs (cs_step nec_e_ecs (ent_cs_run nec_e_ecs pre nec_e_up) i) = true /\
       cs_cost nec_e_ecs i >= 1).
Proof.
  nec_e_splits; [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; lia |].
  intros [pre [i [rest [_ [H _]]]]].
  rewrite nec_e_ecs_run in H.
  assert (Hup : forall l s, E.cert s = true -> E.cert (E.run l s) = true).
  { induction l as [| j l IH]; intros s Hs; simpl; [exact Hs |].
    apply IH, E.cert_permanent, Hs. }
  change (cs_cert nec_e_ecs (E.run pre nec_e_up)) with (E.cert (E.run pre nec_e_up)) in H.
  rewrite (Hup pre nec_e_up eq_refl) in H. discriminate.
Qed.

(* The end must read yes: the chain on "A is 0" from A = 1 fails its
   CHECK, every other premise holds, and no step raises the reading. *)
Theorem nec_e_cs_needs_end_yes :
  cs_cert nec_e_ecs (E.start 1 0) = false /\
  cs_cert nec_e_ecs (ent_cs_run nec_e_ecs nec_e_chain (E.start 1 0)) = false /\
  ent_depth (ent_complete 1) <= ent_cs_paid nec_e_ecs nec_e_chain /\
  ~ (exists pre i rest, nec_e_chain = pre ++ i :: rest /\
       cs_cert nec_e_ecs (ent_cs_run nec_e_ecs pre (E.start 1 0)) = false /\
       cs_cert nec_e_ecs (cs_step nec_e_ecs (ent_cs_run nec_e_ecs pre (E.start 1 0)) i) = true /\
       cs_cost nec_e_ecs i >= 1).
Proof.
  nec_e_splits; [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; lia |].
  intros [pre [i [rest [Htr [_ [H _]]]]]].
  (* the run is trapped after the first move; enumerate the splits *)
  destruct pre as [| a [| b [| c pre]]]; simpl in Htr; inversion Htr; subst;
    try (vm_compute in H; discriminate H).
  destruct pre; discriminate.
Qed.

(* ================================================================= *)
(* 5. ent-cs: the bound is attained for every k >= 1.                  *)
(* ================================================================= *)

(* The fact "A is 0" about version 0 of A. *)
Definition nec_e_f : E.fact := E.mkfact E.PZero E.CA 0.

(* A core with A = B = 0, versions 0, the fact in the table, the given
   program counter and channel, no trap. *)
Definition nec_e_core (p : nat) (ch : option E.fact) : E.core :=
  E.mkcore 0 0 0 0 p [nec_e_f] ch false.

Lemma nec_e_commits : forall j p ch m,
  E.run (repeat (E.COMMIT E.PZero E.CA) j) (E.mkst (nec_e_core p ch) m false)
  = E.mkst (nec_e_core (p + j) (match j with 0 => ch | S _ => Some nec_e_f end)) (m + j) false.
Proof.
  induction j as [| j IH]; intros p ch m.
  - simpl. rewrite !Nat.add_0_r. reflexivity.
  - simpl repeat. cbn [E.run].
    assert (Hx : E.exec (E.mkst (nec_e_core p ch) m false) (E.COMMIT E.PZero E.CA)
                 = E.mkst (nec_e_core (S p) (Some nec_e_f)) (m + 1) false) by reflexivity.
    rewrite Hx, IH. replace (S p + j) with (p + S j) by lia.
    replace (m + 1 + j) with (m + S j) by lia. destruct j; reflexivity.
Qed.

(* A state that reads no, with the fact checked and committed already. *)
Definition nec_e_primed : E.state := E.mkst (nec_e_core 1 (Some nec_e_f)) 0 false.

Definition nec_e_runk (k : nat) : list E.instr :=
  repeat (E.COMMIT E.PZero E.CA) (k - 1) ++ [E.CERTIFY].

Lemma nec_e_runk_cert : forall k,
  E.cert (E.run (nec_e_runk k) nec_e_primed) = true.
Proof.
  intro k. unfold nec_e_runk. rewrite E.run_app. unfold nec_e_primed. rewrite nec_e_commits.
  destruct (k - 1); reflexivity.
Qed.

Lemma nec_e_paid_runk : forall k, ent_cs_paid nec_e_ecs (nec_e_runk k) = k - 1 + 1.
Proof.
  intro k. unfold nec_e_runk. induction (k - 1) as [| j IH]; [reflexivity |].
  simpl repeat. simpl app. cbn [ent_cs_paid]. rewrite IH. reflexivity.
Qed.

Lemma nec_e_bill_runk : forall k, ent_cs_bill nec_e_ecs (nec_e_runk k) = k - 1 + 1.
Proof.
  intro k. unfold nec_e_runk. induction (k - 1) as [| j IH]; [reflexivity |].
  simpl repeat. simpl app. cbn [ent_cs_bill]. rewrite IH. reflexivity.
Qed.

Lemma nec_e_seq_bits : forall k,
  Nat.log2_up (length (seq 0 (2 ^ k))) - Nat.log2_up (length [0]) = k.
Proof. intro k. rewrite seq_length, Nat.log2_up_pow2 by lia. change (length [0]) with 1. rewrite Nat.log2_up_1. lia. Qed.

Lemma nec_e_pow_ge2 : forall k, 1 <= k -> 2 <= 2 ^ k.
Proof.
  intros k Hk. destruct k as [| k]; [lia |]. rewrite Nat.pow_succ_r'.
  pose proof (Nat.pow_nonzero 2 k ltac:(lia)). lia.
Qed.

(* For every k >= 1: a certification system (the small machine), a state
   reading no, and a run that ends reading yes with bill exactly k, with a
   narrowing of exactly k index bits that meets every premise of ent-cs. *)
Theorem nec_e_cs_tight : forall k, 1 <= k ->
  let prior := seq 0 (2 ^ k) in
  let post := [0] in
  let T := ent_complete k in
  ent_strict_sublist post prior /\
  (exists w, In w prior /\ ~ In w post /\ ent_distinguishes (fun x : nat => x) w post) /\
  cs_cert nec_e_ecs nec_e_primed = false /\
  cs_cert nec_e_ecs (ent_cs_run nec_e_ecs (nec_e_runk k) nec_e_primed) = true /\
  ent_member Nat.eqb (fun x => x) post 0 = true /\
  0 < length post /\
  length prior <= ent_leaves T * length post /\
  ent_depth T <= ent_cs_paid nec_e_ecs (nec_e_runk k) /\
  Nat.log2_up (length prior) - Nat.log2_up (length post) = k /\
  ent_cs_bill nec_e_ecs (nec_e_runk k) = k.
Proof.
  intros k Hk prior post T. pose proof (nec_e_pow_ge2 k Hk) as H2.
  assert (Hin : forall x, x < 2 ^ k -> In x prior)
    by (intros x Hx; unfold prior; apply in_seq; lia).
  split; [split |].
  - intros x [<- | []]. apply Hin. lia.
  - exists 1. split; [apply Hin; lia | simpl; intros [H | []]; discriminate].
  - split; [exists 1; split; [apply Hin; lia |];
            split; [simpl; intros [H | []]; discriminate | intros t [<- | []]; discriminate] |].
    split; [reflexivity |].
    split; [rewrite nec_e_ecs_run; apply nec_e_runk_cert |].
    split; [reflexivity |]. split; [simpl; lia |].
    split; [unfold prior, T, post; rewrite seq_length, ent_complete_leaves; simpl; lia |].
    split; [unfold T; rewrite ent_complete_depth, nec_e_paid_runk; lia |].
    split; [apply nec_e_seq_bits |].
    rewrite nec_e_bill_runk. lia.
Qed.

(* ================================================================= *)
(* 6. ent-machine: the stronger statement.                             *)
(* ================================================================= *)

(* Structural entitlement represented, with four premises fewer: no
   strictness half of (M1), no "w not in the posterior", no decoder half
   of (M3) (only the record being up), no (M5). *)
Theorem nec_e_representation_stronger :
  forall (M : machine) (I : thiele_interface M) (X O : Type)
         (s0 : m_state M) (tr : list (m_move M))
         (obs r : X -> O) (eqb : O -> O -> bool)
         (prior post : list X) (T : ent_tree),
    thiele_complete_with I ->
    (forall o1 o2, eqb o1 o2 = true <-> o1 = o2) ->
    incl post prior ->
    (exists w, In w prior /\ ent_distinguishes obs w post) ->
    ti_clean I s0 ->
    m_record M (run M tr s0) = true ->
    ent_depth T <= record_moves I tr ->
    ent_reduction r T prior post ->
    ent_strictly_stronger (ent_member eqb obs post) (ent_member eqb obs prior) /\
    earned_chain I s0 tr /\
    (exists pre c chk mid1 cmt rest,
       tr = pre ++ chk :: mid1 ++ cmt :: rest /\
       ti_kind I chk = KCheck c /\ ti_kind I cmt = KCommit c /\
       ti_meaning I c (run M pre s0) /\ ti_meaning I c (run M (pre ++ chk :: mid1) s0)) /\
    Nat.log2_up (length prior) - Nat.log2_up (length post) <= record_moves I tr /\
    record_moves I tr = ti_ledger I (run M tr s0) - ti_ledger I s0 /\
    ti_ledger I s0 + 3 <= ti_ledger I (run M tr s0).
Proof.
  intros M I X O s0 tr obs r eqb prior post T HC Heq Hincl [w [Hw Hd]] H0 Hrec HT Hred.
  pose proof HC as [_ [[_ [Hchain _]] [Htoll _]]].
  split; [apply (ent_narrowing_strengthens eqb obs prior post w Heq Hincl Hw Hd) |].
  split; [apply Hchain; assumption |].
  split; [apply (committed_claim_holds M I HC s0 tr H0 Hrec) |].
  split; [pose proof (ent_index_bits_le_depth r T prior post
                        (nec_e_reduction_post_pos r T prior post w Hw Hred) Hred); lia |].
  split; [apply ent_ledger_rise, Htoll |].
  destruct (certificate_costs_three M I HC s0 tr H0 Hrec) as [_ H3]. lia.
Qed.

(* What the record adds, part (2), with the same four premises fewer: only
   the exact toll, the equality test, the inclusion, the distinguishing
   rival, the depth and the fibre covering. No decoder premise, no
   |Omega'| > 0. *)
Theorem nec_e_observed_stronger :
  forall (M : machine) (I : thiele_interface M) (X O : Type)
         (s0 : m_state M) (tr : list (m_move M))
         (obs r : X -> O) (eqb : O -> O -> bool)
         (prior post : list X) (T : ent_tree),
    exact_toll_clause I ->
    (forall o1 o2, eqb o1 o2 = true <-> o1 = o2) ->
    incl post prior ->
    (exists w, In w prior /\ ent_distinguishes obs w post) ->
    ent_depth T <= record_moves I tr ->
    ent_reduction r T prior post ->
    ent_strictly_stronger (ent_member eqb obs post) (ent_member eqb obs prior) /\
    Nat.log2_up (length prior) - Nat.log2_up (length post) <= record_moves I tr /\
    record_moves I tr = ti_ledger I (run M tr s0) - ti_ledger I s0.
Proof.
  intros M I X O s0 tr obs r eqb prior post T Htoll Heq Hincl [w [Hw Hd]] HT Hred.
  split; [apply (ent_narrowing_strengthens eqb obs prior post w Heq Hincl Hw Hd) |].
  split; [pose proof (ent_index_bits_le_depth r T prior post
                        (nec_e_reduction_post_pos r T prior post w Hw Hred) Hred); lia |].
  apply ent_ledger_rise, Htoll.
Qed.

(* ================================================================= *)
(* 7. ent-machine: each remaining premise is needed.                   *)
(* ================================================================= *)

Lemma nec_e_earned_complete : thiele_complete_with earned_interface.
Proof. exact ent_earned_complete_with. Qed.

(* An earned chain has at least three moves. *)
Lemma nec_e_chain_len : forall (M : machine) (I : thiele_interface M) s0 tr,
  earned_chain I s0 tr -> 3 <= length tr.
Proof.
  intros M I s0 tr [pre [c [chk [mid1 [cmt [mid2 [crt [post [Htr _]]]]]]]]].
  rewrite Htr. rewrite app_length. simpl. rewrite app_length. simpl. rewrite app_length. simpl. lia.
Qed.

(* (M4) is needed: the chain from a clean start, the depth-4 covering of
   16 rivals by one, every other premise met, and conclusion (3) fails:
   4 index bits against 3 record moves. *)
Theorem nec_e_rep_needs_depth :
  thiele_complete_with earned_interface /\
  ent_strict_sublist nec_e_po1 nec_e_pr16 /\
  (exists w, In w nec_e_pr16 /\ ~ In w nec_e_po1 /\ ent_distinguishes (fun x : nat => x) w nec_e_po1) /\
  ti_clean earned_interface (E.start 0 0) /\
  ent_certified earned_interface (E.start 0 0) nec_e_chain (fun _ => 0)
    (ent_member Nat.eqb (fun x => x) nec_e_po1) /\
  ~ (ent_depth (ent_complete 4) <= record_moves earned_interface nec_e_chain) /\
  0 < length nec_e_po1 /\
  ent_reduction (fun _ : nat => 0) (ent_complete 4) nec_e_pr16 nec_e_po1 /\
  ~ (Nat.log2_up (length nec_e_pr16) - Nat.log2_up (length nec_e_po1)
       <= record_moves earned_interface nec_e_chain).
Proof.
  split; [exact nec_e_earned_complete |]. split; [exact nec_e_sub16 |].
  split; [exact nec_e_w16 |]. split; [apply E.start_clean |].
  split; [split; vm_compute; reflexivity |].
  split; [vm_compute; lia |]. split; [simpl; lia |]. split; [exact nec_e_red16 |].
  vm_compute. lia.
Qed.

(* (M6) is needed: the same data with a tree of depth 0, so (M4) holds,
   no covering exists, and conclusion (3) fails. The repo's own witness of
   this on a certified posterior is ent2_uncovered_claim_false. *)
Theorem nec_e_rep_needs_covering :
  thiele_complete_with earned_interface /\
  ent_strict_sublist nec_e_po1 nec_e_pr16 /\
  ti_clean earned_interface (E.start 0 0) /\
  ent_certified earned_interface (E.start 0 0) nec_e_chain (fun _ => 0)
    (ent_member Nat.eqb (fun x => x) nec_e_po1) /\
  ent_depth ent_leaf <= record_moves earned_interface nec_e_chain /\
  (forall (r : nat -> nat), ~ ent_reduction r ent_leaf nec_e_pr16 nec_e_po1) /\
  ~ (Nat.log2_up (length nec_e_pr16) - Nat.log2_up (length nec_e_po1)
       <= record_moves earned_interface nec_e_chain).
Proof.
  split; [exact nec_e_earned_complete |]. split; [exact nec_e_sub16 |].
  split; [apply E.start_clean |].
  split; [split; vm_compute; reflexivity |].
  split; [vm_compute; lia |].
  split; [| vm_compute; lia].
  intros r Hred. pose proof (ent_index_bits_le_depth r ent_leaf nec_e_pr16 nec_e_po1
                               ltac:(simpl; lia) Hred) as H. vm_compute in H. lia.
Qed.

(* A state that reads no but is not a clean start: the fact is committed
   already. *)
Definition nec_e_dirty : E.state := E.mkst (nec_e_core 1 (Some nec_e_f)) 0 false.

(* The clean start is needed: from that state CERTIFY alone raises the
   record; every other premise holds; the run contains no earned chain
   and the ledger rose by 1, not 3. *)
Theorem nec_e_rep_needs_clean :
  thiele_complete_with earned_interface /\
  ~ ti_clean earned_interface nec_e_dirty /\
  m_record earned_machine nec_e_dirty = false /\
  ent_strict_sublist nec_e_po1 nec_e_pr2 /\
  ent_certified earned_interface nec_e_dirty [E.CERTIFY] (fun _ => 0)
    (ent_member Nat.eqb (fun x => x) nec_e_po1) /\
  ent_depth (ent_complete 1) <= record_moves earned_interface [E.CERTIFY] /\
  ent_reduction (fun _ : nat => 0) (ent_complete 1) nec_e_pr2 nec_e_po1 /\
  ~ earned_chain earned_interface nec_e_dirty [E.CERTIFY] /\
  ~ (ti_ledger earned_interface nec_e_dirty + 3
       <= ti_ledger earned_interface (run earned_machine [E.CERTIFY] nec_e_dirty)).
Proof.
  split; [exact nec_e_earned_complete |].
  split; [intros [_ [H _]]; discriminate H |].
  split; [reflexivity |]. split; [exact nec_e_sub2 |].
  split; [split; vm_compute; reflexivity |].
  split; [vm_compute; lia |]. split; [exact nec_e_red2 |].
  split; [intro H; apply nec_e_chain_len in H; simpl in H; lia |].
  vm_compute. lia.
Qed.

(* The record being up is needed for (2) and (5): one CHECK from a clean
   start, the decoder half of (M3) and every other premise met, no chain,
   and the ledger rose by 1. *)
Theorem nec_e_rep_needs_record :
  thiele_complete_with earned_interface /\
  ti_clean earned_interface (E.start 0 0) /\
  m_record earned_machine (run earned_machine [E.CHECK E.PZero E.CA] (E.start 0 0)) = false /\
  ent_member Nat.eqb (fun x : nat => x) nec_e_po1 0 = true /\
  ent_strict_sublist nec_e_po1 nec_e_pr2 /\
  ent_depth (ent_complete 1) <= record_moves earned_interface [E.CHECK E.PZero E.CA] /\
  ent_reduction (fun _ : nat => 0) (ent_complete 1) nec_e_pr2 nec_e_po1 /\
  ~ earned_chain earned_interface (E.start 0 0) [E.CHECK E.PZero E.CA] /\
  ~ (ti_ledger earned_interface (E.start 0 0) + 3
       <= ti_ledger earned_interface (run earned_machine [E.CHECK E.PZero E.CA] (E.start 0 0))).
Proof.
  split; [exact nec_e_earned_complete |]. split; [apply E.start_clean |].
  split; [vm_compute; reflexivity |]. split; [vm_compute; reflexivity |].
  split; [exact nec_e_sub2 |]. split; [vm_compute; lia |]. split; [exact nec_e_red2 |].
  split; [intro H; apply nec_e_chain_len in H; simpl in H; lia |].
  vm_compute. lia.
Qed.

(* (M2) is needed for (1): with a constant observation, a certified run
   from a clean start meets every other premise and the posterior's test
   is not strictly stronger. *)
Theorem nec_e_rep_needs_distinguishing :
  thiele_complete_with earned_interface /\
  ent_strict_sublist nec_e_po1 nec_e_pr2 /\
  ti_clean earned_interface (E.start 0 0) /\
  ent_certified earned_interface (E.start 0 0) nec_e_chain (fun _ => 0)
    (ent_member Nat.eqb (fun _ : nat => 0) nec_e_po1) /\
  ent_depth (ent_complete 1) <= record_moves earned_interface nec_e_chain /\
  ent_reduction (fun _ : nat => 0) (ent_complete 1) nec_e_pr2 nec_e_po1 /\
  ~ (exists w, In w nec_e_pr2 /\ ent_distinguishes (fun _ : nat => 0) w nec_e_po1) /\
  ~ ent_strictly_stronger (ent_member Nat.eqb (fun _ : nat => 0) nec_e_po1)
                          (ent_member Nat.eqb (fun _ : nat => 0) nec_e_pr2).
Proof.
  split; [exact nec_e_earned_complete |]. split; [exact nec_e_sub2 |].
  split; [apply E.start_clean |]. split; [split; vm_compute; reflexivity |].
  split; [vm_compute; lia |]. split; [exact nec_e_red2 |].
  split; [intros [w [_ Hd]]; apply (Hd 0 (or_introl eq_refl)); reflexivity |].
  apply nec_e_not_strict_if_equal. intro o. unfold ent_member. simpl.
  destruct o; reflexivity.
Qed.

(* The exact equality test is needed for (1), on the machine too: the
   test that says yes to everything. *)
Theorem nec_e_rep_needs_eqb :
  let eqb := fun _ _ : nat => true in
  thiele_complete_with earned_interface /\
  ent_strict_sublist nec_e_po1 nec_e_pr2 /\
  (exists w, In w nec_e_pr2 /\ ~ In w nec_e_po1 /\ ent_distinguishes (fun x : nat => x) w nec_e_po1) /\
  ti_clean earned_interface (E.start 0 0) /\
  ent_certified earned_interface (E.start 0 0) nec_e_chain (fun _ => 0)
    (ent_member eqb (fun x => x) nec_e_po1) /\
  ent_depth (ent_complete 1) <= record_moves earned_interface nec_e_chain /\
  ent_reduction (fun _ : nat => 0) (ent_complete 1) nec_e_pr2 nec_e_po1 /\
  ~ ent_strictly_stronger (ent_member eqb (fun x => x) nec_e_po1)
                          (ent_member eqb (fun x => x) nec_e_pr2).
Proof.
  intro eqb.
  split; [exact nec_e_earned_complete |]. split; [exact nec_e_sub2 |].
  split; [exact nec_e_w2 |]. split; [apply E.start_clean |].
  split; [split; vm_compute; reflexivity |].
  split; [vm_compute; lia |]. split; [exact nec_e_red2 |].
  apply nec_e_not_strict_if_equal. intro o. reflexivity.
Qed.

(* (M1)'s inclusion is needed for (1): a posterior [2] outside the prior. *)
Theorem nec_e_rep_needs_inclusion :
  thiele_complete_with earned_interface /\
  ~ incl [2] nec_e_pr2 /\
  (exists w, In w nec_e_pr2 /\ ~ In w [2] /\ ent_distinguishes (fun x : nat => x) w [2]) /\
  ti_clean earned_interface (E.start 0 0) /\
  ent_certified earned_interface (E.start 0 0) nec_e_chain (fun _ => 2)
    (ent_member Nat.eqb (fun x => x) [2]) /\
  ent_depth (ent_complete 1) <= record_moves earned_interface nec_e_chain /\
  ent_reduction (fun _ : nat => 0) (ent_complete 1) nec_e_pr2 [2] /\
  ~ ent_strictly_stronger (ent_member Nat.eqb (fun x => x) [2])
                          (ent_member Nat.eqb (fun x => x) nec_e_pr2).
Proof.
  split; [exact nec_e_earned_complete |].
  split; [intro H; specialize (H 2 (or_introl eq_refl)); simpl in H; lia |].
  split; [exists 0; split; [simpl; auto |];
          split; [simpl; intros [H | []]; discriminate | intros t [<- | []]; discriminate] |].
  split; [apply E.start_clean |]. split; [split; vm_compute; reflexivity |].
  split; [vm_compute; lia |].
  split; [exists (fun _ => nec_e_pr2); split; [| split];
          [intros x Hx; exists 2; split; [left; reflexivity | split; [exact Hx | reflexivity]]
          | vm_compute; lia | intros t _; vm_compute; lia] |].
  intros [Hs _]. specialize (Hs 2 eq_refl). discriminate Hs.
Qed.

(* ================================================================= *)
(* 8. ent-machine: the bound is attained for every k >= 3.             *)
(* ================================================================= *)

Definition nec_e_mrun (k : nat) : list E.instr :=
  E.CHECK E.PZero E.CA :: repeat (E.COMMIT E.PZero E.CA) (k - 2) ++ [E.CERTIFY].

Lemma nec_e_mrun_run : forall k, 3 <= k ->
  E.run (nec_e_mrun k) (E.start 0 0)
  = E.mkst (E.goto (nec_e_core (2 + (k - 2)) (Some nec_e_f)) (S (2 + (k - 2)))) (1 + (k - 2) + 1) true.
Proof.
  intros k Hk. unfold nec_e_mrun. cbn [E.run].
  assert (H1 : E.exec (E.start 0 0) (E.CHECK E.PZero E.CA) = E.mkst (nec_e_core 2 None) 1 false)
    by reflexivity.
  rewrite H1, E.run_app, nec_e_commits.
  destruct (k - 2) as [| j] eqn:Hj; [lia |]. reflexivity.
Qed.

Lemma nec_e_record_moves_mrun : forall k, 3 <= k ->
  record_moves earned_interface (nec_e_mrun k) = k.
Proof.
  intros k Hk. unfold nec_e_mrun. cbn [record_moves]. rewrite record_moves_app.
  assert (H : forall j, record_moves earned_interface (repeat (E.COMMIT E.PZero E.CA) j) = j)
    by (induction j as [| j IH]; [reflexivity | simpl; rewrite IH; reflexivity]).
  rewrite H. simpl. unfold record_move. simpl. lia.
Qed.

(* For every k >= 3, from a clean start, a certified run with exactly k
   record moves and a ledger rise of exactly k, with a narrowing of exactly
   k index bits that meets every premise of ent-machine. *)
Theorem nec_e_rep_tight : forall k, 3 <= k ->
  let prior := seq 0 (2 ^ k) in
  let post := [0] in
  let T := ent_complete k in
  thiele_complete_with earned_interface /\
  ent_strict_sublist post prior /\
  (exists w, In w prior /\ ~ In w post /\ ent_distinguishes (fun x : nat => x) w post) /\
  ti_clean earned_interface (E.start 0 0) /\
  ent_certified earned_interface (E.start 0 0) (nec_e_mrun k) (fun _ => 0)
    (ent_member Nat.eqb (fun x => x) post) /\
  ent_depth T <= record_moves earned_interface (nec_e_mrun k) /\
  0 < length post /\
  ent_reduction (fun _ : nat => 0) T prior post /\
  Nat.log2_up (length prior) - Nat.log2_up (length post) = k /\
  record_moves earned_interface (nec_e_mrun k) = k /\
  ti_ledger earned_interface (run earned_machine (nec_e_mrun k) (E.start 0 0))
    - ti_ledger earned_interface (E.start 0 0) = k.
Proof.
  intros k Hk prior post T. pose proof (nec_e_pow_ge2 k ltac:(lia)) as H2.
  assert (Hin : forall x, x < 2 ^ k -> In x prior)
    by (intros x Hx; unfold prior; apply in_seq; lia).
  assert (Hrun : run earned_machine (nec_e_mrun k) (E.start 0 0) = E.run (nec_e_mrun k) (E.start 0 0))
    by apply run_earned.
  split; [exact nec_e_earned_complete |].
  split; [split; [intros x [<- | []]; apply Hin; lia |
                  exists 1; split; [apply Hin; lia | simpl; intros [H | []]; discriminate]] |].
  split; [exists 1; split; [apply Hin; lia |];
          split; [simpl; intros [H | []]; discriminate | intros t [<- | []]; discriminate] |].
  split; [apply E.start_clean |].
  split; [split; [change (E.cert (run earned_machine (nec_e_mrun k) (E.start 0 0)) = true);
                  rewrite Hrun, (nec_e_mrun_run k Hk); reflexivity | reflexivity] |].
  split; [unfold T; rewrite ent_complete_depth, nec_e_record_moves_mrun by exact Hk; lia |].
  split; [simpl; lia |].
  split; [exists (fun _ => prior); split; [| split];
          [intros x Hx; exists 0; split; [left; reflexivity | split; [exact Hx | reflexivity]]
          | unfold post; simpl; lia
          | intros t _; unfold prior, T; rewrite seq_length, ent_complete_leaves; lia] |].
  split; [apply nec_e_seq_bits |].
  split; [apply nec_e_record_moves_mrun, Hk |].
  change (E.mu (run earned_machine (nec_e_mrun k) (E.start 0 0)) - E.mu (E.start 0 0) = k).
  rewrite Hrun, (nec_e_mrun_run k Hk). simpl. lia.
Qed.

(* ================================================================= *)
(* 9. Converse: paying does not make a narrowing.                     *)
(* ================================================================= *)

(* A certified run from a clean start pays 3 and the bound holds, with a
   posterior equal to the prior: the test is not strictly stronger. So the
   ledger bound does not give back the narrowing. *)
Theorem nec_e_pay_without_narrowing :
  ti_clean earned_interface (E.start 0 0) /\
  m_record earned_machine (run earned_machine nec_e_chain (E.start 0 0)) = true /\
  ti_ledger earned_interface (run earned_machine nec_e_chain (E.start 0 0)) = 3 /\
  Nat.log2_up (length nec_e_pr2) - Nat.log2_up (length nec_e_pr2)
    <= ti_ledger earned_interface (run earned_machine nec_e_chain (E.start 0 0)) /\
  ~ ent_strictly_stronger (ent_member Nat.eqb (fun x : nat => x) nec_e_pr2)
                          (ent_member Nat.eqb (fun x => x) nec_e_pr2).
Proof.
  split; [apply E.start_clean |]. split; [vm_compute; reflexivity |].
  split; [vm_compute; reflexivity |]. split; [vm_compute; lia |].
  apply nec_e_not_strict_if_equal. intro o. reflexivity.
Qed.

(* ================================================================= *)
(* 10. The questions floor: no toll and no m > 0 needed for its first   *)
(*     two conclusions.                                                *)
(* ================================================================= *)

Theorem nec_e_questions_floor_stronger :
  forall (M : machine) (I : thiele_interface M)
         (tr : list (m_move M)) (prior : list (m_state M)) (m : nat),
    (forall x, In x prior ->
       length (filter (fun y => ent_bools_eqb (ent_answers I tr y) (ent_answers I tr x))
                      prior) <= m) ->
    Nat.log2_up (length prior) - Nat.log2_up m <= length (ent_checked I tr) /\
    length (ent_checked I tr) <= record_moves I tr.
Proof.
  intros M I tr prior m Hfib.
  destruct m as [| m].
  - destruct prior as [| x prior].
    + split; [simpl; lia | apply ent_checked_le_record_moves].
    + exfalso. specialize (Hfib x (or_introl eq_refl)). simpl in Hfib.
      assert (Hr : ent_bools_eqb (ent_answers I tr x) (ent_answers I tr x) = true)
        by (apply ent_bools_eqb_eq; reflexivity).
      rewrite Hr in Hfib. simpl in Hfib. lia.
  - (* use any interface's toll-free part of ent_questions_floor *)
    set (k := length (ent_checked I tr)).
    assert (Hcount : length prior <= S m * 2 ^ k).
    { rewrite <- ent_all_bools_length.
      apply (ent_fibres_count ent_bools_eqb ent_bools_eqb_eq (ent_answers I tr) (S m)
               (ent_all_bools k) prior); [| exact Hfib].
      intros x _. unfold k.
      replace (length (ent_checked I tr)) with (length (ent_answers I tr x))
        by (unfold ent_answers; apply map_length).
      apply ent_all_bools_complete. }
    split.
    + assert (H1 : Nat.log2_up (length prior) <= Nat.log2_up (S m * 2 ^ k))
        by (apply Nat.log2_up_le_mono; exact Hcount).
      assert (H2 : Nat.log2_up (S m * 2 ^ k) <= Nat.log2_up (S m) + Nat.log2_up (2 ^ k))
        by (apply Nat.log2_up_mul_above; lia).
      rewrite Nat.log2_up_pow2 in H2 by lia. lia.
    + apply ent_checked_le_record_moves.
Qed.

(* ================================================================= *)
(* 11. Tree width: exactly the complete trees attain 2^depth.         *)
(* ================================================================= *)

Theorem nec_e_tree_full_iff : forall t,
  ent_leaves t = 2 ^ ent_depth t <-> t = ent_complete (ent_depth t).
Proof.
  induction t as [| l IHl r IHr]; [simpl; split; reflexivity |]. split.
  - intro H. simpl in H. simpl.
    set (d := Nat.max (ent_depth l) (ent_depth r)) in *.
    pose proof (ent_leaves_le_pow2 l) as Hl. pose proof (ent_leaves_le_pow2 r) as Hr.
    assert (Hdl : 2 ^ ent_depth l <= 2 ^ d) by (apply Nat.pow_le_mono_r; lia).
    assert (Hdr : 2 ^ ent_depth r <= 2 ^ d) by (apply Nat.pow_le_mono_r; lia).
    try rewrite Nat.pow_succ_r' in H.
    assert (El : ent_leaves l = 2 ^ ent_depth l) by lia.
    assert (Er : ent_leaves r = 2 ^ ent_depth r) by lia.
    assert (Pl : 2 ^ ent_depth l = 2 ^ d) by lia.
    assert (Pr : 2 ^ ent_depth r = 2 ^ d) by lia.
    apply Nat.pow_inj_r in Pl; [| lia]. apply Nat.pow_inj_r in Pr; [| lia].
    apply IHl in El. apply IHr in Er. rewrite El, Er, Pl, Pr. reflexivity.
  - intro H. rewrite H at 1. rewrite ent_complete_leaves. reflexivity.
Qed.

(* ================================================================= *)
(* Assumption audit.                                                  *)
(* ================================================================= *)

Print Assumptions nec_e_cover_bits_any.
Print Assumptions nec_e_cs_count_any.
Print Assumptions nec_e_weighted_bits_any.
Print Assumptions nec_e_cs_entitlement_stronger.
Print Assumptions nec_e_cs_entitlement_from_stronger.
Print Assumptions nec_e_cs_needs_eqb_sound.
Print Assumptions nec_e_cs_needs_eqb_refl.
Print Assumptions nec_e_cs_needs_inclusion.
Print Assumptions nec_e_cs_needs_distinguishing.
Print Assumptions nec_e_cs_needs_covering.
Print Assumptions nec_e_cs_needs_paid_depth.
Print Assumptions nec_e_cs_needs_start_no.
Print Assumptions nec_e_cs_needs_end_yes.
Print Assumptions nec_e_cs_tight.
Print Assumptions nec_e_representation_stronger.
Print Assumptions nec_e_rep_needs_depth.
Print Assumptions nec_e_rep_needs_covering.
Print Assumptions nec_e_rep_needs_clean.
Print Assumptions nec_e_rep_needs_record.
Print Assumptions nec_e_rep_needs_distinguishing.
Print Assumptions nec_e_rep_needs_eqb.
Print Assumptions nec_e_rep_needs_inclusion.
Print Assumptions nec_e_rep_tight.
Print Assumptions nec_e_pay_without_narrowing.
Print Assumptions nec_e_questions_floor_stronger.
Print Assumptions nec_e_tree_full_iff.
Print Assumptions nec_e_observed_stronger.
