(** ThieleCompleteIndependent.v: the four clauses of Thiele-complete are
    independent.

    For each clause of the definition in ThieleComplete.v there is a machine
    with an interface that meets the other three clauses and fails that one.
    Each of the four machines obeys the toll and has a universal base (it is
    weakly Thiele-complete), and none of them is Thiele-complete through any
    interface at all. Three of them are the small machine of EarnedCore.v
    with one change.

      (a) fails. The small machine with one more move, DROP, a free base
          move that lowers the flag and trips the trap latch. A run that
          uses DROP ends with the flag down for good, so every run that ends
          with the flag up is a run of the small machine, and (b), (c), (d)
          hold as they do there. The record can come down, so no interface
          meets (a) [drop_meets_b_c_d, drop_fails_a,
          drop_not_thiele_complete].
      (b) fails. The small machine with one more move, FREE, read as a
          CERTIFY and costing 1, that raises the flag on any live state with
          no commitment behind it. (a), (c) and (d) hold; from a clean start
          FREE alone raises the flag, and a one-move run holds no earned
          chain [free_meets_a_c_d, free_fails_b,
          free_not_thiele_complete].
      (c) fails. The small machine with every move costing 1. (a), (b) and
          (d) do not mention prices and hold as they do there; base moves
          cost 1, so (c) fails, and a Thiele-complete machine has a free
          move [paid_meets_a_b_d, paid_fails_c, paid_not_thiele_complete].
      (d) fails. The silent machine of ThieleComplete.v: a free two-counter
          base whose record never rises [silent_meets_base_record_toll,
          silent_not_thiele_complete].

    The four together are [thiele_complete_clauses_independent].

    Dependencies: Coq standard library, EarnedCore.v, EarnedGeneric.v and
    ThieleComplete.v. No axioms, no Admitted.                              *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Minimal.ThieleComplete.
Require Minimal.EarnedCore.
Module E := Minimal.EarnedCore.

(* ================================================================= *)
(* The small machine with one extra move.                             *)
(* ================================================================= *)

Inductive ext_move : Type := EM (i : E.instr) | EX.

Section Extension.

(* What the extra move does, what it costs, and how the interface reads it. *)
Variable x_step : E.state -> E.state.
Variable x_cost : nat.
Variable x_kind : kind (E.prop * E.ctr).

Definition ext_step (s : E.state) (m : ext_move) : E.state :=
  match m with EM i => E.exec s i | EX => x_step s end.

Definition ext_cost (m : ext_move) : nat :=
  match m with EM i => E.cost i | EX => x_cost end.

Definition ext_machine : machine := mk_machine E.state ext_move ext_step ext_cost E.cert.

Definition ext_base : universal_base ext_machine :=
  mk_ub ext_machine (fun s => E.window (E.core_of s))
    (fun s => E.err (E.core_of s) = false) (fun i => EM (earned_compile i)) E.start
    (fun a b => eq_refl) (fun a b => eq_refl) earned_sim.

Definition ext_kind (m : ext_move) : kind (E.prop * E.ctr) :=
  match m with EM i => earned_kind i | EX => x_kind end.

Definition ext_interface : thiele_interface ext_machine :=
  mk_ti ext_machine ext_base (E.prop * E.ctr) ext_kind
    (fun pc s => E.holds (fst pc) (E.val (E.core_of s) (snd pc)))
    (fun s pc => E.check_ok (E.core_of s) (fst pc) (snd pc))
    (fun pc s t => E.ver (E.core_of s) (snd pc) = E.ver (E.core_of t) (snd pc) /\
                   E.val (E.core_of s) (snd pc) = E.val (E.core_of t) (snd pc))
    E.clean_start E.mu.

Lemma ext_run_map : forall l s, run ext_machine (map EM l) s = E.run l s.
Proof. induction l; intros; simpl; auto. Qed.

Lemma ext_run_EM_app : forall l1 l2 s,
  run ext_machine (map EM l1 ++ l2) s = run ext_machine l2 (E.run l1 s).
Proof. intros. rewrite run_app, ext_run_map. reflexivity. Qed.

Lemma ext_run_EM_cons : forall x l s,
  run ext_machine (EM x :: l) s = run ext_machine l (E.exec s x).
Proof. reflexivity. Qed.

Lemma E_run_cons : forall x l s, E.run (x :: l) s = E.run l (E.exec s x).
Proof. reflexivity. Qed.

Ltac ext_norm :=
  repeat first [rewrite ext_run_EM_app | rewrite ext_run_EM_cons | rewrite ext_run_map
               | rewrite E.run_app | rewrite E_run_cons].

(* An earned chain of the small machine is an earned chain here. *)
Lemma ext_chain_transport : forall s0 tr,
  earned_chain earned_interface s0 tr -> earned_chain ext_interface s0 (map EM tr).
Proof.
  intros s0 tr [pre [c [chk [mid1 [cmt [mid2 [crt [post
                [Htr [Hk1 [Hk2 [Hk3 [Hck [Hsame [Hdown Hup]]]]]]]]]]]]]]].
  exists (map EM pre), c, (EM chk), (map EM mid1), (EM cmt), (map EM mid2), (EM crt),
         (map EM post).
  split; [rewrite Htr; repeat (rewrite map_app; simpl); reflexivity |].
  split; [exact Hk1 |]. split; [exact Hk2 |]. split; [exact Hk3 |].
  split; [rewrite ext_run_map; rewrite run_earned in Hck; exact Hck |].
  split.
  { intros t1 t2 Hm. apply map_eq_app in Hm as [t1' [t2' [Hmid [<- _]]]].
    specialize (Hsame t1' t2' Hmid). rewrite !run_earned in Hsame.
    repeat first [rewrite E.run_app in Hsame | rewrite E_run_cons in Hsame].
    ext_norm. exact Hsame. }
  rewrite run_earned in Hdown, Hup.
  repeat first [rewrite E.run_app in Hdown | rewrite E_run_cons in Hdown].
  repeat first [rewrite E.run_app in Hup | rewrite E_run_cons in Hup].
  ext_norm.
  split; [exact Hdown | exact Hup].
Qed.

(* The parts of the clauses that do not involve the extra move. *)
Lemma ext_record_parts :
  (forall s, ti_clean ext_interface s -> m_record ext_machine s = false) /\
  (forall s c, ti_check ext_interface s c = true -> ti_meaning ext_interface c s) /\
  (forall c s s', ti_same ext_interface c s s' -> ti_meaning ext_interface c s ->
                  ti_meaning ext_interface c s').
Proof.
  split; [intros s [_ [_ H]]; exact H |]. split.
  - intros s [p c] H. simpl in *. unfold E.check_ok in H.
    apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [_ H].
    apply E.eval_iff, H.
  - intros [p c] s t [_ Hw] H. simpl in *. rewrite <- Hw. exact H.
Qed.

Lemma ext_non_vacuity : non_vacuity_clause ext_interface.
Proof.
  exists (E.PZero, E.CA), (EM (E.CHECK E.PZero E.CA)), (EM (E.COMMIT E.PZero E.CA)),
         (EM E.CERTIFY).
  split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
  split; [| split; [exists 0, 0; reflexivity | exists 1, 0; simpl; intro H; discriminate H]].
  intros a b. destruct a as [| a]; simpl; split; intro H;
    try reflexivity; try discriminate H.
Qed.

(* The exact toll holds when the extra move is priced and booked by its
   kind. *)
Lemma ext_exact_toll :
  x_cost = (match x_kind with KBase => 0 | _ => 1 end) ->
  (forall s, E.mu (x_step s) = E.mu s + x_cost) ->
  exact_toll_clause ext_interface.
Proof.
  intros Hc Hl. split.
  - intros [i |]; [destruct i; reflexivity | exact Hc].
  - intros s [i |]; [apply E.mu_conservation | apply Hl].
Qed.

End Extension.

Arguments ext_machine x_step x_cost : clear implicits.
Arguments ext_interface x_step x_cost x_kind : clear implicits.

(* ================================================================= *)
(* (a) fails: DROP lowers the record.                                 *)
(* ================================================================= *)

Definition drop_step (s : E.state) : E.state :=
  E.mkst (E.trap (E.core_of s)) (E.mu s) false.

Definition drop_machine : machine := ext_machine drop_step 0.
Definition drop_interface : thiele_interface drop_machine :=
  ext_interface drop_step 0 KBase.

(* A trapped state with the flag down stays that way. *)
Lemma drop_trapped_stays : forall l s,
  E.err (E.core_of s) = true -> E.cert s = false ->
  E.err (E.core_of (run drop_machine l s)) = true /\
  E.cert (run drop_machine l s) = false.
Proof.
  induction l as [| m l IH]; intros s He Hc; simpl; [auto |].
  apply IH.
  - destruct m as [i |]; simpl; [unfold E.cexec; rewrite He; exact He | reflexivity].
  - destruct m as [i |]; simpl; [| reflexivity].
    rewrite Hc. destruct i; simpl; try reflexivity.
    unfold E.certify_ok. rewrite He. reflexivity.
Qed.

(* A run that ends with the record up never used DROP. *)
Lemma drop_free_run : forall tr s0,
  E.cert (run drop_machine tr s0) = true -> exists tr', tr = map EM tr'.
Proof.
  induction tr as [| m tr IH]; intros s0 H; [exists []; reflexivity |].
  destruct m as [i |].
  - destruct (IH _ H) as [tr' ->]. exists (i :: tr'). reflexivity.
  - exfalso. simpl in H.
    destruct (drop_trapped_stays tr (drop_step s0) eq_refl eq_refl) as [_ Hc].
    rewrite Hc in H. discriminate.
Qed.

Theorem drop_meets_b_c_d :
  earned_record_clause drop_interface /\ exact_toll_clause drop_interface /\
  non_vacuity_clause drop_interface.
Proof.
  destruct (ext_record_parts drop_step 0 KBase) as [Hclean [Hsound Hresp]].
  split; [| split].
  - split; [exact Hclean |]. split; [| split; [exact Hsound | exact Hresp]].
    intros s0 tr H0 H1. destruct (drop_free_run tr s0 H1) as [tr' ->].
    apply ext_chain_transport. apply earned_chain_holds; [exact H0 |].
    rewrite <- (ext_run_map drop_step 0). exact H1.
  - apply ext_exact_toll; [reflexivity | intro s; simpl; lia].
  - apply ext_non_vacuity.
Qed.

(* A raised flag, and DROP. *)
Definition drop_witness : E.state := E.mkst (E.start_core 0 0) 0 true.

Lemma drop_not_permanent :
  m_record drop_machine drop_witness = true /\
  m_record drop_machine (m_step drop_machine drop_witness EX) = false.
Proof. split; reflexivity. Qed.

Theorem drop_fails_a : ~ universal_base_clause drop_interface.
Proof.
  intros [_ [_ [_ Hperm]]]. destruct drop_not_permanent as [H1 H2].
  rewrite (Hperm _ _ H1) in H2. discriminate.
Qed.

(* Permanence is a property of the machine, so no interface meets (a). *)
Theorem drop_not_thiele_complete : ~ thiele_complete drop_machine.
Proof.
  intros [I [[_ [_ [_ Hperm]]] _]]. destruct drop_not_permanent as [H1 H2].
  rewrite (Hperm _ _ H1) in H2. discriminate.
Qed.

Theorem drop_weakly_thiele_complete : weakly_thiele_complete drop_machine.
Proof.
  split; [| exact (inhabits (ext_base drop_step 0))].
  intros s [i |] H0 H1; simpl in *.
  - destruct (E.only_certify_certifies s i H0 H1) as [-> _]. simpl. lia.
  - discriminate.
Qed.

(* ================================================================= *)
(* (b) fails: FREE raises the record with nothing behind it.          *)
(* ================================================================= *)

Definition free_step (s : E.state) : E.state :=
  E.mkst (E.core_of s) (E.mu s + 1) (E.cert s || negb (E.err (E.core_of s))).

Definition free_machine : machine := ext_machine free_step 1.
Definition free_interface : thiele_interface free_machine :=
  ext_interface free_step 1 KCertify.

Theorem free_meets_a_c_d :
  universal_base_clause free_interface /\ exact_toll_clause free_interface /\
  non_vacuity_clause free_interface.
Proof.
  split; [| split].
  - split; [intros [[|] | [|] j]; reflexivity |].
    split; [intros a b; apply E.start_clean |]. split.
    + intros s [i |] Hk; simpl in Hk; [| discriminate].
      destruct i; simpl in Hk; try discriminate; simpl; apply orb_false_r.
    + intros s [i |] H; [apply E.cert_permanent, H |].
      change (E.cert s = true) in H. simpl. rewrite H. reflexivity.
  - apply ext_exact_toll; [reflexivity | intro s; reflexivity].
  - apply ext_non_vacuity.
Qed.

(* No earned chain fits in a run of one move. *)
Lemma chain_needs_three : forall M (I : thiele_interface M) s0 m,
  ~ earned_chain I s0 [m].
Proof.
  intros M I s0 m [pre [c [chk [mid1 [cmt [mid2 [crt [post [Htr _]]]]]]]]].
  apply (f_equal (@length _)) in Htr. simpl in Htr.
  rewrite !app_length in Htr. simpl in Htr. rewrite app_length in Htr. simpl in Htr.
  lia.
Qed.

Theorem free_fails_b : ~ earned_record_clause free_interface.
Proof.
  intros [_ [Hchain _]].
  apply (chain_needs_three _ free_interface (E.start 0 0) EX).
  apply Hchain; [apply E.start_clean | reflexivity].
Qed.

(* On a trapped state no move changes the record. *)
Lemma free_trapped_stays : forall l s,
  E.err (E.core_of s) = true ->
  E.err (E.core_of (run free_machine l s)) = true /\
  E.cert (run free_machine l s) = E.cert s.
Proof.
  induction l as [| m l IH]; intros s He; [simpl; auto |].
  change (run free_machine (m :: l) s) with (run free_machine l (m_step free_machine s m)).
  assert (He' : E.err (E.core_of (m_step free_machine s m)) = true /\
                E.cert (m_step free_machine s m) = E.cert s).
  { destruct m as [i |]; simpl.
    - unfold E.cexec. rewrite He. split; [exact He |].
      destruct i; simpl; try apply orb_false_r.
      unfold E.certify_ok. rewrite He. apply orb_false_r.
    - rewrite He. split; [reflexivity | apply orb_false_r]. }
  destruct He' as [He1 Hc1]. destruct (IH _ He1) as [He2 Hc2].
  split; [exact He2 | rewrite Hc2; exact Hc1].
Qed.

(* No interface makes it Thiele-complete. Clause (d) finds a loaded state
   from which the record rises, so its trap is down; it is clean by (a), so
   its record is down by (b); and FREE alone raises it, which (b) forbids. *)
Theorem free_not_thiele_complete : ~ thiele_complete free_machine.
Proof.
  intros [I [[_ [Hclean _]] [[Hdown [Hchain _]] [_ Hnv]]]].
  destruct Hnv as [c [chk [cmt [crt [_ [_ [_ [Hiff [[a [b Hyes]] _]]]]]]]]].
  apply Hiff in Hyes.
  set (s := load I a b) in *.
  assert (H0 : E.cert s = false) by (apply Hdown, Hclean).
  destruct (E.err (E.core_of s)) eqn:He.
  - destruct (free_trapped_stays [chk; cmt; crt] s He) as [_ Hc].
    simpl in Hyes, Hc. congruence.
  - apply (chain_needs_three _ I s EX). apply Hchain; [apply Hclean |].
    simpl. rewrite H0, He. reflexivity.
Qed.

Theorem free_weakly_thiele_complete : weakly_thiele_complete free_machine.
Proof.
  split; [| exact (inhabits (ext_base free_step 1))].
  intros s [i |] H0 H1; simpl in *.
  - destruct (E.only_certify_certifies s i H0 H1) as [-> _]. simpl. lia.
  - lia.
Qed.

(* ================================================================= *)
(* (c) fails: every move costs 1.                                     *)
(* ================================================================= *)

Definition paid_machine : machine :=
  mk_machine E.state E.instr E.exec (fun _ => 1) E.cert.

Lemma paid_run : forall tr s, run paid_machine tr s = run earned_machine tr s.
Proof. induction tr; intros; simpl; auto. Qed.

Definition paid_base : universal_base paid_machine :=
  mk_ub paid_machine (ub_window earned_base) (ub_live earned_base)
    (ub_compile earned_base) (ub_load earned_base)
    (ub_load_window earned_base) (ub_load_live earned_base) (ub_sim earned_base).

Definition paid_interface : thiele_interface paid_machine :=
  mk_ti paid_machine paid_base (E.prop * E.ctr) earned_kind
    (ti_meaning earned_interface) (ti_check earned_interface)
    (ti_same earned_interface) (ti_clean earned_interface) (ti_ledger earned_interface).

(* Clauses (a), (b) and (d) of the small machine, which never mention a
   price. *)
Lemma earned_clauses : thiele_complete_with earned_interface.
Proof.
  split; [| split; [| split]].
  - split; [intros [[|] | [|] j]; reflexivity |].
    split; [intros a b; apply E.start_clean |]. split.
    + intros s m Hk. destruct m; simpl in Hk; try discriminate; simpl;
        apply orb_false_r.
    + intros s m H. apply E.cert_permanent, H.
  - split; [intros s [_ [_ H]]; exact H |]. split.
    + intros s0 tr H0 H1. apply earned_chain_holds; [exact H0 |].
      rewrite <- run_earned. exact H1.
    + split.
      * intros s [p c] H. simpl in *. unfold E.check_ok in H.
        apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [_ H].
        apply E.eval_iff, H.
      * intros [p c] s t [_ Hw] H. simpl in *. rewrite <- Hw. exact H.
  - split; [intros []; reflexivity | intros s m; apply E.mu_conservation].
  - exists (E.PZero, E.CA), (E.CHECK E.PZero E.CA), (E.COMMIT E.PZero E.CA), E.CERTIFY.
    split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
    split; [| split; [exists 0, 0; reflexivity | exists 1, 0; simpl; intro H; discriminate H]].
    intros a b. destruct a as [| a]; simpl; split; intro H;
      try reflexivity; try discriminate H.
Qed.

Lemma paid_chain : forall s0 tr,
  earned_chain earned_interface s0 tr -> earned_chain paid_interface s0 tr.
Proof.
  intros s0 tr [pre [c [chk [mid1 [cmt [mid2 [crt [post
                [Htr [Hk1 [Hk2 [Hk3 [Hck [Hsame [Hdown Hup]]]]]]]]]]]]]]].
  exists pre, c, chk, mid1, cmt, mid2, crt, post.
  split; [exact Htr |]. split; [exact Hk1 |]. split; [exact Hk2 |]. split; [exact Hk3 |].
  split; [rewrite paid_run; exact Hck |].
  split; [intros t1 t2 Hm; rewrite !paid_run; exact (Hsame t1 t2 Hm) |].
  split; rewrite paid_run; assumption.
Qed.

Theorem paid_meets_a_b_d :
  universal_base_clause paid_interface /\ earned_record_clause paid_interface /\
  non_vacuity_clause paid_interface.
Proof.
  destruct earned_clauses as [[Hk [Hcl [Hb Hp]]] [[Hd [Hch [Hs Hr]]] [_ Hnv]]].
  split; [| split].
  - split; [exact Hk |]. split; [exact Hcl |]. split; [exact Hb | exact Hp].
  - split; [exact Hd |]. split; [| split; [exact Hs | exact Hr]].
    intros s0 tr H0 H1. apply paid_chain, Hch; [exact H0 |].
    rewrite <- paid_run. exact H1.
  - destruct Hnv as [c [chk [cmt [crt [Hk1 [Hk2 [Hk3 [Hiff [Hyes Hno]]]]]]]]].
    exists c, chk, cmt, crt.
    split; [exact Hk1 |]. split; [exact Hk2 |]. split; [exact Hk3 |].
    split; [intros a b; rewrite paid_run; apply Hiff |].
    split; [exact Hyes | exact Hno].
Qed.

Theorem paid_fails_c : ~ exact_toll_clause paid_interface.
Proof.
  intros [Hcost _]. specialize (Hcost (E.INC E.CA)). discriminate.
Qed.

Theorem paid_not_thiele_complete : ~ thiele_complete paid_machine.
Proof.
  intro H. destruct (complete_has_free_move _ H) as [m Hm]. discriminate.
Qed.

Theorem paid_weakly_thiele_complete : weakly_thiele_complete paid_machine.
Proof.
  split; [intros s m _ _; simpl; lia | exact (inhabits paid_base)].
Qed.

(* ================================================================= *)
(* The four together.                                                 *)
(* ================================================================= *)

Theorem thiele_complete_clauses_independent :
  (exists (M : machine) (I : thiele_interface M),
     ~ universal_base_clause I /\ earned_record_clause I /\ exact_toll_clause I /\
     non_vacuity_clause I /\ weakly_thiele_complete M /\ ~ thiele_complete M) /\
  (exists (M : machine) (I : thiele_interface M),
     universal_base_clause I /\ ~ earned_record_clause I /\ exact_toll_clause I /\
     non_vacuity_clause I /\ weakly_thiele_complete M /\ ~ thiele_complete M) /\
  (exists (M : machine) (I : thiele_interface M),
     universal_base_clause I /\ earned_record_clause I /\ ~ exact_toll_clause I /\
     non_vacuity_clause I /\ weakly_thiele_complete M /\ ~ thiele_complete M) /\
  (exists (M : machine) (I : thiele_interface M),
     universal_base_clause I /\ earned_record_clause I /\ exact_toll_clause I /\
     ~ non_vacuity_clause I /\ weakly_thiele_complete M /\ ~ thiele_complete M).
Proof.
  split; [| split; [| split]].
  - exists drop_machine, drop_interface.
    destruct drop_meets_b_c_d as [Hb [Hc Hd]].
    exact (conj drop_fails_a (conj Hb (conj Hc (conj Hd
             (conj drop_weakly_thiele_complete drop_not_thiele_complete))))).
  - exists free_machine, free_interface.
    destruct free_meets_a_c_d as [Ha [Hc Hd]].
    exact (conj Ha (conj free_fails_b (conj Hc (conj Hd
             (conj free_weakly_thiele_complete free_not_thiele_complete))))).
  - exists paid_machine, paid_interface.
    destruct paid_meets_a_b_d as [Ha [Hb Hd]].
    exact (conj Ha (conj Hb (conj paid_fails_c (conj Hd
             (conj paid_weakly_thiele_complete paid_not_thiele_complete))))).
  - exists silent, silent_interface.
    destruct silent_meets_base_record_toll as [Ha [Hb Hc]].
    refine (conj Ha (conj Hb (conj Hc (conj _
              (conj silent_weakly_thiele_complete silent_not_thiele_complete))))).
    intros [c [chk [cmt [crt [_ [_ [_ [Hiff [[a [b Hyes]] _]]]]]]]]].
    apply Hiff in Hyes. discriminate.
Qed.

(* ================================================================= *)
(* Assumption audit. Every line must print                            *)
(* "Closed under the global context".                                 *)
(* ================================================================= *)

Print Assumptions drop_meets_b_c_d.
Print Assumptions drop_fails_a.
Print Assumptions drop_not_thiele_complete.
Print Assumptions drop_weakly_thiele_complete.
Print Assumptions free_meets_a_c_d.
Print Assumptions free_fails_b.
Print Assumptions free_not_thiele_complete.
Print Assumptions free_weakly_thiele_complete.
Print Assumptions paid_meets_a_b_d.
Print Assumptions paid_fails_c.
Print Assumptions paid_not_thiele_complete.
Print Assumptions paid_weakly_thiele_complete.
Print Assumptions thiele_complete_clauses_independent.
