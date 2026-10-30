(** NecTLoop.v: the ledger half of the exact-toll clause is necessary, for the
    machine and not only for one interface.

    Take any Thiele-complete machine and add one move LOOP that costs 1 and
    changes nothing. Read LOOP as a CHECK. The universal base, the earned
    record, non-vacuity and the first half of the exact toll (every move
    costs what its kind says) all still hold. What cannot hold is that the
    ledger grows by the cost of each move: a ledger is a function of the
    state, LOOP leaves the state where it was, and it costs 1. So no ledger
    exists, and the machine is not Thiele-complete through any interface.

      [nec_t_loop_meets_all_but_ledger]  the interface that reads LOOP as a
        CHECK meets the base clause, the earned-record clause, non-vacuity
        and the cost half of the toll, and fails the ledger half.
      [nec_t_loop_not_thiele_complete]  the machine with LOOP is not
        Thiele-complete, through any interface. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Minimal.ThieleComplete.

Definition loop_machine (M : machine) : machine :=
  mk_machine (m_state M) (option (m_move M))
    (fun s o => match o with Some m => m_step M s m | None => s end)
    (fun o => match o with Some m => m_cost M m | None => 1 end)
    (m_record M).

(* The moves of M with the LOOP moves taken out. *)
Fixpoint strip {M : machine} (tr : list (option (m_move M))) : list (m_move M) :=
  match tr with
  | [] => []
  | None :: rest => strip rest
  | Some m :: rest => m :: strip rest
  end.

Lemma strip_app : forall M (l1 l2 : list (option (m_move M))),
  strip (l1 ++ l2) = strip l1 ++ strip l2.
Proof.
  intros M. induction l1 as [| [m |] l1 IH]; intro l2; simpl; [reflexivity | | apply IH].
  rewrite IH. reflexivity.
Qed.

Lemma loop_run : forall M tr s, run (loop_machine M) tr s = run M (strip tr) s.
Proof.
  intros M. induction tr as [| [m |] tr IH]; intro s; simpl; [reflexivity | apply IH | apply IH].
Qed.

(* A decomposition of the stripped trace lifts to the trace. *)
Lemma strip_split : forall M (tr : list (option (m_move M))) A x B,
  strip tr = A ++ x :: B ->
  exists A0 B0, tr = A0 ++ Some x :: B0 /\ strip A0 = A /\ strip B0 = B.
Proof.
  intros M. induction tr as [| [m |] tr IH]; intros A x B H; simpl in H.
  - destruct A; discriminate H.
  - destruct A as [| a A].
    + simpl in H. injection H as Hm Hr. subst m.
      exists [], tr. simpl. repeat split. exact Hr.
    + simpl in H. injection H as Hm Hr. subst a.
      destruct (IH A x B Hr) as [A0 [B0 [Htr [HA HB]]]].
      exists (Some m :: A0), B0. rewrite Htr. simpl. rewrite HA. repeat split; auto.
  - destruct (IH A x B H) as [A0 [B0 [Htr [HA HB]]]].
    exists (None :: A0), B0. rewrite Htr. simpl. repeat split; auto.
Qed.

Definition loop_base {M : machine} (U : universal_base M) : universal_base (loop_machine M) :=
  mk_ub (loop_machine M) (ub_window U) (ub_live U)
    (fun i => Some (ub_compile U i)) (ub_load U)
    (ub_load_window U) (ub_load_live U) (ub_sim U).

Definition loop_interface {M : machine} (I : thiele_interface M) (c0 : ti_claim I) :
  thiele_interface (loop_machine M) :=
  mk_ti (loop_machine M) (loop_base (ti_base I)) (ti_claim I)
    (fun o => match o with Some m => ti_kind I m | None => KCheck c0 end)
    (ti_meaning I) (ti_check I) (ti_same I) (ti_clean I) (ti_ledger I).

Theorem nec_t_loop_meets_all_but_ledger : forall M (I : thiele_interface M),
  thiele_complete_with I ->
  exists c0 : ti_claim I,
    universal_base_clause (loop_interface I c0) /\
    earned_record_clause (loop_interface I c0) /\
    non_vacuity_clause (loop_interface I c0) /\
    (forall m, m_cost (loop_machine M) m = record_move (loop_interface I c0) m) /\
    ~ exact_toll_clause (loop_interface I c0).
Proof.
  intros M I HC.
  destruct HC as [[Hk [Hclean [Hbase Hperm]]] [[Hb1 [Hb2 [Hb3 Hb4]]] [[Hc1 Hc2] Hd]]].
  destruct Hd as [c [chk [cmt [crt [Hk1 [Hk2 [Hk3 [Hiff [Hyes Hno]]]]]]]]].
  exists c.
  split; [| split; [| split; [| split]]].
  - (* base clause *)
    split; [intro i; simpl; apply Hk |].
    split; [intros a b; simpl; apply Hclean |].
    split.
    + intros s [m |] Hkm; simpl in *; [apply Hbase; exact Hkm | discriminate Hkm].
    + intros s [m |] H; simpl in *; [apply Hperm; exact H | exact H].
  - (* earned record clause *)
    split; [exact Hb1 |]. split; [| split; [exact Hb3 | exact Hb4]].
    intros s0 tr Hcl Hr. cbn in Hr. rewrite loop_run in Hr.
    destruct (Hb2 s0 (strip tr) Hcl Hr)
      as [pre [c' [chk' [mid1 [cmt' [mid2 [crt' [post [Htr [K1 [K2 [K3 [Hck [Hs [Hf Ht]]]]]]]]]]]]]]].
    destruct (strip_split M tr pre chk' _ Htr) as [pre0 [R1 [Htr1 [Hp0 HR1]]]].
    destruct (strip_split M R1 mid1 cmt' _ HR1) as [mid1_0 [R2 [HR1' [Hm1 HR2]]]].
    destruct (strip_split M R2 mid2 crt' post HR2) as [mid2_0 [post0 [HR2' [Hm2 Hpost]]]].
    assert (E1 : strip (pre0 ++ Some chk' :: mid1_0 ++ Some cmt' :: mid2_0) =
                 pre ++ chk' :: mid1 ++ cmt' :: mid2).
    { repeat (rewrite strip_app; simpl). rewrite Hp0, Hm1, Hm2. reflexivity. }
    assert (E2 : strip (pre0 ++ Some chk' :: mid1_0 ++ Some cmt' :: mid2_0 ++ [Some crt']) =
                 pre ++ chk' :: mid1 ++ cmt' :: mid2 ++ [crt']).
    { repeat (rewrite strip_app; simpl). rewrite Hp0, Hm1, Hm2. reflexivity. }
    exists pre0, c', (Some chk'), mid1_0, (Some cmt'), mid2_0, (Some crt'), post0.
    split; [rewrite Htr1, HR1', HR2'; reflexivity |].
    split; [exact K1 |]. split; [exact K2 |]. split; [exact K3 |].
    split; [cbn; rewrite loop_run, Hp0; exact Hck |].
    split.
    + intros t1 t2 Hm. cbn. rewrite !loop_run.
      assert (Hst : mid1 = strip t1 ++ strip t2) by (rewrite <- Hm1, Hm, strip_app; reflexivity).
      pose proof (Hs (strip t1) (strip t2) Hst) as Hsame.
      rewrite strip_app. simpl. rewrite Hp0. exact Hsame.
    + split.
      * cbn. rewrite loop_run, E1. exact Hf.
      * cbn. rewrite loop_run, E2. exact Ht.
  - (* non-vacuity *)
    exists c, (Some chk), (Some cmt), (Some crt).
    split; [exact Hk1 |]. split; [exact Hk2 |]. split; [exact Hk3 |].
    split; [| split; [exact Hyes | exact Hno]].
    intros a b. cbn. exact (Hiff a b).
  - (* cost half of the toll *)
    intros [m |]; cbn; [apply Hc1 | reflexivity].
  - (* the ledger half fails *)
    intros [_ H]. specialize (H (ub_load (ti_base I) 0 0) None). cbn in H. lia.
Qed.

Theorem nec_t_loop_not_thiele_complete : forall M, ~ thiele_complete (loop_machine M).
Proof.
  intros M [I [_ [_ [[_ H] _]]]].
  specialize (H (ub_load (ti_base I) 0 0) None). cbn in H. lia.
Qed.

Print Assumptions nec_t_loop_meets_all_but_ledger.
Print Assumptions nec_t_loop_not_thiele_complete.
