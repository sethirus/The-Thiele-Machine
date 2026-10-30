(** NecTUnclean.v: the clean-start hypothesis of only_certify_raises is needed.

    ThieleComplete.v proves that on a run from a clean state, the move that
    raises the record is a CERTIFY. Take any Thiele-complete machine and add
    one extra state W that no clean state can reach, from which every record
    move jumps to a state with the record up. The new machine is still
    Thiele-complete, and from W a CHECK raises the record. So "clean" cannot
    be dropped.

      [nec_t_unclean_start_breaks_only_certify]  for every Thiele-complete
        machine there is a Thiele-complete machine, a state, and a move that
        is not a CERTIFY, such that the move raises the record from that
        state. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Minimal.ThieleComplete.

Section Unclean.

Variable M : machine.
Variable I : thiele_interface M.
Variable s1 : m_state M.     (* a state with the record up *)
Hypothesis Hs1 : m_record M s1 = true.
Hypothesis Hl1 : 1 <= ti_ledger I s1.

Definition un_state : Type := (m_state M + unit)%type.

Definition un_step (s : un_state) (m : m_move M) : un_state :=
  match s with
  | inl x => inl (m_step M x m)
  | inr _ => match record_move I m with 0 => inr tt | _ => inl s1 end
  end.

Definition un_rec (s : un_state) : bool :=
  match s with inl x => m_record M x | inr _ => false end.

Definition un_machine : machine :=
  mk_machine un_state (m_move M) un_step (m_cost M) un_rec.

Definition un_base : universal_base un_machine :=
  mk_ub un_machine
    (fun s => match s with inl x => ub_window (ti_base I) x | inr _ => (1, (0, 0)) end)
    (fun s => match s with inl x => ub_live (ti_base I) x | inr _ => False end)
    (ub_compile (ti_base I))
    (fun a b => inl (ub_load (ti_base I) a b))
    (fun a b => ub_load_window (ti_base I) a b)
    (fun a b => ub_load_live (ti_base I) a b)
    (fun s i => match s as s0 return
         (match s0 with inl x => ub_live (ti_base I) x | inr _ => False end) ->
         (match un_step s0 (ub_compile (ti_base I) i) with
          | inl x => ub_window (ti_base I) x | inr _ => (1, (0, 0)) end) =
           cm_exec i (match s0 with inl x => ub_window (ti_base I) x | inr _ => (1, (0, 0)) end) /\
         (match un_step s0 (ub_compile (ti_base I) i) with
          | inl x => ub_live (ti_base I) x | inr _ => False end)
       with
       | inl x => fun Hl => ub_sim (ti_base I) x i Hl
       | inr _ => fun Hl => match Hl with end
       end).

Definition un_interface : thiele_interface un_machine :=
  mk_ti un_machine un_base (ti_claim I) (ti_kind I)
    (fun c s => match s with inl x => ti_meaning I c x | inr _ => True end)
    (fun s c => match s with inl x => ti_check I x c | inr _ => false end)
    (fun c s t => match s, t with
                  | inl x, inl y => ti_same I c x y
                  | inr _, inr _ => True
                  | _, _ => False
                  end)
    (fun s => match s with inl x => ti_clean I x | inr _ => False end)
    (fun s => match s with inl x => ti_ledger I x | inr _ => ti_ledger I s1 - 1 end).

Lemma un_run_inl : forall tr x, run un_machine tr (inl x) = inl (run M tr x).
Proof. induction tr as [| m tr IH]; intro x; simpl; [reflexivity | apply IH]. Qed.

Theorem un_complete : thiele_complete_with I -> thiele_complete_with un_interface.
Proof.
  intros [[Hk [Hclean [Hbase Hperm]]] [[Hb1 [Hb2 [Hb3 Hb4]]] [[Hc1 Hc2] Hd]]].
  split; [| split; [| split]].
  - split; [exact Hk |]. split; [exact Hclean |]. split.
    + intros [x | w] m Hkm; simpl in *; [apply Hbase; exact Hkm |].
      unfold record_move in *. rewrite Hkm. reflexivity.
    + intros [x | w] m H; simpl in *; [apply Hperm; exact H | discriminate H].
  - split; [intros [x | w] H; simpl in H; [apply Hb1; exact H | contradiction] |].
    split.
    + intros [x | w] tr Hcl Hr; simpl in Hcl; [| contradiction].
      cbn in Hr. rewrite un_run_inl in Hr. simpl in Hr.
      destruct (Hb2 x tr Hcl Hr)
        as [pre [c [chk [mid1 [cmt [mid2 [crt [post [Htr [K1 [K2 [K3 [Hck [Hs [Hf Ht]]]]]]]]]]]]]]].
      exists pre, c, chk, mid1, cmt, mid2, crt, post.
      split; [exact Htr |]. split; [exact K1 |]. split; [exact K2 |]. split; [exact K3 |].
      cbn. rewrite !un_run_inl. split; [exact Hck |].
      split; [intros t1 t2 Hm; specialize (Hs t1 t2 Hm); rewrite !un_run_inl; exact Hs |].
      split; [exact Hf | exact Ht].
    + split.
      * intros [x | w] c H; simpl in *; [apply Hb3, H | discriminate H].
      * intros c [x | w] [y | w'] H Hm; simpl in *; try contradiction; [eapply Hb4; eauto | exact Hm].
  - split; [exact Hc1 |].
    intros [x | w] m; simpl.
    + apply Hc2.
    + cbn. rewrite (Hc1 m). unfold un_step. destruct (record_move I m) eqn:E; cbn; [lia |].
      assert (Hle : record_move I m <= 1) by (unfold record_move; destruct (ti_kind I m); lia).
      rewrite E in Hle. lia.
  - destruct Hd as [c [chk [cmt [crt [Hk1 [Hk2 [Hk3 [Hiff [Hyes Hno]]]]]]]]].
    exists c, chk, cmt, crt. split; [exact Hk1 |]. split; [exact Hk2 |]. split; [exact Hk3 |].
    split; [| split; [exact Hyes | exact Hno]].
    intros a b. unfold load. cbn. exact (Hiff a b).
Qed.

End Unclean.

Theorem nec_t_unclean_start_breaks_only_certify : forall M,
  thiele_complete M ->
  exists (M' : machine) (I' : thiele_interface M') (w : m_state M') (m : m_move M'),
    thiele_complete_with I' /\ ~ ti_clean I' w /\ ti_kind I' m <> KCertify /\
    m_record M' w = false /\ m_record M' (m_step M' w m) = true.
Proof.
  intros M [I HC].
  destruct (some_run_certifies M I HC) as [a [b [tr [Hcl Hr]]]].
  destruct (certificate_costs_three M I HC (load I a b) tr Hcl Hr) as [_ Hled].
  set (s1 := run M tr (load I a b)) in *.
  assert (Hl1 : 1 <= ti_ledger I s1) by lia.
  pose proof HC as HC'.
  destruct HC' as [_ [_ [[Hc1 _] [c' [chk' [cmt' [crt' [Hk1 _]]]]]]]].
  exists (un_machine M I s1), (un_interface M I s1), (inr tt), chk'.
  split; [apply (un_complete M I s1 Hl1); exact HC |].
  split; [simpl; intro H; exact H |].
  split; [cbn; rewrite Hk1; discriminate |].
  split; [reflexivity |].
  cbn. unfold record_move. rewrite Hk1. exact Hr.
Qed.

Print Assumptions nec_t_unclean_start_breaks_only_certify.
