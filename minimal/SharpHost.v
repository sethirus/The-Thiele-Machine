(* SCOPE NOTE: standalone proof scope.
   Constructs finite hosts attaining the abstract permanent-holding capacity bound.
   The stated interface supplies the hypotheses; no concrete native-machine
   implementation is assumed. *)

From Coq Require Import List Arith Lia Vectors.Fin.
From Minimal Require Import CompleteHost.
Import ListNotations.

(* A genuinely finite state type. Natural labels are only coordinates;
   there are no unused states beyond the last held state. *)
Section Construction.
  Variables T K : nat.
  Hypothesis T_positive : 1 <= T.
  Hypothesis K_positive : 1 <= K.

  Definition HostState := Fin.t (S (T+K)).
  Definition index (s : HostState) := proj1_sig (Fin.to_nat s).
  Lemma index_bound : forall s, index s <= T+K.
  Proof.
    intro s; pose proof (proj2_sig (Fin.to_nat s)) as H.
    change (index s < S (T+K)) in H; lia.
  Qed.
  Lemma index_injective : forall a b, index a=index b -> a=b.
  Proof. apply Fin.to_nat_inj. Qed.

  Definition node (n : nat) : HostState :=
    Fin.of_nat_lt (proj2 (Nat.lt_succ_r _ _) (Nat.le_min_r n (T+K))).

  Lemma index_node : forall n, index (node n)=Nat.min n (T+K).
  Proof. intro n; unfold index,node; rewrite Fin.to_nat_of_nat; reflexivity. Qed.
  Lemma index_node_small : forall n, n<=T+K -> index (node n)=n.
  Proof. intros; rewrite index_node, Nat.min_l; auto. Qed.
  Lemma node_index : forall s, node (index s)=s.
  Proof. intro s; apply index_injective; apply index_node_small; apply index_bound. Qed.

  Definition step (s : HostState) := node (S (index s)).
  Definition prep := node 0.
  Definition start := node 1.
  Definition entry := node T.
  Definition all_states := map node (seq 0 (S (T+K))).
  Definition held_states := map node (seq (S T) K).
  Definition held (s : HostState) := T < index s.

  Lemma step_index : forall s,
    index (step s)=Nat.min (S (index s)) (T+K).
  Proof. intro s; unfold step; apply index_node. Qed.

  Lemma step_node : forall n,
    step (node n)=node (S n).
  Proof.
    intro n; apply index_injective; rewrite step_index, !index_node.
    destruct (le_dec n (T+K)) as [H|H].
    - rewrite (Nat.min_l n (T+K)) by lia; reflexivity.
    - rewrite (Nat.min_r n (T+K)) by lia.
      rewrite !Nat.min_r by lia; reflexivity.
  Qed.

  Lemma iter_node : forall n a, iter step n (node a)=node (n+a).
  Proof.
    induction n; intro a; simpl; [reflexivity|].
    rewrite IHn, step_node; reflexivity.
  Qed.

  Lemma all_states_exact : forall s, In s all_states.
  Proof.
    intro s; unfold all_states; apply in_map_iff; exists (index s).
    split; [apply node_index|apply in_seq; pose proof (index_bound s); lia].
  Qed.
  Lemma all_states_nodup : NoDup all_states.
  Proof.
    unfold all_states; apply nodup_map_on; [apply seq_NoDup|].
    intros a b Ha Hb E; apply in_seq in Ha; apply in_seq in Hb.
    apply (f_equal index) in E; rewrite !index_node_small in E by lia; exact E.
  Qed.
  Lemma all_states_count : length all_states=1+T+K.
  Proof. unfold all_states; rewrite map_length,seq_length; lia. Qed.
  Lemma held_states_exact : forall s, In s held_states <-> held s.
  Proof.
    intro s; unfold held_states,held; rewrite in_map_iff; split.
    - intros [n [<- Hn]]; apply in_seq in Hn; rewrite index_node_small by lia; lia.
    - intro Hs; exists (index s); split; [apply node_index|].
      apply in_seq; pose proof (index_bound s); lia.
  Qed.
  Lemma held_states_nodup : NoDup held_states.
  Proof.
    unfold held_states; apply nodup_map_on; [apply seq_NoDup|].
    intros a b Ha Hb E; apply in_seq in Ha; apply in_seq in Hb.
    apply (f_equal index) in E; rewrite !index_node_small in E by lia; exact E.
  Qed.
  Lemma held_states_count : length held_states=K.
  Proof. unfold held_states; rewrite map_length,seq_length; reflexivity. Qed.
  Lemma entry_outside : ~held entry.
  Proof. unfold held,entry; rewrite index_node_small by lia; lia. Qed.
  Lemma entry_enters : held (step entry).
  Proof. unfold held,entry; rewrite step_node,index_node_small by lia; lia. Qed.
  Lemma held_closed : forall s, held s -> held (step s).
  Proof.
    intros s Hs; unfold held in *; rewrite step_index; apply Nat.min_glb_lt; lia.
  Qed.

  (* Exactly K source states, including the last running state, retain
     their identities. Adding the next source introduces the first collision. *)
  Theorem retains_capacity : retains step entry K.
  Proof.
    intros i j Hi Hj E; unfold entry in *; rewrite !iter_node in *.
    rewrite !step_node in E; apply (f_equal index) in E.
    rewrite !index_node_small in E by lia.
    assert (i=j) by lia; subst; reflexivity.
  Qed.
  Theorem first_collision :
    iter step (K-1) entry <> iter step K entry /\
    step (iter step (K-1) entry)=step (iter step K entry).
  Proof.
    unfold entry; rewrite !iter_node; split.
    - intro E; apply (f_equal index) in E.
      rewrite !index_node_small in E by lia; lia.
    - rewrite !step_node; apply index_injective; rewrite !index_node.
      repeat rewrite Nat.min_r by lia; reflexivity.
  Qed.
  Theorem fails_next_capacity : ~retains step entry (S K).
  Proof.
    intro Hr; destruct first_collision as [Hneq Heq]; apply Hneq.
    apply Hr; try lia; exact Heq.
  Qed.
  Theorem capacity_exact : forall L, retains step entry L <-> L<=K.
  Proof.
    intro L; split.
    - intro Hr.
      pose proof (@held_prefix_capacity HostState step held entry
        entry_outside entry_enters held_closed L held_states Hr
        (fun s Hs => proj2 (held_states_exact s) Hs)) as H.
      rewrite held_states_count in H; exact H.
    - intros HL i j Hi Hj E; apply retains_capacity; try lia; exact E.
  Qed.

  Section Guest.
    Context {G : Type}.
    Variable delta : G -> option G.
    Variable trace : nat -> G.
    Hypothesis trace_steps : forall n, n<T -> delta (trace n)=Some (trace (S n)).
    Hypothesis terminal : delta (trace T)=None.

    Definition view (s : HostState) : option G :=
      match index s with 0 => None | S n => Some (trace (Nat.min n T)) end.

    Lemma early_not_terminal : forall n, n<T -> trace n<>trace T.
    Proof.
      intros n Hn E; pose proof (trace_steps n Hn) as H;
        rewrite E,terminal in H; discriminate.
    Qed.
    Lemma view_prep : view prep=None.
    Proof. unfold view,prep; rewrite index_node_small by lia; reflexivity. Qed.
    Lemma prepares_start : step prep=start.
    Proof. unfold prep,start; apply step_node. Qed.
    Lemma view_node_positive : forall n, n<=T+K ->
      view (node (S n))=Some (trace (Nat.min n T)).
    Proof.
      intros n Hn; unfold view; rewrite index_node.
      destruct (le_dec (S n) (T+K)) as [H|H].
      - rewrite Nat.min_l by lia; reflexivity.
      - rewrite Nat.min_r by lia.
        assert (E:T+K=S (T+K-1)) by lia; rewrite E at 1.
        rewrite !Nat.min_r by lia; reflexivity.
    Qed.
    Lemma view_start : view start=Some (trace 0).
    Proof. unfold start; rewrite view_node_positive by lia; reflexivity. Qed.
    Lemma view_held_exact : forall s, view s=Some (trace T) <-> held s.
    Proof.
      intro s; unfold view,held; destruct (index s) as [|n] eqn:E.
      - split; [discriminate|lia].
      - destruct (lt_dec n T) as [Hn|Hn].
        + rewrite Nat.min_l by lia; split; [|lia].
          intro H; injection H as H; exfalso; eapply early_not_terminal; eauto.
        + rewrite Nat.min_r by lia; split; auto; lia.
    Qed.
    Lemma view_holds : forall s, view s=Some (trace T) ->
      view (step s)=Some (trace T).
    Proof. intros s H; apply view_held_exact,held_closed,view_held_exact; exact H. Qed.

    Lemma view_simulates : forall s c d,
      view s=Some c -> delta c=Some d -> view (step s)=Some d.
    Proof.
      intros s c d Hv Hd; unfold view in Hv.
      destruct (index s) as [|n] eqn:E; [discriminate|].
      destruct (lt_dec n T) as [Hn|Hn].
      - rewrite Nat.min_l in Hv by lia; injection Hv as Hv; subst c.
        rewrite trace_steps in Hd by lia; injection Hd as Hd; subst d.
        unfold step; rewrite E,view_node_positive by lia.
        rewrite Nat.min_l by lia; reflexivity.
      - rewrite Nat.min_r in Hv by lia; injection Hv as Hv; subst c.
        rewrite terminal in Hd; discriminate.
    Qed.

    Theorem guest_all_time : forall n,
      view (iter step n start)=Some (trace (Nat.min n T)).
    Proof.
      intro n; unfold start; rewrite iter_node.
      replace (n+1) with (S n) by lia.
      destruct (le_dec n (T+K)) as [Hn|Hn].
      - apply view_node_positive; exact Hn.
      - assert (En:node (S n)=node (T+K)).
        { apply index_injective; rewrite !index_node, !Nat.min_r by lia; reflexivity. }
        rewrite En; replace (T+K) with (S (T+K-1)) by lia.
        rewrite view_node_positive by lia; rewrite !Nat.min_r by lia; reflexivity.
    Qed.
    Lemma entry_is_last_running : entry=iter step (T-1) start.
    Proof. unfold entry,start; rewrite iter_node; f_equal; lia. Qed.

    (* Existential witness for every supplied deterministic halting trace.
       This constructs a host for that trace; it is not a halting decider. *)
    Theorem sharp_finite_host_exists :
      exists (F : HostState -> HostState) (v : HostState -> option G)
        (pre a u : HostState) (all hs : list HostState),
      NoDup all /\ (forall s, In s all) /\ length all=1+T+K /\
      NoDup hs /\ length hs=K /\
      (forall s, In s hs <-> v s=Some (trace T)) /\
      v pre=None /\ F pre=a /\ v a=Some (trace 0) /\
      (forall s c d, v s=Some c -> delta c=Some d -> v (F s)=Some d) /\
      (forall s, v s=Some (trace T) -> v (F s)=Some (trace T)) /\
      (forall n, v (iter F n a)=Some (trace (Nat.min n T))) /\
      u=iter F (T-1) a /\
      (forall L, retains F u L <-> L<=K) /\
      (iter F (K-1) u <> iter F K u /\
       F (iter F (K-1) u)=F (iter F K u)).
    Proof.
      exists step,view,prep,start,entry,all_states,held_states.
      split; [apply all_states_nodup|].
      split; [apply all_states_exact|].
      split; [apply all_states_count|].
      split; [apply held_states_nodup|].
      split; [apply held_states_count|].
      split; [intro s; rewrite held_states_exact,view_held_exact; reflexivity|].
      split; [apply view_prep|].
      split; [apply prepares_start|].
      split; [apply view_start|].
      split; [apply view_simulates|].
      split; [apply view_holds|].
      split; [apply guest_all_time|].
      split; [apply entry_is_last_running|].
      split; [apply capacity_exact|apply first_collision].
    Qed.
  End Guest.
End Construction.
