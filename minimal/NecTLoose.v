(** NecTLoose.v: the universal-base clause of Thiele-complete is necessary.

    Thiele-complete (ThieleComplete.v) asks for four clauses: (a) a
    universal base, (b) an earned record, (c) an exact toll and (d)
    non-vacuity. This file drops (a) and keeps the other three, in a form
    that mentions no universal base at all (the "loose" notion), and builds
    a machine that meets the loose notion and is not Thiele-complete.

    What is proved (every result closed under the global context):

      1. Every Thiele-complete machine meets the loose notion
         [nec_t_complete_is_loose]. So the loose notion is a genuine
         weakening of the definition.
      2. A machine with one free move that does nothing, and three record
         moves CHECK, COMMIT, CERTIFY that must come in that order, meets the
         loose notion [nec_t_nb_loose_complete] and is not Thiele-complete
         through any interface [nec_t_nb_not_thiele_complete]: its only
         free move cannot be the compiled form of both "increment A" and
         "increment B".
      3. Every Thiele-complete machine has a certificate that costs exactly
         3, not only at least 3 [nec_t_certificate_three_attained]. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Minimal.ThieleComplete.

(* ================================================================= *)
(* 1. Three is attained on every Thiele-complete machine.             *)
(* ================================================================= *)

Theorem nec_t_certificate_three_attained : forall M (I : thiele_interface M),
  thiele_complete_with I ->
  exists a b tr, ti_clean I (load I a b) /\
    m_record M (run M tr (load I a b)) = true /\
    record_moves I tr = 3 /\
    ti_ledger I (run M tr (load I a b)) = ti_ledger I (load I a b) + 3.
Proof.
  intros M I HC.
  destruct HC as [[_ [Hclean _]] [_ [Htoll Hnv]]].
  destruct Hnv as [c [chk [cmt [crt [Hk1 [Hk2 [Hk3 [Hiff [[a [b Hyes]] _]]]]]]]]].
  exists a, b, [chk; cmt; crt].
  split; [apply Hclean |].
  split; [apply Hiff, Hyes |].
  assert (Hm : record_moves I [chk; cmt; crt] = 3).
  { simpl. unfold record_move. rewrite Hk1, Hk2, Hk3. reflexivity. }
  split; [exact Hm |].
  rewrite (ledger_counts_record_moves M I Htoll), Hm. reflexivity.
Qed.

(* ================================================================= *)
(* 2. The loose notion: Thiele-complete without the universal base.   *)
(* ================================================================= *)

Record loose_interface (M : machine) : Type := mk_li {
  li_claim : Type;
  li_kind : m_move M -> kind li_claim;
  li_meaning : li_claim -> m_state M -> Prop;
  li_check : m_state M -> li_claim -> bool;
  li_same : li_claim -> m_state M -> m_state M -> Prop;
  li_clean : m_state M -> Prop;
  li_ledger : m_state M -> nat;
  li_load : nat -> nat -> m_state M
}.

Section LooseClauses.

Variable M : machine.
Variable L : loose_interface M.

(* (a) without the universal base: loaded states are clean, base moves
   leave the record alone, and the record stays up. *)
Definition loose_base_clause : Prop :=
  (forall a b, li_clean M L (li_load M L a b)) /\
  (forall s m, li_kind M L m = KBase -> m_record M (m_step M s m) = m_record M s) /\
  (forall s m, m_record M s = true -> m_record M (m_step M s m) = true).

Definition loose_earned_chain (s0 : m_state M) (tr : list (m_move M)) : Prop :=
  exists pre c chk mid1 cmt mid2 crt post,
    tr = pre ++ chk :: mid1 ++ cmt :: mid2 ++ crt :: post /\
    li_kind M L chk = KCheck c /\ li_kind M L cmt = KCommit c /\
    li_kind M L crt = KCertify /\
    li_check M L (run M pre s0) c = true /\
    (forall t1 t2, mid1 = t1 ++ t2 ->
       li_same M L c (run M pre s0) (run M (pre ++ chk :: t1) s0)) /\
    m_record M (run M (pre ++ chk :: mid1 ++ cmt :: mid2) s0) = false /\
    m_record M (run M (pre ++ chk :: mid1 ++ cmt :: mid2 ++ [crt]) s0) = true.

Definition loose_earned_record_clause : Prop :=
  (forall s, li_clean M L s -> m_record M s = false) /\
  (forall s0 tr, li_clean M L s0 -> m_record M (run M tr s0) = true ->
     loose_earned_chain s0 tr) /\
  (forall s c, li_check M L s c = true -> li_meaning M L c s) /\
  (forall c s s', li_same M L c s s' -> li_meaning M L c s -> li_meaning M L c s').

Definition loose_record_move (m : m_move M) : nat :=
  match li_kind M L m with KBase => 0 | _ => 1 end.

Definition loose_exact_toll_clause : Prop :=
  (forall m, m_cost M m = loose_record_move m) /\
  (forall s m, li_ledger M L (m_step M s m) = li_ledger M L s + m_cost M m).

Definition loose_non_vacuity_clause : Prop :=
  exists c chk cmt crt,
    li_kind M L chk = KCheck c /\ li_kind M L cmt = KCommit c /\
    li_kind M L crt = KCertify /\
    (forall a b, m_record M (run M [chk; cmt; crt] (li_load M L a b)) = true <->
                 li_meaning M L c (li_load M L a b)) /\
    (exists a b, li_meaning M L c (li_load M L a b)) /\
    (exists a b, ~ li_meaning M L c (li_load M L a b)).

Definition loose_complete_with : Prop :=
  loose_base_clause /\ loose_earned_record_clause /\
  loose_exact_toll_clause /\ loose_non_vacuity_clause.

End LooseClauses.

(* The interface of a Thiele-complete machine, forgetting its base. *)
Definition loose_of {M : machine} (I : thiele_interface M) : loose_interface M :=
  mk_li M (ti_claim I) (ti_kind I) (ti_meaning I) (ti_check I) (ti_same I)
    (ti_clean I) (ti_ledger I) (load I).

Theorem nec_t_complete_is_loose : forall M (I : thiele_interface M),
  thiele_complete_with I -> loose_complete_with M (loose_of I).
Proof.
  intros M I [[_ [Hclean [Hbase Hperm]]] [Hb [Hc Hd]]].
  split; [exact (conj Hclean (conj Hbase Hperm)) |].
  split; [exact Hb |]. split; [exact Hc | exact Hd].
Qed.

(* ================================================================= *)
(* 3. A machine with a trivial base that meets the loose notion.      *)
(* ================================================================= *)

Inductive nb_st : Type := NZ | NN | NK | NM | NC | ND.
Inductive nb_mv : Type := NCHK | NCMT | NCRT | NNOP.

(* Z: loaded, claim true. N: loaded, claim false. K: checked. M: committed.
   C: certified. D: dead. The three record moves must come in order; the
   free move NNOP changes nothing. *)
Definition nb_stst (s : nb_st) (m : nb_mv) : nb_st :=
  match s, m with
  | NC, _ => NC
  | NZ, NCHK => NK
  | NZ, NNOP => NZ
  | NN, NNOP => NN
  | NK, NCMT => NM
  | NK, NNOP => NK
  | NM, NCRT => NC
  | NM, NNOP => NM
  | _, _ => ND
  end.

Definition nb_cost (m : nb_mv) : nat :=
  match m with NNOP => 0 | _ => 1 end.

Definition nb_step (x : nb_st * nat) (m : nb_mv) : nb_st * nat :=
  (nb_stst (fst x) m, snd x + nb_cost m).

Definition nb_rec (x : nb_st * nat) : bool :=
  match fst x with NC => true | _ => false end.

Definition nb_machine : machine :=
  mk_machine (nb_st * nat) nb_mv nb_step nb_cost nb_rec.

Definition nb_isZ (x : nb_st * nat) : bool :=
  match fst x with NZ => true | _ => false end.

Definition nb_loose : loose_interface nb_machine :=
  mk_li nb_machine unit
    (fun m => match m with
              | NCHK => KCheck tt
              | NCMT => KCommit tt
              | NCRT => KCertify
              | NNOP => KBase
              end)
    (fun _ x => match fst x with NZ | NK | NM | NC => True | _ => False end)
    (fun x _ => nb_isZ x)
    (fun _ x y => x = y \/ (fst x = NZ /\ fst y = NK))
    (fun x => fst x = NZ \/ fst x = NN)
    (fun x => snd x)
    (fun a b => ((if a =? 0 then NZ else NN), 0)).

Definition nbn (p : nat) : list nb_mv := repeat NNOP p.

Lemma nb_allnop : forall tr x, (forall m, In m tr -> m = NNOP) ->
  run nb_machine tr x = x.
Proof.
  induction tr as [| m tr IH]; intros [s l] H; simpl; [reflexivity |].
  assert (Hm : m = NNOP) by (apply H; left; reflexivity). subst m.
  simpl. unfold nb_step. simpl.
  rewrite Nat.add_0_r.
  assert (Hs : nb_stst s NNOP = s) by (destruct s; reflexivity).
  rewrite Hs. apply IH. intros m Hin. apply H. right. exact Hin.
Qed.

Lemma nb_nops : forall p x, run nb_machine (nbn p) x = x.
Proof.
  intros p x. apply nb_allnop. intros m Hin. unfold nbn in Hin.
  apply repeat_spec in Hin. exact Hin.
Qed.

Lemma nb_dead : forall tr l, fst (run nb_machine tr (ND, l)) = ND.
Proof.
  induction tr as [| m tr IH]; intro l; simpl; [reflexivity |].
  unfold nb_step. simpl. destruct m; apply IH.
Qed.

Lemma nb_N : forall tr l, fst (run nb_machine tr (NN, l)) <> NC.
Proof.
  induction tr as [| m tr IH]; intro l; simpl; [discriminate |].
  unfold nb_step. simpl. destruct m; simpl.
  - rewrite nb_dead. discriminate.
  - rewrite nb_dead. discriminate.
  - rewrite nb_dead. discriminate.
  - apply IH.
Qed.

Lemma nb_M : forall tr l, fst (run nb_machine tr (NM, l)) = NC ->
  exists p post, tr = nbn p ++ NCRT :: post.
Proof.
  induction tr as [| m tr IH]; intros l H; simpl in H; [discriminate |].
  unfold nb_step in H. simpl in H. destruct m.
  - rewrite nb_dead in H. discriminate.
  - rewrite nb_dead in H. discriminate.
  - exists 0, tr. reflexivity.
  - destruct (IH _ H) as [p [post Htr]]. exists (S p), post.
    rewrite Htr. reflexivity.
Qed.

Lemma nb_K : forall tr l, fst (run nb_machine tr (NK, l)) = NC ->
  exists p2 p3 post, tr = nbn p2 ++ NCMT :: nbn p3 ++ NCRT :: post.
Proof.
  induction tr as [| m tr IH]; intros l H; simpl in H; [discriminate |].
  unfold nb_step in H. simpl in H. destruct m.
  - rewrite nb_dead in H. discriminate.
  - destruct (nb_M tr _ H) as [p [post Htr]]. exists 0, p, post.
    rewrite Htr. reflexivity.
  - rewrite nb_dead in H. discriminate.
  - destruct (IH _ H) as [p2 [p3 [post Htr]]]. exists (S p2), p3, post.
    rewrite Htr. reflexivity.
Qed.

Lemma nb_Z : forall tr l, fst (run nb_machine tr (NZ, l)) = NC ->
  exists p1 p2 p3 post,
    tr = nbn p1 ++ NCHK :: nbn p2 ++ NCMT :: nbn p3 ++ NCRT :: post.
Proof.
  induction tr as [| m tr IH]; intros l H; simpl in H; [discriminate |].
  unfold nb_step in H. simpl in H. destruct m.
  - destruct (nb_K tr _ H) as [p2 [p3 [post Htr]]]. exists 0, p2, p3, post.
    rewrite Htr. reflexivity.
  - rewrite nb_dead in H. discriminate.
  - rewrite nb_dead in H. discriminate.
  - destruct (IH _ H) as [p1 [p2 [p3 [post Htr]]]]. exists (S p1), p2, p3, post.
    rewrite Htr. reflexivity.
Qed.

Lemma nb_in_nbn : forall m p, In m (nbn p) -> m = NNOP.
Proof. intros m p H. unfold nbn in H. apply repeat_spec in H. exact H. Qed.

Lemma nb_chain_run : forall p1 p2 p3 tl l,
  run nb_machine (nbn p1 ++ NCHK :: nbn p2 ++ NCMT :: nbn p3 ++ tl) (NZ, l) =
  run nb_machine tl (NM, l + 2).
Proof.
  intros p1 p2 p3 tl l.
  rewrite run_app, nb_nops. simpl run. unfold nb_step at 1. simpl.
  rewrite run_app, nb_nops. simpl run. unfold nb_step at 1. simpl.
  rewrite run_app, nb_nops. simpl run. 
  replace (l + 1 + 1) with (l + 2) by lia. reflexivity.
Qed.

Theorem nec_t_nb_loose_complete : loose_complete_with nb_machine nb_loose.
Proof.
  split; [| split; [| split]].
  - (* base clause *)
    split; [intros a b; simpl; destruct (a =? 0); [left | right]; reflexivity |].
    split.
    + intros [s l] m Hk. destruct m; simpl in Hk; try discriminate.
      unfold nb_machine, nb_step, nb_rec. simpl.
      assert (Hs : nb_stst s NNOP = s) by (destruct s; reflexivity).
      rewrite Hs. reflexivity.
    + intros [s l] m H. unfold nb_machine, nb_step, nb_rec in *. simpl in *.
      destruct s; try discriminate H; destruct m; reflexivity.
  - (* earned record clause *)
    split; [intros [s l] [Hs | Hs]; simpl in Hs; subst; reflexivity |].
    split; [| split].
    + intros [s0 l] tr Hclean Hrec. simpl in Hclean.
      destruct Hclean as [Hs | Hs]; simpl in Hs; subst s0.
      * assert (Hc : fst (run nb_machine tr (NZ, l)) = NC).
        { change (nb_rec (run nb_machine tr (NZ, l)) = true) in Hrec.
          unfold nb_rec in Hrec.
          destruct (fst (run nb_machine tr (NZ, l))); try discriminate Hrec; reflexivity. }
        destruct (nb_Z tr l Hc) as [p1 [p2 [p3 [post Htr]]]].
        unfold loose_earned_chain. simpl.
        exists (nbn p1), tt, NCHK, (nbn p2), NCMT, (nbn p3), NCRT, post.
        split; [exact Htr |]. split; [reflexivity |]. split; [reflexivity |].
        split; [reflexivity |].
        rewrite nb_nops. split; [reflexivity |].
        split.
        { intros t1 t2 Hm. rewrite run_app, nb_nops. right. split; [reflexivity |].
          assert (Hall : forall m, In m t1 -> m = NNOP).
          { intros m Hin. apply (nb_in_nbn m p2). rewrite Hm. apply in_or_app. left. exact Hin. }
          simpl. unfold nb_step. simpl. rewrite nb_allnop; [reflexivity | exact Hall]. }
        replace (nbn p1 ++ NCHK :: nbn p2 ++ NCMT :: nbn p3) with
          (nbn p1 ++ NCHK :: nbn p2 ++ NCMT :: nbn p3 ++ []) by (rewrite app_nil_r; reflexivity).
        rewrite nb_chain_run. replace (nbn p1 ++ NCHK :: nbn p2 ++ NCMT :: nbn p3 ++ [NCRT]) with
          (nbn p1 ++ NCHK :: nbn p2 ++ NCMT :: nbn p3 ++ [NCRT]) by reflexivity.
        rewrite nb_chain_run. simpl run. unfold nb_step. simpl.
        split; reflexivity.
      * exfalso. apply (nb_N tr l).
        change (nb_rec (run nb_machine tr (NN, l)) = true) in Hrec.
        unfold nb_rec in Hrec.
        destruct (fst (run nb_machine tr (NN, l))); try discriminate Hrec; reflexivity.
    + intros [s l] [] Hc. simpl in *. unfold nb_isZ in Hc. destruct s; simpl in Hc;
        try discriminate Hc; exact I.
    + intros [] [s l] [t l'] Hsame Hm. simpl in *.
      destruct Hsame as [Heq | [Hs Ht]].
      * inversion Heq; subst. exact Hm.
      * simpl in Hs, Ht. rewrite Ht. exact I.
  - (* exact toll *)
    split; [intros m; destruct m; reflexivity |].
    intros [s l] m. destruct m; reflexivity.
  - (* non-vacuity *)
    exists tt, NCHK, NCMT, NCRT. split; [reflexivity |]. split; [reflexivity |].
    split; [reflexivity |]. split.
    + intros a b. simpl. destruct (a =? 0) eqn:Ea; simpl; split; intro H;
        try reflexivity; try exact I; try discriminate H; try contradiction.
    + split; [exists 0, 0; simpl; exact I |].
      exists 1, 0. simpl. intro H. exact H.
Qed.

(* The base clause of Thiele-complete is not implied by the other three:
   no interface at all makes this machine Thiele-complete. *)
Theorem nec_t_nb_not_thiele_complete : ~ thiele_complete nb_machine.
Proof.
  intros [I [[Hk [_ _]] [_ [[Hcost _] _]]]].
  (* every compiled move is a base move, and a base move costs 0, so it is NNOP *)
  assert (Hfree : forall i, ub_compile (ti_base I) i = NNOP).
  { intro i. specialize (Hk i). pose proof (Hcost (ub_compile (ti_base I) i)) as Hc.
    unfold record_move in Hc. rewrite Hk in Hc.
    destruct (ub_compile (ti_base I) i); simpl in Hc; try discriminate Hc; reflexivity. }
  set (s0 := ub_load (ti_base I) 0 0).
  destruct (ub_sim (ti_base I) s0 (CINC RA) (ub_load_live (ti_base I) 0 0)) as [HA _].
  destruct (ub_sim (ti_base I) s0 (CINC RB) (ub_load_live (ti_base I) 0 0)) as [HB _].
  rewrite (Hfree (CINC RA)) in HA. rewrite (Hfree (CINC RB)) in HB.
  rewrite HA in HB. unfold s0 in HB. rewrite ub_load_window in HB. simpl in HB.
  discriminate HB.
Qed.

Print Assumptions nec_t_certificate_three_attained.
Print Assumptions nec_t_complete_is_loose.
Print Assumptions nec_t_nb_loose_complete.
Print Assumptions nec_t_nb_not_thiele_complete.
