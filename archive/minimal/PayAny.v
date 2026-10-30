(* PayAny.v: a PAY move added to any Thiele-complete machine.

   Bolt PAY onto ANY Thiele-complete machine.  The new machine has states
   (s, k) with k a pay counter, moves Some m (the old move) and None (PAY);
   PAY adds 1 to k and does nothing else; the record is the old record.
   For EVERY non-base kind chosen for PAY -- a CHECK, a COMMIT or a CERTIFY,
   of the empty claim None or of any real claim Some c -- the new machine is
   Thiele-complete (ThieleComplete.v's definition, unchanged).  And with a
   PAY before every base move, its ledger counts the base steps of any
   two-counter program exactly.                                            *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.ThieleComplete.
Module T := Minimal.ThieleComplete.

Section Pay.

Variable M : T.machine.
Variable I : T.thiele_interface M.
Hypothesis HI : T.thiele_complete_with I.

Notation S0 := (T.m_state M).
Notation Mv := (T.m_move M).
Notation C := (T.ti_claim I).

Definition pstep (x : S0 * nat) (m : option Mv) : S0 * nat :=
  match m with Some m0 => (T.m_step M (fst x) m0, snd x) | None => (fst x, S (snd x)) end.
Definition pcost (m : option Mv) : nat :=
  match m with Some m0 => T.m_cost M m0 | None => 1 end.
Definition precord (x : S0 * nat) : bool := T.m_record M (fst x).

Definition pmachine : T.machine := T.mk_machine (S0 * nat) (option Mv) pstep pcost precord.

Fixpoint erase (tr : list (option Mv)) : list Mv :=
  match tr with [] => [] | Some m :: r => m :: erase r | None :: r => erase r end.

Lemma erase_app : forall a b, erase (a ++ b) = erase a ++ erase b.
Proof. induction a as [| [m |] a IH]; intros b; simpl; rewrite ?IH; reflexivity. Qed.

Lemma erase_mid : forall a x b, erase (a ++ Some x :: b) = erase a ++ x :: erase b.
Proof. intros. rewrite erase_app. reflexivity. Qed.

Lemma prun_fst : forall tr x, fst (T.run pmachine tr x) = T.run M (erase tr) (fst x).
Proof. induction tr as [| [m |] tr IH]; intros [s k]; simpl; rewrite ?IH; reflexivity. Qed.

Lemma erase_split : forall tr A x B, erase tr = A ++ x :: B ->
  exists A' B', tr = A' ++ Some x :: B' /\ erase A' = A /\ erase B' = B.
Proof.
  induction tr as [| [m |] tr IH]; intros A x B H; simpl in H.
  - destruct A; discriminate.
  - destruct A as [| a A].
    + injection H as Hx HB. subst x B. exists [], tr. auto.
    + injection H as Ha H. subst m. destruct (IH A x B H) as [A' [B' [-> [HA HB]]]].
      exists (Some a :: A'), B'. simpl. rewrite HA. auto.
  - destruct (IH A x B H) as [A' [B' [-> [HA HB]]]].
    exists (None :: A'), B'. simpl. auto.
Qed.

Definition map_kind (k : T.kind C) : T.kind (option C) :=
  match k with
  | T.KBase => T.KBase | T.KCheck c => T.KCheck (Some c)
  | T.KCommit c => T.KCommit (Some c) | T.KCertify => T.KCertify
  end.

(* PAY's filing: any non-base kind at all. *)
Variable pay_kind : T.kind (option C).
Hypothesis pay_not_base : pay_kind <> T.KBase.

Definition pbase : T.universal_base pmachine.
Proof.
  refine (T.mk_ub pmachine (fun x => T.ub_window (T.ti_base I) (fst x))
            (fun x => T.ub_live (T.ti_base I) (fst x))
            (fun i => Some (T.ub_compile (T.ti_base I) i))
            (fun a b => (T.ub_load (T.ti_base I) a b, 0)) _ _ _).
  - intros a b. apply T.ub_load_window.
  - intros a b. apply T.ub_load_live.
  - intros [s k] i Hl. simpl in *. exact (T.ub_sim (T.ti_base I) s i Hl).
Defined.

Definition pinterface : T.thiele_interface pmachine :=
  T.mk_ti pmachine pbase (option C)
    (fun m => match m with Some m0 => map_kind (T.ti_kind I m0) | None => pay_kind end)
    (fun oc x => match oc with Some c => T.ti_meaning I c (fst x) | None => False end)
    (fun x oc => match oc with Some c => T.ti_check I (fst x) c | None => false end)
    (fun oc x y => match oc with Some c => T.ti_same I c (fst x) (fst y) | None => True end)
    (fun x => T.ti_clean I (fst x))
    (fun x => T.ti_ledger I (fst x) + snd x).

Theorem pay_thiele_complete_with : T.thiele_complete_with pinterface.
Proof.
  destruct HI as [[Ha1 [Ha2 [Ha3 Ha4]]] [[Hb1 [Hb2 [Hb3 Hb4]]] [[Hc1 Hc2] Hd]]].
  split; [| split; [| split]].
  - (* (a) *)
    split; [intro i; simpl; rewrite Ha1; reflexivity |].
    split; [intros a b; simpl; apply Ha2 |].
    split.
    + intros [s k] [m |] Hk; simpl in *.
      * apply Ha3. destruct (T.ti_kind I m); simpl in Hk; congruence.
      * reflexivity.
    + intros [s k] [m |] H; simpl in *; [apply Ha4, H | exact H].
  - (* (b) *)
    split; [intros [s k] H; apply Hb1, H |].
    split.
    + intros [s0 k0] tr H0 H1. unfold precord in H1. simpl in H0, H1.
      change (T.m_record M (fst (T.run pmachine tr (s0, k0))) = true) in H1.
      rewrite prun_fst in H1. simpl in H1.
      destruct (Hb2 s0 (erase tr) H0 H1)
        as [pre [c [chk [mid1 [cmt [mid2 [crt [post
             [Htr [Hk1 [Hk2 [Hk3 [Hck [Hsame [Hdn Hup]]]]]]]]]]]]]]].
      destruct (erase_split tr pre chk _ Htr) as [pre' [R1 [-> [Hpre HR1]]]].
      destruct (erase_split R1 mid1 cmt _ HR1) as [mid1' [R2 [-> [Hmid1 HR2]]]].
      destruct (erase_split R2 mid2 crt _ HR2) as [mid2' [post' [-> [Hmid2 Hpost]]]].
      exists pre', (Some c), (Some chk), mid1', (Some cmt), mid2', (Some crt), post'.
      split; [reflexivity |].
      split; [simpl; rewrite Hk1; reflexivity |].
      split; [simpl; rewrite Hk2; reflexivity |].
      split; [simpl; rewrite Hk3; reflexivity |].
      split.
      { change (T.ti_check I (fst (T.run pmachine pre' (s0, k0))) c = true).
        rewrite prun_fst, Hpre. exact Hck. }
      split.
      { intros t1 t2 Hm.
        change (T.ti_same I c (fst (T.run pmachine pre' (s0, k0)))
                  (fst (T.run pmachine (pre' ++ Some chk :: t1) (s0, k0)))).
        rewrite !prun_fst, erase_app. simpl.
        rewrite Hpre. apply (Hsame (erase t1) (erase t2)).
        rewrite <- Hmid1, Hm, erase_app. reflexivity. }
      split.
      { change (T.m_record M (fst (T.run pmachine
                  (pre' ++ Some chk :: mid1' ++ Some cmt :: mid2') (s0, k0))) = false).
        rewrite prun_fst. simpl fst. rewrite !erase_mid. simpl erase.
        rewrite Hpre, Hmid1, Hmid2. exact Hdn. }
      { change (T.m_record M (fst (T.run pmachine
                  (pre' ++ Some chk :: mid1' ++ Some cmt :: mid2' ++ [Some crt]) (s0, k0))) = true).
        rewrite prun_fst. simpl fst. rewrite !erase_mid. simpl erase.
        rewrite Hpre, Hmid1, Hmid2. exact Hup. }
    + split.
      * intros [s k] [c |] H; simpl in *; [apply Hb3, H | discriminate].
      * intros [c |] [s k] [s' k'] Hs Hm; simpl in *; [apply (Hb4 c s s' Hs Hm) | exact Hm].
  - (* (c) *)
    split.
    + intros [m |]; simpl; unfold T.record_move; simpl.
      * rewrite Hc1. unfold T.record_move. destruct (T.ti_kind I m); reflexivity.
      * destruct pay_kind; [congruence | reflexivity | reflexivity | reflexivity].
    + intros [s k] [m |]; simpl; [rewrite Hc2; lia | lia].
  - (* (d) *)
    destruct Hd as [c [chk [cmt [crt [Hk1 [Hk2 [Hk3 [Hiff [Hyes Hno]]]]]]]]].
    exists (Some c), (Some chk), (Some cmt), (Some crt).
    split; [simpl; rewrite Hk1; reflexivity |].
    split; [simpl; rewrite Hk2; reflexivity |].
    split; [simpl; rewrite Hk3; reflexivity |].
    split; [| split; [exact Hyes | exact Hno]].
    intros a b. unfold T.load. simpl. exact (Hiff a b).
Qed.

(* PAY never passes as a check of the empty claim, its meaning never holds,
   and it changes nothing but the pay counter. *)
Lemma pay_inert : forall x,
  T.ti_check pinterface x None = false /\ ~ T.ti_meaning pinterface None x /\
  pstep x None = (fst x, S (snd x)).
Proof. intros [s k]. simpl. auto. Qed.

(* The clock: a PAY before every base move. *)
Fixpoint cm_exact (n : nat) (P : list T.cm_instr) (x : T.cm_conf) : option T.cm_conf :=
  match n with
  | 0 => Some x
  | S k => match T.cm_step P x with None => None | Some y => cm_exact k P y end
  end.

Fixpoint pay_prog_run (n : nat) (P : list T.cm_instr) (x : S0 * nat) : S0 * nat :=
  match n with
  | 0 => x
  | S k => match T.cm_fetch P (fst (T.ub_window (T.ti_base I) (fst x))) with
           | None => x
           | Some i => pay_prog_run k P
                         (pstep (pstep x None) (Some (T.ub_compile (T.ti_base I) i)))
           end
  end.

Theorem pay_clock : forall n P x y,
  T.ub_live (T.ti_base I) (fst x) ->
  cm_exact n P (T.ub_window (T.ti_base I) (fst x)) = Some y ->
  T.ub_window (T.ti_base I) (fst (pay_prog_run n P x)) = y /\
  T.ub_live (T.ti_base I) (fst (pay_prog_run n P x)) /\
  T.ti_ledger pinterface (pay_prog_run n P x) = T.ti_ledger pinterface x + n /\
  T.m_record pmachine (pay_prog_run n P x) = T.m_record pmachine x.
Proof.
  destruct HI as [[Ha1 [_ [Ha3 _]]] [_ [[Hc1 Hc2] _]]].
  induction n as [| n IH]; intros P [s k] y Hl He; simpl in *.
  - injection He as <-. repeat split; auto; lia.
  - unfold T.cm_step in He.
    destruct (T.cm_fetch P (fst (T.ub_window (T.ti_base I) s))) as [i |] eqn:Hf;
      [| discriminate].
    destruct (T.ub_sim (T.ti_base I) s i Hl) as [Hw Hl'].
    rewrite <- Hw in He.
    destruct (IH P (T.m_step M s (T.ub_compile (T.ti_base I) i), S k) y Hl' He)
      as [H1 [H2 [H3 H4]]].
    simpl in H3, H4.
    assert (Hcost : T.m_cost M (T.ub_compile (T.ti_base I) i) = 0).
    { rewrite Hc1. unfold T.record_move. rewrite Ha1. reflexivity. }
    repeat split; auto.
    + rewrite H3, Hc2, Hcost. lia.
    + rewrite H4. unfold precord. simpl. apply Ha3. apply Ha1.
Qed.

End Pay.

Theorem pay_thiele_complete : forall M, T.thiele_complete M -> T.thiele_complete (pmachine M).
Proof.
  intros M [I HI]. exists (pinterface M I (T.KCheck None)).
  apply pay_thiele_complete_with; [exact HI | discriminate].
Qed.

(* Any non-base filing works, including a CHECK or COMMIT of a REAL claim. *)
Theorem pay_any_filing : forall M (I : T.thiele_interface M)
  (pk : T.kind (option (T.ti_claim I))),
  T.thiele_complete_with I -> pk <> T.KBase -> T.thiele_complete_with (pinterface M I pk).
Proof. intros. apply pay_thiele_complete_with; assumption. Qed.

(* PAY filed as a CHECK, a COMMIT or a CERTIFY of the empty claim. *)
Corollary pay_as_check_commit_or_certify : forall M (I : T.thiele_interface M),
  T.thiele_complete_with I ->
  T.thiele_complete_with (pinterface M I (T.KCheck None)) /\
  T.thiele_complete_with (pinterface M I (T.KCommit None)) /\
  T.thiele_complete_with (pinterface M I T.KCertify).
Proof.
  intros M I HI. split; [| split]; apply pay_thiele_complete_with; auto; discriminate.
Qed.

Print Assumptions pay_thiele_complete.
Print Assumptions pay_any_filing.
Print Assumptions pay_as_check_commit_or_certify.
Print Assumptions pay_clock.
Print Assumptions pay_inert.
