(** NecWLRice: recursion, Rice and halting for L, pushed to their limits.

    - The recursion theorem needs a closed term, not a closed value: for
      every closed term s there is a closed t that reaches s applied to the
      code of t. Closedness is needed: a closed term only reaches closed
      terms, so no closed t reaches (var 0) applied to anything.
    - Rice's theorem needs extensionality and both witnesses: a constant
      property is decided by a closed term, and the syntactic property "is
      an abstraction" has closed witnesses and a closed decider.
    - Rice's theorem does not need the witnesses to be closed: for every
      extensional property with any witness and any counterexample, no
      closed term decides it. The proof reduces halting to the property. *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the call-by-value lambda calculus L (closed terms
   and their codes), not on a Thiele machine. The recursion and Rice theorems
   on the host machine are the Sm files, linked to the abstract record in
   UniversalInterpreterLinks.v. *)

From Coq Require Import Arith.PeanoNat Lia.
From Kernel Require Import LRecursion.

(* ================================================================= *)
(** * 1. The recursion theorem                                        *)
(* ================================================================= *)

Theorem nec_w_second_recursion_any_closed :
  forall s, closed s -> exists t, closed t /\ star t (app s (enc t)).
Proof.
  intros s Hs.
  set (s' := lam (app s (var 0))).
  assert (Hs' : closed s').
  { unfold s', closed. simpl. split; [eapply bound_mono; [| exact Hs]; lia | lia]. }
  destruct (second_recursion s' Hs' (ex_intro _ _ eq_refl)) as [t [Ht Hstar]].
  exists t. split; [exact Ht |].
  eapply star_trans; [exact Hstar |]. apply star_one.
  replace (app s (enc t)) with (subst (app s (var 0)) 0 (enc t)).
  - apply stepBeta. apply enc_value.
  - simpl. rewrite (subst_closed s) by exact Hs. reflexivity.
Qed.

(** The recursion corollary without the value requirement. *)
Corollary nec_w_recursion_theorem_any_closed :
  forall f : term -> term,
    (exists s, closed s /\ forall p, equiv (app s (enc p)) (f p)) ->
    exists p, equiv p (f p).
Proof.
  intros f [s [Hs Hf]].
  destruct (nec_w_second_recursion_any_closed s Hs) as [t [_ Ht]].
  exists t. eapply equiv_trans; [apply star_equiv; exact Ht | apply Hf].
Qed.

Lemma nec_w_step_closed : forall s t, step s t -> closed s -> closed t.
Proof.
  intros s t H. induction H as [b v Hv | s s' t' H IH | v t t' Hv H IH]; unfold closed in *; simpl.
  - intros [Hb Hvc]. apply bound_subst; assumption.
  - intros [H1 H2]. split; [apply IH; exact H1 | exact H2].
  - intros [H1 H2]. split; [exact H1 | apply IH; exact H2].
Qed.

Lemma nec_w_star_closed : forall s t, star s t -> closed s -> closed t.
Proof.
  intros s t H. induction H as [s | s t u H _ IH]; intros Hs; [exact Hs |].
  apply IH. exact (nec_w_step_closed s t H Hs).
Qed.

(** Closedness is needed: no closed term reaches [var 0] applied to its
    own code. *)
Theorem nec_w_second_recursion_needs_closed :
  ~ exists t, closed t /\ star t (app (var 0) (enc t)).
Proof.
  intros [t [Ht Hstar]].
  pose proof (nec_w_star_closed _ _ Hstar Ht) as H.
  unfold closed in H. simpl in H. lia.
Qed.

(* ================================================================= *)
(** * 2. Rice: both witnesses and extensionality are needed           *)
(* ================================================================= *)

Lemma nec_w_const_decider : forall c p,
  closed c -> star (app (lam c) (enc p)) c.
Proof.
  intros c p Hc. apply star_one.
  replace c with (subst c 0 (enc p)) at 2 by (apply subst_closed; exact Hc).
  apply stepBeta. apply enc_value.
Qed.

Lemma nec_w_ltrue_closed : closed ltrue.
Proof. cbv. lia. Qed.

Lemma nec_w_lfalse_closed : closed lfalse.
Proof. cbv. lia. Qed.

(** A property true of every program is extensional and decided by a
    closed term; so is a property false of every program. *)
Theorem nec_w_rice_needs_both_witnesses :
  (extensional (fun _ => True) /\ closed (lam ltrue) /\ L_decides (lam ltrue) (fun _ => True)) /\
  (extensional (fun _ => False) /\ closed (lam lfalse) /\ L_decides (lam lfalse) (fun _ => False)).
Proof.
  split; split; [intros p q _ _; exact I | | intros p q _ H; exact H |].
  - split; [cbv; lia |]. intros p. split.
    + intros _. apply nec_w_const_decider. exact nec_w_ltrue_closed.
    + intros H. contradiction H. exact I.
  - split; [cbv; lia |]. intros p. split.
    + intros H. contradiction.
    + intros _. apply nec_w_const_decider. exact nec_w_lfalse_closed.
Qed.

(** The Scott code of a term picks one of three continuations. *)
Lemma nec_w_enc_case : forall p v1 v2 v3,
  closed v1 -> closed v2 -> closed v3 -> value v1 -> value v2 -> value v3 ->
  star (app (app (app (enc p) v1) v2) v3)
    (match p with
     | var n => app v1 (encn n)
     | app s t => app (app v2 (enc s)) (enc t)
     | lam s => app v3 (enc s)
     end).
Proof.
  intros p v1 v2 v3 H1 H2 H3 Hv1 Hv2 Hv3.
  destruct p as [n | s t | s]; simpl.
  - eapply star_step; [apply stepL; apply stepL; apply stepBeta; exact Hv1 |]. simpl.
    rewrite (subst_closed (encn n)) by apply encn_closed.
    eapply star_step; [apply stepL; apply stepBeta; exact Hv2 |]. simpl.
    rewrite (subst_closed v1) by exact H1. rewrite (subst_closed (encn n)) by apply encn_closed.
    eapply star_step; [apply stepBeta; exact Hv3 |]. simpl.
    rewrite (subst_closed v1) by exact H1. rewrite (subst_closed (encn n)) by apply encn_closed.
    apply star_refl.
  - eapply star_step; [apply stepL; apply stepL; apply stepBeta; exact Hv1 |]. simpl.
    rewrite (subst_closed (enc s)), (subst_closed (enc t)) by apply enc_closed.
    eapply star_step; [apply stepL; apply stepBeta; exact Hv2 |]. simpl.
    rewrite (subst_closed (enc s)), (subst_closed (enc t)) by apply enc_closed.
    eapply star_step; [apply stepBeta; exact Hv3 |]. simpl.
    rewrite (subst_closed v2) by exact H2.
    rewrite (subst_closed (enc s)), (subst_closed (enc t)) by apply enc_closed.
    apply star_refl.
  - eapply star_step; [apply stepL; apply stepL; apply stepBeta; exact Hv1 |]. simpl.
    rewrite (subst_closed (enc s)) by apply enc_closed.
    eapply star_step; [apply stepL; apply stepBeta; exact Hv2 |]. simpl.
    rewrite (subst_closed (enc s)) by apply enc_closed.
    eapply star_step; [apply stepBeta; exact Hv3 |]. simpl.
    rewrite (subst_closed (enc s)) by apply enc_closed.
    apply star_refl.
Qed.

(** "The program is an abstraction". *)
Definition nec_w_is_lam (p : term) : Prop := exists b, p = lam b.

Definition nec_w_is_lam_decider : term :=
  lam (app (app (app (var 0) (lam lfalse)) (lam (lam lfalse))) (lam ltrue)).

Lemma nec_w_is_lam_decider_run : forall p,
  star (app nec_w_is_lam_decider (enc p))
    (match p with
     | var n => app (lam lfalse) (encn n)
     | app s t => app (app (lam (lam lfalse)) (enc s)) (enc t)
     | lam s => app (lam ltrue) (enc s)
     end).
Proof.
  intros p. eapply star_step; [apply stepBeta; apply enc_value |].
  change (subst (app (app (app (var 0) (lam lfalse)) (lam (lam lfalse))) (lam ltrue)) 0 (enc p))
    with (app (app (app (enc p) (lam lfalse)) (lam (lam lfalse))) (lam ltrue)).
  apply nec_w_enc_case; try (cbv; lia); eexists; reflexivity.
Qed.

(** Extensionality is needed: "is an abstraction" has closed witnesses, a
    closed decider, and is not extensional. *)
Theorem nec_w_rice_needs_extensional :
  nec_w_is_lam lid /\ ~ nec_w_is_lam (app lid lid) /\
  closed lid /\ closed (app lid lid) /\
  closed nec_w_is_lam_decider /\ L_decides nec_w_is_lam_decider nec_w_is_lam /\
  ~ extensional nec_w_is_lam.
Proof.
  split; [eexists; reflexivity |].
  split; [intros [b H]; discriminate |].
  split; [cbv; lia |]. split; [cbv; lia |]. split; [cbv; repeat split; lia |].
  split.
  - intros p. pose proof (nec_w_is_lam_decider_run p) as Hrun. split.
    + intros [b ->]. eapply star_trans; [exact Hrun |].
      apply nec_w_const_decider. exact nec_w_ltrue_closed.
    + intros Hn. destruct p as [n | s t | s].
      * eapply star_trans; [exact Hrun |]. apply star_one.
        replace lfalse with (subst lfalse 0 (encn n)) at 2 by reflexivity.
        apply stepBeta. apply encn_value.
      * eapply star_trans; [exact Hrun |].
        eapply star_step; [apply stepL; apply stepBeta; apply enc_value |]. simpl.
        apply star_one.
        replace lfalse with (subst lfalse 0 (enc t)) at 2 by reflexivity.
        apply stepBeta. apply enc_value.
      * exfalso. apply Hn. eexists; reflexivity.
  - intros Hext. assert (Heq : equiv lid (app lid lid)).
    { apply equiv_sym. apply star_equiv. apply star_one.
      replace lid with (subst (var 0) 0 lid) at 2 by reflexivity.
      apply stepBeta. eexists; reflexivity. }
    destruct (Hext lid (app lid lid) Heq (ex_intro _ _ eq_refl)) as [b H]. discriminate.
Qed.

(* ================================================================= *)
(** * 3. Rice for any witnesses                                       *)
(* ================================================================= *)

Lemma nec_w_app_halts_inv : forall s w, star s w -> value w ->
  forall a b, s = app a b -> halts a /\ halts b.
Proof.
  intros s w H. induction H as [s | s t u Hst Htu IH]; intros Hw a b E.
  - subst. destruct Hw as [b' Hb']. discriminate.
  - subst. inversion Hst; subst.
    + split; [exists (lam b0); split; [apply star_refl | eexists; reflexivity] |].
      exists b. split; [apply star_refl | assumption].
    + destruct (IH Hw s' b eq_refl) as [[v [Hv Hvv]] Hb].
      split; [exists v; split; [eapply star_step; eassumption | exact Hvv] | exact Hb].
    + destruct (IH Hw a t' eq_refl) as [Ha [v [Hv Hvv]]].
      split; [exact Ha | exists v; split; [eapply star_step; eassumption | exact Hvv]].
Qed.

Definition nec_w_K : term := lam (lam (var 0)).

(** [nec_w_px X v] evaluates to [v] when [X] halts and has no value when
    [X] does not. *)
Definition nec_w_px (X v : term) : term := app (app nec_w_K X) v.

Lemma nec_w_px_halts : forall X v, halts X -> value v -> star (nec_w_px X v) v.
Proof.
  intros X v [x [HX Hx]] Hv. unfold nec_w_px.
  eapply star_trans.
  { apply star_appL. eapply star_trans; [apply star_appR; [eexists; reflexivity | exact HX] |].
    apply star_one. apply stepBeta. exact Hx. }
  simpl. apply star_one.
  replace v with (subst (var 0) 0 v) at 2 by reflexivity.
  apply stepBeta. exact Hv.
Qed.

Lemma nec_w_px_value_halts : forall X v w, eval (nec_w_px X v) w -> halts X.
Proof.
  intros X v w [Hs Hw].
  destruct (nec_w_app_halts_inv _ _ Hs Hw (app nec_w_K X) v eq_refl) as [[u [Hu Huv]] _].
  destruct (nec_w_app_halts_inv _ _ Hu Huv nec_w_K X eq_refl) as [_ HX]. exact HX.
Qed.

Lemma nec_w_no_value_equiv_omega : forall p, (forall v, ~ eval p v) -> equiv p Omega.
Proof.
  intros p H v. split; intros Hv; [exfalso; exact (H v Hv) | exfalso; exact (Omega_diverges v Hv)].
Qed.

(** The halting decider built from a decider [D] of the property and the
    code [c] of a value. *)
Definition nec_w_hbody (D c : term) : term :=
  app (lam (app D (var 0))) (app (app mk_app (app (app mk_app (enc nec_w_K)) (var 0))) c).

Lemma nec_w_mk_app_closed : closed mk_app.
Proof. cbv. repeat split; lia. Qed.

Lemma nec_w_hbody_bound : forall D c, closed D -> closed c -> bound 1 (nec_w_hbody D c).
Proof.
  intros D c HD Hc. unfold nec_w_hbody. simpl.
  repeat split; try lia;
    (eapply bound_mono; [| first [exact HD | exact Hc | exact nec_w_mk_app_closed | apply enc_closed]]; lia).
Qed.

Lemma nec_w_hbody_subst : forall D c e, closed D -> closed c ->
  subst (nec_w_hbody D c) 0 e =
  app (lam (app D (var 0))) (app (app mk_app (app (app mk_app (enc nec_w_K)) e)) c).
Proof.
  intros D c e HD Hc. unfold nec_w_hbody. cbn [subst Nat.eqb].
  rewrite (subst_closed D) by exact HD. rewrite (subst_closed c) by exact Hc.
  rewrite (subst_closed mk_app) by exact nec_w_mk_app_closed.
  rewrite (subst_closed (enc nec_w_K)) by apply enc_closed. reflexivity.
Qed.

Lemma nec_w_hbody_run : forall D v p, closed D ->
  star (subst (nec_w_hbody D (enc v)) 0 (enc p)) (app D (enc (nec_w_px p v))).
Proof.
  intros D v p HD. rewrite nec_w_hbody_subst by (exact HD || apply enc_closed).
  eapply star_trans.
  { apply star_appR; [eexists; reflexivity |].
    apply (mk_app_eval _ _ (enc (app nec_w_K p)) (enc v)).
    - apply mk_app_enc.
    - apply enc_value.
    - apply enc_closed.
    - apply star_refl.
    - apply enc_value. }
  apply star_one.
  replace (app D (enc (nec_w_px p v))) with
    (subst (app D (var 0)) 0 (enc (nec_w_px p v))).
  - apply stepBeta. apply enc_value.
  - simpl. rewrite (subst_closed D) by exact HD. reflexivity.
Qed.

Lemma nec_w_ltrue_select : forall a b, closed a -> value a -> value b -> star (app (app ltrue a) b) a.
Proof.
  intros a b Ha Hva Hb. eapply star_step.
  - apply stepL. apply stepBeta. exact Hva.
  - simpl. apply star_one.
    replace a with (subst a 0 b) at 2 by (apply subst_closed; exact Ha).
    apply stepBeta. exact Hb.
Qed.

Lemma nec_w_lfalse_select : forall a b, value a -> value b -> star (app (app lfalse a) b) b.
Proof.
  intros a b Ha Hb. eapply star_step.
  - apply stepL. apply stepBeta. exact Ha.
  - simpl. apply star_one.
    replace b with (subst (var 0) 0 b) at 2 by reflexivity.
    apply stepBeta. exact Hb.
Qed.

(** Rice's theorem for L with any witness and any counterexample, closed or
    not. *)
Theorem nec_w_rice_any_witnesses :
  forall P yes no,
    extensional P -> P yes -> ~ P no ->
    ~ exists D, closed D /\ L_decides D P.
Proof.
  intros P yes no Hext Hy Hn [D [HD Hdec]].
  assert (Hlem : ~ ~ (P Omega \/ ~ P Omega)) by tauto.
  apply Hlem. intros [HO | HO].
  - (* P holds of the diverging program: use the counterexample. *)
    assert (Hlem2 : ~ ~ (halts no \/ ~ halts no)) by tauto.
    apply Hlem2. intros [[vn [Hno Hvn]] | Hnh].
    2: { apply Hn. apply (Hext Omega no); [| exact HO].
         apply equiv_sym. apply nec_w_no_value_equiv_omega.
         intros v Hv. apply Hnh. exists v. exact Hv. }
    assert (HPvn : ~ P vn).
    { intros H. apply Hn. apply (Hext vn no); [| exact H].
      apply equiv_sym. apply star_equiv. exact Hno. }
    apply L_halting_undecidable.
    exists (lam (app (app (nec_w_hbody D (enc vn)) lfalse) ltrue)). split.
    + change (bound 1 (app (app (nec_w_hbody D (enc vn)) lfalse) ltrue)). split; [split |].
      * apply nec_w_hbody_bound; [exact HD | apply enc_closed].
      * eapply bound_mono; [| exact nec_w_lfalse_closed]; lia.
      * eapply bound_mono; [| exact nec_w_ltrue_closed]; lia.
    + intros p.
      assert (Hrun : star (app (lam (app (app (nec_w_hbody D (enc vn)) lfalse) ltrue)) (enc p))
                          (app (app (app D (enc (nec_w_px p vn))) lfalse) ltrue)).
      { eapply star_step; [apply stepBeta; apply enc_value |].
        cbn [subst]. change (subst lfalse 0 (enc p)) with lfalse.
        change (subst ltrue 0 (enc p)) with ltrue.
        do 2 apply star_appL. apply nec_w_hbody_run. exact HD. }
      split.
      * intros Hh. eapply star_trans; [exact Hrun |].
        assert (HnP : ~ P (nec_w_px p vn)).
        { intros H. apply HPvn. apply (Hext (nec_w_px p vn) vn); [| exact H].
          apply star_equiv. apply nec_w_px_halts; assumption. }
        destruct (Hdec (nec_w_px p vn)) as [_ HF].
        eapply star_trans; [do 2 apply star_appL; exact (HF HnP) |].
        apply nec_w_lfalse_select; eexists; reflexivity.
      * intros Hnh. eapply star_trans; [exact Hrun |].
        assert (HP : P (nec_w_px p vn)).
        { apply (Hext Omega); [| exact HO]. apply equiv_sym.
          apply nec_w_no_value_equiv_omega. intros w Hw.
          exact (Hnh (nec_w_px_value_halts p vn w Hw)). }
        destruct (Hdec (nec_w_px p vn)) as [HT _].
        eapply star_trans; [do 2 apply star_appL; exact (HT HP) |].
        apply nec_w_ltrue_select; [exact nec_w_lfalse_closed | eexists; reflexivity | eexists; reflexivity].
  - (* P fails at the diverging program: use the witness. *)
    assert (Hlem2 : ~ ~ (halts yes \/ ~ halts yes)) by tauto.
    apply Hlem2. intros [[vy [Hyes Hvy]] | Hnh].
    2: { apply HO. apply (Hext yes Omega); [| exact Hy].
         apply nec_w_no_value_equiv_omega.
         intros v Hv. apply Hnh. exists v. exact Hv. }
    assert (HPvy : P vy).
    { apply (Hext yes vy); [| exact Hy]. apply star_equiv. exact Hyes. }
    apply L_halting_undecidable.
    exists (lam (nec_w_hbody D (enc vy))). split.
    + change (bound 1 (nec_w_hbody D (enc vy))). apply nec_w_hbody_bound; [exact HD | apply enc_closed].
    + intros p.
      assert (Hrun : star (app (lam (nec_w_hbody D (enc vy))) (enc p))
                          (app D (enc (nec_w_px p vy)))).
      { eapply star_step; [apply stepBeta; apply enc_value |].
        apply nec_w_hbody_run. exact HD. }
      split.
      * intros Hh. eapply star_trans; [exact Hrun |].
        assert (HP : P (nec_w_px p vy)).
        { apply (Hext vy); [| exact HPvy].
          apply equiv_sym. apply star_equiv. apply nec_w_px_halts; assumption. }
        exact (proj1 (Hdec (nec_w_px p vy)) HP).
      * intros Hnh. eapply star_trans; [exact Hrun |].
        assert (HnP : ~ P (nec_w_px p vy)).
        { intros H. apply HO. apply (Hext (nec_w_px p vy)); [| exact H].
          apply nec_w_no_value_equiv_omega. intros w Hw.
          exact (Hnh (nec_w_px_value_halts p vy w Hw)). }
        exact (proj2 (Hdec (nec_w_px p vy)) HnP).
Qed.

(** The repository's Rice theorem is a corollary. *)
Corollary nec_w_L_rice_corollary :
  forall P yes no,
    extensional P -> P yes -> ~ P no -> closed yes -> closed no ->
    ~ exists D, closed D /\ L_decides D P.
Proof. intros P yes no Hext Hy Hn _ _. exact (nec_w_rice_any_witnesses P yes no Hext Hy Hn). Qed.

Print Assumptions nec_w_second_recursion_any_closed.
Print Assumptions nec_w_recursion_theorem_any_closed.
Print Assumptions nec_w_second_recursion_needs_closed.
Print Assumptions nec_w_rice_needs_both_witnesses.
Print Assumptions nec_w_rice_needs_extensional.
Print Assumptions nec_w_rice_any_witnesses.
Print Assumptions nec_w_L_rice_corollary.
