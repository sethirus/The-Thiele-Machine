(** NecWWindow: windows pushed to their limits.

    The book's window results (decoders need constant fibres; no exact
    window price across a collision; three conditional escapes), with every
    hypothesis tested.

    - Fibres. Constancy on fibres alone does not give a decoder: an empty
      state type with one view is a counterexample. A partial section (a
      state for some views, a safe answer for the rest) is enough, and
      exactly enough. With only a surjective window, the converse is
      equivalent to the unique choice principle, so it is neither provable
      nor refutable in Coq's core logic.
    - Window prices. An exact window price exists exactly when the flip is
      a function of the observed transition; on a finite system that is
      exactly "no collision". The reading being a function of the view is
      sufficient but not necessary. On a finite system there is a least
      floor-meeting window price; it overcharges by exactly one on exactly
      the non-raising steps whose observed transition some raise shares,
      and every floor-meeting window price overcharges at least that much
      along every run.
    - Escapes. The commitment verifier is sound and complete exactly when
      the contract holds; the response verifier exactly when the response
      test is exact; the unchecked relation breaks the contract as soon as
      it explains anything at all. *)

From Coq Require Import List Bool Arith Lia.
Import ListNotations.
From Kernel Require Import ObservationPolicy ShadowPricing.
Require Import Minimal.VerifierSmall.
Require Minimal.ThieleComplete.

(* ================================================================= *)
(** * 1. Decoders and fibres                                          *)
(* ================================================================= *)

(** Constancy on fibres is not enough on its own: an empty state type, one
    view, and an empty answer type. *)
Theorem nec_w_fibre_converse_fails_without_section :
  ~ (forall (State View Answer : Type) (observe : State -> View)
            (query : State -> Answer),
       query_fiber_constant observe query ->
       exists decode : View -> Answer, forall s, decode (observe s) = query s).
Proof.
  intro H.
  destruct (H Empty_set unit Empty_set (fun e => match e with end) (fun e => e))
    as [d _].
  - intros s. destruct s.
  - destruct (d tt).
Qed.

(** The exact constructive content: a decoder exists exactly when the
    question is constant on fibres and every view can be handed either a
    state that shows it or an answer that is right for all its states. *)
Theorem nec_w_decoder_iff_fibre_and_partial_section
    {State View Answer : Type} (observe : State -> View) (query : State -> Answer) :
  (exists decode : View -> Answer, forall s, decode (observe s) = query s) <->
  (query_fiber_constant observe query /\
   exists pick : View -> State + Answer,
     (forall v s, pick v = inl s -> observe s = v) /\
     (forall v a, pick v = inr a -> forall s, observe s = v -> query s = a)).
Proof.
  split.
  - intros Hd. split; [apply decoding_requires_fiber_constancy; exact Hd |].
    destruct Hd as [decode Hdec].
    exists (fun v => inr (decode v)). split.
    + intros v s H. discriminate.
    + intros v a H s Hs. injection H as <-. subst v. symmetry. apply Hdec.
  - intros [Hfib [pick [Hl Hr]]].
    exists (fun v => match pick v with inl t => query t | inr a => a end).
    intros s. destruct (pick (observe s)) as [t | a] eqn:E.
    + apply Hfib. exact (Hl _ _ E).
    + symmetry. exact (Hr _ _ E s eq_refl).
Qed.

(** The hypothesis form: with a partial section on the image, constancy on
    fibres is equivalent to a decoder. *)
Theorem nec_w_fibre_iff_partial_section
    {State View Answer : Type} (observe : State -> View) (query : State -> Answer)
    (pick : View -> State + Answer)
    (pick_sound : forall v s, pick v = inl s -> observe s = v)
    (pick_image : forall s, exists t, pick (observe s) = inl t) :
  query_fiber_constant observe query <->
  exists decode : View -> Answer, forall s, decode (observe s) = query s.
Proof.
  split; [| apply decoding_requires_fiber_constancy].
  intro Hfib.
  exists (fun v => match pick v with inl t => query t | inr a => a end).
  intros s. destruct (pick_image s) as [t E]. rewrite E.
  apply Hfib. exact (pick_sound _ _ E).
Qed.

(** The repository's section form is the special case [pick = inl o r]. *)
Corollary nec_w_fibre_section_corollary
    {State View Answer : Type} (observe : State -> View) (query : State -> Answer)
    (representative : View -> State)
    (section_law : forall v, observe (representative v) = v) :
  query_fiber_constant observe query <->
  exists decode : View -> Answer, forall s, decode (observe s) = query s.
Proof.
  apply (nec_w_fibre_iff_partial_section observe query (fun v => inl (representative v))).
  - intros v s H. injection H as <-. apply section_law.
  - intros s. eexists. reflexivity.
Qed.

(** Unique choice: a total functional relation has a choice function. *)
Definition nec_w_unique_choice : Prop :=
  forall (A B : Type) (R : A -> B -> Prop),
    (forall a, exists! b, R a b) -> exists f : A -> B, forall a, R a (f a).

(** The converse of the fibre theorem for every surjective window. *)
Definition nec_w_surjective_fibre_converse : Prop :=
  forall (State View Answer : Type) (observe : State -> View)
         (query : State -> Answer),
    (forall v, exists s, observe s = v) ->
    query_fiber_constant observe query ->
    exists decode : View -> Answer, forall s, decode (observe s) = query s.

(** With only surjectivity, the converse is exactly unique choice, a
    principle Coq's core logic neither proves nor refutes. *)
Theorem nec_w_surjective_converse_iff_unique_choice :
  nec_w_surjective_fibre_converse <-> nec_w_unique_choice.
Proof.
  split.
  - intros Hconv A B R Huniq.
    set (St := {p : A * B | R (fst p) (snd p)}).
    destruct (Hconv St A B (fun x => fst (proj1_sig x)) (fun x => snd (proj1_sig x)))
      as [f Hf].
    + intros a. destruct (Huniq a) as [b [Hb _]].
      exists (exist _ (a, b) Hb). reflexivity.
    + intros [[a1 b1] H1] [[a2 b2] H2] E. simpl in *. subst a2.
      destruct (Huniq a1) as [b [_ Hu]].
      rewrite <- (Hu b1 H1), <- (Hu b2 H2). reflexivity.
    + exists f. intros a. destruct (Huniq a) as [b [Hb _]].
      pose proof (Hf (exist _ (a, b) Hb)) as E. simpl in E. rewrite E. exact Hb.
  - intros UC State View Answer observe query Hsurj Hfib.
    destruct (UC View Answer (fun v a => exists s, observe s = v /\ query s = a))
      as [f Hf].
    + intros v. destruct (Hsurj v) as [s Hs]. exists (query s). split.
      * exists s. split; [exact Hs | reflexivity].
      * intros a [s' [Hs' Ha]]. subst. apply Hfib. rewrite Hs'. reflexivity.
    + exists f. intros s. destruct (Hf (observe s)) as [s' [Hs' Ha]].
      rewrite <- Ha. apply Hfib. exact Hs'.
Qed.

(* ================================================================= *)
(** * 2. Window prices                                                *)
(* ================================================================= *)

Section Window.

Context {S I O : Type}.
Variable step : S -> I -> S.
Variable cert : S -> bool.
Variable obs : S -> O.

Definition nec_w_exact (price : O -> O -> nat) : Prop :=
  meets_floor step cert (shadow_cost step obs price) /\
  never_overcharges step cert (shadow_cost step obs price).

(** For every system: an exact window price exists exactly when the flip
    is a function of the observed transition. *)
Theorem nec_w_exact_iff_flip_factors :
  (exists price, nec_w_exact price) <->
  exists g : O -> O -> bool, forall s i, flips step cert s i = g (obs s) (obs (step s i)).
Proof.
  split.
  - intros [price [Hfl Hno]].
    exists (fun o o' => Nat.leb 1 (price o o')). intros s i.
    destruct (flips step cert s i) eqn:E.
    + symmetry. apply Nat.leb_le. exact (Hfl s i E).
    + symmetry. apply Nat.leb_gt. pose proof (Hno s i E) as H.
      unfold shadow_cost in H. lia.
  - intros [g Hg]. exists (fun o o' => if g o o' then 1 else 0). split.
    + intros s i H. unfold shadow_cost. rewrite <- Hg, H. lia.
    + intros s i H. unfold shadow_cost. rewrite <- Hg, H. reflexivity.
Qed.

(** A flip that factors through the observed transition rules out a
    collision; this holds for every system. *)
Theorem nec_w_factor_no_collision :
  (exists g : O -> O -> bool, forall s i, flips step cert s i = g (obs s) (obs (step s i))) ->
  ~ shadow_collision step cert obs.
Proof.
  intros [g Hg] [s1 [i1 [s2 [i2 [Hpre [Hpost [H1 H2]]]]]]].
  rewrite Hg in H1, H2. rewrite Hpre, Hpost in H1. congruence.
Qed.

(** For every system and every window price that meets the floor: each
    non-raising step whose observed transition is shared by a raise is
    charged at least one. *)
Theorem nec_w_shadowed_step_overcharged :
  forall price, meets_floor step cert (shadow_cost step obs price) ->
  forall s i s' i',
    obs s' = obs s -> obs (step s' i') = obs (step s i) ->
    flips step cert s' i' = true ->
    shadow_cost step obs price s i >= 1.
Proof.
  intros price Hfl s i s' i' E1 E2 Hf.
  unfold shadow_cost. rewrite <- E1, <- E2. exact (Hfl s' i' Hf).
Qed.

(** ** Finite systems *)

Variable Ss : list S.
Variable Is : list I.
Hypothesis Ss_complete : forall s, In s Ss.
Hypothesis Is_complete : forall i, In i Is.
Variable O_eq : forall a b : O, {a = b} + {a <> b}.

Definition nec_w_oeqb (a b : O) : bool := if O_eq a b then true else false.

Lemma nec_w_oeqb_spec : forall a b, nec_w_oeqb a b = true <-> a = b.
Proof.
  intros a b. unfold nec_w_oeqb. destruct (O_eq a b); split; congruence.
Qed.

(** Some raise shows the observed transition [(o, o')]. *)
Definition nec_w_flip_transition (o o' : O) : bool :=
  existsb (fun s => existsb (fun i =>
    flips step cert s i && nec_w_oeqb (obs s) o && nec_w_oeqb (obs (step s i)) o') Is) Ss.

Lemma nec_w_flip_transition_spec : forall o o',
  nec_w_flip_transition o o' = true <->
  exists s i, flips step cert s i = true /\ obs s = o /\ obs (step s i) = o'.
Proof.
  intros o o'. unfold nec_w_flip_transition. rewrite existsb_exists. split.
  - intros [s [_ H]]. apply existsb_exists in H. destruct H as [i [_ H]].
    apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply nec_w_oeqb_spec in H2, H3. exists s, i. auto.
  - intros [s [i [H1 [H2 H3]]]]. exists s. split; [apply Ss_complete |].
    apply existsb_exists. exists i. split; [apply Is_complete |].
    rewrite H1. simpl. apply andb_true_intro. split; apply nec_w_oeqb_spec; assumption.
Qed.

(** The least window price that meets the floor. *)
Definition nec_w_least_price (o o' : O) : nat :=
  if nec_w_flip_transition o o' then 1 else 0.

Theorem nec_w_least_price_spec :
  meets_floor step cert (shadow_cost step obs nec_w_least_price) /\
  (forall price, meets_floor step cert (shadow_cost step obs price) ->
     forall s i, shadow_cost step obs nec_w_least_price s i <= shadow_cost step obs price s i) /\
  (forall s i, shadow_cost step obs nec_w_least_price s i <= 1) /\
  (forall s i, flips step cert s i = false ->
     (shadow_cost step obs nec_w_least_price s i = 1 <->
      exists s' i', obs s' = obs s /\ obs (step s' i') = obs (step s i) /\
                    flips step cert s' i' = true)).
Proof.
  split; [| split; [| split]].
  - intros s i H. unfold shadow_cost, nec_w_least_price.
    replace (nec_w_flip_transition (obs s) (obs (step s i))) with true; [lia |].
    symmetry. apply nec_w_flip_transition_spec. exists s, i. auto.
  - intros price Hfl s i. unfold shadow_cost, nec_w_least_price.
    destruct (nec_w_flip_transition (obs s) (obs (step s i))) eqn:E; [| lia].
    apply nec_w_flip_transition_spec in E. destruct E as [s' [i' [Hf [E1 E2]]]].
    rewrite <- E1, <- E2. exact (Hfl s' i' Hf).
  - intros s i. unfold shadow_cost, nec_w_least_price.
    destruct (nec_w_flip_transition _ _); lia.
  - intros s i _. unfold shadow_cost, nec_w_least_price. split.
    + intro H. destruct (nec_w_flip_transition (obs s) (obs (step s i))) eqn:E;
        [| discriminate].
      apply nec_w_flip_transition_spec in E. destruct E as [s' [i' [Hf [E1 E2]]]].
      exists s', i'. auto.
    + intros [s' [i' [E1 [E2 Hf]]]].
      replace (nec_w_flip_transition (obs s) (obs (step s i))) with true; [reflexivity |].
      symmetry. apply nec_w_flip_transition_spec. exists s', i'. auto.
Qed.

(** On a finite system, an exact window price exists exactly when the
    window has no collision. *)
Theorem nec_w_finite_exact_iff_no_collision :
  (exists price, nec_w_exact price) <-> ~ shadow_collision step cert obs.
Proof.
  split.
  - intros [price Hex] Hcol. exact (shadow_cannot_price_exactly S I O step cert obs Hcol price Hex).
  - intros Hno. exists nec_w_least_price.
    destruct nec_w_least_price_spec as [Hfl [_ [_ Hover]]]. split; [exact Hfl |].
    intros s i Hf. unfold shadow_cost, nec_w_least_price.
    destruct (nec_w_flip_transition (obs s) (obs (step s i))) eqn:E; [| reflexivity].
    exfalso. apply nec_w_flip_transition_spec in E. destruct E as [s' [i' [Hf' [E1 E2]]]].
    apply Hno. exists s', i', s, i. auto.
Qed.

(** Overcharge along a run: the charge on the steps that do not raise. *)
Fixpoint nec_w_run_overcharge (cost : S -> I -> nat) (s : S) (t : list I) : nat :=
  match t with
  | [] => 0
  | i :: t' => (if flips step cert s i then 0 else cost s i) +
               nec_w_run_overcharge cost (step s i) t'
  end.

(** The non-raising steps of a run whose observed transition some raise
    shares. *)
Fixpoint nec_w_shadowed_count (s : S) (t : list I) : nat :=
  match t with
  | [] => 0
  | i :: t' => (if flips step cert s i then 0
                else if nec_w_flip_transition (obs s) (obs (step s i)) then 1 else 0) +
               nec_w_shadowed_count (step s i) t'
  end.

(** The unavoidable total overcharge: along every run, every window price
    that meets the floor overcharges at least the number of shadowed
    non-raising steps, and the least price overcharges exactly that. *)
Theorem nec_w_run_overcharge_tight :
  forall s t,
    nec_w_run_overcharge (shadow_cost step obs nec_w_least_price) s t = nec_w_shadowed_count s t /\
    forall price, meets_floor step cert (shadow_cost step obs price) ->
      nec_w_shadowed_count s t <= nec_w_run_overcharge (shadow_cost step obs price) s t.
Proof.
  intros s t. revert s. induction t as [| i t IH]; intros s; [split; [reflexivity | intros; simpl; lia] |].
  destruct (IH (step s i)) as [IH1 IH2]. split.
  - simpl. rewrite IH1. destruct (flips step cert s i); [reflexivity |].
    unfold shadow_cost, nec_w_least_price. reflexivity.
  - intros price Hfl. simpl. specialize (IH2 price Hfl).
    destruct (flips step cert s i) eqn:Ef; [lia |].
    destruct nec_w_least_price_spec as [_ [Hmin _]].
    specialize (Hmin price Hfl s i).
    assert (Hm : (if nec_w_flip_transition (obs s) (obs (step s i)) then 1 else 0)
                 <= shadow_cost step obs price s i) by exact Hmin.
    destruct (nec_w_flip_transition (obs s) (obs (step s i))); lia.
Qed.

End Window.

(** Why the finite iff needs finiteness (or some way to decide which
    observed transitions carry a raise): the same iff for every system
    gives weak excluded middle, which Coq's core logic does not prove.
    The system: states are (reading, view) pairs, an instruction is a proof
    of Q or a proof of not Q, a proof of Q raises the reading and shows the
    view true, a proof of not Q drops the reading and shows the view true,
    and a proof of Q from a raised state shows the view false. No collision
    is possible, and an exact price must say yes on (false, true) exactly
    when Q has a proof. *)
Definition nec_w_wlem_step (Q : Prop) (x : bool * bool) (i : Q + ~ Q) : bool * bool :=
  match i with
  | inl _ => if fst x then (true, false) else (true, true)
  | inr _ => (false, true)
  end.

Theorem nec_w_general_converse_gives_wlem :
  (forall (S I O : Type) (step : S -> I -> S) (cert : S -> bool) (obs : S -> O),
     ~ shadow_collision step cert obs -> exists price, nec_w_exact step cert obs price) ->
  forall Q : Prop, ~ Q \/ ~ ~ Q.
Proof.
  intros Hall Q.
  destruct (Hall (bool * bool)%type (Q + ~ Q)%type bool (nec_w_wlem_step Q) fst snd)
    as [price Hex].
  - intros [[c1 o1] [i1 [[c2 o2] [i2 [Hpre [Hpost [H1 H2]]]]]]].
    simpl in Hpre. subst o2.
    destruct c1, i1 as [q | nq]; unfold flips in H1; simpl in H1; try discriminate.
    destruct c2, i2 as [q' | nq']; unfold flips in H2; simpl in Hpost, H2;
      try discriminate; contradiction.
  - destruct (proj1 (nec_w_exact_iff_flip_factors (nec_w_wlem_step Q) fst snd) (ex_intro _ price Hex)) as [g Hg].
    destruct (g false true) eqn:E.
    + right. intros nq. pose proof (Hg (false, false) (inr nq)) as H.
      unfold flips in H. simpl in H. congruence.
    + left. intros q. pose proof (Hg (false, false) (inl q)) as H.
      unfold flips in H. simpl in H. congruence.
Qed.

(** The reading being a function of the view is sufficient for an exact
    window price, not necessary: three states, the window hides which of
    two equal-looking states is certified, and every raise is still
    visible. *)
Definition nec_w_ex_step (s : nat) (_ : unit) : nat :=
  match s with 0 => 1 | n => n end.
Definition nec_w_ex_cert (s : nat) : bool := negb (Nat.eqb s 0).
Definition nec_w_ex_obs (s : nat) : bool := Nat.eqb s 1.

Theorem nec_w_exact_without_reading_in_view :
  (exists price, nec_w_exact nec_w_ex_step nec_w_ex_cert nec_w_ex_obs price) /\
  (exists s i, flips nec_w_ex_step nec_w_ex_cert s i = true) /\
  ~ exists read : bool -> bool, forall s, nec_w_ex_cert s = read (nec_w_ex_obs s).
Proof.
  split; [| split].
  - apply nec_w_exact_iff_flip_factors.
    exists (fun o o' => negb o && o'). intros s [].
    destruct s as [| [| n]]; reflexivity.
  - exists 0, tt. reflexivity.
  - intros [read Hr]. pose proof (Hr 0) as H0. pose proof (Hr 2) as H2.
    unfold nec_w_ex_cert, nec_w_ex_obs in H0, H2. simpl in H0, H2. congruence.
Qed.

(* ================================================================= *)
(** * 3. The escapes, exactly                                         *)
(* ================================================================= *)

(** The commitment verifier is sound and complete exactly when the
    explanation relation meets the contract. *)
Theorem nec_w_commitment_escape_iff {St B : Type} (claim_b : St -> bool)
    (EC : St -> B * bool -> Prop) :
  (ver_sound (ver_claim claim_b) EC ver_bit_verifier /\
   ver_complete (ver_claim claim_b) EC ver_bit_verifier) <->
  ver_contract claim_b EC.
Proof.
  split.
  - intros [Hs Hc]. split.
    + intros s t b He Hb. apply (Hs (t, b)); [exact Hb | exact He].
    + intros s t b He Hcl. exact (Hc s (t, b) Hcl He).
  - apply ver_commitment_escape.
Qed.

(** The unchecked relation breaks the contract exactly when it explains
    anything at all; no unclaimed explained state is needed. *)
Theorem nec_w_unchecked_contract_iff {St B : Type} (claim_b : St -> bool)
    (E0 : St -> B -> Prop) :
  ver_contract claim_b (ver_unchecked E0) <-> forall s t, ~ E0 s t.
Proof.
  split.
  - intros [Hbind Hhon] s t He. unfold ver_claim in *.
    destruct (claim_b s) eqn:Hc.
    + specialize (Hhon s t false He Hc). discriminate.
    + specialize (Hbind s t true He eq_refl). congruence.
  - intros Hno. split; intros s t b He; exfalso; exact (Hno s t He).
Qed.

(** The response verifier is sound and complete exactly when the response
    test is exact, provided some bare transcript exists. *)
Theorem nec_w_response_escape_iff {St B R : Type} (claim_b : St -> bool)
    (resp : St -> R) (acc : R -> bool) (b0 : B) :
  (ver_sound (ver_claim claim_b) (fun s (tr : B * R) => snd tr = resp s) (fun tr => acc (snd tr)) /\
   ver_complete (ver_claim claim_b) (fun s (tr : B * R) => snd tr = resp s) (fun tr => acc (snd tr)))
  <-> (forall s, acc (resp s) = claim_b s).
Proof.
  split.
  - intros [Hs Hc] s. destruct (claim_b s) eqn:Hcl.
    + exact (Hc s (b0, resp s) Hcl eq_refl).
    + destruct (acc (resp s)) eqn:Ha; [| reflexivity].
      pose proof (Hs (b0, resp s) Ha s eq_refl) as H. unfold ver_claim in H. congruence.
  - intros H. apply ver_response_escape. exact H.
Qed.

(** Without a bare transcript the iff fails: with no transcripts the
    verifier is vacuously sound and complete, whatever the test says. *)
Theorem nec_w_response_needs_transcript :
  ver_sound (ver_claim (fun _ : bool => true))
    (fun s (tr : Empty_set * bool) => snd tr = s) (fun tr => negb (snd tr)) /\
  ver_complete (ver_claim (fun _ : bool => true))
    (fun s (tr : Empty_set * bool) => snd tr = s) (fun tr => negb (snd tr)) /\
  ~ (forall s : bool, negb s = true).
Proof.
  split; [| split].
  - intros [e b]. destruct e.
  - intros s [e b]. destruct e.
  - intro H. specialize (H true). discriminate.
Qed.

Print Assumptions nec_w_fibre_converse_fails_without_section.
Print Assumptions nec_w_decoder_iff_fibre_and_partial_section.
Print Assumptions nec_w_fibre_iff_partial_section.
Print Assumptions nec_w_fibre_section_corollary.
Print Assumptions nec_w_surjective_converse_iff_unique_choice.
Print Assumptions nec_w_exact_iff_flip_factors.
Print Assumptions nec_w_factor_no_collision.
Print Assumptions nec_w_shadowed_step_overcharged.
Print Assumptions nec_w_least_price_spec.
Print Assumptions nec_w_finite_exact_iff_no_collision.
Print Assumptions nec_w_run_overcharge_tight.
Print Assumptions nec_w_exact_without_reading_in_view.
Print Assumptions nec_w_commitment_escape_iff.
Print Assumptions nec_w_unchecked_contract_iff.
Print Assumptions nec_w_response_escape_iff.
Print Assumptions nec_w_response_needs_transcript.

(* ================================================================= *)
(** * 4. The collision is exactly what blocks a verifier              *)
(* ================================================================= *)

Section VerifierFinite.

Context {St Tr P : Type}.
Variable claim_b : St -> bool.
Variable ex : St -> Tr -> bool.
Variable Sts : list St.
Hypothesis Sts_complete : forall s, In s Sts.

Definition nec_w_vclaim (s : St) : Prop := claim_b s = true.
Definition nec_w_vexplains (s : St) (t : Tr) : Prop := ex s t = true.

(** On finitely many states with decidable claim and explanation: a sound
    and complete verifier exists exactly when no transcript is explained
    by a state with the claim and a state without it. *)
Theorem nec_w_verifier_iff_no_collision :
  (exists V, ver_sound nec_w_vclaim nec_w_vexplains V /\ ver_complete nec_w_vclaim nec_w_vexplains V) <->
  ~ exists t A B, ex A t = true /\ ex B t = true /\ claim_b A = true /\ claim_b B = false.
Proof.
  split.
  - intros HV [t [A [B [HA [HB [HcA HcB]]]]]].
    apply (ver_collision_blocks nec_w_vclaim nec_w_vexplains t A B HA HB HcA); [| exact HV].
    unfold nec_w_vclaim. congruence.
  - intros Hno. exists (fun t => existsb (fun s => ex s t && claim_b s) Sts). split.
    + intros t Hv s He. apply existsb_exists in Hv. destruct Hv as [s' [_ Hs']].
      apply andb_prop in Hs'. destruct Hs' as [Hex Hcl].
      unfold nec_w_vclaim. destruct (claim_b s) eqn:E; [reflexivity |].
      exfalso. apply Hno. exists t, s', s. auto.
    + intros s t Hc He. apply existsb_exists. exists s. split; [apply Sts_complete |].
      unfold nec_w_vexplains, nec_w_vclaim in *. rewrite He, Hc. reflexivity.
Qed.

Variable Trs : list Tr.
Hypothesis Trs_complete : forall t, In t Trs.
Variable proj : Tr -> P.
Variable P_eq : forall a b : P, {a = b} + {a <> b}.

Definition nec_w_peqb (a b : P) : bool := if P_eq a b then true else false.

(** The same for verifiers that only read a projection of the transcript:
    one exists exactly when no two transcripts with the same projection
    are explained by a state with the claim and a state without it. *)
Theorem nec_w_factoring_verifier_iff_no_collision :
  (exists V, ver_sound nec_w_vclaim nec_w_vexplains V /\ ver_complete nec_w_vclaim nec_w_vexplains V /\
             ver_factors proj V) <->
  ~ exists tA tB A B, proj tA = proj tB /\ ex A tA = true /\ ex B tB = true /\
                      claim_b A = true /\ claim_b B = false.
Proof.
  split.
  - intros [V [Hs [Hc Hf]]] [tA [tB [A [B [Hp [HA [HB [HcA HcB]]]]]]]].
    apply (ver_no_factor St Tr P nec_w_vclaim nec_w_vexplains proj tA tB A B V Hp HA HB HcA);
      [unfold nec_w_vclaim; congruence | exact Hs | exact Hc | exact Hf].
  - intros Hno.
    exists (fun t => existsb (fun s => existsb (fun t' =>
              nec_w_peqb (proj t') (proj t) && ex s t' && claim_b s) Trs) Sts).
    split; [| split].
    + intros t Hv s He. apply existsb_exists in Hv. destruct Hv as [s' [_ Hs']].
      apply existsb_exists in Hs'. destruct Hs' as [t' [_ Ht']].
      apply andb_prop in Ht'. destruct Ht' as [Ht' Hcl]. apply andb_prop in Ht'. destruct Ht' as [Hp Hex].
      unfold nec_w_peqb in Hp. destruct (P_eq (proj t') (proj t)) as [Ep | _]; [| discriminate].
      unfold nec_w_vclaim. destruct (claim_b s) eqn:E; [reflexivity |].
      exfalso. apply Hno. exists t', t, s', s. auto.
    + intros s t Hc He. apply existsb_exists. exists s. split; [apply Sts_complete |].
      apply existsb_exists. exists t. split; [apply Trs_complete |].
      unfold nec_w_peqb, nec_w_vexplains, nec_w_vclaim in *.
      destruct (P_eq (proj t) (proj t)) as [_ | Hn]; [| contradiction].
      rewrite He, Hc. reflexivity.
    + intros t1 t2 E. rewrite E. reflexivity.
Qed.

End VerifierFinite.

Print Assumptions nec_w_verifier_iff_no_collision.
Print Assumptions nec_w_factoring_verifier_iff_no_collision.
Print Assumptions nec_w_general_converse_gives_wlem.
