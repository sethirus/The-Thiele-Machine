(** LiftOneCounter: one counter is not enough.

    A one-counter machine has a finite control (a program of instructions)
    and one counter that can be incremented, and decremented with a zero test:
    the two-counter machine of ThieleComplete.v with register B removed.
    This file proves that its halting problem is decidable, from every
    starting configuration, by an explicit bound.

      oc_halts_within_bound    a program of k instructions started at
                               (pc, n) halts if and only if it has stopped
                               after k * (n + k + 1) steps;
      lift_oc_halts_dec             so "halts" is decided by running that many steps.

    Two-counter halting is not decidable (the vendored library: halting of
    two-counter Minsky machines is undecidable, in LiftModels.v), so no
    translation of two-counter programs into one-counter programs preserves
    halting.  Two counters is the fewest a counter machine can have.

    The proof, in words.  Call a configuration lift_alive when the program counter
    is inside the program.  A run that has been lift_alive for k * (n + k + 1)
    steps never stops.  Either the counter stayed at most n + k all that time,
    and then some configuration (program counter, counter) occurred twice
    among fewer than k * (n + k + 1) possibilities, so the run repeats for
    ever; or the counter reached n + k + 1.  In the second case look at the
    last moment the counter was at most n.  After it the counter is at least
    n + 1, so no zero test fires and the program counter follows the same
    path whatever the counter is.  The counter passes through each of the
    levels n + 1, ..., n + k + 1 for the first time; among these k + 1 first
    passages two have the same program counter, at levels a < b.  Between
    them no zero test fired, so the same stretch run from the higher counter
    does the same thing, ends at the same program counter, and has counter
    raised by b - a at its end.  So the stretch repeats for ever, each time
    from a higher counter, and the run never stops.

    No axioms and no unfinished proofs.                                                  *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file is
   about a different machine, one counter instead of two, and proves its
   halting decidable from the standard library and LiftPigeon.v alone. It uses
   nothing of the small machine. LiftModels.v consumes lift_oc_halts_dec next
   to LiftCore.v, which carries the link to the abstract record. *)

From Coq Require Import List Arith Lia.
Import ListNotations.
From Minimal Require Import LiftPigeon.

(** * The machine *)

Inductive lift_oc_instr : Type :=
| lift_OInc
| lift_ODec (j : nat).

(** (program counter, counter), program counter from 1. *)
Definition lift_oc_conf : Type := (nat * nat)%type.

Definition lift_oc_exec (i : lift_oc_instr) (x : lift_oc_conf) : lift_oc_conf :=
  match i with
  | lift_OInc => (S (fst x), S (snd x))
  | lift_ODec j => match snd x with 0 => (S (fst x), 0) | S n => (j, n) end
  end.

Definition lift_oc_fetch (P : list lift_oc_instr) (n : nat) : option lift_oc_instr :=
  match n with 0 => None | S m => nth_error P m end.

Definition lift_oc_step (P : list lift_oc_instr) (x : lift_oc_conf) : option lift_oc_conf :=
  match lift_oc_fetch P (fst x) with None => None | Some i => Some (lift_oc_exec i x) end.

Fixpoint lift_oc_run (n : nat) (P : list lift_oc_instr) (x : lift_oc_conf) : lift_oc_conf :=
  match n with
  | 0 => x
  | S m => match lift_oc_step P x with None => x | Some y => lift_oc_run m P y end
  end.

Definition lift_oc_halts (P : list lift_oc_instr) (x : lift_oc_conf) : Prop :=
  exists n, lift_oc_step P (lift_oc_run n P x) = None.

(** The step as a total function: a stopped configuration stays. *)
Definition lift_oc_f (P : list lift_oc_instr) (x : lift_oc_conf) : lift_oc_conf :=
  match lift_oc_step P x with Some y => y | None => x end.

Lemma lift_oc_f_some : forall P x y, lift_oc_step P x = Some y -> lift_oc_f P x = y.
Proof. intros P x y H. unfold lift_oc_f. rewrite H. reflexivity. Qed.

Lemma lift_oc_f_none : forall P x, lift_oc_step P x = None -> lift_oc_f P x = x.
Proof. intros P x H. unfold lift_oc_f. rewrite H. reflexivity. Qed.

Lemma lift_oc_iter_fixed : forall P n x, lift_oc_f P x = x -> Nat.iter n (lift_oc_f P) x = x.
Proof.
  intros P n. induction n as [| n IH]; intros x H; [reflexivity |].
  rewrite Nat.iter_succ_r, H. apply IH. exact H.
Qed.

Lemma lift_oc_run_iter : forall n P x, lift_oc_run n P x = Nat.iter n (lift_oc_f P) x.
Proof.
  induction n as [| n IH]; intros P x; [reflexivity |].
  cbn [lift_oc_run]. rewrite Nat.iter_succ_r. destruct (lift_oc_step P x) as [y |] eqn:E.
  - rewrite (lift_oc_f_some P x y E). apply IH.
  - rewrite (lift_oc_f_none P x E). symmetry. apply lift_oc_iter_fixed. apply lift_oc_f_none, E.
Qed.

Section Engine.

Variable P : list lift_oc_instr.
Variable x : lift_oc_conf.

Local Notation f := (lift_oc_f P).
Local Notation k := (length P).
Definition lift_cf (t : nat) : lift_oc_conf := Nat.iter t f x.
Definition lift_cnt (t : nat) : nat := snd (lift_cf t).
Definition lift_pcn (t : nat) : nat := fst (lift_cf t).
Definition lift_alive (t : nat) : Prop := lift_oc_step P (lift_cf t) <> None.

Lemma lift_cf_succ : forall t, lift_cf (S t) = f (lift_cf t).
Proof. intro t. reflexivity. Qed.

Lemma lift_cf_add : forall a b, lift_cf (a + b) = Nat.iter a f (lift_cf b).
Proof. intros a b. unfold lift_cf. rewrite Nat.iter_add. reflexivity. Qed.

Lemma lift_stopped_stays : forall d y, lift_oc_step P y = None -> Nat.iter d f y = y.
Proof. intros d y H. apply lift_oc_iter_fixed, lift_oc_f_none, H. Qed.

Lemma lift_alive_down : forall t s, lift_alive t -> s <= t -> lift_alive s.
Proof.
  intros t s Ht Hs Hn. apply Ht.
  assert (Hc : lift_cf t = lift_cf s).
  { replace t with ((t - s) + s) by lia. rewrite lift_cf_add. apply lift_stopped_stays. exact Hn. }
  unfold lift_alive. rewrite Hc. exact Hn.
Qed.

(** An lift_alive configuration has its program counter inside the program. *)
Lemma lift_alive_pc : forall t, lift_alive t -> 1 <= lift_pcn t /\ lift_pcn t <= k.
Proof.
  intros t H. unfold lift_alive, lift_oc_step in H. unfold lift_pcn.
  destruct (lift_cf t) as [p c]. simpl in *. destruct p as [| p]; [simpl in H; congruence |].
  simpl in H. destruct (nth_error P p) as [i |] eqn:E; [| congruence].
  assert (Hn : nth_error P p <> None) by (rewrite E; discriminate).
  apply nth_error_Some in Hn. lia.
Qed.

Lemma lift_alive_iff_pc : forall y y', fst y = fst y' ->
  (lift_oc_step P y <> None <-> lift_oc_step P y' <> None).
Proof.
  intros y y' H. unfold lift_oc_step. rewrite H.
  destruct (lift_oc_fetch P (fst y')); split; intro; congruence.
Qed.

(** An lift_alive step changes the counter by at most one. *)
Lemma lift_cnt_step : forall t, lift_cnt (S t) <= lift_cnt t + 1 /\ lift_cnt t <= lift_cnt (S t) + 1.
Proof.
  intro t. unfold lift_cnt. rewrite lift_cf_succ. unfold lift_oc_f, lift_oc_step.
  destruct (lift_cf t) as [p c]. simpl. destruct (lift_oc_fetch P p) as [i |]; simpl; [| lia].
  destruct i as [| j]; simpl; [lia |]. destruct c; simpl; lia.
Qed.

(** A configuration that repeats while lift_alive repeats for ever. *)
Lemma lift_rep_never : forall i j, i < j -> lift_cf i = lift_cf j -> lift_alive j -> forall t, lift_alive t.
Proof.
  intros i j Hij Hc Hj.
  assert (Hper : forall d, lift_cf (i + d) = lift_cf (j + d)).
  { intro d. rewrite (Nat.add_comm i d), (Nat.add_comm j d), !lift_cf_add.
    rewrite Hc. reflexivity. }
  intro t. induction t as [t IH] using lt_wf_ind.
  destruct (le_lt_dec t j) as [Hle | Hgt]; [exact (lift_alive_down j t Hj Hle) |].
  assert (Ht : t = j + (t - j)) by lia.
  assert (Hct : lift_cf t = lift_cf (i + (t - j))) by (rewrite Ht at 1; rewrite <- Hper; reflexivity).
  assert (Hal : lift_alive (i + (t - j))) by (apply IH; lia).
  unfold lift_alive in *. rewrite Hct. exact Hal.
Qed.

(** Case A: counters stay low for long enough. *)
Lemma lift_bounded_never : forall Bm, (forall t, t <= k * (Bm + 1) -> lift_cnt t <= Bm) ->
  lift_alive (k * (Bm + 1)) -> forall t, lift_alive t.
Proof.
  intros Bm Hb Hal.
  set (N := k * (Bm + 1)) in *.
  set (g := fun t => (lift_pcn t - 1) * (Bm + 1) + lift_cnt t).
  destruct (lift_pigeon N g) as [i [j [Hij [Hj Hg]]]].
  - intros t Ht. unfold g. pose proof (lift_alive_pc t (lift_alive_down N t Hal Ht)) as [H1 H2].
    pose proof (Hb t Ht) as H3. subst N.
    assert (Hlt : (lift_pcn t - 1) * (Bm + 1) + (Bm + 1) <= k * (Bm + 1)).
    { replace ((lift_pcn t - 1) * (Bm + 1) + (Bm + 1)) with ((lift_pcn t - 1 + 1) * (Bm + 1)) by ring.
      apply Nat.mul_le_mono_r. lia. }
    lia.
  - assert (Hbi : lift_cnt i <= Bm) by (apply Hb; lia).
    assert (Hbj : lift_cnt j <= Bm) by (apply Hb; lia).
    unfold g in Hg.
    assert (Hp : lift_pcn i - 1 = lift_pcn j - 1 /\ lift_cnt i = lift_cnt j).
    { destruct (Nat.lt_trichotomy (lift_pcn i - 1) (lift_pcn j - 1)) as [H | [H | H]].
      - exfalso. assert ((lift_pcn i - 1 + 1) * (Bm + 1) <= (lift_pcn j - 1) * (Bm + 1))
          by (apply Nat.mul_le_mono_r; lia). nia.
      - split; [exact H |]. rewrite H in Hg. lia.
      - exfalso. assert ((lift_pcn j - 1 + 1) * (Bm + 1) <= (lift_pcn i - 1) * (Bm + 1))
          by (apply Nat.mul_le_mono_r; lia). nia. }
    destruct Hp as [Hp Hc].
    pose proof (lift_alive_pc i (lift_alive_down N i Hal ltac:(lia))) as [Hi1 _].
    pose proof (lift_alive_pc j (lift_alive_down N j Hal Hj)) as [Hj1 _].
    assert (Hpc : lift_pcn i = lift_pcn j) by lia.
    apply (lift_rep_never i j Hij); [| apply lift_alive_down with N; [exact Hal | exact Hj]].
    unfold lift_cnt, lift_pcn in *. destruct (lift_cf i), (lift_cf j). simpl in *. subst. reflexivity.
Qed.

End Engine.

(** * Positive runs and the shift lemma *)

(** A zero test that fires: a decrement of a counter that is zero. *)
Definition lift_oc_zero_event (P : list lift_oc_instr) (y : lift_oc_conf) : Prop :=
  (exists j, lift_oc_fetch P (fst y) = Some (lift_ODec j)) /\ snd y = 0.

(** A positive step: the program counter is inside the program and no zero
    test fires. *)
Definition lift_oc_pos (P : list lift_oc_instr) (y : lift_oc_conf) : Prop :=
  lift_oc_step P y <> None /\ ~ lift_oc_zero_event P y.

Lemma lift_oc_pos_shift : forall P p c e, lift_oc_pos P (p, c) ->
  lift_oc_pos P (p, c + e) /\
  lift_oc_f P (p, c + e) = (fst (lift_oc_f P (p, c)), snd (lift_oc_f P (p, c)) + e).
Proof.
  intros P p c e [Hs Hz]. unfold lift_oc_step in Hs. simpl in Hs.
  destruct (lift_oc_fetch P p) as [i |] eqn:Ef; [| congruence].
  unfold lift_oc_f, lift_oc_step. simpl. rewrite Ef. simpl.
  destruct i as [| j].
  - simpl. split; [| reflexivity]. split.
    + unfold lift_oc_step. simpl. rewrite Ef. simpl. congruence.
    + intros [[j Hj] _]. simpl in Hj. rewrite Ef in Hj. congruence.
  - assert (Hc : c <> 0).
    { intro H0. apply Hz. split; [exists j; simpl; exact Ef | simpl; exact H0]. }
    destruct c as [| c']; [congruence |].
    replace (S c' + e) with (S (c' + e)) by lia. simpl. split; [| reflexivity].
    split.
    + unfold lift_oc_step. simpl. rewrite Ef. simpl. congruence.
    + intros [_ H]. simpl in H. lia.
Qed.

Definition lift_oc_posrun (P : list lift_oc_instr) (D : nat) (y : lift_oc_conf) : Prop :=
  forall d, d < D -> lift_oc_pos P (Nat.iter d (lift_oc_f P) y).

Lemma lift_oc_posrun_shift : forall P D p c, lift_oc_posrun P D (p, c) -> forall e,
  lift_oc_posrun P D (p, c + e) /\
  Nat.iter D (lift_oc_f P) (p, c + e)
  = (fst (Nat.iter D (lift_oc_f P) (p, c)), snd (Nat.iter D (lift_oc_f P) (p, c)) + e).
Proof.
  induction D as [| D IH]; intros p c Hr e.
  - split; [intros d Hd; lia | simpl; reflexivity].
  - assert (H0 : lift_oc_pos P (p, c)) by (specialize (Hr 0 ltac:(lia)); exact Hr).
    destruct (lift_oc_pos_shift P p c e H0) as [Hp Hf].
    destruct (lift_oc_f P (p, c)) as [p' c'] eqn:Ef. simpl in Hf.
    assert (Hr' : lift_oc_posrun P D (p', c')).
    { intros d Hd. specialize (Hr (S d) ltac:(lia)).
      rewrite Nat.iter_succ_r in Hr. rewrite Ef in Hr. exact Hr. }
    destruct (IH p' c' Hr' e) as [IHp IHe].
    rewrite !Nat.iter_succ_r, Ef, Hf.
    split; [| exact IHe].
    intros d Hd. destruct d as [| d]; [exact Hp |].
    rewrite Nat.iter_succ_r. rewrite Hf. apply IHp. lia.
Qed.

(** * Searching *)

Lemma lift_oc_bounded_dec : forall (Q : nat -> Prop), (forall n, Q n \/ ~ Q n) -> forall T,
  (exists m, m < T /\ Q m) \/ (forall m, m < T -> ~ Q m).
Proof.
  intros Q Hd. induction T as [| T IH].
  - right. intros m Hm. lia.
  - destruct IH as [[m [Hm Hq]] | Hn].
    + left. exists m. split; [lia | exact Hq].
    + destruct (Hd T) as [Hq | Hq].
      * left. exists T. split; [lia | exact Hq].
      * right. intros m Hm. destruct (Nat.eq_dec m T) as [-> | Hne]; [exact Hq |].
        apply Hn. lia.
Qed.

Lemma lift_oc_greatest_below : forall (Q : nat -> Prop), (forall n, Q n \/ ~ Q n) -> forall t,
  (exists s, s < t /\ Q s) ->
  exists z, z < t /\ Q z /\ forall s, z < s -> s < t -> ~ Q s.
Proof.
  intros Q Hd. induction t as [| t IH]; intros [s [Hs Hq]]; [lia |].
  destruct (Hd t) as [Hqt | Hqt].
  - exists t. split; [lia |]. split; [exact Hqt |]. intros s' H1 H2. lia.
  - assert (Hs' : s < t) by (destruct (Nat.eq_dec s t) as [-> | Hne]; [contradiction | lia]).
    destruct (IH (ex_intro _ s (conj Hs' Hq))) as [z [Hz [Hqz Hnz]]].
    exists z. split; [lia |]. split; [exact Hqz |].
    intros s' H1 H2. destruct (Nat.eq_dec s' t) as [-> | Hne]; [exact Hqt |].
    apply Hnz; lia.
Qed.

(** The first index at or after s, within d steps, where a test holds. *)
Fixpoint lift_oc_first (Qb : nat -> bool) (s d : nat) : nat :=
  match d with
  | 0 => s
  | S d' => if Qb s then s else lift_oc_first Qb (S s) d'
  end.

Lemma lift_oc_first_spec : forall (Qb : nat -> bool) d s,
  (exists m, s <= m /\ m <= s + d /\ Qb m = true) ->
  s <= lift_oc_first Qb s d /\ lift_oc_first Qb s d <= s + d /\ Qb (lift_oc_first Qb s d) = true /\
  forall m, s <= m -> m < lift_oc_first Qb s d -> Qb m = false.
Proof.
  intros Qb. induction d as [| d IH]; intros s [m [H1 [H2 H3]]].
  - assert (m = s) by lia. subst m. simpl. repeat split; try lia; try exact H3;
      try (intros m' Hm' Hlt; lia).
  - simpl. destruct (Qb s) eqn:Es.
    + repeat split; try lia; try exact Es; try (intros m' Hm' Hlt; lia).
    + assert (Hms : S s <= m).
      { destruct (Nat.eq_dec m s) as [-> | Hne]; [congruence | lia]. }
      destruct (IH (S s) (ex_intro _ m (conj Hms (conj (ltac:(lia) : m <= S s + d) H3))))
        as [A [B [C D]]].
      repeat split; try lia. exact C.
      intros m' Hm' Hlt. destruct (Nat.eq_dec m' s) as [-> | Hne]; [exact Es |].
      apply D; lia.
Qed.

Section Levels.

Variable P : list lift_oc_instr.
Variable x : lift_oc_conf.

Local Notation f := (lift_oc_f P).
Local Notation k := (length P).
Local Notation lift_cf := (lift_cf P x).
Local Notation lift_cnt := (lift_cnt P x).
Local Notation lift_pcn := (lift_pcn P x).
Local Notation lift_alive := (lift_alive P x).

(** The counter takes every value between two of its values. *)
Lemma lift_oc_ivt : forall s1 s0 v, s0 <= s1 -> lift_cnt s0 <= v -> v <= lift_cnt s1 ->
  exists s, s0 <= s /\ s <= s1 /\ lift_cnt s = v.
Proof.
  induction s1 as [| s1 IH]; intros s0 v H0 Hlo Hhi.
  - assert (s0 = 0) by lia. subst. exists 0. repeat split; lia.
  - destruct (Nat.eq_dec s0 (S s1)) as [-> | Hne].
    + exists (S s1). repeat split; lia.
    + destruct (le_lt_dec v (lift_cnt s1)) as [Hle | Hgt].
      * destruct (IH s0 v ltac:(lia) Hlo Hle) as [s [A [B C]]]. exists s. repeat split; lia.
      * pose proof (lift_cnt_step P x s1) as [Hs _]. exists (S s1). repeat split; lia.
Qed.


(** The first passage of level n + j, searched for between S z and t. *)
Definition lift_oc_tau (z t n j : nat) : nat :=
  lift_oc_first (fun s => Nat.eqb (lift_cnt s) (n + j)) (S z) (t - S z).

(** Case B: the counter climbs k + 1 levels above its start. *)
Lemma lift_oc_caseB : forall T, lift_alive T ->
  (exists t, t <= T /\ lift_cnt 0 + k + 1 <= lift_cnt t) -> forall t, lift_alive t.
Proof.
  intros T HT [t [Htt Hhigh]].
  set (n := lift_cnt 0) in *.
  assert (Halive_t : lift_alive t) by (apply lift_alive_down with T; assumption).
  assert (Ht0 : 0 < t) by (destruct t as [| t']; lia).
  (* the last moment the counter was at most n *)
  destruct (lift_oc_greatest_below (fun s => lift_cnt s <= n)
              (fun s => match Compare_dec.le_dec (lift_cnt s) n with
                        | left h => or_introl h | right h => or_intror h end)
              t (ex_intro _ 0 (conj Ht0 (le_n n))))
    as [z [Hzt [Hzn Hover]]].
  assert (Habove : forall s, z < s -> s <= t -> n + 1 <= lift_cnt s).
  { intros s H1 H2. destruct (Nat.eq_dec s t) as [-> | Hne]; [lia |].
    specialize (Hover s H1 ltac:(lia)). lia. }
  pose proof (lift_cnt_step P x z) as [Hz1 _].
  assert (Hlevel1 : lift_cnt (S z) = n + 1)
    by (pose proof (Habove (S z) ltac:(lia) ltac:(lia)); lia).
  assert (Htau : forall j, 1 <= j -> j <= k + 1 ->
    S z <= lift_oc_tau z t n j /\ lift_oc_tau z t n j <= t /\ lift_cnt (lift_oc_tau z t n j) = n + j /\
    forall m, S z <= m -> m < lift_oc_tau z t n j -> lift_cnt m <> n + j).
  { intros j Hj1 Hj2.
    destruct (lift_oc_ivt t (S z) (n + j) ltac:(lia) ltac:(lia) ltac:(lia)) as [s [A [B C]]].
    assert (Hex : exists m, S z <= m /\ m <= S z + (t - S z) /\
                            Nat.eqb (lift_cnt m) (n + j) = true)
      by (exists s; repeat split; try lia; apply Nat.eqb_eq; exact C).
    destruct (lift_oc_first_spec (fun s => Nat.eqb (lift_cnt s) (n + j)) (t - S z) (S z) Hex)
      as [H1 [H2 [H3 H4]]].
    unfold lift_oc_tau. repeat split; try lia.
    - apply Nat.eqb_eq. exact H3.
    - intros m Hm Hlt Heq. specialize (H4 m Hm Hlt). apply Nat.eqb_neq in H4. congruence. }
  destruct (lift_pigeon k (fun j' => lift_pcn (lift_oc_tau z t n (S j')) - 1))
    as [a' [b' [Hab [Hb' Hpc]]]].
  { intros j' Hj'. destruct (Htau (S j') ltac:(lia) ltac:(lia)) as [A [B [C D]]].
    pose proof (lift_alive_pc P x (lift_oc_tau z t n (S j')) (lift_alive_down P x t _ Halive_t B)) as [E F].
    lia. }
  simpl in Hpc.
  destruct (Htau (S a') ltac:(lia) ltac:(lia)) as [Ha1 [Ha2 [Ha3 Ha4]]].
  destruct (Htau (S b') ltac:(lia) ltac:(lia)) as [Hb1 [Hb2 [Hb3 Hb4]]].
  assert (Hpa : 1 <= lift_pcn (lift_oc_tau z t n (S a')) /\ lift_pcn (lift_oc_tau z t n (S a')) <= k)
    by (apply lift_alive_pc; apply lift_alive_down with t; assumption).
  assert (Hpb : 1 <= lift_pcn (lift_oc_tau z t n (S b')) /\ lift_pcn (lift_oc_tau z t n (S b')) <= k)
    by (apply lift_alive_pc; apply lift_alive_down with t; assumption).
  remember (lift_oc_tau z t n (S a')) as i eqn:Ei.
  remember (lift_oc_tau z t n (S b')) as j eqn:Ej.
  assert (Hpeq : lift_pcn i = lift_pcn j) by lia.
  assert (Hlt : i < j).
  { destruct (le_lt_dec j i) as [Hle | Hgt]; [| exact Hgt]. exfalso.
    destruct (lift_oc_ivt j (S z) (n + S a') ltac:(lia) ltac:(lia) ltac:(lia)) as [s [A [B C]]].
    destruct (le_lt_dec i s) as [Hs | Hs].
    - assert (Heq : i = j) by lia. rewrite Heq in Ha3. lia.
    - exact (Ha4 s A Hs C). }
  assert (Hci : lift_cf i = (lift_pcn i, lift_cnt i)) by (unfold lift_pcn, lift_cnt; destruct (lift_cf i); reflexivity).
  assert (Hcj : lift_cf j = (lift_pcn j, lift_cnt j)) by (unfold lift_pcn, lift_cnt; destruct (lift_cf j); reflexivity).
  set (D := j - i).
  set (e := lift_cnt j - lift_cnt i).
  assert (HDi : D + i = j) by (unfold D; lia).
  assert (Hcnt : lift_cnt j = lift_cnt i + e) by (unfold e; lia).
  assert (He : 1 <= e) by (unfold e; lia).
  assert (HD : 1 <= D) by (unfold D; lia).
  assert (Hpos : lift_oc_posrun P D (lift_pcn i, lift_cnt i)).
  { intros d Hd. rewrite <- Hci. rewrite <- lift_cf_add. split.
    - apply (lift_alive_down P x t); [exact Halive_t | lia].
    - intros [_ H0]. pose proof (Habove (d + i) ltac:(lia) ltac:(lia)) as H1.
      unfold lift_cnt in H1. simpl in H0. lia. }
  assert (HiterD : Nat.iter D f (lift_pcn i, lift_cnt i) = (lift_pcn i, lift_cnt i + e)).
  { rewrite <- Hci. rewrite <- lift_cf_add, HDi, Hcj. rewrite <- Hpeq, <- Hcnt.
    f_equal. }
  assert (Hclaim : forall r, lift_cf (r * D + i) = (lift_pcn i, lift_cnt i + r * e)).
  { induction r as [| r IH].
    - simpl. rewrite Hci. f_equal; lia.
    - replace (S r * D + i) with (D + (r * D + i)) by ring.
      rewrite lift_cf_add, IH.
      destruct (lift_oc_posrun_shift P D (lift_pcn i) (lift_cnt i) Hpos (r * e)) as [_ Hsh].
      rewrite Hsh, HiterD. simpl. f_equal. ring. }
  assert (Halive_i : lift_alive i) by (apply lift_alive_down with t; [exact Halive_t | lia]).
  assert (Hall : forall r, lift_alive (r * D + i)).
  { intro r. unfold lift_alive. apply (lift_alive_iff_pc P (lift_cf i) (lift_cf (r * D + i))).
    - rewrite Hclaim, Hci. reflexivity.
    - exact Halive_i. }
  intro t'. apply lift_alive_down with (t' * D + i); [apply Hall |]. nia.
Qed.

End Levels.

(** * The decision procedure *)

Theorem lift_oc_halts_bound : forall P x,
  lift_oc_halts P x <->
  lift_oc_step P (lift_oc_run (length P * (snd x + length P + 1)) P x) = None.
Proof.
  intros P x. split.
  - intros [n Hn]. set (F := length P * (snd x + length P + 1)).
    destruct (lift_oc_step P (lift_oc_run F P x)) as [y |] eqn:E; [exfalso | reflexivity].
    assert (HF : lift_alive P x F).
    { unfold lift_alive, lift_cf. rewrite <- lift_oc_run_iter. rewrite E. discriminate. }
    assert (Hall : forall t, lift_alive P x t).
    { destruct (lift_oc_bounded_dec (fun t => lift_cnt P x 0 + length P + 1 <= lift_cnt P x t)
                  (fun t => match Compare_dec.le_dec (lift_cnt P x 0 + length P + 1) (lift_cnt P x t) with
                            | left h => or_introl h | right h => or_intror h end)
                  (S F)) as [[t [Ht Hq]] | Hn'].
      - apply (lift_oc_caseB P x F HF). exists t. split; [lia | exact Hq].
      - apply (lift_bounded_never P x (snd x + length P)).
        + intros t Ht. specialize (Hn' t ltac:(lia)). unfold lift_cnt in *. simpl in *.
          change (snd (lift_cf P x 0)) with (snd x) in Hn'. lia.
        + exact HF. }
    apply (Hall n). unfold lift_alive, lift_cf. rewrite <- lift_oc_run_iter. exact Hn.
  - intro H. exists (length P * (snd x + length P + 1)). exact H.
Qed.

(** Halting of a one-counter program from any configuration is decidable. *)
Theorem lift_oc_halts_dec : forall P x, {lift_oc_halts P x} + {~ lift_oc_halts P x}.
Proof.
  intros P x.
  destruct (lift_oc_step P (lift_oc_run (length P * (snd x + length P + 1)) P x)) eqn:E.
  - right. rewrite lift_oc_halts_bound. rewrite E. discriminate.
  - left. rewrite lift_oc_halts_bound. exact E.
Qed.

(** One-counter programs are two-counter programs that leave register B at
    zero and never name it, so the theorem is a restriction of the machine of
    ThieleComplete.v, not a different machine. *)
Require Minimal.ThieleComplete.
Module T := Minimal.ThieleComplete.

Definition lift_oc_to_cm (i : lift_oc_instr) : T.cm_instr :=
  match i with lift_OInc => T.CINC T.RA | lift_ODec j => T.CDEC T.RA j end.

Lemma lift_oc_embed_step : forall P x,
  T.cm_step (map lift_oc_to_cm P) (fst x, (snd x, 0)) =
  match lift_oc_step P x with
  | Some y => Some (fst y, (snd y, 0))
  | None => None
  end.
Proof.
  intros P [p c]. unfold T.cm_step, T.cm_fetch, lift_oc_step, lift_oc_fetch. simpl.
  destruct p as [| p]; [reflexivity |].
  rewrite nth_error_map. destruct (nth_error P p) as [i |]; [| reflexivity].
  simpl. destruct i as [| j]; simpl; [reflexivity |].
  destruct c; reflexivity.
Qed.

Theorem lift_oc_embed_run : forall n P x,
  T.cm_run n (map lift_oc_to_cm P) (fst x, (snd x, 0))
  = (fst (lift_oc_run n P x), (snd (lift_oc_run n P x), 0)).
Proof.
  induction n as [| n IH]; intros P x; [destruct x; reflexivity |].
  cbn [T.cm_run lift_oc_run]. rewrite lift_oc_embed_step.
  destruct (lift_oc_step P x) as [y |]; [| destruct x; reflexivity].
  exact (IH P y).
Qed.

(** The two-counter machine started with register B empty and a program that
    never names register B halts exactly when the one-counter program does, and
    that is decided. *)
Theorem lift_oc_embed_halts : forall P x,
  (exists n, T.cm_step (map lift_oc_to_cm P) (T.cm_run n (map lift_oc_to_cm P) (fst x, (snd x, 0))) = None)
  <-> lift_oc_halts P x.
Proof.
  intros P x. split; intros [n Hn]; exists n.
  - rewrite lift_oc_embed_run in Hn. rewrite lift_oc_embed_step in Hn.
    destruct (lift_oc_step P (lift_oc_run n P x)); [discriminate | reflexivity].
  - rewrite lift_oc_embed_run. rewrite lift_oc_embed_step. rewrite Hn. reflexivity.
Qed.

Print Assumptions lift_oc_halts_bound.
Print Assumptions lift_oc_halts_dec.
Print Assumptions lift_oc_embed_halts.
