(** Tc2Forced.v: the forced run of a tame machine.

    Take a configuration of a tame machine in which counter A is small (below
    the threshold) and counter B is large. As long as counter B stays at or
    above the threshold, the run does not depend on how large B is, except
    through the parity of B: B is a passive store that the control only reads
    through its parity. The forced run records this: its state is
    (control, counter A, parity of B) and its output is the change of B.

    This file defines the forced run, proves that the real run is the forced
    run while B stays at or above the threshold ([fs_corr]) and that the
    forced run is translated when counter A is raised by an even amount that
    keeps it at or above the threshold ([fs_orb_sh]).

    Dependencies: Tc2Am.v. No axioms and no unfinished proofs.                         *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is about abstract two-counter machines with a finite control, the shape
   the two-counter machine of EarnedCore.v takes once its finite part is the
   control (Tc2Embed.v). The machine's link to the abstract record (a
   CertificationSystem with the trace cost floor, and a Thiele-complete
   machine) lives in EarnedCoreLinks.v and ThieleComplete.v. *)


From Coq Require Import List Arith Lia Bool ZArith.
Import ListNotations.
Require Import Minimal.Tc2Am.
Set Default Goal Selector "!".

Definition fcfg (M : tc2_am) : Type := (am_Q M * nat * nat)%type.

(* the smallest value of B at or above the threshold with the parity p *)
(* the parity of a number, kept folded so that no tactic unfolds it *)
Definition fs_par (y : nat) : nat := y mod 2.

Lemma fs_par_lt : forall y, fs_par y < 2.
Proof. intro y. unfold fs_par. apply Nat.mod_upper_bound. lia. Qed.

Lemma fs_par_spec : forall y, y = 2 * (y / 2) + fs_par y.
Proof. intro y. unfold fs_par. apply Nat.div_mod. lia. Qed.

Lemma fs_par_add2 : forall y d, fs_par (y + 2 * d) = fs_par y.
Proof.
  intros y d. unfold fs_par. replace (y + 2 * d) with (y + d * 2) by lia. apply Nat.Div0.mod_add.
Qed.

Lemma fs_par_eq : forall y z, fs_par y = fs_par z -> exists a b, y = 2 * a + fs_par z /\ z = 2 * b + fs_par z.
Proof.
  intros y z H. exists (y / 2), (z / 2). split.
  - rewrite <- H. apply fs_par_spec.
  - apply fs_par_spec.
Qed.

Definition fs_yrep (M : tc2_am) (p : nat) : nat := am_B M + (am_B M + p) mod 2.

Lemma fs_yrep_ge : forall M p, am_B M <= fs_yrep M p.
Proof. intros. unfold fs_yrep. lia. Qed.

Lemma fs_yrep_le : forall M p, fs_yrep M p <= am_B M + 1.
Proof.
  intros. unfold fs_yrep. pose proof (Nat.mod_upper_bound (am_B M + p) 2 ltac:(lia)). lia.
Qed.

Lemma fs_yrep_mod : forall M p, p < 2 -> fs_par (fs_yrep M p) = p.
Proof.
  intros M p Hp. unfold fs_yrep, fs_par.
  set (B := am_B M).
  pose proof (Nat.div_mod B 2 ltac:(lia)) as H1.
  pose proof (Nat.mod_upper_bound B 2 ltac:(lia)) as H2.
  pose proof (Nat.div_mod (B + p) 2 ltac:(lia)) as H3.
  pose proof (Nat.mod_upper_bound (B + p) 2 ltac:(lia)) as H4.
  pose proof (Nat.div_mod (B + (B + p) mod 2) 2 ltac:(lia)) as H5.
  pose proof (Nat.mod_upper_bound (B + (B + p) mod 2) 2 ltac:(lia)) as H6.
  lia.
Qed.

Definition fq (M : tc2_am) (s : fcfg M) : am_Q M := fst (fst s).
Definition fx (M : tc2_am) (s : fcfg M) : nat := snd (fst s).
Definition fp (M : tc2_am) (s : fcfg M) : nat := snd s.
Definition fs_shA (M : tc2_am) (d : nat) (s : fcfg M) : fcfg M :=
  match s with (q, x, p) => (q, x + d, p) end.

(* one step of the forced run: the control and counter A move as the machine moves
   when B holds the representative value; the second component is the change of B *)
Definition fs_nx (M : tc2_am) (s : fcfg M) : option (fcfg M * Z) :=
  match s with (q, x, p) =>
    match am_nx M q x (fs_yrep M p) with
    | Some (q', x', y') => Some ((q', x', fs_par y'), (Z.of_nat y' - Z.of_nat (fs_yrep M p))%Z)
    | None => None
    end
  end.

Fixpoint fs_orb (M : tc2_am) (s0 : fcfg M) (n : nat) : fcfg M * Z :=
  match n with
  | 0 => (s0, 0%Z)
  | S n' => match fs_nx M (fst (fs_orb M s0 n')) with
            | Some (s', dy) => (s', (snd (fs_orb M s0 n') + dy)%Z)
            | None => fs_orb M s0 n'
            end
  end.

Definition fo_s (M : tc2_am) (s0 : fcfg M) (n : nat) : fcfg M := fst (fs_orb M s0 n).
Definition fo_d (M : tc2_am) (s0 : fcfg M) (n : nat) : Z := snd (fs_orb M s0 n).

Lemma fo_s_0 : forall M s0, fo_s M s0 0 = s0.
Proof. reflexivity. Qed.
Lemma fo_d_0 : forall M s0, fo_d M s0 0 = 0%Z.
Proof. reflexivity. Qed.

Lemma fo_S_some : forall M s0 n s' dy, fs_nx M (fo_s M s0 n) = Some (s', dy) ->
  fo_s M s0 (S n) = s' /\ fo_d M s0 (S n) = (fo_d M s0 n + dy)%Z.
Proof.
  intros M s0 n s' dy H. unfold fo_s, fo_d in *. simpl. rewrite H. split; reflexivity.
Qed.

Lemma fo_S_none : forall M s0 n, fs_nx M (fo_s M s0 n) = None ->
  fo_s M s0 (S n) = fo_s M s0 n /\ fo_d M s0 (S n) = fo_d M s0 n.
Proof.
  intros M s0 n H. unfold fo_s, fo_d in *. simpl. rewrite H. split; reflexivity.
Qed.

Definition fs_start (M : tc2_am) (q0 : am_Q M) (s0 v : nat) : fcfg M := (q0, s0, fs_par v).

(* the real run is the forced run while B stays at or above the threshold *)
Lemma fs_corr : forall M q0 s0 v n,
  (forall t, t < n -> (Z.of_nat (am_B M) <= Z.of_nat v + fo_d M (fs_start M q0 s0 v) t)%Z) ->
  exists y, Z.of_nat y = (Z.of_nat v + fo_d M (fs_start M q0 s0 v) n)%Z /\
    am_run M n (q0, s0, v) = (fq M (fo_s M (fs_start M q0 s0 v) n), fx M (fo_s M (fs_start M q0 s0 v) n), y) /\
    fp M (fo_s M (fs_start M q0 s0 v) n) = fs_par y.
Proof.
  intros M q0 s0 v n. induction n as [| n IH]; intro H.
  - exists v. unfold fo_s, fo_d, fq, fx, fp, fs_start. simpl. repeat split; first [reflexivity | lia].
  - destruct (IH (fun t Ht => H t (Nat.lt_lt_succ_r _ _ Ht))) as (y & Hy & Hrun & Hp).
    assert (HB : (Z.of_nat (am_B M) <= Z.of_nat y)%Z) by (rewrite Hy; apply H; lia).
    rewrite am_run_S_r, Hrun.
    set (s := fo_s M (fs_start M q0 s0 v) n) in *.
    destruct s as [[q x] pp] eqn:Hs. unfold fq, fx, fp in *. cbn [fst snd] in *.
    pose proof (fs_yrep_ge M pp) as Hge.
    assert (Hpp : pp < 2) by (rewrite Hp; apply fs_par_lt).
    pose proof (fs_yrep_mod M pp Hpp) as Hmod.
    pose proof (fs_yrep_le M pp) as Hle.
    assert (Hd : exists d, y = fs_yrep M pp + 2 * d).
    { pose proof (fs_par_spec y) as H1.
      pose proof (fs_par_spec (fs_yrep M pp)) as H2.
      exists (y / 2 - fs_yrep M pp / 2). rewrite <- Hp in H1. rewrite Hmod in H2. lia. }
    destruct Hd as [d Hd].
    unfold am_stp. rewrite Hd. rewrite (am_tameB M q x (fs_yrep M pp) d Hge).
    destruct (am_nx M q x (fs_yrep M pp)) as [[[q' x'] y'] |] eqn:En.
    + destruct (fo_S_some M (fs_start M q0 s0 v) n (q', x', fs_par y') (Z.of_nat y' - Z.of_nat (fs_yrep M pp))%Z) as [Hs1 Hs2].
      * unfold fo_s in *. fold s. rewrite Hs. simpl. rewrite En. reflexivity.
      * exists (y' + 2 * d). rewrite Hs1. unfold fq, fx, fp. cbn [fst snd].
        rewrite Hs2. repeat split; try lia.
        symmetry. apply fs_par_add2.
    + destruct (fo_S_none M (fs_start M q0 s0 v) n) as [Hs1 Hs2].
      * unfold fo_s in *. fold s. rewrite Hs. simpl. rewrite En. reflexivity.
      * exists y. rewrite Hs1, Hs2. fold s. rewrite Hs. unfold fq, fx, fp. cbn [fst snd]. subst y. repeat split; try lia.
Qed.

(* ------------------------------------------------------------------ *)
(* the forced orbit: composition, steps, parity, translation          *)
(* ------------------------------------------------------------------ *)

Lemma fo_add : forall M s0 n m,
  fo_s M s0 (n + m) = fo_s M (fo_s M s0 n) m /\
  fo_d M s0 (n + m) = (fo_d M s0 n + fo_d M (fo_s M s0 n) m)%Z.
Proof.
  intros M s0 n m. induction m as [| m IH].
  - rewrite Nat.add_0_r. rewrite fo_d_0. split; [reflexivity | lia].
  - destruct IH as [IH1 IH2].
    replace (n + S m) with (S (n + m)) by lia.
    destruct (fs_nx M (fo_s M s0 (n + m))) as [[s' dy] |] eqn:E.
    + destruct (fo_S_some M s0 (n + m) s' dy E) as [H1 H2].
      assert (E' : fs_nx M (fo_s M (fo_s M s0 n) m) = Some (s', dy)) by (rewrite <- IH1; exact E).
      destruct (fo_S_some M _ m s' dy E') as [H3 H4].
      rewrite H1, H2, H3, H4, IH2. split; [reflexivity | lia].
    + destruct (fo_S_none M s0 (n + m) E) as [H1 H2].
      assert (E' : fs_nx M (fo_s M (fo_s M s0 n) m) = None) by (rewrite <- IH1; exact E).
      destruct (fo_S_none M _ m E') as [H3 H4].
      rewrite H1, H2, H3, H4, IH1, IH2. split; [reflexivity | lia].
Qed.

Lemma fs_nx_bound : forall M s s' dy, fs_nx M s = Some (s', dy) ->
  (fx M s' = fx M s \/ fx M s' = S (fx M s) \/ S (fx M s') = fx M s) /\
  (-1 <= dy <= 1)%Z /\ fp M s' < 2.
Proof.
  intros M [[q x] p] s' dy H. unfold fs_nx in H.
  destruct (am_nx M q x (fs_yrep M p)) as [[[q' x'] y'] |] eqn:E; [| discriminate].
  injection H as <- <-.
  change (fx M (q', x', fs_par y')) with x'. change (fx M (q, x, p)) with x.
  change (fp M (q', x', fs_par y')) with (fs_par y').
  destruct (am_step1 M _ _ _ _ _ _ E) as [[H1 [H2 | [H2 | H2]]] | [H1 [H2 | H2]]];
    pose proof (fs_par_lt y'); repeat split; lia.
Qed.

Lemma fo_step : forall M s0 t,
  (fx M (fo_s M s0 (S t)) = fx M (fo_s M s0 t) \/ fx M (fo_s M s0 (S t)) = S (fx M (fo_s M s0 t)) \/
   S (fx M (fo_s M s0 (S t))) = fx M (fo_s M s0 t)) /\
  (-1 <= fo_d M s0 (S t) - fo_d M s0 t <= 1)%Z.
Proof.
  intros M s0 t. destruct (fs_nx M (fo_s M s0 t)) as [[s' dy] |] eqn:E.
  - destruct (fo_S_some M s0 t s' dy E) as [H1 H2]. destruct (fs_nx_bound M _ _ _ E) as (B1 & B2 & _).
    rewrite H1, H2. split; [exact B1 | lia].
  - destruct (fo_S_none M s0 t E) as [H1 H2]. rewrite H1, H2. split; [left; reflexivity | lia].
Qed.

Lemma fo_x_le : forall M s0 t, fx M (fo_s M s0 t) <= fx M s0 + t.
Proof.
  intros M s0 t. induction t as [| t IH]; [rewrite fo_s_0; lia |].
  destruct (fo_step M s0 t) as [[H | [H | H]] _]; lia.
Qed.

Lemma fo_d_bound : forall M s0 t, (- Z.of_nat t <= fo_d M s0 t <= Z.of_nat t)%Z.
Proof.
  intros M s0 t. induction t as [| t IH]; [rewrite fo_d_0; simpl; lia |].
  destruct (fo_step M s0 t) as [_ H]. lia.
Qed.

Lemma fo_p_lt : forall M s0 t, fp M s0 < 2 -> fp M (fo_s M s0 t) < 2.
Proof.
  intros M s0 t H. induction t as [| t IH]; [exact H |].
  destruct (fs_nx M (fo_s M s0 t)) as [[s' dy] |] eqn:E.
  - destruct (fo_S_some M s0 t s' dy E) as [H1 _]. rewrite H1. destruct (fs_nx_bound M _ _ _ E) as (_ & _ & B3). exact B3.
  - destruct (fo_S_none M s0 t E) as [H1 _]. rewrite H1. exact IH.
Qed.

Lemma fs_nx_q : forall M s s' dy, fs_nx M s = Some (s', dy) ->
  In (fq M s) (am_lq M) -> In (fq M s') (am_lq M).
Proof.
  intros M [[q x] p] s' dy H Hin. unfold fs_nx in H.
  destruct (am_nx M q x (fs_yrep M p)) as [[[q' x'] y'] |] eqn:E; [| discriminate].
  injection H as <- <-. change (fq M (q', x', fs_par y')) with q'. change (fq M (q, x, p)) with q in Hin.
  exact (am_closed M _ _ _ _ _ _ Hin E).
Qed.

Lemma fo_q_in : forall M s0 t, In (fq M s0) (am_lq M) -> In (fq M (fo_s M s0 t)) (am_lq M).
Proof.
  intros M s0 t H. induction t as [| t IH]; [exact H |].
  destruct (fs_nx M (fo_s M s0 t)) as [[s' dy] |] eqn:E.
  - destruct (fo_S_some M s0 t s' dy E) as [H1 _]. rewrite H1. exact (fs_nx_q M _ _ _ E IH).
  - destruct (fo_S_none M s0 t E) as [H1 _]. rewrite H1. exact IH.
Qed.

(* the parity of B tracked by the forced run is the parity of its start plus the change of B *)
Lemma fo_par : forall M s0 n, fp M s0 < 2 ->
  exists k : Z, Z.of_nat (fp M (fo_s M s0 n)) = (Z.of_nat (fp M s0) + fo_d M s0 n + 2 * k)%Z.
Proof.
  intros M s0 n Hp. induction n as [| n IH].
  - exists 0%Z. rewrite fo_s_0, fo_d_0. lia.
  - destruct IH as [k Hk].
    destruct (fs_nx M (fo_s M s0 n)) as [[s' dy] |] eqn:E.
    + destruct (fo_S_some M s0 n s' dy E) as [H1 H2]. rewrite H1, H2.
      unfold fs_nx in E. destruct (fo_s M s0 n) as [[q x] p] eqn:Hs.
      destruct (am_nx M q x (fs_yrep M p)) as [[[q' x'] y'] |] eqn:En; [| discriminate].
      injection E as <- <-. unfold fp in *. cbn [fst snd] in *.
      assert (Hp2 : p < 2).
      { pose proof (fo_p_lt M s0 n Hp) as H. rewrite Hs in H. unfold fp in H. cbn [fst snd] in H. exact H. }
      pose proof (fs_yrep_mod M p Hp2) as Hm.
      pose proof (fs_par_spec y') as D1.
      pose proof (fs_par_spec (fs_yrep M p)) as D2. rewrite Hm in D2.
      exists (k + Z.of_nat (fs_yrep M p / 2) - Z.of_nat (y' / 2))%Z. lia.
    + destruct (fo_S_none M s0 n E) as [H1 H2]. rewrite H1, H2. exists k. exact Hk.
Qed.

Lemma fs_nx_sh : forall M d q x p, am_B M <= x ->
  fs_nx M (q, x + 2 * d, p) =
    match fs_nx M (q, x, p) with Some (s', dy) => Some (fs_shA M (2 * d) s', dy) | None => None end.
Proof.
  intros M d q x p H. unfold fs_nx. rewrite (am_tameA M q x (fs_yrep M p) d H).
  destruct (am_nx M q x (fs_yrep M p)) as [[[q' x'] y'] |]; reflexivity.
Qed.

(* the forced orbit of a translated start is the translated orbit, while counter A stays above the threshold *)
Lemma fo_sh : forall M d s0 n,
  (forall t, t < n -> am_B M <= fx M (fo_s M s0 t)) ->
  fo_s M (fs_shA M (2 * d) s0) n = fs_shA M (2 * d) (fo_s M s0 n) /\
  fo_d M (fs_shA M (2 * d) s0) n = fo_d M s0 n.
Proof.
  intros M d s0 n. induction n as [| n IH]; intro H.
  - simpl. split; reflexivity.
  - destruct (IH (fun t Ht => H t (Nat.lt_lt_succ_r _ _ Ht))) as [IH1 IH2].
    assert (HB : am_B M <= fx M (fo_s M s0 n)) by (apply H; lia).
    assert (E1 : fs_nx M (fo_s M (fs_shA M (2 * d) s0) n) =
                 match fs_nx M (fo_s M s0 n) with Some (s', dy) => Some (fs_shA M (2 * d) s', dy) | None => None end).
    { rewrite IH1. destruct (fo_s M s0 n) as [[q x] p] eqn:Hs. cbn [fs_shA].
      unfold fx in HB. cbn [fst snd] in HB. apply fs_nx_sh. exact HB. }
    destruct (fs_nx M (fo_s M s0 n)) as [[s' dy] |] eqn:E.
    + cbv iota in E1. destruct (fo_S_some M _ n _ _ E1) as [H1 H2].
      destruct (fo_S_some M s0 n s' dy E) as [H3 H4]. rewrite H1, H2, H3, H4, IH2. split; reflexivity.
    + cbv iota in E1. destruct (fo_S_none M _ n E1) as [H1 H2].
      destruct (fo_S_none M s0 n E) as [H3 H4]. rewrite H1, H2, H3, H4, IH1, IH2. split; reflexivity.
Qed.

Lemma fx_shA : forall M d s, fx M (fs_shA M d s) = fx M s + d.
Proof. intros M d [[q x] p]. reflexivity. Qed.
Lemma fq_shA : forall M d s, fq M (fs_shA M d s) = fq M s.
Proof. intros M d [[q x] p]. reflexivity. Qed.
Lemma fp_shA : forall M d s, fp M (fs_shA M d s) = fp M s.
Proof. intros M d [[q x] p]. reflexivity. Qed.

Lemma fs_nx_shs : forall M d s, am_B M <= fx M s ->
  fs_nx M (fs_shA M (2 * d) s) =
    match fs_nx M s with Some (s', dy) => Some (fs_shA M (2 * d) s', dy) | None => None end.
Proof.
  intros M d [[q x] p] H. unfold fx in H. cbn [fst snd] in H. cbn [fs_shA]. apply fs_nx_sh. exact H.
Qed.

Lemma fs_cfg_eq : forall M (x y : am_Q M * nat * nat), {x = y} + {x <> y}.
Proof.
  intros M [[a b] c] [[a' b'] c'].
  destruct (am_eq M a a') as [-> | Hn]; [| right; intro H; apply Hn; congruence].
  destruct (Nat.eq_dec b b') as [-> | Hn]; [| right; intro H; apply Hn; congruence].
  destruct (Nat.eq_dec c c') as [-> | Hn]; [| right; intro H; apply Hn; congruence].
  left. reflexivity.
Qed.

Section Orb.
Variable M : tc2_am.
Variable s0 : fcfg M.
Local Notation Sx t := (fo_s M s0 t).
Local Notation Xx t := (fx M (fo_s M s0 t)).
Local Notation Dx t := (fo_d M s0 t).
Local Notation Bt := (am_B M).

(* a translated state continues as the translation, while the lower orbit stays above the threshold *)
Lemma orb_pump_asc : forall i p g2,
  0 < p ->
  Sx (i + p) = fs_shA M (2 * g2) (Sx i) ->
  (forall t, i <= t -> t <= i + p -> Bt <= Xx t) ->
  (forall t, t <= i + p -> fs_nx M (Sx t) <> None) ->
  forall t, i <= t ->
    Bt <= Xx t /\ fs_nx M (Sx t) <> None /\
    Sx (t + p) = fs_shA M (2 * g2) (Sx t) /\ Dx (t + p) = (Dx t + (Dx (i + p) - Dx i))%Z.
Proof.
  intros i p g2 Hp Hs Hhigh Hnh.
  assert (key : forall n t, t = i + n ->
    Bt <= Xx t /\ fs_nx M (Sx t) <> None /\
    Sx (t + p) = fs_shA M (2 * g2) (Sx t) /\ Dx (t + p) = (Dx t + (Dx (i + p) - Dx i))%Z).
  { intro n. induction n as [n IH] using lt_wf_ind. intros t Ht.
    destruct n as [| n'].
    - subst t. rewrite Nat.add_0_r. repeat split; [apply Hhigh; lia | apply Hnh; lia | exact Hs | lia].
    - destruct (IH n' ltac:(lia) (i + n') eq_refl) as (H1 & H2 & H3 & H4).
      destruct (fs_nx M (Sx (i + n'))) as [[s' dy] |] eqn:E; [| contradiction].
      destruct (fo_S_some M s0 (i + n') s' dy E) as [E1 E2].
      assert (E3 : fs_nx M (Sx (i + n' + p)) = Some (fs_shA M (2 * g2) s', dy)).
      { rewrite H3. rewrite fs_nx_shs by exact H1. rewrite E. reflexivity. }
      destruct (fo_S_some M s0 (i + n' + p) _ _ E3) as [E4 E5].
      assert (Ht1 : t = S (i + n')) by lia.
      assert (HS : Sx (t + p) = fs_shA M (2 * g2) (Sx t)).
      { rewrite Ht1. replace (S (i + n') + p) with (S (i + n' + p)) by lia. rewrite E4, E1. reflexivity. }
      assert (HD : Dx (t + p) = (Dx t + (Dx (i + p) - Dx i))%Z).
      { rewrite Ht1. replace (S (i + n') + p) with (S (i + n' + p)) by lia. rewrite E5, E2. lia. }
      assert (Hup : t > i + p -> Bt <= Xx (t - p) /\ fs_nx M (Sx (t - p)) <> None /\ Sx t = fs_shA M (2 * g2) (Sx (t - p))).
      { intro Hgt. destruct (IH (t - p - i) ltac:(lia) (t - p) ltac:(lia)) as (K1 & K2 & K3 & _).
        replace (t - p + p) with t in K3 by lia. split; [exact K1 | split; [exact K2 | exact K3]]. }
      repeat split.
      + destruct (le_lt_dec t (i + p)) as [Hle | Hgt].
        * apply Hhigh; lia.
        * destruct (Hup Hgt) as (U1 & U2 & U3). rewrite U3, fx_shA. lia.
      + destruct (le_lt_dec t (i + p)) as [Hle | Hgt].
        * apply Hnh; lia.
        * destruct (Hup Hgt) as (U1 & U2 & U3). rewrite U3, fs_nx_shs by exact U1.
          destruct (fs_nx M (Sx (t - p))) as [[s'' dy'] |]; [discriminate | contradiction].
      + exact HS.
      + exact HD. }
  intros t Ht. apply (key (t - i) t). lia.
Qed.

End Orb.

Print Assumptions orb_pump_asc.

Lemma fs_shA_of : forall M d (s s' : fcfg M), fq M s = fq M s' -> fp M s = fp M s' ->
  fx M s = fx M s' + 2 * d -> s = fs_shA M (2 * d) s'.
Proof.
  intros M d [[q x] p] [[q' x'] p'] H1 H2 H3. unfold fq, fp, fx in *. cbn [fst snd fs_shA] in *.
  subst. reflexivity.
Qed.

Section Orb2.
Variable M : tc2_am.
Variable s0 : fcfg M.
Hypothesis hq0 : In (fq M s0) (am_lq M).
Hypothesis hp0 : fp M s0 < 2.
Hypothesis hx0 : fx M s0 < am_B M.
Local Notation Sx t := (fo_s M s0 t).
Local Notation Xx t := (fx M (fo_s M s0 t)).
Local Notation Dx t := (fo_d M s0 t).
Local Notation Bt := (am_B M).

Lemma orb_x_from : forall s k, Xx (s + k) <= Xx s + k.
Proof.
  intros s k. induction k as [| k IH]; [rewrite Nat.add_0_r; lia |].
  replace (s + S k) with (S (s + k)) by lia.
  destruct (fo_step M s0 (s + k)) as [[H | [H | H]] _]; lia.
Qed.

(* the orbit drifts down: an even descent per period cannot continue for more than X i + 1 periods *)
Lemma orb_pump_desc : forall i p g2 R,
  0 < p -> 0 < g2 ->
  Sx i = fs_shA M (2 * g2) (Sx (i + p)) ->
  (forall t, i <= t -> t <= i + (R + 1) * p -> Bt <= Xx t) ->
  forall r, r <= R ->
    fq M (Sx (i + r * p)) = fq M (Sx i) /\ fp M (Sx (i + r * p)) = fp M (Sx i) /\
    Xx (i + r * p) + 2 * (r * g2) = Xx i.
Proof.
  intros i p g2 R Hp Hg Hs Hhigh r. induction r as [| r IH]; intro Hr.
  - rewrite Nat.mul_0_l, Nat.add_0_r. repeat split; lia.
  - destruct (IH ltac:(lia)) as (I1 & I2 & I3).
    assert (Hsh : Sx i = fs_shA M (2 * (r * g2)) (Sx (i + r * p))).
    { apply fs_shA_of; [symmetry; exact I1 | symmetry; exact I2 | lia]. }
    assert (Hhi : forall t, t < p -> Bt <= fx M (fo_s M (Sx (i + r * p)) t)).
    { intros t Ht. rewrite <- (proj1 (fo_add M s0 (i + r * p) t)). apply Hhigh.
      - lia.
      - assert ((r + 1) * p = r * p + p) by ring. nia. }
    destruct (fo_sh M (r * g2) (Sx (i + r * p)) p Hhi) as [F1 _].
    rewrite <- Hsh in F1.
    rewrite <- (proj1 (fo_add M s0 i p)) in F1.
    rewrite <- (proj1 (fo_add M s0 (i + r * p) p)) in F1.
    assert (Hq1 : fq M (Sx (i + p)) = fq M (Sx (i + r * p + p))) by (rewrite F1, fq_shA; reflexivity).
    assert (Hp1 : fp M (Sx (i + p)) = fp M (Sx (i + r * p + p))) by (rewrite F1, fp_shA; reflexivity).
    assert (Hx1 : Xx (i + p) = Xx (i + r * p + p) + 2 * (r * g2)) by (rewrite F1, fx_shA; reflexivity).
    assert (Hq2 : fq M (Sx i) = fq M (Sx (i + p))) by (rewrite Hs, fq_shA; reflexivity).
    assert (Hp2 : fp M (Sx i) = fp M (Sx (i + p))) by (rewrite Hs, fp_shA; reflexivity).
    assert (Hx2 : Xx i = Xx (i + p) + 2 * g2) by (rewrite Hs, fx_shA; reflexivity).
    replace (i + S r * p) with (i + r * p + p) by (simpl; ring).
    repeat split; [rewrite <- Hq1; symmetry; exact Hq2 | rewrite <- Hp1; symmetry; exact Hp2 | ].
    replace (S r * g2) with (r * g2 + g2) by (simpl; ring). lia.
Qed.

Lemma orb_no_desc : forall i p g2,
  0 < p -> 0 < g2 ->
  Sx i = fs_shA M (2 * g2) (Sx (i + p)) ->
  (forall t, i <= t -> t <= i + (Xx i + 2) * p -> Bt <= Xx t) -> False.
Proof.
  intros i p g2 Hp Hg Hs Hh.
  assert (Hhigh : forall t, i <= t -> t <= i + (Xx i + 1 + 1) * p -> Bt <= Xx t).
  { intros t H1 H2. apply Hh; [exact H1 |]. replace (Xx i + 1 + 1) with (Xx i + 2) in H2 by lia. exact H2. }
  destruct (orb_pump_desc i p g2 (Xx i + 1) Hp Hg Hs Hhigh (Xx i + 1) (le_n _)) as (_ & _ & H).
  assert (Hge : (Xx i + 1) <= (Xx i + 1) * g2) by nia. lia.
Qed.

(* the first time counter A reaches the threshold from below it is exactly at the threshold *)
Lemma orb_entry : forall K s, (forall k, k <= K -> Bt <= Xx (s + k)) ->
  exists s', s' <= s /\ Xx s' = Bt /\ (forall k, k <= K -> Bt <= Xx (s' + k)).
Proof.
  intros K s. induction s as [| s IH]; intro Hw.
  - exfalso. specialize (Hw 0 ltac:(lia)). rewrite Nat.add_0_r, fo_s_0 in Hw. lia.
  - destruct (le_lt_dec Bt (Xx s)) as [Hle | Hlt].
    + assert (Hw' : forall k, k <= K -> Bt <= Xx (s + k)).
      { intros k Hk. destruct k as [| k]; [rewrite Nat.add_0_r; exact Hle |].
        replace (s + S k) with (S s + k) by lia. apply Hw. lia. }
      destruct (IH Hw') as (s' & H1 & H2 & H3). exists s'. repeat split; auto; lia.
    + exists (S s). repeat split; [lia | | exact Hw].
      specialize (Hw 0 ltac:(lia)). rewrite Nat.add_0_r in Hw.
      destruct (fo_step M s0 s) as [[H | [H | H]] _]; lia.
Qed.

Definition fs_lA : list (am_Q M * nat * nat) := list_prod (list_prod (am_lq M) [0; 1]) [0; 1].
Definition fs_Ax (t : nat) : am_Q M * nat * nat := (fq M (Sx t), fs_par (Xx t), fp M (Sx t)).
Local Notation K1 := (length fs_lA).
Local Notation K2 := (K1 + (Bt + K1 + 2) * K1).

Lemma in01 : forall n : nat, n < 2 -> In n [0; 1].
Proof. intros n H. destruct n as [| [| n]]; [left; reflexivity | right; left; reflexivity | lia]. Qed.

Lemma fs_Ax_in : forall t, In (fs_Ax t) fs_lA.
Proof.
  intro t. unfold fs_Ax, fs_lA. apply in_prod_iff. split; [apply in_prod_iff; split |].
  - apply fo_q_in, hq0.
  - apply in01, fs_par_lt.
  - apply in01, fo_p_lt, hp0.
Qed.

Lemma orb_win : forall s, exists r1 r2, r1 < r2 /\ r2 <= K1 /\ fs_Ax (s + r1) = fs_Ax (s + r2).
Proof.
  intro s. destruct (tc2_pigeon_b _ (fs_cfg_eq M) fs_lA (fun r => fs_Ax (s + r)) (fun r _ => fs_Ax_in (s + r)))
    as (r1 & r2 & H1 & H2 & H3). exists r1, r2. auto.
Qed.

Definition fs_pump (i p g2 : nat) (d : Z) : Prop :=
  0 < p /\ (forall t, fs_nx M (Sx t) <> None) /\
  (forall t, i <= t -> Sx (t + p) = fs_shA M (2 * g2) (Sx t) /\ Dx (t + p) = (Dx t + d)%Z) /\
  (g2 = 0 \/ (0 < g2 /\ p <= K1 /\ forall t, i <= t -> Bt <= Xx t)).
(* a window of K2 + 1 consecutive steps at or above the threshold contains a pumpable cycle that never descends *)
Lemma orb_stretch : forall s,
  (forall k, k <= K2 -> Bt <= Xx (s + k)) ->
  (forall t, t <= s + K2 -> fs_nx M (Sx t) <> None) ->
  exists i p g2 d, fs_pump i p g2 d.
Proof.
  intros s Hw Hnh.
  destruct (orb_entry K2 s Hw) as (s' & Hs's & Hx' & Hw').
  destruct (orb_win s') as (r1 & r2 & Hr & Hr2 & Hax).
  assert (HK12 : K1 <= K2) by nia.
  unfold fs_Ax in Hax. injection Hax as Hq Hpar Hp.
  set (i := s' + r1) in *. set (j := s' + r2) in *. set (p := r2 - r1) in *.
  assert (Hj : j = i + p) by (unfold i, j, p; lia).
  assert (Hhi : forall t, i <= t -> t <= i + p -> Bt <= Xx t).
  { intros t H1 H2. replace t with (s' + (t - s')) by lia. apply Hw'. unfold i, p in *. lia. }
  assert (Hnh' : forall t, t <= i + p -> fs_nx M (Sx t) <> None).
  { intros t Ht. apply Hnh. unfold i, p in *. lia. }
  destruct (le_lt_dec (Xx i) (Xx j)) as [Hle | Hlt].
  - destruct (fs_par_eq _ _ Hpar) as (a & b & Ha & Hb).
    assert (Hjs : Sx (i + p) = fs_shA M (2 * (b - a)) (Sx i)).
    { rewrite <- Hj. apply fs_shA_of; [symmetry; exact Hq | symmetry; exact Hp | lia]. }
    pose proof (orb_pump_asc M s0 i p (b - a) ltac:(unfold p; lia) Hjs Hhi Hnh') as Hasc.
    exists i, p, (b - a), (Dx (i + p) - Dx i)%Z. unfold fs_pump.
    repeat split.
    + unfold p; lia.
    + intro t. destruct (le_lt_dec i t) as [Hit | Hit].
      * apply Hasc. exact Hit.
      * apply Hnh. unfold i in Hit. lia.
    + apply Hasc. exact H.
    + apply Hasc. exact H.
    + destruct (Nat.eq_dec (b - a) 0) as [Hz | Hz]; [left; exact Hz | right].
      repeat split; [lia | unfold p; lia | intros t Ht; apply Hasc; exact Ht].
  - exfalso.
    destruct (fs_par_eq _ _ Hpar) as (a & b & Ha & Hb).
    assert (Hjs : Sx i = fs_shA M (2 * (a - b)) (Sx (i + p))).
    { rewrite <- Hj. apply fs_shA_of; [exact Hq | exact Hp | lia]. }
    apply (orb_no_desc i p (a - b) ltac:(unfold p; lia) ltac:(lia) Hjs).
    intros t H1 H2. replace t with (s' + (t - s')) by lia. apply Hw'.
    assert (Hxi : Xx i <= Bt + r1).
    { pose proof (orb_x_from s' r1) as Hx. unfold i. lia. }
    assert (Hpk : p <= K1) by (unfold p; lia).
    assert (Hm : (Xx i + 2) * p <= (Bt + K1 + 2) * K1).
    { apply Nat.mul_le_mono; lia. }
    unfold i in *. nia.
Qed.


Lemma fs_shA_0 : forall (s : fcfg M), fs_shA M (2 * 0) s = s.
Proof. intros [[q x] p]. cbn [fs_shA]. rewrite Nat.mul_0_r, Nat.add_0_r. reflexivity. Qed.

Definition fs_lS : list (am_Q M * nat * nat) := list_prod (list_prod (am_lq M) (seq 0 Bt)) [0; 1].
Local Notation NS := (length fs_lS).
Local Notation LL := ((NS + 1) * (K2 + 1)).

Lemma fs_Sx_in_lS : forall t, Xx t < Bt -> In (Sx t) fs_lS.
Proof.
  intros t Ht.
  pose proof (fo_q_in M s0 t hq0) as H1. pose proof (fo_p_lt M s0 t hp0) as H3.
  unfold fs_lS. destruct (Sx t) as [[q x] p].
  unfold fq, fx, fp in *. cbn [fst snd] in *.
  apply in_prod_iff. split; [apply in_prod_iff; split |].
  - exact H1.
  - apply in_seq. lia.
  - apply in01. exact H3.
Qed.

Lemma orb_periodic : forall i p, 0 < p -> Sx (i + p) = Sx i ->
  (forall t, t < i + p -> fs_nx M (Sx t) <> None) ->
  forall t, i <= t -> Sx (t + p) = Sx t /\ Dx (t + p) = (Dx t + (Dx (i + p) - Dx i))%Z /\ fs_nx M (Sx t) <> None.
Proof.
  intros i p Hp Hs Hnh.
  assert (key : forall n t, t = i + n ->
    Sx (t + p) = Sx t /\ Dx (t + p) = (Dx t + (Dx (i + p) - Dx i))%Z /\ fs_nx M (Sx t) <> None).
  { intro n. induction n as [n IH] using lt_wf_ind. intros t Ht.
    destruct n as [| n'].
    - subst t. rewrite Nat.add_0_r. repeat split; [exact Hs | lia | apply Hnh; lia].
    - destruct (IH n' ltac:(lia) (i + n') eq_refl) as (H1 & H2 & H3).
      destruct (fs_nx M (Sx (i + n'))) as [[s' dy] |] eqn:E; [| contradiction].
      destruct (fo_S_some M s0 (i + n') s' dy E) as [E1 E2].
      assert (E3 : fs_nx M (Sx (i + n' + p)) = Some (s', dy)) by (rewrite H1; exact E).
      destruct (fo_S_some M s0 (i + n' + p) _ _ E3) as [E4 E5].
      assert (Ht1 : t = S (i + n')) by lia.
      repeat split.
      + rewrite Ht1. replace (S (i + n') + p) with (S (i + n' + p)) by lia. rewrite E4, E1. reflexivity.
      + rewrite Ht1. replace (S (i + n') + p) with (S (i + n' + p)) by lia. rewrite E5, E2. lia.
      + destruct (le_lt_dec (i + p) t) as [Hge | Hlt].
        * destruct (IH (t - p - i) ltac:(lia) (t - p) ltac:(lia)) as (K1' & _ & K3').
          replace (t - p + p) with t in K1' by lia. rewrite K1'. exact K3'.
        * apply Hnh. lia. }
  intros t Ht. apply (key (t - i) t). lia.
Qed.

Theorem orb_class :
  (exists H, fs_nx M (Sx H) = None /\ forall t, t < H -> fs_nx M (Sx t) <> None) \/
  (exists i p g2 d, fs_pump i p g2 d).
Proof.
  set (PH := fun t => fs_nx M (Sx t) = None).
  assert (PHd : forall n, {PH n} + {~ PH n}).
  { intro n. unfold PH. destruct (fs_nx M (Sx n)); [right; discriminate | left; reflexivity]. }
  destruct (tc2_bex_dec PH PHd LL) as [Hh | Hn].
  - left. destruct Hh as (t & _ & Ht).
    destruct (tc2_least PH PHd (ex_intro _ t Ht)) as (H & H1 & H2).
    exists H. split; [exact H1 | intros u Hu Hc; exact (H2 u Hu Hc)].
  - right.
    assert (Hnh : forall t, t <= LL -> fs_nx M (Sx t) <> None) by (intros t Ht Hc; exact (Hn t Ht Hc)).
    set (PW := fun s => forall k, k <= K2 -> Bt <= Xx (s + k)).
    assert (PWd : forall n, {PW n} + {~ PW n}).
    { intro n. unfold PW.
      destruct (tc2_ball_dec (fun k => Bt <= Xx (n + k)) (fun k => le_dec Bt (Xx (n + k))) K2) as [H | H];
        [left; exact H | right; intro Hc; destruct H as (k & Hk & Hnk); exact (Hnk (Hc k Hk))]. }
    assert (HLK : K2 + 1 <= LL) by nia.
    destruct (tc2_bex_dec PW PWd (LL - K2)) as [Hw | Hnw].
    + destruct Hw as (s & Hs & Hpw).
      apply (orb_stretch s Hpw). intros t Ht. apply Hnh. lia.
    + set (sel := fun r k => Nat.ltb (Xx (r * (K2 + 1) + k)) Bt).
      set (tsel := fun r => r * (K2 + 1) + tc2_pick K2 (sel r)).
      assert (Hsel : forall r, r <= NS -> tc2_pick K2 (sel r) <= K2 /\ Xx (tsel r) < Bt).
      { intros r Hr.
        assert (Hrs : r * (K2 + 1) <= LL - K2).
        { assert (r * (K2 + 1) <= NS * (K2 + 1)) by (apply Nat.mul_le_mono_r; lia). nia. }
        assert (Hex : exists k, k <= K2 /\ sel r k = true).
        { destruct (tc2_ball_dec (fun k => Bt <= Xx (r * (K2 + 1) + k)) (fun k => le_dec Bt (Xx (r * (K2 + 1) + k))) K2)
            as [H | (k & Hk & Hnk)].
          - exfalso. exact (Hnw (r * (K2 + 1)) Hrs H).
          - exists k. split; [exact Hk |]. unfold sel. apply Nat.ltb_lt. lia. }
        destruct (tc2_pick_spec K2 (sel r) Hex) as [H1 H2]. split; [exact H1 |].
        unfold tsel. unfold sel in H2. apply Nat.ltb_lt in H2. exact H2. }
      destruct (tc2_pigeon_b _ (fs_cfg_eq M) fs_lS (fun r => Sx (tsel r))
                  (fun r Hr => fs_Sx_in_lS (tsel r) (proj2 (Hsel r Hr)))) as (r1 & r2 & Hr & Hr2 & Heq).
      set (i := tsel r1) in *. set (j := tsel r2) in *.
      destruct (Hsel r1 ltac:(lia)) as [Hk1 _]. destruct (Hsel r2 ltac:(lia)) as [Hk2 _].
      assert (Hij : i < j).
      { unfold i, j, tsel. assert ((r1 + 1) * (K2 + 1) <= r2 * (K2 + 1)) by (apply Nat.mul_le_mono_r; lia). nia. }
      assert (Hjb : j < LL).
      { unfold j, tsel. assert (r2 * (K2 + 1) <= NS * (K2 + 1)) by (apply Nat.mul_le_mono_r; lia). nia. }
      set (p := j - i).
      assert (Hji : j = i + p) by (unfold p; lia).
      assert (Hper : Sx (i + p) = Sx i) by (rewrite <- Hji; symmetry; exact Heq).
      assert (Hnh2 : forall t, t < i + p -> fs_nx M (Sx t) <> None) by (intros t Ht; apply Hnh; lia).
      pose proof (orb_periodic i p ltac:(unfold p; lia) Hper Hnh2) as Hpr.
      exists i, p, 0, (Dx (i + p) - Dx i)%Z. unfold fs_pump. repeat split.
      * unfold p; lia.
      * intro t. destruct (le_lt_dec i t) as [Hit | Hit].
        -- apply Hpr. exact Hit.
        -- apply Hnh. lia.
      * rewrite fs_shA_0. destruct (Hpr t H) as (X1 & _ & _). exact X1.
      * destruct (Hpr t H) as (_ & X2 & _). exact X2.
      * left. reflexivity.
Qed.

End Orb2.

Print Assumptions orb_class.
