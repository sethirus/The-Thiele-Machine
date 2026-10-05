(** TimeTax2.v: the time tax on the small machine.

    The exchange is time bought with ledger: a blind search that pays
    nothing and takes many moves, a sighted search that pays a constant
    ledger and takes few. On the small machine the blind side is a lower
    bound over every program, not one program.

    The question. Is counter A at least m? Two ways to find out.

      Free. Base moves only (INC, DEC, and falling off the end). They cost
      nothing. But a base move reads A one unit at a time: a DEC takes a
      unit off A or finds it empty. After n moves, a run that started with A
      at least n has never seen A empty, so it behaves identically for every
      such A, up to a constant shift in A itself.
      [ent2_free_run_shift]. Hence no free program of fewer than m moves
      tells A = m - 1 from A = m [ent2_free_cannot_decide_fast], and the
      ladder of m DECs decides in exactly m moves [ent2_ladder_decides], on
      the machine itself [ent2_machine_free_cannot_decide,
      ent2_machine_ladder_decides, ent2_ladder_free].

      Paid. CHECK "A >= m", COMMIT it, CERTIFY. Three moves and a ledger of
      3, whatever m is, and the record is up exactly when A >= m
      [ent2_chain_decides].

    So the exchange, for any price lambda of a ledger unit in moves: the
    paid route costs 3 + 3 lambda, the free route costs at least m, and the
    paid route is cheaper exactly when 3 + 3 lambda < m
    [ent2_time_tax]. No free program does better than the ladder; the
    blind side is not a choice of program.

    The paid side is constant (the earned chain, exactly 3) and the free
    side is linear in the number asked about (exactly m). The k-dimensional
    counts (N^k blind against k N factored) are arithmetic on formulas;
    the ones that carry content are cost-model lemmas below
    [ent2_tax_pow_ge, ent2_tax_pow_gap, ent2_tax_ratio_grows,
    ent2_tax_last_saves_zero, ent2_tax_sighted_wins,
    ent2_tax_sighted_loses_at_zero]; they say nothing about any machine
    until a machine realizes the counts.

    Limits. The lower bound is for the INC/DEC fragment of this machine
    (programs that make no record move); a machine with a base move that
    changes a counter by more than one unit per move is a different machine
    and the bound does not speak for it. The paid route certifies and the
    free route decides into the program counter; the comparison is of two
    ways to answer the same question, not of two certifications.

    Dependencies: Coq standard library and EarnedCore.v. No axioms and no
    unfinished proofs.                                                             *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.EarnedCore.
Module E := Minimal.EarnedCore.

(* ================================================================= *)
(* 1. A free run reads A one unit at a time.                          *)
(* ================================================================= *)

(* Two counter-machine configurations alike except that A differs by a
   fixed amount: (pc, (a, b)) and (pc, (a', b)) with a + e1 = a' + e0. *)
Definition ent2_rel (e0 e1 : nat) (x x' : E.mconf) : Prop :=
  fst x = fst x' /\ snd (snd x) = snd (snd x') /\ fst (snd x) + e1 = fst (snd x') + e0.

(* One move from two configurations alike except for the size of A, both
   with at least n >= 1 in A: both halt, or both move and stay alike with
   at least n - 1 in A. *)
Lemma ent2_step_rel : forall M e0 e1 x x' n,
  1 <= n -> n <= fst (snd x) -> n <= fst (snd x') -> ent2_rel e0 e1 x x' ->
  (E.mstep M x = None /\ E.mstep M x' = None) \/
  exists y y', E.mstep M x = Some y /\ E.mstep M x' = Some y' /\ ent2_rel e0 e1 y y' /\
    n - 1 <= fst (snd y) /\ n - 1 <= fst (snd y').
Proof.
  intros M e0 e1 [p [a b]] [p' [a' b']] n Hn Hx Hx' [Hp [Hb Ha]].
  simpl in *. subst p' b'. unfold E.mstep. simpl.
  destruct (E.fetch M p) as [[c | c j] |].
  - right. destruct c; simpl; eexists; eexists; repeat split; try reflexivity; simpl; lia.
  - right. destruct c; simpl.
    + destruct a as [| a0]; [lia |]. destruct a' as [| a0']; [lia |].
      eexists; eexists; repeat split; try reflexivity; simpl; lia.
    + destruct b as [| b0]; eexists; eexists; repeat split; try reflexivity; simpl; lia.
  - left. split; reflexivity.
Qed.

(* A run of n moves from two configurations alike except for the size of
   A, both with at least n in A, keeps them alike. *)
Theorem ent2_free_run_shift : forall M n e0 e1 x x',
  n <= fst (snd x) -> n <= fst (snd x') -> ent2_rel e0 e1 x x' ->
  ent2_rel e0 e1 (E.mrun n M x) (E.mrun n M x').
Proof.
  intros M n. induction n as [| n IH]; intros e0 e1 x x' Hx Hx' Hr; simpl; [exact Hr |].
  destruct (ent2_step_rel M e0 e1 x x' (S n) ltac:(lia) Hx Hx' Hr)
    as [[H1 H2] | [y [y' [H1 [H2 [Hr' [Hy Hy']]]]]]].
  - rewrite H1, H2. exact Hr.
  - rewrite H1, H2. apply IH; [| | exact Hr']; lia.
Qed.

(* The consequence in plain words. From A = a and A = a', both at least n,
   n moves leave the same program counter and the same B, and A shifted by
   the same amount it started shifted by. *)
Corollary ent2_free_same_view : forall M n a a' b,
  n <= a -> n <= a' ->
  fst (E.mrun n M (1, (a, b))) = fst (E.mrun n M (1, (a', b))) /\
  snd (snd (E.mrun n M (1, (a, b)))) = snd (snd (E.mrun n M (1, (a', b)))).
Proof.
  intros M n a a' b Ha Ha'.
  destruct (ent2_free_run_shift M n a a' (1, (a, b)) (1, (a', b)) Ha Ha'
              (conj eq_refl (conj eq_refl (Nat.add_comm a a')))) as [H1 [H2 _]].
  split; assumption.
Qed.

(* Deciding "A >= m" from the program counter and B after n moves. *)
Definition ent2_decides (M : list E.minsky) (n m : nat) : Prop :=
  exists f : nat * nat -> bool, forall a b,
    f (fst (E.mrun n M (1, (a, b))), snd (snd (E.mrun n M (1, (a, b))))) = Nat.leb m a.

(* No free program of fewer than m moves decides whether A is at least m. *)
Theorem ent2_free_cannot_decide_fast : forall M n m, n < m -> ~ ent2_decides M n m.
Proof.
  intros M n m Hn [f Hf].
  destruct (ent2_free_same_view M n (m - 1) m 0 ltac:(lia) ltac:(lia)) as [H1 H2].
  pose proof (Hf (m - 1) 0) as E1. pose proof (Hf m 0) as E2.
  rewrite H1, H2 in E1. rewrite E1 in E2.
  assert (Nat.leb m (m - 1) = false) by (apply Nat.leb_gt; lia).
  assert (Nat.leb m m = true) by (apply Nat.leb_le; lia). congruence.
Qed.

(* ================================================================= *)
(* 2. The ladder decides in exactly m moves.                          *)
(* ================================================================= *)

(* Pair i (counting from 0) sits at program counters 2i+1 and 2i+2:
   "DEC A, and on success go to the next pair", then "INC B". A success
   skips the INC B; a failure falls through to it. *)
Fixpoint ent2_ladder (m : nat) : list E.minsky :=
  match m with
  | 0 => []
  | S k => ent2_ladder k ++ [E.MDEC E.CA (2 * k + 3); E.MINC E.CB]
  end.

Lemma ent2_ladder_length : forall m, length (ent2_ladder m) = 2 * m.
Proof. induction m; simpl; [reflexivity | rewrite app_length, IHm; simpl; lia]. Qed.

Lemma ent2_ladder_nth : forall m i, i < m ->
  nth_error (ent2_ladder m) (2 * i) = Some (E.MDEC E.CA (2 * i + 3)) /\
  nth_error (ent2_ladder m) (2 * i + 1) = Some (E.MINC E.CB).
Proof.
  induction m as [| m IH]; intros i Hi; [lia |].
  simpl ent2_ladder.
  destruct (Nat.lt_ge_cases i m) as [Hlt | Hge].
  - destruct (IH i Hlt) as [H1 H2].
    rewrite !nth_error_app1 by (rewrite ent2_ladder_length; lia). split; assumption.
  - assert (i = m) by lia. subst i.
    rewrite !nth_error_app2 by (rewrite ent2_ladder_length; lia).
    rewrite ent2_ladder_length.
    replace (2 * m - 2 * m) with 0 by lia.
    replace (2 * m + 1 - 2 * m) with 1 by lia. simpl. split; reflexivity.
Qed.

Lemma ent2_ladder_fetch : forall m i, i < m ->
  E.fetch (ent2_ladder m) (2 * i + 1) = Some (E.MDEC E.CA (2 * i + 3)) /\
  E.fetch (ent2_ladder m) (2 * i + 2) = Some (E.MINC E.CB).
Proof.
  intros m i Hi. destruct (ent2_ladder_nth m i Hi) as [H1 H2].
  replace (2 * i + 1) with (S (2 * i)) by lia.
  replace (2 * i + 2) with (S (2 * i + 1)) by lia.
  split; assumption.
Qed.

(* Every program counter from 1 to 2m holds an instruction. *)
Lemma ent2_ladder_fetch_some : forall m p, 1 <= p -> p <= 2 * m ->
  exists i, E.fetch (ent2_ladder m) p = Some i.
Proof.
  intros m p H1 H2.
  destruct (Nat.Even_or_Odd p) as [[q Hq] | [q Hq]].
  - destruct (ent2_ladder_fetch m (q - 1) ltac:(lia)) as [_ H].
    replace (2 * (q - 1) + 2) with p in H by lia. eexists; exact H.
  - assert (Hq' : q < m) by lia.
    destruct (ent2_ladder_fetch m q Hq') as [H _].
    replace (2 * q + 1) with p in H by lia. eexists; exact H.
Qed.

(* Counter-machine runs add. *)
Lemma ent2_mrun_stuck : forall n M x, E.mstep M x = None -> E.mrun n M x = x.
Proof. induction n; intros M x H; simpl; [reflexivity | rewrite H; reflexivity]. Qed.

Lemma ent2_mrun_add : forall n1 n2 M x,
  E.mrun (n1 + n2) M x = E.mrun n2 M (E.mrun n1 M x).
Proof.
  induction n1 as [| n1 IH]; intros n2 M x; simpl; [reflexivity |].
  destruct (E.mstep M x) as [y |] eqn:H; [apply IH |].
  rewrite ent2_mrun_stuck by exact H. reflexivity.
Qed.

(* Success: j moves from pair i consume j units of A and land at pair i+j. *)
Lemma ent2_ladder_climb : forall m j i a b,
  i + j <= m -> j <= a ->
  E.mrun j (ent2_ladder m) (2 * i + 1, (a, b)) = (2 * (i + j) + 1, (a - j, b)).
Proof.
  intros m j. induction j as [| j IH]; intros i a b Hm Ha.
  - cbn [E.mrun]. replace (i + 0) with i by lia. rewrite Nat.sub_0_r. reflexivity.
  - cbn [E.mrun].
    destruct (ent2_ladder_fetch m i ltac:(lia)) as [H1 _].
    unfold E.mstep. cbn [fst snd]. rewrite H1. cbn [E.mval fst snd].
    destruct a as [| a0]; [lia |]. cbn [E.mset fst snd].
    replace (2 * i + 3) with (2 * S i + 1) by lia.
    rewrite (IH (S i) a0 b ltac:(lia) ltac:(lia)).
    replace (2 * (S i + j) + 1) with (2 * (i + S j) + 1) by lia.
    replace (a0 - j) with (S a0 - S j) by lia. reflexivity.
Qed.

(* Failure: with A empty every move goes to the next program counter. *)
Lemma ent2_ladder_fail : forall m t p b,
  1 <= p -> p + t <= 2 * m + 1 ->
  exists b', E.mrun t (ent2_ladder m) (p, (0, b)) = (p + t, (0, b')).
Proof.
  intros m t. induction t as [| t IH]; intros p b H1 H2.
  - exists b. cbn [E.mrun]. rewrite Nat.add_0_r. reflexivity.
  - destruct (Nat.Even_or_Odd p) as [[q Hq] | [q Hq]].
    + destruct (ent2_ladder_fetch m (q - 1) ltac:(lia)) as [_ Hf].
      replace (2 * (q - 1) + 2) with p in Hf by lia.
      destruct (IH (S p) (S b) ltac:(lia) ltac:(lia)) as [b' Hb'].
      exists b'. cbn [E.mrun]. unfold E.mstep. cbn [fst snd]. rewrite Hf.
      cbn [E.mval E.mset fst snd]. rewrite Hb'. replace (S p + t) with (p + S t) by lia.
      reflexivity.
    + destruct (ent2_ladder_fetch m q ltac:(lia)) as [Hf _].
      replace (2 * q + 1) with p in Hf by lia.
      destruct (IH (S p) b ltac:(lia) ltac:(lia)) as [b' Hb'].
      exists b'. cbn [E.mrun]. unfold E.mstep. cbn [fst snd]. rewrite Hf.
      cbn [E.mval E.mset fst snd]. rewrite Hb'. replace (S p + t) with (p + S t) by lia.
      reflexivity.
Qed.

(* After m moves, the program counter is 2m + 1 exactly when A >= m. *)
Theorem ent2_ladder_decides : forall m a b,
  (fst (E.mrun m (ent2_ladder m) (1, (a, b))) = 2 * m + 1 <-> m <= a) /\
  (m <= a -> E.mrun m (ent2_ladder m) (1, (a, b)) = (2 * m + 1, (a - m, b))).
Proof.
  intros m a b.
  assert (Hclimb : m <= a -> E.mrun m (ent2_ladder m) (1, (a, b)) = (2 * m + 1, (a - m, b))).
  { intro Hma. pose proof (ent2_ladder_climb m m 0 a b ltac:(lia) Hma) as H.
    replace (2 * (0 + m) + 1) with (2 * m + 1) in H by lia.
    replace (2 * 0 + 1) with 1 in H by lia. exact H. }
  split; [| exact Hclimb]. split.
  - intro Hp. destruct (Nat.le_gt_cases m a) as [Hle | Hlt]; [exact Hle |].
    exfalso.
    assert (Hs : E.mrun m (ent2_ladder m) (1, (a, b)) =
                 E.mrun (m - a) (ent2_ladder m) (E.mrun a (ent2_ladder m) (1, (a, b)))).
    { rewrite <- ent2_mrun_add. f_equal. lia. }
    rewrite Hs in Hp.
    pose proof (ent2_ladder_climb m a 0 a b ltac:(lia) ltac:(lia)) as Hc.
    replace (2 * (0 + a) + 1) with (2 * a + 1) in Hc by lia.
    replace (2 * 0 + 1) with 1 in Hc by lia. rewrite Nat.sub_diag in Hc.
    rewrite Hc in Hp.
    destruct (ent2_ladder_fail m (m - a) (2 * a + 1) b ltac:(lia) ltac:(lia)) as [b' Hb'].
    rewrite Hb' in Hp. simpl in Hp. lia.
  - intro Hma. rewrite (Hclimb Hma). reflexivity.
Qed.

(* So the ladder decides "A >= m" in m moves, from the program counter. *)
Corollary ent2_ladder_decides_in_m : forall m, ent2_decides (ent2_ladder m) m m.
Proof.
  intro m.
  exists (fun pb => Nat.eqb (fst pb) (2 * m + 1)). intros a b. simpl.
  destruct (ent2_ladder_decides m a b) as [H _].
  destruct (Nat.leb m a) eqn:E1.
  - apply Nat.leb_le in E1. apply Nat.eqb_eq. apply H. exact E1.
  - apply Nat.leb_gt in E1. apply Nat.eqb_neq. intro Hp. apply H in Hp. lia.
Qed.

(* ================================================================= *)
(* 3. The same on the small machine.                                  *)
(* ================================================================= *)

(* The run of the compiled program, window and ledger. *)
Lemma ent2_machine_window : forall M n a b,
  E.window (E.core_of (E.run_prog n (E.compile M) (E.start a b))) = E.mrun n M (1, (a, b)).
Proof.
  intros M n a b. rewrite E.core_run_prog.
  exact (proj1 (E.simulation_run n M (E.start_core a b) eq_refl)).
Qed.

Lemma ent2_fetch_in : forall (P : list E.instr) n j, E.fetch P n = Some j -> In j P.
Proof.
  intros P [| q] j H; simpl in H; [discriminate |]. eapply nth_error_In; exact H.
Qed.

Lemma ent2_next_in : forall P k i, E.next_instr P k = Some i -> In i P.
Proof.
  intros P k i H. unfold E.next_instr in H.
  destruct (E.err k); [discriminate |].
  destruct (E.fetch P (E.pc k)) as [j |] eqn:Hf; [| discriminate].
  apply ent2_fetch_in in Hf. destruct j; try discriminate H; injection H as <-; exact Hf.
Qed.

(* A compiled program has only INC and DEC, which cost nothing, so its
   ledger never moves. *)
Lemma ent2_compile_free : forall M n s,
  E.mu (E.run_prog n (E.compile M) s) = E.mu s.
Proof.
  intros M n. induction n as [| n IH]; intro s; simpl; [reflexivity |].
  rewrite IH. unfold E.step.
  destruct (E.next_instr (E.compile M) (E.core_of s)) as [i |] eqn:Hn; [| reflexivity].
  apply ent2_next_in in Hn. unfold E.compile in Hn.
  apply in_map_iff in Hn as [m [<- _]].
  destruct m; simpl; lia.
Qed.

(* Deciding "A >= m" on the machine itself, from the program counter and B
   after n moves of a free program. *)
Definition ent2_machine_decides (M : list E.minsky) (n m : nat) : Prop :=
  exists f : nat * nat -> bool, forall a b,
    f (E.pc (E.core_of (E.run_prog n (E.compile M) (E.start a b))),
       E.cb (E.core_of (E.run_prog n (E.compile M) (E.start a b)))) = Nat.leb m a.

Theorem ent2_machine_free_cannot_decide : forall M n m, n < m -> ~ ent2_machine_decides M n m.
Proof.
  intros M n m Hn [f Hf]. apply (ent2_free_cannot_decide_fast M n m Hn).
  exists f. intros a b. specialize (Hf a b).
  pose proof (ent2_machine_window M n a b) as H. unfold E.window in H.
  rewrite <- H. simpl. exact Hf.
Qed.

Theorem ent2_machine_ladder_decides : forall m,
  ent2_machine_decides (ent2_ladder m) m m.
Proof.
  intro m. destruct (ent2_ladder_decides_in_m m) as [f Hf]. exists f. intros a b.
  specialize (Hf a b).
  pose proof (ent2_machine_window (ent2_ladder m) m a b) as H. unfold E.window in H.
  rewrite <- H in Hf. exact Hf.
Qed.

(* The ladder is free. *)
Theorem ent2_ladder_free : forall m n a b,
  E.mu (E.run_prog n (E.compile (ent2_ladder m)) (E.start a b)) = 0.
Proof. intros. rewrite ent2_compile_free. reflexivity. Qed.

(* ================================================================= *)
(* 4. The paid route.                                                 *)
(* ================================================================= *)

Definition ent2_chain (m : nat) : list E.instr :=
  [E.CHECK (E.PGe m) E.CA; E.COMMIT (E.PGe m) E.CA; E.CERTIFY].

(* Three moves, a ledger of exactly 3 whatever m is, and the record is up
   exactly when A >= m. *)
Theorem ent2_chain_decides : forall m a b,
  E.cert (E.run (ent2_chain m) (E.start a b)) = Nat.leb m a /\
  E.mu (E.run (ent2_chain m) (E.start a b)) = 3 /\
  length (ent2_chain m) = 3.
Proof.
  intros m a b. split; [| split; [| reflexivity]].
  - unfold ent2_chain. destruct (Nat.leb m a) eqn:H.
    + simpl. unfold E.cexec, E.check_ok. simpl. rewrite H. simpl.
      unfold E.commit_ok, E.fact_eqb. simpl. rewrite Nat.eqb_refl. simpl.
      unfold E.certify_ok. simpl. reflexivity.
    + simpl. unfold E.cexec, E.check_ok. simpl. rewrite H. simpl. reflexivity.
  - rewrite E.mu_conservation_trace. reflexivity.
Qed.

(* ================================================================= *)
(* 5. The exchange.                                                   *)
(* ================================================================= *)

(* THE TIME TAX. For every m and every price lambda of one ledger unit in
   moves:
   (1) no free program of fewer than m moves decides whether A >= m;
   (2) the ladder decides it in exactly m moves, at ledger 0;
   (3) the three-move chain certifies it at ledger exactly 3, and the
       record is up exactly when A >= m;
   (4) the chain's total, 3 + 3 lambda, is below the free route's, m,
       exactly when 3 + 3 lambda < m. *)
Theorem ent2_time_tax : forall m lambda,
  (forall M n, n < m -> ~ ent2_machine_decides M n m) /\
  (ent2_machine_decides (ent2_ladder m) m m /\
   forall n a b, E.mu (E.run_prog n (E.compile (ent2_ladder m)) (E.start a b)) = 0) /\
  (forall a b, E.cert (E.run (ent2_chain m) (E.start a b)) = Nat.leb m a /\
               E.mu (E.run (ent2_chain m) (E.start a b)) = 3) /\
  (length (ent2_chain m) + lambda * 3 < m + lambda * 0 <-> 3 + 3 * lambda < m).
Proof.
  intros m lambda. split; [exact (fun M n H => ent2_machine_free_cannot_decide M n m H) |].
  split; [split; [apply ent2_machine_ladder_decides | intros; apply ent2_ladder_free] |].
  split; [intros a b; destruct (ent2_chain_decides m a b) as [H1 [H2 _]]; auto |].
  simpl length. lia.
Qed.

(* The old file also priced certificate strength (a longer formula cost more
   bits) and found the step count unchanged. Here the premium is zero for
   every claim: the three record moves cost exactly 1 each, whatever the
   property or the counter, and the chain of any claim is three moves. *)
Theorem ent2_claim_strength_free : forall p c,
  E.total_cost [E.CHECK p c; E.COMMIT p c; E.CERTIFY] = 3.
Proof. reflexivity. Qed.

(* ================================================================= *)
(* 6. The cost-model arithmetic of the old file.                      *)
(* ================================================================= *)

(* A search through k dimensions of size N costs N^k moves blind and k N
   moves with each dimension asked separately. These are facts about the
   formulas. *)

Theorem ent2_tax_pow_ge : forall N k, 2 <= N -> 1 <= k -> k * N <= N ^ k.
Proof.
  intros N k HN Hk. induction k as [| k IH]; [lia |].
  destruct k as [| k']; [simpl; lia |].
  assert (IH' : S k' * N <= N ^ S k') by (apply IH; lia).
  rewrite (Nat.pow_succ_r' N (S k')). nia.
Qed.

Theorem ent2_tax_pow_gap : forall N k, 4 <= N -> 2 <= k -> k * N + k < N ^ k.
Proof.
  intros N k HN. induction k as [| k IH]; intro Hk; [lia |].
  destruct k as [| k']; [lia |]. destruct k' as [| k''].
  - simpl. nia.
  - assert (IH' : S (S k'') * N + S (S k'') < N ^ S (S k'')) by (apply IH; lia).
    rewrite (Nat.pow_succ_r' N (S (S k''))). nia.
Qed.

Theorem ent2_tax_ratio_grows : forall N k, 2 <= N -> 2 <= k -> N ^ (k + 1) * k > N ^ k * (k + 1).
Proof.
  intros N k HN Hk.
  assert (Hge : 1 <= N ^ k) by (pose proof (Nat.pow_nonzero N k ltac:(lia)); lia).
  assert (Hpow : N ^ (k + 1) = N * N ^ k)
    by (replace (k + 1) with (S k) by lia; apply Nat.pow_succ_r').
  rewrite Hpow. nia.
Qed.

(* The last dimension certified saves nothing. *)
Theorem ent2_tax_last_saves_zero : forall N k, 1 <= k -> (k - 1) * N + N = k * N.
Proof. intros N k Hk. nia. Qed.

(* On an N by N grid with the target at row L, the factored search beats
   the blind one at every row but the first. *)
Theorem ent2_tax_sighted_wins : forall N L R, 3 <= N -> 1 <= L -> L + R + 2 < L * N + R + 1.
Proof. intros N L R HN HL. nia. Qed.

Theorem ent2_tax_sighted_loses_at_zero : forall N R, 0 * N + R + 1 < 0 + R + 2.
Proof. intros N R. lia. Qed.

(* ================================================================= *)
(* Assumption audit.                                                  *)
(* ================================================================= *)

Print Assumptions ent2_free_run_shift.
Print Assumptions ent2_free_same_view.
Print Assumptions ent2_free_cannot_decide_fast.
Print Assumptions ent2_ladder_decides.
Print Assumptions ent2_ladder_decides_in_m.
Print Assumptions ent2_compile_free.
Print Assumptions ent2_machine_free_cannot_decide.
Print Assumptions ent2_machine_ladder_decides.
Print Assumptions ent2_ladder_free.
Print Assumptions ent2_chain_decides.
Print Assumptions ent2_time_tax.
Print Assumptions ent2_claim_strength_free.
Print Assumptions ent2_tax_pow_ge.
Print Assumptions ent2_tax_pow_gap.
Print Assumptions ent2_tax_ratio_grows.
Print Assumptions ent2_tax_last_saves_zero.
Print Assumptions ent2_tax_sighted_wins.
Print Assumptions ent2_tax_sighted_loses_at_zero.
