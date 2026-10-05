(* ================================================================= *)
(* The invariant at HEAD, and the three phases.                        *)
(* ================================================================= *)

(* The guest's registers at the start: S holds the code of s0. *)
Definition cg_e0 (s0 : st) : env nat nat := fun y => if Nat.eqb y 0 then sc s0 else 0.

Lemma cg_e0_rf : forall s0, cg_eqv (cg_e0 s0) (cg_rf (sc s0) 0 0 0 0 0 0 0).
Proof. intros s0 y. unfold cg_e0. cg_rf_tac. Qed.

Lemma cg_e0_high : forall s0 y, cg_k <= y -> cg_e0 s0 y = 0.
Proof. intros s0 y H. rewrite cg_e0_rf. apply cg_rf_high. exact H. Qed.

(* inv_head n: S holds the code of the state after n driven steps, E the
   latch bit, every other register 0; the record is (ledger + surcharge,
   latch, latch). *)
Definition cg_inv_head (s0 : st) (n : nat) (x : cg_xstate) : Prop :=
  cg_eqv (fst x) (cg_rf (sc (presented_run M s0 n)) 0 0 0 0 0
                    (if mlatch M s0 n then 1 else 0) 0) /\
  snd x = cg_mkaux (mledger M s0 n + surcharge M s0 n) (mlatch M s0 n) (mlatch M s0 n).

Theorem cg_x_prologue : forall s0,
  exists x, cg_inv_head s0 0 x /\ Xp (1, cg_xstart (cg_e0 s0)) (2, x).
Proof.
  intros s0.
  destruct (cg_x_check s0 0 false 0 (cg_e0 s0) (cg_e0_rf s0)) as (e' & He' & H).
  destruct (cg_account_start M s0) as [Hl Ha].
  exists (e', cg_mkaux (0 + cg_chk_pay false (rd s0) 0) (false || rd s0) (false || rd s0)).
  split; [split |].
  - cbn [fst presented_run]. rewrite Hl. exact He'.
  - cbn [snd]. rewrite Hl, Ha. reflexivity.
  - eapply sss_progress_trans; [| exact H].
    apply cg_x_dec0 with (x := 8); [exact cg_sc_jmp0 | cg_get (cg_e0_rf s0)].
Qed.

Theorem cg_x_step : forall s0 n x i,
  cg_inv_head s0 n x -> pm_next M (presented_run M s0 n) = Some i ->
  exists x', cg_inv_head s0 (S n) x' /\ Xp (2, x) (2, x').
Proof.
  intros s0 n [e a] i [He Ha] Hn. cbn [fst snd] in He, Ha. subst a.
  destruct (cg_x_move _ i _ e (cg_mkaux (mledger M s0 n + surcharge M s0 n)
              (mlatch M s0 n) (mlatch M s0 n)) He Hn) as (e1 & He1 & H1).
  destruct (cg_x_check (cstep (presented_run M s0 n) i) (ccost i) (mlatch M s0 n)
              (mledger M s0 n + surcharge M s0 n) e1 He1) as (e2 & He2 & H2).
  destruct (cg_account_step M s0 n i Hn) as (Hr & Hl & Ha).
  eexists. split; [split |].
  - cbn [fst]. rewrite Hr, Hl. exact He2.
  - cbn [snd]. rewrite Hl, Ha. reflexivity.
  - eapply sss_progress_trans; [exact H1 | exact H2].
Qed.

Theorem cg_x_stop : forall s0 n x,
  cg_inv_head s0 n x -> pm_next M (presented_run M s0 n) = None ->
  exists x', cg_inv_head s0 n x' /\ Xp (2, x) (cg_HALTB, x').
Proof.
  intros s0 n [e a] [He Ha] Hn. cbn [fst snd] in He, Ha.
  destruct (cg_x_halt _ _ e a He Hn) as (e1 & He1 & H1).
  exists (e1, a). split; [split; [exact He1 | exact Ha] | exact H1].
Qed.

