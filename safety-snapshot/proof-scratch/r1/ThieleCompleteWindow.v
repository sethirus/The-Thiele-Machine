(** ThieleCompleteWindow.v: every Thiele-complete machine hides its record
    and its ledger from its own base window.

    The window is the one ThieleComplete.v's definition names: the
    universal base's ub_window, the two-counter view (pc, (A, B)) of a
    state. The results hold for every machine M and every interface I that
    witnesses thiele_complete M, so they are consequences of the
    definition, not facts about one machine.

      1. Every window is printed for free. For any state s at all, there is
         a clean start and one base move (cost 0) that ends in a state
         showing the same window as s, with the record down and the ledger
         where the clean start left it [complete_every_window_printed]. The
         start is the loaded state (pc 1, (x + 1, y)) and the move is the
         compiled counter instruction "decrement A, jump to pc".
      2. Same start, same window, different ledger. There is a clean start
         and two runs from it that end showing the same window, one the
         certified run of some_run_certifies, the other made of base moves
         only; the first ledger is at least 3 above the second
         [complete_hides_ledger].
      3. Same start, same window, different record. The same two runs: the
         record is up after the first and down after the second
         [complete_hides_record].
      4. Hence no function of the window gives the ledger, and none gives
         the record, even on runs from clean starts alone
         [complete_no_ledger_oracle, complete_no_record_oracle], and every
         candidate function is refuted by a specific run
         [complete_ledger_oracle_fails, complete_record_oracle_fails].
      5. The same, stated per machine [thiele_complete_hides].

    Only the base clause, the clean-start clause, the exact toll and the
    two existing consequences some_run_certifies and certificate_costs_three
    are used. Of universality, only the fact that each compiled instruction
    acts on the window as the instruction acts on a configuration is used.

    Dependencies: Coq standard library and ThieleComplete.v. No axioms, no
    Admitted.                                                              *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Minimal.ThieleComplete.

(* ================================================================= *)
(* The window, and runs of counter instructions on configurations.   *)
(* ================================================================= *)

(* The base window of a state, as the interface's universal base reads it. *)
Definition window {M : machine} (I : thiele_interface M) (s : m_state M) : cm_conf :=
  ub_window (ti_base I) s.

(* Running a list of counter instructions on a configuration, with no
   program counter lookup: each instruction is applied in turn. *)
Definition cm_runl (is : list cm_instr) (x : cm_conf) : cm_conf :=
  fold_left (fun y i => cm_exec i y) is x.

Lemma cm_dec_a_to_zero : forall u p v,
  exists p', cm_runl (repeat (CDEC RA 1) u) (p, (u, v)) = (p', (0, v)).
Proof.
  induction u as [| u IH]; intros p v; [exists p; reflexivity |].
  destruct (IH 1 v) as [p' H]. exists p'. exact H.
Qed.

Lemma cm_dec_b_to_zero : forall u p a,
  exists p', cm_runl (repeat (CDEC RB 1) u) (p, (a, u)) = (p', (a, 0)).
Proof.
  induction u as [| u IH]; intros p a; [exists p; reflexivity |].
  destruct (IH 1 a) as [p' H]. exists p'. exact H.
Qed.

Lemma cm_inc_a : forall n p u v,
  exists p', cm_runl (repeat (CINC RA) n) (p, (u, v)) = (p', (u + n, v)).
Proof.
  induction n as [| n IH]; intros p u v; [exists p; rewrite Nat.add_0_r; reflexivity |].
  destruct (IH (S p) (S u) v) as [p' H]. exists p'.
  replace (u + S n) with (S u + n) by lia. exact H.
Qed.

Lemma cm_inc_b : forall n p a u,
  exists p', cm_runl (repeat (CINC RB) n) (p, (a, u)) = (p', (a, u + n)).
Proof.
  induction n as [| n IH]; intros p a u; [exists p; rewrite Nat.add_0_r; reflexivity |].
  destruct (IH (S p) a (S u)) as [p' H]. exists p'.
  replace (u + S n) with (S u + n) by lia. exact H.
Qed.

(* From any configuration, some list of counter instructions reaches any
   chosen configuration. *)
Lemma cm_reach : forall w pc x y, exists is, cm_runl is w = (pc, (x, y)).
Proof.
  intros [p [u v]] pc x y.
  exists (repeat (CDEC RA 1) u ++ repeat (CINC RA) (S x) ++
          repeat (CDEC RB 1) v ++ repeat (CINC RB) y ++ [CDEC RA pc]).
  unfold cm_runl. rewrite !fold_left_app.
  destruct (cm_dec_a_to_zero u p v) as [p1 H1]. unfold cm_runl in H1. rewrite H1.
  destruct (cm_inc_a (S x) p1 0 v) as [p2 H2]. unfold cm_runl in H2. rewrite H2.
  destruct (cm_dec_b_to_zero v p2 (0 + S x)) as [p3 H3]. unfold cm_runl in H3. rewrite H3.
  destruct (cm_inc_b y p3 (0 + S x) 0) as [p4 H4]. unfold cm_runl in H4. rewrite H4.
  reflexivity.
Qed.

(* ================================================================= *)
(* Base runs on a Thiele-complete machine.                           *)
(* ================================================================= *)

Section Window.

Variable M : machine.
Variable I : thiele_interface M.
Hypothesis HC : thiele_complete_with I.

(* A run of compiled base moves acts on the window as the counter
   instructions act on the configuration, and keeps the state live. *)
Lemma base_run_window : forall is s, ub_live (ti_base I) s ->
  window I (run M (map (ub_compile (ti_base I)) is) s) = cm_runl is (window I s) /\
  ub_live (ti_base I) (run M (map (ub_compile (ti_base I)) is) s).
Proof.
  induction is as [| i is IH]; intros s Hl; simpl; [auto |].
  destruct (ub_sim (ti_base I) s i Hl) as [Hw Hl'].
  destruct (IH _ Hl') as [Hw2 Hl2]. split; [| exact Hl2].
  rewrite Hw2. unfold window in *. rewrite Hw. reflexivity.
Qed.

(* A run of compiled base moves leaves the record and the ledger alone. *)
Lemma base_run_blind : forall is s,
  m_record M (run M (map (ub_compile (ti_base I)) is) s) = m_record M s /\
  ti_ledger I (run M (map (ub_compile (ti_base I)) is) s) = ti_ledger I s.
Proof.
  destruct HC as [[Hk [_ [Hbase _]]] [_ [[Hcost Hled] _]]].
  induction is as [| i is IH]; intro s; simpl; [auto |].
  destruct (IH (m_step M s (ub_compile (ti_base I) i))) as [Hr Hlg].
  rewrite Hr, Hlg, (Hbase s _ (Hk i)), Hled, Hcost.
  unfold record_move. rewrite Hk. split; [reflexivity | lia].
Qed.

Lemma base_run_only_base : forall is,
  Forall (fun m => ti_kind I m = KBase) (map (ub_compile (ti_base I)) is).
Proof.
  destruct HC as [[Hk _] _].
  intro is. apply Forall_forall. intros m Hm.
  apply in_map_iff in Hm as [i [<- _]]. apply Hk.
Qed.

End Window.

Arguments base_run_window {M} I is s _.
Arguments base_run_blind {M} I _ is s.
Arguments base_run_only_base {M} I _ is.

(* ================================================================= *)
(* 1. Every window is printed by one free move from a clean start.   *)
(* ================================================================= *)

Theorem complete_every_window_printed : forall M (I : thiele_interface M),
  thiele_complete_with I ->
  forall s : m_state M, exists a b m,
    ti_clean I (load I a b) /\ ti_kind I m = KBase /\ m_cost M m = 0 /\
    window I (m_step M (load I a b) m) = window I s /\
    m_record M (m_step M (load I a b) m) = false /\
    ti_ledger I (m_step M (load I a b) m) = ti_ledger I (load I a b).
Proof.
  intros M I HC s.
  pose proof HC as [[Hk [Hclean [Hbase _]]] [[Hcl0 _] [[Hcost Hled] _]]].
  destruct (window I s) as [pc [x y]] eqn:Hw.
  exists (S x), y, (ub_compile (ti_base I) (CDEC RA pc)).
  assert (Hkm : ti_kind I (ub_compile (ti_base I) (CDEC RA pc)) = KBase) by apply Hk.
  assert (Hc0 : m_cost M (ub_compile (ti_base I) (CDEC RA pc)) = 0)
    by (rewrite Hcost; unfold record_move; rewrite Hkm; reflexivity).
  split; [apply Hclean |]. split; [exact Hkm |]. split; [exact Hc0 |].
  split.
  - unfold window, load.
    destruct (ub_sim (ti_base I) (ub_load (ti_base I) (S x) y) (CDEC RA pc)
                (ub_load_live (ti_base I) (S x) y)) as [Hs _].
    rewrite Hs, ub_load_window. reflexivity.
  - split.
    + rewrite (Hbase _ _ Hkm). apply Hcl0, Hclean.
    + rewrite Hled, Hc0. lia.
Qed.

(* ================================================================= *)
(* 2 and 3. Same start, same window, different ledger and record.    *)
(* ================================================================= *)

(* The two runs together: from one clean start, a certified run and a run
   of base moves only, ending in the same window. *)
Lemma complete_two_runs : forall M (I : thiele_interface M),
  thiele_complete_with I ->
  exists a b tr1 tr2,
    ti_clean I (load I a b) /\
    Forall (fun m => ti_kind I m = KBase) tr2 /\
    window I (run M tr1 (load I a b)) = window I (run M tr2 (load I a b)) /\
    m_record M (run M tr1 (load I a b)) = true /\
    m_record M (run M tr2 (load I a b)) = false /\
    ti_ledger I (run M tr2 (load I a b)) = ti_ledger I (load I a b) /\
    ti_ledger I (load I a b) + 3 <= ti_ledger I (run M tr1 (load I a b)).
Proof.
  intros M I HC.
  pose proof HC as [_ [[Hcl0 _] _]].
  destruct (some_run_certifies M I HC) as [a [b [tr1 [Hclean Hup]]]].
  destruct (certificate_costs_three M I HC (load I a b) tr1 Hclean Hup) as [_ H3].
  destruct (window I (run M tr1 (load I a b))) as [pc [x y]] eqn:Hw.
  destruct (cm_reach (1, (a, b)) pc x y) as [is His].
  exists a, b, tr1, (map (ub_compile (ti_base I)) is).
  destruct (base_run_window I is (load I a b) (ub_load_live (ti_base I) a b)) as [Hw2 _].
  destruct (base_run_blind I HC is (load I a b)) as [Hr2 Hl2].
  split; [exact Hclean |]. split; [apply base_run_only_base, HC |].
  split.
  - rewrite Hw, Hw2. unfold window, load. rewrite ub_load_window. symmetry. exact His.
  - split; [exact Hup |]. split; [rewrite Hr2; apply Hcl0, Hclean |].
    split; [exact Hl2 | lia].
Qed.

Theorem complete_hides_ledger : forall M (I : thiele_interface M),
  thiele_complete_with I ->
  exists a b tr1 tr2,
    ti_clean I (load I a b) /\
    window I (run M tr1 (load I a b)) = window I (run M tr2 (load I a b)) /\
    ti_ledger I (run M tr1 (load I a b)) <> ti_ledger I (run M tr2 (load I a b)) /\
    ti_ledger I (run M tr2 (load I a b)) + 3 <= ti_ledger I (run M tr1 (load I a b)).
Proof.
  intros M I HC.
  destruct (complete_two_runs M I HC)
    as [a [b [tr1 [tr2 [Hc [_ [Hw [_ [_ [Hl2 Hl1]]]]]]]]]].
  exists a, b, tr1, tr2. split; [exact Hc |]. split; [exact Hw |]. lia.
Qed.

Theorem complete_hides_record : forall M (I : thiele_interface M),
  thiele_complete_with I ->
  exists a b tr1 tr2,
    ti_clean I (load I a b) /\
    window I (run M tr1 (load I a b)) = window I (run M tr2 (load I a b)) /\
    m_record M (run M tr1 (load I a b)) = true /\
    m_record M (run M tr2 (load I a b)) = false.
Proof.
  intros M I HC.
  destruct (complete_two_runs M I HC)
    as [a [b [tr1 [tr2 [Hc [_ [Hw [Hr1 [Hr2 _]]]]]]]]].
  exists a, b, tr1, tr2. auto.
Qed.

(* ================================================================= *)
(* 4. No function of the window gives the ledger or the record.      *)
(* ================================================================= *)

(* Every candidate function of the window is wrong about the ledger on
   some run from a clean start. *)
Theorem complete_ledger_oracle_fails : forall M (I : thiele_interface M),
  thiele_complete_with I ->
  forall f : cm_conf -> nat, exists a b tr,
    ti_clean I (load I a b) /\
    f (window I (run M tr (load I a b))) <> ti_ledger I (run M tr (load I a b)).
Proof.
  intros M I HC f.
  destruct (complete_hides_ledger M I HC) as [a [b [tr1 [tr2 [Hc [Hw [Hne _]]]]]]].
  destruct (Nat.eq_dec (f (window I (run M tr1 (load I a b))))
                       (ti_ledger I (run M tr1 (load I a b)))) as [He | He].
  - exists a, b, tr2. split; [exact Hc |]. rewrite <- Hw, He. exact Hne.
  - exists a, b, tr1. split; [exact Hc | exact He].
Qed.

Theorem complete_record_oracle_fails : forall M (I : thiele_interface M),
  thiele_complete_with I ->
  forall f : cm_conf -> bool, exists a b tr,
    ti_clean I (load I a b) /\
    f (window I (run M tr (load I a b))) <> m_record M (run M tr (load I a b)).
Proof.
  intros M I HC f.
  destruct (complete_hides_record M I HC) as [a [b [tr1 [tr2 [Hc [Hw [Hr1 Hr2]]]]]]].
  destruct (f (window I (run M tr1 (load I a b)))) eqn:Hf.
  - exists a, b, tr2. split; [exact Hc |]. rewrite <- Hw, Hf, Hr2. discriminate.
  - exists a, b, tr1. split; [exact Hc |]. rewrite Hf, Hr1. discriminate.
Qed.

Theorem complete_no_ledger_oracle : forall M (I : thiele_interface M),
  thiele_complete_with I ->
  ~ exists f : cm_conf -> nat, forall a b tr,
      f (window I (run M tr (load I a b))) = ti_ledger I (run M tr (load I a b)).
Proof.
  intros M I HC [f Hf].
  destruct (complete_ledger_oracle_fails M I HC f) as [a [b [tr [_ Hne]]]].
  apply Hne, Hf.
Qed.

Theorem complete_no_record_oracle : forall M (I : thiele_interface M),
  thiele_complete_with I ->
  ~ exists f : cm_conf -> bool, forall a b tr,
      f (window I (run M tr (load I a b))) = m_record M (run M tr (load I a b)).
Proof.
  intros M I HC [f Hf].
  destruct (complete_record_oracle_fails M I HC f) as [a [b [tr [_ Hne]]]].
  apply Hne, Hf.
Qed.

(* ================================================================= *)
(* 5. Per machine.                                                   *)
(* ================================================================= *)

(* Every Thiele-complete machine has an interface making it Thiele-complete
   (by definition), and through it the machine keeps its ledger and its
   record out of its window. The theorems above say more: this holds
   through EVERY such interface. *)
Theorem thiele_complete_hides : forall M, thiele_complete M ->
  exists I : thiele_interface M, thiele_complete_with I /\
  (~ exists f : cm_conf -> nat, forall a b tr,
      f (window I (run M tr (load I a b))) = ti_ledger I (run M tr (load I a b))) /\
  (~ exists f : cm_conf -> bool, forall a b tr,
      f (window I (run M tr (load I a b))) = m_record M (run M tr (load I a b))).
Proof.
  intros M [I HC]. exists I. split; [exact HC |].
  split; [apply complete_no_ledger_oracle | apply complete_no_record_oracle]; exact HC.
Qed.

(* ================================================================= *)
(* Assumption audit. Every line must print                            *)
(* "Closed under the global context".                                 *)
(* ================================================================= *)

Print Assumptions cm_reach.
Print Assumptions complete_every_window_printed.
Print Assumptions complete_two_runs.
Print Assumptions complete_hides_ledger.
Print Assumptions complete_hides_record.
Print Assumptions complete_ledger_oracle_fails.
Print Assumptions complete_record_oracle_fails.
Print Assumptions complete_no_ledger_oracle.
Print Assumptions complete_no_record_oracle.
Print Assumptions thiele_complete_hides.
