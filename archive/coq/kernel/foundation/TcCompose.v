(** TcCompose.v: a counter program run first, then another program.

    Let M be a program of INC and DEC only (a list of [E.minsky]) and B its
    compiled form [E.compile M]. Suppose M, started at line 1 with n in
    counter A and 0 in counter B, falls off its end with n' in counter A and
    0 in counter B. Then the program

        B ++ (V moved down by length M lines)

    started on n behaves, from the moment M has finished, exactly as V
    started on n': it stops on n exactly when V stops on n', and the two
    final states agree on the counters, the trap latch, the ledger, the flag
    and the shape of the fact table and the channel ([tc_agree]). M itself
    pays nothing and records nothing; it only moves the versions of the two
    counters, which is why facts are compared by shape.

    [tc_compose_halts] is this statement. It is the engine behind the
    specialisation program of the packed universal machine and the packed
    recursion theorem.

    Dependencies: Coq standard library, EarnedCore.v, TcBridge.v,
    TcBlocks.v, TcRice.v. No axioms and no unfinished proofs.                           *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the two-counter machine of EarnedCore.v (its
   programs, runs and the numbering of programs). The machine's link to the
   abstract record (a CertificationSystem with the trace cost floor, and a
   Thiele-complete machine) lives in EarnedCoreLinks.v and ThieleComplete.v. *)


From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Kernel.TcBridge Minimal.TcBlocks Kernel.TcRice.
Module E := Minimal.EarnedCore.
Unset Implicit Arguments.

Theorem tc_compose_halts : forall (M : list E.minsky) n n' (V : list E.instr) m,
  tc_steps M m (1, (n, 0)) (S (length M), (n', 0)) ->
  let Q := E.compile M ++ tc_greloc (length M) V in
  (forall s, tc_ends n Q s -> exists t, tc_ends n' V t /\ tc_agree s t) /\
  (forall t, tc_ends n' V t -> exists s, tc_ends n Q s /\ tc_agree s t).
Proof.
  intros M n n' V m Hsteps Q.
  set (B := E.compile M).
  set (s0 := E.start n 0).
  assert (Hlen : length B = length M) by (unfold B, E.compile; apply map_length).
  assert (Hin : forall k, k < m -> E.next_instr B (E.core_of (E.run_prog k B s0)) <> None).
  { intros k Hk. destruct (tc_steps_inside M m _ _ Hsteps k Hk) as [ck [Hck Hs]].
    eapply tc_not_stopped; [reflexivity | exact Hck | exact Hs]. }
  assert (Hrun : E.run_prog m Q (E.start n 0) = E.run_prog m B (E.start n 0)).
  { unfold Q. apply tc_prefix_run. exact Hin. }
  destruct (tc_compile_run M m s0 eq_refl) as (Hw & Hf & Hc & He & Hm & Hk).
  change (E.window (E.core_of s0)) with (1, (n, 0)) in Hw.
  rewrite (tc_steps_mrun M m _ _ Hsteps) in Hw.
  unfold E.window in Hw. injection Hw as Hpc Hca Hcb.
  assert (HQ : Q = B ++ tc_greloc (length B) V) by (unfold Q; rewrite Hlen; reflexivity).
  eapply tc_gfinal_two with (da := E.va (E.core_of (E.run_prog m B s0)))
                            (db := E.vb (E.core_of (E.run_prog m B s0)))
                            (n := n) (n' := n') (P := V) (off := length B).
  - rewrite HQ. rewrite <- (app_nil_r (tc_greloc _ V)). apply tc_gembeds_app.
  - rewrite HQ. rewrite app_length, tc_greloc_length. reflexivity.
  - exists m. rewrite Hrun.
    apply tc_rel_start.
    + exact Hca. 
    + exact Hcb.
    + exact Hf.
    + exact Hc.
    + exact He.
    + exact Hm.
    + exact Hk.
    + rewrite Hlen. exact Hpc.
Qed.

(* the compiled program alone: it stops exactly when the counter program does *)
Theorem tc_compile_ends : forall (M : list E.minsky) n s,
  tc_ends n (E.compile M) s ->
  exists m c, tc_steps M m (1, (n, 0)) c /\ E.mstep M c = None /\
              E.ca (E.core_of s) = fst (snd c) /\ E.cb (E.core_of s) = snd (snd c).
Proof.
  intros M n s [N [-> HN]].
  destruct (tc_compile_run M N (E.start n 0) eq_refl) as (Hw & _ & _ & He & _).
  change (E.window (E.core_of (E.start n 0))) with (1, (n, 0)) in Hw.
  assert (Hstop : E.mstep M (E.mrun N M (1, (n, 0))) = None).
  { rewrite <- Hw. destruct (E.simulation_step M _ He) as [Hnone _]. apply Hnone. exact HN. }
  destruct (tc_mrun_steps M N (1, (n, 0)) _ eq_refl Hstop) as [m [_ Hm]].
  exists m, (E.mrun N M (1, (n, 0))). repeat split.
  - exact Hm.
  - exact Hstop.
  - unfold E.window in Hw. destruct (E.mrun N M (1, (n, 0))) as [j [a b]]. simpl.
    injection Hw as _ H2 _. exact H2.
  - unfold E.window in Hw. destruct (E.mrun N M (1, (n, 0))) as [j [a b]]. simpl.
    injection Hw as _ _ H3. exact H3.
Qed.

Theorem tc_ends_compile : forall (M : list E.minsky) n m c,
  tc_steps M m (1, (n, 0)) c -> E.mstep M c = None ->
  exists s, tc_ends n (E.compile M) s /\
            E.ca (E.core_of s) = fst (snd c) /\ E.cb (E.core_of s) = snd (snd c).
Proof.
  intros M n m c Hsteps Hstop.
  destruct (tc_compile_run M m (E.start n 0) eq_refl) as (Hw & _ & _ & He & _).
  change (E.window (E.core_of (E.start n 0))) with (1, (n, 0)) in Hw.
  rewrite (tc_steps_mrun M m _ _ Hsteps) in Hw.
  exists (E.run_prog m (E.compile M) (E.start n 0)). split; [| split].
  - exists m. split; [reflexivity |].
    unfold E.halted. destruct (E.simulation_step M _ He) as [_ _].
    destruct (E.simulation_step M _ He) as [Hnone _]. apply Hnone. rewrite Hw. exact Hstop.
  - unfold E.window in Hw. destruct c as [j [a b]]. simpl. injection Hw as _ H2 _. exact H2.
  - unfold E.window in Hw. destruct c as [j [a b]]. simpl. injection Hw as _ _ H3. exact H3.
Qed.

Print Assumptions tc_compose_halts.
Print Assumptions tc_compile_ends.
Print Assumptions tc_ends_compile.
