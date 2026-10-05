(** SmHostRice.v: Rice's theorem for programs of the host machine.

    The host machine is the machine of EarnedMulti.v, with a counter for
    every register number, and its property language is left open. A
    program is run on one number x placed in register 1 (sm_hstart).
    Two programs behave the same (sm_hequiv, SmHostBlocks.v) when on every
    input both run forever, or both stop and the final states agree on every
    register value, the fact table, the channel, the trap latch, the ledger
    and the flag.

    Theorem [sm_host_rice]. Let Pi be a property of host programs that
    respects behaving the same, with Pi y for some program y and not Pi n
    for some program n. Then Pi is undecidable, in the sense of the vendored
    Saarland library: a decider for Pi would make the complement of
    single-tape Turing machine halting enumerable.

    The proof reduces the complement of two-counter halting (MM2) to the
    complement of Pi. A two-counter program H with start (a, b) goes to the
    host program that puts a and b into two fresh registers K and K + 1,
    runs a copy of H on them, empties them, and then runs y. Every
    instruction before the copy of y is an INC or a DEC, so it pays nothing
    and touches no fact, channel, trap latch or flag. If H stops, the
    program behaves the same as y; if H runs forever, so does the program.

    Dependencies: Coq standard library, the vendored coq-undecidability
    library (MM2, Synthetic), EarnedCore.v, EarnedMulti.v, SmHostBlocks.v
    and SmMM2Compl.v (a copy of MM2ComplementUndec.v). No axioms, no
    Admitted.                                                              *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Coq Require Import Relations.Relation_Operators Relations.Operators_Properties.
From Undecidability.Synthetic Require Import Undecidability.
From Undecidability.MinskyMachines Require Import MM2.
Require Minimal.EarnedCore Minimal.EarnedMulti.
Require Import Sm.SmHostBlocks Sm.SmMM2Compl.
Module E := Minimal.EarnedCore.
Module M := Minimal.EarnedMulti.
Unset Implicit Arguments.

(* ================================================================= *)
(* The vendored two-counter machine, read through EarnedCore's mstep. *)
(* (Copied from EarnedCoreLinks.v, which imports more than this needs.) *)
(* ================================================================= *)

Definition sm_of_mm2 (i : mm2_instr) : E.minsky :=
  match i with
  | mm2_inc_a => E.MINC E.CA
  | mm2_inc_b => E.MINC E.CB
  | mm2_dec_a j => E.MDEC E.CA j
  | mm2_dec_b j => E.MDEC E.CB j
  end.

Lemma sm_mm2_instr_at_iff : forall (r : mm2_instr) i P,
  mm2_instr_at r i P <-> E.fetch P i = Some r.
Proof.
  intros r i P. split.
  - intros [l [rest [-> <-]]]. simpl.
    rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
  - destruct i as [| i]; simpl; [discriminate |]. intro H.
    destruct (nth_error_split P i H) as [l [rest [-> Hl]]].
    exists l, rest. split; [reflexivity | lia].
Qed.

Lemma sm_mm2_step_iff : forall P x y,
  mm2_step P x y <-> E.mstep (map sm_of_mm2 P) x = Some y.
Proof.
  intros P [i [a b]] y. unfold mm2_step, E.mstep. simpl.
  rewrite E.fetch_map. split.
  - intros [r [Hat Hr]]. apply sm_mm2_instr_at_iff in Hat. simpl in Hat.
    rewrite Hat. inversion Hr; subst; reflexivity.
  - destruct (E.fetch P i) as [r |] eqn:Hf; simpl; [| discriminate].
    intro H. exists r. split; [apply sm_mm2_instr_at_iff; exact Hf |].
    destruct r; simpl in H;
      [ | | destruct a | destruct b]; injection H as <-; constructor.
Qed.

Lemma sm_mm2_stop_iff : forall P x, mm2_stop P x <-> E.mstep (map sm_of_mm2 P) x = None.
Proof.
  intros P x. unfold mm2_stop. split.
  - intro H. destruct (E.mstep (map sm_of_mm2 P) x) as [y |] eqn:Hm; [| reflexivity].
    exfalso. apply (H y). apply sm_mm2_step_iff. exact Hm.
  - intros H y Hs. apply sm_mm2_step_iff in Hs. congruence.
Qed.

Lemma sm_mm2_terminates_iff : forall P x,
  mm2_terminates P x <->
  exists n, E.mstep (map sm_of_mm2 P) (E.mrun n (map sm_of_mm2 P) x) = None.
Proof.
  intros P x. unfold mm2_terminates. split.
  - intros [z [Hrt Hstop]]. apply clos_rt_rt1n_iff in Hrt.
    induction Hrt as [x | x y z Hs _ IH].
    + exists 0. simpl. apply sm_mm2_stop_iff. exact Hstop.
    + destruct (IH Hstop) as [n Hn]. exists (S n). simpl.
      apply sm_mm2_step_iff in Hs. rewrite Hs. exact Hn.
  - intros [n Hn]. revert x Hn. induction n as [| n IH]; intros x Hn; simpl in Hn.
    + exists x. split; [apply rt_refl | apply sm_mm2_stop_iff; exact Hn].
    + destruct (E.mstep (map sm_of_mm2 P) x) as [y |] eqn:Hm.
      * destruct (IH y Hn) as [z [Hrt Hstop]]. exists z. split; [| exact Hstop].
        apply rt_trans with y; [apply rt_step, sm_mm2_step_iff; exact Hm | exact Hrt].
      * exists x. split; [apply rt_refl | apply sm_mm2_stop_iff; exact Hm].
Qed.

(* The least number with a decidable property, from any number with it. *)
Lemma sm_least : forall (Q : nat -> Prop), (forall n, Q n \/ ~ Q n) ->
  forall n, Q n -> exists m, Q m /\ forall k, k < m -> ~ Q k.
Proof.
  intros Q Hd n. induction n as [n IH] using (well_founded_induction lt_wf). intro Hn.
  assert (Hcase : (exists k, k < n /\ Q k) \/ (forall k, k < n -> ~ Q k)).
  { clear IH Hn. induction n as [| n IHn].
    - right. intros k Hk. lia.
    - destruct IHn as [[k [Hk Hq]] | Hno].
      + left. exists k. split; [lia | exact Hq].
      + destruct (Hd n) as [Hq | Hq].
        * left. exists n. split; [lia | exact Hq].
        * right. intros k Hk. destruct (Nat.eq_dec k n) as [-> | Hne]; [exact Hq |].
          apply Hno. lia. }
  destruct Hcase as [[k [Hk Hq]] | Hno].
  - exact (IH k Hk Hq).
  - exists n. split; [exact Hn | exact Hno].
Qed.

Section HostRice.

Context {prop : Type}.
Variable prop_eqb : prop -> prop -> bool.
Variable eval : prop -> nat -> bool.

Local Notation instr := (@M.instr prop).
Local Notation core := (@M.core prop).
Local Notation state := (@M.state prop).
Local Notation exec := (M.exec prop_eqb eval).
Local Notation step := (M.step prop_eqb eval).
Local Notation run_prog := (M.run_prog prop_eqb eval).
Local Notation hends := (sm_hends prop_eqb eval).
Local Notation hequiv := (sm_hequiv prop_eqb eval).
Local Notation srel := (sm_srel (prop := prop)).

(* ================================================================= *)
(* A two-counter program on two host registers.                       *)
(* ================================================================= *)

Definition sm_mk (K : nat) (m : E.minsky) : instr :=
  match m with
  | E.MINC E.CA => M.INC K
  | E.MINC E.CB => M.INC (S K)
  | E.MDEC E.CA j => M.DEC K j
  | E.MDEC E.CB j => M.DEC (S K) j
  end.

Definition sm_win (K : nat) (k : core) : E.mconf := (M.pc k, (M.vals k K, M.vals k (S K))).

Lemma sm_mk_plain : forall K m, M.plain (sm_mk K m) = true.
Proof. intros K [[] | [] j]; reflexivity. Qed.

Lemma sm_mk_step : forall (Mp : list E.minsky) K s,
  M.err (M.core_of s) = false ->
  (E.mstep Mp (sm_win K (M.core_of s)) = None <->
   M.next_instr (map (sm_mk K) Mp) (M.core_of s) = None) /\
  (forall y, E.mstep Mp (sm_win K (M.core_of s)) = Some y ->
     sm_win K (M.core_of (step (map (sm_mk K) Mp) s)) = y /\
     (forall q, q <> K -> q <> S K ->
        M.vals (M.core_of (step (map (sm_mk K) Mp) s)) q = M.vals (M.core_of s) q) /\
     (forall q, q <> K -> q <> S K ->
        M.vers (M.core_of (step (map (sm_mk K) Mp) s)) q = M.vers (M.core_of s) q) /\
     M.facts (M.core_of (step (map (sm_mk K) Mp) s)) = M.facts (M.core_of s) /\
     M.chan (M.core_of (step (map (sm_mk K) Mp) s)) = M.chan (M.core_of s) /\
     M.err (M.core_of (step (map (sm_mk K) Mp) s)) = false /\
     M.mu (step (map (sm_mk K) Mp) s) = M.mu s /\
     M.cert (step (map (sm_mk K) Mp) s) = M.cert s).
Proof.
  intros Mp K s He.
  assert (Hn : M.next_instr (map (sm_mk K) Mp) (M.core_of s) =
               option_map (sm_mk K) (E.fetch Mp (M.pc (M.core_of s)))).
  { unfold M.next_instr. rewrite He.
    replace (M.fetch (map (sm_mk K) Mp) (M.pc (M.core_of s)))
      with (option_map (sm_mk K) (E.fetch Mp (M.pc (M.core_of s))))
      by (destruct (M.pc (M.core_of s)); simpl; [reflexivity | rewrite nth_error_map; reflexivity]).
    destruct (E.fetch Mp (M.pc (M.core_of s))) as [[[] | [] j] |]; reflexivity. }
  unfold E.mstep, sm_win. simpl fst.
  destruct (E.fetch Mp (M.pc (M.core_of s))) as [m |] eqn:Hf.
  - split; [destruct m as [[] | [] j]; simpl;
            [ | | destruct (M.vals (M.core_of s) K) | destruct (M.vals (M.core_of s) (S K))];
            split; intro H; try discriminate; rewrite Hn in H; discriminate |].
    intros y Hy.
    assert (Hst : step (map (sm_mk K) Mp) s = exec s (sm_mk K m))
      by (unfold step; rewrite Hn; reflexivity).
    rewrite Hst.
    destruct (sm_plain_exec prop_eqb eval s (sm_mk K m) (sm_mk_plain K m)) as (Hf1 & Hc1 & He1 & Hm1 & Hk1).
    rewrite Hf1, Hc1, He1, Hm1, Hk1. clear Hf1 Hc1 He1 Hm1 Hk1.
    assert (HKS : Nat.eqb K (S K) = false) by (apply Nat.eqb_neq; lia).
    assert (HSK : Nat.eqb (S K) K = false) by (apply Nat.eqb_neq; lia).
    unfold sm_win.
    destruct m as [[] | [] j]; simpl in Hy.
    + injection Hy as <-.
      assert (Hk : M.core_of (exec s (sm_mk K (E.MINC E.CA))) =
                   M.write (M.core_of s) K (S (M.vals (M.core_of s) K)) (S (M.pc (M.core_of s))))
        by (simpl; unfold M.cexec; rewrite He; reflexivity).
      rewrite Hk, !M.multi_val_write, M.multi_pc_write, Nat.eqb_refl, HKS.
      repeat split; auto.
      all: intros q Hq1 Hq2; rewrite ?M.multi_val_write, ?M.multi_ver_write; repeat match goal with |- context [Nat.eqb ?u ?v] => destruct (Nat.eqb_spec u v) end; try lia; reflexivity.
    + injection Hy as <-.
      assert (Hk : M.core_of (exec s (sm_mk K (E.MINC E.CB))) =
                   M.write (M.core_of s) (S K) (S (M.vals (M.core_of s) (S K))) (S (M.pc (M.core_of s))))
        by (simpl; unfold M.cexec; rewrite He; reflexivity).
      rewrite Hk, !M.multi_val_write, M.multi_pc_write, Nat.eqb_refl, HSK.
      repeat split; auto.
      all: intros q Hq1 Hq2; rewrite ?M.multi_val_write, ?M.multi_ver_write; repeat match goal with |- context [Nat.eqb ?u ?v] => destruct (Nat.eqb_spec u v) end; try lia; reflexivity.
    + destruct (M.vals (M.core_of s) K) as [| v] eqn:Hv; injection Hy as <-.
      * assert (Hk : M.core_of (exec s (sm_mk K (E.MDEC E.CA j))) =
                     M.goto (M.core_of s) (S (M.pc (M.core_of s))))
          by (simpl; unfold M.cexec; rewrite He, Hv; reflexivity).
        rewrite Hk. simpl. rewrite Hv. repeat split; auto.
      * assert (Hk : M.core_of (exec s (sm_mk K (E.MDEC E.CA j))) = M.write (M.core_of s) K v j)
          by (simpl; unfold M.cexec; rewrite He, Hv; reflexivity).
        rewrite Hk, !M.multi_val_write, M.multi_pc_write, Nat.eqb_refl, HKS.
        repeat split; auto.
      all: intros q Hq1 Hq2; rewrite ?M.multi_val_write, ?M.multi_ver_write; repeat match goal with |- context [Nat.eqb ?u ?v] => destruct (Nat.eqb_spec u v) end; try lia; reflexivity.
    + destruct (M.vals (M.core_of s) (S K)) as [| v] eqn:Hv; injection Hy as <-.
      * assert (Hk : M.core_of (exec s (sm_mk K (E.MDEC E.CB j))) =
                     M.goto (M.core_of s) (S (M.pc (M.core_of s))))
          by (simpl; unfold M.cexec; rewrite He, Hv; reflexivity).
        rewrite Hk. simpl. rewrite Hv. repeat split; auto.
      * assert (Hk : M.core_of (exec s (sm_mk K (E.MDEC E.CB j))) = M.write (M.core_of s) (S K) v j)
          by (simpl; unfold M.cexec; rewrite He, Hv; reflexivity).
        rewrite Hk, !M.multi_val_write, M.multi_pc_write, Nat.eqb_refl, HSK.
        repeat split; auto.
      all: intros q Hq1 Hq2; rewrite ?M.multi_val_write, ?M.multi_ver_write; repeat match goal with |- context [Nat.eqb ?u ?v] => destruct (Nat.eqb_spec u v) end; try lia; reflexivity.
  - split; [split; intro; [rewrite Hn; reflexivity | reflexivity] |].
    intros y Hy. discriminate.
Qed.

Lemma sm_mk_run : forall (Mp : list E.minsky) K n s,
  M.err (M.core_of s) = false ->
  sm_win K (M.core_of (run_prog n (map (sm_mk K) Mp) s)) = E.mrun n Mp (sm_win K (M.core_of s)) /\
  (forall q, q <> K -> q <> S K ->
     M.vals (M.core_of (run_prog n (map (sm_mk K) Mp) s)) q = M.vals (M.core_of s) q) /\
  (forall q, q <> K -> q <> S K ->
     M.vers (M.core_of (run_prog n (map (sm_mk K) Mp) s)) q = M.vers (M.core_of s) q) /\
  M.facts (M.core_of (run_prog n (map (sm_mk K) Mp) s)) = M.facts (M.core_of s) /\
  M.chan (M.core_of (run_prog n (map (sm_mk K) Mp) s)) = M.chan (M.core_of s) /\
  M.err (M.core_of (run_prog n (map (sm_mk K) Mp) s)) = false /\
  M.mu (run_prog n (map (sm_mk K) Mp) s) = M.mu s /\
  M.cert (run_prog n (map (sm_mk K) Mp) s) = M.cert s.
Proof.
  intros Mp K n. induction n as [| n IH]; intros s He; [simpl; repeat split; auto |].
  destruct (sm_mk_step Mp K s He) as [Hnone Hsome].
  rewrite sm_run_succ. simpl E.mrun.
  destruct (E.mstep Mp (sm_win K (M.core_of s))) as [y |] eqn:Hm.
  - destruct (Hsome y eq_refl) as (Hw & Hv & Hw' & Hf & Hc & He' & Hmu & Hk).
    destruct (IH (step (map (sm_mk K) Mp) s) He') as (Hw2 & Hv2 & Hww2 & Hf2 & Hc2 & He2 & Hm2 & Hk2).
    rewrite Hw in Hw2. repeat split; try congruence.
    + intros q H1 H2. rewrite Hv2, Hv by assumption. reflexivity.
    + intros q H1 H2. rewrite Hww2, Hw' by assumption. reflexivity.
  - assert (Hh : M.next_instr (map (sm_mk K) Mp) (M.core_of s) = None) by (apply Hnone; reflexivity).
    assert (Hs : step (map (sm_mk K) Mp) s = s) by (unfold step; rewrite Hh; reflexivity).
    rewrite Hs. rewrite sm_halted_stay by exact Hh.
    repeat split; auto.
Qed.

Lemma sm_mk_halted : forall (Mp : list E.minsky) K s,
  M.err (M.core_of s) = false ->
  (M.next_instr (map (sm_mk K) Mp) (M.core_of s) = None <->
   E.mstep Mp (sm_win K (M.core_of s)) = None).
Proof. intros. symmetry. apply (sm_mk_step Mp K s). assumption. Qed.

(* ================================================================= *)
(* The reduction program.                                             *)
(* ================================================================= *)

Definition sm_reg_of (i : instr) : nat :=
  match i with
  | M.INC r | M.DEC r _ | M.CHECK _ r | M.COMMIT _ r => r
  | _ => 0
  end.

(* A bound on the registers a program names. *)
Definition sm_regs_bound (P : list instr) : nat :=
  fold_right (fun i m => Nat.max (sm_reg_of i) m) 0 P.

Lemma sm_regs_bound_spec : forall P i r, In i P -> M.mentions i r = true -> r <= sm_regs_bound P.
Proof.
  induction P as [| i0 P IH]; intros i r Hin Hm; [destruct Hin |].
  simpl. destruct Hin as [-> | Hin].
  - destruct i as [d | d j | | p d | p d |]; simpl in Hm; try discriminate;
      apply Nat.eqb_eq in Hm; subst; simpl; lia.
  - specialize (IH i r Hin Hm). lia.
Qed.

(* The first fresh register for P: two above every register P names, so it
   is never 0 or 1 either. *)
Definition sm_fresh (P : list instr) : nat := S (S (sm_regs_bound P)).

Definition sm_hblock (K : nat) (H : list mm2_instr) : list instr :=
  map (sm_mk K) (map sm_of_mm2 H).

Definition sm_rice_pre (K a b : nat) (H : list mm2_instr) : list instr :=
  let L1 := S (a + b + length (sm_hblock K H)) in
  (sm_incs K a ++ sm_incs (S K) b) ++ sm_reloc (a + b) (sm_hblock K H) ++
  [M.DEC K L1; M.DEC (S K) (S L1)].

Definition sm_rice_prog (a b : nat) (H : list mm2_instr) (P : list instr) : list instr :=
  let K := sm_fresh P in
  sm_rice_pre K a b H ++ sm_reloc (length (sm_rice_pre K a b H)) P.

Lemma sm_rice_pre_length : forall K a b H,
  length (sm_rice_pre K a b H) = S (S (a + b + length (sm_hblock K H))).
Proof.
  intros. unfold sm_rice_pre. rewrite !app_length, sm_reloc_length, !sm_incs_length.
  simpl. lia.
Qed.

(* Where each part of the reduction program sits. *)
Lemma sm_rice_fetch_a : forall a b H P p, 1 <= p <= a ->
  M.fetch (sm_rice_prog a b H P) (p + 0) = Some (M.INC (sm_fresh P)).
Proof.
  intros a b H P p Hp. unfold sm_rice_prog, sm_rice_pre.
  rewrite <- !app_assoc. rewrite sm_fetch_app_left by (rewrite sm_incs_length; lia).
  destruct p as [| p]; [lia |]. simpl. unfold sm_incs.
  apply nth_error_repeat. lia.
Qed.

Lemma sm_rice_fetch_b : forall a b H P p, 1 <= p <= b ->
  M.fetch (sm_rice_prog a b H P) (p + a) = Some (M.INC (S (sm_fresh P))).
Proof.
  intros a b H P p Hp. unfold sm_rice_prog, sm_rice_pre.
  rewrite <- !app_assoc.
  destruct p as [| p]; [lia |]. replace (S p + a) with (S (a + p)) by lia. simpl.
  rewrite nth_error_app2 by (rewrite sm_incs_length; lia).
  rewrite sm_incs_length. replace (a + p - a) with p by lia.
  rewrite nth_error_app1 by (rewrite sm_incs_length; lia).
  unfold sm_incs. apply nth_error_repeat. lia.
Qed.

Lemma sm_rice_embeds_h : forall a b H P,
  sm_embeds (sm_rice_prog a b H P) (sm_hblock (sm_fresh P) H) (a + b).
Proof.
  intros a b H P. unfold sm_rice_prog, sm_rice_pre.
  set (A := sm_incs (sm_fresh P) a ++ sm_incs (S (sm_fresh P)) b).
  assert (HA : length A = a + b) by (unfold A; rewrite app_length, !sm_incs_length; reflexivity).
  rewrite <- HA. rewrite <- !app_assoc. apply sm_embeds_app.
Qed.

Lemma sm_fetch_app_right : forall (A C : list instr) p,
  M.fetch (A ++ C) (length A + S p) = M.fetch C (S p).
Proof.
  intros A C p. replace (length A + S p) with (S (length A + p)) by lia. simpl.
  rewrite nth_error_app2 by lia. f_equal. lia.
Qed.

Lemma sm_rice_prog_split : forall a b H P,
  let K := sm_fresh P in
  let L1 := S (a + b + length (sm_hblock K H)) in
  sm_rice_prog a b H P =
  ((sm_incs K a ++ sm_incs (S K) b) ++ sm_reloc (a + b) (sm_hblock K H)) ++
  ([M.DEC K L1; M.DEC (S K) (S L1)] ++ sm_reloc (S L1) P).
Proof.
  intros a b H P K L1. unfold sm_rice_prog. rewrite sm_rice_pre_length.
  unfold sm_rice_pre. fold K. fold L1. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma sm_rice_fetch_clear1 : forall a b H P,
  let L1 := S (a + b + length (sm_hblock (sm_fresh P) H)) in
  M.fetch (sm_rice_prog a b H P) L1 = Some (M.DEC (sm_fresh P) L1).
Proof.
  intros a b H P L1. rewrite sm_rice_prog_split. fold L1.
  set (A := (sm_incs (sm_fresh P) a ++ sm_incs (S (sm_fresh P)) b) ++
                    sm_reloc (a + b) (sm_hblock (sm_fresh P) H)).
  assert (E : L1 = length A + 1)
    by (unfold A; rewrite !app_length, sm_reloc_length, !sm_incs_length; unfold L1; lia).
  transitivity (M.fetch (A ++ ([M.DEC (sm_fresh P) L1; M.DEC (S (sm_fresh P)) (S L1)] ++
                  sm_reloc (S L1) P)) (length A + 1)); [f_equal; exact E |].
  rewrite sm_fetch_app_right. reflexivity.
Qed.

Lemma sm_rice_fetch_clear2 : forall a b H P,
  let L1 := S (a + b + length (sm_hblock (sm_fresh P) H)) in
  M.fetch (sm_rice_prog a b H P) (S L1) = Some (M.DEC (S (sm_fresh P)) (S L1)).
Proof.
  intros a b H P L1. rewrite sm_rice_prog_split. fold L1.
  set (A := (sm_incs (sm_fresh P) a ++ sm_incs (S (sm_fresh P)) b) ++
                    sm_reloc (a + b) (sm_hblock (sm_fresh P) H)).
  assert (E : (S L1) = length A + 2)
    by (unfold A; rewrite !app_length, sm_reloc_length, !sm_incs_length; unfold L1; lia).
  transitivity (M.fetch (A ++ ([M.DEC (sm_fresh P) L1; M.DEC (S (sm_fresh P)) (S L1)] ++
                  sm_reloc (S L1) P)) (length A + 2)); [f_equal; exact E |].
  rewrite sm_fetch_app_right. reflexivity.
Qed.

Lemma sm_rice_embeds_p : forall a b H P,
  sm_embeds (sm_rice_prog a b H P) P (length (sm_rice_pre (sm_fresh P) a b H)).
Proof.
  intros a b H P. unfold sm_rice_prog. rewrite <- (app_nil_r (sm_reloc _ P)).
  apply sm_embeds_app.
Qed.

Lemma sm_rice_length : forall a b H P,
  length (sm_rice_prog a b H P) = length (sm_rice_pre (sm_fresh P) a b H) + length P.
Proof. intros. unfold sm_rice_prog. rewrite app_length, sm_reloc_length. reflexivity. Qed.

Lemma sm_within_fresh : forall P, sm_within (fun r => r < sm_fresh P) P.
Proof.
  intros P i r Hin Hm. pose proof (sm_regs_bound_spec P i r Hin Hm). unfold sm_fresh. lia.
Qed.

Lemma sm_within_all : forall (B : list instr), sm_within (fun _ => True) B.
Proof. intros B i r _ _. exact I. Qed.

Lemma sm_hblock_no_halt : forall K H, ~ In M.HALT (sm_hblock K H).
Proof.
  intros K H Hin. unfold sm_hblock in Hin. rewrite map_map in Hin.
  apply in_map_iff in Hin. destruct Hin as [[| | j | j] [Hx _]]; discriminate.
Qed.

(* The state at the start of the block of H: a and b loaded. *)
Lemma sm_rice_phase1 : forall a b H P x,
  let s1 := run_prog (a + b) (sm_rice_prog a b H P) (sm_hstart x) in
  (forall q, M.vals (M.core_of s1) q =
     if Nat.eqb q (sm_fresh P) then a
     else if Nat.eqb q (S (sm_fresh P)) then b else sm_hin x q) /\
  (forall q, q <> sm_fresh P -> q <> S (sm_fresh P) -> M.vers (M.core_of s1) q = 0) /\
  M.facts (M.core_of s1) = [] /\ M.chan (M.core_of s1) = None /\
  M.err (M.core_of s1) = false /\ M.pc (M.core_of s1) = S (a + b) /\
  M.mu s1 = 0 /\ M.cert s1 = false.
Proof.
  intros a b H P x s1. unfold s1. rewrite sm_run_add.
  set (Q := sm_rice_prog a b H P). set (K := sm_fresh P).
  assert (HK1 : K <> 1) by (unfold K, sm_fresh; lia).
  destruct (sm_incs_run prop_eqb eval Q K a 0 (sm_hstart x)) as (Hv1 & Hw1 & Hf1 & Hc1 & He1 & Hp1 & Hm1 & Hk1).
  { intros p Hp. apply sm_rice_fetch_a. exact Hp. }
  { reflexivity. }
  { reflexivity. }
  destruct (sm_incs_run prop_eqb eval Q (S K) b a (run_prog a Q (sm_hstart x)))
    as (Hv2 & Hw2 & Hf2 & Hc2 & He2 & Hp2 & Hm2 & Hk2).
  { intros p Hp. apply sm_rice_fetch_b. exact Hp. }
  { exact He1. }
  { rewrite Hp1. lia. }
  repeat split.
  - intro q. rewrite Hv2, !Hv1. cbn [M.vals M.core_of sm_hstart M.start M.start_core].
    assert (E1 : Nat.eqb (S K) K = false) by (apply Nat.eqb_neq; lia).
    assert (E2 : Nat.eqb K (S K) = false) by (apply Nat.eqb_neq; lia).
    assert (E3 : sm_hin x K = 0) by (unfold sm_hin; rewrite (proj2 (Nat.eqb_neq K 1) HK1); reflexivity).
    assert (E4 : sm_hin x (S K) = 0)
      by (unfold sm_hin; rewrite (proj2 (Nat.eqb_neq (S K) 1)) by (unfold K, sm_fresh; lia); reflexivity).
    destruct (Nat.eqb_spec q (S K)) as [-> | Hq1].
    + rewrite ?E1, ?E4, ?Nat.eqb_refl. lia.
    + destruct (Nat.eqb_spec q K) as [-> | Hq2].
      * rewrite ?E2, ?E3, ?Nat.eqb_refl. lia.
      * reflexivity.
  - intros q H1 H2. rewrite Hw2 by exact H2. rewrite Hw1 by exact H1. reflexivity.
  - rewrite Hf2, Hf1. reflexivity.
  - rewrite Hc2, Hc1. reflexivity.
  - exact He2.
  - rewrite Hp2. lia.
  - rewrite Hm2, Hm1. reflexivity.
  - rewrite Hk2, Hk1. reflexivity.
Qed.

(* The B-side twin of a state: the same core with the program counter at 1. *)
Definition sm_at1 (s : state) : state :=
  M.mkst (M.goto (M.core_of s) 1) (M.mu s) (M.cert s).

Lemma sm_at1_rel : forall (s : state) off len,
  M.pc (M.core_of s) = S off ->
  srel (fun _ => True) off len (sm_at1 s) s.
Proof.
  intros s off len Hp. unfold srel, sm_crel, sm_at1, M.goto. simpl.
  repeat split; auto. rewrite Hp. unfold sm_rj.
  destruct (Nat.leb_spec 1 1), (Nat.leb_spec 1 len); simpl; lia.
Qed.

(* ================================================================= *)
(* A final block that is reached from every input.                    *)
(* ================================================================= *)

Lemma sm_srel_agree : forall Sr off len (s t : state),
  srel Sr off len s t -> sm_hagree s t.
Proof.
  intros Sr off len s t ((Hv & _ & Hf & Hc & He & _) & Hm & Hk).
  unfold sm_hagree. repeat split; auto.
Qed.

(* If Q holds P as its last block, and from every input Q reaches a state
   that matches P's start, then Q behaves the same as P. *)
Lemma sm_final_hequiv : forall Q P off Sr,
  sm_embeds Q P off -> sm_within Sr P -> length Q = off + length P ->
  (forall x, exists T0, srel Sr off (length P) (sm_hstart x) (run_prog T0 Q (sm_hstart x))) ->
  hequiv Q P.
Proof.
  intros Q P off Sr Hemb Hwin HQ Hreach x. destruct (Hreach x) as [T0 HT].
  assert (Hall : forall m, srel Sr off (length P) (run_prog m P (sm_hstart x))
                                 (run_prog (T0 + m) Q (sm_hstart x))).
  { intro m. rewrite sm_run_add. apply (sm_block_run_final prop_eqb eval Sr Q P off Hemb Hwin HQ), HT. }
  split.
  - intros s [N [-> HN]].
    set (m := N - T0).
    assert (Es : run_prog (T0 + m) Q (sm_hstart x) = run_prog N Q (sm_hstart x))
      by (apply sm_halted_after; [unfold m; lia | exact HN]).
    pose proof (Hall m) as Hr. rewrite Es in Hr.
    exists (run_prog m P (sm_hstart x)). split.
    + exists m. split; [reflexivity |].
      unfold M.halted. destruct (M.next_instr P (M.core_of (run_prog m P (sm_hstart x)))) eqn:Hn;
        [| reflexivity].
      exfalso. apply (sm_block_not_halted prop_eqb eval Sr Q P off _ _ Hemb Hwin Hr); [congruence | exact HN].
    + apply sm_hagree_sym. exact (sm_srel_agree _ _ _ _ _ Hr).
  - intros t [m [-> Hm]].
    exists (run_prog (T0 + m) Q (sm_hstart x)). split.
    + exists (T0 + m). split; [reflexivity |].
      apply (sm_block_halted Sr Q P off (M.core_of (run_prog m P (sm_hstart x)))); auto.
      apply (Hall m).
    + apply sm_hagree_sym. exact (sm_srel_agree _ _ _ _ _ (Hall m)).
Qed.

(* ================================================================= *)
(* The reduction program, when H stops and when it does not.          *)
(* ================================================================= *)

Lemma sm_option_dec : forall (o : option E.mconf), o = None \/ ~ o = None.
Proof. intros [y |]; [right; discriminate | left; reflexivity]. Qed.

Lemma sm_fetch_none_out : forall (B : list instr) p, M.fetch B p = None -> ~ (1 <= p <= length B).
Proof.
  intros B p H Hr. destruct p as [| p]; [lia |]. simpl in H.
  apply nth_error_None in H. lia.
Qed.

(* The state reached after the block of H, given a step count n0 at which
   H has stopped and before which it had not. *)
Lemma sm_rice_reach : forall H a b P x,
  MM2_HALTING (H, a, b) ->
  exists T0, srel (fun r => r < sm_fresh P) (length (sm_rice_pre (sm_fresh P) a b H)) (length P)
               (sm_hstart x) (run_prog T0 (sm_rice_prog a b H P) (sm_hstart x)).
Proof.
  intros H a b P x Hh.
  set (Q := sm_rice_prog a b H P). set (K := sm_fresh P).
  set (Mp := map sm_of_mm2 H).
  set (B := sm_hblock K H).
  assert (HB : B = map (sm_mk K) Mp) by reflexivity.
  assert (HK1 : K <> 1) by (unfold K, sm_fresh; lia).
  assert (HK0 : 2 <= K) by (unfold K, sm_fresh; lia).
  apply sm_mm2_terminates_iff in Hh. fold Mp in Hh. destruct Hh as [n1 Hn1].
  destruct (sm_least (fun n => E.mstep Mp (E.mrun n Mp (1, (a, b))) = None)
              (fun n => sm_option_dec _) n1 Hn1) as [n0 [Hn0 Hlt]].
  destruct (sm_rice_phase1 a b H P x) as (Hv1 & Hw1 & Hf1 & Hc1 & He1 & Hp1 & Hm1 & Hk1).
  fold Q K in Hv1, Hw1, Hf1, Hc1, He1, Hp1, Hm1, Hk1.
  set (s1 := run_prog (a + b) Q (sm_hstart x)) in *.
  set (sB := sm_at1 s1).
  assert (HeB : M.err (M.core_of sB) = false) by exact He1.
  assert (HwinB : sm_win K (M.core_of sB) = (1, (a, b))).
  { unfold sm_win, sB, sm_at1, M.goto. cbn [M.pc M.vals M.core_of]. rewrite !Hv1. rewrite Nat.eqb_refl.
    replace (Nat.eqb (S K) K) with false by (symmetry; apply Nat.eqb_neq; lia).
    rewrite Nat.eqb_refl. reflexivity. }
  (* The standalone run of the block of H. *)
  destruct (sm_mk_run Mp K n0 sB HeB) as (HwB & HvB & HwwB & HfB & HcB & HeB2 & HmB & HkB).
  rewrite HwinB in HwB. rewrite <- HB in HwB, HvB, HwwB, HfB, HcB, HeB2, HmB, HkB.
  destruct (E.mrun n0 Mp (1, (a, b))) as [p' [a' b']] eqn:Erun.
  assert (HhB : M.next_instr B (M.core_of (run_prog n0 B sB)) = None).
  { rewrite HB. apply sm_mk_halted; [rewrite <- HB; exact HeB2 |]. rewrite <- HB, HwB. exact Hn0. }
  assert (HgoB : forall m, m < n0 -> M.next_instr B (M.core_of (run_prog m B sB)) <> None).
  { intros m Hm Hn. apply (Hlt m Hm).
    destruct (sm_mk_run Mp K m sB HeB) as (Hw' & _ & _ & _ & _ & He' & _).
    rewrite HwinB in Hw'. rewrite <- Hw'. apply sm_mk_halted; [exact He' |]. rewrite <- HB. exact Hn. }
  (* The block of H inside Q. *)
  assert (Hrel1 : srel (fun _ => True) (a + b) (length B) sB s1) by (apply sm_at1_rel; exact Hp1).
  pose proof (sm_block_run_mid prop_eqb eval (fun _ => True) Q B (a + b) (sm_rice_embeds_h a b H P)
                (sm_within_all B) n0 sB s1 Hrel1 HgoB) as Hrel2.
  set (s2 := run_prog n0 Q s1) in *.
  destruct Hrel2 as ((Hv2 & Hw2 & Hf2 & Hc2 & He2 & Hp2) & Hm2 & Hk2).
  assert (Hpc' : M.pc (M.core_of (run_prog n0 B sB)) = p') by (unfold sm_win in HwB; congruence).
  assert (Hout : ~ (1 <= p' <= length B)).
  { rewrite <- Hpc'. apply sm_fetch_none_out. unfold M.next_instr in HhB. rewrite HeB2 in HhB.
    destruct (M.fetch B (M.pc (M.core_of (run_prog n0 B sB)))) as [i |] eqn:Hf; [| reflexivity].
    exfalso. destruct i; try discriminate. apply (sm_hblock_no_halt K H).
    rewrite Hpc' in Hf. destruct p' as [| q]; [discriminate |]. simpl in Hf.
    eapply nth_error_In. exact Hf. }
  set (L1 := S (a + b + length (sm_hblock K H))).
  assert (Hpc2 : M.pc (M.core_of s2) = L1).
  { rewrite Hp2, Hpc', sm_rj_out by exact Hout. unfold L1. fold B. lia. }
  assert (Hva : M.vals (M.core_of s2) K = a') by (rewrite <- Hv2; unfold sm_win in HwB; congruence).
  assert (Hvb : M.vals (M.core_of s2) (S K) = b') by (rewrite <- Hv2; unfold sm_win in HwB; congruence).
  assert (Hvo : forall q, q <> K -> q <> S K -> M.vals (M.core_of s2) q = sm_hin x q).
  { intros q Hq1 Hq2. rewrite <- Hv2, HvB by assumption. unfold sB, sm_at1, M.goto. simpl.
    rewrite Hv1. apply Nat.eqb_neq in Hq1. apply Nat.eqb_neq in Hq2. rewrite Hq1, Hq2. reflexivity. }
  assert (Hwo : forall q, q <> K -> q <> S K -> M.vers (M.core_of s2) q = 0).
  { intros q Hq1 Hq2. rewrite <- (Hw2 q I), HwwB by assumption. unfold sB, sm_at1, M.goto. simpl.
    apply Hw1; assumption. }
  assert (Hf2' : M.facts (M.core_of s2) = []) by (rewrite <- Hf2, HfB; exact Hf1).
  assert (Hc2' : M.chan (M.core_of s2) = None) by (rewrite <- Hc2, HcB; exact Hc1).
  assert (He2' : M.err (M.core_of s2) = false) by (rewrite <- He2; exact HeB2).
  assert (Hm2' : M.mu s2 = 0) by (rewrite <- Hm2, HmB; exact Hm1).
  assert (Hk2' : M.cert s2 = false) by (rewrite <- Hk2, HkB; exact Hk1).
  (* Empty K, then K + 1. *)
  destruct (sm_clear_run prop_eqb eval Q K L1 a' s2 (sm_rice_fetch_clear1 a b H P) He2' Hpc2 Hva)
    as (Hv3 & Hw3 & Hf3 & Hc3 & He3 & Hp3 & Hm3 & Hk3).
  set (s3 := run_prog (S a') Q s2) in *.
  assert (Hvb3 : M.vals (M.core_of s3) (S K) = b').
  { rewrite Hv3. replace (Nat.eqb (S K) K) with false by (symmetry; apply Nat.eqb_neq; lia). exact Hvb. }
  destruct (sm_clear_run prop_eqb eval Q (S K) (S L1) b' s3 (sm_rice_fetch_clear2 a b H P) He3 Hp3 Hvb3)
    as (Hv4 & Hw4 & Hf4 & Hc4 & He4 & Hp4 & Hm4 & Hk4).
  set (s4 := run_prog (S b') Q s3) in *.
  exists (a + b + n0 + S a' + S b').
  replace (run_prog (a + b + n0 + S a' + S b') Q (sm_hstart x)) with s4
    by (unfold s4, s3, s2, s1; rewrite !sm_run_add; reflexivity).
  split; [| split].
  - repeat split.
    + intro q. cbn [M.vals M.core_of sm_hstart M.start M.start_core]. rewrite Hv4, Hv3.
      destruct (Nat.eqb_spec q (S K)) as [-> | Hq1].
      * unfold sm_hin. replace (Nat.eqb (S K) 1) with false by (symmetry; apply Nat.eqb_neq; lia).
        reflexivity.
      * destruct (Nat.eqb_spec q K) as [-> | Hq2].
        -- unfold sm_hin. replace (Nat.eqb K 1) with false by (symmetry; apply Nat.eqb_neq; lia).
           reflexivity.
        -- symmetry. apply Hvo; assumption.
    + intros r Hr. cbn [M.vers M.core_of sm_hstart M.start M.start_core].
      rewrite Hw4 by lia. rewrite Hw3 by lia. symmetry. apply Hwo; lia.
    + cbn [M.facts M.core_of sm_hstart M.start M.start_core]. rewrite Hf4, Hf3, Hf2'. reflexivity.
    + cbn [M.chan M.core_of sm_hstart M.start M.start_core]. rewrite Hc4, Hc3, Hc2'. reflexivity.
    + cbn [M.err M.core_of sm_hstart M.start M.start_core]. rewrite He4. reflexivity.
    + cbn [M.pc M.core_of sm_hstart M.start M.start_core]. rewrite Hp4, sm_rice_pre_length.
      unfold sm_rj. destruct (Nat.leb_spec 1 1), (Nat.leb_spec 1 (length P)); simpl; unfold L1; lia.
  - cbn [M.mu sm_hstart M.start]. rewrite Hm4, Hm3, Hm2'. reflexivity.
  - cbn [M.cert sm_hstart M.start]. rewrite Hk4, Hk3, Hk2'. reflexivity.
Qed.

(* If H stops, the reduction program behaves the same as P. *)
Theorem sm_rice_prog_halts : forall H a b P,
  MM2_HALTING (H, a, b) -> hequiv (sm_rice_prog a b H P) P.
Proof.
  intros H a b P Hh.
  apply (sm_final_hequiv (sm_rice_prog a b H P) P (length (sm_rice_pre (sm_fresh P) a b H))
           (fun r => r < sm_fresh P)).
  - apply sm_rice_embeds_p.
  - apply sm_within_fresh.
  - apply sm_rice_length.
  - intro x. apply sm_rice_reach. exact Hh.
Qed.

(* If H runs forever, so does the reduction program, on every input. *)
Theorem sm_rice_prog_diverges : forall H a b P,
  ~ MM2_HALTING (H, a, b) ->
  forall x N, ~ M.halted (sm_rice_prog a b H P) (M.core_of (run_prog N (sm_rice_prog a b H P) (sm_hstart x))).
Proof.
  intros H a b P Hnh x N HN.
  set (Q := sm_rice_prog a b H P) in *. set (K := sm_fresh P).
  set (Mp := map sm_of_mm2 H).
  set (B := sm_hblock K H).
  assert (HB : B = map (sm_mk K) Mp) by reflexivity.
  destruct (sm_rice_phase1 a b H P x) as (Hv1 & Hw1 & Hf1 & Hc1 & He1 & Hp1 & Hm1 & Hk1).
  fold Q K in Hv1, Hw1, Hf1, Hc1, He1, Hp1, Hm1, Hk1.
  set (s1 := run_prog (a + b) Q (sm_hstart x)) in *.
  set (sB := sm_at1 s1).
  assert (HeB : M.err (M.core_of sB) = false) by exact He1.
  assert (HwinB : sm_win K (M.core_of sB) = (1, (a, b))).
  { unfold sm_win, sB, sm_at1, M.goto. cbn [M.pc M.vals M.core_of]. rewrite !Hv1. rewrite Nat.eqb_refl.
    replace (Nat.eqb (S K) K) with false by (symmetry; apply Nat.eqb_neq; lia).
    rewrite Nat.eqb_refl. reflexivity. }
  assert (HgoB : forall m, M.next_instr B (M.core_of (run_prog m B sB)) <> None).
  { intros m Hn. apply Hnh. apply sm_mm2_terminates_iff. exists m. fold Mp.
    destruct (sm_mk_run Mp K m sB HeB) as (Hw' & _ & _ & _ & _ & He' & _).
    rewrite HwinB in Hw'. rewrite <- Hw'. apply sm_mk_halted; [exact He' |]. rewrite <- HB. exact Hn. }
  assert (Hrel1 : srel (fun _ => True) (a + b) (length B) sB s1) by (apply sm_at1_rel; exact Hp1).
  pose proof (sm_block_run_mid prop_eqb eval (fun _ => True) Q B (a + b) (sm_rice_embeds_h a b H P)
                (sm_within_all B) N sB s1 Hrel1 (fun m _ => HgoB m)) as Hrel2.
  apply (sm_block_not_halted prop_eqb eval (fun _ => True) Q B (a + b) _ _ (sm_rice_embeds_h a b H P)
           (sm_within_all B) Hrel2 (HgoB N)).
  unfold s1. rewrite <- sm_run_add.
  rewrite (sm_halted_after prop_eqb eval N (a + b + N) Q (sm_hstart x)) by (lia || exact HN).
  exact HN.
Qed.

(* ================================================================= *)
(* A program that never stops.                                        *)
(* ================================================================= *)

Definition sm_hloop : list instr := [M.INC 0; M.DEC 0 1].

Lemma sm_hloop_runs : forall n s,
  M.err (M.core_of s) = false ->
  (M.pc (M.core_of s) = 1 \/ (M.pc (M.core_of s) = 2 /\ M.vals (M.core_of s) 0 <> 0)) ->
  M.err (M.core_of (run_prog n sm_hloop s)) = false /\
  (M.pc (M.core_of (run_prog n sm_hloop s)) = 1 \/
   (M.pc (M.core_of (run_prog n sm_hloop s)) = 2 /\ M.vals (M.core_of (run_prog n sm_hloop s)) 0 <> 0)).
Proof.
  induction n as [| n IH]; intros s He Hp; [auto |].
  rewrite sm_run_succ.
  destruct Hp as [Hp | [Hp Hv]].
  - assert (E : M.core_of (step sm_hloop s) =
                M.write (M.core_of s) 0 (S (M.vals (M.core_of s) 0)) 2).
    { unfold step, M.next_instr. rewrite He, Hp. simpl. unfold M.cexec. rewrite He, Hp. reflexivity. }
    apply IH; rewrite E; cbn [M.err M.write M.pc M.vals].
    + exact He.
    + right. split; [reflexivity |]. unfold M.upd. simpl. discriminate.
  - destruct (M.vals (M.core_of s) 0) as [| v] eqn:Ev; [congruence |].
    assert (E : M.core_of (step sm_hloop s) = M.write (M.core_of s) 0 v 1).
    { unfold step, M.next_instr. rewrite He, Hp. simpl. unfold M.cexec. rewrite He, Ev. reflexivity. }
    apply IH; rewrite E; cbn [M.err M.write M.pc M.vals].
    + exact He.
    + left. reflexivity.
Qed.

Lemma sm_hloop_diverges : forall x N,
  ~ M.halted sm_hloop (M.core_of (run_prog N sm_hloop (sm_hstart x))).
Proof.
  intros x N HN. destruct (sm_hloop_runs N (sm_hstart x) eq_refl (or_introl eq_refl)) as [He Hp].
  unfold M.halted, M.next_instr in HN. rewrite He in HN.
  destruct Hp as [Hp | [Hp _]]; rewrite Hp in HN; discriminate.
Qed.

Lemma sm_never_hequiv : forall P Q,
  (forall x N, ~ M.halted P (M.core_of (run_prog N P (sm_hstart x)))) ->
  (forall x N, ~ M.halted Q (M.core_of (run_prog N Q (sm_hstart x)))) ->
  hequiv P Q.
Proof.
  intros P Q HP HQ x. split.
  - intros s [N [-> HN]]. exfalso. exact (HP x N HN).
  - intros t [N [-> HN]]. exfalso. exact (HQ x N HN).
Qed.

(* ================================================================= *)
(* Rice's theorem on the host machine.                                *)
(* ================================================================= *)

(* A property of programs that respects behaving the same. *)
Definition sm_hext (Pi : list instr -> Prop) : Prop :=
  forall p q, hequiv p q -> Pi p -> Pi q.

Lemma sm_hext_compl : forall Pi, sm_hext Pi -> sm_hext (complement Pi).
Proof.
  intros Pi H p q Hpq Hnp Hq. apply Hnp. apply (H q p); [apply sm_hequiv_sym, Hpq | exact Hq].
Qed.

Lemma sm_host_rice_loop : forall (Pi : list instr -> Prop) y,
  sm_hext Pi -> Pi y -> ~ Pi sm_hloop -> undecidable Pi.
Proof.
  intros Pi y Hext Hy Hloop.
  apply undecidability_from_complement.
  apply (undecidability_from_reducibility MM2_HALTING_compl_undec).
  exists (fun q : MM2_PROBLEM => let '(H, a, b) := q in sm_rice_prog a b H y).
  intros [[H a] b]. unfold complement. split.
  - intros Hnh HPi. apply Hloop.
    apply (Hext (sm_rice_prog a b H y)); [| exact HPi].
    apply sm_never_hequiv; [apply sm_rice_prog_diverges, Hnh | apply sm_hloop_diverges].
  - intros HnPi Hh. apply HnPi.
    apply (Hext y); [apply sm_hequiv_sym, sm_rice_prog_halts, Hh | exact Hy].
Qed.

(* Rice's theorem: every property of host programs that respects behaving
   the same, holds of some program and fails of another, is undecidable. *)
Theorem sm_host_rice : forall (Pi : list instr -> Prop) y n,
  sm_hext Pi -> Pi y -> ~ Pi n -> undecidable Pi.
Proof.
  intros Pi y n Hext Hy Hn Hdec.
  destruct Hdec as [d Hd] eqn:Hdec'.
  destruct (d sm_hloop) eqn:Hdl.
  - (* Pi holds of the loop: work with the complement. *)
    assert (Hl : Pi sm_hloop) by (apply Hd; exact Hdl).
    apply (undecidability_from_complement (p := Pi)); [| exact Hdec].
    apply (sm_host_rice_loop (complement Pi) n).
    + apply sm_hext_compl, Hext.
    + exact Hn.
    + intro H. exact (H Hl).
  - assert (Hl : ~ Pi sm_hloop) by (intro H; apply Hd in H; congruence).
    exact (sm_host_rice_loop Pi y Hext Hy Hl Hdec).
Qed.

End HostRice.

(* ================================================================= *)
(* Assumption audit.                                                  *)
(* ================================================================= *)

Print Assumptions sm_rice_prog_halts.
Print Assumptions sm_rice_prog_diverges.
Print Assumptions sm_hloop_diverges.
Print Assumptions sm_host_rice.
