(** SmTally.v: what a host program's record looks like when it stops, as
    numbers a fixed program can compute.

    SmInterp.v runs a host program on plain data and reports only register 0.
    This file runs the same machine with the ledger and the flag added, and
    reports five numbers about the final state of a program that stops:

      sel 0   out    register 0
      sel 1   nf     how many facts are in the fact table
      sel 2   bc     the commits the replay must pay for
      sel 3   cc     the certifies the replay must pay for (0 or 1)
      sel 4   fe     1 if the trap latch is up, else 0

    With rest = ledger - nf - fe, cc is 1 when the flag is up and 0
    otherwise, and bc is rest - cc.

    What is proved:
      1. The plain machine with ledger and flag stays related to the host
         machine step for step [sm2_krun_rel].
      2. The five numbers of the plain final state equal the five numbers
         read off the host's final state [sm2_comp_rel].
      3. Every state reachable from a start satisfies the record invariant
         [sm2_reach_inv]: at most 16 facts; the ledger is the fact count plus
         the latch plus the number of paid commits and certifies; no channel
         means no paid commit; a raised flag means at least one commit and one
         certify were paid.
      4. So the five numbers describe the final record exactly: ledger =
         nf + bc + cc + fe, the flag is up exactly when cc >= 1, the channel
         is full exactly when bc >= 1, bc >= 1 forces nf >= 1, and nf <= 16
         [sm2_final_numbers].
      5. The evaluator of the recursion theorem with a selector: run the
         program numbered t on the number of the specialised program, run
         the program that comes out on x, and report component sel
         [sm2_ev], with its specification [sm2_ev_spec] and its monotonicity
         in the fuel.

    Every function defined for evaluation is a plain recursion over numbers,
    booleans, pairs, options and lists, so SmTallyL.v can turn it into a term
    of L.

    Dependencies: Coq standard library, EarnedMulti.v, UniversalCodes.v,
    SmHostBlocks.v, SmCodes.v and SmInterp.v. No axioms and no unfinished proofs. *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the host machine, here the record of a stopped host program as five numbers, and the evaluator that reports one of them.
   The host machine's link to the abstract record (a CertificationSystem
   with the trace floor, a Thiele-complete machine, and the halting problem
   of U) lives in UniversalInterpreterLinks.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.EarnedMulti Minimal.UniversalCodes.
Require Import Minimal.SmHostBlocks Minimal.SmCodes Minimal.SmInterp.
Module M := Minimal.EarnedMulti.
Module UC := Minimal.UniversalCodes.
Unset Implicit Arguments.

Local Notation hinstr := (@M.instr UC.hprop).
Local Notation hcore := (@M.core UC.hprop).
Local Notation hstate := (@M.state UC.hprop).
Local Notation hexec := (M.exec UC.hprop_eqb UC.heval).
Local Notation hcexec := (M.cexec UC.hprop_eqb UC.heval).
Local Notation hstep := (M.step UC.hprop_eqb UC.heval).
Local Notation hrun_prog := (M.run_prog UC.hprop_eqb UC.heval).
Local Notation hfun := (sm_hfun UC.hprop_eqb UC.heval).
Local Notation hends := (sm_hends UC.hprop_eqb UC.heval).

(* ================================================================= *)
(* The plain machine with a ledger and a flag.                        *)
(* ================================================================= *)

(* The plain core, the ledger, the flag. *)
Definition sm2_S : Type := (sm_KC * (nat * bool))%type.

Definition sm2_kcost (i : sm_ki) : nat :=
  match i with
  | sm_KCheck _ => 1
  | sm_KCommit _ => 1
  | sm_KCertify => 1
  | _ => 0
  end.

Definition sm2_kfires (i : sm_ki) (ch : option (nat * nat)) : bool :=
  match i with
  | sm_KCertify => match ch with Some _ => true | None => false end
  | _ => false
  end.

Definition sm2_kstep (P : list sm_ki) (k : sm2_S) : sm2_S :=
  if sm_khalted P (fst k) then k else
  match sm_kfetch P (fst (snd (snd (fst k)))) with
  | None => k
  | Some i =>
      (sm_kstep P (fst k),
       (fst (snd k) + sm2_kcost i,
        orb (snd (snd k)) (sm2_kfires i (fst (snd (snd (snd (snd (fst k)))))))))
  end.

Fixpoint sm2_krun (n : nat) (P : list sm_ki) (k : sm2_S) : sm2_S :=
  match n with 0 => k | S m => sm2_krun m P (sm2_kstep P k) end.

Definition sm2_kstart (x : nat) : sm2_S := (sm_kstart x, (0, false)).

(* The five numbers of a final plain state. *)
Definition sm2_fe (k : sm2_S) : nat :=
  if snd (snd (snd (snd (snd (fst k))))) then 1 else 0.

Definition sm2_nf (k : sm2_S) : nat := length (fst (snd (snd (snd (fst k))))).

Definition sm2_rest (k : sm2_S) : nat := fst (snd k) - sm2_nf k - sm2_fe k.

Definition sm2_comp (sel : nat) (k : sm2_S) : nat :=
  if Nat.eqb sel 0 then nth 0 (fst (fst k)) 0
  else if Nat.eqb sel 1 then sm2_nf k
  else if Nat.eqb sel 2 then (sm2_rest k - (if snd (snd k) then 1 else 0))
  else if Nat.eqb sel 3 then (if snd (snd k) then 1 else 0)
  else sm2_fe k.

Definition sm2_tal (sel fuel : nat) (P : list sm_ki) (x : nat) : option nat :=
  if sm_khalted P (fst (sm2_krun fuel P (sm2_kstart x)))
  then Some (sm2_comp sel (sm2_krun fuel P (sm2_kstart x)))
  else None.

(* The evaluator with a selector: run the program numbered t on the number of
   the program specialised to c, run the program whose number comes out on x,
   and report component sel of its final record. *)
Definition sm2_ev (sel t fuel x c : nat) : option nat :=
  match sm_kout fuel (sm_kpdec t) (sm_kspec c) with
  | Some d => sm2_tal sel fuel (sm_kpdec d) x
  | None => None
  end.

(* ================================================================= *)
(* The plain machine is the host machine, with the ledger and flag.   *)
(* ================================================================= *)

Definition sm2_rel (s : hstate) (t : sm2_S) : Prop :=
  sm_krel (M.core_of s) (fst t) /\ M.mu s = fst (snd t) /\ M.cert s = snd (snd t).

Lemma sm2_cost_eq : forall i, M.cost (sm_of_ki i) = sm2_kcost i.
Proof. intros []; reflexivity. Qed.

Lemma sm2_rel_step : forall P s t, sm2_rel s t ->
  sm2_rel (hstep (map sm_of_ki P) s) (sm2_kstep P t).
Proof.
  intros P s [k [m ct]] (Hk & Hm & Hc). cbn [fst snd] in Hk, Hm, Hc.
  unfold sm2_kstep. cbn [fst snd].
  destruct (sm_khalted P k) eqn:Hh.
  - assert (Hhalt : M.halted (map sm_of_ki P) (M.core_of s))
      by (apply (sm_krel_halted P _ _ Hk); exact Hh).
    unfold hstep, M.step. unfold M.halted in Hhalt. rewrite Hhalt.
    unfold sm2_rel. cbn [fst snd]. repeat split; auto.
  - destruct k as [vs [ws [pc [fs [ch er]]]]]. cbn [fst snd] in Hk, Hh |- *.
    pose proof Hk as (Hv & Hw & Hp & Hf & Hch & He).
    unfold sm_khalted in Hh. cbn [fst snd] in Hh.
    destruct er; [discriminate |].
    destruct (sm_kfetch P pc) as [i |] eqn:Hfi; [| discriminate].
    assert (Hi : i <> sm_KHalt) by (intro E; rewrite E in Hh; discriminate).
    assert (Hn : M.next_instr (map sm_of_ki P) (M.core_of s) = Some (sm_of_ki i)).
    { unfold M.next_instr. rewrite He, Hp, sm_fetch_of, Hfi.
      destruct i; try reflexivity. exfalso. apply Hi. reflexivity. }
    assert (Hst : hstep (map sm_of_ki P) s = hexec s (sm_of_ki i))
      by (unfold hstep, M.step; rewrite Hn; reflexivity).
    rewrite Hst.
    pose proof (sm_krel_step P (M.core_of s) _ Hk) as Hkr.
    unfold sm_cstep in Hkr. rewrite Hn in Hkr.
    unfold sm2_rel. cbn [fst snd].
    split.
    + unfold hexec, M.exec. cbn [M.core_of]. exact Hkr.
    + unfold hexec, M.exec. cbn [M.mu M.cert]. rewrite Hm, Hc, sm2_cost_eq.
      split; [reflexivity |].
      f_equal. destruct i; try reflexivity.
      cbn [sm2_kfires M.fires sm_of_ki]. unfold M.certify_ok.
      rewrite He, Hch. destruct ch; reflexivity.
Qed.

Lemma sm2_krun_rel : forall n P s t, sm2_rel s t ->
  sm2_rel (hrun_prog n (map sm_of_ki P) s) (sm2_krun n P t).
Proof.
  induction n as [| n IH]; intros P s t H; [exact H |].
  simpl. apply IH, sm2_rel_step, H.
Qed.

Lemma sm2_rel_start : forall x, sm2_rel (sm_hstart x) (sm2_kstart x).
Proof.
  intro x. unfold sm2_rel, sm2_kstart. cbn [fst snd]. split; [apply sm_krel_start |].
  split; reflexivity.
Qed.

Definition sm2_rfe (s : hstate) : nat := if M.err (M.core_of s) then 1 else 0.
Definition sm2_rrest (s : hstate) : nat :=
  M.mu s - length (M.facts (M.core_of s)) - sm2_rfe s.

Definition sm2_rcomp (sel : nat) (s : hstate) : nat :=
  if Nat.eqb sel 0 then M.vals (M.core_of s) 0
  else if Nat.eqb sel 1 then length (M.facts (M.core_of s))
  else if Nat.eqb sel 2 then (sm2_rrest s - (if M.cert s then 1 else 0))
  else if Nat.eqb sel 3 then (if M.cert s then 1 else 0)
  else sm2_rfe s.

Lemma sm2_comp_rel : forall sel s t, sm2_rel s t -> sm2_comp sel t = sm2_rcomp sel s.
Proof.
  intros sel s [k [m ct]] (Hk & Hm & Hc). cbn [fst snd] in Hk, Hm, Hc.
  destruct k as [vs [ws [pc [fs [ch er]]]]].
  destruct Hk as (Hv & Hw & Hp & Hf & Hch & He).
  cbn [fst snd] in *.
  assert (Hfe : sm2_fe (((vs, (ws, (pc, (fs, (ch, er))))) : sm_KC), (m, ct)) = sm2_rfe s)
    by (unfold sm2_fe, sm2_rfe; cbn [fst snd]; rewrite He; reflexivity).
  assert (Hnf : sm2_nf (((vs, (ws, (pc, (fs, (ch, er))))) : sm_KC), (m, ct)) = length (M.facts (M.core_of s)))
    by (unfold sm2_nf; cbn [fst snd]; rewrite Hf, map_length; reflexivity).
  assert (Hrest : sm2_rest (((vs, (ws, (pc, (fs, (ch, er))))) : sm_KC), (m, ct)) = sm2_rrest s)
    by (unfold sm2_rest, sm2_rrest; rewrite Hfe, Hnf; cbn [fst snd]; rewrite Hm; reflexivity).
  unfold sm2_comp, sm2_rcomp. cbn [fst snd].
  destruct (Nat.eqb sel 0); [rewrite Hv; reflexivity |].
  destruct (Nat.eqb sel 1); [exact Hnf |].
  destruct (Nat.eqb sel 2); [rewrite Hc, Hrest; reflexivity |].
  destruct (Nat.eqb sel 3); [rewrite Hc; reflexivity |].
  exact Hfe.
Qed.

Lemma sm2_krun_halted : forall n P k, sm_khalted P (fst k) = true -> sm2_krun n P k = k.
Proof.
  induction n as [| n IH]; intros P k H; [reflexivity |].
  simpl. unfold sm2_kstep. rewrite H. apply IH, H.
Qed.

Lemma sm2_krun_add : forall a b P k, sm2_krun (a + b) P k = sm2_krun b P (sm2_krun a P k).
Proof. induction a as [| a IH]; intros; simpl; [reflexivity | apply IH]. Qed.

Lemma sm2_tal_mono : forall sel n n' P x m, n <= n' ->
  sm2_tal sel n P x = Some m -> sm2_tal sel n' P x = Some m.
Proof.
  intros sel n n' P x m Hle H. unfold sm2_tal in *.
  destruct (sm_khalted P (fst (sm2_krun n P (sm2_kstart x)))) eqn:Hh; [| discriminate].
  replace n' with (n + (n' - n)) by lia. rewrite sm2_krun_add.
  rewrite (sm2_krun_halted (n' - n) P _ Hh), Hh. exact H.
Qed.

(* The plain final state gives the numbers read off the host's final state. *)
Lemma sm2_tal_real : forall sel n P x m,
  sm2_tal sel n P x = Some m <->
  M.halted (map sm_of_ki P) (M.core_of (hrun_prog n (map sm_of_ki P) (sm_hstart x))) /\
  m = sm2_rcomp sel (hrun_prog n (map sm_of_ki P) (sm_hstart x)).
Proof.
  intros sel n P x m.
  pose proof (sm2_krun_rel n P _ _ (sm2_rel_start x)) as Hr.
  pose proof (sm2_comp_rel sel _ _ Hr) as Hcomp.
  assert (Hh : M.halted (map sm_of_ki P) (M.core_of (hrun_prog n (map sm_of_ki P) (sm_hstart x))) <->
               sm_khalted P (fst (sm2_krun n P (sm2_kstart x))) = true)
    by (apply sm_krel_halted, Hr).
  unfold sm2_tal. split.
  - intro H. destruct (sm_khalted P (fst (sm2_krun n P (sm2_kstart x)))) eqn:Hh'; [| discriminate].
    injection H as <-. split; [apply Hh; reflexivity | exact Hcomp].
  - intros [H1 H2]. apply Hh in H1. rewrite H1. rewrite Hcomp, H2. reflexivity.
Qed.

(* ================================================================= *)
(* The record invariant.                                              *)
(* ================================================================= *)

Definition sm2_inv (s : hstate) : Prop :=
  length (M.facts (M.core_of s)) <= 16 /\
  length (M.facts (M.core_of s)) + sm2_rfe s <= M.mu s /\
  (M.chan (M.core_of s) = None -> M.mu s = length (M.facts (M.core_of s)) + sm2_rfe s) /\
  (M.chan (M.core_of s) <> None ->
     length (M.facts (M.core_of s)) + sm2_rfe s + 1 <= M.mu s /\ 1 <= length (M.facts (M.core_of s))) /\
  (M.cert s = true ->
     M.chan (M.core_of s) <> None /\ length (M.facts (M.core_of s)) + sm2_rfe s + 2 <= M.mu s).

Lemma sm2_inv_start : forall vs, sm2_inv (M.start vs).
Proof.
  intro vs. unfold sm2_inv, sm2_rfe. cbn [M.start M.core_of M.start_core M.facts M.chan M.err M.mu M.cert length].
  split; [lia |]. split; [lia |]. split; [intros _; lia |].
  split; [intro Hx; exfalso; apply Hx; reflexivity |].
  intro Hx; discriminate Hx.
Qed.

Lemma sm2_inv_exec : forall (s : hstate) (i : hinstr),
  M.err (M.core_of s) = false -> i <> M.HALT -> sm2_inv s -> sm2_inv (hexec s i).
Proof.
  intros s i Ee Hnh Hinv.
  destruct Hinv as (H16 & Hge & Hnone & Hsome & Hcert).
  unfold sm2_rfe in *. rewrite Ee in *. simpl in *.
  destruct i as [r | r j | | p r | p r |].
  - destruct (sm_plain_exec UC.hprop_eqb UC.heval s (M.INC r) eq_refl) as (Hf & Hc & He & Hm & Hk).
    unfold sm2_inv, sm2_rfe. rewrite Hf, Hc, He, Hm, Hk, Ee. simpl.
    refine (conj _ (conj _ (conj _ (conj _ _)))).
    + exact H16.
    + lia.
    + intro Hy. specialize (Hnone Hy). lia.
    + intro Hy. destruct (Hsome Hy). split; lia.
    + intro Hy. destruct (Hcert Hy). split; [assumption | lia].
  - destruct (sm_plain_exec UC.hprop_eqb UC.heval s (M.DEC r j) eq_refl) as (Hf & Hc & He & Hm & Hk).
    unfold sm2_inv, sm2_rfe. rewrite Hf, Hc, He, Hm, Hk, Ee. simpl.
    refine (conj _ (conj _ (conj _ (conj _ _)))).
    + exact H16.
    + lia.
    + intro Hy. specialize (Hnone Hy). lia.
    + intro Hy. destruct (Hsome Hy). split; lia.
    + intro Hy. destruct (Hcert Hy). split; [assumption | lia].
  - exfalso. apply Hnh. reflexivity.
  - unfold sm2_inv, sm2_rfe, hexec, M.exec, M.cexec. cbn [M.core_of M.mu M.cert]. rewrite Ee.
    destruct (M.check_ok UC.heval (M.core_of s) p r) eqn:Hok.
    + unfold M.check_ok in Hok. apply andb_true_iff in Hok as [Hok1 Hok2].
      apply Nat.ltb_lt in Hok2. unfold M.fact_cap in Hok2.
      unfold M.record_fact. cbn [M.facts M.chan M.err M.cost M.fires length]. rewrite Ee.
      refine (conj _ (conj _ (conj _ (conj _ _)))).
      * lia.
      * lia.
      * intro Hy. specialize (Hnone Hy). lia.
      * intro Hy. destruct (Hsome Hy). split; lia.
      * rewrite orb_false_r. intro Hy. destruct (Hcert Hy). split; [assumption | lia].
    + unfold M.trap. cbn [M.facts M.chan M.err M.cost M.fires length].
      refine (conj _ (conj _ (conj _ (conj _ _)))).
      * exact H16.
      * lia.
      * intro Hy. specialize (Hnone Hy). lia.
      * intro Hy. destruct (Hsome Hy). split; lia.
      * rewrite orb_false_r. intro Hy. destruct (Hcert Hy). split; [assumption | lia].
  - unfold sm2_inv, sm2_rfe, hexec, M.exec, M.cexec. cbn [M.core_of M.mu M.cert]. rewrite Ee.
    destruct (M.commit_ok UC.hprop_eqb (M.core_of s) p r) eqn:Hok.
    + unfold M.commit_ok in Hok. apply andb_true_iff in Hok as [_ Hok].
      assert (Hl : 1 <= length (M.facts (M.core_of s))).
      { destruct (M.facts (M.core_of s)); [discriminate Hok | simpl; lia]. }
      unfold M.commit_to. cbn [M.facts M.chan M.err M.cost M.fires length]. rewrite Ee.
      refine (conj _ (conj _ (conj _ (conj _ _)))).
      * exact H16.
      * lia.
      * intro Hy. discriminate Hy.
      * intro Hy. split; lia.
      * rewrite orb_false_r. intro Hy. destruct (Hcert Hy). split; [discriminate | lia].
    + unfold M.trap. cbn [M.facts M.chan M.err M.cost M.fires length].
      refine (conj _ (conj _ (conj _ (conj _ _)))).
      * exact H16.
      * lia.
      * intro Hy. specialize (Hnone Hy). lia.
      * intro Hy. destruct (Hsome Hy). split; lia.
      * rewrite orb_false_r. intro Hy. destruct (Hcert Hy). split; [assumption | lia].
  - unfold sm2_inv, sm2_rfe, hexec, M.exec, M.cexec. cbn [M.core_of M.mu M.cert]. rewrite Ee.
    destruct (M.certify_ok (M.core_of s)) eqn:Hok.
    + unfold M.certify_ok in Hok. apply andb_true_iff in Hok as [_ Hok].
      assert (Hc : M.chan (M.core_of s) <> None).
      { destruct (M.chan (M.core_of s)); [discriminate | discriminate Hok]. }
      destruct (Hsome Hc) as [Hs1 Hs2].
      unfold M.goto. cbn [M.facts M.chan M.err M.cost M.fires length]. rewrite Ee.
      unfold M.certify_ok in *. 
      refine (conj _ (conj _ (conj _ (conj _ _)))).
      * exact H16.
      * lia.
      * intro Hy. exfalso. apply Hc. exact Hy.
      * intro Hy. split; lia.
      * intro Hy. split; [exact Hc | lia].
    + unfold M.trap. cbn [M.facts M.chan M.err M.cost M.fires length].
      refine (conj _ (conj _ (conj _ (conj _ _)))).
      * exact H16.
      * lia.
      * intro Hy. specialize (Hnone Hy). lia.
      * intro Hy. destruct (Hsome Hy). split; lia.
      * rewrite Hok, orb_false_r. intro Hy. destruct (Hcert Hy). split; [assumption | lia].
Qed.

Lemma sm2_inv_step : forall P s, sm2_inv s -> sm2_inv (hstep P s).
Proof.
  intros P s Hinv. unfold hstep, M.step.
  destruct (M.next_instr P (M.core_of s)) as [i |] eqn:Hn; [| exact Hinv].
  destruct (sm_next_some P _ i Hn) as (Ee & _ & Hnh).
  apply sm2_inv_exec; assumption.
Qed.

Lemma sm2_reach_inv : forall n P x, sm2_inv (hrun_prog n P (sm_hstart x)).
Proof.
  induction n as [| n IH]; intros P x.
  - apply sm2_inv_start.
  - rewrite sm_run_succ. change (hrun_prog n P (hstep P (sm_hstart x))) with
      (hrun_prog n P (hstep P (sm_hstart x))).
    (* run_prog (S n) = run_prog n (step ...); use the other order *)
    rewrite <- sm_run_succ. rewrite (M.multi_run_prog_succ UC.hprop_eqb UC.heval n P).
    apply sm2_inv_step, IH.
Qed.

(* The five numbers describe the final record exactly. *)
Theorem sm2_final_numbers : forall P x s, hends P x s ->
  length (M.facts (M.core_of s)) <= 16 /\
  sm2_rcomp 4 s <= 1 /\
  (M.err (M.core_of s) = true <-> sm2_rcomp 4 s = 1) /\
  M.mu s = length (M.facts (M.core_of s)) + sm2_rcomp 2 s + sm2_rcomp 3 s + sm2_rcomp 4 s /\
  (M.cert s = true <-> 1 <= sm2_rcomp 3 s) /\
  (M.chan (M.core_of s) = None <-> sm2_rcomp 2 s = 0) /\
  (1 <= sm2_rcomp 2 s -> 1 <= length (M.facts (M.core_of s))) /\
  (1 <= sm2_rcomp 3 s -> 1 <= sm2_rcomp 2 s) /\
  sm2_rcomp 1 s = length (M.facts (M.core_of s)) /\
  sm2_rcomp 0 s = M.vals (M.core_of s) 0.
Proof.
  intros P x s [n [Hs _]]. subst s.
  pose proof (sm2_reach_inv n P x) as Hinv.
  set (s := hrun_prog n P (sm_hstart x)) in *.
  destruct Hinv as (H16 & Hge & Hnone & Hsome & Hcert).
  unfold sm2_rcomp, sm2_rrest, sm2_rfe in *. simpl.
  destruct (M.err (M.core_of s)) eqn:He; destruct (M.cert s) eqn:Hct;
    destruct (M.chan (M.core_of s)) eqn:Hch.
  all: try (specialize (Hnone eq_refl)).
  all: try (destruct (Hsome ltac:(congruence))).
  all: try (destruct (Hcert eq_refl)).
  all: try (exfalso; congruence).
  all: repeat split; try lia; intros; try discriminate; try lia.
Qed.

(* ================================================================= *)
(* The evaluator with a selector.                                     *)
(* ================================================================= *)

Lemma sm2_ev_mono : forall sel t n n' x c m, n <= n' ->
  sm2_ev sel t n x c = Some m -> sm2_ev sel t n' x c = Some m.
Proof.
  intros sel t n n' x c m Hle H. unfold sm2_ev in *.
  destruct (sm_kout n (sm_kpdec t) (sm_kspec c)) as [d |] eqn:Hd; [| discriminate].
  rewrite (sm_kout_mono n n' _ _ d Hle Hd). eapply sm2_tal_mono; eauto.
Qed.

(* A program numbered t sends the number of the specialised program to d, the
   program numbered d stops on x, and component sel of its final record is m. *)
Theorem sm2_ev_spec : forall sel t x c m,
  (exists n, sm2_ev sel t n x c = Some m) <->
  exists d, hfun (sm_hdecode t) (sm_kspec c) d /\
            exists s, hends (sm_hdecode d) x s /\ m = sm2_rcomp sel s.
Proof.
  intros sel t x c m. unfold sm_hdecode. split.
  - intros [n Hn]. unfold sm2_ev in Hn.
    destruct (sm_kout n (sm_kpdec t) (sm_kspec c)) as [d |] eqn:Hd; [| discriminate].
    exists d. split.
    + apply sm_kout_hfun. exists n. exact Hd.
    + apply sm2_tal_real in Hn as [Hh Hm].
      exists (hrun_prog n (map sm_of_ki (sm_kpdec d)) (sm_hstart x)). split.
      * exists n. split; [reflexivity | exact Hh].
      * exact Hm.
  - intros [d [H1 [s [[n2 [-> Hh]] Hm]]]].
    apply sm_kout_hfun in H1. destruct H1 as [n1 H1].
    exists (n1 + n2). unfold sm2_ev.
    rewrite (sm_kout_mono n1 (n1 + n2) _ _ d) by (lia || exact H1).
    apply (sm2_tal_mono sel n2); [lia |].
    apply sm2_tal_real. split; assumption.
Qed.

Print Assumptions sm2_ev_spec.
Print Assumptions sm2_ev_mono.
Print Assumptions sm2_krun_rel.
Print Assumptions sm2_tal_real.
Print Assumptions sm2_final_numbers.
