(** SmInterp.v: an interpreter for host programs, written over plain data.

    The host machine (EarnedMulti.v with the property PSlot) keeps its
    registers as functions nat -> nat. This file runs the same machine on
    plain data: register values and versions as lists of numbers (a missing
    entry reads as 0), the fact table as a list of (register, version)
    pairs, the channel as an option of such a pair, and the trap latch as a
    boolean. It never reads the ledger or the flag, because the next core
    of the host never depends on them.

      sm_kstep P k     one step of the program P on the plain core k
      sm_kout n P x    run P on input x for n steps; if it has stopped,
                       Some (register 0), otherwise None

    What is proved:
      1. The plain core and the host core stay related, step for step, and
         one has stopped exactly when the other has [sm_krel_step,
         sm_krel_halted].
      2. A host program computes y from x exactly when some number of steps
         of the interpreter gives Some y  [sm_kout_hfun].
      3. More steps never change an answer  [sm_kout_mono].
      4. The evaluator used for the recursion theorem, sm_ev t n x c: run
         the program numbered t on the number of the program specialised to
         c, and run the program whose number comes out on x. It finds y
         exactly when the program numbered t sends sm_kspec c to some d
         and the program numbered d sends x to y  [sm_ev_spec]. The plain
         universal evaluator sm_uev is the same without the first stage
         [sm_uev_spec].

    Every function here is a plain recursion over numbers, booleans, pairs,
    options and lists, so SmEvalL.v can turn it into a term of L.

    Dependencies: Coq standard library, EarnedCore.v, EarnedGeneric.v,
    EarnedMulti.v, UniversalCodes.v, SmHostBlocks.v and SmCodes.v. No
    axioms, no Admitted.                                                   *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the host machine, here the interpreter of the host machine of EarnedMulti.v on plain data.
   The host machine's link to the abstract record (a CertificationSystem
   with the trace floor, a Thiele-complete machine, and the halting problem
   of U) lives in UniversalInterpreterLinks.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.EarnedCore Minimal.EarnedMulti Minimal.UniversalCodes.
Require Import Minimal.SmHostBlocks Minimal.SmCodes.
Module E := Minimal.EarnedCore.
Module M := Minimal.EarnedMulti.
Module UC := Minimal.UniversalCodes.
Unset Implicit Arguments.

Local Notation hinstr := (@M.instr UC.hprop).
Local Notation hcore := (@M.core UC.hprop).
Local Notation hstate := (@M.state UC.hprop).
Local Notation hcexec := (M.cexec UC.hprop_eqb UC.heval).
Local Notation hstep := (M.step UC.hprop_eqb UC.heval).
Local Notation hrun_prog := (M.run_prog UC.hprop_eqb UC.heval).
Local Notation hfun := (sm_hfun UC.hprop_eqb UC.heval).
Local Notation hcstep := (sm_cstep UC.hprop_eqb UC.heval).

(* ================================================================= *)
(* Lists as register files.                                           *)
(* ================================================================= *)

Fixpoint sm_lset (l : list nat) (r v : nat) : list nat :=
  match r with
  | 0 => match l with [] => [v] | _ :: t => v :: t end
  | S r' => match l with [] => 0 :: sm_lset [] r' v | x :: t => x :: sm_lset t r' v end
  end.

Lemma sm_lset_nth : forall r l v q,
  nth q (sm_lset l r v) 0 = if Nat.eqb q r then v else nth q l 0.
Proof.
  induction r as [| r IH]; intros l v q.
  - destruct l as [| x t], q as [| q]; simpl; try reflexivity; destruct q; reflexivity.
  - destruct l as [| x t], q as [| q]; simpl; try reflexivity.
    + rewrite IH. destruct (Nat.eqb q r), q; reflexivity.
    + apply IH.
Qed.

(* ================================================================= *)
(* The property checker and the fact table, on plain data.            *)
(* ================================================================= *)

Definition sm_keval (m v : nat) : bool :=
  match m with
  | 0 => Nat.eqb v 0
  | S m1 => match m1 with 0 => negb (snd (sm_hb v)) | S n => Nat.leb n v end
  end.

Definition sm_kheval (x : nat) : bool :=
  match sm_unpair x with Some (m, v) => sm_keval m v | None => false end.

Lemma sm_kheval_eq : forall x, sm_kheval x = UC.heval UC.PSlot x.
Proof.
  intro x. unfold sm_kheval, UC.heval. rewrite sm_unpair_eq.
  destruct (UC.unpair x) as [[m v] |]; [| reflexivity].
  destruct m as [| [| n]]; simpl; try reflexivity.
  rewrite sm_hb_spec. simpl. apply Nat.negb_odd.
Qed.

Fixpoint sm_kmem (f : nat * nat) (l : list (nat * nat)) : bool :=
  match l with
  | [] => false
  | g :: t => (Nat.eqb (fst f) (fst g) && Nat.eqb (snd f) (snd g)) || sm_kmem f t
  end.

Definition sm_tofact (f : nat * nat) : @M.fact UC.hprop := M.mkfact UC.PSlot (fst f) (snd f).

Lemma sm_kmem_eq : forall r v fs,
  existsb (M.fact_eqb UC.hprop_eqb (M.mkfact UC.PSlot r v)) (map sm_tofact fs) = sm_kmem (r, v) fs.
Proof.
  intros r v fs. induction fs as [| [r' v'] fs IH]; [reflexivity |].
  simpl. rewrite IH. reflexivity.
Qed.

(* ================================================================= *)
(* The plain machine.                                                 *)
(* ================================================================= *)

Definition sm_KC : Type := (list nat * (list nat * (nat * (list (nat * nat) * (option (nat * nat) * bool)))))%type.

Definition sm_kfetch (P : list sm_ki) (n : nat) : option sm_ki :=
  match n with 0 => None | S m => nth_error P m end.

Definition sm_kexec (i : sm_ki) (vs ws : list nat) (pc : nat) (fs : list (nat * nat))
    (ch : option (nat * nat)) (er : bool) : sm_KC :=
  match i with
  | sm_KHalt => (vs, (ws, (pc, (fs, (ch, er)))))
  | sm_KInc r => (sm_lset vs r (S (nth r vs 0)), (sm_lset ws r (S (nth r ws 0)), (S pc, (fs, (ch, er)))))
  | sm_KDec r j =>
      match nth r vs 0 with
      | 0 => (vs, (ws, (S pc, (fs, (ch, er)))))
      | S n => (sm_lset vs r n, (sm_lset ws r (S (nth r ws 0)), (j, (fs, (ch, er)))))
      end
  | sm_KCheck r =>
      if sm_kheval (nth r vs 0) && Nat.ltb (length fs) 16
      then (vs, (ws, (S pc, ((r, nth r ws 0) :: fs, (ch, er)))))
      else (vs, (ws, (pc, (fs, (ch, true)))))
  | sm_KCommit r =>
      if sm_kmem (r, nth r ws 0) fs
      then (vs, (ws, (S pc, (fs, (Some (r, nth r ws 0), er)))))
      else (vs, (ws, (pc, (fs, (ch, true)))))
  | sm_KCertify =>
      match ch with
      | Some _ => (vs, (ws, (S pc, (fs, (ch, er)))))
      | None => (vs, (ws, (pc, (fs, (ch, true)))))
      end
  end.

(* Written with projections rather than a nested pattern, which the
   extraction tactic of SmEvalL.v handles. *)
Definition sm_kstep (P : list sm_ki) (k : sm_KC) : sm_KC :=
  if snd (snd (snd (snd (snd k)))) then k else
  match sm_kfetch P (fst (snd (snd k))) with
  | None => k
  | Some i => sm_kexec i (fst k) (fst (snd k)) (fst (snd (snd k))) (fst (snd (snd (snd k))))
                (fst (snd (snd (snd (snd k))))) (snd (snd (snd (snd (snd k)))))
  end.

Definition sm_khalted (P : list sm_ki) (k : sm_KC) : bool :=
  if snd (snd (snd (snd (snd k)))) then true else
  match sm_kfetch P (fst (snd (snd k))) with None => true | Some sm_KHalt => true | Some _ => false end.

Fixpoint sm_krun (n : nat) (P : list sm_ki) (k : sm_KC) : sm_KC :=
  match n with 0 => k | S m => sm_krun m P (sm_kstep P k) end.

Definition sm_kstart (x : nat) : sm_KC := ([0; x], ([], (1, ([], (None, false))))).

Definition sm_kout (fuel : nat) (P : list sm_ki) (x : nat) : option nat :=
  let k := sm_krun fuel P (sm_kstart x) in
  if sm_khalted P k then Some (nth 0 (fst k) 0) else None.

(* ================================================================= *)
(* The plain machine is the host machine.                             *)
(* ================================================================= *)

Definition sm_krel (k : hcore) (t : sm_KC) : Prop :=
  match t with
  | (vs, (ws, (pc, (fs, (ch, er))))) =>
      (forall r, M.vals k r = nth r vs 0) /\ (forall r, M.vers k r = nth r ws 0) /\
      M.pc k = pc /\ M.facts k = map sm_tofact fs /\
      M.chan k = option_map sm_tofact ch /\ M.err k = er
  end.

Lemma sm_fetch_of : forall P n, M.fetch (map sm_of_ki P) n = option_map sm_of_ki (sm_kfetch P n).
Proof. intros P [| n]; simpl; [reflexivity | apply nth_error_map]. Qed.

Lemma sm_krel_halted : forall P k t, sm_krel k t ->
  (M.halted (map sm_of_ki P) k <-> sm_khalted P t = true).
Proof.
  intros P k [vs [ws [pc [fs [ch er]]]]] (Hv & Hw & Hp & Hf & Hc & He).
  unfold M.halted, M.next_instr, sm_khalted. cbn [fst snd]. rewrite He, Hp, sm_fetch_of.
  destruct er; [split; reflexivity |].
  destruct (sm_kfetch P pc) as [[] |]; simpl; split; intro H; congruence.
Qed.

Lemma sm_write_rel : forall k vs ws r n j fs ch er,
  (forall q, M.vals k q = nth q vs 0) -> (forall q, M.vers k q = nth q ws 0) ->
  M.facts k = map sm_tofact fs -> M.chan k = option_map sm_tofact ch -> M.err k = er ->
  sm_krel (M.write k r n j) (sm_lset vs r n, (sm_lset ws r (S (nth r ws 0)), (j, (fs, (ch, er))))).
Proof.
  intros k vs ws r n j fs ch er Hv Hw Hf Hc He. simpl. repeat split; auto.
  - intro q. rewrite sm_lset_nth. unfold M.upd. destruct (Nat.eqb q r); auto.
  - intro q. rewrite sm_lset_nth. unfold M.upd. rewrite Hw. destruct (Nat.eqb q r); auto.
Qed.

Lemma sm_krel_step : forall P k t, sm_krel k t -> sm_krel (hcstep (map sm_of_ki P) k) (sm_kstep P t).
Proof.
  intros P k [vs [ws [pc [fs [ch er]]]]] Hrel.
  pose proof Hrel as (Hv & Hw & Hp & Hf & Hc & He).
  unfold sm_kstep. cbn [fst snd]. destruct er.
  { assert (Hn : M.next_instr (map sm_of_ki P) k = None)
      by (unfold M.next_instr; rewrite He; reflexivity).
    unfold sm_cstep. rewrite Hn. exact Hrel. }
  destruct (sm_kfetch P pc) as [i |] eqn:Hi.
  2: { assert (Hn : M.next_instr (map sm_of_ki P) k = None)
         by (unfold M.next_instr; rewrite He, Hp, sm_fetch_of, Hi; reflexivity).
       unfold sm_cstep. rewrite Hn. exact Hrel. }
  destruct i as [r | r j | | r | r |] eqn:Ei.
  3: { assert (Hn : M.next_instr (map sm_of_ki P) k = None)
         by (unfold M.next_instr; rewrite He, Hp, sm_fetch_of, Hi; reflexivity).
       unfold sm_cstep. rewrite Hn. exact Hrel. }
  all: assert (Hn : M.next_instr (map sm_of_ki P) k = Some (sm_of_ki i))
         by (unfold M.next_instr; rewrite He, Hp, sm_fetch_of, Hi, Ei; reflexivity).
  all: unfold sm_cstep; rewrite Hn, Ei; unfold M.cexec; rewrite He; cbn [sm_of_ki sm_kexec].
  - rewrite Hv, Hp. apply sm_write_rel; auto.
  - rewrite Hv. destruct (nth r vs 0) as [| n].
    + unfold M.goto. simpl. rewrite Hp. repeat split; auto.
    + apply sm_write_rel; auto.
  - assert (Hok : M.check_ok UC.heval k UC.PSlot r = sm_kheval (nth r vs 0) && Nat.ltb (length fs) 16).
    { unfold M.check_ok. rewrite He, Hv, Hf, map_length, sm_kheval_eq. reflexivity. }
    rewrite Hok. destruct (sm_kheval (nth r vs 0) && Nat.ltb (length fs) 16).
    + unfold M.record_fact, M.claim. simpl. rewrite Hp, Hf, Hw. repeat split; auto.
    + unfold M.trap. simpl. rewrite Hp. repeat split; auto.
  - assert (Hok : M.commit_ok UC.hprop_eqb k UC.PSlot r = sm_kmem (r, nth r ws 0) fs).
    { unfold M.commit_ok, M.claim. rewrite He, Hf, Hw. simpl. apply sm_kmem_eq. }
    rewrite Hok. destruct (sm_kmem (r, nth r ws 0) fs).
    + unfold M.commit_to, M.claim. simpl. rewrite Hp, Hw. repeat split; auto.
    + unfold M.trap. simpl. rewrite Hp. repeat split; auto.
  - assert (Hok : M.certify_ok k = match ch with Some _ => true | None => false end).
    { unfold M.certify_ok. rewrite He, Hc. destruct ch; reflexivity. }
    rewrite Hok. destruct ch as [f |].
    + unfold M.goto. simpl. rewrite Hp. repeat split; auto.
    + unfold M.trap. simpl. rewrite Hp. repeat split; auto.
Qed.

(* Core runs of the host. *)
Fixpoint sm_crun (n : nat) (P : list hinstr) (k : hcore) : hcore :=
  match n with 0 => k | S m => sm_crun m P (hcstep P k) end.

Lemma sm_core_run : forall n P s, M.core_of (hrun_prog n P s) = sm_crun n P (M.core_of s).
Proof.
  induction n as [| n IH]; intros P s; [reflexivity |].
  simpl. rewrite IH, sm_step_core. reflexivity.
Qed.

Lemma sm_krel_run : forall n P k t, sm_krel k t ->
  sm_krel (sm_crun n (map sm_of_ki P) k) (sm_krun n P t).
Proof.
  induction n as [| n IH]; intros P k t H; [exact H |].
  simpl. apply IH, sm_krel_step, H.
Qed.

Lemma sm_krel_start : forall x, sm_krel (M.core_of (sm_hstart x)) (sm_kstart x).
Proof.
  intro x. simpl. repeat split.
  - intros [| [| [| r]]]; reflexivity.
  - intros [| r]; [reflexivity | destruct r; reflexivity].
Qed.

Theorem sm_kout_hfun : forall P x y,
  hfun (map sm_of_ki P) x y <-> exists n, sm_kout n P x = Some y.
Proof.
  intros P x y. split.
  - intros [s [[n [-> Hh]] Hy]]. exists n.
    pose proof (sm_krel_run n P _ _ (sm_krel_start x)) as Hr.
    rewrite <- sm_core_run in Hr.
    unfold sm_kout. rewrite (proj1 (sm_krel_halted P _ _ Hr) Hh).
    destruct (sm_krun n P (sm_kstart x)) as [vs [ws [pc [fs [ch er]]]]].
    destruct Hr as (Hv & _). simpl. rewrite <- Hv, Hy. reflexivity.
  - intros [n Hn]. unfold sm_kout in Hn.
    pose proof (sm_krel_run n P _ _ (sm_krel_start x)) as Hr.
    rewrite <- sm_core_run in Hr.
    destruct (sm_khalted P (sm_krun n P (sm_kstart x))) eqn:Hh; [| discriminate].
    injection Hn as <-.
    exists (hrun_prog n (map sm_of_ki P) (sm_hstart x)). split.
    + exists n. split; [reflexivity |]. apply (sm_krel_halted P _ _ Hr), Hh.
    + destruct (sm_krun n P (sm_kstart x)) as [vs [ws [pc [fs [ch er]]]]].
      destruct Hr as (Hv & _). apply Hv.
Qed.

(* ================================================================= *)
(* More steps never change an answer.                                 *)
(* ================================================================= *)

Lemma sm_kstep_halted : forall P k, sm_khalted P k = true -> sm_kstep P k = k.
Proof.
  intros P [vs [ws [pc [fs [ch er]]]]] H. unfold sm_khalted in H. unfold sm_kstep.
  cbn [fst snd] in H |- *.
  destruct er; [reflexivity |].
  destruct (sm_kfetch P pc) as [[] |]; try discriminate; reflexivity.
Qed.

Lemma sm_krun_halted : forall n P k, sm_khalted P k = true -> sm_krun n P k = k.
Proof.
  induction n as [| n IH]; intros P k H; [reflexivity |].
  simpl. rewrite sm_kstep_halted by exact H. apply IH, H.
Qed.

Lemma sm_krun_add : forall a b P k, sm_krun (a + b) P k = sm_krun b P (sm_krun a P k).
Proof. induction a as [| a IH]; intros; simpl; [reflexivity | apply IH]. Qed.

Theorem sm_kout_mono : forall n n' P x y, n <= n' ->
  sm_kout n P x = Some y -> sm_kout n' P x = Some y.
Proof.
  intros n n' P x y Hle H. unfold sm_kout in *.
  destruct (sm_khalted P (sm_krun n P (sm_kstart x))) eqn:Hh; [| discriminate].
  replace n' with (n + (n' - n)) by lia. rewrite sm_krun_add.
  rewrite (sm_krun_halted (n' - n) P _ Hh), Hh. exact H.
Qed.

(* ================================================================= *)
(* The two evaluators.                                                *)
(* ================================================================= *)

(* The universal evaluator: run the program numbered c on x. *)
Definition sm_uev (fuel x c : nat) : option nat := sm_kout fuel (sm_kpdec c) x.

Theorem sm_uev_spec : forall x c y,
  (exists n, sm_uev n x c = Some y) <-> hfun (sm_hdecode c) x y.
Proof. intros x c y. unfold sm_uev, sm_hdecode. rewrite sm_kout_hfun. reflexivity. Qed.

Lemma sm_uev_mono : forall n n' x c, n <= n' ->
  forall y, sm_uev n x c = Some y -> sm_uev n' x c = Some y.
Proof. intros n n' x c Hle y H. eapply sm_kout_mono; eauto. Qed.

(* The evaluator of the recursion theorem, for the transformation numbered
   t: run program t on the number of the program specialised to c, then
   run the program whose number that gives on x. *)
Definition sm_ev (t fuel x c : nat) : option nat :=
  match sm_kout fuel (sm_kpdec t) (sm_kspec c) with
  | Some d => sm_kout fuel (sm_kpdec d) x
  | None => None
  end.

Lemma sm_ev_mono : forall t n n' x c y, n <= n' ->
  sm_ev t n x c = Some y -> sm_ev t n' x c = Some y.
Proof.
  intros t n n' x c y Hle H. unfold sm_ev in *.
  destruct (sm_kout n (sm_kpdec t) (sm_kspec c)) as [d |] eqn:Hd; [| discriminate].
  rewrite (sm_kout_mono n n' _ _ d Hle Hd). eapply sm_kout_mono; eauto.
Qed.

Theorem sm_ev_spec : forall t x c y,
  (exists n, sm_ev t n x c = Some y) <->
  exists d, hfun (sm_hdecode t) (sm_kspec c) d /\ hfun (sm_hdecode d) x y.
Proof.
  intros t x c y. unfold sm_hdecode. split.
  - intros [n Hn]. unfold sm_ev in Hn.
    destruct (sm_kout n (sm_kpdec t) (sm_kspec c)) as [d |] eqn:Hd; [| discriminate].
    exists d. split; apply sm_kout_hfun; exists n; assumption.
  - intros [d [H1 H2]]. apply sm_kout_hfun in H1. apply sm_kout_hfun in H2.
    destruct H1 as [n1 H1]. destruct H2 as [n2 H2].
    exists (n1 + n2). unfold sm_ev.
    rewrite (sm_kout_mono n1 (n1 + n2) _ _ d) by (lia || exact H1).
    apply (sm_kout_mono n2); [lia | exact H2].
Qed.

Print Assumptions sm_kout_hfun.
Print Assumptions sm_ev_spec.
Print Assumptions sm_uev_spec.
