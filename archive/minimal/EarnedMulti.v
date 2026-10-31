(** EarnedMulti.v: the machine of EarnedGeneric.v with a counter for every
    natural number.

    The instructions, costs, versions, fact table, commitment channel, trap
    latch, certified flag and fact cap of 16 are those of EarnedGeneric.v.
    The one difference is the store: instead of two counters A and B there
    is a counter for every register r : nat, held as two functions

      vals : nat -> nat    the value of each counter
      vers : nat -> nat    the version of each counter

    A write to register r sets vals at r, adds 1 to vers at r, and leaves
    every other register alone. INC r, DEC r j, CHECK p r and COMMIT p r name
    one register each; HALT and CERTIFY name none.

    The property language is left open exactly as in EarnedGeneric.v: any
    type [prop] with a boolean equality prop_eqb (prop_eqb_eq), a boolean
    checker eval, a meaning holds, and eval_iff tying them together.

    Every theorem of EarnedGeneric.v is restated under a multi_ name and
    proved here. Three groups are new.
      1. mentions i r: instruction i names register r. An instruction that
         does not mention r leaves the value and version of r unchanged
         (multi_frame_step), and so does a whole trace none of whose
         instructions mention r (multi_frame_run).
      2. An INC or DEC leaves the fact table, the channel, the trap latch,
         the ledger and the flag unchanged (multi_plain_step,
         multi_plain_run).
      3. A trapped machine takes no further step (multi_step_trapped,
         multi_trapped_halted, multi_run_prog_trapped).

    Dependencies: Coq standard library only. No axioms, no Admitted.        *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose, as in
   EarnedCore.v: this file imports nothing but the Coq standard library so
   anyone can re-check it from a clean checkout. Its link to the abstract
   record (the host machine running the fixed program U, read as a
   CertificationSystem with the trace cost floor) lives in
   coq/kernel/foundation/UniversalInterpreterLinks.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.

Section Multi.

(* ================================================================= *)
(* The open property language.                                        *)
(* ================================================================= *)

Context {prop : Type}.
Variable prop_eqb : prop -> prop -> bool.
Hypothesis prop_eqb_eq : forall p q, prop_eqb p q = true <-> p = q.
Variable eval : prop -> nat -> bool.
Variable holds : prop -> nat -> Prop.
Hypothesis eval_iff : forall p v, eval p v = true <-> holds p v.

(* Registers are natural numbers. *)
Definition reg : Type := nat.

(* A fact is a claim about one version of one register. *)
Record fact : Type := mkfact { f_prop : prop; f_reg : reg; f_ver : nat }.

(* Exact claim identity: field by field, no digest. *)
Definition fact_eqb (f g : fact) : bool :=
  prop_eqb (f_prop f) (f_prop g) && Nat.eqb (f_reg f) (f_reg g)
  && Nat.eqb (f_ver f) (f_ver g).

Lemma multi_prop_eqb_refl : forall p, prop_eqb p p = true.
Proof. intro p. apply prop_eqb_eq. reflexivity. Qed.

Lemma multi_fact_eqb_eq : forall f g, fact_eqb f g = true <-> f = g.
Proof.
  intros [p c v] [q d w]. unfold fact_eqb. simpl.
  rewrite !andb_true_iff, !Nat.eqb_eq, prop_eqb_eq. split.
  - intros [[Hp Hc] Hv]. subst. reflexivity.
  - intros H. inversion H. subst. auto.
Qed.

(* ================================================================= *)
(* The machine.                                                       *)
(* ================================================================= *)

Inductive instr : Type :=
| INC (r : reg)              (* r := r + 1                               *)
| DEC (r : reg) (j : nat)    (* if r > 0 then r := r - 1, jump to j      *)
| HALT
| CHECK (p : prop) (r : reg)
| COMMIT (p : prop) (r : reg)
| CERTIFY.

Definition cost (i : instr) : nat :=
  match i with
  | CHECK _ _ | COMMIT _ _ | CERTIFY => 1
  | _ => 0
  end.

(* Everything except the ledger and the flag. *)
Record core : Type := mkcore {
  vals : nat -> nat;        (* the value of each register   *)
  vers : nat -> nat;        (* the version of each register *)
  pc : nat;                 (* 1-based, as in Minsky        *)
  facts : list fact;        (* established facts            *)
  chan : option fact;       (* the commitment channel       *)
  err : bool                (* the trap latch               *)
}.

(* A function that agrees with f except at r, where it is v. *)
Definition upd (f : nat -> nat) (r v : nat) : nat -> nat :=
  fun x => if Nat.eqb x r then v else f x.

(* A write sets register r, bumps its version, and moves pc to j. *)
Definition write (k : core) (r : reg) (n j : nat) : core :=
  mkcore (upd (vals k) r n) (upd (vers k) r (S (vers k r))) j
         (facts k) (chan k) (err k).
Definition goto (k : core) (j : nat) : core :=
  mkcore (vals k) (vers k) j (facts k) (chan k) (err k).
Definition trap (k : core) : core :=
  mkcore (vals k) (vers k) (pc k) (facts k) (chan k) true.
Definition record_fact (k : core) (f : fact) : core :=
  mkcore (vals k) (vers k) (S (pc k)) (f :: facts k) (chan k) (err k).
Definition commit_to (k : core) (f : fact) : core :=
  mkcore (vals k) (vers k) (S (pc k)) (facts k) (Some f) (err k).

Definition fact_cap : nat := 16.

(* The claim "p holds of r" about r's current version. *)
Definition claim (k : core) (p : prop) (r : reg) : fact := mkfact p r (vers k r).

Definition check_ok (k : core) (p : prop) (r : reg) : bool :=
  negb (err k) && eval p (vals k r) && Nat.ltb (length (facts k)) fact_cap.
Definition commit_ok (k : core) (p : prop) (r : reg) : bool :=
  negb (err k) && existsb (fact_eqb (claim k p r)) (facts k).
Definition certify_ok (k : core) : bool :=
  negb (err k) && match chan k with Some _ => true | None => false end.

Definition cexec (k : core) (i : instr) : core :=
  if err k then k else
  match i with
  | INC r => write k r (S (vals k r)) (S (pc k))
  | DEC r j =>
      match vals k r with
      | 0 => goto k (S (pc k))
      | S n => write k r n j
      end
  | HALT => k
  | CHECK p r => if check_ok k p r then record_fact k (claim k p r) else trap k
  | COMMIT p r => if commit_ok k p r then commit_to k (claim k p r) else trap k
  | CERTIFY => if certify_ok k then goto k (S (pc k)) else trap k
  end.

(* The one event that raises the flag. *)
Definition fires (k : core) (i : instr) : bool :=
  match i with CERTIFY => certify_ok k | _ => false end.

Record state : Type := mkst { core_of : core; mu : nat; cert : bool }.

Definition exec (s : state) (i : instr) : state :=
  mkst (cexec (core_of s) i) (mu s + cost i) (cert s || fires (core_of s) i).

Fixpoint run (tr : list instr) (s : state) : state :=
  match tr with [] => s | i :: rest => run rest (exec s i) end.

Fixpoint total_cost (tr : list instr) : nat :=
  match tr with [] => 0 | i :: rest => cost i + total_cost rest end.

(* A start: the given register values, every version 0, pc 1, no facts,
   an empty channel, no trap, an empty ledger, the flag down. *)
Definition start_core (vs : nat -> nat) : core :=
  mkcore vs (fun _ => 0) 1 [] None false.
Definition start (vs : nat -> nat) : state := mkst (start_core vs) 0 false.

Definition clean_start (s : state) : Prop :=
  facts (core_of s) = [] /\ chan (core_of s) = None /\ cert s = false.

Lemma multi_start_clean : forall vs, clean_start (start vs).
Proof. intros. repeat split. Qed.

(* Stored programs. *)
Definition fetch {A : Type} (P : list A) (n : nat) : option A :=
  match n with 0 => None | S m => nth_error P m end.

Definition next_instr (P : list instr) (k : core) : option instr :=
  if err k then None else
  match fetch P (pc k) with Some HALT => None | o => o end.

Definition halted (P : list instr) (k : core) : Prop := next_instr P k = None.

Definition step (P : list instr) (s : state) : state :=
  match next_instr P (core_of s) with None => s | Some i => exec s i end.

Fixpoint run_prog (n : nat) (P : list instr) (s : state) : state :=
  match n with 0 => s | S m => run_prog m P (step P s) end.

(* The instructions a program run actually executes. *)
Fixpoint trace_of (n : nat) (P : list instr) (s : state) : list instr :=
  match n with
  | 0 => []
  | S m => match next_instr P (core_of s) with
           | None => []
           | Some i => i :: trace_of m P (exec s i)
           end
  end.

Lemma multi_run_app : forall l1 l2 s, run (l1 ++ l2) s = run l2 (run l1 s).
Proof. induction l1; intros; simpl; auto. Qed.

Lemma multi_run_snoc : forall l i s, run (l ++ [i]) s = exec (run l s) i.
Proof. intros. rewrite multi_run_app. reflexivity. Qed.

Lemma multi_total_cost_app : forall l1 l2,
  total_cost (l1 ++ l2) = total_cost l1 + total_cost l2.
Proof. induction l1; intros; simpl; [| rewrite IHl1]; lia. Qed.

Lemma multi_run_prog_halted : forall n P s, halted P (core_of s) -> run_prog n P s = s.
Proof.
  induction n; intros P s H; simpl; [reflexivity |].
  unfold step. unfold halted in H. rewrite H. apply IHn. exact H.
Qed.

Lemma multi_run_prog_trace : forall n P s, run_prog n P s = run (trace_of n P s) s.
Proof.
  induction n; intros P s; simpl; [reflexivity |].
  unfold step. destruct (next_instr P (core_of s)) eqn:H.
  - apply IHn.
  - apply multi_run_prog_halted. exact H.
Qed.

Lemma multi_run_prog_add : forall n m P s,
  run_prog (n + m) P s = run_prog m P (run_prog n P s).
Proof. induction n; intros m P s; simpl; [reflexivity | apply IHn]. Qed.

Lemma multi_run_prog_succ : forall n P s,
  run_prog (S n) P s = step P (run_prog n P s).
Proof.
  intros n P s. replace (S n) with (n + 1) by lia.
  rewrite multi_run_prog_add. reflexivity.
Qed.

(* ================================================================= *)
(* A trapped machine takes no further step.                           *)
(* ================================================================= *)

Lemma multi_cexec_trapped : forall k i, err k = true -> cexec k i = k.
Proof. intros k i H. unfold cexec. rewrite H. reflexivity. Qed.

Theorem multi_trapped_halted : forall P k, err k = true -> halted P k.
Proof. intros P k H. unfold halted, next_instr. rewrite H. reflexivity. Qed.

Theorem multi_step_trapped : forall P s, err (core_of s) = true -> step P s = s.
Proof. intros P s H. unfold step, next_instr. rewrite H. reflexivity. Qed.

Lemma multi_run_prog_trapped : forall n P s,
  err (core_of s) = true -> run_prog n P s = s.
Proof.
  intros n P s H. apply multi_run_prog_halted, multi_trapped_halted, H.
Qed.

(* The trap latch never resets. *)
Lemma multi_err_permanent : forall k i, err k = true -> err (cexec k i) = true.
Proof. intros k i H. rewrite multi_cexec_trapped by exact H. exact H. Qed.

(* ================================================================= *)
(* The toll, the ledger, the latch.                                   *)
(* ================================================================= *)

Theorem multi_mu_conservation_trace : forall tr s, mu (run tr s) = mu s + total_cost tr.
Proof. induction tr; intros; simpl; [lia | rewrite IHtr; simpl; lia]. Qed.

Theorem multi_mu_conservation_program : forall n P s,
  mu (run_prog n P s) = mu s + total_cost (trace_of n P s).
Proof. intros. rewrite multi_run_prog_trace. apply multi_mu_conservation_trace. Qed.

Theorem multi_cert_latch : forall s i, cert (exec s i) = cert s || fires (core_of s) i.
Proof. reflexivity. Qed.

Theorem multi_cert_permanent : forall s i, cert s = true -> cert (exec s i) = true.
Proof. intros s i H. simpl. rewrite H. reflexivity. Qed.

Theorem multi_only_certify_certifies : forall s i,
  cert s = false -> cert (exec s i) = true ->
  i = CERTIFY /\ certify_ok (core_of s) = true.
Proof.
  intros s i H0 H1. simpl in H1. rewrite H0 in H1. simpl in H1.
  destruct i; simpl in H1; try discriminate. auto.
Qed.

Theorem multi_a2 : forall s i, cert s = false -> cert (exec s i) = true -> cost i >= 1.
Proof.
  intros s i H0 H1. destruct (multi_only_certify_certifies s i H0 H1) as [-> _].
  simpl. lia.
Qed.

Theorem multi_nfi_floor : forall tr s,
  cert s = false -> cert (run tr s) = true -> total_cost tr >= 1.
Proof.
  induction tr as [| i rest IH]; intros s H0 H1; simpl in *; [congruence |].
  destruct (cert (exec s i)) eqn:Hm.
  - pose proof (multi_a2 s i H0 Hm). lia.
  - pose proof (IH _ Hm H1). lia.
Qed.

(* ================================================================= *)
(* Per-instruction facts about the substrate.                         *)
(* ================================================================= *)

Lemma multi_ver_write : forall k r n j d,
  vers (write k r n j) d = if Nat.eqb r d then S (vers k d) else vers k d.
Proof.
  intros. simpl. unfold upd.
  destruct (Nat.eqb_spec d r), (Nat.eqb_spec r d); subst; congruence.
Qed.

Lemma multi_val_write : forall k r n j d,
  vals (write k r n j) d = if Nat.eqb r d then n else vals k d.
Proof.
  intros. simpl. unfold upd.
  destruct (Nat.eqb_spec d r), (Nat.eqb_spec r d); subst; congruence.
Qed.

Lemma multi_facts_write : forall k r n j, facts (write k r n j) = facts k.
Proof. reflexivity. Qed.

Lemma multi_chan_write : forall k r n j, chan (write k r n j) = chan k.
Proof. reflexivity. Qed.

Lemma multi_err_write : forall k r n j, err (write k r n j) = err k.
Proof. reflexivity. Qed.

Lemma multi_pc_write : forall k r n j, pc (write k r n j) = j.
Proof. reflexivity. Qed.

Lemma multi_ver_mono : forall k i c, vers k c <= vers (cexec k i) c.
Proof.
  intros k i c. unfold cexec. destruct (err k); [lia |].
  destruct i as [d | d j | | p d | p d |].
  - rewrite multi_ver_write. destruct (Nat.eqb d c); lia.
  - destruct (vals k d); [simpl; lia |].
    rewrite multi_ver_write. destruct (Nat.eqb d c); lia.
  - lia.
  - destruct (check_ok k p d); simpl; lia.
  - destruct (commit_ok k p d); simpl; lia.
  - destruct (certify_ok k); simpl; lia.
Qed.

Lemma multi_ver_same_val : forall k i c,
  vers (cexec k i) c = vers k c -> vals (cexec k i) c = vals k c.
Proof.
  intros k i c H. unfold cexec in *. destruct (err k); [reflexivity |].
  destruct i as [d | d j | | p d | p d |].
  - rewrite multi_ver_write in H. rewrite multi_val_write.
    destruct (Nat.eqb d c); [lia | reflexivity].
  - destruct (vals k d); [reflexivity |].
    rewrite multi_ver_write in H. rewrite multi_val_write.
    destruct (Nat.eqb d c); [lia | reflexivity].
  - reflexivity.
  - destruct (check_ok k p d); reflexivity.
  - destruct (commit_ok k p d); reflexivity.
  - destruct (certify_ok k); reflexivity.
Qed.

Lemma multi_ver_check : forall k p c d, vers (cexec k (CHECK p c)) d = vers k d.
Proof.
  intros. unfold cexec. destruct (err k); [reflexivity |].
  destruct (check_ok k p c); reflexivity.
Qed.

Lemma multi_val_check : forall k p c d, vals (cexec k (CHECK p c)) d = vals k d.
Proof.
  intros. unfold cexec. destruct (err k); [reflexivity |].
  destruct (check_ok k p c); reflexivity.
Qed.

Theorem multi_facts_step : forall k i f,
  In f (facts (cexec k i)) ->
  In f (facts k) \/
  (i = CHECK (f_prop f) (f_reg f) /\ check_ok k (f_prop f) (f_reg f) = true /\
   f = claim k (f_prop f) (f_reg f)).
Proof.
  intros k i f H. unfold cexec in H. destruct (err k) eqn:He; [auto |].
  destruct i as [d | d j | | p d | p d |].
  - auto.
  - destruct (vals k d); auto.
  - auto.
  - destruct (check_ok k p d) eqn:Hc; simpl in H; [| auto].
    destruct H as [<- | H]; [right | auto]. simpl. auto.
  - destruct (commit_ok k p d); simpl in H; auto.
  - destruct (certify_ok k); simpl in H; auto.
Qed.

Theorem multi_facts_keep : forall k i f, In f (facts k) -> In f (facts (cexec k i)).
Proof.
  intros k i f H. unfold cexec. destruct (err k); [exact H |].
  destruct i as [d | d j | | p d | p d |].
  - exact H.
  - destruct (vals k d); exact H.
  - exact H.
  - destruct (check_ok k p d); simpl; auto.
  - destruct (commit_ok k p d); simpl; auto.
  - destruct (certify_ok k); simpl; auto.
Qed.

Theorem multi_full_table_traps : forall k p c,
  fact_cap <= length (facts k) ->
  err (cexec k (CHECK p c)) = true /\ facts (cexec k (CHECK p c)) = facts k.
Proof.
  intros k p c H. unfold cexec. destruct (err k) eqn:He; [auto |].
  unfold check_ok. rewrite He.
  replace (Nat.ltb (length (facts k)) fact_cap) with false
    by (symmetry; apply Nat.ltb_ge; exact H).
  rewrite andb_false_r. auto.
Qed.

Theorem multi_facts_bounded_step : forall k i,
  length (facts k) <= fact_cap -> length (facts (cexec k i)) <= fact_cap.
Proof.
  intros k i H. unfold cexec. destruct (err k); [exact H |].
  destruct i as [d | d j | | p d | p d |].
  - exact H.
  - destruct (vals k d); exact H.
  - exact H.
  - destruct (check_ok k p d) eqn:Hc; simpl; [| exact H].
    unfold check_ok in Hc. apply andb_true_iff in Hc as [_ Hc].
    apply Nat.ltb_lt in Hc. lia.
  - destruct (commit_ok k p d); simpl; exact H.
  - destruct (certify_ok k); simpl; exact H.
Qed.

Lemma multi_chan_step : forall k i,
  chan (cexec k i) = chan k \/
  exists p c, i = COMMIT p c /\ commit_ok k p c = true /\
              chan (cexec k i) = Some (claim k p c).
Proof.
  intros k i. unfold cexec. destruct (err k); [auto |].
  destruct i as [d | d j | | p d | p d |].
  - auto.
  - destruct (vals k d); auto.
  - auto.
  - destruct (check_ok k p d); simpl; auto.
  - destruct (commit_ok k p d) eqn:Hc; simpl; [right; eauto | auto].
  - destruct (certify_ok k); simpl; auto.
Qed.

Lemma multi_commit_ok_iff : forall k p c,
  commit_ok k p c = true <-> err k = false /\ In (claim k p c) (facts k).
Proof.
  intros. unfold commit_ok. rewrite andb_true_iff, negb_true_iff, existsb_exists.
  split.
  - intros [He [f [Hin Hf]]]. apply multi_fact_eqb_eq in Hf. subst. auto.
  - intros [He Hin]. split; [exact He |]. exists (claim k p c).
    split; [exact Hin | apply multi_fact_eqb_eq; reflexivity].
Qed.

Theorem multi_unearned_commit_traps : forall k p c,
  commit_ok k p c = false ->
  err (cexec k (COMMIT p c)) = true /\
  chan (cexec k (COMMIT p c)) = chan k /\ facts (cexec k (COMMIT p c)) = facts k.
Proof.
  intros k p c H. unfold cexec. destruct (err k) eqn:He; [auto |].
  rewrite H. auto.
Qed.

Theorem multi_uncommitted_certify_traps : forall s,
  certify_ok (core_of s) = false ->
  err (core_of (exec s CERTIFY)) = true /\ cert (exec s CERTIFY) = cert s.
Proof.
  intros [k m r] H. simpl in *. rewrite H, orb_false_r. unfold cexec.
  destruct (err k) eqn:He; [auto |]. rewrite H. auto.
Qed.

(* ================================================================= *)
(* The frame: registers an instruction does not name.                 *)
(* ================================================================= *)

(* Instruction i names register r. *)
Definition mentions (i : instr) (r : reg) : bool :=
  match i with
  | INC d | DEC d _ | CHECK _ d | COMMIT _ d => Nat.eqb d r
  | HALT | CERTIFY => false
  end.

(* Instruction i is an INC or a DEC. *)
Definition plain (i : instr) : bool :=
  match i with INC _ | DEC _ _ => true | _ => false end.

Lemma multi_frame_cexec : forall k i r,
  mentions i r = false ->
  vals (cexec k i) r = vals k r /\ vers (cexec k i) r = vers k r.
Proof.
  intros k i r H. unfold cexec. destruct (err k); [auto |].
  destruct i as [d | d j | | p d | p d |]; simpl in H.
  - rewrite multi_val_write, multi_ver_write, H. auto.
  - destruct (vals k d); [auto |].
    rewrite multi_val_write, multi_ver_write, H. auto.
  - auto.
  - destruct (check_ok k p d); auto.
  - destruct (commit_ok k p d); auto.
  - destruct (certify_ok k); auto.
Qed.

Lemma multi_plain_cexec : forall k i,
  plain i = true ->
  facts (cexec k i) = facts k /\ chan (cexec k i) = chan k /\ err (cexec k i) = err k.
Proof.
  intros k i H. unfold cexec. destruct (err k) eqn:He; [auto |].
  destruct i as [d | d j | | p d | p d |]; simpl in H; try discriminate.
  - auto.
  - destruct (vals k d); auto.
Qed.

Theorem multi_plain_step : forall s i,
  plain i = true ->
  facts (core_of (exec s i)) = facts (core_of s) /\
  chan (core_of (exec s i)) = chan (core_of s) /\
  err (core_of (exec s i)) = err (core_of s) /\
  mu (exec s i) = mu s /\ cert (exec s i) = cert s.
Proof.
  intros s i H. destruct (multi_plain_cexec (core_of s) i H) as [Hf [Hc He]].
  simpl. rewrite Hf, Hc, He.
  destruct i; simpl in H; try discriminate; simpl;
    rewrite Nat.add_0_r, orb_false_r; auto.
Qed.

(* An instruction that does not mention r leaves r's value and version
   alone; an INC or DEC also leaves the fact table, channel, trap latch,
   ledger and flag alone. *)
Theorem multi_frame_step : forall s i r,
  mentions i r = false ->
  vals (core_of (exec s i)) r = vals (core_of s) r /\
  vers (core_of (exec s i)) r = vers (core_of s) r /\
  (plain i = true ->
   facts (core_of (exec s i)) = facts (core_of s) /\
   chan (core_of (exec s i)) = chan (core_of s) /\
   err (core_of (exec s i)) = err (core_of s) /\
   mu (exec s i) = mu s /\ cert (exec s i) = cert s).
Proof.
  intros s i r H. destruct (multi_frame_cexec (core_of s) i r H) as [Hv Hw].
  split; [exact Hv |]. split; [exact Hw |]. apply multi_plain_step.
Qed.

Theorem multi_frame_run : forall tr s r,
  (forall i, In i tr -> mentions i r = false) ->
  vals (core_of (run tr s)) r = vals (core_of s) r /\
  vers (core_of (run tr s)) r = vers (core_of s) r.
Proof.
  induction tr as [| i tr IH]; intros s r H; simpl; [auto |].
  destruct (IH (exec s i) r) as [Hv Hw]; [intros i' Hi; apply H; right; exact Hi |].
  destruct (multi_frame_cexec (core_of s) i r (H i (or_introl eq_refl))) as [Hv' Hw'].
  simpl in *. rewrite Hv, Hw, Hv', Hw'. auto.
Qed.

Theorem multi_plain_run : forall tr s,
  (forall i, In i tr -> plain i = true) ->
  facts (core_of (run tr s)) = facts (core_of s) /\
  chan (core_of (run tr s)) = chan (core_of s) /\
  err (core_of (run tr s)) = err (core_of s) /\
  mu (run tr s) = mu s /\ cert (run tr s) = cert s.
Proof.
  induction tr as [| i tr IH]; intros s H; simpl; [auto |].
  destruct (IH (exec s i)) as [Hf [Hc [He [Hm Hcert]]]];
    [intros i' Hi; apply H; right; exact Hi |].
  destruct (multi_plain_step s i (H i (or_introl eq_refl)))
    as [Hf' [Hc' [He' [Hm' Hcert']]]].
  rewrite Hf, Hc, He, Hm, Hcert, Hf', Hc', He', Hm', Hcert'. auto.
Qed.

(* ================================================================= *)
(* Runs: versions only grow, equal version means equal value.         *)
(* ================================================================= *)

Lemma multi_ver_mono_run : forall l s c,
  vers (core_of s) c <= vers (core_of (run l s)) c.
Proof.
  induction l as [| i l IH]; intros s c; simpl; [lia |].
  pose proof (multi_ver_mono (core_of s) i c). pose proof (IH (exec s i) c).
  simpl in *. lia.
Qed.

Definition untouched (s : state) (mid : list instr) (c : reg) : Prop :=
  forall t1 i t2, mid = t1 ++ i :: t2 ->
    let k := core_of (run t1 s) in
    vers (cexec k i) c = vers k c /\ vals (cexec k i) c = vals k c.

Lemma multi_untouched_of_ver : forall s mid c,
  vers (core_of (run mid s)) c = vers (core_of s) c -> untouched s mid c.
Proof.
  intros s mid c H t1 i t2 ->. simpl.
  rewrite multi_run_app in H. simpl in H.
  pose proof (multi_ver_mono_run t1 s c).
  pose proof (multi_ver_mono (core_of (run t1 s)) i c).
  pose proof (multi_ver_mono_run t2 (exec (run t1 s) i) c). simpl in *.
  assert (Hv : vers (cexec (core_of (run t1 s)) i) c = vers (core_of (run t1 s)) c)
    by lia.
  split; [exact Hv | apply multi_ver_same_val; exact Hv].
Qed.

(* ================================================================= *)
(* Checker soundness.                                                 *)
(* ================================================================= *)

Definition sound (k : core) : Prop :=
  forall f, In f (facts k) ->
    f_ver f <= vers k (f_reg f) /\
    (f_ver f = vers k (f_reg f) -> holds (f_prop f) (vals k (f_reg f))).

Lemma multi_sound_step : forall k i, sound k -> sound (cexec k i).
Proof.
  intros k i Hs f Hin.
  pose proof (multi_ver_mono k i (f_reg f)) as Hm.
  destruct (multi_facts_step k i f Hin) as [Hold | [Hi [Hc Hf]]].
  - destruct (Hs f Hold) as [Hle Hlive]. split; [lia |].
    intro Heq. assert (Hv : vers (cexec k i) (f_reg f) = vers k (f_reg f)) by lia.
    rewrite (multi_ver_same_val k i _ Hv). apply Hlive. lia.
  - subst i. rewrite multi_ver_check, multi_val_check.
    rewrite Hf. simpl. split; [lia | intros _].
    unfold check_ok in Hc. apply andb_true_iff in Hc as [Hc _].
    apply andb_true_iff in Hc as [_ Hc]. apply eval_iff. exact Hc.
Qed.

Lemma multi_sound_run : forall tr s, sound (core_of s) -> sound (core_of (run tr s)).
Proof.
  induction tr; intros s H; simpl; [exact H | apply IHtr, multi_sound_step, H].
Qed.

Theorem multi_checker_soundness : forall s0 tr f,
  clean_start s0 ->
  let k := core_of (run tr s0) in
  In f (facts k) -> f_ver f = vers k (f_reg f) -> holds (f_prop f) (vals k (f_reg f)).
Proof.
  intros s0 tr f [Hf _] k Hin Hv.
  assert (Hs0 : sound (core_of s0)) by (intros g Hg; rewrite Hf in Hg; destruct Hg).
  exact (proj2 (multi_sound_run tr s0 Hs0 f Hin) Hv).
Qed.

Corollary multi_committed_claim_holds : forall s0 tr p c,
  clean_start s0 ->
  commit_ok (core_of (run tr s0)) p c = true ->
  holds p (vals (core_of (run tr s0)) c).
Proof.
  intros s0 tr p c H0 Hc. apply multi_commit_ok_iff in Hc as [_ Hin].
  exact (multi_checker_soundness s0 tr _ H0 Hin eq_refl).
Qed.

(* ================================================================= *)
(* No forging, over any run.                                          *)
(* ================================================================= *)

Definition earned (s0 : state) (tr : list instr) (f : fact) : Prop :=
  exists pre mid,
    tr = pre ++ CHECK (f_prop f) (f_reg f) :: mid /\
    check_ok (core_of (run pre s0)) (f_prop f) (f_reg f) = true /\
    f = claim (core_of (run pre s0)) (f_prop f) (f_reg f) /\
    (f_ver f = vers (core_of (run tr s0)) (f_reg f) ->
     untouched (run (pre ++ [CHECK (f_prop f) (f_reg f)]) s0) mid (f_reg f)).

Definition no_forgery (s0 : state) (tr : list instr) : Prop :=
  forall f, In f (facts (core_of (run tr s0))) -> earned s0 tr f.

Lemma multi_earned_intro : forall s0 pre mid f,
  check_ok (core_of (run pre s0)) (f_prop f) (f_reg f) = true ->
  f = claim (core_of (run pre s0)) (f_prop f) (f_reg f) ->
  earned s0 (pre ++ CHECK (f_prop f) (f_reg f) :: mid) f.
Proof.
  intros s0 pre mid f Hc Hf. exists pre, mid.
  split; [reflexivity |]. split; [exact Hc |]. split; [exact Hf |].
  intro Hlive. apply multi_untouched_of_ver.
  replace (pre ++ CHECK (f_prop f) (f_reg f) :: mid)
    with ((pre ++ [CHECK (f_prop f) (f_reg f)]) ++ mid) in Hlive
    by (rewrite <- app_assoc; reflexivity).
  rewrite multi_run_app in Hlive. rewrite <- Hlive.
  rewrite multi_run_snoc. simpl. rewrite multi_ver_check.
  rewrite Hf at 1. reflexivity.
Qed.

Theorem multi_no_forging_step : forall s0 tr i,
  no_forgery s0 tr -> no_forgery s0 (tr ++ [i]).
Proof.
  intros s0 tr i Hnf f Hin. rewrite multi_run_snoc in Hin. simpl in Hin.
  destruct (multi_facts_step _ i f Hin) as [Hold | [Hi [Hc Hf]]].
  - destruct (Hnf f Hold) as [pre [mid [Htr [Hc [Hf _]]]]].
    rewrite Htr, <- app_assoc. simpl. apply multi_earned_intro; assumption.
  - subst i. apply multi_earned_intro; assumption.
Qed.

Theorem multi_no_forging : forall s0 tr, clean_start s0 -> no_forgery s0 tr.
Proof.
  intros s0 tr [Hf _]. induction tr as [| i tr IH] using rev_ind.
  - intros f Hin. simpl in Hin. rewrite Hf in Hin. destruct Hin.
  - apply multi_no_forging_step, IH.
Qed.

(* ================================================================= *)
(* Earned provenance.                                                 *)
(* ================================================================= *)

Theorem multi_earned_commitment_provenance : forall s0 pre p c,
  clean_start s0 ->
  commit_ok (core_of (run pre s0)) p c = true ->
  exists pre1 mid,
    pre = pre1 ++ CHECK p c :: mid /\
    check_ok (core_of (run pre1 s0)) p c = true /\
    cost (CHECK p c) >= 1 /\ cost (COMMIT p c) >= 1 /\
    vers (core_of (run pre1 s0)) c = vers (core_of (run pre s0)) c /\
    untouched (run (pre1 ++ [CHECK p c]) s0) mid c.
Proof.
  intros s0 pre p c H0 Hc. apply multi_commit_ok_iff in Hc as [_ Hin].
  destruct (multi_no_forging s0 pre H0 _ Hin) as [pre1 [mid [Htr [Hck [Hf Hlive]]]]].
  simpl in *. exists pre1, mid.
  split; [exact Htr |]. split; [exact Hck |].
  split; [simpl; lia |]. split; [simpl; lia |].
  split; [unfold claim in Hf; injection Hf as Hv; symmetry; exact Hv |].
  apply Hlive. reflexivity.
Qed.

Lemma multi_cert_first : forall s0 tr,
  cert s0 = false -> cert (run tr s0) = true ->
  exists pre post, tr = pre ++ CERTIFY :: post /\
    cert (run pre s0) = false /\ certify_ok (core_of (run pre s0)) = true.
Proof.
  intros s0 tr H0. induction tr as [| i tr IH] using rev_ind; intro H1.
  - simpl in H1. congruence.
  - rewrite multi_run_snoc in H1. destruct (cert (run tr s0)) eqn:Hc.
    + destruct (IH eq_refl) as [pre [post [-> Hrest]]].
      exists pre, (post ++ [i]). rewrite <- app_assoc. auto.
    + destruct (multi_only_certify_certifies _ i Hc H1) as [-> Hok].
      exists tr, []. auto.
Qed.

Lemma multi_chan_origin : forall s0 tr f,
  chan (core_of s0) = None -> chan (core_of (run tr s0)) = Some f ->
  exists pre1 p c mid, tr = pre1 ++ COMMIT p c :: mid /\
    commit_ok (core_of (run pre1 s0)) p c = true /\
    f = claim (core_of (run pre1 s0)) p c.
Proof.
  intros s0 tr f H0. induction tr as [| i tr IH] using rev_ind; intro H1.
  - simpl in H1. congruence.
  - rewrite multi_run_snoc in H1. simpl in H1.
    destruct (multi_chan_step (core_of (run tr s0)) i) as [Hs | [p [c [-> [Hok Hch]]]]].
    + rewrite Hs in H1. destruct (IH H1) as [pre1 [p [c [mid [-> Hrest]]]]].
      exists pre1, p, c, (mid ++ [i]). rewrite <- app_assoc. auto.
    + rewrite Hch in H1. injection H1 as <-. exists tr, p, c, []. auto.
Qed.

(* A raised flag was earned: CHECK, then COMMIT of the same claim at the
   same version with the register untouched between, then CERTIFY. *)
Theorem multi_earned_certification_provenance : forall s0 tr,
  clean_start s0 -> cert (run tr s0) = true ->
  exists pre1 p c mid1 mid2 post,
    tr = pre1 ++ CHECK p c :: mid1 ++ COMMIT p c :: mid2 ++ CERTIFY :: post /\
    check_ok (core_of (run pre1 s0)) p c = true /\
    commit_ok (core_of (run (pre1 ++ CHECK p c :: mid1) s0)) p c = true /\
    certify_ok (core_of (run (pre1 ++ CHECK p c :: mid1 ++ COMMIT p c :: mid2) s0))
      = true /\
    vers (core_of (run pre1 s0)) c
      = vers (core_of (run (pre1 ++ CHECK p c :: mid1) s0)) c /\
    untouched (run (pre1 ++ [CHECK p c]) s0) mid1 c.
Proof.
  intros s0 tr H0 H1. pose proof H0 as [_ [Hch Hc0]].
  destruct (multi_cert_first s0 tr Hc0 H1) as [pre [post [-> [_ Hok]]]].
  pose proof Hok as Hset. unfold certify_ok in Hset.
  apply andb_true_iff in Hset as [_ Hset].
  destruct (chan (core_of (run pre s0))) as [f |] eqn:Hf; [| discriminate].
  destruct (multi_chan_origin s0 pre f Hch Hf) as [preC [p [c [mid2 [-> [Hcm _]]]]]].
  destruct (multi_earned_commitment_provenance s0 preC p c H0 Hcm)
    as [pre1 [mid1 [-> [Hck [_ [_ [Hv Hun]]]]]]].
  exists pre1, p, c, mid1, mid2, post.
  assert (Heq : (pre1 ++ CHECK p c :: mid1) ++ COMMIT p c :: mid2
                = pre1 ++ CHECK p c :: mid1 ++ COMMIT p c :: mid2)
    by (rewrite <- app_assoc; reflexivity).
  rewrite Heq in Hok.
  split; [rewrite Heq, <- app_assoc; simpl; rewrite <- app_assoc; reflexivity |].
  split; [exact Hck |]. split; [exact Hcm |]. split; [exact Hok |].
  split; [exact Hv | exact Hun].
Qed.

(* ================================================================= *)
(* The price of an earned certificate.                                *)
(* ================================================================= *)

Theorem multi_certified_run_min_cost : forall s0 tr,
  clean_start s0 -> cert (run tr s0) = true ->
  total_cost tr >= 3 /\ mu (run tr s0) >= mu s0 + 3.
Proof.
  intros s0 tr H0 H1.
  assert (Hc : total_cost tr >= 3).
  { destruct (multi_earned_certification_provenance s0 tr H0 H1)
      as [pre1 [p [c [mid1 [mid2 [post [-> _]]]]]]].
    rewrite multi_total_cost_app. simpl. rewrite multi_total_cost_app. simpl.
    rewrite multi_total_cost_app. simpl. lia. }
  split; [exact Hc | rewrite multi_mu_conservation_trace; lia].
Qed.

Corollary multi_program_certified_min_cost : forall n P vs,
  cert (run_prog n P (start vs)) = true -> mu (run_prog n P (start vs)) >= 3.
Proof.
  intros n P vs H. rewrite multi_run_prog_trace in *.
  apply (multi_certified_run_min_cost (start vs)) in H;
    [simpl in H; lia | apply multi_start_clean].
Qed.

(* ================================================================= *)
(* Single CHECK, COMMIT and CERTIFY steps.                            *)
(* ================================================================= *)

Lemma multi_exec_check_pass : forall s p c,
  check_ok (core_of s) p c = true ->
  exec s (CHECK p c) =
  mkst (record_fact (core_of s) (claim (core_of s) p c)) (mu s + 1) (cert s).
Proof.
  intros [k m r] p c H. simpl in *.
  assert (He : err k = false)
    by (unfold check_ok in H; destruct (err k); [discriminate | reflexivity]).
  unfold exec, cexec. simpl. rewrite He, H. simpl. rewrite orb_false_r. reflexivity.
Qed.

Lemma multi_exec_check_fail : forall s p c,
  err (core_of s) = false -> check_ok (core_of s) p c = false ->
  exec s (CHECK p c) = mkst (trap (core_of s)) (mu s + 1) (cert s).
Proof.
  intros [k m r] p c He H. simpl in *.
  unfold exec, cexec. simpl. rewrite He, H. simpl. rewrite orb_false_r. reflexivity.
Qed.

Lemma multi_exec_commit_pass : forall s p c,
  commit_ok (core_of s) p c = true ->
  exec s (COMMIT p c) =
  mkst (commit_to (core_of s) (claim (core_of s) p c)) (mu s + 1) (cert s).
Proof.
  intros [k m r] p c H. simpl in *.
  assert (He : err k = false) by (apply multi_commit_ok_iff in H; apply H).
  unfold exec, cexec. simpl. rewrite He, H. simpl. rewrite orb_false_r. reflexivity.
Qed.

Lemma multi_exec_commit_fail : forall s p c,
  err (core_of s) = false -> commit_ok (core_of s) p c = false ->
  exec s (COMMIT p c) = mkst (trap (core_of s)) (mu s + 1) (cert s).
Proof.
  intros [k m r] p c He H. simpl in *.
  unfold exec, cexec. simpl. rewrite He, H. simpl. rewrite orb_false_r. reflexivity.
Qed.

Lemma multi_exec_certify_pass : forall s,
  certify_ok (core_of s) = true ->
  exec s CERTIFY = mkst (goto (core_of s) (S (pc (core_of s)))) (mu s + 1) true.
Proof.
  intros [k m r] H. simpl in *.
  assert (He : err k = false)
    by (unfold certify_ok in H; destruct (err k); [discriminate | reflexivity]).
  unfold exec, cexec. simpl. rewrite He, H, orb_true_r. reflexivity.
Qed.

Lemma multi_exec_certify_fail : forall s,
  err (core_of s) = false -> certify_ok (core_of s) = false ->
  exec s CERTIFY = mkst (trap (core_of s)) (mu s + 1) (cert s).
Proof.
  intros [k m r] He H. simpl in *.
  unfold exec, cexec. simpl. rewrite He, H, orb_false_r. reflexivity.
Qed.

(* ================================================================= *)
(* The three-instruction chain on one property.                       *)
(* ================================================================= *)

Definition chain (p : prop) (c : reg) : list instr := [CHECK p c; COMMIT p c; CERTIFY].

(* From a start where p holds of register c, the chain certifies and pays
   exactly the floor of 3. *)
Theorem multi_chain_certifies : forall p c vs,
  holds p (vs c) ->
  cert (run_prog 4 (chain p c) (start vs)) = true /\
  mu (run_prog 4 (chain p c) (start vs)) = 3.
Proof.
  intros p c vs H. apply eval_iff in H.
  assert (Hck : check_ok (start_core vs) p c = true)
    by (unfold check_ok; simpl; rewrite H; reflexivity).
  set (P := chain p c).
  change (run_prog 4 P (start vs)) with (step P (step P (step P (step P (start vs))))).
  assert (E1 : step P (start vs) = exec (start vs) (CHECK p c)) by reflexivity.
  rewrite E1, (multi_exec_check_pass (start vs) p c Hck).
  change (core_of (start vs)) with (start_core vs).
  set (k1 := record_fact (start_core vs) (claim (start_core vs) p c)).
  assert (Hcm : commit_ok k1 p c = true).
  { apply multi_commit_ok_iff. split; [reflexivity |]. left. reflexivity. }
  set (s1 := mkst k1 (mu (start vs) + 1) (cert (start vs))).
  assert (E2 : step P s1 = exec s1 (COMMIT p c)) by reflexivity.
  rewrite E2, (multi_exec_commit_pass s1 p c Hcm).
  split; reflexivity.
Qed.

(* From a start where p fails on register c, the CHECK traps, and no number
   of further steps raises the flag. *)
Theorem multi_chain_refused_forever : forall n p c vs,
  ~ holds p (vs c) ->
  cert (run_prog n (chain p c) (start vs)) = false /\
  (n >= 1 -> err (core_of (run_prog n (chain p c) (start vs))) = true).
Proof.
  intros n p c vs H.
  assert (He : eval p (vs c) = false)
    by (destruct (eval p _) eqn:E; [exfalso; apply H, eval_iff, E | reflexivity]).
  assert (Hck : check_ok (start_core vs) p c = false)
    by (unfold check_ok; simpl; rewrite He; reflexivity).
  destruct n as [| n]; [split; [reflexivity | lia] |].
  set (P := chain p c).
  change (run_prog (S n) P (start vs)) with (run_prog n P (step P (start vs))).
  assert (E1 : step P (start vs) = exec (start vs) (CHECK p c)) by reflexivity.
  rewrite E1, (multi_exec_check_fail (start vs) p c eq_refl Hck).
  rewrite multi_run_prog_trapped by reflexivity.
  split; [reflexivity | intros _; reflexivity].
Qed.

(* So the chain certifies exactly when p holds of the start value. *)
Corollary multi_chain_certifies_iff : forall p c vs,
  cert (run_prog 4 (chain p c) (start vs)) = true <-> holds p (vs c).
Proof.
  intros p c vs. split.
  - intro H1. apply eval_iff.
    destruct (eval p (vs c)) eqn:E; [reflexivity | exfalso].
    assert (Hn : ~ holds p (vs c))
      by (intro Hh; apply eval_iff in Hh; congruence).
    destruct (multi_chain_refused_forever 4 p c vs Hn) as [H2 _]. congruence.
  - intro H. apply multi_chain_certifies, H.
Qed.

End Multi.

(* ================================================================= *)
(* Assumption audit. Every line must print                            *)
(* "Closed under the global context".                                 *)
(* ================================================================= *)

Print Assumptions multi_fact_eqb_eq.
Print Assumptions multi_run_prog_trace.
Print Assumptions multi_run_prog_add.
Print Assumptions multi_trapped_halted.
Print Assumptions multi_step_trapped.
Print Assumptions multi_run_prog_trapped.
Print Assumptions multi_err_permanent.
Print Assumptions multi_mu_conservation_trace.
Print Assumptions multi_mu_conservation_program.
Print Assumptions multi_cert_latch.
Print Assumptions multi_cert_permanent.
Print Assumptions multi_only_certify_certifies.
Print Assumptions multi_a2.
Print Assumptions multi_nfi_floor.
Print Assumptions multi_facts_step.
Print Assumptions multi_facts_keep.
Print Assumptions multi_full_table_traps.
Print Assumptions multi_facts_bounded_step.
Print Assumptions multi_unearned_commit_traps.
Print Assumptions multi_uncommitted_certify_traps.
Print Assumptions multi_frame_cexec.
Print Assumptions multi_plain_step.
Print Assumptions multi_frame_step.
Print Assumptions multi_frame_run.
Print Assumptions multi_plain_run.
Print Assumptions multi_checker_soundness.
Print Assumptions multi_committed_claim_holds.
Print Assumptions multi_no_forging_step.
Print Assumptions multi_no_forging.
Print Assumptions multi_earned_commitment_provenance.
Print Assumptions multi_earned_certification_provenance.
Print Assumptions multi_certified_run_min_cost.
Print Assumptions multi_program_certified_min_cost.
Print Assumptions multi_exec_certify_pass.
Print Assumptions multi_chain_certifies.
Print Assumptions multi_chain_refused_forever.
Print Assumptions multi_chain_certifies_iff.
