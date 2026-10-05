(** EarnedMultiPriced.v: the machine of EarnedMulti.v with one more
    instruction, PAY.

    Everything of EarnedMulti.v is kept: a counter for every register
    r : nat (values vals, versions vers), INC, DEC, HALT, CHECK, COMMIT and
    CERTIFY with their costs, the fact table with cap 16, the commitment
    channel, the trap latch, the ledger and the flag. The one addition:

      PAY      costs 1, moves pc to the next address, and changes nothing
               else: no register, no version, no fact, no channel, no
               trap, no flag. On a trapped machine it does nothing, like
               every instruction.

    PAY is the paid move that does no record work. A host that runs a
    guest whose moves have prices pays a guest price above the record
    cost with PAY, so its ledger can follow the guest's ledger exactly.

    Every definition of EarnedMulti.v is restated under a pu_ name (pu_exec,
    pu_run_prog, pu_check_ok, ...; the record fields and the constructors
    keep their names), and every theorem under a pu_multi_ name, proved
    here with PAY among the instructions. PAY never raises the flag
    (pu_multi_pay_never_fires), and its effect is exactly a jump to the
    next address with the ledger one higher (pu_multi_exec_pay).

    Dependencies: Coq standard library only. No axioms, no Admitted.        *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose, as in
   EarnedMulti.v: this file imports nothing but the Coq standard library so
   anyone can re-check it from a clean checkout. Its link to the abstract
   record (the host machine running the fixed program U_P, meeting
   thiele_complete of ThieleComplete.v) lives in UniversalPRun.v. *)

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
Definition pu_reg : Type := nat.

(* A fact is a claim about one version of one register. *)
Record pu_fact : Type := mkfact { f_prop : prop; f_reg : pu_reg; f_ver : nat }.

(* Exact claim identity: field by field, no digest. *)
Definition pu_fact_eqb (f g : pu_fact) : bool :=
  prop_eqb (f_prop f) (f_prop g) && Nat.eqb (f_reg f) (f_reg g)
  && Nat.eqb (f_ver f) (f_ver g).

Lemma pu_multi_prop_eqb_refl : forall p, prop_eqb p p = true.
Proof. intro p. apply prop_eqb_eq. reflexivity. Qed.

Lemma pu_multi_fact_eqb_eq : forall f g, pu_fact_eqb f g = true <-> f = g.
Proof.
  intros [p c v] [q d w]. unfold pu_fact_eqb. simpl.
  rewrite !andb_true_iff, !Nat.eqb_eq, prop_eqb_eq. split.
  - intros [[Hp Hc] Hv]. subst. reflexivity.
  - intros H. inversion H. subst. auto.
Qed.

(* ================================================================= *)
(* The machine.                                                       *)
(* ================================================================= *)

Inductive pu_instr : Type :=
| INC (r : pu_reg)              (* r := r + 1                               *)
| DEC (r : pu_reg) (j : nat)    (* if r > 0 then r := r - 1, jump to j      *)
| HALT
| CHECK (p : prop) (r : pu_reg)
| COMMIT (p : prop) (r : pu_reg)
| CERTIFY
| PAY.                       (* cost 1, pc + 1, nothing else           *)

Definition pu_cost (i : pu_instr) : nat :=
  match i with
  | CHECK _ _ | COMMIT _ _ | CERTIFY | PAY => 1
  | _ => 0
  end.

(* Everything except the ledger and the flag. *)
Record pu_core : Type := mkcore {
  vals : nat -> nat;        (* the value of each register   *)
  vers : nat -> nat;        (* the version of each register *)
  pc : nat;                 (* 1-based, as in Minsky        *)
  facts : list pu_fact;        (* established facts            *)
  chan : option pu_fact;       (* the commitment channel       *)
  err : bool                (* the trap latch               *)
}.

(* A function that agrees with f except at r, where it is v. *)
Definition pu_upd (f : nat -> nat) (r v : nat) : nat -> nat :=
  fun x => if Nat.eqb x r then v else f x.

(* A write sets register r, bumps its version, and moves pc to j. *)
Definition pu_write (k : pu_core) (r : pu_reg) (n j : nat) : pu_core :=
  mkcore (pu_upd (vals k) r n) (pu_upd (vers k) r (S (vers k r))) j
         (facts k) (chan k) (err k).
Definition pu_goto (k : pu_core) (j : nat) : pu_core :=
  mkcore (vals k) (vers k) j (facts k) (chan k) (err k).
Definition pu_trap (k : pu_core) : pu_core :=
  mkcore (vals k) (vers k) (pc k) (facts k) (chan k) true.
Definition pu_record_fact (k : pu_core) (f : pu_fact) : pu_core :=
  mkcore (vals k) (vers k) (S (pc k)) (f :: facts k) (chan k) (err k).
Definition pu_commit_to (k : pu_core) (f : pu_fact) : pu_core :=
  mkcore (vals k) (vers k) (S (pc k)) (facts k) (Some f) (err k).

Definition pu_fact_cap : nat := 16.

(* The claim "p holds of r" about r's current version. *)
Definition pu_claim (k : pu_core) (p : prop) (r : pu_reg) : pu_fact := mkfact p r (vers k r).

Definition pu_check_ok (k : pu_core) (p : prop) (r : pu_reg) : bool :=
  negb (err k) && eval p (vals k r) && Nat.ltb (length (facts k)) pu_fact_cap.
Definition pu_commit_ok (k : pu_core) (p : prop) (r : pu_reg) : bool :=
  negb (err k) && existsb (pu_fact_eqb (pu_claim k p r)) (facts k).
Definition pu_certify_ok (k : pu_core) : bool :=
  negb (err k) && match chan k with Some _ => true | None => false end.

Definition pu_cexec (k : pu_core) (i : pu_instr) : pu_core :=
  if err k then k else
  match i with
  | INC r => pu_write k r (S (vals k r)) (S (pc k))
  | DEC r j =>
      match vals k r with
      | 0 => pu_goto k (S (pc k))
      | S n => pu_write k r n j
      end
  | HALT => k
  | CHECK p r => if pu_check_ok k p r then pu_record_fact k (pu_claim k p r) else pu_trap k
  | COMMIT p r => if pu_commit_ok k p r then pu_commit_to k (pu_claim k p r) else pu_trap k
  | CERTIFY => if pu_certify_ok k then pu_goto k (S (pc k)) else pu_trap k
  | PAY => pu_goto k (S (pc k))
  end.

(* The one event that raises the flag. *)
Definition pu_fires (k : pu_core) (i : pu_instr) : bool :=
  match i with CERTIFY => pu_certify_ok k | _ => false end.

Record pu_state : Type := mkst { core_of : pu_core; mu : nat; cert : bool }.

Definition pu_exec (s : pu_state) (i : pu_instr) : pu_state :=
  mkst (pu_cexec (core_of s) i) (mu s + pu_cost i) (cert s || pu_fires (core_of s) i).

Fixpoint pu_run (tr : list pu_instr) (s : pu_state) : pu_state :=
  match tr with [] => s | i :: rest => pu_run rest (pu_exec s i) end.

Fixpoint pu_total_cost (tr : list pu_instr) : nat :=
  match tr with [] => 0 | i :: rest => pu_cost i + pu_total_cost rest end.

(* A start: the given register values, every version 0, pc 1, no facts,
   an empty channel, no trap, an empty ledger, the flag down. *)
Definition pu_start_core (vs : nat -> nat) : pu_core :=
  mkcore vs (fun _ => 0) 1 [] None false.
Definition pu_start (vs : nat -> nat) : pu_state := mkst (pu_start_core vs) 0 false.

Definition pu_clean_start (s : pu_state) : Prop :=
  facts (core_of s) = [] /\ chan (core_of s) = None /\ cert s = false.

Lemma pu_multi_start_clean : forall vs, pu_clean_start (pu_start vs).
Proof. intros. repeat split. Qed.

(* Stored programs. *)
Definition pu_fetch {A : Type} (P : list A) (n : nat) : option A :=
  match n with 0 => None | S m => nth_error P m end.

Definition pu_next_instr (P : list pu_instr) (k : pu_core) : option pu_instr :=
  if err k then None else
  match pu_fetch P (pc k) with Some HALT => None | o => o end.

Definition pu_halted (P : list pu_instr) (k : pu_core) : Prop := pu_next_instr P k = None.

Definition pu_step (P : list pu_instr) (s : pu_state) : pu_state :=
  match pu_next_instr P (core_of s) with None => s | Some i => pu_exec s i end.

Fixpoint pu_run_prog (n : nat) (P : list pu_instr) (s : pu_state) : pu_state :=
  match n with 0 => s | S m => pu_run_prog m P (pu_step P s) end.

(* The instructions a program run actually executes. *)
Fixpoint pu_trace_of (n : nat) (P : list pu_instr) (s : pu_state) : list pu_instr :=
  match n with
  | 0 => []
  | S m => match pu_next_instr P (core_of s) with
           | None => []
           | Some i => i :: pu_trace_of m P (pu_exec s i)
           end
  end.

Lemma pu_multi_run_app : forall l1 l2 s, pu_run (l1 ++ l2) s = pu_run l2 (pu_run l1 s).
Proof. induction l1; intros; simpl; auto. Qed.

Lemma pu_multi_run_snoc : forall l i s, pu_run (l ++ [i]) s = pu_exec (pu_run l s) i.
Proof. intros. rewrite pu_multi_run_app. reflexivity. Qed.

Lemma pu_multi_total_cost_app : forall l1 l2,
  pu_total_cost (l1 ++ l2) = pu_total_cost l1 + pu_total_cost l2.
Proof. induction l1; intros; simpl; [| rewrite IHl1]; lia. Qed.

Lemma pu_multi_run_prog_halted : forall n P s, pu_halted P (core_of s) -> pu_run_prog n P s = s.
Proof.
  induction n; intros P s H; simpl; [reflexivity |].
  unfold pu_step. unfold pu_halted in H. rewrite H. apply IHn. exact H.
Qed.

Lemma pu_multi_run_prog_trace : forall n P s, pu_run_prog n P s = pu_run (pu_trace_of n P s) s.
Proof.
  induction n; intros P s; simpl; [reflexivity |].
  unfold pu_step. destruct (pu_next_instr P (core_of s)) eqn:H.
  - apply IHn.
  - apply pu_multi_run_prog_halted. exact H.
Qed.

Lemma pu_multi_run_prog_add : forall n m P s,
  pu_run_prog (n + m) P s = pu_run_prog m P (pu_run_prog n P s).
Proof. induction n; intros m P s; simpl; [reflexivity | apply IHn]. Qed.

Lemma pu_multi_run_prog_succ : forall n P s,
  pu_run_prog (S n) P s = pu_step P (pu_run_prog n P s).
Proof.
  intros n P s. replace (S n) with (n + 1) by lia.
  rewrite pu_multi_run_prog_add. reflexivity.
Qed.

(* ================================================================= *)
(* A trapped machine takes no further step.                           *)
(* ================================================================= *)

Lemma pu_multi_cexec_trapped : forall k i, err k = true -> pu_cexec k i = k.
Proof. intros k i H. unfold pu_cexec. rewrite H. reflexivity. Qed.

Theorem pu_multi_trapped_halted : forall P k, err k = true -> pu_halted P k.
Proof. intros P k H. unfold pu_halted, pu_next_instr. rewrite H. reflexivity. Qed.

Theorem pu_multi_step_trapped : forall P s, err (core_of s) = true -> pu_step P s = s.
Proof. intros P s H. unfold pu_step, pu_next_instr. rewrite H. reflexivity. Qed.

Lemma pu_multi_run_prog_trapped : forall n P s,
  err (core_of s) = true -> pu_run_prog n P s = s.
Proof.
  intros n P s H. apply pu_multi_run_prog_halted, pu_multi_trapped_halted, H.
Qed.

(* The trap latch never resets. *)
Lemma pu_multi_err_permanent : forall k i, err k = true -> err (pu_cexec k i) = true.
Proof. intros k i H. rewrite pu_multi_cexec_trapped by exact H. exact H. Qed.

(* ================================================================= *)
(* The toll, the ledger, the latch.                                   *)
(* ================================================================= *)

Theorem pu_multi_mu_conservation_trace : forall tr s, mu (pu_run tr s) = mu s + pu_total_cost tr.
Proof. induction tr; intros; simpl; [lia | rewrite IHtr; simpl; lia]. Qed.

Theorem pu_multi_mu_conservation_program : forall n P s,
  mu (pu_run_prog n P s) = mu s + pu_total_cost (pu_trace_of n P s).
Proof. intros. rewrite pu_multi_run_prog_trace. apply pu_multi_mu_conservation_trace. Qed.

Theorem pu_multi_cert_latch : forall s i, cert (pu_exec s i) = cert s || pu_fires (core_of s) i.
Proof. reflexivity. Qed.

Theorem pu_multi_cert_permanent : forall s i, cert s = true -> cert (pu_exec s i) = true.
Proof. intros s i H. simpl. rewrite H. reflexivity. Qed.

Theorem pu_multi_only_certify_certifies : forall s i,
  cert s = false -> cert (pu_exec s i) = true ->
  i = CERTIFY /\ pu_certify_ok (core_of s) = true.
Proof.
  intros s i H0 H1. simpl in H1. rewrite H0 in H1. simpl in H1.
  destruct i; simpl in H1; try discriminate. auto.
Qed.

Theorem pu_multi_a2 : forall s i, cert s = false -> cert (pu_exec s i) = true -> pu_cost i >= 1.
Proof.
  intros s i H0 H1. destruct (pu_multi_only_certify_certifies s i H0 H1) as [-> _].
  simpl. lia.
Qed.

Theorem pu_multi_nfi_floor : forall tr s,
  cert s = false -> cert (pu_run tr s) = true -> pu_total_cost tr >= 1.
Proof.
  induction tr as [| i rest IH]; intros s H0 H1; simpl in *; [congruence |].
  destruct (cert (pu_exec s i)) eqn:Hm.
  - pose proof (pu_multi_a2 s i H0 Hm). lia.
  - pose proof (IH _ Hm H1). lia.
Qed.

(* ================================================================= *)
(* Per-instruction facts about the substrate.                         *)
(* ================================================================= *)

Lemma pu_multi_ver_write : forall k r n j d,
  vers (pu_write k r n j) d = if Nat.eqb r d then S (vers k d) else vers k d.
Proof.
  intros. simpl. unfold pu_upd.
  destruct (Nat.eqb_spec d r), (Nat.eqb_spec r d); subst; congruence.
Qed.

Lemma pu_multi_val_write : forall k r n j d,
  vals (pu_write k r n j) d = if Nat.eqb r d then n else vals k d.
Proof.
  intros. simpl. unfold pu_upd.
  destruct (Nat.eqb_spec d r), (Nat.eqb_spec r d); subst; congruence.
Qed.

Lemma pu_multi_facts_write : forall k r n j, facts (pu_write k r n j) = facts k.
Proof. reflexivity. Qed.

Lemma pu_multi_chan_write : forall k r n j, chan (pu_write k r n j) = chan k.
Proof. reflexivity. Qed.

Lemma pu_multi_err_write : forall k r n j, err (pu_write k r n j) = err k.
Proof. reflexivity. Qed.

Lemma pu_multi_pc_write : forall k r n j, pc (pu_write k r n j) = j.
Proof. reflexivity. Qed.

Lemma pu_multi_ver_mono : forall k i c, vers k c <= vers (pu_cexec k i) c.
Proof.
  intros k i c. unfold pu_cexec. destruct (err k); [lia |].
  destruct i as [d | d j | | p d | p d | |].
  - rewrite pu_multi_ver_write. destruct (Nat.eqb d c); lia.
  - destruct (vals k d); [simpl; lia |].
    rewrite pu_multi_ver_write. destruct (Nat.eqb d c); lia.
  - lia.
  - destruct (pu_check_ok k p d); simpl; lia.
  - destruct (pu_commit_ok k p d); simpl; lia.
  - destruct (pu_certify_ok k); simpl; lia.
  - simpl; lia.
Qed.

Lemma pu_multi_ver_same_val : forall k i c,
  vers (pu_cexec k i) c = vers k c -> vals (pu_cexec k i) c = vals k c.
Proof.
  intros k i c H. unfold pu_cexec in *. destruct (err k); [reflexivity |].
  destruct i as [d | d j | | p d | p d | |].
  - rewrite pu_multi_ver_write in H. rewrite pu_multi_val_write.
    destruct (Nat.eqb d c); [lia | reflexivity].
  - destruct (vals k d); [reflexivity |].
    rewrite pu_multi_ver_write in H. rewrite pu_multi_val_write.
    destruct (Nat.eqb d c); [lia | reflexivity].
  - reflexivity.
  - destruct (pu_check_ok k p d); reflexivity.
  - destruct (pu_commit_ok k p d); reflexivity.
  - destruct (pu_certify_ok k); reflexivity.
  - reflexivity.
Qed.

Lemma pu_multi_ver_check : forall k p c d, vers (pu_cexec k (CHECK p c)) d = vers k d.
Proof.
  intros. unfold pu_cexec. destruct (err k); [reflexivity |].
  destruct (pu_check_ok k p c); reflexivity.
Qed.

Lemma pu_multi_val_check : forall k p c d, vals (pu_cexec k (CHECK p c)) d = vals k d.
Proof.
  intros. unfold pu_cexec. destruct (err k); [reflexivity |].
  destruct (pu_check_ok k p c); reflexivity.
Qed.

Theorem pu_multi_facts_step : forall k i f,
  In f (facts (pu_cexec k i)) ->
  In f (facts k) \/
  (i = CHECK (f_prop f) (f_reg f) /\ pu_check_ok k (f_prop f) (f_reg f) = true /\
   f = pu_claim k (f_prop f) (f_reg f)).
Proof.
  intros k i f H. unfold pu_cexec in H. destruct (err k) eqn:He; [auto |].
  destruct i as [d | d j | | p d | p d | |].
  - auto.
  - destruct (vals k d); auto.
  - auto.
  - destruct (pu_check_ok k p d) eqn:Hc; simpl in H; [| auto].
    destruct H as [<- | H]; [right | auto]. simpl. auto.
  - destruct (pu_commit_ok k p d); simpl in H; auto.
  - destruct (pu_certify_ok k); simpl in H; auto.
  - simpl in H; auto.
Qed.

Theorem pu_multi_facts_keep : forall k i f, In f (facts k) -> In f (facts (pu_cexec k i)).
Proof.
  intros k i f H. unfold pu_cexec. destruct (err k); [exact H |].
  destruct i as [d | d j | | p d | p d | |].
  - exact H.
  - destruct (vals k d); exact H.
  - exact H.
  - destruct (pu_check_ok k p d); simpl; auto.
  - destruct (pu_commit_ok k p d); simpl; auto.
  - destruct (pu_certify_ok k); simpl; auto.
  - simpl; auto.
Qed.

Theorem pu_multi_full_table_traps : forall k p c,
  pu_fact_cap <= length (facts k) ->
  err (pu_cexec k (CHECK p c)) = true /\ facts (pu_cexec k (CHECK p c)) = facts k.
Proof.
  intros k p c H. unfold pu_cexec. destruct (err k) eqn:He; [auto |].
  unfold pu_check_ok. rewrite He.
  replace (Nat.ltb (length (facts k)) pu_fact_cap) with false
    by (symmetry; apply Nat.ltb_ge; exact H).
  rewrite andb_false_r. auto.
Qed.

Theorem pu_multi_facts_bounded_step : forall k i,
  length (facts k) <= pu_fact_cap -> length (facts (pu_cexec k i)) <= pu_fact_cap.
Proof.
  intros k i H. unfold pu_cexec. destruct (err k); [exact H |].
  destruct i as [d | d j | | p d | p d | |].
  - exact H.
  - destruct (vals k d); exact H.
  - exact H.
  - destruct (pu_check_ok k p d) eqn:Hc; simpl; [| exact H].
    unfold pu_check_ok in Hc. apply andb_true_iff in Hc as [_ Hc].
    apply Nat.ltb_lt in Hc. lia.
  - destruct (pu_commit_ok k p d); simpl; exact H.
  - destruct (pu_certify_ok k); simpl; exact H.
  - simpl; exact H.
Qed.

Lemma pu_multi_chan_step : forall k i,
  chan (pu_cexec k i) = chan k \/
  exists p c, i = COMMIT p c /\ pu_commit_ok k p c = true /\
              chan (pu_cexec k i) = Some (pu_claim k p c).
Proof.
  intros k i. unfold pu_cexec. destruct (err k); [auto |].
  destruct i as [d | d j | | p d | p d | |].
  - auto.
  - destruct (vals k d); auto.
  - auto.
  - destruct (pu_check_ok k p d); simpl; auto.
  - destruct (pu_commit_ok k p d) eqn:Hc; simpl; [right; eauto | auto].
  - destruct (pu_certify_ok k); simpl; auto.
  - simpl; auto.
Qed.

Lemma pu_multi_commit_ok_iff : forall k p c,
  pu_commit_ok k p c = true <-> err k = false /\ In (pu_claim k p c) (facts k).
Proof.
  intros. unfold pu_commit_ok. rewrite andb_true_iff, negb_true_iff, existsb_exists.
  split.
  - intros [He [f [Hin Hf]]]. apply pu_multi_fact_eqb_eq in Hf. subst. auto.
  - intros [He Hin]. split; [exact He |]. exists (pu_claim k p c).
    split; [exact Hin | apply pu_multi_fact_eqb_eq; reflexivity].
Qed.

Theorem pu_multi_unearned_commit_traps : forall k p c,
  pu_commit_ok k p c = false ->
  err (pu_cexec k (COMMIT p c)) = true /\
  chan (pu_cexec k (COMMIT p c)) = chan k /\ facts (pu_cexec k (COMMIT p c)) = facts k.
Proof.
  intros k p c H. unfold pu_cexec. destruct (err k) eqn:He; [auto |].
  rewrite H. auto.
Qed.

Theorem pu_multi_uncommitted_certify_traps : forall s,
  pu_certify_ok (core_of s) = false ->
  err (core_of (pu_exec s CERTIFY)) = true /\ cert (pu_exec s CERTIFY) = cert s.
Proof.
  intros [k m r] H. simpl in *. rewrite H, orb_false_r. unfold pu_cexec.
  destruct (err k) eqn:He; [auto |]. rewrite H. auto.
Qed.

(* ================================================================= *)
(* The frame: registers an instruction does not name.                 *)
(* ================================================================= *)

(* Instruction i names register r. *)
Definition pu_mentions (i : pu_instr) (r : pu_reg) : bool :=
  match i with
  | INC d | DEC d _ | CHECK _ d | COMMIT _ d => Nat.eqb d r
  | HALT | CERTIFY | PAY => false
  end.

(* Instruction i is an INC or a DEC. *)
Definition pu_plain (i : pu_instr) : bool :=
  match i with INC _ | DEC _ _ => true | _ => false end.

Lemma pu_multi_frame_cexec : forall k i r,
  pu_mentions i r = false ->
  vals (pu_cexec k i) r = vals k r /\ vers (pu_cexec k i) r = vers k r.
Proof.
  intros k i r H. unfold pu_cexec. destruct (err k); [auto |].
  destruct i as [d | d j | | p d | p d | |]; simpl in H.
  - rewrite pu_multi_val_write, pu_multi_ver_write, H. auto.
  - destruct (vals k d); [auto |].
    rewrite pu_multi_val_write, pu_multi_ver_write, H. auto.
  - auto.
  - destruct (pu_check_ok k p d); auto.
  - destruct (pu_commit_ok k p d); auto.
  - destruct (pu_certify_ok k); auto.
  - simpl; auto.
Qed.

Lemma pu_multi_plain_cexec : forall k i,
  pu_plain i = true ->
  facts (pu_cexec k i) = facts k /\ chan (pu_cexec k i) = chan k /\ err (pu_cexec k i) = err k.
Proof.
  intros k i H. unfold pu_cexec. destruct (err k) eqn:He; [auto |].
  destruct i as [d | d j | | p d | p d | |]; simpl in H; try discriminate.
  - auto.
  - destruct (vals k d); auto.
Qed.

Theorem pu_multi_plain_step : forall s i,
  pu_plain i = true ->
  facts (core_of (pu_exec s i)) = facts (core_of s) /\
  chan (core_of (pu_exec s i)) = chan (core_of s) /\
  err (core_of (pu_exec s i)) = err (core_of s) /\
  mu (pu_exec s i) = mu s /\ cert (pu_exec s i) = cert s.
Proof.
  intros s i H. destruct (pu_multi_plain_cexec (core_of s) i H) as [Hf [Hc He]].
  simpl. rewrite Hf, Hc, He.
  destruct i; simpl in H; try discriminate; simpl;
    rewrite Nat.add_0_r, orb_false_r; auto.
Qed.

(* An instruction that does not mention r leaves r's value and version
   alone; an INC or DEC also leaves the fact table, channel, trap latch,
   ledger and flag alone. *)
Theorem pu_multi_frame_step : forall s i r,
  pu_mentions i r = false ->
  vals (core_of (pu_exec s i)) r = vals (core_of s) r /\
  vers (core_of (pu_exec s i)) r = vers (core_of s) r /\
  (pu_plain i = true ->
   facts (core_of (pu_exec s i)) = facts (core_of s) /\
   chan (core_of (pu_exec s i)) = chan (core_of s) /\
   err (core_of (pu_exec s i)) = err (core_of s) /\
   mu (pu_exec s i) = mu s /\ cert (pu_exec s i) = cert s).
Proof.
  intros s i r H. destruct (pu_multi_frame_cexec (core_of s) i r H) as [Hv Hw].
  split; [exact Hv |]. split; [exact Hw |]. apply pu_multi_plain_step.
Qed.

Theorem pu_multi_frame_run : forall tr s r,
  (forall i, In i tr -> pu_mentions i r = false) ->
  vals (core_of (pu_run tr s)) r = vals (core_of s) r /\
  vers (core_of (pu_run tr s)) r = vers (core_of s) r.
Proof.
  induction tr as [| i tr IH]; intros s r H; simpl; [auto |].
  destruct (IH (pu_exec s i) r) as [Hv Hw]; [intros i' Hi; apply H; right; exact Hi |].
  destruct (pu_multi_frame_cexec (core_of s) i r (H i (or_introl eq_refl))) as [Hv' Hw'].
  simpl in *. rewrite Hv, Hw, Hv', Hw'. auto.
Qed.

Theorem pu_multi_plain_run : forall tr s,
  (forall i, In i tr -> pu_plain i = true) ->
  facts (core_of (pu_run tr s)) = facts (core_of s) /\
  chan (core_of (pu_run tr s)) = chan (core_of s) /\
  err (core_of (pu_run tr s)) = err (core_of s) /\
  mu (pu_run tr s) = mu s /\ cert (pu_run tr s) = cert s.
Proof.
  induction tr as [| i tr IH]; intros s H; simpl; [auto |].
  destruct (IH (pu_exec s i)) as [Hf [Hc [He [Hm Hcert]]]];
    [intros i' Hi; apply H; right; exact Hi |].
  destruct (pu_multi_plain_step s i (H i (or_introl eq_refl)))
    as [Hf' [Hc' [He' [Hm' Hcert']]]].
  rewrite Hf, Hc, He, Hm, Hcert, Hf', Hc', He', Hm', Hcert'. auto.
Qed.

(* ================================================================= *)
(* Runs: versions only grow, equal version means equal value.         *)
(* ================================================================= *)

Lemma pu_multi_ver_mono_run : forall l s c,
  vers (core_of s) c <= vers (core_of (pu_run l s)) c.
Proof.
  induction l as [| i l IH]; intros s c; simpl; [lia |].
  pose proof (pu_multi_ver_mono (core_of s) i c). pose proof (IH (pu_exec s i) c).
  simpl in *. lia.
Qed.

Definition pu_untouched (s : pu_state) (mid : list pu_instr) (c : pu_reg) : Prop :=
  forall t1 i t2, mid = t1 ++ i :: t2 ->
    let k := core_of (pu_run t1 s) in
    vers (pu_cexec k i) c = vers k c /\ vals (pu_cexec k i) c = vals k c.

Lemma pu_multi_untouched_of_ver : forall s mid c,
  vers (core_of (pu_run mid s)) c = vers (core_of s) c -> pu_untouched s mid c.
Proof.
  intros s mid c H t1 i t2 ->. simpl.
  rewrite pu_multi_run_app in H. simpl in H.
  pose proof (pu_multi_ver_mono_run t1 s c).
  pose proof (pu_multi_ver_mono (core_of (pu_run t1 s)) i c).
  pose proof (pu_multi_ver_mono_run t2 (pu_exec (pu_run t1 s) i) c). simpl in *.
  assert (Hv : vers (pu_cexec (core_of (pu_run t1 s)) i) c = vers (core_of (pu_run t1 s)) c)
    by lia.
  split; [exact Hv | apply pu_multi_ver_same_val; exact Hv].
Qed.

(* ================================================================= *)
(* Checker soundness.                                                 *)
(* ================================================================= *)

Definition pu_sound (k : pu_core) : Prop :=
  forall f, In f (facts k) ->
    f_ver f <= vers k (f_reg f) /\
    (f_ver f = vers k (f_reg f) -> holds (f_prop f) (vals k (f_reg f))).

Lemma pu_multi_sound_step : forall k i, pu_sound k -> pu_sound (pu_cexec k i).
Proof.
  intros k i Hs f Hin.
  pose proof (pu_multi_ver_mono k i (f_reg f)) as Hm.
  destruct (pu_multi_facts_step k i f Hin) as [Hold | [Hi [Hc Hf]]].
  - destruct (Hs f Hold) as [Hle Hlive]. split; [lia |].
    intro Heq. assert (Hv : vers (pu_cexec k i) (f_reg f) = vers k (f_reg f)) by lia.
    rewrite (pu_multi_ver_same_val k i _ Hv). apply Hlive. lia.
  - subst i. rewrite pu_multi_ver_check, pu_multi_val_check.
    rewrite Hf. simpl. split; [lia | intros _].
    unfold pu_check_ok in Hc. apply andb_true_iff in Hc as [Hc _].
    apply andb_true_iff in Hc as [_ Hc]. apply eval_iff. exact Hc.
Qed.

Lemma pu_multi_sound_run : forall tr s, pu_sound (core_of s) -> pu_sound (core_of (pu_run tr s)).
Proof.
  induction tr; intros s H; simpl; [exact H | apply IHtr, pu_multi_sound_step, H].
Qed.

Theorem pu_multi_checker_soundness : forall s0 tr f,
  pu_clean_start s0 ->
  let k := core_of (pu_run tr s0) in
  In f (facts k) -> f_ver f = vers k (f_reg f) -> holds (f_prop f) (vals k (f_reg f)).
Proof.
  intros s0 tr f [Hf _] k Hin Hv.
  assert (Hs0 : pu_sound (core_of s0)) by (intros g Hg; rewrite Hf in Hg; destruct Hg).
  exact (proj2 (pu_multi_sound_run tr s0 Hs0 f Hin) Hv).
Qed.

Corollary pu_multi_committed_claim_holds : forall s0 tr p c,
  pu_clean_start s0 ->
  pu_commit_ok (core_of (pu_run tr s0)) p c = true ->
  holds p (vals (core_of (pu_run tr s0)) c).
Proof.
  intros s0 tr p c H0 Hc. apply pu_multi_commit_ok_iff in Hc as [_ Hin].
  exact (pu_multi_checker_soundness s0 tr _ H0 Hin eq_refl).
Qed.

(* ================================================================= *)
(* No forging, over any run.                                          *)
(* ================================================================= *)

Definition pu_earned (s0 : pu_state) (tr : list pu_instr) (f : pu_fact) : Prop :=
  exists pre mid,
    tr = pre ++ CHECK (f_prop f) (f_reg f) :: mid /\
    pu_check_ok (core_of (pu_run pre s0)) (f_prop f) (f_reg f) = true /\
    f = pu_claim (core_of (pu_run pre s0)) (f_prop f) (f_reg f) /\
    (f_ver f = vers (core_of (pu_run tr s0)) (f_reg f) ->
     pu_untouched (pu_run (pre ++ [CHECK (f_prop f) (f_reg f)]) s0) mid (f_reg f)).

Definition pu_no_forgery (s0 : pu_state) (tr : list pu_instr) : Prop :=
  forall f, In f (facts (core_of (pu_run tr s0))) -> pu_earned s0 tr f.

Lemma pu_multi_earned_intro : forall s0 pre mid f,
  pu_check_ok (core_of (pu_run pre s0)) (f_prop f) (f_reg f) = true ->
  f = pu_claim (core_of (pu_run pre s0)) (f_prop f) (f_reg f) ->
  pu_earned s0 (pre ++ CHECK (f_prop f) (f_reg f) :: mid) f.
Proof.
  intros s0 pre mid f Hc Hf. exists pre, mid.
  split; [reflexivity |]. split; [exact Hc |]. split; [exact Hf |].
  intro Hlive. apply pu_multi_untouched_of_ver.
  replace (pre ++ CHECK (f_prop f) (f_reg f) :: mid)
    with ((pre ++ [CHECK (f_prop f) (f_reg f)]) ++ mid) in Hlive
    by (rewrite <- app_assoc; reflexivity).
  rewrite pu_multi_run_app in Hlive. rewrite <- Hlive.
  rewrite pu_multi_run_snoc. simpl. rewrite pu_multi_ver_check.
  rewrite Hf at 1. reflexivity.
Qed.

Theorem pu_multi_no_forging_step : forall s0 tr i,
  pu_no_forgery s0 tr -> pu_no_forgery s0 (tr ++ [i]).
Proof.
  intros s0 tr i Hnf f Hin. rewrite pu_multi_run_snoc in Hin. simpl in Hin.
  destruct (pu_multi_facts_step _ i f Hin) as [Hold | [Hi [Hc Hf]]].
  - destruct (Hnf f Hold) as [pre [mid [Htr [Hc [Hf _]]]]].
    rewrite Htr, <- app_assoc. simpl. apply pu_multi_earned_intro; assumption.
  - subst i. apply pu_multi_earned_intro; assumption.
Qed.

Theorem pu_multi_no_forging : forall s0 tr, pu_clean_start s0 -> pu_no_forgery s0 tr.
Proof.
  intros s0 tr [Hf _]. induction tr as [| i tr IH] using rev_ind.
  - intros f Hin. simpl in Hin. rewrite Hf in Hin. destruct Hin.
  - apply pu_multi_no_forging_step, IH.
Qed.

(* ================================================================= *)
(* Earned provenance.                                                 *)
(* ================================================================= *)

Theorem pu_multi_earned_commitment_provenance : forall s0 pre p c,
  pu_clean_start s0 ->
  pu_commit_ok (core_of (pu_run pre s0)) p c = true ->
  exists pre1 mid,
    pre = pre1 ++ CHECK p c :: mid /\
    pu_check_ok (core_of (pu_run pre1 s0)) p c = true /\
    pu_cost (CHECK p c) >= 1 /\ pu_cost (COMMIT p c) >= 1 /\
    vers (core_of (pu_run pre1 s0)) c = vers (core_of (pu_run pre s0)) c /\
    pu_untouched (pu_run (pre1 ++ [CHECK p c]) s0) mid c.
Proof.
  intros s0 pre p c H0 Hc. apply pu_multi_commit_ok_iff in Hc as [_ Hin].
  destruct (pu_multi_no_forging s0 pre H0 _ Hin) as [pre1 [mid [Htr [Hck [Hf Hlive]]]]].
  simpl in *. exists pre1, mid.
  split; [exact Htr |]. split; [exact Hck |].
  split; [simpl; lia |]. split; [simpl; lia |].
  split; [unfold pu_claim in Hf; injection Hf as Hv; symmetry; exact Hv |].
  apply Hlive. reflexivity.
Qed.

Lemma pu_multi_cert_first : forall s0 tr,
  cert s0 = false -> cert (pu_run tr s0) = true ->
  exists pre post, tr = pre ++ CERTIFY :: post /\
    cert (pu_run pre s0) = false /\ pu_certify_ok (core_of (pu_run pre s0)) = true.
Proof.
  intros s0 tr H0. induction tr as [| i tr IH] using rev_ind; intro H1.
  - simpl in H1. congruence.
  - rewrite pu_multi_run_snoc in H1. destruct (cert (pu_run tr s0)) eqn:Hc.
    + destruct (IH eq_refl) as [pre [post [-> Hrest]]].
      exists pre, (post ++ [i]). rewrite <- app_assoc. auto.
    + destruct (pu_multi_only_certify_certifies _ i Hc H1) as [-> Hok].
      exists tr, []. auto.
Qed.

Lemma pu_multi_chan_origin : forall s0 tr f,
  chan (core_of s0) = None -> chan (core_of (pu_run tr s0)) = Some f ->
  exists pre1 p c mid, tr = pre1 ++ COMMIT p c :: mid /\
    pu_commit_ok (core_of (pu_run pre1 s0)) p c = true /\
    f = pu_claim (core_of (pu_run pre1 s0)) p c.
Proof.
  intros s0 tr f H0. induction tr as [| i tr IH] using rev_ind; intro H1.
  - simpl in H1. congruence.
  - rewrite pu_multi_run_snoc in H1. simpl in H1.
    destruct (pu_multi_chan_step (core_of (pu_run tr s0)) i) as [Hs | [p [c [-> [Hok Hch]]]]].
    + rewrite Hs in H1. destruct (IH H1) as [pre1 [p [c [mid [-> Hrest]]]]].
      exists pre1, p, c, (mid ++ [i]). rewrite <- app_assoc. auto.
    + rewrite Hch in H1. injection H1 as <-. exists tr, p, c, []. auto.
Qed.

(* A raised flag was earned: CHECK, then COMMIT of the same claim at the
   same version with the register untouched between, then CERTIFY. *)
Theorem pu_multi_earned_certification_provenance : forall s0 tr,
  pu_clean_start s0 -> cert (pu_run tr s0) = true ->
  exists pre1 p c mid1 mid2 post,
    tr = pre1 ++ CHECK p c :: mid1 ++ COMMIT p c :: mid2 ++ CERTIFY :: post /\
    pu_check_ok (core_of (pu_run pre1 s0)) p c = true /\
    pu_commit_ok (core_of (pu_run (pre1 ++ CHECK p c :: mid1) s0)) p c = true /\
    pu_certify_ok (core_of (pu_run (pre1 ++ CHECK p c :: mid1 ++ COMMIT p c :: mid2) s0))
      = true /\
    vers (core_of (pu_run pre1 s0)) c
      = vers (core_of (pu_run (pre1 ++ CHECK p c :: mid1) s0)) c /\
    pu_untouched (pu_run (pre1 ++ [CHECK p c]) s0) mid1 c.
Proof.
  intros s0 tr H0 H1. pose proof H0 as [_ [Hch Hc0]].
  destruct (pu_multi_cert_first s0 tr Hc0 H1) as [pre [post [-> [_ Hok]]]].
  pose proof Hok as Hset. unfold pu_certify_ok in Hset.
  apply andb_true_iff in Hset as [_ Hset].
  destruct (chan (core_of (pu_run pre s0))) as [f |] eqn:Hf; [| discriminate].
  destruct (pu_multi_chan_origin s0 pre f Hch Hf) as [preC [p [c [mid2 [-> [Hcm _]]]]]].
  destruct (pu_multi_earned_commitment_provenance s0 preC p c H0 Hcm)
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

Theorem pu_multi_certified_run_min_cost : forall s0 tr,
  pu_clean_start s0 -> cert (pu_run tr s0) = true ->
  pu_total_cost tr >= 3 /\ mu (pu_run tr s0) >= mu s0 + 3.
Proof.
  intros s0 tr H0 H1.
  assert (Hc : pu_total_cost tr >= 3).
  { destruct (pu_multi_earned_certification_provenance s0 tr H0 H1)
      as [pre1 [p [c [mid1 [mid2 [post [-> _]]]]]]].
    rewrite pu_multi_total_cost_app. simpl. rewrite pu_multi_total_cost_app. simpl.
    rewrite pu_multi_total_cost_app. simpl. lia. }
  split; [exact Hc | rewrite pu_multi_mu_conservation_trace; lia].
Qed.

Corollary pu_multi_program_certified_min_cost : forall n P vs,
  cert (pu_run_prog n P (pu_start vs)) = true -> mu (pu_run_prog n P (pu_start vs)) >= 3.
Proof.
  intros n P vs H. rewrite pu_multi_run_prog_trace in *.
  apply (pu_multi_certified_run_min_cost (pu_start vs)) in H;
    [simpl in H; lia | apply pu_multi_start_clean].
Qed.

(* ================================================================= *)
(* Single CHECK, COMMIT and CERTIFY steps.                            *)
(* ================================================================= *)

Lemma pu_multi_exec_check_pass : forall s p c,
  pu_check_ok (core_of s) p c = true ->
  pu_exec s (CHECK p c) =
  mkst (pu_record_fact (core_of s) (pu_claim (core_of s) p c)) (mu s + 1) (cert s).
Proof.
  intros [k m r] p c H. simpl in *.
  assert (He : err k = false)
    by (unfold pu_check_ok in H; destruct (err k); [discriminate | reflexivity]).
  unfold pu_exec, pu_cexec. simpl. rewrite He, H. simpl. rewrite orb_false_r. reflexivity.
Qed.

Lemma pu_multi_exec_check_fail : forall s p c,
  err (core_of s) = false -> pu_check_ok (core_of s) p c = false ->
  pu_exec s (CHECK p c) = mkst (pu_trap (core_of s)) (mu s + 1) (cert s).
Proof.
  intros [k m r] p c He H. simpl in *.
  unfold pu_exec, pu_cexec. simpl. rewrite He, H. simpl. rewrite orb_false_r. reflexivity.
Qed.

Lemma pu_multi_exec_commit_pass : forall s p c,
  pu_commit_ok (core_of s) p c = true ->
  pu_exec s (COMMIT p c) =
  mkst (pu_commit_to (core_of s) (pu_claim (core_of s) p c)) (mu s + 1) (cert s).
Proof.
  intros [k m r] p c H. simpl in *.
  assert (He : err k = false) by (apply pu_multi_commit_ok_iff in H; apply H).
  unfold pu_exec, pu_cexec. simpl. rewrite He, H. simpl. rewrite orb_false_r. reflexivity.
Qed.

Lemma pu_multi_exec_commit_fail : forall s p c,
  err (core_of s) = false -> pu_commit_ok (core_of s) p c = false ->
  pu_exec s (COMMIT p c) = mkst (pu_trap (core_of s)) (mu s + 1) (cert s).
Proof.
  intros [k m r] p c He H. simpl in *.
  unfold pu_exec, pu_cexec. simpl. rewrite He, H. simpl. rewrite orb_false_r. reflexivity.
Qed.

Lemma pu_multi_exec_certify_pass : forall s,
  pu_certify_ok (core_of s) = true ->
  pu_exec s CERTIFY = mkst (pu_goto (core_of s) (S (pc (core_of s)))) (mu s + 1) true.
Proof.
  intros [k m r] H. simpl in *.
  assert (He : err k = false)
    by (unfold pu_certify_ok in H; destruct (err k); [discriminate | reflexivity]).
  unfold pu_exec, pu_cexec. simpl. rewrite He, H, orb_true_r. reflexivity.
Qed.

Lemma pu_multi_exec_certify_fail : forall s,
  err (core_of s) = false -> pu_certify_ok (core_of s) = false ->
  pu_exec s CERTIFY = mkst (pu_trap (core_of s)) (mu s + 1) (cert s).
Proof.
  intros [k m r] He H. simpl in *.
  unfold pu_exec, pu_cexec. simpl. rewrite He, H, orb_false_r. reflexivity.
Qed.

(* PAY on a live machine: pc + 1, ledger + 1, nothing else. *)
Lemma pu_multi_exec_pay : forall s,
  err (core_of s) = false ->
  pu_exec s PAY = mkst (pu_goto (core_of s) (S (pc (core_of s)))) (mu s + 1) (cert s).
Proof.
  intros [k m r] He. simpl in *. unfold pu_exec, pu_cexec. simpl. rewrite He, orb_false_r.
  reflexivity.
Qed.

(* PAY never raises the flag. *)
Lemma pu_multi_pay_never_fires : forall k, pu_fires k PAY = false.
Proof. reflexivity. Qed.

(* PAY leaves every register, version, fact, the channel and the trap
   latch alone. *)
Lemma pu_multi_pay_keeps : forall k r,
  vals (pu_cexec k PAY) r = vals k r /\ vers (pu_cexec k PAY) r = vers k r /\
  facts (pu_cexec k PAY) = facts k /\ chan (pu_cexec k PAY) = chan k /\
  err (pu_cexec k PAY) = err k.
Proof. intros k r. unfold pu_cexec. destruct (err k) eqn:E; simpl; rewrite ?E; repeat split. Qed.

(* ================================================================= *)
(* The three-instruction chain on one property.                       *)
(* ================================================================= *)

Definition pu_chain (p : prop) (c : pu_reg) : list pu_instr := [CHECK p c; COMMIT p c; CERTIFY].

(* From a start where p holds of register c, the chain certifies and pays
   exactly the floor of 3. *)
Theorem pu_multi_chain_certifies : forall p c vs,
  holds p (vs c) ->
  cert (pu_run_prog 4 (pu_chain p c) (pu_start vs)) = true /\
  mu (pu_run_prog 4 (pu_chain p c) (pu_start vs)) = 3.
Proof.
  intros p c vs H. apply eval_iff in H.
  assert (Hck : pu_check_ok (pu_start_core vs) p c = true)
    by (unfold pu_check_ok; simpl; rewrite H; reflexivity).
  set (P := pu_chain p c).
  change (pu_run_prog 4 P (pu_start vs)) with (pu_step P (pu_step P (pu_step P (pu_step P (pu_start vs))))).
  assert (E1 : pu_step P (pu_start vs) = pu_exec (pu_start vs) (CHECK p c)) by reflexivity.
  rewrite E1, (pu_multi_exec_check_pass (pu_start vs) p c Hck).
  change (core_of (pu_start vs)) with (pu_start_core vs).
  set (k1 := pu_record_fact (pu_start_core vs) (pu_claim (pu_start_core vs) p c)).
  assert (Hcm : pu_commit_ok k1 p c = true).
  { apply pu_multi_commit_ok_iff. split; [reflexivity |]. left. reflexivity. }
  set (s1 := mkst k1 (mu (pu_start vs) + 1) (cert (pu_start vs))).
  assert (E2 : pu_step P s1 = pu_exec s1 (COMMIT p c)) by reflexivity.
  rewrite E2, (pu_multi_exec_commit_pass s1 p c Hcm).
  split; reflexivity.
Qed.

(* From a start where p fails on register c, the CHECK traps, and no number
   of further steps raises the flag. *)
Theorem pu_multi_chain_refused_forever : forall n p c vs,
  ~ holds p (vs c) ->
  cert (pu_run_prog n (pu_chain p c) (pu_start vs)) = false /\
  (n >= 1 -> err (core_of (pu_run_prog n (pu_chain p c) (pu_start vs))) = true).
Proof.
  intros n p c vs H.
  assert (He : eval p (vs c) = false)
    by (destruct (eval p _) eqn:E; [exfalso; apply H, eval_iff, E | reflexivity]).
  assert (Hck : pu_check_ok (pu_start_core vs) p c = false)
    by (unfold pu_check_ok; simpl; rewrite He; reflexivity).
  destruct n as [| n]; [split; [reflexivity | lia] |].
  set (P := pu_chain p c).
  change (pu_run_prog (S n) P (pu_start vs)) with (pu_run_prog n P (pu_step P (pu_start vs))).
  assert (E1 : pu_step P (pu_start vs) = pu_exec (pu_start vs) (CHECK p c)) by reflexivity.
  rewrite E1, (pu_multi_exec_check_fail (pu_start vs) p c eq_refl Hck).
  rewrite pu_multi_run_prog_trapped by reflexivity.
  split; [reflexivity | intros _; reflexivity].
Qed.

(* So the chain certifies exactly when p holds of the start value. *)
Corollary pu_multi_chain_certifies_iff : forall p c vs,
  cert (pu_run_prog 4 (pu_chain p c) (pu_start vs)) = true <-> holds p (vs c).
Proof.
  intros p c vs. split.
  - intro H1. apply eval_iff.
    destruct (eval p (vs c)) eqn:E; [reflexivity | exfalso].
    assert (Hn : ~ holds p (vs c))
      by (intro Hh; apply eval_iff in Hh; congruence).
    destruct (pu_multi_chain_refused_forever 4 p c vs Hn) as [H2 _]. congruence.
  - intro H. apply pu_multi_chain_certifies, H.
Qed.

End Multi.

(* ================================================================= *)
(* Assumption audit. Every line must print                            *)
(* "Closed under the global context".                                 *)
(* ================================================================= *)

Print Assumptions pu_multi_fact_eqb_eq.
Print Assumptions pu_multi_run_prog_trace.
Print Assumptions pu_multi_run_prog_add.
Print Assumptions pu_multi_trapped_halted.
Print Assumptions pu_multi_step_trapped.
Print Assumptions pu_multi_run_prog_trapped.
Print Assumptions pu_multi_err_permanent.
Print Assumptions pu_multi_mu_conservation_trace.
Print Assumptions pu_multi_mu_conservation_program.
Print Assumptions pu_multi_cert_latch.
Print Assumptions pu_multi_cert_permanent.
Print Assumptions pu_multi_only_certify_certifies.
Print Assumptions pu_multi_a2.
Print Assumptions pu_multi_nfi_floor.
Print Assumptions pu_multi_facts_step.
Print Assumptions pu_multi_facts_keep.
Print Assumptions pu_multi_full_table_traps.
Print Assumptions pu_multi_facts_bounded_step.
Print Assumptions pu_multi_unearned_commit_traps.
Print Assumptions pu_multi_uncommitted_certify_traps.
Print Assumptions pu_multi_frame_cexec.
Print Assumptions pu_multi_plain_step.
Print Assumptions pu_multi_frame_step.
Print Assumptions pu_multi_frame_run.
Print Assumptions pu_multi_plain_run.
Print Assumptions pu_multi_checker_soundness.
Print Assumptions pu_multi_committed_claim_holds.
Print Assumptions pu_multi_no_forging_step.
Print Assumptions pu_multi_no_forging.
Print Assumptions pu_multi_earned_commitment_provenance.
Print Assumptions pu_multi_earned_certification_provenance.
Print Assumptions pu_multi_certified_run_min_cost.
Print Assumptions pu_multi_program_certified_min_cost.
Print Assumptions pu_multi_exec_certify_pass.
Print Assumptions pu_multi_exec_pay.
Print Assumptions pu_multi_pay_never_fires.
Print Assumptions pu_multi_pay_keeps.
Print Assumptions pu_multi_chain_certifies.
Print Assumptions pu_multi_chain_refused_forever.
Print Assumptions pu_multi_chain_certifies_iff.
