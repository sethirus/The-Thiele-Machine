(** EarnedPriced.v: the machine of EarnedGeneric.v with one more
    instruction, PAY.

    The machine is the one in EarnedGeneric.v, with its property language
    left open in the same way (prop_eqb, eval, holds, eval_iff), the same
    state, core, versions, fact table, commitment channel, trap latch,
    certified flag and fact cap. The instructions are INC, DEC, HALT, CHECK,
    COMMIT and CERTIFY, acting exactly as there, plus

      PAY   costs 1 and moves the program counter on by one. It writes no
            counter, bumps no version, records no fact, names no
            commitment, never traps and never raises the flag.

    PAY is a way to put a price on the ledger without doing anything else.
    On a trapped machine it changes nothing but the ledger, like every
    other instruction.

    What is proved (every result closed under the global context):

      1. PAY is neutral: it changes only the program counter and the ledger
         [pr_pay_neutral, pr_pay_exec].
      2. A program without PAY runs exactly as in EarnedGeneric.v, state for
         state, with the same trace and the same halting
         [priced_extends_generic, pr_pay_free_is_generic].
      3. Every theorem of EarnedGeneric.v holds with PAY present: the toll
         and the latch [pr_mu_conservation_trace, pr_cert_latch,
         pr_cert_permanent, pr_only_certify_certifies, pr_nfi_floor], trapped
         machines are inert [pr_trapped_inert, pr_run_prog_trapped], checker
         soundness [pr_checker_soundness, pr_committed_claim_holds], no
         forging [pr_no_forging], commitment and certification provenance
         [pr_earned_commitment_provenance,
         pr_earned_certification_provenance], the price floor of 3
         [pr_certified_run_min_cost, pr_program_certified_min_cost] and the
         three-instruction chain [pr_chain_certifies,
         pr_chain_refused_forever, pr_chain_certifies_iff].
      4. The fact table counts the passing checks: its length is the number
         of CHECK instructions in the trace that passed [pr_facts_count].
      5. The two instances of EarnedGeneric.v, the counter language and the
         sorted-list language, with their provenance, soundness, price and
         demonstration results [pr_core_*, pr_sorted_*].

    Dependencies: Coq standard library and EarnedGeneric.v.
    No axioms, no Admitted.                                                 *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose, as in
   EarnedGeneric.v: this file imports nothing outside the standard library
   and EarnedGeneric.v, so it re-checks from a clean checkout. *)

From Coq Require Import List Arith Lia Bool.
From Coq Require Import Sorting.Sorted.
Import ListNotations.
Require Minimal.EarnedGeneric.
Module G := Minimal.EarnedGeneric.

Section Priced.

(* ================================================================= *)
(* The open property language, as in EarnedGeneric.v.                 *)
(* ================================================================= *)

Context {prop : Type}.
Variable prop_eqb : prop -> prop -> bool.
Hypothesis prop_eqb_eq : forall p q, prop_eqb p q = true <-> p = q.
Variable eval : prop -> nat -> bool.
Variable holds : prop -> nat -> Prop.
Hypothesis eval_iff : forall p v, eval p v = true <-> holds p v.

Local Notation ctr := G.ctr.
Local Notation core := (@G.core prop).
Local Notation fact := (@G.fact prop).
Local Notation state := (@G.state prop).
Local Notation check_ok := (G.check_ok eval).
Local Notation commit_ok := (G.commit_ok prop_eqb).
Local Notation start := (@G.start prop).
Local Notation start_core := (@G.start_core prop).

(* ================================================================= *)
(* The machine.                                                       *)
(* ================================================================= *)

Inductive pr_instr : Type :=
| INC (c : ctr)
| DEC (c : ctr) (j : nat)
| HALT
| CHECK (p : prop) (c : ctr)
| COMMIT (p : prop) (c : ctr)
| CERTIFY
| PAY.

Definition pr_cost (i : pr_instr) : nat :=
  match i with
  | CHECK _ _ | COMMIT _ _ | CERTIFY | PAY => 1
  | _ => 0
  end.

Definition pr_cexec (k : core) (i : pr_instr) : core :=
  if G.err k then k else
  match i with
  | INC c => G.write k c (S (G.val k c)) (S (G.pc k))
  | DEC c j =>
      match G.val k c with
      | 0 => G.goto k (S (G.pc k))
      | S n => G.write k c n j
      end
  | HALT => k
  | CHECK p c => if check_ok k p c then G.record_fact k (G.claim k p c) else G.trap k
  | COMMIT p c => if commit_ok k p c then G.commit_to k (G.claim k p c) else G.trap k
  | CERTIFY => if G.certify_ok k then G.goto k (S (G.pc k)) else G.trap k
  | PAY => G.goto k (S (G.pc k))
  end.

Definition pr_fires (k : core) (i : pr_instr) : bool :=
  match i with CERTIFY => G.certify_ok k | _ => false end.

Definition pr_exec (s : state) (i : pr_instr) : state :=
  G.mkst (pr_cexec (G.core_of s) i) (G.mu s + pr_cost i)
         (G.cert s || pr_fires (G.core_of s) i).

Fixpoint pr_run (tr : list pr_instr) (s : state) : state :=
  match tr with [] => s | i :: rest => pr_run rest (pr_exec s i) end.

Fixpoint pr_total_cost (tr : list pr_instr) : nat :=
  match tr with [] => 0 | i :: rest => pr_cost i + pr_total_cost rest end.

Definition pr_next_instr (P : list pr_instr) (k : core) : option pr_instr :=
  if G.err k then None else
  match G.fetch P (G.pc k) with Some HALT => None | o => o end.

Definition pr_halted (P : list pr_instr) (k : core) : Prop := pr_next_instr P k = None.

Definition pr_step (P : list pr_instr) (s : state) : state :=
  match pr_next_instr P (G.core_of s) with None => s | Some i => pr_exec s i end.

Fixpoint pr_run_prog (n : nat) (P : list pr_instr) (s : state) : state :=
  match n with 0 => s | S m => pr_run_prog m P (pr_step P s) end.

Fixpoint pr_trace_of (n : nat) (P : list pr_instr) (s : state) : list pr_instr :=
  match n with
  | 0 => []
  | S m => match pr_next_instr P (G.core_of s) with
           | None => []
           | Some i => i :: pr_trace_of m P (pr_exec s i)
           end
  end.

Lemma pr_run_app : forall l1 l2 s, pr_run (l1 ++ l2) s = pr_run l2 (pr_run l1 s).
Proof. induction l1; intros; simpl; auto. Qed.

Lemma pr_run_snoc : forall l i s, pr_run (l ++ [i]) s = pr_exec (pr_run l s) i.
Proof. intros. rewrite pr_run_app. reflexivity. Qed.

Lemma pr_total_cost_app : forall l1 l2,
  pr_total_cost (l1 ++ l2) = pr_total_cost l1 + pr_total_cost l2.
Proof. induction l1; intros; simpl; [| rewrite IHl1]; lia. Qed.

Lemma pr_base_blind : forall s i, G.core_of (pr_exec s i) = pr_cexec (G.core_of s) i.
Proof. reflexivity. Qed.

Lemma pr_run_prog_halted : forall n P s,
  pr_halted P (G.core_of s) -> pr_run_prog n P s = s.
Proof.
  induction n; intros P s H; simpl; [reflexivity |].
  unfold pr_step. unfold pr_halted in H. rewrite H. apply IHn. exact H.
Qed.

Lemma pr_run_prog_trace : forall n P s, pr_run_prog n P s = pr_run (pr_trace_of n P s) s.
Proof.
  induction n; intros P s; simpl; [reflexivity |].
  unfold pr_step. destruct (pr_next_instr P (G.core_of s)) eqn:H.
  - apply IHn.
  - apply pr_run_prog_halted. exact H.
Qed.

(* A trapped core is left as it is by every instruction. *)
Theorem pr_trapped_inert : forall k i, G.err k = true -> pr_cexec k i = k.
Proof. intros k i H. unfold pr_cexec. rewrite H. reflexivity. Qed.

(* A trapped machine takes no further step. *)
Theorem pr_run_prog_trapped : forall n P s,
  G.err (G.core_of s) = true -> pr_run_prog n P s = s.
Proof.
  induction n as [| n IH]; intros P s H; simpl; [reflexivity |].
  unfold pr_step, pr_next_instr. rewrite H. apply IH. exact H.
Qed.

(* ================================================================= *)
(* PAY is neutral.                                                    *)
(* ================================================================= *)

(* PAY changes only the program counter (on a live machine) and the
   ledger, which grows by 1. *)
Theorem pr_pay_neutral : forall s,
  let s' := pr_exec s PAY in
  G.ca (G.core_of s') = G.ca (G.core_of s) /\
  G.cb (G.core_of s') = G.cb (G.core_of s) /\
  G.va (G.core_of s') = G.va (G.core_of s) /\
  G.vb (G.core_of s') = G.vb (G.core_of s) /\
  G.facts (G.core_of s') = G.facts (G.core_of s) /\
  G.chan (G.core_of s') = G.chan (G.core_of s) /\
  G.err (G.core_of s') = G.err (G.core_of s) /\
  G.cert s' = G.cert s /\
  G.mu s' = G.mu s + 1 /\
  G.pc (G.core_of s') =
    (if G.err (G.core_of s) then G.pc (G.core_of s) else S (G.pc (G.core_of s))).
Proof.
  intros [k m r] s'. unfold s', pr_exec, pr_cexec. simpl. rewrite orb_false_r.
  destruct (G.err k) eqn:He; simpl; rewrite ?He; repeat split.
Qed.

Theorem pr_pay_exec : forall s, G.err (G.core_of s) = false ->
  pr_exec s PAY =
  G.mkst (G.goto (G.core_of s) (S (G.pc (G.core_of s)))) (G.mu s + 1) (G.cert s).
Proof.
  intros [k m r] He. simpl in *. unfold pr_exec, pr_cexec. simpl.
  rewrite He, orb_false_r. reflexivity.
Qed.

Theorem pr_pay_never_fires : forall k, pr_fires k PAY = false.
Proof. reflexivity. Qed.

(* ================================================================= *)
(* Without PAY, the machine of EarnedGeneric.v.                       *)
(* ================================================================= *)

Definition pr_embed (i : @G.instr prop) : pr_instr :=
  match i with
  | G.INC c => INC c
  | G.DEC c j => DEC c j
  | G.HALT => HALT
  | G.CHECK p c => CHECK p c
  | G.COMMIT p c => COMMIT p c
  | G.CERTIFY => CERTIFY
  end.

Lemma pr_cexec_embed : forall k i,
  pr_cexec k (pr_embed i) = G.cexec prop_eqb eval k i.
Proof. intros k i. destruct i; reflexivity. Qed.

Lemma pr_exec_embed : forall s i,
  pr_exec s (pr_embed i) = G.exec prop_eqb eval s i.
Proof. intros s i. destruct i; reflexivity. Qed.

Lemma pr_cost_embed : forall i, pr_cost (pr_embed i) = G.cost i.
Proof. intro i. destruct i; reflexivity. Qed.

Lemma pr_run_embed : forall tr s,
  pr_run (map pr_embed tr) s = G.run prop_eqb eval tr s.
Proof.
  induction tr as [| i tr IH]; intro s; simpl; [reflexivity |].
  rewrite pr_exec_embed. apply IH.
Qed.

Lemma pr_fetch_map : forall (A B : Type) (f : A -> B) (l : list A) n,
  G.fetch (map f l) n = option_map f (G.fetch l n).
Proof. intros A B f l [| n]; simpl; [reflexivity | apply nth_error_map]. Qed.

Lemma pr_next_instr_embed : forall P k,
  pr_next_instr (map pr_embed P) k = option_map pr_embed (G.next_instr P k).
Proof.
  intros P k. unfold pr_next_instr, G.next_instr. destruct (G.err k); [reflexivity |].
  rewrite pr_fetch_map. destruct (G.fetch P (G.pc k)) as [[] |]; reflexivity.
Qed.

(* A program without PAY runs exactly as the same program does in
   EarnedGeneric.v: the same state after every number of steps, the same
   trace, and the same halting. *)
Theorem priced_extends_generic : forall n P s,
  pr_run_prog n (map pr_embed P) s = G.run_prog prop_eqb eval n P s /\
  pr_trace_of n (map pr_embed P) s = map pr_embed (G.trace_of prop_eqb eval n P s) /\
  (pr_halted (map pr_embed P) (G.core_of s) <-> G.halted P (G.core_of s)).
Proof.
  induction n as [| n IH]; intros P s.
  - split; [reflexivity |]. split; [reflexivity |].
    unfold pr_halted, G.halted. rewrite pr_next_instr_embed.
    destruct (G.next_instr P (G.core_of s)); simpl; split; congruence.
  - split; [| split].
    + simpl. unfold pr_step, G.step. rewrite pr_next_instr_embed.
      destruct (G.next_instr P (G.core_of s)) as [i |]; simpl.
      * rewrite pr_exec_embed. exact (proj1 (IH P _)).
      * exact (proj1 (IH P _)).
    + simpl. rewrite pr_next_instr_embed.
      destruct (G.next_instr P (G.core_of s)) as [i |]; simpl; [| reflexivity].
      rewrite pr_exec_embed. f_equal. exact (proj1 (proj2 (IH P _))).
    + unfold pr_halted, G.halted. rewrite pr_next_instr_embed.
      destruct (G.next_instr P (G.core_of s)); simpl; split; congruence.
Qed.

(* A program is free of PAY exactly when it is the image of a program of
   EarnedGeneric.v. *)
Theorem pr_pay_free_is_generic : forall P : list pr_instr,
  ~ In PAY P -> exists Q, P = map pr_embed Q.
Proof.
  induction P as [| i P IH]; intro H; [exists []; reflexivity |].
  destruct IH as [Q HQ]; [intro Hin; apply H; right; exact Hin |].
  destruct i as [c | c j | | p c | p c | |].
  - exists (G.INC c :: Q). simpl. rewrite HQ. reflexivity.
  - exists (G.DEC c j :: Q). simpl. rewrite HQ. reflexivity.
  - exists (G.HALT :: Q). simpl. rewrite HQ. reflexivity.
  - exists (G.CHECK p c :: Q). simpl. rewrite HQ. reflexivity.
  - exists (G.COMMIT p c :: Q). simpl. rewrite HQ. reflexivity.
  - exists (G.CERTIFY :: Q). simpl. rewrite HQ. reflexivity.
  - exfalso. apply H. left. reflexivity.
Qed.

(* ================================================================= *)
(* The toll, the ledger, the latch.                                   *)
(* ================================================================= *)

Theorem pr_mu_conservation : forall s i, G.mu (pr_exec s i) = G.mu s + pr_cost i.
Proof. reflexivity. Qed.

Theorem pr_mu_conservation_trace : forall tr s,
  G.mu (pr_run tr s) = G.mu s + pr_total_cost tr.
Proof. induction tr; intros; simpl; [lia | rewrite IHtr; simpl; lia]. Qed.

Theorem pr_mu_conservation_program : forall n P s,
  G.mu (pr_run_prog n P s) = G.mu s + pr_total_cost (pr_trace_of n P s).
Proof. intros. rewrite pr_run_prog_trace. apply pr_mu_conservation_trace. Qed.

Theorem pr_cert_latch : forall s i,
  G.cert (pr_exec s i) = G.cert s || pr_fires (G.core_of s) i.
Proof. reflexivity. Qed.

Theorem pr_cert_permanent : forall s i, G.cert s = true -> G.cert (pr_exec s i) = true.
Proof. intros s i H. simpl. rewrite H. reflexivity. Qed.

Theorem pr_only_certify_certifies : forall s i,
  G.cert s = false -> G.cert (pr_exec s i) = true ->
  i = CERTIFY /\ G.certify_ok (G.core_of s) = true.
Proof.
  intros s i H0 H1. simpl in H1. rewrite H0 in H1. simpl in H1.
  destruct i; simpl in H1; try discriminate. auto.
Qed.

Theorem pr_a2 : forall s i,
  G.cert s = false -> G.cert (pr_exec s i) = true -> pr_cost i >= 1.
Proof.
  intros s i H0 H1. destruct (pr_only_certify_certifies s i H0 H1) as [-> _].
  simpl. lia.
Qed.

Theorem pr_nfi_floor : forall tr s,
  G.cert s = false -> G.cert (pr_run tr s) = true -> pr_total_cost tr >= 1.
Proof.
  induction tr as [| i rest IH]; intros s H0 H1; simpl in *; [congruence |].
  destruct (G.cert (pr_exec s i)) eqn:Hm.
  - pose proof (pr_a2 s i H0 Hm). lia.
  - pose proof (IH _ Hm H1). lia.
Qed.

(* ================================================================= *)
(* Per-instruction facts about the substrate.                         *)
(* ================================================================= *)

Lemma pr_ver_mono : forall k i c, G.ver k c <= G.ver (pr_cexec k i) c.
Proof.
  intros k i c. unfold pr_cexec. destruct (G.err k); [lia |].
  destruct i as [d | d j | | p d | p d | |]; simpl.
  - rewrite G.generic_ver_write. destruct (G.ctr_eqb d c); lia.
  - destruct (G.val k d); [destruct c; simpl; lia |].
    rewrite G.generic_ver_write. destruct (G.ctr_eqb d c); lia.
  - lia.
  - destruct (check_ok k p d); destruct c; simpl; lia.
  - destruct (commit_ok k p d); destruct c; simpl; lia.
  - destruct (G.certify_ok k); destruct c; simpl; lia.
  - destruct c; simpl; lia.
Qed.

Lemma pr_ver_same_val : forall k i c,
  G.ver (pr_cexec k i) c = G.ver k c -> G.val (pr_cexec k i) c = G.val k c.
Proof.
  intros k i c H. unfold pr_cexec in *. destruct (G.err k); [reflexivity |].
  destruct i as [d | d j | | p d | p d | |]; simpl in *.
  - rewrite G.generic_ver_write in H. rewrite G.generic_val_write.
    destruct (G.ctr_eqb d c); [lia | reflexivity].
  - destruct (G.val k d); [destruct c; reflexivity |].
    rewrite G.generic_ver_write in H. rewrite G.generic_val_write.
    destruct (G.ctr_eqb d c); [lia | reflexivity].
  - reflexivity.
  - destruct (check_ok k p d); destruct c; reflexivity.
  - destruct (commit_ok k p d); destruct c; reflexivity.
  - destruct (G.certify_ok k); destruct c; reflexivity.
  - destruct c; reflexivity.
Qed.

Lemma pr_ver_check : forall k p c d, G.ver (pr_cexec k (CHECK p c)) d = G.ver k d.
Proof.
  intros. unfold pr_cexec. destruct (G.err k); [reflexivity |].
  destruct (check_ok k p c); destruct d; reflexivity.
Qed.

Lemma pr_val_check : forall k p c d, G.val (pr_cexec k (CHECK p c)) d = G.val k d.
Proof.
  intros. unfold pr_cexec. destruct (G.err k); [reflexivity |].
  destruct (check_ok k p c); destruct d; reflexivity.
Qed.

Theorem pr_facts_step : forall k i f,
  In f (G.facts (pr_cexec k i)) ->
  In f (G.facts k) \/
  (i = CHECK (G.f_prop f) (G.f_ctr f) /\ check_ok k (G.f_prop f) (G.f_ctr f) = true /\
   f = G.claim k (G.f_prop f) (G.f_ctr f)).
Proof.
  intros k i f H. unfold pr_cexec in H. destruct (G.err k) eqn:He; [auto |].
  destruct i as [d | d j | | p d | p d | |]; simpl in H.
  - rewrite G.generic_facts_write in H. auto.
  - destruct (G.val k d); simpl in H; [auto | rewrite G.generic_facts_write in H; auto].
  - auto.
  - destruct (check_ok k p d) eqn:Hc; simpl in H; [| auto].
    destruct H as [<- | H]; [right | auto]. simpl. auto.
  - destruct (commit_ok k p d); simpl in H; auto.
  - destruct (G.certify_ok k); simpl in H; auto.
  - auto.
Qed.

Theorem pr_facts_keep : forall k i f,
  In f (G.facts k) -> In f (G.facts (pr_cexec k i)).
Proof.
  intros k i f H. unfold pr_cexec. destruct (G.err k); [exact H |].
  destruct i as [d | d j | | p d | p d | |]; simpl.
  - rewrite G.generic_facts_write. exact H.
  - destruct (G.val k d); simpl; [exact H | rewrite G.generic_facts_write; exact H].
  - exact H.
  - destruct (check_ok k p d); simpl; auto.
  - destruct (commit_ok k p d); simpl; auto.
  - destruct (G.certify_ok k); simpl; auto.
  - exact H.
Qed.

Theorem pr_full_table_traps : forall k p c,
  G.fact_cap <= length (G.facts k) ->
  G.err (pr_cexec k (CHECK p c)) = true /\ G.facts (pr_cexec k (CHECK p c)) = G.facts k.
Proof.
  intros k p c H. unfold pr_cexec. destruct (G.err k) eqn:He; [auto |].
  unfold G.check_ok. rewrite He.
  replace (Nat.ltb (length (G.facts k)) G.fact_cap) with false
    by (symmetry; apply Nat.ltb_ge; exact H).
  rewrite andb_false_r. auto.
Qed.

Theorem pr_facts_bounded_step : forall k i,
  length (G.facts k) <= G.fact_cap -> length (G.facts (pr_cexec k i)) <= G.fact_cap.
Proof.
  intros k i H. unfold pr_cexec. destruct (G.err k); [exact H |].
  destruct i as [d | d j | | p d | p d | |]; simpl.
  - rewrite G.generic_facts_write. exact H.
  - destruct (G.val k d); simpl; [exact H | rewrite G.generic_facts_write; exact H].
  - exact H.
  - destruct (check_ok k p d) eqn:Hc; simpl; [| exact H].
    unfold G.check_ok in Hc. apply andb_true_iff in Hc as [_ Hc].
    apply Nat.ltb_lt in Hc. lia.
  - destruct (commit_ok k p d); simpl; exact H.
  - destruct (G.certify_ok k); simpl; exact H.
  - exact H.
Qed.

Lemma pr_chan_step : forall k i,
  G.chan (pr_cexec k i) = G.chan k \/
  exists p c, i = COMMIT p c /\ commit_ok k p c = true /\
              G.chan (pr_cexec k i) = Some (G.claim k p c).
Proof.
  intros k i. unfold pr_cexec. destruct (G.err k); [auto |].
  destruct i as [d | d j | | p d | p d | |]; simpl.
  - rewrite G.generic_chan_write. auto.
  - destruct (G.val k d); simpl; [auto | rewrite G.generic_chan_write; auto].
  - auto.
  - destruct (check_ok k p d); simpl; auto.
  - destruct (commit_ok k p d) eqn:Hc; simpl; [right; eauto | auto].
  - destruct (G.certify_ok k); simpl; auto.
  - auto.
Qed.

Theorem pr_unearned_commit_traps : forall k p c,
  commit_ok k p c = false ->
  G.err (pr_cexec k (COMMIT p c)) = true /\
  G.chan (pr_cexec k (COMMIT p c)) = G.chan k /\
  G.facts (pr_cexec k (COMMIT p c)) = G.facts k.
Proof.
  intros k p c H. unfold pr_cexec. destruct (G.err k) eqn:He; [auto |].
  rewrite H. auto.
Qed.

Theorem pr_uncommitted_certify_traps : forall s,
  G.certify_ok (G.core_of s) = false ->
  G.err (G.core_of (pr_exec s CERTIFY)) = true /\ G.cert (pr_exec s CERTIFY) = G.cert s.
Proof.
  intros [k m r] H. simpl in *. rewrite H, orb_false_r. unfold pr_cexec.
  destruct (G.err k) eqn:He; [auto |]. rewrite H. auto.
Qed.

(* ================================================================= *)
(* The fact table counts the passing checks.                          *)
(* ================================================================= *)

(* 1 when the instruction is a CHECK that passes on this core, else 0. *)
Definition pr_passes (k : core) (i : pr_instr) : nat :=
  match i with CHECK p c => if check_ok k p c then 1 else 0 | _ => 0 end.

(* The number of passing CHECKs along a trace. *)
Fixpoint pr_passing_checks (tr : list pr_instr) (s : state) : nat :=
  match tr with
  | [] => 0
  | i :: rest => pr_passes (G.core_of s) i + pr_passing_checks rest (pr_exec s i)
  end.

Lemma pr_facts_length_step : forall k i,
  length (G.facts (pr_cexec k i)) = length (G.facts k) + pr_passes k i.
Proof.
  intros k i. unfold pr_cexec, pr_passes. destruct (G.err k) eqn:He.
  - destruct i; try lia. unfold G.check_ok. rewrite He. simpl. lia.
  - destruct i as [d | d j | | p d | p d | |]; simpl.
    + rewrite G.generic_facts_write. lia.
    + destruct (G.val k d); simpl; [lia | rewrite G.generic_facts_write; lia].
    + lia.
    + destruct (check_ok k p d); simpl; lia.
    + destruct (commit_ok k p d); simpl; lia.
    + destruct (G.certify_ok k); simpl; lia.
    + lia.
Qed.

Theorem pr_facts_count : forall tr s,
  length (G.facts (G.core_of (pr_run tr s))) =
  length (G.facts (G.core_of s)) + pr_passing_checks tr s.
Proof.
  induction tr as [| i tr IH]; intro s; simpl; [lia |].
  rewrite IH. simpl. rewrite pr_facts_length_step. lia.
Qed.

(* From a clean start, the fact table has exactly one entry per passing
   CHECK. *)
Corollary pr_facts_count_clean : forall tr s,
  G.clean_start s ->
  length (G.facts (G.core_of (pr_run tr s))) = pr_passing_checks tr s.
Proof.
  intros tr s [Hf _]. rewrite pr_facts_count, Hf. reflexivity.
Qed.

Corollary pr_facts_count_program : forall n P s,
  length (G.facts (G.core_of (pr_run_prog n P s))) =
  length (G.facts (G.core_of s)) + pr_passing_checks (pr_trace_of n P s) s.
Proof. intros. rewrite pr_run_prog_trace. apply pr_facts_count. Qed.

(* ================================================================= *)
(* Runs: versions only grow, equal version means equal value.         *)
(* ================================================================= *)

Lemma pr_ver_mono_run : forall l s c,
  G.ver (G.core_of s) c <= G.ver (G.core_of (pr_run l s)) c.
Proof.
  induction l as [| i l IH]; intros s c; simpl; [lia |].
  pose proof (pr_ver_mono (G.core_of s) i c). pose proof (IH (pr_exec s i) c).
  simpl in *. lia.
Qed.

Definition pr_untouched (s : state) (mid : list pr_instr) (c : ctr) : Prop :=
  forall t1 i t2, mid = t1 ++ i :: t2 ->
    let k := G.core_of (pr_run t1 s) in
    G.ver (pr_cexec k i) c = G.ver k c /\ G.val (pr_cexec k i) c = G.val k c.

Lemma pr_untouched_of_ver : forall s mid c,
  G.ver (G.core_of (pr_run mid s)) c = G.ver (G.core_of s) c -> pr_untouched s mid c.
Proof.
  intros s mid c H t1 i t2 ->. simpl.
  rewrite pr_run_app in H. simpl in H.
  pose proof (pr_ver_mono_run t1 s c).
  pose proof (pr_ver_mono (G.core_of (pr_run t1 s)) i c).
  pose proof (pr_ver_mono_run t2 (pr_exec (pr_run t1 s) i) c). simpl in *.
  assert (Hv : G.ver (pr_cexec (G.core_of (pr_run t1 s)) i) c
               = G.ver (G.core_of (pr_run t1 s)) c) by lia.
  split; [exact Hv | apply pr_ver_same_val; exact Hv].
Qed.

(* An untouched stretch leaves the counter's version and value as they
   were, at every point inside it. *)
Lemma pr_untouched_prefix : forall s mid c, pr_untouched s mid c ->
  forall t1 t2, mid = t1 ++ t2 ->
  G.ver (G.core_of (pr_run t1 s)) c = G.ver (G.core_of s) c /\
  G.val (G.core_of (pr_run t1 s)) c = G.val (G.core_of s) c.
Proof.
  intros s mid c Hu t1. induction t1 as [| i t1 IH] using rev_ind; intros t2 Hmid;
    [simpl; auto |].
  destruct (IH (i :: t2)) as [Hv Hw]; [rewrite Hmid, <- app_assoc; reflexivity |].
  destruct (Hu t1 i t2) as [Hv' Hw']; [rewrite Hmid, <- app_assoc; reflexivity |].
  rewrite pr_run_snoc, pr_base_blind. rewrite Hv', Hw'. auto.
Qed.

(* ================================================================= *)
(* Checker soundness.                                                 *)
(* ================================================================= *)

Lemma pr_sound_step : forall k i, G.sound holds k -> G.sound holds (pr_cexec k i).
Proof.
  intros k i Hs f Hin.
  pose proof (pr_ver_mono k i (G.f_ctr f)) as Hm.
  destruct (pr_facts_step k i f Hin) as [Hold | [Hi [Hc Hf]]].
  - destruct (Hs f Hold) as [Hle Hlive]. split; [lia |].
    intro Heq. assert (Hv : G.ver (pr_cexec k i) (G.f_ctr f) = G.ver k (G.f_ctr f)) by lia.
    rewrite (pr_ver_same_val k i _ Hv). apply Hlive. lia.
  - subst i. rewrite pr_ver_check, pr_val_check.
    rewrite Hf. simpl. split; [lia | intros _].
    unfold G.check_ok in Hc. apply andb_true_iff in Hc as [Hc _].
    apply andb_true_iff in Hc as [_ Hc]. apply eval_iff. exact Hc.
Qed.

Lemma pr_sound_run : forall tr s,
  G.sound holds (G.core_of s) -> G.sound holds (G.core_of (pr_run tr s)).
Proof. induction tr; intros s H; simpl; [exact H | apply IHtr, pr_sound_step, H]. Qed.

Theorem pr_checker_soundness : forall s0 tr f,
  G.clean_start s0 ->
  let k := G.core_of (pr_run tr s0) in
  In f (G.facts k) -> G.f_ver f = G.ver k (G.f_ctr f) ->
  holds (G.f_prop f) (G.val k (G.f_ctr f)).
Proof.
  intros s0 tr f [Hf _] k Hin Hv.
  assert (Hs0 : G.sound holds (G.core_of s0))
    by (intros g Hg; rewrite Hf in Hg; destruct Hg).
  exact (proj2 (pr_sound_run tr s0 Hs0 f Hin) Hv).
Qed.

Corollary pr_committed_claim_holds : forall s0 tr p c,
  G.clean_start s0 ->
  commit_ok (G.core_of (pr_run tr s0)) p c = true ->
  holds p (G.val (G.core_of (pr_run tr s0)) c).
Proof.
  intros s0 tr p c H0 Hc.
  apply (G.generic_commit_ok_iff prop_eqb prop_eqb_eq) in Hc as [_ Hin].
  exact (pr_checker_soundness s0 tr _ H0 Hin eq_refl).
Qed.

(* ================================================================= *)
(* No forging, over any run.                                          *)
(* ================================================================= *)

Definition pr_earned (s0 : state) (tr : list pr_instr) (f : fact) : Prop :=
  exists pre mid,
    tr = pre ++ CHECK (G.f_prop f) (G.f_ctr f) :: mid /\
    check_ok (G.core_of (pr_run pre s0)) (G.f_prop f) (G.f_ctr f) = true /\
    f = G.claim (G.core_of (pr_run pre s0)) (G.f_prop f) (G.f_ctr f) /\
    (G.f_ver f = G.ver (G.core_of (pr_run tr s0)) (G.f_ctr f) ->
     pr_untouched (pr_run (pre ++ [CHECK (G.f_prop f) (G.f_ctr f)]) s0) mid (G.f_ctr f)).

Definition pr_no_forgery (s0 : state) (tr : list pr_instr) : Prop :=
  forall f, In f (G.facts (G.core_of (pr_run tr s0))) -> pr_earned s0 tr f.

Lemma pr_earned_intro : forall s0 pre mid f,
  check_ok (G.core_of (pr_run pre s0)) (G.f_prop f) (G.f_ctr f) = true ->
  f = G.claim (G.core_of (pr_run pre s0)) (G.f_prop f) (G.f_ctr f) ->
  pr_earned s0 (pre ++ CHECK (G.f_prop f) (G.f_ctr f) :: mid) f.
Proof.
  intros s0 pre mid f Hc Hf. exists pre, mid.
  split; [reflexivity |]. split; [exact Hc |]. split; [exact Hf |].
  intro Hlive. apply pr_untouched_of_ver.
  replace (pre ++ CHECK (G.f_prop f) (G.f_ctr f) :: mid)
    with ((pre ++ [CHECK (G.f_prop f) (G.f_ctr f)]) ++ mid) in Hlive
    by (rewrite <- app_assoc; reflexivity).
  rewrite pr_run_app in Hlive. rewrite <- Hlive.
  rewrite pr_run_snoc. simpl. rewrite pr_ver_check.
  rewrite Hf at 1. reflexivity.
Qed.

Theorem pr_no_forging_step : forall s0 tr i,
  pr_no_forgery s0 tr -> pr_no_forgery s0 (tr ++ [i]).
Proof.
  intros s0 tr i Hnf f Hin. rewrite pr_run_snoc in Hin. simpl in Hin.
  destruct (pr_facts_step _ i f Hin) as [Hold | [Hi [Hc Hf]]].
  - destruct (Hnf f Hold) as [pre [mid [Htr [Hc [Hf _]]]]].
    rewrite Htr, <- app_assoc. simpl. apply pr_earned_intro; assumption.
  - subst i. apply pr_earned_intro; assumption.
Qed.

Theorem pr_no_forging : forall s0 tr, G.clean_start s0 -> pr_no_forgery s0 tr.
Proof.
  intros s0 tr [Hf _]. induction tr as [| i tr IH] using rev_ind.
  - intros f Hin. simpl in Hin. rewrite Hf in Hin. destruct Hin.
  - apply pr_no_forging_step, IH.
Qed.

(* ================================================================= *)
(* Earned provenance.                                                 *)
(* ================================================================= *)

Theorem pr_earned_commitment_provenance : forall s0 pre p c,
  G.clean_start s0 ->
  commit_ok (G.core_of (pr_run pre s0)) p c = true ->
  exists pre1 mid,
    pre = pre1 ++ CHECK p c :: mid /\
    check_ok (G.core_of (pr_run pre1 s0)) p c = true /\
    pr_cost (CHECK p c) >= 1 /\ pr_cost (COMMIT p c) >= 1 /\
    G.ver (G.core_of (pr_run pre1 s0)) c = G.ver (G.core_of (pr_run pre s0)) c /\
    pr_untouched (pr_run (pre1 ++ [CHECK p c]) s0) mid c.
Proof.
  intros s0 pre p c H0 Hc.
  apply (G.generic_commit_ok_iff prop_eqb prop_eqb_eq) in Hc as [_ Hin].
  destruct (pr_no_forging s0 pre H0 _ Hin) as [pre1 [mid [Htr [Hck [Hf Hlive]]]]].
  simpl in *. exists pre1, mid.
  split; [exact Htr |]. split; [exact Hck |].
  split; [simpl; lia |]. split; [simpl; lia |].
  split; [unfold G.claim in Hf; injection Hf as Hv; symmetry; exact Hv |].
  apply Hlive. reflexivity.
Qed.

Lemma pr_cert_first : forall s0 tr,
  G.cert s0 = false -> G.cert (pr_run tr s0) = true ->
  exists pre post, tr = pre ++ CERTIFY :: post /\
    G.cert (pr_run pre s0) = false /\ G.certify_ok (G.core_of (pr_run pre s0)) = true.
Proof.
  intros s0 tr H0. induction tr as [| i tr IH] using rev_ind; intro H1.
  - simpl in H1. congruence.
  - rewrite pr_run_snoc in H1. destruct (G.cert (pr_run tr s0)) eqn:Hc.
    + destruct (IH eq_refl) as [pre [post [-> Hrest]]].
      exists pre, (post ++ [i]). rewrite <- app_assoc. auto.
    + destruct (pr_only_certify_certifies _ i Hc H1) as [-> Hok].
      exists tr, []. auto.
Qed.

Lemma pr_chan_origin : forall s0 tr f,
  G.chan (G.core_of s0) = None -> G.chan (G.core_of (pr_run tr s0)) = Some f ->
  exists pre1 p c mid, tr = pre1 ++ COMMIT p c :: mid /\
    commit_ok (G.core_of (pr_run pre1 s0)) p c = true /\
    f = G.claim (G.core_of (pr_run pre1 s0)) p c.
Proof.
  intros s0 tr f H0. induction tr as [| i tr IH] using rev_ind; intro H1.
  - simpl in H1. congruence.
  - rewrite pr_run_snoc in H1. simpl in H1.
    destruct (pr_chan_step (G.core_of (pr_run tr s0)) i)
      as [Hs | [p [c [-> [Hok Hch]]]]].
    + rewrite Hs in H1. destruct (IH H1) as [pre1 [p [c [mid [-> Hrest]]]]].
      exists pre1, p, c, (mid ++ [i]). rewrite <- app_assoc. auto.
    + rewrite Hch in H1. injection H1 as <-. exists tr, p, c, []. auto.
Qed.

(* A raised flag was earned: CHECK, then COMMIT of the same claim at the
   same version with the counter untouched between, then CERTIFY. PAY may
   appear anywhere; it never stands in for any of the three. *)
Theorem pr_earned_certification_provenance : forall s0 tr,
  G.clean_start s0 -> G.cert (pr_run tr s0) = true ->
  exists pre1 p c mid1 mid2 post,
    tr = pre1 ++ CHECK p c :: mid1 ++ COMMIT p c :: mid2 ++ CERTIFY :: post /\
    check_ok (G.core_of (pr_run pre1 s0)) p c = true /\
    commit_ok (G.core_of (pr_run (pre1 ++ CHECK p c :: mid1) s0)) p c = true /\
    G.certify_ok (G.core_of (pr_run (pre1 ++ CHECK p c :: mid1 ++ COMMIT p c :: mid2) s0))
      = true /\
    G.ver (G.core_of (pr_run pre1 s0)) c
      = G.ver (G.core_of (pr_run (pre1 ++ CHECK p c :: mid1) s0)) c /\
    pr_untouched (pr_run (pre1 ++ [CHECK p c]) s0) mid1 c.
Proof.
  intros s0 tr H0 H1. pose proof H0 as [_ [Hch Hc0]].
  destruct (pr_cert_first s0 tr Hc0 H1) as [pre [post [-> [_ Hok]]]].
  pose proof Hok as Hset. unfold G.certify_ok in Hset.
  apply andb_true_iff in Hset as [_ Hset].
  destruct (G.chan (G.core_of (pr_run pre s0))) as [f |] eqn:Hf; [| discriminate].
  destruct (pr_chan_origin s0 pre f Hch Hf) as [preC [p [c [mid2 [-> [Hcm _]]]]]].
  destruct (pr_earned_commitment_provenance s0 preC p c H0 Hcm)
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

Theorem pr_certified_run_min_cost : forall s0 tr,
  G.clean_start s0 -> G.cert (pr_run tr s0) = true ->
  pr_total_cost tr >= 3 /\ G.mu (pr_run tr s0) >= G.mu s0 + 3.
Proof.
  intros s0 tr H0 H1.
  assert (Hc : pr_total_cost tr >= 3).
  { destruct (pr_earned_certification_provenance s0 tr H0 H1)
      as [pre1 [p [c [mid1 [mid2 [post [-> _]]]]]]].
    rewrite pr_total_cost_app. simpl. rewrite pr_total_cost_app. simpl.
    rewrite pr_total_cost_app. simpl. lia. }
  split; [exact Hc | rewrite pr_mu_conservation_trace; lia].
Qed.

Corollary pr_program_certified_min_cost : forall n P a b,
  G.cert (pr_run_prog n P (start a b)) = true -> G.mu (pr_run_prog n P (start a b)) >= 3.
Proof.
  intros n P a b H. rewrite pr_run_prog_trace in *.
  apply (pr_certified_run_min_cost (start a b)) in H;
    [simpl in H; lia | apply G.generic_start_clean].
Qed.

(* ================================================================= *)
(* The three-instruction chain on one property.                       *)
(* ================================================================= *)

Lemma pr_exec_check_pass : forall s p c,
  check_ok (G.core_of s) p c = true ->
  pr_exec s (CHECK p c) =
  G.mkst (G.record_fact (G.core_of s) (G.claim (G.core_of s) p c)) (G.mu s + 1) (G.cert s).
Proof.
  intros [k m r] p c H. simpl in *.
  assert (He : G.err k = false)
    by (unfold G.check_ok in H; destruct (G.err k); [discriminate | reflexivity]).
  unfold pr_exec, pr_cexec. simpl. rewrite He, H. simpl. rewrite orb_false_r. reflexivity.
Qed.

Lemma pr_exec_check_fail : forall s p c,
  G.err (G.core_of s) = false -> check_ok (G.core_of s) p c = false ->
  pr_exec s (CHECK p c) = G.mkst (G.trap (G.core_of s)) (G.mu s + 1) (G.cert s).
Proof.
  intros [k m r] p c He H. simpl in *.
  unfold pr_exec, pr_cexec. simpl. rewrite He, H. simpl. rewrite orb_false_r. reflexivity.
Qed.

Lemma pr_exec_commit_pass : forall s p c,
  commit_ok (G.core_of s) p c = true ->
  pr_exec s (COMMIT p c) =
  G.mkst (G.commit_to (G.core_of s) (G.claim (G.core_of s) p c)) (G.mu s + 1) (G.cert s).
Proof.
  intros [k m r] p c H. simpl in *.
  assert (He : G.err k = false)
    by (apply (G.generic_commit_ok_iff prop_eqb prop_eqb_eq) in H; apply H).
  unfold pr_exec, pr_cexec. simpl. rewrite He, H. simpl. rewrite orb_false_r. reflexivity.
Qed.

Definition pr_chain (p : prop) (c : ctr) : list pr_instr := [CHECK p c; COMMIT p c; CERTIFY].

(* From a start where p holds of counter c, the chain certifies and pays
   exactly the floor of 3. *)
Theorem pr_chain_certifies : forall p c a b,
  holds p (G.val (start_core a b) c) ->
  G.cert (pr_run_prog 4 (pr_chain p c) (start a b)) = true /\
  G.mu (pr_run_prog 4 (pr_chain p c) (start a b)) = 3.
Proof.
  intros p c a b H. apply eval_iff in H.
  assert (Hck : check_ok (start_core a b) p c = true)
    by (unfold G.check_ok; rewrite H; reflexivity).
  set (P := pr_chain p c).
  change (pr_run_prog 4 P (start a b))
    with (pr_step P (pr_step P (pr_step P (pr_step P (start a b))))).
  assert (E1 : pr_step P (start a b) = pr_exec (start a b) (CHECK p c)) by reflexivity.
  rewrite E1, (pr_exec_check_pass (start a b) p c Hck).
  change (G.core_of (start a b)) with (start_core a b).
  set (k1 := G.record_fact (start_core a b) (G.claim (start_core a b) p c)).
  assert (Hcm : commit_ok k1 p c = true).
  { apply (G.generic_commit_ok_iff prop_eqb prop_eqb_eq). split; [reflexivity |].
    left. destruct c; reflexivity. }
  set (s1 := G.mkst k1 (G.mu (start a b) + 1) (G.cert (start a b))).
  assert (E2 : pr_step P s1 = pr_exec s1 (COMMIT p c)) by reflexivity.
  rewrite E2, (pr_exec_commit_pass s1 p c Hcm).
  split; reflexivity.
Qed.

(* From a start where p fails on counter c, the CHECK traps, and no number
   of further steps raises the flag. *)
Theorem pr_chain_refused_forever : forall n p c a b,
  ~ holds p (G.val (start_core a b) c) ->
  G.cert (pr_run_prog n (pr_chain p c) (start a b)) = false /\
  (n >= 1 -> G.err (G.core_of (pr_run_prog n (pr_chain p c) (start a b))) = true).
Proof.
  intros n p c a b H.
  assert (He : eval p (G.val (start_core a b) c) = false)
    by (destruct (eval p _) eqn:E; [exfalso; apply H, eval_iff, E | reflexivity]).
  assert (Hck : check_ok (start_core a b) p c = false)
    by (unfold G.check_ok; rewrite He; reflexivity).
  destruct n as [| n]; [split; [reflexivity | lia] |].
  set (P := pr_chain p c).
  change (pr_run_prog (S n) P (start a b)) with (pr_run_prog n P (pr_step P (start a b))).
  assert (E1 : pr_step P (start a b) = pr_exec (start a b) (CHECK p c)) by reflexivity.
  rewrite E1, (pr_exec_check_fail (start a b) p c eq_refl Hck).
  rewrite pr_run_prog_trapped by reflexivity.
  split; [reflexivity | intros _; reflexivity].
Qed.

(* So the chain certifies exactly when p holds of the start value. *)
Corollary pr_chain_certifies_iff : forall p c a b,
  G.cert (pr_run_prog 4 (pr_chain p c) (start a b)) = true <->
  holds p (G.val (start_core a b) c).
Proof.
  intros p c a b. split.
  - intro H1. apply eval_iff.
    destruct (eval p (G.val (start_core a b) c)) eqn:E; [reflexivity | exfalso].
    assert (Hn : ~ holds p (G.val (start_core a b) c))
      by (intro Hh; apply eval_iff in Hh; congruence).
    destruct (pr_chain_refused_forever 4 p c a b Hn) as [H2 _]. congruence.
  - intro H. apply pr_chain_certifies, H.
Qed.

End Priced.

Arguments PAY {prop}.
Arguments HALT {prop}.
Arguments CERTIFY {prop}.

(* ================================================================= *)
(* Instance 1: the property language of EarnedCore.v.                 *)
(* ================================================================= *)

Corollary pr_core_earned_certification_provenance :
  forall (s0 : @G.state G.cprop) (tr : list (@pr_instr G.cprop)),
  G.clean_start s0 -> G.cert (pr_run G.cprop_eqb G.ceval tr s0) = true ->
  exists pre1 p c mid1 mid2 post,
    tr = pre1 ++ CHECK p c :: mid1 ++ COMMIT p c :: mid2 ++ CERTIFY :: post /\
    G.check_ok G.ceval (G.core_of (pr_run G.cprop_eqb G.ceval pre1 s0)) p c = true /\
    G.commit_ok G.cprop_eqb
      (G.core_of (pr_run G.cprop_eqb G.ceval (pre1 ++ CHECK p c :: mid1) s0)) p c = true /\
    G.certify_ok (G.core_of (pr_run G.cprop_eqb G.ceval
      (pre1 ++ CHECK p c :: mid1 ++ COMMIT p c :: mid2) s0)) = true /\
    G.ver (G.core_of (pr_run G.cprop_eqb G.ceval pre1 s0)) c
      = G.ver (G.core_of (pr_run G.cprop_eqb G.ceval (pre1 ++ CHECK p c :: mid1) s0)) c /\
    pr_untouched G.cprop_eqb G.ceval
      (pr_run G.cprop_eqb G.ceval (pre1 ++ [CHECK p c]) s0) mid1 c.
Proof. exact (pr_earned_certification_provenance G.cprop_eqb G.cprop_eqb_eq G.ceval). Qed.

Corollary pr_core_checker_soundness :
  forall (s0 : @G.state G.cprop) (tr : list (@pr_instr G.cprop)) (f : @G.fact G.cprop),
  G.clean_start s0 ->
  let k := G.core_of (pr_run G.cprop_eqb G.ceval tr s0) in
  In f (G.facts k) -> G.f_ver f = G.ver k (G.f_ctr f) ->
  G.cholds (G.f_prop f) (G.val k (G.f_ctr f)).
Proof. exact (pr_checker_soundness G.cprop_eqb G.ceval G.cholds G.ceval_iff). Qed.

Corollary pr_core_no_forging :
  forall (s0 : @G.state G.cprop) (tr : list (@pr_instr G.cprop)),
  G.clean_start s0 -> pr_no_forgery G.cprop_eqb G.ceval s0 tr.
Proof. exact (pr_no_forging G.cprop_eqb G.ceval). Qed.

Corollary pr_core_certified_run_min_cost :
  forall (s0 : @G.state G.cprop) (tr : list (@pr_instr G.cprop)),
  G.clean_start s0 -> G.cert (pr_run G.cprop_eqb G.ceval tr s0) = true ->
  pr_total_cost tr >= 3 /\ G.mu (pr_run G.cprop_eqb G.ceval tr s0) >= G.mu s0 + 3.
Proof. exact (pr_certified_run_min_cost G.cprop_eqb G.cprop_eqb_eq G.ceval). Qed.

(* The chain on "A is 0" certifies exactly from the starts with A = 0. *)
Corollary pr_core_zero_chain_iff : forall a b,
  G.cert (pr_run_prog G.cprop_eqb G.ceval 4 (pr_chain G.PZero G.CA) (G.start a b)) = true
  <-> a = 0.
Proof.
  exact (fun a b => pr_chain_certifies_iff G.cprop_eqb G.cprop_eqb_eq G.ceval G.cholds
                      G.ceval_iff G.PZero G.CA a b).
Qed.

(* ================================================================= *)
(* Instance 2: the same language plus "this counter is a sorted list". *)
(* ================================================================= *)

Corollary pr_sorted_earned_certification_provenance :
  forall (s0 : @G.state G.sprop) (tr : list (@pr_instr G.sprop)),
  G.clean_start s0 -> G.cert (pr_run G.sprop_eqb G.seval tr s0) = true ->
  exists pre1 p c mid1 mid2 post,
    tr = pre1 ++ CHECK p c :: mid1 ++ COMMIT p c :: mid2 ++ CERTIFY :: post /\
    G.check_ok G.seval (G.core_of (pr_run G.sprop_eqb G.seval pre1 s0)) p c = true /\
    G.commit_ok G.sprop_eqb
      (G.core_of (pr_run G.sprop_eqb G.seval (pre1 ++ CHECK p c :: mid1) s0)) p c = true /\
    G.certify_ok (G.core_of (pr_run G.sprop_eqb G.seval
      (pre1 ++ CHECK p c :: mid1 ++ COMMIT p c :: mid2) s0)) = true /\
    G.ver (G.core_of (pr_run G.sprop_eqb G.seval pre1 s0)) c
      = G.ver (G.core_of (pr_run G.sprop_eqb G.seval (pre1 ++ CHECK p c :: mid1) s0)) c /\
    pr_untouched G.sprop_eqb G.seval
      (pr_run G.sprop_eqb G.seval (pre1 ++ [CHECK p c]) s0) mid1 c.
Proof. exact (pr_earned_certification_provenance G.sprop_eqb G.sprop_eqb_eq G.seval). Qed.

Corollary pr_sorted_checker_soundness :
  forall (s0 : @G.state G.sprop) (tr : list (@pr_instr G.sprop)) (f : @G.fact G.sprop),
  G.clean_start s0 ->
  let k := G.core_of (pr_run G.sprop_eqb G.seval tr s0) in
  In f (G.facts k) -> G.f_ver f = G.ver k (G.f_ctr f) ->
  G.sholds (G.f_prop f) (G.val k (G.f_ctr f)).
Proof. exact (pr_checker_soundness G.sprop_eqb G.seval G.sholds G.seval_iff). Qed.

Corollary pr_sorted_no_forging :
  forall (s0 : @G.state G.sprop) (tr : list (@pr_instr G.sprop)),
  G.clean_start s0 -> pr_no_forgery G.sprop_eqb G.seval s0 tr.
Proof. exact (pr_no_forging G.sprop_eqb G.seval). Qed.

Corollary pr_sorted_certified_run_min_cost :
  forall (s0 : @G.state G.sprop) (tr : list (@pr_instr G.sprop)),
  G.clean_start s0 -> G.cert (pr_run G.sprop_eqb G.seval tr s0) = true ->
  pr_total_cost tr >= 3 /\ G.mu (pr_run G.sprop_eqb G.seval tr s0) >= G.mu s0 + 3.
Proof. exact (pr_certified_run_min_cost G.sprop_eqb G.sprop_eqb_eq G.seval). Qed.

(* A COMMIT of PSorted that would succeed means the counter's current value
   decodes to a sorted list. *)
Corollary pr_sorted_committed_claim_holds :
  forall (s0 : @G.state G.sprop) (tr : list (@pr_instr G.sprop)) c,
  G.clean_start s0 ->
  G.commit_ok G.sprop_eqb (G.core_of (pr_run G.sprop_eqb G.seval tr s0)) G.PSorted c = true ->
  Sorted le (G.decode (G.val (G.core_of (pr_run G.sprop_eqb G.seval tr s0)) c)).
Proof.
  intros s0 tr c H0 H.
  exact (pr_committed_claim_holds G.sprop_eqb G.sprop_eqb_eq G.seval G.sholds G.seval_iff
           s0 tr G.PSorted c H0 H).
Qed.

(* The program: check that counter A is a sorted list, commit, certify. *)
Definition pr_sorted_run : list (@pr_instr G.sprop) := pr_chain G.PSorted G.CA.

(* It certifies exactly from the starts whose A decodes to a sorted list,
   paying exactly 3, and from every other start it is refused forever. *)
Theorem pr_sorted_run_certifies_iff : forall a b,
  G.cert (pr_run_prog G.sprop_eqb G.seval 4 pr_sorted_run (G.start a b)) = true <->
  Sorted le (G.decode a).
Proof.
  exact (fun a b => pr_chain_certifies_iff G.sprop_eqb G.sprop_eqb_eq G.seval G.sholds
                      G.seval_iff G.PSorted G.CA a b).
Qed.

Theorem pr_sorted_run_certifies : forall a b,
  Sorted le (G.decode a) ->
  G.cert (pr_run_prog G.sprop_eqb G.seval 4 pr_sorted_run (G.start a b)) = true /\
  G.mu (pr_run_prog G.sprop_eqb G.seval 4 pr_sorted_run (G.start a b)) = 3.
Proof.
  intros a b H.
  exact (pr_chain_certifies G.sprop_eqb G.sprop_eqb_eq G.seval G.sholds G.seval_iff
           G.PSorted G.CA a b H).
Qed.

Theorem pr_sorted_run_refused_forever : forall n a b,
  ~ Sorted le (G.decode a) ->
  G.cert (pr_run_prog G.sprop_eqb G.seval n pr_sorted_run (G.start a b)) = false.
Proof.
  intros n a b H.
  exact (proj1 (pr_chain_refused_forever G.sprop_eqb G.seval G.sholds G.seval_iff
                  n G.PSorted G.CA a b H)).
Qed.

(* Concrete starts, as in EarnedGeneric.v: 18 decodes to [1; 2] and 20
   decodes to [2; 1]. *)
Theorem pr_sorted_demo_certifies :
  G.decode 18 = [1; 2] /\
  G.cert (pr_run_prog G.sprop_eqb G.seval 4 pr_sorted_run (G.start 18 0)) = true /\
  G.mu (pr_run_prog G.sprop_eqb G.seval 4 pr_sorted_run (G.start 18 0)) = 3.
Proof. vm_compute. auto. Qed.

Theorem pr_sorted_demo_refused_forever :
  G.decode 20 = [2; 1] /\
  forall n, G.cert (pr_run_prog G.sprop_eqb G.seval n pr_sorted_run (G.start 20 0)) = false.
Proof.
  split; [vm_compute; reflexivity |].
  intro n. apply pr_sorted_run_refused_forever.
  intro H. apply G.sortedb_iff in H. vm_compute in H. discriminate H.
Qed.

(* PAY placed between CHECK and COMMIT leaves the chain intact and adds its
   price: from a start whose A decodes to a sorted list, CHECK; PAY; COMMIT;
   CERTIFY certifies and pays 4. *)
Definition pr_sorted_paid_run : list (@pr_instr G.sprop) :=
  [CHECK G.PSorted G.CA; PAY; COMMIT G.PSorted G.CA; CERTIFY].

Theorem pr_sorted_paid_demo :
  G.cert (pr_run_prog G.sprop_eqb G.seval 5 pr_sorted_paid_run (G.start 18 0)) = true /\
  G.mu (pr_run_prog G.sprop_eqb G.seval 5 pr_sorted_paid_run (G.start 18 0)) = 4 /\
  G.cert (pr_run_prog G.sprop_eqb G.seval 5 pr_sorted_paid_run (G.start 20 0)) = false.
Proof. vm_compute. auto. Qed.

(* ================================================================= *)
(* Assumption audit. Every line must print                            *)
(* "Closed under the global context".                                 *)
(* ================================================================= *)

Print Assumptions pr_pay_neutral.
Print Assumptions pr_pay_exec.
Print Assumptions pr_pay_never_fires.
Print Assumptions priced_extends_generic.
Print Assumptions pr_pay_free_is_generic.
Print Assumptions pr_trapped_inert.
Print Assumptions pr_run_prog_trapped.
Print Assumptions pr_mu_conservation_trace.
Print Assumptions pr_mu_conservation_program.
Print Assumptions pr_cert_latch.
Print Assumptions pr_cert_permanent.
Print Assumptions pr_only_certify_certifies.
Print Assumptions pr_a2.
Print Assumptions pr_nfi_floor.
Print Assumptions pr_full_table_traps.
Print Assumptions pr_facts_bounded_step.
Print Assumptions pr_unearned_commit_traps.
Print Assumptions pr_uncommitted_certify_traps.
Print Assumptions pr_facts_count.
Print Assumptions pr_facts_count_clean.
Print Assumptions pr_facts_count_program.
Print Assumptions pr_checker_soundness.
Print Assumptions pr_committed_claim_holds.
Print Assumptions pr_no_forging_step.
Print Assumptions pr_no_forging.
Print Assumptions pr_earned_commitment_provenance.
Print Assumptions pr_earned_certification_provenance.
Print Assumptions pr_certified_run_min_cost.
Print Assumptions pr_program_certified_min_cost.
Print Assumptions pr_chain_certifies.
Print Assumptions pr_chain_refused_forever.
Print Assumptions pr_chain_certifies_iff.
Print Assumptions pr_core_earned_certification_provenance.
Print Assumptions pr_core_checker_soundness.
Print Assumptions pr_core_no_forging.
Print Assumptions pr_core_certified_run_min_cost.
Print Assumptions pr_core_zero_chain_iff.
Print Assumptions pr_sorted_earned_certification_provenance.
Print Assumptions pr_sorted_checker_soundness.
Print Assumptions pr_sorted_no_forging.
Print Assumptions pr_sorted_certified_run_min_cost.
Print Assumptions pr_sorted_committed_claim_holds.
Print Assumptions pr_sorted_run_certifies_iff.
Print Assumptions pr_sorted_run_certifies.
Print Assumptions pr_sorted_run_refused_forever.
Print Assumptions pr_sorted_demo_certifies.
Print Assumptions pr_sorted_demo_refused_forever.
Print Assumptions pr_sorted_paid_demo.
