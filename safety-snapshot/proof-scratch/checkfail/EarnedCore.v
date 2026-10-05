(** EarnedCore.v: the substrate on the smallest scaffold I could build.

    MuCore.v shows the toll: raising the certified flag costs at least 1.
    This file shows the other half, the part that makes the flag mean
    something. The machine is two unbounded counters and a program counter,
    which is already every computation there is (Minsky's two-counter
    machine), plus the substrate: a version per counter, a ledger mu, a table
    of established facts, a commitment channel, the certified flag, and a trap
    latch. Three instructions touch the substrate:

      CHECK p c   evaluate the property p on counter c. On success the fact
                  (p, c, current version of c) goes into the table. Costs 1.
      COMMIT p c  succeeds only if the table holds (p, c, current version of
                  c). Then the channel names that fact. Costs 1.
      CERTIFY     succeeds only if the channel names a commitment. Then the
                  flag goes up. Costs 1.

    Every failure traps: the latch goes up, a stored program stops there,
    and any instruction issued after that changes nothing but the ledger. Every write to a counter bumps that counter's version, so a fact
    about an old version never authorizes a claim about the new one. Facts
    are never removed or overwritten; a full table traps instead of evicting,
    and versions are unbounded naturals, so nothing wraps. The start state
    holds no facts, no commitment, and a lowered flag.

    What is proved (every result closed under the global context):

      1. Universality. The INC/DEC fragment is the two-counter machine, step
         for step, with the halting correspondence  [simulation_step,
         simulation_run, halting_correspondence]. Minsky (1961, 1967) showed
         two counters run every program, and EarnedCoreLinks.v turns this into
         undecidability of this machine's halting problem with the vendored
         MM2 library.
      2. The toll. mu is the exact sum of what was executed, only CERTIFY
         raises the flag, it pays at least 1 doing so, and the flag is a
         latch of the base: it never drops, and its next value is a function
         of the rest of the state and itself  [mu_conservation_trace, a2,
         nfi_floor, only_certify_certifies, cert_latch, cert_permanent].
      3. Earned provenance. From a clean start, every commitment that can
         succeed is preceded by a successful paid CHECK of the same claim at
         the same version, and nothing touched that counter in between; a
         raised flag is preceded by CHECK, then COMMIT, then CERTIFY
         [earned_commitment_provenance, earned_certification_provenance].
      4. Checker soundness. A live fact (p, c, v), with v the current version
         of c, means p holds of c's current value  [checker_soundness].
      5. No forging. Every instruction keeps "every fact in the table was
         written by a passing CHECK of exactly that claim, and if it is still
         live, nothing touched its counter since"  [facts_step,
         no_forging_step, no_forging].
      6. Separation. Two runs end with the same counters, versions and
         program counter and different (mu, flag, facts); no function of
         that window recovers mu, the flag, or the right to commit
         [receipt_separation, no_mu_oracle, no_cert_oracle,
         no_commit_oracle].
      7. Price. A certified run from a clean start costs at least 3, and a
         three-instruction program pays exactly 3  [certified_run_min_cost,
         min_cost_tight].

    Dependencies: Coq standard library only. No axioms, no Admitted.        *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose, for the
   same reason as MuCore.v: this file imports nothing but the Coq standard
   library so anyone can re-check it from a clean checkout. Its link to the
   abstract records (CertificationSystem, the latch base, Adequate) and to
   the vendored halting undecidability lives in EarnedCoreLinks.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.

(* ================================================================= *)
(* Objects, properties, facts.                                        *)
(* ================================================================= *)

Inductive ctr : Type := CA | CB.

(* The property language: fixed, finite in shape, exact. *)
Inductive prop : Type :=
| PZero          (* the counter is 0      *)
| PEven          (* the counter is even   *)
| PGe (n : nat). (* the counter is >= n   *)

Definition eval (p : prop) (v : nat) : bool :=
  match p with
  | PZero => Nat.eqb v 0
  | PEven => Nat.even v
  | PGe n => Nat.leb n v
  end.

(* What each property means, stated without the checker. *)
Definition holds (p : prop) (v : nat) : Prop :=
  match p with
  | PZero => v = 0
  | PEven => exists m, v = 2 * m
  | PGe n => n <= v
  end.

Lemma eval_iff : forall p v, eval p v = true <-> holds p v.
Proof.
  intros [| | n] v; simpl.
  - apply Nat.eqb_eq.
  - rewrite Nat.even_spec. unfold Nat.Even. tauto.
  - apply Nat.leb_le.
Qed.

(* A fact is a claim about one version of one object. *)
Record fact : Type := mkfact { f_prop : prop; f_ctr : ctr; f_ver : nat }.

Definition ctr_eqb (c d : ctr) : bool :=
  match c, d with CA, CA | CB, CB => true | _, _ => false end.

Definition prop_eqb (p q : prop) : bool :=
  match p, q with
  | PZero, PZero | PEven, PEven => true
  | PGe n, PGe m => Nat.eqb n m
  | _, _ => false
  end.

(* Exact claim identity: field by field, no digest. *)
Definition fact_eqb (f g : fact) : bool :=
  prop_eqb (f_prop f) (f_prop g) && ctr_eqb (f_ctr f) (f_ctr g)
  && Nat.eqb (f_ver f) (f_ver g).

Lemma fact_eqb_eq : forall f g, fact_eqb f g = true <-> f = g.
Proof.
  intros [p c v] [q d w]. unfold fact_eqb. simpl.
  rewrite !andb_true_iff, Nat.eqb_eq. split.
  - intros [[Hp Hc] Hv]. subst w.
    assert (p = q) as ->.
    { destruct p, q; simpl in Hp; try discriminate; try reflexivity.
      apply Nat.eqb_eq in Hp. subst. reflexivity. }
    assert (c = d) as ->.
    { destruct c, d; simpl in Hc; try discriminate; reflexivity. }
    reflexivity.
  - intros H. inversion H. subst.
    split; [split |]; [destruct q; simpl; auto using Nat.eqb_refl
                      | destruct d; reflexivity | reflexivity].
Qed.

(* ================================================================= *)
(* The machine.                                                       *)
(* ================================================================= *)

Inductive instr : Type :=
| INC (c : ctr)              (* c := c + 1                               *)
| DEC (c : ctr) (j : nat)    (* if c > 0 then c := c - 1, jump to j      *)
| HALT
| CHECK (p : prop) (c : ctr)
| COMMIT (p : prop) (c : ctr)
| CERTIFY.

Definition cost (i : instr) : nat :=
  match i with
  | CHECK _ _ | COMMIT _ _ | CERTIFY => 1
  | _ => 0
  end.

(* Everything except the ledger and the flag. *)
Record core : Type := mkcore {
  ca : nat; cb : nat;       (* the two counters        *)
  va : nat; vb : nat;       (* their versions          *)
  pc : nat;                 (* 1-based, as in Minsky   *)
  facts : list fact;        (* established facts       *)
  chan : option fact;       (* the commitment channel  *)
  err : bool                (* the trap latch          *)
}.

Definition val (k : core) (c : ctr) : nat :=
  match c with CA => ca k | CB => cb k end.
Definition ver (k : core) (c : ctr) : nat :=
  match c with CA => va k | CB => vb k end.

(* A write sets a counter, bumps its version, and moves pc to j. *)
Definition write (k : core) (c : ctr) (n j : nat) : core :=
  match c with
  | CA => mkcore n (cb k) (S (va k)) (vb k) j (facts k) (chan k) (err k)
  | CB => mkcore (ca k) n (va k) (S (vb k)) j (facts k) (chan k) (err k)
  end.
Definition goto (k : core) (j : nat) : core :=
  mkcore (ca k) (cb k) (va k) (vb k) j (facts k) (chan k) (err k).
Definition trap (k : core) : core :=
  mkcore (ca k) (cb k) (va k) (vb k) (pc k) (facts k) (chan k) true.
Definition record_fact (k : core) (f : fact) : core :=
  mkcore (ca k) (cb k) (va k) (vb k) (S (pc k)) (f :: facts k) (chan k) (err k).
Definition commit_to (k : core) (f : fact) : core :=
  mkcore (ca k) (cb k) (va k) (vb k) (S (pc k)) (facts k) (Some f) (err k).

Definition fact_cap : nat := 16.

(* The claim "p holds of c" about c's current version. *)
Definition claim (k : core) (p : prop) (c : ctr) : fact := mkfact p c (ver k c).

Definition check_ok (k : core) (p : prop) (c : ctr) : bool :=
  negb (err k) && eval p (val k c) && Nat.ltb (length (facts k)) fact_cap.
Definition commit_ok (k : core) (p : prop) (c : ctr) : bool :=
  negb (err k) && existsb (fact_eqb (claim k p c)) (facts k).
Definition certify_ok (k : core) : bool :=
  negb (err k) && match chan k with Some _ => true | None => false end.

Definition cexec (k : core) (i : instr) : core :=
  if err k then k else
  match i with
  | INC c => write k c (S (val k c)) (S (pc k))
  | DEC c j =>
      match val k c with
      | 0 => goto k (S (pc k))
      | S n => write k c n j
      end
  | HALT => k
  | CHECK p c => if check_ok k p c then record_fact k (claim k p c) else trap k
  | COMMIT p c => if commit_ok k p c then commit_to k (claim k p c) else trap k
  | CERTIFY => if certify_ok k then goto k (S (pc k)) else trap k
  end.

(* The one event that raises the flag. *)
Definition fires (k : core) (i : instr) : bool :=
  match i with CERTIFY => certify_ok k | _ => false end.

Record state : Type := mkst { core_of : core; mu : nat; cert : bool }.

(* The base moves without reading mu or the flag; the ledger is charged in
   the same step; the flag is a latch of the base. *)
Definition exec (s : state) (i : instr) : state :=
  mkst (cexec (core_of s) i) (mu s + cost i) (cert s || fires (core_of s) i).

Fixpoint run (tr : list instr) (s : state) : state :=
  match tr with [] => s | i :: rest => run rest (exec s i) end.

Fixpoint total_cost (tr : list instr) : nat :=
  match tr with [] => 0 | i :: rest => cost i + total_cost rest end.

Definition start_core (a b : nat) : core := mkcore a b 0 0 1 [] None false.
Definition start (a b : nat) : state := mkst (start_core a b) 0 false.

Definition clean_start (s : state) : Prop :=
  facts (core_of s) = [] /\ chan (core_of s) = None /\ cert s = false.

Lemma start_clean : forall a b, clean_start (start a b).
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

Definition core_step (P : list instr) (k : core) : core :=
  match next_instr P k with None => k | Some i => cexec k i end.

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

Lemma run_app : forall l1 l2 s, run (l1 ++ l2) s = run l2 (run l1 s).
Proof. induction l1; intros; simpl; auto. Qed.

Lemma run_snoc : forall l i s, run (l ++ [i]) s = exec (run l s) i.
Proof. intros. rewrite run_app. reflexivity. Qed.

Lemma total_cost_app : forall l1 l2,
  total_cost (l1 ++ l2) = total_cost l1 + total_cost l2.
Proof. induction l1; intros; simpl; [| rewrite IHl1]; lia. Qed.

Lemma run_prog_halted : forall n P s, halted P (core_of s) -> run_prog n P s = s.
Proof.
  induction n; intros P s H; simpl; [reflexivity |].
  unfold step. unfold halted in H. rewrite H. apply IHn. exact H.
Qed.

Lemma run_prog_trace : forall n P s, run_prog n P s = run (trace_of n P s) s.
Proof.
  induction n; intros P s; simpl; [reflexivity |].
  unfold step. destruct (next_instr P (core_of s)) eqn:H.
  - apply IHn.
  - apply run_prog_halted. exact H.
Qed.

Lemma step_core : forall P s, core_of (step P s) = core_step P (core_of s).
Proof. intros. unfold step, core_step. destruct (next_instr P (core_of s)); reflexivity. Qed.

Lemma step_cert : forall P s,
  cert (step P s) =
  cert s || match next_instr P (core_of s) with
            | Some i => fires (core_of s) i | None => false end.
Proof.
  intros. unfold step. destruct (next_instr P (core_of s)); simpl;
  [reflexivity | rewrite orb_false_r; reflexivity].
Qed.

Lemma step_mu : forall P s,
  mu (step P s) =
  mu s + match next_instr P (core_of s) with Some i => cost i | None => 0 end.
Proof.
  intros. unfold step. destruct (next_instr P (core_of s)); simpl; lia.
Qed.

(* ================================================================= *)
(* 1. Universality: the INC/DEC fragment is the two-counter machine.  *)
(* ================================================================= *)

Inductive minsky : Type := MINC (c : ctr) | MDEC (c : ctr) (j : nat).

(* (pc, (a, b)), 1-based pc; a pc with no instruction is a stop. *)
Definition mconf : Type := (nat * (nat * nat))%type.

Definition mval (x : mconf) (c : ctr) : nat :=
  match c with CA => fst (snd x) | CB => snd (snd x) end.
Definition mset (x : mconf) (c : ctr) (n j : nat) : mconf :=
  match c with CA => (j, (n, snd (snd x))) | CB => (j, (fst (snd x), n)) end.

Definition mstep (M : list minsky) (x : mconf) : option mconf :=
  match fetch M (fst x) with
  | None => None
  | Some (MINC c) => Some (mset x c (S (mval x c)) (S (fst x)))
  | Some (MDEC c j) =>
      match mval x c with
      | 0 => Some (S (fst x), snd x)
      | S n => Some (mset x c n j)
      end
  end.

Fixpoint mrun (n : nat) (M : list minsky) (x : mconf) : mconf :=
  match n with
  | 0 => x
  | S m => match mstep M x with None => x | Some y => mrun m M y end
  end.

Definition compile_instr (m : minsky) : instr :=
  match m with MINC c => INC c | MDEC c j => DEC c j end.
Definition compile (M : list minsky) : list instr := map compile_instr M.

(* What a counter-machine observer sees. *)
Definition window (k : core) : mconf := (pc k, (ca k, cb k)).

Lemma fetch_map : forall (A B : Type) (f : A -> B) (l : list A) n,
  fetch (map f l) n = option_map f (fetch l n).
Proof. intros A B f l [| n]; simpl; [reflexivity | apply nth_error_map]. Qed.

Theorem simulation_step : forall M k,
  err k = false ->
  (mstep M (window k) = None <-> halted (compile M) k) /\
  (forall y, mstep M (window k) = Some y ->
     window (core_step (compile M) k) = y /\ err (core_step (compile M) k) = false).
Proof.
  intros M k Herr. unfold halted, core_step, next_instr, compile.
  rewrite Herr, fetch_map. unfold mstep, window. simpl.
  destruct (fetch M (pc k)) as [[c | c j] |]; simpl.
  - split; [split; intro H; discriminate H |].
    intros y Hy. inversion Hy. subst y. unfold cexec. rewrite Herr.
    destruct c; simpl; auto.
  - split; [destruct c; simpl; [destruct (ca k) | destruct (cb k)];
            split; intro H; discriminate H |].
    intros y Hy. unfold cexec. rewrite Herr.
    destruct c; simpl in *.
    + destruct (ca k) eqn:Ha; inversion Hy; subst y; simpl; rewrite ?Ha; auto.
    + destruct (cb k) eqn:Hb; inversion Hy; subst y; simpl; rewrite ?Hb; auto.
  - split; [split; reflexivity | intros y Hy; discriminate Hy].
Qed.

Fixpoint core_run (n : nat) (P : list instr) (k : core) : core :=
  match n with 0 => k | S m => core_run m P (core_step P k) end.

Lemma core_run_prog : forall n P s,
  core_of (run_prog n P s) = core_run n P (core_of s).
Proof.
  induction n; intros; simpl; [reflexivity |]. rewrite IHn, step_core. reflexivity.
Qed.

Lemma core_run_halted : forall n P k, halted P k -> core_run n P k = k.
Proof.
  induction n; intros P k H; simpl; [reflexivity |].
  unfold core_step. unfold halted in H. rewrite H. apply IHn. exact H.
Qed.

Theorem simulation_run : forall n M k,
  err k = false ->
  window (core_run n (compile M) k) = mrun n M (window k) /\
  err (core_run n (compile M) k) = false.
Proof.
  induction n; intros M k Herr; simpl; [auto |].
  destruct (simulation_step M k Herr) as [Hstop Hgo].
  destruct (mstep M (window k)) as [y |] eqn:Hm.
  - destruct (Hgo y eq_refl) as [Hw He].
    rewrite <- Hw. apply IHn. exact He.
  - assert (Hh : halted (compile M) k) by (apply Hstop; reflexivity).
    unfold core_step. unfold halted in Hh. rewrite Hh.
    rewrite core_run_halted by exact Hh. auto.
Qed.

(* A two-counter program halts from (a, b) iff its compiled program halts
   on this machine from start a b. *)
Theorem halting_correspondence : forall M a b,
  (exists n, mstep M (mrun n M (1, (a, b))) = None) <->
  (exists n, halted (compile M) (core_of (run_prog n (compile M) (start a b)))).
Proof.
  intros M a b.
  assert (Hrun : forall n,
    window (core_run n (compile M) (start_core a b)) = mrun n M (1, (a, b)) /\
    err (core_run n (compile M) (start_core a b)) = false)
    by (intro n; apply (simulation_run n M (start_core a b)); reflexivity).
  split; intros [n Hn]; exists n.
  - rewrite core_run_prog. destruct (Hrun n) as [Hw He].
    apply (proj1 (simulation_step M _ He)). simpl. rewrite Hw. exact Hn.
  - rewrite core_run_prog in Hn. destruct (Hrun n) as [Hw He].
    rewrite <- Hw. apply (proj1 (simulation_step M _ He)). exact Hn.
Qed.

(* ================================================================= *)
(* 2. The toll, the ledger, the latch.                                *)
(* ================================================================= *)

Theorem mu_conservation : forall s i, mu (exec s i) = mu s + cost i.
Proof. reflexivity. Qed.

Theorem mu_conservation_trace : forall tr s, mu (run tr s) = mu s + total_cost tr.
Proof. induction tr; intros; simpl; [lia | rewrite IHtr; simpl; lia]. Qed.

Theorem mu_conservation_program : forall n P s,
  mu (run_prog n P s) = mu s + total_cost (trace_of n P s).
Proof. intros. rewrite run_prog_trace. apply mu_conservation_trace. Qed.

Theorem cert_latch : forall s i, cert (exec s i) = cert s || fires (core_of s) i.
Proof. reflexivity. Qed.

Theorem base_blind : forall s i, core_of (exec s i) = cexec (core_of s) i.
Proof. reflexivity. Qed.

Theorem cert_permanent : forall s i, cert s = true -> cert (exec s i) = true.
Proof. intros s i H. simpl. rewrite H. reflexivity. Qed.

Theorem only_certify_certifies : forall s i,
  cert s = false -> cert (exec s i) = true ->
  i = CERTIFY /\ certify_ok (core_of s) = true.
Proof.
  intros s i H0 H1. simpl in H1. rewrite H0 in H1. simpl in H1.
  destruct i; simpl in H1; try discriminate. auto.
Qed.

Theorem a2 : forall s i, cert s = false -> cert (exec s i) = true -> cost i >= 1.
Proof.
  intros s i H0 H1. destruct (only_certify_certifies s i H0 H1) as [-> _].
  simpl. lia.
Qed.

Theorem nfi_floor : forall tr s,
  cert s = false -> cert (run tr s) = true -> total_cost tr >= 1.
Proof.
  induction tr as [| i rest IH]; intros s H0 H1; simpl in *; [congruence |].
  destruct (cert (exec s i)) eqn:Hm.
  - pose proof (a2 s i H0 Hm). lia.
  - pose proof (IH _ Hm H1). lia.
Qed.

(* ================================================================= *)
(* Per-instruction facts about the substrate.                         *)
(* ================================================================= *)

Lemma ver_write : forall k c n j d,
  ver (write k c n j) d = if ctr_eqb c d then S (ver k d) else ver k d.
Proof. intros k [] n j []; reflexivity. Qed.

Lemma val_write : forall k c n j d,
  val (write k c n j) d = if ctr_eqb c d then n else val k d.
Proof. intros k [] n j []; reflexivity. Qed.

Lemma facts_write : forall k c n j, facts (write k c n j) = facts k.
Proof. intros k [] n j; reflexivity. Qed.

Lemma chan_write : forall k c n j, chan (write k c n j) = chan k.
Proof. intros k [] n j; reflexivity. Qed.

Lemma err_write : forall k c n j, err (write k c n j) = err k.
Proof. intros k [] n j; reflexivity. Qed.

(* Versions only grow, and an unchanged version means an unchanged value. *)
Lemma ver_mono : forall k i c, ver k c <= ver (cexec k i) c.
Proof.
  intros k i c. unfold cexec. destruct (err k); [lia |].
  destruct i as [d | d j | | p d | p d |]; simpl.
  - rewrite ver_write. destruct (ctr_eqb d c); lia.
  - destruct (val k d); [destruct c; simpl; lia |].
    rewrite ver_write. destruct (ctr_eqb d c); lia.
  - lia.
  - destruct (check_ok k p d); destruct c; simpl; lia.
  - destruct (commit_ok k p d); destruct c; simpl; lia.
  - destruct (certify_ok k); destruct c; simpl; lia.
Qed.

Lemma ver_same_val : forall k i c,
  ver (cexec k i) c = ver k c -> val (cexec k i) c = val k c.
Proof.
  intros k i c H. unfold cexec in *. destruct (err k); [reflexivity |].
  destruct i as [d | d j | | p d | p d |]; simpl in *.
  - rewrite ver_write in H. rewrite val_write.
    destruct (ctr_eqb d c); [lia | reflexivity].
  - destruct (val k d); [destruct c; reflexivity |].
    rewrite ver_write in H. rewrite val_write.
    destruct (ctr_eqb d c); [lia | reflexivity].
  - reflexivity.
  - destruct (check_ok k p d); destruct c; reflexivity.
  - destruct (commit_ok k p d); destruct c; reflexivity.
  - destruct (certify_ok k); destruct c; reflexivity.
Qed.

Lemma ver_check : forall k p c d, ver (cexec k (CHECK p c)) d = ver k d.
Proof.
  intros. unfold cexec. destruct (err k); [reflexivity |].
  destruct (check_ok k p c); destruct d; reflexivity.
Qed.

Lemma val_check : forall k p c d, val (cexec k (CHECK p c)) d = val k d.
Proof.
  intros. unfold cexec. destruct (err k); [reflexivity |].
  destruct (check_ok k p c); destruct d; reflexivity.
Qed.

(* No forging, one instruction: a fact after the step was there before,
   or this step is a passing CHECK of exactly that claim. *)
Theorem facts_step : forall k i f,
  In f (facts (cexec k i)) ->
  In f (facts k) \/
  (i = CHECK (f_prop f) (f_ctr f) /\ check_ok k (f_prop f) (f_ctr f) = true /\
   f = claim k (f_prop f) (f_ctr f)).
Proof.
  intros k i f H. unfold cexec in H. destruct (err k) eqn:He; [auto |].
  destruct i as [d | d j | | p d | p d |]; simpl in H.
  - rewrite facts_write in H. auto.
  - destruct (val k d); simpl in H; [auto | rewrite facts_write in H; auto].
  - auto.
  - destruct (check_ok k p d) eqn:Hc; simpl in H; [| auto].
    destruct H as [<- | H]; [right | auto]. simpl. auto.
  - destruct (commit_ok k p d); simpl in H; auto.
  - destruct (certify_ok k); simpl in H; auto.
Qed.

(* Immutable history: nothing is ever evicted. *)
Theorem facts_keep : forall k i f, In f (facts k) -> In f (facts (cexec k i)).
Proof.
  intros k i f H. unfold cexec. destruct (err k); [exact H |].
  destruct i as [d | d j | | p d | p d |]; simpl.
  - rewrite facts_write. exact H.
  - destruct (val k d); simpl; [exact H | rewrite facts_write; exact H].
  - exact H.
  - destruct (check_ok k p d); simpl; auto.
  - destruct (commit_ok k p d); simpl; auto.
  - destruct (certify_ok k); simpl; auto.
Qed.

(* Bounded storage: a full table traps and stays as it was. *)
Theorem full_table_traps : forall k p c,
  fact_cap <= length (facts k) ->
  err (cexec k (CHECK p c)) = true /\ facts (cexec k (CHECK p c)) = facts k.
Proof.
  intros k p c H. unfold cexec. destruct (err k) eqn:He; [auto |].
  unfold check_ok. rewrite He.
  replace (Nat.ltb (length (facts k)) fact_cap) with false
    by (symmetry; apply Nat.ltb_ge; exact H).
  rewrite andb_false_r. auto.
Qed.

Theorem facts_bounded_step : forall k i,
  length (facts k) <= fact_cap -> length (facts (cexec k i)) <= fact_cap.
Proof.
  intros k i H. unfold cexec. destruct (err k); [exact H |].
  destruct i as [d | d j | | p d | p d |]; simpl.
  - rewrite facts_write. exact H.
  - destruct (val k d); simpl; [exact H | rewrite facts_write; exact H].
  - exact H.
  - destruct (check_ok k p d) eqn:Hc; simpl; [| exact H].
    unfold check_ok in Hc. apply andb_true_iff in Hc as [_ Hc].
    apply Nat.ltb_lt in Hc. lia.
  - destruct (commit_ok k p d); simpl; exact H.
  - destruct (certify_ok k); simpl; exact H.
Qed.

Lemma chan_step : forall k i,
  chan (cexec k i) = chan k \/
  exists p c, i = COMMIT p c /\ commit_ok k p c = true /\
              chan (cexec k i) = Some (claim k p c).
Proof.
  intros k i. unfold cexec. destruct (err k); [auto |].
  destruct i as [d | d j | | p d | p d |]; simpl.
  - rewrite chan_write. auto.
  - destruct (val k d); simpl; [auto | rewrite chan_write; auto].
  - auto.
  - destruct (check_ok k p d); simpl; auto.
  - destruct (commit_ok k p d) eqn:Hc; simpl; [right; eauto | auto].
  - destruct (certify_ok k); simpl; auto.
Qed.

Lemma commit_ok_iff : forall k p c,
  commit_ok k p c = true <-> err k = false /\ In (claim k p c) (facts k).
Proof.
  intros. unfold commit_ok. rewrite andb_true_iff, negb_true_iff, existsb_exists.
  split.
  - intros [He [f [Hin Hf]]]. apply fact_eqb_eq in Hf. subst. auto.
  - intros [He Hin]. split; [exact He |]. exists (claim k p c).
    split; [exact Hin | apply fact_eqb_eq; reflexivity].
Qed.

(* A commitment without a live fact traps and changes no claim state. *)
Theorem unearned_commit_traps : forall k p c,
  commit_ok k p c = false ->
  err (cexec k (COMMIT p c)) = true /\
  chan (cexec k (COMMIT p c)) = chan k /\ facts (cexec k (COMMIT p c)) = facts k.
Proof.
  intros k p c H. unfold cexec. destruct (err k) eqn:He; [auto |].
  rewrite H. auto.
Qed.

Theorem uncommitted_certify_traps : forall s,
  certify_ok (core_of s) = false ->
  err (core_of (exec s CERTIFY)) = true /\ cert (exec s CERTIFY) = cert s.
Proof.
  intros [k m r] H. simpl in *. rewrite H, orb_false_r. unfold cexec.
  destruct (err k) eqn:He; [auto |]. rewrite H. auto.
Qed.

(* ================================================================= *)
(* Runs: versions only grow, equal version means equal value.         *)
(* ================================================================= *)

Lemma ver_mono_run : forall l s c, ver (core_of s) c <= ver (core_of (run l s)) c.
Proof.
  induction l as [| i l IH]; intros s c; simpl; [lia |].
  pose proof (ver_mono (core_of s) i c). pose proof (IH (exec s i) c). simpl in *. lia.
Qed.

(* "Nothing touched c along mid, starting from s." *)
Definition untouched (s : state) (mid : list instr) (c : ctr) : Prop :=
  forall t1 i t2, mid = t1 ++ i :: t2 ->
    let k := core_of (run t1 s) in
    ver (cexec k i) c = ver k c /\ val (cexec k i) c = val k c.

Lemma untouched_of_ver : forall s mid c,
  ver (core_of (run mid s)) c = ver (core_of s) c -> untouched s mid c.
Proof.
  intros s mid c H t1 i t2 ->. simpl.
  rewrite run_app in H. simpl in H.
  pose proof (ver_mono_run t1 s c).
  pose proof (ver_mono (core_of (run t1 s)) i c).
  pose proof (ver_mono_run t2 (exec (run t1 s) i) c). simpl in *.
  assert (Hv : ver (cexec (core_of (run t1 s)) i) c = ver (core_of (run t1 s)) c) by lia.
  split; [exact Hv | apply ver_same_val; exact Hv].
Qed.

(* ================================================================= *)
(* 4. Checker soundness.                                              *)
(* ================================================================= *)

(* Every fact is about a version no newer than the current one, and a
   live fact (current version) holds of the current value. *)
Definition sound (k : core) : Prop :=
  forall f, In f (facts k) ->
    f_ver f <= ver k (f_ctr f) /\
    (f_ver f = ver k (f_ctr f) -> holds (f_prop f) (val k (f_ctr f))).

Lemma sound_step : forall k i, sound k -> sound (cexec k i).
Proof.
  intros k i Hs f Hin.
  pose proof (ver_mono k i (f_ctr f)) as Hm.
  destruct (facts_step k i f Hin) as [Hold | [Hi [Hc Hf]]].
  - destruct (Hs f Hold) as [Hle Hlive]. split; [lia |].
    intro Heq. assert (Hv : ver (cexec k i) (f_ctr f) = ver k (f_ctr f)) by lia.
    rewrite (ver_same_val k i _ Hv). apply Hlive. lia.
  - subst i. rewrite ver_check, val_check.
    rewrite Hf. simpl. split; [lia | intros _].
    unfold check_ok in Hc. apply andb_true_iff in Hc as [Hc _].
    apply andb_true_iff in Hc as [_ Hc]. apply eval_iff. exact Hc.
Qed.

Lemma sound_run : forall tr s, sound (core_of s) -> sound (core_of (run tr s)).
Proof. induction tr; intros s H; simpl; [exact H | apply IHtr, sound_step, H]. Qed.

Theorem checker_soundness : forall s0 tr f,
  clean_start s0 ->
  let k := core_of (run tr s0) in
  In f (facts k) -> f_ver f = ver k (f_ctr f) -> holds (f_prop f) (val k (f_ctr f)).
Proof.
  intros s0 tr f [Hf _] k Hin Hv.
  assert (Hs0 : sound (core_of s0)) by (intros g Hg; rewrite Hf in Hg; destruct Hg).
  exact (proj2 (sound_run tr s0 Hs0 f Hin) Hv).
Qed.

(* So the claim a successful COMMIT names is true when it is committed. *)
Corollary committed_claim_holds : forall s0 tr p c,
  clean_start s0 ->
  commit_ok (core_of (run tr s0)) p c = true ->
  holds p (val (core_of (run tr s0)) c).
Proof.
  intros s0 tr p c H0 Hc. apply commit_ok_iff in Hc as [_ Hin].
  exact (checker_soundness s0 tr _ H0 Hin eq_refl).
Qed.

(* ================================================================= *)
(* 5. No forging, over any run.                                       *)
(* ================================================================= *)

(* f was written by a passing CHECK of exactly f, after pre; and if f is
   still live at the end of tr, nothing touched its counter since. *)
Definition earned (s0 : state) (tr : list instr) (f : fact) : Prop :=
  exists pre mid,
    tr = pre ++ CHECK (f_prop f) (f_ctr f) :: mid /\
    check_ok (core_of (run pre s0)) (f_prop f) (f_ctr f) = true /\
    f = claim (core_of (run pre s0)) (f_prop f) (f_ctr f) /\
    (f_ver f = ver (core_of (run tr s0)) (f_ctr f) ->
     untouched (run (pre ++ [CHECK (f_prop f) (f_ctr f)]) s0) mid (f_ctr f)).

Definition no_forgery (s0 : state) (tr : list instr) : Prop :=
  forall f, In f (facts (core_of (run tr s0))) -> earned s0 tr f.

Lemma earned_intro : forall s0 pre mid f,
  check_ok (core_of (run pre s0)) (f_prop f) (f_ctr f) = true ->
  f = claim (core_of (run pre s0)) (f_prop f) (f_ctr f) ->
  earned s0 (pre ++ CHECK (f_prop f) (f_ctr f) :: mid) f.
Proof.
  intros s0 pre mid f Hc Hf. exists pre, mid.
  split; [reflexivity |]. split; [exact Hc |]. split; [exact Hf |].
  intro Hlive. apply untouched_of_ver.
  replace (pre ++ CHECK (f_prop f) (f_ctr f) :: mid)
    with ((pre ++ [CHECK (f_prop f) (f_ctr f)]) ++ mid) in Hlive
    by (rewrite <- app_assoc; reflexivity).
  rewrite run_app in Hlive. rewrite <- Hlive.
  rewrite run_snoc. simpl. rewrite ver_check.
  rewrite Hf at 1. reflexivity.
Qed.

Theorem no_forging_step : forall s0 tr i,
  no_forgery s0 tr -> no_forgery s0 (tr ++ [i]).
Proof.
  intros s0 tr i Hnf f Hin. rewrite run_snoc in Hin. simpl in Hin.
  destruct (facts_step _ i f Hin) as [Hold | [Hi [Hc Hf]]].
  - destruct (Hnf f Hold) as [pre [mid [Htr [Hc [Hf _]]]]].
    rewrite Htr, <- app_assoc. simpl. apply earned_intro; assumption.
  - subst i. apply earned_intro; assumption.
Qed.

Theorem no_forging : forall s0 tr, clean_start s0 -> no_forgery s0 tr.
Proof.
  intros s0 tr [Hf _]. induction tr as [| i tr IH] using rev_ind.
  - intros f Hin. simpl in Hin. rewrite Hf in Hin. destruct Hin.
  - apply no_forging_step, IH.
Qed.

(* ================================================================= *)
(* 3. Earned provenance.                                              *)
(* ================================================================= *)

(* A COMMIT that would succeed after pre has, inside pre, a successful
   paid CHECK of the same claim at the same version, and nothing touched
   the counter between the two. *)
Theorem earned_commitment_provenance : forall s0 pre p c,
  clean_start s0 ->
  commit_ok (core_of (run pre s0)) p c = true ->
  exists pre1 mid,
    pre = pre1 ++ CHECK p c :: mid /\
    check_ok (core_of (run pre1 s0)) p c = true /\
    cost (CHECK p c) >= 1 /\ cost (COMMIT p c) >= 1 /\
    ver (core_of (run pre1 s0)) c = ver (core_of (run pre s0)) c /\
    untouched (run (pre1 ++ [CHECK p c]) s0) mid c.
Proof.
  intros s0 pre p c H0 Hc. apply commit_ok_iff in Hc as [_ Hin].
  destruct (no_forging s0 pre H0 _ Hin) as [pre1 [mid [Htr [Hck [Hf Hlive]]]]].
  simpl in *. exists pre1, mid.
  split; [exact Htr |]. split; [exact Hck |].
  split; [simpl; lia |]. split; [simpl; lia |].
  split; [unfold claim in Hf; injection Hf as Hv; symmetry; exact Hv |].
  apply Hlive. reflexivity.
Qed.

Lemma cert_first : forall s0 tr,
  cert s0 = false -> cert (run tr s0) = true ->
  exists pre post, tr = pre ++ CERTIFY :: post /\
    cert (run pre s0) = false /\ certify_ok (core_of (run pre s0)) = true.
Proof.
  intros s0 tr H0. induction tr as [| i tr IH] using rev_ind; intro H1.
  - simpl in H1. congruence.
  - rewrite run_snoc in H1. destruct (cert (run tr s0)) eqn:Hc.
    + destruct (IH eq_refl) as [pre [post [-> Hrest]]].
      exists pre, (post ++ [i]). rewrite <- app_assoc. auto.
    + destruct (only_certify_certifies _ i Hc H1) as [-> Hok].
      exists tr, []. auto.
Qed.

Lemma chan_origin : forall s0 tr f,
  chan (core_of s0) = None -> chan (core_of (run tr s0)) = Some f ->
  exists pre1 p c mid, tr = pre1 ++ COMMIT p c :: mid /\
    commit_ok (core_of (run pre1 s0)) p c = true /\
    f = claim (core_of (run pre1 s0)) p c.
Proof.
  intros s0 tr f H0. induction tr as [| i tr IH] using rev_ind; intro H1.
  - simpl in H1. congruence.
  - rewrite run_snoc in H1. simpl in H1.
    destruct (chan_step (core_of (run tr s0)) i) as [Hs | [p [c [-> [Hok Hch]]]]].
    + rewrite Hs in H1. destruct (IH H1) as [pre1 [p [c [mid [-> Hrest]]]]].
      exists pre1, p, c, (mid ++ [i]). rewrite <- app_assoc. auto.
    + rewrite Hch in H1. injection H1 as <-. exists tr, p, c, []. auto.
Qed.

(* A raised flag was earned: CHECK, then COMMIT of the same claim at the
   same version with the counter untouched between, then CERTIFY. *)
Theorem earned_certification_provenance : forall s0 tr,
  clean_start s0 -> cert (run tr s0) = true ->
  exists pre1 p c mid1 mid2 post,
    tr = pre1 ++ CHECK p c :: mid1 ++ COMMIT p c :: mid2 ++ CERTIFY :: post /\
    check_ok (core_of (run pre1 s0)) p c = true /\
    commit_ok (core_of (run (pre1 ++ CHECK p c :: mid1) s0)) p c = true /\
    certify_ok (core_of (run (pre1 ++ CHECK p c :: mid1 ++ COMMIT p c :: mid2) s0))
      = true /\
    ver (core_of (run pre1 s0)) c = ver (core_of (run (pre1 ++ CHECK p c :: mid1) s0)) c /\
    untouched (run (pre1 ++ [CHECK p c]) s0) mid1 c.
Proof.
  intros s0 tr H0 H1. pose proof H0 as [_ [Hch Hc0]].
  destruct (cert_first s0 tr Hc0 H1) as [pre [post [-> [_ Hok]]]].
  pose proof Hok as Hset. unfold certify_ok in Hset.
  apply andb_true_iff in Hset as [_ Hset].
  destruct (chan (core_of (run pre s0))) as [f |] eqn:Hf; [| discriminate].
  destruct (chan_origin s0 pre f Hch Hf) as [preC [p [c [mid2 [-> [Hcm _]]]]]].
  destruct (earned_commitment_provenance s0 preC p c H0 Hcm)
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
(* 7. The price of an earned certificate.                             *)
(* ================================================================= *)

Theorem certified_run_min_cost : forall s0 tr,
  clean_start s0 -> cert (run tr s0) = true ->
  total_cost tr >= 3 /\ mu (run tr s0) >= mu s0 + 3.
Proof.
  intros s0 tr H0 H1.
  assert (Hc : total_cost tr >= 3).
  { destruct (earned_certification_provenance s0 tr H0 H1)
      as [pre1 [p [c [mid1 [mid2 [post [-> _]]]]]]].
    rewrite total_cost_app. simpl. rewrite total_cost_app. simpl.
    rewrite total_cost_app. simpl. lia. }
  split; [exact Hc | rewrite mu_conservation_trace; lia].
Qed.

Corollary program_certified_min_cost : forall n P a b,
  cert (run_prog n P (start a b)) = true -> mu (run_prog n P (start a b)) >= 3.
Proof.
  intros n P a b H. rewrite run_prog_trace in *.
  apply (certified_run_min_cost (start a b)) in H; [simpl in H; lia | apply start_clean].
Qed.

(* "Counter A is at least 0" holds of every start, so this program
   certifies from every start, paying exactly the floor. *)
Definition witness : list instr := [CHECK (PGe 0) CA; COMMIT (PGe 0) CA; CERTIFY].

Theorem min_cost_tight : forall a b,
  cert (run_prog 4 witness (start a b)) = true /\
  mu (run_prog 4 witness (start a b)) = 3 /\
  halted witness (core_of (run_prog 4 witness (start a b))).
Proof. intros a b. repeat split. Qed.

(* ================================================================= *)
(* 6. Separation: the window does not hold the record.                *)
(* ================================================================= *)

Definition earned_run : list instr := [CHECK PZero CA; COMMIT PZero CA; CERTIFY].
Definition idle_run : list instr := [DEC CA 0; DEC CA 0; DEC CA 0].

Definition state_A : state := run earned_run (start 0 0).
Definition state_B : state := run idle_run (start 0 0).

Theorem receipt_separation :
  window (core_of state_A) = window (core_of state_B) /\
  ver (core_of state_A) CA = ver (core_of state_B) CA /\
  ver (core_of state_A) CB = ver (core_of state_B) CB /\
  mu state_A <> mu state_B /\ cert state_A <> cert state_B /\
  facts (core_of state_A) <> facts (core_of state_B) /\
  commit_ok (core_of state_A) PZero CA <> commit_ok (core_of state_B) PZero CA.
Proof. vm_compute. repeat split; congruence. Qed.

Theorem no_mu_oracle :
  ~ exists g : mconf -> nat,
      forall tr, g (window (core_of (run tr (start 0 0)))) = mu (run tr (start 0 0)).
Proof.
  intros [g Hg]. pose proof (Hg earned_run) as HA. pose proof (Hg idle_run) as HB.
  destruct receipt_separation as [Hw [_ [_ [Hmu _]]]].
  unfold state_A, state_B in *. rewrite Hw in HA. congruence.
Qed.

Theorem no_cert_oracle :
  ~ exists g : mconf -> bool,
      forall tr, g (window (core_of (run tr (start 0 0)))) = cert (run tr (start 0 0)).
Proof.
  intros [g Hg]. pose proof (Hg earned_run) as HA. pose proof (Hg idle_run) as HB.
  destruct receipt_separation as [Hw [_ [_ [_ [Hc _]]]]].
  unfold state_A, state_B in *. rewrite Hw in HA. congruence.
Qed.

(* The right to commit is not in the counters either. *)
Theorem no_commit_oracle :
  ~ exists g : mconf -> bool,
      forall tr, g (window (core_of (run tr (start 0 0))))
                 = commit_ok (core_of (run tr (start 0 0))) PZero CA.
Proof.
  intros [g Hg]. pose proof (Hg earned_run) as HA. pose proof (Hg idle_run) as HB.
  destruct receipt_separation as [Hw [_ [_ [_ [_ [_ Hk]]]]]].
  unfold state_A, state_B in *. rewrite Hw in HA. congruence.
Qed.

(* ================================================================= *)
(* 7. The check can fail, and a failed check blocks the commitment.   *)
(* ================================================================= *)

(* A trapped machine takes no further step. *)
Lemma run_prog_trapped : forall n P s,
  err (core_of s) = true -> run_prog n P s = s.
Proof.
  induction n as [| n IH]; intros P s H; simpl; [reflexivity |].
  unfold step, next_instr. rewrite H. apply IH. exact H.
Qed.

(* The same three instructions certify when counter A is 0, paying exactly
   the floor, and trap with the flag down when it isn't. *)
Theorem earned_run_check_can_fail : forall a b,
  (a = 0 ->
     cert (run_prog 4 earned_run (start a b)) = true /\
     mu (run_prog 4 earned_run (start a b)) = 3) /\
  (a <> 0 ->
     cert (run_prog 4 earned_run (start a b)) = false /\
     err (core_of (run_prog 4 earned_run (start a b))) = true).
Proof.
  intros a b. split; intro Ha.
  - subst a. split; reflexivity.
  - destruct a as [| a]; [contradiction |]. split; reflexivity.
Qed.

(* And no amount of further running raises it. *)
Theorem earned_run_refused_forever : forall n a b,
  a <> 0 -> cert (run_prog n earned_run (start a b)) = false.
Proof.
  intros n a b Ha. destruct a as [| a]; [contradiction |].
  destruct n as [| n]; [reflexivity |].
  simpl. rewrite run_prog_trapped; reflexivity.
Qed.

(* ================================================================= *)
(* Assumption audit. Every line must print                            *)
(* "Closed under the global context".                                 *)
(* ================================================================= *)

Print Assumptions simulation_step.
Print Assumptions simulation_run.
Print Assumptions halting_correspondence.
Print Assumptions mu_conservation_trace.
Print Assumptions mu_conservation_program.
Print Assumptions cert_latch.
Print Assumptions cert_permanent.
Print Assumptions only_certify_certifies.
Print Assumptions a2.
Print Assumptions nfi_floor.
Print Assumptions facts_step.
Print Assumptions facts_keep.
Print Assumptions full_table_traps.
Print Assumptions facts_bounded_step.
Print Assumptions unearned_commit_traps.
Print Assumptions uncommitted_certify_traps.
Print Assumptions checker_soundness.
Print Assumptions committed_claim_holds.
Print Assumptions no_forging_step.
Print Assumptions no_forging.
Print Assumptions earned_commitment_provenance.
Print Assumptions earned_certification_provenance.
Print Assumptions certified_run_min_cost.
Print Assumptions program_certified_min_cost.
Print Assumptions min_cost_tight.
Print Assumptions receipt_separation.
Print Assumptions no_mu_oracle.
Print Assumptions no_cert_oracle.
Print Assumptions no_commit_oracle.
Print Assumptions earned_run_check_can_fail.
Print Assumptions earned_run_refused_forever.
