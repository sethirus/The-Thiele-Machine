(** EarnedGeneric.v: the small machine of EarnedCore.v with its property
    language left open.

    The machine is the one in EarnedCore.v, instruction for instruction:
    INC, DEC, HALT, CHECK, COMMIT, CERTIFY, the same costs (1 for CHECK,
    COMMIT and CERTIFY, 0 for the rest), the same versions, fact table,
    commitment channel, trap latch, certified flag and fact cap of 16. The
    one difference is that the properties CHECK can test are left open.
    Inside the section below they are any type [prop] with

      prop_eqb     a boolean equality, with prop_eqb_eq : prop_eqb p q = true <-> p = q
      eval         a boolean checker, eval : prop -> nat -> bool
      holds        what each property means, holds : prop -> nat -> Prop
      eval_iff     the checker is exact: eval p v = true <-> holds p v

    The provenance, soundness, no-forging and price theorems of EarnedCore.v
    are restated here and proved for every such language. The property
    language enters the proofs only through prop_eqb_eq (claim identity in
    the fact table) and eval_iff (checker soundness).

    Two instances follow the section.
      1. The language of EarnedCore.v: PZero, PEven, PGe n.
      2. That language plus PSorted. A counter value v is read as a list of
         naturals by decode, the bijection that sends 0 to the empty list
         and 2^x * (2y + 1) to x :: decode y. PSorted holds of v when
         decode v is sorted in nondecreasing order (Coq.Sorting.Sorted,
         Sorted le), and its checker is a boolean pass over adjacent pairs,
         proved equal to Sorted le. encode is the inverse direction, with
         decode (encode l) = l for every list l, so every list of naturals
         can sit in a counter.
    On instance 2, CHECK PSorted A; COMMIT PSorted A; CERTIFY certifies
    exactly when decode A is sorted, paying 3, and is refused forever
    otherwise; concrete starts 18 (decoding to [1; 2]) and 20 (decoding to
    [2; 1]) show both outcomes.

    Dependencies: Coq standard library only. No axioms, no Admitted.        *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose, as in
   EarnedCore.v: this file imports nothing but the Coq standard library so
   anyone can re-check it from a clean checkout. Its link to the abstract
   record (the machine over any property language, and over the sorted-list
   language, as a CertificationSystem with the trace cost floor) lives in
   EarnedGenericLinks.v. *)

From Coq Require Import List Arith Lia Bool.
From Coq Require Import Sorting.Sorted.
Import ListNotations.

Section Generic.

(* ================================================================= *)
(* The open property language.                                        *)
(* ================================================================= *)

Context {prop : Type}.
Variable prop_eqb : prop -> prop -> bool.
Hypothesis prop_eqb_eq : forall p q, prop_eqb p q = true <-> p = q.
Variable eval : prop -> nat -> bool.
Variable holds : prop -> nat -> Prop.
Hypothesis eval_iff : forall p v, eval p v = true <-> holds p v.

Inductive ctr : Type := CA | CB.

(* A fact is a claim about one version of one object. *)
Record fact : Type := mkfact { f_prop : prop; f_ctr : ctr; f_ver : nat }.

Definition ctr_eqb (c d : ctr) : bool :=
  match c, d with CA, CA | CB, CB => true | _, _ => false end.

(* Exact claim identity: field by field, no digest. *)
Definition fact_eqb (f g : fact) : bool :=
  prop_eqb (f_prop f) (f_prop g) && ctr_eqb (f_ctr f) (f_ctr g)
  && Nat.eqb (f_ver f) (f_ver g).

Lemma prop_eqb_refl : forall p, prop_eqb p p = true.
Proof. intro p. apply prop_eqb_eq. reflexivity. Qed.

Lemma generic_fact_eqb_eq : forall f g, fact_eqb f g = true <-> f = g.
Proof.
  intros [p c v] [q d w]. unfold fact_eqb. simpl.
  rewrite !andb_true_iff, Nat.eqb_eq, prop_eqb_eq. split.
  - intros [[Hp Hc] Hv]. subst q w.
    destruct c, d; simpl in Hc; try discriminate; reflexivity.
  - intros H. inversion H. subst.
    split; [split |]; [reflexivity | destruct d; reflexivity | reflexivity].
Qed.

(* ================================================================= *)
(* The machine.                                                       *)
(* ================================================================= *)

Inductive instr : Type :=
| INC (c : ctr)
| DEC (c : ctr) (j : nat)
| HALT
| CHECK (p : prop) (c : ctr)
| COMMIT (p : prop) (c : ctr)
| CERTIFY.

Definition cost (i : instr) : nat :=
  match i with
  | CHECK _ _ | COMMIT _ _ | CERTIFY => 1
  | _ => 0
  end.

Record core : Type := mkcore {
  ca : nat; cb : nat;
  va : nat; vb : nat;
  pc : nat;
  facts : list fact;
  chan : option fact;
  err : bool
}.

Definition val (k : core) (c : ctr) : nat :=
  match c with CA => ca k | CB => cb k end.
Definition ver (k : core) (c : ctr) : nat :=
  match c with CA => va k | CB => vb k end.

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

Definition fires (k : core) (i : instr) : bool :=
  match i with CERTIFY => certify_ok k | _ => false end.

Record state : Type := mkst { core_of : core; mu : nat; cert : bool }.

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

Lemma generic_start_clean : forall a b, clean_start (start a b).
Proof. intros. repeat split. Qed.

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

Fixpoint trace_of (n : nat) (P : list instr) (s : state) : list instr :=
  match n with
  | 0 => []
  | S m => match next_instr P (core_of s) with
           | None => []
           | Some i => i :: trace_of m P (exec s i)
           end
  end.

Lemma generic_run_app : forall l1 l2 s, run (l1 ++ l2) s = run l2 (run l1 s).
Proof. induction l1; intros; simpl; auto. Qed.

Lemma generic_run_snoc : forall l i s, run (l ++ [i]) s = exec (run l s) i.
Proof. intros. rewrite generic_run_app. reflexivity. Qed.

Lemma generic_total_cost_app : forall l1 l2,
  total_cost (l1 ++ l2) = total_cost l1 + total_cost l2.
Proof. induction l1; intros; simpl; [| rewrite IHl1]; lia. Qed.

Lemma generic_run_prog_halted : forall n P s, halted P (core_of s) -> run_prog n P s = s.
Proof.
  induction n; intros P s H; simpl; [reflexivity |].
  unfold step. unfold halted in H. rewrite H. apply IHn. exact H.
Qed.

Lemma generic_run_prog_trace : forall n P s, run_prog n P s = run (trace_of n P s) s.
Proof.
  induction n; intros P s; simpl; [reflexivity |].
  unfold step. destruct (next_instr P (core_of s)) eqn:H.
  - apply IHn.
  - apply generic_run_prog_halted. exact H.
Qed.

(* A trapped machine takes no further step. *)
Lemma generic_run_prog_trapped : forall n P s,
  err (core_of s) = true -> run_prog n P s = s.
Proof.
  induction n as [| n IH]; intros P s H; simpl; [reflexivity |].
  unfold step, next_instr. rewrite H. apply IH. exact H.
Qed.

(* ================================================================= *)
(* The toll, the ledger, the latch.                                   *)
(* ================================================================= *)

Theorem generic_mu_conservation_trace : forall tr s, mu (run tr s) = mu s + total_cost tr.
Proof. induction tr; intros; simpl; [lia | rewrite IHtr; simpl; lia]. Qed.

Theorem generic_mu_conservation_program : forall n P s,
  mu (run_prog n P s) = mu s + total_cost (trace_of n P s).
Proof. intros. rewrite generic_run_prog_trace. apply generic_mu_conservation_trace. Qed.

Theorem generic_cert_latch : forall s i, cert (exec s i) = cert s || fires (core_of s) i.
Proof. reflexivity. Qed.

Theorem generic_cert_permanent : forall s i, cert s = true -> cert (exec s i) = true.
Proof. intros s i H. simpl. rewrite H. reflexivity. Qed.

Theorem generic_only_certify_certifies : forall s i,
  cert s = false -> cert (exec s i) = true ->
  i = CERTIFY /\ certify_ok (core_of s) = true.
Proof.
  intros s i H0 H1. simpl in H1. rewrite H0 in H1. simpl in H1.
  destruct i; simpl in H1; try discriminate. auto.
Qed.

Theorem generic_a2 : forall s i, cert s = false -> cert (exec s i) = true -> cost i >= 1.
Proof.
  intros s i H0 H1. destruct (generic_only_certify_certifies s i H0 H1) as [-> _].
  simpl. lia.
Qed.

Theorem generic_nfi_floor : forall tr s,
  cert s = false -> cert (run tr s) = true -> total_cost tr >= 1.
Proof.
  induction tr as [| i rest IH]; intros s H0 H1; simpl in *; [congruence |].
  destruct (cert (exec s i)) eqn:Hm.
  - pose proof (generic_a2 s i H0 Hm). lia.
  - pose proof (IH _ Hm H1). lia.
Qed.

(* ================================================================= *)
(* Per-instruction facts about the substrate.                         *)
(* ================================================================= *)

Lemma generic_ver_write : forall k c n j d,
  ver (write k c n j) d = if ctr_eqb c d then S (ver k d) else ver k d.
Proof. intros k [] n j []; reflexivity. Qed.

Lemma generic_val_write : forall k c n j d,
  val (write k c n j) d = if ctr_eqb c d then n else val k d.
Proof. intros k [] n j []; reflexivity. Qed.

Lemma generic_facts_write : forall k c n j, facts (write k c n j) = facts k.
Proof. intros k [] n j; reflexivity. Qed.

Lemma generic_chan_write : forall k c n j, chan (write k c n j) = chan k.
Proof. intros k [] n j; reflexivity. Qed.

Lemma generic_ver_mono : forall k i c, ver k c <= ver (cexec k i) c.
Proof.
  intros k i c. unfold cexec. destruct (err k); [lia |].
  destruct i as [d | d j | | p d | p d |]; simpl.
  - rewrite generic_ver_write. destruct (ctr_eqb d c); lia.
  - destruct (val k d); [destruct c; simpl; lia |].
    rewrite generic_ver_write. destruct (ctr_eqb d c); lia.
  - lia.
  - destruct (check_ok k p d); destruct c; simpl; lia.
  - destruct (commit_ok k p d); destruct c; simpl; lia.
  - destruct (certify_ok k); destruct c; simpl; lia.
Qed.

Lemma generic_ver_same_val : forall k i c,
  ver (cexec k i) c = ver k c -> val (cexec k i) c = val k c.
Proof.
  intros k i c H. unfold cexec in *. destruct (err k); [reflexivity |].
  destruct i as [d | d j | | p d | p d |]; simpl in *.
  - rewrite generic_ver_write in H. rewrite generic_val_write.
    destruct (ctr_eqb d c); [lia | reflexivity].
  - destruct (val k d); [destruct c; reflexivity |].
    rewrite generic_ver_write in H. rewrite generic_val_write.
    destruct (ctr_eqb d c); [lia | reflexivity].
  - reflexivity.
  - destruct (check_ok k p d); destruct c; reflexivity.
  - destruct (commit_ok k p d); destruct c; reflexivity.
  - destruct (certify_ok k); destruct c; reflexivity.
Qed.

Lemma generic_ver_check : forall k p c d, ver (cexec k (CHECK p c)) d = ver k d.
Proof.
  intros. unfold cexec. destruct (err k); [reflexivity |].
  destruct (check_ok k p c); destruct d; reflexivity.
Qed.

Lemma generic_val_check : forall k p c d, val (cexec k (CHECK p c)) d = val k d.
Proof.
  intros. unfold cexec. destruct (err k); [reflexivity |].
  destruct (check_ok k p c); destruct d; reflexivity.
Qed.

Theorem generic_facts_step : forall k i f,
  In f (facts (cexec k i)) ->
  In f (facts k) \/
  (i = CHECK (f_prop f) (f_ctr f) /\ check_ok k (f_prop f) (f_ctr f) = true /\
   f = claim k (f_prop f) (f_ctr f)).
Proof.
  intros k i f H. unfold cexec in H. destruct (err k) eqn:He; [auto |].
  destruct i as [d | d j | | p d | p d |]; simpl in H.
  - rewrite generic_facts_write in H. auto.
  - destruct (val k d); simpl in H; [auto | rewrite generic_facts_write in H; auto].
  - auto.
  - destruct (check_ok k p d) eqn:Hc; simpl in H; [| auto].
    destruct H as [<- | H]; [right | auto]. simpl. auto.
  - destruct (commit_ok k p d); simpl in H; auto.
  - destruct (certify_ok k); simpl in H; auto.
Qed.

Theorem generic_facts_keep : forall k i f, In f (facts k) -> In f (facts (cexec k i)).
Proof.
  intros k i f H. unfold cexec. destruct (err k); [exact H |].
  destruct i as [d | d j | | p d | p d |]; simpl.
  - rewrite generic_facts_write. exact H.
  - destruct (val k d); simpl; [exact H | rewrite generic_facts_write; exact H].
  - exact H.
  - destruct (check_ok k p d); simpl; auto.
  - destruct (commit_ok k p d); simpl; auto.
  - destruct (certify_ok k); simpl; auto.
Qed.

Theorem generic_full_table_traps : forall k p c,
  fact_cap <= length (facts k) ->
  err (cexec k (CHECK p c)) = true /\ facts (cexec k (CHECK p c)) = facts k.
Proof.
  intros k p c H. unfold cexec. destruct (err k) eqn:He; [auto |].
  unfold check_ok. rewrite He.
  replace (Nat.ltb (length (facts k)) fact_cap) with false
    by (symmetry; apply Nat.ltb_ge; exact H).
  rewrite andb_false_r. auto.
Qed.

Theorem generic_facts_bounded_step : forall k i,
  length (facts k) <= fact_cap -> length (facts (cexec k i)) <= fact_cap.
Proof.
  intros k i H. unfold cexec. destruct (err k); [exact H |].
  destruct i as [d | d j | | p d | p d |]; simpl.
  - rewrite generic_facts_write. exact H.
  - destruct (val k d); simpl; [exact H | rewrite generic_facts_write; exact H].
  - exact H.
  - destruct (check_ok k p d) eqn:Hc; simpl; [| exact H].
    unfold check_ok in Hc. apply andb_true_iff in Hc as [_ Hc].
    apply Nat.ltb_lt in Hc. lia.
  - destruct (commit_ok k p d); simpl; exact H.
  - destruct (certify_ok k); simpl; exact H.
Qed.

Lemma generic_chan_step : forall k i,
  chan (cexec k i) = chan k \/
  exists p c, i = COMMIT p c /\ commit_ok k p c = true /\
              chan (cexec k i) = Some (claim k p c).
Proof.
  intros k i. unfold cexec. destruct (err k); [auto |].
  destruct i as [d | d j | | p d | p d |]; simpl.
  - rewrite generic_chan_write. auto.
  - destruct (val k d); simpl; [auto | rewrite generic_chan_write; auto].
  - auto.
  - destruct (check_ok k p d); simpl; auto.
  - destruct (commit_ok k p d) eqn:Hc; simpl; [right; eauto | auto].
  - destruct (certify_ok k); simpl; auto.
Qed.

Lemma generic_commit_ok_iff : forall k p c,
  commit_ok k p c = true <-> err k = false /\ In (claim k p c) (facts k).
Proof.
  intros. unfold commit_ok. rewrite andb_true_iff, negb_true_iff, existsb_exists.
  split.
  - intros [He [f [Hin Hf]]]. apply generic_fact_eqb_eq in Hf. subst. auto.
  - intros [He Hin]. split; [exact He |]. exists (claim k p c).
    split; [exact Hin | apply generic_fact_eqb_eq; reflexivity].
Qed.

Theorem generic_unearned_commit_traps : forall k p c,
  commit_ok k p c = false ->
  err (cexec k (COMMIT p c)) = true /\
  chan (cexec k (COMMIT p c)) = chan k /\ facts (cexec k (COMMIT p c)) = facts k.
Proof.
  intros k p c H. unfold cexec. destruct (err k) eqn:He; [auto |].
  rewrite H. auto.
Qed.

Theorem generic_uncommitted_certify_traps : forall s,
  certify_ok (core_of s) = false ->
  err (core_of (exec s CERTIFY)) = true /\ cert (exec s CERTIFY) = cert s.
Proof.
  intros [k m r] H. simpl in *. rewrite H, orb_false_r. unfold cexec.
  destruct (err k) eqn:He; [auto |]. rewrite H. auto.
Qed.

(* ================================================================= *)
(* Runs: versions only grow, equal version means equal value.         *)
(* ================================================================= *)

Lemma generic_ver_mono_run : forall l s c, ver (core_of s) c <= ver (core_of (run l s)) c.
Proof.
  induction l as [| i l IH]; intros s c; simpl; [lia |].
  pose proof (generic_ver_mono (core_of s) i c). pose proof (IH (exec s i) c). simpl in *. lia.
Qed.

Definition untouched (s : state) (mid : list instr) (c : ctr) : Prop :=
  forall t1 i t2, mid = t1 ++ i :: t2 ->
    let k := core_of (run t1 s) in
    ver (cexec k i) c = ver k c /\ val (cexec k i) c = val k c.

Lemma generic_untouched_of_ver : forall s mid c,
  ver (core_of (run mid s)) c = ver (core_of s) c -> untouched s mid c.
Proof.
  intros s mid c H t1 i t2 ->. simpl.
  rewrite generic_run_app in H. simpl in H.
  pose proof (generic_ver_mono_run t1 s c).
  pose proof (generic_ver_mono (core_of (run t1 s)) i c).
  pose proof (generic_ver_mono_run t2 (exec (run t1 s) i) c). simpl in *.
  assert (Hv : ver (cexec (core_of (run t1 s)) i) c = ver (core_of (run t1 s)) c) by lia.
  split; [exact Hv | apply generic_ver_same_val; exact Hv].
Qed.

(* ================================================================= *)
(* Checker soundness.                                                 *)
(* ================================================================= *)

Definition sound (k : core) : Prop :=
  forall f, In f (facts k) ->
    f_ver f <= ver k (f_ctr f) /\
    (f_ver f = ver k (f_ctr f) -> holds (f_prop f) (val k (f_ctr f))).

Lemma generic_sound_step : forall k i, sound k -> sound (cexec k i).
Proof.
  intros k i Hs f Hin.
  pose proof (generic_ver_mono k i (f_ctr f)) as Hm.
  destruct (generic_facts_step k i f Hin) as [Hold | [Hi [Hc Hf]]].
  - destruct (Hs f Hold) as [Hle Hlive]. split; [lia |].
    intro Heq. assert (Hv : ver (cexec k i) (f_ctr f) = ver k (f_ctr f)) by lia.
    rewrite (generic_ver_same_val k i _ Hv). apply Hlive. lia.
  - subst i. rewrite generic_ver_check, generic_val_check.
    rewrite Hf. simpl. split; [lia | intros _].
    unfold check_ok in Hc. apply andb_true_iff in Hc as [Hc _].
    apply andb_true_iff in Hc as [_ Hc]. apply eval_iff. exact Hc.
Qed.

Lemma generic_sound_run : forall tr s, sound (core_of s) -> sound (core_of (run tr s)).
Proof. induction tr; intros s H; simpl; [exact H | apply IHtr, generic_sound_step, H]. Qed.

Theorem generic_checker_soundness : forall s0 tr f,
  clean_start s0 ->
  let k := core_of (run tr s0) in
  In f (facts k) -> f_ver f = ver k (f_ctr f) -> holds (f_prop f) (val k (f_ctr f)).
Proof.
  intros s0 tr f [Hf _] k Hin Hv.
  assert (Hs0 : sound (core_of s0)) by (intros g Hg; rewrite Hf in Hg; destruct Hg).
  exact (proj2 (generic_sound_run tr s0 Hs0 f Hin) Hv).
Qed.

Corollary generic_committed_claim_holds : forall s0 tr p c,
  clean_start s0 ->
  commit_ok (core_of (run tr s0)) p c = true ->
  holds p (val (core_of (run tr s0)) c).
Proof.
  intros s0 tr p c H0 Hc. apply generic_commit_ok_iff in Hc as [_ Hin].
  exact (generic_checker_soundness s0 tr _ H0 Hin eq_refl).
Qed.

(* ================================================================= *)
(* No forging, over any run.                                          *)
(* ================================================================= *)

Definition earned (s0 : state) (tr : list instr) (f : fact) : Prop :=
  exists pre mid,
    tr = pre ++ CHECK (f_prop f) (f_ctr f) :: mid /\
    check_ok (core_of (run pre s0)) (f_prop f) (f_ctr f) = true /\
    f = claim (core_of (run pre s0)) (f_prop f) (f_ctr f) /\
    (f_ver f = ver (core_of (run tr s0)) (f_ctr f) ->
     untouched (run (pre ++ [CHECK (f_prop f) (f_ctr f)]) s0) mid (f_ctr f)).

Definition no_forgery (s0 : state) (tr : list instr) : Prop :=
  forall f, In f (facts (core_of (run tr s0))) -> earned s0 tr f.

Lemma generic_earned_intro : forall s0 pre mid f,
  check_ok (core_of (run pre s0)) (f_prop f) (f_ctr f) = true ->
  f = claim (core_of (run pre s0)) (f_prop f) (f_ctr f) ->
  earned s0 (pre ++ CHECK (f_prop f) (f_ctr f) :: mid) f.
Proof.
  intros s0 pre mid f Hc Hf. exists pre, mid.
  split; [reflexivity |]. split; [exact Hc |]. split; [exact Hf |].
  intro Hlive. apply generic_untouched_of_ver.
  replace (pre ++ CHECK (f_prop f) (f_ctr f) :: mid)
    with ((pre ++ [CHECK (f_prop f) (f_ctr f)]) ++ mid) in Hlive
    by (rewrite <- app_assoc; reflexivity).
  rewrite generic_run_app in Hlive. rewrite <- Hlive.
  rewrite generic_run_snoc. simpl. rewrite generic_ver_check.
  rewrite Hf at 1. reflexivity.
Qed.

Theorem generic_no_forging_step : forall s0 tr i,
  no_forgery s0 tr -> no_forgery s0 (tr ++ [i]).
Proof.
  intros s0 tr i Hnf f Hin. rewrite generic_run_snoc in Hin. simpl in Hin.
  destruct (generic_facts_step _ i f Hin) as [Hold | [Hi [Hc Hf]]].
  - destruct (Hnf f Hold) as [pre [mid [Htr [Hc [Hf _]]]]].
    rewrite Htr, <- app_assoc. simpl. apply generic_earned_intro; assumption.
  - subst i. apply generic_earned_intro; assumption.
Qed.

Theorem generic_no_forging : forall s0 tr, clean_start s0 -> no_forgery s0 tr.
Proof.
  intros s0 tr [Hf _]. induction tr as [| i tr IH] using rev_ind.
  - intros f Hin. simpl in Hin. rewrite Hf in Hin. destruct Hin.
  - apply generic_no_forging_step, IH.
Qed.

(* ================================================================= *)
(* Earned provenance.                                                 *)
(* ================================================================= *)

Theorem generic_earned_commitment_provenance : forall s0 pre p c,
  clean_start s0 ->
  commit_ok (core_of (run pre s0)) p c = true ->
  exists pre1 mid,
    pre = pre1 ++ CHECK p c :: mid /\
    check_ok (core_of (run pre1 s0)) p c = true /\
    cost (CHECK p c) >= 1 /\ cost (COMMIT p c) >= 1 /\
    ver (core_of (run pre1 s0)) c = ver (core_of (run pre s0)) c /\
    untouched (run (pre1 ++ [CHECK p c]) s0) mid c.
Proof.
  intros s0 pre p c H0 Hc. apply generic_commit_ok_iff in Hc as [_ Hin].
  destruct (generic_no_forging s0 pre H0 _ Hin) as [pre1 [mid [Htr [Hck [Hf Hlive]]]]].
  simpl in *. exists pre1, mid.
  split; [exact Htr |]. split; [exact Hck |].
  split; [simpl; lia |]. split; [simpl; lia |].
  split; [unfold claim in Hf; injection Hf as Hv; symmetry; exact Hv |].
  apply Hlive. reflexivity.
Qed.

Lemma generic_cert_first : forall s0 tr,
  cert s0 = false -> cert (run tr s0) = true ->
  exists pre post, tr = pre ++ CERTIFY :: post /\
    cert (run pre s0) = false /\ certify_ok (core_of (run pre s0)) = true.
Proof.
  intros s0 tr H0. induction tr as [| i tr IH] using rev_ind; intro H1.
  - simpl in H1. congruence.
  - rewrite generic_run_snoc in H1. destruct (cert (run tr s0)) eqn:Hc.
    + destruct (IH eq_refl) as [pre [post [-> Hrest]]].
      exists pre, (post ++ [i]). rewrite <- app_assoc. auto.
    + destruct (generic_only_certify_certifies _ i Hc H1) as [-> Hok].
      exists tr, []. auto.
Qed.

Lemma generic_chan_origin : forall s0 tr f,
  chan (core_of s0) = None -> chan (core_of (run tr s0)) = Some f ->
  exists pre1 p c mid, tr = pre1 ++ COMMIT p c :: mid /\
    commit_ok (core_of (run pre1 s0)) p c = true /\
    f = claim (core_of (run pre1 s0)) p c.
Proof.
  intros s0 tr f H0. induction tr as [| i tr IH] using rev_ind; intro H1.
  - simpl in H1. congruence.
  - rewrite generic_run_snoc in H1. simpl in H1.
    destruct (generic_chan_step (core_of (run tr s0)) i) as [Hs | [p [c [-> [Hok Hch]]]]].
    + rewrite Hs in H1. destruct (IH H1) as [pre1 [p [c [mid [-> Hrest]]]]].
      exists pre1, p, c, (mid ++ [i]). rewrite <- app_assoc. auto.
    + rewrite Hch in H1. injection H1 as <-. exists tr, p, c, []. auto.
Qed.

(* A raised flag was earned: CHECK, then COMMIT of the same claim at the
   same version with the counter untouched between, then CERTIFY. *)
Theorem generic_earned_certification_provenance : forall s0 tr,
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
  destruct (generic_cert_first s0 tr Hc0 H1) as [pre [post [-> [_ Hok]]]].
  pose proof Hok as Hset. unfold certify_ok in Hset.
  apply andb_true_iff in Hset as [_ Hset].
  destruct (chan (core_of (run pre s0))) as [f |] eqn:Hf; [| discriminate].
  destruct (generic_chan_origin s0 pre f Hch Hf) as [preC [p [c [mid2 [-> [Hcm _]]]]]].
  destruct (generic_earned_commitment_provenance s0 preC p c H0 Hcm)
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

Theorem generic_certified_run_min_cost : forall s0 tr,
  clean_start s0 -> cert (run tr s0) = true ->
  total_cost tr >= 3 /\ mu (run tr s0) >= mu s0 + 3.
Proof.
  intros s0 tr H0 H1.
  assert (Hc : total_cost tr >= 3).
  { destruct (generic_earned_certification_provenance s0 tr H0 H1)
      as [pre1 [p [c [mid1 [mid2 [post [-> _]]]]]]].
    rewrite generic_total_cost_app. simpl. rewrite generic_total_cost_app. simpl.
    rewrite generic_total_cost_app. simpl. lia. }
  split; [exact Hc | rewrite generic_mu_conservation_trace; lia].
Qed.

Corollary generic_program_certified_min_cost : forall n P a b,
  cert (run_prog n P (start a b)) = true -> mu (run_prog n P (start a b)) >= 3.
Proof.
  intros n P a b H. rewrite generic_run_prog_trace in *.
  apply (generic_certified_run_min_cost (start a b)) in H; [simpl in H; lia | apply generic_start_clean].
Qed.

(* ================================================================= *)
(* The three-instruction chain on one property.                       *)
(* ================================================================= *)

Lemma exec_check_pass : forall s p c,
  check_ok (core_of s) p c = true ->
  exec s (CHECK p c) =
  mkst (record_fact (core_of s) (claim (core_of s) p c)) (mu s + 1) (cert s).
Proof.
  intros [k m r] p c H. simpl in *.
  assert (He : err k = false)
    by (unfold check_ok in H; destruct (err k); [discriminate | reflexivity]).
  unfold exec, cexec. simpl. rewrite He, H. simpl. rewrite orb_false_r. reflexivity.
Qed.

Lemma exec_check_fail : forall s p c,
  err (core_of s) = false -> check_ok (core_of s) p c = false ->
  exec s (CHECK p c) = mkst (trap (core_of s)) (mu s + 1) (cert s).
Proof.
  intros [k m r] p c He H. simpl in *.
  unfold exec, cexec. simpl. rewrite He, H. simpl. rewrite orb_false_r. reflexivity.
Qed.

Lemma exec_commit_pass : forall s p c,
  commit_ok (core_of s) p c = true ->
  exec s (COMMIT p c) =
  mkst (commit_to (core_of s) (claim (core_of s) p c)) (mu s + 1) (cert s).
Proof.
  intros [k m r] p c H. simpl in *.
  assert (He : err k = false) by (apply generic_commit_ok_iff in H; apply H).
  unfold exec, cexec. simpl. rewrite He, H. simpl. rewrite orb_false_r. reflexivity.
Qed.

Definition chain (p : prop) (c : ctr) : list instr := [CHECK p c; COMMIT p c; CERTIFY].

(* From a start where p holds of counter c, the chain certifies and pays
   exactly the floor of 3. *)
Theorem chain_certifies : forall p c a b,
  holds p (val (start_core a b) c) ->
  cert (run_prog 4 (chain p c) (start a b)) = true /\
  mu (run_prog 4 (chain p c) (start a b)) = 3.
Proof.
  intros p c a b H. apply eval_iff in H.
  assert (Hck : check_ok (start_core a b) p c = true)
    by (unfold check_ok; rewrite H; reflexivity).
  set (P := chain p c).
  change (run_prog 4 P (start a b)) with (step P (step P (step P (step P (start a b))))).
  assert (E1 : step P (start a b) = exec (start a b) (CHECK p c)) by reflexivity.
  rewrite E1, (exec_check_pass (start a b) p c Hck).
  change (core_of (start a b)) with (start_core a b).
  set (k1 := record_fact (start_core a b) (claim (start_core a b) p c)).
  assert (Hcm : commit_ok k1 p c = true).
  { apply generic_commit_ok_iff. split; [reflexivity |]. left. destruct c; reflexivity. }
  set (s1 := mkst k1 (mu (start a b) + 1) (cert (start a b))).
  assert (E2 : step P s1 = exec s1 (COMMIT p c)) by reflexivity.
  rewrite E2, (exec_commit_pass s1 p c Hcm).
  split; reflexivity.
Qed.

(* From a start where p fails on counter c, the CHECK traps, and no number
   of further steps raises the flag. *)
Theorem chain_refused_forever : forall n p c a b,
  ~ holds p (val (start_core a b) c) ->
  cert (run_prog n (chain p c) (start a b)) = false /\
  (n >= 1 -> err (core_of (run_prog n (chain p c) (start a b))) = true).
Proof.
  intros n p c a b H.
  assert (He : eval p (val (start_core a b) c) = false)
    by (destruct (eval p _) eqn:E; [exfalso; apply H, eval_iff, E | reflexivity]).
  assert (Hck : check_ok (start_core a b) p c = false)
    by (unfold check_ok; rewrite He; reflexivity).
  destruct n as [| n]; [split; [reflexivity | lia] |].
  set (P := chain p c).
  change (run_prog (S n) P (start a b)) with (run_prog n P (step P (start a b))).
  assert (E1 : step P (start a b) = exec (start a b) (CHECK p c)) by reflexivity.
  rewrite E1, (exec_check_fail (start a b) p c eq_refl Hck).
  rewrite generic_run_prog_trapped by reflexivity.
  split; [reflexivity | intros _; reflexivity].
Qed.

(* So the chain certifies exactly when p holds of the start value. *)
Corollary chain_certifies_iff : forall p c a b,
  cert (run_prog 4 (chain p c) (start a b)) = true <-> holds p (val (start_core a b) c).
Proof.
  intros p c a b. split.
  - intro H1. apply eval_iff.
    destruct (eval p (val (start_core a b) c)) eqn:E; [reflexivity | exfalso].
    assert (Hn : ~ holds p (val (start_core a b) c))
      by (intro Hh; apply eval_iff in Hh; congruence).
    destruct (chain_refused_forever 4 p c a b Hn) as [H2 _]. congruence.
  - intro H. apply chain_certifies, H.
Qed.

End Generic.

(* ================================================================= *)
(* Instance 1: the property language of EarnedCore.v.                 *)
(* ================================================================= *)

Inductive cprop : Type :=
| PZero          (* the counter is 0      *)
| PEven          (* the counter is even   *)
| PGe (n : nat). (* the counter is >= n   *)

Definition ceval (p : cprop) (v : nat) : bool :=
  match p with
  | PZero => Nat.eqb v 0
  | PEven => Nat.even v
  | PGe n => Nat.leb n v
  end.

Definition cholds (p : cprop) (v : nat) : Prop :=
  match p with
  | PZero => v = 0
  | PEven => exists m, v = 2 * m
  | PGe n => n <= v
  end.

Lemma ceval_iff : forall p v, ceval p v = true <-> cholds p v.
Proof.
  intros [| | n] v; simpl.
  - apply Nat.eqb_eq.
  - rewrite Nat.even_spec. unfold Nat.Even. tauto.
  - apply Nat.leb_le.
Qed.

Definition cprop_eqb (p q : cprop) : bool :=
  match p, q with
  | PZero, PZero | PEven, PEven => true
  | PGe n, PGe m => Nat.eqb n m
  | _, _ => false
  end.

Lemma cprop_eqb_eq : forall p q, cprop_eqb p q = true <-> p = q.
Proof.
  intros [| | n] [| | m]; simpl; split; intro H; try discriminate; try reflexivity.
  - apply Nat.eqb_eq in H. subst. reflexivity.
  - injection H as ->. apply Nat.eqb_refl.
Qed.

Corollary core_earned_certification_provenance :
  forall (s0 : @state cprop) (tr : list (@instr cprop)),
  clean_start s0 -> cert (run cprop_eqb ceval tr s0) = true ->
  exists pre1 p c mid1 mid2 post,
    tr = pre1 ++ CHECK p c :: mid1 ++ COMMIT p c :: mid2 ++ CERTIFY :: post /\
    check_ok ceval (core_of (run cprop_eqb ceval pre1 s0)) p c = true /\
    commit_ok cprop_eqb
      (core_of (run cprop_eqb ceval (pre1 ++ CHECK p c :: mid1) s0)) p c = true /\
    certify_ok (core_of (run cprop_eqb ceval
      (pre1 ++ CHECK p c :: mid1 ++ COMMIT p c :: mid2) s0)) = true /\
    ver (core_of (run cprop_eqb ceval pre1 s0)) c
      = ver (core_of (run cprop_eqb ceval (pre1 ++ CHECK p c :: mid1) s0)) c /\
    untouched cprop_eqb ceval (run cprop_eqb ceval (pre1 ++ [CHECK p c]) s0) mid1 c.
Proof. exact (generic_earned_certification_provenance cprop_eqb cprop_eqb_eq ceval). Qed.

Corollary core_checker_soundness :
  forall (s0 : @state cprop) (tr : list (@instr cprop)) (f : @fact cprop),
  clean_start s0 ->
  let k := core_of (run cprop_eqb ceval tr s0) in
  In f (facts k) -> f_ver f = ver k (f_ctr f) -> cholds (f_prop f) (val k (f_ctr f)).
Proof. exact (generic_checker_soundness cprop_eqb ceval cholds ceval_iff). Qed.

Corollary core_no_forging : forall (s0 : @state cprop) (tr : list (@instr cprop)),
  clean_start s0 -> no_forgery cprop_eqb ceval s0 tr.
Proof. exact (generic_no_forging cprop_eqb ceval). Qed.

Corollary core_certified_run_min_cost :
  forall (s0 : @state cprop) (tr : list (@instr cprop)),
  clean_start s0 -> cert (run cprop_eqb ceval tr s0) = true ->
  total_cost tr >= 3 /\ mu (run cprop_eqb ceval tr s0) >= mu s0 + 3.
Proof. exact (generic_certified_run_min_cost cprop_eqb cprop_eqb_eq ceval). Qed.

(* The chain on "A is 0" certifies exactly from the starts with A = 0. *)
Corollary core_zero_chain_iff : forall a b,
  cert (run_prog cprop_eqb ceval 4 (chain PZero CA) (start a b)) = true <-> a = 0.
Proof.
  exact (fun a b => chain_certifies_iff cprop_eqb cprop_eqb_eq ceval cholds ceval_iff
                      PZero CA a b).
Qed.

(* ================================================================= *)
(* Instance 2: the same language plus "this counter is a sorted list". *)
(* ================================================================= *)

(* The list a counter value stands for. 0 is the empty list, and
   2^x * (2y + 1) is x :: decode y. The fuel argument is the value itself,
   which is always enough, since each round halves the value. *)
Fixpoint dec (fuel v acc : nat) : list nat :=
  match fuel with
  | 0 => []
  | S f =>
      match v with
      | 0 => []
      | S _ => if Nat.odd v then acc :: dec f (Nat.div2 v) 0
               else dec f (Nat.div2 v) (S acc)
      end
  end.

Definition decode (v : nat) : list nat := dec v v 0.

Fixpoint encode (l : list nat) : nat :=
  match l with [] => 0 | x :: t => 2 ^ x * (2 * encode t + 1) end.

Lemma dec_fuel : forall f1 f2 v acc, v <= f1 -> v <= f2 -> dec f1 v acc = dec f2 v acc.
Proof.
  induction f1 as [| f1 IH]; intros f2 v acc H1 H2.
  - assert (v = 0) as -> by lia. destruct f2; reflexivity.
  - destruct v as [| v']; [destruct f2; reflexivity |].
    destruct f2 as [| f2]; [lia |].
    assert (Hd : Nat.div2 (S v') < S v') by (apply Nat.lt_div2; lia).
    change (dec (S f1) (S v') acc) with
      (if Nat.odd (S v') then acc :: dec f1 (Nat.div2 (S v')) 0
       else dec f1 (Nat.div2 (S v')) (S acc)).
    change (dec (S f2) (S v') acc) with
      (if Nat.odd (S v') then acc :: dec f2 (Nat.div2 (S v')) 0
       else dec f2 (Nat.div2 (S v')) (S acc)).
    rewrite (IH f2 (Nat.div2 (S v')) 0) by lia.
    rewrite (IH f2 (Nat.div2 (S v')) (S acc)) by lia. reflexivity.
Qed.

Lemma dec_odd : forall y acc, dec (S (2 * y)) (S (2 * y)) acc = acc :: dec y y 0.
Proof.
  intros y acc.
  change (dec (S (2 * y)) (S (2 * y)) acc) with
    (if Nat.odd (S (2 * y)) then acc :: dec (2 * y) (Nat.div2 (S (2 * y))) 0
     else dec (2 * y) (Nat.div2 (S (2 * y))) (S acc)).
  replace (Nat.odd (S (2 * y))) with true
    by (replace (S (2 * y)) with (1 + 2 * y) by lia;
        rewrite Nat.odd_add_mul_2; reflexivity).
  rewrite Nat.div2_succ_double. f_equal. apply dec_fuel; lia.
Qed.

Lemma dec_even : forall v acc, 0 < v -> dec (2 * v) (2 * v) acc = dec v v (S acc).
Proof.
  intros v acc Hv. destruct (2 * v) as [| w] eqn:E; [lia |].
  change (dec (S w) (S w) acc) with
    (if Nat.odd (S w) then acc :: dec w (Nat.div2 (S w)) 0
     else dec w (Nat.div2 (S w)) (S acc)).
  rewrite <- E.
  replace (Nat.odd (2 * v)) with false
    by (replace (2 * v) with (0 + 2 * v) by lia;
        rewrite Nat.odd_add_mul_2; reflexivity).
  rewrite Nat.div2_double. apply dec_fuel; lia.
Qed.

Lemma dec_pow : forall x m acc, 0 < m ->
  dec (2 ^ x * m) (2 ^ x * m) acc = dec m m (x + acc).
Proof.
  induction x as [| x IH]; intros m acc Hm.
  - simpl. rewrite Nat.add_0_r. reflexivity.
  - assert (Hp : 0 < 2 ^ x) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
    replace (2 ^ S x * m) with (2 * (2 ^ x * m)) by (simpl; lia).
    rewrite dec_even by nia. rewrite IH by exact Hm. f_equal. lia.
Qed.

(* Every list of naturals is the reading of some counter value. *)
Theorem decode_encode : forall l, decode (encode l) = l.
Proof.
  induction l as [| x t IH]; [reflexivity |].
  unfold decode. change (encode (x :: t)) with (2 ^ x * (2 * encode t + 1)).
  rewrite dec_pow by lia. rewrite Nat.add_0_r.
  replace (2 * encode t + 1) with (S (2 * encode t)) by lia.
  rewrite dec_odd. f_equal. exact IH.
Qed.

(* The checker: every adjacent pair is in order. *)
Fixpoint sortedb (l : list nat) : bool :=
  match l with
  | x :: ((y :: _) as t) => Nat.leb x y && sortedb t
  | _ => true
  end.

Lemma sortedb_iff : forall l, sortedb l = true <-> Sorted le l.
Proof.
  intro l. rewrite Sorted_LocallySorted_iff.
  induction l as [| x t IH].
  - split; intros _; [constructor | reflexivity].
  - destruct t as [| y t'].
    + split; intros _; [constructor | reflexivity].
    + change (sortedb (x :: y :: t')) with (Nat.leb x y && sortedb (y :: t')).
      rewrite andb_true_iff, Nat.leb_le, IH. split.
      * intros [Hxy Ht]. constructor; assumption.
      * intro H. inversion H; subst. split; assumption.
Qed.

Inductive sprop : Type :=
| Base (p : cprop)   (* a property of instance 1        *)
| PSorted.           (* decode of the counter is sorted *)

Definition seval (p : sprop) (v : nat) : bool :=
  match p with
  | Base q => ceval q v
  | PSorted => sortedb (decode v)
  end.

Definition sholds (p : sprop) (v : nat) : Prop :=
  match p with
  | Base q => cholds q v
  | PSorted => Sorted le (decode v)
  end.

Lemma seval_iff : forall p v, seval p v = true <-> sholds p v.
Proof.
  intros [q |] v; simpl; [apply ceval_iff | apply sortedb_iff].
Qed.

Definition sprop_eqb (p q : sprop) : bool :=
  match p, q with
  | Base p', Base q' => cprop_eqb p' q'
  | PSorted, PSorted => true
  | _, _ => false
  end.

Lemma sprop_eqb_eq : forall p q, sprop_eqb p q = true <-> p = q.
Proof.
  intros [p' |] [q' |]; simpl; split; intro H; try discriminate; try reflexivity.
  - apply cprop_eqb_eq in H. subst. reflexivity.
  - injection H as ->. apply cprop_eqb_eq. reflexivity.
Qed.

Corollary sorted_earned_certification_provenance :
  forall (s0 : @state sprop) (tr : list (@instr sprop)),
  clean_start s0 -> cert (run sprop_eqb seval tr s0) = true ->
  exists pre1 p c mid1 mid2 post,
    tr = pre1 ++ CHECK p c :: mid1 ++ COMMIT p c :: mid2 ++ CERTIFY :: post /\
    check_ok seval (core_of (run sprop_eqb seval pre1 s0)) p c = true /\
    commit_ok sprop_eqb
      (core_of (run sprop_eqb seval (pre1 ++ CHECK p c :: mid1) s0)) p c = true /\
    certify_ok (core_of (run sprop_eqb seval
      (pre1 ++ CHECK p c :: mid1 ++ COMMIT p c :: mid2) s0)) = true /\
    ver (core_of (run sprop_eqb seval pre1 s0)) c
      = ver (core_of (run sprop_eqb seval (pre1 ++ CHECK p c :: mid1) s0)) c /\
    untouched sprop_eqb seval (run sprop_eqb seval (pre1 ++ [CHECK p c]) s0) mid1 c.
Proof. exact (generic_earned_certification_provenance sprop_eqb sprop_eqb_eq seval). Qed.

Corollary sorted_checker_soundness :
  forall (s0 : @state sprop) (tr : list (@instr sprop)) (f : @fact sprop),
  clean_start s0 ->
  let k := core_of (run sprop_eqb seval tr s0) in
  In f (facts k) -> f_ver f = ver k (f_ctr f) -> sholds (f_prop f) (val k (f_ctr f)).
Proof. exact (generic_checker_soundness sprop_eqb seval sholds seval_iff). Qed.

Corollary sorted_no_forging : forall (s0 : @state sprop) (tr : list (@instr sprop)),
  clean_start s0 -> no_forgery sprop_eqb seval s0 tr.
Proof. exact (generic_no_forging sprop_eqb seval). Qed.

Corollary sorted_certified_run_min_cost :
  forall (s0 : @state sprop) (tr : list (@instr sprop)),
  clean_start s0 -> cert (run sprop_eqb seval tr s0) = true ->
  total_cost tr >= 3 /\ mu (run sprop_eqb seval tr s0) >= mu s0 + 3.
Proof. exact (generic_certified_run_min_cost sprop_eqb sprop_eqb_eq seval). Qed.

(* A COMMIT of PSorted that would succeed means the counter's current value
   decodes to a sorted list. *)
Corollary sorted_committed_claim_holds :
  forall (s0 : @state sprop) (tr : list (@instr sprop)) c,
  clean_start s0 ->
  commit_ok sprop_eqb (core_of (run sprop_eqb seval tr s0)) PSorted c = true ->
  Sorted le (decode (val (core_of (run sprop_eqb seval tr s0)) c)).
Proof.
  intros s0 tr c H0 H.
  exact (generic_committed_claim_holds sprop_eqb sprop_eqb_eq seval sholds seval_iff
           s0 tr PSorted c H0 H).
Qed.

(* A raised flag on a run whose every COMMIT names PSorted on counter A was
   earned by a passing CHECK of PSorted on A, committed at the same version
   with A untouched between, and A's value at the CHECK decodes to a sorted
   list. *)
Corollary sorted_earned_provenance :
  forall (s0 : @state sprop) (tr : list (@instr sprop)),
  clean_start s0 ->
  (forall p c, In (COMMIT p c) tr -> p = PSorted /\ c = CA) ->
  cert (run sprop_eqb seval tr s0) = true ->
  exists pre1 mid1 mid2 post,
    tr = pre1 ++ CHECK PSorted CA :: mid1 ++ COMMIT PSorted CA :: mid2
           ++ CERTIFY :: post /\
    check_ok seval (core_of (run sprop_eqb seval pre1 s0)) PSorted CA = true /\
    Sorted le (decode (val (core_of (run sprop_eqb seval pre1 s0)) CA)) /\
    commit_ok sprop_eqb
      (core_of (run sprop_eqb seval (pre1 ++ CHECK PSorted CA :: mid1) s0))
      PSorted CA = true /\
    ver (core_of (run sprop_eqb seval pre1 s0)) CA
      = ver (core_of (run sprop_eqb seval (pre1 ++ CHECK PSorted CA :: mid1) s0)) CA /\
    untouched sprop_eqb seval
      (run sprop_eqb seval (pre1 ++ [CHECK PSorted CA]) s0) mid1 CA.
Proof.
  intros s0 tr H0 Honly H1.
  destruct (sorted_earned_certification_provenance s0 tr H0 H1)
    as [pre1 [p [c [mid1 [mid2 [post [Htr [Hck [Hcm [_ [Hv Hun]]]]]]]]]]].
  assert (Hin : In (COMMIT p c) tr).
  { rewrite Htr. apply in_or_app. right. right. apply in_or_app. right. left.
    reflexivity. }
  destruct (Honly p c Hin) as [-> ->].
  exists pre1, mid1, mid2, post.
  split; [exact Htr |]. split; [exact Hck |].
  split; [| split; [exact Hcm | split; [exact Hv | exact Hun]]].
  unfold check_ok in Hck. apply andb_true_iff in Hck as [Hck _].
  apply andb_true_iff in Hck as [_ Hck]. apply sortedb_iff. exact Hck.
Qed.

(* The program: check that counter A is a sorted list, commit, certify. *)
Definition sorted_run : list (@instr sprop) := chain PSorted CA.

(* It certifies exactly from the starts whose A decodes to a sorted list,
   paying exactly 3, and from every other start it is refused forever. *)
Theorem sorted_run_certifies_iff : forall a b,
  cert (run_prog sprop_eqb seval 4 sorted_run (start a b)) = true <->
  Sorted le (decode a).
Proof.
  exact (fun a b => chain_certifies_iff sprop_eqb sprop_eqb_eq seval sholds seval_iff
                      PSorted CA a b).
Qed.

Theorem sorted_run_certifies : forall a b,
  Sorted le (decode a) ->
  cert (run_prog sprop_eqb seval 4 sorted_run (start a b)) = true /\
  mu (run_prog sprop_eqb seval 4 sorted_run (start a b)) = 3.
Proof.
  intros a b H.
  exact (chain_certifies sprop_eqb sprop_eqb_eq seval sholds seval_iff PSorted CA a b H).
Qed.

Theorem sorted_run_refused_forever : forall n a b,
  ~ Sorted le (decode a) ->
  cert (run_prog sprop_eqb seval n sorted_run (start a b)) = false.
Proof.
  intros n a b H.
  exact (proj1 (chain_refused_forever sprop_eqb seval sholds seval_iff n PSorted CA a b H)).
Qed.

(* Concrete starts. 18 = 2^1 * 9, 9 = 2 * 4 + 1, 4 = 2^2 * 1, so 18
   decodes to [1; 2]. 20 = 2^2 * 5, 5 = 2 * 2 + 1, 2 = 2^1 * 1, so 20
   decodes to [2; 1]. *)
Theorem sorted_demo_certifies :
  decode 18 = [1; 2] /\ encode [1; 2] = 18 /\
  cert (run_prog sprop_eqb seval 4 sorted_run (start 18 0)) = true /\
  mu (run_prog sprop_eqb seval 4 sorted_run (start 18 0)) = 3.
Proof. vm_compute. auto. Qed.

Theorem sorted_demo_refused_forever :
  decode 20 = [2; 1] /\ encode [2; 1] = 20 /\
  forall n, cert (run_prog sprop_eqb seval n sorted_run (start 20 0)) = false.
Proof.
  split; [vm_compute; reflexivity |]. split; [vm_compute; reflexivity |].
  intro n. apply sorted_run_refused_forever.
  intro H. apply sortedb_iff in H. vm_compute in H. discriminate H.
Qed.

(* ================================================================= *)
(* Assumption audit. Every line must print                            *)
(* "Closed under the global context".                                 *)
(* ================================================================= *)

Print Assumptions generic_earned_certification_provenance.
Print Assumptions generic_earned_commitment_provenance.
Print Assumptions generic_checker_soundness.
Print Assumptions generic_committed_claim_holds.
Print Assumptions generic_no_forging_step.
Print Assumptions generic_no_forging.
Print Assumptions generic_certified_run_min_cost.
Print Assumptions generic_program_certified_min_cost.
Print Assumptions generic_nfi_floor.
Print Assumptions generic_only_certify_certifies.
Print Assumptions chain_certifies.
Print Assumptions chain_refused_forever.
Print Assumptions chain_certifies_iff.
Print Assumptions core_earned_certification_provenance.
Print Assumptions core_checker_soundness.
Print Assumptions core_no_forging.
Print Assumptions core_certified_run_min_cost.
Print Assumptions core_zero_chain_iff.
Print Assumptions decode_encode.
Print Assumptions sortedb_iff.
Print Assumptions sorted_earned_certification_provenance.
Print Assumptions sorted_checker_soundness.
Print Assumptions sorted_no_forging.
Print Assumptions sorted_certified_run_min_cost.
Print Assumptions sorted_committed_claim_holds.
Print Assumptions sorted_earned_provenance.
Print Assumptions sorted_run_certifies_iff.
Print Assumptions sorted_run_certifies.
Print Assumptions sorted_run_refused_forever.
Print Assumptions sorted_demo_certifies.
Print Assumptions sorted_demo_refused_forever.
