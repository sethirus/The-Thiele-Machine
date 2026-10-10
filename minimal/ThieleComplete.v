(** ThieleComplete.v: what it takes for a machine to be Thiele-complete.

    The weak notion. A Thiele machine is a certification system: states,
    moves, a step, a cost per move, a yes/no reading (the record), and the
    toll: a step that turns the reading from no to yes costs at least 1.
    Read that way, "Thiele-complete" meant a Thiele machine whose base is
    Turing-universal. That notion is nearly empty: a two-counter machine
    that charges 1 for every move is a Thiele machine for ANY reading,
    because every move pays the toll whether or not it certifies anything
    [clock_weakly_thiele_complete, latch_clock_weakly_thiele_complete].
    A machine that never raises its reading is one too, vacuously
    [silent_weakly_thiele_complete].

    The strong notion, thiele_complete, ties the record to certification.
    A machine is Thiele-complete when its moves can be read as base moves
    and three record moves, CHECK (claim), COMMIT (claim) and CERTIFY, over
    a type of claims with a meaning on states, a checker, a notion of "the
    thing the claim is about is unchanged", a set of clean starts and a
    ledger, such that four clauses hold.

      (a) Universal base. Every two-counter instruction has a base move
          that acts on a window of the state exactly as the instruction
          acts on a two-counter configuration, from every live state, and
          keeps the state live. Every two-counter start (1, (a, b)) has a
          clean, live state showing it. Base moves never change the record,
          and the record, once up, stays up.
      (b) Earned record. A clean start has the record down. Every run from
          a clean start that ends with the record up contains a passing
          CHECK of some claim, then a COMMIT of the same claim with the
          thing the claim is about unchanged at every state in between,
          then a CERTIFY that is the move raising the record. A passing
          check means its claim holds of the state it checked, and a claim
          that holds keeps holding while the thing it is about is
          unchanged.
      (c) Exact toll. Base moves cost 0, each record move costs exactly 1,
          and the ledger grows by the cost of each move, so the ledger
          counts exactly the record moves.
      (d) Non-vacuity. Some claim is true at some clean start and false at
          another, and the bare chain CHECK, COMMIT, CERTIFY on that claim
          raises the record from a clean start exactly when the claim holds
          there.

    Over a fixed claim language. In thiele_interface the claims, their
    meanings and "unchanged" are fields beside the checker, so a reading
    could take "the checker says yes" as the meaning and meet checker
    soundness for free. thiele_complete_over M L fixes them first: a claim
    language L (claim_language) carries the claims, an exact equality test,
    the meaning of each claim on states, "unchanged", and the fact that a
    meaning that holds keeps holding while its subject is unchanged. An
    interface over L (lang_interface) supplies only the base, the kinds,
    the checker with its soundness proof against L's meanings, the clean
    states and the ledger, and the four clauses are asked of the interface
    that results.

    What is proved (every result closed under the global context):

      0. Over a fixed language. Thiele-complete over some L implies
         Thiele-complete, so every consequence below carries over
         [thiele_complete_over_complete]; a reading whose claims have an
         exact equality test loses nothing [thiele_complete_with_over]; and
         over L, a certified run from a clean start contains a passing
         CHECK of a claim of L and a COMMIT of it, with L's own meaning
         holding at both [over_certificate_means]. The small machine over
         its property language, whose meanings EarnedCore.v states without
         the checker [earned_core_thiele_complete_over], the generic machine
         over any property language, whose claim language is built without
         the checker [earned_generic_thiele_complete_over], and the sorted
         instance [sorted_machine_thiele_complete_over] meet it; so do the
         two universal hosts (UniversalRun.v, UniversalPRun.v).

      1. Consequences of the definition, for every machine. A
         Thiele-complete machine is a Thiele machine with a universal base
         [thiele_complete_is_weak]; its base runs every two-counter program
         step for step, with halting matched [base_runs_every_program,
         base_halting_correspondence]; the ledger counts the record moves
         [ledger_counts_record_moves]; a certificate costs at least 3
         [certificate_costs_three]; the committed claim holds when it is
         committed [committed_claim_holds]; some check fails on a false
         claim, and some run from a clean start certifies
         [check_can_fail, some_run_certifies]; on a run from a clean
         start, the move that raises the record is a CERTIFY
         [only_certify_raises]; and every move costs 0 or 1
         [complete_costs_at_most_one].
      2. The small machine of EarnedCore.v is Thiele-complete
         [earned_core_thiele_complete]. Its reference model agrees with
         EarnedCore's two-counter machine, so its universality is the one
         halting_correspondence states [reference_agrees].
      3. The small machine with any property language that has an exact
         checker and a property true of one counter value and false of
         another is Thiele-complete [earned_generic_thiele_complete], and
         so is the instance with "this counter is a sorted list"
         [sorted_machine_thiele_complete].
      4. The clock fails. A Thiele-complete machine has a move of cost 0
         [complete_has_free_move], so the two-counter machine charging 1
         per move, with any reading, or with any latch on its
         configuration as the record, is weakly Thiele-complete and not
         Thiele-complete [clock_not_thiele_complete,
         latch_clock_not_thiele_complete].
      5. The other clauses do work too. A two-counter machine with a free
         base, a ledger, and one paid move TICK that raises a latch meets
         (a) and (c) and is weakly Thiele-complete, but fails (b), because
         no record that one move can raise is earned
         [paid_latch_meets_base_and_toll, one_move_record_excluded,
         paid_latch_not_thiele_complete]. A machine whose record never
         rises meets (a), (b) and (c) and fails (d)
         [silent_meets_base_record_toll, silent_not_thiele_complete].

    Dependencies: Coq standard library, EarnedCore.v and EarnedGeneric.v.
    No axioms, no Admitted.                                                *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose, as in
   EarnedCore.v: this file imports nothing outside the standard library,
   EarnedCore.v and EarnedGeneric.v, so it re-checks from a clean checkout.
   Its link to the abstract record (every Thiele-complete machine as a
   CertificationSystem with the trace cost floor, and the small machine's
   instance agreeing with the one in EarnedCoreLinks.v) lives in
   EarnedGenericLinks.v. *)

From Coq Require Import List Arith Lia Bool.
From Coq Require Import Sorting.Sorted.
Import ListNotations.
Require Minimal.EarnedCore.
Require Minimal.EarnedGeneric.
Module E := Minimal.EarnedCore.
Module G := Minimal.EarnedGeneric.

(* ================================================================= *)
(* The two-counter machine, the reference for universality.          *)
(* ================================================================= *)

(* Two registers, increment, and decrement-or-fall-through. Minsky
   (1961, 1967) showed this runs every Turing machine. *)
Inductive reg : Type := RA | RB.
Inductive cm_instr : Type := CINC (r : reg) | CDEC (r : reg) (j : nat).

(* (program counter, (register A, register B)), 1-based program counter. *)
Definition cm_conf : Type := (nat * (nat * nat))%type.

Definition cm_get (x : cm_conf) (r : reg) : nat :=
  match r with RA => fst (snd x) | RB => snd (snd x) end.
Definition cm_set (x : cm_conf) (r : reg) (n j : nat) : cm_conf :=
  match r with RA => (j, (n, snd (snd x))) | RB => (j, (fst (snd x), n)) end.

(* What one instruction does to a configuration. *)
Definition cm_exec (i : cm_instr) (x : cm_conf) : cm_conf :=
  match i with
  | CINC r => cm_set x r (S (cm_get x r)) (S (fst x))
  | CDEC r j =>
      match cm_get x r with
      | 0 => (S (fst x), snd x)
      | S n => cm_set x r n j
      end
  end.

Definition cm_fetch (P : list cm_instr) (n : nat) : option cm_instr :=
  match n with 0 => None | S m => nth_error P m end.

(* A program counter with no instruction is a stop. *)
Definition cm_step (P : list cm_instr) (x : cm_conf) : option cm_conf :=
  match cm_fetch P (fst x) with None => None | Some i => Some (cm_exec i x) end.

Fixpoint cm_run (n : nat) (P : list cm_instr) (x : cm_conf) : cm_conf :=
  match n with
  | 0 => x
  | S m => match cm_step P x with None => x | Some y => cm_run m P y end
  end.

(* ================================================================= *)
(* Machines and the weak notion.                                      *)
(* ================================================================= *)

Record machine : Type := mk_machine {
  m_state : Type;
  m_move : Type;
  m_step : m_state -> m_move -> m_state;
  m_cost : m_move -> nat;
  m_record : m_state -> bool
}.

Fixpoint run (M : machine) (tr : list (m_move M)) (s : m_state M) : m_state M :=
  match tr with [] => s | m :: rest => run M rest (m_step M s m) end.

Lemma run_app : forall M l1 l2 s, run M (l1 ++ l2) s = run M l2 (run M l1 s).
Proof. induction l1; intros; simpl; auto. Qed.

(* Closes an equation between two groupings of the same list. *)
Ltac list_eq := repeat first [rewrite <- app_assoc | progress simpl]; reflexivity.

(* The toll: a step that turns the record from no to yes costs at least 1. *)
Definition thiele_machine (M : machine) : Prop :=
  forall s m, m_record M s = false -> m_record M (m_step M s m) = true ->
    m_cost M m >= 1.

(* The certification-system record of the book, field for field. *)
Record CertificationSystem := mk_cert_system {
  cs_state : Type;
  cs_instr : Type;
  cs_step : cs_state -> cs_instr -> cs_state;
  cs_cost : cs_instr -> nat;
  cs_cert : cs_state -> bool;
  cs_cert_costs : forall s i, cs_cert s = false -> cs_cert (cs_step s i) = true ->
    cs_cost i >= 1
}.

Definition as_cert_system (M : machine) (H : thiele_machine M) : CertificationSystem :=
  mk_cert_system (m_state M) (m_move M) (m_step M) (m_cost M) (m_record M) H.

(* A universal base: each two-counter instruction compiles to one move that
   acts on a window of the state exactly as the instruction acts on a
   configuration, from every live state, and keeps the state live. *)
Record universal_base (M : machine) : Type := mk_ub {
  ub_window : m_state M -> cm_conf;
  ub_live : m_state M -> Prop;
  ub_compile : cm_instr -> m_move M;
  ub_load : nat -> nat -> m_state M;
  ub_load_window : forall a b, ub_window (ub_load a b) = (1, (a, b));
  ub_load_live : forall a b, ub_live (ub_load a b);
  ub_sim : forall s i, ub_live s ->
    ub_window (m_step M s (ub_compile i)) = cm_exec i (ub_window s) /\
    ub_live (m_step M s (ub_compile i))
}.

Arguments ub_window {M} u s.
Arguments ub_live {M} u s.
Arguments ub_compile {M} u i.
Arguments ub_load {M} u a b.
Arguments ub_load_window {M} u a b.
Arguments ub_load_live {M} u a b.
Arguments ub_sim {M} u s i _.

(* The weak notion: a Thiele machine whose base is universal. *)
Definition weakly_thiele_complete (M : machine) : Prop :=
  thiele_machine M /\ inhabited (universal_base M).

(* Running a two-counter program on the base: look up the instruction at
   the window's program counter and take its compiled move. The lookup
   does no computation of its own. *)
Fixpoint prog_run {M : machine} (U : universal_base M) (n : nat)
  (P : list cm_instr) (s : m_state M) : m_state M :=
  match n with
  | 0 => s
  | S k => match cm_fetch P (fst (ub_window U s)) with
           | None => s
           | Some i => prog_run U k P (m_step M s (ub_compile U i))
           end
  end.

Definition prog_halted {M : machine} (U : universal_base M) (P : list cm_instr)
  (s : m_state M) : Prop := cm_fetch P (fst (ub_window U s)) = None.

Theorem base_runs_every_program : forall M (U : universal_base M) n P s,
  ub_live U s ->
  ub_window U (prog_run U n P s) = cm_run n P (ub_window U s) /\
  ub_live U (prog_run U n P s).
Proof.
  intros M U n. induction n as [| n IH]; intros P s Hl; simpl; [auto |].
  unfold cm_step. destruct (cm_fetch P (fst (ub_window U s))) as [i |] eqn:Hf.
  - destruct (ub_sim U s i Hl) as [Hw Hl'].
    rewrite <- Hw. apply IH. exact Hl'.
  - auto.
Qed.

(* A two-counter program halts from (a, b) iff the base, started on the
   state loaded with (a, b), reaches a stop. *)
Theorem base_halting_correspondence : forall M (U : universal_base M) P a b,
  (exists n, cm_step P (cm_run n P (1, (a, b))) = None) <->
  (exists n, prog_halted U P (prog_run U n P (ub_load U a b))).
Proof.
  intros M U P a b.
  assert (Hrun : forall n, ub_window U (prog_run U n P (ub_load U a b))
                           = cm_run n P (1, (a, b))).
  { intro n. rewrite <- (ub_load_window U a b).
    apply base_runs_every_program, ub_load_live. }
  unfold prog_halted, cm_step. split; intros [n Hn]; exists n.
  - rewrite Hrun. destruct (cm_fetch P (fst (cm_run n P (1, (a, b))))); congruence.
  - rewrite Hrun in Hn. rewrite Hn. reflexivity.
Qed.

(* ================================================================= *)
(* The strong notion.                                                 *)
(* ================================================================= *)

(* How a move reads: a base move, or one of the three record moves. *)
Inductive kind (C : Type) : Type :=
| KBase
| KCheck (c : C)
| KCommit (c : C)
| KCertify.

Arguments KBase {C}.
Arguments KCheck {C} c.
Arguments KCommit {C} c.
Arguments KCertify {C}.

(* The reading of a machine as a certifier: its universal base, its
   claims, what each claim means of a state, its checker, when the thing a
   claim is about counts as unchanged, its clean starts, and its ledger. *)
Record thiele_interface (M : machine) : Type := mk_ti {
  ti_base : universal_base M;
  ti_claim : Type;
  ti_kind : m_move M -> kind ti_claim;
  ti_meaning : ti_claim -> m_state M -> Prop;
  ti_check : m_state M -> ti_claim -> bool;
  ti_same : ti_claim -> m_state M -> m_state M -> Prop;
  ti_clean : m_state M -> Prop;
  ti_ledger : m_state M -> nat
}.

Arguments ti_base {M} t.
Arguments ti_claim {M} t.
Arguments ti_kind {M} t m.
Arguments ti_meaning {M} t c s.
Arguments ti_check {M} t s c.
Arguments ti_same {M} t c s s'.
Arguments ti_clean {M} t s.
Arguments ti_ledger {M} t s.

Section Clauses.

Variable M : machine.
Variable I : thiele_interface M.

Definition load (a b : nat) : m_state M := ub_load (ti_base I) a b.

(* (a) Universal base, and the base leaves the record alone. *)
Definition universal_base_clause : Prop :=
  (forall i, ti_kind I (ub_compile (ti_base I) i) = KBase) /\
  (forall a b, ti_clean I (load a b)) /\
  (forall s m, ti_kind I m = KBase -> m_record M (m_step M s m) = m_record M s) /\
  (forall s m, m_record M s = true -> m_record M (m_step M s m) = true).

(* The earned chain inside a run tr from s0: a passing CHECK of claim c,
   then a COMMIT of c with the thing c is about unchanged at every state
   in between, then the CERTIFY that raises the record. *)
Definition earned_chain (s0 : m_state M) (tr : list (m_move M)) : Prop :=
  exists pre c chk mid1 cmt mid2 crt post,
    tr = pre ++ chk :: mid1 ++ cmt :: mid2 ++ crt :: post /\
    ti_kind I chk = KCheck c /\ ti_kind I cmt = KCommit c /\ ti_kind I crt = KCertify /\
    ti_check I (run M pre s0) c = true /\
    (forall t1 t2, mid1 = t1 ++ t2 ->
       ti_same I c (run M pre s0) (run M (pre ++ chk :: t1) s0)) /\
    m_record M (run M (pre ++ chk :: mid1 ++ cmt :: mid2) s0) = false /\
    m_record M (run M (pre ++ chk :: mid1 ++ cmt :: mid2 ++ [crt]) s0) = true.

(* (b) Earned record, with checker soundness. *)
Definition earned_record_clause : Prop :=
  (forall s, ti_clean I s -> m_record M s = false) /\
  (forall s0 tr, ti_clean I s0 -> m_record M (run M tr s0) = true -> earned_chain s0 tr) /\
  (forall s c, ti_check I s c = true -> ti_meaning I c s) /\
  (forall c s s', ti_same I c s s' -> ti_meaning I c s -> ti_meaning I c s').

Definition record_move (m : m_move M) : nat :=
  match ti_kind I m with KBase => 0 | _ => 1 end.

Fixpoint record_moves (tr : list (m_move M)) : nat :=
  match tr with [] => 0 | m :: rest => record_move m + record_moves rest end.

(* (c) Exact toll. *)
Definition exact_toll_clause : Prop :=
  (forall m, m_cost M m = record_move m) /\
  (forall s m, ti_ledger I (m_step M s m) = ti_ledger I s + m_cost M m).

(* (d) Non-vacuity: the record follows a claim that can fail. *)
Definition non_vacuity_clause : Prop :=
  exists c chk cmt crt,
    ti_kind I chk = KCheck c /\ ti_kind I cmt = KCommit c /\ ti_kind I crt = KCertify /\
    (forall a b, m_record M (run M [chk; cmt; crt] (load a b)) = true <->
                 ti_meaning I c (load a b)) /\
    (exists a b, ti_meaning I c (load a b)) /\
    (exists a b, ~ ti_meaning I c (load a b)).

Definition thiele_complete_with : Prop :=
  universal_base_clause /\ earned_record_clause /\ exact_toll_clause /\ non_vacuity_clause.

End Clauses.

Arguments load {M} I a b.
Arguments universal_base_clause {M} I.
Arguments earned_chain {M} I s0 tr.
Arguments earned_record_clause {M} I.
Arguments record_move {M} I m.
Arguments record_moves {M} I tr.
Arguments exact_toll_clause {M} I.
Arguments non_vacuity_clause {M} I.
Arguments thiele_complete_with {M} I.

(* THE DEFINITION. *)
Definition thiele_complete (M : machine) : Prop :=
  exists I : thiele_interface M, thiele_complete_with I.

(* ================================================================= *)
(* The strong notion over a claim language fixed in advance.          *)
(* ================================================================= *)

(* In thiele_interface the claims, their meanings and "unchanged" are
   fields of the same interface that supplies the checker, so a reading
   could take "the checker says yes" as the meaning and pass checker
   soundness for free. A claim language fixes those three things first:
   its claims, an exact equality test on them, what each claim means of a
   state, when the thing a claim is about counts as unchanged, and the
   fact that a meaning that holds keeps holding while its subject is
   unchanged. *)
Record claim_language (M : machine) : Type := mk_cl {
  cl_claim : Type;
  cl_eqb : cl_claim -> cl_claim -> bool;
  cl_eqb_spec : forall c d, cl_eqb c d = true <-> c = d;
  cl_meaning : cl_claim -> m_state M -> Prop;
  cl_same : cl_claim -> m_state M -> m_state M -> Prop;
  cl_same_keeps : forall c s s', cl_same c s s' -> cl_meaning c s -> cl_meaning c s'
}.

Arguments cl_claim {M} _.
Arguments cl_eqb {M} _ _ _.
Arguments cl_eqb_spec {M} _ _ _.
Arguments cl_meaning {M} _ _ _.
Arguments cl_same {M} _ _ _ _.
Arguments cl_same_keeps {M} _ _ _ _ _ _.

(* An interface over a fixed language L supplies the rest and nothing
   about what the claims mean: a universal base, a kind for each move over
   L's claims, a checker, a proof that the checker is sound for L's
   meanings, the clean states and the ledger. *)
Record lang_interface (M : machine) (L : claim_language M) : Type := mk_lang {
  lang_base : universal_base M;
  lang_kind : m_move M -> kind (cl_claim L);
  lang_check : m_state M -> cl_claim L -> bool;
  lang_sound : forall s c, lang_check s c = true -> cl_meaning L c s;
  lang_clean : m_state M -> Prop;
  lang_ledger : m_state M -> nat
}.

Arguments lang_base {M L} _.
Arguments lang_kind {M L} _ _.
Arguments lang_check {M L} _ _ _.
Arguments lang_sound {M L} _ _ _ _.
Arguments lang_clean {M L} _ _.
Arguments lang_ledger {M L} _ _.

(* The full interface an interface over L determines: claims, meanings and
   "unchanged" are L's own. *)
Definition lang_ti {M : machine} {L : claim_language M} (J : lang_interface M L)
  : thiele_interface M :=
  mk_ti M (lang_base J) (cl_claim L) (lang_kind J) (cl_meaning L) (lang_check J) (cl_same L)
    (lang_clean J) (lang_ledger J).

(* THE DEFINITION OVER A FIXED LANGUAGE. *)
Definition thiele_complete_over (M : machine) (L : claim_language M) : Prop :=
  exists J : lang_interface M L, thiele_complete_with (lang_ti J).

(* Every consequence of thiele_complete carries over. *)
Theorem thiele_complete_over_complete : forall M (L : claim_language M),
  thiele_complete_over M L -> thiele_complete M.
Proof. intros M L [J HJ]. exists (lang_ti J). exact HJ. Qed.

(* Nothing is lost for a reading whose claims have an exact equality test:
   its own claims, meanings and "unchanged" form a language, and the
   machine is Thiele-complete over it. So the strengthening is in naming
   the language before the interface; a theorem over a language written
   down independently of the checker says what that language says. *)
Definition language_of {M : machine} (I : thiele_interface M)
  (eqb : ti_claim I -> ti_claim I -> bool) (Heqb : forall c d, eqb c d = true <-> c = d)
  (Hkeep : forall c s s', ti_same I c s s' -> ti_meaning I c s -> ti_meaning I c s')
  : claim_language M :=
  mk_cl M (ti_claim I) eqb Heqb (ti_meaning I) (ti_same I) Hkeep.

Theorem thiele_complete_with_over : forall M (I : thiele_interface M)
  (eqb : ti_claim I -> ti_claim I -> bool) (Heqb : forall c d, eqb c d = true <-> c = d)
  (Hkeep : forall c s s', ti_same I c s s' -> ti_meaning I c s -> ti_meaning I c s'),
  thiele_complete_with I -> thiele_complete_over M (language_of I eqb Heqb Hkeep).
Proof.
  intros M I eqb Heqb Hkeep HC.
  pose proof HC as [_ [[_ [_ [Hsound _]]] _]].
  exists (mk_lang M (language_of I eqb Heqb Hkeep)
            (ti_base I) (ti_kind I) (ti_check I) Hsound (ti_clean I) (ti_ledger I)).
  destruct I. exact HC.
Qed.

(* What a certificate means over L: on every run from a clean start that
   ends with the record up, a claim of L was checked and then committed,
   and L's own meaning of that claim held at the check and at the
   commit. *)
Theorem over_certificate_means : forall M (L : claim_language M),
  thiele_complete_over M L ->
  exists J : lang_interface M L,
    thiele_complete_with (lang_ti J) /\
    forall s0 tr, lang_clean J s0 -> m_record M (run M tr s0) = true ->
    exists pre c chk mid1 cmt rest,
      tr = pre ++ chk :: mid1 ++ cmt :: rest /\
      lang_kind J chk = KCheck c /\ lang_kind J cmt = KCommit c /\
      lang_check J (run M pre s0) c = true /\
      cl_meaning L c (run M pre s0) /\ cl_meaning L c (run M (pre ++ chk :: mid1) s0).
Proof.
  intros M L [J HJ]. exists J. split; [exact HJ |]. intros s0 tr H0 H1.
  pose proof HJ as [_ [[_ [Hchain _]] _]].
  destruct (Hchain s0 tr H0 H1)
    as [pre [c [chk [mid1 [cmt [mid2 [crt [post
         [Htr [Hk1 [Hk2 [_ [Hck [Hsame _]]]]]]]]]]]]]].
  exists pre, c, chk, mid1, cmt, (mid2 ++ crt :: post).
  split; [exact Htr |]. split; [exact Hk1 |]. split; [exact Hk2 |].
  split; [exact Hck |].
  assert (Hm : cl_meaning L c (run M pre s0)) by (apply (lang_sound J), Hck).
  split; [exact Hm |].
  apply (cl_same_keeps L c (run M pre s0));
    [apply (Hsame mid1 []); rewrite app_nil_r; reflexivity | exact Hm].
Qed.

(* ================================================================= *)
(* 1. Consequences of the definition, for every machine.             *)
(* ================================================================= *)

Theorem thiele_complete_is_weak : forall M,
  thiele_complete M -> weakly_thiele_complete M.
Proof.
  intros M [I [[_ [_ [Hbase _]]] [_ [[Hcost _] _]]]]. split.
  - intros s m H0 H1. rewrite Hcost. unfold record_move.
    destruct (ti_kind I m) eqn:Hk; try lia.
    rewrite (Hbase s m Hk) in H1. congruence.
  - exact (inhabits (ti_base I)).
Qed.

Lemma record_moves_app : forall M (I : thiele_interface M) l1 l2,
  record_moves I (l1 ++ l2) = record_moves I l1 + record_moves I l2.
Proof. induction l1; intros; simpl; [| rewrite IHl1]; lia. Qed.

Theorem ledger_counts_record_moves : forall M (I : thiele_interface M),
  exact_toll_clause I ->
  forall tr s, ti_ledger I (run M tr s) = ti_ledger I s + record_moves I tr.
Proof.
  intros M I [Hcost Hled] tr. induction tr as [| m tr IH]; intro s; simpl; [lia |].
  rewrite IH, Hled, Hcost. lia.
Qed.

Theorem certificate_costs_three : forall M (I : thiele_interface M),
  thiele_complete_with I ->
  forall s0 tr, ti_clean I s0 -> m_record M (run M tr s0) = true ->
    record_moves I tr >= 3 /\ ti_ledger I (run M tr s0) >= ti_ledger I s0 + 3.
Proof.
  intros M I [_ [[_ [Hchain _]] [Htoll _]]] s0 tr H0 H1.
  destruct (Hchain s0 tr H0 H1)
    as [pre [c [chk [mid1 [cmt [mid2 [crt [post [Htr [Hk1 [Hk2 [Hk3 _]]]]]]]]]]]].
  assert (Hm : record_moves I tr >= 3).
  { rewrite Htr. repeat (rewrite record_moves_app; simpl).
    unfold record_move. rewrite Hk1, Hk2, Hk3. lia. }
  split; [exact Hm |]. rewrite (ledger_counts_record_moves M I Htoll). lia.
Qed.

(* The claim a certificate stands on held when it was checked and still
   held when it was committed. *)
Theorem committed_claim_holds : forall M (I : thiele_interface M),
  thiele_complete_with I ->
  forall s0 tr, ti_clean I s0 -> m_record M (run M tr s0) = true ->
  exists pre c chk mid1 cmt rest,
    tr = pre ++ chk :: mid1 ++ cmt :: rest /\
    ti_kind I chk = KCheck c /\ ti_kind I cmt = KCommit c /\
    ti_meaning I c (run M pre s0) /\ ti_meaning I c (run M (pre ++ chk :: mid1) s0).
Proof.
  intros M I [_ [[_ [Hchain [Hsound Hresp]]] _]] s0 tr H0 H1.
  destruct (Hchain s0 tr H0 H1)
    as [pre [c [chk [mid1 [cmt [mid2 [crt [post
         [Htr [Hk1 [Hk2 [_ [Hck [Hsame _]]]]]]]]]]]]]].
  exists pre, c, chk, mid1, cmt, (mid2 ++ crt :: post).
  split; [exact Htr |]. split; [exact Hk1 |]. split; [exact Hk2 |].
  assert (Hm : ti_meaning I c (run M pre s0)) by (apply Hsound; exact Hck).
  split; [exact Hm |].
  apply (Hresp c (run M pre s0)); [apply (Hsame mid1 []); rewrite app_nil_r; reflexivity
                                  | exact Hm].
Qed.

(* Some check fails, on a claim that is false at a clean start. *)
Theorem check_can_fail : forall M (I : thiele_interface M),
  thiele_complete_with I ->
  exists a b chk c,
    ti_kind I chk = KCheck c /\
    ti_check I (load I a b) c = false /\ ~ ti_meaning I c (load I a b).
Proof.
  intros M I [_ [[_ [_ [Hsound _]]] [_ Hnv]]].
  destruct Hnv as [c [chk [_ [_ [Hk1 [_ [_ [_ [_ [a [b Hno]]]]]]]]]]].
  exists a, b, chk, c. split; [exact Hk1 |]. split; [| exact Hno].
  destruct (ti_check I (load I a b) c) eqn:E; [| reflexivity].
  exfalso. apply Hno, Hsound, E.
Qed.

Theorem some_run_certifies : forall M (I : thiele_interface M),
  thiele_complete_with I ->
  exists a b tr, ti_clean I (load I a b) /\ m_record M (run M tr (load I a b)) = true.
Proof.
  intros M I [[_ [Hclean _]] [_ [_ Hnv]]].
  destruct Hnv as [c [chk [cmt [crt [_ [_ [_ [Hiff [[a [b Hyes]] _]]]]]]]]].
  exists a, b, [chk; cmt; crt]. split; [apply Hclean |]. apply Hiff, Hyes.
Qed.

(* The move that raises the record, on any run from a clean start, is a
   CERTIFY. *)
Theorem only_certify_raises : forall M (I : thiele_interface M),
  thiele_complete_with I ->
  forall s0 tr m, ti_clean I s0 ->
    m_record M (run M tr s0) = false ->
    m_record M (m_step M (run M tr s0) m) = true ->
    ti_kind I m = KCertify.
Proof.
  intros M I [[_ [_ [_ Hperm]]] [[_ [Hchain _]] _]] s0 tr m H0 Hdown Hup.
  assert (Hstay : forall l s, m_record M s = true -> m_record M (run M l s) = true)
    by (induction l; intros; simpl; auto).
  assert (Hrun : m_record M (run M (tr ++ [m]) s0) = true)
    by (rewrite run_app; exact Hup).
  destruct (Hchain s0 (tr ++ [m]) H0 Hrun)
    as [pre [c [chk [mid1 [cmt [mid2 [crt [post
         [Htr [_ [_ [Hk3 [_ [_ [Hbefore Hafter]]]]]]]]]]]]]]].
  set (A := pre ++ chk :: mid1 ++ cmt :: mid2) in *.
  assert (HA : pre ++ chk :: mid1 ++ cmt :: mid2 ++ crt :: post = A ++ crt :: post)
    by (unfold A; list_eq).
  assert (HB : pre ++ chk :: mid1 ++ cmt :: mid2 ++ [crt] = A ++ [crt])
    by (unfold A; list_eq).
  rewrite HA in Htr. rewrite HB in Hafter.
  induction post as [| x post' _] using rev_ind.
  - apply app_inj_tail in Htr as [_ ->]. exact Hk3.
  - exfalso.
    replace (A ++ crt :: post' ++ [x]) with ((A ++ crt :: post') ++ [x]) in Htr
      by list_eq.
    apply app_inj_tail in Htr as [Htr _].
    rewrite Htr in Hdown.
    replace (A ++ crt :: post') with ((A ++ [crt]) ++ post') in Hdown by list_eq.
    rewrite run_app, (Hstay post' _ Hafter) in Hdown. discriminate.
Qed.

(* Every move of a Thiele-complete machine costs 0 or 1. *)
(* SAFE: short on purpose: the bound is read off the exact-toll clause by cases on the kind of the move. *)
Theorem complete_costs_at_most_one : forall M,
  thiele_complete M -> forall m : m_move M, m_cost M m <= 1.
Proof.
  intros M [I [_ [_ [[Hcost _] _]]]] m. rewrite Hcost. unfold record_move.
  destruct (ti_kind I m); lia.
Qed.

(* ================================================================= *)
(* 4 and 5. What the definition rules out.                            *)
(* ================================================================= *)

(* A Thiele-complete machine has a move that costs nothing. *)
Theorem complete_has_free_move : forall M,
  thiele_complete M -> exists m : m_move M, m_cost M m = 0.
Proof.
  intros M [I [[Hk _] [_ [[Hcost _] _]]]].
  exists (ub_compile (ti_base I) (CINC RA)). rewrite Hcost.
  unfold record_move. rewrite Hk. reflexivity.
Qed.

(* No record that a single move can raise from every state is earned. *)
Theorem one_move_record_excluded : forall M,
  (exists m : m_move M, forall s, m_record M (m_step M s m) = true) ->
  ~ thiele_complete M.
Proof.
  intros M [m Hm] [I [[_ [Hclean _]] [[_ [Hchain _]] _]]].
  destruct (Hchain (load I 0 0) [m] (Hclean 0 0) (Hm _))
    as [pre [c [chk [mid1 [cmt [mid2 [crt [post [Htr _]]]]]]]]].
  apply (f_equal (@length _)) in Htr. simpl in Htr.
  rewrite !app_length in Htr. simpl in Htr. rewrite app_length in Htr. simpl in Htr.
  lia.
Qed.

(* A record that never rises is not Thiele-complete. *)
Theorem never_certifies_excluded : forall M,
  (forall s, m_record M s = false) -> ~ thiele_complete M.
Proof.
  intros M Hno [I [_ [_ [_ Hnv]]]].
  destruct Hnv as [c [chk [cmt [crt [_ [_ [_ [Hiff [[a [b Hyes]] _]]]]]]]]].
  apply Hiff in Hyes. rewrite Hno in Hyes. discriminate.
Qed.

(* The clock: the two-counter machine itself, every move costing 1, and
   ANY reading of its configuration as the record. *)
Definition clock (rd : cm_conf -> bool) : machine :=
  mk_machine cm_conf cm_instr (fun x i => cm_exec i x) (fun _ => 1) rd.

Definition clock_base (rd : cm_conf -> bool) : universal_base (clock rd) :=
  mk_ub (clock rd) (fun x => x) (fun _ => True) (fun i => i) (fun a b => (1, (a, b)))
    (fun a b => eq_refl) (fun a b => I) (fun s i _ => conj eq_refl I).

(* SAFE: short on purpose: every clock move costs 1 so the toll is arithmetic; the base is clock_base. *)
Theorem clock_weakly_thiele_complete : forall rd,
  weakly_thiele_complete (clock rd).
Proof.
  intro rd. split; [| exact (inhabits (clock_base rd))].
  intros s m _ _. simpl. lia.
Qed.

Definition clock_cert_system (rd : cm_conf -> bool) : CertificationSystem :=
  as_cert_system (clock rd) (proj1 (clock_weakly_thiele_complete rd)).

(* SAFE: short on purpose: a Thiele-complete machine has a free move (complete_has_free_move) and every clock move costs 1. *)
Theorem clock_not_thiele_complete : forall rd, ~ thiele_complete (clock rd).
Proof.
  intros rd H. destruct (complete_has_free_move _ H) as [m Hm].
  simpl in Hm. discriminate.
Qed.

(* The latch clock: the same machine with a flag that latches whenever a
   chosen test lt of the configuration comes out yes, for instance "the
   program counter has reached line 2". The record is the flag. *)
Definition latch_clock (lt : cm_conf -> bool) : machine :=
  mk_machine (cm_conf * bool) cm_instr
    (fun s i => (cm_exec i (fst s), snd s || lt (cm_exec i (fst s))))
    (fun _ => 1) snd.

Definition latch_clock_base (lt : cm_conf -> bool) : universal_base (latch_clock lt) :=
  mk_ub (latch_clock lt) fst (fun _ => True) (fun i => i)
    (fun a b => ((1, (a, b)), false))
    (fun a b => eq_refl) (fun a b => I) (fun s i _ => conj eq_refl I).

(* SAFE: short on purpose: every move costs 1 so the toll is arithmetic; the base is latch_clock_base. *)
Theorem latch_clock_weakly_thiele_complete : forall lt,
  weakly_thiele_complete (latch_clock lt).
Proof.
  intro lt. split; [| exact (inhabits (latch_clock_base lt))].
  intros s m _ _. simpl. lia.
Qed.

(* SAFE: short on purpose: a Thiele-complete machine has a free move (complete_has_free_move) and every move costs 1. *)
Theorem latch_clock_not_thiele_complete : forall lt, ~ thiele_complete (latch_clock lt).
Proof.
  intros lt H. destruct (complete_has_free_move _ H) as [m Hm].
  simpl in Hm. discriminate.
Qed.

(* The paid latch: a free two-counter base, a ledger, and one move TICK
   that costs 1 and raises the flag. It has a universal base and an exact
   toll; what it lacks is an earned record. *)
Inductive pl_move : Type := PL_BASE (i : cm_instr) | PL_TICK.

Definition pl_cost (m : pl_move) : nat :=
  match m with PL_BASE _ => 0 | PL_TICK => 1 end.

Definition pl_step (s : cm_conf * bool * nat) (m : pl_move) : cm_conf * bool * nat :=
  match s with
  | (x, f, l) =>
      match m with
      | PL_BASE i => (cm_exec i x, f, l)
      | PL_TICK => (x, true, S l)
      end
  end.

Definition paid_latch : machine :=
  mk_machine (cm_conf * bool * nat) pl_move pl_step pl_cost (fun s => snd (fst s)).

Definition paid_latch_base : universal_base paid_latch :=
  mk_ub paid_latch (fun s => fst (fst s)) (fun _ => True) PL_BASE
    (fun a b => ((1, (a, b)), false, 0))
    (fun a b => eq_refl) (fun a b => I)
    (fun s i _ => match s with (x, f, l) => conj eq_refl I end).

(* SAFE: short on purpose: only TICK raises the flag and it costs 1; the base is paid_latch_base. *)
Theorem paid_latch_weakly_thiele_complete : weakly_thiele_complete paid_latch.
Proof.
  split; [| exact (inhabits paid_latch_base)].
  intros [[x f] l] [i |] H0 H1; simpl in *; [congruence | lia].
Qed.

(* One reading of its moves meets (a) and (c): TICK as CERTIFY. *)
Definition paid_latch_interface : thiele_interface paid_latch :=
  mk_ti paid_latch paid_latch_base unit
    (fun m => match m with PL_BASE _ => KBase | PL_TICK => KCertify end)
    (fun _ _ => True) (fun _ _ => true) (fun _ _ _ => True)
    (fun s => snd (fst s) = false) (fun s => snd s).

Theorem paid_latch_meets_base_and_toll :
  universal_base_clause paid_latch_interface /\ exact_toll_clause paid_latch_interface.
Proof.
  split; [split; [| split; [| split]] | split].
  - intro i. reflexivity.
  - intros a b. reflexivity.
  - intros [[x f] l] [i |] Hk; simpl in *; [reflexivity | discriminate].
  - intros [[x f] l] [i |] H; simpl in *; [exact H | reflexivity].
  - intros [i |]; reflexivity.
  - intros [[x f] l] [i |]; simpl; lia.
Qed.

(* SAFE: short on purpose: reduces to one_move_record_excluded, proved above. *)
Theorem paid_latch_not_thiele_complete : ~ thiele_complete paid_latch.
Proof.
  apply one_move_record_excluded. exists PL_TICK.
  intros [[x f] l]. reflexivity.
Qed.

(* The silent machine: a free two-counter base and a record that never
   rises. It meets (a), (b) and (c) with nothing to certify. *)
Definition silent : machine :=
  mk_machine cm_conf cm_instr (fun x i => cm_exec i x) (fun _ => 0) (fun _ => false).

Definition silent_base : universal_base silent :=
  mk_ub silent (fun x => x) (fun _ => True) (fun i => i) (fun a b => (1, (a, b)))
    (fun a b => eq_refl) (fun a b => I) (fun s i _ => conj eq_refl I).

Definition silent_interface : thiele_interface silent :=
  mk_ti silent silent_base unit (fun _ => KBase)
    (fun _ _ => True) (fun _ _ => true) (fun _ _ _ => True)
    (fun _ => True) (fun _ => 0).

(* SAFE: short on purpose: no move raises the record, so the toll premise is refuted at once; the base is silent_base. *)
Theorem silent_weakly_thiele_complete : weakly_thiele_complete silent.
Proof.
  split; [| exact (inhabits silent_base)]. intros s m _ H. discriminate.
Qed.

Theorem silent_meets_base_record_toll :
  universal_base_clause silent_interface /\ earned_record_clause silent_interface /\
  exact_toll_clause silent_interface.
Proof.
  split; [| split].
  - repeat split; intros; reflexivity || discriminate.
  - split; [intros; reflexivity |]. split; [intros s0 tr _ H; discriminate |].
    split; intros; exact I.
  - split; intros; reflexivity.
Qed.

Theorem silent_not_thiele_complete : ~ thiele_complete silent.
Proof. apply never_certifies_excluded. intro s. reflexivity. Qed.

(* ================================================================= *)
(* 2. The small machine of EarnedCore.v is Thiele-complete.           *)
(* ================================================================= *)

Definition earned_machine : machine :=
  mk_machine E.state E.instr E.exec E.cost E.cert.

Lemma run_earned : forall tr s, run earned_machine tr s = E.run tr s.
Proof. induction tr; intros; simpl; auto. Qed.

Definition ctr_of (r : reg) : E.ctr := match r with RA => E.CA | RB => E.CB end.

(* Each two-counter instruction is the small machine's own INC or DEC. *)
Definition earned_compile (i : cm_instr) : E.instr :=
  match i with CINC r => E.INC (ctr_of r) | CDEC r j => E.DEC (ctr_of r) j end.

Lemma earned_sim : forall (s : E.state) i, E.err (E.core_of s) = false ->
  E.window (E.core_of (E.exec s (earned_compile i))) = cm_exec i (E.window (E.core_of s)) /\
  E.err (E.core_of (E.exec s (earned_compile i))) = false.
Proof.
  intros [k m r] i He. simpl in *. unfold E.cexec. rewrite He.
  destruct i as [[|] | [|] j]; simpl.
  - auto.
  - auto.
  - destruct (E.ca k) eqn:Ha; unfold E.window, E.goto; simpl; rewrite ?Ha; auto.
  - destruct (E.cb k) eqn:Hb; unfold E.window, E.goto; simpl; rewrite ?Hb; auto.
Qed.

(* The window is the counter-machine view (pc, (A, B)). Live means the
   trap latch is down. The loaded state is the small machine's start a b. *)
Definition earned_base : universal_base earned_machine :=
  mk_ub earned_machine (fun s => E.window (E.core_of s))
    (fun s => E.err (E.core_of s) = false) earned_compile E.start
    (fun a b => eq_refl) (fun a b => eq_refl) earned_sim.

Definition earned_kind (i : E.instr) : kind (E.prop * E.ctr) :=
  match i with
  | E.CHECK p c => KCheck (p, c)
  | E.COMMIT p c => KCommit (p, c)
  | E.CERTIFY => KCertify
  | _ => KBase
  end.

(* A claim is a property and a counter. It means the property holds of the
   counter's value; the checker is CHECK's own test; the thing a claim is
   about is unchanged when the counter's version and value are. *)
Definition earned_interface : thiele_interface earned_machine :=
  mk_ti earned_machine earned_base (E.prop * E.ctr) earned_kind
    (fun pc s => E.holds (fst pc) (E.val (E.core_of s) (snd pc)))
    (fun s pc => E.check_ok (E.core_of s) (fst pc) (snd pc))
    (fun pc s t => E.ver (E.core_of s) (snd pc) = E.ver (E.core_of t) (snd pc) /\
                   E.val (E.core_of s) (snd pc) = E.val (E.core_of t) (snd pc))
    E.clean_start E.mu.

(* An untouched stretch leaves the counter's version and value as they
   were, at every point inside it. *)
Lemma untouched_prefix : forall s mid c, E.untouched s mid c ->
  forall t1 t2, mid = t1 ++ t2 ->
  E.ver (E.core_of (E.run t1 s)) c = E.ver (E.core_of s) c /\
  E.val (E.core_of (E.run t1 s)) c = E.val (E.core_of s) c.
Proof.
  intros s mid c Hu t1. induction t1 as [| i t1 IH] using rev_ind; intros t2 Hmid;
    [simpl; auto |].
  destruct (IH (i :: t2)) as [Hv Hw]; [rewrite Hmid, <- app_assoc; reflexivity |].
  destruct (Hu t1 i t2) as [Hv' Hw']; [rewrite Hmid, <- app_assoc; reflexivity |].
  rewrite E.run_snoc, E.base_blind. rewrite Hv', Hw'. auto.
Qed.

Lemma earned_chain_holds : forall s0 tr,
  E.clean_start s0 -> E.cert (E.run tr s0) = true ->
  earned_chain earned_interface s0 tr.
Proof.
  intros s0 tr H0 H1. pose proof H0 as [_ [Hch Hc0]].
  destruct (E.cert_first s0 tr Hc0 H1) as [pre [post [Htr [Hpre Hok]]]].
  pose proof Hok as Hset. unfold E.certify_ok in Hset.
  apply andb_true_iff in Hset as [_ Hset].
  destruct (E.chan (E.core_of (E.run pre s0))) as [f |] eqn:Hf; [| discriminate].
  destruct (E.chan_origin s0 pre f Hch Hf) as [preC [p [c [mid2 [HpreC [Hcm _]]]]]].
  destruct (E.earned_commitment_provenance s0 preC p c H0 Hcm)
    as [pre1 [mid1 [Hpre1 [Hck [_ [_ [_ Hun]]]]]]].
  assert (Hlist : pre1 ++ E.CHECK p c :: mid1 ++ E.COMMIT p c :: mid2 = pre)
    by (rewrite HpreC, Hpre1; list_eq).
  exists pre1, (p, c), (E.CHECK p c), mid1, (E.COMMIT p c), mid2, E.CERTIFY, post.
  split; [rewrite Htr, <- Hlist; list_eq |].
  split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
  split; [rewrite run_earned; exact Hck |].
  split.
  { intros t1 t2 Hm. rewrite !run_earned. simpl.
    replace (pre1 ++ E.CHECK p c :: t1) with ((pre1 ++ [E.CHECK p c]) ++ t1)
      by (rewrite <- app_assoc; reflexivity).
    rewrite E.run_app. destruct (untouched_prefix _ _ _ Hun t1 t2 Hm) as [Hv Hw].
    rewrite Hv, Hw, E.run_snoc, E.base_blind, E.ver_check, E.val_check.
    split; reflexivity. }
  assert (Hl2 : pre1 ++ E.CHECK p c :: mid1 ++ E.COMMIT p c :: mid2 ++ [E.CERTIFY]
                = pre ++ [E.CERTIFY]) by (rewrite <- Hlist; list_eq).
  assert (Hup : E.cert (E.run (pre ++ [E.CERTIFY]) s0) = true)
    by (rewrite E.run_snoc; simpl; rewrite Hpre; exact Hok).
  rewrite <- Hl2 in Hup. rewrite <- Hlist in Hpre.
  split; rewrite run_earned; assumption.
Qed.

Lemma earned_core_complete_with : thiele_complete_with earned_interface.
Proof.
  split; [| split; [| split]].
  - split; [intros [[|] | [|] j]; reflexivity |].
    split; [intros a b; apply E.start_clean |]. split.
    + intros s m Hk. destruct m; simpl in Hk; try discriminate; simpl;
        apply orb_false_r.
    + intros s m H. apply E.cert_permanent, H.
  - split; [intros s [_ [_ H]]; exact H |]. split.
    + intros s0 tr H0 H1. apply earned_chain_holds; [exact H0 |].
      rewrite <- run_earned. exact H1.
    + split.
      * intros s [p c] H. simpl in *. unfold E.check_ok in H.
        apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [_ H].
        apply E.eval_iff, H.
      * intros [p c] s t [_ Hw] H. simpl in *. rewrite <- Hw. exact H.
  - split; [intros []; reflexivity | intros s m; apply E.mu_conservation].
  - exists (E.PZero, E.CA), (E.CHECK E.PZero E.CA), (E.COMMIT E.PZero E.CA), E.CERTIFY.
    split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
    split; [| split; [exists 0, 0; reflexivity | exists 1, 0; simpl; intro H; discriminate H]].
    intros a b. destruct a as [| a]; simpl; split; intro H;
      try reflexivity; try discriminate H.
Qed.

Theorem earned_core_thiele_complete : thiele_complete earned_machine.
Proof. exists earned_interface. exact earned_core_complete_with. Qed.

(* The small machine's claim language, written down before any interface.
   A claim is a property and a counter. It means the property holds of the
   counter's value, by E.holds, which EarnedCore.v states without the
   checker. The thing it is about is unchanged when the counter's version
   and value are. Claims are equal when property and counter are. *)
Definition earned_claim_eqb (x y : E.prop * E.ctr) : bool :=
  E.prop_eqb (fst x) (fst y) && E.ctr_eqb (snd x) (snd y).

Lemma earned_claim_eqb_spec : forall x y, earned_claim_eqb x y = true <-> x = y.
Proof.
  intros [p c] [q d]. unfold earned_claim_eqb. simpl. rewrite andb_true_iff. split.
  - intros [Hp Hc].
    assert (p = q) by (destruct p, q; simpl in Hp; try discriminate; try reflexivity;
                       apply Nat.eqb_eq in Hp; subst; reflexivity).
    assert (c = d) by (destruct c, d; simpl in Hc; try discriminate; reflexivity).
    subst. reflexivity.
  - intro H. inversion H; subst.
    split; [destruct q; simpl; try reflexivity; apply Nat.eqb_refl | destruct d; reflexivity].
Qed.

Lemma earned_same_keeps : forall (pc : E.prop * E.ctr) (s t : E.state),
  E.ver (E.core_of s) (snd pc) = E.ver (E.core_of t) (snd pc) /\
  E.val (E.core_of s) (snd pc) = E.val (E.core_of t) (snd pc) ->
  E.holds (fst pc) (E.val (E.core_of s) (snd pc)) ->
  E.holds (fst pc) (E.val (E.core_of t) (snd pc)).
Proof. intros pc s t [_ Hw] H. rewrite <- Hw. exact H. Qed.

Definition earned_language : claim_language earned_machine :=
  mk_cl earned_machine (E.prop * E.ctr) earned_claim_eqb earned_claim_eqb_spec
    (fun pc s => E.holds (fst pc) (E.val (E.core_of s) (snd pc)))
    (fun pc s t => E.ver (E.core_of s) (snd pc) = E.ver (E.core_of t) (snd pc) /\
                   E.val (E.core_of s) (snd pc) = E.val (E.core_of t) (snd pc))
    earned_same_keeps.

(* CHECK's own test is sound for those meanings. *)
Lemma earned_check_sound : forall (s : E.state) (pc : E.prop * E.ctr),
  E.check_ok (E.core_of s) (fst pc) (snd pc) = true ->
  E.holds (fst pc) (E.val (E.core_of s) (snd pc)).
Proof.
  intros s [p c] H. simpl in *. unfold E.check_ok in H.
  apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [_ H].
  apply E.eval_iff, H.
Qed.

Definition earned_li : lang_interface earned_machine earned_language :=
  mk_lang earned_machine earned_language earned_base earned_kind
    (fun s pc => E.check_ok (E.core_of s) (fst pc) (snd pc)) earned_check_sound
    E.clean_start E.mu.

(* The small machine is Thiele-complete over its own property language. *)
Theorem earned_core_thiele_complete_over : thiele_complete_over earned_machine earned_language.
Proof. exists earned_li. exact earned_core_complete_with. Qed.

(* The reference model here and the two-counter machine of EarnedCore.v
   agree, so the universality above is the one halting_correspondence
   states there. *)
Definition earned_minsky (i : cm_instr) : E.minsky :=
  match i with CINC r => E.MINC (ctr_of r) | CDEC r j => E.MDEC (ctr_of r) j end.

Lemma reference_step_agrees : forall P x,
  cm_step P x = E.mstep (map earned_minsky P) x.
Proof.
  intros P [pc [a b]].
  assert (Hf : cm_fetch P pc = E.fetch P pc) by reflexivity.
  unfold cm_step, E.mstep. cbn [fst]. rewrite Hf, E.fetch_map.
  destruct (E.fetch P pc) as [[[|] | [|] j] |]; simpl; try reflexivity.
  - destruct a; reflexivity.
  - destruct b; reflexivity.
Qed.

Theorem reference_agrees : forall n P x,
  cm_run n P x = E.mrun n (map earned_minsky P) x.
Proof.
  induction n as [| n IH]; intros P x; simpl; [reflexivity |].
  rewrite reference_step_agrees.
  destruct (E.mstep (map earned_minsky P) x); [apply IH | reflexivity].
Qed.

Theorem earned_core_runs_counter_programs : forall P a b,
  (exists n, cm_step P (cm_run n P (1, (a, b))) = None) <->
  (exists n, E.halted (E.compile (map earned_minsky P))
               (E.core_of (E.run_prog n (E.compile (map earned_minsky P)) (E.start a b)))).
Proof.
  intros P a b. rewrite <- E.halting_correspondence.
  split; intros [n Hn]; exists n.
  - rewrite <- reference_agrees, <- reference_step_agrees. exact Hn.
  - rewrite reference_step_agrees, reference_agrees. exact Hn.
Qed.

(* CHECK is a unit-cost test. From any start (a, b), the single move
   CHECK (A >= m) costs 1 and settles whether a >= m: the trap latch is
   down after it exactly when a >= m. The two counters alone settle that
   only by counting A down. The record (the flag and the ledger) is not
   what makes this one step: the core's next value never reads them
   (E.base_blind). *)
Theorem check_ge_unit_cost : forall a b m,
  E.cost (E.CHECK (E.PGe m) E.CA) = 1 /\
  E.err (E.core_of (E.exec (E.start a b) (E.CHECK (E.PGe m) E.CA))) = negb (Nat.leb m a).
Proof.
  intros a b m. split; [reflexivity |].
  unfold E.exec, E.cexec, E.check_ok. simpl.
  destruct (Nat.leb m a); reflexivity.
Qed.

(* ================================================================= *)
(* 3. The small machine over any property language with an exact     *)
(*    checker and a property that can fail.                           *)
(* ================================================================= *)

Section GenericInstance.

Context {prop : Type}.
Variable prop_eqb : prop -> prop -> bool.
Hypothesis prop_eqb_eq : forall p q, prop_eqb p q = true <-> p = q.
Variable eval : prop -> nat -> bool.
Variable holds : prop -> nat -> Prop.
Hypothesis eval_iff : forall p v, eval p v = true <-> holds p v.

Definition generic_machine : machine :=
  mk_machine (@G.state prop) (@G.instr prop) (G.exec prop_eqb eval)
    (@G.cost prop) (@G.cert prop).

Lemma run_generic : forall tr s, run generic_machine tr s = G.run prop_eqb eval tr s.
Proof. induction tr; intros; simpl; auto. Qed.

Lemma generic_base_blind : forall s i,
  G.core_of (G.exec prop_eqb eval s i) = G.cexec prop_eqb eval (G.core_of s) i.
Proof. reflexivity. Qed.

Definition gctr_of (r : reg) : G.ctr := match r with RA => G.CA | RB => G.CB end.

Definition generic_compile (i : cm_instr) : @G.instr prop :=
  match i with CINC r => G.INC (gctr_of r) | CDEC r j => G.DEC (gctr_of r) j end.

Definition generic_window (s : @G.state prop) : cm_conf :=
  (G.pc (G.core_of s), (G.ca (G.core_of s), G.cb (G.core_of s))).

Lemma generic_sim : forall (s : @G.state prop) i, G.err (G.core_of s) = false ->
  generic_window (G.exec prop_eqb eval s (generic_compile i)) = cm_exec i (generic_window s) /\
  G.err (G.core_of (G.exec prop_eqb eval s (generic_compile i))) = false.
Proof.
  intros [k m r] i He. unfold generic_window. simpl in *. unfold G.cexec. rewrite He.
  destruct i as [[|] | [|] j]; simpl.
  - auto.
  - auto.
  - destruct (G.ca k) eqn:Ha; unfold G.goto; simpl; rewrite ?Ha; auto.
  - destruct (G.cb k) eqn:Hb; unfold G.goto; simpl; rewrite ?Hb; auto.
Qed.

Definition generic_base : universal_base generic_machine :=
  mk_ub generic_machine generic_window (fun s => G.err (G.core_of s) = false)
    generic_compile G.start (fun a b => eq_refl) (fun a b => eq_refl) generic_sim.

Definition generic_kind (i : @G.instr prop) : kind (prop * G.ctr) :=
  match i with
  | G.CHECK p c => KCheck (p, c)
  | G.COMMIT p c => KCommit (p, c)
  | G.CERTIFY => KCertify
  | _ => KBase
  end.

Definition generic_interface : thiele_interface generic_machine :=
  mk_ti generic_machine generic_base (prop * G.ctr) generic_kind
    (fun pc s => holds (fst pc) (G.val (G.core_of s) (snd pc)))
    (fun s pc => G.check_ok eval (G.core_of s) (fst pc) (snd pc))
    (fun pc s t => G.ver (G.core_of s) (snd pc) = G.ver (G.core_of t) (snd pc) /\
                   G.val (G.core_of s) (snd pc) = G.val (G.core_of t) (snd pc))
    G.clean_start (@G.mu prop).

Lemma generic_untouched_prefix : forall s mid c, G.untouched prop_eqb eval s mid c ->
  forall t1 t2, mid = t1 ++ t2 ->
  G.ver (G.core_of (G.run prop_eqb eval t1 s)) c = G.ver (G.core_of s) c /\
  G.val (G.core_of (G.run prop_eqb eval t1 s)) c = G.val (G.core_of s) c.
Proof.
  intros s mid c Hu t1. induction t1 as [| i t1 IH] using rev_ind; intros t2 Hmid;
    [simpl; auto |].
  destruct (IH (i :: t2)) as [Hv Hw]; [rewrite Hmid, <- app_assoc; reflexivity |].
  destruct (Hu t1 i t2) as [Hv' Hw']; [rewrite Hmid, <- app_assoc; reflexivity |].
  rewrite G.generic_run_snoc, generic_base_blind. rewrite Hv', Hw'. auto.
Qed.

Lemma generic_chain_holds : forall s0 tr,
  G.clean_start s0 -> G.cert (G.run prop_eqb eval tr s0) = true ->
  earned_chain generic_interface s0 tr.
Proof.
  intros s0 tr H0 H1. pose proof H0 as [_ [Hch Hc0]].
  destruct (G.generic_cert_first prop_eqb eval s0 tr Hc0 H1)
    as [pre [post [Htr [Hpre Hok]]]].
  pose proof Hok as Hset. unfold G.certify_ok in Hset.
  apply andb_true_iff in Hset as [_ Hset].
  destruct (G.chan (G.core_of (G.run prop_eqb eval pre s0))) as [f |] eqn:Hf;
    [| discriminate].
  destruct (G.generic_chan_origin prop_eqb eval s0 pre f Hch Hf)
    as [preC [p [c [mid2 [HpreC [Hcm _]]]]]].
  destruct (G.generic_earned_commitment_provenance prop_eqb prop_eqb_eq eval
              s0 preC p c H0 Hcm)
    as [pre1 [mid1 [Hpre1 [Hck [_ [_ [_ Hun]]]]]]].
  assert (Hlist : pre1 ++ G.CHECK p c :: mid1 ++ G.COMMIT p c :: mid2 = pre)
    by (rewrite HpreC, Hpre1; list_eq).
  exists pre1, (p, c), (G.CHECK p c), mid1, (G.COMMIT p c), mid2, G.CERTIFY, post.
  split; [rewrite Htr, <- Hlist; list_eq |].
  split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
  split; [rewrite run_generic; exact Hck |].
  split.
  { intros t1 t2 Hm. rewrite !run_generic. simpl.
    replace (pre1 ++ G.CHECK p c :: t1) with ((pre1 ++ [G.CHECK p c]) ++ t1)
      by (rewrite <- app_assoc; reflexivity).
    rewrite G.generic_run_app.
    destruct (generic_untouched_prefix _ _ _ Hun t1 t2 Hm) as [Hv Hw].
    rewrite Hv, Hw, G.generic_run_snoc, generic_base_blind,
      G.generic_ver_check, G.generic_val_check.
    split; reflexivity. }
  assert (Hl2 : pre1 ++ G.CHECK p c :: mid1 ++ G.COMMIT p c :: mid2 ++ [G.CERTIFY]
                = pre ++ [G.CERTIFY]) by (rewrite <- Hlist; list_eq).
  assert (Hup : G.cert (G.run prop_eqb eval (pre ++ [G.CERTIFY]) s0) = true)
    by (rewrite G.generic_run_snoc; simpl; rewrite Hpre; exact Hok).
  rewrite <- Hl2 in Hup. rewrite <- Hlist in Hpre.
  split; rewrite run_generic; assumption.
Qed.

(* The bare chain on (p, A) certifies from start a b exactly when p holds
   of a. *)
Lemma generic_chain_iff : forall p a b,
  G.cert (G.run prop_eqb eval [G.CHECK p G.CA; G.COMMIT p G.CA; G.CERTIFY] (G.start a b))
    = true <-> holds p a.
Proof.
  intros p a b. rewrite <- eval_iff.
  change (G.run prop_eqb eval [G.CHECK p G.CA; G.COMMIT p G.CA; G.CERTIFY] (G.start a b))
    with (G.exec prop_eqb eval (G.exec prop_eqb eval
            (G.exec prop_eqb eval (G.start a b) (G.CHECK p G.CA)) (G.COMMIT p G.CA))
            G.CERTIFY).
  destruct (eval p a) eqn:Ev.
  - assert (Hck : G.check_ok eval (G.core_of (G.start a b)) p G.CA = true)
      by (unfold G.check_ok; simpl; rewrite Ev; reflexivity).
    rewrite (G.exec_check_pass prop_eqb eval (G.start a b) p G.CA Hck).
    set (k1 := G.record_fact (G.core_of (G.start a b))
                 (G.claim (G.core_of (G.start a b)) p G.CA)).
    assert (Hcm : G.commit_ok prop_eqb k1 p G.CA = true).
    { apply (G.generic_commit_ok_iff prop_eqb prop_eqb_eq). split; [reflexivity |].
      left. reflexivity. }
    set (s1 := G.mkst k1 (G.mu (G.start a b) + 1) (G.cert (G.start a b))).
    rewrite (G.exec_commit_pass prop_eqb prop_eqb_eq eval s1 p G.CA Hcm).
    split; reflexivity.
  - assert (Hck : G.check_ok eval (G.core_of (G.start a b)) p G.CA = false)
      by (unfold G.check_ok; simpl; rewrite Ev; reflexivity).
    rewrite (G.exec_check_fail prop_eqb eval (G.start a b) p G.CA eq_refl Hck).
    split; intro H; discriminate H.
Qed.

Lemma generic_thiele_complete_with : forall p v w,
  holds p v -> ~ holds p w -> thiele_complete_with generic_interface.
Proof.
  intros p0 v w Hv Hw. split; [| split; [| split]].
  - split; [intros [[|] | [|] j]; reflexivity |].
    split; [intros a b; apply G.generic_start_clean |]. split.
    + intros s m Hk. destruct m; simpl in Hk; try discriminate; simpl;
        apply orb_false_r.
    + intros s m H. apply G.generic_cert_permanent, H.
  - split; [intros s [_ [_ H]]; exact H |]. split.
    + intros s0 tr H0 H1. apply generic_chain_holds; [exact H0 |].
      rewrite <- run_generic. exact H1.
    + split.
      * intros s [p c] H. simpl in *. unfold G.check_ok in H.
        apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [_ H].
        apply eval_iff, H.
      * intros [p c] s t [_ Hsame] H. simpl in *. rewrite <- Hsame. exact H.
  - split; [intros []; reflexivity | intros s m; reflexivity].
  - exists (p0, G.CA), (G.CHECK p0 G.CA), (G.COMMIT p0 G.CA), G.CERTIFY.
    split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
    split; [| split; [exists v, 0; exact Hv | exists w, 0; exact Hw]].
    intros a b. unfold load. simpl ti_meaning. rewrite run_generic.
    apply generic_chain_iff.
Qed.

(* The generic machine's claim language. It is built from the properties,
   their equality test and what they mean (holds) alone: the checker eval
   is not part of it. *)
Definition generic_claim_eqb (x y : prop * G.ctr) : bool :=
  prop_eqb (fst x) (fst y) &&
  match snd x, snd y with G.CA, G.CA | G.CB, G.CB => true | _, _ => false end.

Lemma generic_claim_eqb_spec : forall x y, generic_claim_eqb x y = true <-> x = y.
Proof.
  intros [p c] [q d]. unfold generic_claim_eqb. simpl. rewrite andb_true_iff, prop_eqb_eq.
  split.
  - intros [Hp Hc]. assert (c = d) by (destruct c, d; try discriminate; reflexivity).
    subst. reflexivity.
  - intro H. inversion H; subst. split; [reflexivity | destruct d; reflexivity].
Qed.

Lemma generic_same_keeps : forall (pc : prop * G.ctr) (s t : @G.state prop),
  G.ver (G.core_of s) (snd pc) = G.ver (G.core_of t) (snd pc) /\
  G.val (G.core_of s) (snd pc) = G.val (G.core_of t) (snd pc) ->
  holds (fst pc) (G.val (G.core_of s) (snd pc)) ->
  holds (fst pc) (G.val (G.core_of t) (snd pc)).
Proof. intros pc s t [_ Hw] H. rewrite <- Hw. exact H. Qed.

Definition generic_language : claim_language generic_machine :=
  mk_cl generic_machine (prop * G.ctr) generic_claim_eqb generic_claim_eqb_spec
    (fun pc s => holds (fst pc) (G.val (G.core_of s) (snd pc)))
    (fun pc s t => G.ver (G.core_of s) (snd pc) = G.ver (G.core_of t) (snd pc) /\
                   G.val (G.core_of s) (snd pc) = G.val (G.core_of t) (snd pc))
    generic_same_keeps.

Lemma generic_check_sound : forall (s : @G.state prop) (pc : prop * G.ctr),
  G.check_ok eval (G.core_of s) (fst pc) (snd pc) = true ->
  holds (fst pc) (G.val (G.core_of s) (snd pc)).
Proof.
  intros s [p c] H. simpl in *. unfold G.check_ok in H.
  apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [_ H].
  apply eval_iff, H.
Qed.

Definition generic_li : lang_interface generic_machine generic_language :=
  mk_lang generic_machine generic_language generic_base generic_kind
    (fun s pc => G.check_ok eval (G.core_of s) (fst pc) (snd pc)) generic_check_sound
    G.clean_start (@G.mu prop).

End GenericInstance.

(* The small machine over any property language with an exact checker, in
   which some property is true of one value and false of another, is
   Thiele-complete. *)
Theorem earned_generic_thiele_complete :
  forall (prop : Type) (prop_eqb : prop -> prop -> bool)
         (eval : prop -> nat -> bool) (holds : prop -> nat -> Prop),
  (forall p q, prop_eqb p q = true <-> p = q) ->
  (forall p v, eval p v = true <-> holds p v) ->
  (exists p v w, holds p v /\ ~ holds p w) ->
  thiele_complete (generic_machine prop_eqb eval).
Proof.
  intros prop prop_eqb eval holds Heq Hiff [p [v [w [Hv Hw]]]].
  exists (generic_interface prop_eqb eval holds).
  exact (generic_thiele_complete_with prop_eqb Heq eval holds Hiff p v w Hv Hw).
Qed.

(* With "this counter is a sorted list": 18 decodes to [1; 2], sorted, and
   20 decodes to [2; 1], not sorted. *)
Theorem sorted_machine_thiele_complete :
  thiele_complete (generic_machine G.sprop_eqb G.seval).
Proof.
  apply (earned_generic_thiele_complete _ _ _ G.sholds G.sprop_eqb_eq G.seval_iff).
  exists G.PSorted, 18, 20. split.
  - simpl. apply G.sortedb_iff. vm_compute. reflexivity.
  - simpl. intro H. apply G.sortedb_iff in H. vm_compute in H. discriminate H.
Qed.

(* The same three machines over their claim languages fixed in advance:
   the property language with its own meanings comes first, and the
   interface supplies only the base, the kinds, the checker with its
   soundness proof, the clean states and the ledger. *)
Theorem earned_generic_thiele_complete_over :
  forall (prop : Type) (prop_eqb : prop -> prop -> bool)
         (eval : prop -> nat -> bool) (holds : prop -> nat -> Prop)
         (Heq : forall p q, prop_eqb p q = true <-> p = q),
  (forall p v, eval p v = true <-> holds p v) ->
  (exists p v w, holds p v /\ ~ holds p w) ->
  thiele_complete_over (generic_machine prop_eqb eval)
    (generic_language prop_eqb Heq eval holds).
Proof.
  intros prop prop_eqb eval holds Heq Hiff [p [v [w [Hv Hw]]]].
  exists (generic_li prop_eqb Heq eval holds Hiff).
  exact (generic_thiele_complete_with prop_eqb Heq eval holds Hiff p v w Hv Hw).
Qed.

Theorem sorted_machine_thiele_complete_over :
  thiele_complete_over (generic_machine G.sprop_eqb G.seval)
    (generic_language G.sprop_eqb G.sprop_eqb_eq G.seval G.sholds).
Proof.
  apply (earned_generic_thiele_complete_over _ _ _ G.sholds G.sprop_eqb_eq G.seval_iff).
  exists G.PSorted, 18, 20. split.
  - simpl. apply G.sortedb_iff. vm_compute. reflexivity.
  - simpl. intro H. apply G.sortedb_iff in H. vm_compute in H. discriminate H.
Qed.

(* ================================================================= *)
(* Assumption audit. Every line must print                            *)
(* "Closed under the global context".                                 *)
(* ================================================================= *)

Print Assumptions thiele_complete_is_weak.
Print Assumptions base_runs_every_program.
Print Assumptions base_halting_correspondence.
Print Assumptions ledger_counts_record_moves.
Print Assumptions certificate_costs_three.
Print Assumptions committed_claim_holds.
Print Assumptions check_can_fail.
Print Assumptions some_run_certifies.
Print Assumptions only_certify_raises.
Print Assumptions complete_costs_at_most_one.
Print Assumptions complete_has_free_move.
Print Assumptions one_move_record_excluded.
Print Assumptions never_certifies_excluded.
Print Assumptions clock_weakly_thiele_complete.
Print Assumptions clock_not_thiele_complete.
Print Assumptions latch_clock_weakly_thiele_complete.
Print Assumptions latch_clock_not_thiele_complete.
Print Assumptions paid_latch_weakly_thiele_complete.
Print Assumptions paid_latch_meets_base_and_toll.
Print Assumptions paid_latch_not_thiele_complete.
Print Assumptions silent_weakly_thiele_complete.
Print Assumptions silent_meets_base_record_toll.
Print Assumptions silent_not_thiele_complete.
Print Assumptions earned_core_thiele_complete.
Print Assumptions reference_agrees.
Print Assumptions earned_core_runs_counter_programs.
Print Assumptions earned_generic_thiele_complete.
Print Assumptions sorted_machine_thiele_complete.
Print Assumptions thiele_complete_over_complete.
Print Assumptions thiele_complete_with_over.
Print Assumptions over_certificate_means.
Print Assumptions earned_core_thiele_complete_over.
Print Assumptions earned_generic_thiele_complete_over.
Print Assumptions sorted_machine_thiele_complete_over.
Print Assumptions check_ge_unit_cost.
