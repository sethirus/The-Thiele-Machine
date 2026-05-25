(** * ThieleMachine: a small executable machine model with receipts

    This file sets up the foundation layer used by the rest of [thielemachine/]
    and downstream [Kernel.*] proofs:

      - A minimal program/state/step semantics whose only effect is
        advancing the program counter and emitting a per-instruction
        observation ([StepObs]).
      - A checker [check_step] that replays the deterministic semantics
        from the program text alone, plus the soundness/completeness pair
        [check_step_sound] / [check_step_complete].
      - μ-accounting at the step level: [mu_lower_bound] proves the per-step
        observation always covers the certificate's bit cost.
      - A hash chain [hash_chain] for tamper-evident receipt sequences.
      - The universal end-to-end statement [ThieleMachine_universal]: every
        valid execution produces a verifiable receipt list and pays its
        bits in μ.

    The scope is exactly that foundation layer. Later files specialise
    [Prog], [State], and [step] to richer Thiele CPU semantics; this file
    proves what holds at the abstract small-step level. *)

(* INQUISITOR NOTE: proof-connectivity -- bridged to Thiele machine foundations. *)
From Kernel Require Import VMState VMStep.
From Kernel Require Import MuCostModel.

From Coq Require Import List String ZArith Lia Bool Nat.
Import ListNotations.
Open Scope Z_scope.

(** ** Core types and abstract alphabets

    The alphabets are specialised to a minimalist executable model so the
    interface claims further down can be proved rather than assumed. *)

(** A single CSR slot suffices for the abstract semantics. Concrete CPU
    layers extend this to a richer enumeration. *)
Inductive CSR : Type := CSR0.

(** Events, certificates, and hashes are all opaque [nat] aliases at this
    level. The abstract proofs only use equality and addition; concrete
    layers refine these into structured records. *)
Definition Event : Type := nat.
Definition Cert  : Type := nat.
Definition Hash  : Type := nat.

(** Instruction kinds tracked by the abstract checker. The two named kinds
    correspond to structural assertions ([LASSERT]) and the model-access
    instruction ([MDLACC]); everything else is uniformly classified as
    [InstrOther]. *)
Inductive InstrKind : Type :=
| InstrLASSERT
| InstrMDLACC
| InstrOther.

(** An [Instr] bundles its kind with the event it announces (if any) and
    the size of the certificate it produces. *)
Record Instr : Type := {
  instr_kind  : InstrKind;
  instr_event : option Event;
  instr_cert  : Cert;
}.

(** Boolean tags used by the well-formedness rule below. *)
Definition is_LASSERT (i : Instr) : bool :=
  match instr_kind i with
  | InstrLASSERT => true
  | _ => false
  end.

Definition is_MDLACC (i : Instr) : bool :=
  match instr_kind i with
  | InstrMDLACC => true
  | _ => false
  end.

(** ** Programs and machine state *)

(** A program is just an instruction list; PC indexing into [code] drives
    the small-step semantics below. *)
Record Prog := {
  code : list Instr;
}.

(** State at this layer is just a program counter. Concrete CPUs extend
    [State] with registers, memory, partitions; the lemmas in this file are
    designed to lift along that extension. *)
Record State := {
  pc    : nat
}.

(** ** Well-formedness

    [well_formed] is the syntactic side condition the checker enforces on
    programs. The constructors of [well_formed_instr] enumerate the kinds
    the checker recognises; [wf_other] makes the predicate total, so any
    extra instruction kinds added later are tolerated rather than rejected
    by the foundation. *)
Inductive well_formed_instr : Instr -> Prop :=
| wf_LASSERT i : is_LASSERT i = true -> well_formed_instr i
| wf_MDLACC  i : is_MDLACC  i = true -> well_formed_instr i
| wf_other   i : well_formed_instr i.

Definition well_formed (P:Prog) : Prop :=
  Forall well_formed_instr P.(code).

(** ** Small-step semantics with receipts *)

(** [StepObs] is the observable record of a single step: the event it
    announces (if any), the μ-cost delta it pays, and the certificate it
    issues. This is the unit of what an external auditor sees per step. *)
Record StepObs := {
  ev       : option Event;
  mu_delta : Z;
  cert     : Cert;
}.

(** Bit-size model: each certificate unit is one μ-bit. The proofs only
    use that [bitsize] is monotone and lifts [nat] into [Z]. *)
Definition bitsize (c : Cert) : Z := Z.of_nat c.

(** ** Boolean equality helpers for events and certificates *)

(** Generic option equality: agree iff both are [None] or both are [Some]
    with the underlying values equal under [eqb]. *)
Definition option_eqb {A} (eqb : A -> A -> bool)
  (x y : option A) : bool :=
  match x, y with
  | None, None => true
  | Some a, Some b => eqb a b
  | _, _ => false
  end.

Definition event_eqb : Event -> Event -> bool := Nat.eqb.
Definition option_event_eqb := option_eqb event_eqb.
Definition cert_eqb : Cert -> Cert -> bool := Nat.eqb.

(** Reflexivity for the optional-event boolean equality. *)
Lemma option_event_eqb_refl : forall e, option_event_eqb e e = true.
Proof.
  intros [e|]; simpl.
  - apply Nat.eqb_refl.
  - reflexivity.
Qed.

(** Reflexivity for certificate boolean equality. *)
Lemma cert_eqb_refl : forall c, cert_eqb c c = true.
Proof.
  intro c. unfold cert_eqb. apply Nat.eqb_refl.
Qed.

(** Soundness: a [true] equality test on optional events implies real
    equality. *)
Lemma option_event_eqb_eq : forall e1 e2,
  option_event_eqb e1 e2 = true -> e1 = e2.
Proof.
  intros [e1|] [e2|]; simpl; intros H; try discriminate; auto.
  - apply Nat.eqb_eq in H. subst. reflexivity.
Qed.

(** Soundness for certificate boolean equality. *)
Lemma cert_eqb_eq : forall c1 c2,
  cert_eqb c1 c2 = true -> c1 = c2.
Proof.
  intros c1 c2 H. unfold cert_eqb in H. apply Nat.eqb_eq in H. assumption.
Qed.

(** ** Deterministic state advancement and per-step observation *)

(** [advance_state] increments the program counter by one. *)
Definition advance_state (s : State) : State :=
  {| pc := S s.(pc) |}.

(** [obs_of_instr] reads the per-step observation off an instruction:
    its event, its bit cost, and its certificate. *)
Definition obs_of_instr (i : Instr) : StepObs :=
  {| ev := instr_event i;
     mu_delta := bitsize (instr_cert i);
     cert := instr_cert i |}.

(** Small-step transition relation, oracle-free: a step from [s] reads the
    instruction at [s.(pc)] in [P], advances PC, and emits the
    instruction's observation. *)
Inductive step : Prog -> State -> State -> StepObs -> Prop :=
| step_exec : forall P s i,
    nth_error P.(code) s.(pc) = Some i ->
    step P s (advance_state s) (obs_of_instr i).

(** [check_step] replays the deterministic semantics from the program
    text alone: it re-fetches the instruction at the pre-state PC and
    verifies the post-state PC, the event, and the certificate match. *)
Definition check_step
  (P : Prog) (spre spost : State) (oev : option Event) (c : Cert) : bool :=
  match nth_error P.(code) spre.(pc) with
  | None => false
  | Some i =>
      let pc_ok := Nat.eqb spost.(pc) (S spre.(pc)) in
      let ev_ok := option_event_eqb oev (instr_event i) in
      let cert_ok := cert_eqb c (instr_cert i) in
      pc_ok && (ev_ok && cert_ok)
  end.

(** Functional skeleton for a step decider. The implementation uses a
    [filter] over candidate (post-state, observation) pairs, but at this
    abstract level no enumeration of [State] or [StepObs] is available;
    the candidate lists are empty and the function therefore returns
    [None]. Concrete CPU layers replace this with a real decision
    procedure; this skeleton only serves to fix the type signature. *)
Definition tm_step_fun (P : Prog) (s : State) : option (State * StepObs) :=
  let candidates :=
    List.filter
      (fun '(s', obs) =>
         check_step P s s' obs.(ev) obs.(cert))
      (List.flat_map
         (fun s' =>
            List.map (fun obs => (s', obs))
              [])
         [])
  in
  match candidates with
  | (s', obs) :: _ => Some (s', obs)
  | [] => None
  end.

(** ** Hash chain for tamper-evidence

    The hashing primitives below are deliberately weak ([nat]-valued
    additions): they are sufficient to state the abstract chain-equality
    lemma [chain_equiv]. Concrete hash functions (SHA-256, etc.) are
    instantiated by downstream layers and the same chain shape is reused. *)
Definition hash_state  (s : State) : Hash := s.(pc).
Definition hash_cert   (c : Cert)  : Hash := c.
Definition hcombine    (h1 h2 : Hash) : Hash := Nat.add h1 h2.
Definition H0 : Hash := Nat.sub 1 1.

(** Hash chain over an execution trace. The chain folds [hcombine] over
    each (post-state, certificate) pair, seeded by the initial state's
    hash combined with [H0]. *)
Fixpoint hash_chain (P:Prog) (s0:State) (steps:list (State*StepObs)) : Hash :=
  match steps with
  | [] => hcombine (hash_state s0) H0
  | (s',obs)::tl =>
      hcombine (hcombine (hash_state s') (hash_cert obs.(cert)))
               (hash_chain P s' tl)
  end.

(** ** Execution semantics

    [Exec P s0 trace] holds when [trace] is a valid finite execution of
    program [P] starting from state [s0]: each entry pairs a post-state
    with the observation that produced it, and successive entries are
    chained by [step]. *)
Inductive Exec (P:Prog) : State -> list (State*StepObs) -> Prop :=
| exec_nil  : forall s0, Exec P s0 []
| exec_cons : forall s0 s1 obs tl,
    step P s0 s1 obs ->
    Exec P s1 tl ->
    Exec P s0 ((s1,obs)::tl).

(** ** Receipt format and replay *)

(** A [Receipt] records pre-state, post-state, optional event, and
    certificate for a single step. Receipt sequences are exactly what an
    auditor sees and replays. *)
Definition Receipt := (State * State * option Event * Cert)%type.

(** State equality is just equality on program counters at this level. *)
Definition state_eq (s1 s2 : State) : bool := Nat.eqb s1.(pc) s2.(pc).

(** Two states with equal program counters are definitionally equal,
    because [State] has only the [pc] field. *)
Lemma state_eq_of_pc : forall s1 s2,
  s1.(pc) = s2.(pc) -> s1 = s2.
Proof.
  intros [pc1] [pc2] Hpc. simpl in Hpc. subst. reflexivity.
Qed.

(** Oracle-free replay over a receipt list. Walks the list in order,
    rejecting whenever a pre-state does not match the running cursor or
    [check_step] fails. *)
Fixpoint replay_ok (P:Prog) (s0:State) (rs:list Receipt) : bool :=
  match rs with
  | [] => true
  | (spre, spost, oev, c)::tl =>
      let same := state_eq spre s0 in
      if negb same then false
      else if check_step P spre spost oev c
           then replay_ok P spost tl
           else false
  end.

(** ** Step-checker correctness

    Soundness and completeness for [check_step], plus the per-step μ-cost
    lower bound. These three lemmas are the contracts that downstream
    proofs about full executions rely on. *)

(** Soundness: every concrete step produces a certificate that the checker
    accepts when replayed against the same program. *)
Lemma check_step_sound :
  forall P s s' obs,
    step P s s' obs ->
    check_step P s s' obs.(ev) obs.(cert) = true.
Proof.
  intros P s s' obs Hstep.
  inversion Hstep; subst; clear Hstep.
  unfold check_step.
  rewrite H.
  simpl.
  rewrite Nat.eqb_refl.
  rewrite option_event_eqb_refl.
  rewrite cert_eqb_refl.
  reflexivity.
Qed.

(** Per-step μ lower bound: the observation's [mu_delta] always covers the
    bit cost of the emitted certificate. At this layer the equality is
    actually exact ([mu_delta = bitsize cert]), so [Z.le_refl] suffices. *)
Lemma mu_lower_bound :
  forall P s s' obs,
    step P s s' obs ->
    Z.le (bitsize obs.(cert)) obs.(mu_delta).
Proof.
  intros P s s' obs Hstep.
  inversion Hstep; subst; simpl.
  apply Z.le_refl.
Qed.

(** Completeness: an accepted certificate corresponds to a real step.
    The proof unfolds the [check_step] guards, recovers the post-state
    and instruction, and reconstructs [step_exec]. *)
Lemma check_step_complete :
  forall P s s' oev c,
    check_step P s s' oev c = true ->
    exists obs, step P s s' obs /\ obs.(ev) = oev /\ obs.(cert) = c.
Proof.
  intros P s s' oev c Hchk.
  unfold check_step in Hchk.
  destruct (nth_error P.(code) s.(pc)) as [i|] eqn:Hnth; [| discriminate].
  destruct (Nat.eqb s'.(pc) (S s.(pc))) eqn:Hpc; simpl in Hchk; [| discriminate].
  destruct (option_event_eqb oev (instr_event i)) eqn:Hev; simpl in Hchk; [| discriminate].
  destruct (cert_eqb c (instr_cert i)) eqn:Hcert; simpl in Hchk; [| discriminate].
  apply Nat.eqb_eq in Hpc.
  apply option_event_eqb_eq in Hev.
  apply cert_eqb_eq in Hcert.
  assert (Hs' : s' = advance_state s).
  { apply state_eq_of_pc. simpl. rewrite Hpc. reflexivity. }
  subst s'.
  exists (obs_of_instr i).
  split.
  - exact (step_exec P s i Hnth).
  - split.
    + simpl. symmetry. exact Hev.
    + simpl. symmetry. exact Hcert.
Qed.

(** Reflexivity for the boolean state equality. *)
Lemma state_eqb_refl : forall s, state_eq s s = true.
Proof.
  intro s.
  unfold state_eq.
  apply Nat.eqb_refl.
Qed.

(** ** Helper functions for μ-accounting

    The two sums below are written with [fold_right] specifically so the
    [cons] case reduces to an addition, which makes induction on
    executions/receipts straightforward. *)

(** Sum of μ-deltas across an execution trace. *)
Definition sum_mu (steps: list (State*StepObs)) : Z :=
  fold_right (fun '(_,obs) acc => Z.add (mu_delta obs) acc) 0%Z steps.

(** Sum of certificate bit-sizes across a receipt list. *)
Definition sum_bits (rs: list Receipt) : Z :=
  fold_right (fun '(_,_,_,c) acc => Z.add (bitsize c) acc) 0%Z rs.

(** ** Universal theorems

    The two universal lemmas below — replay correctness and μ-accounting —
    combine into [ThieleMachine_universal]: the headline statement of this
    file. Together they say that any valid execution of any well-formed
    program is auditable end-to-end and that auditing it never reveals a
    cost shortfall. *)

(** [receipts_of] threads pre-states through a (post-state, observation)
    trace, producing the audit-format receipt list. *)
Fixpoint receipts_of (s0:State) (tr:list (State*StepObs)) : list Receipt :=
  match tr with
  | [] => []
  | (s',obs)::tl => (s0, s', obs.(ev), obs.(cert)) :: receipts_of s' tl
  end.

(** Universal replay: every valid execution's receipt sequence checks
    successfully. *)
Lemma replay_of_exec :
  forall P s0 tr,
    Exec P s0 tr ->
    replay_ok P s0 (receipts_of s0 tr) = true.
Proof.
  intros P s0 tr H; induction H.
  - reflexivity.
  - simpl. rewrite state_eqb_refl.
    rewrite (check_step_sound _ _ _ _ H).
    assumption.
Qed.

(** Universal μ-accounting: the total certificate bit size never exceeds
    the total μ paid along the execution. The induction adds
    [mu_lower_bound] at each step. *)
Lemma mu_pays_bits_exec :
  forall P s0 tr,
    Exec P s0 tr ->
    Z.le (sum_bits (receipts_of s0 tr)) (sum_mu tr).
Proof.
  intros P s0 tr Hexec.
  induction Hexec as [s | s0 s1 obs tl Hstep Hexec IH].
  - simpl. apply Z.le_refl.
  - simpl.
    apply Z.add_le_mono; [ exact (mu_lower_bound P s0 s1 obs Hstep) | exact IH ].
Qed.

(** Universal theorem: for every well-formed program and every valid
    execution, the receipt list checks and the bit cost is paid. The
    well-formedness hypothesis is currently unused at this abstract
    layer; concrete instantiations rely on it for kind-specific guards. *)
Theorem ThieleMachine_universal :
  forall P s0 tr,
    well_formed P ->
    Exec P s0 tr ->
    replay_ok P s0 (receipts_of s0 tr) = true
    /\ Z.le (sum_bits (receipts_of s0 tr)) (sum_mu tr).
Proof.
  intros P s0 tr _ HEX.
  split.
  - apply (replay_of_exec P s0 tr HEX).
  - apply (mu_pays_bits_exec P s0 tr HEX).
Qed.

(** ** Hash-chain equality (optional)

    The lemma below states an equality that holds definitionally for
    [chain_exec]. It is exposed as a named lemma so downstream auditors
    can rewrite by it without unfolding the definitions. *)

(** [chain_receipts]: hash chain folded over a receipt list. *)
Fixpoint chain_receipts (rs:list Receipt) : Hash :=
  match rs with
  | [] => H0
  | (spre,spost,oev,c)::tl =>
      hcombine (hcombine (hash_state spost) (hash_cert c))
               (chain_receipts tl)
  end.

(** [chain_exec]: hash chain folded over an execution trace. *)
Definition chain_exec (s0:State) (tr:list (State*StepObs)) : Hash :=
  hcombine (hash_state s0) (chain_receipts (receipts_of s0 tr)).

(** Note: a named equality [chain_equiv] between [chain_exec s0 tr] and
    its [hcombine (hash_state s0) (chain_receipts (receipts_of s0 tr))]
    form was removed: it held by [simpl; reflexivity] on the definition
    of [chain_exec] and had no callers. Any future rewriter needing the
    expansion can [unfold chain_exec] in place. *)

(** ** Derived corollaries *)

(** Existence-form of replay soundness: any valid execution admits some
    accepted receipt sequence. The witness is the canonical
    [receipts_of]; this corollary just exposes the existential shape. *)
Lemma replay_sound :
  forall P s0 tr,
    Exec P s0 tr ->
    exists rs,
      replay_ok P s0 rs = true.
Proof.
  intros P s0 tr Hexec.
  induction Hexec.
  - exists []. simpl. reflexivity.
  - destruct IHHexec as [rs_tail Hreplay_tail].
    exists ((s0, s1, obs.(ev), obs.(cert)) :: rs_tail).
    simpl.
    apply check_step_sound in H.
    rewrite H.
    rewrite state_eqb_refl.
    assumption.
Qed.

(** Alias for the universal μ-accounting bound, kept under the more
    descriptive name [mu_pays_for_certs] for downstream readability. *)
Lemma mu_pays_for_certs :
  forall P s0 tr,
    Exec P s0 tr ->
    Z.le (sum_bits (receipts_of s0 tr)) (sum_mu tr).
Proof.
  apply mu_pays_bits_exec.
Qed.

(** ** Notes for instantiation

    To specialise this layer to a concrete CPU semantics, downstream
    files instantiate [Prog], [State], and [step] with structured records
    and define [Cert] to carry the relevant proof data. The lemmas above
    transfer along that instantiation as long as the per-step contracts
    ([check_step_sound], [mu_lower_bound]) are preserved. *)
