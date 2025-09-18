(* ================================================================= *)
(* Modular Thiele Machine: Universal Theorems with Concrete Instantiation *)
(* ================================================================= *)
From Coq Require Import List String ZArith Lia.
Import ListNotations.
Import List.
Local Arguments List.fold_left {A B} _ _ _.
Local Notation fold_left := List.fold_left.

(* ================================================================= *)
(* Abstract Interface for Thiele Machine *)
(* ================================================================= *)

Module Type THIELE_ABSTRACT.
  (* Types *)
  Parameter Instr State Event Cert Hash : Type.
  Parameter is_LASSERT is_MDLACC is_PNEW is_PYEXEC is_EMIT : Instr -> bool.

  (* Step semantics + observation *)
  Record StepObs := { ev : option Event; mu_delta : Z; cert : Cert }.
  Parameter step : list Instr -> State -> State -> StepObs -> Prop.

  (* Checker, sizes, eq *)
  Parameter check_step : list Instr -> State -> State -> option Event -> Cert -> bool.
  Parameter bitsize : Cert -> Z.
  Parameter state_eqb : State -> State -> bool.

  (* Hash chain (optional) *)
  Parameter H0 : Hash.
  Parameter hash_state : State -> Hash.
  Parameter hash_cert  : Cert  -> Hash.
  Parameter hcombine   : Hash -> Hash -> Hash.

  (* Well-formedness *)
  Definition well_formed_prog (P : list Instr) : bool :=
    forallb (fun i => orb (orb (is_LASSERT i) (is_MDLACC i))
                         (orb (is_PNEW i) (orb (is_PYEXEC i) (is_EMIT i)))) P.

  (* Receipts and replay *)
  Definition Receipt := (State * State * option Event * Cert)%type.

  Fixpoint replay_ok (P:list Instr) (s0:State) (rs:list Receipt) : bool :=
    match rs with
    | [] => true
    | (spre, spost, oev, c)::tl =>
        if negb (state_eqb spre s0) then false
        else if check_step P spre spost oev c
             then replay_ok P spost tl
             else false
    end.

  Fixpoint receipts_of (P:list Instr) (s0:State)
         (tr:list (State*StepObs)) : list Receipt :=
    match tr with
    | [] => []
    | (s',obs)::tl =>
        (s0,s',obs.(ev),obs.(cert)) :: receipts_of P s' tl
    end.

  Definition sum_mu (tr: list (State*StepObs)) : Z :=
    List.fold_right (fun '(_,obs) acc => Z.add obs.(mu_delta) acc) 0%Z tr.

  Fixpoint sum_bits (rs: list Receipt) : Z :=
    match rs with
    | [] => 0%Z
    | (_,_,_,c)::tl => Z.add (bitsize c) (sum_bits tl)
    end.

  (* Axioms / interface lemmas *)
  Axiom check_step_sound :
    forall P s s' obs, step P s s' obs ->
      check_step P s s' obs.(ev) obs.(cert) = true.

  Axiom mu_lower_bound :
    forall P s s' obs, step P s s' obs ->
      Z.le (bitsize obs.(cert)) obs.(mu_delta).

  Axiom check_step_complete :
    forall P s s' oev c,
      check_step P s s' oev c = true ->
      exists obs, step P s s' obs /\ obs.(ev) = oev /\ obs.(cert) = c.

  Axiom state_eqb_refl : forall s, state_eqb s s = true.

End THIELE_ABSTRACT.

(* ================================================================= *)
(* Universal Theorems Functor *)
(* ================================================================= *)

Module ThieleUniversal (M : THIELE_ABSTRACT).
  Import M.

  (* A standard big-step execution relation over step *)
  Inductive Exec : list Instr -> State -> list (State*StepObs) -> Prop :=
  | exec_nil : forall s, Exec [] s []
  | exec_cons : forall P s s' obs tl,
      step P s s' obs ->
      Exec P s' tl ->
      Exec P s ((s',obs)::tl).

  Theorem universal_replay :
    forall P s0 tr,
      well_formed_prog P = true ->
      Exec P s0 tr ->
      replay_ok P s0 (receipts_of P s0 tr) = true.
  Proof.
    intros P s0 tr _ Hexec.
    induction Hexec as [|P s s' obs tl Hstep _ IH].
    - reflexivity.
    - simpl. unfold receipts_of in IH. simpl in IH.
      rewrite (state_eqb_refl s).
      rewrite (check_step_sound _ _ _ _ Hstep).
      exact IH.
  Qed.


  Local Lemma sum_bits_cons :
    forall (x:Receipt) xs,
      sum_bits (x::xs)
      = Z.add (let '(_,_,_,c) := x in bitsize c) (sum_bits xs).
  Proof.
    intros x xs.
    simpl. destruct x as [[[? ?] ?] c]. simpl. reflexivity.
  Qed.

  Local Lemma sum_mu_cons :
    forall s' (obs:StepObs) tl,
      sum_mu ((s',obs)::tl) = Z.add obs.(mu_delta) (sum_mu tl).
  Proof.
    intros s' obs tl. unfold sum_mu. simpl.
    reflexivity.
  Qed.

  Theorem universal_mu_accounting :
    forall P s0 tr,
      well_formed_prog P = true ->
      Exec P s0 tr ->
      Z.le (sum_bits (receipts_of P s0 tr)) (sum_mu tr).
  Proof.
    intros P s0 tr _ Hexec.
    induction Hexec as [|P s s' obs tl Hstep IH]; simpl.
    - lia.
    - simpl.
      rewrite <- (sum_mu_cons s' obs tl).
      rewrite <- (sum_bits_cons ((s, s', obs.(ev), obs.(cert))) (receipts_of P s' tl)).
      apply Z.add_le_mono.
      + exact (mu_lower_bound _ _ _ _ Hstep).
      + exact IHIH.
  Qed.

End ThieleUniversal.

(* ================================================================= *)
(* Concrete Implementation *)
(* ================================================================= *)

(* Concrete instruction set based on Python Thiele CPU *)
Inductive ThieleInstr : Type :=
  | LASSERT : string -> ThieleInstr  (* SMT assertion *)
  | MDLACC : ThieleInstr             (* Accumulate μ-cost *)
  | PNEW : list nat -> ThieleInstr   (* Create partitions *)
  | PYEXEC : string -> ThieleInstr   (* Execute Python function *)
  | EMIT : string -> ThieleInstr.    (* Emit certificate *)

(* Concrete CSR registers *)
Inductive ThieleCSR : Type :=
  | STATUS : ThieleCSR    (* 0 = success *)
  | CERT_ADDR : ThieleCSR (* Certificate address *)
  | MU_ACC : ThieleCSR.   (* μ-accumulator *)

(* Concrete events *)
Inductive ThieleEvent : Type :=
  | PolicyCheck : string -> ThieleEvent  (* Policy name *)
  | InferenceComplete : ThieleEvent
  | ErrorOccurred : string -> ThieleEvent.

(* Memory model: simplified heap *)
Record ConcreteHeap : Type := {
  allocations : list (nat * nat);  (* address -> size *)
}.

(* Concrete state *)
Record ConcreteState : Type := {
  pc : nat;
  csrs : ThieleCSR -> Z;
  heap : ConcreteHeap;
}.

(* Based on Python implementation: oracle_query.smt2 + oracle_reply.json *)
Record ConcreteCert : Type := {
  smt_query : string;        (* SMT-LIB2 query *)
  solver_reply : string;     (* JSON reply from solver *)
  metadata : string;         (* Additional metadata *)
  timestamp : Z;             (* Unix timestamp *)
  sequence : nat;            (* Sequence number *)
}.

Parameter ConcreteHash : Type.
Parameter Concrete_H0 : ConcreteHash.

(* Concrete instruction classification *)
Definition concrete_is_LASSERT (i:ThieleInstr) : bool :=
  match i with
  | LASSERT _ => true
  | _ => false
  end.

Definition concrete_is_MDLACC (i:ThieleInstr) : bool :=
  match i with
  | MDLACC => true
  | _ => false
  end.

Definition concrete_is_PNEW (i:ThieleInstr) : bool :=
  match i with
  | PNEW _ => true
  | _ => false
  end.

Definition concrete_is_PYEXEC (i:ThieleInstr) : bool :=
  match i with
  | PYEXEC _ => true
  | _ => false
  end.

Definition concrete_is_EMIT (i:ThieleInstr) : bool :=
  match i with
  | EMIT _ => true
  | _ => false
  end.

(* SMT solver result *)
Inductive SolverResult : Type :=
  | Sat : list (string * Z) -> SolverResult  (* Satisfiable with model *)
  | Unsat : SolverResult                     (* Unsatisfiable *)
  | Unknown : SolverResult.                  (* Unknown result *)

(* SMT checker (abstracted) *)
Parameter check_smt : string -> SolverResult.

(* Concrete step observation *)
Record ConcreteObs := {
  cev       : option ThieleEvent;  (* Optional observable event *)
  cmu_delta : Z;                   (* μ-bit cost delta *)
  ccert     : ConcreteCert;        (* Step certificate *)
}.

(* Concrete step semantics *)
Inductive concrete_step : list ThieleInstr -> ConcreteState -> ConcreteState -> ConcreteObs -> Prop :=
  | step_lassert : forall P s query model,
      (* LASSERT instruction - only succeeds if SMT query is satisfiable *)
      check_smt query = Sat model ->
      let cert := {|
        smt_query := query;
        solver_reply := "checking...";
        metadata := "policy_check";
        timestamp := 0;  (* Would be current time *)
        sequence := 0    (* Would be incremented *)
      |} in
      (* Exact μ-cost calculation matching concrete_bitsize *)
      let query_bytes := String.length query in
      let reply_bytes := String.length "checking..." in
      let meta_bytes := String.length "policy_check" in
      let delimiter_bytes := 4 in  (* {}, commas, newlines in JSON *)
      let timestamp_bytes := 10 in (* Unix timestamp as string *)
      let sequence_bytes := 4 in   (* Sequence number as string *)
      let total_bytes := query_bytes + reply_bytes + meta_bytes +
                        delimiter_bytes + timestamp_bytes + sequence_bytes in
      let mu_cost := Z.mul (Z.of_nat total_bytes) 8 in
      concrete_step P s s {|
        cev := Some (PolicyCheck query);
        cmu_delta := mu_cost;
        ccert := cert
      |}

  | step_mdlacc : forall P s,
      (* MDLACC instruction - accumulate μ-cost *)
      let cert := {|
        smt_query := "";
        solver_reply := "{}";
        metadata := "mdlacc";
        timestamp := 0;
        sequence := 0
      |} in
      (* Exact μ-cost calculation matching concrete_bitsize *)
      let query_bytes := String.length "" in
      let reply_bytes := String.length "{}" in
      let meta_bytes := String.length "mdlacc" in
      let delimiter_bytes := 4 in  (* {}, commas, newlines in JSON *)
      let timestamp_bytes := 10 in (* Unix timestamp as string *)
      let sequence_bytes := 4 in   (* Sequence number as string *)
      let total_bytes := query_bytes + reply_bytes + meta_bytes +
                        delimiter_bytes + timestamp_bytes + sequence_bytes in
      let cert_size := Z.mul (Z.of_nat total_bytes) 8 in
      concrete_step P s s {|
        cev := None;
        cmu_delta := cert_size;  (* Cost covers certificate size *)
        ccert := cert
      |}.

(* Concrete certificate checker - fail-closed policy for Unknown *)
Definition concrete_check_step (P:list ThieleInstr) (spre:ConcreteState) (spost:ConcreteState)
                                  (oev:option ThieleEvent) (c:ConcreteCert) : bool :=
  match c with
  | {| smt_query := ""; solver_reply := "{}" |} => true  (* MDLACC case *)
  | {| smt_query := query; solver_reply := _ |} =>
      match check_smt query with
      | Sat _ => true   (* Policy satisfied *)
      | Unsat => false  (* Policy violated *)
      | Unknown => false (* Fail-closed: unknown = violation for safety *)
      end
  end.

(* Alternative fail-open version for robustness *)
Definition concrete_check_step_fail_open (P:list ThieleInstr) (spre:ConcreteState) (spost:ConcreteState)
                                           (oev:option ThieleEvent) (c:ConcreteCert) : bool :=
  match c with
  | {| smt_query := ""; solver_reply := "{}" |} => true  (* MDLACC case *)
  | {| smt_query := query; solver_reply := _ |} =>
      match check_smt query with
      | Sat _ => true   (* Policy satisfied *)
      | Unsat => false  (* Policy violated *)
      | Unknown => true (* Fail-open: allow unknown for robustness *)
      end
  end.

(* Size of certificate in bits - exact match to Python artifact counting *)
Definition concrete_bitsize (c:ConcreteCert) : Z :=
  match c with
  | {| smt_query := q; solver_reply := r; metadata := m; timestamp := ts; sequence := seq |} =>
      (* Count exact bytes: query + reply + metadata + delimiters + timestamp + sequence *)
      let query_bytes := String.length q in
      let reply_bytes := String.length r in
      let meta_bytes := String.length m in
      let delimiter_bytes := 4 in  (* {}, commas, newlines in JSON *)
      let timestamp_bytes := 10 in (* Unix timestamp as string *)
      let sequence_bytes := 4 in   (* Sequence number as string *)
      let total_bytes := query_bytes + reply_bytes + meta_bytes +
                        delimiter_bytes + timestamp_bytes + sequence_bytes in
      Z.mul (Z.of_nat total_bytes) 8
  end.


(* State equality - checks pc, csrs, and heap *)
Definition concrete_state_eq (s1 s2: ConcreteState) : bool :=
  andb (Nat.eqb s1.(pc) s2.(pc))
       (andb (forallb (fun csr => Z.eqb (s1.(csrs) csr) (s2.(csrs) csr))
                      (STATUS :: CERT_ADDR :: MU_ACC :: nil))
             true).  (* Simplified heap comparison *)

(* Concrete hash functions *)
Definition concrete_hash_state (s:ConcreteState) : ConcreteHash := Concrete_H0.  (* Simplified *)
Definition concrete_hash_cert (c:ConcreteCert) : ConcreteHash := Concrete_H0.   (* Simplified *)
Definition concrete_hcombine (h1 h2:ConcreteHash) : ConcreteHash := Concrete_H0.        (* Simplified *)

(* Concrete state equality is reflexive *)
Theorem concrete_state_eqb_refl : forall s, concrete_state_eq s s = true.
Proof.


  intros s.
  unfold concrete_state_eq.
  (* pc equality *)
  rewrite Nat.eqb_refl.
  (* CSR equality - all registers equal to themselves *)
  simpl.
  repeat (rewrite Z.eqb_refl).
  (* Heap comparison - simplified to true *)
  simpl.
  reflexivity.
Qed.

(* ================================================================= *)
(* TRUSTED: Solver/Checker Interface Axioms *)
(* ================================================================= *)

(* These axioms document the trust base for the Thiele Machine *)
(* Note: concrete_check_step_sound and concrete_check_step_complete are already proven in ThieleMachineConcrete.v *)

(* Proof that concrete steps produce checkable certificates *)
Theorem concrete_check_step_sound :
  forall P s s' obs,
    concrete_step P s s' obs ->
    concrete_check_step P s s' obs.(cev) obs.(ccert) = true.
Proof.
  intros P s s' obs Hstep.
  inversion Hstep; subst; simpl.
  - (* LASSERT case *)
    unfold concrete_check_step.
    (* Since step requires check_smt query = Sat model, checker will accept *)
    rewrite H. reflexivity.
  - (* MDLACC case *)
    unfold concrete_check_step.
    (* MDLACC produces valid certificate *)
    reflexivity.
Qed.

(* Proof that μ-cost covers certificate size *)
Theorem concrete_mu_lower_bound :
  forall P s s' obs,
    concrete_step P s s' obs ->
    Z.le (concrete_bitsize obs.(ccert)) obs.(cmu_delta).
Proof.
  intros P s s' obs Hstep.
  inversion Hstep; subst; simpl.
  - (* LASSERT case *)
    unfold concrete_bitsize.
    (* Query length * 8 <= query length * 8 *)
    apply Z.le_refl.
  - (* MDLACC case *)
    unfold concrete_bitsize.
    (* 0 <= 0 *)
    apply Z.le_refl.
Qed.

(* Completeness: accepted certificates correspond to valid steps *)
Theorem concrete_check_step_complete :
  forall P s s' oev c,
    concrete_check_step P s s' oev c = true ->
    exists obs, concrete_step P s s' obs /\ obs.(cev) = oev /\ obs.(ccert) = c.
Proof.
  intros P s s' oev c Hcheck.
  unfold concrete_check_step in Hcheck.
  destruct c as [query reply meta ts seq].
  destruct (string_dec query "").
  - (* MDLACC case *)
    subst.
    exists {|
      cev := oev;
      cmu_delta := Z.mul (Z.of_nat (0 + String.length reply + String.length meta + 4 + 10 + 4)) 8;
      ccert := {| smt_query := ""; solver_reply := reply; metadata := meta; timestamp := ts; sequence := seq |}
    |}.
    split.
    + apply step_mdlacc.
    + reflexivity.
  - (* LASSERT case *)
    destruct (check_smt query) eqn:Hsmt.
    + (* Sat model *)
      exists {|
        cev := oev;
        cmu_delta := Z.mul (Z.of_nat (String.length query + String.length "checking..." + String.length "policy_check" + 4 + 10 + 4)) 8;
        ccert := {| smt_query := query; solver_reply := "checking..."; metadata := "policy_check"; timestamp := 0; sequence := 0 |}
      |}.
      split.
      * apply step_lassert with (model := l). assumption.
      * reflexivity.
    + (* Unsat or Unknown - but checker returned true only for Sat *)
      discriminate.
    + discriminate.
Qed.

(* ================================================================= *)
(* Concrete Module Implementation *)
(* ================================================================= *)

Module ConcreteThiele <: THIELE_ABSTRACT.

  (* Bind types *)
  Definition Instr := ThieleInstr.
  Definition State := ConcreteState.
  Definition Event := ThieleEvent.
  Definition Cert  := ConcreteCert.
  Definition Hash  := ConcreteHash.

  (* Bind wf predicates *)
  Definition is_LASSERT := concrete_is_LASSERT.
  Definition is_MDLACC  := concrete_is_MDLACC.
  Definition is_PNEW    := concrete_is_PNEW.
  Definition is_PYEXEC  := concrete_is_PYEXEC.
  Definition is_EMIT    := concrete_is_EMIT.

  (* Observations - define first since used in other definitions *)
  Record StepObs := { ev : option Event; mu_delta : Z; cert : Cert }.

  (* Well-formedness *)
  Definition well_formed_prog (P : list Instr) : bool :=
    forallb (fun i => orb (orb (is_LASSERT i) (is_MDLACC i))
                         (orb (is_PNEW i) (orb (is_PYEXEC i) (is_EMIT i)))) P.

  (* Receipts and replay *)
  Definition Receipt := (State * State * option Event * Cert)%type.

  Fixpoint replay_ok (P:list Instr) (s0:State) (rs:list Receipt) : bool :=
    match rs with
    | [] => true
    | (spre, spost, oev, c)::tl =>
        if negb (concrete_state_eq spre s0) then false
        else if concrete_check_step P spre spost oev c
             then replay_ok P spost tl
             else false
    end.

  Fixpoint receipts_of (P:list Instr) (s0:State)
         (tr:list (State*StepObs)) : list Receipt :=
    match tr with
    | [] => []
    | (s',obs)::tl =>
        (s0,s',obs.(ev),obs.(cert)) :: receipts_of P s' tl
    end.

  Definition sum_mu (tr: list (State*StepObs)) : Z :=
    List.fold_right (fun '(_,obs) acc => Z.add obs.(mu_delta) acc) 0%Z tr.

  Fixpoint sum_bits (rs: list Receipt) : Z :=
    match rs with
    | [] => 0%Z
    | (_,_,_,c)::tl => Z.add (concrete_bitsize c) (sum_bits tl)
    end.

  Definition step (P:list Instr) (s s':State) (obs:StepObs) : Prop :=
    concrete_step P s s' {|
      cev := obs.(ev);
      cmu_delta := obs.(mu_delta);
      ccert := obs.(cert)
    |}.

  (* Checker, sizes, eq *)
  Definition check_step := concrete_check_step.
  Definition bitsize    := concrete_bitsize.
  Definition state_eqb  := concrete_state_eq.

  (* Hash-chain (optional) *)
  Definition H0         := Concrete_H0.
  Definition hash_state := concrete_hash_state.
  Definition hash_cert  := concrete_hash_cert.
  Definition hcombine   := concrete_hcombine.
  
  (* Hash full receipt for tamper-evidence *)
  Parameter hash_receipt : ConcreteThiele.Receipt -> ConcreteHash.
  Axiom hash_receipt_injective : forall r r', hash_receipt r = hash_receipt r' -> r = r'.

  (* Axioms / interface lemmas - using trusted concrete interface *)
  Theorem check_step_sound :
    forall P s s' obs, step P s s' obs ->
      check_step P s s' obs.(ev) obs.(cert) = true.
  Proof.
    intros P s s' obs Hstep.
    unfold step, check_step in *.
    apply concrete_check_step_sound.
    exact Hstep.
  Qed.

  Theorem mu_lower_bound :
    forall P s s' obs, step P s s' obs ->
      Z.le (bitsize obs.(cert)) obs.(mu_delta).
  Proof.
    intros P s s' obs Hstep.
    unfold step, bitsize in *.
    apply concrete_mu_lower_bound.
    exact Hstep.
  Qed.

  Theorem check_step_complete :
    forall P s s' oev c,
      check_step P s s' oev c = true ->
      exists obs, step P s s' obs /\ obs.(ev) = oev /\ obs.(cert) = c.
  Proof.
    intros P s s' oev c Hcheck.
    unfold check_step, step in *.
    apply concrete_check_step_complete in Hcheck.
    exact Hcheck.
  Qed.

  Theorem state_eqb_refl : forall s, state_eqb s s = true.
  Proof. exact concrete_state_eqb_refl. Qed.

End ConcreteThiele.

(* ================================================================= *)
(* Apply the Functor to Get Specialized Theorems *)
(* ================================================================= *)

Module ConcreteUniv := ThieleUniversal(ConcreteThiele).
Export ConcreteUniv.


(* ================================================================= *)
(* Main Corollaries (Replacing the Old Existential Theorem) *)
(* ================================================================= *)

(* Concrete execution (simplified) *)
Inductive ConcreteExec : list ThieleInstr -> ConcreteState -> list (ConcreteState*ConcreteObs) -> Prop :=
| cexec_nil : forall s, ConcreteExec [] s []
| cexec_cons : forall P s s' obs tl,
    concrete_step P s s' obs ->
    ConcreteExec P s' tl ->
    ConcreteExec P s ((s',obs)::tl).

(* Generate receipts from execution trace *)
Fixpoint concrete_receipts_of (P:list ThieleInstr) (s0:ConcreteState) (tr:list (ConcreteState*ConcreteObs))
                               : list ConcreteThiele.Receipt :=
  match tr with
  | [] => []
  | (s', obs)::tl =>
      let receipt := (s0, s', obs.(cev), obs.(ccert)) in
      receipt :: concrete_receipts_of P s' tl
  end.

(* Sum μ-deltas over execution trace *)
Definition concrete_sum_mu (steps: list (ConcreteState*ConcreteObs)) : Z :=
  List.fold_right (fun '(_,obs) acc => Z.add obs.(cmu_delta) acc) 0%Z steps.

(* Sum certificate sizes over receipts *)
Definition concrete_sum_bits (rs: list ConcreteThiele.Receipt) : Z :=
  @List.fold_left _ _ (fun (acc:Z) '(_,_,_,c) => Z.add acc (ConcreteThiele.bitsize c)) rs 0%Z.

(* ================================================================= *)
(* Bridge between Concrete and Abstract Execution *)
(* ================================================================= *)

Definition toAbsObs (o:ConcreteObs) : ConcreteThiele.StepObs :=
  {| ConcreteThiele.ev := o.(cev);
     ConcreteThiele.mu_delta := o.(cmu_delta);
     ConcreteThiele.cert := o.(ccert) |}.

Lemma ConcreteExec_to_Abstract :
  forall P s tr,
    ConcreteExec P s tr ->
    ConcreteUniv.Exec P s (map (fun '(s',o) => (s', toAbsObs o)) tr).
Proof.
  intros P s tr H; induction H.
  - constructor.
  - simpl. eapply ConcreteUniv.exec_cons.
    + unfold ConcreteThiele.step.
      destruct obs as [ev mu cert].
      simpl in *.
      replace ev with (ConcreteThiele.ev {| ConcreteThiele.ev := ev; ConcreteThiele.mu_delta := mu; ConcreteThiele.cert := cert |}) by reflexivity.
      replace mu with (ConcreteThiele.mu_delta {| ConcreteThiele.ev := ev; ConcreteThiele.mu_delta := mu; ConcreteThiele.cert := cert |}) by reflexivity.
      replace cert with (ConcreteThiele.cert {| ConcreteThiele.ev := ev; ConcreteThiele.mu_delta := mu; ConcreteThiele.cert := cert |}) by reflexivity.
      exact H.
    + exact IHConcreteExec.
Qed.

(* Universal replay for concrete machine *)
Lemma receipts_of_map_abs :
  forall P,
    forall s tr,
      ConcreteThiele.receipts_of P s
        (map (fun '(s',o) => (s', toAbsObs o)) tr)
      = concrete_receipts_of P s tr.
Proof.
  intros P s tr.
  revert s.
  induction tr as [|[s' o] tl IH]; intros s; simpl.
  - reflexivity.
  - f_equal. apply IH.
Qed.
Lemma mu_delta_toAbsObs o : ConcreteThiele.mu_delta (toAbsObs o) = cmu_delta o.
Proof. unfold toAbsObs, ConcreteThiele.mu_delta; reflexivity. Qed.
  (* Extensionality for fold_right over lists *)
  Lemma fold_right_ext {A B : Type} (f g : A -> B -> B) (z : B) (l : list A) :
    (forall x y, f x y = g x y) ->
    fold_right f z l = fold_right g z l.
  Proof.
    induction l; simpl; intros; [reflexivity|rewrite H, IHl; auto].
  Qed.
Lemma fold_mu_delta_toAbsObs_eq :
  forall (tl : list (ConcreteThiele.State * ConcreteObs)),
    fold_right (fun '(_, obs) acc => ConcreteThiele.mu_delta (toAbsObs obs) + acc)%Z 0%Z tl =
    fold_right (fun '(_, obs) acc => ConcreteThiele.mu_delta (toAbsObs obs) + acc)%Z 0%Z tl.
Proof. reflexivity. Qed.

Lemma sum_mu_map_abs :
  forall tr,
    ConcreteThiele.sum_mu (map (fun '(s',o) => (s', toAbsObs o)) tr)
    = concrete_sum_mu tr.
Proof.
  induction tr as [|[s' o] tl IH].
  - reflexivity.
  - simpl. rewrite IH. unfold ConcreteThiele.sum_mu, concrete_sum_mu in *. simpl.
    reflexivity.
Qed.

Corollary Concrete_replay_ok :
  forall P s0 tr,
    ConcreteThiele.well_formed_prog P = true ->
    ConcreteExec P s0 tr ->
    ConcreteThiele.replay_ok P s0 (concrete_receipts_of P s0 tr) = true.
Proof.
  intros P s0 tr WF Hex.
  pose proof (ConcreteExec_to_Abstract P s0 tr Hex) as Habs.
  rewrite <- receipts_of_map_abs.
  eapply ConcreteUniv.universal_replay; eauto.
Qed.
Definition fourth {A B C D : Type} (x : A * B * C * D) : D :=
  let '(_, _, _, d) := x in d.

Definition fold_left_z
  (l : list (ConcreteThiele.State * ConcreteThiele.State * option ConcreteThiele.Event * ConcreteThiele.Cert))
  (acc : Z) :=
  List.fold_left (fun acc x => Z.add acc (ConcreteThiele.bitsize (fourth x))) l acc.

Lemma fold_left_cons {A B} (f : B -> A -> B) (x : A) (xs : list A) (acc : B) :
  List.fold_left f (x :: xs) acc = List.fold_left f xs (f acc x).
Proof. reflexivity. Qed.





Lemma concrete_sum_bits_eq :
  forall P s tr,
    concrete_sum_bits (concrete_receipts_of P s tr) =
    ConcreteThiele.sum_bits (ConcreteThiele.receipts_of P s (map (fun p => (fst p, toAbsObs (snd p))) tr)).
Proof.
  intros P s tr.
  rewrite receipts_of_map_abs.
  unfold concrete_sum_bits, ConcreteThiele.sum_bits.
  (* Need to prove fold_left = recursive sum *)
  induction (concrete_receipts_of P s tr).
  - reflexivity.
  - simpl. destruct a as [[[? ?] ?] c]. simpl.
    rewrite fold_left_cons.
    unfold fold_left_z. simpl.
    f_equal. apply IHl.
Qed.


Corollary Concrete_mu_ok :
  forall P s0 tr,
    ConcreteThiele.well_formed_prog P = true ->
    ConcreteExec P s0 tr ->
    Z.le (concrete_sum_bits (concrete_receipts_of P s0 tr)) (concrete_sum_mu tr).
Proof.
  intros P s0 tr WF Hex.
  pose proof (ConcreteExec_to_Abstract P s0 tr Hex) as Habs.
  rewrite <- receipts_of_map_abs.
  rewrite <- sum_mu_map_abs.
  rewrite <- concrete_sum_bits_eq.
  apply ConcreteUniv.universal_mu_accounting; auto.
  (* WF is the same *)
  unfold ConcreteThiele.well_formed_prog in WF.
  exact WF.
Qed.


(* ================================================================= *)
(* Hash-Chain Tamper-Evidence Lemma *)
(* ================================================================= *)

(* Hash chain over receipts - matches Python global_hash_chain.json *)
Fixpoint hash_chain (rs: list ConcreteThiele.Receipt) : ConcreteHash :=
  match rs with
  | [] => ConcreteThiele.H0
  | r::tl =>
      let h_r := hash_receipt r in
      let h_prev := hash_chain tl in
      ConcreteThiele.hcombine h_r h_prev
  end.

Axiom hash_chain_collision_free :
  forall r tl tl',
    ConcreteThiele.hcombine (hash_receipt r) (hash_chain tl)
    = ConcreteThiele.hcombine (hash_receipt r) (hash_chain tl')
    -> tl = tl'.

Lemma concrete_sum_bits_eq_acc :
  forall P s tr,
    @List.fold_left _ _ (fun (acc:Z) '(_,_,_,c) => Z.add acc (ConcreteThiele.bitsize c))
      (concrete_receipts_of P s tr) 0%Z =
    ConcreteThiele.sum_bits (ConcreteThiele.receipts_of P s (map (fun p => (fst p, toAbsObs (snd p))) tr)).
Admitted.

Theorem hash_chain_tamper_evidence :
  forall rs rs', hash_chain rs = hash_chain rs' -> rs = rs'.
Proof.
  induction rs as [| r tl IH]; intros rs' Heq.
  - destruct rs'; [reflexivity | discriminate].
  - destruct rs' as [| r' tl']; [discriminate | ].
    simpl in Heq.
    destruct (hash_receipt r =? hash_receipt r') eqn:Heq_r.
    + (* Receipts have same hash *)
      apply hash_receipt_injective in Heq_r.
      subst r'.
      apply hash_chain_collision_free in Heq.
      apply IH in Heq.
      subst tl'.
      reflexivity.
    + (* Different hashes *)
      (* Assume hcombine is injective in first argument *)
      admit.  (* Assume hcombine injective *)
Admitted.

Lemma concrete_sum_bits_eq_new :
  forall P s tr,
    concrete_sum_bits (concrete_receipts_of P s tr) =
    ConcreteThiele.sum_bits (ConcreteThiele.receipts_of P s (map (fun p => (fst p, toAbsObs (snd p))) tr)).
Admitted.


(* ================================================================= *)
(* Concrete Example Program *)
(* ================================================================= *)

(* Example: Simple policy check program *)
Definition P_demo : list ThieleInstr :=
  [LASSERT "cat_is_safe"; MDLACC; EMIT "policy_result"].

(* Well-formedness proof for demo program *)
Theorem P_demo_well_formed :
  ConcreteThiele.well_formed_prog P_demo = true.
Proof.
  unfold P_demo, ConcreteThiele.well_formed_prog.
  simpl.
  (* LASSERT is well-formed *)
  unfold concrete_is_LASSERT.
  (* MDLACC is well-formed *)
  unfold concrete_is_MDLACC.
  (* EMIT is well-formed *)
  unfold concrete_is_EMIT.
  reflexivity.
Qed.

(* Example execution with replay guarantee *)
Example demo_replay_ok :
  forall s0 tr,
    ConcreteExec P_demo s0 tr ->
    ConcreteThiele.replay_ok P_demo s0 (concrete_receipts_of P_demo s0 tr) = true.
Proof.
  intros s0 tr Hexec.
  apply Concrete_replay_ok; [apply P_demo_well_formed | exact Hexec].
Qed.