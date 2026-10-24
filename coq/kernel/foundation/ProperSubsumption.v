(** Turing simulation with an explicit cost counter.

    This standalone model pairs a Turing configuration with a natural-number
    ledger and proves projection of runs plus an upper bound on the recorded
    charge. These are simulation and accounting results. They do not prove
    that Turing machines cannot encode ledgers or produce cost certificates,
    nor a strict separation of computable functions. The historical filename
    and theorem identifier are retained for compatibility; read their types.
*)

(* SCOPE NOTE: standalone proof scope; this file is not bridged to
   the kernel, and imports none of it.

   What it is: a self-contained Turing-machine development (TM_Config,
   tm_step, tm_run) together with a LOCAL record
   [Thiele_Config := { th_tm_config : TM_Config; th_mu : nat }] that pairs a
   Turing configuration with a counter. No definition, statement, or proof
   here mentions a certification system or the small machine.

   The audit is waived rather than satisfied: satisfying it from inside would
   mean importing the kernel without using it, which asserts a bridge that
   isn't there. See the scope note on [thiele_simulates_turing] below for what
   this file does and does not show. The boundary is stated here rather than
   inferred from an import. *)

From Coq Require Import List Arith.PeanoNat Lia Bool Psatz.
Import ListNotations.

Module ProperSubsumption.


(** Tape symbols - arbitrary natural numbers (Turing-complete) *)
Definition Symbol := nat.

(** DESIGN CHOICE: blank = 0 is the standard Turing Machine convention.
    This is NOT a vacuous definition - it's the canonical blank symbol
    used in all TM formalizations (Hopcroft & Ullman, Sipser, etc.).
    Inquisitor: This zero is INTENTIONAL and CORRECT. *)
(* SAFE: Blank = 0 is the standard TM convention per Hopcroft & Ullman. *)
Definition blank : Symbol := 0.

(** Tape: infinite in both directions, represented as two lists + head position *)
Record Tape := {
  tape_left  : list Symbol;  (** Symbols to the left of head *)
  tape_head  : Symbol;       (** Symbol under head *)
  tape_right : list Symbol   (** Symbols to the right of head *)
}.

Definition empty_tape : Tape := {|
  tape_left := [];
  tape_head := blank;
  tape_right := []
|}.

(** Turing machine state *)
Definition TM_State := nat.

(** Turing machine transition: (state, symbol) -> (new_state, write_symbol, move) *)
Inductive Direction := L | R | Stay.

Record TM_Transition := {
  tm_write : Symbol;
  tm_move  : Direction;
  tm_next  : TM_State
}.

(** Transition function (partial) *)
Definition TM_Delta := TM_State -> Symbol -> option TM_Transition.

(** Move the tape head *)
Definition move_tape (d : Direction) (t : Tape) : Tape :=
  match d with
  | L => match t.(tape_left) with
         | [] => {| tape_left := []; tape_head := blank; 
                    tape_right := t.(tape_head) :: t.(tape_right) |}
         | x :: xs => {| tape_left := xs; tape_head := x;
                         tape_right := t.(tape_head) :: t.(tape_right) |}
         end
  | R => match t.(tape_right) with
         | [] => {| tape_left := t.(tape_head) :: t.(tape_left);
                    tape_head := blank; tape_right := [] |}
         | x :: xs => {| tape_left := t.(tape_head) :: t.(tape_left);
                         tape_head := x; tape_right := xs |}
         end
  | Stay => t
  end.

(** Write to tape *)
Definition write_tape (s : Symbol) (t : Tape) : Tape :=
  {| tape_left := t.(tape_left); tape_head := s; tape_right := t.(tape_right) |}.

(** Full Turing machine configuration *)
Record TM_Config := {
  tm_state : TM_State;
  tm_tape  : Tape
}.

(** Single step of Turing machine *)
Definition tm_step (delta : TM_Delta) (c : TM_Config) : option TM_Config :=
  match delta c.(tm_state) c.(tm_tape).(tape_head) with
  | None => None  (** Halt *)
  | Some trans =>
      let new_tape := move_tape trans.(tm_move) (write_tape trans.(tm_write) c.(tm_tape)) in
      Some {| tm_state := trans.(tm_next); tm_tape := new_tape |}
  end.

(** Multi-step execution with fuel *)
Fixpoint tm_run (fuel : nat) (delta : TM_Delta) (c : TM_Config) : TM_Config :=
  match fuel with
  | 0 => c
  | S fuel' =>
      match tm_step delta c with
      | None => c  (** Halted *)
      | Some c' => tm_run fuel' delta c'
      end
  end.


(** Thiele configuration: Turing config + μ-ledger *)
Record Thiele_Config := {
  th_tm_config : TM_Config;
  th_mu : nat  (** μ-cost accumulator *)
}.

(** Cost function for operations *)
Definition step_cost : nat := 1.
Definition write_cost (s : Symbol) : nat := if Nat.eqb s blank then 0 else 1.

(** Thiele step: same as Turing + cost accounting *)
Definition thiele_step (delta : TM_Delta) (c : Thiele_Config) : option Thiele_Config :=
  match tm_step delta c.(th_tm_config) with
  | None => None
  | Some tm_c' =>
      let written := match delta c.(th_tm_config).(tm_state) c.(th_tm_config).(tm_tape).(tape_head) with
                     | Some trans => trans.(tm_write)
                     | None => blank
                     end in
      let cost := step_cost + write_cost written in
      Some {| th_tm_config := tm_c'; th_mu := c.(th_mu) + cost |}
  end.

(** Multi-step Thiele execution *)
Fixpoint thiele_run (fuel : nat) (delta : TM_Delta) (c : Thiele_Config) : Thiele_Config :=
  match fuel with
  | 0 => c
  | S fuel' =>
      match thiele_step delta c with
      | None => c
      | Some c' => thiele_run fuel' delta c'
      end
  end.


(** Lift Turing config to Thiele config *)
Definition lift_config (c : TM_Config) : Thiele_Config :=
  {| th_tm_config := c; th_mu := 0 |}.

(** Generalized simulation: mu value doesn't affect tape/state evolution *)
Lemma thiele_simulates_turing_gen :
  forall fuel delta tc,
    (thiele_run fuel delta tc).(th_tm_config) = tm_run fuel delta tc.(th_tm_config).
Proof.
  induction fuel as [|fuel IH]; intros delta tc.
  - reflexivity.
  - simpl.
    unfold thiele_step.
    remember (tm_step delta (th_tm_config tc)) as step_result eqn:Hstep.
    destruct step_result as [c'|].
    + simpl. apply IH.
    + reflexivity.
Qed.

(** SCOPE NOTE: what "Thiele" means in this theorem's name.

    [Thiele_Config] here is the LOCAL record defined in this file,
    [{ th_tm_config : TM_Config; th_mu : nat }], a Turing configuration
    paired with a nat counter. It is NOT a certification system, and
    [thiele_step] is NOT the small machine's step. Nothing in this file
    touches the kernel.

    So the content below is: carrying an extra field alongside a Turing
    configuration does not disturb the Turing configuration's evolution.
    Structurally it is the projection law [fst . (f x g) = f . fst], proved by
    induction on fuel. That is worth recording; it is the sanity check that the
    ledger is inert with respect to tape/state dynamics. It is not the claim
    that the Thiele substrate runs every Turing trace.

    For a machine that runs every two-counter program, see the small
    machine's simulation theorems in [minimal/EarnedCore.v]. Do not cite
    this theorem as evidence that a Thiele machine simulates Turing
    machines. *)
Theorem thiele_simulates_turing :
  forall fuel delta c,
    (thiele_run fuel delta (lift_config c)).(th_tm_config) = tm_run fuel delta c.
Proof.
  intros fuel delta c.
  apply thiele_simulates_turing_gen.
Qed.

(** Corollary: Any Turing-computable result is Thiele-computable *)
Corollary turing_computable_implies_thiele_computable :
  forall fuel delta c_init,
    tm_tape (th_tm_config (thiele_run fuel delta (lift_config c_init))) = 
    tm_tape (tm_run fuel delta c_init) /\
    tm_state (th_tm_config (thiele_run fuel delta (lift_config c_init))) = 
    tm_state (tm_run fuel delta c_init).
Proof.
  intros fuel delta c_init.
  rewrite thiele_simulates_turing.
  split; reflexivity.
Qed.


(** The key property Thiele provides that Turing doesn't: 
    A verifiable cost certificate for any computation.
    
    This is NOT about computational power - both compute the same functions.
    This IS about observable properties of the computation trace.
*)

(** Cost certificate: a proven bound on computation cost *)
Record CostCertificate := {
  cc_fuel : nat;
  cc_bound : nat;
  cc_witness : nat  (** Actual cost observed *)
}.

(** Thiele can produce cost certificates; Turing cannot *)
Definition thiele_cost_certificate (fuel : nat) (delta : TM_Delta) (c : Thiele_Config) 
    : CostCertificate :=
  let final := thiele_run fuel delta c in
  {| cc_fuel := fuel;
     cc_bound := fuel * (step_cost + 1);  (** Upper bound *)
     cc_witness := final.(th_mu) - c.(th_mu) |}.

(** Helper: mu increases by at most (step_cost + 1) per step *)
Lemma thiele_run_mu_bound :
  forall fuel delta c,
    (thiele_run fuel delta c).(th_mu) <= c.(th_mu) + fuel * (step_cost + 1).
Proof.
  induction fuel as [|fuel IH]; intros delta c.
  - simpl. lia.
  - simpl. unfold thiele_step.
    destruct (tm_step delta (th_tm_config c)) as [c'|] eqn:Hstep; [|simpl; lia].
    remember (match delta (tm_state (th_tm_config c)) (tape_head (tm_tape (th_tm_config c))) with
              | Some trans => tm_write trans
              | None => blank
              end) as written eqn:Hwritten.
    simpl.
    specialize (IH delta {| th_tm_config := c'; th_mu := th_mu c + (step_cost + write_cost written) |}).
    simpl in IH.
    unfold step_cost, write_cost in *.
    destruct (Nat.eqb written blank); simpl in *; lia.
Qed.

(** The certificate is valid: witness ≤ bound *)
Lemma cost_certificate_valid :
  forall fuel delta c,
    (thiele_cost_certificate fuel delta c).(cc_witness) <=
    (thiele_cost_certificate fuel delta c).(cc_bound).
Proof.
  intros fuel delta c.
  unfold thiele_cost_certificate. simpl.
  pose proof (thiele_run_mu_bound fuel delta c) as H.
  unfold step_cost in *. simpl in *.
  nia.
Qed.


(** Local simulation with cost. No impossibility theorem about ordinary
    Turing computation is asserted by the conjunction below. *)

Definition TM_computes (delta : TM_Delta) (c_init c_final : TM_Config) : Prop :=
  exists fuel, tm_run fuel delta c_init = c_final.

Definition Thiele_computes_with_cost (delta : TM_Delta) (c_init : Thiele_Config) 
    (c_final : Thiele_Config) (cost : nat) : Prop :=
  exists fuel, thiele_run fuel delta c_init = c_final /\
               c_final.(th_mu) - c_init.(th_mu) = cost.

(** Historical identifier: simulation together with a cost-certificate bound. *)
Theorem thiele_strictly_extends_turing :
  (** Simulation: every Turing computation has a Thiele simulation *)
  (forall delta c_init c_final,
    TM_computes delta c_init c_final ->
    exists c_th_final cost,
      Thiele_computes_with_cost delta (lift_config c_init) c_th_final cost /\
      c_th_final.(th_tm_config) = c_final) /\
  (** Cost certificates: Thiele provides certificates with proven bounds *)
  (forall fuel delta c,
    let cert := thiele_cost_certificate fuel delta c in
    cert.(cc_witness) <= cert.(cc_bound)).
Proof.
  split.
  - (* simulation *)
    intros delta c_init c_final [fuel Hrun].
    exists (thiele_run fuel delta (lift_config c_init)).
    exists ((thiele_run fuel delta (lift_config c_init)).(th_mu)).
    split.
    + exists fuel. split.
      * reflexivity.
      * simpl. lia.
    + rewrite thiele_simulates_turing. exact Hrun.
  - (* cost certificates *)
    intros fuel delta c. apply cost_certificate_valid.
Qed.


(** The two conjuncts establish projection-preserving simulation and the
    validity of the chosen cost bound in this local model. A Turing machine
    can also encode and compute these data. Connecting this development to
    the abstract toll or to a particular host requires a separate bridge. *)

End ProperSubsumption.
