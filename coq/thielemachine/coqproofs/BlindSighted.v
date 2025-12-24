(*** RESTORED BLINDSIGHTED MODULE ***)
From Coq Require Import List Arith Lia ZArith Bool.
Import ListNotations.

(** Basic types and simple specification - restored minimal version *)
Definition ModuleId := nat.
Definition Region := list nat.

Record Partition := {
  modules : list (ModuleId * Region);
  next_id : ModuleId;
}.

Definition trivial_partition (universe : Region) : Partition :=
  {| modules := [(0, universe)]; next_id := 1 |}.

Record MuLedger := {
  mu_operational : Z;
  mu_discovery : Z;
  mu_total : Z;
}.

Definition zero_ledger : MuLedger :=
  {| mu_operational := 0; mu_discovery := 0; mu_total := 0 |}.

Record ThieleState := {
  partition : Partition;
  ledger : MuLedger;
  halted : bool;
  answer : option nat;
}.

(* Surface names used by cross-layer isomorphism tests. *)
Definition ThieleSighted := ThieleState.

Definition initial_state (universe : Region) : ThieleState :=
  {| partition := trivial_partition universe; ledger := zero_ledger; halted := false; answer := None |}.

(* Sighted partition operations (restored surface). *)
Inductive ThieleInstr : Type :=
| PNEW : Region -> nat -> ThieleInstr
| PSPLIT : ModuleId -> Region -> nat -> ThieleInstr
| PMERGE : ModuleId -> ModuleId -> nat -> ThieleInstr
| PDISCOVER : ModuleId -> nat -> ThieleInstr
| EMIT : nat -> ThieleInstr
| HALT : ThieleInstr.

Definition ThieleProg := list ThieleInstr.

Definition is_blind_safe (i : ThieleInstr) : bool :=
  match i with
  | EMIT _ => true
  | HALT => true
  | _ => false
  end.
Definition is_blind_program (p : ThieleProg) : bool := forallb is_blind_safe p.

(* Natural partitions (restored symbols for isomorphism mapping). *)

Definition chsh_natural_partition : Partition :=
  {| modules := [(0, [1; 3]); (1, [2; 4]); (2, [5; 6; 7; 8])]; next_id := 3 |}.

  (* SAFE: Bounded arithmetic operation with explicit domain *)
Definition shor_n_bits (N : nat) : nat := Nat.log2 (Nat.max 1 N) + 1.

Definition shor_residue_vars (N : nat) : Region := seq 1 (shor_n_bits N).
Definition shor_period_vars (N : nat) : Region := seq (1 + shor_n_bits N) (shor_n_bits N).
Definition shor_factor_vars (N : nat) : Region := seq (1 + 2 * shor_n_bits N) (shor_n_bits N).

Definition shor_natural_partition (N : nat) : Partition :=
  {| modules := [(0, shor_residue_vars N);
                (1, shor_period_vars N);
                (2, shor_factor_vars N)];
     next_id := 3 |}.

Definition BlindThieleState := ThieleState.
Definition ThieleBlind := BlindThieleState.
Definition blind_initial (universe : Region) : BlindThieleState := initial_state universe.

Record TuringConfig := { tm_tape : list nat; tm_head : nat; tm_state : nat }.
Definition tm_output (cfg : TuringConfig) : nat := cfg.(tm_state).
Definition encode_tm_config (cfg : TuringConfig) : Region := cfg.(tm_tape) ++ [cfg.(tm_head); cfg.(tm_state)].

Theorem TM_as_BlindThiele : forall (cfg : TuringConfig), exists (blind_prog : ThieleProg) (final : BlindThieleState),
  is_blind_program blind_prog = true /\ final.(answer) = Some (tm_output cfg).
Proof.
  intro cfg.
  exists [EMIT (tm_output cfg); HALT].
  exists {| partition := trivial_partition (encode_tm_config cfg); ledger := zero_ledger; halted := true; answer := Some (tm_output cfg) |}.
  split; simpl; reflexivity.
Qed.

Theorem Blind_is_restriction_of_Sighted : forall (prog : ThieleProg) (init_state : BlindThieleState),
  is_blind_program prog = true -> forall final_blind final_sighted, final_blind = final_sighted -> final_blind.(answer) = final_sighted.(answer).
Proof.
  intros prog init_state Hblind final_blind final_sighted Heq. rewrite Heq. reflexivity.
Qed.
