(** UniversalCertificationCost: any sound certification mechanism costs.

    This file states No Free Insight with nothing fixed. The state type and the
    instruction type are both left abstract, and the theorem only asks for one
    premise: if a single step changes the system from uncertified to certified,
    that step has to cost at least 1.

    That premise is intentionally small. It does not assume monotonicity of the
    certificate, meaningful witnesses, or tight optimal cost. It only says that
    the instant of certification cannot be free. From that, the trace-level
    theorem follows by induction.

    The point is that this base theorem is substrate-independent. If someone has
    any certification system with a step function and a cost function, this
    theorem applies once they pay for that premise. *)

From Coq Require Import List Arith.PeanoNat Lia Bool.
Import ListNotations.

(**

  CertificationSystem is parameterized over both state and instruction type.
  The only base premise is A2: a step that flips certification from false to
  true has to cost at least 1.
*)

Record CertificationSystem := mk_cert_system {
  (** The state space of the computational system. *)
  cs_state : Type;

  (** The instruction type.  Fully abstract: could be a machine instruction,
      a proof term, a network packet, a thermodynamic process, anything. *)
  cs_instr : Type;

  (** The step function: one instruction transforms one state. *)
  cs_step  : cs_state -> cs_instr -> cs_state;

  (** The cost function: how much does executing this instruction cost? *)
  cs_cost  : cs_instr -> nat;

  (** The certification indicator: is this state certified? *)
  cs_cert  : cs_state -> bool;

  (** A2: a single false-to-true certification transition has cost at least
      one. This is the complete premise used by the abstract cost-floor
      theorem. It is a contract on the supplied step and cost functions; the
      record does not identify the cost with work, energy, or any particular
      physical process. *)
  cs_cert_costs :
    forall (s : cs_state) (i : cs_instr),
      cs_cert s = false ->
      cs_cert (cs_step s i) = true ->
      cs_cost i >= 1;
}.


(** Execute a list of instructions on a CertificationSystem.
    Left-fold: instructions applied in list order. *)
Fixpoint cs_run (CS : CertificationSystem)
                (trace : list (cs_instr CS))
                (s : cs_state CS) : cs_state CS :=
  match trace with
  | []        => s
  | i :: rest => cs_run CS rest (cs_step CS s i)
  end.

(** Total cost of a trace: sum of per-instruction costs. *)
Fixpoint cs_total_cost (CS : CertificationSystem)
                       (trace : list (cs_instr CS)) : nat :=
  match trace with
  | []        => 0
  | i :: rest => cs_cost CS i + cs_total_cost CS rest
  end.

(**

    universal_nfi_any_substrate:

    For ANY CertificationSystem CS satisfying A2 (cs_cert_costs),
    any trace from an uncertified initial state to a certified final state
    has total cost ≥ 1.

    Induction on the trace.
    - Base: empty trace; cert cannot go from false to true → contradiction.
    - Step (i :: rest):
        Case A: i certifies (cert goes false→true at step 1).
          → A2 gives cost i ≥ 1.
          → total_cost (i::rest) = cost i + total_cost rest ≥ 1.
        Case B: i does not certify (cert still false after i).
          → cert must be set somewhere in rest.
          → IH on rest gives total_cost rest ≥ 1.
          → total_cost (i::rest) = cost i + total_cost rest ≥ 0 + 1 = 1.
 The proof does NOT require cert monotonicity.
    The single axiom A2 (cs_cert_costs) is sufficient.
*)

Theorem universal_nfi_any_substrate :
  forall (CS : CertificationSystem)
         (trace : list (cs_instr CS))
         (s0 : cs_state CS),
    (** Precondition: start uncertified *)
    cs_cert CS s0 = false ->
    (** Postcondition: end certified *)
    cs_cert CS (cs_run CS trace s0) = true ->
    (** Conclusion: total cost of the trace is ≥ 1 *)
    cs_total_cost CS trace >= 1.
Proof.
  intros CS.
  induction trace as [| i rest IH]; intros s0 Hfalse Htrue.
  - (* Base: empty trace. cs_run returns s0. cert(s0) = false ≠ true. *)
    simpl in Htrue. rewrite Hfalse in Htrue. discriminate.
  - (* Step: trace = i :: rest. *)
    simpl in Htrue. simpl.
    (* Does instruction i certify? *)
    destruct (cs_cert CS (cs_step CS s0 i)) eqn:Hstep.
    + (** Case A: cert becomes true after i.
          cert(s0) = false and cert(step s0 i) = true.
          By A2: cost i ≥ 1. *)
      pose proof (cs_cert_costs CS s0 i Hfalse Hstep).
      lia.
    + (** Case B: cert still false after i.
          cert must be set in the rest of the trace.
          IH gives total_cost rest ≥ 1. *)
      specialize (IH (cs_step CS s0 i) Hstep Htrue).
      lia.
Qed.

(** The same theorem under a name that says what it quantifies over. The
    old name says "any substrate", but a [CertificationSystem] is a
    substrate with the toll built in as its field [cs_cert_costs], so the
    theorem is about every system that has the toll, and about no other.
    The old name stays because other files use it. *)
Theorem every_toll_system_pays_the_floor :
  forall (CS : CertificationSystem)
         (trace : list (cs_instr CS))
         (s0 : cs_state CS),
    cs_cert CS s0 = false ->
    cs_cert CS (cs_run CS trace s0) = true ->
    cs_total_cost CS trace >= 1.
Proof. exact universal_nfi_any_substrate. Qed.

(** Corollary: if the trace certifies from a false-start, the trace is nonempty.
    (Follows from base case: empty trace can't certify.) *)
Corollary cert_trace_nonempty :
  forall (CS : CertificationSystem)
         (trace : list (cs_instr CS))
         (s0 : cs_state CS),
    cs_cert CS s0 = false ->
    cs_cert CS (cs_run CS trace s0) = true ->
    trace <> [].
Proof.
  intros CS trace s0 Hfalse Htrue Hempty.
  subst trace. simpl in Htrue. rewrite Hfalse in Htrue. discriminate.
Qed.

(** A system run by a host.

    A certification system [Guest] is simulated by a host certification
    system [Host] when a map sends guest states to host states and guest
    instructions to host instruction lists, so that one guest step is the
    host running the translated list, and the guest reading is the host
    reading of the image. Nothing about either system is fixed. *)

Record SimulatingCertificationSystem (Host : CertificationSystem) := {
  scs_base   : CertificationSystem ;
  scs_decode : scs_base.(cs_instr) -> list (cs_instr Host) ;
  scs_embed  : scs_base.(cs_state) -> cs_state Host ;
  scs_step_commutes :
    forall (s : scs_base.(cs_state)) (i : scs_base.(cs_instr)),
      scs_embed (scs_base.(cs_step) s i) =
      cs_run Host (scs_decode i) (scs_embed s) ;
  scs_cert_reflects :
    forall (s : scs_base.(cs_state)),
      scs_base.(cs_cert) s = cs_cert Host (scs_embed s)
}.

Arguments scs_base {Host}.
Arguments scs_decode {Host}.
Arguments scs_embed {Host}.
Arguments scs_step_commutes {Host}.
Arguments scs_cert_reflects {Host}.

Lemma cs_run_app :
  forall (CS : CertificationSystem) (t1 t2 : list (cs_instr CS)) (s : cs_state CS),
    cs_run CS (t1 ++ t2) s = cs_run CS t2 (cs_run CS t1 s).
Proof.
  intros CS t1. induction t1 as [| i rest IH]; intros t2 s; simpl.
  - reflexivity.
  - apply IH.
Qed.

Lemma cs_total_cost_app :
  forall (CS : CertificationSystem) (t1 t2 : list (cs_instr CS)),
    cs_total_cost CS (t1 ++ t2) = cs_total_cost CS t1 + cs_total_cost CS t2.
Proof.
  intros CS t1. induction t1 as [| i rest IH]; intros t2; simpl.
  - reflexivity.
  - rewrite IH. lia.
Qed.

(** The guest run, embedded, is the host running the concatenated
    translations. *)
Lemma scs_run_embed :
  forall (Host : CertificationSystem) (SCS : SimulatingCertificationSystem Host)
         (trace : list (cs_instr (scs_base SCS)))
         (s0 : cs_state (scs_base SCS)),
    scs_embed SCS (cs_run (scs_base SCS) trace s0) =
    cs_run Host (concat (map (scs_decode SCS) trace)) (scs_embed SCS s0).
Proof.
  intros Host SCS trace.
  induction trace as [| i rest IH]; intros s0; simpl.
  - reflexivity.
  - rewrite IH, cs_run_app, (scs_step_commutes SCS s0 i). reflexivity.
Qed.

(** A guest run that certifies is a host run that certifies, and the host
    pays at least one unit for it. The host's floor is the host's own A2;
    the guest's cost function plays no part in the second half. *)
Theorem host_represents_simulating_cert_system :
  forall (Host : CertificationSystem) (SCS : SimulatingCertificationSystem Host)
         (s0 : cs_state (scs_base SCS))
         (trace : list (cs_instr (scs_base SCS))),
    cs_cert (scs_base SCS) s0 = false ->
    cs_cert (scs_base SCS) (cs_run (scs_base SCS) trace s0) = true ->
    cs_total_cost (scs_base SCS) trace >= 1 /\
    cs_cert Host (cs_run Host (concat (map (scs_decode SCS) trace))
                                (scs_embed SCS s0)) = true /\
    cs_total_cost Host (concat (map (scs_decode SCS) trace)) >= 1.
Proof.
  intros Host SCS s0 trace Hpre Hpost.
  assert (Hhost : cs_cert Host (cs_run Host (concat (map (scs_decode SCS) trace))
                                  (scs_embed SCS s0)) = true).
  { rewrite <- scs_run_embed, <- (scs_cert_reflects SCS). exact Hpost. }
  split; [exact (universal_nfi_any_substrate (scs_base SCS) trace s0 Hpre Hpost) |].
  split; [exact Hhost |].
  apply (universal_nfi_any_substrate Host _ (scs_embed SCS s0)); [| exact Hhost].
  rewrite <- (scs_cert_reflects SCS). exact Hpre.
Qed.

(** The abstract theorem applies to every supplied [CertificationSystem] whose
    [cs_cert_costs] field holds. If that field were weakened to permit a
    false-to-true step with cost zero, the one-step trace would be a direct
    counterexample to the conclusion. This file proves only the unit floor;
    a bound tied to witness complexity would require additional fields and a
    separate theorem. *)

Print Assumptions every_toll_system_pays_the_floor.
