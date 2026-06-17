(** MuRunIncompleteness.v — μ is NOT a complete invariant of a run.

    NecessityAbstract.v proves, over *arbitrary* VMStates, that vm_mu,
    vm_certified, and vm_graph are three mutually independent trans-classical
    components (thiele_state_three_component_independence). Those separations
    use hand-built witness states — fine for the projection-level statement,
    but they leave one seam open: are the witnesses *runs*? A natural sharper
    question is whether μ becomes complete once you restrict to genuine
    executions:

        if two runs share the full classical shadow (mem, regs, pc) AND share
        μ, must they agree on every run-determined field?

    This file answers NO, over states actually reachable from init_state by
    executing an instruction trace. Each witness is a single one-instruction
    trace, so reachability is immediate:

      certified axis : [certify 2]  vs  [pnew [] 3]
                       certify 2 costs S 2 = 3; pnew [] 3 costs 3. Both leave
                       mem/regs untouched, advance pc to 1, land at μ = 3 —
                       and one is certified, the other is not.

      graph axis     : [pnew [] 0]  vs  [mdlacc 0 0]
                       both cost 0, advance pc to 1, leave mem/regs/μ/certified
                       identical — but pnew conses a module onto the partition
                       graph and mdlacc does not, so the graphs differ.

    Consequence: even restricted to reachable runs, μ is not a complete
    invariant modulo classical-shadow equality. Not every run-determined,
    classically-invisible field factors through μ; the trans-classical
    structure is strictly richer than the single number μ. This is the
    over-runs complement to thiele_state_three_component_independence, and a
    standing guard against the reading that μ is THE universal forgotten
    coordinate. The narrow, true factoring statement remains
    MuInitiality.monotone_factors_through_mu: it holds only for
    instruction-consistent, nat-valued cost functionals — a class that
    excludes vm_certified (a bool that flips independent of cost) and vm_graph. *)

From Coq Require Import List Arith.PeanoNat.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof.
From Kernel Require Import MuInitiality.
From Kernel Require Import NecessityAbstract.

(** ═══════════════════════════════════════════════════════════════════════════
    §1.  CERTIFIED AXIS — equal (mem, regs, pc, μ), differing vm_certified.
    ═══════════════════════════════════════════════════════════════════════════ *)

Definition run_certify : VMState := exec_trace_from init_state [instr_certify 2].
Definition run_pnew3   : VMState := exec_trace_from init_state [instr_pnew [] 3].

Lemma run_certify_reachable : reachable run_certify.
Proof. unfold run_certify. apply reachable_from_trace. Qed.

Lemma run_pnew3_reachable : reachable run_pnew3.
Proof. unfold run_pnew3. apply reachable_from_trace. Qed.

(* exec of a singleton trace is one vm_apply (definitional). *)
Lemma run_certify_step : run_certify = vm_apply init_state (instr_certify 2).
Proof. reflexivity. Qed.

Lemma run_pnew3_step : run_pnew3 = vm_apply init_state (instr_pnew [] 3).
Proof. reflexivity. Qed.

Lemma cert_mem : run_certify.(vm_mem) = run_pnew3.(vm_mem).
Proof.
  rewrite run_certify_step, run_pnew3_step.
  rewrite abs_certify_mem, abs_pnew_mem. reflexivity.
Qed.

Lemma cert_regs : run_certify.(vm_regs) = run_pnew3.(vm_regs).
Proof.
  rewrite run_certify_step, run_pnew3_step.
  rewrite abs_certify_regs, abs_pnew_regs. reflexivity.
Qed.

Lemma cert_pc : run_certify.(vm_pc) = run_pnew3.(vm_pc).
Proof.
  rewrite run_certify_step, run_pnew3_step.
  rewrite abs_certify_pc, abs_pnew_pc. reflexivity.
Qed.

Lemma cert_mu : run_certify.(vm_mu) = run_pnew3.(vm_mu).
Proof.
  rewrite run_certify_step, run_pnew3_step.
  rewrite abs_certify_mu, abs_pnew_mu.
  unfold init_state. reflexivity.
Qed.

Lemma cert_certified_differs :
  run_certify.(vm_certified) <> run_pnew3.(vm_certified).
Proof.
  rewrite run_certify_step, run_pnew3_step.
  rewrite abs_certify_certified, abs_pnew_certified.
  unfold init_state. discriminate.
Qed.

(** THEOREM (certified axis): two reachable runs sharing the full classical
    shadow AND μ, disagreeing on a run-determined field (vm_certified). *)
Theorem mu_cert_not_complete_over_runs :
  exists s1 s2 : VMState,
    reachable s1 /\ reachable s2 /\
    s1.(vm_mem)  = s2.(vm_mem)  /\
    s1.(vm_regs) = s2.(vm_regs) /\
    s1.(vm_pc)   = s2.(vm_pc)   /\
    s1.(vm_mu)   = s2.(vm_mu)   /\
    s1.(vm_certified) <> s2.(vm_certified).
Proof.
  exists run_certify, run_pnew3.
  split. { exact run_certify_reachable. }
  split. { exact run_pnew3_reachable. }
  split. { exact cert_mem. }
  split. { exact cert_regs. }
  split. { exact cert_pc. }
  split. { exact cert_mu. }
  exact cert_certified_differs.
Qed.

(** vm_certified does not factor through μ on reachable states: there is no
    g : nat → bool with vm_certified s = g (vm_mu s) for every run. *)
Theorem certified_does_not_factor_through_mu :
  ~ exists g : nat -> bool,
      forall s, reachable s -> s.(vm_certified) = g (s.(vm_mu)).
Proof.
  intros [g Hg].
  assert (HA := Hg run_certify run_certify_reachable).
  assert (HB := Hg run_pnew3   run_pnew3_reachable).
  rewrite cert_mu in HA.
  apply cert_certified_differs.
  rewrite HA, HB. reflexivity.
Qed.

(** ═══════════════════════════════════════════════════════════════════════════
    §2.  GRAPH AXIS — equal (mem, regs, pc, μ, certified), differing vm_graph.

    Witnesses: pnew [] 0 (conses one module) vs mdlacc 0 0 (graph-preserving
    no-op). The mdlacc helper lemmas below mirror the abs_pnew_* lemmas already
    in NecessityAbstract.v.
    ═══════════════════════════════════════════════════════════════════════════ *)

Lemma mdlacc_mem : forall s m c,
  (vm_apply s (instr_mdlacc m c)).(vm_mem) = s.(vm_mem).
Proof. intros. unfold vm_apply, advance_state. reflexivity. Qed.

Lemma mdlacc_regs : forall s m c,
  (vm_apply s (instr_mdlacc m c)).(vm_regs) = s.(vm_regs).
Proof. intros. unfold vm_apply, advance_state. reflexivity. Qed.

Lemma mdlacc_pc : forall s m c,
  (vm_apply s (instr_mdlacc m c)).(vm_pc) = S s.(vm_pc).
Proof. intros. unfold vm_apply, advance_state. reflexivity. Qed.

Lemma mdlacc_mu : forall s m c,
  (vm_apply s (instr_mdlacc m c)).(vm_mu) = s.(vm_mu) + c.
Proof. intros. unfold vm_apply, advance_state, apply_cost. reflexivity. Qed.

Lemma mdlacc_certified : forall s m c,
  (vm_apply s (instr_mdlacc m c)).(vm_certified) = s.(vm_certified).
Proof. intros. unfold vm_apply, advance_state. reflexivity. Qed.

Lemma mdlacc_graph : forall s m c,
  (vm_apply s (instr_mdlacc m c)).(vm_graph) = s.(vm_graph).
Proof. intros. unfold vm_apply, advance_state. reflexivity. Qed.

(* PNEW conses exactly one module onto the partition graph. *)
Lemma pnew_module_count_succ : forall s r c,
  length (pg_modules ((vm_apply s (instr_pnew r c)).(vm_graph)))
  = S (length (pg_modules s.(vm_graph))).
Proof.
  intros s r c. unfold vm_apply. cbv zeta.
  destruct (graph_add_module s.(vm_graph)
              (List.seq 0 (length (normalize_region r))) []) as [g' mid] eqn:E.
  unfold advance_state. cbn [vm_graph].
  unfold graph_add_module in E. injection E as Hg' _.
  subst g'. cbn [pg_modules]. reflexivity.
Qed.

Definition run_pnew0  : VMState := exec_trace_from init_state [instr_pnew [] 0].
Definition run_mdlacc : VMState := exec_trace_from init_state [instr_mdlacc 0 0].

Lemma run_pnew0_reachable : reachable run_pnew0.
Proof. unfold run_pnew0. apply reachable_from_trace. Qed.

Lemma run_mdlacc_reachable : reachable run_mdlacc.
Proof. unfold run_mdlacc. apply reachable_from_trace. Qed.

Lemma run_pnew0_step : run_pnew0 = vm_apply init_state (instr_pnew [] 0).
Proof. reflexivity. Qed.

Lemma run_mdlacc_step : run_mdlacc = vm_apply init_state (instr_mdlacc 0 0).
Proof. reflexivity. Qed.

(* init_state's graph carries zero modules. *)
Lemma init_modules_zero : length (pg_modules init_state.(vm_graph)) = 0.
Proof. unfold init_state, init_graph. reflexivity. Qed.

Lemma graph_pair_mem : run_pnew0.(vm_mem) = run_mdlacc.(vm_mem).
Proof.
  rewrite run_pnew0_step, run_mdlacc_step.
  rewrite abs_pnew_mem, mdlacc_mem. reflexivity.
Qed.

Lemma graph_pair_regs : run_pnew0.(vm_regs) = run_mdlacc.(vm_regs).
Proof.
  rewrite run_pnew0_step, run_mdlacc_step.
  rewrite abs_pnew_regs, mdlacc_regs. reflexivity.
Qed.

Lemma graph_pair_pc : run_pnew0.(vm_pc) = run_mdlacc.(vm_pc).
Proof.
  rewrite run_pnew0_step, run_mdlacc_step.
  rewrite abs_pnew_pc, mdlacc_pc. reflexivity.
Qed.

Lemma graph_pair_mu : run_pnew0.(vm_mu) = run_mdlacc.(vm_mu).
Proof.
  rewrite run_pnew0_step, run_mdlacc_step.
  rewrite abs_pnew_mu, mdlacc_mu.
  unfold init_state. reflexivity.
Qed.

Lemma graph_pair_certified :
  run_pnew0.(vm_certified) = run_mdlacc.(vm_certified).
Proof.
  rewrite run_pnew0_step, run_mdlacc_step.
  rewrite abs_pnew_certified, mdlacc_certified. reflexivity.
Qed.

Lemma graph_pair_differs : run_pnew0.(vm_graph) <> run_mdlacc.(vm_graph).
Proof.
  intro H.
  assert (Hp : length (pg_modules run_pnew0.(vm_graph)) = 1).
  { rewrite run_pnew0_step.
    rewrite pnew_module_count_succ.
    rewrite init_modules_zero. reflexivity. }
  assert (Hm : length (pg_modules run_mdlacc.(vm_graph)) = 0).
  { rewrite run_mdlacc_step.
    rewrite mdlacc_graph.
    exact init_modules_zero. }
  rewrite H in Hp. rewrite Hm in Hp. discriminate.
Qed.

(** THEOREM (graph axis): two reachable runs sharing the full classical shadow,
    μ, AND vm_certified, disagreeing only on vm_graph. *)
Theorem mu_graph_not_complete_over_runs :
  exists s1 s2 : VMState,
    reachable s1 /\ reachable s2 /\
    s1.(vm_mem)  = s2.(vm_mem)  /\
    s1.(vm_regs) = s2.(vm_regs) /\
    s1.(vm_pc)   = s2.(vm_pc)   /\
    s1.(vm_mu)   = s2.(vm_mu)   /\
    s1.(vm_certified) = s2.(vm_certified) /\
    s1.(vm_graph) <> s2.(vm_graph).
Proof.
  exists run_pnew0, run_mdlacc.
  split. { exact run_pnew0_reachable. }
  split. { exact run_mdlacc_reachable. }
  split. { exact graph_pair_mem. }
  split. { exact graph_pair_regs. }
  split. { exact graph_pair_pc. }
  split. { exact graph_pair_mu. }
  split. { exact graph_pair_certified. }
  exact graph_pair_differs.
Qed.

(** vm_graph does not factor through μ on reachable states. *)
Theorem graph_does_not_factor_through_mu :
  ~ exists g : nat -> PartitionGraph,
      forall s, reachable s -> s.(vm_graph) = g (s.(vm_mu)).
Proof.
  intros [g Hg].
  assert (HA := Hg run_pnew0  run_pnew0_reachable).
  assert (HB := Hg run_mdlacc run_mdlacc_reachable).
  rewrite graph_pair_mu in HA.
  apply graph_pair_differs.
  rewrite HA, HB. reflexivity.
Qed.

(** ═══════════════════════════════════════════════════════════════════════════
    §3.  HEADLINE — μ is not the universal forgotten coordinate, over runs.

    Both axes at once: there are run-determined, classically-invisible fields
    (vm_certified and vm_graph) that do NOT factor through μ even when the
    classical shadow is fixed. The over-runs complement to
    thiele_state_three_component_independence.
    ═══════════════════════════════════════════════════════════════════════════ *)

Theorem mu_not_complete_invariant_over_runs :
  (* certified axis: equal shadow + μ, differing certified *)
  (exists s1 s2 : VMState,
     reachable s1 /\ reachable s2 /\
     s1.(vm_mem) = s2.(vm_mem) /\ s1.(vm_regs) = s2.(vm_regs) /\
     s1.(vm_pc) = s2.(vm_pc) /\ s1.(vm_mu) = s2.(vm_mu) /\
     s1.(vm_certified) <> s2.(vm_certified))
  /\
  (* graph axis: equal shadow + μ + certified, differing graph *)
  (exists s1 s2 : VMState,
     reachable s1 /\ reachable s2 /\
     s1.(vm_mem) = s2.(vm_mem) /\ s1.(vm_regs) = s2.(vm_regs) /\
     s1.(vm_pc) = s2.(vm_pc) /\ s1.(vm_mu) = s2.(vm_mu) /\
     s1.(vm_certified) = s2.(vm_certified) /\
     s1.(vm_graph) <> s2.(vm_graph))
  /\
  (* neither field factors through μ over runs *)
  (~ exists g : nat -> bool,
       forall s, reachable s -> s.(vm_certified) = g (s.(vm_mu)))
  /\
  (~ exists g : nat -> PartitionGraph,
       forall s, reachable s -> s.(vm_graph) = g (s.(vm_mu))).
Proof.
  split. { exact mu_cert_not_complete_over_runs. }
  split. { exact mu_graph_not_complete_over_runs. }
  split. { exact certified_does_not_factor_through_mu. }
  exact graph_does_not_factor_through_mu.
Qed.
