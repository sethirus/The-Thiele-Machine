(** MuCore.v — the whole claim, small enough to read in one sitting.

    I don't trust an informal argument, my own least of all, so here is the
    core of the project with nothing to take on faith. A machine state is the
    classical part you already know (memory, registers, a program counter)
    plus two fields classical machines never carry: a cost ledger [mu] and a
    bit that says [cert]ified. One law, A2: a single step that flips [cert]
    from false to true costs at least 1, and it pays in the same step, not in
    a checker you could skip. Everything below falls out of that, and every
    theorem ends in Print Assumptions reporting "Closed under the global
    context" — no axioms, mine or anyone else's. What it shows:

      1.  mu is conserved exactly (ledger = sum of step costs)        [mu_conservation]
      2.  A2 holds as a theorem of the step relation                  [a2]
      3.  every uncertified->certified trace pays >= 1                [nfi_floor]
      4.  only the CERTIFY instruction can flip the flag              [only_certify_certifies]
      5.  two programs with IDENTICAL classical state (mem, regs, pc)
          end with different (mu, cert): the receipt is not a function
          of the classical shadow                                     [receipt_separation,
                                                                       no_mu_oracle, no_cert_oracle]
      6.  the classical machine is exactly the zero-cost fragment:
          classical programs preserve (mu, cert) and commute with the
          projection onto classical state                             [classical_conservativity,
                                                                       classical_embedding]

    Dependencies: Coq standard library only.  No vendor libraries, no
    axioms, no Admitted.  Each theorem ends with Print Assumptions; every
    one reports "Closed under the global context".

    This is a distillation.  The full kernel generalises each result:
      1 -> coq/kernel/foundation/MuLedgerConservation.v  (vm_apply_mu)
      2 -> coq/kernel/nfi/UniversalCertificationCost.v   (cs_cert_costs, any substrate)
      3 -> coq/kernel/nfi/UniversalCertificationCost.v   (universal_nfi_any_substrate)
      4 -> coq/kernel/foundation/VMStep.v                (vm_apply_preserves_certified_non_certify)
      5 -> coq/ReceiptTheorem.v, coq/NecessityOfMuLedger.v
      6 -> coq/kernel/foundation/ProperSubsumption.v, ClassicalConservativity.v (D3)

    Build:  coqc minimal/MuCore.v        (seconds, from a clean checkout)
    Check:  every Print Assumptions line below must report
            "Closed under the global context".                              *)

(* INQUISITOR NOTE: proof-connectivity gap suppressed, on purpose.
   This file imports nothing but the Coq standard library, and that is the
   whole point: anyone can re-check it from a clean checkout with zero trust
   in me or in the kernel.  It re-proves the kernel results from scratch
   rather than importing them; the connected, general versions live in
   coq/kernel/ and the header docstring above maps each result to its
   counterpart.  Wiring this into the foundation chain would pull in the
   kernel, break the bare-coqc clean-checkout build that tests/test_minimal_core.py
   guards, and defeat the entire purpose of a minimal core.  So it stays
   standalone, and this note tells the gate why. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.

(* ----------------------------------------------------------------- *)
(* State: a classical machine (mem, regs, pc) plus the structural     *)
(* axis (mu, cert).  Nothing else.                                    *)
(* ----------------------------------------------------------------- *)

Record state := mk_state {
  st_mem  : list nat;
  st_regs : list nat;
  st_pc   : nat;
  st_mu   : nat;
  st_cert : bool
}.

(* The classical shadow: what a Turing/RAM observer sees. *)
Record shadow := mk_shadow {
  sh_mem  : list nat;
  sh_regs : list nat;
  sh_pc   : nat
}.

Definition strict_shadow (s : state) : shadow :=
  mk_shadow (st_mem s) (st_regs s) (st_pc s).

(* ----------------------------------------------------------------- *)
(* The minimal ISA: one classical compute primitive (STORE) and one   *)
(* certification primitive (CERTIFY).  Subsumption needs something    *)
(* classical to project to; A2 needs something to enforce.            *)
(* ----------------------------------------------------------------- *)

Fixpoint upd (l : list nat) (n v : nat) : list nat :=
  match l, n with
  | [], _ => []
  | _ :: t, 0 => v :: t
  | h :: t, S k => h :: upd t k v
  end.

Inductive instr : Type :=
| i_store   (addr v : nat)   (* classical compute: cost 0          *)
| i_certify (delta : nat).   (* certification:     cost S delta    *)

Definition cost (i : instr) : nat :=
  match i with
  | i_store _ _ => 0
  | i_certify d => S d
  end.

(* The step relation.  Note: the mu update and the cert flip happen in
   the SAME step.  A2 is not a checker run after the fact; it is the
   transition law itself. *)
Definition step (s : state) (i : instr) : state :=
  match i with
  | i_store a v =>
      mk_state (upd (st_mem s) a v) (st_regs s) (S (st_pc s))
               (st_mu s + cost i) (st_cert s)
  | i_certify d =>
      mk_state (st_mem s) (st_regs s) (S (st_pc s))
               (st_mu s + cost i) true
  end.

Definition run (p : list instr) (s : state) : state :=
  fold_left step p s.

Fixpoint total_cost (p : list instr) : nat :=
  match p with
  | [] => 0
  | i :: rest => cost i + total_cost rest
  end.

(* ----------------------------------------------------------------- *)
(* 1. Exact ledger conservation.                                      *)
(* ----------------------------------------------------------------- *)

Theorem mu_conservation :
  forall (s : state) (i : instr),
    st_mu (step s i) = st_mu s + cost i.
Proof. intros s [a v | d]; reflexivity. Qed.

Theorem mu_conservation_trace :
  forall (p : list instr) (s : state),
    st_mu (run p s) = st_mu s + total_cost p.
Proof.
  induction p as [| i rest IH]; intros s; simpl.
  - lia.
  - unfold run in *. simpl. rewrite IH, mu_conservation. lia.
Qed.

(* ----------------------------------------------------------------- *)
(* 2. A2 as a theorem of the step relation: a single step that flips  *)
(*    certification from false to true costs at least 1.              *)
(* ----------------------------------------------------------------- *)

Theorem a2 :
  forall (s : state) (i : instr),
    st_cert s = false ->
    st_cert (step s i) = true ->
    cost i >= 1.
Proof.
  intros s [a v | d] Hbefore Hafter; simpl in *.
  - congruence.   (* i_store cannot flip the flag *)
  - lia.          (* i_certify costs S d >= 1     *)
Qed.

(* ----------------------------------------------------------------- *)
(* 3. The trace-level floor (No Free Insight, minimal form): any run  *)
(*    from an uncertified state to a certified state has total cost   *)
(*    at least 1.                                                     *)
(* ----------------------------------------------------------------- *)

Theorem nfi_floor :
  forall (p : list instr) (s : state),
    st_cert s = false ->
    st_cert (run p s) = true ->
    total_cost p >= 1.
Proof.
  induction p as [| i rest IH]; intros s Hbefore Hafter; simpl in *.
  - unfold run in Hafter. simpl in Hafter. congruence.
  - destruct (st_cert (step s i)) eqn:Hmid.
    + pose proof (a2 s i Hbefore Hmid). lia.
    + unfold run in Hafter. simpl in Hafter.
      pose proof (IH (step s i) Hmid Hafter). lia.
Qed.

(* ----------------------------------------------------------------- *)
(* 4. Only CERTIFY can flip the flag: the instruction set contains no *)
(*    free side door.  (A buggy simulator that "skips the charge" has *)
(*    no instruction to express itself with.)                         *)
(* ----------------------------------------------------------------- *)

Theorem only_certify_certifies :
  forall (s : state) (i : instr),
    st_cert s = false ->
    st_cert (step s i) = true ->
    exists d, i = i_certify d.
Proof.
  intros s [a v | d] Hbefore Hafter; simpl in *.
  - congruence.
  - exists d. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(* 5. The receipt separation: two one-instruction programs whose      *)
(*    final classical states are IDENTICAL and whose receipts differ. *)
(*    Hence no function of the classical shadow recovers mu or cert.  *)
(* ----------------------------------------------------------------- *)

Definition s0 : state := mk_state [] [] 0 0 false.

Definition state_A : state := step s0 (i_certify 0).  (* mu = 1, cert = true  *)
Definition state_B : state := step s0 (i_store 0 0).  (* mu = 0, cert = false *)

Theorem receipt_separation :
  strict_shadow state_A = strict_shadow state_B /\
  st_mu state_A <> st_mu state_B /\
  st_cert state_A <> st_cert state_B.
Proof.
  unfold state_A, state_B, s0; simpl.
  repeat split; simpl; congruence.
Qed.

Theorem no_mu_oracle :
  ~ exists f : shadow -> nat,
      forall s : state, f (strict_shadow s) = st_mu s.
Proof.
  intros [f Hf].
  pose proof (Hf state_A) as HA.
  pose proof (Hf state_B) as HB.
  destruct receipt_separation as [Heq [Hmu _]].
  rewrite Heq in HA. congruence.
Qed.

Theorem no_cert_oracle :
  ~ exists f : shadow -> bool,
      forall s : state, f (strict_shadow s) = st_cert s.
Proof.
  intros [f Hf].
  pose proof (Hf state_A) as HA.
  pose proof (Hf state_B) as HB.
  destruct receipt_separation as [Heq [_ Hcert]].
  rewrite Heq in HA. congruence.
Qed.

(* ----------------------------------------------------------------- *)
(* 6. The classical machine is exactly the zero-cost fragment.        *)
(*    A bare classical machine over (mem, regs, pc), lifted by        *)
(*    setting mu = 0 and cert = false, runs every classical program   *)
(*    with the same classical state at every step, and the structural *)
(*    axis stays dormant.  Subsumption, conservativity, projection.   *)
(* ----------------------------------------------------------------- *)

Definition is_classical (i : instr) : bool :=
  match i with
  | i_store _ _ => true
  | i_certify _ => false
  end.

(* The bare classical machine: same compute, no structural axis. *)
Definition cstep (c : shadow) (i : instr) : shadow :=
  match i with
  | i_store a v => mk_shadow (upd (sh_mem c) a v) (sh_regs c) (S (sh_pc c))
  | i_certify _ => c   (* not in the classical fragment *)
  end.

Definition crun (p : list instr) (c : shadow) : shadow :=
  fold_left cstep p c.

Lemma run_cons : forall i p s, run (i :: p) s = run p (step s i).
Proof. reflexivity. Qed.

Lemma crun_cons : forall i p c, crun (i :: p) c = crun p (cstep c i).
Proof. reflexivity. Qed.

Definition lift (c : shadow) : state :=
  mk_state (sh_mem c) (sh_regs c) (sh_pc c) 0 false.

(* Conservativity: classical programs leave the structural axis at its
   lifted value — zero cost, uncertified.  D3, minimal form. *)
Theorem classical_conservativity :
  forall (p : list instr) (s : state),
    forallb is_classical p = true ->
    st_mu (run p s) = st_mu s /\ st_cert (run p s) = st_cert s.
Proof.
  induction p as [| i rest IH]; intros s Hcl.
  - split; reflexivity.
  - simpl in Hcl. apply andb_true_iff in Hcl. destruct Hcl as [Hi Hrest].
    destruct i as [a v | d]; [| discriminate].
    rewrite run_cons.
    destruct (IH (step s (i_store a v)) Hrest) as [Hmu Hcert].
    rewrite Hmu, Hcert. simpl. split; [lia | reflexivity].
Qed.

(* Subsumption: the lifted run projects back to exactly the classical
   run, step for step.  The classical machine IS the projection of the
   substrate running in its zero-cost fragment. *)
Theorem classical_embedding :
  forall (p : list instr) (c : shadow),
    forallb is_classical p = true ->
    strict_shadow (run p (lift c)) = crun p c.
Proof.
  intros p.
  induction p as [| i rest IH]; intros c Hcl.
  - destruct c; reflexivity.
  - simpl in Hcl. apply andb_true_iff in Hcl. destruct Hcl as [Hi Hrest].
    destruct i as [a v | d]; [| discriminate].
    rewrite run_cons, crun_cons.
    rewrite <- (IH (cstep c (i_store a v)) Hrest).
    reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(* Assumption audit.  Every line below must print                     *)
(* "Closed under the global context".                                 *)
(* ----------------------------------------------------------------- *)

Print Assumptions mu_conservation.
Print Assumptions mu_conservation_trace.
Print Assumptions a2.
Print Assumptions nfi_floor.
Print Assumptions only_certify_certifies.
Print Assumptions receipt_separation.
Print Assumptions no_mu_oracle.
Print Assumptions no_cert_oracle.
Print Assumptions classical_conservativity.
Print Assumptions classical_embedding.
