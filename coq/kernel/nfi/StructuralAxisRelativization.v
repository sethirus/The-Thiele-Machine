(** StructuralAxisRelativization.v — Rungs B and C of the orthogonality ladder,
    done in the frame the construction actually lives in.

    Rung A (StructuralAxisOrthogonality.v) showed the structural-shortcut reading
    is not a function of the classical (Turing) configuration [forget s]. This
    file pushes that to the remaining rungs — and corrects the frame the original
    blueprint used for Rung C.

    ── Rung B: survives any classical oracle (relativized orthogonality). ───────
    A classical decider may be handed an oracle. But a *classical* oracle answers
    questions about the *classical* configuration: its answer is itself a function
    of [forget s]. So a decider equipped with any such oracle is still a function
    of [forget s], and Rung A kills it. The halting oracle is the special case.

    The triviality here IS the content. Baker–Gill–Solovay is hard precisely
    because *computational* obstructions need not relativize. An
    *information-theoretic* obstruction relativizes for free: you cannot recover,
    by any oracle, information that is not in the input. That is the whole
    difference between the two axes.

    ── Rung C: mutual independence — and why "Turing-degree incomparability" is
       the wrong instrument. ───────────────────────────────────────────────────
    The blueprint's Rung C asked for Turing-degree incomparability of the two
    axes. That is the wrong frame, and it is provably so:

      [structural_membership_decidable] below proves the structural-shortcut set
      is DECIDABLE from the full VMState — it is a total Boolean function of the
      state. A decidable set is Turing degree 0: it sits *below* halting, hence
      it is Turing-COMPARABLE to the classical axis, not incomparable. (More
      generally, any genuinely undecidable predicate of this Turing-complete VM —
      e.g. "does this program ever fire the cert channel?" — is ≡_T halting, the
      same degree. Two predicates of one Turing-complete machine cannot be
      incomparable degrees.)

    So the genuine independence of the two axes is NOT degree-theoretic; it is
    information-theoretic: each axis is not a function of the other's projection.
    [axes_mutually_independent] states exactly that, with reachable witnesses on
    both sides. This is the honest Rung C: the strongest true statement, in the
    frame where the phenomenon is real, with a theorem ([..._decidable]) that
    actively forecloses the degree-theoretic over-reading.

    NO COQ AXIOMS. NO ADMITS. *)

From Coq Require Import List Arith.PeanoNat Bool.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof.
From Kernel Require Import MuInitiality.
From Kernel Require Import BlindnessRepresentation.
From Kernel Require Import StructuralAxisOrthogonality.

(** ═══════════════════════════════════════════════════════════════════════════
    §1.  RUNG B — the obstruction survives any classical oracle.
    ═══════════════════════════════════════════════════════════════════════════ *)

(** A classical oracle of *any* answer type [A] is a function of the classical
    configuration [forget s]. A decider that reads the classical configuration
    and consults such an oracle is therefore *still* a function of [forget s] —
    so Rung A's keystone defeats it. No oracle can supply information the
    classical configuration does not contain. *)
Theorem structural_axis_survives_any_classical_oracle :
  forall (A : Type) (oracle : TMSnapshot -> A) (decode : TMSnapshot -> A -> bool),
    ~ (forall s : VMState,
         decode (forget s) (oracle (forget s)) = admits_structural_shortcut_bool s).
Proof.
  intros A oracle decode Hdec.
  apply structural_shortcut_not_function_of_classical.
  exists (fun cfg => decode cfg (oracle cfg)).
  intro s. exact (Hdec s).
Qed.

(** The headline case: even given a halting oracle on the classical
    configuration, no classical decider is correct about structural-shortcut
    admittance. This is the relativized form of Rung A — Baker–Gill–Solovay's
    question for this predicate — and it holds because the impossibility is
    information-theoretic, not computational. *)
Corollary structural_axis_survives_halting_oracle :
  forall (halts : TMSnapshot -> bool) (decode : TMSnapshot -> bool -> bool),
    ~ (forall s : VMState,
         decode (forget s) (halts (forget s)) = admits_structural_shortcut_bool s).
Proof.
  intros halts decode.
  exact (structural_axis_survives_any_classical_oracle bool halts decode).
Qed.

(** Even a decider with a *finite tuple* of independent classical oracles is a
    function of [forget s], hence defeated. (Stated for two oracles; the same
    move handles any fixed arity.) *)
Corollary structural_axis_survives_two_oracles :
  forall (A B : Type) (o1 : TMSnapshot -> A) (o2 : TMSnapshot -> B)
         (decode : TMSnapshot -> A -> B -> bool),
    ~ (forall s : VMState,
         decode (forget s) (o1 (forget s)) (o2 (forget s))
         = admits_structural_shortcut_bool s).
Proof.
  intros A B o1 o2 decode Hdec.
  apply structural_shortcut_not_function_of_classical.
  exists (fun cfg => decode cfg (o1 cfg) (o2 cfg)).
  intro s. exact (Hdec s).
Qed.

(** ═══════════════════════════════════════════════════════════════════════════
    §2.  RUNG C, reverse direction — a classical quantity is not a function of
         the structural channel either.

    [struct_only] keeps only the structural channel [csr_cert_addr] — the field
    [forget] drops — and discards the classical configuration. Two reachable
    states ([init_state] and [run_cert_unset]) share [struct_only = 0] but differ
    on the classical quantity [vm_pc] (0 vs 3). So [vm_pc] is not a function of
    the structural channel.
    ═══════════════════════════════════════════════════════════════════════════ *)

Definition struct_only (s : VMState) : nat := (vm_csrs s).(csr_cert_addr).

Lemma struct_only_init : struct_only init_state = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma struct_only_run_cert_unset : struct_only run_cert_unset = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma pc_init : init_state.(vm_pc) = 0.
Proof. reflexivity. Qed.

Lemma pc_run_cert_unset : run_cert_unset.(vm_pc) = 3.
Proof. vm_compute. reflexivity. Qed.

Theorem classical_pc_not_function_of_structural :
  ~ exists phi : nat -> nat, forall s : VMState, phi (struct_only s) = s.(vm_pc).
Proof.
  intros [phi Hphi].
  pose proof (Hphi init_state) as H0.
  pose proof (Hphi run_cert_unset) as H3.
  rewrite struct_only_init, pc_init in H0.
  rewrite struct_only_run_cert_unset, pc_run_cert_unset in H3.
  rewrite H0 in H3. discriminate H3.
Qed.

(** ═══════════════════════════════════════════════════════════════════════════
    §3.  RUNG C — mutual information-theoretic independence.

    Neither axis is a function of the other's projection: the structural reading
    is not a function of the classical configuration (Rung A), and the classical
    program counter is not a function of the structural channel (§2). This is the
    honest "the two axes are independent" — in the information-theoretic frame,
    where it is true.
    ═══════════════════════════════════════════════════════════════════════════ *)

Theorem axes_mutually_independent :
  (* structural reading is not a function of the classical configuration *)
  (forall decode : TMSnapshot -> bool,
     ~ (forall s, decode (forget s) = admits_structural_shortcut_bool s))
  /\
  (* classical program counter is not a function of the structural channel *)
  (~ exists phi : nat -> nat, forall s : VMState, phi (struct_only s) = s.(vm_pc)).
Proof.
  split.
  - exact structural_axis_invisible_to_classical.
  - exact classical_pc_not_function_of_structural.
Qed.

(** ═══════════════════════════════════════════════════════════════════════════
    §4.  Why this is NOT Turing-degree incomparability — and must not be read so.

    The structural-shortcut set is decidable from the full state: membership is a
    total Boolean function. A decidable set is Turing degree 0 — below halting,
    hence COMPARABLE to the classical axis. The independence in §3 is therefore
    information-theoretic (projection loss), not degree-theoretic. This theorem
    is the formal guard against reading [axes_mutually_independent] as a
    Turing-degree separation: it is not one, and cannot be, because the predicate
    is computable.
    ═══════════════════════════════════════════════════════════════════════════ *)

Theorem structural_membership_decidable :
  forall s : VMState,
    {admits_structural_shortcut_bool s = true} +
    {~ admits_structural_shortcut_bool s = true}.
Proof.
  intro s. destruct (admits_structural_shortcut_bool s).
  - left. reflexivity.
  - right. discriminate.
Qed.

(** The Prop shadow of the above (a total Boolean predicate takes a definite
    value), used as the degree-guard conjunct in the fused ladder, where a
    [Set]-valued [sumbool] cannot appear under [/\]. *)
Lemma structural_membership_total :
  forall s : VMState,
    admits_structural_shortcut_bool s = true \/
    admits_structural_shortcut_bool s = false.
Proof.
  intro s. destruct (admits_structural_shortcut_bool s).
  - left. reflexivity.
  - right. reflexivity.
Qed.

(** ═══════════════════════════════════════════════════════════════════════════
    §5.  The ladder, fused: A (proven elsewhere), B, C, and the degree guard.
    ═══════════════════════════════════════════════════════════════════════════ *)

Theorem orthogonality_ladder_B_and_C :
  (* Rung B: survives any classical oracle, halting included *)
  (forall (A : Type) (oracle : TMSnapshot -> A) (decode : TMSnapshot -> A -> bool),
     ~ (forall s, decode (forget s) (oracle (forget s))
                  = admits_structural_shortcut_bool s))
  /\
  (* Rung C: the two axes are mutually independent (information-theoretically) *)
  ((forall decode : TMSnapshot -> bool,
      ~ (forall s, decode (forget s) = admits_structural_shortcut_bool s))
   /\
   (~ exists phi : nat -> nat, forall s, phi (struct_only s) = s.(vm_pc)))
  /\
  (* and that independence is NOT a Turing-degree gap: the predicate is total/
     decidable (the strong [sumbool] form is [structural_membership_decidable]) *)
  (forall s : VMState,
     admits_structural_shortcut_bool s = true \/
     admits_structural_shortcut_bool s = false).
Proof.
  split; [| split].
  - exact structural_axis_survives_any_classical_oracle.
  - exact axes_mutually_independent.
  - exact structural_membership_total.
Qed.
