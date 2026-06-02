(** GenRealizability: a dimension-polymorphic GENUINE PSD predicate, and the
    bridge that exhibits the 5x5 CHSH PSD as a special case of it (W2-M1).

    The point of this file is to stop `quantum_realizable` being a standalone
    5x5 coincidence. `psd_n` below is the REAL quadratic-form-nonnegativity over
    EVERY vector — the full double sum over all i,j, NOT a diagonal-only sham
    like SemidefiniteProgramming.PSD {n} is for n >= 6. The dimension lives in
    the top index `top` (= dimension - 1): `psd_n top M` quantifies the genuine
    form summed over indices 0..top.

    The bridge `psd_n_unfold_5` is dimension-GENERIC in its reason: a nat-indexed
    quadratic form summed over 0..d-1 equals the Fin-restricted form under index
    correspondence. Nothing in that reason is special to 5, so it carries to 9
    (W2-M4) with a longer finite unfolding and no new idea. The only 5-specific
    content here is the finite reduction (`cbn`) of a literal-length sum.

    (We use ConstructivePSD's exported `RealNumber := Rdefinitions.R` notation
    throughout, because `From Coq Require Import Fin` shadows the bare `R`.) *)

From Coq Require Import Reals Lra Lia.
From Coq Require Import Fin.
From Coq Require Import Arith.                     (* lt_dec *)
From Coq Require Import FunctionalExtensionality.  (* matrix equality by funext *)
Local Open Scope R_scope.

From Kernel Require Import ConstructivePSD.
From Kernel Require Import MinorConstraints.   (* sum_n : nat -> (nat -> R) -> R *)
From Kernel Require Import NPAMomentMatrix.     (* quantum_realizable, npa_to_matrix, zero_marginal_npa *)
From Kernel Require Import MuLedgerQuantumBridge. (* zero_marginal_column_contractive *)
From Kernel Require Import QuantumPartitionPSD.   (* column_contractive_iff_quantum_realizable *)
From Kernel Require Import QuantumPartitionPSD_1AB. (* PSD9, quad9, nat_matrix_to_fin9, the dim-9 headline *)
From Kernel Require Import VMState VMStep SimulationProof. (* VMState, vm_apply, instr_chsh_lassert: the dim-5 instance is a VM step *)

(** Genuine quadratic form of a nat-indexed matrix over indices 0..top.
    Full double sum: every (i,j) pair, off-diagonal included. *)
Definition quad_n (top : nat) (M : nat -> nat -> RealNumber) (v : nat -> RealNumber)
  : RealNumber :=
  sum_n top (fun i => sum_n top (fun j => v i * M i j * v j)).

(** Genuine PSD: every real vector gives a nonnegative quadratic form.
    This is NOT diagonal-only; quad_n sums all i,j including i <> j. *)
Definition psd_n (top : nat) (M : nat -> nat -> RealNumber) : Prop :=
  forall v : nat -> RealNumber, quad_n top M v >= 0.

(** Explicit nat->R extension of a Fin5 vector (0 outside the live range). *)
Definition vec5_to_nat (v : Fin5 -> RealNumber) : nat -> RealNumber :=
  fun n => match n with
           | 0 => v F1
           | 1 => v (FS F1)
           | 2 => v (FS (FS F1))
           | 3 => v (FS (FS (FS F1)))
           | 4 => v (FS (FS (FS (FS F1))))
           | _ => 0
           end.

(** Restriction of a nat-vector to Fin5 (same shape as nat_matrix_to_fin5). *)
Definition nat_to_vec5 (v : nat -> RealNumber) : Fin5 -> RealNumber :=
  fun i => v (fin_to_nat i).

(** The two quadratic forms agree at dimension 5 (top index 4), in both
    transport directions. Pure ring identities after the finite sums and the
    Fin.to_nat indices are computed. *)
Lemma quad_n4_eq_quad5_ext : forall (M : Matrix 5) (v : Fin5 -> RealNumber),
  quad_n 4 M (vec5_to_nat v) = quad5 (nat_matrix_to_fin5 M) v.
Proof.
  intros M v.
  unfold quad_n, quad5, sum_fin5, nat_matrix_to_fin5, vec5_to_nat, fin_to_nat.
  cbn [sum_n Fin.to_nat proj1_sig].
  ring.
Qed.

Lemma quad_n4_eq_quad5_restr : forall (M : Matrix 5) (v : nat -> RealNumber),
  quad5 (nat_matrix_to_fin5 M) (nat_to_vec5 v) = quad_n 4 M v.
Proof.
  intros M v.
  unfold quad_n, quad5, sum_fin5, nat_matrix_to_fin5, nat_to_vec5, fin_to_nat.
  cbn [sum_n Fin.to_nat proj1_sig].
  ring.
Qed.

(** W2-M1. The bridge. Genuine PSD of the nat-indexed 5x5 matrix (top index 4)
    is equivalent to the genuine PSD5 of its Fin5 restriction. Neither side is
    weakened: both quantify the full quadratic form over all vectors. *)
Lemma psd_n_unfold_5 : forall M : Matrix 5,
  psd_n 4 M <-> PSD5 (nat_matrix_to_fin5 M).
Proof.
  intro M. split.
  - intros H v.
    rewrite <- quad_n4_eq_quad5_ext.
    apply H.
  - intros H v.
    rewrite <- quad_n4_eq_quad5_restr.
    apply H.
Qed.

Print Assumptions psd_n_unfold_5.

(** ── W2-M2: the abstract realizable claim and its CHSH adapter ──────────── *)

(** A certified claim presented for realizability: a finite dimension (carried
    as the top index = dimension - 1) and the nat-indexed moment/layout matrix
    it induces. This is the abstract object the projection acts on; the CHSH
    correlator is one instance of it (chsh_claim below). *)
Record RealizableClaim := mk_realizable_claim {
  rc_top    : nat;
  rc_matrix : nat -> nat -> RealNumber;
}.

(** Symmetry over the live range 0..top — the polymorphic analogue of
    symmetric5. *)
Definition symmetric_n (top : nat) (M : nat -> nat -> RealNumber) : Prop :=
  forall i j, (i <= top)%nat -> (j <= top)%nat -> M i j = M j i.

(** THE GENERAL REALIZABILITY PROJECTION. A claim is realizable iff its moment
    matrix is symmetric and genuinely PSD over the live range. Dimension-
    polymorphic by construction: nothing here is fixed to 5. *)
Definition GenRealizable (c : RealizableClaim) : Prop :=
  symmetric_n (rc_top c) (rc_matrix c) /\ psd_n (rc_top c) (rc_matrix c).

(** The CHSH correlator as a realizable claim: the NPA-1 layout at dimension 5
    (top index 4). *)
Definition chsh_claim (e00 e01 e10 e11 : RealNumber) : RealizableClaim :=
  mk_realizable_claim 4 (npa_to_matrix (zero_marginal_npa e00 e01 e10 e11)).

(** Symmetry bridge, the parallel of psd_n_unfold_5 and equally dimension-
    generic: live-range symmetry of the nat matrix is symmetric5 of its Fin5
    restriction. *)
Lemma symmetric_n_unfold_5 : forall M : Matrix 5,
  symmetric_n 4 M <-> symmetric5 (nat_matrix_to_fin5 M).
Proof.
  intro M. unfold symmetric_n, symmetric5, nat_matrix_to_fin5. split.
  - intros H i j.
    destruct (Fin.to_nat i) as [a Ha].
    destruct (Fin.to_nat j) as [b Hb].
    simpl.
    apply H; simpl; lia.
  - intros H i j Hi Hj.
    assert (Hi5 : (i < 5)%nat) by lia.
    assert (Hj5 : (j < 5)%nat) by lia.
    specialize (H (Fin.of_nat_lt Hi5) (Fin.of_nat_lt Hj5)).
    rewrite !Fin.to_nat_of_nat in H. simpl in H. exact H.
Qed.

(** W2-M2. The adapter equivalence: the general projection applied to the CHSH
    claim is exactly the existing quantum_realizable predicate. Pure combination
    of the two bridges (psd_n_unfold_5 + symmetric_n_unfold_5) — no new
    mathematics, and the matrix is the SAME on both sides (npa_to_matrix of the
    zero-marginal NPA). No appeal to any Hilbert-space, Born-rule, density-
    matrix, or tensor structure. *)
Theorem chsh_claim_is_zero_marginal_npa :
  forall e00 e01 e10 e11 : RealNumber,
    GenRealizable (chsh_claim e00 e01 e10 e11) <->
    quantum_realizable (zero_marginal_npa e00 e01 e10 e11).
Proof.
  intros e00 e01 e10 e11.
  unfold GenRealizable, chsh_claim, quantum_realizable.
  cbn [rc_top rc_matrix].
  split.
  - intros [Hsym Hpsd]. split.
    + apply (proj1 (symmetric_n_unfold_5 _)). exact Hsym.
    + apply (proj1 (psd_n_unfold_5 _)). exact Hpsd.
  - intros [Hsym Hpsd]. split.
    + apply (proj2 (symmetric_n_unfold_5 _)). exact Hsym.
    + apply (proj2 (psd_n_unfold_5 _)). exact Hpsd.
Qed.

Print Assumptions chsh_claim_is_zero_marginal_npa.

(** ── W2-M3: the headline biconditional, re-derived through GenRealizable ── *)

(** W2-M3. The original CHSH biconditional re-expressed against the GENERAL
    projection. This is a genuine Corollary, not a parallel theorem: it
    re-proves NONE of the hard PSD<->contractivity content. It imports the
    original `column_contractive_iff_quantum_realizable` as a black box and
    composes it with the structural adapter `chsh_claim_is_zero_marginal_npa`
    (which only relates GenRealizable to quantum_realizable via the two genuine
    unfold bridges). The proof is pure proj1/proj2 plumbing.

    The decisive evidence that it is a corollary and not a re-derivation is the
    Print Assumptions DIFF below: this result must carry exactly the axioms the
    original carries, no more. A fourth axiom would mean new content sneaked in. *)
Corollary column_contractive_iff_general_realizable :
  forall e00 e01 e10 e11 : RealNumber,
    zero_marginal_column_contractive e00 e01 e10 e11 <->
    GenRealizable (chsh_claim e00 e01 e10 e11).
Proof.
  intros e00 e01 e10 e11.
  split.
  - intro Hcc.
    apply (proj2 (chsh_claim_is_zero_marginal_npa e00 e01 e10 e11)).
    apply (proj1 (column_contractive_iff_quantum_realizable e00 e01 e10 e11)).
    exact Hcc.
  - intro Hgr.
    apply (proj2 (column_contractive_iff_quantum_realizable e00 e01 e10 e11)).
    apply (proj1 (chsh_claim_is_zero_marginal_npa e00 e01 e10 e11)).
    exact Hgr.
Qed.

(** The two assumption lists, for the diff. The corollary's set must equal (or
    be a subset of) the original's — nothing beyond the headline axioms. *)
Print Assumptions column_contractive_iff_general_realizable.
Print Assumptions column_contractive_iff_quantum_realizable.

(** ── W2-M4: the genericity test — dim-9, reusing the SAME psd_n ─────────── *)

(** The whole point of M4: psd_n_unfold_9 below uses the SAME `psd_n` and the
    SAME `quad_n`/`sum_n` as the dim-5 case — only `top := 8`. No new fold, no
    re-rolled dim-9 PSD predicate. If this compiles, `psd_n` genuinely
    generalized; the dim-5 bridge was not a 5-shaped coincidence. *)

Definition vec9_to_nat (v : Fin9 -> RealNumber) : nat -> RealNumber :=
  fun n => match n with
           | 0 => v j0 | 1 => v j1 | 2 => v j2 | 3 => v j3 | 4 => v j4
           | 5 => v j5 | 6 => v j6 | 7 => v j7 | 8 => v j8 | _ => 0
           end.

Definition nat_to_vec9 (v : nat -> RealNumber) : Fin9 -> RealNumber :=
  fun i => v (fin_to_nat i).

Lemma quad_n8_eq_quad9_ext :
  forall (M : nat -> nat -> RealNumber) (v : Fin9 -> RealNumber),
    quad_n 8 M (vec9_to_nat v) = quad9 (nat_matrix_to_fin9 M) v.
Proof.
  intros M v.
  unfold quad_n, quad9, sum_fin9, nat_matrix_to_fin9, vec9_to_nat, fin_to_nat,
         j0, j1, j2, j3, j4, j5, j6, j7, j8.
  cbn [sum_n Fin.to_nat proj1_sig].
  ring.
Qed.

Lemma quad_n8_eq_quad9_restr :
  forall (M : nat -> nat -> RealNumber) (v : nat -> RealNumber),
    quad9 (nat_matrix_to_fin9 M) (nat_to_vec9 v) = quad_n 8 M v.
Proof.
  intros M v.
  unfold quad_n, quad9, sum_fin9, nat_matrix_to_fin9, nat_to_vec9, fin_to_nat,
         j0, j1, j2, j3, j4, j5, j6, j7, j8.
  cbn [sum_n Fin.to_nat proj1_sig].
  ring.
Qed.

(** W2-M4 core. The SAME `psd_n` (top := 8) is equivalent to the genuine dim-9
    PSD9 of the Fin9 restriction. Identical proof shape to psd_n_unfold_5. *)
Lemma psd_n_unfold_9 :
  forall M : nat -> nat -> RealNumber,
    psd_n 8 M <-> PSD9 (nat_matrix_to_fin9 M).
Proof.
  intro M. split.
  - intros H v.
    rewrite <- quad_n8_eq_quad9_ext.
    apply H.
  - intros H v.
    rewrite <- quad_n8_eq_quad9_restr.
    apply H.
Qed.

Print Assumptions psd_n_unfold_9.

(** ── W2-M4 completion: dim-9 as a RealizableClaim, through GenRealizable ── *)

(** nat -> Fin9, clamping out-of-range to F1 (only 0..8 is ever used). *)
Definition fin9_of_nat (a : nat) : Fin9 :=
  match lt_dec a 9 with
  | left p  => Fin.of_nat_lt p
  | right _ => F1
  end.

(** q1ab_moment_matrix reads only proj1_sig (Fin.to_nat .) of its indices, so it
    depends only on those nat indices — no copy of its 81 arms needed. *)
Lemma q1ab_depends_only_on_index :
  forall e00 e01 e10 e11 g1 g2 g3 g4 g5 (a a' b b' : Fin9),
    proj1_sig (Fin.to_nat a) = proj1_sig (Fin.to_nat a') ->
    proj1_sig (Fin.to_nat b) = proj1_sig (Fin.to_nat b') ->
    q1ab_moment_matrix e00 e01 e10 e11 g1 g2 g3 g4 g5 a b
    = q1ab_moment_matrix e00 e01 e10 e11 g1 g2 g3 g4 g5 a' b'.
Proof.
  intros. unfold q1ab_moment_matrix. rewrite H, H0. reflexivity.
Qed.

(** fin9_of_nat round-trips through the nat index of a Fin9. *)
Lemma fin9_index_roundtrip : forall i : Fin9,
  proj1_sig (Fin.to_nat (fin9_of_nat (proj1_sig (Fin.to_nat i))))
  = proj1_sig (Fin.to_nat i).
Proof.
  intro i. unfold fin9_of_nat.
  destruct (lt_dec (proj1_sig (Fin.to_nat i)) 9) as [p|np].
  - rewrite Fin.to_nat_of_nat. reflexivity.
  - exfalso. apply np. destruct (Fin.to_nat i) as [a Ha]. simpl. exact Ha.
Qed.

(** The nat-indexed q1ab matrix: the SAME moment matrix, addressed by nat. *)
Definition q1ab_nat_matrix
  (e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber) : nat -> nat -> RealNumber :=
  fun a b => q1ab_moment_matrix e00 e01 e10 e11 g1 g2 g3 g4 g5
                                (fin9_of_nat a) (fin9_of_nat b).

(** Its Fin9 restriction is exactly q1ab_moment_matrix — so psd_n_unfold_9 and
    symmetric_n_unfold_9 land on the genuine dim-9 moment matrix. *)
Lemma q1ab_nat_to_fin9_eq :
  forall e00 e01 e10 e11 g1 g2 g3 g4 g5,
    nat_matrix_to_fin9 (q1ab_nat_matrix e00 e01 e10 e11 g1 g2 g3 g4 g5)
    = q1ab_moment_matrix e00 e01 e10 e11 g1 g2 g3 g4 g5.
Proof.
  intros. apply functional_extensionality; intro i.
  apply functional_extensionality; intro j.
  unfold nat_matrix_to_fin9, q1ab_nat_matrix.
  apply q1ab_depends_only_on_index; apply fin9_index_roundtrip.
Qed.

(** Symmetry bridge at dim-9, mirror of symmetric_n_unfold_5. *)
Lemma symmetric_n_unfold_9 : forall M : nat -> nat -> RealNumber,
  symmetric_n 8 M <-> symmetric9 (nat_matrix_to_fin9 M).
Proof.
  intro M. unfold symmetric_n, symmetric9, nat_matrix_to_fin9. split.
  - intros H i j.
    destruct (Fin.to_nat i) as [a Ha].
    destruct (Fin.to_nat j) as [b Hb].
    simpl. apply H; simpl; lia.
  - intros H i j Hi Hj.
    assert (Hi9 : (i < 9)%nat) by lia.
    assert (Hj9 : (j < 9)%nat) by lia.
    specialize (H (Fin.of_nat_lt Hi9) (Fin.of_nat_lt Hj9)).
    rewrite !Fin.to_nat_of_nat in H. simpl in H. exact H.
Qed.

(** The Q_{1+AB} correlator as a dim-9 RealizableClaim value (top index 8). *)
Definition q1ab_claim
  (e00 e01 e10 e11 g1 g2 g3 g4 g5 : RealNumber) : RealizableClaim :=
  mk_realizable_claim 8 (q1ab_nat_matrix e00 e01 e10 e11 g1 g2 g3 g4 g5).

(** Adapter: GenRealizable of the dim-9 claim = the existing quantum_realizable_q1ab.
    Same GenRealizable, same psd_n, only top := 8. Pure proj/rewrite plumbing. *)
Theorem q1ab_claim_is_quantum_realizable_q1ab :
  forall e00 e01 e10 e11 g1 g2 g3 g4 g5,
    GenRealizable (q1ab_claim e00 e01 e10 e11 g1 g2 g3 g4 g5) <->
    quantum_realizable_q1ab e00 e01 e10 e11 g1 g2 g3 g4 g5.
Proof.
  intros.
  unfold GenRealizable, q1ab_claim, quantum_realizable_q1ab. cbn [rc_top rc_matrix].
  pose proof (q1ab_nat_to_fin9_eq e00 e01 e10 e11 g1 g2 g3 g4 g5) as Heq.
  split.
  - intros [Hsym Hpsd]. split.
    + rewrite <- Heq. apply (proj1 (symmetric_n_unfold_9 _)). exact Hsym.
    + rewrite <- Heq. apply (proj1 (psd_n_unfold_9 _)). exact Hpsd.
  - intros [Hsym Hpsd]. split.
    + apply (proj2 (symmetric_n_unfold_9 _)). rewrite Heq. exact Hsym.
    + apply (proj2 (psd_n_unfold_9 _)). rewrite Heq. exact Hpsd.
Qed.

(** W2-M4 completion. The dim-9 (Q_{1+AB}) biconditional, re-expressed against
    the SAME general projection — the second instance proving GenRealizable is
    layout-parametric, not 5-shaped. Pure composition; re-derives nothing. *)
Corollary column_contractive_q1ab_iff_general_realizable :
  forall e00 e01 e10 e11 g1 g2 g3 g4 g5,
    column_contractive_q1ab e00 e01 e10 e11 g1 g2 g3 g4 g5 <->
    GenRealizable (q1ab_claim e00 e01 e10 e11 g1 g2 g3 g4 g5).
Proof.
  intros.
  split.
  - intro H.
    apply (proj2 (q1ab_claim_is_quantum_realizable_q1ab _ _ _ _ _ _ _ _ _)).
    apply (proj1 (column_contractive_q1ab_iff_quantum_realizable _ _ _ _ _ _ _ _ _)).
    exact H.
  - intro H.
    apply (proj2 (column_contractive_q1ab_iff_quantum_realizable _ _ _ _ _ _ _ _ _)).
    apply (proj1 (q1ab_claim_is_quantum_realizable_q1ab _ _ _ _ _ _ _ _ _)).
    exact H.
Qed.

Print Assumptions column_contractive_q1ab_iff_general_realizable.

(** ── W2-M5: honest scope — what the projection captures, and what it cannot ─ *)

(** Linearity helper: a sum of an affine combination splits. *)
Lemma sum_n_affine : forall top (c d : RealNumber) a b,
  sum_n top (fun j => c * a j + d * b j)
  = c * sum_n top a + d * sum_n top b.
Proof.
  intros top c d a b.
  rewrite sum_n_plus. rewrite !sum_n_scale. reflexivity.
Qed.

(** quad_n is affine in the matrix: the form of a convex combination of matrices
    is the convex combination of the forms. *)
Lemma quad_n_convex_combo :
  forall top (M1 M2 : nat -> nat -> RealNumber) (t : RealNumber) (v : nat -> RealNumber),
    quad_n top (fun i j => (1 - t) * M1 i j + t * M2 i j) v
    = (1 - t) * quad_n top M1 v + t * quad_n top M2 v.
Proof.
  intros top M1 M2 t v. unfold quad_n.
  rewrite <- sum_n_affine.
  f_equal. apply functional_extensionality. intro i.
  rewrite <- sum_n_affine.
  f_equal. apply functional_extensionality. intro j.
  ring.
Qed.

(** THE SCOPE THEOREM. The feasible region of psd_n (hence of GenRealizable) is
    CONVEX: a convex combination of PSD matrices is PSD. This bounds what the
    general projection can express — only convex (spectrahedral) realizability
    sets. Any certified-realizability notion that is non-convex is out of reach. *)
Lemma psd_n_convex :
  forall top (M1 M2 : nat -> nat -> RealNumber) (t : RealNumber),
    (0 <= t <= 1) ->
    psd_n top M1 -> psd_n top M2 ->
    psd_n top (fun i j => (1 - t) * M1 i j + t * M2 i j).
Proof.
  intros top M1 M2 t [Ht0 Ht1] H1 H2 v.
  pose proof (H1 v) as Hv1. pose proof (H2 v) as Hv2.
  rewrite quad_n_convex_combo.
  apply Rle_ge.
  apply Rplus_le_le_0_compat.
  - apply Rmult_le_pos; lra.
  - apply Rmult_le_pos; lra.
Qed.

(** An honest certified-realizability notion that is NON-convex: deterministic
    CHSH correlators (each E_ij forced to +/-1). The local/deterministic vertex
    set is exactly this, and it is not convex. *)
Definition deterministic_chsh (e00 e01 e10 e11 : RealNumber) : Prop :=
  (e00 = 1 \/ e00 = -1) /\ (e01 = 1 \/ e01 = -1) /\
  (e10 = 1 \/ e10 = -1) /\ (e11 = 1 \/ e11 = -1).

(** Witness that it is non-convex: two deterministic points whose midpoint is
    not deterministic. So no psd_n feasible region (convex) can equal it — this
    realizability notion is provably outside GenRealizable's reach. *)
Lemma deterministic_chsh_not_convex :
  deterministic_chsh 1 1 1 1 /\
  deterministic_chsh (-1) (-1) (-1) (-1) /\
  ~ deterministic_chsh ((1 + -1) / 2) ((1 + -1) / 2) ((1 + -1) / 2) ((1 + -1) / 2).
Proof.
  split; [|split].
  - unfold deterministic_chsh; repeat split; left; reflexivity.
  - unfold deterministic_chsh; repeat split; right; reflexivity.
  - unfold deterministic_chsh. intros [H _]. destruct H as [H|H]; lra.
Qed.

(** "Realizability captured" for the moment-presentable class we actually have:
    GenRealizable coincides with the quantum predicate for BOTH proven instances
    (dim-5 CHSH and dim-9 Q_{1+AB}). This is the FORWARD characterization only.

    It does NOT, and does not claim to, close the open converse
    full_honest_implies_npa_status (HonestMeasurementImpliesNPA.v) — whether
    every honest measurement statistic is NPA-realizable is a separate, open
    question, untouched here. The scope is: GenRealizable captures the
    convex/moment-presentable realizability of these classes, no more. *)
Theorem genrealizable_captures_moment_presentable :
  (forall e00 e01 e10 e11,
     GenRealizable (chsh_claim e00 e01 e10 e11)
     <-> quantum_realizable (zero_marginal_npa e00 e01 e10 e11))
  /\
  (forall e00 e01 e10 e11 g1 g2 g3 g4 g5,
     GenRealizable (q1ab_claim e00 e01 e10 e11 g1 g2 g3 g4 g5)
     <-> quantum_realizable_q1ab e00 e01 e10 e11 g1 g2 g3 g4 g5).
Proof.
  split.
  - exact chsh_claim_is_zero_marginal_npa.
  - exact q1ab_claim_is_quantum_realizable_q1ab.
Qed.

(** ── The dim-5 instance is a VM step, not a free-floating matrix fact ─────── *)

(** Everything above is pure linear algebra: a dimension-polymorphic PSD
    predicate and its CHSH / Q_{1+AB} instances. This corollary ties that general
    machinery back to the machine it generalizes. If a CHSH-LASSERT step does not
    trap --- it advances the program counter by one, leaves the error flag as it
    found it, and started from a clean state --- then the correlators the VM
    derived from its own witness land inside the general realizable set. It is
    the same realizability projection run at dimension five, now stated over the
    actual machine state [s], so GenRealizable connects to vm_apply / VMState
    instead of standing apart from the kernel it generalizes. Composition only:
    the VM bridge supplies quantum_realizable of the witness-derived NPA matrix,
    which is definitionally the explicit four-correlator matrix, and
    chsh_claim_is_zero_marginal_npa carries it across into GenRealizable. *)
Corollary vm_chsh_lassert_step_is_general_realizable :
  forall (s : VMState) (mu_delta : nat),
    let s' := vm_apply s (instr_chsh_lassert mu_delta) in
    s'.(vm_pc) = S s.(vm_pc) ->
    s'.(vm_err) = s.(vm_err) ->
    s.(vm_err) = false ->
    GenRealizable (chsh_claim (state_e00 s) (state_e01 s) (state_e10 s) (state_e11 s)).
Proof.
  intros s mu_delta s' Hpc Herr Herr0.
  apply (proj2 (chsh_claim_is_zero_marginal_npa
                  (state_e00 s) (state_e01 s) (state_e10 s) (state_e11 s))).
  exact (chsh_lassert_no_trap_implies_quantum_realizable s mu_delta Hpc Herr Herr0).
Qed.

Print Assumptions vm_chsh_lassert_step_is_general_realizable.

Print Assumptions psd_n_convex.
Print Assumptions deterministic_chsh_not_convex.
Print Assumptions genrealizable_captures_moment_presentable.
