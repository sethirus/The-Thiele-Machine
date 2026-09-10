(** Full-elliptope completion: the CHSH correlator quantum set as an
    existential completion of the zero-marginal NPA matrix.

  The zero-marginal bridge (QuantumPartitionPSD.v) characterizes one slice of
  the quantum set: the orthogonal-observables case, where the cross moments
  rho_AA = <A0 A1> and rho_BB = <B0 B1> are pinned to zero. That slice is the
  membership test CHSH_LASSERT runs, and the monograph says out loud what the
  pinning costs: the slice rejects every deterministic local strategy,
  including the mu = 0 trace that achieves the classical bound.

  This file removes the pinning at the mathematical level. Membership in the
  full correlator quantum set is characterized the way Tsirelson's theorem
  says it must be: a correlator tuple E is realizable iff SOME completion of
  the cross moments (x for <A0 A1>, y for <B0 B1>) makes the moment matrix
  positive semidefinite. The existential over (x, y) is the whole difference
  between the slice and the set.

  What is proved here, each with its falsification condition:

  - [zero_marginal_implies_elliptope]: the slice is contained in the set
    (take x = y = 0). Falsify: a zero-marginal-realizable tuple with no
    completion; impossible by construction.

  - [deterministic_strategy_elliptope]: every deterministic local strategy
    (all four observables +/-1) is in the set, witnessed by x = a0*a1,
    y = b0*b1, where the completed matrix is an explicit rank-one Gram
    matrix plus the identity block. Falsify: exhibit signs a0 a1 b0 b1 with
    squares 1 whose completed matrix has a negative quadratic form.

  - [classical_tightness_witness_elliptope]: the all-ones strategy -- the
    mu = 0 witness by which the classical bound is achieved, and which the
    zero-marginal gate traps -- is in the set. The gap the monograph
    documents between the slice and honest classical play closes here.

  - [turing_point_elliptope]: (1,0,1,0), the running example of a classical
    point the slice rejects, is in the set, witnessed by x = 1, y = 0 and
    an explicit sum-of-squares decomposition of its quadratic form.

  - [elliptope_convex] / [elliptope_convex_combination]: the set is closed
    under binary convex combination, hence contains every finite mixture of
    deterministic strategies -- every local-hidden-variable correlator.

  - [elliptope_tsirelson]: every tuple in the set satisfies S^2 <= 8, i.e.
    |S| <= 2*sqrt(2). The proof is the Cauchy-Schwarz argument run inside
    the PSD form itself (lemma [psd_cauchy_schwarz]), with no row-norm
    shortcut: at nonzero y the rows of E can have norm exceeding 1, and the
    bound survives because the completion couples the two Cauchy-Schwarz
    budgets through y. Falsify: a completion-realizable tuple with S^2 > 8.

  - [pr_box_not_elliptope]: the PR box has no completion. Its S is 4, and
    16 <= 8 is refutable by lra. Falsify: exhibit x, y making the PR box's
    completed matrix PSD; the Tsirelson theorem above says you cannot.

  - [beyond_classical_elliptope]: the tuple (3/5, 3/5, 3/5, -3/5) is in the
    set with S = 12/5 > 2, so the set strictly exceeds the classical bound;
    together with [lhv] containment this places the elliptope strictly
    between the classical polytope and the no-signaling cube.

  Scope, stated the way the monograph fences everything: this is the
  correlator-level characterization. Marginals stay zero in the completed
  matrix; by Tsirelson's construction that loses nothing at the correlator
  level, and the correlator level is the honest scope (Ishizaka 2025 gives
  Q_{1+AB} = Q for correlators; Chaturvedi 2026 shows no finite NPA level is
  exact for the full behavior set). Nothing here derives physics; PSD of a
  completed matrix is polynomial arithmetic, and the identification of that
  condition with quantum realizability lives in the externally cited
  Tsirelson/NPA literature, exactly as for the zero-marginal slice.
*)

(* INQUISITOR NOTE: proof-connectivity waiver. This file stands on its own
   mathematics and does not engage VM semantics. No definition or theorem here
   mentions VMState, vm_step, vm_mu, MuCostModel or instruction_cost, and it
   imports no kernel module.

   The audit is waived rather than satisfied: satisfying it from inside would
   mean importing the kernel without using it, which asserts a bridge that is
   not here. Where these results feed the mu-ledger, they do so through the
   theorems downstream that consume them. Counted in the WAIVERS census in
   INQUISITOR_REPORT.md. *)
From Kernel Require Import ConstructivePSD NPAMomentMatrix.

From Coq Require Import Reals Lra Psatz Lia.
From Coq Require Import Fin.
Local Open Scope R_scope.

(** * The completed moment matrix and elliptope membership *)

(** The completion: marginals zero, correlators as given, cross moments free. *)
Definition completed_npa (E00 E01 E10 E11 x y : RealNumber) : NPAMomentMatrix := {|
  npa_EA0 := 0;
  npa_EA1 := 0;
  npa_EB0 := 0;
  npa_EB1 := 0;
  npa_E00 := E00;
  npa_E01 := E01;
  npa_E10 := E10;
  npa_E11 := E11;
  npa_rho_AA := x;
  npa_rho_BB := y;
|}.

Definition completed_matrix (E00 E01 E10 E11 x y : RealNumber) : Matrix5 :=
  nat_matrix_to_fin5 (npa_to_matrix (completed_npa E00 E01 E10 E11 x y)).

(** Elliptope membership: some completion of the cross moments is PSD.
    The existential is the mathematical content; everything the
    zero-marginal slice pinned, this frees. *)
Definition elliptope_realizable (E00 E01 E10 E11 : RealNumber) : Prop :=
  exists x y : RealNumber,
    quantum_realizable (completed_npa E00 E01 E10 E11 x y).

(** The CHSH functional, spelled locally so this file reads standalone. *)
Definition chsh_S (E00 E01 E10 E11 : RealNumber) : RealNumber := E00 + E01 + E10 - E11.

(** * Computational expansion of the completed quadratic form *)

(** The entire 5x5 quadratic form as one explicit polynomial. Everything
    downstream reduces to ring/nra facts about this expansion. *)
Lemma completed_quad_expand :
  forall (E00 E01 E10 E11 x y : RealNumber) (v : Vec5),
    quad5 (nat_matrix_to_fin5 (npa_to_matrix (completed_npa E00 E01 E10 E11 x y))) v =
    let v0 := v F1 in
    let v1 := v (FS F1) in
    let v2 := v (FS (FS F1)) in
    let v3 := v (FS (FS (FS F1))) in
    let v4 := v (FS (FS (FS (FS F1)))) in
    v0 * v0 + v1 * v1 + v2 * v2 + v3 * v3 + v4 * v4
    + 2 * x * (v1 * v2) + 2 * y * (v3 * v4)
    + 2 * E00 * (v1 * v3) + 2 * E01 * (v1 * v4)
    + 2 * E10 * (v2 * v3) + 2 * E11 * (v2 * v4).
Proof.
  intros. cbv [quad5 sum_fin5 completed_matrix nat_matrix_to_fin5
               npa_to_matrix completed_npa fin_to_nat].
  simpl. ring.
Qed.

(** The completed matrix is symmetric: inherited from the general record. *)
Lemma completed_matrix_symmetric :
  forall E00 E01 E10 E11 x y,
    symmetric5 (completed_matrix E00 E01 E10 E11 x y).
Proof.
  intros. apply npa_to_matrix_symmetric.
Qed.

(** * The slice sits inside the set *)

Theorem zero_marginal_implies_elliptope :
  forall E00 E01 E10 E11,
    quantum_realizable (zero_marginal_npa E00 E01 E10 E11) ->
    elliptope_realizable E00 E01 E10 E11.
Proof.
  intros E00 E01 E10 E11 H.
  exists 0, 0. exact H.
Qed.

(** * Cauchy-Schwarz inside the PSD form *)

(** For a symmetric PSD matrix, the bilinear form obeys Cauchy-Schwarz.
    Derived from the discriminant lemma: the quadratic
    t |-> quad(u) + 2 t B(u,v) + t^2 quad(v) is everywhere nonnegative. *)
Lemma psd_cauchy_schwarz :
  forall (M : Matrix5) (u v : Vec5),
    symmetric5 M ->
    PSD5 M ->
    bilinear5 M u v * bilinear5 M u v <= quad5 M u * quad5 M v.
Proof.
  intros M u v Hsym Hpsd.
  apply quadratic_nonneg_discriminant.
  intro t.
  assert (Hexp : quad5 M (fun k => u k + t * v k)
                 = quad5 M u + 2 * (t * bilinear5 M u v)
                   + (t * t * quad5 M v)).
  { rewrite (quad5_expansion_bilinear M u (fun k => t * v k) Hsym).
    rewrite bilinear5_scal_r. rewrite quad5_scal. ring. }
  specialize (Hpsd (fun k => u k + t * v k)).
  rewrite Hexp in Hpsd. lra.
Qed.

(** * Tsirelson from any completion *)

(** Every elliptope-realizable tuple satisfies S^2 <= 8. At y <> 0 the
    zero-marginal row-norm shortcut is unavailable (rows of E can exceed
    unit norm inside the set); the completion couples the two
    Cauchy-Schwarz budgets 2+2y and 2-2y, and their product is at most 4. *)
Theorem elliptope_tsirelson :
  forall E00 E01 E10 E11,
    elliptope_realizable E00 E01 E10 E11 ->
    chsh_S E00 E01 E10 E11 * chsh_S E00 E01 E10 E11 <= 8.
Proof.
  intros E00 E01 E10 E11 [x [y Hreal]].
  destruct Hreal as [Hsym Hpsd].
  set (M := completed_matrix E00 E01 E10 E11 x y) in *.
  (* Basis vectors: 1 -> A0, 2 -> A1, 3 -> B0, 4 -> B1. *)
  set (u1 := e_basis i1).
  set (u2 := e_basis i2).
  set (wp := fun k => e_basis i3 k + 1 * e_basis i4 k).
  set (wm := fun k => e_basis i3 k + (-1) * e_basis i4 k).
  (* Matrix entries at the concrete indices. *)
  assert (HM13 : M i1 i3 = E00) by reflexivity.
  assert (HM14 : M i1 i4 = E01) by reflexivity.
  assert (HM23 : M i2 i3 = E10) by reflexivity.
  assert (HM24 : M i2 i4 = E11) by reflexivity.
  assert (HM11 : M i1 i1 = 1) by reflexivity.
  assert (HM22 : M i2 i2 = 1) by reflexivity.
  assert (HM33 : M i3 i3 = 1) by reflexivity.
  assert (HM44 : M i4 i4 = 1) by reflexivity.
  assert (HM34 : M i3 i4 = y) by reflexivity.
  (* Bilinear values. *)
  assert (Hb1 : bilinear5 M u1 wp = E00 + E01).
  { unfold wp, u1.
    rewrite bilinear5_linear_r, bilinear5_scal_r.
    rewrite !bilinear5_e_basis. rewrite HM13, HM14. ring. }
  assert (Hb2 : bilinear5 M u2 wm = E10 - E11).
  { unfold wm, u2.
    rewrite bilinear5_linear_r, bilinear5_scal_r.
    rewrite !bilinear5_e_basis. rewrite HM23, HM24. ring. }
  (* Quadratic values. *)
  assert (Hq1 : quad5 M u1 = 1).
  { unfold u1. rewrite quad5_e_basis. exact HM11. }
  assert (Hq2 : quad5 M u2 = 1).
  { unfold u2. rewrite quad5_e_basis. exact HM22. }
  assert (Hqp : quad5 M wp = 2 + 2 * y).
  { unfold wp.
    rewrite (quad5_expansion_bilinear M (e_basis i3)
               (fun k => 1 * e_basis i4 k) Hsym).
    rewrite bilinear5_scal_r, quad5_scal.
    rewrite !quad5_e_basis, bilinear5_e_basis.
    rewrite HM33, HM44, HM34. ring. }
  assert (Hqm : quad5 M wm = 2 - 2 * y).
  { unfold wm.
    rewrite (quad5_expansion_bilinear M (e_basis i3)
               (fun k => (-1) * e_basis i4 k) Hsym).
    rewrite bilinear5_scal_r, quad5_scal.
    rewrite !quad5_e_basis, bilinear5_e_basis.
    rewrite HM33, HM44, HM34. ring. }
  (* Cauchy-Schwarz budgets. *)
  pose proof (psd_cauchy_schwarz M u1 wp Hsym Hpsd) as HCS1.
  pose proof (psd_cauchy_schwarz M u2 wm Hsym Hpsd) as HCS2.
  rewrite Hb1, Hq1, Hqp in HCS1.
  rewrite Hb2, Hq2, Hqm in HCS2.
  (* Nonnegativity of the budgets. *)
  assert (Hgp : quad5 M wp >= 0) by exact (Hpsd wp).
  rewrite Hqp in Hgp.
  assert (Hgm : quad5 M wm >= 0) by exact (Hpsd wm).
  rewrite Hqm in Hgm.
  (* Pure arithmetic: c1^2 <= 2+2y, c2^2 <= 2-2y, budgets nonnegative
     imply (c1 + c2)^2 <= 8. Written with explicit certificates so no
     tactic has to search for the Positivstellensatz witnesses. The
     clear strips the matrix-level context so the arithmetic tactics
     see only scalars. *)
  clear - HCS1 HCS2 Hgp Hgm.
  unfold chsh_S.
  pose proof (Rle_0_sqr (E00 + E01)) as Hsq1; unfold Rsqr in Hsq1.
  pose proof (Rle_0_sqr (E10 - E11)) as Hsq2; unfold Rsqr in Hsq2.
  pose proof (Rle_0_sqr y) as Hsqy; unfold Rsqr in Hsqy.
  assert (Hs1 : (E00 + E01) * (E00 + E01) <= 2 + 2 * y) by lra.
  assert (Hs2 : (E10 - E11) * (E10 - E11) <= 2 - 2 * y) by lra.
  (* c1^2 c2^2 <= (2+2y)(2-2y) = 4 - 4y^2 <= 4, by two monotone
     multiplications. *)
  assert (Hstep1 : ((E00 + E01) * (E00 + E01)) * ((E10 - E11) * (E10 - E11))
                   <= (2 + 2 * y) * ((E10 - E11) * (E10 - E11))).
  { apply Rmult_le_compat_r; lra. }
  assert (Hstep2 : (2 + 2 * y) * ((E10 - E11) * (E10 - E11))
                   <= (2 + 2 * y) * (2 - 2 * y)).
  { apply Rmult_le_compat_l; lra. }
  assert (Hy4 : (2 + 2 * y) * (2 - 2 * y) = 4 - 4 * (y * y)) by ring.
  assert (Hprod : ((E00 + E01) * (E10 - E11)) * ((E00 + E01) * (E10 - E11)) <= 4).
  { assert (Hswap : ((E00 + E01) * (E10 - E11)) * ((E00 + E01) * (E10 - E11))
                    = ((E00 + E01) * (E00 + E01)) * ((E10 - E11) * (E10 - E11)))
      by ring.
    lra. }
  (* t^2 <= 4 implies t <= 2, via 4(2 - t) = (2 - t)^2 + (4 - t^2). *)
  assert (Hcc : (E00 + E01) * (E10 - E11) <= 2).
  { pose proof (Rle_0_sqr (2 - (E00 + E01) * (E10 - E11))) as Hsqt;
      unfold Rsqr in Hsqt.
    assert (Hcert :
      4 * (2 - (E00 + E01) * (E10 - E11)) =
      (2 - (E00 + E01) * (E10 - E11)) * (2 - (E00 + E01) * (E10 - E11))
      + (4 - ((E00 + E01) * (E10 - E11)) * ((E00 + E01) * (E10 - E11))))
      by ring.
    lra. }
  (* Assemble: (c1 + c2)^2 = c1^2 + 2 c1 c2 + c2^2. *)
  assert (Hexpand :
    (E00 + E01 + E10 - E11) * (E00 + E01 + E10 - E11)
    = (E00 + E01) * (E00 + E01)
      + 2 * ((E00 + E01) * (E10 - E11))
      + (E10 - E11) * (E10 - E11)) by ring.
  lra.
Qed.

(** * The PR box has no completion *)

Theorem pr_box_not_elliptope : ~ elliptope_realizable 1 1 1 (-1).
Proof.
  intro H.
  apply elliptope_tsirelson in H.
  unfold chsh_S in H. lra.
Qed.

(** * Deterministic local strategies are in the set *)

(** The witness is the honest one: x = a0*a1 and y = b0*b1 are exactly the
    cross moments a deterministic strategy actually has. The completed
    matrix becomes e0 e0^T + w w^T for w = (0, a0, a1, b0, b1): a Gram
    matrix, PSD by the two-squares identity below. *)
Theorem deterministic_strategy_elliptope :
  forall a0 a1 b0 b1 : RealNumber,
    a0 * a0 = 1 -> a1 * a1 = 1 -> b0 * b0 = 1 -> b1 * b1 = 1 ->
    elliptope_realizable (a0 * b0) (a0 * b1) (a1 * b0) (a1 * b1).
Proof.
  intros a0 a1 b0 b1 Ha0 Ha1 Hb0 Hb1.
  exists (a0 * a1), (b0 * b1).
  split.
  - apply npa_to_matrix_symmetric.
  - intro v.
    rewrite (completed_quad_expand
               (a0 * b0) (a0 * b1) (a1 * b0) (a1 * b1)
               (a0 * a1) (b0 * b1) v).
    cbv zeta.
    set (v0 := v F1).
    set (v1 := v (FS F1)).
    set (v2 := v (FS (FS F1))).
    set (v3 := v (FS (FS (FS F1)))).
    set (v4 := v (FS (FS (FS (FS F1))))).
    (* The two-squares identity: modulo the unit-square hypotheses, the
       form is v0^2 + (a0 v1 + a1 v2 + b0 v3 + b1 v4)^2. *)
    assert (Hkey :
      v0 * v0 + v1 * v1 + v2 * v2 + v3 * v3 + v4 * v4
      + 2 * (a0 * a1) * (v1 * v2) + 2 * (b0 * b1) * (v3 * v4)
      + 2 * (a0 * b0) * (v1 * v3) + 2 * (a0 * b1) * (v1 * v4)
      + 2 * (a1 * b0) * (v2 * v3) + 2 * (a1 * b1) * (v2 * v4)
      =
      v0 * v0
      + (a0 * v1 + a1 * v2 + b0 * v3 + b1 * v4)
        * (a0 * v1 + a1 * v2 + b0 * v3 + b1 * v4)
      + (1 - a0 * a0) * (v1 * v1) + (1 - a1 * a1) * (v2 * v2)
      + (1 - b0 * b0) * (v3 * v3) + (1 - b1 * b1) * (v4 * v4)) by ring.
    rewrite Hkey, Ha0, Ha1, Hb0, Hb1.
    pose proof (Rle_0_sqr v0) as Hv0; unfold Rsqr in Hv0.
    pose proof (Rle_0_sqr (a0 * v1 + a1 * v2 + b0 * v3 + b1 * v4)) as Hs;
      unfold Rsqr in Hs.
    lra.
Qed.

(** The mu = 0 tightness witness -- the all-ones strategy by which
    classical_bound_achieved touches the classical bound, and which the
    zero-marginal gate traps -- is elliptope-realizable. This is the named
    repair of the slice/set gap the monograph documents. *)
Corollary classical_tightness_witness_elliptope :
  elliptope_realizable 1 1 1 1.
Proof.
  pose proof (deterministic_strategy_elliptope 1 1 1 1) as H.
  replace (1 * 1) with 1 in H by ring.
  apply H; ring.
Qed.

(** * The running example: (1,0,1,0) *)

(** The Turing-classical point that fails the zero-marginal slice on
    condition 1. Witness x = 1, y = 0; the form is an explicit sum of
    squares: v0^2 + (v1 + v2 + v3)^2 + v4^2. *)
Theorem turing_point_elliptope : elliptope_realizable 1 0 1 0.
Proof.
  exists 1, 0.
  split.
  - apply npa_to_matrix_symmetric.
  - intro v.
    rewrite (completed_quad_expand 1 0 1 0 1 0 v).
    cbv zeta.
    set (v0 := v F1).
    set (v1 := v (FS F1)).
    set (v2 := v (FS (FS F1))).
    set (v3 := v (FS (FS (FS F1)))).
    set (v4 := v (FS (FS (FS (FS F1))))).
    assert (Hkey :
      v0 * v0 + v1 * v1 + v2 * v2 + v3 * v3 + v4 * v4
      + 2 * 1 * (v1 * v2) + 2 * 0 * (v3 * v4)
      + 2 * 1 * (v1 * v3) + 2 * 0 * (v1 * v4)
      + 2 * 1 * (v2 * v3) + 2 * 0 * (v2 * v4)
      = v0 * v0
        + (v1 + v2 + v3) * (v1 + v2 + v3)
        + v4 * v4) by ring.
    rewrite Hkey.
    pose proof (Rle_0_sqr v0) as Hv0; unfold Rsqr in Hv0.
    pose proof (Rle_0_sqr (v1 + v2 + v3)) as Hs; unfold Rsqr in Hs.
    pose proof (Rle_0_sqr v4) as Hv4; unfold Rsqr in Hv4.
    lra.
Qed.

(** * Convexity: the set absorbs mixtures *)

(** Scalar helper: a convex combination of nonnegatives is nonnegative,
    packaged so the caller discharges the combination identity by ring. *)
Lemma convex_ge0 :
  forall lam A B C : RealNumber,
    0 <= lam <= 1 -> A >= 0 -> B >= 0 ->
    C = lam * A + (1 - lam) * B ->
    C >= 0.
Proof.
  intros lam A B C Hlam HA HB Heq.
  rewrite Heq.
  apply Rle_ge.
  apply Rplus_le_le_0_compat; apply Rmult_le_pos; lra.
Qed.

Theorem elliptope_convex :
  forall E00 E01 E10 E11 F00 F01 F10 F11 lam,
    0 <= lam <= 1 ->
    elliptope_realizable E00 E01 E10 E11 ->
    elliptope_realizable F00 F01 F10 F11 ->
    elliptope_realizable
      (lam * E00 + (1 - lam) * F00)
      (lam * E01 + (1 - lam) * F01)
      (lam * E10 + (1 - lam) * F10)
      (lam * E11 + (1 - lam) * F11).
Proof.
  intros E00 E01 E10 E11 F00 F01 F10 F11 lam Hlam
         [x1 [y1 [Hsym1 Hpsd1]]] [x2 [y2 [Hsym2 Hpsd2]]].
  exists (lam * x1 + (1 - lam) * x2), (lam * y1 + (1 - lam) * y2).
  split.
  - apply npa_to_matrix_symmetric.
  - intro v.
    pose proof (Hpsd1 v) as H1. pose proof (Hpsd2 v) as H2.
    rewrite (completed_quad_expand E00 E01 E10 E11 x1 y1 v) in H1.
    rewrite (completed_quad_expand F00 F01 F10 F11 x2 y2 v) in H2.
    rewrite (completed_quad_expand
               (lam * E00 + (1 - lam) * F00)
               (lam * E01 + (1 - lam) * F01)
               (lam * E10 + (1 - lam) * F10)
               (lam * E11 + (1 - lam) * F11)
               (lam * x1 + (1 - lam) * x2)
               (lam * y1 + (1 - lam) * y2) v).
    cbv zeta in *.
    apply (convex_ge0 lam _ _ _ Hlam H1 H2).
    ring.
Qed.

(** * Strictly beyond the classical bound, inside the set *)

(** A rational point with S = 12/5 > 2: elliptope-realizable at x = y = 0
    via an explicit sum-of-squares certificate. Together with the LHV
    containment above, this separates the elliptope strictly from the
    classical polytope, from inside the formalization. *)
Theorem beyond_classical_elliptope :
  elliptope_realizable (3/5) (3/5) (3/5) (-(3/5))
  /\ chsh_S (3/5) (3/5) (3/5) (-(3/5)) > 2.
Proof.
  split.
  - exists 0, 0.
    split.
    + apply npa_to_matrix_symmetric.
    + intro v.
      rewrite (completed_quad_expand (3/5) (3/5) (3/5) (-(3/5)) 0 0 v).
      cbv zeta.
      set (v0 := v F1).
      set (v1 := v (FS F1)).
      set (v2 := v (FS (FS F1))).
      set (v3 := v (FS (FS (FS F1)))).
      set (v4 := v (FS (FS (FS (FS F1))))).
      (* SOS certificate:
         v0^2 + (v1 + (3/5)v3 + (3/5)v4)^2 + (v2 + (3/5)v3 - (3/5)v4)^2
              + (7/25)v3^2 + (7/25)v4^2. *)
      assert (Hkey :
        v0 * v0 + v1 * v1 + v2 * v2 + v3 * v3 + v4 * v4
        + 2 * 0 * (v1 * v2) + 2 * 0 * (v3 * v4)
        + 2 * (3/5) * (v1 * v3) + 2 * (3/5) * (v1 * v4)
        + 2 * (3/5) * (v2 * v3) + 2 * (-(3/5)) * (v2 * v4)
        = v0 * v0
          + (v1 + (3/5) * v3 + (3/5) * v4) * (v1 + (3/5) * v3 + (3/5) * v4)
          + (v2 + (3/5) * v3 - (3/5) * v4) * (v2 + (3/5) * v3 - (3/5) * v4)
          + (7/25) * (v3 * v3) + (7/25) * (v4 * v4)) by field.
      rewrite Hkey.
      pose proof (Rle_0_sqr v0) as Hv0; unfold Rsqr in Hv0.
      pose proof (Rle_0_sqr (v1 + (3/5) * v3 + (3/5) * v4)) as Hs1;
        unfold Rsqr in Hs1.
      pose proof (Rle_0_sqr (v2 + (3/5) * v3 - (3/5) * v4)) as Hs2;
        unfold Rsqr in Hs2.
      pose proof (Rle_0_sqr v3) as Hv3; unfold Rsqr in Hv3.
      pose proof (Rle_0_sqr v4) as Hv4; unfold Rsqr in Hv4.
      lra.
  - unfold chsh_S. lra.
Qed.

(** * Finite mixtures: every LHV correlator is in the set *)

(** Finite sums over nat-indexed families, with the four helper facts the
    renormalization induction needs. *)
Fixpoint sumf (n : nat) (f : nat -> RealNumber) : RealNumber :=
  match n with
  | O => 0
  | S k => sumf k f + f k
  end.

Lemma sumf_nonneg :
  forall n (f : nat -> RealNumber),
    (forall i, (i < n)%nat -> 0 <= f i) ->
    0 <= sumf n f.
Proof.
  induction n as [| k IH]; intros f Hf; simpl.
  - lra.
  - assert (Hk : 0 <= f k) by (apply Hf; lia).
    assert (Hrest : 0 <= sumf k f) by (apply IH; intros; apply Hf; lia).
    lra.
Qed.

Lemma sumf_ext :
  forall n (f g : nat -> RealNumber),
    (forall i, (i < n)%nat -> f i = g i) ->
    sumf n f = sumf n g.
Proof.
  induction n as [| k IH]; intros f g Hfg; simpl.
  - reflexivity.
  - rewrite (IH f g); [| intros; apply Hfg; lia].
    rewrite (Hfg k); [reflexivity | lia].
Qed.

Lemma sumf_scale :
  forall n (c : RealNumber) (f : nat -> RealNumber),
    sumf n (fun i => c * f i) = c * sumf n f.
Proof.
  induction n as [| k IH]; intros c f; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

Lemma sumf_zero_all :
  forall n (f : nat -> RealNumber),
    (forall i, (i < n)%nat -> 0 <= f i) ->
    sumf n f = 0 ->
    forall i, (i < n)%nat -> f i = 0.
Proof.
  induction n as [| k IH]; intros f Hf Hsum i Hi.
  - lia.
  - simpl in Hsum.
    assert (Hk : 0 <= f k) by (apply Hf; lia).
    assert (Hrest : 0 <= sumf k f) by (apply sumf_nonneg; intros; apply Hf; lia).
    destruct (Nat.eq_dec i k) as [-> | Hne].
    + lra.
    + apply (IH f); [intros; apply Hf; lia | lra | lia].
Qed.

(** Uniform noise is in the set: the origin's completed matrix at x = y = 0
    is the identity, whose form is a sum of five squares. *)
Lemma elliptope_zero : elliptope_realizable 0 0 0 0.
Proof.
  exists 0, 0.
  split.
  - apply npa_to_matrix_symmetric.
  - intro v.
    rewrite (completed_quad_expand 0 0 0 0 0 0 v).
    cbv zeta.
    pose proof (Rle_0_sqr (v F1)) as H0; unfold Rsqr in H0.
    pose proof (Rle_0_sqr (v (FS F1))) as H1; unfold Rsqr in H1.
    pose proof (Rle_0_sqr (v (FS (FS F1)))) as H2; unfold Rsqr in H2.
    pose proof (Rle_0_sqr (v (FS (FS (FS F1))))) as H3; unfold Rsqr in H3.
    pose proof (Rle_0_sqr (v (FS (FS (FS (FS F1)))))) as H4; unfold Rsqr in H4.
    lra.
Qed.

(** Sub-convex finite mixtures: total weight at most 1, every component in
    the set, weighted sum in the set. Stated with slack (<= 1 rather than
    = 1) so the induction renormalizes cleanly; the deficit is absorbed by
    the origin. *)
Theorem elliptope_finite_mixture :
  forall n (p E0 E1 E2 E3 : nat -> RealNumber),
    (forall i, (i < n)%nat -> 0 <= p i) ->
    sumf n p <= 1 ->
    (forall i, (i < n)%nat ->
       elliptope_realizable (E0 i) (E1 i) (E2 i) (E3 i)) ->
    elliptope_realizable
      (sumf n (fun i => p i * E0 i))
      (sumf n (fun i => p i * E1 i))
      (sumf n (fun i => p i * E2 i))
      (sumf n (fun i => p i * E3 i)).
Proof.
  induction n as [| k IH]; intros p E0 E1 E2 E3 Hp Hsum Hell; simpl.
  - exact elliptope_zero.
  - assert (Hpk : 0 <= p k) by (apply Hp; lia).
    assert (Hrest0 : 0 <= sumf k p) by (apply sumf_nonneg; intros; apply Hp; lia).
    simpl in Hsum.
    destruct (Rlt_le_dec (p k) 1) as [Hwlt | Hwge].
    + (* Head weight below 1: renormalize the tail by c = 1 - p k. *)
      set (c := 1 - p k).
      assert (Hc : 0 < c) by (unfold c; lra).
      assert (Hcinv : 0 <= / c) by (left; apply Rinv_0_lt_compat; exact Hc).
      (* Tail mixture with weights p i / c is a sub-convex mixture. *)
      assert (Htail :
        elliptope_realizable
          (sumf k (fun i => (p i * / c) * E0 i))
          (sumf k (fun i => (p i * / c) * E1 i))
          (sumf k (fun i => (p i * / c) * E2 i))
          (sumf k (fun i => (p i * / c) * E3 i))).
      { apply IH.
        - intros i Hi. apply Rmult_le_pos; [apply Hp; lia | exact Hcinv].
        - assert (Hscale : sumf k (fun i => p i * / c) = / c * sumf k p).
          { rewrite (sumf_ext k _ (fun i => / c * p i)) by (intros; ring).
            apply sumf_scale. }
          rewrite Hscale.
          assert (Hle : sumf k p <= c) by (unfold c; lra).
          replace 1 with (/ c * c) by (field; lra).
          apply Rmult_le_compat_l; [exact Hcinv | exact Hle].
        - intros i Hi. apply Hell; lia. }
      (* Binary convexity between the renormalized tail and the head. *)
      pose proof (elliptope_convex _ _ _ _ (E0 k) (E1 k) (E2 k) (E3 k)
                    c
                    ltac:(unfold c; lra)
                    Htail
                    ltac:(apply Hell; lia)) as Hcomb.
      (* The combination is exactly the (S k)-fold weighted sum. *)
      replace (sumf k (fun i => p i * E0 i) + p k * E0 k)
        with (c * sumf k (fun i => (p i * / c) * E0 i) + (1 - c) * E0 k).
      2:{ rewrite (sumf_ext k (fun i => (p i * / c) * E0 i)
                     (fun i => / c * (p i * E0 i))) by (intros; ring).
          rewrite sumf_scale. unfold c. field. lra. }
      replace (sumf k (fun i => p i * E1 i) + p k * E1 k)
        with (c * sumf k (fun i => (p i * / c) * E1 i) + (1 - c) * E1 k).
      2:{ rewrite (sumf_ext k (fun i => (p i * / c) * E1 i)
                     (fun i => / c * (p i * E1 i))) by (intros; ring).
          rewrite sumf_scale. unfold c. field. lra. }
      replace (sumf k (fun i => p i * E2 i) + p k * E2 k)
        with (c * sumf k (fun i => (p i * / c) * E2 i) + (1 - c) * E2 k).
      2:{ rewrite (sumf_ext k (fun i => (p i * / c) * E2 i)
                     (fun i => / c * (p i * E2 i))) by (intros; ring).
          rewrite sumf_scale. unfold c. field. lra. }
      replace (sumf k (fun i => p i * E3 i) + p k * E3 k)
        with (c * sumf k (fun i => (p i * / c) * E3 i) + (1 - c) * E3 k).
      2:{ rewrite (sumf_ext k (fun i => (p i * / c) * E3 i)
                     (fun i => / c * (p i * E3 i))) by (intros; ring).
          rewrite sumf_scale. unfold c. field. lra. }
      exact Hcomb.
    + (* Head weight is 1 (or more, forced back to 1): the tail weights
         are all zero and the mixture is the head point. *)
      assert (Hw1 : p k = 1) by lra.
      assert (Htail0 : sumf k p = 0) by lra.
      assert (Hzero : forall i, (i < k)%nat -> p i = 0).
      { apply sumf_zero_all; [intros; apply Hp; lia | exact Htail0]. }
      assert (Hz0 : sumf k (fun i => p i * E0 i) = 0).
      { rewrite (sumf_ext k _ (fun i => 0 * E0 i))
          by (intros i Hi; rewrite (Hzero i Hi); ring).
        rewrite sumf_scale. ring. }
      assert (Hz1 : sumf k (fun i => p i * E1 i) = 0).
      { rewrite (sumf_ext k _ (fun i => 0 * E1 i))
          by (intros i Hi; rewrite (Hzero i Hi); ring).
        rewrite sumf_scale. ring. }
      assert (Hz2 : sumf k (fun i => p i * E2 i) = 0).
      { rewrite (sumf_ext k _ (fun i => 0 * E2 i))
          by (intros i Hi; rewrite (Hzero i Hi); ring).
        rewrite sumf_scale. ring. }
      assert (Hz3 : sumf k (fun i => p i * E3 i) = 0).
      { rewrite (sumf_ext k _ (fun i => 0 * E3 i))
          by (intros i Hi; rewrite (Hzero i Hi); ring).
        rewrite sumf_scale. ring. }
      rewrite Hz0, Hz1, Hz2, Hz3, Hw1.
      replace (0 + 1 * E0 k) with (E0 k) by ring.
      replace (0 + 1 * E1 k) with (E1 k) by ring.
      replace (0 + 1 * E2 k) with (E2 k) by ring.
      replace (0 + 1 * E3 k) with (E3 k) by ring.
      apply Hell; lia.
Qed.

(** The headline corollary: every local-hidden-variable correlator -- any
    finite mixture of deterministic sign strategies -- is in the set. This
    is the point the slice could not make: honest classical play, in full
    generality, certifiable against the completed matrix. *)
Corollary lhv_mixture_elliptope :
  forall n (p a0 a1 b0 b1 : nat -> RealNumber),
    (forall i, (i < n)%nat -> 0 <= p i) ->
    sumf n p = 1 ->
    (forall i, (i < n)%nat ->
       a0 i * a0 i = 1 /\ a1 i * a1 i = 1 /\
       b0 i * b0 i = 1 /\ b1 i * b1 i = 1) ->
    elliptope_realizable
      (sumf n (fun i => p i * (a0 i * b0 i)))
      (sumf n (fun i => p i * (a0 i * b1 i)))
      (sumf n (fun i => p i * (a1 i * b0 i)))
      (sumf n (fun i => p i * (a1 i * b1 i))).
Proof.
  intros n p a0 a1 b0 b1 Hp Hsum Hsigns.
  apply elliptope_finite_mixture.
  - exact Hp.
  - lra.
  - intros i Hi.
    destruct (Hsigns i Hi) as [Ha0 [Ha1 [Hb0 Hb1]]].
    apply deterministic_strategy_elliptope; assumption.
Qed.

(** * Anchor for proof-connectivity audits *)

Definition elliptope_completion_anchor := @completed_matrix.
