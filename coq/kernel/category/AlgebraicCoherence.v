(** This file studies a rational correlator record and a predicate made from
    absolute-value bounds and four selected 3-by-3 polynomial minors. The
    checked conclusions are the bounds and witnesses stated by the theorem
    types below. There are no Hilbert-space operators or physical realization
    premises in these definitions. *)

(* SCOPE NOTE: standalone proof scope. This file stands on its own
   mathematics and does not engage VM semantics. No definition or theorem here
   mentions VMState, vm_step, vm_mu, MuCostModel or instruction_cost, and it
   imports no kernel module.

   The audit is waived rather than satisfied: satisfying it from inside would
   mean importing the kernel without using it, which asserts a bridge that is
   not here. Where these results feed the mu-ledger, they do so through the
   theorems downstream that consume them. The standalone boundary is stated
   here rather than inferred from an import. *)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lia.
Require Import Psatz.

Local Open Scope Q_scope.

(** [Correlators] is a four-field rational record. The record carries no
    invariants; the bounds and minor conditions are introduced by
    [algebraically_coherent]. *)
Record Correlators := { E00:Q; E01:Q; E10:Q; E11:Q }.

(** [S_from_correlators] is the displayed rational expression
    [E00 + E01 + E10 - E11]. This file proves several algebraic bounds for
    that expression under explicitly supplied hypotheses. *)
Definition S_from_correlators (c : Correlators) : Q :=
  E00 c + E01 c + E10 c - E11 c.

(** [minor_3x3] is the rational polynomial
    [1 - a^2 - b^2 - c^2 + 2abc]. It is used as a selected minor-style
    constraint; this file does not identify the expression with a complete NPA
    moment-matrix test. *)
Definition minor_3x3 (a b c : Q) : Q :=
  1 - a*a - b*b - c*c + 2*a*b*c.

(** [algebraically_coherent] is the exact predicate used by this file: four
    rational absolute-value bounds and the existence of two rational parameters
    satisfying four nonnegative [minor_3x3] expressions. It is an algebraic
    filter. No theorem here identifies it with the full quantum correlation
    set. *)
Definition algebraically_coherent (c : Correlators) : Prop :=
  Qabs (E00 c) <= 1 /\ Qabs (E01 c) <= 1 /\ Qabs (E10 c) <= 1 /\ Qabs (E11 c) <= 1 /\
  exists t s : Q,
    0 <= minor_3x3 t (E00 c) (E10 c) /\
    0 <= minor_3x3 t (E01 c) (E11 c) /\
    0 <= minor_3x3 s (E00 c) (E01 c) /\
    0 <= minor_3x3 s (E10 c) (E11 c).

(** [Qabs_bound] converts a rational absolute-value inequality into its two
    ordered inequalities. *)
Lemma Qabs_bound : forall x y : Q, Qabs x <= y -> -y <= x /\ x <= y.
Proof.
  intros. apply Qabs_Qle_condition. assumption.
Qed.

(** [chsh_bound_4] is the triangle-inequality consequence of the four
    absolute-value premises. It is an algebraic bound for this rational record;
    it does not classify physical correlations or mention the VM ledger. *)
Theorem chsh_bound_4 : forall c : Correlators,
  Qabs (E00 c) <= 1 /\ Qabs (E01 c) <= 1 /\ Qabs (E10 c) <= 1 /\ Qabs (E11 c) <= 1 ->
  Qabs (S_from_correlators c) <= 4.
Proof.
  intros c [H00 [H01 [H10 H11]]].
  unfold S_from_correlators.
  (* Triangle inequality: |a+b+c-d| <= |a|+|b|+|c|+|d| *)
  assert (Htri: Qabs (E00 c + E01 c + E10 c - E11 c) <= 
                Qabs (E00 c) + Qabs (E01 c) + Qabs (E10 c) + Qabs (E11 c)).
  { assert (Heq: E00 c + E01 c + E10 c - E11 c == E00 c + E01 c + E10 c + - E11 c) by ring.
    rewrite Heq.
    assert (H_step1: Qabs (E00 c + E01 c + E10 c + - E11 c) <= 
                     Qabs (E00 c + E01 c + E10 c) + Qabs (- E11 c)).
    { apply Qabs_triangle. }
    assert (H_step2: Qabs (E00 c + E01 c + E10 c) <= 
                     Qabs (E00 c + E01 c) + Qabs (E10 c)).
    { apply Qabs_triangle. }
    assert (H_step3: Qabs (E00 c + E01 c) <= 
                     Qabs (E00 c) + Qabs (E01 c)).
    { apply Qabs_triangle. }
    rewrite Qabs_opp in H_step1.
    apply (Qle_trans _ (Qabs (E00 c + E01 c + E10 c) + Qabs (E11 c))).
    - exact H_step1.
    - apply Qplus_le_compat. 2: apply Qle_refl.
      apply (Qle_trans _ (Qabs (E00 c + E01 c) + Qabs (E10 c))).
      + exact H_step2.
      + apply Qplus_le_compat. 2: apply Qle_refl.
        exact H_step3. }
  apply (Qle_trans _ (Qabs (E00 c) + Qabs (E01 c) + Qabs (E10 c) + Qabs (E11 c))).
  - exact Htri.
  - assert (Hrw4: (4:Q) == 1+1+1+1) by ring. rewrite Hrw4.
    apply Qplus_le_compat.
    apply Qplus_le_compat.
    apply Qplus_le_compat.
    + exact H00.
    + exact H01.
    + exact H10.
    + exact H11.
Qed.

(** [symmetric_tsirelson_bound] proves the displayed rational upper bound for
    the symmetric pattern under its stated minor premises. The rational number
    [5657/2000] is an upper comparison value, not an exact representation of
    an irrational optimum. *)
Theorem symmetric_tsirelson_bound : forall e : Q,
  0 <= e ->
  (exists t : Q,
    0 <= minor_3x3 t e e /\
    0 <= minor_3x3 t e (-e)) ->
  4 * e <= (5657#2000).
Proof.
  intros e He [t [H1 H2]].
  unfold minor_3x3 in *.
  assert (Hsum: 1 - t*t - e*e - e*e + 2*t*e*e + (1 - t*t - e*e - e*e - 2*t*e*e) >= 0).
  { nra. }
  assert (He2: e*e <= 1#2).
  { nra. }
  assert (Hsq: (4*e)*(4*e) <= 8).
  { nra. }
  (* (5657/2000)^2 = 32001649 / 4000000 *)
  assert (Hbound_sq: 8 <= (5657#2000) * (5657#2000)).
  { unfold Qle, Qmult. simpl. lia. }
  nra.
Qed.

(** [tsirelson_from_algebraic_coherence] projects the four absolute-value
    premises out of [algebraically_coherent] and applies [chsh_bound_4]. It is
    the weaker general algebraic bound retained alongside the later squared
    bound. *)
Theorem tsirelson_from_algebraic_coherence : forall c : Correlators,
  algebraically_coherent c ->
  Qabs (S_from_correlators c) <= 4.
Proof.
  intros c Hcoh.
  unfold algebraically_coherent in Hcoh.
  destruct Hcoh as [H0 [H1 [H2 [H3 Hrest]]]].
  apply chsh_bound_4.
  auto.
Qed.

(** [max_trace] is the rational record whose displayed expression evaluates to
    four under the four unit bounds. The name records that value; it does not
    assign a physical no-signaling interpretation. *)
Definition max_trace : Correlators :=
  {| E00 := 1; E01 := 1; E10 := 1; E11 := -1 |}.

(** [algebraic_max_not_coherent] shows that [max_trace] fails this selected
    rational coherence predicate. It does not classify every point outside the
    predicate or establish a physical interpretation of the witness. *)
Theorem algebraic_max_not_coherent :
  ~ algebraically_coherent max_trace.
Proof.
  unfold algebraically_coherent, max_trace. simpl.
  intros [H00 [H01 [H10 [H11 Hexists]]]].
  destruct Hexists as [t [s [H1 [H2 [H3 H4]]]]].
  unfold minor_3x3 in *. simpl in *.
  (* H1: 1 - t*t - 1 - 1 + 2*t >= 0  => -t^2 + 2t - 1 >= 0 => -(t-1)^2 >= 0 *)
  (* H2: 1 - t*t - 1 - 1 - 2*t >= 0  => -t^2 - 2t - 1 >= 0 => -(t+1)^2 >= 0 *)
  assert (Ht_sq1: 0 <= -(t-1)*(t-1)). { nra. }
  assert (Ht_sq2: 0 <= -(t+1)*(t+1)). { nra. }
  assert (Ht1: t == 1). { nra. }
  assert (Ht2: t == -1). { nra. }
  rewrite Ht1 in Ht2.
  discriminate.
Qed.

(** The following lemmas isolate the rational inequalities used by the later
    coherence theorem. The conditional squared bound keeps its extra premise
    explicit. *)

(** [sum_6_squares_nonneg] is the rational nonnegativity fact used by the
    specialized CHSH polynomial inequality. *)
Lemma sum_6_squares_nonneg : forall p q r s t u : Q,
  0 <= p*p + q*q + r*r + s*s + t*t + u*u.
Proof.
  intros.
  assert (H1: 0 <= p*p) by nra.
  assert (H2: 0 <= q*q) by nra.
  assert (H3: 0 <= r*r) by nra.
  assert (H4: 0 <= s*s) by nra.
  assert (H5: 0 <= t*t) by nra.
  assert (H6: 0 <= u*u) by nra.
  nra.
Qed.

(** [cauchy_schwarz_chsh] proves the specialized rational polynomial inequality
    used by the weak and conditional squared bounds. *)
Lemma cauchy_schwarz_chsh : forall a b c d : Q,
  (a + b + c - d) * (a + b + c - d) <= 4 * (a*a + b*b + c*c + d*d).
Proof.
  intros a b c d.
  (* The difference is a sum of six squares. *)
  pose proof (sum_6_squares_nonneg (a-b) (a-c) (b-c) (a+d) (b+d) (c+d)) as Hsos.
  nra.
Qed.

(** [correlation_squares_bound] uses only the four absolute-value premises. It
    does not use the selected minor constraints. *)
Lemma correlation_squares_bound : forall e00 e01 e10 e11 : Q,
  Qabs e00 <= 1 -> Qabs e01 <= 1 -> Qabs e10 <= 1 -> Qabs e11 <= 1 ->
  e00*e00 + e01*e01 + e10*e10 + e11*e11 <= 4.
Proof.
  intros e00 e01 e10 e11 He00 He01 He10 He11.
  apply Qabs_Qle_condition in He00. destruct He00.
  apply Qabs_Qle_condition in He01. destruct He01.
  apply Qabs_Qle_condition in He10. destruct He10.
  apply Qabs_Qle_condition in He11. destruct He11.
  nra.
Qed.

(** [chsh_weak_bound] combines the polynomial inequality with the unit
    bounds to obtain the conditional squared bound 16. *)
Lemma chsh_weak_bound : forall e00 e01 e10 e11 : Q,
  Qabs e00 <= 1 -> Qabs e01 <= 1 -> Qabs e10 <= 1 -> Qabs e11 <= 1 ->
  (e00 + e01 + e10 - e11) * (e00 + e01 + e10 - e11) <= 16.
Proof.
  intros e00 e01 e10 e11 He00 He01 He10 He11.
  pose proof (cauchy_schwarz_chsh e00 e01 e10 e11) as HCS.
  pose proof (correlation_squares_bound e00 e01 e10 e11 He00 He01 He10 He11) as Hsq.
  nra.
Qed.

(** [chsh_squared_bound_from_correlations] derives the squared bound from its
    explicitly supplied sum-of-squares premise. *)
Lemma chsh_squared_bound_from_correlations : forall e00 e01 e10 e11 : Q,
  Qabs e00 <= 1 -> Qabs e01 <= 1 -> Qabs e10 <= 1 -> Qabs e11 <= 1 ->
  (* The sum-of-squares inequality is an explicit premise of this lemma. *)
  e00*e00 + e01*e01 + e10*e10 + e11*e11 <= 2 ->
  (e00 + e01 + e10 - e11) * (e00 + e01 + e10 - e11) <= 8.
Proof.
  intros e00 e01 e10 e11 He00 He01 He10 He11 Hsum.
  apply Qabs_Qle_condition in He00. destruct He00.
  apply Qabs_Qle_condition in He01. destruct He01.
  apply Qabs_Qle_condition in He10. destruct He10.
  apply Qabs_Qle_condition in He11. destruct He11.
  pose proof (cauchy_schwarz_chsh e00 e01 e10 e11).
  nra.
Qed.

(** [symmetric_minor_implies_sum_bound] reduces the supplied minor inequality
    at parameter zero to [4 * e^2 <= 2]. *)
Lemma symmetric_minor_implies_sum_bound : forall e : Q,
  0 <= minor_3x3 0 e e ->
  4 * (e*e) <= 2.
Proof.
  intros e Hminor.
  unfold minor_3x3 in Hminor.
  nra.
Qed.

(** [symmetric_case_implies_tsirelson] is another symmetric rational bound with
    the parameter fixed to zero. The conclusion uses the declared comparison
    value [5657/2000]; no irrational optimizer is represented. *)
Theorem symmetric_case_implies_tsirelson : forall e : Q,
  Qabs e <= 1 ->
  0 <= minor_3x3 0 e e ->
  0 <= minor_3x3 0 e (-e) ->
  Qabs (4 * e) <= (5657#2000).
Proof.
  intros e He Hm1 Hm2.
  unfold minor_3x3 in *.
  apply Qabs_Qle_condition in He. destruct He as [Hel Heu].
  apply Qabs_Qle_condition.
  split; nra.
Qed.

(** General bound: |S| <= 4 from correlation bounds.

    This is the strongest general theorem in this file. The symmetric lemmas
    above are stronger, but they have symmetric hypotheses. *)
Theorem chsh_general_bound : forall c : Correlators,
  Qabs (E00 c) <= 1 -> Qabs (E01 c) <= 1 -> 
  Qabs (E10 c) <= 1 -> Qabs (E11 c) <= 1 ->
  Qabs (S_from_correlators c) <= 4.
Proof.
  intros c He00 He01 He10 He11.
  unfold S_from_correlators.
  apply Qabs_Qle_condition in He00. destruct He00 as [He00a He00b].
  apply Qabs_Qle_condition in He01. destruct He01 as [He01a He01b].
  apply Qabs_Qle_condition in He10. destruct He10 as [He10a He10b].
  apply Qabs_Qle_condition in He11. destruct He11 as [He11a He11b].
  apply Qabs_Qle_condition.
  split; nra.
Qed.

(** [tsirelson_config] is the symmetric rational family
    [E00 = E01 = E10 = e] and [E11 = -e]. *)
Definition tsirelson_config (e : Q) : Correlators :=
  {| E00 := e; E01 := e; E10 := e; E11 := -e |}.

(** [tsirelson_config_S] records the exact value of [S_from_correlators]
    on the symmetric family. *)
Lemma tsirelson_config_S : forall e : Q, S_from_correlators (tsirelson_config e) == 4 * e.
Proof.
  intros e. unfold S_from_correlators, tsirelson_config. simpl. ring.
Qed.

(** Scope boundary:
    This file establishes the symmetric rational witness and its exact
    coherence calculation. A general optimizer proof for the full Tsirelson
    maximum is outside this file's theorem surface. *)

(** [tsirelson_achieving] is an exact rational witness near the comparison
    value [2 * sqrt 2]. The theorem statements below establish the rational
    values and predicate membership; they do not represent an irrational
    optimizer. *)
Definition tsirelson_achieving : Correlators :=
  {| E00 := 7071#10000;
     E01 := 7071#10000;
     E10 := 7071#10000;
     E11 := -(7071#10000) |}.

(** [tsirelson_achieving_coherent] proves membership of the displayed witness
    in the exact predicate [algebraically_coherent], using rational arithmetic. *)
Lemma tsirelson_achieving_coherent : algebraically_coherent tsirelson_achieving.
Proof.
  unfold algebraically_coherent, tsirelson_achieving. simpl.
  repeat split.
  - unfold Qabs. simpl. unfold Qle. simpl. lia.
  - unfold Qabs. simpl. unfold Qle. simpl. lia.
  - unfold Qabs. simpl. unfold Qle. simpl. lia.
  - unfold Qabs. simpl. unfold Qle. simpl. lia.
  - exists 0. exists 0.
    unfold minor_3x3. simpl.
    repeat split; unfold Qle; simpl; lia.
Qed.

(** [tsirelson_achieving_value] computes the exact rational value of [S] for
    the displayed witness. *)
Lemma tsirelson_achieving_value : S_from_correlators tsirelson_achieving == (28284#10000).
Proof.
  unfold S_from_correlators, tsirelson_achieving. simpl. ring.
Qed.

(** [tsirelson_bound_tight] is a lower-bound witness for the selected rational
    predicate. It gives existence at [28284/10000]; it is not an exact
    optimizer theorem and carries no VM or ledger claim. *)
Theorem tsirelson_bound_tight :
  exists c : Correlators,
    algebraically_coherent c /\
    S_from_correlators c >= (28284#10000).
Proof.
  exists tsirelson_achieving.
  split.
  - exact tsirelson_achieving_coherent.
  - rewrite tsirelson_achieving_value. unfold Qle. simpl. lia.
Qed.


(** The following theorem proves the global squared bound for this selected
    rational predicate. The proof uses its minor witnesses and an SOS
    certificate over [Q]. *)

(* SCOPE NOTE: foundation connectivity — the theorem uses the minor witnesses
   and [psatz Q 4] supplies the required rational SOS certificate. *)
Theorem algebraically_coherent_tsirelson_general :
  forall c : Correlators,
    algebraically_coherent c ->
    (S_from_correlators c) * (S_from_correlators c) <= 8.
Proof.
  intros c Hcoh.
  unfold algebraically_coherent in Hcoh.
  destruct Hcoh as [H00 [H01 [H10 [H11 [t [s [M1 [M2 [M3 M4]]]]]]]]].
  apply Qabs_bound in H00, H01, H10, H11.
  destruct H00 as [H00a H00b].
  destruct H01 as [H01a H01b].
  destruct H10 as [H10a H10b].
  destruct H11 as [H11a H11b].
  unfold S_from_correlators, minor_3x3 in *.
  psatz Q 4.
Qed.

(** Absolute-value form of the preceding rational squared bound. *)
Corollary algebraically_coherent_tsirelson_abs :
  forall c : Correlators,
    algebraically_coherent c ->
    Qabs (S_from_correlators c) <= (5657#2000).
Proof.
  intros c Hcoh.
  pose proof (algebraically_coherent_tsirelson_general c Hcoh) as Hsq.
  apply Qabs_Qle_condition.
  split; nra.
Qed.
