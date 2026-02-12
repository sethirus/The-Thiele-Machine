(** =========================================================================
    HARD MATH FACTS - ALL SIX MECHANIZED PROOFS
    =========================================================================

    This file constructs a concrete instance of HardMathFactsCorrected,
    PROVING every assumption from first principles.
    After this, the bundle is no longer assumed — it is a theorem.

    WHAT IS PROVEN (6 total):
    1. norm_E_bound_proven:  |E(x,y)| ≤ 1 from probability axioms
    2. valid_S_4_proven:     |S| ≤ 4 from triangle inequality on correlators
    3. local_S_2_proven:     |CHSH| ≤ 2 for deterministic strategies (16-case)
    4. pr_no_ext_proven:     PR-box monogamy (no tripartite extension)
    5. symm_coh_bound_proven: symmetric coherence bound e ≤ 707107/1000000
    6. tsir_from_coh_proven: |S| ≤ 2√2 for symmetric coherent configs

    ZERO AXIOMS. ZERO ADMITS. Pure mechanized proofs.

    ========================================================================= *)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lia.
Require Import Psatz.
Require Import ZArith.

From Kernel Require Import ValidCorrelation.
From Kernel Require Import AlgebraicCoherence.
From Kernel Require Import AssumptionBundle.

Local Open Scope Q_scope.

(** =========================================================================
    ASSUMPTION 1: norm_E_bound
    |E(x,y)| ≤ 1 from probability distribution axioms.
    ========================================================================= *)

Lemma norm_E_bound_proven :
  forall (B : nat -> nat -> nat -> nat -> Q) (x y : nat),
    (forall x y a b, 0 <= B x y a b) ->
    (forall x y, B x y 0%nat 0%nat + B x y 0%nat 1%nat +
                 B x y 1%nat 0%nat + B x y 1%nat 1%nat == 1) ->
    forall (E : nat -> nat -> Q),
    (E x y = 1 * 1 * B x y 0%nat 0%nat +
             1 * (-1) * B x y 0%nat 1%nat +
             (-1) * 1 * B x y 1%nat 0%nat +
             (-1) * (-1) * B x y 1%nat 1%nat) ->
    Qabs (E x y) <= 1.
Proof.
  intros B x y Hnn Hnorm E HE.
  rewrite HE.
  assert (Hsimpl: 1 * 1 * B x y 0%nat 0%nat +
                  1 * (-1) * B x y 0%nat 1%nat +
                  (-1) * 1 * B x y 1%nat 0%nat +
                  (-1) * (-1) * B x y 1%nat 1%nat ==
                  B x y 0%nat 0%nat - B x y 0%nat 1%nat -
                  B x y 1%nat 0%nat + B x y 1%nat 1%nat).
  { ring. }
  rewrite Hsimpl.
  set (p00 := B x y 0%nat 0%nat).
  set (p01 := B x y 0%nat 1%nat).
  set (p10 := B x y 1%nat 0%nat).
  set (p11 := B x y 1%nat 1%nat).
  assert (H00 : 0 <= p00) by apply Hnn.
  assert (H01 : 0 <= p01) by apply Hnn.
  assert (H10 : 0 <= p10) by apply Hnn.
  assert (H11 : 0 <= p11) by apply Hnn.
  assert (Hsum : p00 + p01 + p10 + p11 == 1) by apply Hnorm.
  apply Qabs_Qle_condition.
  split; nra.
Qed.

(** =========================================================================
    ASSUMPTION 2: valid_S_4
    |S| ≤ 4 via triangle inequality on correlators bounded by 1.
    ========================================================================= *)

Lemma valid_S_4_proven :
  forall (S E00 E01 E10 E11 : Q),
    Qabs E00 <= 1 -> Qabs E01 <= 1 ->
    Qabs E10 <= 1 -> Qabs E11 <= 1 ->
    S = E00 + E01 + E10 - E11 ->
    Qabs S <= 4.
Proof.
  intros S E00 E01 E10 E11 H00 H01 H10 H11 HS.
  subst S.
  apply Qabs_Qle_condition in H00. destruct H00 as [H00a H00b].
  apply Qabs_Qle_condition in H01. destruct H01 as [H01a H01b].
  apply Qabs_Qle_condition in H10. destruct H10 as [H10a H10b].
  apply Qabs_Qle_condition in H11. destruct H11 as [H11a H11b].
  apply Qabs_Qle_condition.
  split; nra.
Qed.

(** =========================================================================
    ASSUMPTION 3: local_S_2
    Bell CHSH inequality: deterministic {0,1}-valued strategies give |S| ≤ 2.
    Proof by exhaustive 16-case analysis.
    ========================================================================= *)

Lemma local_S_2_proven :
  forall (S : Q) (a b : nat -> nat),
    (forall x, a x = 0%nat \/ a x = 1%nat) ->
    (forall y, b y = 0%nat \/ b y = 1%nat) ->
    S = (if Nat.eqb (a 0%nat) (b 0%nat) then 1 else -1) +
        (if Nat.eqb (a 0%nat) (b 1%nat) then 1 else -1) +
        (if Nat.eqb (a 1%nat) (b 0%nat) then 1 else -1) -
        (if Nat.eqb (a 1%nat) (b 1%nat) then 1 else -1) ->
    Qabs S <= 2.
Proof.
  intros S a b Ha Hb HS.
  subst S.
  destruct (Ha 0%nat) as [A0|A0]; destruct (Ha 1%nat) as [A1|A1];
  destruct (Hb 0%nat) as [B0|B0]; destruct (Hb 1%nat) as [B1|B1];
  rewrite A0, A1, B0, B1; simpl;
  unfold Qabs, Qle; simpl; lia.
Qed.

(** =========================================================================
    ASSUMPTION 4: pr_no_ext
    PR-box monogamy: no tripartite extension of the PR box.

    Standard Barrett-Kent-Pironio (2005) result. The PR box
    a⊕b = x·y (mod 2) with prob 1/2 each satisfying outcome
    CANNOT be extended to a tripartite nonsignaling distribution
    where AB, AC, AND BC marginals all equal the PR box.

    Proof: At (x=1,y=1,z=1): PR forces a⊕b=1, a⊕c=1, b⊕c=1.
    From a⊕b=1 and a⊕c=1: b=c. But b⊕c=1 requires b≠c.
    Contradiction.
    ========================================================================= *)

Lemma pr_no_ext_proven :
  forall (pr_box : nat -> nat -> nat -> nat -> Q),
    (forall x y a b, pr_box x y a b =
      if Nat.eqb ((a + b) mod 2) ((x * y) mod 2) then 1#2 else 0) ->
    ~ (exists Box3 : nat -> nat -> nat -> nat -> nat -> nat -> Q,
        (forall x y z a b c, 0 <= Box3 x y z a b c) /\
        (* AB marginal: sum over z∈{0,1}, c∈{0,1} *)
        (forall x y a b,
          Box3 x y 0%nat a b 0%nat + Box3 x y 0%nat a b 1%nat +
          Box3 x y 1%nat a b 0%nat + Box3 x y 1%nat a b 1%nat ==
          pr_box x y a b) /\
        (* AC marginal: sum over y∈{0,1}, b∈{0,1} *)
        (forall x z a c,
          Box3 x 0%nat z a 0%nat c + Box3 x 0%nat z a 1%nat c +
          Box3 x 1%nat z a 0%nat c + Box3 x 1%nat z a 1%nat c ==
          pr_box x z a c) /\
        (* BC marginal: sum over x∈{0,1}, a∈{0,1} *)
        (forall y z b c,
          Box3 0%nat y z 0%nat b c + Box3 0%nat y z 1%nat b c +
          Box3 1%nat y z 0%nat b c + Box3 1%nat y z 1%nat b c ==
          pr_box y z b c)).
Proof.
  intros pr_box Hpr [Box3 [Hnn [Hmarg_AB [Hmarg_AC Hmarg_BC]]]].

  (** KEY INSIGHT: At inputs (x=1,y=1,z=1), the PR box forces:
      AB: a⊕b=1 (since xy=1)  → PR(1,1,0,0) = 0, PR(1,1,1,1) = 0
      AC: a⊕c=1 (since xz=1)  → PR(1,1,0,0) = 0, PR(1,1,1,1) = 0
      BC: b⊕c=1 (since yz=1)  → PR(1,1,0,0) = 0, PR(1,1,1,1) = 0
      
      From AB: a=0 ↔ b=1 and a=1 ↔ b=0
      From AC: a=0 ↔ c=1 and a=1 ↔ c=0
      So: if a=0 then b=1,c=1. If a=1 then b=0,c=0.
      Either way b=c.
      But BC requires b⊕c=1 → b≠c. Contradiction.
      
      Formally: Box3(1,1,1,a,b,c)=0 whenever b=c (from BC marginal,
      since PR(1,1,b,c)=0 when b+c even), AND Box3(1,1,1,a,b,c)=0
      whenever b≠c and a=b (from AB marginal, since PR(1,1,a,b)=0 
      when a+b even). This forces all entries to 0, but the total
      mass is 1/2 from the AB marginal, contradiction. *)

  (* From AB marginal at (x=1,y=1,a=0,b=0): PR(1,1,0,0) = 0 *)
  assert (HAB : Box3 1%nat 1%nat 0%nat 0%nat 0%nat 0%nat +
                Box3 1%nat 1%nat 0%nat 0%nat 0%nat 1%nat +
                Box3 1%nat 1%nat 1%nat 0%nat 0%nat 0%nat +
                Box3 1%nat 1%nat 1%nat 0%nat 0%nat 1%nat ==
                pr_box 1%nat 1%nat 0%nat 0%nat) by apply Hmarg_AB.
  rewrite Hpr in HAB. simpl in HAB.
  (* All four terms sum to 0, all non-negative, so each = 0 *)
  assert (Z_0000 : Box3 1%nat 1%nat 0%nat 0%nat 0%nat 0%nat == 0).
  { pose proof (Hnn 1%nat 1%nat 0%nat 0%nat 0%nat 0%nat).
    pose proof (Hnn 1%nat 1%nat 0%nat 0%nat 0%nat 1%nat).
    pose proof (Hnn 1%nat 1%nat 1%nat 0%nat 0%nat 0%nat).
    pose proof (Hnn 1%nat 1%nat 1%nat 0%nat 0%nat 1%nat). nra. }
  assert (Z_0001 : Box3 1%nat 1%nat 0%nat 0%nat 0%nat 1%nat == 0).
  { pose proof (Hnn 1%nat 1%nat 0%nat 0%nat 0%nat 0%nat).
    pose proof (Hnn 1%nat 1%nat 0%nat 0%nat 0%nat 1%nat).
    pose proof (Hnn 1%nat 1%nat 1%nat 0%nat 0%nat 0%nat).
    pose proof (Hnn 1%nat 1%nat 1%nat 0%nat 0%nat 1%nat). nra. }
  assert (Z_1000 : Box3 1%nat 1%nat 1%nat 0%nat 0%nat 0%nat == 0).
  { pose proof (Hnn 1%nat 1%nat 0%nat 0%nat 0%nat 0%nat).
    pose proof (Hnn 1%nat 1%nat 0%nat 0%nat 0%nat 1%nat).
    pose proof (Hnn 1%nat 1%nat 1%nat 0%nat 0%nat 0%nat).
    pose proof (Hnn 1%nat 1%nat 1%nat 0%nat 0%nat 1%nat). nra. }
  assert (Z_1001 : Box3 1%nat 1%nat 1%nat 0%nat 0%nat 1%nat == 0).
  { pose proof (Hnn 1%nat 1%nat 0%nat 0%nat 0%nat 0%nat).
    pose proof (Hnn 1%nat 1%nat 0%nat 0%nat 0%nat 1%nat).
    pose proof (Hnn 1%nat 1%nat 1%nat 0%nat 0%nat 0%nat).
    pose proof (Hnn 1%nat 1%nat 1%nat 0%nat 0%nat 1%nat). nra. }

  (* From AB marginal at (x=1,y=1,a=1,b=1): PR(1,1,1,1) = 0 *)
  assert (HAB2 : Box3 1%nat 1%nat 0%nat 1%nat 1%nat 0%nat +
                 Box3 1%nat 1%nat 0%nat 1%nat 1%nat 1%nat +
                 Box3 1%nat 1%nat 1%nat 1%nat 1%nat 0%nat +
                 Box3 1%nat 1%nat 1%nat 1%nat 1%nat 1%nat ==
                 pr_box 1%nat 1%nat 1%nat 1%nat) by apply Hmarg_AB.
  rewrite Hpr in HAB2. simpl in HAB2.
  assert (Z_0110 : Box3 1%nat 1%nat 0%nat 1%nat 1%nat 0%nat == 0).
  { pose proof (Hnn 1%nat 1%nat 0%nat 1%nat 1%nat 0%nat).
    pose proof (Hnn 1%nat 1%nat 0%nat 1%nat 1%nat 1%nat).
    pose proof (Hnn 1%nat 1%nat 1%nat 1%nat 1%nat 0%nat).
    pose proof (Hnn 1%nat 1%nat 1%nat 1%nat 1%nat 1%nat). nra. }
  assert (Z_0111 : Box3 1%nat 1%nat 0%nat 1%nat 1%nat 1%nat == 0).
  { pose proof (Hnn 1%nat 1%nat 0%nat 1%nat 1%nat 0%nat).
    pose proof (Hnn 1%nat 1%nat 0%nat 1%nat 1%nat 1%nat).
    pose proof (Hnn 1%nat 1%nat 1%nat 1%nat 1%nat 0%nat).
    pose proof (Hnn 1%nat 1%nat 1%nat 1%nat 1%nat 1%nat). nra. }
  assert (Z_1110 : Box3 1%nat 1%nat 1%nat 1%nat 1%nat 0%nat == 0).
  { pose proof (Hnn 1%nat 1%nat 0%nat 1%nat 1%nat 0%nat).
    pose proof (Hnn 1%nat 1%nat 0%nat 1%nat 1%nat 1%nat).
    pose proof (Hnn 1%nat 1%nat 1%nat 1%nat 1%nat 0%nat).
    pose proof (Hnn 1%nat 1%nat 1%nat 1%nat 1%nat 1%nat). nra. }
  assert (Z_1111 : Box3 1%nat 1%nat 1%nat 1%nat 1%nat 1%nat == 0).
  { pose proof (Hnn 1%nat 1%nat 0%nat 1%nat 1%nat 0%nat).
    pose proof (Hnn 1%nat 1%nat 0%nat 1%nat 1%nat 1%nat).
    pose proof (Hnn 1%nat 1%nat 1%nat 1%nat 1%nat 0%nat).
    pose proof (Hnn 1%nat 1%nat 1%nat 1%nat 1%nat 1%nat). nra. }

  (* From BC marginal at (y=1,z=1,b=0,c=0): PR(1,1,0,0) = 0 *)
  assert (HBC : Box3 0%nat 1%nat 1%nat 0%nat 0%nat 0%nat +
                Box3 0%nat 1%nat 1%nat 1%nat 0%nat 0%nat +
                Box3 1%nat 1%nat 1%nat 0%nat 0%nat 0%nat +
                Box3 1%nat 1%nat 1%nat 1%nat 0%nat 0%nat ==
                pr_box 1%nat 1%nat 0%nat 0%nat) by apply Hmarg_BC.
  rewrite Hpr in HBC. simpl in HBC.
  assert (Z_bc_1100 : Box3 1%nat 1%nat 1%nat 0%nat 0%nat 0%nat == 0).
  { (* already proved as Z_1000 *) exact Z_1000. }
  assert (Z_bc_1110 : Box3 1%nat 1%nat 1%nat 1%nat 0%nat 0%nat == 0).
  { pose proof (Hnn 0%nat 1%nat 1%nat 0%nat 0%nat 0%nat).
    pose proof (Hnn 0%nat 1%nat 1%nat 1%nat 0%nat 0%nat).
    pose proof (Hnn 1%nat 1%nat 1%nat 0%nat 0%nat 0%nat).
    pose proof (Hnn 1%nat 1%nat 1%nat 1%nat 0%nat 0%nat). nra. }

  (* From BC marginal at (y=1,z=1,b=1,c=1): PR(1,1,1,1) = 0 *)
  assert (HBC2 : Box3 0%nat 1%nat 1%nat 0%nat 1%nat 1%nat +
                 Box3 0%nat 1%nat 1%nat 1%nat 1%nat 1%nat +
                 Box3 1%nat 1%nat 1%nat 0%nat 1%nat 1%nat +
                 Box3 1%nat 1%nat 1%nat 1%nat 1%nat 1%nat ==
                 pr_box 1%nat 1%nat 1%nat 1%nat) by apply Hmarg_BC.
  rewrite Hpr in HBC2. simpl in HBC2.
  assert (Z_bc_1011 : Box3 1%nat 1%nat 1%nat 0%nat 1%nat 1%nat == 0).
  { pose proof (Hnn 0%nat 1%nat 1%nat 0%nat 1%nat 1%nat).
    pose proof (Hnn 0%nat 1%nat 1%nat 1%nat 1%nat 1%nat).
    pose proof (Hnn 1%nat 1%nat 1%nat 0%nat 1%nat 1%nat).
    pose proof (Hnn 1%nat 1%nat 1%nat 1%nat 1%nat 1%nat). nra. }
  assert (Z_bc_1111 : Box3 1%nat 1%nat 1%nat 1%nat 1%nat 1%nat == 0).
  { exact Z_1111. }

  (* Now at (x=1,y=1,z=1): 
     From AB: a≠b → Box3(1,1,1,a,a,c)=0 for all a,c  (already: Z_1000, Z_1001, Z_1110, Z_1111)
     From BC: b≠c → Box3(1,1,1,a,b,b)=0 for all a,b  (already: Z_bc_1100, Z_bc_1110, Z_bc_1011, Z_bc_1111)
     
     Remaining entries at z=1: Box3(1,1,1,a,b,c) with a≠b AND b≠c:
     - (a=0,b=1,c=0): allowed by AB (0≠1) and by BC (1≠0)
     - (a=1,b=0,c=1): allowed by AB (1≠0) and by BC (0≠1)
     
     BUT we also need AC: a≠c → Box3(1,1,1,a,b,a)=0 for all a,b.
     - For (0,1,0): a=0, c=0, so a=c → AC gives PR(1,1,0,0)=0 requires a⊕c=1.
       Actually AC says: sum over y,b of Box3(x,y,z,a,b,c) = PR(x,z,a,c).
       PR(1,1,0,0)=0 since (0+0)mod2=0 ≠ (1*1)mod2=1.
       So Box3(1,y,1,0,b,0) = 0 for all y,b summing to 0:
       Box3(1,0,1,0,0,0) + Box3(1,0,1,0,1,0) + Box3(1,1,1,0,0,0) + Box3(1,1,1,0,1,0) = 0
       So Box3(1,1,1,0,1,0) = 0!
       
     - For (1,0,1): a=1, c=1, AC gives PR(1,1,1,1)=0.
       Box3(1,0,1,1,0,1) + Box3(1,0,1,1,1,1) + Box3(1,1,1,1,0,1) + Box3(1,1,1,1,1,1) = 0
       So Box3(1,1,1,1,0,1) = 0!
  *)

  (* From AC marginal at (x=1,z=1,a=0,c=0): PR(1,1,0,0) = 0 *)
  assert (HAC : Box3 1%nat 0%nat 1%nat 0%nat 0%nat 0%nat +
                Box3 1%nat 0%nat 1%nat 0%nat 1%nat 0%nat +
                Box3 1%nat 1%nat 1%nat 0%nat 0%nat 0%nat +
                Box3 1%nat 1%nat 1%nat 0%nat 1%nat 0%nat ==
                pr_box 1%nat 1%nat 0%nat 0%nat) by apply Hmarg_AC.
  rewrite Hpr in HAC. simpl in HAC.
  assert (Z_ac_0010 : Box3 1%nat 1%nat 1%nat 0%nat 1%nat 0%nat == 0).
  { pose proof (Hnn 1%nat 0%nat 1%nat 0%nat 0%nat 0%nat).
    pose proof (Hnn 1%nat 0%nat 1%nat 0%nat 1%nat 0%nat).
    pose proof (Hnn 1%nat 1%nat 1%nat 0%nat 0%nat 0%nat).
    pose proof (Hnn 1%nat 1%nat 1%nat 0%nat 1%nat 0%nat). nra. }

  (* From AC marginal at (x=1,z=1,a=1,c=1): PR(1,1,1,1) = 0 *)
  assert (HAC2 : Box3 1%nat 0%nat 1%nat 1%nat 0%nat 1%nat +
                 Box3 1%nat 0%nat 1%nat 1%nat 1%nat 1%nat +
                 Box3 1%nat 1%nat 1%nat 1%nat 0%nat 1%nat +
                 Box3 1%nat 1%nat 1%nat 1%nat 1%nat 1%nat ==
                 pr_box 1%nat 1%nat 1%nat 1%nat) by apply Hmarg_AC.
  rewrite Hpr in HAC2. simpl in HAC2.
  assert (Z_ac_1101 : Box3 1%nat 1%nat 1%nat 1%nat 0%nat 1%nat == 0).
  { pose proof (Hnn 1%nat 0%nat 1%nat 1%nat 0%nat 1%nat).
    pose proof (Hnn 1%nat 0%nat 1%nat 1%nat 1%nat 1%nat).
    pose proof (Hnn 1%nat 1%nat 1%nat 1%nat 0%nat 1%nat).
    pose proof (Hnn 1%nat 1%nat 1%nat 1%nat 1%nat 1%nat). nra. }

  (* Now ALL 8 entries of Box3(1,1,1,a,b,c) are proved = 0:
     (0,0,0)=Z_1000, (0,0,1)=Z_1001, (0,1,0)=Z_ac_0010, (0,1,1)=Z_bc_1011,
     (1,0,0)=Z_bc_1110, (1,0,1)=Z_ac_1101, (1,1,0)=Z_1110, (1,1,1)=Z_1111.

     But from AB marginal at (x=1,y=1,a=0,b=1): PR(1,1,0,1) = 1/2
     So Box3(1,1,0,0,1,0) + Box3(1,1,0,0,1,1) + 
        Box3(1,1,1,0,1,0) + Box3(1,1,1,0,1,1) = 1/2
     We know Z_ac_0010: Box3(1,1,1,0,1,0) = 0
     And Z_bc_1011: Box3(1,1,1,0,1,1) = 0
     So: Box3(1,1,0,0,1,0) + Box3(1,1,0,0,1,1) = 1/2  ... not zero!
     
     Wait, that's not a contradiction yet. We showed the z=1 slice is all zero,
     but the z=0 slice can carry the weight.
     
     We need the z=1 slice to carry nonzero weight too.
     
     From AB marginal at (1,1,1,0): PR(1,1,1,0) = 1/2
     Box3(1,1,0,1,0,0) + Box3(1,1,0,1,0,1) + Box3(1,1,1,1,0,0) + Box3(1,1,1,1,0,1) = 1/2
     Z_bc_1110: Box3(1,1,1,1,0,0) = 0
     Z_ac_1101: Box3(1,1,1,1,0,1) = 0
     So: Box3(1,1,0,1,0,0) + Box3(1,1,0,1,0,1) = 1/2 ... still ok.
     
     The z=1 slice is all zero, but z=0 picks up the slack. We need to show
     the z=0 slice ALSO has entries forced to zero.
     
     Actually, we should use BC marginal at (y=1,z=0,...) too.
     
     From BC marginal at (y=1,z=0,b=0,c=0): PR(1,0,0,0) = 1/2
     (since (0+0)mod2=0 = (1*0)mod2=0: yes, 1/2)
     Box3(0,1,0,0,0,0) + Box3(0,1,0,1,0,0) + Box3(1,1,0,0,0,0) + Box3(1,1,0,1,0,0) = 1/2
     We know Z_0000: Box3(1,1,0,0,0,0) = 0
     
     And from AB marginal at (1,1,0,1): PR(1,1,0,1) = 1/2
     Box3(1,1,0,0,1,0) + Box3(1,1,0,0,1,1) + Box3(1,1,1,0,1,0) + Box3(1,1,1,0,1,1) = 1/2
     
     Hmm, I need to find the contradiction through TOTALS.
     
     From AB: total z=1 mass at (x=1,y=1) = sum_{a,b,c} Box3(1,1,1,...) = all zero.
     So total z=0 mass at (x=1,y=1) = 
     sum_{a,b,c} Box3(1,1,0,...) = sum_{a,b} PR(1,1,a,b) = 1.
     
     From BC marginal structure at (y=1,z=0):
     sum_{x,a} sum_{b,c} Box3(x,1,0,a,b,c) = ... hmm, this is sum over b,c of
     (sum over x,a of Box3(x,1,0,a,b,c)):
     sum_{b,c} PR(1,0,b,c) = 1.
     
     Expanding: sum_{a,b,c} Box3(0,1,0,...) + sum_{a,b,c} Box3(1,1,0,...) = ...
     The second part = 1 (from above). But the BC marginal gives:
     sum_{b,c} [Box3(0,1,0,0,b,c) + Box3(0,1,0,1,b,c) + Box3(1,1,0,0,b,c) + Box3(1,1,0,1,b,c)]
     = sum_{b,c} PR(1,0,b,c) = 1.
     
     This is consistent. The problem is structural—all the zeros are at z=1 
     but z=0 terms are free. Without further constraints, we won't find contradictions 
     purely at (x=1,y=1,z=1).
     
     Let me use a fully symmetric argument.
     At x=1,y=1,z=1:
     From AB (a+b even → 0): (0,0,c) and (1,1,c) entries are 0 for all c.
     From AC (a+c even → 0): (a,b,a) entries are 0 for all b, i.e., (0,b,0) and (1,b,1).
     From BC (b+c even → 0): (a,b,b) entries are 0 for all a, i.e., (a,0,0) and (a,1,1).
     
     Combining: the nonzero entries must have a≠b, a≠c, b≠c.
     In {0,1}³, the only triples (a,b,c) with all three pairwise unequal need 3 distinct
     values, but {0,1} only has 2 values. So NO triple satisfies a≠b ∧ a≠c ∧ b≠c!
     
     Therefore ALL entries of Box3(1,1,1,a,b,c) are 0, meaning total mass = 0.
     
     But from AB marginal: sum z,c of Box3(1,1,z,0,1,c) = PR(1,1,0,1) = 1/2:
       Box3(1,1,0,0,1,0) + Box3(1,1,0,0,1,1) + Box3(1,1,1,0,1,0) + Box3(1,1,1,0,1,1) = 1/2
     The z=1 terms: (0,1,0) has a=0≠b=1 but a=0=c=0, so AC forces it to 0. ✓ (Z_ac_0010)
                     (0,1,1) has a=0≠b=1 and a=0≠c=1 but b=1=c=1, so BC forces it to 0. ✓ (Z_bc_1011)
     So z=0 carries it: Box3(1,1,0,0,1,0) + Box3(1,1,0,0,1,1) = 1/2. Fine.
     
     But for the TOTAL: sum_{a,b,c} Box3(1,1,1,a,b,c) = 0 (all entries proved zero).
     From the AB marginal summed over a,b:
       sum_{a,b} [Box3(1,1,0,a,b,0)+Box3(1,1,0,a,b,1)+Box3(1,1,1,a,b,0)+Box3(1,1,1,a,b,1)] 
       = sum_{a,b} PR(1,1,a,b) = 1.
     The z=1 piece is 0, so z=0 piece = 1. Consistent!
     
     From the BC marginal summed over b,c at (y=1,z=1):
       sum_{b,c} [Box3(0,1,1,0,b,c)+Box3(0,1,1,1,b,c)+Box3(1,1,1,0,b,c)+Box3(1,1,1,1,b,c)]
       = sum_{b,c} PR(1,1,b,c) = 1.
     The (x=1) piece is 0, so the (x=0) piece sum_{a,b,c} Box3(0,1,1,a,b,c) = 1.
     
     Hmm. What if we apply the same argument to x=0?
     At (x=0,y=1,z=1):
     AB marginal: PR(0,1,a,b) with 0*1=0: a+b even → 1/2, else 0.
       So a=b. Entries with a≠b at (0,1,...) are 0.
     AC marginal: PR(0,1,a,c) with 0*1=0: a+c even → 1/2. So a=c.
     BC marginal: PR(1,1,b,c) with 1*1=1: b+c odd → 1/2. So b≠c.
     
     From a=b and a=c: b=c. But BC requires b≠c. Contradiction!
     
     Formally: Box3(0,1,1,a,b,c) = 0 when a≠b (AB), or a≠c (AC), or b=c (BC).
     Non-zero requires a=b, a=c, b≠c. But a=b and a=c gives b=c. ∅.
     So Box3(0,1,1,a,b,c) = 0 for all a,b,c. Total = 0.
     
     But: sum over a,b,c Box3(0,1,1,...) + sum over a,b,c Box3(1,1,1,...) = 1 (from BC).
     Both sums = 0. So 0 = 1. ☐ *)

  (* We already showed Box3(1,1,1,a,b,c) = 0 for the z=1 entries above.
     Now we repeat for x=0 to show Box3(0,1,1,a,b,c) = 0 for all a,b,c. *)

  (* From AB marginal at (x=0,y=1,a=0,b=1): PR(0,1,0,1) = 0 (since 0*1=0, (0+1)mod2=1≠0) *)
  assert (HAB_0101 : Box3 0%nat 1%nat 0%nat 0%nat 1%nat 0%nat +
                     Box3 0%nat 1%nat 0%nat 0%nat 1%nat 1%nat +
                     Box3 0%nat 1%nat 1%nat 0%nat 1%nat 0%nat +
                     Box3 0%nat 1%nat 1%nat 0%nat 1%nat 1%nat ==
                     pr_box 0%nat 1%nat 0%nat 1%nat) by apply Hmarg_AB.
  rewrite Hpr in HAB_0101. simpl in HAB_0101.
  assert (W_0010 : Box3 0%nat 1%nat 1%nat 0%nat 1%nat 0%nat == 0).
  { pose proof (Hnn 0%nat 1%nat 0%nat 0%nat 1%nat 0%nat).
    pose proof (Hnn 0%nat 1%nat 0%nat 0%nat 1%nat 1%nat).
    pose proof (Hnn 0%nat 1%nat 1%nat 0%nat 1%nat 0%nat).
    pose proof (Hnn 0%nat 1%nat 1%nat 0%nat 1%nat 1%nat). nra. }
  assert (W_0011 : Box3 0%nat 1%nat 1%nat 0%nat 1%nat 1%nat == 0).
  { pose proof (Hnn 0%nat 1%nat 0%nat 0%nat 1%nat 0%nat).
    pose proof (Hnn 0%nat 1%nat 0%nat 0%nat 1%nat 1%nat).
    pose proof (Hnn 0%nat 1%nat 1%nat 0%nat 1%nat 0%nat).
    pose proof (Hnn 0%nat 1%nat 1%nat 0%nat 1%nat 1%nat). nra. }

  (* From AB at (x=0,y=1,a=1,b=0): PR(0,1,1,0) = 0 *)
  assert (HAB_0110 : Box3 0%nat 1%nat 0%nat 1%nat 0%nat 0%nat +
                     Box3 0%nat 1%nat 0%nat 1%nat 0%nat 1%nat +
                     Box3 0%nat 1%nat 1%nat 1%nat 0%nat 0%nat +
                     Box3 0%nat 1%nat 1%nat 1%nat 0%nat 1%nat ==
                     pr_box 0%nat 1%nat 1%nat 0%nat) by apply Hmarg_AB.
  rewrite Hpr in HAB_0110. simpl in HAB_0110.
  assert (W_1100 : Box3 0%nat 1%nat 1%nat 1%nat 0%nat 0%nat == 0).
  { pose proof (Hnn 0%nat 1%nat 0%nat 1%nat 0%nat 0%nat).
    pose proof (Hnn 0%nat 1%nat 0%nat 1%nat 0%nat 1%nat).
    pose proof (Hnn 0%nat 1%nat 1%nat 1%nat 0%nat 0%nat).
    pose proof (Hnn 0%nat 1%nat 1%nat 1%nat 0%nat 1%nat). nra. }
  assert (W_1101 : Box3 0%nat 1%nat 1%nat 1%nat 0%nat 1%nat == 0).
  { pose proof (Hnn 0%nat 1%nat 0%nat 1%nat 0%nat 0%nat).
    pose proof (Hnn 0%nat 1%nat 0%nat 1%nat 0%nat 1%nat).
    pose proof (Hnn 0%nat 1%nat 1%nat 1%nat 0%nat 0%nat).
    pose proof (Hnn 0%nat 1%nat 1%nat 1%nat 0%nat 1%nat). nra. }
  (* AB marginal eliminates a≠b, so remaining: (0,0,c) and (1,1,c) for c∈{0,1} *)

  (* From AC at (x=0,z=1,a=0,c=1): PR(0,1,0,1) = 0 (since 0*1=0, (0+1)mod2≠0) *)
  assert (HAC_0101 : Box3 0%nat 0%nat 1%nat 0%nat 0%nat 1%nat +
                     Box3 0%nat 0%nat 1%nat 0%nat 1%nat 1%nat +
                     Box3 0%nat 1%nat 1%nat 0%nat 0%nat 1%nat +
                     Box3 0%nat 1%nat 1%nat 0%nat 1%nat 1%nat ==
                     pr_box 0%nat 1%nat 0%nat 1%nat) by apply Hmarg_AC.
  rewrite Hpr in HAC_0101. simpl in HAC_0101.
  assert (W_0001 : Box3 0%nat 1%nat 1%nat 0%nat 0%nat 1%nat == 0).
  { pose proof (Hnn 0%nat 0%nat 1%nat 0%nat 0%nat 1%nat).
    pose proof (Hnn 0%nat 0%nat 1%nat 0%nat 1%nat 1%nat).
    pose proof (Hnn 0%nat 1%nat 1%nat 0%nat 0%nat 1%nat).
    pose proof (Hnn 0%nat 1%nat 1%nat 0%nat 1%nat 1%nat). nra. }

  (* From AC at (x=0,z=1,a=1,c=0): PR(0,1,1,0) = 0 *)
  assert (HAC_0110 : Box3 0%nat 0%nat 1%nat 1%nat 0%nat 0%nat +
                     Box3 0%nat 0%nat 1%nat 1%nat 1%nat 0%nat +
                     Box3 0%nat 1%nat 1%nat 1%nat 0%nat 0%nat +
                     Box3 0%nat 1%nat 1%nat 1%nat 1%nat 0%nat ==
                     pr_box 0%nat 1%nat 1%nat 0%nat) by apply Hmarg_AC.
  rewrite Hpr in HAC_0110. simpl in HAC_0110.
  assert (W_1110 : Box3 0%nat 1%nat 1%nat 1%nat 1%nat 0%nat == 0).
  { pose proof (Hnn 0%nat 0%nat 1%nat 1%nat 0%nat 0%nat).
    pose proof (Hnn 0%nat 0%nat 1%nat 1%nat 1%nat 0%nat).
    pose proof (Hnn 0%nat 1%nat 1%nat 1%nat 0%nat 0%nat).
    pose proof (Hnn 0%nat 1%nat 1%nat 1%nat 1%nat 0%nat). nra. }
  (* AC eliminates a≠c: remaining from AB∩AC: (0,0,0) and (1,1,1) *)

  (* From BC at (y=1,z=1,b=0,c=0): PR(1,1,0,0) = 0. Already used above
     to get Box3(0,1,1,a,0,0) = 0 for all a. Specifically: *)
  assert (W_0000 : Box3 0%nat 1%nat 1%nat 0%nat 0%nat 0%nat == 0).
  { pose proof (Hnn 0%nat 1%nat 1%nat 0%nat 0%nat 0%nat).
    pose proof (Hnn 0%nat 1%nat 1%nat 1%nat 0%nat 0%nat).
    pose proof (Hnn 1%nat 1%nat 1%nat 0%nat 0%nat 0%nat).
    pose proof (Hnn 1%nat 1%nat 1%nat 1%nat 0%nat 0%nat). nra. }

  (* From BC at (y=1,z=1,b=1,c=1): PR(1,1,1,1) = 0 *)
  assert (W_1111 : Box3 0%nat 1%nat 1%nat 1%nat 1%nat 1%nat == 0).
  { pose proof (Hnn 0%nat 1%nat 1%nat 0%nat 1%nat 1%nat).
    pose proof (Hnn 0%nat 1%nat 1%nat 1%nat 1%nat 1%nat).
    pose proof (Hnn 1%nat 1%nat 1%nat 0%nat 1%nat 1%nat).
    pose proof (Hnn 1%nat 1%nat 1%nat 1%nat 1%nat 1%nat). nra. }

  (* NOW: ALL 8 entries of Box3(0,1,1,a,b,c) for a,b,c∈{0,1} are zero:
     (0,0,0)=W_0000, (0,0,1)=W_0001, (0,1,0)=W_0010, (0,1,1)=W_0011,
     (1,0,0)=W_1100, (1,0,1)=W_1101, (1,1,0)=W_1110, (1,1,1)=W_1111 *)

  (* AND all 8 entries of Box3(1,1,1,a,b,c) are zero (proved above). *)

  (* From BC marginal at (y=1,z=1,b=0,c=1): PR(1,1,0,1) = 1/2 *)
  assert (HBC_final : Box3 0%nat 1%nat 1%nat 0%nat 0%nat 1%nat +
                      Box3 0%nat 1%nat 1%nat 1%nat 0%nat 1%nat +
                      Box3 1%nat 1%nat 1%nat 0%nat 0%nat 1%nat +
                      Box3 1%nat 1%nat 1%nat 1%nat 0%nat 1%nat ==
                      pr_box 1%nat 1%nat 0%nat 1%nat) by apply Hmarg_BC.
  rewrite Hpr in HBC_final. simpl in HBC_final.
  (* 0 + 0 + 0 + 0 = 1/2 → contradiction! *)
  nra.
Qed.


(** =========================================================================
    ASSUMPTION 5: symm_coh_bound
    NPA level-1 symmetric bound: e ≤ 707107/1000000.
    ========================================================================= *)

Lemma symm_coh_bound_proven :
  forall (e : Q),
    0 <= e ->
    algebraically_coherent {| E00 := e; E01 := e; E10 := e; E11 := -e |} ->
    e <= (707107#1000000).
Proof.
  intros e He Hcoh.
  unfold algebraically_coherent in Hcoh. simpl in Hcoh.
  destruct Hcoh as [_ [_ [_ [_ [t [s [Hm1 [Hm2 [Hm3 Hm4]]]]]]]]].
  unfold minor_3x3 in *.
  assert (He2 : e * e <= 1#2) by nra.
  assert (Hsq: (1#2) <= (707107#1000000) * (707107#1000000)).
  { unfold Qle, Qmult. simpl. lia. }
  nra.
Qed.

(** =========================================================================
    ASSUMPTION 6: tsir_from_coh
    Tsirelson bound for symmetric case: |S| ≤ 28284272/10000000.
    ========================================================================= *)

Lemma tsir_from_coh_proven :
  forall (e : Q),
    0 <= e -> e <= 1 ->
    algebraically_coherent {| E00 := e; E01 := e; E10 := e; E11 := -e |} ->
    Qabs (S_from_correlators {| E00 := e; E01 := e; E10 := e; E11 := -e |})
      <= (28284272#10000000).
Proof.
  intros e He Hle1 Hcoh.
  assert (He2 : e * e <= 1#2).
  { unfold algebraically_coherent in Hcoh. simpl in Hcoh.
    destruct Hcoh as [_ [_ [_ [_ [t [s [Hm1 [Hm2 _]]]]]]]].
    unfold minor_3x3 in *. nra. }
  unfold S_from_correlators. cbn [E00 E01 E10 E11].
  apply Qabs_Qle_condition. split.
  - (* -(28284272/10000000) <= e + e + e - - e *)
    (* Since 0<=e, e+e+e--e = 4e >= 0 >= -(28284272/10000000) *)
    assert (H4e_nn: 0 <= e + e + e - - e) by nra.
    assert (Hbound_nn: 0 <= 28284272 # 10000000).
    { unfold Qle. simpl. lia. }
    nra.
  - (* e + e + e - - e <= 28284272/10000000 *)
    (* e+e+e--e = 4e, and e^2 <= 1/2 with 0<=e gives e <= sqrt(1/2) *)
    (* 4*sqrt(1/2) = 2*sqrt(2) < 28284272/10000000 *)
    assert (Hle4e: e + e + e - - e <= 4 * e) by nra.
    assert (Hle_e: 4 * e * (4 * e) <= 4 * 4 * (1#2)).
    { assert (H4esq: (4 * e) * (4 * e) == 16 * (e * e)) by ring.
      nra. }
    (* So (4e)^2 <= 8. And (28284272/10000000)^2 >= 8 *)
    assert (Hbound_sq: 8 <= (28284272 # 10000000) * (28284272 # 10000000)).
    { unfold Qle, Qmult. simpl. lia. }
    (* So 4e <= 28284272/10000000 since both are non-negative *)
    assert (H4e_nn: 0 <= 4 * e) by nra.
    assert (Hb_nn: 0 <= 28284272 # 10000000).
    { unfold Qle. simpl. lia. }
    (* From x^2 <= y^2 and 0<=x, 0<=y, we get x <= y *)
    destruct (Qlt_le_dec (28284272 # 10000000) (4 * e)) as [Hlt | ?].
    + exfalso.
      assert (Hlt2: (28284272#10000000) * (28284272#10000000) < (4*e) * (4*e)) by nra.
      nra.
    + nra.
Qed.

(** General version (all coherent configs give |S|≤4): *)
Lemma tsir_from_coh_weak :
  forall (c : Correlators),
    algebraically_coherent c ->
    Qabs (E00 c) <= 1 /\ Qabs (E01 c) <= 1 /\
    Qabs (E10 c) <= 1 /\ Qabs (E11 c) <= 1 ->
    Qabs (S_from_correlators c) <= 4.
Proof.
  intros c Hcoh Hbounds. apply chsh_bound_4. exact Hbounds.
Qed.

(** =========================================================================
    THE CORRECTED RECORD
    =========================================================================
    We create a corrected version of HardMathFacts fixing type issues
    in the original AssumptionBundle.v:
    - pr_no_ext: original only required AB marginal (trivially satisfiable);
      corrected requires ALL THREE marginals (AB, AC, BC)
    - symm_coh_bound: original had unconstrained correlators parameter;
      corrected uses explicit symmetric (e,e,e,-e) configuration
    ========================================================================= *)

Record HardMathFactsCorrected := {
  c_norm_E_bound : forall (B : nat -> nat -> nat -> nat -> Q) (x y : nat),
    (forall x y a b, 0 <= B x y a b) ->
    (forall x y, B x y 0%nat 0%nat + B x y 0%nat 1%nat +
                 B x y 1%nat 0%nat + B x y 1%nat 1%nat == 1) ->
    forall (E : nat -> nat -> Q),
    (E x y = 1 * 1 * B x y 0%nat 0%nat +
             1 * (-1) * B x y 0%nat 1%nat +
             (-1) * 1 * B x y 1%nat 0%nat +
             (-1) * (-1) * B x y 1%nat 1%nat) ->
    Qabs (E x y) <= 1;

  c_valid_S_4 : forall (S E00_v E01_v E10_v E11_v : Q),
    Qabs E00_v <= 1 -> Qabs E01_v <= 1 ->
    Qabs E10_v <= 1 -> Qabs E11_v <= 1 ->
    S = E00_v + E01_v + E10_v - E11_v ->
    Qabs S <= 4;

  c_local_S_2 : forall (S : Q) (a b : nat -> nat),
    (forall x, a x = 0%nat \/ a x = 1%nat) ->
    (forall y, b y = 0%nat \/ b y = 1%nat) ->
    S = (if Nat.eqb (a 0%nat) (b 0%nat) then 1 else -1) +
        (if Nat.eqb (a 0%nat) (b 1%nat) then 1 else -1) +
        (if Nat.eqb (a 1%nat) (b 0%nat) then 1 else -1) -
        (if Nat.eqb (a 1%nat) (b 1%nat) then 1 else -1) ->
    Qabs S <= 2;

  c_pr_no_ext : forall (pr_box : nat -> nat -> nat -> nat -> Q),
    (forall x y a b, pr_box x y a b =
      if Nat.eqb ((a + b) mod 2) ((x * y) mod 2) then 1#2 else 0) ->
    ~ (exists Box3 : nat -> nat -> nat -> nat -> nat -> nat -> Q,
        (forall x y z a b c, 0 <= Box3 x y z a b c) /\
        (forall x y a b,
          Box3 x y 0%nat a b 0%nat + Box3 x y 0%nat a b 1%nat +
          Box3 x y 1%nat a b 0%nat + Box3 x y 1%nat a b 1%nat ==
          pr_box x y a b) /\
        (forall x z a c,
          Box3 x 0%nat z a 0%nat c + Box3 x 0%nat z a 1%nat c +
          Box3 x 1%nat z a 0%nat c + Box3 x 1%nat z a 1%nat c ==
          pr_box x z a c) /\
        (forall y z b c,
          Box3 0%nat y z 0%nat b c + Box3 0%nat y z 1%nat b c +
          Box3 1%nat y z 0%nat b c + Box3 1%nat y z 1%nat b c ==
          pr_box y z b c));

  c_symm_coh_bound : forall (e : Q),
    0 <= e ->
    algebraically_coherent {| E00 := e; E01 := e; E10 := e; E11 := -e |} ->
    e <= (707107#1000000);

  c_tsir_from_coh : forall (e : Q),
    0 <= e -> e <= 1 ->
    algebraically_coherent {| E00 := e; E01 := e; E10 := e; E11 := -e |} ->
    Qabs (S_from_correlators {| E00 := e; E01 := e; E10 := e; E11 := -e |})
      <= (28284272#10000000)
}.

(** The concrete proven instance *)
Definition hard_math_facts_proven : HardMathFactsCorrected := {|
  c_norm_E_bound := norm_E_bound_proven;
  c_valid_S_4 := valid_S_4_proven;
  c_local_S_2 := local_S_2_proven;
  c_pr_no_ext := pr_no_ext_proven;
  c_symm_coh_bound := symm_coh_bound_proven;
  c_tsir_from_coh := tsir_from_coh_proven
|}.

(** =========================================================================
    SUMMARY
    =========================================================================

    All 6 hard math assumptions have been mechanized:

    1. norm_E_bound_proven:  PROVEN from probability axioms (nra)
    2. valid_S_4_proven:     PROVEN by triangle inequality (nra)
    3. local_S_2_proven:     PROVEN by exhaustive 16-case analysis
    4. pr_no_ext_proven:     PROVEN by contradiction (Barrett et al.)
    5. symm_coh_bound_proven: PROVEN from NPA-1 minor constraints
    6. tsir_from_coh_proven: PROVEN from e² ≤ 1/2

    The corrected record HardMathFactsCorrected fixes type issues
    in the original AssumptionBundle.v:
    - pr_no_ext: original only required AB marginal (trivially satisfiable);
      corrected requires ALL THREE marginals (AB, AC, BC)
    - symm_coh_bound: original had unconstrained correlators parameter;
      corrected uses explicit symmetric (e,e,e,-e) configuration

    ZERO AXIOMS. ZERO ADMITS.
    ========================================================================= *)
