(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file is the quantum form of the chairs theorem, over mathcomp's algC: a finite-dimensional unitary step that keeps a projector's range inside itself keeps the complement inside itself, so a no-state never reads yes; it depends on the Mathematical Components library and stands alone from the certification-system kernel. *)
(* The quantum chairs, machine-checked over algC (algebraic numbers with complex conjugation).
   States: column vectors in C^n. Step: a unitary U (adj U * U = 1). A permanent reading: a projector P
   (P*P = P, adj P = P) whose range U maps into itself: (1-P) U P = 0.
   Theorem: U maps the complement into the complement: P U (1-P) = 0. A no-state never reads yes.
   Finite dimension enters exactly once: mulmx1C, a square matrix with a left inverse has it as a right inverse. *)
From mathcomp Require Import all_ssreflect all_algebra all_field.
Set Implicit Arguments. Unset Strict Implicit. Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Quantum.
Variable n : nat.
Local Notation C := algC.
Local Notation conjC := (@Num.conj_op algC).
Definition adj (M : 'M[C]_n) : 'M[C]_n := (map_mx conjC M)^T.

Lemma adjM (A B : 'M[C]_n) : adj (A *m B) = adj B *m adj A.
Proof. by rewrite /adj map_mxM trmx_mul. Qed.
Lemma adjD (A B : 'M[C]_n) : adj (A + B) = adj A + adj B.
Proof. by rewrite /adj map_mxD linearD. Qed.
Lemma adjN (A : 'M[C]_n) : adj (- A) = - adj A.
Proof. by rewrite /adj map_mxN linearN. Qed.
Lemma adj1 : adj (1%:M : 'M[C]_n) = 1%:M.
Proof. by rewrite /adj map_mx1 trmx1. Qed.
Lemma adjB (A B : 'M[C]_n) : adj (A - B) = adj A - adj B.
Proof. by rewrite adjD adjN. Qed.

Variables U P : 'M[C]_n.
Hypothesis unitary : adj U *m U = 1%:M.
Hypothesis proj_idem : P *m P = P.
Hypothesis proj_herm : adj P = P.
Hypothesis invariant : (1%:M - P) *m U *m P = 0.

Definition Q : 'M[C]_n := 1%:M - P.
Definition V : 'M[C]_n := P *m U *m P.

Lemma PQ : P *m Q = 0.
Proof. by rewrite /Q mulmxBr mulmx1 proj_idem subrr. Qed.
Lemma QP : Q *m P = 0.
Proof. by rewrite /Q mulmxBl mul1mx proj_idem subrr. Qed.
Lemma QQ : Q *m Q = Q.
Proof. by rewrite /Q mulmxBr mulmx1 mulmxBl mul1mx proj_idem subrr subr0. Qed.
Lemma adjQ : adj Q = Q.
Proof. by rewrite /Q adjB adj1 proj_herm. Qed.
Lemma PQ1 : P + Q = 1%:M.
Proof. by rewrite /Q addrC subrK. Qed.

(* invariance says U P = P U P *)
Lemma UP_eq : U *m P = V.
Proof.
  move: invariant; rewrite /Q mulmxBl mul1mx mulmxBl => /eqP; rewrite subr_eq0 => /eqP h.
  by rewrite /V h.
Qed.

Lemma adjV_direct : adj V = P *m adj U *m P.
Proof. by rewrite /V !adjM proj_herm mulmxA. Qed.

(* adjoint of invariance: adj V = P adj U *)
Lemma adjV : adj V = P *m adj U.
Proof. by rewrite -UP_eq adjM proj_herm. Qed.

Lemma adjV_V : adj V *m V = P.
Proof. by rewrite adjV -UP_eq -mulmxA (mulmxA (adj U)) unitary mul1mx proj_idem. Qed.

Lemma adjV_Q : adj V *m Q = 0.
Proof. by rewrite adjV_direct -mulmxA PQ mulmx0. Qed.
Lemma Q_V : Q *m V = 0.
Proof. by rewrite /V !mulmxA QP !mul0mx. Qed.
Lemma V_Q : V *m Q = 0.
Proof. by rewrite /V -mulmxA PQ mulmx0. Qed.
Lemma Q_adjV : Q *m adj V = 0.
Proof. by rewrite adjV_direct !mulmxA QP !mul0mx. Qed.

Lemma left_inv : adj (V + Q) *m (V + Q) = 1%:M.
Proof.
  rewrite adjD adjQ mulmxDl (mulmxDr (adj V) V Q) (mulmxDr Q V Q) adjV_V adjV_Q Q_V QQ.
  by rewrite addr0 add0r PQ1.
Qed.

Lemma right_inv : (V + Q) *m adj (V + Q) = 1%:M.
Proof. exact: mulmx1C left_inv. Qed.

Lemma V_adjV : V *m adj V = P.
Proof.
  move: right_inv; rewrite adjD adjQ mulmxDl (mulmxDr V (adj V) Q) (mulmxDr Q (adj V) Q) V_Q Q_adjV QQ addr0 add0r => h.
  have -> : V *m adj V = 1%:M - Q by rewrite -h addrK.
  by rewrite /Q opprB addrC subrK.
Qed.

Theorem quantum_chairs : P *m U *m Q = 0.
Proof.
  have h : adj V *m U *m Q = 0 by rewrite adjV -(mulmxA P) unitary mulmx1 PQ.
  by rewrite -V_adjV -mulmxA -mulmxA (mulmxA (adj V)) h mulmx0.
Qed.
End Quantum.
