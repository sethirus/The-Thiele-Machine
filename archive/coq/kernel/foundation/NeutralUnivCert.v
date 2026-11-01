(** NeutralUnivCert.v: the certified universal machine is the neutral universal
    machine plus a certification layer, in the way Thiele-complete is
    neutral-complete plus certification (NeutralComplete.tc_iff_nc_plus_certification).

      cu_with           the certified notion with its witnesses explicit: the
                        host Thiele-complete through an interface I whose base
                        moves are exactly the counter moves, the universal
                        loads clean for I, (N1)-(N5) as in the neutral notion,
                        and (c) earned-and-tied: whenever the host's record is
                        up, its own trace holds an earned chain whose claim,
                        at the state where it was checked, is tied to the
                        guest by a relation [tie] given with the class;
      cu_iff_nu_plus_certification
                        cu_with I  <->  nu_with (neutralize I)
                                        /\ clean base loads /\ earned record
                                        /\ non-vacuity of a claim
                                        /\ clean universal loads /\ (c);
      earned_part_free  in cu_with the "earned" half of (c) is already a
                        consequence of Thiele-completeness and clean loads:
                        what (c) adds is only the tie to the guest.        *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Kernel.UMachDef.
Require Import Kernel.NeutralUnivBase.
Require Import Kernel.NeutralUnivDef.
Require Import Minimal.ThieleComplete.
Require Import Minimal.NeutralComplete.

Section Cert.
Variable C : gclass.
Variable H : host.
Variable Obs : gi C -> Type.
Variable obs : forall i, gS C i -> Obs i.

Fixpoint htrace (P : hP H) (h : hS H) (n : nat) : list (hI H) :=
  match n with
  | 0 => []
  | S n' => match hnext H P h with None => [] | Some m => m :: htrace P (hstep H h m) n' end
  end.

Lemma hr_trace : forall P n h, hr P h n = run (hmach H) (htrace P h n) h.
Proof.
  intros P n. induction n as [| n IH]; intros h; [reflexivity |].
  simpl. destruct (hnext H P h); simpl; [apply IH | reflexivity].
Qed.

(* ----------------------------------------------------------------- *)
(* The neutral notion with explicit witnesses.                        *)
(* ----------------------------------------------------------------- *)

Definition nu_with (J : neutral_interface (hmach H)) (K : nat) (P : hP H) (R : reg_host H)
  (raise : nat -> bool) (tpl : (nat -> nat) -> hS H) (code : gi C -> nat -> nat)
  (dec : forall i, (nat -> nat) -> Obs i) : Prop :=
  (neutral_complete_with J /\ forall m, ni_isbase J m = is_counter (b_kind R m)) /\
  line_raise H R P raise /\ clean_template H R tpl /\
  forall i, halt_clause C H Obs obs K P (tpl (code i)) i (fun h => dec i (b_reg R h)) /\
    exists f, in_order C H Obs obs K P (tpl (code i)) i (fun h => dec i (b_reg R h)) f.

Theorem nu_with_iff : forall K, neutral_universal C H Obs obs K <->
  exists J P R raise tpl code dec, nu_with J K P R raise tpl code dec.
Proof.
  intros K. split.
  - intros (P & R & ra & tpl & code & dec & [J [HJ Hk]] & H3 & H5 & Hall).
    exists J, P, R, ra, tpl, code, dec. split; [auto |]. auto.
  - intros (J & P & R & ra & tpl & code & dec & [HJ Hk] & H3 & H5 & Hall).
    exists P, R, ra, tpl, code, dec. split; [exists J; auto |]. auto.
Qed.

(* ----------------------------------------------------------------- *)
(* The certified notion.                                              *)
(* ----------------------------------------------------------------- *)

(* An earned chain with its claim and its checking prefix exposed. *)
Definition chain_at (I : thiele_interface (hmach H)) (c : ti_claim I) (s0 : hS H)
  (tr pre : list (hI H)) : Prop :=
  exists chk mid1 cmt mid2 crt post,
    tr = pre ++ chk :: mid1 ++ cmt :: mid2 ++ crt :: post /\
    ti_kind I chk = KCheck c /\ ti_kind I cmt = KCommit c /\ ti_kind I crt = KCertify /\
    ti_check I (run (hmach H) pre s0) c = true /\
    (forall t1 t2, mid1 = t1 ++ t2 ->
       ti_same I c (run (hmach H) pre s0) (run (hmach H) (pre ++ chk :: t1) s0)) /\
    m_record (hmach H) (run (hmach H) (pre ++ chk :: mid1 ++ cmt :: mid2) s0) = false /\
    m_record (hmach H) (run (hmach H) (pre ++ chk :: mid1 ++ cmt :: mid2 ++ [crt]) s0) = true.

Lemma chain_at_iff : forall I s0 tr,
  earned_chain I s0 tr <-> exists c pre, chain_at I c s0 tr pre.
Proof.
  intros I s0 tr. split.
  - intros (pre & c & chk & mid1 & cmt & mid2 & crt & post & X).
    exists c, pre, chk, mid1, cmt, mid2, crt, post. exact X.
  - intros (c & pre & chk & mid1 & cmt & mid2 & crt & post & X).
    exists pre, c, chk, mid1, cmt, mid2, crt, post. exact X.
Qed.

(* (c) earned and tied. *)
Definition earned_tied (I : thiele_interface (hmach H)) (tie : forall i, ti_claim I -> hS H -> Prop)
  (P : hP H) (tpl : (nat -> nat) -> hS H) (code : gi C -> nat -> nat) : Prop :=
  forall i n, hflag H (hr P (tpl (code i)) n) = true ->
    exists c pre, chain_at I c (tpl (code i)) (htrace P (tpl (code i)) n) pre /\
                  tie i c (run (hmach H) pre (tpl (code i))).

Definition cu_with (I : thiele_interface (hmach H)) (tie : forall i, ti_claim I -> hS H -> Prop)
  (K : nat) (P : hP H) (R : reg_host H) (raise : nat -> bool) (tpl : (nat -> nat) -> hS H)
  (code : gi C -> nat -> nat) (dec : forall i, (nat -> nat) -> Obs i) : Prop :=
  (thiele_complete_with I /\ forall m, kind_is_base (ti_kind I m) = is_counter (b_kind R m)) /\
  (forall rho, ti_clean I (tpl rho)) /\
  line_raise H R P raise /\ clean_template H R tpl /\
  (forall i, halt_clause C H Obs obs K P (tpl (code i)) i (fun h => dec i (b_reg R h)) /\
     exists f, in_order C H Obs obs K P (tpl (code i)) i (fun h => dec i (b_reg R h)) f) /\
  earned_tied I tie P tpl code.

Theorem cu_iff_nu_plus_certification : forall I tie K P R raise tpl code dec,
  cu_with I tie K P R raise tpl code dec <->
  nu_with (neutralize I) K P R raise tpl code dec /\
  ((forall a b, ti_clean I (load I a b)) /\ earned_record_clause I /\ non_vacuity_clause I) /\
  (forall rho, ti_clean I (tpl rho)) /\ earned_tied I tie P tpl code.
Proof.
  intros I tie K P R ra tpl code dec. split.
  - intros ((HT & Hk) & Hcl & H3 & H5 & Hall & Hc).
    destruct (proj1 (tc_iff_nc_plus_certification (hmach H) I) HT) as (HN & Hb & He & Hv).
    split; [| split; [auto | auto]].
    split; [split; [exact HN | intros m; exact (Hk m)] |]. auto.
  - intros (((HN & Hk) & H3 & H5 & Hall) & (Hb & He & Hv) & Hcl & Hc).
    split; [split; [apply (proj2 (tc_iff_nc_plus_certification (hmach H) I)); auto | exact Hk] |].
    auto.
Qed.

(* The "earned" half of (c) already holds once the host is Thiele-complete and
   the universal loads are clean. *)
Theorem earned_part_free : forall (I : thiele_interface (hmach H)) P tpl (code : gi C -> nat -> nat),
  thiele_complete_with I -> (forall rho, ti_clean I (tpl rho)) ->
  forall i n, hflag H (hr P (tpl (code i)) n) = true ->
    exists c pre, chain_at I c (tpl (code i)) (htrace P (tpl (code i)) n) pre.
Proof.
  intros I P tpl code [_ [[_ [Hch _]] _]] Hcl i n Hup.
  apply chain_at_iff. apply Hch; [apply Hcl |]. rewrite <- hr_trace. exact Hup.
Qed.

End Cert.

Print Assumptions nu_with_iff.
Print Assumptions cu_iff_nu_plus_certification.
Print Assumptions earned_part_free.
