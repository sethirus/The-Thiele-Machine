(** UniversalThieleLinks.v: the universal host and its guest are
    CertificationSystem instances, so the substrate-independent cost floor
    applies to both. *)

From Kernel Require Import UniversalCertificationCost.
Require Minimal.EarnedCore.
Require Minimal.UniversalThiele.
Module E := Minimal.EarnedCore.
Module U := Minimal.UniversalThiele.

(* The host, read through hcert || mrec. *)
Definition host_cs : CertificationSystem :=
  mk_cert_system U.hstate U.hinstr U.hexec U.hcost U.hread U.host_toll.

(* The host, read through the mirrored guest record alone. *)
Definition host_mirror_cs : CertificationSystem :=
  mk_cert_system U.hstate U.hinstr U.hexec U.hcost U.mrec U.host_mirror_toll.

(* The guest class: the small machine itself. *)
Definition guest_cs : CertificationSystem :=
  mk_cert_system E.state E.instr E.exec E.cost E.cert E.a2.

Lemma host_cs_run : forall tr h, cs_run host_cs tr h = U.hrun tr h.
Proof. induction tr; intros; simpl; auto. Qed.

Lemma host_cs_cost : forall tr, cs_total_cost host_cs tr = U.htotal_cost tr.
Proof. induction tr; simpl; auto. Qed.

(* Any host instruction sequence that raises the host's reading costs at
   least 1, whatever it runs. *)
Corollary host_nfi : forall tr h,
  U.hread h = false -> U.hread (U.hrun tr h) = true -> U.htotal_cost tr >= 1.
Proof.
  intros tr h H0 H1. rewrite <- host_cs_cost.
  apply (universal_nfi_any_substrate host_cs tr h H0).
  simpl. rewrite host_cs_run. exact H1.
Qed.

Print Assumptions host_nfi.
Print Assumptions host_cs.
Print Assumptions host_mirror_cs.
Print Assumptions guest_cs.
