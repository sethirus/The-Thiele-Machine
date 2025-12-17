From Coq Require Import Arith.PeanoNat Lia.

From NoFI Require Import NoFreeInsight_Interface.
From NoFI Require Import NoFreeInsight_Theorem.
From NoFI Require Import Instance_Kernel.

(** C2 (Coq): prediction-pipeline No-Free-Insight instantiation.

    This file is intentionally **not CHSH-specific**.

    We treat “stronger predictive power / stronger evaluation” as a *strengthened claim*
    in the abstract NoFI interface.

    The only thing the kernel model exposes to the observer is the certification CSR
    (via [observe]), and the only semantic “structure addition” event is a runtime
    transition of the certification CSR from 0 -> nonzero during execution.

    Therefore:
      - any run that ends by certifying a strictly stronger claim
      - must contain a structure-addition event.

    This is the Coq half of Deliverable C2; the runtime half is enforced by a
    receipt-defined verifier in Python tests.
*)

Module PredictionPipelineNoFI.
  Module K := Instance_Kernel.KernelNoFI.
  Module Thm := Instance_Kernel.KernelNoFI_Theorem.

  (** A family of “prediction claims” indexed by a strength threshold.

      Intuition: higher thresholds represent stronger asserted improvements.
      We do *not* interpret the threshold numerically here; we only rely on
      the strict strengthening relation and the kernel’s evidence channel.
  *)
  Definition prediction_claim (strength : K.Strength) : K.S -> Prop :=
    fun s => K.certifies s strength.

  Lemma strengthening_example :
    K.strictly_stronger 2 1.
  Proof.
    unfold K.strictly_stronger. lia.
  Qed.

  (** Core C2 theorem (specialized): strengthening implies structure addition. *)
  Theorem strengthened_prediction_requires_structure_addition :
    forall tr s0 s1,
      K.clean_start s0 ->
      K.run tr s0 = Some s1 ->
      K.certifies s1 2 ->
      K.structure_event tr s0.
  Proof.
    intros tr s0 s1 Hclean Hrun Hcert.
    eapply Thm.no_free_insight with (strength := 2) (weak := 1); eauto.
    - apply strengthening_example.
  Qed.
End PredictionPipelineNoFI.
