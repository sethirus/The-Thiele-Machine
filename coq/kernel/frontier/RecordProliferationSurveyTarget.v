(** SCOPE NOTE: standalone proof scope. The survey composes standalone observer
    maps; their real-system correspondence is a prose modeling judgment.

    Target: twelve candidate events and a swapped winner. *)

From Coq Require Import List Bool Arith.PeanoNat.
Import ListNotations.
From Kernel Require Import PointerObservable PointerObservableReductions
  PointerObservableCounterexamples.

Definition twelve_candidate_measurements : Prop :=
  redundantly_proliferating PoS_eco PoS_selected_event /\
  ~ redundantly_proliferating PoS_eco PoS_rival /\
  redundantly_proliferating Gas_eco Gas_selected_event /\
  ~ redundantly_proliferating Gas_eco Gas_rival /\
  redundantly_proliferating TEE_eco TEE_selected_event /\
  ~ redundantly_proliferating TEE_eco TEE_rival /\
  redundantly_proliferating CT_eco CT_selected_event /\
  ~ redundantly_proliferating CT_eco CT_rival /\
  redundantly_proliferating PCC_eco PCC_selected_event /\
  ~ redundantly_proliferating PCC_eco PCC_rival /\
  ~ redundantly_proliferating SymmetricMAC.mac SymmetricMAC.mac_event /\
  redundantly_proliferating DigitalSignature.signature
    DigitalSignature.sig_event.

Record SwapState := { swap_first : bool; swap_second : bool }.

Definition swap_ecosystem : Ecosystem := {|
  eco_state := SwapState;
  eco_observers := 3;
  eco_fragment := fun _ s => swap_second s
|}.

Definition first_event (s : SwapState) : Prop := swap_first s = true.
Definition second_event (s : SwapState) : Prop := swap_second s = true.

Definition swapped_event_is_pointer : Prop :=
  unique_pointer_among swap_ecosystem second_event [first_event].
