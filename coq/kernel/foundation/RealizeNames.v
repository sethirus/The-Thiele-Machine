(** RealizeNames.v: short names for the files the realisation refers to.

    Coq's monolithic extraction refuses any constant that lives in a file
    containing a module alias, so the aliases are kept out of Realize.v and
    RealizePriced.v (which define the extracted constants) and collected
    here, in a file from which nothing is extracted.

    Dependencies: the files named below. No axioms, no Admitted.          *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this
   file only names modules. *)

Require Minimal.EarnedCore Minimal.EarnedGeneric Minimal.EarnedPriced
  Minimal.EarnedMulti Minimal.EarnedMultiPriced Minimal.UniversalCodes.
Require Kernel.CompilerCodes Kernel.CompilerChecker Kernel.UniversalLayout
  Kernel.UniversalSim Kernel.UniversalPCodes Kernel.UniversalPLayout
  Kernel.UniversalPSim.

Module E := Minimal.EarnedCore.
Module G := Minimal.EarnedGeneric.
Module PG := Minimal.EarnedPriced.
Module M := Minimal.EarnedMulti.
Module PM := Minimal.EarnedMultiPriced.
Module UC := Minimal.UniversalCodes.
Module UL := Kernel.UniversalLayout.
Module US := Kernel.UniversalSim.
Module UPC := Kernel.UniversalPCodes.
Module UPL := Kernel.UniversalPLayout.
Module UPS := Kernel.UniversalPSim.
Module CK := Kernel.CompilerChecker.
Module CC := Kernel.CompilerCodes.
