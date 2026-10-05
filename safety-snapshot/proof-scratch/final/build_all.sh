#!/bin/bash
# Full build of the final composition, in dependency order.
cd "$(dirname "$0")"
bash build.sh EarnedCore.v EarnedGeneric.v ThieleComplete.v EarnedPriced.v PricedComplete.v Presented.v \
  vend/MinskyMachines/MMenv/env.v vend/MinskyMachines/MMenv/mme_defs.v vend/MinskyMachines/MMenv/mme_utils.v \
  vend/MuRec/MuRec.v vend/MuRec/Util/recalg.v vend/MuRec/Util/ra_mm_env.v \
  CompilerCodes.v CompilerChecker.v CompilerInstrument.v CompilerLifts.v CompilerIcomp.v CompilerRaBridge.v \
  Presentation.v CompilerGuest.v CompilerGuestRun.v \
  EarnedMultiPriced.v UniversalPCodes.v UniversalPBridge.v UniversalPBlocks.v UniversalPLayout.v \
  UniversalPPhases.v UniversalPSim.v UniversalPRun.v PresentedUniversal.v PresentedDemo.v
