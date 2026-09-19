# Actual scan-loop source review

Source review: NormalizationScanExecution.v against the actual scan map, prior interval lemmas, and NormalizationExecution's Step/Multistep lifting. No concrete mismatch was found. This is source review in the same environment, not external reproduction.

scan_registers carries the seven typed reads required by the actual phase-8 scan action. scan_prefix_state is a finite fold of the exact scan update maps, with an accumulated duplicate flag equal to the initial flag OR comparisons already visited. The execution theorem proves both an actual Multistep trace and the reads needed for the next step by induction; it does not assume that this computed state is executable.

The strict comparison phase covers lo through end-1. A separate actual scan firing at j=end keeps the accumulated flag, advances j to end+1, and selects phase9. This handles the terminal scan even when lo=end, so no empty-range case is omitted. Bounds lo<=end<=16 prevent the compared natural endpoints from wrapping; the terminal pointer can be17. The candidate i is read as a word and has no independent bound in this local theorem; the outer admitted-range invariant must supply its intended distinct-cell interpretation.

All scan firings leave the tables and registers outside duplicate/j/phase unchanged. The resulting duplicate is initial_dup OR scan_seen(lo,end-lo); the outer loop must establish false as the initial flag when it wants precisely suffix membership. The label list has exactly end-lo+1 copies of the actual scan label. This is the length of a constructed sequence of selected rule firings, not a bound on arbitrary scheduler clock cycles.

Remaining integration: establish scan_registers from start/emit, set lo=i+1 and initial_dup=false, feed the terminal duplicate and preserved prefix invariant to actual emit, and induct over remaining candidates. Then compose commit and connect the normalization suffix with dispatch, admission, reset/faults and the full observation contract. The new scan theorem does not by itself discharge those obligations.
