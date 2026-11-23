module

public import MinCostFlow.HierPaths.BuildProgGameEffects
public import MinCostFlow.HierPaths.BuildProgZero

/-!
# Procedure entries for the batched game

The game procedures occupy a consecutive block of the enclosing program.
Only the router and core calls refer to entries outside this block.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

/-- The loop is at offset zero. The router and core indices are supplied by
the enclosing builder. -/
def buildGameProcs (b router core : ℕ) : List Stmt :=
  [buildGameLoopProc (b+1),
    buildGameStepProc (b+2) (b+3) (b+4),
    buildOneRoundProc (b+5) (b+11) (b+15),
    buildPreparedEndProc,
    buildGameAdvanceProc (b+13) (b+25) (b+26),
    buildGameScanProc (b+6),
    buildPrepareChildProc core (b+7),
    buildRequestProc (b+8) (b+9) (b+10),
    buildCutMaskProc,
    buildPadHalfProc,
    buildCutPackProc,
    buildRoundRouteProc (b+12) (b+14) (b+27),
    buildGameSelectProc,
    buildCopyProc,
    buildBatchProc (b+13),
    buildFinishBatchProc (b+16),
    buildApplyBatchProc (b+17),
    buildApplyRowProc (b+18) (b+19) (b+21),
    buildMatchReadProc,
    buildGameAppendProc (b+20),
    buildLocalEndsProc,
    buildWalkRowProc (b+22),
    buildStoreWalkProc (b+23),
    pathProc (b+29) (b+24),
    buildEraseProc (b+30) (b+31) (b+32),
    buildSaveCoreProc,
    buildActiveCompactProc,
    buildFullRouteProc router (b+13) (b+27),
    zeroProc,
    vertsProc,
    posFillProc,
    jumpProc,
    posClearProc]

/-- The enclosing program contains each entry of the game procedure block. -/
theorem buildGameProcs_lookup {p : Program} {prior later : List Stmt}
    {router core : ℕ} (hp : p.procs = prior ++ buildGameProcs prior.length router core ++ later)
    (i : ℕ) (hi : i < 33) :
    p.procs[prior.length + i]? = (buildGameProcs prior.length router core)[i]? := by
  rw [hp, List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left]
  simpa [buildGameProcs] using hi

end MinCostFlow.HierPaths
