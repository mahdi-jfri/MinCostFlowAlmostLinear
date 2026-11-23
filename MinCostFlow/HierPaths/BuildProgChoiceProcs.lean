module

public import MinCostFlow.HierPaths.BuildProgChoiceLoop
public import MinCostFlow.HierPaths.BuildProgGameProcs

/-!
# The linked certified game loop

The same compact procedure table uses the independent-reply scan and
the router's exact output. This is the game loop used by the parent-level
builder.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

/-- Assemble the game loop from the core and router contracts and the verified
local procedures. -/
theorem buildGameChoiceProcs_meetsContract {w core router tailBudget stepBudget : ℕ}
    {p : Program} {prior later : List Stmt} {D : ChoiceLoopData}
    (hp : p.procs = prior ++ buildGameProcs prior.length router core ++ later)
    (hRouter : ProvidesRouter w D.base.K D.base.route D.base.routeCost D.base.routeSpace p router)
    (hCore : ProvidesCore w D.base.K D.base.M D.base.r D.base.coreCost D.base.coreSpace p core)
    (hPlayer : IsMatchingPlayer D.base.route D.base.routeCost)
    {β : ℝ} (hβ : 0 < β) (hExp : D.base.host.IsExpansionExpanderOn D.base.verts β)
    (hXw : D.base.verts.card < 2^w) :
    MeetsContract w p prior.length (buildChoiceLoopContract w tailBudget stepBudget D) := by
  let b := prior.length
  have hh (i : ℕ) (hi : i < 33) : p.procs[b+i]? =
        (buildGameProcs b router core)[i]? := buildGameProcs_lookup hp i hi
  have h0 : p.procs[b]? = some (buildGameLoopProc (b+1)) := by
    simpa [buildGameProcs] using hh 0 (by decide)
  refine buildChoiceLoopProc_meetsContract h0 ?_ hPlayer hβ hExp
  intro heap sts
  let B := D.round sts
  let A := D.atHeap heap
  have h1 := hh 1 (by decide)
  have h2 := hh 2 (by decide)
  have h3 := hh 3 (by decide)
  have h4 := hh 4 (by decide)
  have h5 := hh 5 (by decide)
  have h6 := hh 6 (by decide)
  have h7 := hh 7 (by decide)
  have h8 := hh 8 (by decide)
  have h9 := hh 9 (by decide)
  have h10 := hh 10 (by decide)
  have h11 := hh 11 (by decide)
  have h12 := hh 12 (by decide)
  have h13 := hh 13 (by decide)
  have h14 := hh 14 (by decide)
  have h15 := hh 15 (by decide)
  have h16 := hh 16 (by decide)
  have h17 := hh 17 (by decide)
  have h18 := hh 18 (by decide)
  have h19 := hh 19 (by decide)
  have h20 := hh 20 (by decide)
  have h21 := hh 21 (by decide)
  have h22 := hh 22 (by decide)
  have h23 := hh 23 (by decide)
  have h24 := hh 24 (by decide)
  have h25 := hh 25 (by decide)
  have h26 := hh 26 (by decide)
  have h27 := hh 27 (by decide)
  have h28 := hh 28 (by decide)
  have h29 := hh 29 (by decide)
  have h30 := hh 30 (by decide)
  have h31 := hh 31 (by decide)
  have h32 := hh 32 (by decide)
  simp only [buildGameProcs,List.getElem?_cons_succ,List.getElem?_cons_zero] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32
  refine buildStepChoiceProc_meetsContract h1 ?_
    (fun _ _ _ => buildPreparedEndProc_meetsContract h3)
    (fun _ _ _ => buildGameAdvanceProc_meetsContract h4 h13 h25 h26) hPlayer hβ hExp
  refine buildRoundChoiceProc_meetsContract h2 ?_ ?_ ?_ hPlayer hβ hExp
  · exact buildScanChoiceProc_meetsContract h5
      (fun _ => buildPrepareChoiceProc_meetsContract h6 hCore h7 h8 h9 h10)
  · intro _ _
    exact buildRoundRouteProc_meetsContract h11 h12 h14 h13 h27 hRouter hPlayer hβ hExp hXw
  · intro _ _ Ms emb
    apply buildFinishBatchProc_meetsContract h15
    refine buildApplyBatchProc_meetsContract h16 (fun i _ => ?_)
    refine buildApplyRowProc_meetsContract h17 h18 h19 h20 h21 (fun j _ => ?_)
    exact buildStoreWalkProc_meetsContract h22 (pathProc_meetsContract h23 h29 h24 h30 h31 h32)

end MinCostFlow.HierPaths
