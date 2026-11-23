module

public import MinCostFlow.LinkCut.Path.Pull
public import MinCostFlow.LinkCut.Path.Id

/-!
# The payload steps of the path payload

`pathSteps` collects the five payload procedures of the path payload (`rev`, `act`, `pull`,
`isId`, `setId`) with their contracts, in the form the generic tree programs take
(`PayloadSteps`). It needs a program that holds the five bodies and the helper procedures they
call (block negation and addition, the detector maximum, the segment step, the zero test and
word copying), each meeting its contract.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Path

open WordRAM MinCostFlow.Num MinCostFlow.MinRatio MinCostFlow.LinkCut.Gen

/-- The payload steps of the path payload with numbers in `K` limbs of `h` bits. -/
def pathSteps {w h K : ℕ} {p : Program} (rev act pull isId setId negB addB seg isZ copy : ℕ)
    (hrev : p.procs[rev]? = some (pathRevBody negB))
    (hact : p.procs[act]? = some (pathActBody addB))
    (hpull : p.procs[pull]? = some (pathPullBody seg copy))
    (hisId : p.procs[isId]? = some (pathIsIdBody isZ))
    (hsetId : p.procs[setId]? = some (pathSetIdBody copy))
    (hneg : MeetsContract w p negB (negBlockContract w h K))
    (hadd : MeetsContract w p addB (addBlockContract w h K))
    (hseg : MeetsContract w p seg (segContract w h K))
    (hisZ : MeetsContract w p isZ (isZeroContract w h))
    (hcopy : MeetsContract w p copy (copyWordsContract w)) :
    PayloadSteps w p pathPayload (pathLayout h K) (pathOk h K) where
  rev := rev
  act := act
  pull := pull
  isId := isId
  setId := setId
  cost := pathCost K
  space := pathSpace K
  rev_ok := pathRev_meetsContract hrev hneg
  act_ok := pathAct_meetsContract hact hadd
  pull_ok := pathPull_meetsContract hpull hseg hcopy
  isId_ok := pathIsId_meetsContract hisId hisZ
  setId_ok := pathSetId_meetsContract hsetId hcopy

end MinCostFlow.LinkCut.Path
