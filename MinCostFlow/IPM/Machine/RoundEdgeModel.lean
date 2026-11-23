module

public import MinCostFlow.IPM.Machine.RoundCycleEdge
import Mathlib.Tactic

/-!
# The two directions of a rounding cycle

The direction bit expresses exactly the cost test in Kang and Payor's
Section 4. Naming its intermediate values lets the machine use the
same push and cleanup code in both directions.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open Rounding

/-- In the backward case the forest path runs from the edge tail. -/
def roundFrom (e : Edge) (backward : Bool) : ℕ :=
  if backward then e.tail else e.head

/-- The forest path runs opposite to the cycle traversal of the edge. -/
def roundTo (e : Edge) (backward : Bool) : ℕ :=
  if backward then e.head else e.tail

/-- The new edge's availability in the chosen direction. -/
def roundAvail (q : ℚ) (backward : Bool) : ℚ :=
  if backward then q-(⌊q⌋:ℚ) else (⌈q⌉:ℚ)-q

/-- The cycle cost test chooses the backward direction precisely
when the forward cost is positive. -/
def roundBackward (D : DynForest) {I : Instance} (s : D.State) (j : Fin I.m) : Bool :=
  decide (D.pathSum s (I.edge j).tail (I.edge j).head < (I.edge j).cost)

/-- The new edge's cycle increment for its chosen path. -/
def roundCycleDelta (D : DynForest) {I : Instance} (s : D.State) (j : Fin I.m)
    (q : ℚ) (backward : Bool) : ℚ :=
  let a := roundAvail q backward
  (D.pathMin s (roundFrom (I.edge j) backward) (roundTo (I.edge j) backward)).elim a
    (fun e => min a e.avail)

/-- The exact new flow when pushing the cycle in the chosen direction. -/
def roundCycleValue (D : DynForest) {I : Instance} (s : D.State) (j : Fin I.m)
    (q : ℚ) (backward : Bool) : ℚ :=
  let δ := roundCycleDelta D s j q backward
  if backward then q-δ else q+δ

/-- The witness checked by Link uses the original integer endpoints. -/
def roundingEdge (I : Instance) (j : Fin I.m) (original q : ℚ) : ForestEdge :=
  ⟨j.val,(I.edge j).tail,(I.edge j).head,(I.edge j).cost,q,(⌈original⌉:ℚ)-q,q-(⌊original⌋:ℚ)⟩

/-- Counts just before path cleanup in the connected branch. -/
def roundCycleCounts (c : RoundCounts) : RoundCounts :=
  { c with findRootOps := c.findRootOps+2, pathSumOps := c.pathSumOps+1,
           pathMinOps := c.pathMinOps+1, pathAddOps := c.pathAddOps+1, otherSteps := c.otherSteps+9 }

/-- The numbers computed by the connected branch before path cleanup. -/
def roundCycleRats (D : DynForest) {I : Instance} (s : D.State) (j : Fin I.m)
    (q : ℚ) (backward : Bool) (old : List ℚ) : List ℚ :=
  let tail := (q-(⌊q⌋:ℚ)) :: ((⌈q⌉:ℚ)-q) :: old
  let hit := D.pathMin s (roundFrom (I.edge j) backward) (roundTo (I.edge j) backward)
  roundCycleValue D s j q backward :: roundCycleDelta D s j q backward ::
    hit.elim tail (fun e => e.avail::tail)

/-- The path-cleanup model result in the connected branch. -/
def roundCycleClean (D : DynForest) (I : Instance) (q : ℚ)
    (st : RoundState D I) (j : Fin I.m) (backward : Bool) :
    D.State × (Fin I.m → ℚ) × RoundCounts × List ℚ :=
  let u := roundFrom (I.edge j) backward
  let v := roundTo (I.edge j) backward
  let δ := roundCycleDelta D st.df j q backward
  let val := roundCycleValue D st.df j q backward
  removeZeroEdges D I (D.pathAdd st.df u v δ) (fun k => if k=j then val else st.flowArr k)
    (roundCycleCounts st.counts) (roundCycleRats D st.df j q backward st.computedRats) u v (I.m+1)

/-- The model takes the connected cycle branch with the exact
machine-selected direction. Only the forest and working flow are
needed in the machine representation. -/
theorem roundEdgeStep_connected (D : DynForest) (I : Instance) (f : Fin I.m → ℚ)
    (st : RoundState D I) (j : Fin I.m) (hFrac : isIntRat (f j)=false)
    (hRoots : D.findRoot st.df (I.edge j).tail=D.findRoot st.df (I.edge j).head) :
    let backward := roundBackward D st.df j
    let q := roundCycleValue D st.df j (f j) backward
    let clean := roundCycleClean D I (f j) st j backward
    let out := roundEdgeStep D I f st j
    out.df=(if isIntRat q then clean.1 else D.link clean.1 (roundingEdge I j (f j) q)) ∧
      out.flowArr=clean.2.1 ∧ out.counts.cutOps=clean.2.2.1.cutOps := by
  dsimp only
  by_cases hc : D.pathSum st.df (I.edge j).tail (I.edge j).head < (I.edge j).cost
  · have hh : ¬(I.edge j).cost-D.pathSum st.df (I.edge j).tail (I.edge j).head≤0 := by omega
    simp only [roundEdgeStep,hFrac,Bool.false_eq_true,ite_false,hRoots,ne_eq,not_true_eq_false,
      hh,roundBackward,hc,decide_true,roundCycleClean,roundFrom,roundTo,roundCycleDelta,roundAvail,
      roundCycleValue,roundCycleCounts,roundCycleRats,roundingEdge]
    cases hHit : D.pathMin st.df (I.edge j).tail (I.edge j).head with
    | none => simp only; split <;> simp_all
    | some hit => simp only; split <;> simp_all
  · have hh : (I.edge j).cost-D.pathSum st.df (I.edge j).tail (I.edge j).head≤0 := by omega
    simp only [roundEdgeStep,hFrac,Bool.false_eq_true,ite_false,hRoots,ne_eq,not_true_eq_false,
      hh,roundBackward,hc,decide_false,roundCycleClean,roundFrom,roundTo,roundCycleDelta,roundAvail,
      roundCycleValue,roundCycleCounts,roundCycleRats,roundingEdge,ite_true]
    cases hHit : D.pathMin st.df (I.edge j).head (I.edge j).tail with
    | none => simp only [Option.elim_none]; split <;> simp_all
    | some hit => simp only [Option.elim_some]; split <;> simp_all

/-- In the disconnected branch, the model simply links the new
fractional edge and leaves the flow table unchanged. -/
theorem roundEdgeStep_disconnected (D : DynForest) (I : Instance) (f : Fin I.m → ℚ)
    (st : RoundState D I) (j : Fin I.m) (hFrac : isIntRat (f j)=false)
    (hRoots : D.findRoot st.df (I.edge j).tail≠D.findRoot st.df (I.edge j).head) :
    let out := roundEdgeStep D I f st j
    out.df=D.link st.df (roundingEdge I j (f j) (f j)) ∧ out.flowArr=st.flowArr ∧
      out.counts.cutOps=st.counts.cutOps := by
  simp [roundEdgeStep,hFrac,hRoots,roundingEdge]

end MinCostFlow.IPM.Machine
