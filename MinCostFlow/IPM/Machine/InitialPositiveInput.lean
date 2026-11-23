module

public import MinCostFlow.IPM.InitialConstruction
public import MinCostFlow.Scaling.CirculationInstance
import Mathlib.Data.Finset.Sort

/-!
# Retained edges on the bounded circulation input

The solver contract supplies strictly positive capacities and zero
lower capacities. Thus Lemma 4.12's fixed-edge deletion removes no
original edge. This file proves that its increasing `freeIndex` keeps
the original edge order and that its reduced demands remain zero.
These facts connect the machine's copied records to the existing
initialization construction, rather than a permuted variant.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine
open Scaling

/-- No fixed-capacity edge occurs in the bounded solver input. -/
theorem freeEdges_circulation (J : Circulation) (hp : ∀ e, 1 ≤ J.capacity e) :
    freeEdges J.toInstance = Finset.univ := by
  ext e
  simp only [freeEdges,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [Circulation.toInstance_edge]
  change (0 : ℤ) < (J.capacity (J.inputIndex e) : ℤ) ↔ True
  exact iff_true_intro (by exact_mod_cast hp (J.inputIndex e))

/-- The increasing enumeration of a full finite edge set preserves the
edge's natural-number index. -/
theorem freeIndex_val_of_univ (I : Instance) (hfree : freeEdges I = Finset.univ)
    (j : Fin (freeEdges I).card) : ((freeIndex I j).val : ℕ) = j.val := by
  change ((freeEdges I).orderEmbOfFin rfl j).val = j.val
  rw [Finset.orderEmbOfFin_apply]
  simp only [hfree,Fin.sort_univ]
  change ((List.finRange I.m)[j.val]'_).val = j.val
  rw [List.getElem_finRange]
  rfl

/-- Copying the solver's original edge array gives exactly the source's
retained edge array, including its order. -/
theorem freeEdgeArray_circulation (J : Circulation) (hp : ∀ e, 1 ≤ J.capacity e) :
    List.ofFn (freeEdgeArray J.toInstance) = J.toInstance.edges := by
  have hfree := freeEdges_circulation J hp
  have hcard : (freeEdges J.toInstance).card = J.m := by
    rw [hfree,Finset.card_univ,Fintype.card_fin,Circulation.toInstance_m]
  apply List.ext_getElem
  · simpa only [List.length_ofFn,Circulation.toInstance,List.length_ofFn] using hcard
  · intro i hi hj
    let j : Fin (freeEdges J.toInstance).card := ⟨i,by simpa using hi⟩
    have hval := freeIndex_val_of_univ J.toInstance hfree j
    rw [List.getElem_ofFn]
    change freeEdgeArray J.toInstance j = J.toInstance.edges[i]
    rw [freeEdgeArray,Circulation.toInstance_edge]
    change J.inputEdge (J.inputIndex (freeIndex J.toInstance j).val) =
      (List.ofFn J.inputEdge)[i]
    rw [List.getElem_ofFn]
    congr 1
    exact Fin.ext hval

/-- With no fixed edges and zero input demands, the demand reduction
subtracts no routing contribution. -/
theorem freeDemands_circulation (J : Circulation) (hp : ∀ e, 1 ≤ J.capacity e)
    (v : Fin J.n) : freeDemands J.toInstance v = 0 := by
  have hfree := freeEdges_circulation J hp
  simp [freeDemands,fixedFlow,hfree,Instance.d]

/-- Every vertex of the augmented instance still has zero demand. -/
theorem initialDemands_circulation (J : Circulation) (hp : ∀ e, 1 ≤ J.capacity e)
    (v : Fin (J.n+1)) : initialDemands J.toInstance v = 0 := by
  refine Fin.lastCases ?_ (fun u => ?_) v
  · rw [initialDemands,Fin.lastCases_last]
  · rw [initialDemands,Fin.lastCases_castSucc]
    exact freeDemands_circulation J hp u

end MinCostFlow.IPM.Machine
