module

public import MinCostFlow.Scaling.PositiveEdges
public import MinCostFlow.Scaling.Scatter

/-!
# Restoring removed edge slots with one scatter pass

The positive-capacity preprocessing for Appendix C of Chen et al.,
arXiv:2203.00671v2, retains original edge indices. To reconstruct a flow, clear
the original flow table and write each retained coordinate to its saved index.
This file proves that the explicit scatter loop agrees with the inverse-index
map, and counts at most five operations per original edge including clearing.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- Pair each retained edge's original index with its returned flow value. -/
def positiveFlowEntries (I : Circulation) {β : Type}
    (f : Fin I.positiveEdges.length → β) : List (Fin I.m × β) :=
  List.ofFn (fun e => (I.positiveIndex e, f e))

/-- The saved original indices are precisely the retained-edge list. -/
theorem positiveFlowEntries_keys (I : Circulation) {β : Type}
    (f : Fin I.positiveEdges.length → β) :
    (I.positiveFlowEntries f).map Prod.fst = I.positiveEdges := by
  simp only [positiveFlowEntries, List.map_ofFn]
  exact List.ofFn_get I.positiveEdges

/-- Reconstruct the original vector by clearing it and scattering retained values. -/
def scatterPositive (I : Circulation) {β : Type} [Zero β]
    (f : Fin I.positiveEdges.length → β) : Fin I.m → β :=
  Scatter.write (fun _ => 0) (I.positiveFlowEntries f)

/-- The efficient scatter loop agrees with the inverse-index description of
extension by zero, for real flow vectors. -/
theorem scatterPositive_eq_extendPositive (I : Circulation)
    (f : Fin I.positiveEdges.length → ℝ) : I.scatterPositive f = I.extendPositive f := by
  funext e
  have hn : ((I.positiveFlowEntries f).map Prod.fst).Nodup := by
    rw [positiveFlowEntries_keys]
    exact I.positiveEdges_nodup
  by_cases he : 0 < I.capacity e
  · rw [extendPositive, dite_eq_left he]
    apply Scatter.lookup _ _ hn
    apply List.mem_ofFn.mpr
    exact ⟨I.positiveSlot e he, by simp only [positiveIndex_positiveSlot]⟩
  · have hz : I.capacity e = 0 := by omega
    rw [I.extendPositive_zero f e hz]
    apply Scatter.unchanged
    intro entry hentry
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hentry
    intro hkey
    have hpos : 0 < I.capacity (I.positiveIndex k) :=
      (I.mem_positiveEdges_iff _).mp (List.getElem_mem k.isLt)
    exact he (hkey ▸ hpos)

/-- Scatter restoration preserves feasibility after removing zero-capacity slots. -/
theorem scatterPositive_feasible (I : Circulation)
    (f : Fin I.positiveEdges.length → ℝ) (hf : I.withoutZeroEdges.Feasible f) :
    I.Feasible (I.scatterPositive f) := by
  rw [scatterPositive_eq_extendPositive]
  exact I.extendPositive_feasible f hf

/-- Scatter restoration preserves exact optimality after zero slots are removed. -/
theorem scatterPositive_optimal (I : Circulation)
    (f : Fin I.positiveEdges.length → ℝ) (hf : I.withoutZeroEdges.Optimal f) :
    I.Optimal (I.scatterPositive f) := by
  rw [scatterPositive_eq_extendPositive]
  exact I.extendPositive_optimal f hf

/-- Execute scatter restoration with a counter including initialization of
all original edge coordinates to zero. -/
def scatterPositiveWithWork (I : Circulation) {β : Type} [Zero β]
    (f : Fin I.positiveEdges.length → β) : (Fin I.m → β) × ℕ :=
  let r := Scatter.withWork (fun _ => 0) (I.positiveFlowEntries f)
  (r.1, I.m + r.2)

/-- Work recording does not change the reconstructed vector. -/
theorem scatterPositiveWithWork_value (I : Circulation) {β : Type} [Zero β]
    (f : Fin I.positiveEdges.length → β) :
    (I.scatterPositiveWithWork f).1 = I.scatterPositive f :=
  Scatter.withWork_value _ _

/-- The reconstruction uses at most `5*m` counted operations. -/
theorem scatterPositiveWithWork_work (I : Circulation) {β : Type} [Zero β]
    (f : Fin I.positiveEdges.length → β) :
    (I.scatterPositiveWithWork f).2 ≤ 5 * I.m := by
  change I.m + (Scatter.withWork (fun _ => 0) (I.positiveFlowEntries f)).2 ≤ _
  rw [Scatter.withWork_work]
  have hl : (I.positiveFlowEntries f).length ≤ I.m := by
    simpa only [positiveFlowEntries, List.length_ofFn] using I.positiveEdges_length_le
  omega

/-- Integer scatter reconstruction commutes with casting to real flows. -/
theorem scatterPositive_cast (I : Circulation) (f : Fin I.positiveEdges.length → ℤ) :
    (fun e => ((I.scatterPositive f e : ℤ) : ℝ)) =
      I.scatterPositive (fun e => (f e : ℝ)) := by
  unfold scatterPositive
  rw [Scatter.map_write]
  simp only [positiveFlowEntries, List.map_ofFn, Int.cast_zero, Function.comp_def]

/-- Call a circulation solver on positive-capacity edges only and scatter its
integral result back to the original edge coordinates. -/
def solvePruned (solve : (J : Circulation) → Fin J.m → ℤ) (I : Circulation) :
    Fin I.m → ℤ := I.scatterPositive (solve I.withoutZeroEdges)

/-- Pruning requires no additional solver hypothesis: the original comparison
with feasible real circulations is preserved after the integer scatter loop. -/
theorem solvePruned_correct (solve : (J : Circulation) → Fin J.m → ℤ)
    (hsolve : ∀ J : Circulation, J.Optimal (fun e => (solve J e : ℝ)))
    (I : Circulation) : I.Optimal (fun e => (solvePruned solve I e : ℝ)) := by
  unfold solvePruned
  rw [scatterPositive_cast]
  exact I.scatterPositive_optimal _ (hsolve I.withoutZeroEdges)

end MinCostFlow.Scaling.Circulation
