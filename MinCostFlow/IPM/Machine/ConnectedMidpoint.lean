module

public import MinCostFlow.IPM.Machine.ConnectedPairOrder
public import MinCostFlow.IPM.Machine.InitialFlow
import MinCostFlow.IPM.InitialDomain
import Mathlib.Tactic

/-!
# Loading the connected midpoint

Each added hub edge has upper capacity two, so the same capacity
loader used in Lemma 4.12 writes one on every added edge.
-/

public section
namespace MinCostFlow.IPM.Machine
open Scaling WordRAM

/-- The connected midpoint equals half the corresponding capacity word. -/
theorem connectedInitialFlow_half_encoded (J : Circulation)
    (hp : ∀ e, 1 ≤ J.capacity e) (K : ℤ) (e : Fin (connectedInitialInstance J.toInstance K).m) :
    ((((connectedInitialInstance J.toInstance K).edge e).upper.toNat : ℕ) : ℝ)/2 =
      connectedInitialFlow J.toInstance K e := by
  have hnonneg := ((connectedInitialInstance_zeroLower J hp K).1 e).2
  have hcast : ((((connectedInitialInstance J.toInstance K).edge e).upper.toNat : ℕ) : ℝ) =
      (((connectedInitialInstance J.toInstance K).edge e).upper : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnonneg
  rw [hcast, show (connectedInitialInstance J.toInstance K).edge e = _ from instanceOfArrays_edge _ _ e]
  unfold connectedInitialFlow flowOfArray
  generalize arrayIndex (connectedInitialEdgeArray J.toInstance K) (initialDemands J.toInstance) e = i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [connectedInitialEdgeArray, Fin.addCases_left]
    let k : Fin (initialInstance J.toInstance K).m :=
      (arrayIndex (initialEdgeArray J.toInstance K) (initialDemands J.toInstance)).symm j
    have h := initialFlow_half_upper J K k
    change flowOfArray (initialEdgeArray J.toInstance K) (initialDemands J.toInstance)
      (initialArrayFlow J.toInstance) k = _ at h
    rw [show (initialInstance J.toInstance K).edge k = _ from instanceOfArrays_edge _ _ k] at h
    simpa only [flowOfArray, k, Equiv.apply_symm_apply] using h.symm
  · simp only [connectedInitialEdgeArray, Fin.addCases_right]
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) j <;>
      simp only [Fin.addCases_left, Fin.addCases_right, starEdge_upper] <;> norm_num

/-- The existing loader emits the connected instance's exact fixed-point
midpoint once the graph has been encoded. -/
theorem connectedMidpoint_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0 < h) (hw : 2*h+2 ≤ w) (hconst : 5 < 2^w)
    (hprog : p.HasAt b (initialFlowModule b h)) (J : Circulation) (hm : 0 < J.m)
    (hp : ∀ e, 1 ≤ J.capacity e) (K : ℤ) :
    MeetsContract w p b (midpointFlowContract w h (connectedInitialInstance J.toInstance K)
      (connectedInitialFlow J.toInstance K)) :=
  midpointFlow_meetsContract hh hw hconst hprog _
    (connectedInitialInstance_valid J.toInstance K J.toInstance_valid)
    (hm.trans_le (connectedInitial_circulation_m_ge J hp K)) _
    (connectedInitialFlow_half_encoded J hp K)

end MinCostFlow.IPM.Machine
