module

public import MinCostFlow.IPM.DataStructureTest
public import MinCostFlow.IPM.GuessSearch
import MinCostFlow.IPM.GuessInitial
import MinCostFlow.IPM.GuessBounds
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Searching for the target with the dynamic data structure

The bounded guarded target test supplies the comparison needed by the
binary search proposed in Section 4 of Chen et al., arXiv:2203.00671v2
(page 24). Integrality makes acceptance equivalent to the integer target
being at least the optimum. Bisection therefore finds the optimal integer
target in at most `clog 2 (2B+1)` tests. One final test returns a feasible
flow within one quarter of optimal. The only algorithmic parameter is a
data structure meeting Definition 4.5 (page 14 of arXiv:2309.16629v1).
-/

noncomputable section
@[expose] public section
namespace MinCostFlow.IPM

/-- The actual data structure target test compares an integer guess with
the optimal integer value. Its soundness uses feasibility, not hidden
stability of a wrong guess. Its completeness uses the proved upper-guess
hidden witness and epoch progress. -/
theorem dataStructureGuessTest_integer_iff (I : Instance) (U κ : ℝ) (F z : ℤ)
    (A : MinRatioDataStructure) (base fstar : Fin I.m → ℝ)
    (hI : I.IsValid) (hm : 0 < I.m) (hU : 1 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hk : 0 < κ) (hk' : κ ≤ 1)
    (hs : I.IsMinCostFlow fstar) (hz : I.cost fstar = z)
    (hA : MinRatioSpec A κ (normalizedIpmAlpha I) (ipmPsi I U) (ipmDetectThreshold I U κ))
    (hbase : StrictlyInside I base) (hroute : I.Routes base)
    (hpot : 0 < residual I F base → potential I (alpha I U) F base ≤ 200*I.m*Real.log (I.m*U)) :
    (dataStructureGuessTest I U F κ A base).isSome = true ↔ z ≤ F := by
  constructor
  · intro hh
    obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp hh
    have hout := boundedTargetRun_sound I U F κ A (ipmEpochLimit I U κ) base g hI hm
      (le_trans (by norm_num) hU) hsize hnums hk hk' hA hbase hroute hg
    have hopt := hs.2 g hout.1
    rw [hz] at hopt
    have hgap : (z : ℝ) < F+1 := by linarith only [hopt, hout.2]
    have hi : z < F+1 := by exact_mod_cast hgap
    exact Int.lt_add_one_iff.mp hi
  · intro hh
    apply dataStructureGuessTest_complete I U F κ A base fstar hI hm hU hsize hnums hk hk'
      hs.1 _ hA hbase hroute hpot
    rw [hz]
    exact_mod_cast hh

/-- Binary search using actual bounded data structure runs, together with
an upper bound on the number of target runs invoked, including the final
run at the selected integer value. -/
def dataStructureCostSearch (I : Instance) (U κ : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (B : ℕ) : Option (Fin I.m → ℝ) × ℕ :=
  let result := bisectCost (fun F => (dataStructureGuessTest I U F κ A base).isSome)
    (-(B : ℤ)) (2*B) (Nat.clog 2 (2*B+1))
  (dataStructureGuessTest I U result.1 κ A base, result.2.length+1)

/-- The actual-data-structure cost search returns a feasible flow within
one quarter of optimal and uses at most `clog 2 (2B+1)+1` target runs.
Every target run is capped at `ipmEpochLimit` guarded epochs. -/
theorem dataStructureCostSearch_correct (I : Instance) (U κ : ℝ) (A : MinRatioDataStructure)
    (base fstar : Fin I.m → ℝ) (z : ℤ) (B : ℕ)
    (hI : I.IsValid) (hm : 0 < I.m) (hU : 1 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hk : 0 < κ) (hk' : κ ≤ 1)
    (hs : I.IsMinCostFlow fstar) (hz : I.cost fstar = z)
    (hzlo : -(B : ℤ) ≤ z) (hzhi : z ≤ B)
    (hA : MinRatioSpec A κ (normalizedIpmAlpha I) (ipmPsi I U) (ipmDetectThreshold I U κ))
    (hbase : StrictlyInside I base) (hroute : I.Routes base)
    (hpot : ∀ F : ℤ, -(B : ℤ) ≤ F → F ≤ B → 0 < residual I F base →
      potential I (alpha I U) F base ≤ 200*I.m*Real.log (I.m*U)) :
    ∃ g, (dataStructureCostSearch I U κ A base B).1 = some g ∧ I.IsFeasible g ∧
      I.cost g ≤ I.cost fstar+1/4 ∧
      (dataStructureCostSearch I U κ A base B).2 ≤ Nat.clog 2 (2*B+1)+1 := by
  let test : ℤ → Bool := fun F => (dataStructureGuessTest I U F κ A base).isSome
  have htest : ∀ F, -(B : ℤ) ≤ F → F ≤ B → (test F = true ↔ z ≤ F) := by
    intro F hFl hFh
    exact dataStructureGuessTest_integer_iff I U κ F z A base fstar hI hm hU hsize hnums
      hk hk' hs hz hA hbase hroute (hpot F hFl hFh)
  have hspan : 2*B < 2^(Nat.clog 2 (2*B+1)) := by
    have hh := Nat.le_pow_clog (by decide : 1 < 2) (2*B+1)
    omega
  have hb := bisectCost_correct test z (-(B : ℤ)) (2*B) (Nat.clog 2 (2*B+1))
    hzlo (by omega) hspan (by intro F hFl hFh; exact htest F hFl (by omega))
  have hsome := (htest z hzlo hzhi).mpr le_rfl
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp hsome
  have hsnd := boundedTargetRun_sound I U z κ A (ipmEpochLimit I U κ) base g hI hm
    (le_trans (by norm_num) hU) hsize hnums hk hk' hA hbase hroute hg
  refine ⟨g, ?_, hsnd.1, ?_, Nat.succ_le_succ hb.2⟩
  · change dataStructureGuessTest I U (bisectCost test (-(B : ℤ)) (2*B) (Nat.clog 2 (2*B+1))).1 κ A base = _
    rw [hb.1]
    exact hg
  · rw [hz]
    exact hsnd.2

/-- The actual-data-structure search needs no supplied optimum or
comparison flow. A half-unit-slack feasible initial flow and integral
numeric bound determine its entire search interval. -/
theorem dataStructure_halfSlack_search (I : Instance) (U : ℕ) (κ : ℝ)
    (A : MinRatioDataStructure) (base : Fin I.m → ℝ)
    (hI : I.IsValid) (hm : 0 < I.m) (hU : 2 ≤ U) (hnums : NumbersBounded I (U : ℝ))
    (hk : 0 < κ) (hk' : κ ≤ 1)
    (hA : MinRatioSpec A κ (normalizedIpmAlpha I) (ipmPsi I (U : ℝ)) (ipmDetectThreshold I (U : ℝ) κ))
    (hf : I.IsFeasible base)
    (hslack : ∀ e, (1/2 : ℝ) ≤ base e-(I.edge e).lower ∧ (1/2 : ℝ) ≤ (I.edge e).upper-base e) :
    ∃ g, (dataStructureCostSearch I (U : ℝ) κ A base (I.m*U^2)).1 = some g ∧ I.IsFeasible g ∧
      (∀ fstar, I.IsMinCostFlow fstar → I.cost g ≤ I.cost fstar+1/4) ∧
      (dataStructureCostSearch I (U : ℝ) κ A base (I.m*U^2)).2 ≤
        Nat.clog 2 (2*(I.m*U^2)+1)+1 := by
  have hUR : (2 : ℝ) ≤ U := by exact_mod_cast hU
  have hmR : (1 : ℝ) ≤ I.m := Nat.one_le_cast.mpr hm
  have hsize : (2 : ℝ) ≤ I.m*(U : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hmR (le_trans (by norm_num) hUR)
    nlinarith only [hh, hUR]
  have hstrict : StrictlyInside I base := by
    intro e
    constructor <;> linarith only [(hslack e).1, (hslack e).2]
  obtain ⟨fstar, hs, hint⟩ := exists_integral_minCostFlow I hI ⟨base, hf⟩
  obtain ⟨z, hz⟩ := integral_cost I fstar hint
  have hbound := feasible_cost_abs_le I (U : ℝ) (Nat.cast_nonneg _) hnums fstar hs.1
  rw [hz] at hbound
  have hzlo : -((I.m*U^2 : ℕ) : ℤ) ≤ z := by exact_mod_cast (abs_le.mp hbound).1
  have hzhi : z ≤ ((I.m*U^2 : ℕ) : ℤ) := by exact_mod_cast (abs_le.mp hbound).2
  have hinit : ∀ F : ℤ, -((I.m*U^2 : ℕ) : ℤ) ≤ F → F ≤ ((I.m*U^2 : ℕ) : ℤ) →
      0 < residual I F base → potential I (alpha I (U : ℝ)) F base ≤ 200*I.m*Real.log (I.m*(U : ℝ)) := by
    intro F hFl _ hr
    apply guess_initial_potential I (U : ℝ) F base hm (le_trans (by norm_num) hUR) hsize
      hnums hf hslack _ hr
    exact_mod_cast hFl
  obtain ⟨g, hg, hgf, hgc, hcount⟩ := dataStructureCostSearch_correct I (U : ℝ) κ A
    base fstar z (I.m*U^2) hI hm (le_trans (by norm_num) hUR) hsize hnums hk hk'
    hs hz hzlo hzhi hA hstrict hf.1 hinit
  exact ⟨g, hg, hgf, fun f' hf' => hgc.trans (add_le_add_left (hs.2 f' hf'.1) (1/4 : ℝ)), hcount⟩

end MinCostFlow.IPM
