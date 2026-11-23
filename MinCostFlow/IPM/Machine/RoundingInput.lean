module

public import MinCostFlow.IPM.Machine.ForestContract
public import MinCostFlow.IPM.Machine.TargetOffsetTestRun
public import MinCostFlow.Rounding.Lemma4_1
import MinCostFlow.IPM.RoundedRecovery
import MinCostFlow.IPM.Machine.PrecisionProducts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Exact rational input to Lemma 4.1

The search's stored numerators already describe a rational flow in
the same format as the forest. Reading them supplies the fixed-point
premise of the rounder, and the quarter-unit objective error makes
its integral result exactly optimal.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open Rounding

/-- Read the machine flow directly on the exact rational grid. -/
noncomputable def roundingInput {w : ℕ} (F : MinRatioFormat w) (I : Instance)
    (mem : ℕ → ℕ) (source : ℕ) (e : Fin I.m) : ℚ :=
  readRat mem (source+e.val*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision

/-- The actual rational and real readings agree coordinate by coordinate. -/
theorem roundingInput_real {w : ℕ} (F : MinRatioFormat w) (I : Instance)
    (mem : ℕ → ℕ) (source : ℕ) :
    (fun e => (roundingInput F I mem source e:ℝ))=epochVector F I mem source := by
  funext e
  simp only [roundingInput,readRat,epochVector,Num.fixVal,Rat.cast_div,Rat.cast_intCast,Rat.cast_pow,Rat.cast_ofNat]

/-- The numerator in the stored block witnesses fixed-point exactly. -/
theorem roundingInput_fixed {w : ℕ} (F : MinRatioFormat w) (I : Instance)
    (mem : ℕ → ℕ) (source : ℕ) (e : Fin I.m) :
    IsFixedPoint F.fmt.precision (roundingInput F I mem source e) :=
  ⟨Num.intVal mem (source+e.val*F.limbs) F.fmt.limbBits F.limbs,rfl⟩

/-- The chosen signed width covers any bounded rational on the
rounder's fixed-point grid. -/
theorem ratFits_chosen_precision (m U : ℕ) (q : ℚ)
    (hfixed : IsFixedPoint (ipmPrecision m U) q)
    (hmag : |(q:ℝ)|≤(2:ℝ)^(ipmRangeExponent m U)) :
    RatFits 4 (ipmLimbs m U) (ipmPrecision m U) q := by
  obtain ⟨z,hz⟩ := hfixed
  refine ⟨z,fits_chosen_scaled_bound m U ?_,hz⟩
  rw [hz] at hmag
  simpa only [Rat.cast_div,Rat.cast_intCast,Rat.cast_pow,Rat.cast_ofNat] using hmag

/-- The exact search result supplies all inputs of the mathematical
rounder in Lemma 4.1 (page 13). Its output is integral and exactly
optimal, with the model's linear count. -/
theorem roundingInput_optimal {w : ℕ} (F : MinRatioFormat w) (I : Instance)
    (D : DynForest) (hD : D.IsSpec) (hI : I.IsValid)
    (E heap out : ℕ) (mem final : ℕ → ℕ) (z : ℤ)
    (fstar : Fin I.m → ℝ) (hstar : I.IsMinCostFlow fstar) (hz : I.cost fstar=(z:ℝ))
    (hResult : TargetOffsetResult F I E heap out z z mem final) (hBit : final (out-1)=1) :
    let f := roundingInput F I final (final (out-2))
    let r := roundFlow D I f
    IsIntegral (fun e => (r.flowArr e:ℝ)) ∧ I.IsMinCostFlow (fun e => (r.flowArr e:ℝ)) ∧
      (D.toForest r.df).edges=[] ∧ r.counts.treeOps≤10*I.m ∧ r.counts.otherSteps≤19*I.m := by
  dsimp only
  let ptr := final (out-2)
  let f := roundingInput F I final ptr
  let r := roundFlow D I f
  obtain ⟨hf,hcost⟩ := hResult.2.2.2.2.2.2 hBit
  have hCast := roundingInput_real F I final ptr
  have hFeas : I.IsFeasible (fun e => (f e:ℝ)) := hCast.symm ▸ hf.2.1
  have h := roundFlow_correct hD hI hFeas F.fmt.precision (maxAbsFlow I f+1)
  obtain ⟨hEmpty,_,hInt,hF,hC,hTree,hOther,_⟩ := h
  rw [hCast] at hC
  have hClose : I.cost (fun e => (r.flowArr e:ℝ))≤I.cost fstar+1/2 := by
    rw [hz]
    linarith only [hC,hcost]
  have hOpt := integral_near_optimal_isMinCostFlow I hI (fun e => (r.flowArr e:ℝ)) hF hInt
    (fun g hg => by rw [(le_antisymm (hg.2 _ hstar.1) (hstar.2 _ hg.1))]; exact hClose)
  exact ⟨hInt,hOpt,hEmpty,hTree,hOther⟩

/-- The chosen signed width covers any bounded rational on the
rounder's fixed-point grid. -/
theorem ratFits_widened_precision (m U k : ℕ) (q : ℚ)
    (hfixed : IsFixedPoint (ipmQualityPrecision m U k) q)
    (hmag : |(q:ℝ)|≤(2:ℝ)^(ipmQualityRangeExponent m U k)) :
    RatFits 4 (ipmQualityLimbs m U k) (ipmQualityPrecision m U k) q := by
  obtain ⟨z,hz⟩ := hfixed
  refine ⟨z,fits_quality_scaled_bound m U k ?_,hz⟩
  rw [hz] at hmag
  simpa only [Rat.cast_div,Rat.cast_intCast,Rat.cast_pow,Rat.cast_ofNat] using hmag

end MinCostFlow.IPM.Machine
