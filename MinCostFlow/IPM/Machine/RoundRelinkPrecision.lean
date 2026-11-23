module

public import MinCostFlow.IPM.Machine.RoundRelinkModel
import MinCostFlow.IPM.Machine.PrecisionProducts
import Mathlib.Tactic

/-!
# Precision for a connected rounding edge

The loop invariant supplies exact dyadic forest payloads,
including the ones created by the cycle push. Both the corrected
coordinate and the new Link record then fit the chosen precision.
-/

public section
namespace MinCostFlow.IPM.Machine
open Rounding

/-- All signed-range checks for the connected branch follow from
the common precision and the model's unit-interval invariant. -/
theorem roundRepairRelink_numeric {D : DynForest} (hD : D.IsSpec) {I : Instance}
    {f : Fin I.m → ℚ} {M : ℚ} (U : ℕ) (hm : 0<I.m) (hU : 1≤U)
    (hn : NumbersBounded I (U:ℝ)) (hf : ∀ j,|(f j:ℝ)|≤U)
    (model : RoundState D I) (j : Fin I.m) (back : Bool)
    (hModel : LoopInv D I f (ipmPrecision I.m U) M j.val model)
    (hFP : ∀ j,IsFixedPoint (ipmPrecision I.m U) (f j))
    (hFrac : isIntRat (f j)=false)
    (hComp : (D.toForest model.df).SameComp (I.edge j).tail (I.edge j).head) :
    let L := ipmLimbs I.m U
    let P := ipmPrecision I.m U
    let clean := roundCycleClean D I (f j) model j back
    let q := roundCycleValue D model.df j (f j) back
    let δ := roundCycleDelta D model.df j (f j) back
    ForestFits D 4 L P model.df ∧
      ForestFits D 4 L P (D.pathAdd model.df (roundFrom (I.edge j) back) (roundTo (I.edge j) back) δ) ∧
      ForestFits D 4 L P clean.1 ∧ Num.Fits 4 L (I.edge j).cost ∧ RatFits 4 L P q ∧
      (isIntRat q=false → RatFits 4 L P (⌊q⌋:ℚ) ∧ RatFits 4 L P ((⌈q⌉:ℚ)-q) ∧
        RatFits 4 L P (q-(⌊q⌋:ℚ))) := by
  dsimp only
  have hM := hModel
  obtain ⟨_,_,hStrict,_,_,_,_,_,_,_,_,_,_,_,_,hBits,_,_⟩ := hM
  obtain ⟨_,hP,hLo,hHi,hPushed,hClean,_,_,_,_,_,_⟩ :=
    roundCycleClean_properties hD model j back hModel hFP hFrac hComp
  let x := roundCycleValue D model.df j (f j) back
  have hX : |(x:ℝ)|≤U := round_between_abs_le (hf j) hLo hHi
  have hBound := round_capacity_range I.m U hm hU
  have hC := (hn.2 j).2.2
  refine ⟨roundForest_fits U hm hU hn hf (fun e he => ⟨(hStrict e he).1.1,(hBits hFP).1 e he⟩),
    roundForest_fits U hm hU hn hf hPushed,
    roundForest_fits U hm hU hn hf (fun e he => ⟨(hClean e he).1,(hClean e he).2.1,
      (hClean e he).2.2.1,(hClean e he).2.2.2.1⟩),
    (fits_integer_at_chosen_precision I.m U (I.edge j).cost (by linarith only [hC,hBound])).1,
    ratFits_chosen_precision I.m U x hP (by linarith only [hX,hBound]),?_⟩
  intro hQ
  exact ⟨(round_availability_fits I.m U x hm hU hP hX hQ).1,
    (round_availability_fits I.m U x hm hU hP hX hQ).2.2,
    (round_availability_fits I.m U x hm hU hP hX hQ).2.1⟩

/-- All signed-range checks for the connected branch follow from
the common precision and the model's unit-interval invariant. -/
theorem roundRepairRelink_numeric_widened {D : DynForest} (hD : D.IsSpec) {I : Instance}
    {f : Fin I.m → ℚ} {M : ℚ} (U k : ℕ) (hm : 0<I.m) (hU : 1≤U)
    (hn : NumbersBounded I (U:ℝ)) (hf : ∀ j,|(f j:ℝ)|≤U)
    (model : RoundState D I) (j : Fin I.m) (back : Bool)
    (hModel : LoopInv D I f (ipmQualityPrecision I.m U k) M j.val model)
    (hFP : ∀ j,IsFixedPoint (ipmQualityPrecision I.m U k) (f j))
    (hFrac : isIntRat (f j)=false)
    (hComp : (D.toForest model.df).SameComp (I.edge j).tail (I.edge j).head) :
    let L := ipmQualityLimbs I.m U k
    let P := ipmQualityPrecision I.m U k
    let clean := roundCycleClean D I (f j) model j back
    let q := roundCycleValue D model.df j (f j) back
    let δ := roundCycleDelta D model.df j (f j) back
    ForestFits D 4 L P model.df ∧
      ForestFits D 4 L P (D.pathAdd model.df (roundFrom (I.edge j) back) (roundTo (I.edge j) back) δ) ∧
      ForestFits D 4 L P clean.1 ∧ Num.Fits 4 L (I.edge j).cost ∧ RatFits 4 L P q ∧
      (isIntRat q=false → RatFits 4 L P (⌊q⌋:ℚ) ∧ RatFits 4 L P ((⌈q⌉:ℚ)-q) ∧
        RatFits 4 L P (q-(⌊q⌋:ℚ))) := by
  dsimp only
  have hM := hModel
  obtain ⟨_,_,hStrict,_,_,_,_,_,_,_,_,_,_,_,_,hBits,_,_⟩ := hM
  obtain ⟨_,hP,hLo,hHi,hPushed,hClean,_,_,_,_,_,_⟩ :=
    roundCycleClean_properties hD model j back hModel hFP hFrac hComp
  let x := roundCycleValue D model.df j (f j) back
  have hX : |(x:ℝ)|≤U := round_between_abs_le (hf j) hLo hHi
  have hBound := round_capacity_range_widened I.m U k hm hU
  have hC := (hn.2 j).2.2
  refine ⟨roundForest_fits_widened U k hm hU hn hf (fun e he => ⟨(hStrict e he).1.1,(hBits hFP).1 e he⟩),
    roundForest_fits_widened U k hm hU hn hf hPushed,
    roundForest_fits_widened U k hm hU hn hf (fun e he => ⟨(hClean e he).1,(hClean e he).2.1,
      (hClean e he).2.2.1,(hClean e he).2.2.2.1⟩),
    (fits_integer_at_quality_precision I.m U k (I.edge j).cost (by linarith only [hC,hBound])).1,
    ratFits_widened_precision I.m U k x hP (by linarith only [hX,hBound]),?_⟩
  intro hQ
  exact ⟨(round_availability_fits_widened I.m U k x hm hU hP hX hQ).1,
    (round_availability_fits_widened I.m U k x hm hU hP hX hQ).2.2,
    (round_availability_fits_widened I.m U k x hm hU hP hX hQ).2.1⟩

end MinCostFlow.IPM.Machine
