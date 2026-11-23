module

public import MinCostFlow.MinRatio.InitThresholdDimensions
public import MinCostFlow.Num.Subtract
public import MinCostFlow.Num.Add
public import MinCostFlow.Num.Multiply
import MinCostFlow.Num.IPM.FixedPointFacts
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Multiword rebuild logarithm endpoints

Add and subtract the certified error at the selected precision
to obtain an interval for the sparse-core logarithm.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM

/-- The logarithm block gives signed integer endpoints at its own
precision. Their difference is twice the scaled error budget. -/
theorem rebuildMultiwordLog_endpoints
    {mem : ℕ → ℕ} {addr h limbs precision accuracy input : ℕ}
    (hq : accuracy ≤ precision)
    (herr : |Num.fixVal mem addr h limbs precision - Real.log ((input + 2 : ℕ) : ℝ)| ≤
      1 / (2 : ℝ) ^ accuracy) :
    let center := Num.intVal mem addr h limbs
    let error : ℤ := 2 ^ (precision - accuracy)
    let scale : ℝ := 2 ^ precision
    (↑(center - error) : ℝ) ≤ Real.log ((input + 2 : ℕ) : ℝ) * scale ∧
      Real.log ((input + 2 : ℕ) : ℝ) * scale ≤ (↑(center + error) : ℝ) ∧
      (center + error) - (center - error) = 2 * error := by
  dsimp only
  have hs : (0 : ℝ) < 2 ^ precision := by positivity
  have hqpos : (0 : ℝ) < 2 ^ accuracy := by positivity
  have hcreal : (1 / (2 : ℝ) ^ accuracy) * 2 ^ precision = 2 ^ (precision - accuracy) := by
    conv_lhs => rw [← Nat.sub_add_cancel hq, pow_add]
    field_simp
  rw [Num.fixVal, abs_le] at herr
  have hlo := mul_le_mul_of_nonneg_right herr.1 hs.le
  have hhi := mul_le_mul_of_nonneg_right herr.2 hs.le
  rw [neg_mul, hcreal, sub_mul, div_mul_cancel₀ _ hs.ne'] at hlo
  rw [hcreal, sub_mul, div_mul_cancel₀ _ hs.ne'] at hhi
  push_cast
  push_cast at hlo hhi
  refine ⟨?_, ?_, by ring⟩
  · linarith only [hhi]
  · linarith only [hlo]

/-- Put the scaled logarithm error into a signed limb block beside
the center returned by the logarithm routine. -/
@[expose] def loadRebuildLogError (load : ℕ) : Stmt :=
  .call 105 load [.reg 100, .reg 67, .reg 99]

/-- The error block is positive in the signed representation and
allocation leaves the logarithm center below the incoming cursor. -/
theorem loadRebuildLogError_runs
    {w h load heap limbs error : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (h99 : st.regs 99 = heap) (h67 : st.regs 67 = limbs) (h100 : st.regs 100 = error)
    (hword : error < 2 ^ w) (hroom : heap + limbs < 2 ^ w)
    (hz : ZeroFrom st.mem heap) (hfit : 2 * error < Num.capacity h limbs) :
    ∃ out cost, Runs w p ω (loadRebuildLogError load) st .normal out cost ∧
      out.regs 105 = heap + limbs ∧ Num.Valid out.mem heap h limbs ∧
      Num.intVal out.mem heap h limbs = (error : ℤ) ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (heap + limbs) ∧
      (∀ r, r ≠ 105 → out.regs r = st.regs r) ∧ cost ≤ 23 * limbs + 10 := by
  have hargs : evalArgs w st [.reg 100, .reg 67, .reg 99] = some [error, limbs, heap] := by
    simp [evalArgs, Expr.eval, h100, h67, h99]
  have hpre : (Num.loadSmallContract w h).pre [error, limbs, heap] st.mem :=
    ⟨⟨error, limbs, heap, rfl⟩, hz, hroom⟩
  obtain ⟨out, cost, ret, hr, hp, hv, hf, hc⟩ :=
    runs_call_of_meetsContract (r := 105) hload hargs (by wram_words) hpre ω
  change ret = heap + limbs ∧ heap ≤ ret ∧ ret ≤ heap + limbs ∧
    (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem ret ∧
    ListAt out.mem heap (Num.digits h limbs error) at hp
  obtain ⟨heq, _, _, hframe, hzero, hdigits⟩ := hp
  obtain ⟨hvalid, hu, _⟩ := Num.loadSmall_value hdigits
  have hsmall : error < Num.capacity h limbs := by omega
  have hi : Num.intVal out.mem heap h limbs = (error : ℤ) := by
    rw [Num.intVal, hu, Nat.mod_eq_of_lt hsmall, Num.signedVal, ite_eq_right (not_le_of_gt hfit), sub_zero]
  exact ⟨out, cost, hr, hv.trans heq, hvalid, hi, hframe, heq ▸ hzero, hf, by simp [Num.loadSmallContract, heapContract, argsSize, Expr.size] at hc; omega⟩

/-- Subtract the error block from the logarithm block. The result is the
last block below the new cursor. -/
@[expose] def subtractRebuildLogError (sub : ℕ) : Stmt :=
  .call 106 sub [.bin .sub (.reg 99) (.reg 67), .reg 99, .reg 67, .reg 105]

/-- Signed subtraction gives the lower endpoint when the difference fits. -/
theorem subtractRebuildLogError_runs
    {w h sub heap limbs error : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hsub : MeetsContract w p sub (Num.subtractContract w h))
    (h99 : st.regs 99 = heap) (h67 : st.regs 67 = limbs)
    (h105 : st.regs 105 = heap + limbs) (hle : limbs ≤ heap)
    (hcenter : Num.Valid st.mem (heap - limbs) h limbs)
    (herror : Num.Valid st.mem heap h limbs)
    (hvalue : Num.intVal st.mem heap h limbs = (error : ℤ))
    (hfit : Num.Fits h limbs (Num.intVal st.mem (heap - limbs) h limbs - (error : ℤ)))
    (hz : ZeroFrom st.mem (heap + limbs)) (hroom : heap + limbs + 2 * limbs < 2 ^ w) :
    ∃ out cost, Runs w p ω (subtractRebuildLogError sub) st .normal out cost ∧
      out.regs 106 = heap + limbs + 2 * limbs ∧
      Num.Valid out.mem (heap + limbs + limbs) h limbs ∧
      Num.intVal out.mem (heap + limbs + limbs) h limbs =
        Num.intVal st.mem (heap - limbs) h limbs - (error : ℤ) ∧
      (∀ x < heap + limbs, out.mem x = st.mem x) ∧
      ZeroFrom out.mem (heap + limbs + 2 * limbs) ∧
      (∀ r, r ≠ 106 → out.regs r = st.regs r) ∧ cost ≤ 74 * limbs + 49 := by
  let args := [heap - limbs, heap, limbs, heap + limbs]
  have hargs : evalArgs w st [.bin .sub (.reg 99) (.reg 67), .reg 99, .reg 67, .reg 105] =
      some args := by simp [evalArgs, Expr.eval, BinOp.eval, h99, h67, h105, args,
        show heap - limbs < 2 ^ w by omega]
  have hpre : (Num.subtractContract w h).pre args st.mem := by
    exact ⟨⟨heap - limbs, heap, limbs, heap + limbs, rfl, by omega, le_rfl, hcenter, herror⟩,
      hz, hroom⟩
  obtain ⟨out, cost, ret, hr, hp, hv, hf, hc⟩ :=
    runs_call_of_meetsContract (r := 106) hsub hargs (by dsimp [args]; wram_words) hpre ω
  change ret = heap + limbs + 2 * limbs ∧ heap + limbs ≤ ret ∧
    ret ≤ heap + limbs + 2 * limbs ∧ (∀ x < heap + limbs, out.mem x = st.mem x) ∧
    ZeroFrom out.mem ret ∧ Num.Valid out.mem (heap + limbs + limbs) h limbs ∧ _ at hp
  obtain ⟨heq, _, _, hframe, hzero, hvalid, hval⟩ := hp
  change Num.intVal out.mem (heap + limbs + limbs) h limbs =
    Num.wrap h limbs (Num.intVal st.mem (heap - limbs) h limbs - Num.intVal st.mem heap h limbs) at hval
  rw [hvalue, Num.wrap_of_fits hfit] at hval
  exact ⟨out, cost, hr, hv.trans heq, hvalid, hval, hframe, heq ▸ hzero, hf, by
    simp [Num.subtractContract, heapContract, args, argsSize, Expr.size] at hc
    omega⟩

/-- Add the error to the logarithm center after the lower endpoint
has been stored. -/
@[expose] def addRebuildLogError (add : ℕ) : Stmt :=
  .call 105 add [.bin .sub (.reg 99) (.reg 67), .reg 99, .reg 67, .reg 106]

/-- Signed addition gives the upper endpoint and keeps both input
blocks and the lower endpoint intact. -/
theorem addRebuildLogError_runs
    {w h add heap limbs error : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hadd : MeetsContract w p add (Num.addContract w h))
    (h99 : st.regs 99 = heap) (h67 : st.regs 67 = limbs)
    (h106 : st.regs 106 = heap + limbs + 2 * limbs) (hle : limbs ≤ heap)
    (hcenter : Num.Valid st.mem (heap - limbs) h limbs)
    (herror : Num.Valid st.mem heap h limbs)
    (hvalue : Num.intVal st.mem heap h limbs = (error : ℤ))
    (hfit : Num.Fits h limbs (Num.intVal st.mem (heap - limbs) h limbs + (error : ℤ)))
    (hz : ZeroFrom st.mem (heap + limbs + 2 * limbs))
    (hroom : heap + limbs + 2 * limbs + limbs < 2 ^ w) :
    ∃ out cost, Runs w p ω (addRebuildLogError add) st .normal out cost ∧
      out.regs 105 = heap + limbs + 2 * limbs + limbs ∧
      Num.Valid out.mem (heap + limbs + 2 * limbs) h limbs ∧
      Num.intVal out.mem (heap + limbs + 2 * limbs) h limbs =
        Num.intVal st.mem (heap - limbs) h limbs + (error : ℤ) ∧
      (∀ x < heap + limbs + 2 * limbs, out.mem x = st.mem x) ∧
      ZeroFrom out.mem (heap + limbs + 2 * limbs + limbs) ∧
      (∀ r, r ≠ 105 → out.regs r = st.regs r) ∧ cost ≤ 38 * limbs + 22 := by
  let base := heap + limbs + 2 * limbs
  let args := [heap - limbs, heap, limbs, base]
  have hargs : evalArgs w st [.bin .sub (.reg 99) (.reg 67), .reg 99, .reg 67, .reg 106] =
      some args := by simp [evalArgs, Expr.eval, BinOp.eval, h99, h67, h106, args, base,
        show heap - limbs < 2 ^ w by omega]
  have hpre : (Num.addContract w h).pre args st.mem := by
    refine ⟨heap - limbs, heap, limbs, base, rfl, ⟨?_, hz, hroom⟩⟩
    exact ⟨heap - limbs, heap, limbs, 0, base, rfl, by dsimp [base]; omega,
      by dsimp [base]; omega, by decide, hcenter, herror⟩
  obtain ⟨out, cost, ret, hr, hp, hv, hf, hc⟩ :=
    runs_call_of_meetsContract (r := 105) hadd hargs (by dsimp [args, base]; wram_words) hpre ω
  change ret = base + limbs ∧ base ≤ ret ∧ ret ≤ base + limbs ∧
    (∀ x < base, out.mem x = st.mem x) ∧ ZeroFrom out.mem ret ∧
    ListAt out.mem base (Num.digits h limbs
      (Num.unsignedVal st.mem (heap - limbs) h limbs + Num.unsignedVal st.mem heap h limbs + 0)) at hp
  obtain ⟨heq, _, _, hframe, hzero, hdigits⟩ := hp
  obtain ⟨hvalid, hval⟩ := Num.addCarry_value hdigits
  simp only [Int.natCast_zero, add_zero, hvalue, Num.wrap_of_fits hfit] at hval
  exact ⟨out, cost, hr, hv.trans heq, hvalid, hval, hframe, heq ▸ hzero, hf, by
    simp [Num.addContract, args, argsSize, Expr.size] at hc
    omega⟩

/-- Store the two endpoints in separate blocks above the logarithm
center. Register 105 is the final fresh cursor. -/
@[expose] def encloseRebuildLog (load sub add : ℕ) : Stmt :=
  loadRebuildLogError load ;; subtractRebuildLogError sub ;; addRebuildLogError add

/-- The two endpoint blocks contain the exact signed center minus and
plus the scaled error. -/
theorem encloseRebuildLog_runs
    {w h load sub add heap limbs error : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hsub : MeetsContract w p sub (Num.subtractContract w h))
    (hadd : MeetsContract w p add (Num.addContract w h))
    (h99 : st.regs 99 = heap) (h67 : st.regs 67 = limbs) (h100 : st.regs 100 = error)
    (hle : limbs ≤ heap) (hcenter : Num.Valid st.mem (heap - limbs) h limbs)
    (herrorWord : error < 2 ^ w) (herrorFits : 2 * error < Num.capacity h limbs)
    (hz : ZeroFrom st.mem heap) (hroom : heap + limbs + 2 * limbs + limbs < 2 ^ w) :
    let center := Num.intVal st.mem (heap - limbs) h limbs
    Num.Fits h limbs (center - (error : ℤ)) → Num.Fits h limbs (center + (error : ℤ)) →
    ∃ out cost, Runs w p ω (encloseRebuildLog load sub add) st .normal out cost ∧
      out.regs 105 = heap + limbs + 2 * limbs + limbs ∧ out.regs 67 = limbs ∧
      Num.Valid out.mem (heap + limbs + limbs) h limbs ∧
      Num.Valid out.mem (heap + limbs + 2 * limbs) h limbs ∧
      Num.intVal out.mem (heap + limbs + limbs) h limbs = center - (error : ℤ) ∧
      Num.intVal out.mem (heap + limbs + 2 * limbs) h limbs = center + (error : ℤ) ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (heap + limbs + 2 * limbs + limbs) ∧
      out.regs 68 = st.regs 68 ∧ cost ≤ 135 * limbs + 83 := by
  dsimp only
  intro hminus hplus
  obtain ⟨s₁, c₁, hr₁, h105, heValid, heVal, hf₁, hz₁, hk₁, hc₁⟩ :=
    loadRebuildLogError_runs (ω := ω) hload h99 h67 h100 herrorWord (by omega) hz herrorFits
  have hcenter₁ : Num.Valid s₁.mem (heap - limbs) h limbs := by
    intro j hj
    rw [hf₁ _ (by omega)]
    exact hcenter j hj
  have hval₁ := Num.intVal_congr (h := h) (L := limbs)
    (fun j hj => hf₁ (heap - limbs + j) (by omega))
  obtain ⟨s₂, c₂, hr₂, h106, hlValid, hlVal, hf₂, hz₂, hk₂, hc₂⟩ :=
    subtractRebuildLogError_runs (ω := ω) hsub ((hk₁ 99 (by decide)).trans h99)
      ((hk₁ 67 (by decide)).trans h67) h105 hle hcenter₁ heValid heVal (hval₁.symm ▸ hminus)
      hz₁ (by omega)
  have hcenter₂ : Num.Valid s₂.mem (heap - limbs) h limbs := by
    intro j hj
    rw [hf₂ _ (by omega)]
    exact hcenter₁ j hj
  have heValid₂ : Num.Valid s₂.mem heap h limbs := by
    intro j hj
    rw [hf₂ _ (by omega)]
    exact heValid j hj
  have hval₂ := (Num.intVal_congr (h := h) (L := limbs)
    (fun j hj => hf₂ (heap - limbs + j) (by omega))).trans hval₁
  have heVal₂ := (Num.intVal_congr (h := h) (L := limbs)
    (fun j hj => hf₂ (heap + j) (by omega))).trans heVal
  obtain ⟨out, c₃, hr₃, hout, huValid, huVal, hf₃, hz₃, hk₃, hc₃⟩ :=
    addRebuildLogError_runs (ω := ω) hadd ((hk₂ 99 (by decide)).trans ((hk₁ 99 (by decide)).trans h99))
      ((hk₂ 67 (by decide)).trans ((hk₁ 67 (by decide)).trans h67)) h106 hle hcenter₂ heValid₂
      heVal₂ (hval₂.symm ▸ hplus) hz₂ hroom
  refine ⟨out, c₁ + (c₂ + c₃ + 1) + 1, ?_, hout, (hk₃ 67 (by decide)).trans ((hk₂ 67 (by decide)).trans ((hk₁ 67 (by decide)).trans h67)),
    ?_, huValid, ?_, by rwa [hval₂] at huVal,
    fun x hx => (hf₃ x (by omega)).trans ((hf₂ x (by omega)).trans (hf₁ x hx)), hz₃, ?_, by omega⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨s₁, c₁, _, hr₁,
      runs_seq_iff.mpr (Or.inr ⟨s₂, c₂, c₃, hr₂, hr₃, rfl⟩), rfl⟩)
  · intro j hj
    rw [hf₃ _ (by omega)]
    exact hlValid j hj
  · rw [Num.intVal_congr (fun j hj => hf₃ (heap + limbs + limbs + j) (by omega)), hlVal, hval₁]
  · exact (hk₃ 68 (by decide)).trans ((hk₂ 68 (by decide)).trans (hk₁ 68 (by decide)))

/-- At positive accuracy, both signed endpoints fit the workspace
selected for the sparse-core logarithm. -/
theorem rebuildMultiwordLog_endpoints_fit
    {mem : ℕ → ℕ} {addr h precision accuracy input : ℕ}
    (hh : 0 < h) (hacc : 1 ≤ accuracy) (hq : accuracy ≤ precision)
    (herr : |Num.fixVal mem addr h (precision + (input + 2).size + 4) precision -
      Real.log ((input + 2 : ℕ) : ℝ)| ≤ 1 / (2 : ℝ) ^ accuracy) :
    let L := precision + (input + 2).size + 4
    let center := Num.intVal mem addr h L
    let error : ℤ := 2 ^ (precision - accuracy)
    Num.Fits h L (center - error) ∧ Num.Fits h L (center + error) := by
  dsimp only
  let L := precision + (input + 2).size + 4
  let center := Num.intVal mem addr h L
  let error : ℤ := 2 ^ (precision - accuracy)
  have hs : (0 : ℝ) < 2 ^ precision := by positivity
  have he : (error : ℝ) / 2 ^ precision = 1 / (2 : ℝ) ^ accuracy := by
    apply (div_eq_iff hs.ne').mpr
    dsimp [error]
    push_cast
    conv_rhs => rw [← Nat.sub_add_cancel hq, pow_add]
    field_simp
  have hsmall : 1 / (2 : ℝ) ^ accuracy ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hacc)
  have hpos : (0 : ℝ) < (input + 2 : ℕ) := by positivity
  have hl := Real.log_nonneg (show (1 : ℝ) ≤ (input + 2 : ℕ) by exact_mod_cast (by omega : 1 ≤ input + 2))
  have hu := Real.log_le_sub_one_of_pos hpos
  have hsize : ((input + 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (input + 2).size := by
    exact_mod_cast (Nat.lt_size_self (input + 2)).le
  have hc : -(1 / (2 : ℝ) ^ accuracy) ≤ (center : ℝ) / 2 ^ precision -
      Real.log ((input + 2 : ℕ) : ℝ) ∧
      (center : ℝ) / 2 ^ precision - Real.log ((input + 2 : ℕ) : ℝ) ≤ 1 / (2 : ℝ) ^ accuracy := by
    exact abs_le.mp herr
  have hwidth : precision + (input + 2).size + 2 ≤ h * L :=
    (by dsimp [L]; omega : precision + (input + 2).size + 2 ≤ L).trans
      (Nat.le_mul_of_pos_left _ hh)
  constructor
  · apply Num.IPM.fits_of_scaled_bound (P := precision) hwidth
    rw [Int.cast_sub, sub_div, he, abs_le]
    constructor <;> linarith only [hc.1, hc.2, hl, hu, hsize, hsmall]
  · apply Num.IPM.fits_of_scaled_bound (P := precision) hwidth
    rw [Int.cast_add, add_div, he, abs_le]
    constructor <;> linarith only [hc.1, hc.2, hl, hu, hsize, hsmall,
      show 0 ≤ 1 / (2 : ℝ) ^ accuracy by positivity]

/-- Form the certified endpoint blocks from the logarithm result and
the scaled error passed in register 100. -/
theorem encloseRebuildLog_certified_runs
    {w h load sub add heap precision input : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hsub : MeetsContract w p sub (Num.subtractContract w h))
    (hadd : MeetsContract w p add (Num.addContract w h))
    (hh : 0 < h) (h99 : st.regs 99 = heap) :
    let range := (input + 2).size
    let limbs := precision + range + 4
    let accuracy := precision - range - 10
    let error := 2 ^ (precision - accuracy)
    st.regs 67 = limbs → st.regs 100 = error → limbs ≤ heap →
    Num.Valid st.mem (heap - limbs) h limbs →
    |Num.fixVal st.mem (heap - limbs) h limbs precision - Real.log ((input + 2 : ℕ) : ℝ)| ≤
      1 / (2 : ℝ) ^ accuracy →
    range + 11 ≤ precision → 4096 * (input + 2) < 2 ^ w →
    ZeroFrom st.mem heap → heap + limbs + 2 * limbs + limbs < 2 ^ w →
    ∃ out cost, Runs w p ω (encloseRebuildLog load sub add) st .normal out cost ∧
      out.regs 105 = heap + limbs + 2 * limbs + limbs ∧ out.regs 67 = limbs ∧
      Num.Valid out.mem (heap + limbs + limbs) h limbs ∧
      Num.Valid out.mem (heap + limbs + 2 * limbs) h limbs ∧
      (Num.intVal out.mem (heap + limbs + limbs) h limbs : ℝ) ≤
        Real.log ((input + 2 : ℕ) : ℝ) * (2 : ℝ) ^ precision ∧
      Real.log ((input + 2 : ℕ) : ℝ) * (2 : ℝ) ^ precision ≤
        (Num.intVal out.mem (heap + limbs + 2 * limbs) h limbs : ℝ) ∧
      Num.intVal out.mem (heap + limbs + 2 * limbs) h limbs -
        Num.intVal out.mem (heap + limbs + limbs) h limbs = 2 * (error : ℤ) ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (heap + limbs + 2 * limbs + limbs) ∧
      out.regs 68 = st.regs 68 ∧ cost ≤ 135 * limbs + 83 := by
  dsimp only
  intro hL h100 hheap hvalid herr hprec hallow hz hroom
  let range := (input + 2).size
  let limbs := precision + range + 4
  let accuracy := precision - range - 10
  have hacc : 1 ≤ accuracy := by dsimp [accuracy, range]; omega
  have hle : accuracy ≤ precision := by dsimp [accuracy]; omega
  have hwidth : precision + 1 ≤ h * limbs :=
    (show precision + 1 ≤ limbs by dsimp [limbs]; omega).trans (Nat.le_mul_of_pos_left _ hh)
  have herror : 2 * 2 ^ (precision - accuracy) < Num.capacity h limbs := by
    rw [Num.capacity_eq_two_pow, ← pow_succ']
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  have herrorWord : 2 ^ (precision - accuracy) < 2 ^ w := by
    have hg := sparseCoreLog_error_le input precision hprec
    change 2 * 2 ^ (precision - accuracy) ≤ 4096 * (input + 2) at hg
    omega
  obtain ⟨hm, hp⟩ := rebuildMultiwordLog_endpoints_fit hh hacc hle herr
  obtain ⟨out, c, hr, h105, h67, hv₁, hv₂, hlo, hhi, hf, hz', h68, hc⟩ :=
    encloseRebuildLog_runs (ω := ω) hload hsub hadd h99 hL h100 hheap hvalid
      herrorWord herror hz hroom hm hp
  obtain ⟨hlo', hhi', hgap⟩ := rebuildMultiwordLog_endpoints hle herr
  exact ⟨out, c, hr, h105, h67, hv₁, hv₂, hlo ▸ hlo', hhi ▸ hhi', by rw [hlo, hhi]; exact hgap,
    hf, hz', h68, hc⟩

/-- Evaluate the logarithm and place both endpoints above its center. -/
@[expose] def initRebuildMultiwordLogInterval (clog bits h load log sub add : ℕ) : Stmt :=
  initRebuildMultiwordLog clog bits h load log ;; encloseRebuildLog load sub add

/-- The linked logarithm interval preserves every allocation below the
initial heap, including the solver's graph and numeric tables. -/
theorem initRebuildMultiwordLogInterval_runs
    {w clog bits h load log sub add heap M N depth L buckets degree err bound : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hp : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (hb : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hsub : MeetsContract w p sub (Num.subtractContract w h))
    (hadd : MeetsContract w p add (Num.addContract w h))
    (hheap : st.regs 98 = heap) (hz : ZeroFrom st.mem heap)
    (hh : 0 < h) (hhw : h < 2 ^ w)
    (hM : st.regs 22 = M) (hN : st.regs 92 = N) (hMpos : 0 < M)
    (hd : st.regs 75 = depth) (hL : st.regs 44 = L)
    (hB : st.regs 47 = buckets) (hD : st.regs 48 = degree) (hBpos : 0 < buckets)
    (he : st.regs 35 = err) (hbound : st.regs 36 = bound) :
    let input := SparseCore.coreNMax (M ^ 2) + M ^ 2
    let range := (input + 2).size
    let coarse := Chain.concreteThresholdScale depth
    let cap := (L + 1) * buckets * (2 * degree + 190)
    let allowance := max err (4096 * (input + 2))
    let total := cap + coarse + allowance + bound
    let width := total.size + L + range + 16
    let budget := width * (width + 5) + 7
    let precision := (budget + (h - 1)) / h * h
    input + 2 < 2 ^ w → 2 * (depth + 1) + 1 < 2 ^ w →
    total < 2 ^ w → width + 5 < 2 ^ w →
    budget + (h - 1) < 2 ^ w → precision + range + 4 < 2 ^ w →
    let limbs := precision + range + 4
    let accuracy := precision - range - 10
    MeetsContract w p log (Num.logarithmContract w h accuracy) →
    2 * precision + 9 < 2 ^ w →
    heap + limbs + limbs + Num.logarithmSpace limbs precision range +
      limbs + 2 * limbs + limbs < 2 ^ w →
    ∃ out cost ret, Runs w p ω (initRebuildMultiwordLogInterval clog bits h load log sub add)
      st .normal out cost ∧ out.regs 105 = ret + limbs + 2 * limbs + limbs ∧
      out.regs 67 = limbs ∧ out.regs 68 = precision ∧ heap ≤ ret ∧
      out.regs 105 ≤ heap + limbs + limbs + Num.logarithmSpace limbs precision range +
        limbs + 2 * limbs + limbs ∧
      Num.Valid out.mem (ret + limbs + limbs) h limbs ∧
      Num.Valid out.mem (ret + limbs + 2 * limbs) h limbs ∧
      (Num.intVal out.mem (ret + limbs + limbs) h limbs : ℝ) ≤
        Real.log ((input + 2 : ℕ) : ℝ) * (2 : ℝ) ^ precision ∧
      Real.log ((input + 2 : ℕ) : ℝ) * (2 : ℝ) ^ precision ≤
        (Num.intVal out.mem (ret + limbs + 2 * limbs) h limbs : ℝ) ∧
      Num.intVal out.mem (ret + limbs + 2 * limbs) h limbs -
        Num.intVal out.mem (ret + limbs + limbs) h limbs =
          2 * ((2 ^ (precision - accuracy) : ℕ) : ℤ) ∧
      Num.intVal out.mem (ret + limbs + 2 * limbs) h limbs -
        Num.intVal out.mem (ret + limbs + limbs) h limbs ≤ (2 : ℤ) ^ precision ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (ret + limbs + 2 * limbs + limbs) ∧
      cost ≤ 14 * range + 40 * Nat.clog 2 (2 * (depth + 1)) + 14 * total.size + 170 +
        (46 * limbs + Num.logarithmCost limbs precision range + 45) + 8 + (135 * limbs + 83) + 1 := by
  dsimp only
  intro hinput hdepth htotal hwidth hbudget hlimbs hlog hprecision hinterval
  obtain ⟨mid, c, ret, hr, h99, h100, hlo, hhi, hretBound, h67, h68, hacc, hv, herr, hf, hzero, hc⟩ :=
    initRebuildMultiwordLog_runs (ω := ω) hp hb hload hheap hz hh hhw hM hN hMpos hd hL hB hD
      hBpos he hbound hinput hdepth htotal hwidth hbudget hlimbs hlog hprecision (by omega)
  obtain ⟨out, d, hs, h105, h67out, hv₁, hv₂, hlow, hupp, hgap, hf', hz', h68out, hd'⟩ :=
    encloseRebuildLog_certified_runs (ω := ω) hload hsub hadd hh h99 h67 h100 (by omega) hv
      herr hacc (by omega) hzero (by omega)
  refine ⟨out, c + d + 1, ret, runs_seq_iff.mpr (Or.inr ⟨mid, c, d, hr, hs, rfl⟩),
    h105, h67out, h68out.trans h68, by omega, by rw [h105]; omega, hv₁, hv₂, hlow, hupp, by exact_mod_cast hgap, ?_,
    fun x hx => (hf' x (by omega)).trans (hf x hx), hz', by omega⟩
  rw [hgap]
  push_cast
  rw [← pow_succ']
  exact pow_le_pow_right₀ (by decide) (by omega)

/-- For the sparse-core logarithm, an interval no wider than one
scaled unit has a nonnegative lower endpoint. -/
theorem rebuildLogInterval_lower_nonneg
    {lo hi : ℤ} {precision input : ℕ} (hin : 2 ≤ input)
    (hhi : Real.log ((input + 2 : ℕ) : ℝ) * (2 : ℝ) ^ precision ≤ (hi : ℝ))
    (hgap : (hi - lo : ℤ) ≤ (2 : ℤ) ^ precision) : 0 ≤ lo := by
  have hlog : (1 : ℝ) ≤ Real.log ((input + 2 : ℕ) : ℝ) := by
    have hm := Real.log_le_log (show (0 : ℝ) < 2 ^ (2 : ℕ) by positivity)
      (show (2 : ℝ) ^ (2 : ℕ) ≤ ((input + 2 : ℕ) : ℝ) by
        norm_num
        exact_mod_cast (show 4 ≤ input + 2 by omega))
    rw [Real.log_pow] at hm
    norm_num at hm
    push_cast
    linarith only [hm, Real.log_two_gt_d9]
  have hscale := mul_le_mul_of_nonneg_right hlog (show (0 : ℝ) ≤ 2 ^ precision by positivity)
  have hg : (hi : ℝ) - (lo : ℝ) ≤ (2 : ℝ) ^ precision := by exact_mod_cast hgap
  exact_mod_cast (show (0 : ℝ) ≤ (lo : ℝ) by linarith only [hhi, hscale, hg])

/-- Squaring the nonnegative interval bounds the logarithm squared in
the sparsity factor of Lemma 5.17 (page 23). The lower endpoint may be
clamped at zero before squaring. -/
theorem rebuildLogInterval_square
    {lo hi : ℤ} {precision input : ℕ}
    (hlo : (lo : ℝ) ≤ Real.log ((input + 2 : ℕ) : ℝ) * (2 : ℝ) ^ precision)
    (hhi : Real.log ((input + 2 : ℕ) : ℝ) * (2 : ℝ) ^ precision ≤ (hi : ℝ)) :
    ((max 0 lo : ℤ) : ℝ) ^ 2 ≤
        Real.log ((input + 2 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ (2 * precision) ∧
      Real.log ((input + 2 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ (2 * precision) ≤ (hi : ℝ) ^ 2 := by
  have hlog : 0 ≤ Real.log ((input + 2 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ input + 2))
  have hmiddle : 0 ≤ Real.log ((input + 2 : ℕ) : ℝ) * (2 : ℝ) ^ precision :=
    mul_nonneg hlog (by positivity)
  have hmin : 0 ≤ ((max 0 lo : ℤ) : ℝ) := by exact_mod_cast (le_max_left (0 : ℤ) lo)
  have hlow : ((max 0 lo : ℤ) : ℝ) ≤ Real.log ((input + 2 : ℕ) : ℝ) * (2 : ℝ) ^ precision := by
    rw [Int.cast_max, Int.cast_zero]
    exact max_le hmiddle hlo
  rw [Nat.mul_comm 2, pow_mul, ← mul_pow]
  exact ⟨pow_le_pow_left₀ hmin hlow 2, pow_le_pow_left₀ hmiddle hhi 2⟩

/-- Square a logarithm endpoint into a double-width signed block. -/
@[expose] def squareRebuildLogEndpoint (mul endpoint cursor next : ℕ) : Stmt :=
  .call next mul [.reg endpoint, .reg endpoint, .reg 67, .reg cursor]

/-- Exact signed multiplication writes the square without touching
either of the input endpoints below the cursor. -/
theorem squareRebuildLogEndpoint_runs
    {w h mul endpoint cursor next addr heap limbs : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hmul : MeetsContract w p mul (Num.multiplyContract w h))
    (ha : st.regs endpoint = addr) (hheap : st.regs cursor = heap)
    (hL : st.regs 67 = limbs)
    (hbelow : addr + limbs ≤ heap) (hv : Num.Valid st.mem addr h limbs)
    (hz : ZeroFrom st.mem heap) (hroom : heap + 6 * limbs < 2 ^ w) :
    ∃ out cost, Runs w p ω (squareRebuildLogEndpoint mul endpoint cursor next) st .normal out cost ∧
      out.regs next = heap + 6 * limbs ∧ Num.Valid out.mem (heap + 4 * limbs) h (2 * limbs) ∧
      Num.intVal out.mem (heap + 4 * limbs) h (2 * limbs) = Num.intVal st.mem addr h limbs ^ 2 ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (heap + 6 * limbs) ∧
      (∀ r, r ≠ next → out.regs r = st.regs r) ∧
      cost ≤ (2 * limbs) * (38 * (2 * limbs) + 35) + 120 * limbs + 104 := by
  let args := [addr, addr, limbs, heap]
  have hargs : evalArgs w st [.reg endpoint, .reg endpoint, .reg 67, .reg cursor] = some args := by
    simp [evalArgs, Expr.eval, ha, hheap, hL, args]
  have hpre : (Num.multiplyContract w h).pre args st.mem :=
    ⟨⟨addr, addr, limbs, heap, rfl, hbelow, hbelow, hv, hv⟩, hz, hroom⟩
  obtain ⟨out, cost, ret, hr, hp, hret, hf, hc⟩ :=
    runs_call_of_meetsContract (r := next) hmul hargs (by dsimp [args]; wram_words) hpre ω
  change ret = heap + 6 * limbs ∧ heap ≤ ret ∧ ret ≤ heap + 6 * limbs ∧
    (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem ret ∧
    Num.Valid out.mem (heap + 4 * limbs) h (2 * limbs) ∧ _ at hp
  obtain ⟨heq, _, _, hframe, hzero, hvalid, hsq⟩ := hp
  refine ⟨out, cost, hr, hret.trans heq, hvalid, ?_, hframe, heq ▸ hzero, hf, ?_⟩
  · change Num.intVal out.mem (heap + 4 * limbs) h (2 * limbs) =
      Num.intVal st.mem addr h limbs * Num.intVal st.mem addr h limbs at hsq
    simpa only [pow_two] using hsq
  · simp [Num.multiplyContract, heapContract, args, argsSize, Expr.size] at hc
    omega

/-- The endpoint addresses are two blocks and one block below the
end cursor of interval construction. -/
@[expose] def stageRebuildLogEndpointAddresses : Stmt :=
  .assign 109 (.bin .sub (.reg 105) (.bin .mul (.const 2) (.reg 67))) ;;
  .assign 110 (.bin .sub (.reg 105) (.reg 67))

/-- Decode the endpoint addresses without changing the interval. -/
theorem stageRebuildLogEndpointAddresses_runs
    {w heap limbs : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (h105 : st.regs 105 = heap + limbs + 2 * limbs + limbs)
    (h67 : st.regs 67 = limbs) (hword : heap + limbs + 2 * limbs + limbs < 2 ^ w)
    (hw : 2 < 2 ^ w) :
    ∃ out, Runs w p ω stageRebuildLogEndpointAddresses st .normal out 11 ∧
      out.regs 109 = heap + limbs + limbs ∧ out.regs 110 = heap + limbs + 2 * limbs ∧
      out.mem = st.mem ∧ (∀ r, r ≠ 109 → r ≠ 110 → out.regs r = st.regs r) := by
  let mid := {st with regs := Function.update st.regs 109 (heap + limbs + limbs)}
  let out := {mid with regs := Function.update mid.regs 110 (heap + limbs + 2 * limbs)}
  have hr : Runs w p ω (.assign 109 (.bin .sub (.reg 105) (.bin .mul (.const 2) (.reg 67))))
      st .normal mid 6 := by
    apply runs_assign_iff.mpr
    refine ⟨_, ?_, rfl, rfl, rfl⟩
    simp [Expr.eval, BinOp.eval, h105, h67, hw, show 2 * limbs < 2 ^ w by omega,
      show heap + limbs + 2 * limbs + limbs - 2 * limbs = heap + limbs + limbs by omega]
    omega
  have hs : Runs w p ω (.assign 110 (.bin .sub (.reg 105) (.reg 67))) mid .normal out 4 := by
    apply runs_assign_iff.mpr
    refine ⟨_, ?_, rfl, rfl, rfl⟩
    simp [Expr.eval, BinOp.eval, mid, h105, h67, show heap + limbs + 2 * limbs < 2 ^ w by omega]
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 6, 4, hr, hs, rfl⟩),
    by simp [out, mid], by simp [out], rfl, fun r h109 h110 => by simp [out, mid, h109, h110]⟩

/-- Square the two endpoints in sequence. Registers 107 and 108
identify the ends of the two double-width result blocks. -/
@[expose] def squareRebuildLogEndpoints (mul : ℕ) : Stmt :=
  squareRebuildLogEndpoint mul 109 105 107 ;;
  squareRebuildLogEndpoint mul 110 107 108

/-- Both squared endpoint blocks remain valid at the final cursor. -/
theorem squareRebuildLogEndpoints_runs
    {w h mul lo hi heap limbs : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hmul : MeetsContract w p mul (Num.multiplyContract w h))
    (hlo : st.regs 109 = lo) (hhi : st.regs 110 = hi)
    (hheap : st.regs 105 = heap) (hL : st.regs 67 = limbs)
    (hlEnd : lo + limbs ≤ heap) (huEnd : hi + limbs ≤ heap)
    (hl : Num.Valid st.mem lo h limbs) (hu : Num.Valid st.mem hi h limbs)
    (hz : ZeroFrom st.mem heap) (hroom : heap + 12 * limbs < 2 ^ w) :
    ∃ out cost, Runs w p ω (squareRebuildLogEndpoints mul) st .normal out cost ∧
      out.regs 107 = heap + 6 * limbs ∧ out.regs 108 = heap + 12 * limbs ∧
      Num.Valid out.mem (heap + 4 * limbs) h (2 * limbs) ∧
      Num.Valid out.mem (heap + 10 * limbs) h (2 * limbs) ∧
      Num.intVal out.mem (heap + 4 * limbs) h (2 * limbs) = Num.intVal st.mem lo h limbs ^ 2 ∧
      Num.intVal out.mem (heap + 10 * limbs) h (2 * limbs) = Num.intVal st.mem hi h limbs ^ 2 ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (heap + 12 * limbs) ∧
      out.regs 67 = limbs ∧ out.regs 68 = st.regs 68 ∧
      cost ≤ 2 * ((2 * limbs) * (38 * (2 * limbs) + 35) + 120 * limbs + 104) + 1 := by
  obtain ⟨mid, c, hr, h107, hv, hsq, hf, hz', hk, hc⟩ :=
    squareRebuildLogEndpoint_runs (ω := ω) (next := 107) hmul hlo hheap hL hlEnd hl hz (by omega)
  have hu' : Num.Valid mid.mem hi h limbs := by
    intro j hj
    rw [hf _ (by omega)]
    exact hu j hj
  obtain ⟨out, d, hs, h108, hv', hsq', hf', hz'', hk', hd⟩ :=
    squareRebuildLogEndpoint_runs (ω := ω) (next := 108) hmul ((hk 110 (by decide)).trans hhi)
      h107 ((hk 67 (by decide)).trans hL) (by omega) hu' hz' (by omega)
  have he : heap + 6 * limbs + 4 * limbs = heap + 10 * limbs := by omega
  have hend : heap + 6 * limbs + 6 * limbs = heap + 12 * limbs := by omega
  refine ⟨out, c + d + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c, d, hr, hs, rfl⟩),
    (hk' 107 (by decide)).trans h107, h108.trans hend, ?_, he ▸ hv', ?_, ?_,
    fun x hx => (hf' x (by omega)).trans (hf x hx), hend ▸ hz'',
    (hk' 67 (by decide)).trans ((hk 67 (by decide)).trans hL),
    (hk' 68 (by decide)).trans (hk 68 (by decide)), by omega⟩
  · intro j hj
    rw [hf' _ (by omega)]
    exact hv j hj
  · rw [Num.intVal_congr (fun j hj => hf' (heap + 4 * limbs + j) (by omega)), hsq]
  · rw [← he, hsq', Num.intVal_congr (fun j hj => hf (hi + j) (by omega))]

/-- Square the endpoints using the cursor returned by the interval builder. -/
@[expose] def squareStoredRebuildLogInterval (mul : ℕ) : Stmt :=
  stageRebuildLogEndpointAddresses ;; squareRebuildLogEndpoints mul

/-- The address arithmetic and the two multiplications preserve the
interval and leave both exact squares below the returned cursor. -/
theorem squareStoredRebuildLogInterval_runs
    {w h mul heap limbs : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hmul : MeetsContract w p mul (Num.multiplyContract w h))
    (h67 : st.regs 67 = limbs) (hw : 2 < 2 ^ w) :
    let cursor := heap + limbs + 2 * limbs + limbs
    st.regs 105 = cursor →
    Num.Valid st.mem (heap + limbs + limbs) h limbs →
    Num.Valid st.mem (heap + limbs + 2 * limbs) h limbs →
    ZeroFrom st.mem cursor → cursor + 12 * limbs < 2 ^ w →
    ∃ out cost, Runs w p ω (squareStoredRebuildLogInterval mul) st .normal out cost ∧
      out.regs 107 = cursor + 6 * limbs ∧ out.regs 108 = cursor + 12 * limbs ∧
      Num.Valid out.mem (cursor + 4 * limbs) h (2 * limbs) ∧
      Num.Valid out.mem (cursor + 10 * limbs) h (2 * limbs) ∧
      Num.intVal out.mem (cursor + 4 * limbs) h (2 * limbs) =
        Num.intVal st.mem (heap + limbs + limbs) h limbs ^ 2 ∧
      Num.intVal out.mem (cursor + 10 * limbs) h (2 * limbs) =
        Num.intVal st.mem (heap + limbs + 2 * limbs) h limbs ^ 2 ∧
      (∀ x < cursor, out.mem x = st.mem x) ∧ ZeroFrom out.mem (cursor + 12 * limbs) ∧
      out.regs 67 = limbs ∧ out.regs 68 = st.regs 68 ∧
      cost ≤ 2 * ((2 * limbs) * (38 * (2 * limbs) + 35) + 120 * limbs + 104) + 13 := by
  dsimp only
  intro h105 hlo hhi hz hroom
  obtain ⟨mid, hr, h109, h110, hm, hk⟩ :=
    stageRebuildLogEndpointAddresses_runs (w := w) (p := p) (ω := ω) h105 h67 (by omega) hw
  obtain ⟨out, c, hs, h107, h108, hv₁, hv₂, hs₁, hs₂, hf, hz', h67out, h68, hc⟩ :=
    squareRebuildLogEndpoints_runs (ω := ω) hmul h109 h110
      ((hk 105 (by decide) (by decide)).trans h105)
      ((hk 67 (by decide) (by decide)).trans h67)
      (by omega) (by omega) (hm.symm ▸ hlo) (hm.symm ▸ hhi) (hm.symm ▸ hz) hroom
  exact ⟨out, 11 + c + 1, runs_seq_iff.mpr (Or.inr ⟨mid, 11, c, hr, hs, rfl⟩),
    h107, h108, hv₁, hv₂, by simpa only [hm] using hs₁, by simpa only [hm] using hs₂,
    fun x hx => (hf x hx).trans (congrFun hm x), hz', h67out, h68.trans (hk 68 (by decide) (by decide)), by omega⟩

/-- The stored squares decode to an interval for the squared logarithm
at twice the original fractional precision. -/
theorem squareStoredRebuildLogInterval_bounds
    {h heap limbs precision input : ℕ} {mem squared : ℕ → ℕ}
    (hin : 2 ≤ input) :
    let cursor := heap + limbs + 2 * limbs + limbs
    let lo := Num.intVal mem (heap + limbs + limbs) h limbs
    let hi := Num.intVal mem (heap + limbs + 2 * limbs) h limbs
    (lo : ℝ) ≤ Real.log ((input + 2 : ℕ) : ℝ) * (2 : ℝ) ^ precision →
    Real.log ((input + 2 : ℕ) : ℝ) * (2 : ℝ) ^ precision ≤ (hi : ℝ) →
    hi - lo ≤ (2 : ℤ) ^ precision →
    Num.intVal squared (cursor + 4 * limbs) h (2 * limbs) = lo ^ 2 →
    Num.intVal squared (cursor + 10 * limbs) h (2 * limbs) = hi ^ 2 →
    Num.fixVal squared (cursor + 4 * limbs) h (2 * limbs) (2 * precision) ≤
      Real.log ((input + 2 : ℕ) : ℝ) ^ 2 ∧
    Real.log ((input + 2 : ℕ) : ℝ) ^ 2 ≤
      Num.fixVal squared (cursor + 10 * limbs) h (2 * limbs) (2 * precision) := by
  dsimp only
  intro hlo hhi hgap hs₁ hs₂
  have hnonneg := rebuildLogInterval_lower_nonneg hin hhi hgap
  obtain ⟨hl, hu⟩ := rebuildLogInterval_square hlo hhi
  rw [max_eq_right hnonneg] at hl
  have hs : (0 : ℝ) < 2 ^ (2 * precision) := by positivity
  unfold Num.fixVal
  rw [hs₁, hs₂, div_le_iff₀ hs, le_div_iff₀ hs]
  push_cast
  simpa only [Nat.cast_add, Nat.cast_ofNat] using And.intro hl hu

/-- Compute both squared logarithm endpoints without materializing
the fixed-point scale in a register. -/
@[expose] def initRebuildMultiwordLogSquared (clog bits h load log sub add mul : ℕ) : Stmt :=
  initRebuildMultiwordLogInterval clog bits h load log sub add ;; squareStoredRebuildLogInterval mul

/-- The squared endpoints bound the logarithm squared at twice the
working precision and preserve all earlier allocations. -/
theorem initRebuildMultiwordLogSquared_runs
    {w clog bits h load log sub add mul heap M N depth L buckets degree err bound : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hp : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (hb : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hsub : MeetsContract w p sub (Num.subtractContract w h))
    (hadd : MeetsContract w p add (Num.addContract w h))
    (hmul : MeetsContract w p mul (Num.multiplyContract w h))
    (hheap : st.regs 98 = heap) (hz : ZeroFrom st.mem heap)
    (hh : 0 < h) (hhw : h < 2 ^ w)
    (hM : st.regs 22 = M) (hN : st.regs 92 = N) (hMpos : 0 < M)
    (hd : st.regs 75 = depth) (hL : st.regs 44 = L)
    (hB : st.regs 47 = buckets) (hD : st.regs 48 = degree) (hBpos : 0 < buckets)
    (he : st.regs 35 = err) (hbound : st.regs 36 = bound) :
    let input := SparseCore.coreNMax (M ^ 2) + M ^ 2
    let range := (input + 2).size
    let coarse := Chain.concreteThresholdScale depth
    let cap := (L + 1) * buckets * (2 * degree + 190)
    let allowance := max err (4096 * (input + 2))
    let total := cap + coarse + allowance + bound
    let width := total.size + L + range + 16
    let budget := width * (width + 5) + 7
    let precision := (budget + (h - 1)) / h * h
    input + 2 < 2 ^ w → 2 * (depth + 1) + 1 < 2 ^ w →
    total < 2 ^ w → width + 5 < 2 ^ w →
    budget + (h - 1) < 2 ^ w → precision + range + 4 < 2 ^ w →
    let limbs := precision + range + 4
    let accuracy := precision - range - 10
    MeetsContract w p log (Num.logarithmContract w h accuracy) →
    2 * precision + 9 < 2 ^ w →
    heap + limbs + limbs + Num.logarithmSpace limbs precision range +
      limbs + 2 * limbs + limbs + 12 * limbs < 2 ^ w →
    ∃ out cost cursor, Runs w p ω (initRebuildMultiwordLogSquared clog bits h load log sub add mul)
      st .normal out cost ∧ out.regs 108 = cursor + 12 * limbs ∧
      out.regs 67 = limbs ∧ out.regs 68 = precision ∧
      heap ≤ cursor ∧ out.regs 108 ≤ heap + limbs + limbs +
        Num.logarithmSpace limbs precision range + limbs + 2 * limbs + limbs + 12 * limbs ∧
      Num.Valid out.mem (cursor + 4 * limbs) h (2 * limbs) ∧
      Num.Valid out.mem (cursor + 10 * limbs) h (2 * limbs) ∧
      Num.fixVal out.mem (cursor + 4 * limbs) h (2 * limbs) (2 * precision) ≤
        Real.log ((input + 2 : ℕ) : ℝ) ^ 2 ∧
      Real.log ((input + 2 : ℕ) : ℝ) ^ 2 ≤
        Num.fixVal out.mem (cursor + 10 * limbs) h (2 * limbs) (2 * precision) ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (cursor + 12 * limbs) ∧
      cost ≤ 14 * range + 40 * Nat.clog 2 (2 * (depth + 1)) + 14 * total.size + 170 +
        (46 * limbs + Num.logarithmCost limbs precision range + 45) + 8 + (135 * limbs + 83) + 1 +
        (2 * ((2 * limbs) * (38 * (2 * limbs) + 35) + 120 * limbs + 104) + 13) + 1 := by
  dsimp only
  intro hinput hdepth htotal hwidth hbudget hlimbs hlog hprecision hroom
  obtain ⟨mid, c, ret, hr, h105, h67, h68, hretLow, hcursor, hv₁, hv₂, hlo, hhi, _, hgap, hf, hz', hc⟩ :=
    initRebuildMultiwordLogInterval_runs (ω := ω) hp hb hload hsub hadd hheap hz hh hhw
      hM hN hMpos hd hL hB hD hBpos he hbound hinput hdepth htotal hwidth hbudget hlimbs
      hlog hprecision (by omega)
  obtain ⟨out, d, hs, _, h108, hs₁, hs₂, hl, hu, hf', hz'', h67out, h68out, hcost⟩ :=
    squareStoredRebuildLogInterval_runs (ω := ω) hmul h67 (by omega) h105 hv₁ hv₂ hz' (by omega)
  have hin : 2 ≤ SparseCore.coreNMax (M ^ 2) + M ^ 2 := by
    have hm := Nat.pow_pos (n := 2) hMpos
    unfold SparseCore.coreNMax SparseCore.coreSplitMax
    omega
  obtain ⟨hlow, hupp⟩ := squareStoredRebuildLogInterval_bounds hin hlo hhi
    hgap hl hu
  refine ⟨out, c + d + 1, _, runs_seq_iff.mpr (Or.inr ⟨mid, c, d, hr, hs, rfl⟩),
    h108, h67out, h68out.trans h68, by omega, by omega, hs₁, hs₂, hlow, hupp, ?_, hz'', by omega⟩
  intro x hx
  exact (hf' x (by omega)).trans (hf x hx)

/-- Recover the upper squared logarithm block from the returned cursor
and set the width and precision for the growth-factor arithmetic. -/
@[expose] def stageRebuildLogSquareUpper : Stmt :=
  .assign 111 (.bin .mul (.const 2) (.reg 67)) ;;
  .assign 112 (.bin .sub (.reg 108) (.reg 111)) ;;
  .assign 113 (.bin .mul (.const 2) (.reg 68))

/-- The staged pointer addresses the upper square and keeps the original
limb count and precision available for the path factors. -/
theorem stageRebuildLogSquareUpper_runs
    {w cursor limbs precision : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (h108 : st.regs 108 = cursor + 12 * limbs)
    (h67 : st.regs 67 = limbs) (h68 : st.regs 68 = precision)
    (hroom : cursor + 12 * limbs < 2 ^ w) (hprec : 2 * precision < 2 ^ w)
    (hw : 2 < 2 ^ w) :
    ∃ out, Runs w p ω stageRebuildLogSquareUpper st .normal out 14 ∧
      out.regs 111 = 2 * limbs ∧ out.regs 112 = cursor + 10 * limbs ∧
      out.regs 113 = 2 * precision ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 111 → r ≠ 112 → r ≠ 113 → out.regs r = st.regs r) := by
  let s₁ := {st with regs := Function.update st.regs 111 (2 * limbs)}
  let s₂ := {s₁ with regs := Function.update s₁.regs 112 (cursor + 10 * limbs)}
  let out := {s₂ with regs := Function.update s₂.regs 113 (2 * precision)}
  have hr₁ : Runs w p ω (.assign 111 (.bin .mul (.const 2) (.reg 67))) st .normal s₁ 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, h67, hw, show 2 * limbs < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign 112 (.bin .sub (.reg 108) (.reg 111))) s₁ .normal s₂ 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s₁, h108,
      show cursor + 12 * limbs - 2 * limbs = cursor + 10 * limbs by omega,
      show cursor + 10 * limbs < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hr₃ : Runs w p ω (.assign 113 (.bin .mul (.const 2) (.reg 68))) s₂ .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s₂, s₁, h68, hw, hprec], rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨s₁, 4, 9, hr₁,
      runs_seq_iff.mpr (Or.inr ⟨s₂, 4, 4, hr₂, hr₃, rfl⟩), rfl⟩),
    by simp [out, s₂, s₁], by simp [out, s₂], by simp [out], rfl,
    fun r h111 h112 h113 => by simp [out, s₂, s₁, h111, h112, h113]⟩

/-- Compute and stage the upper squared logarithm for the growth calculation. -/
@[expose] def initRebuildMultiwordLogUpper (clog bits h load log sub add mul : ℕ) : Stmt :=
  initRebuildMultiwordLogSquared clog bits h load log sub add mul ;; stageRebuildLogSquareUpper

/-- The staged block bounds the squared logarithm and the returned
cursor has room for the next allocation. -/
theorem initRebuildMultiwordLogUpper_runs
    {w clog bits h load log sub add mul heap M N depth L buckets degree err bound : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hp : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (hb : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hsub : MeetsContract w p sub (Num.subtractContract w h))
    (hadd : MeetsContract w p add (Num.addContract w h))
    (hmul : MeetsContract w p mul (Num.multiplyContract w h))
    (hheap : st.regs 98 = heap) (hz : ZeroFrom st.mem heap)
    (hh : 0 < h) (hhw : h < 2 ^ w)
    (hM : st.regs 22 = M) (hN : st.regs 92 = N) (hMpos : 0 < M)
    (hd : st.regs 75 = depth) (hL : st.regs 44 = L)
    (hB : st.regs 47 = buckets) (hD : st.regs 48 = degree) (hBpos : 0 < buckets)
    (he : st.regs 35 = err) (hbound : st.regs 36 = bound) :
    let input := SparseCore.coreNMax (M ^ 2) + M ^ 2
    let range := (input + 2).size
    let coarse := Chain.concreteThresholdScale depth
    let cap := (L + 1) * buckets * (2 * degree + 190)
    let allowance := max err (4096 * (input + 2))
    let total := cap + coarse + allowance + bound
    let width := total.size + L + range + 16
    let budget := width * (width + 5) + 7
    let precision := (budget + (h - 1)) / h * h
    input + 2 < 2 ^ w → 2 * (depth + 1) + 1 < 2 ^ w →
    total < 2 ^ w → width + 5 < 2 ^ w →
    budget + (h - 1) < 2 ^ w → precision + range + 4 < 2 ^ w →
    let limbs := precision + range + 4
    let accuracy := precision - range - 10
    MeetsContract w p log (Num.logarithmContract w h accuracy) →
    2 * precision + 9 < 2 ^ w →
    heap + limbs + limbs + Num.logarithmSpace limbs precision range +
      limbs + 2 * limbs + limbs + 12 * limbs < 2 ^ w →
    ∃ out cost cursor, Runs w p ω (initRebuildMultiwordLogUpper clog bits h load log sub add mul)
      st .normal out cost ∧ out.regs 108 = cursor + 12 * limbs ∧
      out.regs 111 = 2 * limbs ∧ out.regs 112 = cursor + 10 * limbs ∧
      out.regs 113 = 2 * precision ∧ out.regs 67 = limbs ∧ out.regs 68 = precision ∧
      out.regs 108 < 2 ^ w ∧ heap ≤ cursor ∧
      Num.Valid out.mem (cursor + 10 * limbs) h (2 * limbs) ∧
      Real.log ((input + 2 : ℕ) : ℝ) ^ 2 ≤
        Num.fixVal out.mem (cursor + 10 * limbs) h (2 * limbs) (2 * precision) ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (cursor + 12 * limbs) ∧
      cost ≤ 14 * range + 40 * Nat.clog 2 (2 * (depth + 1)) + 14 * total.size + 170 +
        (46 * limbs + Num.logarithmCost limbs precision range + 45) + 8 + (135 * limbs + 83) + 1 +
        (2 * ((2 * limbs) * (38 * (2 * limbs) + 35) + 120 * limbs + 104) + 13) + 16 := by
  dsimp only
  intro hinput hdepth htotal hwidth hbudget hlimbs hlog hprecision hroom
  obtain ⟨mid, c, cursor, hr, h108, h67, h68, hcursor, hcursorBound, _, hv, _, hu, hf, hzero, hc⟩ :=
    initRebuildMultiwordLogSquared_runs (ω := ω) hp hb hload hsub hadd hmul hheap hz hh hhw
      hM hN hMpos hd hL hB hD hBpos he hbound hinput hdepth htotal hwidth hbudget hlimbs
      hlog hprecision hroom
  have hword := hcursorBound.trans_lt hroom
  obtain ⟨out, ht, h111, h112, h113, hm, hk⟩ :=
    stageRebuildLogSquareUpper_runs (w := w) (p := p) (ω := ω) h108 h67 h68
      (h108 ▸ hword) (by omega) (by omega)
  refine ⟨out, c + 14 + 1, cursor, runs_seq_iff.mpr (Or.inr ⟨mid, c, 14, hr, ht, rfl⟩),
    (hk 108 (by decide) (by decide) (by decide)).trans h108, h111, h112, h113,
    (hk 67 (by decide) (by decide) (by decide)).trans h67,
    (hk 68 (by decide) (by decide) (by decide)).trans h68,
    (hk 108 (by decide) (by decide) (by decide)).symm ▸ hword, hcursor, hm.symm ▸ hv,
    hm.symm ▸ hu, fun x hx => (congrFun hm x).trans (hf x hx), hm.symm ▸ hzero, by omega⟩

end MinCostFlow.MinRatio
