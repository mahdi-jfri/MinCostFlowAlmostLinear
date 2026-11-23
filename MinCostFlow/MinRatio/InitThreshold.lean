module

public import MinCostFlow.MinRatio.InitThresholdStore
public import MinCostFlow.Num.Logarithm
public import MinCostFlow.Num.PackWord
public import MinCostFlow.Num.LoadSmall
public import MinCostFlow.Num.IPM.BitLength
import MinCostFlow.MinRatio.ShiftForestScan
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Size
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Runtime logarithm for the rebuild threshold

Allocate fixed-point inputs, run the shared logarithm procedure, and read
its enclosure for the checked threshold store.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain

/-- Run the shared logarithm procedure using runtime format and range
words. The input block holds the vertex count plus two. -/
@[expose] def approximateInitVertexLog (entry : ℕ) : Stmt :=
  .call 99 entry [.reg 95, .reg 96, .reg 67, .reg 68, .reg 97, .reg 98]

/-- The allocated logarithm block has the absolute error required for
forming a threshold enclosure, and caller registers survive the call. -/
theorem approximateInitLogValue_runs
    {w h accuracy entry a one limbs precision range heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p entry (Num.logarithmContract w h accuracy))
    (ha : st.regs 95 = a) (hone : st.regs 96 = one)
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision)
    (hE : st.regs 97 = range) (hh : st.regs 98 = heap)
    (hwords : ∀ v ∈ [a, one, limbs, precision, range, heap], v < 2 ^ w)
    (hpre : (Num.logarithmContract w h accuracy).pre [a, one, limbs, precision, range, heap] st.mem)
    {value : ℝ} (hvalue : Num.fixVal st.mem a h limbs precision = value) :
    ∃ out c ret, Runs w p ω (approximateInitVertexLog entry) st .normal out c ∧
      out.regs 99 = ret ∧ (∀ r ≠ 99, out.regs r = st.regs r) ∧
      heap ≤ ret ∧ ret ≤ heap + Num.logarithmSpace limbs precision range ∧
      (∀ addr < heap, out.mem addr = st.mem addr) ∧ ZeroFrom out.mem ret ∧
      Num.Valid out.mem (ret - limbs) h limbs ∧
      |Num.fixVal out.mem (ret - limbs) h limbs precision - Real.log value| ≤
        1 / (2 : ℝ) ^ accuracy ∧ c ≤ Num.logarithmCost limbs precision range + 7 := by
  have hargs : evalArgs w st [.reg 95, .reg 96, .reg 67, .reg 68, .reg 97, .reg 98] =
      some [a, one, limbs, precision, range, heap] := by
    simp [evalArgs, Expr.eval, ha, hone, hL, hP, hE, hh]
  obtain ⟨out, c, ret, hr, hp, hreg, hkeep, hc⟩ :=
    runs_call_of_meetsContract (r := 99) himpl hargs hwords hpre ω
  obtain ⟨⟨hretLo, hretHi, hframe, hzero, _⟩, hvalid, herror⟩ := hp
  change |Num.fixVal out.mem (ret - limbs) h limbs precision -
    Real.log (Num.fixVal st.mem a h limbs precision)| ≤ 1 / (2 : ℝ) ^ accuracy at herror
  rw [hvalue] at herror
  change c ≤ 6 + Num.logarithmCost limbs precision range + 1 at hc
  exact ⟨out, c, ret, hr, hreg, hkeep, hretLo, hretHi, hframe, hzero, hvalid, herror, by omega⟩

/-- The allocated logarithm block has the absolute error required for
forming a threshold enclosure, and caller registers survive the call. -/
theorem approximateInitVertexLog_runs
    {w h accuracy entry N a one limbs precision range heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p entry (Num.logarithmContract w h accuracy))
    (ha : st.regs 95 = a) (hone : st.regs 96 = one)
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision)
    (hE : st.regs 97 = range) (hh : st.regs 98 = heap)
    (hwords : ∀ v ∈ [a, one, limbs, precision, range, heap], v < 2 ^ w)
    (hpre : (Num.logarithmContract w h accuracy).pre [a, one, limbs, precision, range, heap] st.mem)
    (hN : Num.fixVal st.mem a h limbs precision = (N : ℝ) + 2) :
    ∃ out c ret, Runs w p ω (approximateInitVertexLog entry) st .normal out c ∧
      out.regs 99 = ret ∧ (∀ r ≠ 99, out.regs r = st.regs r) ∧
      heap ≤ ret ∧ ret ≤ heap + Num.logarithmSpace limbs precision range ∧
      (∀ addr < heap, out.mem addr = st.mem addr) ∧ ZeroFrom out.mem ret ∧
      Num.Valid out.mem (ret - limbs) h limbs ∧
      |Num.fixVal out.mem (ret - limbs) h limbs precision - Real.log ((N : ℝ) + 2)| ≤
        1 / (2 : ℝ) ^ accuracy ∧ c ≤ Num.logarithmCost limbs precision range + 7 :=
  approximateInitLogValue_runs (ω := ω) himpl ha hone hL hP hE hh hwords hpre hN

/-- Bounding a positive logarithm away from zero permits unsigned
packing of the fixed-point numerator. -/
theorem initLogValue_scaledError {mem : ℕ → ℕ} {a h limbs precision accuracy : ℕ} {value : ℝ}
    (hpos : 1 ≤ accuracy) (hwidth : accuracy ≤ precision)
    (hlog : (1 / 2 : ℝ) ≤ Real.log value)
    (herror : |Num.fixVal mem a h limbs precision - Real.log value| ≤
      1 / (2 : ℝ) ^ accuracy) :
    let approx := (Num.intVal mem a h limbs).toNat
    let scale := 2 ^ precision
    let error := 2 ^ (precision - accuracy)
    0 ≤ Num.intVal mem a h limbs ∧
      |(approx : ℝ) / scale - Real.log value| ≤ (error : ℝ) / scale := by
  dsimp only
  have hpow : (2 : ℝ) ≤ (2 : ℝ) ^ accuracy := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hpos
  have hhalf' : 1 / (2 : ℝ) ^ accuracy ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hpow
  have hval : 0 ≤ Num.fixVal mem a h limbs precision := by
    have hl := (abs_le.mp herror).1
    linarith only [hl, hlog, hhalf']
  have hn : 0 ≤ Num.intVal mem a h limbs := by
    have ht : (0 : ℝ) ≤ (Num.intVal mem a h limbs : ℝ) := by
      simpa only [zero_mul] using
        (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ precision)).mp hval
    exact_mod_cast ht
  refine ⟨hn, ?_⟩
  have hcast : ((Num.intVal mem a h limbs).toNat : ℝ) = (Num.intVal mem a h limbs : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hn
  rw [hcast]
  change |Num.fixVal mem a h limbs precision - _| ≤ _
  refine herror.trans_eq ?_
  have hsplit : (2 : ℝ) ^ precision = 2 ^ (precision - accuracy) * 2 ^ accuracy := by
    rw [← pow_add, Nat.sub_add_cancel hwidth]
  rw [hsplit]
  field_simp

/-- An accuracy of at least one bit gives a nonnegative vertex logarithm numerator. -/
theorem initVertexLog_scaledError {mem : ℕ → ℕ} {a h limbs precision accuracy N : ℕ}
    (hpos : 1 ≤ accuracy) (hwidth : accuracy ≤ precision)
    (herror : |Num.fixVal mem a h limbs precision - Real.log ((N : ℝ) + 2)| ≤
      1 / (2 : ℝ) ^ accuracy) :
    let approx := (Num.intVal mem a h limbs).toNat
    let scale := 2 ^ precision
    let error := 2 ^ (precision - accuracy)
    0 ≤ Num.intVal mem a h limbs ∧
      |(approx : ℝ) / scale - Real.log ((N : ℝ) + 2)| ≤ (error : ℝ) / scale := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log ((N : ℝ) + 2) := by
    have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
      linarith only [Real.log_two_gt_d9]
    exact htwo.trans (Real.log_le_log (by norm_num) (by
      linarith only [Nat.cast_nonneg (α := ℝ) N]))
  exact initLogValue_scaledError hpos hwidth hlog herror

/-- The logarithm procedure's accuracy bound supplies both squared
endpoints used by the rebuild threshold calculation for Algorithm 1
(page 20). -/
theorem initVertexLog_squareBounds {mem : ℕ → ℕ} {a h limbs precision accuracy N : ℕ}
    (hpos : 1 ≤ accuracy) (hwidth : accuracy ≤ precision)
    (herror : |Num.fixVal mem a h limbs precision - Real.log ((N : ℝ) + 2)| ≤
      1 / (2 : ℝ) ^ accuracy) :
    let approx := (Num.intVal mem a h limbs).toNat
    let error : ℕ := 2 ^ (precision - accuracy)
    let scale : ℕ := 2 ^ precision
    ((approx - error : ℕ) ^ 2 : ℝ) / ((scale ^ 2 : ℕ) : ℝ) ≤
        (Real.log ((N : ℝ) + 2)) ^ 2 ∧
      (Real.log ((N : ℝ) + 2)) ^ 2 ≤
        ((approx + error : ℕ) ^ 2 : ℝ) / ((scale ^ 2 : ℕ) : ℝ) := by
  dsimp only
  apply rebuildLogSquare_scaled_bounds N _ _ _ (by positivity)
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using (initVertexLog_scaledError hpos hwidth herror).2

/-- Pack the logarithm numerator from the end of the allocated block
using the runtime limb count. -/
@[expose] def packInitVertexLog (entry : ℕ) : Stmt :=
  .call 2 entry [.bin .sub (.reg 99) (.reg 67), .reg 67]

/-- A nonnegative logarithm numerator that fits a word can be read by
the shared packing procedure without changing memory. -/
theorem packInitVertexLog_runs
    {w h entry top limbs : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p entry (Num.packWordContract w h))
    (htop : st.regs 99 = top) (hL : st.regs 67 = limbs)
    (hle : limbs ≤ top) (hw : top < 2 ^ w)
    (hv : Num.Valid st.mem (top - limbs) h limbs)
    (hn : 0 ≤ Num.intVal st.mem (top - limbs) h limbs)
    (hfit : (Num.intVal st.mem (top - limbs) h limbs).toNat < 2 ^ w) :
    ∃ out c, Runs w p ω (packInitVertexLog entry) st .normal out c ∧
      out.regs 2 = (Num.intVal st.mem (top - limbs) h limbs).toNat ∧
      out.mem = st.mem ∧ (∀ r ≠ 2, out.regs r = st.regs r) ∧
      c ≤ 25 * limbs + 11 := by
  have ha : top - limbs < 2 ^ w := (Nat.sub_le _ _).trans_lt hw
  have hl : limbs < 2 ^ w := hle.trans_lt hw
  have hu : Num.unsignedVal st.mem (top - limbs) h limbs =
      (Num.intVal st.mem (top - limbs) h limbs).toNat := by
    unfold Num.intVal Num.signedVal at hn ⊢
    have hub := Num.unsignedVal_lt hv
    split at hn <;> split <;> omega
  have hargs : evalArgs w st [.bin .sub (.reg 99) (.reg 67), .reg 67] =
      some [top - limbs, limbs] := by
    simp [evalArgs, Expr.eval, BinOp.eval, htop, hL, ha]
  obtain ⟨out, c, ret, hr, hp, hreg, hkeep, hc⟩ :=
    runs_call_of_meetsContract (r := 2) himpl hargs (by
      intro v hm
      simp at hm
      rcases hm with rfl | rfl
      · exact ha
      · exact hl) ⟨top - limbs, limbs, rfl, by omega, hv, hu ▸ hfit⟩ ω
  obtain ⟨hmem, hret⟩ := hp
  change ret = Num.unsignedVal st.mem (top - limbs) h limbs at hret
  change c ≤ 4 + (25 * limbs + 6) + 1 at hc
  exact ⟨out, c, hr, hreg.trans (hret.trans hu), hmem, hkeep, by omega⟩

/-- Compute the error and scale words from the runtime precision and
the accuracy in register 100. -/
@[expose] def prepareInitLogScale : Stmt :=
  .assign 3 (.bin .shiftLeft (.const 1) (.bin .sub (.reg 68) (.reg 100))) ;;
  .assign 4 (.bin .shiftLeft (.const 1) (.reg 68))

/-- The scale and error use two shifts, with no change to the packed
numerator or threshold parameters. -/
theorem prepareInitLogScale_runs {w precision accuracy : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hP : st.regs 68 = precision) (hq : st.regs 100 = accuracy)
    (hwidth : precision < w) :
    ∃ out, Runs w p ω prepareInitLogScale st .normal out 11 ∧
      out.regs 3 = 2 ^ (precision - accuracy) ∧ out.regs 4 = 2 ^ precision ∧
      (∀ r, r ≠ 3 → r ≠ 4 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  have hp : 2 ^ precision < 2 ^ w := Nat.pow_lt_pow_right (by decide) hwidth
  have he : 2 ^ (precision - accuracy) < 2 ^ w :=
    (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)).trans_lt hp
  have hone : 1 < 2 ^ w := (Nat.one_le_two_pow).trans_lt hp
  have hexp : precision - accuracy < 2 ^ w :=
    (Nat.le_of_lt (Nat.lt_two_pow_self)).trans_lt he
  let mid := { st with regs := Function.update st.regs 3 (2 ^ (precision - accuracy)) }
  let out := { mid with regs := Function.update mid.regs 4 (2 ^ precision) }
  refine ⟨out, ?_, by simp [out, mid], by simp [out], ?_, rfl, rfl⟩
  · unfold prepareInitLogScale
    refine runs_seq_iff.mpr (Or.inr ⟨mid, 6, 4, ?_, ?_, rfl⟩)
    · apply runs_assign_iff.mpr
      refine ⟨_, ?_, rfl, rfl, rfl⟩
      simp [Expr.eval, BinOp.eval, hP, hq, hone, hexp, he, Nat.shiftLeft_eq]
    · apply runs_assign_iff.mpr
      refine ⟨_, ?_, rfl, rfl, rfl⟩
      simp [Expr.eval, BinOp.eval, mid, hP, hone, hp, Nat.shiftLeft_eq]
  · intro r h3 h4
    simp [out, mid, h3, h4]

/-- Allocate the limb block for the vertex count plus two, using the
runtime scale in register 4. Register 98 advances to the next heap word. -/
@[expose] def encodeInitVertexLogInput (entry : ℕ) : Stmt :=
  .call 98 entry [.bin .mul (.bin .add (.reg 92) (.const 2)) (.reg 4), .reg 67, .reg 98]

/-- Load the fixed-point numerator for the vertex count plus two when
its scaled value fits in one word. -/
theorem encodeInitVertexLogInput_runs
    {w h entry N precision limbs heap : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p entry (Num.loadSmallContract w h))
    (hN : st.regs 92 = N) (hscale : st.regs 4 = 2 ^ precision)
    (hL : st.regs 67 = limbs) (hh : st.regs 98 = heap)
    (hw : N + 2 < 2 ^ w) (hfit : (N + 2) * 2 ^ precision < 2 ^ w)
    (hroom : heap + limbs < 2 ^ w) (hz : ZeroFrom st.mem heap) :
    ∃ out c, Runs w p ω (encodeInitVertexLogInput entry) st .normal out c ∧
      out.regs 98 = heap + limbs ∧ (∀ r ≠ 98, out.regs r = st.regs r) ∧
      ListAt out.mem heap (Num.digits h limbs ((N + 2) * 2 ^ precision)) ∧
      (∀ addr < heap, out.mem addr = st.mem addr) ∧ ZeroFrom out.mem (heap + limbs) ∧
      c ≤ 23 * limbs + 14 := by
  let numerator := (N + 2) * 2 ^ precision
  have hargs : evalArgs w st
      [.bin .mul (.bin .add (.reg 92) (.const 2)) (.reg 4), .reg 67, .reg 98] =
        some [numerator, limbs, heap] := by
    simp [evalArgs, Expr.eval, BinOp.eval, hN, hscale, hL, hh, hw, numerator, hfit,
      show 2 < 2 ^ w by omega]
  have hwords : ∀ v ∈ [numerator, limbs, heap], v < 2 ^ w := by
    intro v hm
    simp at hm
    rcases hm with rfl | rfl | rfl
    · exact hfit
    · omega
    · omega
  have hpre : (Num.loadSmallContract w h).pre [numerator, limbs, heap] st.mem :=
    ⟨⟨numerator, limbs, heap, rfl⟩, hz, hroom⟩
  obtain ⟨out, c, ret, hr, hp, hreg, hkeep, hc⟩ :=
    runs_call_of_meetsContract (r := 98) himpl hargs hwords hpre ω
  obtain ⟨hret, _, _, hframe, hzero, hblock⟩ := hp
  change ret = heap + limbs at hret
  rw [hret] at hzero
  change c ≤ 7 + (23 * limbs + 6) + 1 at hc
  exact ⟨out, c, hr, hreg.trans hret, hkeep, hblock, hframe, hzero, by omega⟩

/-- The stored digits of a scaled nonnegative integer give its exact
fixed-point value when the numerator is below the signed cutoff. -/
theorem initLogInput_value {mem : ℕ → ℕ} {a h limbs precision value : ℕ}
    (hblock : ListAt mem a (Num.digits h limbs (value * 2 ^ precision)))
    (hfit : 2 * (value * 2 ^ precision) < Num.capacity h limbs) :
    Num.Valid mem a h limbs ∧ Num.fixVal mem a h limbs precision = (value : ℝ) := by
  obtain ⟨hv, _, hi⟩ := Num.loadSmall_value hblock
  have hm : value * 2 ^ precision < Num.capacity h limbs := by omega
  rw [Nat.mod_eq_of_lt hm, Num.signedVal, ite_eq_right (Nat.not_le.mpr hfit), sub_zero] at hi
  refine ⟨hv, ?_⟩
  rw [Num.fixVal, hi]
  push_cast
  field_simp

/-- Allocate the constant one in the same runtime fixed-point format
as the logarithm input. -/
@[expose] def encodeInitLogOne (entry : ℕ) : Stmt :=
  .call 98 entry [.reg 4, .reg 67, .reg 98]

/-- The one block is valid and stores the exact power-of-two numerator
required by the shared logarithm routine. -/
theorem encodeInitLogOne_runs
    {w h entry precision limbs heap : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p entry (Num.loadSmallContract w h))
    (hscale : st.regs 4 = 2 ^ precision)
    (hL : st.regs 67 = limbs) (hh : st.regs 98 = heap)
    (hw : 2 ^ precision < 2 ^ w) (hfit : 2 * 2 ^ precision < Num.capacity h limbs)
    (hroom : heap + limbs < 2 ^ w) (hz : ZeroFrom st.mem heap) :
    ∃ out c, Runs w p ω (encodeInitLogOne entry) st .normal out c ∧
      out.regs 98 = heap + limbs ∧ (∀ r ≠ 98, out.regs r = st.regs r) ∧
      Num.Valid out.mem heap h limbs ∧
      Num.intVal out.mem heap h limbs = (2 : ℤ) ^ precision ∧
      (∀ addr < heap, out.mem addr = st.mem addr) ∧ ZeroFrom out.mem (heap + limbs) ∧
      c ≤ 23 * limbs + 10 := by
  have hargs : evalArgs w st [.reg 4, .reg 67, .reg 98] =
      some [2 ^ precision, limbs, heap] := by
    simp [evalArgs, Expr.eval, hscale, hL, hh]
  have hwords : ∀ v ∈ [2 ^ precision, limbs, heap], v < 2 ^ w := by
    intro v hm
    simp at hm
    rcases hm with rfl | rfl | rfl
    · exact hw
    · omega
    · omega
  have hpre : (Num.loadSmallContract w h).pre [2 ^ precision, limbs, heap] st.mem :=
    ⟨⟨_, limbs, heap, rfl⟩, hz, hroom⟩
  obtain ⟨out, c, ret, hr, hp, hreg, hkeep, hc⟩ :=
    runs_call_of_meetsContract (r := 98) himpl hargs hwords hpre ω
  obtain ⟨hret, _, _, hframe, hzero, hblock⟩ := hp
  change ret = heap + limbs at hret
  change ListAt out.mem heap (Num.digits h limbs (2 ^ precision)) at hblock
  obtain ⟨hv, _, hi⟩ := Num.loadSmall_value hblock
  have hm : 2 ^ precision < Num.capacity h limbs := by omega
  rw [Nat.mod_eq_of_lt hm, Num.signedVal, ite_eq_right (Nat.not_le.mpr hfit), sub_zero] at hi
  rw [hret] at hzero
  change c ≤ 3 + (23 * limbs + 6) + 1 at hc
  exact ⟨out, c, hr, hreg.trans hret, hkeep, hv, by exact_mod_cast hi, hframe, hzero, by omega⟩

/-- Allocate the logarithm argument and the constant one consecutively. -/
@[expose] def encodeInitLogInputs (entry : ℕ) : Stmt :=
  encodeInitVertexLogInput entry ;; encodeInitLogOne entry

/-- Both logarithm arguments have the exact fixed-point values, with the
second allocation preserving the first block. -/
theorem encodeInitLogInputs_runs
    {w h entry N precision limbs heap : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p entry (Num.loadSmallContract w h))
    (hN : st.regs 92 = N) (hscale : st.regs 4 = 2 ^ precision)
    (hL : st.regs 67 = limbs) (hh : st.regs 98 = heap)
    (hw : N + 2 < 2 ^ w)
    (hword : (N + 2) * 2 ^ precision < 2 ^ w)
    (hfit : 2 * ((N + 2) * 2 ^ precision) < Num.capacity h limbs)
    (hroom : heap + limbs + limbs < 2 ^ w) (hz : ZeroFrom st.mem heap) :
    ∃ out c, Runs w p ω (encodeInitLogInputs entry) st .normal out c ∧
      out.regs 98 = heap + limbs + limbs ∧ (∀ r ≠ 98, out.regs r = st.regs r) ∧
      Num.Valid out.mem heap h limbs ∧
      Num.fixVal out.mem heap h limbs precision = (N : ℝ) + 2 ∧
      Num.Valid out.mem (heap + limbs) h limbs ∧
      Num.intVal out.mem (heap + limbs) h limbs = (2 : ℤ) ^ precision ∧
      (∀ addr < heap, out.mem addr = st.mem addr) ∧
      ZeroFrom out.mem (heap + limbs + limbs) ∧ c ≤ 46 * limbs + 25 := by
  obtain ⟨mid, c₁, hr₁, hheap, hreg₁, hblock, hframe₁, hz₁, hc₁⟩ :=
    encodeInitVertexLogInput_runs (ω := ω) himpl hN hscale hL hh hw hword (by omega) hz
  have hpow : 2 ^ precision ≤ (N + 2) * 2 ^ precision := by
    simpa only [one_mul] using Nat.mul_le_mul_right (2 ^ precision) (show 1 ≤ N + 2 by omega)
  obtain ⟨out, c₂, hr₂, hout, hreg₂, hvOne, hOne, hframe₂, hz₂, hc₂⟩ :=
    encodeInitLogOne_runs (ω := ω) himpl ((hreg₁ 4 (by decide)).trans hscale)
      ((hreg₁ 67 (by decide)).trans hL) hheap (hpow.trans_lt hword) (by omega) hroom hz₁
  have hblock' : ListAt out.mem heap (Num.digits h limbs ((N + 2) * 2 ^ precision)) := by
    intro j hj
    have hj' : j < limbs := by simpa only [Num.digits_length] using hj
    exact (hframe₂ (heap + j) (by omega)).trans (hblock j hj)
  obtain ⟨hv, hvalue⟩ := initLogInput_value hblock' hfit
  refine ⟨out, c₁ + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c₁, c₂, hr₁, hr₂, rfl⟩),
    hout, fun r hr => (hreg₂ r hr).trans (hreg₁ r hr), hv, ?_, hvOne, hOne,
    fun addr ha => (hframe₂ addr (by omega)).trans (hframe₁ addr ha), hz₂, by omega⟩
  exact_mod_cast hvalue

/-- Save the two argument addresses before allocating their limb blocks. -/
@[expose] def setInitLogInputPointers : Stmt :=
  .assign 95 (.reg 98) ;;
  .assign 96 (.bin .add (.reg 98) (.reg 67))

/-- Consecutive allocations supply the two pointers used by the logarithm call. -/
theorem setInitLogInputPointers_runs {w heap limbs : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hh : st.regs 98 = heap) (hL : st.regs 67 = limbs)
    (hroom : heap + limbs < 2 ^ w) :
    ∃ out, Runs w p ω setInitLogInputPointers st .normal out 7 ∧
      out.regs 95 = heap ∧ out.regs 96 = heap + limbs ∧
      (∀ r, r ≠ 95 → r ≠ 96 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  let mid := { st with regs := Function.update st.regs 95 heap }
  let out := { mid with regs := Function.update mid.regs 96 (heap + limbs) }
  have hr₁ : Runs w p ω (.assign 95 (.reg 98)) st .normal mid 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, hh], rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign 96 (.bin .add (.reg 98) (.reg 67))) mid .normal out 4 :=
    runs_assign_iff.mpr ⟨heap + limbs, by
      simp [Expr.eval, BinOp.eval, mid, hh, hL, hroom], rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 2, 4, hr₁, hr₂, rfl⟩),
    by simp [out, mid], by simp [out], fun r h95 h96 => by simp [out, mid, h95, h96],
    rfl, rfl⟩

/-- Allocate and evaluate the logarithm from the runtime vertex count. -/
@[expose] def computeInitVertexLog (load log : ℕ) : Stmt :=
  setInitLogInputPointers ;; encodeInitLogInputs load ;; approximateInitVertexLog log

/-- The input allocations establish the logarithm call's precondition
under the format, range, and heap bounds of the shared procedure. -/
theorem computeInitVertexLog_runs
    {w h load log N precision accuracy range limbs heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hlog : MeetsContract w p log (Num.logarithmContract w h accuracy))
    (hN : st.regs 92 = N) (hscale : st.regs 4 = 2 ^ precision)
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision)
    (hE : st.regs 97 = range) (hh : st.regs 98 = heap)
    (hw : N + 2 < 2 ^ w) (hword : (N + 2) * 2 ^ precision < 2 ^ w)
    (hfit : 2 * ((N + 2) * 2 ^ precision) < Num.capacity h limbs)
    (hroom : heap + limbs + limbs + Num.logarithmSpace limbs precision range < 2 ^ w)
    (hz : ZeroFrom st.mem heap) (hdiv : h ∣ precision)
    (hacc : accuracy + range + 10 ≤ precision) (hcap : precision + range + 4 ≤ h * limbs)
    (hprec : 2 * precision + 9 < 2 ^ w)
    (hlo : 1 / (2 : ℝ) ^ range ≤ (N : ℝ) + 2)
    (hhi : (N : ℝ) + 2 ≤ (2 : ℝ) ^ range) :
    ∃ out c ret, Runs w p ω (computeInitVertexLog load log) st .normal out c ∧
      out.regs 99 = ret ∧ heap + limbs ≤ ret ∧ ret < 2 ^ w ∧
      ret ≤ heap + limbs + limbs + Num.logarithmSpace limbs precision range ∧
      (∀ r, r ≠ 95 → r ≠ 96 → r ≠ 98 → r ≠ 99 → out.regs r = st.regs r) ∧
      Num.Valid out.mem (ret - limbs) h limbs ∧
      |Num.fixVal out.mem (ret - limbs) h limbs precision - Real.log ((N : ℝ) + 2)| ≤
        1 / (2 : ℝ) ^ accuracy ∧
      (∀ addr < heap, out.mem addr = st.mem addr) ∧ ZeroFrom out.mem ret ∧
      c ≤ 46 * limbs + Num.logarithmCost limbs precision range + 41 := by
  obtain ⟨s₁, hr₁, ha, hone, hkeep₁, hm₁, _⟩ :=
    setInitLogInputPointers_runs (w := w) (p := p) (ω := ω) hh hL (by omega)
  obtain ⟨s₂, c₂, hr₂, hheap, hkeep₂, hv, hvalue, hvOne, hOne, hframe₂, hz₂, hc₂⟩ :=
    encodeInitLogInputs_runs (ω := ω) hload ((hkeep₁ 92 (by decide) (by decide)).trans hN)
      ((hkeep₁ 4 (by decide) (by decide)).trans hscale)
      ((hkeep₁ 67 (by decide) (by decide)).trans hL)
      ((hkeep₁ 98 (by decide) (by decide)).trans hh) hw hword hfit (by omega) (hm₁.symm ▸ hz)
  have hkeep (r : ℕ) (hr : r ≠ 98) (hp : r ≠ 95) (ho : r ≠ 96) :
      s₂.regs r = st.regs r := (hkeep₂ r hr).trans (hkeep₁ r hp ho)
  let scratch := heap + limbs + limbs
  have hpre : (Num.logarithmContract w h accuracy).pre
      [heap, heap + limbs, limbs, precision, range, scratch] s₂.mem := by
    refine ⟨⟨heap, heap + limbs, limbs, precision, range, scratch, rfl, hdiv, hacc, hcap,
      hprec, by omega, le_rfl, hv, hvOne, hOne, ?_, ?_⟩, hz₂, hroom⟩
    · exact hvalue.symm ▸ hlo
    · exact hvalue.symm ▸ hhi
  have hwords : ∀ v ∈ [heap, heap + limbs, limbs, precision, range, scratch], v < 2 ^ w := by
    intro v hm
    simp at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp [scratch] at * <;> omega
  obtain ⟨out, c₃, ret, hr₃, hret, hkeep₃, hretLo, hretHi, hframe₃, hzero, hvout, herr, hc₃⟩ :=
    approximateInitVertexLog_runs (ω := ω) hlog ((hkeep₂ 95 (by decide)).trans ha)
      ((hkeep₂ 96 (by decide)).trans hone) (by exact (hkeep 67 (by decide) (by decide) (by decide)).trans hL)
      ((hkeep 68 (by decide) (by decide) (by decide)).trans hP)
      ((hkeep 97 (by decide) (by decide) (by decide)).trans hE) hheap hwords hpre hvalue
  refine ⟨out, 7 + (c₂ + c₃ + 1) + 1, ret, ?_, hret, ?_, ?_, by omega,
    fun r hp ho hh' hr => (hkeep₃ r hr).trans (hkeep r hh' hp ho),
    hvout, herr, ?_, hzero, by omega⟩
  · unfold computeInitVertexLog
    exact runs_seq_iff.mpr (Or.inr ⟨s₁, 7, _, hr₁,
      runs_seq_iff.mpr (Or.inr ⟨s₂, c₂, c₃, hr₂, hr₃, rfl⟩), rfl⟩)
  · omega
  · omega
  · intro addr ha'
    exact (hframe₃ addr (by omega)).trans
      ((hframe₂ addr ha').trans (congrFun hm₁ addr))

/-- Convert the allocated logarithm result to the three enclosure words. -/
@[expose] def prepareInitLogEnclosure (pack : ℕ) : Stmt :=
  packInitVertexLog pack ;; prepareInitLogScale

/-- Extract the numerator, absolute error, and scale without changing
the threshold destination or the level parameters. -/
theorem prepareInitLogValueEnclosure_runs
    {w h pack ret limbs precision accuracy : ℕ} {value : ℝ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hret : st.regs 99 = ret) (hL : st.regs 67 = limbs)
    (hP : st.regs 68 = precision) (hq : st.regs 100 = accuracy)
    (hle : limbs ≤ ret) (hw : ret < 2 ^ w) (hwidth : precision < w)
    (hv : Num.Valid st.mem (ret - limbs) h limbs)
    (hqpos : 1 ≤ accuracy) (hqprec : accuracy ≤ precision)
    (hlog : (1 / 2 : ℝ) ≤ Real.log value)
    (herr : |Num.fixVal st.mem (ret - limbs) h limbs precision - Real.log value| ≤
      1 / (2 : ℝ) ^ accuracy)
    (hfit : (Num.intVal st.mem (ret - limbs) h limbs).toNat < 2 ^ w) :
    let approx := (Num.intVal st.mem (ret - limbs) h limbs).toNat
    let error : ℕ := 2 ^ (precision - accuracy)
    let scale : ℕ := 2 ^ precision
    ∃ out c, Runs w p ω (prepareInitLogEnclosure pack) st .normal out c ∧
      out.regs 2 = approx ∧ out.regs 3 = error ∧ out.regs 4 = scale ∧
      |(approx : ℝ) / scale - Real.log value| ≤ (error : ℝ) / scale ∧
      (∀ r, r ≠ 2 → r ≠ 3 → r ≠ 4 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ c ≤ 25 * limbs + 23 := by
  dsimp only
  obtain ⟨hn, he⟩ := initLogValue_scaledError hqpos hqprec hlog herr
  obtain ⟨mid, c, hr, ha, hm, hkeep, hc⟩ :=
    packInitVertexLog_runs (ω := ω) hpack hret hL hle hw hv hn hfit
  obtain ⟨out, hs, herror, hscale, hregs, hmem, _⟩ :=
    prepareInitLogScale_runs (p := p) (ω := ω) ((hkeep 68 (by decide)).trans hP)
      ((hkeep 100 (by decide)).trans hq) hwidth
  refine ⟨out, c + 11 + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c, 11, hr, hs, rfl⟩),
    (hregs 2 (by decide) (by decide)).trans ha, herror, hscale, ?_,
    fun r h2 h3 h4 => (hregs r h3 h4).trans (hkeep r h2), hmem.trans hm, by omega⟩
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using he

/-- Specialize the enclosure to the logarithm of the vertex count plus two. -/
theorem prepareInitLogEnclosure_runs
    {w h pack ret limbs precision accuracy N : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hret : st.regs 99 = ret) (hL : st.regs 67 = limbs)
    (hP : st.regs 68 = precision) (hq : st.regs 100 = accuracy)
    (hle : limbs ≤ ret) (hw : ret < 2 ^ w) (hwidth : precision < w)
    (hv : Num.Valid st.mem (ret - limbs) h limbs)
    (hqpos : 1 ≤ accuracy) (hqprec : accuracy ≤ precision)
    (herr : |Num.fixVal st.mem (ret - limbs) h limbs precision - Real.log ((N : ℝ) + 2)| ≤
      1 / (2 : ℝ) ^ accuracy)
    (hfit : (Num.intVal st.mem (ret - limbs) h limbs).toNat < 2 ^ w) :
    let approx := (Num.intVal st.mem (ret - limbs) h limbs).toNat
    let error : ℕ := 2 ^ (precision - accuracy)
    let scale : ℕ := 2 ^ precision
    ∃ out c, Runs w p ω (prepareInitLogEnclosure pack) st .normal out c ∧
      out.regs 2 = approx ∧ out.regs 3 = error ∧ out.regs 4 = scale ∧
      |(approx : ℝ) / scale - Real.log ((N : ℝ) + 2)| ≤ (error : ℝ) / scale ∧
      (∀ r, r ≠ 2 → r ≠ 3 → r ≠ 4 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ c ≤ 25 * limbs + 23 := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log ((N : ℝ) + 2) := by
    have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
      linarith only [Real.log_two_gt_d9]
    exact htwo.trans (Real.log_le_log (by norm_num) (by
      linarith only [Nat.cast_nonneg (α := ℝ) N]))
  exact prepareInitLogValueEnclosure_runs (ω := ω) hpack hret hL hP hq hle hw hwidth hv
    hqpos hqprec hlog herr hfit

/-- Check and store the rebuild threshold from the allocated logarithm. -/
@[expose] def storeInitThresholdFromVertexLog (pack : ℕ) : Stmt :=
  prepareInitLogEnclosure pack ;; initRebuildThresholdFromLog

/-- The allocated logarithm suffices to run the checked store. If its
enclosure does not determine the floor, the threshold cell is preserved. -/
theorem storeInitThresholdFromVertexLog_runs
    (TP : SparseCoreParams) (P : ChainParams) (i : ℕ)
    {w h pack ret limbs precision accuracy N cell : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hret : st.regs 99 = ret) (hL : st.regs 67 = limbs)
    (hP : st.regs 68 = precision) (hq : st.regs 100 = accuracy)
    (hle : limbs ≤ ret) (hw : ret < 2 ^ w) (hwidth : precision < w)
    (hv : Num.Valid st.mem (ret - limbs) h limbs)
    (hqpos : 1 ≤ accuracy) (hqprec : accuracy ≤ precision)
    (herr : |Num.fixVal st.mem (ret - limbs) h limbs precision - Real.log ((N : ℝ) + 2)| ≤
      1 / (2 : ℝ) ^ accuracy)
    (hfit : (Num.intVal st.mem (ret - limbs) h limbs).toNat < 2 ^ w)
    (h0 : st.regs 0 = levelM TP P i) (h1 : st.regs 1 = P.k)
    (hcell : st.regs 11 = cell) :
    let approx := (Num.intVal st.mem (ret - limbs) h limbs).toNat
    let error : ℕ := 2 ^ (precision - accuracy)
    let scale : ℕ := 2 ^ precision
    let lower := (approx - error) ^ 2
    let upper := (approx + error) ^ 2
    let scaleSq := scale ^ 2
    let num := levelM TP P i * scaleSq
    let q := num / (P.k * upper)
    lower < 2 ^ w → upper < 2 ^ w → scaleSq < 2 ^ w →
    num < 2 ^ w → P.k * upper < 2 ^ w → P.k * lower < 2 ^ w →
    q + 1 < 2 ^ w → (q + 1) * (P.k * lower) < 2 ^ w →
    ∃ out c, Runs w p ω (storeInitThresholdFromVertexLog pack) st .normal out c ∧
      (out.regs 10 = 0 ∧ out.mem = st.mem ∨
        out.regs 10 = 1 ∧ out.mem cell = rebuildThresholdWord TP P N i) ∧
      (∀ a ≠ cell, out.mem a = st.mem a) ∧ c ≤ 25 * limbs + 86 := by
  dsimp only
  intro hlo hhi hs hn hu hl hqw hc
  obtain ⟨mid, c₁, hr₁, ha, he, hscale, herror, hkeep, hm, hc₁⟩ :=
    prepareInitLogEnclosure_runs (ω := ω) hpack hret hL hP hq hle hw hwidth hv hqpos hqprec herr hfit
  have hw' : 1 < 2 ^ w := (Nat.one_le_two_pow.trans_lt
    (Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hwidth))
  obtain ⟨out, c₂, hr₂, hres, hframe, _, hc₂⟩ :=
    initRebuildThresholdFromLog_runs (p := p) (ω := ω) TP P N i _ _ _
      ((hkeep 0 (by decide) (by decide) (by decide)).trans h0)
      ((hkeep 1 (by decide) (by decide) (by decide)).trans h1) ha he hscale
      ((hkeep 11 (by decide) (by decide) (by decide)).trans hcell)
      (by positivity) hw' herror hlo hhi hs hn hu hl hqw hc
  refine ⟨out, c₁ + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c₁, c₂, hr₁, hr₂, rfl⟩),
    ?_, fun a ha' => (hframe a ha').trans (congrFun hm a), by omega⟩
  simpa only [hm] using hres

/-- The upper endpoint bounds the lower endpoint and the extra term
in the candidate check. Reserving one upper product beyond the scaled
numerator suffices for the cross-product test. -/
theorem rebuildThreshold_checkWordBounds {w k num lower upper : ℕ}
    (horder : lower ≤ upper) (hpos : 0 < k * upper)
    (hbound : num + k * upper < 2 ^ w) :
    k * upper < 2 ^ w ∧ k * lower < 2 ^ w ∧
      num / (k * upper) + 1 < 2 ^ w ∧
      (num / (k * upper) + 1) * (k * lower) < 2 ^ w := by
  have hmul := Nat.mul_le_mul_left k horder
  have hcut : (num / (k * upper) + 1) * (k * lower) ≤ num + k * upper := by
    calc
      _ ≤ (num / (k * upper) + 1) * (k * upper) := Nat.mul_le_mul_left _ hmul
      _ ≤ _ := by
        rw [Nat.add_mul, Nat.one_mul]
        exact Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
  have hq := Nat.div_le_self num (k * upper)
  exact ⟨by omega, by omega, by omega, hcut.trans_lt hbound⟩

/-- A half-unit logarithm error leaves the upper integer endpoint
below the scaled input. The bound is independent of the returned limbs. -/
theorem initLogUpper_le_scaledInput {N approx error scale : ℕ}
    (hs : 0 < scale) (he : 2 * error ≤ scale)
    (herr : |(approx : ℝ) / scale - Real.log ((N : ℝ) + 2)| ≤ (error : ℝ) / scale) :
    approx + error ≤ (N + 2) * scale := by
  have hs' : (0 : ℝ) < scale := by exact_mod_cast hs
  have he' : (2 : ℝ) * error ≤ scale := by exact_mod_cast he
  have hlog : Real.log ((N : ℝ) + 2) ≤ (N : ℝ) + 1 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (N : ℝ) + 2 by positivity)
    linarith only [h]
  have hu := (abs_le.mp herr).2
  have hh : ((approx : ℝ) + error) / scale ≤ (N : ℝ) + 2 := by
    have hfrac : (2 * (error : ℝ)) / scale ≤ 1 :=
      (div_le_iff₀ hs').mpr (by simpa only [one_mul] using he')
    rw [add_div]
    rw [mul_div_assoc] at hfrac
    linarith only [hu, hlog, hfrac]
  exact_mod_cast (div_le_iff₀ hs').mp hh

/-- A bound on the vertex count and level parameters gives a word
budget for the squared logarithm enclosure and the checked division. -/
theorem initThreshold_wordBudget {w N precision levelSize k vertexBits parameterBits : ℕ}
    (hv : N + 2 ≤ 2 ^ vertexBits)
    (hp : levelSize + k ≤ 2 ^ parameterBits)
    (hk : 0 < k)
    (hw : 2 * (vertexBits + precision) + parameterBits < w) :
    ((N + 2) * 2 ^ precision) ^ 2 < 2 ^ w ∧
      levelSize * (2 ^ precision) ^ 2 + k * ((N + 2) * 2 ^ precision) ^ 2 < 2 ^ w := by
  let input := (N + 2) * 2 ^ precision
  have hi : input ≤ 2 ^ (vertexBits + precision) := by
    rw [pow_add]
    exact Nat.mul_le_mul_right _ hv
  have hsq : input ^ 2 ≤ 2 ^ (2 * (vertexBits + precision)) := by
    rw [Nat.mul_comm 2, pow_mul]
    exact Nat.pow_le_pow_left hi _
  have hscale : (2 ^ precision) ^ 2 ≤ input ^ 2 := by
    apply Nat.pow_le_pow_left
    simpa only [one_mul] using Nat.mul_le_mul_right (2 ^ precision) (show 1 ≤ N + 2 by omega)
  have hprod : (levelSize + k) * input ^ 2 ≤
      2 ^ (2 * (vertexBits + precision) + parameterBits) := by
    rw [Nat.add_comm (2 * (vertexBits + precision)), pow_add]
    exact Nat.mul_le_mul hp hsq
  have hbound := hprod.trans_lt (Nat.pow_lt_pow_right (by decide) hw)
  constructor
  · have hle : input ^ 2 ≤ (levelSize + k) * input ^ 2 := by
      simpa only [one_mul] using Nat.mul_le_mul_right (input ^ 2)
        (show 1 ≤ levelSize + k by omega)
    exact hle.trans_lt hbound
  · change levelSize * (2 ^ precision) ^ 2 + k * input ^ 2 < 2 ^ w
    apply lt_of_le_of_lt _ hbound
    rw [Nat.add_mul]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left levelSize hscale) _

/-- Algorithm 1's edge upper bound gives one threshold word budget
that applies to every level. -/
theorem initThreshold_chainWordBudget {TP : SparseCoreParams} {P : ChainParams}
    (hTP : TP.Valid) (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀)
    (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k) (i : ℕ) {w N precision : ℕ}
    (hw : 2 * ((N + 2).size + precision) + (P.M₀ ^ 2 + P.k).size < w) :
    ((N + 2) * 2 ^ precision) ^ 2 < 2 ^ w ∧
      levelM TP P i * (2 ^ precision) ^ 2 + P.k * ((N + 2) * 2 ^ precision) ^ 2 < 2 ^ w := by
  have hparams : levelM TP P i + P.k ≤ 2 ^ (P.M₀ ^ 2 + P.k).size :=
    (Nat.add_le_add_right (levelM_le_sq hTP hγM₀ hγk i) _).trans
      (Nat.lt_size_self _).le
  exact initThreshold_wordBudget (Nat.lt_size_self (N + 2)).le hparams P.hk hw

/-- Obtain the logarithm range from the runtime vertex count. -/
@[expose] def setInitVertexLogRange (bits : ℕ) : Stmt :=
  .call 97 bits [.bin .add (.reg 92) (.const 2)]

/-- The bit length supplies an exponent whose range contains the input
to the shared logarithm routine. -/
theorem setInitVertexLogRange_runs {w bits N : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hN : st.regs 92 = N) (hw : N + 2 < 2 ^ w) :
    ∃ out c, Runs w p ω (setInitVertexLogRange bits) st .normal out c ∧
      out.regs 97 = (N + 2).size ∧ out.mem = st.mem ∧
      (∀ r ≠ 97, out.regs r = st.regs r) ∧
      1 / (2 : ℝ) ^ (N + 2).size ≤ (N : ℝ) + 2 ∧
      (N : ℝ) + 2 ≤ (2 : ℝ) ^ (N + 2).size ∧
      c ≤ 14 * (N + 2).size + 10 := by
  have hargs : evalArgs w st [.bin .add (.reg 92) (.const 2)] = some [N + 2] := by
    simp [evalArgs, Expr.eval, BinOp.eval, hN, hw, show 2 < 2 ^ w by omega]
  obtain ⟨out, c, ret, hr, hp, hreg, hkeep, hc⟩ :=
    runs_call_of_meetsContract (r := 97) hbits hargs (by simpa using hw) ⟨_, rfl⟩ ω
  obtain ⟨hm, hret⟩ := hp
  change ret = (N + 2).size at hret
  change c ≤ 3 + (14 * (N + 2).size + 6) + 1 at hc
  refine ⟨out, c, hr, hreg.trans hret, hm, hkeep, ?_, ?_, by omega⟩
  · have hf : 1 / (2 : ℝ) ^ (N + 2).size ≤ 1 :=
      (div_le_iff₀ (by positivity)).mpr (by simpa using one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    exact hf.trans (by linarith only [Nat.cast_nonneg (α := ℝ) N])
  · exact_mod_cast (Nat.lt_size_self (N + 2)).le

/-- Give the logarithm the remaining accuracy after reserving the
range and ten guard bits required by its contract. -/
@[expose] def setInitLogAccuracy : Stmt :=
  .assign 100 (.bin .sub (.bin .sub (.reg 68) (.reg 97)) (.const 10))

/-- The accuracy word is derived from the stored precision and range. -/
theorem setInitLogAccuracy_runs {w precision range : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hP : st.regs 68 = precision) (hE : st.regs 97 = range)
    (hw : 10 < 2 ^ w) (hp : precision < 2 ^ w) :
    ∃ out, Runs w p ω setInitLogAccuracy st .normal out 6 ∧
      out.regs 100 = precision - range - 10 ∧
      (∀ r ≠ 100, out.regs r = st.regs r) ∧ out.mem = st.mem ∧ out.pos = st.pos := by
  let out := { st with regs := Function.update st.regs 100 (precision - range - 10) }
  have hsub : precision - range < 2 ^ w := (Nat.sub_le _ _).trans_lt hp
  have hacc : precision - range - 10 < 2 ^ w := (Nat.sub_le _ _).trans_lt hsub
  refine ⟨out, ?_, by simp [out], fun r hr => by simp [out, hr], rfl, rfl⟩
  exact runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hP, hE,
    hw, hsub, hacc], rfl, rfl, rfl⟩

/-- Compute the logarithm once for all of the level thresholds. -/
@[expose] def cacheInitVertexLog (bits load log : ℕ) : Stmt :=
  setInitVertexLogRange bits ;; setInitLogAccuracy ;; computeInitVertexLog load log

/-- Retain the logarithm block, its accuracy, and the registers used by
the level-size and threshold calculations. -/
theorem cacheInitVertexLog_runs
    {w h bits load log N precision limbs heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hlog : MeetsContract w p log (Num.logarithmContract w h (precision - (N + 2).size - 10)))
    (hN : st.regs 92 = N) (hscale : st.regs 4 = 2 ^ precision)
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision)
    (hh : st.regs 98 = heap)
    (hw : N + 2 < 2 ^ w) (hword : (N + 2) * 2 ^ precision < 2 ^ w)
    (hfit : 2 * ((N + 2) * 2 ^ precision) < Num.capacity h limbs)
    (hroom : heap + limbs + limbs + Num.logarithmSpace limbs precision (N + 2).size < 2 ^ w)
    (hz : ZeroFrom st.mem heap) (hdiv : h ∣ precision)
    (hacc : (N + 2).size + 11 ≤ precision) (hcap : precision + (N + 2).size + 4 ≤ h * limbs)
    (hprec : 2 * precision + 9 < 2 ^ w) :
    let accuracy := precision - (N + 2).size - 10
    ∃ out c ret, Runs w p ω (cacheInitVertexLog bits load log) st .normal out c ∧
      out.regs 99 = ret ∧ out.regs 100 = accuracy ∧ heap + limbs ≤ ret ∧ ret < 2 ^ w ∧
      ret ≤ heap + limbs + limbs + Num.logarithmSpace limbs precision (N + 2).size ∧
      Num.Valid out.mem (ret - limbs) h limbs ∧
      |Num.fixVal out.mem (ret - limbs) h limbs precision - Real.log ((N : ℝ) + 2)| ≤
        1 / (2 : ℝ) ^ accuracy ∧
      (∀ r, r < 95 ∨ 100 < r → out.regs r = st.regs r) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem ret ∧
      c ≤ 46 * limbs + Num.logarithmCost limbs precision (N + 2).size + 14 * (N + 2).size + 59 := by
  dsimp only
  obtain ⟨ready, c₀, hr₀, hE, hm, hkeep₀, hlo, hhi, hc₀⟩ :=
    setInitVertexLogRange_runs (ω := ω) hbits hN hw
  let accuracy := precision - (N + 2).size - 10
  have hqbound : accuracy + (N + 2).size + 10 ≤ precision := by dsimp [accuracy]; omega
  obtain ⟨prepared, hrPrecision, hq, hkeepPrecision, hmPrecision, _⟩ :=
    setInitLogAccuracy_runs (w := w) (p := p) (ω := ω)
      ((hkeep₀ 68 (by decide)).trans hP) hE (by omega) (by omega)
  have hprepared (r : ℕ) (hq' : r ≠ 100) (he' : r ≠ 97) :
      prepared.regs r = st.regs r :=
    (hkeepPrecision r hq').trans (hkeep₀ r he')
  have hmem : prepared.mem = st.mem := hmPrecision.trans hm
  obtain ⟨mid, c₁, ret, hr₁, hret, hretLo, hretHi, hretSpace, hkeep, hv, herr, hframe, hzero, hc₁⟩ :=
    computeInitVertexLog_runs (ω := ω) hload hlog ((hprepared 92 (by decide) (by decide)).trans hN)
      ((hprepared 4 (by decide) (by decide)).trans hscale) ((hprepared 67 (by decide) (by decide)).trans hL)
      ((hprepared 68 (by decide) (by decide)).trans hP)
      ((hkeepPrecision 97 (by decide)).trans hE) ((hprepared 98 (by decide) (by decide)).trans hh)
      hw hword hfit hroom (hmem.symm ▸ hz) hdiv hqbound hcap hprec hlo hhi
  have hreg (r : ℕ) (hr : r ≠ 95 ∧ r ≠ 96 ∧ r ≠ 98 ∧ r ≠ 99 ∧ r ≠ 97 ∧ r ≠ 100) :
      mid.regs r = st.regs r :=
    (hkeep r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1).trans (hprepared r hr.2.2.2.2.2 hr.2.2.2.2.1)
  refine ⟨mid, c₀ + (6 + c₁ + 1) + 1, ret, ?_, hret,
    (hkeep 100 (by decide) (by decide) (by decide) (by decide)).trans hq,
    hretLo, hretHi, hretSpace, hv, herr, ?_, fun addr ha => (hframe addr ha).trans (congrFun hmem addr),
    hzero, by omega⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨ready, c₀, _, hr₀,
      runs_seq_iff.mpr (Or.inr ⟨prepared, 6, c₁, hrPrecision, hr₁, rfl⟩), rfl⟩)
  · intro r hr
    exact hreg r ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- Evaluate the runtime logarithm and conditionally install the exact
integer rebuild threshold for Algorithm 1 (page 20). -/
@[expose] def computeAndStoreInitThreshold (bits load log pack : ℕ) : Stmt :=
  cacheInitVertexLog bits load log ;; storeInitThresholdFromVertexLog pack

/-- Compose the logarithm evaluation and checked threshold store.
The scaled input bounds the numerator and the products used by the
threshold check. -/
theorem computeAndStoreInitThreshold_runs
    (TP : SparseCoreParams) (P : ChainParams) (i : ℕ)
    {w h bits load log pack N precision limbs heap cell : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hlog : MeetsContract w p log (Num.logarithmContract w h (precision - (N + 2).size - 10)))
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hN : st.regs 92 = N) (hscale : st.regs 4 = 2 ^ precision)
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision)
    (hh : st.regs 98 = heap)
    (hsize : st.regs 0 = levelM TP P i) (hk : st.regs 1 = P.k)
    (hdest : st.regs 11 = cell) (hcell : cell < heap)
    (hw : N + 2 < 2 ^ w) (hword : (N + 2) * 2 ^ precision < 2 ^ w)
    (hfit : 2 * ((N + 2) * 2 ^ precision) < Num.capacity h limbs)
    (hroom : heap + limbs + limbs + Num.logarithmSpace limbs precision (N + 2).size < 2 ^ w)
    (hz : ZeroFrom st.mem heap) (hdiv : h ∣ precision)
    (hacc : (N + 2).size + 11 ≤ precision) (hcap : precision + (N + 2).size + 4 ≤ h * limbs)
    (hprec : 2 * precision + 9 < 2 ^ w) (hwidth : precision < w)
    (hkpos : 0 < P.k)
    (hupper : ((N + 2) * 2 ^ precision) ^ 2 < 2 ^ w)
    (hbudget : levelM TP P i * (2 ^ precision) ^ 2 +
      P.k * ((N + 2) * 2 ^ precision) ^ 2 < 2 ^ w) :
    ∃ out c, Runs w p ω (computeAndStoreInitThreshold bits load log pack) st .normal out c ∧
      (out.regs 10 = 0 ∧ out.mem cell = st.mem cell ∨
        out.regs 10 = 1 ∧ out.mem cell = rebuildThresholdWord TP P N i) ∧
      (∀ a < heap, a ≠ cell → out.mem a = st.mem a) ∧
      c ≤ 71 * limbs + Num.logarithmCost limbs precision (N + 2).size + 14 * (N + 2).size + 146 := by
  let accuracy := precision - (N + 2).size - 10
  have hqpos : 1 ≤ accuracy := by dsimp [accuracy]; omega
  obtain ⟨mid, c₁, ret, hr₁, hret, hq, hretLo, hretHi, _, hv, herr, hreg, hframe, _, hc₁⟩ :=
    cacheInitVertexLog_runs (ω := ω) hbits hload hlog hN hscale hL hP hh hw hword hfit
      hroom hz hdiv hacc hcap hprec
  have hqprec : accuracy ≤ precision := by omega
  have he := (initVertexLog_scaledError hqpos hqprec herr).2
  let approx := (Num.intVal mid.mem (ret - limbs) h limbs).toNat
  let error : ℕ := 2 ^ (precision - accuracy)
  let scale : ℕ := 2 ^ precision
  have herrorScale : 2 * error ≤ scale := by
    dsimp [error, scale]
    rw [← pow_succ']
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hendpoint : approx + error ≤ (N + 2) * scale :=
    initLogUpper_le_scaledInput (by dsimp [scale]; positivity) herrorScale
      (by simpa only [approx, error, scale, Nat.cast_pow, Nat.cast_ofNat] using he)
  have hupperSq := Nat.pow_le_pow_left hendpoint 2
  have ha : approx < 2 ^ w := (Nat.le_add_right _ _).trans_lt (hendpoint.trans_lt hword)
  have hu : (approx + error) ^ 2 < 2 ^ w := hupperSq.trans_lt hupper
  have hs : scale ^ 2 < 2 ^ w := by
    apply (Nat.pow_le_pow_left _ 2).trans_lt hupper
    simpa only [one_mul] using Nat.mul_le_mul_right scale (show 1 ≤ N + 2 by omega)
  have hpositive : 0 < P.k * (approx + error) ^ 2 := by
    have : 0 < error := by dsimp [error]; positivity
    positivity
  have hroomCheck : levelM TP P i * scale ^ 2 + P.k * (approx + error) ^ 2 < 2 ^ w :=
    (Nat.add_le_add_left (Nat.mul_le_mul_left P.k hupperSq) _).trans_lt hbudget
  have horder : ((Num.intVal mid.mem (ret - limbs) h limbs).toNat -
      2 ^ (precision - accuracy)) ^ 2 ≤
      ((Num.intVal mid.mem (ret - limbs) h limbs).toNat + 2 ^ (precision - accuracy)) ^ 2 :=
    Nat.pow_le_pow_left ((Nat.sub_le _ _).trans (Nat.le_add_right _ _)) _
  obtain ⟨hku, hkl, hqw, hcut⟩ :=
    rebuildThreshold_checkWordBounds horder hpositive hroomCheck
  obtain ⟨out, c₂, hr₂, hres, hframe₂, hc₂⟩ :=
    storeInitThresholdFromVertexLog_runs (ω := ω) TP P i hpack hret
      ((hreg 67 (by decide)).trans hL) ((hreg 68 (by decide)).trans hP)
      hq (by omega) hretHi hwidth hv hqpos hqprec herr ha
      ((hreg 0 (by decide)).trans hsize) ((hreg 1 (by decide)).trans hk)
      ((hreg 11 (by decide)).trans hdest) (horder.trans_lt hu) hu hs (by omega) hku hkl hqw hcut
  refine ⟨out, c₁ + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c₁, c₂, hr₁, hr₂, rfl⟩),
    ?_, fun a hheap hne => (hframe₂ a hne).trans (hframe a hheap), by omega⟩
  rcases hres with ⟨hf, hm⟩ | hset
  · exact Or.inl ⟨hf, (congrFun hm cell).trans (hframe cell hcell)⟩
  · exact Or.inr hset

/-- Set the initial logarithm input scale from the stored precision
before computing and storing the threshold. -/
@[expose] def initThresholdFromRuntimePrecision (bits load log pack : ℕ) : Stmt :=
  .assign 4 (.bin .shiftLeft (.const 1) (.reg 68)) ;;
  computeAndStoreInitThreshold bits load log pack

/-- The threshold routine needs no precomputed scale in its input registers. -/
theorem initThresholdFromRuntimePrecision_runs
    (TP : SparseCoreParams) (P : ChainParams) (i : ℕ)
    {w h bits load log pack N precision limbs heap cell : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hlog : MeetsContract w p log (Num.logarithmContract w h (precision - (N + 2).size - 10)))
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hN : st.regs 92 = N)
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision)
    (hh : st.regs 98 = heap)
    (hsize : st.regs 0 = levelM TP P i) (hk : st.regs 1 = P.k)
    (hdest : st.regs 11 = cell) (hcell : cell < heap)
    (hw : N + 2 < 2 ^ w) (hword : (N + 2) * 2 ^ precision < 2 ^ w)
    (hfit : 2 * ((N + 2) * 2 ^ precision) < Num.capacity h limbs)
    (hroom : heap + limbs + limbs + Num.logarithmSpace limbs precision (N + 2).size < 2 ^ w)
    (hz : ZeroFrom st.mem heap) (hdiv : h ∣ precision)
    (hacc : (N + 2).size + 11 ≤ precision) (hcap : precision + (N + 2).size + 4 ≤ h * limbs)
    (hprec : 2 * precision + 9 < 2 ^ w) (hwidth : precision < w)
    (hkpos : 0 < P.k)
    (hupper : ((N + 2) * 2 ^ precision) ^ 2 < 2 ^ w)
    (hbudget : levelM TP P i * (2 ^ precision) ^ 2 +
      P.k * ((N + 2) * 2 ^ precision) ^ 2 < 2 ^ w) :
    ∃ out c, Runs w p ω (initThresholdFromRuntimePrecision bits load log pack) st .normal out c ∧
      (out.regs 10 = 0 ∧ out.mem cell = st.mem cell ∨
        out.regs 10 = 1 ∧ out.mem cell = rebuildThresholdWord TP P N i) ∧
      (∀ a < heap, a ≠ cell → out.mem a = st.mem a) ∧
      c ≤ 71 * limbs + Num.logarithmCost limbs precision (N + 2).size + 14 * (N + 2).size + 151 := by
  let ready := { st with regs := Function.update st.regs 4 (2 ^ precision) }
  have hpow : 2 ^ precision < 2 ^ w := Nat.pow_lt_pow_right (by decide) hwidth
  have hone : 1 < 2 ^ w := Nat.one_le_two_pow.trans_lt hpow
  have hstart : Runs w p ω (.assign 4 (.bin .shiftLeft (.const 1) (.reg 68))) st .normal ready 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hP, hpow, hone, Nat.shiftLeft_eq],
      rfl, rfl, rfl⟩
  obtain ⟨out, c, hrun, hres, hkeep, hcost⟩ :=
    computeAndStoreInitThreshold_runs (ω := ω) (st := ready) TP P i hbits hload hlog hpack
      (by simpa [ready] using hN) (by simp [ready]) (by simpa [ready] using hL)
      (by simpa [ready] using hP) (by simpa [ready] using hh)
      (by simpa [ready] using hsize) (by simpa [ready] using hk) (by simpa [ready] using hdest)
      hcell hw hword hfit hroom hz hdiv hacc hcap hprec hwidth hkpos hupper hbudget
  exact ⟨out, 4 + c + 1, runs_seq_iff.mpr (Or.inr ⟨ready, 4, c, hstart, hrun, rfl⟩),
    hres, hkeep, by omega⟩

/-- Skip the threshold calculation when the level-size check was
inconclusive, and clear the threshold success flag in that branch. -/
@[expose] def guardInitThreshold (bits load log pack : ℕ) : Stmt :=
  .cond (.reg 18) (initThresholdFromRuntimePrecision bits load log pack)
    (.assign 10 (.const 0))

/-- Run the threshold calculation only with a certified level size.
When the level check fails, the guard preserves memory. -/
theorem guardInitThreshold_runs
    {w bits load log pack cell heap budget : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    {threshold : ℕ} (hflag : st.regs 18 = 0 ∨ st.regs 18 = 1)
    (hrun : st.regs 18 = 1 →
      ∃ out c, Runs w p ω (initThresholdFromRuntimePrecision bits load log pack) st .normal out c ∧
        (out.regs 10 = 0 ∧ out.mem cell = st.mem cell ∨
          out.regs 10 = 1 ∧ out.mem cell = threshold) ∧
        (∀ a < heap, a ≠ cell → out.mem a = st.mem a) ∧ c ≤ budget) :
    ∃ out c, Runs w p ω (guardInitThreshold bits load log pack) st .normal out c ∧
      (out.regs 10 = 0 ∧ out.mem cell = st.mem cell ∨
        out.regs 10 = 1 ∧ out.mem cell = threshold) ∧
      (∀ a < heap, a ≠ cell → out.mem a = st.mem a) ∧ c ≤ budget + 4 := by
  rcases hflag with hzero | hone
  · let out := { st with regs := Function.update st.regs 10 0 }
    have hclear : Runs w p ω (.assign 10 (.const 0)) st .normal out 2 :=
      runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by positivity], rfl, rfl, rfl⟩
    exact ⟨out, 4, runs_cond_iff.mpr ⟨0, 2, by simp [Expr.eval, hzero], hclear, rfl⟩,
      Or.inl ⟨by simp [out], rfl⟩, fun _ _ _ => rfl, by omega⟩
  · obtain ⟨out, c, hr, hpost, hframe, hc⟩ := hrun hone
    exact ⟨out, c + 2, runs_cond_iff.mpr ⟨1, c, by simp [Expr.eval, hone], hr, by simp [Expr.size]; omega⟩,
      hpost, hframe, by omega⟩

/-- The level check suffices for the guarded threshold call. Its
certificate supplies the exact level size only on the taken branch. -/
theorem guardInitThreshold_fromLevelCheck_runs
    (TP : SparseCoreParams) (P : ChainParams) (i : ℕ)
    {w h bits load log pack N precision limbs heap cell : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hlog : MeetsContract w p log (Num.logarithmContract w h (precision - (N + 2).size - 10)))
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hN : st.regs 92 = N)
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision)
    (hh : st.regs 98 = heap)
    (hflag : st.regs 18 = 0 ∨ st.regs 18 = 1)
    (hsize : st.regs 18 = 1 → st.regs 0 = levelM TP P i) (hk : st.regs 1 = P.k)
    (hdest : st.regs 11 = cell) (hcell : cell < heap)
    (hw : N + 2 < 2 ^ w) (hword : (N + 2) * 2 ^ precision < 2 ^ w)
    (hfit : 2 * ((N + 2) * 2 ^ precision) < Num.capacity h limbs)
    (hroom : heap + limbs + limbs + Num.logarithmSpace limbs precision (N + 2).size < 2 ^ w)
    (hz : ZeroFrom st.mem heap) (hdiv : h ∣ precision)
    (hacc : (N + 2).size + 11 ≤ precision) (hcap : precision + (N + 2).size + 4 ≤ h * limbs)
    (hprec : 2 * precision + 9 < 2 ^ w) (hwidth : precision < w)
    (hkpos : 0 < P.k)
    (hupper : ((N + 2) * 2 ^ precision) ^ 2 < 2 ^ w)
    (hbudget : levelM TP P i * (2 ^ precision) ^ 2 +
      P.k * ((N + 2) * 2 ^ precision) ^ 2 < 2 ^ w) :
    ∃ out c, Runs w p ω (guardInitThreshold bits load log pack) st .normal out c ∧
      (out.regs 10 = 0 ∧ out.mem cell = st.mem cell ∨
        out.regs 10 = 1 ∧ out.mem cell = rebuildThresholdWord TP P N i) ∧
      (∀ a < heap, a ≠ cell → out.mem a = st.mem a) ∧
      c ≤ 71 * limbs + Num.logarithmCost limbs precision (N + 2).size + 14 * (N + 2).size + 155 := by
  have hrun := guardInitThreshold_runs (ω := ω) (bits := bits) (load := load)
    (log := log) (pack := pack) (st := st) (w := w) (p := p) (cell := cell) (heap := heap)
    (threshold := rebuildThresholdWord TP P N i)
    (budget := 71 * limbs + Num.logarithmCost limbs precision (N + 2).size + 14 * (N + 2).size + 151)
    hflag
  obtain ⟨out, c, hr, hpost, hframe, hc⟩ := hrun (fun hone => by
    obtain ⟨out, c, hr, hpost, hframe, hc⟩ :=
      initThresholdFromRuntimePrecision_runs (ω := ω) TP P i hbits hload hlog hpack hN hL hP hh
        (hsize hone) hk hdest hcell hw hword hfit hroom hz hdiv hacc hcap hprec hwidth
        hkpos hupper hbudget
    exact ⟨out, c, hr, hpost, hframe, hc⟩)
  exact ⟨out, c, hr, hpost, hframe, by omega⟩

end MinCostFlow.MinRatio
