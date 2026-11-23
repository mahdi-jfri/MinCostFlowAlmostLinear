module

public import MinCostFlow.MinRatio.RebuildGuard
public import MinCostFlow.Chain.ConcreteDefs
public import MinCostFlow.Scaling.ClogTwoProgram
import MinCostFlow.MinRatio.ShiftForestScan
import Mathlib.Tactic.Linarith

/-!
# Computing a periodic rebuild threshold from a logarithm enclosure

The integer threshold for Algorithm 1 (page 20) can be selected by
dividing by the upper denominator and checking the resulting candidate
against the lower denominator.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain

/-- Use runtime inputs `[levelM, k, lower, upper, scale]` in registers
0 through 4. Register 7 holds the candidate and register 10 marks
whether the enclosure determines the exact floor. -/
@[expose] def selectRebuildThreshold : Stmt :=
  .assign 5 (.bin .mul (.reg 0) (.reg 4)) ;;
  .assign 6 (.bin .mul (.reg 1) (.reg 3)) ;;
  .assign 7 (.bin .div (.reg 5) (.reg 6)) ;;
  .assign 8 (.bin .mul (.reg 1) (.reg 2)) ;;
  .assign 9 (.bin .mul (.bin .add (.reg 7) (.const 1)) (.reg 8)) ;;
  .assign 10 (.bin .lt (.reg 5) (.reg 9))

/-- Select and check the candidate in 31 steps. A set flag proves that
the candidate equals the model threshold. -/
theorem selectRebuildThreshold_runs
    (TP : SparseCoreParams) (P : ChainParams) (N i lower upper scale : ℕ)
    {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (h0 : st.regs 0 = levelM TP P i) (h1 : st.regs 1 = P.k)
    (h2 : st.regs 2 = lower) (h3 : st.regs 3 = upper) (h4 : st.regs 4 = scale)
    (hscale : 0 < scale) (hw : 1 < 2 ^ w)
    (hlo : (lower : ℝ) / scale ≤ (Real.log ((N : ℝ) + 2)) ^ 2)
    (hhi : (Real.log ((N : ℝ) + 2)) ^ 2 ≤ (upper : ℝ) / scale)
    (hn : levelM TP P i * scale < 2 ^ w)
    (hu : P.k * upper < 2 ^ w) (hl : P.k * lower < 2 ^ w)
    (hq : levelM TP P i * scale / (P.k * upper) + 1 < 2 ^ w)
    (hc : (levelM TP P i * scale / (P.k * upper) + 1) * (P.k * lower) < 2 ^ w) :
    ∃ out, Runs w p ω selectRebuildThreshold st .normal out 31 ∧
      out.regs 7 = levelM TP P i * scale / (P.k * upper) ∧
      (out.regs 10 = 1 ↔
        levelM TP P i * scale < (out.regs 7 + 1) * (P.k * lower)) ∧
      (out.regs 10 = 1 → out.regs 7 = rebuildThresholdWord TP P N i) ∧
      (out.regs 10 = 0 ∨ out.regs 10 = 1) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  let num := levelM TP P i * scale
  let up := P.k * upper
  let lo := P.k * lower
  let q := num / up
  let cut := (q + 1) * lo
  let flag := if num < cut then 1 else 0
  let s1 := { st with regs := Function.update st.regs 5 num }
  let s2 := { s1 with regs := Function.update s1.regs 6 up }
  let s3 := { s2 with regs := Function.update s2.regs 7 q }
  let s4 := { s3 with regs := Function.update s3.regs 8 lo }
  let s5 := { s4 with regs := Function.update s4.regs 9 cut }
  let out := { s5 with regs := Function.update s5.regs 10 flag }
  have hwp : w ≠ 0 := by intro he; simp [he] at hw
  have hqw : q < 2 ^ w := (Nat.div_le_self _ _).trans_lt hn
  have hr1 : Runs w p ω (.assign 5 (.bin .mul (.reg 0) (.reg 4))) st .normal s1 4 :=
    runs_assign_iff.mpr ⟨num, by simp [Expr.eval, BinOp.eval, h0, h4, num, hn], rfl, rfl, rfl⟩
  have hr2 : Runs w p ω (.assign 6 (.bin .mul (.reg 1) (.reg 3))) s1 .normal s2 4 :=
    runs_assign_iff.mpr ⟨up, by simp [Expr.eval, BinOp.eval, s1, h1, h3, up, hu], rfl, rfl, rfl⟩
  have hr3 : Runs w p ω (.assign 7 (.bin .div (.reg 5) (.reg 6))) s2 .normal s3 4 :=
    runs_assign_iff.mpr ⟨q, by simp [Expr.eval, BinOp.eval, s2, s1, q, hqw], rfl, rfl, rfl⟩
  have hr4 : Runs w p ω (.assign 8 (.bin .mul (.reg 1) (.reg 2))) s3 .normal s4 4 :=
    runs_assign_iff.mpr ⟨lo, by simp [Expr.eval, BinOp.eval, s3, s2, s1, h1, h2, lo, hl],
      rfl, rfl, rfl⟩
  have hr5 : Runs w p ω (.assign 9 (.bin .mul (.bin .add (.reg 7) (.const 1)) (.reg 8)))
      s4 .normal s5 6 :=
    runs_assign_iff.mpr ⟨cut, by simp [Expr.eval, BinOp.eval, s4, s3, cut, lo, q, num, up, hw, hq, hc],
      rfl, rfl, rfl⟩
  have hr6 : Runs w p ω (.assign 10 (.bin .lt (.reg 5) (.reg 9))) s5 .normal out 4 :=
    runs_assign_iff.mpr ⟨flag, by
      by_cases h : num < cut <;> simp [Expr.eval, BinOp.eval, s5, s4, s3, s2, s1, flag, h, hwp],
      rfl, rfl, rfl⟩
  have hres : out.regs 7 = q := by simp [out, s5, s4, s3]
  have hf : out.regs 10 = 1 ↔ num < cut := by simp [out, flag]
  have hbit : out.regs 10 = 0 ∨ out.regs 10 = 1 := by
    by_cases h : num < cut <;> simp [out, flag, h]
  refine ⟨out, ?_, hres, by simpa only [hres] using hf, ?_, hbit, rfl, rfl⟩
  · unfold selectRebuildThreshold
    refine runs_seq_iff.mpr (Or.inr ⟨s1, 4, 26, hr1, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s2, 4, 21, hr2, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s3, 4, 16, hr3, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s4, 4, 11, hr4, ?_, rfl⟩)
    exact runs_seq_iff.mpr (Or.inr ⟨s5, 6, 4, hr5, hr6, rfl⟩)
  · intro h
    rw [hres]
    symm
    apply rebuildThresholdWord_eq_of_scaled_bounds TP P N i lower upper scale q hscale hlo hhi
    · simpa only [q, num, up, Nat.mul_assoc] using Nat.div_mul_le_self num up
    · simpa only [num, cut, lo, Nat.mul_assoc] using hf.mp h

/-- An absolute error bound on a dyadic logarithm gives an enclosure
for its square using only integer endpoint squaring. When the lower
endpoint would be negative, use zero. -/
theorem rebuildLogSquare_scaled_bounds (N approx error scale : ℕ)
    (hscale : 0 < scale)
    (herror : |(approx : ℝ) / scale - Real.log ((N : ℝ) + 2)| ≤ (error : ℝ) / scale) :
    ((approx - error : ℕ) ^ 2 : ℝ) / ((scale ^ 2 : ℕ) : ℝ) ≤
        (Real.log ((N : ℝ) + 2)) ^ 2 ∧
      (Real.log ((N : ℝ) + 2)) ^ 2 ≤
        ((approx + error : ℕ) ^ 2 : ℝ) / ((scale ^ 2 : ℕ) : ℝ) := by
  have hs : (0 : ℝ) < scale := Nat.cast_pos.mpr hscale
  have hlog : 0 ≤ Real.log ((N : ℝ) + 2) := by
    apply Real.log_nonneg
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    linarith only [hN]
  obtain ⟨hl, hu⟩ := abs_le.mp herror
  have hupper : Real.log ((N : ℝ) + 2) ≤ ((approx : ℝ) + error) / scale := by
    rw [add_div]
    linarith only [hl]
  have hlower : ((approx - error : ℕ) : ℝ) / scale ≤ Real.log ((N : ℝ) + 2) := by
    by_cases h : error ≤ approx
    · rw [Nat.cast_sub h, sub_div]
      linarith only [hu]
    · simpa only [Nat.sub_eq_zero_of_le (Nat.le_of_lt (Nat.lt_of_not_ge h)),
        Nat.cast_zero, zero_div] using hlog
  have h1 := pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) hs.le) hlower 2
  have h2 := pow_le_pow_left₀ hlog hupper 2
  constructor
  · simpa only [div_pow, Nat.cast_pow] using h1
  · simpa only [div_pow, Nat.cast_pow, Nat.cast_add] using h2

/-- Write a threshold word only when its enclosure determines the
exact floor. The target cell is in register 11. -/
@[expose] def selectAndStoreRebuildThreshold : Stmt :=
  selectRebuildThreshold ;;
    .cond (.reg 10) (.store (.reg 11) (.reg 7)) .nop

/-- The Init store preserves the threshold cell on an inconclusive
enclosure and otherwise writes the exact model threshold. -/
theorem selectAndStoreRebuildThreshold_runs
    (TP : SparseCoreParams) (P : ChainParams) (N i lower upper scale : ℕ)
    {w cell : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (h0 : st.regs 0 = levelM TP P i) (h1 : st.regs 1 = P.k)
    (h2 : st.regs 2 = lower) (h3 : st.regs 3 = upper) (h4 : st.regs 4 = scale)
    (hcell : st.regs 11 = cell)
    (hscale : 0 < scale) (hw : 1 < 2 ^ w)
    (hlo : (lower : ℝ) / scale ≤ (Real.log ((N : ℝ) + 2)) ^ 2)
    (hhi : (Real.log ((N : ℝ) + 2)) ^ 2 ≤ (upper : ℝ) / scale)
    (hn : levelM TP P i * scale < 2 ^ w)
    (hu : P.k * upper < 2 ^ w) (hl : P.k * lower < 2 ^ w)
    (hq : levelM TP P i * scale / (P.k * upper) + 1 < 2 ^ w)
    (hc : (levelM TP P i * scale / (P.k * upper) + 1) * (P.k * lower) < 2 ^ w) :
    ∃ out c, Runs w p ω selectAndStoreRebuildThreshold st .normal out c ∧
      (out.regs 10 = 0 ∧ out.mem = st.mem ∨
        out.regs 10 = 1 ∧ out.mem cell = rebuildThresholdWord TP P N i) ∧
      (∀ a ≠ cell, out.mem a = st.mem a) ∧ out.pos = st.pos ∧ c ≤ 37 := by
  obtain ⟨mid, hr, _, _, hcorrect, hbits, hmem, hpos⟩ :=
    selectRebuildThreshold_runs TP P N i lower upper scale (p := p) (ω := ω)
      h0 h1 h2 h3 h4 hscale hw hlo hhi hn hu hl hq hc
  have hmidCell : mid.regs 11 = cell := by
    have hkeep := runs_preserves_above (s := selectRebuildThreshold) (r := 11)
      (bound := 11) (by decide) rfl hr
    exact hkeep.trans hcell
  by_cases hzero : mid.regs 10 = 0
  · have hskip : Runs w p ω (.cond (.reg 10) (.store (.reg 11) (.reg 7)) .nop)
        mid .normal mid 3 :=
      runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, hzero],
        runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
    exact ⟨mid, 35, runs_seq_iff.mpr (Or.inr ⟨mid, 31, 3, hr, hskip, rfl⟩),
      Or.inl ⟨hzero, hmem⟩, fun a _ => congrFun hmem a, hpos, by decide⟩
  · have hbit : mid.regs 10 = 1 := hbits.resolve_left hzero
    let out := { mid with mem := Function.update mid.mem cell (mid.regs 7) }
    have hstore : Runs w p ω (.store (.reg 11) (.reg 7)) mid .normal out 3 :=
      runs_store_iff.mpr ⟨cell, mid.regs 7, by simp [Expr.eval, hmidCell], rfl, rfl, rfl, rfl⟩
    have hwrite : Runs w p ω (.cond (.reg 10) (.store (.reg 11) (.reg 7)) .nop)
        mid .normal out 5 :=
      runs_cond_iff.mpr ⟨1, 3, by simp [Expr.eval, hbit], hstore, rfl⟩
    exact ⟨out, 37, runs_seq_iff.mpr (Or.inr ⟨mid, 31, 5, hr, hwrite, rfl⟩),
      Or.inr ⟨hbit, by simp [out, hcorrect hbit]⟩,
      fun a ha => by simp [out, Function.update_of_ne ha, hmem], hpos, le_rfl⟩

/-- Square the lower and upper logarithm endpoints and their scale.
Registers 2 through 4 then supply the threshold search arguments. -/
@[expose] def squareRebuildLogEnclosure : Stmt :=
  .assign 12 (.bin .sub (.reg 2) (.reg 3)) ;;
  .assign 13 (.bin .add (.reg 2) (.reg 3)) ;;
  .assign 2 (.bin .mul (.reg 12) (.reg 12)) ;;
  .assign 3 (.bin .mul (.reg 13) (.reg 13)) ;;
  .assign 4 (.bin .mul (.reg 4) (.reg 4))

/-- Bounds on the squared endpoints suffice for every word operation
in the enclosure transformation. -/
theorem squareRebuildLogEnclosure_runs {w approx error scale : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (ha : st.regs 2 = approx) (he : st.regs 3 = error) (hs : st.regs 4 = scale)
    (hlo : (approx - error) ^ 2 < 2 ^ w) (hhi : (approx + error) ^ 2 < 2 ^ w)
    (hscale : scale ^ 2 < 2 ^ w) :
    ∃ out, Runs w p ω squareRebuildLogEnclosure st .normal out 24 ∧
      out.regs 2 = (approx - error) ^ 2 ∧ out.regs 3 = (approx + error) ^ 2 ∧
      out.regs 4 = scale ^ 2 ∧
      (∀ r, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 12 → r ≠ 13 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  have hself (x : ℕ) : x ≤ x ^ 2 := by
    cases x with
    | zero => decide
    | succ n =>
      rw [pow_two]
      exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have hlo' := (hself _).trans_lt hlo
  have hhi' := (hself _).trans_lt hhi
  let s1 := { st with regs := Function.update st.regs 12 (approx - error) }
  let s2 := { s1 with regs := Function.update s1.regs 13 (approx + error) }
  let s3 := { s2 with regs := Function.update s2.regs 2 ((approx - error) ^ 2) }
  let s4 := { s3 with regs := Function.update s3.regs 3 ((approx + error) ^ 2) }
  let out := { s4 with regs := Function.update s4.regs 4 (scale ^ 2) }
  have hr1 : Runs w p ω (.assign 12 (.bin .sub (.reg 2) (.reg 3))) st .normal s1 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, ha, he, hlo'], rfl, rfl, rfl⟩
  have hr2 : Runs w p ω (.assign 13 (.bin .add (.reg 2) (.reg 3))) s1 .normal s2 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, s1, ha, he, hhi'], rfl, rfl, rfl⟩
  have hr3 : Runs w p ω (.assign 2 (.bin .mul (.reg 12) (.reg 12))) s2 .normal s3 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, s2, s1, ← pow_two, hlo],
      rfl, rfl, rfl⟩
  have hr4 : Runs w p ω (.assign 3 (.bin .mul (.reg 13) (.reg 13))) s3 .normal s4 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, s3, s2, ← pow_two, hhi],
      rfl, rfl, rfl⟩
  have hr5 : Runs w p ω (.assign 4 (.bin .mul (.reg 4) (.reg 4))) s4 .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, s4, s3, s2, s1, hs, ← pow_two, hscale],
      rfl, rfl, rfl⟩
  refine ⟨out, ?_, by simp [out, s4, s3], by simp [out, s4], by simp [out],
    fun r h2 h3 h4 h12 h13 => by simp [out, s4, s3, s2, s1, h2, h3, h4, h12, h13],
    rfl, rfl⟩
  exact runs_seq_iff.mpr (Or.inr ⟨s1, 4, 19, hr1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 4, 14, hr2,
      runs_seq_iff.mpr (Or.inr ⟨s3, 4, 9, hr3,
        runs_seq_iff.mpr (Or.inr ⟨s4, 4, 4, hr4, hr5, rfl⟩), rfl⟩), rfl⟩), rfl⟩)

/-- Square the logarithm enclosure and install the threshold if it
determines a unique floor. -/
@[expose] def initRebuildThresholdFromLog : Stmt :=
  squareRebuildLogEnclosure ;; selectAndStoreRebuildThreshold

/-- An input approximation and its absolute error suffice to run the
checked threshold store. The flag records whether the floor was resolved. -/
theorem initRebuildThresholdFromLog_runs
    (TP : SparseCoreParams) (P : ChainParams) (N i approx error scale : ℕ)
    {w cell : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (h0 : st.regs 0 = levelM TP P i) (h1 : st.regs 1 = P.k)
    (h2 : st.regs 2 = approx) (h3 : st.regs 3 = error) (h4 : st.regs 4 = scale)
    (hcell : st.regs 11 = cell)
    (hscale : 0 < scale) (hw : 1 < 2 ^ w)
    (herror : |(approx : ℝ) / scale - Real.log ((N : ℝ) + 2)| ≤ (error : ℝ) / scale) :
    let lower := (approx - error) ^ 2
    let upper := (approx + error) ^ 2
    let scaleSq := scale ^ 2
    let num := levelM TP P i * scaleSq
    let q := num / (P.k * upper)
    lower < 2 ^ w → upper < 2 ^ w → scaleSq < 2 ^ w →
    num < 2 ^ w → P.k * upper < 2 ^ w → P.k * lower < 2 ^ w →
    q + 1 < 2 ^ w → (q + 1) * (P.k * lower) < 2 ^ w →
    ∃ out c, Runs w p ω initRebuildThresholdFromLog st .normal out c ∧
      (out.regs 10 = 0 ∧ out.mem = st.mem ∨
        out.regs 10 = 1 ∧ out.mem cell = rebuildThresholdWord TP P N i) ∧
      (∀ a ≠ cell, out.mem a = st.mem a) ∧ out.pos = st.pos ∧ c ≤ 62 := by
  dsimp only
  intro hlo hhi hs hn hu hl hq hc
  obtain ⟨mid, hr, hlower, hupper, hscaleSq, hkeep, hmem, hpos⟩ :=
    squareRebuildLogEnclosure_runs (ω := ω) (p := p) h2 h3 h4 hlo hhi hs
  obtain ⟨hbelow, habove⟩ := rebuildLogSquare_scaled_bounds N approx error scale hscale herror
  have keep (r : ℕ) (hr : r = 0 ∨ r = 1 ∨ r = 11) : mid.regs r = st.regs r :=
    hkeep r (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨out, c, hrun, hresult, hframe, hpos', hcost⟩ :=
    selectAndStoreRebuildThreshold_runs TP P N i _ _ _ (ω := ω)
      ((keep 0 (by decide)).trans h0) ((keep 1 (by decide)).trans h1)
      hlower hupper hscaleSq ((keep 11 (by decide)).trans hcell)
      (pow_pos hscale _) hw
      (by simpa only [Nat.cast_pow] using hbelow)
      (by simpa only [Nat.cast_pow, Nat.cast_add] using habove) hn hu hl hq hc
  refine ⟨out, c + 25, runs_seq_iff.mpr (Or.inr ⟨mid, 24, c, hr, hrun, by omega⟩), ?_,
    fun a ha => (hframe a ha).trans (congrFun hmem a), hpos'.trans hpos, by omega⟩
  rcases hresult with ⟨hf, hmem'⟩ | hwritten
  · exact Or.inl ⟨hf, hmem'.trans hmem⟩
  · exact Or.inr hwritten

/-- Select the integer rebuild threshold for Algorithm 2 (page 28).
Register 0 holds the rounded level edge bound, register 1 holds the
branch count, and register 3 holds the ceiling binary vertex logarithm.
The budget is returned in register 7. -/
@[expose] def selectIntegerRebuildThreshold : Stmt :=
  .assign 6 (.bin .mul (.bin .mul (.const 3) (.reg 1))
    (.bin .mul (.reg 3) (.reg 3))) ;;
  .assign 7 (.bin .div (.reg 0) (.reg 6))

/-- Integer division produces the conservative rebuild budget without an
enclosure test. The logarithm is shared by all levels. -/
theorem selectIntegerRebuildThreshold_runs
    {w edges branches vertices : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (h0 : st.regs 0 = edges) (h1 : st.regs 1 = branches)
    (h3 : st.regs 3 = Nat.clog 2 (vertices + 2))
    (hk : 0 < branches) (hedges : edges < 2 ^ w)
    (hroom : 3 * branches * Nat.clog 2 (vertices + 2) ^ 2 < 2 ^ w) :
    ∃ out, Runs w p ω selectIntegerRebuildThreshold st .normal out 13 ∧
      out.regs 7 = concreteRebuildCount (3 * branches) edges vertices ∧
      out.mem = st.mem ∧ (∀ r, r ≠ 6 → r ≠ 7 → out.regs r = st.regs r) := by
  let b := Nat.clog 2 (vertices + 2)
  let D := 3 * branches * b ^ 2
  have hb : 0 < b := Nat.clog_pos Nat.one_lt_two (by omega)
  have h3k : 0 < 3 * branches := by omega
  have hD : D < 2 ^ w := hroom
  have hleft : 3 * branches < 2 ^ w :=
    (Nat.le_mul_of_pos_right _ (pow_pos hb _)).trans_lt hD
  have hright : b ^ 2 < 2 ^ w :=
    (Nat.le_mul_of_pos_left _ h3k).trans_lt hD
  have hthree : 3 < 2 ^ w := (Nat.le_mul_of_pos_right _ hk).trans_lt hleft
  let mid := {st with regs := Function.update st.regs 6 D}
  let out := {mid with regs := Function.update mid.regs 7 (edges / D)}
  have r₁ : Runs w p ω
      (.assign 6 (.bin .mul (.bin .mul (.const 3) (.reg 1)) (.bin .mul (.reg 3) (.reg 3))))
      st .normal mid 8 := by
    refine runs_assign_iff.mpr ⟨D, ?_, rfl, rfl, rfl⟩
    have hbword : b * b < 2 ^ w := by simpa only [pow_two] using hright
    have hprod : 3 * branches * (b * b) < 2 ^ w := by simpa only [D, pow_two] using hD
    simp [Expr.eval, hthree, h1, h3, BinOp.eval, hleft, D, pow_two, b,
      show Nat.clog 2 (vertices + 2) * Nat.clog 2 (vertices + 2) < 2 ^ w from hbword,
      show 3 * branches * (Nat.clog 2 (vertices + 2) * Nat.clog 2 (vertices + 2)) <
        2 ^ w from hprod]
  have r₂ : Runs w p ω (.assign 7 (.bin .div (.reg 0) (.reg 6))) mid .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, mid, h0,
      (Nat.div_le_self edges D).trans_lt hedges], rfl, rfl, rfl⟩
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 8, 4, r₁, r₂, rfl⟩), ?_, rfl, ?_⟩
  · simp [out, concreteRebuildCount, D, b]
  · intro r h6 h7
    simp [out, mid, h6, h7]

/-- Compute the integer rebuild budget and write it to the cell in
register 11. This store needs no certification branch. -/
@[expose] def selectAndStoreIntegerRebuildThreshold : Stmt :=
  selectIntegerRebuildThreshold ;; .store (.reg 11) (.reg 7)

/-- The threshold cell receives the exact integer budget in 17 steps.
All other cells are preserved. -/
theorem selectAndStoreIntegerRebuildThreshold_runs
    {w edges branches vertices cell : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (h0 : st.regs 0 = edges) (h1 : st.regs 1 = branches)
    (h3 : st.regs 3 = Nat.clog 2 (vertices + 2)) (h11 : st.regs 11 = cell)
    (hk : 0 < branches) (hedges : edges < 2 ^ w)
    (hroom : 3 * branches * Nat.clog 2 (vertices + 2) ^ 2 < 2 ^ w) :
    ∃ out, Runs w p ω selectAndStoreIntegerRebuildThreshold st .normal out 17 ∧
      out.mem = Function.update st.mem cell (concreteRebuildCount (3 * branches) edges vertices) ∧
      (∀ r, r ≠ 6 → r ≠ 7 → out.regs r = st.regs r) := by
  obtain ⟨mid, hr, hval, hmem, hregs⟩ :=
    selectIntegerRebuildThreshold_runs (p := p) (ω := ω) h0 h1 h3 hk hedges hroom
  have hcell : mid.regs 11 = cell := (hregs 11 (by decide) (by decide)).trans h11
  let value := concreteRebuildCount (3 * branches) edges vertices
  let out := {mid with mem := Function.update mid.mem cell value}
  have hs : Runs w p ω (.store (.reg 11) (.reg 7)) mid .normal out 3 :=
    runs_store_iff.mpr ⟨cell, value, congrArg some hcell, congrArg some hval,
      rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 13, 3, hr, hs, rfl⟩),
    by simp [out, hmem, value], hregs⟩

/-- A stored level budget remains within the real threshold and retains
the lower bound on the count that triggers a rebuild. -/
theorem selectAndStoreIntegerRebuildThreshold_level_runs
    (TP : SparseCoreParams) (P : ChainParams) (a scale level vertices : ℕ)
    {w cell : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hs : 0 < scale) (hi : level ≤ P.d)
    (hγ : 1 ≤ TP.γ_ℓ (P.M₀ ^ 2))
    (hlo : TP.γ_ℓ (P.M₀ ^ 2) ≤ (a : ℝ) / scale)
    (hhi : (a : ℝ) / scale ≤ TP.γ_ℓ (P.M₀ ^ 2) + 1 / ((P.d : ℝ) + 1))
    (h0 : st.regs 0 = concreteLevelEdgeBound P.M₀ P.k a scale level)
    (h1 : st.regs 1 = P.k) (h3 : st.regs 3 = Nat.clog 2 (vertices + 2))
    (h11 : st.regs 11 = cell)
    (hedges : concreteLevelEdgeBound P.M₀ P.k a scale level < 2 ^ w)
    (hroom : 3 * P.k * Nat.clog 2 (vertices + 2) ^ 2 < 2 ^ w) :
    let count := concreteLevelRebuildCount P.M₀ P.k a scale level vertices
    let budget := SparseCoreTool.updateThreshold P.k (levelM TP P level) vertices
    ∃ out, Runs w p ω selectAndStoreIntegerRebuildThreshold st .normal out 17 ∧
      out.mem = Function.update st.mem cell count ∧
      (∀ r, r ≠ 6 → r ≠ 7 → out.regs r = st.regs r) ∧
      (out.mem cell : ℝ) ≤ budget ∧ budget ≤ 48 * ((out.mem cell : ℝ) + 1) := by
  dsimp only
  obtain ⟨out, hr, hmem, hregs⟩ :=
    selectAndStoreIntegerRebuildThreshold_runs (p := p) (ω := ω) h0 h1 h3 h11 P.hk hedges hroom
  have hval : out.mem cell = concreteLevelRebuildCount P.M₀ P.k a scale level vertices := by
    rw [hmem, Function.update_self]
    rfl
  refine ⟨out, hr, hmem, hregs, ?_⟩
  rw [hval]
  exact concreteLevelRebuildCount_bounds TP P a scale level vertices hs hi hγ hlo hhi

/-- Read the current numerator and denominator of a rounded level size
from registers 8 and 9 and write its ceiling to register 0. -/
@[expose] def selectIntegerLevelEdgeBound : Stmt :=
  .assign 0 (.bin .div
    (.bin .sub (.bin .add (.reg 8) (.reg 9)) (.const 1)) (.reg 9))

/-- The level edge bound is obtained by exact ceiling division of the
current integer powers. No logarithm enclosure is inspected here. -/
theorem selectIntegerLevelEdgeBound_runs
    {w edges branches a scale level : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (h8 : st.regs 8 = edges * a ^ (level + 1))
    (h9 : st.regs 9 = scale ^ (level + 1) * branches ^ level)
    (hword : 1 < 2 ^ w) (hroom : st.regs 8 + st.regs 9 < 2 ^ w) :
    ∃ out, Runs w p ω selectIntegerLevelEdgeBound st .normal out 8 ∧
      out.regs 0 = concreteLevelEdgeBound edges branches a scale level ∧
      out.mem = st.mem ∧ (∀ r, r ≠ 0 → out.regs r = st.regs r) := by
  let t := st.regs 8 + st.regs 9
  let v := (t - 1) / st.regs 9
  let out := {st with regs := Function.update st.regs 0 v}
  have hsub : t - 1 < 2 ^ w := (Nat.sub_le _ _).trans_lt hroom
  have hv : v < 2 ^ w := (Nat.div_le_self _ _).trans_lt hsub
  have hr : Runs w p ω selectIntegerLevelEdgeBound st .normal out 8 :=
    runs_assign_iff.mpr ⟨v, by simp [Expr.eval, BinOp.eval,
      hword, hroom, show st.regs 8 + st.regs 9 - 1 < 2 ^ w from hsub,
      show (st.regs 8 + st.regs 9 - 1) / st.regs 9 < 2 ^ w from hv, v, t], rfl, rfl, rfl⟩
  refine ⟨out, hr, ?_, rfl, ?_⟩
  · simp [out, v, t, h8, h9, concreteLevelEdgeBound]
  · intro r hr
    simp [out, hr]

/-- Advance the exact powers in the level edge bound. Registers 12 and
13 hold the numerator and the product of the scale and branch count. -/
@[expose] def advanceIntegerLevelEdgeBound : Stmt :=
  .assign 8 (.bin .mul (.reg 8) (.reg 12)) ;;
  .assign 9 (.bin .mul (.reg 9) (.reg 13))

/-- One advance obtains the powers for the next level in nine steps. -/
theorem advanceIntegerLevelEdgeBound_runs
    {w edges branches a scale level : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (h8 : st.regs 8 = edges * a ^ (level + 1))
    (h9 : st.regs 9 = scale ^ (level + 1) * branches ^ level)
    (h12 : st.regs 12 = a) (h13 : st.regs 13 = scale * branches)
    (ht : edges * a ^ (level + 2) < 2 ^ w)
    (hb : scale ^ (level + 2) * branches ^ (level + 1) < 2 ^ w) :
    ∃ out, Runs w p ω advanceIntegerLevelEdgeBound st .normal out 9 ∧
      out.regs 8 = edges * a ^ (level + 2) ∧
      out.regs 9 = scale ^ (level + 2) * branches ^ (level + 1) ∧
      out.mem = st.mem ∧ (∀ r, r ≠ 8 → r ≠ 9 → out.regs r = st.regs r) := by
  let top := edges * a ^ (level + 2)
  let bottom := scale ^ (level + 2) * branches ^ (level + 1)
  let mid := {st with regs := Function.update st.regs 8 top}
  let out := {mid with regs := Function.update mid.regs 9 bottom}
  have et : st.regs 8 * st.regs 12 = top := by
    rw [h8, h12]
    simp only [top, pow_succ a (level + 1), Nat.mul_assoc]
  have eb : st.regs 9 * st.regs 13 = bottom := by
    rw [h9, h13]
    simp only [bottom, pow_succ scale (level + 1), pow_succ branches level]
    ac_rfl
  have r₁ : Runs w p ω (.assign 8 (.bin .mul (.reg 8) (.reg 12))) st .normal mid 4 :=
    runs_assign_iff.mpr ⟨top, by simp [Expr.eval, BinOp.eval, et, show top < 2 ^ w from ht],
      rfl, rfl, rfl⟩
  have r₂ : Runs w p ω (.assign 9 (.bin .mul (.reg 9) (.reg 13))) mid .normal out 4 :=
    runs_assign_iff.mpr ⟨bottom, by simp [Expr.eval, BinOp.eval, mid, eb, show bottom < 2 ^ w from hb],
      rfl, rfl, rfl⟩
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 4, 4, r₁, r₂, rfl⟩), ?_, ?_, rfl, ?_⟩
  · simp [out, mid, top]
  · simp [out, bottom]
  · intro r hr₈ hr₉
    simp [out, mid, hr₈, hr₉]

/-- Compute the rounded level size and write that level's rebuild budget. -/
@[expose] def writeIntegerLevelThreshold : Stmt :=
  selectIntegerLevelEdgeBound ;; selectAndStoreIntegerRebuildThreshold

/-- One threshold table cell is filled from the current integer powers
and the shared binary vertex logarithm in 26 steps. -/
theorem writeIntegerLevelThreshold_runs
    {w edges branches a scale level vertices cell : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (h8 : st.regs 8 = edges * a ^ (level + 1))
    (h9 : st.regs 9 = scale ^ (level + 1) * branches ^ level)
    (h1 : st.regs 1 = branches) (h3 : st.regs 3 = Nat.clog 2 (vertices + 2))
    (h11 : st.regs 11 = cell)
    (hk : 0 < branches) (hword : 1 < 2 ^ w) (hroom : st.regs 8 + st.regs 9 < 2 ^ w)
    (hden : 3 * branches * Nat.clog 2 (vertices + 2) ^ 2 < 2 ^ w) :
    ∃ out, Runs w p ω writeIntegerLevelThreshold st .normal out 26 ∧
      out.mem = Function.update st.mem cell
        (concreteLevelRebuildCount edges branches a scale level vertices) ∧
      (∀ r, r ≠ 0 → r ≠ 6 → r ≠ 7 → out.regs r = st.regs r) := by
  obtain ⟨mid, hr, hsize, hm, hf⟩ :=
    selectIntegerLevelEdgeBound_runs (p := p) (ω := ω) h8 h9 hword hroom
  have hfit : concreteLevelEdgeBound edges branches a scale level < 2 ^ w := by
    change ((edges * a ^ (level + 1) + scale ^ (level + 1) * branches ^ level - 1) /
      (scale ^ (level + 1) * branches ^ level)) < 2 ^ w
    rw [← h8, ← h9]
    exact (Nat.div_le_self _ _).trans_lt ((Nat.sub_le _ _).trans_lt hroom)
  obtain ⟨out, hr', hm', hf'⟩ :=
    selectAndStoreIntegerRebuildThreshold_runs (p := p) (ω := ω) hsize
      ((hf 1 (by decide)).trans h1) ((hf 3 (by decide)).trans h3)
      ((hf 11 (by decide)).trans h11) hk hfit hden
  rw [hm] at hm'
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 8, 17, hr, hr', rfl⟩), hm',
    fun r h0 h6 h7 => (hf' r h6 h7).trans (hf r h0)⟩

/-- Advance to the next level and write its integer threshold. Registers
54 and 11 hold the current level and table address. -/
@[expose] def writeIntegerNextThreshold : Stmt :=
  advanceIntegerLevelEdgeBound ;;
  .assign 54 (.bin .add (.reg 54) (.const 1)) ;;
  .assign 11 (.bin .add (.reg 11) (.const 1)) ;;
  writeIntegerLevelThreshold

/-- One iteration writes the next threshold and preserves the powers
and indices needed for the following level. -/
theorem writeIntegerNextThreshold_runs
    {w edges branches a scale level vertices cell : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (h8 : st.regs 8 = edges * a ^ (level + 1))
    (h9 : st.regs 9 = scale ^ (level + 1) * branches ^ level)
    (h12 : st.regs 12 = a) (h13 : st.regs 13 = scale * branches)
    (h1 : st.regs 1 = branches) (h3 : st.regs 3 = Nat.clog 2 (vertices + 2))
    (h54 : st.regs 54 = level) (h11 : st.regs 11 = cell)
    (hk : 0 < branches) (hword : 1 < 2 ^ w)
    (hlevel : level + 1 < 2 ^ w) (hcell : cell + 1 < 2 ^ w)
    (hroom : edges * a ^ (level + 2) + scale ^ (level + 2) * branches ^ (level + 1) < 2 ^ w)
    (hden : 3 * branches * Nat.clog 2 (vertices + 2) ^ 2 < 2 ^ w) :
    ∃ out, Runs w p ω writeIntegerNextThreshold st .normal out 46 ∧
      out.mem = Function.update st.mem (cell + 1)
        (concreteLevelRebuildCount edges branches a scale (level + 1) vertices) ∧
      out.regs 8 = edges * a ^ (level + 2) ∧
      out.regs 9 = scale ^ (level + 2) * branches ^ (level + 1) ∧
      out.regs 54 = level + 1 ∧ out.regs 11 = cell + 1 ∧
      (∀ r, r ∉ [0, 6, 7, 8, 9, 11, 54] → out.regs r = st.regs r) := by
  obtain ⟨mid, hr, e8, e9, hm, hf⟩ :=
    advanceIntegerLevelEdgeBound_runs (w := w) (p := p) (ω := ω) h8 h9 h12 h13 (by omega) (by omega)
  let next := {mid with regs := Function.update mid.regs 54 (level + 1)}
  let ready := {next with regs := Function.update next.regs 11 (cell + 1)}
  have r₁ : Runs w p ω (.assign 54 (.bin .add (.reg 54) (.const 1))) mid .normal next 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hword, hlevel,
      (hf 54 (by decide) (by decide)).trans h54], rfl, rfl, rfl⟩
  have r₂ : Runs w p ω (.assign 11 (.bin .add (.reg 11) (.const 1))) next .normal ready 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, next, hword, hcell,
      (hf 11 (by decide) (by decide)).trans h11], rfl, rfl, rfl⟩
  have keep (r : ℕ) (h8' : r ≠ 8) (h9' : r ≠ 9) (h11' : r ≠ 11) (h54' : r ≠ 54) :
      ready.regs r = st.regs r := by simp [ready, next, h11', h54', hf r h8' h9']
  obtain ⟨out, hr', hm', hf'⟩ :=
    writeIntegerLevelThreshold_runs (p := p) (ω := ω) (level := level + 1) (cell := cell + 1)
      (by simpa [ready, next] using e8) (by simpa [ready, next] using e9)
      ((keep 1 (by decide) (by decide) (by decide) (by decide)).trans h1)
      ((keep 3 (by decide) (by decide) (by decide) (by decide)).trans h3)
      (by simp [ready]) hk hword (by simpa [ready, next, e8, e9] using hroom) hden
  change ready.mem = st.mem at hm
  rw [hm] at hm'
  refine ⟨out, ?_, hm', ?_, ?_, ?_, ?_, ?_⟩
  · refine runs_seq_iff.mpr (Or.inr ⟨mid, 9, 36, hr, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨next, 4, 31, r₁, ?_, rfl⟩)
    exact runs_seq_iff.mpr (Or.inr ⟨ready, 4, 26, r₂, hr', rfl⟩)
  · simp [hf' 8 (by decide) (by decide) (by decide), ready, next, e8]
  · simp [hf' 9 (by decide) (by decide) (by decide), ready, next, e9]
  · simp [hf' 54 (by decide) (by decide) (by decide), ready, next]
  · simp [hf' 11 (by decide) (by decide) (by decide), ready]
  · intro r h
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    exact (hf' r h.1 h.2.1 h.2.2.1).trans
      (keep r h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2)

/-- Fill the remaining integer thresholds through the last level in
register 56. The current level has already been written. -/
@[expose] def writeIntegerThresholdTail : Stmt :=
  .loop (.bin .lt (.reg 54) (.reg 56)) writeIntegerNextThreshold

/-- The loop extends a correct prefix to the last level and preserves
memory outside the table. Each additional level costs 50 steps. -/
theorem writeIntegerThresholdTail_runs
    {w edges branches a scale vertices base last : ℕ} {p : Program} {ω : ℕ → Bool}
    (hk : 0 < branches) (hword : 1 < 2 ^ w) (hbase : base + last < 2 ^ w)
    (hroom : ∀ j ≤ last, edges * a ^ (j + 1) + scale ^ (j + 1) * branches ^ j < 2 ^ w)
    (hden : 3 * branches * Nat.clog 2 (vertices + 2) ^ 2 < 2 ^ w)
    {i : ℕ} {st : State} (hi : i ≤ last)
    (h8 : st.regs 8 = edges * a ^ (i + 1))
    (h9 : st.regs 9 = scale ^ (i + 1) * branches ^ i)
    (h12 : st.regs 12 = a) (h13 : st.regs 13 = scale * branches)
    (h1 : st.regs 1 = branches) (h3 : st.regs 3 = Nat.clog 2 (vertices + 2))
    (h54 : st.regs 54 = i) (h56 : st.regs 56 = last) (h11 : st.regs 11 = base + i)
    (hprefix : ∀ j ≤ i, st.mem (base + j) =
      concreteLevelRebuildCount edges branches a scale j vertices) :
    ∃ out, Runs w p ω writeIntegerThresholdTail st .normal out (50 * (last - i) + 4) ∧
      (∀ j ≤ last, out.mem (base + j) =
        concreteLevelRebuildCount edges branches a scale j vertices) ∧
      (∀ x, x < base ∨ base + last < x → out.mem x = st.mem x) ∧
      (∀ r, r ∉ [0, 6, 7, 8, 9, 11, 54] → out.regs r = st.regs r) := by
  by_cases hlt : i < last
  · have hj : i + 1 ≤ last := Nat.succ_le_of_lt hlt
    obtain ⟨mid, hr, hm, e8, e9, e54, e11, hf⟩ :=
      writeIntegerNextThreshold_runs (w := w) (p := p) (ω := ω)
        h8 h9 h12 h13 h1 h3 h54 h11 hk hword (by omega) (by omega)
        (hroom (i + 1) hj) hden
    have hpref : ∀ j ≤ i + 1, mid.mem (base + j) =
        concreteLevelRebuildCount edges branches a scale j vertices := by
      intro j hj'
      by_cases he : j = i + 1
      · subst j
        rw [hm, ← Nat.add_assoc, Function.update_self]
      · rw [hm, Function.update_of_ne (by omega)]
        exact hprefix j (by omega)
    obtain ⟨out, hr', hp, hframe, hregs⟩ :=
      writeIntegerThresholdTail_runs hk hword hbase hroom hden hj e8 e9
        ((hf 12 (by decide)).trans h12) ((hf 13 (by decide)).trans h13)
        ((hf 1 (by decide)).trans h1) ((hf 3 (by decide)).trans h3)
        e54 ((hf 56 (by decide)).trans h56) (by simpa only [Nat.add_assoc] using e11) hpref
    have he : Expr.eval w st (.bin .lt (.reg 54) (.reg 56)) = some 1 := by
      simp [Expr.eval, BinOp.eval, h54, h56, hlt, hword]
    refine ⟨out, ?_, hp, ?_, fun r h => (hregs r h).trans (hf r h)⟩
    · exact runs_loop_iff.mpr (Or.inr (Or.inr
        ⟨1, mid, 46, 50 * (last - (i + 1)) + 4, he, by decide, hr, hr', by
          simp [Expr.size]; omega⟩))
    · intro x hx
      rw [hframe x hx, hm, Function.update_of_ne]
      rcases hx with hx | hx <;> omega
  · have heq : i = last := by omega
    have he : Expr.eval w st (.bin .lt (.reg 54) (.reg 56)) = some 0 := by
      simp [Expr.eval, BinOp.eval, h54, h56, hlt, show 0 < 2 ^ w by omega]
    refine ⟨st, ?_, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    · exact runs_loop_iff.mpr (Or.inl ⟨he, rfl, rfl, by simp [Expr.size, heq]⟩)
    · simpa only [heq] using hprefix
termination_by last - i
decreasing_by omega

/-- Write the level-zero threshold and fill the table through the last level. -/
@[expose] def writeIntegerThresholdTable : Stmt :=
  writeIntegerLevelThreshold ;; writeIntegerThresholdTail

/-- Given the shared logarithm and the initial powers, Init writes every
threshold in linear time in the number of levels. -/
theorem writeIntegerThresholdTable_runs
    {w edges branches a scale vertices base last : ℕ} {p : Program} {ω : ℕ → Bool}
    {st : State}
    (hk : 0 < branches) (hword : 1 < 2 ^ w) (hbase : base + last < 2 ^ w)
    (hroom : ∀ j ≤ last, edges * a ^ (j + 1) + scale ^ (j + 1) * branches ^ j < 2 ^ w)
    (hden : 3 * branches * Nat.clog 2 (vertices + 2) ^ 2 < 2 ^ w)
    (h8 : st.regs 8 = edges * a) (h9 : st.regs 9 = scale)
    (h12 : st.regs 12 = a) (h13 : st.regs 13 = scale * branches)
    (h1 : st.regs 1 = branches) (h3 : st.regs 3 = Nat.clog 2 (vertices + 2))
    (h54 : st.regs 54 = 0) (h56 : st.regs 56 = last) (h11 : st.regs 11 = base) :
    ∃ out, Runs w p ω writeIntegerThresholdTable st .normal out (50 * last + 31) ∧
      (∀ j ≤ last, out.mem (base + j) =
        concreteLevelRebuildCount edges branches a scale j vertices) ∧
      (∀ x, x < base ∨ base + last < x → out.mem x = st.mem x) ∧
      (∀ r, r ∉ [0, 6, 7, 8, 9, 11, 54] → out.regs r = st.regs r) := by
  obtain ⟨mid, hr, hm, hf⟩ :=
    writeIntegerLevelThreshold_runs (w := w) (p := p) (ω := ω) (level := 0)
      (by simpa using h8) (by simpa using h9) h1 h3 h11 hk hword
      (by simpa [h8, h9] using hroom 0 (Nat.zero_le _)) hden
  have keep (r : ℕ) (h0 : r ≠ 0 := by decide) (h6 : r ≠ 6 := by decide)
      (h7 : r ≠ 7 := by decide) := hf r h0 h6 h7
  have hprefix : ∀ j ≤ 0, mid.mem (base + j) =
      concreteLevelRebuildCount edges branches a scale j vertices := by
    intro j hj
    have he : j = 0 := by omega
    subst j
    simp [hm]
  obtain ⟨out, hr', hp, hframe, hregs⟩ :=
    writeIntegerThresholdTail_runs (p := p) (ω := ω) hk hword hbase hroom hden (Nat.zero_le _)
      (by simpa using (keep 8).trans h8) (by simpa using (keep 9).trans h9)
      ((keep 12).trans h12) ((keep 13).trans h13) ((keep 1).trans h1)
      ((keep 3).trans h3) ((keep 54).trans h54) ((keep 56).trans h56)
      (by simpa using (keep 11).trans h11) hprefix
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 26, _, hr, hr', by omega⟩), hp, ?_, ?_⟩
  · intro x hx
    rw [hframe x hx, hm, Function.update_of_ne]
    rcases hx with hx | hx <;> omega
  · intro r h
    have hh := h
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hh
    exact (hregs r h).trans (hf r hh.1 hh.2.1 hh.2.2.1)

/-- Prepare the initial powers and reuse the bucket stage's binary
vertex logarithm. The table header provides the base and branch count. -/
@[expose] def prepareIntegerThresholdTable : Stmt :=
  .assign 1 (.reg 55) ;;
  .assign 3 (.reg 14) ;;
  .assign 8 (.bin .mul (.reg 22) (.reg 12)) ;;
  .assign 9 (.reg 4) ;;
  .assign 11 (.reg 53) ;;
  .assign 13 (.bin .mul (.reg 4) (.reg 1))

/-- The table writer receives the level-zero powers and inputs in 21 steps. -/
theorem prepareIntegerThresholdTable_runs
    {w edges branches a scale vertices base : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (h22 : st.regs 22 = edges) (h12 : st.regs 12 = a) (h4 : st.regs 4 = scale)
    (h14 : st.regs 14 = Nat.clog 2 (vertices + 2))
    (h53 : st.regs 53 = base) (h55 : st.regs 55 = branches)
    (ha : edges * a < 2 ^ w) (hs : scale * branches < 2 ^ w) :
    ∃ out, Runs w p ω prepareIntegerThresholdTable st .normal out 21 ∧
      out.regs 1 = branches ∧ out.regs 3 = Nat.clog 2 (vertices + 2) ∧
      out.regs 8 = edges * a ∧ out.regs 9 = scale ∧ out.regs 11 = base ∧
      out.regs 13 = scale * branches ∧ out.mem = st.mem ∧
      (∀ r, r ∉ [1, 3, 8, 9, 11, 13] → out.regs r = st.regs r) := by
  let s₁ := {st with regs := Function.update st.regs 1 branches}
  let s₂ := {s₁ with regs := Function.update s₁.regs 3 (Nat.clog 2 (vertices + 2))}
  let s₃ := {s₂ with regs := Function.update s₂.regs 8 (edges * a)}
  let s₄ := {s₃ with regs := Function.update s₃.regs 9 scale}
  let s₅ := {s₄ with regs := Function.update s₄.regs 11 base}
  let out := {s₅ with regs := Function.update s₅.regs 13 (scale * branches)}
  have r₁ : Runs w p ω (.assign 1 (.reg 55)) st .normal s₁ 2 :=
    runs_assign_iff.mpr ⟨_, congrArg some h55, rfl, rfl, rfl⟩
  have r₂ : Runs w p ω (.assign 3 (.reg 14)) s₁ .normal s₂ 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s₁, h14], rfl, rfl, rfl⟩
  have r₃ : Runs w p ω (.assign 8 (.bin .mul (.reg 22) (.reg 12))) s₂ .normal s₃ 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, s₂, s₁, h22, h12, ha],
      rfl, rfl, rfl⟩
  have r₄ : Runs w p ω (.assign 9 (.reg 4)) s₃ .normal s₄ 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s₃, s₂, s₁, h4], rfl, rfl, rfl⟩
  have r₅ : Runs w p ω (.assign 11 (.reg 53)) s₄ .normal s₅ 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s₄, s₃, s₂, s₁, h53], rfl, rfl, rfl⟩
  have r₆ : Runs w p ω (.assign 13 (.bin .mul (.reg 4) (.reg 1))) s₅ .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, s₅, s₄, s₃, s₂, s₁, h4, hs],
      rfl, rfl, rfl⟩
  refine ⟨out, ?_, by simp [out, s₅, s₄, s₃, s₂, s₁], by simp [out, s₅, s₄, s₃, s₂],
    by simp [out, s₅, s₄, s₃], by simp [out, s₅, s₄], by simp [out, s₅],
    by simp [out], rfl, ?_⟩
  · refine runs_seq_iff.mpr (Or.inr ⟨s₁, 2, 18, r₁, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s₂, 2, 15, r₂, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s₃, 4, 10, r₃, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s₄, 2, 7, r₄, ?_, rfl⟩)
    exact runs_seq_iff.mpr (Or.inr ⟨s₅, 2, 4, r₅, r₆, rfl⟩)
  · intro r hz
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    rcases hz with ⟨h₁, h₃, h₈, h₉, h₁₁, h₁₃⟩
    simp [out, s₅, s₄, s₃, s₂, s₁, h₁, h₃, h₈, h₉, h₁₁, h₁₃]

/-- Initialize the reserved threshold table from the growth-factor
numerator, scale and the cached vertex logarithm. -/
@[expose] def initIntegerThresholdTable : Stmt :=
  prepareIntegerThresholdTable ;; writeIntegerThresholdTable

/-- The prepared table contains all integer rebuild counts and preserves
memory outside the reserved cells. -/
theorem initIntegerThresholdTable_runs
    {w edges branches a scale vertices base last : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hk : 0 < branches) (hword : 1 < 2 ^ w) (hbase : base + last < 2 ^ w)
    (hroom : ∀ j ≤ last, edges * a ^ (j + 1) + scale ^ (j + 1) * branches ^ j < 2 ^ w)
    (hden : 3 * branches * Nat.clog 2 (vertices + 2) ^ 2 < 2 ^ w)
    (h22 : st.regs 22 = edges) (h12 : st.regs 12 = a) (h4 : st.regs 4 = scale)
    (h14 : st.regs 14 = Nat.clog 2 (vertices + 2))
    (h53 : st.regs 53 = base) (h55 : st.regs 55 = branches)
    (h54 : st.regs 54 = 0) (h56 : st.regs 56 = last)
    (hs : scale * branches < 2 ^ w) :
    ∃ out, Runs w p ω initIntegerThresholdTable st .normal out (50 * last + 53) ∧
      (∀ j ≤ last, out.mem (base + j) =
        concreteLevelRebuildCount edges branches a scale j vertices) ∧
      (∀ x, x < base ∨ base + last < x → out.mem x = st.mem x) ∧
      (∀ r, r ∉ [0, 1, 3, 6, 7, 8, 9, 11, 13, 54] → out.regs r = st.regs r) := by
  have ha : edges * a < 2 ^ w := by
    have hzero := hroom 0 (Nat.zero_le last)
    simp only [Nat.zero_add, pow_one, pow_zero, mul_one] at hzero
    omega
  obtain ⟨mid, hr, e1, e3, e8, e9, e11, e13, hm, hf⟩ :=
    prepareIntegerThresholdTable_runs (p := p) (ω := ω) h22 h12 h4 h14 h53 h55 ha hs
  obtain ⟨out, hr', hp, hf', hregs⟩ :=
    writeIntegerThresholdTable_runs hk hword hbase hroom hden e8 e9
      ((hf 12 (by decide)).trans h12) e13 e1 e3
      ((hf 54 (by decide)).trans h54) ((hf 56 (by decide)).trans h56) e11
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 21, _, hr, hr', by omega⟩), hp,
    fun x hx => (hf' x hx).trans (congrFun hm x), ?_⟩
  intro r h
  have hwrite : ([0, 6, 7, 8, 9, 11, 54] : List ℕ).Sublist [0, 1, 3, 6, 7, 8, 9, 11, 13, 54] := by decide
  have hprep : ([1, 3, 8, 9, 11, 13] : List ℕ).Sublist [0, 1, 3, 6, 7, 8, 9, 11, 13, 54] := by decide
  exact (hregs r (fun hr => h (hwrite.subset hr))).trans (hf r (fun hr => h (hprep.subset hr)))

/-- Round the upper growth endpoint in register 20 to the coarser scale
for the threshold table. Register 23 holds the old scale and register
24 holds the exact divisor of that scale. -/
@[expose] def roundIntegerLevelGrowth : Stmt :=
  .assign 12 (.bin .add
    (.bin .div (.bin .sub (.reg 20) (.const 1)) (.reg 24)) (.const 1)) ;;
  .assign 4 (.bin .div (.reg 23) (.reg 24))

/-- The rounded numerator and scale represent an upper bound with the
error budget required for integer level thresholds. -/
theorem roundIntegerLevelGrowth_runs
    {w upper scale divisor depth : ℕ} {γ : ℝ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (h20 : st.regs 20 = upper) (h23 : st.regs 23 = scale * divisor)
    (h24 : st.regs 24 = divisor) (hs : 0 < scale) (hd : 0 < divisor)
    (hu : 0 < upper) (hfit : upper < 2 ^ w) (hscale : scale < 2 ^ w)
    (hw : 1 < 2 ^ w)
    (hlo : γ ≤ (upper : ℝ) / ((scale * divisor : ℕ) : ℝ))
    (herr : (upper : ℝ) / ((scale * divisor : ℕ) : ℝ) + 1 / scale ≤
      γ + 1 / ((depth : ℝ) + 1)) :
    ∃ out, Runs w p ω roundIntegerLevelGrowth st .normal out 13 ∧
      out.regs 12 = (upper + divisor - 1) / divisor ∧ out.regs 4 = scale ∧
      γ ≤ (out.regs 12 : ℝ) / scale ∧
      (out.regs 12 : ℝ) / scale ≤ γ + 1 / ((depth : ℝ) + 1) ∧
      out.mem = st.mem ∧ (∀ r, r ≠ 12 → r ≠ 4 → out.regs r = st.regs r) := by
  let a := (upper + divisor - 1) / divisor
  let mid := {st with regs := Function.update st.regs 12 a}
  let out := {mid with regs := Function.update mid.regs 4 scale}
  have hsub : upper - 1 < 2 ^ w := (Nat.sub_le _ _).trans_lt hfit
  have hquot : (upper - 1) / divisor < 2 ^ w := (Nat.div_le_self _ _).trans_lt hsub
  have haEq : (upper - 1) / divisor + 1 = a := by
    change _ = (upper + divisor - 1) / divisor
    rw [show upper + divisor - 1 = (upper - 1) + divisor by omega, Nat.add_div_right _ hd]
  have ha : (upper - 1) / divisor + 1 < 2 ^ w := by
    have h := Nat.div_le_self (upper - 1) divisor
    omega
  have he : scale * divisor / divisor = scale := Nat.mul_div_cancel _ hd
  have r₁ : Runs w p ω
      (.assign 12 (.bin .add
        (.bin .div (.bin .sub (.reg 20) (.const 1)) (.reg 24)) (.const 1)))
      st .normal mid 8 :=
    runs_assign_iff.mpr ⟨a, by simp [Expr.eval, BinOp.eval, h20, h24, hw, hsub, hquot, show a < 2 ^ w from haEq ▸ ha, haEq], rfl, rfl, rfl⟩
  have r₂ : Runs w p ω (.assign 4 (.bin .div (.reg 23) (.reg 24))) mid .normal out 4 :=
    runs_assign_iff.mpr ⟨scale, by simp [Expr.eval, BinOp.eval, mid, h23, h24, he, hscale],
      rfl, rfl, rfl⟩
  obtain ⟨hl, hu⟩ := roundLevelGrowthUpper_bounds upper scale divisor hs hd
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 8, 4, r₁, r₂, rfl⟩),
    by simp [out, mid, a], by simp [out], ?_, ?_, rfl, ?_⟩
  · simpa [out, mid, a] using hlo.trans hl
  · simpa [out, mid, a] using hu.trans herr
  · intro r h12 h4
    simp [out, mid, h12, h4]

/-- Find the power-of-two divisor that produces the coarse threshold scale.
The depth is in register 75 and the original scale is in register 23. -/
@[expose] def prepareIntegerGrowthDivisor (clog : ℕ) : Stmt :=
  .call 25 clog [.bin .mul (.const 2) (.bin .add (.reg 75) (.const 1))] ;;
  .assign 24 (.bin .div (.reg 23) (.bin .shiftLeft (.const 1) (.reg 25)))

/-- Reducing a dyadic scale uses one binary logarithm and preserves
the growth endpoints and all table and heap inputs. -/
theorem prepareIntegerGrowthDivisor_runs
    {w clog depth precision : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hp : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (h75 : st.regs 75 = depth) (h23 : st.regs 23 = 2 ^ precision)
    (hfit : 2 * (depth + 1) + 1 < 2 ^ w) (hprecision : 2 ^ precision < 2 ^ w)
    (he : Nat.clog 2 (2 * (depth + 1)) ≤ precision) :
    let e := Nat.clog 2 (2 * (depth + 1))
    ∃ out cost, Runs w p ω (prepareIntegerGrowthDivisor clog) st .normal out cost ∧
      out.regs 24 = 2 ^ (precision - e) ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 24 → r ≠ 25 → out.regs r = st.regs r) ∧ cost ≤ 40 * e + 33 := by
  dsimp only
  let n := 2 * (depth + 1)
  let e := Nat.clog 2 n
  have htwo : 2 < 2 ^ w := by omega
  have hargs : evalArgs w st [.bin .mul (.const 2) (.bin .add (.reg 75) (.const 1))] = some [n] := by
    simp [evalArgs, Expr.eval, BinOp.eval, h75, htwo, show 1 < 2 ^ w by omega,
      show depth + 1 < 2 ^ w by omega, show 2 * (depth + 1) < 2 ^ w by omega, n]
  obtain ⟨mid, c, v, hr, ⟨hm, hval⟩, h25, hf, hcost⟩ :=
    runs_call_of_meetsContract (r := 25) (Scaling.Machine.clogTwo_meetsContract hp n)
      hargs (by simp; omega) ⟨rfl, hfit, htwo⟩ ω
  have hscale : 2 ^ e < 2 ^ w :=
    (Nat.pow_le_pow_right (by decide) he).trans_lt hprecision
  have hsplit : 2 ^ precision = 2 ^ (precision - e) * 2 ^ e := by
    rw [← pow_add, Nat.sub_add_cancel he]
  have hquot : 2 ^ precision / 2 ^ e = 2 ^ (precision - e) := by
    rw [hsplit, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
  have hqfit : 2 ^ (precision - e) < 2 ^ w :=
    (hquot ▸ Nat.div_le_self (2 ^ precision) (2 ^ e)).trans_lt hprecision
  let out := {mid with regs := Function.update mid.regs 24 (2 ^ (precision - e))}
  have hr' : Runs w p ω (.assign 24 (.bin .div (.reg 23) (.bin .shiftLeft (.const 1) (.reg 25))))
      mid .normal out 6 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval,
      (hf 23 (by decide)).trans h23, show mid.regs 25 = e from h25.trans hval, show 1 < 2 ^ w by omega,
      Nat.shiftLeft_eq, hscale, hquot, hqfit],
      rfl, rfl, rfl⟩
  refine ⟨out, c + 7, runs_seq_iff.mpr (Or.inr ⟨mid, c, 6, hr, hr', rfl⟩),
    by simp [out, e, n], hm, ?_, ?_⟩
  · intro r h24 h25
    simp [out, h24, hf r h25]
  · simp [Scaling.Machine.clogTwoContract, argsSize, Expr.size] at hcost
    change c + 7 ≤ 40 * e + 33
    omega

/-- The word bound for the bucket stretch also covers the shared
denominator in the integer rebuild count. -/
theorem integerRebuildDenominator_fits_of_bucket {w lsstConstant branches vertices : ℕ}
    (hfit : max 2 (concreteBucketStretch lsstConstant branches vertices) + 1 < 2 ^ w) :
    3 * branches * Nat.clog 2 (vertices + 2) ^ 2 < 2 ^ w := by
  let b := Nat.clog 2 (vertices + 2)
  have hb : 0 < b := Nat.clog_pos Nat.one_lt_two (by omega)
  have hcoeff : 3 ≤ 6272 * max 1 lsstConstant := by
    exact (by decide : 3 ≤ 6272).trans
      (Nat.le_mul_of_pos_right _ (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)))
  have hpow : b ^ 2 ≤ b ^ 6 := Nat.pow_le_pow_right hb (by decide)
  have hle : 3 * branches * b ^ 2 ≤ concreteBucketStretch lsstConstant branches vertices :=
    Nat.mul_le_mul (Nat.mul_le_mul_right branches hcoeff) hpow
  exact hle.trans_lt ((le_max_right 2 _).trans_lt (by omega))

end MinCostFlow.MinRatio
