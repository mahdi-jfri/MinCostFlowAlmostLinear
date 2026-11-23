module

public import MinCostFlow.Chain.ConcreteDefs
public import WordRAM.Logic
public import WordRAM.Entry
public import MinCostFlow.Scaling.ClogTwoProgram
import WordRAM.Exec

/-!
# Integer bucket initialization

The initializer counts buckets using two ceiling binary logarithms and
integer arithmetic. All input-dependent quantities come from registers.
-/

@[expose] public section
namespace MinCostFlow.MinRatio

open WordRAM Chain

/-- Compute the integer bucket capacity for Lemma 5.17 (page 23).
The program receives the rounded LSST constant as a fixed witness
constant, and reads the width, branch count, depth and vertex bound
from registers 6, 76, 75 and 92. The result goes in register 47. -/
def initIntegerBucketCap (clog lsstConstant : ℕ) : Stmt :=
  .call 14 clog [.bin .add (.reg 92) (.const 2)] ;;
  .assign 15 (.bin .mul (.reg 14) (.reg 14)) ;;
  .assign 15 (.bin .mul (.reg 15) (.bin .mul (.reg 15) (.reg 15))) ;;
  .assign 16 (.bin .mul (.bin .mul (.const (6272 * max 1 lsstConstant)) (.reg 76)) (.reg 15)) ;;
  .assign 16 (.bin .add (.const 2) (.bin .sub (.reg 16) (.const 2))) ;;
  .call 17 clog [.reg 16] ;;
  .assign 47 (.bin .add (.bin .add (.bin .mul (.const 3) (.reg 6))
    (.bin .mul (.reg 75) (.reg 17))) (.const 2))

theorem initIntegerBucketCap_noRand (clog lsstConstant : ℕ) :
    (initIntegerBucketCap clog lsstConstant).NoRand := by
  simp [initIntegerBucketCap, Stmt.NoRand]

/-- The initializer returns the exact integer cap, preserves memory and
has cost linear in the two ceiling logarithms. The room assumptions
bound the inputs and intermediate arithmetic of the two calls. -/
theorem initIntegerBucketCap_runs {w clog lsstConstant width branches depth vertices : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hp : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (hw : st.regs 6 = width) (hk : st.regs 76 = branches)
    (hd : st.regs 75 = depth) (hn : st.regs 92 = vertices)
    (hbranches : 0 < branches)
    (hvertices : vertices + 3 < 2 ^ w)
    (hstretch : max 2 (concreteBucketStretch lsstConstant branches vertices) + 1 < 2 ^ w)
    (hcap : concreteBucketCap lsstConstant width branches depth vertices < 2 ^ w) :
    ∃ out cost, Runs w p ω (initIntegerBucketCap clog lsstConstant) st .normal out cost ∧
      out.regs 47 = concreteBucketCap lsstConstant width branches depth vertices ∧
      out.regs 14 = Nat.clog 2 (vertices + 2) ∧
      out.mem = st.mem ∧
      (∀ r, r ≠ 14 → r ≠ 15 → r ≠ 16 → r ≠ 17 → r ≠ 47 → out.regs r = st.regs r) ∧
      cost ≤ 40 * (Nat.clog 2 (vertices + 2) +
        Nat.clog 2 (max 2 (concreteBucketStretch lsstConstant branches vertices))) + 100 := by
  let a := Nat.clog 2 (vertices + 2)
  let K := 6272 * max 1 lsstConstant
  let S := concreteBucketStretch lsstConstant branches vertices
  let B := max 2 S
  let b := Nat.clog 2 B
  have ha : 0 < a := Nat.clog_pos Nat.one_lt_two (by omega)
  have hK : 0 < K := by dsimp [K]; positivity
  have hS : S = K * branches * (a * a * (a * a * (a * a))) := by
    simp only [S, concreteBucketStretch, K, a]
    ring
  have hSfit : S < 2 ^ w := (le_max_right 2 S).trans_lt (by omega : B < 2 ^ w)
  have htwo : 2 < 2 ^ w := (le_max_left 2 S).trans_lt (by omega : B < 2 ^ w)
  have hKk : K * branches < 2 ^ w := by
    apply Nat.lt_of_le_of_lt _ hSfit
    rw [hS]
    exact Nat.le_mul_of_pos_right _ (by positivity)
  have hKfit := (Nat.le_mul_of_pos_right K hbranches).trans_lt hKk
  let q := a * a
  have hq3 : q * (q * q) < 2 ^ w := by
    apply Nat.lt_of_le_of_lt _ hSfit
    rw [hS]
    exact Nat.le_mul_of_pos_left _ (by positivity)
  have hq2 := (Nat.le_mul_of_pos_left (q * q) (show 0 < q by dsimp [q]; positivity)).trans_lt hq3
  have hq := (Nat.le_mul_of_pos_right q (show 0 < q by dsimp [q]; positivity)).trans_lt hq2
  have harg : evalArgs w st [.bin .add (.reg 92) (.const 2)] = some [vertices + 2] := by
    simp [evalArgs, Expr.eval, BinOp.eval, hn, htwo, show vertices + 2 < 2 ^ w by omega]
  obtain ⟨s₁, c₁, v₁, r₁, ⟨m₁, hv₁⟩, e₁, f₁, t₁⟩ :=
    runs_call_of_meetsContract (r := 14) (Scaling.Machine.clogTwo_meetsContract hp (vertices + 2))
      harg (by simp; omega) ⟨rfl, by omega, htwo⟩ ω
  have e₁' : s₁.regs 14 = a := e₁.trans hv₁
  let s₂ := {s₁ with regs := Function.update s₁.regs 15 q}
  let s₃ := {s₂ with regs := Function.update s₂.regs 15 (q * (q * q))}
  let s₄ := {s₃ with regs := Function.update s₃.regs 16 S}
  let s₅ := {s₄ with regs := Function.update s₄.regs 16 B}
  have r₂ : Runs w p ω (.assign 15 (.bin .mul (.reg 14) (.reg 14))) s₁ .normal s₂ 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, e₁', q, show a * a < 2 ^ w from hq], rfl, rfl, rfl⟩
  have r₃ : Runs w p ω (.assign 15 (.bin .mul (.reg 15) (.bin .mul (.reg 15) (.reg 15))))
      s₂ .normal s₃ 6 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, s₂, hq2, hq3], rfl, rfl, rfl⟩
  have r₄ : Runs w p ω
      (.assign 16 (.bin .mul (.bin .mul (.const K) (.reg 76)) (.reg 15))) s₃ .normal s₄ 6 := by
    refine runs_assign_iff.mpr ⟨S, ?_, rfl, rfl, rfl⟩
    have hb : s₂.regs 76 = branches := by simp [s₂, f₁ 76 (by decide), hk]
    simp [Expr.eval, BinOp.eval, s₃, hb, hKfit, hKk, ← hS, q, hSfit]
  have hB : 2 + (S - 2) = B := by dsimp [B]; omega
  have r₅ : Runs w p ω (.assign 16 (.bin .add (.const 2) (.bin .sub (.reg 16) (.const 2))))
      s₄ .normal s₅ 6 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, s₄, htwo, hB,
      (Nat.sub_le S 2).trans_lt hSfit, show B < 2 ^ w by omega], rfl, rfl, rfl⟩
  have harg' : evalArgs w s₅ [.reg 16] = some [B] := by simp [evalArgs, Expr.eval, s₅]
  obtain ⟨s₆, c₆, v₆, r₆, ⟨m₆, hv₆⟩, e₆, f₆, t₆⟩ :=
    runs_call_of_meetsContract (r := 17) (Scaling.Machine.clogTwo_meetsContract hp B)
      harg' (by simp; omega) ⟨rfl, hstretch, htwo⟩ ω
  have e₆' : s₆.regs 17 = b := e₆.trans hv₆
  let cap := concreteBucketCap lsstConstant width branches depth vertices
  have hcap' : 3 * width + depth * b + 2 < 2 ^ w := hcap
  let out := {s₆ with regs := Function.update s₆.regs 47 cap}
  have r₇ : Runs w p ω
      (.assign 47 (.bin .add (.bin .add (.bin .mul (.const 3) (.reg 6))
        (.bin .mul (.reg 75) (.reg 17))) (.const 2))) s₆ .normal out 10 := by
    refine runs_assign_iff.mpr ⟨cap, ?_, rfl, rfl, rfl⟩
    have h6 : s₆.regs 6 = width := by simp [f₆ 6 (by decide), s₅, s₄, s₃, s₂, f₁ 6 (by decide), hw]
    have h75 : s₆.regs 75 = depth := by simp [f₆ 75 (by decide), s₅, s₄, s₃, s₂, f₁ 75 (by decide), hd]
    simp [Expr.eval, BinOp.eval, h6, h75, e₆', show 3 < 2 ^ w by omega, htwo,
      show 3 * width < 2 ^ w by omega, show depth * b < 2 ^ w by omega,
      show 3 * width + depth * b < 2 ^ w by omega, hcap', show cap = 3 * width + depth * b + 2 from rfl]
  refine ⟨out, c₁ + c₆ + 38, ?_, by simp [out, cap], ?_, m₆.trans m₁, ?_, ?_⟩
  · unfold initIntegerBucketCap
    refine runs_seq_iff.mpr (Or.inr ⟨s₁, c₁, c₆ + 37, r₁, ?_, by omega⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s₂, 4, c₆ + 32, r₂, ?_, by omega⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s₃, 6, c₆ + 25, r₃, ?_, by omega⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s₄, 6, c₆ + 18, r₄, ?_, by omega⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s₅, 6, c₆ + 11, r₅, ?_, by omega⟩)
    exact runs_seq_iff.mpr (Or.inr ⟨s₆, c₆, 10, r₆, r₇, by omega⟩)
  · simpa [out, f₆ 14 (by decide), s₅, s₄, s₃, s₂, a] using e₁'
  · intro r h14 h15 h16 h17 h47
    simp [out, h47, f₆ r h17, s₅, s₄, s₃, s₂, h16, h15, f₁ r h14]
  · simp [Scaling.Machine.clogTwoContract, argsSize, Expr.size] at t₁ t₆
    change c₁ + c₆ + 38 ≤ 40 * (a + b) + 100
    omega

/-- Publish the exact cap and forward the existing heap cursor to the
next Init stage. The success word is always set on a successful run. -/
def initIntegerBucketStage (clog lsstConstant : ℕ) : Stmt :=
  initIntegerBucketCap clog lsstConstant ;;
  .assign 99 (.reg 98) ;;
  .assign 18 (.const 1)

theorem initIntegerBucketStage_noRand (clog lsstConstant : ℕ) :
    (initIntegerBucketStage clog lsstConstant).NoRand := by
  simp [initIntegerBucketStage, Stmt.NoRand, initIntegerBucketCap_noRand]

/-- The integer bucket stage supplies the exact cap and the cursor for
the following sparsifier stage, preserving the saved solver arguments. -/
theorem initIntegerBucketStage_runs {w clog lsstConstant width branches depth vertices heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hp : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (hw : st.regs 6 = width) (hk : st.regs 76 = branches)
    (hd : st.regs 75 = depth) (hn : st.regs 92 = vertices) (hh : st.regs 98 = heap)
    (hbranches : 0 < branches)
    (hvertices : vertices + 3 < 2 ^ w)
    (hstretch : max 2 (concreteBucketStretch lsstConstant branches vertices) + 1 < 2 ^ w)
    (hcap : concreteBucketCap lsstConstant width branches depth vertices < 2 ^ w) :
    ∃ out cost, Runs w p ω (initIntegerBucketStage clog lsstConstant) st .normal out cost ∧
      out.regs 47 = concreteBucketCap lsstConstant width branches depth vertices ∧
      out.regs 14 = Nat.clog 2 (vertices + 2) ∧
      out.regs 18 = 1 ∧ out.regs 99 = heap ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 14 → r ≠ 15 → r ≠ 16 → r ≠ 17 → r ≠ 18 → r ≠ 47 → r ≠ 99 →
        out.regs r = st.regs r) ∧
      cost ≤ 40 * (Nat.clog 2 (vertices + 2) +
        Nat.clog 2 (max 2 (concreteBucketStretch lsstConstant branches vertices))) + 106 := by
  obtain ⟨mid, c, hr, hc, hlog, hm, hf, hcost⟩ :=
    initIntegerBucketCap_runs (ω := ω) hp hw hk hd hn hbranches hvertices hstretch hcap
  have hh' : mid.regs 98 = heap := (hf 98 (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans hh
  have hone : 1 < 2 ^ w := by omega
  let next := {mid with regs := Function.update mid.regs 99 heap}
  let out := {next with regs := Function.update next.regs 18 1}
  have hnext : Runs w p ω (.assign 99 (.reg 98)) mid .normal next 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hh'], rfl, rfl, rfl⟩
  have hout : Runs w p ω (.assign 18 (.const 1)) next .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hone], rfl, rfl, rfl⟩
  refine ⟨out, c + 6, ?_, by simpa [out, next] using hc, by simpa [out, next] using hlog, by simp [out],
    by simp [out, next], hm, ?_, by omega⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨mid, c, 5, hr,
      runs_seq_iff.mpr (Or.inr ⟨next, 2, 2, hnext, hout, rfl⟩), by omega⟩)
  · intro r h14 h15 h16 h17 h18 h47 h99
    simpa [out, next, h18, h99] using hf r h14 h15 h16 h17 h47

/-- One polynomial word bound is enough for both logarithm arguments
and the final bucket capacity. -/
theorem integerBucketStage_word_bounds {w lsstConstant width branches depth vertices base : ℕ}
    (hbase : 3 ≤ base) (hwidth : width ≤ base) (hbranches : branches ≤ base)
    (hdepth : depth ≤ base) (hvertices : vertices + 3 ≤ base)
    (hconstant : 6272 * max 1 lsstConstant ≤ base)
    (hword : base ^ 10 < 2 ^ w) :
    vertices + 3 < 2 ^ w ∧
      max 2 (concreteBucketStretch lsstConstant branches vertices) + 1 < 2 ^ w ∧
      concreteBucketCap lsstConstant width branches depth vertices < 2 ^ w := by
  have hb : 0 < base := by omega
  have hpow (i j : ℕ) (h : i ≤ j) : base ^ i ≤ base ^ j :=
    Nat.pow_le_pow_right hb h
  have hclog (n : ℕ) : Nat.clog 2 n ≤ n :=
    Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have ha : Nat.clog 2 (vertices + 2) ≤ base :=
    (hclog _).trans (by omega)
  have hs : concreteBucketStretch lsstConstant branches vertices ≤ base ^ 8 := by
    unfold concreteBucketStretch
    calc
      _ ≤ base * base * base ^ 6 := Nat.mul_le_mul
        (Nat.mul_le_mul hconstant hbranches) (Nat.pow_le_pow_left ha 6)
      _ = base ^ 8 := by ring
  have hlinear : base ≤ base ^ 8 := by simpa using hpow 1 8 (by decide)
  have hS : max 2 (concreteBucketStretch lsstConstant branches vertices) ≤ base ^ 8 :=
    max_le ((show 2 ≤ base by omega).trans hlinear) hs
  have hnext : base ^ 8 + 1 ≤ base ^ 9 := by
    have h := Nat.mul_le_mul_left (base ^ 8) hbase
    rw [show base ^ 8 * base = base ^ 9 by ring, Nat.mul_comm (base ^ 8) 3] at h
    have hp : 0 < base ^ 8 := Nat.pow_pos hb
    omega
  have hcap : concreteBucketCap lsstConstant width branches depth vertices ≤ base ^ 10 := by
    unfold concreteBucketCap
    have hprod := Nat.mul_le_mul hdepth ((hclog _).trans hS)
    have hp : base ≤ base ^ 9 := by simpa using hpow 1 9 (by decide)
    have hpow₉ : base ^ 8 ≤ base ^ 9 := hpow 8 9 (by decide)
    have hsmall : 3 * base + 2 ≤ 2 * base ^ 9 := by
      have hlarge : base ^ 2 ≤ base ^ 9 := hpow 2 9 (by decide)
      have hsq := Nat.mul_le_mul_right base hbase
      have hsq' : 3 * base ≤ base ^ 2 := by simpa [pow_two] using hsq
      omega
    have hmul : base * base ^ 8 = base ^ 9 := by ring
    rw [hmul] at hprod
    have hbig : 3 * base ^ 9 ≤ base ^ 10 := by
      rw [show base ^ 10 = base * base ^ 9 by ring]
      exact Nat.mul_le_mul_right (base ^ 9) hbase
    omega
  have hbaseword : base < 2 ^ w := hlinear.trans_lt ((hpow 8 10 (by decide)).trans_lt hword)
  exact ⟨hvertices.trans_lt hbaseword,
    ((Nat.add_le_add_right hS 1).trans (hnext.trans (hpow 9 10 (by decide)))).trans_lt hword,
    hcap.trans_lt hword⟩

/-- At the encoded input's word size, a common power bound on the
parameters provides all three room bounds of the initializer. -/
theorem integerBucketStage_wordSize_bounds (input : List ℕ)
    {c degree lsstConstant width branches depth vertices : ℕ} :
    let base := input.length + input.foldr max 0 + 2
    1 ≤ degree → 10 * degree ≤ c →
    width ≤ base ^ degree → branches ≤ base ^ degree → depth ≤ base ^ degree →
    vertices + 3 ≤ base ^ degree → 6272 * max 1 lsstConstant ≤ base ^ degree →
    vertices + 3 < 2 ^ wordSize c input ∧
      max 2 (concreteBucketStretch lsstConstant branches vertices) + 1 < 2 ^ wordSize c input ∧
      concreteBucketCap lsstConstant width branches depth vertices < 2 ^ wordSize c input := by
  dsimp only
  let base := input.length + input.foldr max 0 + 2
  intro hdegree hc hwidth hbranches hdepth hvertices hconstant
  have hbase : 0 < base := by dsimp [base]; omega
  have hpower : (base ^ degree) ^ 10 < 2 ^ wordSize c input := by
    rw [← pow_mul]
    exact (Nat.pow_le_pow_right hbase (by omega : degree * 10 ≤ c)).trans_lt
      (pow_lt_two_pow_wordSize (by omega) input)
  have hlarge : 3 ≤ base ^ degree := (by omega : 3 ≤ vertices + 3).trans hvertices
  exact integerBucketStage_word_bounds hlarge hwidth hbranches hdepth hvertices hconstant hpower

end MinCostFlow.MinRatio
