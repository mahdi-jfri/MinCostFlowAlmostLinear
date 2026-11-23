module

public import MinCostFlow.MinRatio.InitSparsifierPath
public import MinCostFlow.Expander.DecomposePhiProg

/-!
# Runtime conductance and edge-cap inputs

Compute the conductance denominator and witness edge cap from the input
size. Use the working precision to scale both conductances and the fixed
coefficient bounds.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM

/-- Compute the witness edge cap from the input edge cap and the exact
ratio of the degree coefficient to the input conductance. -/
@[expose] def initSparsifierWitnessEdgeCap : Stmt :=
  .assign 58 (.bin .add
    (.bin .div (.bin .add (.bin .mul (.reg 59) (.reg 23)) (.bin .sub (.reg 62) (.const 1))) (.reg 62))
    (.const 1))

/-- Ceiling division gives the Section 8 witness edge cap when the
ratio of the degree coefficient to conductance is represented exactly. -/
theorem initSparsifierWitnessEdgeCap_runs {w M num den : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {cDeg phiMin : ℝ}
    (hM : st.regs 23 = M) (hn : st.regs 59 = num) (hd : st.regs 62 = den)
    (hpos : 0 < den)
    (hratio : cDeg / phiMin = (num : ℝ) / den)
    (hfit : num * M + (den - 1) + 1 < 2 ^ w) :
    ∃ out, Runs w p ω initSparsifierWitnessEdgeCap st .normal out 12 ∧
      out.regs 58 = Spanner.capM_W cDeg phiMin M ∧ out.mem = st.mem ∧
      (∀ r ≠ 58, out.regs r = st.regs r) := by
  let n := num * M
  let q := (n + (den - 1)) / den
  have hnum : num * M < 2 ^ w := by omega
  have hden : den - 1 < 2 ^ w := by omega
  have hadd : num * M + (den - 1) < 2 ^ w := by omega
  have hq : q ≤ n + (den - 1) := Nat.div_le_self _ _
  have hqw : q < 2 ^ w := hq.trans_lt hadd
  have hq1 : q + 1 < 2 ^ w := (Nat.add_le_add_right hq _).trans_lt hfit
  let out := {st with regs := Function.update st.regs 58 (q + 1)}
  have hr : Runs w p ω initSparsifierWitnessEdgeCap st .normal out 12 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, hM, hn, hd,
        hnum, hden, hadd, show 1 < 2 ^ w by omega,
        show (num * M + (den - 1)) / den < 2 ^ w from hqw,
        show (num * M + (den - 1)) / den + 1 < 2 ^ w from hq1, q, n],
      rfl, rfl, rfl⟩
  have hreal : cDeg * (M : ℝ) / phiMin = (n : ℝ) / den := by
    rw [mul_comm cDeg, mul_div_assoc, hratio, ← mul_div_assoc, mul_comm, Nat.cast_mul]
  have hd' : (0 : ℝ) < den := by exact_mod_cast hpos
  have hceil : ⌈(n : ℝ) / den⌉₊ = q := by
    apply Nat.le_antisymm
    · apply Nat.ceil_le.mpr
      apply (div_le_iff₀ hd').mpr
      have hmod := Nat.mod_lt (n + (den - 1)) hpos
      have hsum := Nat.mod_add_div (n + (den - 1)) den
      rw [Nat.mul_comm den] at hsum
      change (n + (den - 1)) % den + q * den = n + (den - 1) at hsum
      exact_mod_cast (show n ≤ q * den by omega)
    · have hb := (div_le_iff₀ hd').mp (Nat.le_ceil ((n : ℝ) / den))
      have hb' : n ≤ ⌈(n : ℝ) / den⌉₊ * den := by exact_mod_cast hb
      have hmul : n + (den - 1) < (⌈(n : ℝ) / den⌉₊ + 1) * den := by
        rw [Nat.add_mul, one_mul]
        omega
      exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hpos).mpr hmul)
  exact ⟨out, hr, by simp [out, Spanner.capM_W, hreal, hceil], rfl, fun r h => by simp [out, h]⟩

/-- Compute the decomposition conductance denominator using the shared
integer routine and the current edge cap in register 23. -/
@[expose] def initSparsifierConductanceDen (K thr : ℕ) : Stmt :=
  Expander.computePhiDenStmt K thr 23 63 24 31 32 33 36 ;;
  .assign 63 (.bin .mul (.const 3) (.reg 63))

/-- Register 63 contains the denominator of the concrete conductance
lower bound. The calculation only uses registers. -/
theorem initSparsifierConductanceDen_runs {w K thr M : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hK : 1 ≤ K) (hM : st.regs 23 = M)
    (hm : 4 * M + 2 < 2 ^ w) (hcube : (Nat.log 2 (4 * M + 2) + 2) ^ 3 < 2 ^ w)
    (hfit : Expander.maxPhiDenOf K thr M < 2 ^ w) :
    ∃ out cost, Runs w p ω (initSparsifierConductanceDen K thr) st .normal out cost ∧
      out.regs 63 = Expander.maxPhiDenOf K thr M ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 63 → r ≠ 24 → r ≠ 31 → r ≠ 32 → r ≠ 33 → r ≠ 36 → out.regs r = st.regs r) ∧
      cost ≤ 120 * (Nat.log 2 (4 * M + 2) + K * (Expander.rOf (4 * M)) ^ 2 + 4) + 5 := by
  have hhalf : Expander.phiDenHalf K thr M < 2 ^ w := by
    change 3 * Expander.phiDenHalf K thr M < 2 ^ w at hfit
    omega
  have ht := Expander.computePhiDenStmt_triple (w := w) (p := p) (thr := thr)
    (rOut := 63) (rL := 24) (rR := 31) (rPow := 32) (rIdx := 33) (rCur := 36)
    hK (by decide) st hM hm hcube hhalf
  obtain ⟨result, mid, cost, hr₁, hp, hc⟩ := ht st ω rfl
  change cost ≤ 120 * (Nat.log 2 (4 * M + 2) + K * (Expander.rOf (4 * M)) ^ 2 + 4) at hc
  cases result <;> simp only [normalPost] at hp
  obtain ⟨h63, hmem, _, hk⟩ := hp
  let out := {mid with regs := Function.update mid.regs 63 (Expander.maxPhiDenOf K thr M)}
  have hmul : 3 * Expander.phiDenHalf K thr M < 2 ^ w := hfit
  have hthree : 3 < 2 ^ w := by
    have hpos := Expander.le_phiDenHalf_thr K thr M
    omega
  have hr₂ : Runs w p ω (.assign 63 (.bin .mul (.const 3) (.reg 63))) mid .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, h63, hthree, hmul, Expander.maxPhiDenOf],
      rfl, rfl, rfl⟩
  exact ⟨out, cost + 5, runs_seq_iff.mpr (Or.inr ⟨mid, cost, 4, hr₁, hr₂, by omega⟩),
    by simp [out], hmem, fun r h63' h24 h31 h32 h33 h36 =>
      by simpa [out, h63'] using hk r h63' h24 h31 h32 h33 h36, by omega⟩

/-- With reciprocal conductance in register 63, compute the witness
edge cap for the degree coefficient of the Section 8 construction. -/
@[expose] def initSparsifierWitnessEdgeCapOfDenWithDegree (cDeg : ℕ) : Stmt :=
  .assign 58 (.bin .add (.bin .mul (.bin .mul (.const cDeg) (.reg 63)) (.reg 23)) (.const 1))

/-- Reciprocal conductance makes the witness edge cap integral. -/
theorem sparsifierWitnessEdgeCap_eq (cDeg den M : ℕ) (hden : 0 < den) :
    Spanner.capM_W cDeg (1 / (den : ℝ)) M = cDeg * den * M + 1 := by
  have hd : (den : ℝ) ≠ 0 := by exact_mod_cast hden.ne'
  have hval : (cDeg : ℝ) * M / (1 / (den : ℝ)) = ((cDeg * den * M : ℕ) : ℝ) := by
    push_cast
    field_simp
  rw [Spanner.capM_W, hval, Nat.ceil_natCast]

/-- The quotient in the witness edge cap is integral for reciprocal
conductance, so its ceiling is computed by word multiplication. -/
theorem initSparsifierWitnessEdgeCapOfDenWithDegree_runs {w M den cDeg : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hM : st.regs 23 = M) (hd : st.regs 63 = den) (hpos : 0 < den)
    (hcWord : cDeg < 2 ^ w) (hc : cDeg * den < 2 ^ w) (hfit : cDeg * den * M + 1 < 2 ^ w) :
    ∃ out, Runs w p ω (initSparsifierWitnessEdgeCapOfDenWithDegree cDeg) st .normal out 8 ∧
      out.regs 58 = Spanner.capM_W cDeg (1 / (den : ℝ)) M ∧ out.mem = st.mem ∧
      (∀ r ≠ 58, out.regs r = st.regs r) := by
  let value := cDeg * den * M + 1
  let out := {st with regs := Function.update st.regs 58 value}
  have hr : Runs w p ω (initSparsifierWitnessEdgeCapOfDenWithDegree cDeg) st .normal out 8 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hM, hd, hc, hfit, value,
      hcWord, show 1 < 2 ^ w by omega, show cDeg * den * M < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  exact ⟨out, hr, by rw [sparsifierWitnessEdgeCap_eq cDeg den M hpos]; simp [out, value],
    rfl, fun r h => by simp [out, h]⟩

/-- With reciprocal conductance in register 63, compute the witness
edge cap for the degree coefficient 36 of the Section 8 construction. -/
@[expose] def initSparsifierWitnessEdgeCapOfDen : Stmt :=
  initSparsifierWitnessEdgeCapOfDenWithDegree 36

/-- The quotient in the witness edge cap is integral for reciprocal
conductance, so its ceiling is computed by word multiplication. -/
theorem initSparsifierWitnessEdgeCapOfDen_runs {w M den : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hM : st.regs 23 = M) (hd : st.regs 63 = den) (hpos : 0 < den)
    (hc : 36 * den < 2 ^ w) (hfit : 36 * den * M + 1 < 2 ^ w) :
    ∃ out, Runs w p ω initSparsifierWitnessEdgeCapOfDen st .normal out 8 ∧
      out.regs 58 = Spanner.capM_W 36 (1 / (den : ℝ)) M ∧ out.mem = st.mem ∧
      (∀ r ≠ 58, out.regs r = st.regs r) := by
  exact initSparsifierWitnessEdgeCapOfDenWithDegree_runs hM hd hpos (by omega) hc hfit

/-- Compute the input conductance denominator and its corresponding
witness edge cap from the same runtime graph size. -/
@[expose] def computeInitSparsifierWitnessEdgeCapWithDegree (K thr cDeg : ℕ) : Stmt :=
  initSparsifierConductanceDen K thr ;; initSparsifierWitnessEdgeCapOfDenWithDegree cDeg

/-- The two saved words use the same concrete conductance lower bound. -/
theorem computeInitSparsifierWitnessEdgeCapWithDegree_runs {w K thr M cDeg : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hK : 1 ≤ K) (hM : st.regs 23 = M)
    (hm : 4 * M + 2 < 2 ^ w) (hcube : (Nat.log 2 (4 * M + 2) + 2) ^ 3 < 2 ^ w)
    (hcPos : 0 < cDeg) (hcWord : cDeg < 2 ^ w)
    (hc : cDeg * Expander.maxPhiDenOf K thr M < 2 ^ w)
    (hfit : cDeg * Expander.maxPhiDenOf K thr M * M + 1 < 2 ^ w) :
    ∃ out cost, Runs w p ω (computeInitSparsifierWitnessEdgeCapWithDegree K thr cDeg) st .normal out cost ∧
      out.regs 63 = Expander.maxPhiDenOf K thr M ∧
      out.regs 58 = Spanner.capM_W cDeg (1 / (Expander.maxPhiDenOf K thr M : ℝ)) M ∧
      out.mem = st.mem ∧
      (∀ r, r ∉ ([24, 31, 32, 33, 36, 58, 63] : List ℕ) → out.regs r = st.regs r) ∧
      cost ≤ 120 * (Nat.log 2 (4 * M + 2) + K * (Expander.rOf (4 * M)) ^ 2 + 4) + 14 := by
  have hden : Expander.maxPhiDenOf K thr M < 2 ^ w :=
    (Nat.le_mul_of_pos_left _ hcPos).trans_lt hc
  obtain ⟨mid, cost, hr₁, h63, hm₁, hk₁, hc₁⟩ :=
    initSparsifierConductanceDen_runs (ω := ω) hK hM hm hcube hden
  obtain ⟨out, hr₂, h58, hm₂, hk₂⟩ :=
    initSparsifierWitnessEdgeCapOfDenWithDegree_runs (p := p) (ω := ω)
      ((hk₁ 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hM)
      h63 (Expander.maxPhiDenOf_pos K thr M) hcWord hc hfit
  refine ⟨out, cost + 9, runs_seq_iff.mpr (Or.inr ⟨mid, cost, 8, hr₁, hr₂, by omega⟩),
    (hk₂ 63 (by decide)).trans h63, h58, hm₂.trans hm₁, ?_, by omega⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h24, h31, h32, h33, h36, h58', h63'⟩ := hr
  exact (hk₂ r h58').trans (hk₁ r h63' h24 h31 h32 h33 h36)

/-- Compute the input conductance denominator and its corresponding
witness edge cap from the same runtime graph size. -/
@[expose] def computeInitSparsifierWitnessEdgeCap (K thr : ℕ) : Stmt :=
  computeInitSparsifierWitnessEdgeCapWithDegree K thr 36

/-- The two saved words use the same concrete conductance lower bound. -/
theorem computeInitSparsifierWitnessEdgeCap_runs {w K thr M : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hK : 1 ≤ K) (hM : st.regs 23 = M)
    (hm : 4 * M + 2 < 2 ^ w) (hcube : (Nat.log 2 (4 * M + 2) + 2) ^ 3 < 2 ^ w)
    (hc : 36 * Expander.maxPhiDenOf K thr M < 2 ^ w)
    (hfit : 36 * Expander.maxPhiDenOf K thr M * M + 1 < 2 ^ w) :
    ∃ out cost, Runs w p ω (computeInitSparsifierWitnessEdgeCap K thr) st .normal out cost ∧
      out.regs 63 = Expander.maxPhiDenOf K thr M ∧
      out.regs 58 = Spanner.capM_W 36 (1 / (Expander.maxPhiDenOf K thr M : ℝ)) M ∧
      out.mem = st.mem ∧
      (∀ r, r ∉ ([24, 31, 32, 33, 36, 58, 63] : List ℕ) → out.regs r = st.regs r) ∧
      cost ≤ 120 * (Nat.log 2 (4 * M + 2) + K * (Expander.rOf (4 * M)) ^ 2 + 4) + 14 := by
  exact computeInitSparsifierWitnessEdgeCapWithDegree_runs hK hM hm hcube (by decide) (by have := Expander.maxPhiDenOf_pos K thr M; omega) hc hfit

/-- Encode the reciprocal conductance at the working scale, rounding
the endpoints in opposite directions. -/
@[expose] def initSparsifierConductanceBounds : Stmt :=
  .assign 53 (.bin .div (.reg 4) (.reg 63)) ;;
  .assign 54 (.bin .div (.bin .add (.reg 4) (.bin .sub (.reg 63) (.const 1))) (.reg 63))

/-- The two scaled words enclose the decomposition conductance. -/
theorem initSparsifierConductanceBounds_runs {w scale den : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hs : st.regs 4 = scale) (hd : st.regs 63 = den)
    (hpos : 0 < den) (hscale : 0 < scale) (hw : 1 < 2 ^ w)
    (hfit : scale + (den - 1) < 2 ^ w) :
    ∃ out, Runs w p ω initSparsifierConductanceBounds st .normal out 13 ∧
      (out.regs 53 : ℝ) / scale ≤ 1 / (den : ℝ) ∧ 1 / (den : ℝ) ≤ (out.regs 54 : ℝ) / scale ∧
      out.regs 53 = scale / den ∧ out.regs 54 = (scale + (den - 1)) / den ∧
      (den ≤ scale → 0 < out.regs 53) ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 53 → r ≠ 54 → out.regs r = st.regs r) := by
  let lo := scale / den
  let hi := (scale + (den - 1)) / den
  let mid := {st with regs := Function.update st.regs 53 lo}
  let out := {mid with regs := Function.update mid.regs 54 hi}
  have hwlo : scale / den < 2 ^ w := (Nat.div_le_self ..).trans_lt (by omega)
  have hwhi : (scale + (den - 1)) / den < 2 ^ w := (Nat.div_le_self ..).trans_lt hfit
  have hr₁ : Runs w p ω (.assign 53 (.bin .div (.reg 4) (.reg 63))) st .normal mid 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hs, hd, lo, hwlo], rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω
      (.assign 54 (.bin .div (.bin .add (.reg 4) (.bin .sub (.reg 63) (.const 1))) (.reg 63)))
      mid .normal out 8 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, mid, hs, hd, hw,
      show den - 1 < 2 ^ w by omega, hfit, hi, hwhi], rfl, rfl, rfl⟩
  have hLo : out.regs 53 = lo := by simp [out, mid]
  have hHi : out.regs 54 = hi := by simp [out]
  have hround : scale ≤ hi * den := by
    have hm := Nat.mod_lt (scale + (den - 1)) hpos
    have he := Nat.mod_add_div (scale + (den - 1)) den
    rw [Nat.mul_comm den] at he
    change (scale + (den - 1)) % den + hi * den = scale + (den - 1) at he
    omega
  have hd' : (0 : ℝ) < den := by exact_mod_cast hpos
  have hs' : (0 : ℝ) < scale := by exact_mod_cast hscale
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 4, 8, hr₁, hr₂, rfl⟩), ?_, ?_,
    hLo, hHi, ?_, rfl, fun r h53 h54 => by simp [out, mid, h53, h54]⟩
  · rw [hLo]
    exact (div_le_div_iff₀ hs' hd').mpr (by
      simpa only [one_mul] using (show (lo : ℝ) * den ≤ scale by
        exact_mod_cast Nat.div_mul_le_self scale den))
  · rw [hHi]
    exact (div_le_div_iff₀ hd' hs').mpr (by
      simpa only [one_mul] using (show (scale : ℝ) ≤ (hi : ℝ) * den by exact_mod_cast hround))
  · intro he
    rw [hLo]
    exact Nat.div_pos he hpos

/-- Prepare the input conductance interval and witness edge cap for the
two path calls. -/
@[expose] def prepareInitSparsifierConductanceWithDegree (K thr cDeg : ℕ) : Stmt :=
  computeInitSparsifierWitnessEdgeCapWithDegree K thr cDeg ;; initSparsifierConductanceBounds

/-- The saved cap and the conductance bounds refer to the same
decomposition denominator. -/
theorem prepareInitSparsifierConductanceWithDegree_runs {w K thr M scale cDeg : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hK : 1 ≤ K) (hM : st.regs 23 = M) (hs : st.regs 4 = scale) (hsPos : 0 < scale)
    (hm : 4 * M + 2 < 2 ^ w) (hcube : (Nat.log 2 (4 * M + 2) + 2) ^ 3 < 2 ^ w)
    (hcPos : 0 < cDeg) (hcWord : cDeg < 2 ^ w)
    (hc : cDeg * Expander.maxPhiDenOf K thr M < 2 ^ w)
    (hfit : cDeg * Expander.maxPhiDenOf K thr M * M + 1 < 2 ^ w)
    (hden : Expander.maxPhiDenOf K thr M ≤ scale)
    (hround : scale + (Expander.maxPhiDenOf K thr M - 1) < 2 ^ w) :
    let den := Expander.maxPhiDenOf K thr M
    ∃ out cost, Runs w p ω (prepareInitSparsifierConductanceWithDegree K thr cDeg) st .normal out cost ∧
      out.regs 63 = den ∧ out.regs 58 = Spanner.capM_W cDeg (1 / (den : ℝ)) M ∧
      (out.regs 53 : ℝ) / scale ≤ 1 / (den : ℝ) ∧ 1 / (den : ℝ) ≤ (out.regs 54 : ℝ) / scale ∧
      out.regs 53 = scale / den ∧ out.regs 54 = (scale + (den - 1)) / den ∧
      0 < out.regs 53 ∧ out.mem = st.mem ∧
      (∀ r, r ∉ ([24, 31, 32, 33, 36, 53, 54, 58, 63] : List ℕ) → out.regs r = st.regs r) ∧
      cost ≤ 120 * (Nat.log 2 (4 * M + 2) + K * (Expander.rOf (4 * M)) ^ 2 + 4) + 28 := by
  obtain ⟨mid, cost, hr₁, h63, h58, hm₁, hk₁, hc₁⟩ :=
    computeInitSparsifierWitnessEdgeCapWithDegree_runs (ω := ω) hK hM hm hcube hcPos hcWord hc hfit
  obtain ⟨out, hr₂, lb, ub, h53, h54, hp, hm₂, hk₂⟩ :=
    initSparsifierConductanceBounds_runs (p := p) (ω := ω)
      ((hk₁ 4 (by decide)).trans hs) h63 (Expander.maxPhiDenOf_pos K thr M) hsPos (by omega) hround
  refine ⟨out, cost + 14, runs_seq_iff.mpr (Or.inr ⟨mid, cost, 13, hr₁, hr₂, by omega⟩),
    (hk₂ 63 (by decide) (by decide)).trans h63, (hk₂ 58 (by decide) (by decide)).trans h58,
    lb, ub, h53, h54, hp hden, hm₂.trans hm₁, ?_, by omega⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h24, h31, h32, h33, h36, h53', h54', h58', h63'⟩ := hr
  exact (hk₂ r h53' h54').trans (hk₁ r (by simp [h24, h31, h32, h33, h36, h58', h63']))

/-- Prepare the input conductance interval and witness edge cap for the
two path calls. -/
@[expose] def prepareInitSparsifierConductance (K thr : ℕ) : Stmt :=
  prepareInitSparsifierConductanceWithDegree K thr 36

/-- The saved cap and the conductance bounds refer to the same
decomposition denominator. -/
theorem prepareInitSparsifierConductance_runs {w K thr M scale : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hK : 1 ≤ K) (hM : st.regs 23 = M) (hs : st.regs 4 = scale) (hsPos : 0 < scale)
    (hm : 4 * M + 2 < 2 ^ w) (hcube : (Nat.log 2 (4 * M + 2) + 2) ^ 3 < 2 ^ w)
    (hc : 36 * Expander.maxPhiDenOf K thr M < 2 ^ w)
    (hfit : 36 * Expander.maxPhiDenOf K thr M * M + 1 < 2 ^ w)
    (hden : Expander.maxPhiDenOf K thr M ≤ scale)
    (hround : scale + (Expander.maxPhiDenOf K thr M - 1) < 2 ^ w) :
    let den := Expander.maxPhiDenOf K thr M
    ∃ out cost, Runs w p ω (prepareInitSparsifierConductance K thr) st .normal out cost ∧
      out.regs 63 = den ∧ out.regs 58 = Spanner.capM_W 36 (1 / (den : ℝ)) M ∧
      (out.regs 53 : ℝ) / scale ≤ 1 / (den : ℝ) ∧ 1 / (den : ℝ) ≤ (out.regs 54 : ℝ) / scale ∧
      out.regs 53 = scale / den ∧ out.regs 54 = (scale + (den - 1)) / den ∧
      0 < out.regs 53 ∧ out.mem = st.mem ∧
      (∀ r, r ∉ ([24, 31, 32, 33, 36, 53, 54, 58, 63] : List ℕ) → out.regs r = st.regs r) ∧
      cost ≤ 120 * (Nat.log 2 (4 * M + 2) + K * (Expander.rOf (4 * M)) ^ 2 + 4) + 28 := by
  exact prepareInitSparsifierConductanceWithDegree_runs hK hM hs hsPos hm hcube
    (by decide) (by have := Expander.maxPhiDenOf_pos K thr M; omega) hc hfit hden hround

/-- When the cited conductance bound is below the witness conductance,
the concrete path length can use the rational conductance `1 / c`
provided it too is above the cited bound. -/
theorem initSparsifierWitnessPath_conductance_eq (Kγ c M : ℕ) (K phiConst : ℝ)
    (hc : 0 < c) (hphi : Cited.csPhi Kγ c (3 * M) ≤ phiConst) :
    Expander.csGammaExpPath Kγ c K phiConst M =
      Expander.csGammaExpPath Kγ c K (1 / (c : ℝ)) M := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hg : (1 : ℝ) ≤ Cited.csGamma Kγ (3 * M) := by
    unfold Cited.csGamma
    exact_mod_cast Nat.one_le_pow _ _ (by decide : 0 < (2 : ℕ))
  have hle : Cited.csPhi Kγ c (3 * M) ≤ 1 / (c : ℝ) := by
    unfold Cited.csPhi
    apply one_div_le_one_div_of_le hc'
    simpa using mul_le_mul_of_nonneg_left hg hc'.le
  have he : Expander.csPhiOut Kγ c phiConst M = Expander.csPhiOut Kγ c (1 / (c : ℝ)) M := by
    unfold Expander.csPhiOut
    have h₁ := (min_le_right (1 / 2 : ℝ) (Cited.csPhi Kγ c (3 * M))).trans hphi
    have h₂ := (min_le_right (1 / 2 : ℝ) (Cited.csPhi Kγ c (3 * M))).trans hle
    rw [min_eq_right h₁, min_eq_right h₂]
  unfold Expander.csGammaExpPath
  rw [he]

/-- Encode the rational witness conductance using its fixed denominator
and the runtime working scale. -/
@[expose] def initSparsifierWitnessConductanceBounds (den : ℕ) : Stmt :=
  .assign 56 (.bin .div (.reg 4) (.const den)) ;;
  .assign 57 (.bin .div (.bin .add (.reg 4) (.bin .sub (.const den) (.const 1))) (.const den))

/-- The two scaled words enclose the rational witness conductance. -/
theorem initSparsifierWitnessConductanceBounds_runs {w scale den : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hs : st.regs 4 = scale)
    (hpos : 0 < den) (hscale : 0 < scale) (hw : 1 < 2 ^ w)
    (hd : den < 2 ^ w) (hfit : scale + (den - 1) < 2 ^ w) :
    ∃ out, Runs w p ω (initSparsifierWitnessConductanceBounds den) st .normal out 13 ∧
      (out.regs 56 : ℝ) / scale ≤ 1 / (den : ℝ) ∧ 1 / (den : ℝ) ≤ (out.regs 57 : ℝ) / scale ∧
      out.regs 56 = scale / den ∧ out.regs 57 = (scale + (den - 1)) / den ∧
      (den ≤ scale → 0 < out.regs 56) ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 56 → r ≠ 57 → out.regs r = st.regs r) := by
  let lo := scale / den
  let hi := (scale + (den - 1)) / den
  let mid := {st with regs := Function.update st.regs 56 lo}
  let out := {mid with regs := Function.update mid.regs 57 hi}
  have hwlo : scale / den < 2 ^ w := (Nat.div_le_self ..).trans_lt (by omega)
  have hwhi : (scale + (den - 1)) / den < 2 ^ w := (Nat.div_le_self ..).trans_lt hfit
  have hr₁ : Runs w p ω (.assign 56 (.bin .div (.reg 4) (.const den))) st .normal mid 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hs, hd, lo, hwlo], rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω
      (.assign 57 (.bin .div (.bin .add (.reg 4) (.bin .sub (.const den) (.const 1))) (.const den)))
      mid .normal out 8 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, mid, hs, hd, hw,
      show den - 1 < 2 ^ w by omega, hfit, hi, hwhi], rfl, rfl, rfl⟩
  have hLo : out.regs 56 = lo := by simp [out, mid]
  have hHi : out.regs 57 = hi := by simp [out]
  have hround : scale ≤ hi * den := by
    have hm := Nat.mod_lt (scale + (den - 1)) hpos
    have he := Nat.mod_add_div (scale + (den - 1)) den
    rw [Nat.mul_comm den] at he
    change (scale + (den - 1)) % den + hi * den = scale + (den - 1) at he
    omega
  have hd' : (0 : ℝ) < den := by exact_mod_cast hpos
  have hs' : (0 : ℝ) < scale := by exact_mod_cast hscale
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 4, 8, hr₁, hr₂, rfl⟩), ?_, ?_,
    hLo, hHi, ?_, rfl, fun r h56 h57 => by simp [out, mid, h56, h57]⟩
  · rw [hLo]
    exact (div_le_div_iff₀ hs' hd').mpr (by
      simpa only [one_mul] using (show (lo : ℝ) * den ≤ scale by
        exact_mod_cast Nat.div_mul_le_self scale den))
  · rw [hHi]
    exact (div_le_div_iff₀ hd' hs').mpr (by
      simpa only [one_mul] using (show (scale : ℝ) ≤ (hi : ℝ) * den by exact_mod_cast hround))
  · intro he
    rw [hLo]
    exact Nat.div_pos he hpos

/-- Prepare both conductance intervals and the witness edge cap. -/
@[expose] def prepareInitSparsifierPathInputsWithDegree (K thr c cDeg : ℕ) : Stmt :=
  prepareInitSparsifierConductanceWithDegree K thr cDeg ;; initSparsifierWitnessConductanceBounds c

/-- The input and witness path calls use outward bounds at one scale
and share the same witness edge cap. -/
theorem prepareInitSparsifierPathInputsWithDegree_runs {w K thr c M scale cDeg : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hK : 1 ≤ K) (hM : st.regs 23 = M) (hs : st.regs 4 = scale) (hsPos : 0 < scale)
    (hm : 4 * M + 2 < 2 ^ w) (hcube : (Nat.log 2 (4 * M + 2) + 2) ^ 3 < 2 ^ w)
    (hcPos : 0 < cDeg) (hcWord : cDeg < 2 ^ w)
    (hcoeff : cDeg * Expander.maxPhiDenOf K thr M < 2 ^ w)
    (hfit : cDeg * Expander.maxPhiDenOf K thr M * M + 1 < 2 ^ w)
    (hden : Expander.maxPhiDenOf K thr M ≤ scale)
    (hround : scale + (Expander.maxPhiDenOf K thr M - 1) < 2 ^ w)
    (hc : 0 < c) (hcScale : c ≤ scale) (hcRound : scale + (c - 1) < 2 ^ w) :
    let den := Expander.maxPhiDenOf K thr M
    ∃ out cost, Runs w p ω (prepareInitSparsifierPathInputsWithDegree K thr c cDeg) st .normal out cost ∧
      out.regs 63 = den ∧ out.regs 58 = Spanner.capM_W cDeg (1 / (den : ℝ)) M ∧
      (out.regs 53 : ℝ) / scale ≤ 1 / (den : ℝ) ∧ 1 / (den : ℝ) ≤ (out.regs 54 : ℝ) / scale ∧
      (out.regs 56 : ℝ) / scale ≤ 1 / (c : ℝ) ∧ 1 / (c : ℝ) ≤ (out.regs 57 : ℝ) / scale ∧
      out.regs 53 = scale / den ∧ out.regs 54 = (scale + (den - 1)) / den ∧
      out.regs 56 = scale / c ∧ out.regs 57 = (scale + (c - 1)) / c ∧
      0 < out.regs 53 ∧ 0 < out.regs 56 ∧ out.mem = st.mem ∧
      (∀ r, r ∉ ([24, 31, 32, 33, 36, 53, 54, 56, 57, 58, 63] : List ℕ) → out.regs r = st.regs r) ∧
      cost ≤ 120 * (Nat.log 2 (4 * M + 2) + K * (Expander.rOf (4 * M)) ^ 2 + 4) + 42 := by
  obtain ⟨mid, cost, hr₁, h63, h58, lb, ub, h53, h54, hp, hm₁, hk₁, hc₁⟩ :=
    prepareInitSparsifierConductanceWithDegree_runs (ω := ω) hK hM hs hsPos hm hcube hcPos hcWord hcoeff hfit hden hround
  obtain ⟨out, hr₂, lb', ub', h56, h57, hp', hm₂, hk₂⟩ :=
    initSparsifierWitnessConductanceBounds_runs (p := p) (ω := ω)
      ((hk₁ 4 (by decide)).trans hs) hc hsPos (by omega) (by omega) hcRound
  have h53' := hk₂ 53 (by decide) (by decide)
  have h54' := hk₂ 54 (by decide) (by decide)
  refine ⟨out, cost + 14, runs_seq_iff.mpr (Or.inr ⟨mid, cost, 13, hr₁, hr₂, by omega⟩),
    (hk₂ 63 (by decide) (by decide)).trans h63,
    (hk₂ 58 (by decide) (by decide)).trans h58, h53'.symm ▸ lb, h54'.symm ▸ ub, lb', ub',
    h53'.trans h53, h54'.trans h54, h56, h57, h53'.symm ▸ hp, hp' hcScale, hm₂.trans hm₁, ?_, by omega⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h24, h31, h32, h33, h36, h53', h54', h56', h57', h58', h63⟩ := hr
  exact (hk₂ r h56' h57').trans (hk₁ r (by simp [h24, h31, h32, h33, h36, h53', h54', h58', h63]))

/-- Prepare both conductance intervals and the witness edge cap. -/
@[expose] def prepareInitSparsifierPathInputs (K thr c : ℕ) : Stmt :=
  prepareInitSparsifierPathInputsWithDegree K thr c 36

/-- The input and witness path calls use outward bounds at one scale
and share the same witness edge cap. -/
theorem prepareInitSparsifierPathInputs_runs {w K thr c M scale : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hK : 1 ≤ K) (hM : st.regs 23 = M) (hs : st.regs 4 = scale) (hsPos : 0 < scale)
    (hm : 4 * M + 2 < 2 ^ w) (hcube : (Nat.log 2 (4 * M + 2) + 2) ^ 3 < 2 ^ w)
    (hcoeff : 36 * Expander.maxPhiDenOf K thr M < 2 ^ w)
    (hfit : 36 * Expander.maxPhiDenOf K thr M * M + 1 < 2 ^ w)
    (hden : Expander.maxPhiDenOf K thr M ≤ scale)
    (hround : scale + (Expander.maxPhiDenOf K thr M - 1) < 2 ^ w)
    (hc : 0 < c) (hcScale : c ≤ scale) (hcRound : scale + (c - 1) < 2 ^ w) :
    let den := Expander.maxPhiDenOf K thr M
    ∃ out cost, Runs w p ω (prepareInitSparsifierPathInputs K thr c) st .normal out cost ∧
      out.regs 63 = den ∧ out.regs 58 = Spanner.capM_W 36 (1 / (den : ℝ)) M ∧
      (out.regs 53 : ℝ) / scale ≤ 1 / (den : ℝ) ∧ 1 / (den : ℝ) ≤ (out.regs 54 : ℝ) / scale ∧
      (out.regs 56 : ℝ) / scale ≤ 1 / (c : ℝ) ∧ 1 / (c : ℝ) ≤ (out.regs 57 : ℝ) / scale ∧
      out.regs 53 = scale / den ∧ out.regs 54 = (scale + (den - 1)) / den ∧
      out.regs 56 = scale / c ∧ out.regs 57 = (scale + (c - 1)) / c ∧
      0 < out.regs 53 ∧ 0 < out.regs 56 ∧ out.mem = st.mem ∧
      (∀ r, r ∉ ([24, 31, 32, 33, 36, 53, 54, 56, 57, 58, 63] : List ℕ) → out.regs r = st.regs r) ∧
      cost ≤ 120 * (Nat.log 2 (4 * M + 2) + K * (Expander.rOf (4 * M)) ^ 2 + 4) + 42 := by
  exact prepareInitSparsifierPathInputsWithDegree_runs hK hM hs hsPos hm hcube
    (by decide) (by have := Expander.maxPhiDenOf_pos K thr M; omega)
    hcoeff hfit hden hround hc hcScale hcRound

end MinCostFlow.MinRatio
