module

public import MinCostFlow.MinRatio.InitCertifiedWordBudget
import MinCostFlow.MinRatio.ShiftForestScan

/-!
# Solver initialization with the integer rebuild table

After bucket initialization and sparsifier preparation, compute the
endpoint product, certify the rebuild table, and enter level construction.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain

/-- Re-encode the exact sparsifier length at the new workspace scale. -/
@[expose] def rescaleCertifiedSparsifierLength : Stmt :=
  .assign 50 (.bin .mul (.reg 4) (.reg 35)) ;;
  .assign 52 (.reg 50) ;; .assign 25 (.const 1)

/-- Both endpoints remain exact after changing the scale. -/
theorem rescaleCertifiedSparsifierLength_runs
    {w scale growth : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (h4 : st.regs 4 = scale) (h35 : st.regs 35 = growth)
    (hOne : 1 < 2 ^ w) (hw : scale * growth < 2 ^ w) :
    ∃ out, Runs w p ω rescaleCertifiedSparsifierLength st .normal out 10 ∧
      out.regs 50 = scale * growth ∧ out.regs 52 = scale * growth ∧ out.regs 25 = 1 ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 50 → r ≠ 52 → r ≠ 25 → out.regs r = st.regs r) := by
  let mid := {st with regs := Function.update st.regs 50 (scale * growth)}
  let ready := {mid with regs := Function.update mid.regs 52 (scale * growth)}
  let out := {ready with regs := Function.update ready.regs 25 1}
  have hr : Runs w p ω (.assign 50 (.bin .mul (.reg 4) (.reg 35))) st .normal mid 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, h4, h35, hw], rfl, rfl, rfl⟩
  have ht : Runs w p ω (.assign 52 (.reg 50)) mid .normal ready 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, mid], rfl, rfl, rfl⟩
  have hu : Runs w p ω (.assign 25 (.const 1)) ready .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hOne], rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 4, 5, hr,
    runs_seq_iff.mpr (Or.inr ⟨ready, 2, 2, ht, hu, rfl⟩), rfl⟩),
    by simp [out, ready, mid], by simp [out, ready], by simp [out], rfl,
    fun r h50 h52 h25 => by simp [out, ready, mid, h50, h52, h25]⟩

/-- Install the exact length at the workspace scale while keeping the
input cursor, graph dimensions, and saved solver arguments. -/
theorem certifiedEndpointWorkspace_rescale_runs
    {w power bits clog coefficient h workspaceCost precision limbs growth vertices : ℕ}
    {p : Program} {ω : ℕ → Bool} {st work : State}
    (hwork : Runs w p ω (initCertifiedEndpointWorkspace power bits clog coefficient h)
      st .normal work workspaceCost)
    (hP : work.regs 68 = precision) (hL : work.regs 67 = limbs)
    (hscale : work.regs 4 = 2 ^ precision) (hg : work.regs 35 = growth)
    (hN : work.regs 92 = vertices) (hm : work.mem = st.mem)
    (hw : 1 < 2 ^ w) (hfit : 2 ^ precision * growth < 2 ^ w) :
    ∃ out, Runs w p ω rescaleCertifiedSparsifierLength work .normal out 10 ∧
      out.regs 68 = precision ∧ out.regs 67 = limbs ∧ out.regs 4 = 2 ^ precision ∧
      out.regs 50 = 2 ^ precision * growth ∧ out.regs 52 = 2 ^ precision * growth ∧
      out.regs 25 = 1 ∧ out.regs 92 = vertices ∧ out.mem = st.mem ∧
      out.regs 22 = st.regs 22 ∧ out.regs 75 = st.regs 75 ∧ out.regs 98 = st.regs 98 ∧
      (∀ r, 101 ≤ r → r ≤ 104 → out.regs r = st.regs r) := by
  obtain ⟨out, hr, h50, h52, h25, hout, hkeep⟩ :=
    rescaleCertifiedSparsifierLength_runs (p := p) (ω := ω) hscale hg hw hfit
  have keep (r : ℕ) (h₅₀ : r ≠ 50 := by decide) (h₅₂ : r ≠ 52 := by decide)
      (h₂₅ : r ≠ 25 := by decide) := hkeep r h₅₀ h₅₂ h₂₅
  refine ⟨out, hr, (keep 68).trans hP, (keep 67).trans hL, (keep 4).trans hscale,
    h50, h52, h25, (keep 92).trans hN, hout.trans hm,
    (keep 22).trans (runs_preserves_register rfl hwork),
    (keep 75).trans (runs_preserves_register rfl hwork),
    (keep 98).trans (runs_preserves_register rfl hwork), ?_⟩
  intro r h₁ h₂
  have hk : work.regs r = st.regs r := by
    interval_cases r <;> exact runs_preserves_register rfl hwork
  exact (keep r (by omega) (by omega) (by omega)).trans hk

/-- Preserve the solver format, query-factor scale, edge count, and stability width. -/
@[expose] def saveCertifiedThresholdFormat : Stmt :=
  saveInitDepthNumericFormat ;; .assign 130 (.reg 4) ;; .assign 131 (.reg 0) ;; .assign 132 (.reg 6)

/-- Saving leaves the original format registers and allocation cursor intact. -/
theorem saveCertifiedThresholdFormat_runs
    {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State} :
    ∃ out, Runs w p ω saveCertifiedThresholdFormat st .normal out 14 ∧
      out.regs 128 = st.regs 67 ∧ out.regs 129 = st.regs 68 ∧ out.regs 130 = st.regs 4 ∧
      out.regs 131 = st.regs 0 ∧ out.regs 132 = st.regs 6 ∧
      out.mem = st.mem ∧ (∀ r, r ≠ 128 → r ≠ 129 → r ≠ 130 → r ≠ 131 → r ≠ 132 → out.regs r = st.regs r) := by
  obtain ⟨mid, hr, h128, h129, hm, hk⟩ :=
    saveInitDepthNumericFormat_runs (w := w) (p := p) (ω := ω) (st := st)
  let s1 := {mid with regs := Function.update mid.regs 130 (st.regs 4)}
  let s2 := {s1 with regs := Function.update s1.regs 131 (st.regs 0)}
  let out := {s2 with regs := Function.update s2.regs 132 (st.regs 6)}
  have ht1 : Runs w p ω (.assign 130 (.reg 4)) mid .normal s1 2 :=
    runs_assign_iff.mpr ⟨_, congrArg some (hk 4 (by decide) (by decide)), rfl, rfl, rfl⟩
  have ht2 : Runs w p ω (.assign 131 (.reg 0)) s1 .normal s2 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s1, hk 0 (by decide) (by decide)], rfl, rfl, rfl⟩
  have ht3 : Runs w p ω (.assign 132 (.reg 6)) s2 .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s2, s1, hk 6 (by decide) (by decide)], rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 5, 8, hr,
    runs_seq_iff.mpr (Or.inr ⟨s1, 2, 5, ht1, runs_seq_iff.mpr (Or.inr ⟨s2, 2, 2, ht2, ht3, rfl⟩), rfl⟩), rfl⟩),
    by simpa [out, s2, s1] using h128, by simpa [out, s2, s1] using h129,
    by simp [out, s2, s1], by simp [out, s2], by simp [out], hm,
    fun r h1 h2 h3 h4 h5 => by simpa [out, s2, s1, h3, h4, h5] using hk r h1 h2⟩

/-- Restore the solver format, edge count, and stability width without changing the table cursor. -/
@[expose] def restoreCertifiedThresholdFormat : Stmt :=
  .assign 67 (.reg 128) ;; .assign 68 (.reg 129) ;; .assign 4 (.reg 130) ;; .assign 0 (.reg 131) ;; .assign 6 (.reg 132)

/-- The restore step changes only the saved header and format registers. -/
theorem restoreCertifiedThresholdFormat_runs
    {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State} :
    ∃ out, Runs w p ω restoreCertifiedThresholdFormat st .normal out 14 ∧
      out.regs 67 = st.regs 128 ∧ out.regs 68 = st.regs 129 ∧ out.regs 4 = st.regs 130 ∧
      out.regs 0 = st.regs 131 ∧ out.regs 6 = st.regs 132 ∧
      out.mem = st.mem ∧ (∀ r, r ≠ 67 → r ≠ 68 → r ≠ 4 → r ≠ 0 → r ≠ 6 → out.regs r = st.regs r) := by
  let s1 := {st with regs := Function.update st.regs 67 (st.regs 128)}
  let s2 := {s1 with regs := Function.update s1.regs 68 (st.regs 129)}
  let s3 := {s2 with regs := Function.update s2.regs 4 (st.regs 130)}
  let s4 := {s3 with regs := Function.update s3.regs 0 (st.regs 131)}
  let out := {s4 with regs := Function.update s4.regs 6 (st.regs 132)}
  have hr1 : Runs w p ω (.assign 67 (.reg 128)) st .normal s1 2 := runs_assign_iff.mpr ⟨_, rfl, rfl, rfl, rfl⟩
  have hr2 : Runs w p ω (.assign 68 (.reg 129)) s1 .normal s2 2 := runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s1], rfl, rfl, rfl⟩
  have hr3 : Runs w p ω (.assign 4 (.reg 130)) s2 .normal s3 2 := runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s2, s1], rfl, rfl, rfl⟩
  have hr4 : Runs w p ω (.assign 0 (.reg 131)) s3 .normal s4 2 := runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s3, s2, s1], rfl, rfl, rfl⟩
  have hr5 : Runs w p ω (.assign 6 (.reg 132)) s4 .normal out 2 := runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s4, s3, s2, s1], rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨s1, 2, 11, hr1, runs_seq_iff.mpr (Or.inr ⟨s2, 2, 8, hr2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 2, 5, hr3, runs_seq_iff.mpr (Or.inr ⟨s4, 2, 2, hr4, hr5, rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    by simp [out, s4, s3, s2, s1], by simp [out, s4, s3, s2], by simp [out, s4, s3],
    by simp [out, s4], by simp [out], rfl,
    fun r h67 h68 h4 h0 h6 => by simp [out, s4, s3, s2, s1, h67, h68, h4, h0, h6]⟩

/-- Compute both endpoint intervals at one installed precision,
passing the fresh heap cursor from the coefficient to the logarithm. -/
theorem prepareCertifiedThresholdEndpoints_numeric_runs
    (E : SparseCore.SparseCoreEnv) (M : ℕ)
    {w h bits load log pack coefficient clog N precision limbs heap depth : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hclog : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (hLog : p.HasAt log (Num.logarithmModule log h)) (hLogWord : 3 * h + 2 ≤ w)
    (h92 : st.regs 92 = N) (h4 : st.regs 4 = 2 ^ precision)
    (h67 : st.regs 67 = limbs) (h68 : st.regs 68 = precision) (h98 : st.regs 98 = heap)
    (h22 : st.regs 22 = M) (h25 : st.regs 25 = (E.P_fn (M ^ 2)).p_s)
    (hps : (E.P_fn (M ^ 2)).p_s ≤ 1)
    (h75 : st.regs 75 = depth) (hDepth : 2 * (depth + 1) + 1 < 2 ^ w)
    (hCoarse : concreteThresholdScale depth < 2 ^ w)
    (hprec : 16 ≤ precision) (hdiv : h ∣ precision)
    (hh : 0 < h)
    (hz : ZeroFrom st.mem heap)
    (hword : (coefficient + 3) * (2 ^ precision) ^ 2 < 2 ^ w)
    (hMpos : 0 < M) :
    let input := SparseCore.coreNMax (M ^ 2) + M ^ 2
    let range := (input + 2).size
    let room := heap + limbs + limbs + Num.logarithmSpace limbs precision 2
    (input + 3) * 2 ^ precision < 2 ^ w →
    limbs = precision + range + 4 →
    room + limbs + limbs + Num.logarithmSpace limbs precision range +
      (39 * limbs + 3 * (depth + 1) + 17) < 2 ^ w →
    range + 11 ≤ precision →
    ∃ out cost ret,
      Runs w p ω (prepareCertifiedThresholdEndpoints bits load log pack coefficient clog)
        st .normal out cost ∧
      (out.regs 49 : ℝ) / (2 ^ precision : ℕ) ≤ 1 + coefficient / Real.log 2 ∧
      1 + coefficient / Real.log 2 ≤ (out.regs 51 : ℝ) / (2 ^ precision : ℕ) ∧
      out.regs 49 ≤ out.regs 51 ∧ out.regs 51 ≤ (2 * coefficient + 2) * 2 ^ precision ∧
      out.regs 51 - out.regs 49 ≤ 65536 * coefficient + 2 ∧
      (out.regs 26 : ℝ) / (2 ^ precision : ℕ) ≤ SparseCore.coreLambdaS (E.P_fn (M ^ 2)) (M ^ 2) ∧
      SparseCore.coreLambdaS (E.P_fn (M ^ 2)) (M ^ 2) ≤ (out.regs 27 : ℝ) / (2 ^ precision : ℕ) ∧
      out.regs 26 ≤ out.regs 27 ∧ out.regs 27 ≤ (input + 3) * 2 ^ precision ∧
      out.regs 27 - out.regs 26 ≤ 4096 * (input + 2) ∧
      out.regs 4 = 2 ^ precision ∧ out.regs 30 = concreteThresholdScale depth ∧
      out.regs 119 = Nat.clog 2 (2 * (depth + 1)) ∧ out.regs 99 = ret ∧
      out.regs 92 = N ∧ heap ≤ ret ∧ ret ≤ room + limbs + limbs + Num.logarithmSpace limbs precision range ∧
      ret + 39 * limbs + 3 * (depth + 1) + 17 < 2 ^ w ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem ret ∧
      cost ≤ 142 * limbs + Num.logarithmCost limbs precision 2 +
        Num.logarithmCost limbs precision range + 14 * range + 40 * Nat.clog 2 (2 * (depth + 1)) + 315 := by
  dsimp only
  intro hEndpoint hWorkspace hRoom hguard
  have hpow := (Nat.le_mul_of_pos_left (2 ^ precision) (by omega : 0 < coefficient + 3)).trans
    (Nat.mul_le_mul_left (coefficient + 3) (Nat.le_self_pow (by decide : 2 ≠ 0) (2 ^ precision)))
  have hwidth : precision < w :=
    (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (hpow.trans_lt hword)
  have hprecWord : 2 * precision + 9 < 2 ^ w := by
    have hsmall : precision ≤ 2 ^ precision := Nat.lt_two_pow_self.le
    have hlarge : 9 ≤ 2 ^ precision :=
      (by decide : 9 ≤ 2 ^ 16).trans (Nat.pow_le_pow_right (by decide) hprec)
    calc
      _ ≤ 3 * 2 ^ precision := by omega
      _ ≤ (coefficient + 3) * (2 ^ precision) ^ 2 :=
        Nat.mul_le_mul (by omega) (Nat.le_self_pow (by decide) _)
      _ < _ := hword
  have hInputWord : (SparseCore.coreNMax (M ^ 2) + M ^ 2 + 2) * 2 ^ precision < 2 ^ w :=
    (Nat.mul_le_mul_right _ (by omega)).trans_lt hEndpoint
  have hInput : SparseCore.coreNMax (M ^ 2) + M ^ 2 + 2 < 2 ^ w :=
    (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos precision)).trans_lt hInputWord
  have hInputEq : M ^ 2 * (2 * M ^ 2 + 60) = SparseCore.coreNMax (M ^ 2) + M ^ 2 := by
    unfold SparseCore.coreNMax SparseCore.coreSplitMax
    ring
  have hproduct : M ^ 2 * (2 * M ^ 2 + 60) < 2 ^ w := by rw [hInputEq]; omega
  have hlinear := (Nat.le_mul_of_pos_left _ (Nat.pow_pos hMpos)).trans_lt hproduct
  have hMw := (Nat.le_mul_of_pos_right (M ^ 2) (by omega : 0 < 2 * M ^ 2 + 60)).trans_lt hproduct
  have hw : 60 < 2 ^ w := by omega
  obtain ⟨hLimb, hfit, hInputFit, _⟩ := certifiedEndpointWorkspace_log_capacity
    (input := SparseCore.coreNMax (M ^ 2) + M ^ 2) (precision := precision) hh
  rw [← hWorkspace] at hLimb hfit hInputFit
  have hRange : 2 ≤ (SparseCore.coreNMax (M ^ 2) + M ^ 2 + 2).size := by
    by_contra! hn
    have hn' := Nat.size_le.mp (show (SparseCore.coreNMax (M ^ 2) + M ^ 2 + 2).size ≤ 1 by omega)
    omega
  have hcap : precision + 6 ≤ h * limbs := by omega
  obtain ⟨mid, c₁, cursor, hr, hklo, hkhi, hkOrd, hkUpper, hkGap, hScale, hCur,
    hN, hCurLo, hCurHi, hf, hzero, hk, hc₁⟩ :=
    initRebuildCoefficient_runs (ω := ω) hbits hload hpack (Num.logarithm_meetsContract hh hLogWord hLog) h92 h4 h67 h68 h98
      hprec hwidth hdiv hcap hprecWord hfit (by omega) hz hword
  have keep₁ (r : ℕ) (hr : r < 95 := by decide)
      (hn : r ∉ ([2, 3, 4, 28, 29, 37, 49, 51, 57] : List ℕ) := by decide) := hk r hr hn
  obtain ⟨ready, c₂, ret, ht, hllo, hlhi, _, _, hlOrd, hlUpper, hlGap, hs, h92',
    _, h99, hretLo, _, hretHi, hk', hf', hz', hc₂⟩ :=
    initSparseCoreLogForThresholds_runs (ω := ω) E M hbits hload hpack ((keep₁ 25).trans h25)
      hps hwidth ((keep₁ 22).trans h22) hN hScale ((keep₁ 67).trans h67)
      ((keep₁ 68).trans h68) hCur hMw hw hlinear hproduct (Num.logarithm_meetsContract hh hLogWord hLog) hInput hInputWord hInputFit
      (by omega) hzero hdiv hguard (hWorkspace ▸ hLimb) hprecWord hEndpoint
  have keep₂ (r : ℕ) (hr : r < 95 := by decide)
      (hn : r ∉ ([2, 3, 4, 24, 26, 27, 57, 77] : List ℕ) := by decide) := hk' r hr hn
  obtain ⟨out, c₃, hu, h30, h119, hm, hk'', hc₃⟩ :=
    prepareCertifiedThresholdScale_runs (ω := ω) hclog ((keep₂ 75).trans ((keep₁ 75).trans h75))
      hDepth hCoarse
  have keep₃ (r : ℕ) (ha : r ≠ 30 := by decide) (hb : r ≠ 119 := by decide) := hk'' r ha hb
  have h49 := (keep₃ 49).trans (keep₂ 49)
  have h51 := (keep₃ 51).trans (keep₂ 51)
  have h26 := keep₃ 26
  have h27 := keep₃ 27
  refine ⟨out, c₁ + c₂ + c₃ + 2, ret, prepareCertifiedThresholdEndpoints_runs hr ht hu,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, (keep₃ 4).trans hs, h30, h119,
    (keep₃ 99).trans h99, (keep₃ 92).trans h92', by omega, by omega, by omega, ?_, hm.symm ▸ hz', by omega⟩
  · simpa only [h49] using hklo
  · simpa only [h51] using hkhi
  · simpa only [h49, h51] using hkOrd
  · simpa only [h51] using hkUpper
  · simpa only [h49, h51] using hkGap
  · simpa only [h26] using hllo
  · simpa only [h27] using hlhi
  · simpa only [h26, h27] using hlOrd
  · simpa only [h27] using hlUpper
  · simpa only [h26, h27] using hlGap
  · exact fun a ha => (congrFun hm a).trans ((hf' a (by omega)).trans (hf a ha))

/-- A word bounded by the square of the endpoint scale fits in the
signed endpoint workspace when the limb width is at least two. -/
theorem certifiedEndpointTable_signed_fit {h limbs precision value : ℕ}
    (hh : 2 ≤ h) (hL : precision + 4 ≤ limbs)
    (hvalue : value ≤ (2 ^ precision) ^ 2) :
    2 * value < Num.capacity h limbs := by
  have hbits : 2 * precision + 1 < h * limbs := by
    have hprod := Nat.mul_le_mul hh hL
    omega
  calc
    _ ≤ 2 * (2 ^ precision) ^ 2 := Nat.mul_le_mul_left _ hvalue
    _ = 2 ^ (2 * precision + 1) := by
      rw [Nat.mul_comm 2 ((2 ^ precision) ^ 2), ← pow_mul, ← pow_succ, Nat.mul_comm precision 2]
    _ < _ := by
      rw [Num.capacity, Num.base, ← pow_mul]
      exact Nat.pow_lt_pow_right (by decide) hbits

/-- The workspace precision makes the scale dominate each of the
unscaled load bounds used by the table writer. -/
theorem certifiedEndpointTable_scale_bounds (depth factor coefficient input h : ℕ)
    (hh : 0 < h) :
    let minimum := Nat.clog 2 (2 * (depth + 1)) + Nat.clog 2 factor +
      (17 + Nat.clog 2 (coefficient + 1) + Nat.clog 2 (input + 3))
    let precision := (minimum + (h - 1)) / h * h
    2 ≤ 2 ^ precision ∧ 2 * coefficient + 2 ≤ 2 ^ precision ∧
      input + 3 ≤ 2 ^ precision ∧ factor ≤ 2 ^ precision := by
  dsimp only
  let minimum := Nat.clog 2 (2 * (depth + 1)) + Nat.clog 2 factor +
    (17 + Nat.clog 2 (coefficient + 1) + Nat.clog 2 (input + 3))
  let precision := (minimum + (h - 1)) / h * h
  have hmod := Nat.mod_lt (minimum + (h - 1)) hh
  have hdiv := Nat.mod_add_div (minimum + (h - 1)) h
  rw [Nat.mul_comm h] at hdiv
  change (minimum + (h - 1)) % h + precision = _ at hdiv
  have hmin : minimum ≤ precision := by omega
  have power (x : ℕ) (hx : Nat.clog 2 x ≤ precision) : x ≤ 2 ^ precision :=
    (Nat.le_pow_clog (by decide) x).trans (Nat.pow_le_pow_right (by decide) hx)
  have hc : 2 * coefficient + 2 ≤ 2 ^ (Nat.clog 2 (coefficient + 1) + 1) := by
    calc
      _ = (coefficient + 1) * 2 := by omega
      _ ≤ 2 ^ Nat.clog 2 (coefficient + 1) * 2 :=
        Nat.mul_le_mul_right 2 (Nat.le_pow_clog (by decide) _)
      _ = _ := (pow_succ 2 _).symm
  change 2 ≤ 2 ^ precision ∧ 2 * coefficient + 2 ≤ 2 ^ precision ∧
    input + 3 ≤ 2 ^ precision ∧ factor ≤ 2 ^ precision
  dsimp [minimum] at hmin
  exact ⟨power 2 (by change 1 ≤ precision; omega),
    hc.trans (Nat.pow_le_pow_right (by decide) (by omega)),
    power _ (by omega), power _ (by omega)⟩

/-- Transfer the endpoint and multiplier bounds to the signed loads
used by the table writer. -/
theorem certifiedEndpointTable_load_bounds
    {w h limbs precision coefficient input factor ku lu : ℕ}
    (hh : 2 ≤ h) (hL : precision + 4 ≤ limbs)
    (hscale : 2 ≤ 2 ^ precision)
    (hkScale : 2 * coefficient + 2 ≤ 2 ^ precision)
    (hlScale : input + 3 ≤ 2 ^ precision) (hfScale : factor ≤ 2 ^ precision)
    (hku : ku ≤ (2 * coefficient + 2) * 2 ^ precision)
    (hlu : lu ≤ (input + 3) * 2 ^ precision)
    (hkWord : (coefficient + 3) * (2 ^ precision) ^ 2 < 2 ^ w)
    (hlWord : (input + 3) * 2 ^ precision < 2 ^ w) :
    ku < 2 ^ w ∧ lu < 2 ^ w ∧
      2 * ku < Num.capacity h limbs ∧ 2 * lu < Num.capacity h limbs ∧
      2 * factor < Num.capacity h limbs := by
  have hSq : 2 ^ precision ≤ (2 ^ precision) ^ 2 := Nat.le_self_pow (by decide) _
  have hkMul : 2 * coefficient + 2 ≤ (coefficient + 3) * 2 ^ precision :=
    (show 2 * coefficient + 2 ≤ (coefficient + 3) * 2 by omega).trans
      (Nat.mul_le_mul_left _ hscale)
  have hku' : ku < 2 ^ w := hku.trans_lt (lt_of_le_of_lt
    (by rw [pow_two, ← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ hkMul) hkWord)
  refine ⟨hku', hlu.trans_lt hlWord, ?_, ?_, certifiedEndpointTable_signed_fit hh hL (hfScale.trans hSq)⟩
  · exact certifiedEndpointTable_signed_fit hh hL (hku.trans (by
      rw [pow_two]; exact Nat.mul_le_mul_right _ hkScale))
  · exact certifiedEndpointTable_signed_fit hh hL (hlu.trans (by
      rw [pow_two]; exact Nat.mul_le_mul_right _ hlScale))

/-- The top-level growth bound also bounds the integer affine multiplier,
the sparsifier depth, and the unscaled path length used in workspace sizing. -/
theorem certifiedSparseCoreGrowth_le_top (E : SparseCore.SparseCoreEnv)
    {M growth : ℕ} (hg : 0 < growth) (hGrowth : (E.P_fn (M ^ 2)).γ_ℓ = growth)
    (hK : 1 ≤ (E.P_fn (M ^ 2)).K_s)
    (hTop : (SparseCore.sparseCoreParams E).γ_ℓ (M ^ 2) ≤ M) :
    let factor := 11 * (E.L + 1) * growth * E.B_fn (M ^ 2) * (2 * E.d_fn (M ^ 2) + 190)
    factor ≤ M ∧ E.L + 1 ≤ M ∧ growth ≤ M := by
  dsimp only
  let m := M ^ 2
  let factor := 11 * (E.L + 1) * growth * E.B_fn m * (2 * E.d_fn m + 190)
  have hprod : (1 : ℝ) ≤ (E.P_fn m).K_s * SparseCore.coreLambdaS (E.P_fn m) m := by
    simpa using mul_le_mul hK (SparseCore.coreLambdaS_ge_one (E.P_fn m) m) (by norm_num)
      (by linarith only [hK] : 0 ≤ (E.P_fn m).K_s)
  have hcast : (factor : ℝ) ≤ (M : ℝ) := by
    calc
      _ ≤ (factor : ℝ) * ((E.P_fn m).K_s * SparseCore.coreLambdaS (E.P_fn m) m) := by
        exact le_mul_of_one_le_right (Nat.cast_nonneg _) hprod
      _ ≤ (SparseCore.sparseCoreParams E).γ_ℓ m := by
        apply le_trans _ (le_max_right _ _)
        change _ ≤ 11 * (((E.L : ℝ) + 1) * (E.P_fn m).K_s * (E.P_fn m).γ_ℓ *
          SparseCore.coreLambdaS (E.P_fn m) m * (E.B_fn m : ℝ) * (2 * (E.d_fn m : ℝ) + 190) + 115)
        rw [show (E.P_fn m).γ_ℓ = growth from hGrowth]
        dsimp only [factor]
        push_cast
        linarith
      _ ≤ _ := hTop
  have hf : factor ≤ M := Nat.cast_le.mp hcast
  have hb : 0 < E.B_fn m := E.hB_pos m
  have hd : E.L + 1 ≤ factor := by
    calc
      _ ≤ 11 * (E.L + 1) := by omega
      _ ≤ _ := (Nat.le_mul_of_pos_right _ hg).trans
        ((Nat.le_mul_of_pos_right _ hb).trans (Nat.le_mul_of_pos_right _ (by omega)))
  have hG : growth ≤ factor := by
    calc
      _ ≤ 11 * (E.L + 1) * growth := Nat.le_mul_of_pos_left _ (by omega)
      _ ≤ _ := (Nat.le_mul_of_pos_right _ hb).trans (Nat.le_mul_of_pos_right _ (by omega))
  exact ⟨hf, hd.trans hf, hG.trans hf⟩

/-- Run workspace sizing with the concrete top-level growth cap. -/
theorem initCertifiedEndpointWorkspace_atTop_runs
    (E : SparseCore.SparseCoreEnv) (words : List ℕ)
    {w c dd dm power bits clog depth growth coefficient M h vertices : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hp : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (hb : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hM : st.regs 22 = M) (hN : st.regs 92 = vertices) (hpos : 0 < M)
    (hpow : MeetsContract w p power (initStretchPowerContract w))
    (h75 : st.regs 75 = depth) (hDepth : 2 * (depth + 1) + 1 < 2 ^ w)
    (hcoarse : concreteThresholdScale depth < 2 ^ w)
    (h44 : st.regs 44 = E.L) (h50 : st.regs 50 = growth)
    (h4 : st.regs 4 = 1) (hg : 0 < growth)
    (hGrowth : (E.P_fn (M ^ 2)).γ_ℓ = growth) (hK : 1 ≤ (E.P_fn (M ^ 2)).K_s)
    (hTop : (SparseCore.sparseCoreParams E).γ_ℓ (M ^ 2) ≤ M)
    (h47 : st.regs 47 = E.B_fn (M ^ 2)) (h48 : st.regs 48 = E.d_fn (M ^ 2))
    (hh : 0 < h) (hhw : h < 2 ^ w) (hw : 11 < 2 ^ w) :
    let factor := 11 * (E.L + 1) * growth * E.B_fn (M ^ 2) * (2 * E.d_fn (M ^ 2) + 190)
    let input := SparseCore.coreNMax (M ^ 2) + M ^ 2
    let range := (input + 2).size
    let minimum := Nat.clog 2 (2 * (depth + 1)) + Nat.clog 2 factor +
      (17 + Nat.clog 2 (coefficient + 1) + Nat.clog 2 (input + 3))
    let precision := (minimum + (h - 1)) / h * h
    let B := words.length + words.foldr max 0 + 2
    let df := dm
    let di := 7 + 4 * dm
    let ds := 2 * (dd + df + di) + 17 + Nat.clog 2 (coefficient + 1) + (h - 1)
    2 * (depth + 1) ≤ B ^ dd → M + 2 ≤ B ^ dm →
    max (max (df + 1) (di + 1)) (max ds (max ds di + 3)) ≤ c → wordSize c words ≤ w →
    ∃ out cost, Runs w p ω (initCertifiedEndpointWorkspace power bits clog coefficient h)
        st .normal out cost ∧
      out.regs 68 = precision ∧ out.regs 67 = precision + range + 4 ∧ out.regs 4 = 2 ^ precision ∧
      Nat.clog 2 (2 * (depth + 1) * factor *
        ((65536 * coefficient + 2) * (input + 3) +
          (2 * coefficient + 2) * (4096 * (input + 2)))) ≤ precision ∧
      Nat.clog 2 (2 * (depth + 1)) ≤ precision ∧ 16 ≤ precision ∧
      range + 11 ≤ precision ∧ out.regs 35 = growth ∧ out.regs 92 = vertices ∧ h ∣ precision ∧ out.mem = st.mem ∧
      cost ≤ 14 * range + 40 * (Nat.clog 2 factor + Nat.clog 2 (input + 3) +
        Nat.clog 2 (2 * (depth + 1))) + 40 * E.L + 237 := by
  dsimp only
  intro hd hsize hc hword
  let B := words.length + words.foldr max 0 + 2
  have hB : 2 ≤ B := by dsimp [B]; omega
  have hMfit : M + 2 < 2 ^ w := by
    have hdm : dm ≤ c := by omega
    exact (hsize.trans (Nat.pow_le_pow_right (by omega : 0 < B) hdm)).trans_lt
      ((pow_lt_two_pow_wordSize (by omega) words).trans_le (Nat.pow_le_pow_right (by decide) hword))
  obtain ⟨hf, hdepth, hlength⟩ := certifiedSparseCoreGrowth_le_top E hg hGrowth hK hTop
  have hinput : SparseCore.coreNMax (M ^ 2) + M ^ 2 + 3 ≤ B ^ (7 + 4 * dm) := by
    calc
      _ ≤ 65 * (M + 2) ^ 4 := certifiedThresholdLogInput_le M
      _ ≤ B ^ 7 * (B ^ dm) ^ 4 := Nat.mul_le_mul
        ((by decide : 65 ≤ 2 ^ 7).trans (Nat.pow_le_pow_left hB 7))
        (Nat.pow_le_pow_left hsize 4)
      _ = _ := by rw [← pow_mul, ← pow_add, Nat.mul_comm dm 4]
  have hfirst := initSparseCoreFirstGrowth_fits E (M ^ 2) M growth w hGrowth hTop (by omega)
  exact initCertifiedEndpointWorkspace_budgeted_runs words hp hb hM hN hpos hpow h75 hDepth hcoarse
    h44 (by simpa only [one_mul] using h50) h4 (by decide) hg (by omega)
    (by simp only [one_mul]; omega) hfirst h47 h48 (E.hB_pos _) hh hhw hw
    hd (hf.trans ((Nat.le_add_right M 2).trans hsize)) hinput hc hword

/-- Write the threshold table using the workspace precision certificate
and the two computed endpoint intervals. -/
theorem initCertifiedEndpointTable_runs
    (E : SparseCore.SparseCoreEnv) (C : Chain.ChainParams)
    {w power depth buckets degree h load extend mul shift add heap limbs factor precision ku lu round vertices coefficient : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hpower : MeetsContract w p power (initStretchPowerContract w))
    (h44 : st.regs 44 = depth) (hDepth : depth = E.L)
    (h47 : st.regs 47 = buckets) (hBuckets : buckets = E.B_fn (C.M₀ ^ 2))
    (h48 : st.regs 48 = degree) (hDegree : degree = E.d_fn (C.M₀ ^ 2))
    (h4 : st.regs 4 = 2 ^ precision)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hext : MeetsContract w p extend (Num.extendCopyContract w h))
    (hmul : MeetsContract w p mul (Num.multiplyContract w h))
    (hshift : MeetsContract w p shift (Num.shiftLeftContract w h))
    (hadd : MeetsContract w p add (Num.addContract w h))
    (h99 : st.regs 99 = heap) (h67 : st.regs 67 = limbs)
    (h68 : st.regs 68 = precision)
    (h51 : st.regs 51 = ku) (h27 : st.regs 27 = lu)
    (hL : limbs = precision + (SparseCore.coreNMax (C.M₀ ^ 2) + C.M₀ ^ 2 + 2).size + 4)
    (hh : 2 ≤ h)
    (hword : factor < 2 ^ w) (hz : ZeroFrom st.mem heap)
    (hcword : 1265 < 2 ^ w) (hPword : 2 * precision < 2 ^ w)
    (hround : MeetsContract w p round (initDepthEndpointContract w h))
    (h30 : st.regs 30 = concreteThresholdScale C.d)
    (he : st.regs 119 = Nat.clog 2 (2 * (C.d + 1)))
    (hwordH : h < 2 ^ w) (hdvd : h ∣ precision)
    (hePrecision : Nat.clog 2 (2 * (C.d + 1)) ≤ precision)
    (hγM : (SparseCore.sparseCoreParams E).γ_ℓ (C.M₀ ^ 2) ≤ C.M₀)
    (hγk : (SparseCore.sparseCoreParams E).γ_ℓ (C.M₀ ^ 2) ≤ C.k)
    (hbase : heap + 39 * limbs + C.d + 1 < 2 ^ w)
    {growth kl ll : ℕ}
    (hfactor : factor = 11 * (E.L + 1) * growth * E.B_fn (C.M₀ ^ 2) *
      (2 * E.d_fn (C.M₀ ^ 2) + 190))
    (hGrowth : (E.P_fn (C.M₀ ^ 2)).γ_ℓ = growth)
    (h50 : st.regs 50 = 2 ^ precision * growth) (hg : 0 < growth)
    (hb : 0 < buckets) (hDepthWord : max (depth + 1) 3 < 2 ^ w)
    (hScaled : 2 ^ precision * growth < 2 ^ w)
    (hkl : (kl : ℝ) / (2 : ℝ) ^ precision ≤ (E.P_fn (C.M₀ ^ 2)).K_s)
    (hkuBound : (E.P_fn (C.M₀ ^ 2)).K_s ≤ (ku : ℝ) / (2 : ℝ) ^ precision)
    (hll : (ll : ℝ) / (2 : ℝ) ^ precision ≤
      SparseCore.coreLambdaS (E.P_fn (C.M₀ ^ 2)) (C.M₀ ^ 2))
    (hluBound : SparseCore.coreLambdaS (E.P_fn (C.M₀ ^ 2)) (C.M₀ ^ 2) ≤
      (lu : ℝ) / (2 : ℝ) ^ precision)
    (hklOrder : kl ≤ ku) (hllOrder : ll ≤ lu)
    (h22 : st.regs 22 = C.M₀) (h14 : st.regs 14 = Nat.clog 2 (vertices + 2))
    (h76 : st.regs 76 = C.k) (h75 : st.regs 75 = C.d)
    (hden : 3 * C.k * Nat.clog 2 (vertices + 2) ^ 2 < 2 ^ w)
    (hcapacity : (3 * C.M₀ ^ 2 + 1) * (C.M₀ * (2 * concreteThresholdScale C.d) ^ (C.d + 1)) < 2 ^ w) :
    let input := SparseCore.coreNMax (C.M₀ ^ 2) + C.M₀ ^ 2
    let minimum := Nat.clog 2 (2 * (C.d + 1)) + Nat.clog 2 factor +
      (17 + Nat.clog 2 (coefficient + 1) + Nat.clog 2 (input + 3))
    let scale := concreteThresholdScale C.d
    let e := Nat.clog 2 (2 * (C.d + 1))
    let first := 3 ^ E.L * growth ^ (E.L + 1)
    let upper := factor * (ku * lu) + 1265 * 2 ^ (2 * precision)
    let a := max (first * scale) ((upper + 2 ^ (2 * precision - e) - 1) / 2 ^ (2 * precision - e))
    precision = (minimum + (h - 1)) / h * h →
    Nat.clog 2 (2 * (C.d + 1) * factor *
      ((65536 * coefficient + 2) * (input + 3) +
        (2 * coefficient + 2) * (4096 * (input + 2)))) ≤ precision →
    ku ≤ (2 * coefficient + 2) * 2 ^ precision → lu ≤ (input + 3) * 2 ^ precision →
    ku - kl ≤ 65536 * coefficient + 2 → lu - ll ≤ 4096 * (input + 2) →
    (coefficient + 3) * (2 ^ precision) ^ 2 < 2 ^ w →
    (input + 3) * 2 ^ precision < 2 ^ w →
    let base := heap + 39 * limbs
    ∃ out cost, Runs w p ω (initSparseCoreThresholdsFromEndpoints power load extend mul shift add round h)
        st .normal out cost ∧
      out.regs 83 = base ∧ out.regs 98 = base + C.d + 1 ∧
      (∀ j ≤ C.d, out.mem (base + j) = Chain.concreteLevelRebuildCount C.M₀ C.k a scale j vertices ∧
        (out.mem (base + j) : ℝ) ≤ Chain.SparseCoreTool.updateThreshold C.k (Chain.levelM (SparseCore.sparseCoreParams E) C j) vertices ∧
        Chain.SparseCoreTool.updateThreshold C.k (Chain.levelM (SparseCore.sparseCoreParams E) C j) vertices ≤
          48 * ((out.mem (base + j) : ℝ) + 1)) ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (base + C.d + 1) ∧
      cost ≤ (4 * limbs) * (38 * (4 * limbs) + 35) + (2 * limbs) * (38 * (2 * limbs) + 35) + 1113 * limbs + 50 * C.d + 637 + 40 * depth := by
  dsimp only
  intro hp hgap hku hlu hk hl hkWord hlWord
  let input := SparseCore.coreNMax (C.M₀ ^ 2) + C.M₀ ^ 2
  have hhpos : 0 < h := by omega
  have hscales := certifiedEndpointTable_scale_bounds C.d factor coefficient input h hhpos
  dsimp only [input] at hscales
  rw [← hp] at hscales
  obtain ⟨hs, hks, hls, hfs⟩ := hscales
  obtain ⟨hkuw, hluw, hkfit, hlfit, hfit⟩ :=
    certifiedEndpointTable_load_bounds hh (by omega : precision + 4 ≤ limbs)
      hs hks hls hfs hku hlu hkWord hlWord
  have hfine := certifiedThresholdEndpointBudget hku hlu hk hl hgap
  have haff := certifiedEndpointWorkspace_affine_bits (M := C.M₀) hhpos hePrecision
  dsimp only at haff
  rw [← hL] at haff
  have heP : Nat.clog 2 (2 * (C.d + 1)) ≤ 2 * precision := by omega
  exact initSparseCoreThresholdsFromEndpoints_runs E C hpower h44 hDepth h47 hBuckets
    h48 hDegree h4 (Nat.two_pow_pos _) hload hext hmul hshift hadd h99 h67 h68 rfl
    h51 h27 hkuw hluw hkfit hlfit hword hz hfit hcword hPword haff hround h30 he hwordH
    (heP.trans_lt hPword) (dvd_mul_of_dvd_right hdvd _) heP
    ((Nat.div_le_self _ _).trans (by omega)) hγM hγk hbase rfl rfl hfactor hGrowth h50 hg hb
    hDepthWord hScaled rfl (by rw [← hfactor]) hkl hkuBound hll hluBound hklOrder hllOrder hfine
    (Nat.le_pow_clog (by decide) _) h22 h14 h76 h75 hden hcapacity

/-- The endpoint phase preserves the runtime dimensions, numeric
width, and exact sparsifier length required by the table writer. -/
theorem prepareCertifiedThresholdEndpoints_preserves_table_inputs
    {w bits load log pack coefficient clog cost : ℕ}
    {p : Program} {ω : ℕ → Bool} {st out : State} {outcome : Outcome}
    (hr : Runs w p ω (prepareCertifiedThresholdEndpoints bits load log pack coefficient clog)
        st outcome out cost) :
    out.regs 14 = st.regs 14 ∧ out.regs 22 = st.regs 22 ∧ out.regs 44 = st.regs 44 ∧
      out.regs 47 = st.regs 47 ∧ out.regs 48 = st.regs 48 ∧ out.regs 50 = st.regs 50 ∧
      out.regs 67 = st.regs 67 ∧ out.regs 68 = st.regs 68 ∧
      out.regs 75 = st.regs 75 ∧ out.regs 76 = st.regs 76 := by
  repeat' apply And.intro
  all_goals exact runs_preserves_register (by rfl) hr

/-- Compute both endpoint intervals, then write the certified threshold
table at the cursor returned by the logarithms. -/
theorem prepareAndWriteCertifiedEndpointTable_runs
    (E : SparseCore.SparseCoreEnv) (C : Chain.ChainParams)
    {w power depth buckets degree h load extend mul shift add heap limbs factor precision round vertices coefficient bits log pack clog N : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hpower : MeetsContract w p power (initStretchPowerContract w))
    (h44 : st.regs 44 = depth) (hDepth : depth = E.L)
    (h47 : st.regs 47 = buckets) (hBuckets : buckets = E.B_fn (C.M₀ ^ 2))
    (h48 : st.regs 48 = degree) (hDegree : degree = E.d_fn (C.M₀ ^ 2))
    (h4 : st.regs 4 = 2 ^ precision)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hext : MeetsContract w p extend (Num.extendCopyContract w h))
    (hmul : MeetsContract w p mul (Num.multiplyContract w h))
    (hshift : MeetsContract w p shift (Num.shiftLeftContract w h))
    (hadd : MeetsContract w p add (Num.addContract w h))
    (h98 : st.regs 98 = heap) (h67 : st.regs 67 = limbs)
    (h68 : st.regs 68 = precision)
    (hL : limbs = precision + (SparseCore.coreNMax (C.M₀ ^ 2) + C.M₀ ^ 2 + 2).size + 4)
    (hh : 2 ≤ h)
    (hword : factor < 2 ^ w) (hz : ZeroFrom st.mem heap)
    (hcword : 1265 < 2 ^ w) (hPword : 2 * precision < 2 ^ w)
    (hround : MeetsContract w p round (initDepthEndpointContract w h))
    (hwordH : h < 2 ^ w) (hdvd : h ∣ precision)
    (hePrecision : Nat.clog 2 (2 * (C.d + 1)) ≤ precision)
    (hγM : (SparseCore.sparseCoreParams E).γ_ℓ (C.M₀ ^ 2) ≤ C.M₀)
    (hγk : (SparseCore.sparseCoreParams E).γ_ℓ (C.M₀ ^ 2) ≤ C.k)
    {growth : ℕ}
    (hfactor : factor = 11 * (E.L + 1) * growth * E.B_fn (C.M₀ ^ 2) *
      (2 * E.d_fn (C.M₀ ^ 2) + 190))
    (hGrowth : (E.P_fn (C.M₀ ^ 2)).γ_ℓ = growth)
    (h50 : st.regs 50 = 2 ^ precision * growth) (hg : 0 < growth)
    (hb : 0 < buckets) (hDepthWord : max (depth + 1) 3 < 2 ^ w)
    (hScaled : 2 ^ precision * growth < 2 ^ w)
    (h22 : st.regs 22 = C.M₀) (h14 : st.regs 14 = Nat.clog 2 (vertices + 2))
    (h76 : st.regs 76 = C.k) (h75 : st.regs 75 = C.d)
    (hden : 3 * C.k * Nat.clog 2 (vertices + 2) ^ 2 < 2 ^ w)
    (hcapacity : (3 * C.M₀ ^ 2 + 1) * (C.M₀ * (2 * concreteThresholdScale C.d) ^ (C.d + 1)) < 2 ^ w)
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hclog : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (hLog : p.HasAt log (Num.logarithmModule log h)) (hLogWord : 3 * h + 2 ≤ w)
    (h92 : st.regs 92 = N) (h25 : st.regs 25 = (E.P_fn (C.M₀ ^ 2)).p_s)
    (hps : (E.P_fn (C.M₀ ^ 2)).p_s ≤ 1)
    (hCoeff : (E.P_fn (C.M₀ ^ 2)).K_s = 1 + coefficient / Real.log 2)
    (hDepthFit : 2 * (C.d + 1) + 1 < 2 ^ w)
    (hCoarse : concreteThresholdScale C.d < 2 ^ w)
    (hprec : 16 ≤ precision) (hMpos : 0 < C.M₀) :
    let input := SparseCore.coreNMax (C.M₀ ^ 2) + C.M₀ ^ 2
    let minimum := Nat.clog 2 (2 * (C.d + 1)) + Nat.clog 2 factor +
      (17 + Nat.clog 2 (coefficient + 1) + Nat.clog 2 (input + 3))
    precision = (minimum + (h - 1)) / h * h →
    Nat.clog 2 (2 * (C.d + 1) * factor *
      ((65536 * coefficient + 2) * (input + 3) +
        (2 * coefficient + 2) * (4096 * (input + 2)))) ≤ precision →
    (coefficient + 3) * (2 ^ precision) ^ 2 < 2 ^ w →
    (input + 3) * 2 ^ precision < 2 ^ w →
    (input + 2).size + 11 ≤ precision →
    heap + limbs + limbs + Num.logarithmSpace limbs precision 2 +
      limbs + limbs + Num.logarithmSpace limbs precision (input + 2).size +
      (39 * limbs + 3 * (C.d + 1) + 17) < 2 ^ w →
    ∃ ready out endpointCost tableCost base a,
      Runs w p ω (prepareCertifiedThresholdEndpoints bits load log pack coefficient clog)
        st .normal ready endpointCost ∧
      Runs w p ω (initSparseCoreThresholdsFromEndpoints power load extend mul shift add round h)
        {ready with regs := Function.update (Function.update ready.regs 126 (ready.regs 114)) 127 (ready.regs 115)} .normal out tableCost ∧
      out.regs 83 = base ∧ out.regs 98 = base + C.d + 1 ∧
      (∀ j ≤ C.d, out.mem (base + j) = Chain.concreteLevelRebuildCount C.M₀ C.k a
          (concreteThresholdScale C.d) j vertices ∧
        (out.mem (base + j) : ℝ) ≤
          Chain.SparseCoreTool.updateThreshold C.k (Chain.levelM (SparseCore.sparseCoreParams E) C j) vertices ∧
        Chain.SparseCoreTool.updateThreshold C.k (Chain.levelM (SparseCore.sparseCoreParams E) C j) vertices ≤
          48 * ((out.mem (base + j) : ℝ) + 1)) ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (base + C.d + 1) ∧
      heap ≤ base ∧ base + 3 * (C.d + 1) + 17 < 2 ^ w := by
  dsimp only
  intro hp hgap hkWord hlWord hguard hroom
  obtain ⟨ready, ce, ret, hr, hkl, hku, hko, hkmax, hkgap, hll, hlu, hlo, hlmax, hlgap,
    h4', h30, he, h99, _, hret, _, hroom', hm, hzero, _⟩ :=
    prepareCertifiedThresholdEndpoints_numeric_runs E C.M₀ hbits hload hpack hclog
      hLog hLogWord h92 h4 h67 h68 h98 h22 h25 hps h75 hDepthFit hCoarse hprec hdvd
      (by omega) hz hkWord hMpos hlWord hL hroom hguard
  obtain ⟨h14', h22', h44', h47', h48', h50', h67', h68', h75', h76'⟩ :=
    prepareCertifiedThresholdEndpoints_preserves_table_inputs hr
  let saved := {ready with regs := Function.update (Function.update ready.regs 126 (ready.regs 114)) 127 (ready.regs 115)}
  have keep (r : ℕ) (h₁ : r ≠ 126 := by decide) (h₂ : r ≠ 127 := by decide) :
      saved.regs r = ready.regs r := by simp [saved, h₁, h₂]
  have hkl' : (ready.regs 49 : ℝ) / (2 : ℝ) ^ precision ≤ (E.P_fn (C.M₀ ^ 2)).K_s := by
    rw [hCoeff]
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hkl
  have hku' : (E.P_fn (C.M₀ ^ 2)).K_s ≤ (ready.regs 51 : ℝ) / (2 : ℝ) ^ precision := by
    rw [hCoeff]
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hku
  obtain ⟨out, ct, ht, h83, hcursor, htable, hf, hz', _⟩ :=
    initCertifiedEndpointTable_runs E C hpower ((keep 44).trans (h44'.trans h44)) hDepth
      ((keep 47).trans (h47'.trans h47)) hBuckets ((keep 48).trans (h48'.trans h48)) hDegree
      ((keep 4).trans h4') hload hext hmul hshift hadd ((keep 99).trans h99)
      ((keep 67).trans (h67'.trans h67)) ((keep 68).trans (h68'.trans h68)) (keep 51) (keep 27)
      hL hh hword hzero hcword hPword hround ((keep 30).trans h30) ((keep 119).trans he)
      hwordH hdvd hePrecision hγM hγk (by omega) hfactor hGrowth
      ((keep 50).trans (h50'.trans h50)) hg hb hDepthWord hScaled hkl' hku'
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hll)
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hlu)
      hko hlo ((keep 22).trans (h22'.trans h22)) ((keep 14).trans (h14'.trans h14))
      ((keep 76).trans (h76'.trans h76)) ((keep 75).trans (h75'.trans h75)) hden hcapacity
      hp hgap hkmax hlmax hkgap hlgap hkWord hlWord
  exact ⟨ready, out, ce, ct, ret + 39 * limbs, _, hr, ht, h83, hcursor, htable,
    fun x hx => (hf x (hx.trans_le hret)).trans (hm x hx), hz', by omega, by omega⟩

/-- Endpoint preparation retains the query words returned by the
sparsifier. Only the threshold body needs to save and restore them. -/
theorem prepareCertifiedThresholdEndpoints_preserves_query
    {w bits load log pack coefficient clog cost : ℕ}
    {p : Program} {ω : ℕ → Bool} {st out : State} {outcome : Outcome}
    (hr : Runs w p ω (prepareCertifiedThresholdEndpoints bits load log pack coefficient clog)
      st outcome out cost) :
    out.regs 114 = st.regs 114 ∧ out.regs 115 = st.regs 115 := by
  have h₁ : writesBelow 114 (initRebuildCoefficient bits load log pack coefficient) = true := rfl
  have h₂ : writesBelow 114 (initSparseCoreLogForThresholds bits load log pack) = true := rfl
  have keep (r : ℕ) (h : 114 ≤ r) (h119 : r ≠ 119) (h30 : r ≠ 30) :
      out.regs r = st.regs r := by
    unfold prepareCertifiedThresholdEndpoints at hr
    rcases runs_seq_iff.mp hr with ⟨c, hn, ht, _⟩ | ⟨mid, c, d, ht, hu, _⟩
    · exact runs_preserves_above h h₁ ht
    · rw [← runs_preserves_above h h₁ ht]
      rcases runs_seq_iff.mp hu with ⟨c', hn, hv, _⟩ | ⟨ready, c', d', hv, hz, _⟩
      · exact runs_preserves_above h h₂ hv
      · rw [← runs_preserves_above h h₂ hv]
        unfold prepareCertifiedThresholdScale at hz
        rcases runs_seq_iff.mp hz with ⟨_, _, hc, _⟩ | ⟨next, _, _, hc, ha, _⟩
        · obtain ⟨_, _, _, _, _, _, _, _, _, rfl, _⟩ := runs_call_iff.mp hc
          simp [h119]
        · obtain ⟨_, _, _, rfl, _⟩ := runs_assign_iff.mp ha
          obtain ⟨_, _, _, _, _, _, _, _, _, rfl, _⟩ := runs_call_iff.mp hc
          simp [h119, h30]
  exact ⟨keep 114 (by decide) (by decide) (by decide), keep 115 (by decide) (by decide) (by decide)⟩

/-- The vertex logarithm computed by the integer bucket stage reaches
the threshold writer unchanged. -/
theorem prepareCertifiedThresholdEndpoints_preserves_vertexLog
    {w bits load log pack coefficient clog cost : ℕ}
    {p : Program} {ω : ℕ → Bool} {st out : State} {outcome : Outcome}
    (hr : Runs w p ω (prepareCertifiedThresholdEndpoints bits load log pack coefficient clog)
      st outcome out cost) :
    out.regs 14 = st.regs 14 :=
  runs_preserves_register (by rfl) hr

/-- Depth, sparsifier factors, and numerical endpoints retain the
vertex logarithm supplied by the integer bucket stage. -/
theorem certifiedThresholdInputs_preserve_vertexLog
    {w bits load log pack roundEntry h factorEntry decK thr cDeg witnessDen coefficient clog
      c₁ c₂ c₃ : ℕ}
    {p : Program} {ω : ℕ → Bool} {st depth factors out : State} {retry : Stmt}
    (hr : Runs w p ω (prepareSolverSparseCoreWithDepthWorkspace bits load log roundEntry h retry)
      st .normal depth c₁)
    (ht : Runs w p ω (initMergedSparsifierFactors factorEntry decK thr cDeg witnessDen)
      depth .normal factors c₂)
    (hu : Runs w p ω (prepareCertifiedThresholdEndpoints bits load log pack coefficient clog)
      factors .normal out c₃)
    (hRetry : avoidsRegister 14 retry = true) :
    out.regs 14 = st.regs 14 := by
  have hdepth : avoidsRegister 14
      (prepareSolverSparseCoreWithDepthWorkspace bits load log roundEntry h retry) = true := by
    change (true && avoidsRegister 14 retry && true) = true
    simp [hRetry]
  exact (prepareCertifiedThresholdEndpoints_preserves_vertexLog hu).trans
    ((runs_preserves_register (by rfl) ht).trans (runs_preserves_register hdepth hr))

/-- Build the table in a workspace sized for its endpoints and restore
the solver format before entering level construction. -/
@[expose] def initCertifiedThresholdsWithWorkspace
    (power bits load log pack clog coefficient h extend mul shift add roundEntry : ℕ) : Stmt :=
  saveCertifiedThresholdFormat ;;
  initCertifiedEndpointWorkspace power bits clog coefficient h ;;
  rescaleCertifiedSparsifierLength ;;
  prepareCertifiedThresholdEndpoints bits load log pack coefficient clog ;;
  initCertifiedSparseCoreThresholds power load extend mul shift add roundEntry h ;;
  restoreCertifiedThresholdFormat ;; .assign 99 (.reg 98)

/-- The workspace calculations preserve the saved solver format and
the query-factor scale. Restoring them leaves the certified table intact. -/
theorem initCertifiedThresholdsWithWorkspace_runs
    {w power bits load log pack clog coefficient h extend mul shift add roundEntry c₁ c₂ c₃ c₄ : ℕ}
    {p : Program} {ω : ℕ → Bool} {st saved work scaled ready finished : State}
    (hr : Runs w p ω saveCertifiedThresholdFormat st .normal saved 14)
    (h67 : saved.regs 128 = st.regs 67) (h68 : saved.regs 129 = st.regs 68)
    (h4 : saved.regs 130 = st.regs 4) (h0 : saved.regs 131 = st.regs 0)
    (h6 : saved.regs 132 = st.regs 6)
    (ht : Runs w p ω (initCertifiedEndpointWorkspace power bits clog coefficient h) saved .normal work c₁)
    (hu : Runs w p ω rescaleCertifiedSparsifierLength work .normal scaled c₂)
    (hv : Runs w p ω (prepareCertifiedThresholdEndpoints bits load log pack coefficient clog)
      scaled .normal ready c₃)
    (hw : 1 < 2 ^ w)
    (hx : Runs w p ω (initSparseCoreThresholdsFromEndpoints power load extend mul shift add roundEntry h)
      {ready with regs := Function.update (Function.update ready.regs 126 (ready.regs 114)) 127 (ready.regs 115)}
      .normal finished c₄) :
    ∃ out, Runs w p ω (initCertifiedThresholdsWithWorkspace power bits load log pack clog
        coefficient h extend mul shift add roundEntry) st .normal out (c₁ + c₂ + c₃ + c₄ + 51) ∧
      out.regs 67 = st.regs 67 ∧ out.regs 68 = st.regs 68 ∧ out.regs 4 = st.regs 4 ∧
      out.regs 0 = st.regs 0 ∧ out.regs 6 = st.regs 6 ∧
      out.regs 114 = st.regs 114 ∧ out.regs 115 = st.regs 115 ∧ out.regs 10 = 1 ∧
      out.mem = finished.mem ∧ out.regs 99 = finished.regs 98 ∧
      (∀ r, r ≠ 99 → r ≠ 67 → r ≠ 68 → r ≠ 4 → r ≠ 0 → r ≠ 6 → r ≠ 114 → r ≠ 115 → r ≠ 10 → out.regs r = finished.regs r) := by
  obtain ⟨certified, hz, hq₁, hq₂, h10, hm', hk'⟩ :=
    initCertifiedSparseCoreThresholds_runs hw hx
  have keep (r : ℕ) (hr : 128 ≤ r) : certified.regs r = saved.regs r :=
    (runs_preserves_above hr (by rfl) hz).trans
      ((runs_preserves_above hr (by rfl) hv).trans
        ((runs_preserves_above hr (by rfl) hu).trans (runs_preserves_above hr (by rfl) ht)))
  obtain ⟨restored, hy, h67', h68', h4', h0', h6', hm, hk⟩ :=
    restoreCertifiedThresholdFormat_runs (w := w) (p := p) (ω := ω) (st := certified)
  obtain ⟨hv₁, hv₂⟩ := prepareCertifiedThresholdEndpoints_preserves_query hv
  have hQuery (r : ℕ) (hSave : avoidsRegister r saveCertifiedThresholdFormat = true)
      (hWork : avoidsRegister r (initCertifiedEndpointWorkspace power bits clog coefficient h) = true)
      (hRescale : avoidsRegister r rescaleCertifiedSparsifierLength = true) :
      scaled.regs r = st.regs r :=
    (runs_preserves_register hRescale hu).trans
      ((runs_preserves_register hWork ht).trans (runs_preserves_register hSave hr))
  let out := {restored with regs := Function.update restored.regs 99 (restored.regs 98)}
  have hz' : Runs w p ω (.assign 99 (.reg 98)) restored .normal out 2 :=
    runs_assign_iff.mpr ⟨_, rfl, rfl, rfl, rfl⟩
  have hkeep (r : ℕ) (hne : r ≠ 99) : out.regs r = restored.regs r := by
    simp [out, hne]
  refine ⟨out, ?_, (hkeep 67 (by decide)).trans (h67'.trans ((keep 128 (by decide)).trans h67)),
    (hkeep 68 (by decide)).trans (h68'.trans ((keep 129 (by decide)).trans h68)),
    (hkeep 4 (by decide)).trans (h4'.trans ((keep 130 (by decide)).trans h4)),
    (hkeep 0 (by decide)).trans (h0'.trans ((keep 131 (by decide)).trans h0)),
    (hkeep 6 (by decide)).trans (h6'.trans ((keep 132 (by decide)).trans h6)),
    (hkeep 114 (by decide)).trans ((hk 114 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (hq₁.trans (hv₁.trans (hQuery 114 rfl rfl rfl)))),
    (hkeep 115 (by decide)).trans ((hk 115 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (hq₂.trans (hv₂.trans (hQuery 115 rfl rfl rfl)))),
    (hkeep 10 (by decide)).trans ((hk 10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h10),
    hm.trans hm', ?_, ?_⟩
  ·
    exact runs_seq_iff.mpr (Or.inr ⟨saved, 14, _, hr,
    runs_seq_iff.mpr (Or.inr ⟨work, c₁, _, ht,
      runs_seq_iff.mpr (Or.inr ⟨scaled, c₂, _, hu,
        runs_seq_iff.mpr (Or.inr ⟨ready, c₃, _, hv,
          runs_seq_iff.mpr (Or.inr ⟨certified, c₄ + 15, 17, hz,
            runs_seq_iff.mpr (Or.inr ⟨restored, 14, 2, hy, hz', rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), by omega⟩)
  · simpa [out] using
      (hk 98 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hk' 98 (by decide) (by decide) (by decide))
  · intro r h99r h67r h68r h4r h0r h6r h114 h115 h10r
    exact (hkeep r h99r).trans ((hk r h67r h68r h4r h0r h6r).trans (hk' r h114 h115 h10r))

/-- Level construction sees the certified threshold entries below the header
and starts with the next unused address after the header. -/
theorem continueSolverInit_thresholdTable_runs
    {w heap table count m V depth branch psi alphaPtr quality epsilon limbs precision : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {levels inconclusive : Stmt}
    {entry : ℕ → ℕ}
    (hcert : st.regs 10 = 1) (hw : 1 < 2 ^ w)
    (hh : st.regs 99 = heap) (ht : st.regs 83 = table)
    (hentries : ∀ j < count, st.mem (table + j) = entry j)
    (htable : table + count ≤ heap)
    (ha : st.regs 101 = alphaPtr)
    (hm : st.regs 0 = m) (hV : st.regs 102 = V) (hd : st.regs 75 = depth)
    (hb : st.regs 76 = branch) (hpsi : st.regs 6 = psi)
    (hq : st.regs 72 = quality) (he : st.regs 73 = epsilon)
    (hL : st.regs 103 = limbs) (hP : st.regs 104 = precision)
    (hspace : 80 * limbs + 260 < 2 ^ w)
    (hz : ZeroFrom st.mem heap) (hroom : heap + 17 < 2 ^ w)
    (hlevels : ∀ header,
      header.regs 74 = heap → header.regs 77 = heap + 17 →
      header.regs 83 = table → ZeroFrom header.mem (heap + 17) →
      ChainInitParametersAt header.mem heap m V depth branch psi alphaPtr quality epsilon →
      MinRatioNumericHeaderAt header.mem heap limbs precision
        (20 * (4 * limbs + 8) + 100) (20 * (4 * limbs + 8) + 100) →
      (∀ j < count, header.mem (table + j) = entry j) →
      (∀ a < heap, header.mem a = st.mem a) →
      (∀ r ∈ ([67, 68, 69, 70, 71, 75] : List ℕ), header.regs r = st.regs r) →
      ∃ out cost, Runs w p ω levels header .normal out cost) :
    ∃ out cost, Runs w p ω (continueSolverInit levels inconclusive)
      st .normal out (104 + cost + 5) := by
  obtain ⟨header, hr, h74, h77, hchain, hnum, hframe, hzero, hregs, _⟩ :=
    allocateSolverInitHeader_runs (p := p) (ω := ω) hh ha hm hV hd hb hpsi
      hq he hL hP hspace hz hroom
  have h83 := (hregs 83 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).trans ht
  have hkeep (j : ℕ) (hj : j < count) : header.mem (table + j) = entry j :=
    (hframe _ (by omega)).trans (hentries j hj)
  have hinputs (r : ℕ) (hr : r ∈ ([67, 68, 69, 70, 71, 75] : List ℕ)) :
      header.regs r = st.regs r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    apply hregs <;> omega
  obtain ⟨out, cost, hl⟩ :=
    hlevels header h74 h77 h83 hzero hchain hnum hkeep (fun a ha => hframe a (by omega)) hinputs
  exact ⟨out, cost, continueSolverInit_certified_runs hcert hw hr hl⟩

/-- A certified bucket supplies the unit scale and heap for both the
linked sparsifier depth selector and the fixed-budget path factor phase. -/
theorem prepareCertifiedSparsifierFactors_runs
    (J : Scaling.Circulation)
    (threshold h b Kγ pathC Kint cw factorEntry decK thr cDeg witnessDen cursorDegree : ℕ)
    (hK : 1 ≤ decK) (hc : 0 < cDeg) (hWitness : 0 < witnessDen) :
    ∃ multiplier, ∀ {c a : ℕ} {p : Program} {ω : ℕ → Bool} {st : State} {retry : Stmt},
      let B := J.solverWords.length + J.solverWords.foldr max 0 + 2
      let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
      let w := wordSize c J.solverWords
      let den := Expander.maxPhiDenOf decK thr (M ^ 2)
      let cap := Spanner.capM_W cDeg (1 / (den : ℝ)) (M ^ 2)
      let length := (max (Expander.PathDSProg.gExpImpl Kγ pathC Kint den (M ^ 2))
        (Expander.PathDSProg.gExpImpl Kγ pathC Kint witnessDen cap)) ^ 2
      let query := max (Expander.PathDSProg.gQueryImpl Kγ pathC Kint den (M ^ 2))
        (Expander.PathDSProg.gQueryImpl Kγ pathC Kint witnessDen cap)
      3 * h + 2 ≤ w → p.HasAt b (initDepthProcedures b h) →
      MeetsContract w p factorEntry (initMachinePathFactorsContract w Kγ pathC Kint cw) →
      st.regs 22 = M → 1 ≤ M → 0 < h →
      st.regs 99 = a → ZeroFrom st.mem a → st.regs 18 = 1 → st.regs 4 = 1 →
      a ≤ B ^ cursorDegree → multiplier ≤ c →
      ∃ depthState out depthCost factorCost ret,
        Runs w p ω (prepareSolverSparseCoreWithDepthWorkspace b (b + 1) (b + 6) (b + 2) h retry)
          {st with regs := Function.update st.regs 98 a} .normal depthState depthCost ∧
        Runs w p ω (initMergedSparsifierFactors factorEntry decK thr cDeg witnessDen)
          depthState .normal out factorCost ∧
        out.regs 44 = Expander.chosenL (M ^ 2) ∧ out.regs 4 = 1 ∧
        out.regs 98 = ret + 4 ∧ ZeroFrom out.mem (ret + 4) ∧
        out.regs 50 = length ∧ out.regs 52 = length ∧ out.regs 114 = query ∧ out.regs 115 = query ∧
        length < 2 ^ w ∧ 0 < length ∧
        (∀ r < 98, r ∉ ([23, 24, 31, 32, 33, 36, 44, 50, 52, 58, 63] : List ℕ) →
          out.regs r = st.regs r) ∧
        (∀ r, 101 ≤ r → r ≤ 104 → out.regs r = st.regs r) ∧
        (∀ x < a, out.mem x = st.mem x) := by
  let d := max 2 (Nat.clog 2 threshold + 1)
  let cd := Nat.clog 2 (h * (38 * (2 ^ 48) ^ 8 + 12) + 5)
  let dh := max cursorDegree (10 + 3 * (cd + 8 * (2 * d))) + 1
  obtain ⟨factorMultiplier, hfactor⟩ :=
    initMergedSparsifierFactors_budgeted_runs Kγ pathC Kint cw factorEntry decK thr cDeg
      witnessDen (2 * d) 0 dh hK hc hWitness
  refine ⟨max dh factorMultiplier, ?_⟩
  intro c a p ω st retry
  dsimp only
  intro hw hlink himpl h22 hM hh ha hz hflag hscale hcursor hsize
  have hd : dh ≤ c := (le_max_left _ _).trans hsize
  have hf : factorMultiplier ≤ c := (le_max_right _ _).trans hsize
  obtain ⟨depthState, _, ret, _, h23, h44, h98, hlow, _, _, hmem, hzero, hframe, hargs, _, _, hret,
      depthCost, hdepth, _⟩ :=
    prepareLinkedDepthAfterBucket_runs (b := b) (p := p) (ω := ω) (retry := retry)
      J hw hlink h22 hM hh ha hz hflag hcursor hd
  have h4 := (hframe 4 (by decide) (by decide) (by decide)).trans hscale
  have hword : wordSize factorMultiplier J.solverWords ≤ wordSize c J.solverWords :=
    Nat.mul_le_mul_right _ hf
  obtain ⟨out, factorCost, hrun, h50, h52, h114, h115, hpos, hfit, hout, _, hfree, hkeep, hmem', _⟩ :=
    hfactor J.solverWords himpl h23 h98 h4 hzero (by decide)
      (solverDepthPaddedSize_power_bounds J threshold).2 (by simp) hret hword
  refine ⟨depthState, out, depthCost, factorCost, ret, hdepth, hrun,
    (hkeep 44 (by decide)).trans h44, (hkeep 4 (by decide)).trans h4, hout, hfree,
    by simpa only [one_mul] using h50, by simpa only [one_mul] using h52,
    by simpa only [one_mul] using h114, by simpa only [one_mul] using h115,
    by simpa only [h52, one_mul] using hfit,
    by simpa only [h50, one_mul] using hpos, ?_, ?_, ?_⟩
  · intro r hr hn
    have hskip : r ∉ ([24, 31, 32, 33, 36, 50, 52, 58, 63, 98, 99, 114, 115, 122] : List ℕ) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢
      omega
    refine (hkeep r hskip).trans (hframe r hr ?_ ?_)
    · intro he; subst r; exact hn (by decide)
    · intro he; subst r; exact hn (by decide)
  · intro r h₁ h₂
    have hn : r ∉ ([24, 31, 32, 33, 36, 50, 52, 58, 63, 98, 99, 114, 115, 122] : List ℕ) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    exact (hkeep r hn).trans (hargs r h₁ h₂)
  · intro x hx
    exact (hmem' x (Or.inl (hx.trans_le hlow))).trans (hmem x hx)

/-- Initialize the certified table after the bucket-cap check. -/
@[expose] def initCertifiedThresholdPhase
    (bits load log pack roundEntry h factorEntry decK thr cDeg witnessDen coefficient clog
      power extend mul shift add : ℕ) (retry degreeSetup : Stmt) : Stmt :=
  initThresholdsAfterBucketCap
    (prepareSolverSparseCoreWithDepthWorkspace bits load log roundEntry h retry ;;
      initMergedSparsifierFactors factorEntry decK thr cDeg witnessDen ;;
      degreeSetup ;;
      initCertifiedThresholdsWithWorkspace power bits load log pack clog coefficient h extend mul shift add roundEntry)

/-- After bucket certification the selected sparsifier and workspace
produce the table used by level construction. -/
theorem initCertifiedThresholdPhase_runs
    {w bits load log pack roundEntry h factorEntry decK thr cDeg witnessDen coefficient clog
      power extend mul shift add heap c₁ c₂ c₃ c₄ : ℕ}
    {p : Program} {ω : ℕ → Bool} {st depth factors capped out : State} {retry degreeSetup : Stmt}
    (hflag : st.regs 18 = 1) (hheap : st.regs 99 = heap) (hw : 1 < 2 ^ w)
    (hr : Runs w p ω (prepareSolverSparseCoreWithDepthWorkspace bits load log roundEntry h retry)
      {st with regs := Function.update st.regs 98 heap} .normal depth c₁)
    (ht : Runs w p ω (initMergedSparsifierFactors factorEntry decK thr cDeg witnessDen)
      depth .normal factors c₂)
    (hDegree : Runs w p ω degreeSetup factors .normal capped c₃)
    (hu : Runs w p ω (initCertifiedThresholdsWithWorkspace power bits load log pack clog
      coefficient h extend mul shift add roundEntry) capped .normal out c₄) :
    Runs w p ω (initCertifiedThresholdPhase bits load log pack roundEntry h factorEntry
      decK thr cDeg witnessDen coefficient clog power extend mul shift add retry degreeSetup)
      st .normal out (c₁ + c₂ + c₃ + c₄ + 10) := by
  unfold initCertifiedThresholdPhase
  have hseq := runs_seq_iff.mpr (Or.inr ⟨depth, c₁, c₂ + c₃ + c₄ + 2, hr,
    runs_seq_iff.mpr (Or.inr ⟨factors, c₂, c₃ + c₄ + 1, ht,
      runs_seq_iff.mpr (Or.inr ⟨capped, c₃, c₄, hDegree, hu, rfl⟩), by omega⟩), rfl⟩)
  have hrun := initThresholdsAfterBucketCap_runs hflag hheap hw hseq
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hrun

/-- Enter level initialization using the certified integer rebuild table. -/
@[expose] def solverInitWithCertifiedThresholds
    (alpha select quality graphPack threshold branch lsstConstant power bits load log pack
      roundEntry h factorEntry decK thr cDeg witnessDen extend mul shift add coefficient clog : ℕ)
    (retry degreeSetup levels inconclusive : Stmt) : Stmt :=
  prepareMinRatioSolverThresholdInputs alpha select quality graphPack ;;
  prepareSolverChainWithDepthWorkspace threshold bits load log roundEntry h branch retry ;;
  stageCertifiedInitUnitScale ;; saveSolverInitArguments ;;
  initConcreteIntegerBucketStage clog lsstConstant ;;
  initCertifiedThresholdPhase bits load log pack roundEntry h factorEntry decK thr cDeg
    witnessDen coefficient clog power extend mul shift add retry degreeSetup ;;
  continueSolverInit levels inconclusive

/-- Compose the verified stages of multiword Init, including the
conditional threshold phase and the final continuation. -/
theorem solverInitWithCertifiedThresholds_runs
    {w alpha select quality graphPack threshold branch lsstConstant power bits load log pack
      roundEntry h factorEntry decK thr cDeg witnessDen extend mul shift add coefficient clog
      inputCost chainCost scaleCost argsCost bucketCost thresholdCost continuationCost : ℕ}
    {p : Program} {ω : ℕ → Bool} {st ready chain scaled saved bucket checked out : State}
    {retry degreeSetup levels inconclusive : Stmt} {outcome : Outcome}
    (hi : Runs w p ω (prepareMinRatioSolverThresholdInputs alpha select quality graphPack)
      st .normal ready inputCost)
    (hd : Runs w p ω (prepareSolverChainWithDepthWorkspace threshold bits load log roundEntry h branch retry)
      ready .normal chain chainCost)
    (hs : Runs w p ω stageCertifiedInitUnitScale chain .normal scaled scaleCost)
    (ha : Runs w p ω saveSolverInitArguments scaled .normal saved argsCost)
    (hb : Runs w p ω (initConcreteIntegerBucketStage clog lsstConstant)
      saved .normal bucket bucketCost)
    (ht : Runs w p ω (initCertifiedThresholdPhase bits load log pack roundEntry h factorEntry decK thr cDeg
      witnessDen coefficient clog power extend mul shift add retry degreeSetup) bucket .normal checked thresholdCost)
    (hc : Runs w p ω (continueSolverInit levels inconclusive) checked outcome out continuationCost) :
    Runs w p ω (solverInitWithCertifiedThresholds alpha select quality graphPack threshold branch
      lsstConstant power bits load log pack roundEntry h factorEntry decK thr cDeg
      witnessDen extend mul shift add coefficient clog retry degreeSetup levels inconclusive)
      st outcome out (inputCost + chainCost + scaleCost + argsCost + bucketCost + thresholdCost +
        continuationCost + 6) := by
  unfold solverInitWithCertifiedThresholds
  refine runs_seq_iff.mpr (Or.inr ⟨ready, inputCost,
    chainCost + scaleCost + argsCost + bucketCost + thresholdCost + continuationCost + 5,
    hi, ?_, by omega⟩)
  refine runs_seq_iff.mpr (Or.inr ⟨chain, chainCost,
    scaleCost + argsCost + bucketCost + thresholdCost + continuationCost + 4,
    hd, ?_, by omega⟩)
  refine runs_seq_iff.mpr (Or.inr ⟨scaled, scaleCost,
    argsCost + bucketCost + thresholdCost + continuationCost + 3, hs, ?_, by omega⟩)
  refine runs_seq_iff.mpr (Or.inr ⟨saved, argsCost,
    bucketCost + thresholdCost + continuationCost + 2, ha, ?_, by omega⟩)
  refine runs_seq_iff.mpr (Or.inr ⟨bucket, bucketCost,
    thresholdCost + continuationCost + 1, hb, ?_, by omega⟩)
  exact runs_seq_iff.mpr (Or.inr ⟨checked, _, _, ht, hc, rfl⟩)

end MinCostFlow.MinRatio
