module

public import MinCostFlow.MinRatio.InitGraphInput
public import MinCostFlow.MinRatio.InitRuntimeDimensions
public import MinCostFlow.MinRatio.InitMachineFallbackCost
public import MinCostFlow.IPM.Machine.ConnectedSolverInitialize
public import MinCostFlow.Scaling.SolverContract
import MinCostFlow.IPM.ConnectedInitialConstruction

/-!
# Runtime dimensions for solver Init

Prepare the padded size and preserve the solver arguments across
the logarithm and dimension selection.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM

/-- Prepare the padded count, scale and saved solver arguments before
the logarithm routine uses the low registers. -/
@[expose] def stageSolverRuntimeDimensions (threshold : ℕ) : Stmt :=
  initConcreteBucketBaseEdgeBound threshold ;; stageInitBucketScale ;; saveSolverInitArguments

/-- The runtime dimension routine receives the padded count and exact
scale, with the solver arguments saved for later header allocation. -/
theorem stageSolverRuntimeDimensions_runs {w threshold precision heap V limbs : ℕ} (I : Instance)
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hm : st.regs 0 = (IPM.namedInstance I).m) (hmw : I.m < 2 ^ w) (ht : threshold < 2 ^ w)
    (ha : st.regs 4 = heap) (hP : st.regs 68 = precision) (hw : precision < w)
    (hV : st.regs 1 = V) (hL : st.regs 2 = limbs) (hp : st.regs 3 = precision) :
    ∃ out, Runs w p ω (stageSolverRuntimeDimensions threshold) st .normal out 23 ∧
      out.regs 22 = max I.m threshold ∧ out.regs 4 = 2 ^ precision ∧ out.regs 101 = heap ∧
      out.regs 102 = V ∧ out.regs 103 = limbs ∧ out.regs 104 = precision ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 22 → r ≠ 4 → r ≠ 101 → r ≠ 102 → r ≠ 103 → r ≠ 104 →
        out.regs r = st.regs r) := by
  obtain ⟨mid, hr₁, h22, hm₁, hk₁⟩ :=
    initConcreteBucketBaseEdgeBound_runs (p := p) (ω := ω) hm
      (by simpa only [IPM.namedInstance_m] using hmw) ht
  rw [namedInstance_initBaseEdgeBound] at h22
  obtain ⟨ready, hr₂, hs, h101, hk₂, hm₂, _⟩ :=
    stageInitBucketScale_runs (w := w) (p := p) (ω := ω)
      ((hk₁ 4 (by decide)).trans ha) ((hk₁ 68 (by decide)).trans hP) hw
  have keep (r : ℕ) (h22 : r ≠ 22 := by decide) (h4 : r ≠ 4 := by decide)
      (h101 : r ≠ 101 := by decide) := (hk₂ r h4 h101).trans (hk₁ r h22)
  obtain ⟨out, hr₃, hv, hlimbs, hprec, hk₃, hm₃⟩ :=
    saveSolverInitArguments_runs (w := w) (p := p) (ω := ω)
      ((keep 1).trans hV) ((keep 2).trans hL) ((keep 3).trans hp)
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 6, 16, hr₁,
    runs_seq_iff.mpr (Or.inr ⟨ready, 7, 8, hr₂, hr₃, rfl⟩), rfl⟩),
    (hk₃ 22 (by decide) (by decide) (by decide)).trans ((hk₂ 22 (by decide) (by decide)).trans h22),
    (hk₃ 4 (by decide) (by decide) (by decide)).trans hs,
    (hk₃ 101 (by decide) (by decide) (by decide)).trans h101,
    hv, hlimbs, hprec, hm₃.trans (hm₂.trans hm₁),
    fun r h22 h4 h101 h102 h103 h104 =>
      (hk₃ r h102 h103 h104).trans (keep r h22 h4 h101)⟩

/-- Save the solver's numeric format before using the depth logarithm workspace. -/
@[expose] def saveInitDepthNumericFormat : Stmt :=
  .assign 128 (.reg 67) ;; .assign 129 (.reg 68)

/-- Restore the solver format and advance the heap past the logarithm workspace. -/
@[expose] def restoreInitDepthNumericFormat : Stmt :=
  .assign 67 (.reg 128) ;; .assign 68 (.reg 129) ;; .assign 98 (.reg 99)

/-- Saving the numeric format costs two assignments and preserves memory. -/
theorem saveInitDepthNumericFormat_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State} :
    ∃ out, Runs w p ω saveInitDepthNumericFormat st .normal out 5 ∧
      out.regs 128 = st.regs 67 ∧ out.regs 129 = st.regs 68 ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 128 → r ≠ 129 → out.regs r = st.regs r) := by
  let mid := {st with regs := Function.update st.regs 128 (st.regs 67)}
  let out := {mid with regs := Function.update mid.regs 129 (st.regs 68)}
  have h₁ : Runs w p ω (.assign 128 (.reg 67)) st .normal mid 2 :=
    runs_assign_iff.mpr ⟨_, rfl, rfl, rfl, rfl⟩
  have h₂ : Runs w p ω (.assign 129 (.reg 68)) mid .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, mid], rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 2, 2, h₁, h₂, rfl⟩),
    by simp [out, mid], by simp [out], rfl, fun r ha hb => by simp [out, mid, ha, hb]⟩

/-- Restoring the format preserves the chosen depth and every other
register except the workspace cursor. -/
theorem restoreInitDepthNumericFormat_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State} :
    ∃ out, Runs w p ω restoreInitDepthNumericFormat st .normal out 8 ∧
      out.regs 67 = st.regs 128 ∧ out.regs 68 = st.regs 129 ∧ out.regs 98 = st.regs 99 ∧
      out.mem = st.mem ∧ (∀ r, r ≠ 67 → r ≠ 68 → r ≠ 98 → out.regs r = st.regs r) := by
  let mid := {st with regs := Function.update st.regs 67 (st.regs 128)}
  let ready := {mid with regs := Function.update mid.regs 68 (st.regs 129)}
  let out := {ready with regs := Function.update ready.regs 98 (st.regs 99)}
  have h₁ : Runs w p ω (.assign 67 (.reg 128)) st .normal mid 2 :=
    runs_assign_iff.mpr ⟨_, rfl, rfl, rfl, rfl⟩
  have h₂ : Runs w p ω (.assign 68 (.reg 129)) mid .normal ready 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, mid], rfl, rfl, rfl⟩
  have h₃ : Runs w p ω (.assign 98 (.reg 99)) ready .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, ready, mid], rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 2, 5, h₁,
    runs_seq_iff.mpr (Or.inr ⟨ready, 2, 2, h₂, h₃, rfl⟩), rfl⟩),
    by simp [out, ready, mid], by simp [out, ready], by simp [out], rfl,
    fun r ha hb hc => by simp [out, ready, mid, ha, hb, hc]⟩

/-- Run the chain selector with a separate numeric workspace. -/
@[expose] def solverChainWithDepthWorkspace (bits load log roundEntry h branch : ℕ)
    (retry : Stmt) : Stmt :=
  saveInitDepthNumericFormat ;;
  initRuntimeWorkspaceChainDimensions bits load log roundEntry h branch retry ;;
  restoreInitDepthNumericFormat

/-- The chain selector installs the model dimensions and advances the
heap while preserving the solver format. -/
theorem solverChainWithDepthWorkspace_runs {w h bits load log roundEntry branch a M : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {retry : Stmt}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hround : MeetsContract w p roundEntry (initDepthEndpointContract w h))
    (hbranch : MeetsContract w p branch (minRatioBranchCountContract w))
    (hm : st.regs 22 = M) (hM : 1 ≤ M) (hMw : M + 2 < 2 ^ w)
    (hh : 0 < h) (hhw : h < 2 ^ w) (ha : st.regs 98 = a) (hz : ZeroFrom st.mem a) :
    let E := (M + 2).size
    let q := 38 * (2 ^ 48 * E) ^ 8 + E
    let P := h * (q + E + 10)
    let L := P + E + 4
    let C := Chain.concreteChainParams M hM
    MeetsContract w p log (Num.logarithmContract w h q) →
    a + L + L + Num.logarithmSpace L P E < 2 ^ w → 2 * P + 9 < 2 ^ w →
    C.d ^ 48 + 1 < 2 ^ w →
    ∃ out cost ret, Runs w p ω (solverChainWithDepthWorkspace bits load log roundEntry h branch retry)
        st .normal out cost ∧ out.regs 75 = C.d ∧ out.regs 76 = C.k ∧ out.regs 98 = ret ∧
      a ≤ ret ∧ ret < 2 ^ w ∧ ret ≤ a + L + L + Num.logarithmSpace L P E ∧
      (∀ x < a, out.mem x = st.mem x) ∧ ZeroFrom out.mem ret ∧
      (∀ r < 98, r ≠ 75 → r ≠ 76 → out.regs r = st.regs r) ∧
      (∀ r, 101 ≤ r → r ≤ 104 → out.regs r = st.regs r) ∧
      cost ≤ 71 * L + Num.logarithmCost L P E + 14 * E +
        (19 * C.d + 32) * M.size + 310 * (C.d - 1) + 530 := by
  dsimp only
  intro hlog hroom hprec hcut
  obtain ⟨saved, hs, h120, h121, hm', hf⟩ :=
    saveInitDepthNumericFormat_runs (w := w) (p := p) (ω := ω) (st := st)
  obtain ⟨mid, cost, ret, hr, hd, hk, h99, hlo, hhi, hroomRet, hmem, hz', hlow, hhigh, hc⟩ :=
    initRuntimeWorkspaceChainDimensions_runs hbits hload hround hbranch
      ((hf 22 (by decide) (by decide)).trans hm) hM hMw hh hhw
      ((hf 98 (by decide) (by decide)).trans ha) (hm'.symm ▸ hz) hlog hroom hprec hcut
  obtain ⟨out, hr', h67, h68, h98, hm'', hf'⟩ :=
    restoreInitDepthNumericFormat_runs (w := w) (p := p) (ω := ω) (st := mid)
  refine ⟨out, cost + 15, ret, runs_seq_iff.mpr (Or.inr ⟨saved, 5, cost + 9, hs,
    runs_seq_iff.mpr (Or.inr ⟨mid, cost, 8, hr, hr', by omega⟩), by omega⟩),
    (hf' 75 (by decide) (by decide) (by decide)).trans hd,
    (hf' 76 (by decide) (by decide) (by decide)).trans hk, h98.trans h99, by omega, hhi, hroomRet,
    fun x hx => (congrFun hm'' x).trans ((hmem x hx).trans (congrFun hm' x)),
    hm''.symm ▸ hz', ?_, ?_, by omega⟩
  · intro r hlt h75 h76
    by_cases h67' : r = 67
    · subst r
      exact h67.trans ((hhigh 128 (Or.inr le_rfl)).trans h120)
    by_cases h68' : r = 68
    · subst r
      exact h68.trans ((hhigh 129 (Or.inr (by decide))).trans h121)
    exact (hf' r h67' h68' (by omega)).trans
      ((hlow r (by omega) h67' h68' h75 h76).trans (hf r (by omega) (by omega)))
  · intro r hlo' hhi'
    exact (hf' r (by omega) (by omega) (by omega)).trans
      ((hhigh r (Or.inl ⟨hlo', hhi'⟩)).trans (hf r (by omega) (by omega)))


/-- Run the sparsifier selector with a separate numeric workspace. -/
@[expose] def solverSparseCoreWithDepthWorkspace (bits load log roundEntry h : ℕ)
    (retry : Stmt) : Stmt :=
  saveInitDepthNumericFormat ;;
  initRuntimeWorkspaceSparseCoreDepth bits load log roundEntry h retry ;;
  restoreInitDepthNumericFormat

/-- The sparsifier selector installs the model dimensions and advances the
heap while preserving the solver format. -/
theorem solverSparseCoreWithDepthWorkspace_runs {w h bits load log roundEntry a M : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {retry : Stmt}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hround : MeetsContract w p roundEntry (initDepthEndpointContract w h))
    (hm : st.regs 23 = M ^ 2) (hM : 1 ≤ M) (hMw : M ^ 2 + 2 < 2 ^ w)
    (hh : 0 < h) (hhw : h < 2 ^ w) (ha : st.regs 98 = a) (hz : ZeroFrom st.mem a) :
    let E := (M ^ 2 + 2).size
    let q := 38 * (2 ^ 24 * E) ^ 8 + E
    let P := h * (q + E + 10)
    let L := P + E + 4
    let depth := Expander.chosenL (M ^ 2)
    MeetsContract w p log (Num.logarithmContract w h q) →
    a + L + L + Num.logarithmSpace L P E < 2 ^ w → 2 * P + 9 < 2 ^ w →
    depth ^ 24 + 1 < 2 ^ w →
    ∃ out cost ret, Runs w p ω (solverSparseCoreWithDepthWorkspace bits load log roundEntry h retry)
        st .normal out cost ∧ out.regs 44 = depth ∧ out.regs 98 = ret ∧
      a ≤ ret ∧ ret < 2 ^ w ∧ ret ≤ a + L + L + Num.logarithmSpace L P E ∧
      (∀ x < a, out.mem x = st.mem x) ∧ ZeroFrom out.mem ret ∧
      (∀ r < 98, r ≠ 44 → out.regs r = st.regs r) ∧
      (∀ r, 101 ≤ r → r ≤ 104 → out.regs r = st.regs r) ∧
      cost ≤ 71 * L + Num.logarithmCost L P E + 14 * E +
        166 * (depth - 1) + 363 := by
  dsimp only
  intro hlog hroom hprec hcut
  obtain ⟨saved, hs, h120, h121, hm', hf⟩ :=
    saveInitDepthNumericFormat_runs (w := w) (p := p) (ω := ω) (st := st)
  obtain ⟨mid, cost, ret, hr, hd, h99, hlo, hhi, hroomRet, hmem, hz', hlow, hhigh, hc⟩ :=
    initRuntimeWorkspaceSparseCoreDepth_runs hbits hload hround
      ((hf 23 (by decide) (by decide)).trans hm) hM hMw hh hhw
      ((hf 98 (by decide) (by decide)).trans ha) (hm'.symm ▸ hz) hlog hroom hprec hcut
  obtain ⟨out, hr', h67, h68, h98, hm'', hf'⟩ :=
    restoreInitDepthNumericFormat_runs (w := w) (p := p) (ω := ω) (st := mid)
  refine ⟨out, cost + 15, ret, runs_seq_iff.mpr (Or.inr ⟨saved, 5, cost + 9, hs,
    runs_seq_iff.mpr (Or.inr ⟨mid, cost, 8, hr, hr', by omega⟩), by omega⟩),
    (hf' 44 (by decide) (by decide) (by decide)).trans hd, h98.trans h99, by omega, hhi, hroomRet,
    fun x hx => (congrFun hm'' x).trans ((hmem x hx).trans (congrFun hm' x)),
    hm''.symm ▸ hz', ?_, ?_, by omega⟩
  · intro r hlt h44
    by_cases h67' : r = 67
    · subst r
      exact h67.trans ((hhigh 128 (Or.inr le_rfl)).trans h120)
    by_cases h68' : r = 68
    · subst r
      exact h68.trans ((hhigh 129 (Or.inr (by decide))).trans h121)
    exact (hf' r h67' h68' (by omega)).trans
      ((hlow r (by omega) h67' h68' h44).trans (hf r (by omega) (by omega)))
  · intro r hlo' hhi'
    exact (hf' r (by omega) (by omega) (by omega)).trans
      ((hhigh r (Or.inl ⟨hlo', hhi'⟩)).trans (hf r (by omega) (by omega)))


/-- Compute the augmented instance's padded edge count before running the
chain selector with its own numeric workspace. -/
@[expose] def prepareSolverChainWithDepthWorkspace
    (threshold bits load log roundEntry h branch : ℕ) (retry : Stmt) : Stmt :=
  initConcreteBucketBaseEdgeBound threshold ;;
  solverChainWithDepthWorkspace bits load log roundEntry h branch retry

/-- Padding uses the augmented instance's edge count. The chain selector
uses that same padded count and retains it for the bucket calculation. -/
theorem prepareSolverChainWithDepthWorkspace_runs
    {w threshold bits load log roundEntry h branch a : ℕ} (I : Instance)
    {p : Program} {ω : ℕ → Bool} {st : State} {retry : Stmt}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hround : MeetsContract w p roundEntry (initDepthEndpointContract w h))
    (hbranch : MeetsContract w p branch (minRatioBranchCountContract w))
    (hm : st.regs 0 = (IPM.namedInstance I).m)
    (hh : 0 < h) (hhw : h < 2 ^ w) (ha : st.regs 98 = a) (hz : ZeroFrom st.mem a)
    (hM : 1 ≤ max I.m threshold) (hMw : max I.m threshold + 2 < 2 ^ w) :
    let M := max I.m threshold
    let E := (M + 2).size
    let q := 38 * (2 ^ 48 * E) ^ 8 + E
    let P := h * (q + E + 10)
    let L := P + E + 4
    let C := Chain.concreteChainParams M hM
    MeetsContract w p log (Num.logarithmContract w h q) →
    a + L + L + Num.logarithmSpace L P E < 2 ^ w →
    ∃ out cost ret, Runs w p ω (prepareSolverChainWithDepthWorkspace threshold bits load log roundEntry h branch retry)
        st .normal out cost ∧ out.regs 22 = M ∧ out.regs 75 = C.d ∧ out.regs 76 = C.k ∧
      out.regs 98 = ret ∧ a ≤ ret ∧ ret < 2 ^ w ∧ ret ≤ a + L + L + Num.logarithmSpace L P E ∧
      (∀ x < a, out.mem x = st.mem x) ∧ ZeroFrom out.mem ret ∧
      (∀ r < 98, r ≠ 22 → r ≠ 75 → r ≠ 76 → out.regs r = st.regs r) ∧
      cost ≤ 71 * L + Num.logarithmCost L P E + 14 * E +
        (19 * C.d + 32) * M.size + 310 * (C.d - 1) + 537 := by
  dsimp only
  intro hlog hroom
  let E := (max I.m threshold + 2).size
  let P := h * (38 * (2 ^ 48 * E) ^ 8 + E + E + 10)
  have hE : 1 ≤ E := Nat.lt_size.mpr (by norm_num)
  have hprec := initDepthLog_series_guard (a := a) (P := P) hE hroom
  have hcut := initRuntimeDepth_cutoff_word hh (initRuntimeChainDepth_cutoff_le hM) hprec
  have hIw : I.m < 2 ^ w := (le_max_left I.m threshold).trans_lt (by omega)
  have htw : threshold < 2 ^ w := (le_max_right I.m threshold).trans_lt (by omega)
  obtain ⟨mid, hr, h22, hmem, hf⟩ := initConcreteBucketBaseEdgeBound_runs (p := p) (ω := ω) hm
    (by simpa only [IPM.namedInstance_m] using hIw) htw
  rw [namedInstance_initBaseEdgeBound] at h22
  obtain ⟨out, c, ret, hr', hd, hk, h98, hlo, hhi, hroomRet, hmem', hz', hf', _, hc⟩ :=
    solverChainWithDepthWorkspace_runs hbits hload hround hbranch h22 hM hMw hh hhw
      ((hf 98 (by decide)).trans ha) (hmem.symm ▸ hz) hlog hroom hprec hcut
  exact ⟨out, 6 + c + 1, ret, runs_seq_iff.mpr (Or.inr ⟨mid, 6, c, hr, hr', rfl⟩),
    (hf' 22 (by decide) (by decide) (by decide)).trans h22, hd, hk, h98, hlo, hhi, hroomRet,
    fun x hx => (hmem' x hx).trans (congrFun hmem x), hz',
    fun r hr h22' h75 h76 => (hf' r hr h75 h76).trans (hf r h22'), by omega⟩

/-- Bounds for the augmented graph and the fixed padding threshold give
input power bounds for both depth logarithms. -/
theorem initDepthPaddedSize_power_bounds {m n augmented threshold base degree : ℕ}
    (hbase : n + m + 2 ≤ base) (hgraph : augmented ≤ m + 2 * n)
    (hthreshold : threshold ≤ base ^ degree) :
    let M := max augmented threshold
    let d := max 2 (degree + 1)
    M + 2 ≤ base ^ d ∧ M ^ 2 + 2 ≤ base ^ (2 * d) := by
  dsimp only
  have hb : 2 ≤ base := by omega
  have hgraph' : augmented + 2 ≤ base ^ 2 := by
    have ht : augmented + 2 ≤ 2 * base := by omega
    exact ht.trans (by rw [pow_two]; exact Nat.mul_le_mul_right base hb)
  have hthreshold' : threshold + 2 ≤ base ^ max 2 (degree + 1) := by
    by_cases hd : degree = 0
    · subst degree
      simp only [pow_zero] at hthreshold
      have hfour : 4 ≤ base ^ 2 := by
        exact Nat.pow_le_pow_left hb 2
      exact (show threshold + 2 ≤ base ^ 2 by omega).trans
        (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
    · have hp : 2 ≤ base ^ degree := by
        have hpow := Nat.pow_le_pow_right (by omega : 0 < base) (show 1 ≤ degree by omega)
        rw [pow_one] at hpow
        exact hb.trans hpow
      have ht : threshold + 2 ≤ base ^ (degree + 1) := by
        rw [pow_succ]
        exact (show threshold + 2 ≤ 2 * base ^ degree by omega).trans
          (by simpa only [mul_comm] using Nat.mul_le_mul_right (base ^ degree) hb)
      exact ht.trans (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
  have hm : max augmented threshold + 2 ≤ base ^ max 2 (degree + 1) := by
    rcases le_total augmented threshold with h | h
    · rwa [max_eq_right h]
    · rw [max_eq_left h]
      exact hgraph'.trans (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
  refine ⟨hm, ?_⟩
  rw [Nat.mul_comm 2, pow_mul]
  exact (show (max augmented threshold) ^ 2 + 2 ≤ (max augmented threshold + 2) ^ 2 by
    calc
      _ ≤ (max augmented threshold) ^ 2 + 4 * max augmented threshold + 4 := by omega
      _ = _ := by ring).trans (Nat.pow_le_pow_left hm _)

/-- The encoded circulation bounds both depth inputs after connected
augmentation and padding by the fixed threshold. -/
theorem solverDepthPaddedSize_power_bounds (J : Scaling.Circulation) (threshold : ℕ) :
    let base := J.solverWords.length + J.solverWords.foldr max 0 + 2
    let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
    let d := max 2 (Nat.clog 2 threshold + 1)
    M + 2 ≤ base ^ d ∧ M ^ 2 + 2 ≤ base ^ (2 * d) := by
  dsimp only
  let base := J.solverWords.length + J.solverWords.foldr max 0 + 2
  have hb : 2 ≤ base := by unfold base; omega
  have hn : J.n ≤ J.solverWords.foldr max 0 := le_max_left _ _
  have hlen := J.solverWords_length
  have hbase : J.n + J.m + 2 ≤ base := by unfold base; omega
  have hgraph := IPM.connectedInitialInstance_m_le J.toInstance (IPM.Machine.solverPenalty J.m : ℤ)
  rw [Scaling.Circulation.toInstance_m] at hgraph
  have ht : threshold ≤ base ^ Nat.clog 2 threshold :=
    (Nat.le_pow_clog (by decide : 1 < 2) threshold).trans (Nat.pow_le_pow_left hb _)
  exact initDepthPaddedSize_power_bounds hbase hgraph ht

/-- A single fixed multiplier covers the chain and sparsifier depth
workspaces for the encoded solver input. -/
theorem solverDepthWordSize_bounds (J : Scaling.Circulation) {threshold h a b da db c : ℕ} :
    let input := J.solverWords
    let base := input.length + input.foldr max 0 + 2
    let d := max 2 (Nat.clog 2 threshold + 1)
    let cd := Nat.clog 2 (h * (38 * (2 ^ 48) ^ 8 + 12) + 5)
    a ≤ base ^ da → b ≤ base ^ db →
    max (max da db) (10 + 3 * (cd + 8 * (2 * d))) + 1 ≤ c →
    let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
    let E₁ := (M + 2).size
    let E₂ := (M ^ 2 + 2).size
    let P₁ := h * (38 * (2 ^ 48 * E₁) ^ 8 + E₁ + E₁ + 10)
    let P₂ := h * (38 * (2 ^ 24 * E₂) ^ 8 + E₂ + E₂ + 10)
    let L₁ := P₁ + E₁ + 4
    let L₂ := P₂ + E₂ + 4
    let w := wordSize c input
    M + 2 < 2 ^ w ∧ M ^ 2 + 2 < 2 ^ w ∧ h < 2 ^ w ∧
      a + L₁ + L₁ + Num.logarithmSpace L₁ P₁ E₁ < 2 ^ w ∧
      b + L₂ + L₂ + Num.logarithmSpace L₂ P₂ E₂ < 2 ^ w := by
  dsimp only
  intro ha hb hc
  let input := J.solverWords
  let base := input.length + input.foldr max 0 + 2
  let cd := Nat.clog 2 (h * (38 * (2 ^ 48) ^ 8 + 12) + 5)
  let d := max 2 (Nat.clog 2 threshold + 1)
  have hbase : 2 ≤ base := by unfold base; omega
  have hcoeff : h * (38 * (2 ^ 48) ^ 8 + 12) + 5 ≤ base ^ cd :=
    (Nat.le_pow_clog (by decide : 1 < 2) _).trans (Nat.pow_le_pow_left hbase _)
  have hcoeff' : h * (38 * (2 ^ 24) ^ 8 + 12) + 5 ≤ base ^ cd := by
    apply le_trans _ hcoeff
    gcongr
    decide
  obtain ⟨hs, hs'⟩ := solverDepthPaddedSize_power_bounds J threshold
  have hda : max da (10 + 3 * (cd + 8 * d)) + 1 ≤ c := by
    change max (max da db) (10 + 3 * (cd + 8 * (2 * d))) + 1 ≤ c at hc
    omega
  have hdb : max db (10 + 3 * (cd + 8 * (2 * d))) + 1 ≤ c := by
    change max (max da db) (10 + 3 * (cd + 8 * (2 * d))) + 1 ≤ c at hc
    omega
  obtain ⟨hm, hh, hroom⟩ := initDepthLog_runtime_size_budget
    (exponent := 48) (multiplier := c) input hs ha hcoeff hda
  obtain ⟨hm', _, hroom'⟩ := initDepthLog_runtime_size_budget
    (exponent := 24) (multiplier := c) input hs' hb hcoeff' hdb
  exact ⟨hm, hm', hh, hroom, hroom'⟩

/-- A power bound on the solver input and cursor suffices for the
multiword chain initializer's word and workspace requirements. -/
theorem prepareSolverChainWithDepthWorkspace_wordSize_runs
    {threshold bits load log roundEntry h branch a sizeDegree cursorDegree coefficientDegree c : ℕ}
    (I : Instance) (input : List ℕ)
    {p : Program} {ω : ℕ → Bool} {st : State} {retry : Stmt}
    (hbits : MeetsContract (wordSize c input) p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract (wordSize c input) p load (Num.loadSmallContract (wordSize c input) h))
    (hround : MeetsContract (wordSize c input) p roundEntry (initDepthEndpointContract (wordSize c input) h))
    (hbranch : MeetsContract (wordSize c input) p branch (minRatioBranchCountContract (wordSize c input)))
    (hm : st.regs 0 = (IPM.namedInstance I).m)
    (hh : 0 < h) (ha : st.regs 98 = a) (hz : ZeroFrom st.mem a)
    (hM : 1 ≤ max I.m threshold) :
    let base := input.length + input.foldr max 0 + 2
    max I.m threshold + 2 ≤ base ^ sizeDegree →
    a ≤ base ^ cursorDegree →
    h * (38 * (2 ^ 48) ^ 8 + 12) + 5 ≤ base ^ coefficientDegree →
    max cursorDegree (10 + 3 * (coefficientDegree + 8 * sizeDegree)) + 1 ≤ c →
    let M := max I.m threshold
    let E := (M + 2).size
    let q := 38 * (2 ^ 48 * E) ^ 8 + E
    let P := h * (q + E + 10)
    let L := P + E + 4
    let C := Chain.concreteChainParams M hM
    MeetsContract (wordSize c input) p log (Num.logarithmContract (wordSize c input) h q) →
    ∃ out cost ret, Runs (wordSize c input) p ω (prepareSolverChainWithDepthWorkspace threshold bits load log roundEntry h branch retry)
        st .normal out cost ∧ out.regs 22 = M ∧ out.regs 75 = C.d ∧ out.regs 76 = C.k ∧
      out.regs 98 = ret ∧ a ≤ ret ∧ ret < 2 ^ wordSize c input ∧ ret ≤ a + L + L + Num.logarithmSpace L P E ∧
      (∀ x < a, out.mem x = st.mem x) ∧ ZeroFrom out.mem ret ∧
      (∀ r < 98, r ≠ 22 → r ≠ 75 → r ≠ 76 → out.regs r = st.regs r) ∧
      cost ≤ 71 * L + Num.logarithmCost L P E + 14 * E +
        (19 * C.d + 32) * M.size + 310 * (C.d - 1) + 537 := by
  dsimp only
  intro hsize hcursor hcoeff hdegree hlog
  obtain ⟨hmw, hhw, hroom⟩ := initDepthLog_runtime_size_budget
    (M := max I.m threshold) (exponent := 48) input hsize hcursor hcoeff hdegree
  exact prepareSolverChainWithDepthWorkspace_runs I hbits hload hround hbranch
    hm hh hhw ha hz hM hmw hlog hroom

/-- Stage the solver inputs and select the chain dimensions. -/
@[expose] def prepareSolverRuntimeDimensions (threshold bits load log pack branch : ℕ)
    (retry : Stmt) : Stmt :=
  stageSolverRuntimeDimensions threshold ;; initRuntimeChainDimensions bits load log pack branch retry

/-- The staged solver prefix adds a fixed cost to the runtime dimension run. -/
theorem prepareSolverRuntimeDimensions_runs
    {w threshold bits load log pack branch cost : ℕ}
    {p : Program} {ω : ℕ → Bool} {st ready out : State} {retry : Stmt}
    (hs : Runs w p ω (stageSolverRuntimeDimensions threshold) st .normal ready 23)
    (hd : Runs w p ω (initRuntimeChainDimensions bits load log pack branch retry) ready .normal out cost) :
    Runs w p ω (prepareSolverRuntimeDimensions threshold bits load log pack branch retry)
      st .normal out (cost + 24) :=
  runs_seq_iff.mpr (Or.inr ⟨ready, 23, cost, hs, hd, by omega⟩)

/-- Run the chain selector on the staged cap of the augmented instance
and retain its certified depth and branch count. -/
theorem prepareSolverRuntimeDimensions_certified_runs
    {w threshold precision heap nextHeap N V limbs bits load log pack branch cost : ℕ}
    (I : Instance) (hM : 1 ≤ max I.m threshold)
    {p : Program} {ω : ℕ → Bool} {st : State} {retry : Stmt}
    (hm : st.regs 0 = (IPM.namedInstance I).m) (hmw : I.m < 2 ^ w) (ht : threshold < 2 ^ w)
    (ha : st.regs 4 = heap) (hP : st.regs 68 = precision) (hw : precision < w)
    (hV : st.regs 1 = V) (hL : st.regs 2 = limbs) (hp : st.regs 3 = precision) :
    let M := max I.m threshold
    let P := Chain.concreteChainParams M hM
    (∀ ready, ready.regs 22 = M → ready.regs 4 = 2 ^ precision → ready.regs 101 = heap →
      ready.regs 102 = V → ready.regs 103 = limbs → ready.regs 104 = precision → ready.mem = st.mem →
      (∀ r, r ≠ 22 → r ≠ 4 → r ≠ 101 → r ≠ 102 → r ≠ 103 → r ≠ 104 →
        ready.regs r = st.regs r) →
      ∃ out, Runs w p ω (initRuntimeChainDimensions bits load log pack branch retry)
        ready .normal out cost ∧
        out.regs 22 = M ∧ out.regs 75 = P.d ∧ out.regs 76 = P.k ∧
        out.regs 92 = N ∧ out.regs 98 = nextHeap ∧ out.regs 4 = 2 ^ precision ∧ ZeroFrom out.mem nextHeap ∧
        out.regs 6 = ready.regs 6 ∧ out.regs 67 = ready.regs 67 ∧ out.regs 68 = ready.regs 68) →
    ∃ out, Runs w p ω (prepareSolverRuntimeDimensions threshold bits load log pack branch retry)
      st .normal out (cost + 24) ∧ out.regs 22 = M ∧ out.regs 75 = P.d ∧ out.regs 76 = P.k ∧
        out.regs 92 = N ∧ out.regs 98 = nextHeap ∧ out.regs 4 = 2 ^ precision ∧ ZeroFrom out.mem nextHeap ∧
        out.regs 6 = st.regs 6 ∧ out.regs 67 = st.regs 67 ∧ out.regs 68 = precision := by
  dsimp only
  intro hselect
  obtain ⟨ready, hr, hcap, hscale, hheap, hV', hL', hP', hmem, hregs⟩ :=
    stageSolverRuntimeDimensions_runs I (p := p) (ω := ω) hm hmw ht ha hP hw hV hL hp
  obtain ⟨out, hd, hcap', hdepth, hbranch, hN, hnext, hscale', hzero, h6, h67, h68⟩ :=
    hselect ready hcap hscale hheap hV' hL' hP' hmem hregs
  exact ⟨out, prepareSolverRuntimeDimensions_runs hr hd, hcap', hdepth, hbranch, hN, hnext, hscale', hzero,
    h6.trans (hregs 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)),
    h67.trans (hregs 67 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)),
    h68.trans ((hregs 68 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hP)⟩

/-- Decode the solver inputs, pack the graph and select the chain
dimensions using the padded bound and its runtime logarithm. -/
@[expose] def prepareSolverInitWithRuntimeDepth
    (alpha select quality graphPack threshold bits load log pack branch : ℕ) (retry : Stmt) : Stmt :=
  prepareMinRatioSolverThresholdInputs alpha select quality graphPack ;;
  prepareSolverRuntimeDimensions threshold bits load log pack branch retry

/-- The runtime-depth prefix charges input preparation and dimension selection. -/
theorem prepareSolverInitWithRuntimeDepth_runs
    {w alpha select quality graphPack threshold bits load log pack branch inputCost dimensionCost : ℕ}
    {p : Program} {ω : ℕ → Bool} {st ready out : State} {retry : Stmt}
    (hi : Runs w p ω (prepareMinRatioSolverThresholdInputs alpha select quality graphPack)
      st .normal ready inputCost)
    (hd : Runs w p ω (prepareSolverRuntimeDimensions threshold bits load log pack branch retry)
      ready .normal out dimensionCost) :
    Runs w p ω (prepareSolverInitWithRuntimeDepth alpha select quality graphPack threshold
      bits load log pack branch retry) st .normal out (inputCost + dimensionCost + 1) :=
  runs_seq_iff.mpr (Or.inr ⟨ready, inputCost, dimensionCost, hi, hd, rfl⟩)

/-- Run bucket selection after the runtime-depth solver prefix. -/
@[expose] def prepareSolverBucketWithRuntimeDepth
    (alpha select quality graphPack threshold branch lower upper denominator power bits load log pack : ℕ)
    (retry : Stmt) : Stmt :=
  prepareSolverInitWithRuntimeDepth alpha select quality graphPack threshold bits load log pack branch retry ;;
  initConcreteBucketCapWithWitness lower upper denominator power bits load log pack

/-- The bucket phase starts from the selected chain dimensions. Its
certificate and the frame below the initial heap carry through the prefix. -/
theorem prepareSolverBucketWithRuntimeDepth_runs
    {w alpha select quality graphPack threshold branch lower upper denominator power bits load log pack
      prefixCost bucketCost heap cap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st ready out : State} {retry : Stmt}
    (hprefix : Runs w p ω
      (prepareSolverInitWithRuntimeDepth alpha select quality graphPack threshold bits load log pack branch retry)
      st .normal ready prefixCost)
    (hbucket : Runs w p ω (initConcreteBucketCapWithWitness lower upper denominator power bits load log pack)
      ready .normal out bucketCost)
    (hcap : out.regs 18 = 1 → out.regs 47 = cap)
    (hprefixFrame : ∀ a < heap, ready.mem a = st.mem a)
    (hheap : heap ≤ ready.regs 98)
    (hbucketFrame : ∀ a < ready.regs 98, out.mem a = ready.mem a) :
    Runs w p ω (prepareSolverBucketWithRuntimeDepth alpha select quality graphPack threshold branch
      lower upper denominator power bits load log pack retry) st .normal out (prefixCost + bucketCost + 1) ∧
      (out.regs 18 = 1 → out.regs 47 = cap) ∧
      (∀ a < heap, out.mem a = st.mem a) :=
  ⟨runs_seq_iff.mpr (Or.inr ⟨ready, prefixCost, bucketCost, hprefix, hbucket, rfl⟩),
    hcap, fun a ha => (hbucketFrame a (ha.trans_le hheap)).trans (hprefixFrame a ha)⟩

open IPM.Machine in
/-- The parameter-word minimum alone does not guarantee that the Init
working scale fits. The caller's word budget must cover the precision too. -/
theorem initWorkingScale_wordBudget_gap :
    ipmQualityParameterWordBits 1 1 1 < ipmQualityPrecision 1 1 1 := by
  decide

/-- Square the padded edge count before selecting the sparsifier depth. -/
@[expose] def prepareSolverSparseCoreWithDepthWorkspace (bits load log roundEntry h : ℕ)
    (retry : Stmt) : Stmt :=
  stageInitSparsifierEdgeCap ;; solverSparseCoreWithDepthWorkspace bits load log roundEntry h retry

/-- Both the squared edge count and its model depth are available to the
factor calculation after restoring the solver format. -/
theorem prepareSolverSparseCoreWithDepthWorkspace_runs
    {w h bits load log roundEntry a M : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {retry : Stmt}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hround : MeetsContract w p roundEntry (initDepthEndpointContract w h))
    (hm : st.regs 22 = M) (hM : 1 ≤ M) (hMw : M ^ 2 + 2 < 2 ^ w)
    (hh : 0 < h) (hhw : h < 2 ^ w) (ha : st.regs 98 = a) (hz : ZeroFrom st.mem a) :
    let E := (M ^ 2 + 2).size
    let q := 38 * (2 ^ 24 * E) ^ 8 + E
    let P := h * (q + E + 10)
    let L := P + E + 4
    let depth := Expander.chosenL (M ^ 2)
    MeetsContract w p log (Num.logarithmContract w h q) →
    a + L + L + Num.logarithmSpace L P E < 2 ^ w →
    ∃ out cost ret, Runs w p ω (prepareSolverSparseCoreWithDepthWorkspace bits load log roundEntry h retry)
        st .normal out cost ∧ out.regs 23 = M ^ 2 ∧ out.regs 44 = depth ∧
      out.regs 98 = ret ∧ a ≤ ret ∧ ret < 2 ^ w ∧ ret ≤ a + L + L + Num.logarithmSpace L P E ∧
      (∀ x < a, out.mem x = st.mem x) ∧ ZeroFrom out.mem ret ∧
      (∀ r < 98, r ≠ 23 → r ≠ 44 → out.regs r = st.regs r) ∧
      (∀ r, 101 ≤ r → r ≤ 104 → out.regs r = st.regs r) ∧
      cost ≤ 71 * L + Num.logarithmCost L P E + 14 * E + 166 * (depth - 1) + 368 := by
  dsimp only
  intro hlog hroom
  let E := (M ^ 2 + 2).size
  let P := h * (38 * (2 ^ 24 * E) ^ 8 + E + E + 10)
  have hE : 1 ≤ E := Nat.lt_size.mpr (by norm_num)
  have hprec := initDepthLog_series_guard (a := a) (P := P) hE hroom
  have hcut := initRuntimeDepth_cutoff_word hh (initRuntimeSparseCoreDepth_cutoff_le hM) hprec
  obtain ⟨mid, hr, h23, hmem, hf⟩ :=
    stageInitSparsifierEdgeCap_runs (w := w) (p := p) (ω := ω) hm (by omega)
  obtain ⟨out, c, ret, hr', hd, h98, hlo, hhi, hroomRet, hmem', hz', hf', hargs, hc⟩ :=
    solverSparseCoreWithDepthWorkspace_runs hbits hload hround h23 hM hMw hh hhw
      ((hf 98 (by decide)).trans ha) (hmem.symm ▸ hz) hlog hroom hprec hcut
  exact ⟨out, 4 + c + 1, ret, runs_seq_iff.mpr (Or.inr ⟨mid, 4, c, hr, hr', rfl⟩),
    (hf' 23 (by decide) (by decide)).trans h23, hd, h98, hlo, hhi, hroomRet,
    fun x hx => (hmem' x hx).trans (congrFun hmem x), hz',
    fun r hr h23' h44 => (hf' r hr h44).trans (hf r h23'),
    fun r hlo' hhi' => (hargs r hlo' hhi').trans (hf r (by omega)), by omega⟩

/-- A power bound on the squared size and cursor suffices at the
solver's word size. -/
theorem prepareSolverSparseCoreWithDepthWorkspace_wordSize_runs
    {h bits load log roundEntry a M sizeDegree cursorDegree coefficientDegree c : ℕ}
    (input : List ℕ)
    {p : Program} {ω : ℕ → Bool} {st : State} {retry : Stmt}
    (hbits : MeetsContract (wordSize c input) p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract (wordSize c input) p load (Num.loadSmallContract (wordSize c input) h))
    (hround : MeetsContract (wordSize c input) p roundEntry (initDepthEndpointContract (wordSize c input) h))
    (hm : st.regs 22 = M) (hM : 1 ≤ M)
    (hh : 0 < h) (ha : st.regs 98 = a) (hz : ZeroFrom st.mem a) :
    let base := input.length + input.foldr max 0 + 2
    M ^ 2 + 2 ≤ base ^ sizeDegree →
    a ≤ base ^ cursorDegree →
    h * (38 * (2 ^ 24) ^ 8 + 12) + 5 ≤ base ^ coefficientDegree →
    max cursorDegree (10 + 3 * (coefficientDegree + 8 * sizeDegree)) + 1 ≤ c →
    let E := (M ^ 2 + 2).size
    let q := 38 * (2 ^ 24 * E) ^ 8 + E
    let P := h * (q + E + 10)
    let L := P + E + 4
    let depth := Expander.chosenL (M ^ 2)
    MeetsContract (wordSize c input) p log (Num.logarithmContract (wordSize c input) h q) →
    ∃ out cost ret, Runs (wordSize c input) p ω (prepareSolverSparseCoreWithDepthWorkspace bits load log roundEntry h retry)
        st .normal out cost ∧ out.regs 23 = M ^ 2 ∧ out.regs 44 = depth ∧
      out.regs 98 = ret ∧ a ≤ ret ∧ ret < 2 ^ wordSize c input ∧ ret ≤ a + L + L + Num.logarithmSpace L P E ∧
      (∀ x < a, out.mem x = st.mem x) ∧ ZeroFrom out.mem ret ∧
      (∀ r < 98, r ≠ 23 → r ≠ 44 → out.regs r = st.regs r) ∧
      (∀ r, 101 ≤ r → r ≤ 104 → out.regs r = st.regs r) ∧
      cost ≤ 71 * L + Num.logarithmCost L P E + 14 * E + 166 * (depth - 1) + 368 := by
  dsimp only
  intro hsize hcursor hcoeff hdegree hlog
  obtain ⟨hmw, hhw, hroom⟩ := initDepthLog_runtime_size_budget
    (M := M ^ 2) (exponent := 24) input hsize hcursor hcoeff hdegree
  exact prepareSolverSparseCoreWithDepthWorkspace_runs hbits hload hround
    hm hM hmw hh hhw ha hz hlog hroom


/-- Compute the squared edge cap, then select the sparsifier depth
from its runtime logarithm. -/
@[expose] def prepareSolverSparsifierDepth (bits load log pack : ℕ) (retry : Stmt) : Stmt :=
  stageInitSparsifierEdgeCap ;; initRuntimeSparseCoreDepth bits load log pack retry

/-- The depth phase starts with the squared padded bound and charges
the cap calculation once. -/
theorem prepareSolverSparsifierDepth_runs {w M bits load log pack cost : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {retry : Stmt} {post : State → Prop}
    (hM : st.regs 22 = M) (hfit : M ^ 2 < 2 ^ w)
    (hdepth : ∀ ready, ready.regs 23 = M ^ 2 → ready.mem = st.mem →
      (∀ r ≠ 23, ready.regs r = st.regs r) →
      ∃ out, Runs w p ω (initRuntimeSparseCoreDepth bits load log pack retry)
        ready .normal out cost ∧ post out) :
    ∃ out, Runs w p ω (prepareSolverSparsifierDepth bits load log pack retry)
      st .normal out (cost + 5) ∧ post out := by
  obtain ⟨ready, hr₁, h23, hm, hf⟩ :=
    stageInitSparsifierEdgeCap_runs (w := w) (p := p) (ω := ω) hM hfit
  obtain ⟨out, hr₂, hout⟩ := hdepth ready h23 hm hf
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨ready, 4, cost, hr₁, hr₂, by omega⟩), hout⟩

/-- A certified sparse-core depth run supplies the same squared padded
edge cap to the factor code and hands off the fresh heap. -/
theorem prepareSolverSparsifierDepth_certified_runs
    {w M bits load log pack heap n scale precision logCost : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {retry : Stmt} {logError : ℝ}
    (hM : st.regs 22 = M) (hMWord : M ^ 2 < 2 ^ w)
    (hw : 1 < 2 ^ w)
    (hlog : ∀ ready, ready.regs 23 = M ^ 2 → ready.mem = st.mem →
      (∀ r ≠ 23, ready.regs r = st.regs r) →
      ∃ logged, Runs w p ω (computeInitDepthLog 23 bits load log pack) ready .normal logged logCost ∧
        logged.regs 23 = M ^ 2 ∧ logged.regs 57 = n ∧ logged.regs 99 = heap ∧ logged.regs 4 = scale ∧
        ZeroFrom logged.mem heap ∧
        (∀ r ∈ ([1, 22, 25, 28, 29, 47, 48, 67, 68, 75, 76] : List ℕ),
          logged.regs r = ready.regs r) ∧
        (logged.regs 107 : ℝ) / scale ≤ Real.log (((M ^ 2 : ℕ) : ℝ) + 2) ∧
        Real.log (((M ^ 2 : ℕ) : ℝ) + 2) ≤ (logged.regs 108 : ℝ) / scale ∧
        Real.log (((M ^ 2 : ℕ) : ℝ) + 2) - logError ≤ (logged.regs 107 : ℝ) / scale ∧
        (logged.regs 108 : ℝ) / scale ≤ Real.log (((M ^ 2 : ℕ) : ℝ) + 2) + logError) :
    let depth := Expander.chosenL (M ^ 2)
    scale = 2 ^ precision → precision + 24 * ((M ^ 2) + 2).size.size ≤ w →
    (((depth - 1) ^ 24 : ℕ) : ℝ) + logError < Real.log (((M ^ 2 : ℕ) : ℝ) + 2) →
    Real.log (((M ^ 2 : ℕ) : ℝ) + 2) + logError ≤ ((depth ^ 24 : ℕ) : ℝ) →
    ∃ out, Runs w p ω (prepareSolverSparsifierDepth bits load log pack retry)
        st .normal out (logCost + 166 * (depth - 1) + 195) ∧
      out.regs 44 = depth ∧ out.regs 23 = M ^ 2 ∧ out.regs 92 = n ∧
      out.regs 98 = heap ∧ out.regs 4 = scale ∧ ZeroFrom out.mem heap ∧
        (∀ r ∈ ([1, 22, 25, 28, 29, 47, 48, 67, 68, 75, 76] : List ℕ), out.regs r = st.regs r) := by
  dsimp only
  intro hscaleEq hbudget hgapLo hgapHi
  have hs : 0 < scale := hscaleEq.symm ▸ Nat.two_pow_pos precision
  have hpos := Nat.zero_lt_of_lt (Expander.one_le_chosenL (M ^ 2))
  have hdepthSize : Expander.chosenL (M ^ 2) ≤ ((M ^ 2) + 2).size :=
    initDepth_le_inputBits (M ^ 2) (1 / 24 : ℝ) (by norm_num) (by norm_num)
  have hdepthBits := Nat.size_le_size hdepthSize
  have hb := (Nat.add_le_add_left (Nat.mul_le_mul_left 24 hdepthBits) precision).trans hbudget
  have hscaled := initDepthPower_wordFits (depth := Expander.chosenL (M ^ 2)) (exponent := 24)
    (by decide) hb
  have hfit := hscaleEq.symm ▸ hscaled
  have hword := (Nat.le_self_pow (by decide : 24 ≠ 0) (Expander.chosenL (M ^ 2))).trans_lt
    ((Nat.le_mul_of_pos_right _ (show 0 < scale from hs)).trans_lt hfit)
  have hr := prepareSolverSparsifierDepth_runs (p := p) (ω := ω) (retry := retry)
    (bits := bits) (load := load) (log := log) (pack := pack)
    (cost := logCost + 166 * (Expander.chosenL (M ^ 2) - 1) + 190)
    (post := fun out => out.regs 44 = Expander.chosenL (M ^ 2) ∧ out.regs 23 = M ^ 2 ∧
      out.regs 92 = n ∧ out.regs 98 = heap ∧ out.regs 4 = scale ∧ ZeroFrom out.mem heap ∧
        (∀ r ∈ ([1, 22, 25, 28, 29, 47, 48, 67, 68, 75, 76] : List ℕ), out.regs r = st.regs r))
    hM hMWord
  exact hr (by
    intro ready h23 hm hk
    obtain ⟨logged, hl, hcap, hn, hh, hscale, hfree, hlogRegs, hlo, hhi, herrorLo, herrorHi⟩ :=
      hlog ready h23 hm hk
    obtain ⟨hprev, hnext⟩ :=
      initDepth_separation_of_error hs herrorLo herrorHi hgapLo hgapHi
    obtain ⟨out, hd, hdepth, hv, hheap, hz, hregs⟩ :=
      initRuntimeSparseCoreDepth_certified_runs (ω := ω) (retry := retry) hl hn hh hscale
        hfree hs hw hlo hhi hpos hword hfit hprev hnext
    refine ⟨out, hd, hdepth, (hregs 23 (by decide)).trans hcap, hv, hheap,
      (hregs 4 (by decide)).trans hscale, hz, ?_⟩
    intro r hr'
    have hlogKeep := hlogRegs r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (hregs _ (by decide)).trans (hlogKeep.trans (hk _ (by decide))))

/-- After bucket certification, compute the runtime sparsifier depth
before constructing the stretch enclosure and rebuild thresholds. -/
@[expose] def initStretchAndThresholdsWithRuntimeDepth
    (factorEntry power bits load log pack decK thr cDeg coefficient witnessDen : ℕ)
    (retry : Stmt) : Stmt :=
  initThresholdsAfterBucketCap
    (prepareSolverSparsifierDepth bits load log pack retry ;;
      initMergedSparsifierFactors factorEntry decK thr cDeg witnessDen ;;
      initThresholdsAfterLength power bits load log pack coefficient)

/-- Charge the depth, factor and threshold phases after
bucket certification. An uncertified bucket clears the threshold flag. -/
theorem initStretchAndThresholdsWithRuntimeDepth_runs
    {w factorEntry power bits load log pack decK thr
      cDeg coefficient witnessDen heap queryLo queryHi depthCost factorCost thresholdCost : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {retry : Stmt} {post : State → Prop}
    (hh : st.regs 99 = heap) (hw : 1 < 2 ^ w)
    (hbody : st.regs 18 = 1 →
      ∃ depth factors out,
        Runs w p ω (prepareSolverSparsifierDepth bits load log pack retry)
          {st with regs := Function.update st.regs 98 heap} .normal depth depthCost ∧
        Runs w p ω (initMergedSparsifierFactors factorEntry decK thr cDeg witnessDen) depth .normal factors factorCost ∧
        Runs w p ω (initThresholdsAfterLength power bits load log pack coefficient) factors .normal out thresholdCost ∧
        factors.regs 114 = queryLo ∧ factors.regs 115 = queryHi ∧ post out) :
    ∃ out cost, Runs w p ω (initStretchAndThresholdsWithRuntimeDepth factorEntry power bits load log pack decK thr cDeg coefficient witnessDen retry)
        st .normal out cost ∧
      (out.regs 10 = 0 ∨ out.regs 114 = queryLo ∧ out.regs 115 = queryHi ∧ post out) ∧ cost ≤ depthCost + factorCost + thresholdCost + 9 := by
  by_cases hflag : st.regs 18 = 1
  · obtain ⟨depth, factors, out, hd, hf, ht, hqLo, hqHi, hp⟩ := hbody hflag
    have hmid := runs_seq_iff.mpr (Or.inr ⟨factors, factorCost, thresholdCost, hf, ht, rfl⟩)
    have hr := runs_seq_iff.mpr (Or.inr ⟨depth, depthCost, factorCost + thresholdCost + 1,
      hd, hmid, rfl⟩)
    obtain ⟨hLo, hHi⟩ := initThresholdsAfterLength_preserves_query ht
    exact ⟨out, _, initThresholdsAfterBucketCap_runs hflag hh hw hr,
      Or.inr ⟨hLo.trans hqLo, hHi.trans hqHi, hp⟩, by omega⟩
  · obtain ⟨out, hr, hzero, _, _⟩ :=
      initThresholdsAfterBucketCap_inconclusive_runs (w := w) (p := p) (ω := ω) hflag hw
    exact ⟨out, 6, hr, Or.inl hzero, by omega⟩

/-- Compute the configuration with runtime depth selection and dispatch to
level construction once the threshold table is certified. -/
@[expose] def solverInitWithRuntimeDepth
    (alpha select quality graphPack threshold branch lower upper denominator power bits load log pack
      factorEntry decK thr cDeg coefficient witnessDen : ℕ)
    (retry levels inconclusive : Stmt) : Stmt :=
  prepareSolverBucketWithRuntimeDepth alpha select quality graphPack threshold branch lower upper denominator
    power bits load log pack retry ;;
  initStretchAndThresholdsWithRuntimeDepth factorEntry power bits load log pack decK thr cDeg coefficient witnessDen retry ;;
  continueSolverInit levels inconclusive

/-- Charge the bucket, threshold and continuation runs and both sequencing steps. -/
theorem solverInitWithRuntimeDepth_runs
    {w alpha select quality graphPack threshold branch lower upper denominator power bits load log pack
      factorEntry decK thr cDeg coefficient witnessDen bucketCost thresholdCost continuationCost : ℕ}
    {p : Program} {ω : ℕ → Bool} {st bucket checked out : State} {retry levels inconclusive : Stmt}
    {outcome : Outcome}
    (hb : Runs w p ω
      (prepareSolverBucketWithRuntimeDepth alpha select quality graphPack threshold branch lower upper denominator
        power bits load log pack retry) st .normal bucket bucketCost)
    (ht : Runs w p ω
      (initStretchAndThresholdsWithRuntimeDepth factorEntry power bits load log pack decK thr cDeg coefficient witnessDen retry) bucket .normal checked thresholdCost)
    (hc : Runs w p ω (continueSolverInit levels inconclusive) checked outcome out continuationCost) :
    Runs w p ω
      (solverInitWithRuntimeDepth alpha select quality graphPack threshold branch lower upper denominator
        power bits load log pack factorEntry decK thr cDeg coefficient witnessDen
        retry levels inconclusive) st outcome out (bucketCost + thresholdCost + continuationCost + 2) :=
  runs_seq_iff.mpr (Or.inr ⟨bucket, bucketCost, thresholdCost + continuationCost + 1, hb,
    runs_seq_iff.mpr (Or.inr ⟨checked, thresholdCost, continuationCost, ht, hc, rfl⟩), by omega⟩)

/-- Charge the depth, factor and threshold phases after
bucket certification. An uncertified bucket clears the threshold flag. -/
theorem initStretchAndThresholdsWithMultiwordDepth_runs
    {w factorEntry power bits load log pack roundEntry h decK thr
      cDeg coefficient witnessDen heap queryLo queryHi depthCost factorCost thresholdCost : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {retry : Stmt} {post : State → Prop}
    (hh : st.regs 99 = heap) (hw : 1 < 2 ^ w)
    (hbody : st.regs 18 = 1 →
      ∃ depth factors out,
        Runs w p ω (prepareSolverSparseCoreWithDepthWorkspace bits load log roundEntry h retry)
          {st with regs := Function.update st.regs 98 heap} .normal depth depthCost ∧
        Runs w p ω (initMergedSparsifierFactors factorEntry decK thr cDeg witnessDen) depth .normal factors factorCost ∧
        Runs w p ω (initThresholdsAfterLength power bits load log pack coefficient) factors .normal out thresholdCost ∧
        factors.regs 114 = queryLo ∧ factors.regs 115 = queryHi ∧ post out) :
    ∃ out cost, Runs w p ω (initThresholdsAfterBucketCap
        (prepareSolverSparseCoreWithDepthWorkspace bits load log roundEntry h retry ;;
          initMergedSparsifierFactors factorEntry decK thr cDeg witnessDen ;;
          initThresholdsAfterLength power bits load log pack coefficient))
        st .normal out cost ∧
      (out.regs 10 = 0 ∨ out.regs 114 = queryLo ∧ out.regs 115 = queryHi ∧ post out) ∧ cost ≤ depthCost + factorCost + thresholdCost + 9 := by
  by_cases hflag : st.regs 18 = 1
  · obtain ⟨depth, factors, out, hd, hf, ht, hqLo, hqHi, hp⟩ := hbody hflag
    have hmid := runs_seq_iff.mpr (Or.inr ⟨factors, factorCost, thresholdCost, hf, ht, rfl⟩)
    have hr := runs_seq_iff.mpr (Or.inr ⟨depth, depthCost, factorCost + thresholdCost + 1,
      hd, hmid, rfl⟩)
    obtain ⟨hLo, hHi⟩ := initThresholdsAfterLength_preserves_query ht
    exact ⟨out, _, initThresholdsAfterBucketCap_runs hflag hh hw hr,
      Or.inr ⟨hLo.trans hqLo, hHi.trans hqHi, hp⟩, by omega⟩
  · obtain ⟨out, hr, hzero, _, _⟩ :=
      initThresholdsAfterBucketCap_inconclusive_runs (w := w) (p := p) (ω := ω) hflag hw
    exact ⟨out, 6, hr, Or.inl hzero, by omega⟩

/-- Stage the bucket scale and save the solver inputs after selecting the
chain dimensions. The fresh cursor and the chain dimensions carry through
this handoff. -/
theorem stageMultiwordInitBucketInputs_runs {w precision alphaPtr V limbs : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (ha : st.regs 4 = alphaPtr) (hP : st.regs 68 = precision) (hPw : precision < w)
    (hV : st.regs 1 = V) (hL : st.regs 2 = limbs) (hp : st.regs 3 = precision) :
    ∃ scaled saved, Runs w p ω stageInitBucketScale st .normal scaled 7 ∧
      Runs w p ω saveSolverInitArguments scaled .normal saved 8 ∧
      saved.regs 4 = 2 ^ precision ∧ saved.regs 101 = alphaPtr ∧
      saved.regs 102 = V ∧ saved.regs 103 = limbs ∧ saved.regs 104 = precision ∧
      saved.mem = st.mem ∧
      (∀ r, r ≠ 4 → r < 101 → saved.regs r = st.regs r) := by
  obtain ⟨scaled, hs, hscale, h101, hk, hm, _⟩ :=
    stageInitBucketScale_runs (w := w) (p := p) (ω := ω) ha hP hPw
  obtain ⟨saved, hs', h102, h103, h104, hk', hm'⟩ :=
    saveSolverInitArguments_runs (w := w) (p := p) (ω := ω)
      ((hk 1 (by decide) (by decide)).trans hV)
      ((hk 2 (by decide) (by decide)).trans hL)
      ((hk 3 (by decide) (by decide)).trans hp)
  exact ⟨scaled, saved, hs, hs', (hk' 4 (by decide) (by decide) (by decide)).trans hscale,
    (hk' 101 (by decide) (by decide) (by decide)).trans h101,
    h102, h103, h104, hm'.trans hm, fun r h4 hr =>
      (hk' r (by omega) (by omega) (by omega)).trans (hk r h4 (by omega))⟩

/-- The chain dimension run hands its heap and selected dimensions to
bucket preparation together with the original solver inputs. -/
theorem stageBucketAfterMultiwordChain_runs
    {w precision alphaPtr V limbs heap threshold bits load log roundEntry h branch cost : ℕ}
    {p : Program} {ω : ℕ → Bool} {st chain : State} {retry : Stmt}
    (hr : Runs w p ω
      (prepareSolverChainWithDepthWorkspace threshold bits load log roundEntry h branch retry)
      st .normal chain cost)
    (hframe : ∀ r < 98, r ≠ 22 → r ≠ 75 → r ≠ 76 → chain.regs r = st.regs r)
    (hheap : chain.regs 98 = heap) (hz : ZeroFrom chain.mem heap)
    (ha : st.regs 4 = alphaPtr) (hP : st.regs 68 = precision) (hPw : precision < w)
    (hV : st.regs 1 = V) (hL : st.regs 2 = limbs) (hp : st.regs 3 = precision) :
    ∃ out, Runs w p ω
        (prepareSolverChainWithDepthWorkspace threshold bits load log roundEntry h branch retry ;;
          stageInitBucketScale ;; saveSolverInitArguments) st .normal out (cost + 17) ∧
      out.regs 4 = 2 ^ precision ∧ out.regs 101 = alphaPtr ∧ out.regs 102 = V ∧
      out.regs 103 = limbs ∧ out.regs 104 = precision ∧ out.regs 98 = heap ∧
      out.mem = chain.mem ∧ ZeroFrom out.mem heap ∧
      (∀ r, r ≠ 4 → r < 101 → out.regs r = chain.regs r) := by
  have keep (r : ℕ) (hr : r < 98 := by decide) (h22 : r ≠ 22 := by decide)
      (h75 : r ≠ 75 := by decide) (h76 : r ≠ 76 := by decide) :=
    hframe r hr h22 h75 h76
  obtain ⟨scaled, out, hs, hs', hscale, h101, h102, h103, h104, hm, hf⟩ :=
    stageMultiwordInitBucketInputs_runs
      ((keep 4).trans ha) ((keep 68).trans hP) hPw
      ((keep 1).trans hV) ((keep 2).trans hL) ((keep 3).trans hp)
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨chain, cost, 16, hr,
    runs_seq_iff.mpr (Or.inr ⟨scaled, 7, 8, hs, hs', rfl⟩), by omega⟩),
    hscale, h101, h102, h103, h104, (hf 98 (by decide) (by decide)).trans hheap,
    hm, hm.symm ▸ hz, hf⟩

/-- Chain selection and bucket input staging keep the packed graph and
the barrier value available at their original addresses. -/
theorem stageBucketAfterMultiwordChain_preserves_graph_alpha
    {w precision alphaPtr V limbs heap h threshold bits load log roundEntry branch cost : ℕ}
    {p : Program} {ω : ℕ → Bool} {st chain : State} {retry : Stmt} {G : MGraph}
    (hr : Runs w p ω
      (prepareSolverChainWithDepthWorkspace threshold bits load log roundEntry h branch retry)
      st .normal chain cost)
    (hframe : ∀ r < 98, r ≠ 22 → r ≠ 75 → r ≠ 76 → chain.regs r = st.regs r)
    (hheap : chain.regs 98 = heap) (hz : ZeroFrom chain.mem heap)
    (ha : st.regs 4 = alphaPtr) (hP : st.regs 68 = precision) (hPw : precision < w)
    (hV : st.regs 1 = V) (hL : st.regs 2 = limbs) (hp : st.regs 3 = precision)
    (hG : DynSpanner.Program.DynGraphAt st.mem (alphaPtr + (limbs + 1) + 6) G.n G.m G)
    (hExp : st.mem alphaPtr = Num.IPM.alphaExponent G.m V)
    (hValid : Num.Valid st.mem (alphaPtr + 1) h limbs)
    (hAlpha : Num.fixVal st.mem (alphaPtr + 1) h limbs precision = Num.IPM.alphaPrime G.m V / 8)
    (hm : ∀ a < alphaPtr + (limbs + 1) + 6 + DynSpanner.Program.dynGraphSize G.n G.m,
      chain.mem a = st.mem a) :
    ∃ out, Runs w p ω
        (prepareSolverChainWithDepthWorkspace threshold bits load log roundEntry h branch retry ;;
          stageInitBucketScale ;; saveSolverInitArguments) st .normal out (cost + 17) ∧
      out.regs 4 = 2 ^ precision ∧ out.regs 101 = alphaPtr ∧ out.regs 102 = V ∧
      out.regs 103 = limbs ∧ out.regs 104 = precision ∧ out.regs 98 = heap ∧
      ZeroFrom out.mem heap ∧ (∀ r, r ≠ 4 → r < 101 → out.regs r = chain.regs r) ∧
      DynSpanner.Program.DynGraphAt out.mem (alphaPtr + (limbs + 1) + 6) G.n G.m G ∧
      out.mem alphaPtr = Num.IPM.alphaExponent G.m V ∧ Num.Valid out.mem (alphaPtr + 1) h limbs ∧
      Num.fixVal out.mem (alphaPtr + 1) h limbs precision = Num.IPM.alphaPrime G.m V / 8 := by
  obtain ⟨out, ho, h4, h101, h102, h103, h104, h98, hmem, hzero, hkeep⟩ :=
    stageBucketAfterMultiwordChain_runs hr hframe hheap hz ha hP hPw hV hL hp
  exact ⟨out, ho, h4, h101, h102, h103, h104, h98, hzero, hkeep,
    initPackedGraphAlpha_of_frame hG hExp hValid hAlpha
      (fun a h => (congrFun hmem a).trans (hm a h))⟩

/-- Compute the configuration with multiword depth logarithms, then
dispatch to level construction after certifying the threshold table. -/
@[expose] def solverInitWithMultiwordDepth
    (alpha select quality graphPack threshold branch lower upper denominator power bits load log pack
      roundEntry h factorEntry decK thr cDeg coefficient witnessDen : ℕ)
    (retry levels inconclusive : Stmt) : Stmt :=
  prepareMinRatioSolverThresholdInputs alpha select quality graphPack ;;
  prepareSolverChainWithDepthWorkspace threshold bits load log roundEntry h branch retry ;;
  stageInitBucketScale ;; saveSolverInitArguments ;;
  initConcreteBucketCapWithWitness lower upper denominator power bits load log pack ;;
  initThresholdsAfterBucketCap
    (prepareSolverSparseCoreWithDepthWorkspace bits load log roundEntry h retry ;;
      initMergedSparsifierFactors factorEntry decK thr cDeg witnessDen ;;
      initThresholdsAfterLength power bits load log pack coefficient) ;;
  continueSolverInit levels inconclusive

/-- Compose the verified stages of multiword Init, including the
conditional threshold phase and the final continuation. -/
theorem solverInitWithMultiwordDepth_runs
    {w alpha select quality graphPack threshold branch lower upper denominator power bits load log pack
      roundEntry h factorEntry decK thr cDeg coefficient witnessDen
      inputCost chainCost scaleCost argsCost bucketCost thresholdCost continuationCost : ℕ}
    {p : Program} {ω : ℕ → Bool} {st ready chain scaled saved bucket checked out : State}
    {retry levels inconclusive : Stmt} {outcome : Outcome}
    (hi : Runs w p ω (prepareMinRatioSolverThresholdInputs alpha select quality graphPack)
      st .normal ready inputCost)
    (hd : Runs w p ω (prepareSolverChainWithDepthWorkspace threshold bits load log roundEntry h branch retry)
      ready .normal chain chainCost)
    (hs : Runs w p ω stageInitBucketScale chain .normal scaled scaleCost)
    (ha : Runs w p ω saveSolverInitArguments scaled .normal saved argsCost)
    (hb : Runs w p ω (initConcreteBucketCapWithWitness lower upper denominator power bits load log pack)
      saved .normal bucket bucketCost)
    (ht : Runs w p ω (initThresholdsAfterBucketCap
      (prepareSolverSparseCoreWithDepthWorkspace bits load log roundEntry h retry ;;
        initMergedSparsifierFactors factorEntry decK thr cDeg witnessDen ;;
        initThresholdsAfterLength power bits load log pack coefficient)) bucket .normal checked thresholdCost)
    (hc : Runs w p ω (continueSolverInit levels inconclusive) checked outcome out continuationCost) :
    Runs w p ω (solverInitWithMultiwordDepth alpha select quality graphPack threshold branch
      lower upper denominator power bits load log pack roundEntry h factorEntry decK thr cDeg
      coefficient witnessDen retry levels inconclusive)
      st outcome out (inputCost + chainCost + scaleCost + argsCost + bucketCost + thresholdCost +
        continuationCost + 6) := by
  unfold solverInitWithMultiwordDepth
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
