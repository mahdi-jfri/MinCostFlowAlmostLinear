module

public import MinCostFlow.MinRatio.InitBucketAssembly
public import MinCostFlow.MinRatio.InitDepthPower
public import MinCostFlow.MinRatio.InitDepthEndpoint
import MinCostFlow.MinRatio.InitDepthSeparation

/-!
# Runtime chain dimensions

Compute an enclosure of the logarithm of the padded edge count and use
it to select the chain depth and its branch count.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain SparseCore

/-- Compute the padded bound and select its chain dimensions from a
runtime enclosure of the logarithm. -/
@[expose] def initConcreteChainDimensionsFromLog (threshold branchEntry : ℕ) (retry : Stmt) : Stmt :=
  initConcreteBucketBaseEdgeBound threshold ;; selectInitChainDimensions branchEntry 22 retry

/-- A separating enclosure for the padded bound gives the model's depth
and branch count for any word width that fits the arithmetic. -/
theorem initConcreteChainDimensionsFromLog_runs {w m threshold branchEntry lo hi scale : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {retry : Stmt}
    (hbranch : MeetsContract w p branchEntry (minRatioBranchCountContract w))
    (hm : st.regs 0 = m) (hmWord : m < 2 ^ w) (htWord : threshold < 2 ^ w)
    (hM : 1 ≤ max m threshold) (hw : 2 < 2 ^ w)
    (hloReg : st.regs 107 = lo) (hhiReg : st.regs 108 = hi) (hsReg : st.regs 111 = scale)
    (hs : 0 < scale) :
    let M := max m threshold
    let P := concreteChainParams M hM
    P.d < 2 ^ w → P.d ^ 48 * scale < 2 ^ w →
    (lo : ℝ) / scale ≤ Real.log ((M : ℝ) + 2) →
    Real.log ((M : ℝ) + 2) ≤ (hi : ℝ) / scale →
    (P.d - 1) ^ 48 * scale < lo → hi ≤ P.d ^ 48 * scale →
    ∃ out cost, Runs w p ω (initConcreteChainDimensionsFromLog threshold branchEntry retry)
        st .normal out cost ∧ out.regs 22 = M ∧ out.regs 75 = P.d ∧ out.regs 76 = P.k ∧
      out.mem = st.mem ∧
      (∀ r, r ≠ 22 → r ≠ 75 → r ≠ 76 → r ≠ 105 → r ≠ 106 → r ≠ 109 → r ≠ 110 →
        out.regs r = st.regs r) ∧
      cost ≤ (19 * P.d + 32) * M.size + 310 * (P.d - 1) + 354 := by
  dsimp only
  intro hdw hfit hlo hhi hprev hnext
  obtain ⟨mid, hr₁, h22, hm₁, hk₁⟩ :=
    initConcreteBucketBaseEdgeBound_runs (p := p) (ω := ω) hm hmWord htWord
  have hdpos := (chosenD_bounds (by norm_num : (23 : ℝ) / 24 < 1) hM).1
  obtain ⟨out, cost, hr₂, hd, hk, hm₂, hf, hcost⟩ :=
    selectInitChainDimensions_runs (ω := ω) (retry := retry) hbranch
      ((hk₁ 111 (by decide)).trans hsReg) ((hk₁ 107 (by decide)).trans hloReg)
      ((hk₁ 108 (by decide)).trans hhiReg) h22
      (by decide) (by decide) (by decide) (by decide) (by decide)
      rfl hdpos hM hs hw (max_lt hmWord htWord) hdw hfit hlo hhi hprev hnext
  refine ⟨out, 6 + cost + 1, runs_seq_iff.mpr (Or.inr ⟨mid, 6, cost, hr₁, hr₂, rfl⟩),
    (hf 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h22,
    hd, hk, hm₂.trans hm₁,
    fun r h22 h75 h76 h105 h106 h109 h110 =>
      (hf r h75 h76 h105 h106 h109 h110).trans (hk₁ r h22), ?_⟩
  change cost ≤ (19 * (concreteChainParams (max m threshold) hM).d + 32) *
    (max m threshold).size + 310 * ((concreteChainParams (max m threshold) hM).d - 1) + 347 at hcost
  omega

/-- Use the runtime size as the logarithm input and save the
graph's vertex count for the bucket calculation. -/
@[expose] def stageInitDepthLog (sizeReg : ℕ) : Stmt :=
  .assign 57 (.reg 92) ;; .assign 92 (.reg sizeReg) ;; .assign 111 (.reg 4)

/-- The logarithm stage sees the padded count and shares its scale
with the depth selector. -/
theorem stageInitDepthLog_runs {w sizeReg M N scale : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hSizeReg : sizeReg ≠ 57) (hM : st.regs sizeReg = M) (hN : st.regs 92 = N) (hs : st.regs 4 = scale) :
    ∃ out, Runs w p ω (stageInitDepthLog sizeReg) st .normal out 8 ∧
      out.regs 92 = M ∧ out.regs 57 = N ∧ out.regs 111 = scale ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 57 → r ≠ 92 → r ≠ 111 → out.regs r = st.regs r) := by
  let s₁ := {st with regs := Function.update st.regs 57 N}
  let s₂ := {s₁ with regs := Function.update s₁.regs 92 M}
  let out := {s₂ with regs := Function.update s₂.regs 111 scale}
  have h₁ : Runs w p ω (.assign 57 (.reg 92)) st .normal s₁ 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hN], rfl, rfl, rfl⟩
  have h₂ : Runs w p ω (.assign 92 (.reg sizeReg)) s₁ .normal s₂ 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s₁, hSizeReg, hM], rfl, rfl, rfl⟩
  have h₃ : Runs w p ω (.assign 111 (.reg 4)) s₂ .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s₂, s₁, hs], rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨s₁, 2, 5, h₁,
    runs_seq_iff.mpr (Or.inr ⟨s₂, 2, 2, h₂, h₃, rfl⟩), rfl⟩),
    by simp [out, s₂], by simp [out, s₂, s₁], by simp [out], rfl,
    fun r h57 h92 h111 => by simp [out, s₂, s₁, h57, h92, h111]⟩

/-- Compute the logarithm enclosure used by a runtime depth selector. -/
@[expose] def computeInitDepthLog (sizeReg bits load log pack : ℕ) : Stmt :=
  stageInitDepthLog sizeReg ;; computeInitBucketLogBounds bits load log pack 107 108

/-- Compute the enclosure for the padded count and retain the vertex
count and the cursor for subsequent Init calculations. -/
theorem computeInitDepthLog_runs
    {w h sizeReg bits load log pack M N precision limbs heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hlog : MeetsContract w p log (Num.logarithmContract w h (precision - (M + 2).size - 10)))
    (hSizeReg : sizeReg ≠ 57) (hM : st.regs sizeReg = M) (hN : st.regs 92 = N) (hs : st.regs 4 = 2 ^ precision)
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision) (hh : st.regs 98 = heap)
    (hw : M + 2 < 2 ^ w) (hword : (M + 2) * 2 ^ precision < 2 ^ w)
    (hfit : 2 * ((M + 2) * 2 ^ precision) < Num.capacity h limbs)
    (hroom : heap + limbs + limbs + Num.logarithmSpace limbs precision (M + 2).size < 2 ^ w)
    (hz : ZeroFrom st.mem heap) (hdiv : h ∣ precision)
    (hacc : (M + 2).size + 11 ≤ precision) (hcap : precision + (M + 2).size + 4 ≤ h * limbs)
    (hprec : 2 * precision + 9 < 2 ^ w) (hwidth : precision < w)
 :
    ∃ out c ret, Runs w p ω (computeInitDepthLog sizeReg bits load log pack) st .normal out c ∧
      (out.regs 107 : ℝ) / (2 ^ precision : ℕ) ≤ Real.log ((M : ℝ) + 2) ∧
      Real.log ((M : ℝ) + 2) ≤ (out.regs 108 : ℝ) / (2 ^ precision : ℕ) ∧
      (2 ≤ precision - (M + 2).size - 10 → 0 < out.regs 107) ∧
      out.regs 108 ≤ (M + 2) * 2 ^ precision ∧ out.regs 4 = 2 ^ precision ∧
      out.regs 57 = N ∧ out.regs 92 = M ∧ out.regs 99 = ret ∧ heap + limbs ≤ ret ∧
      ret ≤ heap + limbs + limbs + Num.logarithmSpace limbs precision (M + 2).size ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem ret ∧
      (∀ r < 95, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 57 → r ≠ 92 → out.regs r = st.regs r) ∧
      c ≤ 71 * limbs + Num.logarithmCost limbs precision (M + 2).size + 14 * (M + 2).size + 102 ∧
      let error := 2 / (2 : ℝ) ^ (precision - (M + 2).size - 10)
      Real.log ((M : ℝ) + 2) - error ≤ (out.regs 107 : ℝ) / (2 ^ precision : ℕ) ∧
      (out.regs 108 : ℝ) / (2 ^ precision : ℕ) ≤ Real.log ((M : ℝ) + 2) + error := by
  obtain ⟨ready, hr₁, h92, h57, _, hm, hk⟩ :=
    stageInitDepthLog_runs (w := w) (p := p) (ω := ω) hSizeReg hM hN hs
  have keep (r : ℕ) (h57 : r ≠ 57 := by decide) (h92 : r ≠ 92 := by decide)
      (h111 : r ≠ 111 := by decide) := hk r h57 h92 h111
  obtain ⟨out, cost, ret, hr₂, hlo, hhi, hpos, hub, hscale, h99, hret, hbudget, hf, hz', hk', hcost, hel, heu⟩ :=
    computeInitBucketLogBounds_runs (ω := ω) (lower := 107) (upper := 108) hbits hload hpack hlog h92
      ((keep 4).trans hs) ((keep 67).trans hL) ((keep 68).trans hP) ((keep 98).trans hh)
      hw hword hfit hroom (hm.symm ▸ hz) hdiv hacc hcap hprec hwidth
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨out, 8 + cost + 1, ret, runs_seq_iff.mpr (Or.inr ⟨ready, 8, cost, hr₁, hr₂, rfl⟩),
    hlo, hhi, hpos, hub, hscale, ?_, ?_, h99, hret, hbudget,
    fun a ha => (hf a ha).trans (congrFun hm a), hz', ?_, by omega, hel, heu⟩
  · exact (hk' 57 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h57
  · exact (hk' 92 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h92
  · intro r hr h2 h3 h4 h57 h92
    exact (hk' r hr h2 h3 h4 (by omega) (by omega)).trans (keep r h57 h92 (by omega))

/-- Restore the actual vertex count, advance the heap past the
logarithm, and pass its scale to the depth selector. -/
@[expose] def finishInitChainDepthLog : Stmt :=
  .assign 92 (.reg 57) ;;
  .assign 98 (.reg 99) ;;
  .assign 111 (.reg 4)

/-- The handoff saves the logarithm endpoints in registers 107 and 108. -/
theorem finishInitChainDepthLog_runs {w vertices heap scale : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hv : st.regs 57 = vertices) (hh : st.regs 99 = heap) (hs : st.regs 4 = scale) :
    ∃ out, Runs w p ω finishInitChainDepthLog st .normal out 8 ∧
      out.regs 92 = vertices ∧ out.regs 98 = heap ∧ out.regs 111 = scale ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 92 → r ≠ 98 → r ≠ 111 → out.regs r = st.regs r) := by
  let s₁ := {st with regs := Function.update st.regs 92 vertices}
  let s₂ := {s₁ with regs := Function.update s₁.regs 98 heap}
  let out := {s₂ with regs := Function.update s₂.regs 111 scale}
  have h₁ : Runs w p ω (.assign 92 (.reg 57)) st .normal s₁ 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hv], rfl, rfl, rfl⟩
  have h₂ : Runs w p ω (.assign 98 (.reg 99)) s₁ .normal s₂ 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s₁, hh], rfl, rfl, rfl⟩
  have h₃ : Runs w p ω (.assign 111 (.reg 4)) s₂ .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s₂, s₁, hs], rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨s₁, 2, 5, h₁,
    runs_seq_iff.mpr (Or.inr ⟨s₂, 2, 2, h₂, h₃, rfl⟩), rfl⟩),
    by simp [out, s₂, s₁], by simp [out, s₂], by simp [out], rfl,
    fun r h92 h98 h111 => by simp [out, s₂, s₁, h92, h98, h111]⟩

/-- Use the padded edge logarithm to compute the chain dimensions and
pass the vertex count and heap cursor on to the bucket calculation. -/
@[expose] def selectInitDimensionsAfterLog (branch : ℕ) (retry : Stmt) : Stmt :=
  finishInitChainDepthLog ;; selectInitChainDimensions branch 22 retry

/-- With a separating enclosure, the handoff installs the model's chain
dimensions and retains the next available heap word. -/
theorem selectInitDimensionsAfterLog_runs {w M N heap lo hi scale branch : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {retry : Stmt}
    (hbranch : MeetsContract w p branch (minRatioBranchCountContract w))
    (hm : st.regs 22 = M) (hv : st.regs 57 = N) (hh : st.regs 99 = heap)
    (hs : st.regs 4 = scale) (hl : st.regs 107 = lo) (hu : st.regs 108 = hi)
    (hM : 1 ≤ M) (hMw : M < 2 ^ w) (hw : 2 < 2 ^ w) (hsPos : 0 < scale) :
    let P := concreteChainParams M hM
    P.d < 2 ^ w → P.d ^ 48 * scale < 2 ^ w →
    (lo : ℝ) / scale ≤ Real.log ((M : ℝ) + 2) →
    Real.log ((M : ℝ) + 2) ≤ (hi : ℝ) / scale →
    (P.d - 1) ^ 48 * scale < lo → hi ≤ P.d ^ 48 * scale →
    ∃ out cost, Runs w p ω (selectInitDimensionsAfterLog branch retry) st .normal out cost ∧
      out.regs 75 = P.d ∧ out.regs 76 = P.k ∧ out.regs 92 = N ∧ out.regs 98 = heap ∧
      out.regs 22 = M ∧ out.regs 4 = scale ∧
      (∀ r, r ∉ ([75, 76, 92, 98, 105, 106, 109, 110, 111] : List ℕ) → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ cost ≤ (19 * P.d + 32) * M.size + 310 * (P.d - 1) + 356 := by
  dsimp only
  intro hdw hfit hlo hhi hprev hnext
  obtain ⟨ready, hr₁, hn, hheap, hscale, hm₁, hk₁⟩ :=
    finishInitChainDepthLog_runs (w := w) (p := p) (ω := ω) hv hh hs
  have hdpos := (chosenD_bounds (by norm_num : (23 : ℝ) / 24 < 1) hM).1
  have keep (r : ℕ) (h92 : r ≠ 92 := by decide) (h98 : r ≠ 98 := by decide)
      (h111 : r ≠ 111 := by decide) := hk₁ r h92 h98 h111
  obtain ⟨out, c, hr₂, hd, hk, hm₂, hf, hc⟩ :=
    selectInitChainDimensions_runs (ω := ω) (retry := retry) hbranch hscale
      ((keep 107).trans hl) ((keep 108).trans hu) ((keep 22).trans hm)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      rfl hdpos hM hsPos hw hMw hdw hfit hlo hhi hprev hnext
  have hcost : c ≤ (19 * (concreteChainParams M hM).d + 32) * M.size +
      310 * ((concreteChainParams M hM).d - 1) + 347 := hc
  refine ⟨out, 8 + c + 1, runs_seq_iff.mpr (Or.inr ⟨ready, 8, c, hr₁, hr₂, rfl⟩), hd, hk,
    (hf 92 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hn,
    (hf 98 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hheap,
    (hf 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((keep 22).trans hm),
    (hf 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((keep 4).trans hs),
    ?_, hm₂.trans hm₁, by omega⟩
  intro r hreg
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hreg
  obtain ⟨h75, h76, h92, h98, h105, h106, h109, h110, h111⟩ := hreg
  exact (hf r h75 h76 h105 h106 h109 h110).trans (keep r h92 h98 h111)

/-- Compute the padded logarithm and use it to select chain dimensions. -/
@[expose] def initRuntimeChainDimensions (bits load log pack branch : ℕ) (retry : Stmt) : Stmt :=
  computeInitDepthLog 22 bits load log pack ;; selectInitDimensionsAfterLog branch retry

/-- A certified run of the padded logarithm phase supplies the exact
dimensions and a fresh cursor for the next allocation. -/
theorem initRuntimeChainDimensions_runs
    {w M N heap oldHeap scale precision bits load log pack branch logCost : ℕ}
    {p : Program} {ω : ℕ → Bool} {st logged : State} {retry : Stmt} {logError : ℝ}
    (hbranch : MeetsContract w p branch (minRatioBranchCountContract w))
    (hr : Runs w p ω (computeInitDepthLog 22 bits load log pack) st .normal logged logCost)
    (hm : logged.regs 22 = M) (hv : logged.regs 57 = N) (hh : logged.regs 99 = heap)
    (hs : logged.regs 4 = scale) (hM : 1 ≤ M) (hMw : M < 2 ^ w)
    (hw : 2 < 2 ^ w)
    (hf : ∀ a < oldHeap, logged.mem a = st.mem a) (hz : ZeroFrom logged.mem heap) :
    let P := concreteChainParams M hM
    scale = 2 ^ precision → precision + 48 * (M + 2).size.size ≤ w →
    (logged.regs 107 : ℝ) / scale ≤ Real.log ((M : ℝ) + 2) →
    Real.log ((M : ℝ) + 2) ≤ (logged.regs 108 : ℝ) / scale →
    Real.log ((M : ℝ) + 2) - logError ≤ (logged.regs 107 : ℝ) / scale →
    (logged.regs 108 : ℝ) / scale ≤ Real.log ((M : ℝ) + 2) + logError →
    (((P.d - 1) ^ 48 : ℕ) : ℝ) + logError < Real.log ((M : ℝ) + 2) →
    Real.log ((M : ℝ) + 2) + logError ≤ ((P.d ^ 48 : ℕ) : ℝ) →
    ∃ out cost, Runs w p ω (initRuntimeChainDimensions bits load log pack branch retry)
        st .normal out cost ∧
      out.regs 75 = P.d ∧ out.regs 76 = P.k ∧ out.regs 92 = N ∧ out.regs 98 = heap ∧
      out.regs 22 = M ∧ out.regs 4 = scale ∧
      (∀ r, r ∉ ([75, 76, 92, 98, 105, 106, 109, 110, 111] : List ℕ) → out.regs r = logged.regs r) ∧
      (∀ a < oldHeap, out.mem a = st.mem a) ∧ ZeroFrom out.mem heap ∧
      cost ≤ logCost + (19 * P.d + 32) * M.size + 310 * (P.d - 1) + 357 := by
  dsimp only
  intro hscaleEq hbudget hlo hhi herrorLo herrorHi hgapLo hgapHi
  have hsPos : 0 < scale := hscaleEq.symm ▸ Nat.two_pow_pos precision
  have hdepthSize : (concreteChainParams M hM).d ≤ (M + 2).size :=
    initDepth_le_inputBits M ((1 - (23 / 24 : ℝ)) / 2) (by norm_num) (by norm_num)
  have hdepthBits := Nat.size_le_size hdepthSize
  have hb := (Nat.add_le_add_left (Nat.mul_le_mul_left 48 hdepthBits) precision).trans hbudget
  have hscaled := initDepthPower_wordFits (depth := (concreteChainParams M hM).d) (exponent := 48)
    (by decide) hb
  have hfit := hscaleEq.symm ▸ hscaled
  have hdw := (Nat.le_self_pow (by decide : 48 ≠ 0) ((concreteChainParams M hM).d)).trans_lt
    ((Nat.le_mul_of_pos_right _ (show 0 < scale from hsPos)).trans_lt hfit)
  obtain ⟨hprev, hnext⟩ := initDepth_separation_of_error hsPos herrorLo herrorHi hgapLo hgapHi
  obtain ⟨out, cost, hsuffix, hd, hk, hn, hheap, hbase, hscale, hregs, hmem, hcost⟩ :=
    selectInitDimensionsAfterLog_runs (ω := ω) (retry := retry) hbranch hm hv hh hs rfl rfl
      hM hMw hw hsPos hdw hfit hlo hhi hprev hnext
  exact ⟨out, logCost + cost + 1, runs_seq_iff.mpr (Or.inr ⟨logged, logCost, cost, hr, hsuffix, rfl⟩),
    hd, hk, hn, hheap, hbase, hscale, hregs, hmem.symm ▸ hf, hmem.symm ▸ hz, by omega⟩

/-- Scaled integer comparisons certify the sparsifier depth for
Theorem 8.2. -/
theorem initSparseCoreDepth_eq_of_scaledLogBounds (m candidate lo hi scale : ℕ)
    (hc : 0 < candidate) (hs : 0 < scale)
    (hlo : (lo : ℝ) / scale ≤ Real.log ((m : ℝ) + 2))
    (hhi : Real.log ((m : ℝ) + 2) ≤ (hi : ℝ) / scale)
    (hprev : (candidate - 1) ^ 24 * scale < lo)
    (hnext : hi ≤ candidate ^ 24 * scale) :
    Expander.chosenL m = candidate := by
  have hs' : (0 : ℝ) < scale := by exact_mod_cast hs
  have hu : Expander.chosenL m ≤ candidate :=
    (initSparseCoreDepth_le_iff m candidate).2
      (hhi.trans ((div_le_iff₀ hs').2 (by exact_mod_cast hnext)))
  have hl : ¬ Expander.chosenL m ≤ candidate - 1 := by
    intro h
    have hp : ((candidate - 1 : ℕ) : ℝ) ^ (24 : ℕ) < (lo : ℝ) / scale :=
      (lt_div_iff₀ hs').2 (by exact_mod_cast hprev)
    exact (hp.trans_le hlo).not_ge ((initSparseCoreDepth_le_iff m (candidate - 1)).1 h)
  omega

/-- When the input-size and accuracy bounds give the two depth-two
gaps, the real logarithm certifies the model's sparse-core depth. -/
theorem initSparseCoreDepth_eq_two_of_inputBits {m : ℕ}
    (hm : 1 ≤ m) (hbits : (m + 2).size < 2 ^ 24) :
    Expander.chosenL m = 2 := by
  obtain ⟨hlo, hhi⟩ := initDepthTwo_gaps_of_accuracy hm hbits (by decide : 5 ≤ 5)
  have herror : (0 : ℝ) ≤ 2 / (2 : ℝ) ^ (5 : ℕ) := by positivity
  have hup : Real.log ((m : ℝ) + 2) ≤ (2 : ℝ) ^ (24 : ℕ) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using (le_add_of_nonneg_right herror).trans hhi
  have hdown : ((1 : ℕ) : ℝ) ^ (24 : ℕ) < Real.log ((m : ℝ) + 2) := by
    have h := (le_add_of_nonneg_right herror).trans_lt hlo
    simpa only [Nat.reduceSub, one_pow, Nat.cast_one] using h
  have hle := (initSparseCoreDepth_le_iff m 2).2 hup
  have hn : ¬ Expander.chosenL m ≤ 1 := fun h =>
    hdown.not_ge ((initSparseCoreDepth_le_iff m 1).1 h)
  omega

/-- Every padded edge count in Algorithm 1 admits an enclosure that
certifies its chain depth. -/
theorem initRuntimeChainDepth_exists_accuracy {M : ℕ} (hM : 1 ≤ M) :
    let depth := (concreteChainParams M hM).d
    ∃ accuracy : ℕ,
      (((depth - 1) ^ 48 : ℕ) : ℝ) + 2 / (2 : ℝ) ^ accuracy < Real.log ((M : ℝ) + 2) ∧
      Real.log ((M : ℝ) + 2) + 2 / (2 : ℝ) ^ accuracy ≤ ((depth ^ 48 : ℕ) : ℝ) := by
  let depth := chosenD (23 / 24) M
  have hd : 0 < depth := (chosenD_bounds (by norm_num : (23 : ℝ) / 24 < 1) hM).1
  have hlo : (((depth - 1) ^ 48 : ℕ) : ℝ) < Real.log ((M : ℝ) + 2) := by
    push_cast
    exact lt_of_not_ge (fun h => by
      have hle : depth ≤ depth - 1 := (minRatioDepth_le_iff M (depth - 1)).mpr h
      omega)
  have hhi : Real.log ((M : ℝ) + 2) ≤ ((depth ^ 48 : ℕ) : ℝ) := by
    exact_mod_cast (minRatioDepth_le_iff M depth).mp (le_refl depth)
  have hcast : ((M + 2 : ℕ) : ℝ) = ((M : ℕ) : ℝ) + 2 := by
    exact Nat.cast_add _ _
  obtain ⟨accuracy, hl, hu⟩ := initDepthThreshold_exists_accuracy
    (m := M + 2) (lower := (depth - 1) ^ 48) (upper := depth ^ 48)
    (by omega) (pow_pos hd _) (hcast.symm ▸ hlo) (hcast.symm ▸ hhi)
  rw [hcast] at hl hu
  exact ⟨accuracy, hl, hu⟩

/-- Every squared padded edge count in Theorem 8.2 admits an enclosure
that certifies its sparsifier depth. -/
theorem initRuntimeSparseCoreDepth_exists_accuracy (M : ℕ) :
    let depth := Expander.chosenL (M ^ 2)
    ∃ accuracy : ℕ,
      (((depth - 1) ^ 24 : ℕ) : ℝ) + 2 / (2 : ℝ) ^ accuracy < Real.log (((M ^ 2 : ℕ) : ℝ) + 2) ∧
      Real.log (((M ^ 2 : ℕ) : ℝ) + 2) + 2 / (2 : ℝ) ^ accuracy ≤ ((depth ^ 24 : ℕ) : ℝ) := by
  let depth := Expander.chosenL (M ^ 2)
  have hd : 0 < depth := Nat.zero_lt_of_lt (Expander.one_le_chosenL (M ^ 2))
  have hlo : (((depth - 1) ^ 24 : ℕ) : ℝ) < Real.log (((M ^ 2 : ℕ) : ℝ) + 2) := by
    push_cast
    exact lt_of_not_ge (fun h => by
      have hle : depth ≤ depth - 1 := (initSparseCoreDepth_le_iff (M ^ 2) (depth - 1)).mpr
        (by push_cast; exact h)
      omega)
  have hhi : Real.log (((M ^ 2 : ℕ) : ℝ) + 2) ≤ ((depth ^ 24 : ℕ) : ℝ) := by
    exact_mod_cast (initSparseCoreDepth_le_iff (M ^ 2) depth).mp (le_refl depth)
  have hcast : ((M ^ 2 + 2 : ℕ) : ℝ) = ((M ^ 2 : ℕ) : ℝ) + 2 := by
    exact Nat.cast_add _ _
  obtain ⟨accuracy, hl, hu⟩ := initDepthThreshold_exists_accuracy
    (m := M ^ 2 + 2) (lower := (depth - 1) ^ 24) (upper := depth ^ 24)
    (by omega) (pow_pos hd _) (hcast.symm ▸ hlo) (hcast.symm ▸ hhi)
  rw [hcast] at hl hu
  exact ⟨accuracy, hl, hu⟩

private theorem initRuntimeDepth_cutoff_bounds {m e depth : ℕ}
    (hm : 1 ≤ m)
    (hdepth : ∀ candidate : ℕ, depth ≤ candidate ↔
      Real.log ((m : ℝ) + 2) ≤ ((candidate ^ e : ℕ) : ℝ))
    : 1 < depth ∧ (((depth - 1) ^ e : ℕ) : ℝ) < Real.log ((m : ℝ) + 2) ∧
      depth ^ e ≤ 2 ^ e * (m + 2).size := by
  have h₁ : (1 : ℝ) < Real.log ((m : ℝ) + 2) := by
    have h := initDepthTwo_lowerGap (exponent := e) hm (error := 0) (by norm_num)
    simpa only [Nat.reduceSub, one_pow, Nat.cast_one, add_zero] using h
  have hd₂ : 1 < depth := by
    apply lt_of_not_ge
    intro h
    have hlog := (hdepth 1).mp h
    exact h₁.not_ge (by simpa only [one_pow, Nat.cast_one] using hlog)
  have hlo : (((depth - 1) ^ e : ℕ) : ℝ) < Real.log ((m : ℝ) + 2) := by
    apply lt_of_not_ge
    intro h
    have hle := (hdepth (depth - 1)).mpr h
    omega
  have hprev : (depth - 1) ^ e ≤ (m + 2).size := by
    exact_mod_cast (hlo.le.trans (initDepthLog_le_inputBits m))
  have hbound : depth ^ e ≤ 2 ^ e * (m + 2).size := by
    have hdouble : depth ≤ 2 * (depth - 1) := by omega
    calc
      depth ^ e ≤ (2 * (depth - 1)) ^ e := Nat.pow_le_pow_left hdouble _
      _ = 2 ^ e * (depth - 1) ^ e := mul_pow _ _ _
      _ ≤ _ := Nat.mul_le_mul_left _ hprev
  exact ⟨hd₂, hlo, hbound⟩

/-- The chain cutoff fits an unscaled word once the bit-length bound fits. -/
theorem initRuntimeChainDepth_cutoff_le {M : ℕ} (hM : 1 ≤ M) :
    (concreteChainParams M hM).d ^ 48 ≤ 2 ^ 48 * (M + 2).size :=
  (initRuntimeDepth_cutoff_bounds (depth := (concreteChainParams M hM).d) hM
    (fun j => by exact_mod_cast minRatioDepth_le_iff M j)).2.2

/-- The sparsifier cutoff fits an unscaled word once the bit-length bound fits. -/
theorem initRuntimeSparseCoreDepth_cutoff_le {M : ℕ} (hM : 1 ≤ M) :
    Expander.chosenL (M ^ 2) ^ 24 ≤ 2 ^ 24 * (M ^ 2 + 2).size :=
  (initRuntimeDepth_cutoff_bounds (depth := Expander.chosenL (M ^ 2))
    (Nat.one_le_pow _ _ hM) (fun j => by exact_mod_cast initSparseCoreDepth_le_iff (M ^ 2) j)).2.2

private theorem initRuntimeDepth_gaps_of_polylog_accuracy {m e depth accuracy : ℕ}
    (hm : 1 ≤ m)
    (hdepth : ∀ candidate : ℕ, depth ≤ candidate ↔
      Real.log ((m : ℝ) + 2) ≤ ((candidate ^ e : ℕ) : ℝ))
    (hacc : 38 * (2 ^ e * (m + 2).size) ^ 8 + (m + 2).size ≤ accuracy) :
    (((depth - 1) ^ e : ℕ) : ℝ) + 2 / (2 : ℝ) ^ accuracy < Real.log ((m : ℝ) + 2) ∧
    Real.log ((m : ℝ) + 2) + 2 / (2 : ℝ) ^ accuracy ≤ ((depth ^ e : ℕ) : ℝ) := by
  obtain ⟨hd₂, hlo, hbound⟩ := initRuntimeDepth_cutoff_bounds hm hdepth
  have hhi := (hdepth depth).mp le_rfl
  have hcast : ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 2 := Nat.cast_add _ _
  have h := initDepthThreshold_gaps_of_cutoff_bound (m := m + 2)
    (lower := (depth - 1) ^ e) (upper := depth ^ e) (bound := 2 ^ e * (m + 2).size)
    (by omega) (pow_pos (by omega) _) (Nat.pow_le_pow_left (Nat.sub_le _ _) _)
    hbound (hcast.symm ▸ hlo) (hcast.symm ▸ hhi) hacc
  rwa [hcast] at h

/-- A polynomial in the padded edge count's bit length suffices for
both chain depth comparisons in Algorithm 1. -/
theorem initRuntimeChainDepth_gaps_of_polylog_accuracy {M accuracy : ℕ} (hM : 1 ≤ M)
    (hacc : 38 * (2 ^ 48 * (M + 2).size) ^ 8 + (M + 2).size ≤ accuracy) :
    let depth := (concreteChainParams M hM).d
    (((depth - 1) ^ 48 : ℕ) : ℝ) + 2 / (2 : ℝ) ^ accuracy < Real.log ((M : ℝ) + 2) ∧
    Real.log ((M : ℝ) + 2) + 2 / (2 : ℝ) ^ accuracy ≤ ((depth ^ 48 : ℕ) : ℝ) := by
  apply initRuntimeDepth_gaps_of_polylog_accuracy (depth := (concreteChainParams M hM).d) hM
    (fun j => by exact_mod_cast minRatioDepth_le_iff M j) hacc

/-- A polynomial in the squared padded edge count's bit length suffices
for both sparsifier depth comparisons in Theorem 8.2. -/
theorem initRuntimeSparseCoreDepth_gaps_of_polylog_accuracy {M accuracy : ℕ} (hM : 1 ≤ M)
    (hacc : 38 * (2 ^ 24 * (M ^ 2 + 2).size) ^ 8 + (M ^ 2 + 2).size ≤ accuracy) :
    let depth := Expander.chosenL (M ^ 2)
    (((depth - 1) ^ 24 : ℕ) : ℝ) + 2 / (2 : ℝ) ^ accuracy < Real.log (((M ^ 2 : ℕ) : ℝ) + 2) ∧
    Real.log (((M ^ 2 : ℕ) : ℝ) + 2) + 2 / (2 : ℝ) ^ accuracy ≤ ((depth ^ 24 : ℕ) : ℝ) := by
  apply initRuntimeDepth_gaps_of_polylog_accuracy (depth := Expander.chosenL (M ^ 2))
    (Nat.one_le_pow _ _ hM)
    (fun j => by exact_mod_cast initSparseCoreDepth_le_iff (M ^ 2) j) hacc

/-- The logarithm accuracy suffices for chain selection when the padded
edge count lies in the depth-two range. -/
theorem initRuntimeChainDepth_gaps_of_inputBits {M accuracy : ℕ}
    (hM : 1 ≤ M) (hbits : (M + 2).size < 2 ^ 48) (hacc : 5 ≤ accuracy) :
    let depth := (concreteChainParams M hM).d
    let error := 2 / (2 : ℝ) ^ accuracy
    (((depth - 1) ^ 48 : ℕ) : ℝ) + error < Real.log ((M : ℝ) + 2) ∧
      Real.log ((M : ℝ) + 2) + error ≤ ((depth ^ 48 : ℕ) : ℝ) := by
  dsimp only
  have hd : (concreteChainParams M hM).d = 2 := initChainDepth_eq_two_of_inputBits hM hbits
  rw [hd]
  exact initDepthTwo_gaps_of_accuracy hM hbits hacc

/-- The logarithm accuracy suffices for sparsifier selection when the squared
padded edge count lies in the depth-two range. -/
theorem initRuntimeSparseCoreDepth_gaps_of_inputBits {M accuracy : ℕ}
    (hM : 1 ≤ M) (hbits : (M ^ 2 + 2).size < 2 ^ 24) (hacc : 5 ≤ accuracy) :
    let depth := Expander.chosenL (M ^ 2)
    let error := 2 / (2 : ℝ) ^ accuracy
    (((depth - 1) ^ 24 : ℕ) : ℝ) + error < Real.log (((M ^ 2 : ℕ) : ℝ) + 2) ∧
      Real.log (((M ^ 2 : ℕ) : ℝ) + 2) + error ≤ ((depth ^ 24 : ℕ) : ℝ) := by
  dsimp only
  have hsq : 1 ≤ M ^ 2 := Nat.one_le_pow _ _ hM
  rw [initSparseCoreDepth_eq_two_of_inputBits hsq hbits]
  exact initDepthTwo_gaps_of_accuracy hsq hbits hacc

/-- Search the sparsifier depth and store it when both bounds certify it. -/
@[expose] def selectInitSparseCoreDepth (retry : Stmt) : Stmt :=
  searchInitDepth 24 ;; stageInitDepthPowers 24 ;; checkInitDepthBounds ;;
  .cond (.reg 109) (.assign 44 (.reg 110)) retry

private theorem selectInitSparseCoreDepth_of_order_runs {w m lo hi scale : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {retry : Stmt}
    (hloReg : st.regs 107 = lo) (hhiReg : st.regs 108 = hi) (hsReg : st.regs 111 = scale)
    (hsPos : 0 < scale) (hw : 1 < 2 ^ w)
    (hord : lo ≤ hi) :
    let depth := Expander.chosenL m
    0 < depth → depth < 2 ^ w → depth ^ 24 * scale < 2 ^ w →
    (depth - 1) ^ 24 * scale < lo → hi ≤ depth ^ 24 * scale →
    ∃ out, Runs w p ω (selectInitSparseCoreDepth retry) st .normal out (166 * (depth - 1) + 180) ∧
      out.regs 44 = depth ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 44 → r ≠ 105 → r ≠ 106 → r ≠ 109 → r ≠ 110 → out.regs r = st.regs r) := by
  dsimp only
  intro hpos hword hfit hprev hnext
  obtain ⟨mid, hr₁, hd, hm₁, hl, hscale, hk₁⟩ :=
    searchInitDepth_runs (exponent := 24) (p := p) (ω := ω) hloReg hsReg hpos hword hw
      hsPos hfit hprev (hord.trans hnext)
  obtain ⟨powers, hr₂, hp, hn, hm₂, hk₂⟩ :=
    stageInitDepthPowers_runs (p := p) (ω := ω) hd hscale hword hsPos hw hfit
  obtain ⟨checked, hr₃, hflag, hm₃, hk₃⟩ :=
    checkInitDepthBounds_runs (ω := ω) hp hn ((hk₂ 107 (by decide) (by decide)).trans hl)
      ((hk₂ 108 (by decide) (by decide)).trans ((hk₁ 108 (by decide) (by decide) (by decide)).trans hhiReg)) hw
  have hpass : checked.regs 109 = 1 := by simp [hflag, hprev, hnext]
  have hcandidate := (hk₃ 110 (by decide)).trans ((hk₂ 110 (by decide) (by decide)).trans hd)
  let out := {checked with regs := Function.update checked.regs 44 (Expander.chosenL m)}
  have ha : Runs w p ω (.assign 44 (.reg 110)) checked .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hcandidate], rfl, rfl, rfl⟩
  have hr₄ : Runs w p ω (.cond (.reg 109) (.assign 44 (.reg 110)) retry) checked .normal out 4 :=
    runs_cond_iff.mpr ⟨1, 2, by simp [Expr.eval, hpass], ha, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, _, 169, hr₁,
    runs_seq_iff.mpr (Or.inr ⟨powers, 153, 15, hr₂,
      runs_seq_iff.mpr (Or.inr ⟨checked, 10, 4, hr₃, hr₄, rfl⟩), rfl⟩), by omega⟩),
    by simp [out], hm₃.trans (hm₂.trans hm₁),
    fun r h44 h105 h106 h109 h110 => by
      have hreg := (hk₃ r h109).trans ((hk₂ r h105 h106).trans (hk₁ r h105 h106 h110))
      simpa [out, h44] using hreg⟩

/-- A separating logarithm enclosure installs the exact sparsifier depth. -/
theorem selectInitSparseCoreDepth_runs {w m lo hi scale : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {retry : Stmt}
    (hloReg : st.regs 107 = lo) (hhiReg : st.regs 108 = hi) (hsReg : st.regs 111 = scale)
    (hsPos : 0 < scale) (hw : 1 < 2 ^ w)
    (hlo : (lo : ℝ) / scale ≤ Real.log ((m : ℝ) + 2))
    (hhi : Real.log ((m : ℝ) + 2) ≤ (hi : ℝ) / scale) :
    let depth := Expander.chosenL m
    0 < depth → depth < 2 ^ w → depth ^ 24 * scale < 2 ^ w →
    (depth - 1) ^ 24 * scale < lo → hi ≤ depth ^ 24 * scale →
    ∃ out, Runs w p ω (selectInitSparseCoreDepth retry) st .normal out (166 * (depth - 1) + 180) ∧
      out.regs 44 = depth ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 44 → r ≠ 105 → r ≠ 106 → r ≠ 109 → r ≠ 110 → out.regs r = st.regs r) := by
  have hs : (0 : ℝ) < scale := by exact_mod_cast hsPos
  have hord : lo ≤ hi := by
    exact_mod_cast (div_le_div_iff_of_pos_right hs).mp (hlo.trans hhi)
  exact selectInitSparseCoreDepth_of_order_runs hloReg hhiReg hsReg hsPos hw hord

/-- Rounded endpoints permit sparsifier depth selection with unit scale
even when the original logarithm scale spans many words. -/
theorem selectInitSparseCoreDepth_rounded_runs {w m lo hi scale : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {retry : Stmt}
    (hl : st.regs 107 = lo / scale + (if lo % scale = 0 then 0 else 1))
    (hh : st.regs 108 = hi / scale + (if hi % scale = 0 then 0 else 1))
    (hs : st.regs 111 = 1) (hsPos : 0 < scale) (hw : 1 < 2 ^ w) (horder : lo ≤ hi) :
    let depth := Expander.chosenL m
    0 < depth → depth < 2 ^ w → depth ^ 24 < 2 ^ w →
    (depth - 1) ^ 24 * scale < lo → hi ≤ depth ^ 24 * scale →
    ∃ out, Runs w p ω (selectInitSparseCoreDepth retry) st .normal out (166 * (depth - 1) + 180) ∧
      out.regs 44 = depth ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 44 → r ≠ 105 → r ≠ 106 → r ≠ 109 → r ≠ 110 → out.regs r = st.regs r) := by
  dsimp only
  intro hp hw' hf hprev hnext
  have hround : lo / scale + (if lo % scale = 0 then 0 else 1) ≤
      hi / scale + (if hi % scale = 0 then 0 else 1) :=
    (initDepth_endpoint_le_iff hsPos).mpr
      (horder.trans ((initDepth_endpoint_le_iff hsPos).mp le_rfl))
  have hbefore : (Expander.chosenL m - 1) ^ 24 < lo / scale + (if lo % scale = 0 then 0 else 1) :=
    Nat.lt_of_not_ge fun h => hprev.not_ge ((initDepth_endpoint_le_iff hsPos).mp h)
  have hafter := (initDepth_endpoint_le_iff hsPos).mpr hnext
  refine selectInitSparseCoreDepth_of_order_runs hl hh hs (by decide) hw hround hp hw' ?_ ?_ ?_
  · simpa only [mul_one] using hf
  · simpa only [mul_one] using hbefore
  · simpa only [mul_one] using hafter

/-- Compute the depth logarithm for the squared edge bound in
register 23, restore the workspace cursor and select the sparsifier depth. -/
@[expose] def initRuntimeSparseCoreDepth (bits load log pack : ℕ) (retry : Stmt) : Stmt :=
  computeInitDepthLog 23 bits load log pack ;; finishInitChainDepthLog ;;
  selectInitSparseCoreDepth retry

/-- The squared-size logarithm and the certified sparsifier depth
selection run in sequence with the supplied workspace handoff. -/
theorem initRuntimeSparseCoreDepth_runs {w bits load log pack logCost depthCost : ℕ}
    {p : Program} {ω : ℕ → Bool} {st logged ready out : State} {retry : Stmt}
    (hl : Runs w p ω (computeInitDepthLog 23 bits load log pack) st .normal logged logCost)
    (hr : Runs w p ω finishInitChainDepthLog logged .normal ready 8)
    (hd : Runs w p ω (selectInitSparseCoreDepth retry) ready .normal out depthCost) :
    Runs w p ω (initRuntimeSparseCoreDepth bits load log pack retry) st .normal out
      (logCost + depthCost + 10) :=
  runs_seq_iff.mpr (Or.inr ⟨logged, logCost, 8 + depthCost + 1, hl,
    runs_seq_iff.mpr (Or.inr ⟨ready, 8, depthCost, hr, hd, rfl⟩), by omega⟩)

/-- A certified squared-size enclosure gives the runtime depth while
retaining the restored vertex count and the fresh heap cursor. -/
theorem initRuntimeSparseCoreDepth_certified_runs {w m n heap scale bits load log pack logCost : ℕ}
    {p : Program} {ω : ℕ → Bool} {st logged : State} {retry : Stmt}
    (hl : Runs w p ω (computeInitDepthLog 23 bits load log pack) st .normal logged logCost)
    (hv : logged.regs 57 = n) (hh : logged.regs 99 = heap) (hs : logged.regs 4 = scale)
    (hfree : ZeroFrom logged.mem heap) (hsPos : 0 < scale) (hw : 1 < 2 ^ w)
    (hlo : (logged.regs 107 : ℝ) / scale ≤ Real.log ((m : ℝ) + 2))
    (hhi : Real.log ((m : ℝ) + 2) ≤ (logged.regs 108 : ℝ) / scale) :
    let depth := Expander.chosenL m
    0 < depth → depth < 2 ^ w → depth ^ 24 * scale < 2 ^ w →
    (depth - 1) ^ 24 * scale < logged.regs 107 → logged.regs 108 ≤ depth ^ 24 * scale →
    ∃ out, Runs w p ω (initRuntimeSparseCoreDepth bits load log pack retry)
        st .normal out (logCost + 166 * (depth - 1) + 190) ∧
      out.regs 44 = depth ∧ out.regs 92 = n ∧ out.regs 98 = heap ∧ ZeroFrom out.mem heap ∧
      (∀ r, r ∉ ([44, 92, 98, 105, 106, 109, 110, 111] : List ℕ) →
        out.regs r = logged.regs r) := by
  dsimp only
  intro hpos hword hfit hprev hnext
  obtain ⟨ready, hr, hn, hheap, hscale, hm₁, hk₁⟩ :=
    finishInitChainDepthLog_runs (w := w) (p := p) (ω := ω) hv hh hs
  obtain ⟨out, hd, hdepth, hm₂, hk₂⟩ :=
    selectInitSparseCoreDepth_runs (ω := ω) (retry := retry)
      (hk₁ 107 (by decide) (by decide) (by decide))
      (hk₁ 108 (by decide) (by decide) (by decide))
      hscale hsPos hw hlo hhi hpos hword hfit hprev hnext
  refine ⟨out, ?_, hdepth,
    (hk₂ 92 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hn,
    (hk₂ 98 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hheap,
    (hm₂.trans hm₁).symm ▸ hfree, ?_⟩
  · convert initRuntimeSparseCoreDepth_runs hl hr hd using 1
  · intro r hreg
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hreg
    obtain ⟨h44, h92, h98, h105, h106, h109, h110, h111⟩ := hreg
    exact (hk₂ r h44 h105 h106 h109 h110).trans (hk₁ r h92 h98 h111)

/-- Select the chain dimensions from a logarithm stored at the end of
the current workspace. -/
@[expose] def selectInitChainFromLogBlock (roundEntry h branch : ℕ) (retry : Stmt) : Stmt :=
  initRoundDepthLog roundEntry h ;; selectInitChainDimensions branch 22 retry

/-- Rounding a certified logarithm block and selecting the chain
dimensions takes linear time in the block width plus the scan cost. -/
theorem selectInitChainFromLogBlock_runs {w h roundEntry branch M L P heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {retry : Stmt} {error : ℝ}
    (hround : MeetsContract w p roundEntry (initDepthEndpointContract w h))
    (hbranch : MeetsContract w p branch (minRatioBranchCountContract w))
    (hw : 2 < 2 ^ w) (hhw : h < 2 ^ w) (hm : st.regs 22 = M) (hM : 1 ≤ M)
    (hMw : M < 2 ^ w)
    (hL : st.regs 67 = L) (hP : st.regs 68 = P) (hheap : st.regs 99 = heap)
    (hfit : heap < 2 ^ w) (hPfit : P < 2 ^ w) (hlen : L ≤ heap) (hfrac : P / h ≤ L)
    (hv : Num.Valid st.mem (heap - L) h L) (halign : h ∣ P)
    (happrox : |Num.fixVal st.mem (heap - L) h L P - Real.log ((M : ℝ) + 2)| ≤ error) :
    let C := concreteChainParams M hM
    (((C.d - 1) ^ 48 : ℕ) : ℝ) + error < Real.log ((M : ℝ) + 2) →
    Real.log ((M : ℝ) + 2) + error ≤ ((C.d ^ 48 : ℕ) : ℝ) →
    C.d ^ 48 + 1 < 2 ^ w →
    ∃ out cost, Runs w p ω (selectInitChainFromLogBlock roundEntry h branch retry) st .normal out cost ∧
      out.regs 75 = C.d ∧ out.regs 76 = C.k ∧ out.mem = st.mem ∧
      (∀ r, r ∉ ([75, 76, 105, 106, 107, 108, 109, 110, 111] : List ℕ) → out.regs r = st.regs r) ∧
      cost ≤ 25 * L + (19 * C.d + 32) * M.size + 310 * (C.d - 1) + 413 := by
  dsimp only
  intro hlo hhi hcut
  have hd : 0 < (concreteChainParams M hM).d :=
    (chosenD_bounds (by norm_num : (23 : ℝ) / 24 < 1) hM).1
  have hpow : (concreteChainParams M hM).d ^ 48 < 2 ^ w := by omega
  have hdw := (Nat.le_self_pow (by decide : 48 ≠ 0) _).trans_lt hpow
  obtain ⟨mid, c₁, hr₁, hl, hu, hord, hs, hm₁, hf₁, hc₁⟩ :=
    initRoundDepthLog_certified_runs hround (by omega) hhw hL hP hheap hfit hPfit hlen hfrac
      hv halign happrox hlo hhi hcut
  obtain ⟨out, c₂, hr₂, hd', hk, hm₂, hf₂, hc₂⟩ :=
    selectInitChainDimensions_of_order_runs (depth := (concreteChainParams M hM).d) (ω := ω) (retry := retry)
      hbranch hs rfl rfl ((hf₁ 22 (by decide) (by decide) (by decide)).trans hm)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      rfl hd hM (by decide) hw hMw hdw (by simpa only [mul_one] using hpow)
      hord.le (by simpa only [mul_one] using hl) (by simpa only [mul_one] using hu)
  refine ⟨out, c₁ + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c₁, c₂, hr₁, hr₂, rfl⟩),
    hd', hk, hm₂.trans hm₁, ?_, by omega⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h75, h76, h105, h106, h107, h108, h109, h110, h111⟩ := hr
  exact (hf₂ r h75 h76 h105 h106 h109 h110).trans (hf₁ r h107 h108 h111)

/-- Select the sparsifier depth from a logarithm stored at the end of
the current workspace. -/
@[expose] def selectInitSparseCoreFromLogBlock (roundEntry h : ℕ) (retry : Stmt) : Stmt :=
  initRoundDepthLog roundEntry h ;; selectInitSparseCoreDepth retry

/-- The sparsifier selector needs only unscaled cutoff powers in its
registers. The precision of the logarithm affects the rounding cost. -/
theorem selectInitSparseCoreFromLogBlock_runs {w h roundEntry m L P heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {retry : Stmt} {error : ℝ}
    (hround : MeetsContract w p roundEntry (initDepthEndpointContract w h))
    (hw : 1 < 2 ^ w) (hhw : h < 2 ^ w)
    (hL : st.regs 67 = L) (hP : st.regs 68 = P) (hheap : st.regs 99 = heap)
    (hfit : heap < 2 ^ w) (hPfit : P < 2 ^ w) (hlen : L ≤ heap) (hfrac : P / h ≤ L)
    (hv : Num.Valid st.mem (heap - L) h L) (halign : h ∣ P)
    (happrox : |Num.fixVal st.mem (heap - L) h L P - Real.log ((m : ℝ) + 2)| ≤ error) :
    let depth := Expander.chosenL m
    (((depth - 1) ^ 24 : ℕ) : ℝ) + error < Real.log ((m : ℝ) + 2) →
    Real.log ((m : ℝ) + 2) + error ≤ ((depth ^ 24 : ℕ) : ℝ) →
    depth ^ 24 + 1 < 2 ^ w →
    ∃ out cost, Runs w p ω (selectInitSparseCoreFromLogBlock roundEntry h retry) st .normal out cost ∧
      out.regs 44 = depth ∧ out.mem = st.mem ∧
      (∀ r, r ∉ ([44, 105, 106, 107, 108, 109, 110, 111] : List ℕ) → out.regs r = st.regs r) ∧
      cost ≤ 25 * L + 166 * (depth - 1) + 246 := by
  dsimp only
  intro hlo hhi hcut
  have hpos := Nat.zero_lt_of_lt (Expander.one_le_chosenL m)
  have hpow : Expander.chosenL m ^ 24 < 2 ^ w := by omega
  have hword := (Nat.le_self_pow (by decide : 24 ≠ 0) _).trans_lt hpow
  obtain ⟨mid, c, hr, hl, hu, hord, hs, hm, hf, hc⟩ :=
    initRoundDepthLog_certified_runs hround hw hhw hL hP hheap hfit hPfit hlen hfrac
      hv halign happrox hlo hhi hcut
  obtain ⟨out, hsparse, hd, hm', hf'⟩ :=
    selectInitSparseCoreDepth_of_order_runs (m := m) (ω := ω) (retry := retry)
      rfl rfl hs (by decide) hw hord.le hpos hword
      (by simpa only [mul_one] using hpow)
      (by simpa only [mul_one] using hl) (by simpa only [mul_one] using hu)
  refine ⟨out, _, runs_seq_iff.mpr (Or.inr ⟨mid, c, _, hr, hsparse, rfl⟩),
    hd, hm'.trans hm, ?_, by omega⟩
  intro r hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
  obtain ⟨h44, h105, h106, h107, h108, h109, h110, h111⟩ := hr'
  exact (hf' r h44 h105 h106 h109 h110).trans (hf r h107 h108 h111)

/-- The chain depth and branching scans fit a quadratic bound in the
padded input's bit length. The constant includes the bucket handoff. -/
theorem initRuntimeChainDepth_scanCost_le {M : ℕ} (hM : 1 ≤ M) :
    let depth := (concreteChainParams M hM).d
    (19 * depth + 32) * M.size + 310 * (depth - 1) + 554 ≤ 915 * (M + 2).size ^ 2 := by
  dsimp only
  let E := (M + 2).size
  have hE : 1 ≤ E := Nat.lt_size.mpr (by norm_num)
  have hd : (concreteChainParams M hM).d ≤ E :=
    initDepth_le_inputBits M ((1 - (23 / 24 : ℝ)) / 2) (by norm_num) (by norm_num)
  have hm : M.size ≤ E := Nat.size_le_size (by omega)
  have hlin : E ≤ E ^ 2 := Nat.le_self_pow (by decide) _
  have hone : 1 ≤ E ^ 2 := hE.trans hlin
  calc
    _ ≤ (19 * E + 32) * E + 310 * E + 554 := by
      exact Nat.add_le_add_right (Nat.add_le_add
        (Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left _ hd) _) hm)
        (Nat.mul_le_mul_left _ ((Nat.sub_le _ _).trans hd))) _
    _ = 19 * E ^ 2 + 342 * E + 554 := by ring
    _ ≤ 915 * E ^ 2 := by omega

/-- The sparsifier scan and bucket guard cost at most a linear function
of the squared input's bit length. -/
theorem initRuntimeSparseCoreDepth_scanCost_le (M : ℕ) :
    166 * (Expander.chosenL (M ^ 2) - 1) + 375 ≤ 541 * (M ^ 2 + 2).size := by
  have hd : Expander.chosenL (M ^ 2) ≤ (M ^ 2 + 2).size :=
    initDepth_le_inputBits (M ^ 2) (1 / 24 : ℝ) (by norm_num) (by norm_num)
  have hE : 1 ≤ (M ^ 2 + 2).size := Nat.lt_size.mpr (by norm_num)
  omega

/-- The workspace precision bound also covers an unscaled cutoff and its
rounding carry. -/
theorem initRuntimeDepth_cutoff_word {w h e E cutoff : ℕ}
    (hh : 0 < h) (hcut : cutoff ≤ 2 ^ e * E)
    (hword : 2 * (h * (38 * (2 ^ e * E) ^ 8 + E + E + 10)) + 9 < 2 ^ w) :
    cutoff + 1 < 2 ^ w := by
  have hb : 2 ^ e * E ≤ (2 ^ e * E) ^ 8 := Nat.le_self_pow (by decide) _
  have hp : 38 * (2 ^ e * E) ^ 8 + E + E + 10 ≤
      h * (38 * (2 ^ e * E) ^ 8 + E + E + 10) := by
    exact Nat.le_mul_of_pos_left _ hh
  omega

/-- Compute the multiword logarithm and select the chain dimensions. -/
@[expose] def initMultiwordChainDimensions (bits load log roundEntry h branch : ℕ)
    (retry : Stmt) : Stmt :=
  computeInitDepthLogFromSize 22 bits load log h ;;
  selectInitChainFromLogBlock roundEntry h branch retry

/-- The multiword logarithm and chain selector preserve the memory frame
and return the model dimensions at the stated precision. -/
theorem initMultiwordChainDimensions_runs {w h bits load log roundEntry branch a L P q M : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {retry : Stmt}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hlog : MeetsContract w p log (Num.logarithmContract w h q))
    (hround : MeetsContract w p roundEntry (initDepthEndpointContract w h))
    (hbranch : MeetsContract w p branch (minRatioBranchCountContract w))
    (hm : st.regs 22 = M) (hM : 1 ≤ M) (hMw : M + 2 < 2 ^ w)
    (hhw : h < 2 ^ w) (hL : st.regs 67 = L) (hP : st.regs 68 = P)
    (ha : st.regs 98 = a) (hPword : P < 2 ^ w)
    (hroom : a + L + L + Num.logarithmSpace L P (M + 2).size < 2 ^ w)
    (hfrac : P / h ≤ L) (halign : h ∣ P) (hz : ZeroFrom st.mem a)
    (hvalue : M + 2 < Num.capacity h (L - P / h))
    (hfit : 2 * ((M + 2) * Num.capacity h (P / h)) < Num.capacity h L)
    (hacc : q + (M + 2).size + 10 ≤ P) (hcap : P + (M + 2).size + 4 ≤ h * L)
    (hprec : 2 * P + 9 < 2 ^ w)
    (hq : 38 * (2 ^ 48 * (M + 2).size) ^ 8 + (M + 2).size ≤ q) :
    let C := concreteChainParams M hM
    C.d ^ 48 + 1 < 2 ^ w →
    ∃ out cost ret, Runs w p ω (initMultiwordChainDimensions bits load log roundEntry h branch retry)
        st .normal out cost ∧ out.regs 75 = C.d ∧ out.regs 76 = C.k ∧ out.regs 99 = ret ∧
      a + L + L ≤ ret ∧ ret < 2 ^ w ∧
      (∀ x < a, out.mem x = st.mem x) ∧ ZeroFrom out.mem ret ∧
      (∀ r < 99, r ≠ 75 → r ≠ 76 → out.regs r = st.regs r) ∧
      cost ≤ 71 * L + Num.logarithmCost L P (M + 2).size + 14 * (M + 2).size +
        (19 * C.d + 32) * M.size + 310 * (C.d - 1) + 476 := by
  dsimp only
  intro hcut
  obtain ⟨mid, c, ret, hr, h99, hlo, hhi, hv, happ, hf, hz', hk, hc⟩ :=
    computeInitDepthLogFromSize_runs hbits hload hlog hm hMw hhw hL hP ha hPword
      hroom hfrac halign hz hvalue hfit hacc hcap hprec
  obtain ⟨hl, hu⟩ := initRuntimeChainDepth_gaps_of_polylog_accuracy hM hq
  have herr : (1 : ℝ) / 2 ^ q ≤ 2 / 2 ^ q :=
    div_le_div_of_nonneg_right (by norm_num) (by positivity)
  obtain ⟨out, d, hr', hd, hbranches, hmem, hk', hc'⟩ :=
    selectInitChainFromLogBlock_runs hround hbranch (by omega) hhw
      ((hk 22 (by decide)).trans hm) hM (by omega)
      ((hk 67 (by decide)).trans hL) ((hk 68 (by decide)).trans hP)
      h99 hhi hPword (by omega) hfrac hv halign (happ.trans herr) hl hu hcut
  refine ⟨out, c + d + 1, ret, runs_seq_iff.mpr (Or.inr ⟨mid, c, d, hr, hr', rfl⟩),
    hd, hbranches, (hk' 99 (by decide)).trans h99, hlo, hhi,
    fun x hx => (congrFun hmem x).trans (hf x hx), hmem.symm ▸ hz', ?_, by omega⟩
  intro r hlt h75 h76
  exact (hk' r (by simp; omega)).trans (hk r hlt)

/-- Compute the multiword logarithm of the squared padded edge count and
select the sparsifier depth. -/
@[expose] def initMultiwordSparseCoreDepth (bits load log roundEntry h : ℕ) (retry : Stmt) : Stmt :=
  computeInitDepthLogFromSize 23 bits load log h ;;
  selectInitSparseCoreFromLogBlock roundEntry h retry

/-- At the certified precision, the sparsifier depth follows from the
multiword logarithm without packing its scale into a word. -/
theorem initMultiwordSparseCoreDepth_runs {w h bits load log roundEntry a L P q M : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {retry : Stmt}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hlog : MeetsContract w p log (Num.logarithmContract w h q))
    (hround : MeetsContract w p roundEntry (initDepthEndpointContract w h))
    (hm : st.regs 23 = M ^ 2) (hM : 1 ≤ M) (hMw : M ^ 2 + 2 < 2 ^ w)
    (hhw : h < 2 ^ w) (hL : st.regs 67 = L) (hP : st.regs 68 = P)
    (ha : st.regs 98 = a) (hPword : P < 2 ^ w)
    (hroom : a + L + L + Num.logarithmSpace L P (M ^ 2 + 2).size < 2 ^ w)
    (hfrac : P / h ≤ L) (halign : h ∣ P) (hz : ZeroFrom st.mem a)
    (hvalue : M ^ 2 + 2 < Num.capacity h (L - P / h))
    (hfit : 2 * ((M ^ 2 + 2) * Num.capacity h (P / h)) < Num.capacity h L)
    (hacc : q + (M ^ 2 + 2).size + 10 ≤ P) (hcap : P + (M ^ 2 + 2).size + 4 ≤ h * L)
    (hprec : 2 * P + 9 < 2 ^ w)
    (hq : 38 * (2 ^ 24 * (M ^ 2 + 2).size) ^ 8 + (M ^ 2 + 2).size ≤ q) :
    let depth := Expander.chosenL (M ^ 2)
    depth ^ 24 + 1 < 2 ^ w →
    ∃ out cost ret, Runs w p ω (initMultiwordSparseCoreDepth bits load log roundEntry h retry)
        st .normal out cost ∧ out.regs 44 = depth ∧ out.regs 99 = ret ∧
      a + L + L ≤ ret ∧ ret < 2 ^ w ∧
      (∀ x < a, out.mem x = st.mem x) ∧ ZeroFrom out.mem ret ∧
      (∀ r < 99, r ≠ 44 → out.regs r = st.regs r) ∧
      cost ≤ 71 * L + Num.logarithmCost L P (M ^ 2 + 2).size + 14 * (M ^ 2 + 2).size +
        166 * (depth - 1) + 309 := by
  dsimp only
  intro hcut
  obtain ⟨mid, c, ret, hr, h99, hlo, hhi, hv, happ, hf, hz', hk, hc⟩ :=
    computeInitDepthLogFromSize_runs hbits hload hlog hm hMw hhw hL hP ha hPword
      hroom hfrac halign hz hvalue hfit hacc hcap hprec
  obtain ⟨hl, hu⟩ := initRuntimeSparseCoreDepth_gaps_of_polylog_accuracy hM hq
  have herr : (1 : ℝ) / 2 ^ q ≤ 2 / 2 ^ q :=
    div_le_div_of_nonneg_right (by norm_num) (by positivity)
  obtain ⟨out, d, hr', hd, hmem, hk', hc'⟩ :=
    selectInitSparseCoreFromLogBlock_runs (m := M ^ 2) hround (by omega) hhw
      ((hk 67 (by decide)).trans hL) ((hk 68 (by decide)).trans hP)
      h99 hhi hPword (by omega) hfrac hv halign (happ.trans herr) hl hu hcut
  refine ⟨out, c + d + 1, ret, runs_seq_iff.mpr (Or.inr ⟨mid, c, d, hr, hr', rfl⟩),
    hd, (hk' 99 (by decide)).trans h99, hlo, hhi,
    fun x hx => (congrFun hmem x).trans (hf x hx), hmem.symm ▸ hz', ?_, by omega⟩
  intro r hlt h44
  exact (hk' r (by simp; omega)).trans (hk r hlt)

/-- Compute the multiword logarithm and select the chain dimensions. -/
@[expose] def initRuntimeWorkspaceChainDimensions (bits load log roundEntry h branch : ℕ)
    (retry : Stmt) : Stmt :=
  computeInitDepthLogRuntime 22 bits load log 48 h ;;
  selectInitChainFromLogBlock roundEntry h branch retry

/-- The multiword logarithm and chain selector preserve the memory frame
and return the model dimensions at the stated precision. -/
theorem initRuntimeWorkspaceChainDimensions_runs {w h bits load log roundEntry branch a M : ℕ}
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
    let C := concreteChainParams M hM
    MeetsContract w p log (Num.logarithmContract w h q) →
    a + L + L + Num.logarithmSpace L P E < 2 ^ w → 2 * P + 9 < 2 ^ w →
    C.d ^ 48 + 1 < 2 ^ w →
    ∃ out cost ret, Runs w p ω (initRuntimeWorkspaceChainDimensions bits load log roundEntry h branch retry)
        st .normal out cost ∧ out.regs 75 = C.d ∧ out.regs 76 = C.k ∧ out.regs 99 = ret ∧
      a + L + L ≤ ret ∧ ret < 2 ^ w ∧ ret ≤ a + L + L + Num.logarithmSpace L P E ∧
      (∀ x < a, out.mem x = st.mem x) ∧ ZeroFrom out.mem ret ∧
      (∀ r < 99, r ≠ 67 → r ≠ 68 → r ≠ 75 → r ≠ 76 → out.regs r = st.regs r) ∧
      (∀ r, (101 ≤ r ∧ r ≤ 104) ∨ 128 ≤ r → out.regs r = st.regs r) ∧
      cost ≤ 71 * L + Num.logarithmCost L P (M + 2).size + 14 * (M + 2).size +
        (19 * C.d + 32) * M.size + 310 * (C.d - 1) + 515 := by
  dsimp only
  intro hlog hroom hprec hcut
  let E := (M + 2).size
  let q := 38 * (2 ^ 48 * E) ^ 8 + E
  let P := h * (q + E + 10)
  change 2 * P + 9 < 2 ^ w at hprec
  have hPword : P < 2 ^ w := by omega
  obtain ⟨halign, hfrac, _, _, _⟩ := initDepthLog_workspace_bounds (q := q) (E := E) hh
  obtain ⟨mid, c, ret, hr, h99, h67, h68, hlo, hhi, hroomRet, hv, happ, hf, hz', hk, hhigh, hc⟩ :=
    computeInitDepthLogRuntime_runs (exponent := 48) hbits hload hm hMw ha hh hhw hz hlog hroom hprec
  obtain ⟨hl, hu⟩ := initRuntimeChainDepth_gaps_of_polylog_accuracy (accuracy := q) hM le_rfl
  have herr : (1 : ℝ) / 2 ^ q ≤ 2 / 2 ^ q :=
    div_le_div_of_nonneg_right (by norm_num) (by positivity)
  obtain ⟨out, d, hr', hd, hbranches, hmem, hk', hc'⟩ :=
    selectInitChainFromLogBlock_runs hround hbranch (by omega) hhw
      ((hk 22 (by decide) (by decide) (by decide)).trans hm) hM (by omega)
      h67 h68
      h99 hhi hPword (by omega) hfrac hv halign (happ.trans herr) hl hu hcut
  refine ⟨out, c + d + 1, ret, runs_seq_iff.mpr (Or.inr ⟨mid, c, d, hr, hr', rfl⟩),
    hd, hbranches, (hk' 99 (by decide)).trans h99, hlo, hhi, hroomRet,
    fun x hx => (congrFun hmem x).trans (hf x hx), hmem.symm ▸ hz', ?_, ?_, by omega⟩
  · intro r hlt h67' h68' h75 h76
    exact (hk' r (by simp; omega)).trans (hk r hlt h67' h68')
  · intro r h
    exact (hk' r (by simp; omega)).trans (hhigh r h)

/-- Compute the multiword logarithm of the squared padded edge count and
select the sparsifier depth. -/
@[expose] def initRuntimeWorkspaceSparseCoreDepth (bits load log roundEntry h : ℕ) (retry : Stmt) : Stmt :=
  computeInitDepthLogRuntime 23 bits load log 24 h ;;
  selectInitSparseCoreFromLogBlock roundEntry h retry

/-- At the certified precision, the sparsifier depth follows from the
multiword logarithm without packing its scale into a word. -/
theorem initRuntimeWorkspaceSparseCoreDepth_runs {w h bits load log roundEntry a M : ℕ}
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
    ∃ out cost ret, Runs w p ω (initRuntimeWorkspaceSparseCoreDepth bits load log roundEntry h retry)
        st .normal out cost ∧ out.regs 44 = depth ∧ out.regs 99 = ret ∧
      a + L + L ≤ ret ∧ ret < 2 ^ w ∧ ret ≤ a + L + L + Num.logarithmSpace L P E ∧
      (∀ x < a, out.mem x = st.mem x) ∧ ZeroFrom out.mem ret ∧
      (∀ r < 99, r ≠ 67 → r ≠ 68 → r ≠ 44 → out.regs r = st.regs r) ∧
      (∀ r, (101 ≤ r ∧ r ≤ 104) ∨ 128 ≤ r → out.regs r = st.regs r) ∧
      cost ≤ 71 * L + Num.logarithmCost L P (M ^ 2 + 2).size + 14 * (M ^ 2 + 2).size +
        166 * (depth - 1) + 348 := by
  dsimp only
  intro hlog hroom hprec hcut
  let E := (M ^ 2 + 2).size
  let q := 38 * (2 ^ 24 * E) ^ 8 + E
  let P := h * (q + E + 10)
  change 2 * P + 9 < 2 ^ w at hprec
  have hPword : P < 2 ^ w := by omega
  obtain ⟨halign, hfrac, _, _, _⟩ := initDepthLog_workspace_bounds (q := q) (E := E) hh
  obtain ⟨mid, c, ret, hr, h99, h67, h68, hlo, hhi, hroomRet, hv, happ, hf, hz', hk, hhigh, hc⟩ :=
    computeInitDepthLogRuntime_runs (exponent := 24) hbits hload hm hMw ha hh hhw hz hlog hroom hprec
  obtain ⟨hl, hu⟩ := initRuntimeSparseCoreDepth_gaps_of_polylog_accuracy (accuracy := q) hM le_rfl
  have herr : (1 : ℝ) / 2 ^ q ≤ 2 / 2 ^ q :=
    div_le_div_of_nonneg_right (by norm_num) (by positivity)
  obtain ⟨out, d, hr', hd, hmem, hk', hc'⟩ :=
    selectInitSparseCoreFromLogBlock_runs (m := M ^ 2) hround (by omega) hhw
      h67 h68
      h99 hhi hPword (by omega) hfrac hv halign (happ.trans herr) hl hu hcut
  refine ⟨out, c + d + 1, ret, runs_seq_iff.mpr (Or.inr ⟨mid, c, d, hr, hr', rfl⟩),
    hd, (hk' 99 (by decide)).trans h99, hlo, hhi, hroomRet,
    fun x hx => (congrFun hmem x).trans (hf x hx), hmem.symm ▸ hz', ?_, ?_, by omega⟩
  · intro r hlt h67' h68' h44
    exact (hk' r (by simp; omega)).trans (hk r hlt h67' h68')
  · intro r h
    exact (hk' r (by simp; omega)).trans (hhigh r h)

end MinCostFlow.MinRatio
