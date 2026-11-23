module

public import MinCostFlow.MinRatio.InitBucketSigmaLog
public import MinCostFlow.MinRatio.InitIntegerBucket
public import MinCostFlow.MinRatio.InitStretchAssembly
public import MinCostFlow.MinRatio.InitParameterEntry

/-!
# Assembly of the checked bucket cap

Evaluate the schedule from the runtime logarithm bounds and certify the
ceiling that determines the concrete configuration's bucket count.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain SparseCore

/-- Set the concrete base edge bound to the maximum of the runtime edge
count and the fixed threshold from the witness. -/
@[expose] def initConcreteBucketBaseEdgeBound (threshold : ℕ) : Stmt :=
  .assign 22 (.bin .add (.const threshold) (.bin .sub (.reg 0) (.const threshold)))

/-- The maximum is evaluated exactly when both arguments fit a word. -/
theorem initConcreteBucketBaseEdgeBound_runs {w m threshold : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hm : st.regs 0 = m) (hmWord : m < 2 ^ w) (htWord : threshold < 2 ^ w) :
    ∃ out, Runs w p ω (initConcreteBucketBaseEdgeBound threshold) st .normal out 6 ∧
      out.regs 22 = max m threshold ∧ out.mem = st.mem ∧
      (∀ r ≠ 22, out.regs r = st.regs r) := by
  have hsub : m - threshold < 2 ^ w := (Nat.sub_le ..).trans_lt hmWord
  have hmax : max m threshold < 2 ^ w := max_lt hmWord htWord
  have he : threshold + (m - threshold) = max m threshold := by omega
  let out := {st with regs := Function.update st.regs 22 (max m threshold)}
  exact ⟨out, runs_assign_iff.mpr ⟨_, by
    simp [Expr.eval, BinOp.eval, hm, htWord, hsub, he, hmax], rfl, rfl, rfl⟩,
    by simp [out], rfl, fun r hr => by simp [out, hr]⟩

/-- Copy the computed potential bound and chain branching factor to
the working registers for bucket and threshold initialization. -/
@[expose] def prepareInitBucketParameters : Stmt :=
  .assign 20 (.reg 6) ;;
  .assign 38 (.reg 76) ;;
  .assign 1 (.reg 76)

/-- The bucket and threshold calculations receive the same runtime
branching factor. -/
theorem prepareInitBucketParameters_runs {w psi branch : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hpsi : st.regs 6 = psi) (hbranch : st.regs 76 = branch) :
    ∃ out, Runs w p ω prepareInitBucketParameters st .normal out 8 ∧
      out.regs 20 = psi ∧ out.regs 38 = branch ∧ out.regs 1 = branch ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 20 → r ≠ 38 → r ≠ 1 → out.regs r = st.regs r) := by
  let s₁ := {st with regs := Function.update st.regs 20 psi}
  let s₂ := {s₁ with regs := Function.update s₁.regs 38 branch}
  let out := {s₂ with regs := Function.update s₂.regs 1 branch}
  have hr₁ : Runs w p ω (.assign 20 (.reg 6)) st .normal s₁ 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hpsi], rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign 38 (.reg 76)) s₁ .normal s₂ 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s₁, hbranch], rfl, rfl, rfl⟩
  have hr₃ : Runs w p ω (.assign 1 (.reg 76)) s₂ .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s₂, s₁, hbranch], rfl, rfl, rfl⟩
  refine ⟨out, ?_, by simp [out, s₂, s₁], by simp [out, s₂], by simp [out], rfl, ?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨s₁, 2, 5, hr₁,
      runs_seq_iff.mpr (Or.inr ⟨s₂, 2, 2, hr₂, hr₃, rfl⟩), rfl⟩)
  · intro r h20 h38 h1
    simp [out, s₂, s₁, h20, h38, h1]

/-- Convert fixed rational bounds for the witness's MWU coefficient to
the runtime scale. Only the three witness constants are immediate words. -/
@[expose] def initBucketCoefficient (lower upper denominator : ℕ) : Stmt :=
  .assign 34 (.bin .div (.bin .mul (.const lower) (.reg 4)) (.const denominator)) ;;
  .assign 35 (.bin .div
    (.bin .add (.bin .mul (.const upper) (.reg 4)) (.bin .sub (.const denominator) (.const 1)))
    (.const denominator))

/-- Rounding the witness bounds outward provides the coefficient words
read by the bucket schedule. -/
theorem initBucketCoefficient_runs (C : ℝ)
    {w lower upper denominator scale : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hs : st.regs 4 = scale) (hsPos : 0 < scale) (hdPos : 0 < denominator)
    (hlo : (lower : ℝ) / denominator ≤ mwuK0 C)
    (hhi : mwuK0 C ≤ (upper : ℝ) / denominator)
    (hw : 1 < 2 ^ w) (hd : denominator < 2 ^ w)
    (hl : lower * scale < 2 ^ w) (hu : upper * scale + (denominator - 1) < 2 ^ w) :
    ∃ out, Runs w p ω (initBucketCoefficient lower upper denominator) st .normal out 17 ∧
      (out.regs 34 : ℝ) / scale ≤ mwuK0 C ∧ mwuK0 C ≤ (out.regs 35 : ℝ) / scale ∧
      out.regs 34 = lower * scale / denominator ∧
      out.regs 35 = (upper * scale + (denominator - 1)) / denominator ∧
      out.mem = st.mem ∧ (∀ r, r ≠ 34 → r ≠ 35 → out.regs r = st.regs r) := by
  let lo := lower * scale / denominator
  let hi := (upper * scale + (denominator - 1)) / denominator
  have hlw : lower < 2 ^ w := (Nat.le_mul_of_pos_right _ hsPos).trans_lt hl
  have hup : upper * scale < 2 ^ w := (Nat.le_add_right ..).trans_lt hu
  have huw : upper < 2 ^ w := (Nat.le_mul_of_pos_right _ hsPos).trans_lt hup
  have hloWord : lo < 2 ^ w := (Nat.div_le_self ..).trans_lt hl
  have hhiWord : hi < 2 ^ w := (Nat.div_le_self ..).trans_lt hu
  have hsub : denominator - 1 < 2 ^ w := (Nat.sub_le ..).trans_lt hd
  let mid := {st with regs := Function.update st.regs 34 lo}
  let out := {mid with regs := Function.update mid.regs 35 hi}
  have hr₁ : Runs w p ω
      (.assign 34 (.bin .div (.bin .mul (.const lower) (.reg 4)) (.const denominator)))
      st .normal mid 6 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hs, hlw, hd, hl, lo, hloWord],
      rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign 35 (.bin .div
      (.bin .add (.bin .mul (.const upper) (.reg 4)) (.bin .sub (.const denominator) (.const 1)))
      (.const denominator))) mid .normal out 10 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, mid, hs, hw, huw, hup, hd, hsub,
      hu, hi, hhiWord], rfl, rfl, rfl⟩
  have hb₁ : lo * denominator ≤ lower * scale := Nat.div_mul_le_self ..
  have hb₂ : upper * scale ≤ hi * denominator := by
    have hmod := Nat.mod_lt (upper * scale + (denominator - 1)) hdPos
    have hsum := Nat.mod_add_div (upper * scale + (denominator - 1)) denominator
    rw [Nat.mul_comm denominator] at hsum
    change (upper * scale + (denominator - 1)) % denominator + hi * denominator =
      upper * scale + (denominator - 1) at hsum
    omega
  have hsReal : (0 : ℝ) < scale := by exact_mod_cast hsPos
  have hdReal : (0 : ℝ) < denominator := by exact_mod_cast hdPos
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 6, 10, hr₁, hr₂, rfl⟩),
    ?_, ?_, by simp [out, mid, lo], by simp [out, hi], rfl, ?_⟩
  · simp only [out, mid, Function.update_of_ne (by decide : (34 : ℕ) ≠ 35), Function.update_self]
    exact ((div_le_div_iff₀ hsReal hdReal).mpr (by exact_mod_cast hb₁)).trans hlo
  · simp only [out, Function.update_self]
    exact hhi.trans ((div_le_div_iff₀ hdReal hsReal).mpr (by exact_mod_cast hb₂))
  · intro r h34 h35
    simp [out, mid, h34, h35]

/-- Prepare the bucket parameters and scale the fixed witness coefficient. -/
@[expose] def prepareInitConcreteBucket (lower upper denominator : ℕ) : Stmt :=
  prepareInitBucketParameters ;; initBucketCoefficient lower upper denominator

/-- The bucket calculator can read its runtime parameters and its scaled
coefficient from the same state. -/
theorem prepareInitConcreteBucket_runs (C : ℝ)
    {w lower upper denominator scale psi branch : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hpsi : st.regs 6 = psi) (hbranch : st.regs 76 = branch)
    (hs : st.regs 4 = scale) (hsPos : 0 < scale) (hdPos : 0 < denominator)
    (hlo : (lower : ℝ) / denominator ≤ mwuK0 C)
    (hhi : mwuK0 C ≤ (upper : ℝ) / denominator)
    (hw : 1 < 2 ^ w) (hd : denominator < 2 ^ w)
    (hl : lower * scale < 2 ^ w) (hu : upper * scale + (denominator - 1) < 2 ^ w) :
    ∃ out, Runs w p ω (prepareInitConcreteBucket lower upper denominator) st .normal out 26 ∧
      out.regs 20 = psi ∧ out.regs 38 = branch ∧ out.regs 1 = branch ∧
      (out.regs 34 : ℝ) / scale ≤ mwuK0 C ∧ mwuK0 C ≤ (out.regs 35 : ℝ) / scale ∧
      out.regs 34 = lower * scale / denominator ∧
      out.regs 35 = (upper * scale + (denominator - 1)) / denominator ∧
      out.mem = st.mem ∧
      (∀ r, r ≠ 1 → r ≠ 20 → r ≠ 34 → r ≠ 35 → r ≠ 38 → out.regs r = st.regs r) := by
  obtain ⟨mid, hr, hp, hb, hk, hm, hkeep⟩ :=
    prepareInitBucketParameters_runs (w := w) (p := p) (ω := ω) hpsi hbranch
  obtain ⟨out, hr', hl', hu', h34, h35, hm', hkeep'⟩ :=
    initBucketCoefficient_runs (ω := ω) C ((hkeep 4 (by decide) (by decide) (by decide)).trans hs)
      hsPos hdPos hlo hhi hw hd hl hu
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 8, 17, hr, hr', rfl⟩),
    (hkeep' 20 (by decide) (by decide)).trans hp, (hkeep' 38 (by decide) (by decide)).trans hb,
    (hkeep' 1 (by decide) (by decide)).trans hk, hl', hu', h34, h35, hm'.trans hm,
    fun r h1 h20 h34 h35 h38 => (hkeep' r h34 h35).trans (hkeep r h20 h38 h1)⟩

/-- Pass the concrete vertex bound for the bucket schedule to the
shared logarithm routine and save the graph's actual vertex count. -/
@[expose] def prepareInitBucketVertexLog : Stmt :=
  .assign 57 (.reg 92) ;;
  initBucketVertexBound ;;
  .assign 92 (.reg 46)

/-- The runtime logarithm input is four times the base edge bound. -/
theorem prepareInitBucketVertexLog_runs {w M N : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hM : st.regs 22 = M) (hN : st.regs 92 = N) (hw : 4 < 2 ^ w)
    (hfit : 4 * M < 2 ^ w) :
    ∃ out, Runs w p ω prepareInitBucketVertexLog st .normal out 10 ∧
      out.regs 57 = N ∧ out.regs 92 = 4 * M ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 46 → r ≠ 57 → r ≠ 92 → out.regs r = st.regs r) := by
  let ready := {st with regs := Function.update st.regs 57 N}
  have hr₁ : Runs w p ω (.assign 57 (.reg 92)) st .normal ready 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hN], rfl, rfl, rfl⟩
  obtain ⟨mid, hr₂, h46, hm, hk⟩ :=
    initBucketVertexBound_runs (p := p) (ω := ω) (st := ready) (by simpa [ready] using hM) hw hfit
  let out := {mid with regs := Function.update mid.regs 92 (4 * M)}
  have hr₃ : Runs w p ω (.assign 92 (.reg 46)) mid .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, h46], rfl, rfl, rfl⟩
  refine ⟨out, ?_, ?_, by simp [out], hm, ?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨ready, 2, 7, hr₁,
      runs_seq_iff.mpr (Or.inr ⟨mid, 4, 2, hr₂, hr₃, rfl⟩), rfl⟩)
  · simp [out, hk 57 (by decide), ready]
  · intro r h46 h57 h92
    simpa [out, ready, h57, h92] using hk r h46

/-- Compute the bucket base logarithms and restore the graph vertex count. -/
@[expose] def initBucketBaseLogs (bits load log pack : ℕ) : Stmt :=
  prepareInitBucketVertexLog ;;
  computeInitBucketBaseLogs bits load log pack ;;
  .assign 98 (.reg 99) ;;
  .assign 92 (.reg 57)

/-- The base logarithms use the concrete vertex bound. Subsequent
initialization reads the actual vertex count and the new heap pointer. -/
theorem initBucketBaseLogs_runs
    {w h bits load log pack M N precision limbs heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hlogN : MeetsContract w p log (Num.logarithmContract w h (precision - (4 * M + 2).size - 10)))
    (hlogTwo : MeetsContract w p log (Num.logarithmContract w h (precision - 2 - 10)))
    (hM : st.regs 22 = M) (hN : st.regs 92 = N) (hs : st.regs 4 = 2 ^ precision)
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision) (hh : st.regs 98 = heap)
    (hwFour : 4 < 2 ^ w) (hw : 4 * M + 2 < 2 ^ w) (hword : (4 * M + 2) * 2 ^ precision < 2 ^ w)
    (hfit : 2 * ((4 * M + 2) * 2 ^ precision) < Num.capacity h limbs)
    (hz : ZeroFrom st.mem heap) (hdiv : h ∣ precision) (hwidth : precision < w)
    (hacc : (4 * M + 2).size + 11 ≤ precision) (hcap : precision + (4 * M + 2).size + 4 ≤ h * limbs)
    (hprec : 2 * precision + 9 < 2 ^ w) :
    let spaceN := limbs + limbs + Num.logarithmSpace limbs precision (4 * M + 2).size
    let spaceTwo := limbs + limbs + Num.logarithmSpace limbs precision 2
    heap + spaceN + spaceTwo < 2 ^ w →
    ∃ out c ret, Runs w p ω (initBucketBaseLogs bits load log pack) st .normal out c ∧
      (out.regs 26 : ℝ) / (2 ^ precision : ℕ) ≤ Real.log (((4 * M : ℕ) : ℝ) + 2) ∧
      Real.log (((4 * M : ℕ) : ℝ) + 2) ≤ (out.regs 27 : ℝ) / (2 ^ precision : ℕ) ∧
      (out.regs 28 : ℝ) / (2 ^ precision : ℕ) ≤ Real.log 2 ∧
      Real.log 2 ≤ (out.regs 29 : ℝ) / (2 ^ precision : ℕ) ∧
      (14 ≤ precision → 0 < out.regs 28) ∧
      out.regs 27 ≤ (4 * M + 2) * 2 ^ precision ∧ out.regs 29 ≤ 2 * 2 ^ precision ∧
      out.regs 4 = 2 ^ precision ∧ out.regs 98 = ret ∧ out.regs 92 = N ∧
      heap ≤ ret ∧ ret ≤ heap + spaceN + spaceTwo ∧ ZeroFrom out.mem ret ∧
      (∀ a < heap, out.mem a = st.mem a) ∧
      (∀ r < 95, r ∉ ([2, 3, 4, 26, 27, 28, 29, 46, 57] : List ℕ) → out.regs r = st.regs r) ∧
      c ≤ 142 * limbs + Num.logarithmCost limbs precision (4 * M + 2).size +
        Num.logarithmCost limbs precision 2 + 14 * (4 * M + 2).size + 238 := by
  dsimp only
  intro hroom
  obtain ⟨ready, hr₁, h57, h92, hm, hk⟩ :=
    prepareInitBucketVertexLog_runs (p := p) (ω := ω) hM hN hwFour (by omega)
  obtain ⟨mid, c, ret, hr₂, h26, h27, h28, h29, h28Pos, hu27, hu29, hs', h99, hretLo, hretHi,
    hz', hf, hk', hc⟩ :=
    computeInitBucketBaseLogs_runs (ω := ω) hbits hload hpack hlogN hlogTwo h92
      ((hk 4 (by decide) (by decide) (by decide)).trans hs)
      ((hk 67 (by decide) (by decide) (by decide)).trans hL)
      ((hk 68 (by decide) (by decide) (by decide)).trans hP)
      ((hk 98 (by decide) (by decide) (by decide)).trans hh)
      hw hword hfit (hm.symm ▸ hz) hdiv hwidth hacc hcap hprec hroom
  let next := {mid with regs := Function.update mid.regs 98 ret}
  let out := {next with regs := Function.update next.regs 92 N}
  have hr₃ : Runs w p ω (.assign 98 (.reg 99)) mid .normal next 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, h99], rfl, rfl, rfl⟩
  have hr₄ : Runs w p ω (.assign 92 (.reg 57)) next .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, next, hk' 57 (by decide) (by decide), h57],
      rfl, rfl, rfl⟩
  refine ⟨out, c + 17, ret, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp [out, next],
    by simp [out], hretLo, hretHi, hz', fun a ha => (hf a ha).trans (congrFun hm a), ?_, by omega⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨ready, 10, c + 6, hr₁,
      runs_seq_iff.mpr (Or.inr ⟨mid, c, 5, hr₂,
        runs_seq_iff.mpr (Or.inr ⟨next, 2, 2, hr₃, hr₄, rfl⟩), rfl⟩), by omega⟩)
  · simpa [out, next] using h26
  · simpa [out, next] using h27
  · simpa [out, next] using h28
  · simpa [out, next] using h29
  · simpa [out, next] using h28Pos
  · simpa [out, next] using hu27
  · simpa [out, next] using hu29
  · simpa [out, next] using hs'
  · intro r hr hn
    by_cases he : r = 92
    · subst r
      simpa [out] using hN.symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
      rcases hn with ⟨h2, h3, h4, h26, h27, h28, h29, h46, h57⟩
      have hm' := hk' r hr (by simp [h2, h3, h4, h26, h27, h28, h29, he])
      simpa [out, next, he, show r ≠ 98 by omega] using hm'.trans (hk r h46 h57 he)

/-- Evaluate the schedule logarithm and check the concrete bucket count. -/
@[expose] def initBucketCapFromSigma (bits load log pack : ℕ) : Stmt :=
  initBucketSigmaLogs bits load log pack ;; computeInitBucketCap

/-- From an enclosure of the schedule base, a set flag certifies the
bucket cap and the scratch heap remains available for initialization. -/
theorem initBucketCapFromSigma_runs
    (C : ℝ) (M N psi twoLo twoHi : ℕ) (hM : 1 ≤ M)
    {w h bits load log pack lo hi basePrecision limbs heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (h45 : st.regs 45 = lo) (h46 : st.regs 46 = hi)
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = basePrecision)
    (hh : st.regs 98 = heap)
    (hwlo : lo < 2 ^ w) (hwhi : hi < 2 ^ w) (hwidth : (7 * basePrecision) < w)
    (hflo : 2 * lo < Num.capacity h limbs) (hfhi : 2 * hi < Num.capacity h limbs)
    (hsfit : 2 * 2 ^ (7 * basePrecision) < Num.capacity h limbs)
    (hz : ZeroFrom st.mem heap) (hdiv : h ∣ (7 * basePrecision))
    (hprec : 2 * (7 * basePrecision) + 9 < 2 ^ w)
    (h43 : st.regs 43 = (2 ^ basePrecision) ^ 7) (hw : 10 < 2 ^ w)
    (htwo : 2 ≤ (lo : ℝ) / (2 : ℝ) ^ (7 * basePrecision))
    (hpsi : st.regs 20 = psi) (hpsiPos : 0 < psi) (hpsiFit : 2 * psi < 2 ^ w)
    (hd : st.regs 75 = (concreteChainParams M hM).d)
    (h28 : st.regs 28 = twoLo) (h29 : st.regs 29 = twoHi) (htwoLoPos : 0 < twoLo)
    (htwoLo : (twoLo : ℝ) / (2 : ℝ) ^ basePrecision ≤ Real.log 2)
    (htwoHi : Real.log 2 ≤ (twoHi : ℝ) / (2 : ℝ) ^ basePrecision)
    (hDenWord : twoLo * twoHi < 2 ^ w) :
    let P := concreteChainParams M hM
    let σ := max (2 : ℝ) (max 1 (mwuK0 C * (P.k : ℝ) * (Real.log ((N : ℝ) + 2)) ^ 6))
    let range := hi.size - 7 * basePrecision
    let accuracy := 7 * basePrecision - range - 10
    let logLimit := (range + 1) * 2 ^ basePrecision
    let numerator := 2 * psi * 2 ^ basePrecision + P.d * logLimit
    (lo : ℝ) / (2 : ℝ) ^ (7 * basePrecision) ≤ σ →
    σ ≤ (hi : ℝ) / (2 : ℝ) ^ (7 * basePrecision) →
    MeetsContract w p log (Num.logarithmContract w h accuracy) →
    range + 11 ≤ 7 * basePrecision → 7 * basePrecision + range + 4 ≤ h * limbs →
    heap + 2 * (limbs + limbs + Num.logarithmSpace limbs (7 * basePrecision) range) < 2 ^ w →
    (range + 1) * 2 ^ (7 * basePrecision) + (2 ^ (6 * basePrecision) - 1) < 2 ^ w →
    numerator * twoLo < 2 ^ w → numerator * twoHi + 2 < 2 ^ w →
    ∃ out c ret, Runs w p ω (initBucketCapFromSigma bits load log pack) st .normal out c ∧
      (out.regs 18 = 1 → out.regs 47 = concreteBCap C psi M N hM) ∧
      (out.regs 18 = 1 ↔ (out.regs 15 - 1) / out.regs 16 * out.regs 16 < out.regs 14) ∧
      out.regs 4 = 2 ^ basePrecision ∧ out.regs 68 = basePrecision ∧ out.regs 99 = ret ∧
      heap ≤ ret ∧ ret ≤ heap + 2 * (limbs + limbs + Num.logarithmSpace limbs (7 * basePrecision) range) ∧
      (∀ r, r ∉ ([2, 3, 4, 14, 15, 16, 17, 18, 19, 26, 27, 30, 31, 32, 33, 36,
        47, 95, 96, 97, 98, 99, 100] : List ℕ) → out.regs r = st.regs r) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem ret ∧
      c ≤ 142 * limbs + 2 * Num.logarithmCost limbs (7 * basePrecision) range + 14 * hi.size + 254 := by
  dsimp only
  intro hlo hhi hlog hacc hcap hroom hbound hLoWord hHiWord
  obtain ⟨mid, c, ret, hr, hl, hu, hlimit, hs, hp, hret, hretLo, hretHi, hk, hf, hz', hc⟩ :=
    initBucketSigmaLogs_runs (ω := ω) hload hbits hpack h45 h46 hL hP hh hwlo hwhi hwidth
      hflo hfhi hsfit hz hdiv hprec h43 hw htwo hlo hhi hlog hacc hcap hroom hbound
  have hsReal : 0 < (2 : ℝ) ^ basePrecision := by positivity
  have hord : mid.regs 26 ≤ mid.regs 27 := by
    exact_mod_cast (div_le_div_iff_of_pos_right hsReal).mp (hl.trans hu)
  have hn (x y : ℕ) (hxy : x ≤ y) :
      2 * psi * 2 ^ basePrecision + (concreteChainParams M hM).d * x ≤
        2 * psi * 2 ^ basePrecision + (concreteChainParams M hM).d * y :=
    Nat.add_le_add_left (Nat.mul_le_mul_left _ hxy) _
  have htwoHiPos : 0 < twoHi := by
    by_contra! hh
    have he : twoHi = 0 := by omega
    simp [he, (Real.log_pos (by norm_num : (1 : ℝ) < 2)).not_ge] at htwoHi
  obtain ⟨out, hr', hcap', _, hflag, hm, hk'⟩ :=
    computeInitBucketCap_runs (ω := ω) C M N psi (2 ^ basePrecision)
      (mid.regs 26) (mid.regs 27) twoLo twoHi hM
      ((hk 20 (by decide)).trans hpsi) ((hk 75 (by decide)).trans hd) hs (by positivity)
      rfl rfl ((hk 28 (by decide)).trans h28) ((hk 29 (by decide)).trans h29) (by omega)
      hpsiFit htwoLoPos hDenWord
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hl)
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hu)
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using htwoLo)
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using htwoHi)
      ((Nat.mul_le_mul_right _ (hn _ _ (hord.trans hlimit))).trans_lt hLoWord)
      (by positivity) ((Nat.add_le_add_right (Nat.mul_le_mul_right _ (hn _ _ hlimit)) _).trans_lt hHiWord)
  refine ⟨out, c + 49, ret, runs_seq_iff.mpr (Or.inr ⟨mid, c, 48, hr, hr', rfl⟩),
    hcap', hflag, (hk' 4 (by decide)).trans hs, (hk' 68 (by decide)).trans hp,
    (hk' 99 (by decide)).trans hret, hretLo, hretHi, ?_,
    fun a ha => (congrFun hm a).trans (hf a ha), hm.symm ▸ hz', by omega⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rcases hr with ⟨h2, h3, h4, h14, h15, h16, h17, h18, h19, h26, h27, h30, h31, h32,
    h33, h36, h47, h95, h96, h97, h98, h99, h100⟩
  exact (hk' r (by simp [h14, h15, h16, h17, h18, h19, h47])).trans
    (hk r (by simp [h2, h3, h4, h26, h27, h30, h31, h32, h33, h36, h95, h96, h97, h98, h99, h100]))

/-- Form the schedule base interval, then evaluate its logarithms and
check the cap. -/
@[expose] def initBucketCapFromBaseLogs (power bits load log pack : ℕ) : Stmt :=
  computeInitBucketSigma power ;; initBucketCapFromSigma bits load log pack

/-- The checked bucket count follows from the runtime base logarithms and
the bounds on the fixed MWU coefficient. -/
theorem initBucketCapFromBaseLogs_runs
    (C : ℝ) (M N psi twoLo twoHi cLo cHi logLo logHi : ℕ) (hM : 1 ≤ M)
    {w h power bits load log pack basePrecision limbs heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hpower : MeetsContract w p power (initStretchPowerContract w))
    (hs : st.regs 4 = 2 ^ basePrecision)
    (h34 : st.regs 34 = cLo) (h35 : st.regs 35 = cHi)
    (h26 : st.regs 26 = logLo) (h27 : st.regs 27 = logHi)
    (h38 : st.regs 38 = (concreteChainParams M hM).k)
    (hcLo : (cLo : ℝ) / (2 ^ basePrecision : ℕ) ≤ mwuK0 C)
    (hcHi : mwuK0 C ≤ (cHi : ℝ) / (2 ^ basePrecision : ℕ))
    (hlLo : (logLo : ℝ) / (2 ^ basePrecision : ℕ) ≤ Real.log ((N : ℝ) + 2))
    (hlHi : Real.log ((N : ℝ) + 2) ≤ (logHi : ℝ) / (2 ^ basePrecision : ℕ))
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = basePrecision)
    (hh : st.regs 98 = heap)
     (hwidth : (7 * basePrecision) < w)
    (hsfit : 2 * 2 ^ (7 * basePrecision) < Num.capacity h limbs)
    (hz : ZeroFrom st.mem heap) (hdiv : h ∣ (7 * basePrecision))
    (hprec : 2 * (7 * basePrecision) + 9 < 2 ^ w)
    (hw : 10 < 2 ^ w)
    (hpsi : st.regs 20 = psi) (hpsiPos : 0 < psi) (hpsiFit : 2 * psi < 2 ^ w)
    (hd : st.regs 75 = (concreteChainParams M hM).d)
    (h28 : st.regs 28 = twoLo) (h29 : st.regs 29 = twoHi) (htwoLoPos : 0 < twoLo)
    (htwoLo : (twoLo : ℝ) / (2 : ℝ) ^ basePrecision ≤ Real.log 2)
    (htwoHi : Real.log 2 ≤ (twoHi : ℝ) / (2 : ℝ) ^ basePrecision)
    (hDenWord : twoLo * twoHi < 2 ^ w) :
    let P := concreteChainParams M hM
    let scale : ℕ := 2 ^ basePrecision
    let lo := max (2 * scale ^ 7) (cLo * P.k * logLo ^ 6)
    let hi := max (2 * scale ^ 7) (cHi * P.k * logHi ^ 6)
    let range := hi.size - 7 * basePrecision
    let accuracy := 7 * basePrecision - range - 10
    let logLimit := (range + 1) * 2 ^ basePrecision
    let numerator := 2 * psi * 2 ^ basePrecision + P.d * logLimit
    logLo ^ 2 < 2 ^ w ∧ logLo ^ 3 < 2 ^ w ∧ logLo ^ 6 < 2 ^ w ∧ cLo * P.k < 2 ^ w →
    logHi ^ 2 < 2 ^ w ∧ logHi ^ 3 < 2 ^ w ∧ logHi ^ 6 < 2 ^ w ∧ cHi * P.k < 2 ^ w →
    lo < 2 ^ w → hi < 2 ^ w → 2 * lo < Num.capacity h limbs → 2 * hi < Num.capacity h limbs →
    MeetsContract w p log (Num.logarithmContract w h accuracy) →
    range + 11 ≤ 7 * basePrecision → 7 * basePrecision + range + 4 ≤ h * limbs →
    heap + 2 * (limbs + limbs + Num.logarithmSpace limbs (7 * basePrecision) range) < 2 ^ w →
    (range + 1) * 2 ^ (7 * basePrecision) + (2 ^ (6 * basePrecision) - 1) < 2 ^ w →
    numerator * twoLo < 2 ^ w → numerator * twoHi + 2 < 2 ^ w →
    ∃ out c ret, Runs w p ω (initBucketCapFromBaseLogs power bits load log pack) st .normal out c ∧
      (out.regs 18 = 1 → out.regs 47 = concreteBCap C psi M N hM) ∧
      (out.regs 18 = 1 ↔ (out.regs 15 - 1) / out.regs 16 * out.regs 16 < out.regs 14) ∧
      out.regs 4 = 2 ^ basePrecision ∧ out.regs 68 = basePrecision ∧ out.regs 99 = ret ∧
      heap ≤ ret ∧ ret ≤ heap + 2 * (limbs + limbs + Num.logarithmSpace limbs (7 * basePrecision) range) ∧
      (∀ r, r ∉ ([2, 3, 4, 14, 15, 16, 17, 18, 19, 26, 27, 30, 31, 32, 33, 36,
        40, 42, 43, 45, 46, 47, 95, 96, 97, 98, 99, 100] : List ℕ) → out.regs r = st.regs r) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem ret ∧
      c ≤ 142 * limbs + 2 * Num.logarithmCost limbs (7 * basePrecision) range + 14 * hi.size + 455 := by
  dsimp only
  intro hwordsLo hwordsHi hwlo hwhi hflo hfhi hlog hacc hcap hroom hbound hLoWord hHiWord
  let k := (concreteChainParams M hM).k
  let scale : ℕ := 2 ^ basePrecision
  let lo := max (2 * scale ^ 7) (cLo * k * logLo ^ 6)
  let hi := max (2 * scale ^ 7) (cHi * k * logHi ^ 6)
  have hdenFit : 2 * scale ^ 7 < 2 ^ w := (le_max_left _ _).trans_lt hwlo
  obtain ⟨mid, c₁, hr₁, hlow, hhigh, h45, h46, h43, hm, hk, hc₁⟩ :=
    computeInitBucketSigma_runs (ω := ω) C N k scale cLo cHi logLo logHi
      hpower hs (by positivity) h34 h35 h26 h27 h38 hcLo hcHi hlLo hlHi (by omega) hdenFit
      ⟨hwordsLo.1, hwordsLo.2.1, hwordsLo.2.2.1, hwordsLo.2.2.2,
        (le_max_right _ _).trans_lt hwlo⟩
      ⟨hwordsHi.1, hwordsHi.2.1, hwordsHi.2.2.1, hwordsHi.2.2.2,
        (le_max_right _ _).trans_lt hwhi⟩
  have hpow : ((scale ^ 7 : ℕ) : ℝ) = 2 ^ (7 * basePrecision) := by
    simp [scale, ← pow_mul, Nat.mul_comm]
  have htwo : (2 : ℝ) ≤ (lo : ℝ) / (2 : ℝ) ^ (7 * basePrecision) := by
    apply (le_div_iff₀ (by positivity)).mpr
    rw [← hpow, ← Nat.cast_ofNat (R := ℝ) (n := 2), ← Nat.cast_mul]
    exact_mod_cast (le_max_left (2 * scale ^ 7) (cLo * k * logLo ^ 6))
  obtain ⟨out, c₂, ret, hr₂, hres, hflag, hs', hp', hret, hretLo, hretHi, hk', hf, hz', hc₂⟩ :=
    initBucketCapFromSigma_runs (ω := ω) C M N psi twoLo twoHi hM hload hbits hpack h45 h46
      ((hk 67 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hL)
      ((hk 68 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hP)
      ((hk 98 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hh)
      hwlo hwhi hwidth hflo hfhi hsfit (hm.symm ▸ hz) hdiv hprec h43 hw htwo
      ((hk 20 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hpsi)
      hpsiPos hpsiFit ((hk 75 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hd)
      ((hk 28 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h28)
      ((hk 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h29)
      htwoLoPos htwoLo htwoHi hDenWord
      (by simpa only [h45, h43, hpow] using hlow)
      (by simpa only [h46, h43, hpow] using hhigh)
      hlog hacc hcap hroom hbound hLoWord hHiWord
  refine ⟨out, c₁ + c₂ + 1, ret, runs_seq_iff.mpr (Or.inr ⟨mid, c₁, c₂, hr₁, hr₂, rfl⟩),
    hres, hflag, hs', hp', hret, hretLo, hretHi, ?_,
    fun x hx => (hf x hx).trans (congrFun hm x), hz', ?_⟩
  · intro r hn
    have hsub : ([2, 3, 4, 14, 15, 16, 17, 18, 19, 26, 27, 30, 31, 32, 33, 36,
        47, 95, 96, 97, 98, 99, 100] : List ℕ).Sublist
        [2, 3, 4, 14, 15, 16, 17, 18, 19, 26, 27, 30, 31, 32, 33, 36,
          40, 42, 43, 45, 46, 47, 95, 96, 97, 98, 99, 100] := by
      repeat first | apply List.Sublist.cons_cons | apply List.Sublist.cons | exact List.Sublist.slnil
    exact (hk' r (fun hm => hn (hsub.subset hm))).trans (hk r
      (fun he => hn (he.symm ▸ (by decide)))
      (fun he => hn (he.symm ▸ (by decide)))
      (fun he => hn (he.symm ▸ (by decide)))
      (fun he => hn (he.symm ▸ (by decide)))
      (fun he => hn (he.symm ▸ (by decide))))
  · change c₂ ≤ 142 * limbs + 2 *
      Num.logarithmCost limbs (7 * basePrecision) (hi.size - 7 * basePrecision) + 14 * hi.size + 254 at hc₂
    change c₁ + c₂ + 1 ≤ 142 * limbs + 2 *
      Num.logarithmCost limbs (7 * basePrecision) (hi.size - 7 * basePrecision) + 14 * hi.size + 455
    omega

/-- Build the concrete bucket cap from the runtime edge bound and the
fixed MWU coefficient enclosure. -/
@[expose] def initConcreteBucketCap (power bits load log pack : ℕ) : Stmt :=
  initBucketBaseLogs bits load log pack ;; initBucketCapFromBaseLogs power bits load log pack

/-- The bucket initializer computes the logarithm inputs from the edge
bound and certifies the cap whenever its ceiling check succeeds. -/
theorem initConcreteBucketCap_runs
    (C : ℝ) (M N psi cLo cHi : ℕ) (hM : 1 ≤ M)
    {w h power bits load log pack precision limbs heap heapLimit costLimit : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hpower : MeetsContract w p power (initStretchPowerContract w))
    (hlogN : MeetsContract w p log (Num.logarithmContract w h (precision - (4 * M + 2).size - 10)))
    (hlogTwo : MeetsContract w p log (Num.logarithmContract w h (precision - 2 - 10)))
    (h22 : st.regs 22 = M) (h92 : st.regs 92 = N)
    (hs : st.regs 4 = 2 ^ precision) (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision)
    (hh : st.regs 98 = heap)
    (h34 : st.regs 34 = cLo) (h35 : st.regs 35 = cHi)
    (h38 : st.regs 38 = (concreteChainParams M hM).k)
    (hcLo : (cLo : ℝ) / (2 ^ precision : ℕ) ≤ mwuK0 C)
    (hcHi : mwuK0 C ≤ (cHi : ℝ) / (2 ^ precision : ℕ))
    (hpsi : st.regs 20 = psi) (hpsiPos : 0 < psi) (hpsiFit : 2 * psi < 2 ^ w)
    (hd : st.regs 75 = (concreteChainParams M hM).d)
    (hw : 10 < 2 ^ w) (hvertex : 4 * M + 2 < 2 ^ w)
    (hword : (4 * M + 2) * 2 ^ precision < 2 ^ w)
    (hfit : 2 * ((4 * M + 2) * 2 ^ precision) < Num.capacity h limbs)
    (hdiv : h ∣ precision) (hwidth : 7 * precision < w) (hz : ZeroFrom st.mem heap)
    (hacc : (4 * M + 2).size + 11 ≤ precision) (hlogPos : 14 ≤ precision)
    (hcap : precision + (4 * M + 2).size + 4 ≤ h * limbs)
    (hprec : 2 * (7 * precision) + 9 < 2 ^ w)
    (hsfit : 2 * 2 ^ (7 * precision) < Num.capacity h limbs) :
    let P := concreteChainParams M hM
    let scale : ℕ := 2 ^ precision
    let baseRange := (4 * M + 2).size
    let baseHeap := heap + (limbs + limbs + Num.logarithmSpace limbs precision baseRange) +
      (limbs + limbs + Num.logarithmSpace limbs precision 2)
    baseHeap < 2 ^ w →
    (∀ logLo logHi twoLo twoHi : ℕ,
      logLo ≤ logHi → logHi ≤ (4 * M + 2) * scale → twoLo ≤ twoHi → twoHi ≤ 2 * scale →
      let lo := max (2 * scale ^ 7) (cLo * P.k * logLo ^ 6)
      let hi := max (2 * scale ^ 7) (cHi * P.k * logHi ^ 6)
      let range := hi.size - 7 * precision
      let accuracy := 7 * precision - range - 10
      let numerator := 2 * psi * scale + P.d * ((range + 1) * scale)
      (logLo ^ 2 < 2 ^ w ∧ logLo ^ 3 < 2 ^ w ∧ logLo ^ 6 < 2 ^ w ∧ cLo * P.k < 2 ^ w) ∧
      (logHi ^ 2 < 2 ^ w ∧ logHi ^ 3 < 2 ^ w ∧ logHi ^ 6 < 2 ^ w ∧ cHi * P.k < 2 ^ w) ∧
      lo < 2 ^ w ∧ hi < 2 ^ w ∧ 2 * lo < Num.capacity h limbs ∧ 2 * hi < Num.capacity h limbs ∧
      MeetsContract w p log (Num.logarithmContract w h accuracy) ∧
      range + 11 ≤ 7 * precision ∧ 7 * precision + range + 4 ≤ h * limbs ∧
      baseHeap + 2 * (limbs + limbs + Num.logarithmSpace limbs (7 * precision) range) < 2 ^ w ∧
      baseHeap + 2 * (limbs + limbs + Num.logarithmSpace limbs (7 * precision) range) ≤ heapLimit ∧
      (range + 1) * 2 ^ (7 * precision) + (2 ^ (6 * precision) - 1) < 2 ^ w ∧
      numerator * twoLo < 2 ^ w ∧ numerator * twoHi + 2 < 2 ^ w ∧ twoLo * twoHi < 2 ^ w ∧
      142 * limbs + 2 * Num.logarithmCost limbs (7 * precision) range + 14 * hi.size + 455 ≤ costLimit) →
    ∃ out c ret, Runs w p ω (initConcreteBucketCap power bits load log pack) st .normal out c ∧
      (out.regs 18 = 1 → out.regs 47 = concreteBCap C psi M (4 * M) hM) ∧
      (out.regs 18 = 1 ↔ (out.regs 15 - 1) / out.regs 16 * out.regs 16 < out.regs 14) ∧
      (0 < out.regs 28 ∧ (out.regs 28 : ℝ) / scale ≤ Real.log 2 ∧
        Real.log 2 ≤ (out.regs 29 : ℝ) / scale ∧ out.regs 29 ≤ 2 * scale) ∧
      out.regs 4 = scale ∧ out.regs 68 = precision ∧ out.regs 92 = N ∧ out.regs 99 = ret ∧
      heap ≤ ret ∧ ret ≤ heapLimit ∧ ZeroFrom out.mem ret ∧
      (∀ r < 95, r ∉ ([2, 3, 4, 14, 15, 16, 17, 18, 19, 26, 27, 28, 29,
        30, 31, 32, 33, 36, 40, 42, 43, 45, 46, 47, 57] : List ℕ) → out.regs r = st.regs r) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧
      c ≤ 142 * limbs + Num.logarithmCost limbs precision baseRange +
        Num.logarithmCost limbs precision 2 + 14 * baseRange + 239 + costLimit := by
  dsimp only
  intro hbaseRoom hbudget
  obtain ⟨mid, c₁, next, hr₁, hlo, hhi, htwoLo, htwoHi, htwoPos, hu, htu, hs', hh', h92', hnext,
    hnextHi, hz', hf, hk, hc₁⟩ :=
    initBucketBaseLogs_runs (ω := ω) hbits hload hpack hlogN hlogTwo h22 h92 hs hL hP hh
      (by omega) hvertex hword hfit hz hdiv (by omega) hacc hcap (by omega) hbaseRoom
  have hsReal : (0 : ℝ) < ((2 ^ precision : ℕ) : ℝ) := by positivity
  have horder : mid.regs 26 ≤ mid.regs 27 := by
    exact_mod_cast (div_le_div_iff_of_pos_right hsReal).mp (hlo.trans hhi)
  have htorder : mid.regs 28 ≤ mid.regs 29 := by
    exact_mod_cast (div_le_div_iff_of_pos_right hsReal).mp (htwoLo.trans htwoHi)
  obtain ⟨hLw, hHw, hLo, hHi, hLf, hHf, hlog, ha, hc, hroom, hheap, hb, hnLo, hnHi, hden, hcost⟩ :=
    hbudget _ _ _ _ horder hu htorder htu
  have keep (r : ℕ) (hr : r < 95)
      (hn : r ∉ ([2, 3, 4, 26, 27, 28, 29, 46, 57] : List ℕ)) :
      mid.regs r = st.regs r := hk r hr hn
  obtain ⟨out, c₂, ret, hr₂, hres, hflag, hs'', hp'', h99, hretLo, hretHi, hk', hf', hz'', hc₂⟩ :=
    initBucketCapFromBaseLogs_runs (ω := ω) C M (4 * M) psi (mid.regs 28) (mid.regs 29)
      cLo cHi (mid.regs 26) (mid.regs 27) hM
      hload hbits hpack hpower hs' ((keep 34 (by decide) (by decide)).trans h34)
      ((keep 35 (by decide) (by decide)).trans h35) rfl rfl
      ((keep 38 (by decide) (by decide)).trans h38) hcLo hcHi hlo hhi
      ((keep 67 (by decide) (by decide)).trans hL) ((keep 68 (by decide) (by decide)).trans hP)
      hh' hwidth hsfit hz' (dvd_mul_of_dvd_right hdiv 7) hprec hw
      ((keep 20 (by decide) (by decide)).trans hpsi) hpsiPos hpsiFit
      ((keep 75 (by decide) (by decide)).trans hd) rfl rfl (htwoPos hlogPos)
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using htwoLo)
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using htwoHi)
      hden hLw hHw hLo hHi hLf hHf hlog ha hc
      ((Nat.add_le_add_right hnextHi _).trans_lt hroom) hb hnLo hnHi
  refine ⟨out, c₁ + c₂ + 1, ret, runs_seq_iff.mpr (Or.inr ⟨mid, c₁, c₂, hr₁, hr₂, rfl⟩),
    hres, hflag, ?_, hs'', hp'', (hk' 92 (by decide)).trans h92', h99, hnext.trans hretLo,
    hretHi.trans ((Nat.add_le_add_right hnextHi _).trans hheap), hz'', ?_,
    fun a ha => (hf' a (ha.trans_le hnext)).trans (hf a ha), ?_⟩
  · rw [hk' 28 (by decide), hk' 29 (by decide)]
    exact ⟨htwoPos hlogPos, htwoLo, htwoHi, htu⟩
  · intro r hr hn
    have hs₁ : ([2, 3, 4, 26, 27, 28, 29, 46, 57] : List ℕ).Sublist
        [2, 3, 4, 14, 15, 16, 17, 18, 19, 26, 27, 28, 29,
          30, 31, 32, 33, 36, 40, 42, 43, 45, 46, 47, 57] := by decide
    have hs₂ : ([2, 3, 4, 14, 15, 16, 17, 18, 19, 26, 27, 30, 31, 32, 33, 36,
        40, 42, 43, 45, 46, 47] : List ℕ).Sublist
        [2, 3, 4, 14, 15, 16, 17, 18, 19, 26, 27, 28, 29,
          30, 31, 32, 33, 36, 40, 42, 43, 45, 46, 47, 57] := by decide
    apply Eq.trans (hk' r _) (hk r hr (fun hm => hn (hs₁.subset hm)))
    intro hm
    have hsplit : r ∈ ([2, 3, 4, 14, 15, 16, 17, 18, 19, 26, 27, 30, 31, 32, 33, 36,
        40, 42, 43, 45, 46, 47] : List ℕ) ∨ r ∈ ([95, 96, 97, 98, 99, 100] : List ℕ) :=
      List.mem_append.mp hm
    rcases hsplit with hl | hh
    · exact hn (hs₂.subset hl)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
      omega
  · exact (Nat.add_le_add_right (Nat.add_le_add hc₁ (hc₂.trans hcost)) 1).trans (by omega)

/-- The concrete bucket formula already produces a positive count, so a
certified count is the bucket bound used by each sparse-core level. -/
theorem concreteEnv_bucketBound_eq
    (C Ψ : ℝ) (M degree : ℕ) (hM : 1 ≤ M)
    (params : ℕ → DynSpanner.SparsifyParams)
    (hp_s : ∀ m, (params m).p_s ≤ 1) (hp_t : ∀ m, (params m).p_t ≤ 1)
    (m : ℕ) :
    (concreteEnv C params hp_s hp_t M (concreteBCap C Ψ M (4 * M) hM) degree).B_fn m =
      concreteBCap C Ψ M (4 * M) hM := by
  have hpos : 1 ≤ concreteBCap C Ψ M (4 * M) hM := by
    dsimp only [concreteBCap]
    omega
  change max 1 (concreteBCap C Ψ M (4 * M) hM) = _
  exact max_eq_right hpos

/-- Run the threshold initializer only when the bucket ceiling has
been certified. Pass it the heap returned by the bucket calculation. -/
@[expose] def initThresholdsAfterBucketCap (thresholds : Stmt) : Stmt :=
  .cond (.bin .eq (.reg 18) (.const 1))
    (.assign 98 (.reg 99) ;; thresholds)
    (.assign 10 (.const 0))

/-- A certified bucket cap enters threshold initialization with a fresh
heap and the same runtime configuration registers. -/
theorem initThresholdsAfterBucketCap_runs {w heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st out : State} {thresholds : Stmt}
    {c : ℕ} (hflag : st.regs 18 = 1) (hh : st.regs 99 = heap)
    (hw : 1 < 2 ^ w)
    (hr : Runs w p ω thresholds {st with regs := Function.update st.regs 98 heap}
      .normal out c) :
    Runs w p ω (initThresholdsAfterBucketCap thresholds) st .normal out (c + 7) := by
  let mid := {st with regs := Function.update st.regs 98 heap}
  have hmove : Runs w p ω (.assign 98 (.reg 99)) st .normal mid 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hh], rfl, rfl, rfl⟩
  have hcond : Expr.eval w st (.bin .eq (.reg 18) (.const 1)) = some 1 := by
    simp [Expr.eval, BinOp.eval, hflag, hw]
  exact runs_cond_iff.mpr ⟨1, 2 + c + 1, hcond,
    runs_seq_iff.mpr (Or.inr ⟨mid, 2, c, hmove, hr, rfl⟩), by
      simp [Expr.size_bin, Expr.size_reg, Expr.size_const]; omega⟩

/-- An inconclusive cap check leaves memory untouched and clears the
threshold certification flag. -/
theorem initThresholdsAfterBucketCap_inconclusive_runs {w : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {thresholds : Stmt}
    (hflag : st.regs 18 ≠ 1) (hw : 1 < 2 ^ w) :
    ∃ out, Runs w p ω (initThresholdsAfterBucketCap thresholds) st .normal out 6 ∧
      out.regs 10 = 0 ∧ out.mem = st.mem ∧ out.regs 99 = st.regs 99 := by
  let out := {st with regs := Function.update st.regs 10 0}
  have hr : Runs w p ω (.assign 10 (.const 0)) st .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hcond : Expr.eval w st (.bin .eq (.reg 18) (.const 1)) = some 0 := by
    simp [Expr.eval, BinOp.eval, hflag, hw, show 0 < 2 ^ w by omega]
  exact ⟨out, runs_cond_iff.mpr ⟨0, 2, hcond, hr, rfl⟩, by simp [out], rfl, by simp [out]⟩

/-- Initialize the bucket cap and then the checked rebuild thresholds
for Algorithms 1 and 2. -/
@[expose] def initConcreteBucketAndThresholds (power bits load log pack : ℕ) : Stmt :=
  initConcreteBucketCap power bits load log pack ;;
  initThresholdsAfterBucketCap
    (initSparsifierCoefficient ;; initThresholdTableFromSparseCoreLog power bits load log pack)

/-- The threshold table is read only after its certification flag is
set. An inconclusive bucket check leaves that flag clear. -/
theorem initConcreteBucketAndThresholds_runs
    (TP : SparseCoreParams) (P : ChainParams) (N last : ℕ)
    {w power bits load log pack bucketCost thresholdCost heap scale : ℕ}
    {p : Program} {ω : ℕ → Bool} {st bucket : State}
    (hw : 36 < 2 ^ w)
    (hb : Runs w p ω (initConcreteBucketCap power bits load log pack) st .normal bucket bucketCost)
    (hh : bucket.regs 99 = heap)
    (hscale : bucket.regs 4 = scale) (hsPos : 0 < scale)
    (hlog : 0 < bucket.regs 28 ∧ (bucket.regs 28 : ℝ) / scale ≤ Real.log 2 ∧
      Real.log 2 ≤ (bucket.regs 29 : ℝ) / scale)
    (hword : scale + 36 * scale * scale + (bucket.regs 28 - 1) < 2 ^ w)
    (ht : bucket.regs 18 = 1 → ∀ ready,
        (ready.regs 49 : ℝ) / scale ≤ 1 + 36 / Real.log 2 →
        1 + 36 / Real.log 2 ≤ (ready.regs 51 : ℝ) / scale →
        ready.mem = bucket.mem →
        (∀ r, r ≠ 37 → r ≠ 49 → r ≠ 51 → r ≠ 98 → ready.regs r = bucket.regs r) →
        ready.regs 98 = heap →
      ∃ out c base,
        Runs w p ω (initThresholdTableFromSparseCoreLog power bits load log pack)
          ready .normal out c ∧
        (out.regs 10 = 0 ∨ out.regs 10 = 1 ∧
          ∀ j ≤ last, out.mem (base + j) = rebuildThresholdWord TP P N j) ∧
        out.regs 83 = base ∧ c ≤ thresholdCost) :
    ∃ out c, Runs w p ω (initConcreteBucketAndThresholds power bits load log pack) st .normal out c ∧
      (out.regs 10 = 0 ∨ out.regs 10 = 1 ∧
        ∀ j ≤ last, out.mem (out.regs 83 + j) = rebuildThresholdWord TP P N j) ∧
      c ≤ bucketCost + thresholdCost + 33 := by
  by_cases hf : bucket.regs 18 = 1
  · let start := {bucket with regs := Function.update bucket.regs 98 heap}
    have hsReal : (0 : ℝ) < scale := by exact_mod_cast hsPos
    have hord : bucket.regs 28 ≤ bucket.regs 29 := by
      exact_mod_cast (div_le_div_iff_of_pos_right hsReal).mp (hlog.2.1.trans hlog.2.2)
    obtain ⟨ready, hcoeff, hlo, hhi, _, _, hm, hk⟩ :=
      initSparsifierCoefficient_runs (p := p) (ω := ω) (st := start)
        (by simpa [start] using hscale) (by simp [start]) (by simp [start])
        hsPos hlog.1 hord hlog.2.1 hlog.2.2 hw hword
    obtain ⟨out, c, base, hr, hcert, h83, hc⟩ :=
      ht hf ready hlo hhi hm (fun r h37 h49 h51 h98 =>
        (hk r h37 h49 h51).trans (by simp [start, h98]))
        ((hk 98 (by decide) (by decide) (by decide)).trans (by simp [start]))
    have hrun : Runs w p ω
        (initSparsifierCoefficient ;; initThresholdTableFromSparseCoreLog power bits load log pack)
        {bucket with regs := Function.update bucket.regs 98 heap} .normal out (24 + c + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨ready, 24, c, hcoeff, hr, rfl⟩)
    have hnext := initThresholdsAfterBucketCap_runs (w := w) hf hh (by omega) hrun
    refine ⟨out, bucketCost + (24 + c + 1 + 7) + 1,
      runs_seq_iff.mpr (Or.inr ⟨bucket, bucketCost, 24 + c + 1 + 7, hb, hnext, rfl⟩), ?_, by omega⟩
    simpa only [h83] using hcert
  · obtain ⟨out, hr, hflag, _, _⟩ := initThresholdsAfterBucketCap_inconclusive_runs
      (w := w) (p := p) (ω := ω) (thresholds := initSparsifierCoefficient ;;
        initThresholdTableFromSparseCoreLog power bits load log pack) hf (by omega)
    exact ⟨out, bucketCost + 6 + 1,
      runs_seq_iff.mpr (Or.inr ⟨bucket, bucketCost, 6, hb, hr, rfl⟩),
      Or.inl hflag, by omega⟩

/-- Set the fixed witness coefficient and calculate the concrete bucket cap. -/
@[expose] def initConcreteBucketCapWithWitness
    (lower upper denominator power bits load log pack : ℕ) : Stmt :=
  prepareInitConcreteBucket lower upper denominator ;; initConcreteBucketCap power bits load log pack

/-- The integrated bucket calculator uses the computed branching factor and
potential bound and certifies the concrete cap when its check succeeds. -/
theorem initConcreteBucketCapWithWitness_runs
    (C : ℝ) (M N psi : ℕ) (hM : 1 ≤ M)
    {w h lower upper denominator power bits load log pack precision limbs heap heapLimit costLimit : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hpower : MeetsContract w p power (initStretchPowerContract w))
    (hlogN : MeetsContract w p log (Num.logarithmContract w h (precision - (4 * M + 2).size - 10)))
    (hlogTwo : MeetsContract w p log (Num.logarithmContract w h (precision - 2 - 10)))
    (h22 : st.regs 22 = M) (h92 : st.regs 92 = N)
    (hs : st.regs 4 = 2 ^ precision) (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision)
    (hh : st.regs 98 = heap)
    (h76 : st.regs 76 = (concreteChainParams M hM).k)
    (hdPos : 0 < denominator) (hdWord : denominator < 2 ^ w)
    (hcl : (lower : ℝ) / denominator ≤ mwuK0 C) (hcu : mwuK0 C ≤ (upper : ℝ) / denominator)
    (hlWord : lower * 2 ^ precision < 2 ^ w)
    (huWord : upper * 2 ^ precision + (denominator - 1) < 2 ^ w)
    (hpsi : st.regs 6 = psi) (hpsiPos : 0 < psi) (hpsiFit : 2 * psi < 2 ^ w)
    (hd : st.regs 75 = (concreteChainParams M hM).d)
    (hw : 10 < 2 ^ w) (hvertex : 4 * M + 2 < 2 ^ w)
    (hword : (4 * M + 2) * 2 ^ precision < 2 ^ w)
    (hfit : 2 * ((4 * M + 2) * 2 ^ precision) < Num.capacity h limbs)
    (hdiv : h ∣ precision) (hwidth : 7 * precision < w) (hz : ZeroFrom st.mem heap)
    (hacc : (4 * M + 2).size + 11 ≤ precision) (hlogPos : 14 ≤ precision)
    (hcap : precision + (4 * M + 2).size + 4 ≤ h * limbs)
    (hprec : 2 * (7 * precision) + 9 < 2 ^ w)
    (hsfit : 2 * 2 ^ (7 * precision) < Num.capacity h limbs) :
    let P := concreteChainParams M hM
    let scale : ℕ := 2 ^ precision
    let cLo := lower * scale / denominator
    let cHi := (upper * scale + (denominator - 1)) / denominator
    let baseRange := (4 * M + 2).size
    let baseHeap := heap + (limbs + limbs + Num.logarithmSpace limbs precision baseRange) +
      (limbs + limbs + Num.logarithmSpace limbs precision 2)
    baseHeap < 2 ^ w →
    (∀ logLo logHi twoLo twoHi : ℕ,
      logLo ≤ logHi → logHi ≤ (4 * M + 2) * scale → twoLo ≤ twoHi → twoHi ≤ 2 * scale →
      let lo := max (2 * scale ^ 7) (cLo * P.k * logLo ^ 6)
      let hi := max (2 * scale ^ 7) (cHi * P.k * logHi ^ 6)
      let range := hi.size - 7 * precision
      let accuracy := 7 * precision - range - 10
      let numerator := 2 * psi * scale + P.d * ((range + 1) * scale)
      (logLo ^ 2 < 2 ^ w ∧ logLo ^ 3 < 2 ^ w ∧ logLo ^ 6 < 2 ^ w ∧ cLo * P.k < 2 ^ w) ∧
      (logHi ^ 2 < 2 ^ w ∧ logHi ^ 3 < 2 ^ w ∧ logHi ^ 6 < 2 ^ w ∧ cHi * P.k < 2 ^ w) ∧
      lo < 2 ^ w ∧ hi < 2 ^ w ∧ 2 * lo < Num.capacity h limbs ∧ 2 * hi < Num.capacity h limbs ∧
      MeetsContract w p log (Num.logarithmContract w h accuracy) ∧
      range + 11 ≤ 7 * precision ∧ 7 * precision + range + 4 ≤ h * limbs ∧
      baseHeap + 2 * (limbs + limbs + Num.logarithmSpace limbs (7 * precision) range) < 2 ^ w ∧
      baseHeap + 2 * (limbs + limbs + Num.logarithmSpace limbs (7 * precision) range) ≤ heapLimit ∧
      (range + 1) * 2 ^ (7 * precision) + (2 ^ (6 * precision) - 1) < 2 ^ w ∧
      numerator * twoLo < 2 ^ w ∧ numerator * twoHi + 2 < 2 ^ w ∧ twoLo * twoHi < 2 ^ w ∧
      142 * limbs + 2 * Num.logarithmCost limbs (7 * precision) range + 14 * hi.size + 455 ≤ costLimit) →
    ∃ out c ret, Runs w p ω (initConcreteBucketCapWithWitness lower upper denominator power bits load log pack) st .normal out c ∧
      (out.regs 18 = 1 → out.regs 47 = concreteBCap C psi M (4 * M) hM) ∧
      (out.regs 18 = 1 ↔ (out.regs 15 - 1) / out.regs 16 * out.regs 16 < out.regs 14) ∧
      (0 < out.regs 28 ∧ (out.regs 28 : ℝ) / scale ≤ Real.log 2 ∧
        Real.log 2 ≤ (out.regs 29 : ℝ) / scale ∧ out.regs 29 ≤ 2 * scale) ∧
      out.regs 4 = scale ∧ out.regs 68 = precision ∧ out.regs 92 = N ∧ out.regs 99 = ret ∧
      heap ≤ ret ∧ ret ≤ heapLimit ∧ ZeroFrom out.mem ret ∧
      (∀ r < 95, r ∉ ([1, 2, 3, 4, 14, 15, 16, 17, 18, 19, 20, 26, 27, 28, 29,
        30, 31, 32, 33, 34, 35, 36, 38, 40, 42, 43, 45, 46, 47, 57] : List ℕ) → out.regs r = st.regs r) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧
      c ≤ 142 * limbs + Num.logarithmCost limbs precision baseRange +
        Num.logarithmCost limbs precision 2 + 14 * baseRange + 266 + costLimit := by
  dsimp only
  intro hroom hbudget
  obtain ⟨mid, hr₁, hp, hk, _, hlo, hhi, hcLo, hcHi, hm, hkeep⟩ :=
    prepareInitConcreteBucket_runs (ω := ω) C hpsi h76 hs (by positivity)
      hdPos hcl hcu (by omega) hdWord hlWord huWord
  have keep (r : ℕ) (h : r ∉ ([1, 20, 34, 35, 38] : List ℕ)) :
      mid.regs r = st.regs r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    exact hkeep r h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
  obtain ⟨out, c, ret, hr₂, hres, hflag, hlogBounds, hscale, hprecision, hN, hheap, hretLo, hretHi, hz',
    hkeep', hf, hc⟩ :=
    initConcreteBucketCap_runs (ω := ω) C M N psi _ _ hM hload hbits hpack hpower hlogN hlogTwo
      ((keep 22 (by decide)).trans h22) ((keep 92 (by decide)).trans h92)
      ((keep 4 (by decide)).trans hs) ((keep 67 (by decide)).trans hL)
      ((keep 68 (by decide)).trans hP) ((keep 98 (by decide)).trans hh)
      hcLo hcHi hk (hcLo ▸ hlo) (hcHi ▸ hhi) hp hpsiPos hpsiFit ((keep 75 (by decide)).trans hd)
      hw hvertex hword hfit hdiv hwidth (hm.symm ▸ hz) hacc hlogPos hcap hprec hsfit hroom hbudget
  refine ⟨out, c + 27, ret, runs_seq_iff.mpr (Or.inr ⟨mid, 26, c, hr₁, hr₂, by omega⟩),
    hres, hflag, hlogBounds, hscale, hprecision, hN, hheap, hretLo, hretHi, hz', ?_,
    fun x hx => (hf x hx).trans (congrFun hm x), by omega⟩
  intro r hr hn
  exact (hkeep' r hr (fun hh => hn (show r ∈ _ from (List.Sublist.subset (by decide :
    ([2, 3, 4, 14, 15, 16, 17, 18, 19, 26, 27, 28, 29, 30, 31, 32, 33, 36,
      40, 42, 43, 45, 46, 47, 57] : List ℕ).Sublist
    [1, 2, 3, 4, 14, 15, 16, 17, 18, 19, 20, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35,
      36, 38, 40, 42, 43, 45, 46, 47, 57])) hh))).trans
    (keep r (fun hh => hn ((List.Sublist.subset (by decide :
      ([1, 20, 34, 35, 38] : List ℕ).Sublist
      [1, 2, 3, 4, 14, 15, 16, 17, 18, 19, 20, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35,
        36, 38, 40, 42, 43, 45, 46, 47, 57])) hh)))

/-- Compute the integer bucket cap with the chain vertex bound and
restore the actual graph vertex count for the following Init stages. -/
@[expose] def initConcreteIntegerBucketStage (clog lsstConstant : ℕ) : Stmt :=
  prepareInitBucketVertexLog ;;
  initIntegerBucketStage clog lsstConstant ;;
  .assign 92 (.reg 57)

/-- The concrete bucket stage uses the model's vertex bound, returns the
exact cap, and restores the graph's vertex count and heap cursor. -/
theorem initConcreteIntegerBucketStage_runs
    {w clog lsstConstant width M N heap : ℕ} (hM : 1 ≤ M)
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hp : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (h22 : st.regs 22 = M) (h92 : st.regs 92 = N) (h98 : st.regs 98 = heap)
    (h6 : st.regs 6 = width) (h75 : st.regs 75 = (concreteChainParams M hM).d)
    (h76 : st.regs 76 = (concreteChainParams M hM).k)
    (hvertices : 4 * M + 3 < 2 ^ w) :
    let P := concreteChainParams M hM
    let stretch := max 2 (concreteBucketStretch lsstConstant P.k (4 * M))
    let cap := concreteBucketCap lsstConstant width P.k P.d (4 * M)
    stretch + 1 < 2 ^ w → cap < 2 ^ w →
    ∃ out cost, Runs w p ω (initConcreteIntegerBucketStage clog lsstConstant) st .normal out cost ∧
      out.regs 47 = cap ∧ out.regs 14 = Nat.clog 2 (4 * M + 2) ∧ out.regs 92 = N ∧ out.regs 18 = 1 ∧ out.regs 99 = heap ∧
      out.mem = st.mem ∧
      (∀ r, r ∉ [14, 15, 16, 17, 18, 46, 47, 57, 99] → out.regs r = st.regs r) ∧
      cost ≤ 40 * (Nat.clog 2 (4 * M + 2) + Nat.clog 2 stretch) + 120 := by
  dsimp only
  intro hstretch hcap
  obtain ⟨ready, hr, h57, hN, hm, hf⟩ :=
    prepareInitBucketVertexLog_runs (w := w) (p := p) (ω := ω) h22 h92 (by omega) (by omega)
  obtain ⟨mid, c, hr', h47, hlog, h18, hh, hm', hf', hc⟩ :=
    initIntegerBucketStage_runs (ω := ω) hp
      ((hf 6 (by decide) (by decide) (by decide)).trans h6)
      ((hf 76 (by decide) (by decide) (by decide)).trans h76)
      ((hf 75 (by decide) (by decide) (by decide)).trans h75) hN
      ((hf 98 (by decide) (by decide) (by decide)).trans h98)
      (concreteChainParams M hM).hk hvertices hstretch hcap
  have hn : mid.regs 57 = N := (hf' 57 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)).trans h57
  let out := {mid with regs := Function.update mid.regs 92 N}
  have hout : Runs w p ω (.assign 92 (.reg 57)) mid .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hn], rfl, rfl, rfl⟩
  refine ⟨out, c + 14, ?_, by simpa [out] using h47, by simpa [out] using hlog, by simp [out],
    by simpa [out] using h18, by simpa [out] using hh, hm'.trans hm, ?_, by omega⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨ready, 10, c + 3, hr,
      runs_seq_iff.mpr (Or.inr ⟨mid, c, 2, hr', hout, rfl⟩), by omega⟩)
  · intro r h
    by_cases he : r = 92
    · subst r
      simp [out, h92]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
      simpa [out, he] using
        (hf' r h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.2.1
          h.2.2.2.2.2.2.2.2).trans
          (hf r h.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1 he)

end MinCostFlow.MinRatio
