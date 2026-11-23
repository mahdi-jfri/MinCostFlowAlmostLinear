module

public import MinCostFlow.MinRatio.InitMachineThresholds
import MinCostFlow.MinRatio.ShiftForestScan

/-!
# Linking the sparse-core rebuild threshold table

Combine the computed sparse-core growth terms and write the integer
thresholds used by the rebuild schedule.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM

/-- Install the integer rebuild table using one multiword rounding buffer. -/
@[expose] def initSparseCoreCoarseThresholdTable (shift round h : ℕ) : Stmt :=
  roundSparseCoreGrowth shift round h ;;
  stageMultiwordRebuildTable ;;
  reserveAndInitIntegerThresholdTable

/-- The selected coarse growth word yields the two rebuild budget bounds. -/
theorem initSparseCoreCoarseThresholdTable_runs
    (TP : Chain.SparseCoreParams) (C : Chain.ChainParams)
    {w h shift round addr limbs e heap P upper first scale vertices : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hshift : MeetsContract w p shift (Num.shiftLeftContract w h))
    (hround : MeetsContract w p round (initDepthEndpointContract w h))
    (h36 : st.regs 36 = first) (h30 : st.regs 30 = scale) (hfirst : first * scale < 2 ^ w)
    (ha : st.regs 117 = addr) (hL : st.regs 118 = limbs)
    (he : st.regs 119 = e) (hh : st.regs 115 = heap) (hP : st.regs 121 = P)
    (hw : 1 < 2 ^ w) (hword : h < 2 ^ w) (heword : e < 2 ^ w)
    (hdvd : h ∣ P) (heP : e ≤ P) (hfrac : P / h ≤ limbs)
    (hbelow : addr + limbs ≤ heap) (hv : Num.Valid st.mem addr h limbs)
    (hz : ZeroFrom st.mem heap) (hroom : heap + limbs < 2 ^ w)
    (hvalue : Num.intVal st.mem addr h limbs = (upper : ℤ))
    (hfit : Num.Fits h limbs ((upper : ℤ) * (2 : ℤ) ^ e))
    (hrounded : upper * 2 ^ e / 2 ^ P + 1 < 2 ^ w)
    (hTP : TP.Valid) (hγM : TP.γ_ℓ (C.M₀ ^ 2) ≤ C.M₀)
    (hγk : TP.γ_ℓ (C.M₀ ^ 2) ≤ C.k)
    (hbase : heap + limbs + C.d + 1 < 2 ^ w)
    (hscale : scale = 2 ^ e)
    (hlow : TP.γ_ℓ (C.M₀ ^ 2) ≤ max (first : ℝ) ((upper : ℝ) / ↑(scale * 2 ^ (P - e))))
    (hhigh : max (first : ℝ) ((upper : ℝ) / ↑(scale * 2 ^ (P - e))) + 1 / scale ≤
      TP.γ_ℓ (C.M₀ ^ 2) + 1 / ((C.d : ℝ) + 1))
    (h22 : st.regs 22 = C.M₀) (h14 : st.regs 14 = Nat.clog 2 (vertices + 2))
    (h76 : st.regs 76 = C.k) (h75 : st.regs 75 = C.d)
    (hden : 3 * C.k * Nat.clog 2 (vertices + 2) ^ 2 < 2 ^ w)
    (hcapacity : (3 * C.M₀ ^ 2 + 1) * (C.M₀ * (2 * scale) ^ (C.d + 1)) < 2 ^ w) :
    let a := max (first * scale) ((upper + 2 ^ (P - e) - 1) / 2 ^ (P - e))
    let base := heap + limbs
    ∃ out cost, Runs w p ω (initSparseCoreCoarseThresholdTable shift round h) st .normal out cost ∧
      out.regs 83 = base ∧ out.regs 98 = base + C.d + 1 ∧
      (∀ j ≤ C.d, out.mem (base + j) = Chain.concreteLevelRebuildCount C.M₀ C.k a scale j vertices ∧
        (out.mem (base + j) : ℝ) ≤ Chain.SparseCoreTool.updateThreshold C.k (Chain.levelM TP C j) vertices ∧
        Chain.SparseCoreTool.updateThreshold C.k (Chain.levelM TP C j) vertices ≤
          48 * ((out.mem (base + j) : ℝ) + 1)) ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (base + C.d + 1) ∧
      cost ≤ 60 * limbs + 50 * C.d + 191 := by
  dsimp only
  obtain ⟨mid, c, hr, h12, h120, hf, hz', hk, hc⟩ :=
    roundSparseCoreGrowth_runs (ω := ω) hshift hround h36 h30 hfirst ha hL he hh hP
      hw hword heword hdvd heP hfrac hbelow hv hz hroom hvalue hfit hrounded
  obtain ⟨ready, ht, h4, h77, hm, hk'⟩ :=
    stageMultiwordRebuildTable_runs (w := w) (p := p) (ω := ω)
      ((hk 30 (by decide) (by decide) (by decide)).trans h30) h120
  have hs : 0 < scale := hscale.symm ▸ Nat.two_pow_pos e
  have hx : ((first * scale : ℕ) : ℝ) / scale = first := by
    rw [Nat.cast_mul, mul_div_cancel_right₀]
    exact_mod_cast hs.ne'
  have hsReal : (0 : ℝ) < scale := Nat.cast_pos.mpr hs
  have heq (a b : ℕ) : (↑(max a b) : ℝ) / scale =
      max ((a : ℝ) / scale) ((b : ℝ) / scale) := by
    rcases le_total a b with hab | hab
    · rw [max_eq_right hab, max_eq_right]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hab) hsReal.le
    · rw [max_eq_left hab, max_eq_left]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hab) hsReal.le
  obtain ⟨hlo, hu⟩ := Chain.roundLevelGrowthUpper_bounds upper scale
    (2 ^ (P - e)) hs (Nat.two_pow_pos _)
  have hunit : 0 ≤ (1 : ℝ) / scale := by positivity
  have keep (r : ℕ) (hr₁ : r ≠ 4 := by decide) (hr₂ : r ≠ 77 := by decide)
      (hr₃ : r ≠ 12 := by decide) (hr₄ : r ≠ 120 := by decide)
      (hr₅ : r ≠ 122 := by decide) :=
    (hk' r hr₁ hr₂).trans (hk r hr₃ hr₄ hr₅)
  obtain ⟨out, hwrite, h83, h98, htable, hf', hzero⟩ :=
    initIntegerThresholdTable_fromCoarse_runs (ω := ω) TP C hw hbase (hm.symm ▸ hz')
      ((hk' 12 (by decide) (by decide)).trans h12) h4 hs hTP hγM hγk
      (by rw [heq, hx]; exact hlow.trans (max_le_max le_rfl hlo))
      (by rw [heq, hx]; apply max_le
          · exact (le_max_left _ _).trans ((le_add_of_nonneg_right hunit).trans hhigh)
          · exact hu.trans ((add_le_add_left (le_max_right _ _) _).trans hhigh)) ((keep 22).trans h22) ((keep 14).trans h14)
      h77 ((keep 76).trans h76) ((keep 75).trans h75) hden hcapacity
  refine ⟨out, c + 5 + (50 * C.d + 75) + 2, ?_, h83, h98, htable, ?_, hzero, by omega⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨mid, c, _, hr,
      runs_seq_iff.mpr (Or.inr ⟨ready, 5, _, ht, hwrite, rfl⟩), by omega⟩)
  · intro x hx
    exact (hf' x (by omega)).trans ((congrFun hm x).trans (hf x hx))

/-- The exact first term and bounded second term instantiate the
one-buffer table writer for the concrete sparse-core envelope. -/
theorem initConcreteSparseCoreCoarseThresholdTable_runs
    (E : SparseCore.SparseCoreEnv) (C : Chain.ChainParams)
    {w h shift round addr limbs e heap P upper first scale vertices : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hshift : MeetsContract w p shift (Num.shiftLeftContract w h))
    (hround : MeetsContract w p round (initDepthEndpointContract w h))
    (h36 : st.regs 36 = first) (h30 : st.regs 30 = scale) (hfirst : first * scale < 2 ^ w)
    (ha : st.regs 117 = addr) (hL : st.regs 118 = limbs)
    (he : st.regs 119 = e) (hh : st.regs 115 = heap) (hP : st.regs 121 = P)
    (hw : 1 < 2 ^ w) (hword : h < 2 ^ w) (heword : e < 2 ^ w)
    (hdvd : h ∣ P) (heP : e ≤ P) (hfrac : P / h ≤ limbs)
    (hbelow : addr + limbs ≤ heap) (hv : Num.Valid st.mem addr h limbs)
    (hz : ZeroFrom st.mem heap) (hroom : heap + limbs < 2 ^ w)
    (hvalue : Num.intVal st.mem addr h limbs = (upper : ℤ))
    (hfit : Num.Fits h limbs ((upper : ℤ) * (2 : ℤ) ^ e))
    (hrounded : upper * 2 ^ e / 2 ^ P + 1 < 2 ^ w)
    (hγM : (SparseCore.sparseCoreParams E).γ_ℓ (C.M₀ ^ 2) ≤ C.M₀)
    (hγk : (SparseCore.sparseCoreParams E).γ_ℓ (C.M₀ ^ 2) ≤ C.k)
    (hbase : heap + limbs + C.d + 1 < 2 ^ w)
    (hscale : scale = 2 ^ e)
    {growth productUpper : ℕ} {error : ℝ}
    (hGrowth : (E.P_fn (C.M₀ ^ 2)).γ_ℓ = growth)
    (hfirstEq : first = 3 ^ E.L * growth ^ (E.L + 1))
    (hsecondEq : upper = 11 * (E.L + 1) * growth * E.B_fn (C.M₀ ^ 2) *
      (2 * E.d_fn (C.M₀ ^ 2) + 190) * productUpper + (11 * 115) * 2 ^ P)
    (hloProduct : (E.P_fn (C.M₀ ^ 2)).K_s *
      SparseCore.coreLambdaS (E.P_fn (C.M₀ ^ 2)) (C.M₀ ^ 2) ≤
        (productUpper : ℝ) / (2 : ℝ) ^ P)
    (hhiProduct : (productUpper : ℝ) / (2 : ℝ) ^ P -
      (E.P_fn (C.M₀ ^ 2)).K_s * SparseCore.coreLambdaS (E.P_fn (C.M₀ ^ 2)) (C.M₀ ^ 2) ≤ error)
    (hcoarse : 1 / (scale : ℝ) ≤ 1 / ((C.d : ℝ) + 1))
    (hfine : ((11 * (E.L + 1) * growth * E.B_fn (C.M₀ ^ 2) *
      (2 * E.d_fn (C.M₀ ^ 2) + 190) : ℕ) : ℝ) * error + 1 / (scale : ℝ) ≤
        1 / ((C.d : ℝ) + 1))
    (h22 : st.regs 22 = C.M₀) (h14 : st.regs 14 = Nat.clog 2 (vertices + 2))
    (h76 : st.regs 76 = C.k) (h75 : st.regs 75 = C.d)
    (hden : 3 * C.k * Nat.clog 2 (vertices + 2) ^ 2 < 2 ^ w)
    (hcapacity : (3 * C.M₀ ^ 2 + 1) * (C.M₀ * (2 * scale) ^ (C.d + 1)) < 2 ^ w) :
    let a := max (first * scale) ((upper + 2 ^ (P - e) - 1) / 2 ^ (P - e))
    let base := heap + limbs
    ∃ out cost, Runs w p ω (initSparseCoreCoarseThresholdTable shift round h) st .normal out cost ∧
      out.regs 83 = base ∧ out.regs 98 = base + C.d + 1 ∧
      (∀ j ≤ C.d, out.mem (base + j) = Chain.concreteLevelRebuildCount C.M₀ C.k a scale j vertices ∧
        (out.mem (base + j) : ℝ) ≤ Chain.SparseCoreTool.updateThreshold C.k (Chain.levelM (SparseCore.sparseCoreParams E) C j) vertices ∧
        Chain.SparseCoreTool.updateThreshold C.k (Chain.levelM (SparseCore.sparseCoreParams E) C j) vertices ≤
          48 * ((out.mem (base + j) : ℝ) + 1)) ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (base + C.d + 1) ∧
      cost ≤ 60 * limbs + 50 * C.d + 191 := by
  obtain ⟨hlow, hhigh⟩ := initSparseCoreCoarseGrowth_bounds E (C.M₀ ^ 2) C.d growth
    productUpper P scale e hscale heP hGrowth hloProduct hhiProduct hcoarse hfine
  rw [← hfirstEq, ← hsecondEq] at hlow hhigh
  exact initSparseCoreCoarseThresholdTable_runs (SparseCore.sparseCoreParams E) C
    hshift hround h36 h30 hfirst ha hL he hh hP hw hword heword hdvd heP hfrac
    hbelow hv hz hroom hvalue hfit hrounded (SparseCore.sparseCoreParams_valid E)
    hγM hγk hbase hscale hlow hhigh h22 h14 h76 h75 hden hcapacity

/-- Compute the affine numerator and write the rebuild table. -/
@[expose] def initSparseCoreThresholdsFromProduct (load extend mul shift add round h : ℕ) : Stmt :=
  initSparseCoreSecondNumerator load extend mul shift add ;;
  initSparseCoreCoarseThresholdTable shift round h

/-- The affine calculation and threshold writer share the same
precision and preserve the allocations preceding the coefficient product. -/
theorem initSparseCoreThresholdsFromProduct_runs
    (E : SparseCore.SparseCoreEnv) (C : Chain.ChainParams)
    {w h load extend mul shift add heap limbs factor source P round e first scale vertices upper : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hext : MeetsContract w p extend (Num.extendCopyContract w h))
    (hmul : MeetsContract w p mul (Num.multiplyContract w h))
    (hshift : MeetsContract w p shift (Num.shiftLeftContract w h))
    (hadd : MeetsContract w p add (Num.addContract w h))
    (h121 : st.regs 121 = P)
    (h99 : st.regs 99 = heap) (h67 : st.regs 67 = limbs) (h37 : st.regs 37 = factor)
    (h112 : st.regs 112 = source) (h111 : st.regs 111 = 2 * limbs)
    (hword : factor < 2 ^ w) (hbelow : source + 2 * limbs ≤ heap)
    (hv : Num.Valid st.mem source h (2 * limbs)) (hz : ZeroFrom st.mem heap)
    (hfit : 2 * factor < Num.capacity h limbs)
    (hroom : heap + 27 * limbs < 2 ^ w)
    (hcword : 1265 < 2 ^ w) (hPword : P < 2 ^ w)
    (hcfit : 2 * 1265 < Num.capacity h (4 * limbs))
    (hshiftFit : Num.Fits h (4 * limbs) (1265 * (2 : ℤ) ^ P))
    (hsum : Num.Fits h (4 * limbs)
      (Num.intVal st.mem source h (2 * limbs) * (factor : ℤ) + 1265 * (2 : ℤ) ^ P))
    (hround : MeetsContract w p round (initDepthEndpointContract w h))
    (h36 : st.regs 36 = first) (h30 : st.regs 30 = scale) (hfirst : first * scale < 2 ^ w)
    (he : st.regs 119 = e) (hwordH : h < 2 ^ w) (heword : e < 2 ^ w)
    (hdvd : h ∣ P) (heP : e ≤ P) (hfrac : P / h ≤ 4 * limbs)
    (hshiftUpper : Num.Fits h (4 * limbs) ((upper : ℤ) * (2 : ℤ) ^ e))
    (hrounded : upper * 2 ^ e / 2 ^ P + 1 < 2 ^ w)
    (hγM : (SparseCore.sparseCoreParams E).γ_ℓ (C.M₀ ^ 2) ≤ C.M₀)
    (hγk : (SparseCore.sparseCoreParams E).γ_ℓ (C.M₀ ^ 2) ≤ C.k)
    (hbase : heap + 31 * limbs + C.d + 1 < 2 ^ w)
    (hscale : scale = 2 ^ e)
    {growth productUpper : ℕ} {error : ℝ}
    (hproduct : Num.intVal st.mem source h (2 * limbs) = (productUpper : ℤ))
    (hfactor : factor = 11 * (E.L + 1) * growth * E.B_fn (C.M₀ ^ 2) *
      (2 * E.d_fn (C.M₀ ^ 2) + 190))
    (hGrowth : (E.P_fn (C.M₀ ^ 2)).γ_ℓ = growth)
    (hfirstEq : first = 3 ^ E.L * growth ^ (E.L + 1))
    (hsecondEq : upper = 11 * (E.L + 1) * growth * E.B_fn (C.M₀ ^ 2) *
      (2 * E.d_fn (C.M₀ ^ 2) + 190) * productUpper + (11 * 115) * 2 ^ P)
    (hloProduct : (E.P_fn (C.M₀ ^ 2)).K_s *
      SparseCore.coreLambdaS (E.P_fn (C.M₀ ^ 2)) (C.M₀ ^ 2) ≤
        (productUpper : ℝ) / (2 : ℝ) ^ P)
    (hhiProduct : (productUpper : ℝ) / (2 : ℝ) ^ P -
      (E.P_fn (C.M₀ ^ 2)).K_s * SparseCore.coreLambdaS (E.P_fn (C.M₀ ^ 2)) (C.M₀ ^ 2) ≤ error)
    (hcoarse : 1 / (scale : ℝ) ≤ 1 / ((C.d : ℝ) + 1))
    (hfine : ((11 * (E.L + 1) * growth * E.B_fn (C.M₀ ^ 2) *
      (2 * E.d_fn (C.M₀ ^ 2) + 190) : ℕ) : ℝ) * error + 1 / (scale : ℝ) ≤
        1 / ((C.d : ℝ) + 1))
    (h22 : st.regs 22 = C.M₀) (h14 : st.regs 14 = Nat.clog 2 (vertices + 2))
    (h76 : st.regs 76 = C.k) (h75 : st.regs 75 = C.d)
    (hden : 3 * C.k * Nat.clog 2 (vertices + 2) ^ 2 < 2 ^ w)
    (hcapacity : (3 * C.M₀ ^ 2 + 1) * (C.M₀ * (2 * scale) ^ (C.d + 1)) < 2 ^ w) :
    let a := max (first * scale) ((upper + 2 ^ (P - e) - 1) / 2 ^ (P - e))
    let base := heap + 31 * limbs
    ∃ out cost, Runs w p ω (initSparseCoreThresholdsFromProduct load extend mul shift add round h)
        st .normal out cost ∧
      out.regs 83 = base ∧ out.regs 98 = base + C.d + 1 ∧
      (∀ j ≤ C.d, out.mem (base + j) = Chain.concreteLevelRebuildCount C.M₀ C.k a scale j vertices ∧
        (out.mem (base + j) : ℝ) ≤ Chain.SparseCoreTool.updateThreshold C.k (Chain.levelM (SparseCore.sparseCoreParams E) C j) vertices ∧
        Chain.SparseCoreTool.updateThreshold C.k (Chain.levelM (SparseCore.sparseCoreParams E) C j) vertices ≤
          48 * ((out.mem (base + j) : ℝ) + 1)) ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (base + C.d + 1) ∧
      cost ≤ (4 * limbs) * (38 * (4 * limbs) + 35) + 947 * limbs + 50 * C.d + 412 := by
  dsimp only
  have hvalue : Num.intVal st.mem source h (2 * limbs) * (factor : ℤ) +
      1265 * (2 : ℤ) ^ P = (upper : ℤ) := by
    rw [hproduct, hsecondEq, ← hfactor]
    push_cast
    ring
  obtain ⟨mid, c, hr, ha, hh, hL, hv', hi, hf, hz', hk, hc⟩ :=
    initSparseCoreSecondNumerator_runs (ω := ω) hload hext hmul hshift hadd
      h121 h99 h67 h37 h112 h111 hword hbelow hv hz hfit hroom hcword hPword hcfit hshiftFit hsum
  have keep (r : ℕ) (hr : r ∉ ([108, 114, 115, 116, 117, 118] : List ℕ) := by decide) :=
    hk r hr
  have hcursor : heap + 27 * limbs + 4 * limbs = heap + 31 * limbs := by omega
  obtain ⟨out, d, ht, h83, h98, htable, hf', hz'', hd⟩ :=
    initConcreteSparseCoreCoarseThresholdTable_runs (ω := ω) E C hshift hround
      ((keep 36).trans h36) ((keep 30).trans h30) hfirst ha hL ((keep 119).trans he)
      hh ((keep 121).trans h121) (by omega) hwordH heword hdvd heP hfrac
      (by omega) hv' hz' (by omega) (hi.trans hvalue) hshiftUpper hrounded
      hγM hγk (by omega) hscale hGrowth hfirstEq hsecondEq hloProduct hhiProduct hcoarse hfine ((keep 22).trans h22) ((keep 14).trans h14)
      ((keep 76).trans h76) ((keep 75).trans h75) hden hcapacity
  rw [hcursor] at h83 h98 htable hz''
  exact ⟨out, c + d + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c, d, hr, ht, rfl⟩),
    h83, h98, htable, fun x hx => (hf' x (by omega)).trans (hf x hx), hz'', by omega⟩

/-- Compute the growth words and build the thresholds from the
coefficient product and sparsifier length. -/
@[expose] def initSparseCoreThresholdsFromSparsifier (power load extend mul shift add round h : ℕ) : Stmt :=
  initSparseCoreGrowthWords power ;;
  initSparseCoreThresholdsFromProduct load extend mul shift add round h

/-- The runtime sparsifier output supplies both words used by the table writer. -/
theorem initSparseCoreThresholdsFromSparsifier_runs
    (E : SparseCore.SparseCoreEnv) (C : Chain.ChainParams)
    {w power depth buckets degree growthScale h load extend mul shift add heap limbs factor source P round e first scale vertices upper : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hpower : MeetsContract w p power (initStretchPowerContract w))
    (h44 : st.regs 44 = depth) (hDepth : depth = E.L)
    (h47 : st.regs 47 = buckets) (hBuckets : buckets = E.B_fn (C.M₀ ^ 2))
    (h48 : st.regs 48 = degree) (hDegree : degree = E.d_fn (C.M₀ ^ 2))
    (h4 : st.regs 4 = growthScale) (hGrowthScale : 0 < growthScale)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hext : MeetsContract w p extend (Num.extendCopyContract w h))
    (hmul : MeetsContract w p mul (Num.multiplyContract w h))
    (hshift : MeetsContract w p shift (Num.shiftLeftContract w h))
    (hadd : MeetsContract w p add (Num.addContract w h))
    (h121 : st.regs 121 = P)
    (h99 : st.regs 99 = heap) (h67 : st.regs 67 = limbs)
    (h112 : st.regs 112 = source) (h111 : st.regs 111 = 2 * limbs)
    (hword : factor < 2 ^ w) (hbelow : source + 2 * limbs ≤ heap)
    (hv : Num.Valid st.mem source h (2 * limbs)) (hz : ZeroFrom st.mem heap)
    (hfit : 2 * factor < Num.capacity h limbs)
    (hcword : 1265 < 2 ^ w) (hPword : P < 2 ^ w)
    (hcfit : 2 * 1265 < Num.capacity h (4 * limbs))
    (hshiftFit : Num.Fits h (4 * limbs) (1265 * (2 : ℤ) ^ P))
    (hsum : Num.Fits h (4 * limbs)
      (Num.intVal st.mem source h (2 * limbs) * (factor : ℤ) + 1265 * (2 : ℤ) ^ P))
    (hround : MeetsContract w p round (initDepthEndpointContract w h))
     (h30 : st.regs 30 = scale) (hfirst : first * scale < 2 ^ w)
    (he : st.regs 119 = e) (hwordH : h < 2 ^ w) (heword : e < 2 ^ w)
    (hdvd : h ∣ P) (heP : e ≤ P) (hfrac : P / h ≤ 4 * limbs)
    (hshiftUpper : Num.Fits h (4 * limbs) ((upper : ℤ) * (2 : ℤ) ^ e))
    (hrounded : upper * 2 ^ e / 2 ^ P + 1 < 2 ^ w)
    (hγM : (SparseCore.sparseCoreParams E).γ_ℓ (C.M₀ ^ 2) ≤ C.M₀)
    (hγk : (SparseCore.sparseCoreParams E).γ_ℓ (C.M₀ ^ 2) ≤ C.k)
    (hbase : heap + 31 * limbs + C.d + 1 < 2 ^ w)
    (hscale : scale = 2 ^ e)
    {growth productUpper : ℕ} {error : ℝ}
    (hproduct : Num.intVal st.mem source h (2 * limbs) = (productUpper : ℤ))
    (hfactor : factor = 11 * (E.L + 1) * growth * E.B_fn (C.M₀ ^ 2) *
      (2 * E.d_fn (C.M₀ ^ 2) + 190))
    (hGrowth : (E.P_fn (C.M₀ ^ 2)).γ_ℓ = growth)
    (h50 : st.regs 50 = growthScale * growth) (hg : 0 < growth)
    (hb : 0 < buckets) (hDepthWord : max (depth + 1) 3 < 2 ^ w)
    (hScaled : growthScale * growth < 2 ^ w)
    (hfirstEq : first = 3 ^ E.L * growth ^ (E.L + 1))
    (hsecondEq : upper = 11 * (E.L + 1) * growth * E.B_fn (C.M₀ ^ 2) *
      (2 * E.d_fn (C.M₀ ^ 2) + 190) * productUpper + (11 * 115) * 2 ^ P)
    (hloProduct : (E.P_fn (C.M₀ ^ 2)).K_s *
      SparseCore.coreLambdaS (E.P_fn (C.M₀ ^ 2)) (C.M₀ ^ 2) ≤
        (productUpper : ℝ) / (2 : ℝ) ^ P)
    (hhiProduct : (productUpper : ℝ) / (2 : ℝ) ^ P -
      (E.P_fn (C.M₀ ^ 2)).K_s * SparseCore.coreLambdaS (E.P_fn (C.M₀ ^ 2)) (C.M₀ ^ 2) ≤ error)
    (hcoarse : 1 / (scale : ℝ) ≤ 1 / ((C.d : ℝ) + 1))
    (hfine : ((11 * (E.L + 1) * growth * E.B_fn (C.M₀ ^ 2) *
      (2 * E.d_fn (C.M₀ ^ 2) + 190) : ℕ) : ℝ) * error + 1 / (scale : ℝ) ≤
        1 / ((C.d : ℝ) + 1))
    (h22 : st.regs 22 = C.M₀) (h14 : st.regs 14 = Nat.clog 2 (vertices + 2))
    (h76 : st.regs 76 = C.k) (h75 : st.regs 75 = C.d)
    (hden : 3 * C.k * Nat.clog 2 (vertices + 2) ^ 2 < 2 ^ w)
    (hcapacity : (3 * C.M₀ ^ 2 + 1) * (C.M₀ * (2 * scale) ^ (C.d + 1)) < 2 ^ w) :
    let a := max (first * scale) ((upper + 2 ^ (P - e) - 1) / 2 ^ (P - e))
    let base := heap + 31 * limbs
    ∃ out cost, Runs w p ω (initSparseCoreThresholdsFromSparsifier power load extend mul shift add round h)
        st .normal out cost ∧
      out.regs 83 = base ∧ out.regs 98 = base + C.d + 1 ∧
      (∀ j ≤ C.d, out.mem (base + j) = Chain.concreteLevelRebuildCount C.M₀ C.k a scale j vertices ∧
        (out.mem (base + j) : ℝ) ≤ Chain.SparseCoreTool.updateThreshold C.k (Chain.levelM (SparseCore.sparseCoreParams E) C j) vertices ∧
        Chain.SparseCoreTool.updateThreshold C.k (Chain.levelM (SparseCore.sparseCoreParams E) C j) vertices ≤
          48 * ((out.mem (base + j) : ℝ) + 1)) ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (base + C.d + 1) ∧
      cost ≤ (4 * limbs) * (38 * (4 * limbs) + 35) + 947 * limbs + 50 * C.d + 492 + 40 * depth := by
  dsimp only
  have hfirstFit : 3 ^ depth * growth ^ (depth + 1) < 2 ^ w := by
    rw [hDepth]
    rw [← hfirstEq]
    exact (Nat.le_mul_of_pos_right first (hscale.symm ▸ Nat.two_pow_pos e)).trans_lt hfirst
  have hfactorEq : 11 * ((depth + 1) * buckets * (2 * degree + 190)) * growth = factor := by
    rw [hDepth, hBuckets, hDegree, hfactor]
    ac_rfl
  obtain ⟨mid, c, hr, _, h36, h37, hm, hk, hc⟩ :=
    initSparseCoreGrowthWords_runs (ω := ω) hpower h44 h50 h4 hGrowthScale hg hDepthWord
      hScaled hfirstFit h47 h48 hb (by omega) (hfactorEq.symm ▸ hword)
  have keep (r : ℕ) (hr : r ∉ ([33, 34, 35, 36, 37, 38, 45] : List ℕ) := by decide) :=
    hk r hr
  have h36' : mid.regs 36 = first := by rwa [hDepth, ← hfirstEq] at h36
  have h37' : mid.regs 37 = factor := by
    rw [h37, ← hfactorEq]
    ac_rfl
  obtain ⟨out, d, ht, h83, h98, htable, hf, hz', hd⟩ :=
    initSparseCoreThresholdsFromProduct_runs (ω := ω) E C hload hext hmul hshift hadd
      ((keep 121).trans h121) ((keep 99).trans h99) ((keep 67).trans h67) h37'
      ((keep 112).trans h112) ((keep 111).trans h111) hword hbelow (hm.symm ▸ hv)
      (hm.symm ▸ hz) hfit (by omega) hcword hPword hcfit hshiftFit (hm.symm ▸ hsum)
      hround h36' ((keep 30).trans h30) hfirst ((keep 119).trans he)
      hwordH heword hdvd heP hfrac hshiftUpper hrounded hγM hγk hbase hscale
      (hm.symm ▸ hproduct) hfactor hGrowth hfirstEq hsecondEq hloProduct hhiProduct hcoarse hfine
      ((keep 22).trans h22) ((keep 14).trans h14) ((keep 76).trans h76) ((keep 75).trans h75) hden hcapacity
  exact ⟨out, c + d + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c, d, hr, ht, rfl⟩),
    h83, h98, htable, fun x hx => (hf x hx).trans (congrFun hm x), hz', by omega⟩

/-- Bound the coefficient product using the two scaled interval widths
from the sparsifier coefficient and logarithmic factor calculations. -/
theorem initSparseCoreCoefficientProduct_bounds
    {coefficient logarithm : ℝ} {kl ku ll lu scale : ℕ}
    (hkl : (kl : ℝ) / scale ≤ coefficient) (hku : coefficient ≤ (ku : ℝ) / scale)
    (hll : (ll : ℝ) / scale ≤ logarithm) (hlu : logarithm ≤ (lu : ℝ) / scale) :
    coefficient * logarithm ≤ ((ku * lu : ℕ) : ℝ) / (scale : ℝ) ^ 2 ∧
      ((ku * lu : ℕ) : ℝ) / (scale : ℝ) ^ 2 - coefficient * logarithm ≤
        ((ku : ℝ) / scale - (kl : ℝ) / scale) * ((lu : ℝ) / scale) +
          coefficient * ((lu : ℝ) / scale - (ll : ℝ) / scale) := by
  have hk : 0 ≤ coefficient := (by positivity : 0 ≤ (kl : ℝ) / scale).trans hkl
  have hl : 0 ≤ logarithm := (by positivity : 0 ≤ (ll : ℝ) / scale).trans hll
  have hprod : ((ku * lu : ℕ) : ℝ) / (scale : ℝ) ^ 2 =
      ((ku : ℝ) / scale) * ((lu : ℝ) / scale) := by
    rw [Nat.cast_mul, div_mul_div_comm, pow_two]
  rw [hprod]
  obtain ⟨hlo, hhi⟩ := rebuildLogFactorProduct_error hk hl hku hlu
    (sub_le_sub_left hkl _) (sub_le_sub_left hll _)
  exact ⟨sub_nonneg.mp hlo, hhi⟩

/-- Bound the product error by integer endpoint gaps at the shared
scale. These gaps can be checked before writing the rebuild table. -/
theorem initSparseCoreCoefficientProduct_gap
    {coefficient logarithm : ℝ} {kl ku ll lu scale : ℕ}
    (hs : 0 < scale) (hk : kl ≤ ku) (hl : ll ≤ lu)
    (hkl : (kl : ℝ) / scale ≤ coefficient) (hku : coefficient ≤ (ku : ℝ) / scale)
    (hll : (ll : ℝ) / scale ≤ logarithm) (hlu : logarithm ≤ (lu : ℝ) / scale) :
    ((ku * lu : ℕ) : ℝ) / (scale : ℝ) ^ 2 - coefficient * logarithm ≤
      ((((ku - kl) * lu + ku * (lu - ll) : ℕ) : ℝ)) / (scale : ℝ) ^ 2 := by
  obtain ⟨_, hhi⟩ := initSparseCoreCoefficientProduct_bounds hkl hku hll hlu
  have hgap : 0 ≤ (lu : ℝ) / scale - (ll : ℝ) / scale := by
    apply sub_nonneg.mpr
    exact div_le_div_of_nonneg_right (by exact_mod_cast hl) (by positivity)
  refine hhi.trans ((add_le_add_right (mul_le_mul_of_nonneg_right hku hgap) _).trans_eq ?_)
  push_cast [Nat.cast_sub hk, Nat.cast_sub hl]
  have hs' : (scale : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  field_simp

/-- A dyadic working scale with enough room for the weighted endpoint
gap leaves half of the rebuild budget available for coarse rounding. -/
theorem initSparseCoreCoefficientGap_budget
    {gap factor scale coarse d : ℕ}
    (hs : 0 < scale)
    (hFine : 2 * (d + 1) * factor * gap ≤ scale ^ 2)
    (hCoarse : 2 * (d + 1) ≤ coarse) :
    (factor : ℝ) * ((gap : ℝ) / (scale : ℝ) ^ 2) + 1 / (coarse : ℝ) ≤
      1 / ((d : ℝ) + 1) := by
  have hd : 0 < 2 * ((d : ℝ) + 1) := by positivity
  have hc : 0 < (coarse : ℝ) := by exact_mod_cast (show 0 < coarse by omega)
  have hs' : 0 < (scale : ℝ) ^ 2 := by positivity
  have hf : (factor : ℝ) * ((gap : ℝ) / (scale : ℝ) ^ 2) ≤
      1 / (2 * ((d : ℝ) + 1)) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hs' hd).mpr
    have he : 2 * ((d : ℝ) + 1) * factor * gap ≤ (scale : ℝ) ^ 2 := by
      exact_mod_cast hFine
    nlinarith only [he]
  have hcr : 1 / (coarse : ℝ) ≤ 1 / (2 * ((d : ℝ) + 1)) :=
    one_div_le_one_div_of_le hd (by exact_mod_cast hCoarse)
  refine (add_le_add hf hcr).trans_eq ?_
  field_simp
  ring

/-- Encode an upper endpoint in a signed limb block. -/
@[expose] def loadSparseCoreCoefficientEndpoint (load source width cursor next : ℕ) : Stmt :=
  .call next load [.reg source, .reg width, .reg cursor]

/-- Allocate a fitting upper endpoint while preserving earlier blocks. -/
theorem loadSparseCoreCoefficientEndpoint_runs
    {w h load source width cursor next heap limbs factor : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (h99 : st.regs cursor = heap) (h67 : st.regs width = limbs)
    (h37 : st.regs source = factor)
    (hword : factor < 2 ^ w) (hroom : heap + limbs < 2 ^ w)
    (hz : ZeroFrom st.mem heap) (hfit : 2 * factor < Num.capacity h limbs) :
    ∃ out cost, Runs w p ω (loadSparseCoreCoefficientEndpoint load source width cursor next) st .normal out cost ∧
      out.regs next = heap + limbs ∧ Num.Valid out.mem heap h limbs ∧
      Num.intVal out.mem heap h limbs = (factor : ℤ) ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (heap + limbs) ∧
      (∀ r, r ≠ next → out.regs r = st.regs r) ∧ cost ≤ 23 * limbs + 10 := by
  have hargs : evalArgs w st [.reg source, .reg width, .reg cursor] = some [factor, limbs, heap] := by
    simp [evalArgs, Expr.eval, h37, h67, h99]
  have hpre : (Num.loadSmallContract w h).pre [factor, limbs, heap] st.mem :=
    ⟨⟨factor, limbs, heap, rfl⟩, hz, hroom⟩
  obtain ⟨out, cost, ret, hr, hp, hv, hf, hc⟩ :=
    runs_call_of_meetsContract (r := next) hload hargs (by wram_words) hpre ω
  change ret = heap + limbs ∧ heap ≤ ret ∧ ret ≤ heap + limbs ∧
    (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem ret ∧
    ListAt out.mem heap (Num.digits h limbs factor) at hp
  obtain ⟨heq, _, _, hframe, hzero, hdigits⟩ := hp
  obtain ⟨hvalid, hu, _⟩ := Num.loadSmall_value hdigits
  have hsmall : factor < Num.capacity h limbs := by omega
  have hi : Num.intVal out.mem heap h limbs = (factor : ℤ) := by
    rw [Num.intVal, hu, Nat.mod_eq_of_lt hsmall, Num.signedVal, ite_eq_right (not_le_of_gt hfit), sub_zero]
  exact ⟨out, cost, hr, hv.trans heq, hvalid, hi, hframe, heq ▸ hzero, hf, by simp [Num.loadSmallContract, heapContract, argsSize, Expr.size] at hc; omega⟩

/-- Allocate adjacent blocks for the coefficient and logarithm upper endpoints. -/
@[expose] def loadSparseCoreCoefficientPair (load : ℕ) : Stmt :=
  loadSparseCoreCoefficientEndpoint load 51 67 99 108 ;;
  loadSparseCoreCoefficientEndpoint load 27 67 108 114

/-- The endpoint blocks preserve their exact word numerators. -/
theorem loadSparseCoreCoefficientPair_runs
    {w h load heap limbs ku lu : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (h99 : st.regs 99 = heap) (h67 : st.regs 67 = limbs)
    (h51 : st.regs 51 = ku) (h27 : st.regs 27 = lu)
    (hku : ku < 2 ^ w) (hlu : lu < 2 ^ w)
    (hfitK : 2 * ku < Num.capacity h limbs) (hfitL : 2 * lu < Num.capacity h limbs)
    (hz : ZeroFrom st.mem heap) (hroom : heap + limbs + limbs < 2 ^ w) :
    ∃ out cost, Runs w p ω (loadSparseCoreCoefficientPair load) st .normal out cost ∧
      out.regs 108 = heap + limbs ∧ out.regs 114 = heap + limbs + limbs ∧
      Num.Valid out.mem heap h limbs ∧ Num.Valid out.mem (heap + limbs) h limbs ∧
      Num.intVal out.mem heap h limbs = (ku : ℤ) ∧
      Num.intVal out.mem (heap + limbs) h limbs = (lu : ℤ) ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (heap + limbs + limbs) ∧
      (∀ r, r ≠ 108 → r ≠ 114 → out.regs r = st.regs r) ∧ cost ≤ 46 * limbs + 21 := by
  obtain ⟨mid, c, hr, h108, hv, hi, hf, hz', hk, hc⟩ :=
    loadSparseCoreCoefficientEndpoint_runs (ω := ω) (next := 108)
      hload h99 h67 h51 hku (by omega) hz hfitK
  obtain ⟨out, d, ht, h114, hv', hi', hf', hz'', hk', hd⟩ :=
    loadSparseCoreCoefficientEndpoint_runs (ω := ω) (next := 114)
      hload h108 ((hk 67 (by decide)).trans h67) ((hk 27 (by decide)).trans h27)
      hlu hroom hz' hfitL
  have hblock (j : ℕ) (hj : j < limbs) : out.mem (heap + j) = mid.mem (heap + j) :=
    hf' _ (by omega)
  exact ⟨out, c + d + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c, d, hr, ht, rfl⟩),
    (hk' 108 (by decide)).trans h108, h114,
    fun j hj => (hblock j hj).symm ▸ hv j hj, hv',
    (Num.intVal_congr hblock).trans hi, hi',
    fun x hx => (hf' x (by omega)).trans (hf x hx), hz'',
    fun r h108r h114r => (hk' r h114r).trans (hk r h108r), by omega⟩

/-- Multiply the two upper endpoints at their common limb width. -/
@[expose] def multiplySparseCoreCoefficientPair (mul : ℕ) : Stmt :=
  .call 115 mul [.reg 99, .reg 108, .reg 67, .reg 114]

/-- The exact numerator occupies twice the width of either input. -/
theorem multiplySparseCoreCoefficientPair_runs
    {w h mul heap limbs ku lu : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hmul : MeetsContract w p mul (Num.multiplyContract w h))
    (h99 : st.regs 99 = heap) (h108 : st.regs 108 = heap + limbs)
    (h67 : st.regs 67 = limbs) (h114 : st.regs 114 = heap + limbs + limbs)
    (hvK : Num.Valid st.mem heap h limbs) (hvL : Num.Valid st.mem (heap + limbs) h limbs)
    (hiK : Num.intVal st.mem heap h limbs = (ku : ℤ))
    (hiL : Num.intVal st.mem (heap + limbs) h limbs = (lu : ℤ))
    (hz : ZeroFrom st.mem (heap + limbs + limbs)) (hroom : heap + 8 * limbs < 2 ^ w) :
    ∃ out cost, Runs w p ω (multiplySparseCoreCoefficientPair mul) st .normal out cost ∧
      out.regs 115 = heap + 8 * limbs ∧ Num.Valid out.mem (heap + 6 * limbs) h (2 * limbs) ∧
      Num.intVal out.mem (heap + 6 * limbs) h (2 * limbs) = ((ku * lu : ℕ) : ℤ) ∧
      (∀ x < heap + limbs + limbs, out.mem x = st.mem x) ∧ ZeroFrom out.mem (heap + 8 * limbs) ∧
      (∀ r ≠ 115, out.regs r = st.regs r) ∧
      cost ≤ (2 * limbs) * (38 * (2 * limbs) + 35) + 120 * limbs + 104 := by
  let args := [heap, heap + limbs, limbs, heap + limbs + limbs]
  have he : evalArgs w st [.reg 99, .reg 108, .reg 67, .reg 114] = some args := by
    simp [args, evalArgs, Expr.eval, h99, h108, h67, h114]
  have hp : (Num.multiplyContract w h).pre args st.mem :=
    ⟨⟨heap, heap + limbs, limbs, heap + limbs + limbs, rfl, by omega, le_rfl, hvK, hvL⟩,
      hz, by change heap + limbs + limbs + 6 * limbs < 2 ^ w; omega⟩
  obtain ⟨out, cost, ret, hr, hpost, hret, hk, hc⟩ :=
    runs_call_of_meetsContract (r := 115) hmul he (by dsimp [args]; wram_words) hp ω
  change ret = heap + limbs + limbs + 6 * limbs ∧ _ ∧ _ ∧ _ ∧ _ ∧
    Num.Valid out.mem (heap + limbs + limbs + 4 * limbs) h (2 * limbs) ∧ _ at hpost
  obtain ⟨heq, _, _, hf, hzero, hv, hi⟩ := hpost
  have haddr : heap + limbs + limbs + 4 * limbs = heap + 6 * limbs := by omega
  have hcursor : heap + limbs + limbs + 6 * limbs = heap + 8 * limbs := by omega
  change Num.intVal out.mem (heap + limbs + limbs + 4 * limbs) h (2 * limbs) =
    Num.intVal st.mem heap h limbs * Num.intVal st.mem (heap + limbs) h limbs at hi
  rw [haddr, hiK, hiL, ← Int.natCast_mul] at hi
  refine ⟨out, cost, hr, hret.trans (heq.trans hcursor), haddr ▸ hv, hi, hf,
    (heq.trans hcursor) ▸ hzero, hk, ?_⟩
  simp [Num.multiplyContract, heapContract, args, argsSize, Expr.size] at hc
  omega

/-- Encode the upper endpoint words and multiply their numerators. -/
@[expose] def initSparseCoreCoefficientProduct (load mul : ℕ) : Stmt :=
  loadSparseCoreCoefficientPair load ;; multiplySparseCoreCoefficientPair mul

/-- The computed block stores the exact numerator at the sum of the
two input precisions. The earlier Init allocations are preserved. -/
theorem initSparseCoreCoefficientProduct_runs
    {w h load mul heap limbs ku lu : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hmul : MeetsContract w p mul (Num.multiplyContract w h))
    (h99 : st.regs 99 = heap) (h67 : st.regs 67 = limbs)
    (h51 : st.regs 51 = ku) (h27 : st.regs 27 = lu)
    (hku : ku < 2 ^ w) (hlu : lu < 2 ^ w)
    (hfitK : 2 * ku < Num.capacity h limbs) (hfitL : 2 * lu < Num.capacity h limbs)
    (hz : ZeroFrom st.mem heap) (hroom : heap + 8 * limbs < 2 ^ w) :
    ∃ out cost, Runs w p ω (initSparseCoreCoefficientProduct load mul) st .normal out cost ∧
      out.regs 115 = heap + 8 * limbs ∧ Num.Valid out.mem (heap + 6 * limbs) h (2 * limbs) ∧
      Num.intVal out.mem (heap + 6 * limbs) h (2 * limbs) = ((ku * lu : ℕ) : ℤ) ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (heap + 8 * limbs) ∧
      (∀ r, r ≠ 108 → r ≠ 114 → r ≠ 115 → out.regs r = st.regs r) ∧
      cost ≤ (2 * limbs) * (38 * (2 * limbs) + 35) + 166 * limbs + 126 := by
  obtain ⟨mid, c, hr, h108, h114, hvK, hvL, hiK, hiL, hf, hz', hk, hc⟩ :=
    loadSparseCoreCoefficientPair_runs (ω := ω) hload h99 h67 h51 h27 hku hlu hfitK hfitL
      hz (by omega)
  obtain ⟨out, d, ht, h115, hv, hi, hf', hz'', hk', hd⟩ :=
    multiplySparseCoreCoefficientPair_runs (ω := ω) hmul
      ((hk 99 (by decide) (by decide)).trans h99) h108
      ((hk 67 (by decide) (by decide)).trans h67) h114 hvK hvL hiK hiL hz' hroom
  exact ⟨out, c + d + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c, d, hr, ht, rfl⟩),
    h115, hv, hi, fun x hx => (hf' x (by omega)).trans (hf x hx), hz'',
    fun r h108r h114r h115r => (hk' r h115r).trans (hk r h108r h114r), by omega⟩

/-- Stage the exact coefficient product and advance the allocation cursor. -/
@[expose] def stageSparseCoreCoefficientProduct : Stmt :=
  .assign 111 (.bin .add (.reg 67) (.reg 67)) ;;
  .assign 112 (.bin .sub (.reg 115) (.reg 111)) ;;
  .assign 121 (.bin .add (.reg 68) (.reg 68)) ;;
  .assign 99 (.reg 115)

/-- Multiplication doubles both the limb count and fractional precision. -/
theorem stageSparseCoreCoefficientProduct_runs
    {w heap limbs precision : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (h115 : st.regs 115 = heap + 8 * limbs) (h67 : st.regs 67 = limbs)
    (h68 : st.regs 68 = precision)
    (hh : heap + 8 * limbs < 2 ^ w) (hP : 2 * precision < 2 ^ w) :
    ∃ out, Runs w p ω stageSparseCoreCoefficientProduct st .normal out 17 ∧
      out.regs 111 = 2 * limbs ∧ out.regs 112 = heap + 6 * limbs ∧
      out.regs 121 = 2 * precision ∧ out.regs 99 = heap + 8 * limbs ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 111 → r ≠ 112 → r ≠ 121 → r ≠ 99 → out.regs r = st.regs r) := by
  let s₁ := {st with regs := Function.update st.regs 111 (2 * limbs)}
  let s₂ := {s₁ with regs := Function.update s₁.regs 112 (heap + 6 * limbs)}
  let s₃ := {s₂ with regs := Function.update s₂.regs 121 (2 * precision)}
  let out := {s₃ with regs := Function.update s₃.regs 99 (heap + 8 * limbs)}
  have hL : 2 * limbs < 2 ^ w := by omega
  have hAddr : heap + 6 * limbs < 2 ^ w := by omega
  have he : heap + 8 * limbs - 2 * limbs = heap + 6 * limbs := by omega
  have hr : Runs w p ω (.assign 111 (.bin .add (.reg 67) (.reg 67))) st .normal s₁ 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, h67, ← two_mul, hL], rfl, rfl, rfl⟩
  have ht : Runs w p ω (.assign 112 (.bin .sub (.reg 115) (.reg 111))) s₁ .normal s₂ 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, s₁, h115, he, hAddr], rfl, rfl, rfl⟩
  have hu : Runs w p ω (.assign 121 (.bin .add (.reg 68) (.reg 68))) s₂ .normal s₃ 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, s₁, s₂, h68, ← two_mul, hP],
      rfl, rfl, rfl⟩
  have hv : Runs w p ω (.assign 99 (.reg 115)) s₃ .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s₁, s₂, s₃, h115], rfl, rfl, rfl⟩
  refine ⟨out, ?_, by simp [out, s₃, s₂, s₁], by simp [out, s₃, s₂],
    by simp [out, s₃], by simp [out], rfl, ?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨s₁, 4, 12, hr,
      runs_seq_iff.mpr (Or.inr ⟨s₂, 4, 7, ht,
        runs_seq_iff.mpr (Or.inr ⟨s₃, 4, 2, hu, hv, rfl⟩), rfl⟩), rfl⟩)
  · intro r h111 h112 h121 h99
    simp [out, s₃, s₂, s₁, h111, h112, h121, h99]

/-- Compute the upper coefficient product and stage it for the table writer. -/
@[expose] def prepareSparseCoreCoefficientProduct (load mul : ℕ) : Stmt :=
  initSparseCoreCoefficientProduct load mul ;; stageSparseCoreCoefficientProduct

/-- The numerator and its doubled precision are ready at the new cursor. -/
theorem prepareSparseCoreCoefficientProduct_runs
    {w h load mul heap limbs ku lu precision : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hmul : MeetsContract w p mul (Num.multiplyContract w h))
    (h99 : st.regs 99 = heap) (h67 : st.regs 67 = limbs) (h68 : st.regs 68 = precision)
    (h51 : st.regs 51 = ku) (h27 : st.regs 27 = lu)
    (hku : ku < 2 ^ w) (hlu : lu < 2 ^ w)
    (hfitK : 2 * ku < Num.capacity h limbs) (hfitL : 2 * lu < Num.capacity h limbs)
    (hz : ZeroFrom st.mem heap) (hroom : heap + 8 * limbs < 2 ^ w) (hP : 2 * precision < 2 ^ w) :
    ∃ out cost, Runs w p ω (prepareSparseCoreCoefficientProduct load mul) st .normal out cost ∧
      out.regs 111 = 2 * limbs ∧ out.regs 112 = heap + 6 * limbs ∧
      out.regs 121 = 2 * precision ∧ out.regs 99 = heap + 8 * limbs ∧
      Num.Valid out.mem (heap + 6 * limbs) h (2 * limbs) ∧
      Num.intVal out.mem (heap + 6 * limbs) h (2 * limbs) = ((ku * lu : ℕ) : ℤ) ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (heap + 8 * limbs) ∧
      (∀ r, r ∉ ([99, 108, 111, 112, 114, 115, 121] : List ℕ) →
        out.regs r = st.regs r) ∧
      cost ≤ (2 * limbs) * (38 * (2 * limbs) + 35) + 166 * limbs + 144 := by
  obtain ⟨mid, c, hr, h115, hv, hi, hf, hz', hk, hc⟩ :=
    initSparseCoreCoefficientProduct_runs (ω := ω) hload hmul h99 h67 h51 h27
      hku hlu hfitK hfitL hz hroom
  obtain ⟨out, ht, h111, h112, h121, h99', hm, hk'⟩ :=
    stageSparseCoreCoefficientProduct_runs (p := p) (ω := ω) h115
      ((hk 67 (by decide) (by decide) (by decide)).trans h67)
      ((hk 68 (by decide) (by decide) (by decide)).trans h68) hroom hP
  refine ⟨out, c + 18, runs_seq_iff.mpr (Or.inr ⟨mid, c, 17, hr, ht, by omega⟩),
    h111, h112, h121, h99', hm.symm ▸ hv, hm.symm ▸ hi,
    fun x hx => (congrFun hm x).trans (hf x hx), hm.symm ▸ hz', ?_, by omega⟩
  intro r hn
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  obtain ⟨h99r, h108r, h111r, h112r, h114r, h115r, h121r⟩ := hn
  exact (hk' r h111r h112r h121r h99r).trans (hk r h108r h114r h115r)

/-- One capacity bound for the shifted affine numerator suffices for
the constant shift, the sum, and the final rounding shift. -/
theorem sparseCoreAffineNumerator_fits
    {h limbs factor productUpper precision coarse : ℕ}
    (hFit : 2 * (factor * productUpper + 1265 * 2 ^ precision) * 2 ^ coarse <
      Num.capacity h (4 * limbs)) :
    2 * 1265 < Num.capacity h (4 * limbs) ∧
      Num.Fits h (4 * limbs) (1265 * (2 : ℤ) ^ precision) ∧
      Num.Fits h (4 * limbs) ((productUpper : ℤ) * factor + 1265 * (2 : ℤ) ^ precision) ∧
      Num.Fits h (4 * limbs)
        (((productUpper : ℤ) * factor + 1265 * (2 : ℤ) ^ precision) * (2 : ℤ) ^ coarse) := by
  let constant := 1265 * 2 ^ precision
  let total := factor * productUpper + constant
  have htotal : 2 * total < Num.capacity h (4 * limbs) :=
    (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos coarse)).trans_lt hFit
  have hconstant : 2 * constant < Num.capacity h (4 * limbs) :=
    (Nat.mul_le_mul_left 2 (Nat.le_add_left constant _)).trans_lt htotal
  have hsmall : 2 * 1265 < Num.capacity h (4 * limbs) :=
    (Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_right 1265 (Nat.two_pow_pos precision))).trans_lt hconstant
  have signed (n : ℕ) (hn : 2 * n < Num.capacity h (4 * limbs)) :
      Num.Fits h (4 * limbs) (n : ℤ) := by
    unfold Num.Fits
    refine ⟨by omega, ?_⟩
    exact_mod_cast hn
  refine ⟨hsmall, ?_, ?_, ?_⟩
  · exact_mod_cast signed constant hconstant
  · have hh := signed total htotal
    push_cast [total, constant] at hh
    simpa only [Int.mul_comm (factor : ℤ) (productUpper : ℤ)] using hh
  · have hh := signed (total * 2 ^ coarse) (by rw [← Nat.mul_assoc]; exact hFit)
    push_cast [total, constant] at hh
    simpa only [Int.mul_comm (factor : ℤ) (productUpper : ℤ)] using hh

/-- A real upper bound on the fine endpoint bounds the word quotient
computed by the rounding routine. -/
theorem sparseCoreRoundedGrowth_word
    {w upper P e scale cap : ℕ}
    (hs : scale = 2 ^ e) (hu : (upper : ℝ) / (2 : ℝ) ^ P ≤ cap)
    (hw : cap * scale + 1 < 2 ^ w) :
    upper * 2 ^ e / 2 ^ P + 1 < 2 ^ w := by
  have hu' : upper ≤ cap * 2 ^ P := by
    have he := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ P)).mp hu
    exact_mod_cast he
  have hm : upper * 2 ^ e ≤ (cap * scale) * 2 ^ P := by
    rw [hs, Nat.mul_right_comm cap]
    exact Nat.mul_le_mul_right _ hu'
  exact (Nat.add_le_add_right (Nat.div_le_of_le_mul (Nat.mul_comm (cap * scale) (2 ^ P) ▸ hm)) 1).trans_lt hw

/-- The growth cap and fractional precisions bound the bit length of
the affine numerator after the rounding shift. -/
theorem sparseCoreShiftedGrowth_capacity
    {h limbs upper P e cap : ℕ}
    (hu : (upper : ℝ) / (2 : ℝ) ^ P ≤ cap)
    (hbits : 1 + Nat.clog 2 cap + P + e < h * (4 * limbs)) :
    2 * upper * 2 ^ e < Num.capacity h (4 * limbs) := by
  have hUpper : upper ≤ cap * 2 ^ P := by
    have he := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ P)).mp hu
    exact_mod_cast he
  calc
    _ ≤ 2 * (2 ^ Nat.clog 2 cap * 2 ^ P) * 2 ^ e :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hUpper.trans
        (Nat.mul_le_mul_right _ (Nat.le_pow_clog (by decide) _))))
    _ = 2 ^ (1 + Nat.clog 2 cap + P + e) := by simp [pow_add, Nat.mul_assoc]
    _ < Num.capacity h (4 * limbs) := by
      rw [Num.capacity, Num.base, ← pow_mul]
      exact Nat.pow_lt_pow_right (by decide) hbits

/-- Compute the coefficient product and use it to initialize the
integer rebuild table. -/
@[expose] def initSparseCoreThresholdsFromEndpoints (power load extend mul shift add round h : ℕ) : Stmt :=
  prepareSparseCoreCoefficientProduct load mul ;;
  initSparseCoreThresholdsFromSparsifier power load extend mul shift add round h

/-- The table is built directly from the runtime upper endpoint words. -/
theorem initSparseCoreThresholdsFromEndpoints_runs
    (E : SparseCore.SparseCoreEnv) (C : Chain.ChainParams)
    {w power depth buckets degree growthScale h load extend mul shift add heap limbs factor P precision ku lu round e first scale vertices upper : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hpower : MeetsContract w p power (initStretchPowerContract w))
    (h44 : st.regs 44 = depth) (hDepth : depth = E.L)
    (h47 : st.regs 47 = buckets) (hBuckets : buckets = E.B_fn (C.M₀ ^ 2))
    (h48 : st.regs 48 = degree) (hDegree : degree = E.d_fn (C.M₀ ^ 2))
    (h4 : st.regs 4 = growthScale) (hGrowthScale : 0 < growthScale)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hext : MeetsContract w p extend (Num.extendCopyContract w h))
    (hmul : MeetsContract w p mul (Num.multiplyContract w h))
    (hshift : MeetsContract w p shift (Num.shiftLeftContract w h))
    (hadd : MeetsContract w p add (Num.addContract w h))
    (h99 : st.regs 99 = heap) (h67 : st.regs 67 = limbs)
    (h68 : st.regs 68 = precision) (hP : P = 2 * precision)
    (h51 : st.regs 51 = ku) (h27 : st.regs 27 = lu)
    (hku : ku < 2 ^ w) (hlu : lu < 2 ^ w)
    (hfitK : 2 * ku < Num.capacity h limbs) (hfitL : 2 * lu < Num.capacity h limbs)
    (hword : factor < 2 ^ w) (hz : ZeroFrom st.mem heap)
    (hfit : 2 * factor < Num.capacity h limbs)
    (hcword : 1265 < 2 ^ w) (hPword : P < 2 ^ w)
    (hAffineBits : 1 + Nat.clog 2 (C.M₀ + 1) + P + e < h * (4 * limbs))
    (hround : MeetsContract w p round (initDepthEndpointContract w h))
    (h30 : st.regs 30 = scale)
    (he : st.regs 119 = e) (hwordH : h < 2 ^ w) (heword : e < 2 ^ w)
    (hdvd : h ∣ P) (heP : e ≤ P) (hfrac : P / h ≤ 4 * limbs)
    (hγM : (SparseCore.sparseCoreParams E).γ_ℓ (C.M₀ ^ 2) ≤ C.M₀)
    (hγk : (SparseCore.sparseCoreParams E).γ_ℓ (C.M₀ ^ 2) ≤ C.k)
    (hbase : heap + 39 * limbs + C.d + 1 < 2 ^ w)
    (hscale : scale = 2 ^ e)
    {growth productUpper kl ll : ℕ}
    (hproduct : productUpper = ku * lu)
    (hfactor : factor = 11 * (E.L + 1) * growth * E.B_fn (C.M₀ ^ 2) *
      (2 * E.d_fn (C.M₀ ^ 2) + 190))
    (hGrowth : (E.P_fn (C.M₀ ^ 2)).γ_ℓ = growth)
    (h50 : st.regs 50 = growthScale * growth) (hg : 0 < growth)
    (hb : 0 < buckets) (hDepthWord : max (depth + 1) 3 < 2 ^ w)
    (hScaled : growthScale * growth < 2 ^ w)
    (hfirstEq : first = 3 ^ E.L * growth ^ (E.L + 1))
    (hsecondEq : upper = 11 * (E.L + 1) * growth * E.B_fn (C.M₀ ^ 2) *
      (2 * E.d_fn (C.M₀ ^ 2) + 190) * productUpper + (11 * 115) * 2 ^ P)
    (hkl : (kl : ℝ) / (2 : ℝ) ^ precision ≤ (E.P_fn (C.M₀ ^ 2)).K_s)
    (hkuBound : (E.P_fn (C.M₀ ^ 2)).K_s ≤ (ku : ℝ) / (2 : ℝ) ^ precision)
    (hll : (ll : ℝ) / (2 : ℝ) ^ precision ≤
      SparseCore.coreLambdaS (E.P_fn (C.M₀ ^ 2)) (C.M₀ ^ 2))
    (hluBound : SparseCore.coreLambdaS (E.P_fn (C.M₀ ^ 2)) (C.M₀ ^ 2) ≤
      (lu : ℝ) / (2 : ℝ) ^ precision)
    (hklOrder : kl ≤ ku) (hllOrder : ll ≤ lu)
    (hFine : 2 * (C.d + 1) * factor * ((ku - kl) * lu + ku * (lu - ll)) ≤
      (2 ^ precision) ^ 2)
    (hCoarse : 2 * (C.d + 1) ≤ scale)
    (h22 : st.regs 22 = C.M₀) (h14 : st.regs 14 = Nat.clog 2 (vertices + 2))
    (h76 : st.regs 76 = C.k) (h75 : st.regs 75 = C.d)
    (hden : 3 * C.k * Nat.clog 2 (vertices + 2) ^ 2 < 2 ^ w)
    (hcapacity : (3 * C.M₀ ^ 2 + 1) * (C.M₀ * (2 * scale) ^ (C.d + 1)) < 2 ^ w) :
    let a := max (first * scale) ((upper + 2 ^ (P - e) - 1) / 2 ^ (P - e))
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
  have hUpper : ((upper : ℤ) * (2 : ℤ) ^ e) =
      ((((ku * lu : ℕ) : ℤ) * factor + 1265 * (2 : ℤ) ^ P) * (2 : ℤ) ^ e) := by
    rw [hsecondEq, hproduct, ← hfactor]
    push_cast
    ring
  have hpow : ((2 ^ precision : ℕ) : ℝ) = (2 : ℝ) ^ precision := by push_cast; rfl
  have hpowP : (((2 ^ precision : ℕ) : ℝ) ^ 2) = (2 : ℝ) ^ P := by
    rw [hpow, ← pow_mul, hP, Nat.mul_comm 2 precision]
  have hs : 0 < (2 ^ precision : ℕ) := Nat.two_pow_pos _
  rw [← hpow] at hkl hkuBound hll hluBound
  have hloProduct := (initSparseCoreCoefficientProduct_bounds hkl hkuBound hll hluBound).1
  have hhiProduct := initSparseCoreCoefficientProduct_gap hs hklOrder hllOrder hkl hkuBound hll hluBound
  rw [hpowP, ← hproduct] at hloProduct hhiProduct
  have hfine := initSparseCoreCoefficientGap_budget hs hFine hCoarse
  rw [hfactor, hpowP] at hfine
  have hcoarse : 1 / (scale : ℝ) ≤ 1 / ((C.d : ℝ) + 1) := by
    have hcs : C.d + 1 ≤ scale := by omega
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hcs)
  obtain ⟨_, hSecondHi⟩ := initSparseCoreSecondGrowth_bounds E (C.M₀ ^ 2) growth
    productUpper P hGrowth hloProduct hhiProduct
  rw [← hsecondEq] at hSecondHi
  have hSecondLe : 11 * (((E.L : ℝ) + 1) * (E.P_fn (C.M₀ ^ 2)).K_s *
      (E.P_fn (C.M₀ ^ 2)).γ_ℓ * SparseCore.coreLambdaS (E.P_fn (C.M₀ ^ 2)) (C.M₀ ^ 2) *
      (E.B_fn (C.M₀ ^ 2) : ℝ) * (2 * (E.d_fn (C.M₀ ^ 2) : ℝ) + 190) + 115) ≤
      (SparseCore.sparseCoreParams E).γ_ℓ (C.M₀ ^ 2) := le_max_right _ _
  have hOne : 1 / ((C.d : ℝ) + 1) ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (show (1 : ℝ) ≤ (C.d : ℝ) + 1 from le_add_of_nonneg_left (by positivity))
  have hroundError := (le_add_of_nonneg_right (by positivity : 0 ≤ (1 : ℝ) / scale)).trans hfine
  have hroundHi : (upper : ℝ) / (2 : ℝ) ^ P ≤ ((C.M₀ + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_one]
    exact hSecondHi.trans (add_le_add (hSecondLe.trans hγM) (hroundError.trans hOne))
  have hAffineFit := sparseCoreShiftedGrowth_capacity hroundHi hAffineBits
  rw [hsecondEq, hproduct, ← hfactor] at hAffineFit
  change 2 * (factor * (ku * lu) + 1265 * 2 ^ P) * 2 ^ e <
    Num.capacity h (4 * limbs) at hAffineFit
  obtain ⟨hcfit, hshiftFit, hsum, hshiftUpper⟩ :=
    sparseCoreAffineNumerator_fits hAffineFit
  have hscalePos : 0 < scale := hscale.symm ▸ Nat.two_pow_pos e
  have hScalePower : 2 * scale ≤ (2 * scale) ^ (C.d + 1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < 2 * scale)
      (show 1 ≤ C.d + 1 by omega)
  have hbaseEdge : 1 ≤ C.M₀ := C.hM₀
  have hsquare : 1 ≤ C.M₀ ^ 2 := Nat.one_le_pow _ _ hbaseEdge
  have hroundWord : (C.M₀ + 1) * scale + 1 < 2 ^ w := by
    apply lt_of_le_of_lt _ hcapacity
    calc
      (C.M₀ + 1) * scale + 1 ≤ 2 * (C.M₀ * (2 * scale)) := by
        have hm : scale ≤ C.M₀ * scale := Nat.le_mul_of_pos_left _ (by omega)
        rw [Nat.add_mul, Nat.one_mul, ← Nat.mul_assoc C.M₀, Nat.mul_comm C.M₀ 2,
          Nat.mul_assoc 2, ← Nat.mul_assoc 2]
        omega
      _ ≤ (3 * C.M₀ ^ 2 + 1) * (C.M₀ * (2 * scale) ^ (C.d + 1)) :=
        Nat.mul_le_mul (show 2 ≤ 3 * C.M₀ ^ 2 + 1 by omega)
          (Nat.mul_le_mul_left _ hScalePower)
  have hfirstLe : first ≤ C.M₀ := by
    have hExact := initSparseCoreFirstGrowth_exact E (C.M₀ ^ 2) growth 0 hGrowth
    simp only [pow_zero, Nat.mul_one, div_one, ← hfirstEq] at hExact
    have hFirstTerm : SparseCore.coreE82Len E.L (E.P_fn (C.M₀ ^ 2)) ≤
        (SparseCore.sparseCoreParams E).γ_ℓ (C.M₀ ^ 2) := le_max_left _ _
    exact Nat.cast_le.mp (hExact.le.trans (hFirstTerm.trans hγM))
  have hfirst : first * scale < 2 ^ w :=
    (Nat.mul_le_mul_right scale (show first ≤ C.M₀ + 1 by omega)).trans_lt
      (lt_trans (Nat.lt_succ_self _) hroundWord)
  have hrounded := sparseCoreRoundedGrowth_word hscale hroundHi hroundWord
  obtain ⟨mid, c, hr, h111, h112, h121, h99', hv, hi, hf, hz', hk, hc⟩ :=
    prepareSparseCoreCoefficientProduct_runs (ω := ω) hload hmul h99 h67 h68 h51 h27
      hku hlu hfitK hfitL hz (by omega) (hP ▸ hPword)
  have keep (r : ℕ) (hr : r ∉ ([99, 108, 111, 112, 114, 115, 121] : List ℕ) := by decide) :=
    hk r hr
  obtain ⟨out, d, ht, h83, h98, htable, hf', hz'', hd⟩ :=
    initSparseCoreThresholdsFromSparsifier_runs (ω := ω) E C hpower
      ((keep 44).trans h44) hDepth ((keep 47).trans h47) hBuckets
      ((keep 48).trans h48) hDegree ((keep 4).trans h4) hGrowthScale
      hload hext hmul hshift hadd (h121.trans hP.symm) h99' ((keep 67).trans h67)
      h112 h111 hword (by omega) hv hz' hfit hcword hPword hcfit hshiftFit
      (by rw [hi]; exact hsum) hround ((keep 30).trans h30) hfirst ((keep 119).trans he)
      hwordH heword hdvd heP hfrac (hUpper.symm ▸ hshiftUpper) hrounded hγM hγk (by omega) hscale
      (by rw [hi, hproduct]) hfactor hGrowth ((keep 50).trans h50) hg hb hDepthWord
      hScaled hfirstEq hsecondEq hloProduct hhiProduct hcoarse hfine
      ((keep 22).trans h22) ((keep 14).trans h14) ((keep 76).trans h76)
      ((keep 75).trans h75) hden hcapacity
  have hbase' : heap + 8 * limbs + 31 * limbs = heap + 39 * limbs := by omega
  rw [hbase'] at h83 h98 htable hz''
  exact ⟨out, c + d + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c, d, hr, ht, rfl⟩),
    h83, h98, htable, fun x hx => (hf' x (by omega)).trans (hf x hx), hz'', by omega⟩

/-- Save the two query-factor words across threshold scratch use. -/
@[expose] def saveInitQueryFactors : Stmt :=
  .assign 126 (.reg 114) ;; .assign 127 (.reg 115)

/-- Restore the query-factor words and mark the completed table certified. -/
@[expose] def certifyInitThresholdTable : Stmt :=
  .assign 114 (.reg 126) ;; .assign 115 (.reg 127) ;; .assign 10 (.const 1)

/-- Saving the factors changes only the two holding registers. -/
theorem saveInitQueryFactors_runs
    {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State} :
    let regs := Function.update (Function.update st.regs 126 (st.regs 114)) 127 (st.regs 115)
    let saved := {st with regs := regs}
    Runs w p ω saveInitQueryFactors st .normal saved 5 := by
  let mid := {st with regs := Function.update st.regs 126 (st.regs 114)}
  have hr : Runs w p ω (.assign 126 (.reg 114)) st .normal mid 2 :=
    runs_assign_iff.mpr ⟨_, rfl, rfl, rfl, rfl⟩
  exact runs_seq_iff.mpr (Or.inr ⟨mid, 2, 2, hr,
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, mid], rfl, rfl, rfl⟩, rfl⟩)

/-- Certification preserves the table, cursor, and all other registers. -/
theorem certifyInitThresholdTable_runs
    {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State} (hw : 1 < 2 ^ w) :
    ∃ out, Runs w p ω certifyInitThresholdTable st .normal out 8 ∧
      out.regs 114 = st.regs 126 ∧ out.regs 115 = st.regs 127 ∧ out.regs 10 = 1 ∧
      out.mem = st.mem ∧ (∀ r, r ≠ 114 → r ≠ 115 → r ≠ 10 → out.regs r = st.regs r) := by
  let mid := {st with regs := Function.update st.regs 114 (st.regs 126)}
  let ready := {mid with regs := Function.update mid.regs 115 (st.regs 127)}
  let out := {ready with regs := Function.update ready.regs 10 1}
  have hr : Runs w p ω (.assign 114 (.reg 126)) st .normal mid 2 :=
    runs_assign_iff.mpr ⟨_, rfl, rfl, rfl, rfl⟩
  have ht : Runs w p ω (.assign 115 (.reg 127)) mid .normal ready 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, mid], rfl, rfl, rfl⟩
  have hu : Runs w p ω (.assign 10 (.const 1)) ready .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hw], rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 2, 5, hr,
      runs_seq_iff.mpr (Or.inr ⟨ready, 2, 2, ht, hu, rfl⟩), rfl⟩),
    by simp [out, ready, mid], by simp [out, ready], by simp [out], rfl,
    fun r h114 h115 h10 => by simp [out, ready, mid, h114, h115, h10]⟩

/-- Certify the endpoint-based threshold table and retain both
query-factor words for level initialization. -/
@[expose] def initCertifiedSparseCoreThresholds (power load extend mul shift add round h : ℕ) : Stmt :=
  saveInitQueryFactors ;;
  initSparseCoreThresholdsFromEndpoints power load extend mul shift add round h ;;
  certifyInitThresholdTable

/-- The certification assignments preserve the completed table and cursor. -/
theorem initCertifiedSparseCoreThresholds_runs
    {w power load extend mul shift add round h cost : ℕ}
    {p : Program} {ω : ℕ → Bool} {st finished : State}
    (hw : 1 < 2 ^ w)
    (hr : Runs w p ω (initSparseCoreThresholdsFromEndpoints power load extend mul shift add round h)
      {st with regs := Function.update (Function.update st.regs 126 (st.regs 114)) 127 (st.regs 115)}
      .normal finished cost) :
    ∃ out, Runs w p ω (initCertifiedSparseCoreThresholds power load extend mul shift add round h)
        st .normal out (cost + 15) ∧
      out.regs 114 = st.regs 114 ∧ out.regs 115 = st.regs 115 ∧ out.regs 10 = 1 ∧
      out.mem = finished.mem ∧
      (∀ r, r ≠ 114 → r ≠ 115 → r ≠ 10 → out.regs r = finished.regs r) := by
  have hf : writesBelow 126
      (initSparseCoreThresholdsFromEndpoints power load extend mul shift add round h) = true := rfl
  have h126 := runs_preserves_above (by decide : 126 ≤ 126) hf hr
  have h127 := runs_preserves_above (by decide : 126 ≤ 127) hf hr
  obtain ⟨out, ht, h114, h115, h10, hm, hk⟩ :=
    certifyInitThresholdTable_runs (p := p) (ω := ω) (st := finished) hw
  refine ⟨out, ?_, h114.trans (by simpa using h126), h115.trans (by simpa using h127), h10, hm, hk⟩
  exact runs_seq_iff.mpr (Or.inr ⟨_, 5, _, saveInitQueryFactors_runs,
    runs_seq_iff.mpr (Or.inr ⟨finished, cost, 8, hr, ht, rfl⟩), by omega⟩)

/-- The coefficient and logarithm routines give absolute integer gap
bounds. A scale linear in those gaps suffices after multiplying the endpoints. -/
theorem initSparseCoreCoefficientGap_of_endpoint_bounds
    {kl ku ll lu scale factor d kBound lBound kGap lGap : ℕ}
    (hku : ku ≤ kBound * scale) (hlu : lu ≤ lBound * scale)
    (hk : ku - kl ≤ kGap) (hl : lu - ll ≤ lGap)
    (hscale : 2 * (d + 1) * factor * (kGap * lBound + kBound * lGap) ≤ scale) :
    2 * (d + 1) * factor * ((ku - kl) * lu + ku * (lu - ll)) ≤ scale ^ 2 := by
  have hgap : (ku - kl) * lu + ku * (lu - ll) ≤
      (kGap * lBound + kBound * lGap) * scale := by
    calc
      _ ≤ kGap * (lBound * scale) + (kBound * scale) * lGap :=
        Nat.add_le_add (Nat.mul_le_mul hk hlu) (Nat.mul_le_mul hku hl)
      _ = _ := by ring
  calc
    _ ≤ 2 * (d + 1) * factor * ((kGap * lBound + kBound * lGap) * scale) :=
      Nat.mul_le_mul_left _ hgap
    _ = (2 * (d + 1) * factor * (kGap * lBound + kBound * lGap)) * scale := by ring
    _ ≤ scale ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul_right _ hscale

end MinCostFlow.MinRatio
