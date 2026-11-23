module

public import MinCostFlow.MinRatio.InitMachineFallbackCost
public import MinCostFlow.MinRatio.InitGrowthConstant

/-!
# Integer thresholds from machine sparsifier factors

Use the exact scaled length factor to populate the rebuild threshold table.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Expander.PathDSProg

/-- The scaled numerator computed by the merged path tool decodes to
the model growth cap used in the threshold recurrence. -/
theorem initMachineThresholdGrowth_eq
    (Kγ c Kint den M scale : ℕ) (cDeg phiConst : ℝ) (paths : Spanner.PathDSTool)
    (hscale : 0 < scale)
    (hExp : ∀ phi cap, paths.γ_ExpPath phi cap =
      (gExpImpl Kγ c Kint (Nat.ceil (1 / phi)) cap : ℝ)) :
    let phiMin := 1 / (den : ℝ)
    let cap := Spanner.capM_W cDeg phiMin M
    let witnessDen := Nat.ceil (1 / phiConst)
    let numerator := scale * (max (gExpImpl Kγ c Kint den M)
      (gExpImpl Kγ c Kint witnessDen cap)) ^ 2
    (numerator : ℝ) / scale = Spanner.capGammaL cDeg phiConst paths phiMin M := by
  dsimp only
  have hden : Nat.ceil (1 / (1 / (den : ℝ))) = den := by simp [one_div]
  have hs : (scale : ℝ) ≠ 0 := by exact_mod_cast hscale.ne'
  rw [Spanner.capGammaL, Spanner.capGammaExpPath, hExp, hExp, hden,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_max, mul_comm, mul_div_cancel_right₀ _ hs]

/-- With integer path factors, the first sparse-core growth term is
an exact natural power product at any fine dyadic precision. -/
theorem initSparseCoreFirstGrowth_exact
    (E : SparseCore.SparseCoreEnv) (M growth precision : ℕ)
    (hGrowth : (E.P_fn M).γ_ℓ = growth) :
    ((3 ^ E.L * growth ^ (E.L + 1) * 2 ^ precision : ℕ) : ℝ) /
        (2 : ℝ) ^ precision = SparseCore.coreE82Len E.L (E.P_fn M) := by
  push_cast
  rw [mul_div_cancel_right₀ _ (by positivity), SparseCore.coreE82Len, hGrowth]

/-- The unscaled first numerator fits whenever the model permits its
growth factor at the top level and the top edge count fits. -/
theorem initSparseCoreFirstGrowth_fits
    (E : SparseCore.SparseCoreEnv) (M top growth w : ℕ)
    (hGrowth : (E.P_fn M).γ_ℓ = growth)
    (hcap : (SparseCore.sparseCoreParams E).γ_ℓ M ≤ top)
    (hword : top < 2 ^ w) :
    3 ^ E.L * growth ^ (E.L + 1) < 2 ^ w := by
  have hfirst := initSparseCoreFirstGrowth_exact E M growth 0 hGrowth
  simp only [pow_zero, Nat.mul_one, div_one] at hfirst
  have hle : SparseCore.coreE82Len E.L (E.P_fn M) ≤
      (SparseCore.sparseCoreParams E).γ_ℓ M := by
    exact le_max_left _ _
  have hcast := hfirst.le.trans (hle.trans hcap)
  exact (Nat.cast_le.mp hcast).trans_lt hword

/-- Read the integer sparsifier length from its exactly scaled word. -/
@[expose] def stageIntegerSparsifierLength : Stmt :=
  .assign 35 (.bin .div (.reg 50) (.reg 4))

/-- Division removes the scale exactly and preserves all other inputs. -/
theorem stageIntegerSparsifierLength_runs
    {w growth scale : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (h50 : st.regs 50 = scale * growth) (h4 : st.regs 4 = scale)
    (hs : 0 < scale) (hw : scale * growth < 2 ^ w) :
    ∃ out, Runs w p ω stageIntegerSparsifierLength st .normal out 4 ∧
      out.regs 35 = growth ∧ out.mem = st.mem ∧
      (∀ r ≠ 35, out.regs r = st.regs r) := by
  let out := {st with regs := Function.update st.regs 35 growth}
  have he : scale * growth / scale = growth := by
    rw [Nat.mul_comm]
    exact Nat.mul_div_cancel _ hs
  have hg : growth < 2 ^ w := (Nat.le_mul_of_pos_left growth hs).trans_lt hw
  exact ⟨out, runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, h50, h4, he, hg],
    rfl, rfl, rfl⟩, by simp [out], rfl, fun r hr => by simp [out, hr]⟩

/-- Evaluate the unscaled first term by two exact word powers and a
multiplication. Registers 44, 33, and 35 hold the depth, depth plus
one, and the integer sparsifier length factor. -/
@[expose] def initSparseCoreFirstGrowth (power : ℕ) : Stmt :=
  .call 34 power [.const 3, .reg 44] ;;
  computeInitStretchFirstEndpoint power

/-- The final product bound supplies the room for both power calls. -/
theorem initSparseCoreFirstGrowth_runs
    {w power depth growth : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p power (initStretchPowerContract w))
    (h44 : st.regs 44 = depth) (h33 : st.regs 33 = depth + 1)
    (h35 : st.regs 35 = growth) (hpos : 0 < growth)
    (hw : max 3 (max growth (depth + 1)) < 2 ^ w)
    (hfit : 3 ^ depth * growth ^ (depth + 1) < 2 ^ w) :
    ∃ out cost, Runs w p ω (initSparseCoreFirstGrowth power) st .normal out cost ∧
      out.regs 36 = 3 ^ depth * growth ^ (depth + 1) ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 34 → r ≠ 36 → out.regs r = st.regs r) ∧ cost ≤ 40 * depth + 44 := by
  have h3 : 3 < 2 ^ w := (le_max_left _ _).trans_lt hw
  have hg : growth < 2 ^ w := (le_max_left _ _).trans (le_max_right _ _) |>.trans_lt hw
  have hd : depth + 1 < 2 ^ w := (le_max_right _ _).trans (le_max_right _ _) |>.trans_lt hw
  have hpow : 0 < growth ^ (depth + 1) := Nat.pow_pos hpos
  have h3pow := (Nat.le_mul_of_pos_right (3 ^ depth) hpow).trans_lt hfit
  have hgp := (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide : 0 < 3))).trans_lt hfit
  have hargs : evalArgs w st [.const 3, .reg 44] = some [3, depth] := by
    simp [evalArgs, Expr.eval, h44, h3]
  have hwords : ∀ a ∈ [3, depth], a < 2 ^ w := by
    intro a ha
    simp at ha
    rcases ha with rfl | rfl
    · exact h3
    · omega
  obtain ⟨mid, c, ret, hr, ⟨hm, hret⟩, h34, hk, hc⟩ :=
    runs_call_of_meetsContract (r := 34) himpl hargs hwords
      ⟨3, depth, rfl, by decide, h3pow⟩ ω
  obtain ⟨out, d, ht, h36, hm', hk', hdCost⟩ :=
    computeInitStretchFirstEndpoint_runs (ω := ω) himpl ((hk 33 (by decide)).trans h33)
      (h34.trans hret) ((hk 35 (by decide)).trans h35) hpos hg hd hgp hfit
  change c ≤ 2 + (20 * depth + 6) + 1 at hc
  refine ⟨out, c + d + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c, d, hr, ht, rfl⟩),
    h36, hm'.trans hm, fun r h₁ h₂ => (hk' r h₂).trans (hk r h₁), by omega⟩

/-- Compute the first growth term from the scaled sparsifier output
and the runtime sparse-core depth. -/
@[expose] def initFirstGrowthFromSparsifier (power : ℕ) : Stmt :=
  stageIntegerSparsifierLength ;;
  prepareInitStretchExponents ;;
  initSparseCoreFirstGrowth power

/-- The first term is computed exactly with a cost linear in the depth. -/
theorem initFirstGrowthFromSparsifier_runs
    {w power depth growth scale : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p power (initStretchPowerContract w))
    (h44 : st.regs 44 = depth) (h50 : st.regs 50 = scale * growth)
    (h4 : st.regs 4 = scale) (hs : 0 < scale) (hg : 0 < growth)
    (hw : max (depth + 1) 3 < 2 ^ w) (hScaled : scale * growth < 2 ^ w)
    (hfit : 3 ^ depth * growth ^ (depth + 1) < 2 ^ w) :
    ∃ out cost, Runs w p ω (initFirstGrowthFromSparsifier power) st .normal out cost ∧
      out.regs 36 = 3 ^ depth * growth ^ (depth + 1) ∧ out.regs 35 = growth ∧ out.regs 33 = depth + 1 ∧
      out.mem = st.mem ∧
      (∀ r, r ∉ ([33, 34, 35, 36, 45] : List ℕ) → out.regs r = st.regs r) ∧
      cost ≤ 40 * depth + 61 := by
  obtain ⟨mid, hr, h35, hm, hk⟩ :=
    stageIntegerSparsifierLength_runs (p := p) (ω := ω) h50 h4 hs hScaled
  obtain ⟨ready, ht, h33, _, hk', hm', _⟩ :=
    prepareInitStretchExponents_runs (p := p) (ω := ω) ((hk 44 (by decide)).trans h44) hw
  have hword : max 3 (max growth (depth + 1)) < 2 ^ w := by
    have hgw := (Nat.le_mul_of_pos_left growth hs).trans_lt hScaled
    omega
  obtain ⟨out, c, hu, h36, hm'', hk'', hc⟩ :=
    initSparseCoreFirstGrowth_runs (ω := ω) himpl
      ((hk' 44 (by decide) (by decide)).trans ((hk 44 (by decide)).trans h44))
      h33 ((hk' 35 (by decide) (by decide)).trans h35) hg hword hfit
  refine ⟨out, 4 + 11 + c + 2, ?_, h36,
    (hk'' 35 (by decide) (by decide)).trans ((hk' 35 (by decide) (by decide)).trans h35),
    (hk'' 33 (by decide) (by decide)).trans h33, hm''.trans (hm'.trans hm), ?_, by omega⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨mid, 4, _, hr,
      runs_seq_iff.mpr (Or.inr ⟨ready, 11, c, ht, hu, rfl⟩), by omega⟩)
  · intro r h
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    exact (hk'' r h.2.1 h.2.2.2.1).trans
      ((hk' r h.1 h.2.2.2.2).trans (hk r h.2.2.1))

/-- Save the exact first term at the coarse scale while the second
term is rounded from its multiword representation. -/
@[expose] def stageSparseCoreFirstGrowth : Stmt :=
  .assign 122 (.bin .mul (.reg 36) (.reg 30))

/-- The scaled first term has no rounding error and leaves the second
term and table inputs intact. -/
theorem stageSparseCoreFirstGrowth_runs
    {w first scale : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (h36 : st.regs 36 = first) (h30 : st.regs 30 = scale)
    (hfit : first * scale < 2 ^ w) :
    ∃ out, Runs w p ω stageSparseCoreFirstGrowth st .normal out 4 ∧
      out.regs 122 = first * scale ∧ out.mem = st.mem ∧
      (∀ r ≠ 122, out.regs r = st.regs r) := by
  let out := {st with regs := Function.update st.regs 122 (first * scale)}
  exact ⟨out, runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, h36, h30, hfit],
    rfl, rfl, rfl⟩, by simp [out], rfl, fun r hr => by simp [out, hr]⟩

/-- Combine the exact first term with the rounded multiword second term. -/
@[expose] def roundSparseCoreGrowth (shift round h : ℕ) : Stmt :=
  stageSparseCoreFirstGrowth ;;
  roundMultiwordRebuildGrowth shift round h ;;
  selectRoundedRebuildGrowth

/-- Only the second term needs a rounding buffer. -/
theorem roundSparseCoreGrowth_runs
    {w h shift round addr limbs e heap P upper first scale : ℕ}
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
    (hrounded : upper * 2 ^ e / 2 ^ P + 1 < 2 ^ w) :
    ∃ out cost, Runs w p ω (roundSparseCoreGrowth shift round h) st .normal out cost ∧
      out.regs 12 = max (first * scale) ((upper + 2 ^ (P - e) - 1) / 2 ^ (P - e)) ∧
      out.regs 120 = heap + limbs ∧ (∀ a < heap, out.mem a = st.mem a) ∧
      ZeroFrom out.mem (heap + limbs) ∧
      (∀ r, r ≠ 12 → r ≠ 120 → r ≠ 122 → out.regs r = st.regs r) ∧
      cost ≤ 60 * limbs + 109 := by
  obtain ⟨mid, hr, h122, hm, hk⟩ :=
    stageSparseCoreFirstGrowth_runs (p := p) (ω := ω) h36 h30 hfirst
  obtain ⟨ready, c, ht, h12, h120, hf, hz', hk', hc⟩ :=
    roundMultiwordRebuildGrowth_runs (ω := ω) hshift hround
      ((hk 117 (by decide)).trans ha) ((hk 118 (by decide)).trans hL)
      ((hk 119 (by decide)).trans he) ((hk 115 (by decide)).trans hh)
      ((hk 121 (by decide)).trans hP) hword heword hdvd heP hfrac hbelow
      (hm.symm ▸ hv) (hm.symm ▸ hz) hroom (hm.symm ▸ hvalue) hfit hrounded
  obtain ⟨out, d, hu, hmax, hm', hk'', hd⟩ :=
    selectRoundedRebuildGrowth_runs (ω := ω)
      ((hk' 122 (by decide) (by decide)).trans h122) h12 hw
  refine ⟨out, 4 + c + d + 2, ?_, hmax, (hk'' 120 (by decide)).trans h120,
    fun a ha' => (congrFun hm' a).trans ((hf a ha').trans (congrFun hm a)),
    hm'.symm ▸ hz', fun r h12r h120r h122r =>
      (hk'' r h12r).trans ((hk' r h12r h120r).trans (hk r h122r)), by omega⟩
  exact runs_seq_iff.mpr (Or.inr ⟨mid, 4, _, hr,
    runs_seq_iff.mpr (Or.inr ⟨ready, c, d, ht, hu, rfl⟩), by omega⟩)

/-- Form the integer multiplier of the second growth term from the
capacity multiplier and the exact sparsifier length. -/
@[expose] def stageSparseCoreSecondMultiplier : Stmt :=
  .assign 37 (.bin .mul (.bin .mul (.const 11) (.reg 38)) (.reg 35))

/-- The entire multiplier fits if its final product fits and the
sparsifier length is positive. -/
theorem stageSparseCoreSecondMultiplier_runs
    {w capacity growth : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (h38 : st.regs 38 = capacity) (h35 : st.regs 35 = growth)
    (hpos : 0 < growth) (hw : 11 < 2 ^ w)
    (hfit : 11 * capacity * growth < 2 ^ w) :
    ∃ out, Runs w p ω stageSparseCoreSecondMultiplier st .normal out 6 ∧
      out.regs 37 = 11 * capacity * growth ∧ out.mem = st.mem ∧
      (∀ r ≠ 37, out.regs r = st.regs r) := by
  let out := {st with regs := Function.update st.regs 37 (11 * capacity * growth)}
  have hcap := (Nat.le_mul_of_pos_right (11 * capacity) hpos).trans_lt hfit
  exact ⟨out, runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, h38, h35, hw, hcap, hfit],
    rfl, rfl, rfl⟩, by simp [out], rfl, fun r hr => by simp [out, hr]⟩

/-- Compute the second growth multiplier from the runtime depth,
bucket cap, degree cap, and exact sparsifier length. -/
@[expose] def initSparseCoreSecondMultiplier : Stmt :=
  prepareInitStretchCapacity ;; stageSparseCoreSecondMultiplier

/-- The final multiplier bound covers both stages of the calculation. -/
theorem initSparseCoreSecondMultiplier_runs
    {w depth buckets degree growth : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (h33 : st.regs 33 = depth + 1) (h47 : st.regs 47 = buckets)
    (h48 : st.regs 48 = degree) (h35 : st.regs 35 = growth)
    (hb : 0 < buckets) (hg : 0 < growth) (hw : 11 < 2 ^ w)
    (hfit : 11 * ((depth + 1) * buckets * (2 * degree + 190)) * growth < 2 ^ w) :
    ∃ out, Runs w p ω initSparseCoreSecondMultiplier st .normal out 17 ∧
      out.regs 37 = 11 * (depth + 1) * growth * buckets * (2 * degree + 190) ∧
      out.mem = st.mem ∧ (∀ r, r ≠ 37 → r ≠ 38 → out.regs r = st.regs r) := by
  let capacity := (depth + 1) * buckets * (2 * degree + 190)
  have hcap : capacity < 2 ^ w :=
    ((Nat.le_mul_of_pos_left capacity (by decide : 0 < 11)).trans
      (Nat.le_mul_of_pos_right (11 * capacity) hg)).trans_lt hfit
  obtain ⟨mid, hr, h38, hk, hm, _⟩ :=
    prepareInitStretchCapacity_runs (p := p) (ω := ω) h33 h47 h48 hb hcap
  obtain ⟨out, ht, h37, hm', hk'⟩ :=
    stageSparseCoreSecondMultiplier_runs (p := p) (ω := ω) h38 ((hk 35 (by decide)).trans h35) hg hw hfit
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 10, 6, hr, ht, rfl⟩),
    ?_, hm'.trans hm, fun r h37r h38r => (hk' r h37r).trans (hk r h38r)⟩
  rw [h37]
  ac_rfl

/-- Compute the exact first growth term and the multiplier of the second. -/
@[expose] def initSparseCoreGrowthWords (power : ℕ) : Stmt :=
  initFirstGrowthFromSparsifier power ;; initSparseCoreSecondMultiplier

/-- Both words come from the same integer sparsifier length and depth. -/
theorem initSparseCoreGrowthWords_runs
    {w power depth growth scale buckets degree : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p power (initStretchPowerContract w))
    (h44 : st.regs 44 = depth) (h50 : st.regs 50 = scale * growth)
    (h4 : st.regs 4 = scale) (hs : 0 < scale) (hg : 0 < growth)
    (hw : max (depth + 1) 3 < 2 ^ w) (hScaled : scale * growth < 2 ^ w)
    (hfit : 3 ^ depth * growth ^ (depth + 1) < 2 ^ w)
    (h47 : st.regs 47 = buckets) (h48 : st.regs 48 = degree) (hb : 0 < buckets)
    (hw' : 11 < 2 ^ w)
    (hfit' : 11 * ((depth + 1) * buckets * (2 * degree + 190)) * growth < 2 ^ w) :
    ∃ out cost, Runs w p ω (initSparseCoreGrowthWords power) st .normal out cost ∧
      out.regs 35 = growth ∧ out.regs 36 = 3 ^ depth * growth ^ (depth + 1) ∧
      out.regs 37 = 11 * (depth + 1) * growth * buckets * (2 * degree + 190) ∧
      out.mem = st.mem ∧
      (∀ r, r ∉ ([33, 34, 35, 36, 37, 38, 45] : List ℕ) → out.regs r = st.regs r) ∧
      cost ≤ 40 * depth + 79 := by
  obtain ⟨mid, c, hr, h36, h35, h33, hm, hk, hc⟩ :=
    initFirstGrowthFromSparsifier_runs (ω := ω) himpl h44 h50 h4 hs hg hw hScaled hfit
  obtain ⟨out, ht, h37, hm', hk'⟩ :=
    initSparseCoreSecondMultiplier_runs (p := p) (ω := ω) h33
      ((hk 47 (by decide)).trans h47) ((hk 48 (by decide)).trans h48) h35 hb hg hw' hfit'
  refine ⟨out, c + 18, runs_seq_iff.mpr (Or.inr ⟨mid, c, 17, hr, ht, by omega⟩),
    (hk' 35 (by decide) (by decide)).trans h35, (hk' 36 (by decide) (by decide)).trans h36, h37, hm'.trans hm, ?_, by omega⟩
  intro r hn
  apply (hk' r (fun h => hn (by simp [h])) (fun h => hn (by simp [h]))).trans
  apply hk r
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using
    (show ¬ (r = 33 ∨ r = 34 ∨ r = 35 ∨ r = 36 ∨ r = 45) by
      intro h
      rcases h with h | h | h | h | h <;> exact hn (by simp [h]))

/-- Encode the second-term multiplier in a signed limb block. -/
@[expose] def loadSparseCoreSecondMultiplier (load : ℕ) : Stmt :=
  .call 116 load [.reg 37, .reg 67, .reg 99]

/-- Allocate the multiplier while preserving earlier blocks. -/
theorem loadSparseCoreSecondMultiplier_runs
    {w h load heap limbs factor : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (h99 : st.regs 99 = heap) (h67 : st.regs 67 = limbs) (h37 : st.regs 37 = factor)
    (hword : factor < 2 ^ w) (hroom : heap + limbs < 2 ^ w)
    (hz : ZeroFrom st.mem heap) (hfit : 2 * factor < Num.capacity h limbs) :
    ∃ out cost, Runs w p ω (loadSparseCoreSecondMultiplier load) st .normal out cost ∧
      out.regs 116 = heap + limbs ∧ Num.Valid out.mem heap h limbs ∧
      Num.intVal out.mem heap h limbs = (factor : ℤ) ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (heap + limbs) ∧
      (∀ r, r ≠ 116 → out.regs r = st.regs r) ∧ cost ≤ 23 * limbs + 10 := by
  have hargs : evalArgs w st [.reg 37, .reg 67, .reg 99] = some [factor, limbs, heap] := by
    simp [evalArgs, Expr.eval, h37, h67, h99]
  have hpre : (Num.loadSmallContract w h).pre [factor, limbs, heap] st.mem :=
    ⟨⟨factor, limbs, heap, rfl⟩, hz, hroom⟩
  obtain ⟨out, cost, ret, hr, hp, hv, hf, hc⟩ :=
    runs_call_of_meetsContract (r := 116) hload hargs (by wram_words) hpre ω
  change ret = heap + limbs ∧ heap ≤ ret ∧ ret ≤ heap + limbs ∧
    (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem ret ∧
    ListAt out.mem heap (Num.digits h limbs factor) at hp
  obtain ⟨heq, _, _, hframe, hzero, hdigits⟩ := hp
  obtain ⟨hvalid, hu, _⟩ := Num.loadSmall_value hdigits
  have hsmall : factor < Num.capacity h limbs := by omega
  have hi : Num.intVal out.mem heap h limbs = (factor : ℤ) := by
    rw [Num.intVal, hu, Nat.mod_eq_of_lt hsmall, Num.signedVal, ite_eq_right (not_le_of_gt hfit), sub_zero]
  exact ⟨out, cost, hr, hv.trans heq, hvalid, hi, hframe, heq ▸ hzero, hf, by simp [Num.loadSmallContract, heapContract, argsSize, Expr.size] at hc; omega⟩

/-- Pass the multiplier block and its fresh cursor to the widening
and multiplication calls. -/
@[expose] def stageSparseCoreMultiplierBlock : Stmt :=
  .assign 108 (.reg 116) ;; .assign 116 (.reg 99)

/-- Staging preserves the product block and its precision. -/
theorem stageSparseCoreMultiplierBlock_runs
    {w addr cursor : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (ha : st.regs 99 = addr) (hc : st.regs 116 = cursor) :
    ∃ out, Runs w p ω stageSparseCoreMultiplierBlock st .normal out 5 ∧
      out.regs 116 = addr ∧ out.regs 108 = cursor ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 108 → r ≠ 116 → out.regs r = st.regs r) := by
  let mid := {st with regs := Function.update st.regs 108 cursor}
  let out := {mid with regs := Function.update mid.regs 116 addr}
  have hr : Runs w p ω (.assign 108 (.reg 116)) st .normal mid 2 :=
    runs_assign_iff.mpr ⟨_, congrArg some hc, rfl, rfl, rfl⟩
  have ht : Runs w p ω (.assign 116 (.reg 99)) mid .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, mid, ha], rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 2, 2, hr, ht, rfl⟩),
    by simp [out], by simp [out, mid], rfl, fun r h108 h116 => by simp [out, mid, h108, h116]⟩

/-- Multiply the coefficient product by the exact integer multiplier. -/
@[expose] def multiplySparseCoreSecondGrowth (load extend mul : ℕ) : Stmt :=
  loadSparseCoreSecondMultiplier load ;;
  stageSparseCoreMultiplierBlock ;;
  rebuildLogFactorProduct extend mul

/-- The multiplier leaves the fractional precision of the input
product unchanged. The new block stores its exact integer product. -/
theorem multiplySparseCoreSecondGrowth_runs
    {w h load extend mul heap limbs factor source : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hext : MeetsContract w p extend (Num.extendCopyContract w h))
    (hmul : MeetsContract w p mul (Num.multiplyContract w h))
    (h99 : st.regs 99 = heap) (h67 : st.regs 67 = limbs) (h37 : st.regs 37 = factor)
    (h112 : st.regs 112 = source) (h111 : st.regs 111 = 2 * limbs)
    (hword : factor < 2 ^ w) (hbelow : source + 2 * limbs ≤ heap)
    (hv : Num.Valid st.mem source h (2 * limbs)) (hz : ZeroFrom st.mem heap)
    (hfit : 2 * factor < Num.capacity h limbs)
    (hroom : heap + 15 * limbs < 2 ^ w) :
    ∃ out cost, Runs w p ω (multiplySparseCoreSecondGrowth load extend mul) st .normal out cost ∧
      out.regs 115 = heap + 15 * limbs ∧
      Num.Valid out.mem (heap + 11 * limbs) h (4 * limbs) ∧
      Num.intVal out.mem (heap + 11 * limbs) h (4 * limbs) =
        Num.intVal st.mem source h (2 * limbs) * (factor : ℤ) ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (heap + 15 * limbs) ∧
      (∀ r, r ≠ 108 → r ≠ 114 → r ≠ 115 → r ≠ 116 → out.regs r = st.regs r) ∧
      cost ≤ (4 * limbs) * (38 * (4 * limbs) + 35) + 323 * limbs + 134 := by
  obtain ⟨mid, c, hr, h116, hvf, hif, hf, hz', hk, hc⟩ :=
    loadSparseCoreSecondMultiplier_runs (ω := ω) hload h99 h67 h37 hword (by omega) hz hfit
  obtain ⟨ready, ht, ha, h108, hm, hk'⟩ :=
    stageSparseCoreMultiplierBlock_runs (w := w) (p := p) (ω := ω)
      ((hk 99 (by decide)).trans h99) h116
  have hframe (x : ℕ) (hx : x < heap) : ready.mem x = st.mem x :=
    (congrFun hm x).trans (hf x hx)
  have hsv : Num.Valid ready.mem source h (2 * limbs) := by
    intro j hj
    rw [hframe _ (by omega)]
    exact hv j hj
  have hvf' : Num.Valid ready.mem heap h limbs := hm.symm ▸ hvf
  have huf : Num.unsignedVal ready.mem heap h limbs = factor := by
    have hi : Num.intVal ready.mem heap h limbs = (factor : ℤ) := hm.symm ▸ hif
    unfold Num.intVal Num.signedVal at hi
    have hb := Num.unsignedVal_lt hvf'
    split at hi <;> omega
  have keep (r : ℕ) (h₁ : r ≠ 108 := by decide) (h₂ : r ≠ 116 := by decide) :=
    (hk' r h₁ h₂).trans (hk r h₂)
  obtain ⟨out, d, hu, h115, hout, hprod, hf', hzero, hkOut, hd⟩ :=
    rebuildLogFactorProduct_runs (ω := ω) hext hmul ha ((keep 112).trans h112)
      ((keep 67).trans h67) ((keep 111).trans h111) h108 le_rfl (by omega)
      hvf' hsv (by rwa [huf]) (hm.symm ▸ hz') (by omega)
  have haEq : heap + limbs + 2 * limbs + 4 * (2 * limbs) = heap + 11 * limbs := by omega
  have hEnd : heap + limbs + 2 * limbs + 6 * (2 * limbs) = heap + 15 * limbs := by omega
  have hL : 2 * (2 * limbs) = 4 * limbs := by omega
  rw [haEq, hL] at hout hprod
  have hsrc : Num.intVal ready.mem source h (2 * limbs) = Num.intVal st.mem source h (2 * limbs) :=
    Num.intVal_congr (fun j hj => hframe _ (by omega))
  rw [hsrc, (show Num.intVal ready.mem heap h limbs = (factor : ℤ) from hm.symm ▸ hif)] at hprod
  exact ⟨out, c + 5 + d + 2, runs_seq_iff.mpr (Or.inr ⟨mid, c, _,
    hr, runs_seq_iff.mpr (Or.inr ⟨ready, 5, d, ht, hu, rfl⟩), by omega⟩),
    h115.trans hEnd, hout, hprod, fun x hx => (hf' x (by omega)).trans (hframe x hx),
    hEnd ▸ hzero, fun r hr₁ hr₂ hr₃ hr₄ => (hkOut r hr₂ hr₃).trans (keep r hr₁ hr₄), by omega⟩

/-- Form the complete second growth numerator at the product precision. -/
@[expose] def initSparseCoreSecondNumerator (load extend mul shift add : ℕ) : Stmt :=
  multiplySparseCoreSecondGrowth load extend mul ;;
  completeSparseCoreSecondGrowth load shift add

/-- Multiplication and affine correction allocate fresh blocks and
return the numerator address, width, and cursor for rounding. -/
theorem initSparseCoreSecondNumerator_runs
    {w h load extend mul shift add heap limbs factor source P : ℕ}
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
      (Num.intVal st.mem source h (2 * limbs) * (factor : ℤ) + 1265 * (2 : ℤ) ^ P)) :
    ∃ out cost, Runs w p ω (initSparseCoreSecondNumerator load extend mul shift add)
        st .normal out cost ∧
      out.regs 117 = heap + 23 * limbs ∧ out.regs 115 = heap + 27 * limbs ∧
      out.regs 118 = 4 * limbs ∧ Num.Valid out.mem (heap + 23 * limbs) h (4 * limbs) ∧
      Num.intVal out.mem (heap + 23 * limbs) h (4 * limbs) =
        Num.intVal st.mem source h (2 * limbs) * (factor : ℤ) + 1265 * (2 : ℤ) ^ P ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (heap + 27 * limbs) ∧
      (∀ r, r ∉ ([108, 114, 115, 116, 117, 118] : List ℕ) →
        out.regs r = st.regs r) ∧
      cost ≤ (4 * limbs) * (38 * (4 * limbs) + 35) + 707 * limbs + 220 := by
  obtain ⟨mid, c, hr, h115, hvp, hprod, hf, hz', hk, hc⟩ :=
    multiplySparseCoreSecondGrowth_runs (ω := ω) hload hext hmul h99 h67 h37 h112 h111
      hword hbelow hv hz hfit (by omega)
  have hwidth : 2 * limbs + 2 * limbs = 4 * limbs := by omega
  have haddr : heap + 15 * limbs - 4 * limbs = heap + 11 * limbs := by omega
  obtain ⟨out, d, ht, ha, hh, hL, hv', hi, hf', hzero, hk', hd⟩ :=
    completeSparseCoreSecondGrowth_runs (ω := ω) hload hshift hadd h115
      ((hk 111 (by decide) (by decide) (by decide) (by decide)).trans h111)
      ((hk 121 (by decide) (by decide) (by decide) (by decide)).trans h121)
      (by omega) (by simpa only [haddr, hwidth] using hvp) hcword hPword hz' (by omega)
      (by simpa only [hwidth] using hcfit) (by simpa only [hwidth] using hshiftFit)
      (by simpa only [haddr, hwidth, hprod] using hsum)
  have ha' : heap + 15 * limbs + 2 * (2 * limbs + 2 * limbs) = heap + 23 * limbs := by omega
  have hh' : heap + 15 * limbs + 3 * (2 * limbs + 2 * limbs) = heap + 27 * limbs := by omega
  rw [ha', hwidth, haddr, hprod] at hi
  rw [ha', hwidth] at hv'
  refine ⟨out, c + d + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c, d, hr, ht, rfl⟩),
    ha.trans ha', hh.trans hh', hL.trans hwidth, hv', hi,
    fun x hx => (hf' x (by omega)).trans (hf x hx), hh' ▸ hzero, ?_, by omega⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h108, h114, h115r, h116, h117, h118⟩ := hr
  exact (hk' r h114 h115r h116 h117 h118).trans (hk r h108 h114 h115r h116)

/-- The second term dominates its integer multiplier because the
coefficient and logarithmic factor are at least one. -/
theorem initSparseCoreSecondMultiplier_le_growth
    (E : SparseCore.SparseCoreEnv) (M growth : ℕ)
    (hGrowth : (E.P_fn M).γ_ℓ = growth)
    (hK : 1 ≤ (E.P_fn M).K_s) :
    ((11 * (E.L + 1) * growth * E.B_fn M * (2 * E.d_fn M + 190) : ℕ) : ℝ) ≤
      (SparseCore.sparseCoreParams E).γ_ℓ M := by
  let factor : ℝ := 11 * ((E.L : ℝ) + 1) * growth * (E.B_fn M : ℝ) *
    (2 * (E.d_fn M : ℝ) + 190)
  have hf : 0 ≤ factor := by dsimp [factor]; positivity
  have hLambda := SparseCore.coreLambdaS_ge_one (E.P_fn M) M
  have hprod : 1 ≤ (E.P_fn M).K_s * SparseCore.coreLambdaS (E.P_fn M) M := by
    simpa only [one_mul] using mul_le_mul hK hLambda zero_le_one (zero_le_one.trans hK)
  have hle : factor ≤ factor * ((E.P_fn M).K_s * SparseCore.coreLambdaS (E.P_fn M) M) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hprod hf
  push_cast
  change factor ≤ SparseCore.gammaLEnv E M
  unfold SparseCore.gammaLEnv
  apply le_trans _ (le_max_right _ _)
  rw [hGrowth]
  calc
    factor ≤ factor * ((E.P_fn M).K_s * SparseCore.coreLambdaS (E.P_fn M) M) := hle
    _ ≤ factor * ((E.P_fn M).K_s * SparseCore.coreLambdaS (E.P_fn M) M) + 11 * 115 :=
      le_add_of_nonneg_right (by positivity)
    _ = _ := by dsimp [factor]; ring

/-- An exact length factor leaves only the product of the coefficient
and logarithm factors to enclose in the second growth term. -/
theorem initSparseCoreSecondGrowth_error
    (E : SparseCore.SparseCoreEnv) (M growth : ℕ)
    {upper error : ℝ} (hGrowth : (E.P_fn M).γ_ℓ = growth)
    (herror : 0 ≤ upper - (E.P_fn M).K_s * SparseCore.coreLambdaS (E.P_fn M) M)
    (hbudget : upper - (E.P_fn M).K_s * SparseCore.coreLambdaS (E.P_fn M) M ≤ error) :
    let factor := 11 * ((E.L : ℝ) + 1) * growth * (E.B_fn M : ℝ) *
      (2 * (E.d_fn M : ℝ) + 190)
    let term := 11 * (((E.L : ℝ) + 1) * (E.P_fn M).K_s * (E.P_fn M).γ_ℓ *
      SparseCore.coreLambdaS (E.P_fn M) M * (E.B_fn M : ℝ) *
      (2 * (E.d_fn M : ℝ) + 190) + 115)
    0 ≤ (factor * upper + 11 * 115) - term ∧
      (factor * upper + 11 * 115) - term ≤ factor * error := by
  dsimp only
  rw [hGrowth]
  let factor := 11 * ((E.L : ℝ) + 1) * growth * (E.B_fn M : ℝ) *
    (2 * (E.d_fn M : ℝ) + 190)
  have hfactor : 0 ≤ factor := by dsimp [factor]; positivity
  have heq : factor * upper + 11 * 115 -
      11 * (((E.L : ℝ) + 1) * (E.P_fn M).K_s * growth *
        SparseCore.coreLambdaS (E.P_fn M) M * (E.B_fn M : ℝ) *
        (2 * (E.d_fn M : ℝ) + 190) + 115) =
      factor * (upper - (E.P_fn M).K_s * SparseCore.coreLambdaS (E.P_fn M) M) := by
    dsimp [factor]
    ring
  rw [heq]
  exact ⟨mul_nonneg hfactor herror, mul_le_mul_of_nonneg_left hbudget hfactor⟩

/-- The affine part of the second term is exact in a dyadic block.
The constant is encoded at the same precision as the coefficient product. -/
theorem initSparseCoreSecondGrowth_numerator
    (E : SparseCore.SparseCoreEnv) (M growth upper precision : ℕ) :
    let factor := 11 * (E.L + 1) * growth * E.B_fn M * (2 * E.d_fn M + 190)
    let numerator := factor * upper + (11 * 115) * 2 ^ precision
    (numerator : ℝ) / (2 : ℝ) ^ precision =
      (factor : ℝ) * ((upper : ℝ) / (2 : ℝ) ^ precision) + 11 * 115 := by
  dsimp only
  push_cast
  rw [add_div, mul_div_assoc, mul_div_cancel_right₀ _ (by positivity)]
  norm_num

/-- A dyadic upper endpoint of the coefficient product gives the
required lower and upper bounds on the encoded second term. -/
theorem initSparseCoreSecondGrowth_bounds
    (E : SparseCore.SparseCoreEnv) (M growth upper precision : ℕ)
    {error : ℝ} (hGrowth : (E.P_fn M).γ_ℓ = growth)
    (hlo : (E.P_fn M).K_s * SparseCore.coreLambdaS (E.P_fn M) M ≤
      (upper : ℝ) / (2 : ℝ) ^ precision)
    (hhi : (upper : ℝ) / (2 : ℝ) ^ precision -
      (E.P_fn M).K_s * SparseCore.coreLambdaS (E.P_fn M) M ≤ error) :
    let factor := 11 * (E.L + 1) * growth * E.B_fn M * (2 * E.d_fn M + 190)
    let value := ((factor * upper + (11 * 115) * 2 ^ precision : ℕ) : ℝ) / (2 : ℝ) ^ precision
    let term := 11 * (((E.L : ℝ) + 1) * (E.P_fn M).K_s * (E.P_fn M).γ_ℓ *
      SparseCore.coreLambdaS (E.P_fn M) M * (E.B_fn M : ℝ) *
      (2 * (E.d_fn M : ℝ) + 190) + 115)
    term ≤ value ∧ value ≤ term + (factor : ℝ) * error := by
  dsimp only
  rw [initSparseCoreSecondGrowth_numerator]
  push_cast
  obtain ⟨hl, hu⟩ := initSparseCoreSecondGrowth_error E M growth hGrowth (sub_nonneg.mpr hlo) hhi
  exact ⟨sub_nonneg.mp hl, sub_le_iff_le_add.mp hu |>.trans_eq (add_comm _ _)⟩

/-- Combine the two fine endpoint budgets for the sparse-core growth
factor. The sparsifier length factor enters these terms through the
parameters of the sparse-core envelope. -/
theorem initSparseCoreThresholdGrowth_bounds
    (E : SparseCore.SparseCoreEnv) (M d : ℕ)
    {a b upperA upperB scale : ℝ}
    (hA : a = SparseCore.coreE82Len E.L (E.P_fn M))
    (hB : b = 11 * (((E.L : ℝ) + 1) * (E.P_fn M).K_s * (E.P_fn M).γ_ℓ *
      SparseCore.coreLambdaS (E.P_fn M) M * (E.B_fn M : ℝ) *
      (2 * (E.d_fn M : ℝ) + 190) + 115))
    (ha : a ≤ upperA) (hb : b ≤ upperB)
    (ha' : upperA + 1 / scale ≤ a + 1 / ((d : ℝ) + 1))
    (hb' : upperB + 1 / scale ≤ b + 1 / ((d : ℝ) + 1)) :
    (SparseCore.sparseCoreParams E).γ_ℓ M ≤ max upperA upperB ∧
      max upperA upperB + 1 / scale ≤
        (SparseCore.sparseCoreParams E).γ_ℓ M + 1 / ((d : ℝ) + 1) := by
  have he : (SparseCore.sparseCoreParams E).γ_ℓ M = max a b := by
    rw [hA, hB]
    rfl
  rw [he]
  exact rebuildGrowth_max_budget ha hb ha' hb'

/-- Exact first-term arithmetic and the enclosed coefficient product
suffice for the combined budget, including one coarse unit for rounding. -/
theorem initSparseCoreGrowthNumerators_bounds
    (E : SparseCore.SparseCoreEnv) (M d growth upper P P' scale e : ℕ)
    (hscale : scale = 2 ^ e) (heP : e ≤ P) (heP' : e ≤ P')
    {error : ℝ} (hGrowth : (E.P_fn M).γ_ℓ = growth)
    (hlo : (E.P_fn M).K_s * SparseCore.coreLambdaS (E.P_fn M) M ≤
      (upper : ℝ) / (2 : ℝ) ^ P')
    (hhi : (upper : ℝ) / (2 : ℝ) ^ P' -
      (E.P_fn M).K_s * SparseCore.coreLambdaS (E.P_fn M) M ≤ error)
    (hcoarse : 1 / (scale : ℝ) ≤ 1 / ((d : ℝ) + 1))
    (hfine : ((11 * (E.L + 1) * growth * E.B_fn M * (2 * E.d_fn M + 190) : ℕ) : ℝ) *
      error + 1 / (scale : ℝ) ≤ 1 / ((d : ℝ) + 1)) :
    let a := 3 ^ E.L * growth ^ (E.L + 1) * 2 ^ P
    let b := 11 * (E.L + 1) * growth * E.B_fn M * (2 * E.d_fn M + 190) * upper +
      (11 * 115) * 2 ^ P'
    let bound := max ((a : ℝ) / ↑(scale * 2 ^ (P - e)))
      ((b : ℝ) / ↑(scale * 2 ^ (P' - e)))
    (SparseCore.sparseCoreParams E).γ_ℓ M ≤ bound ∧
      bound + 1 / (scale : ℝ) ≤
        (SparseCore.sparseCoreParams E).γ_ℓ M + 1 / ((d : ℝ) + 1) := by
  dsimp only
  have ha := initSparseCoreFirstGrowth_exact E M growth P hGrowth
  obtain ⟨hb, hb'⟩ := initSparseCoreSecondGrowth_bounds E M growth upper P' hGrowth hlo hhi
  refine rebuildGrowth_dyadic_max_budget hscale heP heP' rfl ha.ge hb ?_ ?_
  · rw [ha]
    exact add_le_add_right hcoarse _
  · exact (add_le_add_left hb' _).trans (by rw [add_assoc]; exact add_le_add_right hfine _)

/-- The exact first term and the dyadic second term certify the input
to the table writer that uses one rounding buffer. -/
theorem initSparseCoreCoarseGrowth_bounds
    (E : SparseCore.SparseCoreEnv) (M d growth upper P scale e : ℕ)
    (hscale : scale = 2 ^ e) (heP : e ≤ P)
    {error : ℝ} (hGrowth : (E.P_fn M).γ_ℓ = growth)
    (hlo : (E.P_fn M).K_s * SparseCore.coreLambdaS (E.P_fn M) M ≤
      (upper : ℝ) / (2 : ℝ) ^ P)
    (hhi : (upper : ℝ) / (2 : ℝ) ^ P -
      (E.P_fn M).K_s * SparseCore.coreLambdaS (E.P_fn M) M ≤ error)
    (hcoarse : 1 / (scale : ℝ) ≤ 1 / ((d : ℝ) + 1))
    (hfine : ((11 * (E.L + 1) * growth * E.B_fn M * (2 * E.d_fn M + 190) : ℕ) : ℝ) *
      error + 1 / (scale : ℝ) ≤ 1 / ((d : ℝ) + 1)) :
    let first := 3 ^ E.L * growth ^ (E.L + 1)
    let second := 11 * (E.L + 1) * growth * E.B_fn M * (2 * E.d_fn M + 190) * upper +
      (11 * 115) * 2 ^ P
    let bound := max (first : ℝ) ((second : ℝ) / ↑(scale * 2 ^ (P - e)))
    (SparseCore.sparseCoreParams E).γ_ℓ M ≤ bound ∧
      bound + 1 / (scale : ℝ) ≤
        (SparseCore.sparseCoreParams E).γ_ℓ M + 1 / ((d : ℝ) + 1) := by
  have h := initSparseCoreGrowthNumerators_bounds E M d growth upper e P scale e
    hscale le_rfl heP hGrowth hlo hhi hcoarse hfine
  dsimp only at h ⊢
  have hs : (scale : ℝ) ≠ 0 := by rw [hscale]; positivity
  simp only [Nat.sub_self, pow_zero, Nat.mul_one, ← hscale] at h
  rw [Nat.cast_mul, mul_div_cancel_right₀ _ hs] at h
  exact h

/-- Compute the machine sparsifier factors, then install the integer
threshold table using the exact scaled length factor. -/
@[expose] def initMergedSparsifierThresholds (entry decK thr cDeg witnessDen : ℕ) : Stmt :=
  initMergedSparsifierFactors entry decK thr cDeg witnessDen ;;
  initScaledGrowthThresholdTable

/-- The factor allocations and threshold table have disjoint storage.
Every threshold has both bounds against the model update budget. -/
theorem initMergedSparsifierThresholds_runs
    (TP : Chain.SparseCoreParams) (C : Chain.ChainParams)
    {w Kγ c Kint cw entry decK thr cDeg witnessDen M heap scale vertices : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p entry (initMachinePathFactorsContract w Kγ c Kint cw))
    (hK : 1 ≤ decK) (hM : st.regs 23 = M) (hh : st.regs 98 = heap)
    (hz : ZeroFrom st.mem heap)
    (hs : st.regs 4 = scale) (hscale : 0 < scale)
    (hm : 4 * M + 2 < 2 ^ w) (hcube : (Nat.log 2 (4 * M + 2) + 2) ^ 3 < 2 ^ w)
    (hcPos : 0 < cDeg) (hcWord : cDeg < 2 ^ w) (hw : heap + 4 < 2 ^ w)
    (hw' : 1 < 2 ^ w) (hroom : heap + 4 + C.d + 1 < 2 ^ w)
    (impl : Spanner.PathDSImpl) {phiConst : ℝ}
    (hparams : impl.params = pathDSParams Kγ c Kint cw)
    (hWitness : witnessDen = Nat.ceil (1 / phiConst))
    (hGrowth : Spanner.capGammaL cDeg phiConst (Spanner.pathDSTool_of_impl impl)
      (1 / (Expander.maxPhiDenOf decK thr M : ℝ)) M = TP.γ_ℓ (C.M₀ ^ 2))
    (hTP : TP.Valid) (hγM : TP.γ_ℓ (C.M₀ ^ 2) ≤ C.M₀)
    (hγk : TP.γ_ℓ (C.M₀ ^ 2) ≤ C.k)
    (h22 : st.regs 22 = C.M₀) (h14 : st.regs 14 = Nat.clog 2 (vertices + 2))
    (h76 : st.regs 76 = C.k) (h75 : st.regs 75 = C.d)
    (hden : 3 * C.k * Nat.clog 2 (vertices + 2) ^ 2 < 2 ^ w)
    (hcapacity : (3 * C.M₀ ^ 2 + 1) * (C.M₀ * (2 * scale) ^ (C.d + 1)) < 2 ^ w) :
    let den := Expander.maxPhiDenOf decK thr M
    let cap := Spanner.capM_W cDeg (1 / (den : ℝ)) M
    let growth := (max (gExpImpl Kγ c Kint den M) (gExpImpl Kγ c Kint witnessDen cap)) ^ 2
    let len := scale * growth
    let query := scale * max (gQueryImpl Kγ c Kint den M) (gQueryImpl Kγ c Kint witnessDen cap)
    let contract := initMachinePathFactorsContract w Kγ c Kint cw
    cDeg * den < 2 ^ w → cDeg * den * M + 1 < 2 ^ w →
    0 < witnessDen → witnessDen < 2 ^ w →
    max 24 (4 * cw + 8) *
      (Nat.log 2 (den + M + gExpImpl Kγ c Kint den M + gDelImpl Kint den M + 2) + 1) ≤ w →
    max 24 (4 * cw + 8) *
      (Nat.log 2 (witnessDen + cap + gExpImpl Kγ c Kint witnessDen cap + gDelImpl Kint witnessDen cap + 2) + 1) ≤ w →
    len < 2 ^ w → query < 2 ^ w →
    ∃ out cost, Runs w p ω (initMergedSparsifierThresholds entry decK thr cDeg witnessDen)
        st .normal out cost ∧
      out.regs 83 = heap + 4 ∧ out.regs 98 = heap + 4 + C.d + 1 ∧
      (∀ j ≤ C.d, out.mem (heap + 4 + j) =
        Chain.concreteLevelRebuildCount C.M₀ C.k growth 1 j vertices ∧
        (out.mem (heap + 4 + j) : ℝ) ≤ Chain.SparseCoreTool.updateThreshold C.k
          (Chain.levelM TP C j) vertices ∧
        Chain.SparseCoreTool.updateThreshold C.k (Chain.levelM TP C j) vertices ≤
          48 * ((out.mem (heap + 4 + j) : ℝ) + 1)) ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (heap + 4 + C.d + 1) ∧
      cost ≤ 120 * (Nat.log 2 (4 * M + 2) + decK * (Expander.rOf (4 * M)) ^ 2 + 4) +
        contract.cost [den, M, heap] st.mem + contract.cost [witnessDen, cap, heap + 2] st.mem +
        50 * C.d + 193 := by
  dsimp only
  intro hc hfit hwpos hwword hcw hcw' hlen hquery
  have hγ := (initMachineThresholdGrowth_eq Kγ c Kint
    (Expander.maxPhiDenOf decK thr M) M scale cDeg phiConst (Spanner.pathDSTool_of_impl impl) hscale
    (fun phi cap => (initMachinePathTool_factors impl hparams phi cap).1)).trans hGrowth
  rw [← hWitness] at hγ
  obtain ⟨mid, c₁, hr, h50, _, _, _, _, _, h98, _, hz', hk, hf, hc₁⟩ :=
    initMergedSparsifierFactors_runs (ω := ω) himpl hK hM hh hz hs hscale hm hcube
      hcPos hcWord hw hc hfit hwpos hwword hcw hcw' hlen hquery
  obtain ⟨out, ht, h83, hout, htable, hf', hzero⟩ :=
    initScaledGrowthThresholdTable_runs (ω := ω) TP C hw' hroom hz' h50
      ((hk 4 (by decide)).trans hs) hscale hTP hγM hγk hγ
      ((hk 22 (by decide)).trans h22) ((hk 14 (by decide)).trans h14)
      h98 ((hk 76 (by decide)).trans h76) ((hk 75 (by decide)).trans h75) hden hcapacity
  have htable' (j : ℕ) (hj : j ≤ C.d) := htable j hj
  simp only [Chain.concreteLevelRebuildCount_exact_scale _ _ _ _ _ _ C.hk hscale] at htable'
  exact ⟨out, c₁ + (50 * C.d + 81) + 1,
    runs_seq_iff.mpr (Or.inr ⟨mid, c₁, _, hr, ht, rfl⟩), h83, hout, htable',
    fun x hx => (hf' x (by omega)).trans (hf x (Or.inl hx)), hzero, by omega⟩

/-- Write the sparse-core table directly from two fine dyadic endpoint
certificates for the explicit growth terms. -/
theorem initSparseCoreIntegerThresholdTable_runs
    (E : SparseCore.SparseCoreEnv) (C : Chain.ChainParams)
    {w h shift round addr limbs e heap P upper addr' limbs' P' upper' vertices scale : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hshift : MeetsContract w p shift (Num.shiftLeftContract w h))
    (hround : MeetsContract w p round (initDepthEndpointContract w h))
    (ha : st.regs 117 = addr) (hL : st.regs 118 = limbs)
    (he : st.regs 119 = e) (hh : st.regs 115 = heap) (hP : st.regs 121 = P)
    (ha' : st.regs 123 = addr') (hL' : st.regs 124 = limbs') (hP' : st.regs 125 = P')
    (hw : 1 < 2 ^ w) (hword : h < 2 ^ w) (heword : e < 2 ^ w)
    (hdvd : h ∣ P) (heP : e ≤ P) (hfrac : P / h ≤ limbs)
    (hdvd' : h ∣ P') (heP' : e ≤ P') (hfrac' : P' / h ≤ limbs')
    (hbelow : addr + limbs ≤ heap) (hbelow' : addr' + limbs' ≤ heap)
    (hv : Num.Valid st.mem addr h limbs) (hv' : Num.Valid st.mem addr' h limbs')
    (hz : ZeroFrom st.mem heap) (hroom : heap + limbs + limbs' < 2 ^ w)
    (hvalue : Num.intVal st.mem addr h limbs = (upper : ℤ))
    (hvalue' : Num.intVal st.mem addr' h limbs' = (upper' : ℤ))
    (hfit : Num.Fits h limbs ((upper : ℤ) * (2 : ℤ) ^ e))
    (hfit' : Num.Fits h limbs' ((upper' : ℤ) * (2 : ℤ) ^ e))
    (hrounded : upper * 2 ^ e / 2 ^ P + 1 < 2 ^ w)
    (hrounded' : upper' * 2 ^ e / 2 ^ P' + 1 < 2 ^ w)
    (h30 : st.regs 30 = scale) (hscale : scale = 2 ^ e)
    (hγM : (SparseCore.sparseCoreParams E).γ_ℓ (C.M₀ ^ 2) ≤ C.M₀)
    (hγk : (SparseCore.sparseCoreParams E).γ_ℓ (C.M₀ ^ 2) ≤ C.k)
    (hbase : heap + limbs + limbs' + C.d + 1 < 2 ^ w)
    {growth productUpper : ℕ} {error : ℝ}
    (hGrowth : (E.P_fn (C.M₀ ^ 2)).γ_ℓ = growth)
    (hfirst : upper = 3 ^ E.L * growth ^ (E.L + 1) * 2 ^ P)
    (hsecond : upper' = 11 * (E.L + 1) * growth * E.B_fn (C.M₀ ^ 2) *
      (2 * E.d_fn (C.M₀ ^ 2) + 190) * productUpper + (11 * 115) * 2 ^ P')
    (hloProduct : (E.P_fn (C.M₀ ^ 2)).K_s *
      SparseCore.coreLambdaS (E.P_fn (C.M₀ ^ 2)) (C.M₀ ^ 2) ≤
        (productUpper : ℝ) / (2 : ℝ) ^ P')
    (hhiProduct : (productUpper : ℝ) / (2 : ℝ) ^ P' -
      (E.P_fn (C.M₀ ^ 2)).K_s * SparseCore.coreLambdaS (E.P_fn (C.M₀ ^ 2)) (C.M₀ ^ 2) ≤ error)
    (hcoarse : 1 / (scale : ℝ) ≤ 1 / ((C.d : ℝ) + 1))
    (hfine : ((11 * (E.L + 1) * growth * E.B_fn (C.M₀ ^ 2) *
      (2 * E.d_fn (C.M₀ ^ 2) + 190) : ℕ) : ℝ) * error + 1 / (scale : ℝ) ≤
        1 / ((C.d : ℝ) + 1))
    (h22 : st.regs 22 = C.M₀) (h14 : st.regs 14 = Nat.clog 2 (vertices + 2))
    (h76 : st.regs 76 = C.k) (h75 : st.regs 75 = C.d)
    (hden : 3 * C.k * Nat.clog 2 (vertices + 2) ^ 2 < 2 ^ w)
    (hcapacity : (3 * C.M₀ ^ 2 + 1) * (C.M₀ * (2 * scale) ^ (C.d + 1)) < 2 ^ w) :
    let a := (upper + 2 ^ (P - e) - 1) / 2 ^ (P - e)
      |> fun x => max x ((upper' + 2 ^ (P' - e) - 1) / 2 ^ (P' - e))
    let base := heap + limbs + limbs'
    ∃ out cost, Runs w p ω (initTwoGrowthIntegerThresholdTable shift round h) st .normal out cost ∧
      out.regs 83 = base ∧ out.regs 98 = base + C.d + 1 ∧
      (∀ j ≤ C.d, out.mem (base + j) = Chain.concreteLevelRebuildCount C.M₀ C.k a scale j vertices ∧
        (out.mem (base + j) : ℝ) ≤ Chain.SparseCoreTool.updateThreshold C.k (Chain.levelM (SparseCore.sparseCoreParams E) C j) vertices ∧
        Chain.SparseCoreTool.updateThreshold C.k (Chain.levelM (SparseCore.sparseCoreParams E) C j) vertices ≤
          48 * ((out.mem (base + j) : ℝ) + 1)) ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (base + C.d + 1) ∧
      cost ≤ 60 * (limbs + limbs') + 50 * C.d + 299 := by
  obtain ⟨hlo, hhi⟩ :=
    initSparseCoreGrowthNumerators_bounds E (C.M₀ ^ 2) C.d growth productUpper P P' scale e
      hscale heP heP' hGrowth hloProduct hhiProduct hcoarse hfine
  rw [← hfirst, ← hsecond] at hlo hhi
  exact initTwoGrowthIntegerThresholdTable_runs (SparseCore.sparseCoreParams E) C
    hshift hround ha hL he hh hP ha' hL' hP' hw hword heword hdvd heP hfrac
    hdvd' heP' hfrac' hbelow hbelow' hv hv' hz hroom hvalue hvalue' hfit hfit'
    hrounded hrounded' h30 hscale (SparseCore.sparseCoreParams_valid E) hγM hγk hbase hlo hhi h22 h14 h76 h75 hden hcapacity

end MinCostFlow.MinRatio
