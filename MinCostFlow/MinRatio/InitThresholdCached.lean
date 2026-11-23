module

public import MinCostFlow.MinRatio.InitThreshold
public import MinCostFlow.MinRatio.InitLevelSize
import MinCostFlow.MinRatio.ShiftForestScan
import MinCostFlow.Num.Representation

/-!
# Reuse of the vertex logarithm across rebuild thresholds

Use each level's ceiling certificate before checking its threshold.
Preserve the shared logarithm inputs and level products across the store.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain

/-- Reuse the allocated logarithm when checking a later threshold.
A failed level-size check clears the store flag and leaves memory alone. -/
@[expose] def guardInitThresholdFromVertexLog (pack : ℕ) : Stmt :=
  .cond (.reg 18) (storeInitThresholdFromVertexLog pack) (.assign 10 (.const 0))

/-- A guarded store from the cached logarithm changes at most its
destination word. In particular the logarithm block can be reused. -/
theorem guardInitThresholdFromVertexLog_runs
    {w pack cell budget threshold : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hflag : st.regs 18 = 0 ∨ st.regs 18 = 1)
    (hrun : st.regs 18 = 1 →
      ∃ out c, Runs w p ω (storeInitThresholdFromVertexLog pack) st .normal out c ∧
        (out.regs 10 = 0 ∧ out.mem = st.mem ∨
          out.regs 10 = 1 ∧ out.mem cell = threshold) ∧
        (∀ a ≠ cell, out.mem a = st.mem a) ∧ c ≤ budget) :
    ∃ out c, Runs w p ω (guardInitThresholdFromVertexLog pack) st .normal out c ∧
      (out.regs 10 = 0 ∧ out.mem = st.mem ∨ out.regs 10 = 1 ∧ out.mem cell = threshold) ∧
      (∀ a ≠ cell, out.mem a = st.mem a) ∧ c ≤ budget + 4 := by
  rcases hflag with hzero | hone
  · let out := { st with regs := Function.update st.regs 10 0 }
    have hclear : Runs w p ω (.assign 10 (.const 0)) st .normal out 2 :=
      runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by positivity], rfl, rfl, rfl⟩
    exact ⟨out, 4, runs_cond_iff.mpr ⟨0, 2, by simp [Expr.eval, hzero], hclear, rfl⟩,
      Or.inl ⟨by simp [out], rfl⟩, fun _ _ => rfl, by omega⟩
  · obtain ⟨out, c, hr, hpost, hframe, hc⟩ := hrun hone
    exact ⟨out, c + 2, runs_cond_iff.mpr ⟨1, c, by simp [Expr.eval, hone], hr,
      by simp [Expr.size]; omega⟩, hpost, hframe, by omega⟩

/-- A certified level size and the cached logarithm suffice to check
the threshold without allocating any additional scratch memory. -/
theorem guardInitThresholdFromVertexLog_fromLevelCheck_runs
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
    (hflag : st.regs 18 = 0 ∨ st.regs 18 = 1)
    (h0 : st.regs 18 = 1 → st.regs 0 = levelM TP P i) (h1 : st.regs 1 = P.k)
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
    ∃ out c, Runs w p ω (guardInitThresholdFromVertexLog pack) st .normal out c ∧
      (out.regs 10 = 0 ∧ out.mem = st.mem ∨
        out.regs 10 = 1 ∧ out.mem cell = rebuildThresholdWord TP P N i) ∧
      (∀ a ≠ cell, out.mem a = st.mem a) ∧
      (∀ r ≥ 14, out.regs r = st.regs r) ∧ c ≤ 25 * limbs + 90 := by
  dsimp only
  intro hlo hhi hs hn hu hl hqw hc
  have hrun := guardInitThresholdFromVertexLog_runs (ω := ω) (pack := pack)
    (p := p) (w := w) (st := st) (cell := cell) (budget := 25 * limbs + 86)
    (threshold := rebuildThresholdWord TP P N i) hflag
  obtain ⟨out, c, hr, hpost, hframe, hcost⟩ := hrun (fun hone =>
    storeInitThresholdFromVertexLog_runs (ω := ω) TP P i hpack hret hL hP hq hle hw hwidth
      hv hqpos hqprec herr hfit (h0 hone) h1 hcell hlo hhi hs hn hu hl hqw hc)
  have hreg (r : ℕ) (hr' : 14 ≤ r) : out.regs r = st.regs r := by
    apply runs_preserves_above hr' _ hr
    rfl
  exact ⟨out, c, hr, hpost, hframe, hreg, by omega⟩

/-- Advance the level products, certify the next size, and check its
threshold using the cached vertex logarithm. -/
@[expose] def checkInitNextThreshold (pack : ℕ) : Stmt :=
  selectInitNextLevelSize ;; guardInitThresholdFromVertexLog pack

/-- Check and store the exact next threshold when both enclosures
determine the required integers. The level product words advance even
when the threshold cannot be certified. -/
theorem checkInitNextThreshold_fromProducts_runs
    (TP : SparseCoreParams) (P : ChainParams) (i : ℕ)
    {w h pack ret limbs precision accuracy N cell stretchLo stretchHi stretchScale : ℕ}
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
    (h1 : st.regs 1 = P.k)
    (h14 : st.regs 14 = P.M₀ * stretchLo ^ (i + 1))
    (h15 : st.regs 15 = P.M₀ * stretchHi ^ (i + 1))
    (h16 : st.regs 16 = stretchScale * (stretchScale * P.k) ^ i)
    (h19 : st.regs 19 = stretchLo) (h20 : st.regs 20 = stretchHi)
    (h21 : st.regs 21 = stretchScale * P.k)
    (hs : 0 < stretchScale) (hu : 0 < P.M₀ * stretchHi ^ (i + 2))
    (hlo : (stretchLo : ℝ) / stretchScale ≤ TP.γ_ℓ (P.M₀ ^ 2))
    (hhi : TP.γ_ℓ (P.M₀ ^ 2) ≤ (stretchHi : ℝ) / stretchScale)
    (hlw : P.M₀ * stretchLo ^ (i + 2) < 2 ^ w) (huw : P.M₀ * stretchHi ^ (i + 2) < 2 ^ w)
    (hdw : stretchScale * (stretchScale * P.k) ^ (i + 1) < 2 ^ w)
    (hone : 1 < 2 ^ w)
    (hcell : st.regs 11 = cell) :
    let approx := (Num.intVal st.mem (ret - limbs) h limbs).toNat
    let error : ℕ := 2 ^ (precision - accuracy)
    let scale : ℕ := 2 ^ precision
    let lower := (approx - error) ^ 2
    let upper := (approx + error) ^ 2
    let scaleSq := scale ^ 2
    let num := levelM TP P (i + 1) * scaleSq
    let q := num / (P.k * upper)
    lower < 2 ^ w → upper < 2 ^ w → scaleSq < 2 ^ w →
    num < 2 ^ w → P.k * upper < 2 ^ w → P.k * lower < 2 ^ w →
    q + 1 < 2 ^ w → (q + 1) * (P.k * lower) < 2 ^ w →
    ∃ out c, Runs w p ω (checkInitNextThreshold pack) st .normal out c ∧
      (out.regs 10 = 0 ∧ out.mem = st.mem ∨
        out.regs 10 = 1 ∧ out.mem cell = rebuildThresholdWord TP P N (i + 1)) ∧
      (∀ a ≠ cell, out.mem a = st.mem a) ∧
      out.regs 14 = P.M₀ * stretchLo ^ (i + 2) ∧
      out.regs 15 = P.M₀ * stretchHi ^ (i + 2) ∧
      out.regs 16 = stretchScale * (stretchScale * P.k) ^ (i + 1) ∧
      (∀ r ≥ 19, out.regs r = st.regs r) ∧ c ≤ 25 * limbs + 124 := by
  dsimp only
  intro hlow hupp hscale hn hku hkl hqw hcut
  obtain ⟨mid, hr, hsize, _, hflag, hloReg, hhiReg, hden, hkeep, hm, _⟩ :=
    selectInitNextLevelSize_runs (p := p) (ω := ω) TP P i stretchLo stretchHi stretchScale
      h14 h15 h16 h19 h20 h21 hs hu hlo hhi hlw huw hdw hone
  have hk (r : ℕ) (h : r ≠ 0 ∧ r ≠ 14 ∧ r ≠ 15 ∧ r ≠ 16 ∧ r ≠ 17 ∧ r ≠ 18) :
      mid.regs r = st.regs r := hkeep r h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
  obtain ⟨out, c, hr', hres, hframe, hreg, hcost⟩ :=
    guardInitThresholdFromVertexLog_fromLevelCheck_runs (ω := ω) TP P (i + 1) hpack
      ((hk 99 (by decide)).trans hret) ((hk 67 (by decide)).trans hL)
      ((hk 68 (by decide)).trans hP) ((hk 100 (by decide)).trans hq)
      hle hw hwidth (hm.symm ▸ hv) hqpos hqprec (hm.symm ▸ herr) (hm.symm ▸ hfit) hflag hsize
      ((hk 1 (by decide)).trans h1) ((hk 11 (by decide)).trans hcell)
      (hm.symm ▸ hlow) (hm.symm ▸ hupp) hscale hn (hm.symm ▸ hku) (hm.symm ▸ hkl)
      (hm.symm ▸ hqw) (hm.symm ▸ hcut)
  refine ⟨out, 33 + c + 1, runs_seq_iff.mpr (Or.inr ⟨mid, 33, c, hr, hr', rfl⟩),
    by simpa only [hm] using hres, fun a ha => (hframe a ha).trans (congrFun hm a),
    (hreg 14 (by decide)).trans hloReg, (hreg 15 (by decide)).trans hhiReg,
    (hreg 16 (by decide)).trans hden, ?_, by omega⟩
  intro r h
  exact (hreg r (by omega)).trans (hk r ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩)

/-- Load the branching factor and compute the current threshold cell.
Registers 53 and 54 hold the table base and current level index. -/
@[expose] def prepareInitThresholdCell : Stmt :=
  .assign 1 (.reg 55) ;;
  .assign 11 (.bin .add (.reg 53) (.reg 54))

/-- Address calculation uses the runtime table base and level index,
and preserves the cached logarithm and level product words. -/
theorem prepareInitThresholdCell_runs {w base level k : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hb : st.regs 53 = base) (hi : st.regs 54 = level) (hk : st.regs 55 = k)
    (hw : base + level < 2 ^ w) :
    ∃ out, Runs w p ω prepareInitThresholdCell st .normal out 7 ∧
      out.regs 1 = k ∧ out.regs 11 = base + level ∧
      (∀ r, r ≠ 1 → r ≠ 11 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  let mid := { st with regs := Function.update st.regs 1 k }
  let out := { mid with regs := Function.update mid.regs 11 (base + level) }
  have hr₁ : Runs w p ω (.assign 1 (.reg 55)) st .normal mid 2 :=
    runs_assign_iff.mpr ⟨k, by simp [Expr.eval, hk], rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign 11 (.bin .add (.reg 53) (.reg 54))) mid .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, mid, hb, hi, hw], rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 2, 4, hr₁, hr₂, rfl⟩),
    by simp [out, mid], by simp [out], fun r h1 h11 => by simp [out, mid, h1, h11], rfl, rfl⟩

/-- Advance the runtime index and prepare the next threshold destination. -/
@[expose] def prepareInitNextThresholdCell : Stmt :=
  .assign 54 (.bin .add (.reg 54) (.const 1)) ;; prepareInitThresholdCell

/-- The next destination is the table base plus the successor index. -/
theorem prepareInitNextThresholdCell_runs {w base level k : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hb : st.regs 53 = base) (hi : st.regs 54 = level) (hk : st.regs 55 = k)
    (hw : base + (level + 1) < 2 ^ w) :
    ∃ out, Runs w p ω prepareInitNextThresholdCell st .normal out 12 ∧
      out.regs 54 = level + 1 ∧ out.regs 1 = k ∧ out.regs 11 = base + (level + 1) ∧
      (∀ r, r ≠ 1 → r ≠ 11 → r ≠ 54 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  let mid := { st with regs := Function.update st.regs 54 (level + 1) }
  have hstep : Runs w p ω (.assign 54 (.bin .add (.reg 54) (.const 1))) st .normal mid 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hi, show level + 1 < 2 ^ w by omega,
      show 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
  obtain ⟨out, hr, hbranch, hcell, hkeep, hm, hp⟩ :=
    prepareInitThresholdCell_runs (p := p) (ω := ω) (st := mid)
      (by simpa [mid] using hb) (by simp [mid]) (by simpa [mid] using hk) hw
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 4, 7, hstep, hr, rfl⟩),
    (hkeep 54 (by decide) (by decide)).trans (by simp [mid]), hbranch, hcell,
    fun r h1 h11 h54 => (hkeep r h1 h11).trans (by simp [mid, h54]), hm, hp⟩

/-- Compute the next table address and run the checked threshold step. -/
@[expose] def writeInitNextThreshold (pack : ℕ) : Stmt :=
  prepareInitNextThresholdCell ;; checkInitNextThreshold pack

/-- The indexed step changes at most the next table cell and advances
the product words and runtime index together. -/
theorem writeInitNextThreshold_runs
    (TP : SparseCoreParams) (P : ChainParams) (i : ℕ)
    {w h pack ret limbs precision accuracy N base stretchLo stretchHi stretchScale : ℕ}
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
    (hb : st.regs 53 = base) (hi : st.regs 54 = i) (hk : st.regs 55 = P.k)
    (h14 : st.regs 14 = P.M₀ * stretchLo ^ (i + 1))
    (h15 : st.regs 15 = P.M₀ * stretchHi ^ (i + 1))
    (h16 : st.regs 16 = stretchScale * (stretchScale * P.k) ^ i)
    (h19 : st.regs 19 = stretchLo) (h20 : st.regs 20 = stretchHi)
    (h21 : st.regs 21 = stretchScale * P.k)
    (hs : 0 < stretchScale) (hu : 0 < P.M₀ * stretchHi ^ (i + 2))
    (hlo : (stretchLo : ℝ) / stretchScale ≤ TP.γ_ℓ (P.M₀ ^ 2))
    (hhi : TP.γ_ℓ (P.M₀ ^ 2) ≤ (stretchHi : ℝ) / stretchScale)
    (hlw : P.M₀ * stretchLo ^ (i + 2) < 2 ^ w) (huw : P.M₀ * stretchHi ^ (i + 2) < 2 ^ w)
    (hdw : stretchScale * (stretchScale * P.k) ^ (i + 1) < 2 ^ w)
    (hone : 1 < 2 ^ w)
    (hcell : base + (i + 1) < 2 ^ w) :
    let approx := (Num.intVal st.mem (ret - limbs) h limbs).toNat
    let error : ℕ := 2 ^ (precision - accuracy)
    let scale : ℕ := 2 ^ precision
    let lower := (approx - error) ^ 2
    let upper := (approx + error) ^ 2
    let scaleSq := scale ^ 2
    let num := levelM TP P (i + 1) * scaleSq
    let q := num / (P.k * upper)
    lower < 2 ^ w → upper < 2 ^ w → scaleSq < 2 ^ w →
    num < 2 ^ w → P.k * upper < 2 ^ w → P.k * lower < 2 ^ w →
    q + 1 < 2 ^ w → (q + 1) * (P.k * lower) < 2 ^ w →
    ∃ out c, Runs w p ω (writeInitNextThreshold pack) st .normal out c ∧
      (out.regs 10 = 0 ∧ out.mem = st.mem ∨
        out.regs 10 = 1 ∧ out.mem (base + (i + 1)) = rebuildThresholdWord TP P N (i + 1)) ∧
      (∀ a ≠ base + (i + 1), out.mem a = st.mem a) ∧
      out.regs 54 = i + 1 ∧ out.regs 14 = P.M₀ * stretchLo ^ (i + 2) ∧
      out.regs 15 = P.M₀ * stretchHi ^ (i + 2) ∧
      out.regs 16 = stretchScale * (stretchScale * P.k) ^ (i + 1) ∧
      (∀ r ≥ 19, r ≠ 54 → out.regs r = st.regs r) ∧ c ≤ 25 * limbs + 137 := by
  dsimp only
  intro hlow hupp hscale hn hku hkl hqw hcut
  obtain ⟨mid, hr, hindex, hbranch, hdest, hkeep, hm, _⟩ :=
    prepareInitNextThresholdCell_runs (p := p) (ω := ω) hb hi hk hcell
  have hreg (r : ℕ) (h : r ≠ 1 ∧ r ≠ 11 ∧ r ≠ 54) : mid.regs r = st.regs r :=
    hkeep r h.1 h.2.1 h.2.2
  obtain ⟨out, c, hr', hres, hframe, hloReg, hhiReg, hden, hkeep', hcost⟩ :=
    checkInitNextThreshold_fromProducts_runs (ω := ω) TP P i hpack
      ((hreg 99 (by decide)).trans hret) ((hreg 67 (by decide)).trans hL)
      ((hreg 68 (by decide)).trans hP) ((hreg 100 (by decide)).trans hq)
      hle hw hwidth (hm.symm ▸ hv) hqpos hqprec (hm.symm ▸ herr) (hm.symm ▸ hfit) hbranch
      ((hreg 14 (by decide)).trans h14) ((hreg 15 (by decide)).trans h15)
      ((hreg 16 (by decide)).trans h16) ((hreg 19 (by decide)).trans h19)
      ((hreg 20 (by decide)).trans h20) ((hreg 21 (by decide)).trans h21)
      hs hu hlo hhi hlw huw hdw hone hdest
      (hm.symm ▸ hlow) (hm.symm ▸ hupp) hscale hn (hm.symm ▸ hku)
      (hm.symm ▸ hkl) (hm.symm ▸ hqw) (hm.symm ▸ hcut)
  refine ⟨out, 12 + c + 1, runs_seq_iff.mpr (Or.inr ⟨mid, 12, c, hr, hr', rfl⟩),
    by simpa only [hm] using hres, fun a ha => (hframe a ha).trans (congrFun hm a),
    (hkeep' 54 (by decide)).trans hindex, hloReg, hhiReg, hden, ?_, by omega⟩
  intro r hr hne
  exact (hkeep' r hr).trans (hreg r ⟨by omega, by omega, hne⟩)

/-- Fill later threshold cells in order, stopping on the first
inconclusive check or after the runtime last level in register 56. -/
@[expose] def writeInitThresholdTail (pack : ℕ) : Stmt :=
  .loop (.bin .and (.reg 10) (.bin .lt (.reg 54) (.reg 56)))
    (writeInitNextThreshold pack)

/-- Iterate the indexed threshold step with a decreasing number of
remaining levels. The invariant may retain the certified table prefix
when an enclosure fails. -/
theorem writeInitThresholdTail_runs
    {w pack last budget : ℕ} {p : Program} {ω : ℕ → Bool}
    (inv : ℕ → State → Prop) (hw : 1 < 2 ^ w)
    (hstep : ∀ {i st}, i < last → st.regs 10 = 1 →
      st.regs 54 = i → st.regs 56 = last → inv i st →
      ∃ mid c, Runs w p ω (writeInitNextThreshold pack) st .normal mid c ∧
        mid.regs 54 = i + 1 ∧ mid.regs 56 = last ∧ inv (i + 1) mid ∧
        (mid.regs 10 = 0 ∨ mid.regs 10 = 1) ∧ c ≤ budget)
    {i : ℕ} {st : State} (hi : i ≤ last) (hindex : st.regs 54 = i)
    (hlast : st.regs 56 = last) (hflag : st.regs 10 = 0 ∨ st.regs 10 = 1) (hinv : inv i st) :
    ∃ out c j, Runs w p ω (writeInitThresholdTail pack) st .normal out c ∧
      i ≤ j ∧ j ≤ last ∧ out.regs 54 = j ∧ inv j out ∧
      (out.regs 10 = 0 ∨ j = last) ∧ c ≤ (budget + 6) * (last - i) + 6 := by
  by_cases hlive : i < last ∧ st.regs 10 = 1
  · obtain ⟨mid, c, hr, hidx, hlast', hinv', hflag', hc⟩ :=
      hstep hlive.1 hlive.2 hindex hlast hinv
    obtain ⟨out, d, j, hrun, hj, hj', hidx', hinv'', hstop, hd⟩ :=
      writeInitThresholdTail_runs inv hw hstep (by omega) hidx hlast' hflag' hinv'
    have he : Expr.eval w st (.bin .and (.reg 10) (.bin .lt (.reg 54) (.reg 56))) =
        some 1 := by
      simp [Expr.eval, BinOp.eval, hindex, hlast, hlive.1, hlive.2, hw]
    refine ⟨out, c + 6 + d, j, runs_loop_iff.mpr (Or.inr (Or.inr
      ⟨1, mid, c, d, he, by decide, hr, hrun, by simp [Expr.size]; omega⟩)),
      by omega, hj', hidx', hinv'', hstop, ?_⟩
    rw [show last - i = (last - (i + 1)) + 1 by omega, Nat.mul_add, Nat.mul_one]
    omega
  · have hstop : st.regs 10 = 0 ∨ i = last := by
      rcases hflag with hzero | hone
      · exact Or.inl hzero
      · exact Or.inr (by omega)
    have he : Expr.eval w st (.bin .and (.reg 10) (.bin .lt (.reg 54) (.reg 56))) =
        some 0 := by
      rcases hstop with hzero | heq
      · by_cases hlt : i < last <;>
          simp [Expr.eval, BinOp.eval, hindex, hlast, hzero, hlt, hw, show 0 < 2 ^ w by omega]
      · simp [Expr.eval, BinOp.eval, hindex, hlast, heq, show 0 < 2 ^ w by omega]
    exact ⟨st, 6, i, runs_loop_iff.mpr (Or.inl ⟨he, rfl, rfl, rfl⟩),
      le_rfl, hi, hindex, hinv, hstop, by omega⟩
termination_by last - i
decreasing_by omega

/-- The next threshold store preserves every earlier certified entry.
When the store succeeds, the certified prefix extends by one. -/
theorem writeInitThreshold_prefix_step
    (TP : SparseCoreParams) (P : ChainParams) (N base i : ℕ) {st out : State}
    (hprefix : ∀ j ≤ i, st.mem (base + j) = rebuildThresholdWord TP P N j)
    (hframe : ∀ a ≠ base + (i + 1), out.mem a = st.mem a)
    (hresult : out.regs 10 = 0 ∧ out.mem = st.mem ∨
      out.regs 10 = 1 ∧ out.mem (base + (i + 1)) = rebuildThresholdWord TP P N (i + 1)) :
    (∀ j ≤ i, out.mem (base + j) = rebuildThresholdWord TP P N j) ∧
      (out.regs 10 = 0 ∨ out.regs 10 = 1) ∧
      (out.regs 10 = 1 → ∀ j ≤ i + 1, out.mem (base + j) = rebuildThresholdWord TP P N j) := by
  have hearlier j (hj : j ≤ i) :
      out.mem (base + j) = rebuildThresholdWord TP P N j :=
    (hframe (base + j) (by omega)).trans (hprefix j hj)
  refine ⟨hearlier, ?_, ?_⟩
  · exact hresult.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  · intro hflag j hj
    rcases hresult with ⟨hzero, _⟩ | ⟨_, hnew⟩
    · omega
    · by_cases hle : j ≤ i
      · exact hearlier j hle
      · have heq : j = i + 1 := by omega
        simpa only [heq] using hnew

/-- A successful tail run leaves the entire threshold table certified.
If a check fails, every cell preceding the attempted level stays certified. -/
theorem writeInitThresholdTail_prefix_runs
    (TP : SparseCoreParams) (P : ChainParams) (N base : ℕ)
    {w pack last budget : ℕ} {p : Program} {ω : ℕ → Bool}
    (inv : ℕ → State → Prop) (hw : 1 < 2 ^ w)
    (hstep : ∀ {i st}, i < last → st.regs 10 = 1 →
      st.regs 54 = i → st.regs 56 = last → inv i st →
      ∃ mid c, Runs w p ω (writeInitNextThreshold pack) st .normal mid c ∧
        mid.regs 54 = i + 1 ∧ mid.regs 56 = last ∧ inv (i + 1) mid ∧
        (mid.regs 10 = 0 ∧ mid.mem = st.mem ∨
          mid.regs 10 = 1 ∧ mid.mem (base + (i + 1)) = rebuildThresholdWord TP P N (i + 1)) ∧
        (∀ a ≠ base + (i + 1), mid.mem a = st.mem a) ∧ c ≤ budget)
    {i : ℕ} {st : State} (hi : i ≤ last) (hindex : st.regs 54 = i)
    (hlast : st.regs 56 = last) (hflag : st.regs 10 = 1) (hinv : inv i st)
    (hprefix : ∀ k ≤ i, st.mem (base + k) = rebuildThresholdWord TP P N k) :
    ∃ out c j, Runs w p ω (writeInitThresholdTail pack) st .normal out c ∧
      i ≤ j ∧ j ≤ last ∧ out.regs 54 = j ∧ inv j out ∧
      (∀ k < j, out.mem (base + k) = rebuildThresholdWord TP P N k) ∧
      (out.regs 10 = 1 → j = last ∧
        ∀ k ≤ last, out.mem (base + k) = rebuildThresholdWord TP P N k) ∧
      c ≤ (budget + 6) * (last - i) + 6 := by
  let certified (j : ℕ) (s : State) := inv j s ∧
    (∀ k < j, s.mem (base + k) = rebuildThresholdWord TP P N k) ∧
    (s.regs 10 = 1 → ∀ k ≤ j, s.mem (base + k) = rebuildThresholdWord TP P N k)
  have hstart : certified i st := ⟨hinv, fun k hk => hprefix k hk.le, fun _ => hprefix⟩
  obtain ⟨out, c, j, hr, hij, hj, hidx, hcert, hstop, hcost⟩ :=
    writeInitThresholdTail_runs certified hw (fun {j s} hj hflag hidx hlast hcert => by
      obtain ⟨mid, c, hr, hidx', hlast', hinv', hres, hframe, hc⟩ :=
        hstep hj hflag hidx hlast hcert.1
      obtain ⟨hearlier, hflag', hnew⟩ :=
        writeInitThreshold_prefix_step TP P N base j (hcert.2.2 hflag) hframe hres
      exact ⟨mid, c, hr, hidx', hlast',
        ⟨hinv', fun k hk => hearlier k (by omega), hnew⟩, hflag', hc⟩)
      hi hindex hlast (Or.inr hflag) hstart
  refine ⟨out, c, j, hr, hij, hj, hidx, hcert.1, hcert.2.1, ?_, hcost⟩
  intro h
  have he : j = last := hstop.resolve_left (by omega)
  exact ⟨he, he ▸ hcert.2.2 h⟩

/-- Fill the remaining table entries from the cached logarithm and
level products. The logarithm occupies words beyond the threshold table. -/
theorem writeInitThresholdTail_fromProducts_runs
    (TP : SparseCoreParams) (P : ChainParams) (i : ℕ)
    {w h pack ret limbs precision accuracy N base last stretchLo stretchHi stretchScale : ℕ}
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
    (hb : st.regs 53 = base) (hi : st.regs 54 = i) (hk : st.regs 55 = P.k)
    (h14 : st.regs 14 = P.M₀ * stretchLo ^ (i + 1))
    (h15 : st.regs 15 = P.M₀ * stretchHi ^ (i + 1))
    (h16 : st.regs 16 = stretchScale * (stretchScale * P.k) ^ i)
    (h19 : st.regs 19 = stretchLo) (h20 : st.regs 20 = stretchHi)
    (h21 : st.regs 21 = stretchScale * P.k)
    (hs : 0 < stretchScale) (hu : 0 < stretchHi)
    (hlo : (stretchLo : ℝ) / stretchScale ≤ TP.γ_ℓ (P.M₀ ^ 2))
    (hhi : TP.γ_ℓ (P.M₀ ^ 2) ≤ (stretchHi : ℝ) / stretchScale)
    (hprod : ∀ j ≤ last, P.M₀ * stretchLo ^ (j + 1) < 2 ^ w ∧
      P.M₀ * stretchHi ^ (j + 1) < 2 ^ w ∧ stretchScale * (stretchScale * P.k) ^ j < 2 ^ w)
    (hone : 1 < 2 ^ w)
    (hcell : base + last < 2 ^ w) (hdisjoint : base + last < ret - limbs)
    (hindex : i ≤ last) (hlast : st.regs 56 = last) (hflag : st.regs 10 = 1)
    (hprefix : ∀ j ≤ i, st.mem (base + j) = rebuildThresholdWord TP P N j) :
    let approx := (Num.intVal st.mem (ret - limbs) h limbs).toNat
    let error : ℕ := 2 ^ (precision - accuracy)
    let scale : ℕ := 2 ^ precision
    let lower := (approx - error) ^ 2
    let upper := (approx + error) ^ 2
    let scaleSq := scale ^ 2
    lower < 2 ^ w → upper < 2 ^ w → scaleSq < 2 ^ w →
    P.k * upper < 2 ^ w → P.k * lower < 2 ^ w →
    (∀ j ≤ last,
      let num := levelM TP P j * scaleSq
      let q := num / (P.k * upper)
      num < 2 ^ w ∧ q + 1 < 2 ^ w ∧ (q + 1) * (P.k * lower) < 2 ^ w) →
    ∃ out c j, Runs w p ω (writeInitThresholdTail pack) st .normal out c ∧
      i ≤ j ∧ j ≤ last ∧ out.regs 54 = j ∧
      (out.regs 10 = 0 ∨ out.regs 10 = 1) ∧
      (∀ k < j, out.mem (base + k) = rebuildThresholdWord TP P N k) ∧
      (out.regs 10 = 1 → j = last ∧
        ∀ k ≤ last, out.mem (base + k) = rebuildThresholdWord TP P N k) ∧
      (∀ a, a < base ∨ base + last < a → out.mem a = st.mem a) ∧
      (∀ r ≥ 19, r ≠ 54 → out.regs r = st.regs r) ∧
      c ≤ (25 * limbs + 143) * (last - i) + 6 := by
  dsimp only
  intro hlow hupp hscale hku hkl hwords
  let inv (j : ℕ) (s : State) :=
    (∀ r ≥ 19, r ≠ 54 → s.regs r = st.regs r) ∧
    s.regs 14 = P.M₀ * stretchLo ^ (j + 1) ∧
    s.regs 15 = P.M₀ * stretchHi ^ (j + 1) ∧
    s.regs 16 = stretchScale * (stretchScale * P.k) ^ j ∧
    (∀ a, a < base ∨ base + last < a → s.mem a = st.mem a) ∧ (s.regs 10 = 0 ∨ s.regs 10 = 1)
  have hstart : inv i st := ⟨fun _ _ _ => rfl, h14, h15, h16, fun _ _ => rfl, Or.inr hflag⟩
  obtain ⟨out, c, j, hrun, hj₁, hj₂, hidx, hinv, hcert, hfinish, hcost⟩ :=
    writeInitThresholdTail_prefix_runs TP P N base (budget := 25 * limbs + 137) inv hone
      (fun {j s} hj _ hidx hlast' hinv => by
        obtain ⟨hkeep, hp₁, hp₂, hp₃, hm, _⟩ := hinv
        have hr (r : ℕ) (h₁ : 19 ≤ r) (h₂ : r ≠ 54) := hkeep r h₁ h₂
        have hvalid : Num.Valid s.mem (ret - limbs) h limbs := by
          intro a ha
          rw [hm _ (Or.inr (by omega))]
          exact hv a ha
        have hval : Num.intVal s.mem (ret - limbs) h limbs = Num.intVal st.mem (ret - limbs) h limbs :=
          Num.intVal_congr fun a ha => hm _ (Or.inr (by omega))
        have hfix : Num.fixVal s.mem (ret - limbs) h limbs precision =
            Num.fixVal st.mem (ret - limbs) h limbs precision := by simp only [Num.fixVal, hval]
        obtain ⟨hlw, huw, hdw⟩ := hprod (j + 1) (by omega)
        obtain ⟨hn, hqw, hc⟩ := hwords (j + 1) (by omega)
        have hup : 0 < P.M₀ * stretchHi ^ (j + 2) := Nat.mul_pos P.hM₀ (pow_pos hu _)
        obtain ⟨mid, c, hr', hres, hframe, hidx', hp₁', hp₂', hp₃', hkeep', hcost⟩ :=
          writeInitNextThreshold_runs (ω := ω) TP P j hpack
            ((hr 99 (by decide) (by decide)).trans hret) ((hr 67 (by decide) (by decide)).trans hL)
            ((hr 68 (by decide) (by decide)).trans hP) ((hr 100 (by decide) (by decide)).trans hq)
            hle hw hwidth hvalid hqpos hqprec (hfix.symm ▸ herr) (hval.symm ▸ hfit)
            ((hr 53 (by decide) (by decide)).trans hb) hidx ((hr 55 (by decide) (by decide)).trans hk)
            hp₁ hp₂ hp₃ ((hr 19 (by decide) (by decide)).trans h19)
            ((hr 20 (by decide) (by decide)).trans h20) ((hr 21 (by decide) (by decide)).trans h21)
            hs hup hlo hhi hlw huw hdw hone (by omega)
            (by simpa only [hval] using hlow) (by simpa only [hval] using hupp) hscale hn
            (by simpa only [hval] using hku) (by simpa only [hval] using hkl)
            (by simpa only [hval] using hqw) (by simpa only [hval] using hc)
        exact ⟨mid, c, hr', hidx', (hkeep' 56 (by decide) (by decide)).trans hlast',
          ⟨fun r ha hb => (hkeep' r ha hb).trans (hkeep r ha hb), hp₁', hp₂', hp₃',
            fun a ha => (hframe a (by rcases ha with ha | ha <;> omega)).trans (hm a ha),
            hres.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)⟩, hres, hframe, hcost⟩)
      hindex hi hlast hflag hstart hprefix
  exact ⟨out, c, j, hrun, hj₁, hj₂, hidx, hinv.2.2.2.2.2, hcert, hfinish, hinv.2.2.2.2.1, hinv.1,
    by simpa only [Nat.add_assoc] using hcost⟩

/-- Write level zero using the cached logarithm and the threshold table base. -/
@[expose] def writeInitBaseThresholdCached (pack : ℕ) : Stmt :=
  prepareInitThresholdCell ;; guardInitThresholdFromVertexLog pack

/-- The base store uses the certified level-zero size and leaves the
level products and the cached logarithm registers available for the tail. -/
theorem writeInitBaseThresholdCached_runs
    (TP : SparseCoreParams) (P : ChainParams)
    {w h pack ret limbs precision accuracy N base : ℕ}
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
    (hflag : st.regs 18 = 0 ∨ st.regs 18 = 1)
    (h0 : st.regs 18 = 1 → st.regs 0 = levelM TP P 0)
    (hb : st.regs 53 = base) (hi : st.regs 54 = 0) (hk : st.regs 55 = P.k)
    (hbase : base < 2 ^ w) :
    let approx := (Num.intVal st.mem (ret - limbs) h limbs).toNat
    let error : ℕ := 2 ^ (precision - accuracy)
    let scale : ℕ := 2 ^ precision
    let lower := (approx - error) ^ 2
    let upper := (approx + error) ^ 2
    let scaleSq := scale ^ 2
    let num := levelM TP P 0 * scaleSq
    let q := num / (P.k * upper)
    lower < 2 ^ w → upper < 2 ^ w → scaleSq < 2 ^ w →
    num < 2 ^ w → P.k * upper < 2 ^ w → P.k * lower < 2 ^ w →
    q + 1 < 2 ^ w → (q + 1) * (P.k * lower) < 2 ^ w →
    ∃ out c, Runs w p ω (writeInitBaseThresholdCached pack) st .normal out c ∧
      (out.regs 10 = 0 ∧ out.mem = st.mem ∨
        out.regs 10 = 1 ∧ out.mem base = rebuildThresholdWord TP P N 0) ∧
      (∀ a ≠ base, out.mem a = st.mem a) ∧
      (∀ r ≥ 14, out.regs r = st.regs r) ∧ c ≤ 25 * limbs + 98 := by
  dsimp only
  intro hlo hhi hs hn hu hl hqw hc
  obtain ⟨mid, hr, hbranch, hdest, hkeep, hm, _⟩ :=
    prepareInitThresholdCell_runs (p := p) (ω := ω) hb hi hk (by simpa using hbase)
  have hreg (r : ℕ) (h : r ≠ 1 ∧ r ≠ 11) : mid.regs r = st.regs r := hkeep r h.1 h.2
  have h18 := hreg 18 (by decide)
  obtain ⟨out, c, hr', hres, hframe, hkeep', hcost⟩ :=
    guardInitThresholdFromVertexLog_fromLevelCheck_runs (ω := ω) TP P 0 hpack
      ((hreg 99 (by decide)).trans hret) ((hreg 67 (by decide)).trans hL)
      ((hreg 68 (by decide)).trans hP) ((hreg 100 (by decide)).trans hq)
      hle hw hwidth (hm.symm ▸ hv) hqpos hqprec (hm.symm ▸ herr) (hm.symm ▸ hfit)
      (h18.symm ▸ hflag) (fun h => (hreg 0 (by decide)).trans (h0 (h18.symm.trans h)))
      hbranch (by simpa using hdest) (hm.symm ▸ hlo) (hm.symm ▸ hhi)
      hs hn (hm.symm ▸ hu) (hm.symm ▸ hl) (hm.symm ▸ hqw) (hm.symm ▸ hc)
  refine ⟨out, 7 + c + 1, runs_seq_iff.mpr (Or.inr ⟨mid, 7, c, hr, hr', rfl⟩),
    by simpa only [hm] using hres, fun a ha => (hframe a ha).trans (congrFun hm a),
    fun r h => (hkeep' r h).trans (hreg r ⟨by omega, by omega⟩), by omega⟩

/-- Write level zero and continue only while each level's check succeeds. -/
@[expose] def writeInitThresholdTable (pack : ℕ) : Stmt :=
  writeInitBaseThresholdCached pack ;; writeInitThresholdTail pack

/-- A successful flag certifies the whole table from one cached logarithm.
The invariant on the logarithm block holds because the table precedes it. -/
theorem writeInitThresholdTable_runs
    (TP : SparseCoreParams) (P : ChainParams)
    {w h pack ret limbs precision accuracy N base last stretchLo stretchHi stretchScale : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hret : st.regs 99 = ret) (hL : st.regs 67 = limbs)
    (hP : st.regs 68 = precision) (hq : st.regs 100 = accuracy)
    (hle : limbs ≤ ret) (hw : ret < 2 ^ w) (hwidth : precision < w)
    (hv : Num.Valid st.mem (ret - limbs) h limbs)
    (hqpos : 1 ≤ accuracy) (hqprec : accuracy ≤ precision)
    (herr : |Num.fixVal st.mem (ret - limbs) h limbs precision - Real.log ((N : ℝ) + 2)| ≤
      1 / (2 : ℝ) ^ accuracy)
    (hb : st.regs 53 = base) (hi : st.regs 54 = 0) (hk : st.regs 55 = P.k)
    (h14 : st.regs 14 = P.M₀ * stretchLo)
    (h15 : st.regs 15 = P.M₀ * stretchHi)
    (h16 : st.regs 16 = stretchScale)
    (h19 : st.regs 19 = stretchLo) (h20 : st.regs 20 = stretchHi)
    (h21 : st.regs 21 = stretchScale * P.k)
    (hs : 0 < stretchScale) (hu : 0 < stretchHi)
    (hlo : (stretchLo : ℝ) / stretchScale ≤ TP.γ_ℓ (P.M₀ ^ 2))
    (hhi : TP.γ_ℓ (P.M₀ ^ 2) ≤ (stretchHi : ℝ) / stretchScale)
    (hprod : ∀ j ≤ last, P.M₀ * stretchLo ^ (j + 1) < 2 ^ w ∧
      P.M₀ * stretchHi ^ (j + 1) < 2 ^ w ∧ stretchScale * (stretchScale * P.k) ^ j < 2 ^ w)
    (hone : 1 < 2 ^ w)
    (hcell : base + last < 2 ^ w) (hdisjoint : base + last < ret - limbs)
    (hlast : st.regs 56 = last) (hflag : st.regs 18 = 0 ∨ st.regs 18 = 1)
    (hsize : st.regs 18 = 1 → st.regs 0 = levelM TP P 0) :
    ((N + 2) * 2 ^ precision) ^ 2 < 2 ^ w →
    (∀ j ≤ last, levelM TP P j * (2 ^ precision) ^ 2 +
      P.k * ((N + 2) * 2 ^ precision) ^ 2 < 2 ^ w) →
    ∃ out c, Runs w p ω (writeInitThresholdTable pack) st .normal out c ∧
      (out.regs 10 = 0 ∨ out.regs 10 = 1 ∧
        ∀ k ≤ last, out.mem (base + k) = rebuildThresholdWord TP P N k) ∧
      (∀ a, a < base ∨ base + last < a → out.mem a = st.mem a) ∧
      (∀ r ≥ 19, r ≠ 54 → out.regs r = st.regs r) ∧
      c ≤ 25 * limbs + (25 * limbs + 143) * last + 105 := by
  intro hupper hbudget
  let approx := (Num.intVal st.mem (ret - limbs) h limbs).toNat
  let error : ℕ := 2 ^ (precision - accuracy)
  let scale : ℕ := 2 ^ precision
  let lower := (approx - error) ^ 2
  let upper := (approx + error) ^ 2
  have he := (initVertexLog_scaledError hqpos hqprec herr).2
  have herrorScale : 2 * error ≤ scale := by
    dsimp [error, scale]
    rw [← pow_succ']
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hendpoint : approx + error ≤ (N + 2) * scale :=
    initLogUpper_le_scaledInput (by dsimp [scale]; positivity) herrorScale
      (by simpa only [approx, error, scale, Nat.cast_pow, Nat.cast_ofNat] using he)
  have horder : lower ≤ upper :=
    Nat.pow_le_pow_left ((Nat.sub_le _ _).trans (Nat.le_add_right _ _)) _
  have hupperSq := Nat.pow_le_pow_left hendpoint 2
  have hsInput : scale ≤ (N + 2) * scale := by
    simpa only [one_mul] using Nat.mul_le_mul_right scale (show 1 ≤ N + 2 by omega)
  have hscale := (Nat.pow_le_pow_left hsInput 2).trans_lt hupper
  have hupp : upper < 2 ^ w := hupperSq.trans_lt hupper
  have hlow : lower < 2 ^ w := horder.trans_lt hupp
  have hupperPos : 0 < P.k * upper :=
    Nat.mul_pos P.hk (pow_pos (by have : 0 < error := pow_pos (by decide) _; omega) _)
  have hfit : approx < 2 ^ w := by
    have h₁ : approx ≤ approx + error := Nat.le_add_right _ _
    have h₂ : (N + 2) * scale ≤ ((N + 2) * scale) ^ 2 := by
      exact (by simpa only [pow_two, Nat.mul_one] using
        Nat.mul_le_mul_left ((N + 2) * scale) (show 1 ≤ (N + 2) * scale by
          exact Nat.succ_le_of_lt (by dsimp [scale]; positivity)))
    exact (h₁.trans (hendpoint.trans h₂)).trans_lt hupper
  have hchecks (j : ℕ) (hj : j ≤ last) :=
    rebuildThreshold_checkWordBounds horder hupperPos
      ((Nat.add_le_add_left (Nat.mul_le_mul_left P.k hupperSq)
        (levelM TP P j * scale ^ 2)).trans_lt (hbudget j hj))
  obtain ⟨hku, hkl, _, _⟩ := hchecks 0 (Nat.zero_le last)
  have hwords (j : ℕ) (hj : j ≤ last) :
      let num := levelM TP P j * scale ^ 2
      let q := num / (P.k * upper)
      num < 2 ^ w ∧ q + 1 < 2 ^ w ∧ (q + 1) * (P.k * lower) < 2 ^ w := by
    obtain ⟨_, _, hq, hcut⟩ := hchecks j hj
    exact ⟨(Nat.le_add_right _ _).trans_lt (hbudget j hj), hq, hcut⟩
  obtain ⟨hn, hqw, hcut⟩ := hwords 0 (Nat.zero_le last)
  obtain ⟨mid, c₁, hr₁, hres, hframe, hkeep, hc₁⟩ :=
    writeInitBaseThresholdCached_runs (ω := ω) TP P hpack hret hL hP hq hle hw hwidth
      hv hqpos hqprec herr hfit hflag hsize hb hi hk (by omega)
      hlow hupp hscale hn hku hkl hqw hcut
  rcases hres with ⟨hzero, _⟩ | ⟨hone', hbase⟩
  · have he : Expr.eval w mid (.bin .and (.reg 10) (.bin .lt (.reg 54) (.reg 56))) =
        some 0 := by
      by_cases hl : 0 < last <;>
        simp [Expr.eval, BinOp.eval, hzero, (hkeep 54 (by decide)).trans hi,
          (hkeep 56 (by decide)).trans hlast, hl, hone, show 0 < 2 ^ w by omega]
    have hr₂ : Runs w p ω (writeInitThresholdTail pack) mid .normal mid 6 :=
      runs_loop_iff.mpr (Or.inl ⟨he, rfl, rfl, rfl⟩)
    refine ⟨mid, c₁ + 6 + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c₁, 6, hr₁, hr₂, rfl⟩),
      Or.inl hzero, fun a ha => hframe a (by rcases ha with ha | ha <;> omega), fun r hr _ => hkeep r (by omega), by omega⟩
  · have hvalid : Num.Valid mid.mem (ret - limbs) h limbs := by
      intro a ha
      rw [hframe _ (by omega)]
      exact hv a ha
    have hval : Num.intVal mid.mem (ret - limbs) h limbs = Num.intVal st.mem (ret - limbs) h limbs :=
      Num.intVal_congr fun a ha => hframe _ (by omega)
    have hfix : Num.fixVal mid.mem (ret - limbs) h limbs precision =
        Num.fixVal st.mem (ret - limbs) h limbs precision := by simp only [Num.fixVal, hval]
    obtain ⟨out, c₂, j, hr₂, _, _, _, hbit, _, hfinal, hframe₂, hregs, hc₂⟩ :=
      writeInitThresholdTail_fromProducts_runs (ω := ω) TP P 0 hpack
        ((hkeep 99 (by decide)).trans hret) ((hkeep 67 (by decide)).trans hL)
        ((hkeep 68 (by decide)).trans hP) ((hkeep 100 (by decide)).trans hq)
        hle hw hwidth hvalid hqpos hqprec (hfix.symm ▸ herr) (hval.symm ▸ hfit)
        ((hkeep 53 (by decide)).trans hb) ((hkeep 54 (by decide)).trans hi)
        ((hkeep 55 (by decide)).trans hk)
        (by simpa using (hkeep 14 (by decide)).trans h14)
        (by simpa using (hkeep 15 (by decide)).trans h15)
        (by simpa using (hkeep 16 (by decide)).trans h16)
        ((hkeep 19 (by decide)).trans h19) ((hkeep 20 (by decide)).trans h20)
        ((hkeep 21 (by decide)).trans h21) hs hu hlo hhi hprod hone hcell hdisjoint
        (Nat.zero_le last) ((hkeep 56 (by decide)).trans hlast) hone'
        (fun k hk => by simpa [Nat.eq_zero_of_le_zero hk] using hbase)
        (by simpa only [hval] using hlow) (by simpa only [hval] using hupp) hscale
        (by simpa only [hval] using hku) (by simpa only [hval] using hkl)
        (by simpa only [hval] using hwords)
    refine ⟨out, c₁ + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c₁, c₂, hr₁, hr₂, rfl⟩), ?_, ?_, ?_, ?_⟩
    · exact hbit.elim Or.inl (fun h => Or.inr ⟨h, (hfinal h).2⟩)
    · intro a ha
      exact (hframe₂ a ha).trans (hframe a (by rcases ha with ha | ha <;> omega))
    · intro r hr hne
      exact (hregs r hr hne).trans (hkeep r (by omega))
    · simp only [Nat.sub_zero] at hc₂
      omega

/-- Allocate the vertex logarithm once, then use it for the whole table. -/
@[expose] def cacheAndWriteInitThresholdTable (bits load log pack : ℕ) : Stmt :=
  cacheInitVertexLog bits load log ;; writeInitThresholdTable pack

/-- The table agrees with the model when the checked run succeeds,
and the only changes below the initial heap are table entries. -/
theorem cacheAndWriteInitThresholdTable_runs
    (TP : SparseCoreParams) (P : ChainParams)
    {w h bits load log pack heap limbs precision N base last stretchLo stretchHi stretchScale : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hlog : MeetsContract w p log (Num.logarithmContract w h (precision - (N + 2).size - 10)))
    (hN : st.regs 92 = N) (hscale : st.regs 4 = 2 ^ precision)
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision) (hh : st.regs 98 = heap)
    (hw : N + 2 < 2 ^ w) (hword : (N + 2) * 2 ^ precision < 2 ^ w)
    (hfit : 2 * ((N + 2) * 2 ^ precision) < Num.capacity h limbs)
    (hroom : heap + limbs + limbs + Num.logarithmSpace limbs precision (N + 2).size < 2 ^ w)
    (hz : ZeroFrom st.mem heap) (hdiv : h ∣ precision)
    (hacc : (N + 2).size + 11 ≤ precision) (hcap : precision + (N + 2).size + 4 ≤ h * limbs)
    (hprec : 2 * precision + 9 < 2 ^ w) (hwidth : precision < w)
    (hb : st.regs 53 = base) (hi : st.regs 54 = 0) (hk : st.regs 55 = P.k)
    (h14 : st.regs 14 = P.M₀ * stretchLo)
    (h15 : st.regs 15 = P.M₀ * stretchHi)
    (h16 : st.regs 16 = stretchScale)
    (h19 : st.regs 19 = stretchLo) (h20 : st.regs 20 = stretchHi)
    (h21 : st.regs 21 = stretchScale * P.k)
    (hs : 0 < stretchScale) (hu : 0 < stretchHi)
    (hlo : (stretchLo : ℝ) / stretchScale ≤ TP.γ_ℓ (P.M₀ ^ 2))
    (hhi : TP.γ_ℓ (P.M₀ ^ 2) ≤ (stretchHi : ℝ) / stretchScale)
    (hprod : ∀ j ≤ last, P.M₀ * stretchLo ^ (j + 1) < 2 ^ w ∧
      P.M₀ * stretchHi ^ (j + 1) < 2 ^ w ∧ stretchScale * (stretchScale * P.k) ^ j < 2 ^ w)
    (hone : 1 < 2 ^ w)
    (hcell : base + last < heap)
    (hlast : st.regs 56 = last) (hflag : st.regs 18 = 0 ∨ st.regs 18 = 1)
    (hsize : st.regs 18 = 1 → st.regs 0 = levelM TP P 0) :
    ((N + 2) * 2 ^ precision) ^ 2 < 2 ^ w →
    (∀ j ≤ last, levelM TP P j * (2 ^ precision) ^ 2 +
      P.k * ((N + 2) * 2 ^ precision) ^ 2 < 2 ^ w) →
    ∃ out c, Runs w p ω (cacheAndWriteInitThresholdTable bits load log pack) st .normal out c ∧
      (out.regs 10 = 0 ∨ out.regs 10 = 1 ∧
        ∀ k ≤ last, out.mem (base + k) = rebuildThresholdWord TP P N k) ∧
      (∀ a < heap, a < base ∨ base + last < a → out.mem a = st.mem a) ∧
      (∀ r, 19 ≤ r → r < 95 → r ≠ 54 → out.regs r = st.regs r) ∧
      heap + limbs ≤ out.regs 99 ∧ out.regs 99 < 2 ^ w ∧ ZeroFrom out.mem (out.regs 99) ∧
      c ≤ 71 * limbs + (25 * limbs + 143) * last +
        Num.logarithmCost limbs precision (N + 2).size + 14 * (N + 2).size + 165 := by
  intro hupper hbudget
  obtain ⟨mid, c₁, ret, hr₁, hret, hq, hretLo, hretHi, _, hv, herr, hkeep, hframe₁, hzero, hc₁⟩ :=
    cacheInitVertexLog_runs (ω := ω) hbits hload hlog hN hscale hL hP hh hw hword hfit
      hroom hz hdiv hacc hcap hprec
  have hr (r : ℕ) (h : r < 95) := hkeep r (Or.inl h)
  have h18 := hr 18 (by decide)
  obtain ⟨out, c₂, hr₂, hres, hframe₂, hregs₂, hc₂⟩ :=
    writeInitThresholdTable_runs (ω := ω) TP P hpack hret ((hr 67 (by decide)).trans hL)
      ((hr 68 (by decide)).trans hP) hq (by omega) hretHi hwidth hv (by omega) (by omega) herr
      ((hr 53 (by decide)).trans hb) ((hr 54 (by decide)).trans hi) ((hr 55 (by decide)).trans hk)
      ((hr 14 (by decide)).trans h14) ((hr 15 (by decide)).trans h15) ((hr 16 (by decide)).trans h16)
      ((hr 19 (by decide)).trans h19) ((hr 20 (by decide)).trans h20) ((hr 21 (by decide)).trans h21)
      hs hu hlo hhi hprod hone (by omega) (by omega) ((hr 56 (by decide)).trans hlast)
      (h18.symm ▸ hflag) (fun hf => (hr 0 (by decide)).trans (hsize (h18.symm.trans hf))) hupper hbudget
  have htop := (hregs₂ 99 (by decide) (by decide)).trans hret
  refine ⟨out, c₁ + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c₁, c₂, hr₁, hr₂, rfl⟩), hres,
    fun a ha houtside => (hframe₂ a houtside).trans (hframe₁ a ha),
    fun r hlo hhi hne => (hregs₂ r hlo hne).trans (hr r hhi),
    htop.symm ▸ hretLo, htop.symm ▸ hretHi, ?_, by omega⟩
  intro a ha
  rw [htop] at ha
  exact (hframe₂ a (Or.inr (by omega))).trans (hzero a ha)

/-- Reserve the threshold words after the Init header and establish the
table registers. The logarithm scratch begins immediately after the table. -/
@[expose] def reserveInitThresholdTable : Stmt :=
  .assign 53 (.reg 77) ;;
  .assign 54 (.const 0) ;;
  .assign 55 (.reg 76) ;;
  .assign 56 (.reg 75) ;;
  .assign 83 (.reg 53) ;;
  .assign 98 (.bin .add (.bin .add (.reg 53) (.reg 56)) (.const 1))

/-- Reservation sets the header's threshold pointer, and the untouched
zero suffix is ready for the table and logarithm allocation. -/
theorem reserveInitThresholdTable_runs {w base last branch : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hb : st.regs 77 = base) (hd : st.regs 75 = last) (hk : st.regs 76 = branch)
    (hroom : base + last + 1 < 2 ^ w) (hz : ZeroFrom st.mem base) :
    ∃ out, Runs w p ω reserveInitThresholdTable st .normal out 21 ∧
      out.regs 53 = base ∧ out.regs 54 = 0 ∧ out.regs 55 = branch ∧ out.regs 56 = last ∧
      out.regs 83 = base ∧ out.regs 98 = base + last + 1 ∧
      (∀ r, r ≠ 53 → r ≠ 54 → r ≠ 55 → r ≠ 56 → r ≠ 83 → r ≠ 98 →
        out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ ZeroFrom out.mem (base + last + 1) := by
  let s₁ := { st with regs := Function.update st.regs 53 base }
  let s₂ := { s₁ with regs := Function.update s₁.regs 54 0 }
  let s₃ := { s₂ with regs := Function.update s₂.regs 55 branch }
  let s₄ := { s₃ with regs := Function.update s₃.regs 56 last }
  let s₅ := { s₄ with regs := Function.update s₄.regs 83 base }
  let out := { s₅ with regs := Function.update s₅.regs 98 (base + last + 1) }
  have hr₁ : Runs w p ω (.assign 53 (.reg 77)) st .normal s₁ 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hb], rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign 54 (.const 0)) s₁ .normal s₂ 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hr₃ : Runs w p ω (.assign 55 (.reg 76)) s₂ .normal s₃ 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s₂, s₁, hk], rfl, rfl, rfl⟩
  have hr₄ : Runs w p ω (.assign 56 (.reg 75)) s₃ .normal s₄ 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s₃, s₂, s₁, hd], rfl, rfl, rfl⟩
  have hr₅ : Runs w p ω (.assign 83 (.reg 53)) s₄ .normal s₅ 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s₄, s₃, s₂, s₁], rfl, rfl, rfl⟩
  have hr₆ : Runs w p ω (.assign 98 (.bin .add (.bin .add (.reg 53) (.reg 56)) (.const 1)))
      s₅ .normal out 6 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, s₅, s₄, s₃, s₂, s₁, hroom,
      show base + last < 2 ^ w by omega, show 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
  refine ⟨out, ?_, by simp [out, s₅, s₄, s₃, s₂, s₁], by simp [out, s₅, s₄, s₃, s₂],
    by simp [out, s₅, s₄, s₃], by simp [out, s₅, s₄], by simp [out, s₅],
    by simp [out], ?_, rfl, fun a ha => hz a (by omega)⟩
  · refine runs_seq_iff.mpr (Or.inr ⟨s₁, 2, 18, hr₁, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s₂, 2, 15, hr₂, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s₃, 2, 12, hr₃, ?_, rfl⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨s₄, 2, 9, hr₄, ?_, rfl⟩)
    exact runs_seq_iff.mpr (Or.inr ⟨s₅, 2, 6, hr₅, hr₆, rfl⟩)
  · intro r h53 h54 h55 h56 h83 h98
    simp [out, s₅, s₄, s₃, s₂, s₁, h53, h54, h55, h56, h83, h98]

/-- Reserve the threshold table and fill it from the rounded length factor
and cached vertex logarithm. -/
@[expose] def reserveAndInitIntegerThresholdTable : Stmt :=
  reserveInitThresholdTable ;; initIntegerThresholdTable

/-- The threshold stage writes exactly the reserved cells, installs
the table pointer, and leaves a fresh heap for level initialization. -/
theorem reserveAndInitIntegerThresholdTable_runs
    {w edges branches a scale vertices base last : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hk : 0 < branches) (hword : 1 < 2 ^ w) (hbase : base + last + 1 < 2 ^ w)
    (hz : ZeroFrom st.mem base)
    (hroom : ∀ j ≤ last, edges * a ^ (j + 1) + scale ^ (j + 1) * branches ^ j < 2 ^ w)
    (hden : 3 * branches * Nat.clog 2 (vertices + 2) ^ 2 < 2 ^ w)
    (h22 : st.regs 22 = edges) (h12 : st.regs 12 = a) (h4 : st.regs 4 = scale)
    (h14 : st.regs 14 = Nat.clog 2 (vertices + 2))
    (h77 : st.regs 77 = base) (h76 : st.regs 76 = branches) (h75 : st.regs 75 = last)
    (hs : scale * branches < 2 ^ w) :
    ∃ out, Runs w p ω reserveAndInitIntegerThresholdTable st .normal out (50 * last + 75) ∧
      out.regs 83 = base ∧ out.regs 98 = base + last + 1 ∧
      (∀ j ≤ last, out.mem (base + j) =
        concreteLevelRebuildCount edges branches a scale j vertices) ∧
      (∀ x < base, out.mem x = st.mem x) ∧ ZeroFrom out.mem (base + last + 1) := by
  obtain ⟨mid, hr, h53, h54, h55, h56, h83, h98, hf, hm, hz'⟩ :=
    reserveInitThresholdTable_runs (p := p) (ω := ω) h77 h75 h76 hbase hz
  have keep (r : ℕ) (h53 : r ≠ 53 := by decide) (h54 : r ≠ 54 := by decide)
      (h55 : r ≠ 55 := by decide) (h56 : r ≠ 56 := by decide)
      (h83 : r ≠ 83 := by decide) (h98 : r ≠ 98 := by decide) := hf r h53 h54 h55 h56 h83 h98
  obtain ⟨out, hr', hp, hframe, hregs⟩ :=
    initIntegerThresholdTable_runs (p := p) (ω := ω) hk hword (by omega) hroom hden
      ((keep 22).trans h22) ((keep 12).trans h12) ((keep 4).trans h4) ((keep 14).trans h14)
      h53 h55 h54 h56 hs
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 21, _, hr, hr', by omega⟩),
    (hregs 83 (by decide)).trans h83, (hregs 98 (by decide)).trans h98, hp,
    fun x hx => (hframe x (.inl hx)).trans (congrFun hm x),
    fun x hx => (hframe x (.inr (by omega))).trans (hz' x hx)⟩

/-- Round the growth endpoint, then reserve and populate the threshold table. -/
@[expose] def initRoundedIntegerThresholdTable : Stmt :=
  roundIntegerLevelGrowth ;; reserveAndInitIntegerThresholdTable

/-- The terminal powers dominate the arithmetic at every table entry. -/
private theorem integerThresholdPowers_fit {w m k a scale d : ℕ}
    (ha : 0 < a) (hs : 0 < scale) (hk : 0 < k) (hd : 0 < d)
    (hroom : m * a ^ (d + 1) + scale ^ (d + 1) * k ^ d < 2 ^ w) :
    scale * k < 2 ^ w ∧
      ∀ j ≤ d, m * a ^ (j + 1) + scale ^ (j + 1) * k ^ j < 2 ^ w := by
  have hscale : scale ≤ scale ^ (d + 1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right hs (show 1 ≤ d + 1 by omega)
  have hbranch : k ≤ k ^ d := by
    simpa only [pow_one] using Nat.pow_le_pow_right hk hd
  refine ⟨(Nat.mul_le_mul hscale hbranch).trans_lt ((Nat.le_add_left _ _).trans_lt hroom), ?_⟩
  intro j hj
  exact (Nat.add_le_add
    (Nat.mul_le_mul_left m (Nat.pow_le_pow_right ha (Nat.add_le_add_right hj 1)))
    (Nat.mul_le_mul (Nat.pow_le_pow_right hs (Nat.add_le_add_right hj 1))
      (Nat.pow_le_pow_right hk hj))).trans_lt hroom

private theorem terminalThresholdDenominator_le (P : ChainParams) (scale : ℕ) :
    scale ^ (P.d + 1) * P.k ^ P.d ≤ P.M₀ * (2 * scale) ^ (P.d + 1) := by
  have hM : (0 : ℝ) ≤ P.M₀ := Nat.cast_nonneg _
  have hd : (0 : ℝ) < P.d := Nat.cast_pos.mpr P.hd
  have hroot : ((P.M₀ : ℝ) ^ (1 / (P.d : ℝ))) ^ P.d = P.M₀ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM, one_div_mul_cancel hd.ne', Real.rpow_one]
  have hk : P.k ^ P.d ≤ 2 ^ P.d * P.M₀ := by
    have h := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) P.k) P.hk_upper P.d
    rw [mul_pow, hroot] at h
    exact_mod_cast h
  calc
    _ ≤ scale ^ (P.d + 1) * (2 ^ P.d * P.M₀) := Nat.mul_le_mul_left _ hk
    _ ≤ scale ^ (P.d + 1) * (2 ^ (P.d + 1) * P.M₀) := by
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _
        (Nat.pow_le_pow_right (by decide) (Nat.le_succ _)))
    _ = _ := by rw [mul_pow]; ac_rfl

/-- A certified coarse growth numerator suffices to write the integer
rebuild table and prove its two bounds at every level. -/
theorem initIntegerThresholdTable_fromCoarse_runs
    (TP : SparseCoreParams) (P : ChainParams)
    {w numerator scale vertices base : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hword : 1 < 2 ^ w) (hbase : base + P.d + 1 < 2 ^ w) (hz : ZeroFrom st.mem base)
    (h12 : st.regs 12 = numerator) (h4 : st.regs 4 = scale) (hs : 0 < scale)
    (hTP : TP.Valid) (hγM : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀)
    (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    (hlow : TP.γ_ℓ (P.M₀ ^ 2) ≤ (numerator : ℝ) / scale)
    (hhigh : (numerator : ℝ) / scale ≤ TP.γ_ℓ (P.M₀ ^ 2) + 1 / ((P.d : ℝ) + 1))
    (h22 : st.regs 22 = P.M₀) (h14 : st.regs 14 = Nat.clog 2 (vertices + 2))
    (h77 : st.regs 77 = base) (h76 : st.regs 76 = P.k) (h75 : st.regs 75 = P.d)
    (hden : 3 * P.k * Nat.clog 2 (vertices + 2) ^ 2 < 2 ^ w) :
    (3 * P.M₀ ^ 2 + 1) * (P.M₀ * (2 * scale) ^ (P.d + 1)) < 2 ^ w →
    ∃ out, Runs w p ω reserveAndInitIntegerThresholdTable st .normal out (50 * P.d + 75) ∧
      out.regs 83 = base ∧ out.regs 98 = base + P.d + 1 ∧
      (∀ j ≤ P.d, out.mem (base + j) = concreteLevelRebuildCount P.M₀ P.k numerator scale j vertices ∧
        (out.mem (base + j) : ℝ) ≤ SparseCoreTool.updateThreshold P.k (levelM TP P j) vertices ∧
        SparseCoreTool.updateThreshold P.k (levelM TP P j) vertices ≤
          48 * ((out.mem (base + j) : ℝ) + 1)) ∧
      (∀ x < base, out.mem x = st.mem x) ∧ ZeroFrom out.mem (base + P.d + 1) := by
  intro hcapacity
  have hγ := hTP.2.2.1 (P.M₀ ^ 2)
  have ha : 0 < numerator := by
    by_contra! hz
    have he : numerator = 0 := by omega
    have h := hγ.trans hlow
    norm_num [he] at h
  have hterminal := (concreteLevelEdgePowers_le TP P hTP _ scale P.d hs le_rfl
    hγM hγk hlow hhigh).trans_lt
      ((Nat.mul_le_mul_left _ (terminalThresholdDenominator_le P scale)).trans_lt hcapacity)
  obtain ⟨hkfit, hroom⟩ := integerThresholdPowers_fit ha hs P.hk P.hd hterminal
  obtain ⟨out, hr, h83, h98, ht, hf, hz'⟩ :=
    reserveAndInitIntegerThresholdTable_runs (p := p) (ω := ω) P.hk hword hbase
      hz hroom hden h22 h12 h4 h14 h77 h76 h75 hkfit
  refine ⟨out, hr, h83, h98, ?_, hf, hz'⟩
  intro j hj
  rw [ht j hj]
  exact ⟨rfl, concreteLevelRebuildCount_bounds TP P _ scale j vertices hs hj hγ hlow hhigh⟩

/-- From a sufficiently narrow growth enclosure, Init stores integer
thresholds with the safety and charging bounds of the rebuild schedule. -/
theorem initRoundedIntegerThresholdTable_runs
    (TP : SparseCoreParams) (P : ChainParams)
    {w upper scale divisor vertices base : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hword : 1 < 2 ^ w) (hbase : base + P.d + 1 < 2 ^ w) (hz : ZeroFrom st.mem base)
    (h20 : st.regs 20 = upper) (h23 : st.regs 23 = scale * divisor)
    (h24 : st.regs 24 = divisor) (hs : 0 < scale) (hd : 0 < divisor)
    (hfit : upper < 2 ^ w) (hscale : scale < 2 ^ w)
    (hTP : TP.Valid) (hγM : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀)
    (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    (hlo : TP.γ_ℓ (P.M₀ ^ 2) ≤ (upper : ℝ) / ((scale * divisor : ℕ) : ℝ))
    (herr : (upper : ℝ) / ((scale * divisor : ℕ) : ℝ) + 1 / scale ≤
      TP.γ_ℓ (P.M₀ ^ 2) + 1 / ((P.d : ℝ) + 1))
    (h22 : st.regs 22 = P.M₀) (h14 : st.regs 14 = Nat.clog 2 (vertices + 2))
    (h77 : st.regs 77 = base) (h76 : st.regs 76 = P.k) (h75 : st.regs 75 = P.d)
    (hden : 3 * P.k * Nat.clog 2 (vertices + 2) ^ 2 < 2 ^ w) :
    let a := (upper + divisor - 1) / divisor
    (3 * P.M₀ ^ 2 + 1) * (P.M₀ * (2 * scale) ^ (P.d + 1)) < 2 ^ w →
    ∃ out, Runs w p ω initRoundedIntegerThresholdTable st .normal out (50 * P.d + 89) ∧
      out.regs 83 = base ∧ out.regs 98 = base + P.d + 1 ∧
      (∀ j ≤ P.d, out.mem (base + j) = concreteLevelRebuildCount P.M₀ P.k a scale j vertices ∧
        (out.mem (base + j) : ℝ) ≤ SparseCoreTool.updateThreshold P.k (levelM TP P j) vertices ∧
        SparseCoreTool.updateThreshold P.k (levelM TP P j) vertices ≤
          48 * ((out.mem (base + j) : ℝ) + 1)) ∧
      (∀ x < base, out.mem x = st.mem x) ∧ ZeroFrom out.mem (base + P.d + 1) := by
  dsimp only
  intro hcapacity
  have hγ := hTP.2.2.1 (P.M₀ ^ 2)
  have hu : 0 < upper := by
    by_contra h
    have he : upper = 0 := by omega
    have hle := hγ.trans hlo
    norm_num [he] at hle
  obtain ⟨mid, hr, h12, h4, hlow, hhigh, hm, hf⟩ :=
    roundIntegerLevelGrowth_runs (p := p) (ω := ω) h20 h23 h24 hs hd hu hfit hscale hword hlo herr
  have keep (r : ℕ) (h12 : r ≠ 12 := by decide) (h4 : r ≠ 4 := by decide) := hf r h12 h4
  obtain ⟨out, hr', h83, h98, ht, hframe, hz'⟩ :=
    initIntegerThresholdTable_fromCoarse_runs (ω := ω) TP P hword hbase (hm.symm ▸ hz)
      h12 h4 hs hTP hγM hγk (h12 ▸ hlow) (h12 ▸ hhigh) ((keep 22).trans h22)
      ((keep 14).trans h14) ((keep 77).trans h77) ((keep 76).trans h76) ((keep 75).trans h75)
      hden hcapacity
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 13, _, hr, hr', by omega⟩), h83, h98,
    ht, fun x hx => (hframe x hx).trans (congrFun hm x), hz'⟩

end MinCostFlow.MinRatio
