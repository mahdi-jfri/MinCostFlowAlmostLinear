module

public import MinCostFlow.MinRatio.InitStretch
public import MinCostFlow.MinRatio.InitLevelSize
public import MinCostFlow.MinRatio.InitThresholdCached
import Mathlib.Tactic.Linarith

/-!
# Assembly of the sparse-core stretch computation

Prepare the common scale and the term multipliers, then compute and combine
the endpoint numerators.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain

/-- Compute the stretch enclosure from runtime factor bounds. -/
@[expose] def assembleInitStretch (power : ℕ) : Stmt :=
  prepareInitStretchTerms power ;; computeInitStretchBounds power

/-- The resulting scale and endpoints enclose the two model terms.
The bounds on those terms use the same integer numerators as the program. -/
theorem assembleInitStretch_runs
    (E : SparseCore.SparseCoreEnv) (m : ℕ)
    {w power scale kl ku sl su ll lu : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p power (initStretchPowerContract w))
    (hs : st.regs 4 = scale) (hd : st.regs 44 = E.L)
    (hb : st.regs 47 = E.B_fn m) (hg : st.regs 48 = E.d_fn m)
    (hkl : st.regs 49 = kl) (hku : st.regs 51 = ku)
    (hsl : st.regs 50 = sl) (hsu : st.regs 52 = su)
    (hll : st.regs 26 = ll) (hlu : st.regs 27 = lu)
    (hsPos : 0 < scale) (hbPos : 0 < E.B_fn m)
    (hslPos : 0 < sl) (hllPos : 0 < ll) (hluPos : 0 < lu) (horder : sl ≤ su)
    (hklBound : (kl : ℝ) / scale ≤ (E.P_fn m).K_s)
    (hkuBound : (E.P_fn m).K_s ≤ (ku : ℝ) / scale)
    (hslBound : (sl : ℝ) / scale ≤ (E.P_fn m).γ_ℓ)
    (hsuBound : (E.P_fn m).γ_ℓ ≤ (su : ℝ) / scale)
    (hllBound : (ll : ℝ) / scale ≤ SparseCore.coreLambdaS (E.P_fn m) m)
    (hluBound : SparseCore.coreLambdaS (E.P_fn m) m ≤ (lu : ℝ) / scale)
    (hsw : scale < 2 ^ w) (huw : su < 2 ^ w) (hw : 115 < 2 ^ w) :
    let exponent := max (E.L + 1) 3
    let common := scale ^ exponent
    let factor := 3 ^ E.L * scale ^ (exponent - (E.L + 1))
    let cap := (E.L + 1) * E.B_fn m * (2 * E.d_fn m + 190)
    let first := fun s : ℕ => factor * s ^ (E.L + 1)
    let second : ℕ → ℕ → ℕ → ℕ := fun k s l : ℕ =>
      11 * (cap * k * s * l + 115 * scale ^ 3) * scale ^ (exponent - 3)
    exponent < 2 ^ w → common < 2 ^ w → factor < 2 ^ w → cap < 2 ^ w →
    first su < 2 ^ w → second kl sl ll < 2 ^ w → second ku su lu < 2 ^ w →
    ∃ out c, Runs w p ω (assembleInitStretch power) st .normal out c ∧
      out.regs 23 = common ∧
      out.regs 19 = max (first sl) (second kl sl ll) ∧
      out.regs 20 = max (first su) (second ku su lu) ∧
      (out.regs 19 : ℝ) / common ≤ SparseCore.gammaLEnv E m ∧
      SparseCore.gammaLEnv E m ≤ (out.regs 20 : ℝ) / common ∧
      (∀ r, r < 19 ∨ r = 22 ∨ 46 < r → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ c ≤ 100 * exponent + 171 := by
  dsimp only
  intro hew hcommon hf hc hfirst hlo hhi
  obtain ⟨hfl, hfu, hsecondLo, hsecondHi⟩ :=
    initSparseCoreStretch_scaledTermBounds E m kl ku sl su ll lu scale hsPos
      hklBound hkuBound hslBound hsuBound hllBound hluBound
  obtain ⟨mid, c₁, hr₁, h23, h33, h34, h38, h42, h43, hkeep, hm₁, hc₁⟩ :=
    prepareInitStretchTerms_runs (ω := ω) himpl hs hd hb hg hsPos hsw hbPos hew hcommon hf hc
  have hk (r : ℕ) (h : r ≠ 23 ∧ r ≠ 33 ∧ r ≠ 34 ∧ r ≠ 38 ∧ r ≠ 42 ∧
      r ≠ 43 ∧ r ≠ 45 ∧ r ≠ 46) : mid.regs r = st.regs r :=
    hkeep r h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1
      h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2
  have hdepth := le_max_left (E.L + 1) 3
  obtain ⟨out, c₂, hr₂, h19, h20, hLo, hHi, hkeep₂, hm₂, hc₂⟩ :=
    computeInitStretchBounds_runs (ω := ω) himpl h33 h34 h38 h42 h43
      ((hk 49 (by decide)).trans hkl) ((hk 51 (by decide)).trans hku)
      ((hk 50 (by decide)).trans hsl) ((hk 52 (by decide)).trans hsu)
      ((hk 26 (by decide)).trans hll) ((hk 27 (by decide)).trans hlu)
      hslPos (hslPos.trans_le horder) hllPos hluPos (by positivity) (pow_pos hsPos _)
      horder (hdepth.trans_lt hew) huw hw hfirst hlo hhi (pow_pos hsPos _) (by simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hfl)
      (by simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hfu) hsecondLo hsecondHi
  refine ⟨out, c₁ + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c₁, c₂, hr₁, hr₂, rfl⟩),
    (hkeep₂ 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h23,
    h19, h20, by simpa only [SparseCore.gammaLEnv] using hLo,
    by simpa only [SparseCore.gammaLEnv] using hHi, ?_, hm₂.trans hm₁, by omega⟩
  intro r hsafe
  exact (hkeep₂ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)).trans (hk r ⟨by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega⟩)

/-- Compute the stretch enclosure and use it to check the base level size. -/
@[expose] def assembleInitBaseLevelSize (power : ℕ) : Stmt :=
  assembleInitStretch power ;; selectInitBaseLevelSize

/-- The stretch calculation supplies the bounds for the base-level
ceiling check. A successful check returns the exact model level size. -/
theorem assembleInitBaseLevelSize_runs
    (E : SparseCore.SparseCoreEnv) (P : ChainParams)
    {w power scale kl ku sl su ll lu : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p power (initStretchPowerContract w))
    (hM : st.regs 22 = P.M₀) (hk : st.regs 1 = P.k)
    (hs : st.regs 4 = scale) (hd : st.regs 44 = E.L)
    (hb : st.regs 47 = E.B_fn (P.M₀ ^ 2)) (hg : st.regs 48 = E.d_fn (P.M₀ ^ 2))
    (hkl : st.regs 49 = kl) (hku : st.regs 51 = ku)
    (hsl : st.regs 50 = sl) (hsu : st.regs 52 = su)
    (hll : st.regs 26 = ll) (hlu : st.regs 27 = lu)
    (hsPos : 0 < scale) (hbPos : 0 < E.B_fn (P.M₀ ^ 2))
    (hslPos : 0 < sl) (hllPos : 0 < ll) (hluPos : 0 < lu) (horder : sl ≤ su)
    (hklBound : (kl : ℝ) / scale ≤ (E.P_fn (P.M₀ ^ 2)).K_s)
    (hkuBound : (E.P_fn (P.M₀ ^ 2)).K_s ≤ (ku : ℝ) / scale)
    (hslBound : (sl : ℝ) / scale ≤ (E.P_fn (P.M₀ ^ 2)).γ_ℓ)
    (hsuBound : (E.P_fn (P.M₀ ^ 2)).γ_ℓ ≤ (su : ℝ) / scale)
    (hllBound : (ll : ℝ) / scale ≤ SparseCore.coreLambdaS (E.P_fn (P.M₀ ^ 2)) (P.M₀ ^ 2))
    (hluBound : SparseCore.coreLambdaS (E.P_fn (P.M₀ ^ 2)) (P.M₀ ^ 2) ≤ (lu : ℝ) / scale)
    (hsw : scale < 2 ^ w) (huw : su < 2 ^ w) (hw : 115 < 2 ^ w) :
    let exponent := max (E.L + 1) 3
    let common := scale ^ exponent
    let factor := 3 ^ E.L * scale ^ (exponent - (E.L + 1))
    let cap := (E.L + 1) * E.B_fn (P.M₀ ^ 2) * (2 * E.d_fn (P.M₀ ^ 2) + 190)
    let first := fun s : ℕ => factor * s ^ (E.L + 1)
    let second : ℕ → ℕ → ℕ → ℕ := fun k s l : ℕ =>
      11 * (cap * k * s * l + 115 * scale ^ 3) * scale ^ (exponent - 3)
    exponent < 2 ^ w → common < 2 ^ w → factor < 2 ^ w → cap < 2 ^ w →
    first su < 2 ^ w → second kl sl ll < 2 ^ w → second ku su lu < 2 ^ w →
    P.M₀ * max (first sl) (second kl sl ll) < 2 ^ w →
    P.M₀ * max (first su) (second ku su lu) < 2 ^ w →
    common * P.k < 2 ^ w →
    ∃ out c, Runs w p ω (assembleInitBaseLevelSize power) st .normal out c ∧
      (out.regs 18 = 1 → out.regs 0 = levelM (SparseCore.sparseCoreParams E) P 0) ∧
      (out.regs 18 = 0 ∨ out.regs 18 = 1) ∧
      out.regs 19 = max (first sl) (second kl sl ll) ∧
      out.regs 20 = max (first su) (second ku su lu) ∧ out.regs 23 = common ∧
      out.regs 14 = P.M₀ * out.regs 19 ∧ out.regs 15 = P.M₀ * out.regs 20 ∧
      out.regs 16 = common ∧ out.regs 21 = common * P.k ∧
      (out.regs 19 : ℝ) / common ≤ (SparseCore.sparseCoreParams E).γ_ℓ (P.M₀ ^ 2) ∧
      (SparseCore.sparseCoreParams E).γ_ℓ (P.M₀ ^ 2) ≤ (out.regs 20 : ℝ) / common ∧
      (∀ r, (0 < r ∧ r < 14) ∨ 46 < r → out.regs r = st.regs r) ∧ out.regs 1 = P.k ∧
      out.mem = st.mem ∧ c ≤ 100 * exponent + 208 := by
  dsimp only
  intro hew hcommon hf hc hfirst hlo hhi hbaseLo hbaseHi hmul
  obtain ⟨mid, c, hr, hscale, hlow, hupp, hloBound, hhiBound, hkeep, hm, hcost⟩ :=
    assembleInitStretch_runs (ω := ω) E (P.M₀ ^ 2) himpl hs hd hb hg hkl hku hsl hsu hll hlu
      hsPos hbPos hslPos hllPos hluPos horder hklBound hkuBound hslBound hsuBound hllBound hluBound
      hsw huw hw hew hcommon hf hc hfirst hlo hhi
  have hs' : 0 < scale ^ max (E.L + 1) 3 := pow_pos hsPos _
  have hu' : 0 < mid.regs 20 := by
    by_contra! h
    have hzero := Nat.eq_zero_of_le_zero h
    have hgamma := SparseCore.gammaLEnv_ge_three E (P.M₀ ^ 2)
    rw [hzero, Nat.cast_zero, zero_div] at hhiBound
    linarith
  have hMpos : 0 < P.M₀ := P.hM₀
  obtain ⟨out, hr', hsize, _, hflag, h14, h15, h16, h21, hkeep', hm', _⟩ :=
    selectInitBaseLevelSize_runs (p := p) (ω := ω) (SparseCore.sparseCoreParams E) P
      (mid.regs 19) (mid.regs 20) (scale ^ max (E.L + 1) 3)
      ((hkeep 22 (by decide)).trans hM) ((hkeep 1 (by decide)).trans hk)
      rfl rfl hscale hs' (Nat.mul_pos hMpos hu')
      (by simpa only [SparseCore.sparseCoreParams] using hloBound)
      (by simpa only [SparseCore.sparseCoreParams] using hhiBound)
      (hlow ▸ hbaseLo) (hupp ▸ hbaseHi) hmul (by omega)
  have hr19 := hkeep' 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hr20 := hkeep' 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨out, c + 36 + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c, 36, hr, hr', rfl⟩),
    hsize, hflag, hr19.trans hlow, hr20.trans hupp,
    (hkeep' 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hscale,
    hr19.symm ▸ h14, hr20.symm ▸ h15, h16, h21, ?_, ?_, ?_, ?_, hm'.trans hm, by omega⟩
  · simpa only [hr19, SparseCore.sparseCoreParams] using hloBound
  · simpa only [hr20, SparseCore.sparseCoreParams] using hhiBound
  · intro r h
    have hsafe : r < 19 ∨ r = 22 ∨ 46 < r := by
      rcases h with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inr h)
    exact (hkeep' r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)).trans (hkeep r hsafe)
  · exact (hkeep' 1 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans ((hkeep 1 (by decide)).trans hk)

/-- Certify the base level and compute its rebuild threshold when the
level-size enclosure determines an exact ceiling. -/
@[expose] def assembleInitBaseThreshold (power bits load log pack : ℕ) : Stmt :=
  assembleInitBaseLevelSize power ;; guardInitThreshold bits load log pack

/-- A successful store gives the exact model threshold at level zero.
Both inconclusive cases leave the threshold cell unchanged. -/
theorem assembleInitBaseThreshold_runs
    (E : SparseCore.SparseCoreEnv) (P : ChainParams)
    {w h power bits load log pack N precision limbs heap cell scale kl ku sl su ll lu : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p power (initStretchPowerContract w))
    (hM : st.regs 22 = P.M₀) (hk : st.regs 1 = P.k)
    (hs : st.regs 4 = scale) (hd : st.regs 44 = E.L)
    (hb : st.regs 47 = E.B_fn (P.M₀ ^ 2)) (hg : st.regs 48 = E.d_fn (P.M₀ ^ 2))
    (hkl : st.regs 49 = kl) (hku : st.regs 51 = ku)
    (hsl : st.regs 50 = sl) (hsu : st.regs 52 = su)
    (hll : st.regs 26 = ll) (hlu : st.regs 27 = lu)
    (hsPos : 0 < scale) (hbPos : 0 < E.B_fn (P.M₀ ^ 2))
    (hslPos : 0 < sl) (hllPos : 0 < ll) (hluPos : 0 < lu) (horder : sl ≤ su)
    (hklBound : (kl : ℝ) / scale ≤ (E.P_fn (P.M₀ ^ 2)).K_s)
    (hkuBound : (E.P_fn (P.M₀ ^ 2)).K_s ≤ (ku : ℝ) / scale)
    (hslBound : (sl : ℝ) / scale ≤ (E.P_fn (P.M₀ ^ 2)).γ_ℓ)
    (hsuBound : (E.P_fn (P.M₀ ^ 2)).γ_ℓ ≤ (su : ℝ) / scale)
    (hllBound : (ll : ℝ) / scale ≤ SparseCore.coreLambdaS (E.P_fn (P.M₀ ^ 2)) (P.M₀ ^ 2))
    (hluBound : SparseCore.coreLambdaS (E.P_fn (P.M₀ ^ 2)) (P.M₀ ^ 2) ≤ (lu : ℝ) / scale)
    (hsw : scale < 2 ^ w) (huw : su < 2 ^ w) (hw : 115 < 2 ^ w)
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hlog : MeetsContract w p log (Num.logarithmContract w h (precision - (N + 2).size - 10)))
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hN : st.regs 92 = N)
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision)
    (hh : st.regs 98 = heap)
    (hdest : st.regs 11 = cell) (hcell : cell < heap)
    (hwLog : N + 2 < 2 ^ w) (hword : (N + 2) * 2 ^ precision < 2 ^ w)
    (hfit : 2 * ((N + 2) * 2 ^ precision) < Num.capacity h limbs)
    (hroom : heap + limbs + limbs + Num.logarithmSpace limbs precision (N + 2).size < 2 ^ w)
    (hz : ZeroFrom st.mem heap) (hdiv : h ∣ precision)
    (hacc : (N + 2).size + 11 ≤ precision) (hcap : precision + (N + 2).size + 4 ≤ h * limbs)
    (hprec : 2 * precision + 9 < 2 ^ w) (hwidth : precision < w)
    (hkpos : 0 < P.k)
    (hupper : ((N + 2) * 2 ^ precision) ^ 2 < 2 ^ w)
    (hbudget : levelM (SparseCore.sparseCoreParams E) P 0 * (2 ^ precision) ^ 2 +
      P.k * ((N + 2) * 2 ^ precision) ^ 2 < 2 ^ w) :
    let exponent := max (E.L + 1) 3
    let common := scale ^ exponent
    let factor := 3 ^ E.L * scale ^ (exponent - (E.L + 1))
    let cap := (E.L + 1) * E.B_fn (P.M₀ ^ 2) * (2 * E.d_fn (P.M₀ ^ 2) + 190)
    let first := fun s : ℕ => factor * s ^ (E.L + 1)
    let second : ℕ → ℕ → ℕ → ℕ := fun k s l : ℕ =>
      11 * (cap * k * s * l + 115 * scale ^ 3) * scale ^ (exponent - 3)
    exponent < 2 ^ w → common < 2 ^ w → factor < 2 ^ w → cap < 2 ^ w →
    first su < 2 ^ w → second kl sl ll < 2 ^ w → second ku su lu < 2 ^ w →
    P.M₀ * max (first sl) (second kl sl ll) < 2 ^ w →
    P.M₀ * max (first su) (second ku su lu) < 2 ^ w →
    common * P.k < 2 ^ w →
    ∃ out c, Runs w p ω (assembleInitBaseThreshold power bits load log pack) st .normal out c ∧
      (out.regs 10 = 0 ∧ out.mem cell = st.mem cell ∨
        out.regs 10 = 1 ∧ out.mem cell = rebuildThresholdWord (SparseCore.sparseCoreParams E) P N 0) ∧
      (∀ a < heap, a ≠ cell → out.mem a = st.mem a) ∧
      c ≤ 100 * exponent + 71 * limbs + Num.logarithmCost limbs precision (N + 2).size +
        14 * (N + 2).size + 364 := by
  dsimp only
  intro hew hcommon hf hc hfirst hlo hhi hbaseLo hbaseHi hmul
  obtain ⟨mid, c₁, hr₁, hsize, hflag, _, _, _, _, _, _, _, _, _, hkeep, hk', hm, hc₁⟩ :=
    assembleInitBaseLevelSize_runs (ω := ω) E P himpl hM hk hs hd hb hg hkl hku hsl hsu hll hlu
      hsPos hbPos hslPos hllPos hluPos horder hklBound hkuBound hslBound hsuBound hllBound hluBound
      hsw huw hw hew hcommon hf hc hfirst hlo hhi hbaseLo hbaseHi hmul
  obtain ⟨out, c₂, hr₂, hpost, hframe, hc₂⟩ :=
    guardInitThreshold_fromLevelCheck_runs (ω := ω) (SparseCore.sparseCoreParams E) P 0
      hbits hload hlog hpack ((hkeep 92 (by decide)).trans hN) ((hkeep 67 (by decide)).trans hL)
      ((hkeep 68 (by decide)).trans hP) ((hkeep 98 (by decide)).trans hh) hflag hsize hk'
      ((hkeep 11 (by decide)).trans hdest) hcell hwLog hword hfit hroom (hm.symm ▸ hz)
      hdiv hacc hcap hprec hwidth hkpos hupper hbudget
  exact ⟨out, c₁ + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c₁, c₂, hr₁, hr₂, rfl⟩),
    by simpa only [hm] using hpost, fun a ha hne => (hframe a ha hne).trans (congrFun hm a), by omega⟩

/-- Compute the stretch enclosure and fill the checked threshold table,
evaluating the vertex logarithm only once. -/
@[expose] def assembleInitThresholdTable (power bits load log pack : ℕ) : Stmt :=
  assembleInitBaseLevelSize power ;; cacheAndWriteInitThresholdTable bits load log pack

/-- After a successful run, all threshold entries agree with the
integer tests of Algorithm 1. An inconclusive check clears the flag. -/
theorem assembleInitThresholdTable_runs
    (E : SparseCore.SparseCoreEnv) (P : ChainParams)
    {w h power bits load log pack N precision limbs heap base last scale kl ku sl su ll lu : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p power (initStretchPowerContract w))
    (hM : st.regs 22 = P.M₀) (hk : st.regs 1 = P.k)
    (hs : st.regs 4 = scale) (hd : st.regs 44 = E.L)
    (hb : st.regs 47 = E.B_fn (P.M₀ ^ 2)) (hg : st.regs 48 = E.d_fn (P.M₀ ^ 2))
    (hkl : st.regs 49 = kl) (hku : st.regs 51 = ku)
    (hsl : st.regs 50 = sl) (hsu : st.regs 52 = su)
    (hll : st.regs 26 = ll) (hlu : st.regs 27 = lu)
    (hsPos : 0 < scale) (hbPos : 0 < E.B_fn (P.M₀ ^ 2))
    (hslPos : 0 < sl) (hllPos : 0 < ll) (hluPos : 0 < lu) (horder : sl ≤ su)
    (hklBound : (kl : ℝ) / scale ≤ (E.P_fn (P.M₀ ^ 2)).K_s)
    (hkuBound : (E.P_fn (P.M₀ ^ 2)).K_s ≤ (ku : ℝ) / scale)
    (hslBound : (sl : ℝ) / scale ≤ (E.P_fn (P.M₀ ^ 2)).γ_ℓ)
    (hsuBound : (E.P_fn (P.M₀ ^ 2)).γ_ℓ ≤ (su : ℝ) / scale)
    (hllBound : (ll : ℝ) / scale ≤ SparseCore.coreLambdaS (E.P_fn (P.M₀ ^ 2)) (P.M₀ ^ 2))
    (hluBound : SparseCore.coreLambdaS (E.P_fn (P.M₀ ^ 2)) (P.M₀ ^ 2) ≤ (lu : ℝ) / scale)
    (hsw : scale < 2 ^ w) (huw : su < 2 ^ w) (hw : 115 < 2 ^ w)
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hlog : MeetsContract w p log (Num.logarithmContract w h (precision - (N + 2).size - 10)))
    (hN : st.regs 92 = N)
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision) (hh : st.regs 98 = heap)
    (hwLog : N + 2 < 2 ^ w) (hword : (N + 2) * 2 ^ precision < 2 ^ w)
    (hfit : 2 * ((N + 2) * 2 ^ precision) < Num.capacity h limbs)
    (hroom : heap + limbs + limbs + Num.logarithmSpace limbs precision (N + 2).size < 2 ^ w)
    (hz : ZeroFrom st.mem heap) (hdiv : h ∣ precision)
    (hacc : (N + 2).size + 11 ≤ precision) (hcap : precision + (N + 2).size + 4 ≤ h * limbs)
    (hprec : 2 * precision + 9 < 2 ^ w) (hwidth : precision < w)
    (hScaleEq : scale = 2 ^ precision)
    (hTable : st.regs 53 = base) (hIndex : st.regs 54 = 0) (hBranch : st.regs 55 = P.k)
    (hLast : st.regs 56 = last) (hCell : base + last < heap) :
    let exponent := max (E.L + 1) 3
    let common := scale ^ exponent
    let factor := 3 ^ E.L * scale ^ (exponent - (E.L + 1))
    let cap := (E.L + 1) * E.B_fn (P.M₀ ^ 2) * (2 * E.d_fn (P.M₀ ^ 2) + 190)
    let first := fun s : ℕ => factor * s ^ (E.L + 1)
    let second : ℕ → ℕ → ℕ → ℕ := fun k s l : ℕ =>
      11 * (cap * k * s * l + 115 * scale ^ 3) * scale ^ (exponent - 3)
    exponent < 2 ^ w → common < 2 ^ w → factor < 2 ^ w → cap < 2 ^ w →
    first su < 2 ^ w → second kl sl ll < 2 ^ w → second ku su lu < 2 ^ w →
    P.M₀ * max (first sl) (second kl sl ll) < 2 ^ w →
    P.M₀ * max (first su) (second ku su lu) < 2 ^ w →
    common * P.k < 2 ^ w →
    (∀ j ≤ last,
      P.M₀ * max (first sl) (second kl sl ll) ^ (j + 1) < 2 ^ w ∧
      P.M₀ * max (first su) (second ku su lu) ^ (j + 1) < 2 ^ w ∧
      common * (common * P.k) ^ j < 2 ^ w) →
    ((N + 2) * 2 ^ precision) ^ 2 < 2 ^ w →
    (∀ j ≤ last, levelM (SparseCore.sparseCoreParams E) P j * (2 ^ precision) ^ 2 +
      P.k * ((N + 2) * 2 ^ precision) ^ 2 < 2 ^ w) →
    ∃ out c, Runs w p ω (assembleInitThresholdTable power bits load log pack) st .normal out c ∧
      (out.regs 10 = 0 ∨ out.regs 10 = 1 ∧
        ∀ j ≤ last, out.mem (base + j) = rebuildThresholdWord (SparseCore.sparseCoreParams E) P N j) ∧
      (∀ a < heap, a < base ∨ base + last < a → out.mem a = st.mem a) ∧
      (∀ r, 46 < r → r < 95 → r ≠ 54 → out.regs r = st.regs r) ∧
      heap + limbs ≤ out.regs 99 ∧ out.regs 99 < 2 ^ w ∧ ZeroFrom out.mem (out.regs 99) ∧
      c ≤ 100 * exponent + 71 * limbs + (25 * limbs + 143) * last +
        Num.logarithmCost limbs precision (N + 2).size + 14 * (N + 2).size + 374 := by
  dsimp only
  intro hew hcommon hf hc hfirst hlo hhi hbaseLo hbaseHi hmul hprod hupper hbudget
  obtain ⟨mid, c₁, hr₁, hsize, hflag, h19, h20, h23, h14, h15, h16, h21,
    hloBound, hhiBound, hkeep, _, hm, hc₁⟩ :=
    assembleInitBaseLevelSize_runs (ω := ω) E P himpl hM hk hs hd hb hg hkl hku hsl hsu hll hlu
      hsPos hbPos hslPos hllPos hluPos horder hklBound hkuBound hslBound hsuBound hllBound hluBound
      hsw huw hw hew hcommon hf hc hfirst hlo hhi hbaseLo hbaseHi hmul
  have hs' : 0 < scale ^ max (E.L + 1) 3 := pow_pos hsPos _
  have hu' : 0 < mid.regs 20 := by
    by_contra! h
    have hzero := Nat.eq_zero_of_le_zero h
    rw [hzero, Nat.cast_zero, zero_div] at hhiBound
    change SparseCore.gammaLEnv E (P.M₀ ^ 2) ≤ 0 at hhiBound
    linarith [SparseCore.gammaLEnv_ge_three E (P.M₀ ^ 2)]
  have hscale' : mid.regs 4 = 2 ^ precision :=
    (hkeep 4 (by decide)).trans (hs.trans hScaleEq)
  obtain ⟨out, c₂, hr₂, hres, hframe, hregs, hretLo, hretHi, hzero, hc₂⟩ :=
    cacheAndWriteInitThresholdTable_runs (ω := ω) (SparseCore.sparseCoreParams E) P
      hpack hbits hload hlog ((hkeep 92 (by decide)).trans hN) hscale'
      ((hkeep 67 (by decide)).trans hL) ((hkeep 68 (by decide)).trans hP)
      ((hkeep 98 (by decide)).trans hh) hwLog hword hfit hroom (hm.symm ▸ hz) hdiv hacc hcap
      hprec hwidth ((hkeep 53 (by decide)).trans hTable) ((hkeep 54 (by decide)).trans hIndex)
      ((hkeep 55 (by decide)).trans hBranch) h14 h15 h16 rfl rfl h21 hs' hu' hloBound hhiBound
      (by simpa only [h19, h20] using hprod) (by omega) hCell
      ((hkeep 56 (by decide)).trans hLast) hflag hsize hupper hbudget
  exact ⟨out, c₁ + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c₁, c₂, hr₁, hr₂, rfl⟩), hres,
    fun a ha ho => (hframe a ha ho).trans (congrFun hm a),
    fun r hlo hhi hne => (hregs r (by omega) hhi hne).trans (hkeep r (Or.inr hlo)), hretLo, hretHi, hzero, by omega⟩

/-- Reserve the table after the Init header and fill it using the
runtime stretch and logarithm computations. -/
@[expose] def reserveAndAssembleInitThresholdTable (power bits load log pack : ℕ) : Stmt :=
  reserveInitThresholdTable ;; assembleInitThresholdTable power bits load log pack

/-- Successful initialization provides the whole model table at the
reserved address, with memory before the table preserved. -/
theorem reserveAndAssembleInitThresholdTable_runs
    (E : SparseCore.SparseCoreEnv) (P : ChainParams)
    {w h power bits load log pack N precision limbs base last scale kl ku sl su ll lu : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p power (initStretchPowerContract w))
    (hM : st.regs 22 = P.M₀) (hk : st.regs 1 = P.k)
    (hs : st.regs 4 = scale) (hd : st.regs 44 = E.L)
    (hb : st.regs 47 = E.B_fn (P.M₀ ^ 2)) (hg : st.regs 48 = E.d_fn (P.M₀ ^ 2))
    (hkl : st.regs 49 = kl) (hku : st.regs 51 = ku)
    (hsl : st.regs 50 = sl) (hsu : st.regs 52 = su)
    (hll : st.regs 26 = ll) (hlu : st.regs 27 = lu)
    (hsPos : 0 < scale) (hbPos : 0 < E.B_fn (P.M₀ ^ 2))
    (hslPos : 0 < sl) (hllPos : 0 < ll) (hluPos : 0 < lu) (horder : sl ≤ su)
    (hklBound : (kl : ℝ) / scale ≤ (E.P_fn (P.M₀ ^ 2)).K_s)
    (hkuBound : (E.P_fn (P.M₀ ^ 2)).K_s ≤ (ku : ℝ) / scale)
    (hslBound : (sl : ℝ) / scale ≤ (E.P_fn (P.M₀ ^ 2)).γ_ℓ)
    (hsuBound : (E.P_fn (P.M₀ ^ 2)).γ_ℓ ≤ (su : ℝ) / scale)
    (hllBound : (ll : ℝ) / scale ≤ SparseCore.coreLambdaS (E.P_fn (P.M₀ ^ 2)) (P.M₀ ^ 2))
    (hluBound : SparseCore.coreLambdaS (E.P_fn (P.M₀ ^ 2)) (P.M₀ ^ 2) ≤ (lu : ℝ) / scale)
    (hsw : scale < 2 ^ w) (huw : su < 2 ^ w) (hw : 115 < 2 ^ w)
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hlog : MeetsContract w p log (Num.logarithmContract w h (precision - (N + 2).size - 10)))
    (hN : st.regs 92 = N)
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision)
    (hwLog : N + 2 < 2 ^ w) (hword : (N + 2) * 2 ^ precision < 2 ^ w)
    (hfit : 2 * ((N + 2) * 2 ^ precision) < Num.capacity h limbs)
    (hroom : base + last + 1 + limbs + limbs + Num.logarithmSpace limbs precision (N + 2).size < 2 ^ w)
    (hz : ZeroFrom st.mem base) (hdiv : h ∣ precision)
    (hacc : (N + 2).size + 11 ≤ precision) (hcap : precision + (N + 2).size + 4 ≤ h * limbs)
    (hprec : 2 * precision + 9 < 2 ^ w) (hwidth : precision < w)
    (hScaleEq : scale = 2 ^ precision)
    (hBase : st.regs 77 = base) (hBranch : st.regs 76 = P.k) (hLast : st.regs 75 = last) :
    let exponent := max (E.L + 1) 3
    let common := scale ^ exponent
    let factor := 3 ^ E.L * scale ^ (exponent - (E.L + 1))
    let cap := (E.L + 1) * E.B_fn (P.M₀ ^ 2) * (2 * E.d_fn (P.M₀ ^ 2) + 190)
    let first := fun s : ℕ => factor * s ^ (E.L + 1)
    let second : ℕ → ℕ → ℕ → ℕ := fun k s l : ℕ =>
      11 * (cap * k * s * l + 115 * scale ^ 3) * scale ^ (exponent - 3)
    exponent < 2 ^ w → common < 2 ^ w → factor < 2 ^ w → cap < 2 ^ w →
    first su < 2 ^ w → second kl sl ll < 2 ^ w → second ku su lu < 2 ^ w →
    P.M₀ * max (first sl) (second kl sl ll) < 2 ^ w →
    P.M₀ * max (first su) (second ku su lu) < 2 ^ w →
    common * P.k < 2 ^ w →
    (∀ j ≤ last,
      P.M₀ * max (first sl) (second kl sl ll) ^ (j + 1) < 2 ^ w ∧
      P.M₀ * max (first su) (second ku su lu) ^ (j + 1) < 2 ^ w ∧
      common * (common * P.k) ^ j < 2 ^ w) →
    ((N + 2) * 2 ^ precision) ^ 2 < 2 ^ w →
    (∀ j ≤ last, levelM (SparseCore.sparseCoreParams E) P j * (2 ^ precision) ^ 2 +
      P.k * ((N + 2) * 2 ^ precision) ^ 2 < 2 ^ w) →
    ∃ out c, Runs w p ω (reserveAndAssembleInitThresholdTable power bits load log pack) st .normal out c ∧
      (out.regs 10 = 0 ∨ out.regs 10 = 1 ∧
        ∀ j ≤ last, out.mem (base + j) = rebuildThresholdWord (SparseCore.sparseCoreParams E) P N j) ∧
      (∀ a < base, out.mem a = st.mem a) ∧
      out.regs 83 = base ∧ (∀ r, 56 < r → r < 95 → r ≠ 83 → out.regs r = st.regs r) ∧
      base + last + 1 + limbs ≤ out.regs 99 ∧ out.regs 99 < 2 ^ w ∧ ZeroFrom out.mem (out.regs 99) ∧
      c ≤ 100 * exponent + 71 * limbs + (25 * limbs + 143) * last +
        Num.logarithmCost limbs precision (N + 2).size + 14 * (N + 2).size + 396 := by
  dsimp only
  intro hew hcommon hf hc hfirst hlo hhi hbaseLo hbaseHi hmul hprod hupper hbudget
  obtain ⟨mid, hr₁, h53, h54, h55, h56, h83, h98, hkeep, hm, hzero⟩ :=
    reserveInitThresholdTable_runs (w := w) (p := p) (ω := ω) hBase hLast hBranch (by omega) hz
  have hr (r : ℕ) (h : r ≠ 53 ∧ r ≠ 54 ∧ r ≠ 55 ∧ r ≠ 56 ∧ r ≠ 83 ∧ r ≠ 98) :
      mid.regs r = st.regs r := hkeep r h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
  obtain ⟨out, c, hr₂, hres, hframe, hregs, hretLo, hretHi, hzero', hcost⟩ :=
    assembleInitThresholdTable_runs (ω := ω) E P himpl
      ((hr 22 (by decide)).trans hM) ((hr 1 (by decide)).trans hk)
      ((hr 4 (by decide)).trans hs) ((hr 44 (by decide)).trans hd)
      ((hr 47 (by decide)).trans hb) ((hr 48 (by decide)).trans hg)
      ((hr 49 (by decide)).trans hkl) ((hr 51 (by decide)).trans hku)
      ((hr 50 (by decide)).trans hsl) ((hr 52 (by decide)).trans hsu)
      ((hr 26 (by decide)).trans hll) ((hr 27 (by decide)).trans hlu)
      hsPos hbPos hslPos hllPos hluPos horder hklBound hkuBound hslBound hsuBound hllBound hluBound
      hsw huw hw hpack hbits hload hlog ((hr 92 (by decide)).trans hN)
      ((hr 67 (by decide)).trans hL) ((hr 68 (by decide)).trans hP) h98 hwLog hword hfit
      hroom hzero hdiv hacc hcap hprec hwidth hScaleEq h53 h54 h55 h56 (by omega)
      hew hcommon hf hc hfirst hlo hhi hbaseLo hbaseHi hmul hprod hupper hbudget
  exact ⟨out, 21 + c + 1, runs_seq_iff.mpr (Or.inr ⟨mid, 21, c, hr₁, hr₂, rfl⟩), hres,
    fun a ha => (hframe a (by omega) (Or.inl ha)).trans (congrFun hm a),
    (hregs 83 (by decide) (by decide) (by decide)).trans h83,
    fun r hlo hhi hne => (hregs r (by omega) hhi (by omega)).trans
      (hr r ⟨by omega, by omega, by omega, by omega, hne, by omega⟩),
    hretLo, hretHi, hzero', by omega⟩

/-- Evaluate the logarithm used by the sparsity factor at the runtime
sparse-core edge bound, preserving the original graph count in register 57. -/
@[expose] def cacheInitSparseCoreLog (bits load log : ℕ) : Stmt :=
  prepareInitSparseCoreLogInput ;; cacheInitVertexLog bits load log

/-- The cached block approximates the logarithm in the model's
sparse-core sparsity factor. -/
theorem cacheInitSparseCoreLog_runs
    {w h bits load log M N precision limbs heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hM : st.regs 22 = M) (hN : st.regs 92 = N) (hs : st.regs 4 = 2 ^ precision)
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision) (hh : st.regs 98 = heap)
    (hMw : M ^ 2 < 2 ^ w) (hw : 60 < 2 ^ w)
    (hlinear : 2 * M ^ 2 + 60 < 2 ^ w) (hproduct : M ^ 2 * (2 * M ^ 2 + 60) < 2 ^ w) :
    let input := SparseCore.coreNMax (M ^ 2) + M ^ 2
    let range := (input + 2).size
    let accuracy := precision - range - 10
    MeetsContract w p log (Num.logarithmContract w h accuracy) →
    input + 2 < 2 ^ w → (input + 2) * 2 ^ precision < 2 ^ w →
    2 * ((input + 2) * 2 ^ precision) < Num.capacity h limbs →
    heap + limbs + limbs + Num.logarithmSpace limbs precision range < 2 ^ w →
    ZeroFrom st.mem heap → h ∣ precision → range + 11 ≤ precision →
    precision + range + 4 ≤ h * limbs → 2 * precision + 9 < 2 ^ w →
    ∃ out c ret, Runs w p ω (cacheInitSparseCoreLog bits load log) st .normal out c ∧
      out.regs 57 = N ∧ out.regs 99 = ret ∧ out.regs 100 = accuracy ∧
      heap + limbs ≤ ret ∧ ret < 2 ^ w ∧
      ret ≤ heap + limbs + limbs + Num.logarithmSpace limbs precision range ∧ Num.Valid out.mem (ret - limbs) h limbs ∧
      |Num.fixVal out.mem (ret - limbs) h limbs precision -
          Real.log ((SparseCore.coreNMax (M ^ 2) : ℝ) + ((M ^ 2 : ℕ) : ℝ) + 2)| ≤
        1 / (2 : ℝ) ^ accuracy ∧
      (∀ r, r < 95 → r ≠ 24 → r ≠ 57 → r ≠ 92 → out.regs r = st.regs r) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem ret ∧
      c ≤ 46 * limbs + Num.logarithmCost limbs precision range + 14 * range + 76 := by
  dsimp only
  intro hlog hinput hword hfit hroom hz hdiv hacc hcap hprec
  obtain ⟨mid, hr, _, hsave, harg, hkeep, hm, _⟩ :=
    prepareInitSparseCoreLogInput_runs (p := p) (ω := ω) hM hN hMw hw hlinear hproduct
  have hk (r : ℕ) (hne : r ≠ 24 ∧ r ≠ 57 ∧ r ≠ 92) : mid.regs r = st.regs r :=
    hkeep r hne.1 hne.2.1 hne.2.2
  obtain ⟨out, c, ret, hr', hret, hq, hbottom, htop, hretSpace, hv, herr, hkeep', hframe, hzero, hc⟩ :=
    cacheInitVertexLog_runs (ω := ω) hbits hload hlog harg ((hk 4 (by decide)).trans hs)
      ((hk 67 (by decide)).trans hL) ((hk 68 (by decide)).trans hP) ((hk 98 (by decide)).trans hh)
      hinput hword hfit hroom (hm.symm ▸ hz) hdiv hacc hcap hprec
  refine ⟨out, 16 + c + 1, ret, runs_seq_iff.mpr (Or.inr ⟨mid, 16, c, hr, hr', rfl⟩),
    (hkeep' 57 (by decide)).trans hsave, hret, hq, hbottom, htop, hretSpace, hv, ?_,
    fun r hr h24 h57 h92 => (hkeep' r (Or.inl hr)).trans (hkeep r h24 h57 h92),
    fun a ha => (hframe a ha).trans (congrFun hm a), hzero, by omega⟩
  simpa only [Nat.cast_add] using herr

/-- Unpack the cached sparse-core logarithm and form the two sparsity
factor numerators at the runtime scale. -/
@[expose] def prepareInitSparseCoreFactorFromLog (pack : ℕ) : Stmt :=
  prepareInitLogEnclosure pack ;; prepareInitSparseCoreLogFactor

/-- The factor words enclose the model's logarithmic sparsity factor. -/
theorem prepareInitSparseCoreFactorFromLog_runs (E : SparseCore.SparseCoreEnv) (m : ℕ)
    {w h pack ret limbs precision accuracy : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hret : st.regs 99 = ret) (hL : st.regs 67 = limbs)
    (hP : st.regs 68 = precision) (hq : st.regs 100 = accuracy)
    (hle : limbs ≤ ret) (hw : ret < 2 ^ w) (hwidth : precision < w)
    (hv : Num.Valid st.mem (ret - limbs) h limbs)
    (hqpos : 1 ≤ accuracy) (hqprec : accuracy ≤ precision)
    (herr : |Num.fixVal st.mem (ret - limbs) h limbs precision - Real.log ((SparseCore.coreNMax m : ℝ) + (m : ℝ) + 2)| ≤
      1 / (2 : ℝ) ^ accuracy)
    (hfit : (Num.intVal st.mem (ret - limbs) h limbs).toNat < 2 ^ w)
    (hps : st.regs 25 = (E.P_fn m).p_s) (hp : (E.P_fn m).p_s ≤ 1)
    (hroom : 2 ^ precision + ((Num.intVal st.mem (ret - limbs) h limbs).toNat +
      2 ^ (precision - accuracy)) < 2 ^ w) :
    ∃ out c, Runs w p ω (prepareInitSparseCoreFactorFromLog pack) st .normal out c ∧
      (out.regs 26 : ℝ) / (2 ^ precision : ℕ) ≤ SparseCore.coreLambdaS (E.P_fn m) m ∧
      SparseCore.coreLambdaS (E.P_fn m) m ≤ (out.regs 27 : ℝ) / (2 ^ precision : ℕ) ∧
      2 ^ precision ≤ out.regs 26 ∧ 2 ^ precision ≤ out.regs 27 ∧
      out.regs 26 ≤ out.regs 27 ∧
      out.regs 27 ≤ 2 ^ precision + ((Num.intVal st.mem (ret - limbs) h limbs).toNat +
        2 ^ (precision - accuracy)) ∧
      out.regs 27 - out.regs 26 ≤ 2 * 2 ^ (precision - accuracy) ∧
      out.regs 4 = 2 ^ precision ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 26 → r ≠ 27 → out.regs r = st.regs r) ∧
      c ≤ 25 * limbs + 41 := by
  have herr' : |Num.fixVal st.mem (ret - limbs) h limbs precision -
      Real.log (((SparseCore.coreNMax m + m : ℕ) : ℝ) + 2)| ≤ 1 / (2 : ℝ) ^ accuracy := by
    simpa only [Nat.cast_add] using herr
  obtain ⟨mid, c, hr, ha, he, hs, herror, hk, hm, hc⟩ :=
    prepareInitLogEnclosure_runs (ω := ω) hpack hret hL hP hq hle hw hwidth hv hqpos hqprec herr' hfit
  obtain ⟨out, hr', hlo, hhi, hloScale, hhiScale, hord, hupp, hgap, hk', hm', _⟩ :=
    prepareInitSparseCoreLogFactor_runs (p := p) (ω := ω) E m hp (by positivity) ha he hs
      ((hk 25 (by decide) (by decide) (by decide)).trans hps) hroom
      (by simpa only [Nat.cast_add] using herror)
  exact ⟨out, c + 17 + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c, 17, hr, hr', rfl⟩),
    hlo, hhi, hloScale, hhiScale, hord, hupp, hgap, (hk' 4 (by decide) (by decide)).trans hs, hm'.trans hm,
    fun r h2 h3 h4 h26 h27 => (hk' r h26 h27).trans (hk r h2 h3 h4), by omega⟩

/-- Compute and unpack the sparse-core logarithm for the stretch bound. -/
@[expose] def computeInitSparseCoreLogFactor (bits load log pack : ℕ) : Stmt :=
  cacheInitSparseCoreLog bits load log ;; prepareInitSparseCoreFactorFromLog pack

/-- This fragment derives the logarithmic sparsity-factor endpoints
from the runtime base size and keeps the scratch heap available. -/
theorem computeInitSparseCoreLogFactor_runs
    (E : SparseCore.SparseCoreEnv) (M : ℕ)
    {w h bits load log pack N precision limbs heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hps : st.regs 25 = (E.P_fn (M ^ 2)).p_s) (hp : (E.P_fn (M ^ 2)).p_s ≤ 1)
    (hwidth : precision < w)
    (hM : st.regs 22 = M) (hN : st.regs 92 = N) (hs : st.regs 4 = 2 ^ precision)
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision) (hh : st.regs 98 = heap)
    (hMw : M ^ 2 < 2 ^ w) (hw : 60 < 2 ^ w)
    (hlinear : 2 * M ^ 2 + 60 < 2 ^ w) (hproduct : M ^ 2 * (2 * M ^ 2 + 60) < 2 ^ w) :
    let input := SparseCore.coreNMax (M ^ 2) + M ^ 2
    let range := (input + 2).size
    let accuracy := precision - range - 10
    MeetsContract w p log (Num.logarithmContract w h accuracy) →
    input + 2 < 2 ^ w → (input + 2) * 2 ^ precision < 2 ^ w →
    2 * ((input + 2) * 2 ^ precision) < Num.capacity h limbs →
    heap + limbs + limbs + Num.logarithmSpace limbs precision range < 2 ^ w →
    ZeroFrom st.mem heap → h ∣ precision → range + 11 ≤ precision →
    precision + range + 4 ≤ h * limbs → 2 * precision + 9 < 2 ^ w →
    (input + 3) * 2 ^ precision < 2 ^ w →
    ∃ out c ret, Runs w p ω (computeInitSparseCoreLogFactor bits load log pack) st .normal out c ∧
      (out.regs 26 : ℝ) / (2 ^ precision : ℕ) ≤ SparseCore.coreLambdaS (E.P_fn (M ^ 2)) (M ^ 2) ∧
      SparseCore.coreLambdaS (E.P_fn (M ^ 2)) (M ^ 2) ≤ (out.regs 27 : ℝ) / (2 ^ precision : ℕ) ∧
      2 ^ precision ≤ out.regs 26 ∧ 2 ^ precision ≤ out.regs 27 ∧
      out.regs 26 ≤ out.regs 27 ∧ out.regs 27 ≤ (input + 3) * 2 ^ precision ∧
      out.regs 27 - out.regs 26 ≤ 2 * 2 ^ (precision - accuracy) ∧
      out.regs 4 = 2 ^ precision ∧ out.regs 57 = N ∧ out.regs 99 = ret ∧ heap ≤ ret ∧ ret < 2 ^ w ∧
      ret ≤ heap + limbs + limbs + Num.logarithmSpace limbs precision range ∧
      (∀ r, r < 95 → r ∉ ([2, 3, 4, 24, 26, 27, 57, 92] : List ℕ) →
        out.regs r = st.regs r) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem ret ∧
      c ≤ 71 * limbs + Num.logarithmCost limbs precision range + 14 * range + 118 := by
  dsimp only
  intro hlog hinput hword hfit hroom hz hdiv hacc hcap hprec hendpointWord
  obtain ⟨mid, c₁, ret, hr₁, h57, hret, hq, hbottom, htop, hretSpace, hv, herr, hkeep, hframe, hzero, hc₁⟩ :=
    cacheInitSparseCoreLog_runs (ω := ω) hbits hload hM hN hs hL hP hh hMw hw hlinear hproduct
      hlog hinput hword hfit hroom hz hdiv hacc hcap hprec
  let input := SparseCore.coreNMax (M ^ 2) + M ^ 2
  let accuracy := precision - (input + 2).size - 10
  have hqpos : 1 ≤ accuracy := by dsimp [accuracy, input]; omega
  have hqprec : accuracy ≤ precision := by dsimp [accuracy]; omega
  have herr' : |Num.fixVal mid.mem (ret - limbs) h limbs precision -
      Real.log ((input : ℝ) + 2)| ≤ 1 / (2 : ℝ) ^ accuracy := by
    simpa only [input, Nat.cast_add] using herr
  have hscaled := (initVertexLog_scaledError hqpos hqprec herr').2
  let approx := (Num.intVal mid.mem (ret - limbs) h limbs).toNat
  let error : ℕ := 2 ^ (precision - accuracy)
  have he : 2 * error ≤ 2 ^ precision := by
    dsimp [error]
    rw [← pow_succ']
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hbound : approx + error ≤ (input + 2) * 2 ^ precision :=
    initLogUpper_le_scaledInput (by positivity) he
      (by simpa only [approx, error, Nat.cast_pow, Nat.cast_ofNat] using hscaled)
  have hsum : 2 ^ precision + (approx + error) ≤ (input + 3) * 2 ^ precision := by
    have heq : 2 ^ precision + (input + 2) * 2 ^ precision =
        (input + 3) * 2 ^ precision := by ring
    rw [← heq]
    exact Nat.add_le_add_left hbound _
  have happrox : approx < 2 ^ w :=
    ((Nat.le_add_right approx error).trans hbound).trans_lt hword
  obtain ⟨out, c₂, hr₂, hlo, hhi, hloScale, hhiScale, hord, hupp, hgap, hscale, hm, hreg, hc₂⟩ :=
    prepareInitSparseCoreFactorFromLog_runs (ω := ω) E (M ^ 2) hpack hret
      ((hkeep 67 (by decide) (by decide) (by decide) (by decide)).trans hL)
      ((hkeep 68 (by decide) (by decide) (by decide) (by decide)).trans hP)
      hq (by omega) htop hwidth hv hqpos hqprec herr happrox
      ((hkeep 25 (by decide) (by decide) (by decide) (by decide)).trans hps) hp (hsum.trans_lt hendpointWord)
  refine ⟨out, c₁ + c₂ + 1, ret, runs_seq_iff.mpr (Or.inr ⟨mid, c₁, c₂, hr₁, hr₂, rfl⟩),
    hlo, hhi, hloScale, hhiScale, hord, hupp.trans hsum, hgap, hscale, (hreg 57 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h57,
    (hreg 99 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hret, by omega, htop, hretSpace,
    ?_, fun a ha => (congrFun hm a).trans (hframe a ha), hm.symm ▸ hzero, by omega⟩
  intro r hr hne
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hne
  rcases hne with ⟨h2, h3, h4, h24, h26, h27, h57', h92⟩
  exact (hreg r h2 h3 h4 h26 h27).trans (hkeep r hr h24 h57' h92)

/-- Restore the graph's vertex count and pass the fresh heap to table reservation. -/
@[expose] def finishInitSparseCoreLog : Stmt :=
  .assign 92 (.reg 57) ;; .assign 77 (.reg 99)

/-- The handoff writes only the runtime vertex count and the table reservation base. -/
theorem finishInitSparseCoreLog_runs {w N heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hN : st.regs 57 = N) (hh : st.regs 99 = heap) :
    ∃ out, Runs w p ω finishInitSparseCoreLog st .normal out 5 ∧
      out.regs 92 = N ∧ out.regs 77 = heap ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 92 → r ≠ 77 → out.regs r = st.regs r) := by
  let mid := { st with regs := Function.update st.regs 92 N }
  let out := { mid with regs := Function.update mid.regs 77 heap }
  have hr₁ : Runs w p ω (.assign 92 (.reg 57)) st .normal mid 2 :=
    runs_assign_iff.mpr ⟨N, by simp [Expr.eval, hN], rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign 77 (.reg 99)) mid .normal out 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, mid, hh], rfl, rfl, rfl⟩
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 2, 2, hr₁, hr₂, rfl⟩),
    by simp [out, mid], by simp [out], rfl, ?_⟩
  intro r h92 h77
  simp [out, mid, Function.update_of_ne, h92, h77]

/-- Derive the sparse-core logarithmic factor before reserving the threshold table. -/
@[expose] def initSparseCoreLogForThresholds (bits load log pack : ℕ) : Stmt :=
  computeInitSparseCoreLogFactor bits load log pack ;; finishInitSparseCoreLog

/-- The sparse-core logarithm uses an absolute endpoint budget linear in
its integer argument. The budget is independent of the working precision. -/
theorem sparseCoreLog_error_le (input precision : ℕ)
    (hprec : (input + 2).size + 11 ≤ precision) :
    2 * 2 ^ (precision - (precision - (input + 2).size - 10)) ≤
      4096 * (input + 2) := by
  let n := input + 2
  have hsize : 0 < n.size := by
    by_contra! h
    have hn := Nat.lt_size_self n
    rw [show n.size = 0 by omega, pow_zero] at hn
    dsimp [n] at hn
    omega
  have hlow : 2 ^ (n.size - 1) ≤ n := by
    by_contra! h
    have hsmall := Nat.size_le.mpr h
    omega
  have hpow : 2 ^ n.size ≤ 2 * n := by
    rw [show n.size = (n.size - 1) + 1 by omega, pow_succ']
    exact Nat.mul_le_mul_left 2 hlow
  change 2 * 2 ^ (precision - (precision - n.size - 10)) ≤ 4096 * n
  change n.size + 11 ≤ precision at hprec
  rw [show precision - (precision - n.size - 10) = n.size + 10 by omega, pow_add]
  calc
    2 * (2 ^ n.size * 2 ^ 10) = 2048 * 2 ^ n.size := by ring
    _ ≤ 2048 * (2 * n) := Nat.mul_le_mul_left _ hpow
    _ = 4096 * n := by ring

/-- The logarithmic factor bounds and fresh heap feed the threshold computation
with the original graph size restored. -/
theorem initSparseCoreLogForThresholds_runs
    (E : SparseCore.SparseCoreEnv) (M : ℕ)
    {w h bits load log pack N precision limbs heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hps : st.regs 25 = (E.P_fn (M ^ 2)).p_s) (hp : (E.P_fn (M ^ 2)).p_s ≤ 1)
    (hwidth : precision < w)
    (hM : st.regs 22 = M) (hN : st.regs 92 = N) (hs : st.regs 4 = 2 ^ precision)
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision) (hh : st.regs 98 = heap)
    (hMw : M ^ 2 < 2 ^ w) (hw : 60 < 2 ^ w)
    (hlinear : 2 * M ^ 2 + 60 < 2 ^ w) (hproduct : M ^ 2 * (2 * M ^ 2 + 60) < 2 ^ w) :
    let input := SparseCore.coreNMax (M ^ 2) + M ^ 2
    let range := (input + 2).size
    let accuracy := precision - range - 10
    MeetsContract w p log (Num.logarithmContract w h accuracy) →
    input + 2 < 2 ^ w → (input + 2) * 2 ^ precision < 2 ^ w →
    2 * ((input + 2) * 2 ^ precision) < Num.capacity h limbs →
    heap + limbs + limbs + Num.logarithmSpace limbs precision range < 2 ^ w →
    ZeroFrom st.mem heap → h ∣ precision → range + 11 ≤ precision →
    precision + range + 4 ≤ h * limbs → 2 * precision + 9 < 2 ^ w →
    (input + 3) * 2 ^ precision < 2 ^ w →
    ∃ out c ret, Runs w p ω (initSparseCoreLogForThresholds bits load log pack) st .normal out c ∧
      (out.regs 26 : ℝ) / (2 ^ precision : ℕ) ≤ SparseCore.coreLambdaS (E.P_fn (M ^ 2)) (M ^ 2) ∧
      SparseCore.coreLambdaS (E.P_fn (M ^ 2)) (M ^ 2) ≤ (out.regs 27 : ℝ) / (2 ^ precision : ℕ) ∧
      2 ^ precision ≤ out.regs 26 ∧ 2 ^ precision ≤ out.regs 27 ∧
      out.regs 26 ≤ out.regs 27 ∧ out.regs 27 ≤ (input + 3) * 2 ^ precision ∧
      out.regs 27 - out.regs 26 ≤ 4096 * (input + 2) ∧
      out.regs 4 = 2 ^ precision ∧ out.regs 92 = N ∧ out.regs 77 = ret ∧ out.regs 99 = ret ∧ heap ≤ ret ∧ ret < 2 ^ w ∧
      ret ≤ heap + limbs + limbs + Num.logarithmSpace limbs precision range ∧
      (∀ r, r < 95 → r ∉ ([2, 3, 4, 24, 26, 27, 57, 77] : List ℕ) →
        out.regs r = st.regs r) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem ret ∧
      c ≤ 71 * limbs + Num.logarithmCost limbs precision range + 14 * range + 124 := by
  dsimp only
  intro hlog hinput hword hfit hroom hz hdiv hacc hcap hprec hendpoint
  obtain ⟨mid, c, ret, hr, hlo, hhi, hloScale, hhiScale, hord, hupp, hgap, hscale, h57, h99, hbase, htop, hretSpace, hkeep, hframe, hzero, hc⟩ :=
    computeInitSparseCoreLogFactor_runs (ω := ω) E M hbits hload hpack hps hp hwidth
      hM hN hs hL hP hh hMw hw hlinear hproduct hlog hinput hword hfit hroom hz hdiv
      hacc hcap hprec hendpoint
  obtain ⟨out, hr', h92, h77, hm, hk⟩ := finishInitSparseCoreLog_runs (ω := ω) h57 h99
  refine ⟨out, c + 6, ret, runs_seq_iff.mpr (Or.inr ⟨mid, c, 5, hr, hr', rfl⟩),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, (hk 4 (by decide) (by decide)).trans hscale, h92, h77, (hk 99 (by decide) (by decide)).trans h99, hbase, htop, hretSpace, ?_,
    fun a ha => (congrFun hm a).trans (hframe a ha), hm.symm ▸ hzero, by omega⟩
  · rw [hk 26 (by decide) (by decide)]
    exact hlo
  · rw [hk 27 (by decide) (by decide)]
    exact hhi
  · rw [hk 26 (by decide) (by decide)]
    exact hloScale
  · rw [hk 27 (by decide) (by decide)]
    exact hhiScale
  · rw [hk 26 (by decide) (by decide), hk 27 (by decide) (by decide)]
    exact hord
  · rw [hk 27 (by decide) (by decide)]
    exact hupp
  · rw [hk 26 (by decide) (by decide), hk 27 (by decide) (by decide)]
    exact hgap.trans (sparseCoreLog_error_le _ _ hacc)
  · intro r hrange hn
    by_cases he : r = 92
    · subst r
      exact h92.trans hN.symm
    · have hn77 : r ≠ 77 := fun he => hn (he.symm ▸ (by decide : 77 ∈
        ([2, 3, 4, 24, 26, 27, 57, 77] : List ℕ)))
      apply (hk r he hn77).trans (hkeep r hrange _)
      simp only [List.mem_cons, List.not_mem_nil, or_false, he] at hn ⊢
      tauto

/-- Compute the sparse-core logarithm, reserve the table, and fill it with
the checked rebuild thresholds (Algorithm 2, page 28). -/
@[expose] def initThresholdTableFromSparseCoreLog (power bits load log pack : ℕ) : Stmt :=
  initSparseCoreLogForThresholds bits load log pack ;;
    reserveAndAssembleInitThresholdTable power bits load log pack

/-- When the threshold checks succeed, the table agrees with the model at
every runtime level. The code computes the sparsity factor from the base size. -/
theorem initThresholdTableFromSparseCoreLog_runs
    (E : SparseCore.SparseCoreEnv) (P : ChainParams)
    {w h power bits load log pack N precision limbs heap last kl ku sl su : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p power (initStretchPowerContract w))
    (hM : st.regs 22 = P.M₀) (hk : st.regs 1 = P.k)
    (hs : st.regs 4 = 2 ^ precision) (hd : st.regs 44 = E.L)
    (hb : st.regs 47 = E.B_fn (P.M₀ ^ 2)) (hg : st.regs 48 = E.d_fn (P.M₀ ^ 2))
    (hkl : st.regs 49 = kl) (hku : st.regs 51 = ku)
    (hsl : st.regs 50 = sl) (hsu : st.regs 52 = su)
    (hbPos : 0 < E.B_fn (P.M₀ ^ 2))
    (hslPos : 0 < sl) (horder : sl ≤ su)
    (hklBound : (kl : ℝ) / (2 ^ precision : ℕ) ≤ (E.P_fn (P.M₀ ^ 2)).K_s)
    (hkuBound : (E.P_fn (P.M₀ ^ 2)).K_s ≤ (ku : ℝ) / (2 ^ precision : ℕ))
    (hslBound : (sl : ℝ) / (2 ^ precision : ℕ) ≤ (E.P_fn (P.M₀ ^ 2)).γ_ℓ)
    (hsuBound : (E.P_fn (P.M₀ ^ 2)).γ_ℓ ≤ (su : ℝ) / (2 ^ precision : ℕ))
    (huw : su < 2 ^ w) (hw : 115 < 2 ^ w)
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hlog : MeetsContract w p log (Num.logarithmContract w h (precision - (N + 2).size - 10)))
    (hN : st.regs 92 = N)
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision)
    (hwLog : N + 2 < 2 ^ w) (hword : (N + 2) * 2 ^ precision < 2 ^ w)
    (hfit : 2 * ((N + 2) * 2 ^ precision) < Num.capacity h limbs)
    (hz : ZeroFrom st.mem heap) (hdiv : h ∣ precision)
    (hacc : (N + 2).size + 11 ≤ precision) (hcap : precision + (N + 2).size + 4 ≤ h * limbs)
    (hprec : 2 * precision + 9 < 2 ^ w) (hwidth : precision < w)
    (hh : st.regs 98 = heap)
    (hps : st.regs 25 = (E.P_fn (P.M₀ ^ 2)).p_s) (hp : (E.P_fn (P.M₀ ^ 2)).p_s ≤ 1)
    (hMw : P.M₀ ^ 2 < 2 ^ w) (hlinear : 2 * P.M₀ ^ 2 + 60 < 2 ^ w)
    (hproduct : P.M₀ ^ 2 * (2 * P.M₀ ^ 2 + 60) < 2 ^ w)
    (hBranch : st.regs 76 = P.k) (hLast : st.regs 75 = last) :
    let input := SparseCore.coreNMax (P.M₀ ^ 2) + P.M₀ ^ 2
    let range := (input + 2).size
    let limit := heap + limbs + limbs + Num.logarithmSpace limbs precision range
    let scale : ℕ := 2 ^ precision
    MeetsContract w p log (Num.logarithmContract w h (precision - range - 10)) →
    (input + 3) * scale < 2 ^ w → 2 * ((input + 2) * scale) < Num.capacity h limbs →
    range + 11 ≤ precision → precision + range + 4 ≤ h * limbs →
    limit + last + 1 + limbs + limbs + Num.logarithmSpace limbs precision (N + 2).size < 2 ^ w →
    let exponent := max (E.L + 1) 3
    let common := scale ^ exponent
    let factor := 3 ^ E.L * scale ^ (exponent - (E.L + 1))
    let cap := (E.L + 1) * E.B_fn (P.M₀ ^ 2) * (2 * E.d_fn (P.M₀ ^ 2) + 190)
    let first := fun s : ℕ => factor * s ^ (E.L + 1)
    let second : ℕ → ℕ → ℕ → ℕ := fun k s l : ℕ =>
      11 * (cap * k * s * l + 115 * scale ^ 3) * scale ^ (exponent - 3)
    exponent < 2 ^ w → common < 2 ^ w → factor < 2 ^ w → cap < 2 ^ w →
    first su < 2 ^ w → common * P.k < 2 ^ w →
    let logLimit := (input + 3) * scale
    let stretchLo := max (first sl) (second kl sl logLimit)
    let stretchHi := max (first su) (second ku su logLimit)
    second kl sl logLimit < 2 ^ w → second ku su logLimit < 2 ^ w →
    P.M₀ * stretchLo < 2 ^ w → P.M₀ * stretchHi < 2 ^ w →
    (∀ j ≤ last,
      P.M₀ * stretchLo ^ (j + 1) < 2 ^ w ∧
      P.M₀ * stretchHi ^ (j + 1) < 2 ^ w ∧
      common * (common * P.k) ^ j < 2 ^ w) →
    ((N + 2) * 2 ^ precision) ^ 2 < 2 ^ w →
    (∀ j ≤ last, levelM (SparseCore.sparseCoreParams E) P j * (2 ^ precision) ^ 2 +
      P.k * ((N + 2) * 2 ^ precision) ^ 2 < 2 ^ w) →
    ∃ out c base, Runs w p ω (initThresholdTableFromSparseCoreLog power bits load log pack) st .normal out c ∧
      (out.regs 10 = 0 ∨ out.regs 10 = 1 ∧
        ∀ j ≤ last, out.mem (base + j) = rebuildThresholdWord (SparseCore.sparseCoreParams E) P N j) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧
      heap ≤ base ∧ base ≤ limit ∧ out.regs 83 = base ∧
      (∀ r, 57 < r → r < 95 → r ≠ 77 → r ≠ 83 → out.regs r = st.regs r) ∧
      base + last + 1 + limbs ≤ out.regs 99 ∧ out.regs 99 < 2 ^ w ∧ ZeroFrom out.mem (out.regs 99) ∧
      c ≤ 100 * exponent + 71 * limbs + (25 * limbs + 143) * last +
        Num.logarithmCost limbs precision (N + 2).size + 14 * (N + 2).size +
        71 * limbs + Num.logarithmCost limbs precision range + 14 * range + 521 := by
  dsimp only
  intro hlogSparse hendpoint hfitSparse haccSparse hcapSparse hroom
    hew hcommon hf hc hfirst hmul hsecondLo hsecondHi hbaseLo hbaseHi hprod hupper hbudget
  have hwordSparse : (SparseCore.coreNMax (P.M₀ ^ 2) + P.M₀ ^ 2 + 2) * 2 ^ precision < 2 ^ w :=
    (Nat.mul_le_mul_right _ (Nat.le_succ _)).trans_lt hendpoint
  have hscalePos : 0 < (2 : ℕ) ^ precision := by positivity
  have hinput : SparseCore.coreNMax (P.M₀ ^ 2) + P.M₀ ^ 2 + 2 < 2 ^ w :=
    (Nat.le_mul_of_pos_right _ hscalePos).trans_lt hwordSparse
  obtain ⟨mid, c₁, base, hr₁, hlo, hhi, hloPos, hhiPos, hord, hupp, _, hscale, h92, h77, _,
    hheapBase, hbase, hlimit, hkeep, hframe, hzero, hcost₁⟩ :=
    initSparseCoreLogForThresholds_runs (ω := ω) E P.M₀ hbits hload hpack hps hp hwidth
      hM hN hs hL hP hh hMw (by omega) hlinear hproduct hlogSparse hinput hwordSparse
      hfitSparse (by omega) hz hdiv haccSparse hcapSparse hprec hendpoint
  have hmono (k su lo hi : ℕ) (hle : lo ≤ hi) :
      11 * ((E.L + 1) * E.B_fn (P.M₀ ^ 2) * (2 * E.d_fn (P.M₀ ^ 2) + 190) *
        k * su * lo + 115 * (2 ^ precision) ^ 3) * (2 ^ precision) ^ (max (E.L + 1) 3 - 3) ≤
      11 * ((E.L + 1) * E.B_fn (P.M₀ ^ 2) * (2 * E.d_fn (P.M₀ ^ 2) + 190) *
        k * su * hi + 115 * (2 ^ precision) ^ 3) * (2 ^ precision) ^ (max (E.L + 1) 3 - 3) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
      (Nat.add_le_add_right (Nat.mul_le_mul_left _ hle) _))
  have hloLe := hmono kl sl _ _ (hord.trans hupp)
  have hhiLe := hmono ku su _ _ hupp
  have hloMax := max_le_max (le_refl (3 ^ E.L * (2 ^ precision) ^
    (max (E.L + 1) 3 - (E.L + 1)) * sl ^ (E.L + 1))) hloLe
  have hhiMax := max_le_max (le_refl (3 ^ E.L * (2 ^ precision) ^
    (max (E.L + 1) 3 - (E.L + 1)) * su ^ (E.L + 1))) hhiLe
  obtain ⟨out, c₂, hr₂, hres, hframe₂, h83, hregs, hheapLo, hheapHi, hzero₂, hcost₂⟩ :=
    reserveAndAssembleInitThresholdTable_runs (ω := ω) E P himpl
      ((hkeep 22 (by decide) (by decide)).trans hM)
      ((hkeep 1 (by decide) (by decide)).trans hk) hscale
      ((hkeep 44 (by decide) (by decide)).trans hd)
      ((hkeep 47 (by decide) (by decide)).trans hb)
      ((hkeep 48 (by decide) (by decide)).trans hg)
      ((hkeep 49 (by decide) (by decide)).trans hkl)
      ((hkeep 51 (by decide) (by decide)).trans hku)
      ((hkeep 50 (by decide) (by decide)).trans hsl)
      ((hkeep 52 (by decide) (by decide)).trans hsu)
      rfl rfl hscalePos hbPos hslPos (hscalePos.trans_le hloPos)
      (hscalePos.trans_le hhiPos) horder hklBound hkuBound hslBound hsuBound hlo hhi
      ((Nat.le_mul_of_pos_left _ (by omega)).trans_lt hwordSparse) huw hw
      hpack hbits hload hlog h92 ((hkeep 67 (by decide) (by decide)).trans hL)
      ((hkeep 68 (by decide) (by decide)).trans hP) hwLog hword hfit (by omega) hzero
      hdiv hacc hcap hprec hwidth rfl h77 ((hkeep 76 (by decide) (by decide)).trans hBranch)
      ((hkeep 75 (by decide) (by decide)).trans hLast)
      hew hcommon hf hc hfirst (hloLe.trans_lt hsecondLo) (hhiLe.trans_lt hsecondHi)
      ((Nat.mul_le_mul_left _ hloMax).trans_lt hbaseLo)
      ((Nat.mul_le_mul_left _ hhiMax).trans_lt hbaseHi) hmul
      (fun j hj => ⟨(Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hloMax _)).trans_lt (hprod j hj).1,
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hhiMax _)).trans_lt (hprod j hj).2.1,
        (hprod j hj).2.2⟩) hupper hbudget
  refine ⟨out, c₁ + c₂ + 1, base, runs_seq_iff.mpr (Or.inr ⟨mid, c₁, c₂, hr₁, hr₂, rfl⟩),
    hres, ?_, hheapBase, hlimit, h83, ?_, hheapLo, hheapHi, hzero₂, by omega⟩
  · intro a ha
    exact (hframe₂ a (by omega)).trans (hframe a ha)
  · intro r hlo hi h77 h83
    apply (hregs r (by omega) hi h83).trans (hkeep r hi _)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    omega

/-- Form the Section 8 sparsifier coefficient interval from the
runtime endpoints stored for the logarithm of two. -/
@[expose] def initSparsifierCoefficient (coefficient : ℕ := 36) : Stmt :=
  .assign 37 (.bin .mul (.bin .mul (.const coefficient) (.reg 4)) (.reg 4)) ;;
  .assign 49 (.bin .add (.reg 4) (.bin .div (.reg 37) (.reg 29))) ;;
  .assign 51 (.bin .add (.reg 4) (.bin .div
    (.bin .add (.reg 37) (.bin .sub (.reg 28) (.const 1))) (.reg 28)))

/-- Floor and ceiling division give bounds on `1 + coefficient / log 2` at the
scale used by the sparse-core stretch calculation. -/
theorem initSparsifierCoefficient_runs {w scale logLo logHi : ℕ} {coefficient : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hs : st.regs 4 = scale) (h28 : st.regs 28 = logLo) (h29 : st.regs 29 = logHi)
    (hsPos : 0 < scale) (hloPos : 0 < logLo) (hord : logLo ≤ logHi)
    (hlo : (logLo : ℝ) / scale ≤ Real.log 2)
    (hhi : Real.log 2 ≤ (logHi : ℝ) / scale)
    (hw : coefficient < 2 ^ w) (hword : scale + coefficient * scale * scale + (logLo - 1) < 2 ^ w) :
    ∃ out, Runs w p ω (initSparsifierCoefficient coefficient) st .normal out 24 ∧
      (out.regs 49 : ℝ) / scale ≤ 1 + coefficient / Real.log 2 ∧
      1 + coefficient / Real.log 2 ≤ (out.regs 51 : ℝ) / scale ∧
      out.regs 49 = scale + coefficient * scale * scale / logHi ∧
      out.regs 51 = scale + (coefficient * scale * scale + (logLo - 1)) / logLo ∧
      out.mem = st.mem ∧ (∀ r, r ≠ 37 → r ≠ 49 → r ≠ 51 → out.regs r = st.regs r) := by
  let n := coefficient * scale * scale
  let lo := scale + n / logHi
  let hi := scale + (n + (logLo - 1)) / logLo
  have htotal : scale + n + (logLo - 1) < 2 ^ w := hword
  have hn : n < 2 ^ w := by omega
  have hfirst : coefficient * scale < 2 ^ w := (Nat.le_mul_of_pos_right _ hsPos).trans_lt hn
  have hqlo : n / logHi ≤ n := Nat.div_le_self ..
  have hqhi : (n + (logLo - 1)) / logLo ≤ n + (logLo - 1) := Nat.div_le_self ..
  let s₁ := {st with regs := Function.update st.regs 37 n}
  let s₂ := {s₁ with regs := Function.update s₁.regs 49 lo}
  let out := {s₂ with regs := Function.update s₂.regs 51 hi}
  have hr₁ : Runs w p ω (.assign 37 (.bin .mul (.bin .mul (.const coefficient) (.reg 4)) (.reg 4)))
      st .normal s₁ 6 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hs, hw, hfirst,
      show coefficient * scale * scale < 2 ^ w from hn, n], rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign 49 (.bin .add (.reg 4) (.bin .div (.reg 37) (.reg 29))))
      s₁ .normal s₂ 6 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, s₁, hs, h29, lo,
      show n / logHi < 2 ^ w by omega, show scale + n / logHi < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have hr₃ : Runs w p ω (.assign 51 (.bin .add (.reg 4) (.bin .div
      (.bin .add (.reg 37) (.bin .sub (.reg 28) (.const 1))) (.reg 28))))
      s₂ .normal out 10 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, s₂, s₁, hs, h28, hi,
      show 1 < 2 ^ w by omega, show logLo - 1 < 2 ^ w by omega,
      show n + (logLo - 1) < 2 ^ w by omega,
      show (n + (logLo - 1)) / logLo < 2 ^ w by omega,
      show scale + (n + (logLo - 1)) / logLo < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hnat : n ≤ ((n + (logLo - 1)) / logLo) * logLo := by
    have hmod := Nat.mod_lt (n + (logLo - 1)) hloPos
    have hsum := Nat.mod_add_div (n + (logLo - 1)) logLo
    rw [Nat.mul_comm logLo] at hsum
    omega
  have hsReal : (0 : ℝ) < scale := by exact_mod_cast hsPos
  have hlReal : (0 : ℝ) < logLo := by exact_mod_cast hloPos
  have huReal : (0 : ℝ) < logHi := by exact_mod_cast hloPos.trans_le hord
  have hrep (x d : ℕ) (hp : 0 < (d : ℝ)) :
      ((x : ℝ) / scale ≤ ((coefficient * scale : ℕ) : ℝ) / d) ↔ x * d ≤ n := by
    rw [div_le_div_iff₀ hsReal hp]
    norm_cast
  have hl := (hrep (n / logHi) logHi huReal).mpr (Nat.div_mul_le_self ..)
  have hu : ((coefficient * scale : ℕ) : ℝ) / logLo ≤ ((n + (logLo - 1)) / logLo : ℕ) / (scale : ℝ) := by
    apply (div_le_div_iff₀ hlReal hsReal).mpr
    exact_mod_cast hnat
  obtain ⟨hbl, hbu⟩ := initSparsifierCoefficient_bounds coefficient hsReal hloPos hlo hhi
  refine ⟨out, ?_, ?_, ?_, by simp [out, s₂, lo, n], by simp [out, hi, n], rfl, ?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨s₁, 6, 17, hr₁,
      runs_seq_iff.mpr (Or.inr ⟨s₂, 6, 10, hr₂, hr₃, rfl⟩), rfl⟩)
  · simp [out, s₂, lo, Nat.cast_add, add_div, hsReal.ne']
    exact (add_le_add_iff_left (1 : ℝ)).mp ((add_le_add_right hl 1).trans hbl)
  · simp [out, hi, Nat.cast_add, add_div, hsReal.ne']
    exact (add_le_add_iff_left (1 : ℝ)).mp (hbu.trans (add_le_add_right hu 1))
  · intro r h37 h49 h51
    simp [out, s₂, s₁, h37, h49, h51]

end MinCostFlow.MinRatio
