module

public import MinCostFlow.MinRatio.InitSparsifierFallback

/-!
# Runtime path bounds from the cited parameters

Compute the cited exponent using the graph's edge bound and reuse the
cached log-two interval before evaluating the two terms of the path bound.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM

/-- Evaluate the path interval starting from the cached log of two. -/
@[expose] def initSparsifierCitedPath (bits load log pack exp shiftEntry Kγ c lower upper : ℕ) : Stmt :=
  prepareInitSparsifierPathLog Kγ ;;
  computeInitSparsifierPath bits load log pack exp shiftEntry c lower upper

/-- The computed path bounds use the runtime graph size and working
precision, with both phases' costs included. -/
theorem initSparsifierCitedPath_runs
    {w h Kγ c M precision limbs heap bits load log pack lo hi lower upper exp shiftEntry accuracy kLo kHi logLo logHi : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {phi K : ℝ}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hlog : MeetsContract w p log (Num.logarithmContract w h (precision - (2 * M + 2).size - 10)))
    (hexp : MeetsContract w p exp (Num.positiveExponentialContract w h accuracy))
    (hshift : MeetsContract w p shiftEntry (Num.shiftRightContract w h))
    (hM : st.regs 23 = M)
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision) (hh : st.regs 98 = heap)
    (hK : Kγ < 2 ^ w) (htriple : 3 * M < 2 ^ w)
    (hcube : (Nat.log 2 (3 * M) + 2) ^ 4 < 2 ^ w)
    (hexpWord : Expander.PathDSProg.csGammaExp Kγ (3 * M) < 2 ^ w) (hw₄ : 4 < 2 ^ w)
    (h53 : st.regs 53 = lo) (h54 : st.regs 54 = hi)
    (hwide : precision + precision < w)
    (hsfit : 2 * 2 ^ (precision + precision) < Num.capacity h limbs)
    (h39 : st.regs 39 = kLo) (h40 : st.regs 40 = kHi) (h38 : st.regs 38 = Expander.qOf M)
    (h28 : st.regs 28 = logLo) (h29 : st.regs 29 = logHi) (horder : logLo ≤ logHi)
    (hlogFit : Expander.PathDSProg.csGammaExp Kγ (3 * M) * logHi < 2 ^ w)
    (hkLo : (kLo : ℝ) / (2 ^ precision : ℕ) ≤ max K 1)
    (hkHi : max K 1 ≤ (kHi : ℝ) / (2 ^ precision : ℕ))
    (hlLo : (logLo : ℝ) / (2 ^ precision : ℕ) ≤ Real.log 2)
    (hlHi : Real.log 2 ≤ (logHi : ℝ) / (2 ^ precision : ℕ))
    (hkl : kLo * Expander.qOf M < 2 ^ w) (hkh : kHi * Expander.qOf M < 2 ^ w)
    (h49 : lower ≠ 49) (h44 : lower ≠ 44) (hdu : lower ≠ upper)
    (hl4 : lower ≠ 4) (hu4 : upper ≠ 4)
    (hl68 : lower ≠ 68) (hu68 : upper ≠ 68)
    (hl99 : lower ≠ 99) (hu99 : upper ≠ 99)
    (hc : 0 < c) (hl : 0 < lo)
    (hw : 2 * M + 2 < 2 ^ w) (hword : (2 * M + 2) * 2 ^ precision < 2 ^ w)
    (hfit : 2 * ((2 * M + 2) * 2 ^ precision) < Num.capacity h limbs)
    (hz : ZeroFrom st.mem heap) (hdiv : h ∣ precision)
    (hacc : (2 * M + 2).size + 11 ≤ precision)
    (hcap : precision + (2 * M + 2).size + 4 ≤ h * limbs)
    (hprecExp : 2 * (precision + precision) + 9 < 2 ^ w) (hwidth : precision < w) :
    let exponent := Expander.PathDSProg.csGammaExp Kγ (3 * M)
    let expLo := kLo * Expander.qOf M * (exponent * logLo)
    let expHi := kHi * Expander.qOf M * (exponent * logHi)
    expHi + 1 < 2 ^ w →
    max expLo expHi < 2 ^ w →
    2 * max expLo expHi < Num.capacity h limbs →
    let range := expHi / 2 ^ (precision + precision) + 1
    accuracy + range + 10 ≤ precision + precision →
    precision + precision + 2 * range + 4 ≤ h * limbs →
    precision + 2 * range ≤ accuracy →
    2 ^ (precision + 2 * range) + 2 < 2 ^ w →
    let space := limbs + limbs + Num.positiveExponentialSpace limbs (precision + precision) range +
      (2 * limbs + 1)
    let afterPower := heap + space + space
    afterPower + limbs + limbs + Num.logarithmSpace limbs precision (2 * M + 2).size < 2 ^ w →
    let scale := (2 : ℕ) ^ precision
    let cited := max 2 (c * Cited.csGamma Kγ (3 * M)) * scale
    let recLo := scale * scale / hi
    let recHi := (scale * scale + (lo - 1)) / lo
    let logCap := (2 * M + 2) * scale
    (lo : ℝ) / scale ≤ phi → phi ≤ (hi : ℝ) / scale →
    scale * scale + (lo - 1) < 2 ^ w →
    max (max recLo recHi) cited < 2 ^ w →
    25 * (logCap + scale) < 2 ^ w →
    25 * (logCap + scale) * max recLo cited < 2 ^ w →
    25 * (logCap + scale) * max recHi cited + (scale - 1) < 2 ^ w →
    ∃ out cost ret, Runs w p ω (initSparsifierCitedPath bits load log pack exp shiftEntry Kγ c lower upper) st .normal out cost ∧
      (out.regs lower : ℝ) / scale ≤ Expander.csGammaExpPath Kγ c K phi M ∧
      Expander.csGammaExpPath Kγ c K phi M ≤ (out.regs upper : ℝ) / scale ∧
      out.regs upper ≤ max (2 ^ (precision + 2 * range) + 2) ((25 * (logCap + scale) * max recHi cited + (scale - 1)) / scale) ∧
      (∀ logBound invBound conductanceErr exponentErr,
        2 * M + 3 ≤ logBound → max recHi cited ≤ invBound * scale →
        scale ≤ invBound * lo → hi - lo ≤ conductanceErr → expHi - expLo ≤ exponentErr * scale →
        out.regs upper - out.regs lower ≤
          max (2 ^ (2 * range) * exponentErr + 4)
            (25 * ((4 * 2 ^ ((2 * M + 2).size + 10)) * invBound +
              logBound * (invBound ^ 2 * conductanceErr + 2)) + 2)) ∧
      out.regs 4 = scale ∧ out.regs 68 = precision ∧ out.regs 99 = ret ∧ heap ≤ ret ∧
      ret ≤ afterPower + limbs + limbs + Num.logarithmSpace limbs precision (2 * M + 2).size ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem ret ∧
      (∀ r < 95, r ≠ lower → r ≠ upper → r ∉ ([2, 3, 4, 24, 31, 32, 33, 34, 35, 36, 37, 43, 44, 45, 46, 47, 48, 49, 68, 92, 94] : List ℕ) →
        out.regs r = st.regs r) ∧
      cost ≤ 345 * limbs + 2 * Num.positiveExponentialCost limbs (precision + precision) range + Num.logarithmCost limbs precision (2 * M + 2).size +
        14 * (2 * M + 2).size + 35 * (Nat.log 2 (3 * M) + 1) + 675 := by
  intro exponent expLo expHi hup hwExp hfitExp range haccExp hcapExp hq hwordExp space afterPower hroom
    scale cited recLo recHi logCap hlo hhi hrec hmax hm hfLo hfHi
  obtain ⟨mid, cost₁, hr₁, ll, lu, h34, h35, h37, h33, hmem, hk₁, hc₁⟩ :=
    prepareInitSparsifierPathLog_runs (ω := ω) hM hK htriple hcube hexpWord hw₄
      h28 h29 horder hlLo hlHi hlogFit hP hwide
  obtain ⟨out, cost₂, ret, hr₂, lb, ub, hwordOut, hgap, hscaleOut, hprecOut, hret, hbase, htop, hf, hz', hk₂, hc₂⟩ :=
    computeInitSparsifierPath_runs (ω := ω) hbits hload hpack hlog hexp hshift
      ((hk₁ 23 (by decide)).trans hM) ((hk₁ 67 (by decide)).trans hL)
      ((hk₁ 68 (by decide)).trans hP) ((hk₁ 98 (by decide)).trans hh)
      h37 ((hk₁ 53 (by decide)).trans h53) ((hk₁ 54 (by decide)).trans h54)
      h33 (Nat.pow_lt_pow_right (by decide) hwide) hsfit
      ((hk₁ 39 (by decide)).trans h39) ((hk₁ 40 (by decide)).trans h40)
      ((hk₁ 38 (by decide)).trans h38) h34 h35 hkLo hkHi (h34 ▸ ll) (h35 ▸ lu) hkl hkh
      h49 h44 hdu hl4 hu4 hl68 hu68 hl99 hu99 hc hl hw hword hfit (hmem.symm ▸ hz) hdiv hacc hcap hprecExp hwidth
      hup hwExp hfitExp haccExp hcapExp hq hwordExp hroom hlo hhi hrec hmax hm hfLo hfHi
  change cost₂ ≤ 345 * limbs + 2 * Num.positiveExponentialCost limbs (precision + precision) range +
    Num.logarithmCost limbs precision (2 * M + 2).size + 14 * (2 * M + 2).size + 592 at hc₂
  refine ⟨out, cost₁ + cost₂ + 1, ret, runs_seq_iff.mpr (Or.inr ⟨mid, cost₁, cost₂, hr₁, hr₂, rfl⟩),
    lb, ub, hwordOut, hgap, hscaleOut, hprecOut, hret, hbase, htop, fun a ha => (hf a ha).trans (congrFun hmem a), hz', ?_, by omega⟩
  intro r hr hlow hupp hkeep
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hkeep
  obtain ⟨h2, h3, h4, h24, h31, h32, h33, h34, h35, h36, h37, h43, h44, h45, h46, h47, h48, h49, h68, h92, h94⟩ := hkeep
  exact (hk₂ r hr hlow hupp (by simp [h2, h3, h4, h31, h32, h33, h34, h35, h36, h37, h43, h44,
    h45, h46, h47, h48, h49, h68, h92, h94])).trans
    (hk₁ r (by simp [h24, h31, h32, h33, h34, h35, h36, h37]))

/-- Read the exponent multiplier for the current edge cap and evaluate
the cited path interval. -/
@[expose] def computeInitSparsifierCitedPath (qEntry bits load log pack exp shiftEntry Kγ c lower upper : ℕ) : Stmt :=
  initSparsifierPathQ qEntry ;;
  initSparsifierCitedPath bits load log pack exp shiftEntry Kγ c lower upper

/-- The graph-dependent multiplier is computed at runtime and its call
cost is included in the path enclosure. -/
theorem computeInitSparsifierCitedPath_runs
    {w h Kγ c M precision limbs heap bits load log pack qEntry lo hi lower upper exp shiftEntry accuracy kLo kHi logLo logHi : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {phi K : ℝ}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hlog : MeetsContract w p log (Num.logarithmContract w h (precision - (2 * M + 2).size - 10)))
    (hexp : MeetsContract w p exp (Num.positiveExponentialContract w h accuracy))
    (hshift : MeetsContract w p shiftEntry (Num.shiftRightContract w h))
    (hqImpl : MeetsContract w p qEntry (initSparsifierPathQContract w))
    (hq8 : (Expander.PathDSProg.qRoot M + 1) ^ 8 < 2 ^ w)
    (hq2 : Expander.PathDSProg.qRoot M + 2 < 2 ^ w)
    (hM : st.regs 23 = M)
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision) (hh : st.regs 98 = heap)
    (hK : Kγ < 2 ^ w) (htriple : 3 * M < 2 ^ w)
    (hcube : (Nat.log 2 (3 * M) + 2) ^ 4 < 2 ^ w)
    (hexpWord : Expander.PathDSProg.csGammaExp Kγ (3 * M) < 2 ^ w) (hw₄ : 4 < 2 ^ w)
    (h53 : st.regs 53 = lo) (h54 : st.regs 54 = hi)
    (hwide : precision + precision < w)
    (hsfit : 2 * 2 ^ (precision + precision) < Num.capacity h limbs)
    (h39 : st.regs 39 = kLo) (h40 : st.regs 40 = kHi)
    (h28 : st.regs 28 = logLo) (h29 : st.regs 29 = logHi) (horder : logLo ≤ logHi)
    (hlogFit : Expander.PathDSProg.csGammaExp Kγ (3 * M) * logHi < 2 ^ w)
    (hkLo : (kLo : ℝ) / (2 ^ precision : ℕ) ≤ max K 1)
    (hkHi : max K 1 ≤ (kHi : ℝ) / (2 ^ precision : ℕ))
    (hlLo : (logLo : ℝ) / (2 ^ precision : ℕ) ≤ Real.log 2)
    (hlHi : Real.log 2 ≤ (logHi : ℝ) / (2 ^ precision : ℕ))
    (hkl : kLo * Expander.qOf M < 2 ^ w) (hkh : kHi * Expander.qOf M < 2 ^ w)
    (h49 : lower ≠ 49) (h44 : lower ≠ 44) (hdu : lower ≠ upper)
    (hl4 : lower ≠ 4) (hu4 : upper ≠ 4)
    (hl68 : lower ≠ 68) (hu68 : upper ≠ 68)
    (hl99 : lower ≠ 99) (hu99 : upper ≠ 99)
    (hc : 0 < c) (hl : 0 < lo)
    (hw : 2 * M + 2 < 2 ^ w) (hword : (2 * M + 2) * 2 ^ precision < 2 ^ w)
    (hfit : 2 * ((2 * M + 2) * 2 ^ precision) < Num.capacity h limbs)
    (hz : ZeroFrom st.mem heap) (hdiv : h ∣ precision)
    (hacc : (2 * M + 2).size + 11 ≤ precision)
    (hcap : precision + (2 * M + 2).size + 4 ≤ h * limbs)
    (hprecExp : 2 * (precision + precision) + 9 < 2 ^ w) (hwidth : precision < w) :
    let exponent := Expander.PathDSProg.csGammaExp Kγ (3 * M)
    let expLo := kLo * Expander.qOf M * (exponent * logLo)
    let expHi := kHi * Expander.qOf M * (exponent * logHi)
    expHi + 1 < 2 ^ w →
    max expLo expHi < 2 ^ w →
    2 * max expLo expHi < Num.capacity h limbs →
    let range := expHi / 2 ^ (precision + precision) + 1
    accuracy + range + 10 ≤ precision + precision →
    precision + precision + 2 * range + 4 ≤ h * limbs →
    precision + 2 * range ≤ accuracy →
    2 ^ (precision + 2 * range) + 2 < 2 ^ w →
    let space := limbs + limbs + Num.positiveExponentialSpace limbs (precision + precision) range +
      (2 * limbs + 1)
    let afterPower := heap + space + space
    afterPower + limbs + limbs + Num.logarithmSpace limbs precision (2 * M + 2).size < 2 ^ w →
    let scale := (2 : ℕ) ^ precision
    let cited := max 2 (c * Cited.csGamma Kγ (3 * M)) * scale
    let recLo := scale * scale / hi
    let recHi := (scale * scale + (lo - 1)) / lo
    let logCap := (2 * M + 2) * scale
    (lo : ℝ) / scale ≤ phi → phi ≤ (hi : ℝ) / scale →
    scale * scale + (lo - 1) < 2 ^ w →
    max (max recLo recHi) cited < 2 ^ w →
    25 * (logCap + scale) < 2 ^ w →
    25 * (logCap + scale) * max recLo cited < 2 ^ w →
    25 * (logCap + scale) * max recHi cited + (scale - 1) < 2 ^ w →
    ∃ out cost ret, Runs w p ω (computeInitSparsifierCitedPath qEntry bits load log pack exp shiftEntry Kγ c lower upper) st .normal out cost ∧
      (out.regs lower : ℝ) / scale ≤ Expander.csGammaExpPath Kγ c K phi M ∧
      Expander.csGammaExpPath Kγ c K phi M ≤ (out.regs upper : ℝ) / scale ∧
      out.regs upper ≤ max (2 ^ (precision + 2 * range) + 2) ((25 * (logCap + scale) * max recHi cited + (scale - 1)) / scale) ∧
      (∀ logBound invBound conductanceErr exponentErr,
        2 * M + 3 ≤ logBound → max recHi cited ≤ invBound * scale →
        scale ≤ invBound * lo → hi - lo ≤ conductanceErr → expHi - expLo ≤ exponentErr * scale →
        out.regs upper - out.regs lower ≤
          max (2 ^ (2 * range) * exponentErr + 4)
            (25 * ((4 * 2 ^ ((2 * M + 2).size + 10)) * invBound +
              logBound * (invBound ^ 2 * conductanceErr + 2)) + 2)) ∧
      out.regs 4 = scale ∧ out.regs 68 = precision ∧ out.regs 99 = ret ∧ heap ≤ ret ∧
      ret ≤ afterPower + limbs + limbs + Num.logarithmSpace limbs precision (2 * M + 2).size ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem ret ∧
      (∀ r < 95, r ≠ lower → r ≠ upper → r ∉ ([2, 3, 4, 24, 31, 32, 33, 34, 35, 36, 37, 38, 43, 44, 45, 46, 47, 48, 49, 68, 92, 94] : List ℕ) →
        out.regs r = st.regs r) ∧
      cost ≤ 345 * limbs + 2 * Num.positiveExponentialCost limbs (precision + precision) range + Num.logarithmCost limbs precision (2 * M + 2).size +
        14 * (2 * M + 2).size + 35 * (Nat.log 2 (3 * M) + 1) + 65 * (Nat.log 2 (M + 2) + 1) + 764 := by
  intro exponent expLo expHi hup hwExp hfitExp range haccExp hcapExp hq hwordExp space afterPower hroom
    scale cited recLo recHi logCap hlo hhi hrec hmax hm hfLo hfHi
  obtain ⟨mid, cost₁, hr₁, h38, hmem, hk₁, hc₁⟩ :=
    initSparsifierPathQ_runs (ω := ω) hqImpl hM (by omega) hq8 hq2 (by omega)
  obtain ⟨out, cost₂, ret, hr₂, lb, ub, hwordOut, hgap, hscaleOut, hprecOut, hret, hbase, htop, hf, hz', hk₂, hc₂⟩ :=
    initSparsifierCitedPath_runs (ω := ω) hbits hload hpack hlog hexp hshift
      ((hk₁ 23 (by decide)).trans hM) ((hk₁ 67 (by decide)).trans hL)
      ((hk₁ 68 (by decide)).trans hP) ((hk₁ 98 (by decide)).trans hh)
      hK htriple hcube hexpWord hw₄ ((hk₁ 53 (by decide)).trans h53) ((hk₁ 54 (by decide)).trans h54)
      hwide hsfit ((hk₁ 39 (by decide)).trans h39) ((hk₁ 40 (by decide)).trans h40) h38
      ((hk₁ 28 (by decide)).trans h28) ((hk₁ 29 (by decide)).trans h29) horder hlogFit
      hkLo hkHi hlLo hlHi hkl hkh h49 h44 hdu hl4 hu4 hl68 hu68 hl99 hu99 hc hl hw hword hfit (hmem.symm ▸ hz)
      hdiv hacc hcap hprecExp hwidth hup hwExp hfitExp haccExp hcapExp hq hwordExp hroom
      hlo hhi hrec hmax hm hfLo hfHi
  change cost₂ ≤ 345 * limbs + 2 * Num.positiveExponentialCost limbs (precision + precision) range +
    Num.logarithmCost limbs precision (2 * M + 2).size + 14 * (2 * M + 2).size +
      35 * (Nat.log 2 (3 * M) + 1) + 675 at hc₂
  refine ⟨out, cost₁ + cost₂ + 1, ret, runs_seq_iff.mpr (Or.inr ⟨mid, cost₁, cost₂, hr₁, hr₂, rfl⟩),
    lb, ub, hwordOut, hgap, hscaleOut, hprecOut, hret, hbase, htop, fun a ha => (hf a ha).trans (congrFun hmem a), hz', ?_, by omega⟩
  intro r hr hlow hupp hkeep
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hkeep
  obtain ⟨h2, h3, h4, h24, h31, h32, h33, h34, h35, h36, h37, h38', h43, h44, h45, h46, h47,
    h48, h49, h68, h92, h94⟩ := hkeep
  exact (hk₂ r hr hlow hupp (by simp [h2, h3, h4, h24, h31, h32, h33, h34, h35, h36, h37,
    h43, h44, h45, h46, h47, h48, h49, h68, h92, h94])).trans (hk₁ r h38')

/-- Set up the witness-expander path call. Registers 56 and 57 hold
its input conductance bounds and register 58 holds its edge cap. -/
@[expose] def prepareInitSparsifierWitnessPath : Stmt :=
  .assign 23 (.reg 58) ;;
  .assign 53 (.reg 56) ;;
  .assign 54 (.reg 57) ;;
  .assign 98 (.reg 99)

/-- The second call uses the heap returned by the first call and
preserves both of its saved path endpoints. -/
theorem prepareInitSparsifierWitnessPath_runs {w : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} :
    ∃ out, Runs w p ω prepareInitSparsifierWitnessPath st .normal out 11 ∧
      out.regs 23 = st.regs 58 ∧ out.regs 53 = st.regs 56 ∧
      out.regs 54 = st.regs 57 ∧ out.regs 98 = st.regs 99 ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 23 → r ≠ 53 → r ≠ 54 → r ≠ 98 → out.regs r = st.regs r) := by
  let a := {st with regs := Function.update st.regs 23 (st.regs 58)}
  let b := {a with regs := Function.update a.regs 53 (st.regs 56)}
  let c := {b with regs := Function.update b.regs 54 (st.regs 57)}
  let out := {c with regs := Function.update c.regs 98 (st.regs 99)}
  have hr₁ : Runs w p ω (.assign 23 (.reg 58)) st .normal a 2 :=
    runs_assign_iff.mpr ⟨_, rfl, rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign 53 (.reg 56)) a .normal b 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, a], rfl, rfl, rfl⟩
  have hr₃ : Runs w p ω (.assign 54 (.reg 57)) b .normal c 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, a, b], rfl, rfl, rfl⟩
  have hr₄ : Runs w p ω (.assign 98 (.reg 99)) c .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, a, b, c], rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨a, 2, 8, hr₁,
    runs_seq_iff.mpr (Or.inr ⟨b, 2, 5, hr₂,
      runs_seq_iff.mpr (Or.inr ⟨c, 2, 2, hr₃, hr₄, rfl⟩), rfl⟩), rfl⟩),
    by simp [out, c, b, a], by simp [out, c, b], by simp [out, c], by simp [out], rfl,
    fun r h23 h53 h54 h98 => by simp [out, c, b, a, h23, h53, h54, h98]⟩

/-- Use the saved witness-expander parameters and the preceding call's heap
to compute the second path interval. -/
@[expose] def computeInitSparsifierWitnessPath
    (qEntry bits load log pack exp shiftEntry Kγ c lower upper : ℕ) : Stmt :=
  prepareInitSparsifierWitnessPath ;;
  computeInitSparsifierCitedPath qEntry bits load log pack exp shiftEntry Kγ c lower upper

/-- The witness call reads its edge cap and conductance from saved words. -/
theorem computeInitSparsifierWitnessPath_runs
    {w h Kγ c M precision limbs heap bits load log pack qEntry lo hi lower upper exp shiftEntry accuracy kLo kHi logLo logHi : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {phi K : ℝ}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hlog : MeetsContract w p log (Num.logarithmContract w h (precision - (2 * M + 2).size - 10)))
    (hexp : MeetsContract w p exp (Num.positiveExponentialContract w h accuracy))
    (hshift : MeetsContract w p shiftEntry (Num.shiftRightContract w h))
    (hqImpl : MeetsContract w p qEntry (initSparsifierPathQContract w))
    (hq8 : (Expander.PathDSProg.qRoot M + 1) ^ 8 < 2 ^ w)
    (hq2 : Expander.PathDSProg.qRoot M + 2 < 2 ^ w)
    (hM : st.regs 58 = M)
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision) (hh : st.regs 99 = heap)
    (hK : Kγ < 2 ^ w) (htriple : 3 * M < 2 ^ w)
    (hcube : (Nat.log 2 (3 * M) + 2) ^ 4 < 2 ^ w)
    (hexpWord : Expander.PathDSProg.csGammaExp Kγ (3 * M) < 2 ^ w) (hw₄ : 4 < 2 ^ w)
    (h56 : st.regs 56 = lo) (h57 : st.regs 57 = hi)
    (hwide : precision + precision < w)
    (hsfit : 2 * 2 ^ (precision + precision) < Num.capacity h limbs)
    (h39 : st.regs 39 = kLo) (h40 : st.regs 40 = kHi)
    (h28 : st.regs 28 = logLo) (h29 : st.regs 29 = logHi) (horder : logLo ≤ logHi)
    (hlogFit : Expander.PathDSProg.csGammaExp Kγ (3 * M) * logHi < 2 ^ w)
    (hkLo : (kLo : ℝ) / (2 ^ precision : ℕ) ≤ max K 1)
    (hkHi : max K 1 ≤ (kHi : ℝ) / (2 ^ precision : ℕ))
    (hlLo : (logLo : ℝ) / (2 ^ precision : ℕ) ≤ Real.log 2)
    (hlHi : Real.log 2 ≤ (logHi : ℝ) / (2 ^ precision : ℕ))
    (hkl : kLo * Expander.qOf M < 2 ^ w) (hkh : kHi * Expander.qOf M < 2 ^ w)
    (h49 : lower ≠ 49) (h44 : lower ≠ 44) (hdu : lower ≠ upper)
    (hl4 : lower ≠ 4) (hu4 : upper ≠ 4)
    (hl68 : lower ≠ 68) (hu68 : upper ≠ 68)
    (hl99 : lower ≠ 99) (hu99 : upper ≠ 99)
    (hc : 0 < c) (hl : 0 < lo)
    (hw : 2 * M + 2 < 2 ^ w) (hword : (2 * M + 2) * 2 ^ precision < 2 ^ w)
    (hfit : 2 * ((2 * M + 2) * 2 ^ precision) < Num.capacity h limbs)
    (hz : ZeroFrom st.mem heap) (hdiv : h ∣ precision)
    (hacc : (2 * M + 2).size + 11 ≤ precision)
    (hcap : precision + (2 * M + 2).size + 4 ≤ h * limbs)
    (hprecExp : 2 * (precision + precision) + 9 < 2 ^ w) (hwidth : precision < w) :
    let exponent := Expander.PathDSProg.csGammaExp Kγ (3 * M)
    let expLo := kLo * Expander.qOf M * (exponent * logLo)
    let expHi := kHi * Expander.qOf M * (exponent * logHi)
    expHi + 1 < 2 ^ w →
    max expLo expHi < 2 ^ w →
    2 * max expLo expHi < Num.capacity h limbs →
    let range := expHi / 2 ^ (precision + precision) + 1
    accuracy + range + 10 ≤ precision + precision →
    precision + precision + 2 * range + 4 ≤ h * limbs →
    precision + 2 * range ≤ accuracy →
    2 ^ (precision + 2 * range) + 2 < 2 ^ w →
    let space := limbs + limbs + Num.positiveExponentialSpace limbs (precision + precision) range +
      (2 * limbs + 1)
    let afterPower := heap + space + space
    afterPower + limbs + limbs + Num.logarithmSpace limbs precision (2 * M + 2).size < 2 ^ w →
    let scale := (2 : ℕ) ^ precision
    let cited := max 2 (c * Cited.csGamma Kγ (3 * M)) * scale
    let recLo := scale * scale / hi
    let recHi := (scale * scale + (lo - 1)) / lo
    let logCap := (2 * M + 2) * scale
    (lo : ℝ) / scale ≤ phi → phi ≤ (hi : ℝ) / scale →
    scale * scale + (lo - 1) < 2 ^ w →
    max (max recLo recHi) cited < 2 ^ w →
    25 * (logCap + scale) < 2 ^ w →
    25 * (logCap + scale) * max recLo cited < 2 ^ w →
    25 * (logCap + scale) * max recHi cited + (scale - 1) < 2 ^ w →
    ∃ out cost ret, Runs w p ω (computeInitSparsifierWitnessPath qEntry bits load log pack exp shiftEntry Kγ c lower upper) st .normal out cost ∧
      (out.regs lower : ℝ) / scale ≤ Expander.csGammaExpPath Kγ c K phi M ∧
      Expander.csGammaExpPath Kγ c K phi M ≤ (out.regs upper : ℝ) / scale ∧
      out.regs upper ≤ max (2 ^ (precision + 2 * range) + 2) ((25 * (logCap + scale) * max recHi cited + (scale - 1)) / scale) ∧
      (∀ logBound invBound conductanceErr exponentErr,
        2 * M + 3 ≤ logBound → max recHi cited ≤ invBound * scale →
        scale ≤ invBound * lo → hi - lo ≤ conductanceErr → expHi - expLo ≤ exponentErr * scale →
        out.regs upper - out.regs lower ≤
          max (2 ^ (2 * range) * exponentErr + 4)
            (25 * ((4 * 2 ^ ((2 * M + 2).size + 10)) * invBound +
              logBound * (invBound ^ 2 * conductanceErr + 2)) + 2)) ∧
      out.regs 4 = scale ∧ out.regs 68 = precision ∧ out.regs 99 = ret ∧ heap ≤ ret ∧
      ret ≤ afterPower + limbs + limbs + Num.logarithmSpace limbs precision (2 * M + 2).size ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem ret ∧
      (∀ r < 95, r ≠ lower → r ≠ upper → r ∉ ([2, 3, 4, 23, 24, 31, 32, 33, 34, 35, 36, 37, 38, 43, 44, 45, 46, 47, 48, 49, 53, 54, 68, 92, 94] : List ℕ) →
        out.regs r = st.regs r) ∧
      cost ≤ 345 * limbs + 2 * Num.positiveExponentialCost limbs (precision + precision) range + Num.logarithmCost limbs precision (2 * M + 2).size +
        14 * (2 * M + 2).size + 35 * (Nat.log 2 (3 * M) + 1) + 65 * (Nat.log 2 (M + 2) + 1) + 776 := by
  intro exponent expLo expHi hup hwExp hfitExp range haccExp hcapExp hq hwordExp space afterPower hroom
    scale cited recLo recHi logCap hlo hhi hrec hmax hm hfLo hfHi
  obtain ⟨mid, hr₁, h23, h53, h54, h98, hmem, hk₁⟩ :=
    prepareInitSparsifierWitnessPath_runs (w := w) (p := p) (ω := ω) (st := st)
  obtain ⟨out, cost, ret, hr₂, lb, ub, hwOut, hgap, hsOut, hpOut, hret, hbase, htop, hf, hz', hk₂, hcost⟩ :=
    computeInitSparsifierCitedPath_runs (ω := ω) hbits hload hpack hlog hexp hshift
      hqImpl hq8 hq2 (h23.trans hM)
      ((hk₁ 67 (by decide) (by decide) (by decide) (by decide)).trans hL)
      ((hk₁ 68 (by decide) (by decide) (by decide) (by decide)).trans hP)
      (h98.trans hh) hK htriple hcube hexpWord hw₄ (h53.trans h56) (h54.trans h57)
      hwide hsfit
      ((hk₁ 39 (by decide) (by decide) (by decide) (by decide)).trans h39)
      ((hk₁ 40 (by decide) (by decide) (by decide) (by decide)).trans h40)
      ((hk₁ 28 (by decide) (by decide) (by decide) (by decide)).trans h28)
      ((hk₁ 29 (by decide) (by decide) (by decide) (by decide)).trans h29)
      horder hlogFit hkLo hkHi hlLo hlHi hkl hkh h49 h44 hdu hl4 hu4 hl68 hu68 hl99 hu99
      hc hl hw hword hfit (hmem.symm ▸ hz) hdiv hacc hcap hprecExp hwidth
      hup hwExp hfitExp haccExp hcapExp hq hwordExp hroom hlo hhi hrec hmax hm hfLo hfHi
  change cost ≤ 345 * limbs + 2 * Num.positiveExponentialCost limbs (precision + precision) range +
    Num.logarithmCost limbs precision (2 * M + 2).size + 14 * (2 * M + 2).size +
      35 * (Nat.log 2 (3 * M) + 1) + 65 * (Nat.log 2 (M + 2) + 1) + 764 at hcost
  refine ⟨out, cost + 12, ret, runs_seq_iff.mpr (Or.inr ⟨mid, 11, cost, hr₁, hr₂, by omega⟩),
    lb, ub, hwOut, hgap, hsOut, hpOut, hret, hbase, htop, fun a ha => (hf a ha).trans (congrFun hmem a),
    hz', ?_, by omega⟩
  intro r hr hlow hupp hkeep
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hkeep
  obtain ⟨h2, h3, h4, h23', h24, h31, h32, h33, h34, h35, h36, h37, h38, h43, h44,
    h45, h46, h47, h48, h49', h53', h54', h68, h92, h94⟩ := hkeep
  exact (hk₂ r hr hlow hupp (by simp [h2, h3, h4, h24, h31, h32, h33, h34, h35, h36,
    h37, h38, h43, h44, h45, h46, h47, h48, h49', h68, h92, h94])).trans
    (hk₁ r h23' h53' h54' (by omega))

/-- Move the saved first path interval next to the second interval
before taking the squared maximum. -/
@[expose] def prepareInitSparsifierLengthFactor : Stmt :=
  .assign 39 (.reg 60) ;; .assign 41 (.reg 61)

/-- The two copies leave the second endpoints and working scale in place. -/
theorem prepareInitSparsifierLengthFactor_runs {w : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} :
    ∃ out, Runs w p ω prepareInitSparsifierLengthFactor st .normal out 5 ∧
      out.regs 39 = st.regs 60 ∧ out.regs 41 = st.regs 61 ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 39 → r ≠ 41 → out.regs r = st.regs r) := by
  let mid := {st with regs := Function.update st.regs 39 (st.regs 60)}
  let out := {mid with regs := Function.update mid.regs 41 (st.regs 61)}
  have hr₁ : Runs w p ω (.assign 39 (.reg 60)) st .normal mid 2 :=
    runs_assign_iff.mpr ⟨_, rfl, rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign 41 (.reg 61)) mid .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, mid], rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 2, 2, hr₁, hr₂, rfl⟩),
    by simp [out, mid], by simp [out], rfl, fun r h39 h41 => by simp [out, mid, h39, h41]⟩

/-- Compute the length-factor interval from the two collected path
intervals. -/
@[expose] def finishInitSparsifierLengthFactor : Stmt :=
  prepareInitSparsifierLengthFactor ;; initSparsifierLengthFactor

/-- Squaring and outward rounding enclose the sparsifier length factor.
The first path bounds are in registers 60 and 61. -/
theorem finishInitSparsifierLengthFactor_runs
    (cDeg phiConst phiMin : ℝ) (paths : Spanner.PathDSTool) (M : ℕ)
    {w scale lo₁ lo₂ hi₁ hi₂ : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hs : st.regs 4 = scale) (hsPos : 0 < scale)
    (h60 : st.regs 60 = lo₁) (h40 : st.regs 40 = lo₂)
    (h61 : st.regs 61 = hi₁) (h42 : st.regs 42 = hi₂)
    (hlo₁ : (lo₁ : ℝ) / scale ≤ paths.γ_ExpPath phiMin M)
    (hhi₁ : paths.γ_ExpPath phiMin M ≤ (hi₁ : ℝ) / scale)
    (hlo₂ : (lo₂ : ℝ) / scale ≤ paths.γ_ExpPath phiConst (Spanner.capM_W cDeg phiMin M))
    (hhi₂ : paths.γ_ExpPath phiConst (Spanner.capM_W cDeg phiMin M) ≤ (hi₂ : ℝ) / scale)
    (hw : 1 < 2 ^ w) (hl : (max lo₁ lo₂) ^ 2 < 2 ^ w)
    (hh : (max hi₁ hi₂) ^ 2 + (scale - 1) < 2 ^ w) :
    ∃ out, Runs w p ω finishInitSparsifierLengthFactor st .normal out 46 ∧
      (out.regs 50 : ℝ) / scale ≤ Spanner.capGammaL cDeg phiConst paths phiMin M ∧
      Spanner.capGammaL cDeg phiConst paths phiMin M ≤ (out.regs 52 : ℝ) / scale ∧
      (scale ≤ max lo₁ lo₂ → 0 < out.regs 50) ∧
      out.regs 50 ≤ out.regs 52 ∧ out.regs 52 < 2 ^ w ∧
      out.regs 50 = (max lo₁ lo₂) ^ 2 / scale ∧
      out.regs 52 = ((max hi₁ hi₂) ^ 2 + (scale - 1)) / scale ∧ out.mem = st.mem ∧
      (∀ r, r ∉ ([31, 32, 33, 39, 41, 50, 52] : List ℕ) → out.regs r = st.regs r) := by
  obtain ⟨mid, hr₁, h39, h41, hm₁, hk₁⟩ :=
    prepareInitSparsifierLengthFactor_runs (w := w) (p := p) (ω := ω) (st := st)
  obtain ⟨out, hr₂, lb, ub, hp, hle, hfit, hloWord, hhiWord, hm₂, hk₂⟩ :=
    initSparsifierLengthFactor_runs cDeg phiConst phiMin paths M (p := p) (ω := ω)
      ((hk₁ 4 (by decide) (by decide)).trans hs) hsPos (h39.trans h60)
      ((hk₁ 40 (by decide) (by decide)).trans h40) (h41.trans h61)
      ((hk₁ 42 (by decide) (by decide)).trans h42) hlo₁ hhi₁ hlo₂ hhi₂ hw hl hh
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 5, 40, hr₁, hr₂, rfl⟩),
    lb, ub, hp, hle, hfit, hloWord, hhiWord, hm₂.trans hm₁, ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h31, h32, h33, h39', h41', h50, h52⟩ := hr
  exact (hk₂ r h31 h32 h33 h50 h52).trans (hk₁ r h39' h41')

/-- The two path enclosures give a bound on the length factor and its
integer endpoint gap at the same working scale. -/
theorem finishInitSparsifierLengthFactor_withGap_runs
    (cDeg phiConst phiMin : ℝ) (paths : Spanner.PathDSTool) (M : ℕ)
    {w scale lo₁ lo₂ hi₁ hi₂ bound err : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hs : st.regs 4 = scale) (hsPos : 0 < scale)
    (h60 : st.regs 60 = lo₁) (h40 : st.regs 40 = lo₂)
    (h61 : st.regs 61 = hi₁) (h42 : st.regs 42 = hi₂)
    (hlo₁ : (lo₁ : ℝ) / scale ≤ paths.γ_ExpPath phiMin M)
    (hhi₁ : paths.γ_ExpPath phiMin M ≤ (hi₁ : ℝ) / scale)
    (hlo₂ : (lo₂ : ℝ) / scale ≤ paths.γ_ExpPath phiConst (Spanner.capM_W cDeg phiMin M))
    (hhi₂ : paths.γ_ExpPath phiConst (Spanner.capM_W cDeg phiMin M) ≤ (hi₂ : ℝ) / scale)
    (hpos : scale ≤ max lo₁ lo₂)
    (hbound₁ : hi₁ ≤ bound * scale) (hbound₂ : hi₂ ≤ bound * scale)
    (herr₁ : hi₁ - lo₁ ≤ err) (herr₂ : hi₂ - lo₂ ≤ err)
    (hw : 1 < 2 ^ w) (hroom : (bound * scale) ^ 2 + (scale - 1) < 2 ^ w) :
    ∃ out, Runs w p ω finishInitSparsifierLengthFactor st .normal out 46 ∧
      (out.regs 50 : ℝ) / scale ≤ Spanner.capGammaL cDeg phiConst paths phiMin M ∧
      Spanner.capGammaL cDeg phiConst paths phiMin M ≤ (out.regs 52 : ℝ) / scale ∧
      0 < out.regs 50 ∧ out.regs 50 ≤ out.regs 52 ∧
      out.regs 52 ≤ bound ^ 2 * scale ∧ out.regs 52 - out.regs 50 ≤ 2 * bound * err + 2 ∧
      out.mem = st.mem ∧
      (∀ r, r ∉ ([31, 32, 33, 39, 41, 50, 52] : List ℕ) → out.regs r = st.regs r) := by
  have hsReal : (0 : ℝ) < scale := by exact_mod_cast hsPos
  have h₁ : lo₁ ≤ hi₁ := by
    exact_mod_cast (div_le_div_iff_of_pos_right hsReal).mp (hlo₁.trans hhi₁)
  have h₂ : lo₂ ≤ hi₂ := by
    exact_mod_cast (div_le_div_iff_of_pos_right hsReal).mp (hlo₂.trans hhi₂)
  have hl := max_le_max h₁ h₂
  have hu := max_le hbound₁ hbound₂
  have hgap : max hi₁ hi₂ - max lo₁ lo₂ ≤ err := by omega
  have hhiFit : (max hi₁ hi₂) ^ 2 + (scale - 1) < 2 ^ w :=
    (Nat.add_le_add_right (Nat.pow_le_pow_left hu _) _).trans_lt hroom
  have hloFit : (max lo₁ lo₂) ^ 2 < 2 ^ w :=
    ((Nat.pow_le_pow_left hl _).trans (Nat.le_add_right _ _)).trans_lt hhiFit
  obtain ⟨out, hr, lb, ub, hp, horder, _, h50, h52, hm, hf⟩ :=
    finishInitSparsifierLengthFactor_runs cDeg phiConst phiMin paths M
      (ω := ω) hs hsPos h60 h40 h61 h42 hlo₁ hhi₁ hlo₂ hhi₂ hw hloFit hhiFit
  refine ⟨out, hr, lb, ub, hp hpos, horder, ?_, ?_, hm, hf⟩
  · rw [h52]
    exact initSparsifierLengthSquare_upper hsPos hu
  · rw [h50, h52]
    exact initSparsifierLengthSquare_gap hsPos hl hu hgap

/-- Evaluate the path bounds for the input and witness expanders before
taking the squared maximum for the sparsifier length factor. -/
@[expose] def computeInitSparsifierLengthFactor
    (qEntry bits load log pack exp shiftEntry Kγ c : ℕ) : Stmt :=
  computeInitSparsifierCitedPath qEntry bits load log pack exp shiftEntry Kγ c 60 61 ;;
  computeInitSparsifierWitnessPath qEntry bits load log pack exp shiftEntry Kγ c 40 42 ;;
  finishInitSparsifierLengthFactor

/-- Given the two path runs, compose their enclosures and heap frames
with the final squared maximum. -/
theorem computeInitSparsifierLengthFactor_of_runs
    {w qEntry bits load log pack exp shiftEntry Kγ c M scale heap ret₁ ret₂ cost₁ cost₂ : ℕ}
    {p : Program} {ω : ℕ → Bool} {st mid ready : State}
    {cDeg phiConst phiMin : ℝ} {paths : Spanner.PathDSTool}
    (hr₁ : Runs w p ω (computeInitSparsifierCitedPath qEntry bits load log pack exp shiftEntry Kγ c 60 61)
      st .normal mid cost₁)
    (hr₂ : Runs w p ω (computeInitSparsifierWitnessPath qEntry bits load log pack exp shiftEntry Kγ c 40 42)
      mid .normal ready cost₂)
    (hlo₁ : (mid.regs 60 : ℝ) / scale ≤ paths.γ_ExpPath phiMin M)
    (hhi₁ : paths.γ_ExpPath phiMin M ≤ (mid.regs 61 : ℝ) / scale)
    (hlo₂ : (ready.regs 40 : ℝ) / scale ≤ paths.γ_ExpPath phiConst (Spanner.capM_W cDeg phiMin M))
    (hhi₂ : paths.γ_ExpPath phiConst (Spanner.capM_W cDeg phiMin M) ≤ (ready.regs 42 : ℝ) / scale)
    (h60 : ready.regs 60 = mid.regs 60) (h61 : ready.regs 61 = mid.regs 61)
    (hs : ready.regs 4 = scale) (hsPos : 0 < scale) (hw : 1 < 2 ^ w)
    (hh : (max (mid.regs 61) (ready.regs 42)) ^ 2 + (scale - 1) < 2 ^ w)
    (hbase : heap ≤ ret₁) (hret : ready.regs 99 = ret₂)
    (hf₁ : ∀ a < heap, mid.mem a = st.mem a)
    (hf₂ : ∀ a < ret₁, ready.mem a = mid.mem a) (hz : ZeroFrom ready.mem ret₂) :
    ∃ out, Runs w p ω (computeInitSparsifierLengthFactor qEntry bits load log pack exp shiftEntry Kγ c)
      st .normal out (cost₁ + cost₂ + 48) ∧
      (out.regs 50 : ℝ) / scale ≤ Spanner.capGammaL cDeg phiConst paths phiMin M ∧
      Spanner.capGammaL cDeg phiConst paths phiMin M ≤ (out.regs 52 : ℝ) / scale ∧
      (scale ≤ max (mid.regs 60) (ready.regs 40) → 0 < out.regs 50) ∧
      out.regs 50 ≤ out.regs 52 ∧ out.regs 52 < 2 ^ w ∧ out.regs 99 = ret₂ ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem ret₂ := by
  have hsReal : (0 : ℝ) < scale := by exact_mod_cast hsPos
  have hmax := max_le_max
    (show mid.regs 60 ≤ mid.regs 61 by
      exact_mod_cast (div_le_div_iff_of_pos_right hsReal).mp (hlo₁.trans hhi₁))
    (show ready.regs 40 ≤ ready.regs 42 by
      exact_mod_cast (div_le_div_iff_of_pos_right hsReal).mp (hlo₂.trans hhi₂))
  have hl := (Nat.pow_le_pow_left hmax 2).trans_lt ((Nat.le_add_right ..).trans_lt hh)
  obtain ⟨out, hr₃, lb, ub, hp, hle, hfit, _, _, hm, hk⟩ :=
    finishInitSparsifierLengthFactor_runs cDeg phiConst phiMin paths M (p := p) (ω := ω)
      hs hsPos h60 rfl h61 rfl hlo₁ hhi₁ hlo₂ hhi₂ hw hl hh
  refine ⟨out, ?_, lb, ub, hp, hle, hfit, (hk 99 (by decide)).trans hret,
    fun a ha => (congrFun hm a).trans ((hf₂ a (ha.trans_le hbase)).trans (hf₁ a ha)), hm.symm ▸ hz⟩
  exact runs_seq_iff.mpr (Or.inr ⟨mid, cost₁, cost₂ + 47, hr₁,
    runs_seq_iff.mpr (Or.inr ⟨ready, cost₂, 46, hr₂, hr₃, by omega⟩), by omega⟩)

end MinCostFlow.MinRatio
