module

public import MinCostFlow.MinRatio.InitSparsifierPathInputs
import MinCostFlow.MinRatio.ShiftForestScan

/-!
# Paired sparsifier path bounds

Evaluate the input and witness path enclosures and combine them to bound
the length factor used by the sparsifier.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM

/-- Run the input and witness paths in order, handing off the fresh heap. -/
@[expose] def computeInitSparsifierPathPair
    (qEntry bits load log pack exp shiftEntry Kγ c decK thr coeffLo coeffHi coeffBits : ℕ) (cDeg : ℕ := 36) : Stmt :=
  computeInitSparsifierFirstPathWithDegree qEntry bits load log pack exp shiftEntry Kγ c decK thr coeffLo coeffHi coeffBits cDeg ;;
  computeInitSparsifierWitnessPath qEntry bits load log pack exp shiftEntry Kγ c 40 42

/-- Path evaluation leaves the saved chain inputs in registers 130
and above. The linked calls write only their designated return registers. -/
theorem computeInitSparsifierPathPair_preserves_saved
    {w qEntry bits load log pack exp shiftEntry Kγ c decK thr coeffLo coeffHi coeffBits cDeg cost r : ℕ}
    {p : Program} {ω : ℕ → Bool} {st out : State} {o : Outcome}
    (hr : 130 ≤ r)
    (hrun : Runs w p ω
      (computeInitSparsifierPathPair qEntry bits load log pack exp shiftEntry Kγ c
        decK thr coeffLo coeffHi coeffBits cDeg) st o out cost) :
    out.regs r = st.regs r := by
  apply runs_preserves_above hr _ hrun
  rfl

/-- From the first call's postcondition, evaluate the witness path and
preserve the first endpoints. The second heap budget uses an upper
bound on the first call's return. -/
theorem computeInitSparsifierWitnessAfterFirst_runs
    {w h Kγ c M M₀ precision limbs heap heapCap bits load log pack qEntry lo hi coeffLo coeffHi coeffBits decK thr firstCost firstCap exp shiftEntry accuracy kLo kHi logLo logHi cDeg : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {K : ℝ}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hlog : MeetsContract w p log (Num.logarithmContract w h (precision - (2 * M + 2).size - 10)))
    (hexp : MeetsContract w p exp (Num.positiveExponentialContract w h accuracy))
    (hshift : MeetsContract w p shiftEntry (Num.shiftRightContract w h))
    (hqImpl : MeetsContract w p qEntry (initSparsifierPathQContract w))
    (hq8 : (Expander.PathDSProg.qRoot M + 1) ^ 8 < 2 ^ w)
    (hq2 : Expander.PathDSProg.qRoot M + 2 < 2 ^ w)
    (hK : Kγ < 2 ^ w) (htriple : 3 * M < 2 ^ w)
    (hcube : (Nat.log 2 (3 * M) + 2) ^ 4 < 2 ^ w)
    (hexpWord : Expander.PathDSProg.csGammaExp Kγ (3 * M) < 2 ^ w) (hw₄ : 4 < 2 ^ w)
    (hwide : precision + precision < w)
    (hsfit : 2 * 2 ^ (precision + precision) < Num.capacity h limbs)
    (horder : logLo ≤ logHi)
    (hlogFit : Expander.PathDSProg.csGammaExp Kγ (3 * M) * logHi < 2 ^ w)
    (hkLo : (kLo : ℝ) / (2 ^ precision : ℕ) ≤ max K 1)
    (hkHi : max K 1 ≤ (kHi : ℝ) / (2 ^ precision : ℕ))
    (hlLo : (logLo : ℝ) / (2 ^ precision : ℕ) ≤ Real.log 2)
    (hlHi : Real.log 2 ≤ (logHi : ℝ) / (2 ^ precision : ℕ))
    (hkl : kLo * Expander.qOf M < 2 ^ w) (hkh : kHi * Expander.qOf M < 2 ^ w)
    (hc : 0 < c) (hl : 0 < lo)
    (hw : 2 * M + 2 < 2 ^ w) (hword : (2 * M + 2) * 2 ^ precision < 2 ^ w)
    (hfit : 2 * ((2 * M + 2) * 2 ^ precision) < Num.capacity h limbs)
    (hdiv : h ∣ precision)
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
    let afterPower := heapCap + space + space
    afterPower + limbs + limbs + Num.logarithmSpace limbs precision (2 * M + 2).size < 2 ^ w →
    let scale := (2 : ℕ) ^ precision
    let cited := max 2 (c * Cited.csGamma Kγ (3 * M)) * scale
    let recLo := scale * scale / hi
    let recHi := (scale * scale + (lo - 1)) / lo
    let logCap := (2 * M + 2) * scale
    (lo : ℝ) / scale ≤ 1 / (c : ℝ) → 1 / (c : ℝ) ≤ (hi : ℝ) / scale →
    scale * scale + (lo - 1) < 2 ^ w →
    max (max recLo recHi) cited < 2 ^ w →
    25 * (logCap + scale) < 2 ^ w →
    25 * (logCap + scale) * max recLo cited < 2 ^ w →
    25 * (logCap + scale) * max recHi cited + (scale - 1) < 2 ^ w →
    let den := Expander.maxPhiDenOf decK thr M₀
    (∃ mid cost ret, Runs w p ω
      (computeInitSparsifierFirstPathWithDegree qEntry bits load log pack exp shiftEntry Kγ c decK thr coeffLo coeffHi coeffBits cDeg)
      st .normal mid cost ∧
      (mid.regs 60 : ℝ) / scale ≤ Expander.csGammaExpPath Kγ c K (1 / (den : ℝ)) M₀ ∧
      Expander.csGammaExpPath Kγ c K (1 / (den : ℝ)) M₀ ≤ (mid.regs 61 : ℝ) / scale ∧
      mid.regs 61 ≤ firstCap ∧ mid.regs 68 = precision ∧ mid.regs 99 = ret ∧ heap ≤ ret ∧ ret ≤ heapCap ∧
      (∀ a < heap, mid.mem a = st.mem a) ∧ ZeroFrom mid.mem ret ∧
      mid.regs 63 = den ∧ mid.regs 58 = M ∧ mid.regs 56 = lo ∧ mid.regs 57 = hi ∧
      mid.regs 39 = kLo ∧ mid.regs 40 = kHi ∧
      mid.regs 28 = logLo ∧ mid.regs 29 = logHi ∧ mid.regs 67 = limbs ∧
      (∀ r ∈ ([1, 18, 22, 25, 28, 29, 64, 65, 66, 67, 74, 75, 76, 89] : List ℕ), mid.regs r = st.regs r) ∧ cost ≤ firstCost) →
    ∃ (out : State) (cost ret a b d e : ℕ), Runs w p ω
      (computeInitSparsifierPathPair qEntry bits load log pack exp shiftEntry Kγ c decK thr coeffLo coeffHi coeffBits cDeg)
      st .normal out cost ∧
      (a : ℝ) / scale ≤ Expander.csGammaExpPath Kγ c K (1 / (den : ℝ)) M₀ ∧
      Expander.csGammaExpPath Kγ c K (1 / (den : ℝ)) M₀ ≤ (b : ℝ) / scale ∧
      (d : ℝ) / scale ≤ Expander.csGammaExpPath Kγ c K (1 / (c : ℝ)) M ∧
      Expander.csGammaExpPath Kγ c K (1 / (c : ℝ)) M ≤ (e : ℝ) / scale ∧
      b ≤ firstCap ∧ e ≤ max (2 ^ (precision + 2 * range) + 2)
        ((25 * (logCap + scale) * max recHi cited + (scale - 1)) / scale) ∧
      (∀ kBound logBound logErr, c ≤ scale → lo = scale / c → hi = (scale + (c - 1)) / c →
        kHi ≤ kBound * scale → logHi ≤ logBound * scale → logHi - logLo ≤ logErr →
        let exponentErr := Expander.qOf M * exponent *
          ((kHi - kLo) * logBound + kBound * logErr)
        let invBound := max (2 * c + 1) (max 2 (c * Cited.csGamma Kγ (3 * M)))
        e - d ≤ max (2 ^ (2 * range) * exponentErr + 4)
          (25 * ((4 * 2 ^ ((2 * M + 2).size + 10)) * invBound +
            (2 * M + 3) * (invBound ^ 2 + 2)) + 2)) ∧
      out.regs 60 = a ∧ out.regs 61 = b ∧ out.regs 40 = d ∧ out.regs 42 = e ∧
      out.regs 63 = den ∧ out.regs 4 = scale ∧ out.regs 68 = precision ∧ out.regs 99 = ret ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem ret ∧
      (∀ r ∈ ([1, 18, 22, 25, 28, 29, 64, 65, 66, 67, 74, 75, 76, 89] : List ℕ), out.regs r = st.regs r) ∧
      cost ≤ firstCost + (345 * limbs + 2 * Num.positiveExponentialCost limbs (precision + precision) range +
        Num.logarithmCost limbs precision (2 * M + 2).size + 14 * (2 * M + 2).size +
        35 * (Nat.log 2 (3 * M) + 1) + 65 * (Nat.log 2 (M + 2) + 1) + 776) + 1 := by
  intro exponent expLo expHi hup hwExp hfitExp range haccExp hcapExp hq hwordExp space afterPower hroom
    scale cited recLo recHi logCap hlo hhi hrec hmax hm hfLo hfHi den hfirst
  obtain ⟨mid, cost₁, heap₁, hr₁, al, au, hb, hp, hh, hbase, hcap₁, hf₁, hz₁,
    h63, h58, h56, h57, h39, h40, h28, h29, h67, hkeep, hc₁⟩ := hfirst
  have hroom' : heap₁ + space + space + limbs + limbs +
      Num.logarithmSpace limbs precision (2 * M + 2).size < 2 ^ w := by
    change heapCap + space + space + limbs + limbs +
      Num.logarithmSpace limbs precision (2 * M + 2).size < 2 ^ w at hroom
    omega
  obtain ⟨out, cost₂, ret, hr₂, lb, ub, he, hgap, hs, hprecOut, ht, _, _, hf₂, hz₂, hk, hc₂⟩ :=
    computeInitSparsifierWitnessPath_runs (ω := ω) (lower := 40) (upper := 42)
      hbits hload hpack hlog hexp hshift hqImpl hq8 hq2 h58 h67 hp hh hK htriple hcube hexpWord hw₄
      h56 h57 hwide hsfit h39 h40 h28 h29 horder hlogFit hkLo hkHi hlLo hlHi hkl hkh
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hc hl hw hword hfit hz₁ hdiv hacc hcap hprecExp hwidth
      hup hwExp hfitExp haccExp hcapExp hq hwordExp hroom' hlo hhi hrec hmax hm hfLo hfHi
  change cost₂ ≤ 345 * limbs + 2 * Num.positiveExponentialCost limbs (precision + precision) range +
    Num.logarithmCost limbs precision (2 * M + 2).size + 14 * (2 * M + 2).size +
    35 * (Nat.log 2 (3 * M) + 1) + 65 * (Nat.log 2 (M + 2) + 1) + 776 at hc₂
  refine ⟨out, cost₁ + cost₂ + 1, ret, mid.regs 60, mid.regs 61, out.regs 40, out.regs 42,
    runs_seq_iff.mpr (Or.inr ⟨mid, cost₁, cost₂, hr₁, hr₂, rfl⟩), al, au, lb, ub, hb, he, ?_,
    hk 60 (by decide) (by decide) (by decide) (by decide),
    hk 61 (by decide) (by decide) (by decide) (by decide), rfl, rfl,
    (hk 63 (by decide) (by decide) (by decide) (by decide)).trans h63, hs, hprecOut, ht,
    fun a ha => (hf₂ a (ha.trans_le hbase)).trans (hf₁ a ha), hz₂, ?_, by omega⟩
  · intro kBound logBound logErr hcScale hloWord hhiWord hk hlog hlogErr
    let expErr := Expander.qOf M * exponent * ((kHi - kLo) * logBound + kBound * logErr)
    have hsReal : (0 : ℝ) < (scale : ℝ) := by dsimp [scale]; positivity
    have hkOrder : kLo ≤ kHi := by
      exact_mod_cast (div_le_div_iff_of_pos_right hsReal).mp (hkLo.trans hkHi)
    have hExp : expHi - expLo ≤ expErr * scale :=
      initSparsifierPathExponent_gap hkOrder horder hk hlog le_rfl hlogErr
    let citedFactor := max 2 (c * Cited.csGamma Kγ (3 * M))
    let invBound := max (2 * c + 1) citedFactor
    obtain ⟨hcond, hlow, hrec⟩ := initPathConductanceWords_bounds hc hcScale
    have hrecHi : max recHi cited ≤ invBound * scale := by
      rw [show recHi = (scale * scale + (scale / c - 1)) / (scale / c) by simp [recHi, hloWord]]
      exact max_le (hrec.trans (Nat.mul_le_mul_right _ (le_max_left _ _)))
        (Nat.mul_le_mul_right _ (le_max_right _ _))
    have hlow' : scale ≤ invBound * lo := by
      rw [hloWord]
      exact hlow.trans (Nat.mul_le_mul_right _ ((Nat.le_succ _).trans (le_max_left _ _)))
    have hcond' : hi - lo ≤ 1 := by simpa only [hloWord, hhiWord] using hcond
    simpa only [Nat.mul_one] using
      hgap (2 * M + 3) invBound 1 expErr le_rfl hrecHi hlow' hcond' hExp
  · intro r hr
    have hm := hkeep r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (hk _ (by decide) (by decide) (by decide) (by decide)).trans hm

/-- Compute the concrete length-factor bounds from the two runtime path
intervals. -/
@[expose] def computeInitConcreteSparsifierLength
    (qEntry bits load log pack exp shiftEntry Kγ c decK thr coeffLo coeffHi coeffBits : ℕ) (cDeg : ℕ := 36) : Stmt :=
  computeInitSparsifierPathPair qEntry bits load log pack exp shiftEntry Kγ c decK thr
    coeffLo coeffHi coeffBits cDeg ;;
  finishInitSparsifierLengthFactor

/-- Apply the squared maximum to a run of the concrete path pair.
The witness path's effective conductance allows the rational input
used by the machine. -/
theorem computeInitConcreteSparsifierLength_of_pair
    {w qEntry bits load log pack exp shiftEntry Kγ c decK thr coeffLo coeffHi coeffBits
      M scale precision heap ret cost a b d e firstCap secondCap cDeg : ℕ}
    {p : Program} {ω : ℕ → Bool} {st ready : State}
    {K phiConst : ℝ} {paths : Spanner.PathDSTool}
    (hpaths : paths.γ_ExpPath = Expander.csGammaExpPath Kγ c K)
    (hc : 0 < c)
    (hs : ready.regs 4 = scale) (hprec : ready.regs 68 = precision) (hsPos : 0 < scale) (hw : 1 < 2 ^ w)
    (ha : ready.regs 60 = a) (hb : ready.regs 61 = b)
    (hd : ready.regs 40 = d) (he : ready.regs 42 = e)
    (hret : ready.regs 99 = ret) (hf : ∀ x < heap, ready.mem x = st.mem x)
    (hz : ZeroFrom ready.mem ret)
    (hkeep : ∀ r ∈ ([1, 18, 22, 25, 28, 29, 64, 65, 66, 67, 74, 75, 76, 89] : List ℕ), ready.regs r = st.regs r)
    (hbCap : b ≤ firstCap) (heCap : e ≤ secondCap)
    (hfit : (max firstCap secondCap) ^ 2 + (scale - 1) < 2 ^ w) :
    let phiMin := 1 / (Expander.maxPhiDenOf decK thr M : ℝ)
    let witnessCap := Spanner.capM_W cDeg phiMin M
    Cited.csPhi Kγ c (3 * witnessCap) ≤ phiConst →
    Runs w p ω
      (computeInitSparsifierPathPair qEntry bits load log pack exp shiftEntry Kγ c decK thr
        coeffLo coeffHi coeffBits cDeg) st .normal ready cost →
    (a : ℝ) / scale ≤ Expander.csGammaExpPath Kγ c K phiMin M →
    Expander.csGammaExpPath Kγ c K phiMin M ≤ (b : ℝ) / scale →
    (d : ℝ) / scale ≤ Expander.csGammaExpPath Kγ c K (1 / (c : ℝ)) witnessCap →
    Expander.csGammaExpPath Kγ c K (1 / (c : ℝ)) witnessCap ≤ (e : ℝ) / scale →
    ∃ out, Runs w p ω
      (computeInitConcreteSparsifierLength qEntry bits load log pack exp shiftEntry Kγ c decK thr
        coeffLo coeffHi coeffBits cDeg) st .normal out (cost + 47) ∧
      (out.regs 50 : ℝ) / scale ≤ Spanner.capGammaL cDeg phiConst paths phiMin M ∧
      Spanner.capGammaL cDeg phiConst paths phiMin M ≤ (out.regs 52 : ℝ) / scale ∧
      (scale ≤ max a d → 0 < out.regs 50) ∧
      out.regs 50 ≤ out.regs 52 ∧ out.regs 52 < 2 ^ w ∧ out.regs 4 = scale ∧ out.regs 68 = precision ∧ out.regs 99 = ret ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem ret ∧
(∀ r ∈ ([1, 18, 22, 25, 28, 29, 64, 65, 66, 67, 74, 75, 76, 89] : List ℕ), out.regs r = st.regs r) := by
  intro phiMin witnessCap hphi hr al au dl du
  have hscale : (0 : ℝ) < scale := by exact_mod_cast hsPos
  have hab : a ≤ b := by
    exact_mod_cast (div_le_div_iff_of_pos_right hscale).mp (al.trans au)
  have hde : d ≤ e := by
    exact_mod_cast (div_le_div_iff_of_pos_right hscale).mp (dl.trans du)
  have hfit' : (max b e) ^ 2 + (scale - 1) < 2 ^ w :=
    (Nat.add_le_add_right (Nat.pow_le_pow_left (max_le_max hbCap heCap) 2) _).trans_lt hfit
  have hlow : (max a d) ^ 2 < 2 ^ w := (Nat.pow_le_pow_left (max_le_max hab hde) 2).trans_lt
    ((Nat.le_add_right ..).trans_lt hfit')
  have hphiEq := initSparsifierWitnessPath_conductance_eq Kγ c witnessCap K phiConst hc hphi
  obtain ⟨out, hr₂, lb, ub, hp, hle, hw', _, _, hm, hk⟩ :=
    finishInitSparsifierLengthFactor_runs cDeg phiConst phiMin paths M (p := p) (ω := ω)
      hs hsPos ha hd hb he (by rw [hpaths]; exact al) (by rw [hpaths]; exact au)
      (by rw [hpaths, hphiEq]; exact dl) (by rw [hpaths, hphiEq]; exact du) hw hlow hfit'
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨ready, cost, 46, hr, hr₂, by omega⟩),
    lb, ub, hp, hle, hw', (hk 4 (by decide)).trans hs, (hk 68 (by decide)).trans hprec, (hk 99 (by decide)).trans hret,
    fun x hx => (congrFun hm x).trans (hf x hx), hm.symm ▸ hz, ?_⟩
  intro r hr
  exact (hk r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)).trans
    (hkeep r hr)

/-- Starting from the verified input path run, compute the witness path
and then the concrete length-factor interval. -/
theorem computeInitConcreteSparsifierLength_after_first_runs
    {w h Kγ c M M₀ precision limbs heap heapCap bits load log pack qEntry lo hi coeffLo coeffHi coeffBits decK thr firstCost firstCap exp shiftEntry accuracy kLo kHi logLo logHi cDeg : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {K phiConst : ℝ} {paths : Spanner.PathDSTool}
    (hpaths : paths.γ_ExpPath = Expander.csGammaExpPath Kγ c K)
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hlog : MeetsContract w p log (Num.logarithmContract w h (precision - (2 * M + 2).size - 10)))
    (hexp : MeetsContract w p exp (Num.positiveExponentialContract w h accuracy))
    (hshift : MeetsContract w p shiftEntry (Num.shiftRightContract w h))
    (hqImpl : MeetsContract w p qEntry (initSparsifierPathQContract w))
    (hq8 : (Expander.PathDSProg.qRoot M + 1) ^ 8 < 2 ^ w)
    (hq2 : Expander.PathDSProg.qRoot M + 2 < 2 ^ w)
    (hK : Kγ < 2 ^ w) (htriple : 3 * M < 2 ^ w)
    (hcube : (Nat.log 2 (3 * M) + 2) ^ 4 < 2 ^ w)
    (hexpWord : Expander.PathDSProg.csGammaExp Kγ (3 * M) < 2 ^ w) (hw₄ : 4 < 2 ^ w)
    (hwide : precision + precision < w)
    (hsfit : 2 * 2 ^ (precision + precision) < Num.capacity h limbs)
    (horder : logLo ≤ logHi)
    (hlogFit : Expander.PathDSProg.csGammaExp Kγ (3 * M) * logHi < 2 ^ w)
    (hkLo : (kLo : ℝ) / (2 ^ precision : ℕ) ≤ max K 1)
    (hkHi : max K 1 ≤ (kHi : ℝ) / (2 ^ precision : ℕ))
    (hlLo : (logLo : ℝ) / (2 ^ precision : ℕ) ≤ Real.log 2)
    (hlHi : Real.log 2 ≤ (logHi : ℝ) / (2 ^ precision : ℕ))
    (hkl : kLo * Expander.qOf M < 2 ^ w) (hkh : kHi * Expander.qOf M < 2 ^ w)
    (hc : 0 < c) (hl : 0 < lo)
    (hw : 2 * M + 2 < 2 ^ w) (hword : (2 * M + 2) * 2 ^ precision < 2 ^ w)
    (hfit : 2 * ((2 * M + 2) * 2 ^ precision) < Num.capacity h limbs)
    (hdiv : h ∣ precision)
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
    let afterPower := heapCap + space + space
    afterPower + limbs + limbs + Num.logarithmSpace limbs precision (2 * M + 2).size < 2 ^ w →
    let scale := (2 : ℕ) ^ precision
    let cited := max 2 (c * Cited.csGamma Kγ (3 * M)) * scale
    let recLo := scale * scale / hi
    let recHi := (scale * scale + (lo - 1)) / lo
    let logCap := (2 * M + 2) * scale
    (lo : ℝ) / scale ≤ 1 / (c : ℝ) → 1 / (c : ℝ) ≤ (hi : ℝ) / scale →
    scale * scale + (lo - 1) < 2 ^ w →
    max (max recLo recHi) cited < 2 ^ w →
    25 * (logCap + scale) < 2 ^ w →
    25 * (logCap + scale) * max recLo cited < 2 ^ w →
    25 * (logCap + scale) * max recHi cited + (scale - 1) < 2 ^ w →
    let den := Expander.maxPhiDenOf decK thr M₀
    (∃ mid cost ret, Runs w p ω
      (computeInitSparsifierFirstPathWithDegree qEntry bits load log pack exp shiftEntry Kγ c decK thr coeffLo coeffHi coeffBits cDeg)
      st .normal mid cost ∧
      (mid.regs 60 : ℝ) / scale ≤ Expander.csGammaExpPath Kγ c K (1 / (den : ℝ)) M₀ ∧
      Expander.csGammaExpPath Kγ c K (1 / (den : ℝ)) M₀ ≤ (mid.regs 61 : ℝ) / scale ∧
      mid.regs 61 ≤ firstCap ∧ mid.regs 68 = precision ∧ mid.regs 99 = ret ∧ heap ≤ ret ∧ ret ≤ heapCap ∧
      (∀ a < heap, mid.mem a = st.mem a) ∧ ZeroFrom mid.mem ret ∧
      mid.regs 63 = den ∧ mid.regs 58 = M ∧ mid.regs 56 = lo ∧ mid.regs 57 = hi ∧
      mid.regs 39 = kLo ∧ mid.regs 40 = kHi ∧
      mid.regs 28 = logLo ∧ mid.regs 29 = logHi ∧ mid.regs 67 = limbs ∧
      (∀ r ∈ ([1, 18, 22, 25, 28, 29, 64, 65, 66, 67, 74, 75, 76, 89] : List ℕ), mid.regs r = st.regs r) ∧ cost ≤ firstCost) →
    let phiMin := 1 / (den : ℝ)
    M = Spanner.capM_W cDeg phiMin M₀ →
    Cited.csPhi Kγ c (3 * M) ≤ phiConst →
    let secondCap := max (2 ^ (precision + 2 * range) + 2)
      ((25 * (logCap + scale) * max recHi cited + (scale - 1)) / scale)
    (max firstCap secondCap) ^ 2 + (scale - 1) < 2 ^ w →
    ∃ out cost ret, Runs w p ω
      (computeInitConcreteSparsifierLength qEntry bits load log pack exp shiftEntry Kγ c decK thr
        coeffLo coeffHi coeffBits cDeg) st .normal out cost ∧
      (out.regs 50 : ℝ) / scale ≤ Spanner.capGammaL cDeg phiConst paths phiMin M₀ ∧
      Spanner.capGammaL cDeg phiConst paths phiMin M₀ ≤ (out.regs 52 : ℝ) / scale ∧
      out.regs 50 ≤ out.regs 52 ∧ out.regs 52 < 2 ^ w ∧ out.regs 4 = scale ∧ out.regs 68 = precision ∧ out.regs 99 = ret ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem ret ∧
      (∀ r ∈ ([1, 18, 22, 25, 28, 29, 64, 65, 66, 67, 74, 75, 76, 89] : List ℕ), out.regs r = st.regs r) ∧
      cost ≤ firstCost + (345 * limbs + 2 * Num.positiveExponentialCost limbs (precision + precision) range +
        Num.logarithmCost limbs precision (2 * M + 2).size + 14 * (2 * M + 2).size +
        35 * (Nat.log 2 (3 * M) + 1) + 65 * (Nat.log 2 (M + 2) + 1) + 776) + 48 := by
  intro exponent expLo expHi hup hwExp hfitExp range haccExp hcapExp hq hwordExp space afterPower hroom
    scale cited recLo recHi logCap hlo hhi hrec hmax hm hfLo hfHi den hfirst phiMin hM hphi secondCap hfitSq
  obtain ⟨ready, cost, ret, a, b, d, e, hr, al, au, dl, du, hbCap, heCap, _, ha, hb, hd, he,
    _, hs, hprecOut, ht, hf, hz, hkeep, hcost⟩ :=
    computeInitSparsifierWitnessAfterFirst_runs (ω := ω) hbits hload hpack hlog hexp hshift
      hqImpl hq8 hq2 hK htriple hcube hexpWord hw₄ hwide hsfit horder hlogFit
      hkLo hkHi hlLo hlHi hkl hkh hc hl hw hword hfit hdiv hacc hcap hprecExp hwidth
      hup hwExp hfitExp haccExp hcapExp hq hwordExp hroom hlo hhi hrec hmax hm hfLo hfHi hfirst
  obtain ⟨out, hr', lb, ub, _, hle, hw', hs', hp', ht', hf', hz', hkeep'⟩ :=
    computeInitConcreteSparsifierLength_of_pair hpaths hc hs hprecOut (by positivity)
      (by omega) ha hb hd he ht hf hz hkeep hbCap heCap hfitSq (hM ▸ hphi) hr al au (hM ▸ dl) (hM ▸ du)
  change cost ≤ firstCost + (345 * limbs + 2 * Num.positiveExponentialCost limbs (precision + precision) range +
    Num.logarithmCost limbs precision (2 * M + 2).size + 14 * (2 * M + 2).size +
    35 * (Nat.log 2 (3 * M) + 1) + 65 * (Nat.log 2 (M + 2) + 1) + 776) + 1 at hcost
  exact ⟨out, cost + 47, ret, hr', lb, ub, hle, hw', hs', hp', ht', hf', hz', hkeep', by omega⟩

end MinCostFlow.MinRatio
