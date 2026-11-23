module

public import MinCostFlow.MinRatio.InitSparsifierPower

public import MinCostFlow.MinRatio.InitSparsifierFallbackBounds

/-!
# Runtime fallback path length bounds

The path length bound compares a power with a logarithm divided by the
effective conductance. Bound the latter term with scaled products of
the logarithm and the inverse conductance.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM

/-- Compute the conductance maxima and use them in the fallback
products for the current graph. -/
@[expose] def initSparsifierFallback (c : ℕ) : Stmt :=
  initSparsifierInverseBounds c ;; initSparsifierFallbackBounds

/-- The output words bound the logarithmic term in the concrete path
length formula. -/
theorem initSparsifierFallback_runs {w Kγ c M scale logLo logHi lo hi : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {phi : ℝ}
    (h37 : st.regs 37 = Expander.PathDSProg.csGammaExp Kγ (3 * M))
    (h4 : st.regs 4 = scale) (h33 : st.regs 33 = scale)
    (h34 : st.regs 34 = logLo) (h35 : st.regs 35 = logHi)
    (h46 : st.regs 46 = lo) (h47 : st.regs 47 = hi)
    (hc : 0 < c) (hs : 0 < scale) (hp : 0 < phi) (hw : 1 < 2 ^ w)
    (hl : (logLo : ℝ) / scale ≤ Real.log (2 * (M : ℝ) + 2))
    (hu : Real.log (2 * (M : ℝ) + 2) ≤ (logHi : ℝ) / scale)
    (hlo : (lo : ℝ) / scale ≤ 1 / phi) (hhi : 1 / phi ≤ (hi : ℝ) / scale) :
    let cited := max 2 (c * Cited.csGamma Kγ (3 * M)) * scale
    max (max lo hi) cited < 2 ^ w →
    25 * (logLo + scale) < 2 ^ w →
    25 * (logHi + scale) < 2 ^ w →
    25 * (logLo + scale) * max lo cited < 2 ^ w →
    25 * (logHi + scale) * max hi cited + (scale - 1) < 2 ^ w →
    let target := 25 * (Real.log (2 * (M : ℝ) + 2) + 1) / Expander.csPhiOut Kγ c phi M
    ∃ out, Runs w p ω (initSparsifierFallback c) st .normal out 61 ∧
      (out.regs 43 : ℝ) / scale ≤ target ∧ target ≤ (out.regs 44 : ℝ) / scale ∧
      out.regs 44 ≤ (25 * (logHi + scale) * max hi cited + (scale - 1)) / scale ∧
      (∀ logBound invBound logErr invErr,
        logHi + scale ≤ logBound * scale → max hi cited ≤ invBound * scale →
        logHi - logLo ≤ logErr → hi - lo ≤ invErr →
        out.regs 44 - out.regs 43 ≤ 25 * (logErr * invBound + logBound * invErr) + 2) ∧
      out.mem = st.mem ∧
      (∀ r, r ≠ 31 → r ≠ 32 → r ≠ 36 → r ≠ 37 → r ≠ 43 → r ≠ 44 → r ≠ 45 →
        out.regs r = st.regs r) := by
  dsimp only
  intro hfit hmLo hmHi hfLo hfHi
  obtain ⟨mid, hr₁, il, iu, h36, h37', hm₁, hk₁⟩ :=
    initSparsifierInverseBounds_runs (p := p) (ω := ω) h37 h4 h46 h47 hc hs hp hlo hhi hfit
  obtain ⟨out, hr₂, lb, ub, hword, hgap, hm₂, hk₂⟩ :=
    initSparsifierFallbackBounds_runs (p := p) (ω := ω)
      ((hk₁ 4 (by decide) (by decide) (by decide)).trans h4)
      ((hk₁ 33 (by decide) (by decide) (by decide)).trans h33)
      ((hk₁ 34 (by decide) (by decide) (by decide)).trans h34)
      ((hk₁ 35 (by decide) (by decide) (by decide)).trans h35)
      h36 h37' hs hw hl hu (h36 ▸ il) (h37' ▸ iu) hmLo hmHi hfLo hfHi
  rw [mul_one_div] at lb ub
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 29, 31, hr₁, hr₂, rfl⟩), lb, ub,
    hword, ?_, hm₂.trans hm₁, fun r h31 h32 h36 h37 h43 h44 h45 =>
      (hk₂ r h31 h32 h43 h44).trans (hk₁ r h36 h37 h45)⟩

  intro logBound invBound logErr invErr hlog hinv hle hie
  apply hgap logBound invBound logErr invErr hlog hinv hle
  exact (show max hi (max 2 (c * Cited.csGamma Kγ (3 * M)) * scale) -
    max lo (max 2 (c * Cited.csGamma Kγ (3 * M)) * scale) ≤ hi - lo by omega).trans hie

/-- Evaluate the fallback term from a conductance interval in
registers 31 and 32 and logarithm bounds in registers 34 and 35. -/
@[expose] def initSparsifierFallbackFromConductance (c : ℕ) : Stmt :=
  initSparsifierReciprocal ;; initSparsifierFallback c

/-- The fallback enclosure accounts for both reciprocal and product
rounding. -/
theorem initSparsifierFallbackFromConductance_runs
    {w Kγ c M scale logLo logHi lo hi : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {phi : ℝ}
    (h37 : st.regs 37 = Expander.PathDSProg.csGammaExp Kγ (3 * M))
    (h4 : st.regs 4 = scale) (h33 : st.regs 33 = scale)
    (h34 : st.regs 34 = logLo) (h35 : st.regs 35 = logHi)
    (h31 : st.regs 31 = lo) (h32 : st.regs 32 = hi)
    (hc : 0 < c) (hs : 0 < scale) (hl : 0 < lo) (hw : 1 < 2 ^ w)
    (hlogLo : (logLo : ℝ) / scale ≤ Real.log (2 * (M : ℝ) + 2))
    (hlogHi : Real.log (2 * (M : ℝ) + 2) ≤ (logHi : ℝ) / scale)
    (hlo : (lo : ℝ) / scale ≤ phi) (hhi : phi ≤ (hi : ℝ) / scale)
    (hrec : scale * scale + (lo - 1) < 2 ^ w) :
    let cited := max 2 (c * Cited.csGamma Kγ (3 * M)) * scale
    let recLo := scale * scale / hi
    let recHi := (scale * scale + (lo - 1)) / lo
    max (max recLo recHi) cited < 2 ^ w →
    25 * (logLo + scale) < 2 ^ w →
    25 * (logHi + scale) < 2 ^ w →
    25 * (logLo + scale) * max recLo cited < 2 ^ w →
    25 * (logHi + scale) * max recHi cited + (scale - 1) < 2 ^ w →
    let target := 25 * (Real.log (2 * (M : ℝ) + 2) + 1) / Expander.csPhiOut Kγ c phi M
    ∃ out, Runs w p ω (initSparsifierFallbackFromConductance c) st .normal out 80 ∧
      (out.regs 43 : ℝ) / scale ≤ target ∧ target ≤ (out.regs 44 : ℝ) / scale ∧
      out.regs 44 ≤ (25 * (logHi + scale) * max recHi cited + (scale - 1)) / scale ∧
      (∀ logBound invBound logErr invErr,
        logHi + scale ≤ logBound * scale → max recHi cited ≤ invBound * scale →
        logHi - logLo ≤ logErr → recHi - recLo ≤ invErr →
        out.regs 44 - out.regs 43 ≤ 25 * (logErr * invBound + logBound * invErr) + 2) ∧
      out.mem = st.mem ∧
      (∀ r, r ≠ 31 → r ≠ 32 → r ≠ 36 → r ≠ 37 → r ≠ 43 → r ≠ 44 →
        r ≠ 45 → r ≠ 46 → r ≠ 47 → out.regs r = st.regs r) := by
  dsimp only
  intro hfit hmLo hmHi hfLo hfHi
  obtain ⟨mid, hr₁, rl, ru, h46, h47, hm₁, hk₁⟩ :=
    initSparsifierReciprocal_runs (p := p) (ω := ω) h4 h31 h32 hs hl hlo hhi hrec
  have hp : 0 < phi := lt_of_lt_of_le (by positivity) hlo
  obtain ⟨out, hr₂, lb, ub, hword, hgap, hm₂, hk₂⟩ :=
    initSparsifierFallback_runs (p := p) (ω := ω)
      ((hk₁ 37 (by decide) (by decide) (by decide)).trans h37)
      ((hk₁ 4 (by decide) (by decide) (by decide)).trans h4)
      ((hk₁ 33 (by decide) (by decide) (by decide)).trans h33)
      ((hk₁ 34 (by decide) (by decide) (by decide)).trans h34)
      ((hk₁ 35 (by decide) (by decide) (by decide)).trans h35)
      h46 h47 hc hs hp hw hlogLo hlogHi (h46 ▸ rl) (h47 ▸ ru) hfit hmLo hmHi hfLo hfHi
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 18, 61, hr₁, hr₂, rfl⟩), lb, ub,
    hword, hgap, hm₂.trans hm₁, fun r h31 h32 h36 h37 h43 h44 h45 h46 h47 =>
      (hk₂ r h31 h32 h36 h37 h43 h44 h45).trans (hk₁ r h45 h46 h47)⟩

/-- After computing the powered term, restore the working denominator
and copy the saved input conductance bounds into the fallback registers. -/
@[expose] def prepareInitSparsifierFallback : Stmt :=
  .assign 33 (.reg 4) ;;
  .assign 31 (.reg 53) ;;
  .assign 32 (.reg 54)

/-- The three copies preserve the powered endpoints and the heap cursor. -/
theorem prepareInitSparsifierFallback_runs {w : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} :
    ∃ out, Runs w p ω prepareInitSparsifierFallback st .normal out 8 ∧
      out.regs 33 = st.regs 4 ∧ out.regs 31 = st.regs 53 ∧ out.regs 32 = st.regs 54 ∧
      out.mem = st.mem ∧ (∀ r, r ≠ 33 → r ≠ 31 → r ≠ 32 → out.regs r = st.regs r) := by
  let a := {st with regs := Function.update st.regs 33 (st.regs 4)}
  let b := {a with regs := Function.update a.regs 31 (st.regs 53)}
  let out := {b with regs := Function.update b.regs 32 (st.regs 54)}
  have hr₁ : Runs w p ω (.assign 33 (.reg 4)) st .normal a 2 :=
    runs_assign_iff.mpr ⟨_, rfl, rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign 31 (.reg 53)) a .normal b 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, a], rfl, rfl, rfl⟩
  have hr₃ : Runs w p ω (.assign 32 (.reg 54)) b .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, a, b], rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨a, 2, 5, hr₁,
    runs_seq_iff.mpr (Or.inr ⟨b, 2, 2, hr₂, hr₃, rfl⟩), rfl⟩),
    by simp [out, b, a], by simp [out, b], by simp [out], rfl,
    fun r h33 h31 h32 => by simp [out, b, a, h33, h31, h32]⟩

/-- Evaluate the fallback logarithm before forming the reciprocal and
the two fallback endpoints. -/
@[expose] def computeInitSparsifierFallback (bits load log pack c : ℕ) : Stmt :=
  initSparsifierFallbackLog bits load log pack ;;
  initSparsifierFallbackFromConductance c

/-- The logarithm and the reciprocal together enclose the fallback term.
The word budget uses the logarithm routine's upper numerator bound. -/
theorem computeInitSparsifierFallback_runs
    {w h Kγ c M precision limbs heap bits load log pack lo hi : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {phi : ℝ}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hlog : MeetsContract w p log (Num.logarithmContract w h (precision - (2 * M + 2).size - 10)))
    (hM : st.regs 23 = M) (h4 : st.regs 4 = 2 ^ precision)
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision) (hh : st.regs 98 = heap)
    (h33 : st.regs 33 = 2 ^ precision)
    (h37 : st.regs 37 = Expander.PathDSProg.csGammaExp Kγ (3 * M))
    (h31 : st.regs 31 = lo) (h32 : st.regs 32 = hi)
    (hc : 0 < c) (hl : 0 < lo)
    (hw : 2 * M + 2 < 2 ^ w) (hword : (2 * M + 2) * 2 ^ precision < 2 ^ w)
    (hfit : 2 * ((2 * M + 2) * 2 ^ precision) < Num.capacity h limbs)
    (hroom : heap + limbs + limbs + Num.logarithmSpace limbs precision (2 * M + 2).size < 2 ^ w)
    (hz : ZeroFrom st.mem heap) (hdiv : h ∣ precision)
    (hacc : (2 * M + 2).size + 11 ≤ precision)
    (hcap : precision + (2 * M + 2).size + 4 ≤ h * limbs)
    (hprec : 2 * precision + 9 < 2 ^ w) (hwidth : precision < w) :
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
    let target := 25 * (Real.log (2 * (M : ℝ) + 2) + 1) / Expander.csPhiOut Kγ c phi M
    ∃ out cost ret, Runs w p ω (computeInitSparsifierFallback bits load log pack c) st .normal out cost ∧
      (out.regs 43 : ℝ) / scale ≤ target ∧ target ≤ (out.regs 44 : ℝ) / scale ∧
      out.regs 44 ≤ (25 * (logCap + scale) * max recHi cited + (scale - 1)) / scale ∧
      (∀ logBound invBound invErr,
        2 * M + 3 ≤ logBound → max recHi cited ≤ invBound * scale → recHi - recLo ≤ invErr →
        out.regs 44 - out.regs 43 ≤
          25 * ((4 * 2 ^ ((2 * M + 2).size + 10)) * invBound + logBound * invErr) + 2) ∧
      out.regs 4 = scale ∧ out.regs 99 = ret ∧ heap ≤ ret ∧
      ret ≤ heap + limbs + limbs + Num.logarithmSpace limbs precision (2 * M + 2).size ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem ret ∧
      (∀ r < 95, r ∉ ([2, 3, 4, 31, 32, 34, 35, 36, 37, 43, 44, 45, 46, 47, 92] : List ℕ) →
        out.regs r = st.regs r) ∧
      cost ≤ 71 * limbs + Num.logarithmCost limbs precision (2 * M + 2).size +
        14 * (2 * M + 2).size + 179 := by
  dsimp only
  intro hlow hhigh hrec hmax hm hfLo hfHi
  obtain ⟨mid, cost, ret, hr₁, hlo, hhi, hlogGap, hupper, hscale, hret, hbase, htop, hf, hz', hk, hcost⟩ :=
    initSparsifierFallbackLog_runs (ω := ω) hbits hload hpack hlog hM h4 hL hP hh
      hw hword hfit hroom hz hdiv hacc hcap hprec hwidth
  have hpos : (0 : ℝ) < ((2 ^ precision : ℕ) : ℝ) := by positivity
  have horder : mid.regs 34 ≤ mid.regs 35 := by
    exact_mod_cast (div_le_div_iff_of_pos_right hpos).mp (hlo.trans hhi)
  have hml := Nat.mul_le_mul_left 25 (Nat.add_le_add_right (horder.trans hupper) (2 ^ precision))
  have hmu := Nat.mul_le_mul_left 25 (Nat.add_le_add_right hupper (2 ^ precision))
  obtain ⟨out, hr₂, lb, ub, hbound, hgap, hmem, hk₂⟩ :=
    initSparsifierFallbackFromConductance_runs (p := p) (ω := ω)
      ((hk 37 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h37)
      hscale
      ((hk 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h33)
      rfl rfl
      ((hk 31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h31)
      ((hk 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h32)
      hc (by positivity) hl (by omega) hlo hhi hlow hhigh hrec hmax (hml.trans_lt hm) (hmu.trans_lt hm)
      ((Nat.mul_le_mul_right _ hml).trans_lt hfLo)
      ((Nat.add_le_add_right (Nat.mul_le_mul_right _ hmu) _).trans_lt hfHi)
  refine ⟨out, cost + 81, ret, runs_seq_iff.mpr (Or.inr ⟨mid, cost, 80, hr₁, hr₂, by omega⟩),
    lb, ub, hbound.trans (Nat.div_le_div_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ hmu) _)), ?_, ?_, ?_, by omega, htop, fun a ha => (congrFun hmem a).trans (hf a ha),
    hmem.symm ▸ hz', ?_, by omega⟩
  · intro logBound invBound invErr hlog hinv herr
    apply hgap logBound invBound _ invErr ?_ hinv hlogGap herr
    calc
      _ ≤ (2 * M + 2) * 2 ^ precision + 2 ^ precision := Nat.add_le_add_right hupper _
      _ = (2 * M + 3) * 2 ^ precision := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ hlog
  · exact (hk₂ 4 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hscale
  · exact (hk₂ 99 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hret
  · intro r hr hkeep
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hkeep
    obtain ⟨h2, h3, h4, h31, h32, h34, h35, h36, h37, h43, h44, h45, h46, h47, h92⟩ := hkeep
    exact (hk₂ r h31 h32 h36 h37 h43 h44 h45 h46 h47).trans (hk r hr h2 h3 h4 h34 h35 h92)

/-- Evaluate the fallback term using the saved conductance endpoints. -/
@[expose] def evaluateInitSparsifierFallback (bits load log pack c : ℕ) : Stmt :=
  prepareInitSparsifierFallback ;; computeInitSparsifierFallback bits load log pack c

/-- The saved conductance words and the runtime logarithm determine the
fallback enclosure at the working precision. -/
theorem evaluateInitSparsifierFallback_runs
    {w h Kγ c M precision limbs heap bits load log pack lo hi : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {phi : ℝ}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hlog : MeetsContract w p log (Num.logarithmContract w h (precision - (2 * M + 2).size - 10)))
    (hM : st.regs 23 = M) (h4 : st.regs 4 = 2 ^ precision)
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision) (hh : st.regs 98 = heap)
    (h37 : st.regs 37 = Expander.PathDSProg.csGammaExp Kγ (3 * M))
    (h53 : st.regs 53 = lo) (h54 : st.regs 54 = hi)
    (hc : 0 < c) (hl : 0 < lo)
    (hw : 2 * M + 2 < 2 ^ w) (hword : (2 * M + 2) * 2 ^ precision < 2 ^ w)
    (hfit : 2 * ((2 * M + 2) * 2 ^ precision) < Num.capacity h limbs)
    (hroom : heap + limbs + limbs + Num.logarithmSpace limbs precision (2 * M + 2).size < 2 ^ w)
    (hz : ZeroFrom st.mem heap) (hdiv : h ∣ precision)
    (hacc : (2 * M + 2).size + 11 ≤ precision)
    (hcap : precision + (2 * M + 2).size + 4 ≤ h * limbs)
    (hprec : 2 * precision + 9 < 2 ^ w) (hwidth : precision < w) :
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
    let target := 25 * (Real.log (2 * (M : ℝ) + 2) + 1) / Expander.csPhiOut Kγ c phi M
    ∃ out cost ret, Runs w p ω (evaluateInitSparsifierFallback bits load log pack c) st .normal out cost ∧
      (out.regs 43 : ℝ) / scale ≤ target ∧ target ≤ (out.regs 44 : ℝ) / scale ∧
      out.regs 44 ≤ (25 * (logCap + scale) * max recHi cited + (scale - 1)) / scale ∧
      (∀ logBound invBound invErr,
        2 * M + 3 ≤ logBound → max recHi cited ≤ invBound * scale → recHi - recLo ≤ invErr →
        out.regs 44 - out.regs 43 ≤
          25 * ((4 * 2 ^ ((2 * M + 2).size + 10)) * invBound + logBound * invErr) + 2) ∧
      out.regs 4 = scale ∧ out.regs 99 = ret ∧ heap ≤ ret ∧
      ret ≤ heap + limbs + limbs + Num.logarithmSpace limbs precision (2 * M + 2).size ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem ret ∧
      (∀ r < 95, r ∉ ([2, 3, 4, 31, 32, 33, 34, 35, 36, 37, 43, 44, 45, 46, 47, 92] : List ℕ) →
        out.regs r = st.regs r) ∧
      cost ≤ 71 * limbs + Num.logarithmCost limbs precision (2 * M + 2).size +
        14 * (2 * M + 2).size + 188 := by
  intro scale cited recLo recHi logCap hlo hhi hrec hmax hm hfLo hfHi target
  obtain ⟨mid, hr₁, h33, h31, h32, hmem, hk⟩ :=
    prepareInitSparsifierFallback_runs (p := p) (ω := ω) (w := w) (st := st)
  obtain ⟨out, cost, ret, hr₂, hlb, hub, hbound, hgap, hscale, hret, hbase, htop, hf, hz', hk', hcost⟩ :=
    computeInitSparsifierFallback_runs (ω := ω) hbits hload hpack hlog
      ((hk 23 (by decide) (by decide) (by decide)).trans hM)
      ((hk 4 (by decide) (by decide) (by decide)).trans h4)
      ((hk 67 (by decide) (by decide) (by decide)).trans hL)
      ((hk 68 (by decide) (by decide) (by decide)).trans hP)
      ((hk 98 (by decide) (by decide) (by decide)).trans hh)
      (h33.trans h4) ((hk 37 (by decide) (by decide) (by decide)).trans h37)
      (h31.trans h53) (h32.trans h54) hc hl hw hword hfit hroom (hmem.symm ▸ hz)
      hdiv hacc hcap hprec hwidth hlo hhi hrec hmax hm hfLo hfHi
  refine ⟨out, cost + 9, ret, runs_seq_iff.mpr (Or.inr ⟨mid, 8, cost, hr₁, hr₂, by omega⟩),
    hlb, hub, hbound, hgap, hscale, hret, hbase, htop, fun a ha => (hf a ha).trans (congrFun hmem a), hz', ?_, by omega⟩
  intro r hr hkeep
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hkeep
  obtain ⟨h2, h3, h4, h31, h32, h33, h34, h35, h36, h37, h43, h44, h45, h46, h47, h92⟩ := hkeep
  exact (hk' r hr (by simp [h2, h3, h4, h31, h32, h34, h35, h36, h37, h43, h44, h45, h46, h47, h92])).trans
    (hk r h33 h31 h32)

/-- Combine the two terms of the path bound. The powered bounds are
in registers 48 and 49, and the fallback bounds are in 43 and 44. -/
@[expose] def finishInitSparsifierPath (lower upper : ℕ) : Stmt :=
  initSparsifierPathMax 48 43 lower ;; initSparsifierPathMax 49 44 upper

/-- The returned interval encloses the concrete path length bound. -/
theorem finishInitSparsifierPath_runs {w lower upper scale a b c₀ d Kγ c M : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {K phi : ℝ}
    (h48 : st.regs 48 = a) (h49 : st.regs 49 = b)
    (h43 : st.regs 43 = c₀) (h44 : st.regs 44 = d)
    (hs : 0 < (scale : ℝ)) (h49' : lower ≠ 49) (h44' : lower ≠ 44) (hdu : lower ≠ upper)
    (hfitHi : max b d < 2 ^ w)
    (ha : (a : ℝ) / scale ≤ (Cited.csGamma Kγ (3 * M) : ℝ) ^ (max K 1 * (Expander.qOf M : ℝ)))
    (hb : (Cited.csGamma Kγ (3 * M) : ℝ) ^ (max K 1 * (Expander.qOf M : ℝ)) ≤ (b : ℝ) / scale)
    (hc : (c₀ : ℝ) / scale ≤ 25 * (Real.log (2 * (M : ℝ) + 2) + 1) / Expander.csPhiOut Kγ c phi M)
    (hd : 25 * (Real.log (2 * (M : ℝ) + 2) + 1) / Expander.csPhiOut Kγ c phi M ≤ (d : ℝ) / scale) :
    ∃ out, Runs w p ω (finishInitSparsifierPath lower upper) st .normal out 13 ∧
      (out.regs lower : ℝ) / scale ≤ Expander.csGammaExpPath Kγ c K phi M ∧
      Expander.csGammaExpPath Kγ c K phi M ≤ (out.regs upper : ℝ) / scale ∧
      out.regs lower = max a c₀ ∧ out.regs upper = max b d ∧
      max (out.regs lower) (out.regs upper) < 2 ^ w ∧ out.mem = st.mem ∧
      (∀ r, r ≠ lower → r ≠ upper → out.regs r = st.regs r) := by
  have hab : a ≤ b := by
    exact_mod_cast (div_le_div_iff_of_pos_right hs).mp (ha.trans hb)
  have hcd : c₀ ≤ d := by
    exact_mod_cast (div_le_div_iff_of_pos_right hs).mp (hc.trans hd)
  have horder := max_le_max hab hcd
  have hfitLo := horder.trans_lt hfitHi
  obtain ⟨mid, hr₁, hl, hnum₁, hm₁, hk₁⟩ := initSparsifierPathMax_runs (p := p) (ω := ω)
    (dest := lower) h48 h43 hs hfitLo
  obtain ⟨out, hr₂, hu, hnum₂, hm₂, hk₂⟩ := initSparsifierPathMax_runs (p := p) (ω := ω)
    (dest := upper) ((hk₁ 49 h49'.symm).trans h49) ((hk₁ 44 h44'.symm).trans h44) hs hfitHi
  have hn := (hk₂ lower hdu).trans hnum₁
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 6, 6, hr₁, hr₂, rfl⟩), ?_, ?_,
    hn, hnum₂, by rwa [hn, hnum₂, max_eq_right horder], hm₂.trans hm₁,
    fun r h₁ h₂ => (hk₂ r h₂).trans (hk₁ r h₁)⟩
  · rw [hk₂ lower hdu, hl, Expander.csGammaExpPath]
    exact max_le_max ha hc
  · rw [hu, Expander.csGammaExpPath]
    exact max_le_max hb hd

/-- Complete a path interval by evaluating the fallback term and
combining it with the saved powered interval. -/
@[expose] def completeInitSparsifierPath (bits load log pack c lower upper : ℕ) : Stmt :=
  evaluateInitSparsifierFallback bits load log pack c ;;
  finishInitSparsifierPath lower upper

/-- The result encloses both terms of the concrete path bound and
preserves the fresh heap returned by the logarithm. -/
theorem completeInitSparsifierPath_runs
    {w h Kγ c M precision limbs heap bits load log pack lo hi lower upper powerCap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {phi K : ℝ}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hlog : MeetsContract w p log (Num.logarithmContract w h (precision - (2 * M + 2).size - 10)))
    (hM : st.regs 23 = M) (h4 : st.regs 4 = 2 ^ precision)
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision) (hh : st.regs 98 = heap)
    (h37 : st.regs 37 = Expander.PathDSProg.csGammaExp Kγ (3 * M))
    (h53 : st.regs 53 = lo) (h54 : st.regs 54 = hi)
    (hpowerLo : (st.regs 48 : ℝ) / (2 ^ precision : ℕ) ≤
      (Cited.csGamma Kγ (3 * M) : ℝ) ^ (max K 1 * (Expander.qOf M : ℝ)))
    (hpowerHi : (Cited.csGamma Kγ (3 * M) : ℝ) ^ (max K 1 * (Expander.qOf M : ℝ)) ≤
      (st.regs 49 : ℝ) / (2 ^ precision : ℕ))
    (hpowerCap : st.regs 49 ≤ powerCap) (hpowerWord : powerCap < 2 ^ w)
    (h49 : lower ≠ 49) (h44 : lower ≠ 44) (hdu : lower ≠ upper)
    (hl4 : lower ≠ 4) (hu4 : upper ≠ 4)
    (hl99 : lower ≠ 99) (hu99 : upper ≠ 99)
    (hc : 0 < c) (hl : 0 < lo)
    (hw : 2 * M + 2 < 2 ^ w) (hword : (2 * M + 2) * 2 ^ precision < 2 ^ w)
    (hfit : 2 * ((2 * M + 2) * 2 ^ precision) < Num.capacity h limbs)
    (hroom : heap + limbs + limbs + Num.logarithmSpace limbs precision (2 * M + 2).size < 2 ^ w)
    (hz : ZeroFrom st.mem heap) (hdiv : h ∣ precision)
    (hacc : (2 * M + 2).size + 11 ≤ precision)
    (hcap : precision + (2 * M + 2).size + 4 ≤ h * limbs)
    (hprec : 2 * precision + 9 < 2 ^ w) (hwidth : precision < w) :
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
    ∃ out cost ret, Runs w p ω (completeInitSparsifierPath bits load log pack c lower upper) st .normal out cost ∧
      (out.regs lower : ℝ) / scale ≤ Expander.csGammaExpPath Kγ c K phi M ∧
      Expander.csGammaExpPath Kγ c K phi M ≤ (out.regs upper : ℝ) / scale ∧
      out.regs upper ≤ max powerCap ((25 * (logCap + scale) * max recHi cited + (scale - 1)) / scale) ∧
      (∀ logBound invBound conductanceErr powerErr,
        2 * M + 3 ≤ logBound → max recHi cited ≤ invBound * scale →
        scale ≤ invBound * lo → hi - lo ≤ conductanceErr →
        st.regs 49 - st.regs 48 ≤ powerErr →
        out.regs upper - out.regs lower ≤
          max powerErr (25 * ((4 * 2 ^ ((2 * M + 2).size + 10)) * invBound +
            logBound * (invBound ^ 2 * conductanceErr + 2)) + 2)) ∧
      out.regs 4 = scale ∧ out.regs 99 = ret ∧ heap ≤ ret ∧
      ret ≤ heap + limbs + limbs + Num.logarithmSpace limbs precision (2 * M + 2).size ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem ret ∧
      (∀ r < 95, r ≠ lower → r ≠ upper → r ∉ ([2, 3, 4, 31, 32, 33, 34, 35, 36, 37, 43, 44, 45, 46, 47, 92] : List ℕ) →
        out.regs r = st.regs r) ∧
      cost ≤ 71 * limbs + Num.logarithmCost limbs precision (2 * M + 2).size +
        14 * (2 * M + 2).size + 202 := by
  intro scale cited recLo recHi logCap hlo hhi hrec hmax hm hfLo hfHi
  obtain ⟨mid, cost, ret, hr₁, lb, ub, hword', hgap, hscaleWord, hret, hbase, htop, hf, hz', hk, hcost⟩ :=
    evaluateInitSparsifierFallback_runs (ω := ω) hbits hload hpack hlog hM h4 hL hP hh
      h37 h53 h54 hc hl hw hword hfit hroom hz hdiv hacc hcap hprec hwidth
      hlo hhi hrec hmax hm hfLo hfHi
  have h48' := hk 48 (by decide) (by decide)
  have h49' := hk 49 (by decide) (by decide)
  have hscale : (0 : ℝ) < (scale : ℝ) := by dsimp [scale]; positivity
  obtain ⟨out, hr₂, hlb, hub, hloWord, hnum, _, hmem, hk'⟩ :=
    finishInitSparsifierPath_runs (p := p) (ω := ω) (lower := lower) (upper := upper)
      rfl rfl rfl rfl hscale h49 h44 hdu
      (max_lt_iff.mpr ⟨(h49'.symm ▸ hpowerCap).trans_lt hpowerWord, hword'.trans_lt ((Nat.div_le_self ..).trans_lt hfHi)⟩)
      (h48'.symm ▸ hpowerLo) (h49'.symm ▸ hpowerHi) lb ub
  refine ⟨out, cost + 14, ret, runs_seq_iff.mpr (Or.inr ⟨mid, cost, 13, hr₁, hr₂, by omega⟩),
    hlb, hub, hnum.symm ▸ max_le_max (h49'.symm ▸ hpowerCap) hword', ?_, (hk' 4 hl4.symm hu4.symm).trans hscaleWord, (hk' 99 hl99.symm hu99.symm).trans hret, hbase, htop,
    fun a ha => (congrFun hmem a).trans (hf a ha), hmem.symm ▸ hz',
    fun r hr hl' hu' hkeep => (hk' r hl' hu').trans (hk r hr hkeep), by omega⟩

  intro logBound invBound conductanceErr powerErr hlog hinv hlow herr hpow
  have horder : lo ≤ hi := by
    exact_mod_cast (div_le_div_iff_of_pos_right hscale).mp (hlo.trans hhi)
  have hrecGap : recHi - recLo ≤ invBound ^ 2 * conductanceErr + 2 :=
    (initSparsifierReciprocal_gap (by dsimp [scale]; positivity) hlow horder).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left _ herr) 2)
  have hfb := hgap logBound invBound _ hlog hinv hrecGap
  rw [hloWord, hnum, h48', h49']
  omega

/-- Evaluate the powered term, then the fallback term, and combine
their bounds at the same runtime precision. -/
@[expose] def computeInitSparsifierPath (bits load log pack exp shiftEntry c lower upper : ℕ) : Stmt :=
  computeInitSparsifierPathPower load exp shiftEntry pack ;;
  completeInitSparsifierPath bits load log pack c lower upper

/-- The powered and fallback phases share a heap cursor and enclose
the concrete path bound at the working scale. -/
theorem computeInitSparsifierPath_runs
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
    (h37 : st.regs 37 = Expander.PathDSProg.csGammaExp Kγ (3 * M))
    (h53 : st.regs 53 = lo) (h54 : st.regs 54 = hi)
    (hs : st.regs 33 = 2 ^ (precision + precision))
    (hsw : 2 ^ (precision + precision) < 2 ^ w)
    (hsfit : 2 * 2 ^ (precision + precision) < Num.capacity h limbs)
    (h39 : st.regs 39 = kLo) (h40 : st.regs 40 = kHi) (h38 : st.regs 38 = Expander.qOf M)
    (h34 : st.regs 34 = logLo) (h35 : st.regs 35 = logHi)
    (hkLo : (kLo : ℝ) / (2 ^ precision : ℕ) ≤ max K 1)
    (hkHi : max K 1 ≤ (kHi : ℝ) / (2 ^ precision : ℕ))
    (hlLo : (logLo : ℝ) / (2 ^ precision : ℕ) ≤ Real.log (Cited.csGamma Kγ (3 * M)))
    (hlHi : Real.log (Cited.csGamma Kγ (3 * M)) ≤ (logHi : ℝ) / (2 ^ precision : ℕ))
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
    let expLo := kLo * Expander.qOf M * logLo
    let expHi := kHi * Expander.qOf M * logHi
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
    ∃ out cost ret, Runs w p ω (computeInitSparsifierPath bits load log pack exp shiftEntry c lower upper) st .normal out cost ∧
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
      (∀ r < 95, r ≠ lower → r ≠ upper → r ∉ ([2, 3, 4, 31, 32, 33, 34, 35, 36, 37, 43, 44, 45, 46, 47, 48, 49, 68, 92, 94] : List ℕ) →
        out.regs r = st.regs r) ∧
      cost ≤ 345 * limbs + 2 * Num.positiveExponentialCost limbs (precision + precision) range + Num.logarithmCost limbs precision (2 * M + 2).size +
        14 * (2 * M + 2).size + 592 := by
  intro expLo expHi hup hwExp hfitExp range haccExp hcapExp hq hwordExp space afterPower hroom
    scale cited recLo recHi logCap hlo hhi hrec hmax hm hfLo hfHi
  have hdivExp : h ∣ precision + precision := dvd_add hdiv hdiv
  obtain ⟨mid, cost₁, hr₁, pl, pu, hExpLo, hExpHi, pw, hscale, hprecision, hheap, hz₁, hf₁, hk₁, hcost₁⟩ :=
    computeInitSparsifierPathPower_runs (ω := ω) hload hexp hshift hpack hs hL hP hh hsw hsfit
      hz hdivExp hprecExp hwidth h39 h40 h38 h34 h35 hkLo hkHi hlLo hlHi hkl hkh
      hup hwExp hfitExp haccExp hcapExp hq hwordExp (lt_of_le_of_lt (by change afterPower ≤ _; omega) hroom)
  obtain ⟨out, cost₂, ret, hr₂, lb, ub, hwordOut, hgap, hscaleOut, hret, hbase, htop, hf₂, hz₂, hk₂, hc₂⟩ :=
    completeInitSparsifierPath_runs (ω := ω) hbits hload hpack hlog
      ((hk₁ 23 (by decide)).trans hM) hscale ((hk₁ 67 (by decide)).trans hL) hprecision hheap
      ((hk₁ 37 (by decide)).trans h37) ((hk₁ 53 (by decide)).trans h53) ((hk₁ 54 (by decide)).trans h54)
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using pl)
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using pu)
      ((le_max_right ..).trans pw) hwordExp h49 h44 hdu hl4 hu4 hl99 hu99 hc hl hw hword hfit hroom
      hz₁ hdiv hacc hcap (by omega) hwidth hlo hhi hrec hmax hm hfLo hfHi
  change cost₁ ≤ 274 * limbs + 2 * Num.positiveExponentialCost limbs (precision + precision) range + 389 at hcost₁
  refine ⟨out, cost₁ + cost₂ + 1, ret, runs_seq_iff.mpr (Or.inr ⟨mid, cost₁, cost₂, hr₁, hr₂, rfl⟩),
    lb, ub, hwordOut, ?_, hscaleOut, ?_, hret, by omega, htop, fun a ha => (hf₂ a (by omega)).trans (hf₁ a ha),
    hz₂, ?_, by omega⟩
  · intro logBound invBound condErr expErr hlogBound hinv hlow hcond hExp
    have hsReal : (0 : ℝ) < (scale : ℝ) := by dsimp [scale]; positivity
    have hkOrder : kLo ≤ kHi := by
      exact_mod_cast (div_le_div_iff_of_pos_right hsReal).mp (hkLo.trans hkHi)
    have hlogOrder : logLo ≤ logHi := by
      exact_mod_cast (div_le_div_iff_of_pos_right hsReal).mp (hlLo.trans hlHi)
    have hexpOrder : expLo ≤ expHi :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ hkOrder) hlogOrder
    have hRange : (expHi : ℝ) / 2 ^ (precision + precision) ≤ range := by
      have hpow : 0 < (2 : ℕ) ^ (precision + precision) := Nat.two_pow_pos _
      have hlt : expHi < range * 2 ^ (precision + precision) :=
        (Nat.div_lt_iff_lt_mul hpow).mp (Nat.lt_succ_self _)
      apply (div_le_iff₀ (by positivity)).mpr
      exact_mod_cast hlt.le
    exact hgap logBound invBound condErr _ hlogBound hinv hlow hcond
      (initSparsifierPoweredGap hexpOrder hExp hRange hExpLo hExpHi)
  · exact (hk₂ 68 (by decide) hl68.symm hu68.symm (by decide)).trans hprecision
  · intro r hr hlow hupp hkeep
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hkeep
    obtain ⟨h2, h3, h4', h31, h32, h33, h34', h35', h36, h37', h43, h44', h45, h46, h47, h48, h49', h68, h92, h94⟩ := hkeep
    exact (hk₂ r hr hlow hupp (by simp [h2, h3, h4', h31, h32, h33, h34', h35', h36, h37', h43, h44', h45, h46, h47, h92])).trans
      (hk₁ r (by simp [h2, h3, h4', h31, h32, h48, h49', h68, h94,
        show r ≠ 95 by omega, show r ≠ 96 by omega, show r ≠ 97 by omega,
        show r ≠ 98 by omega, show r ≠ 99 by omega]))

end MinCostFlow.MinRatio
