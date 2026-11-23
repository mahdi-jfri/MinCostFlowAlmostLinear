module

public import MinCostFlow.MinRatio.InitSparsifierPower

/-!
# Fallback length and conductance bounds

The path length bound compares a power with a logarithm divided by the
effective conductance. Bound the latter term with scaled products of
the logarithm and the inverse conductance.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM

/-- Enclose the concrete path length using bounds on the logarithms and
on the effective conductance. The conductance interval is reversed in
the quotient. -/
theorem initSparsifierPathLength_bounds
    (Kγ c : ℕ) (K phi : ℝ) (M : ℕ)
    {powLo powHi logLo logHi phiLo phiHi : ℝ}
    (hbase : 0 < Cited.csGamma Kγ (3 * M))
    (hpowLo : powLo ≤ Real.log (Cited.csGamma Kγ (3 * M)))
    (hpowHi : Real.log (Cited.csGamma Kγ (3 * M)) ≤ powHi)
    (hlogPos : 0 ≤ logLo + 1)
    (hlogLo : logLo ≤ Real.log (2 * (M : ℝ) + 2))
    (hlogHi : Real.log (2 * (M : ℝ) + 2) ≤ logHi)
    (hphiPos : 0 < phiLo)
    (hphiLo : phiLo ≤ Expander.csPhiOut Kγ c phi M)
    (hphiHi : Expander.csPhiOut Kγ c phi M ≤ phiHi) :
    let factor := max K 1 * (Expander.qOf M : ℝ)
    max (Real.exp (factor * powLo)) (25 * (logLo + 1) / phiHi) ≤
      Expander.csGammaExpPath Kγ c K phi M ∧
      Expander.csGammaExpPath Kγ c K phi M ≤
        max (Real.exp (factor * powHi)) (25 * (logHi + 1) / phiLo) := by
  dsimp only
  have hphi := hphiPos.trans_le hphiLo
  have hlogLo' : 25 * (logLo + 1) ≤ 25 * (Real.log (2 * (M : ℝ) + 2) + 1) :=
    mul_le_mul_of_nonneg_left (add_le_add_left hlogLo 1) (by norm_num)
  have hlogHi' : 25 * (Real.log (2 * (M : ℝ) + 2) + 1) ≤ 25 * (logHi + 1) :=
    mul_le_mul_of_nonneg_left (add_le_add_left hlogHi 1) (by norm_num)
  have hnumLo : 0 ≤ 25 * (logLo + 1) := mul_nonneg (by norm_num) hlogPos
  have hnumHi := hnumLo.trans (hlogLo'.trans hlogHi')
  have hlow := (div_le_div_of_nonneg_left hnumLo hphi hphiHi).trans
    (div_le_div_of_nonneg_right hlogLo' hphi.le)
  have hhigh := (div_le_div_of_nonneg_right hlogHi' hphi.le).trans
    (div_le_div_of_nonneg_left hnumHi hphiPos hphiLo)
  obtain ⟨hl, hu⟩ := initSparsifierPathPower_bounds Kγ K M hbase hpowLo hpowHi
  unfold Expander.csGammaExpPath
  exact ⟨max_le_max hl hlow, max_le_max hu hhigh⟩

/-- The shared logarithm routine adds two to register 92. Stage twice
the current graph size there to evaluate the fallback logarithm. -/
@[expose] def initSparsifierFallbackLog (bits load log pack : ℕ) : Stmt :=
  .assign 92 (.bin .mul (.const 2) (.reg 23)) ;;
  computeInitBucketLogBounds bits load log pack 34 35

/-- Reuse the shared logarithm enclosure at the runtime graph size. -/
theorem initSparsifierFallbackLog_runs {w h M precision limbs heap bits load log pack : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hlog : MeetsContract w p log (Num.logarithmContract w h (precision - (2 * M + 2).size - 10)))
    (hM : st.regs 23 = M) (hs : st.regs 4 = 2 ^ precision)
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision) (hh : st.regs 98 = heap)
    (hw : 2 * M + 2 < 2 ^ w) (hword : (2 * M + 2) * 2 ^ precision < 2 ^ w)
    (hfit : 2 * ((2 * M + 2) * 2 ^ precision) < Num.capacity h limbs)
    (hroom : heap + limbs + limbs + Num.logarithmSpace limbs precision (2 * M + 2).size < 2 ^ w)
    (hz : ZeroFrom st.mem heap) (hdiv : h ∣ precision)
    (hacc : (2 * M + 2).size + 11 ≤ precision)
    (hcap : precision + (2 * M + 2).size + 4 ≤ h * limbs)
    (hprec : 2 * precision + 9 < 2 ^ w) (hwidth : precision < w) :
    ∃ out c ret, Runs w p ω (initSparsifierFallbackLog bits load log pack) st .normal out c ∧
      (out.regs 34 : ℝ) / (2 ^ precision : ℕ) ≤ Real.log (2 * (M : ℝ) + 2) ∧
      Real.log (2 * (M : ℝ) + 2) ≤ (out.regs 35 : ℝ) / (2 ^ precision : ℕ) ∧
      out.regs 35 - out.regs 34 ≤ 4 * 2 ^ ((2 * M + 2).size + 10) ∧
      out.regs 35 ≤ (2 * M + 2) * 2 ^ precision ∧ out.regs 4 = 2 ^ precision ∧
      out.regs 99 = ret ∧ heap + limbs ≤ ret ∧
      ret ≤ heap + limbs + limbs + Num.logarithmSpace limbs precision (2 * M + 2).size ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem ret ∧
      (∀ r < 95, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 34 → r ≠ 35 → r ≠ 92 →
        out.regs r = st.regs r) ∧
      c ≤ 71 * limbs + Num.logarithmCost limbs precision (2 * M + 2).size +
        14 * (2 * M + 2).size + 98 := by
  let mid := {st with regs := Function.update st.regs 92 (2 * M)}
  have hr₁ : Runs w p ω (.assign 92 (.bin .mul (.const 2) (.reg 23))) st .normal mid 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hM,
      show 2 < 2 ^ w by omega, show 2 * M < 2 ^ w by omega], rfl, rfl, rfl⟩
  obtain ⟨out, c, ret, hr₂, hlo, hhi, _, hupper, hscale, hret, hbase, htop, hf, hz', hk, hc, hel, heu⟩ :=
    computeInitBucketLogBounds_runs (ω := ω) (st := mid) (lower := 34) (upper := 35)
      hbits hload hpack hlog (by simp [mid]) (by simpa [mid] using hs)
      (by simpa [mid] using hL) (by simpa [mid] using hP) (by simpa [mid] using hh)
      hw hword hfit hroom hz hdiv hacc hcap hprec hwidth
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  let range := (2 * M + 2).size
  let q := precision - range - 10
  have hq : q ≤ precision := by dsimp [q]; omega
  change Real.log ((↑(2 * M) : ℝ) + 2) - 2 / (2 : ℝ) ^ q ≤
    (out.regs 34 : ℝ) / (2 ^ precision : ℕ) at hel
  change (out.regs 35 : ℝ) / (2 ^ precision : ℕ) ≤
    Real.log ((↑(2 * M) : ℝ) + 2) + 2 / (2 : ℝ) ^ q at heu
  have hscalePos : (0 : ℝ) < ((2 ^ precision : ℕ) : ℝ) := by positivity
  have hwid : ((out.regs 35 : ℝ) - out.regs 34) / (2 ^ precision : ℕ) ≤
      2 * (2 / (2 : ℝ) ^ q) := by
    rw [sub_div]
    linarith only [hel, heu]
  have hscaled := (div_le_iff₀ hscalePos).mp hwid
  rw [← initDepthLogEndpointError_scale hq, mul_assoc, div_mul_cancel₀ _ hscalePos.ne'] at hscaled
  have he : precision - q = range + 10 := by dsimp [q, range]; omega
  rw [he] at hscaled
  have hgap : out.regs 35 - out.regs 34 ≤ 4 * 2 ^ (range + 10) := by
    apply Nat.sub_le_iff_le_add.mpr
    have hsum : (out.regs 35 : ℝ) ≤ (4 : ℝ) * ((2 ^ (range + 10) : ℕ) : ℝ) + out.regs 34 := by
      linarith only [hscaled]
    exact_mod_cast hsum
  push_cast at hlo hhi
  exact ⟨out, 4 + c + 1, ret, runs_seq_iff.mpr (Or.inr ⟨mid, 4, c, hr₁, hr₂, rfl⟩),
    by simpa using hlo, by simpa using hhi, hgap, hupper, hscale, hret, hbase, htop, hf, hz',
    fun r hr h2 h3 h4 h34 h35 h92 => by simpa [mid, h92] using hk r hr h2 h3 h4 h34 h35,
    by omega⟩

/-- Form a fallback numerator at the squared scale. The same code
handles either endpoint of the logarithm and inverse conductance. -/
@[expose] def initSparsifierFallbackProduct (log inv dest : ℕ) : Stmt :=
  .assign dest (.bin .mul (.bin .mul (.const 25) (.bin .add (.reg log) (.reg 4))) (.reg inv))

/-- The runtime product represents the fallback endpoint exactly at the
squared scale. -/
theorem initSparsifierFallbackProduct_runs {w log inv dest scale x y : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hs : st.regs 4 = scale) (hx : st.regs log = x) (hy : st.regs inv = y)
    (hscale : 0 < scale) (hmid : 25 * (x + scale) < 2 ^ w)
    (hfit : 25 * (x + scale) * y < 2 ^ w) :
    ∃ out, Runs w p ω (initSparsifierFallbackProduct log inv dest) st .normal out 8 ∧
      out.regs dest = 25 * (x + scale) * y ∧
      (out.regs dest : ℝ) / (scale : ℝ) ^ 2 =
        25 * ((x : ℝ) / scale + 1) * ((y : ℝ) / scale) ∧
      out.mem = st.mem ∧ (∀ r ≠ dest, out.regs r = st.regs r) := by
  have hsum : x + scale < 2 ^ w := by omega
  have hconst : 25 < 2 ^ w := by omega
  let out := {st with regs := Function.update st.regs dest (25 * (x + scale) * y)}
  have hr : Runs w p ω (initSparsifierFallbackProduct log inv dest) st .normal out 8 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hs, hx, hy, hsum, hconst, hmid, hfit],
      rfl, rfl, rfl⟩
  have he : out.regs dest = 25 * (x + scale) * y := by simp [out]
  refine ⟨out, hr, he, ?_, rfl, fun r h => by simp [out, h]⟩
  have hs' : (scale : ℝ) ≠ 0 := by exact_mod_cast hscale.ne'
  rw [he]
  push_cast
  field_simp

/-- Enclose the fallback term using nonnegative bounds for the logarithm
and the inverse conductance. -/
theorem initSparsifierFallback_bounds {logValue inverse logLo logHi invLo invHi : ℝ}
    (hl : 0 ≤ logLo + 1) (hi : 0 ≤ invLo)
    (hlogLo : logLo ≤ logValue) (hlogHi : logValue ≤ logHi)
    (hinvLo : invLo ≤ inverse) (hinvHi : inverse ≤ invHi) :
    25 * (logLo + 1) * invLo ≤ 25 * (logValue + 1) * inverse ∧
      25 * (logValue + 1) * inverse ≤ 25 * (logHi + 1) * invHi := by
  have hlog : 0 ≤ logValue + 1 := hl.trans (add_le_add_left hlogLo 1)
  refine ⟨mul_le_mul ?_ hinvLo hi ?_, mul_le_mul ?_ hinvHi (hi.trans hinvLo) ?_⟩
  · exact mul_le_mul_of_nonneg_left (add_le_add_left hlogLo 1) (by norm_num)
  · exact mul_nonneg (by norm_num) hlog
  · exact mul_le_mul_of_nonneg_left (add_le_add_left hlogHi 1) (by norm_num)
  · exact mul_nonneg (by norm_num) (hlog.trans (add_le_add_left hlogHi 1))

/-- Round the lower and upper fallback products back to the scale
held in registers 4 and 33. -/
@[expose] def initSparsifierFallbackBounds : Stmt :=
  initSparsifierFallbackProduct 34 36 31 ;;
  initSparsifierFallbackProduct 35 37 32 ;;
  rescaleInitBucketSigmaLogBounds 43 44

/-- Bound the integer gap of the fallback product using the two input
gaps before dividing by the scale and rounding outward. -/
theorem initSparsifierFallbackProduct_gap
    {scale logLo logHi invLo invHi logBound invBound logErr invErr : ℕ}
    (hs : 0 < scale) (hl : logLo ≤ logHi) (hi : invLo ≤ invHi)
    (hlog : logHi + scale ≤ logBound * scale) (hinv : invHi ≤ invBound * scale)
    (hle : logHi - logLo ≤ logErr) (hie : invHi - invLo ≤ invErr) :
    (25 * (logHi + scale) * invHi + (scale - 1)) / scale -
      25 * (logLo + scale) * invLo / scale ≤
      25 * (logErr * invBound + logBound * invErr) + 2 := by
  let lo := 25 * (logLo + scale) * invLo
  let up := 25 * (logHi + scale) * invHi
  let budget := 25 * (logErr * invBound + logBound * invErr)
  have hd₁ : logLo + (logHi - logLo) = logHi := Nat.add_sub_of_le hl
  have hd₂ : invLo + (invHi - invLo) = invHi := Nat.add_sub_of_le hi
  have he : up = lo + 25 * ((logHi - logLo) * invHi + (logLo + scale) * (invHi - invLo)) := by
    dsimp [up, lo]
    calc
      _ = 25 * (logLo + scale) * invHi + 25 * ((logHi - logLo) * invHi) := by
        conv_lhs => rw [← hd₁]
        ring
      _ = _ := by
        conv_lhs => lhs; rw [← hd₂]
        ring
  have hw : up ≤ lo + budget * scale := by
    rw [he]
    apply Nat.add_le_add_left
    have hLoBound : logLo + scale ≤ logBound * scale :=
      (Nat.add_le_add_right hl _).trans hlog
    calc
      _ ≤ 25 * (logErr * (invBound * scale) + (logBound * scale) * invErr) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul hle hinv) (Nat.mul_le_mul hLoBound hie))
      _ = _ := by dsimp [budget]; ring
  let q := lo / scale
  have hmod := Nat.mod_lt lo hs
  have hq : lo % scale + q * scale = lo := by
    simpa only [q, Nat.mul_comm scale] using Nat.mod_add_div lo scale
  have hup : (up + (scale - 1)) / scale ≤ q + (budget + 2) := by
    apply Nat.div_le_of_le_mul
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_comm scale q, Nat.mul_comm scale budget, Nat.mul_comm scale 2]
    omega
  exact Nat.sub_le_iff_le_add.mpr (hup.trans_eq (Nat.add_comm _ _))

/-- Registers 43 and 44 enclose the fallback term at the working scale. -/
theorem initSparsifierFallbackBounds_runs
    {w scale logLo logHi invLo invHi : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {logValue inverse : ℝ}
    (h4 : st.regs 4 = scale) (h33 : st.regs 33 = scale)
    (h34 : st.regs 34 = logLo) (h35 : st.regs 35 = logHi)
    (h36 : st.regs 36 = invLo) (h37 : st.regs 37 = invHi)
    (hs : 0 < scale) (hw : 1 < 2 ^ w)
    (hl : (logLo : ℝ) / scale ≤ logValue) (hu : logValue ≤ (logHi : ℝ) / scale)
    (hil : (invLo : ℝ) / scale ≤ inverse) (hiu : inverse ≤ (invHi : ℝ) / scale)
    (hmLo : 25 * (logLo + scale) < 2 ^ w) (hmHi : 25 * (logHi + scale) < 2 ^ w)
    (hfLo : 25 * (logLo + scale) * invLo < 2 ^ w)
    (hfHi : 25 * (logHi + scale) * invHi + (scale - 1) < 2 ^ w) :
    ∃ out, Runs w p ω initSparsifierFallbackBounds st .normal out 31 ∧
      (out.regs 43 : ℝ) / scale ≤ 25 * (logValue + 1) * inverse ∧
      25 * (logValue + 1) * inverse ≤ (out.regs 44 : ℝ) / scale ∧
      out.regs 44 ≤ (25 * (logHi + scale) * invHi + (scale - 1)) / scale ∧
      (∀ logBound invBound logErr invErr,
        logHi + scale ≤ logBound * scale → invHi ≤ invBound * scale →
        logHi - logLo ≤ logErr → invHi - invLo ≤ invErr →
        out.regs 44 - out.regs 43 ≤ 25 * (logErr * invBound + logBound * invErr) + 2) ∧
      out.mem = st.mem ∧
      (∀ r, r ≠ 31 → r ≠ 32 → r ≠ 43 → r ≠ 44 → out.regs r = st.regs r) := by
  obtain ⟨mid, hrun₁, h31, hval₁, hm₁, hk₁⟩ :=
    initSparsifierFallbackProduct_runs (p := p) (ω := ω) (dest := 31) h4 h34 h36 hs hmLo hfLo
  obtain ⟨ready, hrun₂, h32, hval₂, hm₂, hk₂⟩ :=
    initSparsifierFallbackProduct_runs (p := p) (ω := ω) (dest := 32)
      ((hk₁ 4 (by decide)).trans h4) ((hk₁ 35 (by decide)).trans h35)
      ((hk₁ 37 (by decide)).trans h37) hs hmHi (by omega)
  have hs₀ : 0 < (scale : ℝ) := by exact_mod_cast hs
  obtain ⟨out, hrun₃, hlo, hhi, hgreatest, _, hleast, hm₃, hk₃⟩ :=
    rescaleInitBucketSigmaLogBounds_runs (p := p) (ω := ω) (lower := 43) (upper := 44)
      ((hk₂ 31 (by decide)).trans h31) h32
      ((hk₂ 33 (by decide)).trans ((hk₁ 33 (by decide)).trans h33))
      (by decide) (by decide) (by decide) hs hw hfLo hfHi
  obtain ⟨hbLo, hbHi⟩ := initSparsifierFallback_bounds (by positivity) (by positivity) hl hu hil hiu
  have hcast (n : ℕ) : (n : ℝ) / scale = ((n * scale : ℕ) : ℝ) / (scale : ℝ) ^ 2 := by
    rw [Nat.cast_mul, pow_two, mul_div_mul_right _ _ hs₀.ne']
  have hupper : out.regs 44 ≤ (25 * (logHi + scale) * invHi + (scale - 1)) / scale := by
    apply hleast
    let n := 25 * (logHi + scale) * invHi
    have hm := Nat.mod_lt (n + (scale - 1)) hs
    have he := Nat.mod_add_div (n + (scale - 1)) scale
    rw [Nat.mul_comm scale] at he
    change n ≤ (n + (scale - 1)) / scale * scale
    omega
  refine ⟨out, ?_, ?_, ?_, hupper, ?_, hm₃.trans (hm₂.trans hm₁), ?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨mid, 8, 22, hrun₁,
      runs_seq_iff.mpr (Or.inr ⟨ready, 8, 13, hrun₂, hrun₃, rfl⟩), rfl⟩)
  · rw [hcast]
    rw [← h31] at hlo
    exact (div_le_div_of_nonneg_right (by exact_mod_cast hlo) (by positivity)).trans (hval₁.trans_le hbLo)
  · rw [hcast]
    rw [← h32] at hhi
    exact hbHi.trans (hval₂.symm.trans_le (div_le_div_of_nonneg_right (by exact_mod_cast hhi) (by positivity)))
  · intro logBound invBound logErr invErr hlog hinv hle hie
    have hlogOrder : logLo ≤ logHi := by
      exact_mod_cast (div_le_div_iff_of_pos_right hs₀).mp (hl.trans hu)
    have hinvOrder : invLo ≤ invHi := by
      exact_mod_cast (div_le_div_iff_of_pos_right hs₀).mp (hil.trans hiu)
    have hlower : 25 * (logLo + scale) * invLo / scale ≤ out.regs 43 :=
      hgreatest _ (Nat.div_mul_le_self _ _)
    exact (Nat.sub_le_sub_right hupper _ |>.trans (Nat.sub_le_sub_left hlower _)).trans
      (initSparsifierFallbackProduct_gap hs hlogOrder hinvOrder hlog hinv hle hie)
  · intro r h₁ h₂ h₃ h₄
    exact (hk₃ r h₃ h₄).trans ((hk₂ r h₂).trans (hk₁ r h₁))

/-- The inverse of the effective conductance is a maximum. This lets
the quotient in the path bound use the cited integer length factor
directly. -/
theorem initSparsifierPathInvConductance_eq (Kγ c M : ℕ) (phi : ℝ)
    (hc : 0 < c) (hphi : 0 < phi) :
    1 / Expander.csPhiOut Kγ c phi M =
      max (1 / phi) (max 2 ((c : ℝ) * Cited.csGamma Kγ (3 * M))) := by
  have hgamma : 0 < Cited.csGamma Kγ (3 * M) := by
    unfold Cited.csGamma
    positivity
  have hp : 0 < (c : ℝ) * Cited.csGamma Kγ (3 * M) :=
    mul_pos (by exact_mod_cast hc) (by exact_mod_cast hgamma)
  have hcs : 0 < Cited.csPhi Kγ c (3 * M) := by
    unfold Cited.csPhi
    exact one_div_pos.mpr hp
  have invMin (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
      1 / min a b = max (1 / a) (1 / b) := by
    rcases le_total a b with h | h
    · rw [min_eq_left h, max_eq_left (one_div_le_one_div_of_le ha h)]
    · rw [min_eq_right h, max_eq_right (one_div_le_one_div_of_le hb h)]
  unfold Expander.csPhiOut
  rw [invMin phi _ hphi (lt_min (by norm_num) hcs), invMin _ _ (by norm_num) hcs]
  norm_num [Cited.csPhi, one_div_one_div]

/-- Compute the exact scaled maximum of the two cited terms from the
runtime cited exponent. Register 45 receives the result. -/
@[expose] def initSparsifierInverseCited (c : ℕ) : Stmt :=
  .assign 45 (.bin .mul (.const c) (.bin .shiftLeft (.const 1) (.reg 37))) ;;
  .assign 45 (.bin .mul (.reg 4) (.bin .add (.const 2) (.bin .sub (.reg 45) (.const 2))))

/-- The cited length factor is obtained by shifting one by the exponent
computed for the current graph. -/
theorem initSparsifierInverseCited_runs {w Kγ c M scale : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (h37 : st.regs 37 = Expander.PathDSProg.csGammaExp Kγ (3 * M))
    (h4 : st.regs 4 = scale) (hc : 0 < c) (hs : 0 < scale)
    (hfit : max 2 (c * Cited.csGamma Kγ (3 * M)) * scale < 2 ^ w) :
    ∃ out, Runs w p ω (initSparsifierInverseCited c) st .normal out 15 ∧
      out.regs 45 = max 2 (c * Cited.csGamma Kγ (3 * M)) * scale ∧
      out.mem = st.mem ∧ (∀ r ≠ 45, out.regs r = st.regs r) := by
  let gamma := Cited.csGamma Kγ (3 * M)
  let bound := max 2 (c * gamma)
  have hbound : bound < 2 ^ w := (Nat.le_mul_of_pos_right _ hs).trans_lt hfit
  have hprod : c * gamma < 2 ^ w := (le_max_right ..).trans_lt hbound
  have hg : 0 < gamma := by unfold gamma Cited.csGamma; positivity
  have hgw : gamma < 2 ^ w := (Nat.le_mul_of_pos_left _ hc).trans_lt hprod
  have hcw : c < 2 ^ w := (Nat.le_mul_of_pos_right _ hg).trans_lt hprod
  have htwo : 2 < 2 ^ w := (le_max_left ..).trans_lt hbound
  have hsub : c * gamma - 2 < 2 ^ w := (Nat.sub_le ..).trans_lt hprod
  have hsum : 2 + (c * gamma - 2) = bound := by dsimp [bound]; omega
  have hexp : 2 ^ Expander.PathDSProg.csGammaExp Kγ (3 * M) = gamma := rfl
  let mid := {st with regs := Function.update st.regs 45 (c * gamma)}
  let out := {mid with regs := Function.update mid.regs 45 (bound * scale)}
  have hr₁ : Runs w p ω
      (.assign 45 (.bin .mul (.const c) (.bin .shiftLeft (.const 1) (.reg 37))))
      st .normal mid 6 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, h37, hcw, show 1 < 2 ^ w by omega, Nat.shiftLeft_eq, hexp, hgw, hprod],
      rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω
      (.assign 45 (.bin .mul (.reg 4) (.bin .add (.const 2) (.bin .sub (.reg 45) (.const 2)))))
      mid .normal out 8 :=
    runs_assign_iff.mpr ⟨_, by
      have hmul : bound * scale < 2 ^ w := hfit
      simp [Expr.eval, BinOp.eval, mid, h4, htwo, hsub, hsum, hbound, hmul, Nat.mul_comm scale],
      rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 6, 8, hr₁, hr₂, rfl⟩),
    by simp [out, bound, gamma], rfl, fun r h => by simp [out, mid, h]⟩

/-- Combine the powered and logarithmic path bounds at one endpoint. -/
@[expose] def initSparsifierPathMax (power fallback dest : ℕ) : Stmt :=
  .assign dest (.bin .add (.reg power) (.bin .sub (.reg fallback) (.reg power)))

/-- Taking the word maximum gives the maximum of the represented real
values at their common positive scale. -/
theorem initSparsifierPathMax_runs {w power fallback dest x y scale : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hx : st.regs power = x) (hy : st.regs fallback = y)
    (hs : 0 < (scale : ℝ)) (hfit : max x y < 2 ^ w) :
    ∃ out, Runs w p ω (initSparsifierPathMax power fallback dest) st .normal out 6 ∧
      (out.regs dest : ℝ) / scale = max ((x : ℝ) / scale) ((y : ℝ) / scale) ∧
      out.regs dest = max x y ∧ out.mem = st.mem ∧
      (∀ r ≠ dest, out.regs r = st.regs r) := by
  have hdiff : y - x < 2 ^ w :=
    (Nat.sub_le y x).trans_lt ((le_max_right x y).trans_lt hfit)
  have hsum : x + (y - x) = max x y := by omega
  let out := {st with regs := Function.update st.regs dest (max x y)}
  have hr : Runs w p ω (initSparsifierPathMax power fallback dest) st .normal out 6 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hx, hy, hdiff, hsum, hfit],
      rfl, rfl, rfl⟩
  have he : out.regs dest = max x y := by simp [out]
  refine ⟨out, hr, ?_, he, rfl, fun r h => by simp [out, h]⟩
  rw [he, Nat.cast_max, max_div_div_right hs.le]

/-- Enclose inverse conductance at one endpoint by taking the maximum
of the scaled reciprocal and the exact cited lower-conductance terms. -/
@[expose] def initSparsifierInverseEndpoint (reciprocal dest : ℕ) : Stmt :=
  initSparsifierPathMax reciprocal 45 dest

/-- With register 45 holding the exact scaled maximum of the two cited
terms, the instruction returns the maximum with the reciprocal endpoint. -/
theorem initSparsifierInverseEndpoint_runs {w reciprocal dest x cited : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hx : st.regs reciprocal = x) (hc : st.regs 45 = cited)
    (hfit : max x cited < 2 ^ w) :
    ∃ out, Runs w p ω (initSparsifierInverseEndpoint reciprocal dest) st .normal out 6 ∧
      out.regs dest = max x cited ∧ out.mem = st.mem ∧
      (∀ r ≠ dest, out.regs r = st.regs r) := by
  obtain ⟨out, hr, _, he, hm, hk⟩ :=
    initSparsifierPathMax_runs (p := p) (ω := ω) (scale := 1) hx hc (by norm_num) hfit
  exact ⟨out, hr, he, hm, hk⟩

/-- The two scaled maxima enclose the inverse of the effective
conductance when the scaled reciprocals enclose the input reciprocal. -/
theorem initSparsifierInverseEndpoints_bounds (Kγ c M scale lo hi : ℕ) (phi : ℝ)
    (hc : 0 < c) (hp : 0 < phi) (hs : 0 < (scale : ℝ))
    (hlo : (lo : ℝ) / scale ≤ 1 / phi) (hhi : 1 / phi ≤ (hi : ℝ) / scale) :
    let cited := max 2 (c * Cited.csGamma Kγ (3 * M)) * scale
    (max lo cited : ℕ) / (scale : ℝ) ≤ 1 / Expander.csPhiOut Kγ c phi M ∧
      1 / Expander.csPhiOut Kγ c phi M ≤ (max hi cited : ℕ) / (scale : ℝ) := by
  dsimp only
  rw [initSparsifierPathInvConductance_eq Kγ c M phi hc hp]
  have hmax (n : ℕ) :
      (↑(max n (max 2 (c * Cited.csGamma Kγ (3 * M)) * scale)) : ℝ) / scale =
        max ((n : ℝ) / scale) (max 2 ((c : ℝ) * Cited.csGamma Kγ (3 * M))) := by
    rw [Nat.cast_max, ← max_div_div_right hs.le, Nat.cast_mul, mul_div_cancel_right₀ _ hs.ne']
    simp only [Nat.cast_max, Nat.cast_ofNat, Nat.cast_mul]
  rw [hmax lo, hmax hi]
  exact ⟨max_le_max hlo le_rfl, max_le_max hhi le_rfl⟩

/-- A lower bound on conductance controls the increase in width when
taking the reciprocal and rounding the two endpoints outward. -/
theorem initSparsifierReciprocal_gap
    {scale logLo logHi invBound : ℕ}
    (hpos : 0 < scale) (hh : scale ≤ invBound * logLo) (hle : logLo ≤ logHi) :
    (scale * scale + (logLo - 1)) / logLo - scale * scale / logHi ≤
      invBound ^ 2 * (logHi - logLo) + 2 := by
  let n := scale * scale
  have hLo : 0 < logLo := by
    by_contra! hz
    have he : logLo = 0 := Nat.eq_zero_of_le_zero hz
    simp [he, hpos.not_ge] at hh
  have hHi : 0 < logHi := hLo.trans_le hle
  have hl : (0 : ℝ) < logLo := by exact_mod_cast hLo
  have hu : (0 : ℝ) < logHi := by exact_mod_cast hHi
  have hlower : (n : ℝ) / logHi ≤ ((n / logHi : ℕ) : ℝ) + 1 := by
    apply (div_le_iff₀ hu).mpr
    have hlt : n < (n / logHi + 1) * logHi := by
      rw [Nat.add_mul, Nat.one_mul]
      have hmod := Nat.mod_lt n hHi
      have heq := Nat.mod_add_div n logHi
      rw [Nat.mul_comm logHi] at heq
      omega
    exact_mod_cast hlt.le
  have hupper : (((n + (logLo - 1)) / logLo : ℕ) : ℝ) ≤ (n : ℝ) / logLo + 1 := by
    apply Nat.cast_div_le.trans
    apply (div_le_iff₀ hl).mpr
    have hsub : ((logLo - 1 : ℕ) : ℝ) ≤ logLo := by exact_mod_cast Nat.sub_le logLo 1
    rw [Nat.cast_add, add_mul, div_mul_cancel₀ _ hl.ne', one_mul]
    exact add_le_add_right hsub _
  have hprod : (scale : ℝ) * scale ≤ (invBound : ℝ) ^ 2 * ((logLo : ℝ) * logHi) := by
    have hl₂ : (scale : ℝ) ≤ invBound * logLo := by exact_mod_cast hh
    have hu₂ : (scale : ℝ) ≤ invBound * logHi := by exact_mod_cast hh.trans (Nat.mul_le_mul_left invBound hle)
    calc
      _ ≤ ((invBound : ℝ) * logLo) * (invBound * logHi) :=
        mul_le_mul hl₂ hu₂ (Nat.cast_nonneg _) (by positivity)
      _ = _ := by ring
  have hgap : (n : ℝ) / logLo - (n : ℝ) / logHi ≤
      (invBound : ℝ) ^ 2 * (logHi - logLo : ℝ) := by
    rw [div_sub_div _ _ hl.ne' hu.ne']
    apply (div_le_iff₀ (mul_pos hl hu)).mpr
    have hnonneg : 0 ≤ (logHi : ℝ) - logLo := sub_nonneg.mpr (by exact_mod_cast hle)
    have hmul := mul_le_mul_of_nonneg_right hprod hnonneg
    push_cast [n]
    linarith only [show (scale : ℝ) * scale * (logHi - logLo : ℝ) ≤
      (invBound : ℝ) ^ 2 * ((logLo : ℝ) * logHi) * (logHi - logLo : ℝ) from hmul]
  have hfinal : (n + (logLo - 1)) / logLo ≤ n / logHi + (invBound ^ 2 * (logHi - logLo) + 2) := by
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast [Nat.cast_sub hle]
    linarith only [hupper, hlower, hgap]
  exact Nat.sub_le_iff_le_add.mpr (by simpa [n, Nat.add_comm] using hfinal)

/-- Floor and ceiling division of the squared scale enclose the
reciprocal of a positive conductance interval. The upper conductance
gives the lower reciprocal. -/
theorem initSparsifierReciprocal_bounds (scale lo hi : ℕ) (phi : ℝ)
    (hs : 0 < scale) (hl : 0 < lo)
    (hlo : (lo : ℝ) / scale ≤ phi) (hhi : phi ≤ (hi : ℝ) / scale) :
    ((scale * scale / hi : ℕ) : ℝ) / scale ≤ 1 / phi ∧
      1 / phi ≤ (((scale * scale + (lo - 1)) / lo : ℕ) : ℝ) / scale := by
  have hs' : (0 : ℝ) < scale := by exact_mod_cast hs
  have hl' : (0 : ℝ) < lo := by exact_mod_cast hl
  have hphi := (div_pos hl' hs').trans_le hlo
  have hhi' := hphi.trans_le hhi
  have hh' : (0 : ℝ) < hi := (div_pos_iff_of_pos_right hs').mp hhi'
  have hroundLo : ((scale * scale / hi : ℕ) : ℝ) * hi ≤ (scale : ℝ) * scale := by
    exact_mod_cast Nat.div_mul_le_self (scale * scale) hi
  let roundHi := (scale * scale + (lo - 1)) / lo
  have hroundHi : scale * scale ≤ roundHi * lo := by
    have hmod := Nat.mod_lt (scale * scale + (lo - 1)) hl
    have hsum := Nat.mod_add_div (scale * scale + (lo - 1)) lo
    rw [Nat.mul_comm lo] at hsum
    change (scale * scale + (lo - 1)) % lo + roundHi * lo = scale * scale + (lo - 1) at hsum
    omega
  have hroundHi' : (scale : ℝ) * scale ≤ (roundHi : ℝ) * lo := by exact_mod_cast hroundHi
  have hlo' : ((scale * scale / hi : ℕ) : ℝ) / scale ≤ 1 / ((hi : ℝ) / scale) := by
    rw [one_div_div]
    exact (div_le_div_iff₀ hs' hh').mpr hroundLo
  have hup' : 1 / ((lo : ℝ) / scale) ≤ (roundHi : ℝ) / scale := by
    rw [one_div_div]
    exact (div_le_div_iff₀ hl' hs').mpr hroundHi'
  exact ⟨hlo'.trans (one_div_le_one_div_of_le hphi hhi),
    (one_div_le_one_div_of_le (div_pos hl' hs') hlo).trans hup'⟩

/-- Form the reciprocal endpoints in registers 46 and 47. Registers
31 and 32 hold the conductance interval at the scale in register 4. -/
@[expose] def initSparsifierReciprocal : Stmt :=
  .assign 45 (.bin .mul (.reg 4) (.reg 4)) ;;
  .assign 46 (.bin .div (.reg 45) (.reg 32)) ;;
  .assign 47 (.bin .div (.bin .add (.reg 45) (.bin .sub (.reg 31) (.const 1))) (.reg 31))

/-- The word divisions give an outward enclosure of the reciprocal. -/
theorem initSparsifierReciprocal_runs {w scale lo hi : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {phi : ℝ}
    (h4 : st.regs 4 = scale) (h31 : st.regs 31 = lo) (h32 : st.regs 32 = hi)
    (hs : 0 < scale) (hl : 0 < lo)
    (hlo : (lo : ℝ) / scale ≤ phi) (hhi : phi ≤ (hi : ℝ) / scale)
    (hfit : scale * scale + (lo - 1) < 2 ^ w) :
    ∃ out, Runs w p ω initSparsifierReciprocal st .normal out 18 ∧
      (out.regs 46 : ℝ) / scale ≤ 1 / phi ∧ 1 / phi ≤ (out.regs 47 : ℝ) / scale ∧
      out.regs 46 = scale * scale / hi ∧
      out.regs 47 = (scale * scale + (lo - 1)) / lo ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 45 → r ≠ 46 → r ≠ 47 → out.regs r = st.regs r) := by
  let sq := scale * scale
  let lb := sq / hi
  let ub := (sq + (lo - 1)) / lo
  have hsq : sq < 2 ^ w := by dsimp [sq]; omega
  have hlb : lb < 2 ^ w := (Nat.div_le_self ..).trans_lt hsq
  have hub : ub < 2 ^ w := (Nat.div_le_self ..).trans_lt hfit
  have hone : 1 < 2 ^ w := by
    have hp := Nat.mul_pos hs hs
    omega
  have hsub : lo - 1 < 2 ^ w := by omega
  let mid := {st with regs := Function.update st.regs 45 sq}
  let ready := {mid with regs := Function.update mid.regs 46 lb}
  let out := {ready with regs := Function.update ready.regs 47 ub}
  have hr₁ : Runs w p ω (.assign 45 (.bin .mul (.reg 4) (.reg 4))) st .normal mid 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, h4, sq, show scale * scale < 2 ^ w from hsq], rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign 46 (.bin .div (.reg 45) (.reg 32))) mid .normal ready 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, mid, h32, lb, show sq / hi < 2 ^ w from hlb], rfl, rfl, rfl⟩
  have hr₃ : Runs w p ω
      (.assign 47 (.bin .div (.bin .add (.reg 45) (.bin .sub (.reg 31) (.const 1))) (.reg 31)))
      ready .normal out 8 :=
    runs_assign_iff.mpr ⟨_, by
      have hf : sq + (lo - 1) < 2 ^ w := hfit
      simp [Expr.eval, BinOp.eval, ready, mid, h31, hone, hsub, hf, ub, show (sq + (lo - 1)) / lo < 2 ^ w from hub],
      rfl, rfl, rfl⟩
  have he₁ : out.regs 46 = lb := by simp [out, ready]
  have he₂ : out.regs 47 = ub := by simp [out]
  obtain ⟨hrecLo, hrecHi⟩ := initSparsifierReciprocal_bounds scale lo hi phi hs hl hlo hhi
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 4, 13, hr₁,
    runs_seq_iff.mpr (Or.inr ⟨ready, 4, 8, hr₂, hr₃, rfl⟩), rfl⟩),
    he₁.symm ▸ hrecLo, he₂.symm ▸ hrecHi, he₁, he₂, rfl,
    fun r h45 h46 h47 => by simp [out, ready, mid, h45, h46, h47]⟩

/-- Form both inverse conductance bounds from reciprocal endpoints in
registers 46 and 47. Register 37 may be reused after reading the exponent. -/
@[expose] def initSparsifierInverseBounds (c : ℕ) : Stmt :=
  initSparsifierInverseCited c ;;
  initSparsifierInverseEndpoint 46 36 ;;
  initSparsifierInverseEndpoint 47 37

/-- Registers 36 and 37 enclose the inverse effective conductance at
the working scale, ready for the fallback products. -/
theorem initSparsifierInverseBounds_runs {w Kγ c M scale lo hi : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {phi : ℝ}
    (h37 : st.regs 37 = Expander.PathDSProg.csGammaExp Kγ (3 * M))
    (h4 : st.regs 4 = scale) (h46 : st.regs 46 = lo) (h47 : st.regs 47 = hi)
    (hc : 0 < c) (hs : 0 < scale) (hp : 0 < phi)
    (hlo : (lo : ℝ) / scale ≤ 1 / phi) (hhi : 1 / phi ≤ (hi : ℝ) / scale)
    (hfit : max (max lo hi) (max 2 (c * Cited.csGamma Kγ (3 * M)) * scale) < 2 ^ w) :
    ∃ out, Runs w p ω (initSparsifierInverseBounds c) st .normal out 29 ∧
      (out.regs 36 : ℝ) / scale ≤ 1 / Expander.csPhiOut Kγ c phi M ∧
      1 / Expander.csPhiOut Kγ c phi M ≤ (out.regs 37 : ℝ) / scale ∧
      out.regs 36 = max lo (max 2 (c * Cited.csGamma Kγ (3 * M)) * scale) ∧
      out.regs 37 = max hi (max 2 (c * Cited.csGamma Kγ (3 * M)) * scale) ∧
      out.mem = st.mem ∧
      (∀ r, r ≠ 36 → r ≠ 37 → r ≠ 45 → out.regs r = st.regs r) := by
  let cited := max 2 (c * Cited.csGamma Kγ (3 * M)) * scale
  have hcf : cited < 2 ^ w := (le_max_right ..).trans_lt hfit
  have hlf : max lo cited < 2 ^ w :=
    (max_le_max (le_max_left lo hi) le_rfl).trans_lt hfit
  have hhf : max hi cited < 2 ^ w :=
    (max_le_max (le_max_right lo hi) le_rfl).trans_lt hfit
  obtain ⟨mid, hr₁, h45, hm₁, hk₁⟩ :=
    initSparsifierInverseCited_runs (p := p) (ω := ω) h37 h4 hc hs hcf
  obtain ⟨ready, hr₂, h36, hm₂, hk₂⟩ :=
    initSparsifierInverseEndpoint_runs (p := p) (ω := ω) (dest := 36)
      ((hk₁ 46 (by decide)).trans h46) h45 hlf
  obtain ⟨out, hr₃, h37', hm₃, hk₃⟩ :=
    initSparsifierInverseEndpoint_runs (p := p) (ω := ω) (dest := 37)
      ((hk₂ 47 (by decide)).trans ((hk₁ 47 (by decide)).trans h47))
      ((hk₂ 45 (by decide)).trans h45) hhf
  obtain ⟨hl, hu⟩ := initSparsifierInverseEndpoints_bounds Kγ c M scale lo hi phi hc hp
    (by exact_mod_cast hs) hlo hhi
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 15, 13, hr₁,
    runs_seq_iff.mpr (Or.inr ⟨ready, 6, 6, hr₂, hr₃, rfl⟩), rfl⟩),
    ((hk₃ 36 (by decide)).trans h36).symm ▸ hl, h37'.symm ▸ hu,
    (hk₃ 36 (by decide)).trans h36, h37', hm₃.trans (hm₂.trans hm₁), fun r h36 h37 h45 =>
      (hk₃ r h37).trans ((hk₂ r h36).trans (hk₁ r h45))⟩

end MinCostFlow.MinRatio
