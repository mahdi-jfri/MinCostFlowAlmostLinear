module

public import MinCostFlow.MinRatio.InitThresholdCached
public import MinCostFlow.MinRatio.InitStretch
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Integer threshold initialization from a dyadic growth bound

The initializer reduces the precision of an upper growth bound before
computing the table. Upward rounding uses half the permitted error.
-/

public section
namespace MinCostFlow.MinRatio

open WordRAM Chain

/-- Compute the coarse divisor, round the upper endpoint and fill the
rebuild threshold table of Algorithm 2 (page 28). -/
@[expose] def initDyadicIntegerThresholdTable (clog : ℕ) : Stmt :=
  prepareIntegerGrowthDivisor clog ;; initRoundedIntegerThresholdTable

/-- An integer bound on the endpoint gap implies the upper error
bound needed by the dyadic threshold initializer. -/
theorem dyadicGrowthUpper_le_of_gap {lower upper scale precision : ℕ} {γ : ℝ}
    (hs : 0 < scale) (horder : lower ≤ upper)
    (hlower : (lower : ℝ) / ((2 ^ precision : ℕ) : ℝ) ≤ γ)
    (hgap : (upper - lower) * scale ≤ 2 ^ precision) :
    (upper : ℝ) / ((2 ^ precision : ℕ) : ℝ) ≤ γ + 1 / scale := by
  let Q := (2 ^ precision : ℕ)
  have hQ : (0 : ℝ) < Q := Nat.cast_pos.mpr (Nat.two_pow_pos _)
  have hs' : (0 : ℝ) < scale := Nat.cast_pos.mpr hs
  have hcast : ((upper : ℝ) - (lower : ℝ)) * (scale : ℝ) ≤ (Q : ℝ) := by
    have h : ((upper - lower : ℕ) : ℝ) * (scale : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hgap
    rwa [Nat.cast_sub horder] at h
  have hwidth : ((upper : ℝ) - (lower : ℝ)) / (Q : ℝ) ≤ 1 / (scale : ℝ) :=
    (div_le_div_iff₀ hQ hs').mpr (by simpa only [one_mul] using hcast)
  rw [sub_div] at hwidth
  linarith only [hlower, hwidth]

/-- The two growth terms may exchange order across the enclosure.
Bounding both integer gaps bounds the gap between their maxima. -/
theorem maxGrowthEndpoint_gap_le {firstLo firstHi secondLo secondHi scale common : ℕ}
    (hfirst : (firstHi - firstLo) * scale ≤ common)
    (hsecond : (secondHi - secondLo) * scale ≤ common) :
    (max firstHi secondHi - max firstLo secondLo) * scale ≤ common := by
  rcases le_total firstHi secondHi with h | h
  · rw [max_eq_right h]
    exact (Nat.mul_le_mul_right scale (Nat.sub_le_sub_left (le_max_right _ _) _)).trans hsecond
  · rw [max_eq_left h]
    exact (Nat.mul_le_mul_right scale (Nat.sub_le_sub_left (le_max_left _ _) _)).trans hfirst

/-- The powered growth term amplifies the endpoint gap by at most the
power times the upper endpoint to one lower power. -/
theorem poweredGrowthEndpoint_gap_le {lo hi : ℕ} (h : lo ≤ hi) (n : ℕ) :
    hi ^ n - lo ^ n ≤ (hi - lo) * n * hi ^ (n - 1) := by
  have hp : lo ^ n ≤ hi ^ n := Nat.pow_le_pow_left h n
  have h' : (lo : ℤ) ≤ hi := by exact_mod_cast h
  have hpow : (lo : ℤ) ^ n ≤ (hi : ℤ) ^ n := by exact_mod_cast hp
  have hgap := abs_pow_sub_pow_le (a := (hi : ℤ)) (b := (lo : ℤ)) (n := n)
  rw [abs_of_nonneg (sub_nonneg.mpr hpow), abs_of_nonneg (sub_nonneg.mpr h'),
    abs_of_nonneg (Int.natCast_nonneg hi), abs_of_nonneg (Int.natCast_nonneg lo),
    max_eq_left h'] at hgap
  exact_mod_cast hgap

/-- The second growth term is a product of three quantities. Charge
its gap by changing one endpoint at a time. -/
theorem productGrowthEndpoint_gap {kl ku sl su ll lu : ℕ}
    (hk : kl ≤ ku) (hs : sl ≤ su) (hl : ll ≤ lu) :
    ku * su * lu - kl * sl * ll =
      (ku - kl) * su * lu + kl * (su - sl) * lu + kl * sl * (lu - ll) := by
  have hp : kl * sl * ll ≤ ku * su * lu := Nat.mul_le_mul (Nat.mul_le_mul hk hs) hl
  apply Int.ofNat_inj.mp
  push_cast [Nat.cast_sub hp, Nat.cast_sub hk, Nat.cast_sub hs, Nat.cast_sub hl]
  ring

/-- Bounds on the component errors suffice for the integer gap of
the two terms assembled for the sparse-core growth factor. -/
theorem assembledGrowthEndpoint_gap_le
    {factor cap scale coarse exponent n kl ku sl su ll lu : ℕ}
    (hk : kl ≤ ku) (hs : sl ≤ su) (hl : ll ≤ lu)
    (hfirst : factor * ((su - sl) * n * su ^ (n - 1)) * coarse ≤ scale ^ exponent)
    (hsecond : 11 * cap * ((ku - kl) * su * lu + kl * (su - sl) * lu +
      kl * sl * (lu - ll)) * scale ^ (exponent - 3) * coarse ≤ scale ^ exponent) :
    let first := fun s : ℕ => factor * s ^ n
    let second := fun k s l : ℕ =>
      11 * (cap * k * s * l + 115 * scale ^ 3) * scale ^ (exponent - 3)
    (first su - first sl) * coarse ≤ scale ^ exponent ∧
      (second ku su lu - second kl sl ll) * coarse ≤ scale ^ exponent := by
  dsimp only
  constructor
  · rw [← Nat.mul_sub]
    exact (Nat.mul_le_mul_right coarse
      (Nat.mul_le_mul_left factor (poweredGrowthEndpoint_gap_le hs n))).trans hfirst
  · have he (k s l : ℕ) : 11 * (cap * k * s * l + 115 * scale ^ 3) * scale ^ (exponent - 3) =
        (11 * cap) * (k * s * l) * scale ^ (exponent - 3) +
          11 * (115 * scale ^ 3) * scale ^ (exponent - 3) := by ring
    rw [he, he, Nat.add_sub_add_right, ← Nat.sub_mul, ← Nat.mul_sub,
      productGrowthEndpoint_gap hk hs hl]
    exact hsecond

/-- A common error and size bound for the three input factors gives
sufficient bounds on both assembled growth terms. -/
theorem assembledGrowthEndpoint_gap_of_uniform
    {factor cap scale coarse exponent n kl ku sl su ll lu err bound : ℕ}
    (hk : kl ≤ ku) (hs : sl ≤ su) (hl : ll ≤ lu)
    (hku : ku ≤ bound) (hsu : su ≤ bound) (hlu : lu ≤ bound)
    (hke : ku - kl ≤ err) (hse : su - sl ≤ err) (hle : lu - ll ≤ err)
    (hfirst : factor * (err * n * bound ^ (n - 1)) * coarse ≤ scale ^ exponent)
    (hsecond : 11 * cap * (3 * (err * bound ^ 2)) * scale ^ (exponent - 3) * coarse ≤
      scale ^ exponent) :
    let first := fun s : ℕ => factor * s ^ n
    let second := fun k s l : ℕ =>
      11 * (cap * k * s * l + 115 * scale ^ 3) * scale ^ (exponent - 3)
    (first su - first sl) * coarse ≤ scale ^ exponent ∧
      (second ku su lu - second kl sl ll) * coarse ≤ scale ^ exponent := by
  apply assembledGrowthEndpoint_gap_le hk hs hl
  · exact (Nat.mul_le_mul_right coarse (Nat.mul_le_mul_left factor
      (Nat.mul_le_mul (Nat.mul_le_mul_right n hse) (Nat.pow_le_pow_left hsu _)))).trans hfirst
  · have h₁ : (ku - kl) * su * lu ≤ err * bound ^ 2 := by
      rw [pow_two, ← Nat.mul_assoc]
      exact Nat.mul_le_mul (Nat.mul_le_mul hke hsu) hlu
    have h₂ : kl * (su - sl) * lu ≤ err * bound ^ 2 := by
      rw [Nat.mul_comm kl, pow_two, ← Nat.mul_assoc]
      exact Nat.mul_le_mul (Nat.mul_le_mul hse (hk.trans hku)) hlu
    have h₃ : kl * sl * (lu - ll) ≤ err * bound ^ 2 := by
      rw [Nat.mul_comm (kl * sl), pow_two]
      exact Nat.mul_le_mul hle (Nat.mul_le_mul (hk.trans hku) (hs.trans hsu))
    have hsum := Nat.add_le_add (Nat.add_le_add h₁ h₂) h₃
    have he : err * bound ^ 2 + err * bound ^ 2 + err * bound ^ 2 = 3 * (err * bound ^ 2) := by ring
    rw [he] at hsum
    exact (Nat.mul_le_mul_right coarse (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hsum))).trans hsecond

/-- Binary precision sufficient for the two stretch term errors and
for rounding to the threshold scale. -/
@[expose] def growthWorkingBits (L cap coarse err bound : ℕ) : ℕ :=
  Nat.clog 2 (max coarse (max
    (3 ^ L * (err * (L + 1) * bound ^ L) * coarse)
    (33 * cap * (err * bound ^ 2) * coarse)))

theorem growthWorkingBits_bounds (L cap coarse err bound : ℕ) :
    let work := 2 ^ growthWorkingBits L cap coarse err bound
    coarse ≤ work ∧ 3 ^ L * (err * (L + 1) * bound ^ L) * coarse ≤ work ∧
      33 * cap * (err * bound ^ 2) * coarse ≤ work := by
  dsimp only [growthWorkingBits]
  let a := 3 ^ L * (err * (L + 1) * bound ^ L) * coarse
  let b := 33 * cap * (err * bound ^ 2) * coarse
  have h := Nat.le_pow_clog Nat.one_lt_two (max coarse (max a b))
  exact ⟨(le_max_left _ _).trans h,
    (le_max_left a b).trans ((le_max_right _ _).trans h),
    (le_max_right a b).trans ((le_max_right _ _).trans h)⟩

/-- The working precision grows linearly with the sparsifier depth times
the bit width of the factor bound. The capacity and error contribute
only their bit widths. -/
theorem growthWorkingBits_le (L cap coarse err bound : ℕ) :
    growthWorkingBits L cap coarse err bound ≤
      Nat.clog 2 coarse + Nat.clog 2 err +
        max (2 * L + Nat.clog 2 (L + 1) + L * Nat.clog 2 bound)
          (6 + Nat.clog 2 cap + 2 * Nat.clog 2 bound) := by
  let c := Nat.clog 2 coarse
  let e := Nat.clog 2 err
  let b := Nat.clog 2 bound
  let a := 2 * L + Nat.clog 2 (L + 1) + L * b
  let d := 6 + Nat.clog 2 cap + 2 * b
  have hc : coarse ≤ 2 ^ c := Nat.le_pow_clog Nat.one_lt_two _
  have he : err ≤ 2 ^ e := Nat.le_pow_clog Nat.one_lt_two _
  have hb : bound ≤ 2 ^ b := Nat.le_pow_clog Nat.one_lt_two _
  have hfirst : 3 ^ L * (err * (L + 1) * bound ^ L) * coarse ≤ 2 ^ (c + e + a) := by
    calc
      _ ≤ (2 ^ 2) ^ L * (2 ^ e * 2 ^ Nat.clog 2 (L + 1) * (2 ^ b) ^ L) * 2 ^ c :=
        Nat.mul_le_mul
          (Nat.mul_le_mul (Nat.pow_le_pow_left (by decide) _)
            (Nat.mul_le_mul (Nat.mul_le_mul he (Nat.le_pow_clog Nat.one_lt_two _))
              (Nat.pow_le_pow_left hb _))) hc
      _ = _ := by
        simp only [← pow_mul, ← pow_add]
        congr 1
        dsimp [a]
        rw [Nat.mul_comm b L]
        omega
  have hsecond : 33 * cap * (err * bound ^ 2) * coarse ≤ 2 ^ (c + e + d) := by
    calc
      _ ≤ 2 ^ 6 * 2 ^ Nat.clog 2 cap * (2 ^ e * (2 ^ b) ^ 2) * 2 ^ c :=
        Nat.mul_le_mul
          (Nat.mul_le_mul (Nat.mul_le_mul (by decide) (Nat.le_pow_clog Nat.one_lt_two _))
            (Nat.mul_le_mul he (Nat.pow_le_pow_left hb _))) hc
      _ = _ := by
        simp only [← pow_mul, ← pow_add]
        congr 1
        dsimp [d]
        omega
  apply Nat.clog_le_of_le_pow
  exact max_le (hc.trans (Nat.pow_le_pow_right (by decide) (by omega)))
    (max_le (hfirst.trans (Nat.pow_le_pow_right (by decide)
      (Nat.add_le_add_left (le_max_left a d) (c + e))))
      (hsecond.trans (Nat.pow_le_pow_right (by decide)
        (Nat.add_le_add_left (le_max_right a d) (c + e)))))

/-- Materialize the coarse threshold scale from the chain depth in
register 75. The choice leaves room for upward rounding of the growth factor. -/
@[expose] def prepareGrowthCoarseScale (clog : ℕ) : Stmt :=
  .call 30 clog [.bin .mul (.const 2) (.bin .add (.reg 75) (.const 1))] ;;
  .assign 30 (.bin .shiftLeft (.const 1) (.reg 30))

/-- Init computes the coarse threshold scale with one ceiling logarithm. -/
theorem prepareGrowthCoarseScale_runs
    {w clog depth : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hp : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (h75 : st.regs 75 = depth) (hfit : 2 * (depth + 1) + 1 < 2 ^ w)
    (hscale : concreteThresholdScale depth < 2 ^ w) :
    ∃ out cost, Runs w p ω (prepareGrowthCoarseScale clog) st .normal out cost ∧
      out.regs 30 = concreteThresholdScale depth ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 30 → out.regs r = st.regs r) ∧
      cost ≤ 40 * Nat.clog 2 (2 * (depth + 1)) + 31 := by
  let n := 2 * (depth + 1)
  have htwo : 2 < 2 ^ w := by omega
  have hargs : evalArgs w st [.bin .mul (.const 2) (.bin .add (.reg 75) (.const 1))] =
      some [n] := by
    simp [evalArgs, Expr.eval, BinOp.eval, h75, htwo, show 1 < 2 ^ w by omega,
      show depth + 1 < 2 ^ w by omega, show 2 * (depth + 1) < 2 ^ w by omega, n]
  obtain ⟨mid, c, v, hr, ⟨hm, hval⟩, h30, hf, hcost⟩ :=
    runs_call_of_meetsContract (r := 30) (Scaling.Machine.clogTwo_meetsContract hp n)
      hargs (by simp; omega) ⟨rfl, hfit, htwo⟩ ω
  let out := {mid with regs := Function.update mid.regs 30 (concreteThresholdScale depth)}
  have hr' : Runs w p ω (.assign 30 (.bin .shiftLeft (.const 1) (.reg 30)))
      mid .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, h30.trans hval, Nat.shiftLeft_eq,
        show 1 < 2 ^ w by omega, show 2 ^ Nat.clog 2 n < 2 ^ w from hscale,
        concreteThresholdScale, n], rfl, rfl, rfl⟩
  refine ⟨out, c + 5, runs_seq_iff.mpr (Or.inr ⟨mid, c, 4, hr, hr', rfl⟩),
    by simp [out], hm, ?_, ?_⟩
  · intro r hne
    simpa [out, hne] using hf r hne
  · simp [Scaling.Machine.clogTwoContract, argsSize, Expr.size, n] at hcost
    omega

/-- Raise three times the factor bound to the runtime depth. The loop
uses registers 27 and 28 and leaves the power in register 29. -/
@[expose] def prepareGrowthScalePower : Stmt :=
  .assign 27 (.bin .mul (.const 3) (.reg 36)) ;;
  .assign 29 (.const 1) ;;
  forRange 28 (.const 0) (.reg 44) (.assign 29 (.bin .mul (.reg 29) (.reg 27)))

/-- Every partial power fits when the final power fits and the factor bound
is positive. The arithmetic takes linear time in the runtime depth. -/
theorem prepareGrowthScalePower_runs
    {w L bound : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (h36 : st.regs 36 = bound) (h44 : st.regs 44 = L) (hb : 0 < bound)
    (hword : 3 < 2 ^ w) (hbase : 3 * bound < 2 ^ w)
    (hdepth : L < 2 ^ w) (hpow : (3 * bound) ^ L < 2 ^ w) :
    ∃ out cost, Runs w p ω prepareGrowthScalePower st .normal out cost ∧
      out.regs 29 = (3 * bound) ^ L ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 27 → r ≠ 28 → r ≠ 29 → out.regs r = st.regs r) ∧
      cost ≤ 13 * L + 15 := by
  let base := 3 * bound
  have hbasePos : 1 ≤ base := Nat.mul_pos (by decide) hb
  let mid := {st with regs := Function.update st.regs 27 base}
  let start := {mid with regs := Function.update mid.regs 29 1}
  have r₁ : Runs w p ω (.assign 27 (.bin .mul (.const 3) (.reg 36))) st .normal mid 4 :=
    runs_assign_iff.mpr ⟨base, by simp [Expr.eval, BinOp.eval, h36, hword, hbase, base],
      rfl, rfl, rfl⟩
  have r₂ : Runs w p ω (.assign 29 (.const 1)) mid .normal start 2 :=
    runs_assign_iff.mpr ⟨1, by simp [Expr.eval, show 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
  let Inv (i : ℕ) (s : State) :=
    s.regs 28 = i ∧ s.regs 29 = base ^ i ∧ s.regs 27 = base ∧
      s.mem = st.mem ∧ (∀ r, r ≠ 27 → r ≠ 28 → r ≠ 29 → s.regs r = st.regs r)
  have hloop := Triple.forRange_const (p := p) (P := fun s => s = start) (r := 28)
    (lo := .const 0) (hi := .reg 44) (body := .assign 29 (.bin .mul (.reg 29) (.reg 27)))
    (Inv := Inv) 4 0 L (Nat.zero_le _) (show 1 < 2 ^ w by omega) (fun _ => hdepth)
    (by
      intro s hs
      subst s
      simp [Expr.eval, Inv, start, mid]
      intro r h27 h28 h29
      simp [h27, h28, h29])
    (fun _ _ _ _ h => h.1)
    (by
      intro _ _ _ _ h
      simp [Expr.eval, (h.2.2.2.2 44 (by decide) (by decide) (by decide)).trans h44])
    (by
      intro i _ hi s tape hs
      obtain ⟨hiReg, hp, hbReg, hm, hf⟩ := hs
      have hfit : base ^ i * base < 2 ^ w := by
        rw [← pow_succ]
        exact (Nat.pow_le_pow_right hbasePos hi).trans_lt hpow
      let out := {s with regs := Function.update s.regs 29 (base ^ (i + 1))}
      have hr : Runs w p tape (.assign 29 (.bin .mul (.reg 29) (.reg 27))) s .normal out 4 :=
        runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hp, hbReg, hfit, pow_succ],
          rfl, rfl, rfl⟩
      refine ⟨.normal, out, 4, hr, ⟨?_, ?_⟩, le_rfl⟩
      · simp [Inv, out, hm, hbReg]
        intro r h27 h28 h29
        simpa [h28, h29] using hf r h27 h28 h29
      · simpa [out] using hiReg)
  obtain ⟨o, out, cost, hr, hout, hcost⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hout
  | normal =>
    obtain ⟨_, hp, _, hm, hf⟩ := hout
    have hc : cost ≤ L * 13 + 7 := by simpa using hcost
    refine ⟨out, cost + 8, ?_, hp, hm, hf, by omega⟩
    refine runs_seq_iff.mpr (Or.inr ⟨mid, 4, cost + 3, r₁, ?_, by omega⟩)
    exact runs_seq_iff.mpr (Or.inr ⟨start, 2, cost, r₂, hr, by omega⟩)

/-- Form the two scale requirements from the runtime depth, cap, error,
and factor bound. Register 29 holds the power of three times the factor bound. -/
@[expose] def prepareGrowthScaleCoefficients : Stmt :=
  .assign 31 (.bin .mul
    (.bin .mul (.bin .mul (.reg 29) (.reg 35)) (.bin .add (.reg 44) (.const 1))) (.reg 30)) ;;
  .assign 32 (.bin .mul
    (.bin .mul (.bin .mul (.bin .mul (.const 33) (.reg 34)) (.reg 35))
      (.bin .mul (.reg 36) (.reg 36))) (.reg 30))

/-- Positive factors make every intermediate product no larger than
the corresponding final scale requirement. -/
theorem prepareGrowthScaleCoefficients_runs
    {w L cap coarse err bound : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (h29 : st.regs 29 = (3 * bound) ^ L) (h30 : st.regs 30 = coarse)
    (h34 : st.regs 34 = cap) (h35 : st.regs 35 = err)
    (h36 : st.regs 36 = bound) (h44 : st.regs 44 = L)
    (hp : 0 < cap) (hc : 0 < coarse) (he : 0 < err) (hb : 0 < bound)
    (hf : 3 ^ L * (err * (L + 1) * bound ^ L) * coarse < 2 ^ w)
    (hs : 33 * cap * (err * bound ^ 2) * coarse < 2 ^ w) :
    ∃ out, Runs w p ω prepareGrowthScaleCoefficients st .normal out 23 ∧
      out.regs 31 = 3 ^ L * (err * (L + 1) * bound ^ L) * coarse ∧
      out.regs 32 = 33 * cap * (err * bound ^ 2) * coarse ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 31 → r ≠ 32 → out.regs r = st.regs r) := by
  let a := (3 * bound) ^ L * err
  let b := 33 * cap * err
  let first := a * (L + 1) * coarse
  let second := b * (bound * bound) * coarse
  have ef : first = 3 ^ L * (err * (L + 1) * bound ^ L) * coarse := by
    dsimp [first, a]
    rw [mul_pow]
    ac_rfl
  have es : second = 33 * cap * (err * bound ^ 2) * coarse := by
    simp only [second, b, pow_two, Nat.mul_assoc]
  have hf' : first < 2 ^ w := ef ▸ hf
  have hs' : second < 2 ^ w := es ▸ hs
  have haf : a * (L + 1) < 2 ^ w := (Nat.le_mul_of_pos_right _ hc).trans_lt hf'
  have ha : a < 2 ^ w := (Nat.le_mul_of_pos_right _ (Nat.succ_pos L)).trans_lt haf
  have haPos : 0 < a := Nat.mul_pos (Nat.pow_pos (Nat.mul_pos (by decide) hb)) he
  have hl : L + 1 < 2 ^ w := (Nat.le_mul_of_pos_left _ haPos).trans_lt haf
  have hbf : b * (bound * bound) < 2 ^ w := (Nat.le_mul_of_pos_right _ hc).trans_lt hs'
  have hbfit : b < 2 ^ w :=
    (Nat.le_mul_of_pos_right _ (Nat.mul_pos hb hb)).trans_lt hbf
  have hcap : 33 * cap < 2 ^ w := (Nat.le_mul_of_pos_right _ he).trans_lt hbfit
  have h33 : 33 < 2 ^ w := (Nat.le_mul_of_pos_right _ hp).trans_lt hcap
  have hbb : bound * bound < 2 ^ w := (Nat.le_mul_of_pos_left _
    (Nat.mul_pos (Nat.mul_pos (by decide) hp) he)).trans_lt hbf
  let mid := {st with regs := Function.update st.regs 31 first}
  let out := {mid with regs := Function.update mid.regs 32 second}
  have r₁ : Runs w p ω
      (.assign 31 (.bin .mul
        (.bin .mul (.bin .mul (.reg 29) (.reg 35)) (.bin .add (.reg 44) (.const 1))) (.reg 30)))
      st .normal mid 10 :=
    runs_assign_iff.mpr ⟨first, by simp [Expr.eval, BinOp.eval, h29, h35, h44, h30,
      show 1 < 2 ^ w by omega, show _ < 2 ^ w from ha, hl, haf, hf', first, a],
      rfl, rfl, rfl⟩
  have r₂ : Runs w p ω
      (.assign 32 (.bin .mul
        (.bin .mul (.bin .mul (.bin .mul (.const 33) (.reg 34)) (.reg 35))
          (.bin .mul (.reg 36) (.reg 36))) (.reg 30)))
      mid .normal out 12 :=
    runs_assign_iff.mpr ⟨second, by simp [Expr.eval, BinOp.eval, mid, h34, h35, h36,
      h30, h33, hcap, hbfit, hbb, hbf, hs', second, b], rfl, rfl, rfl⟩
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 10, 12, r₁, r₂, rfl⟩), ?_, ?_, rfl, ?_⟩
  · simp [out, mid, ef]
  · simp [out, es]
  · intro r h31 h32
    simp [out, mid, h31, h32]

/-- Select the working scale once the two error coefficients and the
coarse scale have been computed in registers 31, 32 and 30. -/
@[expose] def selectGrowthWorkingScale (clog : ℕ) : Stmt :=
  .assign 33 (.bin .add (.reg 31) (.bin .sub (.reg 32) (.reg 31))) ;;
  .assign 33 (.bin .add (.reg 30) (.bin .sub (.reg 33) (.reg 30))) ;;
  .call 37 clog [.reg 33] ;;
  .assign 4 (.bin .shiftLeft (.const 1) (.reg 37))

/-- The machine selects the same binary precision as the stretch error
bound, and materializes its power of two. -/
theorem selectGrowthWorkingScale_runs
    {w clog L cap coarse err bound : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hp : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (h30 : st.regs 30 = coarse)
    (h31 : st.regs 31 = 3 ^ L * (err * (L + 1) * bound ^ L) * coarse)
    (h32 : st.regs 32 = 33 * cap * (err * bound ^ 2) * coarse)
    (hword : 2 < 2 ^ w)
    (hfit : max coarse (max (st.regs 31) (st.regs 32)) + 1 < 2 ^ w)
    (hs : 2 ^ growthWorkingBits L cap coarse err bound < 2 ^ w) :
    ∃ out cost, Runs w p ω (selectGrowthWorkingScale clog) st .normal out cost ∧
      out.regs 37 = growthWorkingBits L cap coarse err bound ∧
      out.regs 4 = 2 ^ growthWorkingBits L cap coarse err bound ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 33 → r ≠ 37 → r ≠ 4 → out.regs r = st.regs r) ∧
      cost ≤ 40 * growthWorkingBits L cap coarse err bound + 41 := by
  let pair := max (st.regs 31) (st.regs 32)
  let n := max coarse pair
  let bits := growthWorkingBits L cap coarse err bound
  have hn : n < 2 ^ w := by omega
  have hpair : pair < 2 ^ w := (le_max_right coarse pair).trans_lt hn
  have e₁ : st.regs 31 + (st.regs 32 - st.regs 31) = pair := by dsimp [pair]; omega
  have e₂ : coarse + (pair - coarse) = n := by dsimp [n]; omega
  have hsub₁ : st.regs 32 - st.regs 31 < 2 ^ w := by omega
  have hsub₂ : pair - coarse < 2 ^ w := by omega
  let mid := {st with regs := Function.update st.regs 33 pair}
  let ready := {mid with regs := Function.update mid.regs 33 n}
  have r₁ : Runs w p ω
      (.assign 33 (.bin .add (.reg 31) (.bin .sub (.reg 32) (.reg 31)))) st .normal mid 6 :=
    runs_assign_iff.mpr ⟨pair, by simp [Expr.eval, BinOp.eval, hsub₁, e₁, hpair], rfl, rfl, rfl⟩
  have r₂ : Runs w p ω
      (.assign 33 (.bin .add (.reg 30) (.bin .sub (.reg 33) (.reg 30)))) mid .normal ready 6 :=
    runs_assign_iff.mpr ⟨n, by simp [Expr.eval, BinOp.eval, mid, h30, hsub₂, e₂, hn], rfl, rfl, rfl⟩
  have hargs : evalArgs w ready [.reg 33] = some [n] := by simp [evalArgs, Expr.eval, ready]
  obtain ⟨done, c, v, hr, ⟨hm, hv⟩, h37, hf, hc⟩ :=
    runs_call_of_meetsContract (r := 37) (Scaling.Machine.clogTwo_meetsContract hp n)
      hargs (by simpa using hn) ⟨rfl, hfit, hword⟩ ω
  have hbits : Nat.clog 2 n = bits := by simp [n, pair, h31, h32, bits, growthWorkingBits]
  have h37' := h37.trans (hv.trans hbits)
  let out := {done with regs := Function.update done.regs 4 (2 ^ bits)}
  have r₄ : Runs w p ω (.assign 4 (.bin .shiftLeft (.const 1) (.reg 37))) done .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, h37', Nat.shiftLeft_eq,
      show 1 < 2 ^ w by omega, show 2 ^ bits < 2 ^ w from hs], rfl, rfl, rfl⟩
  refine ⟨out, c + 19, ?_, by simpa [out] using h37', by simp [out, bits], hm, ?_, ?_⟩
  · refine runs_seq_iff.mpr (Or.inr ⟨mid, 6, c + 12, r₁, ?_, by omega⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨ready, 6, c + 5, r₂, ?_, by omega⟩)
    exact runs_seq_iff.mpr (Or.inr ⟨done, c, 4, hr, r₄, by omega⟩)
  · intro r h33 h37 h4
    simp [out, ready, mid, h33, h4, hf r h37]
  · simp [Scaling.Machine.clogTwoContract, argsSize, Expr.size, hbits] at hc
    change c + 19 ≤ 40 * bits + 41
    omega

/-- Compute the working scale from the stored parameters and the precomputed
power in register 29. The scale calculation preserves the factor inputs. -/
@[expose] def computeGrowthWorkingScale (clog : ℕ) : Stmt :=
  prepareGrowthScaleCoefficients ;; selectGrowthWorkingScale clog

/-- The coefficient preparation and binary logarithm implement the scale
formula using constant arithmetic overhead and one ceiling logarithm. -/
theorem computeGrowthWorkingScale_runs
    {w clog L cap coarse err bound : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hp : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (h29 : st.regs 29 = (3 * bound) ^ L) (h30 : st.regs 30 = coarse)
    (h34 : st.regs 34 = cap) (h35 : st.regs 35 = err)
    (h36 : st.regs 36 = bound) (h44 : st.regs 44 = L)
    (hcap : 0 < cap) (hc : 0 < coarse) (he : 0 < err) (hb : 0 < bound)
    (hword : 2 < 2 ^ w)
    (hfit : max coarse (max (3 ^ L * (err * (L + 1) * bound ^ L) * coarse)
      (33 * cap * (err * bound ^ 2) * coarse)) + 1 < 2 ^ w)
    (hs : 2 ^ growthWorkingBits L cap coarse err bound < 2 ^ w) :
    ∃ out cost, Runs w p ω (computeGrowthWorkingScale clog) st .normal out cost ∧
      out.regs 37 = growthWorkingBits L cap coarse err bound ∧
      out.regs 4 = 2 ^ growthWorkingBits L cap coarse err bound ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 31 → r ≠ 32 → r ≠ 33 → r ≠ 37 → r ≠ 4 → out.regs r = st.regs r) ∧
      cost ≤ 40 * growthWorkingBits L cap coarse err bound + 65 := by
  have hbnd := (Nat.lt_succ_self _).trans hfit
  have hf := (le_max_left _ _).trans_lt ((le_max_right coarse _).trans_lt hbnd)
  have ht := (le_max_right _ _).trans_lt ((le_max_right coarse _).trans_lt hbnd)
  obtain ⟨mid, hr, h31, h32, hm, hframe⟩ :=
    prepareGrowthScaleCoefficients_runs (p := p) (ω := ω) h29 h30 h34 h35 h36 h44
      hcap hc he hb hf ht
  have h30' := (hframe 30 (by decide) (by decide)).trans h30
  have hfit' : max coarse (max (mid.regs 31) (mid.regs 32)) + 1 < 2 ^ w := by
    simpa only [h31, h32] using hfit
  obtain ⟨out, cost, hout, h37, h4, hm', hframe', hcost⟩ :=
    selectGrowthWorkingScale_runs (ω := ω) hp h30' h31 h32 hword hfit' hs
  refine ⟨out, 23 + cost + 1, runs_seq_iff.mpr (Or.inr ⟨mid, 23, cost, hr, hout, rfl⟩),
    h37, h4, hm'.trans hm, ?_, ?_⟩
  · intro r h31r h32r h33r h37r h4r
    exact (hframe' r h33r h37r h4r).trans (hframe r h31r h32r)
  · omega

/-- Compute the stretch working precision from the runtime factor bound,
depth, and error allowance. -/
@[expose] def initGrowthWorkingScale (clog : ℕ) : Stmt :=
  prepareGrowthScalePower ;; computeGrowthWorkingScale clog

/-- The complete precision calculation derives the power internally and
preserves memory and registers outside its scratch set. -/
theorem initGrowthWorkingScale_runs
    {w clog L cap coarse err bound : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hp : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (h30 : st.regs 30 = coarse) (h34 : st.regs 34 = cap)
    (h35 : st.regs 35 = err) (h36 : st.regs 36 = bound) (h44 : st.regs 44 = L)
    (hcap : 0 < cap) (hc : 0 < coarse) (he : 0 < err) (hb : 0 < bound)
    (hword : 3 < 2 ^ w) (hbase : 3 * bound < 2 ^ w) (hdepth : L < 2 ^ w)
    (hfit : max coarse (max (3 ^ L * (err * (L + 1) * bound ^ L) * coarse)
      (33 * cap * (err * bound ^ 2) * coarse)) + 1 < 2 ^ w)
    (hs : 2 ^ growthWorkingBits L cap coarse err bound < 2 ^ w) :
    ∃ out cost, Runs w p ω (initGrowthWorkingScale clog) st .normal out cost ∧
      out.regs 37 = growthWorkingBits L cap coarse err bound ∧
      out.regs 4 = 2 ^ growthWorkingBits L cap coarse err bound ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 31 → r ≠ 32 →
        r ≠ 33 → r ≠ 37 → r ≠ 4 → out.regs r = st.regs r) ∧
      cost ≤ 13 * L + 40 * growthWorkingBits L cap coarse err bound + 81 := by
  have hfirst := (le_max_left _ _).trans_lt
    ((le_max_right coarse _).trans_lt ((Nat.lt_succ_self _).trans hfit))
  have hpow : (3 * bound) ^ L < 2 ^ w := by
    have eq : 3 ^ L * (err * (L + 1) * bound ^ L) * coarse =
        (3 * bound) ^ L * (err * (L + 1) * coarse) := by
      rw [mul_pow]
      ac_rfl
    rw [eq] at hfirst
    exact (Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.mul_pos he (Nat.succ_pos _)) hc)).trans_lt hfirst
  obtain ⟨mid, c₁, hr₁, h29, hm₁, hf₁, hc₁⟩ :=
    prepareGrowthScalePower_runs (p := p) (ω := ω) h36 h44 hb hword hbase hdepth hpow
  obtain ⟨out, c₂, hr₂, h37, h4, hm₂, hf₂, hc₂⟩ :=
    computeGrowthWorkingScale_runs (ω := ω) hp h29
      ((hf₁ 30 (by decide) (by decide) (by decide)).trans h30)
      ((hf₁ 34 (by decide) (by decide) (by decide)).trans h34)
      ((hf₁ 35 (by decide) (by decide) (by decide)).trans h35)
      ((hf₁ 36 (by decide) (by decide) (by decide)).trans h36)
      ((hf₁ 44 (by decide) (by decide) (by decide)).trans h44)
      hcap hc he hb (by omega) hfit hs
  refine ⟨out, c₁ + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c₁, c₂, hr₁, hr₂, rfl⟩),
    h37, h4, hm₂.trans hm₁, ?_, by omega⟩
  intro r h27 h28 h29r h31 h32 h33 h37r h4r
  exact (hf₂ r h31 h32 h33 h37r h4r).trans (hf₁ r h27 h28 h29r)

/-- Include the sparse-core logarithm error in the common endpoint
allowance. Register 92 holds the logarithm input before the shift by two. -/
@[expose] def includeSparseCoreLogError : Stmt :=
  .assign 38 (.bin .mul (.const 4096) (.bin .add (.reg 92) (.const 2))) ;;
  .assign 35 (.bin .add (.reg 35) (.bin .sub (.reg 38) (.reg 35)))

/-- The allowance covers the logarithm and the previous endpoint errors.
All arithmetic fits if the final allowance fits. -/
theorem includeSparseCoreLogError_runs
    {w input err : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (h92 : st.regs 92 = input) (h35 : st.regs 35 = err)
    (hfit : max err (4096 * (input + 2)) < 2 ^ w) :
    ∃ out, Runs w p ω includeSparseCoreLogError st .normal out 13 ∧
      out.regs 35 = max err (4096 * (input + 2)) ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 35 → r ≠ 38 → out.regs r = st.regs r) := by
  let budget := 4096 * (input + 2)
  have hb : budget < 2 ^ w := (le_max_right err budget).trans_lt hfit
  have hi : input + 2 < 2 ^ w := (Nat.le_mul_of_pos_left _ (by decide : 0 < 4096)).trans_lt hb
  have hc : 4096 < 2 ^ w := (Nat.le_mul_of_pos_right _ (by omega : 0 < input + 2)).trans_lt hb
  have hdelta : budget - err < 2 ^ w := (Nat.sub_le _ _).trans_lt hb
  have hmax : err + (budget - err) = max err budget := by omega
  let mid := {st with regs := Function.update st.regs 38 budget}
  let out := {mid with regs := Function.update mid.regs 35 (max err budget)}
  have hr₁ : Runs w p ω
      (.assign 38 (.bin .mul (.const 4096) (.bin .add (.reg 92) (.const 2)))) st .normal mid 6 :=
    runs_assign_iff.mpr ⟨budget, by simp [Expr.eval, BinOp.eval, h92, hi, hc, budget, hb,
      show 2 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω
      (.assign 35 (.bin .add (.reg 35) (.bin .sub (.reg 38) (.reg 35)))) mid .normal out 6 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, mid, h35, hdelta, hmax, hb, (le_max_left err budget).trans_lt hfit], rfl, rfl, rfl⟩
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 6, 6, hr₁, hr₂, ?_⟩), by simp [out, budget], rfl, ?_⟩
  · decide
  · intro r h35r h38r
    simp [out, mid, h35r, h38r]

/-- Derive the logarithm allowance from the padded edge bound, then
restore the graph's vertex count for the rest of Init. -/
@[expose] def prepareRebuildLogAllowance : Stmt :=
  prepareInitSparseCoreLogInput ;; includeSparseCoreLogError ;; .assign 92 (.reg 57)

/-- Computing the allowance takes 33 steps and leaves the graph and
heap inputs available for the scale calculation. -/
theorem prepareRebuildLogAllowance_runs
    {w M N err : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hM : st.regs 22 = M) (hN : st.regs 92 = N) (h35 : st.regs 35 = err)
    (hMw : M ^ 2 < 2 ^ w) (hw : 60 < 2 ^ w) (hlinear : 2 * M ^ 2 + 60 < 2 ^ w)
    (hproduct : M ^ 2 * (2 * M ^ 2 + 60) < 2 ^ w)
    (hfit : max err (4096 * (SparseCore.coreNMax (M ^ 2) + M ^ 2 + 2)) < 2 ^ w) :
    ∃ out, Runs w p ω prepareRebuildLogAllowance st .normal out 33 ∧
      out.regs 35 = max err (4096 * (SparseCore.coreNMax (M ^ 2) + M ^ 2 + 2)) ∧
      out.mem = st.mem ∧
      (∀ r, r ≠ 24 → r ≠ 35 → r ≠ 38 → r ≠ 57 → out.regs r = st.regs r) := by
  obtain ⟨mid, hr₁, _, h57, h92, hf₁, hm₁, _⟩ :=
    prepareInitSparseCoreLogInput_runs (p := p) (ω := ω) hM hN hMw hw hlinear hproduct
  obtain ⟨ready, hr₂, h35', hm₂, hf₂⟩ :=
    includeSparseCoreLogError_runs (p := p) (ω := ω) h92
      ((hf₁ 35 (by decide) (by decide) (by decide)).trans h35) hfit
  let out := {ready with regs := Function.update ready.regs 92 N}
  have hsaved := (hf₂ 57 (by decide) (by decide)).trans h57
  have hr₃ : Runs w p ω (.assign 92 (.reg 57)) ready .normal out 2 :=
    runs_assign_iff.mpr ⟨N, by simp [Expr.eval, hsaved], rfl, rfl, rfl⟩
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 16, 16, hr₁,
      runs_seq_iff.mpr (Or.inr ⟨ready, 13, 2, hr₂, hr₃, rfl⟩), rfl⟩),
    by simpa [out] using h35', hm₂.trans hm₁, ?_⟩
  intro r h24 h35r h38 h57r
  by_cases h : r = 92
  · subst r
    simp [out, hN]
  · simpa [out, h] using (hf₂ r h35r h38).trans (hf₁ r h24 h57r h)

/-- Stage the capacity multiplier for the stretch precision calculation.
The sparsifier depth, bucket cap, and degree cap are runtime inputs. -/
@[expose] def prepareRebuildScaleCapacity : Stmt :=
  .assign 33 (.bin .add (.reg 44) (.const 1)) ;;
  prepareInitStretchCapacity ;;
  .assign 34 (.reg 38)

/-- The same integer capacity multiplier is used for scale selection and
for evaluating the second term of the growth bound. -/
theorem prepareRebuildScaleCapacity_runs
    {w L buckets degree : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (h44 : st.regs 44 = L) (h47 : st.regs 47 = buckets) (h48 : st.regs 48 = degree)
    (hb : 0 < buckets) (hfit : (L + 1) * buckets * (2 * degree + 190) < 2 ^ w) :
    ∃ out, Runs w p ω prepareRebuildScaleCapacity st .normal out 18 ∧
      out.regs 34 = (L + 1) * buckets * (2 * degree + 190) ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 33 → r ≠ 34 → r ≠ 38 → out.regs r = st.regs r) := by
  have h1 : L + 1 ≤ (L + 1) * buckets :=
    Nat.le_mul_of_pos_right _ hb
  have h2 : (L + 1) * buckets ≤ (L + 1) * buckets * (2 * degree + 190) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hn := (h1.trans h2).trans_lt hfit
  let start := {st with regs := Function.update st.regs 33 (L + 1)}
  have hr₁ : Runs w p ω (.assign 33 (.bin .add (.reg 44) (.const 1))) st .normal start 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, h44, hn, show 1 < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  obtain ⟨mid, hr₂, h38, hf, hm, _⟩ :=
    prepareInitStretchCapacity_runs (p := p) (ω := ω) (st := start)
      (by simp [start]) (by simp [start, h47]) (by simp [start, h48]) hb hfit
  let out := {mid with regs := Function.update mid.regs 34 (mid.regs 38)}
  have hr₃ : Runs w p ω (.assign 34 (.reg 38)) mid .normal out 2 :=
    runs_assign_iff.mpr ⟨_, rfl, rfl, rfl, rfl⟩
  refine ⟨out, ?_, by simp [out, h38], hm, ?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨start, 4, 13, hr₁,
      runs_seq_iff.mpr (Or.inr ⟨mid, 10, 2, hr₂, hr₃, rfl⟩), rfl⟩)
  · intro r h33 h34 h38r
    simpa [out, start, h33, h34] using hf r h38r

/-- Compute both rebuild scales from the chain depth and the stretch
factor bounds saved by Init. -/
@[expose] def initRebuildScales (clog : ℕ) : Stmt :=
  prepareGrowthCoarseScale clog ;; initGrowthWorkingScale clog

/-- The scale computation preserves the heap and the input registers. -/
theorem initRebuildScales_runs
    {w clog depth L cap err bound : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hp : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (h75 : st.regs 75 = depth) (h34 : st.regs 34 = cap)
    (h35 : st.regs 35 = err) (h36 : st.regs 36 = bound) (h44 : st.regs 44 = L)
    (hcap : 0 < cap) (he : 0 < err) (hb : 0 < bound)
    (hword : 3 < 2 ^ w) (hbase : 3 * bound < 2 ^ w) (hdepth : L < 2 ^ w)
    (hlog : 2 * (depth + 1) + 1 < 2 ^ w) :
    let coarse := concreteThresholdScale depth
    let bits := growthWorkingBits L cap coarse err bound
    max coarse (max (3 ^ L * (err * (L + 1) * bound ^ L) * coarse)
      (33 * cap * (err * bound ^ 2) * coarse)) + 1 < 2 ^ w →
    2 ^ bits < 2 ^ w →
    ∃ out cost, Runs w p ω (initRebuildScales clog) st .normal out cost ∧
      out.regs 30 = coarse ∧ out.regs 37 = bits ∧ out.regs 4 = 2 ^ bits ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 → r ≠ 31 → r ≠ 32 →
        r ≠ 33 → r ≠ 37 → r ≠ 4 → out.regs r = st.regs r) ∧
      cost ≤ 40 * Nat.clog 2 (2 * (depth + 1)) + 13 * L + 40 * bits + 113 := by
  dsimp only
  intro hfit hs
  have hcoarse : 0 < concreteThresholdScale depth := Nat.two_pow_pos _
  have hroom := (growthWorkingBits_bounds L cap (concreteThresholdScale depth) err bound).1.trans_lt hs
  obtain ⟨mid, c₁, hr₁, h30, hm₁, hf₁, hc₁⟩ :=
    prepareGrowthCoarseScale_runs (ω := ω) hp h75 hlog hroom
  obtain ⟨out, c₂, hr₂, h37, h4, hm₂, hf₂, hc₂⟩ :=
    initGrowthWorkingScale_runs (ω := ω) hp h30
      ((hf₁ 34 (by decide)).trans h34) ((hf₁ 35 (by decide)).trans h35)
      ((hf₁ 36 (by decide)).trans h36) ((hf₁ 44 (by decide)).trans h44)
      hcap hcoarse he hb hword hbase hdepth hfit hs
  refine ⟨out, c₁ + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c₁, c₂, hr₁, hr₂, rfl⟩),
    (hf₂ 30 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans h30,
    h37, h4, hm₂.trans hm₁, ?_, by omega⟩
  intro r h27 h28 h29 h30r h31 h32 h33 h37r h4r
  exact (hf₂ r h27 h28 h29 h31 h32 h33 h37r h4r).trans (hf₁ r h30r)

/-- Compute the capacity multiplier and both scales before evaluating
the stretch endpoints. -/
@[expose] def initRebuildScalesFromCaps (clog : ℕ) : Stmt :=
  prepareRebuildScaleCapacity ;; initRebuildScales clog

/-- The rebuild scales use the capacity derived from the same runtime
depth, bucket cap, and degree cap used by the stretch evaluator. -/
theorem initRebuildScalesFromCaps_runs
    {w clog depth L buckets degree err bound : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hp : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (h75 : st.regs 75 = depth) (h44 : st.regs 44 = L)
    (h47 : st.regs 47 = buckets) (h48 : st.regs 48 = degree)
    (h35 : st.regs 35 = err) (h36 : st.regs 36 = bound)
    (hbuckets : 0 < buckets) (he : 0 < err) (hb : 0 < bound)
    :
    let cap := (L + 1) * buckets * (2 * degree + 190)
    let coarse := concreteThresholdScale depth
    let bits := growthWorkingBits L cap coarse err bound
    2 ^ bits < 2 ^ w →
    ∃ out cost, Runs w p ω (initRebuildScalesFromCaps clog) st .normal out cost ∧
      out.regs 30 = coarse ∧ out.regs 34 = cap ∧ out.regs 37 = bits ∧
      out.regs 4 = 2 ^ bits ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 4 → r < 27 ∨ 38 < r → out.regs r = st.regs r) ∧
      cost ≤ 40 * Nat.clog 2 (2 * (depth + 1)) + 13 * L + 40 * bits + 132 := by
  dsimp only
  intro hs
  let cap := (L + 1) * buckets * (2 * degree + 190)
  have hcap : 0 < cap :=
    Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) hbuckets) (by omega)
  let coarse := concreteThresholdScale depth
  let bits := growthWorkingBits L cap coarse err bound
  let work := 2 ^ bits
  let first := 3 ^ L * (err * (L + 1) * bound ^ L) * coarse
  let second := 33 * cap * (err * bound ^ 2) * coarse
  have hwork : work < 2 ^ w := hs
  have hnext : work * 2 ≤ 2 ^ w := by
    rw [← pow_succ]
    apply Nat.pow_le_pow_right (by decide)
    by_contra! h
    exact (not_lt_of_ge (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : w ≤ bits))) hwork
  have hroom : work + 1 < 2 ^ w := by
    have h₀ : 2 * (depth + 1) ≤ coarse := Nat.le_pow_clog Nat.one_lt_two _
    have h₁ : coarse ≤ work := (growthWorkingBits_bounds L cap coarse err bound).1
    omega
  have hcapMul : cap ≤ 33 * cap := Nat.le_mul_of_pos_left _ (by decide)
  have hcapErr : 33 * cap ≤ 33 * cap * (err * bound ^ 2) :=
    Nat.le_mul_of_pos_right _ (Nat.mul_pos he (Nat.pow_pos hb))
  have hcoarsePos : 0 < coarse := Nat.two_pow_pos _
  have hcapSecond : cap ≤ second :=
    (hcapMul.trans hcapErr).trans (Nat.le_mul_of_pos_right _ hcoarsePos)
  obtain ⟨hcoarse, hfirst, hsecond⟩ := growthWorkingBits_bounds L cap coarse err bound
  have hcapFit : cap < 2 ^ w := hcapSecond.trans_lt (hsecond.trans_lt hwork)
  have hfit : max coarse (max first second) + 1 < 2 ^ w :=
    (Nat.add_le_add_right (max_le hcoarse (max_le hfirst hsecond)) 1).trans_lt hroom
  have hlog : 2 * (depth + 1) + 1 < 2 ^ w :=
    (Nat.add_le_add_right ((Nat.le_pow_clog Nat.one_lt_two _ : 2 * (depth + 1) ≤ coarse).trans hcoarse) 1).trans_lt hroom
  have hbase : 3 * bound < 2 ^ w := by
    have h₀ : bound ≤ err * bound ^ 2 :=
      (by simpa using Nat.pow_le_pow_right hb (show 1 ≤ 2 by decide) :
        bound ≤ bound ^ 2).trans (Nat.le_mul_of_pos_left _ he)
    have h₁ : 3 ≤ 33 * cap := (by decide : 3 ≤ 33).trans (Nat.le_mul_of_pos_right _ hcap)
    exact ((Nat.mul_le_mul h₁ h₀).trans (Nat.le_mul_of_pos_right _ hcoarsePos)).trans_lt
      (hsecond.trans_lt hwork)
  have hdepth : L < 2 ^ w := by
    have h₀ : L + 1 ≤ err * (L + 1) := Nat.le_mul_of_pos_left _ he
    have h₁ := h₀.trans (Nat.le_mul_of_pos_right (err * (L + 1)) (Nat.pow_pos (n := L) hb))
    have h₂ := h₁.trans (Nat.le_mul_of_pos_left _ (Nat.pow_pos (n := L) (by decide : 0 < 3)))
    have h₃ : L + 1 ≤ first := h₂.trans (Nat.le_mul_of_pos_right _ hcoarsePos)
    exact (Nat.le_succ L).trans_lt (h₃.trans_lt (hfirst.trans_lt hwork))
  have hword : 3 < 2 ^ w := (Nat.le_mul_of_pos_right _ hb).trans_lt hbase
  obtain ⟨mid, hr₁, h34, hm₁, hf₁⟩ :=
    prepareRebuildScaleCapacity_runs (p := p) (ω := ω) h44 h47 h48 hbuckets hcapFit
  obtain ⟨out, c, hr₂, h30, h37, h4, hm₂, hf₂, hc⟩ :=
    initRebuildScales_runs (ω := ω) hp ((hf₁ 75 (by decide) (by decide) (by decide)).trans h75)
      h34 ((hf₁ 35 (by decide) (by decide) (by decide)).trans h35)
      ((hf₁ 36 (by decide) (by decide) (by decide)).trans h36)
      ((hf₁ 44 (by decide) (by decide) (by decide)).trans h44)
      hcap he hb hword hbase hdepth hlog hfit hs
  refine ⟨out, 18 + c + 1, runs_seq_iff.mpr (Or.inr ⟨mid, 18, c, hr₁, hr₂, rfl⟩),
    h30, ?_, h37, h4, hm₂.trans hm₁, ?_, by omega⟩
  · exact (hf₂ 34 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans h34
  · intro r h4r hr
    exact (hf₂ r (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) h4r).trans (hf₁ r (by omega) (by omega) (by omega))

/-- The extra bits for assembling either stretch term are bounded by
the depth and the binary widths of the capacity and factor bounds. -/
theorem growthEndpoint_coefficient_bits_le (L cap bound : ℕ) :
    Nat.clog 2 (max (3 ^ L * bound ^ (L + 1)) (11 * (cap * bound ^ 3 + 115))) ≤
      max (2 * L + Nat.clog 2 bound * (L + 1))
        (5 + max (Nat.clog 2 cap + Nat.clog 2 bound * 3) 7) := by
  let b := Nat.clog 2 bound
  let c := Nat.clog 2 cap
  let a := 2 * L + b * (L + 1)
  let d := max (c + b * 3) 7
  have hb : bound ≤ 2 ^ b := Nat.le_pow_clog Nat.one_lt_two _
  have hc : cap ≤ 2 ^ c := Nat.le_pow_clog Nat.one_lt_two _
  have hfirst : 3 ^ L * bound ^ (L + 1) ≤ 2 ^ a := by
    calc
      _ ≤ (2 ^ 2) ^ L * (2 ^ b) ^ (L + 1) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (by decide) _) (Nat.pow_le_pow_left hb _)
      _ = _ := by rw [← pow_mul, ← pow_mul, ← pow_add]
  have hprod : cap * bound ^ 3 ≤ 2 ^ d := by
    calc
      _ ≤ 2 ^ c * (2 ^ b) ^ 3 := Nat.mul_le_mul hc (Nat.pow_le_pow_left hb _)
      _ = 2 ^ (c + b * 3) := by rw [← pow_mul, ← pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (le_max_left _ _)
  have hconst : 115 ≤ 2 ^ d :=
    (by decide : 115 ≤ 2 ^ 7).trans (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
  have hsecond : 11 * (cap * bound ^ 3 + 115) ≤ 2 ^ (5 + d) := by
    calc
      _ ≤ 16 * (2 ^ d + 2 ^ d) := Nat.mul_le_mul (by decide) (Nat.add_le_add hprod hconst)
      _ = (2 ^ 5 : ℕ) * 2 ^ d := by omega
      _ = _ := (pow_add 2 5 d).symm
  apply Nat.clog_le_of_le_pow
  exact max_le (hfirst.trans (Nat.pow_le_pow_right (by decide) (le_max_left a (5 + d))))
    (hsecond.trans (Nat.pow_le_pow_right (by decide) (le_max_right a (5 + d))))

/-- The working precision is bounded by the input bit widths and the
common bound for endpoint coefficients. -/
theorem growthWorkingBits_budget (L cap coarse err bound : ℕ) :
    growthWorkingBits L cap coarse err bound ≤
      Nat.clog 2 coarse + Nat.clog 2 err + Nat.clog 2 (L + 1) +
        (12 + Nat.clog 2 cap + (Nat.clog 2 bound + 2) * (L + 3)) := by
  let b := Nat.clog 2 bound
  let c := Nat.clog 2 cap
  let extra := 12 + c + (b + 2) * (L + 3)
  have he : extra = 12 + c + (b * L + b * 3 + 2 * L + 6) := by
    dsimp [extra]
    ring
  apply (growthWorkingBits_le L cap coarse err bound).trans
  rw [Nat.add_assoc (Nat.clog 2 coarse + Nat.clog 2 err)]
  apply Nat.add_le_add_left
  change max (2 * L + Nat.clog 2 (L + 1) + L * b) (6 + c + 2 * b) ≤
    Nat.clog 2 (L + 1) + extra
  rw [he, Nat.mul_comm L b]
  exact max_le (by omega) (by omega)

/-- A word budget in terms of the input bit widths suffices for the
common precision and the larger of the two endpoint coefficients. -/
theorem growthEndpoint_width_le (L cap coarse err bound : ℕ) :
    let b := Nat.clog 2 bound
    let c := Nat.clog 2 cap
    let extra := 12 + c + (b + 2) * (L + 3)
    growthWorkingBits L cap coarse err bound * max (L + 1) 3 +
        Nat.clog 2 (max (3 ^ L * bound ^ (L + 1)) (11 * (cap * bound ^ 3 + 115))) ≤
      (Nat.clog 2 coarse + Nat.clog 2 err + Nat.clog 2 (L + 1) + extra) *
        max (L + 1) 3 + extra := by
  dsimp only
  let b := Nat.clog 2 bound
  let c := Nat.clog 2 cap
  let extra := 12 + c + (b + 2) * (L + 3)
  have he : extra = 12 + c + (b * L + b * 3 + 2 * L + 6) := by
    dsimp [extra]
    ring
  have hbits := growthWorkingBits_budget L cap coarse err bound
  have hcoeff : Nat.clog 2 (max (3 ^ L * bound ^ (L + 1)) (11 * (cap * bound ^ 3 + 115))) ≤
      extra := by
    apply (growthEndpoint_coefficient_bits_le L cap bound).trans
    change max (2 * L + b * (L + 1)) (5 + max (c + b * 3) 7) ≤ extra
    rw [he, Nat.mul_add, Nat.mul_one]
    apply max_le
    · omega
    · rw [← Nat.add_max_add_left]
      exact max_le (by omega) (by omega)
  exact Nat.add_le_add (Nat.mul_le_mul_right _ hbits) hcoeff

/-- Bound the three words used to assemble the two stretch terms. The
common scale occupies the same precision in both terms, while each term
adds the bit width of its own coefficient. -/
theorem growthEndpoint_words_fit
    {w L cap bits bound k s l : ℕ}
    (hk : k ≤ bound * 2 ^ bits) (hs : s ≤ bound * 2 ^ bits) (hl : l ≤ bound * 2 ^ bits) :
    let e := max (L + 1) 3
    let coeff := max (3 ^ L * bound ^ (L + 1)) (11 * (cap * bound ^ 3 + 115))
    bits * e + Nat.clog 2 coeff < w →
    2 ^ (bits * e) < 2 ^ w ∧
      3 ^ L * (2 ^ bits) ^ (e - (L + 1)) * s ^ (L + 1) < 2 ^ w ∧
      11 * (cap * k * s * l + 115 * (2 ^ bits) ^ 3) * (2 ^ bits) ^ (e - 3) < 2 ^ w := by
  dsimp only
  intro hw
  let e := max (L + 1) 3
  let work := 2 ^ bits
  let a := 3 ^ L * bound ^ (L + 1)
  let b := 11 * (cap * bound ^ 3 + 115)
  change k ≤ bound * work at hk
  change s ≤ bound * work at hs
  change l ≤ bound * work at hl
  have ha : 3 ^ L * work ^ (e - (L + 1)) * s ^ (L + 1) ≤ a * work ^ e := by
    refine (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs _)).trans_eq ?_
    rw [mul_pow]
    calc
      _ = a * (work ^ (e - (L + 1)) * work ^ (L + 1)) := by dsimp [a]; ring
      _ = _ := by rw [← pow_add, Nat.sub_add_cancel (le_max_left _ _)]
  have hb : 11 * (cap * k * s * l + 115 * work ^ 3) * work ^ (e - 3) ≤ b * work ^ e := by
    have hprod := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left cap hk) hs) hl
    refine (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 11 (Nat.add_le_add_right hprod _))).trans_eq ?_
    have he : work ^ 3 * work ^ (e - 3) = work ^ e := by
      rw [← pow_add, Nat.add_sub_of_le (le_max_right _ _)]
    calc
      _ = b * (work ^ 3 * work ^ (e - 3)) := by dsimp [b]; ring
      _ = _ := by rw [he]
  have hpow : work ^ e = 2 ^ (bits * e) := (pow_mul 2 bits e).symm
  have hroom : max a b * work ^ e < 2 ^ w := by
    calc
      _ ≤ 2 ^ Nat.clog 2 (max a b) * work ^ e :=
        Nat.mul_le_mul_right _ (Nat.le_pow_clog Nat.one_lt_two _)
      _ = 2 ^ (bits * e + Nat.clog 2 (max a b)) := by rw [hpow, ← pow_add, Nat.add_comm]
      _ < 2 ^ w := Nat.pow_lt_pow_right (by decide) hw
  exact ⟨Nat.pow_lt_pow_right (by decide) ((Nat.le_add_right _ _).trans_lt hw),
    (ha.trans (Nat.mul_le_mul_right _ (le_max_left a b))).trans_lt hroom,
    (hb.trans (Nat.mul_le_mul_right _ (le_max_right a b))).trans_lt hroom⟩

/-- For uniformly bounded factors, choose the working scale from the
two error coefficients before raising any endpoint to a power. -/
theorem assembledGrowthEndpoint_gap_of_scale
    {cap scale coarse L kl ku sl su ll lu err bound : ℕ}
    (hk : kl ≤ ku) (hs : sl ≤ su) (hl : ll ≤ lu)
    (hku : ku ≤ bound * scale) (hsu : su ≤ bound * scale) (hlu : lu ≤ bound * scale)
    (hke : ku - kl ≤ err) (hse : su - sl ≤ err) (hle : lu - ll ≤ err)
    (hfirst : 3 ^ L * (err * (L + 1) * bound ^ L) * coarse ≤ scale)
    (hsecond : 33 * cap * (err * bound ^ 2) * coarse ≤ scale) :
    let n := L + 1
    let exponent := max n 3
    let first := fun s : ℕ => 3 ^ L * scale ^ (exponent - n) * s ^ n
    let second := fun k s l : ℕ =>
      11 * (cap * k * s * l + 115 * scale ^ 3) * scale ^ (exponent - 3)
    (first su - first sl) * coarse ≤ scale ^ exponent ∧
      (second ku su lu - second kl sl ll) * coarse ≤ scale ^ exponent := by
  dsimp only
  let e := max (L + 1) 3
  have he₁ : e - (L + 1) + L = e - 1 := by dsimp [e]; omega
  have he₂ : 2 + (e - 3) = e - 1 := by dsimp [e]; omega
  apply assembledGrowthEndpoint_gap_of_uniform hk hs hl hku hsu hlu hke hse hle
  · change 3 ^ L * scale ^ (e - (L + 1)) *
        (err * (L + 1) * (bound * scale) ^ (L + 1 - 1)) * coarse ≤ scale ^ e
    rw [Nat.add_sub_cancel, mul_pow]
    calc
      _ = (3 ^ L * (err * (L + 1) * bound ^ L) * coarse) *
          (scale ^ (e - (L + 1)) * scale ^ L) := by ring
      _ ≤ scale * scale ^ (e - 1) := by
        rw [← pow_add, he₁]
        exact Nat.mul_le_mul_right _ hfirst
      _ = _ := by rw [← pow_succ', Nat.sub_add_cancel (by dsimp [e]; omega : 1 ≤ e)]
  · change 11 * cap * (3 * (err * (bound * scale) ^ 2)) * scale ^ (e - 3) * coarse ≤ scale ^ e
    rw [mul_pow]
    calc
      _ = (33 * cap * (err * bound ^ 2) * coarse) * (scale ^ 2 * scale ^ (e - 3)) := by ring
      _ ≤ scale * scale ^ (e - 1) := by
        rw [← pow_add, he₂]
        exact Nat.mul_le_mul_right _ hsecond
      _ = _ := by rw [← pow_succ', Nat.sub_add_cancel (by dsimp [e]; omega : 1 ≤ e)]

/-- An upper endpoint within one coarse unit gives a verified integer
threshold table with the original safety budget and constant loss in
the amortized charge. -/
theorem initDyadicIntegerThresholdTable_runs
    (TP : SparseCoreParams) (P : ChainParams)
    {w clog upper precision vertices base : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hp : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (hTP : TP.Valid) (hγM : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀)
    (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    (hbase : base + P.d + 1 < 2 ^ w) (hz : ZeroFrom st.mem base)
    (h20 : st.regs 20 = upper) (h23 : st.regs 23 = 2 ^ precision)
    (h22 : st.regs 22 = P.M₀) (h14 : st.regs 14 = Nat.clog 2 (vertices + 2))
    (h77 : st.regs 77 = base) (h76 : st.regs 76 = P.k) (h75 : st.regs 75 = P.d)
    (hfit : 2 * (P.d + 1) + 1 < 2 ^ w) (hprecision : 2 ^ precision < 2 ^ w)
    (hden : 3 * P.k * Nat.clog 2 (vertices + 2) ^ 2 < 2 ^ w) :
    let e := Nat.clog 2 (2 * (P.d + 1))
    let scale := concreteThresholdScale P.d
    let divisor := 2 ^ (precision - e)
    let a := (upper + divisor - 1) / divisor
    e ≤ precision → upper < 2 ^ w →
    TP.γ_ℓ (P.M₀ ^ 2) ≤ (upper : ℝ) / ((2 ^ precision : ℕ) : ℝ) →
    (upper : ℝ) / ((2 ^ precision : ℕ) : ℝ) ≤ TP.γ_ℓ (P.M₀ ^ 2) + 1 / scale →
    (3 * P.M₀ ^ 2 + 1) * (P.M₀ * (2 * scale) ^ (P.d + 1)) < 2 ^ w →
    ∃ out cost, Runs w p ω (initDyadicIntegerThresholdTable clog) st .normal out cost ∧
      out.regs 83 = base ∧ out.regs 98 = base + P.d + 1 ∧
      (∀ j ≤ P.d, out.mem (base + j) = concreteLevelRebuildCount P.M₀ P.k a scale j vertices ∧
        (out.mem (base + j) : ℝ) ≤ SparseCoreTool.updateThreshold P.k (levelM TP P j) vertices ∧
        SparseCoreTool.updateThreshold P.k (levelM TP P j) vertices ≤
          48 * ((out.mem (base + j) : ℝ) + 1)) ∧
      (∀ x < base, out.mem x = st.mem x) ∧ ZeroFrom out.mem (base + P.d + 1) ∧
      cost ≤ 50 * P.d + 40 * e + 123 := by
  dsimp only
  intro he hupper hlo hhi hcapacity
  let e := Nat.clog 2 (2 * (P.d + 1))
  let scale := concreteThresholdScale P.d
  let divisor := 2 ^ (precision - e)
  have hs : 0 < scale := Nat.two_pow_pos _
  have hd : 0 < divisor := Nat.two_pow_pos _
  have hword : 1 < 2 ^ w := by omega
  have hscale : scale < 2 ^ w := (Nat.pow_le_pow_right (by decide) he).trans_lt hprecision
  have hsplit : scale * divisor = 2 ^ precision := by
    change 2 ^ e * 2 ^ (precision - e) = _
    rw [← pow_add, Nat.add_sub_of_le he]
  have hcoarse : 2 * ((P.d : ℝ) + 1) ≤ (scale : ℝ) := by
    exact_mod_cast (concreteThresholdScale_bounds P.d).1
  have herror : 1 / (scale : ℝ) + 1 / scale ≤ 1 / ((P.d : ℝ) + 1) := by
    have hdp : 0 < (P.d : ℝ) + 1 := by positivity
    have hsp : 0 < (scale : ℝ) := Nat.cast_pos.mpr hs
    rw [← add_div]
    exact (div_le_div_iff₀ hsp hdp).mpr (by simpa [one_add_one_eq_two] using hcoarse)
  have herr : (upper : ℝ) / ((scale * divisor : ℕ) : ℝ) + 1 / scale ≤
      TP.γ_ℓ (P.M₀ ^ 2) + 1 / ((P.d : ℝ) + 1) := by
    rw [hsplit]
    linarith only [hhi, herror]
  obtain ⟨mid, c, hr, h24, hm, hf, hcost⟩ :=
    prepareIntegerGrowthDivisor_runs (ω := ω) hp h75 h23 hfit hprecision he
  have keep (r : ℕ) (h24 : r ≠ 24 := by decide) (h25 : r ≠ 25 := by decide) := hf r h24 h25
  obtain ⟨out, hr', h83, h98, htable, hframe, hz'⟩ :=
    initRoundedIntegerThresholdTable_runs TP P (p := p) (ω := ω) hword hbase
      (hm.symm ▸ hz) ((keep 20).trans h20) (hsplit ▸ (keep 23).trans h23)
      h24 hs hd hupper hscale hTP hγM hγk (by rwa [hsplit]) herr
      ((keep 22).trans h22) ((keep 14).trans h14) ((keep 77).trans h77)
      ((keep 76).trans h76) ((keep 75).trans h75) hden hcapacity
  exact ⟨out, c + (50 * P.d + 89) + 1,
    runs_seq_iff.mpr (Or.inr ⟨mid, c, _, hr, hr', rfl⟩),
    h83, h98, htable, fun x hx => (hframe x hx).trans (congrFun hm x), hz', by omega⟩

end MinCostFlow.MinRatio
