module

public import MinCostFlow.MinRatio.InitStretchBounds
public import MinCostFlow.MinRatio.InitBucketSigmaLog
public import MinCostFlow.Expander.PathDSProg.RuntimeHelpers

/-!
# Runtime sparsifier length bounds

The length factor is the square of the maximum path bound. Compute
the two endpoint numerators before rounding back to the working scale.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM

/-- Compute the squared maximum for one pair of path endpoints. -/
@[expose] def initSparsifierLengthSquare (left right dest : ℕ) : Stmt :=
  .assign dest (.bin .add (.reg left) (.bin .sub (.reg right) (.reg left))) ;;
  .assign dest (.bin .mul (.reg dest) (.reg dest))

/-- Each endpoint is squared exactly when the product fits one word. -/
theorem initSparsifierLengthSquare_runs {w left right dest lo hi : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hl : st.regs left = lo) (hh : st.regs right = hi)
    (hword : (max lo hi) ^ 2 < 2 ^ w) :
    ∃ out, Runs w p ω (initSparsifierLengthSquare left right dest) st .normal out 11 ∧
      out.regs dest = (max lo hi) ^ 2 ∧ out.mem = st.mem ∧
      (∀ r ≠ dest, out.regs r = st.regs r) := by
  let bound := max lo hi
  have hbound : bound < 2 ^ w := by
    have hle : bound ≤ bound ^ 2 := by
      rcases Nat.eq_zero_or_pos bound with hz | hp
      · simp [hz]
      · simpa [pow_one] using Nat.pow_le_pow_right hp (show 1 ≤ 2 by decide)
    exact hle.trans_lt hword
  have hsub : hi - lo < 2 ^ w :=
    ((Nat.sub_le ..).trans (le_max_right lo hi)).trans_lt hbound
  have hsum : lo + (hi - lo) = bound := by dsimp [bound]; omega
  let mid := {st with regs := Function.update st.regs dest bound}
  let out := {mid with regs := Function.update mid.regs dest (bound ^ 2)}
  have hr₁ : Runs w p ω
      (.assign dest (.bin .add (.reg left) (.bin .sub (.reg right) (.reg left))))
      st .normal mid 6 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hl, hh, hsub, hsum, hbound],
      rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign dest (.bin .mul (.reg dest) (.reg dest))) mid .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, mid, ← pow_two, show bound ^ 2 < 2 ^ w from hword],
      rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 6, 4, hr₁, hr₂, rfl⟩),
    by simp [out, bound], rfl, fun r hr => by simp [out, mid, hr]⟩

/-- Compute the Section 8 length factor bounds at the working scale from
the four path-bound numerators. -/
@[expose] def initSparsifierLengthFactor : Stmt :=
  initSparsifierLengthSquare 39 40 31 ;;
  initSparsifierLengthSquare 41 42 32 ;;
  .assign 33 (.reg 4) ;;
  rescaleInitBucketSigmaLogBounds 50 52

/-- The lower and upper words enclose the concrete Section 8 length
factor. A lower path endpoint at least one gives a positive lower word. -/
theorem initSparsifierLengthFactor_runs
    (cDeg phiConst phiMin : ℝ) (paths : Spanner.PathDSTool) (M : ℕ)
    {w scale lo₁ lo₂ hi₁ hi₂ : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hs : st.regs 4 = scale) (hsPos : 0 < scale)
    (h39 : st.regs 39 = lo₁) (h40 : st.regs 40 = lo₂)
    (h41 : st.regs 41 = hi₁) (h42 : st.regs 42 = hi₂)
    (hlo₁ : (lo₁ : ℝ) / scale ≤ paths.γ_ExpPath phiMin M)
    (hhi₁ : paths.γ_ExpPath phiMin M ≤ (hi₁ : ℝ) / scale)
    (hlo₂ : (lo₂ : ℝ) / scale ≤ paths.γ_ExpPath phiConst (Spanner.capM_W cDeg phiMin M))
    (hhi₂ : paths.γ_ExpPath phiConst (Spanner.capM_W cDeg phiMin M) ≤ (hi₂ : ℝ) / scale)
    (hw : 1 < 2 ^ w) (hl : (max lo₁ lo₂) ^ 2 < 2 ^ w)
    (hh : (max hi₁ hi₂) ^ 2 + (scale - 1) < 2 ^ w) :
    ∃ out, Runs w p ω initSparsifierLengthFactor st .normal out 40 ∧
      (out.regs 50 : ℝ) / scale ≤ Spanner.capGammaL cDeg phiConst paths phiMin M ∧
      Spanner.capGammaL cDeg phiConst paths phiMin M ≤ (out.regs 52 : ℝ) / scale ∧
      (scale ≤ max lo₁ lo₂ → 0 < out.regs 50) ∧
      out.regs 50 ≤ out.regs 52 ∧ out.regs 52 < 2 ^ w ∧
      out.regs 50 = (max lo₁ lo₂) ^ 2 / scale ∧
      out.regs 52 = ((max hi₁ hi₂) ^ 2 + (scale - 1)) / scale ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 31 → r ≠ 32 → r ≠ 33 → r ≠ 50 → r ≠ 52 → out.regs r = st.regs r) := by
  obtain ⟨s₁, hr₁, h31, hm₁, hk₁⟩ :=
    initSparsifierLengthSquare_runs (p := p) (ω := ω) (dest := 31) h39 h40 hl
  obtain ⟨s₂, hr₂, h32, hm₂, hk₂⟩ :=
    initSparsifierLengthSquare_runs (p := p) (ω := ω) (dest := 32)
      ((hk₁ 41 (by decide)).trans h41) ((hk₁ 42 (by decide)).trans h42)
      ((Nat.le_add_right ..).trans_lt hh)
  let ready := {s₂ with regs := Function.update s₂.regs 33 scale}
  have hr₃ : Runs w p ω (.assign 33 (.reg 4)) s₂ .normal ready 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hk₂ 4 (by decide), hk₁ 4 (by decide), hs],
      rfl, rfl, rfl⟩
  obtain ⟨out, hr₄, hlo, hhi, hlower, hfit, hupper, hm, hk⟩ :=
    rescaleInitBucketSigmaLogBounds_runs (p := p) (ω := ω) (st := ready) (lower := 50) (upper := 52)
      (by simp [ready, hk₂ 31 (by decide), h31]) (by simp [ready, h32])
      (by simp [ready]) (by decide) (by decide) (by decide) hsPos hw hl hh
  have hsReal : 0 < (scale : ℝ) := by exact_mod_cast hsPos
  have hcast (n : ℕ) :
      (n : ℝ) / scale = ((n * scale : ℕ) : ℝ) / (scale : ℝ) ^ 2 := by
    rw [Nat.cast_mul, pow_two, mul_div_mul_right _ _ hsReal.ne']
  obtain ⟨hlo', hhi'⟩ :=
    initSparsifierLengthFactor_bounds cDeg phiConst phiMin paths M hsReal hlo₁ hhi₁ hlo₂ hhi₂
  refine ⟨out, ?_, ?_, ?_, ?_, ?_, hfit, ?_, ?_, hm.trans (hm₂.trans hm₁), ?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨s₁, 11, 28, hr₁,
      runs_seq_iff.mpr (Or.inr ⟨s₂, 11, 16, hr₂,
        runs_seq_iff.mpr (Or.inr ⟨ready, 2, 13, hr₃, hr₄, rfl⟩), rfl⟩), rfl⟩)
  · rw [hcast]
    exact (div_le_div_of_nonneg_right (by exact_mod_cast hlo) (by positivity)).trans hlo'
  · rw [hcast]
    exact hhi'.trans (div_le_div_of_nonneg_right (by exact_mod_cast hhi) (by positivity))
  · intro hle
    apply hlower 1
    rw [one_mul, pow_two]
    exact (hle.trans (Nat.le_mul_of_pos_right _ (hsPos.trans_le hle)))
  · apply Nat.le_of_mul_le_mul_right (c := scale)
    · have hmax := Nat.pow_le_pow_left (show max lo₁ lo₂ ≤ max hi₁ hi₂ by
        have h₁ := hlo₁.trans hhi₁
        have h₂ := hlo₂.trans hhi₂
        exact max_le_max
          (by exact_mod_cast (div_le_div_iff_of_pos_right hsReal).mp h₁)
          (by exact_mod_cast (div_le_div_iff_of_pos_right hsReal).mp h₂)) 2
      exact hlo.trans (hmax.trans hhi)
    · exact hsPos
  · exact le_antisymm ((Nat.le_div_iff_mul_le hsPos).mpr hlo)
      (hlower _ (Nat.div_mul_le_self _ _))
  · let n := (max hi₁ hi₂) ^ 2
    let q := (n + (scale - 1)) / scale
    have hround : n ≤ q * scale := by
      have hrem := Nat.mod_lt (n + (scale - 1)) hsPos
      have heq := Nat.mod_add_div (n + (scale - 1)) scale
      rw [Nat.mul_comm scale] at heq
      change (n + (scale - 1)) % scale + q * scale = n + (scale - 1) at heq
      omega
    refine le_antisymm (hupper q hround) ?_
    by_contra! h
    change out.regs 52 < q at h
    have hstep := Nat.mul_le_mul_right scale (Nat.succ_le_of_lt h)
    have hq := Nat.div_mul_le_self (n + (scale - 1)) scale
    change q * scale ≤ n + (scale - 1) at hq
    rw [Nat.succ_mul] at hstep
    change n ≤ out.regs 52 * scale at hhi
    omega
  · intro r h31 h32 h33 h50 h52
    exact (hk r h50 h52).trans ((by simp [ready, h33] : ready.regs r = s₂.regs r).trans
      ((hk₂ r h32).trans (hk₁ r h31)))

/-- Squaring the path enclosure and rounding it back to the original
scale gives a length enclosure with at most two extra rounding units. -/
theorem initSparsifierLengthSquare_gap {lo hi scale bound err : ℕ}
    (hs : 0 < scale) (hlo : lo ≤ hi) (hhi : hi ≤ bound * scale) (he : hi - lo ≤ err) :
    (hi ^ 2 + (scale - 1)) / scale - lo ^ 2 / scale ≤ 2 * bound * err + 2 := by
  have hdiff : (hi - lo) * (hi + lo) + lo ^ 2 = hi ^ 2 := by
    have heq : hi = lo + (hi - lo) := by omega
    conv_rhs => rw [heq]
    rw [show hi + lo = lo + (hi - lo) + lo by omega]
    ring
  have hsum : hi + lo ≤ 2 * (bound * scale) := by omega
  have hprod := Nat.mul_le_mul he hsum
  have hwidth : hi ^ 2 ≤ lo ^ 2 + (2 * bound * err) * scale := by
    have heq : err * (2 * (bound * scale)) = (2 * bound * err) * scale := by ring
    rw [heq] at hprod
    exact hdiff ▸ (Nat.add_le_add_right hprod (lo ^ 2)).trans_eq (Nat.add_comm _ _)
  let q := lo ^ 2 / scale
  have hrem := Nat.mod_lt (lo ^ 2) hs
  have hq : lo ^ 2 % scale + q * scale = lo ^ 2 := by
    simpa only [q, Nat.mul_comm scale] using Nat.mod_add_div (lo ^ 2) scale
  have hupper : (hi ^ 2 + (scale - 1)) / scale ≤ q + (2 * bound * err + 2) := by
    apply Nat.div_le_of_le_mul
    rw [Nat.mul_add, Nat.mul_add]
    have hscale : scale * 2 = 2 * scale := Nat.mul_comm _ _
    have hbudget : scale * (2 * bound * err) = (2 * bound * err) * scale := Nat.mul_comm _ _
    rw [hscale, hbudget, Nat.mul_comm scale q]
    omega
  exact Nat.sub_le_iff_le_add.mpr (hupper.trans_eq (Nat.add_comm _ _))

/-- Squared path endpoints stay within the square of the factor bound
after rescaling, including the upward rounding at the upper endpoint. -/
theorem initSparsifierLengthSquare_upper {hi scale bound : ℕ}
    (hs : 0 < scale) (hhi : hi ≤ bound * scale) :
    (hi ^ 2 + (scale - 1)) / scale ≤ bound ^ 2 * scale := by
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hs).mpr
  have hpow : hi ^ 2 ≤ bound ^ 2 * scale * scale := by
    calc
      _ ≤ (bound * scale) ^ 2 := Nat.pow_le_pow_left hhi _
      _ = _ := by ring
  rw [Nat.succ_mul]
  omega

/-- Read the path edge cap and evaluate the exponent of the cited
power-of-two length bound using the shared fourth-root procedure. -/
@[expose] def initSparsifierPathGammaExponent (Kγ : ℕ) : Stmt :=
  .assign 24 (.bin .mul (.const 3) (.reg 23)) ;;
  Expander.PathDSProg.csGammaExpBlock Kγ 24 37 31 32 33 36

/-- The output is the integer exponent needed for both terms in the
concrete path length formula. -/
theorem initSparsifierPathGammaExponent_runs {w Kγ M : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hM : st.regs 23 = M) (hK : Kγ < 2 ^ w) (hword : 3 * M < 2 ^ w)
    (hcube : (Nat.log 2 (3 * M) + 2) ^ 4 < 2 ^ w)
    (hexp : Expander.PathDSProg.csGammaExp Kγ (3 * M) < 2 ^ w)
    (hw : 4 < 2 ^ w) :
    ∃ out c, Runs w p ω (initSparsifierPathGammaExponent Kγ) st .normal out c ∧
      out.regs 37 = Expander.PathDSProg.csGammaExp Kγ (3 * M) ∧
      out.mem = st.mem ∧
      (∀ r, r ≠ 24 → r ≠ 37 → r ≠ 31 → r ≠ 32 → r ≠ 33 → r ≠ 36 →
        out.regs r = st.regs r) ∧ c ≤ 35 * (Nat.log 2 (3 * M) + 1) + 65 := by
  let mid := {st with regs := Function.update st.regs 24 (3 * M)}
  have hr : Runs w p ω (.assign 24 (.bin .mul (.const 3) (.reg 23))) st .normal mid 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hM, hword, show 3 < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have ht := Expander.PathDSProg.csGammaExpBlock_triple (w := w) (p := p)
    Kγ 24 37 31 32 33 36 (3 * M) (by decide) (by decide) hK hword hcube hexp hw.le
    mid (by simp [mid])
  obtain ⟨result, out, c, hr', hpost, hcost⟩ := ht mid ω rfl
  change c ≤ 35 * (Nat.log 2 (3 * M) + 1) + 60 at hcost
  cases result <;> simp only [normalPost] at hpost
  · obtain ⟨he, hm, _, hk⟩ := hpost
    exact ⟨out, c + 5, runs_seq_iff.mpr (Or.inr ⟨mid, 4, c, hr, hr', by omega⟩),
      he, hm, fun r h24 h37 h31 h32 h33 h36 =>
        (hk r h37 h31 h32 h33 h36).trans (by simp [mid, h24]), by omega⟩

/-- Run the shared path parameter calculation in a call frame so that its
scratch registers do not overwrite the chain parameters. -/
@[expose] def initSparsifierPathQBody : Stmt :=
  .assign 20 (.reg 0) ;; Expander.PathDSProg.qOfStmt ;; .ret (.reg 21)

/-- The path exponent multiplier is computed from the runtime edge cap. -/
@[expose] def initSparsifierPathQContract (w : ℕ) : Contract where
  pre args _ := ∃ M, args = [M] ∧ M + 2 < 2 ^ w ∧
    (Expander.PathDSProg.qRoot M + 1) ^ 8 < 2 ^ w ∧
    Expander.PathDSProg.qRoot M + 2 < 2 ^ w ∧ 4 ≤ 2 ^ w
  post args mem ret out := out = mem ∧ ret = Expander.qOf (args.getD 0 0)
  cost args _ := 65 * (Nat.log 2 (args.getD 0 0 + 2) + 1) + 86

/-- The shared eighth-root calculation implements the one-argument call. -/
theorem initSparsifierPathQ_meetsContract {w entry : ℕ} {p : Program}
    (hp : p.HasAt entry [initSparsifierPathQBody]) :
    MeetsContract w p entry (initSparsifierPathQContract w) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω _ hpre
  obtain ⟨M, rfl, hm, hq8, hq2, hw⟩ := hpre
  let st := startState [M] mem pos
  let ready := {st with regs := Function.update st.regs 20 M}
  have hmove : Runs w p ω (.assign 20 (.reg 0)) st .normal ready 2 :=
    runs_assign_iff.mpr ⟨M, rfl, rfl, rfl, rfl⟩
  have ht := Expander.PathDSProg.qOfStmt_triple (w := w) (p := p) ready (by simp [ready])
    hm hq8 hq2 hw
  obtain ⟨result, out, c, hr, hpost, hc⟩ := ht ready ω rfl
  change c ≤ 65 * (Nat.log 2 (M + 2) + 1) + 80 at hc
  cases result <;> simp only [normalPost] at hpost
  obtain ⟨hval, hmem, _, _⟩ := hpost
  have hret : Runs w p ω (.ret (.reg 21)) out (.returned (out.regs 21)) out 2 :=
    runs_ret_iff.mpr ⟨_, rfl, rfl, rfl, rfl⟩
  refine ⟨.returned (out.regs 21), out, c + 6, ?_, ⟨hmem, hval⟩, ?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨ready, 2, c + 3, hmove,
      runs_seq_iff.mpr (Or.inr ⟨out, c, 2, hr, hret, by omega⟩), by omega⟩)
  · change c + 6 ≤ 65 * (Nat.log 2 (M + 2) + 1) + 86
    omega

/-- Read the runtime path edge cap and save its exponent multiplier. -/
@[expose] def initSparsifierPathQ (entry : ℕ) : Stmt :=
  .call 38 entry [.reg 23]

/-- The shared path arithmetic changes only the multiplier register. -/
theorem initSparsifierPathQ_runs {w entry M : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p entry (initSparsifierPathQContract w))
    (hM : st.regs 23 = M) (hword : M + 2 < 2 ^ w)
    (hq8 : (Expander.PathDSProg.qRoot M + 1) ^ 8 < 2 ^ w)
    (hq2 : Expander.PathDSProg.qRoot M + 2 < 2 ^ w) (hw : 4 ≤ 2 ^ w) :
    ∃ out c, Runs w p ω (initSparsifierPathQ entry) st .normal out c ∧
      out.regs 38 = Expander.qOf M ∧ out.mem = st.mem ∧
      (∀ r ≠ 38, out.regs r = st.regs r) ∧ c ≤ 65 * (Nat.log 2 (M + 2) + 1) + 88 := by
  have hargs : evalArgs w st [.reg 23] = some [M] := by
    simp [evalArgs, Expr.eval, hM]
  have hwords : ∀ x ∈ [M], x < 2 ^ w := by
    simpa using (show M < 2 ^ w by omega)
  obtain ⟨out, c, ret, hr, hp, hret, hk, hc⟩ :=
    runs_call_of_meetsContract (r := 38) himpl hargs hwords ⟨M, rfl, hword, hq8, hq2, hw⟩ ω
  obtain ⟨hm, hq⟩ := hp
  change ret = Expander.qOf M at hq
  change c ≤ 1 + (65 * (Nat.log 2 (M + 2) + 1) + 86) + 1 at hc
  exact ⟨out, c, hr, hret.trans hq, hm, hk, by omega⟩

/-- The cited path bound is a power of two, so its logarithm is obtained
by multiplying the integer exponent by the already available log-two interval. -/
theorem initSparsifierPathGammaLog_bounds (Kγ M : ℕ) {logLo logHi : ℝ}
    (hlo : logLo ≤ Real.log 2) (hhi : Real.log 2 ≤ logHi) :
    let exponent := Kγ * (Nat.sqrt (Nat.sqrt ((Nat.log 2 (3 * M) + 1) ^ 3)) + 1)
    (exponent : ℝ) * logLo ≤ Real.log (Cited.csGamma Kγ (3 * M)) ∧
      Real.log (Cited.csGamma Kγ (3 * M)) ≤ (exponent : ℝ) * logHi := by
  dsimp only [Cited.csGamma]
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  exact ⟨mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg _),
    mul_le_mul_of_nonneg_left hhi (Nat.cast_nonneg _)⟩

/-- Multiply the retained log-two interval by the computed path exponent. -/
@[expose] def initSparsifierPathGammaLog : Stmt :=
  .assign 34 (.bin .mul (.reg 37) (.reg 28)) ;;
  .assign 35 (.bin .mul (.reg 37) (.reg 29))

/-- Both computed words enclose the logarithm at the original scale. -/
theorem initSparsifierPathGammaLog_runs {w Kγ M scale lo hi : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hexp : st.regs 37 = Expander.PathDSProg.csGammaExp Kγ (3 * M))
    (hl : st.regs 28 = lo) (hh : st.regs 29 = hi) (hord : lo ≤ hi)
    (hlo : (lo : ℝ) / scale ≤ Real.log 2) (hhi : Real.log 2 ≤ (hi : ℝ) / scale)
    (hfit : Expander.PathDSProg.csGammaExp Kγ (3 * M) * hi < 2 ^ w) :
    ∃ out, Runs w p ω initSparsifierPathGammaLog st .normal out 9 ∧
      (out.regs 34 : ℝ) / scale ≤ Real.log (Cited.csGamma Kγ (3 * M)) ∧
      Real.log (Cited.csGamma Kγ (3 * M)) ≤ (out.regs 35 : ℝ) / scale ∧
      out.regs 34 = Expander.PathDSProg.csGammaExp Kγ (3 * M) * lo ∧
      out.regs 35 = Expander.PathDSProg.csGammaExp Kγ (3 * M) * hi ∧
      out.mem = st.mem ∧ (∀ r, r ≠ 34 → r ≠ 35 → out.regs r = st.regs r) := by
  let e := Expander.PathDSProg.csGammaExp Kγ (3 * M)
  have hL : e * lo < 2 ^ w := (Nat.mul_le_mul_left e hord).trans_lt hfit
  let mid := {st with regs := Function.update st.regs 34 (e * lo)}
  let out := {mid with regs := Function.update mid.regs 35 (e * hi)}
  have hr₁ : Runs w p ω (.assign 34 (.bin .mul (.reg 37) (.reg 28))) st .normal mid 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hexp, hl, show e * lo < _ from hL, e],
      rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign 35 (.bin .mul (.reg 37) (.reg 29))) mid .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, mid, hexp, hh, hfit, e],
      rfl, rfl, rfl⟩
  have hb := initSparsifierPathGammaLog_bounds Kγ M hlo hhi
  change (e : ℝ) * ((lo : ℝ) / scale) ≤ _ ∧ _ ≤ (e : ℝ) * ((hi : ℝ) / scale) at hb
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 4, 4, hr₁, hr₂, rfl⟩), ?_, ?_, by simp [out, mid, e], by simp [out, e], rfl, ?_⟩
  · simpa only [out, mid, Function.update_of_ne (by decide : (34 : ℕ) ≠ 35),
      Function.update_self, Nat.cast_mul, mul_div_assoc] using hb.1
  · simpa only [out, Function.update_self, Nat.cast_mul, mul_div_assoc] using hb.2
  · intro r h34 h35
    simp [out, mid, h34, h35]

/-- Compute the cited path exponent and then its logarithm bounds. -/
@[expose] def initSparsifierCitedPathLog (Kγ : ℕ) : Stmt :=
  initSparsifierPathGammaExponent Kγ ;; initSparsifierPathGammaLog

/-- The combined fragment needs only the runtime path edge cap and the
cached log-two interval. -/
theorem initSparsifierCitedPathLog_runs {w Kγ M scale lo hi : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hM : st.regs 23 = M) (hK : Kγ < 2 ^ w) (hword : 3 * M < 2 ^ w)
    (hcube : (Nat.log 2 (3 * M) + 2) ^ 4 < 2 ^ w)
    (hexp : Expander.PathDSProg.csGammaExp Kγ (3 * M) < 2 ^ w) (hw : 4 < 2 ^ w)
    (hl : st.regs 28 = lo) (hh : st.regs 29 = hi) (hord : lo ≤ hi)
    (hlo : (lo : ℝ) / scale ≤ Real.log 2) (hhi : Real.log 2 ≤ (hi : ℝ) / scale)
    (hfit : Expander.PathDSProg.csGammaExp Kγ (3 * M) * hi < 2 ^ w) :
    ∃ out c, Runs w p ω (initSparsifierCitedPathLog Kγ) st .normal out c ∧
      (out.regs 34 : ℝ) / scale ≤ Real.log (Cited.csGamma Kγ (3 * M)) ∧
      Real.log (Cited.csGamma Kγ (3 * M)) ≤ (out.regs 35 : ℝ) / scale ∧
      out.regs 34 = Expander.PathDSProg.csGammaExp Kγ (3 * M) * lo ∧
      out.regs 35 = Expander.PathDSProg.csGammaExp Kγ (3 * M) * hi ∧
      out.regs 37 = Expander.PathDSProg.csGammaExp Kγ (3 * M) ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 24 → r ≠ 31 → r ≠ 32 → r ≠ 33 → r ≠ 34 → r ≠ 35 →
        r ≠ 36 → r ≠ 37 → out.regs r = st.regs r) ∧
      c ≤ 35 * (Nat.log 2 (3 * M) + 1) + 75 := by
  obtain ⟨mid, c, hr, he, hm, hk, hc⟩ :=
    initSparsifierPathGammaExponent_runs (ω := ω) hM hK hword hcube hexp hw
  obtain ⟨out, hr', hlo', hhi', h34, h35, hm', hk'⟩ :=
    initSparsifierPathGammaLog_runs (ω := ω) he
      ((hk 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hl)
      ((hk 29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hh)
      hord hlo hhi hfit
  exact ⟨out, c + 10, runs_seq_iff.mpr (Or.inr ⟨mid, c, 9, hr, hr', rfl⟩),
    hlo', hhi', h34, h35, (hk' 37 (by decide) (by decide)).trans he, hm'.trans hm,
    fun r h24 h31 h32 h33 h34 h35 h36 h37 =>
      (hk' r h34 h35).trans (hk r h24 h37 h31 h32 h33 h36), by omega⟩

/-- The powered part of the path bound is an exponential of a
nonnegative factor times the logarithm of the cited length bound. -/
theorem initSparsifierPathPower_bounds (Kγ : ℕ) (K : ℝ) (M : ℕ)
    {lo hi : ℝ} (hbase : 0 < MinCostFlow.Cited.csGamma Kγ (3 * M))
    (hl : lo ≤ Real.log (MinCostFlow.Cited.csGamma Kγ (3 * M)))
    (hh : Real.log (MinCostFlow.Cited.csGamma Kγ (3 * M)) ≤ hi) :
    let factor := max K 1 * (Expander.qOf M : ℝ)
    Real.exp (factor * lo) ≤ (MinCostFlow.Cited.csGamma Kγ (3 * M) : ℝ) ^ factor ∧
      (MinCostFlow.Cited.csGamma Kγ (3 * M) : ℝ) ^ factor ≤ Real.exp (factor * hi) := by
  let factor := max K 1 * (Expander.qOf M : ℝ)
  have hf : 0 ≤ factor :=
    mul_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_right K 1)) (Nat.cast_nonneg _)
  have hb : (0 : ℝ) < MinCostFlow.Cited.csGamma Kγ (3 * M) := by exact_mod_cast hbase
  change Real.exp (factor * lo) ≤ _ ∧ _ ≤ Real.exp (factor * hi)
  rw [Real.rpow_def_of_pos hb, mul_comm (Real.log _) factor]
  exact ⟨Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hl hf),
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hh hf)⟩

/-- Scale the exponent of the path power using separate intervals for
the witness constant and the logarithm. The integer multiplier is exact. -/
theorem initSparsifierPathExponent_bounds (K : ℝ) (M scale kLo kHi logLo logHi : ℕ)
    {value : ℝ} (hs : 0 < (scale : ℝ))
    (hkLo : (kLo : ℝ) / scale ≤ max K 1) (hkHi : max K 1 ≤ (kHi : ℝ) / scale)
    (hlLo : (logLo : ℝ) / scale ≤ value) (hlHi : value ≤ (logHi : ℝ) / scale) :
    let q := Expander.qOf M
    let target := max K 1 * (q : ℝ) * value
    ((kLo * q * logLo : ℕ) : ℝ) / (scale : ℝ) ^ 2 ≤ target ∧
      target ≤ ((kHi * q * logHi : ℕ) : ℝ) / (scale : ℝ) ^ 2 := by
  dsimp only
  have hk : 0 ≤ max K 1 := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_right _ _)
  have hv : 0 ≤ value := (by positivity : 0 ≤ (logLo : ℝ) / scale).trans hlLo
  have hq : (0 : ℝ) ≤ Expander.qOf M := Nat.cast_nonneg _
  have hlo := mul_le_mul (mul_le_mul_of_nonneg_right hkLo hq) hlLo
    (by positivity) (mul_nonneg hk hq)
  have hhi := mul_le_mul (mul_le_mul_of_nonneg_right hkHi hq) hlHi hv (by positivity)
  have prep (k l : ℕ) :
      (k : ℝ) / scale * (Expander.qOf M : ℝ) * ((l : ℝ) / scale) =
        ((k * Expander.qOf M * l : ℕ) : ℝ) / (scale : ℝ) ^ 2 := by
    push_cast
    field_simp
  rw [prep] at hlo hhi
  exact ⟨hlo, hhi⟩

/-- Produce scaled exponent words for the two exponential calls. -/
@[expose] def initSparsifierPathExponent : Stmt :=
  .assign 31 (.bin .mul (.bin .mul (.reg 39) (.reg 38)) (.reg 34)) ;;
  .assign 32 (.bin .mul (.bin .mul (.reg 40) (.reg 38)) (.reg 35))

/-- The two products give the exponent bounds at the squared scale. -/
theorem initSparsifierPathExponent_runs (K : ℝ) (M scale kLo kHi logLo logHi : ℕ)
    {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State} {value : ℝ}
    (hs : 0 < (scale : ℝ))
    (h39 : st.regs 39 = kLo) (h40 : st.regs 40 = kHi) (h38 : st.regs 38 = Expander.qOf M)
    (h34 : st.regs 34 = logLo) (h35 : st.regs 35 = logHi)
    (hkLo : (kLo : ℝ) / scale ≤ max K 1) (hkHi : max K 1 ≤ (kHi : ℝ) / scale)
    (hlLo : (logLo : ℝ) / scale ≤ value) (hlHi : value ≤ (logHi : ℝ) / scale)
    (hkl : kLo * Expander.qOf M < 2 ^ w) (hkh : kHi * Expander.qOf M < 2 ^ w)
    (hlo : kLo * Expander.qOf M * logLo < 2 ^ w)
    (hhi : kHi * Expander.qOf M * logHi < 2 ^ w) :
    let target := max K 1 * (Expander.qOf M : ℝ) * value
    ∃ out, Runs w p ω initSparsifierPathExponent st .normal out 13 ∧
      (out.regs 31 : ℝ) / (scale : ℝ) ^ 2 ≤ target ∧
      target ≤ (out.regs 32 : ℝ) / (scale : ℝ) ^ 2 ∧
      out.regs 31 = kLo * Expander.qOf M * logLo ∧
      out.regs 32 = kHi * Expander.qOf M * logHi ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 31 → r ≠ 32 → out.regs r = st.regs r) := by
  let mid := {st with regs := Function.update st.regs 31 (kLo * Expander.qOf M * logLo)}
  let out := {mid with regs := Function.update mid.regs 32 (kHi * Expander.qOf M * logHi)}
  have hr₁ : Runs w p ω (.assign 31 (.bin .mul (.bin .mul (.reg 39) (.reg 38)) (.reg 34)))
      st .normal mid 6 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, h39, h38, h34, hkl, hlo],
      rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign 32 (.bin .mul (.bin .mul (.reg 40) (.reg 38)) (.reg 35)))
      mid .normal out 6 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, mid, h40, h38, h35, hkh, hhi],
      rfl, rfl, rfl⟩
  have hb := initSparsifierPathExponent_bounds K M scale kLo kHi logLo logHi hs hkLo hkHi hlLo hlHi
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 6, 6, hr₁, hr₂, rfl⟩),
    by simpa [out, mid] using hb.1, by simpa [out] using hb.2, by simp [out, mid], by simp [out],
    rfl, fun r h31 h32 => by simp [out, mid, h31, h32]⟩

/-- Recover the squared scale from the current precision after the
cited exponent routine has used register 33 as scratch. -/
@[expose] def setInitSparsifierPathSquaredScale : Stmt :=
  .assign 33 (.bin .shiftLeft (.const 1) (.bin .add (.reg 68) (.reg 68)))

/-- The squared scale word is computed from the runtime precision. -/
theorem setInitSparsifierPathSquaredScale_runs {w precision : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hp : st.regs 68 = precision) (hwidth : precision + precision < w) :
    ∃ out, Runs w p ω setInitSparsifierPathSquaredScale st .normal out 6 ∧
      out.regs 33 = 2 ^ (precision + precision) ∧ out.mem = st.mem ∧
      (∀ r ≠ 33, out.regs r = st.regs r) := by
  let scale := 2 ^ (precision + precision)
  let out := {st with regs := Function.update st.regs 33 scale}
  have hw : scale < 2 ^ w := Nat.pow_lt_pow_right (by decide) hwidth
  have hone : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have hw' : precision + precision < 2 ^ w :=
    hwidth.trans_le (Nat.le_of_lt (Nat.lt_two_pow_self (n := w)))
  have hr : Runs w p ω setInitSparsifierPathSquaredScale st .normal out 6 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, hp, hone, hw', scale, Nat.shiftLeft_eq,
        show 2 ^ (precision + precision) < 2 ^ w from hw],
      rfl, rfl, rfl⟩
  exact ⟨out, hr, by simp [out, scale], rfl, fun r h => by simp [out, h]⟩

/-- Prepare the logarithm endpoints and squared denominator used by
the powered path calculation. -/
@[expose] def prepareInitSparsifierPathLog (Kγ : ℕ) : Stmt :=
  initSparsifierCitedPathLog Kγ ;; setInitSparsifierPathSquaredScale

/-- The prepared numerator words come from the cached log-two interval
and the cited exponent at the runtime edge cap. -/
theorem prepareInitSparsifierPathLog_runs {w Kγ M precision lo hi : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hM : st.regs 23 = M) (hK : Kγ < 2 ^ w) (hword : 3 * M < 2 ^ w)
    (hcube : (Nat.log 2 (3 * M) + 2) ^ 4 < 2 ^ w)
    (hexp : Expander.PathDSProg.csGammaExp Kγ (3 * M) < 2 ^ w) (hw : 4 < 2 ^ w)
    (hl : st.regs 28 = lo) (hh : st.regs 29 = hi) (hord : lo ≤ hi)
    (hlo : (lo : ℝ) / (2 ^ precision : ℕ) ≤ Real.log 2)
    (hhi : Real.log 2 ≤ (hi : ℝ) / (2 ^ precision : ℕ))
    (hfit : Expander.PathDSProg.csGammaExp Kγ (3 * M) * hi < 2 ^ w)
    (hP : st.regs 68 = precision) (hwidth : precision + precision < w) :
    ∃ out c, Runs w p ω (prepareInitSparsifierPathLog Kγ) st .normal out c ∧
      (out.regs 34 : ℝ) / (2 ^ precision : ℕ) ≤ Real.log (Cited.csGamma Kγ (3 * M)) ∧
      Real.log (Cited.csGamma Kγ (3 * M)) ≤ (out.regs 35 : ℝ) / (2 ^ precision : ℕ) ∧
      out.regs 34 = Expander.PathDSProg.csGammaExp Kγ (3 * M) * lo ∧
      out.regs 35 = Expander.PathDSProg.csGammaExp Kγ (3 * M) * hi ∧
      out.regs 37 = Expander.PathDSProg.csGammaExp Kγ (3 * M) ∧
      out.regs 33 = 2 ^ (precision + precision) ∧ out.mem = st.mem ∧
      (∀ r, r ∉ ([24, 31, 32, 33, 34, 35, 36, 37] : List ℕ) → out.regs r = st.regs r) ∧
      c ≤ 35 * (Nat.log 2 (3 * M) + 1) + 82 := by
  obtain ⟨mid, cost, hr₁, lb, ub, h34, h35, h37, hm₁, hk₁, hc⟩ :=
    initSparsifierCitedPathLog_runs (ω := ω) hM hK hword hcube hexp hw hl hh hord hlo hhi hfit
  obtain ⟨out, hr₂, h33, hm₂, hk₂⟩ :=
    setInitSparsifierPathSquaredScale_runs (p := p) (ω := ω)
      ((hk₁ 68 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans hP) hwidth
  have hl' := hk₂ 34 (by decide)
  have hu' := hk₂ 35 (by decide)
  refine ⟨out, cost + 7, runs_seq_iff.mpr (Or.inr ⟨mid, cost, 6, hr₁, hr₂, by omega⟩),
    hl'.symm ▸ lb, hu'.symm ▸ ub, hl'.trans h34, hu'.trans h35,
    (hk₂ 37 (by decide)).trans h37, h33, hm₂.trans hm₁, ?_, by omega⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h24, h31, h32, h33', h34', h35', h36, h37'⟩ := hr
  exact (hk₂ r h33').trans (hk₁ r h24 h31 h32 h33' h34' h35' h36 h37')

end MinCostFlow.MinRatio
