module

public import MinCostFlow.MinRatio.RebuildGuard
public import MinCostFlow.MinRatio.InitStretchBounds
public import MinCostFlow.Expander.Section8Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import MinCostFlow.MinRatio.ShiftForestScan
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# Sparse-core stretch enclosure at initialization

Form the two terms of the model stretch from scaled integer endpoints
and put both terms on a common scale for the level-size calculation.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain

/-- Bounds on the sparsifier stretch and logarithmic factor propagate
through both terms of the sparse-core stretch in Lemma 5.17. -/
theorem initSparseCoreStretch_bounds (E : SparseCore.SparseCoreEnv) (m : ℕ)
    {stretchLower stretchUpper logLower logUpper : ℝ}
    (hs : 0 ≤ stretchLower) (hl : 0 ≤ logLower)
    (hslo : stretchLower ≤ (E.P_fn m).γ_ℓ) (hshi : (E.P_fn m).γ_ℓ ≤ stretchUpper)
    (hllo : logLower ≤ SparseCore.coreLambdaS (E.P_fn m) m)
    (hlhi : SparseCore.coreLambdaS (E.P_fn m) m ≤ logUpper) :
    let cap := (E.B_fn m : ℝ) * (2 * (E.d_fn m : ℝ) + 190)
    let factor := ((E.L : ℝ) + 1) * (E.P_fn m).K_s
    let bound := fun stretch log : ℝ =>
      max ((3 : ℝ) ^ E.L * stretch ^ (E.L + 1))
        (11 * (factor * (stretch * log) * cap + 115))
    bound stretchLower logLower ≤ SparseCore.gammaLEnv E m ∧
      SparseCore.gammaLEnv E m ≤ bound stretchUpper logUpper := by
  dsimp only
  unfold SparseCore.gammaLEnv SparseCore.coreE82Len
  have hks : 0 ≤ (E.P_fn m).K_s := (E.P_fn m).hK_s.trans' (by norm_num)
  have hfactor : 0 ≤ ((E.L : ℝ) + 1) * (E.P_fn m).K_s := by positivity
  have hcap : 0 ≤ (E.B_fn m : ℝ) * (2 * (E.d_fn m : ℝ) + 190) := by positivity
  have hmono (a b c d : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hab : a ≤ b) (hcd : c ≤ d) :
      ((E.L : ℝ) + 1) * (E.P_fn m).K_s * (a * c) *
          ((E.B_fn m : ℝ) * (2 * (E.d_fn m : ℝ) + 190)) ≤
        ((E.L : ℝ) + 1) * (E.P_fn m).K_s * (b * d) *
          ((E.B_fn m : ℝ) * (2 * (E.d_fn m : ℝ) + 190)) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (mul_le_mul hab hcd hc (ha.trans hab)) hfactor) hcap
  constructor
  · apply max_le_max
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hslo _) (by positivity)
    · have ht := hmono _ _ _ _ hs hl hslo hllo
      convert mul_le_mul_of_nonneg_left (add_le_add_right ht 115) (by norm_num : (0 : ℝ) ≤ 11) using 1 <;> ring
  · apply max_le_max
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hs.trans hslo) hshi _) (by positivity)
    · have ht := hmono _ _ _ _ (hs.trans hslo) (hl.trans hllo) hshi hlhi
      convert mul_le_mul_of_nonneg_left (add_le_add_right ht 115) (by norm_num : (0 : ℝ) ≤ 11) using 1 <;> ring

/-- In the concrete chain the sparsity exponent is at most one.
The logarithmic factor therefore uses either the constant one or
one plus the logarithm of the runtime graph bound. -/
theorem initSparseCoreLogFactor_eq (E : SparseCore.SparseCoreEnv) (m : ℕ)
    (hp : (E.P_fn m).p_s ≤ 1) :
    SparseCore.coreLambdaS (E.P_fn m) m =
      if (E.P_fn m).p_s = 0 then 1
      else 1 + Real.log ((SparseCore.coreNMax m : ℝ) + (m : ℝ) + 2) := by
  unfold SparseCore.coreLambdaS
  by_cases hz : (E.P_fn m).p_s = 0
  · simp [hz]
  · have hOne : (E.P_fn m).p_s = 1 := by omega
    simp [hOne]

/-- Prepare the graph bound for the logarithm in the sparse-core stretch.
Register 24 holds the sparse-core edge bound and register 92 receives
the argument before the logarithm loader adds two. -/
@[expose] def initSparseCoreLogInput : Stmt :=
  .assign 92 (.bin .mul (.reg 24)
    (.bin .add (.bin .mul (.const 2) (.reg 24)) (.const 60)))

/-- The shared logarithm loader sees the sparse-core graph bound. -/
theorem initSparseCoreLogInput_runs {w m : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hm : st.regs 24 = m) (hw : 60 < 2 ^ w)
    (hlinear : 2 * m + 60 < 2 ^ w)
    (hproduct : m * (2 * m + 60) < 2 ^ w) :
    ∃ out, Runs w p ω initSparseCoreLogInput st .normal out 8 ∧
      out.regs 92 = SparseCore.coreNMax m + m ∧
      (∀ r ≠ 92, out.regs r = st.regs r) ∧ out.mem = st.mem ∧ out.pos = st.pos := by
  let out := { st with regs := Function.update st.regs 92 (m * (2 * m + 60)) }
  have he : m * (2 * m + 60) = SparseCore.coreNMax m + m := by
    unfold SparseCore.coreNMax SparseCore.coreSplitMax
    ring
  refine ⟨out, ?_, by simpa [out] using he, fun r hr => by simp [out, hr], rfl, rfl⟩
  apply runs_assign_iff.mpr
  exact ⟨_, by simp [Expr.eval, BinOp.eval, hm, hw, hlinear, hproduct,
    show 2 * m < 2 ^ w by omega, show 2 < 2 ^ w by omega], rfl, rfl, rfl⟩

/-- The logarithm approximation gives scaled endpoints for the sparsity
factor when the sparsity exponent is one. With exponent zero, both
endpoints encode one exactly. -/
theorem initSparseCoreLogFactor_scaledBounds (E : SparseCore.SparseCoreEnv) (m : ℕ)
    (hp : (E.P_fn m).p_s ≤ 1) (approx error scale : ℕ) (hs : 0 < scale)
    (herr : |(approx : ℝ) / scale -
      Real.log ((SparseCore.coreNMax m : ℝ) + (m : ℝ) + 2)| ≤ (error : ℝ) / scale) :
    let lower := if (E.P_fn m).p_s = 0 then scale else scale + (approx - error)
    let upper := if (E.P_fn m).p_s = 0 then scale else scale + (approx + error)
    (lower : ℝ) / scale ≤ SparseCore.coreLambdaS (E.P_fn m) m ∧
      SparseCore.coreLambdaS (E.P_fn m) m ≤ (upper : ℝ) / scale := by
  dsimp only
  rw [initSparseCoreLogFactor_eq E m hp]
  have hs' : (0 : ℝ) < scale := Nat.cast_pos.mpr hs
  by_cases hz : (E.P_fn m).p_s = 0
  · simp [hz, hs'.ne']
  · simp only [hz, ↓reduceIte, Nat.cast_add, add_div, div_self hs'.ne']
    obtain ⟨hl, hu⟩ := abs_le.mp herr
    constructor
    · by_cases hle : error ≤ approx
      · rw [Nat.cast_sub hle, sub_div]
        linarith only [hu]
      · rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hle), Nat.cast_zero, zero_div, add_zero]
        exact le_add_of_nonneg_right (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (SparseCore.coreNMax m), Nat.cast_nonneg (α := ℝ) m]))
    · linarith only [hl]

/-- Form the endpoints from the logarithm enclosure in registers 2
through 4 and the sparsity exponent in register 25. -/
@[expose] def prepareInitSparseCoreLogFactor : Stmt :=
  .assign 26 (.bin .add (.reg 4) (.bin .mul (.reg 25) (.bin .sub (.reg 2) (.reg 3)))) ;;
  .assign 27 (.bin .add (.reg 4) (.bin .mul (.reg 25) (.bin .add (.reg 2) (.reg 3))))

/-- For exponent zero or one, the two word operations give the scaled
sparsity-factor enclosure. The upper endpoint bounds all intermediate words. -/
theorem prepareInitSparseCoreLogFactor_runs (E : SparseCore.SparseCoreEnv) (m : ℕ)
    {w approx error scale : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hp : (E.P_fn m).p_s ≤ 1) (hscale : 0 < scale)
    (ha : st.regs 2 = approx) (he : st.regs 3 = error) (hs : st.regs 4 = scale)
    (hps : st.regs 25 = (E.P_fn m).p_s)
    (hword : scale + (approx + error) < 2 ^ w)
    (herr : |(approx : ℝ) / scale -
      Real.log ((SparseCore.coreNMax m : ℝ) + (m : ℝ) + 2)| ≤ (error : ℝ) / scale) :
    ∃ out, Runs w p ω prepareInitSparseCoreLogFactor st .normal out 17 ∧
      (out.regs 26 : ℝ) / scale ≤ SparseCore.coreLambdaS (E.P_fn m) m ∧
      SparseCore.coreLambdaS (E.P_fn m) m ≤ (out.regs 27 : ℝ) / scale ∧
      scale ≤ out.regs 26 ∧ scale ≤ out.regs 27 ∧
      out.regs 26 ≤ out.regs 27 ∧ out.regs 27 ≤ scale + (approx + error) ∧
      out.regs 27 - out.regs 26 ≤ 2 * error ∧
      (∀ r, r ≠ 26 → r ≠ 27 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  let ps := (E.P_fn m).p_s
  let lo := scale + ps * (approx - error)
  let hi := scale + ps * (approx + error)
  have hp' : ps ≤ 1 := hp
  have hm (n : ℕ) : ps * n ≤ n := by
    simpa only [one_mul] using Nat.mul_le_mul_right n hp'
  have hlo : approx - error < 2 ^ w := by omega
  have hhi : approx + error < 2 ^ w := by omega
  have hlow : lo < 2 ^ w := by
    dsimp [lo]
    have := hm (approx - error)
    omega
  have hupp : hi < 2 ^ w := by
    dsimp [hi]
    have := hm (approx + error)
    omega
  let mid := { st with regs := Function.update st.regs 26 lo }
  let out := { mid with regs := Function.update mid.regs 27 hi }
  have hr₁ : Runs w p ω
      (.assign 26 (.bin .add (.reg 4) (.bin .mul (.reg 25) (.bin .sub (.reg 2) (.reg 3)))))
      st .normal mid 8 :=
    runs_assign_iff.mpr ⟨lo, by
      simp [Expr.eval, BinOp.eval, ha, he, hs, show st.regs 25 = ps from hps, hlo,
        (hm _).trans_lt hlo, show scale + ps * (approx - error) < 2 ^ w from hlow, lo],
      rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω
      (.assign 27 (.bin .add (.reg 4) (.bin .mul (.reg 25) (.bin .add (.reg 2) (.reg 3)))))
      mid .normal out 8 :=
    runs_assign_iff.mpr ⟨hi, by
      simp [Expr.eval, BinOp.eval, mid, ha, he, hs, show st.regs 25 = ps from hps, hhi,
        (hm _).trans_lt hhi, show scale + ps * (approx + error) < 2 ^ w from hupp, hi],
      rfl, rfl, rfl⟩
  have hb := initSparseCoreLogFactor_scaledBounds E m hp approx error scale hscale herr
  have hb' : (lo : ℝ) / scale ≤ SparseCore.coreLambdaS (E.P_fn m) m ∧
      SparseCore.coreLambdaS (E.P_fn m) m ≤ (hi : ℝ) / scale := by
    change ps ≤ 1 at hp
    change ((if ps = 0 then scale else scale + (approx - error) : ℕ) : ℝ) / scale ≤ _ ∧
      _ ≤ ((if ps = 0 then scale else scale + (approx + error) : ℕ) : ℝ) / scale at hb
    rcases (show ps = 0 ∨ ps = 1 by omega) with hzero | hone
    · simpa [lo, hi, hzero] using hb
    · simpa [lo, hi, hone] using hb
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 8, 8, hr₁, hr₂, rfl⟩),
    by simpa [out, mid] using hb'.1, by simpa [out] using hb'.2,
    by simp [out, mid, lo], by simp [out, hi],
    by simpa [out, mid, lo, hi] using Nat.mul_le_mul_left ps (show approx - error ≤ approx + error by omega),
    by simpa [out, hi] using Nat.add_le_add_left (hm (approx + error)) scale,
    by
      have hdiff : approx + error - (approx - error) ≤ 2 * error := by omega
      have hraw : hi - lo = ps * (approx + error - (approx - error)) := by
        simp only [hi, lo, Nat.add_sub_add_left, Nat.mul_sub]
      simpa [out, mid, hraw] using (hm _).trans hdiff,
    fun r h26 h27 => by simp [out, mid, h26, h27], rfl, rfl⟩

/-- Put the maximum of the two stretch enclosures into the level-size
input registers. Both terms must use the same scale in register 23. -/
@[expose] def selectInitSparseCoreStretch : Stmt :=
  .assign 19 (.bin .add (.reg 30) (.bin .sub (.reg 28) (.reg 30))) ;;
  .assign 20 (.bin .add (.reg 31) (.bin .sub (.reg 29) (.reg 31)))

/-- The endpoint maxima preserve the enclosure of the model stretch. -/
theorem selectInitSparseCoreStretch_runs {w scale lower₁ upper₁ lower₂ upper₂ : ℕ}
    {value₁ value₂ : ℝ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hs : 0 < scale)
    (ha : st.regs 28 = lower₁) (hb : st.regs 29 = upper₁)
    (hc : st.regs 30 = lower₂) (hd : st.regs 31 = upper₂)
    (hlw : max lower₁ lower₂ < 2 ^ w) (huw : max upper₁ upper₂ < 2 ^ w)
    (hl₁ : (lower₁ : ℝ) / scale ≤ value₁) (hu₁ : value₁ ≤ (upper₁ : ℝ) / scale)
    (hl₂ : (lower₂ : ℝ) / scale ≤ value₂) (hu₂ : value₂ ≤ (upper₂ : ℝ) / scale) :
    ∃ out, Runs w p ω selectInitSparseCoreStretch st .normal out 13 ∧
      out.regs 19 = max lower₁ lower₂ ∧ out.regs 20 = max upper₁ upper₂ ∧
      (out.regs 19 : ℝ) / scale ≤ max value₁ value₂ ∧
      max value₁ value₂ ≤ (out.regs 20 : ℝ) / scale ∧
      (∀ r, r ≠ 19 → r ≠ 20 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  let mid := { st with regs := Function.update st.regs 19 (max lower₁ lower₂) }
  let out := { mid with regs := Function.update mid.regs 20 (max upper₁ upper₂) }
  have hmax (a b : ℕ) : b + (a - b) = max a b := by
    rcases le_total a b with h | h
    · rw [Nat.sub_eq_zero_of_le h, Nat.add_zero, max_eq_right h]
    · rw [Nat.add_comm, Nat.sub_add_cancel h, max_eq_left h]
  have hsub {a b : ℕ} (hw : max a b < 2 ^ w) : a - b < 2 ^ w :=
    (Nat.sub_le _ _).trans_lt ((le_max_left a b).trans_lt hw)
  have hr₁ : Runs w p ω (.assign 19 (.bin .add (.reg 30) (.bin .sub (.reg 28) (.reg 30))))
      st .normal mid 6 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, ha, hc, hsub hlw, hmax, hlw],
      rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign 20 (.bin .add (.reg 31) (.bin .sub (.reg 29) (.reg 31))))
      mid .normal out 6 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, mid, hb, hd, hsub huw, hmax, huw],
      rfl, rfl, rfl⟩
  obtain ⟨hl, hu⟩ := initSparseCoreStretch_maxScaledBounds hs hl₁ hu₁ hl₂ hu₂
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 6, 6, hr₁, hr₂, rfl⟩),
    by simp [out, mid], by simp [out],
    by simpa [out, mid] using hl, by simpa [out] using hu,
    fun r h19 h20 => by simp [out, mid, h19, h20], rfl, rfl⟩

/-- Raise a positive word to a runtime natural exponent by successive
multiplication. The stretch calculation uses only powers that fit. -/
@[expose] def initStretchPowerBody (entry : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 1))
    (.call 2 entry [.reg 0, .bin .sub (.reg 1) (.const 1)] ;;
      .ret (.bin .mul (.reg 0) (.reg 2)))

/-- Read-only exact word powers for the stretch enclosure. -/
@[expose] def initStretchPowerContract (w : ℕ) : Contract where
  pre args _ := ∃ a e : ℕ, args = [a, e] ∧ 0 < a ∧ a ^ e < 2 ^ w
  post args mem v mem' := mem' = mem ∧ v = args.getD 0 0 ^ args.getD 1 0
  cost args _ := 20 * args.getD 1 0 + 6

/-- The recursive powers fit because a positive base has nondecreasing
powers. Each recursive frame takes at most 20 machine steps. -/
theorem initStretchPower_meetsContract {w entry : ℕ} {p : Program} (hw : 1 < 2 ^ w)
    (hp : p.HasAt entry [initStretchPowerBody entry]) :
    MeetsContract w p entry (initStretchPowerContract w) := by
  apply meetsContract_of_rec (fun args _ => args.getD 1 0) hp.head
  intro k ih args mem pos ω hwords hpre hk
  rcases hpre with ⟨a, e, rfl, ha, hfit⟩
  change e = k at hk
  subst k
  have haw : a < 2 ^ w := hwords a (by simp)
  have hew : e < 2 ^ w := hwords e (by simp)
  apply runs_start_le
  unfold initStretchPowerBody
  wram_step
  · have he : e = 0 := by simpa [startState] using hcond
    subst e
    refine runs_ret_le (v := 1) (by eval_expr) ?_ ?_
    · exact ⟨rfl, by simp [Outcome.value]⟩
    · simp [initStretchPowerContract, Expr.size_bin, Expr.size_reg, Expr.size_const]
  · have he : e ≠ 0 := by simpa [startState] using hcond
    have he' : e - 1 < e := by omega
    have hpred : e - 1 < 2 ^ w := he'.trans hew
    have hpow : a ^ (e - 1) < 2 ^ w :=
      (Nat.pow_le_pow_right ha he'.le).trans_lt hfit
    have hrec : MeetsContract w p entry
        ((initStretchPowerContract w).below (fun args _ => args.getD 1 0) e) := ih
    refine runs_seq_call_le hrec (vs := [a, e - 1]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨⟨a, e - 1, rfl, ha, hpow⟩, he'⟩
    · intro v mem' pos' hpost
      rcases hpost with ⟨hm, hv⟩
      subst mem'
      change v = a ^ (e - 1) at hv
      have hmul : a * v = a ^ e := by
        rw [hv, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ e)]
      refine runs_ret_le (v := a ^ e) (by simp [Expr.eval, BinOp.eval, startState, hmul, hfit]) ?_ ?_
      · exact ⟨rfl, rfl⟩
      · simp only [initStretchPowerContract, Contract.below, List.getD_cons_zero,
          List.getD_cons_succ, Expr.size_bin, Expr.size_reg, Expr.size_const, argsSize_cons, argsSize_nil]
        omega

/-- Evaluate one endpoint numerator for the first stretch term.
Register 33 holds the exponent, 34 the factor including rescaling,
and 35 the scaled sparsifier stretch endpoint. -/
@[expose] def computeInitStretchFirstEndpoint (power : ℕ) : Stmt :=
  .call 36 power [.reg 35, .reg 33] ;;
  .assign 36 (.bin .mul (.reg 34) (.reg 36))

/-- A runtime power and one multiplication form the first numerator. -/
theorem computeInitStretchFirstEndpoint_runs
    {w power exponent endpoint factor : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p power (initStretchPowerContract w))
    (he : st.regs 33 = exponent) (hf : st.regs 34 = factor)
    (ha : st.regs 35 = endpoint) (hapos : 0 < endpoint)
    (haWord : endpoint < 2 ^ w) (heWord : exponent < 2 ^ w)
    (hpow : endpoint ^ exponent < 2 ^ w)
    (hword : factor * endpoint ^ exponent < 2 ^ w) :
    ∃ out c, Runs w p ω (computeInitStretchFirstEndpoint power) st .normal out c ∧
      out.regs 36 = factor * endpoint ^ exponent ∧ out.mem = st.mem ∧
      (∀ r ≠ 36, out.regs r = st.regs r) ∧ c ≤ 20 * exponent + 14 := by
  have ha' : evalArgs w st [.reg 35, .reg 33] = some [endpoint, exponent] := by
    simp [evalArgs, Expr.eval, ha, he]
  have hwords : ∀ a ∈ [endpoint, exponent], a < 2 ^ w := by
    intro a h
    simp at h
    rcases h with rfl | rfl
    · exact haWord
    · exact heWord
  obtain ⟨mid, c, ret, hr, hp, hret, hreg, hc⟩ :=
    runs_call_of_meetsContract (r := 36) himpl ha' hwords ⟨endpoint, exponent, rfl, hapos, hpow⟩ ω
  obtain ⟨hm, hvalue⟩ := hp
  change ret = endpoint ^ exponent at hvalue
  let out := { mid with regs := Function.update mid.regs 36 (factor * endpoint ^ exponent) }
  have hr' : Runs w p ω (.assign 36 (.bin .mul (.reg 34) (.reg 36))) mid .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, (hreg 34 (by decide)).trans hf, hret, hvalue, hword],
      rfl, rfl, rfl⟩
  change c ≤ 2 + (20 * exponent + 6) + 1 at hc
  refine ⟨out, c + 4 + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c, 4, hr, hr', rfl⟩),
    by simp [out], hm, ?_, by omega⟩
  intro r h
  simpa only [out, Function.update_of_ne h] using hreg r h

/-- Compute the second endpoint numerator from capacity, the three
factor numerators, the original denominator, and the rescaling factor. -/
@[expose] def computeInitStretchSecondEndpoint (kReg stretchReg logReg dest : ℕ) : Stmt :=
  .assign dest (.bin .mul (.bin .mul (.const 11)
    (.bin .add (.bin .mul (.bin .mul (.bin .mul (.reg 38) (.reg kReg)) (.reg stretchReg)) (.reg logReg))
      (.bin .mul (.const 115) (.reg 42)))) (.reg 43))

/-- Bound each multiplication by the final numerator. Positivity of
the remaining factors ensures that this bound applies before rescaling. -/
theorem computeInitStretchSecondEndpoint_runs
    {w cap k stretch logFactor den rescale kReg stretchReg logReg dest : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hc : st.regs 38 = cap) (hk : st.regs kReg = k) (hs : st.regs stretchReg = stretch)
    (hl : st.regs logReg = logFactor) (hd : st.regs 42 = den) (hr : st.regs 43 = rescale)
    (hstretch : 0 < stretch) (hlog : 0 < logFactor) (hrescale : 0 < rescale)
    (hw : 115 < 2 ^ w)
    (hword : 11 * (cap * k * stretch * logFactor + 115 * den) * rescale < 2 ^ w) :
    ∃ out, Runs w p ω (computeInitStretchSecondEndpoint kReg stretchReg logReg dest) st .normal out 16 ∧
      out.regs dest = 11 * (cap * k * stretch * logFactor + 115 * den) * rescale ∧
      (∀ r ≠ dest, out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  have hmono (a : ℕ) {b : ℕ} (hb : 0 < b) : a ≤ a * b := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left a hb
  have h11 : 11 * (cap * k * stretch * logFactor + 115 * den) < 2 ^ w :=
    (hmono _ hrescale).trans_lt hword
  have hsum : cap * k * stretch * logFactor + 115 * den < 2 ^ w := by
    exact (by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right
        (cap * k * stretch * logFactor + 115 * den) (show 1 ≤ 11 by decide) :
        _ ≤ _).trans_lt h11
  have hprod : cap * k * stretch * logFactor < 2 ^ w :=
    (Nat.le_add_right _ _).trans_lt hsum
  have hsprod : cap * k * stretch < 2 ^ w := (hmono _ hlog).trans_lt hprod
  have hkprod : cap * k < 2 ^ w := (hmono _ hstretch).trans_lt hsprod
  have hdprod : 115 * den < 2 ^ w := (Nat.le_add_left _ _).trans_lt hsum
  let result := 11 * (cap * k * stretch * logFactor + 115 * den) * rescale
  let out := { st with regs := Function.update st.regs dest result }
  refine ⟨out, ?_, by simp [out, result], fun r h => by simp [out, h], rfl, rfl⟩
  apply runs_assign_iff.mpr
  exact ⟨_, by simp [Expr.eval, BinOp.eval, hc, hk, hs, hl, hd, hr, hw,
    show 11 < 2 ^ w by omega, hkprod, hsprod, hprod, hdprod, hsum, h11, hword, result], rfl, rfl, rfl⟩

/-- Read the runtime sparse-core depth and form the first denominator
exponent and the shared denominator exponent. -/
@[expose] def prepareInitStretchExponents : Stmt :=
  .assign 33 (.bin .add (.reg 44) (.const 1)) ;;
  .assign 45 (.bin .add (.const 3) (.bin .sub (.reg 33) (.const 3)))

/-- The common exponent is the larger of the two term exponents. -/
theorem prepareInitStretchExponents_runs {w depth : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hd : st.regs 44 = depth) (hw : max (depth + 1) 3 < 2 ^ w) :
    ∃ out, Runs w p ω prepareInitStretchExponents st .normal out 11 ∧
      out.regs 33 = depth + 1 ∧ out.regs 45 = max (depth + 1) 3 ∧
      (∀ r, r ≠ 33 → r ≠ 45 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  let mid := { st with regs := Function.update st.regs 33 (depth + 1) }
  let out := { mid with regs := Function.update mid.regs 45 (max (depth + 1) 3) }
  have h₁ := (le_max_left (depth + 1) 3).trans_lt hw
  have h₃ := (le_max_right (depth + 1) 3).trans_lt hw
  have hsub : depth - 2 < 2 ^ w := by omega
  have hmax : 3 + (depth - 2) = max (depth + 1) 3 := by omega
  have hr₁ : Runs w p ω (.assign 33 (.bin .add (.reg 44) (.const 1))) st .normal mid 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hd, h₁, show 1 < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign 45 (.bin .add (.const 3) (.bin .sub (.reg 33) (.const 3))))
      mid .normal out 6 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, mid, h₃, hsub, hmax, hw],
      rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 4, 6, hr₁, hr₂, rfl⟩),
    by simp [out, mid], by simp [out], fun r h33 h45 => by simp [out, mid, h33, h45], rfl, rfl⟩

/-- Compute the shared denominator in the register used by the
level-size product initialization. -/
@[expose] def computeInitStretchScale (power : ℕ) : Stmt :=
  .call 23 power [.reg 4, .reg 45]

/-- The shared denominator is computed from the runtime scale and
exponent without changing the other input registers or memory. -/
theorem computeInitStretchScale_runs {w power scale exponent : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p power (initStretchPowerContract w))
    (hs : st.regs 4 = scale) (he : st.regs 45 = exponent)
    (hpos : 0 < scale) (hsw : scale < 2 ^ w) (hew : exponent < 2 ^ w)
    (hfit : scale ^ exponent < 2 ^ w) :
    ∃ out c, Runs w p ω (computeInitStretchScale power) st .normal out c ∧
      out.regs 23 = scale ^ exponent ∧ out.mem = st.mem ∧
      (∀ r ≠ 23, out.regs r = st.regs r) ∧ c ≤ 20 * exponent + 9 := by
  have hargs : evalArgs w st [.reg 4, .reg 45] = some [scale, exponent] := by
    simp [evalArgs, Expr.eval, hs, he]
  have hwords : ∀ a ∈ [scale, exponent], a < 2 ^ w := by
    intro a ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hsw
    · exact hew
  obtain ⟨out, c, ret, hr, ⟨hm, hv⟩, hret, hregs, hc⟩ :=
    runs_call_of_meetsContract (r := 23) himpl hargs hwords ⟨scale, exponent, rfl, hpos, hfit⟩ ω
  change ret = scale ^ exponent at hv
  change c ≤ 2 + (20 * exponent + 6) + 1 at hc
  exact ⟨out, c, hr, hret.trans hv, hm, hregs, by omega⟩

/-- Compute the second stretch term's denominator and its multiplier
for conversion to the shared denominator. -/
@[expose] def prepareInitStretchSecondScale (power : ℕ) : Stmt :=
  .call 42 power [.reg 4, .const 3] ;;
  .call 43 power [.reg 4, .bin .sub (.reg 45) (.const 3)]

/-- The second term uses its original cubic denominator and the remaining
power of the scale to match the first term. -/
theorem prepareInitStretchSecondScale_runs {w power scale exponent : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p power (initStretchPowerContract w))
    (hs : st.regs 4 = scale) (he : st.regs 45 = exponent)
    (hpos : 0 < scale) (h₃ : 3 ≤ exponent) (hsw : scale < 2 ^ w)
    (hew : exponent < 2 ^ w) (hfit : scale ^ exponent < 2 ^ w) :
    ∃ out c, Runs w p ω (prepareInitStretchSecondScale power) st .normal out c ∧
      out.regs 42 = scale ^ 3 ∧ out.regs 43 = scale ^ (exponent - 3) ∧
      out.mem = st.mem ∧ (∀ r, r ≠ 42 → r ≠ 43 → out.regs r = st.regs r) ∧
      c ≤ 20 * exponent + 21 := by
  have hw : 3 < 2 ^ w := h₃.trans_lt hew
  have hsub : exponent - 3 < 2 ^ w := (Nat.sub_le _ _).trans_lt hew
  have hpow₃ := (Nat.pow_le_pow_right hpos h₃).trans_lt hfit
  have hpowSub := (Nat.pow_le_pow_right hpos (Nat.sub_le exponent 3)).trans_lt hfit
  have ha₁ : evalArgs w st [.reg 4, .const 3] = some [scale, 3] := by
    simp [evalArgs, Expr.eval, hs, hw]
  obtain ⟨mid, c₁, ret₁, hr₁, ⟨hm₁, hv₁⟩, hret₁, hreg₁, hc₁⟩ :=
    runs_call_of_meetsContract (r := 42) himpl ha₁ (by simpa using And.intro hsw hw)
      ⟨scale, 3, rfl, hpos, hpow₃⟩ ω
  have ha₂ : evalArgs w mid [.reg 4, .bin .sub (.reg 45) (.const 3)] =
      some [scale, exponent - 3] := by
    simp [evalArgs, Expr.eval, BinOp.eval, (hreg₁ 4 (by decide)).trans hs,
      (hreg₁ 45 (by decide)).trans he, hw, hsub]
  obtain ⟨out, c₂, ret₂, hr₂, ⟨hm₂, hv₂⟩, hret₂, hreg₂, hc₂⟩ :=
    runs_call_of_meetsContract (r := 43) himpl ha₂ (by simpa using And.intro hsw hsub)
      ⟨scale, exponent - 3, rfl, hpos, hpowSub⟩ ω
  change ret₁ = scale ^ 3 at hv₁
  change ret₂ = scale ^ (exponent - 3) at hv₂
  change c₁ ≤ 2 + (20 * 3 + 6) + 1 at hc₁
  change c₂ ≤ 4 + (20 * (exponent - 3) + 6) + 1 at hc₂
  exact ⟨out, c₁ + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c₁, c₂, hr₁, hr₂, rfl⟩),
    (hreg₂ 42 (by decide)).trans (hret₁.trans hv₁), hret₂.trans hv₂,
    hm₂.trans hm₁, fun r h42 h43 => (hreg₂ r h43).trans (hreg₁ r h42), by omega⟩

/-- Prepare the constant-base power and the shared-scale multiplier for
the first stretch term. The depth and both exponents are runtime words. -/
@[expose] def prepareInitStretchFirstScale (power : ℕ) : Stmt :=
  .call 34 power [.const 3, .reg 44] ;;
  .call 46 power [.reg 4, .bin .sub (.reg 45) (.reg 33)] ;;
  .assign 34 (.bin .mul (.reg 34) (.reg 46))

/-- The first stretch term receives its exact combined multiplier. -/
theorem prepareInitStretchFirstScale_runs {w power scale depth : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p power (initStretchPowerContract w))
    (hs : st.regs 4 = scale) (hd : st.regs 44 = depth)
    (hfirst : st.regs 33 = depth + 1) (hcommon : st.regs 45 = max (depth + 1) 3)
    (hpos : 0 < scale) (hsw : scale < 2 ^ w)
    (hw : max (depth + 1) 3 < 2 ^ w)
    (hfit : 3 ^ depth * scale ^ (max (depth + 1) 3 - (depth + 1)) < 2 ^ w) :
    ∃ out c, Runs w p ω (prepareInitStretchFirstScale power) st .normal out c ∧
      out.regs 34 = 3 ^ depth * scale ^ (max (depth + 1) 3 - (depth + 1)) ∧
      out.mem = st.mem ∧ (∀ r, r ≠ 34 → r ≠ 46 → out.regs r = st.regs r) ∧
      c ≤ 20 * (depth + (max (depth + 1) 3 - (depth + 1))) + 26 := by
  let exponent := max (depth + 1) 3 - (depth + 1)
  have h₃ := (le_max_right (depth + 1) 3).trans_lt hw
  have hdw : depth < 2 ^ w := (Nat.lt_succ_self depth).trans
    ((le_max_left (depth + 1) 3).trans_lt hw)
  have hew : exponent < 2 ^ w := (Nat.sub_le _ _).trans_lt hw
  have h₁ : 1 ≤ scale ^ exponent := Nat.succ_le_of_lt (pow_pos hpos _)
  have h₂ : 1 ≤ 3 ^ depth := Nat.succ_le_of_lt (by positivity)
  have hpow₃ : 3 ^ depth < 2 ^ w := by
    exact (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (3 ^ depth) h₁ :
      3 ^ depth ≤ 3 ^ depth * scale ^ exponent).trans_lt hfit
  have hpowS : scale ^ exponent < 2 ^ w := by
    exact (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right (scale ^ exponent) h₂ :
      scale ^ exponent ≤ 3 ^ depth * scale ^ exponent).trans_lt hfit
  have ha₁ : evalArgs w st [.const 3, .reg 44] = some [3, depth] := by
    simp [evalArgs, Expr.eval, h₃, hd]
  obtain ⟨mid, c₁, ret₁, hr₁, ⟨hm₁, hv₁⟩, hret₁, hreg₁, hc₁⟩ :=
    runs_call_of_meetsContract (r := 34) himpl ha₁ (by simpa using And.intro h₃ hdw)
      ⟨3, depth, rfl, by decide, hpow₃⟩ ω
  have ha₂ : evalArgs w mid [.reg 4, .bin .sub (.reg 45) (.reg 33)] =
      some [scale, exponent] := by
    simp [evalArgs, Expr.eval, BinOp.eval, (hreg₁ 4 (by decide)).trans hs,
      (hreg₁ 45 (by decide)).trans hcommon, (hreg₁ 33 (by decide)).trans hfirst,
      show max (depth + 1) 3 - (depth + 1) < 2 ^ w from hew, exponent]
  obtain ⟨ready, c₂, ret₂, hr₂, ⟨hm₂, hv₂⟩, hret₂, hreg₂, hc₂⟩ :=
    runs_call_of_meetsContract (r := 46) himpl ha₂ (by simpa using And.intro hsw hew)
      ⟨scale, exponent, rfl, hpos, hpowS⟩ ω
  change ret₁ = 3 ^ depth at hv₁
  change ret₂ = scale ^ exponent at hv₂
  let out := { ready with regs := Function.update ready.regs 34 (3 ^ depth * scale ^ exponent) }
  have hr₃ : Runs w p ω (.assign 34 (.bin .mul (.reg 34) (.reg 46))) ready .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval,
      (hreg₂ 34 (by decide)).trans (hret₁.trans hv₁), hret₂.trans hv₂,
      show 3 ^ depth * scale ^ exponent < 2 ^ w from hfit], rfl, rfl, rfl⟩
  change c₁ ≤ 2 + (20 * depth + 6) + 1 at hc₁
  change c₂ ≤ 4 + (20 * exponent + 6) + 1 at hc₂
  refine ⟨out, c₁ + (c₂ + 4 + 1) + 1, ?_, by simp [out, exponent], hm₂.trans hm₁, ?_, ?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨mid, c₁, _, hr₁,
      runs_seq_iff.mpr (Or.inr ⟨ready, c₂, 4, hr₂, hr₃, rfl⟩), rfl⟩)
  · intro r h34 h46
    simpa only [out, Function.update_of_ne h34] using (hreg₂ r h46).trans (hreg₁ r h34)
  · change c₁ + (c₂ + 4 + 1) + 1 ≤ 20 * (depth + exponent) + 26
    omega

/-- Form the integer capacity multiplier of the second stretch term
from runtime depth, bucket cap, and degree cap. -/
@[expose] def prepareInitStretchCapacity : Stmt :=
  .assign 38 (.bin .mul (.bin .mul (.reg 33) (.reg 47))
    (.bin .add (.bin .mul (.const 2) (.reg 48)) (.const 190)))

/-- Positive bucket and depth factors bound all intermediate products
by the final capacity multiplier. -/
theorem prepareInitStretchCapacity_runs {w depth buckets degree : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hd : st.regs 33 = depth + 1) (hb : st.regs 47 = buckets) (hg : st.regs 48 = degree)
    (hpos : 0 < buckets) (hfit : (depth + 1) * buckets * (2 * degree + 190) < 2 ^ w) :
    ∃ out, Runs w p ω prepareInitStretchCapacity st .normal out 10 ∧
      out.regs 38 = (depth + 1) * buckets * (2 * degree + 190) ∧
      (∀ r ≠ 38, out.regs r = st.regs r) ∧ out.mem = st.mem ∧ out.pos = st.pos := by
  have hleft : 1 ≤ (depth + 1) * buckets := Nat.succ_le_of_lt (by positivity)
  have hright : 1 ≤ 2 * degree + 190 := by omega
  have hl : (depth + 1) * buckets < 2 ^ w := by
    exact (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left ((depth + 1) * buckets) hright :
      (depth + 1) * buckets ≤ _).trans_lt hfit
  have hr : 2 * degree + 190 < 2 ^ w := by
    exact (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right (2 * degree + 190) hleft :
      2 * degree + 190 ≤ _).trans_lt hfit
  let value := (depth + 1) * buckets * (2 * degree + 190)
  let out := { st with regs := Function.update st.regs 38 value }
  refine ⟨out, ?_, by simp [out, value], fun r h => by simp [out, h], rfl, rfl⟩
  apply runs_assign_iff.mpr
  exact ⟨value, by simp [Expr.eval, BinOp.eval, hd, hb, hg, hl, hr, value, hfit,
    show 2 < 2 ^ w by omega, show 190 < 2 ^ w by omega, show 2 * degree < 2 ^ w by omega],
    rfl, rfl, rfl⟩

/-- Prepare the input words shared by both endpoints of the second
stretch term. -/
@[expose] def prepareInitStretchSecondTerm (power : ℕ) : Stmt :=
  prepareInitStretchSecondScale power ;; prepareInitStretchCapacity

/-- The second term uses the same capacity multiplier and denominators
for its lower and upper endpoints. -/
theorem prepareInitStretchSecondTerm_runs {w power scale exponent depth buckets degree : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p power (initStretchPowerContract w))
    (hs : st.regs 4 = scale) (he : st.regs 45 = exponent)
    (hd : st.regs 33 = depth + 1) (hb : st.regs 47 = buckets) (hg : st.regs 48 = degree)
    (hpos : 0 < scale) (h₃ : 3 ≤ exponent) (hsw : scale < 2 ^ w)
    (hew : exponent < 2 ^ w) (hfit : scale ^ exponent < 2 ^ w)
    (hbpos : 0 < buckets) (hcap : (depth + 1) * buckets * (2 * degree + 190) < 2 ^ w) :
    ∃ out c, Runs w p ω (prepareInitStretchSecondTerm power) st .normal out c ∧
      out.regs 38 = (depth + 1) * buckets * (2 * degree + 190) ∧
      out.regs 42 = scale ^ 3 ∧ out.regs 43 = scale ^ (exponent - 3) ∧
      (∀ r, r ≠ 38 → r ≠ 42 → r ≠ 43 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ c ≤ 20 * exponent + 32 := by
  obtain ⟨mid, c, hr, hden, hscale, hmem, hkeep, hc⟩ :=
    prepareInitStretchSecondScale_runs (ω := ω) himpl hs he hpos h₃ hsw hew hfit
  obtain ⟨out, hr', hcap', hkeep', hm', _⟩ :=
    prepareInitStretchCapacity_runs (p := p) (ω := ω)
      ((hkeep 33 (by decide) (by decide)).trans hd)
      ((hkeep 47 (by decide) (by decide)).trans hb)
      ((hkeep 48 (by decide) (by decide)).trans hg) hbpos hcap
  exact ⟨out, c + 10 + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c, 10, hr, hr', rfl⟩),
    hcap', (hkeep' 42 (by decide)).trans hden, (hkeep' 43 (by decide)).trans hscale,
    fun r h38 h42 h43 => (hkeep' r h38).trans (hkeep r h42 h43), hm'.trans hmem, by omega⟩

/-- Derive the common scale and both exponents from the runtime depth. -/
@[expose] def prepareInitStretchCommonScale (power : ℕ) : Stmt :=
  prepareInitStretchExponents ;; computeInitStretchScale power

/-- The common scale goes directly into the level-size input register. -/
theorem prepareInitStretchCommonScale_runs {w power scale depth : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p power (initStretchPowerContract w))
    (hs : st.regs 4 = scale) (hd : st.regs 44 = depth)
    (hpos : 0 < scale) (hsw : scale < 2 ^ w)
    (hew : max (depth + 1) 3 < 2 ^ w) (hfit : scale ^ max (depth + 1) 3 < 2 ^ w) :
    ∃ out c, Runs w p ω (prepareInitStretchCommonScale power) st .normal out c ∧
      out.regs 23 = scale ^ max (depth + 1) 3 ∧
      out.regs 33 = depth + 1 ∧ out.regs 45 = max (depth + 1) 3 ∧
      (∀ r, r ≠ 23 → r ≠ 33 → r ≠ 45 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ c ≤ 20 * max (depth + 1) 3 + 21 := by
  obtain ⟨mid, hr₁, hfirst, hcommon, hkeep₁, hm₁, _⟩ :=
    prepareInitStretchExponents_runs (p := p) (ω := ω) hd hew
  obtain ⟨out, c, hr₂, hscale, hm₂, hkeep₂, hc⟩ :=
    computeInitStretchScale_runs (ω := ω) himpl ((hkeep₁ 4 (by decide) (by decide)).trans hs)
      hcommon hpos hsw hew hfit
  exact ⟨out, 11 + c + 1, runs_seq_iff.mpr (Or.inr ⟨mid, 11, c, hr₁, hr₂, rfl⟩),
    hscale, (hkeep₂ 33 (by decide)).trans hfirst, (hkeep₂ 45 (by decide)).trans hcommon,
    fun r h23 h33 h45 => (hkeep₂ r h23).trans (hkeep₁ r h33 h45), hm₂.trans hm₁, by omega⟩

/-- Install a first-term endpoint in the register consumed by the
stretch maximum, using the runtime endpoint from the source register. -/
@[expose] def installInitStretchFirstEndpoint (power source dest : ℕ) : Stmt :=
  .assign 35 (.reg source) ;;
  computeInitStretchFirstEndpoint power ;;
  .assign dest (.reg 36)

/-- The destination receives the exact scaled endpoint numerator. -/
theorem installInitStretchFirstEndpoint_runs
    {w power source dest exponent endpoint factor : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p power (initStretchPowerContract w))
    (he : st.regs 33 = exponent) (hf : st.regs 34 = factor)
    (ha : st.regs source = endpoint) (hapos : 0 < endpoint)
    (haWord : endpoint < 2 ^ w) (heWord : exponent < 2 ^ w)
    (hpow : endpoint ^ exponent < 2 ^ w)
    (hword : factor * endpoint ^ exponent < 2 ^ w) :
    ∃ out c, Runs w p ω (installInitStretchFirstEndpoint power source dest) st .normal out c ∧
      out.regs dest = factor * endpoint ^ exponent ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 35 → r ≠ 36 → r ≠ dest → out.regs r = st.regs r) ∧
      c ≤ 20 * exponent + 20 := by
  let mid := { st with regs := Function.update st.regs 35 endpoint }
  have hr₁ : Runs w p ω (.assign 35 (.reg source)) st .normal mid 2 :=
    runs_assign_iff.mpr ⟨endpoint, by simp [Expr.eval, ha], rfl, rfl, rfl⟩
  obtain ⟨ready, c, hr₂, hvalue, hm, hkeep, hc⟩ :=
    computeInitStretchFirstEndpoint_runs (ω := ω) (st := mid) himpl
      (by simpa [mid] using he) (by simpa [mid] using hf) (by simp [mid])
      hapos haWord heWord hpow hword
  let out := { ready with regs := Function.update ready.regs dest (factor * endpoint ^ exponent) }
  have hr₃ : Runs w p ω (.assign dest (.reg 36)) ready .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hvalue], rfl, rfl, rfl⟩
  refine ⟨out, 2 + (c + 2 + 1) + 1, ?_, by simp [out], hm, ?_, by omega⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨mid, 2, _, hr₁,
      runs_seq_iff.mpr (Or.inr ⟨ready, c, 2, hr₂, hr₃, rfl⟩), rfl⟩)
  · intro r h35 h36 hdest
    simpa only [out, Function.update_of_ne hdest, mid, Function.update_of_ne h35] using hkeep r h36

/-- Compute both second-term endpoints using the prepared logarithmic
factor bounds and the supplied sparsifier parameter bounds. -/
@[expose] def computeInitStretchSecondPair : Stmt :=
  computeInitStretchSecondEndpoint 49 50 26 30 ;;
  computeInitStretchSecondEndpoint 51 52 27 31

/-- The second pair is ready for the maximum at the common scale. -/
theorem computeInitStretchSecondPair_runs
    {w cap kl ku sl su ll lu den rescale : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hc : st.regs 38 = cap) (hd : st.regs 42 = den) (hr : st.regs 43 = rescale)
    (hkl : st.regs 49 = kl) (hku : st.regs 51 = ku)
    (hsl : st.regs 50 = sl) (hsu : st.regs 52 = su)
    (hll : st.regs 26 = ll) (hlu : st.regs 27 = lu)
    (hslPos : 0 < sl) (hsuPos : 0 < su) (hllPos : 0 < ll) (hluPos : 0 < lu)
    (hrPos : 0 < rescale) (hw : 115 < 2 ^ w)
    (hlo : 11 * (cap * kl * sl * ll + 115 * den) * rescale < 2 ^ w)
    (hhi : 11 * (cap * ku * su * lu + 115 * den) * rescale < 2 ^ w) :
    ∃ out, Runs w p ω computeInitStretchSecondPair st .normal out 33 ∧
      out.regs 30 = 11 * (cap * kl * sl * ll + 115 * den) * rescale ∧
      out.regs 31 = 11 * (cap * ku * su * lu + 115 * den) * rescale ∧
      (∀ r, r ≠ 30 → r ≠ 31 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  obtain ⟨mid, hr₁, hlo', hkeep, hm, hp⟩ :=
    computeInitStretchSecondEndpoint_runs (p := p) (ω := ω) (dest := 30)
      hc hkl hsl hll hd hr hslPos hllPos hrPos hw hlo
  obtain ⟨out, hr₂, hhi', hkeep', hm', hp'⟩ :=
    computeInitStretchSecondEndpoint_runs (p := p) (ω := ω) (dest := 31)
      ((hkeep 38 (by decide)).trans hc) ((hkeep 51 (by decide)).trans hku)
      ((hkeep 52 (by decide)).trans hsu) ((hkeep 27 (by decide)).trans hlu)
      ((hkeep 42 (by decide)).trans hd) ((hkeep 43 (by decide)).trans hr)
      hsuPos hluPos hrPos hw hhi
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 16, 16, hr₁, hr₂, rfl⟩),
    (hkeep' 30 (by decide)).trans hlo', hhi',
    fun r h30 h31 => (hkeep' r h31).trans (hkeep r h30), hm'.trans hm, hp'.trans hp⟩

/-- Compute both first-term endpoints for the shared stretch maximum. -/
@[expose] def computeInitStretchFirstPair (power : ℕ) : Stmt :=
  installInitStretchFirstEndpoint power 50 28 ;;
  installInitStretchFirstEndpoint power 52 29

/-- The first pair reuses the exact multiplier and exponent. -/
theorem computeInitStretchFirstPair_runs
    {w power exponent sl su factor : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p power (initStretchPowerContract w))
    (he : st.regs 33 = exponent) (hf : st.regs 34 = factor)
    (hl : st.regs 50 = sl) (hu : st.regs 52 = su)
    (hlpos : 0 < sl) (hupos : 0 < su) (horder : sl ≤ su) (hfpos : 0 < factor)
    (hew : exponent < 2 ^ w) (huw : su < 2 ^ w)
    (hword : factor * su ^ exponent < 2 ^ w) :
    ∃ out c, Runs w p ω (computeInitStretchFirstPair power) st .normal out c ∧
      out.regs 28 = factor * sl ^ exponent ∧ out.regs 29 = factor * su ^ exponent ∧
      (∀ r, r ≠ 28 → r ≠ 29 → r ≠ 35 → r ≠ 36 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ c ≤ 40 * exponent + 41 := by
  have hpow := Nat.pow_le_pow_left horder exponent
  have hpowWord : su ^ exponent < 2 ^ w :=
    (Nat.le_mul_of_pos_left _ hfpos).trans_lt hword
  obtain ⟨mid, c₁, hr₁, hlo, hm₁, hkeep₁, hc₁⟩ :=
    installInitStretchFirstEndpoint_runs (ω := ω) (dest := 28) himpl he hf hl hlpos
      (horder.trans_lt huw) hew (hpow.trans_lt hpowWord)
      ((Nat.mul_le_mul_left factor hpow).trans_lt hword)
  obtain ⟨out, c₂, hr₂, hhi, hm₂, hkeep₂, hc₂⟩ :=
    installInitStretchFirstEndpoint_runs (ω := ω) (dest := 29) himpl
      ((hkeep₁ 33 (by decide) (by decide) (by decide)).trans he)
      ((hkeep₁ 34 (by decide) (by decide) (by decide)).trans hf)
      ((hkeep₁ 52 (by decide) (by decide) (by decide)).trans hu) hupos huw hew hpowWord hword
  exact ⟨out, c₁ + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c₁, c₂, hr₁, hr₂, rfl⟩),
    (hkeep₂ 28 (by decide) (by decide) (by decide)).trans hlo, hhi,
    fun r h28 h29 h35 h36 => (hkeep₂ r h35 h36 h29).trans (hkeep₁ r h35 h36 h28),
    hm₂.trans hm₁, by omega⟩

/-- Fill all four registers consumed by the sparse-core stretch maximum. -/
@[expose] def computeInitStretchPairs (power : ℕ) : Stmt :=
  computeInitStretchFirstPair power ;; computeInitStretchSecondPair

/-- The endpoint computations preserve each other's output registers
and share the runtime stretch bounds. -/
theorem computeInitStretchPairs_runs
    {w power exponent factor cap kl ku sl su ll lu den rescale : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p power (initStretchPowerContract w))
    (he : st.regs 33 = exponent) (hf : st.regs 34 = factor)
    (hc : st.regs 38 = cap) (hd : st.regs 42 = den) (hr : st.regs 43 = rescale)
    (hkl : st.regs 49 = kl) (hku : st.regs 51 = ku)
    (hsl : st.regs 50 = sl) (hsu : st.regs 52 = su)
    (hll : st.regs 26 = ll) (hlu : st.regs 27 = lu)
    (hslPos : 0 < sl) (hsuPos : 0 < su) (hllPos : 0 < ll) (hluPos : 0 < lu)
    (hfPos : 0 < factor) (hrPos : 0 < rescale) (horder : sl ≤ su)
    (hew : exponent < 2 ^ w) (huw : su < 2 ^ w) (hw : 115 < 2 ^ w)
    (hfirst : factor * su ^ exponent < 2 ^ w)
    (hlo : 11 * (cap * kl * sl * ll + 115 * den) * rescale < 2 ^ w)
    (hhi : 11 * (cap * ku * su * lu + 115 * den) * rescale < 2 ^ w) :
    ∃ out c, Runs w p ω (computeInitStretchPairs power) st .normal out c ∧
      out.regs 28 = factor * sl ^ exponent ∧ out.regs 29 = factor * su ^ exponent ∧
      out.regs 30 = 11 * (cap * kl * sl * ll + 115 * den) * rescale ∧
      out.regs 31 = 11 * (cap * ku * su * lu + 115 * den) * rescale ∧
      (∀ r, r ≠ 28 → r ≠ 29 → r ≠ 30 → r ≠ 31 → r ≠ 35 → r ≠ 36 →
        out.regs r = st.regs r) ∧ out.mem = st.mem ∧ c ≤ 40 * exponent + 75 := by
  obtain ⟨mid, c, hr₁, hfl, hfu, hkeep, hm, hcost⟩ :=
    computeInitStretchFirstPair_runs (ω := ω) himpl he hf hsl hsu
      hslPos hsuPos horder hfPos hew huw hfirst
  have hk (r : ℕ) (hne : r ≠ 28 ∧ r ≠ 29 ∧ r ≠ 35 ∧ r ≠ 36) :
      mid.regs r = st.regs r := hkeep r hne.1 hne.2.1 hne.2.2.1 hne.2.2.2
  obtain ⟨out, hr₂, hsl', hsu', hkeep', hm', _⟩ :=
    computeInitStretchSecondPair_runs (p := p) (ω := ω)
      ((hk 38 (by decide)).trans hc) ((hk 42 (by decide)).trans hd) ((hk 43 (by decide)).trans hr)
      ((hk 49 (by decide)).trans hkl) ((hk 51 (by decide)).trans hku)
      ((hk 50 (by decide)).trans hsl) ((hk 52 (by decide)).trans hsu)
      ((hk 26 (by decide)).trans hll) ((hk 27 (by decide)).trans hlu)
      hslPos hsuPos hllPos hluPos hrPos hw hlo hhi
  exact ⟨out, c + 33 + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c, 33, hr₁, hr₂, rfl⟩),
    (hkeep' 28 (by decide) (by decide)).trans hfl, (hkeep' 29 (by decide) (by decide)).trans hfu,
    hsl', hsu', fun r h28 h29 h30 h31 h35 h36 =>
      (hkeep' r h30 h31).trans (hkeep r h28 h29 h35 h36), hm'.trans hm, by omega⟩

/-- Compute the two endpoint pairs and select their maximum. -/
@[expose] def computeInitStretchBounds (power : ℕ) : Stmt :=
  computeInitStretchPairs power ;; selectInitSparseCoreStretch

/-- The resulting registers enclose the maximum of the two stretch terms. -/
theorem computeInitStretchBounds_runs
    {w power exponent factor cap kl ku sl su ll lu den rescale scale : ℕ}
    {value₁ value₂ : ℝ} {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p power (initStretchPowerContract w))
    (he : st.regs 33 = exponent) (hf : st.regs 34 = factor)
    (hc : st.regs 38 = cap) (hd : st.regs 42 = den) (hr : st.regs 43 = rescale)
    (hkl : st.regs 49 = kl) (hku : st.regs 51 = ku)
    (hsl : st.regs 50 = sl) (hsu : st.regs 52 = su)
    (hll : st.regs 26 = ll) (hlu : st.regs 27 = lu)
    (hslPos : 0 < sl) (hsuPos : 0 < su) (hllPos : 0 < ll) (hluPos : 0 < lu)
    (hfPos : 0 < factor) (hrPos : 0 < rescale) (horder : sl ≤ su)
    (hew : exponent < 2 ^ w) (huw : su < 2 ^ w) (hw : 115 < 2 ^ w)
    (hfirst : factor * su ^ exponent < 2 ^ w)
    (hlo : 11 * (cap * kl * sl * ll + 115 * den) * rescale < 2 ^ w)
    (hhi : 11 * (cap * ku * su * lu + 115 * den) * rescale < 2 ^ w)
    (hscale : 0 < scale)
    (hfl : (↑(factor * sl ^ exponent) : ℝ) / scale ≤ value₁)
    (hfu : value₁ ≤ (↑(factor * su ^ exponent) : ℝ) / scale)
    (hsl' : (↑(11 * (cap * kl * sl * ll + 115 * den) * rescale : ℕ) : ℝ) / scale ≤ value₂)
    (hsu' : value₂ ≤ (↑(11 * (cap * ku * su * lu + 115 * den) * rescale : ℕ) : ℝ) / scale) :
    ∃ out c, Runs w p ω (computeInitStretchBounds power) st .normal out c ∧
      out.regs 19 = max (factor * sl ^ exponent) (11 * (cap * kl * sl * ll + 115 * den) * rescale) ∧
      out.regs 20 = max (factor * su ^ exponent) (11 * (cap * ku * su * lu + 115 * den) * rescale) ∧
      (out.regs 19 : ℝ) / scale ≤ max value₁ value₂ ∧
      max value₁ value₂ ≤ (out.regs 20 : ℝ) / scale ∧
      (∀ r, r ≠ 19 → r ≠ 20 → r ≠ 28 → r ≠ 29 → r ≠ 30 → r ≠ 31 → r ≠ 35 → r ≠ 36 →
        out.regs r = st.regs r) ∧ out.mem = st.mem ∧ c ≤ 40 * exponent + 89 := by
  obtain ⟨mid, c, hr₁, h28, h29, h30, h31, hkeep, hm, hcost⟩ :=
    computeInitStretchPairs_runs (ω := ω) himpl he hf hc hd hr hkl hku hsl hsu hll hlu
      hslPos hsuPos hllPos hluPos hfPos hrPos horder hew huw hw hfirst hlo hhi
  have hlWord := (Nat.mul_le_mul_left factor (Nat.pow_le_pow_left horder exponent)).trans_lt hfirst
  have hmaxLo := max_lt_iff.mpr ⟨hlWord, hlo⟩
  have hmaxHi := max_lt_iff.mpr ⟨hfirst, hhi⟩
  obtain ⟨out, hr₂, hloWord, hhiWord, hl, hu, hkeep', hm', _⟩ :=
    selectInitSparseCoreStretch_runs (p := p) (ω := ω) hscale h28 h29 h30 h31
      hmaxLo hmaxHi hfl hfu hsl' hsu'
  exact ⟨out, c + 13 + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c, 13, hr₁, hr₂, rfl⟩),
    hloWord, hhiWord, hl, hu, fun r h19 h20 h28 h29 h30 h31 h35 h36 =>
      (hkeep' r h19 h20).trans (hkeep r h28 h29 h30 h31 h35 h36),
    hm'.trans hm, by omega⟩

/-- Prepare all scale and capacity words shared by the endpoint calculations. -/
@[expose] def prepareInitStretchTerms (power : ℕ) : Stmt :=
  prepareInitStretchCommonScale power ;;
  prepareInitStretchFirstScale power ;;
  prepareInitStretchSecondTerm power

/-- The two terms and the level-size calculation use a single runtime
scale. The endpoint inputs survive all preparation steps. -/
theorem prepareInitStretchTerms_runs {w power scale depth buckets degree : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p power (initStretchPowerContract w))
    (hs : st.regs 4 = scale) (hd : st.regs 44 = depth)
    (hb : st.regs 47 = buckets) (hg : st.regs 48 = degree)
    (hpos : 0 < scale) (hsw : scale < 2 ^ w) (hbpos : 0 < buckets)
    (hew : max (depth + 1) 3 < 2 ^ w) (hfit : scale ^ max (depth + 1) 3 < 2 ^ w)
    (hf : 3 ^ depth * scale ^ (max (depth + 1) 3 - (depth + 1)) < 2 ^ w)
    (hc : (depth + 1) * buckets * (2 * degree + 190) < 2 ^ w) :
    let exponent := max (depth + 1) 3
    ∃ out c, Runs w p ω (prepareInitStretchTerms power) st .normal out c ∧
      out.regs 23 = scale ^ exponent ∧ out.regs 33 = depth + 1 ∧
      out.regs 34 = 3 ^ depth * scale ^ (exponent - (depth + 1)) ∧
      out.regs 38 = (depth + 1) * buckets * (2 * degree + 190) ∧
      out.regs 42 = scale ^ 3 ∧ out.regs 43 = scale ^ (exponent - 3) ∧
      (∀ r, r ≠ 23 → r ≠ 33 → r ≠ 34 → r ≠ 38 → r ≠ 42 → r ≠ 43 → r ≠ 45 → r ≠ 46 →
        out.regs r = st.regs r) ∧ out.mem = st.mem ∧ c ≤ 60 * exponent + 81 := by
  dsimp only
  obtain ⟨s₁, c₁, hr₁, hscale, he, hcommon, hk₁, hm₁, hc₁⟩ :=
    prepareInitStretchCommonScale_runs (ω := ω) himpl hs hd hpos hsw hew hfit
  obtain ⟨s₂, c₂, hr₂, hfactor, hm₂, hk₂, hc₂⟩ :=
    prepareInitStretchFirstScale_runs (ω := ω) himpl
      ((hk₁ 4 (by decide) (by decide) (by decide)).trans hs)
      ((hk₁ 44 (by decide) (by decide) (by decide)).trans hd) he hcommon hpos hsw hew hf
  have hk (r : ℕ) (hne : r ≠ 23 ∧ r ≠ 33 ∧ r ≠ 34 ∧ r ≠ 45 ∧ r ≠ 46) :
      s₂.regs r = st.regs r := (hk₂ r hne.2.2.1 hne.2.2.2.2).trans
        (hk₁ r hne.1 hne.2.1 hne.2.2.2.1)
  obtain ⟨out, c₃, hr₃, hcap, hden, hrescale, hk₃, hm₃, hc₃⟩ :=
    prepareInitStretchSecondTerm_runs (ω := ω) himpl ((hk 4 (by decide)).trans hs)
      ((hk₂ 45 (by decide) (by decide)).trans hcommon)
      ((hk₂ 33 (by decide) (by decide)).trans he)
      ((hk 47 (by decide)).trans hb) ((hk 48 (by decide)).trans hg)
      hpos (le_max_right _ _) hsw hew hfit hbpos hc
  have hdepth := le_max_left (depth + 1) 3
  refine ⟨out, c₁ + (c₂ + c₃ + 1) + 1, ?_,
    (hk₃ 23 (by decide) (by decide) (by decide)).trans ((hk₂ 23 (by decide) (by decide)).trans hscale),
    (hk₃ 33 (by decide) (by decide) (by decide)).trans ((hk₂ 33 (by decide) (by decide)).trans he),
    (hk₃ 34 (by decide) (by decide) (by decide)).trans hfactor, hcap, hden, hrescale,
    fun r h23 h33 h34 h38 h42 h43 h45 h46 =>
      (hk₃ r h38 h42 h43).trans (hk r ⟨h23, h33, h34, h45, h46⟩),
    hm₃.trans (hm₂.trans hm₁), by omega⟩
  exact runs_seq_iff.mpr (Or.inr ⟨s₁, c₁, _, hr₁,
    runs_seq_iff.mpr (Or.inr ⟨s₂, c₂, c₃, hr₂, hr₃, rfl⟩), rfl⟩)

/-- The sparse-core depth comparison reduces to an integer 24th power. -/
theorem initSparseCoreDepth_le_iff (m candidate : ℕ) :
    Expander.chosenL m ≤ candidate ↔ Real.log ((m : ℝ) + 2) ≤ (candidate : ℝ) ^ (24 : ℕ) := by
  unfold Expander.chosenL
  rw [Nat.ceil_le]
  have hlog : 0 ≤ Real.log ((m : ℝ) + 2) :=
    Real.log_nonneg (by linarith only [Nat.cast_nonneg (α := ℝ) m])
  have hp := Real.rpow_le_rpow_iff (Real.rpow_nonneg hlog (1 / 24))
    (Nat.cast_nonneg (α := ℝ) candidate) (by norm_num : (0 : ℝ) < 24)
  rw [← Real.rpow_mul hlog, show (1 : ℝ) / 24 * 24 = 1 by norm_num, Real.rpow_one,
    ← show ((24 : ℕ) : ℝ) = 24 by norm_num, Real.rpow_natCast] at hp
  exact hp.symm

/-- Positive edge bounds fitting the stated word range yield depth two
for the concrete sparse-core model. -/
theorem initSparseCoreDepth_eq_two_of_word {m w : ℕ}
    (hm : 0 < m) (hmw : m < 2 ^ w) (hw : w + 1 ≤ 2 ^ 24) :
    Expander.chosenL m = 2 := by
  have hmAdd : m + 2 ≤ 2 ^ (w + 1) := by
    rw [pow_succ]
    have hp := Nat.two_pow_pos w
    omega
  have hupper : Real.log ((m : ℝ) + 2) ≤ (2 : ℝ) ^ (24 : ℕ) := by
    have hcast : (m : ℝ) + 2 ≤ (2 : ℝ) ^ (w + 1) := by exact_mod_cast hmAdd
    have hlog := Real.log_le_log (by positivity : 0 < (m : ℝ) + 2) hcast
    rw [Real.log_pow] at hlog
    have htwo : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h
      exact h
    have hs : ((w + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (24 : ℕ) := by exact_mod_cast hw
    exact hlog.trans ((mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg _)).trans (by simpa using hs))
  have hlower : 1 < Real.log ((m : ℝ) + 2) := by
    apply (Real.lt_log_iff_exp_lt (by positivity)).mpr
    exact Real.exp_one_lt_three.trans_le (by
      have hc : (1 : ℝ) ≤ m := by exact_mod_cast (Nat.succ_le_of_lt hm)
      linarith only [hc])
  apply Nat.le_antisymm ((initSparseCoreDepth_le_iff m 2).mpr hupper)
  by_contra! h
  have hle := (initSparseCoreDepth_le_iff m 1).mp (show Expander.chosenL m ≤ 1 by omega)
  exact (not_le_of_gt hlower) (by simpa using hle)

/-- Compute the edge bound at which the sparse-core stretch is evaluated. -/
@[expose] def setInitSparseCoreEdgeBound : Stmt :=
  .assign 24 (.bin .mul (.reg 22) (.reg 22))

/-- The computation uses the stored base level size and leaves the
fixed-point format and input vertex count untouched. -/
theorem setInitSparseCoreEdgeBound_runs {w M : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hM : st.regs 22 = M) (hw : M ^ 2 < 2 ^ w) :
    ∃ out, Runs w p ω setInitSparseCoreEdgeBound st .normal out 4 ∧
      out.regs 24 = M ^ 2 ∧ (∀ r ≠ 24, out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  let out := { st with regs := Function.update st.regs 24 (M ^ 2) }
  refine ⟨out, ?_, by simp [out], fun r hr => by simp [out, hr], rfl, rfl⟩
  exact runs_assign_iff.mpr ⟨M ^ 2, by simp [Expr.eval, BinOp.eval, hM, pow_two, show M * M < 2 ^ w by simpa only [pow_two] using hw],
    rfl, rfl, rfl⟩

/-- Save the input graph's vertex count while preparing the distinct
graph bound used by the sparse-core logarithm. -/
@[expose] def prepareInitSparseCoreLogInput : Stmt :=
  .assign 57 (.reg 92) ;; setInitSparseCoreEdgeBound ;; initSparseCoreLogInput

/-- The graph count remains available for the rebuild thresholds after
forming the argument for the sparsity factor. -/
theorem prepareInitSparseCoreLogInput_runs {w M N : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hM : st.regs 22 = M) (hN : st.regs 92 = N)
    (hMw : M ^ 2 < 2 ^ w) (hw : 60 < 2 ^ w)
    (hlinear : 2 * M ^ 2 + 60 < 2 ^ w)
    (hproduct : M ^ 2 * (2 * M ^ 2 + 60) < 2 ^ w) :
    ∃ out, Runs w p ω prepareInitSparseCoreLogInput st .normal out 16 ∧
      out.regs 24 = M ^ 2 ∧ out.regs 57 = N ∧
      out.regs 92 = SparseCore.coreNMax (M ^ 2) + M ^ 2 ∧
      (∀ r, r ≠ 24 → r ≠ 57 → r ≠ 92 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  let saved := { st with regs := Function.update st.regs 57 N }
  have hr₁ : Runs w p ω (.assign 57 (.reg 92)) st .normal saved 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hN], rfl, rfl, rfl⟩
  obtain ⟨mid, hr₂, h24, hkeep, hm, hp⟩ :=
    setInitSparseCoreEdgeBound_runs (p := p) (ω := ω) (st := saved)
      (by simpa [saved] using hM) hMw
  obtain ⟨out, hr₃, h92, hkeep', hm', hp'⟩ :=
    initSparseCoreLogInput_runs (p := p) (ω := ω) h24 hw hlinear hproduct
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨saved, 2, 13, hr₁,
    runs_seq_iff.mpr (Or.inr ⟨mid, 4, 8, hr₂, hr₃, rfl⟩), rfl⟩),
    (hkeep' 24 (by decide)).trans h24,
    (hkeep' 57 (by decide)).trans ((hkeep 57 (by decide)).trans (by simp [saved])),
    h92, fun r h24 h57 h92 => (hkeep' r h92).trans ((hkeep r h24).trans (by simp [saved, h57])),
    hm'.trans hm, hp'.trans hp⟩

end MinCostFlow.MinRatio
