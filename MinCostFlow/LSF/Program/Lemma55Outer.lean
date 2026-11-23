module

public import MinCostFlow.LSF.Program.Lemma55ProgramBase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Weight Initialization, Budgets, and Outer MWU Loop for Lemma 5.5 (`Lemma55Outer`)

Verifies `initWtLoop_runs`, defines the space and cost budgets `lemma55Space` and `lemma55Cost`,
proves the prefix weight envelope `mwu_prefix_weight_envelope`, and verifies the `k_nat`-round
outer multiplicative-weights loop `mwuOuterLoop_runs`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.WideWord
  MinCostFlow.Num

@[expose] public section

/-! ## Helper 2: initializing `wtArr` to `v₀ ≡ 1` on active edges -/

lemma initWtLoop_runs {w wtArr eListPtr m0 eCap L_in pL : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem0 : ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w) (hpL_lt : pL < L_in) (hwt_ltw : wtArr + eCap * L_in < 2 ^ w)
    (heL_disj : eListPtr + m0 ≤ wtArr)
    (heL_lt : ∀ i < m0, mem0 (eListPtr + i) < eCap) :
    ∀ idx ≤ m0, ∀ st : State,
      st.regs 2 = L_in → st.regs 10 = wtArr → st.regs 14 = pL →
      st.regs 16 = idx → st.regs 18 = m0 → st.regs 19 = eListPtr →
      (∀ z, z < wtArr ∨ wtArr + eCap * L_in ≤ z → st.mem z = mem0 z) →
      (∀ i < idx, ∀ t < L_in,
        st.mem (wtArr + mem0 (eListPtr + i) * L_in + t) = if t = pL then 1 else 0) →
      (∀ e < eCap, (∀ i < idx, mem0 (eListPtr + i) ≠ e) → ∀ t < L_in,
        st.mem (wtArr + e * L_in + t) = 0) →
      ∃ st' c,
        Runs w p ω
          (.loop (.bin .lt (.reg 16) (.reg 18))
            ((.assign 17 (.load (.bin .add (.reg 19) (.reg 16))) ;;
              .store (.bin .add (.bin .add (.reg 10) (.bin .mul (.reg 17) (.reg 2))) (.reg 14))
                (.const 1)) ;;
             .assign 16 (.bin .add (.reg 16) (.const 1))))
          st .normal st' c ∧
        (∀ r ≤ 15, st'.regs r = st.regs r) ∧
        (∀ z, z < wtArr ∨ wtArr + eCap * L_in ≤ z → st'.mem z = mem0 z) ∧
        (∀ i < m0, ∀ t < L_in,
          st'.mem (wtArr + mem0 (eListPtr + i) * L_in + t) = if t = pL then 1 else 0) ∧
        c ≤ (m0 - idx) * 30 + 10 := by
  intro idx hidx
  obtain ⟨rem, hrem⟩ : ∃ rem, m0 - idx = rem := ⟨_, rfl⟩
  induction rem generalizing idx with
  | zero =>
    intro st _ _ _ hr16 hr18 _ hfr hinv1 _
    have hidx_eq : idx = m0 := by omega
    refine ⟨st, 4, runs_loop_iff.mpr (Or.inl ⟨by
        simp [Expr.eval, BinOp.eval, hr16, hr18, hidx_eq, show 0 < 2 ^ w by omega],
      rfl, by simp [Expr.size]⟩), fun _ _ => rfl, hfr, ?_, by omega⟩
    intro i hi t ht
    exact hinv1 i (hidx_eq ▸ hi) t ht
  | succ rem ih =>
    intro st hr2 hr10 hr14 hr16 hr18 hr19 hfr hinv1 hinv2
    have hidx_lt : idx < m0 := by omega
    have hLin1 : 1 ≤ L_in := by omega
    set e := mem0 (eListPtr + idx) with he_def
    have he_lt : e < eCap := heL_lt idx hidx_lt
    have he_mul : (e + 1) * L_in ≤ eCap * L_in := Nat.mul_le_mul_right L_in he_lt
    have hadd_eq : e * L_in + L_in = (e + 1) * L_in := by ring
    have he_ltw : e < 2 ^ w := by
      have : e + 1 ≤ (e + 1) * L_in := Nat.le_mul_of_pos_right _ hLin1
      omega
    have he_mem : st.mem (eListPtr + idx) = e := hfr _ (Or.inl (by omega))
    let r1 := Function.update st.regs 17 e
    let mem1 := Function.update st.mem (wtArr + e * L_in + pL) 1
    let st1 : State := { mem := mem1, regs := Function.update r1 16 (idx + 1), pos := st.pos }
    have hbody : Runs w p ω
        ((.assign 17 (.load (.bin .add (.reg 19) (.reg 16))) ;;
          .store (.bin .add (.bin .add (.reg 10) (.bin .mul (.reg 17) (.reg 2))) (.reg 14))
            (.const 1)) ;;
         .assign 16 (.bin .add (.reg 16) (.const 1)))
        st .normal st1 20 := by
      have hs0 : Runs w p ω
          (.assign 17 (.load (.bin .add (.reg 19) (.reg 16))))
          st .normal { mem := st.mem, regs := r1, pos := st.pos } 5 := by
        rw [runs_assign_iff]
        refine ⟨e, ?_, rfl, rfl, by simp [Expr.size]⟩
        simp only [Expr.eval, BinOp.eval, hr19, hr16, show eListPtr + idx < 2 ^ w by omega,
          ↓reduceIte, Option.map_some, he_mem]
      have hs1 : Runs w p ω
          (.store (.bin .add (.bin .add (.reg 10) (.bin .mul (.reg 17) (.reg 2))) (.reg 14))
            (.const 1))
          { mem := st.mem, regs := r1, pos := st.pos } .normal
          { mem := mem1, regs := r1, pos := st.pos } 9 := by
        rw [runs_store_iff]
        refine ⟨wtArr + e * L_in + pL, 1, ?_, by simp [Expr.eval, show 1 < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
        have hr10' : r1 10 = wtArr := by simp [r1, hr10]
        have hr17' : r1 17 = e := by simp [r1]
        have hr2' : r1 2 = L_in := by simp [r1, hr2]
        have hr14' : r1 14 = pL := by simp [r1, hr14]
        simp only [Expr.eval, BinOp.eval, hr10', hr17', hr2', hr14',
          show e * L_in < 2 ^ w by omega, show wtArr + e * L_in < 2 ^ w by omega,
          show wtArr + e * L_in + pL < 2 ^ w by omega, ↓reduceIte]
      have hs01 : Runs w p ω
          (.assign 17 (.load (.bin .add (.reg 19) (.reg 16))) ;;
           .store (.bin .add (.bin .add (.reg 10) (.bin .mul (.reg 17) (.reg 2))) (.reg 14))
             (.const 1))
          st .normal { mem := mem1, regs := r1, pos := st.pos } 15 :=
        runs_seq_iff.mpr (Or.inr ⟨_, 5, 9, hs0, hs1, rfl⟩)
      have hs2 : Runs w p ω (.assign 16 (.bin .add (.reg 16) (.const 1)))
          { mem := mem1, regs := r1, pos := st.pos } .normal st1 4 := by
        rw [runs_assign_iff]
        have hr16' : r1 16 = idx := by simp [r1, hr16]
        refine ⟨idx + 1, by simp [Expr.eval, BinOp.eval, hr16', show 1 < 2 ^ w by omega,
          show idx + 1 < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
      exact runs_seq_iff.mpr (Or.inr ⟨_, 15, 4, hs01, hs2, rfl⟩)
    have hfr1 : ∀ z, z < wtArr ∨ wtArr + eCap * L_in ≤ z → st1.mem z = mem0 z := fun z hz => by
      dsimp only [st1, mem1]
      rw [Function.update_of_ne (by omega)]
      exact hfr z hz
    have hsep : ∀ e' t, e' ≠ e → t < L_in → wtArr + e' * L_in + t ≠ wtArr + e * L_in + pL := by
      intro e' t hne ht hhit
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · have : (e' + 1) * L_in ≤ e * L_in := Nat.mul_le_mul_right L_in hlt
        have : e' * L_in + L_in = (e' + 1) * L_in := by ring
        omega
      · have : (e + 1) * L_in ≤ e' * L_in := Nat.mul_le_mul_right L_in hgt
        omega
    have hinv1' : ∀ i < idx + 1, ∀ t < L_in,
        st1.mem (wtArr + mem0 (eListPtr + i) * L_in + t) = if t = pL then 1 else 0 := by
      intro i hi t ht
      dsimp only [st1, mem1]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
      · rcases eq_or_ne (mem0 (eListPtr + i)) e with hee | hee
        · rw [hee]
          by_cases htp : t = pL
          · subst htp; rw [Function.update_self, ite_eq_left rfl]
          · rw [Function.update_of_ne (by omega), ite_eq_right htp]
            have hprev := hinv1 i hi' t ht
            rw [hee, ite_eq_right htp] at hprev
            exact hprev
        · rw [Function.update_of_ne (hsep _ t hee ht)]
          exact hinv1 i hi' t ht
      · rw [← he_def]
        by_cases htp : t = pL
        · subst htp; rw [Function.update_self, ite_eq_left rfl]
        · rw [Function.update_of_ne (by omega), ite_eq_right htp]
          by_cases hex : ∃ j < i, mem0 (eListPtr + j) = e
          · obtain ⟨j, hj, hje⟩ := hex
            have hprev := hinv1 j hj t ht
            rw [hje, ite_eq_right htp] at hprev
            exact hprev
          · exact hinv2 e he_lt (fun j hj hje => hex ⟨j, hj, hje⟩) t ht
    have hinv2' : ∀ e' < eCap, (∀ i < idx + 1, mem0 (eListPtr + i) ≠ e') → ∀ t < L_in,
        st1.mem (wtArr + e' * L_in + t) = 0 := by
      intro e' he' hne t ht
      dsimp only [st1, mem1]
      have hnee : e' ≠ e := Ne.symm (hne idx (Nat.lt_succ_self _))
      rw [Function.update_of_ne (hsep e' t hnee ht)]
      exact hinv2 e' he' (fun i hi => hne i (Nat.lt_succ_of_lt hi)) t ht
    obtain ⟨st', c_r, hrun_r, hlo', hfr', hinv', hcr⟩ := ih (idx + 1) (by omega) (by omega) st1
      (by simp [st1, r1, hr2]) (by simp [st1, r1, hr10]) (by simp [st1, r1, hr14])
      (by simp [st1]) (by simp [st1, r1, hr18]) (by simp [st1, r1, hr19]) hfr1 hinv1' hinv2'
    refine ⟨st', 3 + 20 + c_r + 1, runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st1, 20, c_r,
      by simp [Expr.eval, BinOp.eval, hr16, hr18, hidx_lt, show 1 < 2 ^ w by omega],
      by decide, hbody, hrun_r, by simp [Expr.size]⟩)),
      fun r hr => (hlo' r hr).trans (by simp [st1, r1, show r ≠ 16 by omega, show r ≠ 17 by omega]),
      hfr', hinv', ?_⟩
    rw [show m0 - (idx + 1) = rem by omega] at hcr
    rw [hrem]
    omega

/-! ## Helper 3: Space/cost budgets and main `lemma55Program_runs` -/

/-- Total heap space above `heap` required by `lemma55InitProc`. -/
noncomputable def lemma55Space (Q_AN : Program) (K_AN : ℝ) (c_AN h L_in L_w P_fp k_nat vCap eCap n0 m0 : ℕ) : ℕ :=
  let L_sim := lsstLSimMin c_AN n0 (2 * m0) L_in h
  let lsfSp := lsfStaticSize vCap eCap n0 n0 L_w + 2 * (eCap * L_w) +
    lsstSpace Q_AN K_AN n0 (2 * m0) L_sim h +
    200 * (n0 + m0 + 1) * (L_w + L_sim + auxLogCap n0 + 20) + 1000
  eCap * L_in + 2 * L_w + k_nat * lsfSp + max (4 * L_w) (mwuEdgeStepSpace L_in L_w P_fp) + 1

/-- Total deterministic step bound for `lemma55InitProc`, independent of `vCap` and `eCap`. -/
noncomputable def lemma55Cost (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (h L_in L_w P_fp k_nat n0 m0 : ℕ) : ℕ :=
  let initC := lsfInitCostFactor *
    Nat.ceil (((m0 + n0 + 1 : ℕ) : ℝ) * lsfOverhead Q_AN c_AN K_AN n0 m0 L_in L_w h)
  k_nat * (initC + m0 * (mwuEdgeStepCost L_in L_w P_fp + 80) + 200) +
    500 * L_w * L_w + 800 * L_w + 20 * Nat.log 2 (n0 + 2) + 30 * m0 + 1000

/-- Prefix weight-envelope helper for step `j < k_nat` of the MWU outer loop. -/
lemma mwu_prefix_weight_envelope {K_AN : ℝ} {G₀ : MGraph} {ℓ₀ : ℕ → ℝ} {k_nat j : ℕ}
    (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty) (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e)
    (hk : 1 ≤ k_nat) (hj_lt : j < k_nat)
    {v : ℕ → ℕ → ℝ} {S₀ : ℕ → LSFState}
    (hv0 : ∀ e ∈ G₀.E, v 0 e = 1)
    (hv_pos : ∀ i ≤ j, ∀ e ∈ G₀.E, 0 < v i e)
    (hinit : ∀ i < j, ∃ T_raw C_reps W_T,
      ValidLSFParams (4 * max K_AN 1 + 5) (5 / 4)
        (defaultThreshNat K_AN G₀.n k_nat : ℝ) (defaultK_sigma K_AN : ℝ)
        G₀ ℓ₀ (v i) (k_nat : ℝ) T_raw (S₀ i).r₀ C_reps (S₀ i).π W_T ∧
      S₀ i = initLSFWith G₀ ℓ₀ (v i) (k_nat : ℝ) T_raw (S₀ i).r₀ C_reps (S₀ i).π W_T
        (defaultThreshNat K_AN G₀.n k_nat : ℝ))
    (hv_step : ∀ i < j, ∀ e ∈ G₀.E,
      (1 - 1 / (4 * (k_nat : ℝ))) * v i e * Real.exp ((S₀ i).wstr e / (lemma55RhoNat K_AN G₀.n k_nat : ℝ)) ≤
        v (i + 1) e ∧
      v (i + 1) e ≤
        (1 + 1 / (4 * (k_nat : ℝ))) * v i e * Real.exp ((S₀ i).wstr e / (lemma55RhoNat K_AN G₀.n k_nat : ℝ))) :
    ∀ e ∈ G₀.E, (1 / 2 : ℝ) ≤ v j e ∧ v j e ≤ 8 * (G₀.E.card : ℝ) := by
  by_cases hj0 : j = 0
  · subst hj0
    intro e he
    have hm1 : (1 : ℝ) ≤ (G₀.E.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨e, he⟩
    rw [hv0 e he]
    constructor <;> linarith
  · have hj1 : 1 ≤ j := Nat.pos_of_ne_zero hj0
    set C_lsst := 4 * max K_AN 1 + 5
    set K_σ := (defaultK_sigma K_AN : ℝ)
    set K₀ := lemma54K0 C_lsst (5 / 4) K_σ
    set L := Real.log ((G₀.n : ℝ) + 2)
    set W := K₀ * L ^ 4
    set U := K₀ * (k_nat : ℝ) * L ^ 6
    set ρ := (lemma55RhoNat K_AN G₀.n k_nat : ℝ)
    set δ := 1 / (4 * (k_nat : ℝ))
    have hk_real : (1 : ℝ) ≤ (k_nat : ℝ) := by exact_mod_cast hk
    have hk_pos : (0 : ℝ) < (k_nat : ℝ) := by linarith
    have hK₀_ge : 2240 ≤ K₀ := lemma54K0_ge C_lsst (5 / 4) K_σ
    have hK₀_pos : 0 < K₀ := by linarith
    have hL_ge : (1 / 2 : ℝ) < L := by
      have hb := real_log_add_two_bounds G₀.n
      have hd : (2 : ℝ) ≤ ((Nat.log 2 (G₀.n + 2) + 1 : ℕ) : ℝ) := by
        have : 1 ≤ Nat.log 2 (G₀.n + 2) := Nat.log_pos (by decide) (by omega)
        exact_mod_cast (by omega : 2 ≤ Nat.log 2 (G₀.n + 2) + 1)
      nlinarith [hb.1]
    have hL_pos : 0 < L := by linarith
    have hU_pos : 0 < U := mul_pos (mul_pos hK₀_pos hk_pos) (pow_pos hL_pos 6)
    have hW_nn : 0 ≤ W := mul_nonneg hK₀_pos.le (pow_nonneg hL_pos.le 4)
    obtain ⟨_, hρ_ge, _⟩ := lemma55Rho_bounds K_AN G₀.n hk
    have hρ_pos : 0 < ρ := by linarith
    have hδ0 : 0 ≤ δ := by positivity
    have hδ_le_j : δ ≤ 1 / (4 * (j : ℝ)) := by
      have hj_r : (j : ℝ) ≤ (k_nat : ℝ) := by exact_mod_cast (Nat.le_of_lt hj_lt)
      have hj_pos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
      dsimp only [δ]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    have hWU_j : (j : ℝ) * (2 * W / ρ) ≤ 1 := by
      have hj_r : (j : ℝ) ≤ (k_nat : ℝ) := by exact_mod_cast (Nat.le_of_lt hj_lt)
      have hL2_ge : (1 / 4 : ℝ) ≤ L ^ 2 := by nlinarith
      have h1 : (k_nat : ℝ) * (2 * W) ≤ (2 / 10) * (1 / L ^ 2) * (10 * U) := by
        have hEq : (2 / 10 : ℝ) * (1 / L ^ 2) * (10 * (K₀ * (k_nat : ℝ) * L ^ 6)) =
            2 * (K₀ * L ^ 4) * (k_nat : ℝ) := by field_simp [ne_of_gt hL_pos]
        dsimp only [W, U]; linarith
      have h2 : (2 / 10 : ℝ) * (1 / L ^ 2) ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity)]; nlinarith
      have h3 : (k_nat : ℝ) * (2 * W) ≤ ρ := by
        calc (k_nat : ℝ) * (2 * W)
            ≤ (2 / 10) * (1 / L ^ 2) * (10 * U) := h1
          _ ≤ 1 * (10 * U) := mul_le_mul_of_nonneg_right h2 (by linarith)
          _ ≤ ρ := by linarith
      have h4 : (j : ℝ) * (2 * W) ≤ (k_nat : ℝ) * (2 * W) :=
        mul_le_mul_of_nonneg_right hj_r (by linarith)
      rw [mul_div_assoc', div_le_one hρ_pos]; linarith
    have hsafe_pos : ∀ e ∈ G₀.E, 0 < safeLen G₀ ℓ₀ e := fun e he => by
      rw [safeLen_eq_of_mem ℓ₀ he]; exact hℓ₀ e he
    have hw_bd : ∀ i < j, ∀ e ∈ G₀.E, 1 ≤ (S₀ i).wstr e ∧ (S₀ i).wstr e ≤ U := by
      intro i hi e he
      obtain ⟨T_raw, C_reps, W_T, hp, hS⟩ := hinit i hi
      have hsp0 := (lemma_5_4_with_explicit C_lsst (5 / 4) K_σ G₀ hG₀ hV₀ ℓ₀ (v i) hℓ₀
        (hv_pos i (Nat.le_of_lt hi)) (k_nat : ℝ) hk_real T_raw (S₀ i).r₀ C_reps (S₀ i).π W_T
        (defaultThreshNat K_AN G₀.n k_nat : ℝ) hp [] trivial (safeLen G₀ ℓ₀) hsafe_pos
        (fun f hf _ _ => safeLen_eq_of_mem ℓ₀ hf)).2
      have hholds0 := hsp0.2.2.2.2.2.2.2.2.1
      rw [← hS] at hholds0
      have hstr := hholds0.2.2.2 e he
      exact ⟨(one_le_stretch_safeLen' hℓ₀ he).trans hstr.1, hstr.2⟩
    have hw_sum : ∀ i < j, ∑ e ∈ G₀.E, v i e * (S₀ i).wstr e ≤ W * G₀.norm1 (v i) := by
      intro i hi
      obtain ⟨T_raw, C_reps, W_T, hp, hS⟩ := hinit i hi
      have hsp0 := (lemma_5_4_with_explicit C_lsst (5 / 4) K_σ G₀ hG₀ hV₀ ℓ₀ (v i) hℓ₀
        (hv_pos i (Nat.le_of_lt hi)) (k_nat : ℝ) hk_real T_raw (S₀ i).r₀ C_reps (S₀ i).π W_T
        (defaultThreshNat K_AN G₀.n k_nat : ℝ) hp [] trivial (safeLen G₀ ℓ₀) hsafe_pos
        (fun f hf _ _ => safeLen_eq_of_mem ℓ₀ hf)).2
      have hbd := hsp0.2.2.2.2.2.2.2.2.2.1
      rw [← hS] at hbd
      dsimp only [W, K₀, lemma54K0] at hbd ⊢
      linarith [show lemma54K0 C_lsst (5 / 4) K_σ * G₀.norm1 (v i) * L ^ 4 =
        lemma54K0 C_lsst (5 / 4) K_σ * L ^ 4 * G₀.norm1 (v i) by ring]
    have hEnv := (approx_mwu_weight_bounds (G₀ := G₀) (k := j) (wstr := fun i e => (S₀ i).wstr e)
      hj1 hW_nn hU_pos hρ_ge hδ0 hδ_le_j hWU_j hv0 hv_pos hw_bd hw_sum hv_step).2.2
    exact hEnv j le_rfl

set_option maxHeartbeats 800000 in
/-- Outer `k_nat`-round MWU loop execution lemma. -/
lemma mwuOuterLoop_runs {w h q c_AN bLsf bWeightsLoop bEdgeStep bDiv bExp bMul bCopy bFill
    g0Ptr lenArr L_in P_fp k_nat L_w vCap eCap handlesOut wtArr onePtr rhoPtr wtEnd vCap0 eCap0 : ℕ}
    {p Q_AN : Program} {K_AN : ℝ} {G₀ : MGraph} {ℓ₀ : ℕ → ℝ} {ω : ℕ → Bool} {mem0 : ℕ → ℕ}
    (hc : 1 ≤ c_AN) (hh : 1 ≤ h) (hw : 3 * h + 2 ≤ w)
    (hLin1 : 1 ≤ L_in) (hLin_le : L_in ≤ L_w) (hk : 1 ≤ k_nat)
    (hdiv : h ∣ P_fp) (hq_P : q + 11 ≤ P_fp) (hk_q : 8 * k_nat ≤ 2 ^ q)
    (hP_Lin : P_fp + 6 ≤ h * L_in)
    (hm_Lin : 32 * (G₀.E.card + 1) * 2 ^ P_fp < 2 ^ (h * L_in - 1))
    (h2P_ltw : 2 * P_fp + 9 < 2 ^ w)
    (hHld_ltw : 3 * (4 * k_nat * (hldDepthBound G₀.n + 1)) < 2 ^ w)
    (hrho_cap : lemma55RhoNat K_AN G₀.n k_nat < 2 ^ (h * (L_w - L_in)))
    (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    (hdg0 : DynGraphAt mem0 g0Ptr vCap0 eCap0 G₀)
    (hvCap_le : vCap0 ≤ vCap) (heCap_le : eCap0 ≤ eCap) (heCap1 : 1 ≤ eCap)
    (hℓ₀_mem : ∀ e ∈ G₀.E, Valid mem0 (lenArr + e * L_in) h L_in ∧
      fixVal mem0 (lenArr + e * L_in) h L_in P_fp = ℓ₀ e ∧ 0 < ℓ₀ e)
    (hℓ₀_eq : ℓ₀ = memArrayReal mem0 lenArr G₀ h L_in P_fp)
    (hg0_le : g0Ptr + dynGraphSize vCap0 eCap0 ≤ wtArr)
    (hlen_le : lenArr + eCap0 * L_in ≤ wtArr)
    (hhnd_le : handlesOut + k_nat ≤ wtArr)
    (hhnd_g0 : handlesOut + k_nat ≤ g0Ptr ∨ g0Ptr + dynGraphSize vCap0 eCap0 ≤ handlesOut)
    (hhnd_len : handlesOut + k_nat ≤ lenArr ∨ lenArr + eCap0 * L_in ≤ handlesOut)
    (hone_def : onePtr = wtArr + eCap * L_in)
    (hrho_def : rhoPtr = onePtr + L_w)
    (hwtEnd_def : wtEnd = rhoPtr + L_w)
    (hsp : wtArr + lemma55Space Q_AN K_AN c_AN h L_in L_w P_fp k_nat vCap eCap G₀.n G₀.m < 2 ^ w)
    (hv_one0 : Valid mem0 onePtr h L_w) (hone_eq0 : intVal mem0 onePtr h L_w = (2 : ℤ) ^ P_fp)
    (hv_rho0 : Valid mem0 rhoPtr h L_w)
    (hrho_eq0 : intVal mem0 rhoPtr h L_w = (lemma55RhoNat K_AN G₀.n k_nat : ℤ) * (2 : ℤ) ^ P_fp)
    (hpLsf : p.HasAt bLsf (lsfModuleProcs Q_AN c_AN K_AN bLsf h))
    (hQ : ∀ (G_a : Cited.WGraph), G_a.graph.IsValid → G_a.graph.IsLoopless → G_a.IsConnected →
      (∀ e ∈ G_a.edges, 1 ≤ e.2.2) →
      ∃ out cost,
        RunsTo (wordSize c_AN G_a.encode) Q_AN G_a.encode (fun _ => false) out cost ∧
          G_a.IsSpanningTree out ∧
          G_a.totalStretch out ≤ K_AN * G_a.m * Cited.logLogFactor G_a.n ∧
          (cost : ℝ) ≤ K_AN * (G_a.m + 1) *
            (Cited.logLogFactor G_a.n + Cited.weightFactor G_a.n G_a.maxWeight))
    (hpWLoop : p.procs[bWeightsLoop]? = some (mwuWeightsLoopProc bEdgeStep))
    (hpStep : p.procs[bEdgeStep]? = some (mwuEdgeStepProc bDiv bExp bMul bCopy bFill))
    (hDiv : MeetsContract w p bDiv (fixedDivideContract w h))
    (hExp : MeetsContract w p bExp (positiveExponentialContract w h q))
    (hMul : MeetsContract w p bMul (fixedMultiplyContract w h))
    (hCopy : MeetsContract w p bCopy (memCopyContract w))
    (hFill : MeetsContract w p bFill (memFillContract w)) :
    let L_sim := lsstLSimMin c_AN G₀.n (2 * G₀.m) L_in h
    let lsfSp := lsfStaticSize vCap eCap G₀.n G₀.n L_w + 2 * (eCap * L_w) +
      lsstSpace Q_AN K_AN G₀.n (2 * G₀.m) L_sim h +
      200 * (G₀.n + G₀.m + 1) * (L_w + L_sim + auxLogCap G₀.n + 20) + 1000
    let initC := lsfInitCostFactor *
      Nat.ceil (((G₀.m + G₀.n + 1 : ℕ) : ℝ) * lsfOverhead Q_AN c_AN K_AN G₀.n G₀.m L_in L_w h)
    ∀ j ≤ k_nat, ∀ (st : State) (curHeap : ℕ)
      (v : ℕ → ℕ → ℝ) (S₀ : ℕ → LSFState) (x₀ : ℕ → LSFConcrete) (hs : ℕ → ℕ),
      st.regs 0 = g0Ptr → st.regs 1 = lenArr → st.regs 2 = L_in → st.regs 3 = P_fp →
      st.regs 4 = k_nat → st.regs 5 = L_w → st.regs 6 = vCap → st.regs 7 = eCap →
      st.regs 8 = handlesOut → st.regs 10 = wtArr → st.regs 11 = onePtr →
      st.regs 12 = rhoPtr → st.regs 13 = curHeap → st.regs 16 = j →
      wtEnd ≤ curHeap → curHeap ≤ wtEnd + j * lsfSp → ZeroFrom st.mem curHeap →
      (∀ z < wtEnd, (z < handlesOut ∨ handlesOut + k_nat ≤ z) →
        (z < wtArr ∨ wtArr + eCap0 * L_in ≤ z) → st.mem z = mem0 z) →
      (∀ e ∈ G₀.E, Valid st.mem (wtArr + e * L_in) h L_in ∧
        fixVal st.mem (wtArr + e * L_in) h L_in P_fp = v j e) →
      v j = memArrayReal st.mem wtArr G₀ h L_in P_fp →
      (∀ e ∈ G₀.E, v 0 e = 1) →
      (∀ i ≤ j, ∀ e ∈ G₀.E, 0 < v i e) →
      (∀ i < j, ∃ T_raw C_reps W_T,
        ValidLSFParams (4 * max K_AN 1 + 5) (5 / 4)
          (defaultThreshNat K_AN G₀.n k_nat : ℝ) (defaultK_sigma K_AN : ℝ)
          G₀ ℓ₀ (v i) (k_nat : ℝ) T_raw (S₀ i).r₀ C_reps (S₀ i).π W_T ∧
        S₀ i = initLSFWith G₀ ℓ₀ (v i) (k_nat : ℝ) T_raw (S₀ i).r₀ C_reps (S₀ i).π W_T
          (defaultThreshNat K_AN G₀.n k_nat : ℝ)) →
      (∀ i < j, ∀ e ∈ G₀.E,
        (1 - 1 / (4 * (k_nat : ℝ))) * v i e * Real.exp ((S₀ i).wstr e / (lemma55RhoNat K_AN G₀.n k_nat : ℝ)) ≤
          v (i + 1) e ∧
        v (i + 1) e ≤
          (1 + 1 / (4 * (k_nat : ℝ))) * v i e * Real.exp ((S₀ i).wstr e / (lemma55RhoNat K_AN G₀.n k_nat : ℝ))) →
      (∀ i < j, st.mem (handlesOut + i) = hs i ∧
        (LSFRep h).rep (hs i) (S₀ i) (x₀ i) st.mem ∧
        ∀ a, (LSFRep h).foot (hs i) (x₀ i) a → wtEnd ≤ a ∧ a < curHeap) →
      ∃ (st' : State) (c endHeap : ℕ) (v' : ℕ → ℕ → ℝ) (S₀' : ℕ → LSFState) (x₀' : ℕ → LSFConcrete) (hs' : ℕ → ℕ),
        Runs w p ω
          (.loop (.bin .lt (.reg 16) (.reg 4))
            ((.call 17 (bLsf + lsfIdxInit) [.reg 0, .reg 1, .reg 10, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 13] ;;
              .store (.bin .add (.reg 8) (.reg 16)) (.reg 13) ;;
              .call 18 bWeightsLoop [.reg 0, .reg 13, .reg 10, .reg 11, .reg 12, .reg 2, .reg 5, .reg 3, .reg 17] ;;
              .assign 13 (.reg 17)) ;;
             .assign 16 (.bin .add (.reg 16) (.const 1))))
          st .normal st' c ∧
        st'.regs 13 = endHeap ∧
        wtEnd ≤ endHeap ∧ endHeap ≤ wtEnd + k_nat * lsfSp ∧
        ZeroFrom st'.mem endHeap ∧
        (∀ z < wtArr, (z < handlesOut ∨ handlesOut + k_nat ≤ z) → st'.mem z = mem0 z) ∧
        (∀ e ∈ G₀.E, v' 0 e = 1) ∧
        (∀ i ≤ k_nat, ∀ e ∈ G₀.E, 0 < v' i e) ∧
        (∀ i < k_nat, ∃ T_raw C_reps W_T,
          ValidLSFParams (4 * max K_AN 1 + 5) (5 / 4)
            (defaultThreshNat K_AN G₀.n k_nat : ℝ) (defaultK_sigma K_AN : ℝ)
            G₀ ℓ₀ (v' i) (k_nat : ℝ) T_raw (S₀' i).r₀ C_reps (S₀' i).π W_T ∧
          S₀' i = initLSFWith G₀ ℓ₀ (v' i) (k_nat : ℝ) T_raw (S₀' i).r₀ C_reps (S₀' i).π W_T
            (defaultThreshNat K_AN G₀.n k_nat : ℝ)) ∧
        (∀ i < k_nat, ∀ e ∈ G₀.E,
          (1 - 1 / (4 * (k_nat : ℝ))) * v' i e * Real.exp ((S₀' i).wstr e / (lemma55RhoNat K_AN G₀.n k_nat : ℝ)) ≤
            v' (i + 1) e ∧
          v' (i + 1) e ≤
            (1 + 1 / (4 * (k_nat : ℝ))) * v' i e * Real.exp ((S₀' i).wstr e / (lemma55RhoNat K_AN G₀.n k_nat : ℝ))) ∧
        (∀ i < k_nat, st'.mem (handlesOut + i) = hs' i ∧
          (LSFRep h).rep (hs' i) (S₀' i) (x₀' i) st'.mem ∧
          ∀ a, (LSFRep h).foot (hs' i) (x₀' i) a → wtEnd ≤ a ∧ a < endHeap) ∧
        c ≤ (k_nat - j) * (initC + G₀.m * (mwuEdgeStepCost L_in L_w P_fp + 80) + 190) + 10 := by
  intro L_sim lsfSp initC
  have h2w_16 : 16 ≤ 2 ^ w := by
    have : 2 ^ 5 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hsp_unfold : wtEnd + k_nat * lsfSp + max (4 * L_w) (mwuEdgeStepSpace L_in L_w P_fp) < 2 ^ w := by
    dsimp only [lemma55Space] at hsp
    have hlsf_eq : lsfSp = lsfStaticSize vCap eCap G₀.n G₀.n L_w + 2 * (eCap * L_w) +
        lsstSpace Q_AN K_AN G₀.n (2 * G₀.m) (lsstLSimMin c_AN G₀.n (2 * G₀.m) L_in h) h +
        200 * (G₀.n + G₀.m + 1) * (L_w + lsstLSimMin c_AN G₀.n (2 * G₀.m) L_in h + auxLogCap G₀.n + 20) + 1000 := rfl
    rw [← hlsf_eq] at hsp
    omega
  have hrho_pos : 1 ≤ lemma55RhoNat K_AN G₀.n k_nat := lemma55RhoNat_pos K_AN G₀.n hk
  obtain ⟨h10_thresh, hρ_ge, _⟩ := lemma55Rho_bounds K_AN G₀.n hk
  have hthresh_cap : defaultThreshNat K_AN G₀.n k_nat < 2 ^ (h * (L_w - L_in)) := by omega
  have heCap_mul_in : eCap0 * L_in ≤ eCap * L_in := Nat.mul_le_mul_right L_in heCap_le
  intro j hj
  obtain ⟨rem, hrem⟩ : ∃ rem, k_nat - j = rem := ⟨_, rfl⟩
  induction rem generalizing j with
  | zero =>
    intro st curHeap v S₀ x₀ hs _ _ _ _ hr4 _ _ _ _ _ _ _ hr13 hr16 hwe hch hz hfr _ _
      hv0 hv_pos hinit hv_step hhnd
    have hj_eq : j = k_nat := by omega
    subst hj_eq
    refine ⟨st, 4, curHeap, v, S₀, x₀, hs,
      runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hr16, hr4, show 0 < 2 ^ w by omega],
        rfl, by simp [Expr.size]⟩),
      hr13, hwe, hch, hz, fun z hz1 hz2 => hfr z (by omega) hz2 (Or.inl hz1),
      hv0, hv_pos, hinit, hv_step, hhnd, by omega⟩
  | succ rem ih =>
    intro st curHeap v S₀ x₀ hs hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8 hr10 hr11 hr12 hr13 hr16
      hwe hch hz hfr hwt_j hvj_eq hv0 hv_pos hinit hv_step hhnd
    have hj_lt : j < k_nat := by omega
    have hdg_st : DynGraphAt st.mem g0Ptr vCap0 eCap0 G₀ :=
      hdg0.of_agree fun a ha1 ha2 =>
        hfr a (by omega) (by rcases hhnd_g0 with h | h <;> [right; left] <;> omega) (Or.inl (by omega))
    have hlen_st : ∀ e ∈ G₀.E, Valid st.mem (lenArr + e * L_in) h L_in ∧
        fixVal st.mem (lenArr + e * L_in) h L_in P_fp = ℓ₀ e ∧ 0 < ℓ₀ e := by
      intro e he
      have he_cap : e < eCap0 := hdg0.2.2.1 e he
      have he_mul : (e + 1) * L_in ≤ eCap0 * L_in := Nat.mul_le_mul_right L_in (by omega)
      have he_add : e * L_in + L_in = (e + 1) * L_in := by ring
      have hag : ∀ t < L_in, st.mem (lenArr + e * L_in + t) = mem0 (lenArr + e * L_in + t) := fun t ht =>
        hfr _ (by omega) (by rcases hhnd_len with h | h <;> [right; left] <;> omega) (Or.inl (by omega))
      obtain ⟨hv0e, hfx0e, hpos0e⟩ := hℓ₀_mem e he
      exact ⟨fun t ht => by rw [hag t ht]; exact hv0e t ht,
        by unfold fixVal; rw [intVal_congr hag]; exact hfx0e, hpos0e⟩
    have hpre_lsf : lsfInitPreFor c_AN K_AN w h G₀
        [g0Ptr, lenArr, wtArr, L_in, P_fp, k_nat, L_w, vCap, eCap, curHeap] st.mem :=
      ⟨v j, ℓ₀, g0Ptr, vCap0, eCap0, lenArr, wtArr, L_in, P_fp, k_nat, L_w, vCap, eCap, curHeap,
        rfl, hc, hh, hw, hG₀, hV₀, hdg_st, by omega, hvCap_le, heCap_le, heCap1,
        by omega, by omega, hLin1, by omega, hdiv, hk, hHld_ltw, hLin_le,
        by have : h * L_in ≤ h * L_w := Nat.mul_le_mul_left h hLin_le; omega,
        hthresh_cap, hlen_st, fun e he => ⟨(hwt_j e he).1, (hwt_j e he).2, hv_pos j le_rfl e he⟩⟩
    have hlsfSp_eq : lsfInitSpace Q_AN K_AN c_AN h
        [g0Ptr, lenArr, wtArr, L_in, P_fp, k_nat, L_w, vCap, eCap, curHeap] st.mem = lsfSp := by
      dsimp only [lsfInitSpace, lsfSp, L_sim]
      simp only [List.getD_cons_zero, List.getD_cons_succ, hdg_st.2.2.2.2.2.1, hdg_st.2.2.2.2.2.2.1]
    have hlsfC_eq : lsfInitCost Q_AN c_AN K_AN h
        [g0Ptr, lenArr, wtArr, L_in, P_fp, k_nat, L_w, vCap, eCap, curHeap] st.mem = initC := by
      dsimp only [lsfInitCost, initC]
      simp only [List.getD_cons_zero, List.getD_cons_succ, hdg_st.2.2.2.2.2.1, hdg_st.2.2.2.2.2.2.1]
    have hjk_sp : (j + 1) * lsfSp ≤ k_nat * lsfSp := Nat.mul_le_mul_right lsfSp (by omega)
    have hadd_sp : j * lsfSp + lsfSp = (j + 1) * lsfSp := by ring
    have hsp_lsf : curHeap + lsfInitSpace Q_AN K_AN c_AN h
        [g0Ptr, lenArr, wtArr, L_in, P_fp, k_nat, L_w, vCap, eCap, curHeap] st.mem < 2 ^ w := by
      rw [hlsfSp_eq]; omega
    have hwords_lsf : ∀ a ∈ [g0Ptr, lenArr, wtArr, L_in, P_fp, k_nat, L_w, vCap, eCap, curHeap], a < 2 ^ w := by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      have hv_lt : vCap < 2 ^ w := by
        have : lsfStaticSize vCap eCap G₀.n G₀.n L_w ≤ lsfSp := by dsimp [lsfSp]; omega
        have : vCap ≤ lsfStaticSize vCap eCap G₀.n G₀.n L_w := by
          dsimp [lsfStaticSize, dynGraphSize]; omega
        have : 1 * lsfSp ≤ k_nat * lsfSp := Nat.mul_le_mul_right lsfSp hk
        omega
      have he_lt_w : eCap < 2 ^ w := by
        have : eCap * 1 ≤ eCap * L_in := Nat.mul_le_mul_left eCap hLin1
        omega
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    -- 1. Run lsfInit
    obtain ⟨bodyInit, hbodyInit, oInit, stInit, cInit, hrunInit, S_new, x_new, hsG0, hrep_new, hpost_new,
      hresp_new, hcInit⟩ :=
      lsfInit_runs_of_hasAt_for hpLsf hQ st.pos ω hwords_lsf hpre_lsf hz hsp_lsf
    set nextHeap := oInit.value
    have hnext_ge : curHeap ≤ nextHeap := hresp_new.1
    have hnext_le : nextHeap ≤ curHeap + lsfSp := hlsfSp_eq ▸ hresp_new.2.1
    have hz_init : ZeroFrom stInit.mem nextHeap := hresp_new.2.2.1
    have hfr_init : ∀ a < curHeap, stInit.mem a = st.mem a := fun a ha => hresp_new.2.2.2.1 a ha id
    have hfoot_new : ∀ a, (LSFRep h).foot curHeap x_new a → curHeap ≤ a ∧ a < nextHeap := fun a ha =>
      (hresp_new.2.2.2.2 a ha).resolve_left id
    have hend_new_le : x_new.endAddr curHeap ≤ nextHeap := by
      by_contra hgt
      have hlt : nextHeap < x_new.endAddr curHeap := by omega
      have := hfoot_new nextHeap ⟨hnext_ge, hlt⟩
      omega
    -- Extract ValidLSFParams and S_new = initLSFWith ... from hpost_new
    obtain ⟨G₀', _, _, _, _, _, _, _, _, _, _, _, _, T_raw, C_reps, W_T,
      hargs_p, _, hVparams, hS_eq, _, hhdr_e, _, _, hhdr_Lw, _, _, _⟩ := hpost_new
    simp only [List.cons.injEq, and_true] at hargs_p
    rcases hargs_p with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hG₀_eq : G₀' = G₀ := by
      have h1 : S_new.G₀ = G₀' := by rw [hS_eq]; rfl
      exact h1.symm.trans hsG0
    subst G₀'
    have hℓ_fun_eq : memArrayReal st.mem lenArr G₀ h L_in P_fp = ℓ₀ := by
      rw [hℓ₀_eq]
      funext e
      by_cases he : e ∈ G₀.E
      · rw [memArrayReal_eq he, memArrayReal_eq he, (hlen_st e he).2.1, ← (hℓ₀_mem e he).2.1]
      · unfold memArrayReal; simp [he]
    have hVparams' : ValidLSFParams (4 * max K_AN 1 + 5) (5 / 4)
        (defaultThreshNat K_AN G₀.n k_nat : ℝ) (defaultK_sigma K_AN : ℝ)
        G₀ ℓ₀ (v j) (k_nat : ℝ) T_raw S_new.r₀ C_reps S_new.π W_T := by
      rwa [hℓ_fun_eq, ← hvj_eq] at hVparams
    have hS_eq' : S_new = initLSFWith G₀ ℓ₀ (v j) (k_nat : ℝ) T_raw S_new.r₀ C_reps S_new.π W_T
        (defaultThreshNat K_AN G₀.n k_nat : ℝ) := by
      rwa [hℓ_fun_eq, ← hvj_eq] at hS_eq
    have hS_new_G : S_new.G = G₀ := by rw [hS_eq']; rfl
    -- Stretch bounds on S_new and weight envelope on v j
    have hsafe_pos : ∀ e ∈ G₀.E, 0 < safeLen G₀ ℓ₀ e := fun e he => by
      rw [safeLen_eq_of_mem ℓ₀ he]; exact (hℓ₀_mem e he).2.2
    have hwstr_bds_new : ∀ e ∈ G₀.E,
        1 ≤ S_new.wstr e ∧ S_new.wstr e ≤ (lemma55RhoNat K_AN G₀.n k_nat : ℝ) / 10 := by
      intro e he
      have hk_real : (1 : ℝ) ≤ (k_nat : ℝ) := by exact_mod_cast hk
      have hsp0 := (lemma_5_4_with_explicit (4 * max K_AN 1 + 5) (5 / 4) (defaultK_sigma K_AN : ℝ)
        G₀ hG₀ hV₀ ℓ₀ (v j) (fun f hf => (hℓ₀_mem f hf).2.2) (hv_pos j le_rfl) (k_nat : ℝ) hk_real
        T_raw S_new.r₀ C_reps S_new.π W_T (defaultThreshNat K_AN G₀.n k_nat : ℝ) hVparams'
        [] trivial (safeLen G₀ ℓ₀) hsafe_pos (fun f hf _ _ => safeLen_eq_of_mem ℓ₀ hf)).2
      have hholds0 := hsp0.2.2.2.2.2.2.2.2.1
      rw [← hS_eq'] at hholds0
      have hstr := hholds0.2.2.2 e he
      have hstr2 : S_new.wstr e ≤
          max (defaultK_sigma K_AN : ℝ) (max (112 * (1 + 5 / 4) * max 1 (4 * max K_AN 1 + 5)) 2240) *
            (k_nat : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 6 := hstr.2
      have hρ_ge' : 10 * (max (defaultK_sigma K_AN : ℝ) (max (112 * (1 + 5 / 4) * max 1 (4 * max K_AN 1 + 5)) 2240) *
          (k_nat : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 6) ≤ (lemma55RhoNat K_AN G₀.n k_nat : ℝ) := hρ_ge
      exact ⟨(one_le_stretch_safeLen' (fun f hf => (hℓ₀_mem f hf).2.2) he).trans hstr.1,
        by linarith only [hstr2, hρ_ge']⟩
    have hvj_env : ∀ e ∈ G₀.E, (1 / 2 : ℝ) ≤ v j e ∧ v j e ≤ 8 * (G₀.E.card : ℝ) :=
      mwu_prefix_weight_envelope hG₀ hV₀ (fun f hf => (hℓ₀_mem f hf).2.2) hk hj_lt
        hv0 hv_pos hinit hv_step
    -- 2. Store curHeap into handlesOut + j
    let memAfterStore := Function.update stInit.mem (handlesOut + j) curHeap
    have hstore_lt_wt : handlesOut + j < wtArr := by omega
    have hmem_store_eq : ∀ z, z ≠ handlesOut + j → memAfterStore z = stInit.mem z :=
      fun z hz' => Function.update_of_ne hz' _ _
    have hdg_ms : DynGraphAt memAfterStore g0Ptr vCap0 eCap0 G₀ :=
      hdg_st.of_agree fun a ha1 ha2 => by
        rw [hmem_store_eq a (by rcases hhnd_g0 with h | h <;> omega)]
        exact hfr_init a (by omega)
    have hrep_ms : (LSFRep h).rep curHeap S_new x_new memAfterStore :=
      ((lsfRep_local h curHeap S_new x_new stInit.mem memAfterStore fun a ha =>
        (hmem_store_eq a (by have := hfoot_new a ha; omega)).symm).1 hrep_new)
    have hx_eCap : x_new.eCap = eCap :=
      hrep_new.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1.symm.trans hhdr_e
    have hx_Lw : x_new.L_w = L_w :=
      hrep_new.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1.symm.trans hhdr_Lw
    have hone_ms : ∀ t < L_w, memAfterStore (onePtr + t) = mem0 (onePtr + t) := fun t ht => by
      rw [hmem_store_eq _ (by omega), hfr_init _ (by omega)]
      exact hfr _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))
    have hrho_ms : ∀ t < L_w, memAfterStore (rhoPtr + t) = mem0 (rhoPtr + t) := fun t ht => by
      rw [hmem_store_eq _ (by omega), hfr_init _ (by omega)]
      exact hfr _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))
    have hwt_ms : ∀ e ∈ G₀.E,
        Valid memAfterStore (wtArr + e * L_in) h L_in ∧
        fixVal memAfterStore (wtArr + e * L_in) h L_in P_fp = v j e ∧
        (1 / 2 : ℝ) ≤ v j e ∧ v j e ≤ 8 * (G₀.E.card : ℝ) := by
      intro e he
      have he_cap : e < eCap0 := hdg0.2.2.1 e he
      have he_mul : (e + 1) * L_in ≤ eCap0 * L_in := Nat.mul_le_mul_right L_in (by omega)
      have he_add : e * L_in + L_in = (e + 1) * L_in := by ring
      have heq_t : ∀ t < L_in, memAfterStore (wtArr + e * L_in + t) = st.mem (wtArr + e * L_in + t) :=
        fun t ht => by rw [hmem_store_eq _ (by omega)]; exact hfr_init _ (by omega)
      exact ⟨fun t ht => by rw [heq_t t ht]; exact (hwt_j e he).1 t ht,
        by unfold fixVal; rw [intVal_congr heq_t]; exact (hwt_j e he).2,
        (hvj_env e he).1, (hvj_env e he).2⟩
    have hz_ms : ZeroFrom memAfterStore nextHeap := fun z hz' => by
      rw [hmem_store_eq z (by omega)]; exact hz_init z hz'
    -- 3. Call mwuWeightsLoop
    obtain ⟨stWL, cWL, hrunWL, hzWL, hfrWL, hinvWL, hcWL⟩ :=
      mwuWeightsLoop_runs (p := p) (ω := ω) (pos := stInit.pos) (mem := memAfterStore)
        hh hw hLin_le hk hdiv hq_P hk_q hP_Lin hm_Lin h2P_ltw hrho_pos hrho_cap
        hdg_ms hrep_ms hS_new_G hx_Lw hwstr_bds_new hwt_ms
        hg0_le (by rw [hx_eCap]; omega) (by rw [hx_eCap]; exact heCap_le)
        (by omega) (by omega) hend_new_le
        (by have : mwuEdgeStepSpace L_in L_w P_fp ≤ max (4 * L_w) (mwuEdgeStepSpace L_in L_w P_fp) :=
              le_max_right _ _
            omega)
        hz_ms
        (fun t ht => by rw [hone_ms t ht]; exact hv_one0 t ht)
        ((intVal_congr hone_ms).trans hone_eq0)
        (fun t ht => by rw [hrho_ms t ht]; exact hv_rho0 t ht)
        ((intVal_congr hrho_ms).trans hrho_eq0)
        hpStep hDiv hExp hMul hCopy hFill
    -- Combine the 4 statements + increment into one loop body run
    have hbody_step : ∃ st1 c_b,
        Runs w p ω
          ((.call 17 (bLsf + lsfIdxInit) [.reg 0, .reg 1, .reg 10, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 13] ;;
            .store (.bin .add (.reg 8) (.reg 16)) (.reg 13) ;;
            .call 18 bWeightsLoop [.reg 0, .reg 13, .reg 10, .reg 11, .reg 12, .reg 2, .reg 5, .reg 3, .reg 17] ;;
            .assign 13 (.reg 17)) ;;
           .assign 16 (.bin .add (.reg 16) (.const 1)))
          st .normal st1 c_b ∧
        (∀ r ≤ 12, st1.regs r = st.regs r) ∧
        st1.regs 13 = nextHeap ∧ st1.regs 16 = j + 1 ∧
        st1.mem = stWL.mem ∧
        c_b ≤ initC + G₀.m * (mwuEdgeStepCost L_in L_w P_fp + 80) + 185 := by
      suffices hs : ∃ o st1 c_b,
          Runs w p ω
            ((.call 17 (bLsf + lsfIdxInit) [.reg 0, .reg 1, .reg 10, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 13] ;;
              .store (.bin .add (.reg 8) (.reg 16)) (.reg 13) ;;
              .call 18 bWeightsLoop [.reg 0, .reg 13, .reg 10, .reg 11, .reg 12, .reg 2, .reg 5, .reg 3, .reg 17] ;;
              .assign 13 (.reg 17)) ;;
             .assign 16 (.bin .add (.reg 16) (.const 1)))
            st o st1 c_b ∧
          (o = .normal ∧ (∀ r ≤ 12, st1.regs r = st.regs r) ∧
            st1.regs 13 = nextHeap ∧ st1.regs 16 = j + 1 ∧ st1.mem = stWL.mem) ∧
          0 + c_b ≤ initC + G₀.m * (mwuEdgeStepCost L_in L_w P_fp + 80) + 185 by
        rcases hs with ⟨_, st1, c_b, hrun, ⟨rfl, h1, h2, h3, h4⟩, hc⟩
        exact ⟨st1, c_b, hrun, h1, h2, h3, h4, by omega⟩
      refine runs_seq_assoc_le ?_
      have hcall1 : Runs w p ω
          (.call 17 (bLsf + lsfIdxInit) [.reg 0, .reg 1, .reg 10, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 13])
          st .normal
          { mem := stInit.mem, regs := Function.update st.regs 17 nextHeap, pos := stInit.pos }
          (argsSize [.reg 0, .reg 1, .reg 10, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 13] + cInit + 1) := by
        rw [runs_call_iff]
        exact ⟨[g0Ptr, lenArr, wtArr, L_in, P_fp, k_nat, L_w, vCap, eCap, curHeap],
          bodyInit, oInit, stInit, cInit,
          by simp [evalArgs, Expr.eval, hr0, hr1, hr10, hr2, hr3, hr4, hr5, hr6, hr7, hr13],
          hbodyInit, hrunInit, rfl, rfl, rfl⟩
      refine runs_seq_of_runs' hcall1 ?_
      refine runs_seq_assoc_le ?_
      refine runs_seq_store_le (x := handlesOut + j) (v := curHeap)
        (by simp [Expr.eval, BinOp.eval, hr8, hr16, show handlesOut + j < 2 ^ w by omega])
        (by simp [Expr.eval, hr13]) ?_
      refine runs_seq_assoc_le ?_
      have hcall2 : Runs w p ω
          (.call 18 bWeightsLoop [.reg 0, .reg 13, .reg 10, .reg 11, .reg 12, .reg 2, .reg 5, .reg 3, .reg 17])
          { mem := memAfterStore, regs := Function.update st.regs 17 nextHeap, pos := stInit.pos }
          .normal
          { mem := stWL.mem, regs := Function.update (Function.update st.regs 17 nextHeap) 18 0, pos := stWL.pos }
          (argsSize [.reg 0, .reg 13, .reg 10, .reg 11, .reg 12, .reg 2, .reg 5, .reg 3, .reg 17] + cWL + 1) := by
        rw [runs_call_iff]
        exact ⟨[g0Ptr, curHeap, wtArr, onePtr, rhoPtr, L_in, L_w, P_fp, nextHeap],
          mwuWeightsLoopProc bEdgeStep, .returned 0, stWL, cWL,
          by simp [evalArgs, Expr.eval, hr0, hr13, hr10, hr11, hr12, hr2, hr5, hr3],
          hpWLoop, hrunWL, rfl, rfl, rfl⟩
      refine runs_seq_of_runs' hcall2 ?_
      refine runs_seq_assign_le (v := nextHeap) (by simp [Expr.eval]) ?_
      refine runs_assign_le (v := j + 1)
        (by simp [Expr.eval, BinOp.eval, hr16, show 1 < 2 ^ w by omega, show j + 1 < 2 ^ w by omega])
        ⟨rfl, fun r hr => by
          dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega)],
         by simp, by simp, rfl⟩ ?_
      dsimp only [argsSize, Expr.size]
      have hGm : G₀.m = G₀.E.card := rfl
      rw [hlsfC_eq] at hcInit
      rw [← hGm] at hcWL
      omega
    obtain ⟨st1, c_b, hrun_b, hr1_lo, hr1_13, hr1_16, hmem1, hcb⟩ := hbody_step
    -- Build updated sequences (v1, S1, x1, hs1) for j + 1
    let v1 : ℕ → ℕ → ℝ := fun i =>
      if i = j + 1 then memArrayReal stWL.mem wtArr G₀ h L_in P_fp else v i
    let S1 : ℕ → LSFState := fun i => if i = j then S_new else S₀ i
    let x1 : ℕ → LSFConcrete := fun i => if i = j then x_new else x₀ i
    let hs1 : ℕ → ℕ := fun i => if i = j then curHeap else hs i
    have hfr1 : ∀ z < wtEnd, (z < handlesOut ∨ handlesOut + k_nat ≤ z) →
        (z < wtArr ∨ wtArr + eCap0 * L_in ≤ z) → st1.mem z = mem0 z := fun z hzw hzh hzwt => by
      rw [hmem1, hfrWL z (by omega) hzwt, hmem_store_eq z (by rcases hzh with h | h <;> omega),
        hfr_init z (by omega)]
      exact hfr z hzw hzh hzwt
    have hwt1 : ∀ e ∈ G₀.E, Valid st1.mem (wtArr + e * L_in) h L_in ∧
        fixVal st1.mem (wtArr + e * L_in) h L_in P_fp = v1 (j + 1) e := fun e he => by
      rw [hmem1]; exact ⟨(hinvWL e he).1, by simp only [v1, ite_true, memArrayReal_eq he]⟩
    have hv1_mem_eq : v1 (j + 1) = memArrayReal st1.mem wtArr G₀ h L_in P_fp := by
      simp only [v1, ite_true, hmem1]
    have hv0_1 : ∀ e ∈ G₀.E, v1 0 e = 1 := fun e he => by
      dsimp only [v1]; rw [ite_eq_right (by omega)]; exact hv0 e he
    have hv_pos1 : ∀ i ≤ j + 1, ∀ e ∈ G₀.E, 0 < v1 i e := fun i hi e he => by
      dsimp only [v1]
      by_cases hij : i = j + 1
      · rw [ite_eq_left hij, memArrayReal_eq he]; exact (hinvWL e he).2.1
      · rw [ite_eq_right hij]; exact hv_pos i (by omega) e he
    have hinit1 : ∀ i < j + 1, ∃ T_raw C_reps W_T,
        ValidLSFParams (4 * max K_AN 1 + 5) (5 / 4)
          (defaultThreshNat K_AN G₀.n k_nat : ℝ) (defaultK_sigma K_AN : ℝ)
          G₀ ℓ₀ (v1 i) (k_nat : ℝ) T_raw (S1 i).r₀ C_reps (S1 i).π W_T ∧
        S1 i = initLSFWith G₀ ℓ₀ (v1 i) (k_nat : ℝ) T_raw (S1 i).r₀ C_reps (S1 i).π W_T
          (defaultThreshNat K_AN G₀.n k_nat : ℝ) := fun i hi => by
      have hv1_eq : v1 i = v i := by dsimp only [v1]; rw [ite_eq_right (by omega)]
      rw [hv1_eq]
      by_cases hij : i = j
      · subst hij
        simp only [S1, ite_true]
        exact ⟨T_raw, C_reps, W_T, hVparams', hS_eq'⟩
      · simp only [S1, ite_eq_right hij]
        exact hinit i (by omega)
    have hv_step1 : ∀ i < j + 1, ∀ e ∈ G₀.E,
        (1 - 1 / (4 * (k_nat : ℝ))) * v1 i e * Real.exp ((S1 i).wstr e / (lemma55RhoNat K_AN G₀.n k_nat : ℝ)) ≤
          v1 (i + 1) e ∧
        v1 (i + 1) e ≤
          (1 + 1 / (4 * (k_nat : ℝ))) * v1 i e * Real.exp ((S1 i).wstr e / (lemma55RhoNat K_AN G₀.n k_nat : ℝ)) := by
      intro i hi e he
      have hv_i : v1 i e = v i e := by dsimp only [v1]; rw [ite_eq_right (by omega)]
      rw [hv_i]
      by_cases hij : i = j
      · subst hij
        simp only [v1, S1, ite_true, memArrayReal_eq he]
        exact ⟨(hinvWL e he).2.2.1, (hinvWL e he).2.2.2⟩
      · have hne1 : i + 1 ≠ j + 1 := by omega
        simp only [v1, S1, ite_eq_right hne1, ite_eq_right hij]
        exact hv_step i (by omega) e he
    have hhnd1 : ∀ i < j + 1, st1.mem (handlesOut + i) = hs1 i ∧
        (LSFRep h).rep (hs1 i) (S1 i) (x1 i) st1.mem ∧
        ∀ a, (LSFRep h).foot (hs1 i) (x1 i) a → wtEnd ≤ a ∧ a < nextHeap := by
      intro i hi
      by_cases hij : i = j
      · subst i
        simp only [hs1, S1, x1, ite_true]
        refine ⟨?_, ?_, fun a ha => ⟨le_trans hwe (hfoot_new a ha).1, (hfoot_new a ha).2⟩⟩
        · rw [hmem1, hfrWL (handlesOut + j) (by omega) (Or.inl (by omega))]
          dsimp only [memAfterStore]; rw [Function.update_self]
        · exact ((lsfRep_local h curHeap S_new x_new memAfterStore st1.mem fun a ha => by
            have hf := hfoot_new a ha
            rw [hmem1, hfrWL a hf.2 (Or.inr (by omega))]).1 hrep_ms)
      · simp only [hs1, S1, x1, hij, ↓reduceIte]
        obtain ⟨hm_i, hrep_i, hfoot_i⟩ := hhnd i (by omega)
        refine ⟨?_, ?_, fun a ha => ⟨(hfoot_i a ha).1, lt_of_lt_of_le (hfoot_i a ha).2 hnext_ge⟩⟩
        · rw [hmem1, hfrWL (handlesOut + i) (by omega) (Or.inl (by omega)),
            hmem_store_eq _ (by omega), hfr_init _ (by omega)]
          exact hm_i
        · exact ((lsfRep_local h (hs i) (S₀ i) (x₀ i) st.mem st1.mem fun a ha => by
            have hf := hfoot_i a ha
            rw [hmem1, hfrWL a (lt_of_lt_of_le hf.2 hnext_ge) (Or.inr (by omega)),
              hmem_store_eq a (by omega), hfr_init a hf.2]).1 hrep_i)
    obtain ⟨st', c_r, endHeap, v', S₀', x₀', hs', hrun_r, h13', hwe', hend', hz', hfr',
      hv0', hv_pos', hinit', hv_step', hhnd', hcr⟩ :=
      ih (j + 1) (by omega) (by omega) st1 nextHeap v1 S1 x1 hs1
        ((hr1_lo 0 (by decide)).trans hr0) ((hr1_lo 1 (by decide)).trans hr1)
        ((hr1_lo 2 (by decide)).trans hr2) ((hr1_lo 3 (by decide)).trans hr3)
        ((hr1_lo 4 (by decide)).trans hr4) ((hr1_lo 5 (by decide)).trans hr5)
        ((hr1_lo 6 (by decide)).trans hr6) ((hr1_lo 7 (by decide)).trans hr7)
        ((hr1_lo 8 (by decide)).trans hr8) ((hr1_lo 10 (by decide)).trans hr10)
        ((hr1_lo 11 (by decide)).trans hr11) ((hr1_lo 12 (by decide)).trans hr12)
        hr1_13 hr1_16 (le_trans hwe hnext_ge) (by omega) (hmem1 ▸ hzWL)
        hfr1 hwt1 hv1_mem_eq hv0_1 hv_pos1 hinit1 hv_step1 hhnd1
    refine ⟨st', 3 + c_b + c_r + 1, endHeap, v', S₀', x₀', hs',
      runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st1, c_b, c_r,
        by simp [Expr.eval, BinOp.eval, hr16, hr4, hj_lt, show 1 < 2 ^ w by omega],
        by decide, hrun_b, hrun_r, by simp [Expr.size]⟩)),
      h13', hwe', hend', hz', hfr', hv0', hv_pos', hinit', hv_step', hhnd', ?_⟩
    have hmul : (rem + 1) * (initC + G₀.m * (mwuEdgeStepCost L_in L_w P_fp + 80) + 190) =
        rem * (initC + G₀.m * (mwuEdgeStepCost L_in L_w P_fp + 80) + 190) +
          (initC + G₀.m * (mwuEdgeStepCost L_in L_w P_fp + 80) + 190) := by ring
    rw [show k_nat - (j + 1) = rem by omega] at hcr
    rw [hrem, hmul]
    omega

end

end MinCostFlow.LSF.Program
