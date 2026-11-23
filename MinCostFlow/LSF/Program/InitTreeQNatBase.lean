module

public import MinCostFlow.LSF.Program.InitTreeWeights
public import MinCostFlow.LSF.Program.InitTreeCopy
public import MinCostFlow.LSF.Program.InitArena
public import WordRAM.Tactic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# InitTreeQNat, first part

The first part of `InitTreeQNat.lean`, split off to keep files short. It contains:
- Procedure and Contract
- Pure Arithmetic Helper
- Base Register Packing and Helpers
- Setup Stage (`r8..r16`, `S_v`, `S_v - 1`, `m0Limbs`)
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF

@[expose] public section

/-! ## Procedure and Contract -/

def initTreeQNatAssignsStmt : Stmt :=
  .assign 8 (.bin .add (.reg 5) (.const 6)) ;;
  .assign 9 (.bin .add (.reg 6) (.bin .mul (.reg 4) (.reg 8))) ;;
  .assign 10 (.bin .add (.reg 9) (.reg 4)) ;;
  .assign 11 (.bin .add (.reg 10) (.reg 5)) ;;
  .assign 12 (.bin .add (.reg 11) (.reg 5)) ;;
  .assign 13 (.bin .add (.reg 12) (.reg 5)) ;;
  .assign 14 (.bin .add (.reg 13) (.reg 5)) ;;
  .assign 15 (.bin .add (.reg 14) (.reg 5)) ;;
  .assign 16 (.bin .add (.reg 15) (.reg 8))

def initTreeQNatSetupStmt (b f_sw : ℕ) : Stmt :=
  .call 17 f_sw [.reg 0, .reg 4, .reg 2, .reg 3, .reg 10, .reg 14, .reg 5] ;;
  .call 17 (lsfBaseUtils b + idxUtilMemCopy) [.reg 11, .reg 10, .reg 5] ;;
  .call 17 (lsfBaseUtils b + idxUtilWordToLimbs) [.reg 13, .reg 5, .const 1] ;;
  .call 17 (lsfBaseUtils b + idxUtilSubFrom) [.reg 11, .reg 13, .reg 5] ;;
  .call 17 (lsfBaseUtils b + idxUtilWordToLimbs) [.reg 12, .reg 5, .reg 4] ;;
  .assign 18 (.reg 7)

def initTreeQNatLoopStmt (f_mq h : ℕ) : Stmt :=
  forRange 17 (.const 0) (.reg 4)
    (.assign 19 (.load (.bin .add (.reg 0) (.reg 17))) ;;
     .assign 20 (.bin .mul (.reg 19) (.reg 3)) ;;
     .assign 21 (.bin .add (.reg 2) (.reg 20)) ;;
     .assign 22 (.bin .add (.reg 1) (.reg 20)) ;;
     .assign 23 (.bin .add (.reg 6) (.bin .mul (.reg 17) (.reg 8))) ;;
     .assign 24 (.bin .add (.reg 9) (.reg 17)) ;;
     .call 18 f_mq
       [.reg 21, .reg 22, .reg 23, .reg 24, .reg 10, .reg 11, .reg 12, .reg 14,
        .reg 15, .reg 16, .reg 3, .reg 5, .reg 18, .const (2 ^ h)])

/-- Compute `S_v`, multiplicities `multPtr[0..m0)`, and `qNatPtr[0..m0)`, then clear the
temporary division heap `[lsstHeap, hp_end)` back to zero.
Args: `[eListPtr, lenArr, wtArr, L_in, m0, K_w, qNatPtr, lsstHeap]`. -/
def initTreeQNatProc (b h f_sw f_mq : ℕ) : Stmt :=
  initTreeQNatAssignsStmt ;;
  initTreeQNatSetupStmt b f_sw ;;
  initTreeQNatLoopStmt f_mq h ;;
  .call 19 (lsfBaseUtils b + idxUtilMemFill) [.reg 7, .bin .sub (.reg 18) (.reg 7), .const 0] ;;
  .ret (.const 0)

lemma initTreeQNatProc_noRand (b h f_sw f_mq : ℕ) : (initTreeQNatProc b h f_sw f_mq).NoRand := by
  simp [initTreeQNatProc, initTreeQNatAssignsStmt, initTreeQNatSetupStmt, initTreeQNatLoopStmt,
    forRange, forUp, Stmt.NoRand]

def initTreeQNatCost (m0 L_in K_w : ℕ) : ℕ :=
  m0 * (800 * (K_w + 6) ^ 2 + 2800 * (K_w + 6) + 16 * multQNatStepSpace K_w + 25 * L_in + 2300) +
    200 * K_w + 300

def initTreeQNatContract (w h : ℕ) (G₀ : MGraph) (v : ℕ → ℝ) : Contract where
  pre args mem :=
    ∃ (ℓ₀ : ℕ → ℝ) (eList : List ℕ)
      (eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap P_fp : ℕ),
      args = [eListPtr, lenArr, wtArr, L_in, m0, K_w, qNatPtr, lsstHeap] ∧
      1 ≤ h ∧ 3 * h + 2 ≤ w ∧
      1 ≤ L_in ∧ h ∣ P_fp ∧
      G₀.IsValid ∧ G₀.E.card = m0 ∧ 1 ≤ m0 ∧ 2 * m0 < 2 ^ w ∧
      K_w = WideWord.kWidthOf m0 L_in ∧
      eList.length = m0 ∧ eList.Nodup ∧ (∀ e, e ∈ eList ↔ e ∈ G₀.E) ∧
      ListAt mem eListPtr eList ∧
      eListPtr + m0 ≤ qNatPtr ∧
      (∀ e ∈ G₀.E, lenArr + e * L_in + L_in ≤ qNatPtr) ∧
      (∀ e ∈ G₀.E, wtArr + e * L_in + L_in ≤ qNatPtr) ∧
      qNatPtr + m0 * (K_w + 6) + m0 + 5 * K_w + 2 * (K_w + 6) ≤ lsstHeap ∧
      lsstHeap + m0 * multQNatStepSpace K_w < 2 ^ w ∧
      (∀ e ∈ G₀.E, Num.Valid mem (lenArr + e * L_in) h L_in ∧
        Num.fixVal mem (lenArr + e * L_in) h L_in P_fp = ℓ₀ e ∧ 0 < ℓ₀ e) ∧
      (∀ e ∈ G₀.E, Num.Valid mem (wtArr + e * L_in) h L_in ∧
        Num.fixVal mem (wtArr + e * L_in) h L_in P_fp = v e ∧ 0 < v e) ∧
      ZeroFrom mem lsstHeap
  post args mem ret mem' :=
    ∃ (eList : List ℕ) (eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap : ℕ),
      args = [eListPtr, lenArr, wtArr, L_in, m0, K_w, qNatPtr, lsstHeap] ∧
      ret = 0 ∧
      eList.length = m0 ∧ eList.Nodup ∧ (∀ e, e ∈ eList ↔ e ∈ G₀.E) ∧
      ListAt mem eListPtr eList ∧
      (∀ j < m0,
        let e := eList.getD j 0
        let ℓ_int := (Num.intVal mem (lenArr + e * L_in) h L_in).toNat
        mem' (qNatPtr + m0 * (K_w + 6) + j) = edgeMult G₀ v e ∧
        Num.Valid mem' (qNatPtr + j * (K_w + 6)) h (K_w + 6) ∧
        Num.unsignedVal mem' (qNatPtr + j * (K_w + 6)) h (K_w + 6) =
          (edgeMult G₀ v e * 2 ^ (h * (L_in + 4))) / ℓ_int) ∧
      ZeroFrom mem' lsstHeap ∧
      ∀ a < qNatPtr, mem' a = mem a
  cost args _ :=
    initTreeQNatCost (args.getD 4 0) (args.getD 3 0) (args.getD 5 0)

/-! ## Pure Arithmetic Helper -/

lemma qNat_pre_arith {G₀ : MGraph} {v ℓ₀ : ℕ → ℝ} {eList : List ℕ}
    {mem : ℕ → ℕ} {lenArr wtArr L_in m0 K_w P_fp h : ℕ}
    (hh1 : 1 ≤ h) (_hLin1 : 1 ≤ L_in)
    (hm_card : G₀.E.card = m0) (hm0 : 1 ≤ m0) (hKw_eq : K_w = WideWord.kWidthOf m0 L_in)
    (hEL_len : eList.length = m0) (hEL_nd : eList.Nodup) (hEL_mem : ∀ e, e ∈ eList ↔ e ∈ G₀.E)
    (hlen : ∀ e ∈ G₀.E, Num.Valid mem (lenArr + e * L_in) h L_in ∧
      Num.fixVal mem (lenArr + e * L_in) h L_in P_fp = ℓ₀ e ∧ 0 < ℓ₀ e)
    (hwt : ∀ e ∈ G₀.E, Num.Valid mem (wtArr + e * L_in) h L_in ∧
      Num.fixVal mem (wtArr + e * L_in) h L_in P_fp = v e ∧ 0 < v e) :
    let v_int := fun e => Num.unsignedVal mem (wtArr + e * L_in) h L_in
    let ℓ_int := fun e => Num.unsignedVal mem (lenArr + e * L_in) h L_in
    let S_v := ∑ j ∈ Finset.range m0, v_int (eList.getD j 0)
    1 ≤ S_v ∧ 2 * S_v < Num.capacity h K_w / 2 ∧
    (∀ j (hj : j < m0),
      let e := eList[j]'(by omega)
      ℓ_int e = (Num.intVal mem (lenArr + e * L_in) h L_in).toNat ∧
      1 ≤ v_int e ∧ 2 * v_int e < Num.capacity h L_in ∧
      1 ≤ ℓ_int e ∧ 2 * ℓ_int e < Num.capacity h L_in ∧
      2 * (m0 * v_int e + (S_v - 1)) < Num.capacity h K_w ∧
      (m0 * v_int e + S_v - 1) / S_v = edgeMult G₀ v e ∧
      1 ≤ edgeMult G₀ v e ∧ edgeMult G₀ v e ≤ m0 ∧
      4 * m0 + 2 < Num.capacity h (K_w + 6 - (L_in + 4)) ∧
      4 * (2 * m0) * 2 ^ (h * (L_in + 4)) < Num.capacity h (K_w + 6) / 2) := by
  intro v_int ℓ_int S_v
  have hv_int_pos : ∀ e ∈ G₀.E, 1 ≤ v_int e ∧ 2 * v_int e < Num.capacity h L_in := by
    intro e he
    obtain ⟨hv_val, hv_fx, hv_pos⟩ := hwt e he
    have hpow_pos : (0 : ℝ) < (2 ^ P_fp : ℝ) := by positivity
    have hint_pos : 0 < Num.intVal mem (wtArr + e * L_in) h L_in := by
      dsimp only [Num.fixVal] at hv_fx; rw [← hv_fx] at hv_pos
      have hmul : (0 : ℝ) < (Num.intVal mem (wtArr + e * L_in) h L_in : ℤ) := by
        have := mul_pos hv_pos hpow_pos
        rwa [div_mul_cancel₀ _ (ne_of_gt hpow_pos)] at this
      exact_mod_cast hmul
    obtain ⟨hu, h2⟩ := pos_intVal_toNat_eq hv_val hint_pos
    exact ⟨by dsimp only [v_int]; rw [hu]; omega, h2⟩
  have hℓ_spec : ∀ e ∈ G₀.E,
      ℓ_int e = (Num.intVal mem (lenArr + e * L_in) h L_in).toNat ∧
      1 ≤ ℓ_int e ∧ 2 * ℓ_int e < Num.capacity h L_in := by
    intro e he
    obtain ⟨hℓ_val, hℓ_fx, hℓ_pos⟩ := hlen e he
    have hpow_pos : (0 : ℝ) < (2 ^ P_fp : ℝ) := by positivity
    have hint_pos : 0 < Num.intVal mem (lenArr + e * L_in) h L_in := by
      dsimp only [Num.fixVal] at hℓ_fx; rw [← hℓ_fx] at hℓ_pos
      have hmul : (0 : ℝ) < (Num.intVal mem (lenArr + e * L_in) h L_in : ℤ) := by
        have := mul_pos hℓ_pos hpow_pos
        rwa [div_mul_cancel₀ _ (ne_of_gt hpow_pos)] at this
      exact_mod_cast hmul
    obtain ⟨hu, h2⟩ := pos_intVal_toNat_eq hℓ_val hint_pos
    exact ⟨hu, by dsimp only [ℓ_int]; rw [hu]; omega, h2⟩
  have hS_pos : 1 ≤ S_v := by
    have h0 : 0 ∈ Finset.range m0 := Finset.mem_range.mpr hm0
    have he0 : eList.getD 0 0 ∈ G₀.E := by
      rw [← hEL_mem, List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _
    exact le_trans (hv_int_pos _ he0).1
      (Finset.single_le_sum (f := fun j => v_int (eList.getD j 0)) (fun _ _ => Nat.zero_le _) h0)
  obtain ⟨hlt1, hpow_le, hcap_lt⟩ := cap_kWidth_bounds hm0 hh1 (L_in := L_in)
  rw [← hKw_eq] at hcap_lt
  have hS_lt : 2 * S_v < 2 * m0 * Num.capacity h L_in := by
    have hterm : ∀ j ∈ Finset.range m0, 2 * v_int (eList.getD j 0) < Num.capacity h L_in := by
      intro j hj; rw [Finset.mem_range] at hj
      have hej : eList.getD j 0 ∈ G₀.E := by
        rw [← hEL_mem, List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
      exact (hv_int_pos _ hej).2
    have hsum_lt := Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.mpr hm0⟩ hterm
    rw [← Finset.mul_sum, Finset.sum_const, Finset.card_range, smul_eq_mul] at hsum_lt
    calc 2 * S_v < m0 * Num.capacity h L_in := hsum_lt
      _ ≤ 2 * m0 * Num.capacity h L_in := by nlinarith
  have hS_half : 2 * S_v < Num.capacity h K_w / 2 :=
    calc 2 * S_v < 2 * m0 * Num.capacity h L_in := hS_lt
      _ ≤ 4 * m0 * Num.capacity h L_in := by gcongr; norm_num
      _ < Num.capacity h K_w / 2 := hcap_lt
  have hnorm_sum : S_v = ∑ e ∈ G₀.E, v_int e := by
    dsimp only [S_v]
    refine Finset.sum_bij (fun j _ => eList.getD j 0) ?_ ?_ ?_ ?_
    · intro j hj; rw [Finset.mem_range] at hj
      rw [← hEL_mem, List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    · intro j₁ hj₁ j₂ hj₂ heq; rw [Finset.mem_range] at hj₁ hj₂
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at heq
      exact (List.Nodup.getElem_inj hEL_nd).mp heq
    · intro e he; obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ((hEL_mem e).mpr he)
      exact ⟨j, Finset.mem_range.mpr (by omega), List.getD_eq_getElem _ _ hj⟩
    · intro _ _; rfl
  have hv_all_pos : ∀ e ∈ G₀.E, 0 < v e := fun e he => (hwt e he).2.2
  have hS_scale : ∃ c > 0, G₀.norm1 v = c * (S_v : ℝ) ∧ ∀ e ∈ G₀.E, v e = c * (v_int e : ℝ) := by
    have hv_e : ∀ e ∈ G₀.E, v e = ((1 : ℝ) / (2 ^ P_fp : ℝ)) * (v_int e : ℝ) := by
      intro e he
      obtain ⟨hv_val, hv_fx, _⟩ := hwt e he
      have hfix := hv_fx.symm; dsimp only [Num.fixVal] at hfix
      have hp2 : (0 : ℝ) < (2 ^ P_fp : ℝ) := by positivity
      have hpos_i : 0 < Num.intVal mem (wtArr + e * L_in) h L_in := by
        have : (0 : ℝ) < (Num.intVal mem (wtArr + e * L_in) h L_in : ℤ) := by
          have := mul_pos (hfix.symm ▸ hv_all_pos e he) hp2
          rwa [div_mul_cancel₀ _ (ne_of_gt hp2)] at this
        exact_mod_cast this
      obtain ⟨hu, _⟩ := pos_intVal_toNat_eq hv_val hpos_i
      have hint_cast : (Num.intVal mem (wtArr + e * L_in) h L_in : ℝ) = (v_int e : ℝ) := by
        change _ = ((Num.unsignedVal mem (wtArr + e * L_in) h L_in : ℕ) : ℝ)
        rw [hu, ← Int.cast_natCast, Int.toNat_of_nonneg (le_of_lt hpos_i)]
      rw [hfix, hint_cast, div_eq_mul_inv, mul_comm, one_div]
    refine ⟨(1 : ℝ) / (2 ^ P_fp : ℝ), by positivity, ?_, hv_e⟩
    have hnorm_eq : G₀.norm1 v = ∑ e ∈ G₀.E, v e :=
      Finset.sum_congr rfl fun e he => abs_of_pos (hv_all_pos e he)
    rw [hnorm_eq, hnorm_sum, Finset.sum_congr rfl hv_e, ← Finset.mul_sum]
    push_cast; rfl
  have hmult_bds := (sum_edgeMult_le hv_all_pos).1
  set A_tmp : InitArena := ⟨0, 0, 0, 1, m0, L_in, L_in, L_in, h⟩
  have hℓ_all_lt : ∀ e, 2 * (if e ∈ G₀.E then ℓ_int e else 0) < Num.capacity h L_in := by
    intro e; split_ifs with he
    · exact (hℓ_spec e he).2.2
    · simp only [mul_zero]; rw [Num.capacity_eq_two_pow]; exact Nat.two_pow_pos _
  obtain ⟨_, hq_cap⟩ := qNat_cap_bounds (A := A_tmp) hm0 hh1 hℓ_all_lt
  have hK_w_tmp : A_tmp.K_w = K_w := hKw_eq.symm
  dsimp only [InitArena.K_q] at hq_cap
  rw [hK_w_tmp] at hq_cap
  have hk_rem : 4 * m0 + 2 < Num.capacity h (K_w + 6 - (L_in + 4)) := by
    have hkle : Nat.log 2 (4 * m0 + 2) + 1 ≤ K_w + 6 - (L_in + 4) := by
      rw [hKw_eq]; dsimp only [WideWord.kWidthOf]; omega
    have hmono : Num.capacity h (Nat.log 2 (4 * m0 + 2) + 1) ≤ Num.capacity h (K_w + 6 - (L_in + 4)) := by
      rw [Num.capacity_eq_two_pow, Num.capacity_eq_two_pow]
      exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left h hkle)
    exact lt_of_lt_of_le (lt_of_lt_of_le hlt1 hpow_le) hmono
  refine ⟨hS_pos, hS_half, fun j hj => ?_⟩
  have hej : eList[j]'(by omega) ∈ G₀.E := (hEL_mem _).mp (List.getElem_mem _)
  obtain ⟨hℓ1, hℓ2, hℓ3⟩ := hℓ_spec _ hej
  obtain ⟨hv1, hv2⟩ := hv_int_pos _ hej
  obtain ⟨c, hc_pos, hnorm_c, hve_c⟩ := hS_scale
  have hceil_eq := ceil_div_eq_edgeMult hm0 hm_card hS_pos ⟨c, hc_pos, hnorm_c, hve_c _ hej⟩
  obtain ⟨hmb1, hmb2⟩ := hmult_bds _ hej
  have hnum_lt : 2 * (m0 * v_int (eList[j]'(by omega)) + (S_v - 1)) < Num.capacity h K_w := by
    have hmv : 2 * (m0 * v_int (eList[j]'(by omega))) < m0 * Num.capacity h L_in := by
      have : 2 * v_int (eList[j]'(by omega)) < Num.capacity h L_in := hv2; nlinarith
    have h4m : m0 * Num.capacity h L_in ≤ 4 * m0 * Num.capacity h L_in := by nlinarith
    omega
  exact ⟨hℓ1, hv1, hv2, hℓ2, hℓ3, hnum_lt, hceil_eq, hmb1, hm_card ▸ hmb2, hk_rem, hq_cap⟩

/-! ## Base Register Packing and Helpers -/

structure QNatRegs (eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap
    K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr : ℕ)
    (st : State) : Prop where
  r0 : st.regs 0 = eListPtr
  r1 : st.regs 1 = lenArr
  r2 : st.regs 2 = wtArr
  r3 : st.regs 3 = L_in
  r4 : st.regs 4 = m0
  r5 : st.regs 5 = K_w
  r6 : st.regs 6 = qNatPtr
  r7 : st.regs 7 = lsstHeap
  r8 : st.regs 8 = K_q
  r9 : st.regs 9 = multPtr
  r10 : st.regs 10 = svPtr
  r11 : st.regs 11 = svMinusOnePtr
  r12 : st.regs 12 = m0LimbsPtr
  r13 : st.regs 13 = oneLimbsPtr
  r14 : st.regs 14 = edgeLimbsPtr
  r15 : st.regs 15 = numerPtr
  r16 : st.regs 16 = lenQPtr

lemma qNatRegs_upd_hi {eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap
    K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr
    r v pos' : ℕ} {mem' : ℕ → ℕ} {st : State}
    (hb : QNatRegs eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap
      K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr st)
    (hr : 17 ≤ r) :
    QNatRegs eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap
      K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr
      { mem := mem', regs := Function.update st.regs r v, pos := pos' } :=
  ⟨by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r0,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r1,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r2,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r3,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r4,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r5,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r6,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r7,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r8,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r9,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r10,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r11,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r12,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r13,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r14,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r15,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r16⟩

private def QNatRegsPrefix (vals : List ℕ) (st : State) : Prop :=
  ∀ i (hi : i < vals.length), st.regs i = vals[i]'hi

private lemma qNatRegsPrefix_snoc {vals : List ℕ} {v : ℕ} {st : State}
    (h : QNatRegsPrefix vals st) :
    QNatRegsPrefix (vals ++ [v]) { st with regs := Function.update st.regs vals.length v } := by
  intro i hi
  rw [List.length_append, List.length_singleton] at hi
  dsimp only
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
  · rw [Function.update_of_ne (by omega), List.getElem_append_left hi']
    exact h i hi'
  · rw [Function.update_self, List.getElem_append_right le_rfl]
    simp

private lemma qNatRegs_of_prefix {e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 : ℕ}
    {st : State}
    (h : QNatRegsPrefix [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16] st) :
    QNatRegs e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 st :=
  ⟨h 0 (by simp), h 1 (by simp), h 2 (by simp), h 3 (by simp), h 4 (by simp),
   h 5 (by simp), h 6 (by simp), h 7 (by simp), h 8 (by simp), h 9 (by simp),
   h 10 (by simp), h 11 (by simp), h 12 (by simp), h 13 (by simp), h 14 (by simp),
   h 15 (by simp), h 16 (by simp)⟩

lemma valid_unsignedVal_congr {m₁ m₂ : ℕ → ℕ} {a₁ a₂ h L : ℕ}
    (hv : Num.Valid m₁ a₁ h L) (hm : ∀ i < L, m₂ (a₂ + i) = m₁ (a₁ + i)) :
    Num.Valid m₂ a₂ h L ∧ Num.unsignedVal m₂ a₂ h L = Num.unsignedVal m₁ a₁ h L := by
  refine ⟨fun i hi => by rw [hm i hi]; exact hv i hi, ?_⟩
  clear hv
  induction L generalizing a₁ a₂ with
  | zero => simp [Num.unsignedVal]
  | succ L ih =>
    rw [Num.unsignedVal, Num.unsignedVal]
    have h0 := hm 0 (Nat.zero_lt_succ _)
    rw [Nat.add_zero, Nat.add_zero] at h0
    rw [h0]
    have hih := ih (a₁ := a₁ + 1) (a₂ := a₂ + 1) fun i hi => by
      rw [show a₁ + 1 + i = a₁ + (i + 1) by omega, show a₂ + 1 + i = a₂ + (i + 1) by omega]
      exact hm (i + 1) (Nat.succ_lt_succ hi)
    rw [hih]

/-! ## Setup Stage (`r8..r16`, `S_v`, `S_v - 1`, `m0Limbs`) -/

lemma initTreeQNat_assigns {w eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap pos : ℕ}
    {p : Program} {mem0 : ℕ → ℕ}
    (harena_w : qNatPtr + m0 * (K_w + 6) + m0 + 5 * K_w + 2 * (K_w + 6) ≤ lsstHeap)
    (hlsst_w : lsstHeap < 2 ^ w) (hw6 : 6 < 2 ^ w) :
    let K_q := K_w + 6
    let multPtr := qNatPtr + m0 * K_q
    let svPtr := multPtr + m0
    let svMinusOnePtr := svPtr + K_w
    let m0LimbsPtr := svMinusOnePtr + K_w
    let oneLimbsPtr := m0LimbsPtr + K_w
    let edgeLimbsPtr := oneLimbsPtr + K_w
    let numerPtr := edgeLimbsPtr + K_w
    let lenQPtr := numerPtr + K_q
    Triple w p
      (fun st => st = startState [eListPtr, lenArr, wtArr, L_in, m0, K_w, qNatPtr, lsstHeap] mem0 pos)
      initTreeQNatAssignsStmt
      (normalPost fun st =>
        QNatRegs eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap
          K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr st ∧
        st.mem = mem0)
      fun _ => 50 := by
  intro K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr
  change qNatPtr + m0 * K_q + m0 + 5 * K_w + 2 * K_q ≤ lsstHeap at harena_w
  have hKq_w : K_q < 2 ^ w := by omega
  have hmKq_w : m0 * K_q < 2 ^ w := by omega
  have h9_w : multPtr < 2 ^ w := by omega
  have h10_w : svPtr < 2 ^ w := by omega
  have h11_w : svMinusOnePtr < 2 ^ w := by omega
  have h12_w : m0LimbsPtr < 2 ^ w := by omega
  have h13_w : oneLimbsPtr < 2 ^ w := by omega
  have h14_w : edgeLimbsPtr < 2 ^ w := by omega
  have h15_w : numerPtr < 2 ^ w := by omega
  have h16_w : lenQPtr < 2 ^ w := by omega
  let base := [eListPtr, lenArr, wtArr, L_in, m0, K_w, qNatPtr, lsstHeap]
  let l8 := base ++ [K_q]
  let l9 := l8 ++ [multPtr]
  let l10 := l9 ++ [svPtr]
  let l11 := l10 ++ [svMinusOnePtr]
  let l12 := l11 ++ [m0LimbsPtr]
  let l13 := l12 ++ [oneLimbsPtr]
  let l14 := l13 ++ [edgeLimbsPtr]
  let l15 := l14 ++ [numerPtr]
  let l16 := l15 ++ [lenQPtr]
  have addStep : ∀ (vals : List ℕ) (a b_r valA valB : ℕ) (ha : a < vals.length) (hb : b_r < vals.length)
      (_ : vals[a]'ha = valA) (_ : vals[b_r]'hb = valB) (_ : valA + valB < 2 ^ w),
      Triple w p (fun st => QNatRegsPrefix vals st ∧ st.mem = mem0)
        (.assign vals.length (.bin .add (.reg a) (.reg b_r)))
        (normalPost fun st => QNatRegsPrefix (vals ++ [valA + valB]) st ∧ st.mem = mem0) fun _ => 4 := by
    intro vals a b_r valA valB ha hb hA hB hsum
    exact Triple.assign
      (fun _ h => Expr.eval_add (Expr.eval_reg_of_eq (hA ▸ h.1 a ha))
        (Expr.eval_reg_of_eq (hB ▸ h.1 b_r hb)) hsum)
      fun _ h => ⟨qNatRegsPrefix_snoc h.1, h.2⟩
  have h0 : QNatRegsPrefix base (startState base mem0 pos) ∧ (startState base mem0 pos).mem = mem0 :=
    ⟨fun i hi => by dsimp only [startState]; exact List.getD_eq_getElem _ _ hi, rfl⟩
  have ha8 : Triple w p (fun st => QNatRegsPrefix base st ∧ st.mem = mem0)
      (.assign 8 (.bin .add (.reg 5) (.const 6)))
      (normalPost fun st => QNatRegsPrefix l8 st ∧ st.mem = mem0) fun _ => 4 := by
    exact Triple.assign
      (fun _ h => Expr.eval_add (Expr.eval_reg_of_eq (by simpa [base] using h.1 5 (by simp [base])))
        (Expr.eval_const hw6) hKq_w)
      fun _ h => ⟨qNatRegsPrefix_snoc h.1, h.2⟩
  have ha9 : Triple w p (fun st => QNatRegsPrefix l8 st ∧ st.mem = mem0)
      (.assign 9 (.bin .add (.reg 6) (.bin .mul (.reg 4) (.reg 8))))
      (normalPost fun st => QNatRegsPrefix l9 st ∧ st.mem = mem0) fun _ => 6 :=
    Triple.assign (P := fun st => QNatRegsPrefix l8 st ∧ st.mem = mem0) (val := fun _ => multPtr)
      (fun _ h => Expr.eval_add
        (Expr.eval_reg_of_eq (by simpa [l8, base] using h.1 6 (by simp [l8, base])))
        (Expr.eval_mul
          (Expr.eval_reg_of_eq (by simpa [l8, base] using h.1 4 (by simp [l8, base])))
          (Expr.eval_reg_of_eq (by simpa [l8, base] using h.1 8 (by simp [l8, base]))) hmKq_w) h9_w)
      fun _ h => ⟨qNatRegsPrefix_snoc h.1, h.2⟩
  have ha10 := addStep l9 9 4 multPtr m0 (by simp [l9, l8, base]) (by simp [l9, l8, base]) rfl rfl h10_w
  have ha11 := addStep l10 10 5 svPtr K_w (by simp [l10, l9, l8, base]) (by simp [l10, l9, l8, base]) rfl rfl h11_w
  have ha12 := addStep l11 11 5 svMinusOnePtr K_w (by simp [l11, l10, l9, l8, base]) (by simp [l11, l10, l9, l8, base]) rfl rfl h12_w
  have ha13 := addStep l12 12 5 m0LimbsPtr K_w (by simp [l12, l11, l10, l9, l8, base]) (by simp [l12, l11, l10, l9, l8, base]) rfl rfl h13_w
  have ha14 := addStep l13 13 5 oneLimbsPtr K_w (by simp [l13, l12, l11, l10, l9, l8, base]) (by simp [l13, l12, l11, l10, l9, l8, base]) rfl rfl h14_w
  have ha15 := addStep l14 14 5 edgeLimbsPtr K_w (by simp [l14, l13, l12, l11, l10, l9, l8, base]) (by simp [l14, l13, l12, l11, l10, l9, l8, base]) rfl rfl h15_w
  have ha16 := addStep l15 15 8 numerPtr K_q (by simp [l15, l14, l13, l12, l11, l10, l9, l8, base]) (by simp [l15, l14, l13, l12, l11, l10, l9, l8, base]) rfl rfl h16_w
  have hseq := Triple.seq_normal_const ha8 (Triple.seq_normal_const ha9 (Triple.seq_normal_const ha10
    (Triple.seq_normal_const ha11 (Triple.seq_normal_const ha12 (Triple.seq_normal_const ha13
      (Triple.seq_normal_const ha14 (Triple.seq_normal_const ha15 ha16)))))))
  refine Triple.conseq hseq (fun _ hst => hst ▸ h0) (fun o st h => ?_) (fun _ _ => by omega)
  cases o with
  | normal =>
    rcases h with ⟨hp16, hm⟩
    have hl : l16 = [eListPtr, lenArr, wtArr, L_in, m0, K_w, qNatPtr, lsstHeap,
        K_q, multPtr, svPtr, svMinusOnePtr, m0LimbsPtr, oneLimbsPtr, edgeLimbsPtr, numerPtr, lenQPtr] := by
      simp only [l16, l15, l14, l13, l12, l11, l10, l9, l8, base, List.cons_append, List.nil_append]
    exact ⟨qNatRegs_of_prefix (hl ▸ hp16), hm⟩
  | returned _ => exact False.elim h

lemma initTreeQNat_setup_calls {w b K_AN h f_sw : ℕ} {p : Program}
    (hp : p.HasAt (b + 2) (lsfSharedProcs b K_AN h))
    (hsw : MeetsContract w p f_sw (sumWeightsContract w h))
    {eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap : ℕ}
    {mem0 : ℕ → ℕ}
    (hw1 : 1 < 2 ^ w) (hh1 : 1 ≤ h) (hw3h : 3 * h + 2 ≤ w) (h16_w : 16 ≤ 2 ^ w)
    (hLin1 : 1 ≤ L_in) (hLK : L_in ≤ K_w) (hm0 : 1 ≤ m0)
    (heL_q : eListPtr + m0 ≤ qNatPtr)
    (hwt_q : ∀ j < m0, wtArr + mem0 (eListPtr + j) * L_in + L_in ≤ qNatPtr)
    (hwt_val : ∀ j < m0, Num.Valid mem0 (wtArr + mem0 (eListPtr + j) * L_in) h L_in)
    (hSv_pos : 1 ≤ ∑ j ∈ Finset.range m0, Num.unsignedVal mem0 (wtArr + mem0 (eListPtr + j) * L_in) h L_in)
    (hSv_half : 2 * (∑ j ∈ Finset.range m0, Num.unsignedVal mem0 (wtArr + mem0 (eListPtr + j) * L_in) h L_in) <
      Num.capacity h K_w / 2)
    (hm0_half : m0 < Num.capacity h K_w)
    (harena_w : qNatPtr + m0 * (K_w + 6) + m0 + 5 * K_w + 2 * (K_w + 6) ≤ lsstHeap)
    (hlsst_w : lsstHeap < 2 ^ w)
    (heL_w : eListPtr < 2 ^ w) (hwt_w : wtArr < 2 ^ w) :
    let K_q := K_w + 6
    let multPtr := qNatPtr + m0 * K_q
    let svPtr := multPtr + m0
    let svMinusOnePtr := svPtr + K_w
    let m0LimbsPtr := svMinusOnePtr + K_w
    let oneLimbsPtr := m0LimbsPtr + K_w
    let edgeLimbsPtr := oneLimbsPtr + K_w
    let numerPtr := edgeLimbsPtr + K_w
    let lenQPtr := numerPtr + K_q
    let S_v := ∑ j ∈ Finset.range m0, Num.unsignedVal mem0 (wtArr + mem0 (eListPtr + j) * L_in) h L_in
    Triple w p
      (fun st =>
        QNatRegs eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap
          K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr st ∧
        st.mem = mem0)
      (initTreeQNatSetupStmt b f_sw)
      (normalPost fun st =>
        QNatRegs eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap
          K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr st ∧
        st.regs 18 = lsstHeap ∧
        Num.Valid st.mem svPtr h K_w ∧ Num.unsignedVal st.mem svPtr h K_w = S_v ∧
        Num.Valid st.mem svMinusOnePtr h K_w ∧ Num.unsignedVal st.mem svMinusOnePtr h K_w = S_v - 1 ∧
        Num.Valid st.mem m0LimbsPtr h K_w ∧ Num.unsignedVal st.mem m0LimbsPtr h K_w = m0 ∧
        ∀ a, (a < svPtr ∨ edgeLimbsPtr + K_w ≤ a) → st.mem a = mem0 a)
      fun _ => m0 * (100 * K_w + 25 * L_in + 120) + 170 * K_w + 200 := by
  intro K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr S_v
  change qNatPtr + m0 * K_q + m0 + 5 * K_w + 2 * K_q ≤ lsstHeap at harena_w
  have hmc_copy := lsfMemCopy_meetsContract hw1 hp
  have hmc_w2l := lsfWordToLimbs_meetsContract (w := w) hp
  have hmc_sub := lsfSubFrom_meetsContract (w := w) hp
  have hw2 : 2 * h + 2 ≤ w := by omega
  have hbase_lt : Num.base h < 2 ^ w := by
    rw [Num.base]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hL_w : L_in < 2 ^ w := by omega
  have hm0_w : m0 < 2 ^ w := by omega
  have hKw_w : K_w < 2 ^ w := by omega
  have hsv_w : svPtr < 2 ^ w := by omega
  have hsv1_w : svMinusOnePtr < 2 ^ w := by omega
  have hm0L_w : m0LimbsPtr < 2 ^ w := by omega
  have h1L_w : oneLimbsPtr < 2 ^ w := by omega
  have hed_w : edgeLimbsPtr < 2 ^ w := by omega
  have hedEnd_w : edgeLimbsPtr + K_w < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := hw1
  have h2K_w : 2 * 1 < Num.capacity h K_w := by omega
  have c1 : Triple w p
      (fun st =>
        QNatRegs eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap
          K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr st ∧
        st.mem = mem0)
      (.call 17 f_sw [.reg 0, .reg 4, .reg 2, .reg 3, .reg 10, .reg 14, .reg 5])
      (normalPost fun st =>
        QNatRegs eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap
          K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr st ∧
        Num.Valid st.mem svPtr h K_w ∧ Num.unsignedVal st.mem svPtr h K_w = S_v ∧
        ∀ a, (a < svPtr ∨ edgeLimbsPtr + K_w ≤ a) → st.mem a = mem0 a)
      fun _ => m0 * (100 * K_w + 25 * L_in + 120) + (20 * K_w + 50) + 12 := by
    refine Triple.conseq
      (Triple.call (vs := fun _ => [eListPtr, m0, wtArr, L_in, svPtr, edgeLimbsPtr, K_w]) hsw
        (fun _ h => evalArgs_cons (Expr.eval_reg_of_eq h.1.r0)
          (evalArgs_cons (Expr.eval_reg_of_eq h.1.r4)
            (evalArgs_cons (Expr.eval_reg_of_eq h.1.r2)
              (evalArgs_cons (Expr.eval_reg_of_eq h.1.r3)
                (evalArgs_cons (Expr.eval_reg_of_eq h.1.r10)
                  (evalArgs_cons (Expr.eval_reg_of_eq h.1.r14)
                    (evalArgs_cons (Expr.eval_reg_of_eq h.1.r5) (evalArgs_nil _ _))))))))
        (fun _ _ v hv => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
        (fun st h => by
          rw [h.2]
          exact ⟨eListPtr, m0, wtArr, L_in, svPtr, edgeLimbsPtr, K_w, rfl, hh1, hw2, h16_w, hm0,
            hLin1, hLK, by omega, fun j hj => by have := hwt_q j hj; omega, hwt_val,
            by omega, hedEnd_w, by omega⟩)
        (fun st _ mem1 _ h ⟨_, _, _, _, _, _, _, heq, _, hval, hu, hfr⟩ => by
          simp only [List.cons.injEq, and_true] at heq
          rcases heq with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          refine ⟨qNatRegs_upd_hi h.1 (by omega), hval, ?_, fun a ha => ?_⟩
          · dsimp; rw [hu, h.2]
          · dsimp; rw [hfr a ha, h.2]))
      (fun _ h => h) (fun _ _ h => h) fun _ _ => by
        simp only [sumWeightsContract, argsSize, Expr.size, List.getD_eq_getElem?_getD,
          List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
        omega
  have c2 : Triple w p
      (fun st =>
        QNatRegs eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap
          K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr st ∧
        Num.Valid st.mem svPtr h K_w ∧ Num.unsignedVal st.mem svPtr h K_w = S_v ∧
        ∀ a, (a < svPtr ∨ edgeLimbsPtr + K_w ≤ a) → st.mem a = mem0 a)
      (.call 17 (lsfBaseUtils b + idxUtilMemCopy) [.reg 11, .reg 10, .reg 5])
      (normalPost fun st =>
        QNatRegs eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap
          K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr st ∧
        Num.Valid st.mem svPtr h K_w ∧ Num.unsignedVal st.mem svPtr h K_w = S_v ∧
        Num.Valid st.mem svMinusOnePtr h K_w ∧ Num.unsignedVal st.mem svMinusOnePtr h K_w = S_v ∧
        ∀ a, (a < svPtr ∨ edgeLimbsPtr + K_w ≤ a) → st.mem a = mem0 a)
      fun _ => 20 * K_w + 20 := by
    refine Triple.conseq
      (Triple.call (vs := fun _ => [svMinusOnePtr, svPtr, K_w]) hmc_copy
        (fun _ h => evalArgs_cons (Expr.eval_reg_of_eq h.1.r11)
          (evalArgs_cons (Expr.eval_reg_of_eq h.1.r10)
            (evalArgs_cons (Expr.eval_reg_of_eq h.1.r5) (evalArgs_nil _ _))))
        (fun _ _ v hv => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with rfl | rfl | rfl <;> assumption)
        (fun _ _ => ⟨svMinusOnePtr, svPtr, K_w, rfl, by omega, by omega, Or.inr (by omega)⟩)
        (fun st _ mem1 _ h ⟨_, _, _, heq, _, hcp, hfr⟩ => by
          simp only [List.cons.injEq, and_true] at heq; rcases heq with ⟨rfl, rfl, rfl⟩
          have hsv_pres := valid_unsignedVal_congr h.2.1 fun i hi => hfr (svPtr + i) (Or.inl (by omega))
          have hsv1_pres := valid_unsignedVal_congr h.2.1 fun i hi => hcp i hi
          refine ⟨qNatRegs_upd_hi h.1 (by omega), hsv_pres.1, hsv_pres.2.trans h.2.2.1,
            hsv1_pres.1, hsv1_pres.2.trans h.2.2.1, fun a ha => ?_⟩
          dsimp; rw [hfr a (by omega)]; exact h.2.2.2 a ha))
      (fun _ h => h) (fun _ _ h => h) fun _ _ => by
        simp only [memCopyContract, argsSize, Expr.size, List.getD_eq_getElem?_getD,
          List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
        omega
  have c3 : Triple w p
      (fun st =>
        QNatRegs eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap
          K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr st ∧
        Num.Valid st.mem svPtr h K_w ∧ Num.unsignedVal st.mem svPtr h K_w = S_v ∧
        Num.Valid st.mem svMinusOnePtr h K_w ∧ Num.unsignedVal st.mem svMinusOnePtr h K_w = S_v ∧
        ∀ a, (a < svPtr ∨ edgeLimbsPtr + K_w ≤ a) → st.mem a = mem0 a)
      (.call 17 (lsfBaseUtils b + idxUtilWordToLimbs) [.reg 13, .reg 5, .const 1])
      (normalPost fun st =>
        QNatRegs eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap
          K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr st ∧
        Num.Valid st.mem svPtr h K_w ∧ Num.unsignedVal st.mem svPtr h K_w = S_v ∧
        Num.Valid st.mem svMinusOnePtr h K_w ∧ Num.unsignedVal st.mem svMinusOnePtr h K_w = S_v ∧
        Num.Valid st.mem oneLimbsPtr h K_w ∧ Num.unsignedVal st.mem oneLimbsPtr h K_w = 1 ∧
        ∀ a, (a < svPtr ∨ edgeLimbsPtr + K_w ≤ a) → st.mem a = mem0 a)
      fun _ => 25 * K_w + 30 := by
    refine Triple.conseq
      (Triple.call (vs := fun _ => [oneLimbsPtr, K_w, 1]) hmc_w2l
        (fun _ hst => evalArgs_cons (Expr.eval_reg_of_eq hst.1.r13)
          (evalArgs_cons (Expr.eval_reg_of_eq hst.1.r5)
            (evalArgs_cons (Expr.eval_const h1_w) (evalArgs_nil _ _))))
        (fun _ _ v hv => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with rfl | rfl | rfl <;> assumption)
        (fun _ _ => ⟨oneLimbsPtr, K_w, 1, rfl, hh1, hbase_lt, by omega⟩)
        (fun st _ mem1 _ hst ⟨_, _, _, heq, _, hval1, hu1, hfr⟩ => by
          simp only [List.cons.injEq, and_true] at heq; rcases heq with ⟨rfl, rfl, rfl⟩
          have hsv_p := valid_unsignedVal_congr hst.2.1 fun i hi => hfr (svPtr + i) (Or.inl (by omega))
          have hsv1_p := valid_unsignedVal_congr hst.2.2.2.1 fun i hi => hfr (svMinusOnePtr + i) (Or.inl (by omega))
          have hu1' : Num.unsignedVal mem1 oneLimbsPtr h K_w = 1 := by
            rw [hu1, Nat.mod_eq_of_lt (by omega)]
          refine ⟨qNatRegs_upd_hi hst.1 (by omega), hsv_p.1, hsv_p.2.trans hst.2.2.1,
            hsv1_p.1, hsv1_p.2.trans hst.2.2.2.2.1, hval1, hu1', fun a ha => ?_⟩
          dsimp; rw [hfr a (by omega)]; exact hst.2.2.2.2.2 a ha))
      (fun _ hst => hst) (fun _ _ hst => hst) fun _ _ => by
        simp only [wordToLimbsContract, argsSize, Expr.size, List.getD_eq_getElem?_getD,
          List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
        omega
  have c4 : Triple w p
      (fun st =>
        QNatRegs eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap
          K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr st ∧
        Num.Valid st.mem svPtr h K_w ∧ Num.unsignedVal st.mem svPtr h K_w = S_v ∧
        Num.Valid st.mem svMinusOnePtr h K_w ∧ Num.unsignedVal st.mem svMinusOnePtr h K_w = S_v ∧
        Num.Valid st.mem oneLimbsPtr h K_w ∧ Num.unsignedVal st.mem oneLimbsPtr h K_w = 1 ∧
        ∀ a, (a < svPtr ∨ edgeLimbsPtr + K_w ≤ a) → st.mem a = mem0 a)
      (.call 17 (lsfBaseUtils b + idxUtilSubFrom) [.reg 11, .reg 13, .reg 5])
      (normalPost fun st =>
        QNatRegs eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap
          K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr st ∧
        Num.Valid st.mem svPtr h K_w ∧ Num.unsignedVal st.mem svPtr h K_w = S_v ∧
        Num.Valid st.mem svMinusOnePtr h K_w ∧ Num.unsignedVal st.mem svMinusOnePtr h K_w = S_v - 1 ∧
        ∀ a, (a < svPtr ∨ edgeLimbsPtr + K_w ≤ a) → st.mem a = mem0 a)
      fun _ => 65 * K_w + 30 := by
    refine Triple.conseq
      (Triple.call (vs := fun _ => [svMinusOnePtr, oneLimbsPtr, K_w]) hmc_sub
        (fun _ hst => evalArgs_cons (Expr.eval_reg_of_eq hst.1.r11)
          (evalArgs_cons (Expr.eval_reg_of_eq hst.1.r13)
            (evalArgs_cons (Expr.eval_reg_of_eq hst.1.r5) (evalArgs_nil _ _))))
        (fun _ _ v hv => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with rfl | rfl | rfl <;> assumption)
        (fun _ hst => ⟨svMinusOnePtr, oneLimbsPtr, K_w, rfl, hh1, hw2, by omega, by omega,
          Or.inl (by omega), hst.2.2.2.1, hst.2.2.2.2.2.1⟩)
        (fun st _ mem1 _ hst ⟨_, _, _, heq, _, hval_sub, hint_sub, hfr⟩ => by
          simp only [List.cons.injEq, and_true] at heq; rcases heq with ⟨rfl, rfl, rfl⟩
          have hsv_p := valid_unsignedVal_congr hst.2.1 fun i hi => hfr (svPtr + i) (Or.inl (by omega))
          have hi_sv : Num.intVal st.mem svMinusOnePtr h K_w = (S_v : ℤ) :=
            (intVal_eq_of_unsignedVal_lt (by rw [hst.2.2.2.2.1]; omega)).trans
              (congrArg Nat.cast hst.2.2.2.2.1)
          have hi_1 : Num.intVal st.mem oneLimbsPtr h K_w = (1 : ℤ) :=
            (intVal_eq_of_unsignedVal_lt (by rw [hst.2.2.2.2.2.2.1]; omega)).trans
              (congrArg Nat.cast hst.2.2.2.2.2.2.1)
          have hi_eq : Num.intVal mem1 svMinusOnePtr h K_w = ((S_v - 1 : ℕ) : ℤ) := by
            rw [hint_sub, hi_sv, hi_1]
            have hcast : (S_v : ℤ) - 1 = ((S_v - 1 : ℕ) : ℤ) := by omega
            rw [hcast]
            exact wrap_of_nat_lt (by omega)
          have hu_sub : Num.unsignedVal mem1 svMinusOnePtr h K_w = S_v - 1 :=
            nat_eq_unsignedVal_of_intVal hval_sub hi_eq
          refine ⟨qNatRegs_upd_hi hst.1 (by omega), hsv_p.1, hsv_p.2.trans hst.2.2.1,
            hval_sub, hu_sub, fun a ha => ?_⟩
          dsimp; rw [hfr a (by omega)]; exact hst.2.2.2.2.2.2.2 a ha))
      (fun _ hst => hst) (fun _ _ hst => hst) fun _ _ => by
        simp only [subFromContract, argsSize, Expr.size, List.getD_eq_getElem?_getD,
          List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
        omega
  have c5 : Triple w p
      (fun st =>
        QNatRegs eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap
          K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr st ∧
        Num.Valid st.mem svPtr h K_w ∧ Num.unsignedVal st.mem svPtr h K_w = S_v ∧
        Num.Valid st.mem svMinusOnePtr h K_w ∧ Num.unsignedVal st.mem svMinusOnePtr h K_w = S_v - 1 ∧
        ∀ a, (a < svPtr ∨ edgeLimbsPtr + K_w ≤ a) → st.mem a = mem0 a)
      (.call 17 (lsfBaseUtils b + idxUtilWordToLimbs) [.reg 12, .reg 5, .reg 4] ;;
       .assign 18 (.reg 7))
      (normalPost fun st =>
        QNatRegs eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap
          K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr st ∧
        st.regs 18 = lsstHeap ∧
        Num.Valid st.mem svPtr h K_w ∧ Num.unsignedVal st.mem svPtr h K_w = S_v ∧
        Num.Valid st.mem svMinusOnePtr h K_w ∧ Num.unsignedVal st.mem svMinusOnePtr h K_w = S_v - 1 ∧
        Num.Valid st.mem m0LimbsPtr h K_w ∧ Num.unsignedVal st.mem m0LimbsPtr h K_w = m0 ∧
        ∀ a, (a < svPtr ∨ edgeLimbsPtr + K_w ≤ a) → st.mem a = mem0 a)
      fun _ => 25 * K_w + 35 := by
    have s5a : Triple w p
        (fun st =>
          QNatRegs eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap
            K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr st ∧
          Num.Valid st.mem svPtr h K_w ∧ Num.unsignedVal st.mem svPtr h K_w = S_v ∧
          Num.Valid st.mem svMinusOnePtr h K_w ∧ Num.unsignedVal st.mem svMinusOnePtr h K_w = S_v - 1 ∧
          ∀ a, (a < svPtr ∨ edgeLimbsPtr + K_w ≤ a) → st.mem a = mem0 a)
        (.call 17 (lsfBaseUtils b + idxUtilWordToLimbs) [.reg 12, .reg 5, .reg 4])
        (normalPost fun st =>
          QNatRegs eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap
            K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr st ∧
          Num.Valid st.mem svPtr h K_w ∧ Num.unsignedVal st.mem svPtr h K_w = S_v ∧
          Num.Valid st.mem svMinusOnePtr h K_w ∧ Num.unsignedVal st.mem svMinusOnePtr h K_w = S_v - 1 ∧
          Num.Valid st.mem m0LimbsPtr h K_w ∧ Num.unsignedVal st.mem m0LimbsPtr h K_w = m0 ∧
          ∀ a, (a < svPtr ∨ edgeLimbsPtr + K_w ≤ a) → st.mem a = mem0 a)
        fun _ => 25 * K_w + 30 :=
      Triple.conseq
        (Triple.call (vs := fun _ => [m0LimbsPtr, K_w, m0]) hmc_w2l
          (fun _ hst => evalArgs_cons (Expr.eval_reg_of_eq hst.1.r12)
            (evalArgs_cons (Expr.eval_reg_of_eq hst.1.r5)
              (evalArgs_cons (Expr.eval_reg_of_eq hst.1.r4) (evalArgs_nil _ _))))
          (fun _ _ v hv => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with rfl | rfl | rfl <;> assumption)
          (fun _ _ => ⟨m0LimbsPtr, K_w, m0, rfl, hh1, hbase_lt, by omega⟩)
          (fun st _ mem1 _ hst ⟨_, _, _, heq, _, hvalm, hum, hfr⟩ => by
            simp only [List.cons.injEq, and_true] at heq; rcases heq with ⟨rfl, rfl, rfl⟩
            have hsv_p := valid_unsignedVal_congr hst.2.1 fun i hi => hfr (svPtr + i) (Or.inl (by omega))
            have hsv1_p := valid_unsignedVal_congr hst.2.2.2.1 fun i hi => hfr (svMinusOnePtr + i) (Or.inl (by omega))
            have hum' : Num.unsignedVal mem1 m0LimbsPtr h K_w = m0 := by
              rw [hum, Nat.mod_eq_of_lt hm0_half]
            refine ⟨qNatRegs_upd_hi hst.1 (by omega), hsv_p.1, hsv_p.2.trans hst.2.2.1,
              hsv1_p.1, hsv1_p.2.trans hst.2.2.2.2.1, hvalm, hum', fun a ha => ?_⟩
            dsimp; rw [hfr a (by omega)]; exact hst.2.2.2.2.2 a ha))
        (fun _ hst => hst) (fun _ _ hst => hst) fun _ _ => by
          simp only [wordToLimbsContract, argsSize, Expr.size, List.getD_eq_getElem?_getD,
            List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
          omega
    have s5b : Triple w p
        (fun st =>
          QNatRegs eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap
            K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr st ∧
          Num.Valid st.mem svPtr h K_w ∧ Num.unsignedVal st.mem svPtr h K_w = S_v ∧
          Num.Valid st.mem svMinusOnePtr h K_w ∧ Num.unsignedVal st.mem svMinusOnePtr h K_w = S_v - 1 ∧
          Num.Valid st.mem m0LimbsPtr h K_w ∧ Num.unsignedVal st.mem m0LimbsPtr h K_w = m0 ∧
          ∀ a, (a < svPtr ∨ edgeLimbsPtr + K_w ≤ a) → st.mem a = mem0 a)
        (.assign 18 (.reg 7))
        (normalPost fun st =>
          QNatRegs eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap
            K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr st ∧
          st.regs 18 = lsstHeap ∧
          Num.Valid st.mem svPtr h K_w ∧ Num.unsignedVal st.mem svPtr h K_w = S_v ∧
          Num.Valid st.mem svMinusOnePtr h K_w ∧ Num.unsignedVal st.mem svMinusOnePtr h K_w = S_v - 1 ∧
          Num.Valid st.mem m0LimbsPtr h K_w ∧ Num.unsignedVal st.mem m0LimbsPtr h K_w = m0 ∧
          ∀ a, (a < svPtr ∨ edgeLimbsPtr + K_w ≤ a) → st.mem a = mem0 a) fun _ => 2 :=
      Triple.assign (fun _ hst => Expr.eval_reg_of_eq hst.1.r7) fun _ hst =>
        ⟨qNatRegs_upd_hi hst.1 (by omega), by dsimp; rw [Function.update_self], hst.2⟩
    exact (Triple.seq_normal_const s5a s5b).mono_cost fun _ _ => by omega
  exact (Triple.seq_normal_const c1 (Triple.seq_normal_const c2 (Triple.seq_normal_const c3
    (Triple.seq_normal_const c4 c5)))).mono_cost fun _ _ => by omega


end

end MinCostFlow.LSF.Program
