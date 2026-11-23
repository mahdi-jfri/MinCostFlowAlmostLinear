module

public import MinCostFlow.Machine.WideWord.LSSTWeightsSub
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Per-edge fixed-point weight computation for Theorem 2.2

This module verifies `weightStepProc`, which computes the copy multiplicity
`mult(e) = ⌈|E_nl| * v(e) / ∑ v⌉₊` and integer weight `w_orig(e) = ⌊2 * |V_act| * ℓ(e) / ℓ_min⌋₊`
for a single non-loop edge `e`.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM MinCostFlow

/-! ### Per-edge weight step -/

private theorem weightStep_phase1_le (K : ℕ) :
    5 + 7 + (6 + (30 * K + 42)) + (6 + (2 * K * (38 * (2 * K) + 35) + 120 * K + 99)) + 7 +
      (6 + (38 * (2 * K) + 15)) +
      (6 + (2 * K * (300 * (2 * K) + 644) + 180 * (2 * K) + 400)) + 5 +
      (4 + (25 * K + 6)) + 4 ≤
      1400 * K * K + 2100 * K + 1000 := by
  nlinarith

private theorem weightStep_phase2_le (K : ℕ) :
    7 + (6 + (30 * K + 42)) + (6 + (2 * K * (38 * (2 * K) + 35) + 120 * K + 99)) + 7 +
      (6 + (2 * K * (300 * (2 * K) + 644) + 180 * (2 * K) + 400)) + 5 +
      (5 + (25 * K + 15)) + 2 ≤
      1400 * K * K + 2100 * K + 800 := by
  nlinarith

private structure WSRegs (s : State) (e lenPtr wtPtr L K nlCnt_K twoV_K S_2K S_m1_2K lmin_2K
    outMultAddr outWAddr : ℕ) : Prop where
  r0 : s.regs 0 = e
  r1 : s.regs 1 = lenPtr
  r2 : s.regs 2 = wtPtr
  r3 : s.regs 3 = L
  r4 : s.regs 4 = K
  r5 : s.regs 5 = nlCnt_K
  r6 : s.regs 6 = twoV_K
  r7 : s.regs 7 = S_2K
  r8 : s.regs 8 = S_m1_2K
  r9 : s.regs 9 = lmin_2K
  r10 : s.regs 10 = outMultAddr
  r11 : s.regs 11 = outWAddr
  r13 : s.regs 13 = 2 * K

private lemma wsRegs_upd {s st' : State} {e lenPtr wtPtr L K nlCnt_K twoV_K S_2K S_m1_2K lmin_2K
    outMultAddr outWAddr k v : ℕ}
    (h : WSRegs s e lenPtr wtPtr L K nlCnt_K twoV_K S_2K S_m1_2K lmin_2K outMultAddr outWAddr)
    (hreg : st'.regs = Function.update s.regs k v) (hk : 14 ≤ k) :
    WSRegs st' e lenPtr wtPtr L K nlCnt_K twoV_K S_2K S_m1_2K lmin_2K outMultAddr outWAddr :=
  ⟨by rw [hreg, Function.update_of_ne (by omega)]; exact h.r0,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r1,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r2,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r3,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r4,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r5,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r6,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r7,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r8,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r9,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r10,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r11,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r13⟩

private lemma wsRegs_sameRegs {s st' : State} {e lenPtr wtPtr L K nlCnt_K twoV_K S_2K S_m1_2K lmin_2K
    outMultAddr outWAddr : ℕ}
    (h : WSRegs s e lenPtr wtPtr L K nlCnt_K twoV_K S_2K S_m1_2K lmin_2K outMultAddr outWAddr)
    (hreg : st'.regs = s.regs) :
    WSRegs st' e lenPtr wtPtr L K nlCnt_K twoV_K S_2K S_m1_2K lmin_2K outMultAddr outWAddr :=
  ⟨by rw [hreg]; exact h.r0, by rw [hreg]; exact h.r1, by rw [hreg]; exact h.r2,
   by rw [hreg]; exact h.r3, by rw [hreg]; exact h.r4, by rw [hreg]; exact h.r5,
   by rw [hreg]; exact h.r6, by rw [hreg]; exact h.r7, by rw [hreg]; exact h.r8,
   by rw [hreg]; exact h.r9, by rw [hreg]; exact h.r10, by rw [hreg]; exact h.r11,
   by rw [hreg]; exact h.r13⟩

def weightStepContract (w h : ℕ) : Contract where
  pre args mem := ∃ (e lenPtr wtPtr L K nlCnt_K twoV_K S_2K S_m1_2K lmin_2K
      outMultAddr outWAddr heap nlCnt Vcnt S_val lmin_val : ℕ),
    args = [e, lenPtr, wtPtr, L, K, nlCnt_K, twoV_K, S_2K, S_m1_2K, lmin_2K,
      outMultAddr, outWAddr, heap] ∧
    0 < h ∧ 3 * h + 2 ≤ w ∧ 1 ≤ L ∧ L ≤ K ∧ 1 ≤ nlCnt ∧ nlCnt < 2 ^ w ∧ 2 ≤ Vcnt ∧
    Num.Valid mem (lenPtr + e * L) h L ∧ 0 < Num.intVal mem (lenPtr + e * L) h L ∧
    Num.Valid mem (wtPtr + e * L) h L ∧ 0 < Num.intVal mem (wtPtr + e * L) h L ∧
    Num.Valid mem nlCnt_K h K ∧ Num.intVal mem nlCnt_K h K = (nlCnt : ℤ) ∧
    Num.Valid mem twoV_K h K ∧ Num.intVal mem twoV_K h K = ((2 * Vcnt : ℕ) : ℤ) ∧
    Num.Valid mem S_2K h (2 * K) ∧ Num.intVal mem S_2K h (2 * K) = (S_val : ℤ) ∧ 1 ≤ S_val ∧
    Num.Valid mem S_m1_2K h (2 * K) ∧ Num.intVal mem S_m1_2K h (2 * K) = ((S_val - 1 : ℕ) : ℤ) ∧
    Num.Valid mem lmin_2K h (2 * K) ∧ Num.intVal mem lmin_2K h (2 * K) = (lmin_val : ℤ) ∧ 1 ≤ lmin_val ∧
    Num.unsignedVal mem (wtPtr + e * L) h L ≤ S_val ∧
    lmin_val ≤ Num.unsignedVal mem (lenPtr + e * L) h L ∧
    2 * nlCnt < Num.capacity h K ∧
    2 * (nlCnt * Num.unsignedVal mem (wtPtr + e * L) h L + (S_val - 1)) < Num.capacity h (2 * K) ∧
    2 * ((2 * Vcnt * Num.unsignedVal mem (lenPtr + e * L) h L) / lmin_val) < Num.capacity h K ∧
    lenPtr + e * L + L ≤ heap ∧ wtPtr + e * L + L ≤ heap ∧
    nlCnt_K + K ≤ heap ∧ twoV_K + K ≤ heap ∧
    S_2K + 2 * K ≤ heap ∧ S_m1_2K + 2 * K ≤ heap ∧ lmin_2K + 2 * K ≤ heap ∧
    outMultAddr < heap ∧ outWAddr + K ≤ heap ∧
    (outMultAddr < outWAddr ∨ outWAddr + K ≤ outMultAddr) ∧
    (outMultAddr < lenPtr + e * L ∨ lenPtr + e * L + L ≤ outMultAddr) ∧
    (outMultAddr < twoV_K ∨ twoV_K + K ≤ outMultAddr) ∧
    (outMultAddr < lmin_2K ∨ lmin_2K + 2 * K ≤ outMultAddr) ∧
    ZeroFrom mem heap ∧ heap + weightStepSpace K < 2 ^ w
  post args mem v mem' := ∃ (e lenPtr wtPtr L K nlCnt_K twoV_K S_2K S_m1_2K lmin_2K
      outMultAddr outWAddr heap nlCnt Vcnt S_val lmin_val : ℕ),
    args = [e, lenPtr, wtPtr, L, K, nlCnt_K, twoV_K, S_2K, S_m1_2K, lmin_2K,
      outMultAddr, outWAddr, heap] ∧
    Num.intVal mem nlCnt_K h K = (nlCnt : ℤ) ∧
    Num.intVal mem twoV_K h K = ((2 * Vcnt : ℕ) : ℤ) ∧
    Num.intVal mem S_2K h (2 * K) = (S_val : ℤ) ∧
    Num.intVal mem lmin_2K h (2 * K) = (lmin_val : ℤ) ∧
    v = heap + weightStepSpace K ∧
    ZeroFrom mem' v ∧
    (∀ a < heap, a ≠ outMultAddr → (a < outWAddr ∨ outWAddr + K ≤ a) → mem' a = mem a) ∧
    mem' outMultAddr =
      (nlCnt * Num.unsignedVal mem (wtPtr + e * L) h L + S_val - 1) / S_val ∧
    LimbsAt mem' outWAddr K h
      ((2 * Vcnt * Num.unsignedVal mem (lenPtr + e * L) h L) / lmin_val)
  cost args _ := weightStepCost (args.getD 4 0)

private theorem weightStep_tail_runs {w copyIdx seIdx mulIdx divIdx h : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {mem : ℕ → ℕ}
    {e lenPtr wtPtr L K nlCnt_K twoV_K S_2K S_m1_2K lmin_2K outMultAddr outWAddr heap
      nlCnt Vcnt S_val lmin_val : ℕ}
    (hcopy_mc : MeetsContract w p copyIdx (copyLimbsContract w))
    (hse_mc : MeetsContract w p seIdx (Num.signExtendContract w h))
    (hml_mc : MeetsContract w p mulIdx (Num.multiplyContract w h))
    (hdv_mc : MeetsContract w p divIdx (Num.integerDivideContract w h))
    (hh : 0 < h) (hw : 3 * h + 2 ≤ w) (hL1 : 1 ≤ L) (hLK : L ≤ K) (hV2 : 2 ≤ Vcnt)
    (hvlen : Num.Valid mem (lenPtr + e * L) h L) (hplen : 0 < Num.intVal mem (lenPtr + e * L) h L)
    (hin : Num.intVal mem nlCnt_K h K = (nlCnt : ℤ))
    (hv2v : Num.Valid mem twoV_K h K) (hi2v : Num.intVal mem twoV_K h K = ((2 * Vcnt : ℕ) : ℤ))
    (hiS : Num.intVal mem S_2K h (2 * K) = (S_val : ℤ))
    (hvlm : Num.Valid mem lmin_2K h (2 * K))
    (hilm : Num.intVal mem lmin_2K h (2 * K) = (lmin_val : ℤ)) (hlm1 : 1 ≤ lmin_val)
    (hlm_le : lmin_val ≤ Num.unsignedVal mem (lenPtr + e * L) h L)
    (hw_cap : 2 * ((2 * Vcnt * Num.unsignedVal mem (lenPtr + e * L) h L) / lmin_val) < Num.capacity h K)
    (hlen_h : lenPtr + e * L + L ≤ heap) (h2V_h : twoV_K + K ≤ heap) (hlm_h : lmin_2K + 2 * K ≤ heap)
    (hom_h : outMultAddr < heap) (how_h : outWAddr + K ≤ heap)
    (homw_disj : outMultAddr < outWAddr ∨ outWAddr + K ≤ outMultAddr)
    (homl_disj : outMultAddr < lenPtr + e * L ∨ lenPtr + e * L + L ≤ outMultAddr)
    (hom2V_disj : outMultAddr < twoV_K ∨ twoV_K + K ≤ outMultAddr)
    (homlm_disj : outMultAddr < lmin_2K ∨ lmin_2K + 2 * K ≤ outMultAddr)
    (hbound : heap + weightStepSpace K < 2 ^ w)
    (hws : WSRegs st e lenPtr wtPtr L K nlCnt_K twoV_K S_2K S_m1_2K lmin_2K outMultAddr outWAddr)
    (hr15 : st.regs 15 = heap + 9 * K + Num.integerDivideSpace (2 * K))
    (hz : ZeroFrom st.mem (heap + 9 * K + Num.integerDivideSpace (2 * K)))
    (hpres : ∀ a < heap, a ≠ outMultAddr → st.mem a = mem a)
    (hmult_mem : st.mem outMultAddr =
      (nlCnt * Num.unsignedVal mem (wtPtr + e * L) h L + S_val - 1) / S_val) :
    ∃ o st'' c, Runs w p ω
      (.assign 14 (.bin .add (.reg 1) (.bin .mul (.reg 0) (.reg 3))) ;;
       .call 16 seIdx [.reg 14, .reg 3, .reg 4, .reg 15] ;;
       .call 17 mulIdx [.reg 6, .reg 15, .reg 4, .reg 16] ;;
       .assign 18 (.bin .add (.reg 16) (.bin .mul (.const 4) (.reg 4))) ;;
       .call 15 divIdx [.reg 18, .reg 9, .reg 13, .reg 17] ;;
       .assign 17 (.bin .sub (.reg 15) (.reg 13)) ;;
       .call 16 copyIdx [.reg 17, .reg 4, .reg 11] ;;
       .ret (.reg 15)) st o st'' c ∧
      (weightStepContract w h).post
        [e, lenPtr, wtPtr, L, K, nlCnt_K, twoV_K, S_2K, S_m1_2K, lmin_2K,
          outMultAddr, outWAddr, heap] mem o.value st''.mem ∧
      c ≤ 1400 * K * K + 2100 * K + 800 := by
  have hbh : Num.base h < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hw1 : 1 < 2 ^ w := lt_of_le_of_lt
    (by simpa [Num.base] using Nat.one_le_two_pow (n := h)) hbh
  have h4_w : 4 < 2 ^ w := lt_of_lt_of_le (by norm_num : 4 < 2 ^ 5)
    (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hl_nat := intVal_eq_nat_of_pos hvlen hplen
  have hdiv_ge : 2 ≤ Num.integerDivideSpace (2 * K) := by
    unfold Num.integerDivideSpace Num.unsignedDivideSpace; omega
  have hlt_K2 : Num.capacity h K < Num.capacity h (2 * K) := by
    simp only [Num.capacity, Num.base, ← pow_mul]
    exact Nat.pow_lt_pow_right (by norm_num) (by nlinarith)
  have hK1 : 1 ≤ K := by omega
  have hK_w : K < 2 ^ w := by unfold weightStepSpace at hbound; omega
  have h2K_w : 2 * K < 2 ^ w := by unfold weightStepSpace at hbound; omega
  have hL_w : L < 2 ^ w := by omega
  have hlen_sub_w : lenPtr + e * L < 2 ^ w := by omega
  have h2V_w : twoV_K < 2 ^ w := by omega
  have hlm_w : lmin_2K < 2 ^ w := by omega
  have how_w : outWAddr < 2 ^ w := by omega
  set div1Out := heap + 9 * K + Num.integerDivideSpace (2 * K)
  have hdiv1_add : div1Out + 7 * K + Num.integerDivideSpace (2 * K) = heap + weightStepSpace K := by
    dsimp only [div1Out, weightStepSpace]; ring
  have h2K_ws : 2 * K ≤ weightStepSpace K := by unfold weightStepSpace; omega
  have hdiv1_w : div1Out < 2 ^ w := by omega
  have hdiv1_K_w : div1Out + K < 2 ^ w := by omega
  have hdiv1_5K_w : div1Out + K + 4 * K < 2 ^ w := by omega
  have hdiv1_7K_w : div1Out + K + 6 * K < 2 ^ w := by omega
  have hdiv1_end_w : div1Out + K + 6 * K + Num.integerDivideSpace (2 * K) < 2 ^ w := by omega
  have h4K_w : 4 * K < 2 ^ w := by omega
  have hheap_le_div1 : heap ≤ div1Out := by dsimp only [div1Out]; omega
  have hq2_w : heap + weightStepSpace K - 2 * K < 2 ^ w := by omega
  have hq2_add_w : heap + weightStepSpace K - 2 * K + K ≤ heap + weightStepSpace K := by omega
  have hq2_sub_w : heap + weightStepSpace K - 2 * K + K < 2 ^ w := by omega
  have how_le_q2 : outWAddr + K ≤ heap + weightStepSpace K - 2 * K := by omega
  have heL_w : e * L < 2 ^ w := by omega
  refine runs_start_le ?_
  -- 6. r14 := lenPtr + e * L; signExtend l_e -> l_K at [div1Out, div1Out + K)
  refine runs_seq_assign_step (Expr.eval_add (Expr.eval_reg_of_eq hws.r1)
    (Expr.eval_mul (Expr.eval_reg_of_eq hws.r0) (Expr.eval_reg_of_eq hws.r3) heL_w)
    hlen_sub_w) rfl fun st10 hm10 _ hr10 => ?_
  have hvlen5 : Num.Valid st10.mem (lenPtr + e * L) h L ∧
      Num.intVal st10.mem (lenPtr + e * L) h L = Num.intVal mem (lenPtr + e * L) h L := by
    have heq : ∀ i < L, st10.mem (lenPtr + e * L + i) = mem (lenPtr + e * L + i) := fun i hi => by
      have hne : lenPtr + e * L + i ≠ outMultAddr := by rcases homl_disj with h | h <;> omega
      have hlt : lenPtr + e * L + i < heap := lt_of_lt_of_le (Nat.add_lt_add_left hi _) hlen_h
      rw [hm10, hpres _ hlt hne]
    exact ⟨numValid_congr (fun i hi => (heq i hi).symm) hvlen, intVal_congr_range heq⟩
  have hz10 : ZeroFrom st10.mem div1Out := fun a ha => by rw [hm10]; exact hz a ha
  have hws10 := wsRegs_upd hws hr10 (by decide)
  have hr14_10 : st10.regs 14 = lenPtr + e * L := by rw [hr10, Function.update_self]
  have hr15_10 : st10.regs 15 = div1Out := by rw [hr10, Function.update_of_ne (by decide), hr15]
  refine runs_seq_call_step hse_mc (vs := [lenPtr + e * L, L, K, div1Out])
    (evalArgs_cons (Expr.eval_reg_of_eq hr14_10)
      (evalArgs_cons (Expr.eval_reg_of_eq hws10.r3)
        (evalArgs_cons (Expr.eval_reg_of_eq hws10.r4)
          (evalArgs_cons (Expr.eval_reg_of_eq hr15_10) (evalArgs_nil _ _)))))
    (fun x hx => by simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> assumption)
    ⟨⟨lenPtr + e * L, L, K, div1Out, rfl, hLK, le_trans hlen_h hheap_le_div1, hvlen5.1⟩, hz10, hdiv1_K_w⟩
    rfl (rfl : _ = 30 * K + 42)
    fun hp5 mem6 st11 hpost5 hm11 hr11 => ?_
  obtain ⟨hhp5, hlo5, hhi5, hfr6, hz6, hv_lK, hi_lK⟩ := hpost5
  clear hlo5 hhi5
  have hhp5_val : hp5 = div1Out + K := by
    have ha : heapArg [lenPtr + e * L, L, K, div1Out] = div1Out := rfl
    have hg : ([lenPtr + e * L, L, K, div1Out] : List ℕ).getD 2 0 = K := rfl
    rw [ha, hg] at hhp5; exact hhp5
  have hz6' : ZeroFrom mem6 (div1Out + K) := hhp5_val ▸ hz6
  have hv_lK' : Num.Valid mem6 div1Out h K := hv_lK
  have hi_lK' : Num.intVal mem6 div1Out h K = Num.intVal st10.mem (lenPtr + e * L) h L := hi_lK
  have hfr6' : ∀ x < div1Out, mem6 x = st10.mem x := hfr6
  clear hfr6 hz6 hv_lK hi_lK hhp5
  have hws11 := wsRegs_upd hws10 hr11 (by decide)
  have hr15_11 : st11.regs 15 = div1Out := by rw [hr11, Function.update_of_ne (by decide), hr15_10]
  have hr16_11 : st11.regs 16 = div1Out + K := by rw [hr11, hhp5_val, Function.update_self]
  -- 7. multiply twoV_K * l_K -> prod2 at [div1Out + K + 4*K, div1Out + K + 6*K)
  have hv_2V6 : Num.Valid mem6 twoV_K h K ∧
      Num.intVal mem6 twoV_K h K = ((2 * Vcnt : ℕ) : ℤ) := by
    have heq : ∀ i < K, mem6 (twoV_K + i) = mem (twoV_K + i) := fun i hi => by
      have hne : twoV_K + i ≠ outMultAddr := by rcases hom2V_disj with h | h <;> omega
      have hlt : twoV_K + i < heap := lt_of_lt_of_le (Nat.add_lt_add_left hi _) h2V_h
      have hlt4 : twoV_K + i < div1Out := lt_of_lt_of_le hlt hheap_le_div1
      rw [hfr6' _ hlt4, hm10, hpres _ hlt hne]
    exact ⟨numValid_congr (fun i hi => (heq i hi).symm) hv2v, by rw [intVal_congr_range heq, hi2v]⟩
  refine runs_seq_call_step hml_mc (vs := [twoV_K, div1Out, K, div1Out + K])
    (evalArgs_cons (Expr.eval_reg_of_eq hws11.r6)
      (evalArgs_cons (Expr.eval_reg_of_eq hr15_11)
        (evalArgs_cons (Expr.eval_reg_of_eq hws11.r4)
          (evalArgs_cons (Expr.eval_reg_of_eq hr16_11) (evalArgs_nil _ _)))))
    (fun x hx => by simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> assumption)
    (hm11 ▸ ⟨⟨twoV_K, div1Out, K, div1Out + K, rfl,
      le_trans h2V_h (le_trans hheap_le_div1 (Nat.le_add_right _ _)),
      Nat.le_refl _, hv_2V6.1, hv_lK'⟩, hz6', hdiv1_7K_w⟩)
    rfl (rfl : _ = 2 * K * (38 * (2 * K) + 35) + 120 * K + 99)
    fun hp6 mem7 st12 hpost6 hm12 hr12 => ?_
  rw [hm11] at hpost6
  obtain ⟨hhp6, hlo6, hhi6, hfr7, hz7, hv_p2, hi_p2⟩ := hpost6
  clear hlo6 hhi6
  have hhp6_val : hp6 = div1Out + K + 6 * K := by
    have ha : heapArg [twoV_K, div1Out, K, div1Out + K] = div1Out + K := rfl
    have hg : ([twoV_K, div1Out, K, div1Out + K] : List ℕ).getD 2 0 = K := rfl
    rw [ha, hg] at hhp6; exact hhp6
  have hz7' : ZeroFrom mem7 (div1Out + K + 6 * K) := hhp6_val ▸ hz7
  have hv_p2' : Num.Valid mem7 (div1Out + K + 4 * K) h (2 * K) := hv_p2
  have hi_p2' : Num.intVal mem7 (div1Out + K + 4 * K) h (2 * K) =
      Num.intVal mem6 twoV_K h K * Num.intVal mem6 div1Out h K := hi_p2
  have hfr7' : ∀ x < div1Out + K, mem7 x = mem6 x := hfr7
  clear hfr7 hz7 hv_p2 hi_p2 hhp6
  have hws12 := wsRegs_upd hws11 hr12 (by decide)
  have hr16_12 : st12.regs 16 = div1Out + K := by rw [hr12, Function.update_of_ne (by decide), hr16_11]
  have hr17_12 : st12.regs 17 = div1Out + K + 6 * K := by rw [hr12, hhp6_val, Function.update_self]
  -- 8. r18 := div1Out + 5*K; integerDivide prod2 / lmin_2K -> q2 at [hp_end - 2*K, hp_end)
  have hv_lm7 : Num.Valid mem7 lmin_2K h (2 * K) ∧
      Num.intVal mem7 lmin_2K h (2 * K) = (lmin_val : ℤ) := by
    have heq : ∀ i < 2 * K, mem7 (lmin_2K + i) = mem (lmin_2K + i) := fun i hi => by
      have hne : lmin_2K + i ≠ outMultAddr := by rcases homlm_disj with h | h <;> omega
      have hlt : lmin_2K + i < heap := lt_of_lt_of_le (Nat.add_lt_add_left hi _) hlm_h
      have hlt4 : lmin_2K + i < div1Out := lt_of_lt_of_le hlt hheap_le_div1
      have hlt5 : lmin_2K + i < div1Out + K := lt_of_lt_of_le hlt4 (Nat.le_add_right _ _)
      rw [hfr7' _ hlt5, hfr6' _ hlt4, hm10, hpres _ hlt hne]
    exact ⟨numValid_congr (fun i hi => (heq i hi).symm) hvlm, by rw [intVal_congr_range heq, hilm]⟩
  refine runs_seq_assign_step (Expr.eval_add (Expr.eval_reg_of_eq hr16_12)
    (Expr.eval_mul (Expr.eval_const h4_w) (Expr.eval_reg_of_eq hws12.r4) h4K_w)
    hdiv1_5K_w) rfl fun st13 hm13 _ hr13 => ?_
  have hws13 := wsRegs_upd hws12 hr13 (by decide)
  have hr17_13 : st13.regs 17 = div1Out + K + 6 * K := by rw [hr13, Function.update_of_ne (by decide), hr17_12]
  have hr18_13 : st13.regs 18 = div1Out + K + 4 * K := by rw [hr13, Function.update_self]
  have hmem13_eq : st13.mem = mem7 := hm13.trans hm12
  refine runs_seq_call_step hdv_mc (vs := [div1Out + K + 4 * K, lmin_2K, 2 * K, div1Out + K + 6 * K])
    (evalArgs_cons (Expr.eval_reg_of_eq hr18_13)
      (evalArgs_cons (Expr.eval_reg_of_eq hws13.r9)
        (evalArgs_cons (Expr.eval_reg_of_eq hws13.r13)
          (evalArgs_cons (Expr.eval_reg_of_eq hr17_13) (evalArgs_nil _ _)))))
    (fun x hx => by simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> assumption)
    (hmem13_eq ▸ ⟨⟨div1Out + K + 4 * K, lmin_2K, 2 * K, div1Out + K + 6 * K, rfl, le_of_eq (by ring),
      le_trans hlm_h (le_trans hheap_le_div1 (le_trans (Nat.le_add_right div1Out K) (Nat.le_add_right _ _))),
      hv_p2', hv_lm7.1, by rw [hv_lm7.2]; exact_mod_cast Nat.ne_of_gt hlm1⟩,
      hz7', hdiv1_end_w⟩)
    rfl (rfl : _ = 2 * K * (300 * (2 * K) + 644) + 180 * (2 * K) + 400)
    fun hp_end mem8 st14 hpost7 hm14 hr14 => ?_
  rw [hmem13_eq] at hpost7
  obtain ⟨hhp_end, hlo7, hhi7, hfr8, hz8, hv_q2, hint_q2⟩ := hpost7
  clear hlo7 hhi7
  have hhp_end_val : hp_end = heap + weightStepSpace K := by
    have ha : heapArg [div1Out + K + 4 * K, lmin_2K, 2 * K, div1Out + K + 6 * K] =
        div1Out + K + 6 * K := rfl
    have hg : ([div1Out + K + 4 * K, lmin_2K, 2 * K, div1Out + K + 6 * K] : List ℕ).getD 2 0 =
        2 * K := rfl
    rw [ha, hg] at hhp_end
    rw [hhp_end, show div1Out + K + 6 * K = div1Out + 7 * K by ring]
    exact hdiv1_add
  have hz8' : ZeroFrom mem8 (heap + weightStepSpace K) := hhp_end_val ▸ hz8
  have hfr8' : ∀ x < div1Out + K + 6 * K, mem8 x = mem7 x := hfr8
  have hq2_addr : heapArg [div1Out + K + 4 * K, lmin_2K, 2 * K, div1Out + K + 6 * K] +
      2 * ([div1Out + K + 4 * K, lmin_2K, 2 * K, div1Out + K + 6 * K].getD 2 0) +
      Num.unsignedDivideSpace ([div1Out + K + 4 * K, lmin_2K, 2 * K, div1Out + K + 6 * K].getD 2 0) =
      heap + weightStepSpace K - 2 * K := by
    have ha : heapArg [div1Out + K + 4 * K, lmin_2K, 2 * K, div1Out + K + 6 * K] =
        div1Out + K + 6 * K := rfl
    have hg : ([div1Out + K + 4 * K, lmin_2K, 2 * K, div1Out + K + 6 * K] : List ℕ).getD 2 0 =
        2 * K := rfl
    have hsp : Num.integerDivideSpace (2 * K) = Num.unsignedDivideSpace (2 * K) + 3 * (2 * K) := rfl
    rw [ha, hg]
    have hsub_add : div1Out + K + 6 * K + 2 * (2 * K) + Num.unsignedDivideSpace (2 * K) + 2 * K =
        heap + weightStepSpace K := by rw [← hdiv1_add, hsp]; ring
    exact eq_tsub_of_add_eq hsub_add
  have hq2_len : ([div1Out + K + 4 * K, lmin_2K, 2 * K, div1Out + K + 6 * K] : List ℕ).getD 2 0 =
      2 * K := rfl
  rw [hq2_addr, hq2_len] at hv_q2
  rw [hq2_addr] at hint_q2
  clear hfr8 hz8 hhp_end
  have hq2_limbs : LimbsAt mem8 (heap + weightStepSpace K - 2 * K) K h
      ((2 * Vcnt * Num.unsignedVal mem (lenPtr + e * L) h L) / lmin_val) := by
    have hw_int_eq : Num.intVal mem8 (heap + weightStepSpace K - 2 * K) h (2 * K) =
        (((2 * Vcnt * Num.unsignedVal mem (lenPtr + e * L) h L) / lmin_val : ℕ) : ℤ) := by
      have hi_p2'' : Num.intVal mem7 (div1Out + K + 4 * K) h (2 * K) =
          ((2 * Vcnt * Num.unsignedVal mem (lenPtr + e * L) h L : ℕ) : ℤ) := by
        rw [hi_p2', hv_2V6.2, hi_lK', hvlen5.2, hl_nat.1]; push_cast; ring
      change Num.intVal mem8 (heap + weightStepSpace K - 2 * K) h (2 * K) =
        Num.wrap h (2 * K) (Num.floorDiv (Num.intVal mem7 (div1Out + K + 4 * K) h (2 * K))
          (Num.intVal mem7 lmin_2K h (2 * K))) at hint_q2
      rw [hint_q2, hi_p2'', hv_lm7.2]
      have hfl : Num.floorDiv ((2 * Vcnt * Num.unsignedVal mem (lenPtr + e * L) h L : ℕ) : ℤ)
          (lmin_val : ℤ) =
          (((2 * Vcnt * Num.unsignedVal mem (lenPtr + e * L) h L) / lmin_val : ℕ) : ℤ) := by
        simp [Num.floorDiv]
      rw [hfl, Num.wrap_of_fits (fits_of_lt_half_cap (lt_trans hw_cap hlt_K2))]
    have hw_pos : 1 ≤ (2 * Vcnt * Num.unsignedVal mem (lenPtr + e * L) h L) / lmin_val := by
      have hmul : lmin_val ≤ 2 * Vcnt * Num.unsignedVal mem (lenPtr + e * L) h L :=
        le_trans hlm_le (Nat.le_mul_of_pos_left _ (Nat.mul_pos (by decide) (lt_of_lt_of_le (by decide) hV2)))
      exact Nat.div_pos hmul hlm1
    have hw_nat_eq : Num.unsignedVal mem8 (heap + weightStepSpace K - 2 * K) h (2 * K) =
        (2 * Vcnt * Num.unsignedVal mem (lenPtr + e * L) h L) / lmin_val := by
      have := intVal_eq_nat_of_pos hv_q2 (by rw [hw_int_eq]; exact_mod_cast hw_pos)
      exact Int.ofNat.inj (this.1.symm.trans hw_int_eq)
    have hq2_pref := unsignedVal_prefix_eq (K := K) (M := K) (by simpa [two_mul] using hv_q2)
      (by rw [show K + K = 2 * K by ring, hw_nat_eq]
          exact lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by decide)) hw_cap)
    rw [show K + K = 2 * K by ring] at hq2_pref
    rw [← hw_nat_eq, ← hq2_pref.2]
    exact limbsAt_of_numValid hq2_pref.1
  clear hv_q2 hint_q2
  have hws14 := wsRegs_upd hws13 hr14 (by decide)
  have hr15_14 : st14.regs 15 = heap + weightStepSpace K := by rw [hr14, hhp_end_val, Function.update_self]
  -- 9. r17 := hp_end - 2*K; copyLimbs q2 -> outWAddr
  refine runs_seq_assign_step (Expr.eval_sub (Expr.eval_reg_of_eq hr15_14) (Expr.eval_reg_of_eq hws14.r13)
    hbound) rfl fun st15 hm15 _ hr15 => ?_
  have hws15 := wsRegs_upd hws14 hr15 (by decide)
  have hr15_15 : st15.regs 15 = heap + weightStepSpace K := by rw [hr15, Function.update_of_ne (by decide), hr15_14]
  have hr17_15 : st15.regs 17 = heap + weightStepSpace K - 2 * K := by rw [hr15, Function.update_self]
  have hmem15_eq : st15.mem = mem8 := hm15.trans hm14
  refine runs_seq_call_step hcopy_mc (vs := [heap + weightStepSpace K - 2 * K, K, outWAddr])
    (evalArgs_cons (Expr.eval_reg_of_eq hr17_15)
      (evalArgs_cons (Expr.eval_reg_of_eq hws15.r4)
        (evalArgs_cons (Expr.eval_reg_of_eq hws15.r11) (evalArgs_nil _ _))))
    (fun x hx => by simp at hx; rcases hx with rfl | rfl | rfl <;> assumption)
    (hmem15_eq ▸ ⟨heap + weightStepSpace K - 2 * K, K, outWAddr, rfl, hw1,
      hq2_sub_w, lt_of_le_of_lt (how_h.trans (Nat.le_add_right _ _)) hbound,
      Or.inr how_le_q2⟩)
    rfl (rfl : _ = 25 * K + 15)
    fun ret_c mem9 st16 hpost9 hm16 hr16 => ?_
  rw [hmem15_eq] at hpost9
  obtain ⟨_, _, _, hcopy_eqs, rfl, hcopied, hfr9⟩ := hpost9
  simp only [List.cons.injEq, and_true] at hcopy_eqs
  obtain ⟨rfl, rfl, rfl⟩ := hcopy_eqs
  have hr15_16 : st16.regs 15 = heap + weightStepSpace K := by
    rw [hr16, Function.update_of_ne (by decide), hr15_15]
  refine runs_ret_le (Expr.eval_reg_of_eq hr15_16) ?_ ?_
  · rw [hm16]
    refine ⟨e, lenPtr, wtPtr, L, K, nlCnt_K, twoV_K, S_2K, S_m1_2K, lmin_2K,
      outMultAddr, outWAddr, heap, nlCnt, Vcnt, S_val, lmin_val,
      rfl, hin, hi2v, hiS, hilm, rfl, ?_, ?_, ?_, ?_⟩
    · intro a ha
      rw [hfr9 a (Or.inr (le_trans how_h (le_trans (Nat.le_add_right _ _) ha))), hz8' a ha]
    · intro a ha hao haw
      have hlt4 : a < div1Out := lt_of_lt_of_le ha hheap_le_div1
      have hlt5 : a < div1Out + K := lt_of_lt_of_le hlt4 (Nat.le_add_right _ _)
      have hlt6 : a < div1Out + K + 6 * K := lt_of_lt_of_le hlt5 (Nat.le_add_right _ _)
      rw [hfr9 a haw, hfr8' a hlt6, hfr7' a hlt5, hfr6' a hlt4, hm10, hpres a ha hao]
    · have hlt4 : outMultAddr < div1Out := lt_of_lt_of_le hom_h hheap_le_div1
      have hlt5 : outMultAddr < div1Out + K := lt_of_lt_of_le hlt4 (Nat.le_add_right _ _)
      have hlt6 : outMultAddr < div1Out + K + 6 * K := lt_of_lt_of_le hlt5 (Nat.le_add_right _ _)
      rw [hfr9 outMultAddr homw_disj, hfr8' outMultAddr hlt6, hfr7' outMultAddr hlt5,
        hfr6' outMultAddr hlt4, hm10, hmult_mem]
    · exact limbsAt_iff_pointwise.mpr ⟨hq2_limbs.lt_pow, fun i hi => by
        rw [hcopied i hi]; exact hq2_limbs.getElem hi⟩
  · have hsum_le := weightStep_phase2_le K
    dsimp only [argsSize, Expr.size]
    exact le_trans (le_of_eq (by ring)) hsum_le

theorem weightStep_meetsContract {w b h : ℕ} {p : Program}
    (hp : p.HasAt b (weightsModule b h)) :
    MeetsContract w p (b + idxWeightStep) (weightStepContract w h) := by
  have hsub := weights_hasAt_sub hp
  have hentry : p.procs[b + idxWeightStep]? =
      some (weightStepProc (b + idxCopyLimbs) (b + idxWPackWord) (b + idxWSignExtend)
        (b + idxWAdd) (b + idxWMultiply) (b + idxWIntegerDivide)) := by
    have := hp 4 (by rw [weightsModule_length]; omega)
    simpa [weightsModule, idxWeightStep] using this
  have hcopy_mc := copyLimbs_meetsContract (w := w) hp
  refine meetsContract_of_runs hentry ?_
  rintro args mem pos ω _ ⟨e, lenPtr, wtPtr, L, K, nlCnt_K, twoV_K, S_2K, S_m1_2K, lmin_2K,
    outMultAddr, outWAddr, heap, nlCnt, Vcnt, S_val, lmin_val, rfl, hh, hw, hL1, hLK, hnl1, hnl_w, hV2,
    hvlen, hplen, hvwt, hpwt, hvn, hin, hv2v, hi2v, hvS, hiS, hS1, hvSm1, hiSm1, hvlm, hilm, hlm1,
    hvleS, hlm_le, hnl_cap, hnum1_cap, hw_cap, hlen_h, hwt_h, hnlK_h, h2V_h, hS_h, hSm1_h, hlm_h,
    hom_h, how_h, homw_disj, homl_disj, hom2V_disj, homlm_disj, hz0, hbound⟩
  have hbh : Num.base h < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hw1 : 1 < 2 ^ w := lt_of_le_of_lt
    (by simpa [Num.base] using Nat.one_le_two_pow (n := h)) hbh
  have hw2 : 2 * h + 2 ≤ w := by omega
  have h4_w : 4 < 2 ^ w := lt_of_lt_of_le (by norm_num : 4 < 2 ^ 5)
    (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hse_mc := Num.signExtend_meetsContract hh hw1 hbh hsub.2.2.2.1
  have hml_mc := Num.multiply_meetsContract hh hw2 hsub.2.2.2.2.2.2.1
  have had_mc := Num.add_meetsContract hh hw2 hsub.2.2.2.2.1
  have hdv_mc := Num.integerDivide_meetsContract hh hw hsub.2.2.2.2.2.2.2
  have hpk_mc := Num.packWord_meetsContract hw1 hbh hsub.2.1
  have hv_nat := intVal_eq_nat_of_pos hvwt hpwt
  have hl_nat := intVal_eq_nat_of_pos hvlen hplen
  have hK1 : 1 ≤ K := by omega
  have hdiv_ge : 2 ≤ Num.integerDivideSpace (2 * K) := by
    unfold Num.integerDivideSpace Num.unsignedDivideSpace; omega
  have hlt_K2 : Num.capacity h K < Num.capacity h (2 * K) := by
    simp only [Num.capacity, Num.base, ← pow_mul]
    exact Nat.pow_lt_pow_right (by norm_num) (by nlinarith)
  have hK_w : K < 2 ^ w := by unfold weightStepSpace at hbound; omega
  have h2K_w : 2 * K < 2 ^ w := by unfold weightStepSpace at hbound; omega
  have hL_w : L < 2 ^ w := by omega
  have he_w : e < 2 ^ w := by
    have : e ≤ e * L := Nat.le_mul_of_pos_right e hL1
    omega
  have hwt_sub_w : wtPtr + e * L < 2 ^ w := by omega
  have hlen_sub_w : lenPtr + e * L < 2 ^ w := by omega
  have hheap_w : heap < 2 ^ w := by unfold weightStepSpace at hbound; omega
  have hnlK_w : nlCnt_K < 2 ^ w := by omega
  have h2V_w : twoV_K < 2 ^ w := by omega
  have hS_w : S_2K < 2 ^ w := by omega
  have hSm1_w : S_m1_2K < 2 ^ w := by omega
  have hlm_w : lmin_2K < 2 ^ w := by omega
  have hom_w : outMultAddr < 2 ^ w := by omega
  have how_w : outWAddr < 2 ^ w := by omega
  have h4K_w : 4 * K < 2 ^ w := by unfold weightStepSpace at hbound; omega
  have heL_w : e * L < 2 ^ w := by omega
  set div1Out := heap + 9 * K + Num.integerDivideSpace (2 * K)
  have hdiv1_add : div1Out + 7 * K + Num.integerDivideSpace (2 * K) = heap + weightStepSpace K := by
    dsimp only [div1Out, weightStepSpace]; ring
  have hheap_le_div1 : heap + 9 * K ≤ div1Out := by dsimp only [div1Out]; omega
  have hdiv1_w : div1Out < 2 ^ w := by omega
  have hheap_K_w : heap + K < 2 ^ w := by omega
  have hheap_5K_w : heap + K + 4 * K < 2 ^ w := by omega
  have hheap_7K_w : heap + K + 6 * K < 2 ^ w := by omega
  have hheap_9K_w : heap + K + 6 * K + 2 * K < 2 ^ w := by omega
  have hdiv1_m2K_w : div1Out - 2 * K < 2 ^ w := by omega
  have hdiv1_mK_w : div1Out - 2 * K + K < 2 ^ w := by omega
  refine runs_start_le ?_
  unfold weightStepProc
  -- r13 := 2 * K
  refine runs_seq_assign_step (Expr.eval_mul (Expr.eval_const (by omega))
    (Expr.eval_reg_of_eq (v := K) rfl) h2K_w) rfl fun st0 hm0 _ hr0 => ?_
  have hws0 : WSRegs st0 e lenPtr wtPtr L K nlCnt_K twoV_K S_2K S_m1_2K lmin_2K outMultAddr outWAddr :=
    ⟨by rw [hr0, Function.update_of_ne (by decide)]; rfl,
     by rw [hr0, Function.update_of_ne (by decide)]; rfl,
     by rw [hr0, Function.update_of_ne (by decide)]; rfl,
     by rw [hr0, Function.update_of_ne (by decide)]; rfl,
     by rw [hr0, Function.update_of_ne (by decide)]; rfl,
     by rw [hr0, Function.update_of_ne (by decide)]; rfl,
     by rw [hr0, Function.update_of_ne (by decide)]; rfl,
     by rw [hr0, Function.update_of_ne (by decide)]; rfl,
     by rw [hr0, Function.update_of_ne (by decide)]; rfl,
     by rw [hr0, Function.update_of_ne (by decide)]; rfl,
     by rw [hr0, Function.update_of_ne (by decide)]; rfl,
     by rw [hr0, Function.update_of_ne (by decide)]; rfl,
     by rw [hr0, Function.update_self]⟩
  have hr12_0 : st0.regs 12 = heap := by rw [hr0, Function.update_of_ne (by decide)]; rfl
  -- r14 := wtPtr + e * L
  refine runs_seq_assign_step (Expr.eval_add (Expr.eval_reg_of_eq hws0.r2)
    (Expr.eval_mul (Expr.eval_reg_of_eq hws0.r0) (Expr.eval_reg_of_eq hws0.r3) heL_w)
    hwt_sub_w) rfl fun st1 hm1 _ hr1 => ?_
  have hws1 := wsRegs_upd hws0 hr1 (by decide)
  have hr12_1 : st1.regs 12 = heap := by rw [hr1, Function.update_of_ne (by decide), hr12_0]
  have hr14_1 : st1.regs 14 = wtPtr + e * L := by rw [hr1, Function.update_self]
  have hmem1_eq : st1.mem = mem := hm1.trans hm0
  -- 1. signExtend v_e -> v_K at [heap, heap + K)
  refine runs_seq_call_step hse_mc (vs := [wtPtr + e * L, L, K, heap])
    (evalArgs_cons (Expr.eval_reg_of_eq hr14_1)
      (evalArgs_cons (Expr.eval_reg_of_eq hws1.r3)
        (evalArgs_cons (Expr.eval_reg_of_eq hws1.r4)
          (evalArgs_cons (Expr.eval_reg_of_eq hr12_1) (evalArgs_nil _ _)))))
    (fun x hx => by simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> assumption)
    (hmem1_eq ▸ ⟨⟨wtPtr + e * L, L, K, heap, rfl, hLK, hwt_h, hvwt⟩, hz0, hheap_K_w⟩)
    rfl (rfl : _ = 30 * K + 42)
    fun hp1 mem1 st2 hpost1 hm2 hr2 => ?_
  rw [hmem1_eq] at hpost1
  obtain ⟨hhp1, hlo1, hhi1, hfr1, hz1, hv1, hi1⟩ := hpost1
  clear hlo1 hhi1
  have hhp1_val : hp1 = heap + K := by
    have ha : heapArg [wtPtr + e * L, L, K, heap] = heap := rfl
    have hg : ([wtPtr + e * L, L, K, heap] : List ℕ).getD 2 0 = K := rfl
    rw [ha, hg] at hhp1; exact hhp1
  have hz1' : ZeroFrom mem1 (heap + K) := hhp1_val ▸ hz1
  have hv1' : Num.Valid mem1 heap h K := hv1
  have hi1' : Num.intVal mem1 heap h K = Num.intVal mem (wtPtr + e * L) h L := hi1
  have hfr1' : ∀ x < heap, mem1 x = mem x := hfr1
  clear hfr1 hz1 hv1 hi1 hhp1
  have hws2 := wsRegs_upd hws1 hr2 (by decide)
  have hr12_2 : st2.regs 12 = heap := by rw [hr2, Function.update_of_ne (by decide), hr12_1]
  have hr15_2 : st2.regs 15 = heap + K := by rw [hr2, hhp1_val, Function.update_self]
  -- 2. multiply nlCnt_K * v_K -> prod1 at [heap + K + 4*K, heap + K + 6*K)
  have hv_nl1 : Num.Valid mem1 nlCnt_K h K ∧ Num.intVal mem1 nlCnt_K h K = (nlCnt : ℤ) := by
    have heq : ∀ i < K, mem1 (nlCnt_K + i) = mem (nlCnt_K + i) := fun i hi =>
      hfr1' _ (lt_of_lt_of_le (Nat.add_lt_add_left hi nlCnt_K) hnlK_h)
    exact ⟨numValid_congr (fun i hi => (heq i hi).symm) hvn, by rw [intVal_congr_range heq, hin]⟩
  refine runs_seq_call_step hml_mc (vs := [nlCnt_K, heap, K, heap + K])
    (evalArgs_cons (Expr.eval_reg_of_eq hws2.r5)
      (evalArgs_cons (Expr.eval_reg_of_eq hr12_2)
        (evalArgs_cons (Expr.eval_reg_of_eq hws2.r4)
          (evalArgs_cons (Expr.eval_reg_of_eq hr15_2) (evalArgs_nil _ _)))))
    (fun x hx => by simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> assumption)
    (hm2 ▸ ⟨⟨nlCnt_K, heap, K, heap + K, rfl, le_trans hnlK_h (Nat.le_add_right _ _),
      Nat.le_refl _, hv_nl1.1, hv1'⟩, hz1', hheap_7K_w⟩)
    rfl (rfl : _ = 2 * K * (38 * (2 * K) + 35) + 120 * K + 99)
    fun hp2 mem2 st3 hpost2 hm3 hr3 => ?_
  rw [hm2] at hpost2
  obtain ⟨hhp2, hlo2, hhi2, hfr2, hz2, hv2, hi2⟩ := hpost2
  clear hlo2 hhi2
  have hhp2_val : hp2 = heap + K + 6 * K := by
    have ha : heapArg [nlCnt_K, heap, K, heap + K] = heap + K := rfl
    have hg : ([nlCnt_K, heap, K, heap + K] : List ℕ).getD 2 0 = K := rfl
    rw [ha, hg] at hhp2; exact hhp2
  have hz2' : ZeroFrom mem2 (heap + K + 6 * K) := hhp2_val ▸ hz2
  have hv2' : Num.Valid mem2 (heap + K + 4 * K) h (2 * K) := hv2
  have hi2' : Num.intVal mem2 (heap + K + 4 * K) h (2 * K) =
      Num.intVal mem1 nlCnt_K h K * Num.intVal mem1 heap h K := hi2
  have hfr2' : ∀ x < heap + K, mem2 x = mem1 x := hfr2
  clear hfr2 hz2 hv2 hi2 hhp2
  have hws3 := wsRegs_upd hws2 hr3 (by decide)
  have hr12_3 : st3.regs 12 = heap := by rw [hr3, Function.update_of_ne (by decide), hr12_2]
  have hr15_3 : st3.regs 15 = heap + K := by rw [hr3, Function.update_of_ne (by decide), hr15_2]
  have hr16_3 : st3.regs 16 = heap + K + 6 * K := by rw [hr3, hhp2_val, Function.update_self]
  -- 3. r17 := heap + K + 4*K; add prod1 + S_m1_2K -> num1 at [heap + 7*K, heap + 9*K)
  have hv_Sm1_2 : Num.Valid mem2 S_m1_2K h (2 * K) ∧
      Num.intVal mem2 S_m1_2K h (2 * K) = ((S_val - 1 : ℕ) : ℤ) := by
    have heq : ∀ i < 2 * K, mem2 (S_m1_2K + i) = mem (S_m1_2K + i) := fun i hi => by
      have hlt : S_m1_2K + i < heap := lt_of_lt_of_le (Nat.add_lt_add_left hi S_m1_2K) hSm1_h
      rw [hfr2' _ (lt_of_lt_of_le hlt (Nat.le_add_right heap K)), hfr1' _ hlt]
    exact ⟨numValid_congr (fun i hi => (heq i hi).symm) hvSm1, by rw [intVal_congr_range heq, hiSm1]⟩
  refine runs_seq_assign_step (Expr.eval_add (Expr.eval_reg_of_eq hr15_3)
    (Expr.eval_mul (Expr.eval_const h4_w) (Expr.eval_reg_of_eq hws3.r4) h4K_w)
    hheap_5K_w) rfl fun st4 hm4 _ hr4 => ?_
  have hws4 := wsRegs_upd hws3 hr4 (by decide)
  have hr12_4 : st4.regs 12 = heap := by rw [hr4, Function.update_of_ne (by decide), hr12_3]
  have hr16_4 : st4.regs 16 = heap + K + 6 * K := by rw [hr4, Function.update_of_ne (by decide), hr16_3]
  have hr17_4 : st4.regs 17 = heap + K + 4 * K := by rw [hr4, Function.update_self]
  have hmem4_eq : st4.mem = mem2 := hm4.trans hm3
  refine runs_seq_call_step had_mc (vs := [heap + K + 4 * K, S_m1_2K, 2 * K, heap + K + 6 * K])
    (evalArgs_cons (Expr.eval_reg_of_eq hr17_4)
      (evalArgs_cons (Expr.eval_reg_of_eq hws4.r8)
        (evalArgs_cons (Expr.eval_reg_of_eq hws4.r13)
          (evalArgs_cons (Expr.eval_reg_of_eq hr16_4) (evalArgs_nil _ _)))))
    (fun x hx => by simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> assumption)
    (hmem4_eq ▸ ⟨heap + K + 4 * K, S_m1_2K, 2 * K, heap + K + 6 * K, rfl,
      ⟨heap + K + 4 * K, S_m1_2K, 2 * K, 0, heap + K + 6 * K, rfl,
        le_of_eq (by ring), le_trans hSm1_h (le_trans (Nat.le_add_right heap K) (Nat.le_add_right _ _)),
        Nat.zero_le 1, hv2', hv_Sm1_2.1⟩, hz2', hheap_9K_w⟩)
    rfl (rfl : _ = 38 * (2 * K) + 15)
    fun hp3 mem3 st5 hpost3 hm5 hr5 => ?_
  rw [hmem4_eq] at hpost3
  obtain ⟨hhp3, hlo3, hhi3, hfr3, hz3, hdig_num1⟩ := hpost3
  clear hlo3 hhi3
  have hhp3_val : hp3 = heap + K + 6 * K + 2 * K := by
    have ha : heapArg (Num.addArgs [heap + K + 4 * K, S_m1_2K, 2 * K, heap + K + 6 * K]) = heap + K + 6 * K := rfl
    have hg : (Num.addArgs [heap + K + 4 * K, S_m1_2K, 2 * K, heap + K + 6 * K]).getD 2 0 = 2 * K := rfl
    rw [ha, hg] at hhp3; exact hhp3
  have hz3' : ZeroFrom mem3 (heap + K + 6 * K + 2 * K) := hhp3_val ▸ hz3
  have hfr3' : ∀ x < heap + K + 6 * K, mem3 x = mem2 x := hfr3
  have hnum1_prop : Num.Valid mem3 (heap + K + 6 * K) h (2 * K) ∧
      Num.intVal mem3 (heap + K + 6 * K) h (2 * K) =
        ((nlCnt * Num.unsignedVal mem (wtPtr + e * L) h L + S_val - 1 : ℕ) : ℤ) := by
    have hdig_num1' : ListAt mem3 (heap + K + 6 * K) (Num.digits h (2 * K)
        (Num.unsignedVal mem2 (heap + K + 4 * K) h (2 * K) +
          Num.unsignedVal mem2 S_m1_2K h (2 * K) + 0)) := hdig_num1
    have hnum1_fits : Num.Fits h (2 * K)
        (Num.intVal mem2 (heap + K + 4 * K) h (2 * K) + Num.intVal mem2 S_m1_2K h (2 * K) + 0) := by
      rw [hi2', hv_nl1.2, hi1', hv_nat.1, hv_Sm1_2.2, add_zero]
      have hle_sum : (nlCnt : ℤ) * ↑(Num.unsignedVal mem (wtPtr + e * L) h L) + ↑(S_val - 1) =
          ((nlCnt * Num.unsignedVal mem (wtPtr + e * L) h L + (S_val - 1) : ℕ) : ℤ) := by
        push_cast; ring
      rw [hle_sum]
      exact fits_of_lt_half_cap hnum1_cap
    have hnum1_val := Num.addCarry_value hdig_num1'
    have hnum1_int := Num.addCarry_value_of_fits hdig_num1' hnum1_fits
    refine ⟨hnum1_val.1, ?_⟩
    rw [hnum1_int, hi2', hv_nl1.2, hi1', hv_nat.1, hv_Sm1_2.2, Int.ofNat_zero, add_zero]
    have hpos_mul : 1 ≤ nlCnt * Num.unsignedVal mem (wtPtr + e * L) h L :=
      Nat.mul_pos hnl1 hv_nat.2.2
    push_cast [Nat.cast_sub hS1, Nat.cast_sub (by omega : 1 ≤ nlCnt * Num.unsignedVal mem (wtPtr + e * L) h L + S_val)]
    ring
  clear hfr3 hz3 hdig_num1 hhp3
  have hws5 := wsRegs_upd hws4 hr5 (by decide)
  have hr12_5 : st5.regs 12 = heap := by rw [hr5, Function.update_of_ne (by decide), hr12_4]
  have hr16_5 : st5.regs 16 = heap + K + 6 * K := by rw [hr5, Function.update_of_ne (by decide), hr16_4]
  have hr18_5 : st5.regs 18 = heap + K + 6 * K + 2 * K := by rw [hr5, hhp3_val, Function.update_self]
  -- 4. integerDivide num1 / S_2K -> q1 at [div1Out - 2*K, div1Out)
  have hv_S3 : Num.Valid mem3 S_2K h (2 * K) ∧ Num.intVal mem3 S_2K h (2 * K) = (S_val : ℤ) := by
    have heq : ∀ i < 2 * K, mem3 (S_2K + i) = mem (S_2K + i) := fun i hi => by
      have hlt : S_2K + i < heap := lt_of_lt_of_le (Nat.add_lt_add_left hi S_2K) hS_h
      have hlt1 : S_2K + i < heap + K := lt_of_lt_of_le hlt (Nat.le_add_right _ _)
      have hlt2 : S_2K + i < heap + K + 6 * K := lt_of_lt_of_le hlt1 (Nat.le_add_right _ _)
      rw [hfr3' _ hlt2, hfr2' _ hlt1, hfr1' _ hlt]
    exact ⟨numValid_congr (fun i hi => (heq i hi).symm) hvS, by rw [intVal_congr_range heq, hiS]⟩
  refine runs_seq_call_step hdv_mc (vs := [heap + K + 6 * K, S_2K, 2 * K, heap + K + 6 * K + 2 * K])
    (evalArgs_cons (Expr.eval_reg_of_eq hr16_5)
      (evalArgs_cons (Expr.eval_reg_of_eq hws5.r7)
        (evalArgs_cons (Expr.eval_reg_of_eq hws5.r13)
          (evalArgs_cons (Expr.eval_reg_of_eq hr18_5) (evalArgs_nil _ _)))))
    (fun x hx => by simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> assumption)
    (hm5 ▸ ⟨⟨heap + K + 6 * K, S_2K, 2 * K, heap + K + 6 * K + 2 * K, rfl, Nat.le_refl _,
      le_trans hS_h (le_trans (Nat.le_add_right heap K)
        (le_trans (Nat.le_add_right (heap + K) (6 * K)) (Nat.le_add_right _ _))),
      hnum1_prop.1, hv_S3.1, by rw [hv_S3.2]; exact_mod_cast Nat.ne_of_gt hS1⟩,
      hz3', by
        dsimp only [heapArg, List.getD]
        have hsum : heap + K + 6 * K + 2 * K + Num.integerDivideSpace (2 * K) = div1Out := by
          dsimp only [div1Out]; ring
        exact hsum.symm ▸ hdiv1_w⟩)
    rfl (rfl : _ = 2 * K * (300 * (2 * K) + 644) + 180 * (2 * K) + 400)
    fun hp4 mem4 st6 hpost4 hm6 hr6 => ?_
  rw [hm5] at hpost4
  obtain ⟨hhp4, hlo4, hhi4, hfr4, hz4, hv_q1, hint_q1⟩ := hpost4
  clear hlo4 hhi4
  have hhp4_val : hp4 = div1Out := by
    have ha : heapArg [heap + K + 6 * K, S_2K, 2 * K, heap + K + 6 * K + 2 * K] =
        heap + K + 6 * K + 2 * K := rfl
    have hg : ([heap + K + 6 * K, S_2K, 2 * K, heap + K + 6 * K + 2 * K] : List ℕ).getD 2 0 = 2 * K := rfl
    rw [ha, hg] at hhp4; dsimp only [div1Out]; rw [hhp4]; omega
  have hfr4' : ∀ x < heap + K + 6 * K + 2 * K, mem4 x = mem3 x := hfr4
  have hq1_addr : heapArg [heap + K + 6 * K, S_2K, 2 * K, heap + K + 6 * K + 2 * K] +
      2 * ([heap + K + 6 * K, S_2K, 2 * K, heap + K + 6 * K + 2 * K].getD 2 0) +
      Num.unsignedDivideSpace ([heap + K + 6 * K, S_2K, 2 * K, heap + K + 6 * K + 2 * K].getD 2 0) =
      div1Out - 2 * K := by
    have ha : heapArg [heap + K + 6 * K, S_2K, 2 * K, heap + K + 6 * K + 2 * K] =
        heap + K + 6 * K + 2 * K := rfl
    have hg : ([heap + K + 6 * K, S_2K, 2 * K, heap + K + 6 * K + 2 * K] : List ℕ).getD 2 0 = 2 * K := rfl
    have hsp : Num.integerDivideSpace (2 * K) = Num.unsignedDivideSpace (2 * K) + 3 * (2 * K) := rfl
    rw [ha, hg]
    have hsub_add : heap + K + 6 * K + 2 * K + 2 * (2 * K) + Num.unsignedDivideSpace (2 * K) + 2 * K =
        div1Out := by dsimp only [div1Out]; rw [hsp]; ring
    exact eq_tsub_of_add_eq hsub_add
  have hq1_len : ([heap + K + 6 * K, S_2K, 2 * K, heap + K + 6 * K + 2 * K] : List ℕ).getD 2 0 =
      2 * K := rfl
  have hz4' : ZeroFrom mem4 div1Out := hhp4_val ▸ hz4
  rw [hq1_addr, hq1_len] at hv_q1
  rw [hq1_addr] at hint_q1
  clear hfr4 hz4 hhp4
  have hmult_val_eq : (nlCnt * Num.unsignedVal mem (wtPtr + e * L) h L + S_val - 1) / S_val ≤ nlCnt := by
    have hmul : nlCnt * Num.unsignedVal mem (wtPtr + e * L) h L + S_val - 1 ≤ S_val * nlCnt + (S_val - 1) := by
      have h1 := Nat.sub_le_sub_right (Nat.add_le_add_right (Nat.mul_le_mul_left nlCnt hvleS) S_val) 1
      rw [Nat.mul_comm nlCnt S_val] at h1
      have hsub : S_val * nlCnt + S_val - 1 = S_val * nlCnt + (S_val - 1) := by
        have := hS1; exact Nat.add_sub_assoc hS1 (S_val * nlCnt)
      exact hsub ▸ h1
    exact (Nat.div_le_iff_le_mul_add_pred hS1).mpr hmul
  have hmult_lt_cap : 2 * ((nlCnt * Num.unsignedVal mem (wtPtr + e * L) h L + S_val - 1) / S_val) <
      Num.capacity h K :=
    lt_of_le_of_lt (Nat.mul_le_mul_left 2 hmult_val_eq) hnl_cap
  have hq1_int_eq : Num.intVal mem4 (div1Out - 2 * K) h (2 * K) =
      (((nlCnt * Num.unsignedVal mem (wtPtr + e * L) h L + S_val - 1) / S_val : ℕ) : ℤ) := by
    change Num.intVal mem4 (div1Out - 2 * K) h (2 * K) =
      Num.wrap h (2 * K) (Num.floorDiv (Num.intVal mem3 (heap + K + 6 * K) h (2 * K))
        (Num.intVal mem3 S_2K h (2 * K))) at hint_q1
    rw [hint_q1, hnum1_prop.2, hv_S3.2]
    have hfl : Num.floorDiv ((nlCnt * Num.unsignedVal mem (wtPtr + e * L) h L + S_val - 1 : ℕ) : ℤ)
        (S_val : ℤ) =
        (((nlCnt * Num.unsignedVal mem (wtPtr + e * L) h L + S_val - 1) / S_val : ℕ) : ℤ) := by
      simp [Num.floorDiv]
    rw [hfl, Num.wrap_of_fits (fits_of_lt_half_cap (lt_trans hmult_lt_cap hlt_K2))]
  have hq1_nat_eq : Num.unsignedVal mem4 (div1Out - 2 * K) h (2 * K) =
      (nlCnt * Num.unsignedVal mem (wtPtr + e * L) h L + S_val - 1) / S_val := by
    have hpos_num : S_val ≤ nlCnt * Num.unsignedVal mem (wtPtr + e * L) h L + S_val - 1 :=
      Nat.le_sub_one_of_lt (Nat.lt_add_of_pos_left (Nat.mul_pos hnl1 hv_nat.2.2))
    have := intVal_eq_nat_of_pos hv_q1 (by
      rw [hq1_int_eq]; exact_mod_cast Nat.div_pos hpos_num hS1)
    exact Int.ofNat.inj (this.1.symm.trans hq1_int_eq)
  have hq1_pref := unsignedVal_prefix_eq (K := K) (M := K) (by simpa [two_mul] using hv_q1)
    (by rw [show K + K = 2 * K by ring, hq1_nat_eq]
        exact lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by decide)) hmult_lt_cap)
  rw [show K + K = 2 * K by ring] at hq1_pref
  have hmult_w : Num.unsignedVal mem4 (div1Out - 2 * K) h K < 2 ^ w := by
    rw [hq1_pref.2, hq1_nat_eq]
    exact lt_of_le_of_lt hmult_val_eq hnl_w
  have hws6 := wsRegs_upd hws5 hr6 (by decide)
  have hr15_6 : st6.regs 15 = div1Out := by rw [hr6, hhp4_val, Function.update_self]
  -- 5. r17 := div1Out - 2*K; packWord q1 K -> store to outMultAddr
  refine runs_seq_assign_step (Expr.eval_sub (Expr.eval_reg_of_eq hr15_6)
    (Expr.eval_reg_of_eq hws6.r13) hdiv1_w) rfl fun st7 hm7 _ hr7 => ?_
  have hws7 := wsRegs_upd hws6 hr7 (by decide)
  have hr15_7 : st7.regs 15 = div1Out := by rw [hr7, Function.update_of_ne (by decide), hr15_6]
  have hr17_7 : st7.regs 17 = div1Out - 2 * K := by rw [hr7, Function.update_self]
  have hmem7_eq : st7.mem = mem4 := hm7.trans hm6
  refine runs_seq_call_step hpk_mc (vs := [div1Out - 2 * K, K])
    (evalArgs_cons (Expr.eval_reg_of_eq hr17_7)
      (evalArgs_cons (Expr.eval_reg_of_eq hws7.r4) (evalArgs_nil _ _)))
    (fun x hx => by simp at hx; rcases hx with rfl | rfl <;> assumption)
    (hmem7_eq ▸ ⟨div1Out - 2 * K, K, rfl, hdiv1_mK_w, hq1_pref.1, hmult_w⟩)
    rfl (rfl : _ = 25 * K + 6)
    fun ret_m mem4' st8 hpost4' hm8 hr8 => ?_
  rw [hmem7_eq] at hpost4'
  obtain ⟨hm4_eq, hret_m⟩ := hpost4'
  have hm_eq : ret_m = (nlCnt * Num.unsignedVal mem (wtPtr + e * L) h L + S_val - 1) / S_val := by
    change ret_m = Num.unsignedVal mem4 (div1Out - 2 * K) h K at hret_m
    rw [hret_m, hq1_pref.2, hq1_nat_eq]
  have hws8 := wsRegs_upd hws7 hr8 (by decide)
  have hr15_8 : st8.regs 15 = div1Out := by rw [hr8, Function.update_of_ne (by decide), hr15_7]
  have hr16_8 : st8.regs 16 = ret_m := by rw [hr8, Function.update_self]
  refine runs_seq_store_step (Expr.eval_reg_of_eq hws8.r10) (Expr.eval_reg_of_eq hr16_8)
    rfl fun st9 hm9 hr9 _ => ?_
  rw [hm8, hm4_eq] at hm9
  let mem5 := Function.update mem4 outMultAddr ret_m
  have hmem9_eq : st9.mem = mem5 := hm9
  have hfr5 : ∀ a, a ≠ outMultAddr → mem5 a = mem4 a := fun a ha => Function.update_of_ne ha _ _
  have hz5 : ZeroFrom mem5 div1Out := fun a ha => by
    rw [hfr5 a (Nat.ne_of_gt (lt_of_lt_of_le hom_h (le_trans (Nat.le_add_right _ _) (le_trans hheap_le_div1 ha))))]
    exact hz4' a ha
  have hws9 := wsRegs_sameRegs hws8 hr9
  have hr15_9 : st9.regs 15 = heap + 9 * K + Num.integerDivideSpace (2 * K) := by
    rw [hr9]; exact hr15_8
  have hpres5 : ∀ a < heap, a ≠ outMultAddr → st9.mem a = mem a := fun a ha hne => by
    have hlt1 : a < heap + K := lt_of_lt_of_le ha (Nat.le_add_right _ _)
    have hlt2 : a < heap + K + 6 * K := lt_of_lt_of_le hlt1 (Nat.le_add_right _ _)
    have hlt3 : a < heap + K + 6 * K + 2 * K := lt_of_lt_of_le hlt2 (Nat.le_add_right _ _)
    rw [hmem9_eq, hfr5 a hne, hfr4' a hlt3, hfr3' a hlt2, hfr2' a hlt1, hfr1' a ha]
  have hmult_mem5 : st9.mem outMultAddr =
      (nlCnt * Num.unsignedVal mem (wtPtr + e * L) h L + S_val - 1) / S_val := by
    rw [hmem9_eq]; dsimp only [mem5]; rw [Function.update_self, hm_eq]
  obtain ⟨o, st'', c_tail, hrun_tail, hpost_tail, hc_tail⟩ :=
    weightStep_tail_runs (nlCnt := nlCnt) (Vcnt := Vcnt) (S_val := S_val) (lmin_val := lmin_val)
      hcopy_mc hse_mc hml_mc hdv_mc
      hh hw hL1 hLK hV2 hvlen hplen hin hv2v hi2v hiS hvlm hilm hlm1 hlm_le hw_cap
      hlen_h h2V_h hlm_h hom_h how_h homw_disj homl_disj hom2V_disj homlm_disj hbound
      hws9 hr15_9 (hmem9_eq ▸ hz5) hpres5 hmult_mem5
  refine ⟨o, st'', c_tail, hrun_tail, hpost_tail, ?_⟩
  have hsum_le := weightStep_phase1_le K
  have hc_out : (weightStepContract w h).cost
      [e, lenPtr, wtPtr, L, K, nlCnt_K, twoV_K, S_2K, S_m1_2K, lmin_2K, outMultAddr, outWAddr, heap] mem =
      2800 * K * K + 4200 * K + 1800 := rfl
  rw [hc_out]
  exact le_trans (Nat.add_le_add hsum_le hc_tail) (le_of_eq (by ring))

end MinCostFlow.WideWord
