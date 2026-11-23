module

public import MinCostFlow.Machine.WideWord.LSSTWeightsPhaseA
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Phase B of Theorem 2.2 weight computation

This module verifies Phase B of `weightsProc`: sign-extending `ℓ_min`, summing non-loop weights
via `sumWeightsProc`, subtracting `1`, and sign-extending `S` and `S - 1` into `2K`-limb operands.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM MinCostFlow

private structure BBaseRegs (s : State) (nlCnt nlPtr lenPtr wtPtr Vcnt L
    outMultPtr outWPtr outKPtr K nlCnt_K twoV_K : ℕ) : Prop where
  r0 : s.regs 0 = nlCnt
  r1 : s.regs 1 = nlPtr
  r2 : s.regs 2 = lenPtr
  r3 : s.regs 3 = wtPtr
  r4 : s.regs 4 = Vcnt
  r5 : s.regs 5 = L
  r6 : s.regs 6 = outMultPtr
  r7 : s.regs 7 = outWPtr
  r8 : s.regs 8 = outKPtr
  r11 : s.regs 11 = K
  r13 : s.regs 13 = 2 * K
  r14 : s.regs 14 = twoV_K
  r15 : s.regs 15 = nlCnt_K

private lemma bBaseRegs_upd {s s' : State} {nlCnt nlPtr lenPtr wtPtr Vcnt L
    outMultPtr outWPtr outKPtr K nlCnt_K twoV_K r v : ℕ}
    (h : BBaseRegs s nlCnt nlPtr lenPtr wtPtr Vcnt L outMultPtr outWPtr outKPtr K nlCnt_K twoV_K)
    (hreg : s'.regs = Function.update s.regs r v)
    (hr : r ∈ ([17, 18, 19, 20, 21, 22, 23] : List ℕ)) :
    BBaseRegs s' nlCnt nlPtr lenPtr wtPtr Vcnt L outMultPtr outWPtr outKPtr K nlCnt_K twoV_K := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  exact ⟨by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r0,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r1,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r2,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r3,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r4,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r5,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r6,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r7,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r8,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r11,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r13,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r14,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r15⟩

private theorem weights_phaseB1_runs {w b h : ℕ} {p : Program} {ω : ℕ → Bool}
    {Q_w : Outcome → (ℕ → ℕ) → Prop}
    {st' : State} {mem : ℕ → ℕ} {G : IndexedGraph} {vNat lNat : ℕ → ℕ}
    {nlPtr lenPtr wtPtr L outMultPtr outWPtr outKPtr heap minIdx target : ℕ}
    (hp : p.HasAt b (weightsModule b h))
    (hh : 0 < h) (hw : 3 * h + 2 ≤ w) (hL1 : 1 ≤ L) (hne : 1 ≤ (nonloopEdges G).length)
    (hmin_lt : minIdx < (nonloopEdges G).length)
    (hnl_list : ListAt mem nlPtr (nonloopEdges G))
    (hnl_h : nlPtr + (nonloopEdges G).length ≤ heap)
    (hoK_h : outKPtr < heap)
    (hlen_mem : ∀ e < G.m, Num.Valid mem (lenPtr + e * L) h L ∧
      Num.intVal mem (lenPtr + e * L) h L = (lNat e : ℤ) ∧ 1 ≤ lNat e)
    (hwt_mem : ∀ e < G.m, Num.Valid mem (wtPtr + e * L) h L ∧
      Num.intVal mem (wtPtr + e * L) h L = (vNat e : ℤ) ∧ 1 ≤ vNat e)
    (hlen_h : lenPtr + G.m * L ≤ heap) (hwt_h : wtPtr + G.m * L ≤ heap)
    (hG_edges : ∀ e ∈ nonloopEdges G, e < G.m)
    (hdisj_K_nl : DisjointRanges outKPtr 1 nlPtr (nonloopEdges G).length)
    (hdisj_K_len : DisjointRanges outKPtr 1 lenPtr (G.m * L))
    (hdisj_K_wt : DisjointRanges outKPtr 1 wtPtr (G.m * L))
    (hbound : heap + weightsSpace (nonloopEdges G).length (kWidthOf (nonloopEdges G).length L) < 2 ^ w)
    (hS_cap : 2 * ((nonloopEdges G).map vNat).sum < Num.capacity h (kWidthOf (nonloopEdges G).length L))
    (hr0 : st'.regs 0 = (nonloopEdges G).length) (hr1 : st'.regs 1 = nlPtr)
    (hr2 : st'.regs 2 = lenPtr) (hr3 : st'.regs 3 = wtPtr)
    (hr4 : st'.regs 4 = (activeVertsList G).length) (hr5 : st'.regs 5 = L)
    (hr6 : st'.regs 6 = outMultPtr) (hr7 : st'.regs 7 = outWPtr) (hr8 : st'.regs 8 = outKPtr)
    (hr11 : st'.regs 11 = kWidthOf (nonloopEdges G).length L) (hr12 : st'.regs 12 = minIdx)
    (hr13 : st'.regs 13 = 2 * kWidthOf (nonloopEdges G).length L)
    (hr14 : st'.regs 14 = heap) (hr15 : st'.regs 15 = heap + kWidthOf (nonloopEdges G).length L)
    (hr16 : st'.regs 16 = heap + 2 * kWidthOf (nonloopEdges G).length L)
    (hr19 : st'.regs 19 = heap + 3 * kWidthOf (nonloopEdges G).length L)
    (hpres : ∀ a < heap, a ≠ outKPtr → st'.mem a = mem a)
    (hz3 : ZeroFrom st'.mem (heap + 3 * kWidthOf (nonloopEdges G).length L))
    (hrest : Stmt) :
    let nl := nonloopEdges G
    let K := kWidthOf nl.length L
    let hp_sum := heap + 7 * K + nl.length * (2 * K)
    let S_val := (nl.map vNat).sum
    let lmin_val := lNat (nl[minIdx]'hmin_lt)
    (∀ st7 : State,
      BBaseRegs st7 nl.length nlPtr lenPtr wtPtr (activeVertsList G).length L
        outMultPtr outWPtr outKPtr K (heap + K) heap →
      st7.regs 16 = heap + 2 * K →
      st7.regs 17 = heap + 4 * K →
      st7.regs 19 = hp_sum →
      (∀ a < heap + 3 * K, st7.mem a = st'.mem a) →
      ZeroFrom st7.mem hp_sum →
      (Num.Valid st7.mem (heap + 4 * K) h (2 * K) ∧
        Num.intVal st7.mem (heap + 4 * K) h (2 * K) = (lmin_val : ℤ)) →
      (Num.Valid st7.mem (hp_sum - K) h K ∧
        Num.intVal st7.mem (hp_sum - K) h K = (S_val : ℤ)) →
      ∃ o st'' c, Runs w p ω hrest st7 o st'' c ∧
        Q_w o st''.mem ∧
        c ≤ target) →
    ∃ o st'' c, Runs w p ω
      (.assign 20 (.bin .add (.reg 2) (.bin .mul (.load (.bin .add (.reg 1) (.reg 12))) (.reg 5))) ;;
       .call 21 (b + idxWSignExtend) [.reg 20, .reg 5, .reg 11, .reg 19] ;;
       .assign 20 (.reg 19) ;;
       .assign 19 (.reg 21) ;;
       .call 21 (b + idxWSignExtend) [.reg 20, .reg 11, .reg 13, .reg 19] ;;
       .assign 17 (.reg 19) ;;
       .assign 19 (.reg 21) ;;
       .call 19 (b + idxSumWeights) [.reg 0, .reg 1, .reg 3, .reg 5, .reg 11, .reg 19] ;;
       hrest)
      st' o st'' c ∧
      Q_w o st''.mem ∧
      c ≤ (30 * K + 42) + (30 * (2 * K) + 42) +
        (nl.length * (70 * K + 120) + 25 * K + 50) + 42 + target := by
  intro nl K hp_sum S_val lmin_val hcont
  have hsub := weights_hasAt_sub hp
  have hsum_mc := sumWeights_meetsContract (w := w) (h := h) hp
  have hbh : Num.base h < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hw1 : 1 < 2 ^ w := lt_of_le_of_lt
    (by simpa [Num.base] using Nat.one_le_two_pow (n := h)) hbh
  have hw2 : 2 * h + 2 ≤ w := by omega
  have hse_mc := Num.signExtend_meetsContract hh hw1 hbh hsub.2.2.2.1
  have hLK : L ≤ K := by dsimp only [K, kWidthOf]; omega
  have hK1 : 1 ≤ K := by dsimp only [K, kWidthOf]; omega
  have hnl_h' : nlPtr + nl.length ≤ heap := hnl_h
  have hdisj_K_nl' : DisjointRanges outKPtr 1 nlPtr nl.length := hdisj_K_nl
  have hbound' : heap + weightsSpace nl.length K < 2 ^ w := hbound
  have hws_lb : 13 * K + nl.length * (2 * K) ≤ weightsSpace nl.length K := by
    dsimp only [weightsSpace]
    have h2 : nl.length * (2 * K) ≤ nl.length * (18 * K + 2 * Num.integerDivideSpace (2 * K)) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  have hsum_w : hp_sum < 2 ^ w := by dsimp only [hp_sum]; omega
  have hheap_w : heap < 2 ^ w := by omega
  have hhp4_w : heap + 4 * K < 2 ^ w := by omega
  have hhp6_w : heap + 6 * K < 2 ^ w := by omega
  have hnl_w : nl.length < 2 ^ w := by
    have : nl.length ≤ nlPtr + nl.length := Nat.le_add_left _ _
    omega
  have hnlPtr_w : nlPtr < 2 ^ w := by
    have : nlPtr ≤ nlPtr + nl.length := Nat.le_add_right _ _
    omega
  have hwtPtr_w : wtPtr < 2 ^ w := by
    have : wtPtr ≤ wtPtr + G.m * L := Nat.le_add_right _ _
    omega
  have hL_w : L < 2 ^ w := by omega
  have hK_w : K < 2 ^ w := by omega
  have h2K_w : 2 * K < 2 ^ w := by omega
  have h3K_w : heap + 3 * K < 2 ^ w := by omega
  have hoK_lt_3K : outKPtr < heap + 3 * K := by omega
  have hmin_e : nl[minIdx]'hmin_lt < G.m := hG_edges _ (List.getElem_mem hmin_lt)
  have hmem_nl : ∀ (j : ℕ) (hj : j < nl.length), st'.mem (nlPtr + j) = nl[j]'hj := fun j hj => by
    have hne_K : nlPtr + j ≠ outKPtr := by
      dsimp only [DisjointRanges] at hdisj_K_nl'
      rcases hdisj_K_nl' with h1 | h1 <;> omega
    have hlt_h : nlPtr + j < heap := by
      have : j + 1 ≤ nl.length := hj
      linarith only [this, hnl_h']
    rw [hpres _ hlt_h hne_K, hnl_list j hj]
  have he_min_mem : st'.mem (nlPtr + minIdx) = nl[minIdx]'hmin_lt := hmem_nl minIdx hmin_lt
  have hmin_add_w : nlPtr + minIdx < 2 ^ w := by
    have : minIdx < nl.length := hmin_lt
    linarith only [this, hnl_h', hheap_w]
  have hmin_mul_w : (nl[minIdx]'hmin_lt) * L < 2 ^ w := by
    have : (nl[minIdx]'hmin_lt) * L ≤ G.m * L := Nat.mul_le_mul_right L (Nat.le_of_lt hmin_e)
    linarith only [this, hlen_h, hheap_w]
  have hmin_mul_end : (nl[minIdx]'hmin_lt) * L + L ≤ G.m * L := by
    have h1 : ((nl[minIdx]'hmin_lt) + 1) * L ≤ G.m * L := Nat.mul_le_mul_right L hmin_e
    rwa [Nat.add_mul, Nat.one_mul] at h1
  have hmin_addr_w : lenPtr + (nl[minIdx]'hmin_lt) * L < 2 ^ w := by
    linarith only [hmin_mul_end, hL1, hlen_h, hheap_w]
  have hmin_addr_h : lenPtr + (nl[minIdx]'hmin_lt) * L + L ≤ heap + 3 * K := by
    linarith only [hmin_mul_end, hlen_h, hK1]
  have hmin_len_valid : Num.Valid st'.mem (lenPtr + (nl[minIdx]'hmin_lt) * L) h L ∧
      Num.intVal st'.mem (lenPtr + (nl[minIdx]'hmin_lt) * L) h L = (lmin_val : ℤ) := by
    have heq : ∀ i < L, st'.mem (lenPtr + (nl[minIdx]'hmin_lt) * L + i) = mem (lenPtr + (nl[minIdx]'hmin_lt) * L + i) := by
      intro i hi
      have hne_K : lenPtr + (nl[minIdx]'hmin_lt) * L + i ≠ outKPtr := by
        dsimp only [DisjointRanges] at hdisj_K_len
        rcases hdisj_K_len with h1 | h1 <;> omega
      exact hpres _ (by linarith only [hi, hmin_mul_end, hlen_h]) hne_K
    have horig := hlen_mem _ hmin_e
    exact ⟨numValid_congr (fun i hi => (heq i hi).symm) horig.1, by rw [intVal_congr_range heq, horig.2.1]⟩
  have hb_init : BBaseRegs st' nl.length nlPtr lenPtr wtPtr (activeVertsList G).length L
      outMultPtr outWPtr outKPtr K (heap + K) heap :=
    ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr11, hr13, hr14, hr15⟩
  refine runs_start_le ?_
  refine runs_seq_assign_step (Expr.eval_add (Expr.eval_reg_of_eq hr2)
    (Expr.eval_mul (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr1)
      (Expr.eval_reg_of_eq hr12) hmin_add_w) he_min_mem)
      (Expr.eval_reg_of_eq hr5) hmin_mul_w) hmin_addr_w) rfl fun st0 hm0 _ hr0' => ?_
  have hb0 := bBaseRegs_upd hb_init hr0' (by decide)
  have hr0_16 : st0.regs 16 = heap + 2 * K := by rw [hr0', Function.update_of_ne (by decide), hr16]
  have hr0_19 : st0.regs 19 = heap + 3 * K := by rw [hr0', Function.update_of_ne (by decide), hr19]
  have hr0_20 : st0.regs 20 = lenPtr + (nl[minIdx]'hmin_lt) * L := by rw [hr0', Function.update_self]
  have hpre1 : (Num.signExtendContract w h).pre
      [lenPtr + (nl[minIdx]'hmin_lt) * L, L, K, heap + 3 * K] st0.mem := by
    rw [hm0]
    exact ⟨⟨lenPtr + (nl[minIdx]'hmin_lt) * L, L, K, heap + 3 * K, rfl, hLK, hmin_addr_h, hmin_len_valid.1⟩,
      hz3, (by change (heap + 3 * K) + K < 2 ^ w; linarith only [hhp4_w])⟩
  refine runs_seq_call_step hse_mc (vs := [lenPtr + (nl[minIdx]'hmin_lt) * L, L, K, heap + 3 * K])
    (evalArgs_cons (Expr.eval_reg_of_eq hr0_20)
      (evalArgs_cons (Expr.eval_reg_of_eq hb0.r5)
        (evalArgs_cons (Expr.eval_reg_of_eq hb0.r11)
          (evalArgs_cons (Expr.eval_reg_of_eq hr0_19) (evalArgs_nil _ _)))))
    (fun x hx => by
      simp at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hmin_addr_w
      · exact hL_w
      · exact hK_w
      · exact h3K_w)
    hpre1 rfl (rfl : _ = 30 * K + 42)
    fun hp1 mem1 st1 hpost1 hm1 hr1' => ?_
  rw [hm0] at hpost1
  obtain ⟨hhp1, _, _, hfr1, hz1, hv_lmK, hi_lmK⟩ := hpost1
  change ∀ x < heap + 3 * K, mem1 x = st'.mem x at hfr1
  change Num.intVal mem1 (heap + 3 * K) h K = Num.intVal st'.mem (lenPtr + (nl[minIdx]'hmin_lt) * L) h L at hi_lmK
  have hhp1_val : hp1 = heap + 4 * K := by
    have ha : heapArg [lenPtr + (nl[minIdx]'hmin_lt) * L, L, K, heap + 3 * K] = heap + 3 * K := rfl
    have hg : ([lenPtr + (nl[minIdx]'hmin_lt) * L, L, K, heap + 3 * K] : List ℕ).getD 2 0 = K := rfl
    rw [ha, hg] at hhp1; rw [hhp1]; ring
  have hz1' : ZeroFrom mem1 (heap + 4 * K) := hhp1_val ▸ hz1
  have hb1 := bBaseRegs_upd hb0 hr1' (by decide)
  have hr1_16 : st1.regs 16 = heap + 2 * K := by rw [hr1', Function.update_of_ne (by decide), hr0_16]
  have hr1_19 : st1.regs 19 = heap + 3 * K := by rw [hr1', Function.update_of_ne (by decide), hr0_19]
  have hr1_21 : st1.regs 21 = heap + 4 * K := by rw [hr1', hhp1_val, Function.update_self]
  refine runs_seq_assign_step (Expr.eval_reg_of_eq hr1_19) rfl fun st2 hm2 _ hr2' => ?_
  have hb2 := bBaseRegs_upd hb1 hr2' (by decide)
  have hr2_16 : st2.regs 16 = heap + 2 * K := by rw [hr2', Function.update_of_ne (by decide), hr1_16]
  have hr2_19 : st2.regs 19 = heap + 3 * K := by rw [hr2', Function.update_of_ne (by decide), hr1_19]
  have hr2_20 : st2.regs 20 = heap + 3 * K := by rw [hr2', Function.update_self]
  have hr2_21 : st2.regs 21 = heap + 4 * K := by rw [hr2', Function.update_of_ne (by decide), hr1_21]
  refine runs_seq_assign_step (Expr.eval_reg_of_eq hr2_21) rfl fun st3 hm3 _ hr3' => ?_
  have hst3_mem : st3.mem = mem1 := hm3.trans (hm2.trans hm1)
  have hb3 := bBaseRegs_upd hb2 hr3' (by decide)
  have hr3_16 : st3.regs 16 = heap + 2 * K := by rw [hr3', Function.update_of_ne (by decide), hr2_16]
  have hr3_19 : st3.regs 19 = heap + 4 * K := by rw [hr3', Function.update_self]
  have hr3_20 : st3.regs 20 = heap + 3 * K := by rw [hr3', Function.update_of_ne (by decide), hr2_20]
  have hpre2 : (Num.signExtendContract w h).pre [heap + 3 * K, K, 2 * K, heap + 4 * K] st3.mem := by
    rw [hst3_mem]
    refine ⟨⟨heap + 3 * K, K, 2 * K, heap + 4 * K, rfl, by linarith only [hK1], by linarith only [hK1], hv_lmK⟩, hz1', ?_⟩
    change (heap + 4 * K) + 2 * K < 2 ^ w; linarith only [hhp6_w]
  refine runs_seq_call_step hse_mc (vs := [heap + 3 * K, K, 2 * K, heap + 4 * K])
    (evalArgs_cons (Expr.eval_reg_of_eq hr3_20)
      (evalArgs_cons (Expr.eval_reg_of_eq hb3.r11)
        (evalArgs_cons (Expr.eval_reg_of_eq hb3.r13)
          (evalArgs_cons (Expr.eval_reg_of_eq hr3_19) (evalArgs_nil _ _)))))
    (fun x hx => by
      simp at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact h3K_w
      · exact hK_w
      · exact h2K_w
      · exact hhp4_w)
    hpre2 rfl (rfl : _ = 30 * (2 * K) + 42)
    fun hp2 mem2 st4 hpost2 hm4 hr4' => ?_
  rw [hst3_mem] at hpost2
  obtain ⟨hhp2, _, _, hfr2, hz2, hv_lm2K, hi_lm2K⟩ := hpost2
  change ∀ x < heap + 4 * K, mem2 x = mem1 x at hfr2
  change Num.intVal mem2 (heap + 4 * K) h (2 * K) = Num.intVal mem1 (heap + 3 * K) h K at hi_lm2K
  have hhp2_val : hp2 = heap + 6 * K := by
    have ha : heapArg [heap + 3 * K, K, 2 * K, heap + 4 * K] = heap + 4 * K := rfl
    have hg : ([heap + 3 * K, K, 2 * K, heap + 4 * K] : List ℕ).getD 2 0 = 2 * K := rfl
    rw [ha, hg] at hhp2; rw [hhp2]; ring
  have hz2' : ZeroFrom mem2 (heap + 6 * K) := hhp2_val ▸ hz2
  have hi_lm2K_eq : Num.intVal mem2 (heap + 4 * K) h (2 * K) = (lmin_val : ℤ) := by
    rw [hi_lm2K, hi_lmK, hmin_len_valid.2]
  have hb4 := bBaseRegs_upd hb3 hr4' (by decide)
  have hr4_16 : st4.regs 16 = heap + 2 * K := by rw [hr4', Function.update_of_ne (by decide), hr3_16]
  have hr4_19 : st4.regs 19 = heap + 4 * K := by rw [hr4', Function.update_of_ne (by decide), hr3_19]
  have hr4_21 : st4.regs 21 = heap + 6 * K := by rw [hr4', hhp2_val, Function.update_self]
  refine runs_seq_assign_step (Expr.eval_reg_of_eq hr4_19) rfl fun st5 hm5 _ hr5' => ?_
  have hb5 := bBaseRegs_upd hb4 hr5' (by decide)
  have hr5_16 : st5.regs 16 = heap + 2 * K := by rw [hr5', Function.update_of_ne (by decide), hr4_16]
  have hr5_17 : st5.regs 17 = heap + 4 * K := by rw [hr5', Function.update_self]
  have hr5_21 : st5.regs 21 = heap + 6 * K := by rw [hr5', Function.update_of_ne (by decide), hr4_21]
  refine runs_seq_assign_step (Expr.eval_reg_of_eq hr5_21) rfl fun st6 hm6 _ hr6' => ?_
  have hst6_mem : st6.mem = mem2 := hm6.trans (hm5.trans hm4)
  have hb6 := bBaseRegs_upd hb5 hr6' (by decide)
  have hr6_16 : st6.regs 16 = heap + 2 * K := by rw [hr6', Function.update_of_ne (by decide), hr5_16]
  have hr6_17 : st6.regs 17 = heap + 4 * K := by rw [hr6', Function.update_of_ne (by decide), hr5_17]
  have hr6_19 : st6.regs 19 = heap + 6 * K := by rw [hr6', Function.update_self]
  have hm2_pres : ∀ a < heap + 3 * K, mem2 a = st'.mem a := fun a ha => by
    rw [hfr2 a (by linarith only [ha, hK1]), hfr1 a ha]
  have hm2_nl : ∀ (j : ℕ) (hj : j < nl.length), mem2 (nlPtr + j) = nl[j]'hj := fun j hj => by
    have hj_h : nlPtr + j < heap + 3 * K := by
      have : j + 1 ≤ nl.length := hj
      linarith only [this, hnl_h', hK1]
    rw [hm2_pres _ hj_h, hmem_nl j hj]
  have hm2_wt_mem : ∀ j (hj : j < nl.length),
      wtPtr + mem2 (nlPtr + j) * L + L ≤ heap + 6 * K ∧
      Num.Valid mem2 (wtPtr + mem2 (nlPtr + j) * L) h L ∧
      0 < Num.intVal mem2 (wtPtr + mem2 (nlPtr + j) * L) h L := by
    intro j hj
    rw [hm2_nl j hj]
    have he_m := hG_edges _ (List.getElem_mem hj)
    have hmul : ((nl[j]'hj) + 1) * L ≤ G.m * L := Nat.mul_le_mul_right L he_m
    rw [Nat.add_mul, Nat.one_mul] at hmul
    have heq : ∀ i < L, mem2 (wtPtr + (nl[j]'hj) * L + i) = mem (wtPtr + (nl[j]'hj) * L + i) := by
      intro i hi
      have hne_K : wtPtr + (nl[j]'hj) * L + i ≠ outKPtr := by
        dsimp only [DisjointRanges] at hdisj_K_wt
        rcases hdisj_K_wt with h1 | h1 <;> omega
      have hlt_h : wtPtr + (nl[j]'hj) * L + i < heap := by linarith only [hi, hmul, hwt_h]
      rw [hm2_pres _ (by linarith only [hlt_h, hK1]), hpres _ hlt_h hne_K]
    have hw0 := hwt_mem _ he_m
    refine ⟨by linarith only [hmul, hwt_h, hK1], numValid_congr (fun i hi => (heq i hi).symm) hw0.1, ?_⟩
    rw [intVal_congr_range heq, hw0.2.1]; exact_mod_cast hw0.2.2
  have hS_list_eq : ((List.range nl.length).map fun j =>
      Num.unsignedVal mem2 (wtPtr + mem2 (nlPtr + j) * L) h L).sum = S_val := by
    dsimp only [S_val]
    congr 1
    refine List.ext_getElem (by simp) fun j hj1 hj2 => ?_
    have hj : j < nl.length := by simpa using hj1
    simp only [List.getElem_map, List.getElem_range]
    rw [hm2_nl j hj]
    have he_m := hG_edges _ (List.getElem_mem hj)
    have hmul : ((nl[j]'hj) + 1) * L ≤ G.m * L := Nat.mul_le_mul_right L he_m
    rw [Nat.add_mul, Nat.one_mul] at hmul
    have heq : ∀ i < L, mem2 (wtPtr + (nl[j]'hj) * L + i) = mem (wtPtr + (nl[j]'hj) * L + i) := by
      intro i hi
      have hne_K : wtPtr + (nl[j]'hj) * L + i ≠ outKPtr := by
        dsimp only [DisjointRanges] at hdisj_K_wt
        rcases hdisj_K_wt with h1 | h1 <;> omega
      have hlt_h : wtPtr + (nl[j]'hj) * L + i < heap := by linarith only [hi, hmul, hwt_h]
      rw [hm2_pres _ (by linarith only [hlt_h, hK1]), hpres _ hlt_h hne_K]
    rw [unsignedVal_congr_range heq]
    have hw0 := hwt_mem _ he_m
    have hpos := intVal_eq_nat_of_pos hw0.1 (by rw [hw0.2.1]; exact_mod_cast hw0.2.2)
    have hcast : ((Num.unsignedVal mem (wtPtr + (nl[j]'hj) * L) h L : ℕ) : ℤ) = (vNat (nl[j]'hj) : ℤ) := by
      rw [← hpos.1, hw0.2.1]
    exact Int.ofNat.inj hcast
  have hpre3 : (sumWeightsContract w h).pre [nl.length, nlPtr, wtPtr, L, K, heap + 6 * K] st6.mem := by
    rw [hst6_mem]
    refine ⟨nl.length, nlPtr, wtPtr, L, K, heap + 6 * K, rfl, hne, hL1, hh, hw2, rfl,
      by linarith only [hnl_h', hK1], hm2_wt_mem, hz2', ?_⟩
    dsimp only [hp_sum] at hsum_w
    linarith only [hsum_w]
  refine runs_seq_call_step hsum_mc (vs := [nl.length, nlPtr, wtPtr, L, K, heap + 6 * K])
    (evalArgs_cons (Expr.eval_reg_of_eq hb6.r0)
      (evalArgs_cons (Expr.eval_reg_of_eq hb6.r1)
        (evalArgs_cons (Expr.eval_reg_of_eq hb6.r3)
          (evalArgs_cons (Expr.eval_reg_of_eq hb6.r5)
            (evalArgs_cons (Expr.eval_reg_of_eq hb6.r11)
              (evalArgs_cons (Expr.eval_reg_of_eq hr6_19) (evalArgs_nil _ _)))))))
    (fun x hx => by
      simp at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hnl_w
      · exact hnlPtr_w
      · exact hwtPtr_w
      · exact hL_w
      · exact hK_w
      · exact hhp6_w)
    hpre3 rfl (rfl : _ = nl.length * (70 * K + 120) + 25 * K + 50)
    fun hp3 mem3 st7 hpost3 hm7 hr7' => ?_
  rw [hst6_mem] at hpost3
  obtain ⟨nlCnt3, nlPtr3, wtPtr3, L3, K3, hp3_in, hsum_eqs, hhp3_val, hz3', hfr3, hv_S3, hi_S3, hu_S3, _⟩ := hpost3
  simp only [List.cons.injEq, and_true] at hsum_eqs
  obtain ⟨rfl, rfl, rfl, rfl, rfl, hhp3_in⟩ := hsum_eqs
  rw [← hhp3_in] at hhp3_val hfr3
  have hp3_eq : hp3 = hp_sum := by rw [hhp3_val]; dsimp only [hp_sum]; ring
  rw [hp3_eq] at hz3' hv_S3 hi_S3 hu_S3
  rw [hS_list_eq] at hi_S3 hu_S3
  have hb7 := bBaseRegs_upd hb6 hr7' (by decide)
  have hr7_16 : st7.regs 16 = heap + 2 * K := by rw [hr7', Function.update_of_ne (by decide), hr6_16]
  have hr7_17 : st7.regs 17 = heap + 4 * K := by rw [hr7', Function.update_of_ne (by decide), hr6_17]
  have hr7_19 : st7.regs 19 = hp_sum := by rw [hr7', hp3_eq, Function.update_self]
  have hmem3_eq3 : ∀ a < heap + 3 * K, mem3 a = st'.mem a := fun a ha => by
    rw [hfr3 _ (by linarith only [ha, hK1]), hm2_pres _ ha]
  have hv_lm2K3 : Num.Valid mem3 (heap + 4 * K) h (2 * K) ∧
      Num.intVal mem3 (heap + 4 * K) h (2 * K) = (lmin_val : ℤ) := by
    have heq : ∀ i < 2 * K, mem3 (heap + 4 * K + i) = mem2 (heap + 4 * K + i) := fun i hi =>
      hfr3 _ (by linarith only [hi])
    exact ⟨numValid_congr (fun i hi => (heq i hi).symm) hv_lm2K, by rw [intVal_congr_range heq, hi_lm2K_eq]⟩
  obtain ⟨o, st'', c_rest, hrun_rest, hpost_rest, hc_rest⟩ :=
    hcont st7 hb7 hr7_16 hr7_17 hr7_19 (fun a ha => by rw [hm7]; exact hmem3_eq3 a ha)
      (hm7 ▸ hz3')
      ⟨hm7 ▸ hv_lm2K3.1, hm7 ▸ hv_lm2K3.2⟩ ⟨hm7 ▸ hv_S3, hm7 ▸ hi_S3⟩
  refine ⟨o, st'', c_rest, hrun_rest, hpost_rest, ?_⟩
  dsimp only [argsSize, Expr.size]
  linarith only [hc_rest]

private theorem weights_phaseB2_runs {w b h : ℕ} {p : Program} {ω : ℕ → Bool}
    {Q_w : Outcome → (ℕ → ℕ) → Prop}
    {st7 : State} {G : IndexedGraph}
    {nlPtr lenPtr wtPtr L outMultPtr outWPtr outKPtr heap S_val target : ℕ}
    (hp : p.HasAt b (weightsModule b h))
    (hh : 0 < h) (hw : 3 * h + 2 ≤ w) (hL1 : 1 ≤ L) (_hne : 1 ≤ (nonloopEdges G).length)
    (hS_pos : 1 ≤ S_val)
    (hS_cap : 2 * S_val < Num.capacity h (kWidthOf (nonloopEdges G).length L))
    (hbound : heap + weightsSpace (nonloopEdges G).length (kWidthOf (nonloopEdges G).length L) < 2 ^ w)
    (hb7 : BBaseRegs st7 (nonloopEdges G).length nlPtr lenPtr wtPtr (activeVertsList G).length L
      outMultPtr outWPtr outKPtr (kWidthOf (nonloopEdges G).length L)
      (heap + kWidthOf (nonloopEdges G).length L) heap)
    (hr7_16 : st7.regs 16 = heap + 2 * kWidthOf (nonloopEdges G).length L)
    (hr7_17 : st7.regs 17 = heap + 4 * kWidthOf (nonloopEdges G).length L)
    (hr7_19 : st7.regs 19 = heap + 7 * kWidthOf (nonloopEdges G).length L +
      (nonloopEdges G).length * (2 * kWidthOf (nonloopEdges G).length L))
    (hz3 : ZeroFrom st7.mem (heap + 7 * kWidthOf (nonloopEdges G).length L +
      (nonloopEdges G).length * (2 * kWidthOf (nonloopEdges G).length L)))
    (hv_one : Num.Valid st7.mem (heap + 2 * kWidthOf (nonloopEdges G).length L) h
        (kWidthOf (nonloopEdges G).length L) ∧
      Num.intVal st7.mem (heap + 2 * kWidthOf (nonloopEdges G).length L) h
        (kWidthOf (nonloopEdges G).length L) = (1 : ℤ))
    (hv_S : Num.Valid st7.mem (heap + 6 * kWidthOf (nonloopEdges G).length L +
        (nonloopEdges G).length * (2 * kWidthOf (nonloopEdges G).length L)) h
        (kWidthOf (nonloopEdges G).length L) ∧
      Num.intVal st7.mem (heap + 6 * kWidthOf (nonloopEdges G).length L +
        (nonloopEdges G).length * (2 * kWidthOf (nonloopEdges G).length L)) h
        (kWidthOf (nonloopEdges G).length L) = (S_val : ℤ))
    (hrest : Stmt) :
    let nl := nonloopEdges G
    let K := kWidthOf nl.length L
    let hp_sum := heap + 7 * K + nl.length * (2 * K)
    let hp_pre := heap + 13 * K + nl.length * (2 * K)
    (∀ st17 : State,
      WeightsRegs st17 nl.length nlPtr lenPtr wtPtr (activeVertsList G).length L
        outMultPtr outWPtr outKPtr K (heap + K) heap (heap + 4 * K) (hp_sum + 2 * K) (hp_sum + 4 * K) →
      st17.regs 19 = hp_pre →
      (∀ a < hp_sum - K, st17.mem a = st7.mem a) →
      ZeroFrom st17.mem hp_pre →
      (Num.Valid st17.mem (hp_sum + 2 * K) h (2 * K) ∧
        Num.intVal st17.mem (hp_sum + 2 * K) h (2 * K) = (S_val : ℤ)) →
      (Num.Valid st17.mem (hp_sum + 4 * K) h (2 * K) ∧
        Num.intVal st17.mem (hp_sum + 4 * K) h (2 * K) = ((S_val - 1 : ℕ) : ℤ)) →
      ∃ o st'' c, Runs w p ω hrest st17 o st'' c ∧
        Q_w o st''.mem ∧
        c ≤ target) →
    ∃ o st'' c, Runs w p ω
      (.assign 20 (.bin .sub (.reg 19) (.reg 11)) ;;
       .call 21 (b + idxWSubtract) [.reg 20, .reg 16, .reg 11, .reg 19] ;;
       .assign 22 (.bin .add (.reg 19) (.reg 11)) ;;
       .assign 19 (.reg 21) ;;
       .call 21 (b + idxWSignExtend) [.reg 20, .reg 11, .reg 13, .reg 19] ;;
       .assign 18 (.reg 19) ;;
       .assign 19 (.reg 21) ;;
       .call 21 (b + idxWSignExtend) [.reg 22, .reg 11, .reg 13, .reg 19] ;;
       .assign 23 (.reg 19) ;;
       .assign 19 (.reg 21) ;;
       hrest)
      st7 o st'' c ∧
      Q_w o st''.mem ∧
      c ≤ (74 * K + 42) + (30 * (2 * K) + 42) + (30 * (2 * K) + 42) + 50 + target := by
  intro nl K hp_sum hp_pre hcont
  have hsub := weights_hasAt_sub hp
  have hbh : Num.base h < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hw1 : 1 < 2 ^ w := lt_of_le_of_lt
    (by simpa [Num.base] using Nat.one_le_two_pow (n := h)) hbh
  have hw2 : 2 * h + 2 ≤ w := by omega
  have hse_mc := Num.signExtend_meetsContract hh hw1 hbh hsub.2.2.2.1
  have hsb_mc := Num.subtract_meetsContract hh hw2 hsub.2.2.2.2.2.1
  have hK1 : 1 ≤ K := by dsimp only [K, kWidthOf]; omega
  have hbound' : heap + weightsSpace nl.length K < 2 ^ w := hbound
  have hws_lb : 13 * K + nl.length * (2 * K) ≤ weightsSpace nl.length K := by
    dsimp only [weightsSpace]
    have h2 : nl.length * (2 * K) ≤ nl.length * (18 * K + 2 * Num.integerDivideSpace (2 * K)) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  have hpre_w : hp_pre < 2 ^ w := by dsimp only [hp_pre]; omega
  have hsum_w : hp_sum < 2 ^ w := by dsimp only [hp_sum, hp_pre] at *; omega
  have hsumK_w : hp_sum + K < 2 ^ w := by dsimp only [hp_sum, hp_pre] at *; omega
  have hsum2K_w : hp_sum + 2 * K < 2 ^ w := by dsimp only [hp_sum, hp_pre] at *; omega
  have hsum4K_w : hp_sum + 4 * K < 2 ^ w := by dsimp only [hp_sum, hp_pre] at *; omega
  have hsumS_w : hp_sum - K < 2 ^ w := lt_of_le_of_lt (Nat.sub_le _ _) hsum_w
  have hK_w : K < 2 ^ w := by dsimp only [hp_pre] at hpre_w; omega
  have h2K_w : 2 * K < 2 ^ w := by dsimp only [hp_pre] at hpre_w; omega
  have hheap2K_w : heap + 2 * K < 2 ^ w := by dsimp only [hp_pre] at hpre_w; omega
  have hS_cap' : 2 * S_val < Num.capacity h K := hS_cap
  have hsumS_eq : hp_sum - K = heap + 6 * K + nl.length * (2 * K) := by
    dsimp only [hp_sum]; omega
  have hv_S_mem : Num.Valid st7.mem (hp_sum - K) h K ∧ Num.intVal st7.mem (hp_sum - K) h K = (S_val : ℤ) := by
    rw [hsumS_eq]; exact hv_S
  have hsumS_lt_sum : hp_sum - K + K = hp_sum := by
    dsimp only [hp_sum]; omega
  have hdst_K2K : heap + 2 * K + K ≤ hp_sum := by dsimp only [hp_sum]; omega
  refine runs_start_le ?_
  refine runs_seq_assign_step (Expr.eval_sub (Expr.eval_reg_of_eq hr7_19) (Expr.eval_reg_of_eq hb7.r11) hsum_w)
    rfl fun st8 hm8 _ hr8' => ?_
  have hb8 := bBaseRegs_upd hb7 hr8' (by decide)
  have hr8_16 : st8.regs 16 = heap + 2 * K := by rw [hr8', Function.update_of_ne (by decide), hr7_16]
  have hr8_17 : st8.regs 17 = heap + 4 * K := by rw [hr8', Function.update_of_ne (by decide), hr7_17]
  have hr8_19 : st8.regs 19 = hp_sum := by rw [hr8', Function.update_of_ne (by decide), hr7_19]
  have hr8_20 : st8.regs 20 = hp_sum - K := by rw [hr8', Function.update_self]
  have hpre4 : (Num.subtractContract w h).pre [hp_sum - K, heap + 2 * K, K, hp_sum] st8.mem := by
    rw [hm8]
    refine ⟨⟨hp_sum - K, heap + 2 * K, K, hp_sum, rfl, hsumS_lt_sum.le, hdst_K2K, hv_S_mem.1, hv_one.1⟩, hz3, ?_⟩
    change hp_sum + 2 * K < 2 ^ w; exact hsum2K_w
  refine runs_seq_call_step hsb_mc (vs := [hp_sum - K, heap + 2 * K, K, hp_sum])
    (evalArgs_cons (Expr.eval_reg_of_eq hr8_20)
      (evalArgs_cons (Expr.eval_reg_of_eq hr8_16)
        (evalArgs_cons (Expr.eval_reg_of_eq hb8.r11)
          (evalArgs_cons (Expr.eval_reg_of_eq hr8_19) (evalArgs_nil _ _)))))
    (fun x hx => by
      simp at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hsumS_w
      · exact hheap2K_w
      · exact hK_w
      · exact hsum_w)
    hpre4 rfl (rfl : _ = 74 * K + 42)
    fun hp4 mem4 st9 hpost4 hm9 hr9' => ?_
  rw [hm8] at hpost4
  obtain ⟨hhp4, _, _, hfr4, hz4, hv_Sm1_4, hi_Sm1_4⟩ := hpost4
  change ∀ x < hp_sum, mem4 x = st7.mem x at hfr4
  change Num.intVal mem4 (hp_sum + K) h K =
    Num.wrap h K (Num.intVal st7.mem (hp_sum - K) h K - Num.intVal st7.mem (heap + 2 * K) h K) at hi_Sm1_4
  have hhp4_val : hp4 = hp_sum + 2 * K := by
    have ha : heapArg [hp_sum - K, heap + 2 * K, K, hp_sum] = hp_sum := rfl
    have hg : ([hp_sum - K, heap + 2 * K, K, hp_sum] : List ℕ).getD 2 0 = K := rfl
    rw [ha, hg] at hhp4; exact hhp4
  have hz4' : ZeroFrom mem4 (hp_sum + 2 * K) := hhp4_val ▸ hz4
  have hi_Sm1_eq : Num.intVal mem4 (hp_sum + K) h K = ((S_val - 1 : ℕ) : ℤ) := by
    rw [hi_Sm1_4, hv_S_mem.2, hv_one.2]
    have hcast : (S_val : ℤ) - 1 = ((S_val - 1 : ℕ) : ℤ) := by omega
    rw [hcast, Num.wrap_of_fits (fits_of_lt_half_cap
      (Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 2 (Nat.sub_le S_val 1)) hS_cap'))]
  have hb9 := bBaseRegs_upd hb8 hr9' (by decide)
  have hr9_17 : st9.regs 17 = heap + 4 * K := by rw [hr9', Function.update_of_ne (by decide), hr8_17]
  have hr9_19 : st9.regs 19 = hp_sum := by rw [hr9', Function.update_of_ne (by decide), hr8_19]
  have hr9_20 : st9.regs 20 = hp_sum - K := by rw [hr9', Function.update_of_ne (by decide), hr8_20]
  have hr9_21 : st9.regs 21 = hp_sum + 2 * K := by rw [hr9', hhp4_val, Function.update_self]
  refine runs_seq_assign_step (Expr.eval_add (Expr.eval_reg_of_eq hr9_19) (Expr.eval_reg_of_eq hb9.r11) hsumK_w)
    rfl fun st10 hm10 _ hr10' => ?_
  have hb10 := bBaseRegs_upd hb9 hr10' (by decide)
  have hr10_17 : st10.regs 17 = heap + 4 * K := by rw [hr10', Function.update_of_ne (by decide), hr9_17]
  have hr10_20 : st10.regs 20 = hp_sum - K := by rw [hr10', Function.update_of_ne (by decide), hr9_20]
  have hr10_21 : st10.regs 21 = hp_sum + 2 * K := by rw [hr10', Function.update_of_ne (by decide), hr9_21]
  have hr10_22 : st10.regs 22 = hp_sum + K := by rw [hr10', Function.update_self]
  refine runs_seq_assign_step (Expr.eval_reg_of_eq hr10_21) rfl fun st11 hm11 _ hr11' => ?_
  have hst11_mem : st11.mem = mem4 := hm11.trans (hm10.trans hm9)
  have hb11 := bBaseRegs_upd hb10 hr11' (by decide)
  have hr11_17 : st11.regs 17 = heap + 4 * K := by rw [hr11', Function.update_of_ne (by decide), hr10_17]
  have hr11_19 : st11.regs 19 = hp_sum + 2 * K := by rw [hr11', Function.update_self]
  have hr11_20 : st11.regs 20 = hp_sum - K := by rw [hr11', Function.update_of_ne (by decide), hr10_20]
  have hr11_22 : st11.regs 22 = hp_sum + K := by rw [hr11', Function.update_of_ne (by decide), hr10_22]
  have hv_S4 : Num.Valid mem4 (hp_sum - K) h K ∧ Num.intVal mem4 (hp_sum - K) h K = (S_val : ℤ) := by
    have heq : ∀ i < K, mem4 (hp_sum - K + i) = st7.mem (hp_sum - K + i) := fun i hi =>
      hfr4 _ (by linarith only [hi, hsumS_lt_sum])
    exact ⟨numValid_congr (fun i hi => (heq i hi).symm) hv_S_mem.1, by rw [intVal_congr_range heq, hv_S_mem.2]⟩
  have hpre5 : (Num.signExtendContract w h).pre [hp_sum - K, K, 2 * K, hp_sum + 2 * K] st11.mem := by
    rw [hst11_mem]
    refine ⟨⟨hp_sum - K, K, 2 * K, hp_sum + 2 * K, rfl, by linarith only [hK1],
      by linarith only [hsumS_lt_sum, hK1], hv_S4.1⟩, hz4', ?_⟩
    change (hp_sum + 2 * K) + 2 * K < 2 ^ w; linarith only [hsum4K_w]
  refine runs_seq_call_step hse_mc (vs := [hp_sum - K, K, 2 * K, hp_sum + 2 * K])
    (evalArgs_cons (Expr.eval_reg_of_eq hr11_20)
      (evalArgs_cons (Expr.eval_reg_of_eq hb11.r11)
        (evalArgs_cons (Expr.eval_reg_of_eq hb11.r13)
          (evalArgs_cons (Expr.eval_reg_of_eq hr11_19) (evalArgs_nil _ _)))))
    (fun x hx => by
      simp at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hsumS_w
      · exact hK_w
      · exact h2K_w
      · exact hsum2K_w)
    hpre5 rfl (rfl : _ = 30 * (2 * K) + 42)
    fun hp5 mem5 st12 hpost5 hm12 hr12' => ?_
  rw [hst11_mem] at hpost5
  obtain ⟨hhp5, _, _, hfr5, hz5, hv_S2K, hi_S2K⟩ := hpost5
  change ∀ x < hp_sum + 2 * K, mem5 x = mem4 x at hfr5
  change Num.intVal mem5 (hp_sum + 2 * K) h (2 * K) = Num.intVal mem4 (hp_sum - K) h K at hi_S2K
  have hhp5_val : hp5 = hp_sum + 4 * K := by
    have ha : heapArg [hp_sum - K, K, 2 * K, hp_sum + 2 * K] = hp_sum + 2 * K := rfl
    have hg : ([hp_sum - K, K, 2 * K, hp_sum + 2 * K] : List ℕ).getD 2 0 = 2 * K := rfl
    rw [ha, hg] at hhp5; rw [hhp5]; ring
  have hz5' : ZeroFrom mem5 (hp_sum + 4 * K) := hhp5_val ▸ hz5
  have hi_S2K_eq : Num.intVal mem5 (hp_sum + 2 * K) h (2 * K) = (S_val : ℤ) := by
    rw [hi_S2K, hv_S4.2]
  have hb12 := bBaseRegs_upd hb11 hr12' (by decide)
  have hr12_17 : st12.regs 17 = heap + 4 * K := by rw [hr12', Function.update_of_ne (by decide), hr11_17]
  have hr12_19 : st12.regs 19 = hp_sum + 2 * K := by rw [hr12', Function.update_of_ne (by decide), hr11_19]
  have hr12_21 : st12.regs 21 = hp_sum + 4 * K := by rw [hr12', hhp5_val, Function.update_self]
  have hr12_22 : st12.regs 22 = hp_sum + K := by rw [hr12', Function.update_of_ne (by decide), hr11_22]
  refine runs_seq_assign_step (Expr.eval_reg_of_eq hr12_19) rfl fun st13 hm13 _ hr13' => ?_
  have hb13 := bBaseRegs_upd hb12 hr13' (by decide)
  have hr13_17 : st13.regs 17 = heap + 4 * K := by rw [hr13', Function.update_of_ne (by decide), hr12_17]
  have hr13_18 : st13.regs 18 = hp_sum + 2 * K := by rw [hr13', Function.update_self]
  have hr13_21 : st13.regs 21 = hp_sum + 4 * K := by rw [hr13', Function.update_of_ne (by decide), hr12_21]
  have hr13_22 : st13.regs 22 = hp_sum + K := by rw [hr13', Function.update_of_ne (by decide), hr12_22]
  refine runs_seq_assign_step (Expr.eval_reg_of_eq hr13_21) rfl fun st14 hm14 _ hr14' => ?_
  have hst14_mem : st14.mem = mem5 := hm14.trans (hm13.trans hm12)
  have hb14 := bBaseRegs_upd hb13 hr14' (by decide)
  have hr14_17 : st14.regs 17 = heap + 4 * K := by rw [hr14', Function.update_of_ne (by decide), hr13_17]
  have hr14_18 : st14.regs 18 = hp_sum + 2 * K := by rw [hr14', Function.update_of_ne (by decide), hr13_18]
  have hr14_19 : st14.regs 19 = hp_sum + 4 * K := by rw [hr14', Function.update_self]
  have hr14_22 : st14.regs 22 = hp_sum + K := by rw [hr14', Function.update_of_ne (by decide), hr13_22]
  have hv_Sm1_5 : Num.Valid mem5 (hp_sum + K) h K ∧ Num.intVal mem5 (hp_sum + K) h K = ((S_val - 1 : ℕ) : ℤ) := by
    have heq : ∀ i < K, mem5 (hp_sum + K + i) = mem4 (hp_sum + K + i) := fun i hi => hfr5 _ (by linarith only [hi])
    exact ⟨numValid_congr (fun i hi => (heq i hi).symm) hv_Sm1_4, by rw [intVal_congr_range heq, hi_Sm1_eq]⟩
  have hpre6 : (Num.signExtendContract w h).pre [hp_sum + K, K, 2 * K, hp_sum + 4 * K] st14.mem := by
    rw [hst14_mem]
    refine ⟨⟨hp_sum + K, K, 2 * K, hp_sum + 4 * K, rfl, (by linarith only [hK1]), (by linarith only [hK1]), hv_Sm1_5.1⟩, hz5', ?_⟩
    have hpre_eq : (hp_sum + 4 * K) + 2 * K = hp_pre := by dsimp only [hp_sum, hp_pre]; ring
    change (hp_sum + 4 * K) + 2 * K < 2 ^ w
    rw [hpre_eq]; exact hpre_w
  refine runs_seq_call_step hse_mc (vs := [hp_sum + K, K, 2 * K, hp_sum + 4 * K])
    (evalArgs_cons (Expr.eval_reg_of_eq hr14_22)
      (evalArgs_cons (Expr.eval_reg_of_eq hb14.r11)
        (evalArgs_cons (Expr.eval_reg_of_eq hb14.r13)
          (evalArgs_cons (Expr.eval_reg_of_eq hr14_19) (evalArgs_nil _ _)))))
    (fun x hx => by
      simp at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hsumK_w
      · exact hK_w
      · exact h2K_w
      · exact hsum4K_w)
    hpre6 rfl (rfl : _ = 30 * (2 * K) + 42)
    fun hp6 mem6 st15 hpost6 hm15 hr15' => ?_
  rw [hst14_mem] at hpost6
  obtain ⟨hhp6, _, _, hfr6, hz6, hv_Sm1_2K, hi_Sm1_2K⟩ := hpost6
  change ∀ x < hp_sum + 4 * K, mem6 x = mem5 x at hfr6
  change Num.intVal mem6 (hp_sum + 4 * K) h (2 * K) = Num.intVal mem5 (hp_sum + K) h K at hi_Sm1_2K
  have hhp6_val : hp6 = hp_pre := by
    have ha : heapArg [hp_sum + K, K, 2 * K, hp_sum + 4 * K] = hp_sum + 4 * K := rfl
    have hg : ([hp_sum + K, K, 2 * K, hp_sum + 4 * K] : List ℕ).getD 2 0 = 2 * K := rfl
    rw [ha, hg] at hhp6; rw [hhp6]; dsimp only [hp_sum, hp_pre]; ring
  have hz6' : ZeroFrom mem6 hp_pre := hhp6_val ▸ hz6
  have hb15 := bBaseRegs_upd hb14 hr15' (by decide)
  have hr15_17 : st15.regs 17 = heap + 4 * K := by rw [hr15', Function.update_of_ne (by decide), hr14_17]
  have hr15_18 : st15.regs 18 = hp_sum + 2 * K := by rw [hr15', Function.update_of_ne (by decide), hr14_18]
  have hr15_19 : st15.regs 19 = hp_sum + 4 * K := by rw [hr15', Function.update_of_ne (by decide), hr14_19]
  have hr15_21 : st15.regs 21 = hp_pre := by rw [hr15', hhp6_val, Function.update_self]
  refine runs_seq_assign_step (Expr.eval_reg_of_eq hr15_19) rfl fun st16 hm16 _ hr16' => ?_
  have hb16 := bBaseRegs_upd hb15 hr16' (by decide)
  have hr16_17 : st16.regs 17 = heap + 4 * K := by rw [hr16', Function.update_of_ne (by decide), hr15_17]
  have hr16_18 : st16.regs 18 = hp_sum + 2 * K := by rw [hr16', Function.update_of_ne (by decide), hr15_18]
  have hr16_21 : st16.regs 21 = hp_pre := by rw [hr16', Function.update_of_ne (by decide), hr15_21]
  have hr16_23 : st16.regs 23 = hp_sum + 4 * K := by rw [hr16', Function.update_self]
  refine runs_seq_assign_step (Expr.eval_reg_of_eq hr16_21) rfl fun st17 hm17 _ hr17' => ?_
  have hst17_mem : st17.mem = mem6 := hm17.trans (hm16.trans hm15)
  have hb17 := bBaseRegs_upd hb16 hr17' (by decide)
  have hregs17 : WeightsRegs st17 nl.length nlPtr lenPtr wtPtr (activeVertsList G).length L
      outMultPtr outWPtr outKPtr K (heap + K) heap (heap + 4 * K) (hp_sum + 2 * K) (hp_sum + 4 * K) :=
    ⟨hb17.r0, hb17.r1, hb17.r2, hb17.r3, hb17.r4, hb17.r5, hb17.r6, hb17.r7, hb17.r8, hb17.r11,
      hb17.r13, hb17.r14, hb17.r15,
      by rw [hr17', Function.update_of_ne (by decide), hr16_17],
      by rw [hr17', Function.update_of_ne (by decide), hr16_18],
      by rw [hr17', Function.update_of_ne (by decide), hr16_23]⟩
  have hr17_19 : st17.regs 19 = hp_pre := by rw [hr17', Function.update_self]
  have hmem6_eq : ∀ a < hp_sum - K, mem6 a = st7.mem a := fun a ha => by
    have ha1 : a < hp_sum := lt_of_lt_of_le ha (Nat.sub_le _ _)
    have ha2 : a < hp_sum + 2 * K := by linarith only [ha1, hK1]
    have ha3 : a < hp_sum + 4 * K := by linarith only [ha1, hK1]
    rw [hfr6 a ha3, hfr5 a ha2, hfr4 a ha1]
  have hv_S2K6 : Num.Valid mem6 (hp_sum + 2 * K) h (2 * K) ∧
      Num.intVal mem6 (hp_sum + 2 * K) h (2 * K) = (S_val : ℤ) := by
    have heq : ∀ i < 2 * K, mem6 (hp_sum + 2 * K + i) = mem5 (hp_sum + 2 * K + i) := fun i hi =>
      hfr6 _ (by linarith only [hi, hK1])
    exact ⟨numValid_congr (fun i hi => (heq i hi).symm) hv_S2K, by rw [intVal_congr_range heq, hi_S2K_eq]⟩
  have hv_Sm1_2K6 : Num.Valid mem6 (hp_sum + 4 * K) h (2 * K) ∧
      Num.intVal mem6 (hp_sum + 4 * K) h (2 * K) = ((S_val - 1 : ℕ) : ℤ) := by
    change Num.intVal mem6 (hp_sum + 4 * K) h (2 * K) = Num.intVal mem5 (hp_sum + K) h K at hi_Sm1_2K
    exact ⟨hv_Sm1_2K, hi_Sm1_2K.trans hv_Sm1_5.2⟩
  obtain ⟨o, st'', c_rest, hrun_rest, hpost_rest, hc_rest⟩ :=
    hcont st17 hregs17 hr17_19 (fun a ha => by rw [hst17_mem]; exact hmem6_eq a ha)
      (hst17_mem ▸ hz6') ⟨hst17_mem ▸ hv_S2K6.1, hst17_mem ▸ hv_S2K6.2⟩
      ⟨hst17_mem ▸ hv_Sm1_2K6.1, hst17_mem ▸ hv_Sm1_2K6.2⟩
  refine ⟨o, st'', c_rest, hrun_rest, hpost_rest, ?_⟩
  dsimp only [argsSize, Expr.size]
  linarith only [hc_rest]

theorem weights_phaseB_runs {w b h : ℕ} {p : Program} {ω : ℕ → Bool}
    {Q_w : Outcome → (ℕ → ℕ) → Prop}
    {st' : State} {mem : ℕ → ℕ} {G : IndexedGraph} {vNat lNat : ℕ → ℕ}
    {nlPtr lenPtr wtPtr L outMultPtr outWPtr outKPtr heap minIdx target : ℕ}
    (hp : p.HasAt b (weightsModule b h))
    (hh : 0 < h) (hw : 3 * h + 2 ≤ w) (hL1 : 1 ≤ L) (hne : 1 ≤ (nonloopEdges G).length)
    (hmin_lt : minIdx < (nonloopEdges G).length)
    (hnl_list : ListAt mem nlPtr (nonloopEdges G))
    (hnl_h : nlPtr + (nonloopEdges G).length ≤ heap)
    (hoK_h : outKPtr < heap)
    (hlen_mem : ∀ e < G.m, Num.Valid mem (lenPtr + e * L) h L ∧
      Num.intVal mem (lenPtr + e * L) h L = (lNat e : ℤ) ∧ 1 ≤ lNat e)
    (hwt_mem : ∀ e < G.m, Num.Valid mem (wtPtr + e * L) h L ∧
      Num.intVal mem (wtPtr + e * L) h L = (vNat e : ℤ) ∧ 1 ≤ vNat e)
    (hlen_h : lenPtr + G.m * L ≤ heap) (hwt_h : wtPtr + G.m * L ≤ heap)
    (hG_edges : ∀ e ∈ nonloopEdges G, e < G.m)
    (hdisj_K_nl : DisjointRanges outKPtr 1 nlPtr (nonloopEdges G).length)
    (hdisj_K_len : DisjointRanges outKPtr 1 lenPtr (G.m * L))
    (hdisj_K_wt : DisjointRanges outKPtr 1 wtPtr (G.m * L))
    (hbound : heap + weightsSpace (nonloopEdges G).length (kWidthOf (nonloopEdges G).length L) < 2 ^ w)
    (hS_cap : 2 * ((nonloopEdges G).map vNat).sum < Num.capacity h (kWidthOf (nonloopEdges G).length L))
    (hr0 : st'.regs 0 = (nonloopEdges G).length) (hr1 : st'.regs 1 = nlPtr)
    (hr2 : st'.regs 2 = lenPtr) (hr3 : st'.regs 3 = wtPtr)
    (hr4 : st'.regs 4 = (activeVertsList G).length) (hr5 : st'.regs 5 = L)
    (hr6 : st'.regs 6 = outMultPtr) (hr7 : st'.regs 7 = outWPtr) (hr8 : st'.regs 8 = outKPtr)
    (hr11 : st'.regs 11 = kWidthOf (nonloopEdges G).length L) (hr12 : st'.regs 12 = minIdx)
    (hr13 : st'.regs 13 = 2 * kWidthOf (nonloopEdges G).length L)
    (hr14 : st'.regs 14 = heap) (hr15 : st'.regs 15 = heap + kWidthOf (nonloopEdges G).length L)
    (hr16 : st'.regs 16 = heap + 2 * kWidthOf (nonloopEdges G).length L)
    (hr19 : st'.regs 19 = heap + 3 * kWidthOf (nonloopEdges G).length L)
    (hm_K : st'.mem outKPtr = kWidthOf (nonloopEdges G).length L)
    (hpres : ∀ a < heap, a ≠ outKPtr → st'.mem a = mem a)
    (hz3 : ZeroFrom st'.mem (heap + 3 * kWidthOf (nonloopEdges G).length L))
    (hv_one : Num.Valid st'.mem (heap + 2 * kWidthOf (nonloopEdges G).length L) h (kWidthOf (nonloopEdges G).length L) ∧
      Num.intVal st'.mem (heap + 2 * kWidthOf (nonloopEdges G).length L) h (kWidthOf (nonloopEdges G).length L) = (1 : ℤ))
    (hrest : Stmt) :
    let nl := nonloopEdges G
    let K := kWidthOf nl.length L
    let hp_sum := heap + 7 * K + nl.length * (2 * K)
    let hp_pre := heap + 13 * K + nl.length * (2 * K)
    let S_val := (nl.map vNat).sum
    let lmin_val := lNat (nl[minIdx]'hmin_lt)
    (∀ stB : State,
      WeightsRegs stB nl.length nlPtr lenPtr wtPtr (activeVertsList G).length L
        outMultPtr outWPtr outKPtr K (heap + K) heap (heap + 4 * K) (hp_sum + 2 * K) (hp_sum + 4 * K) →
      stB.regs 19 = hp_pre →
      stB.mem outKPtr = K →
      (∀ a < heap, a ≠ outKPtr → stB.mem a = mem a) →
      (∀ a < heap + 3 * K, stB.mem a = st'.mem a) →
      ZeroFrom stB.mem hp_pre →
      (Num.Valid stB.mem (heap + 4 * K) h (2 * K) ∧
        Num.intVal stB.mem (heap + 4 * K) h (2 * K) = (lmin_val : ℤ)) →
      (Num.Valid stB.mem (hp_sum + 2 * K) h (2 * K) ∧
        Num.intVal stB.mem (hp_sum + 2 * K) h (2 * K) = (S_val : ℤ)) →
      (Num.Valid stB.mem (hp_sum + 4 * K) h (2 * K) ∧
        Num.intVal stB.mem (hp_sum + 4 * K) h (2 * K) = ((S_val - 1 : ℕ) : ℤ)) →
      ∃ o st'' c, Runs w p ω hrest stB o st'' c ∧
        Q_w o st''.mem ∧
        c ≤ target) →
    ∃ o st'' c, Runs w p ω
      (.assign 20 (.bin .add (.reg 2) (.bin .mul (.load (.bin .add (.reg 1) (.reg 12))) (.reg 5))) ;;
       .call 21 (b + idxWSignExtend) [.reg 20, .reg 5, .reg 11, .reg 19] ;;
       .assign 20 (.reg 19) ;;
       .assign 19 (.reg 21) ;;
       .call 21 (b + idxWSignExtend) [.reg 20, .reg 11, .reg 13, .reg 19] ;;
       .assign 17 (.reg 19) ;;
       .assign 19 (.reg 21) ;;
       .call 19 (b + idxSumWeights) [.reg 0, .reg 1, .reg 3, .reg 5, .reg 11, .reg 19] ;;
       .assign 20 (.bin .sub (.reg 19) (.reg 11)) ;;
       .call 21 (b + idxWSubtract) [.reg 20, .reg 16, .reg 11, .reg 19] ;;
       .assign 22 (.bin .add (.reg 19) (.reg 11)) ;;
       .assign 19 (.reg 21) ;;
       .call 21 (b + idxWSignExtend) [.reg 20, .reg 11, .reg 13, .reg 19] ;;
       .assign 18 (.reg 19) ;;
       .assign 19 (.reg 21) ;;
       .call 21 (b + idxWSignExtend) [.reg 22, .reg 11, .reg 13, .reg 19] ;;
       .assign 23 (.reg 19) ;;
       .assign 19 (.reg 21) ;;
       hrest)
      st' o st'' c ∧
      Q_w o st''.mem ∧
      c ≤ ((30 * K + 42) + (30 * (2 * K) + 42) +
          (nl.length * (70 * K + 120) + 25 * K + 50) + (74 * K + 42) +
          (30 * (2 * K) + 42) + (30 * (2 * K) + 42) + 92) + target := by
  intro nl K hp_sum hp_pre S_val lmin_val hcont
  have hS_pos : 1 ≤ S_val := by
    have hnl_pos : 0 < nl.length := hne
    have he0 := List.getElem_mem (l := nl) (n := 0) hnl_pos
    have hm0 := hwt_mem _ (hG_edges _ he0)
    have hle := List.single_le_sum (fun _ _ => Nat.zero_le _) (vNat nl[0]) (List.mem_map_of_mem he0)
    exact le_trans hm0.2.2 hle
  have hK1 : 1 ≤ K := by dsimp only [K, kWidthOf]; omega
  have hmain : ∃ o st'' cB, Runs w p ω
      (.assign 20 (.bin .add (.reg 2) (.bin .mul (.load (.bin .add (.reg 1) (.reg 12))) (.reg 5))) ;;
       .call 21 (b + idxWSignExtend) [.reg 20, .reg 5, .reg 11, .reg 19] ;;
       .assign 20 (.reg 19) ;;
       .assign 19 (.reg 21) ;;
       .call 21 (b + idxWSignExtend) [.reg 20, .reg 11, .reg 13, .reg 19] ;;
       .assign 17 (.reg 19) ;;
       .assign 19 (.reg 21) ;;
       .call 19 (b + idxSumWeights) [.reg 0, .reg 1, .reg 3, .reg 5, .reg 11, .reg 19] ;;
       .assign 20 (.bin .sub (.reg 19) (.reg 11)) ;;
       .call 21 (b + idxWSubtract) [.reg 20, .reg 16, .reg 11, .reg 19] ;;
       .assign 22 (.bin .add (.reg 19) (.reg 11)) ;;
       .assign 19 (.reg 21) ;;
       .call 21 (b + idxWSignExtend) [.reg 20, .reg 11, .reg 13, .reg 19] ;;
       .assign 18 (.reg 19) ;;
       .assign 19 (.reg 21) ;;
       .call 21 (b + idxWSignExtend) [.reg 22, .reg 11, .reg 13, .reg 19] ;;
       .assign 23 (.reg 19) ;;
       .assign 19 (.reg 21) ;;
       hrest)
      st' o st'' cB ∧
      Q_w o st''.mem ∧
      cB ≤ (30 * K + 42) + (30 * (2 * K) + 42) +
          (nl.length * (70 * K + 120) + 25 * K + 50) + 42 +
          ((74 * K + 42) + (30 * (2 * K) + 42) + (30 * (2 * K) + 42) + 50 + target) := by
    refine weights_phaseB1_runs hp hh hw hL1 hne hmin_lt hnl_list hnl_h hoK_h hlen_mem hwt_mem
      hlen_h hwt_h hG_edges hdisj_K_nl hdisj_K_len hdisj_K_wt hbound hS_cap
      hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8 hr11 hr12 hr13 hr14 hr15 hr16 hr19 hpres hz3
      _ fun st7 hb7 hr7_16 hr7_17 hr7_19 hst7_eq3 hz7 hv7_lm hv7_S => ?_
    have hv7_one : Num.Valid st7.mem (heap + 2 * K) h K ∧ Num.intVal st7.mem (heap + 2 * K) h K = (1 : ℤ) := by
      have heq : ∀ i < K, st7.mem (heap + 2 * K + i) = st'.mem (heap + 2 * K + i) := fun i hi =>
        hst7_eq3 _ (by linarith only [hi])
      exact ⟨numValid_congr (fun i hi => (heq i hi).symm) hv_one.1, by rw [intVal_congr_range heq, hv_one.2]⟩
    have hsumS_eq : hp_sum - K = heap + 6 * K + nl.length * (2 * K) := by
      dsimp only [hp_sum]; omega
    have hv7_S' : Num.Valid st7.mem (heap + 6 * K + nl.length * (2 * K)) h K ∧
        Num.intVal st7.mem (heap + 6 * K + nl.length * (2 * K)) h K = (S_val : ℤ) := by
      rw [← hsumS_eq]; exact hv7_S
    have hsub_ge_4K : heap + 6 * K ≤ heap + 7 * K + nl.length * (2 * K) - K := by omega
    refine weights_phaseB2_runs hp hh hw hL1 hne hS_pos hS_cap hbound hb7 hr7_16 hr7_17 hr7_19
      hz7 hv7_one hv7_S' _ fun stB hregsB hrB19 hstB_eq hzB hvB_S hvB_Sm1 => ?_
    have hstB_eq3 : ∀ a < heap + 3 * K, stB.mem a = st'.mem a := fun a ha => by
      rw [hstB_eq a (lt_of_lt_of_le ha (by linarith only [hsub_ge_4K, hK1])), hst7_eq3 a ha]
    have hmB_K : stB.mem outKPtr = K := by rw [hstB_eq3 outKPtr (by linarith only [hoK_h, hK1]), hm_K]
    have hmB_pres : ∀ a < heap, a ≠ outKPtr → stB.mem a = mem a := fun a ha hne => by
      rw [hstB_eq3 a (by linarith only [ha, hK1]), hpres a ha hne]
    have hvB_lm : Num.Valid stB.mem (heap + 4 * K) h (2 * K) ∧
        Num.intVal stB.mem (heap + 4 * K) h (2 * K) = (lmin_val : ℤ) := by
      have heq : ∀ i < 2 * K, stB.mem (heap + 4 * K + i) = st7.mem (heap + 4 * K + i) := fun i hi =>
        hstB_eq _ (lt_of_lt_of_le (by linarith only [hi]) hsub_ge_4K)
      exact ⟨numValid_congr (fun i hi => (heq i hi).symm) hv7_lm.1, by rw [intVal_congr_range heq, hv7_lm.2]⟩
    exact hcont stB hregsB hrB19 hmB_K hmB_pres hstB_eq3 hzB hvB_lm hvB_S hvB_Sm1
  obtain ⟨o, st'', cB, hrun, hpost, hcB⟩ := hmain
  refine ⟨o, st'', cB, hrun, hpost, ?_⟩
  linarith only [hcB]

end MinCostFlow.WideWord
