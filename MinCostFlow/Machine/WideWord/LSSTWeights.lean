module

public import MinCostFlow.Machine.WideWord.LSSTWeightsPhaseB
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Full multiword weight computation contract for Theorem 2.2

This module proves `weights_meetsContract`, chaining Phases A and B with the per-edge loop
over `weightStepProc` and certifying all hypotheses needed by `concreteLSST_isLSST`.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM MinCostFlow

theorem weights_runs {w b h : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem : ℕ → ℕ} {pos : ℕ}
    (hp : p.HasAt b (weightsModule b h))
    (G : IndexedGraph) (v ℓ : ℕ → ℝ)
    (nlPtr lenPtr wtPtr L P outMultPtr outWPtr outKPtr heap : ℕ)
    (hwords : ∀ a ∈ [(nonloopEdges G).length, nlPtr, lenPtr, wtPtr, (activeVertsList G).length, L,
      outMultPtr, outWPtr, outKPtr, heap], a < 2 ^ w)
    (hG : G.Valid) (hL1 : 1 ≤ L) (hh : 0 < h) (hw : 3 * h + 2 ≤ w)
    (hne : 1 ≤ (nonloopEdges G).length)
    (hnl_list : ListAt mem nlPtr (nonloopEdges G))
    (hlen_pre : ∀ e < G.m, Num.Valid mem (lenPtr + e * L) h L ∧
      Num.fixVal mem (lenPtr + e * L) h L P = ℓ e ∧ 0 < ℓ e)
    (hwt_pre : ∀ e < G.m, Num.Valid mem (wtPtr + e * L) h L ∧
      Num.fixVal mem (wtPtr + e * L) h L P = v e ∧ 0 < v e)
    (hnl_h : nlPtr + (nonloopEdges G).length ≤ heap)
    (hlen_h : lenPtr + G.m * L ≤ heap) (hwt_h : wtPtr + G.m * L ≤ heap)
    (hom_h : outMultPtr + (nonloopEdges G).length ≤ heap)
    (how_h : outWPtr + (nonloopEdges G).length * kWidthOf (nonloopEdges G).length L ≤ heap)
    (hoK_h : outKPtr < heap)
    (homw_disj : DisjointRanges outMultPtr (nonloopEdges G).length outWPtr
      ((nonloopEdges G).length * kWidthOf (nonloopEdges G).length L))
    (homK_disj : DisjointRanges outMultPtr (nonloopEdges G).length outKPtr 1)
    (howK_disj : DisjointRanges outWPtr ((nonloopEdges G).length * kWidthOf (nonloopEdges G).length L) outKPtr 1)
    (hom_nl_disj : DisjointRanges outMultPtr (nonloopEdges G).length nlPtr (nonloopEdges G).length)
    (hom_len_disj : DisjointRanges outMultPtr (nonloopEdges G).length lenPtr (G.m * L))
    (hom_wt_disj : DisjointRanges outMultPtr (nonloopEdges G).length wtPtr (G.m * L))
    (how_nl_disj : DisjointRanges outWPtr ((nonloopEdges G).length * kWidthOf (nonloopEdges G).length L)
      nlPtr (nonloopEdges G).length)
    (how_len_disj : DisjointRanges outWPtr ((nonloopEdges G).length * kWidthOf (nonloopEdges G).length L)
      lenPtr (G.m * L))
    (how_wt_disj : DisjointRanges outWPtr ((nonloopEdges G).length * kWidthOf (nonloopEdges G).length L)
      wtPtr (G.m * L))
    (hoK_nl_disj : DisjointRanges outKPtr 1 nlPtr (nonloopEdges G).length)
    (hoK_len_disj : DisjointRanges outKPtr 1 lenPtr (G.m * L))
    (hoK_wt_disj : DisjointRanges outKPtr 1 wtPtr (G.m * L))
    (hz0 : ZeroFrom mem heap)
    (hbound : heap + weightsSpace (nonloopEdges G).length (kWidthOf (nonloopEdges G).length L) < 2 ^ w) :
    let nl := nonloopEdges G
    let Vcnt := (activeVertsList G).length
    let K := kWidthOf nl.length L
    ∃ st'' c,
      Runs w p ω (weightsProc b)
        (startState [nl.length, nlPtr, lenPtr, wtPtr, Vcnt, L, outMultPtr, outWPtr, outKPtr, heap] mem pos)
        (.returned (heap + weightsSpace nl.length K)) st'' c ∧
      st''.mem outKPtr = K ∧
      ZeroFrom st''.mem (heap + weightsSpace nl.length K) ∧
      (∀ a < heap, (a < outMultPtr ∨ outMultPtr + nl.length ≤ a) →
        (a < outWPtr ∨ outWPtr + nl.length * K ≤ a) → a ≠ outKPtr → st''.mem a = mem a) ∧
      (∃ (mult w_orig : ℕ → ℕ) (δ : ℝ),
        (∀ j (hj : j < nl.length), st''.mem (outMultPtr + j) = mult (nl[j]'hj)) ∧
        (∀ j (hj : j < nl.length), LimbsAt st''.mem (outWPtr + j * K) K h (w_orig (nl[j]'hj))) ∧
        (∀ e ∈ nl, mult e = LSF.edgeMult { G.toMGraph with E := nl.toFinset } v e) ∧
        (∀ e ∈ nl, 1 ≤ mult e ∧ mult e ≤ nl.length) ∧
        0 < δ ∧
        (∀ e ∈ nl, 4 ≤ w_orig e ∧ w_orig e < 2 ^ (K * h - 1)) ∧
        (∀ e ∈ nl, ℓ e ≤ δ * ((w_orig e : ℝ) + 1)) ∧
        (∀ e ∈ nl, δ * (w_orig e : ℝ) ≤ ℓ e) ∧
        (∀ e ∈ nl, δ * (Vcnt : ℝ) ≤ ℓ e / 2)) ∧
      c ≤ weightsCost nl.length L := by
  have hws_mc := weightStep_meetsContract (w := w) (h := h) hp
  let nl := nonloopEdges G
  let K := kWidthOf nl.length L
  let Vcnt := (activeVertsList G).length
  let vNat : ℕ → ℕ := fun e => Num.unsignedVal mem (wtPtr + e * L) h L
  let lNat : ℕ → ℕ := fun e => Num.unsignedVal mem (lenPtr + e * L) h L
  have hG_edges : ∀ e ∈ nl, e < G.m := fun e he => (mem_nonloopEdges_iff.mp he).1
  have h2P : (0 : ℝ) < (2 : ℝ) ^ P := by positivity
  have hlen_nat : ∀ e < G.m, Num.Valid mem (lenPtr + e * L) h L ∧
      Num.intVal mem (lenPtr + e * L) h L = (lNat e : ℤ) ∧
      2 * lNat e < Num.capacity h L ∧ 1 ≤ lNat e ∧ ℓ e = (lNat e : ℝ) / (2 : ℝ) ^ P := by
    intro e he
    obtain ⟨hv, hfx, hpos⟩ := hlen_pre e he
    have hint_pos : 0 < Num.intVal mem (lenPtr + e * L) h L := by
      have hr : (0 : ℝ) < Num.fixVal mem (lenPtr + e * L) h L P := hfx.symm ▸ hpos
      dsimp only [Num.fixVal] at hr
      exact Int.cast_pos.mp ((div_pos_iff_of_pos_right h2P).mp hr)
    have hp_nat := intVal_eq_nat_of_pos hv hint_pos
    have hfx_eq : ℓ e = (lNat e : ℝ) / (2 : ℝ) ^ P := by
      rw [← hfx]; dsimp only [Num.fixVal, lNat]; rw [hp_nat.1, Int.cast_natCast]
    exact ⟨hv, hp_nat.1, hp_nat.2.1, hp_nat.2.2, hfx_eq⟩
  have hwt_nat : ∀ e < G.m, Num.Valid mem (wtPtr + e * L) h L ∧
      Num.intVal mem (wtPtr + e * L) h L = (vNat e : ℤ) ∧
      2 * vNat e < Num.capacity h L ∧ 1 ≤ vNat e ∧ v e = (vNat e : ℝ) / (2 : ℝ) ^ P := by
    intro e he
    obtain ⟨hv, hfx, hpos⟩ := hwt_pre e he
    have hint_pos : 0 < Num.intVal mem (wtPtr + e * L) h L := by
      have hr : (0 : ℝ) < Num.fixVal mem (wtPtr + e * L) h L P := hfx.symm ▸ hpos
      dsimp only [Num.fixVal] at hr
      exact Int.cast_pos.mp ((div_pos_iff_of_pos_right h2P).mp hr)
    have hp_nat := intVal_eq_nat_of_pos hv hint_pos
    have hfx_eq : v e = (vNat e : ℝ) / (2 : ℝ) ^ P := by
      rw [← hfx]; dsimp only [Num.fixVal, vNat]; rw [hp_nat.1, Int.cast_natCast]
    exact ⟨hv, hp_nat.1, hp_nat.2.1, hp_nat.2.2, hfx_eq⟩
  have hcaps := weights_cap_facts hG hh hL1 hne
    (fun e he => (hwt_nat e (hG_edges e he)).2.2.1)
    (fun e he => (hlen_nat e (hG_edges e he)).2.2.1)
  change 2 * nl.length < Num.capacity h K ∧ 2 * (2 * Vcnt) < Num.capacity h K ∧
      2 * (nl.map vNat).sum < Num.capacity h K ∧
      (∀ e ∈ nl, 2 * (nl.length * vNat e + ((nl.map vNat).sum - 1)) < Num.capacity h (2 * K)) ∧
      (∀ e ∈ nl, ∀ lmin, 1 ≤ lmin →
        2 * ((2 * Vcnt * lNat e) / lmin) < Num.capacity h K ∧
        (2 * Vcnt * lNat e) / lmin < 2 ^ (K * h - 1)) at hcaps
  have hV_bds := activeVertsList_length_bounds hG hne
  have hV2 : 2 ≤ Vcnt := hV_bds.1
  have hnl_h' : nlPtr + nl.length ≤ heap := hnl_h
  have hlen_sub_h : ∀ (j : ℕ) (hj : j < nl.length),
      lenPtr + (nl[j]'hj) * L + L ≤ heap ∧ Num.Valid mem (lenPtr + (nl[j]'hj) * L) h L := by
    intro j hj
    have he_m := hG_edges _ (List.getElem_mem hj)
    have hmul : ((nl[j]'hj) + 1) * L ≤ G.m * L := Nat.mul_le_mul_right L he_m
    rw [Nat.add_mul, Nat.one_mul] at hmul
    exact ⟨by omega, (hlen_nat _ he_m).1⟩
  have hK1 : 1 ≤ K := by dsimp only [K, kWidthOf]; omega
  have hLK : L ≤ K := by dsimp only [K, kWidthOf]; omega
  have hbound' : heap + weightsSpace nl.length K < 2 ^ w := hbound
  have hws_lb : 13 * K + nl.length * (2 * K) ≤ weightsSpace nl.length K := by
    dsimp only [weightsSpace]
    have h2 : nl.length * (2 * K) ≤ nl.length * (18 * K + 2 * Num.integerDivideSpace (2 * K)) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  have hw1 : 1 < 2 ^ w := by
    have : 1 < weightsSpace nl.length K := by
      have : 13 ≤ 13 * K := by omega
      omega
    omega
  have hnl_w : nl.length < 2 ^ w := by
    have : nl.length ≤ nlPtr + nl.length := Nat.le_add_left _ _
    omega
  let Q_w : Outcome → (ℕ → ℕ) → Prop := fun o mem' =>
    o = .returned (heap + weightsSpace nl.length K) ∧
    mem' outKPtr = K ∧
    ZeroFrom mem' (heap + weightsSpace nl.length K) ∧
    (∀ a < heap, (a < outMultPtr ∨ outMultPtr + nl.length ≤ a) →
      (a < outWPtr ∨ outWPtr + nl.length * K ≤ a) → a ≠ outKPtr → mem' a = mem a) ∧
    (∃ (mult w_orig : ℕ → ℕ) (δ : ℝ),
      (∀ j (hj : j < nl.length), mem' (outMultPtr + j) = mult (nl[j]'hj)) ∧
      (∀ j (hj : j < nl.length), LimbsAt mem' (outWPtr + j * K) K h (w_orig (nl[j]'hj))) ∧
      (∀ e ∈ nl, mult e = LSF.edgeMult { G.toMGraph with E := nl.toFinset } v e) ∧
      (∀ e ∈ nl, 1 ≤ mult e ∧ mult e ≤ nl.length) ∧
      0 < δ ∧
      (∀ e ∈ nl, 4 ≤ w_orig e ∧ w_orig e < 2 ^ (K * h - 1)) ∧
      (∀ e ∈ nl, ℓ e ≤ δ * ((w_orig e : ℝ) + 1)) ∧
      (∀ e ∈ nl, δ * (w_orig e : ℝ) ≤ ℓ e) ∧
      (∀ e ∈ nl, δ * (Vcnt : ℝ) ≤ ℓ e / 2))
  suffices hmain : ∃ o st'' c_all, Runs w p ω (weightsProc b)
      (startState [nl.length, nlPtr, lenPtr, wtPtr, Vcnt, L, outMultPtr, outWPtr, outKPtr, heap] mem pos)
      o st'' c_all ∧
      Q_w o st''.mem ∧
      c_all ≤ (25 * nl.length + 80) + (nl.length * (41 * L + 100) + 50) +
          (23 * K + 6) + (23 * K + 6) + (23 * K + 6) + 64 +
          (((30 * K + 42) + (30 * (2 * K) + 42) +
            (nl.length * (70 * K + 120) + 25 * K + 50) + (74 * K + 42) +
            (30 * (2 * K) + 42) + (30 * (2 * K) + 42) + 92) +
           (nl.length * (weightStepCost K + 42) + 10)) by
    obtain ⟨o, st'', c_all, hrun_all, ⟨rfl, h1, h2, h3, h4⟩, hc_all⟩ := hmain
    have hcal := weights_callees_le nl.length L
    dsimp only [K, nl] at hcal hc_all
    exact ⟨st'', c_all, hrun_all, h1, h2, h3, h4, by linarith only [hc_all, hcal]⟩
  dsimp only [weightsProc]
  refine weights_phaseA_runs (Q_w := Q_w) hp hG hh hw hL1 hne hnl_list hnl_h hlen_sub_h hoK_nl_disj hoK_len_disj
    hG_edges hoK_h hz0 hbound hcaps.2.1 hcaps.1 _ fun stA minIdx hmin_lt hmin_le hrA0 hrA1 hrA2 hrA3 hrA4 hrA5 hrA6 hrA7 hrA8 hrA9 hrA11 hrA12 hrA13 hrA14 hrA15 hrA16 hrA19 hmA_K hmA_pres hzA3 hvA_2V hvA_nl hvA_one => ?_
  refine weights_phaseB_runs (Q_w := Q_w) hp hh hw hL1 hne hmin_lt hnl_list hnl_h hoK_h
    (fun e he => ⟨(hlen_nat e he).1, (hlen_nat e he).2.1, (hlen_nat e he).2.2.2.1⟩)
    (fun e he => ⟨(hwt_nat e he).1, (hwt_nat e he).2.1, (hwt_nat e he).2.2.2.1⟩)
    hlen_h hwt_h hG_edges hoK_nl_disj hoK_len_disj hoK_wt_disj hbound hcaps.2.2.1
    hrA0 hrA1 hrA2 hrA3 hrA4 hrA5 hrA6 hrA7 hrA8 hrA11 hrA12 hrA13 hrA14 hrA15 hrA16 hrA19
    hmA_K hmA_pres hzA3 hvA_one _ fun stB hregsB hrB19 hmB_K hmB_pres hmB_eq3 hzB hvB_lm hvB_S hvB_Sm1 => ?_
  let hp_sum := heap + 7 * K + nl.length * (2 * K)
  let hp_pre := heap + 13 * K + nl.length * (2 * K)
  let S_val := (nl.map vNat).sum
  let lmin_val := lNat (nl[minIdx]'hmin_lt)
  let stepCost := weightStepCost K + 33
  have hws_space : hp_pre + nl.length * weightStepSpace K = heap + weightsSpace nl.length K := by
    dsimp only [hp_pre, weightsSpace, weightStepSpace]
    ring
  have hS_pos : 1 ≤ S_val := by
    have hnl0 : 0 < nl.length := by dsimp only [nl]; exact hne
    have he0 : nl[0]'hnl0 ∈ nl := List.getElem_mem hnl0
    have hm0 := hwt_nat _ (hG_edges _ he0)
    have hle := List.single_le_sum (fun _ _ => Nat.zero_le _) (vNat (nl[0]'hnl0))
      (List.mem_map_of_mem he0)
    exact le_trans hm0.2.2.2.1 hle
  have hlm_pos : 1 ≤ lmin_val := (hlen_nat _ (hG_edges _ (List.getElem_mem hmin_lt))).2.2.2.1
  have hlm_le_all : ∀ e ∈ nl, lmin_val ≤ lNat e := by
    intro e he
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp he
    have hle := hmin_le j hj
    have hl1 := (hlen_nat _ (hG_edges _ (List.getElem_mem hmin_lt))).2.1
    have hl2 := (hlen_nat _ (hG_edges _ (List.getElem_mem hj))).2.1
    rw [hl1, hl2] at hle
    exact Int.ofNat_le.mp hle
  have hheap_le_hppre : heap + 13 * K ≤ hp_pre := by dsimp only [hp_pre]; omega
  have hheapK_le_hppre : heap + K + K ≤ hp_pre := by dsimp only [hp_pre]; omega
  have hheap4K_le_hppre : heap + 4 * K + 2 * K ≤ hp_pre := by dsimp only [hp_pre]; omega
  have hsum2K_ge_heap : heap ≤ hp_sum + 2 * K := by dsimp only [hp_sum]; omega
  have hsum2K_le_hppre : hp_sum + 2 * K + 2 * K ≤ hp_pre := by dsimp only [hp_sum, hp_pre]; omega
  have hsum4K_ge_heap : heap ≤ hp_sum + 4 * K := by dsimp only [hp_sum]; omega
  have hsum4K_le_hppre : hp_sum + 4 * K + 2 * K ≤ hp_pre := by dsimp only [hp_sum, hp_pre]; omega
  have hhppre_w : hp_pre < 2 ^ w :=
    lt_of_le_of_lt (Nat.le_add_right _ _) (hws_space ▸ hbound')
  have hheap_w : heap < 2 ^ w := lt_of_le_of_lt (by linarith only [hheap_le_hppre, hK1]) hhppre_w
  have hlenPtr_w : lenPtr < 2 ^ w := lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) hlen_h) hheap_w
  have hwtPtr_w : wtPtr < 2 ^ w := lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) hwt_h) hheap_w
  have hL_w : L < 2 ^ w := by omega
  have hK_w : K < 2 ^ w := by omega
  have hheap_w' : heap < 2 ^ w := hheap_w
  have hheapK_w : heap + K < 2 ^ w := by linarith only [hheapK_le_hppre, hhppre_w, hK1]
  have hheap4K_w : heap + 4 * K < 2 ^ w := by linarith only [hheap4K_le_hppre, hhppre_w, hK1]
  have hsum2K_w : hp_sum + 2 * K < 2 ^ w := by linarith only [hsum2K_le_hppre, hhppre_w, hK1]
  have hsum4K_w : hp_sum + 4 * K < 2 ^ w := by linarith only [hsum4K_le_hppre, hhppre_w, hK1]
  let loopInv : ℕ → State → Prop := fun i st =>
    WeightsRegs st nl.length nlPtr lenPtr wtPtr Vcnt L outMultPtr outWPtr outKPtr
      K (heap + K) heap (heap + 4 * K) (hp_sum + 2 * K) (hp_sum + 4 * K) ∧
    st.regs 19 = hp_pre + i * weightStepSpace K ∧
    st.regs 24 = i ∧
    ZeroFrom st.mem (hp_pre + i * weightStepSpace K) ∧
    st.mem outKPtr = K ∧
    (∀ a < heap,
      (∀ j < i, a ≠ outMultPtr + j ∧ (a < outWPtr + j * K ∨ outWPtr + (j + 1) * K ≤ a)) →
      a ≠ outKPtr → st.mem a = mem a) ∧
    (∀ a, heap ≤ a → a < hp_pre → st.mem a = stB.mem a) ∧
    (∀ (j : ℕ) (hj_nl : j < nl.length), j < i →
      st.mem (outMultPtr + j) = (nl.length * vNat (nl[j]'hj_nl) + S_val - 1) / S_val) ∧
    (∀ (j : ℕ) (hj_nl : j < nl.length), j < i →
      LimbsAt st.mem (outWPtr + j * K) K h ((2 * Vcnt * lNat (nl[j]'hj_nl)) / lmin_val))
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 24) (lo := .const 0) (hi := .reg 0)
    (body :=
      .assign 20 (.load (.bin .add (.reg 1) (.reg 24))) ;;
      .assign 21 (.bin .add (.reg 6) (.reg 24)) ;;
      .assign 22 (.bin .add (.reg 7) (.bin .mul (.reg 24) (.reg 11))) ;;
      .call 19 (b + idxWeightStep)
        [.reg 20, .reg 2, .reg 3, .reg 5, .reg 11, .reg 15, .reg 14, .reg 18, .reg 23, .reg 17,
         .reg 21, .reg 22, .reg 19])
    (P := fun st => st = stB) (Inv := loopInv) stepCost 0 nl.length (Nat.zero_le _) hw1 (fun _ => hnl_w)
    (fun st hst => by
      subst hst
      refine ⟨Expr.eval_const (Nat.lt_trans Nat.zero_lt_one hw1),
        weightsRegs_upd hregsB rfl (by decide), by dsimp only [hp_pre, nl, K]; simp [hrB19],
        by simp, by simpa using hzB,
        by simpa using hmB_K, fun a ha _ hne => by simpa using hmB_pres a ha hne,
        fun a _ _ => by simp, fun j _ hj => False.elim (Nat.not_lt_zero _ hj),
        fun j _ hj => False.elim (Nat.not_lt_zero _ hj)⟩)
    (fun _ st _ _ hi => hi.2.2.1)
    (fun _ st _ _ hi => Expr.eval_reg_of_eq hi.1.r0)
    (fun i _ hilt => by
      rintro st ω ⟨hregs, hr19, hr24, hz_i, hm_K_i, hpres_lt, hpres_mid, hmult_i, hw_i⟩
      have hi_w : i < 2 ^ w := lt_trans hilt hnl_w
      have hi1_le : i + 1 ≤ nl.length := hilt
      have hheap_i_w : hp_pre + i * weightStepSpace K + weightStepSpace K < 2 ^ w := by
        have hmul : (i + 1) * weightStepSpace K ≤ nl.length * weightStepSpace K :=
          Nat.mul_le_mul_right _ hilt
        rw [Nat.add_mul, Nat.one_mul] at hmul
        have hbw : hp_pre + nl.length * weightStepSpace K < 2 ^ w := by
          rw [hws_space]; exact hbound'
        linarith only [hmul, hbw]
      have hpre_i_w : hp_pre + i * weightStepSpace K < 2 ^ w :=
        lt_of_le_of_lt (Nat.le_add_right _ _) hheap_i_w
      have hnl_addr_w : nlPtr + i < 2 ^ w := by linarith only [hi1_le, hnl_h', hheap_w]
      have hom_addr_w : outMultPtr + i < 2 ^ w := by linarith only [hi1_le, hom_h, hheap_w]
      have hiK_w : i * K < 2 ^ w := by
        have h1 : i * K ≤ nl.length * K := Nat.mul_le_mul_right K (Nat.le_of_lt hilt)
        have h2 : nl.length * K ≤ outWPtr + nl.length * K := Nat.le_add_left _ _
        linarith only [h1, h2, how_h, hheap_w]
      have how_addr_w : outWPtr + i * K < 2 ^ w := by
        have h1 : (i + 1) * K ≤ nl.length * K := Nat.mul_le_mul_right K hilt
        rw [Nat.add_mul, Nat.one_mul] at h1
        linarith only [h1, how_h, hheap_w, hK1]
      have how_end_le : outWPtr + i * K + K ≤ heap := by
        have h1 : (i + 1) * K ≤ nl.length * K := Nat.mul_le_mul_right K hilt
        rw [Nat.add_mul, Nat.one_mul] at h1
        linarith only [h1, how_h]
      have he_mem : st.mem (nlPtr + i) = nl[i] := by
        have hlt : nlPtr + i < heap := by linarith only [hi1_le, hnl_h']
        have hdisj_past : ∀ j < i, nlPtr + i ≠ outMultPtr + j ∧
            (nlPtr + i < outWPtr + j * K ∨ outWPtr + (j + 1) * K ≤ nlPtr + i) := by
          intro j hj
          constructor
          · rcases hom_nl_disj with h1 | h1
            · apply ne_of_gt; dsimp only [nl] at hj hilt; linarith only [h1, hj, hilt, Nat.zero_le i]
            · apply ne_of_lt; dsimp only [nl] at hilt; linarith only [h1, hilt, Nat.zero_le j]
          · rcases how_nl_disj with h1 | h1
            · right
              have hle : (j + 1) * K ≤ nl.length * K := Nat.mul_le_mul_right K (by linarith only [hj, hilt])
              rw [Nat.add_mul, Nat.one_mul] at hle
              dsimp only [nl, K] at hle ⊢
              linarith only [h1, hle, Nat.zero_le i]
            · left; dsimp only [nl] at hilt; linarith only [h1, hilt, Nat.zero_le (j * K)]
        have hne_K : nlPtr + i ≠ outKPtr := by
          rcases hoK_nl_disj with h1 | h1
          · apply ne_of_gt; linarith only [h1, Nat.zero_le i]
          · apply ne_of_lt; dsimp only [nl] at hilt; linarith only [h1, hilt]
        rw [hpres_lt _ hlt hdisj_past hne_K, hnl_list i hilt]
      have he_m : nl[i] < G.m := hG_edges _ (List.getElem_mem hilt)
      have he_m_w : nl[i] < 2 ^ w :=
        lt_of_lt_of_le (lt_of_lt_of_le he_m (Nat.le_mul_of_pos_right G.m hL1))
          (le_trans (Nat.le_add_left _ _) (le_trans hlen_h hheap_w.le))
      have hmul_end_le : nl[i] * L + L ≤ G.m * L := by
        have h1 : (nl[i] + 1) * L ≤ G.m * L := Nat.mul_le_mul_right L he_m
        rwa [Nat.add_mul, Nat.one_mul] at h1
      have he_h_len : lenPtr + nl[i] * L + L ≤ heap := by linarith only [hmul_end_le, hlen_h]
      have he_h_wt : wtPtr + nl[i] * L + L ≤ heap := by linarith only [hmul_end_le, hwt_h]
      have hlen_valid_i : Num.Valid st.mem (lenPtr + nl[i] * L) h L ∧
          0 < Num.intVal st.mem (lenPtr + nl[i] * L) h L ∧
          Num.unsignedVal st.mem (lenPtr + nl[i] * L) h L = lNat (nl[i]) := by
        have heq : ∀ d < L, st.mem (lenPtr + nl[i] * L + d) = mem (lenPtr + nl[i] * L + d) := by
          intro d hd
          have hmul_lt : nl[i] * L + d < G.m * L := by linarith only [hmul_end_le, hd]
          have hdisj_past : ∀ j < i, lenPtr + nl[i] * L + d ≠ outMultPtr + j ∧
              (lenPtr + nl[i] * L + d < outWPtr + j * K ∨ outWPtr + (j + 1) * K ≤ lenPtr + nl[i] * L + d) := by
            intro j hj
            constructor
            · rcases hom_len_disj with h1 | h1
              · apply ne_of_gt; dsimp only [nl] at hj hilt
                linarith only [h1, hj, hilt, Nat.zero_le (nl[i] * L + d)]
              · apply ne_of_lt; linarith only [h1, hmul_lt, Nat.zero_le j]
            · rcases how_len_disj with h1 | h1
              · right
                have hle : (j + 1) * K ≤ nl.length * K := Nat.mul_le_mul_right K (by linarith only [hj, hilt])
                rw [Nat.add_mul, Nat.one_mul] at hle
                dsimp only [nl, K] at hle ⊢
                linarith only [h1, hle, Nat.zero_le (nl[i] * L + d)]
              · left; linarith only [h1, hmul_lt, Nat.zero_le (j * K)]
          have hne_K : lenPtr + nl[i] * L + d ≠ outKPtr := by
            rcases hoK_len_disj with h1 | h1
            · apply ne_of_gt; linarith only [h1, Nat.zero_le (nl[i] * L + d)]
            · apply ne_of_lt; linarith only [h1, hmul_lt]
          exact hpres_lt _ (by linarith only [he_h_len, hd]) hdisj_past hne_K
        have ho := hlen_nat _ he_m
        refine ⟨numValid_congr (fun d hd => (heq d hd).symm) ho.1, ?_, ?_⟩
        · rw [intVal_congr_range heq, ho.2.1]; exact_mod_cast ho.2.2.2.1
        · exact unsignedVal_congr_range heq
      have hwt_valid_i : Num.Valid st.mem (wtPtr + nl[i] * L) h L ∧
          0 < Num.intVal st.mem (wtPtr + nl[i] * L) h L ∧
          Num.unsignedVal st.mem (wtPtr + nl[i] * L) h L = vNat (nl[i]) := by
        have heq : ∀ d < L, st.mem (wtPtr + nl[i] * L + d) = mem (wtPtr + nl[i] * L + d) := by
          intro d hd
          have hmul_lt : nl[i] * L + d < G.m * L := by linarith only [hmul_end_le, hd]
          have hdisj_past : ∀ j < i, wtPtr + nl[i] * L + d ≠ outMultPtr + j ∧
              (wtPtr + nl[i] * L + d < outWPtr + j * K ∨ outWPtr + (j + 1) * K ≤ wtPtr + nl[i] * L + d) := by
            intro j hj
            constructor
            · rcases hom_wt_disj with h1 | h1
              · apply ne_of_gt; dsimp only [nl] at hj hilt
                linarith only [h1, hj, hilt, Nat.zero_le (nl[i] * L + d)]
              · apply ne_of_lt; linarith only [h1, hmul_lt, Nat.zero_le j]
            · rcases how_wt_disj with h1 | h1
              · right
                have hle : (j + 1) * K ≤ nl.length * K := Nat.mul_le_mul_right K (by linarith only [hj, hilt])
                rw [Nat.add_mul, Nat.one_mul] at hle
                dsimp only [nl, K] at hle ⊢
                linarith only [h1, hle, Nat.zero_le (nl[i] * L + d)]
              · left; linarith only [h1, hmul_lt, Nat.zero_le (j * K)]
          have hne_K : wtPtr + nl[i] * L + d ≠ outKPtr := by
            rcases hoK_wt_disj with h1 | h1
            · apply ne_of_gt; linarith only [h1, Nat.zero_le (nl[i] * L + d)]
            · apply ne_of_lt; linarith only [h1, hmul_lt]
          exact hpres_lt _ (by linarith only [he_h_wt, hd]) hdisj_past hne_K
        have ho := hwt_nat _ he_m
        refine ⟨numValid_congr (fun d hd => (heq d hd).symm) ho.1, ?_, ?_⟩
        · rw [intVal_congr_range heq, ho.2.1]; exact_mod_cast ho.2.2.2.1
        · exact unsignedVal_congr_range heq
      have hmid_val : ∀ a n, heap ≤ a → a + n ≤ hp_pre →
          (∀ d < n, st.mem (a + d) = stB.mem (a + d)) := fun a n ha han d hd =>
        hpres_mid (a + d) (by linarith only [ha]) (by linarith only [han, hd])
      have hv_nl_i : Num.Valid st.mem (heap + K) h K ∧ Num.intVal st.mem (heap + K) h K = (nl.length : ℤ) := by
        have heq := hmid_val (heap + K) K (Nat.le_add_right _ _) hheapK_le_hppre
        have hmA : ∀ d < K, stB.mem (heap + K + d) = stA.mem (heap + K + d) := fun d hd =>
          hmB_eq3 _ (by linarith only [hd])
        have hc : ∀ d < K, st.mem (heap + K + d) = stA.mem (heap + K + d) := fun d hd =>
          (heq d hd).trans (hmA d hd)
        exact ⟨numValid_congr (fun d hd => (hc d hd).symm) hvA_nl.1, by rw [intVal_congr_range hc, hvA_nl.2]⟩
      have hv_2V_i : Num.Valid st.mem heap h K ∧ Num.intVal st.mem heap h K = ((2 * Vcnt : ℕ) : ℤ) := by
        have heq := hmid_val heap K le_rfl (by linarith only [hheapK_le_hppre, hK1])
        have hmA : ∀ d < K, stB.mem (heap + d) = stA.mem (heap + d) := fun d hd => hmB_eq3 _ (by linarith only [hd, hK1])
        have hc : ∀ d < K, st.mem (heap + d) = stA.mem (heap + d) := fun d hd => (heq d hd).trans (hmA d hd)
        exact ⟨numValid_congr (fun d hd => (hc d hd).symm) hvA_2V.1, by rw [intVal_congr_range hc, hvA_2V.2]⟩
      have hv_S_i : Num.Valid st.mem (hp_sum + 2 * K) h (2 * K) ∧
          Num.intVal st.mem (hp_sum + 2 * K) h (2 * K) = (S_val : ℤ) := by
        have heq := hmid_val (hp_sum + 2 * K) (2 * K) hsum2K_ge_heap hsum2K_le_hppre
        exact ⟨numValid_congr (fun d hd => (heq d hd).symm) hvB_S.1, by rw [intVal_congr_range heq, hvB_S.2]⟩
      have hv_Sm1_i : Num.Valid st.mem (hp_sum + 4 * K) h (2 * K) ∧
          Num.intVal st.mem (hp_sum + 4 * K) h (2 * K) = ((S_val - 1 : ℕ) : ℤ) := by
        have heq := hmid_val (hp_sum + 4 * K) (2 * K) hsum4K_ge_heap hsum4K_le_hppre
        exact ⟨numValid_congr (fun d hd => (heq d hd).symm) hvB_Sm1.1, by rw [intVal_congr_range heq, hvB_Sm1.2]⟩
      have hv_lm_i : Num.Valid st.mem (heap + 4 * K) h (2 * K) ∧
          Num.intVal st.mem (heap + 4 * K) h (2 * K) = (lmin_val : ℤ) := by
        have heq := hmid_val (heap + 4 * K) (2 * K) (Nat.le_add_right _ _) hheap4K_le_hppre
        exact ⟨numValid_congr (fun d hd => (heq d hd).symm) hvB_lm.1, by rw [intVal_congr_range heq, hvB_lm.2]⟩
      have hv_le_S_i : Num.unsignedVal st.mem (wtPtr + nl[i] * L) h L ≤ S_val := by
        rw [hwt_valid_i.2.2]
        exact List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem (List.getElem_mem hilt))
      have hlm_le_i : lmin_val ≤ Num.unsignedVal st.mem (lenPtr + nl[i] * L) h L := by
        rw [hlen_valid_i.2.2]; exact hlm_le_all _ (List.getElem_mem hilt)
      have hnum1_cap_i : 2 * (nl.length * Num.unsignedVal st.mem (wtPtr + nl[i] * L) h L + (S_val - 1)) <
          Num.capacity h (2 * K) := by
        rw [hwt_valid_i.2.2]; exact hcaps.2.2.2.1 _ (List.getElem_mem hilt)
      have hw_cap_i : 2 * ((2 * Vcnt * Num.unsignedVal st.mem (lenPtr + nl[i] * L) h L) / lmin_val) <
          Num.capacity h K := by
        rw [hlen_valid_i.2.2]; exact (hcaps.2.2.2.2 _ (List.getElem_mem hilt) lmin_val hlm_pos).1
      have hdisj_omw_i : outMultPtr + i < outWPtr + i * K ∨ outWPtr + i * K + K ≤ outMultPtr + i := by
        rcases homw_disj with h1 | h1
        · exact Or.inl (by dsimp only [nl] at hilt; linarith only [h1, hilt, Nat.zero_le (i * K)])
        · have : (i + 1) * K ≤ nl.length * K := Nat.mul_le_mul_right K hilt
          rw [Nat.add_mul, Nat.one_mul] at this
          dsimp only [nl, K] at this
          exact Or.inr (by linarith only [h1, this, Nat.zero_le i])
      have hdisj_oml_i : outMultPtr + i < lenPtr + nl[i] * L ∨ lenPtr + nl[i] * L + L ≤ outMultPtr + i := by
        rcases hom_len_disj with h1 | h1
        · exact Or.inl (by dsimp only [nl] at hilt; linarith only [h1, hilt, Nat.zero_le (nl[i] * L)])
        · exact Or.inr (by linarith only [h1, hmul_end_le, Nat.zero_le i])
      refine runs_start_le ?_
      refine runs_seq_assign_step (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hregs.r1)
        (Expr.eval_reg_of_eq hr24) hnl_addr_w) he_mem) rfl fun s1 hm1 _ hr1_s => ?_
      have hregs1 := weightsRegs_upd hregs hr1_s (by decide)
      have hr1_19 : s1.regs 19 = hp_pre + i * weightStepSpace K := by
        rw [hr1_s, Function.update_of_ne (by decide), hr19]
      have hr1_20 : s1.regs 20 = nl[i] := by rw [hr1_s, Function.update_self]
      have hr1_24 : s1.regs 24 = i := by rw [hr1_s, Function.update_of_ne (by decide), hr24]
      refine runs_seq_assign_step (Expr.eval_add (Expr.eval_reg_of_eq hregs1.r6)
        (Expr.eval_reg_of_eq hr1_24) hom_addr_w) rfl fun s2 hm2 _ hr2_s => ?_
      have hregs2 := weightsRegs_upd hregs1 hr2_s (by decide)
      have hr2_19 : s2.regs 19 = hp_pre + i * weightStepSpace K := by
        rw [hr2_s, Function.update_of_ne (by decide), hr1_19]
      have hr2_20 : s2.regs 20 = nl[i] := by rw [hr2_s, Function.update_of_ne (by decide), hr1_20]
      have hr2_21 : s2.regs 21 = outMultPtr + i := by rw [hr2_s, Function.update_self]
      have hr2_24 : s2.regs 24 = i := by rw [hr2_s, Function.update_of_ne (by decide), hr1_24]
      refine runs_seq_assign_step (Expr.eval_add (Expr.eval_reg_of_eq hregs2.r7)
        (Expr.eval_mul (Expr.eval_reg_of_eq hr2_24) (Expr.eval_reg_of_eq hregs2.r11) hiK_w)
        how_addr_w) rfl fun s3 hm3 _ hr3_s => ?_
      have hregs3 := weightsRegs_upd hregs2 hr3_s (by decide)
      have hr3_19 : s3.regs 19 = hp_pre + i * weightStepSpace K := by
        rw [hr3_s, Function.update_of_ne (by decide), hr2_19]
      have hr3_20 : s3.regs 20 = nl[i] := by rw [hr3_s, Function.update_of_ne (by decide), hr2_20]
      have hr3_21 : s3.regs 21 = outMultPtr + i := by rw [hr3_s, Function.update_of_ne (by decide), hr2_21]
      have hr3_22 : s3.regs 22 = outWPtr + i * K := by rw [hr3_s, Function.update_self]
      have hr3_24 : s3.regs 24 = i := by rw [hr3_s, Function.update_of_ne (by decide), hr2_24]
      have hs3_mem : s3.mem = st.mem := hm3.trans (hm2.trans hm1)
      have hvs_lt : ∀ x ∈ [nl[i], lenPtr, wtPtr, L, K, heap + K, heap, hp_sum + 2 * K,
          hp_sum + 4 * K, heap + 4 * K, outMultPtr + i, outWPtr + i * K,
          hp_pre + i * weightStepSpace K], x < 2 ^ w := fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
        · exact he_m_w
        · exact hlenPtr_w
        · exact hwtPtr_w
        · exact hL_w
        · exact hK_w
        · exact hheapK_w
        · exact hheap_w'
        · exact hsum2K_w
        · exact hsum4K_w
        · exact hheap4K_w
        · exact hom_addr_w
        · exact how_addr_w
        · exact hpre_i_w
      have hpre_ws : (weightStepContract w h).pre [nl[i], lenPtr, wtPtr, L, K, heap + K, heap,
          hp_sum + 2 * K, hp_sum + 4 * K, heap + 4 * K, outMultPtr + i, outWPtr + i * K,
          hp_pre + i * weightStepSpace K] st.mem :=
        ⟨nl[i], lenPtr, wtPtr, L, K, heap + K, heap, hp_sum + 2 * K, hp_sum + 4 * K,
          heap + 4 * K, outMultPtr + i, outWPtr + i * K, hp_pre + i * weightStepSpace K,
          nl.length, Vcnt, S_val, lmin_val, rfl, hh, hw, hL1, hLK, hne, hnl_w, hV2,
          hlen_valid_i.1, hlen_valid_i.2.1, hwt_valid_i.1, hwt_valid_i.2.1,
          hv_nl_i.1, hv_nl_i.2, hv_2V_i.1, hv_2V_i.2, hv_S_i.1, hv_S_i.2, hS_pos,
          hv_Sm1_i.1, hv_Sm1_i.2, hv_lm_i.1, hv_lm_i.2, hlm_pos,
          hv_le_S_i, hlm_le_i, hcaps.1, hnum1_cap_i, hw_cap_i,
          by linarith only [he_h_len, hheap_le_hppre, hK1, Nat.zero_le (i * weightStepSpace K)],
          by linarith only [he_h_wt, hheap_le_hppre, hK1, Nat.zero_le (i * weightStepSpace K)],
          by linarith only [hheapK_le_hppre, hK1, Nat.zero_le (i * weightStepSpace K)],
          by linarith only [hheapK_le_hppre, hK1, Nat.zero_le (i * weightStepSpace K)],
          by linarith only [hsum2K_le_hppre, hK1, Nat.zero_le (i * weightStepSpace K)],
          by linarith only [hsum4K_le_hppre, Nat.zero_le (i * weightStepSpace K)],
          by linarith only [hheap4K_le_hppre, Nat.zero_le (i * weightStepSpace K)],
          by dsimp only [nl] at hi1_le; linarith only [hi1_le, hom_h, hheap_le_hppre, hK1, Nat.zero_le (i * weightStepSpace K)],
          by linarith only [how_end_le, hheap_le_hppre, hK1, Nat.zero_le (i * weightStepSpace K)],
          hdisj_omw_i, hdisj_oml_i,
          Or.inl (by dsimp only [nl] at hi1_le; linarith only [hi1_le, hom_h]),
          Or.inl (by dsimp only [nl] at hi1_le; linarith only [hi1_le, hom_h, Nat.zero_le (4 * K)]),
          hz_i, hheap_i_w⟩
      rcases runs_call_of_meetsContract (r := 19) hws_mc
          (evalArgs_cons (Expr.eval_reg_of_eq hr3_20)
            (evalArgs_cons (Expr.eval_reg_of_eq hregs3.r2)
              (evalArgs_cons (Expr.eval_reg_of_eq hregs3.r3)
                (evalArgs_cons (Expr.eval_reg_of_eq hregs3.r5)
                  (evalArgs_cons (Expr.eval_reg_of_eq hregs3.r11)
                    (evalArgs_cons (Expr.eval_reg_of_eq hregs3.r15)
                      (evalArgs_cons (Expr.eval_reg_of_eq hregs3.r14)
                        (evalArgs_cons (Expr.eval_reg_of_eq hregs3.r18)
                          (evalArgs_cons (Expr.eval_reg_of_eq hregs3.r23)
                            (evalArgs_cons (Expr.eval_reg_of_eq hregs3.r17)
                              (evalArgs_cons (Expr.eval_reg_of_eq hr3_21)
                                (evalArgs_cons (Expr.eval_reg_of_eq hr3_22)
                                  (evalArgs_cons (Expr.eval_reg_of_eq hr3_19)
                                    (evalArgs_nil _ _))))))))))))))
          hvs_lt (hs3_mem ▸ hpre_ws) ω with
        ⟨s4, c, hp_next, hrun, hpost, hr4_19', hr4_other, hc⟩
      have hr4_s : s4.regs = Function.update s3.regs 19 hp_next := by
        funext r'; by_cases h19 : r' = 19
        · subst h19; simp [hr4_19']
        · simp [h19, hr4_other r' h19]
      let mem' : ℕ → ℕ := s4.mem
      rw [hs3_mem] at hpost
      obtain ⟨e', lenP', wtP', L', K', nlk', tvk', sk', smk', lmk', omP', owP', hpP',
        nlc', vcnt', sval', lmval', hargs_eq, h_nlc, h_vcnt, h_sval, h_lmval,
        hret_eq, hz_next, hfr_next, hmult_next, hw_next⟩ := hpost
      simp only [List.cons.injEq, and_true] at hargs_eq
      rcases hargs_eq with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      have hnlc_eq : nlc' = nl.length := by
        exact Int.ofNat.inj (h_nlc.symm.trans hv_nl_i.2)
      have hvcnt_eq : vcnt' = Vcnt := by
        have h2 := Int.ofNat.inj (h_vcnt.symm.trans hv_2V_i.2)
        linarith only [h2]
      have hsval_eq : sval' = S_val := by
        exact Int.ofNat.inj (h_sval.symm.trans hv_S_i.2)
      have hlmval_eq : lmval' = lmin_val := by
        exact Int.ofNat.inj (h_lmval.symm.trans hv_lm_i.2)
      subst hnlc_eq hvcnt_eq hsval_eq hlmval_eq
      have hr4_19 : s4.regs 19 = hp_pre + (i + 1) * weightStepSpace K := by
        rw [hr4_s, hret_eq, Function.update_self, Nat.add_mul, Nat.one_mul]; ring
      have hregs4 := weightsRegs_upd hregs3 hr4_s (by decide)
      have hr4_24 : s4.regs 24 = i := by
        rw [hr4_s, Function.update_of_ne (by decide), hr3_24]
      have hw_next_u : LimbsAt mem' (outWPtr + i * K) K h
          ((2 * Vcnt * lNat (nl[i]'hilt)) / lmin_val) := by
        rwa [← hlen_valid_i.2.2]
      have hmult_next_u : mem' (outMultPtr + i) =
          (nl.length * vNat (nl[i]'hilt) + S_val - 1) / S_val := by
        rwa [← hwt_valid_i.2.2]
      have ha_lt_next : hp_pre ≤ hp_pre + i * weightStepSpace K := Nat.le_add_right _ _
      refine ⟨.normal, s4, c, hrun, ⟨⟨weightsRegs_upd hregs4 rfl (by decide), ?_, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩, hr4_24⟩, ?_⟩
      · simp [hr4_19]
      · rw [hret_eq] at hz_next
        simpa [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hz_next
      · simp only
        have hok_lt_next : outKPtr < hp_pre + i * weightStepSpace K :=
          lt_of_lt_of_le (lt_of_lt_of_le hoK_h (by linarith only [hheap_le_hppre, hK1])) ha_lt_next
        have hok_om : outKPtr ≠ outMultPtr + i := by
          rcases homK_disj with h1 | h1
          · apply ne_of_gt; dsimp only [nl] at hilt; linarith only [h1, hilt]
          · apply ne_of_lt; linarith only [h1, Nat.zero_le i]
        have hok_ow : outKPtr < outWPtr + i * K ∨ outWPtr + i * K + K ≤ outKPtr := by
          rcases howK_disj with h1 | h1
          · right; have : (i + 1) * K ≤ nl.length * K := Nat.mul_le_mul_right K hilt
            rw [Nat.add_mul, Nat.one_mul] at this
            dsimp only [nl, K] at this
            linarith only [h1, this]
          · left; linarith only [h1, Nat.zero_le (i * K)]
        rw [hfr_next outKPtr hok_lt_next hok_om hok_ow]
        exact hm_K_i
      · intro a ha hdisj hneK
        have ha_lt_heap_i : a < hp_pre + i * weightStepSpace K :=
          lt_of_lt_of_le ha (le_trans (by linarith only [hheap_le_hppre, hK1]) ha_lt_next)
        have hdisj_i := hdisj i (Nat.lt_succ_self i)
        have hdisj_prev : ∀ j < i, a ≠ outMultPtr + j ∧
            (a < outWPtr + j * K ∨ outWPtr + (j + 1) * K ≤ a) := fun j hj =>
          hdisj j (Nat.lt_trans hj (Nat.lt_succ_self i))
        have hnow := hfr_next a ha_lt_heap_i hdisj_i.1
          (by rcases hdisj_i.2 with h1 | h1
              · left; exact h1
              · right; rw [Nat.add_mul, Nat.one_mul] at h1; linarith only [h1])
        exact hnow.trans (hpres_lt a ha hdisj_prev hneK)
      · intro a ha1 ha2
        have ha_lt_heap_i : a < hp_pre + i * weightStepSpace K := lt_of_lt_of_le ha2 ha_lt_next
        have hne_om : a ≠ outMultPtr + i := ne_of_gt (by linarith only [ha1, hom_h, hilt])
        have hdisj_ow : a < outWPtr + i * K ∨ outWPtr + i * K + K ≤ a :=
          Or.inr (le_trans how_end_le ha1)
        exact (hfr_next a ha_lt_heap_i hne_om hdisj_ow).trans (hpres_mid a ha1 ha2)
      · intro j hj_nl hj
        by_cases hji : j = i
        · subst hji; exact hmult_next_u
        · have hj_lt : j < i := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hj) hji
          have hlt_hp : outMultPtr + j < hp_pre + i * weightStepSpace K :=
            lt_of_lt_of_le (by dsimp only [nl] at hj_lt hilt; linarith only [hom_h, hj_lt, hilt, hheap_le_hppre, hK1]) ha_lt_next
          have hdisj_w : outMultPtr + j < outWPtr + i * K ∨ outWPtr + i * K + K ≤ outMultPtr + j := by
            rcases homw_disj with h1 | h1
            · left; dsimp only [nl] at hj_lt hilt; linarith only [h1, hj_lt, hilt, Nat.zero_le (i * K)]
            · right; have : (i + 1) * K ≤ nl.length * K := Nat.mul_le_mul_right K hilt
              rw [Nat.add_mul, Nat.one_mul] at this
              dsimp only [nl, K] at this
              linarith only [h1, this, Nat.zero_le j]
          rw [hfr_next _ hlt_hp (ne_of_lt (by linarith only [hj_lt])) hdisj_w]
          exact hmult_i j hj_nl hj_lt
      · intro j hj_nl hj
        by_cases hji : j = i
        · subst hji; exact hw_next_u
        · have hj_lt : j < i := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hj) hji
          refine (hw_i j hj_nl hj_lt).congr fun k hk1 hk2 => ?_
          have hjK_le : (j + 1) * K ≤ i * K := Nat.mul_le_mul_right K hj_lt
          rw [Nat.add_mul, Nat.one_mul] at hjK_le
          have hjn : (j + 1) * K ≤ nl.length * K := Nat.mul_le_mul_right K (by linarith only [hj_lt, hilt])
          rw [Nat.add_mul, Nat.one_mul] at hjn
          have hlt_hp : k < hp_pre + i * weightStepSpace K :=
            lt_of_lt_of_le (by dsimp only [nl, K] at hjn; linarith only [how_h, hjn, hk2, hheap_le_hppre, hK1]) ha_lt_next
          have hne_om : k ≠ outMultPtr + i := by
            rcases homw_disj with h1 | h1
            · apply ne_of_gt; dsimp only [nl] at hilt; linarith only [h1, hilt, hk1, Nat.zero_le (j * K)]
            · apply ne_of_lt; dsimp only [nl, K] at hjn; linarith only [h1, hjn, hk2, Nat.zero_le i]
          exact hfr_next k hlt_hp hne_om (Or.inl (by linarith only [hjK_le, hk2]))
      · dsimp only [stepCost, weightStepContract] at hc ⊢
        simp only [argsSize, Expr.size, List.getD, List.getElem?_cons_succ,
          List.getElem?_cons_zero, Option.getD_some, Nat.add_zero] at hc ⊢
        linarith only [hc])
  refine runs_start_le ?_
  refine runs_seq_triple_le (hloop.conseq (fun _ h => h) (fun o st hq => by
    cases o with
    | returned _ => exact False.elim hq
    | normal => exact hq) (fun _ _ => le_rfl)) rfl ?_
  rintro st_end ⟨_, hr19_end, _, hz_end, hm_K_end, hpres_end, _, hmult_end, hw_end⟩
  have hret_val : st_end.regs 19 = heap + weightsSpace nl.length K := by
    rw [hr19_end, hws_space]
  refine runs_ret_le (Expr.eval_reg_of_eq hret_val) ?_ ?_
  · let multFn : ℕ → ℕ := fun e => (nl.length * vNat e + S_val - 1) / S_val
    let wOrigFn : ℕ → ℕ := fun e => (2 * Vcnt * lNat e) / lmin_val
    let δ : ℝ := (lmin_val : ℝ) / ((2 : ℝ) ^ P * (2 * (Vcnt : ℝ)))
    have hstretch := stretch_ineq_from_nat (G := G) (ℓ := ℓ) (lNat := lNat) (P := P) (minIdx := minIdx)
      hG hne hmin_lt (fun e he => (hlen_nat e (hG_edges e he)).2.2.2.1)
      (fun e he => (hlen_nat e (hG_edges e he)).2.2.2.2) hlm_le_all
    refine ⟨rfl, hm_K_end, hws_space ▸ hz_end, ?_, multFn, wOrigFn, δ,
      (fun j hj => hmult_end j hj hj), (fun j hj => hw_end j hj hj), ?_, ?_,
      hstretch.1, ?_, hstretch.2.2.1, hstretch.2.2.2.1, hstretch.2.2.2.2⟩
    · intro a ha hom how hoK
      refine hpres_end a ha (fun j hj => ⟨?_, ?_⟩) hoK
      · rcases hom with h1 | h1
        · exact ne_of_lt (lt_of_lt_of_le h1 (Nat.le_add_right _ _))
        · exact ne_of_gt (by dsimp only [nl] at hj; linarith only [h1, hj])
      · rcases how with h1 | h1
        · left; linarith only [h1, Nat.zero_le (j * K)]
        · right; have : (j + 1) * K ≤ nl.length * K := Nat.mul_le_mul_right K hj
          rw [Nat.add_mul, Nat.one_mul] at this
          dsimp only [nl, K] at this ⊢
          linarith only [h1, this]
    · intro e he
      exact (edgeMult_eq_nat (fun x hx => (hwt_nat x (hG_edges x hx)).2.2.2.1)
        (fun x hx => (hwt_nat x (hG_edges x hx)).2.2.2.2) he).2.1.symm
    · intro e he
      have hem := edgeMult_eq_nat (fun x hx => (hwt_nat x (hG_edges x hx)).2.2.2.1)
        (fun x hx => (hwt_nat x (hG_edges x hx)).2.2.2.2) he
      exact ⟨hem.2.2.1, hem.2.2.2⟩
    · intro e he
      exact ⟨hstretch.2.1 e he, (hcaps.2.2.2.2 e he lmin_val hlm_pos).2⟩
  · dsimp only [stepCost, Expr.size]
    simp only [Nat.sub_zero]
    linarith

theorem weights_meetsContract {w b h : ℕ} {p : Program}
    (hp : p.HasAt b (weightsModule b h)) :
    MeetsContract w p (b + idxWeightsEntry) (weightsContract w h) := by
  have hentry : p.procs[b + idxWeightsEntry]? = some (weightsProc b) := by
    have := hp 0 (by rw [weightsModule_length]; omega)
    simpa [weightsModule, idxWeightsEntry] using this
  refine meetsContract_of_runs hentry ?_
  rintro args mem pos ω hwords ⟨G, v, ℓ, nlPtr, lenPtr, wtPtr, L, P, outMultPtr, outWPtr, outKPtr, heap,
    rfl, hG, hL1, hh, hw, hne, hnl_list, hlen_pre, hwt_pre, hnl_h, hlen_h, hwt_h,
    hom_h, how_h, hoK_h, homw_disj, homK_disj, howK_disj, hom_nl_disj, hom_len_disj, hom_wt_disj,
    how_nl_disj, how_len_disj, how_wt_disj, hoK_nl_disj, hoK_len_disj, hoK_wt_disj, hz0, hbound⟩
  obtain ⟨st'', c, hrun, hmK, hz, hfr, hrest, hc⟩ :=
    weights_runs (ω := ω) (pos := pos) hp G v ℓ nlPtr lenPtr wtPtr L P outMultPtr outWPtr outKPtr heap
      hwords hG hL1 hh hw hne hnl_list hlen_pre hwt_pre hnl_h hlen_h hwt_h hom_h how_h hoK_h
      homw_disj homK_disj howK_disj hom_nl_disj hom_len_disj hom_wt_disj
      how_nl_disj how_len_disj how_wt_disj hoK_nl_disj hoK_len_disj hoK_wt_disj hz0 hbound
  refine ⟨.returned (heap + weightsSpace (nonloopEdges G).length (kWidthOf (nonloopEdges G).length L)),
    st'', c, hrun, ⟨G, v, ℓ, nlPtr, lenPtr, wtPtr, L, P, outMultPtr, outWPtr, outKPtr, heap,
      rfl, rfl, hmK, hz, hfr, hrest⟩, ?_⟩
  dsimp only [weightsContract]
  simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  exact hc

end MinCostFlow.WideWord
