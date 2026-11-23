module

public import MinCostFlow.Machine.WideWord.LSSTEncodeGAugBase
import WordRAM.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Verified contract for `encodeGAugProc`

This module proves the loop phase (`encodeGAug_copies_runs`) and main contract theorem
`encodeGAug_meetsContract` for `encodeGAugProc`.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM

private lemma encodeGAug_copies_runs {w encodeBase h : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem : ℕ → ℕ} {st₆ : State} {G : IndexedGraph} {V_list B : List ℕ} {mult w_orig : ℕ → ℕ}
    {nlArr tailArr headArr vIdxPtr multArr wArr K bArr L_sim origPtr outArr : ℕ}
    {k_cost T : ℕ} {Q : Outcome → State → Prop}
    (hec_mc : MeetsContract w p (encodeBase + idxEncodeEdgeCopies) (encodeEdgeCopiesContract w h))
    (hG : G.Valid) (hV_mem : ∀ e ∈ nonloopEdges G, G.tail e ∈ V_list ∧ G.head e ∈ V_list)
    (hh : 1 ≤ h) (hw2 : 2 * h + 2 ≤ w) (hw1 : 1 < 2 ^ w) (hK1 : 1 ≤ K) (hKL : K ≤ L_sim)
    (hV_lt : V_list.length < 2 ^ (L_sim * h)) (hmB_w : ((nonloopEdges G).map mult).sum + B.length < 2 ^ w)
    (hnl_w : nlArr + (nonloopEdges G).length < 2 ^ w) (htl_w : tailArr + G.m < 2 ^ w) (hhd_w : headArr + G.m < 2 ^ w)
    (hvIdx_w : vIdxPtr + G.n < 2 ^ w) (hmul_w : multArr + (nonloopEdges G).length < 2 ^ w)
    (hwArr_w : wArr + (nonloopEdges G).length * K < 2 ^ w)
    (horig_w : origPtr + ((nonloopEdges G).map mult).sum < 2 ^ w)
    (hout_w : outArr + (2 + 3 * (((nonloopEdges G).map mult).sum + B.length)) * L_sim < 2 ^ w)
    (hL_w : L_sim < 2 ^ w) (hK_w : K < 2 ^ w) (hB2h_w : 2 ^ h < 2 ^ w) (hV_w : V_list.length < 2 ^ w)
    (hd_out_nl : DisjointRanges outArr ((2 + 3 * (((nonloopEdges G).map mult).sum + B.length)) * L_sim) nlArr (nonloopEdges G).length)
    (hd_out_tl : DisjointRanges outArr ((2 + 3 * (((nonloopEdges G).map mult).sum + B.length)) * L_sim) tailArr G.m)
    (hd_out_hd : DisjointRanges outArr ((2 + 3 * (((nonloopEdges G).map mult).sum + B.length)) * L_sim) headArr G.m)
    (hd_out_vIdx : DisjointRanges outArr ((2 + 3 * (((nonloopEdges G).map mult).sum + B.length)) * L_sim) vIdxPtr G.n)
    (hd_out_mult : DisjointRanges outArr ((2 + 3 * (((nonloopEdges G).map mult).sum + B.length)) * L_sim) multArr (nonloopEdges G).length)
    (hd_out_w : DisjointRanges outArr ((2 + 3 * (((nonloopEdges G).map mult).sum + B.length)) * L_sim) wArr ((nonloopEdges G).length * K))
    (hd_orig_out : DisjointRanges origPtr ((nonloopEdges G).map mult).sum outArr ((2 + 3 * (((nonloopEdges G).map mult).sum + B.length)) * L_sim))
    (hd_orig_nl : DisjointRanges origPtr ((nonloopEdges G).map mult).sum nlArr (nonloopEdges G).length)
    (hd_orig_tl : DisjointRanges origPtr ((nonloopEdges G).map mult).sum tailArr G.m)
    (hd_orig_hd : DisjointRanges origPtr ((nonloopEdges G).map mult).sum headArr G.m)
    (hd_orig_vIdx : DisjointRanges origPtr ((nonloopEdges G).map mult).sum vIdxPtr G.n)
    (hd_orig_mult : DisjointRanges origPtr ((nonloopEdges G).map mult).sum multArr (nonloopEdges G).length)
    (hd_orig_w : DisjointRanges origPtr ((nonloopEdges G).map mult).sum wArr ((nonloopEdges G).length * K))
    (hnl_list : ListAt mem nlArr (nonloopEdges G))
    (htl_list : ListAt mem tailArr (List.ofFn fun i : Fin G.m => G.tail i))
    (hhd_list : ListAt mem headArr (List.ofFn fun i : Fin G.m => G.head i))
    (hvIdx_spec : ∀ u ∈ V_list, mem (vIdxPtr + u) = V_list.idxOf u)
    (hmult_spec : ∀ j (hj : j < (nonloopEdges G).length), mem (multArr + j) = mult ((nonloopEdges G)[j]'hj))
    (hw_spec : ∀ j (hj : j < (nonloopEdges G).length), LimbsAt mem (wArr + j * K) K h (w_orig ((nonloopEdges G)[j]'hj)))
    (hregs6 : EGAugRegs st₆ (nonloopEdges G).length nlArr tailArr headArr vIdxPtr multArr wArr K V_list.length B.length bArr L_sim (2 ^ h) origPtr outArr)
    (hr15_6 : st₆.regs 15 = ((nonloopEdges G).map mult).sum)
    (hr17_6 : st₆.regs 17 = outArr + 2 * L_sim) (hr18_6 : st₆.regs 18 = 0)
    (hfr6 : ∀ a, a < outArr ∨ outArr + 2 * L_sim ≤ a → st₆.mem a = mem a)
    (hrest : ∀ st₇ : State,
      EGAugRegs st₇ (nonloopEdges G).length nlArr tailArr headArr vIdxPtr multArr wArr K V_list.length B.length bArr L_sim (2 ^ h) origPtr outArr →
      st₇.regs 15 = ((nonloopEdges G).map mult).sum →
      st₇.regs 17 = outArr + (2 + 3 * ((nonloopEdges G).map mult).sum) * L_sim →
      ListAt st₇.mem origPtr (origOfCopy G mult) →
      (∀ (j : ℕ) (hj : j < (nonloopEdges G).length) (c : ℕ), c < mult ((nonloopEdges G)[j]'hj) →
        let idx := (((nonloopEdges G).take j).map mult).sum + c
        LimbsAt st₇.mem (outArr + (2 + 3 * idx) * L_sim) L_sim h (V_list.idxOf (G.tail ((nonloopEdges G)[j]'hj))) ∧
        LimbsAt st₇.mem (outArr + (2 + 3 * idx + 1) * L_sim) L_sim h (V_list.idxOf (G.head ((nonloopEdges G)[j]'hj))) ∧
        LimbsAt st₇.mem (outArr + (2 + 3 * idx + 2) * L_sim) L_sim h (w_orig ((nonloopEdges G)[j]'hj))) →
      (∀ a, a < outArr + 2 * L_sim ∨ outArr + (2 + 3 * ((nonloopEdges G).map mult).sum) * L_sim ≤ a →
        a < origPtr ∨ origPtr + ((nonloopEdges G).map mult).sum ≤ a → st₇.mem a = st₆.mem a) →
      ∃ o st' c,
        Runs w p ω
          (.call 17 (encodeBase + idxEncodeBridges) [.reg 9, .reg 10, .reg 4, .reg 11, .reg 12, .reg 17] ;;
           .ret (.reg 15))
          st₇ o st' c ∧ Q o st' ∧
        (k_cost + (((nonloopEdges G).map mult).sum * (70 * L_sim + 110) + 90 * (nonloopEdges G).length + 10)) + c ≤ T) :
    ∃ o st' c,
      Runs w p ω
        (forRange 19 (.const 0) (.reg 0)
          (.assign 20 (.load (.bin .add (.reg 1) (.reg 19))) ;;
           .assign 21 (.load (.bin .add (.reg 2) (.reg 20))) ;;
           .assign 21 (.load (.bin .add (.reg 4) (.reg 21))) ;;
           .assign 22 (.load (.bin .add (.reg 3) (.reg 20))) ;;
           .assign 22 (.load (.bin .add (.reg 4) (.reg 22))) ;;
           .assign 23 (.bin .add (.reg 6) (.bin .mul (.reg 19) (.reg 7))) ;;
           .assign 24 (.load (.bin .add (.reg 5) (.reg 19))) ;;
           .call 17 (encodeBase + idxEncodeEdgeCopies)
             [.reg 21, .reg 22, .reg 23, .reg 7, .reg 24, .reg 11, .reg 12, .reg 17, .reg 13, .reg 18, .reg 20] ;;
           .assign 18 (.bin .add (.reg 18) (.reg 24))) ;;
         .call 17 (encodeBase + idxEncodeBridges) [.reg 9, .reg 10, .reg 4, .reg 11, .reg 12, .reg 17] ;;
         .ret (.reg 15))
        st₆ o st' c ∧ Q o st' ∧ k_cost + c ≤ T := by
  let nl := nonloopEdges G
  let m₁ := (nl.map mult).sum
  let encLen := 2 + 3 * (m₁ + B.length)
  have h1L : 1 ≤ L_sim := le_trans hK1 hKL
  have hm₁_w : m₁ < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right _ B.length) hmB_w
  have hnl_len_w : nl.length < 2 ^ w := lt_of_le_of_lt (Nat.le_add_left _ _) hnl_w
  have hm_w : G.m < 2 ^ w := lt_of_le_of_lt (Nat.le_add_left _ _) htl_w
  have hn_w : G.n < 2 ^ w := lt_of_le_of_lt (Nat.le_add_left _ _) hvIdx_w
  have h2m1_le : (2 + 3 * m₁) * L_sim ≤ encLen * L_sim :=
    Nat.mul_le_mul_right L_sim (by dsimp only [encLen]; omega)
  have h2_le_enc : 2 * L_sim ≤ encLen * L_sim :=
    Nat.mul_le_mul_right L_sim (by dsimp only [encLen]; omega)
  let stepCost : ℕ → ℕ := fun j =>
    (if hj : j < nl.length then mult (nl[j]'hj) else 0) * (70 * L_sim + 110) + 81
  let loopInv : ℕ → State → Prop := fun j st =>
    let origIdx := ((nl.take j).map mult).sum
    EGAugRegs st nl.length nlArr tailArr headArr vIdxPtr multArr wArr K V_list.length B.length bArr L_sim (2 ^ h) origPtr outArr ∧
    st.regs 15 = m₁ ∧
    st.regs 17 = outArr + (2 + 3 * origIdx) * L_sim ∧
    st.regs 18 = origIdx ∧
    st.regs 19 = j ∧
    (∀ (t : ℕ) (ht : t < nl.length), t < j → ∀ c < mult (nl[t]'ht),
      st.mem (origPtr + ((nl.take t).map mult).sum + c) = nl[t]'ht) ∧
    (∀ (t : ℕ) (ht : t < nl.length), t < j → ∀ c < mult (nl[t]'ht),
      let idx := ((nl.take t).map mult).sum + c
      LimbsAt st.mem (outArr + (2 + 3 * idx) * L_sim) L_sim h (V_list.idxOf (G.tail (nl[t]'ht))) ∧
      LimbsAt st.mem (outArr + (2 + 3 * idx + 1) * L_sim) L_sim h (V_list.idxOf (G.head (nl[t]'ht))) ∧
      LimbsAt st.mem (outArr + (2 + 3 * idx + 2) * L_sim) L_sim h (w_orig (nl[t]'ht))) ∧
    (∀ a, a < outArr + 2 * L_sim ∨ outArr + (2 + 3 * origIdx) * L_sim ≤ a →
      a < origPtr ∨ origPtr + origIdx ≤ a → st.mem a = st₆.mem a)
  have hloop := Triple.forRange_le (w := w) (p := p) (r := 19) (lo := .const 0) (hi := .reg 0)
    (body :=
      .assign 20 (.load (.bin .add (.reg 1) (.reg 19))) ;;
      .assign 21 (.load (.bin .add (.reg 2) (.reg 20))) ;;
      .assign 21 (.load (.bin .add (.reg 4) (.reg 21))) ;;
      .assign 22 (.load (.bin .add (.reg 3) (.reg 20))) ;;
      .assign 22 (.load (.bin .add (.reg 4) (.reg 22))) ;;
      .assign 23 (.bin .add (.reg 6) (.bin .mul (.reg 19) (.reg 7))) ;;
      .assign 24 (.load (.bin .add (.reg 5) (.reg 19))) ;;
      .call 17 (encodeBase + idxEncodeEdgeCopies)
        [.reg 21, .reg 22, .reg 23, .reg 7, .reg 24, .reg 11, .reg 12, .reg 17, .reg 13, .reg 18, .reg 20] ;;
      .assign 18 (.bin .add (.reg 18) (.reg 24)))
    (P := fun st => st = st₆) (Inv := loopInv) stepCost 0 nl.length (Nat.zero_le _) hw1 (fun _ => hnl_len_w)
    (fun st hst => by
      rw [hst]
      refine ⟨Expr.eval_const (Nat.lt_trans Nat.zero_lt_one hw1), ?_⟩
      dsimp only [loopInv]
      refine ⟨egAugRegs_upd hregs6 rfl (by decide),
        by rw [Function.update_of_ne (by decide)]; exact hr15_6,
        by rw [Function.update_of_ne (by decide), hr17_6]; simp,
        by rw [Function.update_of_ne (by decide), hr18_6]; simp,
        by simp, fun _ _ h => False.elim (Nat.not_lt_zero _ h),
        fun _ _ h => False.elim (Nat.not_lt_zero _ h), fun _ _ _ => rfl⟩)
    (fun _ st _ _ hi => hi.2.2.2.2.1)
    (fun _ st _ _ hi => Expr.eval_reg_of_eq hi.1.r0)
    (fun j _ hj => by
      intro st ω hInv
      have hregs := hInv.1
      have hr15 := hInv.2.1
      have hr17 := hInv.2.2.1
      have hr18 := hInv.2.2.2.1
      have hr19 := hInv.2.2.2.2.1
      have hm_orig := hInv.2.2.2.2.2.1
      have hm_limbs := hInv.2.2.2.2.2.2.1
      have hfr_st := hInv.2.2.2.2.2.2.2
      let origIdx := ((nl.take j).map mult).sum
      let e := nl[j]'hj
      let cnt := mult e
      let posJ := outArr + (2 + 3 * origIdx) * L_sim
      have hcnt_step := take_map_sum_succ_le nl mult hj
      have hm1_j1 : origIdx + cnt ≤ m₁ := by dsimp only [origIdx, cnt, e, m₁]; omega
      have hm1_j1' : origIdx + cnt ≤ ((nonloopEdges G).map mult).sum := hm1_j1
      have hposJ_def : posJ = outArr + (2 + 3 * origIdx) * L_sim := rfl
      have hposJ_end : posJ + cnt * (3 * L_sim) = outArr + (2 + 3 * (origIdx + cnt)) * L_sim := by
        dsimp only [posJ]; ring
      have henc_j1 : (2 + 3 * (origIdx + cnt)) * L_sim ≤ encLen * L_sim :=
        Nat.mul_le_mul_right L_sim (by dsimp only [encLen]; linarith only [hm1_j1])
      have henc_j1' : (2 + 3 * (origIdx + cnt)) * L_sim ≤
          (2 + 3 * (((nonloopEdges G).map mult).sum + B.length)) * L_sim := henc_j1
      have henc_j_le : (2 + 3 * origIdx) * L_sim ≤ encLen * L_sim :=
        Nat.mul_le_mul_right L_sim (by dsimp only [encLen]; linarith only [hm1_j1, Nat.zero_le cnt, Nat.zero_le B.length])
      have hposJ_end_w : posJ + cnt * (3 * L_sim) < 2 ^ w := by
        linarith only [hout_w, hposJ_end, henc_j1']
      have hposJ_w : posJ < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right _ _) hposJ_end_w
      have he_nl : e ∈ nl := List.getElem_mem hj
      have he_m : e < G.m := (mem_nonloopEdges_iff.mp he_nl).1
      have he_w : e < 2 ^ w := lt_trans he_m hm_w
      have hu_lt_V : G.tail e ∈ V_list := (hV_mem e he_nl).1
      have hv_lt_V : G.head e ∈ V_list := (hV_mem e he_nl).2
      have htail_lt : G.tail e < G.n := (hG.2 e he_m).1
      have hhead_lt : G.head e < G.n := (hG.2 e he_m).2
      have htail_w : G.tail e < 2 ^ w := lt_trans htail_lt hn_w
      have hhead_w : G.head e < 2 ^ w := lt_trans hhead_lt hn_w
      have hvIdxPtr_w : vIdxPtr + G.n < 2 ^ w := hvIdx_w
      let uIdx := V_list.idxOf (G.tail e)
      let vIdx := V_list.idxOf (G.head e)
      have huIdx_lt : uIdx < V_list.length := List.idxOf_lt_length_of_mem hu_lt_V
      have hvIdx_lt : vIdx < V_list.length := List.idxOf_lt_length_of_mem hv_lt_V
      have huIdx_Vh : uIdx < 2 ^ (L_sim * h) := lt_trans huIdx_lt hV_lt
      have hvIdx_Vh : vIdx < 2 ^ (L_sim * h) := lt_trans hvIdx_lt hV_lt
      have huIdx_w : uIdx < 2 ^ w := lt_trans huIdx_lt hV_w
      have hvIdx_w : vIdx < 2 ^ w := lt_trans hvIdx_lt hV_w
      have hj_w : j < 2 ^ w := lt_trans hj hnl_len_w
      have hcnt_w : cnt < 2 ^ w := lt_of_le_of_lt (le_trans (by omega) hm1_j1) hm₁_w
      have horig_j1_w : origPtr + origIdx + cnt < 2 ^ w := by linarith only [horig_w, hm1_j1']
      have horigIdx_w : origIdx < 2 ^ w := lt_of_le_of_lt (by omega) horig_j1_w
      have hwSrc_end : wArr + j * K + K ≤ wArr + nl.length * K := by
        have hjk : (j + 1) * K ≤ nl.length * K := Nat.mul_le_mul_right K hj
        rw [Nat.add_mul, Nat.one_mul] at hjk; omega
      have hwSrc_w : wArr + j * K + K < 2 ^ w := lt_of_le_of_lt hwSrc_end hwArr_w
      have hjK_w : j * K < 2 ^ w := lt_of_le_of_lt (by omega) hwSrc_w
      have hwSrc_addr_w : wArr + j * K < 2 ^ w := lt_of_le_of_lt (by omega) hwSrc_w
      have hk_range : ∀ {a len}, DisjointRanges outArr (encLen * L_sim) a len →
          DisjointRanges origPtr m₁ a len → ∀ d < len,
          st.mem (a + d) = mem (a + d) := by
        intro a len hdo hdo2 d hd
        have h1 : a + d < outArr + 2 * L_sim ∨ outArr + (2 + 3 * origIdx) * L_sim ≤ a + d := by
          rcases hdo with hlo | hhi
          · right; linarith only [hlo, henc_j_le, Nat.zero_le d]
          · left; linarith only [hhi, hd, Nat.zero_le (2 * L_sim)]
        have h2 : a + d < origPtr ∨ origPtr + origIdx ≤ a + d := by
          rcases hdo2 with hlo | hhi
          · right; linarith only [hlo, hm1_j1, Nat.zero_le cnt, Nat.zero_le d]
          · left; linarith only [hhi, hd]
        have h3 : a + d < outArr ∨ outArr + 2 * L_sim ≤ a + d := by
          rcases hdo with hlo | hhi
          · right; linarith only [hlo, h2_le_enc, Nat.zero_le d]
          · left; linarith only [hhi, hd]
        rw [hfr_st _ h1 h2, hfr6 _ h3]
      have he_mem : st.mem (nlArr + j) = e := by
        rw [hk_range hd_out_nl hd_orig_nl j hj, hnl_list j hj]
      have htl_mem : st.mem (tailArr + e) = G.tail e := by
        rw [hk_range hd_out_tl hd_orig_tl e he_m]
        have h := htl_list e (by simpa using he_m); simpa using h
      have hhd_mem : st.mem (headArr + e) = G.head e := by
        rw [hk_range hd_out_hd hd_orig_hd e he_m]
        have h := hhd_list e (by simpa using he_m); simpa using h
      have hv_tl_mem : st.mem (vIdxPtr + G.tail e) = uIdx := by
        rw [hk_range hd_out_vIdx hd_orig_vIdx (G.tail e) htail_lt, hvIdx_spec _ hu_lt_V]
      have hv_hd_mem : st.mem (vIdxPtr + G.head e) = vIdx := by
        rw [hk_range hd_out_vIdx hd_orig_vIdx (G.head e) hhead_lt, hvIdx_spec _ hv_lt_V]
      have hcnt_mem : st.mem (multArr + j) = cnt := by
        rw [hk_range hd_out_mult hd_orig_mult j hj, hmult_spec j hj]
      have hw_limbs : LimbsAt st.mem (wArr + j * K) K h (w_orig e) :=
        (hw_spec j hj).congr fun a ha1 ha2 => by
          have ha_eq : a = wArr + (j * K + (a - (wArr + j * K))) := by omega
          rw [ha_eq]
          dsimp only [nl] at hwSrc_end
          exact hk_range hd_out_w hd_orig_w (j * K + (a - (wArr + j * K))) (by omega)
      have htail_addr : vIdxPtr + G.tail e < 2 ^ w := lt_trans (Nat.add_lt_add_left htail_lt vIdxPtr) hvIdxPtr_w
      have hhead_addr : vIdxPtr + G.head e < 2 ^ w := lt_trans (Nat.add_lt_add_left hhead_lt vIdxPtr) hvIdxPtr_w
      refine runs_start_le ?_
      refine runs_seq_assign_step (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hregs.r1) (Expr.eval_reg_of_eq hr19) (by linarith only [hj, hnl_w])) he_mem) rfl fun s1 hm1 _ hr1 => ?_
      have hs1_mem : s1.mem = st.mem := hm1
      have hregs1 := egAugRegs_upd hregs hr1 (by decide)
      have hs1_17 : s1.regs 17 = posJ := by rw [hr1, Function.update_of_ne (by decide)]; exact hr17
      have hs1_18 : s1.regs 18 = origIdx := by rw [hr1, Function.update_of_ne (by decide)]; exact hr18
      have hs1_19 : s1.regs 19 = j := by rw [hr1, Function.update_of_ne (by decide)]; exact hr19
      have hs1_20 : s1.regs 20 = e := by rw [hr1, Function.update_self]
      refine runs_seq_assign_step (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hregs1.r2) (Expr.eval_reg_of_eq hs1_20) (by linarith only [he_m, htl_w])) (hs1_mem ▸ htl_mem)) rfl fun s2 hm2 _ hr2 => ?_
      have hregs2 := egAugRegs_upd hregs1 hr2 (by decide)
      have hs2_21 : s2.regs 21 = G.tail e := by rw [hr2, Function.update_self]
      have hs2_20 : s2.regs 20 = e := by rw [hr2, Function.update_of_ne (by decide)]; exact hs1_20
      have hs2_19 : s2.regs 19 = j := by rw [hr2, Function.update_of_ne (by decide)]; exact hs1_19
      have hs2_18 : s2.regs 18 = origIdx := by rw [hr2, Function.update_of_ne (by decide)]; exact hs1_18
      have hs2_17 : s2.regs 17 = posJ := by rw [hr2, Function.update_of_ne (by decide)]; exact hs1_17
      refine runs_seq_assign_step (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hregs2.r4) (Expr.eval_reg_of_eq hs2_21) htail_addr) (hm2.trans hs1_mem ▸ hv_tl_mem)) rfl fun s3 hm3 _ hr3 => ?_
      have hregs3 := egAugRegs_upd hregs2 hr3 (by decide)
      have hs3_21 : s3.regs 21 = uIdx := by rw [hr3, Function.update_self]
      have hs3_20 : s3.regs 20 = e := by rw [hr3, Function.update_of_ne (by decide)]; exact hs2_20
      have hs3_19 : s3.regs 19 = j := by rw [hr3, Function.update_of_ne (by decide)]; exact hs2_19
      have hs3_18 : s3.regs 18 = origIdx := by rw [hr3, Function.update_of_ne (by decide)]; exact hs2_18
      have hs3_17 : s3.regs 17 = posJ := by rw [hr3, Function.update_of_ne (by decide)]; exact hs2_17
      refine runs_seq_assign_step (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hregs3.r3) (Expr.eval_reg_of_eq hs3_20) (by linarith only [he_m, hhd_w])) (hm3.trans (hm2.trans hs1_mem) ▸ hhd_mem)) rfl fun s4 hm4 _ hr4 => ?_
      have hregs4 := egAugRegs_upd hregs3 hr4 (by decide)
      have hs4_22 : s4.regs 22 = G.head e := by rw [hr4, Function.update_self]
      have hs4_21 : s4.regs 21 = uIdx := by rw [hr4, Function.update_of_ne (by decide)]; exact hs3_21
      have hs4_20 : s4.regs 20 = e := by rw [hr4, Function.update_of_ne (by decide)]; exact hs3_20
      have hs4_19 : s4.regs 19 = j := by rw [hr4, Function.update_of_ne (by decide)]; exact hs3_19
      have hs4_18 : s4.regs 18 = origIdx := by rw [hr4, Function.update_of_ne (by decide)]; exact hs3_18
      have hs4_17 : s4.regs 17 = posJ := by rw [hr4, Function.update_of_ne (by decide)]; exact hs3_17
      refine runs_seq_assign_step (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hregs4.r4) (Expr.eval_reg_of_eq hs4_22) hhead_addr) (hm4.trans (hm3.trans (hm2.trans hs1_mem)) ▸ hv_hd_mem)) rfl fun s5 hm5 _ hr5 => ?_
      have hregs5 := egAugRegs_upd hregs4 hr5 (by decide)
      have hs5_22 : s5.regs 22 = vIdx := by rw [hr5, Function.update_self]
      have hs5_21 : s5.regs 21 = uIdx := by rw [hr5, Function.update_of_ne (by decide)]; exact hs4_21
      have hs5_20 : s5.regs 20 = e := by rw [hr5, Function.update_of_ne (by decide)]; exact hs4_20
      have hs5_19 : s5.regs 19 = j := by rw [hr5, Function.update_of_ne (by decide)]; exact hs4_19
      have hs5_18 : s5.regs 18 = origIdx := by rw [hr5, Function.update_of_ne (by decide)]; exact hs4_18
      have hs5_17 : s5.regs 17 = posJ := by rw [hr5, Function.update_of_ne (by decide)]; exact hs4_17
      refine runs_seq_assign_step (Expr.eval_add (Expr.eval_reg_of_eq hregs5.r6) (Expr.eval_mul (Expr.eval_reg_of_eq hs5_19) (Expr.eval_reg_of_eq hregs5.r7) hjK_w) hwSrc_addr_w) rfl fun s6 hm6 _ hr6 => ?_
      have hregs6 := egAugRegs_upd hregs5 hr6 (by decide)
      have hs6_23 : s6.regs 23 = wArr + j * K := by rw [hr6, Function.update_self]
      have hs6_22 : s6.regs 22 = vIdx := by rw [hr6, Function.update_of_ne (by decide)]; exact hs5_22
      have hs6_21 : s6.regs 21 = uIdx := by rw [hr6, Function.update_of_ne (by decide)]; exact hs5_21
      have hs6_20 : s6.regs 20 = e := by rw [hr6, Function.update_of_ne (by decide)]; exact hs5_20
      have hs6_19 : s6.regs 19 = j := by rw [hr6, Function.update_of_ne (by decide)]; exact hs5_19
      have hs6_18 : s6.regs 18 = origIdx := by rw [hr6, Function.update_of_ne (by decide)]; exact hs5_18
      have hs6_17 : s6.regs 17 = posJ := by rw [hr6, Function.update_of_ne (by decide)]; exact hs5_17
      have hs6_mem : s6.mem = st.mem := hm6.trans (hm5.trans (hm4.trans (hm3.trans (hm2.trans hm1))))
      refine runs_seq_assign_step (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hregs6.r5) (Expr.eval_reg_of_eq hs6_19) (by linarith only [hj, hmul_w])) (hs6_mem ▸ hcnt_mem)) rfl fun s7 hm7 _ hr7 => ?_
      have hregs7 := egAugRegs_upd hregs6 hr7 (by decide)
      have hs7_24 : s7.regs 24 = cnt := by rw [hr7, Function.update_self]
      have hs7_23 : s7.regs 23 = wArr + j * K := by rw [hr7, Function.update_of_ne (by decide)]; exact hs6_23
      have hs7_22 : s7.regs 22 = vIdx := by rw [hr7, Function.update_of_ne (by decide)]; exact hs6_22
      have hs7_21 : s7.regs 21 = uIdx := by rw [hr7, Function.update_of_ne (by decide)]; exact hs6_21
      have hs7_20 : s7.regs 20 = e := by rw [hr7, Function.update_of_ne (by decide)]; exact hs6_20
      have hs7_19 : s7.regs 19 = j := by rw [hr7, Function.update_of_ne (by decide)]; exact hs6_19
      have hs7_18 : s7.regs 18 = origIdx := by rw [hr7, Function.update_of_ne (by decide)]; exact hs6_18
      have hs7_17 : s7.regs 17 = posJ := by rw [hr7, Function.update_of_ne (by decide)]; exact hs6_17
      have hs7_mem : s7.mem = st.mem := hm7.trans hs6_mem
      have hdisj_wpos : wArr + j * K + K ≤ posJ ∨ posJ + cnt * (3 * L_sim) ≤ wArr + j * K := by
        rcases hd_out_w with h1 | h1
        · right; linarith only [h1, hposJ_end, henc_j1', Nat.zero_le (j * K)]
        · left; dsimp only [posJ]; linarith only [h1, hwSrc_end, Nat.zero_le ((2 + 3 * origIdx) * L_sim)]
      have hdisj_opos : origPtr + origIdx + cnt ≤ posJ ∨ posJ + cnt * (3 * L_sim) ≤ origPtr + origIdx := by
        rcases hd_orig_out with h1 | h1
        · left; dsimp only [posJ]; linarith only [h1, hm1_j1', Nat.zero_le ((2 + 3 * origIdx) * L_sim)]
        · right; linarith only [h1, hposJ_end, henc_j1', Nat.zero_le origIdx]
      have hdisj_ow : origPtr + origIdx + cnt ≤ wArr + j * K ∨ wArr + j * K + K ≤ origPtr + origIdx := by
        rcases hd_orig_w with h1 | h1
        · left; linarith only [h1, hm1_j1', Nat.zero_le (j * K)]
        · right; linarith only [h1, hwSrc_end, Nat.zero_le origIdx]
      have hpre_ec : (encodeEdgeCopiesContract w h).pre
          [uIdx, vIdx, wArr + j * K, K, cnt, L_sim, 2 ^ h, posJ, origPtr, origIdx, e] st.mem :=
        ⟨uIdx, vIdx, wArr + j * K, K, cnt, L_sim, posJ, origPtr, origIdx, e, w_orig e, rfl,
          hh, hw2, hKL, hcnt_w, hwSrc_w, hposJ_end_w, horig_j1_w, huIdx_Vh, hvIdx_Vh,
          hdisj_wpos, hdisj_opos, hdisj_ow, hw_limbs⟩
      refine runs_seq_call_step hec_mc
        (vs := [uIdx, vIdx, wArr + j * K, K, cnt, L_sim, 2 ^ h, posJ, origPtr, origIdx, e])
        (evalArgs_cons (Expr.eval_reg_of_eq hs7_21)
          (evalArgs_cons (Expr.eval_reg_of_eq hs7_22)
            (evalArgs_cons (Expr.eval_reg_of_eq hs7_23)
              (evalArgs_cons (Expr.eval_reg_of_eq hregs7.r7)
                (evalArgs_cons (Expr.eval_reg_of_eq hs7_24)
                  (evalArgs_cons (Expr.eval_reg_of_eq hregs7.r11)
                    (evalArgs_cons (Expr.eval_reg_of_eq hregs7.r12)
                      (evalArgs_cons (Expr.eval_reg_of_eq hs7_17)
                        (evalArgs_cons (Expr.eval_reg_of_eq hregs7.r13)
                          (evalArgs_cons (Expr.eval_reg_of_eq hs7_18)
                            (evalArgs_cons (Expr.eval_reg_of_eq hs7_20) (evalArgs_nil _ _))))))))))))
        (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with hx|hx|hx|hx|hx|hx|hx|hx|hx|hx|hx <;> rw [hx]
          · exact huIdx_w
          · exact hvIdx_w
          · exact hwSrc_addr_w
          · exact hK_w
          · exact hcnt_w
          · exact hL_w
          · exact hB2h_w
          · exact hposJ_w
          · exact lt_of_le_of_lt (Nat.le_add_right _ _) (lt_of_le_of_lt (Nat.le_add_right _ _) horig_j1_w)
          · exact horigIdx_w
          · exact he_w)
        (hs7_mem ▸ hpre_ec) rfl
        (rfl : _ = encodeEdgeCopiesCost cnt L_sim) fun pos_next mem' s8 hp8 hm8 hr8 => ?_
      rw [hs7_mem] at hp8
      obtain ⟨u', v', wSrc', K', cnt', L', pos', origPtr', origIdx', origVal', wVal',
        heq8, hret8, hlw8, ho8, hl8, hfr8⟩ := hp8
      simp only [List.cons.injEq, and_true] at heq8
      rcases heq8 with ⟨h_u, h_v, h_ws, h_K, h_cnt, h_L, _, h_pos, h_op, h_oi, h_ov⟩
      rw [← h_cnt] at ho8 hl8
      rw [← h_pos, ← h_L] at hret8 hl8 hfr8
      rw [← h_cnt] at hret8 hfr8
      rw [← h_op, ← h_oi] at hfr8
      rw [← h_op, ← h_oi, ← h_ov] at ho8
      rw [← h_u, ← h_v] at hl8
      rw [← h_ws, ← h_K] at hlw8
      have h_wval : wVal' = w_orig e := LimbsAt.ext hlw8 (hs7_mem ▸ hw_limbs)
      rw [h_wval] at hl8
      have hregs8 := egAugRegs_upd hregs7 hr8 (by decide)
      have hs8_15 : s8.regs 15 = m₁ := by
        rw [hr8, Function.update_of_ne (by decide), hr7, Function.update_of_ne (by decide),
          hr6, Function.update_of_ne (by decide), hr5, Function.update_of_ne (by decide),
          hr4, Function.update_of_ne (by decide), hr3, Function.update_of_ne (by decide),
          hr2, Function.update_of_ne (by decide), hr1, Function.update_of_ne (by decide)]; exact hr15
      have hs8_17 : s8.regs 17 = outArr + (2 + 3 * (origIdx + cnt)) * L_sim := by
        rw [hr8, Function.update_self, hret8, ← hposJ_end]
      have hs8_18 : s8.regs 18 = origIdx := by
        rw [hr8, Function.update_of_ne (by decide)]; exact hs7_18
      have hs8_19 : s8.regs 19 = j := by
        rw [hr8, Function.update_of_ne (by decide)]; exact hs7_19
      have hs8_24 : s8.regs 24 = cnt := by
        rw [hr8, Function.update_of_ne (by decide)]; exact hs7_24
      refine runs_assign_le (Expr.eval_add (Expr.eval_reg_of_eq hs8_18) (Expr.eval_reg_of_eq hs8_24) (lt_of_le_of_lt hm1_j1 hm₁_w)) ?_ ?_
      · refine ⟨⟨egAugRegs_upd (egAugRegs_upd hregs8 rfl (by decide)) rfl (by decide),
            by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hs8_15,
            by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hs8_17, hcnt_step.1],
            by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self, hcnt_step.1],
            by dsimp only; rw [Function.update_self], ?_, ?_, ?_⟩, ?_⟩
        · intro t ht htj1 c hc
          dsimp only; rw [hm8]
          by_cases htj : t = j
          · rcases htj.symm with rfl; exact ho8 c hc
          · have hlt : t < j := lt_of_le_of_ne (Nat.lt_succ_iff.mp htj1) htj
            have htm := take_map_sum_succ_le nl mult ht
            have hsub : ((nl.take (t + 1)).map mult).sum ≤ origIdx := take_map_sum_mono nl mult hlt
            have ha_lt_orig : origPtr + ((nl.take t).map mult).sum + c < origPtr + origIdx := by
              linarith only [htm.1, hsub, hc]
            have hle_sum : origIdx ≤ ((nonloopEdges G).map mult).sum :=
              le_trans (Nat.le_add_right _ _) hm1_j1'
            have ha_disj_pos : origPtr + ((nl.take t).map mult).sum + c < posJ ∨
                posJ + cnt * (3 * L_sim) ≤ origPtr + ((nl.take t).map mult).sum + c := by
              rcases hd_orig_out with hdo1 | hdo1
              · left; dsimp only [posJ]
                linarith only [hdo1, ha_lt_orig, hle_sum, Nat.zero_le ((2 + 3 * origIdx) * L_sim)]
              · right; rw [hposJ_end]
                linarith only [hdo1, henc_j1', Nat.zero_le (((nl.take t).map mult).sum), Nat.zero_le c]
            rw [hfr8 _ ha_disj_pos (Or.inl ha_lt_orig)]
            exact hm_orig t ht hlt c hc
        · intro t ht htj1 c hc
          dsimp only; rw [hm8]
          by_cases htj : t = j
          · rcases htj.symm with rfl
            have hm0 : (2 + 3 * (origIdx + c)) * L_sim = (2 + 3 * origIdx) * L_sim + c * (3 * L_sim) := by ring
            have hm1 : (2 + 3 * (origIdx + c) + 1) * L_sim = (2 + 3 * origIdx) * L_sim + c * (3 * L_sim) + L_sim := by ring
            have hm2 : (2 + 3 * (origIdx + c) + 2) * L_sim = (2 + 3 * origIdx) * L_sim + c * (3 * L_sim) + 2 * L_sim := by ring
            have hp0 : outArr + (2 + 3 * (((nl.take j).map mult).sum + c)) * L_sim = posJ + c * (3 * L_sim) := by
              dsimp only [posJ, origIdx]; linarith only [hm0]
            have hp1 : outArr + (2 + 3 * (((nl.take j).map mult).sum + c) + 1) * L_sim = posJ + c * (3 * L_sim) + L_sim := by
              dsimp only [posJ, origIdx]; linarith only [hm1]
            have hp2 : outArr + (2 + 3 * (((nl.take j).map mult).sum + c) + 2) * L_sim = posJ + c * (3 * L_sim) + 2 * L_sim := by
              dsimp only [posJ, origIdx]; linarith only [hm2]
            rw [hp0, hp1, hp2]
            exact hl8 c hc
          · have hlt : t < j := lt_of_le_of_ne (Nat.lt_succ_iff.mp htj1) htj
            have htm := take_map_sum_succ_le nl mult ht
            have hsub : ((nl.take (t + 1)).map mult).sum ≤ origIdx := take_map_sum_mono nl mult hlt
            have hpv := hm_limbs t ht hlt c hc
            let idxT := ((nl.take t).map mult).sum + c
            have hidx_le : idxT + 1 ≤ origIdx := by dsimp only [idxT]; linarith only [htm.1, hsub, hc]
            have hmul_3 : (2 + 3 * idxT + 3) * L_sim ≤ (2 + 3 * origIdx) * L_sim :=
              Nat.mul_le_mul_right L_sim (by linarith only [hidx_le])
            have heq_out : ∀ q, outArr ≤ q → q < posJ → mem' q = st.mem q := fun q hq1 hq2 => by
              have hdo_q : q < origPtr + origIdx ∨ origPtr + origIdx + cnt ≤ q := by
                rcases hd_orig_out with hdo1 | hdo1
                · right; linarith only [hdo1, hm1_j1', hq1]
                · left
                  have hposJ_le_enc : posJ ≤ outArr + (2 + 3 * (((nonloopEdges G).map mult).sum + B.length)) * L_sim := by
                    have henc_j_le' : (2 + 3 * origIdx) * L_sim ≤
                        (2 + 3 * (((nonloopEdges G).map mult).sum + B.length)) * L_sim := henc_j_le
                    dsimp only [posJ]; linarith only [henc_j_le']
                  linarith only [hdo1, hposJ_le_enc, hq2, Nat.zero_le origIdx]
              rw [hfr8 q (Or.inl hq2) hdo_q]
            have h30 : (2 + 3 * idxT) * L_sim + L_sim ≤ (2 + 3 * idxT + 3) * L_sim := by
              have : (2 + 3 * idxT) * L_sim + L_sim = (2 + 3 * idxT + 1) * L_sim := by ring
              have hm := Nat.mul_le_mul_right L_sim (by linarith only : 2 + 3 * idxT + 1 ≤ 2 + 3 * idxT + 3)
              linarith only [this, hm]
            have h31 : (2 + 3 * idxT + 1) * L_sim + L_sim ≤ (2 + 3 * idxT + 3) * L_sim := by
              have : (2 + 3 * idxT + 1) * L_sim + L_sim = (2 + 3 * idxT + 2) * L_sim := by ring
              have hm := Nat.mul_le_mul_right L_sim (by linarith only : 2 + 3 * idxT + 2 ≤ 2 + 3 * idxT + 3)
              linarith only [this, hm]
            have h32 : (2 + 3 * idxT + 2) * L_sim + L_sim = (2 + 3 * idxT + 3) * L_sim := by ring
            dsimp only [idxT] at h30 h31 h32 hmul_3
            refine ⟨hpv.1.congr fun q hq1 hq2 => heq_out q (by linarith only [hq1, Nat.zero_le ((2 + 3 * (((nl.take t).map mult).sum + c)) * L_sim)])
                (by dsimp only [posJ]; linarith only [hq2, h30, hmul_3]),
              hpv.2.1.congr fun q hq1 hq2 => heq_out q (by linarith only [hq1, Nat.zero_le ((2 + 3 * (((nl.take t).map mult).sum + c) + 1) * L_sim)])
                (by dsimp only [posJ]; linarith only [hq2, h31, hmul_3]),
              hpv.2.2.congr fun q hq1 hq2 => heq_out q (by linarith only [hq1, Nat.zero_le ((2 + 3 * (((nl.take t).map mult).sum + c) + 2) * L_sim)])
                (by dsimp only [posJ]; linarith only [hq2, h32, hmul_3])⟩
        · intro a ha hao
          dsimp only at ha hao ⊢
          have htake_j1 : ((nl.take (j + 1)).map mult).sum = origIdx + cnt := hcnt_step.1.symm
          rw [htake_j1] at ha hao
          have ha_pos : a < posJ ∨ posJ + cnt * (3 * L_sim) ≤ a := by
            rcases ha with h1 | h1
            · left; dsimp only [posJ]
              have hm := Nat.mul_le_mul_right L_sim (by linarith only [Nat.zero_le origIdx] : 2 ≤ 2 + 3 * origIdx)
              linarith only [h1, hm]
            · right; rw [hposJ_end]; exact h1
          have ha_orig : a < origPtr + origIdx ∨ origPtr + origIdx + cnt ≤ a := by
            rcases hao with h1 | h1
            · left; linarith only [h1, Nat.zero_le origIdx]
            · right; linarith only [h1]
          have ha_st : a < outArr + 2 * L_sim ∨ outArr + (2 + 3 * origIdx) * L_sim ≤ a := by
            rcases ha with h1 | h1
            · left; exact h1
            · right
              have hm := Nat.mul_le_mul_right L_sim (by linarith only [Nat.zero_le cnt] : 2 + 3 * origIdx ≤ 2 + 3 * (origIdx + cnt))
              linarith only [h1, hm]
          have hao_st : a < origPtr ∨ origPtr + origIdx ≤ a := by
            rcases hao with h1 | h1
            · left; exact h1
            · right; linarith only [h1, Nat.zero_le cnt]
          rw [hm8, hfr8 a ha_pos ha_orig]
          try rw [hs7_mem]
          exact hfr_st a ha_st hao_st
        · dsimp only; rw [Function.update_of_ne (by decide)]; exact hs8_19
      · dsimp only [stepCost, encodeEdgeCopiesCost, argsSize, Expr.size]
        rw [dite_eq_left hj]
        have he_def : e = nl[j]'hj := rfl
        have hcnt_def : cnt = mult (nl[j]'hj) := rfl
        rw [← hcnt_def]
        linarith only)
  refine runs_seq_triple_le (hloop.conseq (fun _ h => h) (fun o st hq => by
    cases o with | returned _ => exact False.elim hq | normal => exact hq) (fun _ _ => le_rfl)) rfl ?_
  intro st7 hInv7
  have hregs7 := hInv7.1
  have hr15_7 := hInv7.2.1
  have hr17_7 := hInv7.2.2.1
  have hr18_7 := hInv7.2.2.2.1
  have hm_orig7 := hInv7.2.2.2.2.2.1
  have hm_limbs7 := hInv7.2.2.2.2.2.2.1
  have hfr7 := hInv7.2.2.2.2.2.2.2
  have htake_all : nl.take nl.length = nl := List.take_length
  rw [htake_all] at hr17_7 hr18_7 hfr7
  have horig_list : ListAt st7.mem origPtr (origOfCopy G mult) := by
    rw [origOfCopy]
    simpa [htake_all] using listAt_orig_prefix nl.length (le_refl _) st7.mem fun t ht _ c hc => hm_orig7 t ht ht c hc
  obtain ⟨o, st', c, hrun, hq, hc⟩ := hrest st7 hregs7 hr15_7 hr17_7 horig_list
    (fun j hj c hc => hm_limbs7 j hj hj c hc) hfr7
  refine ⟨o, st', c, hrun, hq, ?_⟩
  dsimp only [Expr.size]
  have hrc1 := rangeCost_add_const
    (fun j => (if hj : j < nl.length then mult (nl[j]'hj) else 0) * (70 * L_sim + 110)) 81 nl.length
  have hrc2 := rangeCost_scale
    (fun j => if hj : j < nl.length then mult (nl[j]'hj) else 0) (70 * L_sim + 110) nl.length
  have hrc3 := rangeCost_map_take_sum nl mult nl.length (le_refl _)
  rw [htake_all] at hrc3
  simp only [Nat.sub_zero]
  dsimp only [stepCost]
  rw [hrc1, hrc2, hrc3]
  have hc' : k_cost + (((nonloopEdges G).map mult).sum * (70 * L_sim + 110) + 90 * (nonloopEdges G).length + 10) + c ≤ T := hc
  dsimp only [nl]
  linarith only [hc']

theorem encodeGAug_runs {w h a p w' s e : ℕ} {P : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {pos₀ : ℕ}
    (hp : P.HasAt e (encodeDecodeModule a p w' s e))
    (ha : P.HasAt a (arithModule a))
    (G : IndexedGraph) (V_list B : List ℕ) (mult w_orig : ℕ → ℕ)
    (nlArr tailArr headArr vIdxPtr multArr wArr K bArr L_sim origPtr outArr : ℕ)
    (hwords : ∀ a ∈ [(nonloopEdges G).length, nlArr, tailArr, headArr, vIdxPtr, multArr, wArr, K,
      V_list.length, B.length, bArr, L_sim, 2 ^ h, origPtr, outArr], a < 2 ^ w)
    (hG : G.Valid) (_hV_nd : V_list.Nodup) (hV_sub : ∀ u ∈ V_list, u < G.n)
    (hV_mem : ∀ e ∈ nonloopEdges G, G.tail e ∈ V_list ∧ G.head e ∈ V_list)
    (hB_mem : ∀ b ∈ B, b ∈ V_list)
    (hh : 1 ≤ h) (hw2 : 2 * h + 2 ≤ w) (hK1 : 1 ≤ K) (hKL : K ≤ L_sim)
    (hV_lt : V_list.length < 2 ^ (L_sim * h))
    (hmB_lt : (nonloopEdges G |>.map mult).sum + B.length < 2 ^ (L_sim * h))
    (hmB_w : (nonloopEdges G |>.map mult).sum + B.length < 2 ^ w)
    (hnl_w : nlArr + (nonloopEdges G).length < 2 ^ w)
    (htl_w : tailArr + G.m < 2 ^ w) (hhd_w : headArr + G.m < 2 ^ w)
    (hvIdx_w : vIdxPtr + G.n < 2 ^ w) (hmul_w : multArr + (nonloopEdges G).length < 2 ^ w)
    (hwArr_w : wArr + (nonloopEdges G).length * K < 2 ^ w)
    (hbArr_w : bArr + B.length < 2 ^ w)
    (horig_w : origPtr + (nonloopEdges G |>.map mult).sum < 2 ^ w)
    (hout_w : outArr + (2 + 3 * ((nonloopEdges G |>.map mult).sum + B.length)) * L_sim < 2 ^ w)
    (hd_out_nl : DisjointRanges outArr ((2 + 3 * ((nonloopEdges G |>.map mult).sum + B.length)) * L_sim) nlArr (nonloopEdges G).length)
    (hd_out_tl : DisjointRanges outArr ((2 + 3 * ((nonloopEdges G |>.map mult).sum + B.length)) * L_sim) tailArr G.m)
    (hd_out_hd : DisjointRanges outArr ((2 + 3 * ((nonloopEdges G |>.map mult).sum + B.length)) * L_sim) headArr G.m)
    (hd_out_vIdx : DisjointRanges outArr ((2 + 3 * ((nonloopEdges G |>.map mult).sum + B.length)) * L_sim) vIdxPtr G.n)
    (hd_out_mult : DisjointRanges outArr ((2 + 3 * ((nonloopEdges G |>.map mult).sum + B.length)) * L_sim) multArr (nonloopEdges G).length)
    (hd_out_w : DisjointRanges outArr ((2 + 3 * ((nonloopEdges G |>.map mult).sum + B.length)) * L_sim) wArr ((nonloopEdges G).length * K))
    (hd_out_b : DisjointRanges outArr ((2 + 3 * ((nonloopEdges G |>.map mult).sum + B.length)) * L_sim) bArr B.length)
    (hd_orig_out : DisjointRanges origPtr (nonloopEdges G |>.map mult).sum outArr ((2 + 3 * ((nonloopEdges G |>.map mult).sum + B.length)) * L_sim))
    (hd_orig_nl : DisjointRanges origPtr (nonloopEdges G |>.map mult).sum nlArr (nonloopEdges G).length)
    (hd_orig_tl : DisjointRanges origPtr (nonloopEdges G |>.map mult).sum tailArr G.m)
    (hd_orig_hd : DisjointRanges origPtr (nonloopEdges G |>.map mult).sum headArr G.m)
    (hd_orig_vIdx : DisjointRanges origPtr (nonloopEdges G |>.map mult).sum vIdxPtr G.n)
    (hd_orig_mult : DisjointRanges origPtr (nonloopEdges G |>.map mult).sum multArr (nonloopEdges G).length)
    (hd_orig_w : DisjointRanges origPtr (nonloopEdges G |>.map mult).sum wArr ((nonloopEdges G).length * K))
    (hd_orig_b : DisjointRanges origPtr (nonloopEdges G |>.map mult).sum bArr B.length)
    (hnl_list : ListAt mem nlArr (nonloopEdges G))
    (htl_list : ListAt mem tailArr (List.ofFn fun i : Fin G.m => G.tail i))
    (hhd_list : ListAt mem headArr (List.ofFn fun i : Fin G.m => G.head i))
    (hvIdx_spec : ∀ u ∈ V_list, mem (vIdxPtr + u) = V_list.idxOf u)
    (hmult_spec : ∀ j (hj : j < (nonloopEdges G).length), mem (multArr + j) = mult ((nonloopEdges G)[j]'hj))
    (hw_spec : ∀ j (hj : j < (nonloopEdges G).length), LimbsAt mem (wArr + j * K) K h (w_orig ((nonloopEdges G)[j]'hj)))
    (hb_list : ListAt mem bArr B) :
    let nl := nonloopEdges G
    let m₁ := (nl.map mult).sum
    let encLen := 2 + 3 * (m₁ + B.length)
    ∃ st' c,
      Runs w P ω (encodeGAugProc a e)
        (startState [nl.length, nlArr, tailArr, headArr, vIdxPtr, multArr, wArr, K,
          V_list.length, B.length, bArr, L_sim, 2 ^ h, origPtr, outArr] mem pos₀)
        (.returned m₁) st' c ∧
      ListAt st'.mem origPtr (origOfCopy G mult) ∧
      (∀ i (hi : i < (buildGAug G V_list B mult w_orig).encode.length),
        LimbsAt st'.mem (outArr + i * L_sim) L_sim h ((buildGAug G V_list B mult w_orig).encode[i]'hi)) ∧
      (∀ a, (a < outArr ∨ outArr + encLen * L_sim ≤ a) →
        (a < origPtr ∨ origPtr + m₁ ≤ a) → st'.mem a = mem a) ∧
      c ≤ encodeGAugCost [nl.length, nlArr, tailArr, headArr, vIdxPtr, multArr, wArr, K,
        V_list.length, B.length, bArr, L_sim, 2 ^ h, origPtr, outArr] mem := by
  have hfh_mc := mwFromHost_of_arithModule (w := w) ha
  have hec_mc := encodeEdgeCopies_meetsContract (w := w) (h := h) hp ha
  have heb_mc := encodeBridges_meetsContract (w := w) (h := h) hp ha
  have hwords' := hwords
  let nl := nonloopEdges G
  let m₁ := (nl.map mult).sum
  let encLen := 2 + 3 * (m₁ + B.length)
  have hout_w' : outArr + encLen * L_sim < 2 ^ w := hout_w
  have horig_w' : origPtr + m₁ < 2 ^ w := horig_w
  have hd_orig_out' : DisjointRanges origPtr m₁ outArr (encLen * L_sim) := hd_orig_out
  have hd_out_b' : DisjointRanges outArr (encLen * L_sim) bArr B.length := hd_out_b
  have hd_out_vIdx' : DisjointRanges outArr (encLen * L_sim) vIdxPtr G.n := hd_out_vIdx
  have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have h2_w : 2 < 2 ^ w := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ w))
  have hnl_len_w : nl.length < 2 ^ w := hwords' nl.length (by dsimp only [nl]; simp)
  have hm₁_w : m₁ < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right _ B.length) hmB_w
  have hV_w : V_list.length < 2 ^ w := hwords' V_list.length (by simp)
  have hB_w : B.length < 2 ^ w := hwords' B.length (by simp)
  have hbArr_w0 : bArr < 2 ^ w := hwords' bArr (by simp)
  have hvIdx_w0 : vIdxPtr < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right _ _) hvIdx_w
  have hK_w : K < 2 ^ w := hwords' K (by simp)
  have hL_w : L_sim < 2 ^ w := hwords' L_sim (by simp)
  have h2h_w : 2 ^ h < 2 ^ w := hwords' (2 ^ h) (by simp)
  have h2_le_enc : 2 * L_sim ≤ encLen * L_sim :=
    Nat.mul_le_mul_right L_sim (by dsimp only [encLen]; omega)
  have h2m1_le_enc : (2 + 3 * m₁) * L_sim ≤ encLen * L_sim :=
    Nat.mul_le_mul_right L_sim (by dsimp only [encLen]; omega)
  have hout_2L_w : outArr + 2 * L_sim < 2 ^ w := by linarith only [hout_w', h2_le_enc]
  have hout_m1_w : outArr + (2 + 3 * m₁) * L_sim < 2 ^ w := by linarith only [hout_w', h2m1_le_enc]
  have henc_split : (2 + 3 * m₁) * L_sim + B.length * (3 * L_sim) = encLen * L_sim := by
    dsimp only [encLen]; ring
  have hm₁_cost : ((List.range nl.length).map fun j => mem (multArr + j)).sum = m₁ := by
    have hcongr : (List.range nl.length).map (fun j => mem (multArr + j)) =
        (List.range nl.length).map (fun j => if hj : j < nl.length then mult (nl[j]'hj) else 0) := by
      apply List.map_congr_left
      intro j hj
      have hjlt : j < nl.length := List.mem_range.mp hj
      rw [dite_eq_left hjlt]
      exact hmult_spec j hjlt
    rw [hcongr]
    have hr := rangeCost_map_take_sum nl mult nl.length (le_refl _)
    rw [rangeCost_zero_eq_range, List.take_length] at hr
    exact hr
  have hregs0 : EGAugRegs
      (startState [nl.length, nlArr, tailArr, headArr, vIdxPtr, multArr, wArr, K,
        V_list.length, B.length, bArr, L_sim, 2 ^ h, origPtr, outArr] mem pos₀)
      nl.length nlArr tailArr headArr vIdxPtr multArr wArr K V_list.length B.length bArr L_sim (2 ^ h) origPtr outArr := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [startState]
  suffices hrun_o : ∃ o st' c,
      Runs w P ω (encodeGAugProc a e)
        (startState [nl.length, nlArr, tailArr, headArr, vIdxPtr, multArr, wArr, K,
          V_list.length, B.length, bArr, L_sim, 2 ^ h, origPtr, outArr] mem pos₀)
        o st' c ∧
      (o = .returned m₁ ∧
        ListAt st'.mem origPtr (origOfCopy G mult) ∧
        (∀ i (hi : i < (buildGAug G V_list B mult w_orig).encode.length),
          LimbsAt st'.mem (outArr + i * L_sim) L_sim h ((buildGAug G V_list B mult w_orig).encode[i]'hi)) ∧
        (∀ a, (a < outArr ∨ outArr + encLen * L_sim ≤ a) →
          (a < origPtr ∨ origPtr + m₁ ≤ a) → st'.mem a = mem a)) ∧
      0 + c ≤ encodeGAugCost [nl.length, nlArr, tailArr, headArr, vIdxPtr, multArr, wArr, K,
        V_list.length, B.length, bArr, L_sim, 2 ^ h, origPtr, outArr] mem by
    rcases hrun_o with ⟨o, st', c, hrun', ⟨rfl, h1, h2, h3⟩, hc⟩
    refine ⟨st', c, hrun', h1, h2, h3, ?_⟩
    simpa only [m₁, encLen, Nat.zero_add] using hc
  refine encodeGAug_sum_runs hw1 hnl_len_w hmul_w hmB_w hmult_spec hregs0 rfl ?_
  intro st3 hregs3 hr15_3 hr16_3 hm3
  refine encodeGAug_hdr_runs hfh_mc hh hw2 hw1 h2_w hV_lt hmB_lt hV_w hmB_w hL_w h2h_w hout_2L_w
    hregs3 hr15_3 hr16_3 hm3 ?_
  intro st6 hregs6 hr15_6 hr17_6 hr18_6 hl_V hl_m hfr6
  refine encodeGAug_copies_runs hec_mc hG hV_mem hh hw2 hw1 hK1 hKL hV_lt hmB_w hnl_w htl_w hhd_w
    hvIdx_w hmul_w hwArr_w horig_w hout_w hL_w hK_w h2h_w hV_w hd_out_nl hd_out_tl hd_out_hd
    hd_out_vIdx hd_out_mult hd_out_w hd_orig_out hd_orig_nl hd_orig_tl hd_orig_hd hd_orig_vIdx
    hd_orig_mult hd_orig_w hnl_list htl_list hhd_list hvIdx_spec hmult_spec hw_spec
    hregs6 hr15_6 hr17_6 hr18_6 hfr6 ?_
  intro st7 hregs7 hr15_7 hr17_7 horig_list hlimbs_7 hfr_7
  have hout_eq_6 : ∀ q, outArr ≤ q → q < outArr + 2 * L_sim → st7.mem q = st6.mem q := fun q hq1 hq2 => by
    refine hfr_7 q (Or.inl hq2) ?_
    rcases hd_orig_out' with hdo | hdo
    · right; dsimp only [m₁] at hdo; linarith only [hdo, hq1]
    · left; linarith only [hdo, h2_le_enc, hq2]
  have hl_V7 : LimbsAt st7.mem outArr L_sim h V_list.length :=
    hl_V.congr fun q h1 h2 => hout_eq_6 q h1 (by linarith only [h2, Nat.zero_le L_sim])
  have hl_m7 : LimbsAt st7.mem (outArr + L_sim) L_sim h (m₁ + B.length) :=
    hl_m.congr fun q h1 h2 => hout_eq_6 q (by linarith only [h1, Nat.zero_le L_sim]) (by linarith only [h2])
  have hfr_7m : ∀ a, (a < outArr ∨ outArr + encLen * L_sim ≤ a) →
      (a < origPtr ∨ origPtr + m₁ ≤ a) → st7.mem a = mem a := fun a ha hao => by
    have h1 : a < outArr + 2 * L_sim ∨ outArr + (2 + 3 * m₁) * L_sim ≤ a := by
      rcases ha with h1 | h1
      · left; linarith only [h1, Nat.zero_le L_sim]
      · right; linarith only [h1, h2m1_le_enc]
    have h2 : a < outArr ∨ outArr + 2 * L_sim ≤ a := by
      rcases ha with h1 | h1
      · left; exact h1
      · right; linarith only [h1, h2_le_enc]
    rw [hfr_7 a h1 hao, hfr6 a h2]
  let posB := outArr + (2 + 3 * m₁) * L_sim
  let bIdxs := B.map (fun b => V_list.idxOf b)
  have h1L : 1 ≤ L_sim := le_trans hK1 hKL
  have hposB_end_w : posB + B.length * (3 * L_sim) < 2 ^ w := by
    dsimp only [posB]; linarith only [hout_w', henc_split]
  have hb_spec_st7 : ∀ k (hk : k < B.length),
      st7.mem (bArr + k) < 2 ^ w ∧
      st7.mem (vIdxPtr + st7.mem (bArr + k)) = bIdxs.getD k 0 ∧
      vIdxPtr + st7.mem (bArr + k) < 2 ^ w ∧
      bIdxs.getD k 0 < 2 ^ (L_sim * h) ∧
      bIdxs.getD k 0 < 2 ^ w := by
    intro k hk
    have hb_disj_out : bArr + k < outArr ∨ outArr + encLen * L_sim ≤ bArr + k := by
      rcases hd_out_b with h1 | h1
      · right; exact le_trans h1 (Nat.le_add_right _ _)
      · left; linarith only [h1, hk]
    have hb_disj_orig : bArr + k < origPtr ∨ origPtr + m₁ ≤ bArr + k := by
      rcases hd_orig_b with h1 | h1
      · right; exact le_trans h1 (Nat.le_add_right _ _)
      · left; linarith only [h1, hk]
    have hbk_eq : st7.mem (bArr + k) = B[k]'hk := by
      rw [hfr_7m _ hb_disj_out hb_disj_orig, hb_list k hk]
    have hBk_mem : B[k]'hk ∈ V_list := hB_mem _ (List.getElem_mem hk)
    have hBk_n : B[k]'hk < G.n := hV_sub _ hBk_mem
    have hget_eq : bIdxs.getD k 0 = V_list.idxOf (B[k]'hk) := by
      rw [List.getD_eq_getElem?_getD]
      have hlen_b : k < bIdxs.length := by simpa [bIdxs] using hk
      simp [bIdxs, List.getElem?_eq_getElem hk]
    have hvk_eq : st7.mem (vIdxPtr + st7.mem (bArr + k)) = bIdxs.getD k 0 := by
      have hv_disj_out : vIdxPtr + B[k]'hk < outArr ∨ outArr + encLen * L_sim ≤ vIdxPtr + B[k]'hk := by
        rcases hd_out_vIdx with h1 | h1
        · right; exact le_trans h1 (Nat.le_add_right _ _)
        · left; linarith only [h1, hBk_n]
      have hv_disj_orig : vIdxPtr + B[k]'hk < origPtr ∨ origPtr + m₁ ≤ vIdxPtr + B[k]'hk := by
        rcases hd_orig_vIdx with h1 | h1
        · right; exact le_trans h1 (Nat.le_add_right _ _)
        · left; linarith only [h1, hBk_n]
      rw [hbk_eq, hfr_7m _ hv_disj_out hv_disj_orig, hvIdx_spec _ hBk_mem, hget_eq]
    have hidx_lt : bIdxs.getD k 0 < V_list.length := by
      rw [hget_eq]; exact List.idxOf_lt_length_of_mem hBk_mem
    refine ⟨?_, hvk_eq, ?_, lt_trans hidx_lt hV_lt, lt_trans hidx_lt hV_w⟩
    · rw [hbk_eq]; exact lt_of_lt_of_le (lt_of_lt_of_le hBk_n (Nat.le_add_left _ _)) (Nat.le_of_lt hvIdx_w)
    · rw [hbk_eq]; exact lt_of_lt_of_le (Nat.add_lt_add_left hBk_n vIdxPtr) (Nat.le_of_lt hvIdx_w)
  have hdb_posB : ∀ k < B.length, bArr + k < posB ∨ posB + B.length * (3 * L_sim) ≤ bArr + k := fun k hk => by
    rcases hd_out_b' with h1 | h1
    · right; dsimp only [posB]; linarith only [h1, henc_split, Nat.zero_le k]
    · left; dsimp only [posB]; linarith only [h1, hk, Nat.zero_le ((2 + 3 * m₁) * L_sim)]
  have hdv_posB : ∀ k < B.length, vIdxPtr + st7.mem (bArr + k) < posB ∨ posB + B.length * (3 * L_sim) ≤ vIdxPtr + st7.mem (bArr + k) := by
    intro k hk
    have hb_disj_out : bArr + k < outArr ∨ outArr + encLen * L_sim ≤ bArr + k := by
      rcases hd_out_b with h1 | h1
      · right; exact le_trans h1 (Nat.le_add_right _ _)
      · left; linarith only [h1, hk]
    have hb_disj_orig : bArr + k < origPtr ∨ origPtr + m₁ ≤ bArr + k := by
      rcases hd_orig_b with h1 | h1
      · right; exact le_trans h1 (Nat.le_add_right _ _)
      · left; linarith only [h1, hk]
    have hbk_eq : st7.mem (bArr + k) = B[k]'hk := by
      rw [hfr_7m _ hb_disj_out hb_disj_orig, hb_list k hk]
    have hBk_n : B[k]'hk < G.n := hV_sub _ (hB_mem _ (List.getElem_mem hk))
    rw [hbk_eq]
    rcases hd_out_vIdx' with h1 | h1
    · right; dsimp only [posB]; linarith only [h1, henc_split, Nat.zero_le (B[k]'hk)]
    · left; dsimp only [posB]; linarith only [h1, hBk_n, Nat.zero_le ((2 + 3 * m₁) * L_sim)]
  have hpre_b : (encodeBridgesContract w h).pre [B.length, bArr, vIdxPtr, L_sim, 2 ^ h, posB] st7.mem :=
    ⟨B.length, bArr, vIdxPtr, L_sim, posB, bIdxs, rfl, hh, hw2, h1L, hbArr_w, hposB_end_w,
      by simp [bIdxs], hb_spec_st7, hdb_posB, hdv_posB⟩
  refine runs_seq_call_step heb_mc
    (vs := [B.length, bArr, vIdxPtr, L_sim, 2 ^ h, posB])
    (evalArgs_cons (Expr.eval_reg_of_eq hregs7.r9)
      (evalArgs_cons (Expr.eval_reg_of_eq hregs7.r10)
        (evalArgs_cons (Expr.eval_reg_of_eq hregs7.r4)
          (evalArgs_cons (Expr.eval_reg_of_eq hregs7.r11)
            (evalArgs_cons (Expr.eval_reg_of_eq hregs7.r12)
              (evalArgs_cons (Expr.eval_reg_of_eq hr17_7) (evalArgs_nil _ _)))))))
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx | hx | hx | hx | hx <;> rw [hx] <;> assumption)
    hpre_b rfl (rfl : _ = encodeBridgesCost B.length L_sim) fun _ mem_end st_end hp_b hm_end hr_end => ?_
  rcases hp_b with ⟨B', bArr', vIdx', L', pos', bIdxs', heq_b, hret_b, hblen_b, hidx_b, hl_b, hfr_b⟩
  simp only [List.cons.injEq, and_true] at heq_b
  rcases heq_b with ⟨h_B, h_ba, h_vi, h_L, _, h_pos⟩
  rw [← h_B] at hidx_b hl_b hfr_b
  rw [← h_ba, ← h_vi] at hidx_b
  rw [← h_pos, ← h_L] at hl_b hfr_b
  have hr15_end : st_end.regs 15 = m₁ := by
    rw [hr_end, Function.update_of_ne (by decide), hr15_7]
  have horig_end : ListAt st_end.mem origPtr (origOfCopy G mult) := by
    rw [hm_end]
    refine horig_list.congr fun a ha1 ha2 => hfr_b a ?_
    rw [origOfCopy_length, copyEdgeList_length] at ha2
    have hm₁_def : m₁ = ((nonloopEdges G).map mult).sum := rfl
    rcases hd_orig_out' with hdo | hdo
    · left; dsimp only [posB]; linarith only [hdo, ha2, hm₁_def, Nat.zero_le ((2 + 3 * m₁) * L_sim)]
    · right; dsimp only [posB]; linarith only [hdo, ha1, henc_split]
  have hl_V_end : LimbsAt st_end.mem outArr L_sim h V_list.length := by
    rw [hm_end]
    refine hl_V7.congr fun a ha1 ha2 => hfr_b a (Or.inl ?_)
    dsimp only [posB]
    have hm := Nat.mul_le_mul_right L_sim (by omega : 1 ≤ 2 + 3 * m₁)
    linarith only [ha2, hm]
  have hl_m_end : LimbsAt st_end.mem (outArr + L_sim) L_sim h (m₁ + B.length) := by
    rw [hm_end]
    refine hl_m7.congr fun a ha1 ha2 => hfr_b a (Or.inl ?_)
    dsimp only [posB]
    have hm := Nat.mul_le_mul_right L_sim (by omega : 2 ≤ 2 + 3 * m₁)
    linarith only [ha2, hm]
  have hl_copies_end : ∀ (j : ℕ) (hj : j < nl.length) (c : ℕ), c < mult (nl[j]'hj) →
      let idx := ((nl.take j).map mult).sum + c
      LimbsAt st_end.mem (outArr + (2 + 3 * idx) * L_sim) L_sim h (V_list.idxOf (G.tail (nl[j]'hj))) ∧
      LimbsAt st_end.mem (outArr + (2 + 3 * idx + 1) * L_sim) L_sim h (V_list.idxOf (G.head (nl[j]'hj))) ∧
      LimbsAt st_end.mem (outArr + (2 + 3 * idx + 2) * L_sim) L_sim h (w_orig (nl[j]'hj)) := by
    intro j hj c hc
    have hpre_c := hlimbs_7 j hj c hc
    have htm := take_map_sum_succ_le nl mult hj
    have hidx_lt : ((nl.take j).map mult).sum + c + 1 ≤ m₁ := by
      have hsub : ((nl.take (j + 1)).map mult).sum ≤ m₁ := htm.2
      linarith only [htm.1, hsub, hc]
    have hmul_c : (2 + 3 * (((nl.take j).map mult).sum + c) + 3) * L_sim ≤ (2 + 3 * m₁) * L_sim :=
      Nat.mul_le_mul_right L_sim (by linarith only [hidx_lt])
    have heq_posB : ∀ q, q < posB → mem_end q = st7.mem q := fun q hq => hfr_b q (Or.inl hq)
    have h30 : (2 + 3 * (((nl.take j).map mult).sum + c)) * L_sim + L_sim ≤ (2 + 3 * (((nl.take j).map mult).sum + c) + 3) * L_sim := by
      have hm := Nat.mul_le_mul_right L_sim (by omega : 2 + 3 * (((nl.take j).map mult).sum + c) + 1 ≤ 2 + 3 * (((nl.take j).map mult).sum + c) + 3)
      have hr : (2 + 3 * (((nl.take j).map mult).sum + c)) * L_sim + L_sim = (2 + 3 * (((nl.take j).map mult).sum + c) + 1) * L_sim := by ring
      linarith only [hm, hr]
    have h31 : (2 + 3 * (((nl.take j).map mult).sum + c) + 1) * L_sim + L_sim ≤ (2 + 3 * (((nl.take j).map mult).sum + c) + 3) * L_sim := by
      have hm := Nat.mul_le_mul_right L_sim (by omega : 2 + 3 * (((nl.take j).map mult).sum + c) + 2 ≤ 2 + 3 * (((nl.take j).map mult).sum + c) + 3)
      have hr : (2 + 3 * (((nl.take j).map mult).sum + c) + 1) * L_sim + L_sim = (2 + 3 * (((nl.take j).map mult).sum + c) + 2) * L_sim := by ring
      linarith only [hm, hr]
    have h32 : (2 + 3 * (((nl.take j).map mult).sum + c) + 2) * L_sim + L_sim = (2 + 3 * (((nl.take j).map mult).sum + c) + 3) * L_sim := by ring
    rw [hm_end]
    exact ⟨hpre_c.1.congr fun q _ hq2 => heq_posB q (by dsimp only [posB]; linarith only [hq2, h30, hmul_c]),
      hpre_c.2.1.congr fun q _ hq2 => heq_posB q (by dsimp only [posB]; linarith only [hq2, h31, hmul_c]),
      hpre_c.2.2.congr fun q _ hq2 => heq_posB q (by dsimp only [posB]; linarith only [hq2, h32, hmul_c])⟩
  have hl_bridges_end : ∀ (k : ℕ) (hk : k < B.length),
      let idx := m₁ + k
      LimbsAt st_end.mem (outArr + (2 + 3 * idx) * L_sim) L_sim h 0 ∧
      LimbsAt st_end.mem (outArr + (2 + 3 * idx + 1) * L_sim) L_sim h (V_list.idxOf (B[k]'hk)) ∧
      LimbsAt st_end.mem (outArr + (2 + 3 * idx + 2) * L_sim) L_sim h 1 := by
    intro k hk
    have hlb := hl_b k hk
    have hidx_eq : bIdxs'.getD k 0 = V_list.idxOf (B[k]'hk) := by
      have h1 := (hidx_b k hk).symm
      rw [(hb_spec_st7 k hk).2.1] at h1
      rw [h1]
      rw [List.getD_eq_getElem?_getD]
      simp [bIdxs, List.getElem?_eq_getElem hk]
    rw [hidx_eq] at hlb
    have ha0 : outArr + (2 + 3 * (m₁ + k)) * L_sim = posB + k * (3 * L_sim) := by dsimp only [posB]; ring
    have ha1 : outArr + (2 + 3 * (m₁ + k) + 1) * L_sim = posB + k * (3 * L_sim) + L_sim := by dsimp only [posB]; ring
    have ha2 : outArr + (2 + 3 * (m₁ + k) + 2) * L_sim = posB + k * (3 * L_sim) + 2 * L_sim := by dsimp only [posB]; ring
    dsimp only
    rw [hm_end, ha0, ha1, ha2]
    exact hlb
  have hlimbs_enc := limbsAt_gAug_encode_of_pieces hl_V_end hl_m_end hl_copies_end hl_bridges_end
  have hfr_end : ∀ a, (a < outArr ∨ outArr + encLen * L_sim ≤ a) →
      (a < origPtr ∨ origPtr + m₁ ≤ a) → st_end.mem a = mem a := fun a ha hao => by
    rw [hm_end, hfr_b a ?_, hfr_7m a ha hao]
    rcases ha with h1 | h1
    · left; dsimp only [posB]; linarith only [h1, Nat.zero_le ((2 + 3 * m₁) * L_sim)]
    · right; dsimp only [posB]; linarith only [h1, henc_split]
  refine runs_ret_le (Expr.eval_reg_of_eq hr15_end)
    ⟨rfl, horig_end, hlimbs_enc, hfr_end⟩ ?_
  have hcost_eq : encodeGAugCost [(nonloopEdges G).length, nlArr, tailArr, headArr, vIdxPtr, multArr, wArr, K,
      V_list.length, B.length, bArr, L_sim, 2 ^ h, origPtr, outArr] mem =
      110 * nl.length + (m₁ + B.length) * (70 * L_sim + 110) + 50 * L_sim + 120 := by
    unfold encodeGAugCost
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some]
    change 110 * nl.length + (((List.range nl.length).map fun j => mem (multArr + j)).sum + B.length) *
        (70 * L_sim + 110) + 50 * L_sim + 120 =
      110 * nl.length + (m₁ + B.length) * (70 * L_sim + 110) + 50 * L_sim + 120
    rw [hm₁_cost]
  change _ ≤ encodeGAugCost [(nonloopEdges G).length, nlArr, tailArr, headArr, vIdxPtr, multArr, wArr, K,
      V_list.length, B.length, bArr, L_sim, 2 ^ h, origPtr, outArr] mem
  have hm_nl_def : m₁ = ((nonloopEdges G).map mult).sum := rfl
  rw [hcost_eq, hm_nl_def, Nat.add_mul]
  dsimp only [argsSize, Expr.size, encodeBridgesCost, nl]
  have hm_B : B.length * (65 * L_sim + 100) ≤ B.length * (70 * L_sim + 110) :=
    Nat.mul_le_mul_left B.length (by omega)
  linarith only [hm_B]

theorem encodeGAug_meetsContract {w h a p w' s e : ℕ} {P : Program}
    (hp : P.HasAt e (encodeDecodeModule a p w' s e))
    (ha : P.HasAt a (arithModule a)) :
    MeetsContract w P (e + idxEncodeGAug) (encodeGAugContract w h) := by
  have hproc : P.procs[e + idxEncodeGAug]? = some (encodeGAugProc a e) := by
    have := hp 2 (by rw [encodeDecodeModule_length]; omega)
    simpa [encodeDecodeModule, idxEncodeGAug] using this
  refine meetsContract_of_runs hproc ?_
  intro args mem pos₀ ω hwords hpre
  rcases hpre with ⟨G, V_list, B, mult, w_orig,
    nlArr, tailArr, headArr, vIdxPtr, multArr, wArr, K, bArr, L_sim, origPtr, outArr,
    hargs, hG, hV_nd, hV_sub, hV_mem, hB_mem, hh, hw2, hK1, hKL, hV_lt, hmB_lt, hmB_w, hpre_tail⟩
  have hwords' : ∀ a ∈ [(nonloopEdges G).length, nlArr, tailArr, headArr, vIdxPtr, multArr, wArr, K,
      V_list.length, B.length, bArr, L_sim, 2 ^ h, origPtr, outArr], a < 2 ^ w := hargs ▸ hwords
  rw [hargs]
  rcases hpre_tail with ⟨hnl_w, htl_w, hhd_w, hvIdx_w, hmul_w, hwArr_w, hbArr_w, horig_w, hout_w, hdisj⟩
  rcases hdisj with ⟨hd_out_nl, hd_out_tl, hd_out_hd, hd_out_vIdx, hd_out_mult, hd_out_w, hd_out_b, hd_orig⟩
  rcases hd_orig with ⟨hd_orig_out, hd_orig_nl, hd_orig_tl, hd_orig_hd, hd_orig_vIdx, hd_orig_mult, hd_orig_w, hd_orig_b, hdata⟩
  rcases hdata with ⟨hnl_list, htl_list, hhd_list, hvIdx_spec, hmult_spec, hw_spec, hb_list⟩
  obtain ⟨st', c, hrun, horig_end, hlimbs_enc, hfr_end, hc⟩ :=
    encodeGAug_runs (ω := ω) (pos₀ := pos₀) hp ha G V_list B mult w_orig nlArr tailArr headArr vIdxPtr
      multArr wArr K bArr L_sim origPtr outArr hwords' hG hV_nd hV_sub hV_mem hB_mem hh hw2 hK1 hKL
      hV_lt hmB_lt hmB_w hnl_w htl_w hhd_w hvIdx_w hmul_w hwArr_w hbArr_w horig_w hout_w hd_out_nl
      hd_out_tl hd_out_hd hd_out_vIdx hd_out_mult hd_out_w hd_out_b hd_orig_out hd_orig_nl hd_orig_tl
      hd_orig_hd hd_orig_vIdx hd_orig_mult hd_orig_w hd_orig_b hnl_list htl_list hhd_list hvIdx_spec
      hmult_spec hw_spec hb_list
  exact ⟨.returned ((nonloopEdges G |>.map mult).sum), st', c, hrun,
    ⟨G, V_list, B, mult, w_orig, nlArr, tailArr, headArr, vIdxPtr, multArr, wArr, K, bArr, L_sim,
      origPtr, outArr, rfl, rfl, horig_end, hlimbs_enc, hfr_end⟩, hc⟩

end MinCostFlow.WideWord
