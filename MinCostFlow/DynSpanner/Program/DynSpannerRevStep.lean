module

public import MinCostFlow.DynSpanner.Program.DynSpannerRevHelpers

import Mathlib.Tactic.Linarith
import MinCostFlow.DynSpanner.Program.DynSpannerRevStepMiss

/-!
# Loop step lemma for `dsInsertWalkRev` (`DynSpannerRevStep`)

Proves `dsInsertWalkRev_step_triple`, dispatching on whether `cur` was already visited during the
walk traversal and delegating the unvisited case to `dsInsertWalkRev_step_miss_triple`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

public section

lemma dsInsertWalkRev_step_triple {w L vCap eCap b i e uStart wPtr hPtr heapPtr gen0 k : ℕ}
    {H : MGraph} {W : List (ℕ × Bool)} {rev0 : ℕ → List ℕ} {foot0 : ℕ → Prop}
    {mem : ℕ → ℕ} {p : Program} {bOps bRev : ℕ}
    (hpRev : p.HasAt bRev (revProcs bOps bRev)) (hpOps : p.HasAt bOps dgOpsProcs)
    (hw16 : 16 ≤ 2 ^ w) (hfix_le : b + dsFixedSize L vCap eCap ≤ heapPtr)
    (hheap_lt : heapPtr + 2 * (W.length + 1) < 2 ^ w)
    (hiL : i ≤ L) (he_lt : e < 2 ^ w)
    (hfix_w : b + dsFixedSize L vCap eCap ≤ wPtr) (hw_hp : wPtr + (2 * W.length + 1) ≤ heapPtr)
    (hb_h : b + dsHdrSize ≤ hPtr) (hh_min : hPtr + dynGraphSize vCap eCap ≤ dsMinHBase b vCap eCap)
    (hL : mem (b + dsLOff) = L) (hvC : mem (b + dsVCapOff) = vCap) (heC : mem (b + dsECapOff) = eCap)
    (hgen_lt : gen0 + 1 < 2 ^ w)
    (hdom_pos : 0 < mem (dsDomGenBase b L vCap eCap + i))
    (hfoot0 : ∀ a, foot0 a → b + dsFixedSize L vCap eCap ≤ a ∧ a < heapPtr)
    (hH : DynGraphAt mem hPtr vCap eCap H) (hH_val : H.IsValid)
    (hvH : ∀ v ∈ H.V, v < vCap) (heH : ∀ e' ∈ H.E, e' < eCap)
    (huH : uStart ∈ H.V) {vEnd : ℕ} (hWalk : H.IsWalk uStart vEnd W) (hMWalk : MWalkAt mem wPtr W)
    (hb_ltw : b < 2 ^ w) (hi_ltw : i < 2 ^ w) (he_ltw : e < 2 ^ w)
    (hwPtr_ltw : wPtr < 2 ^ w) (hhPtr_ltw : hPtr < 2 ^ w)
    (hh_ltw : hPtr + dynGraphSize vCap eCap < 2 ^ w)
    (hk : k < W.length)
    {st : State} {ω : ℕ → Bool}
    (hInv : dsInsertWalkRevInv L vCap eCap b i e uStart wPtr hPtr heapPtr gen0 H W rev0 foot0 mem k st) :
    ∃ o st' c, Runs w p ω
      (.assign 14 (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 13))) ;;
       .assign 15 (.load (.bin .add (.reg 4) (.reg 14))) ;;
       .assign 14 (.load (.bin .add (.bin .add (.reg 4) (.reg 14)) (.const 1))) ;;
       .cond (.reg 14)
         (.call 15 (bOps + dgIdxGetHead) [.reg 5, .reg 15])
         (.call 15 (bOps + dgIdxGetTail) [.reg 5, .reg 15]) ;;
       .assign 14 (.load (.bin .add (.reg 10) (.reg 15))) ;;
       .cond (.bin .eq (.reg 14) (.reg 11))
         (.nop)
         (.store (.bin .add (.reg 10) (.reg 15)) (.reg 11) ;;
          .call 6 (bRev + revIdxRevCons) [.reg 0, .reg 1, .reg 15, .reg 2, .reg 6]))
      st o st' c ∧
      normalPost (fun st₁ =>
        dsInsertWalkRevInv L vCap eCap b i e uStart wPtr hPtr heapPtr gen0 H W rev0 foot0 mem (k + 1)
          { st₁ with regs := Function.update st₁.regs 13 (k + 1) } ∧
        st₁.regs 13 = k) o st' ∧
      c ≤ 360 := by
  let vStamp := dsVStampBase b L vCap eCap
  let domAddr := dsDomGenBase b L vCap eCap + i
  let domVal := mem domAddr
  let footOf (heapCur : ℕ) (a : ℕ) : Prop := foot0 a ∨ (heapPtr ≤ a ∧ a < heapCur)
  rcases hInv with ⟨heapCur, hhp1, hhp2, hr0, hr1, hr2, hr4, hr5, hr6, hr10, hr11,
    hr12, hr13, hmg, hvst, hrev, hfr⟩
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have h2_lt : (2 : ℕ) < 2 ^ w := by omega
  have h0_lt : (0 : ℕ) < 2 ^ w := by omega
  have hk1_le : k + 1 ≤ W.length := hk
  have hstep_b : heapCur + 2 < 2 ^ w := by linarith only [hhp2, hk1_le, hheap_lt]
  have hk_ltw : k < 2 ^ w := by linarith only [hk, hheap_lt]
  have h2k_ltw : 2 * k < 2 ^ w := by linarith only [hk1_le, hheap_lt]
  have h12k_ltw : 1 + 2 * k < 2 ^ w := by linarith only [hk1_le, hheap_lt]
  have hw_addr1 : wPtr + (1 + 2 * k) < 2 ^ w := by linarith only [hk1_le, hw_hp, hheap_lt]
  have hw_addr2 : wPtr + (1 + 2 * k) + 1 < 2 ^ w := by linarith only [hk1_le, hw_hp, hheap_lt]
  have hx_info := isWalk_mem_V_tail_head hH_val huH hWalk W[k] (List.getElem_mem hk)
  have heStep_E : W[k].1 ∈ H.E := hx_info.1
  have hcur_V : H.dst W[k] ∈ H.V := hx_info.2
  let cur := H.dst W[k]
  have hcur_vCap : cur < vCap := hvH _ hcur_V
  have hdisj := dsLayout_facts hiL hcur_vCap hiL hcur_vCap hfix_le
  have hdom_fix := hdisj.dom_lt_fix
  have hvs_fix : vStamp + vCap ≤ b + dsFixedSize L vCap eCap := by
    have := dsAddrs_bound hfix_le (by linarith only [hheap_lt])
    exact this.2.2.2.2.2.2.2.2.2.1
  have hvs_ltw : vStamp + cur < 2 ^ w := by linarith only [hdisj.vs_lt_hp, hheap_lt]
  have hmin_fix : hPtr + dynGraphSize vCap eCap ≤ b + dsFixedSize L vCap eCap := by
    have h1 := dsMinHBase_eq b vCap eCap
    have h2 := dsDomGenBase_eq b L vCap eCap
    have h3 := dsRevGenBase_eq b L vCap eCap
    have h4 := dsRevHeadBase_eq b L vCap eCap
    have h5 := dsVStampBase_eq b L vCap eCap
    have hm := dsMEmbTempBase_eq_rev b L vCap eCap
    have hf := dsFixedSize_add b L vCap eCap
    omega
  have hgen_lt_fix : b + dsGenOff < b + dsFixedSize L vCap eCap := by
    have : dsGenOff < dsHdrSize := by decide
    have h1 := dsMinHBase_eq b vCap eCap
    have h2 := dsDomGenBase_eq b L vCap eCap
    have h3 := dsRevGenBase_eq b L vCap eCap
    have h4 := dsRevHeadBase_eq b L vCap eCap
    have h5 := dsVStampBase_eq b L vCap eCap
    have hm := dsMEmbTempBase_eq_rev b L vCap eCap
    have hf := dsFixedSize_add b L vCap eCap
    omega
  have hH_st : DynGraphAt st.mem hPtr vCap eCap H := by
    refine dynGraphAt_of_agree hH fun addr ha1 ha2 => ?_
    refine hfr addr
      (Nat.ne_of_gt (by
        have hgd : dsGenOff < dsHdrSize := by decide
        linarith only [hb_h, ha1, hgd]))
      (fun v hv => Nat.ne_of_lt (by
        have h1 := dsMinHBase_eq b vCap eCap; have h2 := dsDomGenBase_eq b L vCap eCap
        have h3 := dsRevGenBase_eq b L vCap eCap; have h4 := dsRevHeadBase_eq b L vCap eCap
        have h5 := dsVStampBase_eq b L vCap eCap; omega))
      (fun v hv => Nat.ne_of_lt (by
        have h1 := dsMinHBase_eq b vCap eCap; have h2 := dsDomGenBase_eq b L vCap eCap
        have h3 := dsRevGenBase_eq b L vCap eCap; omega))
      (fun v hv => Nat.ne_of_lt (by
        have h1 := dsMinHBase_eq b vCap eCap; have h2 := dsDomGenBase_eq b L vCap eCap
        have h3 := dsRevGenBase_eq b L vCap eCap; have h4 := dsRevHeadBase_eq b L vCap eCap; omega))
      (Or.inl (by linarith only [ha2, hmin_fix, hfix_le]))
  have hW_st : MWalkAt st.mem wPtr W := by
    refine hMWalk.of_agree fun addr ha1 ha2 => ?_
    have ha_hp : addr < heapPtr := by linarith only [ha2, hw_hp]
    refine hfr addr (Nat.ne_of_gt (by linarith only [hfix_w, ha1, hgen_lt_fix]))
      (fun v hv => Nat.ne_of_gt (by
        have hvs := (dsLayout_facts hiL hv hiL hv hfix_le).vs_lt_fix
        linarith only [hfix_w, ha1, hvs]))
      (fun v hv => Nat.ne_of_gt (by
        have hrg := (dsLayout_facts hiL hv hiL hv hfix_le).rg_lt_fix
        linarith only [hfix_w, ha1, hrg]))
      (fun v hv => Nat.ne_of_gt (by
        have hrh := (dsLayout_facts hiL hv hiL hv hfix_le).rh_lt_fix
        linarith only [hfix_w, ha1, hrh]))
      (Or.inl ha_hp)
  have hmem_e : st.mem (wPtr + (1 + 2 * k)) = W[k].1 := by
    simpa [Nat.add_assoc] using MWalkAt_step_edge hW_st hk
  have hmem_d : st.mem (wPtr + (1 + 2 * k) + 1) = if W[k].2 then 1 else 0 := by
    simpa [Nat.add_assoc] using MWalkAt_step_dir hW_st hk
  have heStep_ltw : W[k].1 < 2 ^ w := by
    have he_cap := heH _ heStep_E
    have he_lt_fix : eCap ≤ b + dsFixedSize L vCap eCap := by
      have h1 := dsMinHBase_eq b vCap eCap; have h2 := dsDomGenBase_eq b L vCap eCap
      have h3 := dsRevGenBase_eq b L vCap eCap; have h4 := dsRevHeadBase_eq b L vCap eCap
      have h5 := dsVStampBase_eq b L vCap eCap; have hm := dsMEmbTempBase_eq_rev b L vCap eCap
      have hf := dsFixedSize_add b L vCap eCap; omega
    linarith only [he_cap, he_lt_fix, hfix_le, hheap_lt]
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := 1 + 2 * k)
    (by simp [Expr.eval, BinOp.eval, hr13, h1_lt, h2_lt, h2k_ltw, h12k_ltw]) ?_
  refine runs_seq_assign_le (v := W[k].1)
    (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, hr4, hw_addr1]) hmem_e) ?_
  refine runs_seq_assign_le (v := if W[k].2 then 1 else 0)
    (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, hw_addr1, hw_addr2, hr4, h1_lt]) hmem_d) ?_
  refine runs_seq_triple_le
    (dsInsertWalkRev_dir_triple (b := b) (i := i) (e := e) (wPtr := wPtr) (heapCur := heapCur)
      (vStamp := vStamp) (gen1 := gen0 + 1) (len := W.length) (k := k) (eStep := W[k].1)
      (dir := W[k].2) hpOps hw16 hh_ltw hhPtr_ltw heStep_ltw heStep_E hH_st)
    ⟨rfl, by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr4], by simp [hr5],
      by simp [hr6], by simp [hr10, vStamp], by simp [hr11], by simp [hr12], by simp [hr13],
      by simp, by simp⟩ ?_
  intro st_d ⟨hm_d, dr0, dr1, dr2, dr4, dr5, dr6, dr10, dr11, dr12, dr13, dr15⟩
  have hcur_eq : H.dst (W[k].1, W[k].2) = cur := rfl
  have hvs_ltw' : vStamp + H.dst (W[k].1, W[k].2) < 2 ^ w := hcur_eq ▸ hvs_ltw
  have heval_vs : (Expr.load (.bin .add (.reg 10) (.reg 15))).eval w st_d =
      some (st.mem (vStamp + cur)) := by
    refine Expr.eval_load_of_eq (x := vStamp + cur) ?_ (by rw [hm_d])
    dsimp only [vStamp] at dr10 hvs_ltw ⊢
    simp [Expr.eval, BinOp.eval, dr10, dr15, hcur_eq, hvs_ltw]
  refine runs_seq_assign_le (v := st.mem (vStamp + cur)) heval_vs ?_
  have hst_cur := hvst cur hcur_vCap
  by_cases hhit : cur ∈ H.walkVertices uStart (W.take k)
  · simp only [hhit, ↓reduceIte] at hst_cur
    have hcond1 : (Expr.bin .eq (.reg 14) (.reg 11)).eval w
        { st_d with regs := Function.update st_d.regs 14 (st.mem (vStamp + cur)) } = some 1 := by
      have hw_ne0 : w ≠ 0 := by intro h; subst h; simp at hw16
      dsimp only [vStamp] at hst_cur ⊢
      simp [Expr.eval, BinOp.eval, dr11, hst_cur, hw_ne0]
    refine runs_cond_le (v := 1) hcond1
      (fun _ => runs_nop_le ?_ (by dsimp only [Expr.size]; omega))
      (fun h => False.elim (by omega))
    dsimp only [normalPost]
    refine ⟨⟨heapCur, hhp1, by omega, by simp [dr0], by simp [dr1], by simp [dr2],
      by simp [dr4], by simp [dr5], by simp [dr6], by simp [dr10, vStamp], by simp [dr11],
      by simp [dr12], by simp, ?_, ?_, ?_, ?_⟩, by simp [dr13]⟩
    · dsimp only; rw [hm_d]; exact hmg
    · intro v hv
      have hsucc := walkVertices_take_succ (H := H) (uStart := uStart) hk v
      have hvt := hvst v hv
      dsimp only
      by_cases hv_k : v ∈ H.walkVertices uStart (W.take k)
      · have hv1 : v ∈ H.walkVertices uStart (W.take (k + 1)) := hsucc.mpr (Or.inl hv_k)
        simp only [hv1, ↓reduceIte, hm_d]
        simpa [hv_k] using hvt
      · by_cases hvc : v = cur
        · subst hvc; contradiction
        · have hv1 : v ∉ H.walkVertices uStart (W.take (k + 1)) := fun h =>
            (hsucc.mp h).elim hv_k hvc
          simp only [hv1, ↓reduceIte, hm_d]
          simpa [hv_k] using hvt
    · intro v hv
      have hsucc := walkVertices_take_succ (H := H) (uStart := uStart) hk v
      have hr_v := hrev v hv
      dsimp only
      by_cases hv_k : v ∈ H.walkVertices uStart (W.take k)
      · have hv1 : v ∈ H.walkVertices uStart (W.take (k + 1)) := hsucc.mpr (Or.inl hv_k)
        simp only [hv1, ↓reduceIte, hm_d]
        simpa [hv_k] using hr_v
      · by_cases hvc : v = cur
        · subst hvc; contradiction
        · have hv1 : v ∉ H.walkVertices uStart (W.take (k + 1)) := fun h =>
            (hsucc.mp h).elim hv_k hvc
          simp only [hv1, ↓reduceIte, hm_d]
          simpa [hv_k] using hr_v
    · intro addr ha1 ha2 ha3 ha4 ha5
      dsimp only; rw [hm_d]
      exact hfr addr ha1 ha2 ha3 ha4 ha5
  · simp only [hhit, ↓reduceIte] at hst_cur
    have hne_st : st.mem (vStamp + cur) ≠ gen0 + 1 := by
      dsimp only [vStamp]; linarith only [hst_cur]
    have hcond0 : (Expr.bin .eq (.reg 14) (.reg 11)).eval w
        { st_d with regs := Function.update st_d.regs 14 (st.mem (vStamp + cur)) } = some 0 := by
      simp [Expr.eval, BinOp.eval, dr11, hne_st]
    refine runs_cond_le (v := 0) hcond0 (fun h => False.elim (by omega)) fun _ =>
      dsInsertWalkRev_step_miss_triple hpRev hw16 hfix_le hheap_lt hiL he_lt hb_h hh_min
        hL hvC heC hgen_lt hdom_pos hfoot0 hvH hb_ltw hi_ltw he_ltw hk
        (by dsimp only [Expr.size]; omega) hhp1 hhp2 dr0 dr1 dr2 dr4 dr5 dr6 dr10 dr11 dr12 dr13
        hm_d dr15 hmg hvst hrev hfr hcur_V hhit

end

end MinCostFlow.DynSpanner.Program
