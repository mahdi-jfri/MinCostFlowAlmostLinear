module

public import MinCostFlow.DynSpanner.Program.DynSpannerShortcutEdge
public import MinCostFlow.DynSpanner.Program.DynSpannerLevelWalksDefs

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Walk-Shortcutting Verification (`DynSpannerShortcut`)

Proves `dsShortcutEmb_meetsContract` for `dsShortcutEmbStmt` (`lwIdxShortcutEmb = 2` in
`levelWalkProcs`) by verifying the layout address arithmetic preamble and the outer `forRange` loop
via `dsShortcutEdge_triple` and `rangeCost_shortcut_outer`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

public section

/-- Complete verification of `dsShortcutEmbStmt` against `dsShortcutEmbContract` at offset
`bLW + lwIdxShortcutEmb` in `levelWalkProcs bOps bRev`. -/
theorem dsShortcutEmb_meetsContract {w : ℕ} {p : Program} {bLW bOps bRev : ℕ}
    (hpLW : p.HasAt bLW (levelWalkProcs bOps bRev))
    (hpOps : p.HasAt bOps dgOpsProcs)
    {L vCap eCap b vCapG eCapG eCapEmb : ℕ}
    {G : MGraph} {eL : List ℕ} {emb : MinCostFlow.Embedding} :
    MeetsContract w p (bLW + lwIdxShortcutEmb)
      (dsShortcutEmbContract w L vCap eCap b vCapG eCapG eCapEmb G eL emb) := by
  refine meetsContract_of_runs
    (hpLW.get (i := lwIdxShortcutEmb) (by simp [levelWalkProcs, lwIdxShortcutEmb]))
    fun args mem0 pos ω _ hpre => ?_
  rcases hpre with ⟨gPtr, eListPtr, mEmbPtr, heapPtr, rfl, hw16, hb1, hfix, hmax_w,
    hg_w, heL_w, hm_w, hL, hvC, heC, hgen_w, hm_disj, hV_init, hG_disj, heL_disj,
    hNd_eL, hList_eL, hG, hG_val, hvG, hWalks⟩
  set heapMax := heapPtr + dsShortcutHeapSpace eL emb
  set vStampPtr := dsVStampBase b L vCap eCap
  set gen0 := mem0 (b + dsGenOff)
  set stampVal := gen0 + 1
  obtain ⟨hvs_eq, hvs_le⟩ := dsVStampBase_chain b L vCap eCap
  have hfix_w : b + dsFixedSize L vCap eCap < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hw7 : 7 < 2 ^ w := by omega
  have hw9 : 9 < 2 ^ w := by omega
  have hdsHdr : dsHdrSize = 6 := rfl
  refine runs_start_le ?_
  dsimp only [levelWalkProcs, lwIdxShortcutEmb, dsShortcutEmbStmt]
  refine runs_seq_assign_le (v := vCap)
    (Expr.eval_load_of_eq (x := b + dsVCapOff)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
        (Expr.eval_const (by simp [dsVCapOff]; omega)) (by simp [dsVCapOff]; omega)) hvC) ?_
  refine runs_seq_assign_le (v := eCap)
    (Expr.eval_load_of_eq (x := b + dsECapOff)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
        (Expr.eval_const (by simp [dsECapOff]; omega)) (by simp [dsECapOff]; omega)) heC) ?_
  refine runs_seq_assign_le (v := L)
    (Expr.eval_load_of_eq (x := b + dsLOff)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
        (Expr.eval_const (by simp [dsLOff]; omega)) (by simp [dsLOff]; omega)) hL) ?_
  set d := dynGraphSize vCap eCap
  have hd_eq : 4 + (7 * vCap + 9 * eCap) = d := by dsimp [d, dynGraphSize]; omega
  have hd_w : d < 2 ^ w := by
    have h1 := dsMinHBase_eq b vCap eCap
    have h2 : dsMinHBase b vCap eCap ≤ b + dsFixedSize L vCap eCap := by
      rw [← dsFixedSize_add]
      simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase,
        dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase,
        dsEdgeDomGenBase, dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase, dsHNextBase]
      omega
    omega
  refine runs_seq_assign_le (v := d)
    (by simp [Expr.eval, BinOp.eval, startState, hw4, hw7, hw9,
      show 7 * vCap < 2 ^ w by omega, show 9 * eCap < 2 ^ w by omega,
      show 7 * vCap + 9 * eCap < 2 ^ w by omega, hd_eq, hd_w]) ?_
  refine runs_seq_assign_le (v := b + dsHdrSize)
    (by simp [Expr.eval, BinOp.eval, startState, hdsHdr,
      show 6 < 2 ^ w by omega, show b + 6 < 2 ^ w by omega]) ?_
  set m := b + dsHdrSize + 3 * d
  have hm_lt_w : m < 2 ^ w := by
    have := dsMinHBase_eq b vCap eCap; omega
  refine runs_seq_assign_le (v := m)
    (by simp [Expr.eval, BinOp.eval, startState, hw3, m,
      show 3 * d < 2 ^ w by omega, show b + dsHdrSize + 3 * d < 2 ^ w by omega]) ?_
  set dom := m + (3 * eCap + 2 * (L + 1))
  have hdom_lt_w : dom < 2 ^ w := by omega
  refine runs_seq_assign_le (v := dom)
    (by simp [Expr.eval, BinOp.eval, startState, hw3, hw2, hw1, dom,
      show L + 1 < 2 ^ w by omega, show 3 * eCap < 2 ^ w by omega,
      show 2 * (L + 1) < 2 ^ w by omega, show 3 * eCap + 2 * (L + 1) < 2 ^ w by omega,
      hdom_lt_w]) ?_
  set rg := dom + ((L + 1) + 2 * ((L + 1) * eCap))
  have hrg_lt_w : rg < 2 ^ w := by omega
  refine runs_seq_assign_le (v := rg)
    (by simp [Expr.eval, BinOp.eval, startState, hw2, hw1, rg,
      show L + 1 < 2 ^ w by omega, show (L + 1) * eCap < 2 ^ w by omega,
      show 2 * ((L + 1) * eCap) < 2 ^ w by omega,
      show (L + 1) + 2 * ((L + 1) * eCap) < 2 ^ w by omega, hrg_lt_w]) ?_
  refine runs_seq_assign_le (v := vStampPtr)
    (by simp only [Expr.eval, BinOp.eval, startState,
        Function.update_self, Function.update_of_ne (by omega : (8 : ℕ) ≠ 9),
        Function.update_of_ne (by omega : (6 : ℕ) ≠ 9)]
        dsimp only [vStampPtr]
        rw [← hvs_eq]
        have hlt1 : L + 1 < 2 ^ w := by omega
        have hlt2 : (L + 1) * vCap < 2 ^ w := by omega
        have hlt3 : 3 * ((L + 1) * vCap) < 2 ^ w := by omega
        have hlt4 : 2 * (L + 1) < 2 ^ w := by omega
        have hlt5 : 2 * (L + 1) + vCap < 2 ^ w := by omega
        have hlt6 : 3 * ((L + 1) * vCap) + (2 * (L + 1) + vCap) < 2 ^ w := by omega
        have hlt7 : rg + (3 * ((L + 1) * vCap) + (2 * (L + 1) + vCap)) < 2 ^ w := by omega
        simp [hw1, hw2, hw3, hlt1, hlt2, hlt3, hlt4, hlt5, hlt6, hlt7]) ?_
  refine runs_seq_assign_le (v := stampVal)
    (Expr.eval_add
      (Expr.eval_load_of_eq (x := b + dsGenOff)
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
          (Expr.eval_const (by simp [dsGenOff]; omega)) (by simp [dsGenOff]; omega)) rfl)
      (Expr.eval_const hw1) (by simpa [stampVal, gen0] using hgen_w)) ?_
  let OuterInv (k : ℕ) (st : State) : Prop :=
    ∃ permPtr,
      st.regs 0 = b ∧ st.regs 1 = gPtr ∧ st.regs 2 = eListPtr ∧ st.regs 3 = eL.length ∧
      st.regs 4 = mEmbPtr ∧ st.regs 5 = permPtr ∧
      st.regs 6 = vStampPtr ∧ st.regs 7 = stampVal ∧ st.regs 8 = k ∧
      heapPtr ≤ permPtr ∧ permPtr ≤ heapPtr + dsShortcutHeapSpace (eL.take k) emb ∧
      (∀ v < vCap, st.mem (vStampPtr + v) ≤ gen0) ∧
      (∀ j < k, ∃ hj : j < eL.length,
        let e := eL[j]'hj
        let pi := shortcutWalk G (G.tail e) (emb e)
        heapPtr ≤ st.mem (mEmbPtr + e) ∧
        st.mem (mEmbPtr + e) + 1 + 2 * pi.length ≤ permPtr ∧
        MWalkAt st.mem (st.mem (mEmbPtr + e)) pi) ∧
      (∀ j, k ≤ j → ∀ hj : j < eL.length,
        let e := eL[j]'hj
        st.mem (mEmbPtr + e) = mem0 (mEmbPtr + e) ∧
        MWalkAt st.mem (st.mem (mEmbPtr + e)) (emb e)) ∧
      ∀ addr, dsShortcutFrameCond L vCap eCap b eCapEmb mEmbPtr heapPtr permPtr addr →
        st.mem addr = mem0 addr
  let stepCost (k : ℕ) : ℕ :=
    match eL[k]? with | some e => 400 * (emb e).length + 291 | none => 0
  let PreCond (st : State) : Prop :=
    st.mem = mem0 ∧ st.regs 0 = b ∧ st.regs 1 = gPtr ∧ st.regs 2 = eListPtr ∧
    st.regs 3 = eL.length ∧ st.regs 4 = mEmbPtr ∧ st.regs 5 = heapPtr ∧
    st.regs 6 = vStampPtr ∧ st.regs 7 = stampVal
  have hloop : Triple w p PreCond
      (forRange 8 (.const 0) (.reg 3) (dsShortcutEdgeStmt bOps))
      (normalPost (OuterInv eL.length))
      (fun _ => rangeCost stepCost 0 eL.length + eL.length * 9 + 7) := by
    have hfor : Triple w p PreCond
        (forRange 8 (.const 0) (.reg 3) (dsShortcutEdgeStmt bOps))
        (normalPost (OuterInv eL.length))
        (fun _ => rangeCost stepCost 0 eL.length +
          (eL.length - 0) * ((Expr.reg 3).size + 8) +
          ((Expr.const 0).size + (Expr.reg 3).size + 5)) :=
      Triple.forRange_le (p := p) (P := PreCond)
        (r := 8) (lo := .const 0) (hi := .reg 3) (Inv := OuterInv)
        stepCost 0 eL.length (Nat.zero_le _) hw1
      (fun _ => by omega)
      (fun st ⟨hsm, hr0', hr1', hr2', hr3', hr4', hr5', hr6', hr7'⟩ => by
        subst hsm
        refine ⟨Expr.eval_const (by omega), heapPtr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          le_rfl, ?_, hV_init, fun _ hj => by omega,
          fun j _ hj => ⟨rfl, (hWalks _ (List.getElem_mem hj)).2.2.2.1⟩, fun _ _ => rfl⟩ <;>
          simp [hr0', hr1', hr2', hr3', hr4', hr5', hr6', hr7'])
      (fun _ _ _ _ ⟨_, _, _, _, _, _, _, _, _, hr8, _⟩ => hr8)
      (fun _ _ _ _ ⟨_, _, _, _, hr3, _⟩ => Expr.eval_reg_of_eq hr3)
      (fun k _ hk => by
        intro st ω ⟨permPtr, hr0', hr1', hr2', hr3', hr4', hr5', hr6', hr7', hr8',
          hhp_p, hp_hi, hV_st, hDone, hTodo, hfr_st⟩
        set e := eL[k]'hk
        set P := emb e
        obtain ⟨heG, he_cap, hWalk, _, hwPtr_w, hW_disj⟩ := hWalks e (List.getElem_mem hk)
        have hperm_take := dsShortcutHeapSpace_take_succ eL emb hk
        have htake_le := dsShortcutHeapSpace_take_le eL emb (k + 1)
        have hperm_next_hi : permPtr + 7 * (P.length + 1) ≤ heapMax := by
          dsimp only [heapMax, P, e]; omega
        have hp_le_max : permPtr ≤ heapMax :=
          le_trans hp_hi (Nat.add_le_add_left (dsShortcutHeapSpace_take_le eL emb k) heapPtr)
        have he_mem_L : st.mem (eListPtr + k) = e := by
          rw [hfr_st (eListPtr + k) (dsShortcutFrameCond_mono hp_le_max (heL_disj k hk))]
          exact hList_eL.getElem hk
        have hG_cur : DynGraphAt st.mem gPtr vCapG eCapG G :=
          hG.of_agree fun a ha1 ha2 =>
            hfr_st a (dsShortcutFrameCond_mono hp_le_max
              (by have := hG_disj (a - gPtr) (by omega); rwa [Nat.add_sub_of_le ha1] at this))
        have hW_disj_cur : ∀ addr, mem0 (mEmbPtr + e) ≤ addr →
            addr < mem0 (mEmbPtr + e) + 1 + 2 * P.length →
            dsShortcutFrameCond L vCap eCap b eCapEmb mEmbPtr heapPtr heapMax addr := hW_disj
        have hG_disj_cur : ∀ i < dynGraphSize vCapG eCapG,
            dsShortcutFrameCond L vCap eCap b eCapEmb mEmbPtr heapPtr heapMax (gPtr + i) :=
          hG_disj
        obtain ⟨hm_e_eq, hMW_cur⟩ := hTodo k le_rfl hk
        obtain ⟨oE, stE, cE, hrunE, hqE, hcE⟩ :=
          dsShortcutEdge_triple (p := p) (bOps := bOps) hpOps hw16 hfix hhp_p hperm_next_hi
            hmax_w hg_w heL_w hm_w hk (by omega : gen0 < stampVal) hm_disj hG_disj_cur
            he_mem_L heG he_cap hWalk (hm_e_eq ▸ hMW_cur) (hm_e_eq ▸ hwPtr_w)
            (hm_e_eq ▸ hW_disj_cur) hG_cur hG_val hvG hV_st
            ⟨hr0', hr1', hr2', hr3', hr4', hr5', hr6', hr7', hr8'⟩ st ω ⟨rfl, rfl⟩
        cases oE with
        | returned _ => exact False.elim hqE
        | normal =>
          rcases hqE with ⟨outWalkPtr, hnp_lo, hnp_hi, hr5E, hrE, hm_e_E, hMW_E, hV_E, hfr_E⟩
          let endPtr := outWalkPtr + 1 + 2 * (shortcutWalk G (G.tail e) P).length
          have hm'_other : ∀ {j : ℕ} (hj : j < eL.length), j ≠ k →
              stE.mem (mEmbPtr + eL[j]'hj) = st.mem (mEmbPtr + eL[j]'hj) := fun {j} hj hne => by
            have he' := hWalks _ (List.getElem_mem hj)
            have hne_e : mEmbPtr + eL[j]'hj ≠ mEmbPtr + e := fun heq =>
              absurd (hNd_eL.getElem_inj_iff.mp (by omega)) hne
            exact hfr_E _ (hm_disj _ he'.2.1).1 hne_e
              (by rcases (hm_disj _ he'.2.1).2 with h | h <;> [left; right] <;> omega)
          refine ⟨.normal, stE, cE, hrunE, ?_, ?_⟩
          · refine ⟨⟨endPtr,
              hrE 0 (Or.inl (by omega)) |>.trans hr0',
              hrE 1 (Or.inl (by omega)) |>.trans hr1',
              hrE 2 (Or.inl (by omega)) |>.trans hr2',
              hrE 3 (Or.inl (by omega)) |>.trans hr3',
              hrE 4 (Or.inl (by omega)) |>.trans hr4',
              hr5E,
              (hrE 6 (Or.inr ⟨by omega, by omega⟩)).trans hr6',
              (hrE 7 (Or.inr ⟨by omega, by omega⟩)).trans hr7',
              by simp,
              le_trans hhp_p (le_trans hnp_lo (by omega)),
              by rw [hperm_take]
                 dsimp only [endPtr, P, e] at hnp_hi ⊢
                 omega,
              hV_E, ?_, ?_, ?_⟩,
              (hrE 8 (Or.inr ⟨by omega, le_rfl⟩)).trans hr8'⟩
            · intro j hj
              rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt | hj_eq
              · obtain ⟨hj_eL, h1, h2, h3⟩ := hDone j hj_lt
                have hm'_eq := hm'_other hj_eL (by omega)
                refine ⟨hj_eL, by rw [hm'_eq]; exact h1,
                  by rw [hm'_eq]; exact le_trans h2 (le_trans hnp_lo (by omega)), ?_⟩
                rw [hm'_eq]
                exact h3.of_agree fun a ha1 ha2 =>
                  hfr_E a (fun v hv => by have := dsVStampBase_le_fixed b L vCap eCap; omega)
                    (fun _ => by
                      rcases (hm_disj e (hWalks e (List.getElem_mem hk)).2.1).2 with h | h <;>
                        omega)
                    (Or.inl (lt_of_lt_of_le ha2 h2))
              · refine ⟨by omega, ?_, ?_, ?_⟩
                · dsimp only; simp only [hj_eq]; change heapPtr ≤ stE.mem (mEmbPtr + e)
                  rw [hm_e_E]; exact le_trans hhp_p hnp_lo
                · dsimp only [e, P]; simp only [hj_eq] at *; rw [hm_e_E]
                · dsimp only [e, P]; simp only [hj_eq] at *; rw [hm_e_E]; exact hMW_E
            · intro j hkj hj_eL
              have hm'_eq := hm'_other hj_eL (by omega)
              obtain ⟨hm_eq0, hMW0⟩ := hTodo j (by omega) hj_eL
              refine ⟨hm'_eq.trans hm_eq0, ?_⟩
              rw [hm'_eq, hm_eq0]
              exact (hWalks _ (List.getElem_mem hj_eL)).2.2.2.1.of_agree fun a ha1 ha2 => by
                have hfc := (hWalks _ (List.getElem_mem hj_eL)).2.2.2.2.2 a ha1 ha2
                rw [hfr_E a hfc.1 (hfc.2.1 e he_cap)
                  (by rcases hfc.2.2 with h | h <;> [left; right] <;> omega)]
                exact hfr_st a (dsShortcutFrameCond_mono hp_le_max hfc)
            · intro addr hfc
              have hfcE : (∀ v < vCap, addr ≠ vStampPtr + v) ∧ addr ≠ mEmbPtr + e ∧
                  (addr < permPtr ∨ endPtr ≤ addr) := by
                refine ⟨hfc.1, hfc.2.1 e he_cap, ?_⟩
                rcases hfc.2.2 with h | h
                · exact Or.inl (lt_of_lt_of_le h hhp_p)
                · exact Or.inr h
              rw [hfr_E addr hfcE.1 hfcE.2.1 hfcE.2.2]
              exact hfr_st addr (dsShortcutFrameCond_mono (le_trans hnp_lo (by omega)) hfc)
          · dsimp only [stepCost]
            rw [List.getElem?_eq_getElem hk]
            dsimp only [P, e] at hcE ⊢
            omega)
    refine hfor.conseq (fun _ h => h) (fun o st h => h) ?_
    intro st _
    dsimp only [Expr.size]
    omega
  refine runs_seq_triple_le hloop ⟨rfl, by simp [startState], by simp [startState],
    by simp [startState], by simp [startState], by simp [startState], by simp [startState],
    by simp [startState], by simp [startState]⟩ ?_
  intro stF ⟨permPtr, hr0', hr1', hr2', hr3', hr4', hr5', hr6', hr7', hr8',
    hhp_p, hp_hi, hV_F, hDone, hTodo, hfr_F⟩
  have htake_all : eL.take eL.length = eL := List.take_length
  rw [htake_all] at hp_hi
  refine runs_ret_le (Expr.eval_reg_of_eq hr5') ?_ ?_
  · refine ⟨gPtr, eListPtr, mEmbPtr, heapPtr, rfl, hhp_p, hp_hi, hV_F, ?_, ?_⟩
    · intro e he
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp he
      obtain ⟨_, h1, h2, h3⟩ := hDone j hj
      exact ⟨h1, h2, h3⟩
    · exact hfr_F
  · have hrc_le : rangeCost stepCost 0 eL.length + eL.length * 9 ≤
        400 * (eL.map fun e => (emb e).length).sum + 300 * eL.length := by
      have h1 : rangeCost stepCost 0 eL.length + eL.length * 9 =
          rangeCost (fun k => stepCost k + 9) 0 eL.length := by
        rw [rangeCost_add, rangeCost_const]; omega
      have h2 := rangeCost_mono (f := fun k => stepCost k + 9)
        (g := fun k => match eL[k]? with | some e => 400 * (emb e).length + 300 | none => 0)
        (lo := 0) (hi := eL.length) (fun k _ hk => by
          dsimp only [stepCost]
          simp [List.getElem?_eq_getElem hk])
      have hrc := rangeCost_shortcut_outer eL emb
      have h2_le := le_trans h2 hrc.le
      omega
    dsimp only [dsShortcutEmbContract, Expr.size]
    omega

end

end MinCostFlow.DynSpanner.Program
