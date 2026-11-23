module

public import MinCostFlow.DynSpanner.Program.DynSpannerWalkPtrsLevel

/-!
# Walk pointers of the affected edges: the contract

`dsWalkPtrs_meetsContract` proves that `dsWalkPtrsStmt` meets `dsWalkPtrsContract`. The prefix
computes the bases of the state, as in the filter (`dsFilterAffected_bases_triple`). Each loop
step (`dsWalkPtrs_step_triple`) reads the edge `e`, finds its level with
`dsWalkPtrs_findLevel_triple`, reads the walk pointer of `e` at that level and stores it. The
walk itself lies in the footprint `footPi`, which is disjoint from the table, so the stores do
not change it.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

public section

/-- One loop step of `dsWalkPtrsStmt`, cost `35 · j + 40`. -/
theorem dsWalkPtrs_step_triple (c : FilterCtx) {p : Program} {idx : ℕ} (hidx : idx < c.candLen) :
    Triple c.w p (WPInv c idx) dsWalkPtrsBodyStmt
      (normalPost fun st₁ =>
        WPInv c (idx + 1) { st₁ with regs := Function.update st₁.regs 14 (idx + 1) } ∧
          st₁.regs 14 = idx)
      (fun _ => 35 * c.j + 40) := by
  have hlay := c.lay
  have hw16 := c.hw16
  have hk_c : idx < c.cand.length := by have := c.hcand_len; omega
  set e := c.cand[idx]'hk_c
  have he_mem : e ∈ c.cand := List.getElem_mem _
  obtain ⟨he_G, he_cap⟩ := c.hcand_sub e he_mem
  intro st ω hfm
  have hr2 : st.regs 2 = c.candPtr := hfm.1.2.2.1
  have hr4 : st.regs 4 = c.outArrPtr := hfm.1.2.2.2.2.1
  have hr10 : st.regs 10 = dsPiPtrBase c.b c.L c.vCap c.eCap := hfm.1.2.2.2.2.2.2.2.2.2.2.1
  have hr14 : st.regs 14 = idx := hfm.2.1
  have hcand_idx_w : c.candPtr + idx < 2 ^ c.w := by have := c.hcand_w; omega
  have he_eq_mem : st.mem (c.candPtr + idx) = e := hfm.read_cand hidx
  let m₁ := findEmbLevel c.inDom_mid c.j e
  have hm1_lt := findEmbLevel_lt c.inDom_mid c.h1j c.hjL e
  let ptr := c.mem0 (dsPiPtrBase c.b c.L c.vCap c.eCap + m₁ * c.eCap + e)
  have hout_w : c.outArrPtr + idx < 2 ^ c.w := by have := c.hout_w; omega
  dsimp only [dsWalkPtrsBodyStmt]
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := e)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr2) (Expr.eval_reg_of_eq hr14)
      hcand_idx_w) he_eq_mem) ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  let rInit : ℕ → ℕ := Function.update st.regs 15 e
  refine runs_seq_triple_le
    (dsWalkPtrs_findLevel_triple c he_G he_cap rInit)
    ⟨WPInv.of_regs_agree hfm rfl
        (fun r hr _ => by simp [show r ≠ 15 by omega, show r ≠ 16 by omega]) (by simp),
      by simp, by simp,
      fun r hr _ => by
        dsimp only [rInit]
        by_cases h15 : r = 15
        · subst h15; simp
        · simp [show r ≠ 16 by omega, h15]⟩
    ?_
  intro st1 ⟨hfm1, hr15_1, hr16_1, hfr1⟩
  have hm1_e_lt : m₁ * c.eCap + e < (c.L + 1) * c.eCap := by
    have h1 : m₁ * c.eCap + e < m₁ * c.eCap + c.eCap := by omega
    have h2 : (m₁ + 1) * c.eCap ≤ (c.L + 1) * c.eCap := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.succ_mul] at h2; omega
  have hm1_e_w : m₁ * c.eCap + e < 2 ^ c.w := lt_trans hm1_e_lt hlay.Le_w
  have hm1_mul_w : m₁ * c.eCap < 2 ^ c.w := by omega
  have hpi_lt_fix : dsPiPtrBase c.b c.L c.vCap c.eCap + (m₁ * c.eCap + e) <
      c.b + dsFixedSize c.L c.vCap c.eCap := by
    have := hlay.sb_eq; have := hlay.sb_le_fix; omega
  have hpi_w : dsPiPtrBase c.b c.L c.vCap c.eCap + (m₁ * c.eCap + e) < 2 ^ c.w := by
    have := hlay.pi_lt_w; omega
  have hptr_mem : st1.mem (dsPiPtrBase c.b c.L c.vCap c.eCap + (m₁ * c.eCap + e)) = ptr := by
    rw [hfm1.read_fix hpi_lt_fix, ← Nat.add_assoc]
  have h10_1 : st1.regs 10 = dsPiPtrBase c.b c.L c.vCap c.eCap :=
    hfm1.1.2.2.2.2.2.2.2.2.2.2.1
  have h4_1 : st1.regs 4 = c.outArrPtr := hfm1.1.2.2.2.2.1
  have h14_1 : st1.regs 14 = idx := hfm1.2.1
  refine runs_seq_assign_le (v := ptr)
    (Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq h10_1)
        (Expr.eval_add
          (Expr.eval_mul (Expr.eval_reg_of_eq hr16_1) (Expr.eval_reg_of_eq hfm1.1.r6) hm1_mul_w)
          (Expr.eval_reg_of_eq hr15_1) hm1_e_w)
        hpi_w)
      hptr_mem) ?_
  refine runs_store_le (x := c.outArrPtr + idx) (v := ptr)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simpa using h4_1))
      (Expr.eval_reg_of_eq (by simpa using h14_1)) hout_w)
    (Expr.eval_reg_of_eq (by simp)) ?_ (by dsimp only [Expr.size]; omega)
  have hfix2 : FilterFixedRegs c { st1 with regs := Function.update st1.regs 17 ptr } :=
    hfm1.1.agree fun r hr _ => by simp [show r ≠ 17 by omega]
  refine ⟨⟨hfix2.agree fun r hr _ => by simp [show r ≠ 14 by omega], by simp, ?_, ?_⟩,
    by simpa using h14_1⟩
  · intro k hk hki
    by_cases hki' : k = idx
    · subst hki'
      simp [FilterCtx.walkPtr, ptr, m₁, e]
    · have hne : c.outArrPtr + k ≠ c.outArrPtr + idx := by omega
      simp only [Function.update_of_ne hne]
      exact hfm1.2.2.1 k hk (by omega)
  · intro addr ha
    have hne : addr ≠ c.outArrPtr + idx := by omega
    simp only [Function.update_of_ne hne]
    exact hfm1.2.2.2 addr ha

/-- `dsWalkPtrsStmt` meets `dsWalkPtrsContract`, cost `|es| · (35 · j + 60) + 150`. -/
theorem dsWalkPtrs_meetsContract (c : FilterCtx) {p : Program} {bW : ℕ}
    (hpW : p.HasAt bW walkPtrsProcs) :
    MeetsContract c.w p (bW + walkPtrsIdx) (dsWalkPtrsContract c) := by
  refine meetsContract_of_runs
    (hpW.get (i := walkPtrsIdx) (by simp [walkPtrsProcs, walkPtrsIdx])) ?_
  rintro args mem pos ω _ ⟨rfl, hmem⟩
  subst hmem
  have hlay := c.lay
  have hw16 := c.hw16
  have hlen := c.hcand_len
  simp only [walkPtrsProcs, walkPtrsIdx, List.getElem_cons_zero]
  dsimp only [dsWalkPtrsStmt]
  refine runs_start_le ?_
  refine runs_seq_triple_le (dsFilterAffected_bases_triple c)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_
  intro st1 ⟨hm1, hf1, _⟩
  have hloop := Triple.forRange_const (w := c.w) (p := p)
    (P := fun st => st.mem = c.mem0 ∧ FilterFixedRegs c st)
    (r := 14) (lo := .const 0) (hi := .reg 3) (body := dsWalkPtrsBodyStmt)
    (Inv := WPInv c) (35 * c.j + 40) 0 c.candLen (Nat.zero_le _) (by omega)
    (fun _ => by have := c.hcand_w; omega)
    (fun st ⟨hm, hf⟩ => ⟨Expr.eval_const (by omega),
      hf.agree (fun r hr _ => by simp [show r ≠ 14 by omega]), by simp,
      fun k _ hk => absurd hk (Nat.not_lt_zero _), fun addr _ => by simp [hm]⟩)
    (fun i st _ _ h => h.2.1)
    (fun i st _ _ h => Expr.eval_reg_of_eq h.1.2.2.2.1)
    (fun i _ hi => dsWalkPtrs_step_triple c hi)
  refine runs_seq_triple_le hloop ⟨hm1, hf1⟩ ?_
  intro st2 hI
  refine runs_ret_le (v := 0) (Expr.eval_const (by omega)) ?_ ?_
  · refine ⟨fun k hk => ?_, fun addr ha => hI.2.2.2 addr ha⟩
    have he_mem : c.cand[k] ∈ c.cand := List.getElem_mem hk
    obtain ⟨he_G, _⟩ := c.hcand_sub _ he_mem
    have hm1_lt := findEmbLevel_lt c.inDom_mid c.h1j c.hjL c.cand[k]
    have hm1_in := findEmbLevel_mem c.inDom_mid c.h1j c.hjL (c.hinDom0 _ he_G)
    obtain ⟨hWat, hfoot, hbd⟩ := c.hpi_at ⟨_, hm1_lt.2⟩ hm1_lt.1 _ hm1_in
    have hpi_eq : c.piLt_mid c.cand[k] =
        c.Pi_level ⟨findEmbLevel c.inDom_mid c.j c.cand[k], hm1_lt.2⟩ c.cand[k] := by
      rw [c.hpiLt_eq]
      dsimp only [piLtFrom]
      split_ifs with h
      · rfl
      · exact absurd hm1_lt.2 h
    refine ⟨hI.2.2.1 k hk (by omega), ?_, ?_, ?_⟩
    · rw [hpi_eq]
      refine hWat.of_agree fun addr h1 h2 => hI.2.2.2 addr (c.hfoot_out addr (hfoot addr h1 ?_))
      rw [mWalkEncode_length]; omega
    · rw [hpi_eq]; exact hfoot
    · rw [hpi_eq]; exact hbd
  · dsimp only [dsWalkPtrsContract, Expr.size]
    rw [hlen, Nat.sub_zero]
    have : c.candLen * (35 * c.j + 40 + 1 + 8) ≤ c.candLen * (35 * c.j + 60) :=
      Nat.mul_le_mul_left _ (by omega)
    omega

end

end MinCostFlow.DynSpanner.Program
