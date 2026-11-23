module

public import MinCostFlow.DynSpanner.Program.DynSpannerReembedAllInv
import MinCostFlow.DynSpanner.Program.DynGraphOps
import WordRAM.Tactic

/-!
# Re-embedding all affected edges: one loop step

`dsReembedAll_step_triple` proves one iteration of the loop of `dsReembedAllStmt`: from
`RAInv c i`, the body handles the edge `e = es[i]` and reaches `RAInv c (i + 1)`. It reads `e`
and the pointers to its two walks, reads the ends of `e` in `G`, calls `dsReembedEdgeStmt` with
output at the heap pointer `reembHeapAt … i` and scratch right after the output area, and stores
the pointer to the new walk.

The re-embedding writes only inside the heap area beyond `reembHeapAt … i`, so the walks of the
earlier edges stay. The store writes only the table entry of `e`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

public section

/-- One iteration of the loop of `dsReembedAllStmt`, with cost
`800 · (|embLt e| + |embMid e|) + 1090`. -/
theorem dsReembedAll_step_triple (c : RACtx) {p : Program} {bOps bRe bEmb : ℕ}
    (hpOps : p.HasAt bOps dgOpsProcs) (hpRe : p.HasAt bRe (reembedProcs bEmb))
    (hpEmb : p.HasAt bEmb (embOpsProcs bOps))
    {i : ℕ} (hi : i < c.es.length) :
    Triple c.w p (RAInv c i) (dsReembedAllBodyStmt bOps bRe)
      (fun o st₁ => match o with
        | .returned _ => False
        | .normal =>
          RAInv c (i + 1) { st₁ with regs := Function.update st₁.regs 8 (i + 1) } ∧
            st₁.regs 8 = i)
      (fun _ => 800 * ((c.embLt c.es[i]).length + (c.embMid c.es[i]).length) + 1090) := by
  intro st ω hInv
  have hInv' := hInv
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, hT, hfr⟩ := hInv'
  have hw16 := c.hw16
  have hgB := c.hgB
  have hsB := c.hsB
  have hesB := c.hesB
  have hwpB := c.hwpB
  have hmpB := c.hmpB
  have htB := c.htB
  have hhB := c.hhB
  have heCap := c.eCap_le
  have hvCap := c.vCap_le
  have hhi := reembHeapAt_add_le c.G c.embLt c.embMid c.S c.es c.heap i hi
  have hh0 := heap_le_reembHeapAt c.G c.embLt c.embMid c.S c.es c.heap i
  have he_mem : c.es[i] ∈ c.es := List.getElem_mem hi
  have heG : c.es[i] ∈ c.G.E := c.hesG _ he_mem
  have he_cap : c.es[i] < c.eCap := c.es_lt hi
  have he_w : c.es[i] < 2 ^ c.w := by omega
  obtain ⟨hWat0, hwpw, dWH, dWT, hMat0, hmpw, dMH, dMT⟩ := c.hwalk i hi
  have hPw := c.hPw _ he_mem
  have hMe := c.hMe _ he_mem
  -- Reads of the inputs.
  have hes_rd : st.mem (c.esPtr + i) = c.es[i] := by
    rw [hInv.read (c.dHE.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))
      (c.dTE.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))]
    exact c.hes i hi
  have hwp_rd : st.mem (c.wpPtr + i) = c.mem0 (c.wpPtr + i) :=
    hInv.read (c.dHW.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))
      (c.dTW.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))
  have hmp_rd : st.mem (c.mpPtr + i) = c.mem0 (c.mpPtr + i) :=
    hInv.read (c.dHM.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))
      (c.dTM.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))
  have hG_st : DynGraphAt st.mem c.gPtr c.vCap c.eCap c.G :=
    dynGraphAt_of_agree c.hG fun addr h1 h2 =>
      hInv.read (c.dHG.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ h1 h2)
        (c.dTG.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ h1 h2)
  have hW_st : MWalkAt st.mem (c.mem0 (c.wpPtr + i)) (c.embLt c.es[i]) :=
    hWat0.of_agree fun addr h1 h2 =>
      hInv.read (dWH.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ h1 (by omega))
        (dWT.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ h1 (by omega))
  have hM_st : MWalkAt st.mem (c.mem0 (c.mpPtr + i)) (c.embMid c.es[i]) :=
    hMat0.of_agree fun addr h1 h2 =>
      hInv.read (dMH.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ h1 (by omega))
        (dMT.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ h1 (by omega))
  have hS_st : ∀ v < c.vCap, st.mem (c.sBitPtr + v) = if v ∈ c.S then 1 else 0 := fun v hv =>
    (hInv.read (c.dHS.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))
      (c.dTS.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))).trans
      (c.hsBit v hv)
  have hn_rd : st.mem (c.mem0 (c.wpPtr + i)) = (c.embLt c.es[i]).length := MWalkAt_head hW_st
  have hm_rd : st.mem (c.mem0 (c.mpPtr + i)) = (c.embMid c.es[i]).length := MWalkAt_head hM_st
  dsimp only [dsReembedAllBodyStmt]
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := c.es[i])
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r2) (Expr.eval_reg_of_eq r8)
      (by omega)) hes_rd) ?_
  refine runs_seq_assign_le (v := c.mem0 (c.wpPtr + i))
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r4]))
      (Expr.eval_reg_of_eq (by simp [r8])) (by omega)) hwp_rd) ?_
  refine runs_seq_assign_le (v := c.mem0 (c.mpPtr + i))
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r5]))
      (Expr.eval_reg_of_eq (by simp [r8])) (by omega)) hmp_rd) ?_
  -- The ends of `e`.
  refine runs_seq_call_le (dgGetTail_meetsContract (w := c.w) (vCap := c.vCap) (eCap := c.eCap)
      (G := c.G) hpOps) (by eval_expr) (by wram_words)
    ⟨c.gPtr, c.es[i], rfl, hw16, hgB, heG, hG_st⟩ ?_
  rintro vt mem₁ pos₁ ⟨_, _, hargs₁, hmem₁, hvt⟩
  simp only [List.cons.injEq, and_true] at hargs₁
  obtain ⟨rfl, rfl⟩ := hargs₁
  subst hmem₁
  refine runs_seq_call_le (dgGetHead_meetsContract (w := c.w) (vCap := c.vCap) (eCap := c.eCap)
      (G := c.G) hpOps) (by eval_expr) (by wram_words)
    ⟨c.gPtr, c.es[i], rfl, hw16, hgB, heG, hG_st⟩ ?_
  rintro vh mem₂ pos₂ ⟨_, _, hargs₂, hmem₂, hvh⟩
  simp only [List.cons.injEq, and_true] at hargs₂
  obtain ⟨rfl, rfl⟩ := hargs₂
  subst hmem₂
  refine runs_seq_assign_le (v := (c.embLt c.es[i]).length)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp)) hn_rd) ?_
  refine runs_seq_assign_le (v := (c.embMid c.es[i]).length)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp)) hm_rd) ?_
  wram_step
  -- The re-embedding of `e`, output at the heap pointer.
  subst hvt hvh
  have ht_w : c.G.tail c.es[i] < 2 ^ c.w := by have := c.hVc _ (c.hGv _ heG).1; omega
  have hh_w : c.G.head c.es[i] < 2 ^ c.w := by have := c.hVc _ (c.hGv _ heG).2; omega
  have hRlen := reembedWalk_length_le c.G c.embLt c.embMid c.S c.es[i]
  refine runs_seq_call_le (dsReembedEdge_meetsContract (w := c.w) (vCap := c.vCap)
      (eCap := c.eCap) (H := c.G) (a := c.G.tail c.es[i]) (b := c.G.head c.es[i])
      (P := c.embLt c.es[i]) (M := c.embMid c.es[i]) (S := c.S) hpRe hpEmb hpOps)
    (by eval_expr) (by wram_words)
    ⟨c.gPtr, c.mem0 (c.wpPtr + i), c.mem0 (c.mpPtr + i), c.sBitPtr, _, _, rfl, hw16, hgB, hwpw,
      hmpw, hsB, by omega, by omega, Or.inr (by omega),
      c.dHG.sub_left (by omega) (by omega), dWH.sub_left (by omega) (by omega),
      dMH.sub_left (by omega) (by omega), c.dHS.sub_left (by omega) (by omega),
      dMH.sub_left (by omega) (by omega),
      hG_st, c.hGv, c.hVc, c.hEc, (c.hGv _ heG).1, (c.hGv _ heG).2, hPw, hW_st, hM_st, hMe,
      hS_st⟩ ?_
  rintro r₁₇ mem₃ pos₃ ⟨_, _, _, _, _, _, hargs₃, hWat, hret, hfr₃⟩
  simp only [List.cons.injEq, and_true] at hargs₃
  obtain ⟨rfl, -, -, -, -, rfl, rfl, rfl⟩ := hargs₃
  -- Store the walk pointer and move the heap pointer.
  wram_step
  wram_step
  · -- The invariant after edge `i`.
    rw [reembedEdgeWalk_eq_reembedWalk] at hret hWat hfr₃
    have h7 : r₁₇ = reembHeapAt c.G c.embLt c.embMid c.S c.es c.heap (i + 1) := by
      rw [hret, reembHeapAt_succ c.G c.embLt c.embMid c.S c.es c.heap i hi]
      simp only [reembOutLen]
    have hT_heap : ∀ k (hk : k < c.es.length),
        c.piTab + c.es[k] < c.heap ∨
          c.heap + reembHeapNeed c.embLt c.embMid c.es ≤ c.piTab + c.es[k] :=
      fun k hk => c.dHT.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega)
        (by have := c.es_lt hk; omega)
    have hsucc := reembHeapAt_succ c.G c.embLt c.embMid c.S c.es c.heap i hi
    simp only [r6, r7]
    refine ⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4], by simp [r5],
      by simp [r6], by simp [h7], by simp, ?_, ?_⟩, by simp [r8]⟩
    · intro k hk hki
      by_cases hk_eq : k = i
      · subst hk_eq
        simp only [Function.update_apply, ite_true]
        refine ⟨by omega, by simp only [reembOutLen] at hsucc ⊢; omega,
          hWat.of_agree fun addr h1 h2 => ?_⟩
        have hheap : c.heap ≤ addr ∧ addr < c.heap + reembHeapNeed c.embLt c.embMid c.es := by
          simp only [reembOutLen] at hsucc; omega
        have hTa := c.dHT.symm.addr_sub (Nat.le_refl _) (Nat.le_refl _) addr hheap.1 hheap.2
        simp only [Function.update_apply]
        rw [ite_eq_right (by omega)]
      · have hk_lt : k < i := by omega
        have hne : c.es[k] ≠ c.es[i] := fun h => hk_eq ((List.Nodup.getElem_inj_iff c.hnd).mp h)
        obtain ⟨hk1, hk2, hk3⟩ := hT k hk hk_lt
        have hptr : (Function.update mem₃ (c.piTab + c.es[i])
            (reembHeapAt c.G c.embLt c.embMid c.S c.es c.heap i)) (c.piTab + c.es[k]) =
            st.mem (c.piTab + c.es[k]) := by
          rw [Function.update_of_ne (by omega)]
          have := hT_heap k hk
          exact hfr₃ _ (by omega) (by omega)
        have hA : st.mem (c.piTab + c.es[k]) +
            (2 * (reembedWalk c.G c.G c.embLt c.embMid c.S c.es[k]).length + 1) ≤
            reembHeapAt c.G c.embLt c.embMid c.S c.es c.heap i := by
          simpa only [reembOutLen] using hk2
        have hsucc' : reembHeapAt c.G c.embLt c.embMid c.S c.es c.heap i ≤
            reembHeapAt c.G c.embLt c.embMid c.S c.es c.heap (i + 1) := by omega
        simp only [hptr]
        refine ⟨hk1, by omega, hk3.of_agree fun addr h1 h2 => ?_⟩
        try simp only [hptr] at h1 h2
        have hheap : c.heap ≤ addr ∧ addr < c.heap + reembHeapNeed c.embLt c.embMid c.es := by
          omega
        have hTa := c.dHT.symm.addr_sub (Nat.le_refl _) (Nat.le_refl _) addr hheap.1 hheap.2
        simp only [Function.update_apply]
        rw [ite_eq_right (by omega)]
        exact hfr₃ addr (Or.inl (by omega)) (Or.inl (by omega))
    · intro addr hH hTk
      have hne := hTk i hi (Nat.lt_succ_self i)
      simp only [Function.update_apply]
      rw [ite_eq_right hne, hfr₃ addr (by omega) (by omega)]
      exact hfr addr hH fun k hk hki => hTk k hk (by omega)
  · simp only [dgGetTailContract, dgGetHeadContract, dsReembedEdgeContract, Expr.size_const,
      Expr.size_reg, Expr.size_load, Expr.size_bin, argsSize_cons, argsSize_nil]
    omega

end

end MinCostFlow.DynSpanner.Program
