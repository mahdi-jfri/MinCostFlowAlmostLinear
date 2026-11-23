module

public import MinCostFlow.DynSpanner.Program.DynSpannerCompAllDefs
public import MinCostFlow.DynSpanner.Program.DynSpannerComp
import WordRAM.Tactic

/-!
# Composing the walks of all affected edges: one loop step

`dsCompAll_step_triple` proves one iteration of the loop of `dsCompAllStmt`: it reads the edge
`e = es[i]` and the pointer to `outEmb e`, calls `dsCompEdgeStmt` with output at
`compHeapAt … i`, and stores this address at `mpPtr + i`. The call writes only its output area,
which lies in the heap after the outputs of the earlier edges. The store writes only the table
entry of position `i`, outside the heap.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

public section

/-- One iteration of the loop of `dsCompAllStmt`. -/
theorem dsCompAll_step_triple (c : CACtx) {p : Program} {bC bOps bEmb : ℕ}
    (hpC : p.HasAt bC (compProcs bEmb)) (hpEmb : p.HasAt bEmb (embOpsProcs bOps))
    {i : ℕ} (hi : i < c.es.length) :
    Triple c.w p (CAInv c i) (dsCompAllBodyStmt bC)
      (normalPost fun st₁ =>
        CAInv c (i + 1) { st₁ with regs := Function.update st₁.regs 6 (i + 1) } ∧
          st₁.regs 6 = i)
      (fun _ => 70 * ((c.outEmb c.es[i]).flatMap (compPiece c.T)).length +
        120 * (c.outEmb c.es[i]).length + 70) := by
  intro st ω hI
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, hT, hfr⟩ := hI
  have hw16 := c.hw16
  have hqB := c.hqB
  have htB := c.htB
  have hesB := c.hesB
  have hmpB := c.hmpB
  have hhB := c.hhB
  obtain ⟨he_cap, hQat0, hQb, dQH, dQM, hxs⟩ := c.hk i hi
  have hsucc := compHeapAt_succ c.T c.outEmb c.es c.heap i hi
  have hle := compHeapAt_le_need c.T c.outEmb c.es c.heap (i + 1)
  have hh0 : c.heap ≤ compHeapAt c.T c.outEmb c.es c.heap i := by
    simp only [compHeapAt]; omega
  simp only [compOutLen] at hsucc
  -- Reads of the inputs.
  have hes_rd : st.mem (c.esPtr + i) = c.es[i] := by
    rw [hfr _ (c.dHE.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))
      (c.dME.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))]
    exact c.hes i hi
  have hq_rd : st.mem (c.qTab + c.es[i]) = c.mem0 (c.qTab + c.es[i]) :=
    hfr _ (c.dHQ.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))
      (c.dMQ.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))
  have hQst : MWalkAt st.mem (c.mem0 (c.qTab + c.es[i])) (c.outEmb c.es[i]) :=
    hQat0.of_agree fun addr h1 h2 =>
      hfr addr (dQH.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ h1 (by omega))
        (dQM.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ h1 (by omega))
  have hx' : ∀ x ∈ c.outEmb c.es[i], x.1 < c.eCap ∧
      MWalkAt st.mem (st.mem (c.tab + x.1)) (c.T x.1) ∧
      st.mem (c.tab + x.1) + (2 * (c.T x.1).length + 1) < 2 ^ c.w ∧
      IvlDisj (compHeapAt c.T c.outEmb c.es c.heap i)
        (2 * ((c.outEmb c.es[i]).flatMap (compPiece c.T)).length + 1)
        (st.mem (c.tab + x.1)) (2 * (c.T x.1).length + 1) ∧
      ∀ y ∈ c.T x.1, y.1 < c.eCap := by
    intro x hx
    obtain ⟨hxE, hTat0, hTb, dTH, dTM, hTe⟩ := hxs x hx
    have htab : st.mem (c.tab + x.1) = c.mem0 (c.tab + x.1) :=
      hfr _ (c.dHT.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))
        (c.dMT.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))
    rw [htab]
    refine ⟨hxE, hTat0.of_agree fun addr h1 h2 => ?_, hTb,
      dTH.sub_left hh0 (by omega), hTe⟩
    exact hfr addr (dTH.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ h1 (by omega))
      (dTM.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ h1 (by omega))
  dsimp only [dsCompAllBodyStmt]
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := c.es[i])
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r2) (Expr.eval_reg_of_eq r6)
      (by omega)) hes_rd) ?_
  refine runs_seq_assign_le (v := c.mem0 (c.qTab + c.es[i]))
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r0]))
      (Expr.eval_reg_of_eq (by simp)) (by omega)) hq_rd) ?_
  refine runs_seq_call_le (dsCompEdge_meetsContract (w := c.w) (eCap := c.eCap) (T := c.T)
      (Q := c.outEmb c.es[i]) hpC hpEmb) (by eval_expr)
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> omega)
    ⟨_, _, _, rfl, hw16, hQb, htB, by omega, dQH.sub_left hh0 (by omega),
      c.dHT.sub_left hh0 (by omega), hQst, hx'⟩ ?_
  rintro v mem₁ pos₁ ⟨_, _, _, hargs, hW, hret, hfr₁⟩
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl⟩ := hargs
  refine runs_seq_store_le (x := c.mpPtr + i) (v := compHeapAt c.T c.outEmb c.es c.heap i)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r4])) (Expr.eval_reg_of_eq (by simp [r6]))
      (by omega)) (Expr.eval_reg_of_eq (by simp [r5])) ?_
  refine runs_assign_le (v := v) (Expr.eval_reg_of_eq (by simp)) ?_ ?_
  · have hM_heap : ∀ k, k < c.es.length → c.mpPtr + k < c.heap ∨
        c.heap + compHeapNeed c.T c.outEmb c.es ≤ c.mpPtr + k := fun k hk =>
      c.dHM.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega)
    have hMi := hM_heap i hi
    refine ⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4],
      by simp [hret, hsucc], by simp, ?_, ?_⟩, by simp [r6]⟩
    · intro k hk hki
      by_cases hk_eq : k = i
      · subst hk_eq
        refine ⟨by simp, ?_⟩
        rw [comp_eq_flatMap]
        refine hW.of_agree fun addr h1 h2 => ?_
        show Function.update mem₁ _ _ addr = mem₁ addr
        exact Function.update_of_ne (by omega) _ _
      · have hk_lt : k < i := by omega
        obtain ⟨hk1, hk2⟩ := hT k hk hk_lt
        have hsk := compHeapAt_succ c.T c.outEmb c.es c.heap k hk
        have hmk := compHeapAt_mono c.T c.outEmb c.es c.heap (show k + 1 ≤ i by omega)
        have hhk : c.heap ≤ compHeapAt c.T c.outEmb c.es c.heap k := by
          simp only [compHeapAt]; omega
        simp only [compOutLen] at hsk
        have hMk := hM_heap k hk
        refine ⟨?_, hk2.of_agree fun addr h1 h2 => ?_⟩
        · show Function.update mem₁ _ _ (c.mpPtr + k) = _
          rw [Function.update_of_ne (by omega), hfr₁ _ (by omega)]
          exact hk1
        · show Function.update mem₁ _ _ addr = st.mem addr
          rw [comp_eq_flatMap] at h2
          rw [Function.update_of_ne (by omega), hfr₁ _ (Or.inl (by omega))]
    · intro addr hH hM
      show Function.update mem₁ _ _ addr = _
      rw [Function.update_of_ne (by omega), hfr₁ _ (by omega)]
      exact hfr addr hH hM
  · simp only [dsCompEdgeContract, Expr.size_const, Expr.size_reg, Expr.size_load,
      Expr.size_bin, argsSize_cons, argsSize_nil]
    omega

end

end MinCostFlow.DynSpanner.Program
