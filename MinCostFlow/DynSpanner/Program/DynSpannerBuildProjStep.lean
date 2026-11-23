module

public import MinCostFlow.DynSpanner.Program.DynSpannerBuildProjInv
public import MinCostFlow.DynSpanner.Program.DynSpannerProj
import MinCostFlow.DynSpanner.Program.DynGraphInsert
import MinCostFlow.DynSpanner.Program.DynGraphBatch
import MinCostFlow.DynSpanner.Walks
import WordRAM.Tactic

/-!
# Building the projected graph `J`: one loop step

`dsBuildProj_step_triple` proves one iteration of the loop of `dsBuildProjStmt`: from
`BPInv c i`, the body handles the edge `e = es[i]` and reaches `BPInv c (i + 1)`. It reads `e` and
the pointer to its walk, reads the ends of `e` in `G`, calls `dsProjEdgeStmt` with output at the
heap pointer `projHeapAt … i` and scratch right after the output, adds the two projected ends to
`J`, inserts `e`, and stores the pointer to `projWalk e`.

Each write is checked against the invariant: the projection writes only inside the heap area
beyond `projHeapAt … i` (so the earlier walks stay), the graph operations write only inside `J`,
and the store writes only the table entry of `e`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

public section

/-- One iteration of the loop of `dsBuildProjStmt`, with cost `800 · |embLt e| + 1990`. -/
theorem dsBuildProj_step_triple (c : BPCtx) {p : Program} {bOps bEdge bProj bEmb : ℕ}
    (hpOps : p.HasAt bOps dgOpsProcs) (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpProj : p.HasAt bProj (projProcs bEmb)) (hpEmb : p.HasAt bEmb (embOpsProcs bOps))
    {i : ℕ} (hi : i < c.es.length) :
    Triple c.w p (BPInv c i) (dsBuildProjBodyStmt bOps bEdge bProj)
      (fun o st₁ => match o with
        | .returned _ => False
        | .normal =>
          BPInv c (i + 1) { st₁ with regs := Function.update st₁.regs 8 (i + 1) } ∧
            st₁.regs 8 = i)
      (fun _ => 800 * (c.embLt c.es[i]).length + 1990) := by
  intro st ω hInv
  have hInv' := hInv
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, hJ, hT, hfr⟩ := hInv'
  have hw16 := c.hw16
  have hgB := c.hgB
  have hjB := c.hjB
  have hsB := c.hsB
  have hesB := c.hesB
  have hwpB := c.hwpB
  have htB := c.htB
  have hhB := c.hhB
  have heCap := c.eCap_le
  have hvCap := c.vCap_le
  have hhi := projHeapAt_add_le c.G c.embLt c.S c.es c.heap i hi
  have hh0 := heap_le_projHeapAt c.G c.embLt c.S c.es c.heap i
  have he_mem : c.es[i] ∈ c.es := List.getElem_mem hi
  have heG : c.es[i] ∈ c.G.E := c.hesG _ he_mem
  have he_cap : c.es[i] < c.eCap := c.es_lt hi
  have he_w : c.es[i] < 2 ^ c.w := by omega
  obtain ⟨hWat0, hwpw, dWH, dWJ, dWT⟩ := c.hwalk i hi
  have hPw := c.hPw _ he_mem
  -- Reads of the inputs.
  have hes_rd : st.mem (c.esPtr + i) = c.es[i] := by
    rw [hInv.read (c.dHE.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))
      (c.dJE.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))
      (c.dTE.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))]
    exact c.hes i hi
  have hwp_rd : st.mem (c.wpPtr + i) = c.mem0 (c.wpPtr + i) :=
    hInv.read (c.dHW.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))
      (c.dJW.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))
      (c.dTW.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))
  have hG_st : DynGraphAt st.mem c.gPtr c.vCap c.eCap c.G :=
    dynGraphAt_of_agree c.hG fun addr h1 h2 =>
      hInv.read (c.dHG.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ h1 h2)
        (c.dJG.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ h1 h2)
        (c.dTG.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ h1 h2)
  have hW_st : MWalkAt st.mem (c.mem0 (c.wpPtr + i)) (c.embLt c.es[i]) :=
    hWat0.of_agree fun addr h1 h2 =>
      hInv.read (dWH.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ h1 (by omega))
        (dWJ.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ h1 (by omega))
        (dWT.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ h1 (by omega))
  have hS_st : ∀ v < c.vCap, st.mem (c.sBitPtr + v) = if v ∈ c.S then 1 else 0 := fun v hv =>
    (hInv.read (c.dHS.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))
      (c.dJS.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))
      (c.dTS.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))).trans
      (c.hsBit v hv)
  have hn_rd : st.mem (c.mem0 (c.wpPtr + i)) = (c.embLt c.es[i]).length := MWalkAt_head hW_st
  dsimp only [dsBuildProjBodyStmt]
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := c.es[i])
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r3) (Expr.eval_reg_of_eq r8)
      (by omega)) hes_rd) ?_
  refine runs_seq_assign_le (v := c.mem0 (c.wpPtr + i))
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r5]))
      (Expr.eval_reg_of_eq (by simp [r8])) (by omega)) hwp_rd) ?_
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
  wram_step
  -- The projection of `e`, output at the heap pointer.
  subst hvt hvh
  have ht_w : c.G.tail c.es[i] < 2 ^ c.w := by have := c.hVc _ (c.hGv _ heG).1; omega
  have hh_w : c.G.head c.es[i] < 2 ^ c.w := by have := c.hVc _ (c.hGv _ heG).2; omega
  have hWlen : (projEdgeWalk c.G c.es[i] (c.G.tail c.es[i]) (c.G.head c.es[i])
      (c.embLt c.es[i]) c.S).length ≤ 2 * (c.embLt c.es[i]).length + 1 := by
    rw [projEdgeWalk_eq_projWalk]; exact projWalk_length_le _ _ _ _
  refine runs_seq_call_le (dsProjEdge_meetsContract (w := c.w) (vCap := c.vCap)
      (eCap := c.eCap) (H := c.G) (e := c.es[i]) (a := c.G.tail c.es[i])
      (b := c.G.head c.es[i]) (P := c.embLt c.es[i]) (S := c.S) hpProj hpEmb hpOps)
    (by eval_expr) (by wram_words)
    ⟨c.gPtr, c.mem0 (c.wpPtr + i), c.sBitPtr, _, _, rfl, hw16, hgB, hwpw, hsB, by omega,
      by omega, Or.inr (by omega),
      c.dHG.sub_left (by omega) (by omega), dWH.sub_left (by omega) (by omega),
      c.dHS.sub_left (by omega) (by omega), c.dHG.sub_left (by omega) (by omega),
      dWH.sub_left (by omega) (by omega), c.dHS.sub_left (by omega) (by omega),
      hG_st, c.hGv, c.hVc, c.hEc, (c.hGv _ heG).1, (c.hGv _ heG).2, hPw, hW_st, hS_st⟩ ?_
  rintro r₁₅ mem₃ pos₃ ⟨_, _, _, _, _, hargs₃, hAend, hBend, hWat, hret, hfr₃⟩
  simp only [List.cons.injEq, and_true] at hargs₃
  obtain ⟨rfl, -, -, -, rfl, rfl, rfl, rfl⟩ := hargs₃
  have hJ_heap : ∀ addr, c.jPtr ≤ addr → addr < c.jPtr + dynGraphSize c.vCap c.eCap →
      addr < c.heap ∨ c.heap + projHeapNeed c.embLt c.es ≤ addr :=
    fun addr h1 h2 => c.dHJ.addr_sub (Nat.le_refl _) (Nat.le_refl _) addr h1 h2
  have hJ₃ : DynGraphAt mem₃ c.jPtr c.vCap c.eCap
      (buildProjGraph c.G c.G c.embLt c.S (c.es.take i).toFinset) :=
    dynGraphAt_of_agree hJ fun addr h1 h2 => by
      have := hJ_heap addr h1 h2
      exact hfr₃ addr (by omega) (by omega)
  have hA_V : (proj c.G c.G c.embLt c.S c.es[i]).1 ∈ c.G.V :=
    isWalk_end_mem_V c.hGv (c.hGv _ heG).1 hPw.1
  have hB_V : (proj c.G c.G c.embLt c.S c.es[i]).2 ∈ c.G.V :=
    isWalk_end_mem_V c.hGv (c.hGv _ heG).2 hPw.2.1
  have hA_cap := c.hVc _ hA_V
  have hB_cap := c.hVc _ hB_V
  refine runs_seq_assign_le (v := (proj c.G c.G c.embLt c.S c.es[i]).1)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [r7])) hAend) ?_
  refine runs_seq_assign_le (v := (proj c.G c.G c.embLt c.S c.es[i]).2)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r7]))
      (Expr.eval_const (by omega)) (by omega)) hBend) ?_
  -- Add the two ends and the edge to `J`.
  obtain ⟨hnot, hVeq, hEeq, hEnds⟩ := buildProjGraph_take_succ c.G c.G c.embLt c.S c.es i hi c.hnd
  refine runs_seq_call_le (dgAddVertex_meetsContract (w := c.w) (vCap := c.vCap)
      (eCap := c.eCap) (G := buildProjGraph c.G c.G c.embLt c.S (c.es.take i).toFinset) hpOps)
    (by eval_expr) (by wram_words) ⟨c.jPtr, _, rfl, hw16, hjB, hA_cap, hJ₃⟩ ?_
  rintro _ mem₄ pos₄ ⟨_, _, hargs₄, -, hJ₄, hfr₄⟩
  simp only [List.cons.injEq, and_true] at hargs₄
  obtain ⟨rfl, rfl⟩ := hargs₄
  refine runs_seq_call_le (dgAddVertex_meetsContract (w := c.w) (vCap := c.vCap)
      (eCap := c.eCap) hpOps) (by eval_expr) (by wram_words)
    ⟨c.jPtr, _, rfl, hw16, hjB, hB_cap, hJ₄⟩ ?_
  rintro _ mem₅ pos₅ ⟨_, _, hargs₅, -, hJ₅, hfr₅⟩
  simp only [List.cons.injEq, and_true] at hargs₅
  obtain ⟨rfl, rfl⟩ := hargs₅
  refine runs_seq_call_le (dgInsertEdge_meetsContract (w := c.w) (vCap := c.vCap)
      (eCap := c.eCap) hpEdge hpOps) (by eval_expr) (by wram_words)
    ⟨c.jPtr, c.es[i], _, _, rfl, hw16, hjB, by simp, by simp, hJ₅⟩ ?_
  rintro _ mem₆ pos₆ ⟨_, _, _, _, hargs₆, -, hJ₆, hfr₆⟩
  simp only [List.cons.injEq, and_true] at hargs₆
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hargs₆
  rw [ite_eq_left ⟨he_cap, hnot⟩] at hJ₆
  -- Store the walk pointer and move the heap pointer.
  wram_step
  wram_step
  · -- The invariant after edge `i`.
    rw [projEdgeWalk_eq_projWalk] at hret hWat hWlen hfr₃
    have h7 : r₁₅ = projHeapAt c.G c.embLt c.S c.es c.heap (i + 1) := by
      rw [hret, projHeapAt_succ c.G c.embLt c.S c.es c.heap i hi]
      simp only [projOutLen]; omega
    have hT_heap : ∀ k (hk : k < c.es.length),
        c.embTab + c.es[k] < c.heap ∨ c.heap + projHeapNeed c.embLt c.es ≤ c.embTab + c.es[k] :=
      fun k hk => c.dHT.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega)
        (by have := c.es_lt hk; omega)
    have hT_J : ∀ k (hk : k < c.es.length),
        c.embTab + c.es[k] < c.jPtr ∨ c.jPtr + dynGraphSize c.vCap c.eCap ≤ c.embTab + c.es[k] :=
      fun k hk => c.dJT.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega)
        (by have := c.es_lt hk; omega)
    -- Memory outside `J` and the new table entry: as after the projection.
    have hmid : ∀ addr, (addr < c.jPtr ∨ c.jPtr + dynGraphSize c.vCap c.eCap ≤ addr) →
        mem₆ addr = mem₃ addr := fun addr h =>
      (hfr₆ addr h).trans ((hfr₅ addr h).trans (hfr₄ addr h))
    simp only [r6, r7]
    refine ⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4], by simp [r5],
      by simp [r6], by simp [h7], by simp, ?_, ?_, ?_⟩, by simp [r8]⟩
    · refine DynGraphAt.congr_ends hVeq hEeq hEnds (dynGraphAt_of_agree hJ₆ fun addr h1 h2 => ?_)
      have := c.dJT.symm.addr_sub (Nat.le_refl _) (Nat.le_refl _) addr h1 h2
      simp only [Function.update_apply]
      rw [ite_eq_right (by omega)]
    · intro k hk hki
      by_cases hk_eq : k = i
      · subst hk_eq
        simp only [Function.update_apply, ite_true]
        refine ⟨by omega, by omega, hWat.of_agree fun addr h1 h2 => ?_⟩
        have hheap : c.heap ≤ addr ∧ addr < c.heap + projHeapNeed c.embLt c.es := by omega
        have hJa := c.dHJ.symm.addr_sub (Nat.le_refl _) (Nat.le_refl _) addr hheap.1 hheap.2
        have hTa := c.dHT.symm.addr_sub (Nat.le_refl _) (Nat.le_refl _) addr hheap.1 hheap.2
        simp only [Function.update_apply]
        rw [ite_eq_right (by omega)]
        exact hmid addr (by omega)
      · have hk_lt : k < i := by omega
        have hne : c.es[k] ≠ c.es[i] := fun h => hk_eq ((List.Nodup.getElem_inj_iff c.hnd).mp h)
        obtain ⟨hk1, hk2, hk3⟩ := hT k hk hk_lt
        have hptr : (Function.update mem₆ (c.embTab + c.es[i])
            (projHeapAt c.G c.embLt c.S c.es c.heap i + 2)) (c.embTab + c.es[k]) =
            st.mem (c.embTab + c.es[k]) := by
          rw [Function.update_of_ne (by omega), hmid _ (hT_J k hk)]
          have := hT_heap k hk
          exact hfr₃ _ (by omega) (by omega)
        have hmono := projHeapAt_mono c.G c.embLt c.S c.es c.heap i hi
        simp only [hptr]
        refine ⟨hk1, by omega, hk3.of_agree fun addr h1 h2 => ?_⟩
        have hheap : c.heap ≤ addr ∧ addr < c.heap + projHeapNeed c.embLt c.es := by omega
        have hJa := c.dHJ.symm.addr_sub (Nat.le_refl _) (Nat.le_refl _) addr hheap.1 hheap.2
        have hTa := c.dHT.symm.addr_sub (Nat.le_refl _) (Nat.le_refl _) addr hheap.1 hheap.2
        simp only [Function.update_apply]
        rw [ite_eq_right (by omega), hmid addr (by omega)]
        exact hfr₃ addr (by omega) (by omega)
    · intro addr hH hJr hTk
      have hne := hTk i hi (Nat.lt_succ_self i)
      simp only [Function.update_apply]
      rw [ite_eq_right hne, hmid addr hJr, hfr₃ addr (by omega) (by omega)]
      exact hfr addr hH hJr fun k hk hki => hTk k hk (by omega)
  · simp only [dgGetTailContract, dgGetHeadContract, dsProjEdgeContract, dgAddVertexContract,
      dgInsertEdgeContract, Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin,
      argsSize_cons, argsSize_nil]
    omega

end

end MinCostFlow.DynSpanner.Program
