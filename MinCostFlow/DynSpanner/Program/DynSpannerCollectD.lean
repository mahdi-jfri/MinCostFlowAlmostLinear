module

public import MinCostFlow.DynSpanner.Program.DynSpannerCollectDInner
import WordRAM.Tactic

/-!
# The set `D` of a step: the contract

`dsCollectD_outer_triple` proves one iteration of the outer loop of `dsCollectDStmt`: it reads
the edge `e = es[i]`, the pointer to `T e` and its length, and runs the inner loop
(`dsCollectD_inner_triple`). `dsCollectD_meetsContract` proves the contract: the output is
`dList T es`, whose elements are the edges of the walks `T e` for `e ∈ es` (`mem_dList`), each
once (`dList_nodup`), and the cost is `O(Σ |T e| + |es| + 1)`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

private lemma sum_range_getD (es : List ℕ) (g : ℕ → ℕ) :
    ((List.range es.length).map fun i => g (es.getD i 0)).sum = (es.map g).sum := by
  congr 1
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem]

private lemma sum_outer (T : Embedding) (es : List ℕ) :
    (es.map fun e => 50 * (T e).length + 40).sum = 50 * dTotal T es + 40 * es.length := by
  induction es with
  | nil => simp [dTotal]
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, dTotal] at ih ⊢
    omega

public section

/-- The invariant of the outer loop after the first `i` edges of `es`. -/
def DOuterInv (c : DCtx) (i : ℕ) (st : State) : Prop :=
  DState c (dList c.T (c.es.take i)) st ∧ st.regs 7 = i

/-- One iteration of the outer loop of `dsCollectDStmt`. -/
theorem dsCollectD_outer_triple (c : DCtx) {p : Program} {i : ℕ} (hi : i < c.es.length) :
    Triple c.w p (DOuterInv c i) dsCollectDOuterStmt
      (normalPost fun st₁ =>
        DOuterInv c (i + 1) { st₁ with regs := Function.update st₁.regs 7 (i + 1) } ∧
          st₁.regs 7 = i)
      (fun _ => 50 * (c.T c.es[i]).length + 40) := by
  intro st ω hI
  obtain ⟨⟨r0, r1, r2, r3, r4, r5, r6, hL, hS, hfr⟩, r7⟩ := hI
  have hw16 := c.hw16
  have hesB := c.hesB
  have htB := c.htB
  obtain ⟨heC, hW, hWb, dSW, dOW, _⟩ := c.hk i hi
  have hes_rd : st.mem (c.esPtr + i) = c.es[i] := by
    rw [hfr _ (c.dSE.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))
      (c.dOE.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))]
    exact c.hes i hi
  have htab_rd : st.mem (c.tab + c.es[i]) = c.mem0 (c.tab + c.es[i]) :=
    hfr _ (c.dST.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))
      (c.dOT.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))
  have hlen_rd : st.mem (c.mem0 (c.tab + c.es[i])) = (c.T c.es[i]).length := by
    rw [hfr _ (dSW.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))
      (dOW.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))]
    exact MWalkAt_head hW
  dsimp only [dsCollectDOuterStmt]
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := c.es[i])
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r0) (Expr.eval_reg_of_eq r7)
      (by omega)) hes_rd) ?_
  refine runs_seq_assign_le (v := c.mem0 (c.tab + c.es[i]))
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r2]))
      (Expr.eval_reg_of_eq (by simp)) (by omega)) htab_rd) ?_
  refine runs_seq_assign_le (v := (c.T c.es[i]).length)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp)) hlen_rd) ?_
  have hloop := Triple.forRange_const (w := c.w) (p := p)
    (P := fun st' => DInnerInv c i hi 0 { st' with regs := Function.update st'.regs 11 0 })
    (r := 11) (lo := .const 0) (hi := .reg 10) (body := dsCollectDInnerStmt)
    (Inv := DInnerInv c i hi) 40 0 (c.T c.es[i]).length (Nat.zero_le _) (by omega)
    (fun _ => by omega) (fun st' h => ⟨Expr.eval_const (by omega), h⟩)
    (fun k st' _ _ h => h.2.2.2.2.2) (fun k st' _ _ h => Expr.eval_reg_of_eq h.2.2.2.2.1)
    (fun k _ hk => dsCollectD_inner_triple c hi hk)
  refine runs_triple_le hloop ?_ (fun o st' h => ?_) ?_
  · refine ⟨?_, by simp [r7], by simp, by simp, by simp, by simp⟩
    rw [dAcc_zero]
    exact ⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4], by simp [r5],
      by simp [r6], hL, hS, hfr⟩
  · cases o with
    | returned _ => exact h.elim
    | normal =>
      obtain ⟨⟨q0, q1, q2, q3, q4, q5, q6, hL', hS', hfr'⟩, q7, -⟩ := h
      rw [dAcc_len] at q6 hL' hS'
      exact ⟨⟨⟨by simp [q0], by simp [q1], by simp [q2], by simp [q3], by simp [q4],
        by simp [q5], by simp [q6], hL', hS', hfr'⟩, by simp⟩, q7⟩
  · simp only [Expr.size]
    omega

/-- `dsCollectDStmt` meets `dsCollectDContract`. -/
theorem dsCollectD_meetsContract (c : DCtx) {p : Program} {bD : ℕ}
    (hpD : p.HasAt bD collectDProcs) :
    MeetsContract c.w p (bD + collectDIdx) (dsCollectDContract c) := by
  refine meetsContract_of_runs
    (hpD.get (i := collectDIdx) (by simp [collectDProcs, collectDIdx])) ?_
  rintro args mem pos ω _ ⟨rfl, hmem⟩
  subst hmem
  simp only [collectDProcs, collectDIdx, List.getElem_cons_zero]
  dsimp only [dsCollectDStmt]
  have hw16 := c.hw16
  have hesB := c.hesB
  let stepCost : ℕ → ℕ := fun i => 50 * (c.T (c.es.getD i 0)).length + 40
  have hloop := Triple.forRange_le (w := c.w) (p := p)
    (P := fun st' => DOuterInv c 0 { st' with regs := Function.update st'.regs 7 0 })
    (r := 7) (lo := .const 0) (hi := .reg 1) (body := dsCollectDOuterStmt)
    (Inv := DOuterInv c) stepCost 0 c.es.length (Nat.zero_le _) (by omega)
    (fun _ => by omega) (fun st' h => ⟨Expr.eval_const (by omega), h⟩)
    (fun k st' _ _ h => h.2) (fun k st' _ _ h => Expr.eval_reg_of_eq h.1.2.1)
    (fun k _ hk => (dsCollectD_outer_triple c hk).conseq (fun _ h => h) (fun _ _ h => h)
      (fun _ _ => by simp only [stepCost]; rw [List.getD_eq_getElem _ _ hk]))
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  refine runs_seq_triple_le hloop ?_ ?_
  · refine ⟨⟨by simp [startState], by simp [startState], by simp [startState],
      by simp [startState], by simp [startState], by simp [startState], by simp [dList, addNew],
      fun j hj => by simp [dList, addNew] at hj,
      fun x _ => ⟨fun h => by simp [dList, addNew] at h, fun _ => rfl⟩, fun _ _ _ => rfl⟩, by simp⟩
  · intro st hI
    obtain ⟨⟨_, _, _, _, _, _, q6, hL, hS, hfr⟩, _⟩ := hI
    rw [List.take_of_length_le (Nat.le_refl _)] at q6 hL hS
    refine runs_ret_le (v := (dList c.T c.es).length) (Expr.eval_reg_of_eq q6)
      ⟨rfl, hL, hS, hfr⟩ ?_
    have hsum := sum_range_getD c.es (fun e => 50 * (c.T e).length + 40)
    have hout := sum_outer c.T c.es
    simp only [rangeCost_zero_eq_range, Expr.size, dsCollectDContract, stepCost]
    omega

end

end MinCostFlow.DynSpanner.Program
