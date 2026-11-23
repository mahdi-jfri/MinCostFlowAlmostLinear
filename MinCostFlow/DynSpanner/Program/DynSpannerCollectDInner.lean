module

public import MinCostFlow.DynSpanner.Program.DynSpannerCollectDDefs
import WordRAM.Tactic

/-!
# The set `D` of a step: one edge of a walk

`dsCollectD_inner_triple` proves one iteration of the inner loop of `dsCollectDStmt`. It reads
the edge `x` at position `k` of the walk `T e` and its stamp. If the stamp is `g`, then `x` is
already in the output, because only written edges carry the stamp `g` (all stamps start below
`g`). Otherwise `x` is new: the step stamps it and appends it to the output.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-- The invariant of the inner loop at position `k` of the walk of `es[i]`. -/
def DInnerInv (c : DCtx) (i : ℕ) (hi : i < c.es.length) (k : ℕ) (st : State) : Prop :=
  DState c (dAcc c.T c.es i k hi) st ∧ st.regs 7 = i ∧ st.regs 8 = c.es[i] ∧
  st.regs 9 = c.mem0 (c.tab + c.es[i]) ∧ st.regs 10 = (c.T c.es[i]).length ∧ st.regs 11 = k

end

public section

/-- One iteration of the inner loop of `dsCollectDStmt`. -/
theorem dsCollectD_inner_triple (c : DCtx) {p : Program} {i : ℕ} (hi : i < c.es.length)
    {k : ℕ} (hk : k < (c.T c.es[i]).length) :
    Triple c.w p (DInnerInv c i hi k) dsCollectDInnerStmt
      (normalPost fun st₁ =>
        DInnerInv c i hi (k + 1) { st₁ with regs := Function.update st₁.regs 11 (k + 1) } ∧
          st₁.regs 11 = k)
      (fun _ => 40) := by
  intro st ω hI
  obtain ⟨⟨r0, r1, r2, r3, r4, r5, r6, hL, hS, hfr⟩, r7, r8, r9, r10, r11⟩ := hI
  have hw16 := c.hw16
  have hsB := c.hsB
  have hoB := c.hoB
  have hg := c.hg
  obtain ⟨heC, hW, hWb, dSW, dOW, hy⟩ := c.hk i hi
  set ptr := c.mem0 (c.tab + c.es[i]) with hptr
  set acc := dAcc c.T c.es i k hi with hacc
  set x := ((c.T c.es[i])[k]).1 with hx
  have hxC : x < c.eCap := hy _ (List.getElem_mem hk)
  have hlen : acc.length < dTotal c.T c.es := by
    have h1 := length_dAcc_le c.T c.es i k hi
    rw [← hacc] at h1
    have h2 := dTotal_succ c.T c.es i hi
    have h3 := dTotal_take_le c.T c.es (i + 1)
    omega
  -- The edge word of position `k`.
  have hxrd : st.mem (ptr + 1 + 2 * k) = x := by
    rw [hfr _ (dSW.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))
      (dOW.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))]
    exact MWalkAt_step_edge hW hk
  have hnext : dAcc c.T c.es i (k + 1) hi = addNew acc [x] := dAcc_succ c.T c.es i k hi hk
  dsimp only [dsCollectDInnerStmt, dsCollectDAddr]
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := x)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq r9)
      (Expr.eval_const (by omega)) (by omega)) (Expr.eval_mul (Expr.eval_const (by omega))
        (Expr.eval_reg_of_eq r11) (by omega)) (by omega)) hxrd) ?_
  refine runs_seq_assign_le (v := st.mem (c.stamp + x))
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r3]))
      (Expr.eval_reg_of_eq (by simp)) (by omega)) rfl) ?_
  refine runs_cond_le (Expr.eval_eq_op (x := st.mem (c.stamp + x)) (y := c.g)
    (Expr.eval_reg_of_eq (by simp))
    (Expr.eval_reg_of_eq (by simp [r4])) (by omega)) (fun hne => ?_) (fun heq => ?_)
  · -- The stamp is `g`: `x` is already in the output.
    have hsx : st.mem (c.stamp + x) = c.g := by
      by_contra h; simp [h] at hne
    have hxacc : x ∈ acc := by
      by_contra h
      have := (hS x hxC).2 h
      have := c.hstamp x hxC
      omega
    have hsame : dAcc c.T c.es i (k + 1) hi = acc := by
      rw [hnext, addNew_singleton]; simp [hxacc]
    refine runs_nop_le ⟨⟨?_, by simp [r7], by simp [r8], by simp [r9, hptr], by simp [r10], by simp⟩,
      by simp [r11]⟩ (by simp [Expr.size])
    rw [hsame]
    exact ⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4], by simp [r5],
      by simp [r6], hL, hS, hfr⟩
  · -- The stamp is not `g`: `x` is new.
    have hsx : st.mem (c.stamp + x) ≠ c.g := by
      intro h; simp [h] at heq
    have hxacc : x ∉ acc := fun h => hsx ((hS x hxC).1 h)
    have hnew : dAcc c.T c.es i (k + 1) hi = acc ++ [x] := by
      rw [hnext, addNew_singleton]; simp [hxacc]
    have hSO : c.stamp + x < c.out ∨ c.out + dTotal c.T c.es ≤ c.stamp + x :=
      c.dOS.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega)
    refine runs_seq_store_le (x := c.stamp + x) (v := c.g)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r3])) (Expr.eval_reg_of_eq (by simp))
        (by omega)) (Expr.eval_reg_of_eq (by simp [r4])) ?_
    refine runs_seq_store_le (x := c.out + acc.length) (v := x)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r5])) (Expr.eval_reg_of_eq (by simp [r6]))
        (by omega)) (Expr.eval_reg_of_eq (by simp)) ?_
    refine runs_assign_le (v := acc.length + 1)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r6])) (Expr.eval_const (by omega))
        (by omega)) ⟨⟨?_, by simp [r7], by simp [r8], by simp [r9, hptr], by simp [r10], by simp⟩,
          by simp [r11]⟩ (by simp [Expr.size])
    rw [hnew]
    have hOS : c.out + acc.length < c.stamp ∨ c.stamp + c.eCap ≤ c.out + acc.length :=
      c.dOS.symm.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega)
    refine ⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4], by simp [r5],
      by simp, ?_, fun y hyC => ⟨fun hy => ?_, fun hy => ?_⟩, fun addr h1 h2 => ?_⟩
    · show ListAt (Function.update (Function.update st.mem _ _) _ _) _ _
      refine listAt_append.mpr ⟨?_, ?_⟩
      · exact (hL.update_outside (hSO.imp id fun h => by omega)).update_ge (Nat.le_refl _)
      · intro j hj
        simp only [List.length_singleton, Nat.lt_one_iff] at hj
        subst hj
        simp
    · show Function.update (Function.update st.mem _ _) _ _ _ = _
      rw [Function.update_of_ne (by omega)]
      rcases List.mem_append.mp hy with hy | hy
      · by_cases hyx : y = x
        · subst hyx; simp
        · rw [Function.update_of_ne (by omega)]
          exact (hS y hyC).1 hy
      · rw [List.mem_singleton.mp hy]; simp
    · show Function.update (Function.update st.mem _ _) _ _ _ = _
      have hyx : y ≠ x := fun h => hy (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr h)))
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact (hS y hyC).2 fun h => hy (List.mem_append.mpr (Or.inl h))
    · show Function.update (Function.update st.mem _ _) _ _ _ = _
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hfr addr h1 h2

end

end MinCostFlow.DynSpanner.Program
