module

public import MinCostFlow.DynSpanner.Program.DynSpannerClearBucketsDefs
import WordRAM.Tactic

/-!
# Emptying the buckets: one edge of a bucket

`dsClearBuckets_inner_triple` proves one iteration of the inner loop of `dsClearBucketsStmt`: it
takes the edge `x = (B i)[k]` from `r7`, reads the next word of `x` (which holds the following edge
plus one), and writes `0` to `minH[x]`. The next word is outside the cells written so far, because
the `next` array is disjoint from `minH` and from the head and length words.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-- The edges of the buckets `B lo, …, B (i - 1)` are below `eCap`. -/
lemma CBCtx.cat_lt (c : CBCtx) {i : ℕ} (hi : i ≤ c.hi) :
    ∀ y ∈ bucketsCat c.B c.lo (i - c.lo), y < c.eCap := by
  intro y hy
  simp only [bucketsCat, List.mem_flatMap, List.mem_range'] at hy
  obtain ⟨i', ⟨k, hk, rfl⟩, hy⟩ := hy
  exact (c.hB (c.lo + 1 * k) (by omega) (by omega)).1.2.1 y hy

/-- The invariant of the inner loop at position `k` of bucket `i`. -/
def CBInner (c : CBCtx) (i k : ℕ) (st : State) : Prop :=
  st.regs 0 = c.nextBase ∧ st.regs 1 = c.headBase ∧ st.regs 2 = c.degBase ∧
  st.regs 4 = c.hi ∧ st.regs 5 = c.minH ∧ st.regs 6 = i ∧ st.regs 8 = (c.B i).length ∧
  st.regs 9 = k ∧ (∀ hk : k < (c.B i).length, st.regs 7 = (c.B i)[k] + 1) ∧
  CBMem c (bucketsCat c.B c.lo (i - c.lo) ++ (c.B i).take k) i st.mem

end

public section

/-- One iteration of the inner loop of `dsClearBucketsStmt`. -/
theorem dsClearBuckets_inner_triple (c : CBCtx) {p : Program} {i k : ℕ} (hlo : c.lo ≤ i)
    (hi : i < c.hi) (hk : k < (c.B i).length) :
    Triple c.w p (CBInner c i k) dsClearBucketsInnerStmt
      (normalPost fun st₁ =>
        CBInner c i (k + 1) { st₁ with regs := Function.update st₁.regs 9 (k + 1) } ∧
          st₁.regs 9 = k)
      (fun _ => 25) := by
  intro st ω hI
  obtain ⟨r0, r1, r2, r4, r5, r6, r8, r9, r7, hz, hzh, hfr⟩ := hI
  have hw16 := c.hw16
  have hnB := c.hnB
  have hmB := c.hmB
  obtain ⟨hdll, _⟩ := c.hB i hlo hi
  obtain ⟨_, hcap, _, hlinks⟩ := hdll
  set x := (c.B i)[k] with hx
  have hxC : x < c.eCap := hcap x (List.getElem_mem hk)
  have hWs : ∀ y ∈ bucketsCat c.B c.lo (i - c.lo) ++ (c.B i).take k, y < c.eCap := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact c.cat_lt (by omega) y hy
    · exact hcap y (List.mem_of_mem_take hy)
  have hnext_rd : st.mem (c.nextBase + x) =
      if k + 1 = (c.B i).length then 0 else (c.B i).getD (k + 1) 0 + 1 := by
    rw [hfr _ (fun y hy => by
        have := hWs y hy
        have := c.dMN.addr_sub (Nat.le_refl _) (Nat.le_refl _) (c.nextBase + x) (by omega)
          (by omega)
        omega)
      (fun i' h1 h2 => ⟨by
        have := c.dNH.addr_sub (Nat.le_refl _) (Nat.le_refl _) (c.headBase + i') (by omega)
          (by omega)
        omega, by
        have := c.dND.addr_sub (Nat.le_refl _) (Nat.le_refl _) (c.degBase + i') (by omega)
          (by omega)
        omega⟩)]
    exact (hlinks k hk).2
  have htake : (c.B i).take (k + 1) = (c.B i).take k ++ [x] := by
    rw [List.take_succ_eq_append_getElem hk]
  dsimp only [dsClearBucketsInnerStmt]
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := x)
    (Expr.eval_eq_of_eq (Expr.eval_sub (Expr.eval_reg_of_eq (r7 hk)) (Expr.eval_const (by omega))
      (by omega)) (by omega)) ?_
  refine runs_seq_assign_le (v := st.mem (c.nextBase + x))
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r0]))
      (Expr.eval_reg_of_eq (by simp)) (by omega)) rfl) ?_
  refine runs_store_le (x := c.minH + x) (v := 0)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r5])) (Expr.eval_reg_of_eq (by simp))
      (by omega)) (Expr.eval_const (by omega))
    ⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp [r4], by simp [r5], by simp [r6],
      by simp [r8], by simp, fun hk1 => ?_, ?_, ?_, ?_⟩, by simp [r9]⟩ (by simp [Expr.size])
  · simp only [Function.update_of_ne (show (7 : ℕ) ≠ 9 by omega), Function.update_self]
    rw [hnext_rd]
    have hne : ¬ (k + 1 = (c.B i).length) := by omega
    simp only [hne, ite_false, List.getD_eq_getElem _ _ hk1]
  · intro y hy
    show Function.update st.mem _ _ _ = 0
    rw [htake, ← List.append_assoc] at hy
    rcases List.mem_append.mp hy with hy | hy
    · by_cases hyx : y = x
      · subst hyx; simp
      · rw [Function.update_of_ne (by omega)]
        exact hz y hy
    · rw [List.mem_singleton.mp hy]; simp
  · intro i' h1 h2
    show Function.update st.mem _ _ _ = 0 ∧ Function.update st.mem _ _ _ = 0
    have hmh := c.dMH.addr_sub (Nat.le_refl _) (Nat.le_refl _) (c.headBase + i') (by omega)
      (by omega)
    have hmd := c.dMD.addr_sub (Nat.le_refl _) (Nat.le_refl _) (c.degBase + i') (by omega)
      (by omega)
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hzh i' h1 h2
  · intro addr h1 h2
    show Function.update st.mem _ _ _ = _
    rw [htake, ← List.append_assoc] at h1
    rw [Function.update_of_ne (h1 x (List.mem_append.mpr (Or.inr (List.mem_singleton_self x))))]
    exact hfr addr (fun y hy => h1 y (List.mem_append.mpr (Or.inl hy))) h2

end

end MinCostFlow.DynSpanner.Program
