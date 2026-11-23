module

public import MinCostFlow.LSF.Program.RootTreeBase
import Mathlib.Tactic.Linarith

/-!
# Rooting a tree: building the half-edge lists

Phase 1 of `rootTreeProc` (`RootTreeBase.lean`) scans the edges `f < m` once and prepends
half-edge `2 f` to the list of `tail[f]` and half-edge `2 f + 1` to the list of `head[f]`. We
prove `rtBuild_triple`: afterwards the list of each vertex `u < n` is `rtHalf tl hd (2 m) u`, and
only the list heads and links changed. The proof is a loop invariant over `forRange` whose step
is `chainFrom_insert` applied twice.
-/

namespace MinCostFlow.LSF.Program

open WordRAM

@[expose] public section

/-- Layout and input facts shared by all phases of `rootTreeProc`. -/
structure RTInput (w n m tailArr headArr r outPtr sPtr : ℕ) (tl hd : ℕ → ℕ)
    (mem : ℕ → ℕ) : Prop where
  hw : 16 ≤ 2 ^ w
  hr : r < n
  htl : ∀ f < m, mem (tailArr + f) = tl f ∧ tl f < n
  hhd : ∀ f < m, mem (headArr + f) = hd f ∧ hd f < n
  htA : tailArr + m ≤ outPtr
  hhA : headArr + m ≤ outPtr
  hout : outPtr + 3 * n ≤ sPtr
  hword : sPtr + 4 * n + 2 * m < 2 ^ w

/-- The invariant of phase 1 after `i` edges. -/
def RTBuildInv (n m tailArr headArr r outPtr sPtr : ℕ) (tl hd : ℕ → ℕ) (mem₀ : ℕ → ℕ)
    (i : ℕ) (st : State) : Prop :=
  RTRegs st n m tailArr headArr r outPtr sPtr ∧ st.regs 12 = i ∧
  (∀ u < n, ChainFrom st.mem (sPtr + n) (st.mem (sPtr + u)) (rtHalf tl hd (2 * i) u)) ∧
  (∀ a, a < sPtr ∨ sPtr + n + 2 * m ≤ a → st.mem a = mem₀ a)

private lemma rtEnd_even (tl hd : ℕ → ℕ) (i : ℕ) : rtEnd tl hd (2 * i) = tl i := by
  simp [rtEnd]

private lemma rtEnd_odd (tl hd : ℕ → ℕ) (i : ℕ) : rtEnd tl hd (2 * i + 1) = hd i := by
  have h1 : (2 * i + 1) % 2 = 1 := by omega
  have h2 : (2 * i + 1) / 2 = i := by omega
  simp [rtEnd, h1, h2]

theorem rtBuild_body {w : ℕ} {p : Program} {n m tailArr headArr r outPtr sPtr : ℕ}
    {tl hd : ℕ → ℕ} {mem₀ : ℕ → ℕ}
    (hI : RTInput w n m tailArr headArr r outPtr sPtr tl hd mem₀) (i : ℕ) (hi : i < m) :
    Triple w p (RTBuildInv n m tailArr headArr r outPtr sPtr tl hd mem₀ i) rtBuildBody
      (normalPost fun st₁ =>
        RTBuildInv n m tailArr headArr r outPtr sPtr tl hd mem₀ (i + 1)
          { st₁ with regs := Function.update st₁.regs 12 (i + 1) } ∧ st₁.regs 12 = i)
      (fun _ => 60) := by
  intro st ω hinv
  obtain ⟨hb, h12, hch, hfr⟩ := hinv
  obtain ⟨hw, -, htl, hhd, htA, hhA, hout, hword⟩ := hI
  have r2 := hb.r2; have r3 := hb.r3; have r6 := hb.r6; have r9 := hb.r9
  have htl_i := htl i hi
  have hhd_i := hhd i hi
  have hmt : st.mem (tailArr + i) = tl i := by rw [hfr _ (Or.inl (by omega))]; exact htl_i.1
  have hmh : st.mem (headArr + i) = hd i := by rw [hfr _ (Or.inl (by omega))]; exact hhd_i.1
  -- first insertion
  set m1 := Function.update (Function.update st.mem (sPtr + n + 2 * i)
    (st.mem (sPtr + tl i))) (sPtr + tl i) (2 * i + 1) with hm1
  have hch1 := chainFrom_insert (tl := tl) (hd := hd) (first := sPtr) (next := sPtr + n)
    (k := 2 * i) hch (rtEnd_even tl hd i) htl_i.2 le_rfl
  have hfr1 : ∀ a, a < sPtr ∨ sPtr + n + 2 * m ≤ a → m1 a = mem₀ a := by
    intro a ha
    rw [hm1, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hfr a ha
  have hmh1 : m1 (headArr + i) = hd i := by rw [hfr1 _ (Or.inl (by omega))]; exact hhd_i.1
  -- second insertion
  set m2 := Function.update (Function.update m1 (sPtr + n + (2 * i + 1))
    (m1 (sPtr + hd i))) (sPtr + hd i) (2 * i + 1 + 1) with hm2
  have hch2 := chainFrom_insert (tl := tl) (hd := hd) (first := sPtr) (next := sPtr + n)
    (k := 2 * i + 1) (mem := m1) (by simpa [hm1] using hch1) (rtEnd_odd tl hd i) hhd_i.2 le_rfl
  refine runs_start_le ?_
  unfold rtBuildBody
  refine runs_seq_assign_le (v := tl i) (by eval_expr) ?_
  refine runs_seq_store_le (x := sPtr + n + 2 * i) (v := st.mem (sPtr + tl i))
    (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := sPtr + tl i) (v := 2 * i + 1) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_assign_le (v := hd i) (by
    show Expr.eval w { mem := m1, regs := Function.update st.regs 13 (tl i), pos := st.pos }
      (.load (.bin .add (.reg 3) (.reg 12))) = some (hd i)
    eval_expr) ?_
  refine runs_seq_store_le (x := sPtr + n + (2 * i + 1)) (v := m1 (sPtr + hd i))
    (by eval_expr) (by eval_expr) ?_
  refine runs_store_le (x := sPtr + hd i) (v := 2 * i + 2) (by eval_expr) (by eval_expr) ?_ ?_
  · refine ⟨⟨(hb.upd 13 (tl i) (by omega)).mem _ |>.upd 13 (hd i) (by omega) |>.mem _
      |>.upd 12 (i + 1) (by omega), by simp, ?_, ?_⟩, ?_⟩
    · intro u hu
      have h := hch2 u hu
      simpa [hm2, show 2 * (i + 1) = 2 * i + 1 + 1 by ring] using h
    · intro a ha
      show m2 a = mem₀ a
      rw [hm2, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hfr1 a ha
    · simp [h12]
  · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]
    omega

/-- Phase 1 builds the half-edge lists of all vertices and changes only the scratch words
`[sPtr, sPtr + n + 2 m)`. -/
theorem rtBuild_triple {w : ℕ} {p : Program} {n m tailArr headArr r outPtr sPtr : ℕ}
    {tl hd : ℕ → ℕ} {mem₀ : ℕ → ℕ}
    (hI : RTInput w n m tailArr headArr r outPtr sPtr tl hd mem₀)
    (hz : ∀ u < n, mem₀ (sPtr + u) = 0) :
    Triple w p (fun st => RTRegs st n m tailArr headArr r outPtr sPtr ∧ st.mem = mem₀)
      (forRange 12 (.const 0) (.reg 1) rtBuildBody)
      (normalPost (RTBuildInv n m tailArr headArr r outPtr sPtr tl hd mem₀ m))
      (fun _ => m * 70 + 10) := by
  have hw := hI.hw
  have hword := hI.hword
  refine (Triple.forRange_const (Inv := RTBuildInv n m tailArr headArr r outPtr sPtr tl hd mem₀)
    60 0 m (Nat.zero_le _) (by omega) (fun _ => by omega) ?_ ?_ ?_
    (fun i _ hi => rtBuild_body hI i hi)).mono_cost ?_
  · rintro st ⟨hb, rfl⟩
    refine ⟨by eval_expr, hb.upd 12 0 (by omega), by simp, ?_, fun _ _ => rfl⟩
    intro u hu
    simp only [Nat.mul_zero, rtHalf, List.range_zero, List.filter_nil, List.reverse_nil,
      ChainFrom]
    exact hz u hu
  · intro i st _ _ h; exact h.2.1
  · intro i st _ _ h
    have := h.1.r1
    eval_expr
  · intro _ _
    simp only [Expr.size_const, Expr.size_reg, Nat.sub_zero]
    omega

end

end MinCostFlow.LSF.Program
