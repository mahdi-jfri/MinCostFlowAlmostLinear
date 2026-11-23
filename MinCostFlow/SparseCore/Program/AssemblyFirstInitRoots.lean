module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitSlots
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# The roots of the forest in increasing order (`AssemblyFirstInitRoots`)

P5's init of the slots (`bunTableHeadroom_initSlots_runs`) walks the tour lists of a list `rList`
of vertices. Its link to the model (`tableAfterInitSlots_bunAgree`) asks `rList` to be strictly
increasing, made of core vertices, and to hold every vertex whose tour list has an end of a core
edge. The core vertices are the roots of the forest. P4's export holds them as a list without
repeats, but in no fixed order.

So the build copies that list to fresh memory and sorts the copy (`rootsListBody`). The export lies
below the heap pointer and must not change, which is why the sort works on a copy. Since the roots
have no repeats, the sorted copy is strictly increasing (`rootsList_runs`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.DynSpanner.Program

/-- Round `i` of the copy: the word at `rootsPtr + i` goes to `heap + i`. The registers are
`0 = rootsPtr`, `1 = nR`, `2 = heap`, and `3 = i`. -/
def rootsCopyStep : Stmt :=
  .store (.bin .add (.reg 2) (.reg 3)) (.load (.bin .add (.reg 0) (.reg 3)))

/-- **The roots in increasing order**, `[rootsPtr, nR, heap]`: copy the `nR` words at `rootsPtr`
to `heap`, sort the copy with scratch at `heap + nR` (`mergeSortContract`), and return
`heap + 2 nR`. -/
def rootsListBody (bSort : ℕ) : Stmt :=
  forRange 3 (.const 0) (.reg 1) rootsCopyStep ;;
  .call 4 (bSort + sortIdxMergeSort) [.reg 2, .reg 1, .bin .add (.reg 2) (.reg 1)] ;;
  .ret (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 1)))

theorem rootsListBody_noRand (bSort : ℕ) : (rootsListBody bSort).NoRand := by
  simp [rootsListBody, rootsCopyStep, forRange, forUp, Stmt.NoRand]

/-- The cost of `rootsListBody` on `n` roots. -/
def rootsListCost (n : ℕ) : ℕ := 200 * n * (Nat.log 2 (n + 1) + 1) + 25 * n + 100

/-- **The copy loop.** Afterwards the words `heap + t` for `t < nR` hold the words
`rootsPtr + t`; only register `3` and the words in `[heap, heap + nR)` change. -/
theorem rootsCopy_loop {w : ℕ} {p : Program} {mem : ℕ → ℕ} {rootsPtr nR heap : ℕ}
    (R : ℕ → ℕ) (hR0 : R 0 = rootsPtr) (hR1 : R 1 = nR) (hR2 : R 2 = heap)
    (hlay : rootsPtr + nR ≤ heap) (hw : heap + nR < 2 ^ w) (hw16 : 16 ≤ 2 ^ w) :
    Triple w p (fun st => st.mem = mem ∧ ∀ r, r ≠ 3 → st.regs r = R r)
      (forRange 3 (.const 0) (.reg 1) rootsCopyStep)
      (normalPost fun st => (∀ r, r ≠ 3 → st.regs r = R r) ∧
        (∀ a, (a < heap ∨ heap + nR ≤ a) → st.mem a = mem a) ∧
        ∀ t < nR, st.mem (heap + t) = mem (rootsPtr + t))
      (fun _ => nR * 21 + 7) := by
  have hw1 : 1 < 2 ^ w := by omega
  let Inv : ℕ → State → Prop := fun i st =>
    (∀ r, r ≠ 3 → st.regs r = R r) ∧ st.regs 3 = i ∧
    (∀ a, (a < heap ∨ heap + i ≤ a) → st.mem a = mem a) ∧
    ∀ t < i, st.mem (heap + t) = mem (rootsPtr + t)
  have hstep : ∀ i, 0 ≤ i → i < nR →
      Triple w p (Inv i) rootsCopyStep
        (normalPost fun st₁ =>
          Inv (i + 1) { st₁ with regs := Function.update st₁.regs 3 (i + 1) } ∧
            st₁.regs 3 = i)
        (fun _ => 12) := by
    intro i _ hi st ω' hI
    obtain ⟨hR, r3, hfr, hcp⟩ := hI
    have r0 : st.regs 0 = rootsPtr := (hR 0 (by omega)).trans hR0
    have r2 : st.regs 2 = heap := (hR 2 (by omega)).trans hR2
    have m1 : st.mem (rootsPtr + i) = mem (rootsPtr + i) := hfr _ (Or.inl (by omega))
    refine runs_start_le ?_
    unfold rootsCopyStep
    refine runs_store_le (x := heap + i) (v := mem (rootsPtr + i))
      (Expr.eval_add (by eval_expr) (by eval_expr) (by omega))
      (Expr.eval_load_of_eq (Expr.eval_add (by eval_expr) (by eval_expr) (by omega)) m1) ?_ ?_
    · refine ⟨⟨fun r hr => ?_, by simp, fun a ha => ?_, fun t ht => ?_⟩, r3⟩
      · simp [hr, hR r hr]
      · dsimp only
        rw [Function.update_of_ne (by omega)]
        exact hfr a (by omega)
      · dsimp only
        by_cases hti : t = i
        · subst hti
          rw [Function.update_self]
        · rw [Function.update_of_ne (by omega)]
          exact hcp t (by omega)
    · simp only [Expr.size_reg, Expr.size_load, Expr.size_bin]
      omega
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 3) (lo := .const 0)
    (hi := .reg 1) (body := rootsCopyStep)
    (P := fun st => st.mem = mem ∧ ∀ r, r ≠ 3 → st.regs r = R r)
    (Inv := Inv) 12 0 nR (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hP => ⟨Expr.eval_const (by omega), fun r hr => by simp [hr, hP.2 r hr], by simp,
      fun a _ => by simp [hP.1], fun t ht => absurd ht (Nat.not_lt_zero _)⟩)
    (fun _ _ _ _ hI => hI.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq ((hI.1 1 (by omega)).trans hR1)) hstep
  refine hloop.conseq (fun st h => h) ?_ ?_
  · intro o st' hQ
    cases o with
    | returned _ => exact hQ
    | normal =>
      obtain ⟨hR, -, hfr, hcp⟩ := hQ
      exact ⟨hR, hfr, hcp⟩
  · intro st _
    simp only [Expr.size_reg, Expr.size_const]
    omega

/-- **The roots in increasing order.** Let the `nR` words at `rootsPtr` be the list `roots`
without repeats, below the heap pointer. Then `rootsListBody` returns `heap + 2 nR` and leaves at
`heap` a strictly increasing list with the members of `roots`. The memory below `heap` does not
change, and the memory from `heap + 2 nR` on stays zero. -/
theorem rootsList_runs {w bSort : ℕ} {p : Program} (hpSort : p.HasAt bSort (sortProcs bSort))
    (ω : ℕ → Bool) {rootsPtr nR heap pos : ℕ} {roots : List ℕ} {mem : ℕ → ℕ}
    (hlen : roots.length = nR) (hnd : roots.Nodup) (hL : ListAt mem rootsPtr roots)
    (hlay : rootsPtr + nR ≤ heap) (hz : ZeroFrom mem heap) (hw : heap + 2 * nR < 2 ^ w)
    (hw16 : 16 ≤ 2 ^ w) (hrw : ∀ x ∈ roots, x < 2 ^ w) :
    ∃ o st' c, Runs w p ω (rootsListBody bSort) (startState [rootsPtr, nR, heap] mem pos) o st' c ∧
      (o = .returned (heap + 2 * nR) ∧
        (∃ rList : List ℕ, rList.Pairwise (· < ·) ∧ (∀ x, x ∈ rList ↔ x ∈ roots) ∧
          ListAt st'.mem heap rList) ∧
        (∀ a < heap, st'.mem a = mem a) ∧ ZeroFrom st'.mem (heap + 2 * nR)) ∧
      c ≤ rootsListCost nR := by
  subst hlen
  set n := roots.length with hn
  set R : ℕ → ℕ := (startState [rootsPtr, n, heap] mem pos).regs with hRdef
  have hR0 : R 0 = rootsPtr := rfl
  have hR1 : R 1 = n := rfl
  have hR2 : R 2 = heap := rfl
  refine runs_start_le ?_
  unfold rootsListBody
  refine runs_seq_triple_le (rootsCopy_loop (mem := mem) R hR0 hR1 hR2 hlay (by omega) hw16)
    ⟨rfl, fun r _ => rfl⟩ (fun st₁ h₁ => ?_)
  obtain ⟨hR₁, hfr₁, hcp₁⟩ := h₁
  have r1 : st₁.regs 1 = n := (hR₁ 1 (by omega)).trans hR1
  have r2 : st₁.regs 2 = heap := (hR₁ 2 (by omega)).trans hR2
  have hlist : ListAt st₁.mem heap roots := fun t ht => (hcp₁ t ht).trans (hL t ht)
  have hms := mergeSort_meetsContract (w := w) (p := p) (b := bSort) (bSort := bSort)
    (L := roots) hpSort hpSort
  refine runs_seq_call_le hms (vs := [heap, n, heap + n]) (by eval_expr)
    (by intro v hv; simp at hv; omega)
    ⟨heap, heap + n, rfl, hw16, by omega, by omega, Or.inl (le_refl _), hlist, hrw⟩
    (fun v mem' pos' hpost => ?_)
  obtain ⟨a, scr, L', hargs, -, hperm, hsorted, hlist', hfr'⟩ := hpost
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, -, rfl⟩ := hargs
  have hnd' : L'.Nodup := hperm.nodup_iff.mpr hnd
  have r1' : (Function.update st₁.regs 4 v) 1 = n := by simp [r1]
  have r2' : (Function.update st₁.regs 4 v) 2 = heap := by simp [r2]
  refine runs_ret_le (v := heap + 2 * n) (by eval_expr) ⟨rfl, ⟨L', ?_, fun x => hperm.mem_iff,
    hlist'⟩, fun b hb => ?_, fun b hb => ?_⟩ ?_
  · exact (hsorted.and hnd').imp fun h => lt_of_le_of_ne h.1 h.2
  · dsimp only
    rw [hfr' b (Or.inl hb) (Or.inl (by omega))]
    exact hfr₁ b (Or.inl hb)
  · dsimp only
    rw [hfr' b (Or.inr (by omega)) (Or.inr (by omega)), hfr₁ b (Or.inr (by omega))]
    exact hz b (by omega)
  · simp only [mergeSortContract, argsSize_cons, argsSize_nil, Expr.size_reg, Expr.size_const,
      Expr.size_bin, rootsListCost, ← hn]
    omega

end MinCostFlow.SparseCore.Program
