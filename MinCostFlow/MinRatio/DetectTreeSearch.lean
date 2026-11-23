module

public import MinCostFlow.MinRatio.PathTreeCall
import WordRAM.Tactic

/-!
# Reading the forest-wide Detect search result

The proof of Theorem 5.1 (pages 29–30) finds an edge with nonnegative
residual. The linked search writes either an exposed ready slot or
zero. This procedure reads that word and retains the tree's heap.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM LinkCut

/-- The handle and incoming heap are the two search arguments. The
new heap stays in register 2 and the result is placed in register 3. -/
@[expose] def detectTreeSearch (find : ℕ) : Stmt :=
  .call 2 find [.reg 0, .reg 1] ;;
  .assign 3 (.load (.reg 1))

/-- The linked search uses deterministic instructions. -/
theorem detectTreeSearch_noRand (find : ℕ) : (detectTreeSearch find).NoRand := by
  simp [detectTreeSearch, Stmt.NoRand]

/-- Link FindReady and decode its exact search outcome. The amortized
cost adds seven steps to the tree budget. -/
theorem detectTreeSearch_runs {w L constant init handle heap : ℕ}
    {fmt : Num.Format w} {p : Program} {st : State} {ω : ℕ → Bool}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {R : DSRep PathTreeState}
    {op : ℕ → ℕ} {s : PathTreeState} {x : R.τ}
    (himpl : R.Implements w p init op (pathTreeMachineContract fmt L constant allocation))
    (hregs : st.regs 0 = handle ∧ st.regs 1 = heap)
    (hh : handle < 2 ^ w)
    (hpre : (pathTreeMachineContract fmt L constant allocation).pre 6 s [handle, heap] st.mem)
    (hrep : R.rep handle s x st.mem) (hfoot : ∀ a, R.foot handle x a → a < heap)
    (hz : ZeroFrom st.mem heap) (hroom : heap + allocation 6 s.n [handle, heap] < 2 ^ w) :
    ∃ (s' : PathTreeState) (cost ret slot : ℕ) (out : State) (y : R.τ),
      Runs w p ω (detectTreeSearch (op 6)) st .normal out cost ∧
      out.regs 2 = ret ∧ out.regs 3 = slot ∧
      (∀ r, r ≠ 2 → r ≠ 3 → out.regs r = st.regs r) ∧
      R.rep handle s' y out.mem ∧
      R.Respects (R.foot handle x) heap (allocation 6 s.n [handle, heap]) st.mem ret handle y out.mem ∧
      (if slot = 0 then s' = s ∧ ¬ ∃ a, pathTreeReady s a
        else pathTreeReady s slot ∧ s' = lctExpose pathPayload s slot) ∧
      cost + R.phi handle y out.mem ≤ pathTreeBudget constant L s.n + R.phi handle x st.mem + 7 := by
  obtain ⟨hhandle, hheapReg⟩ := hregs
  have hheap : heap < 2 ^ w := by omega
  obtain ⟨s', cost, after, y, ret, hrun, hrep', hpost, hmem, hcost⟩ :=
    pathTree_runs_call (i := 6) (reg := 2) (st := st) (ω := ω) (args := [.reg 0, .reg 1])
      (vs := [handle, heap]) himpl (by simp [evalArgs, Expr.eval, hhandle, hheapReg]) (by wram_words) rfl hrep hpre hfoot hz hroom
  let mid := { after with regs := Function.update st.regs 2 ret }
  let slot := after.mem heap
  let out := { mid with regs := Function.update mid.regs 3 slot }
  have hload : (Expr.load (.reg 1)).eval w mid = some slot := by
    simp [Expr.eval, mid, hheapReg, slot]
  have hassign : Runs w p ω (.assign 3 (.load (.reg 1))) mid .normal out 3 :=
    runs_assign_iff.mpr ⟨slot, hload, rfl, rfl, rfl⟩
  refine ⟨s', cost + 3 + 1, ret, slot, out, y, ?_, ?_, ?_, ?_, hrep', hmem, ?_, ?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨mid, cost, 3, hrun, hassign, rfl⟩)
  · simp [out, mid, Function.update_of_ne]
  · simp [out]
  · intro r hr₂ hr₃
    simp [out, mid, Function.update_of_ne, hr₂, hr₃]
  · by_cases hzero : slot = 0
    · exact (ite_eq_left hzero).symm ▸ pathTreeMachineContract_find_zero hpost hzero
    · exact (ite_eq_right hzero).symm ▸ pathTreeMachineContract_find_nonzero hpost hzero
  · change cost + R.phi handle y after.mem ≤ pathTreeBudget constant L s.n + R.phi handle x st.mem + 3 at hcost
    change cost + 3 + 1 + R.phi handle y after.mem ≤
      pathTreeBudget constant L s.n + R.phi handle x st.mem + 7
    omega

end MinCostFlow.MinRatio
