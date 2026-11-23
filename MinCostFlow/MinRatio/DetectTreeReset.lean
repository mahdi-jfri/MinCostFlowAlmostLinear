module

public import MinCostFlow.MinRatio.PathTreeCall
import WordRAM.Tactic

/-!
# Installing a Detect replacement record

The proof of Theorem 5.1 (pages 29–30) reports a ready edge and
resets its accumulated account. The prepared replacement record
keeps the other fields. The linked point write installs it in the
exposed slot and retains the amortized potential accounting.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM LinkCut

/-- Handle, slot, replacement record, and heap are the input registers. -/
@[expose] def detectTreeReset (write : ℕ) : Stmt :=
  .call 4 write [.reg 0, .reg 1, .reg 2, .reg 3]

/-- The point-write call is deterministic when the linked writer is. -/
theorem detectTreeReset_noRand (write : ℕ) : (detectTreeReset write).NoRand := by
  simp [detectTreeReset, Stmt.NoRand]

/-- The replacement layout and the post-reset fit proof supply the
PointWrite precondition for an active edge slot. -/
theorem detectTreeReset_pre {w L constant handle slot record heap : ℕ}
    {fmt : Num.Format w} {allocation : ℕ → ℕ → List ℕ → ℕ}
    {s : PathTreeState} {mem : ℕ → ℕ} {edge : PathEdgeValue} {threshold : ℤ}
    (hinv : LctInv pathPayload s) (hfit : pathTreeFits fmt.limbBits L s)
    (hword : 2 * s.n + 1 < 2 ^ w) (hwidth : Nat.log 2 (2 * s.n + 1) ≤ fmt.limbBits * L)
    (hslot : isEdgeSlot s.n slot) (hactive : pathTreeActive s slot)
    (hbelow : record + (2 + 4 * L) ≤ heap)
    (hrecord : PathEdgeAt mem record fmt.limbBits L (some { edge with detector := -threshold }))
    (hnext : pathTreeFits fmt.limbBits L
      (pathTreeWrite s slot (some { edge with detector := -threshold }))) :
    (pathTreeMachineContract fmt L constant allocation).pre 5 s [handle, slot, record, heap] mem := by
  have hread := readPathEdge_eq hrecord
  refine ⟨hinv, hfit, hword, hwidth, handle, slot, record, heap, rfl, hslot, hactive, hbelow, ?_, ?_, ?_⟩
  · rwa [hread]
  · rw [hread]
    rfl
  · rwa [hread]

/-- Install the detector reset using the Section 6 point-write
contract. The four argument reads and call instruction cost five steps. -/
theorem detectTreeReset_runs {w L constant init handle slot record heap pos : ℕ}
    {fmt : Num.Format w} {p : Program} {mem : ℕ → ℕ} {ω : ℕ → Bool}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {R : DSRep PathTreeState}
    {op : ℕ → ℕ} {s : PathTreeState} {x : R.τ} {edge : PathEdgeValue} {threshold : ℤ}
    (himpl : R.Implements w p init op (pathTreeMachineContract fmt L constant allocation))
    (hwords : ∀ a ∈ [handle, slot, record, heap], a < 2 ^ w)
    (hpre : (pathTreeMachineContract fmt L constant allocation).pre 5 s
      [handle, slot, record, heap] mem)
    (hrecord : PathEdgeAt mem record fmt.limbBits L (some { edge with detector := -threshold }))
    (hrep : R.rep handle s x mem) (hfoot : ∀ a, R.foot handle x a → a < heap)
    (hz : ZeroFrom mem heap)
    (hroom : heap + allocation 5 s.n [handle, slot, record, heap] < 2 ^ w) :
    let updated := pathTreeWrite s slot (some { edge with detector := -threshold })
    ∃ (cost ret : ℕ) (out : State) (y : R.τ),
      Runs w p ω (detectTreeReset (op 5)) (startState [handle, slot, record, heap] mem pos)
        .normal out cost ∧ out.regs 4 = ret ∧
      R.rep handle updated y out.mem ∧
      R.Respects (R.foot handle x) heap (allocation 5 s.n [handle, slot, record, heap])
        mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤ pathTreeBudget constant L s.n + R.phi handle x mem + 5 := by
  dsimp only
  let st := startState [handle, slot, record, heap] mem pos
  obtain ⟨s', cost, after, y, ret, hrun, hrep', hpost, hmem, hcost⟩ :=
    pathTree_runs_call (i := 5) (reg := 4) (st := st) (ω := ω)
      (args := [.reg 0, .reg 1, .reg 2, .reg 3]) (vs := [handle, slot, record, heap])
      himpl (by eval_expr) hwords rfl hrep hpre hfoot hz hroom
  have hs : s' = pathTreeWrite s slot (some { edge with detector := -threshold }) := by
    change s' = pathTreeWrite s slot (readPathEdge mem record fmt.limbBits L) at hpost
    rw [readPathEdge_eq hrecord] at hpost
    exact hpost
  rw [hs] at hrep'
  exact ⟨cost, ret, { after with regs := Function.update st.regs 4 ret }, y,
    hrun, by simp, hrep', hmem, hcost⟩

end MinCostFlow.MinRatio
