module

public import MinCostFlow.MinRatio.ShiftBranch
public import MinCostFlow.MinRatio.SparseCoreContractState

/-!
# Restarting the selected branch during Shift

Algorithm 1 (page 20) advances the branch and uses the newly selected
sparsifier. Restart its spanner at the current graph before obtaining
that sparsifier, as specified by the run with restarts.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain

/-- Registers 3 and 4 hold the sparse-core handle and live heap. The
restart receives the branch chosen in register 2. -/
@[expose] def shiftRestart (entry : ℕ) : Stmt :=
  shiftBranch ;; .call 4 entry [.reg 3, .reg 2, .reg 4]

/-- Execute the shift branch advance and restart, preserving the
input graph history and charging the linked restart budget. -/
theorem shiftRestart_runs {w L k M N vCap eCap init addr branch handle heap : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph G : MGraph}
    {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep tool.State} {s : tool.State} {x : R.τ}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (himpl : R.Implements w p init op
      (sparseCoreMachineContract fmt L tool initialGraph k M N vCap eCap costs allocation))
    (ha : st.regs 0 = addr) (hk : st.regs 1 = k)
    (hh : st.regs 3 = handle) (hheap : st.regs 4 = heap)
    (hb : st.mem addr = branch) (hj : branch < k) (hw : k < 2 ^ w)
    (hhandle : handle < 2 ^ w) (haheap : addr < heap) (hsep : ¬ R.foot handle x addr)
    (hrep : R.rep handle s x st.mem)
    (hG : SparseCoreInput tool.toSparseCoreTool tool.restart k s G)
    (hfoot : ∀ a, R.foot handle x a → a < heap) (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 1 [handle, (branch + 1) % k, heap] < 2 ^ w) :
    let selected := (branch + 1) % k
    let next := tool.restart s selected
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (shiftRestart (op 1)) st .normal out cost ∧
      out.regs 2 = selected ∧ out.regs 3 = handle ∧ out.regs 4 = ret ∧ out.mem addr = selected ∧
      SparseCoreInput tool.toSparseCoreTool tool.restart k next G ∧ R.rep handle next y out.mem ∧
      R.Respects (R.foot handle x) heap (allocation 1 [handle, selected, heap])
        (Function.update st.mem addr selected) ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤ costs.restartCost M N + R.phi handle x st.mem + 19 ∧
      (∀ r, r ≠ 2 → r ≠ 4 → out.regs r = st.regs r) := by
  dsimp only
  let j := (branch + 1) % k
  obtain ⟨mid, hbranch, hmem, hreg, hsaved, _⟩ :=
    shiftBranch_runs (p := p) (ω := ω) ha hk hb hj hw
  have hlocal := himpl.1 handle s x st.mem mid.mem (fun a hf => by
    have hne : a ≠ addr := fun h => hsep (h ▸ hf)
    rw [hmem, Function.update_of_ne hne])
  have hz' : ZeroFrom mid.mem heap := by
    intro a h
    rw [hmem, Function.update_of_ne (by omega)]
    exact hz a h
  have hj' : j < k := Nat.mod_lt _ (by omega)
  have hword : ∀ a ∈ [handle, j, heap], a < 2 ^ w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> omega
  obtain ⟨body, hbody, o, after, c, hrun, state, y, hrep', hpost, hrespect, hcost⟩ :=
    himpl.2.2 1 handle s x [handle, j, heap] mid.mem mid.pos ω hword rfl
      (hlocal.1 hrep) ⟨handle, j, heap, G, rfl, hj', hG⟩ hfoot hz' hroom
  have hstate : state = tool.restart s j := hpost
  subst state
  let out := { after with regs := Function.update mid.regs 4 o.value }
  have hargs : evalArgs w mid [.reg 3, .reg 2, .reg 4] = some [handle, j, heap] := by
    simp [evalArgs, Expr.eval, hreg, (hsaved 3 (by decide)).trans hh,
      (hsaved 4 (by decide)).trans hheap, j]
  have hcall : Runs w p ω (.call 4 (op 1) [.reg 3, .reg 2, .reg 4]) mid .normal out
      (3 + c + 1) :=
    runs_call_iff.mpr ⟨_, body, o, after, c, hargs, hbody, hrun, rfl, rfl, rfl⟩
  refine ⟨out, o.value, 14 + (3 + c + 1) + 1, y,
    runs_seq_iff.mpr (Or.inr ⟨mid, 14, _, hbranch, hcall, rfl⟩),
    ?_, ?_, by simp [out], ?_, .restart hG j hj', hrep', ?_, ?_, ?_⟩
  · simpa [out, Function.update_of_ne] using hreg
  · simpa only [out, Function.update_of_ne (by decide : 3 ≠ 4)] using
      (hsaved 3 (by decide)).trans hh
  · change after.mem addr = j
    rw [hrespect.2.2.2.1 addr haheap hsep, hmem, Function.update_self]
  · rwa [hmem] at hrespect
  · change c + R.phi handle y after.mem ≤ costs.restartCost M N + R.phi handle x mid.mem at hcost
    change _ + R.phi handle y after.mem ≤ _
    rw [← hlocal.2] at hcost
    omega

  · intro r hr₂ hr₄
    simpa only [out, Function.update_of_ne hr₄] using hsaved r hr₂

end MinCostFlow.MinRatio
