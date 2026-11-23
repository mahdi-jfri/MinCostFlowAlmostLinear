module

public import MinCostFlow.MinRatio.PathTreeContract
public import WordRAM.Logic

/-!
# Calling the Section 6 tree procedures

A call to the shared tree contract changes the concrete tree state
and its potential. The caller pays only the contract's amortized
bound plus the cost of evaluating the call arguments.
-/

public section
namespace MinCostFlow.MinRatio

open WordRAM

/-- A linked tree operation respects its footprint and carries the
potential difference through to the enclosing machine proof. -/
theorem pathTree_runs_call {w L constant init i b reg : ℕ} {p : Program}
    {fmt : Num.Format w} {allocation : ℕ → ℕ → List ℕ → ℕ}
    {R : DSRep PathTreeState} {op : ℕ → ℕ} {s : PathTreeState} {x : R.τ}
    {st : State} {ω : ℕ → Bool} {args : List Expr} {vs : List ℕ}
    (himpl : R.Implements w p init op (pathTreeMachineContract fmt L constant allocation))
    (hargs : evalArgs w st args = some vs) (hwords : ∀ a ∈ vs, a < 2 ^ w)
    (hb : vs.head? = some b) (hrep : R.rep b s x st.mem)
    (hpre : (pathTreeMachineContract fmt L constant allocation).pre i s vs st.mem)
    (hfoot : ∀ a, R.foot b x a → a < heapArg vs)
    (hz : ZeroFrom st.mem (heapArg vs))
    (hroom : heapArg vs + allocation i s.n vs < 2 ^ w) :
    ∃ (next : PathTreeState) (cost : ℕ) (after : State) (y : R.τ) (ret : ℕ),
      Runs w p ω (.call reg (op i) args) st .normal
        { after with regs := Function.update st.regs reg ret } cost ∧
      R.rep b next y after.mem ∧
      (pathTreeMachineContract fmt L constant allocation).post i s vs st.mem next after.mem ∧
      R.Respects (R.foot b x) (heapArg vs) (allocation i s.n vs) st.mem ret b y after.mem ∧
      cost + R.phi b y after.mem ≤
        pathTreeBudget constant L s.n + R.phi b x st.mem + argsSize args + 1 := by
  obtain ⟨body, hbody, o, after, cost, hrun, next, y, hrep', hpost, hmem, hcost⟩ :=
    himpl.2.2 i b s x vs st.mem st.pos ω hwords hb hrep hpre hfoot hz hroom
  refine ⟨next, argsSize args + cost + 1, after, y, o.value, ?_, hrep', hpost, hmem, ?_⟩
  · exact runs_call_iff.mpr ⟨vs, body, o, after, cost, hargs, hbody, hrun, rfl, rfl, rfl⟩
  · change cost + R.phi b y after.mem ≤ pathTreeBudget constant L s.n + R.phi b x st.mem at hcost
    omega

/-- Initialize the Section 6 path tree using the runtime vertex bound,
limb count, and heap pointer. The old heap address is its handle. -/
@[expose] def callInitPathTree (entry vertexReg heapReg resultReg : ℕ) : Stmt :=
  .call resultReg entry [.reg vertexReg, .reg 67, .reg heapReg]

/-- The Init call passes the limb count in the new three-word layout
and produces the empty path tree and a fresh heap pointer. -/
theorem callInitPathTree_runs
    {w L constant entry vertexReg heapReg resultReg n heap : ℕ} {p : Program}
    {fmt : Num.Format w} {allocation : ℕ → ℕ → List ℕ → ℕ}
    {R : DSRep PathTreeState} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (himpl : R.Implements w p entry op (pathTreeMachineContract fmt L constant allocation))
    (hn : st.regs vertexReg = n) (hL : st.regs 67 = L) (hh : st.regs heapReg = heap)
    (hwords : ∀ a ∈ [n, L, heap], a < 2 ^ w)
    (hp : (pathTreeMachineContract fmt L constant allocation).initPre [n, L, heap] st.mem)
    (hz : ZeroFrom st.mem heap) (hroom : heap + allocation 7 n [n, L, heap] < 2 ^ w) :
    ∃ out cost s x ret,
      Runs w p ω (callInitPathTree entry vertexReg heapReg resultReg) st .normal out cost ∧
      out.regs resultReg = ret ∧
      (∀ r ≠ resultReg, out.regs r = st.regs r) ∧ R.rep heap s x out.mem ∧
      (pathTreeMachineContract fmt L constant allocation).initPost [n, L, heap] st.mem s out.mem ∧
      R.Respects (fun _ => False) heap (allocation 7 n [n, L, heap]) st.mem ret heap x out.mem ∧
      cost + R.phi heap x out.mem ≤ constant * (L + 1) ^ 2 * (n + 1) + 4 := by
  have ha : evalArgs w st [.reg vertexReg, .reg 67, .reg heapReg] = some [n, L, heap] := by
    simp [evalArgs, Expr.eval, hn, hL, hh]
  have hpHeap : heapArg [n, L, heap] = heap := by simp [heapArg]
  obtain ⟨body, hbody, o, final, c, hr, s, x, hrep, hpost, hframe, hc⟩ :=
    himpl.2.1 [n, L, heap] st.mem st.pos ω hwords hp (hpHeap.symm ▸ hz) (by
      rw [hpHeap]
      exact hroom)
  let out := { final with regs := Function.update st.regs resultReg o.value }
  rw [hpHeap] at hrep hframe hc
  change R.Respects (fun _ => False) heap (allocation 7 n [n, L, heap])
    st.mem o.value heap x final.mem at hframe
  change c + R.phi heap x final.mem ≤ constant * (L + 1) ^ 2 * (n + 1) at hc
  exact ⟨out, 3 + c + 1, s, x, o.value,
    runs_call_iff.mpr ⟨[n, L, heap], body, o, final, c, ha, hbody, hr, rfl, rfl, rfl⟩,
    by simp [out], fun r hr => by simp [out, hr], hrep, hpost, hframe, by dsimp [out]; omega⟩

/-- Keep the tree handle in the Init header register and advance the
heap pointer after calling the shared path-tree initializer. -/
@[expose] def initPathTreeAtHeap (entry vertexReg : ℕ) : Stmt :=
  .assign 80 (.reg 99) ;;
  callInitPathTree entry vertexReg 99 99

/-- The saved handle identifies the initialized tree after the heap advances. -/
theorem initPathTreeAtHeap_runs
    {w L constant entry vertexReg n heap : ℕ} {p : Program}
    {fmt : Num.Format w} {allocation : ℕ → ℕ → List ℕ → ℕ}
    {R : DSRep PathTreeState} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (himpl : R.Implements w p entry op (pathTreeMachineContract fmt L constant allocation))
    (hvertex : vertexReg ≠ 80)
    (hn : st.regs vertexReg = n) (hL : st.regs 67 = L) (hh : st.regs 99 = heap)
    (hwords : ∀ a ∈ [n, L, heap], a < 2 ^ w)
    (hp : (pathTreeMachineContract fmt L constant allocation).initPre [n, L, heap] st.mem)
    (hz : ZeroFrom st.mem heap) (hroom : heap + allocation 7 n [n, L, heap] < 2 ^ w) :
    ∃ out cost s x ret, Runs w p ω (initPathTreeAtHeap entry vertexReg) st .normal out cost ∧
      out.regs 80 = heap ∧ out.regs 99 = ret ∧
      (∀ r, r ≠ 80 → r ≠ 99 → out.regs r = st.regs r) ∧ R.rep heap s x out.mem ∧
      (pathTreeMachineContract fmt L constant allocation).initPost [n, L, heap] st.mem s out.mem ∧
      R.Respects (fun _ => False) heap (allocation 7 n [n, L, heap]) st.mem ret heap x out.mem ∧
      cost + R.phi heap x out.mem ≤ constant * (L + 1) ^ 2 * (n + 1) + 7 := by
  let mid := { st with regs := Function.update st.regs 80 heap }
  have hr₁ : Runs w p ω (.assign 80 (.reg 99)) st .normal mid 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, hh], rfl, rfl, rfl⟩
  obtain ⟨out, c, s, x, ret, hr₂, hret, hkeep, hrep, hpost, hframe, hc⟩ :=
    callInitPathTree_runs (ω := ω) (st := mid) (vertexReg := vertexReg) (heapReg := 99) (resultReg := 99) himpl
      (by simpa [mid, hvertex] using hn) (by simpa [mid] using hL) (by simpa [mid] using hh)
      hwords hp hz hroom
  exact ⟨out, 2 + c + 1, s, x, ret, runs_seq_iff.mpr (Or.inr ⟨mid, 2, c, hr₁, hr₂, rfl⟩),
    (hkeep 80 (by decide)).trans (by simp [mid]), hret,
    fun r h80 h99 => (hkeep r h99).trans (by simp [mid, h80]), hrep, hpost, hframe, by omega⟩

/-- The path-tree initializer allocates above the threshold table, so
every certified threshold remains valid after the call. -/
theorem initPathTreeAtHeap_preservesTable
    {w L constant entry vertexReg n heap base last : ℕ} {p : Program}
    {fmt : Num.Format w} {allocation : ℕ → ℕ → List ℕ → ℕ}
    {R : DSRep PathTreeState} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    {threshold : ℕ → ℕ}
    (himpl : R.Implements w p entry op (pathTreeMachineContract fmt L constant allocation))
    (hvertex : vertexReg ≠ 80)
    (hn : st.regs vertexReg = n) (hL : st.regs 67 = L) (hh : st.regs 99 = heap)
    (hwords : ∀ a ∈ [n, L, heap], a < 2 ^ w)
    (hp : (pathTreeMachineContract fmt L constant allocation).initPre [n, L, heap] st.mem)
    (hz : ZeroFrom st.mem heap) (hroom : heap + allocation 7 n [n, L, heap] < 2 ^ w)
    (hbase : st.regs 83 = base) (htable : ∀ j ≤ last, st.mem (base + j) = threshold j)
    (hbelow : base + last < heap) :
    ∃ out cost s x ret, Runs w p ω (initPathTreeAtHeap entry vertexReg) st .normal out cost ∧
      out.regs 80 = heap ∧ out.regs 99 = ret ∧ out.regs 83 = base ∧
      R.rep heap s x out.mem ∧
      (pathTreeMachineContract fmt L constant allocation).initPost [n, L, heap] st.mem s out.mem ∧
      R.Respects (fun _ => False) heap (allocation 7 n [n, L, heap]) st.mem ret heap x out.mem ∧
      (∀ j ≤ last, out.mem (base + j) = threshold j) ∧
      cost + R.phi heap x out.mem ≤ constant * (L + 1) ^ 2 * (n + 1) + 7 := by
  obtain ⟨out, cost, s, x, ret, hr, htree, hret, hkeep, hrep, hpost, hframe, hcost⟩ :=
    initPathTreeAtHeap_runs (ω := ω) himpl hvertex hn hL hh hwords hp hz hroom
  refine ⟨out, cost, s, x, ret, hr, htree, hret, (hkeep 83 (by decide) (by decide)).trans hbase,
    hrep, hpost, hframe, ?_, hcost⟩
  intro j hj
  exact (hframe.2.2.2.1 (base + j) (by omega) (by simp)).trans (htable j hj)

/-- The path-tree Init precondition depends on the vertex bound and
fixed-point format. The threshold table occupies separate memory. -/
theorem pathTree_initPre_of_runtimeFormat
    {w L constant n heap : ℕ} {fmt : Num.Format w}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {mem : ℕ → ℕ}
    (hn : 2 * n + 1 < 2 ^ w) (hL : L < 2 ^ w)
    (hP : fmt.precision < 2 ^ w) (hfit : Nat.log 2 (2 * n + 1) ≤ fmt.limbBits * L) :
    (pathTreeMachineContract fmt L constant allocation).initPre [n, L, heap] mem := by
  exact ⟨n, heap, rfl, hn, hL, hP, hfit⟩

end MinCostFlow.MinRatio
