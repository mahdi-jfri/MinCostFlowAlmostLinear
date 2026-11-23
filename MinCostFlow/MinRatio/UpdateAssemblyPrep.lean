module

public import MinCostFlow.MinRatio.UpdateAssemblyBase
import MinCostFlow.MinRatio.SolverTreeBudgetInv
import WordRAM.Tactic

/-!
# Preparation stage of end-to-end Word-RAM `Update` assembly

Proves `solverUpdatePrepBody_runs` covering Steps 0–3 of `solverUpdateBody`:
- Loads header parameters and computes scratch layout (`descOut`, `quotaBase`, `zeroBlock`,
  `etaCopy`, `batchSave`, `h0`).
- Copies `eta` and `batch` above `heap` before mutating any footprint cell.
- Calls `growIntTablesBody` to guarantee `model.nextFresh + U.length ≤ tokG.intCap`.
- Copies `batchSave` above `tokG.inverse` and calls `freshBatchEntry` to produce the
  translated internal batch `U_int` in both `BatchAt` and `SmallBatchAt` layout.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine

/-- Total heap space reserved by `solverUpdateBody`. The term `2 * (m * L)` is the room for the
copies of the caller's `g` and `l` entries at the inserted edges (`copyInsertedStmt`). -/
@[expose] def updateSpaceBound (L m d nextFresh batchLen N findSpace shiftSpace
    maxEdges maxPaths refreshSpace : ℕ) : ℕ :=
  (4 * L + d + 5) + 12 * (nextFresh + batchLen) + 4 * (4 * batchLen + 1) + 2 * (m * L) +
    refreshSpace + (N + 1) * cycleLoopIterSpace L findSpace shiftSpace +
    2 * L + goodApplySpace L maxPaths maxEdges

/-- Good-branch amortized step budget of `solverUpdateBody`. -/
@[expose] def updateGoodBranchBudget (L n maxEdges maxPaths drainUnit : ℕ) : ℕ :=
  2852 * L ^ 2 + 3183 * L +
    maxPaths * (pathTreeBudget LinkCut.PathProg.pathC L n + 45) +
    maxEdges * (136 * maxEdges + 152 * L ^ 2 + 561 * L + drainUnit + 960) + 1400

/-- Total amortized step budget of `solverUpdateBody`. -/
@[expose] def updateBudgetBound (L d n intCap nextFresh batchLen N findBudget shiftBudget
    maxEdges maxPaths drainUnit refreshBudget : ℕ) : ℕ :=
  (if intCap < nextFresh + batchLen then 102 * intCap + 34 * (nextFresh + batchLen) + 270 else 50) +
    20 * L + 300 * batchLen + refreshBudget +
    (batchLen * (34 * L + 100) + 50) +
    (N + 1) * cycleLoopIterBudget L d findBudget shiftBudget +
    updateGoodBranchBudget L n maxEdges maxPaths drainUnit + 500

theorem readVector_congr {m₁ m₂ : ℕ → ℕ} {base h L P m : ℕ}
    (hag : ∀ a, base ≤ a → a < base + m * L → m₁ a = m₂ a) :
    readVector m₁ base h L P m = readVector m₂ base h L P m := by
  funext e
  unfold readVector
  split_ifs with he
  · unfold Num.fixVal Num.intVal
    congr 3
    suffices ∀ k a, (∀ j < k, m₁ (a + j) = m₂ (a + j)) →
        Num.unsignedVal m₁ a h k = Num.unsignedVal m₂ a h k from
      this L (base + e * L) fun j hj => hag (base + e * L + j) (by omega) (by
        have : e * L + L ≤ m * L := by
          have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt he)
          simpa [Nat.succ_mul] using this
        omega)
    intro k
    induction k with
    | zero => intro _ _; rfl
    | succ k ih =>
      intro a hEq
      simp only [Num.unsignedVal]
      rw [show m₁ a = m₂ a by simpa using hEq 0 (Nat.zero_lt_succ k),
        ih (a + 1) fun j hj => by simpa [Nat.add_assoc, Nat.add_comm 1] using hEq (j + 1) (by omega)]
  · rfl

theorem numValid_congr {m₁ m₂ : ℕ → ℕ} {a₁ a₂ h L : ℕ}
    (hV : Num.Valid m₁ a₁ h L) (hag : ∀ j < L, m₂ (a₂ + j) = m₁ (a₁ + j)) :
    Num.Valid m₂ a₂ h L := fun j hj => by rw [hag j hj]; exact hV j hj

theorem numIntVal_congr {m₁ m₂ : ℕ → ℕ} {a₁ a₂ h L : ℕ}
    (hag : ∀ j < L, m₂ (a₂ + j) = m₁ (a₁ + j)) :
    Num.intVal m₂ a₂ h L = Num.intVal m₁ a₁ h L := by
  unfold Num.intVal
  congr 1
  induction L generalizing a₁ a₂ with
  | zero => rfl
  | succ k ih =>
    simp only [Num.unsignedVal]
    rw [show m₂ a₂ = m₁ a₁ by simpa using hag 0 (Nat.zero_lt_succ k),
      ih (a₁ := a₁ + 1) (a₂ := a₂ + 1) fun j hj => by
        simpa [Nat.add_assoc, Nat.add_comm 1] using hag (j + 1) (by omega)]

/-- Helper: execution of the 11-statement `solverUpdatePrefix`. -/
private theorem solverUpdatePrefix_runs
    {w root batch g l eta heap pos handle L P d epsExp batchLen : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    (hw16 : 16 < 2 ^ w) (hH16W : handle + 16 < 2 ^ w)
    (hepsGe7 : 7 ≤ epsExp) (hepsW : epsExp < 2 ^ w)
    (hworkW : heap + 3 * L + d + 5 < 2 ^ w) (hcopyW : 4 * batchLen + 1 < 2 ^ w)
    (hmR0 : mem root = handle) (hmH5 : mem (handle + 5) = L) (hmH8 : mem (handle + 8) = P)
    (hmH11 : mem (handle + 11) = d)
    (hmH16 : mem (handle + 16) = epsExp) (hmB0 : mem batch = batchLen) :
    let descOut := heap + 1 + 2 * L
    let quotaBase := descOut + 2
    let zeroBlock := quotaBase + (d + 2)
    let workHeap0 := zeroBlock + L
    ∃ mid,
      Runs w p ω solverUpdatePrefix (startState [root, batch, g, l, eta, heap] mem pos) .normal mid 66 ∧
      mid.mem = mem ∧ mid.pos = pos ∧
      mid.regs 0 = root ∧ mid.regs 1 = batch ∧ mid.regs 2 = g ∧ mid.regs 3 = l ∧
      mid.regs 4 = eta ∧ mid.regs 5 = heap ∧
      mid.regs 6 = handle ∧ mid.regs 7 = L ∧ mid.regs 8 = P ∧ mid.regs 9 = d ∧
      mid.regs 11 = epsExp - 7 ∧ mid.regs 12 = batchLen ∧
      mid.regs 13 = descOut ∧ mid.regs 14 = quotaBase ∧ mid.regs 15 = zeroBlock ∧
      mid.regs 16 = workHeap0 ∧ mid.regs 18 = 4 * batchLen + 1 := by
  dsimp only
  let descOut := heap + 1 + 2 * L
  let quotaBase := descOut + 2
  let zeroBlock := quotaBase + (d + 2)
  let workHeap0 := zeroBlock + L
  let s0 := startState [root, batch, g, l, eta, heap] mem pos
  let s1 := { s0 with regs := Function.update s0.regs 6 handle }
  let s2 := { s1 with regs := Function.update s1.regs 7 L }
  let s3 := { s2 with regs := Function.update s2.regs 8 P }
  let s4 := { s3 with regs := Function.update s3.regs 9 d }
  let s6 := { s4 with regs := Function.update s4.regs 11 (epsExp - 7) }
  let s7 := { s6 with regs := Function.update s6.regs 12 batchLen }
  let s8 := { s7 with regs := Function.update s7.regs 13 descOut }
  let s9 := { s8 with regs := Function.update s8.regs 14 quotaBase }
  let s10 := { s9 with regs := Function.update s9.regs 15 zeroBlock }
  let s11 := { s10 with regs := Function.update s10.regs 16 workHeap0 }
  let s12 := { s11 with regs := Function.update s11.regs 18 (4 * batchLen + 1) }
  have r1 : Runs w p ω (.assign 6 (.load (.reg 0))) s0 .normal s1 3 :=
    runs_assign_iff.mpr ⟨handle, by simp [Expr.eval, s0, startState, hmR0], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 6) (.const 5)))) s1 .normal s2 5 :=
    runs_assign_iff.mpr ⟨L, by simp [Expr.eval, BinOp.eval, s1, s0, startState, show 5 < 2 ^ w by omega, show handle + 5 < 2 ^ w by omega, hmH5], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 6) (.const 8)))) s2 .normal s3 5 :=
    runs_assign_iff.mpr ⟨P, by simp [Expr.eval, BinOp.eval, s2, s1, s0, startState, show 8 < 2 ^ w by omega, show handle + 8 < 2 ^ w by omega, hmH8], rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 6) (.const 11)))) s3 .normal s4 5 :=
    runs_assign_iff.mpr ⟨d, by simp [Expr.eval, BinOp.eval, s3, s2, s1, s0, startState, show 11 < 2 ^ w by omega, show handle + 11 < 2 ^ w by omega, hmH11], rfl, rfl, rfl⟩
  have r6 : Runs w p ω (.assign 11 (.bin .sub (.load (.bin .add (.reg 6) (.const 16))) (.const 7))) s4 .normal s6 7 :=
    runs_assign_iff.mpr ⟨epsExp - 7, by
      simp [Expr.eval, BinOp.eval, s4, s3, s2, s1, s0, startState, hw16, hH16W, hmH16,
        show 7 < 2 ^ w by omega, show epsExp - 7 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have r7 : Runs w p ω (.assign 12 (.load (.reg 1))) s6 .normal s7 3 :=
    runs_assign_iff.mpr ⟨batchLen, by simp [Expr.eval, s6, s4, s3, s2, s1, s0, startState, hmB0], rfl, rfl, rfl⟩
  have r8 : Runs w p ω (.assign 13 (.bin .add (.bin .add (.reg 5) (.const 1)) (.bin .mul (.const 2) (.reg 7)))) s7 .normal s8 8 :=
    runs_assign_iff.mpr ⟨descOut, by
      simp [Expr.eval, BinOp.eval, s7, s6, s4, s3, s2, s1, s0, startState,
        show 1 < 2 ^ w by omega, show 2 < 2 ^ w by omega, show heap + 1 < 2 ^ w by omega,
        show 2 * L < 2 ^ w by omega, show descOut < 2 ^ w by dsimp only [descOut]; omega, descOut],
      rfl, rfl, rfl⟩
  have r9 : Runs w p ω (.assign 14 (.bin .add (.reg 13) (.const 2))) s8 .normal s9 4 :=
    runs_assign_iff.mpr ⟨quotaBase, by
      simp [Expr.eval, BinOp.eval, s8, show 2 < 2 ^ w by omega,
        show quotaBase < 2 ^ w by dsimp only [quotaBase, descOut]; omega, quotaBase],
      rfl, rfl, rfl⟩
  have r10 : Runs w p ω (.assign 15 (.bin .add (.reg 14) (.bin .add (.reg 9) (.const 2)))) s9 .normal s10 6 :=
    runs_assign_iff.mpr ⟨zeroBlock, by
      simp [Expr.eval, BinOp.eval, s9, s8, s7, s6, s4, show 2 < 2 ^ w by omega,
        show d + 2 < 2 ^ w by omega, show zeroBlock < 2 ^ w by dsimp only [zeroBlock, quotaBase, descOut]; omega, zeroBlock],
      rfl, rfl, rfl⟩
  have r11 : Runs w p ω (.assign 16 (.bin .add (.reg 15) (.reg 7))) s10 .normal s11 4 :=
    runs_assign_iff.mpr ⟨workHeap0, by
      simp [Expr.eval, BinOp.eval, s10, s9, s8, s7, s6, s4, s3, s2,
        show workHeap0 < 2 ^ w by dsimp only [workHeap0, zeroBlock, quotaBase, descOut]; omega, workHeap0],
      rfl, rfl, rfl⟩
  have r12 : Runs w p ω (.assign 18 (.bin .add (.bin .mul (.const 4) (.reg 12)) (.const 1))) s11 .normal s12 6 :=
    runs_assign_iff.mpr ⟨4 * batchLen + 1, by
      simp [Expr.eval, BinOp.eval, s11, s10, s9, s8, s7, show 4 < 2 ^ w by omega, show 1 < 2 ^ w by omega,
        show 4 * batchLen < 2 ^ w by omega, hcopyW],
      rfl, rfl, rfl⟩
  refine ⟨s12, ?_, rfl, rfl,
    by simp [s12, s11, s10, s9, s8, s7, s6, s4, s3, s2, s1, s0, startState],
    by simp [s12, s11, s10, s9, s8, s7, s6, s4, s3, s2, s1, s0, startState],
    by simp [s12, s11, s10, s9, s8, s7, s6, s4, s3, s2, s1, s0, startState],
    by simp [s12, s11, s10, s9, s8, s7, s6, s4, s3, s2, s1, s0, startState],
    by simp [s12, s11, s10, s9, s8, s7, s6, s4, s3, s2, s1, s0, startState],
    by simp [s12, s11, s10, s9, s8, s7, s6, s4, s3, s2, s1, s0, startState],
    by simp [s12, s11, s10, s9, s8, s7, s6, s4, s3, s2, s1],
    by simp [s12, s11, s10, s9, s8, s7, s6, s4, s3, s2],
    by simp [s12, s11, s10, s9, s8, s7, s6, s4, s3],
    by simp [s12, s11, s10, s9, s8, s7, s6, s4],
    by simp [s12, s11, s10, s9, s8, s7, s6],
    by simp [s12, s11, s10, s9, s8, s7],
    by simp [s12, s11, s10, s9, s8, descOut],
    by simp [s12, s11, s10, s9, quotaBase, descOut],
    by simp [s12, s11, s10, zeroBlock, quotaBase, descOut],
    by simp [s12, s11, workHeap0, zeroBlock, quotaBase, descOut],
    by simp [s12]⟩
  exact runs_seq_iff.mpr (Or.inr ⟨s1, 3, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 5, _, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 5, _, r3,
    runs_seq_iff.mpr (Or.inr ⟨s4, 5, _, r4,
    runs_seq_iff.mpr (Or.inr ⟨s6, 7, _, r6,
    runs_seq_iff.mpr (Or.inr ⟨s7, 3, _, r7,
    runs_seq_iff.mpr (Or.inr ⟨s8, 8, _, r8,
    runs_seq_iff.mpr (Or.inr ⟨s9, 4, _, r9,
    runs_seq_iff.mpr (Or.inr ⟨s10, 6, _, r10,
    runs_seq_iff.mpr (Or.inr ⟨s11, 4, 6, r11, r12, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)

set_option maxHeartbeats 1400000 in
/-- Execution of `solverUpdatePrepBody` (Steps 0–3 of `solverUpdateBody`): saves `eta`
and `batch`, copies the entries of `g` and `l` at the inserted edges to `gCopy` and
`gCopy + m * L`, grows internal tables, and runs `freshBatchEntry` on the translated batch. -/
theorem solverUpdatePrepBody_runs
    {w L P m V psi k epsExp drainUnit growTables copyWords freshBatch
      root batch g l eta heap pos : ℕ}
    {cfg : Alg2Config} {G : MGraph} {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} (hlocalCore : Rcore.Local)
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update}
    (hGrow : p.procs[growTables]? = some (growIntTablesBody copyWords))
    (hCopy : MeetsContract w p copyWords (copyWordsContract w))
    (hFresh : ∀ r G' H' f' g' next' U',
      MeetsContract w p freshBatch (freshBatchEntryContract w r G' H' f' g' next' U'))
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hextEq : model.extG = G)
    (hbatch0 : BatchAt mem batch U) (hwordsU : ∀ x ∈ batchWords U, x < 2 ^ w)
    (hRefreshU : RefreshBatch G U)
    (hbatchEnd : batch + (batchWords U).length ≤ heap)
    (hgEnd : g + m * L ≤ heap) (hlEnd : l + m * L ≤ heap)
    (hetaEnd : eta + L ≤ heap)
    (hbelow : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a → a < heap)
    (hz : ZeroFrom mem heap)
    (hmPos : 0 < m)
    (hcapPos : 0 < tok.intCap) (hnfLe : model.nextFresh ≤ tok.intCap)
    (hw16 : 16 < 2 ^ w) (hepsGe7 : 7 ≤ epsExp) (hepsW : epsExp < 2 ^ w)
    (hroom : heap + (4 * L + cfg.P.d + 5) + 12 * (model.nextFresh + U.length) +
      4 * (4 * U.length + 1) + 2 * (m * L) < 2 ^ w) :
    let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
    let descOut := heap + 1 + 2 * L
    let quotaBase := descOut + 2
    let zeroBlock := quotaBase + (cfg.P.d + 2)
    let etaCopy := zeroBlock + L
    let copyLen := 4 * U.length + 1
    let gCopy := etaCopy + L + 2 * copyLen
    let h0 := gCopy + 2 * (m * L)
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    ∃ out cPrep memC2 tokG h2 h3,
      Runs w p ω (solverUpdatePrepBody growTables copyWords freshBatch)
        (startState [root, batch, g, l, eta, heap] mem pos) .normal out cPrep ∧
      out.regs 0 = root ∧ out.regs 2 = g ∧ out.regs 3 = l ∧ out.regs 5 = heap ∧
      out.regs 7 = L ∧ out.regs 8 = P ∧ out.regs 9 = cfg.P.d ∧ out.regs 11 = epsExp - 7 ∧
      out.regs 13 = descOut ∧ out.regs 14 = quotaBase ∧ out.regs 15 = zeroBlock ∧
      out.regs 16 = h3 ∧ out.regs 18 = h2 ∧ out.regs 31 = etaCopy ∧
      out.regs 41 = gCopy ∧ out.regs 42 = gCopy + m * L ∧
      h0 + copyLen ≤ h2 ∧ h2 ≤ h3 ∧ h3 ≤ h0 + 12 * (model.nextFresh + U.length) + 2 * copyLen ∧
      Rrep.rep root model tokG memC2 ∧
      PreservesLevelMeta tok tokG mem memC2 ∧
      Rrep.phi root tokG memC2 = Rrep.phi root tok mem ∧
      (∀ e, (∃ u ∈ U, u.Inserts e) →
        readVector memC2 gCopy 4 L P m e = readVector mem g 4 L P m e ∧
        readVector memC2 (gCopy + m * L) 4 L P m e = readVector mem l 4 L P m e) ∧
      (∀ a < h2, tokG.tag a ≠ 6 → tokG.tag a ≠ 7 → tokG.tag a ≠ 8 → out.mem a = memC2 a) ∧
      FreshTablesAt out.mem tokG.forward tokG.inverse tokG.freshCounter m tokG.intCap
        tr.2.1 tr.2.2.1 tr.2.2.2.1 ∧
      BatchAt out.mem h2 tr.2.2.2.2 ∧
      DynSpanner.Program.SmallBatchAt out.mem h2 (model.chain.G 0) tr.2.2.2.2 (h3 - h2) ∧
      ZeroFrom out.mem h3 ∧
      (∀ a, Rrep.foot root tokG a → Rrep.foot root tok a ∨ (h0 ≤ a ∧ a < h2 - copyLen)) ∧
      (∀ j < L, out.mem (etaCopy + j) = mem (eta + j)) ∧
      (∀ a < etaCopy, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
      cPrep ≤ (if tok.intCap < model.nextFresh + U.length then
        102 * tok.intCap + 34 * (model.nextFresh + U.length) + 270 else 50) +
        17 * L + 298 * U.length + 260 + (U.length * (34 * L + 100) + 50) ∧
      tr.2.2.2.1 ≤ tokG.intCap ∧
      (tokG.intCap =
        (if tok.intCap < model.nextFresh + U.length then 2 * (model.nextFresh + U.length) else tok.intCap) ∧
        tokG.tree = tok.tree ∧ tokG.trees = tok.trees ∧
        (∀ e ∈ model.extG.E, memC2 (tokG.edgeRecords + model.extToInt e) =
          mem (tok.edgeRecords + model.extToInt e)) ∧
        (∀ e < m, (∃ u ∈ U, u.Inserts e) → ∀ j < L,
          memC2 (gCopy + e * L + j) = mem (g + e * L + j) ∧
          memC2 (gCopy + m * L + e * L + j) = mem (l + e * L + j))) := by
  dsimp only
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  have hlocR := solverStateRep_local cfg L P m V psi k epsExp drainUnit hlocalCore
  let descOut := heap + 1 + 2 * L
  let quotaBase := descOut + 2
  let zeroBlock := quotaBase + (cfg.P.d + 2)
  let etaCopy := zeroBlock + L
  let copyLen := 4 * U.length + 1
  let batchSave := etaCopy + L + copyLen
  let gCopy := batchSave + copyLen
  let h0 := gCopy + 2 * (m * L)
  have hh0Eq : h0 = etaCopy + L + 2 * copyLen + 2 * (m * L) := by
    dsimp only [h0, gCopy, batchSave]; omega
  have hheapW : heap < 2 ^ w := by omega
  have hworkW : heap + 3 * L + cfg.P.d + 5 < 2 ^ w := by omega
  have hcopyW : copyLen < 2 ^ w := by dsimp only [copyLen]; omega
  have hh0W : h0 < 2 ^ w := by dsimp only [h0, gCopy, batchSave, copyLen, etaCopy, zeroBlock, quotaBase, descOut]; omega
  have ⟨hrootDir, _, hnumH, hchainP, hfreshInv0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, htags0⟩ := hrep
  obtain ⟨hOwn0, _, t2, _⟩ := htags0
  have hltH0 {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) : a < heap :=
    hbelow a (Or.inl (hOwn0 a (ht ▸ hv)))
  have hmR0 : mem root = tok.handle := by simpa using hrootDir 0 (by simp [List.length])
  have hmH5 : mem (tok.handle + 5) = L := by simpa using hnumH 0 (by simp [List.length])
  have hmH8 : mem (tok.handle + 8) = P := by
    simpa [show tok.handle + 5 + 3 = tok.handle + 8 by omega] using hnumH 3 (by simp [List.length])
  have hmH11 : mem (tok.handle + 11) = cfg.P.d := by
    simpa [show tok.handle + 9 + 2 = tok.handle + 11 by omega] using hchainP 2 (by simp [List.length])
  have hmH16 : mem (tok.handle + 16) = epsExp := by
    simpa [show tok.handle + 9 + 7 = tok.handle + 16 by omega] using hchainP 7 (by simp [List.length])
  have hmB0 : mem batch = U.length := by simpa [batchWords] using hbatch0 0 (by simp [batchWords])
  have hH16W : tok.handle + 16 < 2 ^ w := lt_trans (hltH0 (t2 16 (by omega)) (by decide)) hheapW
  obtain ⟨mid0, hrPref, hm0Mem, hm0Pos, hm0r0, hm0r1, hm0r2, hm0r3, hm0r4, hm0r5,
      hm0r6, hm0r7, hm0r8, hm0r9, hm0r11, hm0r12, hm0r13, hm0r14, hm0r15, hm0r16, hm0r18⟩ :=
    solverUpdatePrefix_runs (w := w) (root := root) (batch := batch) (g := g) (l := l)
      (eta := eta) (heap := heap) (pos := pos) (handle := tok.handle) (L := L) (P := P)
      (d := cfg.P.d) (epsExp := epsExp) (batchLen := U.length) (p := p) (ω := ω)
      (mem := mem) hw16 hH16W hepsGe7 hepsW hworkW hcopyW hmR0 hmH5 hmH8 hmH11 hmH16 hmB0
  -- Copy `eta` -> `etaCopy` and `batch` -> `batchSave`
  let sA1 : State := { mid0 with regs := Function.update mid0.regs 31 etaCopy }
  have rA1 : Runs w p ω (.assign 31 (.reg 16)) mid0 .normal sA1 2 :=
    runs_assign_iff.mpr ⟨etaCopy, by simp [Expr.eval, hm0r16, etaCopy, zeroBlock, quotaBase, descOut], rfl, rfl, rfl⟩
  obtain ⟨bCE, hbCE, oCE, stCE, cCE, hrCE, ⟨_, _, _, hEqCE, _, hcpyE, hfrCE⟩, hcCE⟩ :=
    hCopy [eta, etaCopy, L] mem sA1.pos ω
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl <;>
            (try dsimp only [etaCopy, zeroBlock, quotaBase, descOut] at hh0W ⊢) <;> omega)
      ⟨eta, etaCopy, L, rfl, by omega, by omega, by dsimp only [etaCopy, zeroBlock, quotaBase, descOut] at hh0W ⊢; omega,
        Or.inr (by dsimp only [etaCopy, zeroBlock, quotaBase, descOut]; omega)⟩
  injection hEqCE with h1ce hrc1e; injection hrc1e with h2ce hrc2e; injection hrc2e with h3ce _
  subst h1ce; subst h2ce; subst h3ce
  change cCE ≤ 17 * L + 10 at hcCE
  let sA2 : State := { regs := Function.update sA1.regs 30 oCE.value, mem := stCE.mem, pos := stCE.pos }
  have rA2 : Runs w p ω (.call 30 copyWords [.reg 4, .reg 31, .reg 7]) sA1 .normal sA2 (cCE + 4) :=
    runs_call_iff.mpr ⟨[eta, etaCopy, L], bCE, oCE, stCE, cCE,
      by simp [evalArgs, Expr.eval, sA1, hm0r4, hm0r7], hbCE, by simpa [sA1, hm0Mem] using hrCE, rfl, rfl,
      by simp [argsSize, Expr.size]; omega⟩
  let sA3 : State := { sA2 with regs := Function.update sA2.regs 32 batchSave }
  have rA3 : Runs w p ω (.assign 32 (.bin .add (.bin .add (.reg 31) (.reg 7)) (.reg 18))) sA2 .normal sA3 6 :=
    runs_assign_iff.mpr ⟨batchSave, by
      simp [Expr.eval, BinOp.eval, sA2, sA1, hm0r7, hm0r18,
        show etaCopy + L < 2 ^ w by dsimp only [h0, batchSave] at hh0W; omega,
        show batchSave < 2 ^ w by dsimp only [h0] at hh0W; omega, batchSave, copyLen],
      rfl, rfl, rfl⟩
  have hbatchLeHeap : batch ≤ heap := by
    have : 1 ≤ (batchWords U).length := by simp [batchWords]
    omega
  obtain ⟨bCB, hbCB, oCB, stCB, cCB, hrCB, ⟨_, _, _, hEqCB, _, hcpyB, hfrCB⟩, hcCB⟩ :=
    hCopy [batch, batchSave, copyLen] stCE.mem sA3.pos ω
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl <;> dsimp only [h0] at hh0W <;> omega)
      ⟨batch, batchSave, copyLen, rfl, by omega, by omega, by dsimp only [h0] at hh0W; omega,
        Or.inr (by dsimp only [batchSave, etaCopy, zeroBlock, quotaBase, descOut]; omega)⟩
  injection hEqCB with h1cb hrc1b; injection hrc1b with h2cb hrc2b; injection hrc2b with h3cb _
  subst h1cb; subst h2cb; subst h3cb
  change cCB ≤ 17 * copyLen + 10 at hcCB
  let sA4 : State := { regs := Function.update sA3.regs 30 oCB.value, mem := stCB.mem, pos := stCB.pos }
  have rA4 : Runs w p ω (.call 30 copyWords [.reg 1, .reg 32, .reg 18]) sA3 .normal sA4 (cCB + 4) :=
    runs_call_iff.mpr ⟨[batch, batchSave, copyLen], bCB, oCB, stCB, cCB,
      by simp [evalArgs, Expr.eval, sA3, sA2, sA1, hm0r1, hm0r18, copyLen], hbCB, hrCB, rfl, rfl,
      by simp [argsSize, Expr.size]; omega⟩
  have hbatchWordsLe : (batchWords U).length ≤ copyLen := batchWords_length_le_of_refresh hRefreshU
  have hbatchAtSave0 : BatchAt stCB.mem batchSave U := fun j hj => by
    have hjC : j < copyLen := lt_of_lt_of_le hj hbatchWordsLe
    rw [hcpyB j hjC, hfrCE (batch + j) (Or.inl (by dsimp only [etaCopy, zeroBlock, quotaBase, descOut]; omega))]
    exact hbatch0 j hj
  have hfrCB_mem0 (a : ℕ) (ha : a < etaCopy) : stCB.mem a = mem a := by
    rw [hfrCB a (Or.inl (by dsimp only [batchSave]; omega)), hfrCE a (Or.inl ha)]
  -- Copy the entries of `g` and `l` at the inserted edges to `gCopy` and `gCopy + m * L`
  have hmH9 : mem (tok.handle + 9) = m := by simpa using hchainP 0 (by simp [List.length])
  have hedgeU : ∀ u ∈ U, Bundle.IsEdgeUpdate u := fun u hu => by
    have := hRefreshU.2.2 u hu
    cases u with
    | split _ _ _ _ => exact this.elim
    | delete _ => trivial
    | insert _ _ _ => trivial
  obtain ⟨sA5, cK, rA5, hKregs, hK16, hK41, hK42, hKfr, hKcp, hcK⟩ :=
    copyInsertedStmt_runs (w := w) (copyWords := copyWords) (handle := tok.handle) (m := m)
      (L := L) (g := g) (l := l) (bs := batchSave) (copyLen := copyLen) (p := p) (ω := ω)
      (st := sA4) (U := U) hCopy
      (by simp [sA4, sA3, sA2, sA1, hm0r2]) (by simp [sA4, sA3, sA2, sA1, hm0r3])
      (by simp [sA4, sA3, sA2, sA1, hm0r6]) (by simp [sA4, sA3, sA2, sA1, hm0r7])
      (by simp [sA4, sA3, sA2, sA1, hm0r12]) (by simp [sA4, sA3, sA2, sA1, hm0r18, copyLen])
      (by simp [sA4, sA3])
      (by rw [show sA4.mem = stCB.mem from rfl, hfrCB_mem0 _ (lt_trans (hltH0 (t2 9 (by omega)) (by decide))
            (by dsimp only [etaCopy, zeroBlock, quotaBase, descOut]; omega))]; exact hmH9)
      (lt_trans (hltH0 (t2 9 (by omega)) (by decide)) hheapW)
      hbatchAtSave0 hedgeU hwordsU hbatchWordsLe
      (by dsimp only [batchSave, etaCopy, zeroBlock, quotaBase, descOut]; omega)
      (by dsimp only [batchSave, etaCopy, zeroBlock, quotaBase, descOut]; omega)
      (by dsimp only [h0, gCopy] at hh0W; omega) (by omega)
  have hKr (r : ℕ) (h16 : r ≠ 16) (h30 : r ≠ 30) (h40 : r < 40) : sA5.regs r = sA4.regs r :=
    hKregs r h16 h30 h40
  have hK16' : sA5.regs 16 = h0 := by rw [hK16]; dsimp only [h0, gCopy]; omega
  have hfrK (a : ℕ) (ha : a < gCopy) : sA5.mem a = stCB.mem a := hKfr a (Or.inl ha)
  have hfrCB_mem (a : ℕ) (ha : a < etaCopy) : sA5.mem a = mem a := by
    rw [hfrK a (by dsimp only [gCopy, batchSave]; omega), hfrCB_mem0 a ha]
  have hag0CB (a : ℕ) (ha : Rrep.foot root tok a) : mem a = sA5.mem a :=
    (hfrCB_mem a (lt_of_lt_of_le (hbelow a ha) (by dsimp only [etaCopy, zeroBlock, quotaBase, descOut]; omega))).symm
  have hrepCB : Rrep.rep root model tok sA5.mem := (hlocR root model tok mem sA5.mem hag0CB).1 hrep
  have hphiCB : Rrep.phi root tok sA5.mem = Rrep.phi root tok mem := ((hlocR root model tok mem sA5.mem hag0CB).2).symm
  have hzH0 : ZeroFrom sA5.mem h0 := fun a ha => by
    have ha' : etaCopy + L + 2 * copyLen + 2 * (m * L) ≤ a := hh0Eq ▸ ha
    have e1 : batchSave + copyLen + m * L + m * L ≤ a := by dsimp only [batchSave]; omega
    have e2 : batchSave + copyLen ≤ a := by omega
    have e3 : etaCopy + L ≤ a := by omega
    have e4 : heap ≤ a := by dsimp only [etaCopy, zeroBlock, quotaBase, descOut] at e3; omega
    rw [hKfr a (Or.inr e1), hfrCB a (Or.inr e2), hfrCE a (Or.inr e3)]
    exact hz a e4
  have hetaCopyEq (j : ℕ) (hj : j < L) : sA5.mem (etaCopy + j) = mem (eta + j) := by
    have e1 : etaCopy + j < gCopy := by dsimp only [gCopy, batchSave]; omega
    have e2 : etaCopy + j < batchSave := by dsimp only [batchSave]; omega
    rw [hfrK (etaCopy + j) e1, hfrCB (etaCopy + j) (Or.inl e2)]
    exact hcpyE j hj
  have hbatchAtSave : BatchAt sA5.mem batchSave U := fun j hj => by
    have hjC : j < copyLen := lt_of_lt_of_le hj hbatchWordsLe
    rw [hfrK (batchSave + j) (by dsimp only [gCopy]; omega)]
    exact hbatchAtSave0 j hj
  have hKgl (e : ℕ) (he : ∃ u ∈ U, u.Inserts e) :
      readVector sA5.mem gCopy 4 L P m e = readVector mem g 4 L P m e ∧
      readVector sA5.mem (gCopy + m * L) 4 L P m e = readVector mem l 4 L P m e := by
    have hgm : g + m * L ≤ gCopy := by dsimp only [gCopy, batchSave, etaCopy, zeroBlock, quotaBase, descOut]; omega
    have hlm : l + m * L ≤ gCopy := by dsimp only [gCopy, batchSave, etaCopy, zeroBlock, quotaBase, descOut]; omega
    refine ⟨readVector_copyInserted fun hem j hj => ?_, readVector_copyInserted fun hem j hj => ?_⟩
    · have hb := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hem); rw [Nat.succ_mul] at hb
      rw [(hKcp e hem he j hj).1, show sA4.mem = stCB.mem from rfl, hfrCB_mem0 _ (by
        dsimp only [gCopy, batchSave, etaCopy, zeroBlock, quotaBase, descOut] at hgm ⊢; omega)]
    · have hb := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hem); rw [Nat.succ_mul] at hb
      rw [(hKcp e hem he j hj).2, show sA4.mem = stCB.mem from rfl, hfrCB_mem0 _ (by
        dsimp only [gCopy, batchSave, etaCopy, zeroBlock, quotaBase, descOut] at hlm ⊢; omega)]
  -- Call `growIntTablesBody`
  have hbelowH0 (a : ℕ) (ha : Rrep.foot root tok a) : a < h0 :=
    lt_of_lt_of_le (hbelow a ha) (by dsimp only [h0, gCopy, batchSave, etaCopy, zeroBlock, quotaBase, descOut]; omega)
  obtain ⟨h1, cG, stG, tokG, hrG, hcapG, hrepG, hpresG, hphiG, hcapGLe, htreeG, htreesG, hptrG, hzG,
      hh1Lo, hh1Hi, hfrG, hftG, hcG⟩ :=
    growIntTablesBody_runs (w := w) (L := L) (P := P) (m := m) (V := V) (psi := psi) (k := k)
      (epsExp := epsExp) (drainUnit := drainUnit) (copyWords := copyWords) (root := root)
      (batchLen := U.length) (heap := h0) (pos := sA5.pos) hlocalCore hCopy hrepCB hbelowH0
      hzH0 hcapPos hnfLe (by omega)
      (by dsimp only [h0, gCopy, batchSave, copyLen, etaCopy, zeroBlock, quotaBase, descOut]; omega)
  let s1 : State := { regs := Function.update sA5.regs 16 h1, mem := stG.mem, pos := stG.pos }
  have rCallG : Runs w p ω (.call 16 growTables [.reg 0, .reg 12, .reg 16]) sA5 .normal s1 (cG + 4) :=
    runs_call_iff.mpr ⟨[root, U.length, h0], growIntTablesBody copyWords, .returned h1, stG, cG,
      by simp [evalArgs, Expr.eval, hKr, hK16', sA4, sA3, sA2, sA1, hm0r0, hm0r12], hGrow, hrG, rfl, rfl,
      by simp [argsSize, Expr.size]; omega⟩
  -- Copy `batchSave` -> `h1`
  let h2 := h1 + copyLen
  have hh2W : h2 < 2 ^ w := by
    dsimp only [h2, copyLen, h0, gCopy, batchSave, etaCopy, zeroBlock, quotaBase, descOut] at hh1Hi ⊢; omega
  let s2 : State := { s1 with regs := Function.update s1.regs 17 h1 }
  have rSetBC : Runs w p ω (.assign 17 (.reg 16)) s1 .normal s2 2 :=
    runs_assign_iff.mpr ⟨h1, by simp [Expr.eval, s1], rfl, rfl, rfl⟩
  obtain ⟨bC2, hbC2, oC2, stC2, cC2, hrC2, ⟨_, _, _, hEqC2, _, hcpy2, hfrC2⟩, hcC2⟩ :=
    hCopy [batchSave, h1, copyLen] stG.mem s2.pos ω
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl <;> dsimp only [h2, h0, gCopy] at hh2W hh0W <;> omega)
      ⟨batchSave, h1, copyLen, rfl, by omega, by dsimp only [h0, gCopy] at hh0W; omega, by dsimp only [h2] at hh2W; omega,
        Or.inr (by dsimp only [h0, gCopy] at hh1Lo; omega)⟩
  injection hEqC2 with h1c2 hrc1c2; injection hrc1c2 with h2c2 hrc2c2; injection hrc2c2 with h3c2 _
  subst h1c2; subst h2c2; subst h3c2
  change cC2 ≤ 17 * copyLen + 10 at hcC2
  let s3 : State := { regs := Function.update s2.regs 30 oC2.value, mem := stC2.mem, pos := stC2.pos }
  have rCallC2 : Runs w p ω (.call 30 copyWords [.reg 32, .reg 17, .reg 18]) s2 .normal s3 (cC2 + 4) :=
    runs_call_iff.mpr ⟨[batchSave, h1, copyLen], bC2, oC2, stC2, cC2,
      by simp [evalArgs, Expr.eval, s2, s1, hKr, hK16', sA4, sA3, sA2, sA1, hm0r18, copyLen], hbC2, hrC2, rfl, rfl,
      by simp [argsSize, Expr.size]; omega⟩
  let s4 : State := { s3 with regs := Function.update s3.regs 16 h2 }
  have rSetH2 : Runs w p ω (.assign 16 (.bin .add (.reg 17) (.reg 18))) s3 .normal s4 4 :=
    runs_assign_iff.mpr ⟨h2, by
      simp [Expr.eval, BinOp.eval, s3, s2, s1, hKr, hK16', sA4, sA3, sA2, sA1, hm0r18, hh2W, h2, copyLen],
      rfl, rfl, rfl⟩
  have hfootG_lt (a : ℕ) (ha : Rrep.foot root tokG a) : a < h1 := by
    rcases hftG a ha with h0' | ⟨_, hhi⟩
    · exact lt_of_lt_of_le (hbelowH0 a h0') hh1Lo
    · exact hhi
  have hagGC2 (a : ℕ) (ha : Rrep.foot root tokG a) : stG.mem a = stC2.mem a :=
    (hfrC2 a (Or.inl (hfootG_lt a ha))).symm
  have hrepC2 : Rrep.rep root model tokG stC2.mem := (hlocR root model tokG stG.mem stC2.mem hagGC2).1 hrepG
  have hphiC2 : Rrep.phi root tokG stC2.mem = Rrep.phi root tokG stG.mem :=
    ((hlocR root model tokG stG.mem stC2.mem hagGC2).2).symm
  have hbatchAtH1 : BatchAt stC2.mem h1 U := fun j hj => by
    have hjC : j < copyLen := lt_of_lt_of_le hj hbatchWordsLe
    rw [hcpy2 j hjC, hfrG (batchSave + j) (by dsimp only [h0, gCopy]; omega)
      (fun hf => by have := hbelow _ hf; dsimp only [batchSave, etaCopy, zeroBlock, quotaBase, descOut] at this; omega)]
    exact hbatchAtSave j hj
  have hzH2 : ZeroFrom stC2.mem h2 := fun a ha => by
    rw [hfrC2 a (Or.inr ha)]; exact hzG a (by dsimp only [h2] at ha; omega)
  -- Reload `forward`, `inverse`, `freshCounter` and call `freshBatchEntry`
  have ⟨hrootDirC2, _, _, _, _, hfreshTabC2, hextMC2, _, _, _, _, _, _, _, _, _, _, _, _, htagsC2⟩ := hrepC2
  obtain ⟨hOwnC2, t1C2, _, _, _, _, t6C2, t7C2, t8C2, _⟩ := htagsC2
  have hltH1 {a v : ℕ} (ht : tokG.tag a = v) (hv : v ≠ 0) : a < h1 :=
    hfootG_lt a (Or.inl (hOwnC2 a (ht ▸ hv)))
  have hmC2_3 : stC2.mem (root + 3) = tokG.forward := by simpa using hrootDirC2 3 (by simp [List.length])
  have hmC2_4 : stC2.mem (root + 4) = tokG.inverse := by simpa using hrootDirC2 4 (by simp [List.length])
  have hmC2_5 : stC2.mem (root + 5) = tokG.freshCounter := by simpa using hrootDirC2 5 (by simp [List.length])
  let s5 : State := { s4 with regs := Function.update s4.regs 19 tokG.forward }
  let s6 : State := { s5 with regs := Function.update s5.regs 20 tokG.inverse }
  let s7 : State := { s6 with regs := Function.update s6.regs 21 tokG.freshCounter }
  let s8 : State := { s7 with regs := Function.update s7.regs 18 h2 }
  have rLoad3 : Runs w p ω (.assign 19 (.load (.bin .add (.reg 0) (.const 3)))) s4 .normal s5 5 :=
    runs_assign_iff.mpr ⟨tokG.forward, by
      have hW : root + 3 < 2 ^ w := lt_trans (hltH1 (t1C2 3 (by omega)) (by decide)) (by dsimp only [h2] at hh2W; omega)
      simp [Expr.eval, BinOp.eval, s4, s3, s2, s1, hKr, hK16', sA4, sA3, sA2, sA1, hm0r0, show 3 < 2 ^ w by omega, hW, hmC2_3],
      rfl, rfl, rfl⟩
  have rLoad4 : Runs w p ω (.assign 20 (.load (.bin .add (.reg 0) (.const 4)))) s5 .normal s6 5 :=
    runs_assign_iff.mpr ⟨tokG.inverse, by
      have hW : root + 4 < 2 ^ w := lt_trans (hltH1 (t1C2 4 (by omega)) (by decide)) (by dsimp only [h2] at hh2W; omega)
      simp [Expr.eval, BinOp.eval, s5, s4, s3, s2, s1, hKr, hK16', sA4, sA3, sA2, sA1, hm0r0, show 4 < 2 ^ w by omega, hW, hmC2_4],
      rfl, rfl, rfl⟩
  have rLoad5 : Runs w p ω (.assign 21 (.load (.bin .add (.reg 0) (.const 5)))) s6 .normal s7 5 :=
    runs_assign_iff.mpr ⟨tokG.freshCounter, by
      have hW : root + 5 < 2 ^ w := lt_trans (hltH1 (t1C2 5 (by omega)) (by decide)) (by dsimp only [h2] at hh2W; omega)
      simp [Expr.eval, BinOp.eval, s6, s5, s4, s3, s2, s1, hKr, hK16', sA4, sA3, sA2, sA1, hm0r0, show 5 < 2 ^ w by omega, hW, hmC2_5],
      rfl, rfl, rfl⟩
  have rSetUInt : Runs w p ω (.assign 18 (.reg 16)) s7 .normal s8 2 :=
    runs_assign_iff.mpr ⟨h2, by simp [Expr.eval, s7, s6, s5, s4], rfl, rfl, rfl⟩
  let rFresh : FreshBatchRegions :=
    { forward := tokG.forward, inverse := tokG.inverse, counter := tokG.freshCounter,
      externalCap := m, internalCap := tokG.intCap, input := h1 + 1, output := h2 + 1 }
  have hsepF : rFresh.Separated := freshBatchRegions_separated_of_solver hrepC2 hfootG_lt hmPos (by omega)
  have hpreF : (freshBatchEntryContract w rFresh model.extG (model.chain.G 0)
      model.extToInt model.intToExt model.nextFresh U).pre
      [h1, tokG.forward, tokG.inverse, tokG.freshCounter, h2] stC2.mem :=
    freshBatchEntry_pre_of_refresh rfl rfl hsepF hfreshInv0 hfreshTabC2
      (hextEq ▸ hRefreshU) hextMC2 hbatchAtH1 hwordsU hcapG (by dsimp only [h2]; omega)
      (by dsimp only [h2, copyLen, h0, gCopy, batchSave, etaCopy, zeroBlock, quotaBase, descOut] at hh1Hi ⊢; omega) hzH2
  obtain ⟨bF, hbF, oF, stF, cF, hrF, hpostF, hcF⟩ :=
    hFresh rFresh model.extG (model.chain.G 0) model.extToInt model.intToExt model.nextFresh U
      [h1, tokG.forward, tokG.inverse, tokG.freshCounter, h2] stC2.mem s8.pos ω
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl
          · dsimp only [h2] at hh2W; omega
          · have h1' := hsepF.1; dsimp only [rFresh] at h1'; dsimp only [h2, copyLen] at hh2W; omega
          · have h1' := hsepF.2.1; dsimp only [rFresh] at h1'; dsimp only [h2, copyLen] at hh2W; omega
          · have h1' := hsepF.2.2.1; dsimp only [rFresh] at h1'; dsimp only [h2, copyLen] at hh2W; omega
          · exact hh2W)
      hpreF
  change cF ≤ 162 * U.length + 32 at hcF
  let h3 := oF.value
  have hsmallF := freshBatchEntry_compact (refreshBatch_recordFits (hextEq ▸ hRefreshU) hextMC2) hpostF
  obtain ⟨hbatchInt, hfreshTabF, hh3Eq, hzF, hfrF⟩ := hpostF
  have hh3Bound : h3 ≤ h2 + copyLen := by
    change h3 = h2 + (batchWords (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2).length at hh3Eq
    rw [hh3Eq, translateBatch_refresh_words_length U (refreshBatch_recordFits (hextEq ▸ hRefreshU) hextMC2)]
    omega
  have hh3GeH2 : h2 ≤ h3 := by change h3 = h2 + _ at hh3Eq; omega
  let s9 : State := { regs := Function.update s8.regs 16 h3, mem := stF.mem, pos := stF.pos }
  have rCallF : Runs w p ω (.call 16 freshBatch [.reg 17, .reg 19, .reg 20, .reg 21, .reg 18]) s8 .normal s9 (cF + 6) :=
    runs_call_iff.mpr ⟨[h1, tokG.forward, tokG.inverse, tokG.freshCounter, h2], bF, oF, stF, cF,
      by simp [evalArgs, Expr.eval, s8, s7, s6, s5, s4, s3, s2], hbF, hrF, rfl, rfl,
      by simp [argsSize, Expr.size]; omega⟩
  have hrFull : Runs w p ω (solverUpdatePrepBody growTables copyWords freshBatch)
      (startState [root, batch, g, l, eta, heap] mem pos) .normal s9
      (66 + (2 + ((cCE + 4) + (6 + ((cCB + 4) + (cK + ((cG + 4) + (2 + ((cC2 + 4) + (4 + (5 + (5 + (5 + (2 + (cF + 6) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨mid0, 66, _, hrPref,
    runs_seq_iff.mpr (Or.inr ⟨sA1, 2, _, rA1,
    runs_seq_iff.mpr (Or.inr ⟨sA2, cCE + 4, _, rA2,
    runs_seq_iff.mpr (Or.inr ⟨sA3, 6, _, rA3,
    runs_seq_iff.mpr (Or.inr ⟨sA4, cCB + 4, _, rA4,
    runs_seq_iff.mpr (Or.inr ⟨sA5, cK, _, rA5,
    runs_seq_iff.mpr (Or.inr ⟨s1, cG + 4, _, rCallG,
    runs_seq_iff.mpr (Or.inr ⟨s2, 2, _, rSetBC,
    runs_seq_iff.mpr (Or.inr ⟨s3, cC2 + 4, _, rCallC2,
    runs_seq_iff.mpr (Or.inr ⟨s4, 4, _, rSetH2,
    runs_seq_iff.mpr (Or.inr ⟨s5, 5, _, rLoad3,
    runs_seq_iff.mpr (Or.inr ⟨s6, 5, _, rLoad4,
    runs_seq_iff.mpr (Or.inr ⟨s7, 5, _, rLoad5,
    runs_seq_iff.mpr (Or.inr ⟨s8, 2, cF + 6, rSetUInt, rCallF, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hfrF_tags (a : ℕ) (ha : a < h2) (h6 : tokG.tag a ≠ 6) (h7 : tokG.tag a ≠ 7) (h8 : tokG.tag a ≠ 8) :
      stF.mem a = stC2.mem a := hfrF a ha (by
    rintro (rfl | ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩)
    · exact h6 t6C2
    · dsimp only [rFresh] at hlo hhi
      have := t7C2 (a - tokG.forward) (by omega); rw [Nat.add_sub_of_le hlo] at this; exact h7 this
    · dsimp only [rFresh] at hlo hhi
      have := t8C2 (a - tokG.inverse) (by omega); rw [Nat.add_sub_of_le hlo] at this; exact h8 this)
  have hfrF_notFoot (a : ℕ) (ha : a < h0) (hnf : ¬ Rrep.foot root tok a) : stF.mem a = sA5.mem a := by
    have hnfG : ¬ Rrep.foot root tokG a := fun hf => by
      rcases hftG a hf with h' | ⟨hlo, _⟩
      · exact hnf h'
      · omega
    have h1' := hfrF_tags a (by dsimp only [h2]; omega)
      (fun h => hnfG (Or.inl (hOwnC2 a (by rw [h]; decide))))
      (fun h => hnfG (Or.inl (hOwnC2 a (by rw [h]; decide))))
      (fun h => hnfG (Or.inl (hOwnC2 a (by rw [h]; decide))))
    exact h1'.trans ((hfrC2 a (Or.inl (by omega))).trans (hfrG a ha hnf))
  have hC2K (a : ℕ) (ha1 : gCopy ≤ a) (ha2 : a < h0) : stC2.mem a = sA5.mem a := by
    have hnf : ¬ Rrep.foot root tok a := fun hf => by
      have := hbelow a hf
      dsimp only [gCopy, batchSave, etaCopy, zeroBlock, quotaBase, descOut] at ha1
      omega
    rw [hfrC2 a (Or.inl (by omega)), hfrG a ha2 hnf]
  have hgVecEq (e : ℕ) (he : ∃ u ∈ U, u.Inserts e) :
      readVector stC2.mem gCopy 4 L P m e = readVector mem g 4 L P m e ∧
      readVector stC2.mem (gCopy + m * L) 4 L P m e = readVector mem l 4 L P m e := by
    have hgle : gCopy + m * L ≤ h0 := by dsimp only [h0]; omega
    have hlle : gCopy + m * L + m * L ≤ h0 := by dsimp only [h0]; omega
    have hg1 : readVector stC2.mem gCopy 4 L P m = readVector sA5.mem gCopy 4 L P m :=
      readVector_congr fun a ha1 ha2 => hC2K a ha1 (lt_of_lt_of_le ha2 hgle)
    have hl1 : readVector stC2.mem (gCopy + m * L) 4 L P m =
        readVector sA5.mem (gCopy + m * L) 4 L P m :=
      readVector_congr fun a ha1 ha2 => hC2K a (le_trans (Nat.le_add_right _ _) ha1)
        (lt_of_lt_of_le ha2 hlle)
    rw [hg1, hl1]
    exact hKgl e he
  have hPresMetaC2 : PreservesLevelMeta tok tokG mem stC2.mem := by
    have hPres0 : PreservesLevelMeta tok tok mem sA5.mem :=
      ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ ha => ha, fun a ht =>
        ⟨rfl, hfrCB_mem a (lt_of_lt_of_le (hbelow a (LevelMetaFoot.mem_foot hrep ht))
          (by dsimp only [etaCopy, zeroBlock, quotaBase, descOut]; omega))⟩⟩
    exact (hPres0.trans hpresG).congr_mem_right fun a ht => by
      have hltH1 : a < h1 := by
        rcases hftG a (LevelMetaFoot.mem_foot hrepG ht) with h0 | ⟨_, hhi⟩
        · exact lt_of_lt_of_le (hbelowH0 a h0) hh1Lo
        · exact hhi
      exact hfrC2 a (Or.inl hltH1)
  refine ⟨s9, _, stC2.mem, tokG, h2, h3, hrFull,
    by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, hKr, hK16', sA4, sA3, sA2, sA1, hm0r0],
    by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, hKr, hK16', sA4, sA3, sA2, sA1, hm0r2],
    by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, hKr, hK16', sA4, sA3, sA2, sA1, hm0r3],
    by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, hKr, hK16', sA4, sA3, sA2, sA1, hm0r5],
    by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, hKr, hK16', sA4, sA3, sA2, sA1, hm0r7],
    by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, hKr, hK16', sA4, sA3, sA2, sA1, hm0r8],
    by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, hKr, hK16', sA4, sA3, sA2, sA1, hm0r9],
    by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, hKr, hK16', sA4, sA3, sA2, sA1, hm0r11],
    by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, hKr, hK16', sA4, sA3, sA2, sA1, hm0r13],
    by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, hKr, hK16', sA4, sA3, sA2, sA1, hm0r14],
    by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, hKr, hK16', sA4, sA3, sA2, sA1, hm0r15],
    by simp [s9], by simp [s9, s8],
    by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, hKr, hK16', sA4, sA3, sA2, sA1, etaCopy, zeroBlock, quotaBase, descOut],
    by
      have h41 : sA5.regs 41 = etaCopy + L + 2 * copyLen := by rw [hK41]; dsimp only [batchSave]; omega
      simpa [s9, s8, s7, s6, s5, s4, s3, s2, s1] using h41,
    by
      have h42 : sA5.regs 42 = etaCopy + L + 2 * copyLen + m * L := by
        rw [hK42]; dsimp only [batchSave]; omega
      simpa [s9, s8, s7, s6, s5, s4, s3, s2, s1] using h42,
    by dsimp only [h2]; omega, hh3GeH2,
    by dsimp only [h2] at hh3Bound; omega,
    hrepC2, hPresMetaC2, hphiC2.trans (hphiG.trans hphiCB),
    by
      have hgc : gCopy = etaCopy + L + 2 * copyLen := by dsimp only [gCopy, batchSave]; omega
      rw [hgc] at hgVecEq
      exact hgVecEq,
    hfrF_tags, hfreshTabF, hbatchInt, hsmallF, hzF,
    fun a ha => (hftG a ha).imp_right (fun ⟨h1', h2'⟩ => ⟨by omega, by dsimp only [h2]; omega⟩),
    fun j hj => by
      have hnf : ¬ Rrep.foot root tok (etaCopy + j) := fun hf =>
        absurd (hbelow _ hf) (by dsimp only [etaCopy, zeroBlock, quotaBase, descOut]; omega)
      exact (hfrF_notFoot (etaCopy + j) (by dsimp only [h0, gCopy, batchSave]; omega) hnf).trans (hetaCopyEq j hj),
    fun a ha hnf => (hfrF_notFoot a (by dsimp only [h0, gCopy, batchSave]; omega) hnf).trans (hfrCB_mem a ha),
    ?_, (translateBatch_nextFresh_bounds U _ _ _ _).2.trans hcapG,
    ⟨hcapGLe, htreeG, htreesG, fun e he => ?_, fun e hem he j hj => ?_⟩⟩
  rotate_left
  · rw [← hagGC2 _ (solverStateRep_recPtr_foot hrepG he),
      hptrG _ (solverStateRep_extToInt_lt hrep he)]
    exact (hag0CB _ (solverStateRep_recPtr_foot hrep he)).symm
  · have hgc : gCopy = etaCopy + L + 2 * copyLen := by dsimp only [gCopy, batchSave]; omega
    have hb := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hem); rw [Nat.succ_mul] at hb
    have hgm : g + m * L ≤ etaCopy := by dsimp only [etaCopy, zeroBlock, quotaBase, descOut]; omega
    have hlm : l + m * L ≤ etaCopy := by dsimp only [etaCopy, zeroBlock, quotaBase, descOut]; omega
    rw [← hgc]
    refine ⟨?_, ?_⟩
    · rw [hC2K (gCopy + e * L + j) (by omega) (by dsimp only [h0]; omega),
        (hKcp e hem he j hj).1, show sA4.mem = stCB.mem from rfl, hfrCB_mem0 _ (by omega)]
    · rw [hC2K (gCopy + m * L + e * L + j) (by omega) (by dsimp only [h0]; omega),
        (hKcp e hem he j hj).2, show sA4.mem = stCB.mem from rfl, hfrCB_mem0 _ (by omega)]
  dsimp only [copyLen] at hcCB hcC2 ⊢
  split_ifs at hcG ⊢ <;> omega

end MinCostFlow.MinRatio
