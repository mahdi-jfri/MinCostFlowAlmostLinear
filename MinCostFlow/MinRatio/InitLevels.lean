module

public import MinCostFlow.MinRatio.RebuildSuffix
import MinCostFlow.MinRatio.RebuildModelSuffix
import MinCostFlow.MinRatio.ShiftForestScan

/-!
# Root inputs to level construction

Start the rebuild suffix at level zero using the packed solver graph and
the cursor after allocating the shared header.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain

/-- Supply the packed root graph and fresh heap to the Rebuild suffix,
starting at level zero as in Algorithm 1 (page 20). -/
@[expose] def stageSolverInitLevels : Stmt :=
  .assign 4 (.reg 77) ;;
  .assign 6 (.reg 69) ;;
  .assign 7 (.reg 71) ;;
  .assign 8 (.reg 70) ;;
  .assign 20 (.const 0) ;;
  .assign 21 (.reg 75)

/-- The initial Rebuild starts at zero and stops at the saved depth. -/
theorem stageSolverInitLevels_runs {w heap graph lengths gradient depth : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hh : st.regs 77 = heap) (hg : st.regs 69 = graph) (hl : st.regs 71 = lengths)
    (hc : st.regs 70 = gradient) (hd : st.regs 75 = depth) :
    ∃ out, Runs w p ω stageSolverInitLevels st .normal out 17 ∧
      out.regs 4 = heap ∧ out.regs 6 = graph ∧ out.regs 7 = lengths ∧
      out.regs 8 = gradient ∧ out.regs 20 = 0 ∧ out.regs 21 = depth ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 4 → r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 20 → r ≠ 21 → out.regs r = st.regs r) := by
  let s1 := {st with regs := Function.update st.regs 4 heap}
  let s2 := {s1 with regs := Function.update s1.regs 6 graph}
  let s3 := {s2 with regs := Function.update s2.regs 7 lengths}
  let s4 := {s3 with regs := Function.update s3.regs 8 gradient}
  let s5 := {s4 with regs := Function.update s4.regs 20 0}
  let s6 := {s5 with regs := Function.update s5.regs 21 depth}
  have hr1 : Runs w p ω (.assign 4 (.reg 77)) st .normal s1 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hh], rfl, rfl, rfl⟩
  have hr2 : Runs w p ω (.assign 6 (.reg 69)) s1 .normal s2 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s1, hg], rfl, rfl, rfl⟩
  have hr3 : Runs w p ω (.assign 7 (.reg 71)) s2 .normal s3 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s2, s1, hl], rfl, rfl, rfl⟩
  have hr4 : Runs w p ω (.assign 8 (.reg 70)) s3 .normal s4 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s3, s2, s1, hc], rfl, rfl, rfl⟩
  have hr5 : Runs w p ω (.assign 20 (.const 0)) s4 .normal s5 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval], rfl, rfl, rfl⟩
  have hr6 : Runs w p ω (.assign 21 (.reg 75)) s5 .normal s6 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s5, s4, s3, s2, s1, hd], rfl, rfl, rfl⟩
  refine ⟨s6, runs_seq_iff.mpr (Or.inr ⟨s1, 2, 14, hr1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 2, 11, hr2,
      runs_seq_iff.mpr (Or.inr ⟨s3, 2, 8, hr3,
      runs_seq_iff.mpr (Or.inr ⟨s4, 2, 5, hr4,
      runs_seq_iff.mpr (Or.inr ⟨s5, 2, 2, hr5,
      hr6, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), ?_⟩
  refine ⟨by simp [s6, s5, s4, s3, s2, s1], by simp [s6, s5, s4, s3, s2, s1],
    by simp [s6, s5, s4, s3, s2, s1], by simp [s6, s5, s4, s3, s2, s1],
    by simp [s6, s5, s4, s3, s2, s1], by simp [s6], rfl, ?_⟩
  intro r h4 h6 h7 h8 h20 h21
  simp [s6, s5, s4, s3, s2, s1, Function.update_of_ne, h4, h6, h7, h8, h20, h21]

/-- Reserve disjoint handle and branch tables for levels zero through
the terminal level before constructing the root. -/
@[expose] def reserveSolverInitLevelTables : Stmt :=
  .assign 51 (.reg 77) ;;
  .assign 52 (.bin .add (.reg 51) (.bin .add (.reg 75) (.const 1))) ;;
  .assign 77 (.bin .add (.reg 52) (.bin .add (.reg 75) (.const 1)))

/-- The reserved tables are zero, and the new cursor is beyond both. -/
theorem reserveSolverInitLevelTables_runs {w heap depth : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hh : st.regs 77 = heap) (hd : st.regs 75 = depth)
    (hz : ZeroFrom st.mem heap) (hroom : heap + (depth + 1) + (depth + 1) < 2 ^ w) :
    ∃ out, Runs w p ω reserveSolverInitLevelTables st .normal out 16 ∧
      out.regs 51 = heap ∧ out.regs 52 = heap + (depth + 1) ∧
      out.regs 77 = heap + (depth + 1) + (depth + 1) ∧ ZeroFrom out.mem heap ∧
      out.mem = st.mem ∧ (∀ r, r ≠ 51 → r ≠ 52 → r ≠ 77 → out.regs r = st.regs r) := by
  let s1 := {st with regs := Function.update st.regs 51 heap}
  let s2 := {s1 with regs := Function.update s1.regs 52 (heap + (depth + 1))}
  let out := {s2 with regs := Function.update s2.regs 77 (heap + (depth + 1) + (depth + 1))}
  have hfits : depth + 1 < 2 ^ w := by omega
  have hmid : heap + (depth + 1) < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have hr₁ : Runs w p ω (.assign 51 (.reg 77)) st .normal s1 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hh], rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω
      (.assign 52 (.bin .add (.reg 51) (.bin .add (.reg 75) (.const 1)))) s1 .normal s2 6 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, s1, hd, hfits, hmid, hone], rfl, rfl, rfl⟩
  have hr₃ : Runs w p ω
      (.assign 77 (.bin .add (.reg 52) (.bin .add (.reg 75) (.const 1)))) s2 .normal out 6 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, s2, s1, hd, hfits, hroom, hone], rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨s1, 2, 13, hr₁,
      runs_seq_iff.mpr (Or.inr ⟨s2, 6, 6, hr₂, hr₃, rfl⟩), rfl⟩),
    by simp [out, s2, s1], by simp [out, s2], by simp [out], hz, rfl,
    fun r h51 h52 h77 => by simp [out, s2, s1, Function.update_of_ne, h51, h52, h77]⟩

/-- Reserve both chain tables and prepare the root arguments for Rebuild. -/
@[expose] def prepareSolverInitLevels : Stmt :=
  reserveSolverInitLevelTables ;; stageSolverInitLevels

/-- The first Rebuild receives disjoint tables and a free heap beyond both. -/
theorem prepareSolverInitLevels_runs {w heap graph lengths gradient depth : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hh : st.regs 77 = heap) (hd : st.regs 75 = depth)
    (hg : st.regs 69 = graph) (hl : st.regs 71 = lengths) (hc : st.regs 70 = gradient)
    (hz : ZeroFrom st.mem heap) (hroom : heap + (depth + 1) + (depth + 1) < 2 ^ w) :
    ∃ out, Runs w p ω prepareSolverInitLevels st .normal out 34 ∧
      out.regs 51 = heap ∧ out.regs 52 = heap + (depth + 1) ∧
      out.regs 4 = heap + (depth + 1) + (depth + 1) ∧
      out.regs 6 = graph ∧ out.regs 7 = lengths ∧ out.regs 8 = gradient ∧
      out.regs 20 = 0 ∧ out.regs 21 = depth ∧ out.mem = st.mem ∧ ZeroFrom out.mem heap ∧
      out.regs 67 = st.regs 67 ∧ out.regs 68 = st.regs 68 := by
  obtain ⟨mid, hr₁, h51, h52, h77, hz', hmem, hk⟩ :=
    reserveSolverInitLevelTables_runs (w := w) (p := p) (ω := ω) hh hd hz hroom
  have keep (r : ℕ) (h51 : r ≠ 51 := by decide) (h52 : r ≠ 52 := by decide)
      (h77 : r ≠ 77 := by decide) := hk r h51 h52 h77
  obtain ⟨out, hr₂, h4, h6, h7, h8, h20, h21, hm, hk'⟩ :=
    stageSolverInitLevels_runs (w := w) (p := p) (ω := ω) h77
      ((keep 69).trans hg) ((keep 71).trans hl) ((keep 70).trans hc) ((keep 75).trans hd)
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 16, 17, hr₁, hr₂, rfl⟩),
    (hk' 51 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h51,
    (hk' 52 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h52,
    h4, h6, h7, h8, h20, h21, hm.trans hmem, hm.symm ▸ hz',
    (hk' 67 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (keep 67),
    (hk' 68 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (keep 68)⟩

/-- Build the initial levels by running the Algorithm 1 (page 20)
rebuild suffix from the root. -/
@[expose] def buildSolverInitLevels (init read forestOp copy sort cell terminalInit : ℕ) : Stmt :=
  prepareSolverInitLevels ;; rebuildChainSuffix init read forestOp copy sort cell terminalInit

/-- Enter the rebuild invariant with the packed graph and the fresh
cursor, and account for each level and the terminal tool. -/
theorem buildSolverInitLevels_runs
    {w heap graph lengths gradient depth init read forestOp copy sort cell terminalInit : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {Inv : ℕ → State → Prop} {Done : State → Prop}
    (cost : ℕ → ℕ) (terminalCost : ℕ)
    (hh : st.regs 77 = heap) (hg : st.regs 69 = graph) (hl : st.regs 71 = lengths)
    (hc : st.regs 70 = gradient) (hd : st.regs 75 = depth)
    (hz : ZeroFrom st.mem heap) (hroom : heap + (depth + 1) + (depth + 1) < 2 ^ w)
    (hw : 1 < 2 ^ w) (hword : depth < 2 ^ w)
    (hseed : ∀ ready : State, ready.regs 51 = heap →
      ready.regs 52 = heap + (depth + 1) → ready.regs 4 = heap + (depth + 1) + (depth + 1) → ready.regs 6 = graph →
      ready.regs 7 = lengths → ready.regs 8 = gradient → ready.regs 20 = 0 →
      ready.regs 21 = depth → ready.mem = st.mem →
      ZeroFrom ready.mem heap →
      ready.regs 67 = st.regs 67 → ready.regs 68 = st.regs 68 →
      Inv 0 {ready with regs := Function.update ready.regs 19 0})
    (hindex : ∀ i current, i ≤ depth → Inv i current → current.regs 19 = i)
    (hstop : ∀ i current, i ≤ depth → Inv i current → current.regs 21 = depth)
    (hlevel : ∀ i, i < depth → Triple w p (Inv i) (rebuildCoreStep init read forestOp copy sort cell)
      (normalPost fun next =>
        Inv (i + 1) {next with regs := Function.update next.regs 19 (i + 1)} ∧
        next.regs 19 = i) (fun _ => cost i))
    (hterminal : Triple w p (Inv depth) (rebuildTerminalRuntimeStep terminalInit)
      (normalPost Done) (fun _ => terminalCost)) :
    ∃ out c, Runs w p ω (buildSolverInitLevels init read forestOp copy sort cell terminalInit)
      st .normal out c ∧ Done out ∧
      c ≤ rangeCost cost 0 depth + depth * 9 + terminalCost + 43 := by
  obtain ⟨ready, hr₁, h51, h52, h4, h6, h7, h8, h20, h21, hmem, hz', h67, h68⟩ :=
    prepareSolverInitLevels_runs (w := w) (p := p) (ω := ω) hh hd hg hl hc hz hroom
  obtain ⟨out, c, hr₂, hdone, hcost⟩ :=
    rebuildChainSuffix_runs (ω := ω) cost terminalCost (Nat.zero_le depth) hw hword h20
      (hseed ready h51 h52 h4 h6 h7 h8 h20 h21 hmem hz' h67 h68)
      (fun i current _ => hindex i current) (fun i current _ => hstop i current)
      (fun i _ => hlevel i) hterminal
  exact ⟨out, 34 + c + 1, runs_seq_iff.mpr (Or.inr ⟨ready, 34, c, hr₁, hr₂, rfl⟩),
    hdone, by omega⟩

/-- Compose the memory frames of the level and terminal calls below
the initial heap cursor. The loop changes only the level register. -/
theorem buildSolverInitLevels_framed_runs
    {w heap graph lengths gradient depth init read forestOp copy sort cell terminalInit : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {Inv : ℕ → State → Prop} {Done : State → Prop}
    (cost : ℕ → ℕ) (terminalCost : ℕ)
    (hh : st.regs 77 = heap) (hg : st.regs 69 = graph) (hl : st.regs 71 = lengths)
    (hc : st.regs 70 = gradient) (hd : st.regs 75 = depth)
    (hz : ZeroFrom st.mem heap) (hroom : heap + (depth + 1) + (depth + 1) < 2 ^ w)
    (hw : 1 < 2 ^ w) (hword : depth < 2 ^ w)
    (hseed : ∀ ready : State, ready.regs 51 = heap →
      ready.regs 52 = heap + (depth + 1) → ready.regs 4 = heap + (depth + 1) + (depth + 1) → ready.regs 6 = graph →
      ready.regs 7 = lengths → ready.regs 8 = gradient → ready.regs 20 = 0 →
      ready.regs 21 = depth → ready.mem = st.mem →
      ZeroFrom ready.mem heap →
      ready.regs 67 = st.regs 67 → ready.regs 68 = st.regs 68 →
      Inv 0 {ready with regs := Function.update ready.regs 19 0})
    (hindex : ∀ i current, i ≤ depth → Inv i current → current.regs 19 = i)
    (hstop : ∀ i current, i ≤ depth → Inv i current → current.regs 21 = depth)
    (hdescriptors : ∀ i current, i ≤ depth → Inv i current →
      heap ≤ current.regs 51 ∧ heap ≤ current.regs 52)
    (hlevel : ∀ i, i < depth → ∀ before : State,
      heap + (depth + 1) + (depth + 1) ≤ before.regs 4 →
      before.regs 67 = st.regs 67 → before.regs 68 = st.regs 68 →
      Triple w p (fun current => current = before ∧ Inv i current)
        (rebuildCoreStep init read forestOp copy sort cell)
        (normalPost fun next =>
          (Inv (i + 1) {next with regs := Function.update next.regs 19 (i + 1)} ∧
            next.regs 19 = i) ∧ before.regs 4 ≤ next.regs 4 ∧
          ∀ a < before.regs 4, a ≠ before.regs 51 → a ≠ before.regs 52 →
            next.mem a = before.mem a) (fun _ => cost i))
    (hterminal : ∀ before : State, heap + (depth + 1) + (depth + 1) ≤ before.regs 4 →
      before.regs 67 = st.regs 67 → before.regs 68 = st.regs 68 →
      Triple w p (fun current => current = before ∧ Inv depth current)
        (rebuildTerminalRuntimeStep terminalInit)
        (normalPost fun out => Done out ∧
          ∀ a < before.regs 4, a ≠ before.regs 51 → a ≠ before.regs 52 →
            out.mem a = before.mem a)
        (fun _ => terminalCost)) :
    ∃ out c, Runs w p ω (buildSolverInitLevels init read forestOp copy sort cell terminalInit)
      st .normal out c ∧ Done out ∧ (∀ a < heap, out.mem a = st.mem a) ∧
      c ≤ rangeCost cost 0 depth + depth * 9 + terminalCost + 43 := by
  let reservedEnd := heap + (depth + 1) + (depth + 1)
  let Frame (s : State) := ∀ a < heap, s.mem a = st.mem a
  have hreserved : heap ≤ reservedEnd := by dsimp [reservedEnd]; omega
  obtain ⟨out, c, hr, ⟨hdone, hframe⟩, hcost⟩ :=
    buildSolverInitLevels_runs (Inv := fun i s => Inv i s ∧ reservedEnd ≤ s.regs 4 ∧ Frame s ∧
      s.regs 67 = st.regs 67 ∧ s.regs 68 = st.regs 68)
      (Done := fun s => Done s ∧ Frame s) cost terminalCost hh hg hl hc hd hz hroom hw hword
      (fun ready h51 h52 h4 h6 h7 h8 h20 h21 hm hzero h67 h68 =>
        ⟨hseed ready h51 h52 h4 h6 h7 h8 h20 h21 hm hzero h67 h68,
          by change reservedEnd ≤ ready.regs 4; rw [h4], fun a _ => congrFun hm a, by simpa using h67, by simpa using h68⟩)
      (fun i s hi hs => hindex i s hi hs.1)
      (fun i s hi hs => hstop i s hi hs.1)
      (by
        intro i hi before ω' hs
        obtain ⟨o, next, c, hr, hp, hcost⟩ := (hlevel i hi before hs.2.1 hs.2.2.2.1 hs.2.2.2.2).runs ω' ⟨rfl, hs.1⟩
        cases o with
        | returned value => exact False.elim hp
        | normal =>
          obtain ⟨hhandle, hbranch⟩ := hdescriptors i before hi.le hs.1
          refine ⟨.normal, next, c, hr, ⟨⟨hp.1.1, ?_, ?_, ?_, ?_⟩, hp.1.2⟩, hcost⟩
          · simpa using hs.2.1.trans hp.2.1
          · intro a ha
            exact (hp.2.2 a (ha.trans_le (hreserved.trans hs.2.1)) (Nat.ne_of_lt (ha.trans_le hhandle))
              (Nat.ne_of_lt (ha.trans_le hbranch))).trans (hs.2.2.1 a ha)
          · simpa using (runs_preserves_above (by decide : 55 ≤ 67)
              (rebuildCoreStep_writesBelow ..) hr).trans hs.2.2.2.1
          · simpa using (runs_preserves_above (by decide : 55 ≤ 68)
              (rebuildCoreStep_writesBelow ..) hr).trans hs.2.2.2.2)
      (by
        intro before ω' hs
        obtain ⟨o, next, c, hr, hp, hcost⟩ := (hterminal before hs.2.1 hs.2.2.2.1 hs.2.2.2.2).runs ω' ⟨rfl, hs.1⟩
        cases o with
        | returned value => exact False.elim hp
        | normal =>
          obtain ⟨hhandle, hbranch⟩ := hdescriptors depth before le_rfl hs.1
          exact ⟨.normal, next, c, hr, ⟨hp.1, fun a ha =>
            (hp.2 a (ha.trans_le (hreserved.trans hs.2.1)) (Nat.ne_of_lt (ha.trans_le hhandle))
              (Nat.ne_of_lt (ha.trans_le hbranch))).trans (hs.2.2.1 a ha)⟩, hcost⟩)
  exact ⟨out, c, hr, hdone, hframe, hcost⟩

/-- During Init the two descriptor tables start at or above the incoming
heap. The loop's suffix invariant gives the same lower bound on their cursors. -/
theorem solverInitLevels_descriptor_bounds
    {T : Chain.SparseCoreRestartTool} {P : Chain.ChainParams} {R : DSRep T.State}
    {chain : Chain.ChainState T P} {len grad : ℕ → ℝ}
    {heap i vc ec h limbs precision : ℕ} {st : State}
    (hin : RebuildSuffixAt R chain len grad heap (heap + (P.d + 1)) 0 i
      vc ec h limbs precision st) :
    heap ≤ st.regs 51 ∧ heap ≤ st.regs 52 := by
  rw [hin.handleCursor, hin.branchCursor]
  exact ⟨Nat.le_add_right _ _, (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)⟩

/-- At level zero of Algorithm 1 (page 20), the packed graph and input
vectors establish the suffix invariant with no installed cores. -/
theorem solverInitLevels_entry
    {T : Chain.SparseCoreRestartTool} {P : Chain.ChainParams} {R : DSRep T.State}
    {chain : Chain.ChainState T P} {G : MGraph} {len grad : ℕ → ℝ}
    {handleBase branchBase vc ec h limbs precision : ℕ} {st : State}
    (hroot : chain.G 0 = G) (hd : st.regs 21 = P.d)
    (hh : st.regs 51 = handleBase) (hb : st.regs 52 = branchBase)
    (hg : DynSpanner.Program.DynGraphAt st.mem (st.regs 6) vc ec G)
    (hl : EdgeValuesAt st.mem (st.regs 7) h limbs precision G.E len)
    (hc : EdgeValuesAt st.mem (st.regs 8) h limbs precision G.E grad)
    (hgEnd : st.regs 6 + DynSpanner.Program.dynGraphSize vc ec ≤ st.regs 4)
    (hlEnd : st.regs 7 + ec * limbs ≤ st.regs 4)
    (hcEnd : st.regs 8 + ec * limbs ≤ st.regs 4)
    (hz : ZeroFrom st.mem (st.regs 4)) :
    RebuildSuffixAt R chain len grad handleBase branchBase 0 0 vc ec h limbs precision
      {st with regs := Function.update st.regs 19 0} := by
  have hcores := rebuiltCoresAt_empty R chain st.mem handleBase branchBase 0 (st.regs 4)
  constructor <;> dsimp only <;> simp (config := {decide := true}) only
    [Function.update_self, Function.update_of_ne, ne_eq, Nat.add_zero, hroot,
      Chain.TreeChain.chainLen, Chain.TreeChain.chainGrad]
  all_goals assumption

private theorem rebuildSuffix_root (T : Chain.SparseCoreRestartTool) (L : Chain.LastLevelTool)
    (P : Chain.ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (len grad : ℕ → ℝ) (remaining index : ℕ)
    (graphs : ℕ → MGraph) (cores : ℕ → T.State)
    (branches updates enc dec fwd : ℕ → ℕ) :
    (Chain.rebuildSuffix T L P lvlM N₀ len grad remaining index graphs cores branches updates enc dec fwd).1 0 =
      graphs 0 := by
  induction remaining generalizing index graphs cores branches updates enc dec fwd with
  | zero => rfl
  | succ remaining ih =>
    rw [Chain.rebuildSuffix]
    rw [ih]
    simp

/-- Algorithm 1 initialization keeps the solver graph at the root. -/
theorem solverInit_rootGraph (T : Chain.SparseCoreRestartTool) (L : Chain.LastLevelTool)
    (P : Chain.ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (G : MGraph) (len grad : ℕ → ℝ) :
    (Chain.algorithm1_initialize T L P lvlM N₀ G len grad).1.G 0 = G := by
  unfold Chain.algorithm1_initialize
  dsimp only
  exact rebuildSuffix_root T L P lvlM N₀ len grad P.d 0 (fun _ => G) _ _ _ _ _ _

/-- The packed solver graph and vectors seed the initial suffix
invariant after reserving the handle and branch tables. -/
theorem prepareSolverInitLevels_model_runs
    {T : Chain.SparseCoreRestartTool} {L : Chain.LastLevelTool}
    {P : Chain.ChainParams} {R : DSRep T.State}
    {lvlM : ℕ → ℕ} {N₀ : ℕ}
    {G : MGraph} {len grad : ℕ → ℝ}
    {w heap graph lengths gradient vc ec h limbs precision : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hd : st.regs 75 = P.d)
    (hh : st.regs 77 = heap) (hg : st.regs 69 = graph)
    (hl : st.regs 71 = lengths) (hc : st.regs 70 = gradient)
    (hG : DynSpanner.Program.DynGraphAt st.mem graph vc ec G)
    (hLen : EdgeValuesAt st.mem lengths h limbs precision G.E len)
    (hGrad : EdgeValuesAt st.mem gradient h limbs precision G.E grad)
    (hgEnd : graph + DynSpanner.Program.dynGraphSize vc ec ≤ heap)
    (hlEnd : lengths + ec * limbs ≤ heap) (hcEnd : gradient + ec * limbs ≤ heap)
    (hz : ZeroFrom st.mem heap) (hroom : heap + (P.d + 1) + (P.d + 1) < 2 ^ w) :
    ∃ out, Runs w p ω prepareSolverInitLevels st .normal out 34 ∧ out.regs 20 = 0 ∧
      RebuildSuffixAt R (Chain.algorithm1_initialize T L P lvlM N₀ G len grad).1 len grad heap (heap + (P.d + 1)) 0 0 vc ec h limbs precision
        {out with regs := Function.update out.regs 19 0} := by
  obtain ⟨out, hr, h51, h52, h4, h6, h7, h8, h20, h21, hm, hfree, _, _⟩ :=
    prepareSolverInitLevels_runs (w := w) (p := p) (ω := ω) hh hd hg hl hc hz hroom
  refine ⟨out, hr, h20, solverInitLevels_entry (solverInit_rootGraph T L P lvlM N₀ G len grad) h21 h51 h52 ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · simpa only [hm, h6] using hG
  · simpa only [hm, h7] using hLen
  · simpa only [hm, h8] using hGrad
  · rw [h6, h4]; omega
  · rw [h7, h4]; omega
  · rw [h8, h4]; omega
  · intro a ha
    exact hfree a (by omega)

/-- Apply the framed Init loop with the Algorithm 1 suffix representation.
The descriptor bounds follow from the positions of the two Init tables. -/
theorem buildSolverInitLevels_model_framed_runs
    {T : Chain.SparseCoreRestartTool} {P : Chain.ChainParams} {R : DSRep T.State}
    {L : Chain.LastLevelTool} {lvlM : ℕ → ℕ} {N₀ : ℕ} {G : MGraph} {len grad : ℕ → ℝ} {vc ec : ℕ → ℕ}
    {w heap graph lengths gradient h limbs precision init read forestOp copy sort cell terminalInit : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {Done : State → Prop}
    (cost : ℕ → ℕ) (terminalCost : ℕ)
    (hh : st.regs 77 = heap) (hg : st.regs 69 = graph) (hl : st.regs 71 = lengths)
    (hc : st.regs 70 = gradient) (hd : st.regs 75 = P.d)
    (hz : ZeroFrom st.mem heap) (hroom : heap + (P.d + 1) + (P.d + 1) < 2 ^ w)
    (hG : DynSpanner.Program.DynGraphAt st.mem graph (vc 0) (ec 0) G)
    (hLen : EdgeValuesAt st.mem lengths h limbs precision G.E len)
    (hGrad : EdgeValuesAt st.mem gradient h limbs precision G.E grad)
    (hgEnd : graph + DynSpanner.Program.dynGraphSize (vc 0) (ec 0) ≤ heap)
    (hlEnd : lengths + ec 0 * limbs ≤ heap) (hcEnd : gradient + ec 0 * limbs ≤ heap)
    (hw : 1 < 2 ^ w) (hword : P.d < 2 ^ w) :
    let chain := (Chain.algorithm1_initialize T L P lvlM N₀ G len grad).1
    let Inv := fun i => RebuildSuffixAt R chain len grad heap (heap + (P.d + 1)) 0 i
      (vc i) (ec i) h limbs precision
    (∀ i, i < P.d → ∀ before : State,
      heap + (P.d + 1) + (P.d + 1) ≤ before.regs 4 →
      before.regs 67 = st.regs 67 → before.regs 68 = st.regs 68 →
      Triple w p (fun current => current = before ∧ Inv i current)
        (rebuildCoreStep init read forestOp copy sort cell)
        (normalPost fun next =>
          (Inv (i + 1) {next with regs := Function.update next.regs 19 (i + 1)} ∧
            next.regs 19 = i) ∧ before.regs 4 ≤ next.regs 4 ∧
          ∀ a < before.regs 4, a ≠ before.regs 51 → a ≠ before.regs 52 →
            next.mem a = before.mem a) (fun _ => cost i)) →
    (∀ before : State, heap + (P.d + 1) + (P.d + 1) ≤ before.regs 4 →
      before.regs 67 = st.regs 67 → before.regs 68 = st.regs 68 →
      Triple w p (fun current => current = before ∧ Inv P.d current)
        (rebuildTerminalRuntimeStep terminalInit)
        (normalPost fun out => Done out ∧
          ∀ a < before.regs 4, a ≠ before.regs 51 → a ≠ before.regs 52 →
            out.mem a = before.mem a)
        (fun _ => terminalCost)) →
    ∃ out c, Runs w p ω (buildSolverInitLevels init read forestOp copy sort cell terminalInit)
      st .normal out c ∧ Done out ∧ (∀ a < heap, out.mem a = st.mem a) ∧
      c ≤ rangeCost cost 0 P.d + P.d * 9 + terminalCost + 43 := by
  dsimp only
  intro hlevel hterminal
  exact buildSolverInitLevels_framed_runs cost terminalCost hh hg hl hc hd hz hroom hw hword
    (by
      intro ready h51 h52 h4 h6 h7 h8 _ h21 hm hfree _ _
      apply solverInitLevels_entry (solverInit_rootGraph T L P lvlM N₀ G len grad) h21 h51 h52
      · simpa only [hm, h6] using hG
      · simpa only [hm, h7] using hLen
      · simpa only [hm, h8] using hGrad
      · rw [h6, h4]; omega
      · rw [h7, h4]; omega
      · rw [h8, h4]; omega
      · intro a ha
        exact hfree a (by omega))
    (fun _ _ _ hs => hs.index) (fun _ _ _ hs => hs.depth)
    (fun _ _ _ hs => solverInitLevels_descriptor_bounds hs) hlevel hterminal

/-- The terminal step of Algorithm 1 Init uses the model's last
collection and the two descriptor slots reserved at the incoming heap. -/
theorem solverInitLevels_terminal_triple
    {w L init vCap eCap multiplier stretchPrecision heap : ℕ}
    {fmt : Num.Format w} {tool : LastLevelTool}
    {T : SparseCoreRestartTool} {P : ChainParams}
    (lvlM : ℕ → ℕ) (N₀ : ℕ) (G : MGraph) (len grad : ℕ → ℝ)
    {allocation : ℕ → List ℕ → ℕ} {R : DSRep (ℕ × (ℕ → LSF))} {core : DSRep T.State}
    {p : Program} {op : ℕ → ℕ} {st : State}
    :
    let chain := (algorithm1_initialize T tool P lvlM N₀ G len grad).1
    RebuildSuffixAt core chain len grad heap (heap + (P.d + 1)) 0 P.d
      vCap eCap fmt.limbBits L fmt.precision st →
    (R.Implements w p init op
      (lastLevelRuntimeMachineContract fmt L tool (chain.G P.d) vCap eCap multiplier stretchPrecision allocation)) →
    (st.regs 67 = L) → (st.regs 68 = fmt.precision) →
    (L < 2 ^ w) → (fmt.precision < 2 ^ w) → fmt.limbBits = 4 → fmt.precision ≤ 4 * L →
    (∀ e ∈ (chain.G P.d).E, 2 * (2 : ℝ)^stretchPrecision *
      lastLevelStretchBound (chain.G P.d) (chain.toTreeChain.chainLen len P.d) e <
        Num.capacity fmt.limbBits L) →
    (∀ e ∈ (chain.G P.d).E, 0 < chain.toTreeChain.chainLen len P.d e) →
    (tool.build (chain.G P.d) (fun e => if e ∈ (chain.G P.d).E
        then chain.toTreeChain.chainLen len P.d e else 0) =
      tool.build (chain.G P.d) (chain.toTreeChain.chainLen len P.d)) →
    (st.regs 4 + allocation 1 [st.regs 6, st.regs 7, L, fmt.precision, st.regs 4] < 2 ^ w) →
    heap + (P.d + 1) + (P.d + 1) ≤ st.regs 4 →
    core.Local →
    Triple w p (fun current => current = st) (rebuildTerminalRuntimeStep init)
      (normalPost fun out =>
        (RebuiltCoresAt core chain out.mem heap (heap + (P.d + 1)) 0 P.d (out.regs 4) ∧
          out.mem (heap + (P.d + 1) + P.d) = chain.lastBran ∧ ZeroFrom out.mem (out.regs 4) ∧
          ∃ y : R.τ, R.rep (out.mem (heap + P.d)) (chain.lastK, chain.lastLSFs)
            y out.mem ∧ ∀ a, R.foot (out.mem (heap + P.d)) y a → a < out.regs 4) ∧
        ∀ a < st.regs 4, a ≠ st.regs 51 → a ≠ st.regs 52 → out.mem a = st.mem a)
      (fun _ => multiplier * (tool.cost (chain.G P.d) + 1) + 20) := by
  dsimp only
  intro hin himpl hL hP hLWord hPWord hFour hWidth hst hpos hagreement hroom hend hlocal
  obtain ⟨hmodel, hbranch⟩ := algorithm1_initialize_terminal T tool P lvlM N₀ G len grad
  exact rebuildTerminalRuntimeStep_suffixAt_triple _ len grad hin himpl hL hP hLWord hPWord hFour hWidth
    hst hmodel hbranch hpos hagreement hroom (by omega) (by omega) (Nat.zero_le _)
    (Or.inl (by omega)) hlocal

/-- Finish the framed initial suffix using the linked terminal tool. -/
theorem buildSolverInitLevels_withTerminal_runs
    {T : Chain.SparseCoreRestartTool} {P : Chain.ChainParams} {R : DSRep T.State}
    {L : Chain.LastLevelTool} {lvlM : ℕ → ℕ} {N₀ : ℕ} {G : MGraph} {len grad : ℕ → ℝ} {vc ec : ℕ → ℕ}
    {w heap graph lengths gradient limbs init read forestOp copy sort cell terminalInit : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} 
    {fmt : Num.Format w} {terminal : DSRep (ℕ × (ℕ → LSF))}
    {op : ℕ → ℕ} {allocation : ℕ → List ℕ → ℕ} {multiplier stretchPrecision : ℕ}
    (cost : ℕ → ℕ)
    (hh : st.regs 77 = heap) (hg : st.regs 69 = graph) (hl : st.regs 71 = lengths)
    (hc : st.regs 70 = gradient) (hd : st.regs 75 = P.d)
    (hz : ZeroFrom st.mem heap) (hroom : heap + (P.d + 1) + (P.d + 1) < 2 ^ w)
    (hG : DynSpanner.Program.DynGraphAt st.mem graph (vc 0) (ec 0) G)
    (hLen : EdgeValuesAt st.mem lengths fmt.limbBits limbs fmt.precision G.E len)
    (hGrad : EdgeValuesAt st.mem gradient fmt.limbBits limbs fmt.precision G.E grad)
    (hgEnd : graph + DynSpanner.Program.dynGraphSize (vc 0) (ec 0) ≤ heap)
    (hlEnd : lengths + ec 0 * limbs ≤ heap) (hcEnd : gradient + ec 0 * limbs ≤ heap)
    (h67 : st.regs 67 = limbs) (h68 : st.regs 68 = fmt.precision)
    (hw : 1 < 2 ^ w) (hword : P.d < 2 ^ w) :
    let chain := (Chain.algorithm1_initialize T L P lvlM N₀ G len grad).1
    let Inv := fun i => RebuildSuffixAt R chain len grad heap (heap + (P.d + 1)) 0 i
      (vc i) (ec i) fmt.limbBits limbs fmt.precision
    (∀ i, i < P.d → ∀ before : State,
      heap + (P.d + 1) + (P.d + 1) ≤ before.regs 4 →
      before.regs 67 = st.regs 67 → before.regs 68 = st.regs 68 →
      Triple w p (fun current => current = before ∧ Inv i current)
        (rebuildCoreStep init read forestOp copy sort cell)
        (normalPost fun next =>
          (Inv (i + 1) {next with regs := Function.update next.regs 19 (i + 1)} ∧
            next.regs 19 = i) ∧ before.regs 4 ≤ next.regs 4 ∧
          ∀ a < before.regs 4, a ≠ before.regs 51 → a ≠ before.regs 52 →
            next.mem a = before.mem a) (fun _ => cost i)) →
    terminal.Implements w p terminalInit op
      (lastLevelRuntimeMachineContract fmt limbs L (chain.G P.d) (vc P.d) (ec P.d)
        multiplier stretchPrecision allocation) →
    R.Local → limbs < 2 ^ w → fmt.precision < 2 ^ w → fmt.limbBits = 4 → fmt.precision ≤ 4 * limbs →
    (∀ e ∈ (chain.G P.d).E, 2 * (2 : ℝ)^stretchPrecision *
      lastLevelStretchBound (chain.G P.d) (chain.toTreeChain.chainLen len P.d) e <
        Num.capacity fmt.limbBits limbs) →
    (∀ e ∈ (chain.G P.d).E, 0 < chain.toTreeChain.chainLen len P.d e) →
    L.build (chain.G P.d) (fun e => if e ∈ (chain.G P.d).E then
      chain.toTreeChain.chainLen len P.d e else 0) =
      L.build (chain.G P.d) (chain.toTreeChain.chainLen len P.d) →
    (∀ before, Inv P.d before → before.regs 4 +
        allocation 1 [before.regs 6, before.regs 7, limbs, fmt.precision, before.regs 4] < 2 ^ w) →
    let terminalCost := multiplier * (L.cost (chain.G P.d) + 1) + 20
    ∃ out c, Runs w p ω (buildSolverInitLevels init read forestOp copy sort cell terminalInit)
      st .normal out c ∧
      RebuiltCoresAt R chain out.mem heap (heap + (P.d + 1)) 0 P.d (out.regs 4) ∧
      out.mem (heap + (P.d + 1) + P.d) = chain.lastBran ∧ ZeroFrom out.mem (out.regs 4) ∧
      (∃ y : terminal.τ, terminal.rep (out.mem (heap + P.d)) (chain.lastK, chain.lastLSFs)
        y out.mem ∧ ∀ a, terminal.foot (out.mem (heap + P.d)) y a → a < out.regs 4) ∧ (∀ a < heap, out.mem a = st.mem a) ∧
      c ≤ rangeCost cost 0 P.d + P.d * 9 + terminalCost + 43 := by
  dsimp only
  intro hlevel himpl hlocal hLWord hPWord hFour hWidth hstretch hpos hagreement hspace
  obtain ⟨out, c, hr, ⟨hcores, hb, hzero, hterminal⟩, hframe, hcost⟩ :=
    buildSolverInitLevels_model_framed_runs (lvlM := lvlM) (N₀ := N₀) cost _ hh hg hl hc hd hz hroom hG hLen hGrad
      hgEnd hlEnd hcEnd hw hword hlevel (by
        intro before hend hL hP current ω' hp
        obtain ⟨heq, hin⟩ := hp
        subst current
        have hroom := hspace before hin
        exact (solverInitLevels_terminal_triple lvlM N₀ G len grad hin himpl (hL.trans h67) (hP.trans h68) hLWord hPWord hFour hWidth
          hstretch hpos hagreement hroom hend hlocal).runs ω' rfl)
  exact ⟨out, c, hr, hcores, hb, hzero, hterminal, hframe, hcost⟩

end MinCostFlow.MinRatio
