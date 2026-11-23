module

public import MinCostFlow.MinRatio.WireChainCoreCompactAux
import WordRAM.Tactic

/-!
# Level-0 compaction assembly (`WireChainCoreCompact`)

Proves `wireCompactZeroOffReadyStmt_runs` (Pass 4) and `wireCompactLevel0Body_runs` (combining all
four passes of `wireCompactLevel0Body`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Chain MinCostFlow.Chain.Ordered MinCostFlow.DynSpanner.Program

/-- Execute Pass 4 (`wireCompactZeroOffReadyStmt`): zeroes `inOffReady[0..intCap)` and stores `0`
at `root + 11`. -/
private theorem wireCompactZeroOffReadyStmt_runs
    {w root inOffReady intCap : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hr0 : st.regs 0 = root) (hr12 : st.regs 12 = inOffReady) (hr14 : st.regs 14 = intCap)
    (hDisjR : root + 11 < inOffReady ∨ inOffReady + intCap ≤ root + 11)
    (hW1 : root + 16 < 2 ^ w) (hW2 : inOffReady + intCap < 2 ^ w) (hw11 : 11 < 2 ^ w) :
    ∃ out cost,
      Runs w p ω wireCompactZeroOffReadyStmt st .normal out cost ∧
      cost ≤ 20 * intCap + 40 ∧
      out.mem (root + 11) = 0 ∧
      (∀ e < intCap, out.mem (inOffReady + e) = 0) ∧
      (∀ r ≠ 20, out.regs r = st.regs r) ∧
      (∀ a, a ≠ root + 11 → (a < inOffReady ∨ inOffReady + intCap ≤ a) → out.mem a = st.mem a) := by
  have hw1 : 1 < 2 ^ w := by omega
  let InvZ (j : ℕ) (s : State) : Prop :=
    j ≤ intCap ∧ s.regs 20 = j ∧ (∀ r ≠ 20, s.regs r = st.regs r) ∧
    (∀ k < j, s.mem (inOffReady + k) = 0) ∧
    ∀ a, (a < inOffReady ∨ inOffReady + intCap ≤ a) → s.mem a = st.mem a
  have hloopZ := Triple.forRange_const (w := w) (p := p) (r := 20) (lo := .const 0) (hi := .reg 14)
    (P := fun s => s = st) (Inv := InvZ) 10 0 intCap (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun s hs => by
      subst hs; exact ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], Nat.zero_le _, by simp,
        fun r hr => by simp [Function.update_of_ne hr], fun _ hk => by omega, fun _ _ => rfl⟩)
    (fun _ _ _ _ h => h.2.1)
    (fun _ s _ _ h => by simp [Expr.eval, (h.2.2.1 14 (by decide)).trans hr14])
    (fun j _ hj s ω' ⟨_, hjr, hregs, hzero, hfr⟩ => by
      let t1 := { s with mem := Function.update s.mem (inOffReady + j) 0 }
      have rt1 : Runs w p ω' (.store (.bin .add (.reg 12) (.reg 20)) (.const 0)) s .normal t1 5 :=
        runs_store_iff.mpr ⟨inOffReady + j, 0,
          by simp [Expr.eval, BinOp.eval, (hregs 12 (by decide)).trans hr12, hjr, show inOffReady + j < 2 ^ w by omega],
          by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
      refine ⟨.normal, t1, 5, rt1, ⟨⟨by omega, by simp, fun r hr => by simp [t1, Function.update_of_ne hr, hregs r hr],
        fun k hk => by
          by_cases hkj : k = j
          · subst hkj; simp [t1]
          · simp [t1, Function.update_of_ne (by omega : inOffReady + k ≠ inOffReady + j), hzero k (by omega)],
        fun a ha => by simp [t1, Function.update_of_ne (by rcases ha with h | h <;> omega : a ≠ inOffReady + j), hfr a ha]⟩,
        by simp [t1, hjr]⟩, by dsimp only; omega⟩)
  obtain ⟨oZ, s1, cZ, rZ, hZ, hcZ⟩ := hloopZ.runs ω rfl
  cases oZ with
  | returned _ => exact False.elim hZ
  | normal =>
    obtain ⟨_, _, hs1Regs, hs1Zero, hs1Fr⟩ := hZ
    let out := { s1 with mem := Function.update s1.mem (root + 11) 0 }
    have rStore : Runs w p ω (.store (.bin .add (.reg 0) (.const 11)) (.const 0)) s1 .normal out 5 :=
      runs_store_iff.mpr ⟨root + 11, 0,
        by simp [Expr.eval, BinOp.eval, (hs1Regs 0 (by decide)).trans hr0, hw11, show root + 11 < 2 ^ w by omega],
        by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
    simp only [Expr.size] at hcZ
    exact ⟨out, cZ + 5 + 1, runs_seq_iff.mpr (Or.inr ⟨s1, cZ, 5, rZ, rStore, rfl⟩), by omega,
      by simp [out], fun e he => by simp [out, Function.update_of_ne (by rcases hDisjR with h | h <;> omega : inOffReady + e ≠ root + 11), hs1Zero e he],
      hs1Regs, fun a h1 h2 => by simp [out, Function.update_of_ne h1, hs1Fr a h2]⟩

set_option maxHeartbeats 600000 in
/-- Execute `wireCompactLevel0Body`: performs all 4 compaction passes, resets `inOffReady` and
`root + 11` to `0`, and returns `nextHeap = heap + wireCompactLevel0Space n eCap L G.m`. -/
theorem wireCompactLevel0Body_runs
    {w copyWords dgInit root oldLen0 unrankPtr heap
      handle table levelsEnd forward inverse freshCounter slots names slotThresholds
      edgeThresholds edgeRecords offReadyCount offReadyList inOffReady oldRootGraph intCap
      d n eCap oldLenECap L P pos : ℕ}
    {G : MGraph} {oldℓ : ℕ → ℝ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    (hCopy : MeetsContract w p copyWords (copyWordsContract w))
    (hDGInit : ∀ vL eTriples, MeetsContract w p dgInit (dgInitFromListsContract w n eCap G.compact vL eTriples))
    (hRoot : SolverRootDirAt mem root handle table levelsEnd forward inverse freshCounter slots
      names slotThresholds edgeThresholds edgeRecords offReadyCount offReadyList inOffReady
      oldRootGraph intCap)
    (hDmem : mem (handle + 11) = d) (hLmem : mem (handle + 5) = L)
    (hDG : DynGraphAt mem oldRootGraph n eCap G)
    (hOldLen : EdgeValuesAt mem oldLen0 4 L P G.E oldℓ)
    (hUnr : ∀ j < G.m, mem (unrankPtr + j) = compactUnrank G.E j)
    (hCapE : ∀ e ∈ G.E, e < eCap) (hCapOldLen : ∀ e ∈ G.E, e < oldLenECap)
    (hCapInt : ∀ e ∈ G.E, e < intCap)
    (hdPos : 0 < d)
    (hRootLe : root + 16 ≤ heap) (hHandleLe : handle + 18 ≤ heap)
    (hMetaLe : solverLevelMetaAddr table d + 2 * d ≤ heap)
    (hRGLe : oldRootGraph + dynGraphSize n eCap ≤ heap)
    (hOldLenLe : oldLen0 + oldLenECap * L ≤ heap) (hUnrLe : unrankPtr + G.m ≤ heap)
    (hETLe : edgeThresholds + intCap ≤ heap) (hERLe : edgeRecords + intCap ≤ heap)
    (hIOLe : inOffReady + intCap ≤ heap)
    (hMutDisj :
      let lm := solverLevelMetaAddr table d
      (edgeThresholds + intCap ≤ edgeRecords ∨ edgeRecords + intCap ≤ edgeThresholds) ∧
      (edgeThresholds + intCap ≤ inOffReady ∨ inOffReady + intCap ≤ edgeThresholds) ∧
      (edgeRecords + intCap ≤ inOffReady ∨ inOffReady + intCap ≤ edgeRecords) ∧
      (root + 16 ≤ lm ∨ lm + 2 * d ≤ root) ∧
      (root + 16 ≤ edgeThresholds ∨ edgeThresholds + intCap ≤ root) ∧
      (root + 16 ≤ edgeRecords ∨ edgeRecords + intCap ≤ root) ∧
      (root + 16 ≤ inOffReady ∨ inOffReady + intCap ≤ root) ∧
      (lm + 2 * d ≤ edgeThresholds ∨ edgeThresholds + intCap ≤ lm) ∧
      (lm + 2 * d ≤ edgeRecords ∨ edgeRecords + intCap ≤ lm) ∧
      (lm + 2 * d ≤ inOffReady ∨ inOffReady + intCap ≤ lm))
    (hRODisj :
      (unrankPtr + G.m ≤ edgeThresholds ∨ edgeThresholds + intCap ≤ unrankPtr) ∧
      (unrankPtr + G.m ≤ edgeRecords ∨ edgeRecords + intCap ≤ unrankPtr) ∧
      (oldLen0 + oldLenECap * L ≤ edgeThresholds ∨ edgeThresholds + intCap ≤ oldLen0) ∧
      (oldLen0 + oldLenECap * L ≤ edgeRecords ∨ edgeRecords + intCap ≤ oldLen0) ∧
      (oldRootGraph + dynGraphSize n eCap ≤ edgeThresholds ∨ edgeThresholds + intCap ≤ oldRootGraph) ∧
      (oldRootGraph + dynGraphSize n eCap ≤ edgeRecords ∨ edgeRecords + intCap ≤ oldRootGraph))
    (hz : ZeroFrom mem heap)
    (hRoom : heap + wireCompactLevel0Space n eCap L G.m < 2 ^ w) (hw16 : 16 ≤ 2 ^ w) :
    let levelMeta := solverLevelMetaAddr table d
    let newRootGraph := heap + eCap * L + 3 * G.m
    let newLvlGraph0 := newRootGraph + dynGraphSize n eCap
    let nextHeap := heap + wireCompactLevel0Space n eCap L G.m
    ∃ out cost,
      Runs w p ω (wireCompactLevel0Body copyWords dgInit)
        (startState [root, oldLen0, unrankPtr, G.m, heap] mem pos) (.returned nextHeap) out cost ∧
      cost ≤ wireCompactLevel0Cost n eCap intCap L G.m ∧
      (∀ j < G.m, out.mem (edgeThresholds + j) = mem (edgeThresholds + compactUnrank G.E j) ∧
        out.mem (edgeRecords + j) = mem (edgeRecords + compactUnrank G.E j)) ∧
      EdgeValuesAt out.mem heap 4 L P G.compact.E (fun j => oldℓ (compactUnrank G.E j)) ∧
      DynGraphAt out.mem newRootGraph n eCap G.compact ∧
      DynGraphAt out.mem newLvlGraph0 n eCap G.compact ∧
      out.mem (root + 14) = newRootGraph ∧
      out.mem (root + 11) = 0 ∧
      out.mem levelMeta = heap ∧
      out.mem (levelMeta + d) = newLvlGraph0 ∧
      (∀ e < intCap, out.mem (inOffReady + e) = 0) ∧
      OffReadyInv out.mem 0 offReadyList inOffReady intCap ∧
      ZeroFrom out.mem nextHeap ∧
      ∀ a < heap, ¬ InCompactMutable root table d edgeThresholds edgeRecords offReadyList inOffReady intCap a →
        out.mem a = mem a := by
  dsimp only
  set lm := solverLevelMetaAddr table d
  set newRootGraph := heap + eCap * L + 3 * G.m
  set newLvlGraph0 := newRootGraph + dynGraphSize n eCap
  set nextHeap := heap + wireCompactLevel0Space n eCap L G.m
  have hDgDef : dynGraphSize n eCap = 4 + 7 * n + 9 * eCap := rfl
  have hGmLeIntCap : G.m ≤ intCap := by
    have := Finset.card_le_card (fun e he => Finset.mem_range.mpr (hCapInt e he))
    simpa [MGraph.m] using this
  let s0 := startState [root, oldLen0, unrankPtr, G.m, heap] mem pos
  let s1 := { s0 with regs := Function.update s0.regs 5 handle }
  let s2 := { s1 with regs := Function.update s1.regs 6 table }
  let s3 := { s2 with regs := Function.update s2.regs 7 d }
  let s4 := { s3 with regs := Function.update s3.regs 8 L }
  let s5 := { s4 with regs := Function.update s4.regs 9 edgeThresholds }
  let s6 := { s5 with regs := Function.update s5.regs 10 edgeRecords }
  let s7 := { s6 with regs := Function.update s6.regs 11 offReadyList }
  let s8 := { s7 with regs := Function.update s7.regs 12 inOffReady }
  let s9 := { s8 with regs := Function.update s8.regs 13 oldRootGraph }
  let s10 := { s9 with regs := Function.update s9.regs 14 intCap }
  let s11 := { s10 with regs := Function.update s10.regs 15 n }
  let s12 := { s11 with regs := Function.update s11.regs 16 eCap }
  let s13 := { s12 with regs := Function.update s12.regs 17 (dgIntToExtBase oldRootGraph n) }
  let s14 := { s13 with regs := Function.update s13.regs 18 (dgETailSlotBase oldRootGraph n eCap) }
  let s15 := { s14 with regs := Function.update s14.regs 19 (dgEHeadSlotBase oldRootGraph n eCap) }
  let s16 := { s15 with regs := Function.update s15.regs 32 lm }
  let s17 := { s16 with regs := Function.update s16.regs 22 heap }
  have h1 : Runs w p ω (.assign 5 (.load (.reg 0))) s0 .normal s1 3 :=
    runs_assign_iff.mpr ⟨handle, by simp [Expr.eval, s0, startState, show mem root = handle by simpa using hRoot 0 (by simp)], rfl, rfl, rfl⟩
  have h2 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 0) (.const 1)))) s1 .normal s2 5 :=
    runs_assign_iff.mpr ⟨table, by simp [Expr.eval, BinOp.eval, s1, s0, startState, show 1 < 2 ^ w by omega,
      show root + 1 < 2 ^ w by omega, show mem (root + 1) = table by simpa using hRoot 1 (by simp)], rfl, rfl, rfl⟩
  have h3 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 5) (.const 11)))) s2 .normal s3 5 :=
    runs_assign_iff.mpr ⟨d, by simp [Expr.eval, BinOp.eval, s2, s1, s0, startState, show 11 < 2 ^ w by omega,
      show handle + 11 < 2 ^ w by omega, hDmem], rfl, rfl, rfl⟩
  have h4 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 5) (.const 5)))) s3 .normal s4 5 :=
    runs_assign_iff.mpr ⟨L, by simp [Expr.eval, BinOp.eval, s3, s2, s1, s0, startState, show 5 < 2 ^ w by omega,
      show handle + 5 < 2 ^ w by omega, hLmem], rfl, rfl, rfl⟩
  have h5 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 0) (.const 9)))) s4 .normal s5 5 :=
    runs_assign_iff.mpr ⟨edgeThresholds, by simp [Expr.eval, BinOp.eval, s4, s3, s2, s1, s0, startState,
      show 9 < 2 ^ w by omega, show root + 9 < 2 ^ w by omega, show mem (root + 9) = edgeThresholds by simpa using hRoot 9 (by simp)], rfl, rfl, rfl⟩
  have h6 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 0) (.const 10)))) s5 .normal s6 5 :=
    runs_assign_iff.mpr ⟨edgeRecords, by simp [Expr.eval, BinOp.eval, s5, s4, s3, s2, s1, s0, startState,
      show 10 < 2 ^ w by omega, show root + 10 < 2 ^ w by omega, show mem (root + 10) = edgeRecords by simpa using hRoot 10 (by simp)], rfl, rfl, rfl⟩
  have h7 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 0) (.const 12)))) s6 .normal s7 5 :=
    runs_assign_iff.mpr ⟨offReadyList, by simp [Expr.eval, BinOp.eval, s6, s5, s4, s3, s2, s1, s0, startState,
      show 12 < 2 ^ w by omega, show root + 12 < 2 ^ w by omega, show mem (root + 12) = offReadyList by simpa using hRoot 12 (by simp)], rfl, rfl, rfl⟩
  have h8 : Runs w p ω (.assign 12 (.load (.bin .add (.reg 0) (.const 13)))) s7 .normal s8 5 :=
    runs_assign_iff.mpr ⟨inOffReady, by simp [Expr.eval, BinOp.eval, s7, s6, s5, s4, s3, s2, s1, s0, startState,
      show 13 < 2 ^ w by omega, show root + 13 < 2 ^ w by omega, show mem (root + 13) = inOffReady by simpa using hRoot 13 (by simp)], rfl, rfl, rfl⟩
  have h9 : Runs w p ω (.assign 13 (.load (.bin .add (.reg 0) (.const 14)))) s8 .normal s9 5 :=
    runs_assign_iff.mpr ⟨oldRootGraph, by simp [Expr.eval, BinOp.eval, s8, s7, s6, s5, s4, s3, s2, s1, s0, startState,
      show 14 < 2 ^ w by omega, show root + 14 < 2 ^ w by omega, show mem (root + 14) = oldRootGraph by simpa using hRoot 14 (by simp)], rfl, rfl, rfl⟩
  have h10 : Runs w p ω (.assign 14 (.load (.bin .add (.reg 0) (.const 15)))) s9 .normal s10 5 :=
    runs_assign_iff.mpr ⟨intCap, by simp [Expr.eval, BinOp.eval, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, startState,
      show 15 < 2 ^ w by omega, show root + 15 < 2 ^ w by omega, show mem (root + 15) = intCap by simpa using hRoot 15 (by simp)], rfl, rfl, rfl⟩
  have h11 : Runs w p ω (.assign 15 (.load (.reg 13))) s10 .normal s11 3 :=
    runs_assign_iff.mpr ⟨n, by simp [Expr.eval, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, startState,
      show mem oldRootGraph = n by simpa [dgVCapOff] using hDG.2.2.2.1], rfl, rfl, rfl⟩
  have h12 : Runs w p ω (.assign 16 (.load (.bin .add (.reg 13) (.const 1)))) s11 .normal s12 5 :=
    runs_assign_iff.mpr ⟨eCap, by simp [Expr.eval, BinOp.eval, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0,
      startState, show 1 < 2 ^ w by omega, show oldRootGraph + 1 < 2 ^ w by omega,
      show mem (oldRootGraph + 1) = eCap by simpa [dgECapOff] using hDG.2.2.2.2.1], rfl, rfl, rfl⟩
  have h13 : Runs w p ω (.assign 17 (.bin .add (.bin .add (.reg 13) (.const 4)) (.bin .mul (.const 4) (.reg 15))))
      s12 .normal s13 8 :=
    runs_assign_iff.mpr ⟨dgIntToExtBase oldRootGraph n, by
      simp [Expr.eval, BinOp.eval, s12, s11, s10, s9, show 4 < 2 ^ w by omega, show oldRootGraph + 4 < 2 ^ w by omega,
        show 4 * n < 2 ^ w by omega, show oldRootGraph + 4 + 4 * n < 2 ^ w by omega, dgIntToExtBase], rfl, rfl, rfl⟩
  have h14 : Runs w p ω
      (.assign 18 (.bin .add (.bin .add (.bin .add (.reg 13) (.const 4)) (.bin .mul (.const 7) (.reg 15)))
        (.bin .mul (.const 3) (.reg 16)))) s13 .normal s14 12 :=
    runs_assign_iff.mpr ⟨dgETailSlotBase oldRootGraph n eCap, by
      simp [Expr.eval, BinOp.eval, s13, s12, s11, s10, s9, show 4 < 2 ^ w by omega, show 7 < 2 ^ w by omega,
        show 3 < 2 ^ w by omega, show oldRootGraph + 4 < 2 ^ w by omega, show 7 * n < 2 ^ w by omega,
        show oldRootGraph + 4 + 7 * n < 2 ^ w by omega, show 3 * eCap < 2 ^ w by omega,
        show oldRootGraph + 4 + 7 * n + 3 * eCap < 2 ^ w by omega, dgETailSlotBase], rfl, rfl, rfl⟩
  have h15 : Runs w p ω (.assign 19 (.bin .add (.reg 18) (.reg 16))) s14 .normal s15 4 :=
    runs_assign_iff.mpr ⟨dgEHeadSlotBase oldRootGraph n eCap, by
      simp [Expr.eval, BinOp.eval, s14, s13, s12,
        show dgEHeadSlotBase oldRootGraph n eCap < 2 ^ w by unfold dgEHeadSlotBase; omega,
        show dgETailSlotBase oldRootGraph n eCap + eCap = dgEHeadSlotBase oldRootGraph n eCap by
          unfold dgETailSlotBase dgEHeadSlotBase; omega], rfl, rfl, rfl⟩
  have h16 : Runs w p ω (.assign 32 (.bin .add (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 7))) (.const 2)))
      s15 .normal s16 8 :=
    runs_assign_iff.mpr ⟨lm, by
      have hLmEq : table + 2 * d + 2 = lm := by
        dsimp only [lm, solverLevelMetaAddr, solverLvlMAddr, solverN0Addr]; omega
      simp [Expr.eval, BinOp.eval, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2,
        show 2 < 2 ^ w by omega, show 2 * d < 2 ^ w by omega,
        show table + 2 * d < 2 ^ w by omega, hLmEq, show lm < 2 ^ w by omega], rfl, rfl, rfl⟩
  have h17 : Runs w p ω (.assign 22 (.reg 4)) s16 .normal s17 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4,
      s3, s2, s1, s0, startState], rfl, rfl, rfl⟩
  -- Pass 1
  obtain ⟨sA, cA, rA, hcA, hsARegs, hTabA, hFrA⟩ :=
    wireCompactTablesLoop_runs (w := w) (p := p) (ω := ω) (st := s17) (G := G)
      (unrankPtr := unrankPtr) (edgeThresholds := edgeThresholds)
      (edgeRecords := edgeRecords) (intCap := intCap)
      (by simp [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, startState])
      (by simp [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, startState])
      (by simp [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5])
      (by simp [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6])
      hUnr hCapInt hMutDisj.1 hRODisj.1 hRODisj.2.1 (by omega) (by omega) (by omega) (by omega)
  -- Pass 2
  have hOldLenA : EdgeValuesAt sA.mem oldLen0 4 L P G.E oldℓ := by
    intro e he
    have heL : e * L + L ≤ oldLenECap * L := by simpa [Nat.succ_mul] using Nat.mul_le_mul_right L (Nat.succ_le_of_lt (hCapOldLen e he))
    have hag (t : ℕ) (ht : t < L) : sA.mem (oldLen0 + e * L + t) = mem (oldLen0 + e * L + t) :=
      hFrA _ (by rcases hRODisj.2.2.1 with h | h <;> omega) (by rcases hRODisj.2.2.2.1 with h | h <;> omega)
    refine ⟨fun t ht => by rw [hag t ht]; exact (hOldLen e he).1 t ht, ?_⟩
    rw [← (hOldLen e he).2]; unfold Num.fixVal; congr 2; exact Num.intVal_congr hag
  obtain ⟨sB, cB, rB, hcB, hsBRegs, hLenB, hzB, hFrB⟩ :=
    wireCompactLensLoop_runs (st := sA) (G := G) (oldℓ := oldℓ) (oldLen0 := oldLen0)
      (unrankPtr := unrankPtr) (newLen0 := heap) (L := L) (P := P) (eCap := eCap) (oldLenECap := oldLenECap) hCopy
      (by rw [hsARegs 1 (by decide) (by decide)]; simp [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, startState])
      (by rw [hsARegs 2 (by decide) (by decide)]; simp [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, startState])
      (by rw [hsARegs 3 (by decide) (by decide)]; simp [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, startState])
      (by rw [hsARegs 8 (by decide) (by decide)]; simp [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4])
      (by rw [hsARegs 22 (by decide) (by decide)]; simp [s17])
      (fun j hj => (hFrA _ (by rcases hRODisj.1 with h | h <;> omega) (by rcases hRODisj.2.1 with h | h <;> omega)).trans (hUnr j hj))
      hOldLenA hCapE hCapOldLen hOldLenLe hUnrLe (fun a ha => (hFrA a (Or.inr (by omega)) (Or.inr (by omega))).trans (hz a ha))
      (by dsimp only [nextHeap] at hRoom; unfold wireCompactLevel0Space at hRoom; omega) (by omega)
  -- Pass 3
  have hsB_r (r : ℕ) (h20 : r ≠ 20) (h21 : r ≠ 21) (h23 : r ≠ 23) : sB.regs r = s17.regs r :=
    (hsBRegs r h20 h21 h23).trans (hsARegs r h20 h21)
  have hDGB : DynGraphAt sB.mem oldRootGraph n eCap G :=
    hDG.of_agree (fun a h1 h2 => (hFrB a (by omega)).trans
      (hFrA a (by rcases hRODisj.2.2.2.2.1 with h | h <;> omega) (by rcases hRODisj.2.2.2.2.2 with h | h <;> omega)))
  obtain ⟨sC, cC, rC, hcC, hsC30, hsCRegs, hDG1C, hDG2C, hR14C, hLM0C, hLMdC, hzC, hFrC⟩ :=
    wireCompactGraphsStmt_runs (st := sB) (G := G) (root := root) (unrankPtr := unrankPtr)
      (oldRootGraph := oldRootGraph) (newLen0 := heap) (levelMeta := lm) (d := d) (n := n)
      (eCap := eCap) (L := L) hDGInit
      (by rw [hsB_r 0 (by decide) (by decide) (by decide)]; simp [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, startState])
      (by rw [hsB_r 2 (by decide) (by decide) (by decide)]; simp [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, startState])
      (by rw [hsB_r 3 (by decide) (by decide) (by decide)]; simp [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, startState])
      (by rw [hsB_r 7 (by decide) (by decide) (by decide)]; simp [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3])
      (by rw [hsB_r 8 (by decide) (by decide) (by decide)]; simp [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4])
      (by rw [hsB_r 13 (by decide) (by decide) (by decide)]; simp [s17, s16, s15, s14, s13, s12, s11, s10, s9])
      (by rw [hsB_r 15 (by decide) (by decide) (by decide)]; simp [s17, s16, s15, s14, s13, s12, s11])
      (by rw [hsB_r 16 (by decide) (by decide) (by decide)]; simp [s17, s16, s15, s14, s13, s12])
      (by rw [hsB_r 17 (by decide) (by decide) (by decide)]; simp [s17, s16, s15, s14, s13])
      (by rw [hsB_r 18 (by decide) (by decide) (by decide)]; simp [s17, s16, s15, s14])
      (by rw [hsB_r 19 (by decide) (by decide) (by decide)]; simp [s17, s16, s15])
      (by rw [hsB_r 22 (by decide) (by decide) (by decide)]; simp [s17])
      (by rw [hsB_r 32 (by decide) (by decide) (by decide)]; simp [s17, s16])
      hDGB (fun j hj => (hFrB _ (by omega)).trans
        ((hFrA _ (by rcases hRODisj.1 with h | h <;> omega) (by rcases hRODisj.2.1 with h | h <;> omega)).trans (hUnr j hj)))
      hCapE hRootLe hMetaLe hRGLe hUnrLe (by rcases hMutDisj.2.2.2.1 with h | h <;> omega)
      hdPos hw16 hzB hRoom
  -- Pass 4
  have hsC_r (r : ℕ) (hr : r < 20) : sC.regs r = s17.regs r :=
    (hsCRegs r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
      (hsB_r r (by omega) (by omega) (by omega))
  obtain ⟨sD, cD, rD, hcD, hR11D, hZeroD, hsDRegs, hFrD⟩ :=
    wireCompactZeroOffReadyStmt_runs (w := w) (p := p) (ω := ω) (st := sC) (root := root)
      (inOffReady := inOffReady) (intCap := intCap)
      (by rw [hsC_r 0 (by decide)]; simp [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, startState])
      (by rw [hsC_r 12 (by decide)]; simp [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8])
      (by rw [hsC_r 14 (by decide)]; simp [s17, s16, s15, s14, s13, s12, s11, s10])
      (by rcases hMutDisj.2.2.2.2.2.2.1 with h | h <;> omega) (by omega) (by omega) (by omega)
  have rRet : Runs w p ω (.ret (.reg 30)) sD (.returned nextHeap) sD 2 :=
    runs_ret_iff.mpr ⟨nextHeap, by rw [Expr.eval, hsDRegs 30 (by decide), hsC30], rfl, rfl, rfl⟩
  have rAll := runs_seq_iff.mpr (Or.inr ⟨s1, 3, _, h1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 5, _, h2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 5, _, h3,
    runs_seq_iff.mpr (Or.inr ⟨s4, 5, _, h4,
    runs_seq_iff.mpr (Or.inr ⟨s5, 5, _, h5,
    runs_seq_iff.mpr (Or.inr ⟨s6, 5, _, h6,
    runs_seq_iff.mpr (Or.inr ⟨s7, 5, _, h7,
    runs_seq_iff.mpr (Or.inr ⟨s8, 5, _, h8,
    runs_seq_iff.mpr (Or.inr ⟨s9, 5, _, h9,
    runs_seq_iff.mpr (Or.inr ⟨s10, 5, _, h10,
    runs_seq_iff.mpr (Or.inr ⟨s11, 3, _, h11,
    runs_seq_iff.mpr (Or.inr ⟨s12, 5, _, h12,
    runs_seq_iff.mpr (Or.inr ⟨s13, 8, _, h13,
    runs_seq_iff.mpr (Or.inr ⟨s14, 12, _, h14,
    runs_seq_iff.mpr (Or.inr ⟨s15, 4, _, h15,
    runs_seq_iff.mpr (Or.inr ⟨s16, 8, _, h16,
    runs_seq_iff.mpr (Or.inr ⟨s17, 2, _, h17,
    runs_seq_iff.mpr (Or.inr ⟨sA, cA, _, rA,
    runs_seq_iff.mpr (Or.inr ⟨sB, cB, _, rB,
    runs_seq_iff.mpr (Or.inr ⟨sC, cC, _, rC,
    runs_seq_iff.mpr (Or.inr ⟨sD, cD, 2, rD, rRet, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hGmLeIntCap : G.m ≤ intCap := by
    have := Finset.card_le_card (fun e he => Finset.mem_range.mpr (hCapInt e he))
    simpa [MGraph.m] using this
  have hD_above (a : ℕ) (ha : heap ≤ a) : sD.mem a = sC.mem a :=
    hFrD a (by omega) (Or.inr (by omega))
  refine ⟨sD, _, rAll, ?_, ?_, ?_,
    hDG1C.of_agree (fun a h1 _ => hD_above a (by omega)),
    hDG2C.of_agree (fun a h1 _ => hD_above a (by omega)),
    (hFrD (root + 14) (by omega) (by rcases hMutDisj.2.2.2.2.2.2.1 with h | h <;> omega)).trans hR14C,
    hR11D,
    (hFrD lm (by rcases hMutDisj.2.2.2.1 with h | h <;> omega)
      (by rcases hMutDisj.2.2.2.2.2.2.2.2.2 with h | h <;> omega)).trans hLM0C,
    (hFrD (lm + d) (by rcases hMutDisj.2.2.2.1 with h | h <;> omega)
      (by rcases hMutDisj.2.2.2.2.2.2.2.2.2 with h | h <;> omega)).trans hLMdC,
    hZeroD,
    ⟨Nat.zero_le _, fun _ h => by omega, fun _ h => by omega,
      fun e he => Or.inl (hZeroD e he), fun e he h1 => by rw [hZeroD e he] at h1; omega⟩,
    fun a ha => (hD_above a (by unfold nextHeap wireCompactLevel0Space at ha; omega)).trans (hzC a ha),
    fun a ha hNotM => by
      refine (hFrD a (fun h => hNotM (Or.inl h))
        (by by_contra h; push Not at h; exact hNotM (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))).trans ?_
      refine (hFrC a (by omega) (fun h => hNotM (Or.inr (Or.inl h)))
        (fun h => hNotM (Or.inr (Or.inr (Or.inl h))))
        (fun h => hNotM (Or.inr (Or.inr (Or.inr (Or.inl h)))))).trans ?_
      exact (hFrB a ha).trans (hFrA a
        (by by_contra h; push Not at h; exact hNotM (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1, by omega⟩))))))
        (by by_contra h; push Not at h; exact hNotM (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1, by omega⟩))))))))⟩
  · clear rAll h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 rA rB rC rD rRet
      hTabA hFrA hLenB hzB hFrB hDG1C hDG2C hR14C hLM0C hLMdC hzC hFrC hR11D hZeroD hFrD hD_above
    have hm : G.m * (17 * L + 50) + 1100 * G.m + 40 * G.m = G.m * (17 * L + 1190) := by ring
    have hmLe : G.m * (17 * L + 1190) ≤ G.m * (17 * L + 1300) := Nat.mul_le_mul_left _ (by omega)
    dsimp [wireCompactLevel0Cost]; omega
  · intro j hj
    have h1 := hFrD (edgeThresholds + j) (by rcases hMutDisj.2.2.2.2.1 with h | h <;> omega)
      (by rcases hMutDisj.2.1 with h | h <;> omega)
    have h2 := hFrD (edgeRecords + j) (by rcases hMutDisj.2.2.2.2.2.1 with h | h <;> omega)
      (by rcases hMutDisj.2.2.1 with h | h <;> omega)
    have h1c := hFrC (edgeThresholds + j) (by omega) (by rcases hMutDisj.2.2.2.2.1 with h | h <;> omega)
      (by rcases hMutDisj.2.2.2.2.2.2.2.1 with h | h <;> omega)
      (by rcases hMutDisj.2.2.2.2.2.2.2.1 with h | h <;> omega)
    have h2c := hFrC (edgeRecords + j) (by omega) (by rcases hMutDisj.2.2.2.2.2.1 with h | h <;> omega)
      (by rcases hMutDisj.2.2.2.2.2.2.2.2.1 with h | h <;> omega)
      (by rcases hMutDisj.2.2.2.2.2.2.2.2.1 with h | h <;> omega)
    exact ⟨h1.trans (h1c.trans ((hFrB _ (by omega)).trans (hTabA j hj).1)),
      h2.trans (h2c.trans ((hFrB _ (by omega)).trans (hTabA j hj).2))⟩
  · intro j hj
    have hjM : j < G.m := by simpa [MGraph.compact, MGraph.m] using hj
    have hjL : j * L + L ≤ eCap * L := by
      have : G.m ≤ eCap := by
        have := Finset.card_le_card (fun e he => Finset.mem_range.mpr (hCapE e he))
        simpa [MGraph.m] using this
      simpa [Nat.succ_mul] using Nat.mul_le_mul_right L (by omega : j + 1 ≤ eCap)
    have hag (t : ℕ) (ht : t < L) : sD.mem (heap + j * L + t) = sB.mem (heap + j * L + t) :=
      (hD_above _ (by omega)).trans (hFrC _ (by omega) (by omega) (by omega) (by omega))
    refine ⟨fun t ht => by rw [hag t ht]; exact (hLenB j hj).1 t ht, ?_⟩
    rw [← (hLenB j hj).2]; unfold Num.fixVal; congr 2; exact Num.intVal_congr hag

end MinCostFlow.MinRatio
