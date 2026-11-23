module

public import MinCostFlow.SparseCore.Program.ReadRestartInitOps
public import MinCostFlow.SparseCore.Program.ReadLoops
public import MinCostFlow.DynSpanner.Program.DynGraphInit

import WordRAM.Tactic

/-!
# Branch initialization procedures and first half of verification (`ReadRestartInitSetup`)

Defines `initGraphFromExportStmt`, `initVertsFromExportStmt`, `readInitSetupStmt`,
`readInitPart1Stmt`, `readInitPart2Stmt`, `readInitStmt`, and `readInitProcs`. Proves the
export-initialization contracts (`initGraphFromExport_meetsContract`,
`initVertsFromExport_meetsContract`), the contiguous layout space bound (`readInit_space_le`),
the header-setup run lemma (`readInitSetup_runs`), and Part 1 (`readInitPart1_runs`: header +
`T`, `F`, `roots`, `S`, `G`). Part 2 and `readInit_runs` are in `ReadRestartInit.lean`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program.Read

open WordRAM MinCostFlow.MinRatio MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program MinCostFlow.SparseCore.Program.Restart

/-! ## Procedures -/

/-- `[gPtr, vCap, eCap, d]`: initialize `DynGraphAt` at `gPtr` from the `ExportAt` descriptor `d`. -/
def initGraphFromExportStmt (bBatch : ℕ) : Stmt :=
  .assign 4 (.load (.reg 3)) ;;
  .assign 5 (.load (.bin .add (.reg 3) (.const 1))) ;;
  .assign 6 (.load (.bin .add (.reg 3) (.const 2))) ;;
  .assign 7 (.load (.bin .add (.reg 3) (.const 3))) ;;
  .call 8 (bBatch + dgIdxInitFromLists) [.reg 0, .reg 1, .reg 2, .reg 4, .reg 5, .reg 6, .reg 7] ;;
  .ret (.const 0)

/-- `[gPtr, vCap, eCap, d]`: initialize a vertex-only `DynGraphAt` (`E = ∅`) at `gPtr` from the
vertex list of the `ExportAt` descriptor `d`. -/
def initVertsFromExportStmt (bBatch : ℕ) : Stmt :=
  .assign 4 (.load (.reg 3)) ;;
  .assign 5 (.load (.bin .add (.reg 3) (.const 1))) ;;
  .call 6 (bBatch + dgIdxInitFromLists)
    [.reg 0, .reg 1, .reg 2, .reg 4, .reg 5, .const 0, .const 0] ;;
  .ret (.const 0)

/-- Computes all block pointers in `r13..r25`. -/
def readInitSetupRegsStmt : Stmt :=
  .assign 13 (.bin .add (.bin .add (.const 4) (.bin .mul (.const 7) (.reg 0)))
    (.bin .mul (.const 9) (.reg 2))) ;;
  .assign 14 (.bin .add (.bin .add (.const 4) (.bin .mul (.const 7) (.reg 0)))
    (.bin .mul (.const 9) (.reg 1))) ;;
  .assign 15 (.bin .mul (.reg 1) (.reg 3)) ;;
  .assign 16 (.bin .add (.reg 12) (.const 11)) ;;
  .assign 17 (.bin .add (.reg 16) (.reg 13)) ;;
  .assign 18 (.bin .add (.reg 17) (.reg 13)) ;;
  .assign 19 (.bin .add (.reg 18) (.reg 0)) ;;
  .assign 20 (.bin .add (.reg 19) (.reg 14)) ;;
  .assign 21 (.bin .add (.reg 20) (.reg 14)) ;;
  .assign 22 (.bin .add (.reg 21) (.reg 15)) ;;
  .assign 23 (.bin .add (.reg 22) (.reg 15)) ;;
  .assign 24 (.bin .add (.reg 23) (.reg 14)) ;;
  .assign 25 (.bin .add (.reg 24) (.reg 13))

/-- Writes the 11 header words at `h .. h + 10` from registers `r3, r12, r16..r24`. -/
def readInitSetupHdrStmt : Stmt :=
  .store (.reg 12) (.reg 16) ;;
  .store (.bin .add (.reg 12) (.const 1)) (.reg 17) ;;
  .store (.bin .add (.reg 12) (.const 2)) (.reg 18) ;;
  .store (.bin .add (.reg 12) (.const 3)) (.bin .add (.reg 12) (.const 7)) ;;
  .store (.bin .add (.reg 12) (.const 4)) (.reg 3) ;;
  .store (.bin .add (.reg 12) (.const 5)) (.reg 19) ;;
  .store (.bin .add (.reg 12) (.const 6)) (.reg 20) ;;
  .store (.bin .add (.reg 12) (.const 7)) (.reg 21) ;;
  .store (.bin .add (.reg 12) (.const 8)) (.reg 22) ;;
  .store (.bin .add (.reg 12) (.const 9)) (.reg 23) ;;
  .store (.bin .add (.reg 12) (.const 10)) (.reg 24)

/-- Header-setup prefix of `readInitStmt`: computes all block pointers in `r13..r25` and writes the
11 header words at `h .. h + 10`. -/
def readInitSetupStmt : Stmt :=
  readInitSetupRegsStmt ;; readInitSetupHdrStmt

/-- First half of initialization: header setup and initialization of `T`, `F`, `roots`, `S`, `G`. -/
def readInitPart1Stmt (bLoop bSelf : ℕ) : Stmt :=
  readInitSetupStmt ;;
  .call 28 (bSelf + 0) [.reg 16, .reg 0, .reg 2, .reg 5] ;;
  .call 28 (bSelf + 0) [.reg 17, .reg 0, .reg 2, .reg 6] ;;
  .call 28 (bLoop + readIdxSetRoots) [.reg 18, .reg 7, .reg 8] ;;
  .call 28 (bSelf + 0) [.reg 19, .reg 0, .reg 1, .reg 11] ;;
  .call 28 (bSelf + 0) [.reg 20, .reg 0, .reg 1, .reg 4]

/-- Stretch copy and vertex-only initialization of `live` and `frz`. -/
def readInitPart2aStmt (bInitOps bSelf : ℕ) : Stmt :=
  .assign 26 (.bin .add (.bin .add (.bin .add (.reg 20) (.const 4))
    (.bin .mul (.const 7) (.reg 0))) (.reg 1)) ;;
  .assign 27 (.load (.bin .add (.reg 20) (.const 3))) ;;
  .call 28 (bInitOps + readInitOpsIdxStretch)
    [.reg 26, .reg 27, .reg 3, .reg 9, .reg 10, .reg 21, .reg 22] ;;
  .call 28 (bSelf + 1) [.reg 23, .reg 0, .reg 1, .reg 4] ;;
  .call 28 (bSelf + 1) [.reg 24, .reg 0, .reg 2, .reg 4]

/-- Edge split of `T` into `live` and `frz`, followed by returning `hEnd`. -/
def readInitPart2bStmt (bInitOps : ℕ) : Stmt :=
  .assign 26 (.load (.bin .add (.reg 5) (.const 2))) ;;
  .assign 27 (.load (.bin .add (.reg 5) (.const 3))) ;;
  .call 28 (bInitOps + readInitOpsIdxSplitT) [.reg 20, .reg 23, .reg 24, .reg 27, .reg 26] ;;
  .ret (.reg 25)

/-- Uniform branch initialization `[vCap, eCap, tCap, L_w, gD, tD, fD, rootsPtr, nR, numPtr,
denPtr, sD, h]`. Returns `hEnd`. -/
def readInitStmt (bLoop bInitOps bSelf : ℕ) : Stmt :=
  readInitPart1Stmt bLoop bSelf ;; readInitPart2aStmt bInitOps bSelf ;; readInitPart2bStmt bInitOps

def readInitIdxGraph : ℕ := 0
def readInitIdxVerts : ℕ := 1
def readInitIdxMain : ℕ := 2

/-- Procedure block for branch initialization. -/
def readInitProcs (bBatch bLoop bInitOps bSelf : ℕ) : List Stmt :=
  [initGraphFromExportStmt bBatch,
   initVertsFromExportStmt bBatch,
   readInitStmt bLoop bInitOps bSelf]

theorem readInitProcs_noRand (bBatch bLoop bInitOps bSelf : ℕ) :
    ∀ s ∈ readInitProcs bBatch bLoop bInitOps bSelf, s.NoRand := by
  intro s hs
  simp only [readInitProcs, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl <;>
    simp [initGraphFromExportStmt, initVertsFromExportStmt, readInitStmt,
      readInitPart1Stmt, readInitPart2aStmt, readInitPart2bStmt, readInitSetupStmt,
      readInitSetupRegsStmt, readInitSetupHdrStmt, Stmt.NoRand]

/-! ## Contracts and proofs of the two export helpers -/

/-- Contract of `initGraphFromExportStmt` (`[gPtr, vCap, eCap, d]`). -/
def initGraphFromExportContract (w vCap eCap : ℕ) (G : MGraph) : Contract where
  pre args mem := ∃ gPtr d hEnd, args = [gPtr, vCap, eCap, d] ∧
    16 ≤ 2 ^ w ∧ gPtr + dynGraphSize vCap eCap < 2 ^ w ∧ hEnd ≤ gPtr ∧ ZeroFrom mem gPtr ∧
    G.IsValid ∧ (∀ v ∈ G.V, v < vCap) ∧ (∀ e ∈ G.E, e < eCap) ∧
    ExportAt mem d hEnd G
  post args mem ret mem' := ∃ gPtr d, args = [gPtr, vCap, eCap, d] ∧ ret = 0 ∧
    DynGraphAt mem' gPtr vCap eCap G ∧
    (∀ a, a < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ a → mem' a = mem a) ∧
    ZeroFrom mem' (gPtr + dynGraphSize vCap eCap)
  cost _ _ := 130 * G.n + 490 * G.m + 140

/-- Contract of `initVertsFromExportStmt` (`[gPtr, vCap, eCap, d]`). -/
def initVertsFromExportContract (w vCap eCap : ℕ) (G : MGraph) : Contract where
  pre args mem := ∃ gPtr d hEnd, args = [gPtr, vCap, eCap, d] ∧
    16 ≤ 2 ^ w ∧ gPtr + dynGraphSize vCap eCap < 2 ^ w ∧ hEnd ≤ gPtr ∧ ZeroFrom mem gPtr ∧
    (∀ v ∈ G.V, v < vCap) ∧ ExportAt mem d hEnd G
  post args mem ret mem' := ∃ gPtr d, args = [gPtr, vCap, eCap, d] ∧ ret = 0 ∧
    DynGraphAt mem' gPtr vCap eCap { V := G.V, E := ∅, tail := fun _ => 0, head := fun _ => 0 } ∧
    (∀ a, a < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ a → mem' a = mem a) ∧
    ZeroFrom mem' (gPtr + dynGraphSize vCap eCap)
  cost _ _ := 130 * G.n + 130

theorem initGraphFromExport_meetsContract {w vCap eCap : ℕ} {p : Program}
    {bOps bEdge bSplit bBatch bLoop bInitOps bSelf : ℕ} {G : MGraph}
    (hpSelf : p.HasAt bSelf (readInitProcs bBatch bLoop bInitOps bSelf))
    (hpBatch : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps)) (hpOps : p.HasAt bOps dgOpsProcs) :
    MeetsContract w p (bSelf + readInitIdxGraph) (initGraphFromExportContract w vCap eCap G) := by
  refine meetsContract_of_runs
    (hpSelf.get (i := readInitIdxGraph) (by simp [readInitProcs, readInitIdxGraph])) ?_
  rintro args mem pos ω hargs
    ⟨gPtr, d, hEnd, rfl, hw16, hbound, hle, hz, hval, hvCap, heCap, hExp⟩
  simp only [readInitProcs, readInitIdxGraph, List.getElem_cons_zero, initGraphFromExportStmt]
  obtain ⟨hn, hm, _, hvMem, heNd, heSpec, heCov, hd4, _, _, hvEnd, heEnd⟩ := hExp
  set vL := readList mem (mem (d + 1)) (mem d)
  set eT := readTriples mem (mem (d + 3)) (mem (d + 2))
  have hargs7 : ∀ z ∈ [gPtr, vCap, eCap, mem d, mem (d + 1), mem (d + 2), mem (d + 3)],
      z < 2 ^ w := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro z (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact hargs _ (by simp)
    · exact hargs _ (by simp)
    · exact hargs _ (by simp)
    · omega
    · omega
    · omega
    · omega
  apply runs_start_le
  refine runs_seq_assign_le (v := mem d)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [startState])) rfl) ?_
  refine runs_seq_assign_le (v := mem (d + 1))
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_const (by omega)) (by omega)) rfl) ?_
  refine runs_seq_assign_le (v := mem (d + 2))
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_const (by omega)) (by omega)) rfl) ?_
  refine runs_seq_assign_le (v := mem (d + 3))
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_const (by omega)) (by omega)) rfl) ?_
  refine runs_seq_call_le (dgInitFromLists_meetsContract (G := G) (vL := vL) (eEdges := eT)
      hpBatch hpEdge hpOps)
    (vs := [gPtr, vCap, eCap, mem d, mem (d + 1), mem (d + 2), mem (d + 3)])
    (by simp [evalArgs, Expr.eval, startState]) hargs7
    ⟨gPtr, mem d, mem (d + 1), mem (d + 2), mem (d + 3), rfl, hw16, hbound, hz, hval, hvCap,
      heCap, by simp [vL, readList],
      fun i hi => by simp only [vL, readList, List.getElem_map, List.getElem_range]; rfl,
      hvMem, fun i hi => by omega, by simp [eT, readTriples], heNd,
      fun i hi => by simp only [eT, readTriples, List.getElem_map, List.getElem_range]; exact ⟨rfl, rfl, rfl⟩,
      heSpec, heCov, fun i hi => by omega⟩ ?_
  rintro _ mem' pos' ⟨_, _, _, _, _, hEq, _, hG', hfr', hz'⟩
  simp only [List.cons.injEq, true_and, and_true] at hEq
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hEq
  refine runs_ret_le (v := 0) (Expr.eval_const (by omega)) ⟨gPtr, d, rfl, rfl, hG', hfr', hz'⟩ ?_
  simp only [initGraphFromExportContract, dgInitFromListsContract, argsSize, Expr.size,
    List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, hn, hm]
  omega

theorem initVertsFromExport_meetsContract {w vCap eCap : ℕ} {p : Program}
    {bOps bEdge bSplit bBatch bLoop bInitOps bSelf : ℕ} {G : MGraph}
    (hpSelf : p.HasAt bSelf (readInitProcs bBatch bLoop bInitOps bSelf))
    (hpBatch : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps)) (hpOps : p.HasAt bOps dgOpsProcs) :
    MeetsContract w p (bSelf + readInitIdxVerts) (initVertsFromExportContract w vCap eCap G) := by
  refine meetsContract_of_runs
    (hpSelf.get (i := readInitIdxVerts) (by simp [readInitProcs, readInitIdxVerts])) ?_
  rintro args mem pos ω hargs ⟨gPtr, d, hEnd, rfl, hw16, hbound, hle, hz, hvCap, hExp⟩
  simp only [readInitProcs, readInitIdxVerts, List.getElem_cons_succ, List.getElem_cons_zero,
    initVertsFromExportStmt]
  obtain ⟨hn, _, _, hvMem, _, _, _, hd4, _, _, hvEnd, _⟩ := hExp
  set vL := readList mem (mem (d + 1)) (mem d)
  let VGraph : MGraph := { V := G.V, E := ∅, tail := fun _ => 0, head := fun _ => 0 }
  have hargs7 : ∀ z ∈ [gPtr, vCap, eCap, mem d, mem (d + 1), 0, 0], z < 2 ^ w := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro z (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact hargs _ (by simp)
    · exact hargs _ (by simp)
    · exact hargs _ (by simp)
    · omega
    · omega
    · omega
    · omega
  apply runs_start_le
  refine runs_seq_assign_le (v := mem d)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [startState])) rfl) ?_
  refine runs_seq_assign_le (v := mem (d + 1))
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_const (by omega)) (by omega)) rfl) ?_
  refine runs_seq_call_le (dgInitFromLists_meetsContract (G := VGraph) (vL := vL) (eEdges := [])
      hpBatch hpEdge hpOps)
    (vs := [gPtr, vCap, eCap, mem d, mem (d + 1), 0, 0])
    (by simp [evalArgs, Expr.eval, startState, show (0 : ℕ) < 2 ^ w by omega]) hargs7
    ⟨gPtr, mem d, mem (d + 1), 0, 0, rfl, hw16, hbound, hz,
      fun _ h => absurd h (Finset.notMem_empty _), hvCap, fun _ h => absurd h (Finset.notMem_empty _),
      by simp [vL, readList],
      fun i hi => by simp only [vL, readList, List.getElem_map, List.getElem_range]; rfl,
      hvMem, fun i hi => by omega, rfl, List.nodup_nil, fun _ hi => absurd hi (Nat.not_lt_zero _),
      fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h (Finset.notMem_empty _),
      fun _ hi => absurd hi (Nat.not_lt_zero _)⟩ ?_
  rintro _ mem' pos' ⟨_, _, _, _, _, hEq, _, hG', hfr', hz'⟩
  simp only [List.cons.injEq, true_and, and_true] at hEq
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hEq
  refine runs_ret_le (v := 0) (Expr.eval_const (by omega)) ⟨gPtr, d, rfl, rfl, hG', hfr', hz'⟩ ?_
  simp only [initVertsFromExportContract, dgInitFromListsContract, argsSize, Expr.size,
    List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, hn]
  omega

/-! ## Layout, space bound, setup, and Part 1 -/

/-- Exact contiguous block layout created by `readInitStmt` starting at `h`. -/
def readInitPtrs (h vCap eCap tCap L_w : ℕ) : ReadPtrs × ℕ × ℕ × ℕ :=
  let Dt := dynGraphSize vCap tCap
  let De := dynGraphSize vCap eCap
  let qt := h + 11
  let qf := qt + Dt
  let qroots := qf + Dt
  let qs := qroots + vCap
  let qg := qs + De
  let qnum := qg + De
  let qden := qnum + eCap * L_w
  let live := qden + eCap * L_w
  let frz := live + De
  let hEnd := frz + Dt
  (⟨qt, qf, qroots, qs, qg, qnum, qden⟩, live, frz, hEnd)

theorem readInit_space_le {vCap eCap tCap L_w x mul : ℕ}
    (he : eCap ≤ tCap) (hL : 1 ≤ L_w) (hmul : 60 ≤ mul) :
    (readInitPtrs 0 vCap eCap tCap L_w).2.2.2 ≤ readSpace mul vCap tCap L_w x := by
  dsimp only [readInitPtrs, dynGraphSize, readSpace]
  have h1 : 2 * (eCap * L_w) ≤ 2 * (tCap * L_w) :=
    Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right L_w he)
  have h2 : 35 + 43 * vCap + 27 * tCap + 27 * eCap + 2 * (tCap * L_w) ≤
      60 * (vCap + tCap + x + 1) * (L_w + 1) := by
    have ha : 35 + 43 * vCap + 27 * tCap + 27 * eCap + 2 * (tCap * L_w) ≤
        54 * (vCap + tCap + 1) + 2 * (tCap * L_w) := by omega
    have hb : 54 * (vCap + tCap + 1) + 2 * (tCap * L_w) ≤
        60 * (vCap + tCap + 1) * (L_w + 1) := by nlinarith
    have hc : 60 * (vCap + tCap + 1) * (L_w + 1) ≤
        60 * (vCap + tCap + x + 1) * (L_w + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
    omega
  have h3 : 60 * (vCap + tCap + x + 1) * (L_w + 1) ≤
      mul * (vCap + tCap + x + 1) * (L_w + 1) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hmul)
  omega

/-- Bundled register equalities after `readInitSetupStmt`. -/
structure ReadInitRegs (regs : ℕ → ℕ)
    (vCap eCap tCap L_w gD tD fD rootsPtr nR numPtr denPtr sD h
      qt qf qroots qs qg qnum qden live frz hEnd : ℕ) : Prop where
  r0 : regs 0 = vCap
  r1 : regs 1 = eCap
  r2 : regs 2 = tCap
  r3 : regs 3 = L_w
  r4 : regs 4 = gD
  r5 : regs 5 = tD
  r6 : regs 6 = fD
  r7 : regs 7 = rootsPtr
  r8 : regs 8 = nR
  r9 : regs 9 = numPtr
  r10 : regs 10 = denPtr
  r11 : regs 11 = sD
  r12 : regs 12 = h
  r16 : regs 16 = qt
  r17 : regs 17 = qf
  r18 : regs 18 = qroots
  r19 : regs 19 = qs
  r20 : regs 20 = qg
  r21 : regs 21 = qnum
  r22 : regs 22 = qden
  r23 : regs 23 = live
  r24 : regs 24 = frz
  r25 : regs 25 = hEnd

/-- Bundled 11-word header equalities written at `h .. h + 10`. -/
structure ReadInitHdr (mem : ℕ → ℕ)
    (h L_w qt qf qroots qs qg qnum qden live frz : ℕ) : Prop where
  h0 : mem h = qt
  h1 : mem (h + 1) = qf
  h2 : mem (h + 2) = qroots
  h3 : mem (h + 3) = h + 7
  h4 : mem (h + 4) = L_w
  h5 : mem (h + 5) = qs
  h6 : mem (h + 6) = qg
  h7 : mem (h + 7) = qnum
  h8 : mem (h + 8) = qden
  h9 : mem (h + 9) = live
  h10 : mem (h + 10) = frz

theorem exportAt_of_agree {m₁ m₂ : ℕ → ℕ} {d h : ℕ} {G : MGraph}
    (hExp : ExportAt m₁ d h G) (hag : ∀ a < h, m₂ a = m₁ a) : ExportAt m₂ d h G := by
  obtain ⟨hn, hm, hndV, hvMem, hndE, heSpec, heCov, hd4, hd1, hd3, hvEnd, heEnd⟩ := hExp
  have h0 : m₂ d = m₁ d := hag d (by omega)
  have h1 : m₂ (d + 1) = m₁ (d + 1) := hag (d + 1) (by omega)
  have h2 : m₂ (d + 2) = m₁ (d + 2) := hag (d + 2) (by omega)
  have h3 : m₂ (d + 3) = m₁ (d + 3) := hag (d + 3) (by omega)
  have hvL : readList m₂ (m₂ (d + 1)) (m₂ d) = readList m₁ (m₁ (d + 1)) (m₁ d) := by
    rw [h0, h1]
    exact List.map_congr_left fun i hi => hag _ (by rw [List.mem_range] at hi; omega)
  have heT : readTriples m₂ (m₂ (d + 3)) (m₂ (d + 2)) = readTriples m₁ (m₁ (d + 3)) (m₁ (d + 2)) := by
    rw [h2, h3]
    exact List.map_congr_left fun i hi => by
      rw [List.mem_range] at hi; rw [hag _ (by omega), hag _ (by omega), hag _ (by omega)]
  refine ⟨h0.trans hn, h2.trans hm, ?_, ?_, ?_, ?_, ?_, hd4, h1 ▸ hd1, h3 ▸ hd3,
    h0 ▸ h1 ▸ hvEnd, h2 ▸ h3 ▸ heEnd⟩
  · rwa [hvL]
  · rwa [hvL]
  · rwa [heT]
  · rwa [heT]
  · rwa [heT]

private theorem rootsAt_empty_of_zeroFrom {mem : ℕ → ℕ} {a vCap : ℕ} (hz : ZeroFrom mem a) :
    RootsAt mem a vCap ∅ :=
  ⟨fun _ h => absurd h (Finset.notMem_empty _),
   fun x _ => Or.inr ⟨Finset.notMem_empty _, hz (a + x) (by omega)⟩⟩

private theorem upd11_get {mem : ℕ → ℕ} {h v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : ℕ} :
    let m := Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update mem h v0) (h + 1) v1) (h + 2) v2) (h + 3) v3) (h + 4) v4)
      (h + 5) v5) (h + 6) v6) (h + 7) v7) (h + 8) v8) (h + 9) v9) (h + 10) v10
    (m h = v0 ∧ m (h + 1) = v1 ∧ m (h + 2) = v2 ∧ m (h + 3) = v3 ∧ m (h + 4) = v4 ∧
     m (h + 5) = v5 ∧ m (h + 6) = v6 ∧ m (h + 7) = v7 ∧ m (h + 8) = v8 ∧ m (h + 9) = v9 ∧
     m (h + 10) = v10) ∧ (∀ a, a < h ∨ h + 11 ≤ a → m a = mem a) := by
  intro m
  have hne : ∀ {x y : ℕ}, x ≠ y → ∀ (f : ℕ → ℕ) (v : ℕ), Function.update f y v x = f x :=
    fun h f v => Function.update_of_ne h v f
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    fun a ha => by dsimp [m]; repeat rw [hne (by omega)]⟩ <;>
    (dsimp [m]; repeat first | exact Function.update_self .. | rw [hne (by omega)])

private theorem step_assign {w r v c : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s : Stmt}
    {mem regs : ℕ → ℕ} {pos : ℕ} {o : Outcome} {st' : State}
    (he : e.eval w ⟨mem, regs, pos⟩ = some v)
    (hr : Runs w p ω s ⟨mem, Function.update regs r v, pos⟩ o st' c) :
    Runs w p ω (.assign r e ;; s) ⟨mem, regs, pos⟩ o st' ((e.size + 1) + c + 1) :=
  runs_seq_iff.mpr (Or.inr ⟨_, e.size + 1, c, runs_assign_iff.mpr ⟨v, he, rfl, rfl, rfl⟩, hr, rfl⟩)

private theorem step_assign_ex {w r v k B : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s : Stmt}
    {mem regs : ℕ → ℕ} {pos : ℕ} {P : (ℕ → ℕ) → Prop}
    (he : e.eval w ⟨mem, regs, pos⟩ = some v)
    (hnext : ∀ regs', regs' r = v → (∀ j, j ≠ r → regs' j = regs j) →
      ∃ regs'' c', Runs w p ω s ⟨mem, regs', pos⟩ .normal ⟨mem, regs'', pos⟩ c' ∧
        P regs'' ∧ (k + e.size + 2) + c' ≤ B) :
    ∃ regs'' c', Runs w p ω (.assign r e ;; s) ⟨mem, regs, pos⟩ .normal ⟨mem, regs'', pos⟩ c' ∧
      P regs'' ∧ k + c' ≤ B := by
  obtain ⟨regs'', c0, hr, hP, hc⟩ := hnext (Function.update regs r v)
    (Function.update_self ..) (fun j hj => Function.update_of_ne hj v regs)
  exact ⟨regs'', (e.size + 1) + c0 + 1, step_assign he hr, hP, by omega⟩

private theorem step_store {w x v c : ℕ} {p : Program} {ω : ℕ → Bool} {a e : Expr} {s : Stmt}
    {mem regs : ℕ → ℕ} {pos : ℕ} {o : Outcome} {st' : State}
    (ha : a.eval w ⟨mem, regs, pos⟩ = some x) (he : e.eval w ⟨mem, regs, pos⟩ = some v)
    (hr : Runs w p ω s ⟨Function.update mem x v, regs, pos⟩ o st' c) :
    Runs w p ω (.store a e ;; s) ⟨mem, regs, pos⟩ o st' ((a.size + e.size + 1) + c + 1) :=
  runs_seq_iff.mpr (Or.inr ⟨_, a.size + e.size + 1, c,
    runs_store_iff.mpr ⟨x, v, ha, he, rfl, rfl, rfl⟩, hr, rfl⟩)

private theorem readInitSetupRegs_runs {w vCap eCap tCap L_w gD tD fD rootsPtr nR numPtr denPtr sD h
    Dt De qt qf qroots qs qg qnum qden live frz hEnd : ℕ}
    {p : Program} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (hDt : dynGraphSize vCap tCap = Dt) (hDe : dynGraphSize vCap eCap = De)
    (hqt : h + 11 = qt) (hqf : qt + Dt = qf) (hqroots : qf + Dt = qroots)
    (hqs : qroots + vCap = qs) (hqg : qs + De = qg) (hqnum : qg + De = qnum)
    (hqden : qnum + eCap * L_w = qden) (hlive : qden + eCap * L_w = live)
    (hfrz : live + De = frz) (hhEnd : frz + Dt = hEnd) (hEndW : hEnd < 2 ^ w) :
    ∃ st c, Runs w p ω readInitSetupRegsStmt
        (startState [vCap, eCap, tCap, L_w, gD, tD, fD, rootsPtr, nR, numPtr, denPtr, sD, h] mem pos)
        .normal st c ∧
      ReadInitRegs st.regs vCap eCap tCap L_w gD tD fD rootsPtr nR numPtr denPtr sD h
        qt qf qroots qs qg qnum qden live frz hEnd ∧
      st.mem = mem ∧ c ≤ 100 := by
  have hDt_eq : 4 + 7 * vCap + 9 * tCap = Dt := by rw [← hDt]; rfl
  have hDe_eq : 4 + 7 * vCap + 9 * eCap = De := by rw [← hDe]; rfl
  have ⟨h4W, h7W, h9W, h11W, h7v, h47v, h9t, h9e, hDtW, hDeW, heLW⟩ :
      4 < 2 ^ w ∧ 7 < 2 ^ w ∧ 9 < 2 ^ w ∧ 11 < 2 ^ w ∧ 7 * vCap < 2 ^ w ∧
      4 + 7 * vCap < 2 ^ w ∧ 9 * tCap < 2 ^ w ∧ 9 * eCap < 2 ^ w ∧
      4 + 7 * vCap + 9 * tCap < 2 ^ w ∧ 4 + 7 * vCap + 9 * eCap < 2 ^ w ∧
      eCap * L_w < 2 ^ w := by omega
  have ⟨hqtW, hqfW, hqrootsW, hqsW, hqgW, hqnumW, hqdenW, hliveW, hfrzW, hhEndW⟩ :
      h + 11 < 2 ^ w ∧ qt + Dt < 2 ^ w ∧ qf + Dt < 2 ^ w ∧ qroots + vCap < 2 ^ w ∧
      qs + De < 2 ^ w ∧ qg + De < 2 ^ w ∧ qnum + eCap * L_w < 2 ^ w ∧
      qden + eCap * L_w < 2 ^ w ∧ live + De < 2 ^ w ∧ frz + Dt < 2 ^ w := by omega
  clear hw16 hDt hDe hEndW
  generalize hregs0 : (startState [vCap, eCap, tCap, L_w, gD, tD, fD, rootsPtr, nR, numPtr, denPtr, sD, h] mem pos).regs = f0
  have hf0 : f0 0 = vCap ∧ f0 1 = eCap ∧ f0 2 = tCap ∧ f0 3 = L_w ∧ f0 4 = gD ∧ f0 5 = tD ∧
      f0 6 = fD ∧ f0 7 = rootsPtr ∧ f0 8 = nR ∧ f0 9 = numPtr ∧ f0 10 = denPtr ∧
      f0 11 = sD ∧ f0 12 = h := by
    rw [← hregs0]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  suffices hrun : ∃ regs' c, Runs w p ω readInitSetupRegsStmt ⟨mem, f0, pos⟩ .normal
      ⟨mem, regs', pos⟩ c ∧
      ReadInitRegs regs' vCap eCap tCap L_w gD tD fD rootsPtr nR numPtr denPtr sD h
        qt qf qroots qs qg qnum qden live frz hEnd ∧ 0 + c ≤ 100 by
    obtain ⟨regs', c, hr, hR, hc⟩ := hrun
    exact ⟨⟨mem, regs', pos⟩, c, by rwa [← hregs0] at hr, hR, rfl, by simpa using hc⟩
  clear hregs0
  unfold readInitSetupRegsStmt
  refine step_assign_ex (hDt_eq ▸ Expr.eval_add (Expr.eval_add (Expr.eval_const h4W)
    (Expr.eval_mul (Expr.eval_const h7W) (Expr.eval_reg_of_eq hf0.1) h7v) h47v)
    (Expr.eval_mul (Expr.eval_const h9W) (Expr.eval_reg_of_eq hf0.2.2.1) h9t) hDtW)
    fun f13 e13 n13 => ?_
  have p13 : ∀ k < 13, f13 k = f0 k := fun k hk => n13 k (Nat.ne_of_lt hk)
  refine step_assign_ex (hDe_eq ▸ Expr.eval_add (Expr.eval_add (Expr.eval_const h4W)
    (Expr.eval_mul (Expr.eval_const h7W) (Expr.eval_reg_of_eq ((p13 0 (by decide)).trans hf0.1)) h7v) h47v)
    (Expr.eval_mul (Expr.eval_const h9W) (Expr.eval_reg_of_eq ((p13 1 (by decide)).trans hf0.2.1)) h9e) hDeW)
    fun f14 e14 n14 => ?_
  have p14 : ∀ k < 13, f14 k = f0 k := fun k hk => (n14 k (Nat.ne_of_lt (Nat.lt_succ_of_lt hk))).trans (p13 k hk)
  have e13_14 : f14 13 = Dt := (n14 13 (by decide)).trans e13
  refine step_assign_ex (Expr.eval_mul
    (Expr.eval_reg_of_eq ((p14 1 (by decide)).trans hf0.2.1))
    (Expr.eval_reg_of_eq ((p14 3 (by decide)).trans hf0.2.2.2.1)) heLW) fun f15 e15 n15 => ?_
  have p15 : ∀ k < 13, f15 k = f0 k := fun k hk => (n15 k (Nat.ne_of_lt (Nat.lt_trans hk (by decide)))).trans (p14 k hk)
  have e13_15 : f15 13 = Dt := (n15 13 (by decide)).trans e13_14
  have e14_15 : f15 14 = De := (n15 14 (by decide)).trans e14
  refine step_assign_ex (hqt ▸ Expr.eval_add
    (Expr.eval_reg_of_eq ((p15 12 (by decide)).trans hf0.2.2.2.2.2.2.2.2.2.2.2.2))
    (Expr.eval_const h11W) hqtW) fun f16 e16 n16 => ?_
  have p16 : ∀ k < 13, f16 k = f0 k := fun k hk => (n16 k (Nat.ne_of_lt (Nat.lt_trans hk (by decide)))).trans (p15 k hk)
  have e13_16 : f16 13 = Dt := (n16 13 (by decide)).trans e13_15
  have e14_16 : f16 14 = De := (n16 14 (by decide)).trans e14_15
  have e15_16 : f16 15 = eCap * L_w := (n16 15 (by decide)).trans e15
  refine step_assign_ex (hqf ▸ Expr.eval_add (Expr.eval_reg_of_eq e16)
    (Expr.eval_reg_of_eq e13_16) hqfW) fun f17 e17 n17 => ?_
  have p17 : ∀ k < 17, f17 k = f16 k := fun k hk => n17 k (Nat.ne_of_lt hk)
  refine step_assign_ex (hqroots ▸ Expr.eval_add (Expr.eval_reg_of_eq e17)
    (Expr.eval_reg_of_eq ((p17 13 (by decide)).trans e13_16)) hqrootsW) fun f18 e18 n18 => ?_
  have p18 : ∀ k < 18, f18 k = f17 k := fun k hk => n18 k (Nat.ne_of_lt hk)
  refine step_assign_ex (hqs ▸ Expr.eval_add (Expr.eval_reg_of_eq e18)
    (Expr.eval_reg_of_eq ((p18 0 (by decide)).trans ((p17 0 (by decide)).trans ((p16 0 (by decide)).trans hf0.1))))
    hqsW) fun f19 e19 n19 => ?_
  have p19 : ∀ k < 19, f19 k = f18 k := fun k hk => n19 k (Nat.ne_of_lt hk)
  refine step_assign_ex (hqg ▸ Expr.eval_add (Expr.eval_reg_of_eq e19)
    (Expr.eval_reg_of_eq ((p19 14 (by decide)).trans ((p18 14 (by decide)).trans ((p17 14 (by decide)).trans e14_16))))
    hqgW) fun f20 e20 n20 => ?_
  have p20 : ∀ k < 20, f20 k = f19 k := fun k hk => n20 k (Nat.ne_of_lt hk)
  refine step_assign_ex (hqnum ▸ Expr.eval_add (Expr.eval_reg_of_eq e20)
    (Expr.eval_reg_of_eq ((p20 14 (by decide)).trans ((p19 14 (by decide)).trans ((p18 14 (by decide)).trans ((p17 14 (by decide)).trans e14_16)))))
    hqnumW) fun f21 e21 n21 => ?_
  have p21 : ∀ k < 21, f21 k = f20 k := fun k hk => n21 k (Nat.ne_of_lt hk)
  refine step_assign_ex (hqden ▸ Expr.eval_add (Expr.eval_reg_of_eq e21)
    (Expr.eval_reg_of_eq ((p21 15 (by decide)).trans ((p20 15 (by decide)).trans ((p19 15 (by decide)).trans ((p18 15 (by decide)).trans ((p17 15 (by decide)).trans e15_16))))))
    hqdenW) fun f22 e22 n22 => ?_
  have p22 : ∀ k < 22, f22 k = f21 k := fun k hk => n22 k (Nat.ne_of_lt hk)
  refine step_assign_ex (hlive ▸ Expr.eval_add (Expr.eval_reg_of_eq e22)
    (Expr.eval_reg_of_eq ((p22 15 (by decide)).trans ((p21 15 (by decide)).trans ((p20 15 (by decide)).trans ((p19 15 (by decide)).trans ((p18 15 (by decide)).trans ((p17 15 (by decide)).trans e15_16)))))))
    hliveW) fun f23 e23 n23 => ?_
  have p23 : ∀ k < 23, f23 k = f22 k := fun k hk => n23 k (Nat.ne_of_lt hk)
  refine step_assign_ex (hfrz ▸ Expr.eval_add (Expr.eval_reg_of_eq e23)
    (Expr.eval_reg_of_eq ((p23 14 (by decide)).trans ((p22 14 (by decide)).trans ((p21 14 (by decide)).trans ((p20 14 (by decide)).trans ((p19 14 (by decide)).trans ((p18 14 (by decide)).trans ((p17 14 (by decide)).trans e14_16))))))))
    hfrzW) fun f24 e24 n24 => ?_
  have p24 : ∀ k < 24, f24 k = f23 k := fun k hk => n24 k (Nat.ne_of_lt hk)
  have e13_24 : f24 13 = Dt :=
    (p24 13 (by decide)).trans ((p23 13 (by decide)).trans ((p22 13 (by decide)).trans
      ((p21 13 (by decide)).trans ((p20 13 (by decide)).trans ((p19 13 (by decide)).trans
        ((p18 13 (by decide)).trans ((p17 13 (by decide)).trans e13_16)))))))
  refine ⟨Function.update f24 25 hEnd, _,
    runs_assign_iff.mpr ⟨hEnd, hhEnd ▸ Expr.eval_add (Expr.eval_reg_of_eq e24)
      (Expr.eval_reg_of_eq e13_24) hhEndW, rfl, rfl, rfl⟩, ?_, by dsimp [Expr.size]; decide⟩
  have p25 : ∀ k < 25, Function.update f24 25 hEnd k = f24 k := fun k hk =>
    Function.update_of_ne (Nat.ne_of_lt hk) hEnd f24
  have lo : ∀ k < 13, Function.update f24 25 hEnd k = f0 k := fun k hk =>
    (p25 k (Nat.lt_trans hk (by decide))).trans ((p24 k (Nat.lt_trans hk (by decide))).trans
      ((p23 k (Nat.lt_trans hk (by decide))).trans ((p22 k (Nat.lt_trans hk (by decide))).trans
      ((p21 k (Nat.lt_trans hk (by decide))).trans ((p20 k (Nat.lt_trans hk (by decide))).trans
      ((p19 k (Nat.lt_trans hk (by decide))).trans ((p18 k (Nat.lt_trans hk (by decide))).trans
      ((p17 k (Nat.lt_trans hk (by decide))).trans (p16 k hk)))))))))
  exact ⟨(lo 0 (by decide)).trans hf0.1, (lo 1 (by decide)).trans hf0.2.1,
    (lo 2 (by decide)).trans hf0.2.2.1, (lo 3 (by decide)).trans hf0.2.2.2.1,
    (lo 4 (by decide)).trans hf0.2.2.2.2.1, (lo 5 (by decide)).trans hf0.2.2.2.2.2.1,
    (lo 6 (by decide)).trans hf0.2.2.2.2.2.2.1, (lo 7 (by decide)).trans hf0.2.2.2.2.2.2.2.1,
    (lo 8 (by decide)).trans hf0.2.2.2.2.2.2.2.2.1, (lo 9 (by decide)).trans hf0.2.2.2.2.2.2.2.2.2.1,
    (lo 10 (by decide)).trans hf0.2.2.2.2.2.2.2.2.2.2.1, (lo 11 (by decide)).trans hf0.2.2.2.2.2.2.2.2.2.2.2.1,
    (lo 12 (by decide)).trans hf0.2.2.2.2.2.2.2.2.2.2.2.2,
    (p25 16 (by decide)).trans ((p24 16 (by decide)).trans ((p23 16 (by decide)).trans ((p22 16 (by decide)).trans ((p21 16 (by decide)).trans ((p20 16 (by decide)).trans ((p19 16 (by decide)).trans ((p18 16 (by decide)).trans ((p17 16 (by decide)).trans e16)))))))),
    (p25 17 (by decide)).trans ((p24 17 (by decide)).trans ((p23 17 (by decide)).trans ((p22 17 (by decide)).trans ((p21 17 (by decide)).trans ((p20 17 (by decide)).trans ((p19 17 (by decide)).trans ((p18 17 (by decide)).trans e17))))))),
    (p25 18 (by decide)).trans ((p24 18 (by decide)).trans ((p23 18 (by decide)).trans ((p22 18 (by decide)).trans ((p21 18 (by decide)).trans ((p20 18 (by decide)).trans ((p19 18 (by decide)).trans e18)))))),
    (p25 19 (by decide)).trans ((p24 19 (by decide)).trans ((p23 19 (by decide)).trans ((p22 19 (by decide)).trans ((p21 19 (by decide)).trans ((p20 19 (by decide)).trans e19))))),
    (p25 20 (by decide)).trans ((p24 20 (by decide)).trans ((p23 20 (by decide)).trans ((p22 20 (by decide)).trans ((p21 20 (by decide)).trans e20)))),
    (p25 21 (by decide)).trans ((p24 21 (by decide)).trans ((p23 21 (by decide)).trans ((p22 21 (by decide)).trans e21))),
    (p25 22 (by decide)).trans ((p24 22 (by decide)).trans ((p23 22 (by decide)).trans e22)),
    (p25 23 (by decide)).trans ((p24 23 (by decide)).trans e23),
    (p25 24 (by decide)).trans e24, Function.update_self ..⟩

private theorem readInitSetupHdr_runs {w vCap eCap tCap L_w gD tD fD rootsPtr nR numPtr denPtr sD h
    qt qf qroots qs qg qnum qden live frz hEnd : ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w) (hqt : h + 11 = qt) (hqtW : qt < 2 ^ w)
    (hregs : ReadInitRegs st.regs vCap eCap tCap L_w gD tD fD rootsPtr nR numPtr denPtr sD h
      qt qf qroots qs qg qnum qden live frz hEnd) :
    ∃ st' c, Runs w p ω readInitSetupHdrStmt st .normal st' c ∧
      st'.regs = st.regs ∧
      ReadInitHdr st'.mem h L_w qt qf qroots qs qg qnum qden live frz ∧
      (∀ a, a < h ∨ h + 11 ≤ a → st'.mem a = st.mem a) ∧ c ≤ 100 := by
  rcases st with ⟨mem, regs, pos⟩
  dsimp only at hregs ⊢
  set m0 := Function.update mem h qt
  set m1 := Function.update m0 (h + 1) qf
  set m2 := Function.update m1 (h + 2) qroots
  set m3 := Function.update m2 (h + 3) (h + 7)
  set m4 := Function.update m3 (h + 4) L_w
  set m5 := Function.update m4 (h + 5) qs
  set m6 := Function.update m5 (h + 6) qg
  set m7 := Function.update m6 (h + 7) qnum
  set m8 := Function.update m7 (h + 8) qden
  set m9 := Function.update m8 (h + 9) live
  set m10 := Function.update m9 (h + 10) frz
  have hr12 := Expr.eval_reg_of_eq (w := w) (st := ⟨mem, regs, pos⟩) (r := 12) hregs.r12
  have h10 : Runs w p ω (.store (.bin .add (.reg 12) (.const 10)) (.reg 24)) ⟨m9, regs, pos⟩
      .normal ⟨m10, regs, pos⟩ _ :=
    runs_store_iff.mpr ⟨h + 10, frz,
      Expr.eval_add (Expr.eval_reg_of_eq hregs.r12) (Expr.eval_const (by omega)) (by omega),
      Expr.eval_reg_of_eq hregs.r24, rfl, rfl, rfl⟩
  have h9 := step_store (x := h + 9) (v := live) (Expr.eval_add (Expr.eval_reg_of_eq (r := 12) hregs.r12) (Expr.eval_const (by omega)) (by omega)) (Expr.eval_reg_of_eq (r := 23) hregs.r23) h10
  have h8 := step_store (x := h + 8) (v := qden) (Expr.eval_add (Expr.eval_reg_of_eq (r := 12) hregs.r12) (Expr.eval_const (by omega)) (by omega)) (Expr.eval_reg_of_eq (r := 22) hregs.r22) h9
  have h7 := step_store (x := h + 7) (v := qnum) (Expr.eval_add (Expr.eval_reg_of_eq (r := 12) hregs.r12) (Expr.eval_const (by omega)) (by omega)) (Expr.eval_reg_of_eq (r := 21) hregs.r21) h8
  have h6 := step_store (x := h + 6) (v := qg) (Expr.eval_add (Expr.eval_reg_of_eq (r := 12) hregs.r12) (Expr.eval_const (by omega)) (by omega)) (Expr.eval_reg_of_eq (r := 20) hregs.r20) h7
  have h5 := step_store (x := h + 5) (v := qs) (Expr.eval_add (Expr.eval_reg_of_eq (r := 12) hregs.r12) (Expr.eval_const (by omega)) (by omega)) (Expr.eval_reg_of_eq (r := 19) hregs.r19) h6
  have h4 := step_store (x := h + 4) (v := L_w) (Expr.eval_add (Expr.eval_reg_of_eq (r := 12) hregs.r12) (Expr.eval_const (by omega)) (by omega)) (Expr.eval_reg_of_eq (r := 3) hregs.r3) h5
  have h3 := step_store (x := h + 3) (v := h + 7) (Expr.eval_add (Expr.eval_reg_of_eq (r := 12) hregs.r12) (Expr.eval_const (by omega)) (by omega)) (Expr.eval_add (Expr.eval_reg_of_eq (r := 12) hregs.r12) (Expr.eval_const (by omega)) (by omega)) h4
  have h2 := step_store (x := h + 2) (v := qroots) (Expr.eval_add (Expr.eval_reg_of_eq (r := 12) hregs.r12) (Expr.eval_const (by omega)) (by omega)) (Expr.eval_reg_of_eq (r := 18) hregs.r18) h3
  have h1 := step_store (x := h + 1) (v := qf) (Expr.eval_add (Expr.eval_reg_of_eq (r := 12) hregs.r12) (Expr.eval_const (by omega)) (by omega)) (Expr.eval_reg_of_eq (r := 17) hregs.r17) h2
  have h0 := step_store (x := h) (v := qt) hr12 (Expr.eval_reg_of_eq (r := 16) hregs.r16) h1
  obtain ⟨⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩, mfr⟩ :=
    upd11_get (mem := mem) (h := h) (v0 := qt) (v1 := qf) (v2 := qroots) (v3 := h + 7)
      (v4 := L_w) (v5 := qs) (v6 := qg) (v7 := qnum) (v8 := qden) (v9 := live) (v10 := frz)
  exact ⟨⟨m10, regs, pos⟩, _, h0, rfl, ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩, mfr,
    by simp [Expr.size]⟩

private theorem readInitSetup_runs {w vCap eCap tCap L_w gD tD fD rootsPtr nR numPtr denPtr sD h
    Dt De qt qf qroots qs qg qnum qden live frz hEnd : ℕ}
    {p : Program} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (hDt : dynGraphSize vCap tCap = Dt) (hDe : dynGraphSize vCap eCap = De)
    (hqt : h + 11 = qt) (hqf : qt + Dt = qf) (hqroots : qf + Dt = qroots)
    (hqs : qroots + vCap = qs) (hqg : qs + De = qg) (hqnum : qg + De = qnum)
    (hqden : qnum + eCap * L_w = qden) (hlive : qden + eCap * L_w = live)
    (hfrz : live + De = frz) (hhEnd : frz + Dt = hEnd) (hEndW : hEnd < 2 ^ w) :
    ∃ st c, Runs w p ω readInitSetupStmt
        (startState [vCap, eCap, tCap, L_w, gD, tD, fD, rootsPtr, nR, numPtr, denPtr, sD, h] mem pos)
        .normal st c ∧
      ReadInitRegs st.regs vCap eCap tCap L_w gD tD fD rootsPtr nR numPtr denPtr sD h
        qt qf qroots qs qg qnum qden live frz hEnd ∧
      ReadInitHdr st.mem h L_w qt qf qroots qs qg qnum qden live frz ∧
      (∀ a, a < h ∨ h + 11 ≤ a → st.mem a = mem a) ∧ c ≤ 201 := by
  obtain ⟨stR, cR, hrR, hregsR, hmemR, hcR⟩ :=
    readInitSetupRegs_runs (gD := gD) (tD := tD) (fD := fD) (rootsPtr := rootsPtr) (nR := nR)
      (numPtr := numPtr) (denPtr := denPtr) (sD := sD) (p := p) (mem := mem) (pos := pos)
      (ω := ω) hw16 hDt hDe hqt hqf hqroots hqs hqg hqnum hqden hlive hfrz hhEnd hEndW
  obtain ⟨stH, cH, hrH, hregsH, hhdrH, hfrH, hcH⟩ :=
    readInitSetupHdr_runs (p := p) (ω := ω) hw16 hqt (by omega) hregsR
  exact ⟨stH, cR + cH + 1, runs_seq_iff.mpr (Or.inr ⟨stR, cR, cH, hrR, hrH, rfl⟩),
    hregsH ▸ hregsR, hhdrH, fun a ha => (hfrH a ha).trans (congrFun hmemR a), by omega⟩

/-- Part 1 of `readInitStmt`: header setup + initializing `T`, `F`, `roots`, `S`, `G`. -/
theorem readInitPart1_runs {w vCap eCap tCap L_w : ℕ} {p : Program}
    {bOps bEdge bSplit bBatch bLoop bInitOps bSelf : ℕ}
    (hpOps : p.HasAt bOps dgOpsProcs) (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpBatch : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hpLoop : p.HasAt bLoop (readLoopProcs bEdge))
    (hpSelf : p.HasAt bSelf (readInitProcs bBatch bLoop bInitOps bSelf))
    {gD tD fD rootsPtr nR numPtr denPtr sD h Dt De qt qf qroots qs qg qnum qden live frz hEnd : ℕ}
    {v : ReadView} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (hDt : dynGraphSize vCap tCap = Dt) (hDe : dynGraphSize vCap eCap = De)
    (hqt : h + 11 = qt) (hqf : qt + Dt = qf) (hqroots : qf + Dt = qroots)
    (hqs : qroots + vCap = qs) (hqg : qs + De = qg) (hqnum : qg + De = qnum)
    (hqden : qnum + eCap * L_w = qden) (hlive : qden + eCap * L_w = live)
    (hfrz : live + De = frz) (hhEnd : frz + Dt = hEnd) (hhEnd_lt : hEnd < 2 ^ w)
    (hargsW : ∀ a ∈ [gD, tD, fD, rootsPtr, nR, numPtr, denPtr, sD, h], a < 2 ^ w)
    (hInit : ReadInitAt mem h L_w gD tD fD rootsPtr nR numPtr denPtr sD v)
    (hInv : v.Inv vCap eCap tCap) (hz : ZeroFrom mem h) :
    ∃ st5 c5,
      Runs w p ω (readInitPart1Stmt bLoop bSelf)
        (startState [vCap, eCap, tCap, L_w, gD, tD, fD, rootsPtr, nR, numPtr, denPtr, sD, h] mem pos)
        .normal st5 c5 ∧
      ReadInitRegs st5.regs vCap eCap tCap L_w gD tD fD rootsPtr nR numPtr denPtr sD h
        qt qf qroots qs qg qnum qden live frz hEnd ∧
      ReadInitHdr st5.mem h L_w qt qf qroots qs qg qnum qden live frz ∧
      DynGraphAt st5.mem qt vCap tCap v.lsf.T ∧ DynGraphAt st5.mem qf vCap tCap v.lsf.F.F ∧
      RootsAt st5.mem qroots vCap v.lsf.F.R ∧
      DynGraphAt st5.mem qs vCap eCap v.S ∧ DynGraphAt st5.mem qg vCap eCap v.G ∧
      ZeroFrom st5.mem qnum ∧ (∀ a < h, st5.mem a = mem a) ∧
      c5 ≤ 130 * (v.lsf.T.n + v.G.n + v.S.n + v.G.n) +
        490 * (v.lsf.T.m + v.lsf.F.F.m + v.S.m + v.G.m) + 30 * v.lsf.F.R.card + 860 := by
  have hDt_pos : 4 + 7 * vCap + 9 * tCap = Dt := by rw [← hDt]; rfl
  have hDe_pos : 4 + 7 * vCap + 9 * eCap = De := by rw [← hDe]; rfl
  have hvCapW : vCap < 2 ^ w := by omega
  have heCapW : eCap < 2 ^ w := by omega
  have htCapW : tCap < 2 ^ w := by omega
  have hqtW : qt < 2 ^ w := by omega
  have hqfW : qf < 2 ^ w := by omega
  have hqrootsW : qroots < 2 ^ w := by omega
  have hqsW : qs < 2 ^ w := by omega
  have hqgW : qg < 2 ^ w := by omega
  have hgD_W : gD < 2 ^ w := hargsW _ (by simp)
  have htD_W : tD < 2 ^ w := hargsW _ (by simp)
  have hfD_W : fD < 2 ^ w := hargsW _ (by simp)
  have hrootsP_W : rootsPtr < 2 ^ w := hargsW _ (by simp)
  have hnR_W : nR < 2 ^ w := hargsW _ (by simp)
  have hsD_W : sD < 2 ^ w := hargsW _ (by simp)
  obtain ⟨hExpG, hExpT, hExpF, hExpS, ⟨roots, hR_len, hR_nd, hR_set, hR_at, hR_end⟩, _, _⟩ := hInit
  obtain ⟨hGval, hGvCap, hGeCap, he_le_t, hTval, hTV, hTeCap, _, hFV, hFsub, hRsub, _,
    hSval, hSvCap, hSeCap, _⟩ := hInv
  have hFval : v.lsf.F.F.IsValid := fun e he => by
    have heG : e ∈ v.G.E := hFsub.2.1 he
    obtain ⟨ht, hh⟩ := hFsub.2.2 e he; rw [hFV, ht, hh]; exact hGval e heG
  have hFn_eq : v.lsf.F.F.n = v.G.n := by simp [MGraph.n, hFV]
  have hR_card : roots.length = v.lsf.F.R.card := by rw [← hR_set, List.toFinset_card_of_nodup hR_nd]
  obtain ⟨st0, c0, hr0, hregs0, hhdr0, hfr0, hc0⟩ :=
    readInitSetup_runs (gD := gD) (tD := tD) (fD := fD) (rootsPtr := rootsPtr) (nR := nR)
      (numPtr := numPtr) (denPtr := denPtr) (sD := sD) (p := p) (mem := mem) (pos := pos)
      (ω := ω) hw16 hDt hDe hqt hqf hqroots hqs hqg hqnum hqden hlive hfrz hhEnd hhEnd_lt
  have hz0 : ZeroFrom st0.mem qt := fun a ha => by
    rw [hfr0 a (Or.inr (hqt.symm ▸ ha))]; exact hz a (le_trans (Nat.le_add_right h 11) (hqt.symm ▸ ha))
  have hbelow0 : ∀ a < h, st0.mem a = mem a := fun a ha => hfr0 a (Or.inl ha)
  have hC1 := runs_call_of_meetsContract (r := 28)
    (initGraphFromExport_meetsContract (G := v.lsf.T) hpSelf hpBatch hpEdge hpOps)
    (show evalArgs w st0 [.reg 16, .reg 0, .reg 2, .reg 5] = some [qt, vCap, tCap, tD] by
      simp [evalArgs, Expr.eval, hregs0.r16, hregs0.r0, hregs0.r2, hregs0.r5])
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro z (rfl|rfl|rfl|rfl); exacts [hqtW, hvCapW, htCapW, htD_W])
    ⟨qt, tD, h, rfl, hw16, by omega, by omega, hz0, hTval, fun u hu => hGvCap u (hTV ▸ hu),
      hTeCap, exportAt_of_agree hExpT hbelow0⟩ ω
  obtain ⟨st1, c1, _, hr1, ⟨_, _, hEq1, _, hT1, hfr1, hz1⟩, _, hregs1, hc1⟩ := hC1
  simp only [List.cons.injEq, true_and, and_true] at hEq1; obtain ⟨rfl, rfl⟩ := hEq1
  rw [hDt, hqf] at hz1 hfr1
  have hbelow1 : ∀ a < h, st1.mem a = mem a := fun a ha => (hfr1 a (Or.inl (by omega))).trans (hbelow0 a ha)
  have hC2 := runs_call_of_meetsContract (r := 28)
    (initGraphFromExport_meetsContract (G := v.lsf.F.F) hpSelf hpBatch hpEdge hpOps)
    (show evalArgs w st1 [.reg 17, .reg 0, .reg 2, .reg 6] = some [qf, vCap, tCap, fD] by
      simp [evalArgs, Expr.eval, hregs1 17 (by decide), hregs1 0 (by decide), hregs1 2 (by decide),
        hregs1 6 (by decide), hregs0.r17, hregs0.r0, hregs0.r2, hregs0.r6])
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro z (rfl|rfl|rfl|rfl); exacts [hqfW, hvCapW, htCapW, hfD_W])
    ⟨qf, fD, h, rfl, hw16, by omega, by omega, hz1, hFval, fun u hu => hGvCap u (hFV ▸ hu),
      fun e he => lt_of_lt_of_le (hGeCap e (hFsub.2.1 he)) he_le_t,
      exportAt_of_agree hExpF hbelow1⟩ ω
  obtain ⟨st2, c2, _, hr2, ⟨_, _, hEq2, _, hF2, hfr2, hz2⟩, _, hregs2, hc2⟩ := hC2
  simp only [List.cons.injEq, true_and, and_true] at hEq2; obtain ⟨rfl, rfl⟩ := hEq2
  rw [hDt, hqroots] at hz2 hfr2
  have hbelow2 : ∀ a < h, st2.mem a = mem a := fun a ha => (hfr2 a (Or.inl (by omega))).trans (hbelow1 a ha)
  have hC3 := runs_call_of_meetsContract (r := 28)
    (setRoots_meetsContract (vCap := vCap) (R := ∅) (l := roots) hpLoop)
    (show evalArgs w st2 [.reg 18, .reg 7, .reg 8] = some [qroots, rootsPtr, roots.length] by
      simp [evalArgs, Expr.eval, hregs2 18 (by decide), hregs2 7 (by decide), hregs2 8 (by decide),
        hregs1 18 (by decide), hregs1 7 (by decide), hregs1 8 (by decide), hregs0.r18, hregs0.r7, hregs0.r8, hR_len])
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro z (rfl|rfl|rfl); exacts [hqrootsW, hrootsP_W, hR_len.symm ▸ hnR_W])
    ⟨qroots, rootsPtr, rfl, hw16, by omega, by omega,
      fun i hi => (hbelow2 (rootsPtr + i) (by omega)).trans (hR_at i hi),
      fun u hu => hGvCap u (hRsub (hR_set ▸ List.mem_toFinset.mpr hu)),
      fun i hi => Or.inl (by omega), rootsAt_empty_of_zeroFrom hz2⟩ ω
  obtain ⟨st3, c3, _, hr3, ⟨_, _, hEq3, _, hR3, hfr3⟩, _, hregs3, hc3⟩ := hC3
  simp only [List.cons.injEq, and_true] at hEq3; obtain ⟨rfl, rfl⟩ := hEq3
  rw [hqs] at hfr3
  have hz3 : ZeroFrom st3.mem qs := fun a ha => by rw [hfr3 a (Or.inr ha)]; exact hz2 a (by omega)
  have hbelow3 : ∀ a < h, st3.mem a = mem a := fun a ha => (hfr3 a (Or.inl (by omega))).trans (hbelow2 a ha)
  have hC4 := runs_call_of_meetsContract (r := 28)
    (initGraphFromExport_meetsContract (G := v.S) hpSelf hpBatch hpEdge hpOps)
    (show evalArgs w st3 [.reg 19, .reg 0, .reg 1, .reg 11] = some [qs, vCap, eCap, sD] by
      simp [evalArgs, Expr.eval, hregs3 19 (by decide), hregs3 0 (by decide), hregs3 1 (by decide),
        hregs3 11 (by decide), hregs2 19 (by decide), hregs2 0 (by decide), hregs2 1 (by decide),
        hregs2 11 (by decide), hregs1 19 (by decide), hregs1 0 (by decide), hregs1 1 (by decide),
        hregs1 11 (by decide), hregs0.r19, hregs0.r0, hregs0.r1, hregs0.r11])
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro z (rfl|rfl|rfl|rfl); exacts [hqsW, hvCapW, heCapW, hsD_W])
    ⟨qs, sD, h, rfl, hw16, by omega, by omega, hz3, hSval, hSvCap, hSeCap,
      exportAt_of_agree hExpS hbelow3⟩ ω
  obtain ⟨st4, c4, _, hr4, ⟨_, _, hEq4, _, hS4, hfr4, hz4⟩, _, hregs4, hc4⟩ := hC4
  simp only [List.cons.injEq, true_and, and_true] at hEq4; obtain ⟨rfl, rfl⟩ := hEq4
  rw [hDe, hqg] at hz4 hfr4
  have hbelow4 : ∀ a < h, st4.mem a = mem a := fun a ha => (hfr4 a (Or.inl (by omega))).trans (hbelow3 a ha)
  have hC5 := runs_call_of_meetsContract (r := 28)
    (initGraphFromExport_meetsContract (G := v.G) hpSelf hpBatch hpEdge hpOps)
    (show evalArgs w st4 [.reg 20, .reg 0, .reg 1, .reg 4] = some [qg, vCap, eCap, gD] by
      simp [evalArgs, Expr.eval, hregs4 20 (by decide), hregs4 0 (by decide), hregs4 1 (by decide),
        hregs4 4 (by decide), hregs3 20 (by decide), hregs3 0 (by decide), hregs3 1 (by decide),
        hregs3 4 (by decide), hregs2 20 (by decide), hregs2 0 (by decide), hregs2 1 (by decide),
        hregs2 4 (by decide), hregs1 20 (by decide), hregs1 0 (by decide), hregs1 1 (by decide),
        hregs1 4 (by decide), hregs0.r20, hregs0.r0, hregs0.r1, hregs0.r4])
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro z (rfl|rfl|rfl|rfl); exacts [hqgW, hvCapW, heCapW, hgD_W])
    ⟨qg, gD, h, rfl, hw16, by omega, by omega, hz4, hGval, hGvCap, hGeCap,
      exportAt_of_agree hExpG hbelow4⟩ ω
  obtain ⟨st5, c5, _, hr5, ⟨_, _, hEq5, _, hG5, hfr5, hz5⟩, _, hregs5, hc5⟩ := hC5
  simp only [List.cons.injEq, true_and, and_true] at hEq5; obtain ⟨rfl, rfl⟩ := hEq5
  rw [hDe, hqnum] at hz5 hfr5
  have hregs5_eq : ∀ r, r ≠ 28 → st5.regs r = st0.regs r := fun r hr =>
    (hregs5 r hr).trans ((hregs4 r hr).trans ((hregs3 r hr).trans ((hregs2 r hr).trans (hregs1 r hr))))
  have hlt_qg : ∀ a < qg, st5.mem a = st4.mem a := fun a ha => hfr5 a (Or.inl ha)
  have hlt_qs : ∀ a < qs, st5.mem a = st3.mem a := fun a ha => (hlt_qg a (by omega)).trans (hfr4 a (Or.inl ha))
  have hlt_qroots : ∀ a < qroots, st5.mem a = st2.mem a := fun a ha => (hlt_qs a (by omega)).trans (hfr3 a (Or.inl ha))
  have hlt_qf : ∀ a < qf, st5.mem a = st1.mem a := fun a ha => (hlt_qroots a (by omega)).trans (hfr2 a (Or.inl ha))
  have hlt_qt : ∀ a < qt, st5.mem a = st0.mem a := fun a ha => (hlt_qf a (by omega)).trans (hfr1 a (Or.inl ha))
  have hS4' := runs_seq_iff.mpr (Or.inr ⟨st4, c4, c5, hr4, hr5, rfl⟩)
  have hS3' := runs_seq_iff.mpr (Or.inr ⟨st3, c3, _, hr3, hS4', rfl⟩)
  have hS2' := runs_seq_iff.mpr (Or.inr ⟨st2, c2, _, hr2, hS3', rfl⟩)
  have hS1' := runs_seq_iff.mpr (Or.inr ⟨st1, c1, _, hr1, hS2', rfl⟩)
  have hS0' := runs_seq_iff.mpr (Or.inr ⟨st0, c0, _, hr0, hS1', rfl⟩)
  have hR5 : RootsAt st5.mem qroots vCap v.lsf.F.R := by
    have hR3' : RootsAt st3.mem qroots vCap v.lsf.F.R := by simpa [hR_set] using hR3
    exact ⟨hR3'.1, fun x hx => by rw [hlt_qs (qroots + x) (by omega)]; exact hR3'.2 x hx⟩
  refine ⟨st5, _, hS0',
    ⟨(hregs5_eq 0 (by decide)).trans hregs0.r0, (hregs5_eq 1 (by decide)).trans hregs0.r1,
     (hregs5_eq 2 (by decide)).trans hregs0.r2, (hregs5_eq 3 (by decide)).trans hregs0.r3,
     (hregs5_eq 4 (by decide)).trans hregs0.r4, (hregs5_eq 5 (by decide)).trans hregs0.r5,
     (hregs5_eq 6 (by decide)).trans hregs0.r6, (hregs5_eq 7 (by decide)).trans hregs0.r7,
     (hregs5_eq 8 (by decide)).trans hregs0.r8, (hregs5_eq 9 (by decide)).trans hregs0.r9,
     (hregs5_eq 10 (by decide)).trans hregs0.r10, (hregs5_eq 11 (by decide)).trans hregs0.r11,
     (hregs5_eq 12 (by decide)).trans hregs0.r12, (hregs5_eq 16 (by decide)).trans hregs0.r16,
     (hregs5_eq 17 (by decide)).trans hregs0.r17, (hregs5_eq 18 (by decide)).trans hregs0.r18,
     (hregs5_eq 19 (by decide)).trans hregs0.r19, (hregs5_eq 20 (by decide)).trans hregs0.r20,
     (hregs5_eq 21 (by decide)).trans hregs0.r21, (hregs5_eq 22 (by decide)).trans hregs0.r22,
     (hregs5_eq 23 (by decide)).trans hregs0.r23, (hregs5_eq 24 (by decide)).trans hregs0.r24,
     (hregs5_eq 25 (by decide)).trans hregs0.r25⟩,
    ⟨(hlt_qt h (by omega)).trans hhdr0.h0, (hlt_qt (h + 1) (by omega)).trans hhdr0.h1,
     (hlt_qt (h + 2) (by omega)).trans hhdr0.h2, (hlt_qt (h + 3) (by omega)).trans hhdr0.h3,
     (hlt_qt (h + 4) (by omega)).trans hhdr0.h4, (hlt_qt (h + 5) (by omega)).trans hhdr0.h5,
     (hlt_qt (h + 6) (by omega)).trans hhdr0.h6, (hlt_qt (h + 7) (by omega)).trans hhdr0.h7,
     (hlt_qt (h + 8) (by omega)).trans hhdr0.h8, (hlt_qt (h + 9) (by omega)).trans hhdr0.h9,
     (hlt_qt (h + 10) (by omega)).trans hhdr0.h10⟩,
    hT1.of_agree fun a _ ha2 => hlt_qf a (by omega),
    hF2.of_agree fun a _ ha2 => hlt_qroots a (by omega),
    hR5, hS4.of_agree fun a _ ha2 => hlt_qg a (by omega), hG5, hz5,
    fun a ha => (hlt_qt a (by omega)).trans (hbelow0 a ha), ?_⟩
  dsimp only [initGraphFromExportContract, setRootsContract, argsSize, Expr.size] at hc1 hc2 hc3 hc4 hc5
  rw [hFn_eq] at hc2; rw [hR_card] at hc3; omega

end MinCostFlow.SparseCore.Program.Read
