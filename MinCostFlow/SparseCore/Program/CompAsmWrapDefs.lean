module

public import MinCostFlow.SparseCore.Program.CompModule
public import MinCostFlow.SparseCore.Program.AssemblyCode
import MinCostFlow.LSF.Program.LSFModuleBase

/-!
# Thin P4 Wrapper Definitions for `AsmCompFamilyAt` (`CompAsmWrapDefs`)

Wraps P4's relocatable module `compLSFProcs` (`CompModule.lean`) instantiated on P3's canonical
window initializer `canonicalLSFWindowImpl` (`CompWindowInst.lean`) into the `ScCompCode`
procedure layout and `DSRep CompFamilyAbs` representation required by `AsmCompFamilyAt` and
`ScCompFamilyHyp` (`AssemblyTopIface.lean`, `AssemblyBridge.lean`):

* `compAsmInitProc` (index `0`): copies the input `DynGraphAt` into `gCopy` via `initCopyGStmt` in
  `O(n + m + 1)` time (handling `eCap = 0` cleanly via a zero-filled `L`-word fallback array),
  computes `L_w = canonLw K_AN L n k` on-machine via `log2Stmt`, invokes `compInitProc` at `bComp`,
  and stores the 2-word wrapper handle `[bComp, gCopy]` at `h`.
* `compAsmBatchProc` (index `1`): copies the `words`-word batch above `h`, advances `gCopy`
  in-place via `dgApplyBatchStmt`, invokes `compBatchWithSplitsProc`, and stores `ptrBase` at `h`.
* `compAsmExportProc` (index `2`): forwards `[bComp, j, gCopy, h]` to `compExportBranchProc`.
* `compAsmRootProc` (index `3`): forwards `[bComp, j, u, h]` to `compRootProc`.
* Indices `4 ..`: embedded `compLSFProcs` block (independent of `(L_in, P_fp)`).
-/

@[expose] public noncomputable section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.Bundle
  MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program MinCostFlow.Num

/-! ## 1. Embedded module offsets inside `compAsmProcs` -/

/-- Base index of the embedded `compLSFProcs` block inside `compAsmProcs`. -/
def compAsmBaseComp : ℕ := 4

/-- Procedure index of `compInitProc` inside `compAsmProcs`. -/
def compAsmIdxCompInit : ℕ := compIdxInit compAsmBaseComp

/-- Procedure index of `compBatchWithSplitsProc` inside `compAsmProcs`. -/
def compAsmIdxCompBatch : ℕ := compIdxOp compAsmBaseComp 0

/-- Procedure index of `compRootProc` inside `compAsmProcs`. -/
def compAsmIdxCompRoot : ℕ := compIdxOp compAsmBaseComp 3

/-- Procedure index of `compExportBranchProc` inside `compAsmProcs`. -/
def compAsmIdxCompExport : ℕ := compIdxOp compAsmBaseComp 6

/-- Procedure index of `compCopyWordsProc` inside `compAsmProcs`. -/
def compAsmIdxCopy : ℕ := compAsmBaseComp + 29

/-- Procedure index of `initCopyGStmt` inside `compAsmProcs`. -/
def compAsmIdxCopyG (Q_AN : Program) : ℕ :=
  lsfBaseA1 Q_AN (compBaseLsf compAsmBaseComp) + 2

/-- Procedure index of `dgApplyBatchStmt` inside `compAsmProcs`. -/
def compAsmIdxDgBatch : ℕ :=
  lsfBaseDg (compBaseLsf compAsmBaseComp) + 12 + dgIdxApplyBatch

/-- Procedure index of `log2Stmt` inside `compAsmProcs`. -/
def compAsmIdxLog : ℕ :=
  lsfBaseUtils (compBaseLsf compAsmBaseComp) + idxUtilLog2

/-! ## 2. The four deterministic wrapper procedures -/

/-- Wrapper `init` procedure (`args = [graph, lengths, L, P_fp, k, vCap, eCap, h]`, index `0`). -/
def compAsmInitProc (bCopyG bLog bCompInit rhoConstLog : ℕ) : Stmt :=
  .assign 8 (.load (.bin .add (.reg 0) (.const dgNOff))) ;;
  .assign 9 (.load (.bin .add (.reg 0) (.const dgMOff))) ;;
  .assign 10 (.bin .add (.bin .add (.reg 0) (.const 4)) (.reg 5)) ;;
  .assign 11 (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4))
    (.bin .mul (.const 7) (.reg 5))) (.reg 6)) ;;
  .cond (.reg 6)
    (.assign 12 (.reg 6) ;;
     .assign 13 (.reg 1) ;;
     .assign 14 (.bin .add (.reg 7) (.const 2)))
    (.assign 12 (.const 1) ;;
     .assign 13 (.bin .add (.reg 7) (.const 2)) ;;
     .assign 14 (.bin .add (.bin .add (.reg 7) (.const 2)) (.reg 2))) ;;
  .call 15 bCopyG [.reg 0, .reg 14, .reg 11, .reg 10, .reg 5, .reg 6, .reg 8, .reg 9] ;;
  .assign 15 (.bin .add (.reg 14) (.bin .add (.bin .add (.const 4)
    (.bin .mul (.const 7) (.reg 5))) (.bin .mul (.const 9) (.reg 6)))) ;;
  .cond (.reg 9)
    (.call 16 bLog [.bin .add (.reg 4) (.const 1)] ;;
     .call 17 bLog [.bin .add (.reg 8) (.const 2)] ;;
     .call 17 bLog [.bin .add (.reg 17) (.const 2)] ;;
     .assign 16 (.bin .add (.bin .add (.bin .add (.bin .add (.reg 2) (.const rhoConstLog))
       (.reg 16)) (.bin .mul (.const 6) (.reg 17))) (.const 8)))
    (.assign 16 (.const 1)) ;;
  .call 18 bCompInit [.reg 0, .reg 13, .reg 2, .reg 3, .reg 4, .reg 16, .reg 5, .reg 12, .reg 15] ;;
  .store (.reg 7) (.reg 15) ;;
  .store (.bin .add (.reg 7) (.const 1)) (.reg 14) ;;
  .ret (.reg 18)

/-- Wrapper `batch` procedure (`args = [cfH, batch, words, h]`, index `1`). -/
def compAsmBatchProc (bCopy bDgBatch bCompBatch : ℕ) : Stmt :=
  .assign 4 (.load (.reg 0)) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 6 (.bin .add (.reg 3) (.const 1)) ;;
  .assign 7 (.bin .add (.reg 6) (.reg 2)) ;;
  .call 8 bCopy [.reg 1, .reg 6, .reg 2] ;;
  .call 8 bDgBatch [.reg 5, .reg 6, .const 1] ;;
  .call 8 bCompBatch [.reg 4, .reg 6, .reg 7] ;;
  .assign 9 (.bin .add (.bin .add (.reg 7) (.const 1)) (.load (.reg 7))) ;;
  .store (.reg 3) (.reg 9) ;;
  .ret (.reg 8)

/-- Wrapper `export` procedure (`args = [cfH, j, h]`, index `2`). -/
def compAsmExportProc (bCompExport : ℕ) : Stmt :=
  .assign 3 (.load (.reg 0)) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 5 bCompExport [.reg 3, .reg 1, .reg 4, .reg 2] ;;
  .ret (.reg 5)

/-- Wrapper `root` procedure (`args = [cfH, j, u, h]`, index `3`). -/
def compAsmRootProc (bCompRoot : ℕ) : Stmt :=
  .assign 4 (.load (.reg 0)) ;;
  .call 5 bCompRoot [.reg 4, .reg 1, .reg 2, .reg 3] ;;
  .ret (.reg 5)

lemma compAsmInitProc_noRand (bCopyG bLog bCompInit rhoConstLog : ℕ) :
    (compAsmInitProc bCopyG bLog bCompInit rhoConstLog).NoRand := by
  simp [compAsmInitProc, Stmt.NoRand]

lemma compAsmBatchProc_noRand (bCopy bDgBatch bCompBatch : ℕ) :
    (compAsmBatchProc bCopy bDgBatch bCompBatch).NoRand := by
  simp [compAsmBatchProc, Stmt.NoRand]

lemma compAsmExportProc_noRand (bCompExport : ℕ) :
    (compAsmExportProc bCompExport).NoRand := by
  simp [compAsmExportProc, Stmt.NoRand]

lemma compAsmRootProc_noRand (bCompRoot : ℕ) :
    (compAsmRootProc bCompRoot).NoRand := by
  simp [compAsmRootProc, Stmt.NoRand]

/-- `compLSFProcs` instantiated on `canonicalLSFWindowImpl` is definitionally independent of
`(L_in, P_fp)`. -/
lemma compLSFProcs_canon_eq (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (hQ : FullAN19Spec Q_AN c_AN K_AN) (L_in P_fp b : ℕ) :
    compLSFProcs (canonicalLSFWindowImpl Q_AN c_AN K_AN hQ L_in P_fp) b =
      compLSFProcs (canonicalLSFWindowImpl Q_AN c_AN K_AN hQ 1 0) b := rfl

/-- Complete deterministic procedure list for the P4 wrapper (`ScCompCode`), independent of
`(L_in, P_fp)`. -/
def compAsmProcs (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (hQ : FullAN19Spec Q_AN c_AN K_AN) : List Stmt :=
  [ compAsmInitProc (compAsmIdxCopyG Q_AN) compAsmIdxLog compAsmIdxCompInit
      (Nat.log 2 (lemma55RhoConst K_AN + 1))
  , compAsmBatchProc compAsmIdxCopy compAsmIdxDgBatch compAsmIdxCompBatch
  , compAsmExportProc compAsmIdxCompExport
  , compAsmRootProc compAsmIdxCompRoot ] ++
  compLSFProcs (canonicalLSFWindowImpl Q_AN c_AN K_AN hQ 1 0) compAsmBaseComp

lemma compAsmProcs_noRand (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (hQ : FullAN19Spec Q_AN c_AN K_AN) :
    ∀ s ∈ compAsmProcs Q_AN c_AN K_AN hQ, s.NoRand := by
  intro s hs
  simp only [compAsmProcs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with (rfl | rfl | rfl | rfl) | hC
  · exact compAsmInitProc_noRand _ _ _ _
  · exact compAsmBatchProc_noRand _ _ _
  · exact compAsmExportProc_noRand _
  · exact compAsmRootProc_noRand _
  · exact compLSFProcs_noRand _ _ s hC

/-- Concrete `ScCompCode` record for P4. -/
def compAsmCode (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (hQ : FullAN19Spec Q_AN c_AN K_AN) : ScCompCode where
  procs := compAsmProcs Q_AN c_AN K_AN hQ
  hnoRand := compAsmProcs_noRand Q_AN c_AN K_AN hQ
  fInit := 0
  fBatch := 1
  fExport := 2
  fRoot := 3

/-! ## 3. Placement (`HasAt`) helpers for `⟨compAsmProcs ...⟩` -/

lemma compAsmProg_hasComp (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (hQ : FullAN19Spec Q_AN c_AN K_AN) (L_in P_fp : ℕ) :
    (⟨compAsmProcs Q_AN c_AN K_AN hQ⟩ : Program).HasAt compAsmBaseComp
      (compLSFProcs (canonicalLSFWindowImpl Q_AN c_AN K_AN hQ L_in P_fp) compAsmBaseComp) := by
  rw [compLSFProcs_canon_eq]
  have h0 : (⟨compAsmProcs Q_AN c_AN K_AN hQ⟩ : Program).HasAt 0 (compAsmProcs Q_AN c_AN K_AN hQ) :=
    fun i hi => by simp [hi]
  have h1 := MinCostFlow.Num.hasAt_append_right h0
  simpa [compAsmBaseComp] using h1

lemma compAsmProg_get0 (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (hQ : FullAN19Spec Q_AN c_AN K_AN) :
    (⟨compAsmProcs Q_AN c_AN K_AN hQ⟩ : Program).procs[0]? =
      some (compAsmInitProc (compAsmIdxCopyG Q_AN) compAsmIdxLog compAsmIdxCompInit
        (Nat.log 2 (lemma55RhoConst K_AN + 1))) := rfl

lemma compAsmProg_get1 (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (hQ : FullAN19Spec Q_AN c_AN K_AN) :
    (⟨compAsmProcs Q_AN c_AN K_AN hQ⟩ : Program).procs[1]? =
      some (compAsmBatchProc compAsmIdxCopy compAsmIdxDgBatch compAsmIdxCompBatch) := rfl

lemma compAsmProg_get2 (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (hQ : FullAN19Spec Q_AN c_AN K_AN) :
    (⟨compAsmProcs Q_AN c_AN K_AN hQ⟩ : Program).procs[2]? =
      some (compAsmExportProc compAsmIdxCompExport) := rfl

lemma compAsmProg_get3 (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (hQ : FullAN19Spec Q_AN c_AN K_AN) :
    (⟨compAsmProcs Q_AN c_AN K_AN hQ⟩ : Program).procs[3]? =
      some (compAsmRootProc compAsmIdxCompRoot) := rfl

lemma compAsmProg_hasLsf (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (hQ : FullAN19Spec Q_AN c_AN K_AN) :
    (⟨compAsmProcs Q_AN c_AN K_AN hQ⟩ : Program).HasAt (compBaseLsf compAsmBaseComp)
      (lsfModuleProcs Q_AN c_AN K_AN (compBaseLsf compAsmBaseComp) 4) := by
  have hc := compAsmProg_hasComp Q_AN c_AN K_AN hQ 1 0
  unfold compLSFProcs at hc
  rw [List.append_assoc] at hc
  have h1 := MinCostFlow.Num.hasAt_append_right hc
  rw [compCoreProcs_length] at h1
  exact MinCostFlow.Num.hasAt_append_left h1

lemma compAsmProg_getCopy (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (hQ : FullAN19Spec Q_AN c_AN K_AN) :
    (⟨compAsmProcs Q_AN c_AN K_AN hQ⟩ : Program).procs[compAsmIdxCopy]? =
      some compCopyWordsProc := by
  have hc := compAsmProg_hasComp Q_AN c_AN K_AN hQ 1 0
  unfold compLSFProcs at hc
  rw [List.append_assoc] at hc
  have hcore := MinCostFlow.Num.hasAt_append_left hc
  simpa [compAsmIdxCopy, compCoreProcs] using hcore.get (i := 29) (by rw [compCoreProcs_length]; decide)

lemma compAsmProg_getCopyG (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (hQ : FullAN19Spec Q_AN c_AN K_AN) :
    (⟨compAsmProcs Q_AN c_AN K_AN hQ⟩ : Program).procs[compAsmIdxCopyG Q_AN]? =
      some (initCopyGStmt (lsfBaseDg (compBaseLsf compAsmBaseComp))) := by
  have hA1 := (lsfModuleHasAt_of_hasAt (compAsmProg_hasLsf Q_AN c_AN K_AN hQ)).hA1
  simpa [compAsmIdxCopyG, lsfProcsA1] using hA1.get (i := 2) (by simp [lsfProcsA1])

lemma compAsmProg_hasDg (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (hQ : FullAN19Spec Q_AN c_AN K_AN) :
    (⟨compAsmProcs Q_AN c_AN K_AN hQ⟩ : Program).HasAt (lsfBaseDg (compBaseLsf compAsmBaseComp))
      (dgRelocProcs (lsfBaseDg (compBaseLsf compAsmBaseComp))) :=
  lsfHasAt_dg (lsfModuleHasAt_of_hasAt (compAsmProg_hasLsf Q_AN c_AN K_AN hQ)).hShared

lemma compAsmProg_getLog (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (hQ : FullAN19Spec Q_AN c_AN K_AN) :
    (⟨compAsmProcs Q_AN c_AN K_AN hQ⟩ : Program).procs[compAsmIdxLog]? =
      some log2Stmt := by
  have hU := lsfHasAt_utils (lsfModuleHasAt_of_hasAt (compAsmProg_hasLsf Q_AN c_AN K_AN hQ)).hShared
  simpa [compAsmIdxLog, utilsProcs, idxUtilLog2] using hU.get (i := 6) (by simp [utilsProcs])

/-! ## 4. Concrete state `CompAsmMeta`, `DSRep CompFamilyAbs`, and locality -/

/-- Concrete metadata for the P4 wrapper handle `cfH`: stores `(k, vCap, eCap)`, the addresses
`gCopy` (in-place `DynGraphAt` mirror) and `bComp` (inner `CompLSFRepAt` handle), and the inner
`CompLSFMeta k`. -/
structure CompAsmMeta where
  k : ℕ
  vCap : ℕ
  eCap : ℕ
  gCopy : ℕ
  bComp : ℕ
  xComp : CompLSFMeta k

/-- Memory footprint of a P4 wrapper handle `cfH`: the 2-word wrapper header `[cfH, cfH + 2)`,
the `DynGraphAt` mirror `[x.gCopy, x.gCopy + dynGraphSize x.vCap x.eCap)`, and the inner
`compFoot x.bComp x.xComp`. -/
def compAsmFoot (cfH : ℕ) (x : CompAsmMeta) (a : ℕ) : Prop :=
  (cfH ≤ a ∧ a < cfH + 2) ∨
  (x.gCopy ≤ a ∧ a < x.gCopy + dynGraphSize x.vCap x.eCap) ∨
  compFoot x.bComp x.xComp a

/-- Representation predicate for the P4 wrapper handle `cfH` on `CompFamilyAbs`. -/
def compAsmRepPred (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (hQ : FullAN19Spec Q_AN c_AN K_AN) (L_in P_fp : ℕ)
    (cfH : ℕ) (cfs : CompFamilyAbs) (x : CompAsmMeta) (mem : ℕ → ℕ) : Prop :=
  mem cfH = x.bComp ∧
  mem (cfH + 1) = x.gCopy ∧
  cfH + 2 ≤ x.gCopy ∧
  x.gCopy + dynGraphSize x.vCap x.eCap = x.bComp ∧
  1 ≤ x.k ∧
  (cfs 0).k = x.k ∧
  x.xComp.vCap = x.vCap ∧
  x.xComp.eCap = max x.eCap 1 ∧
  x.xComp.L_w = (if (cfs 0).G₀.m = 0 then 1 else canonLw K_AN L_in (cfs 0).G₀.n x.k) ∧
  DynGraphAt mem x.gCopy x.vCap x.eCap (cfs 0).G ∧
  CompLSFRepAt (canonicalLSFWindowImpl Q_AN c_AN K_AN hQ L_in P_fp) x.k x.bComp
    (fun j : Fin x.k => cfs j.1) x.xComp mem

/-- `DSRep CompFamilyAbs` for the P4 wrapper. -/
def compAsmRep (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (hQ : FullAN19Spec Q_AN c_AN K_AN) (L_in P_fp : ℕ) : DSRep CompFamilyAbs where
  τ := CompAsmMeta
  rep := compAsmRepPred Q_AN c_AN K_AN hQ L_in P_fp
  phi _ x mem := compPhiFull x.k x.bComp x.xComp mem
  foot := compAsmFoot

/-- `compAsmRep` is local (depends only on `compAsmFoot`). -/
theorem compAsmRep_local (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (hQ : FullAN19Spec Q_AN c_AN K_AN) (L_in P_fp : ℕ) :
    (compAsmRep Q_AN c_AN K_AN hQ L_in P_fp).Local := by
  intro cfH cfs x m1 m2 hag
  have hdg : DynGraphAt m1 x.gCopy x.vCap x.eCap (cfs 0).G ↔
      DynGraphAt m2 x.gCopy x.vCap x.eCap (cfs 0).G :=
    ⟨fun h => dynGraphAt_of_agree h fun a ha1 ha2 => (hag a (Or.inr (Or.inl ⟨ha1, ha2⟩))).symm,
     fun h => dynGraphAt_of_agree h fun a ha1 ha2 => hag a (Or.inr (Or.inl ⟨ha1, ha2⟩))⟩
  have hcomp := compLSFRepFull_local (canonicalLSFWindowImpl Q_AN c_AN K_AN hQ L_in P_fp) x.k
    x.bComp (fun j : Fin x.k => cfs j.1) x.xComp m1 m2
    (fun a ha => hag a (Or.inr (Or.inr ha)))
  refine ⟨?_, hcomp.2⟩
  have h0 : m1 cfH = m2 cfH := hag cfH (Or.inl ⟨le_rfl, by omega⟩)
  have h1 : m1 (cfH + 1) = m2 (cfH + 1) := hag (cfH + 1) (Or.inl ⟨by omega, by omega⟩)
  rintro ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩
  exact ⟨h0.symm.trans a1, h1.symm.trans a2, a3, a4, a5, a6, a7, a8, a9, hdg.mp a10, hcomp.1 a11⟩

end MinCostFlow.SparseCore.Program
