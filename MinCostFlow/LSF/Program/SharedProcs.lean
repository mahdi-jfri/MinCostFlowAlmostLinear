module

public import MinCostFlow.LSF.Program.KeyedSort
public import MinCostFlow.Machine.WideWord.LSSTProgram

/-!
# Shared Module Assembly and `HasAt` Interface for `LSF`

Packages all shared deterministic modules (`DynGraph`, `SortOps`, `Num` arithmetic,
utility procedures, and `keyedMergeSortStmt`) at fixed offsets from any program base `b`,
and provides one-step `HasAt` and `MeetsContract` extraction lemmas for downstream modules.
-/

namespace MinCostFlow.LSF.Program

open WordRAM
open MinCostFlow.DynSpanner.Program
open MinCostFlow.Num
open MinCostFlow.WideWord

@[expose] public section

/-! ## Utility Module and Fixed Offsets -/

/-- Shared deterministic utility module at `bUtils` (`8` procedures). -/
noncomputable def utilsProcs (bUtils bULess K_AN h : ℕ) : List Stmt :=
  [ memCopyStmt
  , memFillStmt
  , wordToLimbsStmt h
  , emitNatStmt (defaultC_ceil K_AN) h
  , addToStmt h
  , subFromStmt h
  , log2Stmt
  , keyedMergeSortStmt (bUtils + idxUtilKeyedMergeSort) bULess ]

lemma utilsProcs_length (bUtils bULess K_AN h : ℕ) :
    (utilsProcs bUtils bULess K_AN h).length = 8 := rfl

lemma utilsProcs_noRand (bUtils bULess K_AN h : ℕ) :
    ∀ s ∈ utilsProcs bUtils bULess K_AN h, s.NoRand := by
  intro s hs
  simp only [utilsProcs, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact memCopyStmt_noRand
  · exact memFillStmt_noRand
  · exact wordToLimbsStmt_noRand h
  · exact emitNatStmt_noRand _ h
  · exact addToStmt_noRand h
  · exact subFromStmt_noRand h
  · exact log2Stmt_noRand
  · exact keyedMergeSortStmt_noRand _ _

def lsfIdxInit : ℕ := 0
def lsfIdxBatch : ℕ := 1

def lsfBaseDg (b : ℕ) : ℕ := b + 2
def lsfBaseSort (b : ℕ) : ℕ := lsfBaseDg b + 15
def lsfBaseCopy (b : ℕ) : ℕ := lsfBaseSort b + 4
def lsfBaseLess (b : ℕ) : ℕ := lsfBaseCopy b + 1
def lsfBaseShiftL (b : ℕ) : ℕ := lsfBaseLess b + 3
def lsfBaseAdd (b : ℕ) : ℕ := lsfBaseShiftL b + 2
def lsfBaseSub (b : ℕ) : ℕ := lsfBaseAdd b + 2
def lsfBaseMul (b : ℕ) : ℕ := lsfBaseSub b + 5
def lsfBaseIntDiv (b : ℕ) : ℕ := lsfBaseMul b + 5
def lsfBaseUtils (b : ℕ) : ℕ := lsfBaseIntDiv b + 25
def lsfSharedEnd (b : ℕ) : ℕ := lsfBaseUtils b + 8

/-- Shared deterministic modules for an `LSF` program starting at `b`
(placed at `b + 2` immediately after the two entry stubs). -/
noncomputable def lsfSharedProcs (b K_AN h : ℕ) : List Stmt :=
  dgRelocProcs (lsfBaseDg b) ++
  sortProcs (lsfBaseSort b) ++
  MinCostFlow.Num.copyModule (lsfBaseCopy b) ++
  MinCostFlow.Num.lessModule (lsfBaseLess b) h ++
  MinCostFlow.Num.shiftLeftModule (lsfBaseShiftL b) h ++
  MinCostFlow.Num.addModule (lsfBaseAdd b) h ++
  MinCostFlow.Num.subtractModule (lsfBaseSub b) h ++
  MinCostFlow.Num.multiplyModule (lsfBaseMul b) h ++
  MinCostFlow.Num.integerDivideModule (lsfBaseIntDiv b) h ++
  utilsProcs (lsfBaseUtils b) (lsfBaseLess b + 2) K_AN h

lemma copyModule_length (x : ℕ) : (MinCostFlow.Num.copyModule x).length = 1 := rfl
lemma lessModule_length (x h : ℕ) : (MinCostFlow.Num.lessModule x h).length = 3 := rfl
lemma shiftLeftModule_length (x h : ℕ) : (MinCostFlow.Num.shiftLeftModule x h).length = 2 := rfl
lemma addModule_length (x h : ℕ) : (MinCostFlow.Num.addModule x h).length = 2 := rfl
lemma subtractModule_length (x h : ℕ) : (MinCostFlow.Num.subtractModule x h).length = 5 := rfl
lemma multiplyModule_length (x h : ℕ) : (MinCostFlow.Num.multiplyModule x h).length = 5 := rfl
lemma integerDivideModule_length (x h : ℕ) :
    (MinCostFlow.Num.integerDivideModule x h).length = 25 := rfl

lemma lsfSharedProcs_length (b K_AN h : ℕ) : (lsfSharedProcs b K_AN h).length = 70 := by
  simp only [lsfSharedProcs, List.length_append, dgRelocProcs_length, sortProcs_length,
    copyModule_length, lessModule_length, shiftLeftModule_length, addModule_length,
    subtractModule_length, multiplyModule_length, integerDivideModule_length, utilsProcs_length]

lemma lsfSharedProcs_noRand (b K_AN h : ℕ) : ∀ s ∈ lsfSharedProcs b K_AN h, s.NoRand := by
  intro s hs
  simp only [lsfSharedProcs, List.mem_append] at hs
  rcases hs with ((((((((hs | hs) | hs) | hs) | hs) | hs) | hs) | hs) | hs) | hs
  · exact dgRelocProcs_noRand _ s hs
  · exact sortProcs_noRand _ s hs
  · have : s = copyBody := by simpa [copyModule] using hs
    subst this; exact copyBody_noRand
  · exact lessModule_noRand _ _ s hs
  · exact shiftLeftModule_noRand _ _ s hs
  · exact addModule_noRand _ _ s hs
  · exact subtractModule_noRand _ _ s hs
  · exact multiplyModule_noRand _ _ s hs
  · exact integerDivideModule_noRand _ _ s hs
  · exact utilsProcs_noRand _ _ _ _ s hs

/-! ## Submodule `HasAt` Extraction -/

lemma lsfHasAt_dg {p : Program} {b K_AN h : ℕ}
    (hp : p.HasAt (b + 2) (lsfSharedProcs b K_AN h)) :
    p.HasAt (lsfBaseDg b) (dgRelocProcs (lsfBaseDg b)) := by
  have hp' := MinCostFlow.Num.hasAt_append_left
    (by simpa only [lsfSharedProcs, List.append_assoc] using hp)
  simpa only [lsfBaseDg] using hp'

lemma lsfHasAt_dgOps {p : Program} {b K_AN h : ℕ}
    (hp : p.HasAt (b + 2) (lsfSharedProcs b K_AN h)) :
    p.HasAt (lsfBaseDg b) dgOpsProcs :=
  dgReloc_hasAt_ops (lsfHasAt_dg hp)

lemma lsfHasAt_dgEdge {p : Program} {b K_AN h : ℕ}
    (hp : p.HasAt (b + 2) (lsfSharedProcs b K_AN h)) :
    p.HasAt (lsfBaseDg b + 7) (dgEdgeProcs (lsfBaseDg b)) :=
  dgReloc_hasAt_edge (lsfHasAt_dg hp)

lemma lsfHasAt_dgSplit {p : Program} {b K_AN h : ℕ}
    (hp : p.HasAt (b + 2) (lsfSharedProcs b K_AN h)) :
    p.HasAt (lsfBaseDg b + 9) (dgSplitProcs (lsfBaseDg b) (lsfBaseDg b + 9)) :=
  dgReloc_hasAt_split (lsfHasAt_dg hp)

lemma lsfHasAt_dgBatch {p : Program} {b K_AN h : ℕ}
    (hp : p.HasAt (b + 2) (lsfSharedProcs b K_AN h)) :
    p.HasAt (lsfBaseDg b + 12)
      (dgBatchProcs (lsfBaseDg b) (lsfBaseDg b + 7) (lsfBaseDg b + 9) (lsfBaseDg b + 12)) :=
  dgReloc_hasAt_batch (lsfHasAt_dg hp)

lemma lsfHasAt_sort {p : Program} {b K_AN h : ℕ}
    (hp : p.HasAt (b + 2) (lsfSharedProcs b K_AN h)) :
    p.HasAt (lsfBaseSort b) (sortProcs (lsfBaseSort b)) := by
  have h1 := MinCostFlow.Num.hasAt_append_right
    (by simpa only [lsfSharedProcs, List.append_assoc] using hp)
  rw [dgRelocProcs_length] at h1
  exact MinCostFlow.Num.hasAt_append_left h1

lemma lsfHasAt_copy {p : Program} {b K_AN h : ℕ}
    (hp : p.HasAt (b + 2) (lsfSharedProcs b K_AN h)) :
    p.HasAt (lsfBaseCopy b) (copyModule (lsfBaseCopy b)) := by
  have h1 := MinCostFlow.Num.hasAt_append_right
    (by simpa only [lsfSharedProcs, List.append_assoc] using hp)
  rw [dgRelocProcs_length] at h1
  have h2 := MinCostFlow.Num.hasAt_append_right h1
  rw [sortProcs_length] at h2
  simpa only [lsfBaseCopy, lsfBaseSort, lsfBaseDg, Nat.add_assoc] using
    MinCostFlow.Num.hasAt_append_left h2

lemma lsfHasAt_less {p : Program} {b K_AN h : ℕ}
    (hp : p.HasAt (b + 2) (lsfSharedProcs b K_AN h)) :
    p.HasAt (lsfBaseLess b) (lessModule (lsfBaseLess b) h) := by
  have h1 := MinCostFlow.Num.hasAt_append_right
    (by simpa only [lsfSharedProcs, List.append_assoc] using hp)
  rw [dgRelocProcs_length] at h1
  have h2 := MinCostFlow.Num.hasAt_append_right h1
  rw [sortProcs_length] at h2
  have h3 := MinCostFlow.Num.hasAt_append_right h2
  rw [copyModule_length] at h3
  simpa only [lsfBaseLess, lsfBaseCopy, lsfBaseSort, lsfBaseDg, Nat.add_assoc] using
    MinCostFlow.Num.hasAt_append_left h3

lemma lsfHasAt_unsignedLess {p : Program} {b K_AN h : ℕ}
    (hp : p.HasAt (b + 2) (lsfSharedProcs b K_AN h)) :
    p.HasAt (lsfBaseLess b + 2) (unsignedLessModule (lsfBaseLess b + 2)) := by
  have hless := lsfHasAt_less hp
  intro i hi
  have hi0 : i = 0 := by change i < 1 at hi; omega
  subst hi0
  simpa only [lessModule, unsignedLessModule, Nat.add_zero, List.getElem_cons_succ,
    List.getElem_cons_zero] using hless 2 (by simp [lessModule])

lemma lsfHasAt_shiftL {p : Program} {b K_AN h : ℕ}
    (hp : p.HasAt (b + 2) (lsfSharedProcs b K_AN h)) :
    p.HasAt (lsfBaseShiftL b) (shiftLeftModule (lsfBaseShiftL b) h) := by
  have h1 := MinCostFlow.Num.hasAt_append_right
    (by simpa only [lsfSharedProcs, List.append_assoc] using hp)
  rw [dgRelocProcs_length] at h1
  have h2 := MinCostFlow.Num.hasAt_append_right h1
  rw [sortProcs_length] at h2
  have h3 := MinCostFlow.Num.hasAt_append_right h2
  rw [copyModule_length] at h3
  have h4 := MinCostFlow.Num.hasAt_append_right h3
  rw [lessModule_length] at h4
  simpa only [lsfBaseShiftL, lsfBaseLess, lsfBaseCopy, lsfBaseSort, lsfBaseDg, Nat.add_assoc] using
    MinCostFlow.Num.hasAt_append_left h4

lemma lsfHasAt_add {p : Program} {b K_AN h : ℕ}
    (hp : p.HasAt (b + 2) (lsfSharedProcs b K_AN h)) :
    p.HasAt (lsfBaseAdd b) (addModule (lsfBaseAdd b) h) := by
  have h1 := MinCostFlow.Num.hasAt_append_right
    (by simpa only [lsfSharedProcs, List.append_assoc] using hp)
  rw [dgRelocProcs_length] at h1
  have h2 := MinCostFlow.Num.hasAt_append_right h1
  rw [sortProcs_length] at h2
  have h3 := MinCostFlow.Num.hasAt_append_right h2
  rw [copyModule_length] at h3
  have h4 := MinCostFlow.Num.hasAt_append_right h3
  rw [lessModule_length] at h4
  have h5 := MinCostFlow.Num.hasAt_append_right h4
  rw [shiftLeftModule_length] at h5
  simpa only [lsfBaseAdd, lsfBaseShiftL, lsfBaseLess, lsfBaseCopy, lsfBaseSort, lsfBaseDg,
    Nat.add_assoc] using MinCostFlow.Num.hasAt_append_left h5

lemma lsfHasAt_sub {p : Program} {b K_AN h : ℕ}
    (hp : p.HasAt (b + 2) (lsfSharedProcs b K_AN h)) :
    p.HasAt (lsfBaseSub b) (subtractModule (lsfBaseSub b) h) := by
  have h1 := MinCostFlow.Num.hasAt_append_right
    (by simpa only [lsfSharedProcs, List.append_assoc] using hp)
  rw [dgRelocProcs_length] at h1
  have h2 := MinCostFlow.Num.hasAt_append_right h1
  rw [sortProcs_length] at h2
  have h3 := MinCostFlow.Num.hasAt_append_right h2
  rw [copyModule_length] at h3
  have h4 := MinCostFlow.Num.hasAt_append_right h3
  rw [lessModule_length] at h4
  have h5 := MinCostFlow.Num.hasAt_append_right h4
  rw [shiftLeftModule_length] at h5
  have h6 := MinCostFlow.Num.hasAt_append_right h5
  rw [addModule_length] at h6
  simpa only [lsfBaseSub, lsfBaseAdd, lsfBaseShiftL, lsfBaseLess, lsfBaseCopy, lsfBaseSort,
    lsfBaseDg, Nat.add_assoc] using MinCostFlow.Num.hasAt_append_left h6

lemma lsfHasAt_mul {p : Program} {b K_AN h : ℕ}
    (hp : p.HasAt (b + 2) (lsfSharedProcs b K_AN h)) :
    p.HasAt (lsfBaseMul b) (multiplyModule (lsfBaseMul b) h) := by
  have h1 := MinCostFlow.Num.hasAt_append_right
    (by simpa only [lsfSharedProcs, List.append_assoc] using hp)
  rw [dgRelocProcs_length] at h1
  have h2 := MinCostFlow.Num.hasAt_append_right h1
  rw [sortProcs_length] at h2
  have h3 := MinCostFlow.Num.hasAt_append_right h2
  rw [copyModule_length] at h3
  have h4 := MinCostFlow.Num.hasAt_append_right h3
  rw [lessModule_length] at h4
  have h5 := MinCostFlow.Num.hasAt_append_right h4
  rw [shiftLeftModule_length] at h5
  have h6 := MinCostFlow.Num.hasAt_append_right h5
  rw [addModule_length] at h6
  have h7 := MinCostFlow.Num.hasAt_append_right h6
  rw [subtractModule_length] at h7
  simpa only [lsfBaseMul, lsfBaseSub, lsfBaseAdd, lsfBaseShiftL, lsfBaseLess, lsfBaseCopy,
    lsfBaseSort, lsfBaseDg, Nat.add_assoc] using MinCostFlow.Num.hasAt_append_left h7

lemma lsfHasAt_intDiv {p : Program} {b K_AN h : ℕ}
    (hp : p.HasAt (b + 2) (lsfSharedProcs b K_AN h)) :
    p.HasAt (lsfBaseIntDiv b) (integerDivideModule (lsfBaseIntDiv b) h) := by
  have h1 := MinCostFlow.Num.hasAt_append_right
    (by simpa only [lsfSharedProcs, List.append_assoc] using hp)
  rw [dgRelocProcs_length] at h1
  have h2 := MinCostFlow.Num.hasAt_append_right h1
  rw [sortProcs_length] at h2
  have h3 := MinCostFlow.Num.hasAt_append_right h2
  rw [copyModule_length] at h3
  have h4 := MinCostFlow.Num.hasAt_append_right h3
  rw [lessModule_length] at h4
  have h5 := MinCostFlow.Num.hasAt_append_right h4
  rw [shiftLeftModule_length] at h5
  have h6 := MinCostFlow.Num.hasAt_append_right h5
  rw [addModule_length] at h6
  have h7 := MinCostFlow.Num.hasAt_append_right h6
  rw [subtractModule_length] at h7
  have h8 := MinCostFlow.Num.hasAt_append_right h7
  rw [multiplyModule_length] at h8
  simpa only [lsfBaseIntDiv, lsfBaseMul, lsfBaseSub, lsfBaseAdd, lsfBaseShiftL, lsfBaseLess,
    lsfBaseCopy, lsfBaseSort, lsfBaseDg, Nat.add_assoc] using MinCostFlow.Num.hasAt_append_left h8

lemma lsfHasAt_utils {p : Program} {b K_AN h : ℕ}
    (hp : p.HasAt (b + 2) (lsfSharedProcs b K_AN h)) :
    p.HasAt (lsfBaseUtils b) (utilsProcs (lsfBaseUtils b) (lsfBaseLess b + 2) K_AN h) := by
  have h1 := MinCostFlow.Num.hasAt_append_right
    (by simpa only [lsfSharedProcs, List.append_assoc] using hp)
  rw [dgRelocProcs_length] at h1
  have h2 := MinCostFlow.Num.hasAt_append_right h1
  rw [sortProcs_length] at h2
  have h3 := MinCostFlow.Num.hasAt_append_right h2
  rw [copyModule_length] at h3
  have h4 := MinCostFlow.Num.hasAt_append_right h3
  rw [lessModule_length] at h4
  have h5 := MinCostFlow.Num.hasAt_append_right h4
  rw [shiftLeftModule_length] at h5
  have h6 := MinCostFlow.Num.hasAt_append_right h5
  rw [addModule_length] at h6
  have h7 := MinCostFlow.Num.hasAt_append_right h6
  rw [subtractModule_length] at h7
  have h8 := MinCostFlow.Num.hasAt_append_right h7
  rw [multiplyModule_length] at h8
  have h9 := MinCostFlow.Num.hasAt_append_right h8
  rw [integerDivideModule_length] at h9
  simpa only [lsfBaseUtils, lsfBaseIntDiv, lsfBaseMul, lsfBaseSub, lsfBaseAdd, lsfBaseShiftL,
    lsfBaseLess, lsfBaseCopy, lsfBaseSort, lsfBaseDg, Nat.add_assoc] using h9

/-! ## Utility `MeetsContract` Helpers -/

lemma lsfMemCopy_meetsContract {w b K_AN h : ℕ} {p : Program}
    (hw : 1 < 2 ^ w) (hp : p.HasAt (b + 2) (lsfSharedProcs b K_AN h)) :
    MeetsContract w p (lsfBaseUtils b + idxUtilMemCopy) (memCopyContract w) :=
  memCopy_meetsContract hw ((lsfHasAt_utils hp).get (i := idxUtilMemCopy)
    (by simp [utilsProcs, idxUtilMemCopy]))

lemma lsfMemFill_meetsContract {w b K_AN h : ℕ} {p : Program}
    (hw : 1 < 2 ^ w) (hp : p.HasAt (b + 2) (lsfSharedProcs b K_AN h)) :
    MeetsContract w p (lsfBaseUtils b + idxUtilMemFill) (memFillContract w) :=
  memFill_meetsContract hw ((lsfHasAt_utils hp).get (i := idxUtilMemFill)
    (by simp [utilsProcs, idxUtilMemFill]))

lemma lsfWordToLimbs_meetsContract {w b K_AN h : ℕ} {p : Program}
    (hp : p.HasAt (b + 2) (lsfSharedProcs b K_AN h)) :
    MeetsContract w p (lsfBaseUtils b + idxUtilWordToLimbs) (wordToLimbsContract w h) :=
  wordToLimbs_meetsContract ((lsfHasAt_utils hp).get (i := idxUtilWordToLimbs)
    (by simp [utilsProcs, idxUtilWordToLimbs]))

lemma lsfEmitDefaultC_meetsContract {w b K_AN h : ℕ} {p : Program}
    (hp : p.HasAt (b + 2) (lsfSharedProcs b K_AN h)) :
    MeetsContract w p (lsfBaseUtils b + idxUtilEmitDefaultC)
      (emitNatContract w (defaultC_ceil K_AN) h) :=
  emitNat_meetsContract ((lsfHasAt_utils hp).get (i := idxUtilEmitDefaultC)
    (by simp [utilsProcs, idxUtilEmitDefaultC]))

lemma lsfAddTo_meetsContract {w b K_AN h : ℕ} {p : Program}
    (hp : p.HasAt (b + 2) (lsfSharedProcs b K_AN h)) :
    MeetsContract w p (lsfBaseUtils b + idxUtilAddTo) (addToContract w h) :=
  addTo_meetsContract ((lsfHasAt_utils hp).get (i := idxUtilAddTo)
    (by simp [utilsProcs, idxUtilAddTo]))

lemma lsfSubFrom_meetsContract {w b K_AN h : ℕ} {p : Program}
    (hp : p.HasAt (b + 2) (lsfSharedProcs b K_AN h)) :
    MeetsContract w p (lsfBaseUtils b + idxUtilSubFrom) (subFromContract w h) :=
  subFrom_meetsContract ((lsfHasAt_utils hp).get (i := idxUtilSubFrom)
    (by simp [utilsProcs, idxUtilSubFrom]))

lemma lsfLog2_meetsContract {w b K_AN h : ℕ} {p : Program}
    (hw : 2 < 2 ^ w) (hp : p.HasAt (b + 2) (lsfSharedProcs b K_AN h)) :
    MeetsContract w p (lsfBaseUtils b + idxUtilLog2) log2Contract :=
  log2_meetsContract hw ((lsfHasAt_utils hp).get (i := idxUtilLog2)
    (by simp [utilsProcs, idxUtilLog2]))

lemma lsfKeyedMergeSort_meetsContract {w b K_AN h : ℕ} {p : Program}
    (hw : 1 < 2 ^ w) (hp : p.HasAt (b + 2) (lsfSharedProcs b K_AN h)) :
    MeetsContract w p (lsfBaseUtils b + idxUtilKeyedMergeSort) (keyedMergeSortContract w h) :=
  keyedMergeSort_meetsContract
    ((lsfHasAt_utils hp).get (i := idxUtilKeyedMergeSort)
      (by simp [utilsProcs, idxUtilKeyedMergeSort]))
    (unsignedLess_meetsContract (h := h) hw (lsfHasAt_unsignedLess hp))

end

end MinCostFlow.LSF.Program
