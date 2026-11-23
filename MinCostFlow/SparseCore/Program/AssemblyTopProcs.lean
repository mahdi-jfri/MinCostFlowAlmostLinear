module

public import MinCostFlow.SparseCore.Program.AssemblyTopInitLoop
public import MinCostFlow.SparseCore.Program.AssemblyTopStepLoop
public import MinCostFlow.SparseCore.Program.AssemblyWordSize
public import WordRAM.CopyWords

/-!
# Top-layer sparse-core procedures, parameters, and allocation (`AssemblyTopProcs`)

Defines the 7 top-level dispatch procedures (`init`, `op 0`–`op 5`) of the sparse-core program
together with the embedded order store (`ordStoreProcs`, 19 procedures), linear-time order
compactor (`asmCompactOrdBody`), and empty-graph update writer (`asmEmptyUpdateBody`), forming a
28-procedure block `asmTopProcs`. Also defines the input-independent contract constants
`asmTopParams` and space function `asmTopAlloc`, and proves determinism (`asmTopProcs_noRand`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio MinCostFlow.LSF

/-! ## Top-layer procedure bodies -/

/-- `init [graph, lengths, gradient, ord, k, M, N, L, P_fp, depth, heap]` (`r0..r10`).
Moves `depth` to `r19` and `heap` to `r9`, writes the 20-word header at `heap`, checks
`G.n = mem[graph + 2]`, and either reserves the empty-graph footprint or runs `fCompact`,
P1 `fOrdInit`, P4 `fCFInit`, and `asmInitBranchesLoop`. -/
def asmTopInitBody (fCompact fOrdInit fCFInit fCFExport fBrInit : ℕ) : Stmt :=
  .assign 19 (.reg 9) ;;
  .assign 9 (.reg 10) ;;
  .assign 10 (.load (.reg 0)) ;;
  .assign 11 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 16 (.load (.bin .add (.reg 0) (.const 2))) ;;
  .store (.bin .add (.reg 9) (.const ASM_HDR_K)) (.reg 4) ;;
  .store (.bin .add (.reg 9) (.const ASM_HDR_M)) (.reg 5) ;;
  .store (.bin .add (.reg 9) (.const ASM_HDR_N)) (.reg 6) ;;
  .store (.bin .add (.reg 9) (.const ASM_HDR_VCAP)) (.reg 10) ;;
  .store (.bin .add (.reg 9) (.const ASM_HDR_ECAP)) (.reg 11) ;;
  .store (.bin .add (.reg 9) (.const ASM_HDR_L)) (.reg 7) ;;
  .store (.bin .add (.reg 9) (.const ASM_HDR_PFP)) (.reg 8) ;;
  .assign 14 (.bin .add (.reg 9) (.const ASM_HDR_SIZE)) ;;
  .cond (.reg 16)
    (.store (.reg 9) (.const 1) ;;
     .assign 17 (.reg 14) ;;
     .call 14 fCompact [.reg 3, .reg 14] ;;
     .assign 3 (.reg 17) ;;
     .store (.bin .add (.reg 9) (.const ASM_HDR_ORDH)) (.reg 14) ;;
     .call 14 fOrdInit [.reg 10, .reg 11, .reg 3, .reg 14] ;;
     .assign 12 (.reg 14) ;;
     .store (.bin .add (.reg 9) (.const ASM_HDR_CFH)) (.reg 12) ;;
     .call 14 fCFInit [.reg 0, .reg 1, .reg 7, .reg 8, .reg 4, .reg 10, .reg 11, .reg 14] ;;
     .assign 13 (.reg 14) ;;
     .store (.bin .add (.reg 9) (.const ASM_HDR_TBL)) (.reg 13) ;;
     .assign 14 (.bin .add (.reg 13) (.reg 4)) ;;
     asmInitBranchesLoop fCFExport fBrInit ;;
     .assign 17 (.bin .add (.bin .add (.bin .add (.bin .add (.bin .add (.bin .add
       (.reg 5) (.reg 6)) (.reg 4)) (.reg 10)) (.reg 11)) (.reg 7)) (.const ASM_HDR_SIZE)) ;;
     .ret (.bin .add (.reg 14) (.reg 17)))
    (.store (.reg 14) (.reg 10) ;;
     .store (.bin .add (.reg 14) (.const 1)) (.reg 11) ;;
     .assign 14 (.bin .add (.bin .add (.bin .add (.reg 14) (.const 4))
       (.bin .mul (.const 7) (.reg 10))) (.bin .mul (.const 9) (.reg 11))) ;;
     .assign 17 (.bin .add (.bin .add (.bin .add (.bin .add (.bin .add (.bin .add
       (.reg 5) (.reg 6)) (.reg 4)) (.reg 10)) (.reg 11)) (.reg 7)) (.const ASM_HDR_SIZE)) ;;
     .ret (.bin .add (.reg 14) (.reg 17)))

/-- `op 0` (Update) `[handle, graph, batch, words, edits, editWords, lengths, gradient, heap]`
(`r0..r8`). Dispatches on `mem[handle + ASM_HDR_NE]`: calls `fEmptyUpd` when empty, or copies
`batch` and `edits` onto fresh heap past `heap + 1 + 6 * k` (reserving `heap + 1 + 6 * k` for
`fChgPtr`), runs P1 `fOrdEdit`, P4 `fCFBatch`, stores `fChgPtr` at `heap + 1 + 6 * k`, and runs
`asmStepBranchesLoop` when nonempty. -/
def asmTopUpdateBody (fEmptyUpd fCopy fOrdEdit fCFBatch fBrStep : ℕ) : Stmt :=
  .assign 9 (.load (.reg 0)) ;;
  .assign 10 (.load (.bin .add (.reg 0) (.const ASM_HDR_K))) ;;
  .cond (.reg 9)
    (.store (.reg 8) (.reg 10) ;;
     .assign 14 (.bin .add (.bin .add (.reg 8) (.const 2)) (.bin .mul (.const 6) (.reg 10))) ;;
     .call 19 fCopy [.reg 2, .reg 14, .reg 3] ;;
     .assign 2 (.reg 14) ;;
     .assign 14 (.bin .add (.reg 14) (.reg 3)) ;;
     .call 19 fCopy [.reg 4, .reg 14, .reg 5] ;;
     .assign 4 (.reg 14) ;;
     .assign 14 (.bin .add (.reg 14) (.reg 5)) ;;
     .assign 11 (.load (.bin .add (.reg 0) (.const ASM_HDR_ORDH))) ;;
     .call 14 fOrdEdit [.reg 11, .reg 4, .reg 5, .reg 14] ;;
     .assign 11 (.load (.bin .add (.reg 0) (.const ASM_HDR_CFH))) ;;
     .assign 13 (.reg 14) ;;
     .call 14 fCFBatch [.reg 11, .reg 2, .reg 3, .reg 14] ;;
     .assign 13 (.load (.reg 13)) ;;
     .store (.bin .add (.bin .add (.reg 8) (.const 1)) (.bin .mul (.const 6) (.reg 10))) (.reg 13) ;;
     .assign 12 (.load (.bin .add (.reg 0) (.const ASM_HDR_TBL))) ;;
     asmStepBranchesLoop fBrStep ;;
     .ret (.reg 14))
    (.call 14 fEmptyUpd [.reg 10, .reg 8] ;;
     .ret (.reg 14))

/-- `op 1` (Restart) `[handle, branch, heap]` (`r0, r1, r2`). -/
def asmTopRestartBody (fBrRestart : ℕ) : Stmt :=
  .assign 3 (.load (.reg 0)) ;;
  .cond (.reg 3)
    (.assign 4 (.load (.bin .add (.reg 0) (.const ASM_HDR_CFH))) ;;
     .assign 5 (.load (.bin .add (.reg 0) (.const ASM_HDR_TBL))) ;;
     .assign 6 (.load (.bin .add (.reg 5) (.reg 1))) ;;
     .call 7 fBrRestart [.reg 6, .reg 4, .reg 1, .reg 2] ;;
     .ret (.reg 7))
    (.ret (.reg 2))

/-- `op 2` (Read LSF) `[handle, branch, graph, heap]` (`r0, r1, r2, r3`). -/
def asmTopReadLSFBody (fBrReadLSF : ℕ) : Stmt :=
  .assign 4 (.load (.reg 0)) ;;
  .cond (.reg 4)
    (.assign 5 (.load (.bin .add (.reg 0) (.const ASM_HDR_TBL))) ;;
     .assign 6 (.load (.bin .add (.reg 5) (.reg 1))) ;;
     .call 7 fBrReadLSF [.reg 6, .reg 3] ;;
     .ret (.reg 7))
    (.assign 5 (.bin .add (.reg 0) (.const ASM_HDR_EMPTYG)) ;;
     .store (.reg 3) (.reg 5) ;;
     .store (.bin .add (.reg 3) (.const 1)) (.reg 5) ;;
     .ret (.bin .add (.reg 3) (.const 5)))

/-- `op 3` (Read S) `[handle, branch, heap]` (`r0, r1, r2`). -/
def asmTopReadSBody (fBrReadS : ℕ) : Stmt :=
  .assign 3 (.load (.reg 0)) ;;
  .cond (.reg 3)
    (.assign 4 (.load (.bin .add (.reg 0) (.const ASM_HDR_TBL))) ;;
     .assign 5 (.load (.bin .add (.reg 4) (.reg 1))) ;;
     .call 6 fBrReadS [.reg 5, .reg 2] ;;
     .ret (.reg 6))
    (.store (.reg 2) (.bin .add (.reg 0) (.const ASM_HDR_SIZE)) ;;
     .ret (.bin .add (.reg 2) (.const 1)))

/-- `op 4` (Read Embedding) `[handle, branch, graph, heap]` (`r0, r1, r2, r3`). -/
def asmTopReadEmbBody (fBrReadEmb : ℕ) : Stmt :=
  .assign 4 (.load (.reg 0)) ;;
  .cond (.reg 4)
    (.assign 5 (.load (.bin .add (.reg 0) (.const ASM_HDR_TBL))) ;;
     .assign 6 (.load (.bin .add (.reg 5) (.reg 1))) ;;
     .call 7 fBrReadEmb [.reg 6, .reg 3] ;;
     .ret (.reg 7))
    (.ret (.bin .add (.reg 3) (.const 2)))

/-- `op 5` (Read Order) `[handle, branch, heap]` (`r0, r1, r2`). -/
def asmTopReadOrdBody (fBrReadOrd : ℕ) : Stmt :=
  .assign 3 (.load (.reg 0)) ;;
  .cond (.reg 3)
    (.assign 4 (.load (.bin .add (.reg 0) (.const ASM_HDR_TBL))) ;;
     .assign 5 (.load (.bin .add (.reg 4) (.reg 1))) ;;
     .call 6 fBrReadOrd [.reg 5, .reg 2] ;;
     .ret (.reg 6))
    (.store (.reg 2) (.bin .add (.reg 2) (.const 1)) ;;
     .ret (.bin .add (.reg 2) (.const 2)))

/-! ## Relocatable 29-procedure top-layer block -/

/-- The 29 deterministic procedures of the top layer relocated to base `b`:
* `b + 0 .. b + 18`: `ordStoreProcs b` (P1)
* `b + 19`: `asmCompactOrdBody`
* `b + 20`: `asmEmptyUpdateBody`
* `b + 21`: `WordRAM.copyWords`
* `b + 22`: `init`
* `b + 23 .. b + 28`: `op 0 .. op 5`. -/
def asmTopProcs (b fCFInit fCFBatch fCFExport : ℕ) (bp : AsmBranchProcs) : List Stmt :=
  ordStoreProcs b ++
  [ asmCompactOrdBody,
    asmEmptyUpdateBody,
    WordRAM.copyWords,
    asmTopInitBody (b + 19) (ordStoreInit b) fCFInit fCFExport bp.fInit,
    asmTopUpdateBody (b + 20) (b + 21) (ordStoreOp b 0) fCFBatch bp.fStep,
    asmTopRestartBody bp.fRestart,
    asmTopReadLSFBody bp.fReadLSF,
    asmTopReadSBody bp.fReadS,
    asmTopReadEmbBody bp.fReadEmb,
    asmTopReadOrdBody bp.fReadOrd ]

def asmTopCopyIdx (b : ℕ) : ℕ := b + 21

def asmTopInitIdx (b : ℕ) : ℕ := b + 22

def asmTopOpIdx (b i : ℕ) : ℕ :=
  match i with
  | 0 => b + 23
  | 1 => b + 24
  | 2 => b + 25
  | 3 => b + 26
  | 4 => b + 27
  | _ => b + 28

/-- Program `p` contains `asmTopProcs b fCFInit fCFBatch fCFExport bp` at base `b`. -/
def HasAsmTopProcs (p : Program) (b fCFInit fCFBatch fCFExport : ℕ) (bp : AsmBranchProcs) : Prop :=
  ∀ i < (asmTopProcs b fCFInit fCFBatch fCFExport bp).length,
    p.procs[b + i]? = (asmTopProcs b fCFInit fCFBatch fCFExport bp)[i]?

theorem asmTopProcs_length (b fCFInit fCFBatch fCFExport : ℕ) (bp : AsmBranchProcs) :
    (asmTopProcs b fCFInit fCFBatch fCFExport bp).length = 29 := rfl

theorem HasAsmTopProcs.hasOrdStore {p : Program} {b fCFInit fCFBatch fCFExport : ℕ} {bp : AsmBranchProcs}
    (h : HasAsmTopProcs p b fCFInit fCFBatch fCFExport bp) : HasOrdStoreProcs p b := by
  intro i hi
  have hlen : (ordStoreProcs b).length = 19 := rfl
  have h1 := h i (by simp [asmTopProcs, hlen]; omega)
  simpa [asmTopProcs, List.getElem?_append_left hi] using h1

theorem HasAsmTopProcs.at_compact {p : Program} {b fCFInit fCFBatch fCFExport : ℕ} {bp : AsmBranchProcs}
    (h : HasAsmTopProcs p b fCFInit fCFBatch fCFExport bp) :
    p.procs[b + 19]? = some asmCompactOrdBody := by
  simpa [asmTopProcs, ordStoreProcs] using h 19 (by rw [asmTopProcs_length]; omega)

theorem HasAsmTopProcs.at_emptyUpd {p : Program} {b fCFInit fCFBatch fCFExport : ℕ} {bp : AsmBranchProcs}
    (h : HasAsmTopProcs p b fCFInit fCFBatch fCFExport bp) :
    p.procs[b + 20]? = some asmEmptyUpdateBody := by
  simpa [asmTopProcs, ordStoreProcs] using h 20 (by rw [asmTopProcs_length]; omega)

theorem HasAsmTopProcs.at_copy {p : Program} {b fCFInit fCFBatch fCFExport : ℕ} {bp : AsmBranchProcs}
    (h : HasAsmTopProcs p b fCFInit fCFBatch fCFExport bp) :
    p.procs[asmTopCopyIdx b]? = some WordRAM.copyWords := by
  simpa [asmTopCopyIdx, asmTopProcs, ordStoreProcs] using h 21 (by rw [asmTopProcs_length]; omega)

theorem HasAsmTopProcs.copy_meetsContract {w : ℕ} {p : Program} {b fCFInit fCFBatch fCFExport : ℕ}
    {bp : AsmBranchProcs} (h : HasAsmTopProcs p b fCFInit fCFBatch fCFExport bp) :
    MeetsContract w p (asmTopCopyIdx b) (copyWordsContract w) :=
  copyWords_meetsContract (fun i hi => by
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0; simpa using h.at_copy)

theorem HasAsmTopProcs.at_init {p : Program} {b fCFInit fCFBatch fCFExport : ℕ} {bp : AsmBranchProcs}
    (h : HasAsmTopProcs p b fCFInit fCFBatch fCFExport bp) :
    p.procs[asmTopInitIdx b]? =
      some (asmTopInitBody (b + 19) (ordStoreInit b) fCFInit fCFExport bp.fInit) := by
  simpa [asmTopInitIdx, asmTopProcs, ordStoreProcs] using h 22 (by rw [asmTopProcs_length]; omega)

theorem HasAsmTopProcs.at_op0 {p : Program} {b fCFInit fCFBatch fCFExport : ℕ} {bp : AsmBranchProcs}
    (h : HasAsmTopProcs p b fCFInit fCFBatch fCFExport bp) :
    p.procs[asmTopOpIdx b 0]? =
      some (asmTopUpdateBody (b + 20) (b + 21) (ordStoreOp b 0) fCFBatch bp.fStep) := by
  simpa [asmTopOpIdx, asmTopProcs, ordStoreProcs] using h 23 (by rw [asmTopProcs_length]; omega)

theorem HasAsmTopProcs.at_op1 {p : Program} {b fCFInit fCFBatch fCFExport : ℕ} {bp : AsmBranchProcs}
    (h : HasAsmTopProcs p b fCFInit fCFBatch fCFExport bp) :
    p.procs[asmTopOpIdx b 1]? = some (asmTopRestartBody bp.fRestart) := by
  simpa [asmTopOpIdx, asmTopProcs, ordStoreProcs] using h 24 (by rw [asmTopProcs_length]; omega)

theorem HasAsmTopProcs.at_op2 {p : Program} {b fCFInit fCFBatch fCFExport : ℕ} {bp : AsmBranchProcs}
    (h : HasAsmTopProcs p b fCFInit fCFBatch fCFExport bp) :
    p.procs[asmTopOpIdx b 2]? = some (asmTopReadLSFBody bp.fReadLSF) := by
  simpa [asmTopOpIdx, asmTopProcs, ordStoreProcs] using h 25 (by rw [asmTopProcs_length]; omega)

theorem HasAsmTopProcs.at_op3 {p : Program} {b fCFInit fCFBatch fCFExport : ℕ} {bp : AsmBranchProcs}
    (h : HasAsmTopProcs p b fCFInit fCFBatch fCFExport bp) :
    p.procs[asmTopOpIdx b 3]? = some (asmTopReadSBody bp.fReadS) := by
  simpa [asmTopOpIdx, asmTopProcs, ordStoreProcs] using h 26 (by rw [asmTopProcs_length]; omega)

theorem HasAsmTopProcs.at_op4 {p : Program} {b fCFInit fCFBatch fCFExport : ℕ} {bp : AsmBranchProcs}
    (h : HasAsmTopProcs p b fCFInit fCFBatch fCFExport bp) :
    p.procs[asmTopOpIdx b 4]? = some (asmTopReadEmbBody bp.fReadEmb) := by
  simpa [asmTopOpIdx, asmTopProcs, ordStoreProcs] using h 27 (by rw [asmTopProcs_length]; omega)

theorem HasAsmTopProcs.at_op5 {p : Program} {b fCFInit fCFBatch fCFExport : ℕ} {bp : AsmBranchProcs}
    (h : HasAsmTopProcs p b fCFInit fCFBatch fCFExport bp) :
    p.procs[asmTopOpIdx b 5]? = some (asmTopReadOrdBody bp.fReadOrd) := by
  simpa [asmTopOpIdx, asmTopProcs, ordStoreProcs] using h 28 (by rw [asmTopProcs_length]; omega)

/-- Every procedure in `asmTopProcs` is deterministic (`Stmt.NoRand`). -/
theorem asmTopProcs_noRand (b fCFInit fCFBatch fCFExport : ℕ) (bp : AsmBranchProcs) :
    ∀ s ∈ asmTopProcs b fCFInit fCFBatch fCFExport bp, s.NoRand := by
  intro s hs
  unfold asmTopProcs at hs
  rcases List.mem_append.mp hs with h1 | h2
  · exact ordStoreProcs_noRand b s h1
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
    rcases h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact asmCompactOrdBody_noRand
    · exact asmEmptyUpdateBody_noRand
    · simp [WordRAM.copyWords, forRange, forUp, Stmt.NoRand]
    · simp [asmTopInitBody, asmInitBranchesLoop_noRand, Stmt.NoRand]
    · simp [asmTopUpdateBody, asmStepBranchesLoop_noRand, Stmt.NoRand]
    · simp [asmTopRestartBody, Stmt.NoRand]
    · simp [asmTopReadLSFBody, Stmt.NoRand]
    · simp [asmTopReadSBody, Stmt.NoRand]
    · simp [asmTopReadEmbBody, Stmt.NoRand]
    · simp [asmTopReadOrdBody, Stmt.NoRand]

/-! ## Input-independent parameters and space allocation -/

/-- Input-independent word-size exponent of the top-layer sparse-core program. Depends ONLY on
`capExp` (never on `limbMul`): its floor `asmP10WordExp capExp` covers P10's update word condition
`(vCap + tCap + 2) ^ 2 * (L_w + 1) < 2 ^ w` as well as `16 < 2 ^ w` and P1's `(vCap + eCap + 2) ^ 2`.
At `capExp = 3`, `asmP10WordExp 3 = 24 ≤ 39`. -/
def asmTopWordExp (CFS : AsmCompFamilySpec) (BRS : AsmBranchSpec) (capExp : ℕ) : ℕ :=
  max (max (CFS.wordExp capExp) (BRS.wordExp capExp)) (asmP10WordExp capExp)

/-- Input-independent `SparseCoreOrdParams` combining P1 (`ordStoreMul = 32000`), P4 (`CFS`),
the branch module (`BRS`), and the top-layer dispatch overhead. Its `wordExp` is
`asmTopWordExp CFS BRS capExp` (independent of `limbMul`). -/
def asmTopParams (CFS : AsmCompFamilySpec) (BRS : AsmBranchSpec) (capExp limbMul : ℕ) :
    SparseCoreOrdParams where
  mul := 32000 * 6 * (capExp + 1) + 3 * CFS.mul capExp limbMul + BRS.mul capExp limbMul + 500
  readout := BRS.readout capExp + 60
  wordExp := asmTopWordExp CFS BRS capExp

/-- Input-independent space bound function `allocation` for `sparseCoreOrdMachineContractKFR`,
parameterized by a uniform logical size bound `sizeParam` (with
`M + N + k + vCap + eCap + L + depth ≤ sizeParam`):
* `i = 6` (`init`): pure polynomial in `(k, M, N, L)` (independent of `heap`, `depth`, and
  `sizeParam`, using `vCap + eCap + 2 ≤ (M + N + 2) ^ capExp` and `depth ≤ M + N + k + L`).
* `i = 0` (`update`): pure polynomial in `sizeParam + words + editWords` (independent of `heap`).
* `i = 1` (`restart`): pure polynomial in `sizeParam` (independent of `heap`). -/
def asmTopAlloc (CFS : AsmCompFamilySpec) (BRS : AsmBranchSpec) (capExp sizeParam : ℕ)
    (i : ℕ) (args : List ℕ) : ℕ :=
  match i with
  | 6 =>
    let k := args.getD 4 0
    let M := args.getD 5 0
    let N := args.getD 6 0
    let L := args.getD 7 0
    let capB := (M + N + 2) ^ capExp
    ASM_HDR_SIZE + (1 + 6 * M) + (16 + 2 * capB + 16 * capB) +
      (CFS.initSpace capExp).eval (capB + L + k) + k +
      k * ((CFS.exportSpace capExp).eval (M + N + k + capB + L) +
        (BRS.initSpace capExp).eval (2 * (M + N + k + capB + L))) +
      (M + N + k + capB + L + ASM_HDR_SIZE)
  | 0 =>
    let words := args.getD 3 0
    let editWords := args.getD 5 0
    (4 + 7 * sizeParam) + words + editWords + (3 * editWords + 2) +
      (CFS.batchSpace capExp).eval (sizeParam + words) +
      sizeParam * (BRS.stepSpace capExp).eval (sizeParam + words + editWords)
  | 1 =>
    (BRS.restartSpace capExp).eval sizeParam
  | _ => 0

theorem ordArenaSize_le_of_cap {capExp limbMul L M N vCap eCap : ℕ}
    (hcap : SparseCoreCapHyp capExp limbMul L M N vCap eCap) :
    ordArenaSize vCap eCap ≤ 16 + 2 * (M + N + 2) ^ capExp + 16 * (M + N + 2) ^ capExp := by
  have h1 := hcap.1
  unfold ordArenaSize
  omega

theorem wordBound_ge_16 {CFS : AsmCompFamilySpec} {BRS : AsmBranchSpec} {capExp limbMul w M N : ℕ}
    (hw : (M + N + 2) ^ (asmTopParams CFS BRS capExp limbMul).wordExp < 2 ^ w) :
    16 < 2 ^ w := by
  have hexp : 4 ≤ (asmTopParams CFS BRS capExp limbMul).wordExp :=
    le_trans (asmP10WordExp_ge_four capExp) (le_max_right _ _)
  have h1 : 16 = 2 ^ 4 := by norm_num
  have h2 : 2 ^ 4 ≤ (M + N + 2) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have h3 : (M + N + 2) ^ 4 ≤ (M + N + 2) ^ (asmTopParams CFS BRS capExp limbMul).wordExp :=
    Nat.pow_le_pow_right (by omega) hexp
  omega

/-! ## Shared execution helpers for `asmTopInitBody` and `asmTopUpdateBody` -/

/-- Execute the 11-statement prefix of `asmTopInitBody` (3 `DynGraph` loads, 7 header stores,
and `r14 := heap + ASM_HDR_SIZE`), returning an opaque post-prefix state `s11` and a
continuation wrapper that prepends the prefix to any suffix `rest`. -/
theorem asmTopInit_preamble {w graph lengths gradient ord k M N L Pfp depth heap vCap eCap gn pos : ℕ}
    {p : Program} (ω : ℕ → Bool) {mem : ℕ → ℕ}
    (hw16 : 16 < 2 ^ w) (hgraph2 : graph + 2 < 2 ^ w) (hheap20 : heap + ASM_HDR_SIZE < 2 ^ w)
    (hm0 : mem graph = vCap) (hm1 : mem (graph + 1) = eCap) (hm2 : mem (graph + 2) = gn)
    (hz : ZeroFrom mem heap) :
    let st0 := startState [graph, lengths, gradient, ord, k, M, N, L, Pfp, depth, heap] mem pos
    ∃ s11 : State,
      (∀ (rest : Stmt) (o : Outcome) (st' : State) (cR bnd : ℕ),
        Runs w p ω rest s11 o st' cR → cR + 80 ≤ bnd →
        ∃ cAll, Runs w p ω (
          .assign 19 (.reg 9) ;;
          .assign 9 (.reg 10) ;;
          .assign 10 (.load (.reg 0)) ;;
          .assign 11 (.load (.bin .add (.reg 0) (.const 1))) ;;
          .assign 16 (.load (.bin .add (.reg 0) (.const 2))) ;;
          .store (.bin .add (.reg 9) (.const ASM_HDR_K)) (.reg 4) ;;
          .store (.bin .add (.reg 9) (.const ASM_HDR_M)) (.reg 5) ;;
          .store (.bin .add (.reg 9) (.const ASM_HDR_N)) (.reg 6) ;;
          .store (.bin .add (.reg 9) (.const ASM_HDR_VCAP)) (.reg 10) ;;
          .store (.bin .add (.reg 9) (.const ASM_HDR_ECAP)) (.reg 11) ;;
          .store (.bin .add (.reg 9) (.const ASM_HDR_L)) (.reg 7) ;;
          .store (.bin .add (.reg 9) (.const ASM_HDR_PFP)) (.reg 8) ;;
          .assign 14 (.bin .add (.reg 9) (.const ASM_HDR_SIZE)) ;;
          rest) st0 o st' cAll ∧ cAll ≤ bnd) ∧
      (s11.regs 0 = graph ∧ s11.regs 1 = lengths ∧ s11.regs 3 = ord ∧ s11.regs 4 = k ∧
        s11.regs 5 = M ∧ s11.regs 6 = N ∧ s11.regs 7 = L ∧ s11.regs 8 = Pfp ∧
        s11.regs 9 = heap ∧ s11.regs 10 = vCap ∧ s11.regs 11 = eCap ∧ s11.regs 16 = gn) ∧
      s11.regs 14 = heap + ASM_HDR_SIZE ∧
      s11.regs 19 = depth ∧
      (∀ addr < heap, s11.mem addr = mem addr) ∧
      (∀ addr, heap + 8 ≤ addr → s11.mem addr = 0) ∧
      s11.mem (heap + ASM_HDR_NE) = 0 ∧
      (s11.mem (heap + ASM_HDR_K) = k ∧ s11.mem (heap + ASM_HDR_M) = M ∧
        s11.mem (heap + ASM_HDR_N) = N ∧ s11.mem (heap + ASM_HDR_VCAP) = vCap ∧
        s11.mem (heap + ASM_HDR_ECAP) = eCap ∧ s11.mem (heap + ASM_HDR_L) = L ∧
        s11.mem (heap + ASM_HDR_PFP) = Pfp) := by
  intro st0
  have h1w : 1 < 2 ^ w := by omega
  have hhdr : ASM_HDR_SIZE = 20 := rfl
  have hst_hdr : ∀ (st : State) (off val : ℕ) (r : ℕ),
      st.regs 9 = heap → st.regs r = val → off < ASM_HDR_SIZE →
      Runs w p ω (.store (.bin .add (.reg 9) (.const off)) (.reg r)) st .normal
        { st with mem := Function.update st.mem (heap + off) val }
        ((Expr.bin .add (.reg 9) (.const off)).size + (Expr.reg r).size + 1) := by
    intro st off val r hr9 hrr hoff
    exact runs_store_iff.mpr ⟨heap + off, val,
      Expr.eval_add (Expr.eval_reg_of_eq hr9) (Expr.eval_const (by omega)) (by omega),
      Expr.eval_reg_of_eq hrr, rfl, rfl, rfl⟩
  have hp0a : Runs w p ω (.assign 19 (.reg 9)) st0 .normal
      { st0 with regs := Function.update st0.regs 19 depth } _ :=
    runs_assign_iff.mpr ⟨depth, Expr.eval_reg_of_eq (by simp [st0, startState]), rfl, rfl, rfl⟩
  set s0a : State := { st0 with regs := Function.update st0.regs 19 depth }
  have hp0b : Runs w p ω (.assign 9 (.reg 10)) s0a .normal
      { s0a with regs := Function.update s0a.regs 9 heap } _ :=
    runs_assign_iff.mpr ⟨heap, Expr.eval_reg_of_eq (by simp [s0a, st0, startState]), rfl, rfl, rfl⟩
  set s0b : State := { s0a with regs := Function.update s0a.regs 9 heap }
  have hp1 : Runs w p ω (.assign 10 (.load (.reg 0))) s0b .normal
      { s0b with regs := Function.update s0b.regs 10 vCap } _ :=
    runs_assign_iff.mpr ⟨vCap, Expr.eval_load_of_eq (w := w) (Expr.eval_reg_of_eq (by simp [s0b, s0a, st0, startState])) hm0, rfl, rfl, rfl⟩
  set s1 : State := { s0b with regs := Function.update s0b.regs 10 vCap }
  have hp2 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 0) (.const 1)))) s1 .normal
      { s1 with regs := Function.update s1.regs 11 eCap } _ :=
    runs_assign_iff.mpr ⟨eCap, Expr.eval_load_of_eq (w := w)
      (Expr.eval_add (Expr.eval_reg_of_eq (v := graph) (by simp [s1, s0b, s0a, st0, startState])) (Expr.eval_const h1w) (by omega)) hm1,
      rfl, rfl, rfl⟩
  set s2 : State := { s1 with regs := Function.update s1.regs 11 eCap }
  have hp3 : Runs w p ω (.assign 16 (.load (.bin .add (.reg 0) (.const 2)))) s2 .normal
      { s2 with regs := Function.update s2.regs 16 gn } _ :=
    runs_assign_iff.mpr ⟨gn, Expr.eval_load_of_eq (w := w)
      (Expr.eval_add (Expr.eval_reg_of_eq (v := graph) (by simp [s2, s1, s0b, s0a, st0, startState])) (Expr.eval_const (by omega)) (by omega)) hm2,
      rfl, rfl, rfl⟩
  set s3 : State := { s2 with regs := Function.update s2.regs 16 gn }
  have hp4 := hst_hdr s3 ASM_HDR_K k 4 (by simp [s3, s2, s1, s0b]) (by simp [s3, s2, s1, s0b, s0a, st0, startState]) (by decide)
  set s4 : State := { s3 with mem := Function.update s3.mem (heap + ASM_HDR_K) k }
  have hp5 := hst_hdr s4 ASM_HDR_M M 5 (by simp [s4, s3, s2, s1, s0b]) (by simp [s4, s3, s2, s1, s0b, s0a, st0, startState]) (by decide)
  set s5 : State := { s4 with mem := Function.update s4.mem (heap + ASM_HDR_M) M }
  have hp6 := hst_hdr s5 ASM_HDR_N N 6 (by simp [s5, s4, s3, s2, s1, s0b]) (by simp [s5, s4, s3, s2, s1, s0b, s0a, st0, startState]) (by decide)
  set s6 : State := { s5 with mem := Function.update s5.mem (heap + ASM_HDR_N) N }
  have hp7 := hst_hdr s6 ASM_HDR_VCAP vCap 10 (by simp [s6, s5, s4, s3, s2, s1, s0b]) (by simp [s6, s5, s4, s3, s2, s1]) (by decide)
  set s7 : State := { s6 with mem := Function.update s6.mem (heap + ASM_HDR_VCAP) vCap }
  have hp8 := hst_hdr s7 ASM_HDR_ECAP eCap 11 (by simp [s7, s6, s5, s4, s3, s2, s1, s0b]) (by simp [s7, s6, s5, s4, s3, s2]) (by decide)
  set s8 : State := { s7 with mem := Function.update s7.mem (heap + ASM_HDR_ECAP) eCap }
  have hp9 := hst_hdr s8 ASM_HDR_L L 7 (by simp [s8, s7, s6, s5, s4, s3, s2, s1, s0b]) (by simp [s8, s7, s6, s5, s4, s3, s2, s1, s0b, s0a, st0, startState]) (by decide)
  set s9 : State := { s8 with mem := Function.update s8.mem (heap + ASM_HDR_L) L }
  have hp10 := hst_hdr s9 ASM_HDR_PFP Pfp 8 (by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, s0b]) (by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, s0b, s0a, st0, startState]) (by decide)
  set s10 : State := { s9 with mem := Function.update s9.mem (heap + ASM_HDR_PFP) Pfp }
  have hp11 : Runs w p ω (.assign 14 (.bin .add (.reg 9) (.const ASM_HDR_SIZE))) s10 .normal
      { s10 with regs := Function.update s10.regs 14 (heap + ASM_HDR_SIZE) } _ :=
    runs_assign_iff.mpr ⟨heap + ASM_HDR_SIZE,
      Expr.eval_add (Expr.eval_reg_of_eq (v := heap) (by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0b]))
        (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
  set s11 : State := { s10 with regs := Function.update s10.regs 14 (heap + ASM_HDR_SIZE) }
  refine ⟨s11, fun rest o st' cR bnd hR hbnd => ?_, ?_, by simp [s11], by simp [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0b, s0a], ?_, ?_, ?_, ?_⟩
  · refine ⟨_, runs_seq_iff.mpr (Or.inr ⟨s0a, _, _, hp0a,
      runs_seq_iff.mpr (Or.inr ⟨s0b, _, _, hp0b,
        runs_seq_iff.mpr (Or.inr ⟨s1, _, _, hp1,
          runs_seq_iff.mpr (Or.inr ⟨s2, _, _, hp2,
            runs_seq_iff.mpr (Or.inr ⟨s3, _, _, hp3,
              runs_seq_iff.mpr (Or.inr ⟨s4, _, _, hp4,
                runs_seq_iff.mpr (Or.inr ⟨s5, _, _, hp5,
                  runs_seq_iff.mpr (Or.inr ⟨s6, _, _, hp6,
                    runs_seq_iff.mpr (Or.inr ⟨s7, _, _, hp7,
                      runs_seq_iff.mpr (Or.inr ⟨s8, _, _, hp8,
                        runs_seq_iff.mpr (Or.inr ⟨s9, _, _, hp9,
                          runs_seq_iff.mpr (Or.inr ⟨s10, _, _, hp10,
                            runs_seq_iff.mpr (Or.inr ⟨s11, _, _, hp11, hR, rfl⟩),
                            rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), ?_⟩
    simp only [Expr.size]; omega
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0b, s0a, st0, startState]
  · intro addr ha
    dsimp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0b, s0a, st0]
    repeat rw [Function.update_of_ne (by unfold ASM_HDR_K ASM_HDR_M ASM_HDR_N ASM_HDR_VCAP ASM_HDR_ECAP ASM_HDR_L ASM_HDR_PFP at *; omega)]
    rfl
  · intro addr ha
    dsimp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0b, s0a, st0]
    repeat rw [Function.update_of_ne (by unfold ASM_HDR_K ASM_HDR_M ASM_HDR_N ASM_HDR_VCAP ASM_HDR_ECAP ASM_HDR_L ASM_HDR_PFP at *; omega)]
    exact hz addr (by omega)
  · dsimp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0b, s0a, st0]
    repeat rw [Function.update_of_ne (by unfold ASM_HDR_NE ASM_HDR_K ASM_HDR_M ASM_HDR_N ASM_HDR_VCAP ASM_HDR_ECAP ASM_HDR_L ASM_HDR_PFP at *; omega)]
    exact hz _ (by omega)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · dsimp only [s11, s10, s9, s8, s7, s6, s5, s4]
      simp [ASM_HDR_K, ASM_HDR_M, ASM_HDR_N, ASM_HDR_VCAP, ASM_HDR_ECAP, ASM_HDR_L, ASM_HDR_PFP]

/-- Execute the shared reserve-and-return tail of `asmTopInitBody`. -/
theorem asmTopInit_tail {w k M N L vCap eCap hCur : ℕ} {p : Program} (ω : ℕ → Bool) (st : State)
    (r4 : st.regs 4 = k) (r5 : st.regs 5 = M) (r6 : st.regs 6 = N) (r7 : st.regs 7 = L)
    (r10 : st.regs 10 = vCap) (r11 : st.regs 11 = eCap) (r14 : st.regs 14 = hCur)
    (hlt : hCur + (M + N + k + vCap + eCap + L + ASM_HDR_SIZE) < 2 ^ w) :
    let resSz := M + N + k + vCap + eCap + L + ASM_HDR_SIZE
    ∃ cT, Runs w p ω
      (.assign 17 (.bin .add (.bin .add (.bin .add (.bin .add (.bin .add (.bin .add
        (.reg 5) (.reg 6)) (.reg 4)) (.reg 10)) (.reg 11)) (.reg 7)) (.const ASM_HDR_SIZE)) ;;
       .ret (.bin .add (.reg 14) (.reg 17))) st (.returned (hCur + resSz))
      { st with regs := Function.update st.regs 17 resSz } cT ∧ cT ≤ 25 := by
  intro resSz
  have hhdr : ASM_HDR_SIZE = 20 := rfl
  have ha17 : Runs w p ω
      (.assign 17 (.bin .add (.bin .add (.bin .add (.bin .add (.bin .add (.bin .add
        (.reg 5) (.reg 6)) (.reg 4)) (.reg 10)) (.reg 11)) (.reg 7)) (.const ASM_HDR_SIZE))) st .normal
      { st with regs := Function.update st.regs 17 resSz } _ :=
    runs_assign_iff.mpr ⟨resSz,
      Expr.eval_add (Expr.eval_add (Expr.eval_add (Expr.eval_add (Expr.eval_add (Expr.eval_add
        (Expr.eval_reg_of_eq r5) (Expr.eval_reg_of_eq r6) (by omega))
        (Expr.eval_reg_of_eq r4) (by omega))
        (Expr.eval_reg_of_eq r10) (by omega))
        (Expr.eval_reg_of_eq r11) (by omega))
        (Expr.eval_reg_of_eq r7) (by omega))
        (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
  have hret : Runs w p ω (.ret (.bin .add (.reg 14) (.reg 17)))
      { st with regs := Function.update st.regs 17 resSz } (.returned (hCur + resSz))
      { st with regs := Function.update st.regs 17 resSz } _ :=
    runs_ret_iff.mpr ⟨hCur + resSz,
      Expr.eval_add (Expr.eval_reg_of_eq (v := hCur) (by simp [r14])) (Expr.eval_reg_of_eq (by simp)) hlt,
      rfl, rfl, rfl⟩
  exact ⟨_, runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha17, hret, rfl⟩), by simp only [Expr.size]; omega⟩

/-- Execute the empty branch of `asmTopInitBody`: stores `[vCap, eCap]` at `hCur`, advances `r14`
by `dynGraphSize vCap eCap`, reserves `resSz`, and returns `hCur + dynGraphSize vCap eCap + resSz`. -/
theorem asmTopInit_emptyBranch {w k M N L vCap eCap hCur : ℕ} {p : Program} (ω : ℕ → Bool)
    (st : State) (hw16 : 16 < 2 ^ w)
    (r4 : st.regs 4 = k) (r5 : st.regs 5 = M) (r6 : st.regs 6 = N) (r7 : st.regs 7 = L)
    (r10 : st.regs 10 = vCap) (r11 : st.regs 11 = eCap) (r14 : st.regs 14 = hCur)
    (hz : ZeroFrom st.mem hCur)
    (hlt : hCur + dynGraphSize vCap eCap + (M + N + k + vCap + eCap + L + ASM_HDR_SIZE) < 2 ^ w) :
    let resSz := M + N + k + vCap + eCap + L + ASM_HDR_SIZE
    let stE : State :=
      { st with
        mem := Function.update (Function.update st.mem hCur vCap) (hCur + 1) eCap
        regs := Function.update (Function.update st.regs 14 (hCur + dynGraphSize vCap eCap)) 17 resSz }
    ∃ cE, Runs w p ω
      (.store (.reg 14) (.reg 10) ;;
       .store (.bin .add (.reg 14) (.const 1)) (.reg 11) ;;
       .assign 14 (.bin .add (.bin .add (.bin .add (.reg 14) (.const 4))
         (.bin .mul (.const 7) (.reg 10))) (.bin .mul (.const 9) (.reg 11))) ;;
       .assign 17 (.bin .add (.bin .add (.bin .add (.bin .add (.bin .add (.bin .add
         (.reg 5) (.reg 6)) (.reg 4)) (.reg 10)) (.reg 11)) (.reg 7)) (.const ASM_HDR_SIZE)) ;;
       .ret (.bin .add (.reg 14) (.reg 17)))
      st (.returned (hCur + dynGraphSize vCap eCap + resSz)) stE cE ∧ cE ≤ 70 ∧
      DynGraphAt stE.mem hCur vCap eCap emptyGraph ∧
      (∀ addr < hCur, stE.mem addr = st.mem addr) ∧
      ZeroFrom stE.mem (hCur + dynGraphSize vCap eCap) := by
  intro resSz stE
  have hsz : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  have h1w : 1 < 2 ^ w := by omega
  have hs1 : Runs w p ω (.store (.reg 14) (.reg 10)) st .normal
      { st with mem := Function.update st.mem hCur vCap } _ :=
    runs_store_iff.mpr ⟨hCur, vCap, Expr.eval_reg_of_eq r14, Expr.eval_reg_of_eq r10, rfl, rfl, rfl⟩
  set s1 : State := { st with mem := Function.update st.mem hCur vCap }
  have hs2 : Runs w p ω (.store (.bin .add (.reg 14) (.const 1)) (.reg 11)) s1 .normal
      { s1 with mem := Function.update s1.mem (hCur + 1) eCap } _ :=
    runs_store_iff.mpr ⟨hCur + 1, eCap,
      Expr.eval_add (Expr.eval_reg_of_eq (v := hCur) r14) (Expr.eval_const h1w) (by omega),
      Expr.eval_reg_of_eq r11, rfl, rfl, rfl⟩
  set s2 : State := { s1 with mem := Function.update s1.mem (hCur + 1) eCap }
  set s3 : State := { s2 with regs := Function.update s2.regs 14 (hCur + dynGraphSize vCap eCap) }
  have ha14 : Runs w p ω
      (.assign 14 (.bin .add (.bin .add (.bin .add (.reg 14) (.const 4))
        (.bin .mul (.const 7) (.reg 10))) (.bin .mul (.const 9) (.reg 11))))
      s2 .normal s3 _ :=
    runs_assign_iff.mpr ⟨hCur + dynGraphSize vCap eCap, by
      have hval : hCur + 4 + 7 * vCap + 9 * eCap = hCur + dynGraphSize vCap eCap := by omega
      rw [← hval]
      exact Expr.eval_add
        (Expr.eval_add
          (Expr.eval_add (Expr.eval_reg_of_eq (v := hCur) r14) (Expr.eval_const (by omega)) (by omega))
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := vCap) r10) (by omega))
          (by omega))
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := eCap) r11) (by omega))
        (by omega), rfl, rfl, rfl⟩
  obtain ⟨cT, htail, hcT⟩ := asmTopInit_tail (w := w) (p := p) ω s3
    (by simp [s3, s2, s1, r4]) (by simp [s3, s2, s1, r5]) (by simp [s3, s2, s1, r6])
    (by simp [s3, s2, s1, r7]) (by simp [s3, s2, s1, r10]) (by simp [s3, s2, s1, r11])
    (by simp [s3]) hlt
  refine ⟨_, runs_seq_iff.mpr (Or.inr ⟨s1, _, _, hs1,
    runs_seq_iff.mpr (Or.inr ⟨s2, _, _, hs2,
      runs_seq_iff.mpr (Or.inr ⟨s3, _, _, ha14, htail, rfl⟩), rfl⟩), rfl⟩),
    by simp only [Expr.size]; omega, dynGraphAt_emptyGraph_cap ?_ ?_ ?_, ?_, ?_⟩
  · dsimp only [stE]; rw [Function.update_of_ne (by omega), Function.update_self]
  · dsimp only [stE]; rw [Function.update_self]
  · intro j hj2 hjlt
    dsimp only [stE]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hz _ (by omega)
  · intro addr ha
    dsimp only [stE]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · intro addr ha
    dsimp only [stE]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hz addr (by omega)

/-- Execute the nonempty copy prefix of `asmTopUpdateBody` (store `k` at `heap`, copy `batch`
and `edits` past the `2 + 6 * k` output header reserving `heap + 1 + 6 * k` for `fChgPtr`),
returning an opaque post-copy state `st5f` and a continuation wrapper. -/
theorem asmTopUpdate_copies {w b hndl batch words edits editWords heap k : ℕ}
    {p : Program} (ω : ℕ → Bool) (st2 : State)
    (hcp : MeetsContract w p (b + 21) (copyWordsContract w))
    (hw16 : 16 < 2 ^ w)
    (hb_le : batch + words ≤ heap) (he_le : edits + editWords ≤ heap)
    (hsp : heap + 2 + 6 * k + words + editWords < 2 ^ w)
    (hr0 : st2.regs 0 = hndl) (hr2 : st2.regs 2 = batch) (hr3 : st2.regs 3 = words)
    (hr4 : st2.regs 4 = edits) (hr5 : st2.regs 5 = editWords) (hr8 : st2.regs 8 = heap)
    (hr10 : st2.regs 10 = k) (hz : ZeroFrom st2.mem heap) :
    let bCopy := heap + 2 + 6 * k
    let eCopy := bCopy + words
    let h0 := eCopy + editWords
    ∃ st5f : State,
      (∀ (rest : Stmt) (o : Outcome) (st' : State) (cR : ℕ),
        Runs w p ω rest st5f o st' cR →
        ∃ cAll, Runs w p ω (
          .store (.reg 8) (.reg 10) ;;
          .assign 14 (.bin .add (.bin .add (.reg 8) (.const 2)) (.bin .mul (.const 6) (.reg 10))) ;;
          .call 19 (b + 21) [.reg 2, .reg 14, .reg 3] ;;
          .assign 2 (.reg 14) ;;
          .assign 14 (.bin .add (.reg 14) (.reg 3)) ;;
          .call 19 (b + 21) [.reg 4, .reg 14, .reg 5] ;;
          .assign 4 (.reg 14) ;;
          .assign 14 (.bin .add (.reg 14) (.reg 5)) ;;
          rest) st2 o st' cAll ∧
          cAll ≤ cR + 17 * words + 17 * editWords + 80) ∧
      (st5f.regs 0 = hndl ∧ st5f.regs 2 = bCopy ∧ st5f.regs 3 = words ∧
        st5f.regs 4 = eCopy ∧ st5f.regs 5 = editWords ∧ st5f.regs 8 = heap ∧
        st5f.regs 10 = k ∧ st5f.regs 14 = h0) ∧
      (∀ addr < heap, st5f.mem addr = st2.mem addr) ∧
      st5f.mem heap = k ∧
      (∀ i < words, st5f.mem (bCopy + i) = st2.mem (batch + i)) ∧
      (∀ i < editWords, st5f.mem (eCopy + i) = st2.mem (edits + i)) ∧
      ZeroFrom st5f.mem h0 := by
  intro bCopy eCopy h0
  have h1w : 1 < 2 ^ w := by omega
  have hst_k : Runs w p ω (.store (.reg 8) (.reg 10)) st2 .normal
      { st2 with mem := Function.update st2.mem heap k } _ :=
    runs_store_iff.mpr ⟨heap, k, Expr.eval_reg_of_eq hr8, Expr.eval_reg_of_eq hr10, rfl, rfl, rfl⟩
  set st3 : State := { st2 with mem := Function.update st2.mem heap k }
  have ha14_0 : Runs w p ω (.assign 14 (.bin .add (.bin .add (.reg 8) (.const 2)) (.bin .mul (.const 6) (.reg 10)))) st3 .normal
      { st3 with regs := Function.update st3.regs 14 bCopy } _ :=
    runs_assign_iff.mpr ⟨bCopy,
      Expr.eval_add
        (Expr.eval_add (Expr.eval_reg_of_eq (v := heap) (by simp [st3, hr8])) (Expr.eval_const (by omega)) (by omega))
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := k) (by simp [st3, hr10])) (by omega))
        (by omega), rfl, rfl, rfl⟩
  set st4 : State := { st3 with regs := Function.update st3.regs 14 bCopy }
  obtain ⟨_, hcp1_at, oCp1, stCp1, cCp1, hrunCp1, hpostCp1, hcostCp1⟩ :=
    hcp [batch, bCopy, words] st4.mem st4.pos ω
      (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with rfl | rfl | rfl <;> omega)
      ⟨batch, bCopy, words, rfl, h1w, by omega, by omega, Or.inr (by omega)⟩
  rcases hpostCp1 with ⟨s1_, d1_, l1_, hcp1_args, -, hcp1_eq, hcp1_fr⟩
  simp only [List.cons.injEq, and_true] at hcp1_args
  rcases hcp1_args with ⟨rfl, rfl, rfl⟩
  have hcallCp1 : Runs w p ω (.call 19 (b + 21) [.reg 2, .reg 14, .reg 3]) st4 .normal
      { stCp1 with regs := Function.update st4.regs 19 oCp1.value }
      (argsSize [.reg 2, .reg 14, .reg 3] + cCp1 + 1) := by
    refine (runs_call_iff (r := 19) (f := b + 21) (st := st4) (o := .normal)
      (st' := { stCp1 with regs := Function.update st4.regs 19 oCp1.value })).mpr
      ⟨[batch, bCopy, words], _, oCp1, stCp1, cCp1, ?_, hcp1_at, hrunCp1, rfl, rfl, rfl⟩
    simp [evalArgs, Expr.eval, st4, st3, hr2, hr3]
  set st5a : State := { stCp1 with regs := Function.update st4.regs 19 oCp1.value }
  have ha2_bCopy : Runs w p ω (.assign 2 (.reg 14)) st5a .normal
      { st5a with regs := Function.update st5a.regs 2 bCopy } _ :=
    runs_assign_iff.mpr ⟨bCopy, Expr.eval_reg_of_eq (by simp [st5a, st4]), rfl, rfl, rfl⟩
  set st5b : State := { st5a with regs := Function.update st5a.regs 2 bCopy }
  have ha14_eCopy : Runs w p ω (.assign 14 (.bin .add (.reg 14) (.reg 3))) st5b .normal
      { st5b with regs := Function.update st5b.regs 14 eCopy } _ :=
    runs_assign_iff.mpr ⟨eCopy,
      Expr.eval_add (Expr.eval_reg_of_eq (v := bCopy) (by simp [st5b, st5a, st4]))
        (Expr.eval_reg_of_eq (v := words) (by simp [st5b, st5a, st4, st3, hr3])) (by omega), rfl, rfl, rfl⟩
  set st5c : State := { st5b with regs := Function.update st5b.regs 14 eCopy }
  obtain ⟨_, hcp2_at, oCp2, stCp2, cCp2, hrunCp2, hpostCp2, hcostCp2⟩ :=
    hcp [edits, eCopy, editWords] st5c.mem st5c.pos ω
      (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with rfl | rfl | rfl <;> omega)
      ⟨edits, eCopy, editWords, rfl, h1w, by omega, by omega, Or.inr (by omega)⟩
  rcases hpostCp2 with ⟨s2_, d2_, l2_, hcp2_args, -, hcp2_eq, hcp2_fr⟩
  simp only [List.cons.injEq, and_true] at hcp2_args
  rcases hcp2_args with ⟨rfl, rfl, rfl⟩
  have hcallCp2 : Runs w p ω (.call 19 (b + 21) [.reg 4, .reg 14, .reg 5]) st5c .normal
      { stCp2 with regs := Function.update st5c.regs 19 oCp2.value }
      (argsSize [.reg 4, .reg 14, .reg 5] + cCp2 + 1) := by
    refine (runs_call_iff (r := 19) (f := b + 21) (st := st5c) (o := .normal)
      (st' := { stCp2 with regs := Function.update st5c.regs 19 oCp2.value })).mpr
      ⟨[edits, eCopy, editWords], _, oCp2, stCp2, cCp2, ?_, hcp2_at, hrunCp2, rfl, rfl, rfl⟩
    simp [evalArgs, Expr.eval, st5c, st5b, st5a, st4, st3, hr4, hr5]
  set st5d : State := { stCp2 with regs := Function.update st5c.regs 19 oCp2.value }
  have ha4_eCopy : Runs w p ω (.assign 4 (.reg 14)) st5d .normal
      { st5d with regs := Function.update st5d.regs 4 eCopy } _ :=
    runs_assign_iff.mpr ⟨eCopy, Expr.eval_reg_of_eq (by simp [st5d, st5c]), rfl, rfl, rfl⟩
  set st5e : State := { st5d with regs := Function.update st5d.regs 4 eCopy }
  have ha14_h0 : Runs w p ω (.assign 14 (.bin .add (.reg 14) (.reg 5))) st5e .normal
      { st5e with regs := Function.update st5e.regs 14 h0 } _ :=
    runs_assign_iff.mpr ⟨h0,
      Expr.eval_add (Expr.eval_reg_of_eq (v := eCopy) (by simp [st5e, st5d, st5c]))
        (Expr.eval_reg_of_eq (v := editWords) (by simp [st5e, st5d, st5c, st5b, st5a, st4, st3, hr5]))
        (by omega), rfl, rfl, rfl⟩
  set st5f : State := { st5e with regs := Function.update st5e.regs 14 h0 }
  have hc1 : cCp1 ≤ 17 * words + 10 := by simpa [copyWordsContract] using hcostCp1
  have hc2 : cCp2 ≤ 17 * editWords + 10 := by simpa [copyWordsContract] using hcostCp2
  refine ⟨st5f, fun rest o st' cR hR => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨_, runs_seq_iff.mpr (Or.inr ⟨st3, _, _, hst_k,
      runs_seq_iff.mpr (Or.inr ⟨st4, _, _, ha14_0,
        runs_seq_iff.mpr (Or.inr ⟨st5a, _, _, hcallCp1,
          runs_seq_iff.mpr (Or.inr ⟨st5b, _, _, ha2_bCopy,
            runs_seq_iff.mpr (Or.inr ⟨st5c, _, _, ha14_eCopy,
              runs_seq_iff.mpr (Or.inr ⟨st5d, _, _, hcallCp2,
                runs_seq_iff.mpr (Or.inr ⟨st5e, _, _, ha4_eCopy,
                  runs_seq_iff.mpr (Or.inr ⟨st5f, _, _, ha14_h0, hR, rfl⟩),
                  rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), ?_⟩
    simp only [argsSize_cons, argsSize_nil, Expr.size]; omega
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [st5f, st5e, st5d, st5c, st5b, st5a, st4, st3, hr0, hr3, hr5, hr8, hr10]
  · intro addr ha
    change stCp2.mem addr = st2.mem addr
    rw [hcp2_fr addr (Or.inl (by omega))]
    change stCp1.mem addr = st2.mem addr
    rw [hcp1_fr addr (Or.inl (by omega))]
    dsimp only [st4, st3]; exact Function.update_of_ne (by omega) _ _
  · change stCp2.mem heap = k
    rw [hcp2_fr heap (Or.inl (by omega))]
    change stCp1.mem heap = k
    rw [hcp1_fr heap (Or.inl (by omega))]
    simp [st4, st3]
  · intro i hi
    change stCp2.mem (bCopy + i) = st2.mem (batch + i)
    rw [hcp2_fr (bCopy + i) (Or.inl (by omega)), hcp1_eq i hi]
    dsimp only [st4, st3]; exact Function.update_of_ne (by omega) _ _
  · intro i hi
    change stCp2.mem (eCopy + i) = st2.mem (edits + i)
    rw [hcp2_eq i hi]
    change stCp1.mem (edits + i) = st2.mem (edits + i)
    rw [hcp1_fr (edits + i) (Or.inl (by omega))]
    dsimp only [st4, st3]; exact Function.update_of_ne (by omega) _ _
  · intro addr ha
    change stCp2.mem addr = 0
    rw [hcp2_fr addr (Or.inr ha)]
    change stCp1.mem addr = 0
    rw [hcp1_fr addr (Or.inr (by omega))]
    dsimp only [st4, st3]; rw [Function.update_of_ne (by omega)]; exact hz addr (by omega)

end MinCostFlow.SparseCore.Program
