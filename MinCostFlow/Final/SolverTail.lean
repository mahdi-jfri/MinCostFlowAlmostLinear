module

public import MinCostFlow.LastLevelProgram.RelocatedProgram
public import MinCostFlow.MinRatio.SolverInitWired
public import MinCostFlow.MinRatio.OrdChainRefreshWired
public import MinCostFlow.MinRatio.ShiftQuotaWriter
public import MinCostFlow.MinRatio.WireFindCycle
public import MinCostFlow.MinRatio.ShiftLevelWired
public import MinCostFlow.MinRatio.WireRename
public import MinCostFlow.Final.CappedQuality
public import MinCostFlow.SparseCore.Program.AssemblyStatement
import MinCostFlow.Num.ModulePlacement

/-!
# The code tail of the min-ratio solver

In the linked solver program (`Final/CappedConnectedProgram.lean`), the cycle data structure sits
after the IPM runtime module (`mrdsCycleBase`) as `solverOpsProcs ++ tail`. The first `183`
procedures are the operation bodies `solverOpsProcs` (`MinRatio/MinRatioMachineAssembly.lean`),
which call four entry points in the tail: `cycleInit`, `chainRefreshProc`, `findCycleProc`, and
`shiftLevelProc`.

This file builds that tail as a relocatable procedure list `solverTail` at any base `b`:
1. At `b + 0 .. b + 11` (length `12`), the four top-level wired entries and their concrete helper
   procedures already in the library:
   - `b + 0`: `solverInitWiredBody` (`cycleInit`), calling `initConcrete` and `b + 1`;
   - `b + 1`: `initOverwriteIntThresholdsBody`, calling `b + 2` with `threshold`;
   - `b + 2`: `Scaling.Machine.clogTwoBody (b + 2)` (`clogTwoModule`);
   - `b + 3`: `ordChainRefreshWiredBody` (`chainRefresh`), calling `b + 4`, `ordChainCore`, `b + 5`;
   - `b + 4`: `level0BatchToOrdEditsBody`;
   - `b + 5`: `shiftQuotaWriterBody threshold`;
   - `b + 6`: `ordFindCycleWiredBody` (`findCycle`), calling `selectRoute` and `evalCycle`;
   - `b + 7`: `shiftLevelWiredBody` (`shiftLevel`), calling `shiftTermChain` and `shiftDeepChain`;
   - `b + 8 .. b + 10`: the three capped-quality procedures (`bitLengthBody`, `integerQualityBody`,
     `cappedQualityBody`), exposing `quality := b + 10`;
   - `b + 11`: `level0RenameBody` (level-`0` internal-name compaction).
2. At `lastBase := b + 12`, the real relocated last-level bodies
   `LastLevelProgram.packedLastLevelBodies lastGuest lastD lastC lastBase` (entries `lastBase + 15`
   and `fun _ => lastBase + 16`), with unconditional `NoRand` (`packedLastLevelBodies_noRand`).
3. At `scBase := lastBase + (packedLastLevelProgram lastGuest lastD lastC).procs.length`, the
   relocated sparse-core program `MinRatio.shiftProgramProcs scBase sc.prog` (entries
   `scBase + sc.init` and `fun i => scBase + sc.op i`), parameterized by the standalone
   `SparseCoreCode` data `sc`.
4. At `innerBase := scBase + sc.prog.procs.length`, the inner-level bodies `inner.procs env`,
   parameterized by `SolverInnerCode` receiving `SolverInnerEnv` with its own base and all
   external entry indices (`opsBase`, `quality`, `clog`, `level0Rename`, `scInit`, `scOp`,
   `lastInit`, `lastOp`).

Because the four solver entry indices (`b + 0`, `b + 3`, `b + 6`, `b + 7`) sit in the fixed-length
prefix before the last-level, sparse-core, and inner blocks, none of them depends on the length of
any module given as a parameter. We prove `HasAt` for every block, `NoRand` of the whole tail from `NoRand` of the
sparse-core and inner parts alone, contract and `DSRep.Implements` transfers (`clogTwo`,
`cappedQuality`, `shiftQuotaWriter`, `packedLastLevelBodies`, `SparseCoreOrdProgramUniform`), and
the wired step-spec bridges.
-/

@[expose] public section

namespace MinCostFlow.Final

open WordRAM MinRatio SparseCore SparseCore.Program DynSpanner.Program LastLevelProgram Chain
  IPM.Machine Scaling.Machine

/-! ## Parameters for the code parts -/

/-- Code data of the standalone sparse-core program (`SparseCoreOrdProgramUniform`, Lemma 5.17,
page 23): the standalone `Program` and its initialization and operation entry indices. -/
structure SparseCoreCode where
  prog : Program
  init : ℕ
  op : ℕ → ℕ

/-- External procedure indices available to the inner-level bodies of the solver:
their own base `innerBase`, the base `opsBase` of `solverOpsProcs` (giving `copyWords`, numeric
modules, and `pathTreeBodies 4 (opsBase + 81)`), the capped quality entry `quality`, the
ceiling-log entry `clog`, the level-`0` renaming entry `level0Rename`, the relocated sparse-core
entries `(scInit, scOp)`, and the relocated last-level entries `(lastInit, lastOp)`. -/
structure SolverInnerEnv where
  innerBase : ℕ
  opsBase : ℕ
  quality : ℕ
  clog : ℕ
  level0Rename : ℕ
  scInit : ℕ
  scOp : ℕ → ℕ
  lastInit : ℕ
  lastOp : ℕ → ℕ

/-- Code data of the six inner-level subroutines (`MinRatio/Wire*.lean`): a relocatable procedure
list `procs env` together with the six entry offsets relative to `env.innerBase` (for
`OrdInitConcreteSpecW`, `OrdChainUpdateCoreSpecW`, `OrdCycleRouteSelectSpecW`,
`OrdCycleRouteEvalSpecW`, `ShiftTermChainSyncSpecW`, and `ShiftDeepChainSyncSpecW`). -/
structure SolverInnerCode where
  procs : SolverInnerEnv → List Stmt
  initConcreteOff : ℕ
  ordChainCoreOff : ℕ
  selectRouteOff : ℕ
  evalCycleOff : ℕ
  shiftTermChainOff : ℕ
  shiftDeepChainOff : ℕ

/-- Every procedure emitted by `inner` is deterministic (`Stmt.NoRand`), for every environment. -/
def SolverInnerCode.IsDeterministic (inner : SolverInnerCode) : Prop :=
  ∀ env, ∀ s ∈ inner.procs env, s.NoRand

/-- Combine six separate relocatable inner modules with fixed lengths into one `SolverInnerCode`,
placing them consecutively from `env.innerBase`. -/
def SolverInnerCode.ofSix
    (mInit mCore mSelect mEval mTerm mDeep : SolverInnerEnv → List Stmt)
    (lenInit lenCore lenSelect lenEval lenTerm : ℕ)
    (offInit offCore offSelect offEval offTerm offDeep : ℕ) : SolverInnerCode where
  procs env :=
    let b0 := env.innerBase
    let b1 := b0 + lenInit
    let b2 := b1 + lenCore
    let b3 := b2 + lenSelect
    let b4 := b3 + lenEval
    let b5 := b4 + lenTerm
    mInit { env with innerBase := b0 } ++
    mCore { env with innerBase := b1 } ++
    mSelect { env with innerBase := b2 } ++
    mEval { env with innerBase := b3 } ++
    mTerm { env with innerBase := b4 } ++
    mDeep { env with innerBase := b5 }
  initConcreteOff := offInit
  ordChainCoreOff := lenInit + offCore
  selectRouteOff := lenInit + lenCore + offSelect
  evalCycleOff := lenInit + lenCore + lenSelect + offEval
  shiftTermChainOff := lenInit + lenCore + lenSelect + lenEval + offTerm
  shiftDeepChainOff := lenInit + lenCore + lenSelect + lenEval + lenTerm + offDeep

/-- A trivial deterministic `SparseCoreCode` witnessing that the code-data structure and its
determinism condition are inhabitable. -/
def SparseCoreCode.trivial : SparseCoreCode where
  prog := ⟨[.ret (.const 0)]⟩
  init := 0
  op _ := 0

/-- A trivial deterministic `SolverInnerCode` witnessing that the code-data structure and its
determinism condition are inhabitable. -/
def SolverInnerCode.trivial : SolverInnerCode where
  procs _ := [.ret (.const 0)]
  initConcreteOff := 0
  ordChainCoreOff := 0
  selectRouteOff := 0
  evalCycleOff := 0
  shiftTermChainOff := 0
  shiftDeepChainOff := 0

theorem SparseCoreCode.trivial_isDeterministic : SparseCoreCode.trivial.prog.IsDeterministic := by
  intro s hs
  simp only [SparseCoreCode.trivial, List.mem_singleton] at hs
  subst hs
  simp [Stmt.NoRand]

theorem SolverInnerCode.trivial_isDeterministic : SolverInnerCode.trivial.IsDeterministic := by
  intro _ s hs
  simp only [SolverInnerCode.trivial, List.mem_singleton] at hs
  subst hs
  simp [Stmt.NoRand]

/-! ## Layout and assembly of the solver tail -/

/-- Absolute entry indices for every component placed inside `solverTail` starting at base `b`. -/
structure SolverTailLayout where
  cycleInit : ℕ
  overwrite : ℕ
  clog : ℕ
  chainRefresh : ℕ
  ordEdits : ℕ
  shiftQuotaWriter : ℕ
  findCycle : ℕ
  shiftLevel : ℕ
  bitLength : ℕ
  integerQuality : ℕ
  quality : ℕ
  level0Rename : ℕ
  lastBase : ℕ
  lastInit : ℕ
  lastOp : ℕ → ℕ
  scBase : ℕ
  scInit : ℕ
  scOp : ℕ → ℕ
  innerBase : ℕ
  initConcrete : ℕ
  ordChainCore : ℕ
  selectRoute : ℕ
  evalCycle : ℕ
  shiftTermChain : ℕ
  shiftDeepChain : ℕ

/-- Constant-offset layout of `solverTail` starting at `b`. The four solver entries (`cycleInit`,
`chainRefresh`, `findCycle`, `shiftLevel`) are fixed offsets `b + 0`, `b + 3`, `b + 6`, `b + 7`
independent of all subsequent block lengths. -/
def solverTailLayout (lastGuest : Program) (lastD lastC : ℕ)
    (sc : SparseCoreCode) (inner : SolverInnerCode) (b : ℕ) : SolverTailLayout :=
  let lastBase := b + 12
  let lastLen := (packedLastLevelProgram lastGuest lastD lastC).procs.length
  let scBase := lastBase + lastLen
  let innerBase := scBase + sc.prog.procs.length
  { cycleInit := b
    overwrite := b + 1
    clog := b + 2
    chainRefresh := b + 3
    ordEdits := b + 4
    shiftQuotaWriter := b + 5
    findCycle := b + 6
    shiftLevel := b + 7
    bitLength := b + 8
    integerQuality := b + 9
    quality := b + 10
    level0Rename := b + 11
    lastBase := lastBase
    lastInit := lastBase + 15
    lastOp := fun _ => lastBase + 16
    scBase := scBase
    scInit := scBase + sc.init
    scOp := fun i => scBase + sc.op i
    innerBase := innerBase
    initConcrete := innerBase + inner.initConcreteOff
    ordChainCore := innerBase + inner.ordChainCoreOff
    selectRoute := innerBase + inner.selectRouteOff
    evalCycle := innerBase + inner.evalCycleOff
    shiftTermChain := innerBase + inner.shiftTermChainOff
    shiftDeepChain := innerBase + inner.shiftDeepChainOff }

/-- External environment passed to `inner.procs` when `solverTail` is placed at `b`. -/
def solverTailInnerEnv (opsBase : ℕ) (lastGuest : Program) (lastD lastC : ℕ)
    (sc : SparseCoreCode) (b : ℕ) : SolverInnerEnv :=
  let lastBase := b + 12
  let scBase := lastBase + (packedLastLevelProgram lastGuest lastD lastC).procs.length
  { innerBase := scBase + sc.prog.procs.length
    opsBase := opsBase
    quality := b + 10
    clog := b + 2
    level0Rename := b + 11
    scInit := scBase + sc.init
    scOp := fun i => scBase + sc.op i
    lastInit := lastBase + 15
    lastOp := fun _ => lastBase + 16 }

/-- The 12 concrete wired entries and library helper procedures at the start of `solverTail`. -/
def solverTailWiredBlock (opsBase threshold A : ℕ) (lastGuest : Program) (lastD lastC : ℕ)
    (sc : SparseCoreCode) (inner : SolverInnerCode) (b : ℕ) : List Stmt :=
  let lay := solverTailLayout lastGuest lastD lastC sc inner b
  [ solverInitWiredBody lay.initConcrete lay.overwrite opsBase,
    initOverwriteIntThresholdsBody lay.clog threshold,
    Scaling.Machine.clogTwoBody lay.clog,
    ordChainRefreshWiredBody lay.ordEdits lay.ordChainCore lay.shiftQuotaWriter,
    level0BatchToOrdEditsBody,
    shiftQuotaWriterBody threshold,
    ordFindCycleWiredBody lay.selectRoute lay.evalCycle,
    shiftLevelWiredBody lay.shiftTermChain lay.shiftDeepChain,
    Num.IPM.bitLengthBody lay.bitLength,
    integerQualityBody lay.bitLength A,
    cappedQualityBody (lay.bitLength + 1) A threshold,
    level0RenameBody ]

/-- Complete relocatable code tail of the min-ratio solver starting at base `b`:
the 12 wired/helper procedures, the real packed last-level bodies, the shifted sparse-core
program, and the inner-level bodies. -/
def solverTail (opsBase threshold A : ℕ) (lastGuest : Program) (lastD lastC : ℕ)
    (sc : SparseCoreCode) (inner : SolverInnerCode) (b : ℕ) : List Stmt :=
  let lay := solverTailLayout lastGuest lastD lastC sc inner b
  let env := solverTailInnerEnv opsBase lastGuest lastD lastC sc b
  solverTailWiredBlock opsBase threshold A lastGuest lastD lastC sc inner b ++
    packedLastLevelBodies lastGuest lastD lastC lay.lastBase ++
    shiftProgramProcs lay.scBase sc.prog ++
    inner.procs env

end MinCostFlow.Final

end

public section

namespace MinCostFlow.Final

open WordRAM MinRatio SparseCore SparseCore.Program DynSpanner.Program LastLevelProgram Chain
  IPM.Machine Scaling.Machine

theorem solverTailWiredBlock_length (opsBase threshold A : ℕ) (lastGuest : Program) (lastD lastC : ℕ)
    (sc : SparseCoreCode) (inner : SolverInnerCode) (b : ℕ) :
    (solverTailWiredBlock opsBase threshold A lastGuest lastD lastC sc inner b).length = 12 := rfl

theorem SolverInnerCode.ofSix_isDeterministic
    {mInit mCore mSelect mEval mTerm mDeep : SolverInnerEnv → List Stmt}
    {lenInit lenCore lenSelect lenEval lenTerm offInit offCore offSelect offEval offTerm offDeep : ℕ}
    (hInit : ∀ env, ∀ s ∈ mInit env, s.NoRand)
    (hCore : ∀ env, ∀ s ∈ mCore env, s.NoRand)
    (hSelect : ∀ env, ∀ s ∈ mSelect env, s.NoRand)
    (hEval : ∀ env, ∀ s ∈ mEval env, s.NoRand)
    (hTerm : ∀ env, ∀ s ∈ mTerm env, s.NoRand)
    (hDeep : ∀ env, ∀ s ∈ mDeep env, s.NoRand) :
    (SolverInnerCode.ofSix mInit mCore mSelect mEval mTerm mDeep
      lenInit lenCore lenSelect lenEval lenTerm
      offInit offCore offSelect offEval offTerm offDeep).IsDeterministic := by
  intro env s hs
  unfold SolverInnerCode.ofSix at hs
  simp only [List.mem_append] at hs
  rcases hs with ((((h | h) | h) | h) | h) | h
  · exact hInit _ s h
  · exact hCore _ s h
  · exact hSelect _ s h
  · exact hEval _ s h
  · exact hTerm _ s h
  · exact hDeep _ s h

/-- Every procedure in the 12-procedure concrete wired block is deterministic (`Stmt.NoRand`). -/
theorem solverTailWiredBlock_noRand (opsBase threshold A : ℕ) (lastGuest : Program) (lastD lastC : ℕ)
    (sc : SparseCoreCode) (inner : SolverInnerCode) (b : ℕ) :
    ∀ s ∈ solverTailWiredBlock opsBase threshold A lastGuest lastD lastC sc inner b, s.NoRand := by
  intro s hs
  unfold solverTailWiredBlock at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact solverInitWiredBody_noRand _ _ _
  · exact initOverwriteIntThresholdsBody_noRand _ _
  · exact Scaling.Machine.clogTwoBody_noRand _
  · exact ordChainRefreshWiredBody_noRand _ _ _
  · exact level0BatchToOrdEditsBody_noRand
  · exact shiftQuotaWriterBody_noRand _
  · exact ordFindCycleWiredBody_noRand _ _
  · exact shiftLevelWiredBody_noRand _ _
  · exact Num.IPM.bitLengthModule_noRand _ _ List.mem_cons_self
  · exact integerQualityBody_noRand _ _
  · exact cappedQualityBody_noRand _ _ _
  · exact level0RenameBody_noRand

/-- **Determinism of `solverTail`:** the whole tail is `NoRand` whenever the sparse-core program
and the inner-level bodies are deterministic. The 12 wired/helper procedures and the real
last-level bodies (`packedLastLevelBodies_noRand`) are unconditionally `NoRand`. -/
theorem solverTail_noRand (opsBase threshold A : ℕ) (lastGuest : Program) (lastD lastC : ℕ)
    {sc : SparseCoreCode} {inner : SolverInnerCode} (b : ℕ)
    (hsc : sc.prog.IsDeterministic) (hinner : inner.IsDeterministic) :
    ∀ s ∈ solverTail opsBase threshold A lastGuest lastD lastC sc inner b, s.NoRand := by
  intro s hs
  unfold solverTail at hs
  simp only [List.mem_append] at hs
  rcases hs with ((h | h) | h) | h
  · exact solverTailWiredBlock_noRand opsBase threshold A lastGuest lastD lastC sc inner b s h
  · exact packedLastLevelBodies_noRand lastGuest lastD lastC _ s h
  · exact shiftProgramProcs_noRand hsc s h
  · exact hinner _ s h

/-! ## `HasAt` extraction for every component of `solverTail` -/

private theorem hasAt_peel_tail {p : Program} {b b' : ℕ} {xs ys : List Stmt}
    (h : p.HasAt b (xs ++ ys)) (hlen : b + xs.length = b') :
    p.HasAt b xs ∧ p.HasAt b' ys :=
  ⟨Num.hasAt_append_left h, hlen ▸ Num.hasAt_append_right h⟩

/-- Splits `p.HasAt b (solverTail ...)` into the four blocks at their layout bases without
unfolding `packedLastLevelBodies`, `sc.prog`, or `inner.procs`. -/
theorem solverTail_hasAt_blocks {p : Program} {opsBase threshold A : ℕ}
    {lastGuest : Program} {lastD lastC : ℕ}
    {sc : SparseCoreCode} {inner : SolverInnerCode} {b : ℕ}
    (hp : p.HasAt b (solverTail opsBase threshold A lastGuest lastD lastC sc inner b)) :
    let lay := solverTailLayout lastGuest lastD lastC sc inner b
    let env := solverTailInnerEnv opsBase lastGuest lastD lastC sc b
    p.HasAt b (solverTailWiredBlock opsBase threshold A lastGuest lastD lastC sc inner b) ∧
    p.HasAt lay.lastBase (packedLastLevelBodies lastGuest lastD lastC lay.lastBase) ∧
    p.HasAt lay.scBase (shiftProgramProcs lay.scBase sc.prog) ∧
    p.HasAt lay.innerBase (inner.procs env) := by
  let lay := solverTailLayout lastGuest lastD lastC sc inner b
  let env := solverTailInnerEnv opsBase lastGuest lastD lastC sc b
  have hp' : p.HasAt b
      (solverTailWiredBlock opsBase threshold A lastGuest lastD lastC sc inner b ++
        (packedLastLevelBodies lastGuest lastD lastC lay.lastBase ++
          (shiftProgramProcs lay.scBase sc.prog ++ inner.procs env))) := by
    simpa only [solverTail, List.append_assoc] using hp
  obtain ⟨hWired, r1⟩ := hasAt_peel_tail (b' := lay.lastBase) hp' (by
    rw [solverTailWiredBlock_length]; rfl)
  obtain ⟨hLast, r2⟩ := hasAt_peel_tail (b' := lay.scBase) r1 (by
    rw [packedLastLevelBodies_length]; rfl)
  obtain ⟨hSC, hInner⟩ := hasAt_peel_tail (b' := lay.innerBase) r2 (by
    simp only [shiftProgramProcs, List.length_map]; rfl)
  exact ⟨hWired, hLast, hSC, hInner⟩

/-- Entry `b + 0` (`cycleInit`): `solverInitWiredBody`. -/
theorem solverTail_initWired_at {p : Program} {opsBase threshold A : ℕ}
    {lastGuest : Program} {lastD lastC : ℕ}
    {sc : SparseCoreCode} {inner : SolverInnerCode} {b : ℕ}
    (hp : p.HasAt b (solverTail opsBase threshold A lastGuest lastD lastC sc inner b)) :
    let lay := solverTailLayout lastGuest lastD lastC sc inner b
    p.procs[lay.cycleInit]? = some (solverInitWiredBody lay.initConcrete lay.overwrite opsBase) :=
  (solverTail_hasAt_blocks hp).1.head

/-- Entry `b + 1` (`overwrite`): `initOverwriteIntThresholdsBody`. -/
theorem solverTail_overwrite_at {p : Program} {opsBase threshold A : ℕ}
    {lastGuest : Program} {lastD lastC : ℕ}
    {sc : SparseCoreCode} {inner : SolverInnerCode} {b : ℕ}
    (hp : p.HasAt b (solverTail opsBase threshold A lastGuest lastD lastC sc inner b)) :
    let lay := solverTailLayout lastGuest lastD lastC sc inner b
    p.procs[lay.overwrite]? = some (initOverwriteIntThresholdsBody lay.clog threshold) :=
  (solverTail_hasAt_blocks hp).1.get (i := 1) (by simp [solverTailWiredBlock])

/-- Entry `b + 2` (`clog`): `Scaling.Machine.clogTwoModule`. -/
theorem solverTail_clog_hasAt {p : Program} {opsBase threshold A : ℕ}
    {lastGuest : Program} {lastD lastC : ℕ}
    {sc : SparseCoreCode} {inner : SolverInnerCode} {b : ℕ}
    (hp : p.HasAt b (solverTail opsBase threshold A lastGuest lastD lastC sc inner b)) :
    let lay := solverTailLayout lastGuest lastD lastC sc inner b
    p.HasAt lay.clog (Scaling.Machine.clogTwoModule lay.clog) := by
  intro lay i hi
  have hi0 : i = 0 := by simp [Scaling.Machine.clogTwoModule] at hi; omega
  subst hi0
  simpa [Scaling.Machine.clogTwoModule, lay, solverTailLayout, solverTailWiredBlock] using
    (solverTail_hasAt_blocks hp).1.get (i := 2) (by simp [solverTailWiredBlock])

/-- Contract for `clog` (`Scaling.Machine.clogTwoContract`) at `lay.clog`. -/
theorem solverTail_clog_meetsContract {w : ℕ} {p : Program} {opsBase threshold A : ℕ}
    {lastGuest : Program} {lastD lastC : ℕ}
    {sc : SparseCoreCode} {inner : SolverInnerCode} {b : ℕ}
    (hp : p.HasAt b (solverTail opsBase threshold A lastGuest lastD lastC sc inner b)) (n : ℕ) :
    let lay := solverTailLayout lastGuest lastD lastC sc inner b
    MeetsContract w p lay.clog (Scaling.Machine.clogTwoContract w n) :=
  Scaling.Machine.clogTwo_meetsContract (solverTail_clog_hasAt hp) n

/-- Entry `b + 3` (`chainRefresh`): `ordChainRefreshWiredBody`. -/
theorem solverTail_chainRefresh_at {p : Program} {opsBase threshold A : ℕ}
    {lastGuest : Program} {lastD lastC : ℕ}
    {sc : SparseCoreCode} {inner : SolverInnerCode} {b : ℕ}
    (hp : p.HasAt b (solverTail opsBase threshold A lastGuest lastD lastC sc inner b)) :
    let lay := solverTailLayout lastGuest lastD lastC sc inner b
    p.procs[lay.chainRefresh]? =
      some (ordChainRefreshWiredBody lay.ordEdits lay.ordChainCore lay.shiftQuotaWriter) :=
  (solverTail_hasAt_blocks hp).1.get (i := 3) (by simp [solverTailWiredBlock])

/-- Entry `b + 4` (`ordEdits`): `level0BatchToOrdEditsBody`. -/
theorem solverTail_ordEdits_at {p : Program} {opsBase threshold A : ℕ}
    {lastGuest : Program} {lastD lastC : ℕ}
    {sc : SparseCoreCode} {inner : SolverInnerCode} {b : ℕ}
    (hp : p.HasAt b (solverTail opsBase threshold A lastGuest lastD lastC sc inner b)) :
    let lay := solverTailLayout lastGuest lastD lastC sc inner b
    p.procs[lay.ordEdits]? = some level0BatchToOrdEditsBody :=
  (solverTail_hasAt_blocks hp).1.get (i := 4) (by simp [solverTailWiredBlock])

/-- Entry `b + 5` (`shiftQuotaWriter`): `shiftQuotaWriterBody threshold`. -/
theorem solverTail_shiftQuotaWriter_at {p : Program} {opsBase threshold A : ℕ}
    {lastGuest : Program} {lastD lastC : ℕ}
    {sc : SparseCoreCode} {inner : SolverInnerCode} {b : ℕ}
    (hp : p.HasAt b (solverTail opsBase threshold A lastGuest lastD lastC sc inner b)) :
    let lay := solverTailLayout lastGuest lastD lastC sc inner b
    p.procs[lay.shiftQuotaWriter]? = some (shiftQuotaWriterBody threshold) :=
  (solverTail_hasAt_blocks hp).1.get (i := 5) (by simp [solverTailWiredBlock])

/-- Discharges `ShiftQuotaWriterSpec` directly at `lay.shiftQuotaWriter`. -/
theorem solverTail_shiftQuotaWriter_spec {w L P m V psi k epsExp drainUnit : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {p : Program} {opsBase threshold A : ℕ} {lastGuest : Program} {lastD lastC : ℕ}
    {sc : SparseCoreCode} {inner : SolverInnerCode} {b : ℕ}
    (hp : p.HasAt b (solverTail opsBase threshold A lastGuest lastD lastC sc inner b))
    (hM0 : cfg.P.M₀ = max m threshold) (hpsi : psi = ⌈cfg.Ψ⌉₊) :
    let lay := solverTailLayout lastGuest lastD lastC sc inner b
    ShiftQuotaWriterSpec w L P m V psi k epsExp drainUnit cfg Rcore p
      lay.shiftQuotaWriter (shiftQuotaWriterBudget cfg.P.d cfg.P.M₀) :=
  shiftQuotaWriterSpec_proved (solverTail_shiftQuotaWriter_at hp) hM0 hpsi

/-- Entry `b + 6` (`findCycle`): `ordFindCycleWiredBody`. -/
theorem solverTail_findCycle_at {p : Program} {opsBase threshold A : ℕ}
    {lastGuest : Program} {lastD lastC : ℕ}
    {sc : SparseCoreCode} {inner : SolverInnerCode} {b : ℕ}
    (hp : p.HasAt b (solverTail opsBase threshold A lastGuest lastD lastC sc inner b)) :
    let lay := solverTailLayout lastGuest lastD lastC sc inner b
    p.procs[lay.findCycle]? = some (ordFindCycleWiredBody lay.selectRoute lay.evalCycle) :=
  (solverTail_hasAt_blocks hp).1.get (i := 6) (by simp [solverTailWiredBlock])

/-- Entry `b + 7` (`shiftLevel`): `shiftLevelWiredBody`. -/
theorem solverTail_shiftLevel_at {p : Program} {opsBase threshold A : ℕ}
    {lastGuest : Program} {lastD lastC : ℕ}
    {sc : SparseCoreCode} {inner : SolverInnerCode} {b : ℕ}
    (hp : p.HasAt b (solverTail opsBase threshold A lastGuest lastD lastC sc inner b)) :
    let lay := solverTailLayout lastGuest lastD lastC sc inner b
    p.procs[lay.shiftLevel]? = some (shiftLevelWiredBody lay.shiftTermChain lay.shiftDeepChain) :=
  (solverTail_hasAt_blocks hp).1.get (i := 7) (by simp [solverTailWiredBlock])

/-- Entries `b + 8 .. b + 10`: the capped-quality procedures. -/
theorem solverTail_quality_hasAt {p : Program} {opsBase threshold A : ℕ}
    {lastGuest : Program} {lastD lastC : ℕ}
    {sc : SparseCoreCode} {inner : SolverInnerCode} {b : ℕ}
    (hp : p.HasAt b (solverTail opsBase threshold A lastGuest lastD lastC sc inner b)) :
    let lay := solverTailLayout lastGuest lastD lastC sc inner b
    p.HasAt lay.bitLength
      [Num.IPM.bitLengthBody lay.bitLength, integerQualityBody lay.bitLength A,
        cappedQualityBody (lay.bitLength + 1) A threshold] := by
  intro lay i hi
  have hw := (solverTail_hasAt_blocks hp).1
  rcases i with _ | _ | _ | i
  · simpa [lay, solverTailLayout, solverTailWiredBlock] using
      hw.get (i := 8) (by simp [solverTailWiredBlock])
  · simpa [lay, solverTailLayout, solverTailWiredBlock, Nat.add_assoc] using
      hw.get (i := 9) (by simp [solverTailWiredBlock])
  · simpa [lay, solverTailLayout, solverTailWiredBlock, Nat.add_assoc] using
      hw.get (i := 10) (by simp [solverTailWiredBlock])
  · simp at hi; omega

/-- Contract for `quality` (`solverQualityContract` for `cappedQualityExponent threshold A`) at
`lay.quality`. -/
theorem solverTail_quality_meetsContract {w : ℕ} {p : Program} {opsBase threshold A : ℕ}
    {lastGuest : Program} {lastD lastC : ℕ}
    {sc : SparseCoreCode} {inner : SolverInnerCode} {b : ℕ}
    (hw : 2 < 2 ^ w)
    (hp : p.HasAt b (solverTail opsBase threshold A lastGuest lastD lastC sc inner b)) :
    let lay := solverTailLayout lastGuest lastD lastC sc inner b
    MeetsContract w p lay.quality
      (solverQualityContract w (cappedQualityExponent threshold A) cappedQualityCost) := by
  intro lay
  have hq := solverTail_quality_hasAt hp
  have hSplit : p.HasAt lay.bitLength
      ([Num.IPM.bitLengthBody lay.bitLength] ++
        [integerQualityBody lay.bitLength A,
          cappedQualityBody (lay.bitLength + 1) A threshold]) := hq
  have hBit := Num.IPM.bitLength_meetsContract hw (Num.hasAt_append_left hSplit)
  have hRest := Num.hasAt_append_right hSplit
  change p.HasAt (lay.bitLength + 1)
    ([integerQualityBody lay.bitLength A] ++
      [cappedQualityBody (lay.bitLength + 1) A threshold]) at hRest
  have hInt := integerQuality_meetsContract (Num.hasAt_append_left hRest).head hBit
  have hCapBody : p.procs[lay.quality]? =
      some (cappedQualityBody (lay.bitLength + 1) A threshold) := by
    have hh := (Num.hasAt_append_right hRest).head
    simpa [lay, solverTailLayout, Nat.add_assoc] using hh
  exact cappedQuality_meetsContract hCapBody hInt

/-- Entry `b + 11` (`level0Rename`): `level0RenameBody`. -/
theorem solverTail_level0Rename_at {p : Program} {opsBase threshold A : ℕ}
    {lastGuest : Program} {lastD lastC : ℕ}
    {sc : SparseCoreCode} {inner : SolverInnerCode} {b : ℕ}
    (hp : p.HasAt b (solverTail opsBase threshold A lastGuest lastD lastC sc inner b)) :
    let lay := solverTailLayout lastGuest lastD lastC sc inner b
    p.procs[lay.level0Rename]? = some level0RenameBody :=
  (solverTail_hasAt_blocks hp).1.get (i := 11) (by simp [solverTailWiredBlock])

/-- Block 2 (`lastBase = b + 12`): the real relocated last-level bodies `packedLastLevelBodies`. -/
theorem solverTail_lastLevel_hasAt {p : Program} {opsBase threshold A : ℕ}
    {lastGuest : Program} {lastD lastC : ℕ}
    {sc : SparseCoreCode} {inner : SolverInnerCode} {b : ℕ}
    (hp : p.HasAt b (solverTail opsBase threshold A lastGuest lastD lastC sc inner b)) :
    let lay := solverTailLayout lastGuest lastD lastC sc inner b
    p.HasAt lay.lastBase (packedLastLevelBodies lastGuest lastD lastC lay.lastBase) :=
  (solverTail_hasAt_blocks hp).2.1

/-- Transfers any `DSRep.Implements` theorem of the standalone `packedLastLevelProgram` into any
host program containing `solverTail` at `b`, at entries `lay.lastInit` and `lay.lastOp`. -/
theorem solverTail_lastLevel_implements {S : Type} {R : DSRep S} {w : ℕ} {D : DataStructure S}
    {p : Program} {opsBase threshold A : ℕ} {lastGuest : Program} {lastD lastC : ℕ}
    {sc : SparseCoreCode} {inner : SolverInnerCode} {b : ℕ}
    (hp : p.HasAt b (solverTail opsBase threshold A lastGuest lastD lastC sc inner b))
    (himpl : R.Implements w (packedLastLevelProgram lastGuest lastD lastC) 15 (fun _ => 16) D) :
    let lay := solverTailLayout lastGuest lastD lastC sc inner b
    R.Implements w p lay.lastInit lay.lastOp D :=
  dsRep_implements_shift (solverTail_lastLevel_hasAt hp) himpl

/-- Block 3 (`scBase`): the shifted sparse-core program `shiftProgramProcs lay.scBase sc.prog`. -/
theorem solverTail_sparseCore_hasAt {p : Program} {opsBase threshold A : ℕ}
    {lastGuest : Program} {lastD lastC : ℕ}
    {sc : SparseCoreCode} {inner : SolverInnerCode} {b : ℕ}
    (hp : p.HasAt b (solverTail opsBase threshold A lastGuest lastD lastC sc inner b)) :
    let lay := solverTailLayout lastGuest lastD lastC sc inner b
    p.HasAt lay.scBase (shiftProgramProcs lay.scBase sc.prog) :=
  (solverTail_hasAt_blocks hp).2.2.1

/-- Transfers any `DSRep.Implements` proof of the standalone sparse-core program `sc.prog` into
any host program containing `solverTail` at `b`, at entries `lay.scInit` and `lay.scOp`. -/
theorem solverTail_sparseCore_implements {S : Type} {R : DSRep S} {w : ℕ} {D : DataStructure S}
    {p : Program} {opsBase threshold A : ℕ} {lastGuest : Program} {lastD lastC : ℕ}
    {sc : SparseCoreCode} {inner : SolverInnerCode} {b : ℕ}
    (hp : p.HasAt b (solverTail opsBase threshold A lastGuest lastD lastC sc inner b))
    (himpl : R.Implements w sc.prog sc.init sc.op D) :
    let lay := solverTailLayout lastGuest lastD lastC sc inner b
    R.Implements w p lay.scInit lay.scOp D :=
  dsRep_implements_shift (solverTail_sparseCore_hasAt hp) himpl

/-- Transfers `SparseCoreOrdProgramUniform` (Lemma 5.17, page 23,
`SparseCore/Program/AssemblyStatement.lean`) along `shiftProgramProcs` to any host program
embedding `sc.prog` at `offset`. -/
theorem sparseCoreOrdProgramUniform_shift {C_lsst : ℝ} {lsfInit : ℕ → ℕ → LSFInit}
    {impl : SparsifyImpl} {Q p : Program} {offset init : ℕ} {op : ℕ → ℕ}
    (hp : p.HasAt offset (shiftProgramProcs offset Q))
    (hU : SparseCoreOrdProgramUniform C_lsst lsfInit impl Q init op) :
    SparseCoreOrdProgramUniform C_lsst lsfInit impl p (offset + init) (fun i => offset + op i) := by
  intro capExp
  obtain ⟨wordExp, hw⟩ := hU capExp
  refine ⟨wordExp, fun limbMul => ?_⟩
  obtain ⟨P, allocation, hwe, hP⟩ := hw limbMul
  refine ⟨P, allocation, hwe, fun depth w fmt L => ?_⟩
  obtain ⟨R, hloc, hR⟩ := hP depth w fmt L
  exact ⟨R, hloc, fun G k M N vCap eCap h4 hcap =>
    dsRep_implements_shift hp (hR G k M N vCap eCap h4 hcap)⟩

/-- Transfers `SparseCoreOrdProgramUniform` from `sc.prog` into any host program containing
`solverTail` at `b`, at entries `lay.scInit` and `lay.scOp`. -/
theorem solverTail_sparseCore_uniform {C_lsst : ℝ} {lsfInit : ℕ → ℕ → LSFInit}
    {impl : SparsifyImpl} {p : Program} {opsBase threshold A : ℕ}
    {lastGuest : Program} {lastD lastC : ℕ}
    {sc : SparseCoreCode} {inner : SolverInnerCode} {b : ℕ}
    (hp : p.HasAt b (solverTail opsBase threshold A lastGuest lastD lastC sc inner b))
    (hU : SparseCoreOrdProgramUniform C_lsst lsfInit impl sc.prog sc.init sc.op) :
    let lay := solverTailLayout lastGuest lastD lastC sc inner b
    SparseCoreOrdProgramUniform C_lsst lsfInit impl p lay.scInit lay.scOp :=
  sparseCoreOrdProgramUniform_shift (solverTail_sparseCore_hasAt hp) hU

/-- Block 4 (`innerBase`): the inner-level bodies `inner.procs env`. -/
theorem solverTail_inner_hasAt {p : Program} {opsBase threshold A : ℕ}
    {lastGuest : Program} {lastD lastC : ℕ}
    {sc : SparseCoreCode} {inner : SolverInnerCode} {b : ℕ}
    (hp : p.HasAt b (solverTail opsBase threshold A lastGuest lastD lastC sc inner b)) :
    let lay := solverTailLayout lastGuest lastD lastC sc inner b
    let env := solverTailInnerEnv opsBase lastGuest lastD lastC sc b
    p.HasAt lay.innerBase (inner.procs env) :=
  (solverTail_hasAt_blocks hp).2.2.2

/-- Lookup of any entry at offset `off` inside `inner.procs env` from `solverTail_inner_hasAt`. -/
theorem solverTail_inner_entry_at {p : Program} {opsBase threshold A : ℕ}
    {lastGuest : Program} {lastD lastC : ℕ}
    {sc : SparseCoreCode} {inner : SolverInnerCode} {b off : ℕ}
    (hp : p.HasAt b (solverTail opsBase threshold A lastGuest lastD lastC sc inner b))
    (hoff : off < (inner.procs (solverTailInnerEnv opsBase lastGuest lastD lastC sc b)).length) :
    let lay := solverTailLayout lastGuest lastD lastC sc inner b
    let env := solverTailInnerEnv opsBase lastGuest lastD lastC sc b
    p.procs[lay.innerBase + off]? = some ((inner.procs env)[off]'hoff) :=
  (solverTail_inner_hasAt hp) off hoff

/-- When `inner` is built by `SolverInnerCode.ofSix`, each of the six sub-modules sits at its own
base in any host program embedding `inner.procs env`. -/
theorem solverInnerCode_ofSix_hasAt {p : Program} {env : SolverInnerEnv}
    {mInit mCore mSelect mEval mTerm mDeep : SolverInnerEnv → List Stmt}
    {lenInit lenCore lenSelect lenEval lenTerm offInit offCore offSelect offEval offTerm offDeep : ℕ}
    (hLenInit : (mInit { env with innerBase := env.innerBase }).length = lenInit)
    (hLenCore : (mCore { env with innerBase := env.innerBase + lenInit }).length = lenCore)
    (hLenSelect :
      (mSelect { env with innerBase := env.innerBase + lenInit + lenCore }).length = lenSelect)
    (hLenEval :
      (mEval { env with innerBase := env.innerBase + lenInit + lenCore + lenSelect }).length =
        lenEval)
    (hLenTerm :
      (mTerm { env with
          innerBase := env.innerBase + lenInit + lenCore + lenSelect + lenEval }).length =
        lenTerm)
    (hp : p.HasAt env.innerBase
      ((SolverInnerCode.ofSix mInit mCore mSelect mEval mTerm mDeep
          lenInit lenCore lenSelect lenEval lenTerm
          offInit offCore offSelect offEval offTerm offDeep).procs env)) :
    let b0 := env.innerBase
    let b1 := b0 + lenInit
    let b2 := b1 + lenCore
    let b3 := b2 + lenSelect
    let b4 := b3 + lenEval
    let b5 := b4 + lenTerm
    p.HasAt b0 (mInit { env with innerBase := b0 }) ∧
    p.HasAt b1 (mCore { env with innerBase := b1 }) ∧
    p.HasAt b2 (mSelect { env with innerBase := b2 }) ∧
    p.HasAt b3 (mEval { env with innerBase := b3 }) ∧
    p.HasAt b4 (mTerm { env with innerBase := b4 }) ∧
    p.HasAt b5 (mDeep { env with innerBase := b5 }) := by
  let b0 := env.innerBase
  let b1 := b0 + lenInit
  let b2 := b1 + lenCore
  let b3 := b2 + lenSelect
  let b4 := b3 + lenEval
  let b5 := b4 + lenTerm
  have hp' : p.HasAt b0
      (mInit { env with innerBase := b0 } ++
        (mCore { env with innerBase := b1 } ++
          (mSelect { env with innerBase := b2 } ++
            (mEval { env with innerBase := b3 } ++
              (mTerm { env with innerBase := b4 } ++
                mDeep { env with innerBase := b5 }))))) := by
    simpa only [SolverInnerCode.ofSix, List.append_assoc] using hp
  obtain ⟨h0, r1⟩ := hasAt_peel_tail (b' := b1) hp' (by rw [hLenInit])
  obtain ⟨h1, r2⟩ := hasAt_peel_tail (b' := b2) r1 (by rw [hLenCore])
  obtain ⟨h2, r3⟩ := hasAt_peel_tail (b' := b3) r2 (by rw [hLenSelect])
  obtain ⟨h3, r4⟩ := hasAt_peel_tail (b' := b4) r3 (by rw [hLenEval])
  obtain ⟨h4, h5⟩ := hasAt_peel_tail (b' := b5) r4 (by rw [hLenTerm])
  exact ⟨h0, h1, h2, h3, h4, h5⟩

/-! ## Step-spec bridges from `solverTail` -/

/-- Discharges the corrected `FindCycleStepSpecW` at `lay.findCycle` from the two corrected inner
specs `OrdCycleRouteSelectSpecW` and `OrdCycleRouteEvalSpecW` at `lay.selectRoute` and
`lay.evalCycle`. -/
theorem solverTail_findCycleStepSpecW
    {w L P m V psi k epsExp drainUnit selectSpace selectBudget evalSpace evalBudget
      maxEdges maxPaths capExp limbMul capLimit opsBase threshold A : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program}
    {lastGuest : Program} {lastD lastC : ℕ} {sc : SparseCoreCode} {inner : SolverInnerCode} {b : ℕ}
    (hlocal : Rcore.Local)
    (hp : p.HasAt b (solverTail opsBase threshold A lastGuest lastD lastC sc inner b))
    (hSel : let lay := solverTailLayout lastGuest lastD lastC sc inner b
      OrdCycleRouteSelectSpecW w L P m V psi k epsExp drainUnit capExp limbMul capLimit cfg Rcore p
        lay.selectRoute selectSpace selectBudget maxEdges maxPaths)
    (hEval : let lay := solverTailLayout lastGuest lastD lastC sc inner b
      OrdCycleRouteEvalSpecW w L P m V psi k epsExp drainUnit cfg Rcore p
        lay.evalCycle evalSpace evalBudget maxEdges maxPaths)
    (hw6 : 6 < 2 ^ w) :
    let lay := solverTailLayout lastGuest lastD lastC sc inner b
    FindCycleStepSpecW w L P m V psi k epsExp drainUnit capExp limbMul capLimit cfg Rcore p
      lay.findCycle (6 + selectSpace + evalSpace) (selectBudget + evalBudget + 90)
      maxEdges maxPaths :=
  findCycleStepSpecW_wired hlocal (solverTail_findCycle_at hp) hSel hEval hw6

/-- Discharges `FindCycleStepSpec` at `lay.findCycle` from `OrdCycleRouteSelectSpec` and
`OrdCycleRouteEvalSpec` at `lay.selectRoute` and `lay.evalCycle`. -/
theorem solverTail_findCycleStepSpec
    {w L P m V psi k epsExp drainUnit selectSpace selectBudget evalSpace evalBudget
      maxEdges maxPaths opsBase threshold A : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program}
    {lastGuest : Program} {lastD lastC : ℕ} {sc : SparseCoreCode} {inner : SolverInnerCode} {b : ℕ}
    (hlocal : Rcore.Local)
    (hp : p.HasAt b (solverTail opsBase threshold A lastGuest lastD lastC sc inner b))
    (hSel : let lay := solverTailLayout lastGuest lastD lastC sc inner b
      OrdCycleRouteSelectSpec w L P m V psi k epsExp drainUnit cfg Rcore p
        lay.selectRoute selectSpace selectBudget maxEdges maxPaths)
    (hEval : let lay := solverTailLayout lastGuest lastD lastC sc inner b
      OrdCycleRouteEvalSpec w L P m V psi k epsExp drainUnit cfg Rcore p
        lay.evalCycle evalSpace evalBudget maxEdges maxPaths)
    (hw6 : 6 < 2 ^ w) :
    let lay := solverTailLayout lastGuest lastD lastC sc inner b
    FindCycleStepSpec w L P m V psi k epsExp drainUnit cfg Rcore p
      lay.findCycle (6 + selectSpace + evalSpace) (selectBudget + evalBudget + 90)
      maxEdges maxPaths :=
  findCycleStepSpec_wired hlocal (solverTail_findCycle_at hp) hSel hEval hw6

/-- Discharges `ChainRefreshStepSpec` at `lay.chainRefresh` from `OrdChainUpdateCoreSpec` at
`lay.ordChainCore`, automatically plugging in `level0BatchToOrdEditsBody` (`lay.ordEdits`) and
`shiftQuotaWriterSpec_proved` (`lay.shiftQuotaWriter`). -/
theorem solverTail_chainRefreshStepSpec
    {w L P m V psi k epsExp drainUnit opsBase threshold A : ℕ}
    {coreSpace coreBudget : ℕ → ℕ} {B_bound R_bound : ℤ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program}
    {lastGuest : Program} {lastD lastC : ℕ} {sc : SparseCoreCode} {inner : SolverInnerCode} {b : ℕ}
    (hlocal : Rcore.Local)
    (hp : p.HasAt b (solverTail opsBase threshold A lastGuest lastD lastC sc inner b))
    (hCore : let lay := solverTailLayout lastGuest lastD lastC sc inner b
      OrdChainUpdateCoreSpec w L P m V psi k epsExp drainUnit cfg Rcore p
        lay.ordChainCore coreSpace coreBudget B_bound R_bound)
    (hM0 : cfg.P.M₀ = max m threshold) (hpsi : psi = ⌈cfg.Ψ⌉₊)
    (hw11 : 11 < 2 ^ w) (hdW : cfg.P.d + 1 < 2 ^ w) :
    let lay := solverTailLayout lastGuest lastD lastC sc inner b
    ChainRefreshStepSpec w L P m V psi k epsExp drainUnit cfg Rcore p lay.chainRefresh
      (fun uLen => cfg.P.d + (8 * uLen + 1) + coreSpace uLen)
      (fun uLen => coreBudget uLen + shiftQuotaWriterBudget cfg.P.d cfg.P.M₀ +
        120 * uLen + 62 * (cfg.P.d + 1) + 240)
      B_bound R_bound :=
  chainRefreshStepSpec_wired hlocal (solverTail_chainRefresh_at hp) (solverTail_ordEdits_at hp)
    hCore (solverTail_shiftQuotaWriter_spec hp hM0 hpsi) hw11 hdW

/-- Discharges `ShiftLevelStepSpec` at `lay.shiftLevel` from `ShiftTermChainSyncSpec` and
`ShiftDeepChainSyncSpec` at `lay.shiftTermChain` and `lay.shiftDeepChain`. -/
theorem solverTail_shiftLevelStepSpec
    {w L P m V psi k epsExp drainUnit termSpace termBudget deepSpace deepBudget
      opsBase threshold A : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program}
    {lastGuest : Program} {lastD lastC : ℕ} {sc : SparseCoreCode} {inner : SolverInnerCode} {b : ℕ}
    (hp : p.HasAt b (solverTail opsBase threshold A lastGuest lastD lastC sc inner b))
    (hTerm : let lay := solverTailLayout lastGuest lastD lastC sc inner b
      ShiftTermChainSyncSpec w L P m V psi k epsExp drainUnit cfg Rcore p
        lay.shiftTermChain termSpace termBudget)
    (hDeep : let lay := solverTailLayout lastGuest lastD lastC sc inner b
      ShiftDeepChainSyncSpec w L P m V psi k epsExp drainUnit cfg Rcore p
        lay.shiftDeepChain deepSpace deepBudget)
    (hw17 : 17 < 2 ^ w) (hdW : cfg.P.d + 1 < 2 ^ w) (hkW : cfg.P.k < 2 ^ w) :
    let lay := solverTailLayout lastGuest lastD lastC sc inner b
    ShiftLevelStepSpec w L P m V psi k epsExp drainUnit cfg Rcore p lay.shiftLevel
      (max termSpace deepSpace) (max termBudget deepBudget + 28 * (cfg.P.d + 1) + 220) :=
  shiftLevelStepSpec_wired (solverTail_shiftLevel_at hp) hTerm hDeep hw17 hdW hkW

end MinCostFlow.Final

end
