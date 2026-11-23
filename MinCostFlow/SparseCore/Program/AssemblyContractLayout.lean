module

public import MinCostFlow.SparseCore.Program.AssemblyContractBlocks
public import MinCostFlow.SparseCore.Program.AssemblyTopIface
public import MinCostFlow.SparseCore.Program.ReadRep
public import MinCostFlow.MinRatio.ProgramShift

/-!
# Readout layout postconditions for the sparse-core contract (`AssemblyContractLayout`)

`OrdCoreReadoutLayout` (`MinRatio/WireInitReadoutK.lean`) quantifies universally over every memory
`mem'` and every `cur ≤ ret`, which is unsatisfiable: a memory `mem'` that no readout produced can
break each of its layout facts.
The layout facts that Init needs hold instead as postconditions of the readout operations (`op 2`,
`op 3`, `op 5`) on the memory `mem'` that the operation actually leaves.

This file defines:
* `sparseCoreOrdMachineContractKFBL` and `sparseCoreOrdMachineContractKFRBL`: the smallest change
  to `KFB`/`KFRB` adding the readout-layout postconditions of `readLSFLayout` (`op 2`),
  `readGraphLayout` (`op 3`), and `readOrdLayout` (`op 5`) directly to `D.post`.
* `SparseCoreReadoutFootAt`: the companion per-run guarantees for the two clauses that mention
  `R.foot` or the returned heap pointer `o.value` (which `WordRAM.DataStructure.post` cannot name):
  every cell of the returned forest (`op 2`) or sparsifier (`op 3`) `DynGraphAt` lies in
  `R.foot b x' ∨ (cur ≤ addr ∧ addr < o.value)`, and the written `OrdListAt` (`op 5`) ends at or
  before `o.value` (`st'.mem cur + words ≤ o.value`). Includes relocation (`sparseCoreReadoutFootAt_shift`).
* `AsmBranchReadoutLayout`: companion readout-layout specification for a branch module `BR : AsmBranchAt`
  (leaving `AssemblyTopIface.lean` untouched).
* `readRep_readLSF_layout` and `readRep_readS_layout`: proves directly from P10's `ReadLayout` and
  `ReadRecAt` (`ReadRep.lean`, `ReadRecord.lean`) that P10's readouts satisfy every `op 2` and
  `op 3` layout and footprint fact.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio MinCostFlow.LSF
open MinCostFlow.SparseCore.Program.Read

/-! ## Contract extensions with readout layout postconditions -/

/-- `sparseCoreOrdMachineContractKFB` with readout-layout postconditions added to ops `2`, `3`, `4`, `5`:
* `op 2` (`readLSF`): `fBase + dynGraphSize vcF ecF ≤ cur`, `stDesc + 2 ≤ cur`, and for every
  `e ∈ a.G.E`, `mem' stDesc + e * Lw + Lw ≤ cur` and `mem' (stDesc + 1) + e * Lw + Lw ≤ cur`;
* `op 3` (`readS`): `vcH = vCap ∧ ecH = eCap` (yielding `vcH + ecH + 2 ≤ vCap + eCap + 2 ≤ capLimit`)
  and `mem' cur + dynGraphSize vcH ecH ≤ cur`;
* `op 4` (`readEmb`): `EmbeddingReadoutAt`, `MEmbBounded ... 0 cur` (the pointer table and every walk
  lie below `cur`), `mem' (cur + 1) ≤ eCap`, and every word of every walk fits below `2 ^ w`;
* `op 5` (`readOrd`): `mem' cur = cur + 1` and `∀ j < words, mem' (mem' cur + j) < 2 ^ w`. -/
noncomputable def sparseCoreOrdMachineContractKFBL {w : ℕ} (fmt : Num.Format w) (L depth : ℕ)
    (tool : SparseCoreRestartTool) (initialGraph : MGraph) (k M N vCap eCap capExp : ℕ)
    (P : SparseCoreOrdParams) (allocation : ℕ → List ℕ → ℕ) :
    DataStructure (SparseCoreOrdAbs tool) :=
  let D := sparseCoreOrdMachineContractKFB fmt L tool initialGraph k M N vCap eCap capExp P
    allocation
  { D with
    initPre := fun args mem => ∃ graph lengths gradient ord heap,
      args = [graph, lengths, gradient, ord, k, M, N, L, fmt.precision, depth, heap] ∧
      D.initPre [graph, lengths, gradient, ord, k, M, N, L, fmt.precision, heap] mem
    post := fun i a args mem a' mem' => match i with
      | 2 =>
        let cur := heapArg args
        let b := args.getD 1 0
        let fBase := mem' (cur + 1)
        let stDesc := mem' (cur + 3)
        let Lw := mem' (cur + 4)
        a' = a ∧ ∃ forestVCap forestECap,
          Lw ≤ L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1) ∧
          LSFAt mem' cur forestVCap forestECap fmt.limbBits Lw fmt.precision a.G.E
            (tool.lsfs a.st b) ∧
          fBase + dynGraphSize forestVCap forestECap ≤ cur ∧
          stDesc + 2 ≤ cur ∧
          (∀ e ∈ a.G.E, mem' stDesc + e * Lw + Lw ≤ cur) ∧
          (∀ e ∈ a.G.E, mem' (stDesc + 1) + e * Lw + Lw ≤ cur)
      | 3 =>
        let cur := heapArg args
        let b := args.getD 1 0
        a' = a ∧ ∃ graphVCap graphECap,
          DynGraphAt mem' (mem' cur) graphVCap graphECap (tool.S a.st b) ∧
          graphVCap = vCap ∧ graphECap = eCap ∧
          mem' cur + dynGraphSize graphVCap graphECap ≤ cur
      | 4 =>
        let cur := heapArg args
        let b := args.getD 1 0
        let embTable := mem' cur
        let embCap := mem' (cur + 1)
        let coreE := (coreGraph a.G (tool.lsfs a.st b)).E
        a' = a ∧
        EmbeddingReadoutAt mem' cur embCap a.G (tool.lsfs a.st b) (tool.emb a.st b) ∧
        MEmbBounded mem' embTable coreE embCap (tool.emb a.st b) 0 cur ∧
        embCap ≤ eCap ∧
        (∀ e ∈ coreE, ∀ t < (mWalkEncode (tool.emb a.st b e)).length,
          mem' (mem' (embTable + e) + t) < 2 ^ w)
      | 5 =>
        let cur := heapArg args
        let b := args.getD 1 0
        a' = a ∧ ∃ words,
          OrdListAt mem' (mem' cur) (tool.rot a.st b) words ∧
          words ≤ ordRotWords a b ∧
          mem' cur = cur + 1 ∧
          (∀ j < words, mem' (mem' cur + j) < 2 ^ w)
      | i => D.post i a args mem a' mem' }

/-- `sparseCoreOrdMachineContractKFRB` (with `reembList` on `op 0`) with the run-time `depth`
argument in `initPre` and the same readout-layout postconditions on ops `2`, `3`, `4`, `5`. -/
noncomputable def sparseCoreOrdMachineContractKFRBL {w : ℕ} (fmt : Num.Format w) (L depth : ℕ)
    (tool : SparseCoreRestartTool) (reemb : ToolReembFn tool)
    (initialGraph : MGraph) (k M N vCap eCap capExp : ℕ)
    (P : SparseCoreOrdParams) (allocation : ℕ → List ℕ → ℕ) :
    DataStructure (SparseCoreOrdAbs tool) :=
  let D := sparseCoreOrdMachineContractKFRB fmt L tool reemb initialGraph k M N vCap eCap capExp P
    allocation
  { D with
    initPre := fun args mem => ∃ graph lengths gradient ord heap,
      args = [graph, lengths, gradient, ord, k, M, N, L, fmt.precision, depth, heap] ∧
      D.initPre [graph, lengths, gradient, ord, k, M, N, L, fmt.precision, heap] mem
    post := fun i a args mem a' mem' => match i with
      | 2 => (sparseCoreOrdMachineContractKFBL fmt L depth tool initialGraph k M N vCap eCap capExp P
          allocation).post 2 a args mem a' mem'
      | 3 => (sparseCoreOrdMachineContractKFBL fmt L depth tool initialGraph k M N vCap eCap capExp P
          allocation).post 3 a args mem a' mem'
      | 4 => (sparseCoreOrdMachineContractKFBL fmt L depth tool initialGraph k M N vCap eCap capExp P
          allocation).post 4 a args mem a' mem'
      | 5 => (sparseCoreOrdMachineContractKFBL fmt L depth tool initialGraph k M N vCap eCap capExp P
          allocation).post 5 a args mem a' mem'
      | i => D.post i a args mem a' mem' }

/-- Any implementation of `KFRBL` automatically implements `KFBL`. -/
theorem dsRep_implements_kfbl_of_kfrbl {w : ℕ} {fmt : Num.Format w} {L depth : ℕ}
    {tool : SparseCoreRestartTool} {reemb : ToolReembFn tool}
    {initialGraph : MGraph} {k M N vCap eCap capExp : ℕ}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {p : Program} {init : ℕ} {op : ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)}
    (h : R.Implements w p init op
      (sparseCoreOrdMachineContractKFRBL fmt L depth tool reemb initialGraph k M N vCap eCap capExp P
        allocation)) :
    R.Implements w p init op
      (sparseCoreOrdMachineContractKFBL fmt L depth tool initialGraph k M N vCap eCap capExp P
        allocation) := by
  refine ⟨h.1, h.2.1, fun i b s x args mem pos ω hargs hhead hrep hpre hfoot hz hsp => ?_⟩
  obtain ⟨body, hbody, o, st', c, hrun, s', x', hrep', hpost, hresp, hcost⟩ :=
    h.2.2 i b s x args mem pos ω hargs hhead hrep hpre hfoot hz hsp
  refine ⟨body, hbody, o, st', c, hrun, s', x', hrep', ?_, hresp, hcost⟩
  match i with
  | 0 => exact ⟨hpost.1.1, hpost.2⟩
  | 1 => exact hpost
  | 2 => exact hpost
  | 3 => exact hpost
  | 4 => exact hpost
  | 5 => exact hpost
  | i + 6 => exact hpost

/-! ## Companion footprint / returned-heap-pointer readout postconditions -/

/-- Per-run footprint and returned-heap-pointer readout guarantees for `op 2`, `op 3`, and `op 5`
that `WordRAM.DataStructure.post` cannot state directly because `DataStructure.post` does not take
`R.foot` or the returned heap pointer `o.value`. Together with `sparseCoreOrdMachineContractKFBL`,
this supplies every fact used by `WireInitReadoutK.lean` and `WireInitLinkLoopK.lean` in place of
the unsatisfiable `OrdCoreReadoutLayout`. -/
structure SparseCoreReadoutFootAt {w : ℕ} (fmt : Num.Format w) (L depth : ℕ)
    (tool : SparseCoreRestartTool) (initialGraph : MGraph) (k M N vCap eCap capExp : ℕ)
    (P : SparseCoreOrdParams) (allocation : ℕ → List ℕ → ℕ)
    (R : DSRep (SparseCoreOrdAbs tool)) (p : Program) (op : ℕ → ℕ) : Prop where
  op2_runs :
    let D := sparseCoreOrdMachineContractKFBL fmt L depth tool initialGraph k M N vCap eCap capExp P allocation
    ∀ (b : ℕ) (a : SparseCoreOrdAbs tool) (x : R.τ) (args : List ℕ) (mem : ℕ → ℕ)
      (pos : ℕ) (ω : ℕ → Bool),
      (∀ v ∈ args, v < 2 ^ w) → args.head? = some b →
      R.rep b a x mem → D.pre 2 a args mem → (∀ addr, R.foot b x addr → addr < heapArg args) →
      ZeroFrom mem (heapArg args) → heapArg args + D.space 2 a args mem < 2 ^ w →
      ∃ body, p.procs[op 2]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState args mem pos) o st' c ∧
        R.rep b a x' st'.mem ∧
        (let cur := heapArg args
         let br := args.getD 1 0
         let fBase := st'.mem (cur + 1)
         let stDesc := st'.mem (cur + 3)
         let Lw := st'.mem (cur + 4)
         ∃ forestVCap forestECap,
           Lw ≤ L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1) ∧
           LSFAt st'.mem cur forestVCap forestECap fmt.limbBits Lw fmt.precision a.G.E
             (tool.lsfs a.st br) ∧
           fBase + dynGraphSize forestVCap forestECap ≤ cur ∧
           (∀ addr, fBase ≤ addr → addr < fBase + dynGraphSize forestVCap forestECap →
             R.foot b x' addr ∨ (cur ≤ addr ∧ addr < o.value)) ∧
           stDesc + 2 ≤ cur ∧
           (∀ e ∈ a.G.E, st'.mem stDesc + e * Lw + Lw ≤ cur ∧
             ∀ t < Lw, R.foot b x' (st'.mem stDesc + e * Lw + t) ∨
               (cur ≤ st'.mem stDesc + e * Lw + t ∧ st'.mem stDesc + e * Lw + t < o.value)) ∧
           (∀ e ∈ a.G.E, st'.mem (stDesc + 1) + e * Lw + Lw ≤ cur ∧
             ∀ t < Lw, R.foot b x' (st'.mem (stDesc + 1) + e * Lw + t) ∨
               (cur ≤ st'.mem (stDesc + 1) + e * Lw + t ∧ st'.mem (stDesc + 1) + e * Lw + t < o.value)) ∧
           dynGraphSize forestVCap forestECap ≤ dynGraphSize vCap (2 * (vCap + eCap + 2) ^ 2)) ∧
        R.Respects (R.foot b x) (heapArg args) (D.space 2 a args mem) mem o.value b x' st'.mem ∧
        c + R.phi b x' st'.mem ≤ D.cost 2 a args mem + R.phi b x mem
  op3_runs :
    let D := sparseCoreOrdMachineContractKFBL fmt L depth tool initialGraph k M N vCap eCap capExp P allocation
    ∀ (b : ℕ) (a : SparseCoreOrdAbs tool) (x : R.τ) (args : List ℕ) (mem : ℕ → ℕ)
      (pos : ℕ) (ω : ℕ → Bool),
      (∀ v ∈ args, v < 2 ^ w) → args.head? = some b →
      R.rep b a x mem → D.pre 3 a args mem → (∀ addr, R.foot b x addr → addr < heapArg args) →
      ZeroFrom mem (heapArg args) → heapArg args + D.space 3 a args mem < 2 ^ w →
      ∃ body, p.procs[op 3]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState args mem pos) o st' c ∧
        R.rep b a x' st'.mem ∧
        (let cur := heapArg args
         let br := args.getD 1 0
         ∃ graphVCap graphECap,
           DynGraphAt st'.mem (st'.mem cur) graphVCap graphECap (tool.S a.st br) ∧
           graphVCap = vCap ∧ graphECap = eCap ∧
           st'.mem cur + dynGraphSize graphVCap graphECap ≤ cur ∧
           (∀ addr, st'.mem cur ≤ addr → addr < st'.mem cur + dynGraphSize graphVCap graphECap →
             R.foot b x' addr ∨ (cur ≤ addr ∧ addr < o.value))) ∧
        R.Respects (R.foot b x) (heapArg args) (D.space 3 a args mem) mem o.value b x' st'.mem ∧
        c + R.phi b x' st'.mem ≤ D.cost 3 a args mem + R.phi b x mem
  op4_runs :
    let D := sparseCoreOrdMachineContractKFBL fmt L depth tool initialGraph k M N vCap eCap capExp P allocation
    ∀ (b : ℕ) (a : SparseCoreOrdAbs tool) (x : R.τ) (args : List ℕ) (mem : ℕ → ℕ)
      (pos : ℕ) (ω : ℕ → Bool),
      (∀ v ∈ args, v < 2 ^ w) → args.head? = some b →
      R.rep b a x mem → D.pre 4 a args mem → (∀ addr, R.foot b x addr → addr < heapArg args) →
      ZeroFrom mem (heapArg args) → heapArg args + D.space 4 a args mem < 2 ^ w →
      ∃ body, p.procs[op 4]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState args mem pos) o st' c ∧
        R.rep b a x' st'.mem ∧
        (let cur := heapArg args
         let br := args.getD 1 0
         let embTable := st'.mem cur
         let embCap := st'.mem (cur + 1)
         let coreE := (coreGraph a.G (tool.lsfs a.st br)).E
         EmbeddingReadoutAt st'.mem cur embCap a.G (tool.lsfs a.st br) (tool.emb a.st br) ∧
         MEmbBounded st'.mem embTable coreE embCap (tool.emb a.st br) 0 cur ∧
         embCap ≤ eCap ∧
         (∀ e ∈ coreE, ∀ t < (mWalkEncode (tool.emb a.st br e)).length,
           st'.mem (st'.mem (embTable + e) + t) < 2 ^ w) ∧
         (∀ addr, embTable ≤ addr → addr < embTable + embCap →
           R.foot b x' addr ∨ (cur ≤ addr ∧ addr < o.value)) ∧
         (∀ e ∈ coreE, ∀ addr,
           st'.mem (embTable + e) ≤ addr →
           addr < st'.mem (embTable + e) + (mWalkEncode (tool.emb a.st br e)).length →
           R.foot b x' addr ∨ (cur ≤ addr ∧ addr < o.value))) ∧
        R.Respects (R.foot b x) (heapArg args) (D.space 4 a args mem) mem o.value b x' st'.mem ∧
        c + R.phi b x' st'.mem ≤ D.cost 4 a args mem + R.phi b x mem
  op5_runs :
    let D := sparseCoreOrdMachineContractKFBL fmt L depth tool initialGraph k M N vCap eCap capExp P allocation
    ∀ (b : ℕ) (a : SparseCoreOrdAbs tool) (x : R.τ) (args : List ℕ) (mem : ℕ → ℕ)
      (pos : ℕ) (ω : ℕ → Bool),
      (∀ v ∈ args, v < 2 ^ w) → args.head? = some b →
      R.rep b a x mem → D.pre 5 a args mem → (∀ addr, R.foot b x addr → addr < heapArg args) →
      ZeroFrom mem (heapArg args) → heapArg args + D.space 5 a args mem < 2 ^ w →
      ∃ body, p.procs[op 5]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState args mem pos) o st' c ∧
        R.rep b a x' st'.mem ∧
        (let cur := heapArg args
         let br := args.getD 1 0
         ∃ words,
           OrdListAt st'.mem (st'.mem cur) (tool.rot a.st br) words ∧
           words ≤ ordRotWords a br ∧
           st'.mem cur = cur + 1 ∧
           st'.mem cur + words ≤ o.value ∧
           (∀ j < words, st'.mem (st'.mem cur + j) < 2 ^ w)) ∧
        R.Respects (R.foot b x) (heapArg args) (D.space 5 a args mem) mem o.value b x' st'.mem ∧
        c + R.phi b x' st'.mem ≤ D.cost 5 a args mem + R.phi b x mem

/-- Relocation of `SparseCoreReadoutFootAt` across `shiftProgramProcs`. -/
theorem sparseCoreReadoutFootAt_shift {w L depth k M N vCap eCap capExp offset : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph : MGraph}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {Q p : Program} {op : ℕ → ℕ}
    (hp : p.HasAt offset (shiftProgramProcs offset Q))
    (h : SparseCoreReadoutFootAt fmt L depth tool initialGraph k M N vCap eCap capExp P allocation R Q op) :
    SparseCoreReadoutFootAt fmt L depth tool initialGraph k M N vCap eCap capExp P allocation R p
      (fun i => offset + op i) := by
  have hproc : ∀ i body, Q.procs[op i]? = some body →
      p.procs[offset + op i]? = some (shiftProcIds offset body) := fun i body hbody => by
    have hlen : op i < Q.procs.length := by
      by_contra hge
      simp [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hbody
    have hbe : Q.procs[op i] = body := by
      rw [List.getElem?_eq_getElem hlen] at hbody
      exact Option.some.inj hbody
    simpa [shiftProgramProcs, hbe] using hp (op i) (by simp [shiftProgramProcs, hlen])
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only
    intro b a x args mem pos ω hargs hhead hrep hpre hfoot hz hsp
    obtain ⟨body, hbody, o, st', c, x', hrun, hrep', hout, hresp, hcost⟩ :=
      h.op2_runs b a x args mem pos ω hargs hhead hrep hpre hfoot hz hsp
    exact ⟨shiftProcIds offset body, hproc 2 body hbody, o, st', c, x',
      runs_shiftProcIds hp hrun, hrep', hout, hresp, hcost⟩
  · dsimp only
    intro b a x args mem pos ω hargs hhead hrep hpre hfoot hz hsp
    obtain ⟨body, hbody, o, st', c, x', hrun, hrep', hout, hresp, hcost⟩ :=
      h.op3_runs b a x args mem pos ω hargs hhead hrep hpre hfoot hz hsp
    exact ⟨shiftProcIds offset body, hproc 3 body hbody, o, st', c, x',
      runs_shiftProcIds hp hrun, hrep', hout, hresp, hcost⟩
  · dsimp only
    intro b a x args mem pos ω hargs hhead hrep hpre hfoot hz hsp
    obtain ⟨body, hbody, o, st', c, x', hrun, hrep', hout, hresp, hcost⟩ :=
      h.op4_runs b a x args mem pos ω hargs hhead hrep hpre hfoot hz hsp
    exact ⟨shiftProcIds offset body, hproc 4 body hbody, o, st', c, x',
      runs_shiftProcIds hp hrun, hrep', hout, hresp, hcost⟩
  · dsimp only
    intro b a x args mem pos ω hargs hhead hrep hpre hfoot hz hsp
    obtain ⟨body, hbody, o, st', c, x', hrun, hrep', hout, hresp, hcost⟩ :=
      h.op5_runs b a x args mem pos ω hargs hhead hrep hpre hfoot hz hsp
    exact ⟨shiftProcIds offset body, hproc 5 body hbody, o, st', c, x',
      runs_shiftProcIds hp hrun, hrep', hout, hresp, hcost⟩

/-! ## Uniform capacity-indexed statements with readout layout -/

/-- Capacity-indexed uniform statement for `sparseCoreOrdMachineContractKFRBL` + `SparseCoreReadoutFootAt`. -/
def SparseCoreOrdProgramUniformReembCapLayout (C_lsst : ℝ) (lsfInitAuto : ℕ → LSFInit)
    (impl : SparsifyImpl)
    (brReemb : ∀ depth, BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ)
    (p : Program) (init : ℕ) (op : ℕ → ℕ) : Prop :=
  ∀ capExp : ℕ, ∃ wordExp : ℕ, ∀ limbMul : ℕ,
    ∃ (P : SparseCoreOrdParams) (allocation : ℕ → ℕ → List ℕ → ℕ),
      P.wordExp = wordExp ∧
      ∀ (depth w : ℕ) (fmt : Num.Format w),
        1 ≤ depth →
        ∃ (τ : Type) (phi : ℕ → τ → (ℕ → ℕ) → ℕ) (foot : ℕ → τ → ℕ → Prop),
          ∀ (L vCap eCap : ℕ),
            ∃ rep : ℕ → SparseCoreOrdAbs (sparseCoreProgTool (lsfInitAuto fmt.precision) C_lsst depth impl) →
                τ → (ℕ → ℕ) → Prop,
              let R : DSRep (SparseCoreOrdAbs (sparseCoreProgTool (lsfInitAuto fmt.precision) C_lsst depth impl)) :=
                ⟨τ, rep, phi, foot⟩
              R.Local ∧ ∀ (G : MGraph) (k M N sizeParam : ℕ),
                fmt.limbBits = 4 → fmt.precision ≤ 4 * L → SparseCoreCapHyp capExp limbMul L M N vCap eCap →
                depth ≤ M + N + k + L → depth ≤ bundleLogFactor M N →
                depth ≤ Expander.chosenL ((M + N) ^ 2) →
                M + N + k + vCap + eCap + L + depth ≤ sizeParam →
                (∀ j < k, IsValidLSFInitFor (lsfInitAuto fmt.precision) C_lsst k j) →
                G.n ≤ G.m + 1 →
                CompInitFormatHyp L fmt.precision k G.m → k ≤ (M + N + 2) ^ capExp →
                R.Implements w p init op
                  (sparseCoreOrdMachineContractKFRBL fmt L depth
                    (sparseCoreProgTool (lsfInitAuto fmt.precision) C_lsst depth impl)
                    (bundleToolReemb (brReemb depth))
                    G k M N vCap eCap capExp P (allocation sizeParam)) ∧
                SparseCoreReadoutFootAt fmt L depth
                  (sparseCoreProgTool (lsfInitAuto fmt.precision) C_lsst depth impl)
                  G k M N vCap eCap capExp P (allocation sizeParam) R p op

/-- Capacity-indexed uniform statement for `sparseCoreOrdMachineContractKFBL` + `SparseCoreReadoutFootAt`. -/
def SparseCoreOrdProgramUniformCapLayout (C_lsst : ℝ) (lsfInitAuto : ℕ → LSFInit)
    (impl : SparsifyImpl) (p : Program) (init : ℕ) (op : ℕ → ℕ) : Prop :=
  ∀ capExp : ℕ, ∃ wordExp : ℕ, ∀ limbMul : ℕ,
    ∃ (P : SparseCoreOrdParams) (allocation : ℕ → ℕ → List ℕ → ℕ),
      P.wordExp = wordExp ∧
      ∀ (depth w : ℕ) (fmt : Num.Format w),
        1 ≤ depth →
        ∃ (τ : Type) (phi : ℕ → τ → (ℕ → ℕ) → ℕ) (foot : ℕ → τ → ℕ → Prop),
          ∀ (L vCap eCap : ℕ),
            ∃ rep : ℕ → SparseCoreOrdAbs (sparseCoreProgTool (lsfInitAuto fmt.precision) C_lsst depth impl) →
                τ → (ℕ → ℕ) → Prop,
              let R : DSRep (SparseCoreOrdAbs (sparseCoreProgTool (lsfInitAuto fmt.precision) C_lsst depth impl)) :=
                ⟨τ, rep, phi, foot⟩
              R.Local ∧ ∀ (G : MGraph) (k M N sizeParam : ℕ),
                fmt.limbBits = 4 → fmt.precision ≤ 4 * L → SparseCoreCapHyp capExp limbMul L M N vCap eCap →
                depth ≤ M + N + k + L → depth ≤ bundleLogFactor M N →
                depth ≤ Expander.chosenL ((M + N) ^ 2) →
                M + N + k + vCap + eCap + L + depth ≤ sizeParam →
                (∀ j < k, IsValidLSFInitFor (lsfInitAuto fmt.precision) C_lsst k j) →
                G.n ≤ G.m + 1 →
                CompInitFormatHyp L fmt.precision k G.m → k ≤ (M + N + 2) ^ capExp →
                R.Implements w p init op
                  (sparseCoreOrdMachineContractKFBL fmt L depth
                    (sparseCoreProgTool (lsfInitAuto fmt.precision) C_lsst depth impl)
                    G k M N vCap eCap capExp P (allocation sizeParam)) ∧
                SparseCoreReadoutFootAt fmt L depth
                  (sparseCoreProgTool (lsfInitAuto fmt.precision) C_lsst depth impl)
                  G k M N vCap eCap capExp P (allocation sizeParam) R p op

theorem sparseCoreOrdProgramUniformCapLayout_of_reemb {C_lsst : ℝ} {lsfInitAuto : ℕ → LSFInit}
    {impl : SparsifyImpl}
    {brReemb : ∀ depth, BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ}
    {p : Program} {init : ℕ} {op : ℕ → ℕ}
    (h : SparseCoreOrdProgramUniformReembCapLayout C_lsst lsfInitAuto impl brReemb p init op) :
    SparseCoreOrdProgramUniformCapLayout C_lsst lsfInitAuto impl p init op := fun capExp => by
  obtain ⟨wordExp, hw⟩ := h capExp
  refine ⟨wordExp, fun limbMul => ?_⟩
  obtain ⟨P, allocation, hwe, hP⟩ := hw limbMul
  refine ⟨P, allocation, hwe, fun depth w fmt hdepth => ?_⟩
  obtain ⟨τ, phi, foot, hτ⟩ := hP depth w fmt hdepth
  refine ⟨τ, phi, foot, fun L vCap eCap => ?_⟩
  obtain ⟨rep, hloc, hR⟩ := hτ L vCap eCap
  exact ⟨rep, hloc, fun G k M N sizeParam hfmt hPL hcap hdle hdlg hdch hsize hInit hGn hCFmt hkCap =>
    let ⟨h1, h2⟩ := hR G k M N sizeParam hfmt hPL hcap hdle hdlg hdch hsize hInit hGn hCFmt hkCap
    ⟨dsRep_implements_kfbl_of_kfrbl h1, h2⟩⟩

/-! ## Companion readout-layout interface for a branch module -/

/-- Companion readout-layout specification for a branch module `BR : AsmBranchAt` (defined here
so `AssemblyTopIface.lean` stays untouched). Strengthens `BR.readLSF_runs`, `BR.readS_runs`, and
`BR.readOrd_runs` with the exact P10 (`ReadLayout`) and order-listing layout/footprint facts. -/
structure AsmBranchReadoutLayout {S : AsmBranchSpec} {CFS : AsmCompFamilySpec}
    {lsfInit : LSFInit} {C_lsst : ℝ} {depth w : ℕ} {fmt : Num.Format w} {L capExp limbMul : ℕ}
    {impl : SparsifyImpl}
    {brReemb : BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ}
    {p : Program} {fCFInit fCFBatch : ℕ}
    {CF : AsmCompFamilyAt CFS lsfInit w fmt L capExp limbMul p fCFInit fCFBatch}
    {bp : AsmBranchProcs}
    (BR : AsmBranchAt S CFS lsfInit C_lsst depth w fmt L capExp limbMul impl brReemb p
      fCFInit fCFBatch CF bp) : Prop where
  readLSF_layout_runs : ∀ (brH h M N vCap eCap : ℕ) (tr : BundleTreeState depth) (ord : ℕ → List End)
      (x : BR.rep.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      fmt.limbBits = 4 → tr.m₀ = M → tr.n₀ = N →
      SparseCoreCapHyp capExp limbMul L M N vCap eCap →
      BR.rep.rep brH ⟨tr, ord, vCap, eCap⟩ x mem →
      (∀ a, BR.rep.foot brH x a → a < h) →
      brH < 2 ^ w → h < 2 ^ w → ZeroFrom mem h → h + 5 < 2 ^ w →
      ∃ body, p.procs[bp.fReadLSF]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState [brH, h] mem pos) o st' c ∧
        BR.rep.rep brH ⟨tr, ord, vCap, eCap⟩ x' st'.mem ∧
        (let fBase := st'.mem (h + 1)
         let stDesc := st'.mem (h + 3)
         let Lw := st'.mem (h + 4)
         ∃ forestVCap forestECap,
           Lw ≤ L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1) ∧
           LSFAt st'.mem h forestVCap forestECap fmt.limbBits Lw fmt.precision tr.cs.G.E tr.cs.lsf ∧
           fBase + dynGraphSize forestVCap forestECap ≤ h ∧
           (∀ addr, fBase ≤ addr → addr < fBase + dynGraphSize forestVCap forestECap →
             BR.rep.foot brH x' addr ∨ (h ≤ addr ∧ addr < o.value)) ∧
           stDesc + 2 ≤ h ∧
           (∀ e ∈ tr.cs.G.E, st'.mem stDesc + e * Lw + Lw ≤ h ∧
             ∀ t < Lw, BR.rep.foot brH x' (st'.mem stDesc + e * Lw + t) ∨
               (h ≤ st'.mem stDesc + e * Lw + t ∧ st'.mem stDesc + e * Lw + t < o.value)) ∧
           (∀ e ∈ tr.cs.G.E, st'.mem (stDesc + 1) + e * Lw + Lw ≤ h ∧
             ∀ t < Lw, BR.rep.foot brH x' (st'.mem (stDesc + 1) + e * Lw + t) ∨
               (h ≤ st'.mem (stDesc + 1) + e * Lw + t ∧ st'.mem (stDesc + 1) + e * Lw + t < o.value)) ∧
           dynGraphSize forestVCap forestECap ≤ dynGraphSize vCap (2 * (vCap + eCap + 2) ^ 2)) ∧
        BR.rep.Respects (BR.rep.foot brH x) h 5 mem o.value brH x' st'.mem ∧
        c + BR.rep.phi brH x' st'.mem ≤ S.readout capExp + BR.rep.phi brH x mem
  readS_layout_runs : ∀ (brH h vCap eCap : ℕ) (tr : BundleTreeState depth) (ord : ℕ → List End)
      (x : BR.rep.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      BR.rep.rep brH ⟨tr, ord, vCap, eCap⟩ x mem →
      (∀ a, BR.rep.foot brH x a → a < h) →
      brH < 2 ^ w → h < 2 ^ w → ZeroFrom mem h → h + 1 < 2 ^ w →
      ∃ body, p.procs[bp.fReadS]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState [brH, h] mem pos) o st' c ∧
        BR.rep.rep brH ⟨tr, ord, vCap, eCap⟩ x' st'.mem ∧
        (∃ graphVCap graphECap,
          DynGraphAt st'.mem (st'.mem h) graphVCap graphECap tr.S_cur ∧
          graphVCap = vCap ∧ graphECap = eCap ∧
          st'.mem h + dynGraphSize graphVCap graphECap ≤ h ∧
          (∀ addr, st'.mem h ≤ addr → addr < st'.mem h + dynGraphSize graphVCap graphECap →
            BR.rep.foot brH x' addr ∨ (h ≤ addr ∧ addr < o.value))) ∧
        BR.rep.Respects (BR.rep.foot brH x) h 1 mem o.value brH x' st'.mem ∧
        c + BR.rep.phi brH x' st'.mem ≤ S.readout capExp + BR.rep.phi brH x mem
  readEmb_layout_runs : ∀ (brH h vCap eCap : ℕ) (tr : BundleTreeState depth) (ord : ℕ → List End)
      (x : BR.rep.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      BR.rep.rep brH ⟨tr, ord, vCap, eCap⟩ x mem →
      (∀ a, BR.rep.foot brH x a → a < h) →
      brH < 2 ^ w → h < 2 ^ w → ZeroFrom mem h → h + 2 < 2 ^ w →
      ∃ body, p.procs[bp.fReadEmb]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState [brH, h] mem pos) o st' c ∧
        BR.rep.rep brH ⟨tr, ord, vCap, eCap⟩ x' st'.mem ∧
        (let embTable := st'.mem h
         let embCap := st'.mem (h + 1)
         let coreE := (coreGraph tr.cs.G tr.cs.lsf).E
         EmbeddingReadoutAt st'.mem h embCap tr.cs.G tr.cs.lsf tr.emb ∧
         MEmbBounded st'.mem embTable coreE embCap tr.emb 0 h ∧
         embCap ≤ eCap ∧
         (∀ addr, embTable ≤ addr → addr < embTable + embCap →
           BR.rep.foot brH x' addr ∨ (h ≤ addr ∧ addr < o.value)) ∧
         (∀ e ∈ coreE, ∀ addr,
           st'.mem (embTable + e) ≤ addr →
           addr < st'.mem (embTable + e) + (mWalkEncode (tr.emb e)).length →
           BR.rep.foot brH x' addr ∨ (h ≤ addr ∧ addr < o.value))) ∧
        BR.rep.Respects (BR.rep.foot brH x) h 2 mem o.value brH x' st'.mem ∧
        c + BR.rep.phi brH x' st'.mem ≤ S.readout capExp + BR.rep.phi brH x mem
  readOrd_layout_runs : ∀ (brH h M N vCap eCap : ℕ) (tr : BundleTreeState depth) (ord : ℕ → List End)
      (x : BR.rep.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      tr.m₀ = M → tr.n₀ = N →
      SparseCoreCapHyp capExp limbMul L M N vCap eCap →
      BR.rep.rep brH ⟨tr, ord, vCap, eCap⟩ x mem →
      (∀ a, BR.rep.foot brH x a → a < h) →
      brH < 2 ^ w → h < 2 ^ w → ZeroFrom mem h →
      h + (1 + ordWordsOn tr.S_cur.V (tr.outOrder ord)) < 2 ^ w →
      ∃ body, p.procs[bp.fReadOrd]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState [brH, h] mem pos) o st' c ∧
        BR.rep.rep brH ⟨tr, ord, vCap, eCap⟩ x' st'.mem ∧
        (∃ words, OrdListAt st'.mem (st'.mem h) (tr.outOrder ord) words ∧
          words ≤ ordWordsOn tr.S_cur.V (tr.outOrder ord) ∧
          st'.mem h = h + 1 ∧
          st'.mem h + words ≤ o.value ∧
          (∀ j < words, st'.mem (st'.mem h + j) < 2 ^ w)) ∧
        BR.rep.Respects (BR.rep.foot brH x) h (1 + ordWordsOn tr.S_cur.V (tr.outOrder ord))
          mem o.value brH x' st'.mem ∧
        c + BR.rep.phi brH x' st'.mem ≤
          S.mul capExp limbMul * (ordWordsOn tr.S_cur.V (tr.outOrder ord) + 1) * bundleLogFactor M N +
            BR.rep.phi brH x mem

/-! ## P10 readout-layout proofs from `ReadLayout` and `ReadRecAt` -/

/-- **P10 readout `2` (`readLSFStmt`) satisfies every layout and footprint bound.** Proved directly
from `ReadLayout`, `ReadRecAt`, and `readLSF_runs` (`ReadRep.lean`, `ReadRecord.lean`). -/
theorem readRep_readLSF_layout {w vCap eCap tCap L_w P mul f : ℕ} {p : Program}
    (hp : p.procs[f]? = some readLSFStmt) (hmul : 80 ≤ mul)
    (r h : ℕ) (v : ReadView) (y : ReadConc) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hrep : (readRep vCap eCap tCap L_w P).rep r v y mem)
    (hfoot : ∀ a, (readRep vCap eCap tCap L_w P).foot r y a → a < h)
    (hz : ZeroFrom mem h) (hroom : h + 5 < 2 ^ w) :
    ∃ body, p.procs[f]? = some body ∧ ∃ o st' c y',
      Runs w p ω body (startState [r, h] mem pos) o st' c ∧
      (readRep vCap eCap tCap L_w P).rep r v y' st'.mem ∧
      ReadLSFOut st'.mem h L_w P v ∧
      (let fBase := st'.mem (h + 1)
       let stDesc := st'.mem (h + 3)
       LSFAt st'.mem h vCap tCap 4 L_w P v.G.E v.lsf ∧
       fBase + dynGraphSize vCap tCap ≤ h ∧
       (∀ a, fBase ≤ a → a < fBase + dynGraphSize vCap tCap →
         (readRep vCap eCap tCap L_w P).foot r y' a) ∧
       stDesc + 2 ≤ h ∧
       (∀ e ∈ v.G.E, st'.mem stDesc + e * L_w + L_w ≤ h ∧
         ∀ t < L_w, (readRep vCap eCap tCap L_w P).foot r y' (st'.mem stDesc + e * L_w + t)) ∧
       (∀ e ∈ v.G.E, st'.mem (stDesc + 1) + e * L_w + L_w ≤ h ∧
         ∀ t < L_w, (readRep vCap eCap tCap L_w P).foot r y' (st'.mem (stDesc + 1) + e * L_w + t))) ∧
      (readRep vCap eCap tCap L_w P).Respects ((readRep vCap eCap tCap L_w P).foot r y) h 5 mem
        o.value r y' st'.mem ∧
      c + (readRep vCap eCap tCap L_w P).phi r y' st'.mem ≤
        mul + (readRep vCap eCap tCap L_w P).phi r y mem := by
  have hlay : ReadLayout r vCap eCap tCap L_w y := hrep.2.1
  have hrec : ReadRecAt mem r vCap eCap tCap L_w P v y.q := hrep.2.2.2.1
  have hdom : ∀ e ∈ v.G.E, e < eCap := hrec.gGraph.2.2.1
  have hrecFoot : ∀ a, ReadRecFoot r vCap eCap tCap L_w y.q a → a < h := fun a ha =>
    hfoot a (Or.inr (Or.inl ha))
  obtain ⟨o, st', c, hrun, ho, hout, hbelow, habove, hc⟩ :=
    readLSF_runs (w := w) p ω hrec hrecFoot hdom hroom
  have hrep' : (readRep vCap eCap tCap L_w P).rep r v y st'.mem := hrep.of_below hfoot hbelow
  have hrec' : ReadRecAt st'.mem r vCap eCap tCap L_w P v y.q := hrep'.2.2.2.1
  obtain ⟨h0, h1, h2, h3, h4, _, _, h7, h8, hT, hF, hR, hS, _, _, _⟩ := hrec'
  have hr8 : r + 8 < h := hrecFoot (r + 8) (Or.inl ⟨by omega, by simp [readRecWords]⟩)
  -- `readLSFStmt` copies `r + i` to `h + i` for `i < 5`.
  have hm_copy : st'.mem h = y.q.t ∧ st'.mem (h + 1) = y.q.f ∧ st'.mem (h + 2) = y.q.roots ∧
      st'.mem (h + 3) = r + 7 := by
    obtain ⟨o', st'', c', hrun', ⟨_, hm'⟩, _⟩ :=
      readLSFStmt_runs (w := w) p ω r h pos mem (by omega) hroom
    obtain ⟨_, hst_eq, _⟩ := Runs.det hrun hrun'
    subst hst_eq
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hm']; simp [Function.update_of_ne, hrec.1]
    · rw [hm']; simp [Function.update_of_ne, hrec.2.1]
    · rw [hm']; simp [Function.update_of_ne, hrec.2.2.1]
    · rw [hm']; simp [Function.update_of_ne, hrec.2.2.2.1]
  have hdgPos : 4 ≤ dynGraphSize vCap tCap := by unfold dynGraphSize; omega
  have hfEnd : y.q.f + dynGraphSize vCap tCap ≤ h := by
    have hlt := hrecFoot (y.q.f + dynGraphSize vCap tCap - 1)
      (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
    omega
  have hfrzEnd : y.frz + dynGraphSize vCap tCap ≤ h := by
    have hlt := hfoot (y.frz + dynGraphSize vCap tCap - 1)
      (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
    omega
  have hnumEnd : y.q.num + eCap * L_w ≤ h := by
    obtain ⟨_, _, _, _, _, _, h6, h7', h8'⟩ := hlay
    omega
  have hdenEnd : y.q.den + eCap * L_w ≤ h := by
    obtain ⟨_, _, _, _, _, _, _, h7', h8'⟩ := hlay
    omega
  refine ⟨readLSFStmt, hp, o, st', c, y, hrun, hrep', hout, ?_, ?_, ?_⟩
  · dsimp only
    rw [hm_copy.2.1, hm_copy.2.2.2]
    refine ⟨?_, hfEnd, fun a ha1 ha2 => Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨ha1, ha2⟩)))),
      by omega, fun e he => ?_, fun e he => ?_⟩
    · unfold LSFAt
      rw [hm_copy.1, hm_copy.2.1, hm_copy.2.2.1, hm_copy.2.2.2]
      exact ⟨hT, hF, hR, hS⟩
    · have heLt : e < eCap := hdom e he
      have hmulLe : e * L_w + L_w ≤ eCap * L_w := by
        rw [← Nat.add_one_mul]; exact Nat.mul_le_mul_right L_w (Nat.succ_le_of_lt heLt)
      rw [h7]
      exact ⟨by omega, fun t ht =>
        Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))))))⟩
    · have heLt : e < eCap := hdom e he
      have hmulLe : e * L_w + L_w ≤ eCap * L_w := by
        rw [← Nat.add_one_mul]; exact Nat.mul_le_mul_right L_w (Nat.succ_le_of_lt heLt)
      rw [show r + 7 + 1 = r + 8 by omega, h8]
      exact ⟨by omega, fun t ht =>
        Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))))))⟩
  · refine ⟨by omega, by omega, fun a ha => by rw [habove a (by omega)]; exact hz a (by omega),
      fun a ha _ => hbelow a ha, fun _ ha => Or.inl ha⟩
  · simp only [readRep_phi]; omega

/-- **P10 readout `3` (`readSStmt`) satisfies every layout and footprint bound.** Proved directly
from `ReadLayout`, `ReadRecAt`, and `readS_runs` (`ReadRep.lean`, `ReadRecord.lean`). -/
theorem readRep_readS_layout {w vCap eCap tCap L_w P mul f : ℕ} {p : Program}
    (hp : p.procs[f]? = some readSStmt) (hmul : 20 ≤ mul)
    (r h : ℕ) (v : ReadView) (y : ReadConc) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hrep : (readRep vCap eCap tCap L_w P).rep r v y mem)
    (hfoot : ∀ a, (readRep vCap eCap tCap L_w P).foot r y a → a < h)
    (hz : ZeroFrom mem h) (hroom : h + 1 < 2 ^ w) :
    ∃ body, p.procs[f]? = some body ∧ ∃ o st' c y',
      Runs w p ω body (startState [r, h] mem pos) o st' c ∧
      (readRep vCap eCap tCap L_w P).rep r v y' st'.mem ∧
      DynGraphAt st'.mem (st'.mem h) vCap eCap v.S ∧
      st'.mem h + dynGraphSize vCap eCap ≤ h ∧
      (∀ a, st'.mem h ≤ a → a < st'.mem h + dynGraphSize vCap eCap →
        (readRep vCap eCap tCap L_w P).foot r y' a) ∧
      (readRep vCap eCap tCap L_w P).Respects ((readRep vCap eCap tCap L_w P).foot r y) h 1 mem
        o.value r y' st'.mem ∧
      c + (readRep vCap eCap tCap L_w P).phi r y' st'.mem ≤
        mul + (readRep vCap eCap tCap L_w P).phi r y mem := by
  have hrec : ReadRecAt mem r vCap eCap tCap L_w P v y.q := hrep.2.2.2.1
  have hdom : ∀ e ∈ v.G.E, e < eCap := hrec.gGraph.2.2.1
  have hrecFoot : ∀ a, ReadRecFoot r vCap eCap tCap L_w y.q a → a < h := fun a ha =>
    hfoot a (Or.inr (Or.inl ha))
  obtain ⟨o, st', c, hrun, ho, _, hbelow, habove, hc⟩ :=
    readS_runs (w := w) p ω hrec hrecFoot hdom hroom
  have hrep' : (readRep vCap eCap tCap L_w P).rep r v y st'.mem := hrep.of_below hfoot hbelow
  have hrec' : ReadRecAt st'.mem r vCap eCap tCap L_w P v y.q := hrep'.2.2.2.1
  have hr8 : r + 8 < h := hrecFoot (r + 8) (Or.inl ⟨by omega, by simp [readRecWords]⟩)
  have hm_h : st'.mem h = y.q.s := by
    obtain ⟨o', st'', c', hrun', ⟨_, hm'⟩, _⟩ :=
      readSStmt_runs (w := w) p ω r h pos mem (by omega) hroom
    obtain ⟨_, hst_eq, _⟩ := Runs.det hrun hrun'
    subst hst_eq
    rw [hm', Function.update_self, ← hbelow (r + 5) (by omega)]
    exact hrec'.2.2.2.2.2.1
  have hdgPos : 4 ≤ dynGraphSize vCap eCap := by unfold dynGraphSize; omega
  have hsEnd : y.q.s + dynGraphSize vCap eCap ≤ h := by
    have hlt := hrecFoot (y.q.s + dynGraphSize vCap eCap - 1)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))
    omega
  refine ⟨readSStmt, hp, o, st', c, y, hrun, hrep', ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm_h]; exact hrec'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [hm_h]; exact hsEnd
  · intro a ha1 ha2
    rw [hm_h] at ha1 ha2
    exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha1, ha2⟩))))))
  · refine ⟨by omega, by omega, fun a ha => by rw [habove a (by omega)]; exact hz a (by omega),
      fun a ha _ => hbelow a ha, fun _ ha => Or.inl ha⟩
  · simp only [readRep_phi]; omega

/-! ## Top-layer representation carrying exact empty-graph capacities -/

/-- Strengthens `asmTopRep` (leaving `AssemblyTopIface.lean` untouched) with the invariant that an
empty state (`x.ne = none`) stores `emptyGraph` with exact capacities `(x.vCap, x.eCap)` at
`b + ASM_HDR_SIZE` inside `[x.resLo, x.resHi)`. Shares the exact same `τ`, `phi`, and `foot`. -/
noncomputable def asmTopRepEq {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ} {impl : SparsifyImpl}
    (R_CF : DSRep CompFamilyAbs) (R_BR : DSRep (AsmBranchAbs depth))
    (cfV cfE : R_CF.τ → ℕ)
    (wordExp capExp limbMul w L P_fp vCap eCap : ℕ) :
    DSRep (SparseCoreOrdAbs (sparseCoreProgTool lsfInit C_lsst depth impl)) where
  τ := AsmTopMeta R_CF.τ R_BR.τ
  rep b a x mem :=
    (asmTopRep (lsfInit := lsfInit) (C_lsst := C_lsst) (impl := impl) R_CF R_BR
      wordExp capExp limbMul w L P_fp vCap eCap).rep b a x mem ∧
    (x.ne = none →
      x.resLo = b + ASM_HDR_SIZE ∧
      b + ASM_HDR_SIZE + dynGraphSize x.vCap x.eCap ≤ x.resHi ∧
      DynGraphAt mem (b + ASM_HDR_SIZE) x.vCap x.eCap emptyGraph) ∧
    (∀ ne, x.ne = some ne → cfV ne.xCF = x.vCap ∧ cfE ne.xCF = x.eCap)
  phi _ x mem := asmTopPhi R_CF R_BR x mem
  foot b x a := asmTopFoot R_CF R_BR rfl rfl b x a

/-- `asmTopRepEq` is local whenever `R_CF` and `R_BR` are local. -/
theorem asmTopRepEq_local {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ} {impl : SparsifyImpl}
    {R_CF : DSRep CompFamilyAbs} {R_BR : DSRep (AsmBranchAbs depth)}
    {cfV cfE : R_CF.τ → ℕ}
    {wordExp capExp limbMul w L P_fp vCap eCap : ℕ}
    (hCF : R_CF.Local) (hBR : R_BR.Local) :
    (asmTopRepEq (lsfInit := lsfInit) (C_lsst := C_lsst) (impl := impl) R_CF R_BR cfV cfE
      wordExp capExp limbMul w L P_fp vCap eCap).Local := by
  intro b a x mem mem' hagree
  have hloc := asmTopRep_local (lsfInit := lsfInit) (C_lsst := C_lsst) (impl := impl)
    (wordExp := wordExp) (capExp := capExp) (limbMul := limbMul) (w := w) (L := L) (P_fp := P_fp)
    (vCap := vCap) (eCap := eCap) hCF hBR b a x mem mem' hagree
  refine ⟨fun ⟨h1, h2, h3⟩ => ⟨hloc.1 h1, fun hne => ?_, h3⟩, hloc.2⟩
  obtain ⟨hlo, hhi, hdg⟩ := h2 hne
  refine ⟨hlo, hhi, dynGraphAt_of_agree hdg fun addr ha1 ha2 => ?_⟩
  exact (hagree addr (Or.inr (Or.inl ⟨by omega, by omega⟩))).symm

end MinCostFlow.SparseCore.Program
