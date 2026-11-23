module

public import MinCostFlow.MinRatio.SelectLevelFill
public import MinCostFlow.MinRatio.SelectCoreList
public import MinCostFlow.MinRatio.SelectEmbCopy
public import MinCostFlow.MinRatio.WireCoreReadEmbKFBL
import WordRAM.Tactic

/-!
# Populating an interior select level block (`SelectInteriorFill`)

Verifies `selectFillInteriorLevelBody` (`[metaBase, j, handle, branch, prevLen, L, slot, scratch]`),
which populates `B.fPtr j`, `B.lenPtr j` (`shift = 0`, distinct `L` and `Lw`), and `B.embPtr j`
for an interior level `j < B.d` from sparse-core readouts `op 2` (LSF, via `SparseCoreReadoutFootAt.op2_runs`
and `op2StretchTableBelow_of_readoutFootAt`) and `op 4` (embedding via `selEmbSrcOk_of_op4_selectRegion`,
`WireCoreReadEmbKFBL.lean`), preserving `Rcore.rep` and all other parts of `SelBlocksDataAt`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program SparseCore.Program

/-- Populate `B.fPtr j`, `B.lenPtr j` (`shift = 0`), and `B.embPtr j` for an interior level `j < d`.
Arguments: `[metaBase, j, handle, branch, prevLen, L, slot, scratch]` (`reg 0..7`).
Returns the new scratch pointer. -/
def selectFillInteriorLevelBody
    (readLSFProc readEmbProc dgCopyProc coreLenProc filterProc embCopyProc : ℕ) : Stmt :=
  .assign 8 (.load (.bin .add (.reg 0) (.const 1))) ;; -- d
  .assign 9 (.bin .add (.reg 8) (.const 1)) ;; -- d + 1
  .assign 10 (.bin .add (.reg 0) (.const 2)) ;; -- tb
  .assign 11 (.load (.bin .add (.reg 10) (.reg 1))) ;; -- gPtr = GPtr j
  .assign 12 (.load (.bin .add (.bin .add (.reg 10) (.reg 9)) (.reg 1))) ;; -- vCap
  .assign 13 (.load (.bin .add (.bin .add (.reg 10) (.bin .mul (.const 2) (.reg 9))) (.reg 1))) ;; -- eCap
  .assign 14 (.load (.bin .add (.bin .add (.reg 10) (.bin .mul (.const 4) (.reg 9))) (.reg 1))) ;; -- lenPtr
  .assign 15 (.load (.bin .add (.bin .add (.reg 10) (.bin .mul (.const 5) (.reg 9))) (.reg 1))) ;; -- embPtr
  .assign 16 (.load (.bin .add (.bin .add (.reg 10) (.bin .mul (.const 6) (.reg 9))) (.reg 1))) ;; -- fPtr
  .assign 17 (.load (.bin .add (.reg 11) (.const 3))) ;; -- m_j = (G j).m
  .assign 18 (.bin .add (.bin .add (.bin .add (.reg 11) (.const 4)) (.bin .mul (.const 7) (.reg 12)))
    (.reg 13)) ;; -- dgEListBase gPtr vCap eCap
  .assign 19 (.bin .add (.bin .add (.reg 16) (.const 4)) (.bin .mul (.const 7) (.reg 12))) ;; -- dgEPresBase fPtr vCap
  .call 20 readLSFProc [.reg 2, .reg 3, .reg 11, .reg 7] ;; -- op 2 -> sc1
  .assign 21 (.load (.bin .add (.reg 7) (.const 1))) ;; -- fBase
  .assign 22 (.load (.bin .add (.reg 7) (.const 3))) ;; -- stDesc
  .cond (.reg 17)
    (.assign 23 (.load (.bin .add (.reg 7) (.const 4))) ;; -- Lw
     .assign 24 (.load (.reg 22)) ;; -- numBase
     .assign 25 (.load (.bin .add (.reg 22) (.const 1)))) -- denBase
    .nop ;;
  .call 20 dgCopyProc [.reg 16, .reg 21, .reg 20] ;; -- sc2
  .cond (.reg 17)
    (.call 20 coreLenProc [.reg 4, .reg 24, .reg 25, .reg 14, .reg 18, .reg 17, .reg 5, .reg 23,
       .const 0, .reg 20])
    .nop ;; -- sc3
  .assign 26 (.reg 20) ;; -- coreListPtr = sc3
  .call 27 filterProc [.reg 18, .reg 17, .reg 19, .reg 26] ;; -- coreM
  .assign 28 (.bin .add (.reg 26) (.reg 17)) ;; -- sc4 = sc3 + m_j
  .call 20 readEmbProc [.reg 2, .reg 3, .reg 11, .reg 28] ;; -- op 4 -> sc5
  .assign 29 (.load (.reg 28)) ;; -- embTable
  .call 30 embCopyProc [.reg 29, .reg 15, .reg 13, .reg 6, .reg 26, .reg 27] ;;
  .ret (.reg 20)

theorem selectFillInteriorLevelBody_noRand (a b c d e f : ℕ) :
    (selectFillInteriorLevelBody a b c d e f).NoRand := by
  simp [selectFillInteriorLevelBody, Stmt.NoRand]

/-- Scratch space bound for `selectFillInteriorLevelBody` at a level with `m_j` edges, forest edge
count `mF`, and stretch limb upper bound `LwMax`. -/
def selectFillInteriorLevelSpace (m_j mF L LwMax : ℕ) : ℕ :=
  5 + 3 * mF + m_j * selCoreLenEdgeSpace L LwMax + m_j + 2

/-- Step cost bound for `selectFillInteriorLevelBody`. -/
def selectFillInteriorLevelCost (readoutCost nOld mOld nF mF m_j L LwMax slot : ℕ) : ℕ :=
  2 * readoutCost + dgCopyRefillCost nOld mOld nF mF +
    m_j * (selCoreLenEdgeCost L LwMax + 40) + 40 * m_j +
    m_j * (18 * slot + 80) + 520

/-- Op-`2` stretch-table layout and footprint predicate on all edges of `a.G.E` (implied by
`SparseCoreReadoutFootAt.op2_runs` via `op2StretchTableBelow_of_readoutFootAt`). -/
def Op2StretchTableBelow {w : ℕ} (fmt : Num.Format w) (L depth : ℕ)
    (tool : SparseCoreRestartTool) (initialGraph : MGraph) (k M N vCap eCap capExp : ℕ)
    (P : SparseCoreOrdParams) (allocation : ℕ → List ℕ → ℕ)
    (R : DSRep (SparseCoreOrdAbs tool)) (p : Program) (op : ℕ → ℕ) : Prop :=
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
             (cur ≤ st'.mem (stDesc + 1) + e * Lw + t ∧ st'.mem (stDesc + 1) + e * Lw + t < o.value))) ∧
      R.Respects (R.foot b x) (heapArg args) (D.space 2 a args mem) mem o.value b x' st'.mem ∧
      c + R.phi b x' st'.mem ≤ D.cost 2 a args mem + R.phi b x mem

/-- `SparseCoreReadoutFootAt` directly supplies `Op2StretchTableBelow`. -/
theorem op2StretchTableBelow_of_readoutFootAt {w L depth k M N vCap eCap capExp : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph : MGraph}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {p : Program} {op : ℕ → ℕ}
    (h : SparseCoreReadoutFootAt fmt L depth tool initialGraph k M N vCap eCap capExp P allocation R p op) :
    Op2StretchTableBelow fmt L depth tool initialGraph k M N vCap eCap capExp P allocation R p op :=
  fun b a x args mem pos ω hargs hhead hrep hpre hfoot hz hsp =>
    let ⟨body, hbody, o, st', c, x', hrun, hrep', ⟨fv, fe, hLw, hLSF, hfEnd, hfIn, hStDesc, hNum, hDen, _⟩, hresp, hcost⟩ :=
      h.op2_runs b a x args mem pos ω hargs hhead hrep hpre hfoot hz hsp
    ⟨body, hbody, o, st', c, x', hrun, hrep', ⟨fv, fe, hLw, hLSF, hfEnd, hfIn, hStDesc, hNum, hDen⟩, hresp, hcost⟩

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program SparseCore.Program

private lemma selCoreLenEdgeSpace_mono {L Lw₁ Lw₂ : ℕ} (h : Lw₁ ≤ Lw₂) :
    selCoreLenEdgeSpace L Lw₁ ≤ selCoreLenEdgeSpace L Lw₂ := by
  unfold selCoreLenEdgeSpace wireCoreLenEdgeSpace integerDivideSpace unsignedDivideSpace
  have hm := max_le_max_left L h
  have := Nat.mul_le_mul (show 5 * (2 * max L Lw₁) ≤ 5 * (2 * max L Lw₂) by omega)
    (show 2 * max L Lw₁ + 1 ≤ 2 * max L Lw₂ + 1 by omega)
  omega

private lemma selCoreLenEdgeCost_mono {L Lw₁ Lw₂ : ℕ} (h : Lw₁ ≤ Lw₂) :
    selCoreLenEdgeCost L Lw₁ ≤ selCoreLenEdgeCost L Lw₂ := by
  unfold selCoreLenEdgeCost wireCoreLenEdgeCost
  have hm := max_le_max_left L h; have := Nat.mul_le_mul hm hm; nlinarith

private lemma int_disj_of_foot {foot : ℕ → Prop} {lo hi a len cur ret : ℕ}
    (hFoot : ∀ t < len, foot (a + t) ∨ (cur ≤ a + t ∧ a + t < ret))
    (hDisjLo : ¬ foot lo)
    (hDisjF : ∀ addr, lo ≤ addr → addr < hi → ¬ foot addr)
    (hLenPos : 0 < len) (hLoCur : lo < cur) (hHi : hi ≤ cur) :
    a + len ≤ lo ∨ hi ≤ a := by
  by_contra h
  push Not at h
  by_cases hcmp : lo ≤ a
  · rcases hFoot 0 hLenPos with hf | hnew
    · exact hDisjF a hcmp h.2 (by simpa using hf)
    · omega
  · rcases hFoot (lo - a) (by omega) with hf | hnew
    · exact hDisjLo (by rw [show a + (lo - a) = lo by omega] at hf; exact hf)
    · omega

private lemma runs_seq_assign_ex {w : ℕ} {p : Program} {ω : ℕ → Bool} {r : ℕ} {e : Expr} {s2 : Stmt}
    {st : State} {v : ℕ} {P : Outcome → State → ℕ → Prop} (hv : e.eval w st = some v)
    (h2 : ∃ o out c, Runs w p ω s2 ⟨st.mem, Function.update st.regs r v, st.pos⟩ o out c ∧ P o out ((e.size + 1) + c + 1)) :
    ∃ o out c, Runs w p ω (.assign r e ;; s2) st o out c ∧ P o out c :=
  let ⟨o, out, _, hr2, hp⟩ := h2
  ⟨o, out, _, runs_seq_iff.mpr (Or.inr ⟨_, _, _, runs_assign_iff.mpr ⟨v, hv, rfl, rfl, rfl⟩, hr2, rfl⟩), hp⟩

private lemma runs_seq_call_ex {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ} {args : List Expr}
    {s2 : Stmt} {st st1 : State} {vs : List ℕ} {body : Stmt} {o1 : Outcome} {c1 : ℕ}
    {P : Outcome → State → ℕ → Prop} (hvs : evalArgs w st args = some vs) (hbody : p.procs[f]? = some body)
    (hr1 : Runs w p ω body (startState vs st.mem st.pos) o1 st1 c1)
    (h2 : ∃ o out c, Runs w p ω s2 ⟨st1.mem, Function.update st.regs r o1.value, st1.pos⟩ o out c ∧ P o out ((argsSize args + c1 + 1) + c + 1)) :
    ∃ o out c, Runs w p ω (.call r f args ;; s2) st o out c ∧ P o out c :=
  let ⟨o, out, _, hr2, hp⟩ := h2
  ⟨o, out, _, runs_seq_iff.mpr (Or.inr ⟨_, _, _, runs_call_iff.mpr ⟨vs, body, o1, st1, c1, hvs, hbody, hr1, rfl, rfl, rfl⟩, hr2, rfl⟩), hp⟩

set_option maxHeartbeats 1600000 in
/-- `selectFillInteriorLevelBody` populates `B.fPtr j`, `B.lenPtr j` (`shift = 0`), and
`B.embPtr j` for an interior level `j < B.d`, updating `SelBlocksDataAt` while preserving all
other parts, `R.rep`, and all memory `< scratch` outside `R.foot handle x`, `B.regF j`,
`B.regLen j`, and `B.regEmb j`. -/
theorem selectFillInteriorLevel_runs
    {w depth k M N capExp j pLast handle branch prevLen scratch pos : ℕ}
    {dgCopyProc coreLenProc filterProc embCopyProc : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph : MGraph}
    {Psc : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {p : Program} {op : ℕ → ℕ} {ω : ℕ → Bool}
    {B : SelectBlocksLoc} {metaBase : ℕ} {solverG : ℕ → ℕ} {D : SelBlocksData}
    {a : SparseCoreOrdAbs tool} {x : R.τ} {prevVal : ℕ → ℝ} {mem : ℕ → ℕ}
    (hfmt4 : fmt.limbBits = 4) (hLocalR : R.Local)
    (hw16 : 16 < 2 ^ w) (hLkW : B.Lk < 2 ^ w) (hSlotW : B.slot < 2 ^ w)
    (hj : j < B.d) (hbrLt : branch < k) (hkW : k < 2 ^ w) (hHndW : handle < 2 ^ w)
    (htab : SelectMetaTableAt mem (selectMlocOf B metaBase solverG pLast))
    (hblk : SelBlocksDataAt mem B fmt.precision D pLast)
    (hMetaLe : metaBase + selectLevelMetaSize B.d ≤ B.base)
    (hEndSc : B.endAddr ≤ scratch)
    (hG : DynGraphAt mem (solverG j) B.vCap B.eCap a.G)
    (hGEnd : solverG j + dynGraphSize B.vCap B.eCap ≤ scratch ∧
      (solverG j + dynGraphSize B.vCap B.eCap ≤ B.base ∨ B.endAddr ≤ solverG j))
    (hrep : R.rep handle a x mem)
    (hIn : SparseCoreOrdInput tool k M N a.st a.G a.ord a.n)
    (hFootBelow : ∀ addr, R.foot handle x addr → addr < scratch ∧ (addr < B.base ∨ B.endAddr ≤ addr))
    (hDisjG : ∀ addr, solverG j ≤ addr → addr < solverG j + dynGraphSize B.vCap B.eCap →
      ¬ R.foot handle x addr)
    (hDisjPrev : ∀ addr, prevLen ≤ addr → addr < prevLen + B.eCap * B.Lk → ¬ R.foot handle x addr)
    (hPrevLe : prevLen + B.eCap * B.Lk ≤ scratch)
    (hPrevDisj : prevLen + B.eCap * B.Lk ≤ B.lenPtr j ∨ B.embPtr j ≤ prevLen)
    (hPrevOffF : prevLen + B.eCap * B.Lk ≤ B.fPtr j ∨ B.phiPtr j ≤ prevLen)
    (hPrevVal : EdgeValuesAt mem prevLen 4 B.Lk fmt.precision a.G.E prevVal)
    (hFV : ∀ v ∈ (tool.lsfs a.st branch).F.F.V, v < B.vCap)
    (hFE : ∀ e ∈ (tool.lsfs a.st branch).F.F.E, e < B.eCap)
    (hLenFit : ∀ e ∈ a.G.E,
      ∃ q : ℤ, Num.Fits 4 B.Lk q ∧
        (q : ℝ) / (2 : ℝ) ^ fmt.precision = (tool.lsfs a.st branch).wstr e * prevVal e)
    (hEmbSlot : ∀ e ∈ (coreGraph a.G (tool.lsfs a.st branch)).E,
      (mWalkEncode (tool.emb a.st branch e)).length ≤ B.slot)
    (hFootAt : SparseCoreReadoutFootAt fmt B.Lk depth tool initialGraph k M N B.vCap B.eCap capExp
      Psc allocation R p op)
    (hDgCopy : ∀ vcF ecF, MeetsContract w p dgCopyProc
      (dgCopyRefillContract w B.vCap B.eCap vcF ecF (D.F j) (tool.lsfs a.st branch).F.F))
    (hCoreLen : ∀ eL : List ℕ,
      MeetsContract w p coreLenProc (selCoreLenFillContract w fmt.precision B.eCap eL))
    (hFilter : ∀ eL : List ℕ, MeetsContract w p filterProc (selFilterAbsentContract w eL))
    (hEmbCopy : ∀ eL : List ℕ,
      MeetsContract w p embCopyProc (selEmbCopyContract w eL (tool.emb a.st branch)))
    (hz : ZeroFrom mem scratch)
    (hroom :
      let LwMax := B.Lk + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1)
      scratch + selectFillInteriorLevelSpace a.G.m (tool.lsfs a.st branch).F.F.m B.Lk LwMax < 2 ^ w) :
    let LwMax := B.Lk + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1)
    let F := (tool.lsfs a.st branch).F.F
    let coreE := (coreGraph a.G (tool.lsfs a.st branch)).E
    ∃ sc5 cost out, ∃ y : R.τ,
      Runs w p ω (selectFillInteriorLevelBody (op 2) (op 4) dgCopyProc coreLenProc filterProc embCopyProc)
        (startState [metaBase, j, handle, branch, prevLen, B.Lk, B.slot, scratch] mem pos)
        (.returned sc5) out cost ∧
      scratch ≤ sc5 ∧
      sc5 ≤ scratch + selectFillInteriorLevelSpace a.G.m F.m B.Lk LwMax ∧
      R.rep handle a y out.mem ∧
      SelBlocksDataAt out.mem B fmt.precision
        { D with
          F := Function.update D.F j F
          E := Function.update D.E j a.G.E
          len := Function.update D.len j (fun e => (tool.lsfs a.st branch).wstr e * prevVal e)
          coreE := Function.update D.coreE j coreE
          emb := Function.update D.emb j (tool.emb a.st branch) } pLast ∧
      ZeroFrom out.mem sc5 ∧
      (∀ addr, R.foot handle y addr → R.foot handle x addr ∨ (scratch ≤ addr ∧ addr < sc5)) ∧
      (∀ addr < scratch, ¬ R.foot handle x addr → ¬ B.regF j addr → ¬ B.regLen j addr →
        ¬ B.regEmb j addr → out.mem addr = mem addr) ∧
      cost + R.phi handle y out.mem ≤
        selectFillInteriorLevelCost Psc.readout (D.F j).n (D.F j).m F.n F.m a.G.m B.Lk LwMax B.slot +
          R.phi handle x mem := by
  intro LwMax F coreE
  have hroom' : scratch + (5 + 3 * F.m + a.G.m * selCoreLenEdgeSpace B.Lk LwMax + a.G.m + 2) < 2 ^ w := hroom
  have hw1 : 1 < 2 ^ w := by omega
  have hjLe : j ≤ B.d := Nat.le_of_lt hj
  have hBaseLeEnd : B.base ≤ B.endAddr := by rw [B.endAddr_eq]; omega
  have hBlkJ := B.blk_le_last hjLe
  have hBaseLeFJ : B.base ≤ B.fPtr j := by unfold SelectBlocksLoc.fPtr; omega
  have hFJEnd : B.fPtr j + dynGraphSize B.vCap B.eCap = B.phiPtr j := rfl
  have hLenJEnd : B.lenPtr j + B.eCap * B.Lk = B.embPtr j := rfl
  have hFJLeLenJ : B.phiPtr j ≤ B.lenPtr j := by unfold SelectBlocksLoc.lenPtr; omega
  have hEmbJEnd : B.embPtr j + B.eCap + B.eCap * B.slot = B.fPtr j + B.levelSize := by
    unfold SelectBlocksLoc.embPtr SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr SelectBlocksLoc.levelSize; omega
  have hLastLeEnd : B.lastGPtr ≤ B.endAddr := by unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr; omega
  have hLenLeEnd : B.lenPtr j + B.eCap * B.Lk ≤ B.endAddr := by omega
  have hDgSz : dynGraphSize B.vCap B.eCap = 4 + 7 * B.vCap + 9 * B.eCap := rfl
  have hMetaSz : selectLevelMetaSize B.d = 2 + 8 * (B.d + 1) := rfl
  have hSpDef : selectFillInteriorLevelSpace a.G.m F.m B.Lk LwMax =
      5 + 3 * F.m + a.G.m * selCoreLenEdgeSpace B.Lk LwMax + a.G.m + 2 := rfl
  have hGMLe : a.G.m ≤ B.eCap := by
    unfold MGraph.m
    calc a.G.E.card ≤ (Finset.range B.eCap).card :=
          Finset.card_le_card fun e he => Finset.mem_range.mpr (hG.2.2.1 e he)
      _ = B.eCap := Finset.card_range _
  have hrow := htab.2.2 j hjLe
  have hdM : mem (metaBase + 1) = B.d := by simpa [smDOff, selectMlocOf] using htab.2.1
  have hgPtrM : mem (metaBase + 2 + j) = solverG j := by simpa [smEntryAddr, smTableOff, selectMlocOf, hj] using hrow.1
  have hvCapM : mem (metaBase + 2 + (B.d + 1) + j) = B.vCap := by simpa [smEntryAddr, smTableOff, selectMlocOf] using hrow.2.1
  have heCapM : mem (metaBase + 2 + 2 * (B.d + 1) + j) = B.eCap := by simpa [smEntryAddr, smTableOff, selectMlocOf] using hrow.2.2.1
  have hlenM : mem (metaBase + 2 + 4 * (B.d + 1) + j) = B.lenPtr j := by simpa [smEntryAddr, smTableOff, selectMlocOf] using hrow.2.2.2.2.1
  have hembM : mem (metaBase + 2 + 5 * (B.d + 1) + j) = B.embPtr j := by simpa [smEntryAddr, smTableOff, selectMlocOf] using hrow.2.2.2.2.2.1
  have hfM : mem (metaBase + 2 + 6 * (B.d + 1) + j) = B.fPtr j := by simpa [smEntryAddr, smTableOff, selectMlocOf] using hrow.2.2.2.2.2.2.1
  have hGM : mem (solverG j + 3) = a.G.m := by simpa [dgMOff] using hG.2.2.2.2.2.2.1
  obtain ⟨eL, heL_len, _heL_nd, heL_mem, heL_at, _⟩ := hG.2.2.2.2.2.2.2.2.2.2.2.2.1
  let DMid : SelBlocksData :=
    { D with
      F := Function.update D.F j F
      E := Function.update D.E j a.G.E
      len := Function.update D.len j (fun e => (tool.lsfs a.st branch).wstr e * prevVal e) }
  let DTarget : SelBlocksData :=
    { DMid with
      coreE := Function.update D.coreE j coreE
      emb := Function.update D.emb j (tool.emb a.st branch) }
  -- Step 1: execute `op 2` at `scratch`
  have hGEndSc : solverG j + dynGraphSize B.vCap B.eCap ≤ scratch := hGEnd.1
  obtain ⟨b2, hb2, o1, st1, c1, y1, hr1, hrep1, hpost1, hresp1, hcost1⟩ :=
    op2StretchTableBelow_of_readoutFootAt hFootAt handle a x [handle, branch, solverG j, scratch] mem pos ω
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro v (rfl|rfl|rfl|rfl) <;> omega)
      rfl hrep ⟨hIn, handle, branch, solverG j, scratch, rfl, hbrLt, hG, by omega⟩
      (fun addr ha => (hFootBelow addr ha).1)
      hz (by change scratch + 5 < 2 ^ w; omega)
  obtain ⟨vcF, ecF, hLwLe, hLSF1, hfBaseLe, hfBaseFoot, hStDescLe, hNum1, hDen1⟩ := hpost1
  simp only [heapArg, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.getLastD_cons, List.getLastD_nil]
    at hLwLe hLSF1 hfBaseLe hfBaseFoot hStDescLe hNum1 hDen1 hresp1
  set sc1 := o1.value; set mem1 := st1.mem
  set fBase := mem1 (scratch + 1); set stDesc := mem1 (scratch + 3); set Lw := mem1 (scratch + 4)
  set numBase := mem1 stDesc; set denBase := mem1 (stDesc + 1)
  have hsc1Lo : scratch ≤ sc1 := hresp1.1; have hsc1Hi : sc1 ≤ scratch + 5 := hresp1.2.1
  have hz1 : ZeroFrom mem1 sc1 := hresp1.2.2.1
  have hfr1 := hresp1.2.2.2.1; have hft1 := hresp1.2.2.2.2
  have hblk1 : SelBlocksDataAt mem1 B fmt.precision D pLast :=
    hblk.of_agree fun addr h1 h2 => hfr1 addr (by omega) (fun hf => by have := (hFootBelow addr hf).2; omega)
  have hDisjY1Blk : ∀ addr, B.base ≤ addr → addr < B.endAddr → ¬ R.foot handle y1 addr :=
    fun addr h1 h2 hfy => Or.elim (hft1 addr hfy) (fun hfx => by have := (hFootBelow addr hfx).2; omega) (fun hnew => by omega)
  have hfBaseDisj : fBase + dynGraphSize vcF ecF ≤ B.fPtr j ∨ B.fPtr j + dynGraphSize B.vCap B.eCap ≤ fBase :=
    int_disj_of_foot (fun t ht => hfBaseFoot (fBase + t) (by omega) (by omega))
      (hDisjY1Blk (B.fPtr j) (by omega) (by omega))
      (fun addr h1 h2 => hDisjY1Blk addr (by omega) (by omega))
      (by unfold dynGraphSize; omega) (by omega) (by omega)
  -- Step 2: `dgCopyRefill [B.fPtr j, fBase, sc1]` -> `sc2`, `mem2`
  obtain ⟨bCpy, hbCpy, o2, st2, c2, hr2, hp2, hc2⟩ :=
    hDgCopy vcF ecF [B.fPtr j, fBase, sc1] mem1 st1.pos ω
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro v (rfl|rfl|rfl) <;> omega)
      ⟨B.fPtr j, fBase, sc1, rfl, hw16, by omega, by omega, hfBaseDisj,
        hblk1.1 j hjLe, hLSF1.2.1, hFV, hFE, hz1, by change sc1 + 3 * F.m < 2 ^ w; omega⟩
  obtain ⟨hsc2Eq, hF2, hz2, hfr2⟩ := hp2
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hsc2Eq hfr2
  set sc2 := o2.value
  have hsc2Def : sc2 = sc1 + 3 * F.m := hsc2Eq
  set mem2 := st2.mem
  have hblk2 : SelBlocksDataAt mem2 B fmt.precision { D with F := Function.update D.F j F } pLast :=
    hblk1.setF_below hjLe (by omega)
      (fun a ha hnr => hfr2 a ha (by unfold SelectBlocksLoc.regF at hnr; omega)) hF2
  have hY1Ag2 : ∀ addr, R.foot handle y1 addr → mem2 addr = mem1 addr := fun addr ha =>
    hfr2 addr (Or.elim (hft1 addr ha) (fun hfx => by have := (hFootBelow addr hfx).1; omega) (fun hnew => by omega))
      (by by_contra h; exact hDisjY1Blk addr (by omega) (by omega) ha)
  have hrep2 : R.rep handle a y1 mem2 :=
    (hLocalR handle a y1 mem1 mem2 fun addr ha => (hY1Ag2 addr ha).symm).1 hrep1
  have hphi2 : R.phi handle y1 mem2 = R.phi handle y1 mem1 :=
    ((hLocalR handle a y1 mem1 mem2 fun addr ha => (hY1Ag2 addr ha).symm).2).symm
  -- Step 3: build the complete execution cleanly from `s0`
  let s0 := startState [metaBase, j, handle, branch, prevLen, B.Lk, B.slot, scratch] mem pos
  -- Helper: run Steps 4–6 (`selFilterAbsent` + `op 4` + `selEmbCopy` + `ret`) from any `(sc3, mem3, pos3)`
  have hTail : ∀ (sc3 pos3 : ℕ) (mem3 : ℕ → ℕ) (regs3 : ℕ → ℕ),
      regs3 2 = handle → regs3 3 = branch → regs3 6 = B.slot →
      regs3 11 = solverG j → regs3 13 = B.eCap → regs3 15 = B.embPtr j →
      regs3 17 = a.G.m → regs3 18 = dgEListBase (solverG j) B.vCap B.eCap →
      regs3 19 = dgEPresBase (B.fPtr j) B.vCap → regs3 20 = sc3 →
      sc2 ≤ sc3 → sc3 ≤ sc2 + a.G.m * selCoreLenEdgeSpace B.Lk LwMax →
      ZeroFrom mem3 sc3 →
      R.rep handle a y1 mem3 →
      R.phi handle y1 mem3 = R.phi handle y1 mem1 →
      SelBlocksDataAt mem3 B fmt.precision DMid pLast →
      (∀ addr < scratch, ¬ R.foot handle x addr → ¬ B.regF j addr → ¬ B.regLen j addr →
        mem3 addr = mem addr) →
      ∃ sc5 cTail out, ∃ y2 : R.τ,
        Runs w p ω
          (.assign 26 (.reg 20) ;;
           .call 27 filterProc [.reg 18, .reg 17, .reg 19, .reg 26] ;;
           .assign 28 (.bin .add (.reg 26) (.reg 17)) ;;
           .call 20 (op 4) [.reg 2, .reg 3, .reg 11, .reg 28] ;;
           .assign 29 (.load (.reg 28)) ;;
           .call 30 embCopyProc [.reg 29, .reg 15, .reg 13, .reg 6, .reg 26, .reg 27] ;;
           .ret (.reg 20))
          ⟨mem3, regs3, pos3⟩ (.returned sc5) out cTail ∧
        sc3 + a.G.m ≤ sc5 ∧ sc5 ≤ sc3 + a.G.m + 2 ∧
        R.rep handle a y2 out.mem ∧
        SelBlocksDataAt out.mem B fmt.precision DTarget pLast ∧
        ZeroFrom out.mem sc5 ∧
        (∀ addr, R.foot handle y2 addr → R.foot handle x addr ∨ (scratch ≤ addr ∧ addr < sc5)) ∧
        (∀ addr < scratch, ¬ R.foot handle x addr → ¬ B.regF j addr → ¬ B.regLen j addr →
          ¬ B.regEmb j addr → out.mem addr = mem addr) ∧
        cTail + R.phi handle y2 out.mem ≤
          Psc.readout + 40 * a.G.m + a.G.m * (18 * B.slot + 80) + 120 + R.phi handle y1 mem1 := by
    intro sc3 pos3 mem3 regs3 r2 r3 r6 r11 r13 r15 r17 r18 r19 r20
      hsc3Lo hsc3Hi hz3 hrep3 hphi3 hblk3 hfr3
    have hG3 : DynGraphAt mem3 (solverG j) B.vCap B.eCap a.G :=
      DynGraphAt.of_agree hG fun addr ha1 ha2 =>
        hfr3 addr (by omega) (hDisjG addr ha1 ha2)
          (fun h => by unfold SelectBlocksLoc.regF at h; rcases hGEnd.2 with h1 | h1 <;> omega)
          (fun h => by unfold SelectBlocksLoc.regLen at h; rcases hGEnd.2 with h1 | h1 <;> omega)
    have heL3 : ListAt mem3 (dgEListBase (solverG j) B.vCap B.eCap) eL := fun idx hidx => by
      rw [hfr3 _ (by unfold dgEListBase; omega)
        (hDisjG _ (by unfold dgEListBase; omega) (by unfold dgEListBase; omega))
        (fun h => by unfold SelectBlocksLoc.regF dgEListBase at h; rcases hGEnd.2 with h1 | h1 <;> omega)
        (fun h => by unfold SelectBlocksLoc.regLen dgEListBase at h; rcases hGEnd.2 with h1 | h1 <;> omega)]
      exact heL_at idx hidx
    have hF3 : DynGraphAt mem3 (B.fPtr j) B.vCap B.eCap F := by
      have h := hblk3.1 j hjLe; unfold SelPartF at h; simpa [DMid] using h
    obtain ⟨bFilt, hbFilt, oFilt, st4, c4, hr4, hp4, hc4⟩ :=
      hFilter eL [dgEListBase (solverG j) B.vCap B.eCap, eL.length, dgEPresBase (B.fPtr j) B.vCap, sc3]
        mem3 pos3 ω
        (by simp only [List.mem_cons, List.not_mem_nil, or_false]
            rintro v (rfl|rfl|rfl|rfl)
            · unfold dgEListBase; omega
            · rw [heL_len]; omega
            · unfold dgEPresBase; omega
            · omega)
        ⟨dgEListBase (solverG j) B.vCap B.eCap, dgEPresBase (B.fPtr j) B.vCap, sc3, rfl,
          hw16, by unfold dgEListBase; omega, by rw [heL_len]; omega, Or.inl (by unfold dgEListBase; omega), heL3,
          fun e he => by
            have heC := hG.2.2.1 e ((heL_mem e).mp he)
            have hbit := hF3.2.2.2.2.2.2.2.2.2.2.2.1 e heC
            refine ⟨by omega, by unfold dgEPresBase; omega, by rw [hbit]; split_ifs <;> omega,
              Or.inl (by unfold dgEPresBase; omega)⟩⟩
    obtain ⟨_, _, _, hargs4, hcoreMLen, hCoreAt4, hFr4⟩ := hp4
    simp only [List.cons.injEq] at hargs4; obtain ⟨rfl, -, rfl, rfl, -⟩ := hargs4
    set coreL := selAbsent mem3 (dgEPresBase (B.fPtr j) B.vCap) eL
    have hCoreLenLe : coreL.length ≤ a.G.m := by rw [← heL_len]; exact selAbsent_length_le _ _ _
    have hCoreMem : ∀ e, e ∈ coreL ↔ e ∈ coreE := fun e => by
      simpa [coreL, coreE, coreGraph] using mem_selAbsent_iff hF3 heL_mem hG.2.2.1 e
    set sc4 := sc3 + a.G.m
    have hz4 : ZeroFrom st4.mem sc4 := fun addr ha => (hFr4 addr (Or.inr (by omega))).trans (hz3 addr (by omega))
    have hY1Ag4 : ∀ addr, R.foot handle y1 addr → st4.mem addr = mem3 addr := fun addr ha =>
      hFr4 addr (Or.inl (Or.elim (hft1 addr ha) (fun hfx => by have := (hFootBelow addr hfx).1; omega) (fun hnew => by omega)))
    have hrep4 := (hLocalR handle a y1 mem3 st4.mem fun addr ha => (hY1Ag4 addr ha).symm).1 hrep3
    have hphi4 := ((hLocalR handle a y1 mem3 st4.mem fun addr ha => (hY1Ag4 addr ha).symm).2).symm.trans hphi3
    have hG4 := DynGraphAt.of_agree hG3 fun addr _ ha2 => hFr4 addr (Or.inl (by omega))
    have hblk4 : SelBlocksDataAt st4.mem B fmt.precision DMid pLast :=
      hblk3.of_agree fun addr _ ha2 => hFr4 addr (Or.inl (by omega))
    obtain ⟨b4, hb4, o5, st5, c5, y2, hr5, hrep5, hpost5, hresp5, hcost5⟩ :=
      hFootAt.op4_runs handle a y1 [handle, branch, solverG j, sc4] st4.mem st4.pos ω
        (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro v (rfl|rfl|rfl|rfl) <;> omega)
        rfl hrep4 ⟨hIn, handle, branch, solverG j, sc4, rfl, hbrLt, hG4, by omega⟩
        (fun addr ha => by
          change addr < sc4
          exact Or.elim (hft1 addr ha) (fun hfx => by have := (hFootBelow addr hfx).1; omega) (fun hnew => by omega))
        hz4 (by change sc4 + 2 < 2 ^ w; omega)
    obtain ⟨hEmbRd5, hBounded5, hCapLe5, hWalkWords5, hTableFoot5, hWalkFoot5⟩ := hpost5
    simp only [heapArg, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, List.getLastD_cons, List.getLastD_nil]
      at hEmbRd5 hBounded5 hCapLe5 hWalkWords5 hTableFoot5 hWalkFoot5 hresp5
    set sc5 := o5.value; set embTable := st5.mem sc4
    have hsc5Lo : sc4 ≤ sc5 := hresp5.1; have hsc5Hi : sc5 ≤ sc4 + 2 := hresp5.2.1
    have hz5 : ZeroFrom st5.mem sc5 := hresp5.2.2.1
    have hfr5 := hresp5.2.2.2.1; have hft5 := hresp5.2.2.2.2
    have hDisjY2Blk : ∀ addr, B.base ≤ addr → addr < B.endAddr → ¬ R.foot handle y2 addr :=
      fun addr h1 h2 hfy2 => Or.elim (hft5 addr hfy2) (fun hfy1 => hDisjY1Blk addr h1 h2 hfy1) (fun hnew => by omega)
    have hblk5 : SelBlocksDataAt st5.mem B fmt.precision DMid pLast :=
      hblk4.of_agree fun addr h1 h2 => hfr5 addr (by omega) (hDisjY1Blk addr h1 h2)
    have hCoreAt5 : ListAt st5.mem sc3 coreL := fun idx hidx => by
      rw [hfr5 (sc3 + idx) (by omega) (fun hf =>
        Or.elim (hft1 _ hf) (fun hfx => by have := (hFootBelow _ hfx).1; omega) (fun hnew => by omega))]
      exact hCoreAt4 idx hidx
    have hEmbPre : (selEmbCopyContract w coreL (tool.emb a.st branch)).pre
        [embTable, B.embPtr j, B.eCap, B.slot, sc3, coreL.length] st5.mem := by
      refine ⟨embTable, B.embPtr j, B.eCap, B.slot, sc3, rfl, hw16, by omega, by omega,
        Or.inr (by omega), hCoreAt5, fun e he => ?_⟩
      have heCore := (hCoreMem e).mp he
      have heCap := lt_of_lt_of_le (hBounded5.2.2 e heCore).1 hCapLe5
      exact ⟨heCap, selEmbSrcOk_of_op4_selectRegion hBounded5 hWalkWords5 hTableFoot5 hWalkFoot5
        (by omega) heCap
        (fun addr h1 h2 => hDisjY2Blk addr
          (by unfold SelectBlocksLoc.embPtr SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr at h1; omega)
          (by omega))
        (fun addr _ h2 hnew => by omega) heCore (hEmbSlot e heCore)⟩
    obtain ⟨bEmb, hbEmb, oEmb, st6, c6, hr6, hp6, hc6⟩ :=
      hEmbCopy coreL [embTable, B.embPtr j, B.eCap, B.slot, sc3, coreL.length] st5.mem st5.pos ω
        (by simp only [List.mem_cons, List.not_mem_nil, or_false]
            rintro v (rfl|rfl|rfl|rfl|rfl|rfl); all_goals first | exact hSlotW | (have := hBounded5.2.1; omega))
        hEmbPre
    have hp6' := hp6
    obtain ⟨_, _, _, _, _, hargs6, _, _, hFr6Raw, _⟩ := hp6
    simp only [List.cons.injEq] at hargs6; obtain ⟨rfl, rfl, rfl, rfl, rfl, -⟩ := hargs6
    have hFr6 : ∀ addr, addr < B.embPtr j ∨ B.fPtr j + B.levelSize ≤ addr → st6.mem addr = st5.mem addr :=
      fun addr ha => hFr6Raw addr (by rw [← hEmbJEnd] at ha; exact ha)
    have hblk6 : SelBlocksDataAt st6.mem B fmt.precision DTarget pLast :=
      selEmbCopy_setEmb (pLast := pLast) hp6' hblk5 hj
        (fun e he => ⟨hG.2.2.1 e (Finset.mem_sdiff.mp ((hCoreMem e).mp he)).1, hEmbSlot e ((hCoreMem e).mp he)⟩)
        (fun e he => Or.inl ((hCoreMem e).mpr he))
        (fun _ _ _ => rfl)
        (fun e he hnot => absurd ((hCoreMem e).mpr he) hnot)
    have hY2Ag6 : ∀ addr, R.foot handle y2 addr → st6.mem addr = st5.mem addr := fun addr ha =>
      hFr6 addr (by
        by_contra h
        exact hDisjY2Blk addr
          (by unfold SelectBlocksLoc.embPtr SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr at h; omega)
          (by omega) ha)
    have hrep6 : R.rep handle a y2 st6.mem :=
      (hLocalR handle a y2 st5.mem st6.mem fun addr ha => (hY2Ag6 addr ha).symm).1 hrep5
    have hphi6 : R.phi handle y2 st6.mem = R.phi handle y2 st5.mem :=
      ((hLocalR handle a y2 st5.mem st6.mem fun addr ha => (hY2Ag6 addr ha).symm).2).symm
    have hz6 : ZeroFrom st6.mem sc5 := fun addr ha =>
      (hFr6 addr (Or.inr (by omega))).trans (hz5 addr ha)
    refine (fun h => ?_) (show ∃ o out c, Runs w p ω
        (.assign 26 (.reg 20) ;; .call 27 filterProc [.reg 18, .reg 17, .reg 19, .reg 26] ;;
         .assign 28 (.bin .add (.reg 26) (.reg 17)) ;;
         .call 20 (op 4) [.reg 2, .reg 3, .reg 11, .reg 28] ;;
         .assign 29 (.load (.reg 28)) ;;
         .call 30 embCopyProc [.reg 29, .reg 15, .reg 13, .reg 6, .reg 26, .reg 27] ;; .ret (.reg 20))
        ⟨mem3, regs3, pos3⟩ o out c ∧ o = .returned sc5 ∧ out.mem = st6.mem ∧
        c + R.phi handle y2 out.mem ≤
          Psc.readout + 40 * a.G.m + a.G.m * (18 * B.slot + 80) + 120 + R.phi handle y1 mem1 from by
      refine runs_seq_assign_ex (v := sc3) (by simp [Expr.eval, r20]) ?_
      refine runs_seq_call_ex (by simp [evalArgs, Expr.eval, r17, r18, r19, heL_len]) hbFilt hr4 ?_
      refine runs_seq_assign_ex (v := sc4) (by
        have hsc4W : sc3 + a.G.m < 2 ^ w := by rw [hsc2Def] at hsc3Hi; omega
        simp [Expr.eval, BinOp.eval, r17, hsc4W, sc4]) ?_
      refine runs_seq_call_ex (by simp [evalArgs, Expr.eval, r2, r3, r11]) hb4 hr5 ?_
      refine runs_seq_assign_ex (v := embTable) (by simp [Expr.eval, embTable]) ?_
      refine runs_seq_call_ex (by simp [evalArgs, Expr.eval, r6, r13, r15, hcoreMLen]) hbEmb hr6 ?_
      refine ⟨.returned sc5, _, 2, runs_ret_iff.mpr ⟨sc5, by simp [Expr.eval, sc5], rfl, rfl, rfl⟩, rfl, rfl, ?_⟩
      simp only [selFilterAbsentContract, selEmbCopyContract, List.getD_cons_zero,
        List.getD_cons_succ, heL_len, Expr.size, argsSize] at hc4 hc6 ⊢
      change c5 + R.phi handle y2 st5.mem ≤ Psc.readout + R.phi handle y1 st4.mem at hcost5
      have hmul6 : coreL.length * (18 * B.slot + 80) ≤ a.G.m * (18 * B.slot + 80) :=
        Nat.mul_le_mul_right _ hCoreLenLe
      rw [hphi6]; rw [hphi4] at hcost5; omega)
    obtain ⟨_, out, cTail, rTail, rfl, hmemEq, hcTail⟩ := h
    refine ⟨sc5, cTail, out, y2, rTail, hsc5Lo, hsc5Hi, hmemEq ▸ hrep6, hmemEq ▸ hblk6, hmemEq ▸ hz6,
      fun addr hfy2 => ?_, fun addr hlt hnx hnf hnlen hnemb => ?_, hcTail⟩
    · rcases hft5 addr hfy2 with hfy1 | hnew
      · rcases hft1 addr hfy1 with hfx | hnew1
        · exact Or.inl hfx
        · exact Or.inr ⟨hnew1.1, by omega⟩
      · exact Or.inr ⟨by omega, hnew.2⟩
    · have hny1 : ¬ R.foot handle y1 addr := fun h =>
        Or.elim (hft1 addr h) (fun hfx => hnx hfx) (fun hnew => by omega)
      rw [hmemEq, hFr6 addr (by unfold SelectBlocksLoc.regEmb at hnemb; omega),
        hfr5 addr (by omega) hny1, hFr4 addr (Or.inl (by omega)), hfr3 addr hlt hnx hnf hnlen]
  -- Helper: run `dgCopyRefill` + conditional `selCoreLenFill` + `hTail` from post-`op 2` register state
  have hAfterOp2 : ∀ (regs1 : ℕ → ℕ),
      regs1 2 = handle → regs1 3 = branch → regs1 4 = prevLen → regs1 5 = B.Lk →
      regs1 6 = B.slot → regs1 7 = scratch → regs1 11 = solverG j → regs1 13 = B.eCap →
      regs1 14 = B.lenPtr j → regs1 15 = B.embPtr j → regs1 16 = B.fPtr j →
      regs1 17 = a.G.m → regs1 18 = dgEListBase (solverG j) B.vCap B.eCap →
      regs1 19 = dgEPresBase (B.fPtr j) B.vCap → regs1 20 = sc1 →
      regs1 21 = fBase → regs1 22 = stDesc →
      ∃ sc5 cMid out, ∃ y2 : R.τ,
        Runs w p ω
          (.cond (.reg 17)
            (.assign 23 (.load (.bin .add (.reg 7) (.const 4))) ;;
             .assign 24 (.load (.reg 22)) ;;
             .assign 25 (.load (.bin .add (.reg 22) (.const 1))))
            .nop ;;
           .call 20 dgCopyProc [.reg 16, .reg 21, .reg 20] ;;
           .cond (.reg 17)
             (.call 20 coreLenProc [.reg 4, .reg 24, .reg 25, .reg 14, .reg 18, .reg 17, .reg 5, .reg 23,
                .const 0, .reg 20])
             .nop ;;
           .assign 26 (.reg 20) ;;
           .call 27 filterProc [.reg 18, .reg 17, .reg 19, .reg 26] ;;
           .assign 28 (.bin .add (.reg 26) (.reg 17)) ;;
           .call 20 (op 4) [.reg 2, .reg 3, .reg 11, .reg 28] ;;
           .assign 29 (.load (.reg 28)) ;;
           .call 30 embCopyProc [.reg 29, .reg 15, .reg 13, .reg 6, .reg 26, .reg 27] ;;
           .ret (.reg 20))
          ⟨mem1, regs1, st1.pos⟩ (.returned sc5) out cMid ∧
        scratch ≤ sc5 ∧ sc5 ≤ scratch + selectFillInteriorLevelSpace a.G.m F.m B.Lk LwMax ∧
        R.rep handle a y2 out.mem ∧
        SelBlocksDataAt out.mem B fmt.precision DTarget pLast ∧
        ZeroFrom out.mem sc5 ∧
        (∀ addr, R.foot handle y2 addr → R.foot handle x addr ∨ (scratch ≤ addr ∧ addr < sc5)) ∧
        (∀ addr < scratch, ¬ R.foot handle x addr → ¬ B.regF j addr → ¬ B.regLen j addr →
          ¬ B.regEmb j addr → out.mem addr = mem addr) ∧
        cMid + R.phi handle y2 out.mem ≤
          Psc.readout + dgCopyRefillCost (D.F j).n (D.F j).m F.n F.m +
            a.G.m * (selCoreLenEdgeCost B.Lk LwMax + 40) + 40 * a.G.m +
            a.G.m * (18 * B.slot + 80) + 260 + R.phi handle y1 mem1 := by
    intro regs1 r2 r3 r4 r5 r6 r7 r11 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
    by_cases hm0 : a.G.m = 0
    · have hGEmp : a.G.E = ∅ := Finset.card_eq_zero.mp hm0
      have hblk2' : SelBlocksDataAt mem2 B fmt.precision DMid pLast :=
        hblk2.setLen_below hjLe (by omega) (fun _ _ _ => rfl)
          ⟨hG.2.2.1, fun e he => absurd he (by rw [hGEmp]; exact Finset.notMem_empty e)⟩
      let rg20 := Function.update regs1 20 sc2
      obtain ⟨sc5, cTail, out, y2, rTail, hsc5Lo, hsc5Hi, hrep6, hblk6, hz6, hft6, hfr6, hcTail⟩ :=
        hTail sc2 st2.pos mem2 rg20 (by simp [rg20, r2]) (by simp [rg20, r3]) (by simp [rg20, r6])
          (by simp [rg20, r11]) (by simp [rg20, r13]) (by simp [rg20, r15]) (by simp [rg20, r17])
          (by simp [rg20, r18]) (by simp [rg20, r19]) (by simp [rg20]) le_rfl (Nat.le_add_right _ _)
          hz2 hrep2 hphi2 hblk2' (fun addr hlt hnx hnf _ =>
            (hfr2 addr (by omega) (by unfold SelectBlocksLoc.regF at hnf; omega)).trans (hfr1 addr hlt hnx))
      refine ⟨sc5, _, out, y2,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _,
          runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, r17, hm0], runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _,
          runs_call_iff.mpr ⟨[B.fPtr j, fBase, sc1], bCpy, o2, st2, c2,
            by simp [evalArgs, Expr.eval, r16, r21, r20], hbCpy, hr2, rfl, rfl, rfl⟩,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _,
          runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, r17, hm0], runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩,
          rTail, rfl⟩), rfl⟩), rfl⟩),
        by rw [hsc2Def] at hsc5Lo; omega,
        by rw [hsc2Def, hm0] at hsc5Hi; rw [hSpDef, hm0]; simp only [Nat.zero_mul, Nat.add_zero] at hsc5Hi ⊢; omega,
        hrep6, hblk6, hz6, hft6, hfr6, ?_⟩
      simp only [dgCopyRefillContract, Expr.size, argsSize] at hc2 ⊢
      dsimp only [F, LwMax] at hc2 hcTail ⊢; rw [hm0] at hcTail ⊢; simp only [Nat.zero_mul, Nat.add_zero] at hcTail ⊢; omega
    · obtain ⟨e0, he0⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hm0)
      have hLwLt : Lw < 2 ^ w := by
        have h1 : Lw ≤ selCoreLenEdgeSpace B.Lk LwMax := by
          unfold selCoreLenEdgeSpace wireCoreLenEdgeSpace; have := le_trans hLwLe (le_max_right B.Lk LwMax); omega
        have := Nat.le_mul_of_pos_left (selCoreLenEdgeSpace B.Lk LwMax) (Nat.pos_of_ne_zero hm0); omega
      have hNumLt : numBase < 2 ^ w := by have := (hNum1 e0 he0).1; omega
      have hDenLt : denBase < 2 ^ w := by have := (hDen1 e0 he0).1; omega
      have hSpMono := selCoreLenEdgeSpace_mono (L := B.Lk) hLwLe
      have hCostMono := selCoreLenEdgeCost_mono (L := B.Lk) hLwLe
      have heL2 : ListAt mem2 (dgEListBase (solverG j) B.vCap B.eCap) eL := fun idx hidx => by
        rw [hfr2 _ (by unfold dgEListBase; omega) (by rcases hGEnd.2 with h1 | h1 <;> [left; right] <;> (unfold dgEListBase; omega)),
          hfr1 _ (by unfold dgEListBase; omega) (hDisjG _ (by unfold dgEListBase; omega) (by unfold dgEListBase; omega))]
        exact heL_at idx hidx
      have hPrev2 : ∀ e ∈ a.G.E, ∀ t < B.Lk, mem2 (prevLen + e * B.Lk + t) = mem (prevLen + e * B.Lk + t) := by
        intro e he t ht
        have hmul : e * B.Lk + t < B.eCap * B.Lk := by
          have := Nat.mul_le_mul_right B.Lk (Nat.succ_le_of_lt (hG.2.2.1 e he)); rw [Nat.succ_mul] at this; omega
        rw [hfr2 _ (by omega) (by rcases hPrevOffF with h | h <;> [left; right] <;> omega),
          hfr1 _ (by omega) (hDisjPrev _ (by omega) (by omega))]
      have hPrevVal2 := EdgeValuesAt.congr hPrevVal hPrev2
      have hFootAg2 : ∀ base, (∀ e ∈ a.G.E, base + e * Lw + Lw ≤ scratch ∧
          ∀ t < Lw, R.foot handle y1 (base + e * Lw + t) ∨ (scratch ≤ base + e * Lw + t ∧ base + e * Lw + t < sc1)) →
          ∀ e ∈ a.G.E, ∀ t < Lw, mem2 (base + e * Lw + t) = mem1 (base + e * Lw + t) := fun base hB e he t ht =>
        hfr2 _ (by have := (hB e he).1; omega) (by
          by_contra h; rcases (hB e he).2 t ht with hfy1 | hnew
          · exact hDisjY1Blk _ (by omega) (by omega) hfy1
          · omega)
      have hNum2 := hFootAg2 numBase hNum1
      have hDen2 := hFootAg2 denBase hDen1
      have hCLPre : (selCoreLenFillContract w fmt.precision B.eCap eL).pre
          [prevLen, numBase, denBase, B.lenPtr j, dgEListBase (solverG j) B.vCap B.eCap,
            eL.length, B.Lk, Lw, 0, sc2] mem2 := by
        refine ⟨prevLen, numBase, denBase, B.lenPtr j, dgEListBase (solverG j) B.vCap B.eCap,
          B.Lk, Lw, 0, sc2, rfl, hw16, by omega, by omega, by omega,
          by unfold dgEListBase; omega,
          by rcases hPrevDisj with h | h <;> [left; right] <;> omega,
          by rcases hGEnd.2 with h1 | h1 <;> [left; right] <;> (unfold dgEListBase; omega),
          heL2, fun e he => hG.2.2.1 e ((heL_mem e).mp he), fun e he => ?_, hz2,
          by have h1 := Nat.mul_le_mul_left eL.length hSpMono
             dsimp only [F, LwMax] at h1 hsc2Def hSpDef hroom ⊢
             rw [heL_len] at h1 ⊢; rw [hsc2Def]; omega⟩
        have heG : e ∈ a.G.E := (heL_mem e).mp he
        have hNumEnd := (hNum1 e heG).1
        have hDenEnd := (hDen1 e heG).1
        obtain ⟨hNumV1, hDenV1, hDenPos1, hRatio1⟩ := (hfmt4 ▸ hLSF1.2.2.2) e heG
        have hLwPos : 0 < Lw := by
          by_contra h0
          have hLw0 : Lw = 0 := by omega
          rw [hLw0] at hDenPos1
          simp [Num.fixVal, Num.intVal, Num.unsignedVal] at hDenPos1
        have hNumDisj := int_disj_of_foot (lo := B.lenPtr j) (hi := B.embPtr j)
          (hNum1 e heG).2 (hDisjY1Blk (B.lenPtr j) (by omega) (by omega))
          (fun addr h1 h2 => hDisjY1Blk addr (by omega) (by omega)) hLwPos (by omega) (by omega)
        have hDenDisj := int_disj_of_foot (lo := B.lenPtr j) (hi := B.embPtr j)
          (hDen1 e heG).2 (hDisjY1Blk (B.lenPtr j) (by omega) (by omega))
          (fun addr h1 h2 => hDisjY1Blk addr (by omega) (by omega)) hLwPos (by omega) (by omega)
        obtain ⟨hPrevV2, hPrevEq2⟩ := hPrevVal2 e heG
        obtain ⟨q, hqFit, hqEq⟩ := hLenFit e heG
        have hNumV2 : Num.Valid mem2 (numBase + e * Lw) 4 Lw :=
          fun t ht => (hNum2 e heG t ht) ▸ hNumV1 t ht
        have hDenV2 : Num.Valid mem2 (denBase + e * Lw) 4 Lw :=
          fun t ht => (hDen2 e heG t ht) ▸ hDenV1 t ht
        have hNumFixEq : Num.fixVal mem2 (numBase + e * Lw) 4 Lw fmt.precision =
            Num.fixVal mem1 (numBase + e * Lw) 4 Lw fmt.precision := by
          unfold Num.fixVal; rw [Num.intVal_congr (hNum2 e heG)]
        have hDenFixEq : Num.fixVal mem2 (denBase + e * Lw) 4 Lw fmt.precision =
            Num.fixVal mem1 (denBase + e * Lw) 4 Lw fmt.precision := by
          unfold Num.fixVal; rw [Num.intVal_congr (hDen2 e heG)]
        refine ⟨by omega, by omega, by rcases hNumDisj with h | h <;> [left; right] <;> omega,
          by rcases hDenDisj with h | h <;> [left; right] <;> omega,
          hPrevV2, hNumV2, hDenV2, hDenFixEq.symm ▸ hDenPos1,
          by simpa using Num.intVal_fits hPrevV2, q, hqFit, ?_⟩
        simp only [Nat.add_zero]
        rw [hqEq, selCoreLenVal, hNumFixEq, hDenFixEq, hRatio1, hPrevEq2]
      obtain ⟨bCL, hbCL, oCL, st3, cCL, hrCL, hpCL, hcCL⟩ :=
        hCoreLen eL [prevLen, numBase, denBase, B.lenPtr j, dgEListBase (solverG j) B.vCap B.eCap,
          eL.length, B.Lk, Lw, 0, sc2] mem2 st2.pos ω
          (by simp only [List.mem_cons, List.not_mem_nil, or_false]
              rintro v (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)
              all_goals first | exact hNumLt | exact hDenLt | exact hLkW | exact hLwLt | (unfold dgEListBase; omega) | omega)
          hCLPre
      have hpCL' := hpCL
      obtain ⟨_, _, _, _, _, _, _, _, _, hargs3, hsc3Eq, _, hz3, hfr3, _⟩ := hpCL
      simp only [List.cons.injEq] at hargs3
      obtain ⟨rfl, rfl, rfl, rfl, rfl, -, rfl, rfl, -, rfl, -⟩ := hargs3
      set sc3 := oCL.value
      have hShiftEq : (if j < B.d then 0 else pLast) = 0 := ite_eq_left hj
      have hblk3 : SelBlocksDataAt st3.mem B fmt.precision DMid pLast :=
        selCoreLenFill_setLen (pLast := pLast) (Lw := Lw) (hShiftEq.symm ▸ hpCL') hblk2 hjLe (by omega)
          (fun e he => (hPrevVal2 e ((heL_mem e).mp he)).2)
          (fun e he => by
            have heG := (heL_mem e).mp he
            have hN : Num.fixVal mem2 (numBase + e * Lw) 4 Lw fmt.precision =
                Num.fixVal mem1 (numBase + e * Lw) 4 Lw fmt.precision := by
              unfold Num.fixVal; rw [Num.intVal_congr (hNum2 e heG)]
            have hD : Num.fixVal mem2 (denBase + e * Lw) 4 Lw fmt.precision =
                Num.fixVal mem1 (denBase + e * Lw) 4 Lw fmt.precision := by
              unfold Num.fixVal; rw [Num.intVal_congr (hDen2 e heG)]
            rw [hN, hD]; exact ((hfmt4 ▸ hLSF1.2.2.2) e heG).2.2.2)
          (fun e he => hG.2.2.1 e ((heL_mem e).mp he))
          (fun e he => Or.inl ((heL_mem e).mpr he)) (fun _ _ _ => rfl)
          (fun e he hnot => absurd ((heL_mem e).mpr he) hnot)
      have hY1Ag3 : ∀ addr, R.foot handle y1 addr → st3.mem addr = mem2 addr := fun addr ha =>
        hfr3 addr (Or.elim (hft1 addr ha) (fun hfx => by have := (hFootBelow addr hfx).1; omega) (fun hnew => by omega))
          (by by_contra h; exact hDisjY1Blk addr (by omega) (by omega) ha)
      have hrep3 : R.rep handle a y1 st3.mem :=
        (hLocalR handle a y1 mem2 st3.mem fun addr ha => (hY1Ag3 addr ha).symm).1 hrep2
      have hphi3 : R.phi handle y1 st3.mem = R.phi handle y1 mem1 :=
        ((hLocalR handle a y1 mem2 st3.mem fun addr ha => (hY1Ag3 addr ha).symm).2).symm.trans hphi2
      let rg23 := Function.update regs1 23 Lw
      let rg24 := Function.update rg23 24 numBase
      let rg25 := Function.update rg24 25 denBase
      let rg20a := Function.update rg25 20 sc2
      let rg20b := Function.update rg20a 20 sc3
      have sC1 : Runs w p ω
          (.cond (.reg 17)
            (.assign 23 (.load (.bin .add (.reg 7) (.const 4))) ;;
             .assign 24 (.load (.reg 22)) ;;
             .assign 25 (.load (.bin .add (.reg 22) (.const 1))))
            .nop) ⟨mem1, regs1, st1.pos⟩ .normal ⟨mem1, rg25, st1.pos⟩ 17 :=
        runs_cond_iff.mpr ⟨a.G.m, 15, by simp [Expr.eval, r17], by
          simp only [hm0, ↓reduceIte]
          exact runs_seq_iff.mpr (Or.inr ⟨⟨mem1, rg23, st1.pos⟩, 5, 9,
            runs_assign_iff.mpr ⟨Lw, by simp [Expr.eval, BinOp.eval, r7, show 4 < 2 ^ w by omega,
              show scratch + 4 < 2 ^ w by omega, Lw], rfl, rfl, by simp [Expr.size]⟩,
            runs_seq_iff.mpr (Or.inr ⟨⟨mem1, rg24, st1.pos⟩, 3, 5,
              runs_assign_iff.mpr ⟨numBase, by simp [Expr.eval, rg23, r22, numBase], rfl, rfl, by simp [Expr.size]⟩,
              runs_assign_iff.mpr ⟨denBase, by simp [Expr.eval, BinOp.eval, rg24, rg23, r22, hw1,
                show stDesc + 1 < 2 ^ w by omega, denBase], rfl, rfl, by simp [Expr.size]⟩, rfl⟩), rfl⟩),
          by simp [Expr.size]⟩
      have sCopy : Runs w p ω (.call 20 dgCopyProc [.reg 16, .reg 21, .reg 20])
          ⟨mem1, rg25, st1.pos⟩ .normal ⟨mem2, rg20a, st2.pos⟩ (c2 + 4) :=
        runs_call_iff.mpr ⟨[B.fPtr j, fBase, sc1], bCpy, o2, st2, c2,
          by simp [evalArgs, Expr.eval, rg25, rg24, rg23, r16, r21, r20], hbCpy, hr2, rfl, rfl,
          by simp [argsSize, Expr.size]; omega⟩
      have sC2 : Runs w p ω
          (.cond (.reg 17)
            (.call 20 coreLenProc [.reg 4, .reg 24, .reg 25, .reg 14, .reg 18, .reg 17, .reg 5, .reg 23,
              .const 0, .reg 20])
            .nop) ⟨mem2, rg20a, st2.pos⟩ .normal ⟨st3.mem, rg20b, st3.pos⟩ (cCL + 13) :=
        runs_cond_iff.mpr ⟨a.G.m, cCL + 11, by simp [Expr.eval, rg20a, rg25, rg24, rg23, r17], by
          simp only [hm0, ↓reduceIte]
          exact runs_call_iff.mpr ⟨_, bCL, oCL, st3, cCL,
            by simp [evalArgs, Expr.eval, rg20a, rg25, rg24, rg23, r4, r14, r18, r17, r5, heL_len,
              show 0 < 2 ^ w by omega], hbCL, hrCL, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩,
          by simp [Expr.size]; omega⟩
      have hsc3LeMax : sc3 ≤ sc2 + a.G.m * selCoreLenEdgeSpace B.Lk LwMax := by
        have h1 := Nat.mul_le_mul_left a.G.m hSpMono
        dsimp only [sc3, LwMax] at h1 hsc3Eq ⊢; rw [hsc3Eq, heL_len]; omega
      obtain ⟨sc5, cTail, out, y2, rTail, hsc5Lo, hsc5Hi, hrep6, hblk6, hz6, hft6, hfr6, hcTail⟩ :=
        hTail sc3 st3.pos st3.mem rg20b (by simp [rg20b, rg20a, rg25, rg24, rg23, r2])
          (by simp [rg20b, rg20a, rg25, rg24, rg23, r3]) (by simp [rg20b, rg20a, rg25, rg24, rg23, r6])
          (by simp [rg20b, rg20a, rg25, rg24, rg23, r11]) (by simp [rg20b, rg20a, rg25, rg24, rg23, r13])
          (by simp [rg20b, rg20a, rg25, rg24, rg23, r15]) (by simp [rg20b, rg20a, rg25, rg24, rg23, r17])
          (by simp [rg20b, rg20a, rg25, rg24, rg23, r18]) (by simp [rg20b, rg20a, rg25, rg24, rg23, r19])
          (by simp [rg20b]) (by dsimp only [sc3] at hsc3Eq ⊢; rw [hsc3Eq]; omega) hsc3LeMax hz3 hrep3 hphi3 hblk3
          (fun addr hlt hnx hnf hnlen =>
            (hfr3 addr (by omega) (by unfold SelectBlocksLoc.regLen at hnlen; omega)).trans
              ((hfr2 addr (by omega) (by unfold SelectBlocksLoc.regF at hnf; omega)).trans (hfr1 addr hlt hnx)))
      refine ⟨sc5, _, out, y2,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, sC1, runs_seq_iff.mpr (Or.inr ⟨_, _, _, sCopy,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, sC2, rTail, rfl⟩), rfl⟩), rfl⟩),
        by dsimp only [sc3] at hsc3Eq hsc5Lo; rw [hsc3Eq, hsc2Def] at hsc5Lo; omega,
        by dsimp only [F, LwMax] at hsc2Def hsc3LeMax hSpDef hsc5Hi ⊢; rw [hsc2Def] at hsc3LeMax; rw [hSpDef]; omega,
        hrep6, hblk6, hz6, hft6, hfr6, ?_⟩
      dsimp only [dgCopyRefillContract, selCoreLenFillContract] at hc2 hcCL
      simp only [List.getD_cons_zero, List.getD_cons_succ, heL_len] at hc2 hcCL
      dsimp only [F, LwMax] at hc2 hcTail hCostMono ⊢
      have hmulC : a.G.m * (selCoreLenEdgeCost B.Lk Lw + 40) ≤
          a.G.m * (selCoreLenEdgeCost B.Lk (B.Lk + (capExp + sparseCoreReadout2LimbConst) *
            (Nat.log 2 (M + N + 2) + 1)) + 40) := Nat.mul_le_mul_left _ (by omega)
      omega
  obtain ⟨o, out, cost, hrun, sc5, y2, rfl, h1, h2, h3, h4, h5, h6, h7, h8⟩ : ∃ o out cost,
      Runs w p ω (selectFillInteriorLevelBody (op 2) (op 4) dgCopyProc coreLenProc filterProc embCopyProc) s0 o out cost ∧
      ∃ sc5, ∃ y2 : R.τ, o = .returned sc5 ∧ scratch ≤ sc5 ∧ sc5 ≤ scratch + selectFillInteriorLevelSpace a.G.m F.m B.Lk LwMax ∧
        R.rep handle a y2 out.mem ∧ SelBlocksDataAt out.mem B fmt.precision DTarget pLast ∧ ZeroFrom out.mem sc5 ∧
        (∀ addr, R.foot handle y2 addr → R.foot handle x addr ∨ (scratch ≤ addr ∧ addr < sc5)) ∧
        (∀ addr < scratch, ¬ R.foot handle x addr → ¬ B.regF j addr → ¬ B.regLen j addr → ¬ B.regEmb j addr → out.mem addr = mem addr) ∧
        cost + R.phi handle y2 out.mem ≤ selectFillInteriorLevelCost Psc.readout (D.F j).n (D.F j).m F.n F.m a.G.m B.Lk LwMax B.slot + R.phi handle x mem := by
    dsimp only [s0, startState]; unfold selectFillInteriorLevelBody
    refine runs_seq_assign_ex (v := B.d) (by simp [Expr.eval, BinOp.eval, hw1, show metaBase + 1 < 2 ^ w by omega, hdM]) <|
      runs_seq_assign_ex (v := B.d + 1) (by simp [Expr.eval, BinOp.eval, hw1, show B.d + 1 < 2 ^ w by omega]) <|
      runs_seq_assign_ex (v := metaBase + 2) (by simp [Expr.eval, BinOp.eval, show 2 < 2 ^ w by omega, show metaBase + 2 < 2 ^ w by omega]) <|
      runs_seq_assign_ex (v := solverG j) (by simp [Expr.eval, BinOp.eval, show metaBase + 2 + j < 2 ^ w by omega, hgPtrM]) <|
      runs_seq_assign_ex (v := B.vCap) (by simp [Expr.eval, BinOp.eval, show metaBase + 2 + (B.d + 1) < 2 ^ w by omega, show metaBase + 2 + (B.d + 1) + j < 2 ^ w by omega, hvCapM]) <|
      runs_seq_assign_ex (v := B.eCap) (by simp [Expr.eval, BinOp.eval, show 2 < 2 ^ w by omega, show 2 * (B.d + 1) < 2 ^ w by omega, show metaBase + 2 + 2 * (B.d + 1) < 2 ^ w by omega, show metaBase + 2 + 2 * (B.d + 1) + j < 2 ^ w by omega, heCapM]) <|
      runs_seq_assign_ex (v := B.lenPtr j) (by simp [Expr.eval, BinOp.eval, show 4 < 2 ^ w by omega, show 4 * (B.d + 1) < 2 ^ w by omega, show metaBase + 2 + 4 * (B.d + 1) < 2 ^ w by omega, show metaBase + 2 + 4 * (B.d + 1) + j < 2 ^ w by omega, hlenM]) <|
      runs_seq_assign_ex (v := B.embPtr j) (by simp [Expr.eval, BinOp.eval, show 5 < 2 ^ w by omega, show 5 * (B.d + 1) < 2 ^ w by omega, show metaBase + 2 + 5 * (B.d + 1) < 2 ^ w by omega, show metaBase + 2 + 5 * (B.d + 1) + j < 2 ^ w by omega, hembM]) <|
      runs_seq_assign_ex (v := B.fPtr j) (by simp [Expr.eval, BinOp.eval, show 6 < 2 ^ w by omega, show 6 * (B.d + 1) < 2 ^ w by omega, show metaBase + 2 + 6 * (B.d + 1) < 2 ^ w by omega, show metaBase + 2 + 6 * (B.d + 1) + j < 2 ^ w by omega, hfM]) <|
      runs_seq_assign_ex (v := a.G.m) (by simp [Expr.eval, BinOp.eval, show 3 < 2 ^ w by omega, show solverG j + 3 < 2 ^ w by omega, hGM]) <|
      runs_seq_assign_ex (v := dgEListBase (solverG j) B.vCap B.eCap) (by simp [Expr.eval, BinOp.eval, show 4 < 2 ^ w by omega, show 7 < 2 ^ w by omega, show solverG j + 4 < 2 ^ w by omega, show 7 * B.vCap < 2 ^ w by omega, show solverG j + 4 + 7 * B.vCap < 2 ^ w by omega, show solverG j + 4 + 7 * B.vCap + B.eCap = dgEListBase (solverG j) B.vCap B.eCap from rfl, show dgEListBase (solverG j) B.vCap B.eCap < 2 ^ w by unfold dgEListBase; omega]) <|
      runs_seq_assign_ex (v := dgEPresBase (B.fPtr j) B.vCap) (by simp [Expr.eval, BinOp.eval, show 4 < 2 ^ w by omega, show 7 < 2 ^ w by omega, show B.fPtr j + 4 < 2 ^ w by omega, show 7 * B.vCap < 2 ^ w by omega, show B.fPtr j + 4 + 7 * B.vCap = dgEPresBase (B.fPtr j) B.vCap from rfl, show dgEPresBase (B.fPtr j) B.vCap < 2 ^ w by unfold dgEPresBase; omega]) <|
      runs_seq_call_ex (by simp [evalArgs, Expr.eval]) hb2 hr1 <|
      runs_seq_assign_ex (v := fBase) (by simp [Expr.eval, BinOp.eval, hw1, show scratch + 1 < 2 ^ w by omega, mem1, fBase]) <|
      runs_seq_assign_ex (v := stDesc) (by simp [Expr.eval, BinOp.eval, show 3 < 2 ^ w by omega, show scratch + 3 < 2 ^ w by omega, mem1, stDesc]) <|
      (fun ⟨sc5, cMid, out, y2, rMid, hsc5Lo, hsc5Hi, hrepOut, hblkOut, hzOut, hftOut, hfrOut, hcMid⟩ =>
        ⟨.returned sc5, out, cMid, rMid, sc5, y2, rfl, hsc5Lo, hsc5Hi, hrepOut, hblkOut, hzOut, hftOut, hfrOut, by
          simp only [selectFillInteriorLevelCost, Expr.size, argsSize]
          change c1 + R.phi handle y1 mem1 ≤ Psc.readout + R.phi handle x mem at hcost1; omega⟩)
        (hAfterOp2 _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
          (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp [sc1]) (by simp) (by simp))
  exact ⟨sc5, cost, out, y2, hrun, h1, h2, h3, h4, h5, h6, h7, h8⟩

end MinCostFlow.MinRatio
