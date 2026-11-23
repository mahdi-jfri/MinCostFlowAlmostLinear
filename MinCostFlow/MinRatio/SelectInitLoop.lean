module

public import MinCostFlow.MinRatio.SelectInteriorFill
public import MinCostFlow.MinRatio.SelectInitFinalize
public import MinCostFlow.MinRatio.SelectInitRepLemmas
import WordRAM.Tactic

/-!
# Interior-level initialization loop for the select region (`SelectInitLoop`)

Verifies `selectInitInteriorLoopBody`, which loops across interior levels `cur .. d - 1`,
reading `(handle, branch)` from `levelTable` and `prevLen` from `SolverLevelMetaAt` (`lvlMeta + j`),
and calling `selectFillInteriorLevelBody` to populate `B.fPtr j`, `B.lenPtr j` (`shift = 0`,
`chainLen ℓ (j + 1)`), and `B.embPtr j` while threading `Rcore.rep` and `Rcore.phi` inside
`solverStateRepFull` and preserving `SolverLevelCapsInv`, `SelectMetaTableAt`, and `SelectHeapAt`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine Num DynSpanner.Program SparseCore.Program

/-- Populate interior levels `cur .. d - 1` of the select blocks by calling `fillIntProc`.
Arguments: `[metaBase, cur, d, levelTable, lvlMeta, Lk, slot, scratch]` (`reg 0..7`).
Returns the new scratch pointer. -/
def selectInitInteriorLoopBody (loopProc fillIntProc : ℕ) : Stmt :=
  .cond (.bin .lt (.reg 1) (.reg 2))
    (.assign 8 (.load (.bin .add (.reg 3) (.reg 1))) ;;
     .assign 9 (.load (.bin .add (.bin .add (.reg 3) (.bin .add (.reg 2) (.const 1))) (.reg 1))) ;;
     .assign 10 (.load (.bin .add (.reg 4) (.reg 1))) ;;
     .call 11 fillIntProc [.reg 0, .reg 1, .reg 8, .reg 9, .reg 10, .reg 5, .reg 6, .reg 7] ;;
     .call 12 loopProc [.reg 0, .bin .add (.reg 1) (.const 1), .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 11] ;;
     .ret (.reg 12))
    (.ret (.reg 7))

theorem selectInitInteriorLoopBody_noRand (loopProc fillIntProc : ℕ) :
    (selectInitInteriorLoopBody loopProc fillIntProc).NoRand := by
  simp [selectInitInteriorLoopBody, Stmt.NoRand]

/-- Scratch space bound for `selectInitInteriorLoopBody` across levels `cur .. P.d - 1`. -/
noncomputable def selectInitInteriorLoopSpace {T : SparseCoreRestartTool} {P : ChainParams}
    (C : ChainState T P) (cur L capExp : ℕ) : ℕ :=
  (Finset.Ico cur P.d).sum fun j =>
    let LwMax := L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (C.lvlM j + C.N₀ + 2) + 1)
    selectFillInteriorLevelSpace (C.G j).m (C.toTreeChain.activeLSF j).F.F.m L LwMax

/-- Step cost bound for `selectInitInteriorLoopBody` across levels `cur .. P.d - 1` when starting
from empty forests (`dgEmptyGraph`) at levels `≥ cur`. -/
noncomputable def selectInitInteriorLoopCost {T : SparseCoreRestartTool} {P : ChainParams}
    (C : ChainState T P) (readoutCost cur L capExp slot : ℕ) : ℕ :=
  (Finset.Ico cur P.d).sum (fun j =>
    let LwMax := L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (C.lvlM j + C.N₀ + 2) + 1)
    selectFillInteriorLevelCost readoutCost 0 0 (C.toTreeChain.activeLSF j).F.F.n
      (C.toTreeChain.activeLSF j).F.F.m (C.G j).m L LwMax slot + 60) + 10

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine Num DynSpanner.Program SparseCore.Program

private lemma reg_in_blocks {B : SelectBlocksLoc} {j a : ℕ} (hj : j ≤ B.d)
    (h : B.regF j a ∨ B.regLen j a ∨ B.regEmb j a) : B.base ≤ a ∧ a < B.endAddr := by
  have h1 : B.base ≤ B.fPtr j := by unfold SelectBlocksLoc.fPtr; omega
  have h2 := B.blk_le_last hj
  have h3 : B.lastGPtr ≤ B.endAddr := by unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr; omega
  unfold SelectBlocksLoc.levelSize at h2
  rcases h with h | h | h
  · unfold SelectBlocksLoc.regF SelectBlocksLoc.phiPtr at h; omega
  · unfold SelectBlocksLoc.regLen SelectBlocksLoc.embPtr SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr at h; omega
  · unfold SelectBlocksLoc.regEmb SelectBlocksLoc.embPtr SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr SelectBlocksLoc.levelSize at h; omega

private lemma selectMlocOf_congr_loop {B : SelectBlocksLoc} {metaBase pLast : ℕ}
    {g₁ g₂ : ℕ → ℕ} (h : ∀ j < B.d, g₁ j = g₂ j) :
    selectMlocOf B metaBase g₁ pLast = selectMlocOf B metaBase g₂ pLast := by
  unfold selectMlocOf; congr 1
  · funext j; by_cases hj : j < B.d <;> simp [hj]; exact h j hj
  · funext j; by_cases hj : j < B.d <;> by_cases hj1 : j + 1 < B.d <;> simp [hj, hj1] <;> exact h (j + 1) hj1

set_option maxHeartbeats 1200000 in
/-- `selectInitInteriorLoopBody` populates `F`, `E`, `len` (`shift = 0`, `chainLen ℓ (j + 1)`),
`coreE`, and `emb` for all interior levels `cur .. cfg.P.d - 1`, preserving `solverStateRepFull`,
`SolverLevelCapsInv`, `SelectMetaTableAt`, and `SelectHeapAt`, while telescoping `Rcore.phi`. -/
theorem selectInitInteriorLoop_runs
    {w L P m V psi k epsExp drainUnit unit toolMul treeMul : ℕ}
    {depth capExp vCap eCap sb metaBase pLast cur scratch pos : ℕ}
    {loopProc fillIntProc dgCopyProc coreLenProc filterProc embCopyProc : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {κ : ℝ} {G : MGraph}
    {initialGraph : MGraph} {Psc : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {op : ℕ → ℕ} {ω : ℕ → Bool}
    {root : ℕ} {model : Alg2State cfg}
    {tokFull : (solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul Rcore).τ}
    {loc : SelectHeapLoc} {B : SelectBlocksLoc} {D : SelBlocksData} {mem : ℕ → ℕ}
    (hfmt4 : fmt.limbBits = 4) (hfmtP : fmt.precision = P) (hlocalCore : Rcore.Local)
    (hw16 : 16 < 2 ^ w) (hLkW : L < 2 ^ w) (hSlotW : B.slot < 2 ^ w) (hkW : cfg.P.k < 2 ^ w)
    (hcurLe : cur ≤ cfg.P.d)
    (hreg : SelectRegion sb loc B metaBase)
    (hBd : B.d = cfg.P.d) (hBv : B.vCap = vCap) (hBe : B.eCap = eCap) (hBLk : B.Lk = L)
    (hrepFull : (solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul
      Rcore).rep root model tokFull mem)
    (hFootSc : ∀ a, (solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul
      Rcore).foot root tokFull a → a < scratch)
    (hFootDisj : ∀ a, sb ≤ a → a < B.endAddr →
      ¬ (solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul Rcore).foot
        root tokFull a)
    (hCoreBelow : ∀ j, cur ≤ j → j < cfg.P.d →
      ∀ a, Rcore.foot (tokFull.1.1.coreHandle j) (tokFull.1.1.coreTok j) a → a < sb)
    (hMetaBelow : tokFull.1.1.handle + 18 + 2 * (cfg.P.d + 1) ≤ sb ∧
      solverLevelMetaAddr tokFull.1.1.table cfg.P.d + 2 * cfg.P.d ≤ sb ∧
      ∀ j < cfg.P.d,
        mem (solverLevelMetaAddr tokFull.1.1.table cfg.P.d + j) + eCap * L ≤ sb ∧
        solverLevelG tokFull.1.1 mem j + dynGraphSize vCap eCap ≤ sb)
    (hEndSc : B.endAddr ≤ scratch)
    (hcaps : SolverLevelCapsInv P V vCap eCap model tokFull.1.1 mem)
    (htab : SelectMetaTableAt mem (selectMlocOf B metaBase (solverLevelG tokFull.1.1 mem) pLast))
    (hHeap : SelectHeapAt mem loc 4 0)
    (hblk : SelBlocksDataAt mem B P D pLast)
    (hDEmpty : ∀ j, cur ≤ j → j < cfg.P.d → D.F j = dgEmptyGraph)
    (hScIn : ∀ j, cur ≤ j → j < cfg.P.d →
      SparseCoreOrdInput cfg.T cfg.P.k (model.chain.lvlM j) model.chain.N₀
        (model.chain.scState j) (model.chain.G j) (model.chain.levelOrd j)
        (model.chain.updCount j))
    (hBrLt : ∀ j, cur ≤ j → j < cfg.P.d → model.chain.bran j < cfg.P.k)
    (hFV : ∀ j, cur ≤ j → j < cfg.P.d →
      ∀ v ∈ (model.chain.toTreeChain.activeLSF j).F.F.V, v < vCap)
    (hFE : ∀ j, cur ≤ j → j < cfg.P.d →
      ∀ e ∈ (model.chain.toTreeChain.activeLSF j).F.F.E, e < eCap)
    (hLenFit : ∀ j, cur ≤ j → j < cfg.P.d → ∀ e ∈ (model.chain.G j).E,
      ∃ q : ℤ, Num.Fits 4 L q ∧
        (q : ℝ) / (2 : ℝ) ^ P = model.chain.toTreeChain.chainLen model.chain.ℓ (j + 1) e)
    (hEmbSlot : ∀ j, cur ≤ j → j < cfg.P.d →
      ∀ e ∈ (model.chain.toTreeChain.activeCore j).E,
        (mWalkEncode (model.chain.toTreeChain.activeEmb j e)).length ≤ B.slot)
    (hpLoop : p.procs[loopProc]? = some (selectInitInteriorLoopBody loopProc fillIntProc))
    (hpFillInt : p.procs[fillIntProc]? =
      some (selectFillInteriorLevelBody (op 2) (op 4) dgCopyProc coreLenProc filterProc embCopyProc))
    (hFootAt : ∀ j, cur ≤ j → j < cfg.P.d →
      SparseCoreReadoutFootAt fmt L depth cfg.T initialGraph cfg.P.k
        (model.chain.lvlM j) model.chain.N₀ vCap eCap capExp Psc allocation Rcore p op)
    (hDgCopy : ∀ j, cur ≤ j → j < cfg.P.d → ∀ vcF ecF,
      MeetsContract w p dgCopyProc
        (dgCopyRefillContract w vCap eCap vcF ecF dgEmptyGraph
          (model.chain.toTreeChain.activeLSF j).F.F))
    (hCoreLen : ∀ eL : List ℕ, MeetsContract w p coreLenProc (selCoreLenFillContract w P eCap eL))
    (hFilter : ∀ eL : List ℕ, MeetsContract w p filterProc (selFilterAbsentContract w eL))
    (hEmbCopy : ∀ j, cur ≤ j → j < cfg.P.d → ∀ eL : List ℕ,
      MeetsContract w p embCopyProc (selEmbCopyContract w eL (model.chain.toTreeChain.activeEmb j)))
    (hz : ZeroFrom mem scratch)
    (hroom : scratch + selectInitInteriorLoopSpace model.chain cur L capExp < 2 ^ w) :
    let Rfull := solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul Rcore
    let C := model.chain.toTreeChain
    ∃ scOut cost out tokFull',
      Runs w p ω (selectInitInteriorLoopBody loopProc fillIntProc)
        (startState [metaBase, cur, cfg.P.d, tokFull.1.1.handle + 18,
          solverLevelMetaAddr tokFull.1.1.table cfg.P.d, L, B.slot, scratch] mem pos)
        (.returned scOut) out cost ∧
      scratch ≤ scOut ∧
      scOut ≤ scratch + selectInitInteriorLoopSpace model.chain cur L capExp ∧
      Rfull.rep root model tokFull' out.mem ∧
      tokFull'.1.1.table = tokFull.1.1.table ∧
      tokFull'.1.1.handle = tokFull.1.1.handle ∧
      tokFull'.1.1.termHandle = tokFull.1.1.termHandle ∧
      tokFull'.1.1.termTok = tokFull.1.1.termTok ∧
      tokFull'.1.1.vcLast = tokFull.1.1.vcLast ∧
      tokFull'.1.1.ecLast = tokFull.1.1.ecLast ∧
      tokFull'.1.1.tree = tokFull.1.1.tree ∧ tokFull'.1.1.trees = tokFull.1.1.trees ∧
      tokFull'.1.1.edgeRecords = tokFull.1.1.edgeRecords ∧
      (∀ a, Rfull.foot root tokFull' a → Rfull.foot root tokFull a ∨ (scratch ≤ a ∧ a < scOut)) ∧
      (∀ a, tokFull.1.1.owned a → tokFull'.1.1.owned a) ∧
      (∀ a < scratch, tokFull'.1.1.tag a = tokFull.1.1.tag a) ∧
      (∀ a, tokFull.1.1.tag a ≠ 0 → tokFull'.1.1.tag a = tokFull.1.1.tag a) ∧
      SolverLevelCapsInv P V vCap eCap model tokFull'.1.1 out.mem ∧
      SelectMetaTableAt out.mem (selectMlocOf B metaBase (solverLevelG tokFull'.1.1 out.mem) pLast) ∧
      SelectHeapAt out.mem loc 4 0 ∧
      SelBlocksDataAt out.mem B P
        { D with
          F := fun j => if cur ≤ j ∧ j < cfg.P.d then (C.activeLSF j).F.F else D.F j
          E := fun j => if cur ≤ j ∧ j < cfg.P.d then (C.G j).E else D.E j
          len := fun j => if cur ≤ j ∧ j < cfg.P.d then C.chainLen model.chain.ℓ (j + 1) else D.len j
          coreE := fun j => if cur ≤ j ∧ j < cfg.P.d then (C.activeCore j).E else D.coreE j
          emb := fun j => if cur ≤ j ∧ j < cfg.P.d then C.activeEmb j else D.emb j } pLast ∧
      ZeroFrom out.mem scOut ∧
      (∀ a < sb, ¬ (∃ j, cur ≤ j ∧ j < cfg.P.d ∧
          Rcore.foot (tokFull.1.1.coreHandle j) (tokFull.1.1.coreTok j) a) →
        out.mem a = mem a) ∧
      cost + Rfull.phi root tokFull' out.mem ≤
        selectInitInteriorLoopCost model.chain Psc.readout cur L capExp B.slot +
          Rfull.phi root tokFull mem := by
  -- Proof by induction on `n = cfg.P.d - cur`
  intro Rfull C
  have hInd : ∀ n cur scratch pos (tokFull : Rfull.τ) (D : SelBlocksData) (mem : ℕ → ℕ),
      cfg.P.d - cur = n → cur ≤ cfg.P.d →
      Rfull.rep root model tokFull mem →
      (∀ a, Rfull.foot root tokFull a → a < scratch) →
      (∀ a, sb ≤ a → a < B.endAddr → ¬ Rfull.foot root tokFull a) →
      (∀ j, cur ≤ j → j < cfg.P.d →
        ∀ a, Rcore.foot (tokFull.1.1.coreHandle j) (tokFull.1.1.coreTok j) a → a < sb) →
      (tokFull.1.1.handle + 18 + 2 * (cfg.P.d + 1) ≤ sb ∧
        solverLevelMetaAddr tokFull.1.1.table cfg.P.d + 2 * cfg.P.d ≤ sb ∧
        ∀ j < cfg.P.d,
          mem (solverLevelMetaAddr tokFull.1.1.table cfg.P.d + j) + eCap * L ≤ sb ∧
          solverLevelG tokFull.1.1 mem j + dynGraphSize vCap eCap ≤ sb) →
      B.endAddr ≤ scratch →
      SolverLevelCapsInv P V vCap eCap model tokFull.1.1 mem →
      SelectMetaTableAt mem (selectMlocOf B metaBase (solverLevelG tokFull.1.1 mem) pLast) →
      SelectHeapAt mem loc 4 0 →
      SelBlocksDataAt mem B P D pLast →
      (∀ j, cur ≤ j → j < cfg.P.d → D.F j = dgEmptyGraph) →
      (∀ j, cur ≤ j → j < cfg.P.d →
        SparseCoreOrdInput cfg.T cfg.P.k (model.chain.lvlM j) model.chain.N₀
          (model.chain.scState j) (model.chain.G j) (model.chain.levelOrd j)
          (model.chain.updCount j)) →
      (∀ j, cur ≤ j → j < cfg.P.d → model.chain.bran j < cfg.P.k) →
      (∀ j, cur ≤ j → j < cfg.P.d → ∀ v ∈ (C.activeLSF j).F.F.V, v < vCap) →
      (∀ j, cur ≤ j → j < cfg.P.d → ∀ e ∈ (C.activeLSF j).F.F.E, e < eCap) →
      (∀ j, cur ≤ j → j < cfg.P.d → ∀ e ∈ (model.chain.G j).E,
        ∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ P = C.chainLen model.chain.ℓ (j + 1) e) →
      (∀ j, cur ≤ j → j < cfg.P.d → ∀ e ∈ (C.activeCore j).E, (mWalkEncode (C.activeEmb j e)).length ≤ B.slot) →
      (∀ j, cur ≤ j → j < cfg.P.d →
        SparseCoreReadoutFootAt fmt L depth cfg.T initialGraph cfg.P.k
          (model.chain.lvlM j) model.chain.N₀ vCap eCap capExp Psc allocation Rcore p op) →
      (∀ j, cur ≤ j → j < cfg.P.d → ∀ vcF ecF,
        MeetsContract w p dgCopyProc (dgCopyRefillContract w vCap eCap vcF ecF dgEmptyGraph (C.activeLSF j).F.F)) →
      (∀ j, cur ≤ j → j < cfg.P.d → ∀ eL : List ℕ,
        MeetsContract w p embCopyProc (selEmbCopyContract w eL (C.activeEmb j))) →
      ZeroFrom mem scratch →
      scratch + selectInitInteriorLoopSpace model.chain cur L capExp < 2 ^ w →
      ∃ scOut cost out tokFull',
        Runs w p ω (selectInitInteriorLoopBody loopProc fillIntProc)
          (startState [metaBase, cur, cfg.P.d, tokFull.1.1.handle + 18,
            solverLevelMetaAddr tokFull.1.1.table cfg.P.d, L, B.slot, scratch] mem pos)
          (.returned scOut) out cost ∧
        scratch ≤ scOut ∧ scOut ≤ scratch + selectInitInteriorLoopSpace model.chain cur L capExp ∧
        Rfull.rep root model tokFull' out.mem ∧ tokFull'.1.1.table = tokFull.1.1.table ∧
        tokFull'.1.1.handle = tokFull.1.1.handle ∧ tokFull'.1.1.termHandle = tokFull.1.1.termHandle ∧
        tokFull'.1.1.termTok = tokFull.1.1.termTok ∧ tokFull'.1.1.vcLast = tokFull.1.1.vcLast ∧
        tokFull'.1.1.ecLast = tokFull.1.1.ecLast ∧
        tokFull'.1.1.tree = tokFull.1.1.tree ∧ tokFull'.1.1.trees = tokFull.1.1.trees ∧
        tokFull'.1.1.edgeRecords = tokFull.1.1.edgeRecords ∧
        (∀ a, Rfull.foot root tokFull' a → Rfull.foot root tokFull a ∨ (scratch ≤ a ∧ a < scOut)) ∧
        (∀ a, tokFull.1.1.owned a → tokFull'.1.1.owned a) ∧
        (∀ a < scratch, tokFull'.1.1.tag a = tokFull.1.1.tag a) ∧
        (∀ a, tokFull.1.1.tag a ≠ 0 → tokFull'.1.1.tag a = tokFull.1.1.tag a) ∧
        SolverLevelCapsInv P V vCap eCap model tokFull'.1.1 out.mem ∧
        SelectMetaTableAt out.mem (selectMlocOf B metaBase (solverLevelG tokFull'.1.1 out.mem) pLast) ∧
        SelectHeapAt out.mem loc 4 0 ∧
        SelBlocksDataAt out.mem B P
          { D with
            F := fun j => if cur ≤ j ∧ j < cfg.P.d then (C.activeLSF j).F.F else D.F j
            E := fun j => if cur ≤ j ∧ j < cfg.P.d then (C.G j).E else D.E j
            len := fun j => if cur ≤ j ∧ j < cfg.P.d then C.chainLen model.chain.ℓ (j + 1) else D.len j
            coreE := fun j => if cur ≤ j ∧ j < cfg.P.d then (C.activeCore j).E else D.coreE j
            emb := fun j => if cur ≤ j ∧ j < cfg.P.d then C.activeEmb j else D.emb j } pLast ∧
        ZeroFrom out.mem scOut ∧
        (∀ a < sb, ¬ (∃ j, cur ≤ j ∧ j < cfg.P.d ∧
            Rcore.foot (tokFull.1.1.coreHandle j) (tokFull.1.1.coreTok j) a) →
          out.mem a = mem a) ∧
        cost + Rfull.phi root tokFull' out.mem ≤
          selectInitInteriorLoopCost model.chain Psc.readout cur L capExp B.slot +
            Rfull.phi root tokFull mem := by
    intro n
    induction n with
    | zero =>
      intro cur scratch pos tokFull D mem hsub hcurLe hrepF hFootSc hFootDisj _ _ _ hcaps htab hHeap hblk _ _ _ _ _ _ _ _ _ _ hz hroom
      have hcurEq : cur = cfg.P.d := by omega
      have hSp0 : selectInitInteriorLoopSpace model.chain cur L capExp = 0 := by
        unfold selectInitInteriorLoopSpace; rw [hcurEq, Finset.Ico_self, Finset.sum_empty]
      have hNo : ∀ j, ¬ (cur ≤ j ∧ j < cfg.P.d) := fun j h => by omega
      have hDEq : ({ D with
            F := fun j => if cur ≤ j ∧ j < cfg.P.d then (C.activeLSF j).F.F else D.F j
            E := fun j => if cur ≤ j ∧ j < cfg.P.d then (C.G j).E else D.E j
            len := fun j => if cur ≤ j ∧ j < cfg.P.d then C.chainLen model.chain.ℓ (j + 1) else D.len j
            coreE := fun j => if cur ≤ j ∧ j < cfg.P.d then (C.activeCore j).E else D.coreE j
            emb := fun j => if cur ≤ j ∧ j < cfg.P.d then C.activeEmb j else D.emb j } : SelBlocksData) = D := by
        cases D; simp [hNo]
      let s0 := startState [metaBase, cur, cfg.P.d, tokFull.1.1.handle + 18,
        solverLevelMetaAddr tokFull.1.1.table cfg.P.d, L, B.slot, scratch] mem pos
      have hRun : Runs w p ω (selectInitInteriorLoopBody loopProc fillIntProc) s0
          (.returned scratch) s0 6 := by
        unfold selectInitInteriorLoopBody
        refine runs_cond_iff.mpr ⟨0, 2, by simp [Expr.eval, BinOp.eval, s0, startState, hcurEq], ?_, by simp [Expr.size]⟩
        exact runs_ret_iff.mpr ⟨scratch, by simp [Expr.eval, s0, startState], rfl, rfl, rfl⟩
      refine ⟨scratch, 6, s0, tokFull, hRun, le_refl _, by omega, hrepF, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        fun _ ha => Or.inl ha, fun _ ha => ha, fun _ _ => rfl, fun _ _ => rfl, hcaps, htab, hHeap,
        hDEq.symm ▸ hblk, hz, fun _ _ _ => rfl, ?_⟩
      simp only [s0, startState]; unfold selectInitInteriorLoopCost; omega
    | succ n ih =>
      intro cur scratch pos tokFull D mem hsub hcurLe hrepF hFootSc hFootDisj hCoreBelow
        hMetaBelow hEndSc hcaps htab hHeap hblk hDEmpty hScIn hBrLt hFV hFE hLenFit hEmbSlot
        hFootAt hDgCopy hEmbCopy hz hroom
      rcases tokFull with ⟨⟨tok, fwdG⟩, ⟨rcG, tcG⟩⟩
      dsimp only at hMetaBelow hcaps hCoreBelow
      have hcurLt : cur < cfg.P.d := by omega
      have hcurB : cur < B.d := by omega
      have hsbLeBase : sb ≤ B.base := by
        have := hreg.1; have := hreg.2.1; have := hreg.2.2.1; have := hreg.2.2.2.1
        have : loc.hb ≤ loc.endAddr := by rw [loc.endAddr_eq]; omega
        omega
      have hBaseLeEnd : B.base ≤ B.endAddr := by rw [B.endAddr_eq]; omega
      have hMetaEnd : metaBase + selectLevelMetaSize B.d ≤ B.base := by
        have := hreg.2.2.2.1; omega
      have hrep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem := hrepF.1.1
      have htags := hrep0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      obtain ⟨hOwn, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, t21⟩ := htags
      have hMC := (solverLevelCapsInv_iff_metaCaps.mp hcaps).2.2.2.2.2 cur hcurLt
      set hnd := tok.coreHandle cur
      set br := model.chain.bran cur
      set prevLen := mem (solverLevelMetaAddr tok.table cfg.P.d + cur)
      have hCoreCur := hrep0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 cur hcurLt
      have hSpSplit : selectInitInteriorLoopSpace model.chain cur L capExp =
          selectFillInteriorLevelSpace (model.chain.G cur).m (C.activeLSF cur).F.F.m L
            (L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (model.chain.lvlM cur + model.chain.N₀ + 2) + 1)) +
          selectInitInteriorLoopSpace model.chain (cur + 1) L capExp := by
        unfold selectInitInteriorLoopSpace
        rw [Finset.sum_eq_sum_Ico_succ_bot hcurLt]
      have hCostSplit : selectInitInteriorLoopCost model.chain Psc.readout cur L capExp B.slot =
          (selectFillInteriorLevelCost Psc.readout 0 0 (C.activeLSF cur).F.F.n
            (C.activeLSF cur).F.F.m (model.chain.G cur).m L
            (L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (model.chain.lvlM cur + model.chain.N₀ + 2) + 1))
            B.slot + 60) +
          selectInitInteriorLoopCost model.chain Psc.readout (cur + 1) L capExp B.slot := by
        dsimp only [C, selectInitInteriorLoopCost]
        rw [Finset.sum_eq_sum_Ico_succ_bot hcurLt]; omega
      have hDFCur : D.F cur = dgEmptyGraph := hDEmpty cur (le_refl _) hcurLt
      have hHndW : hnd < 2 ^ w := by
        have := hFootSc hnd (Or.inl (hcaps.1.2.1 cur hcurLt)); omega
      have hprevEnd : prevLen + eCap * L ≤ sb := (hMetaBelow.2.2 cur hcurLt).1
      have hGEnd : solverLevelG tok mem cur + dynGraphSize vCap eCap ≤ sb := (hMetaBelow.2.2 cur hcurLt).2
      have hDisjG : ∀ a, solverLevelG tok mem cur ≤ a →
          a < solverLevelG tok mem cur + dynGraphSize B.vCap B.eCap →
          ¬ Rcore.foot hnd (tok.coreTok cur) a := fun a ha1 ha2 hcf => by
        rw [hBv, hBe] at ha2
        have h1 := hMC.2.2.2.2 a ha1 ha2
        have h2 := t21 cur hcurLt a hcf
        split_ifs at h1 <;> omega
      have hDisjPrev : ∀ a, prevLen ≤ a → a < prevLen + B.eCap * B.Lk →
          ¬ Rcore.foot hnd (tok.coreTok cur) a := fun a ha1 ha2 hcf => by
        rw [hBe, hBLk] at ha2
        have h1 := hMC.2.2.2.1 a ha1 ha2
        have h2 := t21 cur hcurLt a hcf
        omega
      have hFPos : B.base ≤ B.fPtr cur := by unfold SelectBlocksLoc.fPtr; omega
      have hLenPos : B.base ≤ B.lenPtr cur := by unfold SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr SelectBlocksLoc.fPtr; omega
      have hActLSF : (C.activeLSF cur) = cfg.T.lsfs (model.chain.scState cur) br := by
        simp [C, TreeChain.activeLSF, ChainState.toTreeChain, hcurLt, br]
      have hActEmb : C.activeEmb cur = cfg.T.emb (model.chain.scState cur) br := by
        simp [C, TreeChain.activeEmb, ChainState.toTreeChain, hcurLt, br]
      have hActCore : C.activeCore cur = coreGraph (model.chain.G cur) (cfg.T.lsfs (model.chain.scState cur) br) := by
        unfold TreeChain.activeCore; rw [hActLSF]; rfl
      have hChainLenSucc : ∀ e, C.chainLen model.chain.ℓ (cur + 1) e =
          (cfg.T.lsfs (model.chain.scState cur) br).wstr e * C.chainLen model.chain.ℓ cur e := fun e => by
        rw [TreeChain.chainLen, hActLSF]; rfl
      obtain ⟨sc1, cFill, st1, y1, hrFill, hsc1Lo, hsc1Hi, hrepY1, hblk1, hz1, hftY1, hfr1, hcFill⟩ :=
        selectFillInteriorLevel_runs (w := w) (depth := depth) (k := cfg.P.k)
          (M := model.chain.lvlM cur) (N := model.chain.N₀) (capExp := capExp)
          (j := cur) (pLast := pLast) (handle := hnd) (branch := br) (prevLen := prevLen)
          (scratch := scratch) (pos := pos)
          (dgCopyProc := dgCopyProc) (coreLenProc := coreLenProc)
          (filterProc := filterProc) (embCopyProc := embCopyProc)
          (fmt := fmt) (tool := cfg.T) (initialGraph := initialGraph)
          (Psc := Psc) (allocation := allocation) (R := Rcore) (p := p) (op := op) (ω := ω)
          (B := B) (metaBase := metaBase) (solverG := solverLevelG tok mem) (D := D)
          (a := chainLevelOrdAbs model.chain cur) (x := tok.coreTok cur)
          (prevVal := C.chainLen model.chain.ℓ cur) (mem := mem)
          hfmt4 hlocalCore hw16 (hBLk ▸ hLkW) hSlotW hcurB (hBrLt cur (le_refl _) hcurLt) hkW hHndW
          htab (hfmtP.symm ▸ hblk) hMetaEnd hEndSc
          (by rw [hBv, hBe]; exact hMC.1)
          (by rw [hBv, hBe]; exact ⟨by omega, Or.inl (by omega)⟩) hCoreCur.2.2
          (hScIn cur (le_refl _) hcurLt)
          (fun a ha => have hlt := lt_of_lt_of_le (hCoreBelow cur (le_refl _) hcurLt a ha) hsbLeBase; ⟨by omega, Or.inl hlt⟩)
          hDisjG hDisjPrev (by rw [hBe, hBLk]; omega) (Or.inl (by rw [hBe, hBLk]; omega))
          (Or.inl (by rw [hBe, hBLk]; omega)) (by rw [hfmtP, hBLk]; exact hMC.2.1)
          (by dsimp only [chainLevelOrdAbs]; rw [hBv, ← hActLSF]; exact hFV cur (le_refl _) hcurLt)
          (by dsimp only [chainLevelOrdAbs]; rw [hBe, ← hActLSF]; exact hFE cur (le_refl _) hcurLt)
          (fun e he => by
            dsimp only [chainLevelOrdAbs] at he ⊢
            obtain ⟨q, hqF, hqEq⟩ := hLenFit cur (le_refl _) hcurLt e he
            exact ⟨q, hBLk.symm ▸ hqF, by rw [hfmtP, hqEq, hChainLenSucc]⟩)
          (fun e he => by
            dsimp only [chainLevelOrdAbs] at he ⊢
            rw [← hActEmb]; exact hEmbSlot cur (le_refl _) hcurLt e (hActCore.symm ▸ he))
          (by rw [hBLk, hBv, hBe]; exact hFootAt cur (le_refl _) hcurLt)
          (fun vcF ecF => by
            dsimp only [chainLevelOrdAbs]; rw [hBv, hBe, hDFCur, ← hActLSF]; exact hDgCopy cur (le_refl _) hcurLt vcF ecF)
          (fun eL => by rw [hfmtP, hBe]; exact hCoreLen eL) hFilter
          (fun eL => by dsimp only [chainLevelOrdAbs]; rw [← hActEmb]; exact hEmbCopy cur (le_refl _) hcurLt eL)
          hz (by dsimp only [chainLevelOrdAbs]; rw [hBLk, ← hActLSF]; omega)
      dsimp only [chainLevelOrdAbs] at hsc1Hi hcFill
      -- Update `tok` -> `tok1` via `solverStateRep_update_coreTok`
      have hfr1OffCore : ∀ a < scratch, ¬ Rcore.foot hnd (tok.coreTok cur) a →
          (a < sb ∨ B.endAddr ≤ a) → st1.mem a = mem a := fun a ha hnc hoff =>
        hfr1 a ha hnc
          (fun hf => by have := reg_in_blocks hcurB.le (Or.inl hf); omega)
          (fun hl => by have := reg_in_blocks hcurB.le (Or.inr (Or.inl hl)); omega)
          (fun he => by have := reg_in_blocks hcurB.le (Or.inr (Or.inr he)); omega)
      have hfr1Foot : ∀ a < scratch, ¬ Rcore.foot hnd (tok.coreTok cur) a →
          Rfull.foot root ((tok, fwdG), (rcG, tcG)) a → st1.mem a = mem a := fun a ha hnc hf =>
        hfr1OffCore a ha hnc (by
          by_contra h; obtain ⟨h1, h2⟩ := not_or.mp h
          exact hFootDisj a (Nat.le_of_not_lt h1) (Nat.lt_of_not_le h2) hf)
      let tok1 : SolverToken cfg L Rcore :=
        { tok with
          coreTok := Function.update tok.coreTok cur y1
          owned := fun a => tok.owned a ∨ (scratch ≤ a ∧ a < sc1)
          tag := fun a => if scratch ≤ a ∧ a < sc1 then 21 + cur else tok.tag a }
      -- Note: `solverStateRep_update_coreTok` only queries `mem' a = mem a` for `a` with `tok.tag a ≠ 0`
      -- (all in `tok.owned`, hence in `Rfull.foot` and off `[sb, B.endAddr)`), so build `mem1'` agreeing
      -- with `st1.mem` on `Rfull.foot` and `mem` elsewhere? Simpler: `st1.mem` already agrees with `mem`
      -- on EVERY `a` with `Rfull.foot a ∧ ¬ Rcore.foot cur a`! Use `memM` agreeing with `st1.mem` on
      -- `a < sb ∨ B.endAddr ≤ a` and `mem` on `[sb, B.endAddr)`:
      let memM : ℕ → ℕ := fun a => if sb ≤ a ∧ a < B.endAddr then mem a else st1.mem a
      have hfrM : ∀ a < scratch, ¬ Rcore.foot hnd (tok.coreTok cur) a → memM a = mem a := fun a ha hnc => by
        dsimp only [memM]; split_ifs with hrg
        · rfl
        · exact hfr1OffCore a ha hnc (by by_contra h; obtain ⟨h1, h2⟩ := not_or.mp h; exact hrg ⟨Nat.le_of_not_lt h1, Nat.lt_of_not_le h2⟩)
      have hY1DisjReg : ∀ a, Rcore.foot hnd y1 a → ¬ (sb ≤ a ∧ a < B.endAddr) := fun a ha hrg => by
        rcases hftY1 a ha with hold | hnew
        · exact hFootDisj a hrg.1 hrg.2 (Or.inr (Or.inr ⟨cur, hcurLt, hold⟩))
        · omega
      have hrepY1M : Rcore.rep hnd (chainLevelOrdAbs model.chain cur) y1 memM :=
        (hlocalCore hnd (chainLevelOrdAbs model.chain cur) y1 st1.mem memM fun a ha => by
          dsimp only [memM]; rw [ite_eq_right (hY1DisjReg a ha)]).1 hrepY1
      obtain ⟨hrep1M, hfoot1, hphi1M⟩ :=
        solverStateRep_update_coreTok hlocalCore hcurLt hrep0 hFootSc hfrM hrepY1M hftY1
      have hFoot1Disj : ∀ a, sb ≤ a → a < B.endAddr →
          ¬ Rfull.foot root ((tok1, fwdG), (rcG, tcG)) a := fun a h1 h2 hf1 => by
        rcases hfoot1 a hf1 with hf0 | hnew
        · exact hFootDisj a h1 h2 hf0
        · omega
      have hRrepLoc := solverStateRep_local cfg L P m V psi k epsExp drainUnit hlocalCore
      have hrep1 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok1 st1.mem :=
        (hRrepLoc root model tok1 memM st1.mem fun a ha => by
          dsimp only [memM]; rw [ite_eq_right fun hrg => hFoot1Disj a hrg.1 hrg.2 ha]).1 hrep1M
      have hphi1Eq : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).phi root tok1 st1.mem =
          (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).phi root tok1 memM :=
        ((hRrepLoc root model tok1 memM st1.mem fun a ha => by
          dsimp only [memM]; rw [ite_eq_right fun hrg => hFoot1Disj a hrg.1 hrg.2 ha]).2).symm
      have hphiY1Eq : Rcore.phi hnd y1 memM = Rcore.phi hnd y1 st1.mem :=
        ((hlocalCore hnd (chainLevelOrdAbs model.chain cur) y1 st1.mem memM fun a ha => by
          dsimp only [memM]; rw [ite_eq_right (hY1DisjReg a ha)]).2).symm
      have hrepF1 : Rfull.rep root model ((tok1, fwdG), (rcG, tcG)) st1.mem :=
        ⟨⟨hrep1, hrepF.1.2.1, hrepF.1.2.2⟩, hrepF.2.1, hrepF.2.2.1, hrepF.2.2.2⟩
      have hcaps1 : SolverLevelCapsInv P V vCap eCap model tok1 st1.mem := by
        refine hcaps.preserve rfl (fun j hj => Or.inl (hcaps.1.2.1 j hj)) (fun a ha => ?_)
          (fun j hj => Or.inl (SolverLevelMetaAt.atCaps hcaps.1 hcaps.2 j hj).2.2.1)
          rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl
        have hne0 : tok.tag a ≠ 0 := by rcases ha with h | h | h | h <;> omega
        have hlt := hFootSc a (Or.inl (hOwn a hne0))
        have hnc : ¬ Rcore.foot hnd (tok.coreTok cur) a := fun hc => by
          have := t21 cur hcurLt a hc; rcases ha with h | h | h | h <;> omega
        exact ⟨by dsimp only [tok1]; rw [ite_eq_right (by omega)], hfr1Foot a hlt hnc (Or.inl (hOwn a hne0))⟩
      have hFrMetaBelowSb : ∀ a < sb, ¬ Rcore.foot hnd (tok.coreTok cur) a → st1.mem a = mem a :=
        fun a ha hnc => hfr1OffCore a (by omega) hnc (Or.inl ha)
      have hMlocEq1 : selectMlocOf B metaBase (solverLevelG tok1 st1.mem) pLast =
          selectMlocOf B metaBase (solverLevelG tok mem) pLast :=
        selectMlocOf_congr_loop fun j hj => by
          rw [hBd] at hj
          have htag := hcaps.1.2.2.2.2.1 (cfg.P.d + j) (by omega)
          rw [← Nat.add_assoc] at htag
          have hlt := hFootSc _ (Or.inl (hOwn (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) (by omega)))
          have hnc : ¬ Rcore.foot hnd (tok.coreTok cur) (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) := fun hc => by
            have := t21 cur hcurLt _ hc; omega
          exact hfr1Foot _ hlt hnc (Or.inl (hOwn (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) (by omega)))
      have hLocLeBase : loc.hb ≤ loc.endAddr := by rw [loc.endAddr_eq]; omega
      have htab1 : SelectMetaTableAt st1.mem (selectMlocOf B metaBase (solverLevelG tok1 st1.mem) pLast) := by
        rw [hMlocEq1]
        exact htab.of_agree fun a ha1 ha2 => hfr1 a (by simp only [selectMlocOf] at ha2; omega)
          (fun hc => by have := hCoreBelow cur (le_refl _) hcurLt a hc; simp only [selectMlocOf] at ha1; have := hreg.1; have := hreg.2.1; have := hreg.2.2.1; omega)
          (fun hf => by have := reg_in_blocks hcurB.le (Or.inl hf); simp only [selectMlocOf] at ha2; omega)
          (fun hl => by have := reg_in_blocks hcurB.le (Or.inr (Or.inl hl)); simp only [selectMlocOf] at ha2; omega)
          (fun he => by have := reg_in_blocks hcurB.le (Or.inr (Or.inr he)); simp only [selectMlocOf] at ha2; omega)
      have hHeap1 : SelectHeapAt st1.mem loc 4 0 :=
        hHeap.of_agree fun a ha1 ha2 => by
          have hendEq := loc.endAddr_eq
          have := hreg.1; have := hreg.2.1; have := hreg.2.2.1; have := hreg.2.2.2.1
          exact hfr1 a (by omega)
            (fun hc => by have := hCoreBelow cur (le_refl _) hcurLt a hc; omega)
            (fun hf => by have := reg_in_blocks hcurB.le (Or.inl hf); omega)
            (fun hl => by have := reg_in_blocks hcurB.le (Or.inr (Or.inl hl)); omega)
            (fun he => by have := reg_in_blocks hcurB.le (Or.inr (Or.inr he)); omega)
      let D1 : SelBlocksData :=
        { D with
          F := Function.update D.F cur (C.activeLSF cur).F.F
          E := Function.update D.E cur (C.G cur).E
          len := Function.update D.len cur (C.chainLen model.chain.ℓ (cur + 1))
          coreE := Function.update D.coreE cur (C.activeCore cur).E
          emb := Function.update D.emb cur (C.activeEmb cur) }
      have hblk1' : SelBlocksDataAt st1.mem B P D1 pLast := by
        rw [hfmtP] at hblk1
        dsimp only [chainLevelOrdAbs] at hblk1
        have hlenEq : (fun e => (cfg.T.lsfs (model.chain.scState cur) br).wstr e * C.chainLen model.chain.ℓ cur e) =
            C.chainLen model.chain.ℓ (cur + 1) := funext fun e => (hChainLenSucc e).symm
        have hGEq : C.G cur = model.chain.G cur := rfl
        dsimp only [D1]; rw [hGEq, hActLSF, hActCore, hActEmb, ← hlenEq]; exact hblk1
      have hMetaBelow1 : tok1.handle + 18 + 2 * (cfg.P.d + 1) ≤ sb ∧
          solverLevelMetaAddr tok1.table cfg.P.d + 2 * cfg.P.d ≤ sb ∧
          ∀ j < cfg.P.d,
            st1.mem (solverLevelMetaAddr tok1.table cfg.P.d + j) + eCap * L ≤ sb ∧
            solverLevelG tok1 st1.mem j + dynGraphSize vCap eCap ≤ sb := by
        refine ⟨hMetaBelow.1, hMetaBelow.2.1, fun j hj => ?_⟩
        have htagL := hcaps.1.2.2.2.2.1 j (by omega)
        have htagG := hcaps.1.2.2.2.2.1 (cfg.P.d + j) (by omega)
        rw [← Nat.add_assoc] at htagG
        have heqL := hfr1Foot _ (hFootSc _ (Or.inl (hOwn (solverLevelMetaAddr tok.table cfg.P.d + j) (by omega))))
          (fun hc => by have := t21 cur hcurLt _ hc; omega) (Or.inl (hOwn (solverLevelMetaAddr tok.table cfg.P.d + j) (by omega)))
        have heqG := hfr1Foot _ (hFootSc _ (Or.inl (hOwn (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) (by omega))))
          (fun hc => by have := t21 cur hcurLt _ hc; omega) (Or.inl (hOwn (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) (by omega)))
        change st1.mem (solverLevelMetaAddr tok.table cfg.P.d + j) + eCap * L ≤ sb ∧
          st1.mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) + dynGraphSize vCap eCap ≤ sb
        rw [heqL, heqG]; exact hMetaBelow.2.2 j hj
      rw [hBLk, ← hActLSF] at hsc1Hi
      -- Recursive call on `cur + 1`
      obtain ⟨scOut, cRec, out, tokFull', hrRec, hscOutLo, hscOutHi, hrepFOut, htabOutEq,
          hhndOutEq, hthOutEq, httOutEq, hvcOutEq, hecOutEq, htrOutEq, htrsOutEq, hrecOutEq,
          hftOut, hOwnOut, hTagLtOut, hTagOut, hcapsOut, htabOut, hHeapOut, hblkOut, hzOut, hfrOut, hcRec⟩ :=
        ih (cur + 1) sc1 st1.pos ((tok1, fwdG), (rcG, tcG)) D1 st1.mem
          (by omega) (by omega) hrepF1
          (fun a ha => by
            rcases hfoot1 a ha with h0 | hnew
            · have := hFootSc a h0; omega
            · exact hnew.2)
          hFoot1Disj
          (fun j hj1 hj2 a ha => by
            dsimp only [tok1] at ha; rw [Function.update_of_ne (by omega)] at ha
            exact hCoreBelow j (by omega) hj2 a ha)
          hMetaBelow1 (by omega) hcaps1 htab1 hHeap1 hblk1'
          (fun j hj1 hj2 => by simp [D1, show j ≠ cur by omega]; exact hDEmpty j (by omega) hj2)
          (fun j hj1 hj2 => hScIn j (by omega) hj2)
          (fun j hj1 hj2 => hBrLt j (by omega) hj2)
          (fun j hj1 hj2 => hFV j (by omega) hj2)
          (fun j hj1 hj2 => hFE j (by omega) hj2)
          (fun j hj1 hj2 => hLenFit j (by omega) hj2)
          (fun j hj1 hj2 => hEmbSlot j (by omega) hj2)
          (fun j hj1 hj2 => hFootAt j (by omega) hj2)
          (fun j hj1 hj2 => hDgCopy j (by omega) hj2)
          (fun j hj1 hj2 => hEmbCopy j (by omega) hj2)
          hz1 (by omega)
      -- Stitch the current step + recursive call into `selectInitInteriorLoopBody`
      let s0 := startState [metaBase, cur, cfg.P.d, tok.handle + 18,
        solverLevelMetaAddr tok.table cfg.P.d, L, B.slot, scratch] mem pos
      have hsc1W : sc1 < 2 ^ w := by omega
      have hscOutW : scOut < 2 ^ w := by omega
      have hltEval : (Expr.bin .lt (.reg 1) (.reg 2)).eval w s0 = some 1 := by
        simp [Expr.eval, BinOp.eval, s0, startState, hcurLt, show 1 < 2 ^ w by omega]
      have hStepRun : ∃ o final cStep,
          Runs w p ω (selectInitInteriorLoopBody loopProc fillIntProc) s0 o final cStep ∧
          o = .returned scOut ∧ final.mem = out.mem ∧ cStep ≤ cFill + cRec + 50 := by
        unfold selectInitInteriorLoopBody
        have hBody : ∃ o final cB,
            Runs w p ω
              (.assign 8 (.load (.bin .add (.reg 3) (.reg 1))) ;;
               .assign 9 (.load (.bin .add (.bin .add (.reg 3) (.bin .add (.reg 2) (.const 1))) (.reg 1))) ;;
               .assign 10 (.load (.bin .add (.reg 4) (.reg 1))) ;;
               .call 11 fillIntProc [.reg 0, .reg 1, .reg 8, .reg 9, .reg 10, .reg 5, .reg 6, .reg 7] ;;
               .call 12 loopProc [.reg 0, .bin .add (.reg 1) (.const 1), .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 11] ;;
               .ret (.reg 12)) s0 o final cB ∧
            o = .returned scOut ∧ final.mem = out.mem ∧ cB ≤ cFill + cRec + 46 := by
          have hw1 : 1 < 2 ^ w := by omega
          have h1 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 3) (.reg 1)))) s0 .normal
              ⟨mem, Function.update s0.regs 8 hnd, pos⟩ 5 :=
            runs_assign_iff.mpr ⟨hnd, by
              simp [Expr.eval, BinOp.eval, s0, startState, hnd, hCoreCur.1,
                show tok.handle + 18 + cur < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
          let rg8 := Function.update s0.regs 8 hnd
          let rg9 := Function.update rg8 9 br
          let rg10 := Function.update rg9 10 prevLen
          let rg11 := Function.update rg10 11 sc1
          let rg12 := Function.update rg11 12 scOut
          have h2 : Runs w p ω (.assign 9 (.load (.bin .add (.bin .add (.reg 3) (.bin .add (.reg 2) (.const 1))) (.reg 1))))
              ⟨mem, rg8, pos⟩ .normal ⟨mem, rg9, pos⟩ 9 :=
            runs_assign_iff.mpr ⟨br, by
              simp [Expr.eval, BinOp.eval, rg8, s0, startState, hw1, br, hCoreCur.2.1,
                show cfg.P.d + 1 < 2 ^ w by omega,
                show tok.handle + 18 + (cfg.P.d + 1) < 2 ^ w by omega,
                show tok.handle + 18 + (cfg.P.d + 1) + cur < 2 ^ w by omega],
              rfl, rfl, by simp [Expr.size]⟩
          have h3 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 4) (.reg 1))))
              ⟨mem, rg9, pos⟩ .normal ⟨mem, rg10, pos⟩ 5 :=
            runs_assign_iff.mpr ⟨prevLen, by
              simp [Expr.eval, BinOp.eval, rg9, rg8, s0, startState, prevLen,
                show solverLevelMetaAddr tok.table cfg.P.d + cur < 2 ^ w by omega],
              rfl, rfl, by simp [Expr.size]⟩
          have h4 : Runs w p ω (.call 11 fillIntProc [.reg 0, .reg 1, .reg 8, .reg 9, .reg 10, .reg 5, .reg 6, .reg 7])
              ⟨mem, rg10, pos⟩ .normal ⟨st1.mem, rg11, st1.pos⟩ (cFill + 9) :=
            runs_call_iff.mpr ⟨[metaBase, cur, hnd, br, prevLen, B.Lk, B.slot, scratch], _,
              .returned sc1, st1, cFill,
              by simp [evalArgs, Expr.eval, rg10, rg9, rg8, s0, startState, hBLk],
              hpFillInt, hrFill, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
          have h5 : Runs w p ω (.call 12 loopProc [.reg 0, .bin .add (.reg 1) (.const 1), .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 11])
              ⟨st1.mem, rg11, st1.pos⟩ .normal ⟨out.mem, rg12, out.pos⟩ (cRec + 11) :=
            runs_call_iff.mpr ⟨[metaBase, cur + 1, cfg.P.d, tok1.handle + 18,
              solverLevelMetaAddr tok1.table cfg.P.d, L, B.slot, sc1], _, .returned scOut, out, cRec,
              by simp [evalArgs, Expr.eval, BinOp.eval, rg11, rg10, rg9, rg8, s0, startState, hw1,
                show cur + 1 < 2 ^ w by omega, tok1],
              hpLoop, hrRec, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
          have h6 : Runs w p ω (.ret (.reg 12)) ⟨out.mem, rg12, out.pos⟩ (.returned scOut) ⟨out.mem, rg12, out.pos⟩ 2 :=
            runs_ret_iff.mpr ⟨scOut, by simp [Expr.eval, rg12], rfl, rfl, rfl⟩
          exact ⟨.returned scOut, _, _,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, h1,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, h2,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, h3,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, h4,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, h5, h6, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
            rfl, rfl, by omega⟩
        obtain ⟨o, final, cB, hrB, hoEq, hmEq, hcB⟩ := hBody
        exact ⟨o, final, _, runs_cond_iff.mpr ⟨1, cB, hltEval, by simpa using hrB, rfl⟩,
          hoEq, hmEq, by simp [Expr.size]; omega⟩
      obtain ⟨_, final, cStep, hrStep, rfl, hmemEq, hcStep⟩ := hStepRun
      have hDTargetEq :
          ({ D1 with
            F := fun j => if cur + 1 ≤ j ∧ j < cfg.P.d then (C.activeLSF j).F.F else D1.F j
            E := fun j => if cur + 1 ≤ j ∧ j < cfg.P.d then (C.G j).E else D1.E j
            len := fun j => if cur + 1 ≤ j ∧ j < cfg.P.d then C.chainLen model.chain.ℓ (j + 1) else D1.len j
            coreE := fun j => if cur + 1 ≤ j ∧ j < cfg.P.d then (C.activeCore j).E else D1.coreE j
            emb := fun j => if cur + 1 ≤ j ∧ j < cfg.P.d then C.activeEmb j else D1.emb j } : SelBlocksData) =
          { D with
            F := fun j => if cur ≤ j ∧ j < cfg.P.d then (C.activeLSF j).F.F else D.F j
            E := fun j => if cur ≤ j ∧ j < cfg.P.d then (C.G j).E else D.E j
            len := fun j => if cur ≤ j ∧ j < cfg.P.d then C.chainLen model.chain.ℓ (j + 1) else D.len j
            coreE := fun j => if cur ≤ j ∧ j < cfg.P.d then (C.activeCore j).E else D.coreE j
            emb := fun j => if cur ≤ j ∧ j < cfg.P.d then C.activeEmb j else D.emb j } := by
        dsimp only [D1]; congr 1 <;> (funext j; by_cases hEq : j = cur <;> simp [hEq, hcurLt]; split_ifs <;> first | rfl | omega)
      refine ⟨scOut, cStep, final, tokFull', hrStep, by omega, by omega,
        hmemEq ▸ hrepFOut, htabOutEq, hhndOutEq, hthOutEq, httOutEq, hvcOutEq, hecOutEq,
        htrOutEq, htrsOutEq, hrecOutEq,
        fun a ha => ?_, fun a ha => hOwnOut a (Or.inl ha),
        fun a ha => (hTagLtOut a (by omega)).trans (by dsimp only [tok1]; rw [ite_eq_right (by omega)]),
        fun a hne => (hTagOut a (by dsimp only [tok1]; rw [ite_eq_right (by have := hFootSc a (Or.inl (hOwn a hne)); omega)]; exact hne)).trans
          (by dsimp only [tok1]; rw [ite_eq_right (by have := hFootSc a (Or.inl (hOwn a hne)); omega)]),
        hmemEq ▸ hcapsOut, hmemEq ▸ htabOut, hmemEq ▸ hHeapOut,
        hmemEq ▸ (hDTargetEq ▸ hblkOut), hmemEq ▸ hzOut, fun a ha hnc => ?_, ?_⟩
      · rcases hftOut a ha with hf1 | hnew
        · rcases hfoot1 a hf1 with hf0 | hnew1
          · exact Or.inl hf0
          · exact Or.inr ⟨hnew1.1, by omega⟩
        · exact Or.inr ⟨by omega, hnew.2⟩
      · rw [hmemEq, hfrOut a ha (fun ⟨j, hj1, hj2, hc⟩ => by
            dsimp only [tok1] at hc; rw [Function.update_of_ne (by omega)] at hc
            exact hnc ⟨j, by omega, hj2, hc⟩)]
        exact hFrMetaBelowSb a ha fun hc => hnc ⟨cur, le_refl _, hcurLt, hc⟩
      · -- Telescope `Rfull.phi` across `cur` and `cur + 1 .. d - 1`
        have hphiFull1 : Rfull.phi root ((tok1, fwdG), (rcG, tcG)) st1.mem +
            Rcore.phi hnd (tok.coreTok cur) mem =
            Rfull.phi root ((tok, fwdG), (rcG, tcG)) mem + Rcore.phi hnd y1 st1.mem := by
          rw [solverStateRepFull_phi_eq (tok := ((tok1, fwdG), (rcG, tcG))) ⟨hrep1, hrepF.1.2.1, hrepF.1.2.2⟩ hrepF.2.2.1 hrepF.2.2.2,
            solverStateRepFull_phi_eq (tok := ((tok, fwdG), (rcG, tcG))) hrepF.1 hrepF.2.2.1 hrepF.2.2.2,
            hphi1Eq, ← hphiY1Eq]
          dsimp only at hphi1M ⊢
          change (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).phi root tok1 memM +
              Rcore.phi hnd (tok.coreTok cur) mem =
            (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).phi root tok mem +
              Rcore.phi hnd y1 memM at hphi1M
          omega
        rw [hmemEq, hCostSplit]
        rw [hDFCur, ← hActLSF, hBLk] at hcFill
        change cFill + Rcore.phi hnd y1 st1.mem ≤
          selectFillInteriorLevelCost Psc.readout 0 0 (C.activeLSF cur).F.F.n (C.activeLSF cur).F.F.m
            (model.chain.G cur).m L
            (L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (model.chain.lvlM cur + model.chain.N₀ + 2) + 1))
            B.slot + Rcore.phi hnd (tok.coreTok cur) mem at hcFill
        omega
  exact hInd (cfg.P.d - cur) cur scratch pos tokFull D mem rfl hcurLe hrepFull hFootSc hFootDisj
    hCoreBelow hMetaBelow hEndSc hcaps htab hHeap hblk hDEmpty hScIn hBrLt hFV hFE hLenFit hEmbSlot
    hFootAt hDgCopy hEmbCopy hz hroom

end MinCostFlow.MinRatio
