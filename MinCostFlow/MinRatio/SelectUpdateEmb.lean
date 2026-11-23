module

public import MinCostFlow.MinRatio.SelectUpdateNonRebuilt
public import MinCostFlow.MinRatio.SelectInteriorFill
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# Non-rebuilt single-level embedding update (`SelectUpdateEmb`)

Runs Steps 6–9 of non-rebuilt level maintenance (`op 4` readout + three `embUpdateFromList`
calls on `uG`, `fDel`, `reemb`) for one interior level `j < B.d`, updating `D.coreE j` and
`D.emb j` in `SelBlocksDataAt`.

Separated from `SelectUpdateFPhiLen` so that all `stDesc` stretch-table reads finish before any
core `op 4` call can touch `Rcore.foot`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program

/-- Space bound for `selectUpdateEmbLevelBody`. -/
def selectUpdateEmbSpace (uGLen fDelLen uSLen reembLen : ℕ) : ℕ :=
  2 + 2 * (uGLen + fDelLen + uSLen + reembLen)

/-- Cost bound for `selectUpdateEmbLevelBody`. -/
def selectUpdateEmbCost (readoutCost uGLen fDelLen uSLen reembLen slotSz : ℕ) : ℕ :=
  readoutCost +
  selEmbUpdateFromListCost uGLen slotSz +
  selEmbUpdateFromListCost fDelLen slotSz +
  selEmbUpdateFromListCost uSLen slotSz +
  selEmbUpdateFromListCost reembLen slotSz + 320

/-- Update `coreE j` and `emb j` for one non-rebuilt level `j < B.d` using `op 4` and four
`embUpdateFromList` calls on `uG`, `fDel`, `uS`, and `reemb`.
Arguments: `[metaBase, j, slot, handle, branch, slotSz, scratch]` (`reg 0..6`). Returns `scOut`. -/
def selectUpdateEmbLevelBody (op4 embUpdateFromList : ℕ) : Stmt :=
  .assign 7 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 8 (.bin .add (.reg 7) (.const 1)) ;;
  .assign 9 (.bin .add (.reg 0) (.const smTableOff)) ;;
  .assign 10 (.load (.bin .add (.reg 9) (.reg 1))) ;;
  .assign 11 (.load (.bin .add (.bin .add (.reg 9) (.reg 8)) (.reg 1))) ;;
  .assign 12 (.load (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 2) (.reg 8))) (.reg 1))) ;;
  .assign 13 (.load (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 5) (.reg 8))) (.reg 1))) ;;
  .assign 14 (.load (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 6) (.reg 8))) (.reg 1))) ;;
  .assign 15 (.bin .add (.bin .add (.reg 10) (.const 4)) (.bin .mul (.const 7) (.reg 11))) ;;
  .assign 16 (.bin .add (.bin .add (.reg 14) (.const 4)) (.bin .mul (.const 7) (.reg 11))) ;;
  .assign 17 (.load (.reg 2)) ;;
  .assign 18 (.load (.bin .add (.reg 2) (.const 1))) ;;
  .assign 19 (.load (.bin .add (.reg 2) (.const 2))) ;;
  .assign 20 (.load (.bin .add (.reg 2) (.const 3))) ;;
  .assign 21 (.load (.bin .add (.reg 2) (.const 4))) ;;
  .assign 22 (.load (.bin .add (.reg 2) (.const 5))) ;;
  .assign 28 (.load (.bin .add (.reg 2) (.const 6))) ;;
  .assign 29 (.load (.bin .add (.reg 2) (.const 7))) ;;
  .call 23 op4 [.reg 3, .reg 4, .reg 10, .reg 6] ;;
  .assign 24 (.load (.reg 6)) ;;
  .call 25 embUpdateFromList
    [.reg 15, .reg 16, .reg 24, .reg 13, .reg 12, .reg 5, .reg 17, .reg 18, .reg 23] ;;
  .call 26 embUpdateFromList
    [.reg 15, .reg 16, .reg 24, .reg 13, .reg 12, .reg 5, .reg 19, .reg 20, .reg 25] ;;
  .call 27 embUpdateFromList
    [.reg 15, .reg 16, .reg 24, .reg 13, .reg 12, .reg 5, .reg 21, .reg 22, .reg 26] ;;
  .call 30 embUpdateFromList
    [.reg 15, .reg 16, .reg 24, .reg 13, .reg 12, .reg 5, .reg 28, .reg 29, .reg 27] ;;
  .ret (.reg 30)

theorem selectUpdateEmbLevelBody_noRand (op4 embUpdateFromList : ℕ) :
    (selectUpdateEmbLevelBody op4 embUpdateFromList).NoRand := by
  simp [selectUpdateEmbLevelBody, Stmt.NoRand]

/-- Recursive loop calling `selectUpdateEmbLevelBody` for levels `cur .. limit - 1`.
Arguments: `[metaBase, cur, limit, levelTable, selOutBase, d, slotSz, scratch]` (`reg 0..7`). -/
def selectUpdateEmbLoopBody (self embLvlProc : ℕ) : Stmt :=
  .cond (.bin .lt (.reg 1) (.reg 2))
    (.assign 8 (.bin .add (.bin .add (.reg 4) (.const 1)) (.bin .mul (.const 12) (.reg 1))) ;;
     .assign 9 (.load (.bin .add (.reg 3) (.reg 1))) ;;
     .assign 10 (.load (.bin .add (.bin .add (.reg 3) (.bin .add (.reg 5) (.const 1))) (.reg 1))) ;;
     .call 11 embLvlProc [.reg 0, .reg 1, .reg 8, .reg 9, .reg 10, .reg 6, .reg 7] ;;
     .call 12 self [.reg 0, .bin .add (.reg 1) (.const 1), .reg 2, .reg 3, .reg 4, .reg 5,
       .reg 6, .reg 11] ;;
     .ret (.reg 12))
    (.ret (.reg 7))

theorem selectUpdateEmbLoopBody_noRand (self embLvlProc : ℕ) :
    (selectUpdateEmbLoopBody self embLvlProc).NoRand := by
  simp [selectUpdateEmbLoopBody, Stmt.NoRand]

/-- Space bound for `selectUpdateEmbLoopBody` over levels `cur .. limit - 1`. -/
def selectUpdateEmbLoopSpace (diffLists : ℕ → LevelDiffLists) (cur limit : ℕ) : ℕ :=
  (Finset.Ico cur limit).sum fun j =>
    selectUpdateEmbSpace (diffLists j).uG.length (diffLists j).fDel.length
      (diffLists j).uS.length (diffLists j).reemb.length

/-- Cost bound for `selectUpdateEmbLoopBody` over levels `cur .. limit - 1`. -/
def selectUpdateEmbLoopCost (readoutCost : ℕ) (diffLists : ℕ → LevelDiffLists)
    (cur limit slotSz : ℕ) : ℕ :=
  (Finset.Ico cur limit).sum (fun j =>
    selectUpdateEmbCost readoutCost (diffLists j).uG.length (diffLists j).fDel.length
      (diffLists j).uS.length (diffLists j).reemb.length slotSz + 70) + 10

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program

private lemma runs_seq_call_e {w r f : ℕ} {args : List Expr} {s2 : Stmt}
    {p : Program} {ω : ℕ → Bool} {st st1 : State} {o1 : Outcome} {vs : List ℕ}
    {body : Stmt} {c1 k T : ℕ} {Q : Outcome → State → Prop}
    (hvs : evalArgs w st args = some vs) (hbody : p.procs[f]? = some body)
    (hr1 : Runs w p ω body (startState vs st.mem st.pos) o1 st1 c1)
    (h2 : ∃ o st2 c2, Runs w p ω s2 ⟨st1.mem, Function.update st.regs r o1.value, st1.pos⟩ o st2 c2 ∧
      Q o st2 ∧ (k + (argsSize args + c1 + 2)) + c2 ≤ T) :
    ∃ o st2 c, Runs w p ω (.seq (.call r f args) s2) st o st2 c ∧ Q o st2 ∧ k + c ≤ T := by
  obtain ⟨o, st2, c2, hr2, hq, hc⟩ := h2
  exact ⟨o, st2, (argsSize args + c1 + 1) + c2 + 1,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _,
      runs_call_iff.mpr ⟨vs, body, o1, st1, c1, hvs, hbody, hr1, rfl, rfl, rfl⟩, hr2, rfl⟩), hq, by omega⟩

set_option maxHeartbeats 1000000 in
/-- Verification of `selectUpdateEmbLevelBody`: updates `D.coreE j` and `D.emb j` in
`SelBlocksDataAt` while preserving `R.rep`, all other block fields, and all memory `< scratch`
outside `R.foot handle x ∨ B.regEmb j`. -/
theorem selectUpdateEmbLevel_runs
    {w depth k M N capExp j pLast handle branch slot scratch pos embUpdateFromList : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph : MGraph}
    {Psc : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {p : Program} {op : ℕ → ℕ} {ω : ℕ → Bool}
    {B : SelectBlocksLoc} {metaBase : ℕ} {solverG : ℕ → ℕ} {D : SelBlocksData}
    {a : SparseCoreOrdAbs tool} {x : R.τ} {L : LevelDiffLists} {mem : ℕ → ℕ}
    (hLocalR : R.Local)
    (hw16 : 16 < 2 ^ w) (hSlotW : B.slot < 2 ^ w)
    (hj : j < B.d) (hbrLt : branch < k) (hkW : k < 2 ^ w) (hHndW : handle < 2 ^ w)
    (htab : SelectMetaTableAt mem (selectMlocOf B metaBase solverG pLast))
    (hblk : SelBlocksDataAt mem B fmt.precision D pLast)
    (hMetaLe : metaBase + selectLevelMetaSize B.d ≤ scratch)
    (hBEnd : B.endAddr ≤ scratch)
    (hG : DynGraphAt mem (solverG j) B.vCap B.eCap a.G)
    (hGLe : solverG j + dynGraphSize B.vCap B.eCap ≤ scratch)
    (hGOffBlk : solverG j + dynGraphSize B.vCap B.eCap ≤ B.fPtr j ∨
      B.fPtr j + B.levelSize ≤ solverG j)
    (hFMatch : D.F j = (tool.lsfs a.st branch).F.F)
    (hrep : R.rep handle a x mem)
    (hIn : SparseCoreOrdInput tool k M N a.st a.G a.ord a.n)
    (hFootLt : ∀ addr, R.foot handle x addr → addr < scratch)
    (hFootOffB : ∀ addr, B.base ≤ addr → addr < B.endAddr → ¬ R.foot handle x addr)
    (hDisjG : ∀ addr, solverG j ≤ addr → addr < solverG j + dynGraphSize B.vCap B.eCap →
      ¬ R.foot handle x addr)
    (hDisjLists :
      (∀ addr, mem (slot + 0) ≤ addr → addr < mem (slot + 0) + L.uG.length → ¬ R.foot handle x addr) ∧
      (∀ addr, mem (slot + 2) ≤ addr → addr < mem (slot + 2) + L.fDel.length → ¬ R.foot handle x addr) ∧
      (∀ addr, mem (slot + 4) ≤ addr → addr < mem (slot + 4) + L.uS.length → ¬ R.foot handle x addr) ∧
      (∀ addr, mem (slot + 6) ≤ addr → addr < mem (slot + 6) + L.reemb.length → ¬ R.foot handle x addr))
    (hFootAt : SparseCoreReadoutFootAt fmt B.Lk depth tool initialGraph k M N B.vCap B.eCap capExp
      Psc allocation R p op)
    (hDiff : LevelDiffListsAt mem slot L)
    (hSlotLe : slot + 12 ≤ scratch)
    (hUGLe : mem (slot + 0) + L.uG.length ≤ scratch)
    (hUGOffBlk : mem (slot + 0) + L.uG.length ≤ B.fPtr j ∨ B.fPtr j + B.levelSize ≤ mem (slot + 0))
    (hFDelLe : mem (slot + 2) + L.fDel.length ≤ scratch)
    (hFDelOffBlk : mem (slot + 2) + L.fDel.length ≤ B.fPtr j ∨ B.fPtr j + B.levelSize ≤ mem (slot + 2))
    (hUSLe : mem (slot + 4) + L.uS.length ≤ scratch)
    (hUSOffBlk : mem (slot + 4) + L.uS.length ≤ B.fPtr j ∨ B.fPtr j + B.levelSize ≤ mem (slot + 4))
    (hReembLe : mem (slot + 6) + L.reemb.length ≤ scratch)
    (hReembOffBlk : mem (slot + 6) + L.reemb.length ≤ B.fPtr j ∨ B.fPtr j + B.levelSize ≤ mem (slot + 6))
    (hListCaps : (∀ e ∈ L.uG, e < B.eCap) ∧ (∀ e ∈ L.fDel, e < B.eCap) ∧
      (∀ e ∈ L.uS, e < B.eCap) ∧ (∀ e ∈ L.reemb, e < B.eCap))
    (hEmbSlot : ∀ e ∈ (coreGraph a.G (tool.lsfs a.st branch)).E,
      (mWalkEncode (tool.emb a.st branch e)).length ≤ B.slot)
    (hEmbUnchanged : ∀ e ∈ (coreGraph a.G (tool.lsfs a.st branch)).E,
      e ∉ L.uG → e ∉ L.fDel → e ∉ L.uS → e ∉ L.reemb →
      e ∈ D.coreE j ∧ tool.emb a.st branch e = D.emb j e)
    (hEmbUpd : ∀ L' : List ℕ, MeetsContract w p embUpdateFromList
      (selEmbUpdateFromListContract w B.vCap B.eCap a.G (tool.lsfs a.st branch).F.F L'
        (tool.emb a.st branch)))
    (hz : ZeroFrom mem scratch)
    (hroom : scratch + selectUpdateEmbSpace L.uG.length L.fDel.length L.uS.length L.reemb.length < 2 ^ w) :
    let newCoreE := (coreGraph a.G (tool.lsfs a.st branch)).E
    ∃ scOut cost out, ∃ y : R.τ,
      Runs w p ω (selectUpdateEmbLevelBody (op 4) embUpdateFromList)
        (startState [metaBase, j, slot, handle, branch, B.slot, scratch] mem pos)
        (.returned scOut) out cost ∧
      scratch ≤ scOut ∧
      scOut ≤ scratch + selectUpdateEmbSpace L.uG.length L.fDel.length L.uS.length L.reemb.length ∧
      R.rep handle a y out.mem ∧
      SelBlocksDataAt out.mem B fmt.precision
        { D with
          coreE := Function.update D.coreE j newCoreE
          emb := Function.update D.emb j (tool.emb a.st branch) } pLast ∧
      ZeroFrom out.mem scOut ∧
      (∀ addr, R.foot handle y addr → R.foot handle x addr ∨ (scratch ≤ addr ∧ addr < scOut)) ∧
      (∀ addr < scratch, ¬ R.foot handle x addr → ¬ B.regEmb j addr → out.mem addr = mem addr) ∧
      cost + R.phi handle y out.mem ≤
        selectUpdateEmbCost Psc.readout L.uG.length L.fDel.length L.uS.length L.reemb.length B.slot +
          R.phi handle x mem := by
  intro newCoreE
  set newF := (tool.lsfs a.st branch).F.F
  set newEmb := tool.emb a.st branch
  have hjLe : j ≤ B.d := Nat.le_of_lt hj
  have hBaseLeF : B.base ≤ B.fPtr j := by unfold SelectBlocksLoc.fPtr; omega
  have hBlkEndLe : B.fPtr j + B.levelSize ≤ B.endAddr := by
    have := B.blk_le_last hjLe
    unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr; omega
  have hFJEnd : B.fPtr j + dynGraphSize B.vCap B.eCap = B.phiPtr j := rfl
  have hPhiEnd : B.phiPtr j + B.vCap * B.Lk = B.lenPtr j := rfl
  have hLenEnd : B.lenPtr j + B.eCap * B.Lk = B.embPtr j := rfl
  have hEmbEnd : B.embPtr j + B.eCap + B.eCap * B.slot = B.fPtr j + B.levelSize :=
    (B.blkEnd_eq j).symm
  have hDgSz : dynGraphSize B.vCap B.eCap = 4 + 7 * B.vCap + 9 * B.eCap := rfl
  have hMetaSize : selectLevelMetaSize B.d = 2 + 8 * (B.d + 1) := rfl
  have hSpDef : selectUpdateEmbSpace L.uG.length L.fDel.length L.uS.length L.reemb.length =
      2 + 2 * (L.uG.length + L.fDel.length + L.uS.length + L.reemb.length) := rfl
  have hrow := htab.2.2 j hjLe
  have hdM : mem (metaBase + 1) = B.d := by simpa [smDOff, selectMlocOf] using htab.2.1
  have hgPtrM : mem (smEntryAddr metaBase B.d 0 j) = solverG j := by
    simpa [selectMlocOf, hj] using hrow.1
  have hvCapM : mem (smEntryAddr metaBase B.d 1 j) = B.vCap := by
    simpa [selectMlocOf] using hrow.2.1
  have heCapM : mem (smEntryAddr metaBase B.d 2 j) = B.eCap := by
    simpa [selectMlocOf] using hrow.2.2.1
  have hembM : mem (smEntryAddr metaBase B.d 5 j) = B.embPtr j := by
    simpa [selectMlocOf] using hrow.2.2.2.2.2.1
  have hfM : mem (smEntryAddr metaBase B.d 6 j) = B.fPtr j := by
    simpa [selectMlocOf] using hrow.2.2.2.2.2.2.1
  simp only [add_zero] at hUGLe hUGOffBlk hDisjLists
  set uGPtr := mem slot
  set fDelPtr := mem (slot + 2)
  set uSPtr := mem (slot + 4)
  set reembPtr := mem (slot + 6)
  have hUGAt : ListAt mem uGPtr L.uG := hDiff.2.1
  have hFDelAt : ListAt mem fDelPtr L.fDel := hDiff.2.2.2.1
  have hUSAt : ListAt mem uSPtr L.uS := hDiff.2.2.2.2.2.1
  have hReembAt : ListAt mem reembPtr L.reemb := hDiff.2.2.2.2.2.2.2
  -- Step 1: `op 4` (`[handle, branch, solverG j, scratch]`)
  obtain ⟨b6, hb6, o6, st6, c6, y6, hr6, hrep6, hp6, hresp6, hcost6⟩ :=
    hFootAt.op4_runs handle a x [handle, branch, solverG j, scratch] mem pos ω
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro v (rfl|rfl|rfl|rfl) <;> omega)
      rfl hrep ⟨hIn, handle, branch, solverG j, scratch, rfl, hbrLt, hG, by omega⟩
      hFootLt hz (by change scratch + 2 < 2 ^ w; omega)
  obtain ⟨hEmbRd6, hBounded6, hCapLe6, hWalkWords6, hTableFoot6, hWalkFoot6⟩ := hp6
  simp only [heapArg, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.getLastD_cons, List.getLastD_nil]
    at hEmbRd6 hBounded6 hCapLe6 hWalkWords6 hTableFoot6 hWalkFoot6 hresp6
  set sc3 := o6.value
  set embTable := st6.mem scratch
  have hsc3Lo : scratch ≤ sc3 := hresp6.1
  have hsc3Hi : sc3 ≤ scratch + 2 := hresp6.2.1
  have hz6 : ZeroFrom st6.mem sc3 := hresp6.2.2.1
  have hfr6 := hresp6.2.2.2.1
  have hft6 := hresp6.2.2.2.2
  have hDisjY6Blk : ∀ addr, B.base ≤ addr → addr < B.endAddr → ¬ R.foot handle y6 addr :=
    fun addr h1 h2 hfy => Or.elim (hft6 addr hfy) (hFootOffB addr h1 h2) (fun hnew => by omega)
  have hblk6 : SelBlocksDataAt st6.mem B fmt.precision D pLast :=
    hblk.of_agree fun addr h1 h2 => hfr6 addr (by omega) (hFootOffB addr h1 h2)
  have hG6 : DynGraphAt st6.mem (solverG j) B.vCap B.eCap a.G :=
    hG.of_agree fun addr ha1 ha2 => hfr6 addr (by omega) (hDisjG addr ha1 ha2)
  have hNewF6 : DynGraphAt st6.mem (B.fPtr j) B.vCap B.eCap newF := by
    have := hblk6.1 j hjLe; rwa [hFMatch] at this
  have hUGAt6 : ListAt st6.mem uGPtr L.uG := fun i hi =>
    (hfr6 _ (by omega) (hDisjLists.1 _ (by omega) (by omega))).trans (hUGAt i hi)
  have hFDelAt6 : ListAt st6.mem fDelPtr L.fDel := fun i hi =>
    (hfr6 _ (by omega) (hDisjLists.2.1 _ (by omega) (by omega))).trans (hFDelAt i hi)
  have hUSAt6 : ListAt st6.mem uSPtr L.uS := fun i hi =>
    (hfr6 _ (by omega) (hDisjLists.2.2.1 _ (by omega) (by omega))).trans (hUSAt i hi)
  have hReembAt6 : ListAt st6.mem reembPtr L.reemb := fun i hi =>
    (hfr6 _ (by omega) (hDisjLists.2.2.2 _ (by omega) (by omega))).trans (hReembAt i hi)
  have hSrcOk6 : ∀ e ∈ a.G.E \ newF.E,
      SelEmbSrcOk st6.mem w embTable B.slot (B.embPtr j) (B.embPtr j + B.eCap + B.eCap * B.slot) newEmb e ∧
      embTable + e < sc3 ∧
      st6.mem (embTable + e) + (mWalkEncode (newEmb e)).length ≤ sc3 := by
    intro e heDiff
    have heCore : e ∈ newCoreE := heDiff
    have heCap : e < B.eCap := hG.2.2.1 e (Finset.mem_sdiff.mp heDiff).1
    have hTabF := hTableFoot6 (embTable + e) (by omega) (by have := (hEmbRd6 e heCore).1; omega)
    have hTabLt : embTable + e < sc3 := by
      rcases hTabF with hfy | hnew
      · rcases hft6 _ hfy with hfx | hnew2
        · exact lt_of_lt_of_le (hFootLt _ hfx) hsc3Lo
        · omega
      · omega
    have hWalkLe : st6.mem (embTable + e) + (mWalkEncode (newEmb e)).length ≤ sc3 := by
      have hpos : 0 < (mWalkEncode (newEmb e)).length := by rw [mWalkEncode_length]; omega
      have hlast := hWalkFoot6 e heCore
        (st6.mem (embTable + e) + (mWalkEncode (newEmb e)).length - 1)
        (by dsimp only [newEmb] at hpos ⊢; omega) (by dsimp only [newEmb] at hpos ⊢; omega)
      rcases hlast with hfy | hnew
      · rcases hft6 _ hfy with hfx | hnew2
        · have := hFootLt _ hfx; omega
        · omega
      · omega
    refine ⟨selEmbSrcOk_of_op4_selectRegion hBounded6 hWalkWords6 hTableFoot6 hWalkFoot6
      (by omega) heCap
      (fun addr h1 h2 => hDisjY6Blk addr
        (by unfold SelectBlocksLoc.embPtr SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr at h1; omega)
        (by omega))
      (fun addr h1 h2 hnew => by omega) heCore (hEmbSlot e heCore), hTabLt, hWalkLe⟩
  have hEmbTabW : embTable < 2 ^ w := by have := hBounded6.2.1; omega
  -- Step 2: `embUpdateFromList` on `L.uG`
  obtain ⟨b7, hb7, o7, st7, c7, hr7, hp7, hc7⟩ :=
    hEmbUpd L.uG [dgEPresBase (solverG j) B.vCap, dgEPresBase (B.fPtr j) B.vCap, embTable,
      B.embPtr j, B.eCap, B.slot, uGPtr, L.uG.length, sc3] st6.mem st6.pos ω
      (by unfold dgEPresBase; wram_words)
      ⟨solverG j, B.fPtr j, embTable, B.embPtr j, B.slot, uGPtr, sc3, rfl, hw16,
        by omega, by omega, by omega, by omega, hG6, hNewF6, hUGAt6, hListCaps.1,
        fun e _ heDiff => hSrcOk6 e heDiff, hz6, by omega⟩
  obtain ⟨_, _, _, _, _, _, _, hargs7, hsc4Eq, hz7, hcop7, hfr7, hkeep7⟩ := hp7
  simp only [List.cons.injEq, and_true] at hargs7
  obtain ⟨-, -, rfl, rfl, -, rfl, rfl, -, rfl⟩ := hargs7
  set sc4 := sc3 + 2 * L.uG.length
  have hSt7Ag6 : ∀ addr < sc3, (addr < B.embPtr j ∨ B.fPtr j + B.levelSize ≤ addr) →
      st7.mem addr = st6.mem addr := fun addr hlt hout => hfr7 addr hlt (by omega)
  have hG7 : DynGraphAt st7.mem (solverG j) B.vCap B.eCap a.G :=
    hG6.of_agree fun addr _ _ => hSt7Ag6 addr (by omega) (by rcases hGOffBlk with h | h <;> omega)
  have hNewF7 : DynGraphAt st7.mem (B.fPtr j) B.vCap B.eCap newF :=
    hNewF6.of_agree fun addr _ _ => hSt7Ag6 addr (by omega) (Or.inl (by omega))
  have hFDelAt7 : ListAt st7.mem fDelPtr L.fDel := fun i hi =>
    (hSt7Ag6 _ (by omega) (by rcases hFDelOffBlk with h | h <;> omega)).trans (hFDelAt6 i hi)
  have hSrcOk7 : ∀ e ∈ a.G.E \ newF.E,
      SelEmbSrcOk st7.mem w embTable B.slot (B.embPtr j) (B.embPtr j + B.eCap + B.eCap * B.slot) newEmb e ∧
      embTable + e < sc4 ∧
      st7.mem (embTable + e) + (mWalkEncode (newEmb e)).length ≤ sc4 := by
    intro e heDiff
    obtain ⟨⟨hsl, hmw, htw, htd, hww, hwk, hwd⟩, htl, hwl⟩ := hSrcOk6 e heDiff
    have hteq : st7.mem (embTable + e) = st6.mem (embTable + e) := hfr7 _ htl htd
    have hweq : ∀ t < (mWalkEncode (newEmb e)).length,
        st7.mem (st6.mem (embTable + e) + t) = st6.mem (st6.mem (embTable + e) + t) :=
      fun t ht => hfr7 _ (by omega) (by rcases hwd with h | h <;> [left; right] <;> omega)
    refine ⟨⟨hsl, fun t ht => by rw [hteq, hweq t ht]; exact hmw t ht, htw, htd,
      by rw [hteq]; exact hww, fun t ht => by rw [hteq, hweq t ht]; exact hwk t ht,
      by rw [hteq]; exact hwd⟩, by omega, by rw [hteq]; omega⟩
  -- Step 3: `embUpdateFromList` on `L.fDel`
  obtain ⟨b8, hb8, o8, st8, c8, hr8, hp8, hc8⟩ :=
    hEmbUpd L.fDel [dgEPresBase (solverG j) B.vCap, dgEPresBase (B.fPtr j) B.vCap, embTable,
      B.embPtr j, B.eCap, B.slot, fDelPtr, L.fDel.length, sc4] st7.mem st7.pos ω
      (by unfold dgEPresBase; wram_words)
      ⟨solverG j, B.fPtr j, embTable, B.embPtr j, B.slot, fDelPtr, sc4, rfl, hw16,
        by omega, by omega, by omega, by omega, hG7, hNewF7, hFDelAt7, hListCaps.2.1,
        fun e _ heDiff => hSrcOk7 e heDiff, hsc4Eq ▸ hz7, by omega⟩
  obtain ⟨_, _, _, _, _, _, _, hargs8, hsc5Eq, hz8, hcop8, hfr8, hkeep8⟩ := hp8
  simp only [List.cons.injEq, and_true] at hargs8
  obtain ⟨-, -, rfl, rfl, -, rfl, rfl, -, rfl⟩ := hargs8
  set sc5 := sc4 + 2 * L.fDel.length
  have hSt8Ag7 : ∀ addr < sc4, (addr < B.embPtr j ∨ B.fPtr j + B.levelSize ≤ addr) →
      st8.mem addr = st7.mem addr := fun addr hlt hout => hfr8 addr hlt (by omega)
  have hG8 : DynGraphAt st8.mem (solverG j) B.vCap B.eCap a.G :=
    hG7.of_agree fun addr _ _ => hSt8Ag7 addr (by omega) (by rcases hGOffBlk with h | h <;> omega)
  have hNewF8 : DynGraphAt st8.mem (B.fPtr j) B.vCap B.eCap newF :=
    hNewF7.of_agree fun addr _ _ => hSt8Ag7 addr (by omega) (Or.inl (by omega))
  have hUSAt8 : ListAt st8.mem uSPtr L.uS := fun i hi =>
    (hSt8Ag7 _ (by omega) (by rcases hUSOffBlk with h | h <;> omega)).trans
      ((hSt7Ag6 _ (by omega) (by rcases hUSOffBlk with h | h <;> omega)).trans (hUSAt6 i hi))
  have hSrcOk8 : ∀ e ∈ a.G.E \ newF.E,
      SelEmbSrcOk st8.mem w embTable B.slot (B.embPtr j) (B.embPtr j + B.eCap + B.eCap * B.slot) newEmb e ∧
      embTable + e < sc5 ∧
      st8.mem (embTable + e) + (mWalkEncode (newEmb e)).length ≤ sc5 := by
    intro e heDiff
    obtain ⟨⟨hsl, hmw, htw, htd, hww, hwk, hwd⟩, htl, hwl⟩ := hSrcOk7 e heDiff
    have hteq : st8.mem (embTable + e) = st7.mem (embTable + e) := hfr8 _ htl htd
    have hweq : ∀ t < (mWalkEncode (newEmb e)).length,
        st8.mem (st7.mem (embTable + e) + t) = st7.mem (st7.mem (embTable + e) + t) :=
      fun t ht => hfr8 _ (by omega) (by rcases hwd with h | h <;> [left; right] <;> omega)
    refine ⟨⟨hsl, fun t ht => by rw [hteq, hweq t ht]; exact hmw t ht, htw, htd,
      by rw [hteq]; exact hww, fun t ht => by rw [hteq, hweq t ht]; exact hwk t ht,
      by rw [hteq]; exact hwd⟩, by omega, by rw [hteq]; omega⟩
  -- Step 4: `embUpdateFromList` on `L.uS`
  obtain ⟨b8b, hb8b, o8b, st8b, c8b, hr8b, hp8b, hc8b⟩ :=
    hEmbUpd L.uS [dgEPresBase (solverG j) B.vCap, dgEPresBase (B.fPtr j) B.vCap, embTable,
      B.embPtr j, B.eCap, B.slot, uSPtr, L.uS.length, sc5] st8.mem st8.pos ω
      (by unfold dgEPresBase; wram_words)
      ⟨solverG j, B.fPtr j, embTable, B.embPtr j, B.slot, uSPtr, sc5, rfl, hw16,
        by omega, by omega, by omega, by omega, hG8, hNewF8, hUSAt8, hListCaps.2.2.1,
        fun e _ heDiff => hSrcOk8 e heDiff, hsc5Eq ▸ hz8, by omega⟩
  obtain ⟨_, _, _, _, _, _, _, hargs8b, hsc5bEq, hz8b, hcop8b, hfr8b, hkeep8b⟩ := hp8b
  simp only [List.cons.injEq, and_true] at hargs8b
  obtain ⟨-, -, rfl, rfl, -, rfl, rfl, -, rfl⟩ := hargs8b
  set sc5b := sc5 + 2 * L.uS.length
  have hSt8bAg8 : ∀ addr < sc5, (addr < B.embPtr j ∨ B.fPtr j + B.levelSize ≤ addr) →
      st8b.mem addr = st8.mem addr := fun addr hlt hout => hfr8b addr hlt (by omega)
  have hG8b : DynGraphAt st8b.mem (solverG j) B.vCap B.eCap a.G :=
    hG8.of_agree fun addr _ _ => hSt8bAg8 addr (by omega) (by rcases hGOffBlk with h | h <;> omega)
  have hNewF8b : DynGraphAt st8b.mem (B.fPtr j) B.vCap B.eCap newF :=
    hNewF8.of_agree fun addr _ _ => hSt8bAg8 addr (by omega) (Or.inl (by omega))
  have hReembAt8b : ListAt st8b.mem reembPtr L.reemb := fun i hi =>
    (hSt8bAg8 _ (by omega) (by rcases hReembOffBlk with h | h <;> omega)).trans
      ((hSt8Ag7 _ (by omega) (by rcases hReembOffBlk with h | h <;> omega)).trans
        ((hSt7Ag6 _ (by omega) (by rcases hReembOffBlk with h | h <;> omega)).trans (hReembAt6 i hi)))
  have hSrcOk8b : ∀ e ∈ a.G.E \ newF.E,
      SelEmbSrcOk st8b.mem w embTable B.slot (B.embPtr j) (B.embPtr j + B.eCap + B.eCap * B.slot) newEmb e ∧
      embTable + e < sc5b ∧
      st8b.mem (embTable + e) + (mWalkEncode (newEmb e)).length ≤ sc5b := by
    intro e heDiff
    obtain ⟨⟨hsl, hmw, htw, htd, hww, hwk, hwd⟩, htl, hwl⟩ := hSrcOk8 e heDiff
    have hteq : st8b.mem (embTable + e) = st8.mem (embTable + e) := hfr8b _ htl htd
    have hweq : ∀ t < (mWalkEncode (newEmb e)).length,
        st8b.mem (st8.mem (embTable + e) + t) = st8.mem (st8.mem (embTable + e) + t) :=
      fun t ht => hfr8b _ (by omega) (by rcases hwd with h | h <;> [left; right] <;> omega)
    refine ⟨⟨hsl, fun t ht => by rw [hteq, hweq t ht]; exact hmw t ht, htw, htd,
      by rw [hteq]; exact hww, fun t ht => by rw [hteq, hweq t ht]; exact hwk t ht,
      by rw [hteq]; exact hwd⟩, by omega, by rw [hteq]; omega⟩
  -- Step 5: `embUpdateFromList` on `L.reemb`
  obtain ⟨b9, hb9, o9, st9, c9, hr9, hp9, hc9⟩ :=
    hEmbUpd L.reemb [dgEPresBase (solverG j) B.vCap, dgEPresBase (B.fPtr j) B.vCap, embTable,
      B.embPtr j, B.eCap, B.slot, reembPtr, L.reemb.length, sc5b] st8b.mem st8b.pos ω
      (by unfold dgEPresBase; wram_words)
      ⟨solverG j, B.fPtr j, embTable, B.embPtr j, B.slot, reembPtr, sc5b, rfl, hw16,
        by omega, by omega, by omega, by omega, hG8b, hNewF8b, hReembAt8b, hListCaps.2.2.2,
        fun e _ heDiff => hSrcOk8b e heDiff, hsc5bEq ▸ hz8b, by omega⟩
  obtain ⟨_, _, _, _, _, _, _, hargs9, hsc6Eq, hz9, hcop9, hfr9, hkeep9⟩ := hp9
  simp only [List.cons.injEq, and_true] at hargs9
  obtain ⟨-, -, rfl, rfl, -, rfl, rfl, -, rfl⟩ := hargs9
  set sc6 := sc5b + 2 * L.reemb.length
  have hSt9Ag6 : ∀ addr < sc3, (addr < B.embPtr j ∨ B.fPtr j + B.levelSize ≤ addr) →
      st9.mem addr = st6.mem addr := fun addr hlt hout =>
    (hfr9 addr (by omega) (by omega)).trans
      ((hSt8bAg8 addr (by omega) hout).trans ((hSt8Ag7 addr (by omega) hout).trans (hSt7Ag6 addr hlt hout)))
  -- Final `SelBlocksDataAt` and `R.rep` on `st9.mem`
  have hblk9 : SelBlocksDataAt st9.mem B fmt.precision
      { D with coreE := Function.update D.coreE j newCoreE
               emb := Function.update D.emb j newEmb } pLast := by
    let m9b : ℕ → ℕ := fun addr => if addr < scratch then st9.mem addr else st6.mem addr
    have hEmbPart9 : SelPartEmb m9b B j newCoreE newEmb := by
      intro e heCore
      have heDiff : e ∈ a.G.E \ newF.E := heCore
      have heCap : e < B.eCap := hG.2.2.1 e (Finset.mem_sdiff.mp heDiff).1
      have hslotLe : (mWalkEncode (newEmb e)).length ≤ B.slot := hEmbSlot e heCore
      have hslotEnd : e * B.slot + B.slot ≤ B.eCap * B.slot := by
        have := Nat.mul_le_mul_right B.slot (Nat.succ_le_of_lt heCap)
        rw [Nat.succ_mul] at this; exact this
      have hm9Ent : m9b (B.embPtr j + e) = st9.mem (B.embPtr j + e) := by
        simp [m9b, show B.embPtr j + e < scratch by omega]
      have hm9Sl : ∀ t < B.slot, m9b (B.slotPtr j e + t) = st9.mem (B.slotPtr j e + t) :=
        fun t ht => by unfold SelectBlocksLoc.slotPtr; simp [m9b, show B.embPtr j + B.eCap + e * B.slot + t < scratch by omega]
      refine ⟨heCap, ?_, hslotLe, ?_⟩
      · by_cases hR : e ∈ L.reemb
        · rw [hm9Ent]; exact (hcop9 e hR heDiff).1
        · rw [hm9Ent, (hkeep9 e heCap (Or.inl hR)).1]
          by_cases hUS : e ∈ L.uS
          · exact (hcop8b e hUS heDiff).1
          · rw [(hkeep8b e heCap (Or.inl hUS)).1]
            by_cases hFD : e ∈ L.fDel
            · exact (hcop8 e hFD heDiff).1
            · rw [(hkeep8 e heCap (Or.inl hFD)).1]
              by_cases hUG : e ∈ L.uG
              · exact (hcop7 e hUG heDiff).1
              · rw [(hkeep7 e heCap (Or.inl hUG)).1]
                obtain ⟨heOld, _⟩ := hEmbUnchanged e heCore hUG hFD hUS hR
                exact (hblk6.2.2.2.1 j hj e heOld).2.1
      · intro t ht
        have htSl : t < B.slot := lt_of_lt_of_le ht hslotLe
        rw [hm9Sl t htSl]; unfold SelectBlocksLoc.slotPtr
        by_cases hR : e ∈ L.reemb
        · exact (hcop9 e hR heDiff).2 t ht
        · rw [(hkeep9 e heCap (Or.inl hR)).2 t htSl]
          by_cases hUS : e ∈ L.uS
          · exact (hcop8b e hUS heDiff).2 t ht
          · rw [(hkeep8b e heCap (Or.inl hUS)).2 t htSl]
            by_cases hFD : e ∈ L.fDel
            · exact (hcop8 e hFD heDiff).2 t ht
            · rw [(hkeep8 e heCap (Or.inl hFD)).2 t htSl]
              by_cases hUG : e ∈ L.uG
              · exact (hcop7 e hUG heDiff).2 t ht
              · rw [(hkeep7 e heCap (Or.inl hUG)).2 t htSl]
                obtain ⟨heOld, hembEq⟩ := hEmbUnchanged e heCore hUG hFD hUS hR
                have hold := (hblk6.2.2.2.1 j hj e heOld).2.2.2 t (by simpa only [← hembEq] using ht)
                simpa only [SelectBlocksLoc.slotPtr, ← hembEq] using hold
    have hblk9b := hblk6.setEmb hj (fun addr ha => by
      dsimp only [m9b]; split_ifs with hlt
      · exact hSt9Ag6 addr (by omega) (by unfold SelectBlocksLoc.regEmb at ha; omega)
      · rfl) hEmbPart9
    exact hblk9b.of_agree fun addr _ _ => by simp [m9b, show addr < scratch by omega]
  have hY6Ag9 : ∀ addr, R.foot handle y6 addr → st9.mem addr = st6.mem addr := fun addr hfy => by
    have hlt : addr < sc3 := by
      rcases hft6 addr hfy with hfx | hnew
      · exact lt_of_lt_of_le (hFootLt addr hfx) hsc3Lo
      · exact hnew.2
    have hout : addr < B.embPtr j ∨ B.fPtr j + B.levelSize ≤ addr := by
      by_contra hc
      exact hDisjY6Blk addr
        (by unfold SelectBlocksLoc.embPtr SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr at hc; omega)
        (by omega) hfy
    exact hSt9Ag6 addr hlt hout
  have hrep9 : R.rep handle a y6 st9.mem :=
    (hLocalR handle a y6 st6.mem st9.mem fun addr ha => (hY6Ag9 addr ha).symm).1 hrep6
  have hphi9 : R.phi handle y6 st9.mem = R.phi handle y6 st6.mem :=
    ((hLocalR handle a y6 st6.mem st9.mem fun addr ha => (hY6Ag9 addr ha).symm).2).symm
  -- Stitch the 18 setup assignments + 5 calls + 1 assign + ret
  suffices hMain : ∃ o stF cost,
      Runs w p ω (selectUpdateEmbLevelBody (op 4) embUpdateFromList)
        (startState [metaBase, j, slot, handle, branch, B.slot, scratch] mem pos) o stF cost ∧
      (o = .returned sc6 ∧ stF.mem = st9.mem) ∧
      cost ≤ c6 + c7 + c8 + c8b + c9 + 300 by
    obtain ⟨_, stF, cost, hrun, ⟨rfl, hmemEq⟩, hcost⟩ := hMain
    refine ⟨sc6, cost, stF, y6, hrun, by omega, by omega, hmemEq ▸ hrep9, hmemEq ▸ hblk9,
      hmemEq ▸ hsc6Eq ▸ hz9,
      fun addr hfy => Or.elim (hft6 addr hfy) Or.inl (fun hnew => Or.inr ⟨by omega, by omega⟩),
      fun addr hlt hnx hne => hmemEq ▸
        (hSt9Ag6 addr (by omega) (by unfold SelectBlocksLoc.regEmb at hne; omega)).trans
          (hfr6 addr hlt hnx), ?_⟩
    simp only [selEmbUpdateFromListContract, selectUpdateEmbCost, List.getD_cons_zero,
      List.getD_cons_succ] at hc7 hc8 hc8b hc9 ⊢
    change c6 + R.phi handle y6 st6.mem ≤ Psc.readout + R.phi handle x mem at hcost6
    rw [hmemEq, hphi9]; omega
  apply runs_start_le
  unfold selectUpdateEmbLevelBody
  have hEntryLt : ∀ blk ≤ 6, smEntryAddr metaBase B.d blk j < 2 ^ w := fun blk hblk => by
    have hm := Nat.mul_le_mul_right (B.d + 1) hblk
    unfold smEntryAddr smTableOff; omega
  refine runs_seq_assign_flat (v := B.d)
    (by simp [Expr.eval, BinOp.eval, startState, hdM, show 1 < 2 ^ w by omega,
          show metaBase + 1 < 2 ^ w by omega, show B.d < 2 ^ w by omega]) ?_
  refine runs_seq_assign_flat (v := B.d + 1)
    (by simp [Expr.eval, BinOp.eval, Function.update, show 1 < 2 ^ w by omega,
          show B.d + 1 < 2 ^ w by omega]) ?_
  refine runs_seq_assign_flat (v := metaBase + smTableOff)
    (by simp [Expr.eval, BinOp.eval, Function.update, startState,
          show smTableOff < 2 ^ w by unfold smTableOff; omega,
          show metaBase + smTableOff < 2 ^ w by unfold smTableOff; omega]) ?_
  refine runs_seq_assign_flat (v := solverG j)
    (by simp [Expr.eval, BinOp.eval, Function.update, startState,
          show metaBase + smTableOff + j = smEntryAddr metaBase B.d 0 j by unfold smEntryAddr; omega,
          hEntryLt 0 (by omega), hgPtrM, show solverG j < 2 ^ w by omega]) ?_
  refine runs_seq_assign_flat (v := B.vCap)
    (by simp [Expr.eval, BinOp.eval, Function.update, startState,
          show metaBase + smTableOff + (B.d + 1) + j = smEntryAddr metaBase B.d 1 j by
            unfold smEntryAddr; omega,
          show metaBase + smTableOff + (B.d + 1) < 2 ^ w by unfold smTableOff; omega,
          hEntryLt 1 (by omega), hvCapM, show B.vCap < 2 ^ w by omega]) ?_
  refine runs_seq_assign_flat (v := B.eCap)
    (by simp [Expr.eval, BinOp.eval, Function.update, startState,
          show 2 < 2 ^ w by omega, show 2 * (B.d + 1) < 2 ^ w by omega,
          show metaBase + smTableOff + 2 * (B.d + 1) < 2 ^ w by unfold smTableOff; omega,
          show metaBase + smTableOff + 2 * (B.d + 1) + j = smEntryAddr metaBase B.d 2 j by
            unfold smEntryAddr; omega,
          hEntryLt 2 (by omega), heCapM, show B.eCap < 2 ^ w by omega]) ?_
  refine runs_seq_assign_flat (v := B.embPtr j)
    (by simp [Expr.eval, BinOp.eval, Function.update, startState,
          show 5 < 2 ^ w by omega, show 5 * (B.d + 1) < 2 ^ w by omega,
          show metaBase + smTableOff + 5 * (B.d + 1) < 2 ^ w by unfold smTableOff; omega,
          show metaBase + smTableOff + 5 * (B.d + 1) + j = smEntryAddr metaBase B.d 5 j by
            unfold smEntryAddr; omega,
          hEntryLt 5 (by omega), hembM, show B.embPtr j < 2 ^ w by omega]) ?_
  refine runs_seq_assign_flat (v := B.fPtr j)
    (by simp [Expr.eval, BinOp.eval, Function.update, startState,
          show 6 < 2 ^ w by omega, show 6 * (B.d + 1) < 2 ^ w by omega,
          show metaBase + smTableOff + 6 * (B.d + 1) < 2 ^ w by unfold smTableOff; omega,
          show metaBase + smTableOff + 6 * (B.d + 1) + j = smEntryAddr metaBase B.d 6 j by
            unfold smEntryAddr; omega,
          hEntryLt 6 (by omega), hfM, show B.fPtr j < 2 ^ w by omega]) ?_
  refine runs_seq_assign_flat (v := dgEPresBase (solverG j) B.vCap)
    (by simp [Expr.eval, BinOp.eval, Function.update, show 4 < 2 ^ w by omega,
          show 7 < 2 ^ w by omega, show solverG j + 4 < 2 ^ w by omega,
          show 7 * B.vCap < 2 ^ w by omega,
          show solverG j + 4 + 7 * B.vCap = dgEPresBase (solverG j) B.vCap from rfl,
          show dgEPresBase (solverG j) B.vCap < 2 ^ w by unfold dgEPresBase; omega]) ?_
  refine runs_seq_assign_flat (v := dgEPresBase (B.fPtr j) B.vCap)
    (by simp [Expr.eval, BinOp.eval, Function.update, show 4 < 2 ^ w by omega,
          show 7 < 2 ^ w by omega, show B.fPtr j + 4 < 2 ^ w by omega,
          show 7 * B.vCap < 2 ^ w by omega,
          show B.fPtr j + 4 + 7 * B.vCap = dgEPresBase (B.fPtr j) B.vCap from rfl,
          show dgEPresBase (B.fPtr j) B.vCap < 2 ^ w by unfold dgEPresBase; omega]) ?_
  refine runs_seq_assign_flat (v := uGPtr)
    (by simp [Expr.eval, Function.update, startState, show slot < 2 ^ w by omega,
          show uGPtr < 2 ^ w by omega, uGPtr]) ?_
  refine runs_seq_assign_flat (v := L.uG.length)
    (by simp [Expr.eval, BinOp.eval, Function.update, startState, show 1 < 2 ^ w by omega,
          show slot + 1 < 2 ^ w by omega, hDiff.1, show L.uG.length < 2 ^ w by omega]) ?_
  refine runs_seq_assign_flat (v := fDelPtr)
    (by simp [Expr.eval, BinOp.eval, Function.update, startState, show 2 < 2 ^ w by omega,
          show slot + 2 < 2 ^ w by omega, show fDelPtr < 2 ^ w by omega, fDelPtr]) ?_
  refine runs_seq_assign_flat (v := L.fDel.length)
    (by simp [Expr.eval, BinOp.eval, Function.update, startState, show 3 < 2 ^ w by omega,
          show slot + 3 < 2 ^ w by omega, hDiff.2.2.1, show L.fDel.length < 2 ^ w by omega]) ?_
  refine runs_seq_assign_flat (v := uSPtr)
    (by simp [Expr.eval, BinOp.eval, Function.update, startState, show 4 < 2 ^ w by omega,
          show slot + 4 < 2 ^ w by omega, show uSPtr < 2 ^ w by omega, uSPtr]) ?_
  refine runs_seq_assign_flat (v := L.uS.length)
    (by simp [Expr.eval, BinOp.eval, Function.update, startState, show 5 < 2 ^ w by omega,
          show slot + 5 < 2 ^ w by omega, hDiff.2.2.2.2.1, show L.uS.length < 2 ^ w by omega]) ?_
  refine runs_seq_assign_flat (v := reembPtr)
    (by simp [Expr.eval, BinOp.eval, Function.update, startState, show 6 < 2 ^ w by omega,
          show slot + 6 < 2 ^ w by omega, show reembPtr < 2 ^ w by omega, reembPtr]) ?_
  refine runs_seq_assign_flat (v := L.reemb.length)
    (by simp [Expr.eval, BinOp.eval, Function.update, startState, show 7 < 2 ^ w by omega,
          show slot + 7 < 2 ^ w by omega, hDiff.2.2.2.2.2.2.1, show L.reemb.length < 2 ^ w by omega]) ?_
  refine runs_seq_call_e (by simp [evalArgs, Expr.eval, Function.update, startState]) hb6 hr6 ?_
  refine runs_seq_assign_flat (v := embTable)
    (by simp [Expr.eval, Function.update, startState, show scratch < 2 ^ w by omega,
          hEmbTabW, embTable]) ?_
  refine runs_seq_call_e (by simp [evalArgs, Expr.eval, Function.update, startState, sc3]) hb7 hr7 ?_
  refine runs_seq_call_e (by simp [evalArgs, Expr.eval, Function.update, startState, hsc4Eq, sc4]) hb8 hr8 ?_
  refine runs_seq_call_e (by simp [evalArgs, Expr.eval, Function.update, startState, hsc5Eq, sc5]) hb8b hr8b ?_
  refine runs_seq_call_e (by simp [evalArgs, Expr.eval, Function.update, startState, hsc5bEq, sc5b]) hb9 hr9 ?_
  refine ⟨.returned sc6, _, _,
    runs_ret_iff.mpr ⟨sc6, by simp [Expr.eval, Function.update, hsc6Eq, sc6], rfl, rfl, rfl⟩,
    ⟨rfl, rfl⟩, ?_⟩
  simp only [Expr.size, argsSize]
  omega

end MinCostFlow.MinRatio
