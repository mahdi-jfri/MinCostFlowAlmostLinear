module

public import MinCostFlow.MinRatio.SelectInitLoop
public import MinCostFlow.MinRatio.SelectCopyValues
import WordRAM.Tactic

/-!
# End-to-end select-region initialization (`SelectInitBody`)

Composes the five verified select-initialization stages into one fixed Word-RAM procedure
`selectInitRegionBody`:
1. `selectRegionSkeletonBody`: allocates `SelectRegion sb loc B metaBase` on zeroed memory from
   `sb`, stores `sb` at `hbCell` (`table + 4 * d + 2`) and `B.base` at `hbCell + 1`
   (`table + 4 * d + 3`), initializes `SelectHeapAt loc 4 0`, `SelectMetaTableAt`, and empty
   `SelBlocksDataAt B`.
2. `selCopyValuesBody`: copies `g_0` on `(G 0).E` into `B.g0Ptr`.
3. `selectInitInteriorLoopBody`: populates `B.fPtr j`, `B.lenPtr j` (`shift = 0`,
   `chainLen ℓ (j + 1)`), and `B.embPtr j` across interior levels `0 .. d - 1`, threading
   `Rcore.rep` and `Rcore.phi` inside `solverStateRepFull`.
4. `selectFillLastLevelBody`: populates `B.lastGPtr`, `B.fPtr d`, and `B.lenPtr d`
   (`shift = pLast`, `chainLen ℓ (d + 1)`) at terminal level `d`.
5. `selectInitFinalizeBody`: runs `selectPhiLoop` and `selectRebuildSuffix` from level `0` to
   establish `solverStateRepSel.rep root model (tokFull', sg) out.mem` with
   `sg.owned = fun a => sb ≤ a ∧ a < B.endAddr` and `sg.reembPot = chainReembPot pot model.chain`
   (whose initial potential `K * sg.reembPot` is bounded by `K * model.chain.totalRuntime` via
   `chainReembPot_init_le`).
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine Num DynSpanner.Program SparseCore.Program
open MinCostFlow.LastLevelProgram

/-- End-to-end select-region initializer.
Arguments (`reg 0..13`):
`[sb, cap, d, vCap, eCap, Lk, slot, levelTable, lvlMeta, pLast, hbCell, g0Src, srcGd, l0Ptr]`.
Returns the new scratch pointer above the select region and all readout/rebuild scratch. -/
def selectInitRegionBody
    (skelProc copyValProc intLoopProc fillLastProc finalizeProc : ℕ) : Stmt :=
  .call 14 skelProc
    [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 8, .reg 9, .reg 10] ;;
  .assign 15 (.load (.bin .add (.reg 0) (.const 12))) ;; -- B.g0Ptr
  .assign 16 (.load (.bin .add (.reg 0) (.const 13))) ;; -- metaBase
  .cond (.reg 2)
    (.assign 17 (.load (.bin .add (.reg 8) (.reg 2)))) -- G_0 = mem[lvlMeta + d]
    (.assign 17 (.reg 12)) ;; -- d = 0 => G_0 = srcGd
  .assign 18 (.load (.bin .add (.reg 17) (.const 3))) ;; -- (G_0).m
  .assign 19 (.bin .add (.bin .add (.bin .add (.reg 17) (.const 4)) (.bin .mul (.const 7) (.reg 3)))
    (.reg 4)) ;; -- dgEListBase G_0 vCap eCap
  .call 20 copyValProc [.reg 11, .reg 15, .reg 19, .reg 18, .reg 5] ;;
  .call 14 intLoopProc
    [.reg 16, .const 0, .reg 2, .reg 7, .reg 8, .reg 5, .reg 6, .reg 14] ;;
  .assign 21 (.load (.bin .add (.reg 7) (.reg 2))) ;; -- termHandle
  .assign 22 (.load (.bin .add (.bin .add (.reg 7) (.bin .add (.reg 2) (.const 1))) (.reg 2))) ;; -- termBran
  .cond (.reg 2)
    (.assign 23 (.load (.bin .add (.bin .add (.bin .add (.reg 16) (.const 2))
      (.bin .mul (.const 4) (.bin .add (.reg 2) (.const 1)))) (.bin .sub (.reg 2) (.const 1))))) -- B.lenPtr (d - 1)
    (.assign 23 (.reg 13)) ;; -- d = 0 => l0Ptr
  .call 14 fillLastProc
    [.reg 16, .reg 2, .reg 21, .reg 22, .reg 23, .reg 5, .reg 9, .reg 12, .reg 14] ;;
  .call 14 finalizeProc [.reg 0, .reg 16, .reg 2, .reg 5, .reg 14] ;;
  .ret (.reg 14)

theorem selectInitRegionBody_noRand (a b c d e : ℕ) :
    (selectInitRegionBody a b c d e).NoRand := by
  simp [selectInitRegionBody, Stmt.NoRand]

/-- Total space above `B.endAddr` used during `selectInitRegionBody` (readouts + fills + finalize). -/
noncomputable def selectInitRegionScratch {T : SparseCoreRestartTool} {P : ChainParams}
    (C : ChainState T P) (cap L capExp evalSpace : ℕ) : ℕ :=
  selectInitInteriorLoopSpace C 0 L capExp +
  selectFillLastLevelSpace (C.G P.d).m (C.lastLSFs C.lastBran).F.F.m L +
  selectInitFinalizeSpace C.toTreeChain cap L evalSpace

/-- Total step cost bound for `selectInitRegionBody`. -/
noncomputable def selectInitRegionCost {T : SparseCoreRestartTool} {P : ChainParams}
    (C : ChainState T P) (readoutCost cap L capExp slot evalCost : ℕ) : ℕ :=
  selectRegionSkeletonCost P.d +
  ((C.G 0).m * (18 * L + 50) + 20) +
  selectInitInteriorLoopCost C readoutCost 0 L capExp slot +
  selectFillLastLevelCost 0 0 0 0 (C.G P.d).n (C.G P.d).m
    (C.lastLSFs C.lastBran).F.F.n (C.lastLSFs C.lastBran).F.F.m L +
  selectInitFinalizeCost C.toTreeChain cap L evalCost + 240

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine Num DynSpanner.Program SparseCore.Program
open MinCostFlow.LastLevelProgram

private lemma selectMlocOf_congr_body {B : SelectBlocksLoc} {metaBase pLast : ℕ}
    {g₁ g₂ : ℕ → ℕ} (h : ∀ j < B.d, g₁ j = g₂ j) :
    selectMlocOf B metaBase g₁ pLast = selectMlocOf B metaBase g₂ pLast := by
  unfold selectMlocOf; congr 1
  · funext j; by_cases hj : j < B.d <;> simp [hj]; exact h j hj
  · funext j; by_cases hj : j < B.d <;> by_cases hj1 : j + 1 < B.d <;> simp [hj, hj1] <;> exact h (j + 1) hj1

private lemma reg_in_blocks_body {B : SelectBlocksLoc} {j a : ℕ} (hj : j ≤ B.d)
    (h : B.regLast a ∨ B.regF j a ∨ B.regLen j a) : B.base ≤ a ∧ a < B.endAddr := by
  have h1 : B.base ≤ B.fPtr j := by unfold SelectBlocksLoc.fPtr; omega
  have h2 := B.blk_le_last hj
  have h3 : B.lastGPtr ≤ B.endAddr := by unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr; omega
  have h4 : B.base ≤ B.lastGPtr := by unfold SelectBlocksLoc.lastGPtr; omega
  unfold SelectBlocksLoc.levelSize at h2
  rcases h with h | h | h
  · unfold SelectBlocksLoc.regLast at h; unfold SelectBlocksLoc.endAddr; omega
  · unfold SelectBlocksLoc.regF SelectBlocksLoc.phiPtr at h; omega
  · unfold SelectBlocksLoc.regLen SelectBlocksLoc.embPtr SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr at h; omega

set_option maxHeartbeats 1600000 in
/-- **Main select-region initialization theorem**:
`selectInitRegionBody` allocates and populates `SelectRegion sb loc B metaBase` on zeroed memory
starting at `sb`, writes `sb` to `table + dMul * d + kOff` and `B.base` to
`table + dMul * d + kOff + 1`, and establishes `solverStateRepSel.rep root model (tokFull', sg)`
with `sg.owned = fun a => sb ≤ a ∧ a < B.endAddr`, `sg.reembPot = chainReembPot pot model.chain`,
and `SolverLevelCapsInv`. -/
theorem selectInitRegion_runs
    {w L P m V psi k epsExp drainUnit unit toolMul treeMul dMul kOff K : ℕ}
    {depth capExp vCap eCap sb pLast slot g0Src g0SrcCap srcGd srcVCap srcECap l0Ptr
      evalSpace evalCost pos : ℕ}
    {skelProc copyValProc intLoopProc fillIntProc fillLastProc finalizeProc
      dgCopyProc coreLenProc filterProc embCopyProc phiLoopProc phiFillProc
      rebuildSuffixProc rebuildLvlProc : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {κ : ℝ} {G G₀ initialGraph : MGraph}
    {σ σ_mwu γ_ℓ γ_c : ℝ} {Psc : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {pot : cfg.T.State → ℕ}
    {p : Program} {op : ℕ → ℕ} {ω : ℕ → Bool}
    {root : ℕ} {model : Alg2State cfg}
    {tokFull : (solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul Rcore).τ}
    {mem : ℕ → ℕ} {PhiBd : (ℕ → ℕ → ℝ) → ℕ → Prop}
    (hfmt4 : fmt.limbBits = 4) (hfmtP : fmt.precision = P) (hlocalCore : Rcore.Local)
    (hw16 : 16 < 2 ^ w) (hw10 : 10 ≤ w) (hLkW : L < 2 ^ w) (hSlotW : slot < 2 ^ w)
    (hpLastW : pLast < 2 ^ w) (hkW : cfg.P.k < 2 ^ w)
    (hrepFull : (solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul
      Rcore).rep root model tokFull mem)
    (hFootBelow : ∀ a, (solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul
      treeMul Rcore).foot root tokFull a → a < sb)
    (hhbMeta : LevelMetaFoot tokFull.1.1 (tokFull.1.1.table + dMul * cfg.P.d + kOff))
    (hhbTagOff : ∀ a, a = tokFull.1.1.table + dMul * cfg.P.d + kOff ∨
        a = tokFull.1.1.table + dMul * cfg.P.d + kOff + 1 →
      (∀ v, 1 ≤ v → v ≤ 20 + cfg.P.d → tokFull.1.1.tag a ≠ v) ∧
      tokFull.1.1.tag a ≠ 22 + cfg.P.d ∧ tokFull.1.1.tag a ≠ 23 + cfg.P.d)
    (hhbBelow : tokFull.1.1.table + dMul * cfg.P.d + kOff + 1 < sb)
    (hhbDisjMeta : tokFull.1.1.table + dMul * cfg.P.d + kOff + 1 < solverN0Addr tokFull.1.1.table cfg.P.d ∨
      solverLevelMetaAddr tokFull.1.1.table cfg.P.d + 2 * cfg.P.d ≤ tokFull.1.1.table + dMul * cfg.P.d + kOff)
    (hMetaBelow : tokFull.1.1.handle + 18 + 2 * (cfg.P.d + 1) ≤ sb ∧
      solverLevelMetaAddr tokFull.1.1.table cfg.P.d + 2 * cfg.P.d + 1 ≤ sb ∧
      ∀ j < cfg.P.d,
        mem (solverLevelMetaAddr tokFull.1.1.table cfg.P.d + j) + eCap * L ≤ sb ∧
        solverLevelG tokFull.1.1 mem j + dynGraphSize vCap eCap ≤ sb)
    (hcaps : SolverLevelCapsInv P V vCap eCap model tokFull.1.1 mem)
    (hmod : SelectModelInv model G₀ σ σ_mwu γ_ℓ γ_c)
    (hg0Src : EdgeValuesAt mem g0Src 4 L P (model.chain.G 0).E model.chain.g)
    (hg0SrcCap : ∀ e ∈ (model.chain.G 0).E, e < g0SrcCap)
    (hg0SrcEnd : g0Src + g0SrcCap * L ≤ sb)
    (hg0SrcOffHb : ∀ a, a = tokFull.1.1.table + dMul * cfg.P.d + kOff ∨
        a = tokFull.1.1.table + dMul * cfg.P.d + kOff + 1 → a < g0Src ∨ g0Src + g0SrcCap * L ≤ a)
    (hSrcGd : DynGraphAt mem srcGd srcVCap srcECap (model.chain.G cfg.P.d))
    (hSrcGdEnd : srcGd + dynGraphSize srcVCap srcECap ≤ sb)
    (hSrcGdOffHb : ∀ a, a = tokFull.1.1.table + dMul * cfg.P.d + kOff ∨
        a = tokFull.1.1.table + dMul * cfg.P.d + kOff + 1 →
      a < srcGd ∨ srcGd + dynGraphSize srcVCap srcECap ≤ a)
    (hSrcGdOffCore : ∀ j < cfg.P.d, ∀ a, srcGd ≤ a → a < srcGd + dynGraphSize srcVCap srcECap →
      ¬ Rcore.foot (tokFull.1.1.coreHandle j) (tokFull.1.1.coreTok j) a)
    (hl0 : cfg.P.d = 0 →
      EdgeValuesAt mem l0Ptr 4 L P (model.chain.G 0).E model.chain.ℓ ∧ l0Ptr + eCap * L ≤ sb ∧
      (∀ a, a = tokFull.1.1.table + dMul * cfg.P.d + kOff ∨
          a = tokFull.1.1.table + dMul * cfg.P.d + kOff + 1 → a < l0Ptr ∨ l0Ptr + eCap * L ≤ a) ∧
      srcVCap = vCap ∧ srcECap = eCap)
    (hScIn : ∀ j < cfg.P.d,
      SparseCoreOrdInput cfg.T cfg.P.k (model.chain.lvlM j) model.chain.N₀
        (model.chain.scState j) (model.chain.G j) (model.chain.levelOrd j)
        (model.chain.updCount j))
    (hBrLt : ∀ j < cfg.P.d, model.chain.bran j < cfg.P.k)
    (hLastBr : model.chain.lastBran < model.chain.lastK)
    (hTermBelow : tokFull.1.1.termTok ≤ sb)
    (hVcap : ∀ j ≤ cfg.P.d, ∀ v ∈ (model.chain.G j).V, v < vCap)
    (hEcap : ∀ j ≤ cfg.P.d, ∀ e ∈ (model.chain.G j).E, e < eCap)
    (hFV : ∀ j ≤ cfg.P.d, ∀ v ∈ (model.chain.toTreeChain.activeLSF j).F.F.V, v < vCap)
    (hFE : ∀ j ≤ cfg.P.d, ∀ e ∈ (model.chain.toTreeChain.activeLSF j).F.F.E, e < eCap)
    (hLenFitInt : ∀ j < cfg.P.d, ∀ e ∈ (model.chain.G j).E,
      ∃ q : ℤ, Num.Fits 4 L q ∧
        (q : ℝ) / (2 : ℝ) ^ P = model.chain.toTreeChain.chainLen model.chain.ℓ (j + 1) e)
    (hLenFitLast : ∀ e ∈ (model.chain.G cfg.P.d).E,
      (∃ q0 : ℤ, Num.Fits 4 L (q0 * (2 : ℤ) ^ pLast) ∧
        (q0 : ℝ) / (2 : ℝ) ^ P = model.chain.toTreeChain.chainLen model.chain.ℓ cfg.P.d e) ∧
      ∃ q : ℤ, Num.Fits 4 L q ∧
        (q : ℝ) / (2 : ℝ) ^ (P + pLast) =
          model.chain.toTreeChain.chainLen model.chain.ℓ (cfg.P.d + 1) e)
    (hEmbSlot : ∀ j < cfg.P.d,
      ∀ e ∈ (model.chain.toTreeChain.activeCore j).E,
        (mWalkEncode (model.chain.toTreeChain.activeEmb j e)).length ≤ slot)
    (hEcapHeap : ∀ j ≤ cfg.P.d, ∀ e ∈ (model.chain.G j).E, e < selectHeapCap cfg G m / 2)
    (hPhiBdStep : ∀ j ≤ cfg.P.d, ∀ (φ : ℕ → ℕ → ℝ) (φj : ℕ → ℝ),
      (∀ k < j, SelectPotInvAt model.chain.toTreeChain model.chain.g φ k) → (∀ k < j, PhiBd φ k) →
      (∀ v ∈ (model.chain.toTreeChain.activeLSF j).F.F.V, ∃ r ∈ (model.chain.toTreeChain.activeLSF j).F.F.V,
        (model.chain.toTreeChain.activeLSF j).F.F.Connected v r ∧
        φj v = walkInner (potGrad model.chain.toTreeChain model.chain.g φ j) ((model.chain.toTreeChain.activeLSF j).F.F.forestPath v r)) →
      ∀ k < j + 1, PhiBd (Function.update φ j φj) k)
    (hFitPhi : ∀ j ≤ cfg.P.d, ∀ φ' : ℕ → ℕ → ℝ,
      (∀ k < j, SelectPotInvAt model.chain.toTreeChain model.chain.g φ' k) → (∀ k < j, PhiBd φ' k) →
      (∀ e ∈ (model.chain.toTreeChain.activeLSF j).F.F.E, PotGradEvalFits 4 L P model.chain.toTreeChain model.chain.g φ' j e) ∧
      ForestWalkFits 4 L P (model.chain.toTreeChain.activeLSF j).F.F (potGrad model.chain.toTreeChain model.chain.g φ' j))
    (hSkel : MeetsContract w p skelProc
      (selectRegionSkeletonContract w P sb (selectHeapCap cfg G m) cfg.P.d vCap eCap L slot
        (solverLevelMetaAddr tokFull.1.1.table cfg.P.d) pLast
        (tokFull.1.1.table + dMul * cfg.P.d + kOff)))
    (hCopyVal : ∀ eL : List ℕ, MeetsContract w p copyValProc (selCopyValuesContractSrc w g0SrcCap eCap eL))
    (hpIntLoop : p.procs[intLoopProc]? = some (selectInitInteriorLoopBody intLoopProc fillIntProc))
    (hpFillInt : p.procs[fillIntProc]? =
      some (selectFillInteriorLevelBody (op 2) (op 4) dgCopyProc coreLenProc filterProc embCopyProc))
    (hpFillLast : p.procs[fillLastProc]? = some (selectFillLastLevelBody dgCopyProc coreLenProc))
    (hpFinalize : p.procs[finalizeProc]? = some (selectInitFinalizeBody phiLoopProc rebuildSuffixProc))
    (hFootAt : ∀ j < cfg.P.d,
      SparseCoreReadoutFootAt fmt L depth cfg.T initialGraph cfg.P.k
        (model.chain.lvlM j) model.chain.N₀ vCap eCap capExp Psc allocation Rcore p op)
    (hDgCopy : ∀ G_new : MGraph, ∀ vcS ecS,
      MeetsContract w p dgCopyProc (dgCopyRefillContract w vCap eCap vcS ecS dgEmptyGraph G_new))
    (hCoreLen : ∀ eL : List ℕ, MeetsContract w p coreLenProc (selCoreLenFillContract w P eCap eL))
    (hFilter : ∀ eL : List ℕ, MeetsContract w p filterProc (selFilterAbsentContract w eL))
    (hEmbCopy : ∀ j < cfg.P.d, ∀ eL : List ℕ,
      MeetsContract w p embCopyProc (selEmbCopyContract w eL (model.chain.toTreeChain.activeEmb j)))
    (hpPhiLoop : p.procs[phiLoopProc]? = some (selectPhiLoopBody phiLoopProc phiFillProc))
    (hPhiFill :
      let mloc := selectMlocOf ⟨sb + selectHeapSize (selectHeapCap cfg G m) cfg.P.d L + selectLevelMetaSize cfg.P.d,
        cfg.P.d, vCap, eCap, L, slot⟩ (sb + selectHeapSize (selectHeapCap cfg G m) cfg.P.d L) (solverLevelG tokFull.1.1 mem) pLast
      ∀ φ : ℕ → ℕ → ℝ, MeetsContract w p phiFillProc
        (selectPhiFillContract w 4 P mloc model.chain.toTreeChain G₀ model.chain.g model.chain.ℓ σ σ_mwu γ_ℓ γ_c φ))
    (hpRebSuf : p.procs[rebuildSuffixProc]? = some (selectRebuildSuffixBody rebuildSuffixProc rebuildLvlProc))
    (hRebLvl :
      let cap := selectHeapCap cfg G m
      let metaBase := sb + selectHeapSize cap cfg.P.d L
      let B : SelectBlocksLoc := ⟨metaBase + selectLevelMetaSize cfg.P.d, cfg.P.d, vCap, eCap, L, slot⟩
      ∀ φ : ℕ → ℕ → ℝ, MeetsContract w p rebuildLvlProc
        (selectRebuildLevelContract w 4 P ⟨sb, cap, cfg.P.d, L, B.g0Ptr, metaBase⟩
          (selectMlocOf B metaBase (solverLevelG tokFull.1.1 mem) pLast) model.chain.toTreeChain model.chain.g
          model.chain.ℓ φ (fun j => model.chain.toTreeChain.chainLen model.chain.ℓ (j + 1)) evalSpace evalCost))
    (hz : ZeroFrom mem sb)
    (hroom :
      let metaBase := sb + selectHeapSize (selectHeapCap cfg G m) cfg.P.d L
      (⟨metaBase + selectLevelMetaSize cfg.P.d, cfg.P.d, vCap, eCap, L, slot⟩ : SelectBlocksLoc).endAddr +
        selectInitRegionScratch model.chain (selectHeapCap cfg G m) L capExp evalSpace < 2 ^ w) :
    let cap := selectHeapCap cfg G m
    let metaBase := sb + selectHeapSize cap cfg.P.d L
    let B : SelectBlocksLoc := ⟨metaBase + selectLevelMetaSize cfg.P.d, cfg.P.d, vCap, eCap, L, slot⟩
    let Rfull := solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul Rcore
    let Rsel := solverStateRepSel cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul
      dMul kOff Rcore K pot
    ∃ scOut cost out tokFull' sg,
      Runs w p ω (selectInitRegionBody skelProc copyValProc intLoopProc fillLastProc finalizeProc)
        (startState [sb, cap, cfg.P.d, vCap, eCap, L, slot, tokFull.1.1.handle + 18,
          solverLevelMetaAddr tokFull.1.1.table cfg.P.d, pLast,
          tokFull.1.1.table + dMul * cfg.P.d + kOff, g0Src, srcGd, l0Ptr] mem pos)
        (.returned scOut) out cost ∧
      B.endAddr ≤ scOut ∧
      scOut ≤ B.endAddr + selectInitRegionScratch model.chain cap L capExp evalSpace ∧
      Rsel.rep root model (tokFull', sg) out.mem ∧
      sg.owned = (fun a => sb ≤ a ∧ a < B.endAddr) ∧
      sg.reembPot = chainReembPot pot model.chain ∧
      tokFull'.1.1.tree = tokFull.1.1.tree ∧ tokFull'.1.1.trees = tokFull.1.1.trees ∧
      tokFull'.1.1.edgeRecords = tokFull.1.1.edgeRecords ∧
      SolverLevelCapsInv P V vCap eCap model tokFull'.1.1 out.mem ∧
      out.mem (tokFull'.1.1.table + dMul * cfg.P.d + kOff) = sb ∧
      out.mem (tokFull'.1.1.table + dMul * cfg.P.d + kOff + 1) = B.base ∧
      (out.mem (solverSelectHeapAddr tokFull'.1.1.table cfg.P.d) = sb →
        out.mem (solverSelectBlocksAddr tokFull'.1.1.table cfg.P.d) = B.base →
        SolverSelectBlocksInv G L P m vCap eCap pLast B model (Rfull.foot root tokFull')
          tokFull'.1.1 sg out.mem) ∧
      (∀ j ≤ cfg.P.d, PhiBd sg.φ j) ∧
      ZeroFrom out.mem scOut ∧
      (∀ a < sb, a ≠ tokFull.1.1.table + dMul * cfg.P.d + kOff →
        a ≠ tokFull.1.1.table + dMul * cfg.P.d + kOff + 1 →
        ¬ (∃ j < cfg.P.d, Rcore.foot (tokFull.1.1.coreHandle j) (tokFull.1.1.coreTok j) a) →
        out.mem a = mem a) ∧
      (∀ a, Rsel.foot root (tokFull', sg) a → Rfull.foot root tokFull a ∨ (sb ≤ a ∧ a < scOut)) ∧
      cost + Rsel.phi root (tokFull', sg) out.mem ≤
        selectInitRegionCost model.chain Psc.readout cap L capExp slot evalCost +
          Rfull.phi root tokFull mem + K * chainReembPot pot model.chain := by
  intro cap metaBase B Rfull Rsel
  change B.endAddr + selectInitRegionScratch model.chain cap L capExp evalSpace < 2 ^ w at hroom
  set hbCell := tokFull.1.1.table + dMul * cfg.P.d + kOff
  set lvlMeta := solverLevelMetaAddr tokFull.1.1.table cfg.P.d
  set levelTable := tokFull.1.1.handle + 18
  set loc : SelectHeapLoc := ⟨sb, cap, cfg.P.d, L, B.g0Ptr, metaBase⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, htags0⟩ := hrepFull.1.1
  obtain ⟨hOwn0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hCoreTags⟩ := htags0
  have hBaseLeEnd : B.base ≤ B.endAddr := by rw [B.endAddr_eq]; omega
  have hsbLeBase : sb ≤ B.base := by
    have : sb ≤ sb + selectHeapSize cap cfg.P.d L := Nat.le_add_right _ _
    change sb ≤ metaBase + selectLevelMetaSize cfg.P.d; omega
  have hEndW : B.endAddr < 2 ^ w := by omega
  have hSpDef : selectInitRegionScratch model.chain cap L capExp evalSpace =
      selectInitInteriorLoopSpace model.chain 0 L capExp +
      selectFillLastLevelSpace (model.chain.G cfg.P.d).m (model.chain.lastLSFs model.chain.lastBran).F.F.m L +
      selectInitFinalizeSpace model.chain.toTreeChain cap L evalSpace := rfl
  have hw1 : 1 < 2 ^ w := by omega
  have hcapW : cap < 2 ^ w := by
    have : selectHeapSize cap cfg.P.d L = shHdrSize + (cfg.P.d + 1) + 5 * cap + 2 * (cap * L) := rfl
    change metaBase + selectLevelMetaSize cfg.P.d ≤ B.endAddr at hBaseLeEnd; omega
  have hdW : cfg.P.d < 2 ^ w := by
    have : selectLevelMetaSize cfg.P.d = 2 + 8 * (cfg.P.d + 1) := rfl
    change metaBase + selectLevelMetaSize cfg.P.d ≤ B.endAddr at hBaseLeEnd; omega
  have hCapW : vCap < 2 ^ w ∧ eCap < 2 ^ w := by
    have h1 : B.lastGPtr + dynGraphSize vCap eCap = B.g0Ptr := rfl
    have h2 : B.g0Ptr + eCap * L = B.endAddr := rfl
    have h3 : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
    have h4 : B.base ≤ B.lastGPtr := by unfold SelectBlocksLoc.lastGPtr; omega
    exact ⟨by omega, by omega⟩
  obtain ⟨hvCapW, heCapW⟩ := hCapW
  -- Step 1: `selectRegionSkeletonBody`
  have hhbDisjSkel : hbCell + 1 < lvlMeta + cfg.P.d ∨ lvlMeta + 2 * cfg.P.d ≤ hbCell := by
    rcases hhbDisjMeta with h | h
    · left; unfold solverN0Addr at h; unfold lvlMeta solverLevelMetaAddr solverLvlMAddr solverN0Addr; omega
    · exact Or.inr h
  obtain ⟨bSk, hbSk, oSk, st1, cSk, hrSk, hpSk, hcSk⟩ :=
    hSkel [sb, cap, cfg.P.d, vCap, eCap, L, slot, lvlMeta, pLast, hbCell] mem pos ω
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro v (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)
          all_goals first | exact hcapW | exact hdW | exact hvCapW | exact heCapW | exact hLkW | exact hSlotW | exact hpLastW | omega)
      ⟨rfl, hw16, hhbBelow, hhbDisjSkel, by omega, hpLastW, hz, hEndW⟩
  obtain ⟨hsc0Eq, hreg, hhb1, hblkCell1, hHeap1, hTab1Raw, hblk1, hz1, hfr1⟩ := hpSk
  have hMetaEnd : metaBase + selectLevelMetaSize cfg.P.d ≤ B.base := le_of_eq hreg.2.2.2.1.symm
  have hMetaEndB : metaBase + selectLevelMetaSize B.d ≤ B.base := hMetaEnd
  have hLocEnd : loc.endAddr ≤ metaBase := by rw [loc.endAddr_eq]
  have hsb14 : sb + 14 ≤ B.endAddr := by
    have : selectHeapSize cap cfg.P.d L = shHdrSize + (cfg.P.d + 1) + 5 * cap + 2 * (cap * L) := rfl
    unfold shHdrSize at this; have h1 : sb + selectHeapSize cap cfg.P.d L = metaBase := hreg.2.2.1; omega
  have hTab1Eq : selTableOf B metaBase lvlMeta pLast mem =
      selectMlocOf B metaBase (solverLevelG tokFull.1.1 mem) pLast := by
    unfold selTableOf selectMlocOf solverLevelG; rfl
  have hTab1 : SelectMetaTableAt st1.mem (selectMlocOf B metaBase (solverLevelG tokFull.1.1 mem) pLast) :=
    hTab1Eq ▸ hTab1Raw
  obtain ⟨hrep1Core, hphi1Core⟩ :=
    solverStateRep_write_hbCells hlocalCore hrepFull.1.1
      (fun a ha v h1 h2 => (hhbTagOff a ha).1 v h1 h2)
      (fun a ha hne1 hne2 => hfr1 a (hFootBelow a (Or.inl ha)) hne1 hne2)
  have hrep1Full : Rfull.rep root model tokFull st1.mem :=
    ⟨⟨hrep1Core, hrepFull.1.2.1, hrepFull.1.2.2⟩, hrepFull.2.1, hrepFull.2.2.1, hrepFull.2.2.2⟩
  have hphi1Full : Rfull.phi root tokFull st1.mem = Rfull.phi root tokFull mem := by
    rw [solverStateRepFull_phi_eq (tok := tokFull) ⟨hrep1Core, hrepFull.1.2.1, hrepFull.1.2.2⟩
        hrepFull.2.2.1 hrepFull.2.2.2,
      solverStateRepFull_phi_eq (tok := tokFull) hrepFull.1 hrepFull.2.2.1 hrepFull.2.2.2, hphi1Core]
  have hcaps1 : SolverLevelCapsInv P V vCap eCap model tokFull.1.1 st1.mem :=
    solverLevelCapsInv_write_hbCells hcaps hOwn0 hhbDisjMeta
      (fun a ha => ⟨(hhbTagOff a ha).1 20 (by omega) (by omega), (hhbTagOff a ha).2.1, (hhbTagOff a ha).2.2⟩)
      (fun a ha hne1 hne2 => hfr1 a (hFootBelow a (Or.inl ha)) hne1 hne2)
  have hMlocEq1 : selectMlocOf B metaBase (solverLevelG tokFull.1.1 st1.mem) pLast =
      selectMlocOf B metaBase (solverLevelG tokFull.1.1 mem) pLast :=
    selectMlocOf_congr_body fun j hj => by
      change j < cfg.P.d at hj
      have htag := hcaps.1.2.2.2.2.1 (cfg.P.d + j) (by omega)
      rw [← Nat.add_assoc] at htag
      exact hfr1 _ (by omega) (fun h => (hhbTagOff _ (Or.inl h)).2.1 htag)
        (fun h => (hhbTagOff _ (Or.inr h)).2.1 htag)
  -- Step 2: Copy `g0` into `B.g0Ptr` via `selCopyValues`
  let g0Graph : ℕ := if cfg.P.d ≠ 0 then solverLevelG tokFull.1.1 st1.mem 0 else srcGd
  have hG0DG1 : DynGraphAt st1.mem g0Graph vCap eCap (model.chain.G 0) := by
    dsimp only [g0Graph]
    by_cases hd0 : cfg.P.d = 0
    · simp only [hd0, ne_eq, not_true_eq_false, ↓reduceIte]
      have hdg := DynGraphAt.of_agree hSrcGd fun a h1 h2 =>
        hfr1 a (by omega) (fun h => by have := hSrcGdOffHb a (Or.inl h); omega)
          (fun h => by have := hSrcGdOffHb a (Or.inr h); omega)
      obtain ⟨_, _, _, hvcEq, hecEq⟩ := hl0 hd0
      rw [← hvcEq, ← hecEq, ← hd0]; exact hdg
    · simp only [hd0, ne_eq, not_false_eq_true, ↓reduceIte]
      exact (SolverLevelMetaAt.atCaps hcaps1.1 hcaps1.2 0 (Nat.pos_of_ne_zero hd0)).1
  have hG0End1 : g0Graph + dynGraphSize vCap eCap ≤ sb := by
    dsimp only [g0Graph]; split_ifs with hd0
    · have h0 := Nat.pos_of_ne_zero hd0
      have htag := hcaps.1.2.2.2.2.1 (cfg.P.d + 0) (by omega)
      rw [← Nat.add_assoc] at htag
      have heq : solverLevelG tokFull.1.1 st1.mem 0 = solverLevelG tokFull.1.1 mem 0 :=
        hfr1 _ (by omega) (fun h => (hhbTagOff _ (Or.inl h)).2.1 htag)
          (fun h => (hhbTagOff _ (Or.inr h)).2.1 htag)
      rw [heq]; exact (hMetaBelow.2.2 0 h0).2
    · obtain ⟨_, _, _, hvcEq, hecEq⟩ := hl0 (not_not.mp hd0)
      rw [← hvcEq, ← hecEq]; exact hSrcGdEnd
  obtain ⟨eL0, heL0_len, _, heL0_mem, heL0_at, _⟩ := hG0DG1.2.2.2.2.2.2.2.2.2.2.2.2.1
  have heL0_le : eL0.length ≤ eCap := by
    rw [heL0_len]; unfold MGraph.m
    calc (model.chain.G 0).E.card ≤ (Finset.range eCap).card :=
          Finset.card_le_card fun e he => Finset.mem_range.mpr (hEcap 0 (Nat.zero_le _) e he)
      _ = eCap := Finset.card_range _
  have hg0Src1 : EdgeValuesAt st1.mem g0Src 4 L P (model.chain.G 0).E model.chain.g :=
    EdgeValuesAt.congr hg0Src fun e he t ht => by
      have heC := hg0SrcCap e he
      have hmul : e * L + t < g0SrcCap * L := by
        have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt heC); rw [Nat.succ_mul] at this; omega
      exact hfr1 _ (by omega)
        (fun h => by have := hg0SrcOffHb _ (Or.inl h); omega)
        (fun h => by have := hg0SrcOffHb _ (Or.inr h); omega)
  have hg0PtrBase : B.base ≤ B.g0Ptr := by
    unfold SelectBlocksLoc.g0Ptr SelectBlocksLoc.lastGPtr; omega
  have hg0PtrEnd : B.g0Ptr + eCap * L = B.endAddr := rfl
  have hDgSz : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  obtain ⟨bCV, hbCV, oCV, st2, cCV, hrCV, hpCV, hcCV⟩ :=
    hCopyVal eL0 [g0Src, B.g0Ptr, dgEListBase g0Graph vCap eCap, eL0.length, L] st1.mem st1.pos ω
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro v (rfl|rfl|rfl|rfl|rfl)
          all_goals first | exact hLkW | (unfold dgEListBase; omega) | omega)
      ⟨g0Src, B.g0Ptr, dgEListBase g0Graph vCap eCap, L, rfl, hw16, by omega, by omega,
        by unfold dgEListBase; omega, Or.inl (by omega), Or.inl (by unfold dgEListBase; omega),
        heL0_at, fun e he => ⟨hg0SrcCap e ((heL0_mem e).mp he), hEcap 0 (Nat.zero_le _) e ((heL0_mem e).mp he)⟩,
        fun e he t ht => lt_trans ((hg0Src1 e ((heL0_mem e).mp he)).1 t ht) hw16⟩
  obtain ⟨_, _, _, _, hargsCV, _, hCV_cp, hFr2, _⟩ := hpCV
  simp only [List.cons.injEq] at hargsCV; obtain ⟨rfl, rfl, rfl, -, rfl, -⟩ := hargsCV
  have hFr2BelowG0 : ∀ a < B.g0Ptr, st2.mem a = st1.mem a := fun a ha => hFr2 a (Or.inl ha)
  have hz2 : ZeroFrom st2.mem B.endAddr := fun a ha => (hFr2 a (Or.inr (by omega))).trans (hz1 a ha)
  have hblk2 : SelBlocksDataAt st2.mem B P
      { emptySelBlocksData with E0 := (model.chain.G 0).E, g := model.chain.g } pLast :=
    hblk1.setG0 (fun a ha => hFr2 a (by unfold SelectBlocksLoc.regG0 SelectBlocksLoc.endAddr at ha; change ¬ (B.g0Ptr ≤ a ∧ a < B.g0Ptr + eCap * L) at ha; omega))
      ⟨fun e he => hEcap 0 (Nat.zero_le _) e he, fun e he => by
        have h1 := hg0Src1 e he
        refine ⟨fun t ht => by rw [hCV_cp e ((heL0_mem e).mpr he) t ht]; exact h1.1 t ht, ?_⟩
        unfold Num.fixVal; rw [Num.intVal_congr fun t ht => hCV_cp e ((heL0_mem e).mpr he) t ht]
        exact h1.2⟩
  have hRfullLocal := solverStateRepFull_local cfg κ G L P m V psi k epsExp drainUnit unit toolMul
    treeMul hlocalCore
  have hrep2Full : Rfull.rep root model tokFull st2.mem :=
    (hRfullLocal root model tokFull st1.mem st2.mem fun a ha =>
      (hFr2BelowG0 a (by have := hFootBelow a ha; omega)).symm).1 hrep1Full
  have hphi2Full : Rfull.phi root tokFull st2.mem = Rfull.phi root tokFull mem :=
    ((hRfullLocal root model tokFull st1.mem st2.mem fun a ha =>
      (hFr2BelowG0 a (by have := hFootBelow a ha; omega)).symm).2).symm.trans hphi1Full
  have hcaps2 : SolverLevelCapsInv P V vCap eCap model tokFull.1.1 st2.mem :=
    hcaps1.preserve rfl hcaps1.1.2.1
      (fun a ha => ⟨rfl, hFr2BelowG0 a (by
        have hne : tokFull.1.1.tag a ≠ 0 := by rcases ha with h | h | h | h <;> omega
        have := hFootBelow a (Or.inl (hOwn0 a hne)); omega)⟩)
      (fun j hj => (SolverLevelMetaAt.atCaps hcaps1.1 hcaps1.2 j hj).2.2.1)
      rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl
  have hMlocEq2 : selectMlocOf B metaBase (solverLevelG tokFull.1.1 st2.mem) pLast =
      selectMlocOf B metaBase (solverLevelG tokFull.1.1 mem) pLast :=
    (selectMlocOf_congr_body fun j hj => by change j < cfg.P.d at hj; exact hFr2BelowG0 _ (by omega)).trans hMlocEq1
  have hTab2 : SelectMetaTableAt st2.mem (selectMlocOf B metaBase (solverLevelG tokFull.1.1 st2.mem) pLast) := by
    rw [hMlocEq2]; exact hTab1.of_agree fun a _ ha2 => hFr2BelowG0 a (by simp only [selectMlocOf] at ha2; omega)
  have hHeap2 : SelectHeapAt st2.mem loc 4 0 :=
    hHeap1.of_agree fun a _ ha2 => hFr2BelowG0 a (by change a < loc.endAddr at ha2; omega)
  have hMetaBelow2 : tokFull.1.1.handle + 18 + 2 * (cfg.P.d + 1) ≤ sb ∧
      solverLevelMetaAddr tokFull.1.1.table cfg.P.d + 2 * cfg.P.d ≤ sb ∧
      ∀ j < cfg.P.d,
        st2.mem (solverLevelMetaAddr tokFull.1.1.table cfg.P.d + j) + eCap * L ≤ sb ∧
        solverLevelG tokFull.1.1 st2.mem j + dynGraphSize vCap eCap ≤ sb := by
    refine ⟨hMetaBelow.1, by omega, fun j hj => ?_⟩
    have htagL := hcaps.1.2.2.2.2.1 j (by omega)
    have htagG := hcaps.1.2.2.2.2.1 (cfg.P.d + j) (by omega)
    rw [← Nat.add_assoc] at htagG
    have heqL : st2.mem (solverLevelMetaAddr tokFull.1.1.table cfg.P.d + j) =
        mem (solverLevelMetaAddr tokFull.1.1.table cfg.P.d + j) :=
      (hFr2BelowG0 _ (by omega)).trans (hfr1 _ (by omega)
        (fun h => (hhbTagOff _ (Or.inl h)).2.1 htagL) (fun h => (hhbTagOff _ (Or.inr h)).2.1 htagL))
    have heqG : solverLevelG tokFull.1.1 st2.mem j = solverLevelG tokFull.1.1 mem j :=
      (hFr2BelowG0 _ (by omega)).trans (hfr1 _ (by omega)
        (fun h => (hhbTagOff _ (Or.inl h)).2.1 htagG) (fun h => (hhbTagOff _ (Or.inr h)).2.1 htagG))
    rw [heqL, heqG]; exact hMetaBelow.2.2 j hj
  -- Step 3: `selectInitInteriorLoopBody` (`0 .. d - 1`)
  obtain ⟨sc3, cInt, st3, tokFull3, hrInt, hsc3Lo, hsc3Hi, hrep3Full, htab3Eq, hhnd3Eq, hth3Eq,
      htt3Eq, hvc3Eq, hec3Eq, htr3Eq, htrs3Eq, hrec3Eq, hft3, hOwn3, hTagLt3, hTag3, hcaps3, hTab3, hHeap3, hblk3, hz3,
      hfr3, hcInt⟩ :=
    selectInitInteriorLoop_runs (depth := depth) (capExp := capExp)
      (vCap := vCap) (eCap := eCap) (sb := sb) (metaBase := metaBase) (pLast := pLast)
      (cur := 0) (scratch := B.endAddr) (pos := st2.pos)
      (loopProc := intLoopProc) (fillIntProc := fillIntProc) (dgCopyProc := dgCopyProc)
      (coreLenProc := coreLenProc) (filterProc := filterProc) (embCopyProc := embCopyProc)
      (fmt := fmt) (cfg := cfg) (κ := κ) (G := G) (initialGraph := initialGraph)
      (Psc := Psc) (allocation := allocation) (Rcore := Rcore) (p := p) (op := op) (ω := ω)
      hfmt4 hfmtP hlocalCore hw16 hLkW hSlotW hkW (Nat.zero_le _) hreg rfl rfl rfl rfl
      hrep2Full (fun a ha => lt_of_lt_of_le (hFootBelow a ha) (by omega))
      (fun a h1 _ hf => by have := hFootBelow a hf; omega)
      (fun j _ hj a ha => hFootBelow a (Or.inr (Or.inr ⟨j, hj, ha⟩)))
      hMetaBelow2 (le_refl _) hcaps2 hTab2 hHeap2 hblk2 (fun _ _ _ => rfl)
      (fun j _ hj => hScIn j hj) (fun j _ hj => hBrLt j hj)
      (fun j _ hj => hFV j (Nat.le_of_lt hj)) (fun j _ hj => hFE j (Nat.le_of_lt hj))
      (fun j _ hj => hLenFitInt j hj) (fun j _ hj => hEmbSlot j hj)
      hpIntLoop hpFillInt (fun j _ hj => hFootAt j hj)
      (fun j _ hj vcF ecF => hDgCopy _ vcF ecF) hCoreLen hFilter
      (fun j _ hj eL => hEmbCopy j hj eL) hz2 (by omega)
  -- Step 4: `selectFillLastLevelBody` (level `d`)
  have hFr3BelowOffCore : ∀ a < sb,
      ¬ (∃ j < cfg.P.d, Rcore.foot (tokFull.1.1.coreHandle j) (tokFull.1.1.coreTok j) a) →
      st3.mem a = st1.mem a := fun a ha hnc =>
    (hfr3 a ha fun ⟨j, _, hj, hc⟩ => hnc ⟨j, hj, hc⟩).trans (hFr2BelowG0 a (by omega))
  have hhb3 : st3.mem hbCell = sb :=
    (hFr3BelowOffCore hbCell (by omega) (fun ⟨j, hj, hc⟩ =>
      (hhbTagOff hbCell (Or.inl rfl)).1 (21 + j) (by omega) (by omega) (hCoreTags j hj hbCell hc))).trans hhb1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTermH3, hTermBr3, hTermRep3, _, htags3⟩ := hrep3Full.1.1
  have hOwn3Tag : ∀ a, tokFull3.1.1.tag a ≠ 0 → tokFull3.1.1.owned a := htags3.1
  have hSrcGd3 : DynGraphAt st3.mem srcGd srcVCap srcECap (model.chain.G cfg.P.d) :=
    DynGraphAt.of_agree hSrcGd fun a h1 h2 =>
      (hFr3BelowOffCore a (by omega) (fun ⟨j, hj, hc⟩ => hSrcGdOffCore j hj a h1 h2 hc)).trans
        (hfr1 a (by omega) (fun h => by have := hSrcGdOffHb a (Or.inl h); omega)
          (fun h => by have := hSrcGdOffHb a (Or.inr h); omega))
  let prevLenD : ℕ := if cfg.P.d ≠ 0 then B.lenPtr (cfg.P.d - 1) else l0Ptr
  have hPrevVal3 : EdgeValuesAt st3.mem prevLenD 4 L P (model.chain.G cfg.P.d).E
      (model.chain.toTreeChain.chainLen model.chain.ℓ cfg.P.d) := by
    dsimp only [prevLenD]
    by_cases hd0 : cfg.P.d = 0
    · simp only [hd0, ne_eq, not_true_eq_false, ↓reduceIte]
      obtain ⟨hl0EV, hl0End, hl0Hb, _, _⟩ := hl0 hd0
      have hch0 : model.chain.toTreeChain.chainLen model.chain.ℓ 0 = model.chain.ℓ := rfl
      rw [hch0]
      exact EdgeValuesAt.congr hl0EV fun e he t ht => by
        have heC := hEcap 0 (Nat.zero_le _) e he
        have hmul : e * L + t < eCap * L := by
          have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt heC); rw [Nat.succ_mul] at this; omega
        exact (hFr3BelowOffCore _ (by omega) (fun ⟨j, hj, _⟩ => by omega)).trans
          (hfr1 _ (by omega) (fun h => by have := hl0Hb _ (Or.inl h); omega)
            (fun h => by have := hl0Hb _ (Or.inr h); omega))
    · simp only [hd0, ne_eq, not_false_eq_true, ↓reduceIte]
      have hdPos : 0 < cfg.P.d := Nat.pos_of_ne_zero hd0
      have hlt : cfg.P.d - 1 < cfg.P.d := by omega
      have hsubEq : cfg.P.d - 1 + 1 = cfg.P.d := by omega
      have hlenPrev := hblk3.2.2.1 (cfg.P.d - 1) (by change cfg.P.d - 1 ≤ cfg.P.d; omega)
      simp only [Nat.zero_le, hlt, and_self, ↓reduceIte, hsubEq] at hlenPrev
      have hSubE : (model.chain.G cfg.P.d).E ⊆ (model.chain.G (cfg.P.d - 1)).E := by
        obtain ⟨hbr, hLvl, _, hGeq⟩ := hmod.1.2.2.2.2.1 (cfg.P.d - 1) hlt
        change model.chain.G (cfg.P.d - 1 + 1) = _ at hGeq
        rw [hsubEq] at hGeq
        rw [hGeq]; exact (hLvl _ hbr).2.1.2.1.trans Finset.sdiff_subset
      exact fun e he => by
        have h1 := hlenPrev.2 e (hSubE he)
        simpa [coreLenPrec, B, hlt] using h1
  have hPrevBounds3 : (prevLenD + eCap * L ≤ B.lenPtr cfg.P.d ∨ B.embPtr cfg.P.d ≤ prevLenD) ∧
      (prevLenD + eCap * L ≤ B.fPtr cfg.P.d ∨ B.phiPtr cfg.P.d ≤ prevLenD) ∧
      (prevLenD + eCap * L ≤ B.lastGPtr ∨ B.g0Ptr ≤ prevLenD) ∧ prevLenD + eCap * L ≤ sc3 := by
    dsimp only [prevLenD]; split_ifs with hd0
    · have h1 := B.blk_le_of_lt (show cfg.P.d - 1 < cfg.P.d by omega)
      have h1' := B.blk_le_last (show cfg.P.d - 1 ≤ B.d from by change cfg.P.d - 1 ≤ cfg.P.d; omega)
      have h2 : B.lenPtr (cfg.P.d - 1) + eCap * L ≤ B.fPtr (cfg.P.d - 1) + B.levelSize := by
        unfold SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr SelectBlocksLoc.levelSize; dsimp only [B]; omega
      have h3 : B.fPtr cfg.P.d ≤ B.lenPtr cfg.P.d := by unfold SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr; omega
      have h4 : B.lastGPtr ≤ B.endAddr := by unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr; omega
      exact ⟨Or.inl (by omega), Or.inl (by omega), Or.inl (by omega), by omega⟩
    · obtain ⟨_, hl0End, _, _, _⟩ := hl0 (not_not.mp hd0)
      have h1 : B.base ≤ B.fPtr cfg.P.d := by unfold SelectBlocksLoc.fPtr; omega
      have h2 : B.fPtr cfg.P.d ≤ B.lenPtr cfg.P.d := by unfold SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr; omega
      have h3 : B.base ≤ B.lastGPtr := by unfold SelectBlocksLoc.lastGPtr; omega
      exact ⟨Or.inl (by omega), Or.inl (by omega), Or.inl (by omega), by omega⟩
  obtain ⟨hPrevDisj3, hPrevOff3, hPrevOffLast3, hPrevW⟩ := hPrevBounds3
  have hTermTok3 : tokFull3.1.1.termTok ≤ B.base := by rw [htt3Eq]; omega
  have hActLSFD : model.chain.toTreeChain.activeLSF cfg.P.d = model.chain.lastLSFs model.chain.lastBran := by
    simp [TreeChain.activeLSF, ChainState.toTreeChain]
  have hChainLenD1 : ∀ e, model.chain.toTreeChain.chainLen model.chain.ℓ (cfg.P.d + 1) e =
      (model.chain.lastLSFs model.chain.lastBran).wstr e *
        model.chain.toTreeChain.chainLen model.chain.ℓ cfg.P.d e := fun e => by
    rw [TreeChain.chainLen, hActLSFD]; rfl
  obtain ⟨sc4, cLast, st4, hrLast, hsc4Eq, hblk4, hz4, hfr4, hcLast⟩ :=
    selectFillLastLevel_runs (w := w) (P := P) (pLast := pLast)
      (dgCopyProc := dgCopyProc) (coreLenProc := coreLenProc)
      (B := B) (metaBase := metaBase) (termHandle := tokFull3.1.1.termHandle)
      (termBran := model.chain.lastBran) (prevLen := prevLenD)
      (srcGd := srcGd) (srcVCap := srcVCap) (srcECap := srcECap)
      (vcLast := tokFull3.1.1.vcLast) (ecLast := tokFull3.1.1.ecLast)
      (limit := tokFull3.1.1.termTok) (scratch := sc3) (pos := st3.pos)
      (solverG := solverLevelG tokFull3.1.1 st3.mem) (Gd := model.chain.G cfg.P.d)
      (lastK := model.chain.lastK) (lastLSFs := model.chain.lastLSFs)
      (prevVal := model.chain.toTreeChain.chainLen model.chain.ℓ cfg.P.d)
      (p := p) (ω := ω) (mem := st3.mem)
      hw16 hpLastW hLkW hTab3 hblk3 (by have := hreg.2.2.2.1; dsimp only [B]; omega) (by omega)
      hSrcGd3 (Or.inl (by omega)) (by omega)
      (hVcap cfg.P.d (le_refl _)) (hEcap cfg.P.d (le_refl _))
      hTermRep3 hLastBr hTermTok3
      (hActLSFD ▸ hFV cfg.P.d (le_refl _)) (hActLSFD ▸ hFE cfg.P.d (le_refl _))
      hPrevW hPrevDisj3 hPrevOff3 hPrevOffLast3 hPrevVal3
      (fun e he => by
        obtain ⟨⟨q0, hq0F, hq0Eq⟩, q, hqF, hqEq⟩ := hLenFitLast e he
        refine ⟨?_, q, hqF, by rw [hqEq, hChainLenD1]⟩
        have hEq := (hPrevVal3 e he).2
        have hQ0Eq : Num.intVal st3.mem (prevLenD + e * L) 4 L = q0 := by
          unfold Num.fixVal at hEq
          have hpos : (0 : ℝ) < (2 : ℝ) ^ P := by positivity
          have h1 : (Num.intVal st3.mem (prevLenD + e * L) 4 L : ℝ) = (q0 : ℝ) :=
            (div_left_inj' (ne_of_gt hpos)).mp (hEq.trans hq0Eq.symm)
          exact_mod_cast h1
        change Num.Fits 4 L (Num.intVal st3.mem (prevLenD + e * L) 4 L * (2 : ℤ) ^ pLast)
        rw [hQ0Eq]; exact hq0F)
      (by simpa [emptySelBlocksData] using hDgCopy (model.chain.G cfg.P.d) srcVCap srcECap)
      (by have hnot : ¬ (B.d < cfg.P.d) := by change ¬ (cfg.P.d < cfg.P.d); omega
          simpa [hnot, emptySelBlocksData] using hDgCopy (model.chain.lastLSFs model.chain.lastBran).F.F tokFull3.1.1.vcLast tokFull3.1.1.ecLast)
      hCoreLen hz3 (by change sc3 + selectFillLastLevelSpace (model.chain.G cfg.P.d).m (model.chain.lastLSFs model.chain.lastBran).F.F.m L < 2 ^ w; omega)
  change sc4 = sc3 + selectFillLastLevelSpace (model.chain.G cfg.P.d).m (model.chain.lastLSFs model.chain.lastBran).F.F.m L at hsc4Eq
  -- Step 5: `selectInitFinalizeBody` (`selectPhiLoop` + `selectRebuildSuffix` from `0`)
  have hFoot3Disj : ∀ a, sb ≤ a → a < B.endAddr → ¬ Rfull.foot root tokFull3 a := fun a h1 h2 hf3 => by
    rcases hft3 a hf3 with hf2 | hnew
    · have := hFootBelow a hf2; omega
    · omega
  have hFoot3Sc : ∀ a, Rfull.foot root tokFull3 a → a < sc3 := fun a ha => by
    rcases hft3 a ha with hf2 | hnew
    · have := hFootBelow a hf2; omega
    · exact hnew.2
  have hFr4OffReg : ∀ a < sc3, (a < sb ∨ B.endAddr ≤ a) → st4.mem a = st3.mem a := fun a ha hoff =>
    hfr4 a ha
      (fun hl => by have := reg_in_blocks_body (le_refl B.d) (Or.inl hl); omega)
      (fun hf => by have := reg_in_blocks_body (le_refl B.d) (Or.inr (Or.inl hf)); omega)
      (fun hl => by have := reg_in_blocks_body (le_refl B.d) (Or.inr (Or.inr hl)); omega)
  have hFr4Foot : ∀ a, Rfull.foot root tokFull3 a → st4.mem a = st3.mem a := fun a ha =>
    hFr4OffReg a (hFoot3Sc a ha) (by
      by_contra h; obtain ⟨h1, h2⟩ := not_or.mp h
      exact hFoot3Disj a (Nat.le_of_not_lt h1) (Nat.lt_of_not_le h2) ha)
  have hrep4Full : Rfull.rep root model tokFull3 st4.mem :=
    (hRfullLocal root model tokFull3 st3.mem st4.mem fun a ha => (hFr4Foot a ha).symm).1 hrep3Full
  have hphi4Full : Rfull.phi root tokFull3 st4.mem = Rfull.phi root tokFull3 st3.mem :=
    ((hRfullLocal root model tokFull3 st3.mem st4.mem fun a ha => (hFr4Foot a ha).symm).2).symm
  have hcaps4 : SolverLevelCapsInv P V vCap eCap model tokFull3.1.1 st4.mem :=
    hcaps3.preserve rfl hcaps3.1.2.1
      (fun a ha => ⟨rfl, hFr4Foot a (Or.inl (hOwn3Tag a (by rcases ha with h | h | h | h <;> omega)))⟩)
      (fun j hj => (SolverLevelMetaAt.atCaps hcaps3.1 hcaps3.2 j hj).2.2.1)
      rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl
  have hGPtrEq43 : ∀ j < cfg.P.d, solverLevelG tokFull3.1.1 st4.mem j = solverLevelG tokFull3.1.1 st3.mem j := by
    intro j hj
    have htag := hcaps.1.2.2.2.2.1 (cfg.P.d + j) (by omega)
    rw [← Nat.add_assoc] at htag
    have hOwnG : tokFull.1.1.owned (solverLevelMetaAddr tokFull.1.1.table cfg.P.d + cfg.P.d + j) :=
      hOwn0 _ (by omega)
    unfold solverLevelG; rw [htab3Eq]; exact hFr4Foot _ (Or.inl (hOwn3 _ hOwnG))
  have hGPtrEq4 : ∀ j < cfg.P.d, solverLevelG tokFull3.1.1 st4.mem j = solverLevelG tokFull.1.1 mem j := by
    intro j hj
    have htag := hcaps.1.2.2.2.2.1 (cfg.P.d + j) (by omega)
    rw [← Nat.add_assoc] at htag
    have h32 : solverLevelG tokFull3.1.1 st3.mem j = solverLevelG tokFull.1.1 st2.mem j := by
      unfold solverLevelG; rw [htab3Eq]
      exact hfr3 _ (by omega) fun ⟨i, _, hi, hc⟩ => by have := hCoreTags i hi _ hc; omega
    have h21 : solverLevelG tokFull.1.1 st2.mem j = solverLevelG tokFull.1.1 mem j :=
      (hFr2BelowG0 _ (by omega)).trans (hfr1 _ (by omega)
        (fun h => (hhbTagOff _ (Or.inl h)).2.1 htag) (fun h => (hhbTagOff _ (Or.inr h)).2.1 htag))
    exact (hGPtrEq43 j hj).trans (h32.trans h21)
  have hMlocEq4 : selectMlocOf B metaBase (solverLevelG tokFull3.1.1 st4.mem) pLast =
      selectMlocOf B metaBase (solverLevelG tokFull.1.1 mem) pLast :=
    selectMlocOf_congr_body fun j hj => hGPtrEq4 j hj
  have hTab4 : SelectMetaTableAt st4.mem (selectMlocOf B metaBase (solverLevelG tokFull3.1.1 st4.mem) pLast) := by
    rw [selectMlocOf_congr_body fun j hj => hGPtrEq43 j hj]
    exact hTab3.of_agree fun a _ ha2 =>
      hfr4 a (by simp only [selectMlocOf] at ha2; omega)
        (fun hl => by have := reg_in_blocks_body (le_refl B.d) (Or.inl hl); simp only [selectMlocOf] at ha2; omega)
        (fun hf => by have := reg_in_blocks_body (le_refl B.d) (Or.inr (Or.inl hf)); simp only [selectMlocOf] at ha2; omega)
        (fun hl => by have := reg_in_blocks_body (le_refl B.d) (Or.inr (Or.inr hl)); simp only [selectMlocOf] at ha2; omega)
  have hHeap4 : SelectHeapAt st4.mem loc 4 0 :=
    hHeap3.of_agree fun a _ ha2 => by
      change a < loc.endAddr at ha2
      exact hfr4 a (by omega)
        (fun hl => by have := reg_in_blocks_body (le_refl B.d) (Or.inl hl); omega)
        (fun hf => by have := reg_in_blocks_body (le_refl B.d) (Or.inr (Or.inl hf)); omega)
        (fun hl => by have := reg_in_blocks_body (le_refl B.d) (Or.inr (Or.inr hl)); omega)
  have hhbMeta3 : LevelMetaFoot tokFull3.1.1 (tokFull3.1.1.table + dMul * cfg.P.d + kOff) := by
    have hne := hhbMeta.tag_ne_zero
    rw [htab3Eq]; unfold LevelMetaFoot at hhbMeta ⊢; rw [hTag3 _ hne]; exact hhbMeta
  have hhbFoot3 : Rfull.foot root tokFull3 (tokFull3.1.1.table + dMul * cfg.P.d + kOff) :=
    LevelMetaFoot.mem_foot hrep3Full.1.1 hhbMeta3
  have hhb4 : st4.mem (tokFull3.1.1.table + dMul * cfg.P.d + kOff) = loc.hb := by
    rw [hFr4Foot _ hhbFoot3, htab3Eq]; exact hhb3
  have hF4 : ∀ j ≤ cfg.P.d, SelPartF st4.mem B j (model.chain.toTreeChain.activeLSF j).F.F := fun j hj => by
    have h := hblk4.1 j hj
    by_cases hlt : j < cfg.P.d
    · simpa [Function.update, show j ≠ B.d from by change j ≠ cfg.P.d; omega, hlt] using h
    · obtain rfl : j = cfg.P.d := by omega
      dsimp only [B] at h ⊢; simpa [Function.update, hActLSFD] using h
  have hLen4 : ∀ j ≤ cfg.P.d,
      SelPartLen st4.mem B P j (model.chain.toTreeChain.G j).E
        (model.chain.toTreeChain.chainLen model.chain.ℓ (j + 1)) pLast := fun j hj => by
    have h := hblk4.2.2.1 j hj
    by_cases hlt : j < cfg.P.d
    · simpa [Function.update, show j ≠ B.d from by change j ≠ cfg.P.d; omega, hlt] using h
    · obtain rfl : j = cfg.P.d := by omega
      have hlenEq : (fun e => (model.chain.lastLSFs model.chain.lastBran).wstr e *
          model.chain.toTreeChain.chainLen model.chain.ℓ cfg.P.d e) =
          model.chain.toTreeChain.chainLen model.chain.ℓ (cfg.P.d + 1) := funext fun e => (hChainLenD1 e).symm
      change SelPartLen st4.mem B P cfg.P.d (model.chain.G cfg.P.d).E _ pLast
      dsimp only [B] at h ⊢; simpa [Function.update, hlenEq] using h
  have hEmb4 : ∀ j < cfg.P.d,
      SelPartEmb st4.mem B j (model.chain.toTreeChain.activeCore j).E
        (model.chain.toTreeChain.activeEmb j) := fun j hj => by
    simpa [Function.update, show j ≠ B.d from by change j ≠ cfg.P.d; omega, hj] using hblk4.2.2.2.1 j hj
  have hLast4 : SelPartLast st4.mem B (model.chain.toTreeChain.G cfg.P.d) := hblk4.2.2.2.2.1
  have hG04 : SelPartG0 st4.mem B P (model.chain.toTreeChain.G 0).E model.chain.g := hblk4.2.2.2.2.2
  obtain ⟨sc5, cFin, st5, sg, hrFin, hsc5Lo, hsc5Hi, hz5, hsgOwn, hsgReemb, hsgMloc, hrepSel5, hBlk5, hBd5, hFr5, hFrFoot5, hcFin⟩ :=
    selectInitFinalize_runs (dMul := dMul) (kOff := kOff) (K := K) (pot := pot)
      (vCap := vCap) (eCap := eCap) (sb := sb) (metaBase := metaBase) (pLast := pLast)
      (evalSpace := evalSpace) (evalCost := evalCost) (scratch := sc4) (pos := st4.pos)
      (phiLoopProc := phiLoopProc) (phiFillProc := phiFillProc)
      (rebuildSuffixProc := rebuildSuffixProc) (rebuildLvlProc := rebuildLvlProc)
      (G₀ := G₀) (σ := σ) (σ_mwu := σ_mwu) (γ_ℓ := γ_ℓ) (γ_c := γ_c)
      hlocalCore hw16 hw10 hLkW hpLastW hreg rfl rfl rfl rfl rfl hrep4Full
      (fun a ha => lt_of_lt_of_le (hFoot3Sc a ha) (by omega)) hFoot3Disj
      (fun j hj => by rw [hGPtrEq4 j hj]; exact (hMetaBelow.2.2 j hj).2)
      hhb4 hhbMeta3
      (fun j hj a ha1 ha2 => by
        have hMC := (solverLevelCapsInv_iff_metaCaps.mp hcaps4).2.2.2.2.2 j hj
        have htg := hMC.2.2.2.2 a ha1 ha2; unfold LevelMetaFoot; split_ifs at htg <;> omega)
      (fun j hj => by
        have htag := hcaps4.1.2.2.2.2.1 (cfg.P.d + j) (by omega)
        rw [← Nat.add_assoc] at htag; unfold LevelMetaFoot; omega)
      hcaps4 hmod hHeap4 hTab4 hF4 hLen4 hEmb4 hLast4 hG04 hVcap hEcapHeap (PhiBd := PhiBd) hPhiBdStep hFitPhi
      hpPhiLoop (by rw [hMlocEq4]; exact hPhiFill) hpRebSuf (by rw [hMlocEq4]; exact hRebLvl)
      (by change B.endAddr ≤ sc4; omega) hz4 (by change sc4 + selectInitFinalizeSpace model.chain.toTreeChain cap L evalSpace < 2 ^ w; omega)
  change sc5 ≤ sc4 + selectInitFinalizeSpace model.chain.toTreeChain cap L evalSpace at hsc5Hi
  change cFin ≤ selectInitFinalizeCost model.chain.toTreeChain cap L evalCost at hcFin
  let s0 := startState [sb, cap, cfg.P.d, vCap, eCap, L, slot, levelTable, lvlMeta, pLast,
    hbCell, g0Src, srcGd, l0Ptr] mem pos
  have hMainRun : ∃ o out cTot,
      Runs w p ω (selectInitRegionBody skelProc copyValProc intLoopProc fillLastProc finalizeProc)
        s0 o out cTot ∧ o = .returned sc5 ∧ out.mem = st5.mem ∧ cTot ≤ cSk + cCV + cInt + cLast + cFin + 180 := by
    unfold selectInitRegionBody
    refine runs_seq_call_ex2 (by simp [evalArgs, Expr.eval, s0, startState]) hbSk hrSk <|
      runs_seq_assign_ex2 (v := B.g0Ptr)
        (by simp [Expr.eval, BinOp.eval, s0, startState, show 12 < 2 ^ w by omega,
          show sb + 12 < 2 ^ w by omega, show st1.mem (sb + 12) = B.g0Ptr from hHeap1.1 12 (by simp)]) <|
      runs_seq_assign_ex2 (v := metaBase)
        (by simp [Expr.eval, BinOp.eval, s0, startState, show 13 < 2 ^ w by omega,
          show sb + 13 < 2 ^ w by omega, show st1.mem (sb + 13) = metaBase from hHeap1.1 13 (by simp)]) <|
      runs_seq_cond_assign_ex2 (vc := cfg.P.d) (v := g0Graph)
        (by simp [Expr.eval, s0, startState]) (by
          by_cases hd0 : cfg.P.d = 0
          · simp [hd0, g0Graph, Expr.eval, s0, startState]
          · simp [hd0, g0Graph, Expr.eval, BinOp.eval, s0, startState, solverLevelG, lvlMeta,
              show lvlMeta + cfg.P.d < 2 ^ w by omega]) <|
      runs_seq_assign_ex2 (v := (model.chain.G 0).m)
        (by simp [Expr.eval, BinOp.eval, show 3 < 2 ^ w by omega, show g0Graph + 3 < 2 ^ w by omega,
          show st1.mem (g0Graph + 3) = (model.chain.G 0).m from by simpa [dgMOff] using hG0DG1.2.2.2.2.2.2.1]) <|
      runs_seq_assign_ex2 (v := dgEListBase g0Graph vCap eCap)
        (by simp [Expr.eval, BinOp.eval, s0, startState, show 4 < 2 ^ w by omega, show 7 < 2 ^ w by omega,
          show g0Graph + 4 < 2 ^ w by omega, show 7 * vCap < 2 ^ w by omega,
          show g0Graph + 4 + 7 * vCap < 2 ^ w by omega,
          show g0Graph + 4 + 7 * vCap + eCap = dgEListBase g0Graph vCap eCap from rfl,
          show dgEListBase g0Graph vCap eCap < 2 ^ w by unfold dgEListBase; omega]) <|
      runs_seq_call_ex2 (by simp [evalArgs, Expr.eval, s0, startState, heL0_len]) hbCV hrCV <|
      runs_seq_call_ex2 (by simp [evalArgs, Expr.eval, s0, startState, show 0 < 2 ^ w by omega, levelTable, lvlMeta, B]; exact hsc0Eq)
        hpIntLoop hrInt <|
      runs_seq_assign_ex2 (v := tokFull3.1.1.termHandle)
        (by simp [Expr.eval, BinOp.eval, s0, startState, show levelTable + cfg.P.d < 2 ^ w by omega,
          show st3.mem (levelTable + cfg.P.d) = tokFull3.1.1.termHandle from by simpa [levelTable, hhnd3Eq] using hTermH3]) <|
      runs_seq_assign_ex2 (v := model.chain.lastBran)
        (by simp [Expr.eval, BinOp.eval, s0, startState, hw1, show cfg.P.d + 1 < 2 ^ w by omega,
          show levelTable + (cfg.P.d + 1) < 2 ^ w by omega, show levelTable + (cfg.P.d + 1) + cfg.P.d < 2 ^ w by omega,
          show st3.mem (levelTable + (cfg.P.d + 1) + cfg.P.d) = model.chain.lastBran from by simpa [levelTable, hhnd3Eq] using hTermBr3]) <|
      runs_seq_cond_assign_ex2 (vc := cfg.P.d) (v := prevLenD)
        (by simp [Expr.eval, s0, startState]) (by
          by_cases hd0 : cfg.P.d = 0
          · simp [hd0, prevLenD, Expr.eval, s0, startState]
          · have hrow := hTab3.2.2 (cfg.P.d - 1) (by change cfg.P.d - 1 ≤ cfg.P.d; omega)
            have hlenPrevM : st3.mem (metaBase + 2 + 4 * (cfg.P.d + 1) + (cfg.P.d - 1)) = B.lenPtr (cfg.P.d - 1) := by
              simpa [smEntryAddr, smTableOff, selectMlocOf] using hrow.2.2.2.2.1
            have hMetaSz : selectLevelMetaSize B.d = 2 + 8 * (cfg.P.d + 1) := rfl
            simp [hd0, prevLenD, Expr.eval, BinOp.eval, s0, startState, hw1,
              show 2 < 2 ^ w by omega, show 4 < 2 ^ w by omega,
              show cfg.P.d + 1 < 2 ^ w by omega, show cfg.P.d - 1 < 2 ^ w by omega,
              show 4 * (cfg.P.d + 1) < 2 ^ w by omega, show metaBase + 2 < 2 ^ w by omega,
              show metaBase + 2 + 4 * (cfg.P.d + 1) < 2 ^ w by omega,
              show metaBase + 2 + 4 * (cfg.P.d + 1) + (cfg.P.d - 1) < 2 ^ w by omega, hlenPrevM]) <|
      runs_seq_call_ex2 (by simp [evalArgs, Expr.eval, Outcome.value, s0, startState, B]) hpFillLast hrLast <|
      runs_seq_call_ex2 (by simp [evalArgs, Expr.eval, Outcome.value, s0, startState]) hpFinalize hrFin ?_
    refine ⟨.returned sc5, _, 2, runs_ret_iff.mpr ⟨sc5, by simp [Expr.eval, Outcome.value], rfl, rfl, rfl⟩, rfl, rfl, ?_⟩
    simp only [Expr.size, argsSize]; split_ifs <;> simp only [Expr.size] <;> omega
  obtain ⟨_, out, cTot, hrMain, rfl, hmemEq, hcTot⟩ := hMainRun
  have hCaps5 : SolverLevelCapsInv P V vCap eCap model tokFull3.1.1 out.mem := by
    rw [hmemEq]
    refine hcaps4.preserve rfl hcaps4.1.2.1 (fun a ha => ⟨rfl, hFrFoot5 a (Or.inl (hOwn3Tag a (by rcases ha with h | h | h | h <;> omega)))⟩)
      (fun j hj => (SolverLevelMetaAt.atCaps hcaps4.1 hcaps4.2 j hj).2.2.1)
      rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl
  have hhbOut : out.mem (tokFull3.1.1.table + dMul * cfg.P.d + kOff) = sb := by
    rw [hmemEq, hFrFoot5 _ hhbFoot3]; exact hhb4
  have hblkCellOut : out.mem (tokFull3.1.1.table + dMul * cfg.P.d + kOff + 1) = B.base := by
    rw [hmemEq, htab3Eq]
    exact (hFr5 (hbCell + 1) (by omega)).trans <| (hFr4OffReg (hbCell + 1) (by omega) (Or.inl (by omega))).trans <|
      (hFr3BelowOffCore (hbCell + 1) (by omega) fun ⟨j, hj, hc⟩ =>
        (hhbTagOff (hbCell + 1) (Or.inr rfl)).1 (21 + j) (by omega) (by omega) (hCoreTags j hj (hbCell + 1) hc)).trans hblkCell1
  refine ⟨sc5, cTot, out, tokFull3, sg, hrMain, by omega, by omega,
    hmemEq ▸ hrepSel5, hsgOwn, hsgReemb, htr3Eq, htrs3Eq, hrec3Eq, hCaps5, hhbOut, hblkCellOut,
    fun h1 h2 => by rw [hmemEq] at h1 h2 ⊢; exact hBlk5 h1 h2, hBd5, hmemEq ▸ hz5,
    fun a ha hne1 hne2 hnc => by
      rw [hmemEq]
      exact (hFr5 a ha).trans ((hFr4OffReg a (by omega) (Or.inl ha)).trans
        ((hFr3BelowOffCore a ha hnc).trans (hfr1 a ha hne1 hne2))),
    fun a ha => ?_, ?_⟩
  · rcases ha with hf | hown
    · exact (hft3 a hf).imp_right fun h => ⟨by omega, by omega⟩
    · rw [hsgOwn] at hown; exact Or.inr ⟨hown.1, lt_of_lt_of_le (show a < B.endAddr from hown.2) (by omega)⟩
  · rw [hmemEq]
    have hPhiSel : Rsel.phi root (tokFull3, sg) st5.mem = Rfull.phi root tokFull3 st4.mem + K * chainReembPot pot model.chain := by
      dsimp only [Rsel, solverStateRepSel]
      rw [hsgReemb, ((hRfullLocal root model tokFull3 st4.mem st5.mem fun a ha => (hFrFoot5 a ha).symm).2).symm]
    simp only [selectRegionSkeletonContract, selCopyValuesContractSrc, List.getD_cons_zero, List.getD_cons_succ, heL0_len] at hcSk hcCV
    have hnotD : ¬ (0 ≤ B.d ∧ B.d < cfg.P.d) := by change ¬ (0 ≤ cfg.P.d ∧ cfg.P.d < cfg.P.d); omega
    simp only [hnotD, ↓reduceIte, emptySelBlocksData, dgEmptyGraph, MGraph.n, MGraph.m, Finset.card_empty] at hcLast
    change cLast ≤ selectFillLastLevelCost 0 0 0 0 (model.chain.G cfg.P.d).n (model.chain.G cfg.P.d).m
      (model.chain.lastLSFs model.chain.lastBran).F.F.n (model.chain.lastLSFs model.chain.lastBran).F.F.m L at hcLast
    change cInt + Rfull.phi root tokFull3 st3.mem ≤ selectInitInteriorLoopCost model.chain Psc.readout 0 L capExp slot + Rfull.phi root tokFull st2.mem at hcInt
    rw [hPhiSel, hphi4Full, selectInitRegionCost]; rw [hphi2Full] at hcInt; omega

end MinCostFlow.MinRatio
