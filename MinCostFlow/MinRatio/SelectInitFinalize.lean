module

public import MinCostFlow.MinRatio.SelectHeapInit
public import MinCostFlow.MinRatio.SelectBlocksParts
public import MinCostFlow.MinRatio.WireSelectRebuildSuffix
public import MinCostFlow.MinRatio.WireReembPotChain
public import MinCostFlow.MinRatio.SolverSelectBlocks
import WordRAM.Tactic

/-!
# Select initialization finalization and bridge to `solverStateRepSel` (`SelectInitFinalize`)

Once the select region's `F_0 .. F_d`, `G_d`, `g_0`, `coreLen 0 .. d`, `emb 0 .. d - 1`, and
metadata table have been populated on an empty select heap (`SelectHeapAt mem loc 4 0`),
`selectInitFinalizeBody` runs `selectPhiLoop` from `cur = 0` followed by `selectRebuildSuffix`
from `cur = 0`, establishing:
* `SelectPotInv` and `SelectBlocksAt` across all levels `0 .. d`,
* `SelectHeapMatchesChain` for the initial chain, and
* `(solverStateRepSel ...).rep root model (tokFull, sg) out.mem` with
  `sg.owned = fun a => sb ≤ a ∧ a < B.endAddr` and `sg.reembPot = chainReembPot pot model.chain`
  (whose initialization potential `K * chainReembPot pot model.chain` is paid by
  `K * model.chain.totalRuntime` via `chainReembPot_init_le`).
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program SparseCore.Program

/-- Finalize select initialization: fill all level potentials `φ_0 .. φ_d` via `selectPhiLoop` and
populate the select heap via `selectRebuildSuffix` from level `0`.
Arguments: `[sb, metaBase, d, Lk, scratch]` (`reg 0..4`). Returns the new scratch pointer. -/
def selectInitFinalizeBody (phiLoopProc rebuildSuffixProc : ℕ) : Stmt :=
  .call 5 phiLoopProc [.reg 1, .const 0, .reg 2, .reg 3, .reg 4] ;;
  .call 6 rebuildSuffixProc [.reg 0, .reg 1, .const 0, .reg 2, .reg 5] ;;
  .ret (.reg 6)

theorem selectInitFinalizeBody_noRand (phiLoopProc rebuildSuffixProc : ℕ) :
    (selectInitFinalizeBody phiLoopProc rebuildSuffixProc).NoRand := by
  simp [selectInitFinalizeBody, Stmt.NoRand]

/-- Scratch space for `selectInitFinalizeBody`. -/
noncomputable def selectInitFinalizeSpace (C : TreeChain) (cap Lk evalSpace : ℕ) : ℕ :=
  selectPhiLoopSpace C 0 Lk +
    (Finset.Icc 0 C.d).sum fun j => selectRebuildLevelSpace 0 (C.G j).E.card cap Lk evalSpace

/-- Step cost for `selectInitFinalizeBody`. -/
noncomputable def selectInitFinalizeCost (C : TreeChain) (cap Lk evalCost : ℕ) : ℕ :=
  selectPhiLoopCost C 0 Lk +
    (Finset.Icc 0 C.d).sum (fun j => selectRebuildLevelCost 0 (C.G j).E.card cap Lk evalCost + 40) + 60

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program SparseCore.Program

private lemma levelCandCount_of_size_zero {mem : ℕ → ℕ} {loc : SelectHeapLoc} {h j : ℕ}
    (hat : SelectHeapAt mem loc h 0) : levelCandCount mem loc j = 0 := by
  unfold levelCandCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he hbad
  have heCap : e < loc.cap := Finset.mem_range.mp he
  rcases hat.2.1.2.2.2 e heCap with h0 | hpos
  · exact hbad.1 h0
  · exact hbad.1 (Nat.eq_zero_of_le_zero hpos.1)

private lemma selectMlocOf_congr {B : SelectBlocksLoc} {metaBase pLast : ℕ} {g₁ g₂ : ℕ → ℕ}
    (h : ∀ j < B.d, g₁ j = g₂ j) :
    selectMlocOf B metaBase g₁ pLast = selectMlocOf B metaBase g₂ pLast := by
  have h1 : (fun j => if j < B.d then g₁ j else B.lastGPtr) =
      (fun j => if j < B.d then g₂ j else B.lastGPtr) := by
    funext j; split_ifs with hj
    · exact h j hj
    · rfl
  have h2 : (fun j => if j + 1 < B.d then g₁ (j + 1) else if j < B.d then B.lastGPtr else pLast) =
      (fun j => if j + 1 < B.d then g₂ (j + 1) else if j < B.d then B.lastGPtr else pLast) := by
    funext j; split_ifs with hj2
    · exact h (j + 1) hj2
    · rfl
    · rfl
  unfold selectMlocOf
  exact congrArg₂ (fun gp sp : ℕ → ℕ =>
    ({ metaBase := metaBase, d := B.d, Lk := B.Lk, g0Ptr := B.g0Ptr, GPtr := gp,
       vCap := fun _ => B.vCap, eCap := fun _ => B.eCap, phiPtr := B.phiPtr,
       coreLenPtr := B.lenPtr, embPtr := B.embPtr, fPtr := B.fPtr, sPtr := sp,
       pLast := pLast } : SelectLevelMetaLoc)) h1 h2

private lemma solverSelectInv_with_reembPot
    {cfg : Alg2Config} {G : MGraph} {L P m dMul kOff table : ℕ}
    {model : Alg2State cfg} {foot metaFoot : ℕ → Prop} {sg : SelectGhost} {mem : ℕ → ℕ} {rp : ℕ}
    (h : SolverSelectInv G L P m dMul kOff table model foot metaFoot sg mem) :
    SolverSelectInv G L P m dMul kOff table model foot metaFoot { sg with reembPot := rp } mem := h

set_option maxHeartbeats 800000 in
/-- Run `selectInitFinalizeBody` (`selectPhiLoop` from `0` + `selectRebuildSuffix` from `0`) on a
populated `SelectRegion` (whose `F`, `len`, `emb`, `lastG`, `g0`, and `metaTable` are filled, and
whose heap is empty) to establish `SelectBlocksAt`, `SelectPotInv`, `SelectHeapMatchesChain`, and
`solverStateRepSel.rep` with `reembPot = chainReembPot pot model.chain`. -/
theorem selectInitFinalize_runs
    {w L P m V psi k epsExp drainUnit unit toolMul treeMul dMul kOff K : ℕ}
    {vCap eCap sb metaBase pLast evalSpace evalCost scratch pos : ℕ}
    {phiLoopProc phiFillProc rebuildSuffixProc rebuildLvlProc : ℕ}
    {cfg : Alg2Config} {κ : ℝ} {G G₀ : MGraph} {σ σ_mwu γ_ℓ γ_c : ℝ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {pot : cfg.T.State → ℕ}
    {root : ℕ} {model : Alg2State cfg}
    {tokFull : (solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul Rcore).τ}
    {loc : SelectHeapLoc} {B : SelectBlocksLoc} {mem : ℕ → ℕ} {p : Program} {ω : ℕ → Bool}
    {PhiBd : (ℕ → ℕ → ℝ) → ℕ → Prop}
    (hlocalCore : Rcore.Local)
    (hw16 : 16 < 2 ^ w) (hw10 : 10 ≤ w) (hLkW : L < 2 ^ w) (hpLastW : pLast < 2 ^ w)
    (hreg : SelectRegion sb loc B metaBase)
    (hcap : loc.cap = selectHeapCap cfg G m)
    (hBd : B.d = cfg.P.d) (hBv : B.vCap = vCap) (hBe : B.eCap = eCap) (hBLk : B.Lk = L)
    (hrepFull : (solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul
      Rcore).rep root model tokFull mem)
    (hFootSc : ∀ a,
      (solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul Rcore).foot
        root tokFull a → a < scratch)
    (hFootDisj : ∀ a, sb ≤ a → a < B.endAddr →
      ¬ (solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul Rcore).foot
        root tokFull a)
    (hGBelowSb : ∀ j < cfg.P.d,
      solverLevelG tokFull.1.1 mem j + dynGraphSize vCap eCap ≤ sb)
    (hhbRd : mem (tokFull.1.1.table + dMul * cfg.P.d + kOff) = loc.hb)
    (hhbFoot : LevelMetaFoot tokFull.1.1 (tokFull.1.1.table + dMul * cfg.P.d + kOff))
    (hLvlGFoot : ∀ j < cfg.P.d,
      ∀ a, solverLevelG tokFull.1.1 mem j ≤ a →
        a < solverLevelG tokFull.1.1 mem j + dynGraphSize vCap eCap →
        LevelMetaFoot tokFull.1.1 a)
    (hLvlGPtrFoot : ∀ j < cfg.P.d,
      LevelMetaFoot tokFull.1.1 (solverLevelMetaAddr tokFull.1.1.table cfg.P.d + cfg.P.d + j))
    (hcaps : SolverLevelCapsInv P V vCap eCap model tokFull.1.1 mem)
    (hmod : SelectModelInv model G₀ σ σ_mwu γ_ℓ γ_c)
    (hHeap0 : SelectHeapAt mem loc 4 0)
    (htab : SelectMetaTableAt mem (selectMlocOf B metaBase (solverLevelG tokFull.1.1 mem) pLast))
    (hF : ∀ j ≤ cfg.P.d, SelPartF mem B j (model.chain.toTreeChain.activeLSF j).F.F)
    (hLen : ∀ j ≤ cfg.P.d,
      SelPartLen mem B P j (model.chain.toTreeChain.G j).E
        (model.chain.toTreeChain.chainLen model.chain.ℓ (j + 1)) pLast)
    (hEmb : ∀ j < cfg.P.d,
      SelPartEmb mem B j (model.chain.toTreeChain.activeCore j).E
        (model.chain.toTreeChain.activeEmb j))
    (hLastG : SelPartLast mem B (model.chain.toTreeChain.G cfg.P.d))
    (hG0 : SelPartG0 mem B P (model.chain.toTreeChain.G 0).E model.chain.g)
    (hVcap : ∀ j ≤ cfg.P.d, ∀ v ∈ (model.chain.toTreeChain.G j).V, v < vCap)
    (hEcapHeap : ∀ j ≤ cfg.P.d, ∀ e ∈ (model.chain.toTreeChain.G j).E, e < loc.cap / 2)
    (hPhiBdStep : ∀ j ≤ cfg.P.d, ∀ (φ : ℕ → ℕ → ℝ) (φj : ℕ → ℝ),
      (∀ k < j, SelectPotInvAt model.chain.toTreeChain model.chain.g φ k) →
      (∀ k < j, PhiBd φ k) →
      (∀ v ∈ (model.chain.toTreeChain.activeLSF j).F.F.V,
        ∃ r ∈ (model.chain.toTreeChain.activeLSF j).F.F.V,
          (model.chain.toTreeChain.activeLSF j).F.F.Connected v r ∧
          φj v = walkInner (potGrad model.chain.toTreeChain model.chain.g φ j)
            ((model.chain.toTreeChain.activeLSF j).F.F.forestPath v r)) →
      ∀ k < j + 1, PhiBd (Function.update φ j φj) k)
    (hFit : ∀ j ≤ cfg.P.d, ∀ φ' : ℕ → ℕ → ℝ,
      (∀ k < j, SelectPotInvAt model.chain.toTreeChain model.chain.g φ' k) →
      (∀ k < j, PhiBd φ' k) →
      (∀ e ∈ (model.chain.toTreeChain.activeLSF j).F.F.E,
        PotGradEvalFits 4 L P model.chain.toTreeChain model.chain.g φ' j e) ∧
      ForestWalkFits 4 L P (model.chain.toTreeChain.activeLSF j).F.F
        (potGrad model.chain.toTreeChain model.chain.g φ' j))
    (hpPhiLoop : p.procs[phiLoopProc]? = some (selectPhiLoopBody phiLoopProc phiFillProc))
    (hPhiFill :
      let mloc := selectMlocOf B metaBase (solverLevelG tokFull.1.1 mem) pLast
      ∀ φ : ℕ → ℕ → ℝ,
        MeetsContract w p phiFillProc
          (selectPhiFillContract w 4 P mloc model.chain.toTreeChain G₀ model.chain.g model.chain.ℓ
            σ σ_mwu γ_ℓ γ_c φ))
    (hpRebSuf : p.procs[rebuildSuffixProc]? =
      some (selectRebuildSuffixBody rebuildSuffixProc rebuildLvlProc))
    (hRebLvl :
      let mloc := selectMlocOf B metaBase (solverLevelG tokFull.1.1 mem) pLast
      ∀ φ : ℕ → ℕ → ℝ,
        MeetsContract w p rebuildLvlProc
          (selectRebuildLevelContract w 4 P loc mloc model.chain.toTreeChain model.chain.g
            model.chain.ℓ φ (fun j => model.chain.toTreeChain.chainLen model.chain.ℓ (j + 1))
            evalSpace evalCost))
    (hEndSc : B.endAddr ≤ scratch)
    (hz : ZeroFrom mem scratch)
    (hroom : scratch + selectInitFinalizeSpace model.chain.toTreeChain loc.cap L evalSpace < 2 ^ w) :
    let Rsel := solverStateRepSel cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul
      dMul kOff Rcore K pot
    ∃ (sc2 cost : ℕ) (out : State) (sg : SelectGhost),
      Runs w p ω (selectInitFinalizeBody phiLoopProc rebuildSuffixProc)
        (startState [sb, metaBase, cfg.P.d, L, scratch] mem pos) (.returned sc2) out cost ∧
      scratch ≤ sc2 ∧
      sc2 ≤ scratch + selectInitFinalizeSpace model.chain.toTreeChain loc.cap L evalSpace ∧
      ZeroFrom out.mem sc2 ∧
      sg.owned = (fun a => sb ≤ a ∧ a < B.endAddr) ∧
      sg.reembPot = chainReembPot pot model.chain ∧
      sg.mloc = selectMlocOf B metaBase (solverLevelG tokFull.1.1 out.mem) pLast ∧
      Rsel.rep root model (tokFull, sg) out.mem ∧
      (out.mem (solverSelectHeapAddr tokFull.1.1.table cfg.P.d) = sb →
        out.mem (solverSelectBlocksAddr tokFull.1.1.table cfg.P.d) = B.base →
        SolverSelectBlocksInv G L P m vCap eCap pLast B model
          ((solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul
            Rcore).foot root tokFull) tokFull.1.1 sg out.mem) ∧
      (∀ j ≤ cfg.P.d, PhiBd sg.φ j) ∧
      (∀ a < sb, out.mem a = mem a) ∧
      (∀ a, (solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul
        Rcore).foot root tokFull a → out.mem a = mem a) ∧
      cost ≤ selectInitFinalizeCost model.chain.toTreeChain loc.cap L evalCost := by
  intro Rsel
  set C := model.chain.toTreeChain
  set g := model.chain.g
  set ℓ := model.chain.ℓ
  set mloc := selectMlocOf B metaBase (solverLevelG tokFull.1.1 mem) pLast
  have hH : C.Holds G₀ ℓ σ σ_mwu γ_ℓ γ_c := hmod.1
  have hCd : C.d = cfg.P.d := rfl
  have hmlocD : mloc.d = C.d := by simp only [mloc, selectMlocOf, hBd, hCd]
  have hmlocLk : mloc.Lk = L := by simp only [mloc, selectMlocOf, hBLk]
  have hsbLeMeta : sb ≤ metaBase := by
    have := hreg.1; have := hreg.2.1; have := hreg.2.2.1; have := loc.endAddr_eq; omega
  have hMetaEnd : metaBase + selectLevelMetaSize mloc.d = B.base := by
    simp only [mloc, selectMlocOf]; exact hreg.2.2.2.1.symm
  have hBaseLeEnd : B.base ≤ B.endAddr := by rw [B.endAddr_eq]; omega
  have hsbLeEnd : sb ≤ B.endAddr := by omega
  have hBlkLeLast : ∀ j ≤ cfg.P.d, B.fPtr j + B.levelSize ≤ B.lastGPtr := fun j hj =>
    B.blk_le_last (by omega)
  have hLastLeG0 : B.lastGPtr + dynGraphSize vCap eCap = B.g0Ptr := by
    rw [← hBv, ← hBe]; rfl
  have hG0LeEnd : B.g0Ptr + eCap * L = B.endAddr := by
    rw [← hBe, ← hBLk]; rfl
  have hGEndBelowSb : ∀ j < cfg.P.d,
      solverLevelG tokFull.1.1 mem j + dynGraphSize vCap eCap ≤ sb := hGBelowSb
  have hGDG : ∀ j ≤ cfg.P.d, DynGraphAt mem (mloc.GPtr j) (mloc.vCap j) (mloc.eCap j) (C.G j) := by
    intro j hj
    dsimp only [mloc, selectMlocOf]
    rw [hBd, hBv, hBe]
    by_cases hlt : j < cfg.P.d
    · simp only [hlt, ↓reduceIte]
      exact (SolverLevelMetaAt.atCaps hcaps.1 hcaps.2 j hlt).1
    · have hjeq : j = cfg.P.d := by omega
      subst hjeq
      simp only [lt_irrefl, ↓reduceIte]
      rw [← hBv, ← hBe]
      exact hLastG
  -- Step 1: `selectPhiLoop` from `cur = 0`
  have hpref0 : SelectPhiPrefixAt mem mloc 4 P C g (fun _ _ => 0) 0 := by
    refine ⟨hmlocD, htab.1, htab.2.1, ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    simpa only [mloc, selectMlocOf, hBLk] using hG0.2
  have hlevels0 : ∀ j, 0 ≤ j → j ≤ C.d →
      mem (smEntryAddr mloc.metaBase mloc.d 0 j) = mloc.GPtr j ∧
      mem (smEntryAddr mloc.metaBase mloc.d 1 j) = mloc.vCap j ∧
      mem (smEntryAddr mloc.metaBase mloc.d 2 j) = mloc.eCap j ∧
      mem (smEntryAddr mloc.metaBase mloc.d 3 j) = mloc.phiPtr j ∧
      mem (smEntryAddr mloc.metaBase mloc.d 6 j) = mloc.fPtr j ∧
      DynGraphAt mem (mloc.GPtr j) (mloc.vCap j) (mloc.eCap j) (C.G j) ∧
      DynGraphAt mem (mloc.fPtr j) (mloc.vCap j) (mloc.eCap j) (C.activeLSF j).F.F := by
    intro j _ hj
    have hjM : j ≤ mloc.d := by omega
    have hrow := htab.2.2 j hjM
    refine ⟨hrow.1, hrow.2.1, hrow.2.2.1, hrow.2.2.2.1, hrow.2.2.2.2.2.2.1, hGDG j hj, ?_⟩
    exact hF j hj
  have hdisj0 : ∀ j, 0 ≤ j → j ≤ C.d →
      SelectPhiPrefixBelow mloc j scratch ∧
      SelectPhiTargetDisjoint mloc j scratch ∧
      mloc.GPtr j + dynGraphSize (mloc.vCap j) (mloc.eCap j) ≤ scratch ∧
      (∀ j', j ≤ j' → j' ≤ C.d →
        mloc.phiPtr j + mloc.vCap j * mloc.Lk ≤ mloc.GPtr j' ∨
          mloc.GPtr j' + dynGraphSize (mloc.vCap j') (mloc.eCap j') ≤ mloc.phiPtr j) ∧
      (∀ j', j < j' → j' ≤ C.d →
        mloc.phiPtr j + mloc.vCap j * mloc.Lk ≤ mloc.fPtr j' ∨
          mloc.fPtr j' + dynGraphSize (mloc.vCap j') (mloc.eCap j') ≤ mloc.phiPtr j) := by
    intro j _ hj
    have hphiBnd : ∀ k ≤ cfg.P.d,
        B.base ≤ B.fPtr k ∧ B.fPtr k + dynGraphSize vCap eCap = B.phiPtr k ∧
        B.phiPtr k + vCap * L ≤ B.fPtr k + B.levelSize ∧ B.fPtr k + B.levelSize ≤ B.lastGPtr := by
      intro k hk
      refine ⟨by unfold SelectBlocksLoc.fPtr; omega, by rw [← hBv, ← hBe]; rfl, ?_, hBlkLeLast k hk⟩
      unfold SelectBlocksLoc.phiPtr SelectBlocksLoc.levelSize
      rw [hBv, hBe, hBLk]; omega
    have hGPBnd : ∀ k ≤ cfg.P.d,
        mloc.GPtr k + dynGraphSize (mloc.vCap k) (mloc.eCap k) ≤ scratch := fun k hk => by
      dsimp only [mloc, selectMlocOf]; rw [hBd, hBv, hBe]
      by_cases hlt : k < cfg.P.d
      · simp only [hlt, ↓reduceIte]; have := hGEndBelowSb k hlt; omega
      · simp only [hlt, ↓reduceIte]; omega
    refine ⟨⟨by simp only [mloc, selectMlocOf] at hMetaEnd ⊢; omega,
        by simp only [mloc, selectMlocOf]; rw [hBe, hBLk]; omega,
        fun k hk => ⟨hGPBnd k (by omega), by
          have := hphiBnd k (by omega)
          simp only [mloc, selectMlocOf]; rw [hBv, hBLk]; omega⟩⟩,
      ⟨by have := hphiBnd j hj; simp only [mloc, selectMlocOf]; rw [hBv, hBLk]; omega,
       by have := hphiBnd j hj; simp only [mloc, selectMlocOf]; rw [hBv, hBe]; omega,
       Or.inl (by have := hphiBnd j hj; simp only [mloc, selectMlocOf] at hMetaEnd ⊢; omega),
       Or.inr (by have := hphiBnd j hj; simp only [mloc, selectMlocOf]; rw [hBv, hBLk]; omega),
       Or.inl (by have := hphiBnd j hj; simp only [mloc, selectMlocOf]; rw [hBv, hBe]; omega),
       fun k hk => by
         have hlt : k < cfg.P.d := by omega
         have hjB := hphiBnd j hj
         have hGk := hGEndBelowSb k hlt
         have hkj := B.blk_le_of_lt hk
         have hkB := hphiBnd k (by omega)
         refine ⟨Or.inl ?_, Or.inl ?_⟩
         · simp only [mloc, selectMlocOf, hBd, hlt, ↓reduceIte, hBv, hBe]; omega
         · simp only [mloc, selectMlocOf, hBv, hBLk]; omega⟩,
      hGPBnd j hj,
      fun j' hj1 hj2 => by
        have hjB := hphiBnd j hj
        dsimp only [mloc, selectMlocOf]; rw [hBd, hBv, hBe, hBLk]
        by_cases hlt : j' < cfg.P.d
        · simp only [hlt, ↓reduceIte]; right; have := hGEndBelowSb j' hlt; omega
        · simp only [hlt, ↓reduceIte]; left; omega,
      fun j' hj1 hj2 => by
        have hjB := hphiBnd j hj
        have hlt := B.blk_le_of_lt hj1
        left; simp only [mloc, selectMlocOf, hBv, hBLk]; omega⟩
  have hPhiLoopSpLe : selectPhiLoopSpace C 0 mloc.Lk ≤
      selectInitFinalizeSpace C loc.cap L evalSpace := by
    rw [hmlocLk]; unfold selectInitFinalizeSpace; exact Nat.le_add_right _ _
  have hsbW : sb < 2 ^ w := by omega
  have hmetaW : mloc.metaBase < 2 ^ w := by simp only [mloc, selectMlocOf]; omega
  have hdW : C.d < 2 ^ w := by
    have : selectLevelMetaSize mloc.d = 2 + 8 * (mloc.d + 1) := rfl; omega
  have hLkW' : mloc.Lk < 2 ^ w := by rw [hmlocLk]; exact hLkW
  obtain ⟨sc1, cPhi, st1, φ', hrPhi, hsc1Lo, hsc1Hi, hz1, _, hpref1, hpot1, hbd1, hfr1, hcPhi⟩ :=
    selectPhiLoop_runs (PhiBd := PhiBd) hpPhiLoop hPhiFill hw16 hw10 hH
      (by simpa only [mloc, selectMlocOf, hBe] using hG0.1)
      hPhiBdStep
      (fun j hj φ0 hpot0 hbd0 => by rw [hmlocLk]; exact hFit j hj φ0 hpot0 hbd0)
      (C.d + 1) 0 scratch pos mem (fun _ _ => 0) (by omega)
      hmetaW (by omega) hdW hLkW' hpref0
      (fun _ h => absurd h (Nat.not_lt_zero _))
      (fun _ h => absurd h (Nat.not_lt_zero _))
      hlevels0 hdisj0 hz (by omega)
  have hNotPhi : ∀ a, (a < B.base ∨ B.lastGPtr ≤ a) →
      ∀ j, 0 ≤ j → j ≤ C.d → a < mloc.phiPtr j ∨ mloc.phiPtr j + mloc.vCap j * mloc.Lk ≤ a := by
    intro a ha j _ hj
    have hlo : B.base ≤ B.phiPtr j := by unfold SelectBlocksLoc.phiPtr SelectBlocksLoc.fPtr; omega
    have hhi : B.phiPtr j + B.vCap * B.Lk ≤ B.lastGPtr := by
      have hbl := B.blk_le_last (j := j) (by omega)
      unfold SelectBlocksLoc.levelSize at hbl
      unfold SelectBlocksLoc.phiPtr; omega
    simp only [mloc, selectMlocOf]
    rcases ha with h | h <;> [left; right] <;> omega
  have hFr1BelowBase : ∀ a < B.base, st1.mem a = mem a := fun a ha =>
    hfr1 a (by omega) (hNotPhi a (Or.inl ha))
  have hHeap1 : SelectHeapAt st1.mem loc 4 0 :=
    hHeap0.of_agree fun a _ ha2 => hFr1BelowBase a (by
      have := hreg.2.1; have := hreg.2.2.1; have := hreg.2.2.2.1; omega)
  have hTab1 : SelectMetaTableAt st1.mem mloc :=
    htab.of_agree fun a _ ha2 => hFr1BelowBase a (by
      simp only [mloc, selectMlocOf] at hMetaEnd ha2 ⊢; omega)
  have hBlk1 : SelectBlocksAt st1.mem B P C g ℓ φ' pLast := by
    refine ⟨fun j hj => hBv ▸ hVcap j (by omega),
      fun j hj => (hLen j (by omega)).1,
      fun j hj => (hF j (by omega)).of_agree fun a ha =>
        hfr1 a (by have := B.blk_le_last hj; have := B.regF_blk ha; unfold SelectBlocksLoc.regBlk at this; omega)
          (fun j' _ hj' => by
            have hnp : ¬ B.regPhi j' a := fun hp => by
              by_cases hjj : j' = j
              · subst hjj; exact B.regF_not_phi ha hp
              · exact B.regBlk_disj hjj (B.regPhi_blk hp) (B.regF_blk ha)
            simp only [mloc, selectMlocOf]
            unfold SelectBlocksLoc.regPhi SelectBlocksLoc.lenPtr at hnp; omega),
      fun j hj => by
        have hp := (hpref1.2.2.2.2 j (Nat.lt_succ_of_le (by omega))).2.2.2.2.2
        simpa only [mloc, selectMlocOf] using hp,
      fun j hj => ((hLen j (by omega)).of_agree fun a ha =>
        hfr1 a (by have := B.blk_le_last hj; have := B.regLen_blk ha; unfold SelectBlocksLoc.regBlk at this; omega)
          (fun j' _ hj' => by
            have hnp : ¬ B.regPhi j' a := fun hp => by
              by_cases hjj : j' = j
              · subst hjj; exact B.regPhi_not_len hp ha
              · exact B.regBlk_disj hjj (B.regPhi_blk hp) (B.regLen_blk ha)
            simp only [mloc, selectMlocOf]
            unfold SelectBlocksLoc.regPhi SelectBlocksLoc.lenPtr at hnp; omega)).2,
      fun j hj => (hEmb j (by omega)).of_agree fun a ha =>
        hfr1 a (by have := B.blk_le_last hj.le; have := B.regEmb_blk ha; unfold SelectBlocksLoc.regBlk at this; omega)
          (fun j' _ hj' => by
            have hnp : ¬ B.regPhi j' a := fun hp => by
              by_cases hjj : j' = j
              · subst hjj; exact B.regPhi_not_emb hp ha
              · exact B.regBlk_disj hjj (B.regPhi_blk hp) (B.regEmb_blk ha)
            simp only [mloc, selectMlocOf]
            unfold SelectBlocksLoc.regPhi SelectBlocksLoc.lenPtr at hnp; omega),
      hBd.symm ▸ hLastG.of_agree fun a ha => hfr1 a (by unfold SelectBlocksLoc.regLast at ha; omega)
        (hNotPhi a (Or.inr ha.1)),
      (hG0.of_agree fun a ha => hfr1 a (by unfold SelectBlocksLoc.regG0 at ha; omega)
        (hNotPhi a (Or.inr (by unfold SelectBlocksLoc.regG0 SelectBlocksLoc.g0Ptr at ha; omega)))).2⟩
  have hPotInv1 : SelectPotInv C g φ' := fun j hj => hpot1 j hj
  have hMetaDisj1 : SelectMetaDisjoint mloc loc sc1 :=
    selectMetaDisjoint_of_region hreg (by omega) fun j hj => by
      rw [hBd] at hj
      have hhi := hGEndBelowSb j hj
      rw [hBv, hBe, hreg.1]
      exact ⟨by omega, Or.inl hhi⟩
  have hMeta1OfAgree : ∀ m', (∀ a < sc1, (a < loc.hb ∨ loc.endAddr ≤ a) → m' a = st1.mem a) →
      SelectLevelMetaAt m' mloc 4 P C g ℓ φ' (fun j => C.chainLen ℓ (j + 1)) := by
    intro m' hm'
    have hTabM' : SelectMetaTableAt m' mloc :=
      hTab1.of_agree fun a ha1 ha2 => hm' a (by simp only [mloc, selectMlocOf] at hMetaEnd ha2; omega)
        (Or.inr (by simp only [mloc, selectMlocOf] at ha1; have := hreg.2.1; have := hreg.2.2.1; omega))
    have hBlkM' : SelectBlocksAt m' B P C g ℓ φ' pLast :=
      hBlk1.of_agree fun a ha1 ha2 => hm' a (by omega)
        (Or.inr (by have := hreg.2.1; have := hreg.2.2.1; have := hreg.2.2.2.1; omega))
    refine selectLevelMetaAt_of_blocks (by omega) hTabM' (fun j hj => ?_) (fun j hj => ?_) hBlkM' hPotInv1
    · rw [hBd] at hj
      have hG0j := (SolverLevelMetaAt.atCaps hcaps.1 hcaps.2 j hj).1
      have hGhi := hGEndBelowSb j hj
      rw [hBv, hBe]
      exact DynGraphAt.of_agree hG0j fun a ha1 ha2 =>
        (hm' a (by omega) (Or.inl (by rw [hreg.1]; omega))).trans (hFr1BelowBase a (by omega))
    · rw [hBd] at hj; exact hmod.activeS_eq_G_succ j hj
  have hMeta1 : SelectLevelMetaAt st1.mem mloc 4 P C g ℓ φ' (fun j => C.chainLen ℓ (j + 1)) :=
    hMeta1OfAgree st1.mem fun _ _ _ => rfl
  -- Step 2: `selectRebuildSuffix` from `cur = 0`
  have hSufSpEq : selectRebuildSuffixSpace st1.mem loc C 0 evalSpace =
      (Finset.Icc 0 C.d).sum fun j => selectRebuildLevelSpace 0 (C.G j).E.card loc.cap L evalSpace := by
    unfold selectRebuildSuffixSpace
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [levelCandCount_of_size_zero hHeap1, hreg.2.2.2.2.2.1, hBLk]
  have hSufCostEq : selectRebuildSuffixCost st1.mem loc C 0 evalCost =
      (Finset.Icc 0 C.d).sum (fun j => selectRebuildLevelCost 0 (C.G j).E.card loc.cap L evalCost + 40) + 20 := by
    unfold selectRebuildSuffixCost
    rw [Finset.sum_congr rfl fun j _ => by rw [levelCandCount_of_size_zero hHeap1, hreg.2.2.2.2.2.1, hBLk]]
  have hRebSuf := selectRebuildSuffix_meetsContract (w := w) (h := 4) (P := P) (loc := loc)
    (mloc := mloc) (C := C) (G := G₀) (g := g) (ℓ := ℓ) (σ := σ) (σ_mwu := σ_mwu)
    (γ_ℓ := γ_ℓ) (γ_c := γ_c) (φ := φ') (coreLen := fun j => C.chainLen ℓ (j + 1))
    (evalSpace := evalSpace) (evalCost := evalCost) hpRebSuf (hRebLvl φ')
  obtain ⟨bReb, hbReb, oReb, st2, cReb, hrReb, hpReb, hcReb⟩ :=
    hRebSuf [loc.hb, mloc.metaBase, 0, C.d, sc1] st1.mem st1.pos ω
      (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro v (rfl | rfl | rfl | rfl | rfl)
        · rw [hreg.1]; exact hsbW
        · exact hmetaW
        · omega
        · exact hdW
        · rw [hmlocLk] at hsc1Hi; unfold selectInitFinalizeSpace at hroom; omega)
      ⟨0, sc1, 0, rfl, hw16, by simpa only [mloc, selectMlocOf] using hpLastW,
        by have := hreg.2.1; have := hreg.2.2.1; omega,
        by rw [hreg.2.2.2.2.1, hBd]; rfl, hreg.2.2.2.2.2.1.symm, hH,
        fun j _ hj => hEcapHeap j hj,
        fun e he hnz => by
          rcases hHeap1.2.1.2.2.2 e he with h0 | ⟨hle, _⟩
          · exact absurd h0 hnz
          · omega,
        hHeap1, hMeta1, hMetaDisj1, hMeta1OfAgree, hz1,
        by rw [hSufSpEq]; rw [hmlocLk] at hsc1Hi; unfold selectInitFinalizeSpace at hroom; omega⟩
  set sc2 := oReb.value
  have hpostReb := hpReb
  obtain ⟨hsc2Lo, hsc2Hi, _, ⟨_, hfr2⟩, hz2, _, _⟩ := hpReb
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hsc2Lo hsc2Hi hfr2
  obtain ⟨size2, hMatch2, _⟩ := selectInit_establishes_matchesChain hH (by rw [hreg.2.2.2.2.1, hBd]; rfl) hpostReb
  -- Stitch the two calls into `selectInitFinalizeBody`
  let s0 := startState [sb, metaBase, cfg.P.d, L, scratch] mem pos
  let rg5 := Function.update s0.regs 5 sc1
  let rg6 := Function.update rg5 6 sc2
  have hsc1W : sc1 < 2 ^ w := by rw [hmlocLk] at hsc1Hi; unfold selectInitFinalizeSpace at hroom; omega
  have hsc2W : sc2 < 2 ^ w := by rw [hSufSpEq] at hsc2Hi; rw [hmlocLk] at hsc1Hi; unfold selectInitFinalizeSpace at hroom; omega
  have r1 : Runs w p ω (.call 5 phiLoopProc [.reg 1, .const 0, .reg 2, .reg 3, .reg 4])
      s0 .normal ⟨st1.mem, rg5, st1.pos⟩ (cPhi + 6) :=
    runs_call_iff.mpr ⟨[mloc.metaBase, 0, C.d, mloc.Lk, scratch],
      selectPhiLoopBody phiLoopProc phiFillProc, .returned sc1, st1, cPhi,
      by dsimp only [s0, mloc]; simp [evalArgs, Expr.eval, startState, selectMlocOf, hBLk, hCd,
          show 0 < 2 ^ w by omega],
      hpPhiLoop, hrPhi, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
  have r2 : Runs w p ω (.call 6 rebuildSuffixProc [.reg 0, .reg 1, .const 0, .reg 2, .reg 5])
      ⟨st1.mem, rg5, st1.pos⟩ .normal ⟨st2.mem, rg6, st2.pos⟩ (cReb + 6) :=
    runs_call_iff.mpr ⟨[loc.hb, mloc.metaBase, 0, C.d, sc1],
      bReb, oReb, st2, cReb,
      by dsimp only [rg5, s0, mloc]; simp [evalArgs, Expr.eval, startState, hreg.1, selectMlocOf, hCd,
          show 0 < 2 ^ w by omega],
      hbReb, hrReb, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
  have r3 : Runs w p ω (.ret (.reg 6))
      ⟨st2.mem, rg6, st2.pos⟩ (.returned sc2) ⟨st2.mem, rg6, st2.pos⟩ 2 :=
    runs_ret_iff.mpr ⟨sc2, by simp [Expr.eval, rg6], rfl, rfl, rfl⟩
  have rFull : Runs w p ω (selectInitFinalizeBody phiLoopProc rebuildSuffixProc) s0 (.returned sc2)
      ⟨st2.mem, rg6, st2.pos⟩ ((cPhi + 6) + ((cReb + 6) + 2 + 1) + 1) := by
    unfold selectInitFinalizeBody
    exact runs_seq_iff.mpr (Or.inr ⟨_, _, _, r1, runs_seq_iff.mpr (Or.inr ⟨_, _, _, r2, r3, rfl⟩), rfl⟩)
  -- Establish `solverStateRepSel.rep` on `st2.mem`
  have hFrOffReg : ∀ a < scratch, (a < sb ∨ B.endAddr ≤ a) → st2.mem a = mem a := fun a ha hoff => by
    have hnotHeap : a < loc.hb ∨ loc.endAddr ≤ a := by
      have := hreg.1; have := hreg.2.1; have := hreg.2.2.1; have := hreg.2.2.2.1; omega
    have h1 := hfr2 a (by omega) hnotHeap
    have h2 := hfr1 a ha (fun j _ hj => by
      have hbl := hBlkLeLast j (by omega)
      have hlo : B.base ≤ B.phiPtr j := by unfold SelectBlocksLoc.phiPtr SelectBlocksLoc.fPtr; omega
      have hhi : B.phiPtr j + B.vCap * B.Lk ≤ B.fPtr j + B.levelSize := by
        unfold SelectBlocksLoc.phiPtr SelectBlocksLoc.levelSize; omega
      have hlast : B.lastGPtr ≤ B.endAddr := by unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr; omega
      simp only [mloc, selectMlocOf]
      have := hreg.1; have := hreg.2.1; have := hreg.2.2.1; have := hreg.2.2.2.1; omega)
    exact h1.trans h2
  have hFrFoot : ∀ a,
      (solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul Rcore).foot
        root tokFull a → st2.mem a = mem a := fun a ha =>
    hFrOffReg a (hFootSc a ha) (by
      by_contra h; obtain ⟨h1, h2⟩ := not_or.mp h
      exact hFootDisj a (Nat.le_of_not_lt h1) (Nat.lt_of_not_le h2) ha)
  have hFrAllBelowSb : ∀ a < sb, st2.mem a = mem a := fun a ha =>
    hFrOffReg a (by omega) (Or.inl ha)
  have hRfullLocal := solverStateRepFull_local cfg κ G L P m V psi k epsExp drainUnit unit toolMul
    treeMul hlocalCore
  have hrepFull2 : (solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul
      Rcore).rep root model tokFull st2.mem :=
    (hRfullLocal root model tokFull mem st2.mem
      fun a ha => (hFrFoot a ha).symm).1 hrepFull
  have hFrMetaToEnd : ∀ a, metaBase ≤ a → a < B.endAddr → st2.mem a = st1.mem a := fun a h1 h2 =>
    hfr2 a (by omega) (Or.inr (by have := hreg.2.1; have := hreg.2.2.1; omega))
  have hMlocEq2 : selectMlocOf B metaBase (solverLevelG tokFull.1.1 st2.mem) pLast = mloc :=
    selectMlocOf_congr fun j hj => by
      rw [hBd] at hj
      exact hFrFoot _ (LevelMetaFoot.mem_foot hrepFull.1.1 (hLvlGPtrFoot j hj))
  have hTab2 : SelectMetaTableAt st2.mem
      (selectMlocOf B metaBase (solverLevelG tokFull.1.1 st2.mem) pLast) := by
    rw [hMlocEq2]
    exact hTab1.of_agree fun a ha1 ha2 =>
      hFrMetaToEnd a (by simp only [mloc, selectMlocOf] at ha1; exact ha1)
        (by simp only [mloc, selectMlocOf] at hMetaEnd ha2; omega)
  have hBlk2 : SelectBlocksAt st2.mem B P C g ℓ φ' pLast :=
    hBlk1.of_agree fun a ha1 ha2 => hFrMetaToEnd a (by omega) ha2
  have hCaps2 : SolverLevelCapsInv P V vCap eCap model tokFull.1.1 st2.mem := by
    have hTagOwn : ∀ a, tokFull.1.1.tag a ≠ 0 → st2.mem a = mem a := fun a hne =>
      hFrFoot a (Or.inl (hrepFull.1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 a hne))
    exact hcaps.preserve rfl hcaps.1.2.1
      (fun a ha => ⟨rfl, hTagOwn a (by rcases ha with h | h | h | h <;> omega)⟩)
      (fun j hj => (SolverLevelMetaAt.atCaps hcaps.1 hcaps.2 j hj).2.2.1)
      rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl
  have hInvBase := selectRegion_solverSelectInv (dMul := dMul) (kOff := kOff) hreg hcap hBd hBv hBe hBLk
    hFootDisj
    ((hFrFoot _ (LevelMetaFoot.mem_foot hrepFull.1.1 hhbFoot)).trans hhbRd)
    (Or.inl hhbFoot)
    (fun j hj a ha1 ha2 => by
      have hGEq : solverLevelG tokFull.1.1 st2.mem j = solverLevelG tokFull.1.1 mem j :=
        hFrFoot _ (LevelMetaFoot.mem_foot hrepFull.1.1 (hLvlGPtrFoot j hj))
      rw [hGEq] at ha1 ha2
      exact hLvlGFoot j hj a ha1 ha2)
    hLvlGPtrFoot hTab2 hBlk2 hMatch2 hCaps2 hmod hPotInv1
  let sg0 : SelectGhost :=
    { loc := loc
      mloc := selectMlocOf B metaBase (solverLevelG tokFull.1.1 st2.mem) pLast
      size := size2
      φ := φ'
      coreLen := fun j => C.chainLen ℓ (j + 1)
      owned := fun a => sb ≤ a ∧ a < B.endAddr
      reembPot := chainReembPot pot model.chain }
  have hInv2 : SolverSelectInv G L P m dMul kOff tokFull.1.1.table model
      ((solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul Rcore).foot
        root tokFull) (LevelMetaFoot tokFull.1.1) sg0 st2.mem :=
    solverSelectInv_with_reembPot hInvBase
  have hBlocks2 : st2.mem (solverSelectHeapAddr tokFull.1.1.table cfg.P.d) = sb →
      st2.mem (solverSelectBlocksAddr tokFull.1.1.table cfg.P.d) = B.base →
      SolverSelectBlocksInv G L P m vCap eCap pLast B model
        ((solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul
          Rcore).foot root tokFull) tokFull.1.1 sg0 st2.mem := fun hhb hblkA => by
    have hhbEq : loc.hb = sb := hreg.1
    have hmetaEq : metaBase = loc.metaPtr := hreg.2.2.1
    refine ⟨hBd, hBv, hBe, hBLk, hcap, ?_, ?_, fun a ha => hFootDisj a ha.1 ha.2,
      hhb.trans hhbEq.symm, hblkA, ?_, rfl, hTab2, hBlk2, hPotInv1, hMatch2,
      G₀, σ, σ_mwu, γ_ℓ, γ_c, hmod⟩
    · show SelectRegion loc.hb loc B loc.metaPtr
      rw [hhbEq, ← hmetaEq]; exact hreg
    · show (fun a => sb ≤ a ∧ a < B.endAddr) = fun a => loc.hb ≤ a ∧ a < B.endAddr
      rw [hhbEq]
    · show selectMlocOf B metaBase _ pLast = selectMlocOf B loc.metaPtr _ pLast
      rw [hmetaEq]
  refine ⟨sc2, _, ⟨st2.mem, rg6, st2.pos⟩, sg0, rFull, by omega, ?_, hz2, rfl, rfl, rfl,
    ⟨hrepFull2, hInv2, rfl⟩, hBlocks2, fun j hj => hbd1 j hj, hFrAllBelowSb, hFrFoot, ?_⟩
  · rw [hSufSpEq] at hsc2Hi
    rw [hmlocLk] at hsc1Hi
    unfold selectInitFinalizeSpace; omega
  · simp only [selectRebuildSuffixContract, List.getD_cons_zero, List.getD_cons_succ] at hcReb
    rw [hSufCostEq] at hcReb
    rw [hmlocLk] at hcPhi
    unfold selectInitFinalizeCost; omega

end MinCostFlow.MinRatio
