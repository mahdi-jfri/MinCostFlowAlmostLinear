module

public import MinCostFlow.MinRatio.SelectUpdateSuffixDefs
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# Rebuilt suffix block and potential update (`SelectUpdateSuffixBlocks`)

Verifies Phase 3b of the select-maintenance post-core pass of `Update`:
* If `firstReb ≤ d`, runs `selectInitInteriorLoopBody` (`firstReb .. d - 1`), `op 3` on core
  `d - 1`, `selectFillLastLevelBody` (level `d`), and `selectPhiLoopBody` (`firstReb .. d`).
* If `firstReb = d + 1`, executes a zero-scratch no-op returning `scratch`.

On return, `SelectBlocksAt` holds for the new chain `(C', g', ℓ', φ')` across all levels `0 .. d`,
together with `SelectPotInv C' g' φ'` and `∀ j ≤ d, PhiBd φ' j`, while preserving `solverStateRep`,
`SolverLevelCapsInv`, `SelectMetaTableAt`, `SelectHeapAt`, and all memory `< scratch` outside
`[B.base, B.endAddr)` and `Rrep.foot root tok'`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine Num DynSpanner.Program SparseCore.Program

set_option maxHeartbeats 1200000 in
/-- Verification of `selectUpdateSuffixBlocksBody`: updates rebuilt suffix blocks and potentials
for `firstReb .. d` (or performs a zero-scratch no-op when `firstReb = d + 1`), producing full
`SelectBlocksAt`, `SelectPotInv`, and `∀ j ≤ d, PhiBd φ' j` for `modelPre`. -/
theorem selectUpdateSuffixBlocks_runs
    {w L P m V psi k epsExp drainUnit depth capExp vCap eCap sb metaBase pLast heapSize
      firstReb scratch pos : ℕ}
    {initIntLoop fillIntProc dgCopyProc coreLenProc filterProc embCopyProc fillLast
      phiLoop phiFillProc : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {G₀' : MGraph} {σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    {initialGraph : ℕ → MGraph} {Psc : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {op : ℕ → ℕ} {ω : ℕ → Bool}
    {root : ℕ} {modelPre : Alg2State cfg} {tok' : SolverToken cfg L Rcore}
    {loc : SelectHeapLoc} {B : SelectBlocksLoc} {D : SelBlocksData} {mem : ℕ → ℕ}
    {PhiBd : (ℕ → ℕ → ℝ) → ℕ → Prop}
    (hfmt4 : fmt.limbBits = 4) (hfmtP : fmt.precision = P) (hlocalCore : Rcore.Local)
    (hw16 : 16 < 2 ^ w) (hw10 : 10 ≤ w) (hLkW : L < 2 ^ w) (hSlotW : B.slot < 2 ^ w)
    (hkW : cfg.P.k < 2 ^ w) (hpLastW : pLast < 2 ^ w)
    (hdPos : 0 < cfg.P.d) (hFR : firstReb ≤ cfg.P.d + 1)
    (hreg : SelectRegion sb loc B metaBase)
    (hBd : B.d = cfg.P.d) (hBv : B.vCap = vCap) (hBe : B.eCap = eCap) (hBLk : B.Lk = L)
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root modelPre tok' mem)
    (hFootSc : ∀ a,
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok' a → a < scratch)
    (hFootDisj : ∀ a, sb ≤ a → a < B.endAddr →
      ¬ (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok' a)
    (hEndSc : B.endAddr ≤ scratch)
    (hcaps : SolverLevelCapsInv P V vCap eCap modelPre tok' mem)
    (hmodNew : SelectModelInv modelPre G₀' σ' σ'_mwu γ'_ℓ γ'_c)
    (htab : SelectMetaTableAt mem (selectMlocOf B metaBase (solverLevelG tok' mem) pLast))
    (hHeap : SelectHeapAt mem loc 4 heapSize)
    (hblk : SelBlocksDataAt mem B P D pLast)
    (hG0Match : D.E0 = (modelPre.chain.G 0).E ∧ D.g = modelPre.chain.g)
    (hPrefBlocks : ∀ j < min firstReb cfg.P.d,
      D.F j = (modelPre.chain.toTreeChain.activeLSF j).F.F ∧
      D.V j = (modelPre.chain.G j).V ∧
      D.E j = (modelPre.chain.G j).E ∧
      D.len j = modelPre.chain.toTreeChain.chainLen modelPre.chain.ℓ (j + 1) ∧
      D.coreE j = (modelPre.chain.toTreeChain.activeCore j).E ∧
      D.emb j = modelPre.chain.toTreeChain.activeEmb j)
    (hNoRebLast : firstReb = cfg.P.d + 1 →
      D.Gd = modelPre.chain.G cfg.P.d ∧
      D.F cfg.P.d = (modelPre.chain.toTreeChain.activeLSF cfg.P.d).F.F ∧
      D.V cfg.P.d = (modelPre.chain.G cfg.P.d).V ∧
      D.E cfg.P.d = (modelPre.chain.G cfg.P.d).E ∧
      ∀ e ∈ (modelPre.chain.G cfg.P.d).E,
        D.len cfg.P.d e = modelPre.chain.toTreeChain.chainLen modelPre.chain.ℓ (cfg.P.d + 1) e)
    (hPotPref : ∀ j < firstReb, j ≤ cfg.P.d →
      SelectPotInvAt modelPre.chain.toTreeChain modelPre.chain.g D.φ j)
    (hPhiBdPref : ∀ j < firstReb, j ≤ cfg.P.d → PhiBd D.φ j)
    (hPhiBdStep : ∀ j ≤ cfg.P.d, ∀ (φ : ℕ → ℕ → ℝ) (φj : ℕ → ℝ),
      (∀ k < j, SelectPotInvAt modelPre.chain.toTreeChain modelPre.chain.g φ k) →
      (∀ k < j, PhiBd φ k) →
      (∀ v ∈ (modelPre.chain.toTreeChain.activeLSF j).F.F.V,
        ∃ r ∈ (modelPre.chain.toTreeChain.activeLSF j).F.F.V,
          (modelPre.chain.toTreeChain.activeLSF j).F.F.Connected v r ∧
          φj v = walkInner (potGrad modelPre.chain.toTreeChain modelPre.chain.g φ j)
            ((modelPre.chain.toTreeChain.activeLSF j).F.F.forestPath v r)) →
      ∀ k < j + 1, PhiBd (Function.update φ j φj) k)
    (hVcap : ∀ j ≤ cfg.P.d, ∀ v ∈ (modelPre.chain.G j).V, v < vCap)
    (hEcap : ∀ j ≤ cfg.P.d, ∀ e ∈ (modelPre.chain.G j).E, e < eCap)
    (hFV : ∀ j ≤ cfg.P.d, ∀ v ∈ (modelPre.chain.toTreeChain.activeLSF j).F.F.V, v < vCap)
    (hFE : ∀ j ≤ cfg.P.d, ∀ e ∈ (modelPre.chain.toTreeChain.activeLSF j).F.F.E, e < eCap)
    (hLenFitInt : ∀ j, firstReb ≤ j → j < cfg.P.d → ∀ e ∈ (modelPre.chain.G j).E,
      ∃ q : ℤ, Num.Fits 4 L q ∧
        (q : ℝ) / (2 : ℝ) ^ P = modelPre.chain.toTreeChain.chainLen modelPre.chain.ℓ (j + 1) e)
    (hLenFitLast : firstReb ≤ cfg.P.d → ∀ e ∈ (modelPre.chain.G cfg.P.d).E,
      ∀ prevM : ℕ → ℕ,
        EdgeValuesAt prevM (B.lenPtr (cfg.P.d - 1)) 4 L P (modelPre.chain.G cfg.P.d).E
          (modelPre.chain.toTreeChain.chainLen modelPre.chain.ℓ cfg.P.d) →
        Num.Fits 4 L (Num.intVal prevM (B.lenPtr (cfg.P.d - 1) + e * L) 4 L * (2 : ℤ) ^ pLast) ∧
        ∃ q : ℤ, Num.Fits 4 L q ∧
          (q : ℝ) / (2 : ℝ) ^ (P + pLast) =
            modelPre.chain.toTreeChain.chainLen modelPre.chain.ℓ (cfg.P.d + 1) e)
    (hEmbSlot : ∀ j, firstReb ≤ j → j < cfg.P.d →
      ∀ e ∈ (modelPre.chain.toTreeChain.activeCore j).E,
        (mWalkEncode (modelPre.chain.toTreeChain.activeEmb j e)).length ≤ B.slot)
    (hPhiFit : ∀ j ≤ cfg.P.d, ∀ φ' : ℕ → ℕ → ℝ,
      (∀ k < j, SelectPotInvAt modelPre.chain.toTreeChain modelPre.chain.g φ' k) →
      (∀ k < j, PhiBd φ' k) →
      (∀ e ∈ (modelPre.chain.toTreeChain.activeLSF j).F.F.E,
        PotGradEvalFits 4 L P modelPre.chain.toTreeChain modelPre.chain.g φ' j e) ∧
      ForestWalkFits 4 L P (modelPre.chain.toTreeChain.activeLSF j).F.F
        (potGrad modelPre.chain.toTreeChain modelPre.chain.g φ' j))
    (hpInitInt : p.procs[initIntLoop]? = some (selectInitInteriorLoopBody initIntLoop fillIntProc))
    (hpFillInt : p.procs[fillIntProc]? =
      some (selectFillInteriorLevelBody (op 2) (op 4) dgCopyProc coreLenProc filterProc embCopyProc))
    (hpFillLast : p.procs[fillLast]? = some (selectFillLastLevelBody dgCopyProc coreLenProc))
    (hpPhiLoop : p.procs[phiLoop]? = some (selectPhiLoopBody phiLoop phiFillProc))
    (hFootAt : ∀ j < cfg.P.d,
      SparseCoreReadoutFootAt fmt L depth cfg.T (initialGraph j) cfg.P.k
        (modelPre.chain.lvlM j) modelPre.chain.N₀ vCap eCap capExp Psc allocation Rcore p op)
    (hDgCopyInt : ∀ j, firstReb ≤ j → j < cfg.P.d → ∀ vcF ecF,
      MeetsContract w p dgCopyProc
        (dgCopyRefillContract w vCap eCap vcF ecF (D.F j)
          (modelPre.chain.toTreeChain.activeLSF j).F.F))
    (hDgCopyLastG : MeetsContract w p dgCopyProc
      (dgCopyRefillContract w vCap eCap vCap eCap D.Gd (modelPre.chain.G cfg.P.d)))
    (hDgCopyLastF : MeetsContract w p dgCopyProc
      (dgCopyRefillContract w vCap eCap tok'.vcLast tok'.ecLast (D.F cfg.P.d)
        (modelPre.chain.toTreeChain.activeLSF cfg.P.d).F.F))
    (hCoreLen : ∀ eL : List ℕ, MeetsContract w p coreLenProc (selCoreLenFillContract w P eCap eL))
    (hFilter : ∀ eL : List ℕ, MeetsContract w p filterProc (selFilterAbsentContract w eL))
    (hEmbCopy : ∀ j, firstReb ≤ j → j < cfg.P.d → ∀ eL : List ℕ,
      MeetsContract w p embCopyProc
        (selEmbCopyContract w eL (modelPre.chain.toTreeChain.activeEmb j)))
    (hPhiFill :
      let mloc := selectMlocOf B metaBase (solverLevelG tok' mem) pLast
      ∀ φ : ℕ → ℕ → ℝ,
        MeetsContract w p phiFillProc
          (selectPhiFillContract w 4 P mloc modelPre.chain.toTreeChain G₀' modelPre.chain.g
            modelPre.chain.ℓ σ' σ'_mwu γ'_ℓ γ'_c φ))
    (hz : ZeroFrom mem scratch)
    (hroom : scratch + selectUpdateSuffixBlocksSpace modelPre.chain firstReb L capExp < 2 ^ w) :
    let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
    let C' := modelPre.chain.toTreeChain
    ∃ scOut cost out tok2 φ',
      Runs w p ω (selectUpdateSuffixBlocksBody initIntLoop (op 3) fillLast phiLoop)
        (startState [metaBase, firstReb, cfg.P.d, tok'.handle + 18,
          solverLevelMetaAddr tok'.table cfg.P.d, tok'.termHandle, modelPre.chain.lastBran,
          L, B.slot, pLast, scratch] mem pos)
        (.returned scOut) out cost ∧
      scratch ≤ scOut ∧
      scOut ≤ scratch + selectUpdateSuffixBlocksSpace modelPre.chain firstReb L capExp ∧
      Rrep.rep root modelPre tok2 out.mem ∧
      tok2.table = tok'.table ∧ tok2.handle = tok'.handle ∧
      tok2.levelsEnd = tok'.levelsEnd ∧ tok2.intCap = tok'.intCap ∧
      tok2.rootECap = tok'.rootECap ∧
      tok2.tree = tok'.tree ∧ tok2.trees = tok'.trees ∧ tok2.edgeRecords = tok'.edgeRecords ∧
      tok2.termHandle = tok'.termHandle ∧ tok2.termTok = tok'.termTok ∧
      tok2.vcLast = tok'.vcLast ∧ tok2.ecLast = tok'.ecLast ∧
      (∀ a, Rrep.foot root tok2 a → Rrep.foot root tok' a ∨ (scratch ≤ a ∧ a < scOut)) ∧
      (∀ a, tok'.owned a → tok2.owned a) ∧
      (∀ a < scratch, tok2.tag a = tok'.tag a) ∧
      (∀ a, tok'.tag a ≠ 0 → tok2.tag a = tok'.tag a) ∧
      SolverLevelCapsInv P V vCap eCap modelPre tok2 out.mem ∧
      SelectMetaTableAt out.mem (selectMlocOf B metaBase (solverLevelG tok2 out.mem) pLast) ∧
      SelectHeapAt out.mem loc 4 heapSize ∧
      SelectBlocksAt out.mem B P C' modelPre.chain.g modelPre.chain.ℓ φ' pLast ∧
      (∀ k < firstReb, φ' k = D.φ k) ∧
      SelectPotInv C' modelPre.chain.g φ' ∧
      (∀ j ≤ cfg.P.d, PhiBd φ' j) ∧
      ZeroFrom out.mem scOut ∧
      (∀ a < scratch, ¬ (B.base ≤ a ∧ a < B.endAddr) →
        (∀ j < cfg.P.d, tok'.tag a ≠ 21 + j) → out.mem a = mem a) ∧
      cost + Rrep.phi root tok2 out.mem ≤
        selectUpdateSuffixBlocksCost D.F D.Gd modelPre.chain Psc.readout firstReb L capExp B.slot +
          Rrep.phi root tok' mem := by
  intro Rrep C'
  have hsbLeBase : sb ≤ B.base := by
    have := hreg.1; have := hreg.2.1; have := hreg.2.2.1; have := hreg.2.2.2.1
    have : loc.hb ≤ loc.endAddr := by rw [loc.endAddr_eq]; omega
    omega
  have hBaseLeEnd : B.base ≤ B.endAddr := by rw [B.endAddr_eq]; omega
  have hsbLtEnd : sb < B.endAddr := by
    have := hreg.1; have := hreg.2.1; have := hreg.2.2.1; have := hreg.2.2.2.1
    have : loc.hb < loc.endAddr := by rw [loc.endAddr_eq]; unfold selectHeapSize shHdrSize; omega
    omega
  have hMetaEnd : metaBase + selectLevelMetaSize B.d = B.base := hreg.2.2.2.1.symm
  have hMetaSz : metaBase + (2 + 8 * (B.d + 1)) = B.base := by
    unfold selectLevelMetaSize at hMetaEnd; exact hMetaEnd
  have hLastLeEnd : B.lastGPtr + dynGraphSize B.vCap B.eCap ≤ B.endAddr := by
    unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr; omega
  have hLastLSF : C'.activeLSF cfg.P.d = modelPre.chain.lastLSFs modelPre.chain.lastBran := by
    simp [C', TreeChain.activeLSF, ChainState.toTreeChain]
  let s0 := startState [metaBase, firstReb, cfg.P.d, tok'.handle + 18,
    solverLevelMetaAddr tok'.table cfg.P.d, tok'.termHandle, modelPre.chain.lastBran,
    L, B.slot, pLast, scratch] mem pos
  by_cases hReb : firstReb ≤ cfg.P.d
  · have hSpEq : selectUpdateSuffixBlocksSpace modelPre.chain firstReb L capExp =
        selectInitInteriorLoopSpace modelPre.chain firstReb L capExp + 1 +
        selectFillLastLevelSpace (modelPre.chain.G cfg.P.d).m (C'.activeLSF cfg.P.d).F.F.m L +
        selectPhiLoopSpace C' firstReb L := by
      unfold selectUpdateSuffixBlocksSpace; simp [hReb, C']
    rw [hSpEq] at hroom
    have hCostEq : selectUpdateSuffixBlocksCost D.F D.Gd modelPre.chain Psc.readout firstReb L capExp B.slot =
        selectRefreshInteriorLoopCost D.F modelPre.chain Psc.readout firstReb L capExp B.slot +
        Psc.readout +
        selectFillLastLevelCost D.Gd.n D.Gd.m (D.F cfg.P.d).n (D.F cfg.P.d).m
          (modelPre.chain.G cfg.P.d).n (modelPre.chain.G cfg.P.d).m
          (C'.activeLSF cfg.P.d).F.F.n (C'.activeLSF cfg.P.d).F.F.m L +
        selectPhiLoopCost C' firstReb L + 120 := by
      unfold selectUpdateSuffixBlocksCost; simp [hReb, C']
    -- Step 1: `selectInitInteriorLoopBody` from `firstReb` to `cfg.P.d`
    obtain ⟨sc1, c1, st1, tok1, hr1, hsc1Lo, hsc1Hi, hrep1,
        htab1Eq, hhnd1Eq, hlev1Eq, hint1Eq, hrec1Eq, htree1Eq, htrees1Eq, hedg1Eq, hth1Eq, htt1Eq,
        hvc1Eq, hec1Eq, hft1, hown1, htag1Lt, htag1Ne, hcaps1, htab1, hHeap1, hblk1, hz1, hfr1, hc1⟩ :=
      selectRefreshInteriorLoop_runs hfmt4 hfmtP hlocalCore hw16 hLkW hSlotW hkW hReb
        hreg hBd hBv hBe hBLk hrep hFootSc hFootDisj hEndSc hcaps htab hHeap hblk
        (fun j _ hj => hmodNew.2.2.2.1 j hj) (fun j _ hj => hmodNew.2.2.1 j hj)
        (fun j _ hj => hFV j (Nat.le_of_lt hj)) (fun j _ hj => hFE j (Nat.le_of_lt hj))
        hLenFitInt hEmbSlot hpInitInt hpFillInt (fun j _ hj => hFootAt j hj)
        hDgCopyInt hCoreLen hFilter hEmbCopy hz (by omega)
    have hFoot1Sc : ∀ a, Rrep.foot root tok1 a → a < sc1 := fun a ha => by
      rcases hft1 a ha with h0 | hnew
      · exact lt_of_lt_of_le (hFootSc a h0) hsc1Lo
      · exact hnew.2
    have hFoot1Disj : ∀ a, sb ≤ a → a < B.endAddr → ¬ Rrep.foot root tok1 a := fun a h1 h2 ha => by
      rcases hft1 a ha with h0 | hnew
      · exact hFootDisj a h1 h2 h0
      · omega
    -- Step 2: `op 3` on core `cfg.P.d - 1`
    obtain ⟨b3, o3, st2, c2, tok2, hb3, hr2, hsc2Lo, hsc2Hi, hrep2,
        htab2Eq, hhnd2Eq, hlev2Eq, hint2Eq, hrec2Eq, htree2Eq, htrees2Eq, hedg2Eq, hth2Eq, htt2Eq,
        hvc2Eq, hec2Eq, hcaps2, htab2, hHeap2, hblk2, hGdAt2, hGdEnd2, hGdDisj2, hfr2, hft2,
        hown2, htag2Lt, htag2Ne, hz2, hc2⟩ :=
      op3_gd_disj_runs (fmt := fmt) (L := L) hlocalCore hkW hdPos hreg hBd hBv hBe
        hrep1 hFoot1Sc hFoot1Disj (by omega) hcaps1 hmodNew htab1 hHeap1 hblk1
        (hFootAt (cfg.P.d - 1) (by omega)) hz1 (by omega)
    set sc2 := o3.value
    set srcGd := st2.mem sc1
    -- Step 3: `selectFillLastLevelBody`
    have hD1Last : (({ D with
          F := fun j => if firstReb ≤ j ∧ j < cfg.P.d then (C'.activeLSF j).F.F else D.F j
          E := fun j => if firstReb ≤ j ∧ j < cfg.P.d then (C'.G j).E else D.E j
          len := fun j => if firstReb ≤ j ∧ j < cfg.P.d then C'.chainLen modelPre.chain.ℓ (j + 1) else D.len j
          coreE := fun j => if firstReb ≤ j ∧ j < cfg.P.d then (C'.activeCore j).E else D.coreE j
          emb := fun j => if firstReb ≤ j ∧ j < cfg.P.d then C'.activeEmb j else D.emb j } : SelBlocksData)).E (cfg.P.d - 1) =
        (modelPre.chain.G (cfg.P.d - 1)).E ∧
        (({ D with
          F := fun j => if firstReb ≤ j ∧ j < cfg.P.d then (C'.activeLSF j).F.F else D.F j
          E := fun j => if firstReb ≤ j ∧ j < cfg.P.d then (C'.G j).E else D.E j
          len := fun j => if firstReb ≤ j ∧ j < cfg.P.d then C'.chainLen modelPre.chain.ℓ (j + 1) else D.len j
          coreE := fun j => if firstReb ≤ j ∧ j < cfg.P.d then (C'.activeCore j).E else D.coreE j
          emb := fun j => if firstReb ≤ j ∧ j < cfg.P.d then C'.activeEmb j else D.emb j } : SelBlocksData)).len (cfg.P.d - 1) =
        C'.chainLen modelPre.chain.ℓ cfg.P.d := by
      dsimp only
      by_cases hlt : firstReb ≤ cfg.P.d - 1
      · have hr : firstReb ≤ cfg.P.d - 1 ∧ cfg.P.d - 1 < cfg.P.d := ⟨hlt, by omega⟩
        simp [hr, Nat.sub_add_cancel hdPos, C', ChainState.toTreeChain]
      · have hnr : ¬ (firstReb ≤ cfg.P.d - 1 ∧ cfg.P.d - 1 < cfg.P.d) := by omega
        simp only [hnr, ↓reduceIte]
        have hPB := hPrefBlocks (cfg.P.d - 1) (by omega)
        rw [Nat.sub_add_cancel hdPos] at hPB
        exact ⟨hPB.2.2.1, hPB.2.2.2.1⟩
    have hPrevVal2 : EdgeValuesAt st2.mem (B.lenPtr (B.d - 1)) 4 B.Lk P
        (modelPre.chain.G cfg.P.d).E (C'.chainLen modelPre.chain.ℓ cfg.P.d) := by
      have hpart := (hblk2.2.2.1 (B.d - 1) (by omega)).2
      unfold coreLenPrec at hpart
      rw [ite_eq_left (show B.d - 1 < B.d by omega)] at hpart
      intro e he
      have hsub : (modelPre.chain.G cfg.P.d).E ⊆ (modelPre.chain.G (cfg.P.d - 1)).E :=
        C'.G_E_subset_of_le hmodNew.1 (by omega) le_rfl
      have he' : e ∈ (({ D with
          F := fun j => if firstReb ≤ j ∧ j < cfg.P.d then (C'.activeLSF j).F.F else D.F j
          E := fun j => if firstReb ≤ j ∧ j < cfg.P.d then (C'.G j).E else D.E j
          len := fun j => if firstReb ≤ j ∧ j < cfg.P.d then C'.chainLen modelPre.chain.ℓ (j + 1) else D.len j
          coreE := fun j => if firstReb ≤ j ∧ j < cfg.P.d then (C'.activeCore j).E else D.coreE j
          emb := fun j => if firstReb ≤ j ∧ j < cfg.P.d then C'.activeEmb j else D.emb j } : SelBlocksData)).E (B.d - 1) := by
        rw [hBd, hD1Last.1]; exact hsub he
      have h := hpart e he'
      have hlenEq : (({ D with
          F := fun j => if firstReb ≤ j ∧ j < cfg.P.d then (C'.activeLSF j).F.F else D.F j
          E := fun j => if firstReb ≤ j ∧ j < cfg.P.d then (C'.G j).E else D.E j
          len := fun j => if firstReb ≤ j ∧ j < cfg.P.d then C'.chainLen modelPre.chain.ℓ (j + 1) else D.len j
          coreE := fun j => if firstReb ≤ j ∧ j < cfg.P.d then (C'.activeCore j).E else D.coreE j
          emb := fun j => if firstReb ≤ j ∧ j < cfg.P.d then C'.activeEmb j else D.emb j } : SelBlocksData)).len (B.d - 1) =
          C'.chainLen modelPre.chain.ℓ cfg.P.d := by
        rw [hBd]; exact hD1Last.2
      rwa [hlenEq] at h
    have hTermRep2 := hrep2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hTags2 := hrep2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have hOwn2 := hTags2.1
    have hT19 := hTags2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hFoot2Sc : ∀ a, Rrep.foot root tok2 a → a < sc2 := fun a ha => by
      rcases hft2 a ha with h1 | hnew
      · exact lt_of_lt_of_le (hFoot1Sc a h1) hsc2Lo
      · exact hnew.2
    have hFoot2Disj : ∀ a, sb ≤ a → a < B.endAddr → ¬ Rrep.foot root tok2 a := fun a h1 h2 ha => by
      rcases hft2 a ha with h1' | hnew
      · exact hFoot1Disj a h1 h2 h1'
      · omega
    have hTermDisj2 : tok2.termTok ≤ B.base ∨ (B.endAddr ≤ tok2.termHandle ∧ tok2.termTok ≤ sc2) := by
      have hTermPos : tok2.termHandle < tok2.termTok := by
        have := hTermRep2.1; have := hmodNew.1.2.2.2.1; omega
      have hTermFt : ∀ x, tok2.termHandle ≤ x → x < tok2.termTok → Rrep.foot root tok2 x :=
        fun x h1 h2 => Or.inl (hOwn2 x (by
          have hft : (LastLevelProgram.lastLevelRepresentation tok2.vcLast tok2.ecLast 4 L 0
              (modelPre.chain.G cfg.P.d).E).foot tok2.termHandle tok2.termTok x := ⟨h1, h2⟩
          rw [hT19 x hft]; decide))
      have hSc : tok2.termTok ≤ sc2 := by
        have := hFoot2Sc (tok2.termTok - 1) (hTermFt _ (by omega) (by omega)); omega
      have hD := interval_disj_region (a := tok2.termHandle) (len := tok2.termTok - tok2.termHandle)
        (by omega) hsbLtEnd (fun x hx1 hx2 ⟨h1, h2⟩ => hFoot2Disj x hx1 hx2 (hTermFt x h1 (by omega)))
      rcases hD with hL | hR
      · left; omega
      · right; exact ⟨hR, hSc⟩
    have hPrevDisj := prevLen_disj_last (B := B) (by omega)
    have hFdV : ∀ v ∈ (modelPre.chain.lastLSFs modelPre.chain.lastBran).F.F.V, v < B.vCap := by
      rw [hBv, ← hLastLSF]; exact hFV cfg.P.d le_rfl
    have hFdE : ∀ e ∈ (modelPre.chain.lastLSFs modelPre.chain.lastBran).F.F.E, e < B.eCap := by
      rw [hBe, ← hLastLSF]; exact hFE cfg.P.d le_rfl
    have hTermRep2B : (LastLevelProgram.lastLevelRepresentation tok2.vcLast tok2.ecLast 4 B.Lk P
        (modelPre.chain.G cfg.P.d).E).rep tok2.termHandle
        (modelPre.chain.lastK, modelPre.chain.lastLSFs) tok2.termTok st2.mem := by
      rw [hBLk]; exact hTermRep2
    obtain ⟨sc3, c3, st3, hr3, hsc3Eq, hblk3, hz3, hfr3, hc3⟩ :=
      selectFillLastLevel_runs_disj (termBran := modelPre.chain.lastBran)
        hw16 hpLastW (hBLk.symm ▸ hLkW) htab2 hblk2 (by omega) (by omega)
        hGdAt2 hGdDisj2 (by omega)
        (by rw [hBv]; exact hVcap cfg.P.d le_rfl) (by rw [hBe]; exact hEcap cfg.P.d le_rfl)
        hTermRep2B hmodNew.1.2.2.2.2.2.1 hTermDisj2 hFdV hFdE
        (by omega) (Or.inl hPrevDisj.2.1) (Or.inl hPrevDisj.1) (Or.inl hPrevDisj.2.2) hPrevVal2
        (fun e he => by
          have hPV : EdgeValuesAt st2.mem (B.lenPtr (cfg.P.d - 1)) 4 L P
              (modelPre.chain.G cfg.P.d).E (C'.chainLen modelPre.chain.ℓ cfg.P.d) := by
            simpa only [hBd, hBLk] using hPrevVal2
          have h := hLenFitLast hReb e he st2.mem hPV
          rw [hBLk, hBd]
          simpa only [C', TreeChain.chainLen, coreLen, TreeChain.activeLSF, ChainState.toTreeChain,
            lt_irrefl, ↓reduceIte] using h)
        (by rw [hBv, hBe]; exact hDgCopyLastG)
        (by rw [hBv, hBe, hvc2Eq, hvc1Eq, hec2Eq, hec1Eq, hBd, ← hLastLSF]
            simpa only [show ¬ (firstReb ≤ cfg.P.d ∧ cfg.P.d < cfg.P.d) by omega, ↓reduceIte]
              using hDgCopyLastF)
        (by rw [hBe]; exact hCoreLen) hz2
        (by rw [hBLk, ← hLastLSF]; omega)
    have hSt3OffB : ∀ a < sc2, ¬ (B.base ≤ a ∧ a < B.endAddr) → st3.mem a = st2.mem a :=
      fun a ha hnot => hfr3 a ha
        (fun h => hnot (regLast_F_Len_in_B (Or.inl h)))
        (fun h => hnot (regLast_F_Len_in_B (Or.inr (Or.inl h))))
        (fun h => hnot (regLast_F_Len_in_B (Or.inr (Or.inr h))))
    have hRrepLoc := solverStateRep_local cfg L P m V psi k epsExp drainUnit hlocalCore
    have hFoot2Ag3 : ∀ a, Rrep.foot root tok2 a → st3.mem a = st2.mem a := fun a ha =>
      hSt3OffB a (hFoot2Sc a ha) fun hb => hFoot2Disj a (by omega) hb.2 ha
    have hrep3 : Rrep.rep root modelPre tok2 st3.mem :=
      (hRrepLoc root modelPre tok2 st2.mem st3.mem fun a ha => (hFoot2Ag3 a ha).symm).1 hrep2
    have hphi3 : Rrep.phi root tok2 st3.mem = Rrep.phi root tok2 st2.mem :=
      ((hRrepLoc root modelPre tok2 st2.mem st3.mem fun a ha => (hFoot2Ag3 a ha).symm).2).symm
    have hcaps3 : SolverLevelCapsInv P V vCap eCap modelPre tok2 st3.mem :=
      hcaps2.preserve rfl (fun j hj => hcaps2.1.2.1 j hj)
        (fun a ha => by
          have hne : tok2.tag a ≠ 0 := by rcases ha with h | h | h | h <;> omega
          exact ⟨rfl, hFoot2Ag3 a (Or.inl (hOwn2 a hne))⟩)
        (fun j hj => (SolverLevelMetaAt.atCaps hcaps2.1 hcaps2.2 j hj).2.2.1)
        rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl
    have hGPtrEq2 : ∀ j < cfg.P.d, solverLevelG tok2 st2.mem j = solverLevelG tok' mem j := by
      intro j hj
      have htg := hcaps.1.2.2.2.2.1 (cfg.P.d + j) (by omega)
      rw [← Nat.add_assoc] at htg
      have hTags0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      have hOwn0 := hTags0.1
      have hCoreT0 := hTags0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      have hCoreT1 := hrep1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      have hLt0 := hFootSc _ (Or.inl (hOwn0 _ (by rw [htg]; omega)))
      have htg1 : tok1.tag (solverLevelMetaAddr tok'.table cfg.P.d + cfg.P.d + j) = 22 + cfg.P.d :=
        (htag1Ne _ (by rw [htg]; omega)).trans htg
      change st2.mem (solverLevelMetaAddr tok2.table cfg.P.d + cfg.P.d + j) =
        mem (solverLevelMetaAddr tok'.table cfg.P.d + cfg.P.d + j)
      rw [htab2Eq, htab1Eq]
      rw [hfr2 _ (by omega) fun hc => by have := hCoreT1 (cfg.P.d - 1) (by omega) _ hc; rw [htg1] at this; omega]
      exact hfr1 _ hLt0 (fun hb => hFootDisj _ (by omega) hb.2 (Or.inl (hOwn0 _ (by rw [htg]; omega))))
        (fun ⟨i, _, hi, hc⟩ => by have := hCoreT0 i hi _ hc; rw [htg] at this; omega)
    have hGPtrEq3 : ∀ j < cfg.P.d, solverLevelG tok2 st3.mem j = solverLevelG tok' mem j := fun j hj => by
      have htg := hcaps2.1.2.2.2.2.1 (cfg.P.d + j) (by omega)
      rw [← Nat.add_assoc] at htg
      exact (hFoot2Ag3 _ (Or.inl (hOwn2 _ (by rw [htg]; omega)))).trans (hGPtrEq2 j hj)
    set mloc := selectMlocOf B metaBase (solverLevelG tok' mem) pLast
    have hMlocEq2 : selectMlocOf B metaBase (solverLevelG tok2 st2.mem) pLast = mloc := by
      unfold mloc selectMlocOf; congr 1
      · funext j; by_cases hj : j < B.d <;> simp [hj]; exact hGPtrEq2 j (by omega)
      · funext j; by_cases hj1 : j + 1 < B.d <;> simp [hj1]; exact hGPtrEq2 (j + 1) (by omega)
    have htab3 : SelectMetaTableAt st3.mem mloc :=
      (hMlocEq2 ▸ htab2).of_agree fun a _ h2 => hSt3OffB a (by dsimp only [mloc, selectMlocOf] at h2; omega)
        (by dsimp only [mloc, selectMlocOf] at h2; omega)
    have hHeap3 : SelectHeapAt st3.mem loc 4 heapSize :=
      hHeap2.of_agree fun a _ h2 => hSt3OffB a (by have := hreg.2.1; have := hreg.2.2.1; omega)
        (by have := hreg.2.1; have := hreg.2.2.1; omega)
    -- Step 4: `selectPhiLoopBody` from `firstReb` to `cfg.P.d`
    have hGEnd3 : ∀ j < cfg.P.d,
        solverLevelG tok' mem j + dynGraphSize vCap eCap ≤ sc3 ∧
        (solverLevelG tok' mem j + dynGraphSize vCap eCap ≤ sb ∨ B.endAddr ≤ solverLevelG tok' mem j) := by
      intro j hj
      have hAt := SolverLevelMetaAt.atCaps hcaps3.1 hcaps3.2 j hj
      rw [show solverLevelG tok' mem j = solverLevelG tok2 st3.mem j from (hGPtrEq3 j hj).symm]
      have hDGP : 0 < dynGraphSize vCap eCap := by unfold dynGraphSize; omega
      have hSc : solverLevelG tok2 st3.mem j + dynGraphSize vCap eCap ≤ sc3 := by
        have htg := hAt.2.2.2.2 (solverLevelG tok2 st3.mem j + dynGraphSize vCap eCap - 1)
          (by unfold solverLevelG; omega) (by unfold solverLevelG; omega)
        have hne : tok2.tag (solverLevelG tok2 st3.mem j + dynGraphSize vCap eCap - 1) ≠ 0 := by
          split_ifs at htg <;> omega
        have := hFoot2Sc _ (Or.inl (hOwn2 _ hne)); omega
      have hD := interval_disj_region (a := solverLevelG tok2 st3.mem j)
        (len := dynGraphSize vCap eCap) hDGP hsbLtEnd fun x hx1 hx2 hx => by
        have htg := hAt.2.2.2.2 x (by unfold solverLevelG at hx; exact hx.1)
          (by unfold solverLevelG at hx; exact hx.2)
        have hne : tok2.tag x ≠ 0 := by split_ifs at htg <;> omega
        exact hFoot2Disj x hx1 hx2 (Or.inl (hOwn2 x hne))
      exact ⟨hSc, hD⟩
    have hGDG3 : ∀ j ≤ cfg.P.d, DynGraphAt st3.mem (mloc.GPtr j) (mloc.vCap j) (mloc.eCap j) (C'.G j) := by
      intro j hj
      dsimp only [mloc, selectMlocOf]; rw [hBd, hBv, hBe]
      by_cases hlt : j < cfg.P.d
      · simp only [hlt, ↓reduceIte]
        rw [show solverLevelG tok' mem j = solverLevelG tok2 st3.mem j from (hGPtrEq3 j hlt).symm]
        exact (SolverLevelMetaAt.atCaps hcaps3.1 hcaps3.2 j hlt).1
      · have hjeq : j = cfg.P.d := by omega
        subst hjeq; simp only [lt_irrefl, ↓reduceIte]; rw [← hBv, ← hBe]; exact hblk3.2.2.2.2.1
    have hF3 : ∀ j ≤ cfg.P.d, SelPartF st3.mem B j (C'.activeLSF j).F.F := by
      intro j hj
      have hf := hblk3.1 j (by omega)
      dsimp only at hf
      by_cases hjd : j = B.d
      · subst hjd; simp only [Function.update_self] at hf
        have hL : C'.activeLSF B.d = modelPre.chain.lastLSFs modelPre.chain.lastBran := hBd.symm ▸ hLastLSF
        rw [hL]; exact hf
      · rw [Function.update_of_ne hjd] at hf
        by_cases hfr : firstReb ≤ j
        · have hr : firstReb ≤ j ∧ j < cfg.P.d := ⟨hfr, by omega⟩
          simpa only [hr, and_self, ↓reduceIte] using hf
        · have hnr : ¬ (firstReb ≤ j ∧ j < cfg.P.d) := by omega
          simp only [hnr, ↓reduceIte] at hf
          rw [(hPrefBlocks j (by omega)).1] at hf; exact hf
    have hPref3 : SelectPhiPrefixAt st3.mem mloc 4 P C' modelPre.chain.g D.φ firstReb := by
      refine ⟨by simp only [mloc, selectMlocOf, hBd]; rfl, htab3.1, htab3.2.1, ?_, fun k hk => ?_⟩
      · have hg0 := hblk3.2.2.2.2.2.2
        dsimp only at hg0; rw [hG0Match.1, hG0Match.2] at hg0
        simpa only [mloc, selectMlocOf, hBLk, C', ChainState.toTreeChain] using hg0
      · have hkLe : k ≤ cfg.P.d := by omega
        have hrow := htab3.2.2 k (by simp only [mloc, selectMlocOf, hBd]; exact hkLe)
        have hph := (hblk3.2.1 k (by omega)).2
        dsimp only at hph
        rw [(hPrefBlocks k (by omega)).2.1] at hph
        exact ⟨hrow.1, hrow.2.1, hrow.2.2.1, hrow.2.2.2.1, hGDG3 k hkLe,
          by simpa only [mloc, selectMlocOf, hBLk, C', ChainState.toTreeChain] using hph⟩
    have hLevels3 : ∀ j, firstReb ≤ j → j ≤ C'.d →
        st3.mem (smEntryAddr mloc.metaBase mloc.d 0 j) = mloc.GPtr j ∧
        st3.mem (smEntryAddr mloc.metaBase mloc.d 1 j) = mloc.vCap j ∧
        st3.mem (smEntryAddr mloc.metaBase mloc.d 2 j) = mloc.eCap j ∧
        st3.mem (smEntryAddr mloc.metaBase mloc.d 3 j) = mloc.phiPtr j ∧
        st3.mem (smEntryAddr mloc.metaBase mloc.d 6 j) = mloc.fPtr j ∧
        DynGraphAt st3.mem (mloc.GPtr j) (mloc.vCap j) (mloc.eCap j) (C'.G j) ∧
        DynGraphAt st3.mem (mloc.fPtr j) (mloc.vCap j) (mloc.eCap j) (C'.activeLSF j).F.F := by
      intro j _ hj
      have hrow := htab3.2.2 j (by simp only [mloc, selectMlocOf, hBd]; exact hj)
      exact ⟨hrow.1, hrow.2.1, hrow.2.2.1, hrow.2.2.2.1, hrow.2.2.2.2.2.2.1, hGDG3 j hj, hF3 j hj⟩
    have hDisj3 := phiLoop_disj_helper (pLast := pLast) hBd hBv hBe hBLk hsbLeBase hMetaEnd
      (by omega) hGEnd3
    obtain ⟨sc4, c4, st4, φ', hr4, hsc4Lo, hsc4Hi, hz4, hφKeep, hpref4, hpot4, hphiBd4, hfr4, hc4⟩ :=
      selectPhiLoop_runs (ω := ω) (PhiBd := PhiBd) hpPhiLoop hPhiFill hw16 hw10 hmodNew.1
        (by simpa only [mloc, selectMlocOf, hBe, C', ChainState.toTreeChain] using hEcap 0 (Nat.zero_le _))
        hPhiBdStep
        (fun j hj φ0 hpot0 hbd0 => by simpa only [mloc, selectMlocOf, hBLk] using hPhiFit j hj φ0 hpot0 hbd0)
        (C'.d + 1 - firstReb) firstReb sc3 st3.pos st3.mem D.φ rfl
        (by simp only [mloc, selectMlocOf]; omega) (by omega)
        (by change cfg.P.d < 2 ^ w; omega)
        (by simp only [mloc, selectMlocOf, hBLk]; exact hLkW)
        hPref3 (fun k hk => hPotPref k hk (by omega)) (fun k hk => hPhiBdPref k hk (by omega))
        hLevels3 (fun j _ hj => hDisj3 j hj) hz3
        (by simp only [mloc, selectMlocOf, hBLk]; rw [hBLk, ← hLastLSF] at hsc3Eq
            dsimp only [C'] at hroom hsc3Eq ⊢; omega)
    have hPhiInB : ∀ j ≤ cfg.P.d,
        B.base ≤ B.phiPtr j ∧ B.phiPtr j + B.vCap * B.Lk ≤ B.lastGPtr := fun j hj => by
      have hbl := B.blk_le_last (j := j) (by omega)
      unfold SelectBlocksLoc.levelSize at hbl
      have hbf : B.base ≤ B.fPtr j := by unfold SelectBlocksLoc.fPtr; omega
      unfold SelectBlocksLoc.phiPtr; omega
    have hSt4OffB : ∀ a < sc3, ¬ (B.base ≤ a ∧ a < B.endAddr) → st4.mem a = st3.mem a := fun a ha hnot =>
      hfr4 a ha fun j _ hj => by
        have := hPhiInB j hj; simp only [mloc, selectMlocOf]; omega
    have hFoot2Ag4 : ∀ a, Rrep.foot root tok2 a → st4.mem a = st3.mem a := fun a ha =>
      hSt4OffB a (lt_of_lt_of_le (hFoot2Sc a ha) (by omega)) fun hb => hFoot2Disj a (by omega) hb.2 ha
    have hrep4 : Rrep.rep root modelPre tok2 st4.mem :=
      (hRrepLoc root modelPre tok2 st3.mem st4.mem fun a ha => (hFoot2Ag4 a ha).symm).1 hrep3
    have hphi4 : Rrep.phi root tok2 st4.mem = Rrep.phi root tok2 st3.mem :=
      ((hRrepLoc root modelPre tok2 st3.mem st4.mem fun a ha => (hFoot2Ag4 a ha).symm).2).symm
    have hcaps4 : SolverLevelCapsInv P V vCap eCap modelPre tok2 st4.mem :=
      hcaps3.preserve rfl (fun j hj => hcaps3.1.2.1 j hj)
        (fun a ha => by
          have hne : tok2.tag a ≠ 0 := by rcases ha with h | h | h | h <;> omega
          exact ⟨rfl, hFoot2Ag4 a (Or.inl (hOwn2 a hne))⟩)
        (fun j hj => (SolverLevelMetaAt.atCaps hcaps3.1 hcaps3.2 j hj).2.2.1)
        rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl
    have hMlocEq4 : selectMlocOf B metaBase (solverLevelG tok2 st4.mem) pLast = mloc := by
      have hG4 : ∀ j < cfg.P.d, solverLevelG tok2 st4.mem j = solverLevelG tok' mem j := fun j hj => by
        have htg := hcaps3.1.2.2.2.2.1 (cfg.P.d + j) (by omega)
        rw [← Nat.add_assoc] at htg
        exact (hFoot2Ag4 _ (Or.inl (hOwn2 _ (by rw [htg]; omega)))).trans (hGPtrEq3 j hj)
      unfold mloc selectMlocOf; congr 1
      · funext j; by_cases hj : j < B.d <;> simp [hj]; exact hG4 j (by omega)
      · funext j; by_cases hj1 : j + 1 < B.d <;> simp [hj1]; exact hG4 (j + 1) (by omega)
    have htab4 : SelectMetaTableAt st4.mem (selectMlocOf B metaBase (solverLevelG tok2 st4.mem) pLast) := by
      rw [hMlocEq4]
      exact htab3.of_agree fun a _ h2 => hSt4OffB a (by dsimp only [mloc, selectMlocOf] at h2; omega)
        (by dsimp only [mloc, selectMlocOf] at h2; omega)
    have hHeap4 : SelectHeapAt st4.mem loc 4 heapSize :=
      hHeap3.of_agree fun a _ h2 => hSt4OffB a (by have := hreg.2.1; have := hreg.2.2.1; omega)
        (by have := hreg.2.1; have := hreg.2.2.1; omega)
    have hBlocks4 : SelectBlocksAt st4.mem B P C' modelPre.chain.g modelPre.chain.ℓ φ' pLast := by
      have hNotPhi : ∀ a, (a < B.base ∨ B.lastGPtr ≤ a) →
          ∀ j, firstReb ≤ j → j ≤ C'.d → a < mloc.phiPtr j ∨ mloc.phiPtr j + mloc.vCap j * mloc.Lk ≤ a :=
        fun a ha j _ hj => by have := hPhiInB j hj; simp only [mloc, selectMlocOf]; omega
      refine ⟨fun j hj => hBv ▸ hVcap j (by omega), fun j hj => hBe ▸ hEcap j (by omega),
        fun j hj => (hF3 j (by omega)).of_agree fun a ha =>
          hfr4 a (by have := B.blk_le_last hj; have := B.regF_blk ha; unfold SelectBlocksLoc.regBlk at this; omega)
            fun j' _ hj' => by
              have hnp : ¬ B.regPhi j' a := fun hp => by
                by_cases hEq : j' = j
                · subst hEq; exact B.regF_not_phi ha hp
                · exact B.regBlk_disj hEq (B.regPhi_blk hp) (B.regF_blk ha)
              simp only [mloc, selectMlocOf]; unfold SelectBlocksLoc.regPhi SelectBlocksLoc.lenPtr at hnp; omega,
        fun j hj => by
          have hj' : j < C'.d + 1 := by change j < cfg.P.d + 1; omega
          have hp := (hpref4.2.2.2.2 j hj').2.2.2.2.2
          simpa only [mloc, selectMlocOf] using hp,
        fun j hj => by
          have hlen3 := hblk3.2.2.1 j hj
          have hlen3' : SelPartLen st3.mem B P j (C'.G j).E (C'.chainLen modelPre.chain.ℓ (j + 1)) pLast := by
            dsimp only at hlen3
            by_cases hjd : j = B.d
            · subst hjd; simp only [Function.update_self] at hlen3
              have hEqE : (C'.G B.d).E = (modelPre.chain.G cfg.P.d).E := by rw [hBd]; rfl
              have hEqLen : C'.chainLen modelPre.chain.ℓ (B.d + 1) =
                  fun e => (modelPre.chain.lastLSFs modelPre.chain.lastBran).wstr e *
                    C'.chainLen modelPre.chain.ℓ cfg.P.d e := by
                funext e; rw [hBd]
                simp only [C', TreeChain.chainLen, coreLen, TreeChain.activeLSF, ChainState.toTreeChain,
                  lt_irrefl, ↓reduceIte]
              rw [hEqE, hEqLen]; exact hlen3
            · simp only [Function.update_of_ne hjd] at hlen3
              by_cases hfr : firstReb ≤ j
              · have hr : firstReb ≤ j ∧ j < cfg.P.d := ⟨hfr, by omega⟩
                simpa only [hr, and_self, ↓reduceIte] using hlen3
              · have hnr : ¬ (firstReb ≤ j ∧ j < cfg.P.d) := by omega
                simp only [hnr, ↓reduceIte] at hlen3
                have hPB := hPrefBlocks j (by omega)
                rw [hPB.2.2.1, hPB.2.2.2.1] at hlen3; exact hlen3
          exact (hlen3'.of_agree fun a ha =>
            hfr4 a (by have := B.blk_le_last hj; have := B.regLen_blk ha; unfold SelectBlocksLoc.regBlk at this; omega)
              fun j' _ hj' => by
                have hnp : ¬ B.regPhi j' a := fun hp => by
                  by_cases hEq : j' = j
                  · subst hEq; exact B.regPhi_not_len hp ha
                  · exact B.regBlk_disj hEq (B.regPhi_blk hp) (B.regLen_blk ha)
                simp only [mloc, selectMlocOf]; unfold SelectBlocksLoc.regPhi SelectBlocksLoc.lenPtr at hnp; omega).2,
        fun j hj => by
          have hemb3 := hblk3.2.2.2.1 j hj
          have hemb3' : SelPartEmb st3.mem B j (C'.activeCore j).E (C'.activeEmb j) := by
            dsimp only at hemb3
            by_cases hfr : firstReb ≤ j
            · have hr : firstReb ≤ j ∧ j < cfg.P.d := ⟨hfr, by omega⟩
              simpa only [hr, and_self, ↓reduceIte] using hemb3
            · have hnr : ¬ (firstReb ≤ j ∧ j < cfg.P.d) := by omega
              simp only [hnr, ↓reduceIte] at hemb3
              have hPB := hPrefBlocks j (by omega)
              rw [hPB.2.2.2.2.1, hPB.2.2.2.2.2] at hemb3; exact hemb3
          exact hemb3'.of_agree fun a ha =>
            hfr4 a (by have := B.blk_le_last hj.le; have := B.regEmb_blk ha; unfold SelectBlocksLoc.regBlk at this; omega)
              fun j' _ hj' => by
                have hnp : ¬ B.regPhi j' a := fun hp => by
                  by_cases hEq : j' = j
                  · subst hEq; exact B.regPhi_not_emb hp ha
                  · exact B.regBlk_disj hEq (B.regPhi_blk hp) (B.regEmb_blk ha)
                simp only [mloc, selectMlocOf]; unfold SelectBlocksLoc.regPhi SelectBlocksLoc.lenPtr at hnp; omega,
        hBd.symm ▸ (hblk3.2.2.2.2.1).of_agree fun a ha =>
          hfr4 a (by unfold SelectBlocksLoc.regLast SelectBlocksLoc.g0Ptr at ha; omega) (hNotPhi a (Or.inr ha.1)),
        ((hG0Match.1 ▸ hG0Match.2 ▸ hblk3.2.2.2.2.2).of_agree fun a ha =>
          hfr4 a (by unfold SelectBlocksLoc.regG0 at ha; omega)
            (hNotPhi a (Or.inr (by unfold SelectBlocksLoc.regG0 SelectBlocksLoc.g0Ptr at ha; omega)))).2⟩
    -- Stitch the `then` branch of `selectUpdateSuffixBlocksBody`
    have hCoreLast := hrep1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (cfg.P.d - 1) (by omega)
    have hEntLt : smEntryAddr metaBase B.d 4 (B.d - 1) < 2 ^ w := by
      unfold smEntryAddr smTableOff; omega
    have hRowLast := htab2.2.2 (B.d - 1) (by dsimp only [selectMlocOf]; omega)
    have hLenLastM : st2.mem (smEntryAddr metaBase B.d 4 (B.d - 1)) = B.lenPtr (B.d - 1) := by
      simpa [selectMlocOf] using hRowLast.2.2.2.2.1
    have hHnd1Lt : tok1.handle + 18 + (cfg.P.d + 1) + (cfg.P.d - 1) < sc1 := by
      have hTags1 := hrep1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      have hOwn1 := hTags1.1
      have hT4 := hTags1.2.2.2.2.1
      have htg := hT4 ((cfg.P.d + 1) + (cfg.P.d - 1)) (by omega)
      have heq : tok1.handle + 18 + (cfg.P.d + 1) + (cfg.P.d - 1) =
          tok1.handle + 18 + ((cfg.P.d + 1) + (cfg.P.d - 1)) := by omega
      rw [heq]; exact hFoot1Sc _ (Or.inl (hOwn1 _ (by rw [htg]; decide)))
    let rg11 := Function.update s0.regs 11 sc1
    let rg12 := Function.update rg11 12 (cfg.P.d - 1)
    let rg13 := Function.update rg12 13 (tok1.coreHandle (cfg.P.d - 1))
    let rg14 := Function.update rg13 14 (modelPre.chain.bran (cfg.P.d - 1))
    let rg15 := Function.update rg14 15 sc2
    let rg16 := Function.update rg15 16 srcGd
    let rg17 := Function.update rg16 17 (B.lenPtr (B.d - 1))
    let rg18 := Function.update rg17 18 sc3
    let rg19 := Function.update rg18 19 sc4
    have r1 : Runs w p ω (.call 11 initIntLoop [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 7, .reg 8, .reg 10])
        s0 .normal ⟨st1.mem, rg11, st1.pos⟩ (c1 + 9) :=
      runs_call_iff.mpr ⟨[metaBase, firstReb, cfg.P.d, tok'.handle + 18,
          solverLevelMetaAddr tok'.table cfg.P.d, L, B.slot, scratch], _, .returned sc1, st1, c1,
        by simp [evalArgs, Expr.eval, s0, startState], hpInitInt, hr1, rfl, rfl,
        by simp [argsSize, Expr.size]; omega⟩
    have r2 : Runs w p ω (.assign 12 (.bin .sub (.reg 2) (.const 1)))
        ⟨st1.mem, rg11, st1.pos⟩ .normal ⟨st1.mem, rg12, st1.pos⟩ 4 :=
      runs_assign_iff.mpr ⟨cfg.P.d - 1, by
        simp [Expr.eval, BinOp.eval, rg11, s0, startState, show 1 < 2 ^ w by omega,
          show cfg.P.d - 1 < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
    have r3 : Runs w p ω (.assign 13 (.load (.bin .add (.reg 3) (.reg 12))))
        ⟨st1.mem, rg12, st1.pos⟩ .normal ⟨st1.mem, rg13, st1.pos⟩ 5 :=
      runs_assign_iff.mpr ⟨tok1.coreHandle (cfg.P.d - 1), by
        simp [Expr.eval, BinOp.eval, rg12, rg11, s0, startState, hhnd1Eq.symm, hCoreLast.1,
          show tok1.handle + 18 + (cfg.P.d - 1) < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
    have r4 : Runs w p ω
        (.assign 14 (.load (.bin .add (.bin .add (.reg 3) (.bin .add (.reg 2) (.const 1))) (.reg 12))))
        ⟨st1.mem, rg13, st1.pos⟩ .normal ⟨st1.mem, rg14, st1.pos⟩ 9 :=
      runs_assign_iff.mpr ⟨modelPre.chain.bran (cfg.P.d - 1), by
        simp [Expr.eval, BinOp.eval, rg13, rg12, rg11, s0, startState, hhnd1Eq.symm, hCoreLast.2.1,
          show 1 < 2 ^ w by omega, show cfg.P.d + 1 < 2 ^ w by omega,
          show tok1.handle + 18 + (cfg.P.d + 1) < 2 ^ w by omega,
          show tok1.handle + 18 + (cfg.P.d + 1) + (cfg.P.d - 1) < 2 ^ w by omega],
        rfl, rfl, by simp [Expr.size]⟩
    have r5 : Runs w p ω (.call 15 (op 3) [.reg 13, .reg 14, .reg 11])
        ⟨st1.mem, rg14, st1.pos⟩ .normal ⟨st2.mem, rg15, st2.pos⟩ (c2 + 4) :=
      runs_call_iff.mpr ⟨[tok1.coreHandle (cfg.P.d - 1), modelPre.chain.bran (cfg.P.d - 1), sc1],
        b3, o3, st2, c2, by simp [evalArgs, Expr.eval, rg14, rg13, rg12, rg11], hb3, hr2,
        rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
    have r6 : Runs w p ω (.assign 16 (.load (.reg 11)))
        ⟨st2.mem, rg15, st2.pos⟩ .normal ⟨st2.mem, rg16, st2.pos⟩ 3 :=
      runs_assign_iff.mpr ⟨srcGd, by simp [Expr.eval, rg15, rg14, rg13, rg12, rg11, srcGd],
        rfl, rfl, by simp [Expr.size]⟩
    have r7 : Runs w p ω
        (.assign 17 (.load (.bin .add (.bin .add (.bin .add (.reg 0) (.const smTableOff))
          (.bin .mul (.const 4) (.bin .add (.reg 2) (.const 1)))) (.reg 12))))
        ⟨st2.mem, rg16, st2.pos⟩ .normal ⟨st2.mem, rg17, st2.pos⟩ 13 :=
      runs_assign_iff.mpr ⟨B.lenPtr (B.d - 1), by
        simp [Expr.eval, BinOp.eval, rg16, rg15, rg14, rg13, rg12, rg11, s0, startState, hBd.symm,
          show smTableOff < 2 ^ w by unfold smTableOff; omega,
          show metaBase + smTableOff < 2 ^ w by unfold smTableOff; omega,
          show 1 < 2 ^ w by omega, show 4 < 2 ^ w by omega, show B.d + 1 < 2 ^ w by omega,
          show 4 * (B.d + 1) < 2 ^ w by omega,
          show metaBase + smTableOff + 4 * (B.d + 1) < 2 ^ w by unfold smTableOff; omega,
          show metaBase + smTableOff + 4 * (B.d + 1) + (B.d - 1) =
            smEntryAddr metaBase B.d 4 (B.d - 1) by unfold smEntryAddr; omega,
          hEntLt, hLenLastM],
        rfl, rfl, by simp [Expr.size]⟩
    have r8 : Runs w p ω
        (.call 18 fillLast [.reg 0, .reg 2, .reg 5, .reg 6, .reg 17, .reg 7, .reg 9, .reg 16, .reg 15])
        ⟨st2.mem, rg17, st2.pos⟩ .normal ⟨st3.mem, rg18, st3.pos⟩ (c3 + 10) :=
      runs_call_iff.mpr ⟨[metaBase, cfg.P.d, tok'.termHandle, modelPre.chain.lastBran,
          B.lenPtr (B.d - 1), L, pLast, srcGd, sc2], _, .returned sc3, st3, c3,
        by simp [evalArgs, Expr.eval, rg17, rg16, rg15, rg14, rg13, rg12, rg11, s0, startState],
        hpFillLast, by simpa only [hBd, hth2Eq, hth1Eq, hBLk] using hr3, rfl, rfl,
        by simp [argsSize, Expr.size]; omega⟩
    have r9 : Runs w p ω (.call 19 phiLoop [.reg 0, .reg 1, .reg 2, .reg 7, .reg 18])
        ⟨st3.mem, rg18, st3.pos⟩ .normal ⟨st4.mem, rg19, st4.pos⟩ (c4 + 6) :=
      runs_call_iff.mpr ⟨[metaBase, firstReb, cfg.P.d, L, sc3], _, .returned sc4, st4, c4,
        by simp [evalArgs, Expr.eval, rg18, rg17, rg16, rg15, rg14, rg13, rg12, rg11, s0, startState],
        hpPhiLoop, by simpa only [mloc, selectMlocOf, hBLk, C', ChainState.toTreeChain] using hr4,
        rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
    have r10 : Runs w p ω (.ret (.reg 19)) ⟨st4.mem, rg19, st4.pos⟩ (.returned sc4)
        ⟨st4.mem, rg19, st4.pos⟩ 2 :=
      runs_ret_iff.mpr ⟨sc4, by simp [Expr.eval, rg19], rfl, rfl, by simp [Expr.size]⟩
    have rFull : Runs w p ω (selectUpdateSuffixBlocksBody initIntLoop (op 3) fillLast phiLoop) s0
        (.returned sc4) ⟨st4.mem, rg19, st4.pos⟩ (c1 + c2 + c3 + c4 + 80) := by
      unfold selectUpdateSuffixBlocksBody
      refine runs_cond_iff.mpr ⟨1, _,
        by simp [Expr.eval, BinOp.eval, s0, startState, show 1 < 2 ^ w by omega,
          show cfg.P.d + 1 < 2 ^ w by omega, show firstReb < cfg.P.d + 1 by omega],
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, r1,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, r2,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, r3,
              runs_seq_iff.mpr (Or.inr ⟨_, _, _, r4,
                runs_seq_iff.mpr (Or.inr ⟨_, _, _, r5,
                  runs_seq_iff.mpr (Or.inr ⟨_, _, _, r6,
                    runs_seq_iff.mpr (Or.inr ⟨_, _, _, r7,
                      runs_seq_iff.mpr (Or.inr ⟨_, _, _, r8,
                        runs_seq_iff.mpr (Or.inr ⟨_, _, _, r9, r10, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
                rfl⟩), rfl⟩), rfl⟩), rfl⟩),
        by simp [Expr.size]; omega⟩
    refine ⟨sc4, c1 + c2 + c3 + c4 + 80, ⟨st4.mem, rg19, st4.pos⟩, tok2, φ', rFull,
      by omega,
      by rw [hSpEq]; simp only [mloc, selectMlocOf, hBLk] at hsc4Hi; rw [hBLk, ← hLastLSF] at hsc3Eq
         dsimp only [C'] at hsc3Eq hsc4Hi ⊢; omega,
      hrep4, htab2Eq.trans htab1Eq, hhnd2Eq.trans hhnd1Eq, hlev2Eq.trans hlev1Eq,
      hint2Eq.trans hint1Eq, hrec2Eq.trans hrec1Eq, htree2Eq.trans htree1Eq,
      htrees2Eq.trans htrees1Eq, hedg2Eq.trans hedg1Eq, hth2Eq.trans hth1Eq, htt2Eq.trans htt1Eq,
      hvc2Eq.trans hvc1Eq, hec2Eq.trans hec1Eq,
      fun a ha => by
        rcases hft2 a ha with h1 | hnew2
        · rcases hft1 a h1 with h0 | hnew1
          · exact Or.inl h0
          · exact Or.inr ⟨hnew1.1, by omega⟩
        · exact Or.inr ⟨by omega, by omega⟩,
      fun a ha => hown2 a (hown1 a ha),
      fun a ha => (htag2Lt a (by omega)).trans (htag1Lt a ha),
      fun a ha => (htag2Ne a (by rw [htag1Ne a ha]; exact ha)).trans (htag1Ne a ha),
      hcaps4, htab4, hHeap4, hBlocks4, hφKeep, hpot4, hphiBd4, hz4,
      fun a ha hnb hncTag => by
        have hTags0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        have hCoreT0 := hTags0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        have hCoreT1 := hrep1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        have hnc1 : ¬ Rcore.foot (tok1.coreHandle (cfg.P.d - 1)) (tok1.coreTok (cfg.P.d - 1)) a := fun hc => by
          have ht1 := hCoreT1 (cfg.P.d - 1) (by omega) a hc
          exact hncTag (cfg.P.d - 1) (by omega) ((htag1Lt a ha).symm.trans ht1)
        have hnc0 : ¬ (∃ j, firstReb ≤ j ∧ j < cfg.P.d ∧ Rcore.foot (tok'.coreHandle j) (tok'.coreTok j) a) :=
          fun ⟨j, _, hj, hc⟩ => hncTag j hj (hCoreT0 j hj a hc)
        exact (hSt4OffB a (by omega) hnb).trans
          ((hSt3OffB a (by omega) hnb).trans ((hfr2 a (by omega) hnc1).trans (hfr1 a ha hnb hnc0))), ?_⟩
    simp only [mloc, selectMlocOf, hBLk] at hc4
    rw [hCostEq, hphi4, hphi3]
    dsimp only at hc3
    simp only [hBd, lt_irrefl, and_false, ↓reduceIte, hBLk, ← hLastLSF] at hc3
    dsimp only [Rrep, C'] at hc1 hc2 hc3 hc4 ⊢
    omega
  · have hFREq : firstReb = cfg.P.d + 1 := by omega
    have hSpEq : selectUpdateSuffixBlocksSpace modelPre.chain firstReb L capExp = 0 := by
      unfold selectUpdateSuffixBlocksSpace; simp [hReb]
    have hCostEq : selectUpdateSuffixBlocksCost D.F D.Gd modelPre.chain Psc.readout firstReb L capExp B.slot = 12 := by
      unfold selectUpdateSuffixBlocksCost; simp [hReb]
    obtain ⟨hGdEq, hFdEq, hVdEq, hEdEq, hLendEq⟩ := hNoRebLast hFREq
    have hBlocks : SelectBlocksAt mem B P C' modelPre.chain.g modelPre.chain.ℓ D.φ pLast := by
      refine ⟨fun j hj => hBv ▸ hVcap j (by omega), fun j hj => hBe ▸ hEcap j (by omega),
        fun j hj => by
          have hf := hblk.1 j hj
          by_cases hjd : j = cfg.P.d
          · subst hjd; rwa [hFdEq] at hf
          · rwa [(hPrefBlocks j (by omega)).1] at hf,
        fun j hj => by
          have hp := (hblk.2.1 j hj).2
          by_cases hjd : j = cfg.P.d
          · subst hjd; rwa [hVdEq] at hp
          · rwa [(hPrefBlocks j (by omega)).2.1] at hp,
        fun j hj => by
          have hl := (hblk.2.2.1 j hj).2
          by_cases hjd : j = cfg.P.d
          · subst hjd
            intro e he
            have h1 := hl e (hEdEq.symm ▸ he)
            exact ⟨h1.1, h1.2.trans (hLendEq e he)⟩
          · have hPB := hPrefBlocks j (by omega); rwa [hPB.2.2.1, hPB.2.2.2.1] at hl,
        fun j hj => by
          have he := hblk.2.2.2.1 j hj
          have hPB := hPrefBlocks j (by omega)
          rwa [hPB.2.2.2.2.1, hPB.2.2.2.2.2] at he,
        by have hg := hblk.2.2.2.2.1; rw [hGdEq] at hg; exact hBd.symm ▸ hg,
        by have hg0 := hblk.2.2.2.2.2.2; rwa [hG0Match.1, hG0Match.2] at hg0⟩
    have rNoOp : Runs w p ω (selectUpdateSuffixBlocksBody initIntLoop (op 3) fillLast phiLoop) s0
        (.returned scratch) s0 8 := by
      unfold selectUpdateSuffixBlocksBody
      refine runs_cond_iff.mpr ⟨0, 2,
        by simp [Expr.eval, BinOp.eval, s0, startState, show 1 < 2 ^ w by omega,
          show cfg.P.d + 1 < 2 ^ w by omega, hFREq],
        runs_ret_iff.mpr ⟨scratch, by simp [Expr.eval, s0, startState], rfl, rfl, rfl⟩,
        by simp [Expr.size]⟩
    refine ⟨scratch, 8, s0, tok', D.φ, rNoOp, le_rfl, by omega, hrep,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      fun _ ha => Or.inl ha, fun _ ha => ha, fun _ _ => rfl, fun _ _ => rfl,
      hcaps, htab, hHeap, hBlocks, fun _ _ => rfl,
      fun j hj => hPotPref j (by change j ≤ cfg.P.d at hj; omega) hj,
      fun j hj => hPhiBdPref j (by omega) hj,
      hz, fun _ _ _ _ => rfl, by dsimp only [s0, startState]; rw [hCostEq]; omega⟩

end MinCostFlow.MinRatio
