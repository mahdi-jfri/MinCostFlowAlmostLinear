module

public import MinCostFlow.MinRatio.SelectInteriorFill
public import MinCostFlow.MinRatio.SelectInitLoop
public import MinCostFlow.MinRatio.SelectInitRepLemmas
public import MinCostFlow.MinRatio.SelectHeapInit
public import MinCostFlow.MinRatio.SelectRebuildNoRoom
import WordRAM.Tactic

/-!
# Select-region interior refresh loop and `G_d` readout for deep shift (`WireShiftDeepSelectLoop`)

Generalizes the interior fill loop and terminal-graph `op 3` readout from Init to in-place
refresh of an existing select region `[sb, B.endAddr)` whose newly rebuilt solver structures
(cores, level graphs, core-length tables, and terminal collection) may lie above `B.endAddr`:

* `SelectRegionAt`: complete layout and memory invariant of an in-place `SelectRegion sb loc B metaBase`
  with runtime pointers at `solverSelectHeapAddr` (`sb`) and `solverSelectBlocksAddr` (`B.base`),
  plus `SelectRegionAt.to_solverSelectInv`.
* `interval_disj_region`: any contiguous interval disjoint from `[sb, B.endAddr)` lies either
  strictly below `sb` or at/above `B.endAddr`.
* `selectRefreshInteriorLoop_runs`: verifies the unchanged `selectInitInteriorLoopBody` starting
  at any `cur ≤ cfg.P.d` over arbitrary existing `D.F j` and arbitrary heap size `heapSize`,
  with two-sided disjointness of solver footprints from `[sb, B.endAddr)`.
* `op3_gd_disj_runs`: runs `op 3` on core `d - 1` (`0 < d`), returning `srcGd` disjoint from
  `[B.base, B.endAddr)` while preserving `solverStateRep`, `SolverLevelCapsInv`, `SelectMetaTableAt`,
  `SelectHeapAt`, and `SelBlocksDataAt`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine Num DynSpanner.Program SparseCore.Program

/-! ## 1. Complete in-place select-region invariant `SelectRegionAt` -/

/-- Complete layout and memory invariant for an in-place select region `[sb, B.endAddr)` attached
to a solver state `(model, tok)` at global caps `(vCap, eCap)` and terminal stretch precision
`pLast`. -/
def SelectRegionAt {cfg : Alg2Config} {L : ℕ} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    (G : MGraph) (P m vCap eCap pLast sb metaBase : ℕ) (B : SelectBlocksLoc)
    (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (sg : SelectGhost)
    (mem : ℕ → ℕ) : Prop :=
  SelectRegion sb sg.loc B metaBase ∧
  sg.loc.cap = selectHeapCap cfg G m ∧
  B.d = cfg.P.d ∧ B.vCap = vCap ∧ B.eCap = eCap ∧ B.Lk = L ∧
  sg.owned = (fun a => sb ≤ a ∧ a < B.endAddr) ∧
  mem (solverSelectHeapAddr tok.table cfg.P.d) = sb ∧
  mem (solverSelectBlocksAddr tok.table cfg.P.d) = B.base ∧
  sg.mloc = selectMlocOf B metaBase (solverLevelG tok mem) pLast ∧
  SelectMetaTableAt mem (selectMlocOf B metaBase (solverLevelG tok mem) pLast) ∧
  SelectBlocksAt mem B P model.chain.toTreeChain model.chain.g model.chain.ℓ sg.φ pLast ∧
  SelectHeapMatchesChain mem sg.loc 4 P model.chain.toTreeChain model.chain.g
    model.chain.ℓ sg.size ∧
  SelectPotInv model.chain.toTreeChain model.chain.g sg.φ ∧
  sg.coreLen = (fun j => model.chain.toTreeChain.chainLen model.chain.ℓ (j + 1)) ∧
  ∃ (G₀ : MGraph) (σ σ_mwu γ_ℓ γ_c : ℝ), SelectModelInv model G₀ σ σ_mwu γ_ℓ γ_c

/-- Step cost bound for `selectInitInteriorLoopBody` refreshing levels `cur .. P.d - 1` when
existing forest blocks hold `oldF j`. -/
noncomputable def selectRefreshInteriorLoopCost {T : SparseCoreRestartTool} {P : ChainParams}
    (oldF : ℕ → MGraph) (C : ChainState T P) (readoutCost cur L capExp slot : ℕ) : ℕ :=
  (Finset.Ico cur P.d).sum (fun j =>
    let LwMax := L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (C.lvlM j + C.N₀ + 2) + 1)
    selectFillInteriorLevelCost readoutCost (oldF j).n (oldF j).m
      (C.toTreeChain.activeLSF j).F.F.n (C.toTreeChain.activeLSF j).F.F.m (C.G j).m L LwMax slot + 60) + 10

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine Num DynSpanner.Program SparseCore.Program

/-! ## 2. Region bridge and interval-disjointness helpers -/

/-- Any contiguous interval `[a, a + len)` of positive length disjoint from `[lo, hi)` lies either
entirely below `lo` or at/above `hi`. -/
theorem interval_disj_region {a len lo hi : ℕ} (hlen : 0 < len) (hlohi : lo < hi)
    (hdisj : ∀ x, lo ≤ x → x < hi → ¬ (a ≤ x ∧ x < a + len)) :
    a + len ≤ lo ∨ hi ≤ a := by
  by_contra h
  push Not at h
  by_cases hcmp : lo ≤ a
  · exact hdisj a hcmp h.2 ⟨le_refl a, by omega⟩
  · exact hdisj lo (le_refl lo) hlohi ⟨by omega, by omega⟩

/-- `SelectRegionAt` together with `SolverLevelCapsInv` and disjointness of `[sb, B.endAddr)`
from `foot` yields `SolverSelectInv` at `(dMul, kOff) = (4, 2)`. -/
theorem SelectRegionAt.to_solverSelectInv
    {cfg : Alg2Config} {L P V m vCap eCap pLast sb metaBase : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {G : MGraph} {B : SelectBlocksLoc}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {sg : SelectGhost}
    {foot : ℕ → Prop} {mem : ℕ → ℕ}
    (hR : SelectRegionAt G P m vCap eCap pLast sb metaBase B model tok sg mem)
    (hcaps : SolverLevelCapsInv P V vCap eCap model tok mem)
    (hFootDisj : ∀ a, sb ≤ a → a < B.endAddr → ¬ foot a) :
    SolverSelectInv G L P m 4 2 tok.table model foot (LevelMetaFoot tok) sg mem := by
  obtain ⟨hreg, hcap, hBd, hBv, hBe, hBLk, hOwn, hhb, _, hmloc, htab, hblk, hmatch, hpot,
    hcoreLen, G₀, σ, σ_mwu, γ_ℓ, γ_c, hmod⟩ := hR
  have hhbAddr : tok.table + 4 * cfg.P.d + 2 = solverSelectHeapAddr tok.table cfg.P.d := by
    unfold solverSelectHeapAddr solverLevelMetaAddr solverLvlMAddr solverN0Addr; omega
  have hhbFoot : LevelMetaFoot tok (tok.table + 4 * cfg.P.d + 2) :=
    Or.inr (Or.inl (hhbAddr ▸ hcaps.1.1.2.2.1))
  have hLvlGFoot : ∀ j < cfg.P.d,
      ∀ a, solverLevelG tok mem j ≤ a → a < solverLevelG tok mem j + dynGraphSize vCap eCap →
        LevelMetaFoot tok a := fun j hj a h1 h2 => by
    have htg := (SolverLevelMetaAt.atCaps hcaps.1 hcaps.2 j hj).2.2.2.2 a h1 h2
    split_ifs at htg with hj0
    · exact Or.inl htg
    · exact Or.inr (Or.inr (Or.inr htg))
  have hLvlGPtrFoot : ∀ j < cfg.P.d,
      LevelMetaFoot tok (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) := fun j hj => by
    have htg := hcaps.1.2.2.2.2.1 (cfg.P.d + j) (by omega)
    rw [← Nat.add_assoc] at htg
    exact Or.inr (Or.inr (Or.inl htg))
  have hbase := selectRegion_solverSelectInv (dMul := 4) (kOff := 2) hreg hcap hBd hBv hBe hBLk
    hFootDisj (hhbAddr.symm ▸ hreg.1.symm ▸ hhb) (Or.inl hhbFoot) hLvlGFoot hLvlGPtrFoot
    htab hblk hmatch hcaps hmod hpot
  rcases sg with ⟨loc, mloc, size, φ, coreLen, owned, rp⟩
  dsimp only at hOwn hmloc hcoreLen hbase ⊢
  subst hOwn hmloc hcoreLen
  exact hbase

private lemma reg_in_blocks_ref {B : SelectBlocksLoc} {j a : ℕ} (hj : j ≤ B.d)
    (h : B.regF j a ∨ B.regLen j a ∨ B.regEmb j a) : B.base ≤ a ∧ a < B.endAddr := by
  have h1 : B.base ≤ B.fPtr j := by unfold SelectBlocksLoc.fPtr; omega
  have h2 := B.blk_le_last hj
  have h3 : B.lastGPtr ≤ B.endAddr := by unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr; omega
  unfold SelectBlocksLoc.levelSize at h2
  rcases h with h | h | h
  · unfold SelectBlocksLoc.regF SelectBlocksLoc.phiPtr at h; omega
  · unfold SelectBlocksLoc.regLen SelectBlocksLoc.embPtr SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr at h; omega
  · unfold SelectBlocksLoc.regEmb SelectBlocksLoc.embPtr SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr SelectBlocksLoc.levelSize at h; omega

private lemma selectMlocOf_congr_ref {B : SelectBlocksLoc} {metaBase pLast : ℕ}
    {g₁ g₂ : ℕ → ℕ} (h : ∀ j < B.d, g₁ j = g₂ j) :
    selectMlocOf B metaBase g₁ pLast = selectMlocOf B metaBase g₂ pLast := by
  unfold selectMlocOf; congr 1
  · funext j; by_cases hj : j < B.d <;> simp [hj]; exact h j hj
  · funext j; by_cases hj : j < B.d <;> by_cases hj1 : j + 1 < B.d <;> simp [hj, hj1] <;> exact h (j + 1) hj1

/-! ## 3. Generalized interior refresh loop (`selectRefreshInteriorLoop_runs`) -/

set_option maxHeartbeats 1200000 in
/-- `selectInitInteriorLoopBody` refreshes `F`, `E`, `len`, `coreE`, and `emb` across interior
levels `cur .. cfg.P.d - 1` over arbitrary existing `D.F j` and arbitrary heap size `heapSize`,
with two-sided disjointness between `solverStateRep`'s footprint and `[sb, B.endAddr)`. -/
theorem selectRefreshInteriorLoop_runs
    {w L P m V psi k epsExp drainUnit : ℕ}
    {depth capExp vCap eCap sb metaBase pLast heapSize cur scratch pos : ℕ}
    {loopProc fillIntProc dgCopyProc coreLenProc filterProc embCopyProc : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config}
    {initialGraph : ℕ → MGraph} {Psc : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {op : ℕ → ℕ} {ω : ℕ → Bool}
    {root : ℕ} {model : Alg2State cfg} {tok : SolverToken cfg L Rcore}
    {loc : SelectHeapLoc} {B : SelectBlocksLoc} {D : SelBlocksData} {mem : ℕ → ℕ}
    (hfmt4 : fmt.limbBits = 4) (hfmtP : fmt.precision = P) (hlocalCore : Rcore.Local)
    (hw16 : 16 < 2 ^ w) (hLkW : L < 2 ^ w) (hSlotW : B.slot < 2 ^ w) (hkW : cfg.P.k < 2 ^ w)
    (hcurLe : cur ≤ cfg.P.d)
    (hreg : SelectRegion sb loc B metaBase)
    (hBd : B.d = cfg.P.d) (hBv : B.vCap = vCap) (hBe : B.eCap = eCap) (hBLk : B.Lk = L)
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hFootSc : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a → a < scratch)
    (hFootDisj : ∀ a, sb ≤ a → a < B.endAddr →
      ¬ (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a)
    (hEndSc : B.endAddr ≤ scratch)
    (hcaps : SolverLevelCapsInv P V vCap eCap model tok mem)
    (htab : SelectMetaTableAt mem (selectMlocOf B metaBase (solverLevelG tok mem) pLast))
    (hHeap : SelectHeapAt mem loc 4 heapSize)
    (hblk : SelBlocksDataAt mem B P D pLast)
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
      SparseCoreReadoutFootAt fmt L depth cfg.T (initialGraph j) cfg.P.k
        (model.chain.lvlM j) model.chain.N₀ vCap eCap capExp Psc allocation Rcore p op)
    (hDgCopy : ∀ j, cur ≤ j → j < cfg.P.d → ∀ vcF ecF,
      MeetsContract w p dgCopyProc
        (dgCopyRefillContract w vCap eCap vcF ecF (D.F j)
          (model.chain.toTreeChain.activeLSF j).F.F))
    (hCoreLen : ∀ eL : List ℕ, MeetsContract w p coreLenProc (selCoreLenFillContract w P eCap eL))
    (hFilter : ∀ eL : List ℕ, MeetsContract w p filterProc (selFilterAbsentContract w eL))
    (hEmbCopy : ∀ j, cur ≤ j → j < cfg.P.d → ∀ eL : List ℕ,
      MeetsContract w p embCopyProc (selEmbCopyContract w eL (model.chain.toTreeChain.activeEmb j)))
    (hz : ZeroFrom mem scratch)
    (hroom : scratch + selectInitInteriorLoopSpace model.chain cur L capExp < 2 ^ w) :
    let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
    let C := model.chain.toTreeChain
    ∃ scOut cost out tok',
      Runs w p ω (selectInitInteriorLoopBody loopProc fillIntProc)
        (startState [metaBase, cur, cfg.P.d, tok.handle + 18,
          solverLevelMetaAddr tok.table cfg.P.d, L, B.slot, scratch] mem pos)
        (.returned scOut) out cost ∧
      scratch ≤ scOut ∧
      scOut ≤ scratch + selectInitInteriorLoopSpace model.chain cur L capExp ∧
      Rrep.rep root model tok' out.mem ∧
      tok'.table = tok.table ∧ tok'.handle = tok.handle ∧
      tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧
      tok'.rootECap = tok.rootECap ∧
      tok'.tree = tok.tree ∧ tok'.trees = tok.trees ∧ tok'.edgeRecords = tok.edgeRecords ∧
      tok'.termHandle = tok.termHandle ∧ tok'.termTok = tok.termTok ∧
      tok'.vcLast = tok.vcLast ∧ tok'.ecLast = tok.ecLast ∧
      (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (scratch ≤ a ∧ a < scOut)) ∧
      (∀ a, tok.owned a → tok'.owned a) ∧
      (∀ a < scratch, tok'.tag a = tok.tag a) ∧
      (∀ a, tok.tag a ≠ 0 → tok'.tag a = tok.tag a) ∧
      SolverLevelCapsInv P V vCap eCap model tok' out.mem ∧
      SelectMetaTableAt out.mem (selectMlocOf B metaBase (solverLevelG tok' out.mem) pLast) ∧
      SelectHeapAt out.mem loc 4 heapSize ∧
      SelBlocksDataAt out.mem B P
        { D with
          F := fun j => if cur ≤ j ∧ j < cfg.P.d then (C.activeLSF j).F.F else D.F j
          E := fun j => if cur ≤ j ∧ j < cfg.P.d then (C.G j).E else D.E j
          len := fun j => if cur ≤ j ∧ j < cfg.P.d then C.chainLen model.chain.ℓ (j + 1) else D.len j
          coreE := fun j => if cur ≤ j ∧ j < cfg.P.d then (C.activeCore j).E else D.coreE j
          emb := fun j => if cur ≤ j ∧ j < cfg.P.d then C.activeEmb j else D.emb j } pLast ∧
      ZeroFrom out.mem scOut ∧
      (∀ a < scratch, ¬ (B.base ≤ a ∧ a < B.endAddr) →
        ¬ (∃ j, cur ≤ j ∧ j < cfg.P.d ∧ Rcore.foot (tok.coreHandle j) (tok.coreTok j) a) →
        out.mem a = mem a) ∧
      cost + Rrep.phi root tok' out.mem ≤
        selectRefreshInteriorLoopCost D.F model.chain Psc.readout cur L capExp B.slot +
          Rrep.phi root tok mem := by
  intro Rrep C
  have hInd : ∀ n cur scratch pos (tok : SolverToken cfg L Rcore) (D : SelBlocksData) (mem : ℕ → ℕ),
      cfg.P.d - cur = n → cur ≤ cfg.P.d →
      Rrep.rep root model tok mem →
      (∀ a, Rrep.foot root tok a → a < scratch) →
      (∀ a, sb ≤ a → a < B.endAddr → ¬ Rrep.foot root tok a) →
      B.endAddr ≤ scratch →
      SolverLevelCapsInv P V vCap eCap model tok mem →
      SelectMetaTableAt mem (selectMlocOf B metaBase (solverLevelG tok mem) pLast) →
      SelectHeapAt mem loc 4 heapSize →
      SelBlocksDataAt mem B P D pLast →
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
        SparseCoreReadoutFootAt fmt L depth cfg.T (initialGraph j) cfg.P.k
          (model.chain.lvlM j) model.chain.N₀ vCap eCap capExp Psc allocation Rcore p op) →
      (∀ j, cur ≤ j → j < cfg.P.d → ∀ vcF ecF,
        MeetsContract w p dgCopyProc (dgCopyRefillContract w vCap eCap vcF ecF (D.F j) (C.activeLSF j).F.F)) →
      (∀ j, cur ≤ j → j < cfg.P.d → ∀ eL : List ℕ,
        MeetsContract w p embCopyProc (selEmbCopyContract w eL (C.activeEmb j))) →
      ZeroFrom mem scratch →
      scratch + selectInitInteriorLoopSpace model.chain cur L capExp < 2 ^ w →
      ∃ scOut cost out tok',
        Runs w p ω (selectInitInteriorLoopBody loopProc fillIntProc)
          (startState [metaBase, cur, cfg.P.d, tok.handle + 18,
            solverLevelMetaAddr tok.table cfg.P.d, L, B.slot, scratch] mem pos)
          (.returned scOut) out cost ∧
        scratch ≤ scOut ∧ scOut ≤ scratch + selectInitInteriorLoopSpace model.chain cur L capExp ∧
        Rrep.rep root model tok' out.mem ∧
        tok'.table = tok.table ∧ tok'.handle = tok.handle ∧
        tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧
        tok'.rootECap = tok.rootECap ∧
        tok'.tree = tok.tree ∧ tok'.trees = tok.trees ∧ tok'.edgeRecords = tok.edgeRecords ∧
        tok'.termHandle = tok.termHandle ∧ tok'.termTok = tok.termTok ∧
        tok'.vcLast = tok.vcLast ∧ tok'.ecLast = tok.ecLast ∧
        (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (scratch ≤ a ∧ a < scOut)) ∧
        (∀ a, tok.owned a → tok'.owned a) ∧
        (∀ a < scratch, tok'.tag a = tok.tag a) ∧
        (∀ a, tok.tag a ≠ 0 → tok'.tag a = tok.tag a) ∧
        SolverLevelCapsInv P V vCap eCap model tok' out.mem ∧
        SelectMetaTableAt out.mem (selectMlocOf B metaBase (solverLevelG tok' out.mem) pLast) ∧
        SelectHeapAt out.mem loc 4 heapSize ∧
        SelBlocksDataAt out.mem B P
          { D with
            F := fun j => if cur ≤ j ∧ j < cfg.P.d then (C.activeLSF j).F.F else D.F j
            E := fun j => if cur ≤ j ∧ j < cfg.P.d then (C.G j).E else D.E j
            len := fun j => if cur ≤ j ∧ j < cfg.P.d then C.chainLen model.chain.ℓ (j + 1) else D.len j
            coreE := fun j => if cur ≤ j ∧ j < cfg.P.d then (C.activeCore j).E else D.coreE j
            emb := fun j => if cur ≤ j ∧ j < cfg.P.d then C.activeEmb j else D.emb j } pLast ∧
        ZeroFrom out.mem scOut ∧
        (∀ a < scratch, ¬ (B.base ≤ a ∧ a < B.endAddr) →
          ¬ (∃ j, cur ≤ j ∧ j < cfg.P.d ∧ Rcore.foot (tok.coreHandle j) (tok.coreTok j) a) →
          out.mem a = mem a) ∧
        cost + Rrep.phi root tok' out.mem ≤
          selectRefreshInteriorLoopCost D.F model.chain Psc.readout cur L capExp B.slot +
            Rrep.phi root tok mem := by
    intro n
    induction n with
    | zero =>
      intro cur scratch pos tok D mem hsub hcurLe hrep0 _ _ _ hcaps0 htab0 hHeap0 hblk0 _ _ _ _ _ _ _ _ _ hz0 hroom0
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
      let s0 := startState [metaBase, cur, cfg.P.d, tok.handle + 18,
        solverLevelMetaAddr tok.table cfg.P.d, L, B.slot, scratch] mem pos
      have hRun : Runs w p ω (selectInitInteriorLoopBody loopProc fillIntProc) s0 (.returned scratch) s0 6 := by
        unfold selectInitInteriorLoopBody
        refine runs_cond_iff.mpr ⟨0, 2, by simp [Expr.eval, BinOp.eval, s0, startState, hcurEq], ?_, by simp [Expr.size]⟩
        exact runs_ret_iff.mpr ⟨scratch, by simp [Expr.eval, s0, startState], rfl, rfl, rfl⟩
      refine ⟨scratch, 6, s0, tok, hRun, le_refl _, by omega, hrep0,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        fun _ ha => Or.inl ha, fun _ ha => ha, fun _ _ => rfl, fun _ _ => rfl, hcaps0, htab0, hHeap0,
        hDEq.symm ▸ hblk0, hz0, fun _ _ _ _ => rfl, ?_⟩
      simp only [s0, startState]; unfold selectRefreshInteriorLoopCost; omega
    | succ n ih =>
      intro cur scratch pos tok D mem hsub hcurLe hrep0 hFootSc0 hFootDisj0 hEndSc0 hcaps0 htab0
        hHeap0 hblk0 hScIn0 hBrLt0 hFV0 hFE0 hLenFit0 hEmbSlot0 hFootAt0 hDgCopy0 hEmbCopy0 hz0 hroom0
      have hcurLt : cur < cfg.P.d := by omega
      have hcurB : cur < B.d := by omega
      have hsbLeBase : sb ≤ B.base := by
        have := hreg.1; have := hreg.2.1; have := hreg.2.2.1; have := hreg.2.2.2.1
        have : loc.hb ≤ loc.endAddr := by rw [loc.endAddr_eq]; omega
        omega
      have hBaseLeEnd : B.base ≤ B.endAddr := by rw [B.endAddr_eq]; omega
      have hsbLtEnd : sb < B.endAddr := by
        have := hreg.1; have := hreg.2.1; have := hreg.2.2.1; have := hreg.2.2.2.1
        have : loc.hb < loc.endAddr := by rw [loc.endAddr_eq]; unfold selectHeapSize shHdrSize; omega
        omega
      have hMetaEnd : metaBase + selectLevelMetaSize B.d ≤ B.base := by
        have := hreg.2.2.2.1; omega
      have htags := hrep0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      obtain ⟨hOwn, _, _, _, hT4, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, t21⟩ := htags
      have hMC := (solverLevelCapsInv_iff_metaCaps.mp hcaps0).2.2.2.2.2 cur hcurLt
      set hnd := tok.coreHandle cur
      set br := model.chain.bran cur
      set prevLen := mem (solverLevelMetaAddr tok.table cfg.P.d + cur)
      have hCoreCur := hrep0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 cur hcurLt
      have hSpSplit : selectInitInteriorLoopSpace model.chain cur L capExp =
          selectFillInteriorLevelSpace (model.chain.G cur).m (C.activeLSF cur).F.F.m L
            (L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (model.chain.lvlM cur + model.chain.N₀ + 2) + 1)) +
          selectInitInteriorLoopSpace model.chain (cur + 1) L capExp := by
        unfold selectInitInteriorLoopSpace; rw [Finset.sum_eq_sum_Ico_succ_bot hcurLt]
      have hCostSplit : selectRefreshInteriorLoopCost D.F model.chain Psc.readout cur L capExp B.slot =
          (selectFillInteriorLevelCost Psc.readout (D.F cur).n (D.F cur).m (C.activeLSF cur).F.F.n
            (C.activeLSF cur).F.F.m (model.chain.G cur).m L
            (L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (model.chain.lvlM cur + model.chain.N₀ + 2) + 1))
            B.slot + 60) +
          selectRefreshInteriorLoopCost (Function.update D.F cur (C.activeLSF cur).F.F) model.chain
            Psc.readout (cur + 1) L capExp B.slot := by
        dsimp only [C, selectRefreshInteriorLoopCost]
        rw [Finset.sum_eq_sum_Ico_succ_bot hcurLt]
        have hcongr : (Finset.Ico (cur + 1) cfg.P.d).sum (fun j =>
            let LwMax := L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (model.chain.lvlM j + model.chain.N₀ + 2) + 1)
            selectFillInteriorLevelCost Psc.readout (D.F j).n (D.F j).m
              (model.chain.toTreeChain.activeLSF j).F.F.n (model.chain.toTreeChain.activeLSF j).F.F.m
              (model.chain.G j).m L LwMax B.slot + 60) =
            (Finset.Ico (cur + 1) cfg.P.d).sum (fun j =>
            let LwMax := L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (model.chain.lvlM j + model.chain.N₀ + 2) + 1)
            selectFillInteriorLevelCost Psc.readout (Function.update D.F cur (model.chain.toTreeChain.activeLSF cur).F.F j).n
              (Function.update D.F cur (model.chain.toTreeChain.activeLSF cur).F.F j).m
              (model.chain.toTreeChain.activeLSF j).F.F.n (model.chain.toTreeChain.activeLSF j).F.F.m
              (model.chain.G j).m L LwMax B.slot + 60) :=
          Finset.sum_congr rfl fun j hj => by
            have hne : j ≠ cur := by have := (Finset.mem_Ico.mp hj).1; omega
            simp [hne]
        rw [hcongr]; dsimp only; omega
      have hHndW : hnd < 2 ^ w := by have := hFootSc0 hnd (Or.inl (hcaps0.1.2.1 cur hcurLt)); omega
      have hGInFoot : ∀ a, solverLevelG tok mem cur ≤ a →
          a < solverLevelG tok mem cur + dynGraphSize vCap eCap → Rrep.foot root tok a := fun a h1 h2 => by
        have htg := hMC.2.2.2.2 a h1 h2
        exact Or.inl (hOwn a (by split_ifs at htg <;> omega))
      have hGEndSc : solverLevelG tok mem cur + dynGraphSize vCap eCap ≤ scratch := by
        have hpos : 0 < dynGraphSize vCap eCap := by unfold dynGraphSize; omega
        have := hFootSc0 (solverLevelG tok mem cur + dynGraphSize vCap eCap - 1)
          (hGInFoot _ (by omega) (by omega))
        omega
      have hGDisjReg : solverLevelG tok mem cur + dynGraphSize vCap eCap ≤ sb ∨
          B.endAddr ≤ solverLevelG tok mem cur :=
        interval_disj_region (by unfold dynGraphSize; omega) hsbLtEnd
          (fun x h1 h2 hx => hFootDisj0 x h1 h2 (hGInFoot x hx.1 hx.2))
      have hPrevInFoot : ∀ a, prevLen ≤ a → a < prevLen + eCap * L → Rrep.foot root tok a := fun a h1 h2 =>
        Or.inl (hOwn a (by have := hMC.2.2.2.1 a h1 h2; omega))
      have hPrevSc : prevLen + eCap * L ≤ scratch := by
        by_cases heL : eCap * L = 0
        · have := hFootSc0 prevLen (Or.inl hMC.2.2.1); omega
        · have := hFootSc0 (prevLen + eCap * L - 1) (hPrevInFoot _ (by omega) (by omega)); omega
      have hPrevDisjReg : prevLen + eCap * L ≤ sb ∨ B.endAddr ≤ prevLen := by
        by_cases heL : eCap * L = 0
        · by_cases hcmp : prevLen ≤ sb
          · left; omega
          · right
            have hnot := hFootDisj0 prevLen (by omega)
            by_contra hlt; exact hnot (by omega) (Or.inl hMC.2.2.1)
        · exact interval_disj_region (Nat.pos_of_ne_zero heL) hsbLtEnd
            (fun x h1 h2 hx => hFootDisj0 x h1 h2 (hPrevInFoot x hx.1 hx.2))
      have hCoreDisj : ∀ a, Rcore.foot hnd (tok.coreTok cur) a →
          a < scratch ∧ (a < B.base ∨ B.endAddr ≤ a) := fun a ha =>
        ⟨hFootSc0 a (Or.inr (Or.inr ⟨cur, hcurLt, ha⟩)), by
          by_contra h; push Not at h
          exact hFootDisj0 a (by omega) h.2 (Or.inr (Or.inr ⟨cur, hcurLt, ha⟩))⟩
      have hDisjG : ∀ a, solverLevelG tok mem cur ≤ a →
          a < solverLevelG tok mem cur + dynGraphSize B.vCap B.eCap →
          ¬ Rcore.foot hnd (tok.coreTok cur) a := fun a ha1 ha2 hcf => by
        rw [hBv, hBe] at ha2
        have h1 := hMC.2.2.2.2 a ha1 ha2; have h2 := t21 cur hcurLt a hcf
        split_ifs at h1 <;> omega
      have hDisjPrev : ∀ a, prevLen ≤ a → a < prevLen + B.eCap * B.Lk →
          ¬ Rcore.foot hnd (tok.coreTok cur) a := fun a ha1 ha2 hcf => by
        rw [hBe, hBLk] at ha2
        have h1 := hMC.2.2.2.1 a ha1 ha2; have h2 := t21 cur hcurLt a hcf; omega
      have hFPos : B.base ≤ B.fPtr cur := by unfold SelectBlocksLoc.fPtr; omega
      have hLenPos : B.base ≤ B.lenPtr cur := by unfold SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr SelectBlocksLoc.fPtr; omega
      have hBlkEnd : B.fPtr cur + B.levelSize ≤ B.endAddr := by
        have h1 := B.blk_le_last hcurB.le
        have h2 : B.lastGPtr ≤ B.endAddr := by unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr; omega
        omega
      have hEmbLeEnd : B.embPtr cur ≤ B.endAddr := by
        have := B.blkEnd_eq cur; unfold SelectBlocksLoc.embPtr SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr at *; omega
      have hPhiLeEnd : B.phiPtr cur ≤ B.endAddr := by
        have := B.blkEnd_eq cur; unfold SelectBlocksLoc.phiPtr at *; omega
      have hActLSF : C.activeLSF cur = cfg.T.lsfs (model.chain.scState cur) br := by
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
          (fmt := fmt) (tool := cfg.T) (initialGraph := initialGraph cur)
          (Psc := Psc) (allocation := allocation) (R := Rcore) (p := p) (op := op) (ω := ω)
          (B := B) (metaBase := metaBase) (solverG := solverLevelG tok mem) (D := D)
          (a := chainLevelOrdAbs model.chain cur) (x := tok.coreTok cur)
          (prevVal := C.chainLen model.chain.ℓ cur) (mem := mem)
          hfmt4 hlocalCore hw16 (hBLk ▸ hLkW) hSlotW hcurB (hBrLt0 cur le_rfl hcurLt) hkW hHndW
          htab0 (hfmtP.symm ▸ hblk0) hMetaEnd hEndSc0
          (by rw [hBv, hBe]; exact hMC.1)
          (by rw [hBv, hBe]; exact ⟨hGEndSc, hGDisjReg.imp (by omega) id⟩)
          hCoreCur.2.2 (hScIn0 cur le_rfl hcurLt) hCoreDisj
          hDisjG hDisjPrev (by rw [hBe, hBLk]; exact hPrevSc)
          (by rw [hBe, hBLk]; rcases hPrevDisjReg with h | h <;> [left; right] <;> omega)
          (by rw [hBe, hBLk]; rcases hPrevDisjReg with h | h <;> [left; right] <;> omega)
          (by rw [hfmtP, hBLk]; exact hMC.2.1)
          (by dsimp only [chainLevelOrdAbs]; rw [hBv, ← hActLSF]; exact hFV0 cur le_rfl hcurLt)
          (by dsimp only [chainLevelOrdAbs]; rw [hBe, ← hActLSF]; exact hFE0 cur le_rfl hcurLt)
          (fun e he => by
            dsimp only [chainLevelOrdAbs] at he ⊢
            obtain ⟨q, hqF, hqEq⟩ := hLenFit0 cur le_rfl hcurLt e he
            exact ⟨q, hBLk.symm ▸ hqF, by rw [hfmtP, hqEq, hChainLenSucc]⟩)
          (fun e he => by
            dsimp only [chainLevelOrdAbs] at he ⊢
            rw [← hActEmb]; exact hEmbSlot0 cur le_rfl hcurLt e (hActCore.symm ▸ he))
          (by rw [hBLk, hBv, hBe]; exact hFootAt0 cur le_rfl hcurLt)
          (fun vcF ecF => by
            dsimp only [chainLevelOrdAbs]; rw [hBv, hBe, ← hActLSF]; exact hDgCopy0 cur le_rfl hcurLt vcF ecF)
          (fun eL => by rw [hfmtP, hBe]; exact hCoreLen eL) hFilter
          (fun eL => by dsimp only [chainLevelOrdAbs]; rw [← hActEmb]; exact hEmbCopy0 cur le_rfl hcurLt eL)
          hz0 (by dsimp only [chainLevelOrdAbs]; rw [hBLk, ← hActLSF]; omega)
      dsimp only [chainLevelOrdAbs] at hsc1Hi hcFill
      have hfr1OffCore : ∀ a < scratch, ¬ Rcore.foot hnd (tok.coreTok cur) a →
          (a < sb ∨ B.endAddr ≤ a) → st1.mem a = mem a := fun a ha hnc hoff =>
        hfr1 a ha hnc
          (fun hf => by have := reg_in_blocks_ref hcurB.le (Or.inl hf); omega)
          (fun hl => by have := reg_in_blocks_ref hcurB.le (Or.inr (Or.inl hl)); omega)
          (fun he => by have := reg_in_blocks_ref hcurB.le (Or.inr (Or.inr he)); omega)
      have hfr1Foot : ∀ a < scratch, ¬ Rcore.foot hnd (tok.coreTok cur) a →
          Rrep.foot root tok a → st1.mem a = mem a := fun a ha hnc hf =>
        hfr1OffCore a ha hnc (by
          by_contra h; obtain ⟨h1, h2⟩ := not_or.mp h
          exact hFootDisj0 a (Nat.le_of_not_lt h1) (Nat.lt_of_not_le h2) hf)
      let tok1 : SolverToken cfg L Rcore :=
        { tok with
          coreTok := Function.update tok.coreTok cur y1
          owned := fun a => tok.owned a ∨ (scratch ≤ a ∧ a < sc1)
          tag := fun a => if scratch ≤ a ∧ a < sc1 then 21 + cur else tok.tag a }
      let memM : ℕ → ℕ := fun a => if sb ≤ a ∧ a < B.endAddr then mem a else st1.mem a
      have hfrM : ∀ a < scratch, ¬ Rcore.foot hnd (tok.coreTok cur) a → memM a = mem a := fun a ha hnc => by
        dsimp only [memM]; split_ifs with hrg
        · rfl
        · exact hfr1OffCore a ha hnc (by by_contra h; obtain ⟨h1, h2⟩ := not_or.mp h; exact hrg ⟨Nat.le_of_not_lt h1, Nat.lt_of_not_le h2⟩)
      have hY1DisjReg : ∀ a, Rcore.foot hnd y1 a → ¬ (sb ≤ a ∧ a < B.endAddr) := fun a ha hrg => by
        rcases hftY1 a ha with hold | hnew
        · exact hFootDisj0 a hrg.1 hrg.2 (Or.inr (Or.inr ⟨cur, hcurLt, hold⟩))
        · omega
      have hrepY1M : Rcore.rep hnd (chainLevelOrdAbs model.chain cur) y1 memM :=
        (hlocalCore hnd (chainLevelOrdAbs model.chain cur) y1 st1.mem memM fun a ha => by
          dsimp only [memM]; rw [ite_eq_right (hY1DisjReg a ha)]).1 hrepY1
      obtain ⟨hrep1M, hfoot1, hphi1M⟩ :=
        solverStateRep_update_coreTok hlocalCore hcurLt hrep0 hFootSc0 hfrM hrepY1M hftY1
      have hFoot1Disj : ∀ a, sb ≤ a → a < B.endAddr → ¬ Rrep.foot root tok1 a := fun a h1 h2 hf1 => by
        rcases hfoot1 a hf1 with hf0 | hnew
        · exact hFootDisj0 a h1 h2 hf0
        · omega
      have hRrepLoc := solverStateRep_local cfg L P m V psi k epsExp drainUnit hlocalCore
      have hrep1 : Rrep.rep root model tok1 st1.mem :=
        (hRrepLoc root model tok1 memM st1.mem fun a ha => by
          dsimp only [memM]; rw [ite_eq_right fun hrg => hFoot1Disj a hrg.1 hrg.2 ha]).1 hrep1M
      have hphi1Eq : Rrep.phi root tok1 st1.mem = Rrep.phi root tok1 memM :=
        ((hRrepLoc root model tok1 memM st1.mem fun a ha => by
          dsimp only [memM]; rw [ite_eq_right fun hrg => hFoot1Disj a hrg.1 hrg.2 ha]).2).symm
      have hphiY1Eq : Rcore.phi hnd y1 memM = Rcore.phi hnd y1 st1.mem :=
        ((hlocalCore hnd (chainLevelOrdAbs model.chain cur) y1 st1.mem memM fun a ha => by
          dsimp only [memM]; rw [ite_eq_right (hY1DisjReg a ha)]).2).symm
      have hcaps1 : SolverLevelCapsInv P V vCap eCap model tok1 st1.mem := by
        refine hcaps0.preserve rfl (fun j hj => Or.inl (hcaps0.1.2.1 j hj)) (fun a ha => ?_)
          (fun j hj => Or.inl (SolverLevelMetaAt.atCaps hcaps0.1 hcaps0.2 j hj).2.2.1)
          rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl
        have hne0 : tok.tag a ≠ 0 := by rcases ha with h | h | h | h <;> omega
        have hlt := hFootSc0 a (Or.inl (hOwn a hne0))
        have hnc : ¬ Rcore.foot hnd (tok.coreTok cur) a := fun hc => by
          have := t21 cur hcurLt a hc; rcases ha with h | h | h | h <;> omega
        exact ⟨by dsimp only [tok1]; rw [ite_eq_right (by omega)], hfr1Foot a hlt hnc (Or.inl (hOwn a hne0))⟩
      have hMlocEq1 : selectMlocOf B metaBase (solverLevelG tok1 st1.mem) pLast =
          selectMlocOf B metaBase (solverLevelG tok mem) pLast :=
        selectMlocOf_congr_ref fun j hj => by
          rw [hBd] at hj
          have htag := hcaps0.1.2.2.2.2.1 (cfg.P.d + j) (by omega)
          rw [← Nat.add_assoc] at htag
          have hlt := hFootSc0 _ (Or.inl (hOwn (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) (by omega)))
          have hnc : ¬ Rcore.foot hnd (tok.coreTok cur) (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) := fun hc => by
            have := t21 cur hcurLt _ hc; omega
          exact hfr1Foot _ hlt hnc (Or.inl (hOwn (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) (by omega)))
      have hLocLeBase : loc.hb ≤ loc.endAddr := by rw [loc.endAddr_eq]; omega
      have htab1 : SelectMetaTableAt st1.mem (selectMlocOf B metaBase (solverLevelG tok1 st1.mem) pLast) := by
        rw [hMlocEq1]
        have := hreg.1; have := hreg.2.1; have := hreg.2.2.1; have := hreg.2.2.2.1
        exact htab0.of_agree fun a ha1 ha2 => hfr1 a (by simp only [selectMlocOf] at ha2; omega)
          (fun hc => hFootDisj0 a (by simp only [selectMlocOf] at ha1; omega) (by simp only [selectMlocOf] at ha2; omega)
            (Or.inr (Or.inr ⟨cur, hcurLt, hc⟩)))
          (fun hf => by have := reg_in_blocks_ref hcurB.le (Or.inl hf); simp only [selectMlocOf] at ha2; omega)
          (fun hl => by have := reg_in_blocks_ref hcurB.le (Or.inr (Or.inl hl)); simp only [selectMlocOf] at ha2; omega)
          (fun he => by have := reg_in_blocks_ref hcurB.le (Or.inr (Or.inr he)); simp only [selectMlocOf] at ha2; omega)
      have hHeap1 : SelectHeapAt st1.mem loc 4 heapSize :=
        hHeap0.of_agree fun a ha1 ha2 => by
          have := hreg.1; have := hreg.2.1; have := hreg.2.2.1; have := hreg.2.2.2.1
          exact hfr1 a (by omega)
            (fun hc => hFootDisj0 a (by omega) (by omega) (Or.inr (Or.inr ⟨cur, hcurLt, hc⟩)))
            (fun hf => by have := reg_in_blocks_ref hcurB.le (Or.inl hf); omega)
            (fun hl => by have := reg_in_blocks_ref hcurB.le (Or.inr (Or.inl hl)); omega)
            (fun he => by have := reg_in_blocks_ref hcurB.le (Or.inr (Or.inr he)); omega)
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
      rw [hBLk, ← hActLSF] at hsc1Hi
      -- Recursive call on `cur + 1`
      obtain ⟨scOut, cRec, out, tok', hrRec, hscOutLo, hscOutHi, hrepOut, htabOutEq, hhndOutEq,
          hlevOutEq, hintOutEq, hrecOutEq, htreeOutEq, htreesOutEq, hedgOutEq,
          hthOutEq, httOutEq, hvcOutEq, hecOutEq,
          hftOut, hOwnOut, hTagLtOut, hTagOut, hcapsOut, htabOut, hHeapOut, hblkOut, hzOut, hfrOut, hcRec⟩ :=
        ih (cur + 1) sc1 st1.pos tok1 D1 st1.mem (by omega) (by omega) hrep1
          (fun a ha => by rcases hfoot1 a ha with h0 | hnew; exact lt_of_lt_of_le (hFootSc0 a h0) hsc1Lo; exact hnew.2)
          hFoot1Disj (by omega) hcaps1 htab1 hHeap1 hblk1'
          (fun j hj1 hj2 => hScIn0 j (by omega) hj2)
          (fun j hj1 hj2 => hBrLt0 j (by omega) hj2)
          (fun j hj1 hj2 => hFV0 j (by omega) hj2)
          (fun j hj1 hj2 => hFE0 j (by omega) hj2)
          (fun j hj1 hj2 => hLenFit0 j (by omega) hj2)
          (fun j hj1 hj2 => hEmbSlot0 j (by omega) hj2)
          (fun j hj1 hj2 => hFootAt0 j (by omega) hj2)
          (fun j hj1 hj2 => by simp [D1, show j ≠ cur by omega]; exact hDgCopy0 j (by omega) hj2)
          (fun j hj1 hj2 => hEmbCopy0 j (by omega) hj2)
          hz1 (by omega)
      -- Stitch current step + recursive call into `selectInitInteriorLoopBody`
      let s0 := startState [metaBase, cur, cfg.P.d, tok.handle + 18,
        solverLevelMetaAddr tok.table cfg.P.d, L, B.slot, scratch] mem pos
      have hsc1W : sc1 < 2 ^ w := by omega
      have hscOutW : scOut < 2 ^ w := by omega
      have hHndCurLt : tok.handle + 18 + cur < scratch :=
        hFootSc0 _ (Or.inl (hOwn _ (by rw [hT4 cur (by omega)]; decide)))
      have hBrCurLt : tok.handle + 18 + (cfg.P.d + 1) + cur < scratch := by
        have h := hT4 ((cfg.P.d + 1) + cur) (by omega)
        rw [← Nat.add_assoc] at h
        exact hFootSc0 _ (Or.inl (hOwn _ (by rw [h]; decide)))
      have hMetaCurLt : solverLevelMetaAddr tok.table cfg.P.d + cur < scratch :=
        hFootSc0 _ (Or.inl (hOwn _ (by have := hcaps0.1.2.2.2.2.1 cur (by omega); omega)))
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
        exact ⟨o, final, _, runs_cond_iff.mpr ⟨1, cB,
          by simp [Expr.eval, BinOp.eval, s0, startState, hcurLt, show 1 < 2 ^ w by omega],
          by simpa using hrB, rfl⟩, hoEq, hmEq, by simp [Expr.size]; omega⟩
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
      refine ⟨scOut, cStep, final, tok', hrStep, by omega, by omega,
        hmemEq ▸ hrepOut, htabOutEq, hhndOutEq, hlevOutEq, hintOutEq, hrecOutEq, htreeOutEq,
        htreesOutEq, hedgOutEq, hthOutEq, httOutEq, hvcOutEq, hecOutEq,
        fun a ha => ?_, fun a ha => hOwnOut a (Or.inl ha),
        fun a ha => (hTagLtOut a (by omega)).trans (by dsimp only [tok1]; rw [ite_eq_right (by omega)]),
        fun a hne => (hTagOut a (by dsimp only [tok1]; rw [ite_eq_right (by have := hFootSc0 a (Or.inl (hOwn a hne)); omega)]; exact hne)).trans
          (by dsimp only [tok1]; rw [ite_eq_right (by have := hFootSc0 a (Or.inl (hOwn a hne)); omega)]),
        hmemEq ▸ hcapsOut, hmemEq ▸ htabOut, hmemEq ▸ hHeapOut,
        hmemEq ▸ (hDTargetEq ▸ hblkOut), hmemEq ▸ hzOut, fun a ha hnotReg hnc => ?_, ?_⟩
      · rcases hftOut a ha with h1 | hnew
        · rcases hfoot1 a h1 with h0 | hnew1
          · exact Or.inl h0
          · exact Or.inr ⟨hnew1.1, by omega⟩
        · exact Or.inr ⟨by omega, hnew.2⟩
      · rw [hmemEq]
        have hncRec : ¬ (∃ j, cur + 1 ≤ j ∧ j < cfg.P.d ∧ Rcore.foot (tok1.coreHandle j) (tok1.coreTok j) a) := by
          rintro ⟨j, hj1, hj2, hc⟩
          dsimp only [tok1] at hc; rw [Function.update_of_ne (by omega)] at hc
          exact hnc ⟨j, by omega, hj2, hc⟩
        have hncCur : ¬ Rcore.foot hnd (tok.coreTok cur) a := fun hc => hnc ⟨cur, le_rfl, hcurLt, hc⟩
        have hoff : a < B.base ∨ B.endAddr ≤ a := by
          by_contra h; push Not at h; exact hnotReg h
        have hfr1OffBlk : st1.mem a = mem a :=
          hfr1 a ha hncCur
            (fun hf => by have := reg_in_blocks_ref hcurB.le (Or.inl hf); omega)
            (fun hl => by have := reg_in_blocks_ref hcurB.le (Or.inr (Or.inl hl)); omega)
            (fun he => by have := reg_in_blocks_ref hcurB.le (Or.inr (Or.inr he)); omega)
        exact (hfrOut a (by omega) hnotReg hncRec).trans hfr1OffBlk
      · rw [hmemEq]
        have hphi1Sum : Rrep.phi root tok1 st1.mem + Rcore.phi hnd (tok.coreTok cur) mem =
            Rrep.phi root tok mem + Rcore.phi hnd y1 st1.mem := by
          rw [hphi1Eq, ← hphiY1Eq]; exact hphi1M
        rw [hBLk, ← hActLSF] at hcFill
        dsimp only [C, D1, Rrep, hnd, memM] at hcFill hcRec hCostSplit hphi1Sum ⊢
        omega
  exact hInd (cfg.P.d - cur) cur scratch pos tok D mem rfl hcurLe hrep hFootSc hFootDisj hEndSc
    hcaps htab hHeap hblk hScIn hBrLt hFV hFE hLenFit hEmbSlot hFootAt hDgCopy hEmbCopy hz hroom

end MinCostFlow.MinRatio
