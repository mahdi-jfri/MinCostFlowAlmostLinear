module

public import MinCostFlow.MinRatio.WireShiftDeepSelectLoop
public import MinCostFlow.MinRatio.WireSelectRebuildSuffix
public import MinCostFlow.MinRatio.WireReembPotChain
import WordRAM.Tactic

/-!
# Terminal `G_d` readout and suffix-refresh finalization for deep shift (`WireShiftDeepSelectFinalize`)

Provides the remaining two building blocks for refreshing an existing in-place select region
`[sb, B.endAddr)` after a deep shift at level `i < d`:

* `op3_gd_disj_runs`: runs `op 3` on core `d - 1` (`0 < d`), returning `srcGd` disjoint from
  `[B.base, B.endAddr)` while preserving `solverStateRep`, `SolverLevelCapsInv`,
  `SelectMetaTableAt`, `SelectHeapAt`, and `SelBlocksDataAt`.
* `selectRefreshFinalizeBody`: fixed 3-line deterministic procedure running `selectPhiLoop` from
  `cur` followed by `selectRebuildSuffix` from `cur`.
* `selectDeepFinalize_runs`: verifies `selectRefreshFinalizeBody` using
  `selectRebuildSuffix_meetsContract_noRoom` (requiring no total-capacity slack hypothesis) and
  `selectRebuildShift_preserves_matchesChain`, restoring `SelectRegionAt` (and hence
  `SolverSelectInv`) with `sg'.loc = loc`, `sg'.owned = [sb, B.endAddr)`, and
  `sg'.reembPot = chainReembPot pot model'.chain`, with two-sided frame off `[sb, B.endAddr)`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine Num DynSpanner.Program SparseCore.Program

/-- Finalize a suffix refresh from level `cur`: fill level potentials `φ_{cur} .. φ_d` via
`selectPhiLoop` and rebuild select-heap candidates for levels `cur .. d` via `selectRebuildSuffix`.
Arguments: `[sb, metaBase, cur, d, Lk, scratch]` (`reg 0..5`). Returns the new scratch pointer. -/
def selectRefreshFinalizeBody (phiLoopProc rebuildSuffixProc : ℕ) : Stmt :=
  .call 6 phiLoopProc [.reg 1, .reg 2, .reg 3, .reg 4, .reg 5] ;;
  .call 7 rebuildSuffixProc [.reg 0, .reg 1, .reg 2, .reg 3, .reg 6] ;;
  .ret (.reg 7)

theorem selectRefreshFinalizeBody_noRand (phiLoopProc rebuildSuffixProc : ℕ) :
    (selectRefreshFinalizeBody phiLoopProc rebuildSuffixProc).NoRand := by
  simp [selectRefreshFinalizeBody, Stmt.NoRand]

/-- Scratch space for `selectRefreshFinalizeBody` refreshing levels `cur .. C.d`. -/
noncomputable def selectRefreshFinalizeSpace (mem : ℕ → ℕ) (loc : SelectHeapLoc)
    (C : TreeChain) (cur Lk evalSpace : ℕ) : ℕ :=
  selectPhiLoopSpace C cur Lk + selectRebuildSuffixSpace mem loc C cur evalSpace

/-- Step cost for `selectRefreshFinalizeBody` refreshing levels `cur .. C.d`. -/
noncomputable def selectRefreshFinalizeCost (mem : ℕ → ℕ) (loc : SelectHeapLoc)
    (C : TreeChain) (cur Lk evalCost : ℕ) : ℕ :=
  selectPhiLoopCost C cur Lk + selectRebuildSuffixCost mem loc C cur evalCost + 40

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine Num DynSpanner.Program SparseCore.Program

private lemma selectMlocOf_congr_fin {B : SelectBlocksLoc} {metaBase pLast : ℕ} {g₁ g₂ : ℕ → ℕ}
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

/-! ## 1. Direct `G_d` readout via `op 3` disjoint from `[B.base, B.endAddr)` -/

set_option maxHeartbeats 800000 in
/-- Runs `op 3` on core `d - 1` (`0 < d`), producing `srcGd = st1.mem scratch` with
`DynGraphAt st1.mem srcGd vCap eCap (model.chain.G d)` disjoint from `[B.base, B.endAddr)`,
using at most `1` scratch word and `Psc.readout` cost while preserving `solverStateRep`,
`SolverLevelCapsInv`, `SelectMetaTableAt`, `SelectHeapAt`, and `SelBlocksDataAt`. -/
theorem op3_gd_disj_runs
    {w L P m V psi k epsExp drainUnit depth capExp vCap eCap sb metaBase pLast heapSize scratch pos : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {G₀ initialGraph : MGraph}
    {σ σ_mwu γ_ℓ γ_c : ℝ} {Psc : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {op : ℕ → ℕ} {ω : ℕ → Bool}
    {root : ℕ} {model : Alg2State cfg} {tok : SolverToken cfg L Rcore}
    {loc : SelectHeapLoc} {B : SelectBlocksLoc} {D : SelBlocksData} {mem : ℕ → ℕ}
    (hlocalCore : Rcore.Local) (hkW : cfg.P.k < 2 ^ w) (hdPos : 0 < cfg.P.d)
    (hreg : SelectRegion sb loc B metaBase)
    (hBd : B.d = cfg.P.d) (hBv : B.vCap = vCap) (hBe : B.eCap = eCap)
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hFootSc : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a → a < scratch)
    (hFootDisj : ∀ a, sb ≤ a → a < B.endAddr →
      ¬ (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a)
    (hEndSc : B.endAddr ≤ scratch)
    (hcaps : SolverLevelCapsInv P V vCap eCap model tok mem)
    (hmod : SelectModelInv model G₀ σ σ_mwu γ_ℓ γ_c)
    (htab : SelectMetaTableAt mem (selectMlocOf B metaBase (solverLevelG tok mem) pLast))
    (hHeap : SelectHeapAt mem loc 4 heapSize)
    (hblk : SelBlocksDataAt mem B P D pLast)
    (hFootAt : SparseCoreReadoutFootAt fmt L depth cfg.T initialGraph cfg.P.k
      (model.chain.lvlM (cfg.P.d - 1)) model.chain.N₀ vCap eCap capExp Psc allocation Rcore p op)
    (hz : ZeroFrom mem scratch)
    (hroom : scratch + 1 < 2 ^ w) :
    let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
    let j := cfg.P.d - 1
    ∃ b3 o3 st1 c3 tok1,
      p.procs[op 3]? = some b3 ∧
      Runs w p ω b3 (startState [tok.coreHandle j, model.chain.bran j, scratch] mem pos) o3 st1 c3 ∧
      scratch ≤ o3.value ∧ o3.value ≤ scratch + 1 ∧
      Rrep.rep root model tok1 st1.mem ∧
      tok1.table = tok.table ∧ tok1.handle = tok.handle ∧
      tok1.levelsEnd = tok.levelsEnd ∧ tok1.intCap = tok.intCap ∧
      tok1.rootECap = tok.rootECap ∧
      tok1.tree = tok.tree ∧ tok1.trees = tok.trees ∧ tok1.edgeRecords = tok.edgeRecords ∧
      tok1.termHandle = tok.termHandle ∧ tok1.termTok = tok.termTok ∧
      tok1.vcLast = tok.vcLast ∧ tok1.ecLast = tok.ecLast ∧
      SolverLevelCapsInv P V vCap eCap model tok1 st1.mem ∧
      SelectMetaTableAt st1.mem (selectMlocOf B metaBase (solverLevelG tok1 st1.mem) pLast) ∧
      SelectHeapAt st1.mem loc 4 heapSize ∧
      SelBlocksDataAt st1.mem B P D pLast ∧
      DynGraphAt st1.mem (st1.mem scratch) vCap eCap (model.chain.G cfg.P.d) ∧
      st1.mem scratch + dynGraphSize vCap eCap ≤ o3.value ∧
      (st1.mem scratch + dynGraphSize vCap eCap ≤ B.base ∨ B.endAddr ≤ st1.mem scratch) ∧
      (∀ a < scratch, ¬ Rcore.foot (tok.coreHandle j) (tok.coreTok j) a → st1.mem a = mem a) ∧
      (∀ a, Rrep.foot root tok1 a → Rrep.foot root tok a ∨ (scratch ≤ a ∧ a < o3.value)) ∧
      (∀ a, tok.owned a → tok1.owned a) ∧
      (∀ a < scratch, tok1.tag a = tok.tag a) ∧
      (∀ a, tok.tag a ≠ 0 → tok1.tag a = tok.tag a) ∧
      ZeroFrom st1.mem o3.value ∧
      c3 + Rrep.phi root tok1 st1.mem ≤ Psc.readout + Rrep.phi root tok mem := by
  intro Rrep j
  have hjLt : j < cfg.P.d := by dsimp only [j]; omega
  have hjSucc : j + 1 = cfg.P.d := by dsimp only [j]; omega
  have hGdEq : cfg.T.S (model.chain.scState j) (model.chain.bran j) = model.chain.G cfg.P.d := by
    obtain ⟨_, _, _, hGeq⟩ := hmod.1.2.2.2.2.1 j hjLt
    change model.chain.G (j + 1) = cfg.T.S (model.chain.scState j) (model.chain.bran j) at hGeq
    rw [hjSucc] at hGeq; exact hGeq.symm
  have hsbLeBase : sb ≤ B.base := by
    have := hreg.1; have := hreg.2.1; have := hreg.2.2.1; have := hreg.2.2.2.1
    have : loc.hb ≤ loc.endAddr := by rw [loc.endAddr_eq]; omega
    omega
  have hsbLtEnd : sb < B.endAddr := by
    have := hreg.1; have := hreg.2.1; have := hreg.2.2.1; have := hreg.2.2.2.1
    have : loc.hb < loc.endAddr := by rw [loc.endAddr_eq]; unfold selectHeapSize shHdrSize; omega
    have : B.base ≤ B.endAddr := by rw [B.endAddr_eq]; omega
    omega
  have hrep0 := hrep
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hCores0, _, _, _, _, htags0⟩ := hrep
  obtain ⟨hOwn0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hCoreTags⟩ := htags0
  have hCoreRep0 := (hCores0 j hjLt).2.2
  have hHndLt : tok.coreHandle j < scratch := hFootSc _ (Or.inl (hcaps.1.2.1 j hjLt))
  have hBrLtJ : model.chain.bran j < cfg.P.k := hmod.2.2.1 j hjLt
  have hScInJ := hmod.2.2.2.1 j hjLt
  have hCoreFootLt : ∀ a, Rcore.foot (tok.coreHandle j) (tok.coreTok j) a → a < scratch :=
    fun a ha => hFootSc a (Or.inr (Or.inr ⟨j, hjLt, ha⟩))
  obtain ⟨b3, hb3, o3, st1, c3, y1, hr3, hrep1Core, hpost3, hresp3, hcost3⟩ :=
    hFootAt.op3_runs (tok.coreHandle j) (chainLevelOrdAbs model.chain j)
      (tok.coreTok j) [tok.coreHandle j, model.chain.bran j, scratch] mem pos ω
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro v (rfl|rfl|rfl) <;> omega)
      rfl hCoreRep0 ⟨hScInJ, tok.coreHandle j, model.chain.bran j, scratch, rfl, hBrLtJ⟩
      hCoreFootLt hz (by change scratch + 1 < 2 ^ w; omega)
  obtain ⟨gVC, gEC, hDG1Raw, hvcEq, hecEq, hGPtrEnd1, hGPtrFoot1⟩ := hpost3
  simp only [heapArg, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.getLastD_cons, List.getLastD_nil]
    at hDG1Raw hGPtrEnd1 hGPtrFoot1 hresp3 hcost3
  rw [hvcEq, hecEq] at hDG1Raw hGPtrEnd1 hGPtrFoot1
  have hDG1 : DynGraphAt st1.mem (st1.mem scratch) vCap eCap (model.chain.G cfg.P.d) := hGdEq ▸ hDG1Raw
  obtain ⟨hcur1Lo, hcur1Hi, hz1, hFr1Out, hFoot1⟩ := hresp3
  change scratch ≤ o3.value at hcur1Lo
  change o3.value ≤ scratch + 1 at hcur1Hi
  change st1.mem scratch + dynGraphSize vCap eCap ≤ scratch at hGPtrEnd1
  let tok1 : SolverToken cfg L Rcore :=
    { tok with
      coreTok := Function.update tok.coreTok j y1
      owned := fun a => tok.owned a ∨ (scratch ≤ a ∧ a < o3.value)
      tag := fun a => if scratch ≤ a ∧ a < o3.value then 21 + j else tok.tag a }
  obtain ⟨hrep1, hft1, hphi1⟩ :=
    solverStateRep_update_coreTok hlocalCore hjLt hrep0 hFootSc hFr1Out hrep1Core hFoot1
  have htag1 : ∀ a, tok.tag a ≠ 0 → tok1.tag a = tok.tag a := fun a hne => by
    dsimp only [tok1]; exact ite_eq_right (by have := hFootSc a (Or.inl (hOwn0 a hne)); omega)
  have hcaps1 : SolverLevelCapsInv P V vCap eCap model tok1 st1.mem :=
    hcaps.preserve rfl (fun i hi => Or.inl (hcaps.1.2.1 i hi))
      (fun a ha => by
        have hne : tok.tag a ≠ 0 := by rcases ha with h | h | h | h <;> omega
        have hnc : ¬ Rcore.foot (tok.coreHandle j) (tok.coreTok j) a := fun hc => by
          have := hCoreTags j hjLt a hc; rcases ha with h | h | h | h <;> omega
        exact ⟨htag1 a hne, hFr1Out a (hFootSc a (Or.inl (hOwn0 a hne))) hnc⟩)
      (fun i hi => Or.inl (SolverLevelMetaAt.atCaps hcaps.1 hcaps.2 i hi).2.2.1)
      rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl
  have hFrReg : ∀ a, sb ≤ a → a < B.endAddr → st1.mem a = mem a := fun a h1 h2 =>
    hFr1Out a (by omega) (fun hc => hFootDisj a h1 h2 (Or.inr (Or.inr ⟨j, hjLt, hc⟩)))
  have hMlocEq1 : selectMlocOf B metaBase (solverLevelG tok1 st1.mem) pLast =
      selectMlocOf B metaBase (solverLevelG tok mem) pLast :=
    selectMlocOf_congr_fin fun i hi => by
      rw [hBd] at hi
      have htg := hcaps.1.2.2.2.2.1 (cfg.P.d + i) (by omega)
      rw [← Nat.add_assoc] at htg
      change st1.mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + i) =
        mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + i)
      exact hFr1Out _ (hFootSc _ (Or.inl (hOwn0 _ (by rw [htg]; omega))))
        (fun hc => by have := hCoreTags j hjLt _ hc; dsimp only [j] at this; rw [htg] at this; omega)
  have htab1 : SelectMetaTableAt st1.mem (selectMlocOf B metaBase (solverLevelG tok1 st1.mem) pLast) := by
    rw [hMlocEq1]
    exact htab.of_agree fun a h1 h2 => hFrReg a (by
      simp only [selectMlocOf] at h1; have := hreg.1; have := hreg.2.1; have := hreg.2.2.1
      have : loc.hb ≤ loc.endAddr := by rw [loc.endAddr_eq]; omega
      omega) (by
      simp only [selectMlocOf] at h2; have := hreg.2.2.2.1
      have : B.base ≤ B.endAddr := by rw [B.endAddr_eq]; omega
      omega)
  have hHeap1 : SelectHeapAt st1.mem loc 4 heapSize :=
    hHeap.of_agree fun a h1 h2 => hFrReg a (by have := hreg.1; omega) (by
      have := hreg.2.1; have := hreg.2.2.1; have := hreg.2.2.2.1
      have : B.base ≤ B.endAddr := by rw [B.endAddr_eq]; omega
      omega)
  have hblk1 : SelBlocksDataAt st1.mem B P D pLast :=
    hblk.of_agree fun a h1 h2 => hFrReg a (by omega) h2
  have hSrcDisj : st1.mem scratch + dynGraphSize vCap eCap ≤ B.base ∨ B.endAddr ≤ st1.mem scratch := by
    have hD := interval_disj_region (a := st1.mem scratch) (len := dynGraphSize vCap eCap)
      (by unfold dynGraphSize; omega) hsbLtEnd (fun x hx1 hx2 hx => by
        rcases hGPtrFoot1 x hx.1 hx.2 with hfy | hnew
        · rcases hFoot1 x hfy with hfx | hnew1
          · exact hFootDisj x hx1 hx2 (Or.inr (Or.inr ⟨j, hjLt, hfx⟩))
          · omega
        · omega)
    exact hD.imp (by omega) id
  refine ⟨b3, o3, st1, c3, tok1, hb3, hr3, hcur1Lo, hcur1Hi, hrep1,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    hcaps1, htab1, hHeap1, hblk1, hDG1, by omega, hSrcDisj, hFr1Out, hft1,
    fun _ ha => Or.inl ha, fun a ha => by dsimp only [tok1]; rw [ite_eq_right (by omega)],
    htag1, hz1, ?_⟩
  change c3 + Rcore.phi (tok.coreHandle j) y1 st1.mem ≤ Psc.readout + Rcore.phi (tok.coreHandle j) (tok.coreTok j) mem at hcost3
  dsimp only [Rrep, tok1] at hphi1 ⊢
  omega

/-! ## 2. Suffix-refresh finalization (`selectDeepFinalize_runs`) -/

set_option maxHeartbeats 800000 in
/-- Run `selectRefreshFinalizeBody` (`selectPhiLoop` from `cur` + `selectRebuildSuffix` from `cur`)
on an in-place `SelectRegion` whose `F`, `len`, `emb`, `lastG`, `g0`, and `metaTable` have been
refreshed for `model'`, whose prefix `< cur` agrees with `model` (retaining `φOld` and
`SelectHeapMatchesChain` for `model`), and whose newly rebuilt solver level graphs may lie on either
side of `[sb, B.endAddr)`. Restores `SelectRegionAt` (hence `SolverSelectInv`) for `model'` with
`sg'.loc = loc`, `sg'.owned = [sb, B.endAddr)`, and `sg'.reembPot = chainReembPot pot model'.chain`. -/
theorem selectDeepFinalize_runs
    {w L P m V psi k epsExp drainUnit vCap eCap sb metaBase pLast cur sizeOld
      evalSpace evalCost scratch pos : ℕ}
    {phiLoopProc phiFillProc rebuildSuffixProc rebuildLvlProc : ℕ}
    {cfg : Alg2Config} {G G₀ G₀' : MGraph} {σ σ_mwu γ_ℓ γ_c σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {pot : cfg.T.State → ℕ}
    {root : ℕ} {model model' : Alg2State cfg}
    {tok' : SolverToken cfg L Rcore}
    {loc : SelectHeapLoc} {B : SelectBlocksLoc} {φOld : ℕ → ℕ → ℝ}
    {mem : ℕ → ℕ} {p : Program} {ω : ℕ → Bool}
    {PhiBd : (ℕ → ℕ → ℝ) → ℕ → Prop}
    (hlocalCore : Rcore.Local)
    (hw16 : 16 < 2 ^ w) (hw10 : 10 ≤ w) (hLkW : L < 2 ^ w) (hpLastW : pLast < 2 ^ w)
    (hcurLe : cur ≤ cfg.P.d)
    (hreg : SelectRegion sb loc B metaBase)
    (hcap : loc.cap = selectHeapCap cfg G m)
    (hBd : B.d = cfg.P.d) (hBv : B.vCap = vCap) (hBe : B.eCap = eCap) (hBLk : B.Lk = L)
    (hrep' : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model' tok' mem)
    (hFootSc : ∀ a,
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok' a → a < scratch)
    (hFootDisj : ∀ a, sb ≤ a → a < B.endAddr →
      ¬ (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok' a)
    (hhbRd : mem (solverSelectHeapAddr tok'.table cfg.P.d) = sb)
    (hBlkRd : mem (solverSelectBlocksAddr tok'.table cfg.P.d) = B.base)
    (hcaps' : SolverLevelCapsInv P V vCap eCap model' tok' mem)
    (hmodOld : SelectModelInv model G₀ σ σ_mwu γ_ℓ γ_c)
    (hmodNew : SelectModelInv model' G₀' σ' σ'_mwu γ'_ℓ γ'_c)
    (hPrefG : ∀ j < cur, model'.chain.toTreeChain.G j = model.chain.toTreeChain.G j)
    (hPrefLSF : ∀ j < cur,
      model'.chain.toTreeChain.activeLSF j = model.chain.toTreeChain.activeLSF j)
    (hPrefS : ∀ j < cur,
      model'.chain.toTreeChain.activeS j = model.chain.toTreeChain.activeS j)
    (hPrefEmb : ∀ j < cur,
      model'.chain.toTreeChain.activeEmb j = model.chain.toTreeChain.activeEmb j)
    (hgEq : ∀ e, model'.chain.g e = model.chain.g e)
    (hℓEq : ∀ e, model'.chain.ℓ e = model.chain.ℓ e)
    (hMatchOld : SelectHeapMatchesChain mem loc 4 P model.chain.toTreeChain model.chain.g
      model.chain.ℓ sizeOld)
    (hPhiPref : ∀ j < cur,
      SelPartPhi mem B P j (model'.chain.toTreeChain.G j).V (φOld j))
    (hPotPref : ∀ j < cur,
      SelectPotInvAt model'.chain.toTreeChain model'.chain.g φOld j)
    (hPhiBdPref : ∀ j < cur, PhiBd φOld j)
    (hPhiBdStep : ∀ j ≤ cfg.P.d, ∀ (φ : ℕ → ℕ → ℝ) (φj : ℕ → ℝ),
      (∀ k < j, SelectPotInvAt model'.chain.toTreeChain model'.chain.g φ k) →
      (∀ k < j, PhiBd φ k) →
      (∀ v ∈ (model'.chain.toTreeChain.activeLSF j).F.F.V,
        ∃ r ∈ (model'.chain.toTreeChain.activeLSF j).F.F.V,
          (model'.chain.toTreeChain.activeLSF j).F.F.Connected v r ∧
          φj v = walkInner (potGrad model'.chain.toTreeChain model'.chain.g φ j)
            ((model'.chain.toTreeChain.activeLSF j).F.F.forestPath v r)) →
      ∀ k < j + 1, PhiBd (Function.update φ j φj) k)
    (htab : SelectMetaTableAt mem (selectMlocOf B metaBase (solverLevelG tok' mem) pLast))
    (hF : ∀ j ≤ cfg.P.d, SelPartF mem B j (model'.chain.toTreeChain.activeLSF j).F.F)
    (hLen : ∀ j ≤ cfg.P.d,
      SelPartLen mem B P j (model'.chain.toTreeChain.G j).E
        (model'.chain.toTreeChain.chainLen model'.chain.ℓ (j + 1)) pLast)
    (hEmb : ∀ j < cfg.P.d,
      SelPartEmb mem B j (model'.chain.toTreeChain.activeCore j).E
        (model'.chain.toTreeChain.activeEmb j))
    (hLastG : SelPartLast mem B (model'.chain.toTreeChain.G cfg.P.d))
    (hG0 : SelPartG0 mem B P (model'.chain.toTreeChain.G 0).E model'.chain.g)
    (hVcap : ∀ j ≤ cfg.P.d, ∀ v ∈ (model'.chain.toTreeChain.G j).V, v < vCap)
    (hEcapHeap : ∀ j ≤ cfg.P.d, ∀ e ∈ (model'.chain.toTreeChain.G j).E, e < loc.cap)
    (hFit : ∀ j ≤ cfg.P.d, ∀ φ' : ℕ → ℕ → ℝ,
      (∀ k < j, SelectPotInvAt model'.chain.toTreeChain model'.chain.g φ' k) →
      (∀ k < j, PhiBd φ' k) →
      (∀ e ∈ (model'.chain.toTreeChain.activeLSF j).F.F.E,
        PotGradEvalFits 4 L P model'.chain.toTreeChain model'.chain.g φ' j e) ∧
      ForestWalkFits 4 L P (model'.chain.toTreeChain.activeLSF j).F.F
        (potGrad model'.chain.toTreeChain model'.chain.g φ' j))
    (hpPhiLoop : p.procs[phiLoopProc]? = some (selectPhiLoopBody phiLoopProc phiFillProc))
    (hPhiFill :
      let mloc := selectMlocOf B metaBase (solverLevelG tok' mem) pLast
      ∀ φ : ℕ → ℕ → ℝ,
        MeetsContract w p phiFillProc
          (selectPhiFillContract w 4 P mloc model'.chain.toTreeChain G₀' model'.chain.g
            model'.chain.ℓ σ' σ'_mwu γ'_ℓ γ'_c φ))
    (hpRebSuf : p.procs[rebuildSuffixProc]? =
      some (selectRebuildSuffixBody rebuildSuffixProc rebuildLvlProc))
    (hRebLvl :
      let mloc := selectMlocOf B metaBase (solverLevelG tok' mem) pLast
      ∀ φ : ℕ → ℕ → ℝ,
        MeetsContract w p rebuildLvlProc
          (selectRebuildLevelNoRoomContract w 4 P loc mloc model'.chain.toTreeChain model'.chain.g
            model'.chain.ℓ φ (fun j => model'.chain.toTreeChain.chainLen model'.chain.ℓ (j + 1))
            evalSpace evalCost))
    (hEndSc : B.endAddr ≤ scratch)
    (hz : ZeroFrom mem scratch)
    (hroom : scratch + selectRefreshFinalizeSpace mem loc model'.chain.toTreeChain cur L evalSpace < 2 ^ w) :
    let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
    ∃ (sc2 cost : ℕ) (out : State) (sg' : SelectGhost),
      Runs w p ω (selectRefreshFinalizeBody phiLoopProc rebuildSuffixProc)
        (startState [sb, metaBase, cur, cfg.P.d, L, scratch] mem pos) (.returned sc2) out cost ∧
      scratch ≤ sc2 ∧
      sc2 ≤ scratch + selectRefreshFinalizeSpace mem loc model'.chain.toTreeChain cur L evalSpace ∧
      ZeroFrom out.mem sc2 ∧
      sg'.loc = loc ∧
      sg'.owned = (fun a => sb ≤ a ∧ a < B.endAddr) ∧
      sg'.reembPot = chainReembPot pot model'.chain ∧
      Rrep.rep root model' tok' out.mem ∧
      Rrep.phi root tok' out.mem = Rrep.phi root tok' mem ∧
      SolverLevelCapsInv P V vCap eCap model' tok' out.mem ∧
      SelectRegionAt G P m vCap eCap pLast sb metaBase B model' tok' sg' out.mem ∧
      (∀ j ≤ cfg.P.d, PhiBd sg'.φ j) ∧
      (∀ a < scratch, (a < sb ∨ B.endAddr ≤ a) → out.mem a = mem a) ∧
      cost ≤ selectRefreshFinalizeCost mem loc model'.chain.toTreeChain cur L evalCost := by
  intro Rrep
  set C := model.chain.toTreeChain
  set C' := model'.chain.toTreeChain
  set g := model.chain.g
  set g' := model'.chain.g
  set ℓ := model.chain.ℓ
  set ℓ' := model'.chain.ℓ
  set mloc := selectMlocOf B metaBase (solverLevelG tok' mem) pLast
  have hH : C.Holds G₀ ℓ σ σ_mwu γ_ℓ γ_c := hmodOld.1
  have hH' : C'.Holds G₀' ℓ' σ' σ'_mwu γ'_ℓ γ'_c := hmodNew.1
  have hCd : C.d = cfg.P.d := rfl
  have hC'd : C'.d = cfg.P.d := rfl
  have hmlocD : mloc.d = C'.d := by simp only [mloc, selectMlocOf, hBd, hC'd]
  have hmlocLk : mloc.Lk = L := by simp only [mloc, selectMlocOf, hBLk]
  have hlocHb : loc.hb = sb := hreg.1
  have hsbLtEnd : sb < B.endAddr := by
    have := hreg.1; have := hreg.2.1; have := hreg.2.2.1; have := hreg.2.2.2.1
    have : loc.hb < loc.endAddr := by rw [loc.endAddr_eq]; unfold selectHeapSize shHdrSize; omega
    have : B.base ≤ B.endAddr := by rw [B.endAddr_eq]; omega
    omega
  have hsbLeMeta : sb ≤ metaBase := by
    have := hreg.1; have := hreg.2.1; have := hreg.2.2.1
    have : loc.hb ≤ loc.endAddr := by rw [loc.endAddr_eq]; omega
    omega
  have hMetaEnd : metaBase + selectLevelMetaSize mloc.d = B.base := by
    simp only [mloc, selectMlocOf]; exact hreg.2.2.2.1.symm
  have hBaseLeEnd : B.base ≤ B.endAddr := by rw [B.endAddr_eq]; omega
  have hBlkLeLast : ∀ j ≤ cfg.P.d, B.fPtr j + B.levelSize ≤ B.lastGPtr := fun j hj =>
    B.blk_le_last (by omega)
  have hLastLeG0 : B.lastGPtr + dynGraphSize vCap eCap = B.g0Ptr := by
    rw [← hBv, ← hBe]; rfl
  have hG0LeEnd : B.g0Ptr + eCap * L = B.endAddr := by
    rw [← hBe, ← hBLk]; rfl
  -- Two-sided disjointness of every solver level graph `solverLevelG tok' mem j` from `[sb, B.endAddr)`
  have hOwnOfTag := hrep'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hGEnd : ∀ j < cfg.P.d,
      solverLevelG tok' mem j + dynGraphSize vCap eCap ≤ scratch ∧
      (solverLevelG tok' mem j + dynGraphSize vCap eCap ≤ sb ∨
        B.endAddr ≤ solverLevelG tok' mem j) := by
    intro j hj
    have hAt := SolverLevelMetaAt.atCaps hcaps'.1 hcaps'.2 j hj
    have hDGP : 0 < dynGraphSize vCap eCap := by unfold dynGraphSize; omega
    have hSc : solverLevelG tok' mem j + dynGraphSize vCap eCap ≤ scratch := by
      have htg := hAt.2.2.2.2 (solverLevelG tok' mem j + dynGraphSize vCap eCap - 1)
        (by dsimp only [solverLevelG]; omega) (by dsimp only [solverLevelG]; omega)
      have hne : tok'.tag (solverLevelG tok' mem j + dynGraphSize vCap eCap - 1) ≠ 0 := by
        split_ifs at htg <;> omega
      have hlt := hFootSc _ (Or.inl (hOwnOfTag _ hne))
      omega
    have hDisj := interval_disj_region hDGP hsbLtEnd fun x hx1 hx2 hx => by
      have htg := hAt.2.2.2.2 x hx.1 hx.2
      have hne : tok'.tag x ≠ 0 := by split_ifs at htg <;> omega
      exact hFootDisj x hx1 hx2 (Or.inl (hOwnOfTag x hne))
    exact ⟨hSc, hDisj⟩
  have hGDG : ∀ j ≤ cfg.P.d, DynGraphAt mem (mloc.GPtr j) (mloc.vCap j) (mloc.eCap j) (C'.G j) := by
    intro j hj
    dsimp only [mloc, selectMlocOf]
    rw [hBd, hBv, hBe]
    by_cases hlt : j < cfg.P.d
    · simp only [hlt, ↓reduceIte]
      exact (SolverLevelMetaAt.atCaps hcaps'.1 hcaps'.2 j hlt).1
    · have hjeq : j = cfg.P.d := by omega
      subst hjeq
      simp only [lt_irrefl, ↓reduceIte]
      rw [← hBv, ← hBe]
      exact hLastG
  -- Step 1: `selectPhiLoop` from `cur`
  have hpref0 : SelectPhiPrefixAt mem mloc 4 P C' g' φOld cur := by
    refine ⟨hmlocD, htab.1, htab.2.1, ?_, fun k hk => ?_⟩
    · simpa only [mloc, selectMlocOf, hBLk] using hG0.2
    · have hkLe : k ≤ cfg.P.d := by omega
      have hrow := htab.2.2 k (by rw [hmlocD, hC'd]; exact hkLe)
      refine ⟨hrow.1, hrow.2.1, hrow.2.2.1, hrow.2.2.2.1, hGDG k hkLe, ?_⟩
      simpa only [mloc, selectMlocOf, hBLk] using (hPhiPref k hk).2
  have hlevels0 : ∀ j, cur ≤ j → j ≤ C'.d →
      mem (smEntryAddr mloc.metaBase mloc.d 0 j) = mloc.GPtr j ∧
      mem (smEntryAddr mloc.metaBase mloc.d 1 j) = mloc.vCap j ∧
      mem (smEntryAddr mloc.metaBase mloc.d 2 j) = mloc.eCap j ∧
      mem (smEntryAddr mloc.metaBase mloc.d 3 j) = mloc.phiPtr j ∧
      mem (smEntryAddr mloc.metaBase mloc.d 6 j) = mloc.fPtr j ∧
      DynGraphAt mem (mloc.GPtr j) (mloc.vCap j) (mloc.eCap j) (C'.G j) ∧
      DynGraphAt mem (mloc.fPtr j) (mloc.vCap j) (mloc.eCap j) (C'.activeLSF j).F.F := by
    intro j _ hj
    have hrow := htab.2.2 j (by omega)
    exact ⟨hrow.1, hrow.2.1, hrow.2.2.1, hrow.2.2.2.1, hrow.2.2.2.2.2.2.1, hGDG j hj, hF j hj⟩
  have hdisj0 : ∀ j, cur ≤ j → j ≤ C'.d →
      SelectPhiPrefixBelow mloc j scratch ∧
      SelectPhiTargetDisjoint mloc j scratch ∧
      mloc.GPtr j + dynGraphSize (mloc.vCap j) (mloc.eCap j) ≤ scratch ∧
      (∀ j', j ≤ j' → j' ≤ C'.d →
        mloc.phiPtr j + mloc.vCap j * mloc.Lk ≤ mloc.GPtr j' ∨
          mloc.GPtr j' + dynGraphSize (mloc.vCap j') (mloc.eCap j') ≤ mloc.phiPtr j) ∧
      (∀ j', j < j' → j' ≤ C'.d →
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
      · simp only [hlt, ↓reduceIte]; exact (hGEnd k hlt).1
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
         have hGk := (hGEnd k hlt).2
         have hkj := B.blk_le_of_lt hk
         have hkB := hphiBnd k (by omega)
         refine ⟨?_, Or.inl ?_⟩
         · simp only [mloc, selectMlocOf, hBd, hlt, ↓reduceIte, hBv, hBe, hBLk]
           rcases hGk with h1 | h2
           · left; omega
           · right; omega
         · simp only [mloc, selectMlocOf, hBv, hBLk]; omega⟩,
      hGPBnd j hj,
      fun j' hj1 hj2 => by
        have hjB := hphiBnd j hj
        dsimp only [mloc, selectMlocOf]; rw [hBd, hBv, hBe, hBLk]
        by_cases hlt : j' < cfg.P.d
        · simp only [hlt, ↓reduceIte]
          rcases (hGEnd j' hlt).2 with h1 | h2
          · right; omega
          · left; omega
        · simp only [hlt, ↓reduceIte]; left; omega,
      fun j' hj1 hj2 => by
        have hjB := hphiBnd j hj
        have hlt := B.blk_le_of_lt hj1
        left; simp only [mloc, selectMlocOf, hBv, hBLk]; omega⟩
  have hPhiLoopSpLe : selectPhiLoopSpace C' cur mloc.Lk ≤
      selectRefreshFinalizeSpace mem loc C' cur L evalSpace := by
    rw [hmlocLk]; unfold selectRefreshFinalizeSpace; exact Nat.le_add_right _ _
  have hsbW : sb < 2 ^ w := by omega
  have hmetaW : mloc.metaBase < 2 ^ w := by simp only [mloc, selectMlocOf]; omega
  have hdW : C'.d < 2 ^ w := by
    have : selectLevelMetaSize mloc.d = 2 + 8 * (mloc.d + 1) := rfl; omega
  have hcurW : cur < 2 ^ w := by omega
  have hLkW' : mloc.Lk < 2 ^ w := by rw [hmlocLk]; exact hLkW
  obtain ⟨sc1, cPhi, st1, φ', hrPhi, hsc1Lo, hsc1Hi, hz1, _, hpref1, hpot1, hphiBd1, hfr1, hcPhi⟩ :=
    selectPhiLoop_runs (ω := ω) (PhiBd := PhiBd) hpPhiLoop hPhiFill hw16 hw10 hH'
      (by simpa only [mloc, selectMlocOf, hBe] using hG0.1)
      hPhiBdStep
      (fun j hj φ0 hpot0 hbd0 => by rw [hmlocLk]; exact hFit j hj φ0 hpot0 hbd0)
      (C'.d + 1 - cur) cur scratch pos mem φOld rfl
      hmetaW hcurW hdW hLkW' hpref0 hPotPref hPhiBdPref
      hlevels0 hdisj0 hz (by omega)
  have hNotPhi : ∀ a, (a < B.base ∨ B.lastGPtr ≤ a) →
      ∀ j, cur ≤ j → j ≤ C'.d → a < mloc.phiPtr j ∨ mloc.phiPtr j + mloc.vCap j * mloc.Lk ≤ a := by
    intro a ha j _ hj
    have hlo : B.base ≤ B.phiPtr j := by unfold SelectBlocksLoc.phiPtr SelectBlocksLoc.fPtr; omega
    have hhi : B.phiPtr j + B.vCap * B.Lk ≤ B.lastGPtr := by
      have hbl := B.blk_le_last (j := j) (by omega)
      unfold SelectBlocksLoc.levelSize at hbl
      unfold SelectBlocksLoc.phiPtr; omega
    simp only [mloc, selectMlocOf]
    rcases ha with h | h <;> [left; right] <;> omega
  have hFr1OffBlocks : ∀ a < scratch, (a < B.base ∨ B.endAddr ≤ a) → st1.mem a = mem a := fun a ha h =>
    hfr1 a ha (hNotPhi a (by rcases h with h1 | h2 <;> [left; right] <;> omega))
  have hFr1BelowBase : ∀ a < B.base, st1.mem a = mem a := fun a ha =>
    hFr1OffBlocks a (by omega) (Or.inl ha)
  have hHeapAgree1 : ∀ a, loc.hb ≤ a → a < loc.endAddr → st1.mem a = mem a := fun a _ ha2 =>
    hFr1BelowBase a (by have := hreg.2.1; have := hreg.2.2.1; have := hreg.2.2.2.1; omega)
  have hMatch1 : SelectHeapMatchesChain st1.mem loc 4 P C g ℓ sizeOld :=
    hMatchOld.of_agree hHeapAgree1
  have hCandEq1 : ∀ j, levelCandCount st1.mem loc j = levelCandCount mem loc j := fun j => by
    unfold levelCandCount
    congr 1; ext e
    simp only [Finset.mem_filter, Finset.mem_range]
    refine and_congr_right fun he => ?_
    have hpos : loc.hb ≤ loc.posPtr + e ∧ loc.posPtr + e < loc.endAddr := by
      rw [loc.endAddr_eq]; unfold SelectHeapLoc.posPtr SelectHeapLoc.arrPtr selectHeapSize shHdrSize; omega
    have hlvl : loc.hb ≤ loc.lvlPtr + e ∧ loc.lvlPtr + e < loc.endAddr := by
      rw [loc.endAddr_eq]; unfold SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr SelectHeapLoc.arrPtr selectHeapSize shHdrSize; omega
    rw [hHeapAgree1 _ hpos.1 hpos.2, hHeapAgree1 _ hlvl.1 hlvl.2]
  have hSufSp1Eq : selectRebuildSuffixSpace st1.mem loc C' cur evalSpace =
      selectRebuildSuffixSpace mem loc C' cur evalSpace := by
    unfold selectRebuildSuffixSpace
    exact Finset.sum_congr rfl fun j _ => by rw [hCandEq1 j]
  have hSufCost1Eq : selectRebuildSuffixCost st1.mem loc C' cur evalCost =
      selectRebuildSuffixCost mem loc C' cur evalCost := by
    unfold selectRebuildSuffixCost
    exact congrArg (· + 20) (Finset.sum_congr rfl fun j _ => by rw [hCandEq1 j])
  have hTab1 : SelectMetaTableAt st1.mem mloc :=
    htab.of_agree fun a _ ha2 => hFr1BelowBase a (by
      simp only [mloc, selectMlocOf] at hMetaEnd ha2 ⊢; omega)
  have hBlk1 : SelectBlocksAt st1.mem B P C' g' ℓ' φ' pLast := by
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
  have hPotInv1 : SelectPotInv C' g' φ' := fun j hj => hpot1 j hj
  have hMetaDisj1 : SelectMetaDisjoint mloc loc sc1 :=
    selectMetaDisjoint_of_region hreg (by omega) fun j hj => by
      rw [hBd] at hj
      obtain ⟨hSc, hDisj⟩ := hGEnd j hj
      rw [hBv, hBe]
      refine ⟨by omega, ?_⟩
      rcases hDisj with h1 | h2
      · left; omega
      · right; have := hreg.2.1; have := hreg.2.2.1; have := hreg.2.2.2.1; omega
  have hMeta1OfAgree : ∀ m', (∀ a < sc1, (a < loc.hb ∨ loc.endAddr ≤ a) → m' a = st1.mem a) →
      SelectLevelMetaAt m' mloc 4 P C' g' ℓ' φ' (fun j => C'.chainLen ℓ' (j + 1)) := by
    intro m' hm'
    have hTabM' : SelectMetaTableAt m' mloc :=
      hTab1.of_agree fun a ha1 ha2 => hm' a (by simp only [mloc, selectMlocOf] at hMetaEnd ha2; omega)
        (Or.inr (by simp only [mloc, selectMlocOf] at ha1; have := hreg.2.1; have := hreg.2.2.1; omega))
    have hBlkM' : SelectBlocksAt m' B P C' g' ℓ' φ' pLast :=
      hBlk1.of_agree fun a ha1 ha2 => hm' a (by omega)
        (Or.inr (by have := hreg.2.1; have := hreg.2.2.1; have := hreg.2.2.2.1; omega))
    refine selectLevelMetaAt_of_blocks (by omega) hTabM' (fun j hj => ?_) (fun j hj => ?_) hBlkM' hPotInv1
    · rw [hBd] at hj
      have hG0j := (SolverLevelMetaAt.atCaps hcaps'.1 hcaps'.2 j hj).1
      obtain ⟨hSc, hDisj⟩ := hGEnd j hj
      rw [hBv, hBe]
      exact DynGraphAt.of_agree hG0j fun a ha1 ha2 =>
        (hm' a (by omega) (by
          rcases hDisj with h1 | h2
          · left; omega
          · right; have := hreg.2.1; have := hreg.2.2.1; have := hreg.2.2.2.1; omega)).trans
          (hFr1OffBlocks a (by omega) (by rcases hDisj with h1 | h2 <;> [left; right] <;> omega))
    · rw [hBd] at hj; exact hmodNew.activeS_eq_G_succ j hj
  have hMeta1 : SelectLevelMetaAt st1.mem mloc 4 P C' g' ℓ' φ' (fun j => C'.chainLen ℓ' (j + 1)) :=
    hMeta1OfAgree st1.mem fun _ _ _ => rfl
  -- Step 2: `selectRebuildSuffix` from `cur` (no room precondition needed!)
  have hRebSuf := selectRebuildSuffix_meetsContract_noRoom (w := w) (h := 4) (P := P) (loc := loc)
    (mloc := mloc) (C := C') (G := G₀') (g := g') (ℓ := ℓ') (σ := σ') (σ_mwu := σ'_mwu)
    (γ_ℓ := γ'_ℓ) (γ_c := γ'_c) (φ := φ') (coreLen := fun j => C'.chainLen ℓ' (j + 1))
    (evalSpace := evalSpace) (evalCost := evalCost) hpRebSuf (hRebLvl φ')
  obtain ⟨bReb, hbReb, oReb, st2, cReb, hrReb, hpReb, hcReb⟩ :=
    hRebSuf [loc.hb, mloc.metaBase, cur, C'.d, sc1] st1.mem st1.pos ω
      (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro v (rfl | rfl | rfl | rfl | rfl)
        · rw [hreg.1]; exact hsbW
        · exact hmetaW
        · exact hcurW
        · exact hdW
        · rw [hmlocLk] at hsc1Hi; unfold selectRefreshFinalizeSpace at hroom; omega)
      ⟨cur, sc1, sizeOld, rfl, hw16, by simpa only [mloc, selectMlocOf] using hpLastW,
        by have := hreg.2.1; have := hreg.2.2.1; omega,
        by rw [hreg.2.2.2.2.1, hBd]; rfl, hreg.2.2.2.2.2.1.symm, hH',
        fun j _ hj => hEcapHeap j hj,
        hMatch1.1, hMeta1, hMetaDisj1, hMeta1OfAgree, hz1,
        by rw [hSufSp1Eq]; rw [hmlocLk] at hsc1Hi; unfold selectRefreshFinalizeSpace at hroom; omega⟩
  set sc2 := oReb.value
  have hpostReb := hpReb
  obtain ⟨hsc2Lo, hsc2Hi, _, ⟨_, hfr2⟩, hz2, _, _⟩ := hpReb
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hsc2Lo hsc2Hi hfr2
  obtain ⟨size2, hMatch2⟩ := selectRebuildShift_preserves_matchesChain (w := w) (evalCost := evalCost) hH hH'
    (by rw [hreg.2.2.2.2.1, hBd]; rfl) (by omega)
    hPrefG hPrefLSF hPrefS hPrefEmb hgEq hℓEq hMatch1 hpostReb
  -- Stitch the two calls into `selectRefreshFinalizeBody`
  let s0 := startState [sb, metaBase, cur, cfg.P.d, L, scratch] mem pos
  let rg6 := Function.update s0.regs 6 sc1
  let rg7 := Function.update rg6 7 sc2
  have hsc1W : sc1 < 2 ^ w := by rw [hmlocLk] at hsc1Hi; unfold selectRefreshFinalizeSpace at hroom; omega
  have hsc2W : sc2 < 2 ^ w := by rw [hSufSp1Eq] at hsc2Hi; rw [hmlocLk] at hsc1Hi; unfold selectRefreshFinalizeSpace at hroom; omega
  have r1 : Runs w p ω (.call 6 phiLoopProc [.reg 1, .reg 2, .reg 3, .reg 4, .reg 5])
      s0 .normal ⟨st1.mem, rg6, st1.pos⟩ (cPhi + 6) :=
    runs_call_iff.mpr ⟨[mloc.metaBase, cur, C'.d, mloc.Lk, scratch],
      selectPhiLoopBody phiLoopProc phiFillProc, .returned sc1, st1, cPhi,
      by dsimp only [s0, mloc]; simp [evalArgs, Expr.eval, startState, selectMlocOf, hBLk, hC'd],
      hpPhiLoop, hrPhi, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
  have r2 : Runs w p ω (.call 7 rebuildSuffixProc [.reg 0, .reg 1, .reg 2, .reg 3, .reg 6])
      ⟨st1.mem, rg6, st1.pos⟩ .normal ⟨st2.mem, rg7, st2.pos⟩ (cReb + 6) :=
    runs_call_iff.mpr ⟨[loc.hb, mloc.metaBase, cur, C'.d, sc1],
      bReb, oReb, st2, cReb,
      by dsimp only [rg6, s0, mloc]; simp [evalArgs, Expr.eval, startState, hreg.1, selectMlocOf, hC'd],
      hbReb, hrReb, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
  have r3 : Runs w p ω (.ret (.reg 7))
      ⟨st2.mem, rg7, st2.pos⟩ (.returned sc2) ⟨st2.mem, rg7, st2.pos⟩ 2 :=
    runs_ret_iff.mpr ⟨sc2, by simp [Expr.eval, rg7], rfl, rfl, rfl⟩
  have rFull : Runs w p ω (selectRefreshFinalizeBody phiLoopProc rebuildSuffixProc) s0 (.returned sc2)
      ⟨st2.mem, rg7, st2.pos⟩ ((cPhi + 6) + ((cReb + 6) + 2 + 1) + 1) := by
    unfold selectRefreshFinalizeBody
    exact runs_seq_iff.mpr (Or.inr ⟨_, _, _, r1, runs_seq_iff.mpr (Or.inr ⟨_, _, _, r2, r3, rfl⟩), rfl⟩)
  -- Frame off `[sb, B.endAddr)` and reconstruct `Rrep.rep`, `SolverLevelCapsInv`, `SelectRegionAt`
  have hFrOffReg : ∀ a < scratch, (a < sb ∨ B.endAddr ≤ a) → st2.mem a = mem a := fun a ha hoff => by
    have hnotHeap : a < loc.hb ∨ loc.endAddr ≤ a := by
      have := hreg.1; have := hreg.2.1; have := hreg.2.2.1; have := hreg.2.2.2.1; omega
    exact (hfr2 a (by omega) hnotHeap).trans (hFr1OffBlocks a ha (by rcases hoff with h1 | h2 <;> [left; right] <;> omega))
  have hFrFoot : ∀ a, Rrep.foot root tok' a → st2.mem a = mem a := fun a ha =>
    hFrOffReg a (hFootSc a ha) (by
      by_contra h; obtain ⟨h1, h2⟩ := not_or.mp h
      exact hFootDisj a (Nat.le_of_not_lt h1) (Nat.lt_of_not_le h2) ha)
  have hLocal := solverStateRep_local cfg L P m V psi k epsExp drainUnit hlocalCore
  have hrep2 : Rrep.rep root model' tok' st2.mem :=
    (hLocal root model' tok' mem st2.mem fun a ha => (hFrFoot a ha).symm).1 hrep'
  have hphi2 : Rrep.phi root tok' st2.mem = Rrep.phi root tok' mem :=
    ((hLocal root model' tok' mem st2.mem fun a ha => (hFrFoot a ha).symm).2).symm
  have hCaps2 : SolverLevelCapsInv P V vCap eCap model' tok' st2.mem := by
    have hTagOwn : ∀ a, tok'.tag a ≠ 0 → st2.mem a = mem a := fun a hne =>
      hFrFoot a (Or.inl (hOwnOfTag a hne))
    exact hcaps'.preserve rfl hcaps'.1.2.1
      (fun a ha => ⟨rfl, hTagOwn a (by rcases ha with h | h | h | h <;> omega)⟩)
      (fun j hj => (SolverLevelMetaAt.atCaps hcaps'.1 hcaps'.2 j hj).2.2.1)
      rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl
  have hFrMetaToEnd : ∀ a, metaBase ≤ a → a < B.endAddr → st2.mem a = st1.mem a := fun a h1 h2 =>
    hfr2 a (by omega) (Or.inr (by have := hreg.2.1; have := hreg.2.2.1; omega))
  have hMlocEq2 : selectMlocOf B metaBase (solverLevelG tok' st2.mem) pLast = mloc :=
    selectMlocOf_congr_fin fun j hj => by
      rw [hBd] at hj
      have htg := hcaps'.1.2.2.2.2.1 (cfg.P.d + j) (by omega)
      rw [← Nat.add_assoc] at htg
      exact hFrFoot _ (Or.inl (hOwnOfTag _ (by omega)))
  have hTab2 : SelectMetaTableAt st2.mem
      (selectMlocOf B metaBase (solverLevelG tok' st2.mem) pLast) := by
    rw [hMlocEq2]
    exact hTab1.of_agree fun a ha1 ha2 =>
      hFrMetaToEnd a (by simp only [mloc, selectMlocOf] at ha1; exact ha1)
        (by simp only [mloc, selectMlocOf] at hMetaEnd ha2; omega)
  have hBlk2 : SelectBlocksAt st2.mem B P C' g' ℓ' φ' pLast :=
    hBlk1.of_agree fun a ha1 ha2 => hFrMetaToEnd a (by omega) ha2
  have hhbRd2 : st2.mem (solverSelectHeapAddr tok'.table cfg.P.d) = sb :=
    (hFrFoot _ (Or.inl (hOwnOfTag _ (by have := hcaps'.1.1.2.2.1; omega)))).trans hhbRd
  have hBlkRd2 : st2.mem (solverSelectBlocksAddr tok'.table cfg.P.d) = B.base :=
    (hFrFoot _ (Or.inl (hOwnOfTag _ (by have := hcaps'.1.1.2.2.2; omega)))).trans hBlkRd
  let sg' : SelectGhost :=
    { loc := loc
      mloc := selectMlocOf B metaBase (solverLevelG tok' st2.mem) pLast
      size := size2
      φ := φ'
      coreLen := fun j => C'.chainLen ℓ' (j + 1)
      owned := fun a => sb ≤ a ∧ a < B.endAddr
      reembPot := chainReembPot pot model'.chain }
  have hRegAt2 : SelectRegionAt G P m vCap eCap pLast sb metaBase B model' tok' sg' st2.mem :=
    ⟨hreg, hcap, hBd, hBv, hBe, hBLk, rfl, hhbRd2, hBlkRd2, rfl, hTab2, hBlk2, hMatch2,
      hPotInv1, rfl, G₀', σ', σ'_mwu, γ'_ℓ, γ'_c, hmodNew⟩
  refine ⟨sc2, _, ⟨st2.mem, rg7, st2.pos⟩, sg', rFull, by omega, ?_, hz2, rfl, rfl, rfl,
    hrep2, hphi2, hCaps2, hRegAt2, hphiBd1, hFrOffReg, ?_⟩
  · rw [hSufSp1Eq] at hsc2Hi
    rw [hmlocLk] at hsc1Hi
    unfold selectRefreshFinalizeSpace; omega
  · simp only [selectRebuildSuffixNoRoomContract, selectRebuildSuffixContract,
      List.getD_cons_zero, List.getD_cons_succ] at hcReb
    rw [hSufCost1Eq] at hcReb
    rw [hmlocLk] at hcPhi
    unfold selectRefreshFinalizeCost; omega

end MinCostFlow.MinRatio
