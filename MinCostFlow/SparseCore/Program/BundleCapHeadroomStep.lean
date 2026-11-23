module

public import MinCostFlow.SparseCore.Program.BundleModelStep
public import MinCostFlow.SparseCore.Program.AssemblyBranchBunValue

/-!
# Bundle manager operations on `bunTableHeadroomRep` (`BundleCapHeadroomStep`)

Lifts every operation of P5's bundle manager (`readParent`, `initSlots`, `bundleStep`,
`bunTable_step_model_runs`, `initOneSlot`, `initNewlyActive`, and `AsmBrBunAt`) to
`bunTableHeadroomRep slotCap vCap eCap k` (`BunRestartIface.lean`), which adds
`bunTableHeadroomInv S m` to `bunTableRep`.

Main results:
1. `bunTableHeadroomInv_tableAfterStepRuns`: `tableAfterStepRuns` preserves `bunTableHeadroomInv`
   under `BundleStepReady`.
2. `bunTableHeadroom_readParent_runs`, `bunTableHeadroom_initSlots_runs`,
   `bunTableHeadroom_initOneSlot_runs`, `bunTableHeadroom_initNewlyActive_runs`: `readParent` and
   slot initialization (with `4 * m_s ≤ cap`) establish and preserve `bunTableHeadroomRep`.
3. `bunTableHeadroom_step_runs`, `bunTableHeadroom_step_model_runs_on`,
   `bunTableHeadroom_step_model_runs`: the step requires **no `hcap_ok` hypothesis** — it
   discharges `hcap_ok` directly from `bunTableHeadroomRep` via
   `bunTableHeadroomInv_implies_hcap_ok` and preserves `bunTableHeadroomRep` across the step.
4. `asmBrBunAt_of_bunRestart_headroom`: P5's restart satisfies `AsmBrBunAt` with
   `B5 := fun k slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap k`, with the exact same
   multiplier `asmBrBunMul TS cT` and linear space `brSpaceC TS cT · (x + 1)`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart

public section

/-! ## 1. `tableAfterStepRuns` preserves `bunTableHeadroomInv` -/

/-- Under `BundleTableRepAt` and `BundleStepReady`, `tableAfterStepRuns` preserves
`bunTableHeadroomInv`. -/
theorem bunTableHeadroomInv_tableAfterStepRuns {slotCap vCap eCap tbl : ℕ}
    {cs : CompLSFState} {k : ℕ} {ord ord' : ℕ → List End} {U : List Update}
    {S₀ : BundleTableState slotCap} {m : BundleTableMeta slotCap} {mem : ℕ → ℕ}
    (hrep : BundleTableRepAt slotCap vCap eCap tbl S₀ m mem)
    (hH₀ : bunTableHeadroomInv S₀ m)
    (hready : ∀ j B₀, S₀ j = some B₀ → BundleStepReady cs B₀ k ord ord' U) :
    bunTableHeadroomInv (tableAfterStepRuns cs k ord' U S₀) m := by
  intro j B p bunCap hSj hm
  unfold tableAfterStepRuns at hSj
  cases hS₀ : S₀ j with
  | none => simp [hS₀] at hSj
  | some B₀ =>
    simp only [hS₀, Option.map_some, Option.some.injEq] at hSj
    subst hSj
    have hslot := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j
    simp only [hS₀, hm] at hslot
    obtain ⟨nB, hV, -, -, hlive, -⟩ := hslot.2.1
    exact bunCapHeadroomInv_bundleRunsStep (hready j B₀ hS₀) (hH₀ j B₀ p bunCap hS₀ hm)
      (fun x hx => by rw [hV, Finset.mem_range]; exact hlive x hx)

/-! ## 2. `readParent` and `initSlots` on `bunTableHeadroomRep` -/

/-- `readParent` on `bunTableHeadroomRep`, preserving `bunTableHeadroomInv` with zero potential
change. -/
theorem bunTableHeadroom_readParent_runs {TS : BundleTourSpec} {w slotCap vCap eCap k : ℕ}
    {p : Program} {b bTourList bTourLen bTourOwner : ℕ}
    (hp : p.HasAt b (bundleProcs b bTourList bTourLen bTourOwner))
    (htour : BundleTourAt TS w vCap eCap p bTourList bTourLen bTourOwner)
    {tbl tourH bun h : ℕ} {j : Fin slotCap} {S : BundleTableState slotCap}
    {m : BundleTableMeta slotCap} {B : BundleState} {cord : ℕ → List End}
    {tx : htour.rep.τ} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w) (hvCap : vCap < 2 ^ w)
    (htblFit : tbl + bundleTableFixedSize slotCap eCap < 2 ^ w) (htourH : tourH < 2 ^ w)
    (hhSpace : h + TS.querySpace < 2 ^ w) (hzero : ZeroFrom mem h)
    (hfootB : ∀ a, (bunTableHeadroomRep slotCap vCap eCap k).foot tbl m a → a < h)
    (hfootT : ∀ a, htour.rep.foot tourH tx a → a < h)
    (hdisjBT : ∀ a, (bunTableHeadroomRep slotCap vCap eCap k).foot tbl m a → ¬ htour.rep.foot tourH tx a)
    (hrepB : (bunTableHeadroomRep slotCap vCap eCap k).rep tbl S m mem)
    (hrepT : htour.rep.rep tourH cord tx mem)
    (hinv : bunRestartInv vCap eCap S cord)
    (hSj : S j = some B) (hbun : bun ∈ B.vertices) :
    ∃ body, p.procs[b + bundleIdxReadParent]? = some body ∧ ∃ o st' c tx',
      Runs w p ω body (startState [tbl, tourH, j.1, bun, h] mem pos) o st' c ∧
      (bunTableHeadroomRep slotCap vCap eCap k).rep tbl S m st'.mem ∧
      htour.rep.rep tourH cord tx' st'.mem ∧
      bunRestartInv vCap eCap S cord ∧
      st'.mem h = B.parent bun ∧
      h + 1 ≤ o.value ∧ o.value ≤ h + TS.querySpace ∧ ZeroFrom st'.mem o.value ∧
      (∀ a < h, ¬ htour.rep.foot tourH tx a → st'.mem a = mem a) ∧
      (∀ a, htour.rep.foot tourH tx' a → htour.rep.foot tourH tx a ∨ (h ≤ a ∧ a < o.value)) ∧
      c + (bunTableHeadroomRep slotCap vCap eCap k).phi tbl m st'.mem + htour.rep.phi tourH tx' st'.mem ≤
        TS.mul * ordStoreLog eCap + 60 +
        (bunTableHeadroomRep slotCap vCap eCap k).phi tbl m mem + htour.rep.phi tourH tx mem := by
  obtain ⟨body, hbody, o, st', c, tx', hrun, hrepB', hrepT', hinv', hval, hlo, hhi, hzf, hfr, hft, hc⟩ :=
    bunTable_readParent_runs hp htour hw16 hvCap htblFit htourH hhSpace hzero
      hfootB hfootT hdisjBT ⟨hrepB.1, hrepB.2.1⟩ hrepT hinv hSj hbun
  exact ⟨body, hbody, o, st', c, tx', hrun, ⟨hrepB'.1, hrepB'.2, hrepB.2.2⟩, hrepT', hinv',
    hval, hlo, hhi, hzf, hfr, hft, hc⟩

/-- Multi-slot initialization on `bunTableHeadroomRep`: every newly allocated slot receives
`bunCap ≥ 4 * |(slotEdgesOf assigns s)|`, establishing and preserving `bunTableHeadroomInv`. -/
theorem bunTableHeadroom_initSlots_runs {TS : BundleTourSpec} {w slotCap vCap eCap tbl tourH k nSlots
    slotSpecPtr nEdges edgeAssignPtr nR rPtr h : ℕ}
    {p : Program} {b bTourList bTourLen bTourOwner : ℕ}
    (hp : p.HasAt b (bundleProcs b bTourList bTourLen bTourOwner))
    (htour : BundleTourAt TS w vCap eCap p bTourList bTourLen bTourOwner)
    {S₀ : BundleTableState slotCap} {m₀ : BundleTableMeta slotCap}
    {mem₀ : ℕ → ℕ} {pos₀ : ℕ} {tx₀ : htour.rep.τ} {ω : ℕ → Bool}
    {specs assigns : List (ℕ × ℕ)} {cord : ℕ → List End} {rList : List ℕ}
    (hw16 : 16 ≤ 2 ^ w) (hk1 : 1 ≤ k)
    (htourH_w : tourH < 2 ^ w)
    (htbl_h : tbl + bundleTableFixedSize slotCap eCap ≤ h)
    (hfoot0_lt : ∀ a, (bunTableHeadroomRep slotCap vCap eCap k).foot tbl m₀ a → a < h)
    (hspec_h : slotSpecPtr + 2 * nSlots ≤ h)
    (hspec_disj_tbl : slotSpecPtr + 2 * nSlots ≤ tbl ∨
      tbl + bundleTableFixedSize slotCap eCap ≤ slotSpecPtr)
    (hassign_h : edgeAssignPtr + 2 * nEdges ≤ h)
    (hassign_disj_tbl : edgeAssignPtr + 2 * nEdges ≤ tbl ∨
      tbl + bundleTableFixedSize slotCap eCap ≤ edgeAssignPtr)
    (hrPtr_h : rPtr + nR ≤ h)
    (hrPtr_disj_tbl : rPtr + nR ≤ tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ rPtr)
    (hspace_w : h + bundleInitSlotsSpace TS specs cord rList < 2 ^ w)
    (hrep0 : (bunTableHeadroomRep slotCap vCap eCap k).rep tbl S₀ m₀ mem₀)
    (hinv0 : bunRestartInv vCap eCap S₀ cord)
    (hzero0 : ZeroFrom mem₀ h)
    (htour_rep : htour.rep.rep tourH cord tx₀ mem₀)
    (htour_foot_lt : ∀ a, htour.rep.foot tourH tx₀ a → a < h)
    (htour_foot_disj_tbl : ∀ a, htour.rep.foot tourH tx₀ a →
      a < tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ a)
    (htour_foot_disj_blocks : ∀ a, htour.rep.foot tourH tx₀ a →
      ∀ j : Fin slotCap, ∀ ptr c, m₀.slotBlocks j = some (ptr, c) →
        a < ptr ∨ ptr + bundleSlotBlockSize c ≤ a)
    (htour_foot_disj_spec : ∀ a, htour.rep.foot tourH tx₀ a →
      a < slotSpecPtr ∨ slotSpecPtr + 2 * nSlots ≤ a)
    (htour_foot_disj_r : ∀ a, htour.rep.foot tourH tx₀ a → a < rPtr ∨ rPtr + nR ≤ a)
    (hnSlots : specs.length = nSlots) (hspecs_mem : bundleReadPairs mem₀ slotSpecPtr nSlots = specs)
    (hspecs_lt : ∀ sb ∈ specs, sb.1 < slotCap) (hspecs_nd : (specs.map Prod.fst).Nodup)
    (hspecs_empty : ∀ sb ∈ specs, ∀ hlt : sb.1 < slotCap, S₀ ⟨sb.1, hlt⟩ = none)
    (hspecs_cap4 : ∀ sb ∈ specs, 4 * (slotEdgesOf assigns sb.1).card ≤ sb.2)
    (hnEdges : assigns.length = nEdges) (hassigns_mem : bundleReadPairs mem₀ edgeAssignPtr nEdges = assigns)
    (hassigns_in : ∀ es ∈ assigns, es.1 < eCap ∧ es.2 ∈ specs.map Prod.fst)
    (hassigns_nd : (assigns.map Prod.fst).Nodup)
    (hassigns_fresh : ∀ es ∈ assigns, ∀ j : Fin slotCap, ∀ B, S₀ j = some B → es.1 ∉ B.edges)
    (hnEdges_w : nEdges < 2 ^ w) (hnR : rList.length = nR) (hrList_mem : ListAt mem₀ rPtr rList)
    (hrList_lt : ∀ v ∈ rList, v < vCap ∧ v < 2 ^ w) (hrList_nd : rList.Nodup)
    (hcord_nd : ∀ v ∈ rList, (cord v).Nodup)
    (hcov : ∀ es ∈ assigns, ∀ side : Bool, ∃ v ∈ rList, (es.1, side) ∈ cord v) :
    let S' := tableAfterInitSlots S₀ specs assigns cord rList k
    let m' := allocSlotBlocksMeta m₀ specs h
    let args := [tbl, tourH, nSlots, slotSpecPtr, nEdges, edgeAssignPtr, nR, rPtr, h]
    ∃ body, p.procs[b + bundleIdxInitSlots]? = some body ∧ ∃ st' c hEnd tx',
      Runs w p ω body (startState args mem₀ pos₀) (.returned hEnd) st' c ∧
      h + slotBlocksSpace specs ≤ hEnd ∧
      hEnd ≤ h + bundleInitSlotsSpace TS specs cord rList ∧
      ZeroFrom st'.mem hEnd ∧
      (bunTableHeadroomRep slotCap vCap eCap k).rep tbl S' m' st'.mem ∧
      bunRestartInv vCap eCap S' cord ∧
      htour.rep.rep tourH cord tx' st'.mem ∧
      (∀ a, (bunTableHeadroomRep slotCap vCap eCap k).foot tbl m' a →
        (bunTableHeadroomRep slotCap vCap eCap k).foot tbl m₀ a ∨ (h ≤ a ∧ a < h + slotBlocksSpace specs)) ∧
      (∀ a, htour.rep.foot tourH tx' a →
        htour.rep.foot tourH tx₀ a ∨ (h + slotBlocksSpace specs ≤ a ∧ a < hEnd)) ∧
      (∀ a, a < h → ¬ (bunTableHeadroomRep slotCap vCap eCap k).foot tbl m₀ a →
        ¬ htour.rep.foot tourH tx₀ a → st'.mem a = mem₀ a) ∧
      c + (bunTableHeadroomRep slotCap vCap eCap k).phi tbl m' st'.mem + htour.rep.phi tourH tx' st'.mem ≤
        bundleInitSlotsCost TS eCap nSlots nEdges cord rList + bunPhiMul * (2 * nEdges) +
        (bunTableHeadroomRep slotCap vCap eCap k).phi tbl m₀ mem₀ + htour.rep.phi tourH tx₀ mem₀ := by
  intro S' m' args
  have hspecs_cap : ∀ sb ∈ specs,
      (initPrefixSlots cord rList (slotEdgesOf assigns sb.1) k).length ≤ sb.2 := fun sb hsb =>
    (initPrefixSlots_length_le hk1 hrList_nd hcord_nd hinv0.1.1).trans (by
      have := hspecs_cap4 sb hsb; omega)
  obtain ⟨body, hbody, st', c, hEnd, tx', hrun, hhLo, hhHi, hzf, hrep', hinv', htr',
    hfootB', hfootT', hfr, hc⟩ :=
    bunTable_initSlots_runs hp htour hw16 hk1 htourH_w htbl_h hfoot0_lt hspec_h hspec_disj_tbl
      hassign_h hassign_disj_tbl hrPtr_h hrPtr_disj_tbl hspace_w ⟨hrep0.1, hrep0.2.1⟩ hinv0
      hzero0 htour_rep htour_foot_lt htour_foot_disj_tbl htour_foot_disj_blocks
      htour_foot_disj_spec htour_foot_disj_r hnSlots hspecs_mem hspecs_lt hspecs_nd hspecs_empty
      hspecs_cap hnEdges hassigns_mem hassigns_in hassigns_nd hassigns_fresh hnEdges_w hnR
      hrList_mem hrList_lt hrList_nd hcord_nd hcov
  have hH' : bunTableHeadroomInv S' m' :=
    bunTableHeadroomInv_initSlots hrep0.2.2 hk1 hspecs_nd hrList_nd hcord_nd hinv0.1.1 hcov hspecs_cap4
  exact ⟨body, hbody, st', c, hEnd, tx', hrun, hhLo, hhHi, hzf, ⟨hrep'.1, hrep'.2, hH'⟩,
    hinv', htr', hfootB', hfootT', hfr, hc⟩

/-! ## 3. Three-phase `bundleStep` on `bunTableHeadroomRep` (no `hcap_ok` hypothesis) -/

/-- Three-phase `bundleStep` on `bunTableHeadroomRep`: discharges `hcap_ok` automatically from the
table representation (`bunTableHeadroomInv_implies_hcap_ok`) and preserves `bunTableHeadroomRep`. -/
theorem bunTableHeadroom_step_runs {TS : BundleTourSpec}
    {w slotCap vCap eCap k tbl tourH delCount delPtr groupPtr outDescPtr h₀ pos : ℕ}
    {p : Program} {b bTourList bTourLen bTourOwner : ℕ} {ω : ℕ → Bool}
    (hp : p.HasAt b (bundleProcs b bTourList bTourLen bTourOwner))
    (htour : BundleTourAt TS w vCap eCap p bTourList bTourLen bTourOwner)
    {S₀ : BundleTableState slotCap} {m : BundleTableMeta slotCap}
    {dels : List (ℕ × ℕ × ℕ)} {gs : List (List ℕ)}
    {cord' : ℕ → List End} {src' : End → ℕ} {tx₀ : htour.rep.τ} {mem₀ : ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w) (htourH_w : tourH < 2 ^ w)
    (hpk_w : vCap * (2 * eCap) < 2 ^ w)
    (htbl_w : tbl + bundleTableFixedSize slotCap eCap < 2 ^ w)
    (hblks_w : ∀ js : Fin slotCap, ∀ q c, m.slotBlocks js = some (q, c) →
      q + bundleSlotBlockSize c < 2 ^ w)
    (hdel_w : delPtr + 3 * delCount < 2 ^ w)
    (hgrp_w : groupPtr + groupsWords gs < 2 ^ w)
    (hout_w : outDescPtr + 1 + 3 * slotCap < 2 ^ w)
    (hfoot_lt : ∀ a, (bunTableHeadroomRep slotCap vCap eCap k).foot tbl m a → a < h₀)
    (hdel_lt : delPtr + 3 * delCount ≤ h₀)
    (hgrp_lt : groupPtr + groupsWords gs ≤ h₀)
    (hout_lt : outDescPtr + 1 + 3 * slotCap ≤ h₀)
    (hdel_disj_foot : ∀ a, delPtr ≤ a → a < delPtr + 3 * delCount →
      ¬ (bunTableHeadroomRep slotCap vCap eCap k).foot tbl m a)
    (hgrp_disj_foot : ∀ a, groupPtr ≤ a → a < groupPtr + groupsWords gs →
      ¬ (bunTableHeadroomRep slotCap vCap eCap k).foot tbl m a)
    (hout_disj_foot : ∀ a, outDescPtr ≤ a → a < outDescPtr + 1 + 3 * slotCap →
      ¬ (bunTableHeadroomRep slotCap vCap eCap k).foot tbl m a)
    (htfoot_lt : ∀ a, htour.rep.foot tourH tx₀ a → a < h₀)
    (htfoot_disj_tbl : ∀ a, htour.rep.foot tourH tx₀ a →
      ¬ (bunTableHeadroomRep slotCap vCap eCap k).foot tbl m a)
    (htfoot_disj_grp : ∀ a, htour.rep.foot tourH tx₀ a → a < groupPtr ∨ groupPtr + groupsWords gs ≤ a)
    (htfoot_disj_out : ∀ a, htour.rep.foot tourH tx₀ a → a < outDescPtr ∨ outDescPtr + 1 + 3 * slotCap ≤ a)
    (hzero : ZeroFrom mem₀ h₀)
    (htrep : htour.rep.rep tourH cord' tx₀ mem₀)
    (hrep0 : (bunTableHeadroomRep slotCap vCap eCap k).rep tbl S₀ m mem₀)
    (hdels_len : dels.length = delCount)
    (hdels_mem : readDelTriples mem₀ delPtr delCount = dels)
    (hdels_lt : ∀ tr ∈ dels, tr.1 < eCap ∧ tr.2.1 < 2 ^ w ∧ tr.2.2 < 2 ^ w)
    (hdels_par : ∀ i (hi : i < dels.length), dels[i].1 ∉ delPrefixSet dels i →
      ∀ (j : Fin slotCap) (B : BundleState), S₀ j = some B →
        dels[i].1 ∈ B.edges →
        dels[i].2.1 = B.parent (B.bundleOf (dels[i].1, true)) ∧
        dels[i].2.2 = B.parent (B.bundleOf (dels[i].1, false)))
    (hgs_mem : readGroups mem₀ groupPtr gs.length = gs)
    (hgs_pos : ∀ G ∈ gs, 0 < G.length)
    (hgs_lt : ∀ G ∈ gs, ∀ v ∈ G, v < vCap ∧ v < 2 ^ w)
    (hgs_nodup : ∀ G ∈ gs, G.Nodup)
    (hgs_disj : ∀ i (hi : i < gs.length) j (hj : j < gs.length), i ≠ j →
      Disjoint gs[i].toFinset gs[j].toFinset)
    (hgs_ends_lt : ∀ G ∈ gs, ∀ v ∈ G, ∀ x ∈ cord' v, x.1 < eCap)
    (hgs_nd : ∀ G ∈ gs, ∀ v ∈ G, (cord' v).Nodup)
    (hsrc_lt : ∀ j : Fin slotCap, ∀ B₀, S₀ j = some B₀ →
      ∀ x ∈ edgeEnds (B₀.edges \ (dels.map Prod.fst).toFinset), src' x < vCap)
    (hsrc_mem : ∀ j : Fin slotCap, ∀ B₀, S₀ j = some B₀ →
      ∀ x ∈ edgeEnds (B₀.edges \ (dels.map Prod.fst).toFinset), x ∈ cord' (src' x))
    (hsrc_uniq : ∀ j : Fin slotCap, ∀ B₀, S₀ j = some B₀ →
      ∀ x ∈ edgeEnds (B₀.edges \ (dels.map Prod.fst).toFinset), ∀ v', x ∈ cord' v' → v' = src' x)
    (hbundle_in_group : ∀ j B₀, S₀ j = some B₀ → ∀ bun ∈ B₀.vertices,
      2 ≤ (finalRootsOf B₀ (B₀.edges \ (dels.map Prod.fst).toFinset) src' bun).card →
        ∃ gi, ∃ (hgi : gi < gs.length),
          ∀ x ∈ survivingEnds B₀ (B₀.edges \ (dels.map Prod.fst).toFinset) bun,
            src' x ∈ gs[gi].toFinset)
    (hh_sp : ∀ (maxIdxs : List ℕ) (touched : List ℕ),
      maxIdxs.length = gs.length →
      (∀ gi (hgi : gi < gs.length), maxIdxs.getD gi 0 < gs[gi].length) →
      touched.Nodup → (∀ s ∈ touched, s < slotCap) →
      let candSet := addCandsForGroups (tableDelEdges S₀ (dels.map Prod.fst).toFinset)
        cord' gs maxIdxs (fun _ => ∅) gs.length
      let scanLen := slotScannedEnds S₀ (dels.map Prod.fst).toFinset cord' gs maxIdxs
      h₀ + bundleStepSpace TS S₀ (dels.map Prod.fst).toFinset candSet scanLen cord' gs touched < 2 ^ w) :
    let D := (dels.map Prod.fst).toFinset
    let S_del := tableDelEdges S₀ D
    ∃ body, p.procs[b + bundleIdxStep]? = some body ∧ ∃ st' c h' tx' maxIdxs touched,
      let candSet := addCandsForGroups S_del cord' gs maxIdxs (fun _ => ∅) gs.length
      let scanLen := slotScannedEnds S₀ D cord' gs maxIdxs
      let S_final := tableAfterStep S₀ D src' candSet
      Runs w p ω body
        (startState [tbl, tourH, delCount, delPtr, gs.length, groupPtr, outDescPtr, h₀] mem₀ pos)
        (.returned h') st' c ∧
      maxIdxs.length = gs.length ∧
      (∀ gi (hgi : gi < gs.length), ∃ hm : maxIdxs.getD gi 0 < gs[gi].length,
        ∀ j (hj : j < gs[gi].length), (cord' gs[gi][j]).length ≤ (cord' gs[gi][maxIdxs.getD gi 0]).length) ∧
      touched.Nodup ∧ (∀ s ∈ touched, s < slotCap) ∧
      (∀ j : Fin slotCap, match S₀ j with
        | none => j.1 ∉ touched
        | some B₀ => j.1 ∈ touched ↔ (B₀.edges ∩ D).Nonempty ∨ (candSet j).Nonempty) ∧
      h₀ ≤ h' ∧ h' ≤ h₀ + bundleStepSpace TS S₀ D candSet scanLen cord' gs touched ∧
      ZeroFrom st'.mem h' ∧
      htour.rep.rep tourH cord' tx' st'.mem ∧
      (∀ a, htour.rep.foot tourH tx' a → htour.rep.foot tourH tx₀ a ∨ (h₀ ≤ a ∧ a < h')) ∧
      (bunTableHeadroomRep slotCap vCap eCap k).rep tbl S_final m st'.mem ∧
      st'.mem outDescPtr = touched.length ∧
      (∀ i (hi : i < touched.length),
        let s := touched[i]'hi
        ∃ (hs : s < slotCap) (batchPtr totalWords : ℕ),
          st'.mem (outDescPtr + 1 + 3 * i) = s ∧
          st'.mem (outDescPtr + 1 + 3 * i + 1) = batchPtr ∧
          st'.mem (outDescPtr + 1 + 3 * i + 2) = totalWords ∧
          h₀ ≤ batchPtr ∧ batchPtr + totalWords ≤ h' ∧
          ∀ B₀, S₀ ⟨s, hs⟩ = some B₀ →
            SmallBatchAt st'.mem batchPtr B₀.graph (slotBatchOf S₀ D src' candSet ⟨s, hs⟩) totalWords ∧
            ∃ lens, lens.length = (slotBatchOf S₀ D src' candSet ⟨s, hs⟩).length ∧
              lens.sum = totalWords - 1 ∧
              BatchBodyLensAt st'.mem (batchPtr + 1) B₀.graph
                (slotBatchOf S₀ D src' candSet ⟨s, hs⟩) lens) ∧
      (∀ a < h₀, ¬ (bunTableHeadroomRep slotCap vCap eCap k).foot tbl m a →
        (a < outDescPtr ∨ outDescPtr + 1 + 3 * slotCap ≤ a) →
        ¬ htour.rep.foot tourH tx₀ a → st'.mem a = mem₀ a) ∧
      c + 70 * touched.length + (bunTableHeadroomRep slotCap vCap eCap k).phi tbl m st'.mem + htour.rep.phi tourH tx' st'.mem ≤
        bundleStepCost TS eCap delCount gs +
        bunPhiMul * (∑ j : Fin slotCap, batchSplitCount (slotBatchOf S₀ D src' candSet j)) +
        bundleScanPotMul TS eCap * totalNonMaxLen cord' gs maxIdxs +
        (bunTableHeadroomRep slotCap vCap eCap k).phi tbl m mem₀ + htour.rep.phi tourH tx₀ mem₀ := by
  intro D S_del
  have hcap_ok := bunTableHeadroomInv_implies_scanned_hcap_ok (D := D) (cord' := cord') (src' := src')
    (gs := gs) hrep0.2.2 hgs_nodup hgs_disj hgs_nd
    (fun j B₀ hS₀ x hx w => ⟨fun hxw => (hsrc_uniq j B₀ hS₀ x hx w hxw).symm,
      fun h => h ▸ hsrc_mem j B₀ hS₀ x hx⟩)
    hbundle_in_group
  obtain ⟨body, hbody, st', c, h', tx', maxIdxs, touched, hrun, hmaxLen, hmaxSpec,
    hndT, hltT, htouchIff, hhLo, hhHi, hzf, htr', htf', hrep', hout0, hdescs, hfr, hc⟩ :=
    bunTable_step_runs hp htour hw16 htourH_w hpk_w htbl_w hblks_w hdel_w hgrp_w hout_w
      hfoot_lt hdel_lt hgrp_lt hout_lt hdel_disj_foot hgrp_disj_foot hout_disj_foot
      htfoot_lt htfoot_disj_tbl htfoot_disj_grp htfoot_disj_out hzero htrep ⟨hrep0.1, hrep0.2.1⟩
      hdels_len hdels_mem hdels_lt hdels_par hgs_mem hgs_pos hgs_lt hgs_nodup hgs_disj
      hgs_ends_lt hgs_nd hsrc_lt hsrc_mem hsrc_uniq hbundle_in_group hcap_ok hh_sp
  set candSet := addCandsForGroups S_del cord' gs maxIdxs (fun _ => ∅) gs.length
  have hcand_inV : ∀ j : Fin slotCap, ∀ B₀, S₀ j = some B₀ → ∀ b ∈ candSet j, b ∈ B₀.vertices := by
    intro j B₀ hS0 b hb
    have hSj : S_del j = some { B₀ with edges := B₀.edges \ D } := by simp [S_del, tableDelEdges, hS0]
    rcases (mem_addCandsForGroups_iff hSj hgs_nd gs.length (le_refl _) b).mp hb with h0 | ⟨hbV, _⟩
    · cases h0
    · exact hbV
  have hH' := bunTableHeadroomInv_tableAfterStep (D := D) (src' := src') hrep0.1 hrep0.2.2 hcand_inV
  exact ⟨body, hbody, st', c, h', tx', maxIdxs, touched, hrun, hmaxLen, hmaxSpec,
    hndT, hltT, htouchIff, hhLo, hhHi, hzf, htr', htf', ⟨hrep'.1, hrep'.2, hH'⟩,
    hout0, hdescs, hfr, hc⟩

/-- Model-level step on `bunTableHeadroomRep` for any tracked set `P` — **no `hcap_ok` hypothesis**. -/
theorem bunTableHeadroom_step_model_runs_on {TS : BundleTourSpec} {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {w slotCap vCap eCap tbl tourH delCount delPtr groupPtr outDescPtr h₀ pos : ℕ}
    {p : Program} {b bTourList bTourLen bTourOwner : ℕ} {ω : ℕ → Bool}
    (hp : p.HasAt b (bundleProcs b bTourList bTourLen bTourOwner))
    (htour : BundleTourAt TS w vCap eCap p bTourList bTourLen bTourOwner)
    {tr : BundleTreeState L} {U : List Update} {ord ord' : ℕ → List End}
    {slotOf : Finset ℕ × ℤ → ℕ} {P : Finset (Finset ℕ × ℤ)}
    {S₀ : BundleTableState slotCap} {m : BundleTableMeta slotCap}
    {dels : List (ℕ × ℕ × ℕ)} {gs : List (List ℕ)} {R_old R_new : Finset ℕ} {oldRoots : List ℕ}
    {cord : ℕ → List End} {tx₀ : htour.rep.τ} {mem₀ : ℕ → ℕ}
    (hD_eq : (dels.map Prod.fst).toFinset = batchDeletes U)
    (hinv0 : bunRestartInv vCap eCap S₀ cord)
    (hMatch0 : ∀ q ∈ P, ∃ (hs : slotOf q < slotCap) (B : BundleState),
      S₀ ⟨slotOf q, hs⟩ = some B ∧ BunAgree B (tr.bun q))
    (hready : ∀ j B₀, S₀ j = some B₀ → BundleStepReady tr.cs B₀ tr.k ord ord' U)
    (hcord'_bounds : ∀ v x, x ∈ outCoreOrder (stepBundleTree sparsify tr U ord ord').state ord' v →
      v < vCap ∧ x.1 < eCap)
    (hw16 : 16 ≤ 2 ^ w) (htourH_w : tourH < 2 ^ w)
    (hpk_w : vCap * (2 * eCap) < 2 ^ w)
    (htbl_w : tbl + bundleTableFixedSize slotCap eCap < 2 ^ w)
    (hblks_w : ∀ js : Fin slotCap, ∀ q c, m.slotBlocks js = some (q, c) →
      q + bundleSlotBlockSize c < 2 ^ w)
    (hdel_w : delPtr + 3 * delCount < 2 ^ w)
    (hgrp_w : groupPtr + groupsWords gs < 2 ^ w)
    (hout_w : outDescPtr + 1 + 3 * slotCap < 2 ^ w)
    (hfoot_lt : ∀ a, (bunTableHeadroomRep slotCap vCap eCap tr.k).foot tbl m a → a < h₀)
    (hdel_lt : delPtr + 3 * delCount ≤ h₀)
    (hgrp_lt : groupPtr + groupsWords gs ≤ h₀)
    (hout_lt : outDescPtr + 1 + 3 * slotCap ≤ h₀)
    (hdel_disj_foot : ∀ a, delPtr ≤ a → a < delPtr + 3 * delCount →
      ¬ (bunTableHeadroomRep slotCap vCap eCap tr.k).foot tbl m a)
    (hgrp_disj_foot : ∀ a, groupPtr ≤ a → a < groupPtr + groupsWords gs →
      ¬ (bunTableHeadroomRep slotCap vCap eCap tr.k).foot tbl m a)
    (hout_disj_foot : ∀ a, outDescPtr ≤ a → a < outDescPtr + 1 + 3 * slotCap →
      ¬ (bunTableHeadroomRep slotCap vCap eCap tr.k).foot tbl m a)
    (htfoot_lt : ∀ a, htour.rep.foot tourH tx₀ a → a < h₀)
    (htfoot_disj_tbl : ∀ a, htour.rep.foot tourH tx₀ a →
      ¬ (bunTableHeadroomRep slotCap vCap eCap tr.k).foot tbl m a)
    (htfoot_disj_grp : ∀ a, htour.rep.foot tourH tx₀ a → a < groupPtr ∨ groupPtr + groupsWords gs ≤ a)
    (htfoot_disj_out : ∀ a, htour.rep.foot tourH tx₀ a → a < outDescPtr ∨ outDescPtr + 1 + 3 * slotCap ≤ a)
    (hzero : ZeroFrom mem₀ h₀)
    (htrep : htour.rep.rep tourH (outCoreOrder (stepBundleTree sparsify tr U ord ord').state ord') tx₀ mem₀)
    (hrep0 : (bunTableHeadroomRep slotCap vCap eCap tr.k).rep tbl S₀ m mem₀)
    (hdels_len : dels.length = delCount)
    (hdels_mem : readDelTriples mem₀ delPtr delCount = dels)
    (hdels_lt : ∀ trD ∈ dels, trD.1 < eCap ∧ trD.2.1 < 2 ^ w ∧ trD.2.2 < 2 ^ w)
    (hdels_par : ∀ i (hi : i < dels.length), dels[i].1 ∉ delPrefixSet dels i →
      ∀ (j : Fin slotCap) (B : BundleState), S₀ j = some B →
        dels[i].1 ∈ B.edges →
        dels[i].2.1 = B.parent (B.bundleOf (dels[i].1, true)) ∧
        dels[i].2.2 = B.parent (B.bundleOf (dels[i].1, false)))
    (hgs_mem : readGroups mem₀ groupPtr gs.length = gs)
    (hgs_pos : ∀ G ∈ gs, 0 < G.length)
    (hgs_lt : ∀ G ∈ gs, ∀ v ∈ G, v < vCap ∧ v < 2 ^ w)
    (hgs_nd : ∀ G ∈ gs, G.Nodup)
    (hgs_sub : ∀ G ∈ gs, ∀ v ∈ G, v ∈ R_new)
    (hgs_disj : ∀ i (hi : i < gs.length) j (hj : j < gs.length), i ≠ j →
      Disjoint gs[i].toFinset gs[j].toFinset)
    (hold_len : oldRoots.length = gs.length)
    (hold_nd : oldRoots.Nodup)
    (hold_sub : ∀ r ∈ oldRoots, r ∈ R_old)
    {addG : ℕ → ℕ} {addR : ℕ → ℕ} {maxLen : ℕ}
    (hgroup_sum_le : ∀ gi (hgi : gi < gs.length),
      (∑ v ∈ gs[gi].toFinset, (outCoreOrder (stepBundleTree sparsify tr U ord ord').state ord' v).length) ≤
        (cord (oldRoots[gi]'(by omega))).length + addG gi ∧
      (cord (oldRoots[gi]'(by omega))).length + addG gi ≤ maxLen)
    (hrest_le : ∀ r ∈ R_new, (∀ gi (hgi : gi < gs.length), r ∉ gs[gi].toFinset) →
      r ∈ R_old ∧ r ∉ oldRoots ∧
        (outCoreOrder (stepBundleTree sparsify tr U ord ord').state ord' r).length ≤ (cord r).length + addR r ∧
        (cord r).length + addR r ≤ maxLen)
    (hbundle_in_group : ∀ j B₀, S₀ j = some B₀ → ∀ bun ∈ B₀.vertices,
      2 ≤ (finalRootsOf B₀ (B₀.edges \ batchDeletes U)
        (coreGraph (compLSFBatch tr.cs U).G (compLSFBatch tr.cs U).lsf).src bun).card →
        ∃ gi, ∃ (hgi : gi < gs.length),
          ∀ x ∈ survivingEnds B₀ (B₀.edges \ batchDeletes U) bun,
            (coreGraph (compLSFBatch tr.cs U).G (compLSFBatch tr.cs U).lsf).src x ∈ gs[gi].toFinset)
    (hh_sp : ∀ (maxIdxs : List ℕ) (touched : List ℕ),
      maxIdxs.length = gs.length →
      (∀ gi (hgi : gi < gs.length), maxIdxs.getD gi 0 < gs[gi].length) →
      touched.Nodup → (∀ s ∈ touched, s < slotCap) →
      let cord' := outCoreOrder (stepBundleTree sparsify tr U ord ord').state ord'
      let candSet := addCandsForGroups (tableDelEdges S₀ (batchDeletes U)) cord' gs maxIdxs (fun _ => ∅) gs.length
      let scanLen := slotScannedEnds S₀ (batchDeletes U) cord' gs maxIdxs
      h₀ + bundleStepSpace TS S₀ (batchDeletes U) candSet scanLen cord' gs touched < 2 ^ w) :
    let info := stepBundleTree sparsify tr U ord ord'
    let cord' := outCoreOrder info.state ord'
    let S' := tableAfterStepRuns tr.cs tr.k ord' U S₀
    let U_grp := (Finset.range gs.length).biUnion fun gi => (gs.getD gi []).toFinset
    let totalAdded := (∑ gi ∈ Finset.range gs.length, addG gi) + ∑ r ∈ R_new \ U_grp, addR r
    ∃ body, p.procs[b + bundleIdxStep]? = some body ∧ ∃ st' c h' tx' maxIdxs touched,
      let candSet := addCandsForGroups (tableDelEdges S₀ (batchDeletes U)) cord' gs maxIdxs (fun _ => ∅) gs.length
      let scanLen := slotScannedEnds S₀ (batchDeletes U) cord' gs maxIdxs
      Runs w p ω body
        (startState [tbl, tourH, delCount, delPtr, gs.length, groupPtr, outDescPtr, h₀] mem₀ pos)
        (.returned h') st' c ∧
      (bunTableHeadroomRep slotCap vCap eCap tr.k).rep tbl S' m st'.mem ∧
      htour.rep.rep tourH cord' tx' st'.mem ∧
      bunRestartInv vCap eCap S' cord' ∧
      (∀ q ∈ P, ∃ (hs : slotOf q < slotCap) (B' : BundleState),
        S' ⟨slotOf q, hs⟩ = some B' ∧ BunAgree B' (info.state.bun q)) ∧
      h₀ ≤ h' ∧ h' ≤ h₀ + bundleStepSpace TS S₀ (batchDeletes U) candSet scanLen cord' gs touched ∧
      ZeroFrom st'.mem h' ∧
      (∀ a, htour.rep.foot tourH tx' a → htour.rep.foot tourH tx₀ a ∨ (h₀ ≤ a ∧ a < h')) ∧
      st'.mem outDescPtr = touched.length ∧
      (∀ i (hi : i < touched.length),
        let s := touched[i]'hi
        ∃ (hs : s < slotCap) (batchPtr totalWords : ℕ),
          st'.mem (outDescPtr + 1 + 3 * i) = s ∧
          st'.mem (outDescPtr + 1 + 3 * i + 1) = batchPtr ∧
          st'.mem (outDescPtr + 1 + 3 * i + 2) = totalWords ∧
          h₀ ≤ batchPtr ∧ batchPtr + totalWords ≤ h' ∧
          ∀ B₀, S₀ ⟨s, hs⟩ = some B₀ →
            SmallBatchAt st'.mem batchPtr B₀.graph (bundleCompStep tr.cs B₀ tr.k ord ord' U).1 totalWords) ∧
      (∀ a < h₀, ¬ (bunTableHeadroomRep slotCap vCap eCap tr.k).foot tbl m a →
        (a < outDescPtr ∨ outDescPtr + 1 + 3 * slotCap ≤ a) →
        ¬ htour.rep.foot tourH tx₀ a → st'.mem a = mem₀ a) ∧
      c + 70 * touched.length + (bunTableHeadroomRep slotCap vCap eCap tr.k).phi tbl m st'.mem +
          bundleScanPotMul TS eCap * tourPot R_new cord' + htour.rep.phi tourH tx' st'.mem ≤
        bundleStepCost TS eCap delCount gs +
        bunPhiMul * (∑ j : Fin slotCap, match S₀ j with
          | none => 0
          | some B₀ => batchSplitCount (bundleCompStep tr.cs B₀ tr.k ord ord' U).1) +
        (bunTableHeadroomRep slotCap vCap eCap tr.k).phi tbl m mem₀ +
        bundleScanPotMul TS eCap * (tourPot R_old cord + totalAdded * (Nat.log 2 maxLen + 2)) +
        htour.rep.phi tourH tx₀ mem₀ := by
  intro info cord' S' U_grp totalAdded
  set src' := (coreGraph (compLSFBatch tr.cs U).G (compLSFBatch tr.cs U).lsf).src
  have hcord'_nd : ∀ v, (cord' v).Nodup := fun v => by
    unfold cord' outCoreOrder
    split_ifs with hex
    · exact (coreRotation (L := info.state.cs.lsf)
        hex.choose_spec.choose_spec.choose_spec.choose
        hex.choose_spec.choose_spec.choose.hG_val
        (compLSF_RF_isRSF hex.choose_spec.choose_spec.choose)).nodup v
    · exact List.nodup_nil
  have hsrc_iff : ∀ j B₀, S₀ j = some B₀ →
      ∀ x ∈ edgeEnds (B₀.edges \ batchDeletes U), ∀ v, x ∈ cord' v ↔ src' x = v := by
    intro j B₀ hS₀ x hx v
    obtain ⟨C_lsst, ℓ₀, hI, ρ, σ, _, hσ, _, hU, _⟩ := hready j B₀ hS₀
    have hI' := compLSFBatch_inv hI hU
    let σ' : Rotation info.state.cs.G := (compLSFBatch_G tr.cs U).symm ▸ σ
    have hσ' : σ'.order = ord' := by
      dsimp only [σ']
      have hcast : ∀ {G H : MGraph} (he : G = H) (τ : Rotation G), (he ▸ τ : Rotation H).order = τ.order := by
        intro G H he τ; cases he; rfl
      exact (hcast _ σ).trans hσ
    have hpart := (bundleRunsStep_spec (hready j B₀ hS₀)).1.1 σ' hI'.hG_val (compLSF_RF_isRSF hI') hσ'
    have hxE : x.1 ∈ (coreGraph info.state.cs.G info.state.cs.lsf).E := by
      have hsub := hpart.1
      have hEeq := (bundleRunsStep_spec (hready j B₀ hS₀)).2.2.2.2.1
      rw [hEeq] at hsub
      exact hsub ((mem_edgeEnds _ _).mp hx)
    exact outCoreOrder_mem_iff_src hI' σ' hσ' hxE v
  have hcap_ok := bunTableHeadroomInv_implies_scanned_hcap_ok (D := batchDeletes U) (cord' := cord')
    (src' := src') (gs := gs) hrep0.2.2 hgs_nd hgs_disj (fun _ _ v _ => hcord'_nd v)
    hsrc_iff hbundle_in_group
  obtain ⟨body, hbody, st', c, h', tx', maxIdxs, touched, hrun, hrep', htr', hinv', hMatch',
    hhLo, hhHi, hzf, htf', hout0, hdescs, hfr, hc⟩ :=
    bunTable_step_model_runs_on hp htour hD_eq hinv0 hMatch0 hready hcord'_bounds
      hw16 htourH_w hpk_w htbl_w hblks_w hdel_w hgrp_w hout_w hfoot_lt hdel_lt hgrp_lt
      hout_lt hdel_disj_foot hgrp_disj_foot hout_disj_foot htfoot_lt htfoot_disj_tbl htfoot_disj_grp
      htfoot_disj_out hzero htrep ⟨hrep0.1, hrep0.2.1⟩ hdels_len hdels_mem hdels_lt hdels_par
      hgs_mem hgs_pos hgs_lt hgs_nd hgs_sub hgs_disj hold_len hold_nd hold_sub hgroup_sum_le
      hrest_le hbundle_in_group hcap_ok hh_sp
  have hH' := bunTableHeadroomInv_tableAfterStepRuns hrep0.1 hrep0.2.2 hready
  exact ⟨body, hbody, st', c, h', tx', maxIdxs, touched, hrun, ⟨hrep'.1, hrep'.2, hH'⟩, htr',
    hinv', hMatch', hhLo, hhHi, hzf, htf', hout0, hdescs, hfr, hc⟩

/-! ## 4. Single-slot and newly-active lazy init on `bunTableHeadroomRep` -/

/-- One-slot lazy init on `bunTableHeadroomRep` with `4 * E.card ≤ cap`. -/
theorem bunTableHeadroom_initOneSlot_runs {TS : BundleTourSpec} {w slotCap vCap eCap tbl tourH k s cap
    slotSpecPtr edgeAssignPtr rPtr h : ℕ}
    {p : Program} {b bTourList bTourLen bTourOwner : ℕ}
    (hp : p.HasAt b (bundleProcs b bTourList bTourLen bTourOwner))
    (htour : BundleTourAt TS w vCap eCap p bTourList bTourLen bTourOwner)
    {cs : CompLSFState} {ord cord : ℕ → List End} {E : Finset ℕ}
    {edges : List ℕ} {rList : List ℕ}
    {S₀ : BundleTableState slotCap} {m₀ : BundleTableMeta slotCap}
    {mem₀ : ℕ → ℕ} {pos₀ : ℕ} {tx₀ : htour.rep.τ} {ω : ℕ → Bool}
    (hs_lt : s < slotCap) (hs_empty : S₀ ⟨s, hs_lt⟩ = none)
    (hw16 : 16 ≤ 2 ^ w) (hk1 : 1 ≤ k) (hcore : CoreCordOf cs ord cord)
    (htourH_w : tourH < 2 ^ w)
    (htbl_h : tbl + bundleTableFixedSize slotCap eCap ≤ h)
    (hfoot0_lt : ∀ a, (bunTableHeadroomRep slotCap vCap eCap k).foot tbl m₀ a → a < h)
    (hspec_h : slotSpecPtr + 2 ≤ h)
    (hspec_disj_tbl : slotSpecPtr + 2 ≤ tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ slotSpecPtr)
    (hassign_h : edgeAssignPtr + 2 * edges.length ≤ h)
    (hassign_disj_tbl : edgeAssignPtr + 2 * edges.length ≤ tbl ∨
      tbl + bundleTableFixedSize slotCap eCap ≤ edgeAssignPtr)
    (hrPtr_h : rPtr + rList.length ≤ h)
    (hrPtr_disj_tbl : rPtr + rList.length ≤ tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ rPtr)
    (hspace_w : h + bundleInitSlotsSpace TS [(s, cap)] cord rList < 2 ^ w)
    (hrep0 : (bunTableHeadroomRep slotCap vCap eCap k).rep tbl S₀ m₀ mem₀)
    (hinv0 : bunRestartInv vCap eCap S₀ cord)
    (hzero0 : ZeroFrom mem₀ h)
    (htour_rep : htour.rep.rep tourH cord tx₀ mem₀)
    (htour_foot_lt : ∀ a, htour.rep.foot tourH tx₀ a → a < h)
    (htour_foot_disj_tbl : ∀ a, htour.rep.foot tourH tx₀ a →
      a < tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ a)
    (htour_foot_disj_blocks : ∀ a, htour.rep.foot tourH tx₀ a →
      ∀ j : Fin slotCap, ∀ ptr c, m₀.slotBlocks j = some (ptr, c) →
        a < ptr ∨ ptr + bundleSlotBlockSize c ≤ a)
    (htour_foot_disj_spec : ∀ a, htour.rep.foot tourH tx₀ a →
      a < slotSpecPtr ∨ slotSpecPtr + 2 ≤ a)
    (htour_foot_disj_r : ∀ a, htour.rep.foot tourH tx₀ a → a < rPtr ∨ rPtr + rList.length ≤ a)
    (hspec_mem : mem₀ slotSpecPtr = s ∧ mem₀ (slotSpecPtr + 1) = cap)
    (hcap_ok : 4 * E.card ≤ cap)
    (hedges_nd : edges.Nodup) (hedges_eq : edges.toFinset = E)
    (hE_sub : E ⊆ (coreGraph cs.G cs.lsf).E)
    (hE_lt : ∀ e ∈ E, e < eCap)
    (hE_fresh : ∀ e ∈ E, ∀ j : Fin slotCap, ∀ B, S₀ j = some B → e ∉ B.edges)
    (hedges_w : edges.length < 2 ^ w)
    (hassigns_mem : bundleReadPairs mem₀ edgeAssignPtr edges.length = edges.map (·, s))
    (hrList_mem : ListAt mem₀ rPtr rList)
    (hrList_lt : ∀ v ∈ rList, v < vCap ∧ v < 2 ^ w)
    (hrList_pw : rList.Pairwise (· < ·))
    (hrList_sub : ∀ v ∈ rList, v ∈ (coreGraph cs.G cs.lsf).V)
    (hcov : ∀ v x, x ∈ cord v → x.1 ∈ E → v ∈ rList) :
    let m' := allocSlotBlocksMeta m₀ [(s, cap)] h
    let args := [tbl, tourH, 1, slotSpecPtr, edges.length, edgeAssignPtr, rList.length, rPtr, h]
    ∃ body, p.procs[b + bundleIdxInitSlots]? = some body ∧ ∃ st' c hEnd tx' B',
      let S' : BundleTableState slotCap := Function.update S₀ ⟨s, hs_lt⟩ (some B')
      Runs w p ω body (startState args mem₀ pos₀) (.returned hEnd) st' c ∧
      (bunTableHeadroomRep slotCap vCap eCap k).rep tbl S' m' st'.mem ∧
      bunRestartInv vCap eCap S' cord ∧
      htour.rep.rep tourH cord tx' st'.mem ∧
      BunAgree B' (initBundleFor cs ord E k) ∧
      (∀ j : Fin slotCap, j ≠ ⟨s, hs_lt⟩ → S' j = S₀ j) ∧
      h + bundleSlotBlockSize cap ≤ hEnd ∧
      hEnd ≤ h + bundleInitSlotsSpace TS [(s, cap)] cord rList ∧
      ZeroFrom st'.mem hEnd ∧
      (∀ a, (bunTableHeadroomRep slotCap vCap eCap k).foot tbl m' a →
        (bunTableHeadroomRep slotCap vCap eCap k).foot tbl m₀ a ∨ (h ≤ a ∧ a < h + bundleSlotBlockSize cap)) ∧
      (∀ a, htour.rep.foot tourH tx' a →
        htour.rep.foot tourH tx₀ a ∨ (h + bundleSlotBlockSize cap ≤ a ∧ a < hEnd)) ∧
      (∀ a, a < h → ¬ (bunTableHeadroomRep slotCap vCap eCap k).foot tbl m₀ a →
        ¬ htour.rep.foot tourH tx₀ a → st'.mem a = mem₀ a) ∧
      c + (bunTableHeadroomRep slotCap vCap eCap k).phi tbl m' st'.mem + htour.rep.phi tourH tx' st'.mem ≤
        bundleInitSlotsCost TS eCap 1 edges.length cord rList + bunPhiMul * (2 * edges.length) +
        (bunTableHeadroomRep slotCap vCap eCap k).phi tbl m₀ mem₀ + htour.rep.phi tourH tx₀ mem₀ := by
  intro m' args
  obtain ⟨body, hbody, st', c, hEnd, tx', B', hrun, hrep', hB'_H, hinv', htr', hag, hother,
    hhLo, hhHi, hzf, hfootB', hfootT', hfr, hc⟩ :=
    bunTable_initOneSlot_runs hp htour hs_lt hs_empty hw16 hk1 hcore htourH_w htbl_h hfoot0_lt
      hspec_h hspec_disj_tbl hassign_h hassign_disj_tbl hrPtr_h hrPtr_disj_tbl hspace_w
      ⟨hrep0.1, hrep0.2.1⟩ hinv0 hzero0 htour_rep htour_foot_lt htour_foot_disj_tbl
      htour_foot_disj_blocks htour_foot_disj_spec htour_foot_disj_r hspec_mem hcap_ok hedges_nd
      hedges_eq hE_sub hE_lt hE_fresh hedges_w hassigns_mem hrList_mem hrList_lt hrList_pw
      hrList_sub hcov
  have hH' : bunTableHeadroomInv (Function.update S₀ ⟨s, hs_lt⟩ (some B')) m' := by
    intro j B p' bunCap hSj hmj
    by_cases hj : j = ⟨s, hs_lt⟩
    · subst hj
      simp only [Function.update_self, Option.some.injEq] at hSj
      subst hSj
      simp only [m', allocSlotBlocksMeta, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hmj
      rw [← hmj.2]; exact hB'_H
    · have hne : j.1 ≠ s := fun h => hj (Fin.ext h)
      rw [Function.update_of_ne hj] at hSj
      simp only [m', allocSlotBlocksMeta, hne, ↓reduceIte] at hmj
      exact hrep0.2.2 j B p' bunCap hSj hmj
  exact ⟨body, hbody, st', c, hEnd, tx', B', hrun, ⟨hrep'.1, hrep'.2, hH'⟩, hinv', htr', hag,
    hother, hhLo, hhHi, hzf, hfootB', hfootT', hfr, hc⟩

/-- Pre-step lazy initialization of one newly active slot on `bunTableHeadroomRep` with
`4 * E.card ≤ cap`. -/
theorem bunTableHeadroom_initNewlyActive_runs {TS : BundleTourSpec} {L : ℕ}
    {w slotCap vCap eCap tbl tourH cap slotSpecPtr edgeAssignPtr rPtr h : ℕ}
    {p : Program} {b bTourList bTourLen bTourOwner : ℕ}
    (hp : p.HasAt b (bundleProcs b bTourList bTourLen bTourOwner))
    (htour : BundleTourAt TS w vCap eCap p bTourList bTourLen bTourOwner)
    {tr : BundleTreeState L} {ord : ℕ → List End}
    {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} (hI : CompLSFInv C_lsst ℓ₀ tr.cs)
    (ρ : Rotation tr.cs.G) (hρ : ρ.order = ord)
    {slotOf : Finset ℕ × ℤ → ℕ} {P : Finset (Finset ℕ × ℤ)} {qNew : Finset ℕ × ℤ}
    {E : Finset ℕ} {edges : List ℕ} {rList : List ℕ}
    {S₀ : BundleTableState slotCap} {m₀ : BundleTableMeta slotCap}
    {mem₀ : ℕ → ℕ} {pos₀ : ℕ} {tx₀ : htour.rep.τ} {ω : ℕ → Bool}
    (hLazy : BunAgree (initBundleFor tr.cs ord E tr.k) (tr.bun qNew))
    (hs_lt : slotOf qNew < slotCap) (hs_empty : S₀ ⟨slotOf qNew, hs_lt⟩ = none)
    (hMatch0 : ∀ q ∈ P, ∃ (hs : slotOf q < slotCap) (B : BundleState),
      S₀ ⟨slotOf q, hs⟩ = some B ∧ BunAgree B (tr.bun q))
    (hDisjNew : ∀ q ∈ P, slotOf q ≠ slotOf qNew)
    (hw16 : 16 ≤ 2 ^ w) (hk1 : 1 ≤ tr.k)
    (htourH_w : tourH < 2 ^ w)
    (htbl_h : tbl + bundleTableFixedSize slotCap eCap ≤ h)
    (hfoot0_lt : ∀ a, (bunTableHeadroomRep slotCap vCap eCap tr.k).foot tbl m₀ a → a < h)
    (hspec_h : slotSpecPtr + 2 ≤ h)
    (hspec_disj_tbl : slotSpecPtr + 2 ≤ tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ slotSpecPtr)
    (hassign_h : edgeAssignPtr + 2 * edges.length ≤ h)
    (hassign_disj_tbl : edgeAssignPtr + 2 * edges.length ≤ tbl ∨
      tbl + bundleTableFixedSize slotCap eCap ≤ edgeAssignPtr)
    (hrPtr_h : rPtr + rList.length ≤ h)
    (hrPtr_disj_tbl : rPtr + rList.length ≤ tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ rPtr)
    (hspace_w : h + bundleInitSlotsSpace TS [(slotOf qNew, cap)] (outCoreOrder tr ord) rList < 2 ^ w)
    (hrep0 : (bunTableHeadroomRep slotCap vCap eCap tr.k).rep tbl S₀ m₀ mem₀)
    (hinv0 : bunRestartInv vCap eCap S₀ (outCoreOrder tr ord))
    (hzero0 : ZeroFrom mem₀ h)
    (htour_rep : htour.rep.rep tourH (outCoreOrder tr ord) tx₀ mem₀)
    (htour_foot_lt : ∀ a, htour.rep.foot tourH tx₀ a → a < h)
    (htour_foot_disj_tbl : ∀ a, htour.rep.foot tourH tx₀ a →
      a < tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ a)
    (htour_foot_disj_blocks : ∀ a, htour.rep.foot tourH tx₀ a →
      ∀ j : Fin slotCap, ∀ ptr c, m₀.slotBlocks j = some (ptr, c) →
        a < ptr ∨ ptr + bundleSlotBlockSize c ≤ a)
    (htour_foot_disj_spec : ∀ a, htour.rep.foot tourH tx₀ a →
      a < slotSpecPtr ∨ slotSpecPtr + 2 ≤ a)
    (htour_foot_disj_r : ∀ a, htour.rep.foot tourH tx₀ a → a < rPtr ∨ rPtr + rList.length ≤ a)
    (hspec_mem : mem₀ slotSpecPtr = slotOf qNew ∧ mem₀ (slotSpecPtr + 1) = cap)
    (hcap_ok : 4 * E.card ≤ cap)
    (hedges_nd : edges.Nodup) (hedges_eq : edges.toFinset = E)
    (hE_sub : E ⊆ (coreGraph tr.cs.G tr.cs.lsf).E)
    (hE_lt : ∀ e ∈ E, e < eCap)
    (hE_fresh : ∀ e ∈ E, ∀ j : Fin slotCap, ∀ B, S₀ j = some B → e ∉ B.edges)
    (hedges_w : edges.length < 2 ^ w)
    (hassigns_mem : bundleReadPairs mem₀ edgeAssignPtr edges.length = edges.map (·, slotOf qNew))
    (hrList_mem : ListAt mem₀ rPtr rList)
    (hrList_lt : ∀ v ∈ rList, v < vCap ∧ v < 2 ^ w)
    (hrList_pw : rList.Pairwise (· < ·))
    (hrList_sub : ∀ v ∈ rList, v ∈ (coreGraph tr.cs.G tr.cs.lsf).V)
    (hcov : ∀ v x, x ∈ outCoreOrder tr ord v → x.1 ∈ E → v ∈ rList) :
    let cord := outCoreOrder tr ord
    let m' := allocSlotBlocksMeta m₀ [(slotOf qNew, cap)] h
    let args := [tbl, tourH, 1, slotSpecPtr, edges.length, edgeAssignPtr, rList.length, rPtr, h]
    ∃ body, p.procs[b + bundleIdxInitSlots]? = some body ∧ ∃ st' c hEnd tx' B',
      let S' : BundleTableState slotCap := Function.update S₀ ⟨slotOf qNew, hs_lt⟩ (some B')
      Runs w p ω body (startState args mem₀ pos₀) (.returned hEnd) st' c ∧
      (bunTableHeadroomRep slotCap vCap eCap tr.k).rep tbl S' m' st'.mem ∧
      bunRestartInv vCap eCap S' cord ∧
      htour.rep.rep tourH cord tx' st'.mem ∧
      (∀ q ∈ insert qNew P, ∃ (hs : slotOf q < slotCap) (B : BundleState),
        S' ⟨slotOf q, hs⟩ = some B ∧ BunAgree B (tr.bun q)) ∧
      h + bundleSlotBlockSize cap ≤ hEnd ∧
      hEnd ≤ h + bundleInitSlotsSpace TS [(slotOf qNew, cap)] cord rList ∧
      ZeroFrom st'.mem hEnd ∧
      c + (bunTableHeadroomRep slotCap vCap eCap tr.k).phi tbl m' st'.mem + htour.rep.phi tourH tx' st'.mem ≤
        bundleInitSlotsCost TS eCap 1 edges.length cord rList + bunPhiMul * (2 * edges.length) +
        (bunTableHeadroomRep slotCap vCap eCap tr.k).phi tbl m₀ mem₀ + htour.rep.phi tourH tx₀ mem₀ := by
  intro cord m' args
  obtain ⟨body, hbody, st', c, hEnd, tx', B', hrun, hrep', hinv', htr', hag, hother,
    hhLo, hhHi, hzf, _, _, _, hc⟩ :=
    bunTableHeadroom_initOneSlot_runs hp htour hs_lt hs_empty hw16 hk1
      (outCoreOrder_coreCordOf hI ρ hρ) htourH_w htbl_h hfoot0_lt hspec_h hspec_disj_tbl
      hassign_h hassign_disj_tbl hrPtr_h hrPtr_disj_tbl hspace_w hrep0 hinv0 hzero0 htour_rep
      htour_foot_lt htour_foot_disj_tbl htour_foot_disj_blocks htour_foot_disj_spec
      htour_foot_disj_r hspec_mem hcap_ok hedges_nd hedges_eq hE_sub hE_lt hE_fresh hedges_w
      hassigns_mem hrList_mem hrList_lt hrList_pw hrList_sub hcov
  refine ⟨body, hbody, st', c, hEnd, tx', B', hrun, hrep', hinv', htr', ?_, hhLo, hhHi, hzf, hc⟩
  intro q hq
  rcases Finset.mem_insert.mp hq with rfl | hqP
  · refine ⟨hs_lt, B', Function.update_self _ _ _, ?_⟩
    exact ⟨hag.1.trans hLazy.1, hag.2.1.trans hLazy.2.1, hag.2.2.1.trans hLazy.2.2.1,
      fun x hx => (hag.2.2.2 x hx).trans (hLazy.2.2.2 x (hag.2.1 ▸ hx))⟩
  · obtain ⟨hs, B, hSB, hB⟩ := hMatch0 q hqP
    have hne : (⟨slotOf q, hs⟩ : Fin slotCap) ≠ ⟨slotOf qNew, hs_lt⟩ :=
      fun h => hDisjNew q hqP (congrArg Fin.val h)
    exact ⟨hs, B, (hother _ hne).trans hSB, hB⟩

/-! ## 5. Branch restart interface `AsmBrBunAt` on `bunTableHeadroomRep` -/

/-- P5's restart satisfies `AsmBrBunAt` with `B5 := fun k slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap k`,
automatically placing `bunTableHeadroomInv` inside `AsmBrSideAt` without editing `AssemblyBranchSide.lean`. -/
def asmBrBunAt_of_bunRestart_headroom {TS : BundleTourSpec} {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {w cT : ℕ} {p : Program} {bTourList bTourLen bOwner bWalk bSort bInit bDllPush bExport f : ℕ}
    (hT : AsmBrTourBridge TS TR w p bTourList bTourLen bOwner)
    (hw : 16 ≤ 2 ^ w)
    (hLS : ∀ len, TS.listSpace len ≤ cT * (len + 1))
    (hpf : p.procs[f]? = some (bunRestartStmt bWalk bOwner bSort bInit bExport))
    (hpWalk : p.procs[bWalk]? = some outWalkBody) (hpSort : p.HasAt bSort (sortProcs bSort))
    (hpInit : p.procs[bInit]? = some (bundleInitSlotsStmt bDllPush bTourList))
    (hbPush : ∀ eCap prevBase nextBase headAddr key L, MeetsContract w p bDllPush
      (bundleDllPushContract w prevBase nextBase headAddr (2 * eCap) key L))
    (hpExport : p.HasAt bExport [bundleExportGraphStmt]) :
    AsmBrBunAt TR (fun k slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap k) w p f where
  mul := asmBrBunMul TS cT
  space _ x := brSpaceC TS cT * (x + 1)
  space_le slotCap n := brSpaceC_le TS cT slotCap n
  rep_local k slotCap vCap eCap := bunTableHeadroomRep_local slotCap vCap eCap k
  runs := by
    intro k slotCap vCap₅ eCap₅ vCap eCap vo vf vc mk hv he heW hvW
    subst hv he
    obtain ⟨⟨rep, hloc, hlist, hlen, howner⟩, hrep⟩ := hT vCap₅ eCap₅ vo vf vc mk
    subst hrep
    intro tbl tourH slotsPtr h slots S x cord tx cs ord mem pos ω htbl htourH hn hsp hh hlistS
      hsl hnd hact hk hcore hinv hrepS hrepT hfoot hfootT hdisj hz hfit
    let T : BundleTourAt TS w vCap₅ eCap₅ p bTourList bTourLen bOwner :=
      ⟨asmTourCordView (TR vCap₅ eCap₅) vo vf vc mk, hloc, hlist, hlen, howner⟩
    let I := bunRestartAtK_headroom (slotCap := slotCap) (cT := cT) T hw heW hvW hLS hpf hpWalk
      hpSort hpInit (hbPush eCap₅) hpExport
    obtain ⟨body, hb, o, st', c, S', x', tx', hrun, hrS, hrT, hinv', hun, hlisted, hlo, hhi, hz',
        hfr, hft, hftT, hdj, hc⟩ :=
      I.runs k tbl tourH slotsPtr h slots S x cord tx cs ord mem pos ω htbl htourH hn hsp hh hlistS
        hsl hnd hact hk hcore hinv hrepS hrepT hfoot hfootT hdisj hz hfit
    have hc' : c + (bunTableHeadroomRep slotCap vCap₅ eCap₅ k).phi tbl x' st'.mem +
        (asmTourCordView (TR vCap₅ eCap₅) vo vf vc mk).phi tourH tx' st'.mem ≤
        brMul TS * (cs.G.m + slots.length + 1) * ordStoreLog eCap₅ +
          (bunTableHeadroomRep slotCap vCap₅ eCap₅ k).phi tbl x mem +
          (asmTourCordView (TR vCap₅ eCap₅) vo vf vc mk).phi tourH tx mem := hc
    refine ⟨body, hb, o, st', c, S', x', tx', hrun, hrS, hrT, hinv', hun, hlisted, hlo, hhi, hz',
      hfr, hft, hftT, hdj, le_trans hc' ?_⟩
    have hm : brMul TS ≤ asmBrBunMul TS cT := by unfold asmBrBunMul; omega
    have := Nat.mul_le_mul_right (ordStoreLog eCap₅)
      (Nat.mul_le_mul_right (cs.G.m + slots.length + 1) hm)
    omega

end

end MinCostFlow.SparseCore.Program
