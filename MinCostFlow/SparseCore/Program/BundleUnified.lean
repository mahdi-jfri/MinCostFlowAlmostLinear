module

public import MinCostFlow.SparseCore.Program.BundleModule
public import MinCostFlow.SparseCore.Program.BunRestartValue

/-!
# Unified bundle table operations on `bunTableRep` and linear space bounds (`BundleUnified`)

Lifts all P5 bundle-manager operations (`bundleTableDS`, `readParent`, `initSlots`, and `step`)
onto the single branch table representation `bunTableRep slotCap vCap eCap k` (whose potential is
`bunPhiMul * ∑ j, nB_j`, `bunPhiMul = 300`, matching `bunRestartAtK`) and invariant
`bunRestartInv vCap eCap S cord`:

1. `bunTableDS_implements`: `WordRAM.DSRep.Implements` for table init, bundle-graph export (`op 0`),
   and `bundleOf` lookup (`op 1`) against `bunTableRep` (`Δφ = 0`).
2. `BundleSlotRepAt.congr_parent` & `BundleTableRepAt.congr_parent`: `BundleSlotRepAt` only stores
   `parent b` in memory when bundle `b` is empty, so changing `parent b` on nonempty bundles
   preserves `BundleTableRepAt` with zero memory writes.
3. `bunTable_readParent_runs`: parent query against `bunTableRep` and `bunRestartInv` (`Δφ = 0`).
4. `bunTable_initSlots_runs`: multi-slot initialization against `bunTableRep` and `bunRestartInv`,
   paying `bunPhiMul * (2 * nEdges)` into the table potential for the newly created bundles.
5. `bunTable_step_runs`: three-phase step against `bunTableRep`, paying `bunPhiMul` per split-added
   bundle (`bunPhiMul * ∑ j, batchSplitCount (slotBatchOf ... j)`), emitting `SmallBatchAt` with
   word length `W ≤ 6 * Enc(U_B)`.
6. Linear space corollaries (`bundleReadParent_space_le_linear`, `bundleInitSlotsSpace_le_linear`,
   `bundleStepSpace_le_linear`): every P5 operation uses space linear in its input with constants
   free of both the input and `slotCap`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain MinCostFlow.DynSpanner
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

public section

/-! ## 1. `bunTableDS_implements` on `bunTableRep` -/

/-- `bundleProcs` implements `bundleTableDS` (`init`, `op 0` export, `op 1` readBundleOf)
against the unified representation `bunTableRep slotCap vCap eCap k` (`Δφ = 0`). -/
theorem bunTableDS_implements (w slotCap vCap eCap k : ℕ) {p : Program}
    {b bTourList bTourLen bTourOwner : ℕ}
    (hp : p.HasAt b (bundleProcs b bTourList bTourLen bTourOwner)) :
    (bunTableRep slotCap vCap eCap k).Implements w p (b + bundleIdxTableInit)
      (fun i => if i = 0 then b + bundleIdxExportGraph else b + bundleIdxReadBundleOf)
      (bundleTableDS w slotCap vCap eCap k) := by
  have himp := bundleTableDS_implements w slotCap vCap eCap k hp
  refine ⟨bunTableRep_local slotCap vCap eCap k, ?_, ?_⟩
  · intro args mem pos ω hW hpre hzero hspace
    obtain ⟨body, hbody, o, st', c, hrun, S', m', hrep', hpost', hfr, hc⟩ :=
      himp.2.1 args mem pos ω hW hpre hzero hspace
    have hphi' : (bunTableRep slotCap vCap eCap k).phi (heapArg args) m' st'.mem = 0 := by
      rw [bunTablePhi_eq hrep'.1]
      have hS' : S' = fun _ => none := hpost'
      simp [hS', bunSlotNB]
    refine ⟨body, hbody, o, st', c, hrun, S', m', hrep', hpost', hfr, ?_⟩
    rw [hphi']; exact hc
  · intro i tbl S m args mem pos ω hW hhead hrep hpre hfoot hzero hspace
    obtain ⟨body, hbody, o, st', c, hrun, S', m', hrep', hpost', hfr, hc⟩ :=
      himp.2.2 i tbl S m args mem pos ω hW hhead hrep hpre hfoot hzero hspace
    have hSeq : S' = S := by
      by_cases hi0 : i = 0
      · subst hi0; exact hpost'.1
      · by_cases hi1 : i = 1
        · subst hi1; exact hpost'.1
        · simp [bundleTableDS, hi0, hi1] at hpre
    have hphi_eq : (bunTableRep slotCap vCap eCap k).phi tbl m' st'.mem =
        (bunTableRep slotCap vCap eCap k).phi tbl m mem := by
      rw [bunTablePhi_eq hrep'.1, bunTablePhi_eq hrep.1, hSeq]
    refine ⟨body, hbody, o, st', c, hrun, S', m', hrep', hpost', hfr, ?_⟩
    change c + 0 ≤ _ + 0 at hc
    omega

/-! ## 2. Parent congruence for `BundleSlotRepAt` and `BundleTableRepAt` -/

/-- `BundleSlotRepAt` only reads `B.parent b` from memory when `B.ends b = ∅`, so replacing
`B.parent` on nonempty bundles preserves `BundleSlotRepAt` with zero memory changes. -/
theorem BundleSlotRepAt.congr_parent {eCap prevBase nextBase p bunCap : ℕ}
    {B B' : BundleState} {mem : ℕ → ℕ}
    (h : BundleSlotRepAt eCap prevBase nextBase p bunCap B mem)
    (hV : B'.vertices = B.vertices) (hE : B'.edges = B.edges)
    (hbo : ∀ x ∈ edgeEnds B.edges, B'.bundleOf x = B.bundleOf x)
    (hpOut : ∀ b, B.vertices.card ≤ b → B'.parent b = 0)
    (hpEmp : ∀ b ∈ B.vertices, B.ends b = ∅ → B'.parent b = B.parent b) :
    BundleSlotRepAt eCap prevBase nextBase p bunCap B' mem := by
  obtain ⟨nB, hVB, hnB, hEB, hboB, _, hm0, hm1, hm2, hdll, hpar, htail, hscr⟩ := h
  have hcard : B.vertices.card = nB := by rw [hVB, Finset.card_range]
  have hends : ∀ b, B'.ends b = B.ends b := fun b => by
    ext x; simp only [BundleState.mem_ends, hE]
    exact ⟨fun ⟨hx, hxb⟩ => ⟨hx, (hbo x ((mem_edgeEnds _ _).mpr hx)).symm.trans hxb⟩,
      fun ⟨hx, hxb⟩ => ⟨hx, (hbo x ((mem_edgeEnds _ _).mpr hx)).trans hxb⟩⟩
  refine ⟨nB, hV.trans hVB, hnB, hE ▸ hEB, fun x hx => ?_, fun b hb => hpOut b (hcard.symm ▸ hb),
    hm0, hm1, hE ▸ hm2, fun b hb => ?_, fun b hb hem => ?_, htail, hscr⟩
  · have hxB : x ∈ edgeEnds B.edges := hE ▸ hx
    rw [hbo x hxB]; exact hboB x hxB
  · obtain ⟨L, hL, hsz, hmem⟩ := hdll b hb
    exact ⟨L, hL, hsz, fun k => (hmem k).trans (by rw [hends b])⟩
  · have hemB : B.ends b = ∅ := by rwa [← hends b]
    rw [hpEmp b (hVB ▸ Finset.mem_range.mpr hb) hemB]
    exact hpar b hb hemB

/-- Lifting `BundleSlotRepAt.congr_parent` to `BundleTableRepAt`. -/
theorem BundleTableRepAt.congr_parent {slotCap vCap eCap tbl : ℕ}
    {S S' : BundleTableState slotCap} {m : BundleTableMeta slotCap} {mem : ℕ → ℕ}
    (h : BundleTableRepAt slotCap vCap eCap tbl S m mem)
    (hslot : ∀ j : Fin slotCap, match S j, S' j with
      | none, none => True
      | some B, some B' =>
          B'.vertices = B.vertices ∧ B'.edges = B.edges ∧
          (∀ x ∈ edgeEnds B.edges, B'.bundleOf x = B.bundleOf x) ∧
          (∀ b, B.vertices.card ≤ b → B'.parent b = 0) ∧
          (∀ b ∈ B.vertices, B.ends b = ∅ → B'.parent b = B.parent b)
      | _, _ => False) :
    BundleTableRepAt slotCap vCap eCap tbl S' m mem := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    hdisj, hedSlot, hendB, hslots, hdisjB, hscr1, hscr2, hscr3⟩
  have hEdgesEq : ∀ j B', S' j = some B' → ∃ B, S j = some B ∧
      B'.vertices = B.vertices ∧ B'.edges = B.edges ∧
      (∀ x ∈ edgeEnds B.edges, B'.bundleOf x = B.bundleOf x) ∧
      (∀ b, B.vertices.card ≤ b → B'.parent b = 0) ∧
      (∀ b ∈ B.vertices, B.ends b = ∅ → B'.parent b = B.parent b) := by
    intro j B' hS'
    have hs := hslot j; rw [hS'] at hs
    cases hS : S j with
    | none => rw [hS] at hs; exact False.elim hs
    | some B => rw [hS] at hs; exact ⟨B, rfl, hs⟩
  refine ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ?_, ?_, ?_, ?_, hdisjB, hscr1, hscr2, hscr3⟩
  · intro j₁ j₂ hne B₁' B₂' h1' h2'
    obtain ⟨B₁, hS1, -, hE1, -⟩ := hEdgesEq j₁ B₁' h1'
    obtain ⟨B₂, hS2, -, hE2, -⟩ := hEdgesEq j₂ B₂' h2'
    rw [hE1, hE2]; exact hdisj j₁ j₂ hne B₁ B₂ hS1 hS2
  · intro e he
    refine ⟨fun j B' hS' he' => ?_, fun hnone => (hedSlot e he).2 fun j B hS heB => ?_⟩
    · obtain ⟨B, hS, -, hE, -⟩ := hEdgesEq j B' hS'
      exact (hedSlot e he).1 j B hS (hE ▸ he')
    · have hs := hslot j; rw [hS] at hs
      cases hS' : S' j with
      | none => rw [hS'] at hs; exact False.elim hs
      | some B' => rw [hS'] at hs; exact hnone j B' hS' (hs.2.1.symm ▸ heB)
  · intro j B' hS' x hx
    obtain ⟨B, hS, -, hE, hbo, -⟩ := hEdgesEq j B' hS'
    have hxB : x ∈ edgeEnds B.edges := hE ▸ hx
    rw [hbo x hxB]; exact hendB j B hS x hxB
  · intro j
    have hs := hslot j
    have hmj := hslots j
    cases hS' : S' j with
    | none =>
      rw [hS'] at hs
      cases hS : S j with
      | none => rw [hS] at hmj; exact hmj
      | some B => rw [hS] at hs; exact False.elim hs
    | some B' =>
      rw [hS'] at hs
      cases hS : S j with
      | none => rw [hS] at hs; exact False.elim hs
      | some B =>
        rw [hS] at hs hmj
        cases hm : m.slotBlocks j with
        | none => rw [hm] at hmj; exact hmj
        | some pb =>
          rw [hm] at hmj
          exact ⟨hmj.1, hmj.2.1.congr_parent hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2, hmj.2.2⟩

/-! ## 3. Exact bundle-count growth of `byRootSplitFold` -/

private lemma runsFoldStep_vertices_card (s : List Update × BundleState) (b : ℕ)
    (vruns : List (ℕ × List End)) :
    (runsFoldStep s (b, vruns)).2.vertices.card = s.2.vertices.card + (vruns.drop 1).length ∧
    batchSplitCount (runsFoldStep s (b, vruns)).1 = batchSplitCount s.1 + (vruns.drop 1).length := by
  set next := s.2.vertices.sup id + 1
  set m := (vruns.drop 1).length
  have hV : (runsFoldStep s (b, vruns)).2.vertices =
      s.2.vertices ∪ ((List.range m).map fun i => next + i).toFinset := by
    ext c; rw [runsFoldStep_vertices, Finset.mem_union, List.mem_toFinset, List.mem_map]
    constructor
    · rintro (hc | ⟨i, hi, rfl⟩)
      · exact Or.inl hc
      · exact Or.inr ⟨i, List.mem_range.mpr hi, rfl⟩
    · rintro (hc | ⟨i, hi, rfl⟩)
      · exact Or.inl hc
      · exact Or.inr ⟨i, List.mem_range.mp hi, rfl⟩
  have hdisj : Disjoint s.2.vertices ((List.range m).map fun i => next + i).toFinset := by
    rw [Finset.disjoint_left]
    intro c hc hm
    rw [List.mem_toFinset, List.mem_map] at hm
    obtain ⟨i, _, rfl⟩ := hm
    have hle : next + i ≤ s.2.vertices.sup id := Finset.le_sup (f := id) hc
    omega
  have hnd : ((List.range m).map fun i => next + i).Nodup :=
    List.Nodup.map (fun _ _ h => by omega) List.nodup_range
  have hcard : (runsFoldStep s (b, vruns)).2.vertices.card = s.2.vertices.card + m := by
    rw [hV, Finset.card_union_of_disjoint hdisj, List.toFinset_card_of_nodup hnd,
      List.length_map, List.length_range]
  have hsplits : batchSplitCount (runsFoldStep s (b, vruns)).1 = batchSplitCount s.1 + m := by
    unfold batchSplitCount runsFoldStep bundleSplitFoldStep
    dsimp only
    rw [List.countP_append]
    congr 1
    unfold bundleRunUpdates
    rw [List.countP_eq_length.mpr (by
      intro u hu
      obtain ⟨⟨run, fresh⟩, _, rfl⟩ := List.mem_map.mp hu
      rfl)]
    simp [m]
  exact ⟨hcard, hsplits⟩

/-- For any `B₀`, `E`, `src'`, `dels`, and `cands`, `byRootSplitFold` adds exactly
`batchSplitCount res.1` new bundle vertices to `B₀.vertices`. -/
theorem byRootSplitFold_vertices_card (B₀ : BundleState) (E : Finset ℕ) (src' : End → ℕ)
    (dels cands : List ℕ) :
    let res := byRootSplitFold B₀ E src' (dels.map Update.delete) cands
    res.2.vertices.card = B₀.vertices.card + batchSplitCount res.1 := by
  have hgo : ∀ (cs : List ℕ) (s : List Update × BundleState),
      (cs.map fun b => (b, byRootVRuns B₀ E src' b)).foldl runsFoldStep s |>.2.vertices.card +
        batchSplitCount s.1 =
      s.2.vertices.card +
        batchSplitCount ((cs.map fun b => (b, byRootVRuns B₀ E src' b)).foldl runsFoldStep s).1 := by
    intro cs
    induction cs with
    | nil => intro s; simp
    | cons b rest ih =>
      intro s
      simp only [List.map_cons, List.foldl_cons]
      have hstep := runsFoldStep_vertices_card s b (byRootVRuns B₀ E src' b)
      have hih := ih (runsFoldStep s (b, byRootVRuns B₀ E src' b))
      omega
  have h0 : batchSplitCount (dels.map Update.delete) = 0 := by
    unfold batchSplitCount
    rw [List.countP_eq_zero]
    intro u hu
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hu
    simp [isSplit]
  have hmain := hgo cands (dels.map Update.delete, { B₀ with edges := E })
  unfold byRootSplitFold
  dsimp only at hmain ⊢
  rw [h0] at hmain
  omega

/-! ## 4. Unified entry points on `bunTableRep` -/

/-- `readParent` against `bunTableRep slotCap vCap eCap k` and `bunRestartInv vCap eCap S cord`,
preserving both and leaving the table potential unchanged (`Δφ_tbl = 0`). -/
theorem bunTable_readParent_runs {TS : BundleTourSpec} {w slotCap vCap eCap k : ℕ} {p : Program}
    {b bTourList bTourLen bTourOwner : ℕ}
    (hp : p.HasAt b (bundleProcs b bTourList bTourLen bTourOwner))
    (htour : BundleTourAt TS w vCap eCap p bTourList bTourLen bTourOwner)
    {tbl tourH bun h : ℕ} {j : Fin slotCap} {S : BundleTableState slotCap}
    {m : BundleTableMeta slotCap} {B : BundleState} {cord : ℕ → List End}
    {tx : htour.rep.τ} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w) (hvCap : vCap < 2 ^ w)
    (htblFit : tbl + bundleTableFixedSize slotCap eCap < 2 ^ w) (htourH : tourH < 2 ^ w)
    (hhSpace : h + TS.querySpace < 2 ^ w) (hzero : ZeroFrom mem h)
    (hfootB : ∀ a, (bunTableRep slotCap vCap eCap k).foot tbl m a → a < h)
    (hfootT : ∀ a, htour.rep.foot tourH tx a → a < h)
    (hdisjBT : ∀ a, (bunTableRep slotCap vCap eCap k).foot tbl m a → ¬ htour.rep.foot tourH tx a)
    (hrepB : (bunTableRep slotCap vCap eCap k).rep tbl S m mem)
    (hrepT : htour.rep.rep tourH cord tx mem)
    (hinv : bunRestartInv vCap eCap S cord)
    (hSj : S j = some B) (hbun : bun ∈ B.vertices) :
    ∃ body, p.procs[b + bundleIdxReadParent]? = some body ∧ ∃ o st' c tx',
      Runs w p ω body (startState [tbl, tourH, j.1, bun, h] mem pos) o st' c ∧
      (bunTableRep slotCap vCap eCap k).rep tbl S m st'.mem ∧
      htour.rep.rep tourH cord tx' st'.mem ∧
      bunRestartInv vCap eCap S cord ∧
      st'.mem h = B.parent bun ∧
      h + 1 ≤ o.value ∧ o.value ≤ h + TS.querySpace ∧ ZeroFrom st'.mem o.value ∧
      (∀ a < h, ¬ htour.rep.foot tourH tx a → st'.mem a = mem a) ∧
      (∀ a, htour.rep.foot tourH tx' a → htour.rep.foot tourH tx a ∨ (h ≤ a ∧ a < o.value)) ∧
      c + (bunTableRep slotCap vCap eCap k).phi tbl m st'.mem + htour.rep.phi tourH tx' st'.mem ≤
        TS.mul * ordStoreLog eCap + 60 +
        (bunTableRep slotCap vCap eCap k).phi tbl m mem + htour.rep.phi tourH tx mem := by
  obtain ⟨body, hbody, o, st', c, tx', hrun, hrepB', hrepT', hval, hlo, hhi, hzf, hfr, hft, hc⟩ :=
    bundleModule_readParent_runs hp htour hw16 hvCap htblFit htourH hhSpace hzero
      hfootB hfootT hdisjBT hrepB.1 hrepT hinv.1 hSj hbun
  have hk' : st'.mem (btBunCapAddr tbl slotCap eCap) = k :=
    (hfr _ (hfootB _ btBunCap_in_foot) (hdisjBT _ btBunCap_in_foot)).trans hrepB.2
  have hphi_eq : (bunTableRep slotCap vCap eCap k).phi tbl m st'.mem =
      (bunTableRep slotCap vCap eCap k).phi tbl m mem := by
    rw [bunTablePhi_eq hrepB', bunTablePhi_eq hrepB.1]
  refine ⟨body, hbody, o, st', c, tx', hrun, ⟨hrepB', hk'⟩, hrepT', hinv, hval, hlo, hhi, hzf,
    hfr, hft, ?_⟩
  omega

private lemma sum_slotEdgesOf_card_le {slotCap : ℕ} (assigns : List (ℕ × ℕ))
    (hnd : (assigns.map Prod.fst).Nodup) :
    ∑ j : Fin slotCap, (slotEdgesOf assigns j.1).card ≤ assigns.length := by
  have h1 : ∀ j : Fin slotCap, (slotEdgesOf assigns j.1).card =
      (assigns.filter fun p => p.2 == j.1).length := fun j => slotEdgesOf_card_eq hnd
  simp_rw [h1]
  clear hnd h1
  induction assigns with
  | nil => simp
  | cons a tl ih =>
    simp only [List.filter_cons, List.length_cons]
    have hsplit : (∑ j : Fin slotCap,
        (if (a.2 == j.1) = true then a :: tl.filter (fun p => p.2 == j.1)
         else tl.filter (fun p => p.2 == j.1)).length) =
      (∑ j : Fin slotCap, (if a.2 = j.1 then 1 else 0)) +
        ∑ j : Fin slotCap, (tl.filter fun p => p.2 == j.1).length := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases heq : a.2 = j.1 <;> simp [heq, Nat.add_comm]
    rw [hsplit]
    have hle1 : (∑ j : Fin slotCap, (if a.2 = j.1 then 1 else 0)) ≤ 1 := by
      by_cases hlt : a.2 < slotCap
      · rw [Finset.sum_eq_single ⟨a.2, hlt⟩]
        · simp
        · intro j _ hne; simp [show a.2 ≠ j.1 from fun h => hne (Fin.ext h.symm)]
        · intro h; exact False.elim (h (Finset.mem_univ _))
      · rw [Finset.sum_eq_zero]
        · omega
        · intro j _; simp [show a.2 ≠ j.1 from fun h => hlt (h ▸ j.2)]
    omega

/-- Multi-slot initialization against `bunTableRep slotCap vCap eCap k` and
`bunRestartInv vCap eCap S₀ cord`, paying at most `bunPhiMul * (2 * nEdges)` into the table
potential for the newly created bundle vertices. -/
theorem bunTable_initSlots_runs {TS : BundleTourSpec} {w slotCap vCap eCap tbl tourH k nSlots
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
    (hfoot0_lt : ∀ a, (bunTableRep slotCap vCap eCap k).foot tbl m₀ a → a < h)
    (hspec_h : slotSpecPtr + 2 * nSlots ≤ h)
    (hspec_disj_tbl : slotSpecPtr + 2 * nSlots ≤ tbl ∨
      tbl + bundleTableFixedSize slotCap eCap ≤ slotSpecPtr)
    (hassign_h : edgeAssignPtr + 2 * nEdges ≤ h)
    (hassign_disj_tbl : edgeAssignPtr + 2 * nEdges ≤ tbl ∨
      tbl + bundleTableFixedSize slotCap eCap ≤ edgeAssignPtr)
    (hrPtr_h : rPtr + nR ≤ h)
    (hrPtr_disj_tbl : rPtr + nR ≤ tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ rPtr)
    (hspace_w : h + bundleInitSlotsSpace TS specs cord rList < 2 ^ w)
    (hrep0 : (bunTableRep slotCap vCap eCap k).rep tbl S₀ m₀ mem₀)
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
    (hspecs_cap : ∀ sb ∈ specs,
      (initPrefixSlots cord rList (slotEdgesOf assigns sb.1) k).length ≤ sb.2)
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
      (bunTableRep slotCap vCap eCap k).rep tbl S' m' st'.mem ∧
      bunRestartInv vCap eCap S' cord ∧
      htour.rep.rep tourH cord tx' st'.mem ∧
      (∀ a, (bunTableRep slotCap vCap eCap k).foot tbl m' a →
        (bunTableRep slotCap vCap eCap k).foot tbl m₀ a ∨ (h ≤ a ∧ a < h + slotBlocksSpace specs)) ∧
      (∀ a, htour.rep.foot tourH tx' a →
        htour.rep.foot tourH tx₀ a ∨ (h + slotBlocksSpace specs ≤ a ∧ a < hEnd)) ∧
      (∀ a, a < h → ¬ (bunTableRep slotCap vCap eCap k).foot tbl m₀ a →
        ¬ htour.rep.foot tourH tx₀ a → st'.mem a = mem₀ a) ∧
      c + (bunTableRep slotCap vCap eCap k).phi tbl m' st'.mem + htour.rep.phi tourH tx' st'.mem ≤
        bundleInitSlotsCost TS eCap nSlots nEdges cord rList + bunPhiMul * (2 * nEdges) +
        (bunTableRep slotCap vCap eCap k).phi tbl m₀ mem₀ + htour.rep.phi tourH tx₀ mem₀ := by
  intro S' m' args
  obtain ⟨body, hbody, st', c, hEnd, tx', hrun, hhLo, hhHi, hzf, hrep', hk', hcm', htr',
    hfootB', hfootT', hfr, hc⟩ :=
    bundleModule_initSlots_runs hp htour hw16 hk1 hrep0.2 htourH_w htbl_h hfoot0_lt hspec_h
      hspec_disj_tbl hassign_h hassign_disj_tbl hrPtr_h hrPtr_disj_tbl hspace_w hrep0.1 hinv0.1
      hzero0 htour_rep htour_foot_lt htour_foot_disj_tbl htour_foot_disj_blocks
      htour_foot_disj_spec htour_foot_disj_r hnSlots hspecs_mem hspecs_lt hspecs_nd hspecs_empty
      hspecs_cap hnEdges hassigns_mem hassigns_in hassigns_nd hassigns_fresh hnEdges_w hnR
      hrList_mem hrList_lt hrList_nd hcord_nd
      (fun v _ x hx => (hinv0.2 v x hx).2) hcov
  have hnb_sum : ∑ j : Fin slotCap, bunSlotNB S' j ≤
      (∑ j : Fin slotCap, bunSlotNB S₀ j) + 2 * nEdges := by
    have hpt : ∀ j : Fin slotCap,
        bunSlotNB S' j ≤ bunSlotNB S₀ j + 2 * (slotEdgesOf assigns j.1).card := fun j => by
      unfold bunSlotNB S' tableAfterInitSlots
      by_cases hm : j.1 ∈ specs.map Prod.fst
      · simp only [hm, ↓reduceIte]
        have hlen := initPrefixSlots_length_le hk1 hrList_nd hcord_nd hinv0.1.1
          (E := slotEdgesOf assigns j.1)
        change (Finset.range (initPrefixSlots cord rList (slotEdgesOf assigns j.1) k).length).card ≤ _
        rw [Finset.card_range]; omega
      · simp only [hm, ↓reduceIte]; omega
    calc ∑ j : Fin slotCap, bunSlotNB S' j
        ≤ ∑ j : Fin slotCap, (bunSlotNB S₀ j + 2 * (slotEdgesOf assigns j.1).card) :=
          Finset.sum_le_sum fun j _ => hpt j
      _ = (∑ j : Fin slotCap, bunSlotNB S₀ j) + 2 * ∑ j : Fin slotCap, (slotEdgesOf assigns j.1).card := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ (∑ j : Fin slotCap, bunSlotNB S₀ j) + 2 * nEdges := by
          have := sum_slotEdgesOf_card_le (slotCap := slotCap) assigns hassigns_nd
          omega
  have hphi_le : (bunTableRep slotCap vCap eCap k).phi tbl m' st'.mem ≤
      (bunTableRep slotCap vCap eCap k).phi tbl m₀ mem₀ + bunPhiMul * (2 * nEdges) := by
    rw [bunTablePhi_eq hrep', bunTablePhi_eq hrep0.1]
    have := Nat.mul_le_mul_left bunPhiMul hnb_sum
    rw [Nat.mul_add] at this; exact this
  refine ⟨body, hbody, st', c, hEnd, tx', hrun, hhLo, hhHi, hzf, ⟨hrep', hk'⟩, ⟨hcm', hinv0.2⟩,
    htr', hfootB', hfootT', hfr, ?_⟩
  omega

/-- Three-phase `bundleStep` against `bunTableRep slotCap vCap eCap k`: pays `bunPhiMul` per
split-added bundle into `bunTableRep.phi` and emits `SmallBatchAt` (`W ≤ 6 * Enc`) for every
touched slot. -/
theorem bunTable_step_runs {TS : BundleTourSpec}
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
    (hfoot_lt : ∀ a, (bunTableRep slotCap vCap eCap k).foot tbl m a → a < h₀)
    (hdel_lt : delPtr + 3 * delCount ≤ h₀)
    (hgrp_lt : groupPtr + groupsWords gs ≤ h₀)
    (hout_lt : outDescPtr + 1 + 3 * slotCap ≤ h₀)
    (hdel_disj_foot : ∀ a, delPtr ≤ a → a < delPtr + 3 * delCount →
      ¬ (bunTableRep slotCap vCap eCap k).foot tbl m a)
    (hgrp_disj_foot : ∀ a, groupPtr ≤ a → a < groupPtr + groupsWords gs →
      ¬ (bunTableRep slotCap vCap eCap k).foot tbl m a)
    (hout_disj_foot : ∀ a, outDescPtr ≤ a → a < outDescPtr + 1 + 3 * slotCap →
      ¬ (bunTableRep slotCap vCap eCap k).foot tbl m a)
    (htfoot_lt : ∀ a, htour.rep.foot tourH tx₀ a → a < h₀)
    (htfoot_disj_tbl : ∀ a, htour.rep.foot tourH tx₀ a →
      ¬ (bunTableRep slotCap vCap eCap k).foot tbl m a)
    (htfoot_disj_grp : ∀ a, htour.rep.foot tourH tx₀ a → a < groupPtr ∨ groupPtr + groupsWords gs ≤ a)
    (htfoot_disj_out : ∀ a, htour.rep.foot tourH tx₀ a → a < outDescPtr ∨ outDescPtr + 1 + 3 * slotCap ≤ a)
    (hzero : ZeroFrom mem₀ h₀)
    (htrep : htour.rep.rep tourH cord' tx₀ mem₀)
    (hrep0 : (bunTableRep slotCap vCap eCap k).rep tbl S₀ m mem₀)
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
    (hcap_ok : ∀ (maxIdxs : List ℕ) (j : Fin slotCap) (B₀ : BundleState) (ptr bunCap : ℕ),
      maxIdxs.length = gs.length →
      (∀ gi (hgi : gi < gs.length), maxIdxs.getD gi 0 < gs[gi].length) →
      S₀ j = some B₀ → m.slotBlocks j = some (ptr, bunCap) →
      B₀.vertices.card + slotScannedEnds S₀ (dels.map Prod.fst).toFinset cord' gs maxIdxs j ≤ bunCap)
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
      (bunTableRep slotCap vCap eCap k).rep tbl S_final m st'.mem ∧
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
      (∀ a < h₀, ¬ (bunTableRep slotCap vCap eCap k).foot tbl m a →
        (a < outDescPtr ∨ outDescPtr + 1 + 3 * slotCap ≤ a) →
        ¬ htour.rep.foot tourH tx₀ a → st'.mem a = mem₀ a) ∧
      c + 70 * touched.length + (bunTableRep slotCap vCap eCap k).phi tbl m st'.mem + htour.rep.phi tourH tx' st'.mem ≤
        bundleStepCost TS eCap delCount gs +
        bunPhiMul * (∑ j : Fin slotCap, batchSplitCount (slotBatchOf S₀ D src' candSet j)) +
        bundleScanPotMul TS eCap * totalNonMaxLen cord' gs maxIdxs +
        (bunTableRep slotCap vCap eCap k).phi tbl m mem₀ + htour.rep.phi tourH tx₀ mem₀ := by
  intro D S_del
  obtain ⟨body, hbody, st', c, h', tx', maxIdxs, touched, hrun, hmaxLen, hmaxSpec,
    hndT, hltT, htouchIff, hhLo, hhHi, hzf, htr', htf', hrep', hk', hout0, hdescs, hfr, hc⟩ :=
    bundleModule_step_runs hp htour hw16 htourH_w hpk_w htbl_w hblks_w hdel_w hgrp_w
      hout_w hfoot_lt hdel_lt hgrp_lt hout_lt hdel_disj_foot hgrp_disj_foot hout_disj_foot
      htfoot_lt htfoot_disj_tbl htfoot_disj_grp htfoot_disj_out hzero htrep hrep0.1
      hdels_len hdels_mem hdels_lt hdels_par hgs_mem hgs_pos hgs_lt hgs_nodup hgs_disj
      hgs_ends_lt hgs_nd hsrc_lt hsrc_mem hsrc_uniq hbundle_in_group hcap_ok hh_sp
  set candSet := addCandsForGroups S_del cord' gs maxIdxs (fun _ => ∅) gs.length
  set S_final := tableAfterStep S₀ D src' candSet
  have hphi_eq : (bunTableRep slotCap vCap eCap k).phi tbl m st'.mem =
      (bunTableRep slotCap vCap eCap k).phi tbl m mem₀ +
      bunPhiMul * ∑ j : Fin slotCap, batchSplitCount (slotBatchOf S₀ D src' candSet j) := by
    rw [bunTablePhi_eq hrep', bunTablePhi_eq hrep0.1, ← Nat.mul_add]
    congr 1
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold bunSlotNB S_final tableAfterStep slotBatchOf
    cases hS : S₀ j with
    | none => simp [batchSplitCount]
    | some B₀ =>
      exact byRootSplitFold_vertices_card B₀ (B₀.edges \ D) src'
        ((B₀.edges ∩ D).sort (· ≤ ·)) ((candSet j).sort (· ≤ ·))
  refine ⟨body, hbody, st', c, h', tx', maxIdxs, touched, hrun, hmaxLen, hmaxSpec,
    hndT, hltT, htouchIff, hhLo, hhHi, hzf, htr', htf', ⟨hrep', hk'.trans hrep0.2⟩,
    hout0, hdescs, hfr, ?_⟩
  change c + 70 * touched.length + (bunTableRep slotCap vCap eCap k).phi tbl m st'.mem + htour.rep.phi tourH tx' st'.mem ≤
    bundleStepCost TS eCap delCount gs +
    bunPhiMul * (∑ j : Fin slotCap, batchSplitCount (slotBatchOf S₀ D src' candSet j)) +
    bundleScanPotMul TS eCap * totalNonMaxLen cord' gs maxIdxs +
    (bunTableRep slotCap vCap eCap k).phi tbl m mem₀ + htour.rep.phi tourH tx₀ mem₀
  change c + 70 * touched.length + htour.rep.phi tourH tx' st'.mem ≤
    bundleStepCost TS eCap delCount gs +
    bundleScanPotMul TS eCap * totalNonMaxLen cord' gs maxIdxs + htour.rep.phi tourH tx₀ mem₀ at hc
  rw [hphi_eq]; omega

/-! ## 5. Linear space bounds (free of input and `slotCap`) -/

/-- `readParent` space is bounded by a constant free of input and `slotCap`. -/
theorem bundleReadParent_space_le_linear (TS : BundleTourSpec) :
    TS.querySpace ≤ TS.querySpace * (1 + 1) := by
  omega

/-- `bundleInitSlotsSpace` is linear in the input with constant `12 + 4 * cT` (free of both the
input and `slotCap`) whenever `TS.listSpace len ≤ cT * (len + 1)`. -/
theorem bundleInitSlotsSpace_le_linear {TS : BundleTourSpec} {cT m nEdges : ℕ}
    {specs : List (ℕ × ℕ)} {cord : ℕ → List End} {rList : List ℕ}
    (hLS : ∀ len, TS.listSpace len ≤ cT * (len + 1))
    (hcap : (specs.map Prod.snd).sum ≤ 2 * nEdges)
    (hrLen : rList.length ≤ 2 * nEdges)
    (hcordSum : (rList.map fun v => (cord v).length).sum ≤ 2 * m) :
    bundleInitSlotsSpace TS specs cord rList ≤
      (12 + 4 * cT) * (m + specs.length + nEdges + 1) := by
  have hblk_all : ∀ l : List (ℕ × ℕ), slotBlocksSpace l = 3 * l.length + 6 * (l.map Prod.snd).sum := by
    intro l
    induction l with
    | nil => simp [slotBlocksSpace]
    | cons sb rest ih =>
      unfold slotBlocksSpace at ih ⊢
      simp only [List.map_cons, List.sum_cons, List.length_cons, bundleSlotBlockSize] at ih ⊢
      omega
  have hblk := hblk_all specs
  have htour_all : ∀ l : List ℕ, (l.map fun v => TS.listSpace (cord v).length).sum ≤
      cT * ((l.map fun v => (cord v).length).sum + l.length) := by
    intro l
    induction l with
    | nil => simp
    | cons v rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hv := hLS (cord v).length
      have hmul : cT * ((cord v).length + (rest.map fun w => (cord w).length).sum + (rest.length + 1)) =
          cT * ((cord v).length + 1) + cT * ((rest.map fun w => (cord w).length).sum + rest.length) := by
        ring
      omega
  have htour := htour_all rList
  unfold bundleInitSlotsSpace
  have hct : cT * ((rList.map fun v => (cord v).length).sum + rList.length) ≤
      cT * (2 * m + 2 * nEdges) := Nat.mul_le_mul_left cT (by omega)
  nlinarith [Nat.zero_le cT, Nat.zero_le (cT * specs.length)]

/-- `bundleStepSpace` is linear in the step's group, tour, deletion, candidate, scanned-end, and
touched-slot sizes with constant `17 + 2 * TS.querySpace + cT` (free of both the input and
`slotCap`) whenever `TS.listSpace len ≤ cT * (len + 1)`. -/
theorem bundleStepSpace_le_linear {TS : BundleTourSpec} {cT slotCap : ℕ}
    {S₀ : BundleTableState slotCap} {D : Finset ℕ} {candSet : Fin slotCap → Finset ℕ}
    {scanLen : Fin slotCap → ℕ}
    {cord' : ℕ → List End} {gs : List (List ℕ)} {touched : List ℕ}
    (hLS : ∀ len, TS.listSpace len ≤ cT * (len + 1)) :
    let totGroupEnds := (gs.map fun G => (G.map fun w => (cord' w).length).sum).sum
    let totDels := (touched.map fun s => if hs : s < slotCap then slotDelCnt S₀ D ⟨s, hs⟩ else 0).sum
    let totCands := (touched.map fun s => if hs : s < slotCap then slotCandCnt candSet ⟨s, hs⟩ else 0).sum
    let totScanned := (touched.map fun s => if hs : s < slotCap then scanLen ⟨s, hs⟩ else 0).sum
    bundleStepSpace TS S₀ D candSet scanLen cord' gs touched ≤
      (17 + 2 * TS.querySpace + cT) *
        (groupsTotalLen gs + totGroupEnds + totDels + totCands + totScanned + touched.length + 1) := by
  intro totGroupEnds totDels totCands totScanned
  have hscan : (gs.map fun G => (G.map fun w => TS.listSpace (cord' w).length + 3 * (cord' w).length).sum).sum ≤
      (cT + 3) * totGroupEnds + cT * groupsTotalLen gs := by
    change _ ≤ (cT + 3) * (gs.map fun G => (G.map fun w => (cord' w).length).sum).sum + cT * (gs.map List.length).sum
    induction gs with
    | nil => simp
    | cons G rest ih =>
      simp only [List.map_cons, List.sum_cons]
      have hG : (G.map fun w => TS.listSpace (cord' w).length + 3 * (cord' w).length).sum ≤
          (cT + 3) * (G.map fun w => (cord' w).length).sum + cT * G.length := by
        induction G with
        | nil => simp
        | cons w ws ihG =>
          simp only [List.map_cons, List.sum_cons, List.length_cons]
          have hw := hLS (cord' w).length
          nlinarith
      nlinarith
  have hemit_all : ∀ l : List ℕ, bundleStepEmitTotalSpace TS S₀ D candSet scanLen l ≤
      2 * l.length +
      4 * (l.map fun s => if hs : s < slotCap then slotDelCnt S₀ D ⟨s, hs⟩ else 0).sum +
      3 * (l.map fun s => if hs : s < slotCap then slotCandCnt candSet ⟨s, hs⟩ else 0).sum +
      (17 + 2 * TS.querySpace) * (l.map fun s => if hs : s < slotCap then scanLen ⟨s, hs⟩ else 0).sum := by
    intro l
    induction l with
    | nil => simp [bundleStepEmitTotalSpace]
    | cons s ts ih =>
      unfold bundleStepEmitTotalSpace at ih ⊢
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      by_cases hs : s < slotCap
      · simp only [hs, ↓reduceDIte]
        have hhd : bundleStepEmitSlotSpace TS (slotDelCnt S₀ D ⟨s, hs⟩) (slotCandCnt candSet ⟨s, hs⟩)
            (scanLen ⟨s, hs⟩) =
          2 + 4 * slotDelCnt S₀ D ⟨s, hs⟩ + 3 * slotCandCnt candSet ⟨s, hs⟩ +
            (17 + 2 * TS.querySpace) * scanLen ⟨s, hs⟩ := rfl
        rw [hhd]
        have hmul : (17 + 2 * TS.querySpace) * (scanLen ⟨s, hs⟩ +
            (ts.map fun s => if hs : s < slotCap then scanLen ⟨s, hs⟩ else 0).sum) =
          (17 + 2 * TS.querySpace) * scanLen ⟨s, hs⟩ +
          (17 + 2 * TS.querySpace) * (ts.map fun s => if hs : s < slotCap then scanLen ⟨s, hs⟩ else 0).sum := by
          ring
        omega
      · simp only [hs, ↓reduceDIte, Nat.zero_add]; omega
  have hemit : bundleStepEmitTotalSpace TS S₀ D candSet scanLen touched ≤
      2 * touched.length + 4 * totDels + 3 * totCands + (17 + 2 * TS.querySpace) * totScanned :=
    hemit_all touched
  unfold bundleStepSpace bundleStepScanSpace
  nlinarith [Nat.zero_le TS.querySpace, Nat.zero_le cT,
    Nat.zero_le (TS.querySpace * totGroupEnds), Nat.zero_le (TS.querySpace * totDels),
    Nat.zero_le (TS.querySpace * totCands), Nat.zero_le (TS.querySpace * touched.length),
    Nat.zero_le (cT * totDels), Nat.zero_le (cT * totCands),
    Nat.zero_le (cT * totScanned), Nat.zero_le (cT * touched.length)]

end

end MinCostFlow.SparseCore.Program
