module

public import MinCostFlow.SparseCore.SplitTrace
public import MinCostFlow.SparseCore.BundleOutBatchSpec

import MinCostFlow.SparseCore.GraphHelpers

/-!
# Rotation-free batch validity of `canonCoreBatch` and `buildUSOrd` (`CanonCoreValid`)

Proves that `canonCoreBatch cs U` is a valid batch transforming `coreGraph cs.G cs.lsf` into
`coreGraph (compLSFBatch cs U).G (compLSFBatch cs U).lsf` (up to `GraphEq`), deleting only edges
of `batchDeletes U`, and that `buildUSOrd (canonCoreBatch cs U) U ...` is a valid batch on `S_prev`
— using only `CompLSFInv` and `cs.G.BatchIsValid U`, with no `RotationBatch` hypotheses.

* `canonCoreBatch_valid_and_graphEq`: `(coreGraph cs.G cs.lsf).BatchIsValid (canonCoreBatch cs U)`,
  `GraphEq` to the new core graph, and `batchDeletes (canonCoreBatch cs U) ⊆ batchDeletes U`.
* `buildUSOrd_applyBatch_E_eq`: `(S_prev.applyBatch (buildUSOrd ...)).E = targetE` unconditionally.
* `buildUSOrd_batchIsValid`: `S_prev.BatchIsValid (buildUSOrd (canonCoreBatch cs U) ...)` whenever
  `S_prev` is a valid subgraph of the old core graph on `cs.RF.R` and `targetE` lies in the new
  core graph's edge set.
-/

@[expose] public section

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.Bundle MinCostFlow.DynSpanner

/-! ## 1. Validity and `GraphEq` of `refineSplit`, `releasesBatch`, and `canonCoreBatch` -/

private theorem batchDeletes_append' (U₁ U₂ : List Update) :
    batchDeletes (U₁ ++ U₂) = batchDeletes U₁ ∪ batchDeletes U₂ := by
  ext e
  simp only [Finset.mem_union, mem_batchDeletes_iff, List.mem_append]
  constructor
  · rintro ⟨u, hu | hu, heq⟩
    · exact Or.inl ⟨u, hu, heq⟩
    · exact Or.inr ⟨u, hu, heq⟩
  · rintro (⟨u, hu, heq⟩ | ⟨u, hu, heq⟩)
    · exact ⟨u, Or.inl hu, heq⟩
    · exact ⟨u, Or.inr hu, heq⟩

private theorem batchDeletes_eq_empty_of_countP_zero {U : List Update}
    (h : U.countP deleteTag = 0) : batchDeletes U = ∅ := by
  ext e
  simp only [Finset.notMem_empty, iff_false]
  intro he
  obtain ⟨u, hu, rfl⟩ := (mem_batchDeletes_iff U e).mp he
  have hpos : 0 < U.countP deleteTag := List.countP_pos_iff.mpr ⟨.delete e, hu, rfl⟩
  omega

private theorem batchIsValid_congr_graphEq {G H : MGraph} {U : List Update}
    (hEq : GraphEq G H) (hU : G.BatchIsValid U) :
    H.BatchIsValid U ∧ GraphEq (G.applyBatch U) (H.applyBatch U) := by
  induction U generalizing G H with
  | nil => exact ⟨trivial, hEq⟩
  | cons u rest ih =>
    obtain ⟨hu, hrest⟩ := hU
    have hu' : H.UpdateIsValid u := by
      cases u with
      | insert e a b =>
        dsimp only [MGraph.UpdateIsValid] at hu ⊢
        rw [← hEq.1, ← hEq.2.1]; exact hu
      | delete e =>
        dsimp only [MGraph.UpdateIsValid] at hu ⊢
        rw [← hEq.2.1]; exact hu
      | split v v' St Sh =>
        refine ⟨hEq.1 ▸ hu.1, hEq.1 ▸ hu.2.1, hEq.2.1 ▸ hu.2.2.1, fun e he => ?_⟩
        have heG : e ∈ G.E := hu.2.2.1 he
        rw [← (hEq.2.2 e heG).1, ← (hEq.2.2 e heG).2]
        exact hu.2.2.2 e he
    have hEq1 : GraphEq (G.applyUpdate u) (H.applyUpdate u) := by
      cases u with
      | insert e a b =>
        refine ⟨hEq.1, by simp [MGraph.applyUpdate, hEq.2.1], fun f hf => ?_⟩
        by_cases hfe : f = e
        · subst hfe; simp [MGraph.applyUpdate]
        · have hfG : f ∈ G.E := (Finset.mem_insert.mp hf).resolve_left hfe
          simpa [MGraph.applyUpdate, Function.update_of_ne hfe] using hEq.2.2 f hfG
      | delete e =>
        refine ⟨hEq.1, by simp [MGraph.applyUpdate, hEq.2.1], fun f hf =>
          hEq.2.2 f (Finset.mem_of_mem_erase hf)⟩
      | split v v' St Sh =>
        refine ⟨by simp [MGraph.applyUpdate, hEq.1], hEq.2.1, fun f hf => ?_⟩
        obtain ⟨ht, hh⟩ := hEq.2.2 f hf
        simp [MGraph.applyUpdate, ht, hh]
    obtain ⟨hBrest, hEqRest⟩ := ih hEq1 hrest
    exact ⟨⟨hu', hBrest⟩, hEqRest⟩

private theorem batchIsValid_append_graphEq {G G₁ G₂ : MGraph} {U₁ U₂ : List Update}
    (h1 : G.BatchIsValid U₁) (hEq1 : GraphEq G₁ (G.applyBatch U₁))
    (h2 : G₁.BatchIsValid U₂) (hEq2 : GraphEq G₂ (G₁.applyBatch U₂)) :
    G.BatchIsValid (U₁ ++ U₂) ∧ GraphEq G₂ (G.applyBatch (U₁ ++ U₂)) := by
  obtain ⟨h2', hEq2'⟩ := batchIsValid_congr_graphEq hEq1 h2
  refine ⟨batchIsValid_append.mpr ⟨h1, h2'⟩, ?_⟩
  rw [applyBatch_append]
  exact graphEq_trans hEq2 hEq2'

private theorem refineSplit_valid_and_graphEq {C C' : MGraph} {r fresh : ℕ}
    (hC : C.IsValid) (hV' : C'.V = insert fresh C.V) (hr : r ∈ C.V) (hf : fresh ∉ C.V)
    (hE : C'.E = C.E)
    (hEnds : ∀ e ∈ C.E,
      (C'.tail e = C.tail e ∨ (C.tail e = r ∧ C'.tail e = fresh)) ∧
      (C'.head e = C.head e ∨ (C.head e = r ∧ C'.head e = fresh))) :
    C.UpdateIsValid (refineSplit C C' r fresh) ∧
    GraphEq C' (C.applyUpdate (refineSplit C C' r fresh)) := by
  refine ⟨⟨hr, hf, ?_, ?_⟩, hV', hE, fun e he => ?_⟩
  · intro e he
    rcases Finset.mem_union.mp he with h | h <;> exact (Finset.mem_filter.mp h).1
  · intro e he
    rcases Finset.mem_union.mp he with h | h
    · obtain ⟨heC, ht⟩ := Finset.mem_filter.mp h
      rcases (hEnds e heC).1 with hsame | ⟨hfrom, _⟩
      · exact absurd (ht ▸ hsame ▸ (hC e heC).1) hf
      · exact Or.inl hfrom
    · obtain ⟨heC, hh⟩ := Finset.mem_filter.mp h
      rcases (hEnds e heC).2 with hsame | ⟨hfrom, _⟩
      · exact absurd (hh ▸ hsame ▸ (hC e heC).2) hf
      · exact Or.inr hfrom
  · have heC : e ∈ C.E := hE ▸ he
    simp only [refineSplit, MGraph.applyUpdate, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rcases (hEnds e heC).1 with hsame | ⟨hfrom, hto⟩
      · have hne : C.tail e ≠ fresh := fun h => hf (h ▸ (hC e heC).1)
        rw [hsame]; simp [heC, hne]
      · simp [heC, hfrom, hto]
    · rcases (hEnds e heC).2 with hsame | ⟨hfrom, hto⟩
      · have hne : C.head e ≠ fresh := fun h => hf (h ▸ (hC e heC).2)
        rw [hsame]; simp [heC, hne]
      · simp [heC, hfrom, hto]

private theorem releasesBatch_valid_and_graphEq {G : MGraph} (hG : G.IsValid)
    {L L' : LSF} (cuts : List ℕ) (hF : L.F.IsRootedSpanningForestOf G)
    (hF' : L'.F.IsRootedSpanningForestOf G) (hR : L.F.R ⊆ L'.F.R)
    (hCut : cuts.foldl eraseForestEdge L.F.F = L'.F.F)
    (hMem : ∀ e ∈ cuts, e ∈ L.F.F.E) (hn : cuts.Nodup) :
    (coreGraph G L).BatchIsValid (releasesBatch G L'.F.R L cuts) ∧
    GraphEq (coreGraph G L') ((coreGraph G L).applyBatch (releasesBatch G L'.F.R L cuts)) := by
  induction cuts generalizing L with
  | nil =>
    have hFE : L.F.F = L'.F.F := hCut
    have hRC : L.F.R.card = L'.F.R.card := by
      rw [← rootedForest_components_card hF, ← rootedForest_components_card hF', hFE]
    have hRE : L.F.R = L'.F.R := Finset.eq_of_subset_of_card_le hR hRC.ge
    have hRF_eq : L.F = L'.F := by
      cases h1 : L.F; cases h2 : L'.F
      rw [h1, h2] at hFE hRE
      exact congrArg₂ RootedForest.mk hFE hRE
    have hCoreEq : coreGraph G L' = coreGraph G L := by
      simp only [coreGraph, hRF_eq]
    rw [hCoreEq]
    exact ⟨trivial, graphEq_refl _⟩
  | cons e cuts ih =>
    let K := eraseForestEdge L.F.F e
    have he := hMem e List.mem_cons_self
    have hKn := isForest_eraseEdge hF.1 e
    have hKV : K.V = G.V := hF.2.1
    have hKsub : L.F.F.IsSubgraph K := eraseForestEdge_subgraph _ _
    have hKG : G.IsSubgraph K :=
      ⟨hF.2.2.2.2.1, fun _ hf => hF.2.2.2.2.2.1 (Finset.mem_of_mem_erase hf),
        fun f hf => hF.2.2.2.2.2.2 f (Finset.mem_of_mem_erase hf)⟩
    have hrest : cuts.foldl eraseForestEdge K = L'.F.F := hCut
    have hFinalK : K.IsSubgraph L'.F.F := by
      rw [← hrest, foldl_eraseForestEdge]
      exact ⟨Finset.Subset.rfl, Finset.sdiff_subset, fun _ _ => ⟨rfl, rfl⟩⟩
    have hsep : ∀ r₁ ∈ L.F.R, ∀ r₂ ∈ L.F.R, K.Connected r₁ r₂ → r₁ = r₂ := by
      intro r₁ hr₁ r₂ hr₂ hConn
      have hr := root_eq_of_connected hF (hF.2.2.1 hr₁) (hF.2.2.1 hr₂)
        (connected_of_subgraph hKsub hConn)
      rwa [root_eq_of_mem_R hF hr₁, root_eq_of_mem_R hF hr₂] at hr
    obtain ⟨hIncl, hSub, hMid⟩ := canonRoots_spec hKn hKV hKG hF' hFinalK hR hsep
    let Lmid : LSF := ⟨L.T, ⟨K, canonRoots K L.F.R L'.F.R⟩, L.wstr⟩
    have hComp := forest_eraseEdge_components_card hF.1 he
    change (components K).card = _ at hComp
    have hRc : (canonRoots K L.F.R L'.F.R).card = L.F.R.card + 1 := by
      rw [← rootedForest_components_card hMid, ← rootedForest_components_card hF]
      exact hComp
    obtain ⟨fresh, hf, heq⟩ := roots_insert_of_card hIncl hRc
    have hnew : newRoot Lmid.F.R L.F.R = fresh := newRoot_eq heq hf
    -- Step 1: `refineSplit` on `coreGraph G L` to `coreGraph (G.applyUpdate (.delete e)) Lmid`.
    let H := G.applyUpdate (.delete e)
    have hCval : (coreGraph G L).IsValid := coreGraph_isValid hG hF
    have hrR : L.F.root (L.F.F.tail e) ∈ L.F.R :=
      (root_mem_R hF (hF.2.1 ▸ (hF.1.1 e he).1)).1
    have hHE : (coreGraph H Lmid).E = (coreGraph G L).E := by
      ext f
      simp only [coreGraph, H, MGraph.applyUpdate, Lmid, K, eraseForestEdge, Finset.mem_sdiff,
        Finset.mem_erase]
      by_cases hfe : f = e
      · subst hfe; simp [he]
      · simp [hfe]
    have hSp := refineSplit_valid_and_graphEq (C := coreGraph G L) (C' := coreGraph H Lmid)
      (r := L.F.root (L.F.F.tail e)) (fresh := fresh) hCval heq hrR hf hHE fun f hfC => by
        have hfG : f ∈ G.E := (Finset.mem_sdiff.mp hfC).1
        have hEnd := hG f hfG
        exact ⟨eraseForestEdge_root_eq_or_fresh (L' := Lmid) hF hMid rfl he rfl heq hf hEnd.1,
          eraseForestEdge_root_eq_or_fresh (L' := Lmid) hF hMid rfl he rfl heq hf hEnd.2⟩
    -- Step 2: `.insert e ...` moves `coreGraph H Lmid` to `coreGraph G Lmid`.
    let ins := Update.insert e (Lmid.F.root (G.tail e)) (Lmid.F.root (G.head e))
    have heG : e ∈ G.E := hF.2.2.2.2.2.1 he
    have heF' : e ∉ Lmid.F.F.E := Finset.notMem_erase _ _
    have hEnds := hG e heG
    have hiV : (coreGraph H Lmid).UpdateIsValid ins :=
      ⟨fun h => (Finset.mem_erase.mp (Finset.mem_sdiff.mp h).1).1 rfl,
        (root_mem_R hMid hEnds.1).1, (root_mem_R hMid hEnds.2).1⟩
    have hiEq : GraphEq (coreGraph G Lmid) ((coreGraph H Lmid).applyUpdate ins) := by
      refine ⟨rfl, ?_, fun f _ => ?_⟩
      · change G.E \ Lmid.F.F.E = insert e (G.E.erase e \ Lmid.F.F.E)
        ext f
        by_cases h : f = e
        · subst h; simp [heG, heF']
        · simp [h]
      · change Lmid.F.root (G.tail f) = Function.update (fun f => Lmid.F.root (G.tail f)) e
          (Lmid.F.root (G.tail e)) f ∧ Lmid.F.root (G.head f) =
          Function.update (fun f => Lmid.F.root (G.head f)) e (Lmid.F.root (G.head e)) f
        by_cases hfe : f = e
        · subst hfe; simp
        · simp [Function.update_of_ne hfe]
    have hStep2 := batchIsValid_append_graphEq (U₁ := [refineSplit (coreGraph G L) (coreGraph H Lmid)
      (L.F.root (L.F.F.tail e)) fresh]) (U₂ := [ins])
      ⟨hSp.1, trivial⟩ hSp.2 ⟨hiV, trivial⟩ hiEq
    have hMemRest : ∀ f ∈ cuts, f ∈ K.E := fun f hf' =>
      Finset.mem_erase.mpr ⟨fun h => (List.nodup_cons.mp hn).1 (h ▸ hf'),
        hMem f (List.mem_cons_of_mem _ hf')⟩
    have hRest := ih (L := Lmid) hMid hSub hrest hMemRest (List.nodup_cons.mp hn).2
    have hAll := batchIsValid_append_graphEq hStep2.1 hStep2.2 hRest.1 hRest.2
    change (coreGraph G L).BatchIsValid
        (refineSplit (coreGraph G L) (coreGraph H Lmid) (L.F.root (L.F.F.tail e))
          (newRoot Lmid.F.R L.F.R) :: ins :: releasesBatch G L'.F.R Lmid cuts) ∧
      GraphEq (coreGraph G L') ((coreGraph G L).applyBatch
        (refineSplit (coreGraph G L) (coreGraph H Lmid) (L.F.root (L.F.F.tail e))
          (newRoot Lmid.F.R L.F.R) :: ins :: releasesBatch G L'.F.R Lmid cuts))
    rw [hnew]
    exact hAll

private theorem canonStepCore_valid_and_graphEq {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {u : Update} (hI : CompLSFInv C_lsst ℓ₀ cs) (hu : cs.G.UpdateIsValid u) :
    let cs' := compLSFStepSingle cs u
    (coreGraph cs.G cs.lsf).BatchIsValid (canonStepCore cs u) ∧
    GraphEq (coreGraph cs'.G cs'.lsf) ((coreGraph cs.G cs.lsf).applyBatch (canonStepCore cs u)) ∧
    batchDeletes (canonStepCore cs u) ⊆ batchDeletes [u] := by
  intro cs'
  have hI' : CompLSFInv C_lsst ℓ₀ cs' := compLSFInv_step hI hu
  have hF := compLSF_RF_isRSF hI
  have hF' : cs'.RF.IsRootedSpanningForestOf (cs.G.applyUpdate u) := compLSF_RF_isRSF hI'
  have hG' : (cs.G.applyUpdate u).IsValid := hI'.hG_val
  have hR : cs.RF.R ⊆ cs'.RF.R := (compLSFBatch_decremental (U := [u]) hI ⟨hu, trivial⟩).2
  obtain ⟨hK, hKG, hsub, hKV⟩ := compLSF_forestAfterInput' hI hu
  let K := forestAfterInput cs.RF.F u
  let cuts := (K.E \ cs'.RF.F.E).sort (· ≤ ·)
  let Fc := cuts.foldl eraseForestEdge K
  have hFcE : Fc.E = cs'.RF.F.E := by
    simp only [Fc, cuts, foldl_eraseForestEdge, Finset.sort_toFinset]
    exact Finset.sdiff_sdiff_eq_self hsub.2.1
  have hFcK : K.IsSubgraph Fc := by
    refine ⟨?_, ?_, fun _ _ => by simp [Fc, foldl_eraseForestEdge]⟩
    · simp only [Fc, foldl_eraseForestEdge]; exact Finset.Subset.rfl
    · simp only [Fc, foldl_eraseForestEdge]; exact Finset.sdiff_subset
  have hEqF : GraphEq Fc cs'.RF.F := by
    refine ⟨?_, hFcE, fun f hf => ?_⟩
    · simp only [Fc, foldl_eraseForestEdge]; exact hKV
    · obtain ⟨h1, h2⟩ := hsub.2.2 f (hFcE ▸ hf)
      simp only [Fc, foldl_eraseForestEdge]
      exact ⟨h1.symm, h2.symm⟩
  let L'' : LSF := ⟨cs'.lsf.T, ⟨Fc, cs'.RF.R⟩, cs'.lsf.wstr⟩
  have hL'' : L''.F.IsRootedSpanningForestOf (cs.G.applyUpdate u) :=
    isRootedSpanningForestOf_congr hF' rfl (graphEq_symm hEqF)
  have hKV' : K.V = (cs.G.applyUpdate u).V := hKV.trans hF'.2.1
  have hIntermediate := canonRoots_spec hK hKV' hKG hL'' hFcK hR
    (fun _ hr₁ _ hr₂ hc => forestAfterInput_root_sep' hF hu hr₁ hr₂ hc)
  have hCoreEq : GraphEq (coreGraph cs'.G cs'.lsf) (coreGraph (cs.G.applyUpdate u) L'') := by
    refine ⟨rfl, by simp [coreGraph, L'', hFcE]; rfl, fun f hf => ?_⟩
    have hfG' : f ∈ (cs.G.applyUpdate u).E := (Finset.mem_sdiff.mp hf).1
    have hEnds := hG' f hfG'
    have hSubEq : cs'.RF.F.IsSubgraph Fc := ⟨hEqF.1.le, hEqF.2.1.le, fun e he => hEqF.2.2 e he⟩
    have hRootEq : ∀ v ∈ (cs.G.applyUpdate u).V, cs'.RF.root v = L''.F.root v := fun v hv => by
      obtain ⟨hrR, hc⟩ := root_mem_R hL'' hv
      have h1 := root_eq_of_connected hF' hv (hF'.2.2.1 hrR) (connected_of_subgraph hSubEq hc)
      rwa [root_eq_of_mem_R hF' hrR] at h1
    exact ⟨hRootEq _ hEnds.1, hRootEq _ hEnds.2⟩
  -- Half 1: `inputCoreBatch cs u`.
  have hMidData :
      ∃ hm : (inputMid cs u).F.IsRootedSpanningForestOf (cs.G.applyUpdate u),
        (inputMid cs u).F.F = K ∧ (inputMid cs u).F.R ⊆ cs'.RF.R ∧
        (coreGraph cs.G cs.lsf).BatchIsValid (inputCoreBatch cs u) ∧
        GraphEq (coreGraph (cs.G.applyUpdate u) (inputMid cs u))
          ((coreGraph cs.G cs.lsf).applyBatch (inputCoreBatch cs u)) ∧
        batchDeletes (inputCoreBatch cs u) ⊆ batchDeletes [u] := by
    cases u with
    | insert e a b =>
      have hm : cs.lsf.F.IsRootedSpanningForestOf (cs.G.applyUpdate (.insert e a b)) :=
        ⟨hF.1, hF.2.1, hF.2.2.1, hF.2.2.2.1, hKG⟩
      let op := Update.insert e (cs.RF.root a) (cs.RF.root b)
      have hv : (coreGraph cs.G cs.lsf).UpdateIsValid op :=
        ⟨fun h => hu.1 (Finset.mem_sdiff.mp h).1, (root_mem_R hF hu.2.1).1,
          (root_mem_R hF hu.2.2).1⟩
      have heNotF : e ∉ cs.RF.F.E := fun h => hu.1 (hF.2.2.2.2.2.1 h)
      have hEq : GraphEq (coreGraph (cs.G.applyUpdate (.insert e a b)) cs.lsf)
          ((coreGraph cs.G cs.lsf).applyUpdate op) := by
        refine ⟨rfl, ?_, fun f _ => ?_⟩
        · ext f
          simp only [coreGraph, MGraph.applyUpdate, op, Finset.mem_sdiff, Finset.mem_insert]
          by_cases hfe : f = e
          · subst hfe
            simp only [true_or, true_and, iff_true]
            exact heNotF
          · simp [hfe]
        · by_cases hfe : f = e
          · subst hfe; simp [coreGraph, MGraph.applyUpdate, op]; exact ⟨rfl, rfl⟩
          · simp [coreGraph, MGraph.applyUpdate, op, Function.update_of_ne hfe]
      have hdel0 : ([op] : List Update).countP deleteTag = 0 := by simp [op, deleteTag]
      refine ⟨hm, rfl, hR, ⟨hv, trivial⟩, hEq, ?_⟩
      change batchDeletes [op] ⊆ _
      rw [batchDeletes_eq_empty_of_countP_zero hdel0]
      exact Finset.empty_subset _
    | delete e =>
      by_cases he : e ∈ cs.RF.F.E
      · obtain ⟨hRo, hRf, hm⟩ := hIntermediate
        let R := canonRoots K cs.RF.R cs'.RF.R
        let mid : LSF := ⟨cs.lsf.T, ⟨K, R⟩, cs.lsf.wstr⟩
        have hM : inputMid cs (.delete e) = mid := by simp only [inputMid, he, ↓reduceIte]; rfl
        have hB : inputCoreBatch cs (.delete e) =
            [refineSplit (coreGraph cs.G cs.lsf) (coreGraph (cs.G.applyUpdate (.delete e)) mid)
              (cs.RF.root (cs.RF.F.tail e)) (newRoot R cs.RF.R)] := by
          simp only [inputCoreBatch, he, ↓reduceIte, hM]; rfl
        have hcount : R.card = cs.RF.R.card + 1 := by
          rw [← rootedForest_components_card hm, ← rootedForest_components_card hF]
          exact forest_eraseEdge_components_card hF.1 he
        obtain ⟨fresh, hnew, hR'⟩ := roots_insert_of_card hRo hcount
        have hnr : newRoot R cs.RF.R = fresh := newRoot_eq hR' hnew
        have hCE : (coreGraph (cs.G.applyUpdate (.delete e)) mid).E = (coreGraph cs.G cs.lsf).E := by
          ext f
          simp only [coreGraph, MGraph.applyUpdate, mid, K, forestAfterInput, eraseForestEdge,
            Finset.mem_sdiff, Finset.mem_erase]
          by_cases hfe : f = e
          · subst hfe
            exact ⟨fun h => absurd rfl h.1.1, fun h => absurd he h.2⟩
          · simp [hfe]; exact fun _ => Iff.rfl
        have hrR : cs.RF.root (cs.RF.F.tail e) ∈ cs.RF.R :=
          (root_mem_R hF (hF.2.1 ▸ (hF.1.1 e he).1)).1
        have hSp := refineSplit_valid_and_graphEq (coreGraph_isValid hI.hG_val hF)
          hR' hrR hnew hCE fun f hfC => by
            have hfG : f ∈ cs.G.E := (Finset.mem_sdiff.mp hfC).1
            have hEnd := hI.hG_val f hfG
            exact ⟨eraseForestEdge_root_eq_or_fresh (L := cs.lsf) (L' := mid) hF hm rfl he rfl hR' hnew hEnd.1,
              eraseForestEdge_root_eq_or_fresh (L := cs.lsf) (L' := mid) hF hm rfl he rfl hR' hnew hEnd.2⟩
        have hdel0 : ([refineSplit (coreGraph cs.G cs.lsf)
            (coreGraph (cs.G.applyUpdate (.delete e)) mid) (cs.RF.root (cs.RF.F.tail e)) fresh] :
            List Update).countP deleteTag = 0 := by simp [refineSplit, deleteTag]
        refine ⟨hM.symm ▸ hm, by rw [hM], by rw [hM]; exact hRf, ?_, ?_, ?_⟩
        · rw [hB, hnr]; exact ⟨hSp.1, trivial⟩
        · rw [hB, hM, hnr]; exact hSp.2
        · rw [hB, hnr, batchDeletes_eq_empty_of_countP_zero hdel0]; exact Finset.empty_subset _
      · have hK_eq : K = cs.RF.F := by
          change { cs.RF.F with E := cs.RF.F.E.erase e } = cs.RF.F
          exact congrArg (fun E => { cs.RF.F with E := E }) (Finset.erase_eq_of_notMem he)
        have hM : inputMid cs (.delete e) = cs.lsf := by simp only [inputMid, he, ↓reduceIte]
        have hB : inputCoreBatch cs (.delete e) = [.delete e] := by
          simp only [inputCoreBatch, he, ↓reduceIte]
        have hm : cs.lsf.F.IsRootedSpanningForestOf (cs.G.applyUpdate (.delete e)) :=
          ⟨hF.1, hF.2.1, hF.2.2.1, hF.2.2.2.1, hK_eq ▸ hKG⟩
        have hv : (coreGraph cs.G cs.lsf).UpdateIsValid (.delete e) := Finset.mem_sdiff.mpr ⟨hu, he⟩
        have hEq : GraphEq (coreGraph (cs.G.applyUpdate (.delete e)) cs.lsf)
            ((coreGraph cs.G cs.lsf).applyUpdate (.delete e)) := by
          refine ⟨rfl, ?_, fun _ _ => ⟨rfl, rfl⟩⟩
          ext f
          simp only [coreGraph, MGraph.applyUpdate, Finset.mem_sdiff, Finset.mem_erase]
          tauto
        refine ⟨hM.symm ▸ hm, by rw [hM, hK_eq]; rfl, by rw [hM]; exact hR, ?_, ?_, ?_⟩
        · rw [hB]; exact ⟨hv, trivial⟩
        · rw [hB, hM]; exact hEq
        · rw [hB]
    | split v v' St Sh =>
      obtain ⟨hRo, hRf, hm⟩ := hIntermediate
      let R := canonRoots K cs.RF.R cs'.RF.R
      let mid : LSF := ⟨cs.lsf.T, ⟨K, R⟩, cs.lsf.wstr⟩
      have hcount : R.card = cs.RF.R.card + 1 := by
        have ho := rootedForest_R_add_edges hF
        have hn := rootedForest_R_add_edges hm
        have hv : (cs.G.applyUpdate (.split v v' St Sh)).V.card = cs.G.V.card + 1 :=
          Finset.card_insert_of_notMem hu.2.1
        change R.card + cs.RF.F.E.card = (cs.G.applyUpdate (.split v v' St Sh)).V.card at hn
        omega
      obtain ⟨fresh, hnew, hR'⟩ := roots_insert_of_card hRo hcount
      have hnr : newRoot R cs.RF.R = fresh := newRoot_eq hR' hnew
      have hrR : cs.RF.root v ∈ cs.RF.R := (root_mem_R hF hu.1).1
      have hSp := refineSplit_valid_and_graphEq (C := coreGraph cs.G cs.lsf)
        (C' := coreGraph (cs.G.applyUpdate (.split v v' St Sh)) mid)
        (coreGraph_isValid hI.hG_val hF) hR' hrR hnew rfl fun f hfC => by
          have hfG : f ∈ cs.G.E := (Finset.mem_sdiff.mp hfC).1
          have hEnd := hI.hG_val f hfG
          have hT : (cs.G.applyUpdate (.split v v' St Sh)).tail f = cs.G.tail f ∨
              (cs.G.tail f = v ∧ (cs.G.applyUpdate (.split v v' St Sh)).tail f = v') := by
            by_cases ht : f ∈ St ∧ cs.G.tail f = v
            · right; exact ⟨ht.2, by simp [MGraph.applyUpdate, ht]⟩
            · left; simp [MGraph.applyUpdate, ht]
          have hH : (cs.G.applyUpdate (.split v v' St Sh)).head f = cs.G.head f ∨
              (cs.G.head f = v ∧ (cs.G.applyUpdate (.split v v' St Sh)).head f = v') := by
            by_cases hh : f ∈ Sh ∧ cs.G.head f = v
            · right; exact ⟨hh.2, by simp [MGraph.applyUpdate, hh]⟩
            · left; simp [MGraph.applyUpdate, hh]
          exact ⟨applySplit_root_eq_or_fresh (L := cs.lsf) (L' := mid) hF hm rfl hR' hnew hu hEnd.1 hT,
            applySplit_root_eq_or_fresh (L := cs.lsf) (L' := mid) hF hm rfl hR' hnew hu hEnd.2 hH⟩
      have hdel0 : ([refineSplit (coreGraph cs.G cs.lsf)
          (coreGraph (cs.G.applyUpdate (.split v v' St Sh)) mid) (cs.RF.root v) fresh] :
          List Update).countP deleteTag = 0 := by simp [refineSplit, deleteTag]
      refine ⟨hm, rfl, hRf, ?_, ?_, ?_⟩
      · change (coreGraph cs.G cs.lsf).BatchIsValid [refineSplit _ _ _ (newRoot R cs.RF.R)]
        rw [hnr]; exact ⟨hSp.1, trivial⟩
      · change GraphEq (coreGraph _ mid) ((coreGraph cs.G cs.lsf).applyBatch
          [refineSplit _ _ _ (newRoot R cs.RF.R)])
        rw [hnr]; exact hSp.2
      · change batchDeletes [refineSplit (coreGraph cs.G cs.lsf)
          (coreGraph (cs.G.applyUpdate (.split v v' St Sh)) mid) (cs.RF.root v)
          (newRoot R cs.RF.R)] ⊆ _
        rw [hnr, batchDeletes_eq_empty_of_countP_zero hdel0]; exact Finset.empty_subset _
  obtain ⟨hm, hmidF, hmR, hV1, hEq1, hDel1⟩ := hMidData
  -- Half 2: `releasesBatch`.
  have hCut : cuts.foldl eraseForestEdge (inputMid cs u).F.F = L''.F.F := by rw [hmidF]
  have hMem : ∀ e ∈ cuts, e ∈ (inputMid cs u).F.F.E := fun e he => by
    rw [hmidF]
    exact (Finset.mem_sdiff.mp ((Finset.mem_sort (· ≤ ·)).mp he)).1
  have hRel := releasesBatch_valid_and_graphEq hG' cuts hm hL'' hmR hCut hMem (Finset.sort_nodup _ _)
  have hAll := batchIsValid_append_graphEq hV1 hEq1 hRel.1 hRel.2
  refine ⟨hAll.1, graphEq_trans hCoreEq hAll.2, ?_⟩
  unfold canonStepCore
  rw [batchDeletes_append', batchDeletes_eq_empty_of_countP_zero
    (releasesBatch_countP_delete _ _ _ _), Finset.union_empty]
  exact hDel1

/-- **Rotation-free validity and `GraphEq` of `canonCoreBatch`.** -/
theorem canonCoreBatch_valid_and_graphEq {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {U : List Update} (hI : CompLSFInv C_lsst ℓ₀ cs) (hU : cs.G.BatchIsValid U) :
    let cs' := compLSFBatch cs U
    (coreGraph cs.G cs.lsf).BatchIsValid (canonCoreBatch cs U) ∧
    GraphEq (coreGraph cs'.G cs'.lsf) ((coreGraph cs.G cs.lsf).applyBatch (canonCoreBatch cs U)) ∧
    batchDeletes (canonCoreBatch cs U) ⊆ batchDeletes U := by
  induction U generalizing cs with
  | nil => exact ⟨trivial, graphEq_refl _, Finset.Subset.rfl⟩
  | cons u rest ih =>
    obtain ⟨hu, hrest⟩ := hU
    have h1 := canonStepCore_valid_and_graphEq hI hu
    have hI1 : CompLSFInv C_lsst ℓ₀ (compLSFStepSingle cs u) := compLSFInv_step hI hu
    have h2 := ih hI1 hrest
    have hAll := batchIsValid_append_graphEq h1.1 h1.2.1 h2.1 h2.2.1
    refine ⟨hAll.1, hAll.2, ?_⟩
    change batchDeletes (canonStepCore cs u ++ canonCoreBatch (compLSFStepSingle cs u) rest) ⊆ _
    rw [batchDeletes_append']
    have hcons : batchDeletes (u :: rest) = batchDeletes [u] ∪ batchDeletes rest := by
      simpa using batchDeletes_append' [u] rest
    rw [hcons]
    exact Finset.union_subset_union h1.2.2 h2.2.2

/-! ## 2. Unconditional edge set and rotation-free validity of `buildUSOrd` -/

private theorem applyBatch_map_delete_E (G : MGraph) (es : List ℕ) :
    (G.applyBatch (es.map Update.delete)).E = G.E \ es.toFinset := by
  induction es generalizing G with
  | nil => simp [MGraph.applyBatch]
  | cons e rest ih =>
    simp only [List.map_cons, MGraph.applyBatch, List.foldl_cons]
    change ((G.applyUpdate (.delete e)).applyBatch (rest.map Update.delete)).E = _
    rw [ih]
    ext f
    simp [MGraph.applyUpdate]
    tauto

private theorem applyBatch_restrictSplits_E (G : MGraph) (keep : Finset ℕ) (UC : List Update) :
    (G.applyBatch (restrictSplits keep UC)).E = G.E := by
  induction UC generalizing G with
  | nil => rfl
  | cons u rest ih =>
    cases u with
    | insert _ _ _ => exact ih G
    | delete _ => exact ih G
    | split v v' St Sh =>
      change ((G.applyUpdate (.split v v' (St ∩ keep) (Sh ∩ keep))).applyBatch
        (restrictSplits keep rest)).E = G.E
      rw [ih]; rfl

private theorem applyBatch_map_insert_E (G : MGraph) (es : List ℕ) (t h : ℕ → ℕ) :
    (G.applyBatch (es.map fun e => Update.insert e (t e) (h e))).E = G.E ∪ es.toFinset := by
  induction es generalizing G with
  | nil => simp [MGraph.applyBatch]
  | cons e rest ih =>
    simp only [List.map_cons, MGraph.applyBatch, List.foldl_cons]
    change ((G.applyUpdate (.insert e (t e) (h e))).applyBatch
      (rest.map fun e => Update.insert e (t e) (h e))).E = _
    rw [ih]
    ext f
    simp [MGraph.applyUpdate]

/-- Applying `buildUSOrd` always produces edge set `targetE` (unconditionally). -/
theorem buildUSOrd_applyBatch_E_eq (UC U : List Update) (cs_new : CompLSFState)
    (S_prev : MGraph) (targetE D_reins : Finset ℕ) :
    (S_prev.applyBatch (buildUSOrd UC U cs_new S_prev targetE D_reins)).E = targetE := by
  unfold buildUSOrd
  rw [applyBatch_append, applyBatch_append, applyBatch_map_insert_E, applyBatch_restrictSplits_E,
    applyBatch_map_delete_E, Finset.sort_toFinset, Finset.sort_toFinset]
  set keepSet := ((S_prev.E ∩ targetE) \ batchDeletes U) \ D_reins
  have hsubS : keepSet ⊆ S_prev.E := fun e he =>
    (Finset.mem_inter.mp (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp he).1).1).1
  have hsubT : keepSet ⊆ targetE := fun e he =>
    (Finset.mem_inter.mp (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp he).1).1).2
  rw [Finset.sdiff_sdiff_eq_self hsubS, Finset.union_sdiff_of_subset hsubT]

/-- **Rotation-free batch validity of `buildUSOrd`** using `canonCoreBatch`. -/
theorem buildUSOrd_batchIsValid {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs_old : CompLSFState}
    {U : List Update} (hI : CompLSFInv C_lsst ℓ₀ cs_old) (hBU : cs_old.G.BatchIsValid U)
    {S_prev : MGraph} (hS_val : S_prev.IsValid) (hS_V : S_prev.V = cs_old.RF.R)
    (hS_sub : (coreGraph cs_old.G cs_old.lsf).IsSubgraph S_prev)
    {targetE : Finset ℕ}
    (hTgt_sub : targetE ⊆ (compLSFBatch cs_old U).G.E \ (compLSFBatch cs_old U).RF.F.E)
    (D_reins : Finset ℕ) :
    S_prev.BatchIsValid
      (buildUSOrd (canonCoreBatch cs_old U) U (compLSFBatch cs_old U) S_prev targetE D_reins) := by
  set cs_new := compLSFBatch cs_old U
  set UC := canonCoreBatch cs_old U
  have hI_new := compLSFBatch_inv hI hBU
  have hRF_new := compLSF_RF_isRSF hI_new
  obtain ⟨hUC_val, hUC_eq, hUC_del⟩ := canonCoreBatch_valid_and_graphEq hI hBU
  let keepSet := ((S_prev.E ∩ targetE) \ batchDeletes U) \ D_reins
  let delEdges := S_prev.E \ keepSet
  let insEdges := targetE \ keepSet
  let delList := (delEdges.sort (· ≤ ·)).map Update.delete
  let splitList := restrictSplits keepSet UC
  let insList := (insEdges.sort (· ≤ ·)).map fun e =>
    Update.insert e (cs_new.RF.root (cs_new.G.tail e)) (cs_new.RF.root (cs_new.G.head e))
  have hDel_spec := applyUpdate_delete_list_spec hS_val (Finset.sort_nodup delEdges (· ≤ ·))
    (fun e he => Finset.sdiff_subset ((Finset.mem_sort (· ≤ ·)).mp he))
  set S_1 := S_prev.applyBatch delList
  have hS1_E : S_1.E = keepSet := by
    rw [hDel_spec.2.2.1, Finset.sort_toFinset]
    exact Finset.sdiff_sdiff_eq_self fun e he =>
      (Finset.mem_inter.mp (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp he).1).1).1
  have hS1_V : S_1.V = (coreGraph cs_old.G cs_old.lsf).V := hDel_spec.2.1.trans hS_V
  have hS1_val : S_1.IsValid := hDel_spec.2.2.2.2
  have hS1_sub : (coreGraph cs_old.G cs_old.lsf).IsSubgraph S_1 := by
    refine ⟨hS1_V.le, ?_, fun e he => ?_⟩
    · intro e he
      have hePrev : e ∈ S_prev.E :=
        (Finset.mem_inter.mp (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (hS1_E ▸ he)).1).1).1
      exact hS_sub.2.1 hePrev
    · have hePrev : e ∈ S_prev.E :=
        (Finset.mem_inter.mp (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (hS1_E ▸ he)).1).1).1
      have h1 := hDel_spec.2.2.2.1 e he
      have h2 := hS_sub.2.2 e hePrev
      exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
  have hDisj : Disjoint keepSet (batchDeletes UC) := by
    rw [Finset.disjoint_left]
    intro e heK heDel
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp heK).1).2 (hUC_del heDel)
  obtain ⟨hSp_BV, hSp_val, _, hSp_V, hSp_E, _⟩ :=
    restrictSplits_spec hUC_val hS1_val hS1_sub hS1_V hS1_E hDisj
  set S_2 := S_1.applyBatch splitList
  have hS2_V : S_2.V = cs_new.RF.R := hSp_V.trans hUC_eq.1.symm
  let insTriples := (insEdges.sort (· ≤ ·)).map fun e =>
    (e, cs_new.RF.root (cs_new.G.tail e), cs_new.RF.root (cs_new.G.head e))
  have hIns_list_eq : insList = insTriples.map fun t => Update.insert t.1 t.2.1 t.2.2 := by
    simp [insList, insTriples, List.map_map]
  have hIns_nd : (insTriples.map Prod.fst).Nodup := by
    simp [insTriples, List.map_map, Function.comp_def, Finset.sort_nodup]
  have hIns_notin : ∀ t ∈ insTriples, t.1 ∉ S_2.E := by
    intro t ht
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht
    rw [hSp_E]
    exact (Finset.mem_sdiff.mp ((Finset.mem_sort (· ≤ ·)).mp he)).2
  have hIns_ends : ∀ t ∈ insTriples, t.2.1 ∈ S_2.V ∧ t.2.2 ∈ S_2.V := by
    intro t ht
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht
    have heT : e ∈ targetE := (Finset.mem_sdiff.mp ((Finset.mem_sort (· ≤ ·)).mp he)).1
    have heG : e ∈ cs_new.G.E := (Finset.mem_sdiff.mp (hTgt_sub heT)).1
    have hEnds := hI_new.hG_val e heG
    rw [hS2_V]
    exact ⟨(root_mem_R hRF_new hEnds.1).1, (root_mem_R hRF_new hEnds.2).1⟩
  have hIns_BV : S_2.BatchIsValid insList := by
    rw [hIns_list_eq]
    exact (applyUpdate_insert_list_spec hSp_val hIns_nd hIns_notin hIns_ends).1
  unfold buildUSOrd
  exact batchIsValid_append.mpr ⟨batchIsValid_append.mpr ⟨hDel_spec.1, hSp_BV⟩, by
    rw [applyBatch_append]; exact hIns_BV⟩

/-! ## 4. Unconditional vertex set of `S_prev.applyBatch (buildUSOrd ...)` -/

private lemma applyBatch_V_eq_of_V_eq {G₁ G₂ : MGraph} (hV : G₁.V = G₂.V) :
    ∀ U : List Update, (G₁.applyBatch U).V = (G₂.applyBatch U).V
  | [] => hV
  | u :: U => by
    simp only [MGraph.applyBatch, List.foldl_cons]
    apply applyBatch_V_eq_of_V_eq
    cases u <;> simp [MGraph.applyUpdate, hV]

private lemma applyBatch_V_restrictSplits (keep : Finset ℕ) :
    ∀ (G : MGraph) (UC : List Update),
      (G.applyBatch (restrictSplits keep UC)).V = (G.applyBatch UC).V
  | _, [] => rfl
  | G, .insert e u v :: UC => by
    simp only [restrictSplits, MGraph.applyBatch, List.foldl_cons]
    exact (applyBatch_V_restrictSplits keep G UC).trans
      (applyBatch_V_eq_of_V_eq (by simp [MGraph.applyUpdate]) UC)
  | G, .delete e :: UC => by
    simp only [restrictSplits, MGraph.applyBatch, List.foldl_cons]
    exact (applyBatch_V_restrictSplits keep G UC).trans
      (applyBatch_V_eq_of_V_eq (by simp [MGraph.applyUpdate]) UC)
  | G, .split v v' St Sh :: UC => by
    simp only [restrictSplits, MGraph.applyBatch, List.foldl_cons]
    exact (applyBatch_V_restrictSplits keep _ UC).trans
      (applyBatch_V_eq_of_V_eq (by simp [MGraph.applyUpdate]) UC)

private lemma applyBatch_V_of_noSplit :
    ∀ (G : MGraph) (U : List Update), (∀ u ∈ U, ∀ v v' St Sh, u ≠ .split v v' St Sh) →
      (G.applyBatch U).V = G.V
  | _, [], _ => rfl
  | G, u :: U, h => by
    simp only [MGraph.applyBatch, List.foldl_cons]
    have hu : (G.applyUpdate u).V = G.V := by
      cases u with
      | insert _ _ _ => rfl
      | delete _ => rfl
      | split v v' St Sh => exact absurd rfl (h _ (List.mem_cons_self ..) v v' St Sh)
    exact (applyBatch_V_of_noSplit _ U (fun x hx => h x (List.mem_cons_of_mem _ hx))).trans hu

/-- **Unconditional vertex-set preservation of `buildUSOrd`:** whenever `S_prev.V = cs_old.RF.R`,
applying `buildUSOrd (canonCoreBatch cs_old U) U (compLSFBatch cs_old U) S_prev targetE D_reins`
yields vertex set `(compLSFBatch cs_old U).RF.R`, with no assumptions on `targetE`, `D_reins`, or
`S_prev.IsValid`. -/
theorem buildUSOrd_applyBatch_V {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs_old : CompLSFState} {U : List Update}
    (hI : CompLSFInv C_lsst ℓ₀ cs_old) (hBU : cs_old.G.BatchIsValid U)
    {S_prev : MGraph} (hS_V : S_prev.V = cs_old.RF.R) (targetE D_reins : Finset ℕ) :
    (S_prev.applyBatch
      (buildUSOrd (canonCoreBatch cs_old U) U (compLSFBatch cs_old U) S_prev targetE D_reins)).V =
      (compLSFBatch cs_old U).RF.R := by
  have hUC_eq := (canonCoreBatch_valid_and_graphEq hI hBU).2.1
  unfold buildUSOrd
  rw [applyBatch_append, applyBatch_append]
  rw [applyBatch_V_of_noSplit _ _ (fun u hu => by
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hu; intro _ _ _ _ h; cases h)]
  rw [applyBatch_V_restrictSplits]
  have hDelV : (S_prev.applyBatch (((S_prev.E \ (((S_prev.E ∩ targetE) \ batchDeletes U) \ D_reins)).sort
      (· ≤ ·)).map Update.delete)).V = (coreGraph cs_old.G cs_old.lsf).V :=
    (applyBatch_V_of_noSplit _ _ (fun u hu => by
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hu; intro _ _ _ _ h; cases h)).trans hS_V
  exact (applyBatch_V_eq_of_V_eq hDelV _).trans hUC_eq.1.symm

end MinCostFlow.SparseCore
