module

public import MinCostFlow.SparseCore.BundleOutBatch
import MinCostFlow.SparseCore.CanonCoreSpec
import MinCostFlow.LSF.Lemma54Split
import MinCostFlow.SparseCore.CoreModel

/-!
# Specification of the ordered output batch

Proves the specification of the core batch (`coreBatchOf_spec`, from `canonCoreBatch_spec`), the
full validity/endpoint/length/no-reinsert specification
of `buildUSOrd` (`buildUSOrd_spec_of_coreBatch` and `buildUSOrd_spec`), and the surviving-edge
no-reinsert propagation lemma (`buildUSOrd_noReinsertPropagates`).
-/

public section

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.DynSpanner MinCostFlow.Bundle

private theorem cast_order_eq {G H : MGraph} (h : G = H) (σ : Rotation G) :
    (h ▸ σ : Rotation H).order = σ.order := by
  cases h
  rfl

private theorem batchDeletes_append (U₁ U₂ : List Update) :
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

/-- The core batch `coreBatchOf cs ord ord' U` satisfies `CoreBatchSpec` whenever `cs`
meets the component-wise LSF invariant and `U` is a valid ordered batch with split bound two
(paper Lemma 5.14, page 22). -/
theorem coreBatchOf_spec {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState} {U : List Update}
    {ord ord' : ℕ → List End} (hI : CompLSFInv C_lsst ℓ₀ cs) (ρ : Rotation cs.G)
    (σ : Rotation (cs.G.applyBatch U)) (hρ : ρ.order = ord) (hσ : σ.order = ord')
    (hrot : RotationBatch 2 U ρ σ) (hU : cs.G.BatchIsValid U) :
    CoreBatchSpec cs ord ord' U (coreBatchOf cs ord ord' U) :=
  canonCoreBatch_spec hI ρ σ hρ hσ hrot hU

/-! ## Properties of `restrictSplits` -/

/-- The length of `restrictSplits keep UC` equals the number of split updates in `UC`. -/
theorem restrictSplits_length (keep : Finset ℕ) (UC : List Update) :
    (restrictSplits keep UC).length = batchSplitCount UC := by
  induction UC with
  | nil => simp [restrictSplits, batchSplitCount]
  | cons u rest ih =>
    cases u with
    | insert => simp [restrictSplits, batchSplitCount, isSplit, ih]
    | delete => simp [restrictSplits, batchSplitCount, isSplit, ih]
    | split v v' St Sh =>
      simp only [restrictSplits, List.length_cons, batchSplitCount, List.countP_cons, isSplit,
        ↓reduceIte, ih]

/-- Every update emitted by `restrictSplits` is a split, so it never inserts any edge. -/
theorem restrictSplits_not_inserts {keep : Finset ℕ} {UC : List Update} {u : Update}
    (hu : u ∈ restrictSplits keep UC) (e : ℕ) : ¬ u.Inserts e := by
  induction UC with
  | nil => simp [restrictSplits] at hu
  | cons op rest ih =>
    cases op with
    | insert => exact ih hu
    | delete => exact ih hu
    | split v v' St Sh =>
      simp only [restrictSplits, List.mem_cons] at hu
      rcases hu with rfl | hrest
      · exact id
      · exact ih hrest

/-- Restricting the splits of a valid batch `UC` on `C` to a subgraph `S` whose edge set `keep`
is disjoint from `batchDeletes UC` produces a valid batch on `S` that preserves the vertex set
equality `S.V = C.V`, keeps `S.E = keep`, and maintains `C'.IsSubgraph S'`. -/
theorem restrictSplits_spec {C S : MGraph} {keep : Finset ℕ} {UC : List Update}
    (hCV : C.BatchIsValid UC) (hS_val : S.IsValid) (hSub : C.IsSubgraph S)
    (hV : S.V = C.V) (hE : S.E = keep) (hDisj : Disjoint keep (batchDeletes UC)) :
    let U_sp := restrictSplits keep UC
    let S' := S.applyBatch U_sp
    let C' := C.applyBatch UC
    S.BatchIsValid U_sp ∧
    S'.IsValid ∧
    C'.IsSubgraph S' ∧
    S'.V = C'.V ∧
    S'.E = keep ∧
    U_sp.length = batchSplitCount UC := by
  induction UC generalizing C S with
  | nil =>
    exact ⟨trivial, hS_val, hSub, hV, hE, by simp [restrictSplits, batchSplitCount]⟩
  | cons u rest ih =>
    have hcons : batchDeletes (u :: rest) = batchDeletes [u] ∪ batchDeletes rest := by
      simpa using batchDeletes_append [u] rest
    rw [hcons, Finset.disjoint_union_right] at hDisj
    obtain ⟨hDisj_u, hDisj_rest⟩ := hDisj
    cases u with
    | insert f a b =>
      have hSub' : (C.applyUpdate (.insert f a b)).IsSubgraph S := by
        refine ⟨hSub.1, hSub.2.1.trans (Finset.subset_insert f C.E), fun e he => ?_⟩
        have heC : e ∈ C.E := hSub.2.1 he
        have hne : e ≠ f := fun h => hCV.1.1 (h ▸ heC)
        obtain ⟨ht, hh⟩ := hSub.2.2 e he
        exact ⟨ht.trans (by simp [MGraph.applyUpdate, Function.update_of_ne hne]),
          hh.trans (by simp [MGraph.applyUpdate, Function.update_of_ne hne])⟩
      have hres := ih hCV.2 hS_val hSub' hV hE hDisj_rest
      simpa [restrictSplits, batchSplitCount, isSplit, MGraph.applyBatch] using hres
    | delete f =>
      have hfNotKeep : f ∉ keep := by
        have hfMem : f ∈ batchDeletes [.delete f] :=
          (mem_batchDeletes_iff [.delete f] f).mpr ⟨.delete f, List.mem_cons_self, rfl⟩
        exact Finset.disjoint_right.mp hDisj_u hfMem
      have hSub' : (C.applyUpdate (.delete f)).IsSubgraph S := by
        refine ⟨hSub.1, ?_, fun e he => hSub.2.2 e he⟩
        intro e he
        refine Finset.mem_erase.mpr ⟨fun h => hfNotKeep (h ▸ hE ▸ he), hSub.2.1 he⟩
      have hres := ih hCV.2 hS_val hSub' hV hE hDisj_rest
      simpa [restrictSplits, batchSplitCount, isSplit, MGraph.applyBatch] using hres
    | split v v' St Sh =>
      obtain ⟨hvC, hv'C, hStSh, hInc⟩ := hCV.1
      let uS := Update.split v v' (St ∩ keep) (Sh ∩ keep)
      have huS_val : S.UpdateIsValid uS := by
        refine ⟨hV ▸ hvC, hV ▸ hv'C, ?_, ?_⟩
        · intro e he
          rw [hE]
          rcases Finset.mem_union.mp he with ht | hh
          · exact (Finset.mem_inter.mp ht).2
          · exact (Finset.mem_inter.mp hh).2
        · intro e he
          have heS : e ∈ S.E := by
            rw [hE]
            rcases Finset.mem_union.mp he with ht | hh
            · exact (Finset.mem_inter.mp ht).2
            · exact (Finset.mem_inter.mp hh).2
          have heU : e ∈ St ∪ Sh := by
            rcases Finset.mem_union.mp he with ht | hh
            · exact Finset.mem_union_left _ (Finset.mem_inter.mp ht).1
            · exact Finset.mem_union_right _ (Finset.mem_inter.mp hh).1
          obtain ⟨ht, hh⟩ := hSub.2.2 e heS
          rcases hInc e heU with htv | hhv
          · exact Or.inl (ht.trans htv)
          · exact Or.inr (hh.trans hhv)
      let S₁ := S.applyUpdate uS
      let C₁ := C.applyUpdate (.split v v' St Sh)
      have hS₁_val : S₁.IsValid := applyUpdate_isValid hS_val huS_val
      have hS₁_V : S₁.V = C₁.V := by
        change insert v' S.V = insert v' C.V
        rw [hV]
      have hS₁_E : S₁.E = keep := hE
      have hSub₁ : C₁.IsSubgraph S₁ := by
        refine ⟨hS₁_V.le, hSub.2.1, fun e he => ?_⟩
        have heK : e ∈ keep := hE ▸ he
        obtain ⟨ht, hh⟩ := hSub.2.2 e he
        dsimp only [S₁, C₁, uS, MGraph.applyUpdate]
        rw [ht, hh]
        simp only [Finset.mem_inter, heK, and_true, and_self]
      obtain ⟨hBV, hVal, hSub', hV', hE', hLen⟩ :=
        ih hCV.2 hS₁_val hSub₁ hS₁_V hS₁_E hDisj_rest
      refine ⟨⟨huS_val, hBV⟩, hVal, hSub', hV', hE', ?_⟩
      simp only [restrictSplits, List.length_cons, batchSplitCount, List.countP_cons, isSplit,
        ↓reduceIte, hLen]

/-! ## Specification of `buildUSOrd` -/

/-- Specification of `buildUSOrd` for any core batch `UC` satisfying `CoreBatchSpec`. -/
theorem buildUSOrd_spec_of_coreBatch {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs_old : CompLSFState}
    {U UC : List Update} {ord ord' : ℕ → List End}
    (hI : CompLSFInv C_lsst ℓ₀ cs_old) (hBU : cs_old.G.BatchIsValid U)
    (ρ : Rotation cs_old.G) (σ : Rotation (cs_old.G.applyBatch U)) (hρ : ρ.order = ord)
    (hσ : σ.order = ord')
    (hUC : CoreBatchSpec cs_old ord ord' U UC)
    {S_prev : MGraph} (hS_val : S_prev.IsValid) (hS_V : S_prev.V = cs_old.RF.R)
    (hS_sub : (coreGraph cs_old.G cs_old.lsf).IsSubgraph S_prev)
    {targetE : Finset ℕ}
    (hTgt_sub : targetE ⊆ (compLSFBatch cs_old U).G.E \ (compLSFBatch cs_old U).RF.F.E)
    (D_reins : Finset ℕ) :
    let cs_new := compLSFBatch cs_old U
    let U_S := buildUSOrd UC U cs_new S_prev targetE D_reins
    let S_next := S_prev.applyBatch U_S
    let keepSet := ((S_prev.E ∩ targetE) \ batchDeletes U) \ D_reins
    S_prev.BatchIsValid U_S ∧
    S_next.IsValid ∧
    S_next.V = cs_new.RF.R ∧
    S_next.E = targetE ∧
    (∀ e ∈ S_next.E,
      S_next.tail e = cs_new.RF.root (cs_new.G.tail e) ∧
      S_next.head e = cs_new.RF.root (cs_new.G.head e)) ∧
    (coreGraph cs_new.G cs_new.lsf).IsSubgraph S_next ∧
    U_S.length = (S_prev.E \ keepSet).card + (cs_new.RF.R \ cs_old.RF.R).card +
      (targetE \ keepSet).card ∧
    (D_reins = ∅ → NoBatchReinsert cs_old.G U → NoBatchReinsert S_prev U_S) := by
  intro cs_new U_S S_next keepSet
  have hI_new := compLSFBatch_inv hI hBU
  have hcs_new_G : cs_new.G = cs_old.G.applyBatch U := compLSFBatch_G cs_old U
  have hRF_old := compLSF_RF_isRSF hI
  have hRF_new := compLSF_RF_isRSF hI_new
  have hOCB : OrderedCoreBatch 2
      (coreRotation (L := cs_old.lsf) ρ hI.hG_val hRF_old)
      (coreRotation (L := cs_new.lsf) (hcs_new_G.symm ▸ σ) hI_new.hG_val hRF_new) UC :=
    hUC.1 ρ (hcs_new_G.symm ▸ σ) hI.hG_val hRF_old hI_new.hG_val hRF_new hρ
      (by rw [cast_order_eq, hσ])
  obtain ⟨hUC_val, hUC_eq, _⟩ := hOCB
  have hUC_splits : batchSplitCount UC = (cs_new.RF.R \ cs_old.RF.R).card := hUC.2.1
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
    rw [hDel_spec.2.2.1]
    ext e
    simp only [Finset.mem_sdiff, List.mem_toFinset, Finset.mem_sort, delEdges]
    constructor
    · rintro ⟨he, hnot⟩
      by_contra hnk
      exact hnot ⟨he, hnk⟩
    · intro heK
      have hePrev : e ∈ S_prev.E :=
        (Finset.mem_inter.mp (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp heK).1).1).1
      exact ⟨hePrev, fun h => h.2 heK⟩
  have hS1_V : S_1.V = (coreGraph cs_old.G cs_old.lsf).V := hDel_spec.2.1.trans hS_V
  have hS1_val : S_1.IsValid := hDel_spec.2.2.2.2
  have hS1_sub : (coreGraph cs_old.G cs_old.lsf).IsSubgraph S_1 := by
    refine ⟨hS1_V.le, ?_, fun e he => ?_⟩
    · intro e he
      have heK : e ∈ keepSet := hS1_E ▸ he
      have hePrev : e ∈ S_prev.E :=
        (Finset.mem_inter.mp (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp heK).1).1).1
      exact hS_sub.2.1 hePrev
    · have heK : e ∈ keepSet := hS1_E ▸ he
      have hePrev : e ∈ S_prev.E :=
        (Finset.mem_inter.mp (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp heK).1).1).1
      have h1 := hDel_spec.2.2.2.1 e he
      have h2 := hS_sub.2.2 e hePrev
      exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
  have hDisj : Disjoint keepSet (batchDeletes UC) := by
    rw [Finset.disjoint_left]
    intro e heK heDel
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp heK).1).2 (hUC.2.2.2 heDel)
  obtain ⟨hSp_BV, hSp_val, hSp_sub, hSp_V, hSp_E, hSp_len⟩ :=
    restrictSplits_spec hUC_val hS1_val hS1_sub hS1_V hS1_E hDisj
  set S_2 := S_1.applyBatch splitList
  have hS2_V : S_2.V = cs_new.RF.R := hSp_V.trans hUC_eq.1.symm
  have hS2_E : S_2.E = keepSet := hSp_E
  have hS2_ends : ∀ e ∈ S_2.E,
      S_2.tail e = cs_new.RF.root (cs_new.G.tail e) ∧
      S_2.head e = cs_new.RF.root (cs_new.G.head e) := by
    intro e he
    have h1 := hSp_sub.2.2 e he
    have heC1 : e ∈ (coreGraph cs_new.G cs_new.lsf).E := hUC_eq.2.1.symm ▸ hSp_sub.2.1 he
    have h2 := hUC_eq.2.2 e heC1
    exact ⟨h1.1.trans h2.1.symm, h1.2.trans h2.2.symm⟩
  let insPairs := (insEdges.sort (· ≤ ·)).map fun e =>
    (e, cs_new.RF.root (cs_new.G.tail e), cs_new.RF.root (cs_new.G.head e))
  have hInsList_eq : insList = insPairs.map (fun t => Update.insert t.1 t.2.1 t.2.2) := by
    simp [insList, insPairs, List.map_map]
  have hIns_map_fst : insPairs.map Prod.fst = (insEdges.sort (· ≤ ·)) := by
    simp [insPairs, List.map_map, Function.comp_def]
  have hIns_nd : (insPairs.map Prod.fst).Nodup := by
    rw [hIns_map_fst]; exact Finset.sort_nodup _ (· ≤ ·)
  have hIns_notin : ∀ t ∈ insPairs, t.1 ∉ S_2.E := by
    intro t ht hmem
    rw [List.mem_map] at ht
    rcases ht with ⟨e, he, rfl⟩
    rw [hS2_E] at hmem
    exact (Finset.mem_sdiff.mp ((Finset.mem_sort (· ≤ ·)).mp he)).2 hmem
  have hIns_ends : ∀ t ∈ insPairs, t.2.1 ∈ S_2.V ∧ t.2.2 ∈ S_2.V := by
    intro t ht
    rw [List.mem_map] at ht
    rcases ht with ⟨e, he, rfl⟩
    have heTgt : e ∈ targetE := (Finset.mem_sdiff.mp ((Finset.mem_sort (· ≤ ·)).mp he)).1
    have heNew : e ∈ cs_new.G.E := (Finset.mem_sdiff.mp (hTgt_sub heTgt)).1
    have hth := hI_new.hG_val e heNew
    rw [hS2_V]
    exact ⟨(root_mem_R hRF_new hth.1).1, (root_mem_R hRF_new hth.2).1⟩
  have hIns_spec := applyUpdate_insert_list_spec hSp_val hIns_nd hIns_notin hIns_ends
  rcases hIns_spec with ⟨hIns_BV, hIns_V, hIns_E, hIns_Old, hIns_New, hIns_Val⟩
  rw [← hInsList_eq] at hIns_BV hIns_V hIns_E hIns_Old hIns_New hIns_Val
  have hUS_eq : U_S = delList ++ splitList ++ insList := rfl
  have hBV_US : S_prev.BatchIsValid U_S := by
    rw [hUS_eq, batchIsValid_append, batchIsValid_append, applyBatch_append]
    exact ⟨⟨hDel_spec.1, hSp_BV⟩, hIns_BV⟩
  have hSnext_eq : S_next = S_2.applyBatch insList := by
    dsimp only [S_next]
    rw [hUS_eq, applyBatch_append, applyBatch_append]
  have hSnext_V : S_next.V = cs_new.RF.R := by rw [hSnext_eq, hIns_V, hS2_V]
  have hSnext_E : S_next.E = targetE := by
    rw [hSnext_eq, hIns_E, hIns_map_fst, hS2_E]
    ext e
    simp only [Finset.mem_union, List.mem_toFinset, Finset.mem_sort, Finset.mem_sdiff, insEdges]
    constructor
    · rintro (heK | ⟨heT, _⟩)
      · exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp heK).1).1).2
      · exact heT
    · intro heT
      by_cases heK : e ∈ keepSet
      · exact Or.inl heK
      · exact Or.inr ⟨heT, heK⟩
  have hSnext_ends : ∀ e ∈ S_next.E,
      S_next.tail e = cs_new.RF.root (cs_new.G.tail e) ∧
      S_next.head e = cs_new.RF.root (cs_new.G.head e) := by
    intro e he
    rw [hSnext_E] at he
    by_cases heK : e ∈ keepSet
    · have heS2 : e ∈ S_2.E := hS2_E ▸ heK
      have h1 := hSnext_eq ▸ hIns_Old e heS2
      have h2 := hS2_ends e heS2
      exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
    · have heIns : e ∈ insEdges := Finset.mem_sdiff.mpr ⟨he, heK⟩
      have hePair : (e, cs_new.RF.root (cs_new.G.tail e),
          cs_new.RF.root (cs_new.G.head e)) ∈ insPairs :=
        List.mem_map.mpr ⟨e, (Finset.mem_sort (· ≤ ·)).mpr heIns, rfl⟩
      exact hSnext_eq ▸ hIns_New _ hePair
  have hSnext_sub : (coreGraph cs_new.G cs_new.lsf).IsSubgraph S_next := by
    refine ⟨hSnext_V.le, ?_, fun e he => hSnext_ends e he⟩
    rw [hSnext_E]
    exact hTgt_sub
  have hUS_len : U_S.length =
      (S_prev.E \ keepSet).card + (cs_new.RF.R \ cs_old.RF.R).card + (targetE \ keepSet).card := by
    rw [hUS_eq, List.length_append, List.length_append, hSp_len, hUC_splits]
    simp [delList, insList, delEdges, insEdges]
  refine ⟨hBV_US, hSnext_eq ▸ hIns_Val, hSnext_V, hSnext_E, hSnext_ends,
    hSnext_sub, hUS_len, fun hD0 hNoRe => ?_⟩
  intro e hePrev u_op hu hIns
  change u_op ∈ delList ++ splitList ++ insList at hu
  simp only [List.mem_append] at hu
  rcases hu with (hd | hs) | hi
  · rw [List.mem_map] at hd
    rcases hd with ⟨_, _, rfl⟩
    exact hIns
  · exact restrictSplits_not_inserts hs e hIns
  · rw [List.mem_map] at hi
    rcases hi with ⟨e', he', rfl⟩
    simp only [Update.Inserts] at hIns
    subst hIns
    have heIns : e' ∈ insEdges := (Finset.mem_sort (· ≤ ·)).mp he'
    have heTgt : e' ∈ targetE := (Finset.mem_sdiff.mp heIns).1
    have heNotKeep : e' ∉ keepSet := (Finset.mem_sdiff.mp heIns).2
    have heDel : e' ∈ batchDeletes U := by
      by_contra hnd
      exact heNotKeep (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr
        ⟨Finset.mem_inter.mpr ⟨hePrev, heTgt⟩, hnd⟩, by simp [hD0]⟩)
    have heOldG : e' ∈ cs_old.G.E := (Finset.mem_sdiff.mp (hS_sub.2.1 hePrev)).1
    have heNewG : e' ∈ cs_new.G.E := (Finset.mem_sdiff.mp (hTgt_sub heTgt)).1
    exact not_mem_applyBatch_of_delete_not_insert (hNoRe e' heOldG)
      ((mem_batchDeletes_iff U e').mp heDel) (hcs_new_G ▸ heNewG)

/-- Specification of `buildUSOrd` using `coreBatchOf`. -/
theorem buildUSOrd_spec {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs_old : CompLSFState} {U : List Update}
    {ord ord' : ℕ → List End}
    (hI : CompLSFInv C_lsst ℓ₀ cs_old) (hBU : cs_old.G.BatchIsValid U)
    (ρ : Rotation cs_old.G) (σ : Rotation (cs_old.G.applyBatch U)) (hρ : ρ.order = ord)
    (hσ : σ.order = ord') (hrot : RotationBatch 2 U ρ σ)
    {S_prev : MGraph} (hS_val : S_prev.IsValid) (hS_V : S_prev.V = cs_old.RF.R)
    (hS_sub : (coreGraph cs_old.G cs_old.lsf).IsSubgraph S_prev)
    {targetE : Finset ℕ}
    (hTgt_sub : targetE ⊆ (compLSFBatch cs_old U).G.E \ (compLSFBatch cs_old U).RF.F.E)
    (D_reins : Finset ℕ) :
    let cs_new := compLSFBatch cs_old U
    let UC := coreBatchOf cs_old ord ord' U
    let U_S := buildUSOrd UC U cs_new S_prev targetE D_reins
    let S_next := S_prev.applyBatch U_S
    let keepSet := ((S_prev.E ∩ targetE) \ batchDeletes U) \ D_reins
    S_prev.BatchIsValid U_S ∧
    S_next.IsValid ∧
    S_next.V = cs_new.RF.R ∧
    S_next.E = targetE ∧
    (∀ e ∈ S_next.E,
      S_next.tail e = cs_new.RF.root (cs_new.G.tail e) ∧
      S_next.head e = cs_new.RF.root (cs_new.G.head e)) ∧
    (coreGraph cs_new.G cs_new.lsf).IsSubgraph S_next ∧
    U_S.length = (S_prev.E \ keepSet).card + (cs_new.RF.R \ cs_old.RF.R).card +
      (targetE \ keepSet).card ∧
    (D_reins = ∅ → NoBatchReinsert cs_old.G U → NoBatchReinsert S_prev U_S) :=
  buildUSOrd_spec_of_coreBatch hI hBU ρ σ hρ hσ
    (coreBatchOf_spec hI ρ σ hρ hσ hrot hBU) hS_val hS_V hS_sub hTgt_sub D_reins

/-- Surviving-edge insertion and `D_reins`-avoidance propagation for `buildUSOrd`:
any edge `e ∈ S_prev.E ∩ targetE` that avoids insertion in `U_S` cannot belong to `D_reins`
and cannot be inserted in the input batch `U`. -/
theorem buildUSOrd_noReinsertPropagates {cs_old : CompLSFState}
    {UC U : List Update}
    (hBU : cs_old.G.BatchIsValid U)
    {S_prev : MGraph} (hS_sub : (coreGraph cs_old.G cs_old.lsf).IsSubgraph S_prev)
    {targetE D_reins : Finset ℕ} {e : ℕ}
    (hePrev : e ∈ S_prev.E) (heTgt : e ∈ targetE)
    (hNoIns : ∀ u ∈ buildUSOrd UC U (compLSFBatch cs_old U) S_prev targetE D_reins,
      ¬ u.Inserts e) :
    e ∉ D_reins ∧ ∀ u ∈ U, ¬ u.Inserts e := by
  set cs_new := compLSFBatch cs_old U
  let keepSet := ((S_prev.E ∩ targetE) \ batchDeletes U) \ D_reins
  have hmem_of_notKeep : e ∉ keepSet → False := by
    intro hnk
    have heIns : e ∈ targetE \ keepSet := Finset.mem_sdiff.mpr ⟨heTgt, hnk⟩
    have heMem : Update.insert e (cs_new.RF.root (cs_new.G.tail e))
        (cs_new.RF.root (cs_new.G.head e)) ∈
        buildUSOrd UC U cs_new S_prev targetE D_reins := by
      unfold buildUSOrd
      simp only [List.mem_append, List.mem_map]
      right
      exact ⟨e, (Finset.mem_sort (· ≤ ·)).mpr heIns, rfl⟩
    exact hNoIns _ heMem rfl
  refine ⟨fun hD => hmem_of_notKeep (fun h => (Finset.mem_sdiff.mp h).2 hD), fun u hu hIu => ?_⟩
  have heOldG : e ∈ cs_old.G.E := (Finset.mem_sdiff.mp (hS_sub.2.1 hePrev)).1
  have heDel : e ∈ batchDeletes U := mem_batchDeletes_of_inserts hBU heOldG ⟨u, hu, hIu⟩
  exact hmem_of_notKeep (fun h => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h).1).2 heDel)

end MinCostFlow.SparseCore
