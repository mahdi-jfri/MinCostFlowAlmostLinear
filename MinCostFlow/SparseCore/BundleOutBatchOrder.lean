module

public import MinCostFlow.Bundle.CoreSubgraph
public import MinCostFlow.SparseCore.BundleOutBatchSpec

/-!
# One-step order preservation for `buildUSOrd`

Shows that `buildUSOrd UC U cs_new S_prev targetE D_reins` forms a `CoreSubgraphBatch 2`
between the core views before and after the batch:
1. Deleting edges from `S_prev` keeps the initial core graph and rotation fixed.
2. Applying `restrictSplits keepSet UC` follows the ordered core batch `UC`, skipping
   core edge edits outside `keepSet` and restricting each core split to `keepSet`.
3. Inserting the new edges of `targetE \ keepSet` keeps the final core graph and rotation fixed.
-/

public section

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.DynSpanner MinCostFlow.Bundle

private theorem cast_order_eq' {G H : MGraph} (h : G = H) (σ : Rotation G) :
    (h ▸ σ : Rotation H).order = σ.order := by
  cases h
  rfl

/-- Deleting a list of edges from a subgraph keeps the ambient core fixed and forms a
`CoreSubgraphBatch`. -/
theorem coreSubgraphBatch_delete_list {β : ℕ} {C H : MGraph} (ρ : Rotation C)
    (hSub : C.IsSubgraph H) (L : List ℕ)
    (hSub' : C.IsSubgraph (H.applyBatch (L.map Update.delete))) :
    CoreSubgraphBatch β (L.map Update.delete) ⟨C, ρ, hSub⟩ ⟨C, ρ, hSub'⟩ := by
  induction L generalizing H with
  | nil => exact .nil _
  | cons e L ih =>
    have hSub₁ : C.IsSubgraph (H.applyUpdate (.delete e)) :=
      ⟨hSub.1, (Finset.erase_subset e H.E).trans hSub.2.1,
        fun f hf => hSub.2.2 f (Finset.mem_of_mem_erase hf)⟩
    exact .delete (b := ⟨C, ρ, hSub₁⟩) (fun _ => .refl _) (ih hSub₁ hSub')

/-- Inserting a list of edges of `C` at their endpoints in `C` keeps the ambient core fixed
and forms a `CoreSubgraphBatch`. -/
theorem coreSubgraphBatch_insert_list {β : ℕ} {C H : MGraph} (ρ : Rotation C)
    (hSub : C.IsSubgraph H) (L : List ℕ) (hL : ∀ e ∈ L, e ∈ C.E)
    (hSub' : C.IsSubgraph (H.applyBatch (L.map fun e => Update.insert e (C.tail e) (C.head e)))) :
    CoreSubgraphBatch β (L.map fun e => Update.insert e (C.tail e) (C.head e))
      ⟨C, ρ, hSub⟩ ⟨C, ρ, hSub'⟩ := by
  induction L generalizing H with
  | nil => exact .nil _
  | cons e L ih =>
    have heC : e ∈ C.E := hL e List.mem_cons_self
    have hSub₁ : C.IsSubgraph (H.applyUpdate (.insert e (C.tail e) (C.head e))) := by
      refine ⟨hSub.1, Finset.insert_subset heC hSub.2.1, fun f hf => ?_⟩
      rcases Finset.mem_insert.mp hf with rfl | hfH
      · simp [MGraph.applyUpdate]
      · by_cases hfe : f = e
        · subst hfe; simp [MGraph.applyUpdate]
        · obtain ⟨ht, hh⟩ := hSub.2.2 f hfH
          simp [MGraph.applyUpdate, Function.update_of_ne hfe, ht, hh]
    exact .insert (b := ⟨C, ρ, hSub₁⟩) (fun _ => .refl _)
      (ih hSub₁ (fun f hf => hL f (List.mem_cons_of_mem _ hf)) hSub')

private theorem coreSubgraphBatch_split_cast {β : ℕ} {H : MGraph} {U : List Update}
    {v v' : ℕ} {St Sh keep : Finset ℕ} (hE : H.E = keep)
    {a : CoreView H}
    {b : CoreView (H.applyUpdate (.split v v' (St ∩ keep) (Sh ∩ keep)))}
    {c : CoreView ((H.applyUpdate (.split v v' (St ∩ keep) (Sh ∩ keep))).applyBatch U)}
    (he : GraphEq b.graph (a.graph.applyUpdate (.split v v' St Sh)))
    (hs : RotationStep β (.split v v' St Sh) a.rotation (b.rotation.congrGraph he))
    (hrest : CoreSubgraphBatch β U b c) :
    CoreSubgraphBatch β (.split v v' (St ∩ keep) (Sh ∩ keep) :: U) a c := by
  subst hE
  exact .split he hs hrest

private theorem batchDeletes_cons_eq (u : Update) (rest : List Update) :
    batchDeletes (u :: rest) = batchDeletes [u] ∪ batchDeletes rest := by
  ext e
  simp only [Finset.mem_union, mem_batchDeletes_iff, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨x, rfl | hx, heq⟩
    · exact Or.inl ⟨x, rfl, heq⟩
    · exact Or.inr ⟨x, hx, heq⟩
  · rintro (⟨x, rfl, heq⟩ | ⟨x, hx, heq⟩)
    · exact ⟨x, Or.inl rfl, heq⟩
    · exact ⟨x, Or.inr hx, heq⟩

/-- Following an ordered core batch `UC` via `restrictSplits keep UC` on a subgraph `S` whose
edge set `keep` is disjoint from `batchDeletes UC` forms a `CoreSubgraphBatch`. -/
theorem coreSubgraphBatch_restrictSplits {β : ℕ} {C S : MGraph} {keep : Finset ℕ}
    {UC : List Update} {ρ : Rotation C} {σ : Rotation (C.applyBatch UC)}
    (hRot : RotationBatch β UC ρ σ) (hCV : C.BatchIsValid UC)
    (hSub : C.IsSubgraph S) (hV : S.V = C.V) (hE : S.E = keep)
    (hDisj : Disjoint keep (batchDeletes UC))
    (hSub' : (C.applyBatch UC).IsSubgraph (S.applyBatch (restrictSplits keep UC))) :
    CoreSubgraphBatch β (restrictSplits keep UC) ⟨C, ρ, hSub⟩ ⟨C.applyBatch UC, σ, hSub'⟩ := by
  induction hRot generalizing S with
  | nil hr => exact .skip (fun w => isRotated_filter _ (hr w)) (.nil _)
  | @cons C u rest ρ ρ' σ hs _ ih =>
    rw [batchDeletes_cons_eq, Finset.disjoint_union_right] at hDisj
    obtain ⟨hDisj_u, hDisj_rest⟩ := hDisj
    cases u with
    | insert f a b =>
      have hfNotS : f ∉ S.E := fun hf => hCV.1.1 (hSub.2.1 hf)
      have hSub₁ : (C.applyUpdate (.insert f a b)).IsSubgraph S := by
        refine ⟨hSub.1, hSub.2.1.trans (Finset.subset_insert f C.E), fun e he => ?_⟩
        have hne : e ≠ f := fun h => hfNotS (h ▸ he)
        obtain ⟨ht, hh⟩ := hSub.2.2 e he
        exact ⟨ht.trans (by simp [MGraph.applyUpdate, Function.update_of_ne hne]),
          hh.trans (by simp [MGraph.applyUpdate, Function.update_of_ne hne])⟩
      exact CoreSubgraphBatch.coreInsert (b := ⟨C.applyUpdate (.insert f a b), ρ', hSub₁⟩)
        hfNotS (graphEq_refl _) hs (ih hCV.2 hSub₁ hV hE hDisj_rest hSub')
    | delete f =>
      have hfNotKeep : f ∉ keep := by
        have hfMem : f ∈ batchDeletes [.delete f] :=
          (mem_batchDeletes_iff [.delete f] f).mpr ⟨.delete f, List.mem_cons_self, rfl⟩
        exact Finset.disjoint_right.mp hDisj_u hfMem
      have hfNotS : f ∉ S.E := hE.symm ▸ hfNotKeep
      have hSub₁ : (C.applyUpdate (.delete f)).IsSubgraph S := by
        refine ⟨hSub.1, ?_, fun e he => hSub.2.2 e he⟩
        intro e he
        exact Finset.mem_erase.mpr ⟨fun h => hfNotS (h ▸ he), hSub.2.1 he⟩
      exact CoreSubgraphBatch.coreDelete (b := ⟨C.applyUpdate (.delete f), ρ', hSub₁⟩)
        hfNotS (graphEq_refl _) hs (ih hCV.2 hSub₁ hV hE hDisj_rest hSub')
    | split v v' St Sh =>
      let S₁ := S.applyUpdate (.split v v' (St ∩ keep) (Sh ∩ keep))
      let C₁ := C.applyUpdate (.split v v' St Sh)
      have hV₁ : S₁.V = C₁.V := by
        change insert v' S.V = insert v' C.V
        rw [hV]
      have hE₁ : S₁.E = keep := hE
      have hSub₁ : C₁.IsSubgraph S₁ := by
        refine ⟨hV₁.le, hSub.2.1, fun e he => ?_⟩
        have heK : e ∈ keep := hE ▸ he
        obtain ⟨ht, hh⟩ := hSub.2.2 e he
        dsimp only [S₁, C₁, MGraph.applyUpdate]
        rw [ht, hh]
        simp only [Finset.mem_inter, heK, and_true, and_self]
      exact coreSubgraphBatch_split_cast hE (b := ⟨C₁, ρ', hSub₁⟩) (graphEq_refl _) hs
        (ih hCV.2 hSub₁ hV₁ hE₁ hDisj_rest hSub')

private theorem coreSubgraphBatch_append3 {β : ℕ} {H : MGraph} {U₁ U₂ U₃ : List Update}
    {a : CoreView H}
    {b : CoreView (H.applyBatch U₁)}
    {c : CoreView ((H.applyBatch U₁).applyBatch U₂)}
    {d : CoreView (((H.applyBatch U₁).applyBatch U₂).applyBatch U₃)}
    {d' : CoreView (H.applyBatch (U₁ ++ U₂ ++ U₃))}
    (h1 : CoreSubgraphBatch β U₁ a b)
    (h2 : CoreSubgraphBatch β U₂ b c)
    (h3 : CoreSubgraphBatch β U₃ c d)
    (hd : d'.graph = d.graph) (hrot : ∀ w, (d'.rotation.order w).IsRotated (d.rotation.order w)) :
    CoreSubgraphBatch β (U₁ ++ U₂ ++ U₃) a d' := by
  have h12 : CoreSubgraphBatch β (U₁ ++ U₂) a ((applyBatch_append H U₁ U₂).symm ▸ c) :=
    CoreSubgraphBatch.append h1 h2
  have hEq12 : H.applyBatch (U₁ ++ U₂) = (H.applyBatch U₁).applyBatch U₂ :=
    applyBatch_append H U₁ U₂
  have h3' : ∀ (X : MGraph) (hX : X = (H.applyBatch U₁).applyBatch U₂),
      CoreSubgraphBatch β U₃ (hX.symm ▸ c) ((congrArg (·.applyBatch U₃) hX).symm ▸ d) := by
    intro X hX
    subst hX
    exact h3
  have h123 := CoreSubgraphBatch.append h12 (h3' (H.applyBatch (U₁ ++ U₂)) hEq12)
  have hlast : ∀ (X Y : MGraph) (h1' : X = Y) (h2' : Y = (((H.applyBatch U₁).applyBatch U₂).applyBatch U₃))
      (u : CoreView X),
      u.graph = d.graph →
      (∀ w, (u.rotation.order w).IsRotated (d.rotation.order w)) →
      CoreSubgraphBatch β [] (h1'.symm ▸ (h2'.symm ▸ d : CoreView Y) : CoreView X) u := by
    intro X Y h1' h2' u _ hru
    subst h1'
    subst h2'
    exact CoreSubgraphBatch.congrCore hru (.nil u)
  have hfin := CoreSubgraphBatch.append h123 (hlast _ _ (applyBatch_append H (U₁ ++ U₂) U₃)
    (congrArg (·.applyBatch U₃) hEq12) d' hd hrot)
  have hnil_eq : U₁ ++ U₂ ++ U₃ ++ [] = U₁ ++ U₂ ++ U₃ := List.append_nil _
  have htransport : ∀ (W : List Update) (hW : W = U₁ ++ U₂ ++ U₃)
      (e : CoreView (H.applyBatch W)),
      CoreSubgraphBatch β W a e →
      CoreSubgraphBatch β (U₁ ++ U₂ ++ U₃) a (congrArg H.applyBatch hW ▸ e) := by
    intro W hW e hcs
    subst hW
    exact hcs
  have hres := htransport _ hnil_eq _ hfin
  have hcast : (congrArg H.applyBatch hnil_eq ▸
      ((applyBatch_append H (U₁ ++ U₂ ++ U₃) []).symm ▸ d') :
      CoreView (H.applyBatch (U₁ ++ U₂ ++ U₃))) = d' := by
    have hgen : ∀ (W : List Update) (hW : W = U₁ ++ U₂ ++ U₃)
        (hApp : H.applyBatch W = (H.applyBatch (U₁ ++ U₂ ++ U₃)).applyBatch []),
        (congrArg H.applyBatch hW ▸ (hApp.symm ▸ d' : CoreView (H.applyBatch W)) :
          CoreView (H.applyBatch (U₁ ++ U₂ ++ U₃))) = d' := by
      intro W hW hApp
      subst hW
      rfl
    exact hgen _ hnil_eq (applyBatch_append H (U₁ ++ U₂ ++ U₃) [])
  rwa [hcast] at hres

/-- Under the hypotheses of `buildUSOrd_spec_of_coreBatch`, the output batch `buildUSOrd` forms
a `CoreSubgraphBatch 2` from the initial core view of `S_prev` to the final core view of `S_next`.
-/
theorem buildUSOrd_coreSubgraphBatch_of_coreBatch {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    {cs_old : CompLSFState} {U UC : List Update} {ord ord' : ℕ → List End}
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
    let hI_new := compLSFBatch_inv hI hBU
    let hG_eq := compLSFBatch_G cs_old U
    let hNext_sub :=
      (buildUSOrd_spec_of_coreBatch hI hBU ρ σ hρ hσ hUC hS_val hS_V hS_sub hTgt_sub
        D_reins).2.2.2.2.2.1
    CoreSubgraphBatch 2 U_S
      ⟨coreGraph cs_old.G cs_old.lsf,
        coreRotation (L := cs_old.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI), hS_sub⟩
      ⟨coreGraph cs_new.G cs_new.lsf,
        coreRotation (L := cs_new.lsf) (hG_eq.symm ▸ σ) hI_new.hG_val (compLSF_RF_isRSF hI_new),
        hNext_sub⟩ := by
  intro cs_new U_S hI_new hG_eq hNext_sub
  have hRF_old := compLSF_RF_isRSF hI
  have hRF_new := compLSF_RF_isRSF hI_new
  let C₀ := coreGraph cs_old.G cs_old.lsf
  let C₁ := coreGraph cs_new.G cs_new.lsf
  let ρ₀ := coreRotation (L := cs_old.lsf) ρ hI.hG_val hRF_old
  let σ₁ := coreRotation (L := cs_new.lsf) (hG_eq.symm ▸ σ) hI_new.hG_val hRF_new
  have hOCB : OrderedCoreBatch 2 ρ₀ σ₁ UC :=
    hUC.1 ρ (hG_eq.symm ▸ σ) hI.hG_val hRF_old hI_new.hG_val hRF_new hρ
      (by rw [cast_order_eq', hσ])
  obtain ⟨hUC_val, hUC_eq, hUC_rot⟩ := hOCB
  let keepSet := ((S_prev.E ∩ targetE) \ batchDeletes U) \ D_reins
  let delEdges := S_prev.E \ keepSet
  let insEdges := targetE \ keepSet
  let delList := (delEdges.sort (· ≤ ·)).map Update.delete
  let splitList := restrictSplits keepSet UC
  let insList := (insEdges.sort (· ≤ ·)).map fun e => Update.insert e (C₁.tail e) (C₁.head e)
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
  have hS1_V : S_1.V = C₀.V := hDel_spec.2.1.trans hS_V
  have hS1_val : S_1.IsValid := hDel_spec.2.2.2.2
  have hS1_sub : C₀.IsSubgraph S_1 := by
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
  obtain ⟨_, _, hS2_sub_raw, _, _, _⟩ :=
    restrictSplits_spec hUC_val hS1_val hS1_sub hS1_V hS1_E hDisj
  set S_2 := S_1.applyBatch splitList
  have hS2_sub : C₁.IsSubgraph S_2 := by
    refine ⟨hUC_eq.1.symm ▸ hS2_sub_raw.1, hUC_eq.2.1.symm ▸ hS2_sub_raw.2.1, fun e he => ?_⟩
    have h1 := hS2_sub_raw.2.2 e he
    have heC1 : e ∈ C₁.E := hUC_eq.2.1.symm ▸ hS2_sub_raw.2.1 he
    have h2 := hUC_eq.2.2 e heC1
    exact ⟨h1.1.trans h2.1.symm, h1.2.trans h2.2.symm⟩
  have hIns_mem : ∀ e ∈ (insEdges.sort (· ≤ ·)), e ∈ C₁.E :=
    fun e he => hTgt_sub (Finset.mem_sdiff.mp ((Finset.mem_sort (· ≤ ·)).mp he)).1
  have hApp123 : S_prev.applyBatch U_S = S_2.applyBatch insList := by
    change S_prev.applyBatch (delList ++ splitList ++ insList) = S_2.applyBatch insList
    rw [applyBatch_append, applyBatch_append]
  have hP1 : CoreSubgraphBatch 2 delList ⟨C₀, ρ₀, hS_sub⟩ ⟨C₀, ρ₀, hS1_sub⟩ :=
    coreSubgraphBatch_delete_list ρ₀ hS_sub (delEdges.sort (· ≤ ·)) hS1_sub
  have hP2 : CoreSubgraphBatch 2 splitList ⟨C₀, ρ₀, hS1_sub⟩
      ⟨C₀.applyBatch UC, σ₁.congrGraph hUC_eq, hS2_sub_raw⟩ :=
    coreSubgraphBatch_restrictSplits hUC_rot hUC_val hS1_sub hS1_V hS1_E hDisj hS2_sub_raw
  have hP3 : CoreSubgraphBatch 2 insList ⟨C₁, σ₁, hS2_sub⟩
      ⟨C₁, σ₁, hApp123 ▸ hNext_sub⟩ :=
    coreSubgraphBatch_insert_list σ₁ hS2_sub (insEdges.sort (· ≤ ·)) hIns_mem (hApp123 ▸ hNext_sub)
  have hP3' : CoreSubgraphBatch 2 insList
      ⟨C₀.applyBatch UC, σ₁.congrGraph hUC_eq, hS2_sub_raw⟩
      ⟨C₁, σ₁, hApp123 ▸ hNext_sub⟩ :=
    CoreSubgraphBatch.congrCore
      (a := ⟨C₀.applyBatch UC, σ₁.congrGraph hUC_eq, hS2_sub_raw⟩)
      (b := ⟨C₁, σ₁, hS2_sub⟩) (fun _ => .refl _) hP3
  exact coreSubgraphBatch_append3 hP1 hP2 hP3' rfl (fun _ => .refl _)

/-- One-step `CoreSubgraphBatch 2` statement for `buildUSOrd` with `coreBatchOf`. -/
theorem buildUSOrd_coreSubgraphBatch {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs_old : CompLSFState}
    {U : List Update} {ord ord' : ℕ → List End}
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
    let hI_new := compLSFBatch_inv hI hBU
    let hG_eq := compLSFBatch_G cs_old U
    let hNext_sub :=
      (buildUSOrd_spec hI hBU ρ σ hρ hσ hrot hS_val hS_V hS_sub hTgt_sub
        D_reins).2.2.2.2.2.1
    CoreSubgraphBatch 2 U_S
      ⟨coreGraph cs_old.G cs_old.lsf,
        coreRotation (L := cs_old.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI), hS_sub⟩
      ⟨coreGraph cs_new.G cs_new.lsf,
        coreRotation (L := cs_new.lsf) (hG_eq.symm ▸ σ) hI_new.hG_val (compLSF_RF_isRSF hI_new),
        hNext_sub⟩ :=
  buildUSOrd_coreSubgraphBatch_of_coreBatch hI hBU ρ σ hρ hσ
    (coreBatchOf_spec hI ρ σ hρ hσ hrot hBU) hS_val hS_V hS_sub hTgt_sub D_reins

/-- For any `U_S = buildUSOrd ...` (empty or nonempty), the initial and final restricted core
rotations are connected by `RotationBatch 2 U_S`. -/
theorem buildUSOrd_rotationBatch {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs_old : CompLSFState}
    {U : List Update} {ord ord' : ℕ → List End}
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
    let hI_new := compLSFBatch_inv hI hBU
    let hG_eq := compLSFBatch_G cs_old U
    let hNext_sub :=
      (buildUSOrd_spec hI hBU ρ σ hρ hσ hrot hS_val hS_V hS_sub hTgt_sub
        D_reins).2.2.2.2.2.1
    RotationBatch 2 U_S
      ((coreRotation (L := cs_old.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI)).restrict hS_sub)
      ((coreRotation (L := cs_new.lsf) (hG_eq.symm ▸ σ) hI_new.hG_val
        (compLSF_RF_isRSF hI_new)).restrict hNext_sub) := by
  have hCSB := buildUSOrd_coreSubgraphBatch hI hBU ρ σ hρ hσ hrot hS_val hS_V hS_sub
    hTgt_sub D_reins
  have hBV := (buildUSOrd_spec hI hBU ρ σ hρ hσ hrot hS_val hS_V hS_sub hTgt_sub D_reins).1
  exact hCSB.ordered hBV

/-- For any `U_S = buildUSOrd ...` (empty or nonempty), there exists a rotation of `S_prev`
cyclically equivalent at every vertex to the initial restricted core rotation that connects to
the final restricted core rotation by `RotationBatch 2 U_S`. -/
theorem buildUSOrd_rotationBatch_exists {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs_old : CompLSFState}
    {U : List Update} {ord ord' : ℕ → List End}
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
    let hI_new := compLSFBatch_inv hI hBU
    let hG_eq := compLSFBatch_G cs_old U
    let hNext_sub :=
      (buildUSOrd_spec hI hBU ρ σ hρ hσ hrot hS_val hS_V hS_sub hTgt_sub
        D_reins).2.2.2.2.2.1
    ∃ ρ' : Rotation S_prev,
      (∀ w, (ρ'.order w).IsRotated
        (((coreRotation (L := cs_old.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI)).restrict
          hS_sub).order w)) ∧
      RotationBatch 2 U_S ρ'
        ((coreRotation (L := cs_new.lsf) (hG_eq.symm ▸ σ) hI_new.hG_val
          (compLSF_RF_isRSF hI_new)).restrict hNext_sub) := by
  have hCSB := buildUSOrd_coreSubgraphBatch hI hBU ρ σ hρ hσ hrot hS_val hS_V hS_sub
    hTgt_sub D_reins
  have hBV := (buildUSOrd_spec hI hBU ρ σ hρ hσ hrot hS_val hS_V hS_sub hTgt_sub D_reins).1
  exact hCSB.ordered_exists hBV

/-- When `U_S = buildUSOrd ...` is nonempty, the restricted core rotations are connected by
`RotationBatch 2 U_S`. -/
theorem buildUSOrd_rotationBatch_of_ne_nil {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs_old : CompLSFState}
    {U : List Update} {ord ord' : ℕ → List End}
    (hI : CompLSFInv C_lsst ℓ₀ cs_old) (hBU : cs_old.G.BatchIsValid U)
    (ρ : Rotation cs_old.G) (σ : Rotation (cs_old.G.applyBatch U)) (hρ : ρ.order = ord)
    (hσ : σ.order = ord') (hrot : RotationBatch 2 U ρ σ)
    {S_prev : MGraph} (hS_val : S_prev.IsValid) (hS_V : S_prev.V = cs_old.RF.R)
    (hS_sub : (coreGraph cs_old.G cs_old.lsf).IsSubgraph S_prev)
    {targetE : Finset ℕ}
    (hTgt_sub : targetE ⊆ (compLSFBatch cs_old U).G.E \ (compLSFBatch cs_old U).RF.F.E)
    (D_reins : Finset ℕ)
    (hNe : buildUSOrd (coreBatchOf cs_old ord ord' U) U (compLSFBatch cs_old U)
      S_prev targetE D_reins ≠ []) :
    let cs_new := compLSFBatch cs_old U
    let UC := coreBatchOf cs_old ord ord' U
    let U_S := buildUSOrd UC U cs_new S_prev targetE D_reins
    let hI_new := compLSFBatch_inv hI hBU
    let hG_eq := compLSFBatch_G cs_old U
    let hNext_sub :=
      (buildUSOrd_spec hI hBU ρ σ hρ hσ hrot hS_val hS_V hS_sub hTgt_sub
        D_reins).2.2.2.2.2.1
    RotationBatch 2 U_S
      ((coreRotation (L := cs_old.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI)).restrict hS_sub)
      ((coreRotation (L := cs_new.lsf) (hG_eq.symm ▸ σ) hI_new.hG_val
        (compLSF_RF_isRSF hI_new)).restrict hNext_sub) := by
  have hCSB := buildUSOrd_coreSubgraphBatch hI hBU ρ σ hρ hσ hrot hS_val hS_V hS_sub
    hTgt_sub D_reins
  have hBV := (buildUSOrd_spec hI hBU ρ σ hρ hσ hrot hS_val hS_V hS_sub hTgt_sub D_reins).1
  exact hCSB.ordered_of_ne_nil hBV hNe

end MinCostFlow.SparseCore
