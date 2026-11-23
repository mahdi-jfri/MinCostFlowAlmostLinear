module

public import MinCostFlow.SparseCore.BundleTool
public import MinCostFlow.SparseCore.BundleConstants
import MinCostFlow.DynSpanner.WalkCount

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Single-step backward stability for `sparseCoreBundleTool`

Provides the bundle-graph analogues of `SparseCoreStabilityStep.lean`:
* `mem_buildUSOrd_insEdges`: any edge of `targetE` not inserted by `buildUSOrd` belongs to
  `keepSet` (`S_prev.E`, not deleted by `U`, not in `D_reins`).
* `initBundleFor_edges_eq` and `bucketCoreEdges_pairwiseDisjoint`: initial bundle edge sets
  equal `bucketCoreEdges` and are pairwise disjoint across component-bucket pairs.
* `mem_comp_eq_of_mem_bun_and_compG`: any non-cross edge in a bundle state of component `C₁`
  that lies in `(cs.compSt C₂).G.E` satisfies `C₁ = C₂`.
* `bun_edges_disjoint_insertedGlobal`: across a run of `bundleRunSeq`, once bundle edges are
  disjoint from `batchDeletes (D.U (s + 1))` at each step, they stay disjoint from
  `st.cs.insertedGlobal` and `st.cs.crossEdges`.
* `bundleWeakHidden_step_backward_core`: single-step backward preservation of `S_cur` membership,
  `walkEdges`, `walkCount`, and non-insertion for any `BundleTreeState` step evolving via
  `stepBundleTree` (paper Lemma 5.17, item 2, pages 23–24).
-/

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner
open MinCostFlow.Bundle

@[expose] public section

/-! ## 1. `buildUSOrd`, initial bundle edge sets, and disjoint-component helpers -/

lemma mem_buildUSOrd_insEdges
    (UC U : List Update) (cs_new : CompLSFState)
    (S_prev : MGraph) (targetE D_reins : Finset ℕ) {e : ℕ}
    (heT : e ∈ targetE)
    (hNoIns : ∀ u ∈ buildUSOrd UC U cs_new S_prev targetE D_reins, ¬ u.Inserts e) :
    e ∈ ((S_prev.E ∩ targetE) \ batchDeletes U) \ D_reins := by
  by_contra hnot
  apply hNoIns (.insert e (cs_new.RF.root (cs_new.G.tail e)) (cs_new.RF.root (cs_new.G.head e)))
  · dsimp only [buildUSOrd]
    simp only [List.mem_append, List.mem_map]
    right
    exact ⟨e, (Finset.mem_sort (· ≤ ·)).mpr (Finset.mem_sdiff.mpr ⟨heT, hnot⟩), rfl⟩
  · rfl

lemma initBundleFor_edges_eq {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {ord : ℕ → List End} (ρ : Rotation cs.G) (hρ : ρ.order = ord)
    (E : Finset ℕ) (k : ℕ) :
    (initBundleFor cs ord E k).edges = E := by
  have hex : ∃ (C' : ℝ) (ℓ' : ℕ → ℝ) (_ : CompLSFInv C' ℓ' cs) (ρ' : Rotation cs.G),
      ρ'.order = ord := ⟨C_lsst, ℓ₀, hI, ρ, hρ⟩
  unfold initBundleFor
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  rfl

lemma bucketCoreEdges_pairwiseDisjoint {G₀ : MGraph} {C₀ : MGraph} {origB : ℕ → ℤ}
    {C₁ C₂ : Finset ℕ} (hC₁ : C₁ ∈ components G₀) (hC₂ : C₂ ∈ components G₀)
    {b₁ b₂ : ℤ} {e : ℕ}
    (he₁ : e ∈ bucketCoreEdges C₀ origB C₁ b₁)
    (he₂ : e ∈ bucketCoreEdges C₀ origB C₂ b₂) :
    C₁ = C₂ ∧ b₁ = b₂ := by
  simp only [bucketCoreEdges, Finset.mem_filter] at he₁ he₂
  have hC : C₁ = C₂ := by
    by_contra hne
    exact Finset.disjoint_left.mp (components_V_pairwiseDisjoint G₀ hC₁ hC₂ hne) he₁.2.1 he₂.2.1
  exact ⟨hC, he₁.2.2.symm.trans he₂.2.2⟩

lemma mem_comp_eq_of_mem_bun_and_compG {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    {cs : CompLSFState} {G₀ : MGraph} (hI : CompLSFInv C_lsst ℓ₀ cs) (hG₀_eq : cs.G₀ = G₀)
    {C₁ C₂ : Finset ℕ} (hC₁ : C₁ ∈ components G₀) (hC₂ : C₂ ∈ components G₀)
    {B : BundleState} {k : ℕ} (ρ : Rotation cs.G)
    (hPart : B.IsPartition (coreRotation (L := cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI)) k)
    (hPar : ∀ x ∈ B.vertices, B.parent x ∈ (cs.compSt C₁).R)
    {e : ℕ} (he₁ : e ∈ B.edges) (he₂ : e ∈ (cs.compSt C₂).G.E)
    (hNotCross : e ∉ cs.crossEdges) :
    C₁ = C₂ := by
  by_contra hne
  have hC₁' : C₁ ∈ components cs.G₀ := hG₀_eq.symm ▸ hC₁
  have hC₂' : C₂ ∈ components cs.G₀ := hG₀_eq.symm ▸ hC₂
  obtain ⟨hb_mem, hb_par⟩ := hPart.2.2.1 (e, true) ((mem_edgeEnds _ _).mpr he₁)
  have hr₁_R : B.parent (B.bundleOf (e, true)) ∈ (cs.compSt C₁).R := hPar _ hb_mem
  have hRS₁ := lsfInv_to_RS (hI.hCompLSF C₁ hC₁').1
  have hr₁_V : cs.RF.root (cs.G.tail e) ∈ (cs.compSt C₁).G.V := by
    have hsrc : (coreGraph cs.G cs.lsf).src (e, true) = cs.RF.root (cs.G.tail e) := rfl
    rw [← hsrc, ← hb_par]
    exact hRS₁.2.1 ▸ hRS₁.2.2.1 hr₁_R
  have hend₂ := hI.hNonCross_ends C₂ hC₂' e he₂ hNotCross
  have hv₂ : cs.G.tail e ∈ (cs.compSt C₂).G.V := by
    rw [← hend₂.1]
    exact ((hI.hCompLSF C₂ hC₂').1.hG_val e he₂).1
  have hRS₂ := lsfInv_to_RS (hI.hCompLSF C₂ hC₂').1
  have hr₂_eq : cs.RF.root (cs.G.tail e) = (cs.compSt C₂).RF.root (cs.G.tail e) :=
    compLSF_RF_root_eq hI hC₂' hv₂
  have hr₂_R : (cs.compSt C₂).RF.root (cs.G.tail e) ∈ (cs.compSt C₂).RF.R :=
    (rootedForest_root_spec hRS₂ (hRS₂.2.1.symm ▸ hv₂)).1
  have hr₂_V : cs.RF.root (cs.G.tail e) ∈ (cs.compSt C₂).G.V := by
    rw [hr₂_eq]
    exact hRS₂.2.1 ▸ hRS₂.2.2.1 hr₂_R
  exact Finset.disjoint_left.mp (hI.hV_disj C₁ hC₁' C₂ hC₂' hne) hr₁_V hr₂_V

lemma bun_edges_sub_of_delOrSplit_batch {G : MGraph} {U : List Update}
    (hds : ∀ op ∈ U, isDelOrSplit op) :
    (G.applyBatch U).E ⊆ G.E := by
  induction U generalizing G with
  | nil => exact Finset.Subset.rfl
  | cons op rest ih =>
    have hop := hds op List.mem_cons_self
    have hstep : (G.applyUpdate op).E ⊆ G.E := by
      cases op with
      | insert => cases hop
      | delete e => exact Finset.erase_subset e G.E
      | split => exact Finset.Subset.rfl
    exact Finset.Subset.trans (ih fun u hu => hds u (List.mem_cons_of_mem op hu)) hstep

/-- Across a run of `bundleRunSeq`, if each step removes `batchDeletes (D.U (s + 1))` from every
bundle state's edge set, then bundle edges stay disjoint from `st.cs.insertedGlobal` and
`st.cs.crossEdges` at every stage `t ≤ τ`. -/
lemma bun_edges_disjoint_insertedGlobal
    {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {τ : ℕ} {D : DynamicInstance}
    (hD : D.IsValid τ)
    {cs₀ : CompLSFState} (hIns₀ : cs₀.insertedGlobal = ∅)
    {L : ℕ} (st : ℕ → BundleTreeState L)
    (hcs : ∀ t ≤ τ, (st t).cs = compLSFBatch cs₀ (dynBatches D t).flatten)
    (hI : ∀ t ≤ τ, CompLSFInv C_lsst ℓ₀ (st t).cs)
    (hE_sub_G : ∀ t ≤ τ, ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      ((st t).bun (C, b)).edges ⊆ (D.G t).E)
    (hStep_sub : ∀ s < τ, ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      ((st (s + 1)).bun (C, b)).edges ⊆ ((st s).bun (C, b)).edges)
    (hStep_disj : ∀ s < τ, ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      Disjoint ((st (s + 1)).bun (C, b)).edges (batchDeletes (D.U (s + 1)))) :
    ∀ t ≤ τ, ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      Disjoint ((st t).bun (C, b)).edges (st t).cs.insertedGlobal ∧
      Disjoint ((st t).bun (C, b)).edges (st t).cs.crossEdges := by
  intro t ht
  have hMain : ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      Disjoint ((st t).bun (C, b)).edges (st t).cs.insertedGlobal := by
    induction t with
    | zero =>
      intro C _ b
      have hcs0 : (st 0).cs = cs₀ := by
        simpa [dynBatches, compLSFBatch] using hcs 0 ht
      rw [hcs0, hIns₀]
      exact Finset.disjoint_empty_right _
    | succ s ih =>
      intro C hC b
      have hs_le : s ≤ τ := Nat.le_of_succ_le ht
      have hdisj_prev := ih hs_le C hC b
      rw [Finset.disjoint_left]
      intro e he_cur he_ins
      have he_prev : e ∈ ((st s).bun (C, b)).edges := hStep_sub s ht C hC b he_cur
      have he_notDel : e ∉ batchDeletes (D.U (s + 1)) :=
        Finset.disjoint_left.mp (hStep_disj s ht C hC b) he_cur
      have hDs := hD (s + 1) (Nat.succ_pos s) ht
      simp only [Nat.add_sub_cancel] at hDs
      have heGs : e ∈ (D.G s).E := hE_sub_G s hs_le C hC b he_prev
      have hnoIns : ∀ u ∈ D.U (s + 1), ¬ u.Inserts e :=
        not_inserts_of_not_mem_batchDeletes hDs.1 heGs he_notDel
      have heGs1 : e ∈ ((D.G s).applyBatch (D.U (s + 1))).E := by
        rw [← hDs.2]
        exact hE_sub_G (s + 1) ht C hC b he_cur
      have hstep_cs : (st (s + 1)).cs = compLSFBatch (st s).cs (D.U (s + 1)) := by
        rw [hcs (s + 1) ht, hcs s hs_le, compLSFBatch_dynBatches_succ]
      rw [hstep_cs, compLSFBatch_insertedGlobal] at he_ins
      have he_ins_prev : e ∈ (st s).cs.insertedGlobal :=
        (mem_foldl_updateInserted_iff_of_mem_applyBatch_no_ins heGs1 hnoIns).mp he_ins
      exact Finset.disjoint_left.mp hdisj_prev he_prev he_ins_prev
  intro C hC b
  exact ⟨hMain C hC b, Finset.disjoint_of_subset_right (hI t ht).hCross_sub (hMain C hC b)⟩

/-! ## 2. Core single-step backward preservation lemma for `BundleTreeState` -/

/-- Core single-step backward preservation helper for clause 3 of `WeakHiddenStable`,
parameterized over arbitrary `BundleTreeState` states `st_s, st_s1` evolving via `stepBundleTree`
along `D.U (s + 1)` with input orders `ord s` and `ord (s + 1)` (paper Lemma 5.17, item 2, pages
23–24). -/
theorem bundleWeakHidden_step_backward_core
    {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (D : DynamicInstance) (ord : ℕ → ℕ → List End) {s : ℕ}
    (st_s st_s1 : BundleTreeState L)
    (hst_step : st_s1 = (stepBundleTree sparsify st_s (D.U (s + 1)) (ord s) (ord (s + 1))).state)
    (hI_s : CompLSFInv C_lsst ℓ₀ st_s.cs)
    (hI_s1 : CompLSFInv C_lsst ℓ₀ st_s1.cs)
    (hG₀_s : st_s.cs.G₀ = D.G 0)
    (hG₀_s1 : st_s1.cs.G₀ = D.G 0)
    (hG_s : st_s.cs.G = D.G s)
    (hBV_U : (D.G s).BatchIsValid (D.U (s + 1)))
    (ρ_s : Rotation st_s.cs.G) (hρ_s : ρ_s.order = ord s)
    (ρ_s1 : Rotation st_s1.cs.G) (hρ_s1 : ρ_s1.order = ord (s + 1))
    (hAct_s : st_s.activeComps ⊆ components (D.G 0))
    (hAct_s1 : st_s1.activeComps ⊆ components (D.G 0))
    (hS_sub_s : (coreGraph st_s.cs.G st_s.cs.lsf).IsSubgraph st_s.S_cur)
    (hS_E_s : st_s.S_cur.E =
      (st_s.activeComps.biUnion fun C => (st_s.activeBuckets C).biUnion fun b =>
          (st_s.dyn (C, b)).H.E) ∪
        (st_s.activeComps.biUnion fun C => st_s.extraEdges C) ∪
        st_s.cs.crossEdges)
    (hS_E_s1 : st_s1.S_cur.E =
      (st_s1.activeComps.biUnion fun C => (st_s1.activeBuckets C).biUnion fun b =>
          (st_s1.dyn (C, b)).H.E) ∪
        (st_s1.activeComps.biUnion fun C => st_s1.extraEdges C) ∪
        st_s1.cs.crossEdges)
    (hBun_s : ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      (st_s.bun (C, b)).IsPartition
        (coreRotation (L := st_s.cs.lsf) ρ_s hI_s.hG_val (compLSF_RF_isRSF hI_s)) st_s.k ∧
      (∀ x ∈ (st_s.bun (C, b)).vertices, (st_s.bun (C, b)).parent x ∈ (st_s.cs.compSt C).R) ∧
      Disjoint (st_s.bun (C, b)).edges st_s.cs.crossEdges ∧
      GraphEq (st_s.dyn (C, b)).G (st_s.bun (C, b)).graph ∧
      (st_s.dyn (C, b)).G.IsSubgraph (st_s.dyn (C, b)).H)
    (hBun_s1 : ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      (st_s1.bun (C, b)).IsPartition
        (coreRotation (L := st_s1.cs.lsf) ρ_s1 hI_s1.hG_val (compLSF_RF_isRSF hI_s1)) st_s1.k ∧
      (∀ x ∈ (st_s1.bun (C, b)).vertices, (st_s1.bun (C, b)).parent x ∈ (st_s1.cs.compSt C).R) ∧
      Disjoint (st_s1.bun (C, b)).edges st_s1.cs.crossEdges ∧
      GraphEq (st_s1.dyn (C, b)).G (st_s1.bun (C, b)).graph ∧
      (st_s1.dyn (C, b)).G.IsSubgraph (st_s1.dyn (C, b)).H ∧
      (piTotal (st_s1.dyn (C, b))).IsEmbedding (st_s1.dyn (C, b)).G (st_s1.dyn (C, b)).H)
    (hBun_disj_s : ∀ C₁ ∈ components (D.G 0), ∀ C₂ ∈ components (D.G 0), ∀ b₁ b₂ : ℤ,
      ∀ x, x ∈ (st_s.bun (C₁, b₁)).edges → x ∈ (st_s.bun (C₂, b₂)).edges → C₁ = C₂ ∧ b₁ = b₂)
    (hBun_step : ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      (st_s1.bun (C, b)).edges ⊆ (st_s.bun (C, b)).edges ∧
      Disjoint (st_s1.bun (C, b)).edges (batchDeletes (D.U (s + 1))))
    (hDyn_step : ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      let stepOut :=
        (stepBundleTree sparsify st_s (D.U (s + 1)) (ord s) (ord (s + 1))).stepOut (C, b)
      stepOut = update (st_s.dyn (C, b))
        ((stepBundleTree sparsify st_s (D.U (s + 1)) (ord s) (ord (s + 1))).U_B (C, b))
        (sparsify st_s.m₀) ∧
      stepOut.state = st_s1.dyn (C, b) ∧
      (∀ eG ∈ (st_s1.dyn (C, b)).G.E,
        ∀ eH ∈ walkEdges (piTotal (st_s1.dyn (C, b)) eG),
          eH ∉ stepOut.D → eH ∈ walkEdges (piTotal (st_s.dyn (C, b)) eG)) ∧
      (∀ eG ∈ (st_s1.dyn (C, b)).G.E, ∀ x : ℕ,
        x ∉ stepOut.D →
        walkCount (piTotal (st_s1.dyn (C, b)) eG) x ≤
          walkCount (piTotal (st_s.dyn (C, b)) eG) x))
    {e' : ℕ}
    (he'_cur : e' ∈ st_s1.S_cur.E)
    (hNoIns : ∀ u ∈ (stepBundleTree sparsify st_s (D.U (s + 1)) (ord s) (ord (s + 1))).U_S,
      ¬ u.Inserts e') :
    e' ∈ st_s.S_cur.E ∧
    e' ∉ batchDeletes (D.U (s + 1)) ∧
    ∀ e ∈ (coreGraph (D.G (s + 1)) st_s1.cs.lsf).E, e' ∈ walkEdges (st_s1.emb e) →
      e ∈ (coreGraph (D.G s) st_s.cs.lsf).E ∧
      e' ∈ walkEdges (st_s.emb e) ∧
      walkCount (st_s1.emb e) e' ≤ walkCount (st_s.emb e) e' ∧
      (∀ u ∈ D.U (s + 1), ¬ u.Inserts e) := by
  let _ := hρ_s
  let _ := hρ_s1
  set info := stepBundleTree sparsify st_s (D.U (s + 1)) (ord s) (ord (s + 1))
  have hcs1_eq : info.state.cs = st_s1.cs := by rw [← hst_step]
  have hact1_eq : info.state.activeComps = st_s1.activeComps := by rw [← hst_step]
  have hactB1_eq : st_s1.activeBuckets = st_s.activeBuckets := by rw [hst_step]; rfl
  have hbun1_eq : info.state.bun = st_s1.bun := by rw [← hst_step]
  have hdyn1_eq : info.state.dyn = st_s1.dyn := by rw [← hst_step]
  -- Match `stepBundleTree`'s `targetE'` with `st_s1.S_cur.E`.
  let dynUnionE' := info.state.activeComps.biUnion fun C =>
    (st_s.activeBuckets C).biUnion fun b => (info.stepOut (C, b)).state.H.E
  let bunE' := info.state.activeComps.biUnion fun C =>
    (st_s.activeBuckets C).biUnion fun b => (info.state.bun (C, b)).edges
  let extraComps' := info.state.activeComps.biUnion fun C =>
    ((info.state.cs.compSt C).G.E \ (info.state.cs.compSt C).RF.F.E) \ bunE'
  let targetE' := dynUnionE' ∪ extraComps' ∪ info.state.cs.crossEdges
  have hdyn_union : dynUnionE' =
      (st_s1.activeComps.biUnion fun C => (st_s1.activeBuckets C).biUnion fun b =>
        (st_s1.dyn (C, b)).H.E) := by
    dsimp only [dynUnionE']
    rw [hact1_eq, hactB1_eq]
    refine Finset.biUnion_congr rfl fun C hCA => Finset.biUnion_congr rfl fun b _ => ?_
    rw [(hDyn_step C (hAct_s1 hCA) b).2.1]
  have hextra_eq : extraComps' = st_s1.activeComps.biUnion fun C => st_s1.extraEdges C := by
    ext x
    simp only [extraComps', bunE', BundleTreeState.extraEdges, Finset.mem_biUnion,
      Finset.mem_sdiff, hact1_eq, hcs1_eq, hbun1_eq, hactB1_eq]
    constructor
    · rintro ⟨C, hCA, hxG, hxnot⟩
      refine ⟨C, hCA, hxG, fun hmem => hxnot ⟨C, hCA, hmem⟩⟩
    · rintro ⟨C, hCA, hxG, hxnot⟩
      refine ⟨C, hCA, hxG, ?_⟩
      rintro ⟨C', hC'A, b', hb', hxb'⟩
      have hC_comp : C ∈ components (D.G 0) := hAct_s1 hCA
      have hC'_comp : C' ∈ components (D.G 0) := hAct_s1 hC'A
      have hb_props := hBun_s1 C' hC'_comp b'
      have hNotCross : x ∉ st_s1.cs.crossEdges :=
        Finset.disjoint_left.mp hb_props.2.2.1 hxb'
      have hEqC : C' = C := mem_comp_eq_of_mem_bun_and_compG hI_s1 hG₀_s1 hC'_comp hC_comp ρ_s1
        hb_props.1 hb_props.2.1 hxb' hxG.1 hNotCross
      subst hEqC
      exact hxnot ⟨b', hb', hxb'⟩
  have hS_s1_target : st_s1.S_cur.E = targetE' := by
    dsimp only [targetE']
    rw [hS_E_s1, hdyn_union, hextra_eq, hcs1_eq]
  have hU_eq : info.U_S = buildUSOrd info.U_core (D.U (s + 1)) info.state.cs st_s.S_cur
      targetE' info.D_total := rfl
  rw [hU_eq] at hNoIns
  have hkeep := mem_buildUSOrd_insEdges info.U_core (D.U (s + 1)) info.state.cs st_s.S_cur
    targetE' info.D_total (hS_s1_target ▸ he'_cur) hNoIns
  rw [Finset.mem_sdiff, Finset.mem_sdiff, Finset.mem_inter] at hkeep
  have he'_prev : e' ∈ st_s.S_cur.E := hkeep.1.1.1
  have he'_notDel : e' ∉ batchDeletes (D.U (s + 1)) := hkeep.1.2
  have he'_notD : e' ∉ info.D_total := hkeep.2
  refine ⟨he'_prev, he'_notDel, fun e heC1 hew1 => ?_⟩
  by_cases heS1 : e ∈ st_s1.S_cur.E
  · have hemb1 : st_s1.emb e = [(e, true)] := by
      dsimp only [BundleTreeState.emb]; simp only [heS1, ↓reduceIte]
    rw [hemb1] at hew1
    simp only [walkEdges, List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
      insert_empty_eq, Finset.mem_singleton] at hew1
    have he_eq : e = e' := hew1.symm
    subst he_eq
    have heC0 : e ∈ (coreGraph (D.G s) st_s.cs.lsf).E :=
      hG_s ▸ hS_sub_s.2.1 he'_prev
    have hemb0 : st_s.emb e = [(e, true)] := by
      dsimp only [BundleTreeState.emb]; simp only [he'_prev, ↓reduceIte]
    have hew0 : e ∈ walkEdges (st_s.emb e) := by
      rw [hemb0]; simp [walkEdges]
    have hwc_le : walkCount (st_s1.emb e) e ≤ walkCount (st_s.emb e) e := by
      rw [hemb1, hemb0]
    have heGs : e ∈ (D.G s).E := (Finset.mem_sdiff.mp heC0).1
    have hnoIns_e : ∀ u ∈ D.U (s + 1), ¬ u.Inserts e :=
      not_inserts_of_not_mem_batchDeletes hBV_U heGs he'_notDel
    exact ⟨heC0, hew0, hwc_le, hnoIns_e⟩
  · have hEx : ∃ p : Finset ℕ × ℤ, p.1 ∈ st_s1.activeComps ∧ p.2 ∈ st_s1.activeBuckets p.1 ∧
        e ∈ (st_s1.bun p).edges := by
      by_contra hnot
      have hew_nil : st_s1.emb e = [] := by
        dsimp only [BundleTreeState.emb]; simp only [heS1, ↓reduceIte, hnot, ↓reduceDIte]
      rw [hew_nil, walkEdges] at hew1
      simp at hew1
    let p := hEx.choose
    let C := p.1
    let b := p.2
    have hC_act1 : C ∈ st_s1.activeComps := hEx.choose_spec.1
    have hb_act1 : b ∈ st_s1.activeBuckets C := hEx.choose_spec.2.1
    have he_bun1 : e ∈ (st_s1.bun (C, b)).edges := hEx.choose_spec.2.2
    have hC_comp : C ∈ components (D.G 0) := hAct_s1 hC_act1
    have hb_act0 : b ∈ st_s.activeBuckets C := hactB1_eq ▸ hb_act1
    have hemb1 : st_s1.emb e = piTotal (st_s1.dyn (C, b)) e := by
      dsimp only [BundleTreeState.emb]
      simp only [heS1, ↓reduceIte, hEx, ↓reduceDIte]
      rfl
    rw [hemb1] at hew1
    have hBun1 := hBun_s1 C hC_comp b
    have hBun0 := hBun_s C hC_comp b
    have heG1_b : e ∈ (st_s1.dyn (C, b)).G.E := by
      rw [hBun1.2.2.2.1.2.1]; exact he_bun1
    have hnotD_b : e' ∉ (info.stepOut (C, b)).D := by
      intro hmem
      apply he'_notD
      have hC_info : C ∈ info.state.activeComps := by rw [hact1_eq]; exact hC_act1
      dsimp only [info, stepBundleTree]
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨C, hC_info,
        Finset.mem_biUnion.mpr ⟨b, hb_act0, hmem⟩⟩)
    have hDyn_cb := hDyn_step C hC_comp b
    have hew0_b : e' ∈ walkEdges (piTotal (st_s.dyn (C, b)) e) :=
      hDyn_cb.2.2.1 e heG1_b e' hew1 hnotD_b
    have he'H1 : e' ∈ (st_s1.dyn (C, b)).H.E :=
      walkEdges_subset_of_isWalk (hBun1.2.2.2.2.2.2 e heG1_b) hew1
    have he'G1_b : e' ∈ (st_s1.dyn (C, b)).G.E := hBun1.2.2.2.2.1.2.1 he'H1
    have he'_bun1 : e' ∈ (st_s1.bun (C, b)).edges := by
      rw [hBun1.2.2.2.1.2.1] at he'G1_b; exact he'G1_b
    have he'_bun0 : e' ∈ (st_s.bun (C, b)).edges := (hBun_step C hC_comp b).1 he'_bun1
    have he_bun0 : e ∈ (st_s.bun (C, b)).edges := (hBun_step C hC_comp b).1 he_bun1
    have hC_act0 : C ∈ st_s.activeComps := by
      rw [hS_E_s, Finset.mem_union] at he'_prev
      rcases he'_prev with heB | heCr
      · rw [Finset.mem_union] at heB
        rcases heB with heDyn | heExt
        · rw [Finset.mem_biUnion] at heDyn
          rcases heDyn with ⟨C', hC'_act, hC'_b⟩
          rw [Finset.mem_biUnion] at hC'_b
          rcases hC'_b with ⟨b', _, he'H0⟩
          have hC'_comp := hAct_s hC'_act
          have he'_bun0' : e' ∈ (st_s.bun (C', b')).edges := by
            have h1 := (hBun_s C' hC'_comp b').2.2.2.2.2.1 he'H0
            rw [(hBun_s C' hC'_comp b').2.2.2.1.2.1] at h1
            exact h1
          have hEq := (hBun_disj_s C hC_comp C' hC'_comp b b' e' he'_bun0 he'_bun0').1
          rwa [hEq]
        · rw [Finset.mem_biUnion] at heExt
          rcases heExt with ⟨C', hC'_act, he'Ex⟩
          have hC'_comp := hAct_s hC'_act
          have he'G0 : e' ∈ (st_s.cs.compSt C').G.E :=
            (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp he'Ex).1).1
          have hNotCross : e' ∉ st_s.cs.crossEdges :=
            Finset.disjoint_left.mp hBun0.2.2.1 he'_bun0
          have hEqC := mem_comp_eq_of_mem_bun_and_compG hI_s hG₀_s hC_comp hC'_comp ρ_s
            hBun0.1 hBun0.2.1 he'_bun0 he'G0 hNotCross
          rwa [hEqC]
      · exact False.elim (Finset.disjoint_left.mp hBun0.2.2.1 he'_bun0 heCr)
    have heC0 : e ∈ (coreGraph (D.G s) st_s.cs.lsf).E := by
      rw [← hG_s]
      exact hBun0.1.1 he_bun0
    have he_not_S0 : e ∉ st_s.S_cur.E := by
      intro heS0
      rw [hS_E_s, Finset.mem_union] at heS0
      rcases heS0 with heB0 | heCr0
      · rw [Finset.mem_union] at heB0
        rcases heB0 with heDyn0 | heEx0
        · rw [Finset.mem_biUnion] at heDyn0
          rcases heDyn0 with ⟨C', hC'_act, hb'⟩
          rw [Finset.mem_biUnion] at hb'
          rcases hb' with ⟨b', _, heb'H⟩
          have hC'_comp := hAct_s hC'_act
          have he_bun0' : e ∈ (st_s.bun (C', b')).edges := by
            have h1 := (hBun_s C' hC'_comp b').2.2.2.2.2.1 heb'H
            rw [(hBun_s C' hC'_comp b').2.2.2.1.2.1] at h1
            exact h1
          obtain ⟨rfl, rfl⟩ := hBun_disj_s C' hC'_comp C hC_comp b' b e he_bun0' he_bun0
          have he_not_H1 : e ∉ (st_s1.dyn (C, b)).H.E := fun h =>
            heS1 (hS_E_s1 ▸ Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_biUnion.mpr ⟨C, hC_act1, Finset.mem_biUnion.mpr ⟨b, hb_act1, h⟩⟩)))
          have hstep_b : (info.stepOut (C, b)).state = st_s1.dyn (C, b) := hDyn_cb.2.1
          have hC_info : C ∈ info.state.activeComps := by rw [hact1_eq]; exact hC_act1
          apply he'_notD
          dsimp only [info, stepBundleTree]
          refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨C, hC_info,
            Finset.mem_biUnion.mpr ⟨b, hb_act0,
              Finset.mem_biUnion.mpr ⟨e, Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨heb'H, ?_⟩, ?_⟩, ?_⟩⟩⟩)
          · change e ∈ (info.stepOut (C, b)).state.G.E; rw [hstep_b]; exact heG1_b
          · change e ∉ (info.stepOut (C, b)).state.H.E; rw [hstep_b]; exact he_not_H1
          · change e' ∈ walkEdges (piTotal (info.stepOut (C, b)).state e); rw [hstep_b]; exact hew1
        · rw [Finset.mem_biUnion] at heEx0
          rcases heEx0 with ⟨C', hC'_act, heEx0'⟩
          have hC'_comp := hAct_s hC'_act
          have heG_C' : e ∈ (st_s.cs.compSt C').G.E :=
            (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp heEx0').1).1
          have hNotCross : e ∉ st_s.cs.crossEdges :=
            Finset.disjoint_left.mp hBun0.2.2.1 he_bun0
          have hEqC := mem_comp_eq_of_mem_bun_and_compG hI_s hG₀_s hC_comp hC'_comp ρ_s
            hBun0.1 hBun0.2.1 he_bun0 heG_C' hNotCross
          subst hEqC
          exact (Finset.mem_sdiff.mp heEx0').2
            (Finset.mem_biUnion.mpr ⟨b, hb_act0, he_bun0⟩)
      · exact Finset.disjoint_left.mp hBun0.2.2.1 he_bun0 heCr0
    have hEx0 : ∃ q : Finset ℕ × ℤ, q.1 ∈ st_s.activeComps ∧ q.2 ∈ st_s.activeBuckets q.1 ∧
        e ∈ (st_s.bun q).edges := ⟨(C, b), hC_act0, hb_act0, he_bun0⟩
    have hCh_eq : hEx0.choose = (C, b) := by
      rcases hEx0_ch : hEx0.choose with ⟨C', b'⟩
      have hspec := hEx0.choose_spec
      rw [hEx0_ch] at hspec
      have hC'_comp := hAct_s hspec.1
      obtain ⟨rfl, rfl⟩ := hBun_disj_s C' hC'_comp C hC_comp b' b e hspec.2.2 he_bun0
      rfl
    have hemb0 : st_s.emb e = piTotal (st_s.dyn (C, b)) e := by
      dsimp only [BundleTreeState.emb]
      simp only [he_not_S0, ↓reduceIte, hEx0, ↓reduceDIte, hCh_eq]
    have hew0 : e' ∈ walkEdges (st_s.emb e) := hemb0 ▸ hew0_b
    have hwc_le : walkCount (st_s1.emb e) e' ≤ walkCount (st_s.emb e) e' := by
      have hcnt := hDyn_cb.2.2.2 e heG1_b e' hnotD_b
      rw [← hemb1, ← hemb0] at hcnt
      exact hcnt
    have hnoIns_e : ∀ u ∈ D.U (s + 1), ¬ u.Inserts e := by
      have heGs : e ∈ (D.G s).E := (Finset.mem_sdiff.mp heC0).1
      have he_notDel : e ∉ batchDeletes (D.U (s + 1)) :=
        Finset.disjoint_left.mp (hBun_step C hC_comp b).2 he_bun1
      exact not_inserts_of_not_mem_batchDeletes hBV_U heGs he_notDel
    exact ⟨heC0, hew0, hwc_le, hnoIns_e⟩

end

end MinCostFlow.SparseCore
