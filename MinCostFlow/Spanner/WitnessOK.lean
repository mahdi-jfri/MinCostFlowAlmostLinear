module

public import MinCostFlow.Statement.Cited.Graphs
public import MinCostFlow.Spanner.Embedding
public import MinCostFlow.Spanner.Tools
public import MinCostFlow.Spanner.Subgraph
public import MinCostFlow.Spanner.Algorithm
public import MinCostFlow.Spanner.WitnessProps

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Witness structural invariant (`WitnessOK`) and `buildWitness_ok`

Proves raw component list properties and the main structural invariant `WitnessOK`
for `buildWitness tools H' J embJH` (`buildWitness_ok`).
-/

@[expose] public section

namespace MinCostFlow.Spanner

open MinCostFlow.Cited

/-! ## Raw component list properties -/

theorem rawComps_mem_iff {d : DecomposeOutput} {i : ℕ} {X : Finset ℕ} :
    (i, X) ∈ (List.range d.ℓ).flatMap (fun i' => (d.comps (i' + 1)).map fun Y => (i' + 1, Y)) ↔
      0 < i ∧ i ≤ d.ℓ ∧ X ∈ d.comps i := by
  simp only [List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨i', hi', Y, hY, rfl, rfl⟩
    exact ⟨Nat.zero_lt_succ _, hi', hY⟩
  · rintro ⟨hi0, hiℓ, hX⟩
    refine ⟨i - 1, by omega, X, ?_, by omega, rfl⟩
    simpa [Nat.sub_add_cancel hi0] using hX

theorem rawComps_pairwise {d : DecomposeOutput}
    (hdisj : ∀ i, 0 < i → i ≤ d.ℓ → (d.comps i).Pairwise Disjoint) :
    ((List.range d.ℓ).flatMap (fun i' => (d.comps (i' + 1)).map fun Y => (i' + 1, Y))).Pairwise
      (fun a b => a.1 ≠ b.1 ∨ Disjoint a.2 b.2) := by
  have h1 : ∀ (l : List ℕ) (f : ℕ → List (ℕ × Finset ℕ)),
      l.Pairwise (· ≠ ·) →
      (∀ i ∈ l, (f i).Pairwise (fun a b => a.1 = i + 1 ∧ b.1 = i + 1 ∧ Disjoint a.2 b.2) ∧
        ∀ p ∈ f i, p.1 = i + 1) →
      (l.flatMap f).Pairwise (fun a b => a.1 ≠ b.1 ∨ Disjoint a.2 b.2) := by
    intro l f hl hf
    induction l with
    | nil => simp
    | cons a as ih =>
      simp only [List.pairwise_cons] at hl
      simp only [List.flatMap_cons, List.pairwise_append]
      refine ⟨?_, ih hl.2 (fun i hi => hf i (List.mem_cons_of_mem a hi)), ?_⟩
      · exact (hf a List.mem_cons_self).1.imp fun h => Or.inr h.2.2
      · intro p hp q hq
        rw [List.mem_flatMap] at hq
        obtain ⟨b, hb, hqb⟩ := hq
        have hp1 := (hf a List.mem_cons_self).2 p hp
        have hq1 := (hf b (List.mem_cons_of_mem a hb)).2 q hqb
        have hne : a ≠ b := hl.1 b hb
        exact Or.inl (by omega)
  exact h1 (List.range d.ℓ) (fun i' => (d.comps (i' + 1)).map fun Y => (i' + 1, Y))
    (List.nodup_iff_pairwise_ne.mp List.nodup_range) (fun i hi => by
      rw [List.mem_range] at hi
      have hdi := hdisj (i + 1) (Nat.zero_lt_succ i) hi
      refine ⟨?_, ?_⟩
      · rw [List.pairwise_map]
        exact hdi.imp (fun h => ⟨rfl, rfl, h⟩)
      · intro p hp
        rcases List.mem_map.mp hp with ⟨Y, _, rfl⟩
        rfl)

theorem buildComps_mem {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (J0_strip : Graph) (nlIdx : List ℕ)
    (decomp : DecomposeOutput) (φ_dec : ℝ) :
    ∀ offset raw c, c ∈ buildComps tools J0_strip nlIdx decomp φ_dec offset raw →
      (c.level, c.X) ∈ raw ∧
      c.verts = vertsOf c.X ∧
      c.J_sub = inducedSubgraph (decomp.graphAt J0_strip c.level) c.X ∧
      c.jSubOrigEdges = (insideIndices (decomp.graphAt J0_strip c.level) c.X).map
        (fun a => nlIdx.getD ((decomp.edgesAt J0_strip c.level).getD a 0) 0) ∧
      c.W_sub = tools.constructExpander.construct c.X.card
        (fun k => ((decomp.graphAt J0_strip c.level).degIn c.X (c.verts.getD k 0) : ℝ) /
          (φ_dec * (2 ^ c.level : ℝ))) := by
  intro offset raw
  induction raw generalizing offset with
  | nil => simp [buildComps]
  | cons p rest ih =>
    intro c hc
    simp only [buildComps, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ⟨List.mem_cons_self, rfl, rfl, rfl, rfl⟩
    · obtain ⟨h1, h2⟩ := ih _ c hc
      exact ⟨List.mem_cons_of_mem p h1, h2⟩

theorem buildComps_map_pair {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (J0_strip : Graph) (nlIdx : List ℕ)
    (decomp : DecomposeOutput) (φ_dec : ℝ) :
    ∀ offset raw, (buildComps tools J0_strip nlIdx decomp φ_dec offset raw).map
        (fun c => (c.level, c.X)) = raw := by
  intro offset raw
  induction raw generalizing offset with
  | nil => simp [buildComps]
  | cons p rest ih =>
    simp only [buildComps, List.map_cons, ih]

theorem map_getD_nodup {l idx : List ℕ} (hl : l.Nodup) (hidx : idx.Nodup)
    (hlt : ∀ a ∈ idx, a < l.length) :
    (idx.map fun a => l.getD a 0).Nodup := by
  rw [List.nodup_map_iff_inj_on hidx]
  intro a ha b hb hab
  have ha' := hlt a ha
  have hb' := hlt b hb
  rw [List.getD_eq_getElem _ _ ha', List.getD_eq_getElem _ _ hb'] at hab
  exact (hl.getElem_inj_iff).mp hab

private theorem sum_vertsOf_degIn_eq_volIn (G : Graph) (X : Finset ℕ) :
    (∑ k ∈ Finset.range X.card, (G.degIn X ((vertsOf X).getD k 0) : ℝ)) = (G.volIn X X : ℝ) := by
  rw [← Nat.cast_sum]
  congr 1
  unfold Graph.volIn
  rw [← Finset.sum_image (f := G.degIn X) (g := fun k => (vertsOf X).getD k 0) (by
    intro a ha b hb hab
    have ha' : a < X.card := Finset.mem_range.mp ha
    have hb' : b < X.card := Finset.mem_range.mp hb
    dsimp only at hab
    rw [← idxOf_getD_vertsOf ha', hab, idxOf_getD_vertsOf hb'])]
  congr 1
  ext v
  simp only [Finset.mem_image, Finset.mem_range]
  exact ⟨fun ⟨k, hk, hv⟩ => hv ▸ getD_vertsOf_mem hk,
         fun hv => ⟨(vertsOf X).idxOf v, idxOf_lt_card hv, getD_vertsOf_idxOf hv⟩⟩

/-! ## Main structural invariant package for `WitnessData` -/

/-- Witness bundle of Task 1 preconditions and structural invariants. -/
structure WitnessOK {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (wd : WitnessData) : Prop where
  W_n : wd.W.n = J.n
  W_valid : wd.W.IsValid
  W_m_eq : wd.W.m = wd.j0Edges.length + (wd.comps.map fun c => c.W_sub.m).sum
  aligned : CompsAligned wd.j0Edges.length wd.comps
  φ_dec_pos : 0 < wd.φ_dec
  φ_dec_le : wd.φ_dec ≤ 1
  φ_Const_pos : 0 < wd.φ_Const
  φ_Const_le : wd.φ_Const ≤ 1
  c_deg_ge : 1 ≤ wd.c_deg
  φ_ds_pos : 0 < wd.φ_ds
  φ_ds_le_dec : wd.φ_ds ≤ wd.φ_dec
  φ_ds_le_Const : wd.φ_ds ≤ wd.φ_Const
  φ_ds_half : wd.φ_ds ≤ 1 / 2
  γ_ExpPath_ge : 1 / wd.φ_ds ≤ wd.γ_ExpPath
  γ_del_ge : 1 ≤ wd.γ_del
  τ₁_nonneg : 0 ≤ wd.τ₁
  τ₂_pos : 0 < wd.τ₂
  j0_nodup : wd.j0Edges.Nodup
  j0_lt : ∀ j ∈ wd.j0Edges, j < J.m
  comp_props : ∀ ci (hci : ci < wd.comps.length),
    let c := wd.comps[ci]'hci
    0 < c.level ∧ c.level ≤ wd.decomp.ℓ ∧
    c.X ⊆ J.verts ∧ 2 ≤ c.X.card ∧ c.verts = vertsOf c.X ∧
    c.J_sub.n = c.X.card ∧ c.J_sub.IsValid ∧ 1 ≤ c.J_sub.m ∧ c.J_sub.m ≤ wd.J0_strip.m ∧
    (∀ k < c.X.card, 1 ≤ c.J_sub.deg k) ∧
    c.J_sub.IsConductanceExpanderOn c.J_sub.verts wd.φ_dec ∧
    c.W_sub.n = c.X.card ∧ c.W_sub.IsValid ∧ 1 ≤ c.W_sub.m ∧ c.W_sub.m ≤ wd.M_W ∧
    (∀ k < c.X.card, 1 ≤ c.W_sub.deg k) ∧
    c.W_sub.IsConductanceExpanderOn c.W_sub.verts wd.φ_Const ∧
    (∀ k < c.X.card, (c.J_sub.deg k : ℝ) / (wd.φ_dec * (2 ^ c.level : ℝ)) ≤ c.W_sub.deg k ∧
      (c.W_sub.deg k : ℝ) ≤ wd.c_deg * ((c.J_sub.deg k : ℝ) / (wd.φ_dec * (2 ^ c.level : ℝ)))) ∧
    (∀ k < c.X.card, wd.φ_dec * (2 ^ c.level : ℝ) ≤ (c.J_sub.deg k : ℝ)) ∧
    c.jSubOrigEdges.length = c.J_sub.m ∧ c.jSubOrigEdges.Nodup ∧
    (∀ j ∈ c.jSubOrigEdges, j < J.m) ∧
    wd.j0Edges.length ≤ c.wStart ∧ c.wStart + c.W_sub.m ≤ wd.W.m
  comp_disjoint : ∀ ci₁ ci₂ (h1 : ci₁ < wd.comps.length) (h2 : ci₂ < wd.comps.length),
    ci₁ ≠ ci₂ →
    Disjoint (wd.comps[ci₁]'h1).jSubOrigEdges.toFinset (wd.comps[ci₂]'h2).jSubOrigEdges.toFinset
  comp_disjoint_j0 : ∀ ci (hci : ci < wd.comps.length),
    Disjoint (wd.comps[ci]'hci).jSubOrigEdges.toFinset wd.j0Edges.toFinset

theorem buildWitness_ok {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid) (_hembJH : IsEmbedding J H' embJH)
    (hNmax : J.n ≤ N_max)
    (hWmax : 2 * (J.m : ℝ) / tools.decompose.φ_dec (stripLoops J) ≤ W_max) :
    WitnessOK tools H' J embJH (buildWitness tools H' J embJH) := by
  let wd := buildWitness tools H' J embJH
  have hSL_valid : wd.J0_strip.IsValid := stripLoops_isValid hJ
  have hSL_loopless : wd.J0_strip.IsLoopless := stripLoops_isLoopless J
  have hSL_m_le : wd.J0_strip.m ≤ J.m := stripLoops_m_le J
  have hnl_len : wd.nlIdx.length = wd.J0_strip.m := by
    simp [wd, buildWitness, stripLoops, Graph.m]
  have hnl_len_raw : (nonloopIndices J).length = (stripLoops J).m := by
    simpa [wd, buildWitness] using hnl_len
  have hnl_nodup : wd.nlIdx.Nodup := nonloopIndices_nodup J
  have hnl_lt : ∀ k (hk : k < wd.nlIdx.length), (wd.nlIdx[k]'hk) < J.m := fun k hk => by
    have hmem : (wd.nlIdx[k]'hk) ∈ nonloopIndices J := List.getElem_mem hk
    exact (mem_nonloopIndices.mp hmem).1
  have hdec_spec := tools.decompose.decompose_spec wd.J0_strip hSL_valid hSL_loopless
  have hφ_dec_pos : 0 < wd.φ_dec := tools.decompose.hφ_pos wd.J0_strip hSL_valid hSL_loopless
  have hφ_dec_le : wd.φ_dec ≤ 1 := tools.decompose.hφ_le wd.J0_strip hSL_valid hSL_loopless
  have hφ_Const_pos : 0 < wd.φ_Const := tools.constructExpander.hφ_pos
  have hφ_Const_le : wd.φ_Const ≤ 1 := tools.constructExpander.hφ_le
  have hc_deg_ge : 1 ≤ wd.c_deg := tools.constructExpander.hc_deg
  have hφ_J_pos := tools.pathDS.hφ_pos wd.φ_dec wd.J0_strip.m hφ_dec_pos
  have hφ_J_le := tools.pathDS.hφ_le wd.φ_dec wd.J0_strip.m hφ_dec_pos
  have hφ_J_half := tools.pathDS.hφ_half wd.φ_dec wd.J0_strip.m hφ_dec_pos
  have hφ_W_pos := tools.pathDS.hφ_pos wd.φ_Const wd.M_W hφ_Const_pos
  have hφ_W_le := tools.pathDS.hφ_le wd.φ_Const wd.M_W hφ_Const_pos
  have hφ_W_half := tools.pathDS.hφ_half wd.φ_Const wd.M_W hφ_Const_pos
  have hφ_ds_pos : 0 < wd.φ_ds := lt_min hφ_J_pos hφ_W_pos
  have hφ_ds_le_dec : wd.φ_ds ≤ wd.φ_dec := le_trans (min_le_left _ _) hφ_J_le
  have hφ_ds_le_Const : wd.φ_ds ≤ wd.φ_Const := le_trans (min_le_right _ _) hφ_W_le
  have hφ_ds_half : wd.φ_ds ≤ 1 / 2 := le_trans (min_le_left _ _) hφ_J_half
  have hγ_ExpPath_ge : 1 / wd.φ_ds ≤ wd.γ_ExpPath := by
    have h1 := tools.pathDS.hγ_ExpPath_ge wd.φ_dec wd.J0_strip.m hφ_dec_pos
    have h2 := tools.pathDS.hγ_ExpPath_ge wd.φ_Const wd.M_W hφ_Const_pos
    change 1 / min (tools.pathDS.φ_out wd.φ_dec wd.J0_strip.m)
      (tools.pathDS.φ_out wd.φ_Const wd.M_W) ≤
      max (tools.pathDS.γ_ExpPath wd.φ_dec wd.J0_strip.m)
          (tools.pathDS.γ_ExpPath wd.φ_Const wd.M_W)
    rcases min_cases (tools.pathDS.φ_out wd.φ_dec wd.J0_strip.m)
        (tools.pathDS.φ_out wd.φ_Const wd.M_W) with ⟨hm, _⟩ | ⟨hm, _⟩
    · rw [hm]; exact le_trans h1 (le_max_left _ _)
    · rw [hm]; exact le_trans h2 (le_max_right _ _)
  have hγ_del_ge : 1 ≤ wd.γ_del :=
    le_trans (tools.pathDS.hγ_del_ge wd.φ_dec wd.J0_strip.m hφ_dec_pos) (le_max_left _ _)
  have hτ₁_nonneg : 0 ≤ wd.τ₁ := by
    have hv := vcong_nonneg J H' (fun _ => 1) embJH
    have hγE : 0 < wd.γ_ExpPath := lt_of_lt_of_le (by positivity) hγ_ExpPath_ge
    change 0 ≤ 2 * wd.γ_ExpPath * (length J embJH : ℝ) * wd.γ_del *
      (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) / wd.φ_ds
    positivity
  have hτ₂_pos : 0 < wd.τ₂ := by
    have hγE : 0 < wd.γ_ExpPath := lt_of_lt_of_le (by positivity) hγ_ExpPath_ge
    change 0 < wd.γ_ExpPath * wd.γ_del / wd.φ_ds
    positivity
  set rawComps := (List.range wd.decomp.ℓ).flatMap fun i' =>
    (wd.decomp.comps (i' + 1)).map fun X => (i' + 1, X)
  have haligned : CompsAligned wd.j0Edges.length wd.comps :=
    buildComps_aligned tools wd.J0_strip wd.nlIdx wd.decomp wd.φ_dec wd.j0Edges.length rawComps
  have hWm_eq : wd.W.m = wd.j0Edges.length + (wd.comps.map fun c => c.W_sub.m).sum := by
    change (wd.j0Edges.map _ ++ wd.comps.flatMap compWEdges).length = _
    rw [List.length_append, List.length_map, compsAligned_sum_m]
  have hj0_nodup : wd.j0Edges.Nodup := by
    refine map_getD_nodup hnl_nodup (List.Nodup.filter _ List.nodup_range) fun a ha => ?_
    simp only [DecomposeOutput.edgesAt, List.mem_filter, List.mem_range] at ha
    omega
  have hj0_lt : ∀ j ∈ wd.j0Edges, j < J.m := by
    intro j hj
    simp only [wd, buildWitness, DecomposeOutput.edgesAt, List.mem_map, List.mem_filter,
      List.mem_range] at hj
    obtain ⟨a, ⟨ha, _⟩, rfl⟩ := hj
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hnl_lt a (by simp only [wd, buildWitness]; omega)
  have hcomp_props : ∀ ci (hci : ci < wd.comps.length),
      let c := wd.comps[ci]'hci
      0 < c.level ∧ c.level ≤ wd.decomp.ℓ ∧
      c.X ⊆ J.verts ∧ 2 ≤ c.X.card ∧ c.verts = vertsOf c.X ∧
      c.J_sub.n = c.X.card ∧ c.J_sub.IsValid ∧ 1 ≤ c.J_sub.m ∧ c.J_sub.m ≤ wd.J0_strip.m ∧
      (∀ k < c.X.card, 1 ≤ c.J_sub.deg k) ∧
      c.J_sub.IsConductanceExpanderOn c.J_sub.verts wd.φ_dec ∧
      c.W_sub.n = c.X.card ∧ c.W_sub.IsValid ∧ 1 ≤ c.W_sub.m ∧ c.W_sub.m ≤ wd.M_W ∧
      (∀ k < c.X.card, 1 ≤ c.W_sub.deg k) ∧
      c.W_sub.IsConductanceExpanderOn c.W_sub.verts wd.φ_Const ∧
      (∀ k < c.X.card, (c.J_sub.deg k : ℝ) / (wd.φ_dec * (2 ^ c.level : ℝ)) ≤ c.W_sub.deg k ∧
        (c.W_sub.deg k : ℝ) ≤ wd.c_deg * ((c.J_sub.deg k : ℝ) / (wd.φ_dec * (2 ^ c.level : ℝ)))) ∧
      (∀ k < c.X.card, wd.φ_dec * (2 ^ c.level : ℝ) ≤ (c.J_sub.deg k : ℝ)) ∧
      c.jSubOrigEdges.length = c.J_sub.m ∧ c.jSubOrigEdges.Nodup ∧
      (∀ j ∈ c.jSubOrigEdges, j < J.m) ∧
      wd.j0Edges.length ≤ c.wStart ∧ c.wStart + c.W_sub.m ≤ wd.W.m := by
    intro ci hci
    dsimp only
    set c := wd.comps[ci]'hci
    have hmem := buildComps_mem tools wd.J0_strip wd.nlIdx wd.decomp wd.φ_dec
      wd.j0Edges.length rawComps c (List.getElem_mem hci)
    rcases hmem with ⟨hraw, hverts_eq, hJsub_eq, hjOrig_eq, hWsub_eq⟩
    rcases rawComps_mem_iff.mp hraw with ⟨hi0, hiℓ, hXcomp⟩
    have hdi := (hdec_spec.2.2.2 c.level hi0 hiℓ).2.1 c.X hXcomp
    rcases hdi with ⟨hXJ, hX2, hExpJi, hdegJi, hclosed⟩
    have hXJ' : c.X ⊆ J.verts := by simpa [wd, buildWitness, stripLoops, Graph.verts] using hXJ
    set J_i := wd.decomp.graphAt wd.J0_strip c.level
    have hJ_sub_m : c.J_sub.m = (J_i.inside c.X).length := by
      rw [hJsub_eq]; exact inducedSubgraph_m J_i c.X
    have hJ_i_m : J_i.m ≤ wd.J0_strip.m := by
      simp only [J_i, DecomposeOutput.graphAt, DecomposeOutput.edgesAt, Graph.m, List.length_map]
      exact le_trans (List.length_filter_le _ _) (by simp)
    have hinside_le : (J_i.inside c.X).length ≤ J_i.m := by
      unfold Graph.inside Graph.m
      exact List.length_filter_le _ _
    have hJ_sub_deg : ∀ k < c.X.card, c.J_sub.deg k = J_i.degIn c.X (c.verts.getD k 0) := by
      intro k hk
      rw [hJsub_eq, hverts_eq]
      exact inducedSubgraph_deg hk
    have hdeg_ge_phi : ∀ k < c.X.card, wd.φ_dec * (2 ^ c.level : ℝ) ≤ (c.J_sub.deg k : ℝ) := by
      intro k hk
      rw [hJ_sub_deg k hk]
      exact hdegJi _ (by rw [hverts_eq]; exact getD_vertsOf_mem hk)
    have hdeg_pos : ∀ k < c.X.card, 1 ≤ c.J_sub.deg k := by
      intro k hk
      have hpos : (0 : ℝ) < (c.J_sub.deg k : ℝ) :=
        lt_of_lt_of_le (by positivity) (hdeg_ge_phi k hk)
      exact Nat.cast_pos.mp hpos
    have hJ_sub_vol : c.J_sub.vol c.J_sub.verts = 2 * c.J_sub.m :=
      vol_verts_eq_two_mul_m (by rw [hJsub_eq]; exact inducedSubgraph_isValid J_i c.X)
    have hJ_sub_m_pos : 1 ≤ c.J_sub.m := by
      have hvol : c.X.card ≤ c.J_sub.vol c.J_sub.verts := by
        unfold Graph.vol Graph.volIn
        rw [hJsub_eq]
        calc c.X.card = ∑ _k ∈ Finset.range c.X.card, 1 := by simp
          _ ≤ ∑ k ∈ Finset.range c.X.card, (inducedSubgraph J_i c.X).degIn
                (inducedSubgraph J_i c.X).verts k := Finset.sum_le_sum fun k hk => by
                  simpa [hJsub_eq, Graph.deg] using hdeg_pos k (Finset.mem_range.mp hk)
      omega
    have hwVec_ge : ∀ k < c.X.card,
        1 ≤ (J_i.degIn c.X (c.verts.getD k 0) : ℝ) / (wd.φ_dec * (2 ^ c.level : ℝ)) := by
      intro k hk
      rw [one_le_div (by positivity)]
      rw [← hJ_sub_deg k hk]
      exact hdeg_ge_phi k hk
    have hwVec_sum : (∑ k ∈ Finset.range c.X.card,
        (J_i.degIn c.X (c.verts.getD k 0) : ℝ) / (wd.φ_dec * (2 ^ c.level : ℝ))) ≤ W_max := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul, ← div_eq_mul_inv, hverts_eq, sum_vertsOf_degIn_eq_volIn,
        volIn_self_eq_two_mul_inside]
      have h2pow : (2 : ℝ) ≤ (2 ^ c.level : ℝ) := by
        have : 2 ≤ 2 ^ c.level := Nat.le_self_pow hi0.ne' 2
        exact_mod_cast this
      have hinside_leJ : ((J_i.inside c.X).length : ℝ) ≤ (J.m : ℝ) := by
        exact_mod_cast le_trans hinside_le (le_trans hJ_i_m hSL_m_le)
      calc ((2 * (J_i.inside c.X).length : ℕ) : ℝ) / (wd.φ_dec * (2 ^ c.level : ℝ))
          = (2 * ((J_i.inside c.X).length : ℝ)) / (wd.φ_dec * (2 ^ c.level : ℝ)) := by push_cast; rfl
        _ ≤ (2 * (J.m : ℝ)) / (wd.φ_dec * 2) :=
            div_le_div₀ (by positivity) (by gcongr) (by positivity) (by gcongr)
        _ ≤ (2 * (J.m : ℝ)) / wd.φ_dec := by
            gcongr; linarith
        _ ≤ W_max := hWmax
    have hce_spec := tools.constructExpander.construct_spec c.X.card
      (fun k => (J_i.degIn c.X (c.verts.getD k 0) : ℝ) / (wd.φ_dec * (2 ^ c.level : ℝ)))
      (by omega)
      (le_trans (Finset.card_le_card hXJ') (le_trans (by rw [Graph.verts, Finset.card_range]) hNmax))
      hwVec_ge hwVec_sum
    dsimp only at hce_spec
    rw [← hWsub_eq] at hce_spec
    rcases hce_spec with ⟨hWn, hWvalid, hWexp, hWdeg⟩
    have hWdeg_pos : ∀ k < c.X.card, 1 ≤ c.W_sub.deg k := by
      intro k hk
      have h1 : (1 : ℝ) ≤ (c.W_sub.deg k : ℝ) := le_trans (hwVec_ge k hk) (hWdeg k hk).1
      exact Nat.one_le_cast.mp h1
    have hW_vol : c.W_sub.vol c.W_sub.verts = 2 * c.W_sub.m := vol_verts_eq_two_mul_m hWvalid
    have hW_m_pos : 1 ≤ c.W_sub.m := by
      have hvol : c.X.card ≤ c.W_sub.vol c.W_sub.verts := by
        unfold Graph.vol Graph.volIn
        rw [Graph.verts, hWn]
        calc c.X.card = ∑ _k ∈ Finset.range c.X.card, 1 := by simp
          _ ≤ ∑ k ∈ Finset.range c.X.card, c.W_sub.degIn (Finset.range c.X.card) k :=
              Finset.sum_le_sum fun k hk => by
                simpa [Graph.deg, Graph.verts, hWn] using hWdeg_pos k (Finset.mem_range.mp hk)
      omega
    have hW_m_le_MW : c.W_sub.m ≤ wd.M_W := by
      have h2m_real : (2 * (c.W_sub.m : ℝ)) ≤
          wd.c_deg * (2 * ((J_i.inside c.X).length : ℝ)) / (wd.φ_dec * (2 ^ c.level : ℝ)) := by
        have hsum_eq : (2 * (c.W_sub.m : ℝ)) =
            ∑ k ∈ Finset.range c.X.card, (c.W_sub.deg k : ℝ) := by
          have : 2 * c.W_sub.m = ∑ k ∈ Finset.range c.X.card, c.W_sub.deg k := by
            rw [← hW_vol]; unfold Graph.vol Graph.volIn Graph.deg; rw [Graph.verts, hWn]
          exact_mod_cast this
        rw [hsum_eq]
        calc ∑ k ∈ Finset.range c.X.card, (c.W_sub.deg k : ℝ)
            ≤ ∑ k ∈ Finset.range c.X.card,
                wd.c_deg * ((J_i.degIn c.X (c.verts.getD k 0) : ℝ) / (wd.φ_dec * (2 ^ c.level : ℝ))) :=
              Finset.sum_le_sum fun k hk => (hWdeg k (Finset.mem_range.mp hk)).2
          _ = wd.c_deg * ((∑ k ∈ Finset.range c.X.card, (J_i.degIn c.X (c.verts.getD k 0) : ℝ)) /
                (wd.φ_dec * (2 ^ c.level : ℝ))) := by
              rw [← Finset.mul_sum]
              simp_rw [div_eq_mul_inv]
              rw [← Finset.sum_mul]
          _ = wd.c_deg * (2 * ((J_i.inside c.X).length : ℝ)) / (wd.φ_dec * (2 ^ c.level : ℝ)) := by
              rw [hverts_eq, sum_vertsOf_degIn_eq_volIn, volIn_self_eq_two_mul_inside]
              push_cast; ring
      have h2pow : (2 : ℝ) ≤ (2 ^ c.level : ℝ) := by
        exact_mod_cast Nat.le_self_pow hi0.ne' 2
      have hinside_le_strip : ((J_i.inside c.X).length : ℝ) ≤ (wd.J0_strip.m : ℝ) := by
        exact_mod_cast le_trans hinside_le hJ_i_m
      have hm_le_ceil : (c.W_sub.m : ℝ) ≤ wd.c_deg * (wd.J0_strip.m : ℝ) / wd.φ_dec := by
        calc (c.W_sub.m : ℝ)
            ≤ (wd.c_deg * (2 * ((J_i.inside c.X).length : ℝ)) / (wd.φ_dec * (2 ^ c.level : ℝ))) / 2 := by
              linarith
          _ = wd.c_deg * ((J_i.inside c.X).length : ℝ) / (wd.φ_dec * (2 ^ c.level : ℝ)) := by ring
          _ ≤ wd.c_deg * (wd.J0_strip.m : ℝ) / (wd.φ_dec * 2) :=
              div_le_div₀ (by positivity) (by gcongr) (by positivity) (by gcongr)
          _ ≤ wd.c_deg * (wd.J0_strip.m : ℝ) / wd.φ_dec := by
              gcongr; linarith
      have hceil : c.W_sub.m ≤ Nat.ceil (wd.c_deg * (wd.J0_strip.m : ℝ) / wd.φ_dec) :=
        Nat.le_ceil _ |>.trans' (Nat.cast_le.mp (le_trans hm_le_ceil (Nat.le_ceil _)))
      exact le_trans hceil (Nat.le_succ _)
    have hjSub_edges_len : (wd.decomp.edgesAt wd.J0_strip c.level).length = J_i.m := by
      simp [J_i, DecomposeOutput.graphAt, Graph.m]
    have hjOrig_len : c.jSubOrigEdges.length = c.J_sub.m := by
      rw [hjOrig_eq, List.length_map, hJ_sub_m, ← insideIndices_map_eq_inside J_i c.X, List.length_map]
    have hidx_nodup : (insideIndices J_i c.X).Nodup := insideIndices_nodup J_i c.X
    have hidx_lt : ∀ a ∈ insideIndices J_i c.X, a < (wd.decomp.edgesAt wd.J0_strip c.level).length := by
      intro a ha
      rw [hjSub_edges_len]
      exact (mem_insideIndices.mp ha).1
    have hed_nodup : (wd.decomp.edgesAt wd.J0_strip c.level).Nodup :=
      List.Nodup.filter _ List.nodup_range
    have hed_lt : ∀ b ∈ wd.decomp.edgesAt wd.J0_strip c.level, b < wd.nlIdx.length := by
      intro b hb
      simp only [DecomposeOutput.edgesAt, List.mem_filter, List.mem_range] at hb
      omega
    have hjOrig_nodup : c.jSubOrigEdges.Nodup := by
      have hcomp : c.jSubOrigEdges =
          ((insideIndices J_i c.X).map fun a =>
            (wd.decomp.edgesAt wd.J0_strip c.level).getD a 0).map (fun b => wd.nlIdx.getD b 0) := by
        rw [hjOrig_eq, List.map_map]; rfl
      rw [hcomp]
      refine map_getD_nodup hnl_nodup (map_getD_nodup hed_nodup hidx_nodup hidx_lt) fun j hj => ?_
      simp only [List.mem_map] at hj
      rcases hj with ⟨a, ha, rfl⟩
      have ha' := hidx_lt a ha
      rw [List.getD_eq_getElem _ _ ha']
      exact hed_lt _ (List.getElem_mem ha')
    have hjOrig_lt : ∀ j ∈ c.jSubOrigEdges, j < J.m := by
      intro j hj
      rw [hjOrig_eq, List.mem_map] at hj
      rcases hj with ⟨a, ha, rfl⟩
      have ha' := hidx_lt a ha
      rw [List.getD_eq_getElem _ _ ha']
      have hb' := hed_lt _ (List.getElem_mem ha')
      rw [List.getD_eq_getElem _ _ hb']
      exact hnl_lt _ hb'
    have hwStart_ge : wd.j0Edges.length ≤ c.wStart :=
      compsAligned_wStart_ge haligned c (List.getElem_mem hci)
    have hwEnd_le : c.wStart + c.W_sub.m ≤ wd.W.m := by
      rw [hWm_eq]
      exact compsAligned_wEnd_le haligned ci hci
    exact ⟨hi0, hiℓ, hXJ', hX2, hverts_eq, hJsub_eq ▸ rfl, hJsub_eq ▸ inducedSubgraph_isValid J_i c.X,
      hJ_sub_m_pos, hJ_sub_m ▸ le_trans hinside_le hJ_i_m, hdeg_pos,
      hJsub_eq ▸ inducedSubgraph_isConductanceExpander hExpJi, hWn, hWvalid, hW_m_pos, hW_m_le_MW,
      hWdeg_pos, hWexp, fun k hk => ⟨by rw [hJ_sub_deg k hk]; exact (hWdeg k hk).1,
        by rw [hJ_sub_deg k hk]; exact (hWdeg k hk).2⟩,
      hdeg_ge_phi, hjOrig_len, hjOrig_nodup, hjOrig_lt, hwStart_ge, hwEnd_le⟩
  have hW_valid : wd.W.IsValid := by
    intro e he
    change e ∈ wd.j0Edges.map (fun jOrig => J.edges.getD jOrig (0, 0)) ++
        wd.comps.flatMap compWEdges at he
    rcases List.mem_append.mp he with he0 | hec
    · rcases List.mem_map.mp he0 with ⟨jOrig, hjOrig, rfl⟩
      have hj := hj0_lt jOrig hjOrig
      rw [List.getD_eq_getElem _ _ hj]
      exact hJ _ (List.getElem_mem hj)
    · rcases List.mem_flatMap.mp hec with ⟨c, hc, heW⟩
      rcases List.mem_iff_getElem.mp hc with ⟨ci, hci, rfl⟩
      rcases hcomp_props ci hci with
        ⟨_, _, hXJ_c, _, hverts_c, _, _, _, _, _, _, hWn_c, hWvalid_c, _⟩
      rcases List.mem_map.mp heW with ⟨eL, heL, rfl⟩
      have heL_lt := hWvalid_c eL heL
      rw [hWn_c] at heL_lt
      have h1 : (wd.comps[ci]'hci).verts.getD eL.1 0 ∈ J.verts := by
        rw [hverts_c]
        exact hXJ_c (getD_vertsOf_mem heL_lt.1)
      have h2 : (wd.comps[ci]'hci).verts.getD eL.2 0 ∈ J.verts := by
        rw [hverts_c]
        exact hXJ_c (getD_vertsOf_mem heL_lt.2)
      exact ⟨Finset.mem_range.mp h1, Finset.mem_range.mp h2⟩
  have hjSub_mem_preimage : ∀ ci (hci : ci < wd.comps.length) (jOrig : ℕ),
      jOrig ∈ (wd.comps[ci]'hci).jSubOrigEdges →
      ∃ (b : ℕ) (hb : b < wd.J0_strip.m),
        (wd.nlIdx[b]'(by omega)) = jOrig ∧
        wd.decomp.level b = (wd.comps[ci]'hci).level ∧
        (wd.J0_strip.edges[b]'(by simpa [Graph.m] using hb)).1 ∈ (wd.comps[ci]'hci).X ∧
        (wd.J0_strip.edges[b]'(by simpa [Graph.m] using hb)).2 ∈ (wd.comps[ci]'hci).X := by
    intro ci hci jOrig hj
    set c := wd.comps[ci]'hci
    obtain ⟨_, _, _, hjo, _⟩ := buildComps_mem tools wd.J0_strip wd.nlIdx wd.decomp wd.φ_dec
      wd.j0Edges.length rawComps c (List.getElem_mem hci)
    rw [hjo, List.mem_map] at hj
    rcases hj with ⟨a, ha, rfl⟩
    set J_i := wd.decomp.graphAt wd.J0_strip c.level
    have ha' := mem_insideIndices.mp ha
    have ha_len : a < (wd.decomp.edgesAt wd.J0_strip c.level).length := by
      simpa [J_i, DecomposeOutput.graphAt, Graph.m] using ha'.1
    set b := (wd.decomp.edgesAt wd.J0_strip c.level).getD a 0
    have hb_mem : b ∈ wd.decomp.edgesAt wd.J0_strip c.level := by
      dsimp only [b]; rw [List.getD_eq_getElem _ _ ha_len]; exact List.getElem_mem ha_len
    simp only [DecomposeOutput.edgesAt, List.mem_filter, List.mem_range, decide_eq_true_eq] at hb_mem
    have hb_m : b < wd.J0_strip.m := hb_mem.1
    refine ⟨b, hb_m, ?_, hb_mem.2, ?_⟩
    · rw [List.getD_eq_getElem _ _ (by omega)]
    · have hJi_eq : J_i.edges.getD a (0, 0) = wd.J0_strip.edges[b]'(by simpa [Graph.m] using hb_m) := by
        have hba : (wd.decomp.edgesAt wd.J0_strip c.level)[a]'ha_len = b :=
          (List.getD_eq_getElem _ _ ha_len).symm
        simp only [J_i, DecomposeOutput.graphAt]
        rw [List.getD_eq_getElem _ _ (by simpa [List.length_map] using ha_len), List.getElem_map,
          hba, List.getD_eq_getElem _ _ (by simpa [Graph.m] using hb_m)]
      rw [← hJi_eq]
      exact ha'.2
  have hcomp_disj : ∀ ci₁ ci₂ (h1 : ci₁ < wd.comps.length) (h2 : ci₂ < wd.comps.length),
      ci₁ ≠ ci₂ →
      Disjoint (wd.comps[ci₁]'h1).jSubOrigEdges.toFinset (wd.comps[ci₂]'h2).jSubOrigEdges.toFinset := by
    intro ci₁ ci₂ h1 h2 hne
    rw [Finset.disjoint_left]
    intro jOrig hj1 hj2
    rw [List.mem_toFinset] at hj1 hj2
    obtain ⟨b₁, hb1m, hb1nl, hb1lvl, hb1X, _⟩ := hjSub_mem_preimage ci₁ h1 jOrig hj1
    obtain ⟨b₂, hb2m, hb2nl, hb2lvl, hb2X, _⟩ := hjSub_mem_preimage ci₂ h2 jOrig hj2
    have hb_eq : b₁ = b₂ := by
      rw [← hb2nl] at hb1nl
      exact (hnl_nodup.getElem_inj_iff).mp hb1nl
    subst hb_eq
    have hp := rawComps_pairwise (d := wd.decomp) (fun i hi0 hiℓ => (hdec_spec.2.2.2 i hi0 hiℓ).1)
    have hclen : wd.comps.length = rawComps.length :=
      buildComps_length tools wd.J0_strip wd.nlIdx wd.decomp wd.φ_dec wd.j0Edges.length rawComps
    have h1r : ci₁ < rawComps.length := by omega
    have h2r : ci₂ < rawComps.length := by omega
    have hpair1 := buildComps_getElem tools wd.J0_strip wd.nlIdx wd.decomp wd.φ_dec
      wd.j0Edges.length rawComps ci₁ h1r
    have hpair2 := buildComps_getElem tools wd.J0_strip wd.nlIdx wd.decomp wd.φ_dec
      wd.j0Edges.length rawComps ci₂ h2r
    have hrel : (rawComps[ci₁]'h1r).1 ≠ (rawComps[ci₂]'h2r).1 ∨
        Disjoint (rawComps[ci₁]'h1r).2 (rawComps[ci₂]'h2r).2 := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact List.pairwise_iff_getElem.mp hp ci₁ ci₂ h1r h2r hlt
      · rcases List.pairwise_iff_getElem.mp hp ci₂ ci₁ h2r h1r hgt with hneq | hdisj
        · exact Or.inl hneq.symm
        · exact Or.inr hdisj.symm
    rw [← hpair1, ← hpair2] at hrel
    rcases hrel with hlvl_ne | hXdisj
    · exact hlvl_ne (hb1lvl.symm.trans hb2lvl)
    · exact Finset.disjoint_left.mp hXdisj hb1X hb2X
  have hcomp_disj_j0 : ∀ ci (hci : ci < wd.comps.length),
      Disjoint (wd.comps[ci]'hci).jSubOrigEdges.toFinset wd.j0Edges.toFinset := by
    intro ci hci
    rw [Finset.disjoint_left]
    intro jOrig hj1 hj0
    rw [List.mem_toFinset] at hj1 hj0
    obtain ⟨b₁, _, hb1nl, hb1lvl, _, _⟩ := hjSub_mem_preimage ci hci jOrig hj1
    obtain ⟨b₂, hb2m, hb2lvl, hb2nl⟩ :
        ∃ b₂ < wd.J0_strip.m, wd.decomp.level b₂ = 0 ∧ wd.nlIdx.getD b₂ 0 = jOrig := by
      change jOrig ∈ (wd.decomp.edgesAt wd.J0_strip 0).map (fun k => wd.nlIdx.getD k 0) at hj0
      simp only [DecomposeOutput.edgesAt, List.mem_map, List.mem_filter, List.mem_range,
        decide_eq_true_eq] at hj0
      rcases hj0 with ⟨b₂, ⟨hb2m, hb2lvl⟩, rfl⟩
      exact ⟨b₂, hb2m, hb2lvl, rfl⟩
    rw [List.getD_eq_getElem _ _ (by omega)] at hb2nl
    have hb_eq : b₁ = b₂ := (hnl_nodup.getElem_inj_iff).mp (hb1nl.trans hb2nl.symm)
    subst hb_eq
    have hpos := (hcomp_props ci hci).1
    omega
  exact
    { W_n := rfl
      W_valid := hW_valid
      W_m_eq := hWm_eq
      aligned := haligned
      φ_dec_pos := hφ_dec_pos
      φ_dec_le := hφ_dec_le
      φ_Const_pos := hφ_Const_pos
      φ_Const_le := hφ_Const_le
      c_deg_ge := hc_deg_ge
      φ_ds_pos := hφ_ds_pos
      φ_ds_le_dec := hφ_ds_le_dec
      φ_ds_le_Const := hφ_ds_le_Const
      φ_ds_half := hφ_ds_half
      γ_ExpPath_ge := hγ_ExpPath_ge
      γ_del_ge := hγ_del_ge
      τ₁_nonneg := hτ₁_nonneg
      τ₂_pos := hτ₂_pos
      j0_nodup := hj0_nodup
      j0_lt := hj0_lt
      comp_props := hcomp_props
      comp_disjoint := hcomp_disj
      comp_disjoint_j0 := hcomp_disj_j0 }


end MinCostFlow.Spanner
