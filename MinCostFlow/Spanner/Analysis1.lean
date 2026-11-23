module

public import MinCostFlow.Statement.Cited.Graphs
public import MinCostFlow.Spanner.Embedding
public import MinCostFlow.Spanner.Tools
public import MinCostFlow.Spanner.Subgraph
public import MinCostFlow.Spanner.Algorithm
public import MinCostFlow.Spanner.WitnessProps
public import MinCostFlow.Spanner.WitnessBounds
public import MinCostFlow.Spanner.WitnessLift
public import MinCostFlow.Spanner.Task2Base

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Pow

/-!
# Task 2 Analysis: Invariant 1, Claim 8.7, and Corollary 8.8

This file finishes Task 2 of Algorithm 4 (`Sparsify`, `spanner.tex`, lines 84–103, pages 42–44):
- **`invariant_1`** (**Invariant 1**, page 43).
- **`claim_8_7`** (**Claim 8.7**, pages 43–44).
- **`corollary_8_8`** (**Corollary 8.8**, page 44) and `task2_stats`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open MinCostFlow.Cited

private lemma task2Init_embWJ_lt {DSState : Type} {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    {eW : ℕ} (heW : eW < (buildWitness tools H' J embJH).j0Edges.length) :
    let wd := buildWitness tools H' J embJH
    let j0 := wd.j0Edges[eW]'heW
    (task2Init J wd (DSState := DSState)).embWJ eW =
      some (Walk.single (J.edges.getD j0 (0, 0)).1 (J.edges.getD j0 (0, 0)).2 j0) := by
  intro wd j0
  obtain ⟨heW_m, _, hsrc, _⟩ := W_edges_getD_j0 tools H' J embJH heW
  have heW_m' : eW < wd.W.m := heW_m
  simp only [task2Init, heW_m', ↓reduceIte]
  rw [hsrc, List.getD_eq_getElem _ _ heW]

private lemma task2Init_embWJ_ge {DSState : Type} {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    {eW : ℕ} (heW_m : eW < (buildWitness tools H' J embJH).W.m)
    (hge : (buildWitness tools H' J embJH).j0Edges.length ≤ eW) :
    let wd := buildWitness tools H' J embJH
    (task2Init J wd (DSState := DSState)).embWJ eW = none := by
  intro wd
  rcases W_edge_cases tools H' J embJH heW_m with hlt0 | ⟨ci, hci, eL, heL, rfl⟩
  · exact absurd hlt0 (Nat.not_lt_of_ge hge)
  · have hsrc := (W_edges_getD_comp tools H' J embJH hci heL).2.2.2.1
    dsimp only [task2Init, wd]
    split_ifs
    rw [hsrc]

theorem task2Init_inv {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid) (hembJH : IsEmbedding J H' embJH)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH)) :
    let wd := buildWitness tools H' J embJH
    let s0 : Task2State tools.pathDS.State := task2Init J wd
    IsPartialEmbedding wd.W J s0.embWJ ∧
    (∀ eW < wd.j0Edges.length, (s0.embWJ eW).isSome = true) ∧
    (∀ eW < wd.W.m, ((partialToWalk s0.embWJ eW).edges.length : ℝ) ≤ wd.γ_ExpPath) ∧
    vcong wd.W H' wd.wW (compose J embJH (partialToWalk s0.embWJ)) ≤ (1 / 2 : ℝ) * wd.τ₁ := by
  intro wd s0
  have hj0_le_m : wd.j0Edges.length ≤ wd.W.m := by
    by_cases h0 : wd.j0Edges.length = 0
    · omega
    · have hlt : wd.j0Edges.length - 1 < wd.j0Edges.length := by omega
      have hWm : wd.j0Edges.length - 1 < wd.W.m := (W_edges_getD_j0 tools H' J embJH hlt).1
      omega
  have hj0_nl : ∀ j0 ∈ wd.j0Edges, j0 ∈ wd.nlIdx := by
    intro j0 hj0
    change j0 ∈ (wd.decomp.edgesAt wd.J0_strip 0).map (fun e => wd.nlIdx.getD e 0) at hj0
    rw [List.mem_map] at hj0
    rcases hj0 with ⟨a, ha, rfl⟩
    have ha_m : a < wd.nlIdx.length := by
      simp only [DecomposeOutput.edgesAt, List.mem_filter, List.mem_range] at ha
      simpa [wd, buildWitness, stripLoops, Graph.m] using ha.1
    rw [List.getD_eq_getElem _ _ ha_m]
    exact List.getElem_mem ha_m
  have hj0_edges : ∀ eW (heW : eW < wd.j0Edges.length),
      let j0 := wd.j0Edges[eW]'heW
      j0 < J.m ∧
      (J.edges.getD j0 (0, 0)).1 ≠ (J.edges.getD j0 (0, 0)).2 ∧
      wd.W.edges.getD eW (0, 0) = J.edges.getD j0 (0, 0) := by
    intro eW heW j0
    have hnl := mem_nonloopIndices.mp (hj0_nl j0 (List.getElem_mem heW))
    have hW_eq := (W_edges_getD_j0 tools H' J embJH heW).2.1
    rw [List.getD_eq_getElem wd.j0Edges 0 heW] at hW_eq
    exact ⟨hnl.1, hnl.2, hW_eq⟩
  have hγ_ge_2 : 2 ≤ wd.γ_ExpPath := by
    have h2 : (2 : ℝ) ≤ 1 / wd.φ_ds := by
      rw [le_div_iff₀ hw.φ_ds_pos]
      nlinarith [hw.φ_ds_half]
    exact le_trans h2 hw.γ_ExpPath_ge
  have hpart : IsPartialEmbedding wd.W J s0.embWJ := by
    refine ⟨le_rfl, fun eW hm P hP => ?_⟩
    by_cases heW : eW < wd.j0Edges.length
    · rw [task2Init_embWJ_lt tools H' J embJH heW] at hP
      simp only [Option.some.injEq] at hP
      subst hP
      obtain ⟨hj0_m, _, hW_eq⟩ := hj0_edges eW heW
      let j0 := wd.j0Edges[eW]'heW
      have hj0_len : j0 < J.edges.length := hj0_m
      have hv := hJ _ (List.getElem_mem hj0_len)
      rw [← List.getD_eq_getElem _ _ hj0_len] at hv
      have hW_len : eW < wd.W.edges.length := hm
      rw [List.getD_eq_getElem _ _ hW_len] at hW_eq
      change Walk.IsWalk J (wd.W.edges[eW]'hW_len).1 (wd.W.edges[eW]'hW_len).2
        (Walk.single (J.edges.getD j0 (0, 0)).1 (J.edges.getD j0 (0, 0)).2 j0)
      rw [hW_eq]
      exact Walk.isWalk_single hv.1 hv.2 hj0_m (Or.inl ⟨rfl, rfl⟩)
    · rw [task2Init_embWJ_ge tools H' J embJH hm (Nat.le_of_not_lt heW)] at hP
      simp at hP
  have hj0 : ∀ eW < wd.j0Edges.length, (s0.embWJ eW).isSome = true := by
    intro eW heW
    rw [task2Init_embWJ_lt tools H' J embJH heW]
    rfl
  have helen : ∀ eW < wd.W.m, ((partialToWalk s0.embWJ eW).edges.length : ℝ) ≤ wd.γ_ExpPath := by
    intro eW heW
    by_cases h0 : eW < wd.j0Edges.length
    · rw [partialToWalk, task2Init_embWJ_lt tools H' J embJH h0, Option.getD_some,
          Walk.single, List.length_singleton, Nat.cast_one]
      linarith
    · rw [partialToWalk, task2Init_embWJ_ge tools H' J embJH heW (Nat.le_of_not_lt h0),
          Option.getD_none, Walk.empty, List.length_nil, Nat.cast_zero]
      linarith
  have hvcong : vcong wd.W H' wd.wW (compose J embJH (partialToWalk s0.embWJ)) ≤ (1 / 2 : ℝ) * wd.τ₁ := by
    rw [vcong_le_iff]
    refine ⟨by have := hw.τ₁_nonneg; positivity, ?_⟩
    intro x hx
    unfold vcongAt
    rw [Finset.sum_filter]
    have hsum_split :
        (∑ eW ∈ Finset.range wd.W.m,
          if x ∈ (compose J embJH (partialToWalk s0.embWJ) eW).verts then wd.wW eW else 0) =
        ∑ eW ∈ Finset.range wd.j0Edges.length,
          if x ∈ (embJH (wd.j0Edges.getD eW 0)).verts then wd.φ_dec else 0 := by
      rw [← Finset.sum_range_add_sum_Ico _ hj0_le_m]
      have hhi : (∑ eW ∈ Finset.Ico wd.j0Edges.length wd.W.m,
          if x ∈ (compose J embJH (partialToWalk s0.embWJ) eW).verts then wd.wW eW else 0) = 0 := by
        refine Finset.sum_eq_zero fun eW heW => ?_
        have hge : wd.j0Edges.length ≤ eW := (Finset.mem_Ico.mp heW).1
        have heWm : eW < wd.W.m := (Finset.mem_Ico.mp heW).2
        have hs0 : s0.embWJ eW = none := task2Init_embWJ_ge tools H' J embJH heWm hge
        have hcomp : compose J embJH (partialToWalk s0.embWJ) eW = Walk.empty := by
          simp [compose, partialToWalk, hs0, composeAux, Walk.empty]
        simp [hcomp, Walk.empty]
      rw [hhi, add_zero]
      refine Finset.sum_congr rfl fun eW heW => ?_
      have heW' : eW < wd.j0Edges.length := Finset.mem_range.mp heW
      have hs0 := task2Init_embWJ_lt (DSState := tools.pathDS.State) tools H' J embJH heW'
      obtain ⟨hj0_m, hne_loop, _⟩ := hj0_edges eW heW'
      have he_ne : (embJH (wd.j0Edges[eW]'heW')).edges ≠ [] := by
        intro hempty
        have hw0 := hembJH.2 (wd.j0Edges[eW]'heW') hj0_m
        rcases hw0.2.2 with ⟨_, _, huv⟩ | ⟨hne, _⟩
        · rw [List.getD_eq_getElem _ _ (by simpa [Graph.m] using hj0_m)] at hne_loop
          exact hne_loop huv
        · exact hne hempty
      have hcomp : compose J embJH (partialToWalk s0.embWJ) eW = embJH (wd.j0Edges[eW]'heW') := by
        simp only [compose, partialToWalk]
        rw [hs0]
        simp only [Option.getD_some, Walk.single, composeAux, Walk.append, Walk.empty]
        dsimp only [wd] at he_ne ⊢
        simp [he_ne]
      have hwφ : wd.wW eW = wd.φ_dec := (W_edges_getD_j0 tools H' J embJH heW').2.2.2
      rw [hcomp, hwφ, List.getD_eq_getElem _ _ heW']
    rw [hsum_split]
    by_cases hj0_empty : wd.j0Edges.length = 0
    · simp only [hj0_empty, Finset.range_zero, Finset.sum_empty]
      have := hw.τ₁_nonneg
      positivity
    · have h0_lt : 0 < wd.j0Edges.length := Nat.pos_of_ne_zero hj0_empty
      obtain ⟨hj0_m, hne_loop, _⟩ := hj0_edges 0 h0_lt
      have hlen_JH : 1 ≤ length J embJH := by
        have hw0 := hembJH.2 (wd.j0Edges[0]'h0_lt) hj0_m
        have hne_edges : (embJH (wd.j0Edges[0]'h0_lt)).edges ≠ [] := by
          intro hempty
          rcases hw0.2.2 with ⟨_, _, huv⟩ | ⟨hne, _⟩
          · rw [List.getD_eq_getElem _ _ (by simpa [Graph.m] using hj0_m)] at hne_loop
            exact hne_loop huv
          · exact hne hempty
        exact le_trans (List.length_pos_iff_ne_nil.mpr hne_edges) (edges_length_le_length embJH hj0_m)
      have hj0_nodup : wd.j0Edges.Nodup := by
        have hnl : wd.nlIdx.Nodup := by
          simp only [wd, buildWitness, nonloopIndices]
          exact List.nodup_range.filter _
        have hed : (wd.decomp.edgesAt wd.J0_strip 0).Nodup := by
          simp only [DecomposeOutput.edgesAt]
          exact List.nodup_range.filter _
        have h0 : wd.j0Edges = (wd.decomp.edgesAt wd.J0_strip 0).map (fun e => wd.nlIdx.getD e 0) := rfl
        rw [h0]
        exact List.Nodup.map_on (fun a ha b hb hab => by
          have ha_m : a < wd.nlIdx.length := by
            simp only [DecomposeOutput.edgesAt, List.mem_filter, List.mem_range] at ha
            simpa [wd, buildWitness, stripLoops, Graph.m] using ha.1
          have hb_m : b < wd.nlIdx.length := by
            simp only [DecomposeOutput.edgesAt, List.mem_filter, List.mem_range] at hb
            simpa [wd, buildWitness, stripLoops, Graph.m] using hb.1
          rw [List.getD_eq_getElem _ _ ha_m, List.getD_eq_getElem _ _ hb_m] at hab
          exact (List.Nodup.getElem_inj_iff hnl).mp hab) hed
      have hinj : ∑ eW ∈ Finset.range wd.j0Edges.length,
          (if x ∈ (embJH (wd.j0Edges.getD eW 0)).verts then wd.φ_dec else 0) ≤
          ∑ eJ ∈ Finset.range J.m,
          (if x ∈ (embJH eJ).verts then (1 : ℝ) else 0) := by
        have hφ_le_1 : ∑ eW ∈ Finset.range wd.j0Edges.length,
            (if x ∈ (embJH (wd.j0Edges.getD eW 0)).verts then wd.φ_dec else 0) ≤
            ∑ eW ∈ Finset.range wd.j0Edges.length,
            (if x ∈ (embJH (wd.j0Edges.getD eW 0)).verts then (1 : ℝ) else 0) := by
          refine Finset.sum_le_sum fun eW _ => ?_
          split_ifs
          · exact hw.φ_dec_le
          · exact le_rfl
        have himg : ∑ eW ∈ Finset.range wd.j0Edges.length,
            (if x ∈ (embJH (wd.j0Edges.getD eW 0)).verts then (1 : ℝ) else 0) =
            ∑ eJ ∈ (Finset.range wd.j0Edges.length).image (fun eW => wd.j0Edges.getD eW 0),
            (if x ∈ (embJH eJ).verts then (1 : ℝ) else 0) := by
          symm
          refine Finset.sum_image fun a ha b hb hab => ?_
          have ha' : a < wd.j0Edges.length := Finset.mem_range.mp ha
          have hb' : b < wd.j0Edges.length := Finset.mem_range.mp hb
          rw [List.getD_eq_getElem _ _ ha', List.getD_eq_getElem _ _ hb'] at hab
          exact (List.Nodup.getElem_inj_iff hj0_nodup).mp hab
        have hsub : (Finset.range wd.j0Edges.length).image (fun eW => wd.j0Edges.getD eW 0) ⊆
            Finset.range J.m := by
          intro eJ heJ
          rcases Finset.mem_image.mp heJ with ⟨eW, heW, rfl⟩
          have heW' : eW < wd.j0Edges.length := Finset.mem_range.mp heW
          rw [List.getD_eq_getElem _ _ heW', Finset.mem_range]
          exact (hj0_edges eW heW').1
        have hle_img : ∑ eJ ∈ (Finset.range wd.j0Edges.length).image (fun eW => wd.j0Edges.getD eW 0),
            (if x ∈ (embJH eJ).verts then (1 : ℝ) else 0) ≤
            ∑ eJ ∈ Finset.range J.m, (if x ∈ (embJH eJ).verts then (1 : ℝ) else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by split_ifs <;> norm_num
        exact le_trans hφ_le_1 (by rw [himg]; exact hle_img)
      have hvcong_J : (∑ eJ ∈ Finset.range J.m,
          if x ∈ (embJH eJ).verts then (1 : ℝ) else 0) ≤
          vcong J H' (fun _ => 1) embJH := by
        rw [← Finset.sum_filter]
        exact vcongAt_le_vcong (fun _ => 1) embJH hx
      have hτ₁_half : (1 / 2 : ℝ) * wd.τ₁ =
          wd.γ_ExpPath * (length J embJH : ℝ) * wd.γ_del *
            (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) / wd.φ_ds := by
        change (1 / 2 : ℝ) * (2 * wd.γ_ExpPath * (length J embJH : ℝ) * wd.γ_del *
          (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) / wd.φ_ds) = _
        ring
      have hmul_le : vcong J H' (fun _ => 1) embJH ≤ (1 / 2 : ℝ) * wd.τ₁ := by
        rw [hτ₁_half]
        have hlen_r : (1 : ℝ) ≤ (length J embJH : ℝ) := by exact_mod_cast hlen_JH
        have hγdel_ge : 1 ≤ wd.γ_del := hw.γ_del_ge
        have hφ_pos : 0 < wd.φ_ds := hw.φ_ds_pos
        have hφ_inv : 2 ≤ 1 / wd.φ_ds := by rw [le_div_iff₀ hφ_pos]; nlinarith [hw.φ_ds_half]
        have hv_nn : 0 ≤ vcong J H' (fun _ => 1) embJH := vcong_nonneg J H' (fun _ => 1) embJH
        have hprod12 : 2 ≤ wd.γ_ExpPath * (length J embJH : ℝ) := by nlinarith
        have hprod : 1 ≤ wd.γ_ExpPath * (length J embJH : ℝ) * wd.γ_del / wd.φ_ds := by
          have h1 : 1 ≤ wd.γ_ExpPath * (length J embJH : ℝ) * wd.γ_del := by nlinarith
          have hnn : 0 ≤ wd.γ_ExpPath * (length J embJH : ℝ) * wd.γ_del := by linarith
          calc (1 : ℝ) ≤ 1 * 2 := by norm_num
            _ ≤ (wd.γ_ExpPath * (length J embJH : ℝ) * wd.γ_del) * (1 / wd.φ_ds) :=
              mul_le_mul h1 hφ_inv (by positivity) hnn
            _ = _ := by ring
        have hsum_nn : 0 ≤ vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ) :=
          add_nonneg hv_nn (Nat.cast_nonneg _)
        have h1 : vcong J H' (fun _ => 1) embJH ≤
            vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ) :=
          le_add_of_nonneg_right (Nat.cast_nonneg _)
        have h2 : vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ) ≤
            (wd.γ_ExpPath * (length J embJH : ℝ) * wd.γ_del / wd.φ_ds) *
              (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) :=
          le_mul_of_one_le_left hsum_nn hprod
        have h3 : (wd.γ_ExpPath * (length J embJH : ℝ) * wd.γ_del / wd.φ_ds) *
              (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) =
            wd.γ_ExpPath * (length J embJH : ℝ) * wd.γ_del *
              (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) / wd.φ_ds :=
          div_mul_eq_mul_div _ _ _
        exact le_trans h1 (le_trans h2 (le_of_eq h3))
      exact le_trans hinj (le_trans hvcong_J hmul_le)
  exact ⟨hpart, hj0, helen, hvcong⟩

/-- Entry invariant needed to start a new Task 2 round `task2Round`. -/
structure Task2RoundEntryInv (DSState : Type) (H' J : Graph) (embJH : ℕ → Walk)
    (wd : WitnessData) (s : Task2State DSState) : Prop where
  partial_emb : IsPartialEmbedding wd.W J s.embWJ
  j0_embedded : ∀ eW < wd.j0Edges.length, (s.embWJ eW).isSome = true
  emb_len : ∀ eW < wd.W.m, ((partialToWalk s.embWJ eW).edges.length : ℝ) ≤ wd.γ_ExpPath
  vcong_half : ∀ x < H'.n,
    vcongAt wd.W wd.wW (compose J embJH (partialToWalk s.embWJ)) x ≤ (s.η₁ + 1 / 2 : ℝ) * wd.τ₁
  initCount_eq : s.initCountJ = s.η₁ * wd.comps.length
  initEdges_eq : s.initEdgesJ = s.η₁ * (wd.comps.map fun c => c.J_sub.m).sum
  middle_eq : s.middleIters1 = s.getPathCountJ
  unemb_eq : s.getPathCountJ + unembeddedCount1 wd s = wd.W.m - wd.j0Edges.length
  vcongUpdates_le : (s.vcongUpdates : ℝ) ≤
    (s.getPathCountJ : ℝ) * (wd.γ_ExpPath * ((length J embJH : ℝ) + 1))

theorem Task2LoopInv.toEntryInv {pathDS : PathDSTool} {H' J : Graph} {embJH : ℕ → Walk}
    {wd : WitnessData} {s : Task2State pathDS.State}
    (h : Task2LoopInv pathDS H' J embJH wd s) :
    Task2RoundEntryInv pathDS.State H' J embJH wd s :=
  ⟨h.partial_emb, h.j0_embedded, h.emb_len, h.vcong_half, h.initCount_eq, h.initEdges_eq,
   h.middle_eq, h.unemb_eq, h.vcongUpdates_le⟩

theorem task2Init_entryInv {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid) (hembJH : IsEmbedding J H' embJH)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH)) :
    let wd := buildWitness tools H' J embJH
    Task2RoundEntryInv tools.pathDS.State H' J embJH wd (task2Init J wd) := by
  intro wd
  obtain ⟨hpart, hj0, helen, hvcong⟩ := task2Init_inv tools H' J embJH hJ hembJH hw
  have hunemb_init : unembeddedCount1 wd (task2Init J wd (DSState := tools.pathDS.State)) =
      wd.W.m - wd.j0Edges.length := by
    unfold unembeddedCount1 unembeddedSet1
    have hset : (Finset.range wd.W.m).filter
          (fun eW => ((task2Init J wd (DSState := tools.pathDS.State)).embWJ eW).isNone) =
        Finset.Ico wd.j0Edges.length wd.W.m := by
      ext eW
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, Option.isNone_iff_eq_none]
      constructor
      · rintro ⟨hm, hnone⟩
        refine ⟨?_, hm⟩
        by_contra hlt
        have hs := hj0 eW (Nat.lt_of_not_ge hlt)
        rw [hnone] at hs; simp at hs
      · rintro ⟨hle, hm⟩
        exact ⟨hm, task2Init_embWJ_ge tools H' J embJH hm hle⟩
    rw [hset, Nat.card_Ico]
  refine
    { partial_emb := hpart
      j0_embedded := hj0
      emb_len := helen
      vcong_half := fun x hx => by
        simpa [task2Init] using (vcong_le_iff.mp hvcong).2 x hx
      initCount_eq := by simp [task2Init]
      initEdges_eq := by simp [task2Init]
      middle_eq := rfl
      unemb_eq := by simpa [task2Init] using hunemb_init
      vcongUpdates_le := by simp [task2Init] }

/-- **Invariant 1** (`spanner.tex`, page 43):
Executing one round `task2Round` preserves `Task2LoopInv` (in particular,
`vcong(Π_{J → H'} ∘ Π_{W → J}) ≤ (η₁ + 1/2) · τ₁` at all times during and after the round),
terminates its middle loop with `task2MiddleCond = false`, and satisfies `Task2RoundRel`. -/
theorem invariant_1 {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid) (hembJH : IsEmbedding J H' embJH)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    {s : Task2State tools.pathDS.State}
    (hs : Task2RoundEntryInv tools.pathDS.State H' J embJH (buildWitness tools H' J embJH) s) :
    let wd := buildWitness tools H' J embJH
    let s' := task2Round tools.pathDS H' J embJH wd s
    s'.η₁ = s.η₁ + 1 ∧
    Task2LoopInv tools.pathDS H' J embJH wd s' ∧
    Task2RoundRel tools.pathDS wd
      { s with η₁ := s.η₁ + 1, processedVerts := ∅, dsJ := wd.comps.map fun c =>
          tools.pathDS.init wd.φ_dec wd.J0_strip.m c.J_sub } s' ∧
    task2MiddleCond tools.pathDS wd s' = false ∧
    vcong wd.W H' wd.wW (compose J embJH (partialToWalk s'.embWJ)) ≤ (s'.η₁ + 1 / 2 : ℝ) * wd.τ₁ := by
  intro wd s'
  let dsInit := wd.comps.map fun c => tools.pathDS.init wd.φ_dec wd.J0_strip.m c.J_sub
  let s1 : Task2State tools.pathDS.State :=
    { s with
      η₁ := s.η₁ + 1
      dsJ := dsInit
      processedVerts := ∅
      initCountJ := s.initCountJ + wd.comps.length
      initEdgesJ := s.initEdgesJ + (wd.comps.map fun c => c.J_sub.m).sum }
  have hds_len : s1.dsJ.length = wd.comps.length := by simp [s1, dsInit]
  have hinit_spec : ∀ ci (hci : ci < wd.comps.length),
      let c := wd.comps[ci]'hci
      let ds := s1.dsJ[ci]'(by rw [hds_len]; exact hci)
      tools.pathDS.Inv wd.φ_dec wd.J0_strip.m c.J_sub ds ∧
      tools.pathDS.Vhat ds = ∅ ∧
      tools.pathDS.deleted ds = ∅ := by
    intro ci hci c ds
    rcases hw.comp_props ci hci with
      ⟨_, _, _, _, _, hc_Jn, hc_Jvalid, hc_Jm_pos, hc_Jm_le, hc_Jdeg, hc_Jexp, _⟩
    have hds_eq : ds = tools.pathDS.init wd.φ_dec wd.J0_strip.m c.J_sub := by
      simp [ds, s1, dsInit, c]
    rw [hds_eq]
    exact
      ⟨tools.pathDS.init_inv wd.φ_dec wd.J0_strip.m c.J_sub hw.φ_dec_pos hw.φ_dec_le
        hc_Jvalid hc_Jm_pos hc_Jm_le (fun v hv => hc_Jdeg v (hc_Jn ▸ hv)) hc_Jexp,
       tools.pathDS.init_Vhat wd.φ_dec wd.J0_strip.m c.J_sub hw.φ_dec_pos hw.φ_dec_le
        hc_Jvalid hc_Jm_pos hc_Jm_le (fun v hv => hc_Jdeg v (hc_Jn ▸ hv)) hc_Jexp,
       tools.pathDS.init_deleted wd.φ_dec wd.J0_strip.m c.J_sub hw.φ_dec_pos hw.φ_dec_le
        hc_Jvalid hc_Jm_pos hc_Jm_le (fun v hv => hc_Jdeg v (hc_Jn ▸ hv)) hc_Jexp⟩
  have hloop1 : Task2LoopInv tools.pathDS H' J embJH wd s1 :=
    { ds_len := hds_len
      ds_inv := fun ci hci => (hinit_spec ci hci).1
      Vhat_sub := fun ci hci => by rw [(hinit_spec ci hci).2.1]; exact Finset.empty_subset _
      Vhat_vol := fun ci hci => by
        rw [(hinit_spec ci hci).2.1, (hinit_spec ci hci).2.2]
        simp only [Graph.vol, Graph.volIn, Finset.sum_empty, Nat.cast_zero, Finset.card_empty,
          mul_zero, zero_div, le_refl]
      partial_emb := hs.partial_emb
      j0_embedded := hs.j0_embedded
      emb_len := hs.emb_len
      vcong_half := fun x hx => by
        have hhalf : (s.η₁ + 1 / 2 : ℝ) * wd.τ₁ ≤ (s1.η₁ + 1 / 2 : ℝ) * wd.τ₁ := by
          have := hw.τ₁_nonneg
          dsimp only [s1]
          push_cast
          linarith
        exact le_trans (hs.vcong_half x hx) hhalf
      processed_sub := fun x hx => by simp [s1] at hx
      processed_deleted := fun x hx => by simp [s1] at hx
      deleted_sub_processed := fun ci hci b hb => by
        rw [(hinit_spec ci hci).2.2] at hb
        simp at hb
      initCount_eq := by
        dsimp only [s1]; rw [hs.initCount_eq]; ring
      initEdges_eq := by
        dsimp only [s1]; rw [hs.initEdges_eq]; ring
      middle_eq := hs.middle_eq
      unemb_eq := hs.unemb_eq
      vcongUpdates_le := hs.vcongUpdates_le
      inactive_uncongested := fun x hx _ => by
        have hstep : (s.η₁ + 1 / 2 : ℝ) * wd.τ₁ ≤ (s1.η₁ : ℝ) * wd.τ₁ := by
          have := hw.τ₁_nonneg
          dsimp only [s1]
          push_cast
          linarith
        exact le_trans (hs.vcong_half x hx) hstep }
  let s_base : Task2State tools.pathDS.State :=
    { s with η₁ := s.η₁ + 1, processedVerts := ∅, dsJ := dsInit }
  have hrel1 : Task2RoundRel tools.pathDS wd s_base s1 :=
    { emb_mono := fun _ _ => Or.inr rfl
      inner_eq := by simp [s1, s_base]
      del_eq := by
        have hzero : ∀ ci ∈ Finset.range wd.comps.length,
            (tools.pathDS.deleted (s1.dsJ.getD ci
              (tools.pathDS.init wd.φ_dec wd.J0_strip.m ⟨0, []⟩))).card = 0 := by
          intro ci hci_r
          have hci := Finset.mem_range.mp hci_r
          have hci_s : ci < s1.dsJ.length := by rw [hds_len]; exact hci
          rw [List.getD_eq_getElem _ _ hci_s, (hinit_spec ci hci).2.2, Finset.card_empty]
        rw [Finset.sum_eq_zero hzero]
        rfl }
  let P : Task2State tools.pathDS.State → Prop := fun st =>
    Task2LoopInv tools.pathDS H' J embJH wd st ∧
    Task2RoundRel tools.pathDS wd s_base st ∧
    st.η₁ = s1.η₁ ∧
    st.initCountJ = s1.initCountJ ∧
    st.initEdgesJ = s1.initEdgesJ
  have hstep : ∀ st, P st → task2MiddleCond tools.pathDS wd st = true →
      P (task2MiddleStep tools.pathDS H' J embJH wd st) ∧
        unembeddedCount1 wd (task2MiddleStep tools.pathDS H' J embJH wd st) <
          unembeddedCount1 wd st := by
    intro st ⟨hli, hri, hη, hic, hie⟩ hc
    obtain ⟨hli', hri', hlt⟩ := task2MiddleStep_inv tools H' J embJH hJ hembJH hw hli hri hc
    unfold task2MiddleCond at hc
    cases hf : findReadyWEdge tools.pathDS wd st with
    | none => rw [hf] at hc; simp at hc
    | some p =>
      rcases p with ⟨eW, ci, eLocal⟩
      let c := wd.comps.getD ci defaultCompInfo
      let ds := st.dsJ.getD ci (tools.pathDS.init wd.φ_dec wd.J0_strip.m ⟨0, []⟩)
      let eLoc := c.W_sub.edges.getD eLocal (0, 0)
      let P_sub := tools.pathDS.getPath ds eLoc.1 eLoc.2
      let P_J := liftJSubWalk c P_sub
      let updVerts := (P_J.edges.map fun e' => (embJH e').verts.length).sum
      let st1 : Task2State tools.pathDS.State :=
        { st with
          embWJ := Function.update st.embWJ eW (some P_J)
          getPathCountJ := st.getPathCountJ + 1
          vcongUpdates := st.vcongUpdates + updVerts
          middleIters1 := st.middleIters1 + 1 }
      have hmid_eq : task2MiddleStep tools.pathDS H' J embJH wd st =
          whileFuel H'.n (task2InnerCond H' J embJH wd)
            (task2InnerStep tools.pathDS H' J embJH wd) st1 := by
        simp [task2MiddleStep, hf, c, ds, eLoc, P_sub, P_J, updVerts, st1]
      have hη_in : (whileFuel H'.n (task2InnerCond H' J embJH wd)
          (task2InnerStep tools.pathDS H' J embJH wd) st1).η₁ = st1.η₁ :=
        whileFuel_inv (fun a => a.η₁ = st1.η₁) _ _ (fun a ha cnd => by
          unfold task2InnerCond at cnd
          cases hfc : findCongestedVertex H' J embJH wd a with
          | none => rw [hfc] at cnd; simp at cnd
          | some x => simpa [task2InnerStep, hfc] using ha) H'.n st1 rfl
      have hic_in : (whileFuel H'.n (task2InnerCond H' J embJH wd)
          (task2InnerStep tools.pathDS H' J embJH wd) st1).initCountJ = st1.initCountJ :=
        whileFuel_inv (fun a => a.initCountJ = st1.initCountJ) _ _ (fun a ha cnd => by
          unfold task2InnerCond at cnd
          cases hfc : findCongestedVertex H' J embJH wd a with
          | none => rw [hfc] at cnd; simp at cnd
          | some x => simpa [task2InnerStep, hfc] using ha) H'.n st1 rfl
      have hie_in : (whileFuel H'.n (task2InnerCond H' J embJH wd)
          (task2InnerStep tools.pathDS H' J embJH wd) st1).initEdgesJ = st1.initEdgesJ :=
        whileFuel_inv (fun a => a.initEdgesJ = st1.initEdgesJ) _ _ (fun a ha cnd => by
          unfold task2InnerCond at cnd
          cases hfc : findCongestedVertex H' J embJH wd a with
          | none => rw [hfc] at cnd; simp at cnd
          | some x => simpa [task2InnerStep, hfc] using ha) H'.n st1 rfl
      refine ⟨⟨hli', hri', ?_, ?_, ?_⟩, hlt⟩
      · rw [hmid_eq, hη_in]; exact hη
      · rw [hmid_eq, hic_in]; exact hic
      · rw [hmid_eq, hie_in]; exact hie
  have hs'_eq : s' = whileFuel wd.W.m (task2MiddleCond tools.pathDS wd)
      (task2MiddleStep tools.pathDS H' J embJH wd) s1 := rfl
  have hPs' : P s' :=
    whileFuel_inv P (task2MiddleCond tools.pathDS wd)
      (task2MiddleStep tools.pathDS H' J embJH wd) (fun st h c => (hstep st h c).1)
      wd.W.m s1 ⟨hloop1, hrel1, rfl, rfl, rfl⟩
  have hdone : task2MiddleCond tools.pathDS wd s' = false :=
    whileFuel_done P (unembeddedCount1 wd) (task2MiddleCond tools.pathDS wd)
      (task2MiddleStep tools.pathDS H' J embJH wd) hstep wd.W.m s1
      ⟨hloop1, hrel1, rfl, rfl, rfl⟩
      (by unfold unembeddedCount1 unembeddedSet1; exact le_trans (Finset.card_filter_le _ _) (by simp))
  have hvcong : vcong wd.W H' wd.wW (compose J embJH (partialToWalk s'.embWJ)) ≤
      (s'.η₁ + 1 / 2 : ℝ) * wd.τ₁ := by
    rw [vcong_le_iff]
    refine ⟨?_, fun x hx => hPs'.1.vcong_half x hx⟩
    have := hw.τ₁_nonneg
    positivity
  exact ⟨hPs'.2.2.1, hPs'.1, hPs'.2.1, hdone, hvcong⟩

end MinCostFlow.Spanner

