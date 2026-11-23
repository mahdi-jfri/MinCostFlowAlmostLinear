module

public import MinCostFlow.LSF.Tools
public import MinCostFlow.Statement.Cited.AbrahamNeiman
import MinCostFlow.LowStretch.ProgClusterSetupLs
import MinCostFlow.LSF.Theorem22Aux
import MinCostFlow.LSF.Model
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Theorem 2.2: Static Low-Stretch Spanning Trees from `[AN19]`

This file derives `MinCostFlow.LSF.HasLSSTSpec` (**Theorem 2.2**, page 7 of the paper) from the
cited theorem `MinCostFlow.Cited.LowStretchSpanningTree` (`[AN19, Theorem 1]`, SIAM J. Comput.
48(2), 2019, page 228).

Given a valid nonempty graph `G` with positive edge lengths `ℓ` and positive edge weights `v`:
1. Self-loops `E_loop = {e ∈ G.E | G.tail e = G.head e}` always have stretch `1 ≤ log²(G.n + 2)`
   in every spanning tree on `G.V`.
2. If non-loop edges `E_noloop` are empty, we attach all vertices of `G.V` to a root via fresh
   bridge edges outside `G.E`.
3. Otherwise we form the weighted copy multigraph `G_v = weightedCopyGraph G_nl v` (loopless, at
   most `2 |E_noloop|` edges), connect its active vertex components with fewer than `|E(G_v)|`
   cut-edge bridges, round scaled real lengths `ℓ(e') / δ` down to integers `≥ 4` with
   `δ = ℓ_min / (2 |V_act|)`, invoke `[AN19]` at dummy randomness `ω ≡ 0`, lift the resulting
   spanning tree `T_gv` back (verifying via `isForest_of_connected_card_le` and cut-parity that
   `T_gv`-paths of `G_v`-edges use no bridge edges), attach `G.V \ V_act`, and project onto `G_nl`
   via `projectTree_isLSST`.
-/

@[expose] public section

namespace MinCostFlow.LSF

open MinCostFlow

/-! ## Case 1: Only self-loops (`E_noloop = ∅`) -/

private lemma exists_lsst_when_no_nonloop {G : MGraph} (_hG : G.IsValid) (hV : G.V.Nonempty)
    {ℓ v : ℕ → ℝ} (hv : ∀ e ∈ G.E, 0 < v e)
    (hloop : ∀ e ∈ G.E, G.tail e = G.head e)
    {K₁ : ℝ} (hK₁ : 1 ≤ K₁) :
    ∃ T, IsLSST G ℓ v ((4 * K₁ + 5) * (Real.log ((G.n : ℝ) + 2)) ^ 2) T := by
  classical
  obtain ⟨r₀, hr₀⟩ := hV
  let T₀ : MGraph := { V := {r₀}, E := ∅, tail := fun _ => r₀, head := fun _ => r₀ }
  have hT₀_st : T₀.IsSpanningTreeOn {r₀} := by
    refine ⟨⟨fun _ hf => absurd hf (Finset.notMem_empty _), fun C hC => ?_⟩, rfl, fun u hu v hv => ?_⟩
    · rcases hC with ⟨hCne, _, _, hW⟩
      cases hW with
      | nil => exact absurd rfl hCne
      | cons hx _ _ => exact absurd hx (Finset.notMem_empty _)
    · rw [Finset.mem_singleton] at hu hv
      rw [hu, hv]
      exact connected_refl T₀ r₀
  let T := attachVerts T₀ r₀ G.V (copyMod G)
  have hT_st : T.IsSpanningTreeOn G.V :=
    attachVerts_isSpanningTreeOn hT₀_st (Finset.mem_singleton_self r₀)
      (Finset.singleton_subset_iff.mpr hr₀) (fun _ h => absurd h (Finset.notMem_empty _))
  have hT_nG : ∀ f ∈ T.E, f ∉ G.E := by
    intro f hf hfG
    dsimp only [T, attachVerts, T₀] at hf
    rw [Finset.empty_union, Finset.mem_image] at hf
    obtain ⟨w, _, rfl⟩ := hf
    exact Nat.not_lt_of_ge (Nat.le_add_right _ _) (lt_copyMod hfG)
  have hn1 : 1 ≤ G.n := Finset.card_pos.mpr ⟨r₀, hr₀⟩
  have hlog2 : 1 ≤ (Real.log ((G.n : ℝ) + 2)) ^ 2 := one_le_log_add_two_sq hn1
  refine ⟨T, hT_st, fun f hfT hfG => absurd hfG (hT_nG f hfT), ?_, ?_⟩
  · intro e he f hf
    rw [hloop e he, forestPath_self hT_st.1] at hf
    simp [walkEdges] at hf
  · have hsum : ∑ e ∈ G.E, v e * treeStretch G T ℓ e = G.norm1 v := by
      rw [norm1_eq_sum_pos hv]
      refine Finset.sum_congr rfl (fun e he => ?_)
      simp [treeStretch, hloop e he, forestPath_self hT_st.1, walkLength, walkEdges]
    rw [hsum]
    have hnorm0 : 0 ≤ G.norm1 v := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have hcoef : 1 ≤ (4 * K₁ + 5) * (Real.log ((G.n : ℝ) + 2)) ^ 2 := by
      nlinarith
    calc G.norm1 v = 1 * G.norm1 v := (one_mul _).symm
      _ ≤ ((4 * K₁ + 5) * (Real.log ((G.n : ℝ) + 2)) ^ 2) * G.norm1 v :=
          mul_le_mul_of_nonneg_right hcoef hnorm0

/-! ## Case 2: Reduction from `[AN19]` when non-loop edges exist -/

private lemma idxOf_inj_of_mem {xs : List ℕ} {x y : ℕ} (hx : x ∈ xs) (hy : y ∈ xs)
    (hEq : xs.idxOf x = xs.idxOf y) : x = y := by
  have hxlt : xs.idxOf x < xs.length := List.idxOf_lt_length_of_mem hx
  have hylt : xs.idxOf y < xs.length := List.idxOf_lt_length_of_mem hy
  calc x = xs[xs.idxOf x]'hxlt := (List.getElem_idxOf hxlt).symm
    _ = xs[xs.idxOf y]'hylt := by simp [hEq]
    _ = y := List.getElem_idxOf hylt

private lemma idxOf_getElem_of_nodup {xs : List ℕ} (hnd : xs.Nodup) {i : ℕ} (hi : i < xs.length) :
    xs.idxOf (xs[i]'hi) = i :=
  (List.Nodup.getElem_inj hnd).mp
    (List.getElem_idxOf (List.idxOf_lt_length_of_mem (List.getElem_mem hi)))

private lemma lsst_of_projectTree {G G_nl G_v T_raw : MGraph} {ℓ v : ℕ → ℝ} {K₁ : ℝ}
    (hG : G.IsValid) (hV : G.V.Nonempty) (hK₁ : 1 ≤ K₁)
    (hG_nl_eq : G_nl = { G with E := G.E.filter (fun e => G.tail e ≠ G.head e) })
    (hG_v_eq : G_v = weightedCopyGraph G_nl v)
    (hE_nl : G_nl.E.Nonempty)
    (hℓ : ∀ e ∈ G.E, 0 < ℓ e) (hv : ∀ e ∈ G.E, 0 < v e)
    (hT_raw_nonGv : ∀ f ∈ T_raw.E, f ∉ G_v.E → copyMod G ≤ f)
    (hlsst_raw : IsLSST G_v (weightedCopyLen G_nl ℓ) (fun _ => 1)
      ((2 * K₁ + 2) * (Real.log ((G.n : ℝ) + 2)) ^ 2) T_raw) :
    let T := projectTree G_nl v T_raw
    IsLSST G ℓ v ((4 * K₁ + 5) * (Real.log ((G.n : ℝ) + 2)) ^ 2) T := by
  classical
  subst hG_nl_eq hG_v_eq
  let G_nl : MGraph := { G with E := G.E.filter (fun e => G.tail e ≠ G.head e) }
  let G_v := weightedCopyGraph G_nl v
  have hG_nl_val : G_nl.IsValid := fun e he => hG e (Finset.mem_filter.mp he).1
  have hℓ_nl : ∀ e ∈ G_nl.E, 0 < ℓ e := fun e he => hℓ e (Finset.mem_filter.mp he).1
  have hv_nl : ∀ e ∈ G_nl.E, 0 < v e := fun e he => hv e (Finset.mem_filter.mp he).1
  have hG_v_card : (G_v.E.card : ℝ) ≤ 2 * (G_nl.E.card : ℝ) := weightedCopyGraph_card_le hv_nl
  have hn1 : 1 ≤ G.n := Finset.card_pos.mpr hV
  have hlog2 : 1 ≤ (Real.log ((G.n : ℝ) + 2)) ^ 2 := one_le_log_add_two_sq hn1
  have hproj := projectTree_isLSST hG_nl_val hℓ_nl hv_nl hlsst_raw
  let T := projectTree G_nl v T_raw
  have hT_st : T.IsSpanningTreeOn G.V := hproj.1
  have hT_edges : ∀ f' ∈ T.E, f' ∈ G.E → T.tail f' = G.tail f' ∧ T.head f' = G.head f' := by
    intro f' hf'T hf'G
    have hf'' := hf'T
    dsimp only [T] at hf''
    unfold projectTree at hf''
    rw [ite_eq_left hE_nl] at hf''
    obtain ⟨f, hf_raw, hfeq⟩ := Finset.mem_image.mp hf''
    have hf_gv : f ∈ G_v.E := by
      by_contra hnf
      have hproj_eq : projectEdge G_nl v f = f + copyMod G_nl := by
        unfold projectEdge; exact ite_eq_right hnf
      have hge : copyMod G ≤ f' :=
        (hT_raw_nonGv f hf_raw hnf).trans (by rw [← hfeq, hproj_eq]; exact Nat.le_add_right _ _)
      exact Nat.not_lt_of_ge hge (lt_copyMod hf'G)
    have hf'_nl : f' ∈ G_nl.E := by
      have hproj_eq : projectEdge G_nl v f = origEdge (copyMod G_nl) f := by
        unfold projectEdge; exact ite_eq_left hf_gv
      rw [← hfeq, hproj_eq]
      exact (weightedCopyGraph_origEdge_mem hE_nl hf_gv).1
    exact hproj.2.1 f' hf'T hf'_nl
  have hT_paths : ∀ e ∈ G.E, ∀ f ∈ walkEdges (T.forestPath (G.tail e) (G.head e)), f ∈ G.E := by
    intro e he f hf
    by_cases hne : G.tail e ≠ G.head e
    · exact (Finset.mem_filter.mp (hproj.2.2.1 e (Finset.mem_filter.mpr ⟨he, hne⟩) hf)).1
    · simp only [not_ne_iff] at hne
      rw [hne, forestPath_self hT_st.1] at hf
      simp [walkEdges] at hf
  have hsum_nl : ∑ e ∈ G_nl.E, v e * treeStretch G T ℓ e ≤
      (4 * K₁ + 4) * (Real.log ((G.n : ℝ) + 2)) ^ 2 * G.norm1 v := by
    have hst_match : ∀ e' ∈ G_v.E,
        treeStretch G T ℓ (origEdge (copyMod G_nl) e') =
          treeStretch G_v T (weightedCopyLen G_nl ℓ) e' := by
      intro e' he'
      have hm := weightedCopyGraph_origEdge_mem hE_nl he'
      let e := origEdge (copyMod G_nl) e'
      have hw_e : weightedCopyLen G_nl ℓ e' = ℓ e := rfl
      have hlen_eq : walkLength (weightedCopyLen G_nl ℓ) (T.forestPath (G.tail e) (G.head e)) =
          walkLength ℓ (T.forestPath (G.tail e) (G.head e)) := by
        unfold walkLength
        refine Finset.sum_congr rfl (fun f hf => ?_)
        have hf_nl : f ∈ G_nl.E := hproj.2.2.1 e hm.1 hf
        have hf_len : weightedCopyLen G_nl ℓ f = ℓ f := by
          unfold weightedCopyLen origEdge
          rw [Nat.mod_eq_of_lt (lt_copyMod hf_nl)]
        rw [hf_len]
      unfold treeStretch
      rw [hm.2.1, hm.2.2, hw_e, hlen_eq]
    have hcopy_sum : ∑ e ∈ G_nl.E, (edgeMult G_nl v e : ℝ) * treeStretch G T ℓ e =
        ∑ e' ∈ G_v.E, treeStretch G_v T (weightedCopyLen G_nl ℓ) e' := by
      rw [← weightedCopyGraph_sum_eq hE_nl v (treeStretch G T ℓ)]
      exact Finset.sum_congr rfl (fun e' he' => hst_match e' he')
    have hGv_bound : ∑ e' ∈ G_v.E, treeStretch G_v T (weightedCopyLen G_nl ℓ) e' ≤
        (4 * K₁ + 4) * (Real.log ((G.n : ℝ) + 2)) ^ 2 * (G_nl.E.card : ℝ) := by
      have h1 := hproj.2.2.2.2
      have h2 : (2 * K₁ + 2) * (Real.log ((G.n : ℝ) + 2)) ^ 2 * (G_v.E.card : ℝ) ≤
          (2 * K₁ + 2) * (Real.log ((G.n : ℝ) + 2)) ^ 2 * (2 * (G_nl.E.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hG_v_card (by positivity)
      linarith [h1, h2]
    have hnorm_nl_pos : 0 < G_nl.norm1 v := by
      rw [norm1_eq_sum_pos hv_nl]
      exact Finset.sum_pos hv_nl hE_nl
    have hm_nl_pos : (0 : ℝ) < (G_nl.E.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hE_nl)
    have hst_nn : ∀ e ∈ G_nl.E, 0 ≤ treeStretch G T ℓ e := fun e he => by
      unfold treeStretch
      have hwl0 : 0 ≤ walkLength ℓ (T.forestPath (G.tail e) (G.head e)) := by
        unfold walkLength
        refine Finset.sum_nonneg (fun f hf => ?_)
        have hf_nl := hproj.2.2.1 e he hf
        exact mul_nonneg (hℓ_nl f hf_nl).le (abs_nonneg _)
      exact add_nonneg zero_le_one (div_nonneg hwl0 (hℓ_nl e he).le)
    have hsum_scaled : ∑ e ∈ G_nl.E, v e * treeStretch G T ℓ e ≤
        (G_nl.norm1 v / (G_nl.E.card : ℝ)) *
          ∑ e ∈ G_nl.E, (edgeMult G_nl v e : ℝ) * treeStretch G T ℓ e := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun e he => ?_)
      have hceil : (G_nl.E.card : ℝ) * v e / G_nl.norm1 v ≤ (edgeMult G_nl v e : ℝ) := by
        unfold edgeMult; exact Nat.le_ceil _
      have hve : v e ≤ (G_nl.norm1 v / (G_nl.E.card : ℝ)) * (edgeMult G_nl v e : ℝ) := by
        have := mul_le_mul_of_nonneg_left hceil
          (div_nonneg hnorm_nl_pos.le hm_nl_pos.le)
        have heq : (G_nl.norm1 v / (G_nl.E.card : ℝ)) *
            ((G_nl.E.card : ℝ) * v e / G_nl.norm1 v) = v e := by
          field_simp [ne_of_gt hnorm_nl_pos, ne_of_gt hm_nl_pos]
        rwa [heq] at this
      calc v e * treeStretch G T ℓ e
          ≤ ((G_nl.norm1 v / (G_nl.E.card : ℝ)) * (edgeMult G_nl v e : ℝ)) *
              treeStretch G T ℓ e := mul_le_mul_of_nonneg_right hve (hst_nn e he)
        _ = (G_nl.norm1 v / (G_nl.E.card : ℝ)) *
              ((edgeMult G_nl v e : ℝ) * treeStretch G T ℓ e) := by ring
    have hnorm_nl_le : G_nl.norm1 v ≤ G.norm1 v :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => abs_nonneg _)
    calc ∑ e ∈ G_nl.E, v e * treeStretch G T ℓ e
        ≤ (G_nl.norm1 v / (G_nl.E.card : ℝ)) *
            ∑ e ∈ G_nl.E, (edgeMult G_nl v e : ℝ) * treeStretch G T ℓ e := hsum_scaled
      _ = (G_nl.norm1 v / (G_nl.E.card : ℝ)) *
            ∑ e' ∈ G_v.E, treeStretch G_v T (weightedCopyLen G_nl ℓ) e' := by rw [hcopy_sum]
      _ ≤ (G_nl.norm1 v / (G_nl.E.card : ℝ)) *
            ((4 * K₁ + 4) * (Real.log ((G.n : ℝ) + 2)) ^ 2 * (G_nl.E.card : ℝ)) :=
          mul_le_mul_of_nonneg_left hGv_bound (div_nonneg hnorm_nl_pos.le hm_nl_pos.le)
      _ = (4 * K₁ + 4) * (Real.log ((G.n : ℝ) + 2)) ^ 2 * G_nl.norm1 v := by
          field_simp [ne_of_gt hm_nl_pos]
      _ ≤ (4 * K₁ + 4) * (Real.log ((G.n : ℝ) + 2)) ^ 2 * G.norm1 v :=
          mul_le_mul_of_nonneg_left hnorm_nl_le (by positivity)
  let E_loop := G.E.filter (fun e => ¬ (G.tail e ≠ G.head e))
  have hsum_loop : ∑ e ∈ E_loop, v e * treeStretch G T ℓ e ≤
      (Real.log ((G.n : ℝ) + 2)) ^ 2 * G.norm1 v := by
    have hpt : ∀ e ∈ E_loop, v e * treeStretch G T ℓ e = v e := fun e he => by
      have htl := not_ne_iff.mp (Finset.mem_filter.mp he).2
      simp [treeStretch, htl, forestPath_self hT_st.1, walkLength, walkEdges]
    rw [Finset.sum_congr rfl hpt]
    have hle_norm : ∑ e ∈ E_loop, v e ≤ G.norm1 v := by
      rw [norm1_eq_sum_pos hv]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun e he _ => (hv e he).le)
    have hnorm0 : 0 ≤ G.norm1 v := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    calc ∑ e ∈ E_loop, v e ≤ G.norm1 v := hle_norm
      _ = 1 * G.norm1 v := (one_mul _).symm
      _ ≤ (Real.log ((G.n : ℝ) + 2)) ^ 2 * G.norm1 v :=
          mul_le_mul_of_nonneg_right hlog2 hnorm0
  have hsum_total : ∑ e ∈ G.E, v e * treeStretch G T ℓ e ≤
      (4 * K₁ + 5) * (Real.log ((G.n : ℝ) + 2)) ^ 2 * G.norm1 v := by
    have hpart := (Finset.sum_filter_add_sum_filter_not G.E (fun e => G.tail e ≠ G.head e)
      (fun e => v e * treeStretch G T ℓ e)).symm
    change ∑ e ∈ G.E, v e * treeStretch G T ℓ e =
        ∑ e ∈ G_nl.E, v e * treeStretch G T ℓ e +
        ∑ e ∈ E_loop, v e * treeStretch G T ℓ e at hpart
    linarith [hpart, hsum_nl, hsum_loop]
  exact ⟨hT_st, hT_edges, hT_paths, hsum_total⟩

private lemma an19_stretch_sum_bound
    {G_v T_gv T_raw : MGraph} {n_orig : ℕ} {len : ℕ → ℝ} {w_int : ℕ → ℕ}
    {δ K_AN K₁ : ℝ} {V_act : Finset ℕ} {V_list E_list B out : List ℕ}
    {edgeIdGv : ℕ → ℕ} {G_aug : Cited.WGraph}
    (hn1 : 1 ≤ n_orig) (hV_act_ge2 : 2 ≤ V_act.card) (hV_act_le_n : V_act.card ≤ n_orig)
    (hV_len : V_list.length = V_act.card)
    (hV_mem : ∀ x, x ∈ V_list ↔ x ∈ V_act)
    (hG_v_end : ∀ e' ∈ G_v.E, G_v.tail e' ∈ V_act ∧ G_v.head e' ∈ V_act)
    (hB_len_lt : B.length + 1 ≤ G_v.E.card)
    (hE_len : E_list.length = G_v.E.card) (hE_nd : E_list.Nodup)
    (hE_mem : ∀ e', e' ∈ E_list ↔ e' ∈ G_v.E)
    (hδ_pos : 0 < δ) (hw_int_ge : ∀ e' ∈ G_v.E, 4 ≤ w_int e')
    (hlen_pos : ∀ e' ∈ G_v.E, 0 < len e')
    (hlen_upper : ∀ f ∈ G_v.E, len f ≤ δ * ((w_int f : ℝ) + 1))
    (hlen_lower : ∀ e' ∈ G_v.E, δ * (w_int e' : ℝ) ≤ len e')
    (hδ_Vact : ∀ e' ∈ G_v.E, δ * (V_act.card : ℝ) ≤ len e' / 2)
    (hG_aug_n_len : G_aug.n = V_list.length)
    (hG_aug_m : G_aug.m = E_list.length + B.length)
    (hG_aug_edge_E : ∀ (j : ℕ) (hj : j < E_list.length),
      G_aug.edges[j]'(by rw [← Cited.WGraph.m, hG_aug_m]; omega) =
        (V_list.idxOf (G_v.tail (E_list[j]'hj)),
         V_list.idxOf (G_v.head (E_list[j]'hj)), w_int (E_list[j]'hj)))
    (hG_aug_edge_B : ∀ (k : ℕ) (hk : k < B.length),
      G_aug.edges[E_list.length + k]'(by rw [← Cited.WGraph.m, hG_aug_m]; omega) =
        (0, V_list.idxOf (B[k]'hk), 1))
    (hout_conn : ∀ u < G_aug.n, ∀ v < G_aug.n, ∃ es, G_aug.IsWalkIn out u v es)
    (htot_st : G_aug.totalStretch out ≤ K_AN * (G_aug.m : ℝ) * Cited.logLogFactor G_aug.n)
    (hK₁_ge1 : 1 ≤ K₁) (hKAN_le : K_AN ≤ K₁)
    (hedgeId_lt : ∀ j, j < E_list.length → edgeIdGv j ∈ G_v.E)
    (hedgeId_eq_E : ∀ (j : ℕ) (hj : j < E_list.length), edgeIdGv j = E_list[j]'hj)
    (hedgeId_nG_B : ∀ k ∈ out, ¬ k < E_list.length → edgeIdGv k ∉ G_v.E)
    (hT_gv_V : T_gv.V = V_act)
    (hT_gv_val : T_gv.IsValid) (hT_gv_st : T_gv.IsSpanningTreeOn V_act)
    (hT_gv_conn : ∀ u ∈ V_act, ∀ v ∈ V_act, T_gv.Connected u v)
    (hT_gv_lift : ∀ {a b : ℕ} {es : List ℕ}, G_aug.IsWalkIn out a b es →
      ∀ u ∈ V_act, ∀ v ∈ V_act, V_list.idxOf u = a → V_list.idxOf v = b →
      ∃ P : List (ℕ × Bool), T_gv.IsWalk u v P ∧ P.map Prod.fst = es.map edgeIdGv)
    (hT_gv_no_bridges : ∀ e' ∈ G_v.E,
      walkEdges (T_gv.forestPath (G_v.tail e') (G_v.head e')) ⊆ G_v.E)
    (hT_raw_path_eq : ∀ e' ∈ G_v.E,
      T_raw.forestPath (G_v.tail e') (G_v.head e') =
        T_gv.forestPath (G_v.tail e') (G_v.head e')) :
    ∑ e' ∈ G_v.E, treeStretch G_v T_raw len e' ≤
      (2 * K₁ + 2) * (Real.log ((n_orig : ℝ) + 2)) ^ 2 * G_v.norm1 (fun _ => 1) := by
  classical
  let m₁ := E_list.length
  have hIsWalkIn_mem : ∀ {a b : ℕ} {es : List ℕ},
      G_aug.IsWalkIn out a b es → ∀ j ∈ es, j ∈ out ∧ j < G_aug.m := by
    intro a b es hes
    induction hes with
    | nil _ => intro _ h; exact absurd h List.not_mem_nil
    | @cons _ _ _ k ks hk hkm _ _ ih =>
      intro j hj
      rw [List.mem_cons] at hj
      exact hj.elim (fun h => h ▸ ⟨hk, hkm⟩) (fun h => ih j h)
  let toAug : Fin m₁ → Fin G_aug.m :=
    fun i => ⟨i.1, Nat.lt_of_lt_of_le i.2 (by rw [hG_aug_m]; omega)⟩
  have htoAug_inj : Function.Injective toAug := fun a b h =>
    Fin.ext (by simpa [toAug] using congrArg Fin.val h)
  have hwalkLength_gv_le : ∀ (i : Fin m₁),
      treeStretch G_v T_raw len (E_list[i.1]'i.2) ≤
        (G_aug.treeDist out (G_aug.edge (toAug i)).1 (G_aug.edge (toAug i)).2.1 : ℝ) /
          ((G_aug.edge (toAug i)).2.2 : ℝ) + 3 / 2 := by
    intro i
    let e' := E_list[i.1]'i.2
    let j := toAug i
    have he' : e' ∈ G_v.E := (hE_mem e').mp (List.getElem_mem i.2)
    have ho := hG_v_end e' he'
    have hged : G_aug.edge j = (V_list.idxOf (G_v.tail e'), V_list.idxOf (G_v.head e'), w_int e') := by
      dsimp only [Cited.WGraph.edge, j]
      exact hG_aug_edge_E i.1 i.2
    unfold treeStretch
    rw [hT_raw_path_eq e' he']
    let P := T_gv.forestPath (G_v.tail e') (G_v.head e')
    have hP_path : T_gv.IsPath (G_v.tail e') (G_v.head e') P :=
      forestPath_isPath hT_gv_st.1 (hT_gv_conn _ ho.1 _ ho.2)
    have hP_sub : walkEdges P ⊆ G_v.E := hT_gv_no_bridges e' he'
    have hlen_P : (walkEdges P).card ≤ V_act.card := by
      have hverts_sub : (T_gv.walkVertices (G_v.tail e') P).toFinset ⊆ V_act := by
        intro z hz
        exact hT_gv_V ▸ (IsWalk_vertices_mem hT_gv_val (hT_gv_V ▸ ho.1) hP_path.1).2 z
          (List.mem_toFinset.mp hz)
      have hlen_v : (T_gv.walkVertices (G_v.tail e') P).length ≤ V_act.card := by
        rw [← List.toFinset_card_of_nodup hP_path.2]
        exact Finset.card_le_card hverts_sub
      have hvw : (T_gv.walkVertices (G_v.tail e') P).length = P.length + 1 := by
        simp [MGraph.walkVertices]
      have hwe : (walkEdges P).card ≤ P.length := by
        dsimp only [walkEdges]
        calc (P.map Prod.fst).toFinset.card ≤ (P.map Prod.fst).length := List.toFinset_card_le _
          _ = P.length := List.length_map _
      omega
    have hS_ne : {d | ∃ es, G_aug.IsWalkIn out (G_aug.edge j).1 (G_aug.edge j).2.1 es ∧
        d = G_aug.weightOf es}.Nonempty := by
      rw [hged]
      obtain ⟨es, hes⟩ := hout_conn (V_list.idxOf (G_v.tail e'))
        (hG_aug_n_len ▸ List.idxOf_lt_length_of_mem ((hV_mem _).mpr ho.1))
        (V_list.idxOf (G_v.head e'))
        (hG_aug_n_len ▸ List.idxOf_lt_length_of_mem ((hV_mem _).mpr ho.2))
      exact ⟨G_aug.weightOf es, es, hes, rfl⟩
    obtain ⟨es_min, hes_min, hdist_eq⟩ := Nat.sInf_mem hS_ne
    change G_aug.treeDist out (G_aug.edge j).1 (G_aug.edge j).2.1 = G_aug.weightOf es_min at hdist_eq
    have hdist_sub : (∑ f ∈ walkEdges P, (w_int f : ℝ)) ≤
        (G_aug.treeDist out (G_aug.edge j).1 (G_aug.edge j).2.1 : ℝ) := by
      rw [hged] at hes_min
      obtain ⟨Q, hWQ, hQ_map⟩ := hT_gv_lift hes_min (G_v.tail e') ho.1
        (G_v.head e') ho.2 rfl rfl
      obtain ⟨P', hP'_path, hP'_edges, _⟩ := exists_isPath_of_isWalk hWQ
      have hPP' : P = P' := forestPath_eq_of_isPath hT_gv_st.1 hP'_path
      have hP_edges_Q : walkEdges P ⊆ (es_min.map edgeIdGv).toFinset := by
        rw [hPP']
        intro f hf
        have hfQ := hP'_edges hf
        rw [walkEdges, hQ_map] at hfQ
        exact hfQ
      let wf : ℕ → ℝ := fun f => if f ∈ G_v.E then (w_int f : ℝ) else 1
      have hwf_nn : ∀ f, 0 ≤ wf f := fun f => by
        dsimp only [wf]; split_ifs <;> positivity
      have hsum1 : ∑ f ∈ walkEdges P, (w_int f : ℝ) = ∑ f ∈ walkEdges P, wf f := by
        refine Finset.sum_congr rfl (fun f hf => ?_)
        dsimp only [wf]; rw [ite_eq_left (hP_sub hf)]
      have hsum2 : ∑ f ∈ walkEdges P, wf f ≤ ∑ f ∈ (es_min.map edgeIdGv).toFinset, wf f :=
        Finset.sum_le_sum_of_subset_of_nonneg hP_edges_Q (fun f _ _ => hwf_nn f)
      have hsum3 : ∑ f ∈ (es_min.map edgeIdGv).toFinset, wf f ≤
          ((es_min.map edgeIdGv).map wf).sum :=
        finset_sum_le_list_sum_of_nonneg wf hwf_nn (es_min.map edgeIdGv)
      have hsum4 : ((es_min.map edgeIdGv).map wf).sum = (G_aug.weightOf es_min : ℝ) := by
        unfold Cited.WGraph.weightOf
        rw [Nat.cast_list_sum, List.map_map, List.map_map]
        congr 1
        refine List.map_congr_left (fun k hk => ?_)
        have ⟨hk_out, hk_m⟩ := hIsWalkIn_mem hes_min k hk
        have hk_len : k < G_aug.edges.length := hk_m
        dsimp only [Function.comp_def]
        rw [List.getD_eq_getElem _ _ hk_len]
        by_cases hkm1 : k < m₁
        · have hkG := hedgeId_lt k hkm1
          have hke : E_list[k]'hkm1 = edgeIdGv k := (hedgeId_eq_E k hkm1).symm
          have hged_k : G_aug.edges[k]'hk_len =
              (V_list.idxOf (G_v.tail (edgeIdGv k)), V_list.idxOf (G_v.head (edgeIdGv k)),
                w_int (edgeIdGv k)) := by
            simpa only [hke] using hG_aug_edge_E k hkm1
          dsimp only [wf]
          rw [ite_eq_left hkG, hged_k]
        · have hk_nG := hedgeId_nG_B k hk_out hkm1
          have hk_ltB : k - m₁ < B.length := by rw [hG_aug_m] at hk_m; omega
          have hm1k : E_list.length + (k - m₁) = k := by dsimp only [m₁]; omega
          have hged_k : G_aug.edges[k]'hk_len = (0, V_list.idxOf (B[k - m₁]'hk_ltB), 1) := by
            have hB' := hG_aug_edge_B (k - m₁) hk_ltB
            simpa only [hm1k] using hB'
          dsimp only [wf]
          rw [ite_eq_right hk_nG, hged_k]
          norm_num
      rw [hdist_eq, ← hsum4]
      exact hsum1.le.trans (hsum2.trans hsum3)
    have hwl_eq : walkLength len P = ∑ f ∈ walkEdges P, len f :=
      walkLength_eq_sum_of_isPath len hP_path
    have hwl_le : walkLength len P ≤
        δ * (G_aug.treeDist out (G_aug.edge j).1 (G_aug.edge j).2.1 : ℝ) +
          δ * (V_act.card : ℝ) := by
      calc walkLength len P
          = ∑ f ∈ walkEdges P, len f := hwl_eq
        _ ≤ ∑ f ∈ walkEdges P, δ * ((w_int f : ℝ) + 1) :=
            Finset.sum_le_sum (fun f hf => hlen_upper f (hP_sub hf))
        _ = δ * (∑ f ∈ walkEdges P, (w_int f : ℝ)) + δ * ((walkEdges P).card : ℝ) := by
            simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
              nsmul_eq_mul, mul_one, mul_comm ((walkEdges P).card : ℝ) δ]
        _ ≤ δ * (G_aug.treeDist out (G_aug.edge j).1 (G_aug.edge j).2.1 : ℝ) +
              δ * (V_act.card : ℝ) :=
            add_le_add (mul_le_mul_of_nonneg_left hdist_sub hδ_pos.le)
              (mul_le_mul_of_nonneg_left (by exact_mod_cast hlen_P) hδ_pos.le)
    have hlen_e' : 0 < len e' := hlen_pos e' he'
    have hδ_le_e' : δ * (w_int e' : ℝ) ≤ len e' := hlen_lower e' he'
    have hδ_Vact_e' : δ * (V_act.card : ℝ) ≤ len e' / 2 := hδ_Vact e' he'
    have hw_edge_pos : (0 : ℝ) < (w_int e' : ℝ) :=
      Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by decide : 0 < 4) (hw_int_ge e' he'))
    have hterm1 : δ * (G_aug.treeDist out (G_aug.edge j).1 (G_aug.edge j).2.1 : ℝ) / len e' ≤
        (G_aug.treeDist out (G_aug.edge j).1 (G_aug.edge j).2.1 : ℝ) /
          ((G_aug.edge j).2.2 : ℝ) := by
      rw [hged]
      dsimp only
      have hdiv : δ / len e' ≤ 1 / (w_int e' : ℝ) := by
        rw [div_le_div_iff₀ hlen_e' hw_edge_pos]
        linarith
      have hdt0 : 0 ≤ (G_aug.treeDist out (V_list.idxOf (G_v.tail e')) (V_list.idxOf (G_v.head e')) : ℝ) :=
        Nat.cast_nonneg _
      have heq1 : δ * (G_aug.treeDist out (V_list.idxOf (G_v.tail e')) (V_list.idxOf (G_v.head e')) : ℝ) /
          len e' =
        (G_aug.treeDist out (V_list.idxOf (G_v.tail e')) (V_list.idxOf (G_v.head e')) : ℝ) *
          (δ / len e') := by ring
      have heq2 : (G_aug.treeDist out (V_list.idxOf (G_v.tail e')) (V_list.idxOf (G_v.head e')) : ℝ) /
          (w_int e' : ℝ) =
        (G_aug.treeDist out (V_list.idxOf (G_v.tail e')) (V_list.idxOf (G_v.head e')) : ℝ) *
          (1 / (w_int e' : ℝ)) := by ring
      rw [heq1, heq2]
      exact mul_le_mul_of_nonneg_left hdiv hdt0
    have hterm2 : δ * (V_act.card : ℝ) / len e' ≤ 1 / 2 := by
      rw [div_le_iff₀ hlen_e']
      linarith
    calc 1 + walkLength len P / len e'
        ≤ 1 + (δ * (G_aug.treeDist out (G_aug.edge j).1 (G_aug.edge j).2.1 : ℝ) +
            δ * (V_act.card : ℝ)) / len e' :=
          add_le_add le_rfl (div_le_div_of_nonneg_right hwl_le hlen_e'.le)
      _ = 1 + δ * (G_aug.treeDist out (G_aug.edge j).1 (G_aug.edge j).2.1 : ℝ) / len e' +
          δ * (V_act.card : ℝ) / len e' := by ring
      _ ≤ 1 + (G_aug.treeDist out (G_aug.edge j).1 (G_aug.edge j).2.1 : ℝ) /
            ((G_aug.edge j).2.2 : ℝ) + 1 / 2 := add_le_add (add_le_add le_rfl hterm1) hterm2
      _ = (G_aug.treeDist out (G_aug.edge j).1 (G_aug.edge j).2.1 : ℝ) /
            ((G_aug.edge j).2.2 : ℝ) + 3 / 2 := by ring
  have hlog2 : 1 ≤ (Real.log ((n_orig : ℝ) + 2)) ^ 2 := one_le_log_add_two_sq hn1
  have hnorm1_one : G_v.norm1 (fun _ => (1 : ℝ)) = (G_v.E.card : ℝ) := by
    unfold MGraph.norm1
    simp only [abs_one, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsum_list : ∑ e' ∈ G_v.E, treeStretch G_v T_raw len e' =
      ∑ i : Fin m₁, treeStretch G_v T_raw len (E_list[i.1]'i.2) := by
    refine (Finset.sum_bij (i := fun (i : Fin m₁) _ => E_list[i.1]'i.2)
      (fun (i : Fin m₁) _ => (hE_mem (E_list[i.1]'i.2)).mp (List.getElem_mem i.2))
      (fun (i₁ : Fin m₁) _ (i₂ : Fin m₁) _ h =>
        Fin.ext ((List.Nodup.getElem_inj hE_nd).mp h))
      (fun e' he' => ⟨⟨E_list.idxOf e', List.idxOf_lt_length_of_mem ((hE_mem _).mpr he')⟩,
        Finset.mem_univ _, List.getElem_idxOf _⟩)
      (fun _ _ => rfl)).symm
  have hsum_aug_sub : ∑ i : Fin m₁,
        (G_aug.treeDist out (G_aug.edge (toAug i)).1 (G_aug.edge (toAug i)).2.1 : ℝ) /
          ((G_aug.edge (toAug i)).2.2 : ℝ) ≤ G_aug.totalStretch out := by
    have hcongr : ∑ i : Fin m₁,
          (G_aug.treeDist out (G_aug.edge (toAug i)).1 (G_aug.edge (toAug i)).2.1 : ℝ) /
            ((G_aug.edge (toAug i)).2.2 : ℝ) =
        ∑ j ∈ Finset.univ.image toAug,
          (G_aug.treeDist out (G_aug.edge j).1 (G_aug.edge j).2.1 : ℝ) /
            ((G_aug.edge j).2.2 : ℝ) := by
      rw [Finset.sum_image (fun a _ b _ h => htoAug_inj h)]
    rw [hcongr]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hll_bds := logLogFactor_bounds hV_act_ge2 hV_act_le_n
  have hG_aug_m_le : (G_aug.m : ℝ) ≤ 2 * (m₁ : ℝ) := by
    rw [hG_aug_m]
    have : B.length ≤ m₁ := by rw [← hE_len] at hB_len_lt; omega
    exact_mod_cast (by omega : m₁ + B.length ≤ 2 * m₁)
  have htot_le : G_aug.totalStretch out ≤
      2 * K₁ * (m₁ : ℝ) * (Real.log ((n_orig : ℝ) + 2)) ^ 2 := by
    have h1 : K_AN * (G_aug.m : ℝ) * Cited.logLogFactor G_aug.n ≤
        K₁ * (2 * (m₁ : ℝ)) * (Real.log ((n_orig : ℝ) + 2)) ^ 2 := by
      have hG_aug_n : G_aug.n = V_act.card := hG_aug_n_len.trans hV_len
      rw [hG_aug_n]
      exact mul_le_mul
        (mul_le_mul hKAN_le hG_aug_m_le (Nat.cast_nonneg _) (by positivity))
        hll_bds.2 hll_bds.1 (by positivity)
    linarith [htot_st, h1]
  have hm1_eq : (m₁ : ℝ) = (G_v.E.card : ℝ) := by exact_mod_cast hE_len
  calc ∑ e' ∈ G_v.E, treeStretch G_v T_raw len e'
      = ∑ i : Fin m₁, treeStretch G_v T_raw len (E_list[i.1]'i.2) := hsum_list
    _ ≤ ∑ i : Fin m₁,
          ((G_aug.treeDist out (G_aug.edge (toAug i)).1 (G_aug.edge (toAug i)).2.1 : ℝ) /
            ((G_aug.edge (toAug i)).2.2 : ℝ) + 3 / 2) :=
        Finset.sum_le_sum (fun i _ => hwalkLength_gv_le i)
    _ = (∑ i : Fin m₁,
          (G_aug.treeDist out (G_aug.edge (toAug i)).1 (G_aug.edge (toAug i)).2.1 : ℝ) /
            ((G_aug.edge (toAug i)).2.2 : ℝ)) + (3 / 2 : ℝ) * (m₁ : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        ring
    _ ≤ G_aug.totalStretch out + (3 / 2 : ℝ) * (m₁ : ℝ) := add_le_add hsum_aug_sub le_rfl
    _ ≤ 2 * K₁ * (m₁ : ℝ) * (Real.log ((n_orig : ℝ) + 2)) ^ 2 +
          2 * (m₁ : ℝ) * (Real.log ((n_orig : ℝ) + 2)) ^ 2 := by
        have hm0 : (0 : ℝ) ≤ (m₁ : ℝ) := Nat.cast_nonneg m₁
        have h32_1 : (3 / 2 : ℝ) * (m₁ : ℝ) ≤ 2 * (m₁ : ℝ) :=
          mul_le_mul_of_nonneg_right (by norm_num) hm0
        have h32_2 : 2 * (m₁ : ℝ) ≤ 2 * (m₁ : ℝ) * (Real.log ((n_orig : ℝ) + 2)) ^ 2 :=
          le_mul_of_one_le_right (mul_nonneg (by norm_num) hm0) hlog2
        exact add_le_add htot_le (h32_1.trans h32_2)
    _ = (2 * K₁ + 2) * (Real.log ((n_orig : ℝ) + 2)) ^ 2 * G_v.norm1 (fun _ => 1) := by
        rw [hnorm1_one, ← hm1_eq]; ring

private lemma exists_lsst_of_an19
    (P_AN : WordRAM.Program) (c_AN : ℕ) (K_AN : ℝ)
    (hAN : ∀ G : Cited.WGraph, G.graph.IsValid → G.graph.IsLoopless → G.IsConnected →
      (∀ e ∈ G.edges, 1 ≤ e.2.2) → ∀ ω, ∃ out cost,
        WordRAM.RunsTo (WordRAM.wordSize c_AN G.encode) P_AN G.encode ω out cost ∧
        G.IsSpanningTree out ∧
        G.totalStretch out ≤ K_AN * G.m * Cited.logLogFactor G.n ∧
        (cost : ℝ) ≤ K_AN * (G.m + 1) * (Cited.logLogFactor G.n + Cited.weightFactor G.n G.maxWeight))
    {G : MGraph} (hG : G.IsValid) (hV : G.V.Nonempty)
    {ℓ v : ℕ → ℝ} (hℓ : ∀ e ∈ G.E, 0 < ℓ e) (hv : ∀ e ∈ G.E, 0 < v e) :
    ∃ T, IsLSST G ℓ v ((4 * max 1 K_AN + 5) * (Real.log ((G.n : ℝ) + 2)) ^ 2) T := by
  classical
  let K₁ : ℝ := max 1 K_AN
  have hK₁_ge1 : 1 ≤ K₁ := le_max_left _ _
  have hKAN_le : K_AN ≤ K₁ := le_max_right _ _
  let E_noloop := G.E.filter (fun e => G.tail e ≠ G.head e)
  by_cases hE_nl : E_noloop.Nonempty
  · let G_nl : MGraph := { G with E := E_noloop }
    have hG_nl_val : G_nl.IsValid := fun e he => hG e (Finset.mem_filter.mp he).1
    have hℓ_nl : ∀ e ∈ G_nl.E, 0 < ℓ e := fun e he => hℓ e (Finset.mem_filter.mp he).1
    have hv_nl : ∀ e ∈ G_nl.E, 0 < v e := fun e he => hv e (Finset.mem_filter.mp he).1
    have hnl_ne : ∀ e ∈ G_nl.E, G_nl.tail e ≠ G_nl.head e := fun e he =>
      (Finset.mem_filter.mp he).2
    let V_act : Finset ℕ := E_noloop.biUnion (fun e => {G.tail e, G.head e})
    have hV_act_sub : V_act ⊆ G.V := by
      intro x hx
      rw [Finset.mem_biUnion] at hx
      obtain ⟨e, he, hxe⟩ := hx
      have heG := hG e (Finset.mem_filter.mp he).1
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxe
      exact hxe.elim (· ▸ heG.1) (· ▸ heG.2)
    have hV_act_ge2 : 2 ≤ V_act.card := by
      obtain ⟨e₀, he₀⟩ := hE_nl
      have hne₀ : G.tail e₀ ≠ G.head e₀ := (Finset.mem_filter.mp he₀).2
      have hsub2 : {G.tail e₀, G.head e₀} ⊆ V_act :=
        Finset.subset_biUnion_of_mem (fun e => {G.tail e, G.head e}) he₀
      have hcard2 : ({G.tail e₀, G.head e₀} : Finset ℕ).card = 2 := Finset.card_pair hne₀
      exact hcard2 ▸ Finset.card_le_card hsub2
    have hV_act_le_n : V_act.card ≤ G.n := Finset.card_le_card hV_act_sub
    let G_v := weightedCopyGraph G_nl v
    have hG_v_val : G_v.IsValid := weightedCopyGraph_isValid hG_nl_val v
    have hG_v_card : (G_v.E.card : ℝ) ≤ 2 * (G_nl.E.card : ℝ) := weightedCopyGraph_card_le hv_nl
    have hG_v_orig : ∀ e' ∈ G_v.E, origEdge (copyMod G_nl) e' ∈ E_noloop ∧
        G_v.tail e' = G.tail (origEdge (copyMod G_nl) e') ∧
        G_v.head e' = G.head (origEdge (copyMod G_nl) e') ∧
        G_v.tail e' ≠ G_v.head e' ∧ G_v.tail e' ∈ V_act ∧ G_v.head e' ∈ V_act := by
      intro e' he'
      have hm := weightedCopyGraph_origEdge_mem hE_nl he'
      have htl : G_v.tail e' ∈ V_act := Finset.mem_biUnion.mpr
        ⟨origEdge (copyMod G_nl) e', hm.1, by rw [hm.2.1]; exact Finset.mem_insert_self _ _⟩
      have hhd : G_v.head e' ∈ V_act := Finset.mem_biUnion.mpr
        ⟨origEdge (copyMod G_nl) e', hm.1,
          by rw [hm.2.2]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
      have hne : G_v.tail e' ≠ G_v.head e' := by
        rw [hm.2.1, hm.2.2]; exact hnl_ne _ hm.1
      exact ⟨hm.1, hm.2.1, hm.2.2, hne, htl, hhd⟩
    have hV_act_inc : ∀ x ∈ V_act, ∃ e' ∈ G_v.E, G_v.tail e' = x ∨ G_v.head e' = x := by
      intro x hx
      rw [Finset.mem_biUnion] at hx
      obtain ⟨e, he, hxe⟩ := hx
      have h0_mem : copyId (copyMod G_nl) e 0 ∈ G_v.E :=
        (mem_weightedCopyGraph_E_iff hE_nl).mpr ⟨e, he, 0, edgeMult_pos hE_nl hv_nl he, rfl⟩
      have ht0 : G_v.tail (copyId (copyMod G_nl) e 0) = G.tail e :=
        weightedCopyGraph_tail_copyId hE_nl he
      have hh0 : G_v.head (copyId (copyMod G_nl) e 0) = G.head e :=
        weightedCopyGraph_head_copyId hE_nl he
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxe
      exact ⟨copyId (copyMod G_nl) e 0, h0_mem,
        hxe.elim (fun h => Or.inl (ht0.trans h.symm)) (fun h => Or.inr (hh0.trans h.symm))⟩
    let V_list : List ℕ := V_act.sort (· ≤ ·)
    have hV_len : V_list.length = V_act.card := V_act.length_sort (· ≤ ·)
    have hV_nd : V_list.Nodup := V_act.sort_nodup (· ≤ ·)
    have hV_mem : ∀ x, x ∈ V_list ↔ x ∈ V_act := fun x => V_act.mem_sort (· ≤ ·)
    have hV_ne : V_list ≠ [] := by intro h; simp [h] at hV_len; omega
    let r₀ : ℕ := V_list[0]'(by omega)
    let rest : List ℕ := V_list.tail
    have hV_cons : V_list = r₀ :: rest := by
      cases hVl : V_list with
      | nil => exact absurd hVl hV_ne
      | cons a l => simp [r₀, rest, hVl]
    have hr₀_Vact : r₀ ∈ V_act := (hV_mem r₀).mp (hV_cons ▸ List.mem_cons_self)
    have hr₀_nrest : r₀ ∉ rest := by
      have := hV_nd; rw [hV_cons] at this; exact (List.nodup_cons.mp this).1
    have hrest_nd : rest.Nodup := by
      have := hV_nd; rw [hV_cons] at this; exact (List.nodup_cons.mp this).2
    let B : List ℕ := bridgeVerts G_v V_act r₀ rest
    obtain ⟨hB_nd, hB_rest, hr₀_nB, hB_conn, hB_disj⟩ :=
      bridgeVerts_props G_v V_act r₀ rest hr₀_nrest hrest_nd
    have hB_Vlist : ∀ b ∈ B, b ∈ V_list := fun b hb =>
      hV_cons ▸ List.mem_cons_of_mem _ (hB_rest b hb)
    have hB_Vact : ∀ b ∈ B, b ∈ V_act := fun b hb => (hV_mem b).mp (hB_Vlist b hb)
    have hr₀B_nd : (r₀ :: B).Nodup := List.nodup_cons.mpr ⟨hr₀_nB, hB_nd⟩
    have hB_len_lt : B.length + 1 ≤ G_v.E.card := bridgeVerts_length_le hr₀B_nd
      (fun x hx => by
        rw [List.mem_cons] at hx
        exact hx.elim (fun h => h ▸ hr₀_Vact) (fun h => hB_Vact x h))
      hV_act_inc hB_disj
    let E_list : List ℕ := G_v.E.sort (· ≤ ·)
    have hE_len : E_list.length = G_v.E.card := G_v.E.length_sort (· ≤ ·)
    have hE_nd : E_list.Nodup := G_v.E.sort_nodup (· ≤ ·)
    have hE_mem : ∀ e', e' ∈ E_list ↔ e' ∈ G_v.E := fun e' => G_v.E.mem_sort (· ≤ ·)
    let m₁ : ℕ := E_list.length
    have hm₁_pos : 0 < m₁ := by
      dsimp only [m₁]; rw [hE_len]; exact Nat.lt_of_lt_of_le (Nat.succ_pos _) hB_len_lt
    -- Scaled positive integer weights ≥ 4
    let ℓ_imgs := E_noloop.image ℓ
    have hℓ_imgs_ne : ℓ_imgs.Nonempty := Finset.image_nonempty.mpr hE_nl
    let ℓ_min : ℝ := ℓ_imgs.min' hℓ_imgs_ne
    have hℓ_min_pos : 0 < ℓ_min := by
      obtain ⟨e, he, heq⟩ := Finset.mem_image.mp (Finset.min'_mem ℓ_imgs hℓ_imgs_ne)
      dsimp only [ℓ_min]; rw [← heq]; exact hℓ_nl e he
    have hℓ_min_le : ∀ e ∈ E_noloop, ℓ_min ≤ ℓ e := fun e he =>
      Finset.min'_le ℓ_imgs (ℓ e) (Finset.mem_image_of_mem _ he)
    let δ : ℝ := ℓ_min / (2 * (V_act.card : ℝ))
    have hV_act_pos_r : (0 : ℝ) < (V_act.card : ℝ) := by
      have : 0 < V_act.card := by omega
      exact_mod_cast this
    have hδ_pos : 0 < δ := div_pos hℓ_min_pos (mul_pos (by norm_num) hV_act_pos_r)
    let w_int : ℕ → ℕ := fun e' => Nat.floor (ℓ (origEdge (copyMod G_nl) e') / δ)
    have hw_int_ge : ∀ e' ∈ G_v.E, 4 ≤ w_int e' := by
      intro e' he'
      have hle_min := hℓ_min_le _ (hG_v_orig e' he').1
      have hVa4 : (4 : ℝ) ≤ 2 * (V_act.card : ℝ) := by
        have : (2 : ℝ) ≤ (V_act.card : ℝ) := by exact_mod_cast hV_act_ge2
        linarith
      have hdiv_ge : (4 : ℝ) ≤ ℓ (origEdge (copyMod G_nl) e') / δ := by
        calc (4 : ℝ) ≤ 2 * (V_act.card : ℝ) := hVa4
          _ = ℓ_min / δ := by
              have h2Va_ne : 2 * (V_act.card : ℝ) ≠ 0 := (mul_pos (by norm_num) hV_act_pos_r).ne'
              rw [eq_div_iff hδ_pos.ne']
              dsimp only [δ]
              exact mul_div_cancel₀ _ h2Va_ne
          _ ≤ ℓ (origEdge (copyMod G_nl) e') / δ := div_le_div_of_nonneg_right hle_min hδ_pos.le
      exact Nat.le_floor hdiv_ge
    let G_aug : Cited.WGraph :=
      { n := V_list.length
        edges :=
          E_list.map (fun e' => (V_list.idxOf (G_v.tail e'), V_list.idxOf (G_v.head e'), w_int e')) ++
          B.map (fun b => (0, V_list.idxOf b, 1)) }
    have hG_aug_m : G_aug.m = m₁ + B.length := by
      simp [G_aug, Cited.WGraph.m, m₁]
    have hG_aug_val : G_aug.graph.IsValid := by
      intro ed hed
      dsimp only [Cited.WGraph.graph, G_aug] at hed
      rw [List.mem_map] at hed
      obtain ⟨w, hw, rfl⟩ := hed
      rw [List.mem_append] at hw
      rcases hw with hw | hw <;> rw [List.mem_map] at hw
      · obtain ⟨e', he', rfl⟩ := hw
        have ho := hG_v_orig e' ((hE_mem e').mp he')
        exact ⟨List.idxOf_lt_length_of_mem ((hV_mem _).mpr ho.2.2.2.2.1),
               List.idxOf_lt_length_of_mem ((hV_mem _).mpr ho.2.2.2.2.2)⟩
      · obtain ⟨b, hb, rfl⟩ := hw
        exact ⟨by dsimp only [Cited.WGraph.graph, G_aug]; omega, List.idxOf_lt_length_of_mem (hB_Vlist b hb)⟩
    have hG_aug_loopless : G_aug.graph.IsLoopless := by
      intro ed hed
      dsimp only [Cited.WGraph.graph, G_aug] at hed
      rw [List.mem_map] at hed
      obtain ⟨w, hw, rfl⟩ := hed
      rw [List.mem_append] at hw
      rcases hw with hw | hw <;> rw [List.mem_map] at hw
      · obtain ⟨e', he', rfl⟩ := hw
        have ho := hG_v_orig e' ((hE_mem e').mp he')
        intro hEq
        exact ho.2.2.2.1 (idxOf_inj_of_mem
          ((hV_mem _).mpr ho.2.2.2.2.1) ((hV_mem _).mpr ho.2.2.2.2.2) hEq)
      · obtain ⟨b, hb, rfl⟩ := hw
        dsimp only
        have hb_ne : r₀ ≠ b := fun h => by rw [← h] at hb; exact hr₀_nB hb
        intro hEq
        have h0 : V_list.idxOf r₀ = 0 := by rw [hV_cons, List.idxOf_cons_self]
        exact hb_ne (idxOf_inj_of_mem
          ((hV_mem _).mpr hr₀_Vact) (hB_Vlist b hb) (h0.trans hEq))
    have hG_aug_weights : ∀ ed ∈ G_aug.edges, 1 ≤ ed.2.2 := by
      intro ed hed
      dsimp only [G_aug] at hed
      rw [List.mem_append] at hed
      rcases hed with hed | hed <;> rw [List.mem_map] at hed
      · obtain ⟨e', he', rfl⟩ := hed
        exact Nat.le_trans (by decide) (hw_int_ge e' ((hE_mem e').mp he'))
      · obtain ⟨b, _, rfl⟩ := hed
        exact le_rfl
    have hG_aug_edge_E : ∀ (j : ℕ) (hj : j < m₁),
        G_aug.edges[j]'(by rw [← Cited.WGraph.m, hG_aug_m]; omega) =
          (V_list.idxOf (G_v.tail (E_list[j]'hj)),
           V_list.idxOf (G_v.head (E_list[j]'hj)), w_int (E_list[j]'hj)) := by
      intro j hj
      dsimp only [G_aug]
      rw [List.getElem_append_left (by simp [m₁, hj]), List.getElem_map]
    have hG_aug_edge_B : ∀ (k : ℕ) (hk : k < B.length),
        G_aug.edges[m₁ + k]'(by rw [← Cited.WGraph.m, hG_aug_m]; omega) =
          (0, V_list.idxOf (B[k]'hk), 1) := by
      intro k hk
      dsimp only [G_aug]
      have hlen1 : (E_list.map (fun e' =>
          (V_list.idxOf (G_v.tail e'), V_list.idxOf (G_v.head e'), w_int e'))).length = m₁ := by
        simp [m₁]
      rw [List.getElem_append_right (by omega)]
      simp only [hlen1, Nat.add_sub_cancel_left, List.getElem_map]
    let H_br := gvWithBridges G_v V_act r₀ B
    have hH_br_conn : ∀ x ∈ V_act, H_br.Connected r₀ x := by
      intro x hx
      have hxV : x ∈ r₀ :: rest := hV_cons ▸ (hV_mem x).mpr hx
      rw [List.mem_cons] at hxV
      exact hxV.elim (fun h => h ▸ connected_refl H_br r₀) (fun h => hB_conn x h)
    have hH_br_lift_walk : ∀ {a b : ℕ} {P : List (ℕ × Bool)},
        H_br.IsWalk a b P → a ∈ V_act →
        ∃ es : List ℕ, G_aug.IsWalkIn (List.range G_aug.m) (V_list.idxOf a) (V_list.idxOf b) es := by
      intro a b P hWP ha
      induction hWP with
      | nil s => exact ⟨[], .nil _⟩
      | @cons s _ x xs hxE hsx hrest ih =>
        have hx_edge : (x.1 ∈ G_v.E ∧ H_br.tail x.1 = G_v.tail x.1 ∧ H_br.head x.1 = G_v.head x.1) ∨
            (∃ b' ∈ B, x.1 = copyMod G_v + b' ∧ H_br.tail x.1 = r₀ ∧ H_br.head x.1 = b') := by
          dsimp only [H_br, gvWithBridges] at hxE ⊢
          rw [Finset.mem_union] at hxE
          rcases hxE with hxG | hxb
          · left; exact ⟨hxG, ite_eq_left hxG, ite_eq_left hxG⟩
          · right
            rw [Finset.mem_image] at hxb
            obtain ⟨b', hb', hbeq⟩ := hxb
            have hb'_mem := List.mem_toFinset.mp hb'
            have hnG : copyMod G_v + b' ∉ G_v.E := fun h =>
              Nat.not_lt_of_ge (Nat.le_add_right _ _) (lt_copyMod h)
            refine ⟨b', hb'_mem, hbeq.symm, ?_, ?_⟩
            · rw [← hbeq]; exact ite_eq_right hnG
            · rw [← hbeq, ite_eq_right hnG, Nat.add_sub_cancel_left]
        have hdst_Vact : H_br.dst x ∈ V_act := by
          rcases hx_edge with ⟨hxG, ht, hh⟩ | ⟨b', hb', _, ht, hh⟩
          · have ho := hG_v_orig x.1 hxG
            cases hx2 : x.2
            · simp [MGraph.dst, hx2, ht]; exact ho.2.2.2.2.1
            · simp [MGraph.dst, hx2, hh]; exact ho.2.2.2.2.2
          · cases hx2 : x.2
            · simp [MGraph.dst, hx2, ht]; exact hr₀_Vact
            · simp [MGraph.dst, hx2, hh]; exact hB_Vact b' hb'
        obtain ⟨es, hes⟩ := ih hdst_Vact
        rcases hx_edge with ⟨hxG, ht, hh⟩ | ⟨b', hb', hxeq, ht, hh⟩
        · let j := E_list.idxOf x.1
          have hj_lt : j < m₁ := List.idxOf_lt_length_of_mem ((hE_mem _).mpr hxG)
          have hj_len : j < G_aug.edges.length := by change j < G_aug.m; rw [hG_aug_m]; omega
          have hj_m : j < G_aug.m := hj_len
          have hj_rng : j ∈ List.range G_aug.m := List.mem_range.mpr hj_m
          have hj_get : E_list[j]'hj_lt = x.1 := List.getElem_idxOf hj_lt
          have hged : G_aug.edges[j]'hj_len =
              (V_list.idxOf (G_v.tail x.1), V_list.idxOf (G_v.head x.1), w_int x.1) := by
            rw [hG_aug_edge_E j hj_lt, hj_get]
          have hend : (G_aug.edges[j]'hj_len).1 = V_list.idxOf s ∧
              (G_aug.edges[j]'hj_len).2.1 = V_list.idxOf (H_br.dst x) ∨
              (G_aug.edges[j]'hj_len).1 = V_list.idxOf (H_br.dst x) ∧
              (G_aug.edges[j]'hj_len).2.1 = V_list.idxOf s := by
            rw [hged, ← hsx]
            cases hx2 : x.2 <;> simp [MGraph.src, MGraph.dst, hx2, ht, hh]
          exact ⟨j :: es, .cons hj_rng hj_m hend hes⟩
        · let k := B.idxOf b'
          have hk_lt : k < B.length := List.idxOf_lt_length_of_mem hb'
          let j := m₁ + k
          have hj_len : j < G_aug.edges.length := by change j < G_aug.m; rw [hG_aug_m]; omega
          have hj_m : j < G_aug.m := hj_len
          have hj_rng : j ∈ List.range G_aug.m := List.mem_range.mpr hj_m
          have hk_get : B[k]'hk_lt = b' := List.getElem_idxOf hk_lt
          have hged : G_aug.edges[j]'hj_len = (0, V_list.idxOf b', 1) := by
            dsimp only [j]
            rw [hG_aug_edge_B k hk_lt, hk_get]
          have h0_eq : (0 : ℕ) = V_list.idxOf r₀ := by
            rw [hV_cons, List.idxOf_cons_self]
          have hend : (G_aug.edges[j]'hj_len).1 = V_list.idxOf s ∧
              (G_aug.edges[j]'hj_len).2.1 = V_list.idxOf (H_br.dst x) ∨
              (G_aug.edges[j]'hj_len).1 = V_list.idxOf (H_br.dst x) ∧
              (G_aug.edges[j]'hj_len).2.1 = V_list.idxOf s := by
            rw [hged, h0_eq, ← hsx]
            cases hx2 : x.2 <;> simp [MGraph.src, MGraph.dst, hx2, ht, hh]
          exact ⟨j :: es, .cons hj_rng hj_m hend hes⟩
    have hG_aug_conn : G_aug.IsConnected := by
      refine ⟨by dsimp only [G_aug]; rw [hV_len]; omega, fun u hu v hv => ?_⟩
      have hu_Vact : V_list[u]'hu ∈ V_act := (hV_mem _).mp (List.getElem_mem hu)
      have hv_Vact : V_list[v]'hv ∈ V_act := (hV_mem _).mp (List.getElem_mem hv)
      have hconn_uv := connected_trans (connected_symm (hH_br_conn _ hu_Vact)) (hH_br_conn _ hv_Vact)
      obtain ⟨P, hWP⟩ := hconn_uv
      obtain ⟨es, hes⟩ := hH_br_lift_walk hWP hu_Vact
      rw [idxOf_getElem_of_nodup hV_nd hu, idxOf_getElem_of_nodup hV_nd hv] at hes
      exact ⟨es, hes⟩
    obtain ⟨out, cost, _, hT_st_out, htot_st, _⟩ :=
      hAN G_aug hG_aug_val hG_aug_loopless hG_aug_conn hG_aug_weights (fun _ => false)
    rcases hT_st_out with ⟨hout_nd, hout_lt, hout_len, hout_conn⟩
    let bridgeBase : ℕ := max (copyMod G) (copyMod G_v)
    let edgeIdGv : ℕ → ℕ := fun j =>
      if h : j < m₁ then E_list[j]'h else bridgeBase + B[j - m₁]?.getD 0
    have hedgeId_ge : ∀ j, m₁ ≤ j → bridgeBase ≤ edgeIdGv j := fun j hj => by
      dsimp only [edgeIdGv]
      rw [dite_eq_right_of_eq_false (eq_false (Nat.not_lt_of_ge hj))]
      exact Nat.le_add_right _ _
    have hedgeId_lt : ∀ j, (h : j < m₁) → edgeIdGv j ∈ G_v.E := fun j hj => by
      dsimp only [edgeIdGv]
      rw [dite_eq_left_of_eq_true (eq_true hj)]
      exact (hE_mem _).mp (List.getElem_mem hj)
    have hedgeId_inj : ∀ j₁ < G_aug.m, ∀ j₂ < G_aug.m,
        edgeIdGv j₁ = edgeIdGv j₂ → j₁ = j₂ := by
      intro j₁ hj₁ j₂ hj₂ hEq
      by_cases h1 : j₁ < m₁ <;> by_cases h2 : j₂ < m₁
      · dsimp only [edgeIdGv] at hEq
        rw [dite_eq_left_of_eq_true (eq_true h1), dite_eq_left_of_eq_true (eq_true h2)] at hEq
        exact (List.Nodup.getElem_inj hE_nd).mp hEq
      · exfalso
        have hlt := lt_copyMod (hedgeId_lt j₁ h1)
        have hge := (le_max_right (copyMod G) (copyMod G_v)).trans (hedgeId_ge j₂ (Nat.le_of_not_lt h2))
        omega
      · exfalso
        have hlt := lt_copyMod (hedgeId_lt j₂ h2)
        have hge := (le_max_right (copyMod G) (copyMod G_v)).trans (hedgeId_ge j₁ (Nat.le_of_not_lt h1))
        omega
      · dsimp only [edgeIdGv] at hEq
        rw [dite_eq_right_of_eq_false (eq_false h1), dite_eq_right_of_eq_false (eq_false h2)] at hEq
        have hk1 : j₁ - m₁ < B.length := by rw [hG_aug_m] at hj₁; omega
        have hk2 : j₂ - m₁ < B.length := by rw [hG_aug_m] at hj₂; omega
        have hB_eq : B[j₁ - m₁]'hk1 = B[j₂ - m₁]'hk2 := by
          simp only [List.getElem?_eq_getElem hk1, List.getElem?_eq_getElem hk2, Option.getD_some] at hEq
          omega
        have := (List.Nodup.getElem_inj hB_nd).mp hB_eq
        omega
    let idxGv : Finset ℕ := out.toFinset
    let T_gv : MGraph :=
      { V := V_act
        E := idxGv.image edgeIdGv
        tail := fun f => if f ∈ G_v.E then G_v.tail f else r₀
        head := fun f => if f ∈ G_v.E then G_v.head f else f - bridgeBase }
    have hT_gv_E_card : T_gv.E.card = V_act.card - 1 := by
      dsimp only [T_gv, idxGv]
      rw [Finset.card_image_of_injOn (fun a ha b hb h =>
        hedgeId_inj a (hout_lt a (List.mem_toFinset.mp ha))
          b (hout_lt b (List.mem_toFinset.mp hb)) h)]
      rw [List.toFinset_card_of_nodup hout_nd, hout_len]
      dsimp only [G_aug]
      rw [hV_len]
    have hT_gv_edge_B : ∀ j (hj : j ∈ out) (hnj : ¬ j < m₁),
        let b := B[j - m₁]'(by have := hout_lt j hj; rw [hG_aug_m] at this; omega)
        edgeIdGv j = bridgeBase + b ∧
        edgeIdGv j ∉ G_v.E ∧
        T_gv.tail (edgeIdGv j) = r₀ ∧ T_gv.head (edgeIdGv j) = b := by
      intro j hj hnj
      have hjm := hout_lt j hj
      have hk : j - m₁ < B.length := by rw [hG_aug_m] at hjm; omega
      have hnG : edgeIdGv j ∉ G_v.E := fun h =>
        Nat.not_lt_of_ge ((le_max_right (copyMod G) (copyMod G_v)).trans
          (hedgeId_ge j (Nat.le_of_not_lt hnj))) (lt_copyMod h)
      have heq_id : edgeIdGv j = bridgeBase + B[j - m₁]'hk := by
        dsimp only [edgeIdGv]
        rw [dite_eq_right_of_eq_false (eq_false hnj), List.getElem?_eq_getElem hk, Option.getD_some]
      refine ⟨heq_id, hnG, ?_, ?_⟩
      · dsimp only [T_gv]; exact ite_eq_right hnG
      · dsimp only [T_gv]; rw [ite_eq_right hnG, heq_id, Nat.add_sub_cancel_left]
    have hT_gv_val : T_gv.IsValid := by
      intro f hf
      dsimp only [T_gv] at hf ⊢
      rw [Finset.mem_image] at hf
      obtain ⟨j, hj, rfl⟩ := hf
      have hj_out := List.mem_toFinset.mp hj
      by_cases hjm : j < m₁
      · have hfG := hedgeId_lt j hjm
        rw [ite_eq_left hfG, ite_eq_left hfG]
        have ho := hG_v_orig _ hfG
        exact ⟨ho.2.2.2.2.1, ho.2.2.2.2.2⟩
      · obtain ⟨heq_id, hnG, _, _⟩ := hT_gv_edge_B j hj_out hjm
        have hb_mem : B[j - m₁]'(by have := hout_lt j hj_out; rw [hG_aug_m] at this; omega) ∈ B :=
          List.getElem_mem _
        rw [ite_eq_right hnG, ite_eq_right hnG, heq_id, Nat.add_sub_cancel_left]
        exact ⟨hr₀_Vact, hB_Vact _ hb_mem⟩
    have hT_gv_lift : ∀ {a b : ℕ} {es : List ℕ},
        G_aug.IsWalkIn out a b es →
        ∀ u ∈ V_act, ∀ v ∈ V_act,
        V_list.idxOf u = a → V_list.idxOf v = b →
        ∃ P : List (ℕ × Bool), T_gv.IsWalk u v P ∧ P.map Prod.fst = es.map edgeIdGv := by
      intro a b es hes
      induction hes with
      | nil s =>
        intro u hu v hv hua hvb
        have huv : u = v := idxOf_inj_of_mem ((hV_mem _).mpr hu) ((hV_mem _).mpr hv) (hua.trans hvb.symm)
        subst huv; exact ⟨[], .nil u, rfl⟩
      | @cons a_cur x_next b_fin j es' hj_out hj_m hend hrest ih =>
        intro u hu v hv hua hvb
        have hx_lt : x_next < V_list.length := by
          rcases hend with ⟨_, h2⟩ | ⟨h1, _⟩
          · rw [← h2]; exact (hG_aug_val _ (List.mem_map.mpr ⟨_, List.getElem_mem hj_m, rfl⟩)).2
          · rw [← h1]; exact (hG_aug_val _ (List.mem_map.mpr ⟨_, List.getElem_mem hj_m, rfl⟩)).1
        let w := V_list[x_next]'hx_lt
        have hw_Vact : w ∈ V_act := (hV_mem w).mp (List.getElem_mem hx_lt)
        have hwx : V_list.idxOf w = x_next := idxOf_getElem_of_nodup hV_nd hx_lt
        obtain ⟨P, hWP, hP_map⟩ := ih w hw_Vact v hv hwx hvb
        have hf_mem : edgeIdGv j ∈ T_gv.E :=
          Finset.mem_image_of_mem _ (List.mem_toFinset.mpr hj_out)
        have hj_len : j < G_aug.edges.length := by rw [← Cited.WGraph.m]; exact hj_m
        have hends_j : V_list.idxOf (T_gv.tail (edgeIdGv j)) = (G_aug.edges[j]'hj_len).1 ∧
            V_list.idxOf (T_gv.head (edgeIdGv j)) = (G_aug.edges[j]'hj_len).2.1 ∧
            T_gv.tail (edgeIdGv j) ∈ V_act ∧ T_gv.head (edgeIdGv j) ∈ V_act := by
          by_cases hjm1 : j < m₁
          · have hfG := hedgeId_lt j hjm1
            have hget : E_list[j]'hjm1 = edgeIdGv j := by
              dsimp only [edgeIdGv]
              exact (dite_eq_left_of_eq_true (eq_true hjm1)).symm
            have hged : G_aug.edges[j]'hj_len =
                (V_list.idxOf (G_v.tail (edgeIdGv j)), V_list.idxOf (G_v.head (edgeIdGv j)),
                  w_int (edgeIdGv j)) := by
              simpa only [hget] using hG_aug_edge_E j hjm1
            have ht_eq : T_gv.tail (edgeIdGv j) = G_v.tail (edgeIdGv j) := by
              dsimp only [T_gv]; exact ite_eq_left hfG
            have hh_eq : T_gv.head (edgeIdGv j) = G_v.head (edgeIdGv j) := by
              dsimp only [T_gv]; exact ite_eq_left hfG
            have ho := hG_v_orig _ hfG
            rw [hged, ht_eq, hh_eq]
            exact ⟨rfl, rfl, ho.2.2.2.2.1, ho.2.2.2.2.2⟩
          · have hk : j - m₁ < B.length := by rw [hG_aug_m] at hj_m; omega
            obtain ⟨_, _, ht_eq, hh_eq⟩ := hT_gv_edge_B j hj_out hjm1
            have hm1k : m₁ + (j - m₁) = j := by omega
            have hged : G_aug.edges[j]'hj_len = (0, V_list.idxOf (B[j - m₁]'hk), 1) := by
              have hB' := hG_aug_edge_B (j - m₁) hk
              simpa only [hm1k] using hB'
            have h0_eq : V_list.idxOf r₀ = 0 := by rw [hV_cons, List.idxOf_cons_self]
            rw [hged, ht_eq, hh_eq, h0_eq]
            exact ⟨rfl, rfl, hr₀_Vact, hB_Vact _ (List.getElem_mem hk)⟩
        rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hu_eq : T_gv.tail (edgeIdGv j) = u := idxOf_inj_of_mem
            ((hV_mem _).mpr hends_j.2.2.1) ((hV_mem _).mpr hu) (hends_j.1.trans (h1.trans hua.symm))
          have hw_eq : T_gv.head (edgeIdGv j) = w := idxOf_inj_of_mem
            ((hV_mem _).mpr hends_j.2.2.2) ((hV_mem _).mpr hw_Vact) (hends_j.2.1.trans (h2.trans hwx.symm))
          refine ⟨(edgeIdGv j, true) :: P, .cons hf_mem (by simp [MGraph.src, hu_eq])
            (by simpa [MGraph.dst, hw_eq] using hWP), by simp [hP_map]⟩
        · have hu_eq : T_gv.head (edgeIdGv j) = u := idxOf_inj_of_mem
            ((hV_mem _).mpr hends_j.2.2.2) ((hV_mem _).mpr hu) (hends_j.2.1.trans (h2.trans hua.symm))
          have hw_eq : T_gv.tail (edgeIdGv j) = w := idxOf_inj_of_mem
            ((hV_mem _).mpr hends_j.2.2.1) ((hV_mem _).mpr hw_Vact) (hends_j.1.trans (h1.trans hwx.symm))
          refine ⟨(edgeIdGv j, false) :: P, .cons hf_mem (by simp [MGraph.src, hu_eq])
            (by simpa [MGraph.dst, hw_eq] using hWP), by simp [hP_map]⟩
    have hT_gv_conn : ∀ u ∈ V_act, ∀ v ∈ V_act, T_gv.Connected u v := by
      intro u hu v hv
      obtain ⟨es, hes⟩ := hout_conn (V_list.idxOf u) (List.idxOf_lt_length_of_mem ((hV_mem _).mpr hu))
        (V_list.idxOf v) (List.idxOf_lt_length_of_mem ((hV_mem _).mpr hv))
      obtain ⟨P, hWP, _⟩ := hT_gv_lift hes u hu v hv rfl rfl
      exact ⟨P, hWP⟩
    have hT_gv_st : T_gv.IsSpanningTreeOn V_act :=
      ⟨isForest_of_connected_card_le hT_gv_val ⟨r₀, hr₀_Vact⟩ hT_gv_conn (by rw [hT_gv_E_card]),
        rfl, hT_gv_conn⟩
    -- Cut-parity shows no bridge edge lies on `T_gv.forestPath` between endpoints of any `e' ∈ G_v.E`
    have hT_gv_no_bridges : ∀ e' ∈ G_v.E,
        walkEdges (T_gv.forestPath (G_v.tail e') (G_v.head e')) ⊆ G_v.E := by
      intro e' he' f hf
      have ho := hG_v_orig e' he'
      have hP := forestPath_isPath hT_gv_st.1 (hT_gv_conn _ ho.2.2.2.2.1 _ ho.2.2.2.2.2)
      obtain ⟨bf, hbf⟩ := mem_walkEdges_iff.mp hf
      have hfT : f ∈ T_gv.E := IsWalk_edges_mem hP.1 hbf
      dsimp only [T_gv, idxGv] at hfT
      rw [Finset.mem_image] at hfT
      obtain ⟨j, hj, rfl⟩ := hfT
      have hj_out := List.mem_toFinset.mp hj
      by_cases hjm : j < m₁
      · exact hedgeId_lt j hjm
      · exfalso
        have hjm_aug := hout_lt j hj_out
        have hk : j - m₁ < B.length := by rw [hG_aug_m] at hjm_aug; omega
        let b := B[j - m₁]'hk
        have hb_mem : b ∈ B := List.getElem_mem hk
        obtain ⟨hj_id, hnG, htf, hhf⟩ := hT_gv_edge_B j hj_out hjm
        let S_b := V_act.filter (fun w => G_v.Connected b w)
        have hb_Sb : b ∈ S_b := Finset.mem_filter.mpr ⟨hB_Vact b hb_mem, connected_refl G_v b⟩
        have hr₀_Sb : r₀ ∉ S_b := fun h => hB_disj r₀ List.mem_cons_self b
          (List.mem_cons_of_mem _ hb_mem) (fun heq => by
            have hb_mem' : b ∈ B := hb_mem
            rw [← heq] at hb_mem'
            exact hr₀_nB hb_mem')
          (connected_symm (Finset.mem_filter.mp h).2)
        have hsame_e' : G_v.tail e' ∈ S_b ↔ G_v.head e' ∈ S_b := by
          have hc : G_v.Connected (G_v.tail e') (G_v.head e') :=
            ⟨[(e', true)], .cons he' rfl (.nil _)⟩
          constructor <;> intro hmem
          · exact Finset.mem_filter.mpr ⟨ho.2.2.2.2.2,
              connected_trans (Finset.mem_filter.mp hmem).2 hc⟩
          · exact Finset.mem_filter.mpr ⟨ho.2.2.2.2.1,
              connected_trans (Finset.mem_filter.mp hmem).2 (connected_symm hc)⟩
        have hother : ∀ g ∈ walkEdges (T_gv.forestPath (G_v.tail e') (G_v.head e')),
            g ≠ edgeIdGv j → (T_gv.tail g ∈ S_b ↔ T_gv.head g ∈ S_b) := by
          intro g hg hne
          obtain ⟨bg, hbg⟩ := mem_walkEdges_iff.mp hg
          have hgT : g ∈ T_gv.E := IsWalk_edges_mem hP.1 hbg
          dsimp only [T_gv, idxGv] at hgT
          rw [Finset.mem_image] at hgT
          obtain ⟨j', hj', rfl⟩ := hgT
          have hj'_out := List.mem_toFinset.mp hj'
          by_cases hj'm : j' < m₁
          · have hgG := hedgeId_lt j' hj'm
            have hgo := hG_v_orig _ hgG
            have hgt : T_gv.tail (edgeIdGv j') = G_v.tail (edgeIdGv j') := by
              dsimp only [T_gv]; exact ite_eq_left hgG
            have hgh : T_gv.head (edgeIdGv j') = G_v.head (edgeIdGv j') := by
              dsimp only [T_gv]; exact ite_eq_left hgG
            rw [hgt, hgh]
            have hgc : G_v.Connected (G_v.tail (edgeIdGv j')) (G_v.head (edgeIdGv j')) :=
              ⟨[(edgeIdGv j', true)], .cons hgG rfl (.nil _)⟩
            constructor <;> intro hmem
            · exact Finset.mem_filter.mpr ⟨hgo.2.2.2.2.2,
                connected_trans (Finset.mem_filter.mp hmem).2 hgc⟩
            · exact Finset.mem_filter.mpr ⟨hgo.2.2.2.2.1,
                connected_trans (Finset.mem_filter.mp hmem).2 (connected_symm hgc)⟩
          · have hk' : j' - m₁ < B.length := by
              have := hout_lt j' hj'_out; rw [hG_aug_m] at this; omega
            let b' := B[j' - m₁]'hk'
            have hb'_mem : b' ∈ B := List.getElem_mem hk'
            obtain ⟨hj'_id, _, hgt, hgh⟩ := hT_gv_edge_B j' hj'_out hj'm
            have hbb' : b ≠ b' := by
              intro hEq
              exact hne (hj'_id.trans ((congrArg (bridgeBase + ·) hEq.symm).trans hj_id.symm))
            have hb'_nSb : b' ∉ S_b := fun h => hB_disj b (List.mem_cons_of_mem _ hb_mem)
              b' (List.mem_cons_of_mem _ hb'_mem) hbb' (Finset.mem_filter.mp h).2
            rw [hgt, hgh]
            exact ⟨fun h => absurd h hr₀_Sb, fun h => absurd h hb'_nSb⟩
        have hcross : ¬ (T_gv.tail (edgeIdGv j) ∈ S_b ↔ T_gv.head (edgeIdGv j) ∈ S_b) := by
          rw [htf, hhf]; exact fun h => hr₀_Sb (h.mpr hb_Sb)
        exact isPath_no_unique_cut_edge hP hsame_e' hother hcross hf
    -- Attach `G.V \ V_act` to `T_gv` via edges strictly above `max (copyMod G) (copyMod G_v)`
    let base := max bridgeBase (T_gv.E.sup id + 1)
    let T_raw := attachVerts T_gv r₀ G.V base
    have hT_raw_st : T_raw.IsSpanningTreeOn G_v.V := by
      rw [weightedCopyGraph_V]
      exact attachVerts_isSpanningTreeOn hT_gv_st hr₀_Vact hV_act_sub
        (fun f hf => Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (f := id) hf))
          (le_max_right _ _))
    have hT_raw_sub : T_raw.IsSubgraph T_gv :=
      ⟨hV_act_sub, Finset.subset_union_left, fun f hf => by
        dsimp only [T_raw, attachVerts]; exact ⟨(ite_eq_left hf).symm, (ite_eq_left hf).symm⟩⟩
    have hT_raw_nonGv : ∀ f ∈ T_raw.E, f ∉ G_v.E → copyMod G ≤ f := by
      intro f hf hf_nG
      dsimp only [T_raw, attachVerts] at hf
      rw [Finset.mem_union] at hf
      rcases hf with hf_gv | hf_att
      · dsimp only [T_gv, idxGv] at hf_gv
        rw [Finset.mem_image] at hf_gv
        obtain ⟨j, hj, rfl⟩ := hf_gv
        by_cases hjm : j < m₁
        · exact absurd (hedgeId_lt j hjm) hf_nG
        · exact (le_max_left (copyMod G) (copyMod G_v)).trans (hedgeId_ge j (Nat.le_of_not_lt hjm))
      · rw [Finset.mem_image] at hf_att
        obtain ⟨w, _, rfl⟩ := hf_att
        exact le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (Nat.le_add_right _ _))
    have hT_raw_Gv_edges : ∀ f ∈ T_raw.E, f ∈ G_v.E →
        T_raw.tail f = G_v.tail f ∧ T_raw.head f = G_v.head f := by
      intro f hf hfG
      dsimp only [T_raw, attachVerts] at hf ⊢
      have hf_gv : f ∈ T_gv.E := by
        rw [Finset.mem_union] at hf
        rcases hf with h | h
        · exact h
        · exfalso
          rw [Finset.mem_image] at h
          obtain ⟨w, _, rfl⟩ := h
          have hlt := lt_copyMod hfG
          have hge : copyMod G_v ≤ base + w :=
            le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (Nat.le_add_right _ _))
          omega
      rw [ite_eq_left hf_gv, ite_eq_left hf_gv]
      dsimp only [T_gv]
      exact ⟨ite_eq_left hfG, ite_eq_left hfG⟩
    have hT_raw_path_eq : ∀ e' ∈ G_v.E,
        T_raw.forestPath (G_v.tail e') (G_v.head e') =
          T_gv.forestPath (G_v.tail e') (G_v.head e') := by
      intro e' he'
      have ho := hG_v_orig e' he'
      exact (forestPath_subgraph hT_raw_st.1 hT_raw_sub (hT_gv_conn _ ho.2.2.2.2.1 _ ho.2.2.2.2.2)).symm
    -- Bound sum of `treeStretch` on `G_v` using `[AN19]`
    have hsum_raw : ∑ e' ∈ G_v.E, treeStretch G_v T_raw (weightedCopyLen G_nl ℓ) e' ≤
        (2 * K₁ + 2) * (Real.log ((G.n : ℝ) + 2)) ^ 2 * (G_v.norm1 (fun _ => 1)) := by
      refine an19_stretch_sum_bound (Finset.card_pos.mpr hV) hV_act_ge2 hV_act_le_n hV_len hV_mem
        (fun e' he' => let ho := hG_v_orig e' he'; ⟨ho.2.2.2.2.1, ho.2.2.2.2.2⟩)
        hB_len_lt hE_len hE_nd hE_mem hδ_pos hw_int_ge
        (fun e' he' => weightedCopyLen_pos hE_nl hℓ_nl he')
        (fun f _ => by
          dsimp only [weightedCopyLen, w_int]
          have hlt := Nat.lt_floor_add_one (ℓ (origEdge (copyMod G_nl) f) / δ)
          have hmul := mul_le_mul_of_nonneg_left hlt.le hδ_pos.le
          have heq : δ * (ℓ (origEdge (copyMod G_nl) f) / δ) = ℓ (origEdge (copyMod G_nl) f) :=
            mul_div_cancel₀ _ hδ_pos.ne'
          linarith)
        (fun e' he' => by
          have ho := hG_v_orig e' he'
          dsimp only [weightedCopyLen, w_int]
          have hfl := Nat.floor_le (div_nonneg (hℓ_nl _ ho.1).le hδ_pos.le)
          have hmul := mul_le_mul_of_nonneg_left hfl hδ_pos.le
          have heq : δ * (ℓ (origEdge (copyMod G_nl) e') / δ) = ℓ (origEdge (copyMod G_nl) e') :=
            mul_div_cancel₀ _ hδ_pos.ne'
          linarith)
        (fun e' he' => by
          have ho := hG_v_orig e' he'
          have hVa_ne : (V_act.card : ℝ) ≠ 0 := by
            have : 0 < V_act.card := by omega
            exact_mod_cast this.ne'
          have heq : δ * (V_act.card : ℝ) = ℓ_min / 2 := by
            dsimp only [δ]
            calc (ℓ_min / (2 * (V_act.card : ℝ))) * (V_act.card : ℝ)
                = (ℓ_min / 2) * ((V_act.card : ℝ) / (V_act.card : ℝ)) := by ring
              _ = ℓ_min / 2 := by rw [div_self hVa_ne, mul_one]
          rw [heq]
          exact div_le_div_of_nonneg_right (hℓ_min_le _ ho.1) (by norm_num))
        rfl hG_aug_m hG_aug_edge_E hG_aug_edge_B hout_conn htot_st hK₁_ge1 hKAN_le
        hedgeId_lt
        (fun j hj => by dsimp only [edgeIdGv]; exact dite_eq_left_of_eq_true (eq_true hj))
        (fun k hk hnk => (hT_gv_edge_B k hk hnk).2.1)
        rfl hT_gv_val hT_gv_st hT_gv_conn hT_gv_lift hT_gv_no_bridges hT_raw_path_eq
    have hlsst_raw : IsLSST G_v (weightedCopyLen G_nl ℓ) (fun _ => 1)
        ((2 * K₁ + 2) * (Real.log ((G.n : ℝ) + 2)) ^ 2) T_raw := by
      refine ⟨hT_raw_st, hT_raw_Gv_edges, fun e' he' f hf => ?_, ?_⟩
      · rw [hT_raw_path_eq e' he'] at hf
        exact hT_gv_no_bridges e' he' hf
      · simpa only [one_mul] using hsum_raw
    exact ⟨projectTree G_nl v T_raw,
      lsst_of_projectTree (G_nl := G_nl) (G_v := G_v) (T_raw := T_raw)
        hG hV hK₁_ge1 rfl rfl hE_nl hℓ hv hT_raw_nonGv hlsst_raw⟩
  · exact exists_lsst_when_no_nonloop hG hV hv
      (fun e he => by
        by_contra hne
        exact hE_nl ⟨e, Finset.mem_filter.mpr ⟨he, hne⟩⟩) hK₁_ge1

/-- **Theorem 2.2** (Static Low-Stretch Spanning Tree, page 7):
From `[AN19, Theorem 1]` (`Cited.LowStretchSpanningTree`), there exists a static LSST oracle with
overhead `C * log²(n + 2)` (`HasLSSTSpec oracle C`). -/
theorem theorem_2_2 :
    ∃ oracle C, HasLSSTSpec oracle C := by
  classical
  obtain ⟨P_AN, c_AN, K_AN, hAN⟩ := MinCostFlow.LowStretch.lowStretchSpanningTree_lsst
  let C : ℝ := 4 * max 1 K_AN + 5
  let oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph := fun G ℓ v =>
    if h : G.IsValid ∧ G.V.Nonempty ∧ (∀ e ∈ G.E, 0 < ℓ e) ∧ (∀ e ∈ G.E, 0 < v e) then
      Classical.choose (exists_lsst_of_an19 P_AN c_AN K_AN hAN h.1 h.2.1 h.2.2.1 h.2.2.2)
    else G
  refine ⟨oracle, C, fun G ℓ v hG hV hℓ hv => ?_⟩
  have hcond : G.IsValid ∧ G.V.Nonempty ∧ (∀ e ∈ G.E, 0 < ℓ e) ∧ (∀ e ∈ G.E, 0 < v e) :=
    ⟨hG, hV, hℓ, hv⟩
  dsimp only [oracle, C]
  rw [dite_eq_left_of_eq_true (eq_true hcond)]
  exact Classical.choose_spec (exists_lsst_of_an19 P_AN c_AN K_AN hAN hG hV hℓ hv)

end MinCostFlow.LSF
