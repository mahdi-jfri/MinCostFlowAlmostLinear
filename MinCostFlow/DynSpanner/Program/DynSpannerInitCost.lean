module

public import MinCostFlow.DynSpanner.Program.DynSpannerInit

import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Concrete length, word-size, and paper-shape init cost bounds (`DynSpannerInitCost`)

Bounds the size and maximum entry of `canonSparsifyInput (activeSubgraph G) (activeSubgraph G) idEmb`,
converts `Nat.log 2` terms to `Real.log`, and derives the paper-shape cost bound matching
`Complexity.lean` (Theorem 8.2 initialization bound, using `max P.p_t 1` in full generality and
`P.p_t` when `1 ≤ P.p_t`).
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner

public section

lemma foldr_max_le_of_forall {B : ℕ} :
    ∀ {l : List ℕ}, (∀ a ∈ l, a ≤ B) → l.foldr max 0 ≤ B
  | [], _ => Nat.zero_le B
  | x :: _xs, h =>
    max_le (h x List.mem_cons_self)
      (foldr_max_le_of_forall fun a ha => h a (List.mem_cons_of_mem x ha))

lemma natLog2_mul_add_one_le {k d N : ℕ} (hk : k ≤ 2 ^ d * N) (hN : 1 ≤ N) :
    (Nat.log 2 k : ℝ) + 1 ≤ (d + 2 : ℝ) * (1 + Real.log (N : ℝ)) := by
  have hlogN_nn : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  by_cases hk0 : k = 0
  · subst hk0
    simp only [Nat.log_zero_right, CharP.cast_eq_zero, zero_add]
    nlinarith
  · have hlt : k < 2 ^ (d + Nat.log 2 N + 1) := by
      have h1 : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by omega) N
      have h2 : 2 ^ d * N < 2 ^ d * 2 ^ (Nat.log 2 N + 1) :=
        Nat.mul_lt_mul_of_pos_left h1 (pow_pos (by omega) d)
      rw [← pow_add, ← Nat.add_assoc] at h2
      exact lt_of_le_of_lt hk h2
    have hlogk : Nat.log 2 k ≤ d + Nat.log 2 N :=
      Nat.le_of_lt_succ ((Nat.log_lt_iff_lt_pow (by omega) hk0).mpr hlt)
    have hpowN : ((2 : ℝ) ^ Nat.log 2 N) ≤ (N : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : N ≠ 0)
    have hlog_pow : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log (N : ℝ) := by
      have h1 := Real.log_le_log (by positivity) hpowN
      rwa [Real.log_pow] at h1
    have hlog2 : (0.5 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hlogN_nat : (Nat.log 2 N : ℝ) ≤ 2 * Real.log (N : ℝ) := by nlinarith
    have hcast : (Nat.log 2 k : ℝ) ≤ (d : ℝ) + (Nat.log 2 N : ℝ) := by
      exact_mod_cast hlogk
    nlinarith

lemma collectRawEsFun_idEmb_length :
    ∀ l : List ℕ, (collectRawEsFun l idEmb).length = l.length
  | [] => rfl
  | _ :: xs => by
    have _ := collectRawEsFun_idEmb_length xs
    simp [collectRawEsFun, idEmb]

lemma idEmb_length_le_one (G : MGraph) : idEmb.length G ≤ 1 := by
  unfold MinCostFlow.Embedding.length
  exact Finset.sup_le fun e _ => by simp [idEmb]

lemma usedHVerts_active_idEmb (G : MGraph) (hG : G.IsValid) :
    usedHVerts (activeSubgraph G) (activeSubgraph G) idEmb = (activeSubgraph G).V := by
  have hact := activeSubgraph_isValid hG
  apply Finset.Subset.antisymm _ Finset.subset_union_left
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · exact hv
  · rcases Finset.mem_biUnion.mp hv with ⟨e, he, hvw⟩
    have hwalk : (activeSubgraph G).walkVertices ((activeSubgraph G).tail e) (idEmb e) =
        [(activeSubgraph G).tail e, (activeSubgraph G).head e] := by
      simp [idEmb, MGraph.walkVertices, MGraph.dst]
    rw [hwalk] at hvw
    rcases by simpa using hvw with rfl | rfl
    · exact (hact e he).1
    · exact (hact e he).2

lemma usedHEdges_active_idEmb (G : MGraph) :
    usedHEdges (activeSubgraph G) idEmb = (activeSubgraph G).E := by
  ext e
  simp [usedHEdges, idEmb, walkEdges]

lemma toCitedH_active_idEmb_n (G : MGraph) (hG : G.IsValid) :
    (toCitedH (activeSubgraph G) (activeSubgraph G) idEmb).n = (activeSubgraph G).n := by
  simp [toCitedH, hVerts, usedHVerts_active_idEmb G hG, vertsOf, MGraph.n]

lemma toCitedH_active_idEmb_m (G : MGraph) :
    (toCitedH (activeSubgraph G) (activeSubgraph G) idEmb).m = G.m := by
  have hactE : (activeSubgraph G).E = G.E := rfl
  simp [Cited.Graph.m, toCitedH, hEdges, usedHEdges_active_idEmb G, vertsOf, MGraph.m, hactE]

private lemma embToCited_active_idEmb_eq {G : MGraph} (hG : G.IsValid) (j : ℕ) :
    let Gact := activeSubgraph G
    let e := (vertsOf Gact.E).getD j 0
    embToCited Gact Gact idEmb j =
      { verts := [(vertsOf Gact.V).idxOf (Gact.tail e), (vertsOf Gact.V).idxOf (Gact.head e)]
        edges := [(vertsOf Gact.E).idxOf e] } := by
  intro Gact e
  have hvs : hVerts Gact Gact idEmb = vertsOf Gact.V := by
    dsimp only [hVerts, Gact]
    rw [usedHVerts_active_idEmb G hG]
    simp [vertsOf]
  have hes : hEdges Gact idEmb = vertsOf Gact.E := by
    dsimp only [hEdges, Gact]
    rw [usedHEdges_active_idEmb]
  dsimp only [embToCited]
  rw [hvs, hes]
  simp [walkToCited, idEmb, MGraph.walkVertices, MGraph.dst, e]

theorem canonSparsifyInput_id_len (G : MGraph) (hG : G.IsValid) :
    (canonSparsifyInput (activeSubgraph G) (activeSubgraph G) idEmb).length = 7 + 10 * G.m := by
  set Gact := activeSubgraph G
  rw [canonSparsifyInput_length, toCitedH_active_idEmb_m G]
  have hGm : Gact.m = G.m := rfl
  have hflat : (((List.range Gact.m).map (embToCited Gact Gact idEmb)).flatMap Walk.encode).length =
      5 * G.m := by
    have hgen : ∀ n : ℕ,
        (((List.range n).map (embToCited Gact Gact idEmb)).flatMap Walk.encode).length = 5 * n := by
      intro n
      induction n with
      | zero => simp
      | succ k ih =>
        rw [List.range_succ, List.map_append, List.map_singleton, List.flatMap_append,
          List.flatMap_singleton, List.length_append, ih, embToCited_active_idEmb_eq hG k,
          walk_encode_length]
        simp only [List.length_cons, List.length_nil]
        omega
    simpa [hGm] using hgen Gact.m
  rw [hflat, hGm]
  omega

private lemma mem_canonWalkOffsets_le {a base : ℕ} :
    ∀ {ws : List Walk}, a ∈ canonWalkOffsets base ws →
      a ≤ base + (ws.flatMap Walk.encode).length
  | [], ha => by simp [canonWalkOffsets] at ha
  | w :: ws, ha => by
    simp only [canonWalkOffsets, List.mem_cons] at ha
    rcases ha with rfl | hrest
    · exact Nat.le_add_right _ _
    · have ih := mem_canonWalkOffsets_le hrest
      simp only [List.flatMap_cons, List.length_append]
      omega

theorem canonSparsifyInput_id_max (G : MGraph) (hG : G.IsValid) :
    (canonSparsifyInput (activeSubgraph G) (activeSubgraph G) idEmb).foldr max 0 ≤
      (activeSubgraph G).n + 10 * G.m + 7 := by
  set Gact := activeSubgraph G
  have hact := activeSubgraph_isValid hG
  have hactE : Gact.E = G.E := rfl
  refine foldr_max_le_of_forall fun a ha => ?_
  dsimp only [canonSparsifyInput] at ha
  simp only [List.mem_append] at ha
  have hcHn : (toCitedH Gact Gact idEmb).n = Gact.n := toCitedH_active_idEmb_n G hG
  have hcHm : (toCitedH Gact Gact idEmb).m = G.m := toCitedH_active_idEmb_m G
  have hcJn : (toCitedJ Gact).n = Gact.n := by simp [toCitedJ, vertsOf, MGraph.n]
  have hcJm : (toCitedJ Gact).m = G.m := by
    simp [Cited.Graph.m, toCitedJ, vertsOf, Gact, MGraph.m, hactE]
  have hV_len : (vertsOf Gact.V).length = Gact.n := by simp [vertsOf, MGraph.n]
  have hidx_v : ∀ v ∈ Gact.V, (vertsOf Gact.V).idxOf v < Gact.n := fun v hv => by
    have h1 := List.idxOf_lt_length_of_mem ((Finset.mem_sort (· ≤ ·)).mpr hv)
    simpa [vertsOf, MGraph.n] using h1
  have hvs : hVerts Gact Gact idEmb = vertsOf Gact.V := by
    dsimp only [hVerts, Gact]
    rw [usedHVerts_active_idEmb G hG]
    simp [vertsOf]
  have hes : hEdges Gact idEmb = vertsOf Gact.E := by
    dsimp only [hEdges, Gact]
    rw [usedHEdges_active_idEmb]
  have hcH_mem : ∀ z ∈ (toCitedH Gact Gact idEmb).encode, z ≤ Gact.n + 10 * G.m + 7 := by
    intro z hz
    simp only [Cited.Graph.encode, List.mem_cons, List.mem_flatMap] at hz
    rcases hz with rfl | rfl | ⟨ePair, hePair, hzPair⟩
    · rw [hcHn]; omega
    · rw [hcHm]; omega
    · simp only [toCitedH, hvs, hes, List.mem_map] at hePair
      rcases hePair with ⟨e, heL, rfl⟩
      have heE : e ∈ Gact.E := (Finset.mem_sort _).mp heL
      simp only [List.not_mem_nil, or_false] at hzPair
      rcases hzPair with rfl | rfl
      · have h1 := hidx_v _ (hact e heE).1; dsimp only [Gact] at *; omega
      · have h1 := hidx_v _ (hact e heE).2; dsimp only [Gact] at *; omega
  have hcJ_mem : ∀ z ∈ (toCitedJ Gact).encode, z ≤ Gact.n + 10 * G.m + 7 := by
    intro z hz
    simp only [Cited.Graph.encode, List.mem_cons, List.mem_flatMap] at hz
    rcases hz with rfl | rfl | ⟨ePair, hePair, hzPair⟩
    · rw [hcJn]; omega
    · rw [hcJm]; omega
    · simp only [toCitedJ, List.mem_map] at hePair
      rcases hePair with ⟨e, heL, rfl⟩
      have heE : e ∈ Gact.E := (Finset.mem_sort _).mp heL
      simp only [List.not_mem_nil, or_false] at hzPair
      rcases hzPair with rfl | rfl
      · have h1 := hidx_v _ (hact e heE).1; dsimp only [Gact] at *; omega
      · have h1 := hidx_v _ (hact e heE).2; dsimp only [Gact] at *; omega
  rcases ha with (((ha | ha) | ha) | ha) | ha
  · simp only [List.mem_cons, List.not_mem_nil, or_false, graph_encode_length, hcHm, hcJm] at ha
    rcases ha with rfl | rfl | rfl <;> omega
  · exact hcH_mem a ha
  · exact hcJ_mem a ha
  · have hlen := canonSparsifyInput_id_len G hG
    rw [canonSparsifyInput_length] at hlen
    rw [graph_encode_length, graph_encode_length, hcHm, hcJm] at ha
    have hsum_len : (3 + (2 + 2 * G.m) + (2 + 2 * G.m) + G.m) +
        (((List.range G.m).map (embToCited Gact Gact idEmb)).flatMap Walk.encode).length =
        7 + 10 * G.m := by
      have hm1 : (toCitedH Gact Gact idEmb).m = G.m := hcHm
      have hm2 : Gact.m = G.m := rfl
      rw [hm1, hm2] at hlen
      omega
    exact le_trans (mem_canonWalkOffsets_le ha) (by omega)
  · simp only [List.mem_flatMap, List.mem_map, List.mem_range] at ha
    rcases ha with ⟨w, ⟨j, hj, rfl⟩, hza⟩
    have hj' : j < G.m := by simpa [hcJm] using hj
    rw [embToCited_active_idEmb_eq hG j] at hza
    have hE_len : (vertsOf Gact.E).length = G.m := by simp [vertsOf, Gact, MGraph.m, hactE]
    set e := (vertsOf Gact.E).getD j 0
    have heE : e ∈ Gact.E := by
      have hget : e = (vertsOf Gact.E)[j]'(hE_len.symm ▸ hj') := List.getD_eq_getElem _ 0 _
      rw [hget]
      exact (Finset.mem_sort _).mp (List.getElem_mem _)
    simp only [Walk.encode, List.length_cons, List.length_nil, List.mem_cons, List.mem_append,
      List.not_mem_nil, or_false] at hza
    rcases hza with (h2 | rfl | rfl) | (h1 | rfl)
    · rw [h2]; omega
    · have h1 := hidx_v _ (hact e heE).1; dsimp only [Gact] at *; omega
    · have h1 := hidx_v _ (hact e heE).2; dsimp only [Gact] at *; omega
    · rw [h1]; omega
    · have h1 := List.idxOf_lt_length_of_mem ((Finset.mem_sort (· ≤ ·)).mpr heE)
      rw [show Gact.E.sort (· ≤ ·) = vertsOf Gact.E from rfl, hE_len] at h1
      dsimp only [Gact] at *
      omega

theorem wordSize_canonSparsifyInput_id_le (cw : ℕ) (G : MGraph) (hG : G.IsValid) :
    wordSize cw (canonSparsifyInput (activeSubgraph G) (activeSubgraph G) idEmb) ≤
      cw * (Nat.log 2 ((activeSubgraph G).n + 20 * G.m + 16) + 1) := by
  unfold wordSize
  refine Nat.mul_le_mul_left cw (Nat.succ_le_succ (Nat.log_mono_right ?_))
  have h1 := canonSparsifyInput_id_len G hG
  have h2 := canonSparsifyInput_id_max G hG
  omega

/-- Constant factor (depending only on `impl`) in the paper-shape initialization cost bound. -/
def dsInitCostFactor (impl : SparsifyImpl) : ℕ :=
  30000 + 840 * impl.cw + 3 * impl.program.regBound

lemma le_dsInitCostFactor (impl : SparsifyImpl) : 30000 ≤ dsInitCostFactor impl := by
  unfold dsInitCostFactor; omega

private lemma dsInitCost_real_combine
    {K γ Λ Λm gn_act gn gm hm l cw R log_arg log_n log_m ws cQ ceil_gl wsum jcard : ℝ}
    (hK : 1 ≤ K) (hγ : 1 ≤ γ) (hΛ : 1 ≤ Λ) (hΛm : Λ ≤ Λm)
    (hga : 0 ≤ gn_act) (hgn : 0 ≤ gn) (hgm : 0 ≤ gm) (hhm : 0 ≤ hm) (hl : 0 ≤ l)
    (hcw : 0 ≤ cw) (hR : 0 ≤ R)
    (hgn_le : gn_act ≤ gn)
    (hLambda_le : Λ ≤ 2 + K * (gn_act + gm * γ ^ 2) * Λm)
    (hlog_arg : log_arg ≤ 4 * Λ) (hlog_n : log_n ≤ 2 * Λ) (hlog_m : log_m ≤ 2 * Λ)
    (hws : ws ≤ cw * (7 * Λ))
    (hcQ : cQ ≤ K * (gn_act + gm * γ ^ 2) * Λm + 1)
    (hceil : ceil_gl ≤ 2 * γ)
    (hwsum : wsum ≤ gm * γ)
    (hjcard : jcard ≤ hm) :
    1430 * (gn_act + gm + gm) * log_arg + 1250 * (gn_act + gm + gm) + 1500 +
        40 * (7 + 10 * gm + ws + 1) + (R + 6) * cQ + R +
        250 * gn_act * log_n + 250 * gm * log_m + 430 * gn_act + 1065 * gm +
        250 * (gm * ceil_gl) + 1200 + 800 * wsum + 170 * gn + 2600 * gm +
        820 * jcard + 1300 + 140 * gn + 500 * gm + 420 ≤
      (30000 + 840 * cw + 3 * R) *
        (K * (gn_act + gm * γ ^ 2) * Λm + gn + gm + hm + gm * γ + l + 1) := by
  have hγ_sq : 1 ≤ γ ^ 2 := one_le_pow₀ hγ
  have hgm_gl_nn : 0 ≤ gm * γ := mul_nonneg hgm (by linarith only [hγ])
  have hgm_gsq_nn : 0 ≤ gm * γ ^ 2 := mul_nonneg hgm (by linarith only [hγ_sq])
  have hΛm_nn : 0 ≤ Λm := by linarith only [hΛ, hΛm]
  have hKterm_nn : 0 ≤ K * (gn_act + gm * γ ^ 2) * Λm :=
    mul_nonneg (mul_nonneg (by linarith only [hK]) (by linarith only [hga, hgm_gsq_nn])) hΛm_nn
  set Φ := K * (gn_act + gm * γ ^ 2) * Λm + gn + gm + hm + gm * γ + l + 1
  have hΦ_K : K * (gn_act + gm * γ ^ 2) * Λm ≤ Φ := by
    dsimp only [Φ]; linarith only [hgn, hgm, hhm, hgm_gl_nn, hl]
  have hΦ_gn : gn ≤ Φ := by dsimp only [Φ]; linarith only [hKterm_nn, hgm, hhm, hgm_gl_nn, hl]
  have hΦ_gm : gm ≤ Φ := by dsimp only [Φ]; linarith only [hKterm_nn, hgn, hhm, hgm_gl_nn, hl]
  have hΦ_hm : hm ≤ Φ := by dsimp only [Φ]; linarith only [hKterm_nn, hgn, hgm, hgm_gl_nn, hl]
  have hΦ_gl : gm * γ ≤ Φ := by dsimp only [Φ]; linarith only [hKterm_nn, hgn, hgm, hhm, hl]
  have hΦ_1 : 1 ≤ Φ := by dsimp only [Φ]; linarith only [hKterm_nn, hgn, hgm, hhm, hgm_gl_nn, hl]
  have hΦ_nn : 0 ≤ Φ := by linarith only [hΦ_1]
  have h_prod_Λ : (gn_act + gm * γ ^ 2) * Λ ≤ K * (gn_act + gm * γ ^ 2) * Λm := by
    have h1 : (gn_act + gm * γ ^ 2) * Λ ≤ (gn_act + gm * γ ^ 2) * Λm :=
      mul_le_mul_of_nonneg_left hΛm (by linarith only [hga, hgm_gsq_nn])
    have h2 : (gn_act + gm * γ ^ 2) * Λm ≤ K * ((gn_act + gm * γ ^ 2) * Λm) :=
      le_mul_of_one_le_left (mul_nonneg (by linarith only [hga, hgm_gsq_nn]) hΛm_nn) hK
    linarith only [h1, h2]
  have hn_Λ : gn_act * Λ ≤ Φ := by
    have h1 : gn_act * Λ ≤ (gn_act + gm * γ ^ 2) * Λ :=
      mul_le_mul_of_nonneg_right (by linarith only [hgm_gsq_nn]) (by linarith only [hΛ])
    linarith only [h1, h_prod_Λ, hΦ_K]
  have hm_Λ : gm * Λ ≤ Φ := by
    have hle : gm ≤ gn_act + gm * γ ^ 2 := by
      have : gm * 1 ≤ gm * γ ^ 2 := mul_le_mul_of_nonneg_left hγ_sq hgm
      linarith only [this, hga]
    have h1 : gm * Λ ≤ (gn_act + gm * γ ^ 2) * Λ :=
      mul_le_mul_of_nonneg_right hle (by linarith only [hΛ])
    linarith only [h1, h_prod_Λ, hΦ_K]
  have h_p1 : 1430 * (gn_act + gm + gm) * log_arg ≤ 11440 * Φ := by
    have h1 : 1430 * (gn_act + gm + gm) * log_arg ≤ 1430 * (gn_act + gm + gm) * (4 * Λ) :=
      mul_le_mul_of_nonneg_left hlog_arg (by linarith only [hga, hgm])
    have h2 : gn_act + gm + gm ≤ 2 * (gn_act + gm * γ ^ 2) := by
      have : gm ≤ gm * γ ^ 2 := le_mul_of_one_le_right hgm hγ_sq
      linarith only [hga, this]
    have h3 : (gn_act + gm + gm) * Λ ≤ 2 * ((gn_act + gm * γ ^ 2) * Λ) := by
      have := mul_le_mul_of_nonneg_right h2 (by linarith only [hΛ])
      linarith only [this]
    have h4 : 1430 * (gn_act + gm + gm) * (4 * Λ) = 5720 * ((gn_act + gm + gm) * Λ) := by ring
    linarith only [h1, h3, h4, h_prod_Λ, hΦ_K]
  have h_p2 : 40 * (7 + 10 * gm + ws + 1) ≤ 720 * Φ + 840 * cw * Φ := by
    have hws' : 40 * ws ≤ 280 * cw * Λ := by
      have := mul_le_mul_of_nonneg_left hws (by norm_num : (0 : ℝ) ≤ 40)
      linarith only [this]
    have hΛ' : 280 * cw * Λ ≤ 840 * cw * Φ := by
      have h3 : Λ ≤ 3 * Φ := by linarith only [hLambda_le, hΦ_K, hΦ_1]
      have := mul_le_mul_of_nonneg_left h3 (by linarith only [hcw] : 0 ≤ 280 * cw)
      linarith only [this]
    linarith only [hws', hΛ', hΦ_gm, hΦ_1]
  have h_p3 : (R + 6) * cQ ≤ 12 * Φ + 2 * R * Φ := by
    have h1 : (R + 6) * cQ ≤ (R + 6) * (K * (gn_act + gm * γ ^ 2) * Λm + 1) :=
      mul_le_mul_of_nonneg_left hcQ (by linarith only [hR])
    have h2 : (R + 6) * (K * (gn_act + gm * γ ^ 2) * Λm + 1) ≤ (R + 6) * (2 * Φ) :=
      mul_le_mul_of_nonneg_left (by linarith only [hΦ_K, hΦ_1]) (by linarith only [hR])
    linarith only [h1, h2]
  have h_p4 : 250 * gn_act * log_n + 250 * gm * log_m ≤ 1000 * Φ := by
    have h1 : 250 * gn_act * log_n ≤ 250 * gn_act * (2 * Λ) :=
      mul_le_mul_of_nonneg_left hlog_n (by linarith only [hga])
    have h2 : 250 * gm * log_m ≤ 250 * gm * (2 * Λ) :=
      mul_le_mul_of_nonneg_left hlog_m (by linarith only [hgm])
    linarith only [h1, h2, hn_Λ, hm_Λ]
  have h_p5 : 250 * (gm * ceil_gl) ≤ 500 * Φ := by
    have h1 : gm * ceil_gl ≤ gm * (2 * γ) := mul_le_mul_of_nonneg_left hceil hgm
    linarith only [h1, hΦ_gl]
  have h_R_le : R ≤ R * Φ := le_mul_of_one_le_right hR hΦ_1
  have h_rest : 1250 * (gn_act + gm + gm) + 1500 + R + 430 * gn_act + 1065 * gm + 1200 +
      800 * wsum + 170 * gn + 2600 * gm + 820 * jcard + 1300 + 140 * gn + 500 * gm + 420 ≤
      15000 * Φ + R * Φ := by
    linarith only [hgn_le, hwsum, hjcard, hΦ_gn, hΦ_gm, hΦ_hm, hΦ_gl, hΦ_1, h_R_le]
  change _ ≤ (30000 + 840 * cw + 3 * R) * Φ
  linarith only [h_p1, h_p2, h_p3, h_p4, h_p5, h_rest, hΦ_nn]

lemma dsInitCore_initCostBound (impl : SparsifyImpl) (mMax L q : ℕ) {G : MGraph}
    (hG : G.IsValid) (hGm : G.m ≤ mMax) :
    let P := canonicalSparsifyParams impl mMax
    let initOut := init G L q (canonicalSparsify impl)
    ((dsInitCoreCost impl mMax G + 140 * G.n + 500 * G.m + 420 : ℕ) : ℝ) ≤
      (dsInitCostFactor impl : ℝ) *
        (P.K_t * P.γ_t * (((activeSubgraph G).n : ℝ) + (G.m : ℝ) * P.γ_ℓ ^ 2) *
            (1 + Real.log (((activeSubgraph G).n : ℝ) + (G.m : ℝ) + 2)) ^ max P.p_t 1 +
          (G.n : ℝ) + (G.m : ℝ) + (initOut.state.H.m : ℝ) + (G.m : ℝ) * P.γ_ℓ + (L : ℝ) + 1) := by
  intro P initOut
  set Gact := activeSubgraph G
  set out := canonicalSparsify impl Gact Gact idEmb
  have hGm_act : Gact.m = G.m := rfl
  have hPg : P.γ_ℓ = impl.γ_ℓ mMax := rfl
  have hPK : P.K_t = 2 * impl.K_t + 1 := rfl
  have hPgt : P.γ_t = impl.γ_t mMax := rfl
  have hK1 : 1 ≤ P.K_t * P.γ_t := by
    rw [hPK, hPgt]
    exact one_le_mul_of_one_le_of_one_le (by linarith only [impl.hK_t]) (impl.hγ_t mMax)
  by_cases hGm0 : G.m = 0
  case pos =>
    have hGE : G.E = ∅ := Finset.card_eq_zero.mp hGm0
    have hSpec0 := canonicalSparsify_spec_with_time impl mMax Gact Gact idEmb
      (activeSubgraph_isValid hG) (activeSubgraph_isValid hG) hGm
      (fun hE => by rw [idEmb_length_eq_one hE]) (idEmb_isEmbedding Gact)
    have hJt0 : out.Jtilde.E = ∅ := by
      have hsub : out.Jtilde.E ⊆ Gact.E := hSpec0.1.2.1
      have hGactE : Gact.E = ∅ := hGE
      rw [hGactE, Finset.subset_empty] at hsub; exact hsub
    have hLHS : ((dsInitCoreCost impl mMax G + 140 * G.n + 500 * G.m + 420 : ℕ) : ℝ) =
        310 * (G.n : ℝ) + 1720 := by
      dsimp only [out, Gact] at hJt0
      dsimp only [dsInitCoreCost]
      simp only [hGm0, ↓reduceIte, hGE, hJt0, Finset.sum_empty, Finset.card_empty, Nat.mul_zero,
        Nat.add_zero, zero_add]
      push_cast; ring
    have hN1 : (1 : ℝ) ≤ (Gact.n : ℝ) + (G.m : ℝ) + 2 := by
      linarith [Nat.cast_nonneg (α := ℝ) Gact.n, Nat.cast_nonneg (α := ℝ) G.m]
    have hΛ_nn : 0 ≤ (1 + Real.log ((Gact.n : ℝ) + (G.m : ℝ) + 2)) ^ max P.p_t 1 :=
      pow_nonneg (by linarith [Real.log_nonneg hN1]) _
    have hPterm_nn : 0 ≤ P.K_t * P.γ_t * ((Gact.n : ℝ) + (G.m : ℝ) * P.γ_ℓ ^ 2) *
        (1 + Real.log ((Gact.n : ℝ) + (G.m : ℝ) + 2)) ^ max P.p_t 1 :=
      mul_nonneg (mul_nonneg (by linarith only [hK1])
        (add_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))) hΛ_nn
    have hfac_ge : (30000 : ℝ) ≤ (dsInitCostFactor impl : ℝ) := by
      unfold dsInitCostFactor; push_cast
      linarith [Nat.cast_nonneg (α := ℝ) impl.cw, Nat.cast_nonneg (α := ℝ) impl.program.regBound]
    have hinner : (G.n : ℝ) + 1 ≤
        P.K_t * P.γ_t * ((Gact.n : ℝ) + (G.m : ℝ) * P.γ_ℓ ^ 2) *
          (1 + Real.log ((Gact.n : ℝ) + (G.m : ℝ) + 2)) ^ max P.p_t 1 +
        (G.n : ℝ) + (G.m : ℝ) + (initOut.state.H.m : ℝ) + (G.m : ℝ) * P.γ_ℓ + (L : ℝ) + 1 := by
      have hgm_gl : 0 ≤ (G.m : ℝ) * P.γ_ℓ :=
        mul_nonneg (Nat.cast_nonneg _) (le_trans zero_le_one (impl.hγ_ℓ mMax))
      linarith [hPterm_nn, hgm_gl, Nat.cast_nonneg (α := ℝ) G.m,
        Nat.cast_nonneg (α := ℝ) initOut.state.H.m, Nat.cast_nonneg (α := ℝ) L]
    rw [hLHS]
    have hgn_nn : (0 : ℝ) ≤ (G.n : ℝ) := Nat.cast_nonneg _
    nlinarith only [hfac_ge, hinner, hgn_nn]
  have hN1 : 1 ≤ Gact.n + G.m + 2 := by omega
  have hΛ_ge1 : (1 : ℝ) ≤ 1 + Real.log ((Gact.n + G.m + 2 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((Gact.n + G.m + 2 : ℕ) : ℝ) := by exact_mod_cast hN1
    linarith only [Real.log_nonneg this]
  have hΛm_ge : 1 + Real.log ((Gact.n + G.m + 2 : ℕ) : ℝ) ≤
      (1 + Real.log ((Gact.n + G.m + 2 : ℕ) : ℝ)) ^ max P.p_t 1 :=
    le_self_pow₀ hΛ_ge1 (by omega)
  have hLambda_le : 1 + Real.log ((Gact.n + G.m + 2 : ℕ) : ℝ) ≤
      2 + (P.K_t * P.γ_t) * ((Gact.n : ℝ) + (G.m : ℝ) * P.γ_ℓ ^ 2) *
        (1 + Real.log ((Gact.n + G.m + 2 : ℕ) : ℝ)) ^ max P.p_t 1 := by
    have hg1 : 1 ≤ P.γ_ℓ := impl.hγ_ℓ mMax
    have hγsq : 1 ≤ P.γ_ℓ ^ 2 := one_le_pow₀ hg1
    by_cases hzm : Gact.n + G.m = 0
    · have hN2 : Gact.n + G.m + 2 = 2 := by omega
      rw [hN2]
      have h1 : 1 + Real.log ((2 : ℕ) : ℝ) ≤ 2 := by
        push_cast; linarith only [Real.log_two_lt_d9]
      have hΛm_nn : 0 ≤ (1 + Real.log ((2 : ℕ) : ℝ)) ^ max P.p_t 1 := by
        have hΛ2 : 1 ≤ 1 + Real.log ((2 : ℕ) : ℝ) := by push_cast; linarith only [Real.log_two_gt_d9]
        exact pow_nonneg (by linarith only [hΛ2]) _
      have hgm_nn : 0 ≤ (G.m : ℝ) * P.γ_ℓ ^ 2 :=
        mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
      have h2 : 0 ≤ (P.K_t * P.γ_t) * ((Gact.n : ℝ) + (G.m : ℝ) * P.γ_ℓ ^ 2) *
          (1 + Real.log ((2 : ℕ) : ℝ)) ^ max P.p_t 1 :=
        mul_nonneg (mul_nonneg (by linarith only [hK1])
          (add_nonneg (Nat.cast_nonneg _) hgm_nn)) hΛm_nn
      linarith only [h1, h2]
    · have hpos : (1 : ℝ) ≤ (Gact.n : ℝ) + (G.m : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hzm
      have hm_le : (G.m : ℝ) ≤ (G.m : ℝ) * P.γ_ℓ ^ 2 :=
        le_mul_of_one_le_right (Nat.cast_nonneg _) hγsq
      have hquad : 1 ≤ (Gact.n : ℝ) + (G.m : ℝ) * P.γ_ℓ ^ 2 := by linarith only [hpos, hm_le]
      have hΛm_ge1 : 1 ≤ (1 + Real.log ((Gact.n + G.m + 2 : ℕ) : ℝ)) ^ max P.p_t 1 :=
        le_trans hΛ_ge1 hΛm_ge
      have h1 : 1 + Real.log ((Gact.n + G.m + 2 : ℕ) : ℝ) ≤
          ((Gact.n : ℝ) + (G.m : ℝ) * P.γ_ℓ ^ 2) *
            (1 + Real.log ((Gact.n + G.m + 2 : ℕ) : ℝ)) ^ max P.p_t 1 := by
        calc 1 + Real.log ((Gact.n + G.m + 2 : ℕ) : ℝ)
            ≤ (1 + Real.log ((Gact.n + G.m + 2 : ℕ) : ℝ)) ^ max P.p_t 1 := hΛm_ge
          _ ≤ ((Gact.n : ℝ) + (G.m : ℝ) * P.γ_ℓ ^ 2) *
                (1 + Real.log ((Gact.n + G.m + 2 : ℕ) : ℝ)) ^ max P.p_t 1 :=
              le_mul_of_one_le_left (by linarith only [hΛm_ge1]) hquad
      have h2 : ((Gact.n : ℝ) + (G.m : ℝ) * P.γ_ℓ ^ 2) *
            (1 + Real.log ((Gact.n + G.m + 2 : ℕ) : ℝ)) ^ max P.p_t 1 ≤
          (P.K_t * P.γ_t) * (((Gact.n : ℝ) + (G.m : ℝ) * P.γ_ℓ ^ 2) *
            (1 + Real.log ((Gact.n + G.m + 2 : ℕ) : ℝ)) ^ max P.p_t 1) :=
        le_mul_of_one_le_left (by linarith only [hΛ_ge1, h1]) hK1
      linarith only [h1, h2]
  have hraw : (collectRawEsFun (vertsOf Gact.E) idEmb).length = G.m := by
    have hactE : Gact.E = G.E := rfl
    rw [collectRawEsFun_idEmb_length]
    simp [vertsOf, Gact, MGraph.m, hactE]
  have hlog_arg : (Nat.log 2 (Gact.n + 2 * G.m + G.m + 2) : ℝ) + 1 ≤
      4 * (1 + Real.log ((Gact.n + G.m + 2 : ℕ) : ℝ)) := by
    have := natLog2_mul_add_one_le (k := Gact.n + 2 * G.m + G.m + 2) (d := 2)
      (N := Gact.n + G.m + 2) (by omega) hN1
    norm_num at this ⊢
    exact this
  have hlog_n : (Nat.log 2 (Gact.n + 1) : ℝ) + 1 ≤
      2 * (1 + Real.log ((Gact.n + G.m + 2 : ℕ) : ℝ)) := by
    have := natLog2_mul_add_one_le (k := Gact.n + 1) (d := 0) (N := Gact.n + G.m + 2) (by omega) hN1
    norm_num at this ⊢
    exact this
  have hlog_m : (Nat.log 2 (G.m + 1) : ℝ) + 1 ≤
      2 * (1 + Real.log ((Gact.n + G.m + 2 : ℕ) : ℝ)) := by
    have := natLog2_mul_add_one_le (k := G.m + 1) (d := 0) (N := Gact.n + G.m + 2) (by omega) hN1
    norm_num at this ⊢
    exact this
  have hws_r : (wordSize impl.cw (canonSparsifyInput Gact Gact idEmb) : ℝ) ≤
      (impl.cw : ℝ) * (7 * (1 + Real.log ((Gact.n + G.m + 2 : ℕ) : ℝ))) := by
    have hws_nat := wordSize_canonSparsifyInput_id_le impl.cw G hG
    have hlog_ws : (Nat.log 2 (Gact.n + 20 * G.m + 16) : ℝ) + 1 ≤
        7 * (1 + Real.log ((Gact.n + G.m + 2 : ℕ) : ℝ)) := by
      have := natLog2_mul_add_one_le (k := Gact.n + 20 * G.m + 16) (d := 5)
        (N := Gact.n + G.m + 2) (by omega) hN1
      norm_num at this ⊢
      exact this
    have h1 : (wordSize impl.cw (canonSparsifyInput Gact Gact idEmb) : ℝ) ≤
        (impl.cw : ℝ) * ((Nat.log 2 (Gact.n + 20 * G.m + 16) : ℝ) + 1) := by
      exact_mod_cast hws_nat
    exact le_trans h1 (mul_le_mul_of_nonneg_left hlog_ws (Nat.cast_nonneg _))
  have hcQ_r : (⌈impl.K_t * (impl.γ_t mMax) *
      (1 + (Gact.n : ℝ) + (G.m : ℝ) * (impl.γ_ℓ mMax) ^ 2 * (idEmb.length Gact : ℝ)) *
      (1 + Real.log ((Gact.n : ℝ) + (G.m : ℝ) + 2)) ^ impl.p_t⌉₊ : ℝ) ≤
      (P.K_t * P.γ_t) * ((Gact.n : ℝ) + (G.m : ℝ) * P.γ_ℓ ^ 2) *
        (1 + Real.log ((Gact.n + G.m + 2 : ℕ) : ℝ)) ^ max P.p_t 1 + 1 := by
    have hK_nn : 0 ≤ impl.K_t := impl.hK_t
    have hgt_nn : 0 ≤ impl.γ_t mMax := le_trans zero_le_one (impl.hγ_t mMax)
    have hGm_r : (Gact.m : ℝ) = (G.m : ℝ) := rfl
    have hN_cast : ((Gact.n + G.m + 2 : ℕ) : ℝ) = (Gact.n : ℝ) + (G.m : ℝ) + 2 := by
      push_cast; ring
    have hid1 : (idEmb.length Gact : ℝ) ≤ 1 := by exact_mod_cast idEmb_length_le_one Gact
    have hGm_ge1 : (1 : ℝ) ≤ (G.m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hGm0
    have hγsq : 1 ≤ P.γ_ℓ ^ 2 := one_le_pow₀ (impl.hγ_ℓ mMax)
    have h1_le_term : (1 : ℝ) ≤ (Gact.n : ℝ) + (G.m : ℝ) * P.γ_ℓ ^ 2 := by
      have h1 : (G.m : ℝ) ≤ (G.m : ℝ) * P.γ_ℓ ^ 2 :=
        le_mul_of_one_le_right (Nat.cast_nonneg _) hγsq
      linarith [Nat.cast_nonneg (α := ℝ) Gact.n]
    have hm1 : 1 + (Gact.n : ℝ) + (G.m : ℝ) * (impl.γ_ℓ mMax) ^ 2 * (idEmb.length Gact : ℝ) ≤
        2 * ((Gact.n : ℝ) + (G.m : ℝ) * P.γ_ℓ ^ 2) := by
      have h' : (G.m : ℝ) * (impl.γ_ℓ mMax) ^ 2 * (idEmb.length Gact : ℝ) ≤
          (G.m : ℝ) * (impl.γ_ℓ mMax) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hid1 (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
      rw [← hPg] at *
      linarith only [h', h1_le_term]
    have hpow : (1 + Real.log ((Gact.n : ℝ) + (G.m : ℝ) + 2)) ^ impl.p_t ≤
        (1 + Real.log ((Gact.n + G.m + 2 : ℕ) : ℝ)) ^ max P.p_t 1 := by
      rw [← hN_cast]
      exact pow_le_pow_right₀ hΛ_ge1 (le_max_left impl.p_t 1)
    have hnn : 0 ≤ impl.K_t * (impl.γ_t mMax) *
        (1 + (Gact.n : ℝ) + (G.m : ℝ) * (impl.γ_ℓ mMax) ^ 2 * (idEmb.length Gact : ℝ)) *
        (1 + Real.log ((Gact.n : ℝ) + (G.m : ℝ) + 2)) ^ impl.p_t := by
      refine mul_nonneg (mul_nonneg (mul_nonneg hK_nn hgt_nn) ?_) (pow_nonneg ?_ _)
      · linarith [Nat.cast_nonneg (α := ℝ) Gact.n,
          mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) G.m) (sq_nonneg (impl.γ_ℓ mMax)))
            (Nat.cast_nonneg (α := ℝ) (idEmb.length Gact))]
      · rw [← hN_cast]; linarith only [hΛ_ge1]
    have hceil := (Nat.ceil_lt_add_one hnn).le
    have hKle : 2 * impl.K_t * impl.γ_t mMax ≤ P.K_t * P.γ_t := by
      rw [hPK, hPgt]
      exact mul_le_mul_of_nonneg_right (by linarith only) hgt_nn
    have hmul : impl.K_t * (impl.γ_t mMax) *
        (1 + (Gact.n : ℝ) + (G.m : ℝ) * (impl.γ_ℓ mMax) ^ 2 * (idEmb.length Gact : ℝ)) *
        (1 + Real.log ((Gact.n : ℝ) + (G.m : ℝ) + 2)) ^ impl.p_t ≤
        (P.K_t * P.γ_t) * ((Gact.n : ℝ) + (G.m : ℝ) * P.γ_ℓ ^ 2) *
          (1 + Real.log ((Gact.n + G.m + 2 : ℕ) : ℝ)) ^ max P.p_t 1 := by
      have h1 : impl.K_t * (impl.γ_t mMax) *
          (1 + (Gact.n : ℝ) + (G.m : ℝ) * (impl.γ_ℓ mMax) ^ 2 * (idEmb.length Gact : ℝ)) ≤
          (P.K_t * P.γ_t) * ((Gact.n : ℝ) + (G.m : ℝ) * P.γ_ℓ ^ 2) := by
        have ha := mul_le_mul_of_nonneg_left hm1 (mul_nonneg hK_nn hgt_nn)
        have hb := mul_le_mul_of_nonneg_right hKle
          (show (0 : ℝ) ≤ (Gact.n : ℝ) + (G.m : ℝ) * P.γ_ℓ ^ 2 by linarith only [h1_le_term])
        linarith only [ha, hb]
      refine mul_le_mul h1 hpow (pow_nonneg ?_ _) ?_
      · rw [← hN_cast]; linarith only [hΛ_ge1]
      · refine mul_nonneg (mul_nonneg (by rw [hPK]; linarith only [hK_nn]) hgt_nn)
          (by linarith only [h1_le_term])
    linarith only [hceil, hmul]
  have hSpec := canonicalSparsify_spec_with_time impl mMax Gact Gact idEmb
    (activeSubgraph_isValid hG) (activeSubgraph_isValid hG) hGm
    (fun hE => by rw [idEmb_length_eq_one hE]) (idEmb_isEmbedding Gact)
  dsimp only at hSpec
  have hJt_card : (out.Jtilde.E.card : ℝ) ≤ (initOut.state.H.m : ℝ) := by
    by_cases hE : G.E.Nonempty
    · have heq : initOut.state.H.m = out.Jtilde.E.card := by
        simp [initOut, init, initAt, initCore, hE, MGraph.m, out, Gact]
      rw [heq]
    · rw [Finset.not_nonempty_iff_eq_empty] at hE
      have hsub : out.Jtilde.E ⊆ Gact.E := hSpec.1.2.1
      have hGactE : Gact.E = ∅ := hE
      rw [hGactE, Finset.subset_empty] at hsub
      simp [hsub]
  have hwalkSum : (∑ e ∈ G.E, ((out.emb e).length : ℝ)) ≤ (G.m : ℝ) * P.γ_ℓ := by
    by_cases hE : G.E.Nonempty
    · have hlen1 : idEmb.length Gact = 1 := idEmb_length_eq_one hE
      have hL := hSpec.2.2.2.1
      rw [idEmb_comp, hlen1, Nat.cast_one, mul_one] at hL
      have hterm : ∀ e ∈ G.E, ((out.emb e).length : ℝ) ≤ P.γ_ℓ := fun e he =>
        le_trans (Nat.cast_le.mpr (Finset.le_sup (f := fun e => (out.emb e).length) he)) hL
      calc ∑ e ∈ G.E, ((out.emb e).length : ℝ)
          ≤ ∑ _ ∈ G.E, P.γ_ℓ := Finset.sum_le_sum hterm
        _ = (G.m : ℝ) * P.γ_ℓ := by rw [Finset.sum_const, nsmul_eq_mul]; rfl
    · rw [Finset.not_nonempty_iff_eq_empty] at hE
      simp [hE, MGraph.m]
  have hceil_gl : (Nat.ceil (impl.γ_ℓ mMax) : ℝ) ≤ 2 * P.γ_ℓ := by
    have hc := (Nat.ceil_lt_add_one (by linarith only [impl.hγ_ℓ mMax] : 0 ≤ impl.γ_ℓ mMax)).le
    linarith only [hc, impl.hγ_ℓ mMax, hPg]
  have hclen : ((canonSparsifyInput Gact Gact idEmb).length : ℝ) = 7 + 10 * (G.m : ℝ) := by
    exact_mod_cast canonSparsifyInput_id_len G hG
  have hN_cast : ((Gact.n + G.m + 2 : ℕ) : ℝ) = (Gact.n : ℝ) + (G.m : ℝ) + 2 := by
    push_cast; ring
  have hcomb := dsInitCost_real_combine
    (K := P.K_t * P.γ_t) (γ := P.γ_ℓ)
    (Λ := 1 + Real.log ((Gact.n + G.m + 2 : ℕ) : ℝ))
    (Λm := (1 + Real.log ((Gact.n + G.m + 2 : ℕ) : ℝ)) ^ max P.p_t 1)
    (gn_act := Gact.n) (gn := G.n) (gm := G.m) (hm := initOut.state.H.m) (l := L)
    (cw := impl.cw) (R := impl.program.regBound)
    (log_arg := (Nat.log 2 (Gact.n + 2 * G.m + G.m + 2) : ℝ) + 1)
    (log_n := (Nat.log 2 (Gact.n + 1) : ℝ) + 1)
    (log_m := (Nat.log 2 (G.m + 1) : ℝ) + 1)
    (ws := wordSize impl.cw (canonSparsifyInput Gact Gact idEmb))
    (cQ := (Nat.ceil (impl.K_t * (impl.γ_t mMax) *
      (1 + (Gact.n : ℝ) + (G.m : ℝ) * (impl.γ_ℓ mMax) ^ 2 * (idEmb.length Gact : ℝ)) *
      (1 + Real.log ((Gact.n : ℝ) + (G.m : ℝ) + 2)) ^ impl.p_t) : ℕ))
    (ceil_gl := Nat.ceil (impl.γ_ℓ mMax))
    (wsum := ∑ e ∈ G.E, ((out.emb e).length : ℝ))
    (jcard := out.Jtilde.E.card)
    hK1 (impl.hγ_ℓ mMax) hΛ_ge1 hΛm_ge
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_le.mpr (activeSubgraph_n_le G)) hLambda_le
    hlog_arg hlog_n hlog_m hws_r hcQ_r hceil_gl hwalkSum hJt_card
  have hfactor : (dsInitCostFactor impl : ℝ) =
      30000 + 840 * (impl.cw : ℝ) + 3 * (impl.program.regBound : ℝ) := by
    unfold dsInitCostFactor; push_cast; ring
  dsimp only [Gact, out] at hcomb hN_cast
  rw [hN_cast] at hcomb
  dsimp only [dsInitCoreCost, sparsifyDynCost, sparsifyDynContract]
  simp only [hGm0, ↓reduceIte]
  rw [hraw, hGm_act, hfactor]
  push_cast
  rw [hclen]
  exact hcomb

theorem dsInit_initCostBound (impl : SparsifyImpl) (mMax w L q vCap eCap : ℕ)
    (G : MGraph) (vL : List ℕ) (eEdges : List (ℕ × ℕ × ℕ))
    (args : List ℕ) (mem : ℕ → ℕ) (hG : G.IsValid) (hGm : G.m ≤ mMax) :
    let P := canonicalSparsifyParams impl mMax
    let initOut := init G L q (canonicalSparsify impl)
    ((dsInitContract impl mMax w L q vCap eCap G vL eEdges).cost args mem : ℝ) ≤
      (dsInitCostFactor impl : ℝ) *
        (P.K_t * P.γ_t * (((activeSubgraph G).n : ℝ) + (G.m : ℝ) * P.γ_ℓ ^ 2) *
            (1 + Real.log (((activeSubgraph G).n : ℝ) + (G.m : ℝ) + 2)) ^ max P.p_t 1 +
          (G.n : ℝ) + (G.m : ℝ) + (initOut.state.H.m : ℝ) + (G.m : ℝ) * P.γ_ℓ + (L : ℝ) + 1) :=
  dsInitCore_initCostBound impl mMax L q hG hGm

theorem dsInitAt_initCostBound (impl : SparsifyImpl) (mMax w L q t vCap eCap b : ℕ)
    (G : MGraph) (vL : List ℕ) (eEdges : List (ℕ × ℕ × ℕ))
    (args : List ℕ) (mem : ℕ → ℕ) (hG : G.IsValid) (hGm : G.m ≤ mMax) :
    let P := canonicalSparsifyParams impl mMax
    let initOut := initAt G L q t (canonicalSparsify impl)
    ((dsInitAtContract impl mMax w L q t vCap eCap b G vL eEdges).cost args mem : ℝ) ≤
      (dsInitCostFactor impl : ℝ) *
        (P.K_t * P.γ_t * (((activeSubgraph G).n : ℝ) + (G.m : ℝ) * P.γ_ℓ ^ 2) *
            (1 + Real.log (((activeSubgraph G).n : ℝ) + (G.m : ℝ) + 2)) ^ max P.p_t 1 +
          (G.n : ℝ) + (G.m : ℝ) + (initOut.state.H.m : ℝ) + (G.m : ℝ) * P.γ_ℓ + (L : ℝ) + 1) := by
  have h1 : (dsInitAtContract impl mMax w L q t vCap eCap b G vL eEdges).cost args mem ≤
      (dsInitContract impl mMax w L q vCap eCap G vL eEdges).cost args mem := by
    dsimp only [dsInitAtContract, dsInitContract]; omega
  have h2 : (initAt G L q t (canonicalSparsify impl)).state.H.m =
      (init G L q (canonicalSparsify impl)).state.H.m := rfl
  simpa only [h2] using le_trans (Nat.cast_le.mpr h1)
    (dsInit_initCostBound impl mMax w L q vCap eCap G vL eEdges args mem hG hGm)

theorem dsInit_initCostBound_of_one_le_pt (impl : SparsifyImpl) (mMax w L q vCap eCap : ℕ)
    (G : MGraph) (vL : List ℕ) (eEdges : List (ℕ × ℕ × ℕ))
    (args : List ℕ) (mem : ℕ → ℕ) (hG : G.IsValid) (hGm : G.m ≤ mMax) (hpt : 1 ≤ impl.p_t) :
    let P := canonicalSparsifyParams impl mMax
    let initOut := init G L q (canonicalSparsify impl)
    ((dsInitContract impl mMax w L q vCap eCap G vL eEdges).cost args mem : ℝ) ≤
      (dsInitCostFactor impl : ℝ) *
        (P.K_t * P.γ_t * (((activeSubgraph G).n : ℝ) + (G.m : ℝ) * P.γ_ℓ ^ 2) *
            (1 + Real.log (((activeSubgraph G).n : ℝ) + (G.m : ℝ) + 2)) ^ P.p_t +
          (G.n : ℝ) + (G.m : ℝ) + (initOut.state.H.m : ℝ) + (G.m : ℝ) * P.γ_ℓ + (L : ℝ) + 1) := by
  have hmax : max (canonicalSparsifyParams impl mMax).p_t 1 = (canonicalSparsifyParams impl mMax).p_t :=
    max_eq_left hpt
  simpa only [hmax] using dsInit_initCostBound impl mMax w L q vCap eCap G vL eEdges args mem hG hGm

theorem dsInit_initCostBound_of_one (impl : SparsifyImpl) (mMax w L q vCap eCap : ℕ)
    (G : MGraph) (vL : List ℕ) (eEdges : List (ℕ × ℕ × ℕ))
    (args : List ℕ) (mem : ℕ → ℕ) (hG : G.IsValid) (hGm : G.m ≤ mMax)
    (hγ_t : impl.γ_t mMax = 1) :
    let P := canonicalSparsifyParams impl mMax
    let initOut := init G L q (canonicalSparsify impl)
    ((dsInitContract impl mMax w L q vCap eCap G vL eEdges).cost args mem : ℝ) ≤
      (dsInitCostFactor impl : ℝ) *
        (P.K_t * (((activeSubgraph G).n : ℝ) + (G.m : ℝ) * P.γ_ℓ ^ 2) *
            (1 + Real.log (((activeSubgraph G).n : ℝ) + (G.m : ℝ) + 2)) ^ max P.p_t 1 +
          (G.n : ℝ) + (G.m : ℝ) + (initOut.state.H.m : ℝ) + (G.m : ℝ) * P.γ_ℓ + (L : ℝ) + 1) := by
  simpa [canonicalSparsifyParams, hγ_t] using
    dsInit_initCostBound impl mMax w L q vCap eCap G vL eEdges args mem hG hGm

end
end MinCostFlow.DynSpanner.Program
