module

public import MinCostFlow.LastLevelProgram.RepresentativeGraph
import Mathlib.Tactic

/-!
# Specification of the rounded last-level collection

The restriction of each low-stretch tree is the same as in the exact
model. The rounded potential supplies the new bounds on the stored
stretches for Definition 5.8 (pages 19–20) and Lemma 5.5 (page 18).
-/

public section

namespace MinCostFlow.LastLevelProgram

open MinCostFlow.LSF MinCostFlow.SparseCore MinCostFlow.Chain
open scoped BigOperators

private lemma isWalk_of_walkEdges_eq {H K : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (hW : H.IsWalk u v P)
    (hE : ∀ f ∈ walkEdges P, f ∈ K.E ∧ K.tail f = H.tail f ∧ K.head f = H.head f) :
    K.IsWalk u v P ∧ K.walkVertices u P = H.walkVertices u P := by
  induction hW with
  | nil s => exact ⟨.nil s, rfl⟩
  | @cons u₀ v₀ x₀ P₀ hxE hsrc _ ih =>
    have hwe : x₀.1 ∈ walkEdges (x₀ :: P₀) := by
      rw [walkEdges_cons, Finset.mem_insert]; exact Or.inl rfl
    have hxK := hE x₀.1 hwe
    have hsub : ∀ f ∈ walkEdges P₀, f ∈ K.E ∧ K.tail f = H.tail f ∧ K.head f = H.head f :=
      fun f hf => hE f (by rw [walkEdges_cons, Finset.mem_insert]; exact Or.inr hf)
    obtain ⟨ihW, ihV⟩ := ih hsub
    have hsrc' : K.src x₀ = u₀ := by
      rw [← hsrc]
      rcases x₀ with ⟨e, _ | _⟩ <;> simp [MGraph.src, hxK.2.1, hxK.2.2]
    have hdst' : K.dst x₀ = H.dst x₀ := by
      rcases x₀ with ⟨e, _ | _⟩ <;> simp [MGraph.dst, hxK.2.1, hxK.2.2]
    refine ⟨.cons hxK.1 hsrc' (hdst'.symm ▸ ihW), ?_⟩
    rw [walkVertices_cons, walkVertices_cons, hdst']
    exact congrArg (u₀ :: ·) (by simpa [hdst'] using ihV)

private lemma mem_edges_of_mem_walkEdges {G : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (hW : G.IsWalk u v P) {f : ℕ} (hf : f ∈ walkEdges P) : f ∈ G.E := by
  rw [walkEdges, List.mem_toFinset, List.mem_map] at hf
  obtain ⟨a, haP, rfl⟩ := hf
  exact IsWalk_edges_mem hW haP

/-- Definition 5.8 (pages 19–20), using the rounded form of Lemma 5.5
(page 18). The tree guarantee is needed only for the queries in this run. -/
theorem fixedPointLastLevelTool_spec (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (C_lsst : ℝ) (G_d : MGraph) (ℓ_d : ℕ → ℝ)
    (hG : G_d.IsValid) (hℓ : ∀ e ∈ G_d.E, 0 < ℓ_d e)
    (hLSST : let H := representativeGraph G_d ℓ_d
       ∀ j < lastMWUK H,
        let v := weights (weightPrecision C_lsst H) (roundedScale C_lsst H)
          (stretchQuery oracle H ℓ_d (weightPrecision C_lsst H)) j
        (∀ e ∈ H.E, 1 ≤ v e) →
        (∑ e ∈ H.E, v e) ≤ 2 * H.m →
        IsLSST H (safeLen H ℓ_d) v (C_lsst * (Real.log ((H.n : ℝ) + 2)) ^ 2)
          (oracle H (safeLen H ℓ_d) v)) :
    let params := lastLevelParams (128 * max 1 C_lsst)
    let res := (fixedPointLastLevelTool oracle C_lsst).build G_d ℓ_d
    0 < res.1 ∧
    (∀ j < res.1, (res.2 j).Holds G_d ℓ_d (params.σ_last G_d.n)) ∧
    (∀ e ∈ G_d.E,
      (∑ j ∈ Finset.range res.1, (res.2 j).wstr e) / (res.1 : ℝ) ≤ params.σ_mwu G_d.n) ∧
    (∀ j < res.1, ∀ u ∈ G_d.V, ∀ v ∈ G_d.V,
      G_d.Connected u v → (res.2 j).F.F.Connected u v) ∧
    ((fixedPointLastLevelTool oracle C_lsst).cost G_d : ℝ) ≤
      params.c_last * ((G_d.m : ℝ) + 1) ^ 2 *
        (Real.log ((G_d.m : ℝ) + (G_d.n : ℝ) + 2)) ^ params.p_last := by
  classical
  dsimp only [fixedPointLastLevelTool]
  by_cases hnl : (nonLoopEdges G_d).Nonempty
  · simp only [hnl, ↓reduceIte]
    let Gs := representativeGraph G_d ℓ_d
    let K := Gs.m
    let query := stretchQuery oracle Gs ℓ_d (weightPrecision C_lsst Gs)
    let v := weights (weightPrecision C_lsst Gs) (roundedScale C_lsst Gs) query
    let R := componentRoots G_d
    have hGs_val := representativeGraph_valid G_d ℓ_d
    have hGs_sub := representativeGraph_subgraph hG ℓ_d
    have hGs_n : Gs.n ≤ G_d.n := Finset.card_le_card hGs_sub.1
    have hGs_sq := representativeGraph_m_le_sq G_d ℓ_d
    have hGs_m1 : 1 ≤ Gs.m := by
      obtain ⟨e, he⟩ := hnl
      exact Finset.card_pos.mpr ⟨_, (representativeGraph_shortest (ℓ := ℓ_d) he).1⟩
    have hℓs : ∀ e ∈ Gs.E, 0 < ℓ_d e := fun e he => hℓ e (hGs_sub.2.1 he)
    have hInv := stretchQuery_bounds oracle C_lsst Gs ℓ_d hGs_m1 hℓs hLSST
    have hKle : K ≤ lastMWUK Gs := lastMWUK_ge_edges Gs
    have hKpos : 1 ≤ K := hGs_m1
    have hKhalf : (Gs.m : ℝ) / 2 ≤ (K : ℝ) := by
      dsimp only [K]
      linarith [Nat.cast_nonneg (α := ℝ) Gs.m]
    have htree (j : ℕ) (hj : j < K) :
        IsLSST Gs (safeLen Gs ℓ_d) (v j) (C_lsst * (Real.log ((Gs.n : ℝ) + 2)) ^ 2)
          (oracle Gs (safeLen Gs ℓ_d) (v j)) := hLSST j (hj.trans_le hKle) (hInv.1 j (hj.le.trans hKle)).1 (hInv.1 j (hj.le.trans hKle)).2
    have hR_sub := componentRoots_subset G_d
    have hbranch : ∀ j < K,
        let Tj := oracle Gs (safeLen Gs ℓ_d) (v j)
        let F : MGraph := { V := G_d.V, E := Tj.E ∩ Gs.E, tail := G_d.tail, head := G_d.head }
        let RF : RootedForest := { F := F, R := R }
        F.IsForest ∧
        RF.IsRootedSpanningForestOf G_d ∧
        (∀ u v, G_d.Connected u v → F.Connected u v) ∧
        ∀ e ∈ Gs.E, F.forestPath (Gs.tail e) (Gs.head e) = Tj.forestPath (Gs.tail e) (Gs.head e) := by
      intro j hj
      have hIsLSST := htree j hj
      set Tj := oracle Gs (safeLen Gs ℓ_d) (v j)
      let F : MGraph := { V := G_d.V, E := Tj.E ∩ Gs.E, tail := G_d.tail, head := G_d.head }
      have hF_val : F.IsValid := fun e he => hG e (hGs_sub.2.1 (Finset.mem_inter.mp he).2)
      have hF_for : F.IsForest := by
        refine ⟨hF_val, fun P ⟨hne, hnd, u, hW⟩ => hIsLSST.1.1.2 P ⟨hne, hnd, u, ?_⟩⟩
        have hEdges : ∀ f ∈ walkEdges P, f ∈ Tj.E ∧ Tj.tail f = F.tail f ∧ Tj.head f = F.head f := by
          intro f hf
          have hfF := mem_edges_of_mem_walkEdges hW hf
          have hfTj : f ∈ Tj.E := (Finset.mem_inter.mp hfF).1
          have hEnds := hIsLSST.2.1 f hfTj (Finset.mem_inter.mp hfF).2
          exact ⟨hfTj, hEnds.1, hEnds.2⟩
        exact (isWalk_of_walkEdges_eq hW hEdges).1
      have hSub_GF : G_d.IsSubgraph F :=
        ⟨Finset.Subset.refl _, fun e he => hGs_sub.2.1 (Finset.mem_inter.mp he).2, fun _ _ => ⟨rfl, rfl⟩⟩
      have hpath_eq : ∀ e ∈ Gs.E,
          F.forestPath (Gs.tail e) (Gs.head e) = Tj.forestPath (Gs.tail e) (Gs.head e) := by
        intro e he
        have heV := hGs_val e he
        have hP := forestPath_isPath hIsLSST.1.1
          (hIsLSST.1.2.2 (Gs.tail e) (hIsLSST.1.2.1 ▸ heV.1) (Gs.head e) (hIsLSST.1.2.1 ▸ heV.2))
        have hEdges_mem : ∀ f ∈ walkEdges (Tj.forestPath (Gs.tail e) (Gs.head e)),
            f ∈ F.E ∧ F.tail f = Tj.tail f ∧ F.head f = Tj.head f := fun f hf => by
          have hfTj : f ∈ Tj.E := mem_edges_of_mem_walkEdges hP.1 hf
          have hfGs : f ∈ Gs.E := hIsLSST.2.2.1 e he f hf
          have hfF : f ∈ F.E := Finset.mem_inter.mpr ⟨hfTj, hfGs⟩
          have hEnds := hIsLSST.2.1 f hfTj hfGs
          exact ⟨hfF, hEnds.1.symm, hEnds.2.symm⟩
        obtain ⟨hW_F, hverts_F⟩ := isWalk_of_walkEdges_eq hP.1 hEdges_mem
        exact forestPath_eq_of_isPath hF_for ⟨hW_F, hverts_F ▸ hP.2⟩
      have hedge_conn : ∀ e ∈ G_d.E, F.Connected (G_d.tail e) (G_d.head e) := by
        intro e he
        by_cases hloop : G_d.tail e = G_d.head e
        · rw [hloop]; exact MGraph.connected_refl F _
        · let e' := shortestEdge G_d ℓ_d (edgePairKey G_d e)
          obtain ⟨he', hkey, _⟩ := representativeGraph_shortest (ℓ := ℓ_d) (Finset.mem_filter.mpr ⟨he, hloop⟩)
          have hW : F.IsWalk (Gs.tail e') (Gs.head e') (Tj.forestPath (Gs.tail e') (Gs.head e')) := by
            have he'V := hGs_val e' he'
            have hP := forestPath_isPath hIsLSST.1.1
              (hIsLSST.1.2.2 (Gs.tail e') (hIsLSST.1.2.1 ▸ he'V.1)
                (Gs.head e') (hIsLSST.1.2.1 ▸ he'V.2))
            have hEdges_mem : ∀ f ∈ walkEdges (Tj.forestPath (Gs.tail e') (Gs.head e')),
                f ∈ F.E ∧ F.tail f = Tj.tail f ∧ F.head f = Tj.head f := fun f hf => by
              have hfTj := mem_edges_of_mem_walkEdges hP.1 hf
              have hfGs := hIsLSST.2.2.1 e' he' f hf
              have hfF := Finset.mem_inter.mpr ⟨hfTj, hfGs⟩
              have hEnds := hIsLSST.2.1 f hfTj hfGs
              exact ⟨hfF, hEnds.1.symm, hEnds.2.symm⟩
            exact (isWalk_of_walkEdges_eq hP.1 hEdges_mem).1
          have hc_e' : F.Connected (G_d.tail e') (G_d.head e') := hW |> fun hw => ⟨_, hw⟩
          have hpair := pair_eq_of_edgePairKey hkey
          rcases hpair with ⟨ht, hh⟩ | ⟨ht, hh⟩
          · rw [← ht, ← hh]; exact hc_e'
          · rw [← ht, ← hh]; exact MGraph.connected_symm hc_e'
      have hSpan : ∀ u v, G_d.Connected u v → F.Connected u v := by
        intro u v ⟨P, hW⟩
        induction hW with
        | nil s => exact MGraph.connected_refl F s
        | @cons a b x xs hxE hsrc _ ih =>
          have hstep : F.Connected a (G_d.dst x) := by
            rcases x with ⟨e, _ | _⟩ <;> dsimp only [MGraph.src, MGraph.dst] at hsrc ⊢ <;>
              rw [← hsrc]
            · exact MGraph.connected_symm (hedge_conn e hxE)
            · exact hedge_conn e hxE
          exact MGraph.connected_trans hstep ih
      have hRF : ({ F := F, R := R } : RootedForest).IsRootedSpanningForestOf G_d := by
        refine ⟨hF_for, rfl, hR_sub, ?_, hSub_GF⟩
        intro v hv
        obtain ⟨r, hrR, hcG⟩ := componentRoots_connected hv
        refine ⟨r, ⟨hrR, hSpan v r hcG⟩, fun r' ⟨hr'R, hcF'⟩ => ?_⟩
        have hcG' : G_d.Connected r' r :=
          MGraph.connected_trans (MGraph.connected_symm (connected_of_subgraph hSub_GF hcF')) hcG
        exact componentRoots_unique hr'R hrR hcG'
      exact ⟨hF_for, hRF, hSpan, hpath_eq⟩
    have hGs_m_pos : (0 : ℝ) < (Gs.m : ℝ) := by exact_mod_cast hGs_m1
    have hL2_pos : 0 < Real.log ((G_d.n : ℝ) + 2) := by
      have := half_lt_log_add_two G_d.n; linarith
    have hGs_log_le : Real.log ((Gs.n : ℝ) + 2) ≤ Real.log ((G_d.n : ℝ) + 2) :=
      Real.log_le_log (by positivity)
        (by linarith [show (Gs.n : ℝ) ≤ G_d.n from by exact_mod_cast hGs_n])
    have hm_le_Gd_sq : (Gs.m : ℝ) ≤ (G_d.n : ℝ) ^ 2 := by
      exact_mod_cast hGs_sq.trans (Nat.pow_le_pow_left hGs_n 2)
    have hm_log_le : Real.log (2 * (Gs.m : ℝ)) ≤ 3 * Real.log ((G_d.n : ℝ) + 2) := by
      have hm_le_cube : (2 * (Gs.m : ℝ)) ≤ ((G_d.n : ℝ) + 2) ^ 3 := by
        have hn_nn : (0 : ℝ) ≤ G_d.n := Nat.cast_nonneg _
        nlinarith [sq_nonneg ((G_d.n : ℝ))]
      calc Real.log (2 * (Gs.m : ℝ))
          ≤ Real.log (((G_d.n : ℝ) + 2) ^ 3) := Real.log_le_log (by positivity) hm_le_cube
        _ = 3 * Real.log ((G_d.n : ℝ) + 2) := by rw [Real.log_pow]; ring
    have hW_le : lastW C_lsst Gs ≤ max 1 C_lsst * (Real.log ((G_d.n : ℝ) + 2)) ^ 2 := by
      unfold lastW
      have hlog1 : 0 ≤ Real.log ((Gs.n : ℝ) + 2) :=
        (half_lt_log_add_two Gs.n).le.trans' (by norm_num)
      have hsq : Real.log ((Gs.n : ℝ) + 2) ^ 2 ≤ Real.log ((G_d.n : ℝ) + 2) ^ 2 :=
        pow_le_pow_left₀ hlog1 hGs_log_le 2
      have hC0 : 0 ≤ max 1 C_lsst := le_trans zero_le_one (le_max_left _ _)
      exact mul_le_mul_of_nonneg_left hsq hC0
    have hRho_le : roundedScale C_lsst Gs ≤ (lastLevelParams (128 * max 1 C_lsst)).σ_last G_d.n := by
      have hC : (1 : ℝ) ≤ 128 * max 1 C_lsst := by linarith [le_max_left (1 : ℝ) C_lsst]
      refine (roundedScale_bounds C_lsst Gs).2.trans ?_
      unfold lastRho lastLevelParams
      rw [max_eq_right hC]
      apply le_max_of_le_right
      have hprod := mul_le_mul hW_le hm_le_Gd_sq (Nat.cast_nonneg _) (by positivity)
      nlinarith only [hprod, show 0 ≤ max 1 C_lsst * Real.log ((G_d.n : ℝ) + 2)^2 * (G_d.n : ℝ)^2 by positivity]
    have hstretch_bound : ∀ j < K, ∀ e ∈ G_d.E,
        let Tj := oracle Gs (safeLen Gs ℓ_d) (v j)
        let F : MGraph := { V := G_d.V, E := Tj.E ∩ Gs.E, tail := G_d.tail, head := G_d.head }
        let RF : RootedForest := { F := F, R := R }
        let wstr_e := if G_d.tail e = G_d.head e then (1 : ℝ)
          else query (v j) (shortestEdge G_d ℓ_d (edgePairKey G_d e))
        RF.stretch G_d ℓ_d e ≤ wstr_e ∧
        wstr_e ≤ (lastLevelParams (128 * max 1 C_lsst)).σ_last G_d.n := by
      intro j hj e he
      dsimp only
      obtain ⟨hF_for, hRF, hSpan, hpath_eq⟩ := hbranch j hj
      set Tj := oracle Gs (safeLen Gs ℓ_d) (v j)
      let F : MGraph := { V := G_d.V, E := Tj.E ∩ Gs.E, tail := G_d.tail, head := G_d.head }
      let RF : RootedForest := { F := F, R := R }
      by_cases hloop : G_d.tail e = G_d.head e
      · simp only [hloop, ↓reduceIte]
        have hstr1 : RF.stretch G_d ℓ_d e = 1 := by
          unfold RootedForest.stretch
          dsimp only
          rw [hloop]
          simp only [↓reduceIte]
          change 1 + walkLength ℓ_d (F.forestPath (G_d.head e) (G_d.head e)) / ℓ_d e = 1
          rw [forestPath_self hF_for, walkLength_nil, zero_div, add_zero]
        rw [hstr1]
        exact ⟨le_rfl, le_max_left _ _⟩
      · simp only [hloop, ↓reduceIte]
        have he_nl : e ∈ nonLoopEdges G_d := Finset.mem_filter.mpr ⟨he, hloop⟩
        set e' := shortestEdge G_d ℓ_d (edgePairKey G_d e)
        have hspec := representativeGraph_shortest (ℓ := ℓ_d) he_nl
        have he' : e' ∈ Gs.E := hspec.1
        have hkey : edgePairKey G_d e' = edgePairKey G_d e := hspec.2.1
        have hlen_le : ℓ_d e' ≤ ℓ_d e := hspec.2.2
        have hcF : F.Connected (Gs.tail e') (Gs.head e') :=
          hSpan _ _ (connected_of_edge (hGs_sub.2.1 he'))
        have hIsLSST_j := htree j hj
        set P := Tj.forestPath (Gs.tail e') (Gs.head e')
        have hlen_safe : walkLength ℓ_d P = walkLength (safeLen Gs ℓ_d) P := by
          unfold walkLength
          refine Finset.sum_congr rfl fun f hf => ?_
          rw [safeLen_eq_of_mem ℓ_d (hIsLSST_j.2.2.1 e' he' f hf)]
        have hpath_F_Tj : F.forestPath (Gs.tail e') (Gs.head e') = P := hpath_eq e' he'
        have hwalkLen_eq :
            walkLength ℓ_d (F.forestPath (G_d.tail e) (G_d.head e)) =
              walkLength (safeLen Gs ℓ_d) P := by
          have hpair := pair_eq_of_edgePairKey hkey
          rcases hpair with ⟨ht, hh⟩ | ⟨ht, hh⟩
          · change Gs.tail e' = G_d.tail e at ht
            change Gs.head e' = G_d.head e at hh
            rw [← ht, ← hh, hpath_F_Tj, hlen_safe]
          · change Gs.tail e' = G_d.head e at ht
            change Gs.head e' = G_d.tail e at hh
            rw [← ht, ← hh, forestPath_rev hF_for hcF, walkLength_walkRev, hpath_F_Tj, hlen_safe]
        have hroot_eq : RF.root (G_d.tail e) = RF.root (G_d.head e) :=
          root_eq_of_connected hRF (hG e he).1 (hG e he).2 (hSpan _ _ (connected_of_edge he))
        have hstretch_le : RF.stretch G_d ℓ_d e ≤ treeStretch Gs Tj (safeLen Gs ℓ_d) e' := by
          unfold RootedForest.stretch treeStretch
          dsimp only
          simp only [hroot_eq, ↓reduceIte]
          rw [hwalkLen_eq, safeLen_eq_of_mem ℓ_d he']
          have hw_nn : 0 ≤ walkLength (safeLen Gs ℓ_d) P := by
            unfold walkLength
            exact Finset.sum_nonneg fun f _ => mul_nonneg (safeLen_nonneg hℓs f) (abs_nonneg _)
          have hℓe'_pos : 0 < ℓ_d e' := hℓs e' he'
          exact add_le_add_right (div_le_div_of_nonneg_left hw_nn hℓe'_pos hlen_le) 1
        exact ⟨hstretch_le.trans (roundStretch_bounds _ _).1, (hInv.2.1 j (hj.trans_le hKle) e' he').trans hRho_le⟩
    refine ⟨hKpos, ?_, ?_, ?_, ?_⟩
    · intro j hj
      obtain ⟨hF_for, hRF, _, _⟩ := hbranch j hj
      refine ⟨hF_for, hRF, ⟨Finset.Subset.refl _, Finset.Subset.refl _, fun _ _ => ⟨rfl, rfl⟩⟩, ?_⟩
      intro e he
      have hb := hstretch_bound j hj e he
      simpa [nonLoopEdges, he, ite_not] using hb
    · intro e he
      by_cases hloop : G_d.tail e = G_d.head e
      · have hK_ne : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hKpos
        have hout : e ∉ nonLoopEdges G_d := fun h => (Finset.mem_filter.mp h).2 hloop
        have hsum : (∑ j ∈ Finset.range K, (if e ∈ nonLoopEdges G_d then
            query (v j) (shortestEdge G_d ℓ_d (edgePairKey G_d e)) else (1 : ℝ))) = K := by
          simp [hout]
        change (∑ j ∈ Finset.range K, _) / (K : ℝ) ≤ _
        rw [hsum, div_self hK_ne]
        exact le_max_left _ _
      · have he_nl : e ∈ nonLoopEdges G_d := Finset.mem_filter.mpr ⟨he, hloop⟩
        have hrep := (representativeGraph_shortest (ℓ := ℓ_d) he_nl).1
        have hsum := (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hKle)
          (fun j _ _ => show 0 ≤ query (v j) (shortestEdge G_d ℓ_d (edgePairKey G_d e)) from by
            apply zero_le_one.trans
            apply le_trans _ (roundStretch_bounds _ _).1
            unfold treeStretch walkLength
            apply le_add_of_nonneg_right
            exact div_nonneg (Finset.sum_nonneg fun f _ =>
              mul_nonneg (safeLen_nonneg hℓs f) (abs_nonneg _)) (safeLen_nonneg hℓs _))).trans
          (hInv.2.2 _ hrep)
        have hKpos : (0 : ℝ) < K := by exact_mod_cast hKpos
        have hlog : 0 ≤ Real.log (2 * (Gs.m : ℝ)) :=
          Real.log_nonneg (by linarith [show (1 : ℝ) ≤ Gs.m from by exact_mod_cast hGs_m1])
        calc
          _ ≤ (4 * roundedScale C_lsst Gs * Real.log (2 * Gs.m)) / (K : ℝ) := by
            simp only [he_nl, ↓reduceIte]
            exact div_le_div_of_nonneg_right hsum hKpos.le
          _ ≤ (4 * roundedScale C_lsst Gs * Real.log (2 * Gs.m)) / ((Gs.m : ℝ) / 2) :=
            div_le_div_of_nonneg_left
              (mul_nonneg (mul_nonneg (by norm_num) ((mul_nonneg zero_le_two (lastRho_pos hGs_m1).le).trans (roundedScale_bounds C_lsst Gs).1)) hlog)
              (by positivity) hKhalf
          _ ≤ (4 * (32 * (2 * lastRho C_lsst Gs)) * Real.log (2 * Gs.m)) / ((Gs.m : ℝ) / 2) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (roundedScale_bounds C_lsst Gs).2 (by norm_num)) hlog)
              (by positivity)
          _ = 1024 * lastW C_lsst Gs * Real.log (2 * Gs.m) := by
            unfold lastRho
            field_simp [hGs_m_pos.ne']
            ring
          _ ≤ _ := by
            unfold lastLevelParams
            have hC : (1 : ℝ) ≤ 128 * max 1 C_lsst := by linarith [le_max_left (1 : ℝ) C_lsst]
            rw [max_eq_right hC]
            apply le_max_of_le_right
            have hprod := mul_le_mul hW_le hm_log_le hlog (by positivity)
            nlinarith only [hprod]
    · intro j hj u _ v _ hc
      exact (hbranch j hj).2.2.1 u v hc
    · have hG1 := representativeGraph_subgraph hG (fun _ => 1)
      have hG1_m : (representativeGraph G_d (fun _ => 1)).m = Gs.m := by
        rw [representativeGraph_m, representativeGraph_m]
      have hm := Finset.card_le_card hG1.2.1
      have hk := (lastMWUK_bounds (hG1_m.symm ▸ hGs_m1)).2.2.2
      have hk' : lastMWUK (representativeGraph G_d (fun _ => 1)) ≤ 2 * G_d.m :=
        hk.trans (Nat.mul_le_mul_left 2 hm)
      have hcost : lastMWUK (representativeGraph G_d (fun _ => 1)) * (G_d.m + 1) + 1 ≤
          8 * (G_d.m + 1) ^ 2 := by nlinarith [Nat.mul_le_mul_right (G_d.m + 1) hk']
      unfold lastLevelParams
      simp only [pow_zero, mul_one]
      exact_mod_cast hcost
  · simp only [hnl, ↓reduceIte]
    let F0 : MGraph := { V := G_d.V, E := ∅, tail := G_d.tail, head := G_d.head }
    have hloop_all : ∀ e ∈ G_d.E, G_d.tail e = G_d.head e := by
      intro e he
      by_contra hne
      exact hnl ⟨e, Finset.mem_filter.mpr ⟨he, hne⟩⟩
    have hF0_for : F0.IsForest := by
      refine ⟨fun _ he => False.elim (Finset.notMem_empty _ he), fun P ⟨hne, _, _, hW⟩ => ?_⟩
      cases hW with
      | nil _ => exact hne rfl
      | cons hxE _ _ => exact Finset.notMem_empty _ hxE
    have hF0_conn_eq : ∀ {u v : ℕ}, F0.Connected u v → u = v := by
      intro u v ⟨P, hW⟩
      cases hW with
      | nil _ => rfl
      | cons hxE _ _ => exact False.elim (Finset.notMem_empty _ hxE)
    have hG_conn_eq : ∀ {u v : ℕ}, G_d.Connected u v → u = v := by
      intro u v ⟨P, hW⟩
      induction hW with
      | nil _ => rfl
      | @cons a b x xs hxE hsrc _ ih =>
        have hloop := hloop_all x.1 hxE
        have heq_sd : G_d.src x = G_d.dst x := by
          rcases x with ⟨e, _ | _⟩ <;> simp [MGraph.src, MGraph.dst, hloop]
        exact hsrc.symm.trans (heq_sd.trans ih)
    have hRF0 : ({ F := F0, R := G_d.V } : RootedForest).IsRootedSpanningForestOf G_d := by
      refine ⟨hF0_for, rfl, Finset.Subset.refl _, ?_,
        ⟨Finset.Subset.refl _, Finset.empty_subset _, fun _ _ => ⟨rfl, rfl⟩⟩⟩
      intro v hv
      exact ⟨v, ⟨hv, MGraph.connected_refl F0 v⟩, fun r' ⟨_, hc⟩ => (hF0_conn_eq hc).symm⟩
    refine ⟨Nat.zero_lt_one, ?_, ?_, ?_, ?_⟩
    · intro j _
      refine ⟨hF0_for, hRF0, ⟨Finset.Subset.refl _, Finset.Subset.refl _, fun _ _ => ⟨rfl, rfl⟩⟩, ?_⟩
      intro e he
      have hloop := hloop_all e he
      have hstr : ({ F := F0, R := G_d.V } : RootedForest).stretch G_d ℓ_d e = 1 := by
        unfold RootedForest.stretch
        dsimp only
        rw [hloop]
        simp only [↓reduceIte]
        rw [forestPath_self hF0_for, walkLength_nil, zero_div, add_zero]
      rw [hstr]
      exact ⟨le_rfl, le_max_left _ _⟩
    · intro e _
      simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_one, div_one]
      exact le_max_left _ _
    · intro _ _ u _ v _ hc
      rw [hG_conn_eq hc]
      exact MGraph.connected_refl F0 v
    · have hcost1 : (1 : ℝ) ≤ 8 * ((G_d.m : ℝ) + 1) ^ 2 := by
        have hm0 : (0 : ℝ) ≤ (G_d.m : ℝ) := Nat.cast_nonneg _
        nlinarith
      unfold lastLevelParams
      simpa [pow_zero] using hcost1

/-- The fixed-point model satisfies the shared last-level specification.
A total mathematical LSST oracle supplies the actual-query premise of
`fixedPointLastLevelTool_spec` for arbitrary positive real lengths. -/
theorem fixedPointLastLevelTool_isSpec
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ)
    (hLSST : HasLSSTSpec oracle C) :
    (fixedPointLastLevelTool oracle C).IsSpec (lastLevelParams (128 * max 1 C)) := by
  intro G ℓ hG hℓ
  apply fixedPointLastLevelTool_spec oracle C G ℓ hG hℓ
  dsimp only
  intro j hj hv _
  let H := representativeGraph G ℓ
  have hsub := representativeGraph_subgraph hG ℓ
  have hvalid := representativeGraph_valid G ℓ
  have hm : H.m ≠ 0 := by
    intro hm
    have hzero : lastMWUK H = 0 := by simp [lastMWUK, hm]
    exact (Nat.not_lt_zero j) (hzero ▸ hj)
  obtain ⟨e, he⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hm)
  apply hLSST H (safeLen H ℓ) _ hvalid ⟨H.tail e, (hvalid e he).1⟩
  · intro f hf
    rw [safeLen_eq_of_mem ℓ hf]
    exact hℓ f (hsub.2.1 hf)
  · exact fun f hf => zero_lt_one.trans_le (hv f hf)

end MinCostFlow.LastLevelProgram
