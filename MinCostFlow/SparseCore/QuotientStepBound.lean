module

public import MinCostFlow.SparseCore.QuotientStep

import Mathlib.Tactic.Linarith

/-!
# Quantitative bounds on dynamic vertex-split quotient maintenance

Proves the splitting multiplicity bound for `rootSplitStep`, bounds the forest edges touched by
an adversarial split by `Δ_max(G₀)`, and packages `tildeStepSingle` and `tildeStepBatch` with
full structural, cardinality, and update-length guarantees.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner

@[expose] public section

/-! ## 1. Walk & path helpers for root-split targeting -/

lemma walkVertices_dropLast_cons (G : MGraph) (u : ℕ) (x : ℕ × Bool) (P : List (ℕ × Bool)) :
    (G.walkVertices u (x :: P)).dropLast = u :: (G.walkVertices (G.dst x) P).dropLast := by
  simp only [MGraph.walkVertices, List.map_cons]
  exact List.dropLast_cons_of_ne_nil (List.cons_ne_nil _ _)

lemma walkVertices_eq_dropLast_append {G : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (hW : G.IsWalk u v P) :
    G.walkVertices u P = (G.walkVertices u P).dropLast ++ [v] := by
  induction hW with
  | nil z => rfl
  | @cons a _ x P' _ _ hrest ih =>
    rw [walkVertices_dropLast_cons, List.cons_append, ← ih]
    rfl

lemma mem_dropLast_ne_end_of_isPath {G : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (hP : G.IsPath u v P) {z : ℕ} (hz : z ∈ (G.walkVertices u P).dropLast) : z ≠ v := by
  have hnd := hP.2
  rw [walkVertices_eq_dropLast_append hP.1, List.nodup_append] at hnd
  intro rfl
  exact hnd.2.2 z hz z List.mem_cons_self rfl

lemma connected_of_mem_walkVertices {G : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (hW : G.IsWalk u v P) {z : ℕ} (hz : z ∈ G.walkVertices u P) :
    G.Connected z v := by
  induction hW with
  | nil a =>
    simp only [MGraph.walkVertices, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
    subst hz
    exact ⟨[], .nil z⟩
  | @cons a _ x P' he hsrc hrest ih =>
    simp only [MGraph.walkVertices, List.map_cons, List.mem_cons] at hz
    rcases hz with rfl | hz'
    · exact ⟨x :: P', .cons he hsrc hrest⟩
    · exact ih (by simpa [MGraph.walkVertices] using hz')

lemma walkVertices_walkRev {G : MGraph} {u v : ℕ} {P : List (ℕ × Bool)} (hW : G.IsWalk u v P) :
    G.walkVertices v (walkRev P) = (G.walkVertices u P).reverse := by
  induction hW with
  | nil a => simp [MGraph.walkVertices, walkRev]
  | @cons a v₀ x P' _ hsrc hrest ih =>
    rcases x with ⟨xe, xb⟩
    have hdst : G.dst (xe, !xb) = a := by
      cases xb <;> simp [MGraph.src, MGraph.dst] at hsrc ⊢ <;> exact hsrc
    rw [walkRev, List.map_cons, List.reverse_cons]
    simp only [MGraph.walkVertices, List.map_append, List.map_singleton, hdst]
    have ih' : v₀ :: (walkRev P').map G.dst = (G.dst (xe, xb) :: P'.map G.dst).reverse := ih
    calc v₀ :: ((walkRev P').map G.dst ++ [a])
        = (v₀ :: (walkRev P').map G.dst) ++ [a] := List.cons_append.symm
      _ = (G.dst (xe, xb) :: P'.map G.dst).reverse ++ [a] := by rw [ih']
      _ = (a :: G.dst (xe, xb) :: P'.map G.dst).reverse := by simp [List.reverse_cons]

lemma walk_RF_avoiding_iso_to_S0 {thresh₀ K₀ thresh' K' : ℝ} {ℓ₀ : ℕ → ℝ} {S₀ S' : LSFState}
    (hI₀ : LSFInvWith thresh₀ K₀ ℓ₀ S₀) (hI' : LSFInvWith thresh' K' ℓ₀ S') (hD' : LSFDerivedFrom S₀ S')
    {u v : ℕ} {P : List (ℕ × Bool)} (hW : S'.RF.F.IsWalk u v P)
    (havoid : ∀ z ∈ S'.RF.F.walkVertices u P, z ∉ S'.isolatedVerts) :
    S₀.RF.F.IsWalk u v P ∧ S₀.RF.F.walkVertices u P = S'.RF.F.walkVertices u P := by
  induction hW with
  | nil a => exact ⟨.nil a, rfl⟩
  | @cons a _ x P' he hsrc hrest ih =>
    rcases x with ⟨xe, xb⟩
    have ha_niso : a ∉ S'.isolatedVerts := havoid a (by simp [MGraph.walkVertices])
    have hb_niso : S'.RF.F.dst (xe, xb) ∉ S'.isolatedVerts :=
      havoid _ (by simp [MGraph.walkVertices])
    have heF₀ : xe ∈ S₀.RF.F.E := hD'.hFE_sub he
    have heT' : xe ∈ S'.T₀.E := Finset.sdiff_subset he
    have heT₀ : xe ∈ S₀.T₀.E := Finset.sdiff_subset heF₀
    have hRF' := lsfInv_to_RS hI'
    have hRF₀ := lsfInv_to_RS hI₀
    have hV' : S'.RF.F.tail xe ∈ S'.G.V ∧ S'.RF.F.head xe ∈ S'.G.V := by
      have := hRF'.1.1 xe he; rwa [hRF'.2.1] at this
    have haV : a ∈ S'.G.V := by
      rw [← hsrc]; cases xb <;> simp [MGraph.src, hV'.1, hV'.2]
    have hbV : S'.RF.F.dst (xe, xb) ∈ S'.G.V := by
      cases xb <;> simp [MGraph.dst, hV'.1, hV'.2]
    have haT₀ : a ∈ S'.T₀.V := (Finset.mem_union.mp (hI'.hGV_eq ▸ haV)).resolve_right ha_niso
    have hS't : S'.RF.F.tail xe = S'.T₀.tail xe := by
      cases xb
      · have htl_iso : S'.RF.F.tail xe ∉ S'.isolatedVerts := by simpa [MGraph.dst] using hb_niso
        have htl_T₀ : S'.RF.F.tail xe ∈ S'.T₀.V :=
          (Finset.mem_union.mp (hI'.hGV_eq ▸ hV'.1)).resolve_right htl_iso
        calc S'.RF.F.tail xe = S'.origVert (S'.T_cur.tail xe) := (hI'.horig_id _ htl_T₀).symm
          _ = S'.T₀.tail xe := (hI'.horig_T xe heT').1
      · have htl : S'.RF.F.tail xe = a := by simpa [MGraph.src] using hsrc
        calc S'.RF.F.tail xe = S'.origVert (S'.T_cur.tail xe) := (hI'.horig_id _ (htl ▸ haT₀)).symm
          _ = S'.T₀.tail xe := (hI'.horig_T xe heT').1
    have hS'h : S'.RF.F.head xe = S'.T₀.head xe := by
      cases xb
      · have hhd : S'.RF.F.head xe = a := by simpa [MGraph.src] using hsrc
        calc S'.RF.F.head xe = S'.origVert (S'.T_cur.head xe) := (hI'.horig_id _ (hhd ▸ haT₀)).symm
          _ = S'.T₀.head xe := (hI'.horig_T xe heT').2
      · have hhd_iso : S'.RF.F.head xe ∉ S'.isolatedVerts := by simpa [MGraph.dst] using hb_niso
        have hhd_T₀ : S'.RF.F.head xe ∈ S'.T₀.V :=
          (Finset.mem_union.mp (hI'.hGV_eq ▸ hV'.2)).resolve_right hhd_iso
        calc S'.RF.F.head xe = S'.origVert (S'.T_cur.head xe) := (hI'.horig_id _ hhd_T₀).symm
          _ = S'.T₀.head xe := (hI'.horig_T xe heT').2
    have hV₀ : S₀.RF.F.tail xe ∈ S₀.G.V ∧ S₀.RF.F.head xe ∈ S₀.G.V := by
      have := hRF₀.1.1 xe heF₀; rwa [hRF₀.2.1] at this
    have hT₀_mem : ∀ z ∈ S₀.G.V, z ∈ S₀.T₀.V := by
      intro z hz
      rw [hI₀.hGV_eq, hD'.hS₀_iso, Finset.union_empty] at hz
      exact hz
    have hS₀t : S₀.RF.F.tail xe = S₀.T₀.tail xe := by
      calc S₀.RF.F.tail xe = S₀.origVert (S₀.T_cur.tail xe) := (hI₀.horig_id _ (hT₀_mem _ hV₀.1)).symm
        _ = S₀.T₀.tail xe := (hI₀.horig_T xe heT₀).1
    have hS₀h : S₀.RF.F.head xe = S₀.T₀.head xe := by
      calc S₀.RF.F.head xe = S₀.origVert (S₀.T_cur.head xe) := (hI₀.horig_id _ (hT₀_mem _ hV₀.2)).symm
        _ = S₀.T₀.head xe := (hI₀.horig_T xe heT₀).2
    have htail_eq : S₀.RF.F.tail xe = S'.RF.F.tail xe := by rw [hS₀t, hS't, hD'.hT₀_eq]
    have hhead_eq : S₀.RF.F.head xe = S'.RF.F.head xe := by rw [hS₀h, hS'h, hD'.hT₀_eq]
    have hsrc₀ : S₀.RF.F.src (xe, xb) = a := by
      cases xb <;> simp [MGraph.src, htail_eq, hhead_eq] <;> exact hsrc
    have hdst₀ : S₀.RF.F.dst (xe, xb) = S'.RF.F.dst (xe, xb) := by
      cases xb <;> simp [MGraph.dst, htail_eq, hhead_eq]
    obtain ⟨ih_walk, ih_wv⟩ := ih fun z hz => havoid z (by
      simp only [MGraph.walkVertices, List.map_cons, List.mem_cons]
      right; simpa [MGraph.walkVertices] using hz)
    refine ⟨.cons heF₀ hsrc₀ (hdst₀ ▸ ih_walk), ?_⟩
    simp only [MGraph.walkVertices, List.map_cons]
    congr 1
    rw [hdst₀]
    simpa [MGraph.walkVertices] using ih_wv

lemma walk_S0_avoiding_R_stays_in_piece {S₀ : LSFState}
    (hBiU : S₀.W_init.biUnion (inducedEdges S₀.RF.F) = S₀.RF.F.E)
    (hb : boundary S₀.W_init ⊆ S₀.R) :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)},
      S₀.RF.F.IsWalk u v P →
      (∀ z ∈ (S₀.RF.F.walkVertices u P).dropLast, z ∉ S₀.R) →
      ∀ W ∈ S₀.W_init, u ∈ W → v ∈ W := by
  intro u v P hW
  induction hW with
  | nil z => intro _ W _ hz; exact hz
  | @cons a _ x P' he hsrc hrest ih =>
    intro havoid W hW_mem haW
    have ha_nR : a ∉ S₀.R := by
      apply havoid
      rw [walkVertices_dropLast_cons]
      exact List.mem_cons_self
    have heF : x.1 ∈ S₀.RF.F.E := he
    rw [← hBiU, Finset.mem_biUnion] at heF
    obtain ⟨W', hW'_mem, heW'⟩ := heF
    rw [inducedEdges, Finset.mem_filter] at heW'
    have haW' : a ∈ W' := by
      rcases x with ⟨e₀, b₀⟩
      cases b₀ <;> simp only [MGraph.src, Bool.false_eq_true, ↓reduceIte] at hsrc
      · rw [← hsrc]; exact heW'.2.2
      · rw [← hsrc]; exact heW'.2.1
    have hdW' : S₀.RF.F.dst x ∈ W' := by
      rcases x with ⟨e₀, b₀⟩
      cases b₀ <;> simp only [MGraph.dst, Bool.false_eq_true, ↓reduceIte]
      · exact heW'.2.1
      · exact heW'.2.2
    have hWeq : W' = W := unique_piece_of_not_R hb ha_nR hW'_mem hW_mem haW' haW
    apply ih (fun z hz => havoid z ?_) W hW_mem (hWeq ▸ hdW')
    rw [walkVertices_dropLast_cons]
    exact List.mem_cons_of_mem _ hz

/-! ## 2. Splitting multiplicity bound for `splitTargets` -/

lemma splitTarget_mem_witness {S₀ S S' : LSFState} {C_mid : MGraph} {m_mid : ℕ → ℕ}
    {thresh K : ℝ} {ℓ₀ : ℕ → ℝ}
    (hI : LSFInvWith thresh K ℓ₀ S)
    (hMidInv : ∀ x ∈ S'.G.V, ∀ y ∈ S'.G.V,
      m_mid x = m_mid y ↔
        x = y ∨ (x ∈ S₀.G.V ∧ y ∈ S₀.G.V ∧ S.RF.root x = S.RF.root y ∧
          (x ∈ S₀.R ↔ y ∈ S₀.R) ∧ (x ∉ S₀.R → ∃ W ∈ S₀.W_init, x ∈ W ∧ y ∈ W)))
    (hR₀_sub : S₀.R ⊆ S.R)
    {r vT : ℕ} (hp : (r, vT) ∈ splitTargets S S' C_mid m_mid) :
    r ∈ S'.R \ S.R ∧
    ∃ x ∈ S'.G.V, x ∈ S₀.G.V ∧ x ∉ S₀.R ∧ m_mid x = vT ∧ S'.RF.root x = r ∧
      ∃ W ∈ S₀.W_init, x ∈ W := by
  classical
  simp only [splitTargets, Finset.mem_filter, Finset.mem_product] at hp
  rcases hp with ⟨⟨hr_diff, _⟩, ⟨x, hxV, hmx, hrx⟩, ⟨y, hyV, hmy, hry⟩⟩
  have hxy_ne : x ≠ y := fun h => hry (h ▸ hrx)
  have hrel := ((hMidInv x hxV y hyV).mp (hmx.trans hmy.symm)).resolve_left hxy_ne
  rcases hrel with ⟨hx₀, _, hrtS, hR_iff, hW⟩
  have hRF := lsfInv_to_RS hI
  have hx_nR₀ : x ∉ S₀.R := by
    intro hxR
    have hyR : y ∈ S₀.R := hR_iff.mp hxR
    have hrxS := rootedForest_root_eq_of_mem_R hRF (hR₀_sub hxR)
    have hryS := rootedForest_root_eq_of_mem_R hRF (hR₀_sub hyR)
    exact hxy_ne (hrxS.symm.trans (hrtS.trans hryS))
  obtain ⟨W, hW_mem, hxW, _⟩ := hW hx_nR₀
  exact ⟨hr_diff, x, hxV, hx₀, hx_nR₀, hmx, hrx, W, hW_mem, hxW⟩

lemma path_to_root_avoiding_R_iso {thresh' K' : ℝ} {ℓ₀ : ℕ → ℝ} {S₀ S S' : LSFState}
    (hI' : LSFInvWith thresh' K' ℓ₀ S')
    (hR_sub : S₀.R ⊆ S.R) (hR_sub' : S.R ⊆ S'.R)
    {x r : ℕ} {P : List (ℕ × Bool)}
    (hP : S'.RF.F.IsPath x r P) (hrR : r ∈ S'.R)
    {z : ℕ} (hz : z ∈ (S'.RF.F.walkVertices x P).dropLast) :
    z ∉ S'.R ∧ z ∉ S₀.R ∧ z ∉ S'.isolatedVerts := by
  have hRF' := lsfInv_to_RS hI'
  have hne_r : z ≠ r := mem_dropLast_ne_end_of_isPath hP hz
  have hconn : S'.RF.F.Connected z r :=
    connected_of_mem_walkVertices hP.1 (List.mem_of_mem_dropLast hz)
  have hz_nR' : z ∉ S'.R := by
    intro hzR
    have heq := rootedForest_root_eq_of_connected hRF' (hRF'.2.2.1 hzR) (hRF'.2.2.1 hrR) hconn
    rw [rootedForest_root_eq_of_mem_R hRF' hzR, rootedForest_root_eq_of_mem_R hRF' hrR] at heq
    exact hne_r heq
  exact ⟨hz_nR', fun h => hz_nR' (hR_sub' (hR_sub h)),
    fun h => hz_nR' (Finset.mem_union_right _ h)⟩

lemma splitTargets_same_fst_not_iso {thresh₀ K₀ thresh K : ℝ} {ℓ₀ : ℕ → ℝ}
    {S₀ S : LSFState} {u : Update}
    (hI₀ : LSFInvWith thresh₀ K₀ ℓ₀ S₀) (hCov₀ : S₀.W_init.biUnion (inducedEdges S₀.RF.F) = S₀.RF.F.E)
    (hI : LSFInvWith thresh K ℓ₀ S) (hu : S.G.UpdateIsValid u) (hD : LSFDerivedFrom S₀ S)
    {C_mid : MGraph} {m_mid : ℕ → ℕ}
    (hMidInv : ∀ x ∈ (applyLSFUpdate S u).G.V, ∀ y ∈ (applyLSFUpdate S u).G.V,
      m_mid x = m_mid y ↔
        x = y ∨ (x ∈ S₀.G.V ∧ y ∈ S₀.G.V ∧ S.RF.root x = S.RF.root y ∧
          (x ∈ S₀.R ↔ y ∈ S₀.R) ∧ (x ∉ S₀.R → ∃ W ∈ S₀.W_init, x ∈ W ∧ y ∈ W)))
    {r v₁ v₂ : ℕ}
    (h1 : (r, v₁) ∈ splitTargets S (applyLSFUpdate S u) C_mid m_mid)
    (h2 : (r, v₂) ∈ splitTargets S (applyLSFUpdate S u) C_mid m_mid)
    (hniso : r ∉ (applyLSFUpdate S u).isolatedVerts) :
    v₁ = v₂ := by
  let S' := applyLSFUpdate S u
  have hsp := applyLSFUpdate_inv_with hI hu
  have hI' := hsp.1
  have hD' := lsfDerivedFrom_step hI hu hD
  have hR_sub' := hsp.2.2.2.2.2.2.2.2.1
  have hRF' := lsfInv_to_RS hI'
  obtain ⟨hr_diff, x₁, hx₁V, hx₁₀, hx₁_nR₀, hmx₁, hrx₁, W₁, hW₁, hx₁W⟩ :=
    splitTarget_mem_witness hI hMidInv hD.hR_sub h1
  obtain ⟨_, x₂, hx₂V, hx₂₀, hx₂_nR₀, hmx₂, hrx₂, W₂, hW₂, hx₂W⟩ :=
    splitTarget_mem_witness hI hMidInv hD.hR_sub h2
  have hr_diff' := Finset.mem_sdiff.mp hr_diff
  have hrR' : r ∈ S'.R := hr_diff'.1
  have hr_nR₀ : r ∉ S₀.R := fun h => hr_diff'.2 (hD.hR_sub h)
  have hrT₀' : r ∈ S'.T₀.V :=
    (Finset.mem_union.mp (hI'.hGV_eq ▸ hRF'.2.2.1 hrR')).resolve_right hniso
  have hrG : r ∈ S.G.V := by
    rw [hI.hGV_eq, Finset.mem_union]; left; exact hsp.2.2.2.1 ▸ hrT₀'
  have hS₀_sub_G : S₀.G.V ⊆ S.G.V := by
    intro z hz
    rw [hI.hGV_eq, Finset.mem_union]; left
    rw [hI.hTV, hD.hG₀_eq, ← hD.hS₀_G]; exact hz
  have hrt₁_S : S.RF.root x₁ = S.RF.root r := by
    have hrx' : S'.RF.root x₁ = S'.RF.root r := by
      rw [hrx₁, rootedForest_root_eq_of_mem_R hRF' hrR']
    exact root_eq_of_new_root_eq hI hu hI' rfl (hS₀_sub_G hx₁₀) hrG hrx'
  have hrt₂_S : S.RF.root x₂ = S.RF.root r := by
    have hrx' : S'.RF.root x₂ = S'.RF.root r := by
      rw [hrx₂, rootedForest_root_eq_of_mem_R hRF' hrR']
    exact root_eq_of_new_root_eq hI hu hI' rfl (hS₀_sub_G hx₂₀) hrG hrx'
  have hr_in_W : ∀ x W, x ∈ S'.G.V → S'.RF.root x = r → W ∈ S₀.W_init → x ∈ W → r ∈ W := by
    intro x W hxV hrx hW hxW
    have hconn : S'.RF.F.Connected x r := by
      rw [← hrx]; exact (rootedForest_root_spec hRF' hxV).2
    obtain ⟨P, hP⟩ := connected_isPath hconn
    have havoid : ∀ z ∈ (S'.RF.F.walkVertices x P).dropLast,
        z ∉ S'.R ∧ z ∉ S₀.R ∧ z ∉ S'.isolatedVerts :=
      fun z hz => path_to_root_avoiding_R_iso hI' hD.hR_sub hR_sub' hP hrR' hz
    have hP_iso : ∀ z ∈ S'.RF.F.walkVertices x P, z ∉ S'.isolatedVerts := by
      intro z hz
      rw [walkVertices_eq_dropLast_append hP.1, List.mem_append, List.mem_singleton] at hz
      rcases hz with hdl | rfl
      · exact (havoid z hdl).2.2
      · exact hniso
    obtain ⟨hP₀, hwv_eq⟩ := walk_RF_avoiding_iso_to_S0 hI₀ hI' hD' hP.1 hP_iso
    have hb₀ : boundary S₀.W_init ⊆ S₀.R :=
      Finset.Subset.trans hI₀.hb_W Finset.subset_union_left
    exact walk_S0_avoiding_R_stays_in_piece hCov₀ hb₀ hP₀
      (fun z hz => (havoid z (hwv_eq ▸ hz)).2.1) W hW hxW
  have hrW₁ : r ∈ W₁ := hr_in_W x₁ W₁ hx₁V hrx₁ hW₁ hx₁W
  have hrW₂ : r ∈ W₂ := hr_in_W x₂ W₂ hx₂V hrx₂ hW₂ hx₂W
  have hb₀ : boundary S₀.W_init ⊆ S₀.R :=
    Finset.Subset.trans hI₀.hb_W Finset.subset_union_left
  have hWeq : W₁ = W₂ := unique_piece_of_not_R hb₀ hr_nR₀ hW₁ hW₂ hrW₁ hrW₂
  have hmid := (hMidInv x₁ hx₁V x₂ hx₂V).mpr (Or.inr ⟨hx₁₀, hx₂₀, hrt₁_S.trans hrt₂_S.symm,
    by simp [hx₁_nR₀, hx₂_nR₀], fun _ => ⟨W₁, hW₁, hx₁W, hWeq ▸ hx₂W⟩⟩)
  exact hmx₁.symm.trans (hmid.trans hmx₂)

lemma splitTargets_iso_edge_witness {thresh₀ K₀ thresh K : ℝ} {ℓ₀ : ℕ → ℝ} {S₀ S : LSFState}
    {v v' : ℕ} {St Sh : Finset ℕ}
    (hI₀ : LSFInvWith thresh₀ K₀ ℓ₀ S₀) (hCov₀ : S₀.W_init.biUnion (inducedEdges S₀.RF.F) = S₀.RF.F.E)
    (hI : LSFInvWith thresh K ℓ₀ S) (hu : S.G.UpdateIsValid (.split v v' St Sh)) (hD : LSFDerivedFrom S₀ S)
    {C_mid : MGraph} {m_mid : ℕ → ℕ}
    (hMidInv : ∀ x ∈ (applyLSFUpdate S (.split v v' St Sh)).G.V,
      ∀ y ∈ (applyLSFUpdate S (.split v v' St Sh)).G.V,
      m_mid x = m_mid y ↔
        x = y ∨ (x ∈ S₀.G.V ∧ y ∈ S₀.G.V ∧ S.RF.root x = S.RF.root y ∧
          (x ∈ S₀.R ↔ y ∈ S₀.R) ∧ (x ∉ S₀.R → ∃ W ∈ S₀.W_init, x ∈ W ∧ y ∈ W)))
    {r vT : ℕ}
    (hp : (r, vT) ∈ splitTargets S (applyLSFUpdate S (.split v v' St Sh)) C_mid m_mid)
    (hiso : r ∈ (applyLSFUpdate S (.split v v' St Sh)).isolatedVerts) :
    r = v' ∧ ∃ x w e : ℕ, ∃ b : Bool,
      x ∈ S₀.G.V ∧ x ∉ S₀.R ∧ m_mid x = vT ∧
      (∃ W ∈ S₀.W_init, x ∈ W ∧ w ∈ W) ∧
      e ∈ (St ∪ Sh) ∩ S.RF.F.E ∧ e ∈ (applyLSFUpdate S (.split v v' St Sh)).RF.F.E ∧
      (applyLSFUpdate S (.split v v' St Sh)).RF.F.src (e, b) = v' ∧
      (applyLSFUpdate S (.split v v' St Sh)).RF.F.dst (e, b) = w ∧
      w ∉ S₀.R ∧ S.RF.root x = S.RF.root w := by
  let u := Update.split v v' St Sh
  let S' := applyLSFUpdate S u
  have hsp := applyLSFUpdate_inv_with hI hu
  have hI' := hsp.1
  have hD' := lsfDerivedFrom_step hI hu hD
  have hR_sub' := hsp.2.2.2.2.2.2.2.2.1
  have hRF' := lsfInv_to_RS hI'
  have hRF := lsfInv_to_RS hI
  obtain ⟨hr_diff, x, hxV, hx₀, hx_nR₀, hmx, hrx, W, hW, hxW⟩ :=
    splitTarget_mem_witness hI hMidInv hD.hR_sub hp
  have hr_diff' := Finset.mem_sdiff.mp hr_diff
  have hr_eq : r = v' := by
    have hiso' : r ∈ insert v' S.isolatedVerts := hiso
    rcases Finset.mem_insert.mp hiso' with rfl | hmemS
    · rfl
    · exact absurd (Finset.mem_union_right _ hmemS) hr_diff'.2
  have hx_in_S : x ∈ S.G.V := by
    rw [hI.hGV_eq, Finset.mem_union]; left
    rw [hI.hTV, hD.hG₀_eq, ← hD.hS₀_G]; exact hx₀
  have hxv'_ne : x ≠ v' := fun h => hu.2.1 (h ▸ hx_in_S)
  have hrx_v' : S'.RF.root x = v' := hr_eq ▸ hrx
  have hrR'_v' : v' ∈ S'.R := hr_eq ▸ hr_diff'.1
  have hconn : S'.RF.F.Connected x v' := by
    rw [← hrx_v']; exact (rootedForest_root_spec hRF' hxV).2
  obtain ⟨P, hP⟩ := connected_isPath hconn
  have hQ_walk : S'.RF.F.IsWalk v' x (walkRev P) := isWalk_walkRev hP.1
  have hQ_nd : (S'.RF.F.walkVertices v' (walkRev P)).Nodup := by
    rw [walkVertices_walkRev hP.1]
    exact List.nodup_reverse.mpr hP.2
  cases hQ_eq : walkRev P with
  | nil =>
    rw [hQ_eq] at hQ_walk
    cases hQ_walk
    exact absurd rfl hxv'_ne
  | cons step Q' =>
    rw [hQ_eq] at hQ_walk hQ_nd
    cases hQ_walk with
    | cons he_step hsrc_step hrest =>
      let w := S'.RF.F.dst step
      have hw_avoid : ∀ z ∈ S'.RF.F.walkVertices w Q',
          z ∈ S'.RF.F.walkVertices x P ∧ z ≠ v' := by
        intro z hz
        have hzQ : z ∈ S'.RF.F.walkVertices v' (step :: Q') := by
          simp only [MGraph.walkVertices, List.map_cons, List.mem_cons]
          right; simpa [MGraph.walkVertices] using hz
        have hzne : z ≠ v' := by
          rw [MGraph.walkVertices, List.map_cons, List.nodup_cons] at hQ_nd
          intro rfl
          exact hQ_nd.1 (by simpa [MGraph.walkVertices] using hz)
        have hz_rev : z ∈ (S'.RF.F.walkVertices x P).reverse := by
          rw [← walkVertices_walkRev hP.1, hQ_eq]; exact hzQ
        exact ⟨List.mem_reverse.mp hz_rev, hzne⟩
      have hQ'_iso : ∀ z ∈ S'.RF.F.walkVertices w Q',
          z ∉ S'.R ∧ z ∉ S₀.R ∧ z ∉ S'.isolatedVerts := by
        intro z hz
        obtain ⟨hzP, hzne⟩ := hw_avoid z hz
        have hconn_z : S'.RF.F.Connected z v' := connected_of_mem_walkVertices hP.1 hzP
        have hz_nR' : z ∉ S'.R := by
          intro hzR
          have heq := rootedForest_root_eq_of_connected hRF'
            (hRF'.2.2.1 hzR) (hRF'.2.2.1 hrR'_v') hconn_z
          rw [rootedForest_root_eq_of_mem_R hRF' hzR,
            rootedForest_root_eq_of_mem_R hRF' hrR'_v'] at heq
          exact hzne heq
        exact ⟨hz_nR', fun h => hz_nR' (hR_sub' (hD.hR_sub h)),
          fun h => hz_nR' (Finset.mem_union_right _ h)⟩
      have hw_nR₀ : w ∉ S₀.R := (hQ'_iso w (by simp [MGraph.walkVertices])).2.1
      have hw_niso : w ∉ S'.isolatedVerts := (hQ'_iso w (by simp [MGraph.walkVertices])).2.2
      have hQ'rev_walk : S'.RF.F.IsWalk x w (walkRev Q') := isWalk_walkRev hrest
      have hQ'rev_iso : ∀ z ∈ S'.RF.F.walkVertices x (walkRev Q'), z ∉ S'.isolatedVerts := by
        intro z hz
        rw [walkVertices_walkRev hrest, List.mem_reverse] at hz
        exact (hQ'_iso z hz).2.2
      obtain ⟨hQ'rev₀, hQ'rev_wv⟩ := walk_RF_avoiding_iso_to_S0 hI₀ hI' hD' hQ'rev_walk hQ'rev_iso
      have hQ'rev_nR₀ : ∀ z ∈ (S₀.RF.F.walkVertices x (walkRev Q')).dropLast, z ∉ S₀.R := by
        intro z hz
        have hz' : z ∈ S'.RF.F.walkVertices x (walkRev Q') :=
          hQ'rev_wv ▸ List.mem_of_mem_dropLast hz
        rw [walkVertices_walkRev hrest, List.mem_reverse] at hz'
        exact (hQ'_iso z hz').2.1
      have hb₀ : boundary S₀.W_init ⊆ S₀.R :=
        Finset.Subset.trans hI₀.hb_W Finset.subset_union_left
      have hwW : w ∈ W :=
        walk_S0_avoiding_R_stays_in_piece hCov₀ hb₀ hQ'rev₀ hQ'rev_nR₀ W hW hxW
      have hwG : w ∈ S.G.V := by
        have hEnd' : S'.RF.F.tail step.1 ∈ S'.G.V ∧ S'.RF.F.head step.1 ∈ S'.G.V := by
          have := hRF'.1.1 step.1 he_step; rwa [hRF'.2.1] at this
        have hwV' : w ∈ S'.G.V := by
          dsimp only [w]
          rcases step with ⟨se, sb⟩
          cases sb
          · exact hEnd'.1
          · exact hEnd'.2
        rw [hI.hGV_eq, Finset.mem_union]; left
        have hwT' := (Finset.mem_union.mp (hI'.hGV_eq ▸ hwV')).resolve_right hw_niso
        exact hsp.2.2.2.1 ▸ hwT'
      have hconn_S : S.RF.F.Connected w x := by
        have hconn' := forest_connected_stepProj hI hu hI' rfl ⟨Q', hrest⟩
        rwa [stepProj_old_V hu hwG, stepProj_old_V hu hx_in_S] at hconn'
      have hroot_wx : S.RF.root x = S.RF.root w :=
        rootedForest_root_eq_of_connected hRF hx_in_S hwG (connected_symm hconn_S)
      have he_S : step.1 ∈ S.RF.F.E := hsp.2.2.2.2.2.2.2.2.2.1 he_step
      have he_Es : step.1 ∈ St ∪ Sh := by
        have hT₀_E : step.1 ∈ S.T₀.E := Finset.sdiff_subset he_S
        have hT_old_V : S.T_cur.tail step.1 ∈ S.G.V ∧ S.T_cur.head step.1 ∈ S.G.V := by
          rw [← hI.hT_cur_V]; exact hI.hT_cur_forest.1 step.1 (hI.hT_cur_E ▸ hT₀_E)
        have ht_ne : S.T_cur.tail step.1 ≠ v' := fun h => hu.2.1 (h ▸ hT_old_V.1)
        have hh_ne : S.T_cur.head step.1 ≠ v' := fun h => hu.2.1 (h ▸ hT_old_V.2)
        have he_end : S'.RF.F.tail step.1 = v' ∨ S'.RF.F.head step.1 = v' := by
          cases hb : step.2 <;>
            simp only [MGraph.src, hb, Bool.false_eq_true, ↓reduceIte] at hsrc_step
          · right; exact hsrc_step
          · left; exact hsrc_step
        rcases he_end with h | h
        · change (S.T_cur.applyUpdate (.split v v' St Sh)).tail step.1 = v' at h
          dsimp only [MGraph.applyUpdate] at h
          split_ifs at h with hc
          · exact Finset.mem_union_left _ hc.1
          · exact absurd h ht_ne
        · change (S.T_cur.applyUpdate (.split v v' St Sh)).head step.1 = v' at h
          dsimp only [MGraph.applyUpdate] at h
          split_ifs at h with hc
          · exact Finset.mem_union_right _ hc.1
          · exact absurd h hh_ne
      exact ⟨hr_eq, x, w, step.1, step.2, hx₀, hx_nR₀, hmx, ⟨W, hW, hxW, hwW⟩,
        Finset.mem_inter.mpr ⟨he_Es, he_S⟩, he_step, hsrc_step, rfl, hw_nR₀, hroot_wx⟩

def updateSplitTag : Update → ℕ
  | .split _ _ _ _ => 1
  | _ => 0

noncomputable def updateForestSplitCard (S : LSFState) : Update → ℕ
  | .split _ _ St Sh => ((St ∪ Sh) ∩ S.RF.F.E).card
  | _ => 0

lemma splitTargets_card_le {thresh₀ K₀ thresh K : ℝ} {ℓ₀ : ℕ → ℝ} {S₀ S : LSFState} {u : Update}
    (hI₀ : LSFInvWith thresh₀ K₀ ℓ₀ S₀) (hCov₀ : S₀.W_init.biUnion (inducedEdges S₀.RF.F) = S₀.RF.F.E)
    (hI : LSFInvWith thresh K ℓ₀ S) (hu : S.G.UpdateIsValid u) (hD : LSFDerivedFrom S₀ S)
    {C_mid : MGraph} {m_mid : ℕ → ℕ}
    (hMidInv : ∀ x ∈ (applyLSFUpdate S u).G.V, ∀ y ∈ (applyLSFUpdate S u).G.V,
      m_mid x = m_mid y ↔
        x = y ∨ (x ∈ S₀.G.V ∧ y ∈ S₀.G.V ∧ S.RF.root x = S.RF.root y ∧
          (x ∈ S₀.R ↔ y ∈ S₀.R) ∧ (x ∉ S₀.R → ∃ W ∈ S₀.W_init, x ∈ W ∧ y ∈ W))) :
    let S' := applyLSFUpdate S u
    (splitTargets S S' C_mid m_mid).card ≤
      (S'.R \ S.R).card + updateForestSplitCard S u := by
  classical
  intro S'
  let tgts := splitTargets S S' C_mid m_mid
  let tgts₁ := tgts.filter fun p => p.1 ∉ S'.isolatedVerts
  let tgts₂ := tgts.filter fun p => p.1 ∈ S'.isolatedVerts
  have hsplit_card : tgts.card = tgts₁.card + tgts₂.card := by
    have hunion : tgts = tgts₁ ∪ tgts₂ := by
      ext p; by_cases h : p.1 ∈ S'.isolatedVerts <;> simp [tgts₁, tgts₂, h]
    have hdisj : Disjoint tgts₁ tgts₂ :=
      Finset.disjoint_filter.mpr fun _ _ h1 h2 => h1 h2
    rw [hunion, Finset.card_union_of_disjoint hdisj]
  have hcard₁ : tgts₁.card ≤ (S'.R \ S.R).card := by
    refine Finset.card_le_card_of_injOn Prod.fst (fun p hp => ?_) (fun p₁ hp₁ p₂ hp₂ heq => ?_)
    · rw [Finset.mem_coe, Finset.mem_filter] at hp
      have hp' := hp.1
      dsimp only [tgts, splitTargets] at hp'
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hp').1).1
    · rw [Finset.mem_coe, Finset.mem_filter] at hp₁ hp₂
      rcases p₁ with ⟨r₁, v₁⟩
      rcases p₂ with ⟨r₂, v₂⟩
      dsimp only at heq
      subst heq
      congr 1
      exact splitTargets_same_fst_not_iso hI₀ hCov₀ hI hu hD hMidInv hp₁.1 hp₂.1 hp₁.2
  have hcard₂ : tgts₂.card ≤ updateForestSplitCard S u := by
    cases u with
    | delete e₀ =>
      have hem : tgts₂ = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro p hp
        rw [Finset.mem_filter] at hp
        have hr_diff : p.1 ∈ S'.R \ S.R :=
          (Finset.mem_product.mp (Finset.mem_filter.mp hp.1).1).1
        have hiso : p.1 ∈ S.isolatedVerts := hp.2
        exact (Finset.mem_sdiff.mp hr_diff).2 (Finset.mem_union_right _ hiso)
      simp [hem, updateForestSplitCard]
    | insert e₀ a b =>
      have hem : tgts₂ = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro p hp
        rw [Finset.mem_filter] at hp
        have hr_diff : p.1 ∈ S'.R \ S.R :=
          (Finset.mem_product.mp (Finset.mem_filter.mp hp.1).1).1
        have hiso : p.1 ∈ S.isolatedVerts := hp.2
        exact (Finset.mem_sdiff.mp hr_diff).2 (Finset.mem_union_right _ hiso)
      simp [hem, updateForestSplitCard]
    | split v v' St Sh =>
      dsimp only [updateForestSplitCard]
      have hsp := applyLSFUpdate_inv_with hI hu
      have hRF' := lsfInv_to_RS hsp.1
      have hEx : ∀ p ∈ tgts₂, ∃ e ∈ (St ∪ Sh) ∩ S.RF.F.E,
          e ∈ S'.RF.F.E ∧ ∃ w b x, x ∈ S₀.G.V ∧ x ∉ S₀.R ∧ m_mid x = p.2 ∧
            (∃ W ∈ S₀.W_init, x ∈ W ∧ w ∈ W) ∧
            S'.RF.F.src (e, b) = v' ∧ S'.RF.F.dst (e, b) = w ∧ w ∉ S₀.R ∧
            S.RF.root x = S.RF.root w := by
        intro p hp
        rw [Finset.mem_filter] at hp
        obtain ⟨_, x, w, e, b, hx₀, hx_nR₀, hmx, hW, he_mem, heF', hsrc, hdst, hw_nR₀, hrt⟩ :=
          splitTargets_iso_edge_witness hI₀ hCov₀ hI hu hD hMidInv hp.1 hp.2
        exact ⟨e, he_mem, heF', w, b, x, hx₀, hx_nR₀, hmx, hW, hsrc, hdst, hw_nR₀, hrt⟩
      let pickE : ℕ × ℕ → ℕ := fun p => if h : p ∈ tgts₂ then (hEx p h).choose else 0
      refine Finset.card_le_card_of_injOn pickE (fun p hp => ?_) (fun p₁ hp₁ p₂ hp₂ heq => ?_)
      · simp only [Finset.mem_coe] at hp
        dsimp only [pickE]
        split_ifs
        exact (hEx p hp).choose_spec.1
      · simp only [Finset.mem_coe] at hp₁ hp₂
        dsimp only [pickE] at heq
        split_ifs at heq
        · obtain ⟨_, _, w₁, b₁, x₁, hx₁₀, hx₁_nR₀, hmx₁, ⟨W₁, hW₁, hx₁W, hw₁W⟩,
            hsrc₁, hdst₁, hw₁_nR₀, hrt₁⟩ := (hEx p₁ hp₁).choose_spec
          obtain ⟨_, heF'₂, w₂, b₂, x₂, hx₂₀, hx₂_nR₀, hmx₂, ⟨W₂, hW₂, hx₂W, hw₂W⟩,
            hsrc₂, hdst₂, hw₂_nR₀, hrt₂⟩ := (hEx p₂ hp₂).choose_spec
          rw [heq] at hsrc₁ hdst₁
          have hb_eq : b₁ = b₂ := by
            by_contra hne
            have hnoSelf := isForest_no_selfLoop hRF'.1 heF'₂
            cases b₁ <;> cases b₂
            · exact hne rfl
            · exact hnoSelf (hsrc₂.trans hsrc₁.symm)
            · exact hnoSelf (hsrc₁.trans hsrc₂.symm)
            · exact hne rfl
          have hw_eq : w₁ = w₂ := by rw [← hdst₁, ← hdst₂, hb_eq]
          have hb₀ : boundary S₀.W_init ⊆ S₀.R :=
            Finset.Subset.trans hI₀.hb_W Finset.subset_union_left
          have hWeq : W₁ = W₂ :=
            unique_piece_of_not_R hb₀ hw₁_nR₀ hW₁ hW₂ hw₁W (hw_eq ▸ hw₂W)
          have hrt_eq : S.RF.root x₁ = S.RF.root x₂ := hrt₁.trans (by rw [hw_eq, hrt₂])
          have hx₁V' : x₁ ∈ S'.G.V := by
            rw [hsp.1.hGV_eq, Finset.mem_union]; left
            rw [hsp.1.hTV, hsp.2.2.1, hD.hG₀_eq, ← hD.hS₀_G]; exact hx₁₀
          have hx₂V' : x₂ ∈ S'.G.V := by
            rw [hsp.1.hGV_eq, Finset.mem_union]; left
            rw [hsp.1.hTV, hsp.2.2.1, hD.hG₀_eq, ← hD.hS₀_G]; exact hx₂₀
          have hmid := (hMidInv x₁ hx₁V' x₂ hx₂V').mpr (Or.inr ⟨hx₁₀, hx₂₀, hrt_eq,
            by simp [hx₁_nR₀, hx₂_nR₀], fun _ => ⟨W₁, hW₁, hx₁W, hWeq ▸ hx₂W⟩⟩)
          have hf₁ : p₁.1 = v' :=
            (splitTargets_iso_edge_witness hI₀ hCov₀ hI hu hD hMidInv
              (Finset.mem_filter.mp hp₁).1 (Finset.mem_filter.mp hp₁).2).1
          have hf₂ : p₂.1 = v' :=
            (splitTargets_iso_edge_witness hI₀ hCov₀ hI hu hD hMidInv
              (Finset.mem_filter.mp hp₂).1 (Finset.mem_filter.mp hp₂).2).1
          exact Prod.ext (hf₁.trans hf₂.symm) (hmx₁.symm.trans (hmid.trans hmx₂))
  rw [hsplit_card]
  exact Nat.add_le_add hcard₁ hcard₂

lemma split_forest_edges_le_maxDeg {thresh K : ℝ} {ℓ₀ : ℕ → ℝ} {S₀ S : LSFState}
    {v v' : ℕ} {St Sh : Finset ℕ}
    (hI : LSFInvWith thresh K ℓ₀ S) (hu : S.G.UpdateIsValid (.split v v' St Sh))
    (hD : LSFDerivedFrom S₀ S) :
    ((St ∪ Sh) ∩ S.RF.F.E).card ≤ S₀.G.maxDeg := by
  have hRF := lsfInv_to_RS hI
  let u₀ := S.origVert v
  have hu₀_V : u₀ ∈ S₀.G.V := by
    have hv_T : u₀ ∈ S.T₀.V := by
      dsimp only [u₀]
      rcases Finset.mem_union.mp (hI.hGV_eq ▸ hu.1) with hvT | hvI
      · rw [hI.horig_id v hvT]; exact hvT
      · exact upClosure_subset (hldAuxTree_isRootedTree hI.hT₀) hI.hR₀_sub (hI.horig_split v hvI)
    rw [hD.hS₀_G, ← hD.hG₀_eq, ← hI.hTV]
    exact hv_T
  have hsub : (St ∪ Sh) ∩ S.RF.F.E ⊆
      (S₀.G.E.filter fun e => S₀.G.tail e = u₀) ∪ (S₀.G.E.filter fun e => S₀.G.head e = u₀) := by
    intro e he
    rw [Finset.mem_inter] at he
    have heG : e ∈ S.G.E := hRF.2.2.2.2.2.1 he.2
    have hnot_ins : e ∉ S.insertedEdges := by
      intro hins
      have hw := hI.hins_wstr e hins
      have hth := hRF.2.2.2.2.2.2 e he.2
      have hconn : S.RF.F.Connected (S.RF.F.tail e) (S.RF.F.head e) :=
        ⟨[(e, true)], .cons he.2 rfl (.nil _)⟩
      have heq := rootedForest_root_eq_of_connected hRF
        (hRF.2.2.1 (hth.1 ▸ hw.2.1)) (hRF.2.2.1 (hth.2 ▸ hw.2.2)) hconn
      rw [rootedForest_root_eq_of_mem_R hRF (hth.1 ▸ hw.2.1),
        rootedForest_root_eq_of_mem_R hRF (hth.2 ▸ hw.2.2)] at heq
      exact isForest_no_selfLoop hRF.1 he.2 heq
    have heG₀ : e ∈ S₀.G.E := by
      rw [hD.hS₀_G, ← hD.hG₀_eq]; exact (hI.hsurv_edge e heG hnot_ins).1
    have horig := hI.horig_G_nins e heG hnot_ins
    have hG₀_t : S.origVert (S.G.tail e) = S₀.G.tail e := by
      rw [horig.1, hD.hS₀_G, hD.hG₀_eq]
    have hG₀_h : S.origVert (S.G.head e) = S₀.G.head e := by
      rw [horig.2, hD.hS₀_G, hD.hG₀_eq]
    rw [Finset.mem_union]
    rcases hu.2.2.2 e he.1 with ht | hh
    · left; rw [Finset.mem_filter]; exact ⟨heG₀, by rw [← hG₀_t, ht]⟩
    · right; rw [Finset.mem_filter]; exact ⟨heG₀, by rw [← hG₀_h, hh]⟩
  calc ((St ∪ Sh) ∩ S.RF.F.E).card
      ≤ ((S₀.G.E.filter fun e => S₀.G.tail e = u₀) ∪
          (S₀.G.E.filter fun e => S₀.G.head e = u₀)).card := Finset.card_le_card hsub
    _ ≤ (S₀.G.E.filter fun e => S₀.G.tail e = u₀).card +
          (S₀.G.E.filter fun e => S₀.G.head e = u₀).card := Finset.card_union_le _ _
    _ = S₀.G.deg u₀ := rfl
    _ ≤ S₀.G.maxDeg := Finset.le_sup (f := S₀.G.deg) hu₀_V

/-! ## 3. Packaged single-update and multi-update quotient step -/

/-- State of the dynamically maintained vertex-split quotient graph `\tilde{C}`. -/
structure TildeState where
  C : MGraph
  m : ℕ → ℕ
  nextVid : ℕ

/-- Dynamic invariant tying `TildeState` to `S₀` and `S`. -/
structure TildeInv (S₀ S : LSFState) (ts : TildeState) : Prop where
  hC_val : ts.C.IsValid
  hCE_sub : ts.C.E ⊆ S.G.E \ S.RF.F.E
  hV_sub : ∀ x ∈ S.G.V, ts.m x ∈ ts.C.V
  hEnds : ∀ e ∈ ts.C.E, ts.C.tail e = ts.m (S.G.tail e) ∧ ts.C.head e = ts.m (S.G.head e)
  hRPI : RootPieceInv S₀ S ts.m
  hFresh : ∀ v ∈ ts.C.V, v < ts.nextVid

/-- Initial `TildeState` for `S₀` built from `tildeC0Base S₀`. -/
noncomputable def initTildeState (S₀ : LSFState) : TildeState where
  C := tildeC0Base S₀
  m := tildeV0 S₀
  nextVid := (tildeC0Base S₀).V.sup id + 1

lemma initTildeState_inv {thresh₀ K₀ : ℝ} {ℓ₀ : ℕ → ℝ} {S₀ : LSFState}
    (hI₀ : LSFInvWith thresh₀ K₀ ℓ₀ S₀) (hCov₀ : S₀.W_init.biUnion (inducedEdges S₀.RF.F) = S₀.RF.F.E) :
    TildeInv S₀ S₀ (initTildeState S₀) := by
  have hRF₀ := lsfInv_to_RS hI₀
  have hb₀ : boundary S₀.W_init ⊆ S₀.R :=
    Finset.Subset.trans hI₀.hb_W Finset.subset_union_left
  refine ⟨?_, ?_, ?_, ?_, tildeV0_rootPieceInv hRF₀ hCov₀ hb₀, ?_⟩
  · intro e he
    rw [initTildeState, tildeC0Base, Finset.mem_sdiff] at he
    have hth := hI₀.hG_val e he.1
    exact ⟨Finset.mem_image_of_mem _ hth.1, Finset.mem_image_of_mem _ hth.2⟩
  · intro e he
    exact he
  · intro x hx
    exact Finset.mem_image_of_mem _ hx
  · intro _ _
    exact ⟨rfl, rfl⟩
  · intro v hv
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hv)

lemma batchSplitCount_append (U₁ U₂ : List Update) :
    batchSplitCount (U₁ ++ U₂) = batchSplitCount U₁ + batchSplitCount U₂ := by
  simp [batchSplitCount, List.countP_append]

lemma batchSplitCount_le_length (U : List Update) :
    batchSplitCount U ≤ U.length :=
  List.countP_le_length

lemma applyUpdate_V_card_eq_of_isDelOrSplit {G : MGraph} {u : Update}
    (hu : G.UpdateIsValid u) (hds : isDelOrSplit u) :
    (G.applyUpdate u).V.card = G.V.card + (if isSplit u then 1 else 0) := by
  cases u with
  | insert _ _ _ => exact absurd hds id
  | delete _ => simp [MGraph.applyUpdate, isSplit]
  | split _ _ _ _ =>
    simp [MGraph.applyUpdate, isSplit, Finset.card_insert_of_notMem hu.2.1]

lemma applyBatch_V_card_eq_of_isDelOrSplit {G : MGraph} {U : List Update}
    (hB : G.BatchIsValid U) (hds : ∀ u ∈ U, isDelOrSplit u) :
    (G.applyBatch U).V.card = G.V.card + batchSplitCount U := by
  induction U generalizing G with
  | nil => simp [MGraph.applyBatch, batchSplitCount]
  | cons u U ih =>
    rw [MGraph.BatchIsValid] at hB
    have hu_ds : isDelOrSplit u := hds u List.mem_cons_self
    have hU_ds : ∀ x ∈ U, isDelOrSplit x := fun x hx => hds x (List.mem_cons_of_mem _ hx)
    simp only [MGraph.applyBatch, List.foldl_cons, batchSplitCount, List.countP_cons]
    rw [← MGraph.applyBatch, ih hB.2 hU_ds, applyUpdate_V_card_eq_of_isDelOrSplit hB.1 hu_ds]
    cases u with
    | insert _ _ _ => exact absurd hu_ds id
    | delete _ => simp [batchSplitCount, isSplit]
    | split _ _ _ _ => simp [batchSplitCount, isSplit]; omega

/-- Process one valid update `u` on `S` and `\tilde{C}`: returns `(U_C, ts', S')`. -/
noncomputable def tildeStepSingle (S : LSFState) (ts : TildeState) (u : Update) :
    List Update × TildeState × LSFState :=
  let S' := applyLSFUpdate S u
  let U_del := delStepC ts.C u
  let C_del := ts.C.applyBatch U_del
  let spA := splitStepA ts.m S.G C_del u ts.nextVid
  let C_mid := C_del.applyBatch spA.1
  let spB := rootSplitStep S S' C_mid spA.2.1 spA.2.2
  let C' := C_mid.applyBatch spB.1
  (U_del ++ spA.1 ++ spB.1, ⟨C', spB.2.1, spB.2.2⟩, S')

lemma tildeStepSingle_spec {thresh₀ K₀ thresh K : ℝ} {ℓ₀ : ℕ → ℝ} {S₀ S : LSFState}
    {ts : TildeState} {u : Update}
    (hI₀ : LSFInvWith thresh₀ K₀ ℓ₀ S₀) (hCov₀ : S₀.W_init.biUnion (inducedEdges S₀.RF.F) = S₀.RF.F.E)
    (hI : LSFInvWith thresh K ℓ₀ S) (hu : S.G.UpdateIsValid u) (hD : LSFDerivedFrom S₀ S)
    (hT : TildeInv S₀ S ts) :
    let res := tildeStepSingle S ts u
    let U_C := res.1
    let ts' := res.2.1
    let S' := res.2.2
    S' = applyLSFUpdate S u ∧
    TildeInv S₀ S' ts' ∧
    ts.C.BatchIsValid U_C ∧
    ts'.C = ts.C.applyBatch U_C ∧
    (∀ op ∈ U_C, isDelOrSplit op) ∧
    batchSplitCount U_C ≤ updateSplitTag u + (S'.R \ S.R).card + updateForestSplitCard S u ∧
    U_C.length ≤ 1 + (S'.R \ S.R).card + updateForestSplitCard S u ∧
    ts'.C.V.card = ts.C.V.card + batchSplitCount U_C := by
  intro res U_C ts' S'
  have hA := delStepC_splitStepA_spec hI hu hD hT.hC_val hT.hCE_sub
    hT.hV_sub hT.hEnds hT.hRPI hT.hFresh
  rcases hA with ⟨hA_del, hA_sp, hA_BV, hA_val, hA_E,
    hA_Vsub, hA_ends, hA_fresh, _, hA_midInv⟩
  set U_del := delStepC ts.C u
  set C_del := ts.C.applyBatch U_del
  set spA := splitStepA ts.m S.G C_del u ts.nextVid
  set C_mid := C_del.applyBatch spA.1
  set spB := rootSplitStep S S' C_mid spA.2.1 spA.2.2
  have hB := rootSplitStep_spec hI hu hD hA_val
    hA_Vsub hA_ends hA_midInv hA_fresh
  rcases hB with ⟨hB_len, hB_BV, hB_val, hB_E,
    hB_Vsub, hB_ends, hB_fresh, _, hB_RPI⟩
  have hBV_all : ts.C.BatchIsValid (U_del ++ spA.1 ++ spB.1) := by
    rw [batchIsValid_append]
    refine ⟨hA_BV, ?_⟩
    rw [applyBatch_append]
    exact hB_BV
  have hC'_eq : ts'.C = ts.C.applyBatch U_C := by
    dsimp only [ts', U_C, res, tildeStepSingle]
    rw [List.append_assoc, applyBatch_append, ← applyBatch_append]
  have hds_Udel : ∀ op ∈ U_del, isDelOrSplit op := by
    intro op hop
    cases u with
    | delete e₀ =>
      dsimp only [U_del, delStepC] at hop
      split_ifs at hop
      · rw [List.mem_singleton] at hop; subst hop; exact trivial
      · contradiction
    | insert _ _ _ => simp [U_del, delStepC] at hop
    | split _ _ _ _ => simp [U_del, delStepC] at hop
  have hds_spA : ∀ op ∈ spA.1, isDelOrSplit op := by
    intro op hop
    cases u with
    | delete _ => simp [spA, splitStepA] at hop
    | insert _ _ _ => simp [spA, splitStepA] at hop
    | split _ _ _ _ =>
      dsimp only [spA, splitStepA] at hop
      rw [List.mem_singleton] at hop; subst hop; exact trivial
  have hds_spB : ∀ op ∈ spB.1, isDelOrSplit op := by
    intro op hop
    dsimp only [spB, rootSplitStep] at hop
    rw [List.mem_map] at hop
    obtain ⟨vid, _, rfl⟩ := hop
    exact trivial
  have hds_all : ∀ op ∈ U_C, isDelOrSplit op := by
    intro op hop
    simp only [U_C, res, tildeStepSingle, List.mem_append] at hop
    rcases hop with (h | h) | h
    · exact hds_Udel op h
    · exact hds_spA op h
    · exact hds_spB op h
  have htgts_le := splitTargets_card_le hI₀ hCov₀ hI hu hD hA_midInv (C_mid := C_mid)
  have hsc_del : batchSplitCount U_del = 0 := by
    rw [batchSplitCount, List.countP_eq_zero]
    intro op hop
    cases u with
    | delete _ =>
      dsimp only [U_del, delStepC] at hop
      split_ifs at hop
      · rw [List.mem_singleton] at hop; subst hop; simp [isSplit]
      · contradiction
    | insert _ _ _ => simp [U_del, delStepC] at hop
    | split _ _ _ _ => simp [U_del, delStepC] at hop
  have hsc_all : batchSplitCount U_C ≤
      updateSplitTag u + (S'.R \ S.R).card + updateForestSplitCard S u := by
    have hEq : U_C = U_del ++ spA.1 ++ spB.1 := rfl
    rw [hEq, batchSplitCount_append, batchSplitCount_append, hsc_del, zero_add]
    have h1 : batchSplitCount spA.1 ≤ updateSplitTag u := by
      refine le_trans (batchSplitCount_le_length spA.1) ?_
      cases u <;> exact hA_sp
    have h2 : batchSplitCount spB.1 ≤ (splitTargets S S' C_mid spA.2.1).card :=
      le_trans (batchSplitCount_le_length spB.1) (le_of_eq hB_len)
    have h3 : batchSplitCount spA.1 + batchSplitCount spB.1 ≤
        updateSplitTag u + ((S'.R \ S.R).card + updateForestSplitCard S u) :=
      Nat.add_le_add h1 (le_trans h2 htgts_le)
    omega
  have hlen_all : U_C.length ≤ 1 + (S'.R \ S.R).card + updateForestSplitCard S u := by
    have hEq : U_C = U_del ++ spA.1 ++ spB.1 := rfl
    rw [hEq, List.length_append, List.length_append]
    have h2 : spB.1.length ≤ (S'.R \ S.R).card + updateForestSplitCard S u :=
      hB_len ▸ htgts_le
    have h01 : U_del.length + spA.1.length ≤ 1 := by
      cases u with
      | delete _ => simp only [U_del, delStepC, spA, splitStepA]; split_ifs <;> simp
      | insert _ _ _ => simp [U_del, delStepC, spA, splitStepA]
      | split _ _ _ _ => simp [U_del, delStepC, spA, splitStepA]
    omega
  have hV_card : ts'.C.V.card = ts.C.V.card + batchSplitCount U_C := by
    rw [hC'_eq]
    exact applyBatch_V_card_eq_of_isDelOrSplit hBV_all hds_all
  refine ⟨rfl, ⟨hB_val, hB_E ▸ hA_E, hB_Vsub, hB_ends, hB_RPI, hB_fresh⟩,
    hBV_all, hC'_eq, hds_all, hsc_all, hlen_all, hV_card⟩

/-- Process a valid batch `U` on `S` and `\tilde{C}`: returns `(U_C, ts', S')`. -/
noncomputable def tildeStepBatch (S : LSFState) (ts : TildeState) :
    List Update → List Update × TildeState × LSFState
  | [] => ([], ts, S)
  | u :: rest =>
    let r1 := tildeStepSingle S ts u
    let r2 := tildeStepBatch r1.2.2 r1.2.1 rest
    (r1.1 ++ r2.1, r2.2.1, r2.2.2)

lemma tildeStepBatch_spec {thresh₀ K₀ thresh K : ℝ} {ℓ₀ : ℕ → ℝ} {S₀ S : LSFState} {ts : TildeState}
    (hI₀ : LSFInvWith thresh₀ K₀ ℓ₀ S₀) (hCov₀ : S₀.W_init.biUnion (inducedEdges S₀.RF.F) = S₀.RF.F.E)
    (hI : LSFInvWith thresh K ℓ₀ S) (hD : LSFDerivedFrom S₀ S) (hT : TildeInv S₀ S ts)
    {U : List Update} (hBU : S.G.BatchIsValid U) :
    let res := tildeStepBatch S ts U
    let U_C := res.1
    let ts' := res.2.1
    let S' := res.2.2
    S' = applyLSFBatch S U ∧
    LSFInvWith thresh K ℓ₀ S' ∧
    LSFDerivedFrom S₀ S' ∧
    TildeInv S₀ S' ts' ∧
    S.R ⊆ S'.R ∧
    ts.C.BatchIsValid U_C ∧
    ts'.C = ts.C.applyBatch U_C ∧
    (∀ op ∈ U_C, isDelOrSplit op) ∧
    batchSplitCount U_C ≤ U.length * (S₀.G.maxDeg + 1) + (S'.R \ S.R).card ∧
    U_C.length ≤ U.length * (S₀.G.maxDeg + 1) + (S'.R \ S.R).card ∧
    ((U_C.length : ℝ) ≤ (U.length : ℝ) * ((S₀.G.maxDeg : ℝ) + 1 +
      56 * (Real.log ((S₀.G₀.n : ℝ) + 2)) ^ 2)) ∧
    ts'.C.V.card = ts.C.V.card + batchSplitCount U_C := by
  induction U generalizing S ts with
  | nil =>
    dsimp only [tildeStepBatch]
    refine ⟨rfl, hI, hD, hT, Finset.Subset.rfl, trivial, rfl, fun _ h => by simp at h,
      by simp [batchSplitCount], by simp, by simp, by simp [batchSplitCount]⟩
  | cons u rest ih =>
    rw [MGraph.BatchIsValid] at hBU
    obtain ⟨hu, hB_rest⟩ := hBU
    have hsp := applyLSFUpdate_inv_with hI hu
    have h1 := tildeStepSingle_spec hI₀ hCov₀ hI hu hD hT
    rcases h1 with ⟨h1_S, h1_T, h1_BV, h1_C, h1_ds, h1_sc, h1_len, h1_V⟩
    set r1 := tildeStepSingle S ts u
    have hS1_G : r1.2.2.G = S.G.applyUpdate u := h1_S ▸ hsp.2.1
    have hI1 : LSFInvWith thresh K ℓ₀ r1.2.2 := h1_S ▸ hsp.1
    have hD1 : LSFDerivedFrom S₀ r1.2.2 := h1_S ▸ lsfDerivedFrom_step hI hu hD
    have hR_01 : S.R ⊆ r1.2.2.R := h1_S ▸ hsp.2.2.2.2.2.2.2.2.1
    have h2 := ih hI1 hD1 h1_T (hS1_G ▸ hB_rest)
    rcases h2 with ⟨h2_S, h2_I, h2_D, h2_T, h2_R, h2_BV, h2_C, h2_ds, h2_sc, h2_len, h2_lenR, h2_V⟩
    set r2 := tildeStepBatch r1.2.2 r1.2.1 rest
    have hR_02 : S.R ⊆ r2.2.2.R := Finset.Subset.trans hR_01 h2_R
    have hdiff_split : (r1.2.2.R \ S.R).card + (r2.2.2.R \ r1.2.2.R).card =
        (r2.2.2.R \ S.R).card := by
      rw [Finset.card_sdiff_of_subset hR_01, Finset.card_sdiff_of_subset h2_R,
        Finset.card_sdiff_of_subset hR_02]
      have hc1 : S.R.card ≤ r1.2.2.R.card := Finset.card_le_card hR_01
      have hc2 : r1.2.2.R.card ≤ r2.2.2.R.card := Finset.card_le_card h2_R
      omega
    have h_f_edge : updateForestSplitCard S u ≤ S₀.G.maxDeg := by
      cases u with
      | delete _ => simp [updateForestSplitCard]
      | insert _ _ _ => simp [updateForestSplitCard]
      | split _ _ _ _ => exact split_forest_edges_le_maxDeg hI hu hD
    have hBV_all : ts.C.BatchIsValid (r1.1 ++ r2.1) := by
      rw [batchIsValid_append]; exact ⟨h1_BV, h1_C ▸ h2_BV⟩
    have hC'_eq : r2.2.1.C = ts.C.applyBatch (r1.1 ++ r2.1) := by
      rw [applyBatch_append, ← h1_C]; exact h2_C
    have hds_all : ∀ op ∈ r1.1 ++ r2.1, isDelOrSplit op := by
      intro op hop
      rcases List.mem_append.mp hop with h | h
      · exact h1_ds op h
      · exact h2_ds op h
    have h_tag : updateSplitTag u ≤ 1 := by cases u <;> simp [updateSplitTag]
    have h1_sc' : batchSplitCount r1.1 ≤ 1 + (r1.2.2.R \ S.R).card + S₀.G.maxDeg := by omega
    have h1_len' : r1.1.length ≤ 1 + (r1.2.2.R \ S.R).card + S₀.G.maxDeg := by omega
    have hsc_all : batchSplitCount (r1.1 ++ r2.1) ≤
        (u :: rest).length * (S₀.G.maxDeg + 1) + (r2.2.2.R \ S.R).card := by
      rw [batchSplitCount_append, List.length_cons, Nat.succ_mul]
      omega
    have hlen_all : (r1.1 ++ r2.1).length ≤
        (u :: rest).length * (S₀.G.maxDeg + 1) + (r2.2.2.R \ S.R).card := by
      rw [List.length_append, List.length_cons, Nat.succ_mul]
      omega
    have hR_step : ((r1.2.2.R \ S.R).card : ℝ) ≤ 56 * (Real.log ((S₀.G₀.n : ℝ) + 2)) ^ 2 := by
      rw [Finset.card_sdiff_of_subset hR_01, Nat.cast_sub (Finset.card_le_card hR_01)]
      have hR_le := hsp.2.2.2.2.2.2.2.2.2.2
      rw [← h1_S] at hR_le
      rw [hD.hG₀_eq] at hR_le
      linarith
    have hlen_real : ((r1.1 ++ r2.1).length : ℝ) ≤
        ((u :: rest).length : ℝ) *
          ((S₀.G.maxDeg : ℝ) + 1 + 56 * (Real.log ((S₀.G₀.n : ℝ) + 2)) ^ 2) := by
      have hl1 : (r1.1.length : ℝ) ≤ 1 + (S₀.G.maxDeg : ℝ) + ((r1.2.2.R \ S.R).card : ℝ) := by
        exact_mod_cast le_trans h1_len' (by omega)
      rw [List.length_append, Nat.cast_add, List.length_cons, Nat.cast_add, Nat.cast_one]
      have hlog_nn : 0 ≤ 56 * (Real.log ((S₀.G₀.n : ℝ) + 2)) ^ 2 := by positivity
      nlinarith
    have hV_card : r2.2.1.C.V.card = ts.C.V.card + batchSplitCount (r1.1 ++ r2.1) := by
      rw [batchSplitCount_append, ← Nat.add_assoc, ← h1_V]
      exact h2_V
    exact ⟨h2_S, h2_I, h2_D, h2_T, hR_02, hBV_all, hC'_eq, hds_all,
      hsc_all, hlen_all, hlen_real, hV_card⟩

end

end MinCostFlow.SparseCore
