module

public import MinCostFlow.Statement.Cited.Graphs
public import MinCostFlow.Spanner.Embedding
public import MinCostFlow.Spanner.Tools
public import MinCostFlow.Spanner.Subgraph
public import MinCostFlow.Spanner.Algorithm
public import MinCostFlow.Spanner.WitnessProps
public import MinCostFlow.Spanner.WitnessBounds
public import MinCostFlow.Spanner.WitnessLift
public import MinCostFlow.Spanner.Task3Base

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Task 3 Analysis Base: Invariant 2 and Claim 8.9 helpers

Defines `Task3RoundEntryInv`, proves `task3Init_entryInv`, `invariant_2` (Invariant 2,
page 44), and the helper bounds leading into Claim 8.9.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open MinCostFlow.Cited

/-! ## Task 3 round-entry invariant and initialization (`task3Init`) -/

/-- Round-entry invariant holding before round 1 (`task3Init`) and at the end of every
`task3Round`. -/
structure Task3RoundEntryInv {DSState : Type} (J : Graph) (wd : WitnessData)
    (s : Task3State DSState) : Prop where
  partial_emb : IsPartialEmbedding J wd.W s.embJW
  j0_and_loops_embedded : ∀ eJ < J.m,
    (wd.jSources.getD eJ JEdgeSource.isLoop = JEdgeSource.isLoop ∨
     ∃ eW, wd.jSources.getD eJ JEdgeSource.isLoop = JEdgeSource.inJ0 eW) →
    (s.embJW eJ).isSome = true
  emb_len : ∀ eJ < J.m, ((partialToWalk s.embJW eJ).edges.length : ℝ) ≤ wd.γ_ExpPath
  econg_half : ∀ eW < wd.W.m,
    econgAt J (fun _ => 1) wd.wW (partialToWalk s.embJW) eW ≤ (s.η₂ + 1 / 2 : ℝ) * wd.τ₂
  j0_econg : ∀ eW < wd.j0Edges.length,
    econgAt J (fun _ => 1) wd.wW (partialToWalk s.embJW) eW ≤ wd.τ₂ / 2
  initCount_eq : s.initCountW = s.η₂ * wd.comps.length
  initEdges_eq : s.initEdgesW = s.η₂ * (wd.comps.map fun c => c.W_sub.m).sum
  middle_eq : s.middleIters2 = s.getPathCountW
  unemb_eq : s.getPathCountW + unembeddedCount2 J s ≤ J.m
  econgUpdates_le : (s.econgUpdates : ℝ) ≤ (s.getPathCountW : ℝ) * wd.γ_ExpPath
  del_eq_inner : s.deleteCountW = s.innerIters2
  inner_le : s.innerIters2 ≤ s.η₂ * wd.W.m
  inner_le_getPath : (s.innerIters2 : ℝ) ≤ (s.getPathCountW : ℝ) * wd.γ_ExpPath

lemma tau2_pos {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH)) :
    0 < (buildWitness tools H' J embJH).τ₂ := by
  let wd := buildWitness tools H' J embJH
  have hφ : 0 < wd.φ_ds := hw.φ_ds_pos
  have hγE : 0 < wd.γ_ExpPath :=
    lt_of_lt_of_le (div_pos one_pos hφ) hw.γ_ExpPath_ge
  have hγd : 0 < wd.γ_del := lt_of_lt_of_le zero_lt_one hw.γ_del_ge
  change 0 < wd.γ_ExpPath * wd.γ_del / wd.φ_ds
  exact div_pos (mul_pos hγE hγd) hφ

lemma one_le_gamma_ExpPath {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH)) :
    (1 : ℝ) ≤ (buildWitness tools H' J embJH).γ_ExpPath := by
  let wd := buildWitness tools H' J embJH
  have hφ_pos : 0 < wd.φ_ds := hw.φ_ds_pos
  have hφ_half : wd.φ_ds ≤ 1 / 2 := hw.φ_ds_half
  have h2 : (2 : ℝ) ≤ 1 / wd.φ_ds := by
    rw [le_div_iff₀ hφ_pos]
    linarith
  linarith [hw.γ_ExpPath_ge]

theorem task3Init_entryInv {DSState : Type} {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH)) :
    let wd := buildWitness tools H' J embJH
    Task3RoundEntryInv (DSState := DSState) J wd (task3Init J wd) := by
  intro wd
  let s₀ : Task3State DSState := task3Init J wd
  have hτ₂_pos : 0 < wd.τ₂ := tau2_pos tools H' J embJH hw
  have hγE_ge1 : 1 ≤ wd.γ_ExpPath := one_le_gamma_ExpPath tools H' J embJH hw
  have hτ₂_half := one_div_phi_dec_le_tau2_half tools H' J embJH hw
  have hpartial : IsPartialEmbedding J wd.W s₀.embJW := by
    refine ⟨le_rfl, fun eJ heJm P hP => ?_⟩
    dsimp only [s₀, task3Init] at hP
    simp only [heJm, ↓reduceIte] at hP
    have he_mem : J.edges[eJ]'heJm ∈ J.edges := List.getElem_mem heJm
    have hvalid := hJ _ he_mem
    have hu_W : (J.edges[eJ]'heJm).1 < wd.W.n := hvalid.1
    have hv_W : (J.edges[eJ]'heJm).2 < wd.W.n := hvalid.2
    have hcase := jSources_cases tools H' J embJH hJ hw heJm
    dsimp only at hcase
    cases hsrc : wd.jSources.getD eJ JEdgeSource.isLoop with
    | isLoop =>
      have hsrc' : (buildWitness tools H' J embJH).jSources.getD eJ JEdgeSource.isLoop =
          JEdgeSource.isLoop := hsrc
      rw [hsrc] at hP
      rw [hsrc'] at hcase
      simp only [Option.some.injEq] at hP
      subst hP
      rw [List.getD_eq_getElem _ _ heJm] at hcase
      exact ⟨hu_W, hv_W, Or.inl ⟨rfl, rfl, hcase⟩⟩
    | inJ0 eW =>
      have hsrc' : (buildWitness tools H' J embJH).jSources.getD eJ JEdgeSource.isLoop =
          JEdgeSource.inJ0 eW := hsrc
      rw [hsrc] at hP
      rw [hsrc'] at hcase
      simp only [Option.some.injEq] at hP
      subst hP
      rcases hcase with ⟨_, _, heWm, hWeq, _⟩
      rw [List.getD_eq_getElem _ _ heJm] at hWeq
      rw [hWeq]
      refine Walk.isWalk_single hu_W hv_W heWm ?_
      rw [hWeq]
      exact Or.inl ⟨rfl, rfl⟩
    | inComp ci jL =>
      rw [hsrc] at hP
      simp at hP
  have hj0_loops : ∀ eJ < J.m,
      (wd.jSources.getD eJ JEdgeSource.isLoop = JEdgeSource.isLoop ∨
       ∃ eW, wd.jSources.getD eJ JEdgeSource.isLoop = JEdgeSource.inJ0 eW) →
      (s₀.embJW eJ).isSome = true := by
    intro eJ heJm hcase
    dsimp only [s₀, task3Init]
    simp only [heJm, ↓reduceIte]
    rcases hcase with h | ⟨eW, h⟩ <;> · rw [h]; simp
  have hemb_len : ∀ eJ < J.m, ((partialToWalk s₀.embJW eJ).edges.length : ℝ) ≤ wd.γ_ExpPath := by
    intro eJ heJm
    dsimp only [s₀, task3Init, partialToWalk]
    simp only [heJm, ↓reduceIte]
    cases hsrc : wd.jSources.getD eJ JEdgeSource.isLoop with
    | isLoop => simp [Walk.empty]; linarith
    | inJ0 _ => simp [Walk.single]; exact hγE_ge1
    | inComp _ _ => simp [Walk.empty]; linarith
  have hecong_card_le : ∀ eW : ℕ,
      ((Finset.range J.m).filter fun eJ => eW ∈ (partialToWalk s₀.embJW eJ).edges).card ≤ 1 ∧
      (∀ eJ ∈ (Finset.range J.m).filter fun eJ => eW ∈ (partialToWalk s₀.embJW eJ).edges,
        wd.jSources.getD eJ JEdgeSource.isLoop = JEdgeSource.inJ0 eW) := by
    intro eW
    have hmem_src : ∀ eJ, eJ ∈ (Finset.range J.m).filter
        (fun eJ => eW ∈ (partialToWalk s₀.embJW eJ).edges) →
        eJ < J.m ∧ wd.jSources.getD eJ JEdgeSource.isLoop = JEdgeSource.inJ0 eW := by
      intro eJ heJ
      rw [Finset.mem_filter, Finset.mem_range] at heJ
      refine ⟨heJ.1, ?_⟩
      have he_in := heJ.2
      dsimp only [partialToWalk, s₀, task3Init] at he_in
      simp only [heJ.1, ↓reduceIte] at he_in
      cases hsrc : wd.jSources.getD eJ JEdgeSource.isLoop with
      | isLoop => rw [hsrc] at he_in; simp [Walk.empty] at he_in
      | inComp ci jL => rw [hsrc] at he_in; simp [Walk.empty] at he_in
      | inJ0 eW' =>
        rw [hsrc] at he_in
        simp [Walk.single] at he_in
        subst he_in
        rfl
    refine ⟨Finset.card_le_one.mpr ?_, fun eJ heJ => (hmem_src eJ heJ).2⟩
    intro a ha b hb
    obtain ⟨ha_m, ha_src⟩ := hmem_src a ha
    obtain ⟨hb_m, hb_src⟩ := hmem_src b hb
    have hca := jSources_cases tools H' J embJH hJ hw ha_m
    have hcb := jSources_cases tools H' J embJH hJ hw hb_m
    dsimp only at hca hcb
    have hsrc_a : (buildWitness tools H' J embJH).jSources.getD a JEdgeSource.isLoop =
        JEdgeSource.inJ0 eW := ha_src
    have hsrc_b : (buildWitness tools H' J embJH).jSources.getD b JEdgeSource.isLoop =
        JEdgeSource.inJ0 eW := hb_src
    rw [hsrc_a] at hca
    rw [hsrc_b] at hcb
    rw [← hca.2.1, hcb.2.1]
  have hj0_ec : ∀ eW < wd.j0Edges.length,
      econgAt J (fun _ => 1) wd.wW (partialToWalk s₀.embJW) eW ≤ wd.τ₂ / 2 := by
    intro eW heW0
    have hwW_eq := (W_edges_getD_j0 tools H' J embJH heW0).2.2.2
    have hcard := (hecong_card_le eW).1
    have heWm := (W_edges_getD_j0 tools H' J embJH heW0).1
    have hw_pos := wW_pos tools H' J embJH hw heWm
    unfold econgAt
    have hnum_le : ∑ _j ∈ (Finset.range J.m).filter
        (fun j => eW ∈ (partialToWalk s₀.embJW j).edges), (1 : ℝ) ≤ 1 := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast hcard
    have hdiv : (∑ _j ∈ (Finset.range J.m).filter
        (fun j => eW ∈ (partialToWalk s₀.embJW j).edges), (1 : ℝ)) / wd.wW eW ≤ 1 / wd.φ_dec := by
      rw [hwW_eq]
      exact div_le_div_of_nonneg_right hnum_le hw.φ_dec_pos.le
    exact le_trans hdiv hτ₂_half
  have hecong_h : ∀ eW < wd.W.m,
      econgAt J (fun _ => 1) wd.wW (partialToWalk s₀.embJW) eW ≤ (s₀.η₂ + 1 / 2 : ℝ) * wd.τ₂ := by
    intro eW heWm
    have hs0_eta : (s₀.η₂ : ℝ) = 0 := Nat.cast_zero
    have hhalf : 2⁻¹ * wd.τ₂ = wd.τ₂ / 2 := by ring
    rw [hs0_eta, zero_add, one_div, hhalf]
    by_cases heW0 : eW < wd.j0Edges.length
    · exact hj0_ec eW heW0
    · have hempty : (Finset.range J.m).filter
          (fun j => eW ∈ (partialToWalk s₀.embJW j).edges) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro j hj_r
        by_contra hmem
        have hj_in : j ∈ (Finset.range J.m).filter
            (fun j => eW ∈ (partialToWalk s₀.embJW j).edges) :=
          Finset.mem_filter.mpr ⟨hj_r, hmem⟩
        have hsrc := (hecong_card_le eW).2 j hj_in
        have hc := jSources_cases tools H' J embJH hJ hw (Finset.mem_range.mp hj_r)
        dsimp only at hc
        have hsrc' : (buildWitness tools H' J embJH).jSources.getD j JEdgeSource.isLoop =
            JEdgeSource.inJ0 eW := hsrc
        rw [hsrc'] at hc
        exact heW0 hc.1
      unfold econgAt
      rw [hempty, Finset.sum_empty, zero_div]
      linarith
  have hunemb : s₀.getPathCountW + unembeddedCount2 J s₀ ≤ J.m := by
    change 0 + (unembeddedSet2 J s₀).card ≤ J.m
    simpa [unembeddedSet2, Finset.card_range] using
      Finset.card_le_card (Finset.filter_subset _ (Finset.range J.m))
  exact
    { partial_emb := hpartial
      j0_and_loops_embedded := hj0_loops
      emb_len := hemb_len
      econg_half := hecong_h
      j0_econg := hj0_ec
      initCount_eq := by simp [task3Init]
      initEdges_eq := by simp [task3Init]
      middle_eq := rfl
      unemb_eq := hunemb
      econgUpdates_le := by
        change ((0 : ℕ) : ℝ) ≤ ((0 : ℕ) : ℝ) * wd.γ_ExpPath
        simp
      del_eq_inner := rfl
      inner_le := by
        change 0 ≤ 0 * wd.W.m
        simp
      inner_le_getPath := by
        change ((0 : ℕ) : ℝ) ≤ ((0 : ℕ) : ℝ) * wd.γ_ExpPath
        simp }

/-! ## Invariant 2 (`task3Round_inv`) -/

/-- **Invariant 2** (`spanner.tex`, page 44):
One round `task3Round` preserves `Task3CoreInv`, establishes `Task3LoopInv` and
`econg(Π_{J → W}) ≤ (η₂ + 1/2) τ₂` with `task3MiddleCond = false`, and maintains `Task3RoundRel`
from the round entry state `s`. -/
theorem invariant_2 {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    {s : Task3State tools.pathDS.State}
    (hentry : Task3RoundEntryInv J (buildWitness tools H' J embJH) s) :
    let wd := buildWitness tools H' J embJH
    let s' := task3Round tools.pathDS J wd s
    Task3LoopInv tools.pathDS J wd s' ∧
    Task3RoundRel tools.pathDS J wd s s' ∧
    task3MiddleCond tools.pathDS J wd s' = false ∧
    s'.η₂ = s.η₂ + 1 ∧
    s'.initCountW = s'.η₂ * wd.comps.length ∧
    s'.initEdgesW = s'.η₂ * (wd.comps.map fun c => c.W_sub.m).sum := by
  intro wd s'
  let dsInit := wd.comps.map fun c => tools.pathDS.init wd.φ_Const wd.M_W c.W_sub
  let initEdges := (wd.comps.map fun c => c.W_sub.m).sum
  let s1 : Task3State tools.pathDS.State :=
    { s with
      η₂ := s.η₂ + 1
      dsW := dsInit
      initCountW := s.initCountW + wd.comps.length
      initEdgesW := s.initEdgesW + initEdges }
  have hs'_eq : s' = whileFuel J.m (task3MiddleCond tools.pathDS J wd)
      (task3MiddleStep tools.pathDS J wd) s1 := rfl
  have hτ₂_nn : 0 ≤ wd.τ₂ := (tau2_pos tools H' J embJH hw).le
  have hds_len : dsInit.length = wd.comps.length := List.length_map _
  have hds_get : ∀ ci (hci : ci < wd.comps.length),
      dsInit[ci]'(by rw [hds_len]; exact hci) =
        tools.pathDS.init wd.φ_Const wd.M_W (wd.comps[ci]'hci).W_sub := by
    intro ci hci
    exact List.getElem_map _
  have hs1_core : Task3CoreInv tools.pathDS J wd s1 :=
    { ds_len := hds_len
      ds_inv := fun ci hci => by
        change tools.pathDS.Inv wd.φ_Const wd.M_W (wd.comps[ci]'hci).W_sub
          (dsInit[ci]'(by rw [hds_len]; exact hci))
        rw [hds_get ci hci]
        rcases hw.comp_props ci hci with
          ⟨_, _, _, _, _, _, _, _, _, _, _,
           hc_Wn, hc_Wvalid, hc_Wm_pos, hc_Wm_le, hc_Wdeg, hc_Wexp, _⟩
        exact tools.pathDS.init_inv wd.φ_Const wd.M_W (wd.comps[ci]'hci).W_sub
          hw.φ_Const_pos hw.φ_Const_le hc_Wvalid hc_Wm_pos hc_Wm_le
          (fun v hv => hc_Wdeg v (by rw [← hc_Wn]; exact hv)) hc_Wexp
      Vhat_sub := fun ci hci => by
        change tools.pathDS.Vhat (dsInit[ci]'(by rw [hds_len]; exact hci)) ⊆ _
        rw [hds_get ci hci]
        rcases hw.comp_props ci hci with
          ⟨_, _, _, _, _, _, _, _, _, _, _,
           hc_Wn, hc_Wvalid, hc_Wm_pos, hc_Wm_le, hc_Wdeg, hc_Wexp, _⟩
        rw [tools.pathDS.init_Vhat wd.φ_Const wd.M_W (wd.comps[ci]'hci).W_sub
          hw.φ_Const_pos hw.φ_Const_le hc_Wvalid hc_Wm_pos hc_Wm_le
          (fun v hv => hc_Wdeg v (by rw [← hc_Wn]; exact hv)) hc_Wexp]
        exact Finset.empty_subset _
      Vhat_vol := fun ci hci => by
        change ((wd.comps[ci]'hci).W_sub.vol (tools.pathDS.Vhat (dsInit[ci]'(by rw [hds_len]; exact hci))) : ℝ) ≤ _
        rw [hds_get ci hci]
        rcases hw.comp_props ci hci with
          ⟨_, _, _, _, _, _, _, _, _, _, _,
           hc_Wn, hc_Wvalid, hc_Wm_pos, hc_Wm_le, hc_Wdeg, hc_Wexp, _⟩
        rw [tools.pathDS.init_Vhat wd.φ_Const wd.M_W (wd.comps[ci]'hci).W_sub
          hw.φ_Const_pos hw.φ_Const_le hc_Wvalid hc_Wm_pos hc_Wm_le
          (fun v hv => hc_Wdeg v (by rw [← hc_Wn]; exact hv)) hc_Wexp]
        have hdel0 : tools.pathDS.deleted (tools.pathDS.init wd.φ_Const wd.M_W (wd.comps[ci]'hci).W_sub) = ∅ :=
          tools.pathDS.init_deleted wd.φ_Const wd.M_W (wd.comps[ci]'hci).W_sub
            hw.φ_Const_pos hw.φ_Const_le hc_Wvalid hc_Wm_pos hc_Wm_le
            (fun v hv => hc_Wdeg v (by rw [← hc_Wn]; exact hv)) hc_Wexp
        have hvol0 : (wd.comps[ci]'hci).W_sub.vol ∅ = 0 := by
          unfold Graph.vol Graph.volIn
          simp
        rw [hvol0, Nat.cast_zero, hdel0, Finset.card_empty, Nat.cast_zero, mul_zero, zero_div]
      partial_emb := hentry.partial_emb
      j0_and_loops_embedded := hentry.j0_and_loops_embedded
      emb_len := hentry.emb_len
      econg_half := fun eW heWm => by
        have hprev := hentry.econg_half eW heWm
        have hinc : (s.η₂ + 1 / 2 : ℝ) * wd.τ₂ ≤ ((s1.η₂ : ℝ) + 1 / 2) * wd.τ₂ := by
          have hs1_eta : (s1.η₂ : ℝ) = (s.η₂ : ℝ) + 1 := by
            change ((s.η₂ + 1 : ℕ) : ℝ) = _
            push_cast; rfl
          rw [hs1_eta]
          nlinarith
        exact le_trans hprev hinc
      j0_econg := hentry.j0_econg
      deleted_spec := fun ci hci b hb => by
        change b ∈ tools.pathDS.deleted (dsInit[ci]'(by rw [hds_len]; exact hci)) at hb
        rw [hds_get ci hci] at hb
        rcases hw.comp_props ci hci with
          ⟨_, _, _, _, _, _, _, _, _, _, _,
           hc_Wn, hc_Wvalid, hc_Wm_pos, hc_Wm_le, hc_Wdeg, hc_Wexp, _⟩
        rw [tools.pathDS.init_deleted wd.φ_Const wd.M_W (wd.comps[ci]'hci).W_sub
          hw.φ_Const_pos hw.φ_Const_le hc_Wvalid hc_Wm_pos hc_Wm_le
          (fun v hv => hc_Wdeg v (by rw [← hc_Wn]; exact hv)) hc_Wexp] at hb
        simp at hb
      initCount_eq := by
        change s.initCountW + wd.comps.length = (s.η₂ + 1) * wd.comps.length
        rw [hentry.initCount_eq, Nat.add_mul, Nat.one_mul]
      initEdges_eq := by
        change s.initEdgesW + initEdges = (s.η₂ + 1) * initEdges
        rw [hentry.initEdges_eq, Nat.add_mul, Nat.one_mul]
      middle_eq := hentry.middle_eq
      unemb_eq := hentry.unemb_eq
      econgUpdates_le := hentry.econgUpdates_le }
  have hs1_active : ∀ ci (hci : ci < wd.comps.length) eL,
      eL < (wd.comps[ci]'hci).W_sub.m →
      eL ∉ tools.pathDS.deleted (s1.dsW[ci]'(by rw [hs1_core.ds_len]; exact hci)) →
      econgAt J (fun _ => 1) wd.wW (partialToWalk s1.embJW) ((wd.comps[ci]'hci).wStart + eL) ≤
        (s1.η₂ : ℝ) * wd.τ₂ := by
    intro ci hci eL heL _
    have heWm := (W_edges_getD_comp tools H' J embJH hci heL).1
    have hprev := hentry.econg_half ((wd.comps[ci]'hci).wStart + eL) heWm
    have hs1_eta : (s1.η₂ : ℝ) = (s.η₂ : ℝ) + 1 := by
      change ((s.η₂ + 1 : ℕ) : ℝ) = _
      push_cast; rfl
    change econgAt J (fun _ => 1) wd.wW (partialToWalk s.embJW) _ ≤ _
    rw [hs1_eta]
    exact le_trans hprev (by nlinarith)
  have hs1_loop : Task3LoopInv tools.pathDS J wd s1 := ⟨hs1_core, hs1_active⟩
  have hrel_init : Task3RoundRel tools.pathDS J wd s s1 :=
    { emb_mono := fun _ _ => Or.inr rfl
      inner_eq := by
        have hzeros : ∑ ci ∈ Finset.range wd.comps.length,
            (tools.pathDS.deleted (dsInit.getD ci (tools.pathDS.init wd.φ_Const wd.M_W ⟨0, []⟩))).card = 0 := by
          refine Finset.sum_eq_zero fun ci hci_r => ?_
          have hci := Finset.mem_range.mp hci_r
          have hci_ds : ci < dsInit.length := by rw [hds_len]; exact hci
          rw [List.getD_eq_getElem _ _ hci_ds, hds_get ci hci]
          rcases hw.comp_props ci hci with
            ⟨_, _, _, _, _, _, _, _, _, _, _,
             hc_Wn, hc_Wvalid, hc_Wm_pos, hc_Wm_le, hc_Wdeg, hc_Wexp, _⟩
          rw [tools.pathDS.init_deleted wd.φ_Const wd.M_W (wd.comps[ci]'hci).W_sub
            hw.φ_Const_pos hw.φ_Const_le hc_Wvalid hc_Wm_pos hc_Wm_le
            (fun v hv => hc_Wdeg v (by rw [← hc_Wn]; exact hv)) hc_Wexp]
          simp
        change s.innerIters2 = s.innerIters2 + _
        rw [hzeros, add_zero]
      del_eq := by
        change s.deleteCountW = s.innerIters2 - s.innerIters2 + s.deleteCountW
        omega
      getPath_eq := rfl }
  have hmid := task3MiddleLoop_spec tools H' J embJH hJ hw hs1_loop hrel_init
  rcases hmid with ⟨hloop', hrel', hdone', heta', hic', hie'⟩
  refine ⟨hloop', hrel', hdone', heta', ?_, ?_⟩
  · have h1 := hs1_core.initCount_eq
    change s'.initCountW = s'.η₂ * wd.comps.length
    have hic_eq : s'.initCountW = s1.initCountW := hic'
    have heta_eq : s'.η₂ = s1.η₂ := heta'
    rw [hic_eq, heta_eq]
    exact h1
  · have h2 := hs1_core.initEdges_eq
    change s'.initEdgesW = s'.η₂ * initEdges
    have hie_eq : s'.initEdgesW = s1.initEdgesW := hie'
    have heta_eq : s'.η₂ = s1.η₂ := heta'
    rw [hie_eq, heta_eq]
    exact h2

/-! ## Claim 8.9 (`claim_8_9`) -/

noncomputable def delWSet (pathDS : PathDSTool) (wd : WitnessData)
    (s' : Task3State pathDS.State) (dsLen : s'.dsW.length = wd.comps.length) (ci : ℕ) :
    Finset ℕ :=
  if h : ci < wd.comps.length then
    (pathDS.deleted (s'.dsW[ci]'(by rw [dsLen]; exact h))).image
      fun eL => (wd.comps[ci]'h).wStart + eL
  else ∅

theorem delWSet_spec {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (_hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    {s' : Task3State tools.pathDS.State}
    (hcore : Task3CoreInv tools.pathDS J (buildWitness tools H' J embJH) s')
    {ci : ℕ} (hci : ci < (buildWitness tools H' J embJH).comps.length) :
    let wd := buildWitness tools H' J embJH
    (delWSet tools.pathDS wd s' hcore.ds_len ci).card =
      (tools.pathDS.deleted (s'.dsW[ci]'(by rw [hcore.ds_len]; exact hci))).card ∧
    (∀ eW ∈ delWSet tools.pathDS wd s' hcore.ds_len ci,
      wd.comps[ci].wStart ≤ eW ∧ eW < wd.comps[ci].wStart + wd.comps[ci].W_sub.m ∧
      eW < wd.W.m ∧ wd.wW eW = wd.φ_dec * (2 ^ wd.comps[ci].level : ℝ) ∧
      ∃ eL ∈ tools.pathDS.deleted (s'.dsW[ci]'(by rw [hcore.ds_len]; exact hci)),
        eW = wd.comps[ci].wStart + eL) := by
  intro wd
  dsimp only [delWSet]
  split_ifs with hbad
  swap
  · exact False.elim (hbad hci)
  have hinj : Set.InjOn (fun eL => (wd.comps[ci]'hci).wStart + eL)
      (tools.pathDS.deleted (s'.dsW[ci]'(by rw [hcore.ds_len]; exact hci))) := by
    intro a _ b _ hab
    exact Nat.add_left_cancel hab
  refine ⟨Finset.card_image_of_injOn hinj, fun eW heW => ?_⟩
  rcases Finset.mem_image.mp heW with ⟨eL, heL, rfl⟩
  have heL_m : eL < (wd.comps[ci]'hci).W_sub.m := (hcore.deleted_spec ci hci eL heL).1
  have hcomp := W_edges_getD_comp tools H' J embJH hci heL_m
  refine ⟨Nat.le_add_right _ _, by omega, hcomp.1, hcomp.2.2.2.2, eL, heL, rfl⟩

lemma claim_8_9_algebra {U E wSum τ₂ γ_E γ_del φ_ds : ℝ}
    (hγE : 0 < γ_E) (hU_le : U ≤ (γ_del / φ_ds) * wSum)
    (hτ : τ₂ = γ_E * γ_del / φ_ds)
    (hW_le : (τ₂ / 2) * wSum ≤ E * γ_E) :
    U ≤ 2 * E := by
  have hγE2_pos : 0 < γ_E / 2 := div_pos hγE two_pos
  have hleft : U * (γ_E / 2) ≤ (τ₂ / 2) * wSum := by
    calc U * (γ_E / 2) ≤ ((γ_del / φ_ds) * wSum) * (γ_E / 2) :=
          mul_le_mul_of_nonneg_right hU_le hγE2_pos.le
      _ = (γ_E * γ_del / φ_ds / 2) * wSum := by ring
      _ = (τ₂ / 2) * wSum := by rw [← hτ]
  have hright : U * (γ_E / 2) ≤ (2 * E) * (γ_E / 2) := by
    calc U * (γ_E / 2) ≤ (τ₂ / 2) * wSum := hleft
      _ ≤ E * γ_E := hW_le
      _ = (2 * E) * (γ_E / 2) := by ring
  exact le_of_mul_le_mul_right hright hγE2_pos

private noncomputable def unembCompJ' {DSState : Type} (J : Graph) (wd : WitnessData)
    (s' : Task3State DSState) (ci : ℕ) : Finset ℕ :=
  letI := Classical.propDecidable
  (Finset.range J.m).filter fun eJ =>
    (s'.embJW eJ).isNone = true ∧
      ∃ jLocal, wd.jSources.getD eJ JEdgeSource.isLoop = JEdgeSource.inComp ci jLocal

theorem unembeddedSet2_le_sum_comp {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    {s' : Task3State tools.pathDS.State}
    (hcore : Task3CoreInv tools.pathDS J (buildWitness tools H' J embJH) s')
    (hmid : task3MiddleCond tools.pathDS J (buildWitness tools H' J embJH) s' = false) :
    let wd := buildWitness tools H' J embJH
    (unembeddedCount2 J s' : ℝ) ≤
      (wd.γ_del / wd.φ_ds) *
        (∑ ci ∈ Finset.range wd.comps.length,
          ((tools.pathDS.deleted (s'.dsW.getD ci (tools.pathDS.init wd.φ_Const wd.M_W ⟨0, []⟩))).card : ℝ) *
            (wd.φ_dec * (2 ^ (wd.comps.getD ci defaultCompInfo).level : ℝ))) := by
  intro wd
  let dsDef := tools.pathDS.init wd.φ_Const wd.M_W ⟨0, []⟩
  unfold task3MiddleCond at hmid
  rw [Bool.eq_false_iff, ne_eq, Option.isSome_iff_exists] at hmid
  have hfind_none : findReadyJEdge tools.pathDS J wd s' = none := by
    cases hf : findReadyJEdge tools.pathDS J wd s' with
    | none => rfl
    | some p => exact False.elim (hmid ⟨p, hf⟩)
  have htouch : ∀ eJ (heJm : eJ < J.m), s'.embJW eJ = none →
      ∃ (ci jLocal : ℕ) (hci : ci < wd.comps.length),
        wd.jSources.getD eJ JEdgeSource.isLoop = JEdgeSource.inComp ci jLocal ∧
        jLocal < (wd.comps[ci]'hci).J_sub.m ∧
        (wd.comps[ci]'hci).jSubOrigEdges.getD jLocal 0 = eJ ∧
        (((wd.comps[ci]'hci).J_sub.edges.getD jLocal (0, 0)).1 ∈
            tools.pathDS.Vhat (s'.dsW[ci]'(by rw [hcore.ds_len]; exact hci)) ∨
         ((wd.comps[ci]'hci).J_sub.edges.getD jLocal (0, 0)).2 ∈
            tools.pathDS.Vhat (s'.dsW[ci]'(by rw [hcore.ds_len]; exact hci))) := by
    intro eJ heJm hnone
    have hcase := jSources_cases tools H' J embJH hJ hw heJm
    cases hsrc : wd.jSources.getD eJ JEdgeSource.isLoop with
    | isLoop =>
      have hbad := hcore.j0_and_loops_embedded eJ heJm (Or.inl hsrc)
      rw [hnone] at hbad; simp at hbad
    | inJ0 eW =>
      have hbad := hcore.j0_and_loops_embedded eJ heJm (Or.inr ⟨eW, hsrc⟩)
      rw [hnone] at hbad; simp at hbad
    | inComp ci jLocal =>
      dsimp only at hcase
      have hsrc' : (buildWitness tools H' J embJH).jSources.getD eJ JEdgeSource.isLoop =
          JEdgeSource.inComp ci jLocal := hsrc
      rw [hsrc'] at hcase
      rcases hcase with ⟨hci, hj, horig, hjLm, _⟩
      have hci_ds : ci < s'.dsW.length := by rw [hcore.ds_len]; exact hci
      have hnot : ¬ (((wd.comps[ci]'hci).J_sub.edges.getD jLocal (0, 0)).1 ∉
            tools.pathDS.Vhat (s'.dsW[ci]'hci_ds) ∧
          ((wd.comps[ci]'hci).J_sub.edges.getD jLocal (0, 0)).2 ∉
            tools.pathDS.Vhat (s'.dsW[ci]'hci_ds)) := by
        intro hboth
        unfold findReadyJEdge at hfind_none
        dsimp only at hfind_none
        rw [List.head?_eq_none_iff] at hfind_none
        have hmem : (eJ, ci, jLocal) ∈ ([] : List (ℕ × ℕ × ℕ)) := by
          rw [← hfind_none, List.mem_filterMap]
          refine ⟨eJ, List.mem_range.mpr heJm, ?_⟩
          simp only [Option.isNone_iff_eq_none.mpr hnone, ↓reduceIte, hsrc]
          have hci' : ci < wd.comps.length := hci
          rw [List.getD_eq_getElem _ _ hci', List.getD_eq_getElem _ _ hci_ds]
          simp only [hboth.1, hboth.2, not_false_eq_true, and_self, ↓reduceIte]
        simp at hmem
      rw [← not_or] at hnot
      have hV : ((wd.comps[ci]'hci).J_sub.edges.getD jLocal (0, 0)).1 ∈
            tools.pathDS.Vhat (s'.dsW[ci]'hci_ds) ∨
          ((wd.comps[ci]'hci).J_sub.edges.getD jLocal (0, 0)).2 ∈
            tools.pathDS.Vhat (s'.dsW[ci]'hci_ds) := by
        by_contra hneg
        exact hnot hneg
      have horig' : (wd.comps[ci]'hci).jSubOrigEdges.getD jLocal 0 = eJ := by
        rw [List.getD_eq_getElem _ _ hj]
        exact horig
      exact ⟨ci, jLocal, hci, rfl, hjLm, horig', hV⟩
  have hcomp_disj : Set.PairwiseDisjoint (Finset.range wd.comps.length : Set ℕ)
      (unembCompJ' J wd s') := by
    intro ci₁ _ ci₂ _ hne S hS₁ hS₂ eJ heJ
    have he1 := hS₁ heJ
    have he2 := hS₂ heJ
    simp only [unembCompJ', Finset.mem_filter, Finset.mem_range] at he1 he2
    rcases he1.2.2 with ⟨jL₁, hsrc₁⟩
    rcases he2.2.2 with ⟨jL₂, hsrc₂⟩
    rw [hsrc₁] at hsrc₂
    injection hsrc₂ with hci_eq
    exact (hne hci_eq).elim
  have hunemb_sub : unembeddedSet2 J s' ⊆
      (Finset.range wd.comps.length).biUnion (unembCompJ' J wd s') := by
    intro eJ heJ
    simp only [unembeddedSet2, Finset.mem_filter, Finset.mem_range,
      Option.isNone_iff_eq_none] at heJ
    obtain ⟨ci, jLocal, hci, hsrc, _, _, _⟩ := htouch eJ heJ.1 heJ.2
    refine Finset.mem_biUnion.mpr ⟨ci, Finset.mem_range.mpr hci, ?_⟩
    simp only [unembCompJ', Finset.mem_filter, Finset.mem_range,
      Option.isNone_iff_eq_none]
    exact ⟨heJ.1, heJ.2, jLocal, hsrc⟩
  have hcard_le : unembeddedCount2 J s' ≤
      ∑ ci ∈ Finset.range wd.comps.length, (unembCompJ' J wd s' ci).card := by
    unfold unembeddedCount2
    calc (unembeddedSet2 J s').card
        ≤ ((Finset.range wd.comps.length).biUnion (unembCompJ' J wd s')).card :=
            Finset.card_le_card hunemb_sub
      _ = ∑ ci ∈ Finset.range wd.comps.length, (unembCompJ' J wd s' ci).card :=
            Finset.card_biUnion hcomp_disj
  have hper_comp : ∀ ci ∈ Finset.range wd.comps.length,
      ((unembCompJ' J wd s' ci).card : ℝ) ≤
        (wd.γ_del / wd.φ_ds) *
          (((tools.pathDS.deleted (s'.dsW.getD ci dsDef)).card : ℝ) *
            (wd.φ_dec * (2 ^ (wd.comps.getD ci defaultCompInfo).level : ℝ))) := by
    intro ci hci_r
    have hci := Finset.mem_range.mp hci_r
    set c := wd.comps[ci]'hci
    have hci_ds : ci < s'.dsW.length := by rw [hcore.ds_len]; exact hci
    set ds := s'.dsW[ci]'hci_ds
    let Vhat := tools.pathDS.Vhat ds
    let localSet : Finset ℕ := (Finset.range c.J_sub.m).filter fun jL =>
      let eLoc := c.J_sub.edges.getD jL (0, 0)
      (s'.embJW (c.jSubOrigEdges.getD jL 0)).isNone = true ∧
        (eLoc.1 ∈ Vhat ∨ eLoc.2 ∈ Vhat)
    have hsurj : unembCompJ' J wd s' ci ⊆
        localSet.image (fun jL => c.jSubOrigEdges.getD jL 0) := by
      intro eJ heJ
      simp only [unembCompJ', Finset.mem_filter, Finset.mem_range,
        Option.isNone_iff_eq_none] at heJ
      obtain ⟨ci', jL', hci', hsrc', hjLm', horig', hV'⟩ := htouch eJ heJ.1 heJ.2.1
      rcases heJ.2.2 with ⟨jL₀, hsrc₀⟩
      rw [hsrc₀] at hsrc'
      injection hsrc' with hci_eq hjl_eq
      subst hci_eq hjl_eq
      refine Finset.mem_image.mpr ⟨jL₀, ?_, horig'⟩
      simp only [localSet, Finset.mem_filter, Finset.mem_range,
        Option.isNone_iff_eq_none]
      refine ⟨hjLm', ?_, hV'⟩
      rw [horig']
      exact heJ.2.1
    rcases hw.comp_props ci hci with
      ⟨_, _, _, _, _, hc_Jn, hc_Jvalid, _, _, _, _,
       hc_Wn, _, _, _, _, _, hc_deg_rel, _, _, _, _, _, _⟩
    have htouch_card : localSet.card ≤ c.J_sub.vol Vhat := by
      refine card_edges_touching_le_vol c.J_sub Vhat localSet hc_Jvalid
        (Finset.filter_subset _ _) fun jL hjL => ?_
      simp only [localSet, Finset.mem_filter] at hjL
      exact hjL.2.2
    have hcomp_card : (unembCompJ' J wd s' ci).card ≤ c.J_sub.vol Vhat :=
      le_trans (Finset.card_le_card hsurj) (le_trans Finset.card_image_le htouch_card)
    have hVhat_W : Vhat ⊆ c.W_sub.verts := hcore.Vhat_sub ci hci
    have hvol_deg : (c.J_sub.vol Vhat : ℝ) ≤
        (wd.φ_dec * (2 ^ c.level : ℝ)) * (c.W_sub.vol Vhat : ℝ) := by
      unfold Graph.vol Graph.volIn
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk => ?_
      have hk_Wn : k < c.W_sub.n := Finset.mem_range.mp (hVhat_W hk)
      have hk_X : k < c.X.card := by rw [← hc_Wn]; exact hk_Wn
      have hle_k := (hc_deg_rel k hk_X).1
      have hpow_pos : (0 : ℝ) < wd.φ_dec * (2 ^ c.level : ℝ) :=
        mul_pos hw.φ_dec_pos (by positivity)
      exact (div_le_iff₀' hpow_pos).mp hle_k
    have hvol_del : (c.W_sub.vol Vhat : ℝ) ≤
        wd.γ_del * ((tools.pathDS.deleted ds).card : ℝ) / wd.φ_ds :=
      hcore.Vhat_vol ci hci
    have hφ_pow_nn : (0 : ℝ) ≤ wd.φ_dec * (2 ^ c.level : ℝ) := by
      exact mul_nonneg hw.φ_dec_pos.le (by positivity)
    have hget_c : wd.comps.getD ci defaultCompInfo = c := List.getD_eq_getElem _ _ hci
    have hget_ds : s'.dsW.getD ci dsDef = ds := List.getD_eq_getElem _ _ hci_ds
    rw [hget_c, hget_ds]
    calc ((unembCompJ' J wd s' ci).card : ℝ)
        ≤ (c.J_sub.vol Vhat : ℝ) := by exact_mod_cast hcomp_card
      _ ≤ (wd.φ_dec * (2 ^ c.level : ℝ)) * (c.W_sub.vol Vhat : ℝ) := hvol_deg
      _ ≤ (wd.φ_dec * (2 ^ c.level : ℝ)) *
            (wd.γ_del * ((tools.pathDS.deleted ds).card : ℝ) / wd.φ_ds) :=
          mul_le_mul_of_nonneg_left hvol_del hφ_pow_nn
      _ = (wd.γ_del / wd.φ_ds) *
            (((tools.pathDS.deleted ds).card : ℝ) * (wd.φ_dec * (2 ^ c.level : ℝ))) := by ring
  calc (unembeddedCount2 J s' : ℝ)
      ≤ ∑ ci ∈ Finset.range wd.comps.length, ((unembCompJ' J wd s' ci).card : ℝ) := by
          exact_mod_cast hcard_le
    _ ≤ ∑ ci ∈ Finset.range wd.comps.length,
          (wd.γ_del / wd.φ_ds) *
            (((tools.pathDS.deleted (s'.dsW.getD ci dsDef)).card : ℝ) *
              (wd.φ_dec * (2 ^ (wd.comps.getD ci defaultCompInfo).level : ℝ))) :=
          Finset.sum_le_sum hper_comp
    _ = (wd.γ_del / wd.φ_ds) *
          (∑ ci ∈ Finset.range wd.comps.length,
            ((tools.pathDS.deleted (s'.dsW.getD ci dsDef)).card : ℝ) *
              (wd.φ_dec * (2 ^ (wd.comps.getD ci defaultCompInfo).level : ℝ))) :=
          (Finset.mul_sum _ _ _).symm


end MinCostFlow.Spanner
