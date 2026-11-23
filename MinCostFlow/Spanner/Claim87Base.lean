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
public import MinCostFlow.Spanner.Analysis1

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Helper bounds for Claim 8.7

Proves the per-round partition, deleted-edge cardinality, remaining-volume, and algebraic
lemmas used in the proof of Claim 8.7 (`spanner.tex`, pages 43–44).
-/

@[expose] public section

namespace MinCostFlow.Spanner

open MinCostFlow.Cited

/-! ## Helper bounds for Claim 8.7 -/

/-- Set of `W`-edges newly embedded during a single Task 2 round `s → s'`. -/
def newlyEmbeddedSet1 {DSState : Type} (wd : WitnessData) (s s' : Task2State DSState) :
    Finset ℕ :=
  (Finset.range wd.W.m).filter fun eW => (s.embWJ eW).isNone && (s'.embWJ eW).isSome

theorem mem_newlyEmbeddedSet1 {DSState : Type} (wd : WitnessData)
    (s s' : Task2State DSState) {eW : ℕ} :
    eW ∈ newlyEmbeddedSet1 wd s s' ↔
      eW < wd.W.m ∧ s.embWJ eW = none ∧ (s'.embWJ eW).isSome = true := by
  simp [newlyEmbeddedSet1, Option.isNone_iff_eq_none]

theorem unembeddedSet1_partition {DSState : Type} (wd : WitnessData)
    (s s' : Task2State DSState)
    (hmono : ∀ eW < wd.W.m, s.embWJ eW = none ∨ s'.embWJ eW = s.embWJ eW) :
    unembeddedSet1 wd s' ⊆ unembeddedSet1 wd s ∧
    Disjoint (unembeddedSet1 wd s') (newlyEmbeddedSet1 wd s s') ∧
    unembeddedSet1 wd s = unembeddedSet1 wd s' ∪ newlyEmbeddedSet1 wd s s' ∧
    volWRem wd s = volWRem wd s' + ∑ eW ∈ newlyEmbeddedSet1 wd s s', wd.wW eW ∧
    (newlyEmbeddedSet1 wd s s').card = unembeddedCount1 wd s - unembeddedCount1 wd s' := by
  have hsub : unembeddedSet1 wd s' ⊆ unembeddedSet1 wd s := by
    intro eW heW
    simp only [unembeddedSet1, Finset.mem_filter, Finset.mem_range,
      Option.isNone_iff_eq_none] at heW ⊢
    refine ⟨heW.1, ?_⟩
    rcases hmono eW heW.1 with h0 | h01
    · exact h0
    · rw [← h01, heW.2]
  have hdisj : Disjoint (unembeddedSet1 wd s') (newlyEmbeddedSet1 wd s s') := by
    rw [Finset.disjoint_left]
    intro eW h1 h2
    simp only [unembeddedSet1, Finset.mem_filter, Option.isNone_iff_eq_none] at h1
    rw [mem_newlyEmbeddedSet1] at h2
    rw [h1.2] at h2
    simp at h2
  have hunion : unembeddedSet1 wd s = unembeddedSet1 wd s' ∪ newlyEmbeddedSet1 wd s s' := by
    ext eW
    simp only [Finset.mem_union, unembeddedSet1, Finset.mem_filter, Finset.mem_range,
      newlyEmbeddedSet1, Bool.and_eq_true, Option.isNone_iff_eq_none]
    constructor
    · rintro ⟨hm, hnone⟩
      by_cases h' : s'.embWJ eW = none
      · exact Or.inl ⟨hm, h'⟩
      · exact Or.inr ⟨hm, hnone, Option.isSome_iff_ne_none.mpr h'⟩
    · rintro (⟨hm, hnone'⟩ | ⟨hm, hnone, _⟩)
      · have hmem : eW ∈ unembeddedSet1 wd s' :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hm, Option.isNone_iff_eq_none.mpr hnone'⟩
        have hmem0 := Finset.mem_filter.mp (hsub hmem)
        exact ⟨hm, Option.isNone_iff_eq_none.mp hmem0.2⟩
      · exact ⟨hm, hnone⟩
  have hsum : volWRem wd s = volWRem wd s' + ∑ eW ∈ newlyEmbeddedSet1 wd s s', wd.wW eW := by
    unfold volWRem
    rw [hunion, Finset.sum_union hdisj]
  have hcard : (newlyEmbeddedSet1 wd s s').card = unembeddedCount1 wd s - unembeddedCount1 wd s' := by
    unfold unembeddedCount1
    have hcard_u := Finset.card_union_of_disjoint hdisj
    rw [← hunion] at hcard_u
    omega
  exact ⟨hsub, hdisj, hunion, hsum, hcard⟩

theorem verts_toFinset_compose_card_le {H' J : Graph} {embJH : ℕ → Walk}
    (hembJH : IsEmbedding J H' embJH) {P_J : Walk}
    (hPedges : ∀ j ∈ P_J.edges, j < J.m) :
    ((composeAux J embJH P_J.verts P_J.edges).verts.toFinset.card : ℝ) ≤
      (P_J.edges.length : ℝ) * ((length J embJH : ℝ) + 1) := by
  have hsub : (composeAux J embJH P_J.verts P_J.edges).verts.toFinset ⊆
      P_J.edges.toFinset.biUnion fun j => (embJH j).verts.toFinset := by
    intro x hx
    rw [List.mem_toFinset] at hx
    obtain ⟨j, hj, hx_j⟩ := mem_verts_composeAux P_J.verts P_J.edges hx
    exact Finset.mem_biUnion.mpr ⟨j, List.mem_toFinset.mpr hj, List.mem_toFinset.mpr hx_j⟩
  have hcard_nat : (composeAux J embJH P_J.verts P_J.edges).verts.toFinset.card ≤
      P_J.edges.length * (length J embJH + 1) := by
    calc (composeAux J embJH P_J.verts P_J.edges).verts.toFinset.card
        ≤ (P_J.edges.toFinset.biUnion fun j => (embJH j).verts.toFinset).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ j ∈ P_J.edges.toFinset, (embJH j).verts.toFinset.card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ P_J.edges.toFinset, (length J embJH + 1) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj_m := hPedges j (List.mem_toFinset.mp hj)
          have hw := hembJH.2 j hj_m
          exact le_trans (Walk.verts_toFinset_card_le hw)
            (Nat.add_le_add_right (edges_length_le_length embJH hj_m) 1)
      _ = P_J.edges.toFinset.card * (length J embJH + 1) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ P_J.edges.length * (length J embJH + 1) :=
          Nat.mul_le_mul_right _ (List.toFinset_card_le _)
  exact_mod_cast hcard_nat

private noncomputable def delOrigSet (pathDS : PathDSTool) (wd : WitnessData)
    (s' : Task2State pathDS.State) (dsLen : s'.dsJ.length = wd.comps.length) (ci : ℕ) :
    Finset ℕ :=
  if h : ci < wd.comps.length then
    (pathDS.deleted (s'.dsJ[ci]'(by rw [dsLen]; exact h))).image
      fun b => (wd.comps[ci]'h).jSubOrigEdges.getD b 0
  else ∅

private theorem delOrigSet_card {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    {s' : Task2State tools.pathDS.State}
    (hcore : Task2CoreInv tools.pathDS H' J embJH (buildWitness tools H' J embJH) s')
    {ci : ℕ} (hci : ci < (buildWitness tools H' J embJH).comps.length) :
    let wd := buildWitness tools H' J embJH
    (delOrigSet tools.pathDS wd s' hcore.ds_len ci).card =
      (tools.pathDS.deleted (s'.dsJ[ci]'(by rw [hcore.ds_len]; exact hci))).card ∧
    delOrigSet tools.pathDS wd s' hcore.ds_len ci ⊆ (wd.comps[ci]'hci).jSubOrigEdges.toFinset ∧
    delOrigSet tools.pathDS wd s' hcore.ds_len ci ⊆ Finset.range J.m := by
  intro wd
  rcases hw.comp_props ci hci with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hjLen, hjNodup, hjLt, _, _⟩
  dsimp only [delOrigSet]
  split_ifs with hbad
  swap
  · exact False.elim (hbad hci)
  have hinj : Set.InjOn (fun b => (wd.comps[ci]'hci).jSubOrigEdges.getD b 0)
      (tools.pathDS.deleted (s'.dsJ[ci]'(by rw [hcore.ds_len]; exact hci))) := by
    intro a ha b hb hab
    have ha_m : a < (wd.comps[ci]'hci).jSubOrigEdges.length := by
      rw [hjLen]; exact (hcore.deleted_sub_processed ci hci a ha).1
    have hb_m : b < (wd.comps[ci]'hci).jSubOrigEdges.length := by
      rw [hjLen]; exact (hcore.deleted_sub_processed ci hci b hb).1
    change (wd.comps[ci]'hci).jSubOrigEdges.getD a 0 =
      (wd.comps[ci]'hci).jSubOrigEdges.getD b 0 at hab
    rw [List.getD_eq_getElem _ _ ha_m, List.getD_eq_getElem _ _ hb_m] at hab
    exact (List.Nodup.getElem_inj_iff hjNodup).mp hab
  have hsub1 : ((tools.pathDS.deleted (s'.dsJ[ci]'(by rw [hcore.ds_len]; exact hci))).image
      fun b => (wd.comps[ci]'hci).jSubOrigEdges.getD b 0) ⊆
      (wd.comps[ci]'hci).jSubOrigEdges.toFinset := by
    intro jOrig hjOrig
    rcases Finset.mem_image.mp hjOrig with ⟨b, hb, rfl⟩
    have hb_m : b < (wd.comps[ci]'hci).jSubOrigEdges.length := by
      rw [hjLen]; exact (hcore.deleted_sub_processed ci hci b hb).1
    rw [List.getD_eq_getElem _ _ hb_m, List.mem_toFinset]
    exact List.getElem_mem hb_m
  have hsub2 : ((tools.pathDS.deleted (s'.dsJ[ci]'(by rw [hcore.ds_len]; exact hci))).image
      fun b => (wd.comps[ci]'hci).jSubOrigEdges.getD b 0) ⊆ Finset.range J.m := by
    intro jOrig hjOrig
    exact Finset.mem_range.mpr (hjLt jOrig (List.mem_toFinset.mp (hsub1 hjOrig)))
  exact ⟨Finset.card_image_of_injOn hinj, hsub1, hsub2⟩

theorem sum_deleted_bounds {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    {s' : Task2State tools.pathDS.State}
    (hcore : Task2CoreInv tools.pathDS H' J embJH (buildWitness tools H' J embJH) s') :
    let wd := buildWitness tools H' J embJH
    let dsDef := tools.pathDS.init wd.φ_dec wd.J0_strip.m ⟨0, []⟩
    let delSum := ∑ ci ∈ Finset.range wd.comps.length, (tools.pathDS.deleted (s'.dsJ.getD ci dsDef)).card
    delSum ≤ J.m ∧
    (delSum : ℝ) ≤ (s'.processedVerts.card : ℝ) * vcong J H' (fun _ => 1) embJH := by
  intro wd dsDef delSum
  let U := (Finset.range wd.comps.length).biUnion (delOrigSet tools.pathDS wd s' hcore.ds_len)
  have hdisj : Set.PairwiseDisjoint (Finset.range wd.comps.length : Set ℕ)
      (delOrigSet tools.pathDS wd s' hcore.ds_len) := by
    intro ci₁ h1 ci₂ h2 hne
    have hci₁ := Finset.mem_range.mp h1
    have hci₂ := Finset.mem_range.mp h2
    have hsub1 := (delOrigSet_card tools H' J embJH hw hcore hci₁).2.1
    have hsub2 := (delOrigSet_card tools H' J embJH hw hcore hci₂).2.1
    exact (hw.comp_disjoint ci₁ ci₂ hci₁ hci₂ hne).mono hsub1 hsub2
  have hU_eq : U.card = delSum := by
    dsimp only [U, delSum]
    rw [Finset.card_biUnion hdisj]
    refine Finset.sum_congr rfl fun ci hci_r => ?_
    have hci := Finset.mem_range.mp hci_r
    have hci_ds : ci < s'.dsJ.length := by rw [hcore.ds_len]; exact hci
    rw [List.getD_eq_getElem _ _ hci_ds]
    exact (delOrigSet_card tools H' J embJH hw hcore hci).1
  have hU_sub : U ⊆ Finset.range J.m := by
    intro jOrig hj
    rcases Finset.mem_biUnion.mp hj with ⟨ci, hci_r, hmem⟩
    exact (delOrigSet_card tools H' J embJH hw hcore (Finset.mem_range.mp hci_r)).2.2 hmem
  have hle_m : delSum ≤ J.m := by
    rw [← hU_eq]
    calc U.card ≤ (Finset.range J.m).card := Finset.card_le_card hU_sub
      _ = J.m := Finset.card_range J.m
  have hU_proc : U ⊆ s'.processedVerts.biUnion fun x =>
      (Finset.range J.m).filter fun jOrig => x ∈ (embJH jOrig).verts := by
    intro jOrig hj
    have hj_m : jOrig < J.m := Finset.mem_range.mp (hU_sub hj)
    rcases Finset.mem_biUnion.mp hj with ⟨ci, hci_r, hmem⟩
    have hci := Finset.mem_range.mp hci_r
    simp only [delOrigSet, hci, ↓reduceDIte, Finset.mem_image] at hmem
    rcases hmem with ⟨b, hb, rfl⟩
    obtain ⟨_, x, hx, hxb⟩ := hcore.deleted_sub_processed ci hci b hb
    exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj_m, hxb⟩⟩
  have hproc_nat : delSum ≤ ∑ x ∈ s'.processedVerts,
      ((Finset.range J.m).filter fun jOrig => x ∈ (embJH jOrig).verts).card := by
    rw [← hU_eq]
    exact le_trans (Finset.card_le_card hU_proc) Finset.card_biUnion_le
  have hproc_r : (delSum : ℝ) ≤ (s'.processedVerts.card : ℝ) * vcong J H' (fun _ => 1) embJH := by
    have hsum_r : (delSum : ℝ) ≤ ∑ x ∈ s'.processedVerts,
        (((Finset.range J.m).filter fun jOrig => x ∈ (embJH jOrig).verts).card : ℝ) := by
      rw [← Nat.cast_sum]
      exact_mod_cast hproc_nat
    refine le_trans hsum_r ?_
    calc ∑ x ∈ s'.processedVerts,
          (((Finset.range J.m).filter fun jOrig => x ∈ (embJH jOrig).verts).card : ℝ)
        ≤ ∑ _x ∈ s'.processedVerts, vcong J H' (fun _ => 1) embJH := by
          refine Finset.sum_le_sum fun x hx => ?_
          have hx_n := (hcore.processed_sub x hx).1
          have hcard_eq : (((Finset.range J.m).filter fun jOrig => x ∈ (embJH jOrig).verts).card : ℝ) =
              vcongAt J (fun _ => 1) embJH x := by
            unfold vcongAt
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          rw [hcard_eq]
          exact vcongAt_le_vcong (fun _ => 1) embJH hx_n
      _ = (s'.processedVerts.card : ℝ) * vcong J H' (fun _ => 1) embJH := by
          rw [Finset.sum_const, nsmul_eq_mul]
  exact ⟨hle_m, hproc_r⟩

theorem volWRem_le_of_mid_done {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    {s' : Task2State tools.pathDS.State}
    (hcore : Task2CoreInv tools.pathDS H' J embJH (buildWitness tools H' J embJH) s')
    (hmid : task2MiddleCond tools.pathDS (buildWitness tools H' J embJH) s' = false) :
    let wd := buildWitness tools H' J embJH
    let dsDef := tools.pathDS.init wd.φ_dec wd.J0_strip.m ⟨0, []⟩
    volWRem wd s' ≤ (wd.c_deg * wd.γ_del / wd.φ_ds) *
      ((∑ ci ∈ Finset.range wd.comps.length, (tools.pathDS.deleted (s'.dsJ.getD ci dsDef)).card : ℕ) : ℝ) := by
  intro wd dsDef
  unfold task2MiddleCond at hmid
  rw [Bool.eq_false_iff, ne_eq, Option.isSome_iff_exists] at hmid
  have hfind_none : findReadyWEdge tools.pathDS wd s' = none := by
    cases hf : findReadyWEdge tools.pathDS wd s' with
    | none => rfl
    | some p => exact False.elim (hmid ⟨p, hf⟩)
  have htouch : ∀ ci (hci : ci < wd.comps.length) eL,
      eL < (wd.comps[ci]'hci).W_sub.m →
      s'.embWJ ((wd.comps[ci]'hci).wStart + eL) = none →
      ((wd.comps[ci]'hci).W_sub.edges.getD eL (0, 0)).1 ∈
          tools.pathDS.Vhat (s'.dsJ[ci]'(by rw [hcore.ds_len]; exact hci)) ∨
      ((wd.comps[ci]'hci).W_sub.edges.getD eL (0, 0)).2 ∈
          tools.pathDS.Vhat (s'.dsJ[ci]'(by rw [hcore.ds_len]; exact hci)) := by
    intro ci hci eL heL hnone
    set eW := (wd.comps[ci]'hci).wStart + eL
    have hcomp := W_edges_getD_comp tools H' J embJH hci heL
    have heWm : eW < wd.W.m := hcomp.1
    have hsrc : wd.wSources.getD eW (WEdgeSource.fromJ0 0) = WEdgeSource.fromComp ci eL :=
      hcomp.2.2.2.1
    have hnot : ¬ (((wd.comps[ci]'hci).W_sub.edges.getD eL (0, 0)).1 ∉
          tools.pathDS.Vhat (s'.dsJ[ci]'(by rw [hcore.ds_len]; exact hci)) ∧
        ((wd.comps[ci]'hci).W_sub.edges.getD eL (0, 0)).2 ∉
          tools.pathDS.Vhat (s'.dsJ[ci]'(by rw [hcore.ds_len]; exact hci))) := by
      intro hboth
      unfold findReadyWEdge at hfind_none
      dsimp only at hfind_none
      rw [List.head?_eq_none_iff] at hfind_none
      have hmem : (eW, ci, eL) ∈ ([] : List (ℕ × ℕ × ℕ)) := by
        rw [← hfind_none, List.mem_filterMap]
        refine ⟨eW, List.mem_range.mpr heWm, ?_⟩
        have hci_ds : ci < s'.dsJ.length := by rw [hcore.ds_len]; exact hci
        simp only [Option.isNone_iff_eq_none.mpr hnone, ↓reduceIte, hsrc,
          List.getD_eq_getElem _ _ hci,
          List.getD_eq_getElem _ _ hci_ds]
        simp only [hboth.1, hboth.2, not_false_eq_true, and_self, ↓reduceIte]
      simp at hmem
    by_contra hneither
    rw [not_or] at hneither
    exact hnot hneither
  let compUnemb (ci : ℕ) : Finset ℕ :=
    if h : ci < wd.comps.length then
      ((Finset.range (wd.comps[ci]'h).W_sub.m).filter fun eL =>
        (s'.embWJ ((wd.comps[ci]'h).wStart + eL)).isNone).image
        fun eL => (wd.comps[ci]'h).wStart + eL
    else ∅
  have hcomp_disj : Set.PairwiseDisjoint (Finset.range wd.comps.length : Set ℕ) compUnemb := by
    intro ci₁ h1 ci₂ h2 hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro eW he1 he2
    have hci₁ := Finset.mem_range.mp h1
    have hci₂ := Finset.mem_range.mp h2
    simp only [compUnemb, hci₁, hci₂, ↓reduceDIte, Finset.mem_image, Finset.mem_filter,
      Finset.mem_range] at he1 he2
    rcases he1 with ⟨eL₁, ⟨heL₁, _⟩, rfl⟩
    rcases he2 with ⟨eL₂, ⟨heL₂, _⟩, heq⟩
    have hs1 := (W_edges_getD_comp tools H' J embJH hci₁ heL₁).2.2.2.1
    have hs2 := (W_edges_getD_comp tools H' J embJH hci₂ heL₂).2.2.2.1
    dsimp only [wd] at heq
    rw [heq, hs1] at hs2
    injection hs2 with hci_eq
    exact hne hci_eq
  have hunemb_sub : unembeddedSet1 wd s' ⊆ (Finset.range wd.comps.length).biUnion compUnemb := by
    intro eW heW
    simp only [unembeddedSet1, Finset.mem_filter, Finset.mem_range,
      Option.isNone_iff_eq_none] at heW
    have hj0_ge : wd.j0Edges.length ≤ eW := by
      by_contra hlt
      have hs := hcore.j0_embedded eW (Nat.lt_of_not_ge hlt)
      rw [heW.2] at hs
      simp at hs
    rcases W_edge_cases tools H' J embJH heW.1 with hlt0 | ⟨ci, hci, eL, heL, rfl⟩
    · exact absurd hlt0 (Nat.not_lt_of_ge hj0_ge)
    · refine Finset.mem_biUnion.mpr ⟨ci, Finset.mem_range.mpr hci, ?_⟩
      change (wd.comps[ci]'hci).wStart + eL ∈ compUnemb ci
      dsimp only [compUnemb]
      split_ifs with hbad
      · simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range,
          Option.isNone_iff_eq_none]
        exact ⟨eL, ⟨heL, heW.2⟩, rfl⟩
      · exact False.elim (hbad hci)
  have hcomp_eq_sub : (Finset.range wd.comps.length).biUnion compUnemb ⊆ unembeddedSet1 wd s' := by
    intro eW heW
    rcases Finset.mem_biUnion.mp heW with ⟨ci, hci_r, hmem⟩
    have hci := Finset.mem_range.mp hci_r
    simp only [compUnemb, hci, ↓reduceDIte, Finset.mem_image, Finset.mem_filter,
      Finset.mem_range] at hmem
    rcases hmem with ⟨eL, ⟨heL, hnone⟩, rfl⟩
    have heWm := (W_edges_getD_comp tools H' J embJH hci heL).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr heWm, hnone⟩
  have hunemb_eq : unembeddedSet1 wd s' = (Finset.range wd.comps.length).biUnion compUnemb :=
    Finset.Subset.antisymm hunemb_sub hcomp_eq_sub
  have hvol_eq : volWRem wd s' = ∑ ci ∈ Finset.range wd.comps.length,
      ∑ eW ∈ compUnemb ci, wd.wW eW := by
    unfold volWRem
    rw [hunemb_eq, Finset.sum_biUnion hcomp_disj]
  have hcomp_bound : ∀ ci ∈ Finset.range wd.comps.length,
      ∑ eW ∈ compUnemb ci, wd.wW eW ≤
        (wd.c_deg * wd.γ_del / wd.φ_ds) *
          ((tools.pathDS.deleted (s'.dsJ.getD ci dsDef)).card : ℝ) := by
    intro ci hci_r
    have hci := Finset.mem_range.mp hci_r
    have hci_ds : ci < s'.dsJ.length := by rw [hcore.ds_len]; exact hci
    let c := wd.comps[ci]'hci
    let Vhat_ci := tools.pathDS.Vhat (s'.dsJ[ci]'hci_ds)
    let E_ci := (Finset.range c.W_sub.m).filter fun eL => (s'.embWJ (c.wStart + eL)).isNone
    have hsum_ci : ∑ eW ∈ compUnemb ci, wd.wW eW =
        (E_ci.card : ℝ) * (wd.φ_dec * 2 ^ c.level) := by
      simp only [compUnemb, hci, ↓reduceDIte]
      have hinj : Set.InjOn (fun eL => c.wStart + eL) E_ci := fun a _ b _ h => by
        dsimp only at h; omega
      rw [Finset.sum_image hinj]
      calc ∑ eL ∈ E_ci, wd.wW (c.wStart + eL)
          = ∑ _eL ∈ E_ci, (wd.φ_dec * 2 ^ c.level) := by
            refine Finset.sum_congr rfl fun eL heL => ?_
            exact (W_edges_getD_comp tools H' J embJH hci (Finset.mem_range.mp (Finset.mem_filter.mp heL).1)).2.2.2.2
        _ = (E_ci.card : ℝ) * (wd.φ_dec * 2 ^ c.level) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    rcases hw.comp_props ci hci with
      ⟨_, _, _, _, _, hc_Jn, _, _, _, _, _, hc_Wn, hc_Wvalid, _, _, _, _, hc_deg_le, _, _, _, _, _, _⟩
    have hE_card : E_ci.card ≤ c.W_sub.vol Vhat_ci := by
      refine card_edges_touching_le_vol c.W_sub Vhat_ci E_ci hc_Wvalid
        (Finset.filter_subset _ _) fun eL heL => ?_
      simp only [E_ci, Finset.mem_filter, Finset.mem_range, Option.isNone_iff_eq_none] at heL
      exact htouch ci hci eL heL.1 heL.2
    have hWvol_le : (c.W_sub.vol Vhat_ci : ℝ) * (wd.φ_dec * 2 ^ c.level) ≤
        wd.c_deg * (c.J_sub.vol Vhat_ci : ℝ) := by
      have hWvol_eq : (c.W_sub.vol Vhat_ci : ℝ) = ∑ k ∈ Vhat_ci, (c.W_sub.deg k : ℝ) := by
        have heqv : c.W_sub.vol Vhat_ci = ∑ k ∈ Vhat_ci, c.W_sub.deg k := rfl
        rw [heqv, Nat.cast_sum]
      have hJvol_eq : (c.J_sub.vol Vhat_ci : ℝ) = ∑ k ∈ Vhat_ci, (c.J_sub.deg k : ℝ) := by
        have heqv : c.J_sub.vol Vhat_ci = ∑ k ∈ Vhat_ci, c.J_sub.deg k := rfl
        rw [heqv, Nat.cast_sum]
      rw [hWvol_eq, hJvol_eq, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk => ?_
      have hk_J : k ∈ c.J_sub.verts := hcore.Vhat_sub ci hci hk
      have hk_card : k < c.X.card := by
        rw [← hc_Jn]
        exact Finset.mem_range.mp hk_J
      have hdeg := (hc_deg_le k hk_card).2
      have hφ_pos : 0 < wd.φ_dec * 2 ^ c.level := by
        have := hw.φ_dec_pos
        positivity
      calc (c.W_sub.deg k : ℝ) * (wd.φ_dec * 2 ^ c.level)
          ≤ (wd.c_deg * ((c.J_sub.deg k : ℝ) / (wd.φ_dec * 2 ^ c.level))) *
              (wd.φ_dec * 2 ^ c.level) :=
            mul_le_mul_of_nonneg_right hdeg hφ_pos.le
        _ = wd.c_deg * (c.J_sub.deg k : ℝ) := by
          have hφ0 : wd.φ_dec ≠ 0 := hw.φ_dec_pos.ne'
          field_simp [hφ_pos.ne', hφ0]
    have hVvol := hcore.Vhat_vol ci hci
    have hφ_pow_nn : 0 ≤ wd.φ_dec * 2 ^ c.level := by
      have := hw.φ_dec_pos
      positivity
    have hcdeg_nn : 0 ≤ wd.c_deg := le_trans (by norm_num) hw.c_deg_ge
    rw [hsum_ci, List.getD_eq_getElem _ _ hci_ds]
    calc (E_ci.card : ℝ) * (wd.φ_dec * 2 ^ c.level)
        ≤ (c.W_sub.vol Vhat_ci : ℝ) * (wd.φ_dec * 2 ^ c.level) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hE_card) hφ_pow_nn
      _ ≤ wd.c_deg * (c.J_sub.vol Vhat_ci : ℝ) := hWvol_le
      _ ≤ wd.c_deg * (wd.γ_del * ((tools.pathDS.deleted (s'.dsJ[ci]'hci_ds)).card : ℝ) / wd.φ_ds) :=
          mul_le_mul_of_nonneg_left hVvol hcdeg_nn
      _ = (wd.c_deg * wd.γ_del / wd.φ_ds) *
            ((tools.pathDS.deleted (s'.dsJ[ci]'hci_ds)).card : ℝ) := by ring
  rw [hvol_eq]
  calc ∑ ci ∈ Finset.range wd.comps.length, ∑ eW ∈ compUnemb ci, wd.wW eW
      ≤ ∑ ci ∈ Finset.range wd.comps.length,
          (wd.c_deg * wd.γ_del / wd.φ_ds) *
            ((tools.pathDS.deleted (s'.dsJ.getD ci dsDef)).card : ℝ) :=
        Finset.sum_le_sum hcomp_bound
    _ = (wd.c_deg * wd.γ_del / wd.φ_ds) *
          ((∑ ci ∈ Finset.range wd.comps.length,
            (tools.pathDS.deleted (s'.dsJ.getD ci dsDef)).card : ℕ) : ℝ) := by
        simp only [Nat.cast_sum, Finset.mul_sum]

theorem tau_half_eq {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk) :
    let wd := buildWitness tools H' J embJH
    wd.τ₁ / 2 = wd.γ_ExpPath * (length J embJH : ℝ) * wd.γ_del *
      (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) / wd.φ_ds := by
  intro wd
  change (2 * wd.γ_ExpPath * (length J embJH : ℝ) * wd.γ_del *
    (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) / wd.φ_ds) / 2 = _
  ring

theorem maxDeg_le_tau_half {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    (hlen : 1 ≤ length J embJH) :
    (maxDeg J : ℝ) ≤ (buildWitness tools H' J embJH).τ₁ / 2 := by
  set wd := buildWitness tools H' J embJH
  have hγE : 2 ≤ wd.γ_ExpPath := by
    have h1 : (2 : ℝ) ≤ 1 / wd.φ_ds := by
      rw [le_div_iff₀ hw.φ_ds_pos]
      nlinarith [hw.φ_ds_half]
    exact le_trans h1 hw.γ_ExpPath_ge
  have hlen_r : (1 : ℝ) ≤ (length J embJH : ℝ) := by exact_mod_cast hlen
  have hφ_inv : (2 : ℝ) ≤ 1 / wd.φ_ds := by
    rw [le_div_iff₀ hw.φ_ds_pos]; nlinarith [hw.φ_ds_half]
  have hvcong_nn : 0 ≤ vcong J H' (fun _ => 1) embJH := vcong_nonneg J H' (fun _ => 1) embJH
  rw [tau_half_eq tools H' J embJH]
  have h1 : (maxDeg J : ℝ) ≤ vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ) := by linarith
  have h2 : vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ) ≤
      (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) * (1 / wd.φ_ds) := by
    have hnn : 0 ≤ vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ) := by positivity
    nlinarith
  have h_prod : 1 ≤ wd.γ_ExpPath * (length J embJH : ℝ) * wd.γ_del := by
    have h3 : 1 ≤ wd.γ_del := hw.γ_del_ge
    have h12 : 2 ≤ wd.γ_ExpPath * (length J embJH : ℝ) := by nlinarith
    nlinarith
  have hφ_pos : 0 < wd.φ_ds := hw.φ_ds_pos
  have h3 : 0 ≤ (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) / wd.φ_ds := by positivity
  calc (maxDeg J : ℝ)
      ≤ vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ) := h1
    _ ≤ (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) * (1 / wd.φ_ds) := h2
    _ = (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) / wd.φ_ds := by ring
    _ ≤ (wd.γ_ExpPath * (length J embJH : ℝ) * wd.γ_del) *
          ((vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) / wd.φ_ds) := by nlinarith
    _ = wd.γ_ExpPath * (length J embJH : ℝ) * wd.γ_del *
          (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) / wd.φ_ds := by ring

lemma div_mul_assoc_swap (a b c d e : ℝ) :
    (a * b / c) * (d * e) = (a * b * e / c) * d := by ring

private lemma cancel_tau_factor (a b c d e f g : ℝ) :
    (a * b * c / d) * ((2 * e * f) * g) = (2 * a) * (e * f * b * c / d) * g := by ring

lemma two_mul_swap (a b : ℝ) : a * (2 * b) = 2 * a * b := by ring

lemma claim_8_7_algebra {V sP τh c g φ L γ v maxD se : ℝ}
    (hc : 0 ≤ c) (hg : 0 < g) (hφ : 0 < φ) (hL : 0 < L) (hγ : 0 < γ)
    (hv : 0 ≤ v) (hmax : 0 < maxD) (hse : 0 ≤ se)
    (hτ : τh = γ * L * g * (v + maxD) / φ)
    (hV : V ≤ (c * g * v / φ) * sP)
    (hsP : sP * τh ≤ (2 * γ * L) * se) :
    V ≤ (2 * c) * se := by
  have hτ_pos : 0 < τh := by
    rw [hτ]
    positivity
  have hK_nn : 0 ≤ c * g * v / φ := by positivity
  have h1 : V * τh ≤ (c * g * v / φ) * (sP * τh) := by
    calc V * τh ≤ ((c * g * v / φ) * sP) * τh := mul_le_mul_of_nonneg_right hV hτ_pos.le
      _ = (c * g * v / φ) * (sP * τh) := mul_assoc _ _ _
  have h2 : (c * g * v / φ) * (sP * τh) ≤ (c * g * v / φ) * ((2 * γ * L) * se) :=
    mul_le_mul_of_nonneg_left hsP hK_nn
  have h3 : (c * g * v / φ) * ((2 * γ * L) * se) =
      (2 * c) * (γ * L * g * v / φ) * se := by ring
  have hle_v : γ * L * g * v / φ ≤ τh := by
    rw [hτ]
    have h1' : v ≤ v + maxD := by linarith
    gcongr
  have h4 : (2 * c) * (γ * L * g * v / φ) * se ≤ (2 * c) * τh * se := by
    gcongr
  have hmul : V * τh ≤ ((2 * c) * se) * τh := by
    calc V * τh ≤ (2 * c) * τh * se := le_trans (le_trans h1 h2) (le_trans (le_of_eq h3) h4)
      _ = ((2 * c) * se) * τh := by ring
  exact le_of_mul_le_mul_right hmul hτ_pos


end MinCostFlow.Spanner
