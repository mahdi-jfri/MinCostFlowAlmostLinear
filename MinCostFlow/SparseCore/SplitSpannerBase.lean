module

public import MinCostFlow.SparseCore.SplitSpanner
public import MinCostFlow.SparseCore.CoreModel
public import MinCostFlow.Chain.EncodingSize

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Update consistency, quotient edge survival, and component projection helpers

Provides the base trajectory helpers for `SplitSpannerBounds.lean`:
1. `DynSpanner.update` graph consistency (`update_G_eq`, `update_nil`) and symmetric-difference
   cardinality bounds (`symmDiff_applyBatch_card_le`).
2. Exact quotient edge survival (`tildeStepSingle_CE_eq`, `tildeStepBatch_CE_sub`,
   `tildeStepBatch_disjoint_inserted`) and `extraSet` cardinality/transition bounds.
3. Component projection length and initial bucket congruence helpers
   (`projCompBatchG_length_le`, `initCompLSF_origBucket_congr`, `compLSFBatch_dynBatches_succ`).
-/

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner

@[expose] public section

/-! ## 1. `DynSpanner.update` helpers and `Finset` symmetric-difference recourse -/

lemma step_G_eq {L : ℕ} (cur : DynSpannerState L) (u : Update)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) :
    (DynSpanner.step cur u sparsify).state.G = cur.G.applyUpdate u := by
  dsimp only [DynSpanner.step]
  split_ifs <;> rfl

lemma updateGo_G_eq {L : ℕ}
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (cur : DynSpannerState L) (us : List Update)
    (uhAcc : List Update) (dAcc : Finset ℕ) (cAcc : ℕ) :
    (DynSpanner.updateGo sparsify cur us uhAcc dAcc cAcc).state.G = cur.G.applyBatch us := by
  induction us generalizing cur uhAcc dAcc cAcc with
  | nil => rfl
  | cons u rest ih =>
    dsimp only [DynSpanner.updateGo, MGraph.applyBatch, List.foldl_cons]
    rw [ih, step_G_eq]
    rfl

lemma update_G_eq {L : ℕ} (st : DynSpannerState L) (U : List Update)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) :
    (DynSpanner.update st U sparsify).state.G = st.G.applyBatch U :=
  updateGo_G_eq sparsify st U [] ∅ 0

lemma update_nil {L : ℕ} (st : DynSpannerState L)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) :
    DynSpanner.update st [] sparsify = ⟨st, [], ∅, 0⟩ := by
  simp [DynSpanner.update, DynSpanner.updateGo]

lemma symmDiff_applyBatch_card_le (G : MGraph) (U : List Update) :
    (G.E \ (G.applyBatch U).E).card + ((G.applyBatch U).E \ G.E).card ≤ U.length := by
  induction U generalizing G with
  | nil => simp [MGraph.applyBatch]
  | cons u rest ih =>
    simp only [MGraph.applyBatch, List.foldl_cons, List.length_cons]
    set G₁ := G.applyUpdate u
    set G' := G₁.applyBatch rest
    change (G.E \ G'.E).card + (G'.E \ G.E).card ≤ rest.length + 1
    have hstep : (G.E \ G₁.E).card + (G₁.E \ G.E).card ≤ 1 := by
      cases u with
      | delete e₀ =>
        have hsub : G.E \ G₁.E ⊆ {e₀} := fun x hx => by
          rw [Finset.mem_sdiff] at hx
          dsimp only [G₁, MGraph.applyUpdate] at hx
          by_cases hxe : x = e₀
          · simp [hxe]
          · exact absurd (Finset.mem_erase.mpr ⟨hxe, hx.1⟩) hx.2
        have hemp : G₁.E \ G.E = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr (Finset.erase_subset _ _)
        rw [hemp, Finset.card_empty, add_zero]
        exact le_trans (Finset.card_le_card hsub) (by simp)
      | insert e₀ _ _ =>
        have hemp : G.E \ G₁.E = ∅ :=
          Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_insert _ _)
        have hsub : G₁.E \ G.E ⊆ {e₀} := fun x hx => by
          rw [Finset.mem_sdiff] at hx
          dsimp only [G₁, MGraph.applyUpdate] at hx
          rcases Finset.mem_insert.mp hx.1 with rfl | hmem
          · simp
          · exact absurd hmem hx.2
        rw [hemp, Finset.card_empty, zero_add]
        exact le_trans (Finset.card_le_card hsub) (by simp)
      | split _ _ _ _ =>
        simp [G₁, MGraph.applyUpdate]
    have h1 : G.E \ G'.E ⊆ (G.E \ G₁.E) ∪ (G₁.E \ G'.E) := fun x hx => by
      rw [Finset.mem_sdiff] at hx
      by_cases hx1 : x ∈ G₁.E
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx1, hx.2⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx.1, hx1⟩)
    have h2 : G'.E \ G.E ⊆ (G'.E \ G₁.E) ∪ (G₁.E \ G.E) := fun x hx => by
      rw [Finset.mem_sdiff] at hx
      by_cases hx1 : x ∈ G₁.E
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx1, hx.2⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx.1, hx1⟩)
    have hc1 := le_trans (Finset.card_le_card h1) (Finset.card_union_le _ _)
    have hc2 := le_trans (Finset.card_le_card h2) (Finset.card_union_le _ _)
    have hih : (G₁.E \ G'.E).card + (G'.E \ G₁.E).card ≤ rest.length := ih G₁
    omega

/-! ## 2. Exact quotient edge survival, forest drops, and `extraNonLoopsSet` -/

lemma lsf_forest_diff_batch_le_R_diff {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} :
    ∀ (U : List Update) {S : LSFState},
      LSFInvWith thresh K_σ ℓ₀ S → S.G.BatchIsValid U →
      (S.RF.F.E \ (applyLSFBatch S U).RF.F.E).card ≤ ((applyLSFBatch S U).R \ S.R).card
  | [], S, _, _ => by simp [applyLSFBatch]
  | u :: rest, S, hI, ⟨hu, hU⟩ => by
    have h1 := applyLSFUpdate_inv_with hI hu
    set S₁ := applyLSFUpdate S u
    have h2 := applyLSFBatch_inv_with rest h1.1 (h1.2.1 ▸ hU)
    set S' := applyLSFBatch S₁ rest
    have hdiff1 := lsf_forest_diff_le_R_diff (lsfInv_to_RS hI) (lsfInv_to_RS h1.1)
      h1.2.1 hu h1.2.2.2.2.2.2.2.2.1 h1.2.2.2.2.2.2.2.2.2.1
    have hdiff2 := lsf_forest_diff_batch_le_R_diff rest h1.1 (h1.2.1 ▸ hU)
    have hsub_F : S.RF.F.E \ S'.RF.F.E ⊆ (S.RF.F.E \ S₁.RF.F.E) ∪ (S₁.RF.F.E \ S'.RF.F.E) := by
      intro e he
      rw [Finset.mem_sdiff] at he
      by_cases he1 : e ∈ S₁.RF.F.E
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨he1, he.2⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨he.1, he1⟩)
    have hc_F := le_trans (Finset.card_le_card hsub_F) (Finset.card_union_le _ _)
    have hR01 : S.R ⊆ S₁.R := h1.2.2.2.2.2.2.2.2.1
    have hR12 : S₁.R ⊆ S'.R := h2.2.2.2.2.2.2.2.2.1
    have hR02 : S.R ⊆ S'.R := Finset.Subset.trans hR01 hR12
    have hR_eq : (S₁.R \ S.R).card + (S'.R \ S₁.R).card = (S'.R \ S.R).card := by
      rw [Finset.card_sdiff_of_subset hR01, Finset.card_sdiff_of_subset hR12,
        Finset.card_sdiff_of_subset hR02]
      have c1 := Finset.card_le_card hR01
      have c2 := Finset.card_le_card hR12
      omega
    have hd1 : (S.RF.F.E \ S₁.RF.F.E).card ≤ (S₁.R \ S.R).card := hdiff1
    have hd2 : (S₁.RF.F.E \ S'.RF.F.E).card ≤ (S'.R \ S₁.R).card := hdiff2
    change (S.RF.F.E \ S'.RF.F.E).card ≤ (S'.R \ S.R).card
    omega

lemma applyBatch_splits_E_eq (C : MGraph) (parR : List Update)
    (hsp : ∀ op ∈ parR, isSplit op) :
    (C.applyBatch parR).E = C.E := by
  induction parR generalizing C with
  | nil => rfl
  | cons x xs ih =>
    simp only [MGraph.applyBatch, List.foldl_cons]
    have hx := hsp x List.mem_cons_self
    cases x with
    | delete _ => exact absurd hx (by simp [isSplit])
    | insert _ _ _ => exact absurd hx (by simp [isSplit])
    | split _ _ _ _ =>
      exact (ih (C.applyUpdate _) (fun y hy => hsp y (List.mem_cons_of_mem _ hy))).trans rfl

lemma tildeStepSingle_CE_eq {thresh K : ℝ} {ℓ₀ : ℕ → ℝ} {S₀ S : LSFState} {ts : TildeState}
    {u : Update} (hI : LSFInvWith thresh K ℓ₀ S) (hu : S.G.UpdateIsValid u)
    (hT : TildeInv S₀ S ts) :
    let res := tildeStepSingle S ts u
    res.2.1.C.E = ts.C.E ∩ res.2.2.G.E := by
  dsimp only [tildeStepSingle]
  have hsp := applyLSFUpdate_inv_with hI hu
  set S' := applyLSFUpdate S u
  set U_del := delStepC ts.C u
  set C_del := ts.C.applyBatch U_del
  set spA := splitStepA ts.m S.G C_del u ts.nextVid
  set C_mid := C_del.applyBatch spA.1
  set spB := rootSplitStep S S' C_mid spA.2.1 spA.2.2
  have hspB_E : (C_mid.applyBatch spB.1).E = C_mid.E := by
    refine applyBatch_splits_E_eq _ _ fun op hop => ?_
    dsimp only [spB, rootSplitStep] at hop
    rw [List.mem_map] at hop
    obtain ⟨_, _, rfl⟩ := hop
    rfl
  have hspA_E : C_mid.E = C_del.E := by
    refine applyBatch_splits_E_eq _ _ fun op hop => ?_
    cases u <;> simp [spA, splitStepA] at hop
    rcases hop with rfl; rfl
  change (C_mid.applyBatch spB.1).E = ts.C.E ∩ S'.G.E
  rw [hspB_E, hspA_E, show S'.G = S.G.applyUpdate u from hsp.2.1]
  have hCsubG : ts.C.E ⊆ S.G.E := Finset.Subset.trans hT.hCE_sub Finset.sdiff_subset
  cases u with
  | delete e₀ =>
    dsimp only [C_del, U_del, delStepC, MGraph.applyUpdate]
    split_ifs with he₀
    · simp only [MGraph.applyBatch, List.foldl_cons, List.foldl_nil, MGraph.applyUpdate]
      ext e
      simp only [Finset.mem_erase, Finset.mem_inter]
      tauto
    · simp only [MGraph.applyBatch, List.foldl_nil]
      ext e
      simp only [Finset.mem_inter, Finset.mem_erase]
      exact ⟨fun he => ⟨he, fun h => he₀ (h ▸ he), hCsubG he⟩, fun ⟨he, _⟩ => he⟩
  | insert e₀ a b =>
    simp only [C_del, U_del, delStepC, MGraph.applyBatch, List.foldl_nil, MGraph.applyUpdate]
    ext e
    simp only [Finset.mem_inter, Finset.mem_insert]
    exact ⟨fun he => ⟨he, Or.inr (hCsubG he)⟩, fun ⟨he, _⟩ => he⟩
  | split _ _ _ _ =>
    simp only [C_del, U_del, delStepC, MGraph.applyBatch, List.foldl_nil, MGraph.applyUpdate]
    exact (Finset.inter_eq_left.mpr hCsubG).symm

lemma tildeStepBatch_CE_sub {thresh₀ K₀ thresh K : ℝ} {ℓ₀ : ℕ → ℝ} {S₀ : LSFState}
    (hI₀ : LSFInvWith thresh₀ K₀ ℓ₀ S₀) (hCov₀ : S₀.W_init.biUnion (inducedEdges S₀.RF.F) = S₀.RF.F.E) :
    ∀ (U : List Update) {S : LSFState} {ts : TildeState},
      LSFInvWith thresh K ℓ₀ S → LSFDerivedFrom S₀ S → S.G.BatchIsValid U → TildeInv S₀ S ts →
      (tildeStepBatch S ts U).2.1.C.E ⊆ ts.C.E := by
  intro U
  induction U with
  | nil => intro S ts _ _ _ _; exact Finset.Subset.rfl
  | cons u rest ih =>
    intro S ts hI hD ⟨hu, hU⟩ hT
    have hsp := applyLSFUpdate_inv_with hI hu
    have h1 := tildeStepSingle_spec hI₀ hCov₀ hI hu hD hT
    have hCE1 := tildeStepSingle_CE_eq hI hu hT
    set r1 := tildeStepSingle S ts u
    have hS1_eq : r1.2.2 = applyLSFUpdate S u := h1.1
    have hD1 : LSFDerivedFrom S₀ r1.2.2 := hS1_eq ▸ lsfDerivedFrom_step hI hu hD
    have hI1 : LSFInvWith thresh K ℓ₀ r1.2.2 := hS1_eq ▸ hsp.1
    have hU1 : r1.2.2.G.BatchIsValid rest := hS1_eq ▸ (hsp.2.1 ▸ hU)
    exact Finset.Subset.trans (ih hI1 hD1 hU1 h1.2.1) (hCE1 ▸ Finset.inter_subset_left)

lemma tildeStepBatch_disjoint_inserted {thresh₀ K₀ thresh K : ℝ} {ℓ₀ : ℕ → ℝ} {S₀ : LSFState}
    (hI₀ : LSFInvWith thresh₀ K₀ ℓ₀ S₀) (hCov₀ : S₀.W_init.biUnion (inducedEdges S₀.RF.F) = S₀.RF.F.E) :
    ∀ (U : List Update) {S : LSFState} {ts : TildeState},
      LSFInvWith thresh K ℓ₀ S → LSFDerivedFrom S₀ S → S.G.BatchIsValid U → TildeInv S₀ S ts →
      Disjoint ts.C.E S.insertedEdges →
      Disjoint (tildeStepBatch S ts U).2.1.C.E (tildeStepBatch S ts U).2.2.insertedEdges := by
  intro U
  induction U with
  | nil => intro S ts _ _ _ _ hDisj; exact hDisj
  | cons u rest ih =>
    intro S ts hI hD ⟨hu, hU⟩ hT hDisj
    have hsp := applyLSFUpdate_inv_with hI hu
    have h1 := tildeStepSingle_spec hI₀ hCov₀ hI hu hD hT
    have hCE1 := tildeStepSingle_CE_eq hI hu hT
    set r1 := tildeStepSingle S ts u
    have hS1_eq : r1.2.2 = applyLSFUpdate S u := h1.1
    have hD1 : LSFDerivedFrom S₀ r1.2.2 := hS1_eq ▸ lsfDerivedFrom_step hI hu hD
    have hI1 : LSFInvWith thresh K ℓ₀ r1.2.2 := hS1_eq ▸ hsp.1
    have hU1 : r1.2.2.G.BatchIsValid rest := hS1_eq ▸ (hsp.2.1 ▸ hU)
    have hDisj1 : Disjoint r1.2.1.C.E r1.2.2.insertedEdges := by
      rw [hS1_eq, applyLSFUpdate_insertedEdges]
      refine Finset.disjoint_left.mpr fun e heC heI => ?_
      rw [hCE1, Finset.mem_inter] at heC
      cases u with
      | delete e₀ =>
        dsimp only [updateInserted] at heI
        exact Finset.disjoint_left.mp hDisj heC.1 (Finset.erase_subset _ _ heI)
      | split _ _ _ _ =>
        exact Finset.disjoint_left.mp hDisj heC.1 heI
      | insert e₀ a b =>
        dsimp only [updateInserted] at heI
        rcases Finset.mem_insert.mp heI with rfl | hmem
        · exact hu.1 ((Finset.mem_sdiff.mp (hT.hCE_sub heC.1)).1)
        · exact Finset.disjoint_left.mp hDisj heC.1 hmem
    exact ih hI1 hD1 hU1 h1.2.1 hDisj1

/-- Off-forest core edges missing from `\tilde{C}`. -/
noncomputable def extraSet (S : LSFState) (ts : TildeState) : Finset ℕ :=
  (S.G.E \ S.RF.F.E) \ ts.C.E

lemma extraSet_init (S₀ : LSFState) : extraSet S₀ (initTildeState S₀) = ∅ := by
  ext e
  simp only [extraSet, initTildeState, tildeC0Base, Finset.mem_sdiff, Finset.notMem_empty,
    iff_false]
  intro h
  exact h.2 h.1

lemma extraSet_single_diff_le {thresh K : ℝ} {ℓ₀ : ℕ → ℝ} {S₀ S : LSFState}
    {ts : TildeState} {u : Update}
    (hI : LSFInvWith thresh K ℓ₀ S) (hu : S.G.UpdateIsValid u) (hT : TildeInv S₀ S ts) :
    let r1 := tildeStepSingle S ts u
    let S₁ := r1.2.2
    let ts₁ := r1.2.1
    (extraSet S₁ ts₁ \ extraSet S ts).card ≤ 1 + (S₁.R \ S.R).card ∧
    (extraSet S ts \ extraSet S₁ ts₁).card ≤ 1 := by
  classical
  intro r1 S₁ ts₁
  have h1 := applyLSFUpdate_inv_with hI hu
  have hS1G : S₁.G = S.G.applyUpdate u := h1.2.1
  have hCE1 := tildeStepSingle_CE_eq hI hu hT
  have hdiff_F : (S.RF.F.E \ S₁.RF.F.E).card ≤ (S₁.R \ S.R).card :=
    lsf_forest_diff_le_R_diff (lsfInv_to_RS hI) (lsfInv_to_RS h1.1)
      h1.2.1 hu h1.2.2.2.2.2.2.2.2.1 h1.2.2.2.2.2.2.2.2.2.1
  let insSet : Finset ℕ := match u with | .insert e₀ _ _ => {e₀} | _ => ∅
  have hsub_add : extraSet S₁ ts₁ \ extraSet S ts ⊆ insSet ∪ (S.RF.F.E \ S₁.RF.F.E) := by
    intro e he
    rw [Finset.mem_sdiff] at he
    have he1 := he.1
    simp only [extraSet, Finset.mem_sdiff] at he1
    have heG₁ : e ∈ S₁.G.E := he1.1.1
    have henF₁ : e ∉ S₁.RF.F.E := he1.1.2
    have henC₁ : e ∉ ts₁.C.E := he1.2
    have henC : e ∉ ts.C.E := fun hc => henC₁ (hCE1 ▸ Finset.mem_inter.mpr ⟨hc, heG₁⟩)
    simp only [Finset.mem_union]
    by_cases heG : e ∈ S.G.E
    · right
      refine Finset.mem_sdiff.mpr ⟨?_, henF₁⟩
      by_contra heF
      exact he.2 (by simp only [extraSet, Finset.mem_sdiff]; exact ⟨⟨heG, heF⟩, henC⟩)
    · left
      cases u with
      | delete e₀ =>
        rw [hS1G, MGraph.applyUpdate, Finset.mem_erase] at heG₁
        exact absurd heG₁.2 heG
      | split _ _ _ _ =>
        rw [hS1G, MGraph.applyUpdate] at heG₁
        exact absurd heG₁ heG
      | insert e₀ a b =>
        rw [hS1G, MGraph.applyUpdate, Finset.mem_insert] at heG₁
        rcases heG₁ with rfl | hmem
        · simp [insSet]
        · exact absurd hmem heG
  have hc_ins : insSet.card ≤ 1 := by cases u <;> simp [insSet]
  have hc_add : (extraSet S₁ ts₁ \ extraSet S ts).card ≤ 1 + (S₁.R \ S.R).card := by
    refine le_trans (Finset.card_le_card hsub_add) ?_
    exact le_trans (Finset.card_union_le _ _) (by omega)
  let delSet : Finset ℕ := match u with | .delete e₀ => {e₀} | _ => ∅
  have hsub_drop : extraSet S ts \ extraSet S₁ ts₁ ⊆ delSet := by
    intro e he
    rw [Finset.mem_sdiff] at he
    have he0 := he.1
    simp only [extraSet, Finset.mem_sdiff] at he0
    have heG : e ∈ S.G.E := he0.1.1
    have heF : e ∉ S.RF.F.E := he0.1.2
    have heC : e ∉ ts.C.E := he0.2
    by_contra hnot
    apply he.2
    have heG₁ : e ∈ S₁.G.E := by
      rw [hS1G]
      cases u with
      | delete e₀ =>
        simp only [MGraph.applyUpdate, Finset.mem_erase]
        exact ⟨fun h => hnot (by simp [delSet, h]), heG⟩
      | insert _ _ _ => simp [MGraph.applyUpdate, heG]
      | split _ _ _ _ => simp [MGraph.applyUpdate, heG]
    have heF₁ : e ∉ S₁.RF.F.E := fun hf => heF (h1.2.2.2.2.2.2.2.2.2.1 hf)
    have heC₁ : e ∉ ts₁.C.E := fun hc => heC ((hCE1 ▸ hc |> Finset.mem_inter.mp).1)
    simp only [extraSet, Finset.mem_sdiff]
    exact ⟨⟨heG₁, heF₁⟩, heC₁⟩
  have hc_del : delSet.card ≤ 1 := by cases u <;> simp [delSet]
  exact ⟨hc_add, le_trans (Finset.card_le_card hsub_drop) hc_del⟩

lemma extraSet_batch_diff_le {thresh₀ K₀ thresh K : ℝ} {ℓ₀ : ℕ → ℝ} {S₀ : LSFState}
    (hI₀ : LSFInvWith thresh₀ K₀ ℓ₀ S₀) (hCov₀ : S₀.W_init.biUnion (inducedEdges S₀.RF.F) = S₀.RF.F.E) :
    ∀ (U : List Update) {S : LSFState} {ts : TildeState},
      LSFInvWith thresh K ℓ₀ S → LSFDerivedFrom S₀ S → S.G.BatchIsValid U → TildeInv S₀ S ts →
      let td := tildeStepBatch S ts U
      (extraSet td.2.2 td.2.1 \ extraSet S ts).card ≤ U.length + (td.2.2.R \ S.R).card ∧
      (extraSet S ts \ extraSet td.2.2 td.2.1).card ≤ U.length := by
  intro U
  induction U with
  | nil =>
    intro S ts _ _ _ _
    simp [tildeStepBatch]
  | cons u rest ih =>
    intro S ts hI hD ⟨hu, hU⟩ hT
    have h1_LSF := applyLSFUpdate_inv_with hI hu
    have h1_ts := tildeStepSingle_spec hI₀ hCov₀ hI hu hD hT
    have h1_ex := extraSet_single_diff_le hI hu hT
    set r1 := tildeStepSingle S ts u
    have hS1_eq : r1.2.2 = applyLSFUpdate S u := h1_ts.1
    have hI1 : LSFInvWith thresh K ℓ₀ r1.2.2 := hS1_eq ▸ h1_LSF.1
    have hD1 : LSFDerivedFrom S₀ r1.2.2 := hS1_eq ▸ lsfDerivedFrom_step hI hu hD
    have hU1 : r1.2.2.G.BatchIsValid rest := hS1_eq ▸ (h1_LSF.2.1 ▸ hU)
    have h2 := ih hI1 hD1 hU1 h1_ts.2.1
    set td := tildeStepBatch S ts (u :: rest)
    set td2 := tildeStepBatch r1.2.2 r1.2.1 rest
    have htd_S2 : td.2.2 = td2.2.2 := rfl
    have htd_T2 : td.2.1 = td2.2.1 := rfl
    have hR01 : S.R ⊆ r1.2.2.R := hS1_eq ▸ h1_LSF.2.2.2.2.2.2.2.2.1
    have hR12 : r1.2.2.R ⊆ td2.2.2.R := by
      have hspec := (tildeStepBatch_spec hI₀ hCov₀ hI1 hD1 h1_ts.2.1 hU1).1
      rw [hspec]
      exact (applyLSFBatch_inv_with rest hI1 hU1).2.2.2.2.2.2.2.2.1
    have hR02 : S.R ⊆ td2.2.2.R := Finset.Subset.trans hR01 hR12
    have hR_eq : (r1.2.2.R \ S.R).card + (td2.2.2.R \ r1.2.2.R).card =
        (td2.2.2.R \ S.R).card := by
      rw [Finset.card_sdiff_of_subset hR01, Finset.card_sdiff_of_subset hR12,
        Finset.card_sdiff_of_subset hR02]
      have c1 := Finset.card_le_card hR01
      have c2 := Finset.card_le_card hR12
      omega
    have hadd_sub : extraSet td2.2.2 td2.2.1 \ extraSet S ts ⊆
        (extraSet td2.2.2 td2.2.1 \ extraSet r1.2.2 r1.2.1) ∪
          (extraSet r1.2.2 r1.2.1 \ extraSet S ts) := by
      intro e he
      rw [Finset.mem_sdiff] at he
      by_cases he1 : e ∈ extraSet r1.2.2 r1.2.1
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨he1, he.2⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨he.1, he1⟩)
    have hdrop_sub : extraSet S ts \ extraSet td2.2.2 td2.2.1 ⊆
        (extraSet S ts \ extraSet r1.2.2 r1.2.1) ∪
          (extraSet r1.2.2 r1.2.1 \ extraSet td2.2.2 td2.2.1) := by
      intro e he
      rw [Finset.mem_sdiff] at he
      by_cases he1 : e ∈ extraSet r1.2.2 r1.2.1
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨he1, he.2⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨he.1, he1⟩)
    have hc_add := le_trans (Finset.card_le_card hadd_sub) (Finset.card_union_le _ _)
    have hc_drop := le_trans (Finset.card_le_card hdrop_sub) (Finset.card_union_le _ _)
    have h1_ex_add : (extraSet r1.2.2 r1.2.1 \ extraSet S ts).card ≤
        1 + (r1.2.2.R \ S.R).card := h1_ex.1
    have h1_ex_drop : (extraSet S ts \ extraSet r1.2.2 r1.2.1).card ≤ 1 := h1_ex.2
    have h2_add : (extraSet td2.2.2 td2.2.1 \ extraSet r1.2.2 r1.2.1).card ≤
        rest.length + (td2.2.2.R \ r1.2.2.R).card := h2.1
    have h2_drop : (extraSet r1.2.2 r1.2.1 \ extraSet td2.2.2 td2.2.1).card ≤ rest.length := h2.2
    dsimp only [td]
    rw [htd_S2, htd_T2, List.length_cons]
    constructor <;> omega

lemma extraSet_batch_card_le {thresh₀ K₀ thresh K : ℝ} {ℓ₀ : ℕ → ℝ} {S₀ : LSFState}
    (hI₀ : LSFInvWith thresh₀ K₀ ℓ₀ S₀) (hCov₀ : S₀.W_init.biUnion (inducedEdges S₀.RF.F) = S₀.RF.F.E)
    {U : List Update} {S : LSFState} {ts : TildeState}
    (hI : LSFInvWith thresh K ℓ₀ S) (hD : LSFDerivedFrom S₀ S) (hBU : S.G.BatchIsValid U)
    (hT : TildeInv S₀ S ts) :
    let td := tildeStepBatch S ts U
    (extraSet td.2.2 td.2.1).card ≤
      (extraSet S ts).card + U.length + (td.2.2.R \ S.R).card := by
  have h := (extraSet_batch_diff_le hI₀ hCov₀ U hI hD hBU hT).1
  set td := tildeStepBatch S ts U
  have hsub : extraSet td.2.2 td.2.1 ⊆
      (extraSet td.2.2 td.2.1 \ extraSet S ts) ∪ extraSet S ts := by
    intro e he
    rw [Finset.mem_union, Finset.mem_sdiff]
    by_cases hm : e ∈ extraSet S ts
    · exact Or.inr hm
    · exact Or.inl ⟨he, hm⟩
  have hc := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  omega

/-! ## 3. Component projection helpers and Stage-1 invariant on `treeRunSeq` -/

lemma projCompUpdateG_length_le_two (G_glob G_C : MGraph) (u : Update) :
    (projCompUpdateG G_glob G_C u).length ≤ 2 := by
  classical
  cases u <;> simp only [projCompUpdateG] <;> split_ifs <;> simp

lemma projCompBatchG_length_le : ∀ (U : List Update) (G_glob G_C : MGraph),
    (projCompBatchG G_glob G_C U).length ≤ 2 * U.length
  | [], _, _ => by simp [projCompBatchG]
  | u :: rest, G_glob, G_C => by
    dsimp only [projCompBatchG]
    rw [List.length_append, List.length_cons]
    have h1 := projCompUpdateG_length_le_two G_glob G_C u
    have h2 := projCompBatchG_length_le rest (G_glob.applyUpdate u)
      (G_C.applyBatch (projCompUpdateG G_glob G_C u))
    omega

/-- Effective per-update projection weight on a component: `0` when the component is untouched,
`1` when it is touched (including a cross-insert projected to `[insert, delete]`). -/
noncomputable def projCompUpdateWeight (G_glob G_C : MGraph) (u : Update) : ℕ :=
  if projCompUpdateG G_glob G_C u = [] then 0 else 1

/-- Effective per-batch projection weight on a component: counts the number of updates in `U`
that touch the component. -/
noncomputable def projCompBatchWeight (G_glob G_C : MGraph) : List Update → ℕ
  | [] => 0
  | u :: rest =>
      projCompUpdateWeight G_glob G_C u +
        projCompBatchWeight (G_glob.applyUpdate u)
          (G_C.applyBatch (projCompUpdateG G_glob G_C u)) rest

lemma projCompUpdateWeight_le_one (G_glob G_C : MGraph) (u : Update) :
    projCompUpdateWeight G_glob G_C u ≤ 1 := by
  unfold projCompUpdateWeight; split_ifs <;> omega

lemma projCompBatchWeight_le_length : ∀ (U : List Update) (G_glob G_C : MGraph),
    projCompBatchWeight G_glob G_C U ≤ U.length
  | [], _, _ => by simp [projCompBatchWeight]
  | u :: rest, G_glob, G_C => by
    dsimp only [projCompBatchWeight]
    rw [List.length_cons]
    have h1 := projCompUpdateWeight_le_one G_glob G_C u
    have h2 := projCompBatchWeight_le_length rest (G_glob.applyUpdate u)
      (G_C.applyBatch (projCompUpdateG G_glob G_C u))
    omega

lemma sum_projCompUpdateWeight_le {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) (u : Update) :
    (components cs.G₀).sum (fun C => projCompUpdateWeight cs.G (cs.compSt C).G u) ≤ 2 := by
  classical
  have heq : (components cs.G₀).sum (fun C => projCompUpdateWeight cs.G (cs.compSt C).G u) =
      (touchedComps cs u).card := by
    rw [touchedComps, Finset.card_filter]
    refine Finset.sum_congr rfl fun C _ => ?_
    unfold projCompUpdateWeight
    split_ifs <;> simp_all
  rw [heq]
  exact touchedComps_card_le hI u

lemma sum_projCompBatchWeight_le {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} :
    ∀ (U : List Update) {cs : CompLSFState}, CompLSFInv C_lsst ℓ₀ cs → cs.G.BatchIsValid U →
      (components cs.G₀).sum (fun C => projCompBatchWeight cs.G (cs.compSt C).G U) ≤ 2 * U.length
  | [], _, _, _ => by simp [projCompBatchWeight]
  | u :: rest, cs, hI, ⟨hu, hrest⟩ => by
    have h1 := compLSFInv_step hI hu
    have ih := sum_projCompBatchWeight_le rest h1 hrest
    have hsum1 := sum_projCompUpdateWeight_le hI u
    have hsum_rest : (components cs.G₀).sum (fun C =>
        projCompBatchWeight (cs.G.applyUpdate u)
          ((cs.compSt C).G.applyBatch (projCompUpdateG cs.G (cs.compSt C).G u)) rest) ≤
        2 * rest.length := by
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun C hC => ?_)) ih
      have hB := applyLSFBatch_inv_with (projCompUpdateG cs.G (cs.compSt C).G u)
        (hI.hCompLSF C hC).1 (projCompUpdateG_valid hI hu hC)
      change projCompBatchWeight _ _ rest = projCompBatchWeight (cs.G.applyUpdate u)
        (applyLSFBatch (cs.compSt C) (projCompUpdateG cs.G (cs.compSt C).G u)).G rest
      rw [hB.2.1]
    have hsplit : (components cs.G₀).sum (fun C => projCompBatchWeight cs.G (cs.compSt C).G (u :: rest)) =
        (components cs.G₀).sum (fun C => projCompUpdateWeight cs.G (cs.compSt C).G u) +
        (components cs.G₀).sum (fun C =>
          projCompBatchWeight (cs.G.applyUpdate u)
            ((cs.compSt C).G.applyBatch (projCompUpdateG cs.G (cs.compSt C).G u)) rest) := by
      simp only [projCompBatchWeight, Finset.sum_add_distrib]
    rw [hsplit, List.length_cons]
    omega

lemma tildeStepBatch_append (S : LSFState) (ts : TildeState) (U₁ U₂ : List Update) :
    let r1 := tildeStepBatch S ts U₁
    let r2 := tildeStepBatch r1.2.2 r1.2.1 U₂
    tildeStepBatch S ts (U₁ ++ U₂) = (r1.1 ++ r2.1, r2.2.1, r2.2.2) := by
  induction U₁ generalizing S ts with
  | nil => simp [tildeStepBatch]
  | cons u rest ih =>
    dsimp only [List.cons_append, tildeStepBatch]; rw [ih]; simp [List.append_assoc]

lemma tildeStepSingle_insert_length_eq_splitCount (S : LSFState) (ts : TildeState) (e a b : ℕ) :
    (tildeStepSingle S ts (.insert e a b)).1.length =
      batchSplitCount (tildeStepSingle S ts (.insert e a b)).1 := by
  dsimp only [tildeStepSingle, delStepC, splitStepA, List.nil_append, rootSplitStep, batchSplitCount]
  symm; rw [List.countP_eq_length]; intro op hop
  rw [List.mem_map] at hop; obtain ⟨_, _, rfl⟩ := hop; rfl

lemma tildeStepBatch_insert_delete_selfLoop {thresh₀ K₀ thresh K : ℝ} {ℓ₀ : ℕ → ℝ}
    {S₀ S : LSFState} {ts : TildeState} {e a : ℕ}
    (hI₀ : LSFInvWith thresh₀ K₀ ℓ₀ S₀)
    (hCov₀ : S₀.W_init.biUnion (inducedEdges S₀.RF.F) = S₀.RF.F.E)
    (hI : LSFInvWith thresh K ℓ₀ S) (hD : LSFDerivedFrom S₀ S) (hT : TildeInv S₀ S ts)
    (ha : a ∈ S.G.V) (he : e ∉ S.G.E) :
    let td := tildeStepBatch S ts [.insert e a a, .delete e]
    batchSplitCount td.1 ≤ (td.2.2.R \ S.R).card ∧
    ((td.1.length : ℝ) ≤ (S₀.G.maxDeg : ℝ) + 1 + 56 * (Real.log ((S₀.G₀.n : ℝ) + 2)) ^ 2) ∧
    (extraSet td.2.2 td.2.1 \ extraSet S ts).card ≤ (td.2.2.R \ S.R).card ∧
    (extraSet S ts \ extraSet td.2.2 td.2.1).card = 0 := by
  have hu1 : S.G.UpdateIsValid (.insert e a a) := ⟨he, ha, ha⟩
  have h1_lsf := applyLSFUpdate_inv_with (u := .insert e a a) hI hu1
  have h1_ts := tildeStepSingle_spec hI₀ hCov₀ hI hu1 hD hT
  have h1_CE := tildeStepSingle_CE_eq hI hu1 hT
  set r1 := tildeStepSingle S ts (.insert e a a)
  have hS1_eq : r1.2.2 = applyLSFUpdate S (.insert e a a) := h1_ts.1
  have hI1 : LSFInvWith thresh K ℓ₀ r1.2.2 := hS1_eq ▸ h1_lsf.1
  have hD1 : LSFDerivedFrom S₀ r1.2.2 := hS1_eq ▸ lsfDerivedFrom_step hI hu1 hD
  have hG1 : r1.2.2.G = S.G.applyUpdate (.insert e a a) := hS1_eq ▸ h1_lsf.2.1
  have hu2 : r1.2.2.G.UpdateIsValid (.delete e) := by rw [hG1]; exact Finset.mem_insert_self e S.G.E
  have h2_lsf := applyLSFUpdate_inv_with (u := .delete e) hI1 hu2
  have h2_ts := tildeStepSingle_spec hI₀ hCov₀ hI1 hu2 hD1 h1_ts.2.1
  have h2_CE := tildeStepSingle_CE_eq hI1 hu2 h1_ts.2.1
  set r2 := tildeStepSingle r1.2.2 r1.2.1 (.delete e)
  have hS2_eq : r2.2.2 = applyLSFUpdate r1.2.2 (.delete e) := h2_ts.1
  have hpair := applyLSFBatch_insert_delete_selfLoop hI he ha
  have hS2_pair : r2.2.2 = applyLSFBatch S [.insert e a a, .delete e] := by rw [hS2_eq, hS1_eq]; rfl
  have hR_eq : r2.2.2.R = r1.2.2.R := by rw [hS2_pair, hS1_eq]; exact hpair.2.2.2.2.2.2
  have hGE_eq : r2.2.2.G.E = S.G.E := by rw [hS2_pair]; exact hpair.2.2.1
  have hR01 : S.R ⊆ r1.2.2.R := hS1_eq ▸ h1_lsf.2.2.2.2.2.2.2.2.1
  have hR12_empty : (r2.2.2.R \ r1.2.2.R).card = 0 := by rw [hR_eq, Finset.sdiff_self]; rfl
  have htd_eq : tildeStepBatch S ts [.insert e a a, .delete e] = (r1.1 ++ r2.1, r2.2.1, r2.2.2) := by
    simp [tildeStepBatch, r1, r2]
  dsimp only; rw [htd_eq]
  have h1_sc : batchSplitCount r1.1 ≤ (r1.2.2.R \ S.R).card := by
    have h := h1_ts.2.2.2.2.2.1; simp [updateSplitTag, updateForestSplitCard] at h; exact h
  have h2_sc : batchSplitCount r2.1 = 0 := by
    have h := h2_ts.2.2.2.2.2.1; simp [updateSplitTag, updateForestSplitCard, hR12_empty] at h; exact h
  have h1_len : r1.1.length ≤ (r1.2.2.R \ S.R).card := by
    rw [tildeStepSingle_insert_length_eq_splitCount]; exact h1_sc
  have h2_len : r2.1.length ≤ 1 := by
    have h := h2_ts.2.2.2.2.2.2.1; simp [updateForestSplitCard, hR12_empty] at h; exact h
  have hR1_real : ((r1.2.2.R \ S.R).card : ℝ) ≤ 56 * (Real.log ((S₀.G₀.n : ℝ) + 2)) ^ 2 := by
    rw [Finset.card_sdiff_of_subset hR01, Nat.cast_sub (Finset.card_le_card hR01)]
    have hR_le := h1_lsf.2.2.2.2.2.2.2.2.2.2; rw [← hS1_eq, hD.hG₀_eq] at hR_le; linarith
  have hC1_E : r1.2.1.C.E = ts.C.E := by
    rw [h1_CE, hG1]
    have hsub : ts.C.E ⊆ S.G.E := Finset.Subset.trans hT.hCE_sub Finset.sdiff_subset
    ext x; simp only [Finset.mem_inter, MGraph.applyUpdate, Finset.mem_insert]
    exact ⟨fun h => h.1, fun hx => ⟨hx, Or.inr (hsub hx)⟩⟩
  have hC2_E : r2.2.1.C.E = ts.C.E := by
    rw [h2_CE, hC1_E, hGE_eq]
    exact Finset.inter_eq_left.mpr (Finset.Subset.trans hT.hCE_sub Finset.sdiff_subset)
  have hF1_sub : r1.2.2.RF.F.E ⊆ S.RF.F.E := hS1_eq ▸ h1_lsf.2.2.2.2.2.2.2.2.2.1
  have hF2_sub : r2.2.2.RF.F.E ⊆ r1.2.2.RF.F.E := hS2_eq ▸ h2_lsf.2.2.2.2.2.2.2.2.2.1
  have hF1_diff : (S.RF.F.E \ r1.2.2.RF.F.E).card ≤ (r1.2.2.R \ S.R).card :=
    lsf_forest_diff_le_R_diff (lsfInv_to_RS hI) (lsfInv_to_RS hI1) hG1 hu1 hR01 hF1_sub
  have hF2_diff : (r1.2.2.RF.F.E \ r2.2.2.RF.F.E).card ≤ 0 := by
    have h := lsf_forest_diff_le_R_diff (lsfInv_to_RS hI1) (lsfInv_to_RS (hS2_eq ▸ h2_lsf.1))
      (hS2_eq ▸ h2_lsf.2.1) hu2 (by rw [hR_eq]) hF2_sub
    omega
  have hF_diff : (S.RF.F.E \ r2.2.2.RF.F.E).card ≤ (r2.2.2.R \ S.R).card := by
    have hsub : S.RF.F.E \ r2.2.2.RF.F.E ⊆ (S.RF.F.E \ r1.2.2.RF.F.E) ∪ (r1.2.2.RF.F.E \ r2.2.2.RF.F.E) := fun x hx => by
      rw [Finset.mem_sdiff] at hx; by_cases h1 : x ∈ r1.2.2.RF.F.E
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h1, hx.2⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx.1, h1⟩)
    have hc := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _); rw [hR_eq]; omega
  refine ⟨by rw [batchSplitCount_append, hR_eq]; omega, ?_, ?_, ?_⟩
  · rw [List.length_append, Nat.cast_add]
    have h1r : (r1.1.length : ℝ) ≤ ((r1.2.2.R \ S.R).card : ℝ) := by exact_mod_cast h1_len
    have h2r : (r2.1.length : ℝ) ≤ 1 := by exact_mod_cast h2_len
    have hd : (0 : ℝ) ≤ (S₀.G.maxDeg : ℝ) := Nat.cast_nonneg _; linarith
  · have hsub : extraSet r2.2.2 r2.2.1 \ extraSet S ts ⊆ S.RF.F.E \ r2.2.2.RF.F.E := fun x hx => by
      simp only [extraSet, Finset.mem_sdiff, hGE_eq, hC2_E] at hx ⊢
      exact ⟨by by_contra hF; exact hx.2 ⟨⟨hx.1.1.1, hF⟩, hx.1.2⟩, hx.1.1.2⟩
    exact le_trans (Finset.card_le_card hsub) hF_diff
  · rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset]; intro x hx
    simp only [extraSet, Finset.mem_sdiff, hGE_eq, hC2_E] at hx ⊢
    exact ⟨⟨hx.1.1, fun hF => hx.1.2 (hF1_sub (hF2_sub hF))⟩, hx.2⟩

lemma tildeStepBatch_projCompUpdateG_spec {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {thresh₀ K₀ : ℝ}
    {S₀ : LSFState} {cs : CompLSFState} {C : Finset ℕ} {ts : TildeState} {u : Update}
    (hI₀ : LSFInvWith thresh₀ K₀ ℓ₀ S₀)
    (hCov₀ : S₀.W_init.biUnion (inducedEdges S₀.RF.F) = S₀.RF.F.E)
    (hI : CompLSFInv C_lsst ℓ₀ cs) (hC : C ∈ components cs.G₀)
    (hD : LSFDerivedFrom S₀ (cs.compSt C)) (hT : TildeInv S₀ (cs.compSt C) ts)
    (hu : cs.G.UpdateIsValid u) :
    let Up := projCompUpdateG cs.G (cs.compSt C).G u
    let w := projCompUpdateWeight cs.G (cs.compSt C).G u
    let td := tildeStepBatch (cs.compSt C) ts Up
    batchSplitCount td.1 ≤ w * (S₀.G.maxDeg + 1) + (td.2.2.R \ (cs.compSt C).R).card ∧
    ((td.1.length : ℝ) ≤ (w : ℝ) *
      ((S₀.G.maxDeg : ℝ) + 1 + 56 * (Real.log ((S₀.G₀.n : ℝ) + 2)) ^ 2)) ∧
    (extraSet td.2.2 td.2.1 \ extraSet (cs.compSt C) ts).card ≤
      w + (td.2.2.R \ (cs.compSt C).R).card ∧
    (extraSet (cs.compSt C) ts \ extraSet td.2.2 td.2.1).card ≤ w := by
  have hCI := (hI.hCompLSF C hC).1
  have hBV := projCompUpdateG_valid hI hu hC
  by_cases hnil : projCompUpdateG cs.G (cs.compSt C).G u = []
  · dsimp only; simp [projCompUpdateWeight, hnil, tildeStepBatch, batchSplitCount]
  · have hw1 : projCompUpdateWeight cs.G (cs.compSt C).G u = 1 := by unfold projCompUpdateWeight; simp [hnil]
    by_cases hlen1 : (projCompUpdateG cs.G (cs.compSt C).G u).length = 1
    · have htd := tildeStepBatch_spec hI₀ hCov₀ hCI hD hT hBV
      have hex := extraSet_batch_diff_le hI₀ hCov₀ (projCompUpdateG cs.G (cs.compSt C).G u) hCI hD hBV hT
      dsimp only at htd hex ⊢; rw [hlen1] at htd hex; rw [hw1]
      exact ⟨htd.2.2.2.2.2.2.2.2.1, by simpa using htd.2.2.2.2.2.2.2.2.2.2.1, hex.1, hex.2⟩
    · cases u with
      | delete e => simp only [projCompUpdateG] at hnil hlen1; split_ifs at hnil hlen1 <;> simp at hnil hlen1
      | split v v' Lt Lh => simp only [projCompUpdateG] at hnil hlen1; split_ifs at hnil hlen1 <;> simp at hnil hlen1
      | insert e a b =>
        have he_not : e ∉ (cs.compSt C).G.E := fun heC => hu.1 (hI.hCE_sub C hC heC)
        dsimp only; rw [hw1]; simp only [projCompUpdateG] at hnil hlen1 ⊢
        split_ifs at hnil hlen1 ⊢ with hab ha hb
        · simp at hlen1
        · have hpair := tildeStepBatch_insert_delete_selfLoop hI₀ hCov₀ hCI hD hT ha he_not
          exact ⟨by omega, by simpa using hpair.2.1, by omega, by omega⟩
        · have hpair := tildeStepBatch_insert_delete_selfLoop hI₀ hCov₀ hCI hD hT hb he_not
          exact ⟨by omega, by simpa using hpair.2.1, by omega, by omega⟩
        · simp at hnil

lemma tildeStepBatch_projCompBatchG_spec {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {thresh₀ K₀ : ℝ}
    {S₀ : LSFState} (hI₀ : LSFInvWith thresh₀ K₀ ℓ₀ S₀)
    (hCov₀ : S₀.W_init.biUnion (inducedEdges S₀.RF.F) = S₀.RF.F.E) :
    ∀ (U : List Update) {cs : CompLSFState} {C : Finset ℕ} {ts : TildeState},
      CompLSFInv C_lsst ℓ₀ cs → C ∈ components cs.G₀ →
      LSFDerivedFrom S₀ (cs.compSt C) → TildeInv S₀ (cs.compSt C) ts → cs.G.BatchIsValid U →
      let Up := projCompBatchG cs.G (cs.compSt C).G U
      let w := projCompBatchWeight cs.G (cs.compSt C).G U
      let td := tildeStepBatch (cs.compSt C) ts Up
      batchSplitCount td.1 ≤ w * (S₀.G.maxDeg + 1) + (td.2.2.R \ (cs.compSt C).R).card ∧
      ((td.1.length : ℝ) ≤ (w : ℝ) *
        ((S₀.G.maxDeg : ℝ) + 1 + 56 * (Real.log ((S₀.G₀.n : ℝ) + 2)) ^ 2)) ∧
      (extraSet td.2.2 td.2.1 \ extraSet (cs.compSt C) ts).card ≤
        w + (td.2.2.R \ (cs.compSt C).R).card ∧
      (extraSet (cs.compSt C) ts \ extraSet td.2.2 td.2.1).card ≤ w := by
  intro U
  induction U with
  | nil => intro cs C ts _ _ _ _ _; simp [projCompBatchG, projCompBatchWeight, tildeStepBatch, batchSplitCount]
  | cons u rest ih =>
    intro cs C ts hI hC hD hT ⟨hu, hrest⟩
    have hCI := (hI.hCompLSF C hC).1
    have hBV1 := projCompUpdateG_valid hI hu hC
    have h1_td := tildeStepBatch_spec hI₀ hCov₀ hCI hD hT hBV1
    have h1_w := tildeStepBatch_projCompUpdateG_spec hI₀ hCov₀ hI hC hD hT hu
    have hcs1_I := compLSFInv_step hI hu
    have hB1 := applyLSFBatch_inv_with (projCompUpdateG cs.G (cs.compSt C).G u) hCI hBV1
    set r1 := tildeStepBatch (cs.compSt C) ts (projCompUpdateG cs.G (cs.compSt C).G u)
    have hr1_S : r1.2.2 = (compLSFStepSingle cs u).compSt C := h1_td.1
    have hC1_eq : ((compLSFStepSingle cs u).compSt C).G =
        (cs.compSt C).G.applyBatch (projCompUpdateG cs.G (cs.compSt C).G u) := hB1.2.1
    have h2_w := ih (cs := compLSFStepSingle cs u) (C := C) (ts := r1.2.1)
      hcs1_I hC (hr1_S ▸ h1_td.2.2.1) (hr1_S ▸ h1_td.2.2.2.1) hrest
    change _ at h2_w
    rw [show (compLSFStepSingle cs u).G = cs.G.applyUpdate u from rfl, hC1_eq] at h2_w
    set Up1 := projCompUpdateG cs.G (cs.compSt C).G u
    set Up2 := projCompBatchG (cs.G.applyUpdate u) ((cs.compSt C).G.applyBatch Up1) rest
    have happ := tildeStepBatch_append (cs.compSt C) ts Up1 Up2
    set r2 := tildeStepBatch r1.2.2 r1.2.1 Up2
    rw [← hr1_S] at h2_w
    have hR01 : (cs.compSt C).R ⊆ r1.2.2.R := h1_td.2.2.2.2.1
    have hBV2 : r1.2.2.G.BatchIsValid Up2 := by
      have h := (compLSFBatch_compSt hcs1_I hrest hC).2.2.1
      rw [show (compLSFStepSingle cs u).G = cs.G.applyUpdate u from rfl, hC1_eq] at h
      exact (hr1_S.symm ▸ hC1_eq).symm ▸ h
    have h2_td := tildeStepBatch_spec hI₀ hCov₀ h1_td.2.1 h1_td.2.2.1 h1_td.2.2.2.1 hBV2
    have hR12 : r1.2.2.R ⊆ r2.2.2.R := h2_td.2.2.2.2.1
    have hR_tel : (r1.2.2.R \ (cs.compSt C).R).card + (r2.2.2.R \ r1.2.2.R).card =
        (r2.2.2.R \ (cs.compSt C).R).card := by
      rw [Finset.card_sdiff_of_subset hR01, Finset.card_sdiff_of_subset hR12,
        Finset.card_sdiff_of_subset (hR01.trans hR12)]
      have c1 := Finset.card_le_card hR01; have c2 := Finset.card_le_card hR12; omega
    have hc_add : (extraSet r2.2.2 r2.2.1 \ extraSet (cs.compSt C) ts).card ≤
        (extraSet r2.2.2 r2.2.1 \ extraSet r1.2.2 r1.2.1).card +
          (extraSet r1.2.2 r1.2.1 \ extraSet (cs.compSt C) ts).card :=
      le_trans (Finset.card_le_card fun e he => by
        rw [Finset.mem_sdiff] at he; by_cases h1 : e ∈ extraSet r1.2.2 r1.2.1
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h1, he.2⟩)
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨he.1, h1⟩)) (Finset.card_union_le _ _)
    have hc_drop : (extraSet (cs.compSt C) ts \ extraSet r2.2.2 r2.2.1).card ≤
        (extraSet (cs.compSt C) ts \ extraSet r1.2.2 r1.2.1).card +
          (extraSet r1.2.2 r1.2.1 \ extraSet r2.2.2 r2.2.1).card :=
      le_trans (Finset.card_le_card fun e he => by
        rw [Finset.mem_sdiff] at he; by_cases h1 : e ∈ extraSet r1.2.2 r1.2.1
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h1, he.2⟩)
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨he.1, h1⟩)) (Finset.card_union_le _ _)
    dsimp only [projCompBatchG, projCompBatchWeight]
    rw [show projCompUpdateG cs.G (cs.compSt C).G u ++
        projCompBatchG (cs.G.applyUpdate u) ((cs.compSt C).G.applyBatch (projCompUpdateG cs.G (cs.compSt C).G u)) rest =
        Up1 ++ Up2 from rfl, happ]
    change batchSplitCount (r1.1 ++ r2.1) ≤
        (projCompUpdateWeight cs.G (cs.compSt C).G u +
          projCompBatchWeight (cs.G.applyUpdate u) ((cs.compSt C).G.applyBatch Up1) rest) *
          (S₀.G.maxDeg + 1) + (r2.2.2.R \ (cs.compSt C).R).card ∧
      ((r1.1 ++ r2.1).length : ℝ) ≤
        ((projCompUpdateWeight cs.G (cs.compSt C).G u +
          projCompBatchWeight (cs.G.applyUpdate u) ((cs.compSt C).G.applyBatch Up1) rest : ℕ) : ℝ) *
          ((S₀.G.maxDeg : ℝ) + 1 + 56 * Real.log ((S₀.G₀.n : ℝ) + 2) ^ 2) ∧
      (extraSet r2.2.2 r2.2.1 \ extraSet (cs.compSt C) ts).card ≤
        (projCompUpdateWeight cs.G (cs.compSt C).G u +
          projCompBatchWeight (cs.G.applyUpdate u) ((cs.compSt C).G.applyBatch Up1) rest) +
        (r2.2.2.R \ (cs.compSt C).R).card ∧
      (extraSet (cs.compSt C) ts \ extraSet r2.2.2 r2.2.1).card ≤
        projCompUpdateWeight cs.G (cs.compSt C).G u +
          projCompBatchWeight (cs.G.applyUpdate u) ((cs.compSt C).G.applyBatch Up1) rest
    have h1_sc : batchSplitCount r1.1 ≤ projCompUpdateWeight cs.G (cs.compSt C).G u * (S₀.G.maxDeg + 1) + (r1.2.2.R \ (cs.compSt C).R).card := h1_w.1
    have h2_sc : batchSplitCount r2.1 ≤ projCompBatchWeight (cs.G.applyUpdate u) ((cs.compSt C).G.applyBatch Up1) rest * (S₀.G.maxDeg + 1) + (r2.2.2.R \ r1.2.2.R).card := h2_w.1
    have h1_a : (extraSet r1.2.2 r1.2.1 \ extraSet (cs.compSt C) ts).card ≤ projCompUpdateWeight cs.G (cs.compSt C).G u + (r1.2.2.R \ (cs.compSt C).R).card := h1_w.2.2.1
    have h2_a : (extraSet r2.2.2 r2.2.1 \ extraSet r1.2.2 r1.2.1).card ≤ projCompBatchWeight (cs.G.applyUpdate u) ((cs.compSt C).G.applyBatch Up1) rest + (r2.2.2.R \ r1.2.2.R).card := h2_w.2.2.1
    have h1_d : (extraSet (cs.compSt C) ts \ extraSet r1.2.2 r1.2.1).card ≤ projCompUpdateWeight cs.G (cs.compSt C).G u := h1_w.2.2.2
    have h2_d : (extraSet r1.2.2 r1.2.1 \ extraSet r2.2.2 r2.2.1).card ≤ projCompBatchWeight (cs.G.applyUpdate u) ((cs.compSt C).G.applyBatch Up1) rest := h2_w.2.2.2
    exact ⟨by rw [batchSplitCount_append, Nat.add_mul]; omega, by rw [List.length_append, Nat.cast_add, Nat.cast_add, add_mul]; linarith [h1_w.2.1, h2_w.2.1], by omega, by omega⟩

lemma initCompLSF_wstr_eq
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) {C_lsst : ℝ}
    (hLSST : HasLSSTSpec oracle C_lsst)
    {G₀ : MGraph} (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    {ℓ₀ : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e)
    {k : ℕ} (hk : 1 ≤ k) (j : ℕ)
    {C : Finset ℕ} (hC : C ∈ components G₀)
    {e : ℕ} (he : e ∈ (compGraph G₀ C).E) :
    (initCompLSF oracle C_lsst G₀ ℓ₀ k j).wstrGlobal e =
      ((initCompLSF oracle C_lsst G₀ ℓ₀ k j).compSt C).wstr e := by
  have hI₀ := compLSFInv_init oracle hLSST hG₀ hV₀ hℓ₀ hk j
  have heG : e ∈ (initCompLSF oracle C_lsst G₀ ℓ₀ k j).G.E := Finset.filter_subset _ _ he
  have hni : e ∉ (initCompLSF oracle C_lsst G₀ ℓ₀ k j).insertedGlobal := Finset.notMem_empty _
  obtain ⟨C₁, hC₁, heC₁, hniC₁, hw⟩ := hI₀.hWstr_surv e heG hni
  have hCeq : C₁ = C := by
    by_contra hne
    have he1 : e ∈ compEdgeSet G₀ C₁ :=
      (hI₀.hCompLSF C₁ hC₁).2.1 ▸ (hI₀.hCompLSF C₁ hC₁).1.hsurv_edge e heC₁ hniC₁ |>.1
    exact Finset.disjoint_left.mp (compEdgeSet_pairwiseDisjoint G₀ hC₁ hC hne) he1 he
  exact hCeq ▸ hw

lemma initCompLSF_origBucket_congr
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) {C_lsst : ℝ}
    (hLSST : HasLSSTSpec oracle C_lsst)
    {G₀ : MGraph} (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    {ℓ₀ : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e)
    {k : ℕ} (hk : 1 ≤ k) (j : ℕ) {C : Finset ℕ} (hC : C ∈ components G₀) :
    let cs₀ := initCompLSF oracle C_lsst G₀ ℓ₀ k j
    ∀ e ∈ (initTildeState (cs₀.compSt C)).C.E,
      bucketOf (coreLen cs₀.lsf ℓ₀ e) = bucketOf (coreLen (cs₀.compSt C).lsf ℓ₀ e) := by
  intro cs₀ e he
  have heC : e ∈ (compGraph G₀ C).E := (Finset.mem_sdiff.mp he).1
  have hw := initCompLSF_wstr_eq oracle hLSST hG₀ hV₀ hℓ₀ hk j hC heC
  change bucketOf (cs₀.wstrGlobal e * ℓ₀ e) = bucketOf ((cs₀.compSt C).wstr e * ℓ₀ e)
  rw [hw]

lemma compLSFBatch_dynBatches_succ (D : DynamicInstance) (cs₀ : CompLSFState) (t : ℕ) :
    compLSFBatch cs₀ (dynBatches D (t + 1)).flatten =
      compLSFBatch (compLSFBatch cs₀ (dynBatches D t).flatten) (D.U (t + 1)) := by
  rw [dynBatches_succ, List.flatten_append, List.flatten_singleton, compLSFBatch_append]


end

end MinCostFlow.SparseCore
