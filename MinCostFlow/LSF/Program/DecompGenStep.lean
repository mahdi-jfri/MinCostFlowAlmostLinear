module

public import MinCostFlow.LSF.Program.DecompGenBase
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# The step of the tree decomposition, for any child order

`goodDecomp_step` is the inductive step of `treeDecompSub` (`LSF/TreeDecomp.lean`), with the
children of `u` batched in the order of a given duplicate-free list `L` instead of
`Finset.toList`. `GoodDecomp` names the properties that the decomposition of a subtree has; the
step builds them for `u` from those of the children: the batches of `greedyGroupAux` with `u`
added become pieces (`stepPieces`), and the rest with `u` is the open bag (`stepBag`). The proof
is the one of `treeDecompSub`.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program.DecompGen

open MinCostFlow MinCostFlow.LSF

/-- The properties of the decomposition `(𝒲, B)` of the subtree of `u`: the pieces `𝒲`, and the
open bag `B` that holds `u` and still has room. -/
def GoodDecomp (T : MGraph) (r : ℕ) (ν : ℕ → ℝ) (θ : ℝ) (u : ℕ) (𝒲 : Finset (Finset ℕ))
    (B : Finset ℕ) : Prop :=
  PathConvex T B ∧ u ∈ B ∧ B ⊆ subtree T r u ∧
    (∑ x ∈ B, ν x < 2 * θ) ∧
    (∀ P ∈ 𝒲, PathConvex T P ∧ P ⊆ subtree T r u ∧
      (inducedEdges T P).Nonempty ∧ (∑ x ∈ P, ν x < 4 * θ)) ∧
    (∀ P₁ ∈ 𝒲, ∀ P₂ ∈ 𝒲, P₁ ≠ P₂ → Disjoint (inducedEdges T P₁) (inducedEdges T P₂)) ∧
    (∀ P ∈ 𝒲, Disjoint (inducedEdges T P) (inducedEdges T B)) ∧
    (𝒲.biUnion (inducedEdges T) ∪ inducedEdges T B = inducedEdges T (subtree T r u)) ∧
    (θ * (𝒲.card : ℝ) ≤ ∑ x ∈ subtree T r u \ B, ν x)

/-- The children of `u` in the rooted tree `(T, r)`. -/
noncomputable def childSet (T : MGraph) (r u : ℕ) : Finset ℕ :=
  open Classical in (subtree T r u \ {u}).filter (fun c => parent T r c = u)

/-- The batches and the rest of the children list `L`. -/
noncomputable def stepGroups (ν : ℕ → ℝ) (θ : ℝ) (Bc : ℕ → Finset ℕ) (L : List ℕ) :
    List (List ℕ) × List ℕ :=
  greedyGroupAux θ (fun c => ∑ x ∈ Bc c, ν x) [] 0 L

/-- The pieces of `u`: those of the children, and one per batch, the batch bags with `u`. -/
noncomputable def stepPieces (ν : ℕ → ℝ) (θ : ℝ) (u : ℕ) (Wc : ℕ → Finset (Finset ℕ))
    (Bc : ℕ → Finset ℕ) (L : List ℕ) : Finset (Finset ℕ) :=
  open Classical in
  L.toFinset.biUnion Wc ∪
    (stepGroups ν θ Bc L).1.toFinset.image (fun b => insert u (b.toFinset.biUnion Bc))

/-- The open bag of `u`: `u` and the bags of the children that are in no batch. -/
noncomputable def stepBag (ν : ℕ → ℝ) (θ : ℝ) (u : ℕ) (Bc : ℕ → Finset ℕ) (L : List ℕ) :
    Finset ℕ :=
  open Classical in insert u ((stepGroups ν θ Bc L).2.toFinset.biUnion Bc)

lemma goodDecomp_step {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    (ν : ℕ → ℝ) (hν : ∀ v ∈ T.V, 0 ≤ ν v) (θ : ℝ) (hθ : 0 < θ) (hν_le : ∀ v ∈ T.V, ν v ≤ θ)
    {u : ℕ} (hu : u ∈ T.V) (L : List ℕ) (hL : L.Nodup) (hLC : ∀ c, c ∈ L ↔ c ∈ childSet T r u)
    (Wc : ℕ → Finset (Finset ℕ)) (Bc : ℕ → Finset ℕ)
    (hchild : ∀ c ∈ L, GoodDecomp T r ν θ c (Wc c) (Bc c)) :
    GoodDecomp T r ν θ u (stepPieces ν θ u Wc Bc L) (stepBag ν θ u Bc L) := by
  classical
  let C := (subtree T r u \ {u}).filter (fun c => parent T r c = u)
  have hLC : ∀ c, c ∈ L ↔ c ∈ C := by
    intro c; rw [hLC c, childSet]
  have hC_sub : ∀ c ∈ C, c ∈ (subtree T r u \ {u}).filter (fun c => parent T r c = u) :=
    fun _ hc => hc
  have hBc_spec : ∀ c (hc : c ∈ C),
      PathConvex T (Bc c) ∧ c ∈ Bc c ∧ Bc c ⊆ subtree T r c ∧
      (∑ x ∈ Bc c, ν x < 2 * θ) ∧
      (∀ P ∈ Wc c, PathConvex T P ∧ P ⊆ subtree T r c ∧
        (inducedEdges T P).Nonempty ∧ (∑ x ∈ P, ν x < 4 * θ)) ∧
      (∀ P₁ ∈ Wc c, ∀ P₂ ∈ Wc c, P₁ ≠ P₂ → Disjoint (inducedEdges T P₁) (inducedEdges T P₂)) ∧
      (∀ P ∈ Wc c, Disjoint (inducedEdges T P) (inducedEdges T (Bc c))) ∧
      ((Wc c).biUnion (inducedEdges T) ∪ inducedEdges T (Bc c) = inducedEdges T (subtree T r c)) ∧
      (θ * ((Wc c).card : ℝ) ≤ ∑ x ∈ subtree T r c \ Bc c, ν x) :=
    fun c hc => hchild c ((hLC c).mpr hc)
  have hLfin : L.toFinset = C := by ext c; rw [List.mem_toFinset, hLC]
  let f : ℕ → ℝ := fun c => ∑ x ∈ Bc c, ν x
  have hf_range : ∀ c ∈ L, 0 ≤ f c ∧ f c < 2 * θ := by
    intro c hc
    have hcC := (hLC _).mp hc
    have hspec := hBc_spec c hcC
    refine ⟨Finset.sum_nonneg (fun x hx => hν x (mem_subtree_iff.mp (hspec.2.2.1 hx)).1),
      hspec.2.2.2.1⟩
  let res := greedyGroupAux θ f [] 0 L
  have hres := greedyGroupAux_spec θ f hθ L [] 0 le_rfl hθ rfl (by simp) hf_range
  rcases hres with ⟨hperm, hbatches, hrem_sum, _⟩
  dsimp only [List.nil_append] at hperm hbatches hrem_sum
  have hall_nodup : (res.1.flatten ++ res.2).Nodup := hperm.nodup_iff.mp hL
  have hflat_nodup : res.1.flatten.Nodup := (List.nodup_append.mp hall_nodup).1
  have hrem_nodup : res.2.Nodup := (List.nodup_append.mp hall_nodup).2.1
  have hflat_disj_rem : Disjoint res.1.flatten.toFinset res.2.toFinset := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (List.nodup_append.mp hall_nodup).2.2 x (List.mem_toFinset.mp hx1)
      x (List.mem_toFinset.mp hx2) rfl
  have hbatch_sub_C : ∀ b ∈ res.1, b.toFinset ⊆ C := by
    intro b hb c hc
    exact (hLC _).mp (hperm.symm.subset (List.mem_append_left _
      (List.mem_flatten.mpr ⟨b, hb, List.mem_toFinset.mp hc⟩)))
  have hrem_sub_C : res.2.toFinset ⊆ C := by
    intro c hc
    exact (hLC _).mp (hperm.symm.subset (List.mem_append_right _ (List.mem_toFinset.mp hc)))
  have hdisj_children : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ →
      Disjoint (subtree T r c₁) (subtree T r c₂) := by
    intro c₁ hc₁ c₂ hc₂ hne
    have hf₁ := hc₁; have hf₂ := hc₂
    have hcr₁ := child_ne_root hT hu hf₁; have hcr₂ := child_ne_root hT hu hf₂
    rw [Finset.mem_filter, Finset.mem_sdiff] at hf₁ hf₂
    exact children_subtree_disjoint hT (mem_subtree_iff.mp hf₁.1.1).1
      (mem_subtree_iff.mp hf₂.1.1).1 hcr₁ hcr₂ hf₁.2 hf₂.2 hne
  have hu_not_Bc : ∀ {c : ℕ}, c ∈ C → u ∉ Bc c := by
    intro c hc huB
    exact (Finset.mem_sdiff.mp (subtree_child_subset hT hc ((hBc_spec c hc).2.2.1 huB))).2
      (Finset.mem_singleton_self u)
  have hBc_disj : ∀ {c₁ c₂ : ℕ}, c₁ ∈ C → c₂ ∈ C → c₁ ≠ c₂ → Disjoint (Bc c₁) (Bc c₂) :=
    fun hc₁ hc₂ hne => Finset.disjoint_of_subset_left (hBc_spec _ hc₁).2.2.1
      (Finset.disjoint_of_subset_right (hBc_spec _ hc₂).2.2.1 (hdisj_children _ hc₁ _ hc₂ hne))
  have h_insert_disj : ∀ (S₁ S₂ : Finset ℕ), S₁ ⊆ C → S₂ ⊆ C → Disjoint S₁ S₂ →
      Disjoint (inducedEdges T (insert u (S₁.biUnion Bc)))
        (inducedEdges T (insert u (S₂.biUnion Bc))) := by
    intro S₁ S₂ hS₁ hS₂ hSdisj
    have hE₁ := inducedEdges_insert_biUnion hT hu S₁ Bc (fun c hc => hC_sub c (hS₁ hc))
      (fun c hc => ⟨(hBc_spec c (hS₁ hc)).2.1, (hBc_spec c (hS₁ hc)).2.2.1⟩)
    have hE₂ := inducedEdges_insert_biUnion hT hu S₂ Bc (fun c hc => hC_sub c (hS₂ hc))
      (fun c hc => ⟨(hBc_spec c (hS₂ hc)).2.1, (hBc_spec c (hS₂ hc)).2.2.1⟩)
    rw [hE₁, hE₂, Finset.disjoint_left]
    intro e he₁ he₂
    have h_pe_not_in_biUnion : ∀ (S : Finset ℕ), S ⊆ C → ∀ c ∈ C,
        parentEdge T r c ∉ S.biUnion (fun c' => inducedEdges T (Bc c')) := by
      intro S hS c hc hmem
      rw [Finset.mem_biUnion] at hmem
      obtain ⟨c', hc'S, hfe⟩ := hmem
      have hcV := (mem_subtree_iff.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hc).1).1).1
      have hcr := child_ne_root hT hu hc
      have hpar : parent T r c = u := (Finset.mem_filter.mp hc).2
      have hend := parentEdge_endpoints hT hcV hcr
      have h_u_mem : u ∈ ({T.tail (parentEdge T r c), T.head (parentEdge T r c)} : Set ℕ) := by
        rw [hend, hpar]; exact Set.mem_insert_of_mem _ (Set.mem_singleton u)
      rw [inducedEdges, Finset.mem_filter] at hfe
      have huB : u ∈ Bc c' := by
        rcases h_u_mem with h1 | h1
        · exact h1 ▸ hfe.2.1
        · exact (Set.mem_singleton_iff.mp h1) ▸ hfe.2.2
      exact hu_not_Bc (hS hc'S) huB
    rw [Finset.mem_union, Finset.mem_image] at he₁ he₂
    rcases he₁ with ⟨c₁, hc₁, rfl⟩ | he₁_sub <;> rcases he₂ with ⟨c₂, hc₂, hpe⟩ | he₂_sub
    · have hc₁V := (mem_subtree_iff.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hS₁ hc₁)).1).1).1
      have hc₂V := (mem_subtree_iff.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hS₂ hc₂)).1).1).1
      have heq := parentEdge_inj hT hc₁V hc₂V (child_ne_root hT hu (hS₁ hc₁))
        (child_ne_root hT hu (hS₂ hc₂)) hpe.symm
      exact Finset.disjoint_left.mp hSdisj hc₁ (heq ▸ hc₂)
    · exact h_pe_not_in_biUnion S₂ hS₂ c₁ (hS₁ hc₁) he₂_sub
    · rw [← hpe] at he₁_sub
      exact h_pe_not_in_biUnion S₁ hS₁ c₂ (hS₂ hc₂) he₁_sub
    · rw [Finset.mem_biUnion] at he₁_sub he₂_sub
      obtain ⟨c₁, hc₁, hf₁⟩ := he₁_sub
      obtain ⟨c₂, hc₂, hf₂⟩ := he₂_sub
      have hne : c₁ ≠ c₂ := fun hEq => Finset.disjoint_left.mp hSdisj hc₁ (hEq ▸ hc₂)
      rw [inducedEdges, Finset.mem_filter] at hf₁ hf₂
      exact Finset.disjoint_left.mp (hBc_disj (hS₁ hc₁) (hS₂ hc₂) hne) hf₁.2.1 hf₂.2.1
  have h_child_disj : ∀ (S : Finset ℕ), S ⊆ C → ∀ c₀ ∈ C, ∀ Q ∈ Wc c₀,
      Disjoint (inducedEdges T Q) (inducedEdges T (insert u (S.biUnion Bc))) := by
    intro S hS c₀ hc₀ Q hQ
    have hQ_spec := (hBc_spec c₀ hc₀).2.2.2.2.1 Q hQ
    have hE := inducedEdges_insert_biUnion hT hu S Bc (fun c hc => hC_sub c (hS hc))
      (fun c hc => ⟨(hBc_spec c (hS hc)).2.1, (hBc_spec c (hS hc)).2.2.1⟩)
    rw [hE, Finset.disjoint_left]
    intro e heQ heI
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion] at heI
    rcases heI with ⟨c, hc, rfl⟩ | ⟨c, hc, heBc⟩
    · have hcV := (mem_subtree_iff.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hS hc)).1).1).1
      have hend := parentEdge_endpoints hT hcV (child_ne_root hT hu (hS hc))
      have h_u_mem : u ∈ ({T.tail (parentEdge T r c), T.head (parentEdge T r c)} : Set ℕ) := by
        rw [hend, (Finset.mem_filter.mp (hS hc)).2]; exact Set.mem_insert_of_mem _ (Set.mem_singleton u)
      rw [inducedEdges, Finset.mem_filter] at heQ
      have huQ : u ∈ Q := by
        rcases h_u_mem with h1 | h1
        · exact h1 ▸ heQ.2.1
        · exact (Set.mem_singleton_iff.mp h1) ▸ heQ.2.2
      exact (Finset.mem_sdiff.mp (subtree_child_subset hT hc₀ (hQ_spec.2.1 huQ))).2
        (Finset.mem_singleton_self u)
    · by_cases heq : c = c₀
      · subst heq
        exact Finset.disjoint_left.mp ((hBc_spec c hc₀).2.2.2.2.2.2.1 Q hQ) heQ heBc
      · rw [inducedEdges, Finset.mem_filter] at heQ heBc
        exact Finset.disjoint_left.mp (hdisj_children c₀ hc₀ c (hS hc) (Ne.symm heq))
          (hQ_spec.2.1 heQ.2.1) ((hBc_spec c (hS hc)).2.2.1 heBc.2.1)
  let batchPiece : List ℕ → Finset ℕ := fun b => insert u (b.toFinset.biUnion Bc)
  let batchesPieces := res.1.toFinset.image batchPiece
  let childPieces := C.biUnion Wc
  let 𝒲_u := childPieces ∪ batchesPieces
  let B_u := insert u (res.2.toFinset.biUnion Bc)
  have hBu_sub : B_u ⊆ subtree T r u := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_biUnion] at hx
    rcases hx with hEq | ⟨c, hc, hxc⟩
    · rw [hEq]
      exact mem_subtree_iff.mpr ⟨hu, isAncestor_refl T r u⟩
    · exact Finset.sdiff_subset (subtree_child_subset hT (hrem_sub_C hc) ((hBc_spec c (hrem_sub_C hc)).2.2.1 hxc))
  have hPeq : stepPieces ν θ u Wc Bc L = 𝒲_u := by
    unfold stepPieces stepGroups; rw [hLfin]
  have hBeq : stepBag ν θ u Bc L = B_u := rfl
  rw [hPeq, hBeq]
  refine ⟨?_, Finset.mem_insert_self _ _, hBu_sub, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact pathConvex_insert_biUnion hT hu res.2.toFinset Bc (fun c hc => hC_sub c (hrem_sub_C hc))
      (fun c hc => ⟨(hBc_spec c (hrem_sub_C hc)).2.1, (hBc_spec c (hrem_sub_C hc)).2.2.1⟩)
      (fun c hc => (hBc_spec c (hrem_sub_C hc)).1)
  · have hu_not_rem : u ∉ res.2.toFinset.biUnion Bc := by
      rw [Finset.mem_biUnion]; rintro ⟨c, hc, huB⟩
      exact hu_not_Bc (hrem_sub_C hc) huB
    have hdisj_rem : Set.PairwiseDisjoint (↑res.2.toFinset : Set ℕ) Bc := by
      intro c₁ hc₁ c₂ hc₂ hne
      exact hBc_disj (hrem_sub_C hc₁) (hrem_sub_C hc₂) hne
    rw [Finset.sum_insert hu_not_rem, Finset.sum_biUnion hdisj_rem]
    have hsum_rem : (∑ c ∈ res.2.toFinset, ∑ x ∈ Bc c, ν x) = (res.2.map f).sum :=
      List.sum_toFinset f hrem_nodup
    rw [hsum_rem]
    have := hν_le u hu
    linarith
  · intro P hP
    rw [Finset.mem_union, Finset.mem_biUnion, Finset.mem_image] at hP
    rcases hP with ⟨c, hc, hPQ⟩ | ⟨b, hb, rfl⟩
    · have hPs := (hBc_spec c hc).2.2.2.2.1 P hPQ
      exact ⟨hPs.1, Finset.Subset.trans hPs.2.1 (Finset.Subset.trans (subtree_child_subset hT hc) Finset.sdiff_subset),
        hPs.2.2.1, hPs.2.2.2⟩
    · have hbL := List.mem_toFinset.mp hb
      have hbS := hbatch_sub_C b hbL
      have hhb := hbatches b hbL
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact pathConvex_insert_biUnion hT hu b.toFinset Bc (fun c hc => hC_sub c (hbS hc))
          (fun c hc => ⟨(hBc_spec c (hbS hc)).2.1, (hBc_spec c (hbS hc)).2.2.1⟩)
          (fun c hc => (hBc_spec c (hbS hc)).1)
      · intro x hx
        rw [Finset.mem_insert, Finset.mem_biUnion] at hx
        rcases hx with hEq | ⟨c, hc, hxc⟩
        · rw [hEq]
          exact mem_subtree_iff.mpr ⟨hu, isAncestor_refl T r u⟩
        · exact Finset.sdiff_subset (subtree_child_subset hT (hbS hc) ((hBc_spec c (hbS hc)).2.2.1 hxc))
      · obtain ⟨c, hc_mem⟩ := List.exists_mem_of_ne_nil b hhb.1
        have hE := inducedEdges_insert_biUnion hT hu b.toFinset Bc (fun c hc => hC_sub c (hbS hc))
          (fun c hc => ⟨(hBc_spec c (hbS hc)).2.1, (hBc_spec c (hbS hc)).2.2.1⟩)
        rw [hE]
        exact ⟨parentEdge T r c, Finset.mem_union_left _
          (Finset.mem_image_of_mem _ (List.mem_toFinset.mpr hc_mem))⟩
      · have hu_not_b : u ∉ b.toFinset.biUnion Bc := by
          rw [Finset.mem_biUnion]; rintro ⟨c, hc, huB⟩
          exact hu_not_Bc (hbS hc) huB
        have hdisj_b : Set.PairwiseDisjoint (↑b.toFinset : Set ℕ) Bc :=
          fun c₁ hc₁ c₂ hc₂ hne => hBc_disj (hbS hc₁) (hbS hc₂) hne
        rw [Finset.sum_insert hu_not_b, Finset.sum_biUnion hdisj_b]
        have hsum_b : (∑ c ∈ b.toFinset, ∑ x ∈ Bc c, ν x) = (b.map f).sum :=
          List.sum_toFinset f (list_flatten_nodup_mem hflat_nodup hbL)
        rw [hsum_b]
        have := hν_le u hu
        linarith [hhb.2.2.1]
  · intro P₁ hP₁ P₂ hP₂ hne
    rw [Finset.mem_union, Finset.mem_biUnion, Finset.mem_image] at hP₁ hP₂
    rcases hP₁ with ⟨c₁, hc₁, h1⟩ | ⟨b₁, hb₁, rfl⟩ <;>
      rcases hP₂ with ⟨c₂, hc₂, h2⟩ | ⟨b₂, hb₂, rfl⟩
    · by_cases hEq : c₁ = c₂
      · subst hEq; exact (hBc_spec c₁ hc₁).2.2.2.2.2.1 P₁ h1 P₂ h2 hne
      · have hs₁ := (hBc_spec c₁ hc₁).2.2.2.2.1 P₁ h1
        have hs₂ := (hBc_spec c₂ hc₂).2.2.2.2.1 P₂ h2
        rw [Finset.disjoint_left]
        intro e he₁ he₂
        rw [inducedEdges, Finset.mem_filter] at he₁ he₂
        exact Finset.disjoint_left.mp (hdisj_children c₁ hc₁ c₂ hc₂ hEq)
          (hs₁.2.1 he₁.2.1) (hs₂.2.1 he₂.2.1)
    · exact h_child_disj b₂.toFinset (hbatch_sub_C b₂ (List.mem_toFinset.mp hb₂)) c₁ hc₁ P₁ h1
    · exact (h_child_disj b₁.toFinset (hbatch_sub_C b₁ (List.mem_toFinset.mp hb₁)) c₂ hc₂ P₂ h2).symm
    · have hne_b : b₁ ≠ b₂ := fun hEq => hne (by rw [hEq])
      have hb₁L := List.mem_toFinset.mp hb₁
      have hb₂L := List.mem_toFinset.mp hb₂
      exact h_insert_disj b₁.toFinset b₂.toFinset (hbatch_sub_C b₁ hb₁L) (hbatch_sub_C b₂ hb₂L)
        (list_flatten_nodup_pairwise_disjoint res.1 hflat_nodup b₁ hb₁L b₂ hb₂L hne_b)
  · intro P hP
    rw [Finset.mem_union, Finset.mem_biUnion, Finset.mem_image] at hP
    rcases hP with ⟨c, hc, hQ⟩ | ⟨b, hb, rfl⟩
    · exact h_child_disj res.2.toFinset hrem_sub_C c hc P hQ
    · have hbL := List.mem_toFinset.mp hb
      have hdisj_br : Disjoint b.toFinset res.2.toFinset := by
        rw [Finset.disjoint_left]
        intro c hc1 hc2
        exact Finset.disjoint_left.mp hflat_disj_rem
          (List.mem_toFinset.mpr (List.mem_flatten.mpr ⟨b, hbL, List.mem_toFinset.mp hc1⟩)) hc2
      exact h_insert_disj b.toFinset res.2.toFinset (hbatch_sub_C b hbL) hrem_sub_C hdisj_br
  · apply Finset.Subset.antisymm
    · rw [Finset.union_subset_iff]
      constructor
      · rw [Finset.biUnion_subset_iff_forall_subset]
        intro P hP
        have hsub : P ⊆ subtree T r u := by
          rw [Finset.mem_union, Finset.mem_biUnion, Finset.mem_image] at hP
          rcases hP with ⟨c, hc, hQ⟩ | ⟨b, hb, rfl⟩
          · exact Finset.Subset.trans ((hBc_spec c hc).2.2.2.2.1 P hQ).2.1
              (Finset.Subset.trans (subtree_child_subset hT hc) Finset.sdiff_subset)
          · intro x hx
            rw [Finset.mem_insert, Finset.mem_biUnion] at hx
            rcases hx with hEq | ⟨c, hc, hxc⟩
            · rw [hEq]
              exact mem_subtree_iff.mpr ⟨hu, isAncestor_refl T r u⟩
            · exact Finset.sdiff_subset (subtree_child_subset hT
                (hbatch_sub_C b (List.mem_toFinset.mp hb) hc)
                ((hBc_spec c (hbatch_sub_C b (List.mem_toFinset.mp hb) hc)).2.2.1 hxc))
        intro e he
        rw [inducedEdges, Finset.mem_filter] at he ⊢
        exact ⟨he.1, hsub he.2.1, hsub he.2.2⟩
      · intro e he
        rw [inducedEdges, Finset.mem_filter] at he ⊢
        exact ⟨he.1, hBu_sub he.2.1, hBu_sub he.2.2⟩
    · intro e he
      rw [subtree_eq_insert_biUnion hT hu, inducedEdges_insert_biUnion hT hu C (subtree T r)
        hC_sub (fun c hc => ⟨mem_subtree_iff.mpr ⟨(mem_subtree_iff.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hc).1).1).1, isAncestor_refl T r c⟩, Finset.Subset.refl _⟩),
        Finset.mem_union, Finset.mem_image, Finset.mem_biUnion] at he
      have hc_part : ∀ c ∈ C, (∃ b ∈ res.1, c ∈ b.toFinset) ∨ c ∈ res.2.toFinset := by
        intro c hc
        have hmem := hperm.subset ((hLC _).mpr hc)
        rw [List.mem_append] at hmem
        rcases hmem with hf | hr
        · obtain ⟨b, hb, hcb⟩ := List.mem_flatten.mp hf
          exact Or.inl ⟨b, hb, List.mem_toFinset.mpr hcb⟩
        · exact Or.inr (List.mem_toFinset.mpr hr)
      rcases he with ⟨c, hc, rfl⟩ | ⟨c, hc, hec⟩
      · rcases hc_part c hc with ⟨b, hb, hcb⟩ | hcr
        · refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨batchPiece b,
            Finset.mem_union_right _ (Finset.mem_image_of_mem _ (List.mem_toFinset.mpr hb)), ?_⟩)
          rw [inducedEdges_insert_biUnion hT hu b.toFinset Bc (fun c' hc' => hC_sub c' (hbatch_sub_C b hb hc'))
            (fun c' hc' => ⟨(hBc_spec c' (hbatch_sub_C b hb hc')).2.1, (hBc_spec c' (hbatch_sub_C b hb hc')).2.2.1⟩)]
          exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hcb)
        · refine Finset.mem_union_right _ ?_
          rw [inducedEdges_insert_biUnion hT hu res.2.toFinset Bc (fun c' hc' => hC_sub c' (hrem_sub_C hc'))
            (fun c' hc' => ⟨(hBc_spec c' (hrem_sub_C hc')).2.1, (hBc_spec c' (hrem_sub_C hc')).2.2.1⟩)]
          exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hcr)
      · rw [← (hBc_spec c hc).2.2.2.2.2.2.2.1, Finset.mem_union, Finset.mem_biUnion] at hec
        rcases hec with ⟨Q, hQ, heQ⟩ | heB
        · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨Q,
            Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨c, hc, hQ⟩), heQ⟩)
        · rcases hc_part c hc with ⟨b, hb, hcb⟩ | hcr
          · refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨batchPiece b,
              Finset.mem_union_right _ (Finset.mem_image_of_mem _ (List.mem_toFinset.mpr hb)), ?_⟩)
            rw [inducedEdges_insert_biUnion hT hu b.toFinset Bc (fun c' hc' => hC_sub c' (hbatch_sub_C b hb hc'))
              (fun c' hc' => ⟨(hBc_spec c' (hbatch_sub_C b hb hc')).2.1, (hBc_spec c' (hbatch_sub_C b hb hc')).2.2.1⟩)]
            exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨c, hcb, heB⟩)
          · refine Finset.mem_union_right _ ?_
            rw [inducedEdges_insert_biUnion hT hu res.2.toFinset Bc (fun c' hc' => hC_sub c' (hrem_sub_C hc'))
              (fun c' hc' => ⟨(hBc_spec c' (hrem_sub_C hc')).2.1, (hBc_spec c' (hrem_sub_C hc')).2.2.1⟩)]
            exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨c, hcr, heB⟩)
  · have hcard_W : (𝒲_u.card : ℝ) ≤ (∑ c ∈ C, ((Wc c).card : ℝ)) + (res.1.length : ℝ) := by
      have h1 : 𝒲_u.card ≤ childPieces.card + batchesPieces.card := Finset.card_union_le _ _
      have h2 : childPieces.card ≤ ∑ c ∈ C, (Wc c).card := Finset.card_biUnion_le
      have h3 : batchesPieces.card ≤ res.1.toFinset.card := Finset.card_image_le
      have h4 : res.1.toFinset.card ≤ res.1.length := List.toFinset_card_le res.1
      have hnat : 𝒲_u.card ≤ (∑ c ∈ C, (Wc c).card) + res.1.length := by omega
      exact_mod_cast (by simpa only [Nat.cast_add, Nat.cast_sum] using hnat)
    have h_batches_theta : θ * (res.1.length : ℝ) ≤ ∑ c ∈ res.1.flatten.toFinset, f c := by
      have h1 := list_len_mul_le_sum θ f res.1 (fun b hb => (hbatches b hb).2.1)
      rwa [list_sum_map_eq_sum_flatten f res.1 hflat_nodup] at h1
    have h_children_theta : ∑ c ∈ C, θ * ((Wc c).card : ℝ) ≤ ∑ c ∈ C, ∑ x ∈ subtree T r c \ Bc c, ν x :=
      Finset.sum_le_sum (fun c hc => (hBc_spec c hc).2.2.2.2.2.2.2.2)
    have h_flat_sub_C : res.1.flatten.toFinset ⊆ C := by
      intro c hc
      exact (hLC _).mp (hperm.symm.subset (List.mem_append_left _ (List.mem_toFinset.mp hc)))
    have hC_eq_union : C = res.1.flatten.toFinset ∪ res.2.toFinset := by
      apply Finset.ext
      intro c
      rw [Finset.mem_union, List.mem_toFinset, List.mem_toFinset, ← hLC]
      exact ⟨fun hc => List.mem_append.mp (hperm.subset hc),
        fun hc => hperm.symm.subset (List.mem_append.mpr hc)⟩
    have h_lhs_le : θ * (𝒲_u.card : ℝ) ≤
        (∑ c ∈ res.1.flatten.toFinset, ∑ x ∈ subtree T r c, ν x) +
          (∑ c ∈ res.2.toFinset, ∑ x ∈ subtree T r c \ Bc c, ν x) := by
      have hmul : θ * (𝒲_u.card : ℝ) ≤
          (∑ c ∈ C, θ * ((Wc c).card : ℝ)) + θ * (res.1.length : ℝ) := by
        have := mul_le_mul_of_nonneg_left hcard_W (le_of_lt hθ)
        rwa [mul_add, Finset.mul_sum] at this
      have hC_sum : ∑ c ∈ C, ∑ x ∈ subtree T r c \ Bc c, ν x =
          (∑ c ∈ res.1.flatten.toFinset, ∑ x ∈ subtree T r c \ Bc c, ν x) +
            (∑ c ∈ res.2.toFinset, ∑ x ∈ subtree T r c \ Bc c, ν x) := by
        rw [hC_eq_union, Finset.sum_union hflat_disj_rem]
      have h_combine : ∑ c ∈ res.1.flatten.toFinset, ((∑ x ∈ subtree T r c \ Bc c, ν x) + ∑ x ∈ Bc c, ν x) =
          ∑ c ∈ res.1.flatten.toFinset, ∑ x ∈ subtree T r c, ν x :=
        Finset.sum_congr rfl (fun c hc =>
          Finset.sum_sdiff (hBc_spec c (h_flat_sub_C hc)).2.2.1)
      rw [← h_combine, Finset.sum_add_distrib]
      dsimp only [f] at h_batches_theta
      linarith
    have h_sub_diff : subtree T r u \ B_u =
        (res.1.flatten.toFinset.biUnion (subtree T r)) ∪
          (res.2.toFinset.biUnion (fun c => subtree T r c \ Bc c)) := by
      apply Finset.ext
      intro x
      rw [Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion, Finset.mem_biUnion]
      constructor
      · rintro ⟨hx, hxBu⟩
        have hxu : x ≠ u := fun hEq => hxBu (hEq ▸ Finset.mem_insert_self _ _)
        obtain ⟨c, ⟨hcC, hxc⟩, _⟩ := mem_subtree_children_iff hT hu hx hxu
        have hmem : c ∈ res.1.flatten.toFinset ∪ res.2.toFinset := by
          rw [← hC_eq_union]; exact hcC
        rw [Finset.mem_union] at hmem
        rcases hmem with hf | hr
        · exact Or.inl ⟨c, hf, hxc⟩
        · refine Or.inr ⟨c, hr, Finset.mem_sdiff.mpr ⟨hxc, fun hxB => hxBu ?_⟩⟩
          exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨c, hr, hxB⟩)
      · rintro (⟨c, hc, hxc⟩ | ⟨c, hc, hxc⟩)
        · have hcC := h_flat_sub_C hc
          refine ⟨Finset.sdiff_subset (subtree_child_subset hT hcC hxc), fun hxBu => ?_⟩
          rw [Finset.mem_insert, Finset.mem_biUnion] at hxBu
          rcases hxBu with rfl | ⟨c', hc', hxB'⟩
          · exact (Finset.mem_sdiff.mp (subtree_child_subset hT hcC hxc)).2 (Finset.mem_singleton_self _)
          · have hne : c ≠ c' := fun hEq => Finset.disjoint_left.mp hflat_disj_rem hc (hEq ▸ hc')
            exact Finset.disjoint_left.mp (hdisj_children c hcC c' (hrem_sub_C hc') hne)
              hxc ((hBc_spec c' (hrem_sub_C hc')).2.2.1 hxB')
        · rw [Finset.mem_sdiff] at hxc
          have hcC := hrem_sub_C hc
          refine ⟨Finset.sdiff_subset (subtree_child_subset hT hcC hxc.1), fun hxBu => ?_⟩
          rw [Finset.mem_insert, Finset.mem_biUnion] at hxBu
          rcases hxBu with rfl | ⟨c', hc', hxB'⟩
          · exact (Finset.mem_sdiff.mp (subtree_child_subset hT hcC hxc.1)).2 (Finset.mem_singleton_self _)
          · by_cases hEq : c = c'
            · exact hxc.2 (hEq ▸ hxB')
            · exact Finset.disjoint_left.mp (hdisj_children c hcC c' (hrem_sub_C hc') hEq)
                hxc.1 ((hBc_spec c' (hrem_sub_C hc')).2.2.1 hxB')
    have hdisj_part1 : Set.PairwiseDisjoint (↑res.1.flatten.toFinset : Set ℕ) (subtree T r) :=
      fun c₁ hc₁ c₂ hc₂ hne => hdisj_children c₁ (h_flat_sub_C hc₁) c₂ (h_flat_sub_C hc₂) hne
    have hdisj_part2 : Set.PairwiseDisjoint (↑res.2.toFinset : Set ℕ) (fun c => subtree T r c \ Bc c) :=
      fun c₁ hc₁ c₂ hc₂ hne =>
        Finset.disjoint_of_subset_left Finset.sdiff_subset
          (Finset.disjoint_of_subset_right Finset.sdiff_subset
            (hdisj_children c₁ (hrem_sub_C hc₁) c₂ (hrem_sub_C hc₂) hne))
    have hdisj_bi : Disjoint (res.1.flatten.toFinset.biUnion (subtree T r))
        (res.2.toFinset.biUnion (fun c => subtree T r c \ Bc c)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [Finset.mem_biUnion] at hx1 hx2
      obtain ⟨c₁, hc₁, hx1⟩ := hx1
      obtain ⟨c₂, hc₂, hx2⟩ := hx2
      have hne : c₁ ≠ c₂ := fun hEq => Finset.disjoint_left.mp hflat_disj_rem hc₁ (hEq ▸ hc₂)
      exact Finset.disjoint_left.mp (hdisj_children c₁ (h_flat_sub_C hc₁) c₂ (hrem_sub_C hc₂) hne)
        hx1 (Finset.sdiff_subset hx2)
    rw [h_sub_diff, Finset.sum_union hdisj_bi, Finset.sum_biUnion hdisj_part1, Finset.sum_biUnion hdisj_part2]
    exact h_lhs_le


end MinCostFlow.LSF.Program.DecompGen
