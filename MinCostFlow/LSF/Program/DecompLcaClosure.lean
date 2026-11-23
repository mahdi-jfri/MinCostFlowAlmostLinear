module

public import MinCostFlow.LSF.Program.DecompBridge

/-!
# The LCA closure, bottom-up

A vertex `z` is in the LCA closure of a set `S` exactly when `z ∈ S` or two different children of
`z` have a vertex of `S` below them (`mem_lcaClosure_iff_children`). This is what a bottom-up
pass can test: it counts, at every vertex, the children whose subtree meets `S`.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program.DecompGen

theorem mem_lcaClosure_iff_children {T : MGraph} {r : ℕ} (hT : IsRootedTree T r) {S : Finset ℕ}
    (hS : S ⊆ T.V) {z : ℕ} (hz : z ∈ T.V) :
    z ∈ lcaClosure T r S ↔ z ∈ S ∨ ∃ c₁ ∈ childSet T r z, ∃ c₂ ∈ childSet T r z, c₁ ≠ c₂ ∧
      (∃ y ∈ S, y ∈ subtree T r c₁) ∧ (∃ y ∈ S, y ∈ subtree T r c₂) := by
  classical
  have hzs : z ∈ subtree T r z := mem_subtree_iff.mpr ⟨hz, isAncestor_refl T r z⟩
  -- the child of `z` above a vertex strictly below `z`
  have hchild : ∀ y ∈ subtree T r z, y ≠ z → ∃ c ∈ childSet T r z, y ∈ subtree T r c ∧
      ∀ c' ∈ childSet T r z, y ∈ subtree T r c' → c' = c := by
    intro y hy hyz
    obtain ⟨c, ⟨hc, hyc⟩, huniq⟩ := mem_subtree_children_iff hT hz hy hyz
    exact ⟨c, mem_childSet.mpr hc, hyc, fun c' hc' hyc' => huniq c' ⟨mem_childSet.mp hc', hyc'⟩⟩
  rw [mem_lcaClosure_iff]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    have huV := hS hu
    have hvV := hS hv
    by_cases hlu : lca T r u v = u
    · left; rw [hlu]; exact hu
    by_cases hlv : lca T r u v = v
    · left; rw [hlv]; exact hv
    right
    have hus : u ∈ subtree T r (lca T r u v) := mem_subtree_iff.mpr ⟨huV, lca_isAncestor_left hT huV hvV⟩
    have hvs : v ∈ subtree T r (lca T r u v) := mem_subtree_iff.mpr ⟨hvV, lca_isAncestor_right hT huV hvV⟩
    obtain ⟨c₁, hc₁, huc₁, -⟩ := hchild u hus (Ne.symm hlu)
    obtain ⟨c₂, hc₂, hvc₂, -⟩ := hchild v hvs (Ne.symm hlv)
    refine ⟨c₁, hc₁, c₂, hc₂, fun h => ?_, ⟨u, hu, huc₁⟩, ⟨v, hv, hvc₂⟩⟩
    subst h
    obtain ⟨hcV, -, -, hcz, hzV, hzc⟩ := childSet_facts hT hc₁
    have h1 : IsAncestor T r c₁ (lca T r u v) := (isAncestor_lca_iff hT huV hvV).mpr
      ⟨(mem_subtree_iff.mp huc₁).2, (mem_subtree_iff.mp hvc₂).2⟩
    exact hcz (isAncestor_antisymm hT hcV hzV h1 hzc)
  · rintro (hzS | ⟨c₁, hc₁, c₂, hc₂, hne, ⟨u, hu, huc₁⟩, ⟨v, hv, hvc₂⟩⟩)
    · exact ⟨z, hzS, z, hzS, lca_self hT hz⟩
    · have huV := hS hu
      have hvV := hS hv
      obtain ⟨-, -, -, -, -, hzc₁⟩ := childSet_facts hT hc₁
      obtain ⟨-, -, -, -, -, hzc₂⟩ := childSet_facts hT hc₂
      have hzu : IsAncestor T r z u := isAncestor_trans hT huV hzc₁ (mem_subtree_iff.mp huc₁).2
      have hzv : IsAncestor T r z v := isAncestor_trans hT hvV hzc₂ (mem_subtree_iff.mp hvc₂).2
      refine ⟨u, hu, v, hv, ?_⟩
      set l := lca T r u v with hl
      have hlV : l ∈ T.V := lca_mem hT huV hvV
      have hzl : IsAncestor T r z l := (isAncestor_lca_iff hT huV hvV).mpr ⟨hzu, hzv⟩
      by_contra hlz
      obtain ⟨c, hc, hlc, -⟩ := hchild l (mem_subtree_iff.mpr ⟨hlV, hzl⟩) hlz
      have hcl := (mem_subtree_iff.mp hlc).2
      have huc : u ∈ subtree T r c :=
        mem_subtree_iff.mpr ⟨huV, isAncestor_trans hT huV hcl (lca_isAncestor_left hT huV hvV)⟩
      have hvc : v ∈ subtree T r c :=
        mem_subtree_iff.mpr ⟨hvV, isAncestor_trans hT hvV hcl (lca_isAncestor_right hT huV hvV)⟩
      have hus : u ∈ subtree T r z := mem_subtree_iff.mpr ⟨huV, hzu⟩
      have huz : u ≠ z := by
        intro h
        obtain ⟨hc₁V, -, -, hc₁z, -, -⟩ := childSet_facts hT hc₁
        rw [h] at huc₁
        exact hc₁z (isAncestor_antisymm hT hc₁V hz (mem_subtree_iff.mp huc₁).2 hzc₁)
      have hvz : v ≠ z := by
        intro h
        obtain ⟨hc₂V, -, -, hc₂z, -, -⟩ := childSet_facts hT hc₂
        rw [h] at hvc₂
        exact hc₂z (isAncestor_antisymm hT hc₂V hz (mem_subtree_iff.mp hvc₂).2 hzc₂)
      obtain ⟨c', -, -, hu1⟩ := hchild u hus huz
      obtain ⟨c'', -, -, hv1⟩ := hchild v (mem_subtree_iff.mpr ⟨hvV, hzv⟩) hvz
      have e1 := hu1 c₁ hc₁ huc₁
      have e2 := hu1 c hc huc
      have e3 := hv1 c₂ hc₂ hvc₂
      have e4 := hv1 c hc hvc
      exact hne (by rw [e1, ← e2, e4, ← e3])

end MinCostFlow.LSF.Program

end
