module

public import MinCostFlow.HierPaths.QueryPath
public import MinCostFlow.HierPaths.Groups

/-!
# `GetPath` on the group hierarchy

This file instantiates the query of `HierPaths/QueryPath.lean` with the groups of
`HierPaths/Groups.lean`: terminals `0, …, 2 ^ x - 1`, branching `2 ^ b` with `b ≥ 1`, the group
index `groupOf x b`, and the leaf depth `leafDepth x b = ⌈x / b⌉`.

The connector choice is stated as `exists_surviving_matching_edge` gives it (`IsSiblingChoice`): for two different
children `Y` and `Z` of one group that each contain a surviving terminal, `pick j Y Z` is an
eligible connector with one endpoint in `Y` and the other in `Z`. `isConnectorChoice_of_sibling`
turns it into the form that `route_spec` uses. The main results are `route_spec_groups` (`route_spec` on
the hierarchy) and `getPath_spec_groups` (the postcondition of `GetPath`).
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

namespace ConnectorSystem

variable (C : ConnectorSystem)

/-- The connector choice on the group hierarchy: whenever `Y ≠ Z` are children of one group at
depth `j` (groups at depth `j + 1` with the same parent) and contain surviving terminals, the
connector `pick j Y Z` is eligible and has one endpoint in `Y` and the other in `Z`. -/
def IsSiblingChoice (x b : ℕ) (pick : ℕ → ℕ → ℕ → ℕ) (surv : Finset ℕ) : Prop :=
  ∀ j Y Z u v, u ∈ surv → v ∈ surv → u ∈ members x b (j + 1) Y → v ∈ members x b (j + 1) Z →
    parentGroup x b j Y = parentGroup x b j Z → Y ≠ Z →
      C.Eligible surv (pick j Y Z) ∧
        ((C.endA (pick j Y Z) ∈ members x b (j + 1) Y ∧ C.endB (pick j Y Z) ∈ members x b (j + 1) Z) ∨
         (C.endB (pick j Y Z) ∈ members x b (j + 1) Y ∧ C.endA (pick j Y Z) ∈ members x b (j + 1) Z))

end ConnectorSystem

end MinCostFlow.HierPaths

end

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

namespace ConnectorSystem

variable (C : ConnectorSystem)

public section

/-- A sibling choice is a connector choice for the group index `groupOf x b`. -/
theorem isConnectorChoice_of_sibling {x b : ℕ} {pick : ℕ → ℕ → ℕ → ℕ} {surv : Finset ℕ}
    (h : C.IsSiblingChoice x b pick surv) : C.IsConnectorChoice (groupOf x b) pick surv := by
  intro j u v hu hv huv hne
  have hpar : parentGroup x b j (groupOf x b (j + 1) u) =
      parentGroup x b j (groupOf x b (j + 1) v) := by
    rw [parentGroup, parentGroup, groupOf_succ_div, groupOf_succ_div, huv]
  obtain ⟨hel, hside⟩ := h j _ _ u v hu hv (mem_members_groupOf u) (mem_members_groupOf v) hpar hne
  refine ⟨hel, ?_⟩
  simp only [mem_members_iff] at hside
  exact hside

/-- At the leaf depth the group of a terminal is the terminal itself. -/
theorem groupOf_leafDepth {x b : ℕ} (hb : 0 < b) (u : ℕ) : groupOf x b (leafDepth x b) u = u := by
  rw [groupOf, groupSize_eq_one hb le_rfl, Nat.div_one]

/-- Query routing on the group hierarchy. Let `u` and `v` be surviving terminals in one
group at depth `j ≤ ⌈x / b⌉`. Then `route` at height `⌈x / b⌉ - j` is a walk from the owner of `u`
to the owner of `v` that uses no deleted edge and only live vertices, with at most
`2 ^ (⌈x / b⌉ - j) - 1` connectors and at most `(2 ^ (⌈x / b⌉ - j) - 1) · λ` edges. -/
theorem route_spec_groups {G : Graph} (hG : G.IsValid) (hfit : C.FitsGraph G) {D surv : Finset ℕ}
    (hrule : C.ReverseIndexRule D surv) (hsurv : surv ⊆ Finset.range C.numTerm) {x b : ℕ}
    (hb : 0 < b) {pick : ℕ → ℕ → ℕ → ℕ} (hpick : C.IsSiblingChoice x b pick surv) {lam : ℕ}
    (hlam : ∀ c < C.numConn, (C.walk c).edges.length ≤ lam) {j u v : ℕ}
    (hj : j ≤ leafDepth x b) (hu : u ∈ surv) (hv : v ∈ surv)
    (huv : groupOf x b j u = groupOf x b j v) :
    (C.route (groupOf x b) pick (leafDepth x b - j) j u v).IsWalk G (C.owner u) (C.owner v) ∧
      (∀ e ∈ (C.route (groupOf x b) pick (leafDepth x b - j) j u v).edges, e ∉ D) ∧
      (∀ y ∈ (C.route (groupOf x b) pick (leafDepth x b - j) j u v).verts,
        y ∈ C.liveSet G surv) ∧
      (C.route (groupOf x b) pick (leafDepth x b - j) j u v).edges.length ≤
        (2 ^ (leafDepth x b - j) - 1) * lam ∧
      C.routeCount (groupOf x b) pick (leafDepth x b - j) j u v ≤ 2 ^ (leafDepth x b - j) - 1 := by
  have hleaf : ∀ u ∈ surv, ∀ v ∈ surv, groupOf x b (leafDepth x b) u = groupOf x b (leafDepth x b) v →
      u = v := by
    intro u _ v _ h
    rwa [groupOf_leafDepth hb, groupOf_leafDepth hb] at h
  obtain ⟨h1, h2, h3, h4⟩ := C.route_spec (groupOf x b) pick hG hfit hrule hsurv
    (C.isConnectorChoice_of_sibling hpick) hleaf hlam (leafDepth x b - j) j u v (by omega) hu hv
    huv
  exact ⟨h1, h2, h3, h4, C.routeCount_le _ _ _ _ _ _⟩

/-- The postcondition of `GetPath` (operation `1` of `pathDSDataStructure`) on the group hierarchy
with `2 ^ x` terminals, branching `2 ^ b` with `b ≥ 1`, and depth `h = ⌈x / b⌉`: for two vertices
`w`, `w'` of `G` that are not pruned after time `t`, `GetPath(w, w')` is a walk from `w` to `w'`
with no repeated vertex, no deleted edge and no pruned vertex, with at most `(2 ^ h + 1) · λ`
edges, and it takes at most `6 · 2 ^ h · (λ + 1)` steps. -/
theorem getPath_spec_groups {G : Graph} (hG : G.IsValid) (hfit : C.FitsGraph G) {D : Finset ℕ}
    {surv : ℕ → Finset ℕ} (hanti : ∀ t, surv (t + 1) ⊆ surv t) {x b : ℕ}
    (hP : C.numTerm = 2 ^ x) (hb : 0 < b)
    (hsurv : ∀ t, surv t ⊆ Finset.range C.numTerm) {t lam : ℕ} {pick : ℕ → ℕ → ℕ → ℕ}
    (hrule : C.ReverseIndexRule D (surv t)) (hpick : C.IsSiblingChoice x b pick (surv t))
    (hlam : ∀ c < C.numConn, (C.walk c).edges.length ≤ lam)
    {w w' : ℕ} (hw : w ∈ G.verts \ C.prunedSet G (surv t))
    (hw' : w' ∈ G.verts \ C.prunedSet G (surv t)) :
    (C.getPath (groupOf x b) pick surv t (leafDepth x b) w w').IsWalk G w w' ∧
      (C.getPath (groupOf x b) pick surv t (leafDepth x b) w w').verts.Nodup ∧
      (∀ e ∈ (C.getPath (groupOf x b) pick surv t (leafDepth x b) w w').edges, e ∉ D) ∧
      (∀ y ∈ (C.getPath (groupOf x b) pick surv t (leafDepth x b) w w').verts,
        y ∉ C.prunedSet G (surv t)) ∧
      (C.getPath (groupOf x b) pick surv t (leafDepth x b) w w').edges.length ≤
        (2 ^ leafDepth x b + 1) * lam ∧
      C.queryOps (groupOf x b) pick surv t (leafDepth x b) w w' ≤
        6 * 2 ^ leafDepth x b * (lam + 1) := by
  have hroot : ∀ u ∈ surv t, ∀ v ∈ surv t, groupOf x b 0 u = groupOf x b 0 v := by
    intro u hu v hv
    have hu' := Finset.mem_range.mp (hsurv t hu)
    have hv' := Finset.mem_range.mp (hsurv t hv)
    rw [hP] at hu' hv'
    rw [groupOf_zero hu', groupOf_zero hv']
  have hleaf : ∀ u ∈ surv t, ∀ v ∈ surv t,
      groupOf x b (leafDepth x b) u = groupOf x b (leafDepth x b) v → u = v := by
    intro u _ v _ h
    rwa [groupOf_leafDepth hb, groupOf_leafDepth hb] at h
  exact C.getPath_spec (groupOf x b) pick hG hfit hanti hsurv hrule
    (C.isConnectorChoice_of_sibling hpick) hroot hleaf hlam hw hw'

end

end ConnectorSystem

end MinCostFlow.HierPaths
