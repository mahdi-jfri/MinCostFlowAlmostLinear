module

public import MinCostFlow.HierPaths.BuildProgLevelSpec
public import MinCostFlow.HierPaths.BuildTopGeometry
import MinCostFlow.HierPaths.BuildChildCall

/-!
# The hierarchy from the parent calls

Each call contributes the hosts and embeddings of its children and the
connectors between them. Child remainders select the rows of its reply.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- Assemble parent replies in the global group numbering. -/
def buildTopHierarchy (x b : ℕ) (root : Graph) (reply : ℕ → ℕ → BuildLevelData) : HierData where
  host
    | 0, g => if g = 0 then root else ⟨0, []⟩
    | j + 1, c =>
      if c < numGroups x b (j + 1) then
        (reply j (parentGroup x b j c)).host (c % branching x b j)
      else ⟨0, []⟩
  emb j c :=
    if c < numGroups x b (j + 1) then
      (reply j (parentGroup x b j c)).emb (c % branching x b j)
    else fun _ => []
  conn j c c' :=
    if c < c' ∧ c' < numGroups x b (j + 1) ∧
        parentGroup x b j c = parentGroup x b j c' then
      (reply j (parentGroup x b j c)).conn (c % branching x b j) (c' % branching x b j)
    else []

theorem buildTopLevelVerts_eq (x b j g : ℕ) :
    buildLevelVerts (g * groupSize x b j) (groupSize x b (j + 1)) (branching x b j) =
      members x b j g := by
  unfold buildLevelVerts members
  rw [buildTopParent_end]

theorem buildTopLevelChild_eq (x b j g c : ℕ) :
    buildLevelChild (g * groupSize x b j) (groupSize x b (j + 1)) c =
      members x b (j + 1) (g * branching x b j + c) := by
  ext v
  rw [buildLevelChild, mem_shiftSet_iff, Finset.mem_range, members, Finset.mem_Ico,
    buildTopChild_start, Nat.add_mul, Nat.one_mul, buildTopChild_start]
  omega

theorem buildTopChild_decompose (x b j c : ℕ) :
    parentGroup x b j c * branching x b j + c % branching x b j = c := by
  unfold parentGroup
  rw [Nat.mul_comm]
  exact Nat.div_add_mod c (branching x b j)

theorem buildTopChild_global_lt {x b j g c : ℕ}
    (hg : g < numGroups x b j) (hc : c ∈ childGroups x b j g) :
    c < numGroups x b (j + 1) := by
  rw [childGroups_eq_Ico, Finset.mem_Ico] at hc
  rw [numGroups_succ]
  exact hc.2.trans_le (by
    rw [← Nat.succ_mul]
    exact Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hg))

theorem buildTopChild_mod_lt_mod {x b j g c c' : ℕ}
    (hc : c ∈ childGroups x b j g) (hc' : c' ∈ childGroups x b j g)
    (hlt : c < c') :
    c % branching x b j < c' % branching x b j := by
  have h := buildTopChild_decompose x b j c
  have h' := buildTopChild_decompose x b j c'
  rw [mem_childGroups_iff.mp hc] at h
  rw [mem_childGroups_iff.mp hc'] at h'
  omega

/-- Child replies determine the exact host, embedding and connector rows. -/
theorem buildTopHierarchy_rows (x b j g c c' : ℕ) (root : Graph)
    (reply : ℕ → ℕ → BuildLevelData)
    (hg : g < numGroups x b j) (hc : c ∈ childGroups x b j g)
    (hc' : c' ∈ childGroups x b j g) (hlt : c < c') :
    let H := buildTopHierarchy x b root reply
    let k := branching x b j
    H.host (j + 1) c = (reply j g).host (c % k) ∧
    H.emb j c = (reply j g).emb (c % k) ∧
    H.conn j c c' = (reply j g).conn (c % k) (c' % k) := by
  have hC := buildTopChild_global_lt hg hc
  have hC' := buildTopChild_global_lt hg hc'
  have hP := mem_childGroups_iff.mp hc
  have hP' := mem_childGroups_iff.mp hc'
  simp [buildTopHierarchy, hC, hC', hP, hP', hlt]

end MinCostFlow.HierPaths

end
