module

public import MinCostFlow.HierPaths.BuildTopPort
public import MinCostFlow.HierPaths.BuildTopRoot
public import MinCostFlow.HierPaths.InitProg

/-!
# The padded root and its static section words

The in-place padding program gives the root host of `lemma_2` (port graph and padding),
and the owner and edge-label columns are the ones required by StaticOut.
-/

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

theorem buildTopPaddedGraph_eq (G : Graph) :
    buildTopPaddedGraph (portGraph cloud G G.verts) (hostSize G) = hostGraph cloud G := by
  rw [buildTopPaddedGraph, hostGraph, portGraph_n]
  rfl

theorem buildTopRootOwners_eq {G : Graph} (hv : G.IsValid) (hm : 1 ≤ G.m) :
    let owners := (List.range (2 * G.m)).map (portOwner G G.verts)
    owners ++ owners.take (hostSize G - portCount G) = tabList (hostSize G) (hostOwner G) := by
  let owners := (List.range (2 * G.m)).map (portOwner G G.verts)
  let q := hostSize G - portCount G
  have hLen : owners.length = portCount G := by
    simp [owners, portCount, inside_verts_length hv]
  have hle := le_hostSize G
  have hp := hostSize_lt (by rwa [inside_verts_length hv])
  have hq : q ≤ owners.length := by dsimp [q]; omega
  have htake : (owners.take q).length = q := by simp [hq]
  change owners ++ owners.take q = tabList (hostSize G) (hostOwner G)
  apply List.ext_getElem
  · rw [List.length_append, hLen, htake]
    simp [tabList, q, Nat.add_sub_of_le hle]
  · intro i hi hi'
    simp only [tabList, List.getElem_map, List.getElem_range]
    unfold hostOwner
    by_cases ht : i < portCount G
    · rw [ite_eq_left ht, List.getElem_append_left (by omega)]
      simp [owners, portCount, inside_verts_length hv]
    · rw [ite_eq_right ht, List.getElem_append_right (by omega), List.getElem_take]
      simp [owners, portCount, inside_verts_length hv]

theorem buildTopLabelWords_eq {G : Graph} (hv : G.IsValid) (hm : 1 ≤ G.m) :
    buildTopLabelWords G.m (hostGraph cloud G).m =
      tabList (hostGraph cloud G).m (fun i => labelWord (hostLabel G i)) := by
  have hp : G.m ≤ (hostGraph cloud G).m := by
    unfold hostGraph Graph.m portGraph
    simp [origPortEdges, inside_verts_length hv, Graph.m]
  apply List.ext_getElem
  · simp [buildTopLabelWords, tabList, Nat.add_sub_of_le hp]
  intro i hi hi'
  simp only [buildTopLabelWords, tabList, List.getElem_map, List.getElem_range]
  unfold hostLabel
  rw [inside_verts_length hv]
  by_cases h : i < G.m
  · rw [ite_eq_left h, List.getElem_append_left (by simpa using h)]
    simp [labelWord]
  · rw [ite_eq_right h, List.getElem_append_right (by simpa using Nat.le_of_not_gt h)]
    simp [labelWord]

end MinCostFlow.HierPaths

end
