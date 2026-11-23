module

public import MinCostFlow.MinRatio.PathSummaryDetection
public import MinCostFlow.Basic.Forest
public import MinCostFlow.Chain.CoreGraph
public import MinCostFlow.MinRatio.PathPayloadLayout
import MinCostFlow.Chain.Cycles
import MinCostFlow.Chain.WalkFlow
import MinCostFlow.LSF.Walks

/-!
# Interpreting tree summaries as path aggregates

Theorem 5.1 (pages 29–30) reads the gradient inner product and length
of a tree path from its dynamic-tree summary. The signed gradient
depends on the traversal direction, and the length does not. Vertex
nodes contribute zero to both.
-/

public section

namespace MinCostFlow.MinRatio
open Chain

private theorem summarizePath_sums (values : List (Option PathEdgeValue)) :
    (summarizePath values).gradient = ((values.filterMap id).map PathEdgeValue.gradient).sum ∧
    (summarizePath values).length = ((values.filterMap id).map PathEdgeValue.length).sum := by
  induction values with
  | nil => exact ⟨rfl, rfl⟩
  | cons v rest ih =>
    cases v <;> simp [summarizePath, PathSummary.single, PathSummary.combine,
      PathSummary.empty, ih.1, ih.2]

private theorem walkInner_eq_signed_sum (g : ℕ → ℝ) (walk : List (ℕ × Bool)) :
    walkInner g walk = (walk.map fun x => if x.2 then g x.1 else -g x.1).sum := by
  induction walk with
  | nil => exact walkInner_nil g
  | cons x rest ih => rw [walkInner_cons, walkInner_singleton, ih, List.map_cons, List.sum_cons]

/-- Reading an oriented path summary gives exactly the paper's two
path quantities. The edge list may be interleaved with vertex values. -/
theorem summarizePath_walk {F : MGraph} {u v : ℕ} {walk : List (ℕ × Bool)}
    (hpath : F.IsPath u v walk) (P : ℕ)
    (g length : ℕ → ℝ) (values : List (Option PathEdgeValue)) (payload : ℕ × Bool → PathEdgeValue)
    (hvalues : values.filterMap id = walk.map payload)
    (hg : ∀ x ∈ walk, ((payload x).gradient : ℝ) / (2 : ℝ) ^ P =
      if x.2 then g x.1 else -g x.1)
    (hl : ∀ x ∈ walk, ((payload x).length : ℝ) / (2 : ℝ) ^ P = length x.1) :
    ((summarizePath values).gradient : ℝ) / (2 : ℝ) ^ P = walkInner g walk ∧
      ((summarizePath values).length : ℝ) / (2 : ℝ) ^ P = walkLength length walk := by
  obtain ⟨hgradient, hlength⟩ := summarizePath_sums values
  rw [hvalues] at hgradient hlength
  have hsum (field : PathEdgeValue → ℤ) :
      (((walk.map payload).map field).sum : ℝ) / (2 : ℝ) ^ P =
        (walk.map fun x => (field (payload x) : ℝ) / (2 : ℝ) ^ P).sum := by
    clear hpath hvalues hg hl hgradient hlength
    induction walk with
    | nil => simp
    | cons x rest ih =>
      simp only [List.map_cons, List.sum_cons, Int.cast_add, add_div, ih]
  constructor
  · rw [hgradient, hsum, walkInner_eq_signed_sum]
    exact congrArg List.sum (List.map_congr_left hg)
  · rw [hlength, hsum, LSF.walkLength_eq_sum_of_isPath length hpath]
    unfold walkEdges
    rw [List.sum_toFinset _ (LSF.isPath_nodup_edges hpath), List.map_map]
    exact congrArg List.sum (List.map_congr_left hl)

/-- The first two output blocks of a stored summary are the
fixed-point gradient and length readouts used by the routing code. -/
theorem summarizePath_readout {F : MGraph} {u v : ℕ} {walk : List (ℕ × Bool)}
    (hpath : F.IsPath u v walk) (P : ℕ)
    (g length : ℕ → ℝ) (values : List (Option PathEdgeValue)) (payload : ℕ × Bool → PathEdgeValue)
    (hvalues : values.filterMap id = walk.map payload)
    (hg : ∀ x ∈ walk, ((payload x).gradient : ℝ) / (2 : ℝ) ^ P =
      if x.2 then g x.1 else -g x.1)
    (hl : ∀ x ∈ walk, ((payload x).length : ℝ) / (2 : ℝ) ^ P = length x.1)
    {mem : ℕ → ℕ} {a h L : ℕ} (hout : PathSummaryAt mem a h L (summarizePath values)) :
    Num.Valid mem a h L ∧ Num.fixVal mem a h L P = walkInner g walk ∧
      Num.Valid mem (a + L) h L ∧ Num.fixVal mem (a + L) h L P = walkLength length walk := by
  obtain ⟨hgrad, hlen⟩ := summarizePath_walk hpath P g length values payload hvalues hg hl
  refine ⟨hout.1.1, ?_, hout.2.1.1, ?_⟩
  · rw [Num.fixVal, hout.1.2]
    exact hgrad
  · rw [Num.fixVal, hout.2.1.2]
    exact hlen

/-- The signed path summary from a vertex to its component root gives
the stored potential for the core-gradient handoff (Definition 5.6, page 18). -/
theorem treeRootPot_path_readout {F : MGraph} (hforest : F.IsForest) (v : ℕ)
    (prec : ℕ) (g length : ℕ → ℝ)
    (values : List (Option PathEdgeValue)) (payload : ℕ × Bool → PathEdgeValue)
    (hvalues : values.filterMap id = (F.forestPath v (compRoot F v)).map payload)
    (hg : ∀ x ∈ F.forestPath v (compRoot F v),
      ((payload x).gradient : ℝ) / (2 : ℝ) ^ prec = if x.2 then g x.1 else -g x.1)
    (hl : ∀ x ∈ F.forestPath v (compRoot F v),
      ((payload x).length : ℝ) / (2 : ℝ) ^ prec = length x.1)
    {mem : ℕ → ℕ} {a h L : ℕ} (hout : PathSummaryAt mem a h L (summarizePath values)) :
    Num.Valid mem a h L ∧ Num.fixVal mem a h L prec = treeRootPot F g v := by
  have hpath := LSF.forestPath_isPath hforest (connected_compRoot F v)
  obtain ⟨hv, heq, _, _⟩ :=
    summarizePath_readout hpath prec g length values payload hvalues hg hl hout
  exact ⟨hv, heq⟩

/-- A potential traversal can initialize the component root to zero.
This is the base case for the root potentials used in Definition 5.6. -/
theorem treeRootPot_componentRoot (F : MGraph) (hforest : F.IsForest) (g : ℕ → ℝ) (v : ℕ) :
    treeRootPot F g (compRoot F v) = 0 := by
  have hroot : compRoot F (compRoot F v) = compRoot F v :=
    (compRoot_eq_of_connected (connected_compRoot F v)).symm
  unfold treeRootPot
  rw [hroot, LSF.forestPath_self hforest]
  simp [walkInner, walkEdges]

/-- In a traversal of the selected forest, a signed edge from child
to parent adds its gradient to the parent's potential. -/
theorem treeRootPot_of_parent_edge {F : MGraph} (hforest : F.IsForest) (g : ℕ → ℝ)
    {child parent : ℕ} {edge : ℕ × Bool} (hpath : F.IsPath child parent [edge]) :
    treeRootPot F g child =
      treeRootPot F g parent + (if edge.2 then g edge.1 else -g edge.1) := by
  have hconn : F.Connected child parent := ⟨[edge], hpath.1⟩
  have hd := walkInner_forestPath_eq_sub_treeRootPot hforest hconn g
  rw [LSF.forestPath_eq_of_isPath hforest hpath, walkInner_eq_signed_sum] at hd
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hd
  exact (sub_eq_iff_eq_add.mp hd.symm).trans (add_comm _ _)

end MinCostFlow.MinRatio
