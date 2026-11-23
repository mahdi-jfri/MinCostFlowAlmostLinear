module

public import MinCostFlow.HierPaths.BuildTopScheduledDepth
public import MinCostFlow.HierPaths.BuildTopScheduleFrame
public import MinCostFlow.HierPaths.BuildTopModel

/-! # Reading the next depth's parent graphs after an advance -/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- The graph directory names the address of every parent, with its encoded graph. -/
def BuildTopDepthInput.graphsAt (D : BuildTopDepthInput) (mem : ℕ → ℕ) : Prop :=
  ∀ i < D.count, mem (D.graphDir + i) = D.graphAddr i ∧ GraphAt mem (D.graphAddr i) (D.graph i)

/-- Certified replies supply the graph representation for the next iteration. -/
theorem buildTopScheduledGraphs_next {w K table n term x b m d i h v dir : ℕ}
    {addr : ℕ → ℕ} {graphs : ℕ → Cited.Graph} {mem mem' : ℕ → ℕ}
    {space : Cited.Graph → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}
    (hi : i < n) (hstart : buildTopScheduleEnd table n x ≤ h)
    (hp : let D := buildTopScheduledDepth table n term x b m d i dir addr graphs
      (D.advanceContract w K space).post
        (D.args h ++ [buildTopSchedulePointer table n (i + 1)]) mem v mem') :
    ∃ nextAddr nextGraph, let dir' := mem' (buildTopSchedulePointer table n (i + 1))
      (buildTopScheduledDepth table n term x b m d (i + 1) dir' nextAddr nextGraph).graphsAt mem' ∧
      ∀ j < numGroups x b (i + 1),
        (nextGraph j).IsValid ∧ (nextGraph j).IsLoopless ∧
        (∀ u ∈ members x b (i + 1) j, (nextGraph j).deg u ≤ 49 * (x + 1) + 2) ∧
        (1 < groupSize x b (i + 1) →
          (nextGraph j).IsExpansionExpanderOn (members x b (i + 1) j)
            (1 / (2 * (PParam ParamConfig.default (2 ^ x) (depthOf m) : ℝ)))) := by
  dsimp only at hp
  let D := buildTopScheduledDepth table n term x b m d i dir addr graphs
  obtain ⟨_,_,dir',prev,reply,_,_,hptr,hreply,hchild⟩ :=
    buildTopAdvance_scheduleLink (b := b) (D := D) hi rfl hstart hp
  let k := branching x b i
  have hk : 0 < k := branching_pos
  refine ⟨fun j => buildTopChildAddr (prev (j / k)) k (j % k) (reply (j / k)),
    fun j => (reply (j / k)).host (j % k), ?_⟩
  dsimp only
  have hbound (j : ℕ) (hj : j < numGroups x b (i + 1)) :
      j < numGroups x b i * k := by rwa [numGroups_succ] at hj
  constructor
  · intro j hj
    have hcount := hbound j hj
    have hparent : j / k < D.count := (Nat.div_lt_iff_lt_mul hk).mpr hcount
    have hlocal : j % k < k := Nat.mod_lt _ hk
    exact ⟨hptr ▸ hchild j hcount,
      buildTopChildAddr_graphAt (hreply (j / k) hparent).2.2.2.1 hlocal⟩
  · intro j hj
    have hparent : j / k < D.count := (Nat.div_lt_iff_lt_mul hk).mpr (hbound j hj)
    have hlocal : j % k < k := Nat.mod_lt _ hk
    obtain ⟨_,hvalid,hloops,_,hdegree,_,hexp⟩ :=
      (hreply (j / k) hparent).2.2.2.2.graph (j % k) hlocal
    have he : buildLevelChild (D.start (j / k)) D.childSize (j % k) =
        members x b (i + 1) j := by
      have hstart' : D.start (j / k) = (j / k) * groupSize x b i := by
        unfold BuildTopDepthInput.start
        change (j / k) * (groupSize x b (i + 1) * k) = _
        rw [Nat.mul_comm (groupSize x b (i + 1)), ← groupSize_eq_mul_branching]
      rw [hstart', show D.childSize = groupSize x b (i + 1) from rfl, buildTopLevelChild_eq]
      exact congrArg (members x b (i + 1)) (buildTopChild_decompose x b i j)
    rw [he] at hdegree hexp
    exact ⟨hvalid,hloops,hdegree,hexp⟩

end MinCostFlow.HierPaths

end
