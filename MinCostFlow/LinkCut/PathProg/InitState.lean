module

public import MinCostFlow.LinkCut.PathProg.Init

/-!
# The arena after the initialization holds the initial model state

After `pathInitBody`, the records of nodes `0 .. 2 n` hold the nodes of
`lctInit pathPayload n none` in the path layout of width `K = treeLimbs L` (`initMem_nodesAt`),
and the index is empty (`initMem_idx`). Every node starts alone with no value, the empty summary
and the zero tag, and these are all encoded by zero words, apart from the layout words.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathProg

open WordRAM MinCostFlow.Num MinCostFlow.MinRatio MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen
  MinCostFlow.LinkCut.Path NodeLayout

/-- The nodes of the initial state. -/
theorem lctInit_node (n x : ℕ) :
    (lctInit pathPayload n none).splay.nodes x =
      { left := 0, right := 0, par := initPar n x, ppar := 0, sz := 1, val := none,
        sum := PathSummary.empty, tag := PathTag.zero, rev := false } := by
  change lctInitNodes pathPayload n none x = _
  unfold lctInitNodes initPar
  split_ifs <;> first | rfl | omega | (congr 1; omega)

/-- A block of zero words is the number zero. -/
theorem pathIntAt_of_zero {m : ℕ → ℕ} {a h K : ℕ} (hz : ∀ i < K, m (a + i) = 0) :
    PathIntAt m a h K 0 :=
  ⟨fun i hi => by rw [hz i hi]; exact base_pos h, intVal_zero hz⟩

/-- The records hold the initial state. -/
theorem initMem_nodesAt {h n L heap : ℕ} {mem m : ℕ → ℕ} (hI : InitMem n L heap mem m) :
    (pathLayout h (treeLimbs L)).NodesAt m (arenaNb heap n) (2 * n)
      (lctInit pathPayload n none).splay := by
  intro x hx
  set K := treeLimbs L
  have hS : (pathLayout h K).nodeStride = recW K := by rw [pathLayout_stride]; rfl
  have hw : ∀ off < recW K, m ((pathLayout h K).nodeAddr (arenaNb heap n) x + off) =
      initWord n K x off := fun off hoff => by
    unfold nodeAddr; rw [hS]; exact hI.recs x hx off hoff
  have hW : 9 * K + 13 = recW K := by unfold recW; omega
  have hz : ∀ off, 10 ≤ off → off < recW K →
      m ((pathLayout h K).nodeAddr (arenaNb heap n) x + off) = 0 := fun off h1 h2 => by
    rw [hw off h2]; unfold initWord; split_ifs <;> omega
  rw [lctInit_node]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [OFF_LEFT, hw 0 (by omega)]; rfl
  · rw [OFF_RIGHT, hw 1 (by omega)]; rfl
  · rw [OFF_PAR, hw 2 (by omega)]; rfl
  · rw [OFF_PPAR, hw 3 (by omega)]; rfl
  · rw [OFF_SZ, hw 4 (by omega)]; rfl
  · rw [OFF_REV, hw 5 (by omega)]; rfl
  · show PathValAt m _ h K none
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [OFF_VAL, hw 6 (by omega)]; rfl
    · rw [OFF_VAL, Nat.add_assoc, hw 7 (by omega)]; rfl
    · rw [OFF_VAL, Nat.add_assoc, hw 8 (by omega)]; rfl
    · rw [OFF_VAL, Nat.add_assoc, hw 9 (by omega)]; rfl
    · show m _ = 0
      rw [OFF_VAL, Nat.add_assoc]; exact hz 10 (by omega) (by omega)
  · show PathSummaryAt m _ h K PathSummary.empty
    rw [pathLayout_offSum]
    refine ⟨pathIntAt_of_zero fun i hi => ?_, pathIntAt_of_zero fun i hi => ?_, ?_⟩
    · rw [Nat.add_assoc]; exact hz _ (by omega) (by omega)
    · rw [Nat.add_assoc, Nat.add_assoc]; exact hz _ (by omega) (by omega)
    · show m _ = 0
      rw [Nat.add_assoc]; exact hz _ (by omega) (by omega)
  · show PathTagAt m _ h K PathTag.zero
    rw [pathLayout_offTag]
    refine ⟨pathIntAt_of_zero fun i hi => ?_, pathIntAt_of_zero fun i hi => ?_⟩
    · rw [Nat.add_assoc]; exact hz _ (by omega) (by omega)
    · rw [Nat.add_assoc, Nat.add_assoc]; exact hz _ (by omega) (by omega)

/-- The index is empty. -/
theorem initMem_idx {n L heap : ℕ} {mem m : ℕ → ℕ} (hI : InitMem n L heap mem m) :
    IdxAt m (arenaNb heap n) (2 * n) [] := by
  have hnb : arenaNb heap n = heap + 4 * n + 8 := rfl
  refine ⟨List.nodup_nil, fun z hz => by simp at hz, ?_, fun i hi => by simp at hi, ?_⟩
  · rw [hI.idx _ (by omega) (by omega)]; rfl
  · intro x hx
    unfold flagAddr
    rw [hI.idx _ (by omega) (by omega)]; simp

end MinCostFlow.LinkCut.PathProg
