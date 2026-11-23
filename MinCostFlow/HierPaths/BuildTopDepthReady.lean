module

public import MinCostFlow.HierPaths.BuildTopDepthRun

/-!
# Stability of a parent call's input

The parent graph and terminal list stay below the incoming heap and
outside the reply directory. The scan can therefore reuse the
initial memory facts for each call.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

private theorem prefixCost_le (f : ℕ → ℕ) {i n : ℕ} (hi : i ≤ n) :
    rangeCost f 0 i ≤ rangeCost f 0 n := by
  induction n, hi using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih =>
    rw [rangeCost_zero_eq_range f (n + 1), List.range_succ, List.map_append, List.sum_append,
      ← rangeCost_zero_eq_range]
    exact ih.trans (Nat.le_add_right _ _)

/-- The initial level precondition lifts to the current heap and the current memory. -/
theorem buildTopDepth_ready {w K h i : ℕ} {D : BuildTopDepthInput} {st : State} {mem : ℕ → ℕ}
    {space : Graph → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}
    (hi : i < D.count) (hd : D.replyDir + D.count ≤ h) (hst : D.state space h mem i st)
    (hwords : ∀ v ∈ D.callArgs i h, v < 2 ^ w)
    (hinit : (D.level w K space i).pre (D.callArgs i h) mem)
    (hgFrame : ∀ x, D.graphAddr i ≤ x →
      x < D.graphAddr i + (D.graph i).encode.length →
      x < D.replyDir ∨ D.replyDir + D.count ≤ x)
    (hxFrame : ∀ x, D.termBase + D.start i ≤ x →
      x < D.termBase + D.start i + D.childSize * D.branch →
      x < D.replyDir ∨ D.replyDir + D.count ≤ x)
    (hspace : h + rangeCost (D.spaceStep space) 0 D.count +
      space (D.graph i) D.childSize D.branch D.scale D.rank D.degree D.pathLog D.coreLog
        D.denominator < 2 ^ w) :
    (∀ v ∈ D.callArgs i (st.regs 12), v < 2 ^ w) ∧
      (D.level w K space i).pre (D.callArgs i (st.regs 12))
        (Function.update st.mem (D.replyDir + i) (st.regs 12)) := by
  obtain ⟨_, _, _, hlo, hhi, hz, hf, _⟩ := hst
  let cur := st.regs 12
  let mem' := Function.update st.mem (D.replyDir + i) cur
  have hHi := hhi.trans (Nat.add_le_add_left (prefixCost_le _ hi.le) h)
  have hCurrent : cur + space (D.graph i) D.childSize D.branch D.scale D.rank D.degree
      D.pathLog D.coreLog D.denominator < 2 ^ w := by omega
  have hmem (x : ℕ) (hx : x < h) (hDir : x < D.replyDir ∨ D.replyDir + D.count ≤ x) :
      mem' x = mem x := by
    dsimp only [mem']
    exact (Function.update_of_ne (by rcases hDir with ht | ht <;> omega) _ _).trans (hf x hx hDir)
  refine ⟨?_, ?_⟩
  · intro v hv
    by_cases he : v = cur
    · rw [he]
      omega
    · apply hwords
      simp only [BuildTopDepthInput.callArgs, buildLevelArgs, List.mem_cons, List.not_mem_nil,
        or_false] at hv ⊢
      tauto
  obtain ⟨ga, base, top, he, hbase, hp⟩ := hinit
  have he' : ga = D.graphAddr i ∧ base = D.termBase ∧ top = h := by
    simp only [BuildTopDepthInput.callArgs, buildLevelArgs, List.cons.injEq, and_true,
      true_and] at he
    exact ⟨he.1.symm, he.2.1.symm, he.2.2.symm⟩
  obtain ⟨rfl,rfl,rfl⟩ := he'
  obtain ⟨⟨ga, xa, a, he, hG, hX, hGa, hXa, hValid, hHost, hk, hs, hEven, hN, hRank, hDelta,
    hL, hBeta⟩, _, _⟩ := hp
  simp only [buildLevelArgs, List.cons.injEq, and_true, true_and] at he
  obtain ⟨_, _, _⟩ := he
  subst ga xa a
  refine ⟨D.graphAddr i, D.termBase, cur, rfl, hbase, ⟨⟨D.graphAddr i,
    D.termBase + D.start i, cur, rfl, ?_, ?_, hGa.trans hlo, hXa.trans hlo, hValid, hHost,
    hk, hs, hEven, hN, hRank, hDelta, hL, hBeta⟩, ?_, hCurrent⟩⟩
  · unfold GraphAt at *
    exact listAt_congr (fun j hj => (hmem _ (by omega) (hgFrame _ (by omega) (by omega))).symm) hG
  · have hl : (finsetWords (buildLevelVerts (D.start i) D.childSize D.branch)).length =
        D.childSize * D.branch := by rw [buildTopLevelWords_eq, List.length_range']
    refine listAt_congr (fun j hj => (hmem _ (by omega)
      (hxFrame _ (by omega) (by omega))).symm) hX
  · intro x hx
    change cur ≤ x at hx
    exact (Function.update_of_ne (by omega) _ _).trans (hz x hx)

end MinCostFlow.HierPaths

end
