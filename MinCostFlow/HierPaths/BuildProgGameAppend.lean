module

public import MinCostFlow.HierPaths.BuildProgLocalEnds
public import MinCostFlow.HierPaths.BuildProgContracts

/-!
# Adding a matching to a child game graph

After a full-routing call, the builder appends the routed matching for each active child.
Appending writes only the new local edge endpoints and the graph's edge count. The
graph's old edges retain their indices, so previously stored walks keep their indices.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-- The new child graph after appending the matching from the parent host. -/
def appendGameMatching (G : Graph) (off : ℕ) (es : List (ℕ × ℕ)) : Graph :=
  ⟨G.n, G.edges ++ es.map (fun e => (e.1 - off, e.2 - off))⟩

/-- In registers 0 through 3, take the graph base, matching base, matching size and child
offset. Append the local edges and return the new edge count. -/
def buildGameAppendProc (fEnds : ℕ) : Stmt :=
  .seq (.assign 4 (.load (.bin .add (.reg 0) (.const 1))))
    (.seq (.assign 5 (.bin .add (.bin .add (.reg 0) (.const 2))
        (.bin .add (.reg 4) (.reg 4))))
      (.seq (.call 6 fEnds [.reg 1, .bin .add (.reg 2) (.reg 2), .reg 5, .reg 3])
        (.seq (.assign 7 (.bin .add (.reg 4) (.reg 2)))
          (.seq (.store (.bin .add (.reg 0) (.const 1)) (.reg 7)) (.ret (.reg 7))))))

theorem buildGameAppendProc_noRand (fEnds : ℕ) : (buildGameAppendProc fEnds).NoRand :=
  ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-- The source matching is stored outside the part of the game block that is rewritten. -/
def buildGameAppendContract (w : ℕ) (G : Graph) (es : List (ℕ × ℕ)) : Contract where
  pre args mem := ∃ g src off, args = [g, src, es.length, off] ∧ GraphAt mem g G ∧
    ListAt mem src (es.flatMap fun e => [e.1, e.2]) ∧
    g + 2 + 2 * (G.m + es.length) ≤ src ∧ src + 2 * es.length < 2 ^ w ∧
    ∀ e ∈ es, off ≤ e.1 ∧ off ≤ e.2 ∧ e.1 < 2 ^ w ∧ e.2 < 2 ^ w
  post args mem v mem' := ∃ g src off, args = [g, src, es.length, off] ∧
    GraphAt mem' g (appendGameMatching G off es) ∧ v = G.m + es.length ∧
    ∀ i, i ≠ g + 1 → (i < g + 2 + 2 * G.m ∨ g + 2 + 2 * (G.m + es.length) ≤ i) →
      mem' i = mem i
  cost _ _ := 38 * es.length + 64

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

private theorem appendGame_at {mem mem' : ℕ → ℕ} {g off : ℕ} {G : Graph}
    {es : List (ℕ × ℕ)} (hOld : GraphAt mem g G)
    (hCount : mem' (g + 1) = G.m + es.length)
    (hOldCells : ∀ i < g + 2 + 2 * G.m, i ≠ g + 1 → mem' i = mem i)
    (hNew : ListAt mem' (g + 2 + 2 * G.m)
      ((es.flatMap fun e => [e.1, e.2]).map (· - off))) :
    GraphAt mem' g (appendGameMatching G off es) := by
  have he : ((es.map fun e => (e.1 - off, e.2 - off)).flatMap fun e => [e.1, e.2]) =
      (es.flatMap fun e => [e.1, e.2]).map (· - off) := by
    clear hCount hNew
    induction es <;> simp_all
  change ListAt mem' g (appendGameMatching G off es).encode
  have hLayout : (appendGameMatching G off es).encode =
      [G.n, G.m + es.length] ++ (G.edges.flatMap fun e => [e.1, e.2]) ++
        ((es.flatMap fun e => [e.1, e.2]).map (· - off)) := by
    simp [appendGameMatching, Graph.encode, Graph.m, he]
  have hLen : (G.edges.flatMap fun e => [e.1, e.2]).length = 2 * G.m := by
    simp [Graph.m, List.length_flatMap, Nat.mul_comm]
  rw [hLayout, listAt_append, listAt_append]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i hi
    have hi' : i = 0 ∨ i = 1 := by simp at hi; omega
    rcases hi' with rfl | rfl
    · exact (hOldCells g (by omega) (by omega)).trans (hOld 0 (by simp [Graph.encode]))
    · exact hCount
  · intro i hi
    have ho : i + 2 < G.encode.length := by
      change i + 2 < ((G.edges.flatMap fun e => [e.1, e.2]).length + 1) + 1
      omega
    simp only [List.length_cons, List.length_nil]
    rw [hOldCells _ (by omega) (by omega)]
    have hv := hOld (i + 2) ho
    change mem (g + (i + 2)) = (G.edges.flatMap fun e => [e.1, e.2])[i] at hv
    rw [show g + 2 + i = g + (i + 2) by omega]
    exact hv
  · have hb : g + ([G.n, G.m + es.length] ++ (G.edges.flatMap fun e => [e.1, e.2])).length =
        g + 2 + 2 * G.m := by simp only [List.length_append, hLen, List.length_cons, List.length_nil, Nat.add_assoc]; omega
    rwa [hb]

/-- Appending a matching meets its graph and memory contract in linear time. -/
theorem buildGameAppendProc_meetsContract {w : ℕ} {p : Program} {f fEnds : ℕ}
    {G : Graph} {es : List (ℕ × ℕ)}
    (hProc : p.procs[f]? = some (buildGameAppendProc fEnds))
    (hEnds : p.procs[fEnds]? = some buildLocalEndsProc) :
    MeetsContract w p f (buildGameAppendContract w G es) := by
  refine meetsContract_of_runs hProc fun args mem pos ω hWords hPre => ?_
  obtain ⟨g, src, off, rfl, hG, hEs, hSep, hFit, hV⟩ := hPre
  let dst := g + 2 + 2 * G.m
  let len := 2 * es.length
  have hDst : dst + len ≤ src := by dsimp [dst, len]; omega
  have hSrc : src + len < 2 ^ w := hFit
  have hm := hG 1 (by simp [Graph.encode])
  change mem (g + 1) = G.m at hm
  have hLen : (es.flatMap fun e => [e.1, e.2]).length = len := by
    simp [len, List.length_flatMap, Nat.mul_comm]
  have hValid : ∀ i < len, off ≤ mem (src + i) ∧ mem (src + i) < 2 ^ w := by
    intro i hi
    have ho : i < (es.flatMap fun e => [e.1, e.2]).length := hLen ▸ hi
    rw [hEs i ho]
    have hv := List.getElem_mem (l := es.flatMap fun e => [e.1, e.2]) ho
    obtain ⟨e, he, hv⟩ := List.mem_flatMap.mp hv
    obtain ⟨ha, hb, hc, hd⟩ := hV e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with h | h <;> rw [h] <;> omega
  have hOne : 1 < 2 ^ w := by dsimp [dst] at hDst; omega
  have hTwo : 2 < 2 ^ w := by dsimp [dst] at hDst; omega
  have hG1 : g + 1 < 2 ^ w := by dsimp [dst] at hDst; omega
  have hG2 : g + 2 < 2 ^ w := by dsimp [dst] at hDst; omega
  have hDouble : G.m + G.m < 2 ^ w := by dsimp [dst] at hDst; omega
  have hTwice : es.length + es.length < 2 ^ w := by dsimp [len] at hSrc; omega
  have hDstFit : g + 2 + (G.m + G.m) < 2 ^ w := by dsimp [dst] at hDst; omega
  have hTotal : G.m + es.length < 2 ^ w := by omega
  refine runs_start_le ?_
  unfold buildGameAppendProc
  refine runs_seq_assign_le (v := G.m) ?_ ?_
  · simp [Expr.eval, startState, hOne, hG1, hm]
  refine runs_seq_assign_le (v := dst) ?_ ?_
  · simp [Expr.eval, startState, Function.update, hTwo, hG2, hDouble, hDstFit, dst, Nat.two_mul]
  refine runs_seq_call_le (buildLocalEndsProc_meetsContract hEnds)
    (vs := [src, len, dst, off]) ?_ ?_
    ⟨src, len, dst, off, rfl, Or.inr hDst, hSrc, by omega, hOne, hValid⟩ ?_
  · simp [evalArgs, Expr.eval, startState, Function.update, hTwice, len, Nat.two_mul]
  · have hOff := hWords off (by simp)
    wram_words
  intro _ mem₁ pos₁ hPost
  obtain ⟨_, _, _, _, ha, hVals, hFrame⟩ := hPost
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨rfl, rfl, rfl, rfl⟩ := ha
  change (∀ j < len, mem₁ (dst + j) = mem (src + j) - off) at hVals
  refine runs_seq_assign_le (v := G.m + es.length) ?_ ?_
  · simp [Expr.eval, startState, Function.update, hTotal]
  refine runs_seq_store_le (x := g + 1) (v := G.m + es.length) ?_ ?_ ?_
  · simp [Expr.eval, startState, Function.update, hG1, hOne]
  · simp [Expr.eval, Function.update]
  refine runs_ret_le (v := G.m + es.length) (by simp [Expr.eval, Function.update]) ?_ ?_
  · refine ⟨g, src, off, rfl, ?_, rfl, ?_⟩
    · apply appendGame_at hG (by simp)
      · intro i hi hn
        exact (Function.update_of_ne hn _ _).trans (hFrame i (Or.inl hi))
      · intro i hi
        have hi' : i < len := by simpa only [List.length_map, hLen] using hi
        have hne : dst + i ≠ g + 1 := by dsimp [dst]; omega
        change Function.update mem₁ (g + 1) (G.m + es.length) (dst + i) = _
        rw [Function.update_of_ne hne, hVals i hi', List.getElem_map, hEs]
    · intro i hn hi
      change Function.update mem₁ (g + 1) (G.m + es.length) i = mem i
      rw [Function.update_of_ne hn]
      apply hFrame
      dsimp [dst, len]
      omega
  · simp [buildGameAppendContract, buildLocalEndsContract, argsSize, Expr.size, len]
    omega

end MinCostFlow.HierPaths
