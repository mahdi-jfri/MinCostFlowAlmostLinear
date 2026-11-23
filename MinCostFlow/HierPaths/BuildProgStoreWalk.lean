module

public import MinCostFlow.HierPaths.BuildProgPath
public import MinCostFlow.HierPaths.LayoutEncode

/-!
# Storing a routed walk for a child

Read the raw walk from the router's offset table. Shortcut it into the child
walk arena, put its new length before the edge numbers, and return the next
slot. The slot reserves space for the raw length. The position array can be
reused because the shortcut restores it.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The prefix length of the raw walks in one router reply. -/
def routedWalkOffset (emb : ℕ → List ℕ) (i : ℕ) : ℕ :=
  ((List.range i).map fun j => (emb j).length).sum

/-- The base of raw walk `i` in the router's walk table. -/
def routedWalkBase (base n : ℕ) (emb : ℕ → List ℕ) (i : ℕ) : ℕ :=
  base + (n + 1) + routedWalkOffset emb i

/-- Args are `[walkTable, walkCount, i, sourceCell, ends, verts, positions, out]`. -/
def buildStoreWalkProc (fPath : ℕ) : Stmt :=
  .seq (.assign 8 (.bin .add (.reg 0) (.reg 2)))
    (.seq (.assign 9 (.load (.reg 8)))
      (.seq (.assign 10 (.bin .sub (.load (.bin .add (.reg 8) (.const 1))) (.reg 9)))
        (.seq (.call 11 fPath [
            .bin .add (.bin .add (.reg 0) (.bin .add (.reg 1) (.const 1))) (.reg 9),
            .reg 10, .load (.reg 3), .reg 4, .reg 5, .reg 6, .bin .add (.reg 7) (.const 1)])
          (.seq (.store (.reg 7) (.reg 11))
            (.ret (.bin .add (.bin .add (.reg 7) (.const 1)) (.reg 10)))))))

theorem buildStoreWalkProc_noRand (fPath : ℕ) : (buildStoreWalkProc fPath).NoRand := by
  simp [buildStoreWalkProc, Stmt.NoRand]

/-- Store one walk. The input edge and vertex data and the reusable position array
are kept; the output has a length prefix followed by the shortcut edges. -/
def buildStoreWalkContract (w : ℕ) (E : List (ℕ × ℕ)) (u : ℕ) (emb : ℕ → List ℕ)
    (n i : ℕ) : Contract where
  pre args mem := ∃ tb src ends vs P out, args = [tb, n, i, src, ends, vs, P, out] ∧
    i < n ∧ tb + (n + 1) ≤ vs ∧ src < vs ∧ mem src = u ∧ vs + (emb i).length + 1 ≤ out ∧
    ListAt mem tb (csrList n emb) ∧
    PathPre w E u (emb i) mem (routedWalkBase tb n emb i) (emb i).length ends vs P (out + 1)
  post args mem v mem' := ∃ tb src ends vs P out, args = [tb, n, i, src, ends, vs, P, out] ∧
    v = out + 1 + (emb i).length ∧ SeqAt mem' out (erase E u (emb i)) ∧
    ∀ j, (j < vs ∨ (vs + (emb i).length + 1 ≤ j ∧ j < out) ∨ v ≤ j) → mem' j = mem j
  cost _ _ := 136 * (emb i).length + 290

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Store the shortcut of the indexed routed walk in one reserved slot. -/
theorem buildStoreWalkProc_meetsContract {w : ℕ} {E : List (ℕ × ℕ)} {u n i : ℕ}
    {emb : ℕ → List ℕ} {p : Program} {f fPath : ℕ}
    (hf : p.procs[f]? = some (buildStoreWalkProc fPath))
    (hPath : MeetsContract w p fPath (pathContract w E u (emb i))) :
    MeetsContract w p f (buildStoreWalkContract w E u emb n i) := by
  refine meetsContract_of_runs hf fun args mem pos ω hWords hPre => ?_
  obtain ⟨tb, src, ends, vs, P, out, rfl, hi, hTable, hSrc, hu, hVs, hAt, hPathPre⟩ := hPre
  let wk := emb i
  let len := wk.length
  let off := routedWalkOffset emb i
  let ws := routedWalkBase tb n emb i
  let top := out + 1 + len
  have hEnd : top < 2 ^ w := hPathPre.out_lt
  have hw := hPathPre.verts.hw
  have hWs := hPathPre.verts.ws_lt
  change ws + len ≤ vs at hWs
  have hRegN : n + 1 < 2 ^ w := by omega
  have hWordOut : out + 1 < 2 ^ w := by omega
  have hWordCur : tb + i < 2 ^ w := by omega
  have hWordNext : tb + i + 1 < 2 ^ w := by omega
  have hTb : tb + (n + 1) < 2 ^ w := by omega
  have hWsw : tb + (n + 1) + off < 2 ^ w := by change tb + (n + 1) + off + len ≤ vs at hWs; omega
  have hLw : len < 2 ^ w := by omega
  have hCur : mem (tb + i) = off := csrList_offset hAt hi.le
  have hNext : mem (tb + i + 1) = off + len := by
    rw [Nat.add_assoc, csrList_offset hAt (Nat.succ_le_of_lt hi)]
    simp [List.range_succ, off, routedWalkOffset, len, wk]
  refine runs_start_le ?_
  unfold buildStoreWalkProc
  refine runs_seq_assign_le (v := tb + i) ?_ ?_
  · simp [Expr.eval, startState, hWordCur]
  refine runs_seq_assign_le (v := off) ?_ ?_
  · simp [Expr.eval, Function.update, startState, hCur]
  refine runs_seq_assign_le (v := len) ?_ ?_
  · simp [Expr.eval, Function.update, startState, hw, hWordNext, hNext, hLw]
  refine runs_seq_call_le hPath (vs := [ws, len, u, ends, vs, P, out + 1]) ?_ ?_
    ⟨ws, len, ends, vs, P, out + 1, rfl, hPathPre⟩ ?_
  · simp [evalArgs, Expr.eval, Function.update, startState, hw, hRegN, hTb, hWsw, hWordOut, hu,
      ws, routedWalkBase, off]
  · have hU := hPathPre.u_lt
    have hEnds := hPathPre.ends_lt
    have hP : P < 2 ^ w := by
      have hu' : u ∈ walkVerts E u wk := by cases wk <;> simp [walkVerts]
      have hp := hPathPre.P_lt u hu'
      omega
    wram_words
  intro v mem' pos' hReply
  obtain ⟨_, _, _, _, _, _, hEq, hv, hOut, hFrame⟩ := hReply
  simp only [List.cons.injEq, and_true, true_and] at hEq
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hEq
  refine runs_seq_store_le (x := out) (v := v) ?_ ?_ ?_
  · simp [Expr.eval, Function.update, startState]
  · simp [Expr.eval, Function.update]
  refine runs_ret_le (v := top) ?_ ?_ ?_
  · simp [Expr.eval, Function.update, startState, hw, hWordOut, hEnd, top]
  · refine ⟨tb, src, ends, vs, P, out, rfl, rfl, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · change Function.update mem' out v out = _
        rw [Function.update_self, hv]
      · intro j hj
        change Function.update mem' out v (out + 1 + j) = _
        rw [Function.update_of_ne (by omega), hOut j (hv.symm ▸ hj), List.getD_eq_getElem _ _ hj]
    · intro j hj
      change j < vs ∨ (vs + len + 1 ≤ j ∧ j < out) ∨ top ≤ j at hj
      change ∀ x, (x < vs ∨ (vs + len + 1 ≤ x ∧ x < out + 1) ∨ top ≤ x) →
        mem' x = mem x at hFrame
      change vs + len + 1 ≤ out at hVs
      change Function.update mem' out v j = mem j
      have hne : j ≠ out := by dsimp [top] at hj; omega
      rw [Function.update_of_ne hne]
      exact hFrame _ (by dsimp [top] at hj; omega)
  · simp [buildStoreWalkContract, pathContract, argsSize, Expr.size, len, wk]
    omega

end MinCostFlow.HierPaths
