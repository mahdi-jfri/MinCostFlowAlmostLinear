module

public import MinCostFlow.HierPaths.BuildProgApplyBatch
import MinCostFlow.HierPaths.QueryProgRoute

/-!
# Applying a matched router reply

The reply names the matching and walk tables. Read both table bases, reserve
one walk-directory word per matched edge and set the reusable scratch bounds.
Then apply the whole batch.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

/-- Args are `[reply, cuts, graphTable, offsetTable, ends, hostSize, pathBound, heap, rows]`. -/
def buildFinishBatchProc (fApply : ℕ) : Stmt :=
  .seq (.assign 9 (.bin .add (.reg 0) (.const 4)))
    (.seq (.assign 10 (.bin .add (.reg 9) (.load (.bin .add (.reg 0) (.const 1)))))
      (.seq (.assign 11 (.bin .add (.reg 9) (.load (.bin .add (.reg 0) (.const 2)))))
        (.seq (.assign 12 (.bin .add (.reg 7) (.const 4)))
          (.seq (.assign 13 (.bin .add (.reg 12)
              (.bin .div (.load (.bin .add (.reg 10) (.reg 8))) (.const 2))))
            (.seq (.assign 14 (.bin .add (.bin .add (.reg 13) (.reg 6)) (.const 1)))
              (.seq (.call 15 fApply [.reg 10, .reg 11, .reg 8, .reg 1, .reg 2, .reg 3, .reg 7, .reg 4,
                  .reg 13, .reg 14, .reg 12, .bin .add (.reg 14) (.reg 5)])
                (.ret (.reg 15))))))))

theorem buildFinishBatchProc_noRand (fApply : ℕ) : (buildFinishBatchProc fApply).NoRand := by
  simp [buildFinishBatchProc, Stmt.NoRand]

/-- Where the matched reply places the two inner tables. -/
def matchedTableBases (mem : ℕ → ℕ) (rep : ℕ) : ℕ × ℕ :=
  (rep + 4 + mem (rep + 1), rep + 4 + mem (rep + 2))

/-- The arguments computed for the matching-application scan. -/
def finishBatchApplyArgs (D : ApplyBatchData) (mt tb cuts graphs offsets ends cap heap : ℕ) : List ℕ :=
  let dir := heap + 4
  let vs := dir + D.matchings.flatten.length
  let P := vs + cap + 1
  [mt, tb, D.matchings.length, cuts, graphs, offsets, heap, ends, vs, P, dir, P + D.host.n]

/-- The router reply and scratch ranges fit the application scan. -/
def buildFinishBatchContract (w : ℕ) (D : ApplyBatchData) : Contract where
  pre args mem := ∃ rep cuts graphs offsets ends cap heap,
    args = [rep, cuts, graphs, offsets, ends, D.host.n, cap, heap, D.matchings.length] ∧
    ListAt mem rep (routeResultWords (.matched D.matchings D.emb)) ∧
    rep + (routeResultWords (.matched D.matchings D.emb)).length ≤ heap ∧
    heap + 4 + D.matchings.flatten.length + cap + 1 + D.host.n < 2 ^ w ∧
    (buildApplyBatchContract w D).pre
      (finishBatchApplyArgs D (matchedTableBases mem rep).1 (matchedTableBases mem rep).2
        cuts graphs offsets ends cap heap) mem
  post args mem v mem' := ∃ rep cuts graphs offsets ends cap heap,
    args = [rep, cuts, graphs, offsets, ends, D.host.n, cap, heap, D.matchings.length] ∧
    (buildApplyBatchContract w D).post
      (finishBatchApplyArgs D (matchedTableBases mem rep).1 (matchedTableBases mem rep).2
        cuts graphs offsets ends cap heap) mem v mem'
  cost _ _ := rangeCost (applyBatchStepCost D) 0 D.matchings.length + 9 * D.matchings.length + 112

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

/-- Both inner tables end within the matched reply. -/
theorem matchedTables_end_le {mem : ℕ → ℕ} {rep heap : ℕ}
    {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (hAt : ListAt mem rep (routeResultWords (.matched Ms emb)))
    (hFit : rep + (routeResultWords (.matched Ms emb)).length ≤ heap) :
    (matchedTableBases mem rep).1 + (csrList Ms.length (matchingRowWords Ms)).length ≤ heap ∧
      (matchedTableBases mem rep).2 + (csrList Ms.flatten.length emb).length ≤ heap := by
  let sections := [[0], csrList Ms.length (matchingRowWords Ms), csrList Ms.flatten.length emb]
  change ListAt mem rep (layoutList sections) at hAt
  change rep + (layoutList sections).length ≤ heap at hFit
  have h1 : 1 < sections.length := by simp [sections]
  have h2 : 2 < sections.length := by simp [sections]
  have e1 := csr_end_le sections.length (fun i => sections.getD i []) h1
  have e2 := csr_end_le sections.length (fun i => sections.getD i []) h2
  have h1v := csrList_offset hAt h1.le
  have h2v := csrList_offset hAt h2.le
  change 4 + ((List.range 1).map fun j => (sections.getD j []).length).sum +
    (csrList Ms.length (matchingRowWords Ms)).length ≤ (layoutList sections).length at e1
  change 4 + ((List.range 2).map fun j => (sections.getD j []).length).sum +
    (csrList Ms.flatten.length emb).length ≤ (layoutList sections).length at e2
  unfold matchedTableBases
  dsimp only
  rw [h1v, h2v]
  omega

private theorem matchedBases_lt {mem : ℕ → ℕ} {rep heap : ℕ}
    {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (hAt : ListAt mem rep (routeResultWords (.matched Ms emb)))
    (hFit : rep + (routeResultWords (.matched Ms emb)).length ≤ heap) :
    (matchedTableBases mem rep).1 + Ms.length < heap ∧
      (matchedTableBases mem rep).2 < heap := by
  obtain ⟨h1, h2⟩ := matchedTables_end_le hAt hFit
  have hl1 : Ms.length < (csrList Ms.length (matchingRowWords Ms)).length := by simp [csrList]; omega
  have hl2 : 0 < (csrList Ms.flatten.length emb).length := by simp [csrList]
  omega

/-- Decode the reply and run the verified row-application scan. -/
theorem buildFinishBatchProc_meetsContract {w f fApply : ℕ} {D : ApplyBatchData} {p : Program}
    (hf : p.procs[f]? = some (buildFinishBatchProc fApply))
    (hApply : MeetsContract w p fApply (buildApplyBatchContract w D)) :
    MeetsContract w p f (buildFinishBatchContract w D) := by
  refine meetsContract_of_runs hf fun args mem pos ω hWords hPre => ?_
  obtain ⟨rep,cuts,graphs,offsets,ends,cap,heap,rfl,hReply,hHeap,hFit,hPre⟩ := hPre
  let mt := (matchedTableBases mem rep).1
  let tb := (matchedTableBases mem rep).2
  let dir := heap + 4
  let vs := dir + D.matchings.flatten.length
  let P := vs + cap + 1
  let top := P + D.host.n
  have hTop : top < 2 ^ w := hFit
  obtain ⟨hm, ht⟩ := matchedBases_lt hReply hHeap
  change mt + D.matchings.length < heap at hm
  change tb < heap at ht
  have hAt := (routeMatched_view hReply).1
  have hK := csrList_offset hAt (le_refl D.matchings.length)
  have hCount : mem (mt + D.matchings.length) = 2 * D.matchings.flatten.length := by
    by_cases hk : D.matchings.length = 0
    · have hMs := List.length_eq_zero_iff.mp hk
      simp only [hMs, List.length_nil, List.flatten_nil, Nat.mul_zero, Nat.add_zero]
      simpa only [hMs, List.length_nil, List.range_zero, List.map_nil, List.sum_nil, Nat.add_zero,
        mt, matchedTableBases] using hK
    · have hk0 : 0 < D.matchings.length := Nat.pos_of_ne_zero hk
      exact (matchingRow_view hk0 hAt).2.2.1
  have hRep4 : rep + 4 ≤ mt := Nat.le_add_right _ _
  have hR4W : rep + 4 < 2 ^ w := by omega
  have hR1W : rep + 1 < 2 ^ w := by omega
  have hR2W : rep + 2 < 2 ^ w := by omega
  have h4 : 4 < 2 ^ w := by dsimp [top, P, vs, dir] at hTop; omega
  have h2 : 2 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have hmW : rep + 4 + mem (rep + 1) < 2 ^ w := by change mt < _; omega
  have htW : rep + 4 + mem (rep + 2) < 2 ^ w := by change tb < _; omega
  have hHdrW : mt + D.matchings.length < 2 ^ w := by omega
  have hdW : heap + 4 < 2 ^ w := by dsimp [top, P, vs, dir] at hTop; omega
  have hvW : dir + D.matchings.flatten.length < 2 ^ w := by change vs < _; dsimp [top, P] at hTop; omega
  have hVsW : vs < 2 ^ w := hvW
  have hvpW : vs + cap < 2 ^ w := by dsimp [top, P] at hTop; omega
  have hP : vs + cap + 1 < 2 ^ w := by dsimp [top, P] at hTop; omega
  refine runs_start_le ?_
  unfold buildFinishBatchProc
  refine runs_seq_assign_le (v := rep + 4) ?_ ?_
  · simp [Expr.eval, startState, h4, hR4W]
  refine runs_seq_assign_le (v := mt) ?_ ?_
  · simp [Expr.eval, startState, Function.update, h1, hR1W, hmW, mt, matchedTableBases]
  refine runs_seq_assign_le (v := tb) ?_ ?_
  · simp [Expr.eval, startState, Function.update, h2, hR2W, htW, tb, matchedTableBases]
  refine runs_seq_assign_le (v := dir) ?_ ?_
  · simp [Expr.eval, startState, Function.update, h4, hdW, dir]
  refine runs_seq_assign_le (v := vs) ?_ ?_
  · have hLen : D.matchings.flatten.length < 2 ^ w := by omega
    simp only [List.length_flatten] at hvW hLen
    simp [Expr.eval, startState, Function.update, h2, hHdrW, hCount, hvW, hLen, vs]
  refine runs_seq_assign_le (v := P) ?_ ?_
  · simp [Expr.eval, startState, Function.update, h1, hvpW, hP, P]
  refine runs_seq_call_le hApply (vs := [mt,tb,D.matchings.length,cuts,graphs,offsets,heap,ends,vs,P,dir,top]) ?_ ?_
    hPre ?_
  · have hup : P + D.host.n < 2 ^ w := hTop
    simp [evalArgs, Expr.eval, startState, Function.update, hup, top]
  · have ha := hWords cuts (by simp)
    have hb := hWords graphs (by simp)
    have hc := hWords offsets (by simp)
    have he := hWords ends (by simp)
    have hk := hWords D.matchings.length (by simp)
    have hMtW : mt < 2 ^ w := by omega
    have hTbW : tb < 2 ^ w := by omega
    have hHeapW : heap < 2 ^ w := hWords _ (by simp)
    have hPosW : P < 2 ^ w := hP
    have hDirW : dir < 2 ^ w := hdW
    wram_words
  intro v mem' pos' hPost
  refine runs_ret_le (v := v) (Expr.eval_reg_of_eq (by simp)) ?_ ?_
  · exact ⟨rep,cuts,graphs,offsets,ends,cap,heap,rfl,hPost⟩
  · simp [buildFinishBatchContract, buildApplyBatchContract, Expr.size, argsSize]
    omega

end MinCostFlow.HierPaths
