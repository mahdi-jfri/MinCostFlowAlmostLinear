module

public import MinCostFlow.MinRatio.FreshBatchBody
import WordRAM.Tactic

/-!
# Refresh batches with their count headers

The batch entry reads the count, passes the two body pointers to the
verified fresh-name scan, and writes the original count at the output.
The model preserves the number of updates. This produces the exact
shared batch layout and the name tables after Algorithm 2's translation.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM IPM.Machine Chain

/-- Arguments are the count-prefixed input, map bases, counter address,
and old heap. The scan receives pointers just past the two headers. -/
def freshBatchEntry (scan : ℕ) : Stmt :=
  .assign 5 (.load (.reg 0)) ;;
  .call 6 scan [.bin .add (.reg 0) (.const 1), .reg 1, .reg 2, .reg 3,
    .bin .add (.reg 4) (.const 1), .reg 5] ;;
  .store (.reg 4) (.reg 5) ;;
  .ret (.reg 6)

/-- The batch entry returns the model translation in the IPM batch layout,
with the model's final name maps and next fresh name. -/
def freshBatchEntryContract (w : ℕ) (r : FreshBatchRegions) (G H : MGraph)
    (f g : ℕ → ℕ) (next : ℕ) (updates : List Update) : Contract where
  pre args mem :=
    ∃ src heap, args = [src, r.forward, r.inverse, r.counter, heap] ∧
      r.input = src + 1 ∧ r.output = heap + 1 ∧ r.input ≤ heap ∧ BatchAt mem src updates ∧
      FreshBatchInput w r G H f g next updates mem
  post args mem ret mem' :=
    let target := translateBatch G f g next updates
    BatchAt mem' (args.getD 4 0) target.2.2.2.2 ∧
      FreshTablesAt mem' r.forward r.inverse r.counter r.externalCap r.internalCap
        target.2.1 target.2.2.1 target.2.2.2.1 ∧
      ret = (args.getD 4 0) + (batchWords target.2.2.2.2).length ∧ ZeroFrom mem' ret ∧
      ∀ a < args.getD 4 0, ¬ r.mutable a → mem' a = mem a
  cost _ _ := 162 * updates.length + 32

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM IPM.Machine Chain

/-- The batch entry has no random instruction. -/
theorem freshBatchEntry_noRand (scan : ℕ) : (freshBatchEntry scan).NoRand := by
  simp [freshBatchEntry, Stmt.NoRand]

/-- The count-prefixed translator meets the exact batch contract in at
most `162 * updates.length + 32` steps. -/
theorem freshBatchEntry_meetsContract {w base scan : ℕ} {p : Program}
    (r : FreshBatchRegions) (G H : MGraph) (f g : ℕ → ℕ) (next : ℕ) (updates : List Update)
    (hp : p.HasAt base [freshBatchEntry scan])
    (hscan : MeetsContract w p scan (freshBatchBodyContract w r G H f g next updates)) :
    MeetsContract w p base (freshBatchEntryContract w r G H f g next updates) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨src, heap, rfl, hinput, houtput, hinputHeap, hbatch, hpre⟩ := hpre
  rcases hpre with ⟨hsep, hfresh, hvalid, htables, hrec, hbits, hnames, hsrcEnd, houtEnd, hlen,
    hinputWords, hzero⟩
  have hc : mem src = updates.length := by
    simpa only [batchWords, List.getElem_cons_zero, Nat.add_zero] using
      hbatch 0 (by simp [batchWords])
  have houtWord : r.output < 2 ^ w := by omega
  have hinWord : r.input < 2 ^ w := by omega
  have h1w : 1 < 2 ^ w := by omega
  have hfwd := hwords r.forward (by simp)
  have hinv := hwords r.inverse (by simp)
  have hctr := hwords r.counter (by simp)
  have hcallWords : ∀ x ∈ [r.input, r.forward, r.inverse, r.counter, r.output, updates.length], x < 2 ^ w := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hinWord, hfwd, hinv, hctr, houtWord, hlen⟩
  have hcallPre : (freshBatchBodyContract w r G H f g next updates).pre
      [r.input, r.forward, r.inverse, r.counter, r.output, updates.length] mem :=
    ⟨rfl, hsep, hfresh, hvalid, htables, hrec, hbits, hnames, hsrcEnd, houtEnd, hlen, hinputWords, hzero⟩
  have hcount := (translateBatch_preserves updates G H f g next hfresh hvalid).2.2.2.2.1
  apply runs_start_le
  unfold freshBatchEntry
  refine runs_seq_assign_le (v := updates.length) (by eval_expr) ?_
  refine runs_seq_call_le hscan
    (vs := [r.input, r.forward, r.inverse, r.counter, r.output, updates.length])
    ?_ hcallWords hcallPre ?_
  · rw [hinput, houtput]
    eval_expr
  · intro ret mem' pos' hs
    rcases hs with ⟨hlist', htable', hre, hz, hframe⟩
    have hheapRet : heap < ret := by rw [hre, houtput]; omega
    rcases hsep with ⟨hf, hi, hcounter, _⟩
    refine runs_seq_store_le (x := heap) (v := updates.length) (by eval_expr) (by eval_expr) ?_
    refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
    · change BatchAt (Function.update mem' heap updates.length) heap
          (translateBatch G f g next updates).2.2.2.2 ∧ _ ∧ _ ∧ _ ∧ _
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · apply listAt_cons.mpr
        refine ⟨?_, ?_⟩
        · rw [Function.update_self]
          exact hcount.symm
        · rw [← houtput]
          intro i hi'
          rw [Function.update_of_ne (show r.output + i ≠ heap by omega)]
          exact hlist' i hi'
      · dsimp only
        refine ⟨?_, ?_, ?_⟩
        · rw [Function.update_of_ne (show r.counter ≠ heap by omega)]
          exact htable'.1
        · intro e he
          rw [Function.update_of_ne (show r.forward + e ≠ heap by omega)]
          exact htable'.2.1 e he
        · intro e he
          rw [Function.update_of_ne (show r.inverse + e ≠ heap by omega)]
          exact htable'.2.2 e he
      · change ret = heap + (batchWords (translateBatch G f g next updates).2.2.2.2).length
        rw [hre, houtput]
        simp only [batchWords, List.length_cons]
        omega
      · exact hz.update_lt hheapRet
      · intro a ha hmut
        change a < heap at ha
        change Function.update mem' heap updates.length a = mem a
        rw [Function.update_of_ne (Nat.ne_of_lt ha)]
        exact hframe a (by omega) hmut
    · simp only [freshBatchBodyContract, freshBatchEntryContract, Expr.size_load, Expr.size_reg,
        Expr.size_bin, Expr.size_const, argsSize_cons, argsSize_nil]
      omega

end MinCostFlow.MinRatio

public section

namespace MinCostFlow.MinRatio

open WordRAM IPM.Machine Chain

/-- The complete batch entry uses the in-program scan and record bodies.
Its correctness and cost require only the placements of those bodies. -/
theorem freshBatchEntry_meetsContract_of_placement {w base scan dispatch ins del : ℕ} {p : Program}
    (r : FreshBatchRegions) (G H : MGraph) (f g : ℕ → ℕ) (next : ℕ) (updates : List Update)
    (hp : p.HasAt base [freshBatchEntry scan])
    (hs : p.HasAt scan [freshBatchBody dispatch])
    (hd : p.HasAt dispatch [freshRecordBody ins del])
    (hi : p.HasAt ins [freshInsertBody]) (he : p.HasAt del [freshDeleteBody]) :
    MeetsContract w p base (freshBatchEntryContract w r G H f g next updates) :=
  freshBatchEntry_meetsContract r G H f g next updates hp
    (freshBatchBody_meetsContract r G H f g next updates hs hd hi he)

end MinCostFlow.MinRatio
