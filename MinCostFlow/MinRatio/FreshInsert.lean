module

public import MinCostFlow.Chain.Algorithm2
public import MinCostFlow.IPM.Machine.Layout
import WordRAM.Memory
import WordRAM.Tactic

/-!
# Translating an insertion to a fresh internal name

Algorithm 2 sends graph updates to the tree chain (page 29). On an
insertion the name translation assigns the next fresh name to the edge.
The program updates both maps, advances the counter, and writes the
translated insertion with the original endpoints. Its memory changes
match the two function updates in `translateUpdate`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM IPM.Machine

/-- Arguments are the external edge, its two endpoints, the two table
bases, the fresh-counter address, and the heap. -/
def freshInsertBody : Stmt :=
  .assign 7 (.load (.reg 5)) ;;
  .store (.bin .add (.reg 3) (.reg 0)) (.reg 7) ;;
  .store (.bin .add (.reg 4) (.reg 7)) (.reg 0) ;;
  .store (.reg 5) (.bin .add (.reg 7) (.const 1)) ;;
  .store (.reg 6) (.const 0) ;;
  .store (.bin .add (.reg 6) (.const 1)) (.reg 7) ;;
  .store (.bin .add (.reg 6) (.const 2)) (.reg 1) ;;
  .store (.bin .add (.reg 6) (.const 3)) (.reg 2) ;;
  .ret (.bin .add (.reg 6) (.const 4))

/-- The three mutable cells below the heap are the forward entry, inverse
entry, and fresh counter. The four output cells are newly allocated. -/
def freshInsertContract (w e u v next : ℕ) : Contract where
  pre args mem := ∃ forward inverse counter heap,
    args = [e, u, v, forward, inverse, counter, heap] ∧
    mem counter = next ∧ next + 1 < 2 ^ w ∧ heap + 4 < 2 ^ w ∧
    forward + e < heap ∧ inverse + next < heap ∧ counter < heap ∧
    forward + e ≠ inverse + next ∧ forward + e ≠ counter ∧ inverse + next ≠ counter ∧
    ZeroFrom mem heap
  post args mem ret mem' := ∃ forward inverse counter heap,
    args = [e, u, v, forward, inverse, counter, heap] ∧ ret = heap + 4 ∧
    mem' (forward + e) = next ∧ mem' (inverse + next) = e ∧ mem' counter = next + 1 ∧
    ListAt mem' heap (updateWords (.insert next u v)) ∧
    (∀ a < heap, a ≠ forward + e → a ≠ inverse + next → a ≠ counter → mem' a = mem a) ∧
    ZeroFrom mem' ret
  cost _ _ := 64

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM IPM.Machine Chain

/-- The insertion translation is deterministic. -/
theorem freshInsertBody_noRand : freshInsertBody.NoRand := by
  simp [freshInsertBody, Stmt.NoRand]

/-- The fresh-name insertion costs at most 64 steps and uses four new cells. -/
theorem freshInsert_meetsContract {w base e u v next : ℕ} {p : Program}
    (hp : p.HasAt base [freshInsertBody]) :
    MeetsContract w p base (freshInsertContract w e u v next) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨fwd, inv, counter, heap, rfl, hread, hnext, hroom, hf, hi, hctr, hfi, hfc, hic, hz⟩ := hpre
  have hfWord : fwd + e < 2 ^ w := by omega
  have hiWord : inv + next < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have h2 : 2 < 2 ^ w := by omega
  have h3 : 3 < 2 ^ w := by omega
  have h4 : 4 < 2 ^ w := by omega
  have hheap1 : heap + 1 < 2 ^ w := by omega
  have hheap2 : heap + 2 < 2 ^ w := by omega
  have hheap3 : heap + 3 < 2 ^ w := by omega
  apply runs_start_le
  unfold freshInsertBody
  refine runs_seq_assign_le (v := next) (by eval_expr) ?_
  wram_run
  · refine ⟨fwd, inv, counter, heap, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp (disch := omega)
    · simp (disch := omega)
    · simp (disch := omega)
    · intro i hi'
      have hit : i < 4 := by simpa [updateWords] using hi'
      interval_cases i <;> simp (disch := omega) [updateWords]
    · intro a ha haf hai hac
      simp (disch := omega) [startState]
    · intro a ha
      change heap + 4 ≤ a at ha
      simp (disch := omega) [startState, hz a (by omega)]
  · simp only [freshInsertContract]
    wram_cost

/-- The inserted record is the exact record selected by the model. -/
theorem freshInsert_model {w e u v fwd inv counter heap ret next : ℕ} {G : MGraph}
    {e2i i2e : ℕ → ℕ} {mem mem' : ℕ → ℕ}
    (hout : (freshInsertContract w e u v next).post [e, u, v, fwd, inv, counter, heap] mem ret mem') :
    ListAt mem' heap (updateWords (translateUpdate G e2i i2e next (.insert e u v)).2.2.2.2) := by
  obtain ⟨fwd', inv', ctr', heap', hargs, _, _, _, _, hrecord, _, _⟩ := hout
  have hh : heap = heap' := congrArg (fun l : List ℕ => l.getD 6 0) hargs
  subst heap'
  exact hrecord

end MinCostFlow.MinRatio
