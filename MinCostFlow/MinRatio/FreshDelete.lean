module

public import MinCostFlow.Chain.Algorithm2
public import MinCostFlow.IPM.Machine.Layout
import WordRAM.Memory
import WordRAM.Tactic

/-!
# Translating a deletion to its current internal name

Algorithm 2 (page 29) sends an update batch to the tree chain. The model
assigns fresh internal names on insertion. For a deletion, the program
reads the external edge name, looks up its current internal name, and
writes the translated record. Both name tables and the fresh-name
counter stay unchanged, as in `translateUpdate`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM IPM.Machine

/-- Arguments are the external record, the forward name table and the heap. -/
def freshDeleteBody : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 3 (.load (.bin .add (.reg 1) (.reg 3))) ;;
  .store (.reg 2) (.const 1) ;;
  .store (.bin .add (.reg 2) (.const 1)) (.reg 3) ;;
  .ret (.bin .add (.reg 2) (.const 2))

/-- The lookup preserves old memory and writes a two-word delete record. -/
def freshDeleteContract (w external internal : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ src names heap, args = [src, names, heap] ∧
      src + 2 ≤ heap ∧ names + external < heap ∧ internal < 2 ^ w ∧
      ListAt mem src (updateWords (.delete external)) ∧ mem (names + external) = internal)
    (fun args _ mem' => ListAt mem' (heapArg args) (updateWords (.delete internal)))
    (fun _ _ => 32) (fun _ _ => 2)
  { C with post := fun args mem v mem' => v = heapArg args + 2 ∧ C.post args mem v mem' }

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM IPM.Machine Chain

/-- The deletion translation is deterministic. -/
theorem freshDeleteBody_noRand : freshDeleteBody.NoRand := by
  simp [freshDeleteBody, Stmt.NoRand]

/-- The fresh-name deletion procedure meets its contract with at most
32 word operations and two new words. -/
theorem freshDelete_meetsContract {w base external internal : ℕ} {p : Program}
    (hp : p.HasAt base [freshDeleteBody]) :
    MeetsContract w p base (freshDeleteContract w external internal) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨src, names, heap, rfl, hsrc, hname, hi, hinput, hread⟩, hz, hroom⟩ := hpre
  change heap + 2 < 2 ^ w at hroom
  change ZeroFrom mem heap at hz
  have hword : 2 < 2 ^ w := by omega
  have hsrc' : src + 1 < 2 ^ w := by omega
  have hname' : names + external < 2 ^ w := by omega
  have hheap' : heap + 1 < 2 ^ w := by omega
  have hreadExt : mem (src + 1) = external := hinput 1 (by simp [updateWords])
  apply runs_start_le
  unfold freshDeleteBody
  refine runs_seq_assign_le (v := external) (by eval_expr) ?_
  refine runs_seq_assign_le (v := internal) (by eval_expr) ?_
  wram_run
  · refine ⟨rfl, Nat.le_add_right _ _, le_rfl, ?_, ?_, ?_⟩
    · intro x hx
      change x < heap at hx
      change Function.update (Function.update mem heap 1) (heap + 1) internal x = mem x
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    · intro x hx
      change heap + 2 ≤ x at hx
      change Function.update (Function.update mem heap 1) (heap + 1) internal x = 0
      simpa (disch := omega) [Function.update_of_ne] using hz x (by omega)
    · apply listAt_cons.mpr
      refine ⟨?_, listAt_singleton.mpr ?_⟩
      · change Function.update (Function.update mem heap 1) (heap + 1) internal heap = 1
        simp (disch := omega) [Function.update_of_ne]
      · change Function.update (Function.update mem heap 1) (heap + 1) internal (heap + 1) = internal
        simp
  · simp only [freshDeleteContract, heapContract]
    wram_cost

/-- The deletion output is exactly the singleton update selected by
`translateUpdate`, whose preservation of `FreshInv` is proved in the model. -/
theorem freshDelete_model {w external src names heap ret nf : ℕ}
    {G : MGraph} {e2i i2e : ℕ → ℕ} {mem mem' : ℕ → ℕ}
    (hout : (freshDeleteContract w external (e2i external)).post [src, names, heap] mem ret mem') :
    ListAt mem' heap (updateWords (translateUpdate G e2i i2e nf (.delete external)).2.2.2.2) :=
  hout.2.2.2.2.2

end MinCostFlow.MinRatio
