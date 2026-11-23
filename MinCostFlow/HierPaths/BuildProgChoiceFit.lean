module

public import MinCostFlow.HierPaths.BuildProgChoiceNext

/-!
# Memory invariant for the certified game loop

The input graph, compact tables, and original child slots survive each
executed round. Skipped rounds leave the heap and the memory unchanged.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

/-- The graph memory invariant holds throughout the certified loop. -/
theorem ChoiceLoopTrace.memory {w tailBudget : ℕ} {D : ChoiceLoopData} {β : ℝ} {bh : ℕ}
    {initial mem : ℕ → ℕ} {t heap : ℕ} {sts : ℕ → ChildState}
    (hTrace : ChoiceLoopTrace w D initial t heap sts mem) (ht : t ≤ D.limit)
    (h : ChoiceGameHyp D β bh) (hL : GameFixedLayout w D.geometry)
    (hInit : ChoiceGameMemory D D.addrs.heap (fun _ => ChildState.init) initial)
    (hRoom : ∀ t heap sts mem, t < D.limit →
      ChoiceLoopTrace w D initial t heap sts mem → (D.round sts).jobs.count ≠ 0 →
      ChoiceRoundBudget w tailBudget D heap sts) :
    ChoiceGameMemory D heap sts mem := by
  induction hTrace with
  | start => exact hInit
  | skip _ _ ih => exact ih (Nat.le_of_succ_le ht)
  | run hTrace hn ans bump rBump hCert hBump hRBump hPost ih =>
    exact choiceGameMemory_next h hL (ih (Nat.le_of_succ_le ht)) ht hTrace
      (hRoom _ _ _ _ ht hTrace hn) hn hCert hBump hRBump hPost

/-- The loop needs only the numeric budgets in addition to its initial graph layout.
Its step precondition and stopping rule follow from the certified trace. -/
theorem choiceLoopFit_of_initial {w tailBudget stepBudget : ℕ} {D : ChoiceLoopData}
    {β : ℝ} {bh : ℕ} {initial : ℕ → ℕ}
    (h : ChoiceGameHyp D β bh) (hL : GameFixedLayout w D.geometry)
    (hInit : ChoiceGameMemory D D.addrs.heap (fun _ => ChildState.init) initial)
    (hDirectory : D.directory + D.limit < 2^w) (hBudget : 3 ≤ stepBudget)
    (hWords : ∀ t heap sts mem, t < D.limit → ChoiceLoopTrace w D initial t heap sts mem →
      ∀ a ∈ D.args heap sts, a < 2^w)
    (hRoom : ∀ t heap sts mem, t < D.limit →
      ChoiceLoopTrace w D initial t heap sts mem → (D.round sts).jobs.count ≠ 0 →
      ChoiceRoundBudget w tailBudget D heap sts)
    (hStepCost : ∀ t heap sts mem, t < D.limit → ChoiceLoopTrace w D initial t heap sts mem →
      (D.round sts).jobs.count ≠ 0 →
      let B := D.round sts
      let A := D.atHeap heap
      (buildStepChoiceContract w tailBudget B A D.first D.saved (D.active sts)).cost
        (B.stepArgs A D.first D.saved) mem + 60 ≤ stepBudget) :
    ChoiceLoopFit w tailBudget stepBudget D initial := by
  have hDir : D.directory + D.limit ≤ D.saved := hL.directory
  have hSaved : D.saved + D.count ≤ D.addrs.graphs := hL.saved
  have hGraph : D.addrs.graphs + D.count ≤ D.addrs.offsets := hL.graphs
  have hOff : D.addrs.offsets + D.count ≤ D.addrs.replies := hL.offsets
  refine ⟨hL.bits,hDirectory,by omega,hWords,?_,hStepCost,hBudget,?_⟩
  · intro t heap sts mem ht hTrace hn
    exact choiceStep_pre_of_memory h hL (hTrace.memory ht.le h hL hInit hRoom)
      ht hTrace (hRoom t heap sts mem ht hTrace hn) (Nat.pos_of_ne_zero hn)
  · intro heap sts mem hTrace
    exact hTrace.done h.router h.host h.positive h.expansion h.denominator h.children
      h.even (coreLevel_le h.coreSize) h.sizeLog

end MinCostFlow.HierPaths
