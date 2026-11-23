module

public import MinCostFlow.MinRatio.FreshBatchCompact
public import MinCostFlow.IPM.Machine.MinRatioContract
import WordRAM.Memory

/-!
# The IPM refresh supplies the translator's input records

The IPM's use of Definition 4.5 (page 14) refreshes a fixed graph by
deleting and reinserting live external names. The batch precondition
already gives valid records and bounds on their words. This file
combines those facts with the current name tables and available
memory to prepare the exact Algorithm 2 translator call.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain IPM.Machine

/-- Every IPM refresh record is a deletion or insertion with an external
name inside the allocated table. -/
theorem refreshBatch_recordFits {G : MGraph} {U : List Update} {cap : ℕ}
    (hU : RefreshBatch G U) (hcap : ∀ e ∈ G.E, e < cap) :
    ∀ u ∈ U, FreshRecordFits cap u := by
  intro u hu
  have h := hU.2.2 u hu
  cases u with
  | split _ _ _ => exact h
  | delete e => exact hcap e h
  | insert e _ _ => exact hcap e h.1

/-- The actual IPM batch layout gives the translator precondition when
the caller supplies disjoint tables, fresh slots, and output space. -/
theorem freshBatchEntry_pre_of_refresh {w src heap next : ℕ} {r : FreshBatchRegions}
    {G H : MGraph} {f g : ℕ → ℕ} {U : List Update} {mem : ℕ → ℕ}
    (hinput : r.input = src + 1) (houtput : r.output = heap + 1)
    (hsep : r.Separated) (hfresh : FreshInv G H f g next)
    (ht : FreshTablesAt mem r.forward r.inverse r.counter r.externalCap r.internalCap f g next)
    (hU : RefreshBatch G U) (hcap : ∀ e ∈ G.E, e < r.externalCap)
    (hbatch : BatchAt mem src U) (hwords : ∀ x ∈ batchWords U, x < 2 ^ w)
    (hslots : next + U.length ≤ r.internalCap)
    (hsrcEnd : src + (batchWords U).length ≤ heap)
    (hheapEnd : heap + (batchWords U).length < 2 ^ w)
    (hz : ZeroFrom mem heap) :
    (freshBatchEntryContract w r G H f g next U).pre
      [src, r.forward, r.inverse, r.counter, heap] mem := by
  have hlen : (batchWords U).length = (U.flatMap updateWords).length + 1 := rfl
  have hroom : r.output + (U.flatMap updateWords).length < 2 ^ w := by omega
  have hl : U.length < 2 ^ w := hwords _ (by simp [batchWords])
  have hbody := (listAt_cons.mp hbatch).2
  rw [← hinput] at hbody
  refine ⟨src, heap, rfl, hinput, houtput, by omega, hbatch, hsep, hfresh, hU.1, ht,
    refreshBatch_recordFits hU hcap, ?_, hslots, by omega, hroom, hl, hbody, ?_⟩
  · intro x hx
    apply hwords
    exact List.mem_cons_of_mem _ hx
  · apply hz.mono
    omega

end MinCostFlow.MinRatio
