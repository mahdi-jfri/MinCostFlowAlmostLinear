module

public import MinCostFlow.IPM.Machine.QueryAllocationBound

/-!
# Uniform Update allocation for a target-test epoch

The gradient, length and normalization tables stay at fixed addresses
within an epoch. The actual batch and Update heaps depend on preceding
reported sizes. A finite maximum over those two word-sized addresses
bounds every Update allocation. The machine never computes this
maximum. A supplied uniform DS space bound bounds it without any loss.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine

/-- Maximum Update allocation over its word-sized batch and heap pointers,
with the epoch's other arguments fixed. -/
def updateAllocationBound (w b g l eta : ℕ) (allocation : ℕ → List ℕ → ℕ) : ℕ :=
  (Finset.range (2^w)).sup fun batch =>
    (Finset.range (2^w)).sup fun heap => allocation 0 [b,batch,g,l,eta,heap]

/-- Every actual Update allocation is below the epoch's analysis bound. -/
theorem update_allocation_le_bound {w b g l eta batch heap : ℕ}
    (allocation : ℕ → List ℕ → ℕ) (hb : batch<2^w) (hh : heap<2^w) :
    allocation 0 [b,batch,g,l,eta,heap]≤updateAllocationBound w b g l eta allocation := by
  unfold updateAllocationBound
  exact Finset.le_sup_of_le (Finset.mem_range.mpr hb)
    (Finset.le_sup (f:=fun h => allocation 0 [b,batch,g,l,eta,h]) (Finset.mem_range.mpr hh))

/-- A supplied uniform space bound controls this maximum too, so the
analysis does not insert a word-count factor into the workspace. -/
theorem updateAllocationBound_le {w b g l eta bound : ℕ}
    (allocation : ℕ → List ℕ → ℕ)
    (hbound : ∀ batch<2^w,∀ heap<2^w,allocation 0 [b,batch,g,l,eta,heap]≤bound) :
    updateAllocationBound w b g l eta allocation≤bound := by
  apply Finset.sup_le
  intro batch hb
  apply Finset.sup_le
  intro heap hh
  exact hbound batch (Finset.mem_range.mp hb) heap (Finset.mem_range.mp hh)

/-- One uniform epoch budget supplies the actual argument-dependent
batch/Update allocation premise for any reported-set size. -/
theorem batchUpdate_budget_of_uniform {w b g l eta heap L count : ℕ}
    (allocation : ℕ → List ℕ → ℕ)
    (hspace : heap+(1+6*count)+updateAllocationBound w b g l eta allocation+(1+2*L)<2^w) :
    heap+(1+6*count)+allocation 0 [b,heap,g,l,eta,heap+(1+6*count)]+(1+2*L)<2^w := by
  have hb : heap<2^w := by omega
  have hh : heap+(1+6*count)<2^w := by omega
  have ha := update_allocation_le_bound (b:=b) (g:=g) (l:=l) (eta:=eta) allocation hb hh
  exact (Nat.add_le_add_right (Nat.add_le_add_left ha (heap+(1+6*count))) (1+2*L)).trans_lt hspace

end MinCostFlow.IPM.Machine
