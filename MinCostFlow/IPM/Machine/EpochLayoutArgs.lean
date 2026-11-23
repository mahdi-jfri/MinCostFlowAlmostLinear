module

public import MinCostFlow.IPM.Machine.EpochLayout
public import MinCostFlow.IPM.Machine.EpochIterations
import Mathlib.Data.List.GetD

/-!
# The epoch caller's actual packet reads

The loop forwards registers zero through twenty-four. Their equality
with the fixed packet determines the actual argument list. Word-fit is
supplied separately by the fixed-packet word lemma. The count follows those packet words in the outer entry.
These statements connect the fixed layout to the existing caller code.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Evaluate consecutive register reads using the corresponding packet entries. -/
theorem evalArgs_range_regs {w : ℕ} (st : State) (values : List ℕ) (offset : ℕ)
    (hregs : ∀ j<values.length,st.regs (offset+j)=values.getD j 0)
    :
    evalArgs w st ((List.range' offset values.length).map Expr.reg)=some values := by
  induction values generalizing offset with
  | nil => rfl
  | cons a xs ih =>
    have hreg : st.regs offset=a := by simpa using hregs 0 (by simp)
    have hread : Expr.eval w st (.reg offset)=some a := by simp [Expr.eval,hreg]
    have htail := ih (offset+1) (fun j hj => by
      have hh := hregs (j+1) (by simpa using Nat.succ_lt_succ hj)
      simpa only [List.getD_cons_succ,Nat.add_assoc,Nat.add_comm 1 j] using hh)
    simp only [List.length_cons,List.range'_succ,List.map_cons,evalArgs,hread,htail]

/-- Reading the first twenty-five caller registers yields exactly the
existing complete iteration packet, with the original word-fit supplied separately by `packet_words`. -/
theorem EpochLayout.packet_args {w : ℕ} (L : EpochLayout) (F : MinRatioFormat w) (I : Instance)
    (heap : ℕ) (parent : State)
    (hregs : ∀ j<25,parent.regs j=(L.packet F I heap).getD j 0) :
    evalArgs w parent epochIterationsArgs=some (L.packet F I heap) := by
  have hargs : epochIterationsArgs=(List.range' 0 (L.packet F I heap).length).map Expr.reg := by
    rw [L.packet_length]
    rfl
  rw [hargs]
  apply evalArgs_range_regs parent _ 0
  intro j hj
  simpa only [Nat.zero_add] using hregs j (by simpa only [L.packet_length] using hj)

/-- Appending the loop count preserves every forwarded packet register. -/
theorem EpochLayout.packet_start_regs {w : ℕ} (L : EpochLayout) (F : MinRatioFormat w) (I : Instance)
    (heap count : ℕ) (mem : ℕ → ℕ) (pos j : ℕ) (hj : j<25) :
    (startState (L.packet F I heap++[count]) mem pos).regs j=(L.packet F I heap).getD j 0 := by
  change (L.packet F I heap++[count]).getD j 0=(L.packet F I heap).getD j 0
  exact List.getD_append _ _ _ _ (by simpa only [L.packet_length] using hj)

/-- The outer entry reads its iteration count from register twenty-five. -/
theorem EpochLayout.packet_start_count {w : ℕ} (L : EpochLayout) (F : MinRatioFormat w) (I : Instance)
    (heap count : ℕ) (mem : ℕ → ℕ) (pos : ℕ) :
    (startState (L.packet F I heap++[count]) mem pos).regs 25=count := by
  change (L.packet F I heap++[count]).getD 25 0=count
  rw [List.getD_append_right _ _ _ _ (by rw [L.packet_length])]
  simp only [L.packet_length,Nat.sub_self,List.getD_cons_zero]

end MinCostFlow.IPM.Machine
