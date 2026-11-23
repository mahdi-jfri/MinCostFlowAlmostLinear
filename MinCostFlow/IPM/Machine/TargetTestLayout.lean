module

public import MinCostFlow.IPM.Machine.TargetTest
public import MinCostFlow.IPM.Machine.EpochLayoutArgs
import Mathlib.Tactic.IntervalCases

/-!
# Fixed and changing words in the bounded target test

The stage packet has two changing positions, the explicit flow and
the heap. All other words come from the original target call.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The stage packet occupies exactly twenty-three registers. -/
theorem targetEpochPacket_length {w : ℕ} (F : MinRatioFormat w) (I : Instance) (L : EpochLayout)
    (tp qp src heap : ℕ) : (targetEpochPacket L F I tp qp src heap).length=23 := rfl

/-- The target test forwards the exact current stage packet. -/
theorem targetTestStep_args {w : ℕ} (F : MinRatioFormat w) (I : Instance) (L : EpochLayout)
    (tp qp src heap : ℕ) (st : State)
    (hr : ∀ j<23,st.regs j=(targetEpochPacket L F I tp qp src heap).getD j 0) :
    evalArgs w st ((List.range 23).map Expr.reg)=some (targetEpochPacket L F I tp qp src heap) := by
  simpa only [targetEpochPacket_length,List.range_eq_range'] using
    (evalArgs_range_regs (w:=w) st (targetEpochPacket L F I tp qp src heap) 0
      (fun j hj => by simpa only [Nat.zero_add] using hr j hj))

/-- The static words are unaffected by either changing pointer. -/
theorem targetEpochPacket_fixed {w : ℕ} (F : MinRatioFormat w) (I : Instance) (L : EpochLayout)
    (tp qp src heap next newHeap j : ℕ) (hj : j<23) (h20 : j≠20) (h21 : j≠21) :
    (targetEpochPacket L F I tp qp src heap).getD j 0=
      (targetEpochPacket L F I tp qp next newHeap).getD j 0 := by
  interval_cases j <;> simp_all [targetEpochPacket]

/-- A new pair of fitting pointers gives word-fit for the next call. -/
theorem targetEpochPacket_words {w : ℕ} (F : MinRatioFormat w) (I : Instance) (L : EpochLayout)
    (tp qp src heap next newHeap : ℕ)
    (hwords : ∀ z∈targetEpochPacket L F I tp qp src heap,z<2^w)
    (hsrc : next<2^w) (hheap : newHeap<2^w) :
    ∀ z∈targetEpochPacket L F I tp qp next newHeap,z<2^w := by
  intro z hz
  simp only [targetEpochPacket,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact hsrc | exact hheap | exact hwords _ (by simp [targetEpochPacket])

/-- The counter limit follows the stage packet in the actual test entry. -/
theorem targetTest_start_registers {w : ℕ} (F : MinRatioFormat w) (I : Instance) (L : EpochLayout)
    (tp qp src heap limit pos : ℕ) (mem : ℕ → ℕ) :
    let st := startState (targetEpochPacket L F I tp qp src heap++[limit]) mem pos
    st.regs 23=limit ∧ ∀ j<23,st.regs j=(targetEpochPacket L F I tp qp src heap).getD j 0 := by
  constructor
  · change (targetEpochPacket L F I tp qp src heap++[limit]).getD 23 0=limit
    rw [List.getD_append_right _ _ _ _ (by rw [targetEpochPacket_length])]
    rfl
  · intro j hj
    change (targetEpochPacket L F I tp qp src heap++[limit]).getD j 0=_
    exact List.getD_append _ _ _ _ hj

/-- Append evaluated trailing arguments to `evalArgs`. -/
theorem evalArgs_append {w : ℕ} {st : State} {es₁ es₂ : List Expr} {vs₁ vs₂ : List ℕ}
    (h1 : evalArgs w st es₁ = some vs₁) (h2 : evalArgs w st es₂ = some vs₂) :
    evalArgs w st (es₁ ++ es₂) = some (vs₁ ++ vs₂) := by
  induction es₁ generalizing vs₁ with
  | nil => cases h1; simpa using h2
  | cons a es₁ ih =>
    cases ha : a.eval w st with
    | none => simp [evalArgs, ha] at h1
    | some x =>
      cases hrest : evalArgs w st es₁ with
      | none => simp [evalArgs, ha, hrest] at h1
      | some ys =>
        have hvs : x :: ys = vs₁ := by simpa [evalArgs, ha, hrest] using h1
        subst hvs
        simp only [List.cons_append,evalArgs,ha,ih hrest]

end MinCostFlow.IPM.Machine
