module

public import MinCostFlow.Scaling.CapacityUnitProgram
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Scaling and clipping one capacity

Definition C.11 of Appendix C of Chen et al., arXiv:2203.00671v2,
rounds and clips a capacity before passing it to the polynomial-capacity
solver. This procedure computes `scaledCapacity`, including the corrected
clipping threshold described in `CapacityRounding`. Its arguments share
`m^20` and the rounding unit across all edges. It changes no memory and
costs at most 30 steps.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[u,B,m^20,capacityUnit m B]`. -/
def scaledCapacityBody : Stmt :=
  .assign 4 (.bin .div (.reg 0) (.reg 3)) ;;
  .assign 5 (.bin .div (.bin .mul (.reg 1) (.reg 2)) (.reg 3)) ;;
  .cond (.bin .lt (.reg 4) (.reg 5)) (.ret (.reg 4)) (.ret (.reg 5))

/-- Scaling one capacity occupies one procedure slot. -/
def scaledCapacityModule : List Stmt := [scaledCapacityBody]

/-- The clipping product must fit as well as the supplied arguments.
The result is the exact scaled capacity, with unchanged memory. -/
def scaledCapacityContract (w m B u : ℕ) : Contract where
  pre args _ := args = [u, B, m ^ 20, capacityUnit m B] ∧
    B * m ^ 20 < 2 ^ w
  post _ mem out mem' := mem' = mem ∧ out = scaledCapacity m B u
  cost _ _ := 30

/-- Scaling and clipping use no random instructions. -/
theorem scaledCapacityBody_noRand : scaledCapacityBody.NoRand := by
  simp only [scaledCapacityBody, Stmt.NoRand, and_self]

/-- The machine computes Definition C.11's scaled capacity with a constant
cost and no memory changes, uniformly over all tapes. -/
theorem scaledCapacity_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b scaledCapacityModule) (m B u : ℕ) :
    MeetsContract w p b (scaledCapacityContract w m B u) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨rfl, hproduct⟩ := hpre
  have hu : u < 2 ^ w := hwords _ (List.mem_cons_self)
  have hB : B < 2 ^ w :=
    hwords _ (List.mem_cons_of_mem _ (List.mem_cons_self))
  have hd : m ^ 20 < 2 ^ w :=
    hwords _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
  have hc : capacityUnit m B < 2 ^ w :=
    hwords _ (by simp)
  have hpos := capacityUnit_pos m B
  have hq : u / capacityUnit m B < 2 ^ w :=
    lt_of_le_of_lt (Nat.div_le_self _ _) hu
  have hr : B * m ^ 20 / capacityUnit m B < 2 ^ w :=
    lt_of_le_of_lt (Nat.div_le_self _ _) hproduct
  apply runs_start_le
  unfold scaledCapacityBody
  wram_step
  wram_step
  wram_step
  · have hlt : u / capacityUnit m B < B * m ^ 20 / capacityUnit m B := by
      simpa [startState] using hcond
    refine runs_ret_le (by eval_expr) ?_ ?_
    · exact ⟨rfl, (min_eq_left hlt.le).symm⟩
    · simp only [scaledCapacityContract, Expr.size_bin, Expr.size_reg]
      omega
  · have hnlt : ¬u / capacityUnit m B < B * m ^ 20 / capacityUnit m B := by
      simpa [startState] using hcond
    refine runs_ret_le (by eval_expr) ?_ ?_
    · exact ⟨rfl, (min_eq_right (Nat.le_of_not_gt hnlt)).symm⟩
    · simp only [scaledCapacityContract, Expr.size_bin, Expr.size_reg]
      omega

/-- The arithmetic and argument bounds can all hold together for every
capacity and rounding parameter, including zero edge counts. -/
theorem exists_scaledCapacity_pre (m B u : ℕ) :
    ∃ w, (∀ a ∈ [u, B, m ^ 20, capacityUnit m B], a < 2 ^ w) ∧
      (scaledCapacityContract w m B u).pre
        [u, B, m ^ 20, capacityUnit m B] (fun _ => 0) := by
  let w := wordSize 1 [u + B + m ^ 20 + capacityUnit m B + B * m ^ 20 + 2]
  have hlarge : u + B + m ^ 20 + capacityUnit m B + B * m ^ 20 + 2 < 2 ^ w :=
    lt_two_pow_wordSize_of_mem (by decide) (List.mem_cons_self)
  refine ⟨w, ?_, rfl, by omega⟩
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl <;> omega

end MinCostFlow.Scaling.Machine
