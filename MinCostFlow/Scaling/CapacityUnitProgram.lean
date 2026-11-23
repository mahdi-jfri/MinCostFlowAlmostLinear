module

public import MinCostFlow.Scaling.CapacityRounding
public import WordRAM.Layout
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Computing the capacity rounding unit

Definition C.11 of Appendix C of Chen et al., arXiv:2203.00671v2,
uses the ceiling of `B / m^20`. For positive `B` this is
`(B-1) / m^20 + 1`, the function `capacityUnit`. The caller supplies
`m^20` as the first argument so this power can be shared across edges.
The procedure reads no memory, allocates nothing, and costs at most 12.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[m^20,B]`, returning the capacity rounding unit. -/
def capacityUnitBody : Stmt :=
  .ret (.bin .add (.bin .div (.bin .sub (.reg 1) (.const 1)) (.reg 0)) (.const 1))

/-- Computing the unit occupies one procedure slot. -/
def capacityUnitModule : List Stmt := [capacityUnitBody]

/-- The positive rounding parameter fits in a word. The unit is returned
without changing memory. -/
def capacityUnitContract (w m B : ℕ) : Contract where
  pre args _ := args = [m ^ 20, B] ∧ 0 < m ∧ 0 < B ∧ B < 2 ^ w
  post _ mem out mem' := mem' = mem ∧ out = capacityUnit m B
  cost _ _ := 12

/-- Computing the unit uses no random instructions. -/
theorem capacityUnitBody_noRand : capacityUnitBody.NoRand := by
  trivial

/-- The ceiling unit is at most its positive numerator. This bounds
all arithmetic results by a supplied input word. -/
theorem capacityUnit_le (m B : ℕ) (hm : 0 < m) (hB : 0 < B) :
    capacityUnit m B ≤ B := by
  have hd : 0 < m ^ 20 := Nat.pow_pos hm
  have hdiv := Nat.div_le_self (B - 1) (m ^ 20)
  unfold capacityUnit
  omega

/-- The machine returns exactly the capacity unit of Definition C.11,
preserves memory, and costs at most 12 on every tape. -/
theorem capacityUnit_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b capacityUnitModule) (m B : ℕ) :
    MeetsContract w p b (capacityUnitContract w m B) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨rfl, hm, hB, hBword⟩ := hpre
  have hdword : m ^ 20 < 2 ^ w := hwords _ (List.mem_cons_self)
  have hd : 0 < m ^ 20 := Nat.pow_pos hm
  have hsub : B - 1 < 2 ^ w := by omega
  have hdiv : (B - 1) / m ^ 20 < 2 ^ w :=
    lt_of_le_of_lt (Nat.div_le_self _ _) hsub
  have hunit : (B - 1) / m ^ 20 + 1 < 2 ^ w :=
    lt_of_le_of_lt (capacityUnit_le m B hm hB) hBword
  have hone : 1 < 2 ^ w := by omega
  apply runs_start_le
  unfold capacityUnitBody
  refine runs_ret_le (v := capacityUnit m B) ?_ ?_ ?_
  · change _ = some ((B - 1) / m ^ 20 + 1)
    eval_expr
  · exact ⟨rfl, rfl⟩
  · simp only [capacityUnitContract, Expr.size_bin, Expr.size_reg, Expr.size_const]
    omega

/-- Every positive edge count and rounding numerator satisfy all the
procedure's preconditions at a sufficiently large word size. -/
theorem exists_capacityUnit_pre (m B : ℕ) (hm : 0 < m) (hB : 0 < B) :
    ∃ w, (∀ a ∈ [m ^ 20, B], a < 2 ^ w) ∧
      (capacityUnitContract w m B).pre [m ^ 20, B] (fun _ => 0) := by
  let w := wordSize 1 [m ^ 20 + B + 2]
  have hlarge : m ^ 20 + B + 2 < 2 ^ w :=
    lt_two_pow_wordSize_of_mem (by decide) (List.mem_cons_self)
  refine ⟨w, ?_, rfl, hm, hB, by omega⟩
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl <;> omega

end MinCostFlow.Scaling.Machine
