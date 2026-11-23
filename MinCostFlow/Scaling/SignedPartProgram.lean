module

public import MinCostFlow.Statement.Problem
public import WordRAM.Layout
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Selecting positive or negative demand capacity

The demand-to-circulation reduction of Lemma C.1 of Chen et al.,
arXiv:2203.00671v2, gives the two artificial arcs at a vertex capacities
`d.toNat` and `(-d).toNat`. In canonical sign/magnitude form, selecting the
matching sign returns the magnitude and the other sign returns zero.
The procedure changes no memory and costs at most 15 steps.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[sign,magnitude]`. A fixed Boolean selects the negative part. -/
def signedPartBody (negative : Bool) : Stmt :=
  .cond (.bin .eq (.reg 0) (.const (if negative then 1 else 0)))
    (.ret (.reg 1)) (.ret (.const 0))

/-- Signed-part selection occupies one procedure slot. -/
def signedPartModule (negative : Bool) : List Stmt := [signedPartBody negative]

/-- The returned unsigned part is the exact artificial demand capacity. -/
def signedPartContract (w : ℕ) (negative : Bool) (x : ℤ) : Contract where
  pre args _ := args = [if x < 0 then 1 else 0, x.natAbs] ∧ 1 < 2 ^ w
  post _ mem out mem' := mem' = mem ∧ out = if negative then (-x).toNat else x.toNat
  cost _ _ := 15

/-- Sign selection has no random instruction. -/
theorem signedPartBody_noRand (negative : Bool) : (signedPartBody negative).NoRand := by
  trivial

/-- Selecting an unsigned demand part computes its mathematical capacity
with unchanged memory and constant cost on every tape. -/
theorem signedPart_meetsContract {w b : ℕ} {p : Program} (negative : Bool)
    (hp : p.HasAt b (signedPartModule negative)) (x : ℤ) :
    MeetsContract w p b (signedPartContract w negative x) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨rfl, hw⟩ := hpre
  have hm : x.natAbs < 2 ^ w := hwords _ (List.mem_cons_of_mem _ (List.mem_cons_self))
  have hflag : (if negative then 1 else 0 : ℕ) < 2 ^ w := by
    cases negative
    · exact Nat.two_pow_pos _
    · exact hw
  apply runs_start_le
  unfold signedPartBody
  wram_step
  · have hsign : (if x < 0 then 1 else 0 : ℕ) = if negative then 1 else 0 := by
      simpa [startState] using hcond
    have hresult : x.natAbs = if negative then (-x).toNat else x.toNat := by
      cases negative <;> by_cases hx : x < 0 <;> simp only [hx, ↓reduceIte, Bool.false_eq_true] at hsign ⊢ <;> omega
    refine runs_ret_le (by eval_expr) ⟨rfl, hresult⟩ ?_
    simp only [signedPartContract, Expr.size_bin, Expr.size_reg, Expr.size_const]
    omega
  · have hsign : (if x < 0 then 1 else 0 : ℕ) ≠ if negative then 1 else 0 := by
      simpa [startState] using hcond
    have hresult : 0 = if negative then (-x).toNat else x.toNat := by
      cases negative <;> by_cases hx : x < 0 <;> simp only [hx, ↓reduceIte, Bool.false_eq_true] at hsign ⊢ <;> omega
    refine runs_ret_le (by eval_expr) ⟨rfl, hresult⟩ ?_
    simp only [signedPartContract, Expr.size_bin, Expr.size_reg, Expr.size_const]
    omega

/-- Both signs have simultaneous witnesses for the full machine precondition for every integer. -/
theorem exists_signedPart_pre (negative : Bool) (x : ℤ) :
    ∃ w, (∀ a ∈ [if x < 0 then 1 else 0, x.natAbs], a < 2 ^ w) ∧
      (signedPartContract w negative x).pre [if x < 0 then 1 else 0, x.natAbs] (fun _ => 0) := by
  let w := wordSize 1 [x.natAbs + 3]
  have hlarge : x.natAbs + 3 < 2 ^ w :=
    lt_two_pow_wordSize_of_mem (by decide) (List.mem_cons_self)
  refine ⟨w, ?_, rfl, by omega⟩
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · split <;> omega
  · omega

end MinCostFlow.Scaling.Machine
