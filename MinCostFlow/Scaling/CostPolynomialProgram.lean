module

public import WordRAM.Contract
public import WordRAM.Layout
import WordRAM.Tactic
import WordRAM.Entry
import WordRAM.LinkDefs

/-!
# Computing the cost model's polynomial threshold

The cost-scaling wrapper compares its cost bound with `m^10` before
choosing a direct bounded-cost call or the cost loop. Four multiplications
compute that threshold through exponents two, four, eight, and ten. Every
intermediate is at most the final threshold, and memory is unchanged.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[edgeCount]`. -/
def costPolynomialBody : Stmt :=
  .assign 1 (.bin .mul (.reg 0) (.reg 0)) ;;
  .assign 2 (.bin .mul (.reg 1) (.reg 1)) ;;
  .assign 3 (.bin .mul (.reg 2) (.reg 2)) ;;
  .ret (.bin .mul (.reg 3) (.reg 1))

/-- One threshold-computation entry. -/
def costPolynomialModule : List Stmt := [costPolynomialBody]

/-- Exact `m^10` with fitting arithmetic and unchanged memory. -/
def costPolynomialContract (w m : ℕ) : Contract where
  pre args _ := args=[m] ∧ m^10<2^w
  post _ mem ret mem' := ret=m^10 ∧ mem'=mem
  cost _ _ := 30

/-- Threshold computation has no random instruction. -/
theorem costPolynomialBody_noRand : costPolynomialBody.NoRand := by trivial

/-- The polynomial threshold uses four multiplications and at most
30 steps, with no memory changes and no randomness. -/
theorem costPolynomial_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b costPolynomialModule) (m : ℕ) :
    MeetsContract w p b (costPolynomialContract w m) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨rfl,h10⟩ := hpre
  have hlow : ∀ k,0<k → k≤10 → m^k≤m^10 := by
    intro k hk hkle
    by_cases hm : m=0
    · simp only [hm,Nat.zero_pow hk,Nat.zero_pow (by decide : 0<10)]
      exact le_rfl
    · exact Nat.pow_le_pow_right (Nat.pos_of_ne_zero hm) hkle
  have h2 : m^2<2^w := (hlow 2 (by decide) (by decide)).trans_lt h10
  have h4 : m^4<2^w := (hlow 4 (by decide) (by decide)).trans_lt h10
  have h8 : m^8<2^w := (hlow 8 (by decide) (by decide)).trans_lt h10
  have he4 : m^2*m^2=m^4 := by rw [←pow_add]
  have he8 : m^4*m^4=m^8 := by rw [←pow_add]
  have he10 : m^8*m^2=m^10 := by rw [←pow_add]
  have hmul2 : m*m<2^w := by simpa only [pow_two] using h2
  have hmul4 : m^2*m^2<2^w := by rw [he4]; exact h4
  have hmul8 : m^4*m^4<2^w := by rw [he8]; exact h8
  have hmul10 : m^8*m^2<2^w := by rw [he10]; exact h10
  apply runs_start_le
  unfold costPolynomialBody
  refine runs_seq_assign_le (v := m^2) (by rw [pow_two]; eval_expr) ?_
  refine runs_seq_assign_le (v := m^4) (by rw [←he4]; eval_expr) ?_
  refine runs_seq_assign_le (v := m^8) (by rw [←he8]; eval_expr) ?_
  refine runs_ret_le (v := m^10) (by rw [←he10]; eval_expr) ⟨rfl,rfl⟩ ?_
  simp only [costPolynomialContract,Expr.size_bin,Expr.size_reg]
  decide

/-- Multiplier ten on the edge-count encoding jointly covers the
threshold and every intermediate word, also when the edge count is zero. -/
theorem costPolynomial_pre_wordSize (m : ℕ) :
    (∀ x∈[m],x<2^wordSize 10 [m]) ∧
      (costPolynomialContract (wordSize 10 [m]) m).pre [m] (fun _ => 0) := by
  let B := [m].length+[m].foldr max 0+2
  have hmB : m≤B := by simp only [B,List.length_cons,List.length_nil,List.foldr_cons,List.foldr_nil,Nat.max_zero]; omega
  have hp := pow_lt_two_pow_wordSize (by decide : 1≤10) [m]
  change B^10<2^wordSize 10 [m] at hp
  exact ⟨fun x hx => lt_two_pow_wordSize_of_mem (by decide) hx,rfl,(Nat.pow_le_pow_left hmB 10).trans_lt hp⟩

end MinCostFlow.Scaling.Machine
