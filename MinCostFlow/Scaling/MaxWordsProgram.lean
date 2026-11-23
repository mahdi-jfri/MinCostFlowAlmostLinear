module

public import WordRAM.Contract
import WordRAM.Tactic

/-!
# Combining scanned input bounds

The entry program combines maxima of lower capacities, upper capacities,
and demands. A comparison returns the larger of two words without
changing memory or performing arithmetic on their values.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[left,right]`. -/
def maxWordsBody : Stmt :=
  .cond (.bin .lt (.reg 0) (.reg 1)) (.ret (.reg 1)) (.ret (.reg 0))

/-- One procedure compares two words. -/
def maxWordsModule : List Stmt := [maxWordsBody]

/-- Both argument words are supplied explicitly. -/
def maxWordsContract (w x y : ℕ) : Contract where
  pre args _ := args=[x,y] ∧ 1<2^w
  post _ mem ret mem' := mem'=mem ∧ ret=max x y
  cost _ _ := 20

/-- A maximum comparison contains no random instruction. -/
theorem maxWordsModule_noRand : ∀ body∈maxWordsModule,body.NoRand := by
  intro body hb
  have he : body=maxWordsBody := by simpa only [maxWordsModule,List.mem_singleton] using hb
  subst body
  simp only [maxWordsBody,Stmt.NoRand,and_self]

/-- The comparison returns the larger word within twenty steps. -/
theorem maxWords_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b maxWordsModule) (x y : ℕ) :
    MeetsContract w p b (maxWordsContract w x y) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨rfl,h1⟩ := hpre
  apply runs_start_le
  unfold maxWordsBody
  wram_step
  · refine runs_ret_le (v := y) (by eval_expr) (by change mem=mem ∧ y=max x y; exact ⟨rfl,(Nat.max_eq_right (by omega)).symm⟩) ?_
    simp only [maxWordsContract,Expr.size_bin,Expr.size_reg]
    omega
  · refine runs_ret_le (v := x) (by eval_expr) (by change mem=mem ∧ x=max x y; exact ⟨rfl,(Nat.max_eq_left (by omega)).symm⟩) ?_
    simp only [maxWordsContract,Expr.size_bin,Expr.size_reg]
    omega

end MinCostFlow.Scaling.Machine
