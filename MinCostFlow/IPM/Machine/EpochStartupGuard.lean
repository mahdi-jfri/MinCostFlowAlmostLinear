module

public import MinCostFlow.IPM.Machine.EpochStartNamesBudget
public import MinCostFlow.IPM.Machine.EpochStartRangeScan
import WordRAM.Tactic

/-!
# Checking the initialization before entering the lazy loop

Init and the full name list come first. Check all freshly computed
coefficients once, with the same interval used for Detect updates.
On acceptance keep the original budget record. Otherwise append a
failure bit and return before any lazy iteration.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Recover the name list from the final budget record. -/
def epochStartupScanArgs : List Expr :=
  [.bin .sub (.bin .sub (.reg 18) (.const 3)) (.reg 0),.reg 0,
    .bin .add (.reg 13) (.reg 11),.reg 13,.reg 15,.reg 16,.reg 17,.reg 8]

/-- Scan the initialized coefficient arrays and write a fresh bit only
on rejection. -/
def epochStartupTail (scan flag : ℕ) : Stmt :=
  .call 19 scan epochStartupScanArgs ;;
  .cond (.reg 19) (.ret (.reg 18))
    (.call 20 flag [.const 0,.reg 18] ;; .ret (.reg 20))

/-- Arguments are the fifteen startup words followed by the negative
gradient limit, positive limit, and minimum length. -/
def epochStartupBody (start scan flag : ℕ) : Stmt :=
  .call 18 start ((List.range 15).map Expr.reg) ;; epochStartupTail scan flag

/-- Both startup outcomes use deterministic caller code. -/
theorem epochStartupBody_noRand (start scan flag : ℕ) :
    (epochStartupBody start scan flag).NoRand := by
  simp [epochStartupBody,epochStartupTail,Stmt.NoRand]

/-- `V`-passing startup: receives 19 words `[..., graph, neg, mx, mn, V]`, forwards
the 15 startup words plus `V` (in `.reg 18`) to `start`, keeping `neg..mn` in `.reg 15..17`. -/
def epochStartupBodyWithV (start scan flag : ℕ) : Stmt :=
  .call 18 start ((List.range 15).map Expr.reg ++ [.reg 18]) ;; epochStartupTail scan flag

/-- Both `V`-passing startup outcomes use deterministic caller code. -/
theorem epochStartupBodyWithV_noRand (start scan flag : ℕ) :
    (epochStartupBodyWithV start scan flag).NoRand := by
  simp [epochStartupBodyWithV,epochStartupTail,Stmt.NoRand]

end MinCostFlow.IPM.Machine
