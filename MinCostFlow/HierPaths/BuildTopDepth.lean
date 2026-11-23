module

public import MinCostFlow.HierPaths.BuildTopCall

/-!
# Scanning the parent groups at one depth

The input directory contains the addresses of the parent graphs.
The loop records the start of each reply in a second directory and
passes the returned heap pointer to the next parent.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-- Arguments are the graph and reply directories, terminal table, child size,
branching, parent count, player parameters, and the incoming heap pointer. -/
def buildTopDepthBody (call : ℕ) : Stmt :=
  .assign 14 (.bin .mul (.reg 13) (.reg 15)) ;;
  .store (.bin .add (.reg 1) (.reg 13)) (.reg 12) ;;
  .call 12 call
    [.load (.bin .add (.reg 0) (.reg 13)), .reg 2, .reg 14, .reg 3, .reg 4, .reg 6,
      .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12]

/-- Visit each parent exactly once and return the pointer after its replies. -/
def buildTopDepth (call : ℕ) : Stmt :=
  .assign 15 (.bin .mul (.reg 3) (.reg 4)) ;;
  forRange 13 (.const 0) (.reg 5) (buildTopDepthBody call) ;;
  .ret (.reg 12)

theorem buildTopDepth_noRand (call : ℕ) : (buildTopDepth call).NoRand := by
  simp [buildTopDepth, buildTopDepthBody, forRange, forUp, Stmt.NoRand]

end MinCostFlow.HierPaths

end
