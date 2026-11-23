module

public import WordRAM.Logic

/-!
# Refreshing the reported edge list

The per-edge loop of Algorithm 7 of [chen2022maximum], v2, page 69,
recovers the reported coordinates and refreshes their coefficients.
This entry follows the actual order returned by Detect. Each linked
reported-edge call checks capacities and slacks before accepting its
coordinate. A failed call returns immediately. An empty list, or a list
whose calls all succeed, ends with a fresh success record.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Inspect the last word returned by the per-edge call. Success advances
the allocation endpoint. Failure returns that endpoint immediately. -/
def reportedEdgesLoopTail : Stmt :=
  .assign 25 (.load (.bin .sub (.reg 24) (.const 1))) ;;
  .cond (.reg 25) (.assign 21 (.reg 24)) (.ret (.reg 24))

/-- Read the next reported name and its scalar-table offset. -/
def reportedEdgesRead : Stmt :=
  .assign 22 (.load (.bin .add (.reg 1) (.reg 20))) ;;
  .assign 23 (.bin .mul (.reg 22) (.reg 7))

/-- Per-edge arguments computed from the parent table bases and offset. -/
def reportedEdgesCallArgs : List Expr :=
  [.reg 0,.reg 22,.bin .add (.reg 3) (.reg 23),
    .bin .add (.reg 4) (.reg 23),.bin .add (.reg 5) (.reg 23),
    .bin .add (.reg 6) (.reg 23),.reg 7,.reg 21,
    .bin .add (.reg 9) (.reg 23),.reg 10,.reg 11,.reg 12,
    .reg 13,.reg 14,.reg 15,.reg 16,
    .bin .add (.reg 17) (.reg 23),.bin .add (.reg 18) (.reg 23),.reg 19]

/-- Recover and refresh the selected edge, then inspect its final status. -/
def reportedEdgesCallBody (reported : ℕ) : Stmt :=
  .call 24 reported reportedEdgesCallArgs ;; reportedEdgesLoopTail

/-- Read one name, form its scalar-table offset, and call the checked
refresh entry. The counter and allocation endpoint are registers 20
and 21. Only success allows the enclosing loop to increment its counter. -/
def reportedEdgesLoopBody (reported : ℕ) : Stmt :=
  reportedEdgesRead ;; reportedEdgesCallBody reported

/-- Initialize the caller's current endpoint and zero counter. -/
def reportedEdgesInit : Stmt :=
  .assign 21 (.reg 8) ;; .assign 20 (.const 0)

/-- Append the entry's fresh success record after normal loop completion. -/
def reportedEdgesFinish (flag : ℕ) : Stmt :=
  .call 26 flag [.const 1,.reg 21] ;; .ret (.reg 26)

/-- Arguments are
`[handle,names,count,baseTable,lowerTable,upperTable,flowTable,L,heap,costTable,residual,alpha,one,min,max,P,E,lengthTable,gradientTable,m]`.
The name list has no header here: callers pass Detect's answer plus one.
The returned endpoint has a uniform final status at `endpoint-1`.
The success record also covers an empty Detect answer. -/
def reportedEdgesBody (reported flag : ℕ) : Stmt :=
  reportedEdgesInit ;;
  forUp 20 (.reg 2) (reportedEdgesLoopBody reported) ;;
  reportedEdgesFinish flag

/-- The loop itself and both possible return paths contain no randomness. -/
theorem reportedEdgesBody_noRand (reported flag : ℕ) :
    (reportedEdgesBody reported flag).NoRand := by
  simp [reportedEdgesBody,reportedEdgesInit,reportedEdgesFinish,reportedEdgesLoopBody,reportedEdgesCallBody,reportedEdgesRead,reportedEdgesLoopTail,forUp,Stmt.NoRand]

end MinCostFlow.IPM.Machine
