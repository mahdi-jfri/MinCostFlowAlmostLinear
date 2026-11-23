module

public import MinCostFlow.IPM.Machine.RoundLoopBudget
public import MinCostFlow.IPM.Machine.GraphCoefficientRead
import WordRAM.Tactic

/-!
# Decoding the next edge in the rounding scan

The scan uses the existing circulation-row layout. The edge
endpoints come from two words of its row. Its cost and working
flow are addressed by the same index in the fixed-point tables.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Address of the two-cell header plus the current row offset. -/
def roundLoopRowBase : Expr :=
  .bin .add (.reg 3) (.bin .mul (.const 5) (.reg 1))

/-- Arguments to the single-edge procedure. -/
def roundLoopEdgeArgs : List Expr :=
  [.reg 0,.reg 1,
    .load (.bin .add roundLoopRowBase (.const 2)),
    .load (.bin .add roundLoopRowBase (.const 3)),
    .bin .add (.reg 4) (.bin .mul (.reg 1) (.reg 6)),
    .bin .add (.reg 5) (.bin .mul (.reg 1) (.reg 6)),
    .reg 6,.reg 7,.reg 8,.reg 5,.bin .add (.reg 2) (.const 1),.reg 9]

/-- Args [b,k,m,graph,cost,flow,L,P,one,heap]. Scan from k to m
with one call per edge in input order. -/
def roundLoopBody (entry edge : ℕ) : Stmt :=
  .cond (.bin .lt (.reg 1) (.reg 2))
    (.call 10 edge roundLoopEdgeArgs ;;
     .call 10 entry [.reg 0,.bin .add (.reg 1) (.const 1),.reg 2,.reg 3,.reg 4,
       .reg 5,.reg 6,.reg 7,.reg 8,.reg 10] ;;
     .ret (.reg 10))
    (.ret (.reg 9))

/-- The scan contains no random instruction. -/
theorem roundLoop_noRand (entry edge : ℕ) : (roundLoopBody entry edge).NoRand := by
  simp [roundLoopBody,Stmt.NoRand]

/-- The loaded endpoints and address arithmetic give the exact
single-edge arguments. -/
theorem roundLoopEdgeArgs_eval {w L P : ℕ} (I : Instance) (hI : I.IsValid)
    (j : Fin I.m) (b graph cost base one heap : ℕ) (mem : ℕ → ℕ) (pos : ℕ)
    (hRows : ZeroLowerAt mem graph I) (hGraph : graph+(zeroLowerWords I).length≤base)
    (hEnd : base+I.m*L≤b) (hb : b≤heap) (hHeap : heap<2^w)
    (hCost : cost+I.m*L≤base) (hOne : one+L≤base)
    (hM : I.m+1<2^w) (hN : I.n≤2^w) (hL : L<2^w) (hP : P<2^w) (hFive : 5<2^w) :
    let args := [b,j.val,I.m,graph,cost,base,L,P,one,heap]
    let ea := [b,j.val,(I.edge j).tail,(I.edge j).head,cost+j.val*L,base+j.val*L,L,P,one,base,I.m+1,heap]
    evalArgs w (startState args mem pos) roundLoopEdgeArgs=some ea ∧ ∀ z∈ea,z<2^w := by
  dsimp only
  have hLen := zeroLowerWords_length I hI
  rw [hLen] at hGraph
  have hh := Nat.mul_le_mul_left 5 (Nat.succ_le_of_lt j.isLt)
  rw [Nat.mul_succ] at hh
  have hj := Nat.mul_le_mul_right L j.isLt.le
  have hRow : graph+5*j.val+3<2^w := by omega
  have hRowT : graph+5*j.val+2<2^w := by omega
  have hR0 : graph+5*j.val<2^w := by omega
  have hMul : 5*j.val<2^w := by omega
  have hMulL : j.val*L<2^w := by omega
  have hCostW : cost+j.val*L<2^w := by omega
  have hFlowW : base+j.val*L<2^w := by omega
  have hTwo : 2<2^w := by omega
  have hThree : 3<2^w := by omega
  have hOneW : 1<2^w := by omega
  have he := zeroLower_endpoints_at I hI mem graph hRows.2.2 j
  have hTail : mem (graph+5*j.val+2)=(I.edge j).tail := by
    rw [show graph+5*j.val+2=graph+2+5*j.val by omega]
    exact he.1
  have hHead : mem (graph+5*j.val+3)=(I.edge j).head := by
    rw [show graph+5*j.val+3=graph+3+5*j.val by omega]
    exact he.2
  have hEnds := hI.1 (I.edge j) (List.getElem_mem j.isLt)
  have hU : (I.edge j).tail<2^w := hEnds.1.trans_le hN
  have hV : (I.edge j).head<2^w := hEnds.2.trans_le hN
  constructor
  · unfold roundLoopEdgeArgs roundLoopRowBase
    eval_expr
  · wram_words

end MinCostFlow.IPM.Machine
