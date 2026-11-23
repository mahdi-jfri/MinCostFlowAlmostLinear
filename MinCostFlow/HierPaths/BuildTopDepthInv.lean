module

public import MinCostFlow.HierPaths.BuildTopDepthStep

/-!
# Recording the replies of a depth

The scan keeps the graph directory and terminal table below the heap.
Each iteration records the address of its reply and preserves the
encoded replies of the earlier parents.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited

/-- The fixed words of a scan and the parent graphs they describe. -/
structure BuildTopDepthInput where
  graphDir : ℕ
  replyDir : ℕ
  termBase : ℕ
  childSize : ℕ
  branch : ℕ
  count : ℕ
  scale : ℕ
  rank : ℕ
  degree : ℕ
  pathLog : ℕ
  coreLog : ℕ
  denominator : ℕ
  graph : ℕ → Graph
  graphAddr : ℕ → ℕ

namespace BuildTopDepthInput

variable (D : BuildTopDepthInput)

def args (h : ℕ) : List ℕ :=
  [D.graphDir, D.replyDir, D.termBase, D.childSize, D.branch, D.count, D.scale, D.rank,
    D.degree, D.pathLog, D.coreLog, D.denominator, h]

def start (i : ℕ) : ℕ := i * (D.childSize * D.branch)

def callArgs (i h : ℕ) : List ℕ :=
  buildLevelArgs (D.graphAddr i) D.termBase (D.start i) D.childSize D.branch D.scale D.rank
    D.degree D.pathLog D.coreLog D.denominator h

def level (w K : ℕ) (space : Graph → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (i : ℕ) :
    Contract :=
  buildTopParentCallContract w K space (D.graph i) (D.start i) D.childSize D.branch D.scale D.rank
    D.degree D.pathLog D.coreLog D.denominator

def work (K i : ℕ) : ℕ :=
  buildLevelCost K (D.graph i) D.childSize D.branch D.scale D.rank D.degree D.pathLog
    D.coreLog D.denominator

def spaceStep (space : Graph → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (i : ℕ) : ℕ :=
  space (D.graph i) D.childSize D.branch D.scale D.rank D.degree D.pathLog
    D.coreLog D.denominator

def frame (h : ℕ) (initial mem : ℕ → ℕ) : Prop :=
  ∀ a < h, (a < D.replyDir ∨ D.replyDir + D.count ≤ a) → mem a = initial a

/-- A reply already present in the scan's directory. -/
def replyAt (i h cur : ℕ) (mem : ℕ → ℕ) : Prop :=
  ∃ (a : ℕ) (R : BuildLevelData), mem (D.replyDir + i) = a ∧ h ≤ a ∧ a + (R.encode D.branch).length ≤ cur ∧
    ListAt mem a (R.encode D.branch) ∧
    R.Good (D.graph i) (D.start i) D.childSize D.branch D.scale D.rank D.degree D.pathLog
      D.coreLog D.denominator

def state (space : Graph → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (h : ℕ)
    (initial : ℕ → ℕ) (i : ℕ) (st : State) : Prop :=
  (∀ j < 12, st.regs j = (D.args h).getD j 0) ∧
  st.regs 13 = i ∧ st.regs 15 = D.childSize * D.branch ∧
  h ≤ st.regs 12 ∧ st.regs 12 ≤ h + rangeCost (D.spaceStep space) 0 i ∧
  ZeroFrom st.mem (st.regs 12) ∧ D.frame h initial st.mem ∧
  ∀ j < i, D.replyAt j h (st.regs 12) st.mem

end BuildTopDepthInput

end MinCostFlow.HierPaths

end
