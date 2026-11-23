module

public import MinCostFlow.DynSpanner.Program.DynSpannerDelAll

/-!
# Emptying the buckets of the levels `lo ≤ i < hi`: definitions

After a rebuild of level `j`, the levels above `j` are empty and level `j` holds the edges of
`J̃`. So the buckets `hBuckets i` with `j ≤ i` are rebuilt: first every edge of these buckets gets
`minH[e] := 0` and the buckets become empty, then the edges of `J̃` that are in no lower level are
put into bucket `j`. This file has the program of the first part, `dsClearBucketsStmt`, and the
context of its proof. For each level it follows the bucket list (as in `dsDelRecordsStmt`), writes
`0` to `minH[e]` for each edge, and then writes `0` to the head word and the length word.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-- One edge of the bucket: `r7` holds the edge plus one. -/
def dsClearBucketsInnerStmt : Stmt :=
  .assign 10 (.bin .sub (.reg 7) (.const 1)) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.reg 10))) ;;
  .store (.bin .add (.reg 5) (.reg 10)) (.const 0)

/-- One level `r6`. -/
def dsClearBucketsOuterStmt : Stmt :=
  .assign 7 (.load (.bin .add (.reg 1) (.reg 6))) ;;
  .assign 8 (.load (.bin .add (.reg 2) (.reg 6))) ;;
  forRange 9 (.const 0) (.reg 8) dsClearBucketsInnerStmt ;;
  .store (.bin .add (.reg 1) (.reg 6)) (.const 0) ;;
  .store (.bin .add (.reg 2) (.reg 6)) (.const 0)

/-- `args = [nextBase, headBase, degBase, lo, hi, minHBase]`. -/
def dsClearBucketsStmt : Stmt :=
  forRange 6 (.reg 3) (.reg 4) dsClearBucketsOuterStmt ;;
  .ret (.const 0)

def clearBucketsProcs : List Stmt := [dsClearBucketsStmt]

def clearBucketsIdx : ℕ := 0

lemma clearBucketsProcs_noRand : ∀ s ∈ clearBucketsProcs, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-- The data and the precondition of `dsClearBucketsStmt`. -/
structure CBCtx where
  w : ℕ
  eCap : ℕ
  B : ℕ → List ℕ
  lo : ℕ
  hi : ℕ
  prevBase : ℕ
  nextBase : ℕ
  headBase : ℕ
  degBase : ℕ
  minH : ℕ
  mem0 : ℕ → ℕ
  hle : lo ≤ hi
  hw16 : 16 ≤ 2 ^ w
  hnB : nextBase + eCap < 2 ^ w
  hmB : minH + eCap < 2 ^ w
  hhB : headBase + hi < 2 ^ w
  hdB : degBase + hi < 2 ^ w
  dMN : IvlDisj minH eCap nextBase eCap
  dMH : IvlDisj minH eCap (headBase + lo) (hi - lo)
  dMD : IvlDisj minH eCap (degBase + lo) (hi - lo)
  dNH : IvlDisj nextBase eCap (headBase + lo) (hi - lo)
  dND : IvlDisj nextBase eCap (degBase + lo) (hi - lo)
  dHD : IvlDisj (headBase + lo) (hi - lo) (degBase + lo) (hi - lo)
  hB : ∀ i, lo ≤ i → i < hi →
    IsDoublyLinkedList mem0 prevBase nextBase (headBase + i) eCap (B i) ∧
    mem0 (degBase + i) = (B i).length

/-- The cells written so far: `minH` of the edges of `Ws`, and the head and length words of the
levels `lo ≤ i' < i`. Every other cell has its old value. -/
def CBMem (c : CBCtx) (Ws : List ℕ) (i : ℕ) (mem : ℕ → ℕ) : Prop :=
  (∀ x ∈ Ws, mem (c.minH + x) = 0) ∧
  (∀ i', c.lo ≤ i' → i' < i → mem (c.headBase + i') = 0 ∧ mem (c.degBase + i') = 0) ∧
  ∀ addr, (∀ x ∈ Ws, addr ≠ c.minH + x) →
    (∀ i', c.lo ≤ i' → i' < i → addr ≠ c.headBase + i' ∧ addr ≠ c.degBase + i') →
    mem addr = c.mem0 addr

/-- Contract of `dsClearBucketsStmt`. -/
def dsClearBucketsContract (c : CBCtx) : Contract where
  pre args mem :=
    args = [c.nextBase, c.headBase, c.degBase, c.lo, c.hi, c.minH] ∧ mem = c.mem0
  post _ _ _ mem' := CBMem c (bucketsCat c.B c.lo (c.hi - c.lo)) c.hi mem'
  cost _ _ := 40 * (bucketsCat c.B c.lo (c.hi - c.lo)).length + 60 * (c.hi - c.lo) + 20

end

end MinCostFlow.DynSpanner.Program
