module

public import MinCostFlow.DynSpanner.Program.EmbOps
public import MinCostFlow.DynSpanner.Program.DynSpannerWalkHelpers

/-!
# Composing a walk with an embedding: program and contract

After the call of `Sparsify`, Algorithm 6 maps the walk `outEmb e` of each affected edge `e` in
the new sparsifier back to `H_{<j} ∪ E_affected`: every edge `x` of the walk is replaced by its
walk `embJH x` (reversed when `x` is used backward). This is `Embedding.comp embJH outEmb e`
(`embMid` in `step`).

The procedure `dsCompEdgeStmt` gets the walk `Q = outEmb e` and an edge-indexed table of
pointers to the walks `T x`. It writes `Q.flatMap (compPiece T)` at `out`. For each `x ∈ Q` it
copies (or reverses) the walk `T x.1` with the existing walk procedures, with destination just
before the free part of the output, so that the length word of the copy lands on the last word
written so far. It saves this word before the call and restores it after. At the end it writes
the length word of the output.

The proof is in `DynSpannerComp.lean`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

@[expose] public section

/-- The walk that replaces the edge `x` of `Q`: `T x.1`, reversed when `x` is used backward. -/
def compPiece (T : Embedding) (x : ℕ × Bool) : List (ℕ × Bool) :=
  if x.2 then T x.1 else walkRev (T x.1)

/-- The composition is the concatenation of the pieces. -/
lemma comp_eq_flatMap (T Q : Embedding) (e : ℕ) :
    Embedding.comp T Q e = (Q e).flatMap (compPiece T) := rfl

lemma compPiece_length (T : Embedding) (x : ℕ × Bool) :
    (compPiece T x).length = (T x.1).length := by
  unfold compPiece; split_ifs <;> simp [walkRev_length]

/-- Loop body of `dsCompEdgeStmt` for the edge at position `reg 5` of `Q`. -/
def dsCompBodyStmt (bEmb : ℕ) : Stmt :=
  .assign 6 (.load (.bin .add (.reg 0) (.bin .add (.bin .mul (.const 2) (.reg 5)) (.const 1)))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.bin .add (.bin .mul (.const 2) (.reg 5)) (.const 2)))) ;;
  .assign 8 (.load (.bin .add (.reg 1) (.reg 6))) ;;
  .assign 12 (.load (.reg 8)) ;;
  .assign 9 (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 4))) ;;
  .assign 10 (.load (.reg 9)) ;;
  .cond (.reg 7)
    (.call 11 (bEmb + embIdxWalkCopy) [.reg 8, .reg 9])
    (.call 11 (bEmb + embIdxWalkRev) [.reg 8, .reg 9]) ;;
  .store (.reg 9) (.reg 10) ;;
  .assign 4 (.bin .add (.reg 4) (.reg 12))

/-- Compose the walk at `qPtr` with the table at `tab` (`args = [qPtr, tab, out]`); returns the
first address after the output. -/
def dsCompEdgeStmt (bEmb : ℕ) : Stmt :=
  .assign 3 (.load (.reg 0)) ;;
  .assign 4 (.const 0) ;;
  forRange 5 (.const 0) (.reg 3) (dsCompBodyStmt bEmb) ;;
  .store (.reg 2) (.reg 4) ;;
  .ret (.bin .add (.reg 2) (.bin .add (.bin .mul (.const 2) (.reg 4)) (.const 1)))

/-- The procedures of the module. -/
def compProcs (bEmb : ℕ) : List Stmt := [dsCompEdgeStmt bEmb]

def compIdxEdge : ℕ := 0

lemma compProcs_noRand (bEmb : ℕ) : ∀ s ∈ compProcs bEmb, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-- Contract of `dsCompEdgeStmt` for the walk `Q` and the walks `T x` of the table. The output
`Q.flatMap (compPiece T)` is written at `out`, an area disjoint from the inputs. -/
def dsCompEdgeContract (w eCap : ℕ) (T : Embedding) (Q : List (ℕ × Bool)) : Contract where
  pre args mem := ∃ qPtr tab out,
    args = [qPtr, tab, out] ∧ 16 ≤ 2 ^ w ∧
    qPtr + (2 * Q.length + 1) < 2 ^ w ∧ tab + eCap < 2 ^ w ∧
    out + (2 * (Q.flatMap (compPiece T)).length + 1) < 2 ^ w ∧
    IvlDisj out (2 * (Q.flatMap (compPiece T)).length + 1) qPtr (2 * Q.length + 1) ∧
    IvlDisj out (2 * (Q.flatMap (compPiece T)).length + 1) tab eCap ∧
    MWalkAt mem qPtr Q ∧
    (∀ x ∈ Q, x.1 < eCap ∧ MWalkAt mem (mem (tab + x.1)) (T x.1) ∧
      mem (tab + x.1) + (2 * (T x.1).length + 1) < 2 ^ w ∧
      IvlDisj out (2 * (Q.flatMap (compPiece T)).length + 1) (mem (tab + x.1))
        (2 * (T x.1).length + 1) ∧
      ∀ y ∈ T x.1, y.1 < eCap)
  post args mem ret mem' := ∃ qPtr tab out,
    args = [qPtr, tab, out] ∧
    MWalkAt mem' out (Q.flatMap (compPiece T)) ∧
    ret = out + (2 * (Q.flatMap (compPiece T)).length + 1) ∧
    ∀ addr, (addr < out ∨ out + (2 * (Q.flatMap (compPiece T)).length + 1) ≤ addr) →
      mem' addr = mem addr
  cost _ _ := 70 * (Q.flatMap (compPiece T)).length + 120 * Q.length + 40

end

end MinCostFlow.DynSpanner.Program
