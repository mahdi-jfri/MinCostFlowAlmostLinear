module

public import MinCostFlow.DynSpanner.Program.EmbOps
public import MinCostFlow.DynSpanner.Defs

/-!
# The projection of one affected edge: program and contract

Algorithm 6 (lines 70–77) projects each affected edge `e` with walk `P = Π_{<j}(e)` from
`a = tail e` to `b = head e` onto the touched set `S = S_{j-1}`. Walking along `P` from `a` until
the first vertex of `S` gives `â` and the walk `W₁ = Π_{<j}(e)[a, â]`; walking along the reversed
walk from `b` gives `b̂` and `W₂`. The projected edge is `(â, b̂)` (`proj`, Definition 5.4), and its
embedding walk is `walkRev W₁ ++ [(e, true)] ++ W₂` (`projWalk`).

This file gives the procedure `dsProjEdgeStmt` and its contract `dsProjEdgeContract`. The
procedure uses the walk operations of `EmbOps.lean`: two prefix walks, two reversals and two
concatenations, all in a scratch area of `10 · |P| + 10` words whose size is computed from the
length word of `P` at run time. The proof is in `DynSpannerProj.lean`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

@[expose] public section

/-- The intervals `[lo₁, lo₁ + len₁)` and `[lo₂, lo₂ + len₂)` are disjoint. -/
def IvlDisj (lo₁ len₁ lo₂ len₂ : ℕ) : Prop :=
  lo₁ + len₁ ≤ lo₂ ∨ lo₂ + len₂ ≤ lo₁

/-- Projection of one edge (`args = [gPtr, e, a, b, wPtr, sBitPtr, scr, out]`). Writes `â` at
`out`, `b̂` at `out + 1` and the walk `walkRev W₁ ++ [(e, true)] ++ W₂` at `out + 2`, and returns
the first address after that walk. Registers: `8` holds `|P|`, `9` the block size `2|P| + 1`,
`10`–`14` the scratch blocks, `18` the address `out + 2`. -/
def dsProjEdgeStmt (bEmb : ℕ) : Stmt :=
  .assign 8 (.load (.reg 4)) ;;
  .assign 9 (.bin .add (.bin .add (.reg 8) (.reg 8)) (.const 1)) ;;
  .assign 10 (.bin .add (.reg 6) (.reg 9)) ;;
  .assign 11 (.bin .add (.reg 10) (.reg 9)) ;;
  .assign 12 (.bin .add (.reg 11) (.reg 9)) ;;
  .assign 13 (.bin .add (.reg 12) (.reg 9)) ;;
  .assign 14 (.bin .add (.reg 13) (.const 3)) ;;
  .assign 18 (.bin .add (.reg 7) (.const 2)) ;;
  .call 15 (bEmb + embIdxWalkPrefix) [.reg 0, .reg 2, .reg 4, .reg 5, .reg 6] ;;
  .call 16 (bEmb + embIdxWalkRev) [.reg 4, .reg 10] ;;
  .call 16 (bEmb + embIdxWalkPrefix) [.reg 0, .reg 3, .reg 10, .reg 5, .reg 11] ;;
  .call 17 (bEmb + embIdxWalkRev) [.reg 6, .reg 12] ;;
  .store (.reg 13) (.const 1) ;;
  .store (.bin .add (.reg 13) (.const 1)) (.reg 1) ;;
  .store (.bin .add (.reg 13) (.const 2)) (.const 1) ;;
  .call 17 (bEmb + embIdxWalkConcat) [.reg 12, .reg 13, .reg 14] ;;
  .store (.reg 7) (.reg 15) ;;
  .store (.bin .add (.reg 7) (.const 1)) (.reg 16) ;;
  .call 17 (bEmb + embIdxWalkConcat) [.reg 14, .reg 11, .reg 18] ;;
  .ret (.reg 17)

/-- The procedures of the projection module. -/
def projProcs (bEmb : ℕ) : List Stmt :=
  [dsProjEdgeStmt bEmb]

def projIdxEdge : ℕ := 0

lemma projProcs_noRand (bEmb : ℕ) : ∀ s ∈ projProcs bEmb, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-- The walk `walkRev W₁ ++ [(e, true)] ++ W₂` written by `dsProjEdgeStmt`. -/
def projEdgeWalk (H : MGraph) (e a b : ℕ) (P : List (ℕ × Bool)) (S : Finset ℕ) :
    List (ℕ × Bool) :=
  walkRev (prefixWalk H a P S).2 ++ [(e, true)] ++ (prefixWalk H b (walkRev P) S).2

/-- Contract of `dsProjEdgeStmt` for the walk `P` from `a` to `b` in `H` and the set `S`. The
caller gives a scratch area of `10 · |P| + 10` words at `scr` and an output area of
`4 · |P| + 5` words at `out`; both avoid the graph, the walk and the bit array of `S`. -/
def dsProjEdgeContract (w vCap eCap : ℕ) (H : MGraph) (e a b : ℕ) (P : List (ℕ × Bool))
    (S : Finset ℕ) : Contract where
  pre args mem := ∃ gPtr wPtr sBitPtr scr out,
    args = [gPtr, e, a, b, wPtr, sBitPtr, scr, out] ∧ 16 ≤ 2 ^ w ∧
    gPtr + dynGraphSize vCap eCap < 2 ^ w ∧ wPtr + (2 * P.length + 1) < 2 ^ w ∧
    sBitPtr + vCap < 2 ^ w ∧ scr + (10 * P.length + 10) < 2 ^ w ∧
    out + (4 * P.length + 5) < 2 ^ w ∧
    IvlDisj scr (10 * P.length + 10) out (4 * P.length + 5) ∧
    IvlDisj scr (10 * P.length + 10) gPtr (dynGraphSize vCap eCap) ∧
    IvlDisj scr (10 * P.length + 10) wPtr (2 * P.length + 1) ∧
    IvlDisj scr (10 * P.length + 10) sBitPtr vCap ∧
    IvlDisj out (4 * P.length + 5) gPtr (dynGraphSize vCap eCap) ∧
    IvlDisj out (4 * P.length + 5) wPtr (2 * P.length + 1) ∧
    IvlDisj out (4 * P.length + 5) sBitPtr vCap ∧
    DynGraphAt mem gPtr vCap eCap H ∧ H.IsValid ∧ (∀ v ∈ H.V, v < vCap) ∧
    (∀ e ∈ H.E, e < eCap) ∧ a ∈ H.V ∧ b ∈ H.V ∧ PrefixWalksValid H S eCap a b P ∧ MWalkAt mem wPtr P ∧
    (∀ v < vCap, mem (sBitPtr + v) = if v ∈ S then 1 else 0)
  post args mem ret mem' := ∃ gPtr wPtr sBitPtr scr out,
    args = [gPtr, e, a, b, wPtr, sBitPtr, scr, out] ∧
    mem' out = (prefixWalk H a P S).1 ∧
    mem' (out + 1) = (prefixWalk H b (walkRev P) S).1 ∧
    MWalkAt mem' (out + 2) (projEdgeWalk H e a b P S) ∧
    ret = out + 2 + (2 * (projEdgeWalk H e a b P S).length + 1) ∧
    ∀ addr, (addr < scr ∨ scr + (10 * P.length + 10) ≤ addr) →
      (addr < out ∨ out + 2 + (2 * (projEdgeWalk H e a b P S).length + 1) ≤ addr) →
      mem' addr = mem addr
  cost _ _ := 800 * P.length + 800

/-- With `P = embLt e`, `a = G.tail e` and `b = G.head e`, the two words written by
`dsProjEdgeStmt` are the endpoints of `proj G H embLt S e` (Definition 5.4). -/
lemma proj_eq_prefixWalk (G H : MGraph) (embLt : Embedding) (S : Finset ℕ) (e : ℕ) :
    proj G H embLt S e =
      ((prefixWalk H (G.tail e) (embLt e) S).1,
        (prefixWalk H (G.head e) (walkRev (embLt e)) S).1) := rfl

/-- With `P = embLt e`, `a = G.tail e` and `b = G.head e`, the walk written by `dsProjEdgeStmt`
is `projWalk G H embLt S e` (Algorithm 6, line 76). -/
lemma projEdgeWalk_eq_projWalk (G H : MGraph) (embLt : Embedding) (S : Finset ℕ) (e : ℕ) :
    projEdgeWalk H e (G.tail e) (G.head e) (embLt e) S = projWalk G H embLt S e := rfl

end

end MinCostFlow.DynSpanner.Program
