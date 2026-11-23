module

public import MinCostFlow.LinkCut.Prog.MathForestPtrSafe
public import WordRAM.CopyWords

/-!
# Procedure numbers, `LctBaseOk`, and the `init` body

The procedure numbering `LctProcs` and `LctProcs.atBase`, the operation map `LctProcs.op`,
the well-formedness bundle `LctBaseOk`, and the initialization body `lctInitBody`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section ProcsAndBaseOk

/-- Procedure indices of a full `MathForest` Link-Cut tree module inside a `Program`. -/
structure LctProcs where
  init : ℕ
  findRoot : ℕ
  link : ℕ
  cut : ℕ
  pathAdd : ℕ
  pathMin : ℕ
  pathSum : ℕ
  connected : ℕ
  copyWords : ℕ
  expose : ℕ
  reroot : ℕ
  splay : SplayProcs

/-- Contiguous procedure numbering starting at base index `b`. -/
def LctProcs.atBase (b : ℕ) : LctProcs where
  init := b
  findRoot := b + 1
  link := b + 2
  cut := b + 3
  pathAdd := b + 4
  pathMin := b + 5
  pathSum := b + 6
  connected := b + 7
  copyWords := b + 8
  expose := b + 9
  reroot := b + 10
  splay := SplayProcs.atBase (b + 11)

/-- Operation index mapping for `WordRAM.DSRep.Implements` (`0 .. 6`). -/
def LctProcs.op (lp : LctProcs) : ℕ → ℕ
  | 0 => lp.findRoot
  | 1 => lp.link
  | 2 => lp.cut
  | 3 => lp.pathAdd
  | 4 => lp.pathMin
  | 5 => lp.pathSum
  | 6 => lp.connected
  | _ => 0

theorem LctProcs.op_atBase (b i : ℕ) (hi : i < 7) : (LctProcs.atBase b).op i = b + 1 + i := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [LctProcs.op, LctProcs.atBase]

/-- Base program well-formedness witnessing word bounds, `splayBodies`, and `copyWords`. -/
structure LctBaseOk (w h L P : ℕ) (p : Program) (lp : LctProcs) : Prop where
  hh : 0 < h
  hw : 2 * h + 2 ≤ w
  hL : L < 2 ^ w
  hP : P < 2 ^ w
  splay_hasAt : p.HasAt lp.splay.numZero (splayBodies lp.splay h)
  splay_ok : SplayProgramOk w h p lp.splay
  copyWords_ok : MeetsContract w p lp.copyWords (copyWordsContract w)

end ProcsAndBaseOk

section InitProcedure

/-- Deterministic `O(n)` initialization body taking `args = [n, b]`.
Writes the 6-word header, sets `ISV = 1, VCNT = 1` on vertices `1 .. n`, links free edge
slots `n + 1 .. 2 * n` through `OFF_EU`, and returns `b + lctArenaWords n`. -/
def lctInitBody (L P : ℕ) : Stmt :=
  Stmt.assign 2 (.bin .add (.reg 1) (.const LCT_HDR_SIZE)) ;;
  Stmt.assign 3 (.bin .mul (.const 2) (.reg 0)) ;;
  Stmt.assign 4 (.bin .add (.reg 2)
    (.bin .mul (.const NODE_STRIDE) (.bin .add (.reg 3) (.const 1)))) ;;
  Stmt.store (.bin .add (.reg 1) (.const LCT_HDR_N)) (.reg 0) ;;
  Stmt.store (.bin .add (.reg 1) (.const LCT_HDR_CAP)) (.reg 3) ;;
  Stmt.store (.bin .add (.reg 1) (.const LCT_HDR_FREE))
    (.bin .mul (.bin .sub (.const 1) (.bin .eq (.reg 0) (.const 0)))
      (.bin .add (.reg 0) (.const 1))) ;;
  Stmt.store (.bin .add (.reg 1) (.const LCT_HDR_L)) (.const L) ;;
  Stmt.store (.bin .add (.reg 1) (.const LCT_HDR_P)) (.const P) ;;
  Stmt.store (.bin .add (.reg 1) (.const LCT_HDR_HP)) (.reg 4) ;;
  forRange 5 (.const 0) (.reg 0)
    (Stmt.assign 6 (.bin .add (.reg 5) (.const 1)) ;;
     Stmt.assign 7 (nodePtrExpr 2 6) ;;
     Stmt.store (fieldAddrExpr 7 OFF_ISV) (.const 1) ;;
     Stmt.store (fieldAddrExpr 7 OFF_VCNT) (.const 1)) ;;
  forRange 5 (.const 0) (.reg 0)
    (Stmt.assign 6 (.bin .add (.bin .add (.reg 0) (.const 1)) (.reg 5)) ;;
     Stmt.assign 7 (nodePtrExpr 2 6) ;;
     Stmt.store (fieldAddrExpr 7 OFF_EU)
       (.bin .mul (.bin .sub (.const 1) (.bin .eq (.bin .add (.reg 5) (.const 1)) (.reg 0)))
         (.bin .add (.reg 6) (.const 1)))) ;;
  Stmt.ret (.reg 4)

theorem lctInitBody_noRand (L P : ℕ) : (lctInitBody L P).NoRand := by
  simp [lctInitBody, forRange, forUp, nodePtrExpr, fieldAddrExpr, Stmt.NoRand]

theorem runs_seq_normal {w : ℕ} {p : Program} {ω : ℕ → Bool} {s t : Stmt}
    {st st₁ st' : State} {o : Outcome} {c₁ c₂ : ℕ}
    (h1 : Runs w p ω s st .normal st₁ c₁) (h2 : Runs w p ω t st₁ o st' c₂) :
    Runs w p ω (.seq s t) st o st' (c₁ + c₂ + 1) :=
  runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, h1, h2, rfl⟩)

end InitProcedure
end MinCostFlow.LinkCut.Prog
end
