module

public import MinCostFlow.LinkCut.Prog.MathForestLink
public import MinCostFlow.LinkCut.Prog.MathForestCut
public import MinCostFlow.LinkCut.Prog.MathForestPathAdd
public import MinCostFlow.LinkCut.Prog.MathForestPathMin

/-!
# The link-cut tree as one module, and its specification

This file puts all procedures of the link-cut tree into one list (`lctBodies`), shows that none
of them uses random bits (`lctBodies_noRand`), and states what the data structure promises
(`lctDataStructure`). The abstract state is a `MathForest`.

The operations are numbered as in `LctProcs.op`:
`0` findRoot, `1` link, `2` cut, `3` pathAdd, `4` pathMin, `5` pathSum, `6` connected.
Each precondition is the matching clause of `DynForest.IsSpec`, plus the condition that the
numbers the operation produces fit in `L` limbs at precision `P`. Each postcondition is the
matching clause of `DynForest.IsSpec`, with the answer written at the heap pointer.

The amortized cost of operation `i` is `lctOpCoef i L * (log (n + 2) + 1)`, where
`lctOpCoef i L ≤ 450000 * (L + 1)`. Initialization costs `C_LCT_INIT * (n + 1)`.
Allocated space is paid from the same potential as the time, so the space bound of an
operation contains the potential of the memory it starts from.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section LctModuleDefs

/-- All procedures of the link-cut tree, for procedure numbers `LctProcs.atBase b0`. -/
def lctBodies (h L P b0 : ℕ) : List Stmt :=
  [lctInitBody L P, lctFindRootBody (LctProcs.atBase b0), lctLinkBody (LctProcs.atBase b0),
    lctCutBody (LctProcs.atBase b0), lctPathAddBody (LctProcs.atBase b0),
    lctPathMinBody (LctProcs.atBase b0), lctPathSumBody (LctProcs.atBase b0),
    lctConnectedBody (LctProcs.atBase b0), copyWords, exposeBody (LctProcs.atBase b0).splay,
    lctRerootBody (LctProcs.atBase b0)] ++ splayBodies (LctProcs.atBase b0).splay h

/-- The link-cut tree as a program on its own, with procedures from index `0`. -/
def lctProgram (h L P : ℕ) : Program := ⟨lctBodies h L P 0⟩

theorem copyWords_noRand : copyWords.NoRand := by
  simp [copyWords, forRange, forUp, Stmt.NoRand]

/-- No procedure of the link-cut tree uses random bits. -/
theorem lctBodies_noRand (h L P b0 : ℕ) : ∀ s ∈ lctBodies h L P b0, s.NoRand := by
  intro s hs
  simp only [lctBodies, List.cons_append, List.mem_cons, List.nil_append] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hs
  · exact lctInitBody_noRand L P
  · exact lctFindRootBody_noRand _
  · exact lctLinkBody_noRand _
  · exact lctCutBody_noRand _
  · exact lctPathAddBody_noRand _
  · exact lctPathMinBody_noRand _
  · exact lctPathSumBody_noRand _
  · exact lctConnectedBody_noRand _
  · exact copyWords_noRand
  · exact exposeBody_noRand _
  · exact lctRerootBody_noRand _
  · exact splayBodies_noRand _ h s hs

/-- Cost factor of operation `i`: its amortized cost is `lctOpCoef i L * (log (n + 2) + 1)`. -/
def lctOpCoef (i L : ℕ) : ℕ :=
  match i with
  | 0 => C_FINDROOT_OP L
  | 1 => C_LINK_OP L
  | 2 => C_CUT_OP L
  | 3 => C_PATHADD_OP L
  | 4 => C_PATHMIN_OP L
  | 5 => C_PATHSUM_OP L
  | 6 => C_CONNECTED_OP L
  | _ => 0

theorem lctOpCoef_le (i L : ℕ) : lctOpCoef i L ≤ 450000 * (L + 1) := by
  rcases i with _ | _ | _ | _ | _ | _ | _ | i <;>
    simp only [lctOpCoef, C_FINDROOT_OP, C_LINK_OP, C_CUT_OP, C_PATHADD_OP, C_PATHMIN_OP,
      C_PATHSUM_OP, C_CONNECTED_OP] <;> omega

/-- Words of the answer and scratch room that operation `i` needs beyond its cost. -/
def lctOpExtra (i L : ℕ) : ℕ :=
  match i with
  | 0 => 2
  | 1 => 7 * L + 1
  | 2 => 1
  | 3 => L + 1
  | 4 => 2 * L + 5
  | 5 => L + 1
  | 6 => 4
  | _ => 0

/-- The edge that `link` adds, read from `args = [b, u, v, eid, cPtr, fPtr, afPtr, abPtr, hp]`:
the cost is an `L`-limb integer and the three other values are fixed-point numbers. -/
def lctArgEdge (h L P : ℕ) (args : List ℕ) (mem : ℕ → ℕ) : ForestEdge where
  eid := args.getD 3 0
  u := args.getD 1 0
  v := args.getD 2 0
  cost := intVal mem (args.getD 4 0) h L
  flow := fixRat mem (args.getD 5 0) h L P
  availFwd := fixRat mem (args.getD 6 0) h L P
  availBwd := fixRat mem (args.getD 7 0) h L P

/-- The amount that `pathAdd` pushes, read from `args = [b, u, v, dPtr, dNeg, hp]`: the
fixed-point number at `dPtr`, negated when `dNeg = 1`. -/
def lctArgDelta (h L P : ℕ) (args : List ℕ) (mem : ℕ → ℕ) : ℚ :=
  ((if args.getD 4 0 = 0 then intVal mem (args.getD 3 0) h L
    else -intVal mem (args.getD 3 0) h L : ℤ) : ℚ) / (2 : ℚ) ^ P

/-- The answer of `pathMin` at address `a`: `0` if there is no edge, and otherwise `1`, the
edge id, the two ends of the step, the availability and the flow. -/
def LctPathMinAt (h L P : ℕ) (r : Option PathHit) (mem : ℕ → ℕ) (a : ℕ) : Prop :=
  match r with
  | none => mem a = 0
  | some hit =>
      mem a = 1 ∧ mem (a + 1) = hit.eid ∧ mem (a + 2) = hit.x ∧ mem (a + 3) = hit.y ∧
      Valid mem (a + 4) h L ∧ Valid mem (a + 4 + L) h L ∧
      fixRat mem (a + 4) h L P = hit.avail ∧ fixRat mem (a + 4 + L) h L P = hit.flow

/-- Preconditions of the operations. -/
def lctPre (h L P : ℕ) : ℕ → MathForest → List ℕ → (ℕ → ℕ) → Prop
  | 0, F, args, _ => ∃ b v hp, args = [b, v, hp] ∧ v < F.n
  | 1, F, args, mem => ∃ b u v eid cPtr fPtr afPtr abPtr hp,
      args = [b, u, v, eid, cPtr, fPtr, afPtr, abPtr, hp] ∧
      u < F.n ∧ v < F.n ∧ ¬ F.SameComp u v ∧ (∀ e' ∈ F.edges, e'.eid ≠ eid) ∧
      EdgeFits h L P (lctArgEdge h L P args mem) ∧
      Valid mem cPtr h L ∧ cPtr + L ≤ hp ∧ Valid mem fPtr h L ∧ fPtr + L ≤ hp ∧
      Valid mem afPtr h L ∧ afPtr + L ≤ hp ∧ Valid mem abPtr h L ∧ abPtr + L ≤ hp
  | 2, _, args, _ => ∃ b x y hp, args = [b, x, y, hp]
  | 3, F, args, mem => ∃ b u v dPtr dNeg hp, args = [b, u, v, dPtr, dNeg, hp] ∧
      u < F.n ∧ v < F.n ∧ F.SameComp u v ∧ dNeg ≤ 1 ∧ Valid mem dPtr h L ∧ dPtr + L ≤ hp ∧
      ∀ e ∈ (F.pathAdd u v (lctArgDelta h L P args mem)).edges, EdgeFits h L P e
  | 4, F, args, _ => ∃ b u v hp, args = [b, u, v, hp] ∧ u < F.n ∧ v < F.n ∧ F.SameComp u v
  | 5, F, args, _ => ∃ b u v hp, args = [b, u, v, hp] ∧ u < F.n ∧ v < F.n ∧ F.SameComp u v ∧
      Fits h L (F.pathSum u v)
  | 6, F, args, _ => ∃ b u v hp, args = [b, u, v, hp] ∧ u < F.n ∧ v < F.n
  | _, _, _, _ => False

/-- Postconditions of the operations. The answer of a query is at the heap pointer of the
call. -/
def lctPost (h L P : ℕ) : ℕ → MathForest → List ℕ → (ℕ → ℕ) → MathForest → (ℕ → ℕ) → Prop
  | 0, F, args, _, F', mem' => F' = F ∧ mem' (heapArg args) < F.n ∧
      F.SameComp (args.getD 1 0) (mem' (heapArg args))
  | 1, F, args, mem, F', _ => F' = F.link (lctArgEdge h L P args mem)
  | 2, F, args, _, F', _ => F' = F.cut (args.getD 1 0) (args.getD 2 0)
  | 3, F, args, mem, F', _ =>
      F' = F.pathAdd (args.getD 1 0) (args.getD 2 0) (lctArgDelta h L P args mem)
  | 4, F, args, _, F', mem' => F' = F ∧
      LctPathMinAt h L P (F.pathMin (args.getD 1 0) (args.getD 2 0)) mem' (heapArg args)
  | 5, F, args, _, F', mem' => F' = F ∧ Valid mem' (heapArg args) h L ∧
      intVal mem' (heapArg args) h L = F.pathSum (args.getD 1 0) (args.getD 2 0)
  | 6, F, args, _, F', mem' => F' = F ∧ mem' (heapArg args) ≤ 1 ∧
      (mem' (heapArg args) = 1 ↔ F.SameComp (args.getD 1 0) (args.getD 2 0))
  | _, _, _, _, _, _ => False

/-- The link-cut tree as a data structure over `MathForest`. Initialization takes
`args = [n, b]`. Every operation takes the handle `b` first and the heap pointer last. -/
def lctDataStructure (h L P : ℕ) : DataStructure MathForest where
  initPre args _ := ∃ n b, args = [n, b]
  initPost args _ s _ := s = MathForest.empty (args.getD 0 0)
  initCost args _ := C_LCT_INIT * (args.getD 0 0 + 1)
  initSpace args _ := lctArenaWords (args.getD 0 0)
  pre := lctPre h L P
  post := lctPost h L P
  cost i s _ _ := lctOpCoef i L * (Nat.log 2 (s.n + 2) + 1)
  space i s args mem := lctPhi L mem (args.getD 0 0) s.n +
    lctOpCoef i L * (Nat.log 2 (s.n + 2) + 1) + 7000 * (L + 1) * (s.n + 2) + lctOpExtra i L

end LctModuleDefs

end MinCostFlow.LinkCut.Prog
