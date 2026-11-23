module

public import MinCostFlow.MinRatio.SelectPhiFillEval
import Mathlib.Tactic.Ring

/-!
# Procedure definitions, contracts, and relocatable module for `selectPhiFill` (`SelectPhiFillDefs`)

Defines the deterministic Word-RAM BFS forest-potential fill procedures for level `j` of the
select level blocks (`SelectLevelBlocks.lean`):
* `phiFillEdgeStepBody`: evaluates `potGrad C g φ j f` via `evalLevelPotGradBody` and sets
  `φ_j[child] := φ_j[parent] ± potGrad_j f`.
* `phiFillAdjLoopBody`: scans one parent's doubly-linked incidence list in `F_j`, skipping already
  visited neighbors in `O(1)` time and zero scratch, and discovering unvisited children.
* `phiFillBfsLoopBody`: drains the BFS queue for one connected component of `F_j`.
* `phiFillOuterLoopBody`: scans `F_j`'s live vertex list `dgVListBase`, seeding each unvisited
  vertex as a component root with `φ_j[root] := 0` and running BFS.
* `selectPhiFillBody` (`[meta, j, Lk, scratch]`): allocates `[qTail, visited, queue]` (`1 + 2 * n_j`
  words) on the scratch heap and runs `phiFillOuterLoopBody`.
* Relocatable procedure blocks:
  - `selectPhiFillProcs bAdd bSub bCopy bSelf` (`9` procedures, sharing arithmetic & copy procs)
  - `selectPhiFillModule b h` (`17` procedures, completely self-contained, entry at `b + 16`).

Exact space bound: `selectPhiFillSpace j n Lk = 1 + 2 * n + n * (3 * j + 3) * Lk`.
Exact cost bound: `selectPhiFillCost j n Lk = n * (j * (130 * Lk + 240) + 125 * Lk + 650) + 150`
(`O((n_j + 1) * (j + 1) * Lk)`).
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

/-! ## 1. Procedure bodies -/

/-- Compute `φ_j[child] := φ_j[parent] ± potGrad_j f` (`+` if `dir ≠ 0`, `-` if `dir = 0`).
Args: `[meta, j, f, parent, child, dir, Lk, scratch]` (`reg 0..7`). -/
def phiFillEdgeStepBody (evalLvlProc addProc subProc copyTo : ℕ) : Stmt :=
  .assign 8 (.load (.bin .add (.reg 0) (.const smDOff))) ;;
  .assign 9 (.load (.bin .add (.bin .add (.reg 0) (.const smTableOff))
    (.bin .add (.bin .mul (.const 3) (.bin .add (.reg 8) (.const 1))) (.reg 1)))) ;;
  .assign 10 (.bin .add (.reg 9) (.bin .mul (.reg 3) (.reg 6))) ;;
  .assign 11 (.bin .add (.reg 9) (.bin .mul (.reg 4) (.reg 6))) ;;
  .assign 12 (.bin .add (.reg 7) (.reg 6)) ;;
  .call 13 evalLvlProc [.reg 0, .reg 1, .reg 2, .reg 7, .reg 6, .reg 12] ;;
  .cond (.reg 5)
    (.call 14 addProc [.reg 10, .reg 7, .reg 6, .reg 13] ;;
     .call 15 copyTo [.reg 13, .reg 11, .reg 6] ;;
     .ret (.reg 14))
    (.call 14 subProc [.reg 10, .reg 7, .reg 6, .reg 13] ;;
     .call 15 copyTo [.bin .add (.reg 13) (.reg 6), .reg 11, .reg 6] ;;
     .ret (.reg 14))

/-- Scan the doubly-linked incidence list of `parent` starting from half-edge cursor `cur`
(`0 = NIL`, `h + 1` for half-edge `h`). Unvisited neighbors are marked, enqueued, and assigned
their potential via `edgeStepProc`.
Args: `[meta, j, fPtr, parent, cur, visPtr, qPtr, qTailPtr, Lk, scratch]` (`reg 0..9`). -/
def phiFillAdjLoopBody (self edgeStepProc : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 4) (.const 0))
    (.ret (.reg 9))
    (.assign 10 (.bin .sub (.reg 4) (.const 1)) ;;
     .assign 11 (.bin .div (.reg 10) (.const 2)) ;;
     .assign 12 (.bin .mod (.reg 10) (.const 2)) ;;
     .assign 13 (.load (.reg 2)) ;;
     .assign 14 (.load (.bin .add (.reg 2) (.const 1))) ;;
     .assign 15 (.bin .add (.bin .add (.reg 2) (.const 4)) (.bin .mul (.const 7) (.reg 13))) ;;
     .assign 16 (.load (.bin .add (.bin .add (.reg 15) (.bin .mul (.const 7) (.reg 14))) (.reg 10))) ;;
     .assign 17 (.load (.bin .add (.bin .add (.reg 15)
       (.bin .mul (.bin .sub (.const 4) (.reg 12)) (.reg 14))) (.reg 11))) ;;
     .assign 18 (.load (.bin .add (.bin .add (.bin .add (.reg 2) (.const 4))
       (.bin .mul (.const 4) (.reg 13))) (.reg 17))) ;;
     .assign 19 (.load (.bin .add (.bin .add (.bin .add (.reg 2) (.const 4))
       (.bin .mul (.const 2) (.reg 13))) (.reg 18))) ;;
     .assign 20 (.load (.bin .add (.reg 5) (.reg 19))) ;;
     .cond (.bin .eq (.reg 20) (.const 0))
       (.store (.bin .add (.reg 5) (.reg 19)) (.const 1) ;;
        .assign 21 (.load (.reg 7)) ;;
        .store (.bin .add (.reg 6) (.reg 21)) (.reg 18) ;;
        .store (.reg 7) (.bin .add (.reg 21) (.const 1)) ;;
        .call 9 edgeStepProc [.reg 0, .reg 1, .reg 11, .reg 3, .reg 18, .reg 12, .reg 8, .reg 9])
       .nop ;;
     .call 22 self [.reg 0, .reg 1, .reg 2, .reg 3, .reg 16, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9] ;;
     .ret (.reg 22))

/-- Drain the BFS queue from `qHead` to `mem qTailPtr`, scanning each popped vertex's incidence list.
Args: `[meta, j, fPtr, visPtr, qPtr, qHead, qTailPtr, Lk, scratch]` (`reg 0..8`). -/
def phiFillBfsLoopBody (self adjLoopProc : ℕ) : Stmt :=
  .assign 9 (.load (.reg 6)) ;;
  .cond (.bin .lt (.reg 5) (.reg 9))
    (.assign 10 (.load (.bin .add (.reg 4) (.reg 5))) ;;
     .assign 11 (.load (.reg 2)) ;;
     .assign 12 (.load (.bin .add (.bin .add (.bin .add (.reg 2) (.const 4))
       (.bin .mul (.const 3) (.reg 11))) (.reg 10))) ;;
     .assign 13 (.load (.bin .add (.bin .add (.bin .add (.reg 2) (.const 4))
       (.bin .mul (.const 6) (.reg 11))) (.reg 12))) ;;
     .call 14 adjLoopProc [.reg 0, .reg 1, .reg 2, .reg 10, .reg 13, .reg 3, .reg 4, .reg 6, .reg 7, .reg 8] ;;
     .call 15 self [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .bin .add (.reg 5) (.const 1), .reg 6, .reg 7, .reg 14] ;;
     .ret (.reg 15))
    (.ret (.reg 8))

/-- Outer loop over live vertex indices `idx .. n - 1` of `F_j`: for each unvisited vertex, zeroes
its potential slot, pushes it as a component root, and drains its component via `bfsLoopProc`.
Args: `[meta, j, fPtr, phiJ, vListBase, n, idx, visPtr, qPtr, qTailPtr, Lk, scratch]` (`reg 0..11`). -/
def phiFillOuterLoopBody (self bfsLoopProc zeroLimbsProc : ℕ) : Stmt :=
  .cond (.bin .lt (.reg 6) (.reg 5))
    (.assign 12 (.load (.bin .add (.reg 7) (.reg 6))) ;;
     .cond (.bin .eq (.reg 12) (.const 0))
       (.assign 13 (.load (.bin .add (.reg 4) (.reg 6))) ;;
        .store (.bin .add (.reg 7) (.reg 6)) (.const 1) ;;
        .call 14 zeroLimbsProc [.bin .add (.reg 3) (.bin .mul (.reg 13) (.reg 10)), .reg 10] ;;
        .assign 15 (.load (.reg 9)) ;;
        .store (.bin .add (.reg 8) (.reg 15)) (.reg 13) ;;
        .store (.reg 9) (.bin .add (.reg 15) (.const 1)) ;;
        .call 16 bfsLoopProc [.reg 0, .reg 1, .reg 2, .reg 7, .reg 8, .reg 15, .reg 9, .reg 10, .reg 11] ;;
        .call 17 self [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5,
          .bin .add (.reg 6) (.const 1), .reg 7, .reg 8, .reg 9, .reg 10, .reg 16] ;;
        .ret (.reg 17))
       (.call 17 self [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5,
          .bin .add (.reg 6) (.const 1), .reg 7, .reg 8, .reg 9, .reg 10, .reg 11] ;;
        .ret (.reg 17)))
    (.ret (.reg 11))

/-- Entry point for `selectPhiFill`: fills `φ_j` at `mloc.phiPtr j` for level `j` by BFS over `F_j`
at `mloc.fPtr j`. Args: `[meta, j, Lk, scratch]` (`reg 0..3`). -/
def selectPhiFillBody (outerLoopProc : ℕ) : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.const smDOff))) ;;
  .assign 5 (.bin .add (.reg 4) (.const 1)) ;;
  .assign 6 (.load (.bin .add (.bin .add (.reg 0) (.const smTableOff))
    (.bin .add (.bin .mul (.const 3) (.reg 5)) (.reg 1)))) ;;
  .assign 7 (.load (.bin .add (.bin .add (.reg 0) (.const smTableOff))
    (.bin .add (.bin .mul (.const 6) (.reg 5)) (.reg 1)))) ;;
  .assign 8 (.load (.reg 7)) ;;
  .assign 9 (.load (.bin .add (.reg 7) (.const 2))) ;;
  .assign 10 (.bin .add (.bin .add (.reg 7) (.const 4)) (.reg 8)) ;;
  .assign 11 (.bin .add (.reg 3) (.const 1)) ;;
  .assign 12 (.bin .add (.reg 11) (.reg 9)) ;;
  .assign 13 (.bin .add (.reg 12) (.reg 9)) ;;
  .call 14 outerLoopProc
    [.reg 0, .reg 1, .reg 7, .reg 6, .reg 10, .reg 9, .const 0, .reg 11, .reg 12, .reg 3, .reg 2, .reg 13] ;;
  .ret (.reg 14)

/-! ## 2. Relocatable deterministic procedure blocks -/

/-- Procedure index offsets inside `selectPhiFillProcs`. -/
def pfIdxZeroLimbs : ℕ := 0
def pfIdxEvalLoop : ℕ := 1
def pfIdxEvalEdge : ℕ := 2
def pfIdxEvalLevel : ℕ := 3
def pfIdxEdgeStep : ℕ := 4
def pfIdxAdjLoop : ℕ := 5
def pfIdxBfsLoop : ℕ := 6
def pfIdxOuterLoop : ℕ := 7
def pfIdxFill : ℕ := 8

/-- Relocatable 9-procedure block for `selectPhiFill` sharing `Num.add` (`bAdd`),
`Num.subtract` (`bSub`), and `copyLimbsToBody` (`bCopy`), placed at `bSelf`:
- `bSelf + 0`: `zeroLimbsBody`
- `bSelf + 1`: `evalEdgePotGradLoopBody`
- `bSelf + 2`: `evalEdgePotGradBody`
- `bSelf + 3`: `evalLevelPotGradBody`
- `bSelf + 4`: `phiFillEdgeStepBody`
- `bSelf + 5`: `phiFillAdjLoopBody`
- `bSelf + 6`: `phiFillBfsLoopBody`
- `bSelf + 7`: `phiFillOuterLoopBody`
- `bSelf + 8`: `selectPhiFillBody` (entry). -/
def selectPhiFillProcs (bAdd bSub bCopy bSelf : ℕ) : List Stmt :=
  [ zeroLimbsBody
  , evalEdgePotGradLoopBody (bSelf + pfIdxEvalLoop) bCopy bAdd bSub
  , evalEdgePotGradBody (bSelf + pfIdxEvalLoop) bCopy
  , evalLevelPotGradBody (bSelf + pfIdxEvalEdge) bCopy
  , phiFillEdgeStepBody (bSelf + pfIdxEvalLevel) bAdd bSub bCopy
  , phiFillAdjLoopBody (bSelf + pfIdxAdjLoop) (bSelf + pfIdxEdgeStep)
  , phiFillBfsLoopBody (bSelf + pfIdxBfsLoop) (bSelf + pfIdxAdjLoop)
  , phiFillOuterLoopBody (bSelf + pfIdxOuterLoop) (bSelf + pfIdxBfsLoop) (bSelf + pfIdxZeroLimbs)
  , selectPhiFillBody (bSelf + pfIdxOuterLoop) ]

theorem selectPhiFillProcs_length (bAdd bSub bCopy bSelf : ℕ) :
    (selectPhiFillProcs bAdd bSub bCopy bSelf).length = 9 := rfl

theorem phiFillEdgeStepBody_noRand (a b c d : ℕ) : (phiFillEdgeStepBody a b c d).NoRand := by
  simp [phiFillEdgeStepBody, Stmt.NoRand]

theorem phiFillAdjLoopBody_noRand (a b : ℕ) : (phiFillAdjLoopBody a b).NoRand := by
  simp [phiFillAdjLoopBody, Stmt.NoRand]

theorem phiFillBfsLoopBody_noRand (a b : ℕ) : (phiFillBfsLoopBody a b).NoRand := by
  simp [phiFillBfsLoopBody, Stmt.NoRand]

theorem phiFillOuterLoopBody_noRand (a b c : ℕ) : (phiFillOuterLoopBody a b c).NoRand := by
  simp [phiFillOuterLoopBody, Stmt.NoRand]

theorem selectPhiFillBody_noRand (a : ℕ) : (selectPhiFillBody a).NoRand := by
  simp [selectPhiFillBody, Stmt.NoRand]

theorem selectPhiFillProcs_noRand (bAdd bSub bCopy bSelf : ℕ) :
    ∀ s ∈ selectPhiFillProcs bAdd bSub bCopy bSelf, s.NoRand := by
  intro s hs
  simp only [selectPhiFillProcs, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact zeroLimbsBody_noRand
  · exact evalEdgePotGradLoopBody_noRand ..
  · exact evalEdgePotGradBody_noRand ..
  · exact evalLevelPotGradBody_noRand ..
  · exact phiFillEdgeStepBody_noRand ..
  · exact phiFillAdjLoopBody_noRand ..
  · exact phiFillBfsLoopBody_noRand ..
  · exact phiFillOuterLoopBody_noRand ..
  · exact selectPhiFillBody_noRand ..

/-- Completely self-contained relocatable 17-procedure module for `selectPhiFill` starting at `b`:
- `b + 0 .. b + 1`: `Num.addModule b h` (length `2`)
- `b + 2 .. b + 6`: `Num.subtractModule (b + 2) h` (length `5`)
- `b + 7`: `copyLimbsToBody` (length `1`)
- `b + 8 .. b + 16`: `selectPhiFillProcs b (b + 2) (b + 7) (b + 8)` (length `9`; entry
  `selectPhiFill` at `b + 16`, `evalEdgePotGrad` at `b + 10`, `evalLevelPotGrad` at `b + 11`). -/
def selectPhiFillModule (b h : ℕ) : List Stmt :=
  Num.addModule b h ++ Num.subtractModule (b + 2) h ++ [copyLimbsToBody] ++
    selectPhiFillProcs b (b + 2) (b + 7) (b + 8)

theorem selectPhiFillModule_length (b h : ℕ) : (selectPhiFillModule b h).length = 17 := by
  simp [selectPhiFillModule, Num.addModule, Num.subtractModule, Num.negateModule,
    selectPhiFillProcs]

theorem selectPhiFillModule_noRand (b h : ℕ) : ∀ s ∈ selectPhiFillModule b h, s.NoRand := by
  intro s hs
  simp only [selectPhiFillModule, List.mem_append, List.mem_singleton] at hs
  rcases hs with ((ha | hsub) | rfl) | hpf
  · exact Num.addModule_noRand b h s ha
  · exact Num.subtractModule_noRand (b + 2) h s hsub
  · exact copyLimbsToBody_noRand
  · exact selectPhiFillProcs_noRand b (b + 2) (b + 7) (b + 8) s hpf

/-! ## 3. Exact space and step-cost bounds and main contract -/

/-- Scratch space per tree edge in `phiFillEdgeStepBody`: `(3 * j + 3) * Lk` words. -/
def phiFillEdgeStepSpace (j Lk : ℕ) : ℕ := (3 * j + 3) * Lk

/-- Step cost per tree edge in `phiFillEdgeStepBody`: `O((j + 1) * Lk)`. -/
def phiFillEdgeStepCost (j Lk : ℕ) : ℕ :=
  j * (130 * Lk + 240) + 110 * Lk + 260

/-- Exact scratch space bound for `selectPhiFill` on a forest with `n` vertices at level `j`:
`1 + 2 * n + n * (3 * j + 3) * Lk` (`O((n + 1) * (j + 1) * Lk)`). -/
def selectPhiFillSpace (j n Lk : ℕ) : ℕ :=
  1 + 2 * n + n * phiFillEdgeStepSpace j Lk

/-- Exact step-cost bound for `selectPhiFill` on a forest with `n` vertices at level `j`:
`n * (j * (130 * Lk + 240) + 125 * Lk + 900) + 200` (`O((n + 1) * (j + 1) * Lk)`). -/
def selectPhiFillCost (j n Lk : ℕ) : ℕ :=
  n * (j * (130 * Lk + 240) + 125 * Lk + 900) + 200

/-- Paper-form asymptotic corollary for `selectPhiFillCost`: at most
`900 * (n + 1) * (j + 1) * (Lk + 1)`. -/
theorem selectPhiFillCost_paper_form (j n Lk : ℕ) :
    selectPhiFillCost j n Lk ≤ 900 * (n + 1) * (j + 1) * (Lk + 1) := by
  unfold selectPhiFillCost
  have h1 : j * (130 * Lk + 240) + 125 * Lk + 900 ≤ 900 * (j + 1) * (Lk + 1) := by nlinarith
  have h2 : n * (j * (130 * Lk + 240) + 125 * Lk + 900) ≤ n * (900 * (j + 1) * (Lk + 1)) :=
    Nat.mul_le_mul_left n h1
  have h3 : 200 ≤ 900 * (j + 1) * (Lk + 1) := by nlinarith
  have h4 : n * (900 * (j + 1) * (Lk + 1)) + 900 * (j + 1) * (Lk + 1) =
      900 * (n + 1) * (j + 1) * (Lk + 1) := by ring
  exact le_trans (Nat.add_le_add h2 h3) (le_of_eq h4)

/-- Contract for `phiFillEdgeStepBody` (`[meta, j, f, parent, child, dir, Lk, scratch]`): writes
`φ_j[child] := φ_j[parent] ± potGrad_j f` (`+` if `dir ≠ 0`, `-` if `dir = 0`). -/
def phiFillEdgeStepContract (w h P : ℕ) (mloc : SelectLevelMetaLoc)
    (C : TreeChain) (g : ℕ → ℝ) (φ : ℕ → ℕ → ℝ) : Contract where
  pre args mem :=
    ∃ j f parent child dir scratch,
      args = [mloc.metaBase, j, f, parent, child, dir, mloc.Lk, scratch] ∧
      16 < 2 ^ w ∧ 0 < h ∧ 2 * h + 2 ≤ w ∧
      j ≤ C.d ∧
      f ∈ (C.G 0).E ∧ f < mloc.eCap 0 ∧
      (∀ k < j, f ∈ (C.G k).E) ∧
      parent < mloc.vCap j ∧ child < mloc.vCap j ∧ parent ≠ child ∧
      mem (smEntryAddr mloc.metaBase mloc.d 3 j) = mloc.phiPtr j ∧
      SelectPhiPrefixAt mem mloc h P C g φ j ∧
      SelectPhiPrefixBelow mloc j scratch ∧
      SelectPhiTargetDisjoint mloc j scratch ∧
      Num.Valid mem (mloc.phiPtr j + parent * mloc.Lk) h mloc.Lk ∧
      PotGradEvalFits h mloc.Lk P C g φ j f ∧
      (let pVal := Num.fixVal mem (mloc.phiPtr j + parent * mloc.Lk) h mloc.Lk P;
       let gVal := potGrad C g φ j f;
       let cVal := if dir ≠ 0 then pVal + gVal else pVal - gVal;
       -(Num.capacity h mloc.Lk : ℝ) ≤ 2 * (cVal * (2 : ℝ) ^ P) ∧
       2 * (cVal * (2 : ℝ) ^ P) < (Num.capacity h mloc.Lk : ℝ)) ∧
      ZeroFrom mem scratch ∧
      scratch + phiFillEdgeStepSpace j mloc.Lk < 2 ^ w
  post args mem ret mem' :=
    let j := args.getD 1 0
    let f := args.getD 2 0
    let parent := args.getD 3 0
    let child := args.getD 4 0
    let dir := args.getD 5 0
    let Lk := args.getD 6 0
    let scratch := args.getD 7 0
    let pVal := Num.fixVal mem (mloc.phiPtr j + parent * Lk) h Lk P
    let gVal := potGrad C g φ j f
    scratch ≤ ret ∧ ret ≤ scratch + phiFillEdgeStepSpace j Lk ∧
    Num.Valid mem' (mloc.phiPtr j + child * Lk) h Lk ∧
    Num.fixVal mem' (mloc.phiPtr j + child * Lk) h Lk P =
      (if dir ≠ 0 then pVal + gVal else pVal - gVal) ∧
    ZeroFrom mem' ret ∧
    (∀ a < scratch,
      (a < mloc.phiPtr j + child * Lk ∨ mloc.phiPtr j + child * Lk + Lk ≤ a) →
      mem' a = mem a)
  cost args _ := phiFillEdgeStepCost (args.getD 1 0) (args.getD 6 0)

/-- Main contract for `selectPhiFillBody` (`[meta, j, Lk, scratch]`): fills `φ_j` at
`mloc.phiPtr j` by BFS traversal of `F_j = (C.activeLSF j).F.F` at `mloc.fPtr j`, establishing
`EdgeValuesAt` for a `φj` that meets `SelectPotInvAt` at level `j` and the tree-edge difference
equation `φj (F_j.tail e) - φj (F_j.head e) = potGrad C g φ j e`, in `O((n_j + 1) * (j + 1) * Lk)`
steps and scratch words. -/
def selectPhiFillContract (w h P : ℕ) (mloc : SelectLevelMetaLoc)
    (C : TreeChain) (G : MGraph) (g ℓ : ℕ → ℝ) (σ σ_mwu γ_ℓ γ_c : ℝ)
    (φ : ℕ → ℕ → ℝ) : Contract where
  pre args mem :=
    ∃ j scratch,
      args = [mloc.metaBase, j, mloc.Lk, scratch] ∧
      16 < 2 ^ w ∧ 0 < h ∧ 2 * h + 2 ≤ w ∧
      C.Holds G ℓ σ σ_mwu γ_ℓ γ_c ∧
      j ≤ C.d ∧
      (∀ e ∈ (C.G 0).E, e < mloc.eCap 0) ∧
      mem (smEntryAddr mloc.metaBase mloc.d 3 j) = mloc.phiPtr j ∧
      mem (smEntryAddr mloc.metaBase mloc.d 6 j) = mloc.fPtr j ∧
      DynGraphAt mem (mloc.fPtr j) (mloc.vCap j) (mloc.eCap j) (C.activeLSF j).F.F ∧
      SelectPhiPrefixAt mem mloc h P C g φ j ∧
      SelectPhiPrefixBelow mloc j scratch ∧
      SelectPhiTargetDisjoint mloc j scratch ∧
      (∀ e ∈ (C.activeLSF j).F.F.E, PotGradEvalFits h mloc.Lk P C g φ j e) ∧
      ForestWalkFits h mloc.Lk P (C.activeLSF j).F.F (potGrad C g φ j) ∧
      ZeroFrom mem scratch ∧
      scratch + selectPhiFillSpace j (C.activeLSF j).F.F.n mloc.Lk < 2 ^ w
  post args mem ret mem' :=
    let j := args.getD 1 0
    let Lk := args.getD 2 0
    let scratch := args.getD 3 0
    let F := (C.activeLSF j).F.F
    scratch ≤ ret ∧ ret ≤ scratch + selectPhiFillSpace j F.n Lk ∧
    ZeroFrom mem' ret ∧
    (∀ a < scratch,
      (a < mloc.phiPtr j ∨ mloc.phiPtr j + mloc.vCap j * Lk ≤ a) →
      mem' a = mem a) ∧
    ∃ φj : ℕ → ℝ,
      EdgeValuesAt mem' (mloc.phiPtr j) h Lk P (C.G j).V φj ∧
      (∀ e ∈ F.E, φj (F.tail e) - φj (F.head e) = potGrad C g φ j e) ∧
      SelectPotInvAt C g (Function.update φ j φj) j ∧
      (∀ v ∈ F.V, ∃ r ∈ F.V, F.Connected v r ∧
        φj v = walkInner (potGrad C g φ j) (F.forestPath v r))
  cost args _ := selectPhiFillCost (args.getD 1 0) ((C.activeLSF (args.getD 1 0)).F.F.n) (args.getD 2 0)

end MinCostFlow.MinRatio
