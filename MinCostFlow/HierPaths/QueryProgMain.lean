module

public import MinCostFlow.HierPaths.Impl
public import MinCostFlow.HierPaths.QueryProgAttach
public import MinCostFlow.HierPaths.QueryProgChoice
public import MinCostFlow.HierPaths.QueryProgEraseProc
public import MinCostFlow.HierPaths.QueryProgWrite
public import MinCostFlow.HierPaths.BuildProgZero

/-!
# GetPath on the hierarchy block

The program reserves space for the output and four step buffers. It copies the first
attachment, routes between the two support terminals, and copies the second attachment.
It erases loops using the position array in the block, writes the result to the output,
and clears the step buffers before returning.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Read a header field of the block in register zero. -/
def queryHeaderExpr (i : ℕ) : Expr :=
  .load (.bin .add (secExpr 0) (.const i))

/-- Erase the loops, write the returned walk, and clear the scratch buffers. -/
def queryFinish (fErase fWrite fZero : ℕ) : Stmt :=
  .call 19 fErase [.reg 7, .reg 8, .reg 18, .reg 1, secExpr 22, .reg 9, .reg 10] ;;
  .call 20 fWrite [.reg 1, .reg 9, .reg 10, .reg 19, .reg 3] ;;
  .call 20 fZero [.reg 7, .bin .mul (.const 4) (.reg 6)] ;;
  .ret (.bin .add (.reg 3) (.bin .add (.bin .mul (.const 2) (.reg 19)) (.const 3)))

/-- Read the depth and walk bound, then reserve the output and the four step buffers. -/
def queryBegin : Stmt :=
  -- Reserve an output of at most `2 * cap + 3` words and four arrays of length `cap`.
  .assign 4 (queryHeaderExpr 7) ;;
  .assign 5 (queryHeaderExpr 10) ;;
  .assign 6 (.bin .mul
    (.bin .add (.bin .shiftLeft (.const 1) (.reg 4)) (.const 1)) (.reg 5)) ;;
  .assign 7 (.bin .add (.reg 3) (.bin .add (.bin .mul (.const 2) (.reg 6)) (.const 3))) ;;
  .assign 8 (.bin .add (.reg 7) (.reg 6)) ;;
  .assign 9 (.bin .add (.reg 8) (.reg 6)) ;;
  .assign 10 (.bin .add (.reg 9) (.reg 6))

/-- An on-walk support entry gives the first endpoint of its connector. -/
def queryRightTerm : Stmt :=
  .cond (.reg 13) (.assign 14 (.load (.bin .add (secExpr 2) (.reg 14)))) .nop

/-- Write the two support attachments and the route to the input step buffers. -/
def queryFill (f : ℕ) : Stmt :=
  -- The left attachment starts at the beginning of the input step buffers.
  .call 11 (f + 1) [.reg 0, .reg 1, .const 2] ;;
  .call 12 f [.reg 0, .reg 1, .const 0, .reg 7, .reg 8, .const 0] ;;
  -- Find the terminal of the right attachment before routing.
  .call 13 (f + 1) [.reg 0, .reg 2, .const 0] ;;
  .call 14 (f + 1) [.reg 0, .reg 2, .const 1] ;;
  queryRightTerm ;;
  .call 15 (f + 3) [.reg 4, .const 0, .reg 12, .reg 14, .reg 11,
    queryBranchExpr (queryHeaderExpr 5) (queryHeaderExpr 6), secExpr 2, secExpr 3, secExpr 10, secExpr 11, queryHeaderExpr 3,
    .reg 7, .reg 8, .reg 0, queryHeaderExpr 5] ;;
  -- The right attachment follows the stored prefix from the support terminal to the target.
  .call 16 (f + 1) [.reg 0, .reg 2, .const 2] ;;
  .call 17 f [.reg 0, .reg 2, .const 1, .reg 7, .reg 8, .reg 15] ;;
  .assign 18 (.bin .add (.reg 15) (.reg 16))

/-- The entry of GetPath. The arguments are the block, two input vertices, and heap pointer.
Helper indices start at `f`. -/
def queryEntryProc (f : ℕ) : Stmt :=
  queryBegin ;;
  queryFill f ;;
  queryFinish (f + 5) (f + 6) (f + 8)

/-- The query entry and its helper bodies. All addresses in the bodies come from registers
or refer to fixed sections of the block. -/
def hierQueryProc : HierProc where
  entry := queryEntryProc
  helpers f := [attachProc (f + 1) (f + 2), entryWordProc, copyProc,
    routeProc (f + 3) (f + 4) (f + 2), pickProc, eraseProc, writeWalkProc (f + 7),
    copyListBody, zeroProc]

/-- Scratch space for GetPath, including the returned walk. -/
noncomputable def hierQuerySpace (a : ℕ) (phiNum phiDen _n _m M : ℕ) : ℕ :=
  6 * gammaHP a ((phiDen + phiNum - 1) / phiNum) M + 3

end MinCostFlow.HierPaths

end

namespace MinCostFlow.HierPaths

public section

/-- Capacity of each scratch array, computed from the leaf depth and connector bound. -/
@[expose] def HierConcrete.queryCapacity (X : HierConcrete) : ℕ := (2 ^ X.depth + 1) * X.H.lam

/-- The reserved arrays fit the hierarchy's query space. -/
theorem HierConcrete.queryCapacity_le_gamma {a d M : ℕ} (X : HierConcrete)
    (hfit : X.H.Fits a d X.m) (hm : X.m ≤ M) :
    X.queryCapacity ≤ gammaHP a d M := by
  apply le_trans _ (pathLen_le_gamma a d hm)
  unfold queryCapacity pathLen
  exact Nat.mul_le_mul
    (Nat.add_le_add_right (Nat.pow_le_pow_right (by decide : 0 < 2) hfit.depth) 1) hfit.lam

/-- Constant-time calls and all linear sweeps fit a single multiple of the query factor.
Here `route` counts model route steps and `k` is the number of steps before erasure. -/
theorem queryHelper_cost_le {a d m M L lam cap route k left right : ℕ}
    (hm : m ≤ M) (hL : L ≤ depthOf m) (hlam : lam ≤ lamOf a d m)
    (hcap : cap ≤ (2 ^ L + 1) * lam) (hr : route ≤ 2 ^ L * (lam + 3))
    (hk : k ≤ cap) (hl : left ≤ lam) (hh : right ≤ lam) :
    60 * left + 60 * right + 700 * route + 145 * k + 60 * cap + 5000 ≤
      10000 * gammaHP a d M := by
  let F := 2 ^ L * (lam + 1)
  have hP : 1 ≤ 2 ^ L := Nat.one_le_two_pow
  have hF : 1 ≤ F := Nat.mul_pos hP (Nat.succ_pos _)
  have hlamF : lam ≤ F := by
    exact (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ hP)
  have hcapF : cap ≤ 2 * F := by
    refine hcap.trans ?_
    have h := Nat.mul_le_mul (show 2 ^ L + 1 ≤ 2 * 2 ^ L by omega) (Nat.le_succ lam)
    simpa only [F, Nat.mul_assoc] using h
  have hrF : route ≤ 3 * F := by
    refine hr.trans ?_
    have h := Nat.mul_le_mul_left (2 ^ L) (show lam + 3 ≤ 3 * (lam + 1) by omega)
    simpa only [F, ← Nat.mul_assoc, Nat.mul_comm (2 ^ L) 3] using h
  have hγ : F ≤ gammaHP a d M := by
    apply le_trans _ (queryFactor_le_gamma a d hm)
    exact Nat.mul_le_mul (Nat.pow_le_pow_right (by decide : 0 < 2) hL)
      (by omega)
  omega

/-- The workspace fits the polynomial space envelope for the hierarchy. -/
theorem hierQuerySpace_form (a : ℕ) : SpaceForm a (hierQuerySpace a) 9 1 := by
  intro phiNum phiDen n m M _ _
  simp only [hierQuerySpace, pow_one]
  omega

/-- All query bodies are deterministic. -/
theorem hierQueryProc_noRand : hierQueryProc.NoRand := by
  intro f
  simp [hierQueryProc, queryEntryProc, queryBegin, queryFill, queryFinish, queryRightTerm, attachProc_noRand, entryWordProc, copyProc,
    routeProc, pickProc, eraseProc, eraseStepBody, pushStep, popTo, writeWalkProc,
    writeWalkTail, copyListBody, zeroProc, copyStepBody, WordRAM.forRange, WordRAM.forUp,
    WordRAM.Stmt.NoRand]

end

end MinCostFlow.HierPaths
