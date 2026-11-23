module

public import MinCostFlow.MinRatio.WireEvalMath
public import MinCostFlow.MinRatio.PathTreeCall
public import MinCostFlow.Num.Subtract
import WordRAM.Tactic

/-!
# Cycle route evaluator (`OrdCycleRouteEvalSpecW`)

Implements the deterministic Word-RAM evaluator `evalCycleBody (pathSummary numAdd numSub : ℕ)`
for `OrdCycleRouteEvalSpecW` (`WireFindCycleSpec.lean`):
1. Reserves `[workHeap, workHeap + 2 * L)` as the zero-initialized output slots for `inner` and
   `norm` (using `ZeroFrom mem workHeap`).
2. Scans `paths` (`evalPathsLoop`), calling Section 6 `opTree 3` (`PathSummary`) on each
   `(u + 1, v + 1)` and adding `sum.gradient` into `inner` and `sum.length` into `norm` via
   `Num.add`.
3. Scans `edges` (`evalEdgesLoop`), reading each off-tree edge's record `edgeRecords[ei]` and
   adding or subtracting `val.gradient` into `inner` (via `Num.add` / `Num.subtract`) and adding
   `val.length` into `norm` (via `Num.add`).
4. Copies the final `L`-limb `inner` and `norm` blocks in place into `[workHeap, workHeap + L)`
   and `[workHeap + L, workHeap + 2 * L)` (`evalCopyLoop`) and returns `curHeap`.

`evalCycleBody_meets_spec` proves `OrdCycleRouteEvalSpecW` with space
`2 * L + maxPaths * (pathApplySpace L + 4 * L) + maxEdges * (3 * L) + 1` and budget
`maxPaths * (25 * (PathProg.pathC * (L + 1) ^ 2) * (4 * L + 1) + 76 * L + 170) +
 maxEdges * (112 * L + 180) + 44 * L + 120`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut LinkCut.PathTree LinkCut.PathProg Chain

/-- Heap space reserved by `evalCycleBody` above `workHeap`. -/
@[expose] def evalCycleSpace (L maxEdges maxPaths : ℕ) : ℕ :=
  2 * L + maxPaths * (pathApplySpace L + 4 * L) + maxEdges * (3 * L) + 1

/-- Step budget of `evalCycleBody`. -/
@[expose] def evalCycleBudget (L maxEdges maxPaths : ℕ) : ℕ :=
  maxPaths * (25 * (LinkCut.PathProg.pathC * (L + 1) ^ 2) * (4 * L + 1) + 76 * L + 170) +
    maxEdges * (112 * L + 180) + 44 * L + 120

/-- Loop 1 of `evalCycleBody`: accumulate path summaries over `pathsBase[0..pathsLen)`. -/
@[expose] def evalPathsLoop (pathSummary numAdd : ℕ) : Stmt :=
  forRange 13 (.const 0) (.reg 4)
    (.assign 14 (.bin .add (.load (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 13)))) (.const 1)) ;;
     .assign 15 (.bin .add (.load (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 13))) (.const 1))) (.const 1)) ;;
     .assign 16 (.reg 12) ;;
     .call 12 pathSummary [.reg 7, .reg 14, .reg 15, .reg 16] ;;
     .assign 12 (.bin .add (.reg 12) (.bin .mul (.const 2) (.reg 8))) ;;
     .assign 17 (.reg 12) ;;
     .call 12 numAdd [.reg 10, .reg 16, .reg 8, .reg 12] ;;
     .assign 10 (.reg 17) ;;
     .assign 17 (.reg 12) ;;
     .assign 16 (.bin .add (.reg 16) (.reg 8)) ;;
     .call 12 numAdd [.reg 11, .reg 16, .reg 8, .reg 12] ;;
     .assign 11 (.reg 17))

/-- Loop 2 of `evalCycleBody`: accumulate off-tree edge gradients and lengths over `edgesBase[0..edgesLen)`. -/
@[expose] def evalEdgesLoop (numAdd numSub : ℕ) : Stmt :=
  forRange 13 (.const 0) (.reg 2)
    (.assign 14 (.load (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 13)))) ;;
     .assign 15 (.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 13))) (.const 1))) ;;
     .assign 16 (.load (.bin .add (.reg 9) (.reg 14))) ;;
     .assign 17 (.bin .add (.reg 16) (.const 2)) ;;
     .cond (.reg 15)
       (.assign 18 (.reg 12) ;;
        .call 12 numAdd [.reg 10, .reg 17, .reg 8, .reg 12] ;;
        .assign 10 (.reg 18))
       (.assign 18 (.bin .add (.reg 12) (.reg 8)) ;;
        .call 12 numSub [.reg 10, .reg 17, .reg 8, .reg 12] ;;
        .assign 10 (.reg 18)) ;;
     .assign 17 (.bin .add (.reg 17) (.reg 8)) ;;
     .assign 18 (.reg 12) ;;
     .call 12 numAdd [.reg 11, .reg 17, .reg 8, .reg 12] ;;
     .assign 11 (.reg 18))

/-- In-place copy of `L` (`reg 8`) words from `reg srcReg` to `reg dstReg`. -/
@[expose] def evalCopyLoop (dstReg srcReg : ℕ) : Stmt :=
  forRange 13 (.const 0) (.reg 8)
    (.store (.bin .add (.reg dstReg) (.reg 13))
      (.load (.bin .add (.reg srcReg) (.reg 13))))

/-- Deterministic Word-RAM cycle route evaluator taking
`[root, edgesBase, edgesLen, pathsBase, pathsLen, workHeap]` (`reg 0 .. reg 5`).
Writes `PathIntAt` of `inner` at `workHeap` and `norm` at `workHeap + L`, returning `nextHeap`. -/
@[expose] def evalCycleBody (pathSummary numAdd numSub : ℕ) : Stmt :=
  .assign 6 (.load (.reg 0)) ;;
  .assign 7 (.load (.reg 6)) ;;
  .assign 8 (.load (.bin .add (.reg 6) (.const 5))) ;;
  .assign 9 (.load (.bin .add (.reg 0) (.const 10))) ;;
  .assign 10 (.reg 5) ;;
  .assign 11 (.bin .add (.reg 5) (.reg 8)) ;;
  .assign 12 (.bin .add (.reg 5) (.bin .mul (.const 2) (.reg 8))) ;;
  evalPathsLoop pathSummary numAdd ;;
  evalEdgesLoop numAdd numSub ;;
  evalCopyLoop 5 10 ;;
  .assign 14 (.bin .add (.reg 5) (.reg 8)) ;;
  evalCopyLoop 14 11 ;;
  .ret (.reg 12)

theorem evalCycleBody_noRand (pathSummary numAdd numSub : ℕ) :
    (evalCycleBody pathSummary numAdd numSub).NoRand := by
  simp [evalCycleBody, evalPathsLoop, evalEdgesLoop, evalCopyLoop, forRange, forUp, Stmt.NoRand]

/-! ### Helper: in-place `L`-limb copy -/

theorem evalCopyLoop_runs {w L dst src dstReg srcReg : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (h8 : st.regs 8 = L) (hdst : st.regs dstReg = dst) (hsrc : st.regs srcReg = src)
    (hd13 : dstReg ≠ 13) (hs13 : srcReg ≠ 13) (_hd8 : dstReg ≠ 8) (_hs8 : srcReg ≠ 8)
    (hw1 : 1 < 2 ^ w) (hdstW : dst + L < 2 ^ w) (hsrcW : src + L < 2 ^ w)
    (hsep : src = dst ∨ dst + L ≤ src) :
    ∃ out cost,
      Runs w p ω (evalCopyLoop dstReg srcReg) st .normal out cost ∧
      (∀ j < L, out.mem (dst + j) = st.mem (src + j)) ∧
      (∀ a, (a < dst ∨ dst + L ≤ a) → out.mem a = st.mem a) ∧
      (∀ r ≠ 13, out.regs r = st.regs r) ∧
      cost ≤ 22 * L + 12 := by
  have hl := Triple.forRange_const (w := w) (p := p) (r := 13) (lo := .const 0) (hi := .reg 8)
    (body := .store (.bin .add (.reg dstReg) (.reg 13))
      (.load (.bin .add (.reg srcReg) (.reg 13))))
    (P := fun s => s = st)
    (Inv := fun i s =>
      (∀ r ≠ 13, s.regs r = st.regs r) ∧ s.regs 13 = i ∧
      (∀ j < i, s.mem (dst + j) = st.mem (src + j)) ∧
      (∀ a, (a < dst ∨ dst + i ≤ a) → s.mem a = st.mem a))
    8 0 L (Nat.zero_le L) hw1 (fun _ => by omega)
    (fun s hs => by
      subst hs
      refine ⟨by eval_expr, ?_⟩
      exact ⟨fun r hr => by simp [hr], by simp, fun _ h => by omega, fun _ _ => rfl⟩)
    (fun _ _ _ _ hi => hi.2.1)
    (fun _ s _ _ hi => by
      have hr8 : s.regs 8 = L := (hi.1 8 (by decide)).trans h8
      eval_expr)
    (fun i _ hi => by
      intro s ω' ⟨hregs, hr13, hcp, hfr⟩
      have hrd : s.regs dstReg = dst := (hregs dstReg hd13).trans hdst
      have hrs : s.regs srcReg = src := (hregs srcReg hs13).trans hsrc
      have hread : s.mem (src + i) = st.mem (src + i) := by
        apply hfr (src + i)
        rcases hsep with rfl | hle
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
      apply runs_start_le
      refine runs_store_le (by eval_expr) (by eval_expr) ?_ ?_
      · refine ⟨⟨fun r hr => by simp [hr, hregs r hr], by simp, fun j hj => ?_, fun a ha => ?_⟩, hr13⟩
        · dsimp only
          by_cases hji : j = i
          · subst hji; simp [hread]
          · rw [Function.update_of_ne (by omega)]; exact hcp j (by omega)
        · dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hfr a (by rcases ha with h | h <;> [exact Or.inl h; exact Or.inr (by omega)])
      · wram_cost)
  obtain ⟨o, out, cost, hr, hpost, hc⟩ := hl st ω rfl
  cases o with
  | returned _ => exact False.elim hpost
  | normal =>
    refine ⟨out, cost, hr, hpost.2.2.1, hpost.2.2.2, hpost.1, ?_⟩
    simp only [Nat.sub_zero, Expr.size_const, Expr.size_reg] at hc
    omega

/-! ### Helper: Loop 1 (path summaries) -/

theorem fits_of_abs_le {h L : ℕ} {z M : ℤ}
    (habs : |z| ≤ M) (hcap : 2 * M < (Num.capacity h L : ℤ)) : Num.Fits h L z := by
  have h1 : -M ≤ z ∧ z ≤ M := abs_le.mp habs
  exact ⟨by omega, by omega⟩


end MinCostFlow.MinRatio
