module

public import WordRAM.Logic
public import WordRAM.Link
public import WordRAM.Tactic
public import MinCostFlow.Spanner.ToolContracts
public import MinCostFlow.Spanner.PathDSContract
public import MinCostFlow.Expander.ConstructExpander
public import MinCostFlow.Expander.WordRAMHelpers
public import MinCostFlow.ExplicitExpander.Program

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Word-RAM Implementation of `ConstructExpander` (Theorem 8.4)

Implements `constructExpanderImpl : Spanner.ConstructExpanderImpl`, from the explicit expander
`MinCostFlow.ExplicitExpander.explicitExpander : Cited.ExplicitExpander`
(deterministic `Stmt.NoRand` procedures, `c_deg_int = 18`) meeting `constructExpanderHeapContract`:

Given `[n, wAddr, h]` (`1 < n`, integer weights `wList` at `wAddr`, `ZeroFrom mem h`):
1. `sumWeightsStmt`: sums `N = wList.sum` into `reg 3`.
2. `setupAddrsStmt` + `buildGroupTableStmt`: writes `groupTable wList` at `grpAddr = h + 2 + 9 * N`,
   and sets `s = grpAddr + N = h + 2 + 10 * N`.
3. Stores `[N]` at `s` and invokes `runner (stripRandProg P_cited) c_cited (b + 1)` on
   `[s, 1, s + 1]`, producing `H.encode` at `s + 2` and returning `top = s + 2 + 2 ^ wordSize c_cited [N]`.
4. `writeMergedGraphStmt`: maps `H.edges` through `groupTable wList` directly into
   `[h, h + 2 + 2 * H.m) ⊆ [h, grpAddr)` to form `GraphAt mem' h (mergeExpander wList H)`,
   preserving `< h` and `ZeroFrom mem' top`, and returning `top`.
-/

public section

namespace MinCostFlow.Expander

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-! ### Machine Statements -/

/-- Sum `n = reg 0` weights starting at `wAddr = reg 1` into `reg 3` (`N`). -/
@[expose] def sumWeightsStmt : Stmt :=
  .assign 3 (.const 0) ;;
  forRange 4 (.const 0) (.reg 0) (
    .assign 3 (.bin .add (.reg 3) (.load (.bin .add (.reg 1) (.reg 4))))
  )

/-- Set `reg 4 := h + 2 + 9 * N` (`grpAddr`), `reg 5 := grpAddr + N` (`s`), `reg 9 := grpAddr`. -/
@[expose] def setupAddrsStmt : Stmt :=
  .assign 4 (.bin .add (.bin .add (.reg 2) (.const 2)) (.bin .mul (.const 9) (.reg 3))) ;;
  .assign 5 (.bin .add (.reg 4) (.reg 3)) ;;
  .assign 9 (.reg 4)

/-- Write `cnt = reg 7` copies of `v = reg 6` starting at `cursor = reg 9`, advancing `reg 9`. -/
@[expose] def writeGroupInnerStmt : Stmt :=
  forRange 8 (.const 0) (.reg 7) (
    .store (.reg 9) (.reg 6) ;;
    .assign 9 (.bin .add (.reg 9) (.const 1))
  )

/-- Write `groupTable wList` at `grpAddr` (`reg 4`), advancing `reg 9` by `N`. -/
@[expose] def buildGroupTableStmt : Stmt :=
  forRange 6 (.const 0) (.reg 0) (
    .assign 7 (.load (.bin .add (.reg 1) (.reg 6))) ;;
    writeGroupInnerStmt
  )

/-- Remap `H.encode` at `s + 2` (`reg 5 + 2`) via `groupTable` at `grpAddr` (`reg 4`) into `h`
(`reg 2`), then return `top = reg 9`. -/
@[expose] def writeMergedGraphStmt : Stmt :=
  .assign 6 (.load (.bin .add (.reg 5) (.const 3))) ;;
  .store (.reg 2) (.reg 0) ;;
  .store (.bin .add (.reg 2) (.const 1)) (.reg 6) ;;
  forRange 7 (.const 0) (.reg 6) (
    .assign 8 (.load (.bin .add (.bin .add (.reg 5) (.const 4)) (.bin .mul (.const 2) (.reg 7)))) ;;
    .assign 10 (.load (.bin .add (.reg 4) (.reg 8))) ;;
    .store (.bin .add (.bin .add (.reg 2) (.const 2)) (.bin .mul (.const 2) (.reg 7))) (.reg 10) ;;
    .assign 8 (.load (.bin .add (.bin .add (.reg 5) (.const 5)) (.bin .mul (.const 2) (.reg 7)))) ;;
    .assign 10 (.load (.bin .add (.reg 4) (.reg 8))) ;;
    .store (.bin .add (.bin .add (.reg 2) (.const 3)) (.bin .mul (.const 2) (.reg 7))) (.reg 10)
  ) ;;
  .ret (.reg 9)

/-- Entry procedure `b` for `ConstructExpanderImpl`, calling `runner ...` at `b + 1`. -/
@[expose] def constructExpanderEntry (b : ℕ) : Stmt :=
  sumWeightsStmt ;;
  setupAddrsStmt ;;
  buildGroupTableStmt ;;
  .store (.reg 5) (.reg 3) ;;
  .call 9 (b + 1) [.reg 5, .const 1, .bin .add (.reg 5) (.const 1)] ;;
  writeMergedGraphStmt

/-- Complete procedure list for `ConstructExpanderImpl` at base `b`. -/
@[expose] def constructExpanderProcs (P : Program) (c b : ℕ) : List Stmt :=
  constructExpanderEntry b :: runner (stripRandProg P) c (b + 1)

lemma constructExpanderEntry_noRand (b : ℕ) : (constructExpanderEntry b).NoRand := by
  simp [constructExpanderEntry, sumWeightsStmt, setupAddrsStmt, buildGroupTableStmt,
    writeGroupInnerStmt, writeMergedGraphStmt, forRange, forUp, Stmt.NoRand]

theorem constructExpanderProcs_noRand (P : Program) (c b : ℕ) :
    ∀ s ∈ constructExpanderProcs P c b, s.NoRand := by
  intro s hs
  simp only [constructExpanderProcs, List.mem_cons] at hs
  rcases hs with rfl | hs
  · exact constructExpanderEntry_noRand b
  · exact runner_noRand (stripRandProg_isDeterministic P) c (b + 1) s hs

/-! ### List & Expander Helpers -/

private lemma list_take_sum_le (l : List ℕ) (i : ℕ) : (l.take i).sum ≤ l.sum := by
  conv_rhs => rw [← List.take_append_drop i l, List.sum_append]
  omega

private lemma list_take_succ_sum {l : List ℕ} {i : ℕ} (hi : i < l.length) :
    (l.take (i + 1)).sum = (l.take i).sum + l[i] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.sum_append,
    List.sum_singleton]

private lemma list_take_succ_sum_le {l : List ℕ} {i : ℕ} (hi : i < l.length) :
    (l.take i).sum + l[i] ≤ l.sum := by
  rw [← list_take_succ_sum hi]
  exact list_take_sum_le l (i + 1)

private lemma groupTable_append_singleton (l : List ℕ) (x : ℕ) :
    groupTable (l ++ [x]) = groupTable l ++ List.replicate x l.length := by
  unfold groupTable
  simp only [List.length_append, List.length_singleton, List.range_succ, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hpref : ((List.range l.length).flatMap fun v => List.replicate ((l ++ [x]).getD v 0) v) =
      (List.range l.length).flatMap fun v => List.replicate (l.getD v 0) v := by
    apply List.flatMap_congr
    intro v hv
    have hvlt : v < l.length := List.mem_range.mp hv
    simp [List.getD, List.getElem?_append_left hvlt]
  have hlast : (l ++ [x]).getD l.length 0 = x := by simp [List.getD]
  rw [hpref, hlast]

private lemma groupTable_take_succ {l : List ℕ} {i : ℕ} (hi : i < l.length) :
    groupTable (l.take (i + 1)) = groupTable (l.take i) ++ List.replicate l[i] i := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some,
    groupTable_append_singleton, List.length_take_of_le (Nat.le_of_lt hi)]

private lemma rangeCost_le_linear (n A B : ℕ) (l : List ℕ) (hl : l.length = n)
    (stepCost : ℕ → ℕ) (hstep : ∀ i < n, stepCost i ≤ A + B * l.getD i 0) :
    rangeCost stepCost 0 n ≤ A * n + B * l.sum := by
  have hmono : rangeCost stepCost 0 n ≤ rangeCost (fun i => A + B * l.getD i 0) 0 n :=
    rangeCost_mono fun i _ hi => hstep i hi
  have hsplit : rangeCost (fun i => A + B * l.getD i 0) 0 n =
      rangeCost (fun _ => A) 0 n + rangeCost (fun i => B * l.getD i 0) 0 n :=
    rangeCost_add _ _ 0 n
  have hconst : rangeCost (fun _ => A) 0 n = n * A := by simp
  have hconst' : rangeCost (fun _ => A) 0 n = A * n := by rw [hconst, Nat.mul_comm]
  have hsum : rangeCost (fun i => B * l.getD i 0) 0 n = B * l.sum := by
    rw [rangeCost_zero_eq_range]
    clear hmono hsplit hconst hconst' stepCost hstep
    subst hl
    induction l using List.reverseRecOn with
    | nil => simp
    | append_singleton xs x ih =>
      rw [List.length_append, List.length_singleton, List.range_succ, List.map_append,
        List.map_singleton, List.sum_append, List.sum_singleton, List.sum_append,
        List.sum_singleton]
      have hpref : ((List.range xs.length).map fun i => B * (xs ++ [x]).getD i 0) =
          (List.range xs.length).map fun i => B * xs.getD i 0 := by
        apply List.map_congr_left
        intro i hi
        have hilt := List.mem_range.mp hi
        simp [List.getD, List.getElem?_append_left hilt]
      have hlast : (xs ++ [x]).getD xs.length 0 = x := by simp [List.getD]
      rw [hpref, hlast, ih, mul_add]
  omega

private lemma mem_lt_mul_add_two (n N c_cited : ℕ) :
    2 ^ (wordSize c_cited [N] + 1) ≤ 2 * 4 ^ c_cited * (n + N + 2) ^ c_cited := by
  have h1 : 2 ^ wordSize c_cited [N] ≤ (2 * ([N].length + [N].foldr max 0 + 2)) ^ c_cited :=
    two_pow_wordSize_le c_cited [N]
  have h2 : ([N].length + [N].foldr max 0 + 2) = N + 3 := by simp; omega
  have h3 : 2 * (N + 3) ≤ 4 * (n + N + 2) := by omega
  have hpow : (2 * (N + 3)) ^ c_cited ≤ (4 * (n + N + 2)) ^ c_cited :=
    Nat.pow_le_pow_left h3 c_cited
  rw [pow_succ']
  rw [h2] at h1
  calc 2 * 2 ^ wordSize c_cited [N]
      ≤ 2 * (2 * (N + 3)) ^ c_cited := Nat.mul_le_mul_left 2 h1
    _ ≤ 2 * (4 * (n + N + 2)) ^ c_cited := Nat.mul_le_mul_left 2 hpow
    _ = 2 * 4 ^ c_cited * (n + N + 2) ^ c_cited := by rw [mul_pow, ← mul_assoc]

private lemma mergeExpander_edges_of_gt {counts : List ℕ} {H : Graph} (hlen : 1 < counts.length) :
    mergeExpander counts H = ⟨counts.length,
      H.edges.map fun e => ((groupTable counts).getD e.1 0, (groupTable counts).getD e.2 0)⟩ := by
  unfold mergeExpander
  cases h : counts.length with
  | zero => omega
  | succ k =>
    cases k with
    | zero => omega
    | succ _ => simp

/-! ### Stage Triples -/

private lemma sumWeights_triple {w n wAddr h : ℕ} (p : Program) (mem₀ : ℕ → ℕ) (wList : List ℕ)
    (hwlen : wList.length = n) (hlist : ListAt mem₀ wAddr wList)
    (hwaddr : wAddr + n ≤ h) (hbound : h + wList.sum + 2 < 2 ^ w) :
    Triple w p
      (fun st => st.regs 0 = n ∧ st.regs 1 = wAddr ∧ st.regs 2 = h ∧ st.mem = mem₀)
      sumWeightsStmt
      (normalPost fun st =>
        st.regs 0 = n ∧ st.regs 1 = wAddr ∧ st.regs 2 = h ∧ st.regs 3 = wList.sum ∧ st.mem = mem₀)
      (fun _ => 28 * n + 15) := by
  have hw2 : 1 < 2 ^ w := by omega
  have h1 : Triple w p
      (fun st => st.regs 0 = n ∧ st.regs 1 = wAddr ∧ st.regs 2 = h ∧ st.mem = mem₀)
      (.assign 3 (.const 0))
      (normalPost fun st =>
        st.regs 0 = n ∧ st.regs 1 = wAddr ∧ st.regs 2 = h ∧ st.regs 3 = 0 ∧ st.mem = mem₀)
      (fun _ => 2) := by
    refine Triple.assign (fun st hP => by eval_expr) ?_
    intro st ⟨h0, h1', h2, hm⟩
    simp [h0, h1', h2, hm]
  have hloop := Triple.forRange_const (p := p) (r := 4) (lo := .const 0) (hi := .reg 0)
    (body := .assign 3 (.bin .add (.reg 3) (.load (.bin .add (.reg 1) (.reg 4)))))
    (P := fun st => st.regs 0 = n ∧ st.regs 1 = wAddr ∧ st.regs 2 = h ∧ st.regs 3 = 0 ∧
      st.mem = mem₀)
    (Inv := fun i st => st.regs 0 = n ∧ st.regs 1 = wAddr ∧ st.regs 2 = h ∧
      st.regs 3 = (wList.take i).sum ∧ st.regs 4 = i ∧ st.mem = mem₀)
    9 0 n (Nat.zero_le n) hw2 (fun _ => by omega)
    (fun st ⟨h0, h1', h2, h3, hm⟩ =>
      ⟨by eval_expr, by simp [h0, h1', h2, h3, hm]⟩)
    (fun _ st _ _ hInv => hInv.2.2.2.2.1)
    (fun _ st _ _ hInv => by have := hInv.1; eval_expr)
    (fun i hi₀ hilt => by
      intro st ω ⟨h0, h1', h2, h3, h4, hm⟩
      have hi_lt : i < wList.length := hwlen ▸ hilt
      have hmval : st.mem (wAddr + i) = wList[i] := by
        rw [hm]; exact hlist.getElem hi_lt
      have hidx_lt : wAddr + i < 2 ^ w := by omega
      have hmval_lt : st.mem (wAddr + i) < 2 ^ w := by
        rw [hmval]
        have hle1 : wList[i] ≤ (wList.take i).sum + wList[i] := Nat.le_add_left _ _
        exact lt_of_le_of_lt (le_trans hle1 (list_take_succ_sum_le hi_lt)) (by omega)
      have hsum_lt : (wList.take i).sum + st.mem (wAddr + i) < 2 ^ w := by
        rw [hmval]
        exact lt_of_le_of_lt (list_take_succ_sum_le hi_lt) (by omega)
      let newVal := (wList.take i).sum + st.mem (wAddr + i)
      refine runs_start_le (runs_assign_le (v := newVal) (by eval_expr) ?_ (by simp [Expr.size]))
      refine ⟨⟨by simp [h0], by simp [h1'], by simp [h2], ?_, by simp, by simp [hm]⟩,
        by simp [h4]⟩
      simp only [newVal, Function.update_self, Function.update_of_ne (by omega : (3 : ℕ) ≠ 4)]
      rw [hmval, list_take_succ_sum hi_lt])
  refine (Triple.seq_normal h1 hloop (T := fun _ => 28 * n + 15)
    (fun _ _ _ _ => by simp only [Nat.sub_zero, Expr.size_const, Expr.size_reg]; omega)).conseq
    (fun _ h => h) ?_ (fun _ _ => le_rfl)
  · intro o st' h
    cases o with
    | returned _ => exact False.elim h
    | normal =>
      rcases h with ⟨h0, h1', h2, h3, _, hm⟩
      rw [← hwlen, List.take_length] at h3
      exact ⟨h0, h1', h2, h3, hm⟩

private lemma setupAddrs_triple {w n wAddr h N : ℕ} (p : Program) (mem₀ : ℕ → ℕ)
    (h16 : 16 ≤ 2 ^ w) (hbound : h + 2 + 10 * N < 2 ^ w) :
    Triple w p
      (fun st => st.regs 0 = n ∧ st.regs 1 = wAddr ∧ st.regs 2 = h ∧ st.regs 3 = N ∧ st.mem = mem₀)
      setupAddrsStmt
      (normalPost fun st =>
        st.regs 0 = n ∧ st.regs 1 = wAddr ∧ st.regs 2 = h ∧ st.regs 3 = N ∧
        st.regs 4 = h + 2 + 9 * N ∧ st.regs 5 = h + 2 + 10 * N ∧
        st.regs 9 = h + 2 + 9 * N ∧ st.mem = mem₀)
      (fun _ => 25) := by
  have h1 : Triple w p
      (fun st => st.regs 0 = n ∧ st.regs 1 = wAddr ∧ st.regs 2 = h ∧ st.regs 3 = N ∧ st.mem = mem₀)
      (.assign 4 (.bin .add (.bin .add (.reg 2) (.const 2)) (.bin .mul (.const 9) (.reg 3))))
      (normalPost fun st =>
        st.regs 0 = n ∧ st.regs 1 = wAddr ∧ st.regs 2 = h ∧ st.regs 3 = N ∧
        st.regs 4 = h + 2 + 9 * N ∧ st.mem = mem₀)
      (fun _ => 10) := by
    refine (Triple.assign (val := fun _ => h + 2 + 9 * N) (fun st ⟨_, _, h2, h3, _⟩ => by
      eval_expr) fun st ⟨h0, h1', h2, h3, hm⟩ => by
      simp [h0, h1', h2, h3, hm]).mono_cost (fun _ _ => by decide)
  have h2 : Triple w p
      (fun st => st.regs 0 = n ∧ st.regs 1 = wAddr ∧ st.regs 2 = h ∧ st.regs 3 = N ∧
        st.regs 4 = h + 2 + 9 * N ∧ st.mem = mem₀)
      (.assign 5 (.bin .add (.reg 4) (.reg 3)) ;; .assign 9 (.reg 4))
      (normalPost fun st =>
        st.regs 0 = n ∧ st.regs 1 = wAddr ∧ st.regs 2 = h ∧ st.regs 3 = N ∧
        st.regs 4 = h + 2 + 9 * N ∧ st.regs 5 = h + 2 + 10 * N ∧
        st.regs 9 = h + 2 + 9 * N ∧ st.mem = mem₀)
      (fun _ => 10) := by
    have h2a : Triple w p
        (fun st => st.regs 0 = n ∧ st.regs 1 = wAddr ∧ st.regs 2 = h ∧ st.regs 3 = N ∧
          st.regs 4 = h + 2 + 9 * N ∧ st.mem = mem₀)
        (.assign 5 (.bin .add (.reg 4) (.reg 3)))
        (normalPost fun st =>
          st.regs 0 = n ∧ st.regs 1 = wAddr ∧ st.regs 2 = h ∧ st.regs 3 = N ∧
          st.regs 4 = h + 2 + 9 * N ∧ st.regs 5 = h + 2 + 10 * N ∧ st.mem = mem₀)
        (fun _ => 4) := by
      refine Triple.assign (val := fun _ => h + 2 + 10 * N) (fun st ⟨_, _, _, h3, h4, _⟩ => by
        rw [show h + 2 + 10 * N = (h + 2 + 9 * N) + N by ring]
        eval_expr) fun st ⟨h0, h1', h2, h3, h4, hm⟩ => by
        simp [h0, h1', h2, h3, h4, hm]
    have h2b : Triple w p
        (fun st => st.regs 0 = n ∧ st.regs 1 = wAddr ∧ st.regs 2 = h ∧ st.regs 3 = N ∧
          st.regs 4 = h + 2 + 9 * N ∧ st.regs 5 = h + 2 + 10 * N ∧ st.mem = mem₀)
        (.assign 9 (.reg 4))
        (normalPost fun st =>
          st.regs 0 = n ∧ st.regs 1 = wAddr ∧ st.regs 2 = h ∧ st.regs 3 = N ∧
          st.regs 4 = h + 2 + 9 * N ∧ st.regs 5 = h + 2 + 10 * N ∧
          st.regs 9 = h + 2 + 9 * N ∧ st.mem = mem₀)
        (fun _ => 2) := by
      refine Triple.assign (val := fun _ => h + 2 + 9 * N) (fun st ⟨_, _, _, _, h4, _, _⟩ => by
        eval_expr) fun st ⟨h0, h1', h2, h3, h4, h5, hm⟩ => by
        simp [h0, h1', h2, h3, h4, h5, hm]
    exact Triple.seq_normal h2a h2b (fun _ _ _ _ => by omega)
  exact Triple.seq_normal h1 h2 (fun _ _ _ _ => by omega)

private lemma writeGroupInner_triple {w n wAddr h N grpAddr s v cnt cursor₀ : ℕ}
    (p : Program) (mem_init : ℕ → ℕ)
    (hbound : s + 1 < 2 ^ w) (hcur_le : cursor₀ + cnt ≤ s) (_hv_lt : v < 2 ^ w) :
    Triple w p
      (fun st => st.regs 0 = n ∧ st.regs 1 = wAddr ∧ st.regs 2 = h ∧
        st.regs 3 = N ∧ st.regs 4 = grpAddr ∧ st.regs 5 = s ∧
        st.regs 6 = v ∧ st.regs 7 = cnt ∧ st.regs 9 = cursor₀ ∧ st.mem = mem_init)
      writeGroupInnerStmt
      (normalPost fun st =>
        st.regs 0 = n ∧ st.regs 1 = wAddr ∧ st.regs 2 = h ∧
        st.regs 3 = N ∧ st.regs 4 = grpAddr ∧ st.regs 5 = s ∧
        st.regs 6 = v ∧ st.regs 9 = cursor₀ + cnt ∧
        ListAt st.mem cursor₀ (List.replicate cnt v) ∧
        (∀ x, x < cursor₀ ∨ cursor₀ + cnt ≤ x → st.mem x = mem_init x))
      (fun _ => 22 * cnt + 15) := by
  have hw2 : 1 < 2 ^ w := by omega
  have hloop := Triple.forRange_const (p := p) (r := 8) (lo := .const 0) (hi := .reg 7)
    (body := .store (.reg 9) (.reg 6) ;; .assign 9 (.bin .add (.reg 9) (.const 1)))
    (P := fun st => st.regs 0 = n ∧ st.regs 1 = wAddr ∧ st.regs 2 = h ∧
      st.regs 3 = N ∧ st.regs 4 = grpAddr ∧ st.regs 5 = s ∧
      st.regs 6 = v ∧ st.regs 7 = cnt ∧ st.regs 9 = cursor₀ ∧ st.mem = mem_init)
    (Inv := fun j st => st.regs 0 = n ∧ st.regs 1 = wAddr ∧ st.regs 2 = h ∧
      st.regs 3 = N ∧ st.regs 4 = grpAddr ∧ st.regs 5 = s ∧
      st.regs 6 = v ∧ st.regs 7 = cnt ∧ st.regs 8 = j ∧ st.regs 9 = cursor₀ + j ∧
      ListAt st.mem cursor₀ (List.replicate j v) ∧
      (∀ x, x < cursor₀ ∨ cursor₀ + j ≤ x → st.mem x = mem_init x))
    10 0 cnt (Nat.zero_le cnt) hw2 (fun _ => by omega)
    (fun st ⟨h0, h1, h2, h3, h4, h5, h6, h7, h9, hm⟩ =>
      ⟨by eval_expr, by simp [h0, h1, h2, h3, h4, h5, h6, h7, h9, hm, listAt_nil]⟩)
    (fun _ st _ _ hInv => hInv.2.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hInv => by have := hInv.2.2.2.2.2.2.2.1; eval_expr)
    (fun j _ hj_lt => by
      intro st ω ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, hlist, hframe⟩
      refine runs_start_le (runs_seq_store_le (x := cursor₀ + j) (v := v)
        (by eval_expr) (by eval_expr) ?_)
      refine runs_assign_le (v := cursor₀ + j + 1)
        (by eval_expr) ?_ (by simp [Expr.size])
      refine ⟨⟨by simp [h0], by simp [h1], by simp [h2], by simp [h3], by simp [h4],
        by simp [h5], by simp [h6], by simp [h7], by simp, by simp [add_assoc], ?_, ?_⟩,
        by simp [h8]⟩
      · rw [List.replicate_succ']
        simpa [List.length_replicate] using hlist.snoc v
      · intro x hx
        dsimp only
        rw [Function.update_of_ne (by omega)]
        exact hframe x (by omega))
  refine hloop.conseq (fun _ h => h) ?_ ?_
  · intro o st' h
    cases o with
    | returned _ => exact False.elim h
    | normal =>
      rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, _, _, h9, hlist, hframe⟩
      exact ⟨h0, h1, h2, h3, h4, h5, h6, h9, hlist, hframe⟩
  · intro _ _; simp only [Nat.sub_zero, Expr.size_const, Expr.size_reg]; omega

private lemma buildGroupTable_triple {w n wAddr h : ℕ} (p : Program) (mem₀ : ℕ → ℕ)
    (wList : List ℕ) (hwlen : wList.length = n) (hlist₀ : ListAt mem₀ wAddr wList)
    (hwaddr : wAddr + n ≤ h) (hzero₀ : ZeroFrom mem₀ h)
    (hbound : h + 2 + 10 * wList.sum + 1 < 2 ^ w) :
    Triple w p
      (fun st => st.regs 0 = n ∧ st.regs 1 = wAddr ∧ st.regs 2 = h ∧
        st.regs 3 = wList.sum ∧ st.regs 4 = h + 2 + 9 * wList.sum ∧
        st.regs 5 = h + 2 + 10 * wList.sum ∧ st.regs 9 = h + 2 + 9 * wList.sum ∧
        st.mem = mem₀)
      buildGroupTableStmt
      (normalPost fun st =>
        st.regs 0 = n ∧ st.regs 1 = wAddr ∧ st.regs 2 = h ∧
        st.regs 3 = wList.sum ∧ st.regs 4 = h + 2 + 9 * wList.sum ∧
        st.regs 5 = h + 2 + 10 * wList.sum ∧
        ListAt st.mem (h + 2 + 9 * wList.sum) (groupTable wList) ∧
        ZeroFrom st.mem (h + 2 + 10 * wList.sum) ∧
        (∀ x < h + 2 + 9 * wList.sum, st.mem x = mem₀ x))
      (fun _ => 35 * n + 22 * wList.sum + 20) := by
  set N := wList.sum
  set grpAddr := h + 2 + 9 * N
  set s := h + 2 + 10 * N
  have hw2 : 1 < 2 ^ w := by omega
  let stepCost : ℕ → ℕ := fun i => 22 * wList.getD i 0 + 25
  have hloop := Triple.forRange_le (p := p) (r := 6) (lo := .const 0) (hi := .reg 0)
    (body := .assign 7 (.load (.bin .add (.reg 1) (.reg 6))) ;; writeGroupInnerStmt)
    (P := fun st => st.regs 0 = n ∧ st.regs 1 = wAddr ∧ st.regs 2 = h ∧
      st.regs 3 = N ∧ st.regs 4 = grpAddr ∧ st.regs 5 = s ∧ st.regs 9 = grpAddr ∧
      st.mem = mem₀)
    (Inv := fun v st => st.regs 0 = n ∧ st.regs 1 = wAddr ∧ st.regs 2 = h ∧
      st.regs 3 = N ∧ st.regs 4 = grpAddr ∧ st.regs 5 = s ∧ st.regs 6 = v ∧
      st.regs 9 = grpAddr + (wList.take v).sum ∧
      ListAt st.mem grpAddr (groupTable (wList.take v)) ∧
      ZeroFrom st.mem s ∧
      (∀ x < grpAddr, st.mem x = mem₀ x))
    stepCost 0 n (Nat.zero_le n) hw2 (fun _ => by omega)
    (fun st ⟨h0, h1, h2, h3, h4, h5, h9, hm⟩ =>
      ⟨by eval_expr, by
        simp [h0, h1, h2, h3, h4, h5, h9, hm, groupTable, listAt_nil]
        exact hzero₀.mono (by omega)⟩)
    (fun _ st _ _ hInv => hInv.2.2.2.2.2.2.1)
    (fun _ st _ _ hInv => by have := hInv.1; eval_expr)
    (fun v _ hvlt => by
      intro st ω ⟨h0, h1, h2, h3, h4, h5, h6, h9, hgrp, hz, hframe⟩
      have hv_lt : v < wList.length := hwlen ▸ hvlt
      have hmval : st.mem (wAddr + v) = wList[v] := by
        rw [hframe (wAddr + v) (by omega)]
        exact hlist₀.getElem hv_lt
      have hmval_lt : wList[v] < 2 ^ w := by
        have hle1 : wList[v] ≤ (wList.take v).sum + wList[v] := Nat.le_add_left _ _
        exact lt_of_le_of_lt (le_trans hle1 (list_take_succ_sum_le hv_lt)) (by omega)
      have hassign : Triple w p
          (fun st₁ => st₁ = st)
          (.assign 7 (.load (.bin .add (.reg 1) (.reg 6))))
          (normalPost fun st₁ =>
            st₁.regs 0 = n ∧ st₁.regs 1 = wAddr ∧ st₁.regs 2 = h ∧
            st₁.regs 3 = N ∧ st₁.regs 4 = grpAddr ∧ st₁.regs 5 = s ∧
            st₁.regs 6 = v ∧ st₁.regs 7 = wList[v] ∧ st₁.regs 9 = grpAddr + (wList.take v).sum ∧
            st₁.mem = st.mem)
          (fun _ => 5) := by
        refine Triple.assign (val := fun _ => wList[v]) (fun st₁ hEq => by
          subst hEq; eval_expr) ?_
        intro st₁ hEq; subst hEq
        simp [h0, h1, h2, h3, h4, h5, h6, h9]
      have hinner := writeGroupInner_triple (w := w) (n := n) (wAddr := wAddr) (h := h)
        (N := N) (grpAddr := grpAddr) (s := s) (v := v) (cnt := wList[v])
        (cursor₀ := grpAddr + (wList.take v).sum) p st.mem (by omega)
        (by have := list_take_succ_sum_le hv_lt; omega) (by omega)
      have hseq := Triple.seq_normal hassign hinner (T := fun _ => stepCost v)
        (fun _ _ _ _ => by dsimp [stepCost]; rw [List.getD_eq_getElem _ _ hv_lt]; omega)
      refine (hseq.runs ω rfl) |> fun ⟨o, st', c, hr, hq, hc⟩ => ?_
      cases o with
      | returned _ => exact False.elim hq
      | normal =>
        rcases hq with ⟨h0', h1', h2', h3', h4', h5', h6', h9', hrep, hframe'⟩
        refine ⟨.normal, st', c, hr, ⟨⟨h0', h1', h2', h3', h4', h5', by simp, ?_, ?_, ?_, ?_⟩,
          h6'⟩, hc⟩
        · simpa [list_take_succ_sum hv_lt, add_assoc] using h9'
        · rw [groupTable_take_succ hv_lt]
          have hgrp' : ListAt st'.mem grpAddr (groupTable (wList.take v)) := by
            intro j hj
            have hj' : j < (wList.take v).sum := by rwa [groupTable_length] at hj
            rw [hframe' (grpAddr + j) (by left; omega)]
            exact hgrp j hj
          have hlen_gt : (groupTable (wList.take v)).length = (wList.take v).sum :=
            groupTable_length _
          exact listAt_append.mpr ⟨hgrp', by simpa [hlen_gt, add_assoc] using hrep⟩
        · intro x hx
          rw [hframe' x (by right; have := list_take_succ_sum_le hv_lt; omega)]
          exact hz x hx
        · intro x hx
          rw [hframe' x (by left; omega)]
          exact hframe x hx)
  refine hloop.conseq (fun _ h => h) ?_ ?_
  · intro o st' h
    cases o with
    | returned _ => exact False.elim h
    | normal =>
      rcases h with ⟨h0, h1, h2, h3, h4, h5, _, _, hgrp, hz, hframe⟩
      rw [← hwlen, List.take_length] at hgrp
      exact ⟨h0, h1, h2, h3, h4, h5, hgrp, hz, hframe⟩
  · intro _ _
    have hrc := rangeCost_le_linear n 25 22 wList hwlen stepCost
      (fun i hi => by dsimp [stepCost]; omega)
    simp only [Nat.sub_zero, Expr.size_const, Expr.size_reg] at *
    omega

private lemma writeMergedGraph_triple {w n wAddr h N grpAddr s top : ℕ}
    (p : Program) (mem₀ memRunner : ℕ → ℕ) (wList : List ℕ) (H : Graph)
    (hwlen : wList.length = n) (hn_gt : 1 < n) (hn_le_N : n ≤ N) (hN_eq : N = wList.sum)
    (hgrp_eq : grpAddr = h + 2 + 9 * N) (hs_eq : s = grpAddr + N)
    (hHm_le : 2 * H.m ≤ 9 * N) (hHn : H.n = N) (hHv : H.IsValid)
    (hgrp_lt : s < top) (henc_bound : s + 4 + 2 * H.m < 2 ^ w)
    (htop_bound : top < 2 ^ w) (h16 : 16 ≤ 2 ^ w)
    (hmem_below : ∀ x < h, memRunner x = mem₀ x)
    (hmem_zero : ZeroFrom memRunner top)
    (hmem_grp : ListAt memRunner grpAddr (groupTable wList))
    (hmem_H : GraphAt memRunner (s + 2) H) :
    Triple w p
      (fun st => st.regs 0 = n ∧ st.regs 1 = wAddr ∧ st.regs 2 = h ∧
        st.regs 4 = grpAddr ∧ st.regs 5 = s ∧ st.regs 9 = top ∧ st.mem = memRunner)
      writeMergedGraphStmt
      (retPost fun v st =>
        v = top ∧
        (∀ x < h, st.mem x = mem₀ x) ∧
        ZeroFrom st.mem top ∧
        GraphAt st.mem h (mergeExpander wList H))
      (fun _ => 65 * H.m + 45) := by
  have hw2 : 1 < 2 ^ w := by omega
  have hHm_lt : H.m < 2 ^ w := by omega
  have hn_lt : n < 2 ^ w := by omega
  have hgrp_len : (groupTable wList).length = wList.sum := groupTable_length wList
  have hgrp_lt_bound : ∀ u < H.n, (groupTable wList).getD u 0 < n := by
    intro u hu
    have hu' : u < (groupTable wList).length := by omega
    simpa [hwlen] using groupTable_getD_lt hu'
  have ha : Triple w p
      (fun st => st.regs 0 = n ∧ st.regs 1 = wAddr ∧ st.regs 2 = h ∧
        st.regs 4 = grpAddr ∧ st.regs 5 = s ∧ st.regs 9 = top ∧ st.mem = memRunner)
      (.assign 6 (.load (.bin .add (.reg 5) (.const 3))))
      (normalPost fun st =>
        st.regs 0 = n ∧ st.regs 2 = h ∧ st.regs 4 = grpAddr ∧ st.regs 5 = s ∧
        st.regs 6 = H.m ∧ st.regs 9 = top ∧ st.mem = memRunner)
      (fun _ => 5) := by
    refine Triple.assign (val := fun _ => H.m) (fun st ⟨_, _, _, _, h5, _, hm⟩ => by
      have hmH : st.mem (s + 3) = H.m := by rw [hm]; exact graphAt_m hmem_H
      eval_expr) fun st ⟨h0, _, h2, h4, h5, h9, hm⟩ => by
      simp [h0, h2, h4, h5, h9, hm]
  have hb1 : Triple w p
      (fun st => st.regs 0 = n ∧ st.regs 2 = h ∧ st.regs 4 = grpAddr ∧ st.regs 5 = s ∧
        st.regs 6 = H.m ∧ st.regs 9 = top ∧ st.mem = memRunner)
      (.store (.reg 2) (.reg 0))
      (normalPost fun st =>
        st.regs 0 = n ∧ st.regs 2 = h ∧ st.regs 4 = grpAddr ∧ st.regs 5 = s ∧
        st.regs 6 = H.m ∧ st.regs 9 = top ∧ st.mem h = n ∧
        (∀ x, x ≠ h → st.mem x = memRunner x))
      (fun _ => 5) := by
    intro st ω ⟨h0, h2, h4, h5, h6, h9, hm⟩
    refine runs_start_le (runs_store_le (x := h) (v := n)
      (by eval_expr) (by eval_expr) ?_ (by simp [Expr.size]))
    refine ⟨h0, h2, h4, h5, h6, h9, by simp, fun x hx => ?_⟩
    dsimp only; rw [Function.update_of_ne hx, hm]
  have hb2 : Triple w p
      (fun st => st.regs 0 = n ∧ st.regs 2 = h ∧ st.regs 4 = grpAddr ∧ st.regs 5 = s ∧
        st.regs 6 = H.m ∧ st.regs 9 = top ∧ st.mem h = n ∧
        (∀ x, x ≠ h → st.mem x = memRunner x))
      (.store (.bin .add (.reg 2) (.const 1)) (.reg 6))
      (normalPost fun st =>
        st.regs 0 = n ∧ st.regs 2 = h ∧ st.regs 4 = grpAddr ∧ st.regs 5 = s ∧
        st.regs 6 = H.m ∧ st.regs 9 = top ∧ st.mem h = n ∧ st.mem (h + 1) = H.m ∧
        (∀ x, x < h ∨ h + 2 ≤ x → st.mem x = memRunner x))
      (fun _ => 7) := by
    intro st ω ⟨h0, h2, h4, h5, h6, h9, hmh, hframe⟩
    refine runs_start_le (runs_store_le (x := h + 1) (v := H.m)
      (by eval_expr) (by eval_expr) ?_ (by simp [Expr.size]))
    refine ⟨h0, h2, h4, h5, h6, h9, ?_, ?_, ?_⟩
    · dsimp only; rw [Function.update_of_ne (by omega), hmh]
    · simp
    · intro x hx
      dsimp only
      rw [Function.update_of_ne (by omega)]
      exact hframe x (by omega)
  let Inv : ℕ → State → Prop := fun j st =>
    st.regs 0 = n ∧ st.regs 2 = h ∧ st.regs 4 = grpAddr ∧ st.regs 5 = s ∧
    st.regs 6 = H.m ∧ st.regs 7 = j ∧ st.regs 9 = top ∧
    st.mem h = n ∧ st.mem (h + 1) = H.m ∧
    (∀ k < j, ∃ hk : k < H.m,
      st.mem (h + 2 + 2 * k) = (groupTable wList).getD H.edges[k].1 0 ∧
      st.mem (h + 3 + 2 * k) = (groupTable wList).getD H.edges[k].2 0) ∧
    (∀ x, x < h ∨ h + 2 + 2 * j ≤ x → st.mem x = memRunner x)
  let loopBody : Stmt :=
    .assign 8 (.load (.bin .add (.bin .add (.reg 5) (.const 4)) (.bin .mul (.const 2) (.reg 7)))) ;;
    .assign 10 (.load (.bin .add (.reg 4) (.reg 8))) ;;
    .store (.bin .add (.bin .add (.reg 2) (.const 2)) (.bin .mul (.const 2) (.reg 7))) (.reg 10) ;;
    .assign 8 (.load (.bin .add (.bin .add (.reg 5) (.const 5)) (.bin .mul (.const 2) (.reg 7)))) ;;
    .assign 10 (.load (.bin .add (.reg 4) (.reg 8))) ;;
    .store (.bin .add (.bin .add (.reg 2) (.const 3)) (.bin .mul (.const 2) (.reg 7))) (.reg 10)
  have hloop := Triple.forRange_const (p := p) (r := 7) (lo := .const 0) (hi := .reg 6)
    (body := loopBody)
    (P := fun st => st.regs 0 = n ∧ st.regs 2 = h ∧ st.regs 4 = grpAddr ∧ st.regs 5 = s ∧
      st.regs 6 = H.m ∧ st.regs 9 = top ∧ st.mem h = n ∧ st.mem (h + 1) = H.m ∧
      (∀ x, x < h ∨ h + 2 ≤ x → st.mem x = memRunner x))
    (Inv := Inv)
    56 0 H.m (Nat.zero_le H.m) hw2 (fun _ => hHm_lt)
    (fun st ⟨h0, h2, h4, h5, h6, h9, hmh, hmh1, hframe⟩ =>
      ⟨by eval_expr, ⟨h0, h2, h4, h5, h6, by simp, h9, hmh, hmh1,
        fun _ hk => False.elim (Nat.not_lt_zero _ hk), fun x hx => hframe x (by omega)⟩⟩)
    (fun _ st _ _ hInv => hInv.2.2.2.2.2.1)
    (fun _ st _ _ hInv => by have := hInv.2.2.2.2.1; eval_expr)
    (fun j _ hj_lt => by
      intro st ω ⟨h0, h2, h4, h5, h6, h7, h9, hmh, hmh1, hedges, hframe⟩
      have hj_em : j < H.edges.length := hj_lt
      have he_valid := hHv H.edges[j] (List.getElem_mem hj_em)
      have hu_lt : H.edges[j].1 < H.n := he_valid.1
      have hv_lt : H.edges[j].2 < H.n := he_valid.2
      have hgu_lt : (groupTable wList).getD H.edges[j].1 0 < n := hgrp_lt_bound _ hu_lt
      have hgv_lt : (groupTable wList).getD H.edges[j].2 0 < n := hgrp_lt_bound _ hv_lt
      have hmem_s4 : st.mem (s + 4 + 2 * j) = H.edges[j].1 := by
        rw [hframe (s + 4 + 2 * j) (by right; omega),
          show s + 4 + 2 * j = (s + 2) + 2 + 2 * j by omega]
        exact graphAt_edge_fst hmem_H hj_lt
      have hmem_s5 : st.mem (s + 5 + 2 * j) = H.edges[j].2 := by
        rw [hframe (s + 5 + 2 * j) (by right; omega),
          show s + 5 + 2 * j = (s + 2) + 3 + 2 * j by omega]
        exact graphAt_edge_snd hmem_H hj_lt
      have hmem_gu : st.mem (grpAddr + H.edges[j].1) = (groupTable wList).getD H.edges[j].1 0 := by
        rw [hframe (grpAddr + H.edges[j].1) (by right; omega)]
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact hmem_grp.getElem (by omega)
      have hmem_gv : st.mem (grpAddr + H.edges[j].2) = (groupTable wList).getD H.edges[j].2 0 := by
        rw [hframe (grpAddr + H.edges[j].2) (by right; omega)]
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact hmem_grp.getElem (by omega)
      let g1 := (groupTable wList).getD H.edges[j].1 0
      let g2 := (groupTable wList).getD H.edges[j].2 0
      refine runs_start_le (runs_seq_assign_le (v := H.edges[j].1) ?_ ?_)
      · eval_expr
      refine runs_seq_assign_le (v := g1) ?_ ?_
      · eval_expr
      refine runs_seq_store_le (x := h + 2 + 2 * j) (v := g1) ?_ ?_ ?_
      · eval_expr
      · eval_expr
      refine runs_seq_assign_le (v := H.edges[j].2) ?_ ?_
      · have hm_step4 : Function.update st.mem (h + 2 + 2 * j) g1 (s + 5 + 2 * j) = H.edges[j].2 := by
          rw [Function.update_of_ne (by omega), hmem_s5]
        eval_expr
      refine runs_seq_assign_le (v := g2) ?_ ?_
      · have hm_step5 : Function.update st.mem (h + 2 + 2 * j) g1 (grpAddr + H.edges[j].2) = g2 := by
          rw [Function.update_of_ne (by omega), hmem_gv]
        eval_expr
      refine runs_store_le (x := h + 3 + 2 * j) (v := g2) ?_ ?_ ?_ (by simp [Expr.size])
      · eval_expr
      · eval_expr
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · simp [h0]
      · simp [h2]
      · simp [h4]
      · simp [h5]
      · simp [h6]
      · simp
      · simp [h9]
      · dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hmh]
      · dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hmh1]
      · intro k hk
        by_cases hkj : k = j
        · subst hkj
          refine ⟨hj_lt, ?_, ?_⟩
          · dsimp only; rw [Function.update_of_ne (by omega), Function.update_self]; rfl
          · dsimp only; rw [Function.update_self]; rfl
        · obtain ⟨hk_m, hk1, hk2⟩ := hedges k (by omega)
          refine ⟨hk_m, ?_, ?_⟩
          · dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hk1]
          · dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hk2]
      · intro x hx
        dsimp only
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hframe x (by omega)
      · simp [h7])
  intro st ω hpre
  obtain ⟨oa, sta, ca, hra, hqa, hca⟩ := ha st ω hpre
  cases oa with
  | returned _ => exact False.elim hqa
  | normal =>
    obtain ⟨ob1, stb1, cb1, hrb1, hqb1, hcb1⟩ := hb1 sta ω hqa
    cases ob1 with
    | returned _ => exact False.elim hqb1
    | normal =>
      obtain ⟨ob2, stb2, cb2, hrb2, hqb2, hcb2⟩ := hb2 stb1 ω hqb1
      cases ob2 with
      | returned _ => exact False.elim hqb2
      | normal =>
        obtain ⟨o1, st1, c1, hr1, hq1, hc1⟩ := hloop stb2 ω hqb2
        cases o1 with
        | returned _ => exact False.elim hq1
        | normal =>
          rcases hq1 with ⟨h0, h2, h4, h5, h6, h7, h9, hmh, hmh1, hedges, hframe⟩
          have hret : Runs w p ω (.ret (.reg 9)) st1 (.returned top) st1 2 :=
            runs_ret_iff.mpr ⟨top, by eval_expr, rfl, rfl, rfl⟩
          simp only [Nat.sub_zero, Expr.size] at hc1
          refine ⟨.returned top, st1, ca + (cb1 + (cb2 + (c1 + 2 + 1) + 1) + 1) + 1,
            runs_seq_iff.mpr (Or.inr ⟨sta, ca, _, hra,
              runs_seq_iff.mpr (Or.inr ⟨stb1, cb1, _, hrb1,
                runs_seq_iff.mpr (Or.inr ⟨stb2, cb2, _, hrb2,
                  runs_seq_iff.mpr (Or.inr ⟨st1, c1, 2, hr1, hret, rfl⟩), rfl⟩), rfl⟩), rfl⟩),
            ⟨rfl, ?_, ?_, ?_⟩, ?_⟩
          · intro x hx
            rw [hframe x (by left; exact hx)]
            exact hmem_below x hx
          · intro x hx
            rw [hframe x (by right; omega)]
            exact hmem_zero x hx
          · have hw_eq := mergeExpander_edges_of_gt (H := H) (by omega : 1 < wList.length)
            rw [hw_eq]
            refine graphAt_of_cells (by simp [hwlen, hmh]) (by simp [hmh1, Graph.m]) ?_
            intro j hj
            have hj' : j < H.m := by simpa [Graph.m] using hj
            obtain ⟨_, he1, he2⟩ := hedges j hj'
            simp [he1, he2]
            exact ⟨rfl, rfl⟩
          · dsimp only at hca hcb1 hcb2 ⊢
            omega

/-! ### Main Implementation `constructExpanderImpl` -/

/-- Construct a concrete deterministic `Spanner.ConstructExpanderImpl` from `Cited.ExplicitExpander`.
Achieves `c_deg_int = 18` (from `H.deg ≤ 9`), `phiNum = 1`, `cw = 4`, and explicit linear cost
and polynomial space. -/
@[expose] noncomputable def constructExpanderImpl :
    Spanner.ConstructExpanderImpl :=
  let α₀ := Classical.choose MinCostFlow.ExplicitExpander.explicitExpander
  let hrest1 := Classical.choose_spec MinCostFlow.ExplicitExpander.explicitExpander
  let P_cited := Classical.choose hrest1
  let hrest2 := Classical.choose_spec hrest1
  let c_cited := Classical.choose hrest2
  let hrest3 := Classical.choose_spec hrest2
  let K_cited := Classical.choose hrest3
  let hrest4 := Classical.choose_spec hrest3
  let hα_pos : 0 < α₀ := hrest4.1
  let hExpSpec := hrest4.2
  let hα_le_9 : α₀ ≤ 9 := explicitExpander_alpha_le_nine hExpSpec
  let hdiv_pos : 0 < α₀ / 9 := by positivity
  let phiDen := Classical.choose (exists_unit_frac_le hdiv_pos)
  let hphiDen := Classical.choose_spec (exists_unit_frac_le hdiv_pos)
  let space : ℕ → ℕ → ℕ := fun n wSum =>
    15 + 19 * wSum + 2 * 4 ^ c_cited * (n + wSum + 2) ^ c_cited
  let C_space : ℕ := 20 + 2 * 4 ^ c_cited
  let c_space : ℕ := max 1 c_cited
  let K_ce : ℝ :=
    max 0 (600 + (runnerScale P_cited : ℝ) * (2 * max 0 K_cited + 4 * c_cited + 4))
  { phiNum := 1
    phiDen := phiDen
    c_deg_int := 18
    K_ce := K_ce
    cw := 4
    space := space
    C_space := C_space
    c_space := c_space
    hphi_pos := le_rfl
    hphi_le := hphiDen.1
    hc_deg_int := by omega
    hK_ce := le_max_left 0 _
    hcw_pos := by omega
    hC_space := by omega
    hspace_le := by
      intro n wSum
      dsimp only [space, C_space, c_space]
      have hbase1 : 1 ≤ n + wSum + 2 := by omega
      have hp1 : (n + wSum + 2) ^ 1 ≤ (n + wSum + 2) ^ max 1 c_cited :=
        Nat.pow_le_pow_right hbase1 (le_max_left 1 c_cited)
      have hpc : (n + wSum + 2) ^ c_cited ≤ (n + wSum + 2) ^ max 1 c_cited :=
        Nat.pow_le_pow_right hbase1 (le_max_right 1 c_cited)
      have hlin : 15 + 19 * wSum ≤ 20 * (n + wSum + 2) ^ max 1 c_cited := by
        have h1 : 15 + 19 * wSum ≤ 20 * (n + wSum + 2) ^ 1 := by simp; omega
        exact le_trans h1 (Nat.mul_le_mul_left 20 hp1)
      have hexp : 2 * 4 ^ c_cited * (n + wSum + 2) ^ c_cited ≤
          2 * 4 ^ c_cited * (n + wSum + 2) ^ max 1 c_cited :=
        Nat.mul_le_mul_left _ hpc
      rw [Nat.add_mul]
      omega
    procs := constructExpanderProcs P_cited c_cited
    hprocs_nonempty := fun b => by simp [constructExpanderProcs]
    spec := by
      intro w p b hp
      refine meetsContract_of_runs hp.head fun args mem pos ω _ hpre => ?_
      rcases hpre with ⟨⟨n, wAddr, h, wList, rfl, hn_gt, hwaddr, hlist, hwlen, hpos_w, hlog_w⟩,
        hzero_pre, hspace_pre⟩
      simp only [WordRAM.heapArg, List.getLastD_cons, List.getLastD_nil] at hzero_pre hspace_pre
      have hwSum_eq : ((List.range n).map fun v => mem (wAddr + v)).sum = wList.sum := by
        rw [← hwlen]
        exact listAt_range_sum_eq hlist
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hspace_pre
      rw [hwSum_eq] at hspace_pre
      set N := wList.sum
      have hN_ge_n : n ≤ N := by
        calc n = ((List.range n).map fun _ => 1).sum := by simp
          _ ≤ ((List.range n).map fun v => mem (wAddr + v)).sum := by
            apply sum_map_le_sum_map
            intro v hv
            have hv' : v < wList.length := by simpa [hwlen] using List.mem_range.mp hv
            rw [hlist.getElem hv']
            exact hpos_w v hv'
          _ = N := hwSum_eq
      have hN_gt : 1 < N := lt_of_lt_of_le hn_gt hN_ge_n
      have hw_12 : 12 ≤ w := by
        have hlog3 : 3 ≤ Nat.log 2 (n + N + 2) + 1 := by
          have : 2 ≤ Nat.log 2 (n + N + 2) := Nat.le_log_of_pow_le (by omega) (by omega)
          omega
        omega
      have h16 : 16 ≤ 2 ^ w := by
        calc (16 : ℕ) = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega)
      have hws_bound := mem_lt_mul_add_two n N c_cited
      have hbound_top : h + 4 + 10 * N + 2 ^ wordSize c_cited [N] < 2 ^ w := by
        dsimp only [space] at hspace_pre
        have h2p : 2 ^ wordSize c_cited [N] ≤ 2 ^ (wordSize c_cited [N] + 1) := by
          rw [pow_succ']; omega
        omega
      have hbound_run : (h + 2 + 10 * N + 1) + 2 ^ (wordSize c_cited [N] + 1) + 2 ≤ 2 ^ w := by
        dsimp only [space] at hspace_pre
        omega
      obtain ⟨out, cost_cited, hrun_cited, ⟨H, hH_out, hHn, hHv, hHl, hHExp, hHdeg⟩, hcost_cited⟩ :=
        hExpSpec N hN_gt (fun _ => false)
      have hHm_le : 2 * H.m ≤ 9 * N := by
        have hsum_deg := sum_deg_eq_two_mul_m hHv
        have h9 : ∑ u ∈ H.verts, H.deg u ≤ 9 * N := by
          calc ∑ u ∈ H.verts, H.deg u
              ≤ ∑ _u ∈ H.verts, 9 := Finset.sum_le_sum fun u hu =>
                hHdeg u (hHn ▸ Finset.mem_range.mp hu)
            _ = 9 * H.verts.card := by simp [Finset.sum_const, smul_eq_mul, mul_comm]
            _ = 9 * N := by simp [Graph.verts, hHn]
        omega
      have henc_bound : (h + 2 + 10 * N) + 4 + 2 * H.m < 2 ^ w := by
        dsimp only [space] at hspace_pre
        omega
      have hp_run : p.HasAt (b + 1) (runner (stripRandProg P_cited) c_cited (b + 1)) :=
        hasAt_cons_tail hp
      -- Step 1 + Step 2 + Step 3:
      have ht1 := sumWeights_triple (w := w) p mem wList hwlen hlist hwaddr (by omega)
      have ht2 := setupAddrs_triple (w := w) (n := n) (wAddr := wAddr) (h := h) (N := N)
        p mem h16 (by omega)
      have ht3 := buildGroupTable_triple (w := w) p mem wList hwlen hlist hwaddr hzero_pre (by omega)
      obtain ⟨st01, st02, st1, c01, c02, c1, hr01, hr02, hr1, hq1, hc01, hc02, hc1⟩ :
          ∃ st01 st02 st1 c01 c02 c1,
            Runs w p ω sumWeightsStmt (startState [n, wAddr, h] mem pos) .normal st01 c01 ∧
            Runs w p ω setupAddrsStmt st01 .normal st02 c02 ∧
            Runs w p ω buildGroupTableStmt st02 .normal st1 c1 ∧
            (st1.regs 0 = n ∧ st1.regs 1 = wAddr ∧ st1.regs 2 = h ∧ st1.regs 3 = N ∧
              st1.regs 4 = h + 2 + 9 * N ∧ st1.regs 5 = h + 2 + 10 * N ∧
              ListAt st1.mem (h + 2 + 9 * N) (groupTable wList) ∧ ZeroFrom st1.mem (h + 2 + 10 * N) ∧
              ∀ x < h + 2 + 9 * N, st1.mem x = mem x) ∧
            c01 ≤ 28 * n + 15 ∧ c02 ≤ 25 ∧ c1 ≤ 35 * n + 22 * N + 20 := by
        obtain ⟨o01, st01, c01, hr01, hq01, hc01⟩ :=
          ht1 (startState [n, wAddr, h] mem pos) ω
            ⟨by simp [startState], by simp [startState], by simp [startState], rfl⟩
        cases o01 with
        | returned _ => exact False.elim hq01
        | normal =>
          obtain ⟨o02, st02, c02, hr02, hq02, hc02⟩ := ht2 st01 ω hq01
          cases o02 with
          | returned _ => exact False.elim hq02
          | normal =>
            obtain ⟨o1, st1, c1, hr1, hq1, hc1⟩ := ht3 st02 ω hq02
            cases o1 with
            | returned _ => exact False.elim hq1
            | normal =>
              exact ⟨st01, st02, st1, c01, c02, c1, hr01, hr02, hr1, hq1, hc01, hc02, hc1⟩
      rcases hq1 with ⟨h1_0, h1_1, h1_2, h1_3, h1_4, h1_5, hgrp1, hzero1, hframe1⟩
      exact (by
        set grpAddr := h + 2 + 9 * N
        set s := h + 2 + 10 * N
        set top := s + 2 + 2 ^ wordSize c_cited [N]
        have hst_s : Runs w p ω (.store (.reg 5) (.reg 3)) st1 .normal
            { st1 with mem := Function.update st1.mem s N } 3 :=
          runs_store_iff.mpr ⟨s, N, by eval_expr, by eval_expr, rfl, rfl, rfl⟩
        let st1' : State := { st1 with mem := Function.update st1.mem s N }
        have hargs_run : evalArgs w st1' [.reg 5, .const 1, .bin .add (.reg 5) (.const 1)] =
            some [s, 1, s + 1] := by
          simp [evalArgs, Expr.eval, st1', h1_5,
            show 1 < 2 ^ w by omega, show s + 1 < 2 ^ w by omega, BinOp.eval]
        have hlist_s : ListAt st1'.mem s [N] := by
          intro i hi
          simp only [List.length_singleton] at hi
          have hi0 : i = 0 := by omega
          subst hi0
          simp [st1']
        have hzero_s : ZeroFrom st1'.mem (s + 1) := by
          intro x hx
          dsimp [st1']
          rw [Function.update_of_ne (by omega)]
          exact hzero1 x (by omega)
        have hrun_out : RunsTo (wordSize c_cited [N]) P_cited [N] (fun _ => false)
            H.encode cost_cited := hH_out ▸ hrun_cited
        rcases runs_call_runner_stripRand (ω := ω) (r := 9) hp_run hargs_run le_rfl rfl
            hlist_s hzero_s hbound_run hrun_out with
          ⟨st2, c_run, hrun_call, hregs2, hlen2, hout2, hframe2, hzero2, hcost_run⟩
        have hst2_grp : ListAt st2.mem grpAddr (groupTable wList) := by
          intro i hi
          have hilt : i < N := by rwa [groupTable_length] at hi
          rw [hframe2 (grpAddr + i) (by omega)]
          simp only [st1']
          rw [Function.update_of_ne (by omega)]
          exact hgrp1 i hi
        have hst2_below : ∀ x < h, st2.mem x = mem x := by
          intro x hx
          rw [hframe2 x (by omega)]
          dsimp [st1']
          rw [Function.update_of_ne (by omega), hframe1 x (by omega)]
        have hst2_H : GraphAt st2.mem (s + 2) H := hout2
        have hst2_regs : st2.regs 0 = n ∧ st2.regs 1 = wAddr ∧ st2.regs 2 = h ∧
            st2.regs 4 = grpAddr ∧ st2.regs 5 = s ∧ st2.regs 9 = top := by
          rw [hregs2]
          refine ⟨by simp [st1', h1_0], by simp [st1', h1_1], by simp [st1', h1_2],
            by simp [st1', h1_4], by simp [st1', h1_5], ?_⟩
          simp [top, add_assoc]
        have hs_eq : s = grpAddr + N := by dsimp [s, grpAddr]; omega
        have htop_eq : top < 2 ^ w := by dsimp [top, s]; omega
        have hgrp_lt : s < top :=
          Nat.lt_of_lt_of_le (by omega : s < s + 2) (Nat.le_add_right (s + 2) _)
        have ht4 := writeMergedGraph_triple (w := w) (n := n) (wAddr := wAddr) (h := h)
          (N := N) (grpAddr := grpAddr) (s := s) (top := top) p mem st2.mem wList H
          hwlen hn_gt hN_ge_n rfl rfl hs_eq hHm_le hHn hHv hgrp_lt henc_bound htop_eq h16
          hst2_below hzero2 hst2_grp hst2_H
        rcases ht4 st2 ω ⟨hst2_regs.1, hst2_regs.2.1, hst2_regs.2.2.1, hst2_regs.2.2.2.1,
            hst2_regs.2.2.2.2.1, hst2_regs.2.2.2.2.2, rfl⟩ with
          ⟨o3, st3, c4, hr4, hq4, hc4⟩
        cases o3 with
        | normal => exact False.elim hq4
        | returned vret =>
          rcases hq4 with ⟨hv_top, hmem3_below, hzero3, hgraph3⟩
          have hfull_run : Runs w p ω (constructExpanderEntry b) (startState [n, wAddr, h] mem pos)
              (.returned vret) st3 (c01 + (c02 + (c1 + (3 + (c_run + c4 + 1) + 1) + 1) + 1) + 1) :=
            runs_seq_iff.mpr (Or.inr ⟨st01, c01, _, hr01,
              runs_seq_iff.mpr (Or.inr ⟨st02, c02, _, hr02,
                runs_seq_iff.mpr (Or.inr ⟨st1, c1, _, hr1,
                  runs_seq_iff.mpr (Or.inr ⟨st1', 3, _, hst_s,
                    runs_seq_iff.mpr (Or.inr ⟨st2, c_run, c4, hrun_call, hr4, rfl⟩),
                    rfl⟩), rfl⟩), rfl⟩), rfl⟩)
          set W := mergeExpander wList H
          have hcounts : ∀ v < wList.length, 1 ≤ wList.getD v 0 := fun v hv => by
            rw [List.getD_eq_getElem _ _ hv]; exact hpos_w v hv
          have hHn' : H.n = wList.sum := by dsimp [N] at hHn; exact hHn
          have hWn : W.n = n := by rw [mergeExpander_n, hwlen]
          have hWv : W.IsValid := mergeExpander_isValid hHn' hHv
          have hWexp_alpha : W.IsConductanceExpanderOn W.verts (α₀ / 9) :=
            mergeExpander_conductance hcounts hHn' hHv hα_pos hHExp (by simpa [hHn'] using hHdeg)
          have hWexp : W.IsConductanceExpanderOn W.verts ((1 : ℕ) / phiDen : ℝ) := by
            have hle : ((1 : ℕ) : ℝ) / (phiDen : ℝ) ≤ α₀ / 9 := by
              have h := hphiDen.2
              dsimp only [phiDen]
              simpa [one_div] using h
            exact isConductanceExpanderOn_mono hle hWexp_alpha
          have hWdeg : ∀ (v : ℕ) (hv : v < wList.length),
              ((wList[v] : ℕ) : ℝ) ≤ (W.deg v : ℝ) ∧ (W.deg v : ℝ) ≤ (18 : ℕ) * (wList[v] : ℝ) := by
            intro v hv
            have hd := mergeExpander_deg_bounds hcounts hHn' hHv hHl hα_pos hHExp
              (by simpa [hHn'] using hHdeg) v hv
            rw [List.getD_eq_getElem _ _ hv] at hd
            exact ⟨by exact_mod_cast hd.1, by exact_mod_cast le_trans hd.2 (by omega)⟩
          have hcost_total :
              (c01 + (c02 + (c1 + (3 + (c_run + c4 + 1) + 1) + 1) + 1) + 1 : ℝ) ≤
                K_ce * (n + ((List.range n).map fun v => mem (wAddr + v)).sum) := by
            rw [hwSum_eq]
            dsimp only at hc1 hc4
            have hc1_nat : c1 ≤ 65 * n + 25 * N + 65 := by omega
            have hc4_nat : c4 ≤ 300 * N + 45 := by
              have hHm_r : H.m ≤ 5 * N := by omega
              omega
            have hws_le : wordSize c_cited [N] ≤ c_cited * (N + 3) := by
              unfold wordSize
              have hlog : Nat.log 2 ([N].length + [N].foldr max 0 + 2) + 1 ≤ N + 3 := by
                have h2 : [N].length + [N].foldr max 0 + 2 = N + 3 := by simp [List.foldr]; omega
                rw [h2]
                have hlt : Nat.log 2 (N + 3) < N + 3 :=
                  (Nat.log_lt_iff_lt_pow (by decide) (by omega)).mpr Nat.lt_two_pow_self
                omega
              exact Nat.mul_le_mul_left c_cited hlog
            have hcr_nat : c_run ≤ runnerScale P_cited * (2 * cost_cited + wordSize c_cited [N] + 2) + 6 := by
              simp only [Expr.size] at hcost_run
              have hmult : runnerScale P_cited * (2 * cost_cited + 1 + wordSize c_cited [N] + 1) =
                  runnerScale P_cited * (2 * cost_cited + wordSize c_cited [N] + 2) := by ring
              omega
            have hN2_r : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN_gt
            have hn2_r : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_gt
            have hc01_r : (c01 : ℝ) ≤ 28 * n + 15 := by exact_mod_cast hc01
            have hc02_r : (c02 : ℝ) ≤ 25 := by exact_mod_cast hc02
            have hc1_r : (c1 : ℝ) ≤ 65 * n + 25 * N + 65 := by exact_mod_cast hc1_nat
            have hc4_r : (c4 : ℝ) ≤ 300 * N + 45 := by exact_mod_cast hc4_nat
            have hcost_r : (cost_cited : ℝ) ≤ max 0 K_cited * N :=
              le_trans hcost_cited (mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg _))
            have hws_r : (wordSize c_cited [N] : ℝ) ≤ (c_cited : ℝ) * (N + 3) := by exact_mod_cast hws_le
            have hcr_r : (c_run : ℝ) ≤
                (runnerScale P_cited : ℝ) * (2 * max 0 K_cited * N + (c_cited : ℝ) * (N + 3) + 2) + 6 := by
              have h1 : (c_run : ℝ) ≤
                  (runnerScale P_cited : ℝ) * (2 * (cost_cited : ℝ) + (wordSize c_cited [N] : ℝ) + 2) + 6 := by
                exact_mod_cast hcr_nat
              have h2 : 2 * (cost_cited : ℝ) + (wordSize c_cited [N] : ℝ) + 2 ≤
                  2 * max 0 K_cited * N + (c_cited : ℝ) * (N + 3) + 2 := by linarith
              have h3 := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℝ) (runnerScale P_cited))
              linarith
            have hinner_r : 2 * max 0 K_cited * (N : ℝ) + (c_cited : ℝ) * ((N : ℝ) + 3) + 2 ≤
                (2 * max 0 K_cited + 4 * c_cited + 4) * ((n : ℝ) + (N : ℝ)) := by
              have hc_nn : (0 : ℝ) ≤ c_cited := Nat.cast_nonneg _
              have hK_nn : (0 : ℝ) ≤ max 0 K_cited := le_max_left _ _
              nlinarith
            have hscale_r : (runnerScale P_cited : ℝ) * (2 * max 0 K_cited * N + (c_cited : ℝ) * (N + 3) + 2) ≤
                (runnerScale P_cited : ℝ) * (2 * max 0 K_cited + 4 * c_cited + 4) * ((n : ℝ) + (N : ℝ)) := by
              calc (runnerScale P_cited : ℝ) * (2 * max 0 K_cited * N + (c_cited : ℝ) * (N + 3) + 2)
                  ≤ (runnerScale P_cited : ℝ) *
                      ((2 * max 0 K_cited + 4 * c_cited + 4) * ((n : ℝ) + (N : ℝ))) :=
                    mul_le_mul_of_nonneg_left hinner_r (Nat.cast_nonneg (α := ℝ) _)
                _ = (runnerScale P_cited : ℝ) * (2 * max 0 K_cited + 4 * c_cited + 4) *
                      ((n : ℝ) + (N : ℝ)) := by ring
            have hpoly_r : (c01 : ℝ) + (c02 + (c1 + (3 + ((c_run : ℝ) + (c4 : ℝ) + 1) + 1) + 1) + 1) + 1 ≤
                (600 + (runnerScale P_cited : ℝ) * (2 * max 0 K_cited + 4 * c_cited + 4)) *
                  ((n : ℝ) + (N : ℝ)) := by
              linarith
            have hKce_ge : 600 + (runnerScale P_cited : ℝ) * (2 * max 0 K_cited + 4 * c_cited + 4) ≤ K_ce :=
              le_max_right _ _
            have hsum_nn : (0 : ℝ) ≤ (n : ℝ) + (N : ℝ) := by positivity
            have hmul_le := mul_le_mul_of_nonneg_right hKce_ge hsum_nn
            linarith
          have hWm_eq : W.m = H.m := by
            simp only [W, Graph.m, mergeExpander_edges_of_gt (H := H) (by omega : 1 < wList.length),
              List.length_map]
          have hspace_def : space n N = 15 + 19 * N + 2 * 4 ^ c_cited * (n + N + 2) ^ c_cited := rfl
          have htop_le_space : top ≤ h + space n N := by
            have hpow1 : 2 ^ wordSize c_cited [N] ≤ 2 ^ (wordSize c_cited [N] + 1) := by
              rw [pow_succ']; omega
            rw [hspace_def]
            dsimp only [top, s, grpAddr]
            omega
          refine ⟨.returned vret, st3, _, hfull_run, ⟨⟨?_, ?_, hmem3_below, ?_, ?_⟩, ?_⟩, ?_⟩
          · change h ≤ vret
            rw [hv_top]
            dsimp [top, s, grpAddr]
            omega
          · simp only [Outcome.value, WordRAM.heapArg, List.getLastD_cons, List.getLastD_nil,
              List.getD_cons_zero, List.getD_cons_succ, hwSum_eq]
            rw [hv_top]
            exact htop_le_space
          · dsimp only [Outcome.value]
            exact hv_top ▸ hzero3
          · exact ⟨n, wAddr, h, wList, W, rfl, hlist, hwlen, hgraph3, hWn, hWv, hWexp, hWdeg⟩
          · refine ⟨W, hgraph3, ?_⟩
            change h + (2 + 2 * W.m) ≤ vret
            rw [hv_top]
            dsimp only [top, s, grpAddr]
            omega
          · simp only [constructExpanderHeapContract, WordRAM.heapContract,
              List.getD_cons_zero, List.getD_cons_succ]
            exact nat_le_ceil_of_cast_le (by simpa using hcost_total)) }

theorem constructExpanderImpl_noRand (b : ℕ) :
    ∀ s ∈ constructExpanderImpl.procs b, s.NoRand :=
  constructExpanderProcs_noRand _ _ b

end MinCostFlow.Expander
