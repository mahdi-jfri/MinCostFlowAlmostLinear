module

public import MinCostFlow.Chain.SparseCoreRestartCost
import MinCostFlow.Chain.SparseCoreRestartAux
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bookkeeping for the total cost of `sparseCoreRestartTool`

Item 6 of `SparseCoreRestartTool.IsSpecRestart` bounds the total cost of a run with restarts.
The cost of branch `j` grows in three ways: by the step work of each update, by the work of each
restart, and once at the start. Most of the step work depends only on the fields that a restart
does not change, so it is the same as in the run without restarts (`treeRunSeq`). Only two parts
differ: the size of the spanner batch `U_S` and the work of the Theorem 8.2 structures, since
these structures are rebuilt at each restart.

This file proves three facts used for item 6.
* `foldl_restart_tree_cost`: a list of restarts adds `singleRestartCost` once per restart of `j`.
* `branch_cost_eq`: the cost of branch `j` after step `t`, written as the cost of `treeRunSeq`
  with the two differing parts exchanged, plus the restart work.
* `epoch_partition_sum_le`: a bound that holds on every epoch (the steps between two restarts of
  `j`) sums to a bound on all steps, with one constant term per epoch.
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.LSF
open MinCostFlow.SparseCore
open MinCostFlow.DynSpanner

/-- `singleRestartCost` reads only the fields that a restart does not change. -/
lemma singleRestartCost_congr {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) {a b : TreeCoreState L}
    (h : TreeBaseFieldsEq a b) :
    singleRestartCost L sparsify a = singleRestartCost L sparsify b := by
  unfold singleRestartCost restartBucketGraph
  rw [h.cs, h.activeComps, h.activeBuckets, h.ts, h.origBucket, h.splitBound, h.m₀]

/-- Restarting a nonempty state along the list `xs` adds `singleRestartCost` to the cost of branch
`j` once for each occurrence of `j` in `xs`. -/
lemma foldl_restart_tree_cost
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) (xs : List ℕ) :
    ∀ (st : SparseCoreState L), st.isNonempty = true → ∀ j,
      ((xs.foldl (sparseCoreRestartTool oracle C_lsst L sparsify).restart st).trees j).cost =
        (st.trees j).cost + xs.count j * singleRestartCost L sparsify (st.trees j) := by
  induction xs with
  | nil => intro st _ j; simp only [List.foldl_nil, List.count_nil, zero_mul, add_zero]; rfl
  | cons x xs ih =>
    intro st hne j
    have hR : (sparseCoreRestartTool oracle C_lsst L sparsify).restart st x =
        { st with trees := Function.update st.trees x (restartTreeCore L sparsify (st.trees x)) } := by
      change (if st.isNonempty then _ else st) = _
      simp only [hne, ↓reduceIte]
    have hne' : ((sparseCoreRestartTool oracle C_lsst L sparsify).restart st x).isNonempty =
        true := by rw [hR]; exact hne
    change ((xs.foldl (sparseCoreRestartTool oracle C_lsst L sparsify).restart
      ((sparseCoreRestartTool oracle C_lsst L sparsify).restart st x)).trees j).cost = _
    rw [ih _ hne' j, hR]
    by_cases hjx : j = x
    · subst hjx
      have hsrc : singleRestartCost L sparsify (restartTreeCore L sparsify (st.trees j)) =
          singleRestartCost L sparsify (st.trees j) := rfl
      simp only [Function.update_self, restartTreeCore_cost, hsrc, List.count_cons_self]
      ring
    · simp only [Function.update_of_ne hjx]
      rw [List.count_cons_of_ne (Ne.symm hjx)]

/-- The cost added by one step of a branch, as a sum of its five parts. -/
lemma stepTreeCoreAux_cost {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) (tr : TreeCoreState L)
    (U : List Update) :
    (stepTreeCoreAux sparsify tr U).state.cost =
      tr.cost + (U.length +
        ((stepTreeCoreAux sparsify tr U).state.activeComps.sum fun C =>
          ((stepTreeCoreAux sparsify tr U).U_C C).length) +
        (stepTreeCoreAux sparsify tr U).U_S.length +
        ((stepTreeCoreAux sparsify tr U).state.activeComps.sum fun C =>
          (tr.activeBuckets C).sum fun b => ((stepTreeCoreAux sparsify tr U).stepOut (C, b)).cost) +
        (stepTreeCoreAux sparsify tr U).newlyActive.sum tr.lazyInitCost) :=
  rfl

/-- The first state of branch `j` is the first state of `treeRunSeq`. -/
lemma sRT_pre_zero_trees
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (restarts : ℕ → List ℕ) (j : ℕ) :
    ((sparseCoreRestartTool oracle C_lsst L sparsify).runAfterUpdate k M N D restarts 0).1.trees j =
      (treeRunSeq oracle C_lsst L sparsify k M N D j 0).1 := by
  simp only [SparseCoreRestartTool.runAfterUpdate, sparseCoreRestartTool, sparseCoreTool,
    sparseCoreToolWith]
  split_ifs <;> rfl

/-- The cost of branch `j` after step `t`. On the left it carries the batch sizes and the
Theorem 8.2 work of `treeRunSeq`; on the right it carries those of the run with restarts, and the
restart work. All other parts of the step work agree, because they depend only on the fields that
a restart does not change. -/
lemma branch_cost_eq
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (restarts : ℕ → List ℕ) (hV₀ : (D.G 0).V.Nonempty) (j : ℕ) :
    let T := sparseCoreRestartTool oracle C_lsst L sparsify
    let post := fun t => T.runAfterRestarts k M N D restarts t
    let base := fun t => (treeRunSeq oracle C_lsst L sparsify k M N D j t).1
    let infoB := fun s => stepTreeCoreAux sparsify (base s) (D.U (s + 1))
    let infoR := fun s => stepTreeCoreAux sparsify ((post s).trees j) (D.U (s + 1))
    ∀ t,
      ((post t).trees j).cost +
          ∑ s ∈ Finset.range t, ((infoB s).U_S.length +
            ((infoB s).state.activeComps.sum fun C =>
              ((base s).activeBuckets C).sum fun b => ((infoB s).stepOut (C, b)).cost)) =
        (base t).cost +
          ∑ s ∈ Finset.range t, ((infoR s).U_S.length +
            ((infoR s).state.activeComps.sum fun C =>
              (((post s).trees j).activeBuckets C).sum fun b => ((infoR s).stepOut (C, b)).cost)) +
          ∑ r ∈ Finset.range (t + 1),
            (restarts r).count j * singleRestartCost L sparsify (base r) := by
  intro T post base infoB infoR t
  have hne : ∀ s, (post s).isNonempty = true := fun s =>
    (runAfterRestarts_isNonempty oracle C_lsst L sparsify k M N D restarts s).2.1.trans
      (decide_eq_true hV₀)
  have hne_pre : ∀ s, (T.runAfterUpdate k M N D restarts s).1.isNonempty = true := fun s =>
    (runAfterRestarts_isNonempty oracle C_lsst L sparsify k M N D restarts s).1.trans
      (decide_eq_true hV₀)
  have hproj := runAfterRestarts_base_proj oracle C_lsst L sparsify k M N D restarts hV₀ j
  -- The restarts at step `t` add their work to branch `j`.
  have hpost_cost : ∀ t, ((post t).trees j).cost =
      ((T.runAfterUpdate k M N D restarts t).1.trees j).cost +
        (restarts t).count j * singleRestartCost L sparsify (base t) := fun t => by
    have h := foldl_restart_tree_cost oracle C_lsst L sparsify (restarts t)
      (T.runAfterUpdate k M N D restarts t).1 (hne_pre t) j
    rw [singleRestartCost_congr sparsify (hproj t).1] at h
    exact h
  induction t with
  | zero =>
    rw [hpost_cost 0, sRT_pre_zero_trees]
    simp only [Finset.range_zero, Finset.sum_empty, Finset.sum_range_one, add_zero]
    rfl
  | succ s ih =>
    have hpre_eq : (T.runAfterUpdate k M N D restarts (s + 1)).1.trees j = (infoR s).state := by
      rw [T.runAfterUpdate_succ]
      dsimp only [T]
      rw [sRT_update_of_nonempty (hne s)]
    have hb := (hproj s).2
    have hb' := (hproj (s + 1)).1
    rw [hpre_eq] at hb'
    have hUC : ((infoR s).state.activeComps.sum fun C => ((infoR s).U_C C).length) =
        ((infoB s).state.activeComps.sum fun C => ((infoB s).U_C C).length) := by
      have hact : (infoR s).state.activeComps = (infoB s).state.activeComps := hb'.activeComps
      rw [hact]
      exact Finset.sum_congr rfl fun C _ => by
        rw [stepTreeCoreAux_U_C_eq_of_cs_ts sparsify hb.cs hb.ts]
    have hlazy : (infoR s).newlyActive.sum ((post s).trees j).lazyInitCost =
        (infoB s).newlyActive.sum (base s).lazyInitCost := by
      rw [stepTreeCoreAux_newlyActive_eq_of_cs_act sparsify hb.cs hb.activeComps, hb.lazyInitCost]
    have hcR : (infoR s).state.cost = ((post s).trees j).cost + ((D.U (s + 1)).length +
        ((infoR s).state.activeComps.sum fun C => ((infoR s).U_C C).length) +
        (infoR s).U_S.length +
        ((infoR s).state.activeComps.sum fun C =>
          (((post s).trees j).activeBuckets C).sum fun b => ((infoR s).stepOut (C, b)).cost) +
        (infoR s).newlyActive.sum ((post s).trees j).lazyInitCost) :=
      stepTreeCoreAux_cost sparsify ((post s).trees j) (D.U (s + 1))
    have hcB : (infoB s).state.cost = (base s).cost + ((D.U (s + 1)).length +
        ((infoB s).state.activeComps.sum fun C => ((infoB s).U_C C).length) +
        (infoB s).U_S.length +
        ((infoB s).state.activeComps.sum fun C =>
          ((base s).activeBuckets C).sum fun b => ((infoB s).stepOut (C, b)).cost) +
        (infoB s).newlyActive.sum (base s).lazyInitCost) :=
      stepTreeCoreAux_cost sparsify (base s) (D.U (s + 1))
    have hbase_succ : base (s + 1) = (infoB s).state := rfl
    rw [hpost_cost (s + 1), hpre_eq, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ (n := s + 1), hbase_succ]
    rw [hcR, hcB, hUC, hlazy]
    rw [← hbase_succ]
    omega

/-- A bound that holds on every epoch of branch `j` sums to a bound on the steps `1, …, t`. An
epoch is a block of steps `s₀ + 1, …, t'` where `s₀` is `0` or a restart of `j` and no restart of
`j` happens strictly between `s₀` and `t'`. The constant `A` is paid once per epoch, and there are
at most one more epochs than restarts of `j` at the steps `1, …, t - 1`. -/
lemma epoch_partition_sum_le (restarts : ℕ → List ℕ) (j τ : ℕ) (f g : ℕ → ℝ) (A B : ℝ)
    (hA : 0 ≤ A)
    (hEp : ∀ s₀ t, s₀ ≤ t → t ≤ τ → (s₀ = 0 ∨ j ∈ restarts s₀) →
      (∀ r, s₀ < r → r < t → j ∉ restarts r) →
      ∑ s ∈ Finset.Icc (s₀ + 1) t, f s ≤ A + B * ∑ s ∈ Finset.Icc (s₀ + 1) t, g s) :
    ∀ t ≤ τ, ∑ s ∈ Finset.Icc 1 t, f s ≤
      (1 + ∑ r ∈ Finset.Icc 1 (t - 1), (if j ∈ restarts r then (1 : ℝ) else 0)) * A +
        B * ∑ s ∈ Finset.Icc 1 t, g s := by
  have hN_nn : ∀ x, 0 ≤ ∑ r ∈ Finset.Icc 1 x, (if j ∈ restarts r then (1 : ℝ) else 0) :=
    fun x => Finset.sum_nonneg fun r _ => by split_ifs <;> norm_num
  have hN_mono : ∀ x y, x ≤ y →
      ∑ r ∈ Finset.Icc 1 x, (if j ∈ restarts r then (1 : ℝ) else 0) ≤
        ∑ r ∈ Finset.Icc 1 y, (if j ∈ restarts r then (1 : ℝ) else 0) := fun x y hxy =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hxy)
      (fun r _ _ => by split_ifs <;> norm_num)
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    rcases Nat.eq_zero_or_pos t with h0 | hpos
    · subst h0
      have hz : Finset.Icc 1 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty_of_lt (by norm_num)
      rw [hz]
      simp only [Finset.sum_empty, mul_zero, add_zero]
      nlinarith [hN_nn (0 - 1)]
    · obtain ⟨hs₀_le, hs₀_cases, hs₀_none⟩ := lastRestart_spec restarts j (t - 1)
      set s₀ := lastRestart restarts j (t - 1)
      have hNoR : ∀ r, s₀ < r → r < t → j ∉ restarts r := fun r h1 h2 =>
        hs₀_none r h1 (by omega)
      have hEp_t := hEp s₀ t (by omega) ht hs₀_cases hNoR
      have hsplit : ∀ h : ℕ → ℝ, ∑ s ∈ Finset.Icc 1 t, h s =
          ∑ s ∈ Finset.Icc 1 s₀, h s + ∑ s ∈ Finset.Icc (s₀ + 1) t, h s := fun h => by
        have h1 : Finset.Icc 1 t = Finset.Ioc 0 t := Finset.Icc_add_one_left_eq_Ioc 0 t
        have h2 : Finset.Icc 1 s₀ = Finset.Ioc 0 s₀ := Finset.Icc_add_one_left_eq_Ioc 0 s₀
        have h3 : Finset.Icc (s₀ + 1) t = Finset.Ioc s₀ t := Finset.Icc_add_one_left_eq_Ioc s₀ t
        rw [h1, h2, h3, Finset.sum_Ioc_consecutive h (Nat.zero_le s₀) (by omega)]
      rw [hsplit f, hsplit g]
      by_cases hs0 : s₀ = 0
      · have hz : Finset.Icc 1 s₀ = ∅ := by rw [hs0]; rfl
        rw [hz, Finset.sum_empty, Finset.sum_empty]
        have := hN_nn (t - 1)
        nlinarith
      · have hjs : j ∈ restarts s₀ := hs₀_cases.resolve_left hs0
        have hIH := ih s₀ (by omega) (by omega)
        have hstep : ∑ r ∈ Finset.Icc 1 (s₀ - 1), (if j ∈ restarts r then (1 : ℝ) else 0) + 1 =
            ∑ r ∈ Finset.Icc 1 s₀, (if j ∈ restarts r then (1 : ℝ) else 0) := by
          obtain ⟨u, hu⟩ := Nat.exists_eq_succ_of_ne_zero hs0
          have hju : j ∈ restarts (u + 1) := by rw [← Nat.succ_eq_add_one, ← hu]; exact hjs
          rw [hu, Nat.succ_sub_one, Finset.sum_Icc_succ_top (by omega)]
          simp [hju]
        have hmono := hN_mono s₀ (t - 1) (by omega)
        have hmA := mul_le_mul_of_nonneg_right hmono hA
        nlinarith

end MinCostFlow.Chain

end
