module

public import MinCostFlow.Chain.BundleRestartCost
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Cumulative Cost Bookkeeping for `sparseCoreBundleRestartTool`

Proves the structural bookkeeping lemmas for item 7 (total cumulative cost) of `IsSpecOrdRestart`:
- `foldl_bundleRestart_tree_cost`: restarting along a list `xs` adds `xs.count j * singleBundleRestartCost`
  to branch `j`'s cost.
- `bundle_branch_cost_decomp`: direct induction decomposing `((post t).trees j).cost` into initial
  setup, cumulative lazy initializations, input batch lengths, bundle-batch lengths, output batch
  lengths, dynamic-spanner update costs, and restart costs.
- `bundle_epoch_partition_sum_le`: partitioning `[1, t]` into non-restarted epochs via
  `bundleLastRestart` sums per-epoch affine bounds `A + B * ∑ g` with one `A` per epoch.
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.LSF
open MinCostFlow.SparseCore
open MinCostFlow.DynSpanner
open MinCostFlow.Bundle

lemma bundle_sum_Icc_succ_eq_sum_range (f : ℕ → ℝ) (a b : ℕ) :
    ∑ s ∈ Finset.Icc (a + 1) b, f s = ∑ r ∈ Finset.range (b - a), f (a + r + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr (by congr 1; omega) fun r _ => by congr 1; omega

lemma bundle_sum_range_eq_sum_Icc_succ (f : ℕ → ℝ) (t : ℕ) :
    ∑ s ∈ Finset.range t, f (s + 1) = ∑ s ∈ Finset.Icc 1 t, f s := by
  have h := bundle_sum_Icc_succ_eq_sum_range f 0 t
  simpa using h.symm

/-- Restarting a nonempty state along the list `xs` adds `singleBundleRestartCost` to branch `j`
once per occurrence of `j` in `xs`. -/
lemma foldl_bundleRestart_tree_cost
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) (xs : List ℕ) :
    ∀ (st : SparseCoreBundleState L), st.isNonempty = true → ∀ j,
      ((xs.foldl (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).restart st).trees j).cost =
        (st.trees j).cost + xs.count j * singleBundleRestartCost L sparsify (st.trees j) st.ord := by
  induction xs with
  | nil => intro st _ j; simp only [List.count_nil, zero_mul, add_zero]; rfl
  | cons x xs ih =>
    intro st hne j
    let T := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
    have hR : T.restart st x =
        { isNonempty := st.isNonempty, k := st.k, ord := st.ord,
          trees := Function.update st.trees x (restartBundleTree L sparsify (st.trees x) st.ord) } := by
      dsimp only [T]
      rw [sparseCoreBundleRestartTool_restart_eq, ite_eq_left hne]
    have hne' : (T.restart st x).isNonempty = true := by rw [hR]; exact hne
    change ((xs.foldl T.restart (T.restart st x)).trees j).cost = _
    rw [ih _ hne' j, hR]
    dsimp only
    by_cases hjx : j = x
    · subst hjx
      have hsrc := singleBundleRestartCost_restartBundleTree sparsify (st.trees j) st.ord
      simp only [Function.update_self, restartBundleTree_cost, hsrc, List.count_cons_self]
      ring
    · simp only [Function.update_of_ne hjx]
      rw [List.count_cons_of_ne (Ne.symm hjx)]

/-- The cost added by one `stepBundleTree` call, written as a sum of its five terms. -/
lemma stepBundleTree_cost {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) :
    let info := stepBundleTree sparsify tr U ord ord'
    info.state.cost =
      tr.cost + (U.length +
        (info.state.activeComps.sum fun C =>
          (tr.activeBuckets C).sum fun b => (info.U_B (C, b)).length) +
        info.U_S.length +
        (info.state.activeComps.sum fun C =>
          (tr.activeBuckets C).sum fun b => (info.stepOut (C, b)).cost) +
        info.newlyActive.sum tr.lazyInitCost) :=
  rfl

/-- Exact cost decomposition of branch `j` after step `t` of a run with restarts: initial setup,
cumulative lazy initializations, input batches, bundle-step batches, spanner output batches,
dynamic-spanner update costs, and restart costs. -/
lemma bundle_branch_cost_decomp
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hV₀ : (D.G 0).V.Nonempty) (j : ℕ) :
    let T := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
    let st₀ := initBundleTreeWith lsfInit L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j
    let pre := fun t => (T.runOrdAfterUpdate k M N D ord restarts t).1
    let post := fun t => T.runOrdAfterRestarts k M N D ord restarts t
    let base := fun t => (bundleRunSeqWith lsfInit L sparsify k M N D ord j t).1
    let infoR := fun s => stepBundleTree sparsify ((post s).trees j) (D.U (s + 1)) (ord s) (ord (s + 1))
    ∀ t,
      ((post t).trees j).cost =
        (D.G 0).m + (activeSubgraph (D.G 0)).n + 1 +
          ((base t).activeComps.sum st₀.lazyInitCost) +
          ∑ s ∈ Finset.range t, (D.U (s + 1)).length +
          ∑ s ∈ Finset.range t, ((infoR s).state.activeComps.sum fun C =>
            (st₀.activeBuckets C).sum fun b => ((infoR s).U_B (C, b)).length) +
          ∑ s ∈ Finset.range t, (infoR s).U_S.length +
          ∑ s ∈ Finset.range t, ((infoR s).state.activeComps.sum fun C =>
            (st₀.activeBuckets C).sum fun b => ((infoR s).stepOut (C, b)).cost) +
          ∑ r ∈ Finset.range (t + 1),
            (restarts r).count j * singleBundleRestartCost L sparsify ((pre r).trees j) (ord r) := by
  intro T st₀ pre post base infoR t
  have hne_pre : ∀ s, (pre s).isNonempty = true := fun s =>
    (runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts s).1.trans
      (decide_eq_true hV₀)
  have hne_post : ∀ s, (post s).isNonempty = true := fun s =>
    (runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts s).2.1.trans
      (decide_eq_true hV₀)
  have hord_pre : ∀ s, (pre s).ord = ord s := fun s =>
    ((runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts s).2.2.2.2 hV₀).1
  have hord_post : ∀ s, (post s).ord = ord s := fun s =>
    ((runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts s).2.2.2.2 hV₀).2
  have hproj := runOrdAfterRestarts_base_proj lsfInit C_lsst L sparsify k M N D ord restarts hV₀ j
  have hbase_const : ∀ s, (base s).activeBuckets = st₀.activeBuckets ∧
      (base s).lazyInitCost = st₀.lazyInitCost := by
    intro s
    induction s with
    | zero => exact ⟨rfl, rfl⟩
    | succ m ih => exact ih
  have hpost_cost : ∀ s, ((post s).trees j).cost =
      ((pre s).trees j).cost +
        (restarts s).count j * singleBundleRestartCost L sparsify ((pre s).trees j) (ord s) := fun s => by
    have h := foldl_bundleRestart_tree_cost lsfInit C_lsst L sparsify (restarts s)
      (pre s) (hne_pre s) j
    rw [hord_pre s] at h
    exact h
  induction t with
  | zero =>
    rw [hpost_cost 0, Nat.zero_add, Finset.sum_range_one]
    have hpre0 : (pre 0).trees j = st₀ := rfl
    have hst0_cost : st₀.cost = (D.G 0).m + (activeSubgraph (D.G 0)).n + 1 +
        (base 0).activeComps.sum st₀.lazyInitCost := rfl
    rw [hpre0, hst0_cost]
    simp only [Finset.range_zero, Finset.sum_empty, add_zero]
  | succ s ih =>
    have hpre_eq : (pre (s + 1)).trees j = (infoR s).state := by
      dsimp only [pre, T]
      rw [SparseCoreRestartTool.runOrdAfterUpdate_succ,
        sparseCoreBundleRestartTool_updateOrd_of_nonempty (hne_post s), hord_post s]
    have hAB_s : ((post s).trees j).activeBuckets = st₀.activeBuckets :=
      (hproj s).2.activeBuckets.trans (hbase_const s).1
    have hLC_s : ((post s).trees j).lazyInitCost = st₀.lazyInitCost :=
      (hproj s).2.lazyInitCost.trans (hbase_const s).2
    have hact_s : ((post s).trees j).activeComps = (base s).activeComps := (hproj s).2.activeComps
    have hact_s1 : (infoR s).state.activeComps = (base (s + 1)).activeComps := by
      rw [← hpre_eq]; exact (hproj (s + 1)).1.activeComps
    have hdisj_na : Disjoint (base s).activeComps (infoR s).newlyActive := by
      rw [← hact_s]
      exact Finset.disjoint_sdiff
    have hunion_na : (base (s + 1)).activeComps = (base s).activeComps ∪ (infoR s).newlyActive := by
      rw [← hact_s1, ← hact_s]
      rfl
    have hlazy_sum : (base (s + 1)).activeComps.sum st₀.lazyInitCost =
        (base s).activeComps.sum st₀.lazyInitCost + (infoR s).newlyActive.sum st₀.lazyInitCost := by
      rw [hunion_na, Finset.sum_union hdisj_na]
    have hstep : (infoR s).state.cost =
        ((post s).trees j).cost + ((D.U (s + 1)).length +
          ((infoR s).state.activeComps.sum fun C =>
            (((post s).trees j).activeBuckets C).sum fun b => ((infoR s).U_B (C, b)).length) +
          (infoR s).U_S.length +
          ((infoR s).state.activeComps.sum fun C =>
            (((post s).trees j).activeBuckets C).sum fun b => ((infoR s).stepOut (C, b)).cost) +
          (infoR s).newlyActive.sum ((post s).trees j).lazyInitCost) :=
      stepBundleTree_cost sparsify ((post s).trees j) (D.U (s + 1)) (ord s) (ord (s + 1))
    rw [hAB_s, hLC_s] at hstep
    have hpre_cost : ((pre (s + 1)).trees j).cost = (infoR s).state.cost :=
      congrArg BundleTreeState.cost hpre_eq
    rw [Finset.sum_range_succ (n := s + 1),
      Finset.sum_range_succ (n := s), Finset.sum_range_succ (n := s),
      Finset.sum_range_succ (n := s), Finset.sum_range_succ (n := s)]
    rw [hpost_cost (s + 1), hpre_cost, hstep, ih, hlazy_sum]
    omega

/-- Summing a per-epoch affine bound `∑_{s ∈ (s₀, t]} f s ≤ A + B * ∑_{s ∈ (s₀, t]} g s` across
the epochs partitioned by `bundleLastRestart` pays `A` at most once initially plus once per step
`r ∈ [1, t - 1]` with `j ∈ restarts r`. -/
lemma bundle_epoch_partition_sum_le (restarts : ℕ → List ℕ) (j τ : ℕ) (f g : ℕ → ℝ) (A B : ℝ)
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
    · obtain ⟨hs₀_le, hs₀_cases, hs₀_none⟩ := bundleLastRestart_spec restarts j (t - 1)
      set s₀ := bundleLastRestart restarts j (t - 1)
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
