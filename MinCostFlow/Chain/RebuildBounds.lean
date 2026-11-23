module

public import MinCostFlow.Chain.RebuildCollapse
public import MinCostFlow.Chain.RebuildCounterexample
public import MinCostFlow.Chain.Theorem5_1Helpers
public import MinCostFlow.Chain.Examples
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rebuild Count Bounds, Unconditional Collapses, and Counterexamples

This file derives the rebuild-count collapse bounds (`RebuildFloorHyp` and
`Alg2RebuildCollapseHyp`) relative to **Algorithm 1** and **Algorithm 2** under the paper's
level-`i` size bound `levelM TP P i = ⌈M₀ * (γ_ℓ / k)^i⌉` and global vertex cap `N₀`:

1. **Unconditional bounds (all `d ≥ 1`)**:
   * `alg2_rebuildCount_last_eq_zero`: `st.chain.rebuildCount cfg.P.d = 0` holds unconditionally.
   * `alg2_rebuildCount_zero_collapse_uncond`: at level `0` (`levelM TP P 0 ≥ P.M₀` under `TP.Valid`),
     every self-rebuild requires `> max 1 (updateThreshold P.k (levelM TP P 0) N₀)` updates, yielding
     `rebuildCount 0 * max 1 (updateThreshold P.k (levelM TP P 0) N₀) + updCount 0 ≤ Q_upd`
     **unconditionally** (no `hSmall`, no `hSwRec`, no `hV`).
   * `alg2_rebuildCount_zero_le_upd`: `rebuildCount 0 + updCount 0 ≤ Q_upd` unconditionally.
2. **Derived collapse theorems**:
   * **Unconditional for `d = 1` (`hTP` only)**: `alg2RebuildCollapseHyp_of_d_one`,
     `rebuildFloorHyp_of_d_one`, and `theorem_5_1_collapsed_d_one` hold from `cfg.TP.Valid`
     without `hV` or `hSmall`.
   * **General `d ≥ 1` under `cfg.ValidNoHidden` (no `ToolSwitchedRecourse`)**:
     `alg2RebuildCollapseHyp_uncond`, `rebuildFloorHyp_uncond`, and `theorem_5_1_collapsed`
     derive `RebuildFloorHyp` and collapsed total runtime unconditionally for every `d ≥ 1`
     via `ChainInv.hRecFwd` (enabled by calling `T.restart` in `Shift`),
     `algorithm2_uncond_recUpdates_zero_eq`, and `hInv.hRecRebuild`.
3. **Concrete counterexample (`exSwitchedRecourse_counterexample`)**: documents why
   `ToolSwitchedRecourse` (`jtree.tex` page 30, line 852, when `Shift(i)` switches active
   branches WITHOUT calling `restart`) is genuinely stronger than `IsSpecUpTo` (`Lemma 5.17`'s
   fixed-branch recourse bound), exhibiting a `2`-branch `SparseCoreTool` instance where all
   fixed-branch `IsSpecUpTo` / `ToolMWUUpTo` / `ToolEmbedsSurvivingUpTo` / `ToolNoReinsertUpTo`
   guarantees hold at `(k = 2, τ = 2, M = 20, N = 4)`, yet switching from branch `0` at `t = 1`
   to branch `1` at `t = 2` incurs cumulative recourse `3 + 5 = 8 > 6 = γ_r(20) * Q_upd`.
-/

@[expose] public section

namespace MinCostFlow.Chain


section Counterexample

/-- **Concrete cure of `exSwitchedRecourse_counterexample` via `SparseCoreRestartTool`**:
for **every** restart schedule `restarts : ℕ → List ℕ`, `exSwRestartTool` satisfies **all** Clauses 1–6
of `IsSpecRestart exSwParams`, `ToolMWURestart`, `ToolEmbedsSurvivingRestart`, and
`ToolNoReinsertRestart` at `(k = 2, τ = 2, M = 20, N = 4)` on `exSwDyn`; moreover, calling
`restart` on branch `1` at round `1` (`restarts 1 = [1]`) keeps the switched recourse across
`b(1) = 0, b(2) = 1` at `3 + 1 = 4 ≤ 6 = exSwParams.γ_r 20 * 2` (curing `exSwTool`'s `8 > 6` burst). -/
theorem exSwRestartTool_cures_switchedRecourse :
    let P := exSwParams; let T := exSwRestartTool; let D := exSwDyn
    let k := 2; let τ := 2; let M := 20; let N := 4
    let c : ℕ → ℕ → ℝ := fun _ _ => 0; let w : ℕ → ℕ → ℝ := fun _ _ => 1
    let σ_mwu : ℕ → ℝ := fun _ => 3
    (∀ (restarts : ℕ → List ℕ), (∀ r ≤ τ, ∀ j ∈ restarts r, j < k) →
      let pre := fun t => (T.runAfterUpdate k M N D restarts t).1
      let U_S := fun t => (T.runAfterUpdate k M N D restarts t).2
      let st := fun t => T.runAfterRestarts k M N D restarts t
      (∀ t ≤ τ, ∀ j < k,
        (T.lsfs (st t) j).Holds (D.G t) (D.ℓ t) (P.σ k (D.G t).n) ∧
        IsSparsifiedCoreGraph (D.G t) (T.lsfs (st t) j) (D.ℓ t) (k : ℝ) (P.γ_ℓ M) (P.γ_c M)
          (T.S (st t) j) (T.emb (st t) j) ∧
        ((∀ u ∈ (D.G 0).V, ∀ v ∈ (D.G 0).V, (D.G 0).Connected u v) →
          ((T.lsfs (st t) j).F.R.card : ℝ) ≤
            P.c_R * ((M : ℝ) / (k : ℝ) +
              (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
                (Real.log ((N : ℝ) + 2)) ^ 2 + 1))) ∧
      (∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
        (T.lsfs (st t) j).F.F.E ⊆ (T.lsfs (st (t - 1)) j).F.F.E ∧
        (∀ e ∈ (D.G t).E, e ∈ (D.G (t - 1)).E → (∀ u ∈ D.U t, ¬ u.Inserts e) →
          (T.lsfs (st t) j).wstr e = (T.lsfs (st (t - 1)) j).wstr e) ∧
        (∀ e ∈ (D.G t).E, (∃ u ∈ D.U t, u.Inserts e) → (T.lsfs (st t) j).wstr e = 1) ∧
        (T.S (st (t - 1)) j).BatchIsValid (U_S t j) ∧
        T.S (pre t) j = (T.S (st (t - 1)) j).applyBatch (U_S t j)) ∧
      (∀ r ≤ τ, ∀ p j', p ++ [j'] <+: restarts r →
        let st' := List.foldl T.restart (pre r) p
        (∀ b < k, T.lsfs (T.restart st' j') b = T.lsfs st' b) ∧
        (∀ b < k, b ≠ j' →
          T.S (T.restart st' j') b = T.S st' b ∧ T.emb (T.restart st' j') b = T.emb st' b) ∧
        T.cost st' ≤ T.cost (T.restart st' j') ∧
        (T.cost (T.restart st' j') : ℝ) ≤
          (T.cost st' : ℝ) + P.c_T * ((M : ℝ) + 1) * P.γ_r M *
            (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T) ∧
      (∀ s₀ t, s₀ ≤ t → t ≤ τ → ∀ j < k,
        s₀ = 0 ∨ j ∈ restarts s₀ → (∀ r, s₀ < r → r < t → j ∉ restarts r) →
        (((Finset.Icc (s₀ + 1) t).sum fun s => (U_S s j).length : ℕ) : ℝ) ≤
          P.γ_r M * (((Finset.Icc (s₀ + 1) t).sum fun s => (D.U s).length : ℕ) : ℝ) ∧
        (((Finset.Icc (s₀ + 1) t).sum fun s => (T.S (st (s - 1)) j).batchEnc (U_S s j) : ℕ) : ℝ) ≤
          P.γ_r M * ((M : ℝ) / (k : ℝ) +
            (((Finset.Icc (s₀ + 1) t).sum fun s => (D.U s).length : ℕ) : ℝ))) ∧
      (∀ s₀ ≤ τ, ∀ j < k, ∃ Ψ' : ℝ,
        WeakHiddenStable (T.coreInstanceFrom k M N D restarts s₀ j) (τ - s₀) Ψ'
          (T.coreCFrom k M N D restarts c s₀ j) (T.coreWFrom k M N D restarts w s₀ j)) ∧
      ((T.cost (st τ) : ℝ) ≤
        P.c_T * ((M : ℝ) + 1) * ((k : ℝ) + ((Finset.range (τ + 1)).sum fun r => (restarts r).length : ℕ)) *
          P.γ_r M * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T) ∧
      (∀ t ≤ τ, ∀ e ∈ (D.G t).E,
        (∑ j ∈ Finset.range k, (T.lsfs (st t) j).wstr e) / (k : ℝ) ≤ σ_mwu (D.G t).n) ∧
      (∀ t ≤ τ, ∀ j < k, ∀ e ∈ (T.S (st t) j).E, T.emb (st t) j e = [(e, true)]) ∧
      (∀ t, 1 ≤ t → t ≤ τ → ∀ j < k, NoBatchReinsert (T.S (st (t - 1)) j) (U_S t j))) ∧
    (let restarts : ℕ → List ℕ := fun r => if r = 1 then [1] else []
     let b : ℕ → ℕ := fun s => if s ≤ 1 then 0 else 1
     (Finset.Icc 1 2).sum (fun s => ((T.runAfterUpdate k M N D restarts s).2 (b s)).length) = 4 ∧
     (((Finset.Icc 1 2).sum (fun s => ((T.runAfterUpdate k M N D restarts s).2 (b s)).length) : ℕ) : ℝ) ≤
       P.γ_r M * (((Finset.Icc 1 2).sum (fun s => (D.U s).length) : ℕ) : ℝ)) := by
  dsimp only
  have hG0_V : (exSwDyn.G 0).V = {0, 1, 2, 3} := rfl
  have hG1_V : (exSwDyn.G 1).V = {0, 1, 2, 3} := rfl
  have hG2_V : (exSwDyn.G 2).V = {0, 1, 2, 3} := rfl
  have hG0_E : (exSwDyn.G 0).E = {0, 1, 2, 3, 4} := rfl
  have hG1_E : (exSwDyn.G 1).E = {1, 2, 3, 4} := by
    simp [exSwDyn, MGraph.applyBatch, MGraph.applyUpdate, exSwG0]
  have hG2_E : (exSwDyn.G 2).E = {2, 3, 4} := by
    simp [exSwDyn, MGraph.applyBatch, MGraph.applyUpdate, exSwG0]
  have hG_tail : ∀ t, (exSwDyn.G t).tail = exSwG0.tail := fun t => by
    rcases t with _ | _ | _ <;> simp [exSwDyn, MGraph.applyBatch, MGraph.applyUpdate]
  have hG_head : ∀ t, (exSwDyn.G t).head = exSwG0.head := fun t => by
    rcases t with _ | _ | _ <;> simp [exSwDyn, MGraph.applyBatch, MGraph.applyUpdate]
  have hG0_val : (exSwDyn.G 0).IsValid := fun e he => by
    have : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 := by simpa [hG0_E] using he
    rcases this with rfl | rfl | rfl | rfl | rfl <;> simp [exSwDyn, exSwG0]
  have hG1_val : (exSwDyn.G 1).IsValid := by
    rw [MGraph.IsValid, hG1_V, hG1_E, hG_tail 1, hG_head 1]
    exact by decide
  have hG2_val : (exSwDyn.G 2).IsValid := by
    rw [MGraph.IsValid, hG2_V, hG2_E, hG_tail 2, hG_head 2]
    exact by decide
  let S01 := exSwSInit.applyBatch exSwU01
  let S02 := S01.applyBatch exSwU02
  let S11 := exSwSInit.applyBatch exSwU11
  let S12 := S11.applyBatch exSwU12
  let S12R := S11.applyBatch [.delete 1]
  have hS01 : S01.V = {0, 2, 3} ∧ S01.E = {1, 3, 4} ∧
      S01.tail 1 = 0 ∧ S01.head 1 = 2 ∧ S01.tail 3 = 2 ∧ S01.head 3 = 3 ∧
      S01.tail 4 = 0 ∧ S01.head 4 = 3 := by
    dsimp only [S01]
    simp only [MGraph.applyBatch, MGraph.applyUpdate, exSwSInit, exSwU01, Function.update, List.foldl]
    exact ⟨by decide, by decide, by decide⟩
  have hS02 : S02.V = {0, 2, 3} ∧ S02.E = {3, 4} ∧
      S02.tail 3 = 2 ∧ S02.head 3 = 3 ∧ S02.tail 4 = 0 ∧ S02.head 4 = 3 := by
    dsimp only [S02, exSwU02, MGraph.applyBatch]
    exact ⟨hS01.1, by change S01.E.erase 1 = {3, 4}; rw [hS01.2.1]; decide,
      hS01.2.2.2.2.1, hS01.2.2.2.2.2.1, hS01.2.2.2.2.2.2.1, hS01.2.2.2.2.2.2.2⟩
  have hS11 : S11.V = {0, 2} ∧ S11.E = {1, 4} ∧
      S11.tail 1 = 0 ∧ S11.head 1 = 2 ∧ S11.tail 4 = 0 ∧ S11.head 4 = 2 := by
    dsimp only [S11]; simp [MGraph.applyBatch, MGraph.applyUpdate, exSwSInit, exSwU11]
  have hS12 : S12.V = {0, 1, 2, 3} ∧ S12.E = {2, 3, 4} ∧
      S12.tail 2 = 0 ∧ S12.head 2 = 1 ∧ S12.tail 3 = 2 ∧ S12.head 3 = 3 ∧
      S12.tail 4 = 1 ∧ S12.head 4 = 3 := by
    dsimp only [S12, S11]
    simp only [MGraph.applyBatch, MGraph.applyUpdate, exSwSInit, exSwU11, exSwU12, Function.update, List.foldl]
    exact ⟨by decide, by decide, by decide⟩
  have hS12R : S12R.V = {0, 2} ∧ S12R.E = {4} ∧ S12R.tail 4 = 0 ∧ S12R.head 4 = 2 := by
    dsimp only [S12R, MGraph.applyBatch, MGraph.applyUpdate]
    exact ⟨hS11.1, by change S11.E.erase 1 = {4}; rw [hS11.2.1]; decide, hS11.2.2.2.2.1, hS11.2.2.2.2.2⟩
  have hB01 : exSwSInit.BatchIsValid exSwU01 := by
    simp [MGraph.BatchIsValid, MGraph.UpdateIsValid, MGraph.applyUpdate, exSwSInit, exSwU01]
  have hB02 : S01.BatchIsValid exSwU02 := by
    simp [MGraph.BatchIsValid, MGraph.UpdateIsValid, exSwU02, hS01.2.1]
  have hB11 : exSwSInit.BatchIsValid exSwU11 := by
    simp [MGraph.BatchIsValid, MGraph.UpdateIsValid, exSwSInit, exSwU11]
  have hB12 : S11.BatchIsValid exSwU12 := by
    dsimp only [S11]
    simp [MGraph.BatchIsValid, MGraph.UpdateIsValid, MGraph.applyBatch, MGraph.applyUpdate,
      exSwSInit, exSwU11, exSwU12, Function.update]
  have hB12R : S11.BatchIsValid [.delete 1] := by
    simp [MGraph.BatchIsValid, MGraph.UpdateIsValid, hS11.2.1]
  have hEnc01 : exSwSInit.batchEnc exSwU01 ≤ 7 := by
    simp only [exSwU01, MGraph.batchEnc, MGraph.updateEnc]
    have hsp := exSw_updateEnc_split_le (exSwSInit.applyUpdate (.delete 0)) 2 3 {4} {4}
    have hcard : (exSwSInit.applyUpdate (.delete 0)).E.card = 2 := by simp [MGraph.applyUpdate, exSwSInit]
    simp only [MGraph.updateEnc] at hsp; omega
  have hEnc12 : S11.batchEnc exSwU12 ≤ 11 := by
    simp only [exSwU12, MGraph.batchEnc, MGraph.updateEnc]
    have hs1 := exSw_updateEnc_split_le (S11.applyUpdate (.delete 1)) 0 1 {4} {4}
    have hs2 := exSw_updateEnc_split_le ((((S11.applyUpdate (.delete 1)).applyUpdate
      (.split 0 1 {4} {4})).applyUpdate (.insert 2 0 1))) 2 3 {4} {4}
    have hc1 : (S11.applyUpdate (.delete 1)).E.card = 1 := by simp [MGraph.applyUpdate, hS11.2.1]
    have hc2 : ((((S11.applyUpdate (.delete 1)).applyUpdate
        (.split 0 1 {4} {4})).applyUpdate (.insert 2 0 1))).E.card = 2 := by
      simp [MGraph.applyUpdate, hS11.2.1]
    simp only [MGraph.updateEnc] at hs1 hs2; omega
  have hlog26 : 1 ≤ Real.log (26 : ℝ) := by
    have : Real.exp 1 < 26 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    exact le_of_lt ((Real.lt_log_iff_exp_lt (by norm_num)).2 this)
  have rBound (r t : ℕ) (hr : r ≤ 4) : (r : ℝ) ≤ exSwParams.c_R * ((20 : ℝ) / (2 : ℝ) +
      (((Finset.Icc 1 t).sum fun s => (exSwDyn.U s).length : ℕ) : ℝ) * (Real.log ((4 : ℝ) + 2)) ^ 2 + 1) := by
    have hnn : 0 ≤ (((Finset.Icc 1 t).sum fun s => (exSwDyn.U s).length : ℕ) : ℝ) * (Real.log ((4 : ℝ) + 2)) ^ 2 := by
      positivity
    have hr' : (r : ℝ) ≤ (4 : ℝ) := by exact_mod_cast hr
    simp only [exSwParams]; rw [one_mul, show (20 : ℝ) / (2 : ℝ) = 10 by norm_num]; linarith [hnn, hr']
  rcases exSw_roots_eq with ⟨⟨r00, r01, r02, r03⟩, ⟨r10, r11, r12, r13⟩, ⟨re0, re1, re2, re3⟩⟩
  refine ⟨fun restarts _ => ?_, ?_⟩
  · let b0 := decide (1 ∈ restarts 0)
    let b01 := b0 || decide (1 ∈ restarts 1)
    let b012 := b01 || decide (1 ∈ restarts 2)
    let c0 := (restarts 0).length
    let c1 := (restarts 1).length
    let c2 := (restarts 2).length
    have hPre0 : exSwRestartTool.runAfterUpdate 2 20 4 exSwDyn restarts 0 =
        ((0, exSwSInit, exSwSInit, false, false, 0), fun _ => []) := rfl
    have hPost0 : exSwRestartTool.runAfterRestarts 2 20 4 exSwDyn restarts 0 =
        (0, exSwSInit, exSwSInit, b0, false, c0) := by
      rw [SparseCoreRestartTool.runAfterRestarts, hPre0, exSwRestartTool_foldl_restart]
      simp only [Bool.false_or, Nat.zero_add]; rfl
    have hPre1 : exSwRestartTool.runAfterUpdate 2 20 4 exSwDyn restarts 1 =
        ((1, S01, S11, b0, false, c0),
          fun j => if j = 0 then exSwU01 else exSwU11) := by
      rw [exSwRestartTool.runAfterUpdate_succ 2 20 4 exSwDyn restarts 0, hPost0]
      dsimp only [exSwRestartTool]
      exact Prod.ext (by simp [S01, S11]) (funext fun j => by by_cases hj : j = 0 <;> simp [hj])
    have hPost1 : exSwRestartTool.runAfterRestarts 2 20 4 exSwDyn restarts 1 =
        (1, S01, S11, b01, false, c0 + c1) := by
      rw [SparseCoreRestartTool.runAfterRestarts, hPre1]
      dsimp only
      rw [exSwRestartTool_foldl_restart]
    have hPre2 : exSwRestartTool.runAfterUpdate 2 20 4 exSwDyn restarts 2 =
        ((2, S02, if b01 then S12R else S12, b01, b01, c0 + c1),
          fun j => if j = 0 then exSwU02 else if b01 then [.delete 1] else exSwU12) := by
      rw [exSwRestartTool.runAfterUpdate_succ 2 20 4 exSwDyn restarts 1, hPost1]
      dsimp only [exSwRestartTool]
      exact Prod.ext (by cases b01 <;> simp [S02, S12, S12R])
        (funext fun j => by by_cases hj : j = 0 <;> simp [hj])
    have hPost2 : exSwRestartTool.runAfterRestarts 2 20 4 exSwDyn restarts 2 =
        (2, S02, if b01 then S12R else S12, b012, b01, c0 + c1 + c2) := by
      rw [SparseCoreRestartTool.runAfterRestarts, hPre2]
      dsimp only
      rw [exSwRestartTool_foldl_restart]
    have hSJ0 (a : ℕ) (b c : MGraph) (d e : Bool) (f : ℕ) :
        exSwRestartTool.S (a, b, c, d, e, f) 0 = b := by simp [exSwRestartTool]
    have hSJ1 (a : ℕ) (b c : MGraph) (d e : Bool) (f : ℕ) :
        exSwRestartTool.S (a, b, c, d, e, f) 1 = c := by simp [exSwRestartTool]
    have hLJ0 (a : ℕ) (b c : MGraph) (d e : Bool) (f : ℕ) :
        exSwRestartTool.lsfs (a, b, c, d, e, f) 0 = if a = 0 then exSwL0 else exSwL01 := by
      simp [exSwRestartTool]
    have hLJ1 (a : ℕ) (b c : MGraph) (d e : Bool) (f : ℕ) :
        exSwRestartTool.lsfs (a, b, c, d, e, f) 1 =
          if a ≤ 1 ∨ e then exSwL0 else exSwLempty := by
      simp [exSwRestartTool]
    have hSame : ∀ s ≤ 2, ∀ j < 2,
        (exSwRestartTool.S (exSwRestartTool.runAfterRestarts 2 20 4 exSwDyn restarts s) j).E =
        (coreGraph (exSwDyn.G s)
          (exSwRestartTool.lsfs (exSwRestartTool.runAfterRestarts 2 20 4 exSwDyn restarts s) j)).E := by
      intro s hs j hj
      rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2) with rfl | rfl | rfl <;>
        rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> dsimp only [coreGraph]
      · rw [hPost0, hSJ0, hLJ0]; simp [exSwSInit, hG0_E, exSwL0]; decide
      · rw [hPost0, hSJ1, hLJ1]; simp [exSwSInit, hG0_E, exSwL0]; decide
      · rw [hPost1, hSJ0, hLJ0]; simp [hS01.2.1, hG1_E, exSwL01]; decide
      · rw [hPost1, hSJ1, hLJ1]; simp [hS11.2.1, hG1_E, exSwL0]; decide
      · rw [hPost2, hSJ0, hLJ0]; simp [hS02.2.1, hG2_E, exSwL01]; decide
      · rw [hPost2, hSJ1, hLJ1]
        cases hr : b01
        · simp only [Bool.false_eq_true, show ¬(2 ≤ 1) by omega, or_self, ↓reduceIte]
          rw [hS12.2.1, hG2_E]; simp [exSwLempty]; decide
        · simp only [or_true, ↓reduceIte]
          rw [hS12R.2.1, hG2_E]; simp [exSwL0]; decide
    have hwstr3 : ∀ s ≤ 2, ∀ j < 2,
        (exSwRestartTool.lsfs (exSwRestartTool.runAfterRestarts 2 20 4 exSwDyn restarts s) j).wstr =
          fun _ => 3 := fun s _ j _ => by
      rcases hst : exSwRestartTool.runAfterRestarts 2 20 4 exSwDyn restarts s with ⟨a, b, c, d, e, f⟩
      dsimp only [exSwRestartTool]
      by_cases hj0 : j = 0
      · simp only [hj0, ↓reduceIte]
        by_cases ha0 : a = 0 <;> simp [ha0, exSwL0, exSwL01]
      · simp only [hj0, ↓reduceIte]
        by_cases hcond : a ≤ 1 ∨ e = true <;> simp [hcond, exSwL0, exSwLempty]
    have hcoreW : ∀ s₀ ≤ 2, ∀ t ≤ 2 - s₀, ∀ j < 2,
        ∀ e ∈ (exSwRestartTool.S (exSwRestartTool.runAfterRestarts 2 20 4 exSwDyn restarts (s₀ + t)) j).E,
        exSwRestartTool.coreWFrom 2 20 4 exSwDyn restarts (fun _ _ => 1) s₀ j t e = 6 := by
      intro s₀ hs₀ t ht j hj e he
      have hst : s₀ + t ≤ 2 := by omega
      have heC := (hSame (s₀ + t) hst j hj) ▸ he
      dsimp only [SparseCoreRestartTool.coreWFrom, passSparseCoreW, passCoreW]
      have hemb : ∀ x, exSwRestartTool.emb
          (exSwRestartTool.runAfterRestarts 2 20 4 exSwDyn restarts (s₀ + t)) j x = [(x, true)] :=
        fun _ => rfl
      simp_rw [hemb]
      rw [hwstr3 (s₀ + t) hst j hj]
      have hEq : (∑ x ∈ (coreGraph (exSwDyn.G (s₀ + t))
            (exSwRestartTool.lsfs (exSwRestartTool.runAfterRestarts 2 20 4 exSwDyn restarts (s₀ + t)) j)).E,
            ((3 : ℝ) * 1) * walkCount [(x, true)] e) =
          ∑ x ∈ (coreGraph (exSwDyn.G (s₀ + t))
            (exSwRestartTool.lsfs (exSwRestartTool.runAfterRestarts 2 20 4 exSwDyn restarts (s₀ + t)) j)).E,
            if x = e then (3 : ℝ) else 0 :=
        Finset.sum_congr rfl fun x _ => by
          by_cases hxe : x = e
          · subst hxe; simp [walkCount]
          · simp [walkCount, hxe]
      have hsum1 : (∑ x ∈ (coreGraph (exSwDyn.G (s₀ + t))
            (exSwRestartTool.lsfs (exSwRestartTool.runAfterRestarts 2 20 4 exSwDyn restarts (s₀ + t)) j)).E,
            ((3 : ℝ) * 1) * walkCount [(x, true)] e) = 3 := by
        rw [hEq, Finset.sum_ite_eq']
        simp only [heC, ↓reduceIte]
      rw [hsum1]; norm_num
    have hlog6 : |Real.log (6 : ℝ)| ≤ 10 := by
      rw [abs_of_nonneg (Real.log_nonneg (by norm_num))]
      exact le_trans (le_of_lt log_six_lt_two) (by norm_num)
    have hlog3 : |Real.log (3 : ℝ)| ≤ 10 := by
      rw [abs_of_nonneg (Real.log_nonneg (by norm_num))]
      exact le_trans (Real.log_le_log (by norm_num) (by norm_num))
        (le_trans (le_of_lt log_six_lt_two) (by norm_num))
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht j hj
      rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl <;>
        rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · rw [hPost0, hLJ0, hSJ0]; simp only [↓reduceIte]
        refine ⟨(exSwL_holds_all hG0_V (hG_tail 0) (hG_head 0) hG0_val).1 (by rw [hG0_E]; decide), ?_, fun _ => ?_⟩
        · refine exSw_sparsified_of_eq rfl (by rw [hG0_E]; decide) (fun e he => ?_) rfl ?_
          · have : e = 0 ∨ e = 1 ∨ e = 4 := by simpa [exSwSInit] using he
            rcases this with rfl | rfl | rfl <;>
              simp [exSwSInit, r00, r01, r02, r03, hG_tail 0, hG_head 0, exSwG0]
          · simp [MGraph.m, hG0_E, exSwSInit]; norm_num
        · exact rBound _ 0 (by simp [exSwL0])
      · rw [hPost0, hLJ1, hSJ1]; simp only [show (0 : ℕ) ≤ 1 by omega, true_or, ↓reduceIte]
        refine ⟨(exSwL_holds_all hG0_V (hG_tail 0) (hG_head 0) hG0_val).1 (by rw [hG0_E]; decide), ?_, fun _ => ?_⟩
        · refine exSw_sparsified_of_eq rfl (by rw [hG0_E]; decide) (fun e he => ?_) rfl ?_
          · have : e = 0 ∨ e = 1 ∨ e = 4 := by simpa [exSwSInit] using he
            rcases this with rfl | rfl | rfl <;>
              simp [exSwSInit, r00, r01, r02, r03, hG_tail 0, hG_head 0, exSwG0]
          · simp [MGraph.m, hG0_E, exSwSInit]; norm_num
        · exact rBound _ 0 (by simp [exSwL0])
      · rw [hPost1, hLJ0, hSJ0]; simp only [show (1 : ℕ) ≠ 0 by omega, ↓reduceIte]
        refine ⟨(exSwL_holds_all hG1_V (hG_tail 1) (hG_head 1) hG1_val).2.1 (by rw [hG1_E]; decide), ?_, fun _ => ?_⟩
        · refine exSw_sparsified_of_eq hS01.1 (by rw [hG1_E]; exact hS01.2.1) (fun e he => ?_) rfl ?_
          · have : e = 1 ∨ e = 3 ∨ e = 4 := by rw [hS01.2.1] at he; simpa using he
            rcases this with rfl | rfl | rfl
            · simp [hS01.2.2.1, hS01.2.2.2.1, r10, r12, hG_tail 1, hG_head 1, exSwG0]
            · simp [hS01.2.2.2.2.1, hS01.2.2.2.2.2.1, r12, r13, hG_tail 1, hG_head 1, exSwG0]
            · simp [hS01.2.2.2.2.2.2.1, hS01.2.2.2.2.2.2.2, r11, r13, hG_tail 1, hG_head 1, exSwG0]
          · simp [MGraph.m, hG1_E, hS01.2.1]; norm_num
        · exact rBound _ 1 (by simp [exSwL01])
      · rw [hPost1, hLJ1, hSJ1]; simp only [show (1 : ℕ) ≤ 1 by omega, true_or, ↓reduceIte]
        refine ⟨(exSwL_holds_all hG1_V (hG_tail 1) (hG_head 1) hG1_val).1 (by rw [hG1_E]; decide), ?_, fun _ => ?_⟩
        · refine exSw_sparsified_of_eq hS11.1 (by rw [hG1_E]; exact hS11.2.1) (fun e he => ?_) rfl ?_
          · have : e = 1 ∨ e = 4 := by rw [hS11.2.1] at he; simpa using he
            rcases this with rfl | rfl
            · simp [hS11.2.2.1, hS11.2.2.2.1, r00, r02, hG_tail 1, hG_head 1, exSwG0]
            · simp [hS11.2.2.2.2.1, hS11.2.2.2.2.2, r01, r03, hG_tail 1, hG_head 1, exSwG0]
          · simp [MGraph.m, hG1_E, hS11.2.1]; norm_num
        · exact rBound _ 1 (by simp [exSwL0])
      · rw [hPost2, hLJ0, hSJ0]; simp only [show (2 : ℕ) ≠ 0 by omega, ↓reduceIte]
        refine ⟨(exSwL_holds_all hG2_V (hG_tail 2) (hG_head 2) hG2_val).2.1 (by rw [hG2_E]; decide), ?_, fun _ => ?_⟩
        · refine exSw_sparsified_of_eq hS02.1 (by rw [hG2_E]; exact hS02.2.1) (fun e he => ?_) rfl ?_
          · have : e = 3 ∨ e = 4 := by rw [hS02.2.1] at he; simpa using he
            rcases this with rfl | rfl
            · simp [hS02.2.2.1, hS02.2.2.2.1, r12, r13, hG_tail 2, hG_head 2, exSwG0]
            · simp [hS02.2.2.2.2.1, hS02.2.2.2.2.2, r11, r13, hG_tail 2, hG_head 2, exSwG0]
          · simp [MGraph.m, hG2_E, hS02.2.1]; norm_num
        · exact rBound _ 2 (by simp [exSwL01])
      · rw [hPost2, hLJ1, hSJ1]
        cases hr : b01
        · simp only [Bool.false_eq_true, show ¬(2 ≤ 1) by omega, or_self, ↓reduceIte]
          refine ⟨(exSwL_holds_all hG2_V (hG_tail 2) (hG_head 2) hG2_val).2.2, ?_, fun _ => ?_⟩
          · refine exSw_sparsified_of_eq hS12.1 (by rw [hG2_E]; exact hS12.2.1) (fun e he => ?_) rfl ?_
            · have : e = 2 ∨ e = 3 ∨ e = 4 := by rw [hS12.2.1] at he; simpa using he
              rcases this with rfl | rfl | rfl
              · simp [hS12.2.2.1, hS12.2.2.2.1, re0, re1, hG_tail 2, hG_head 2, exSwG0]
              · simp [hS12.2.2.2.2.1, hS12.2.2.2.2.2.1, re2, re3, hG_tail 2, hG_head 2, exSwG0]
              · simp [hS12.2.2.2.2.2.2.1, hS12.2.2.2.2.2.2.2, re1, re3, hG_tail 2, hG_head 2, exSwG0]
            · simp [MGraph.m, hG2_E, hS12.2.1]; norm_num
          · exact rBound _ 2 (by simp [exSwLempty])
        · simp only [or_true, ↓reduceIte]
          refine ⟨(exSwL_holds_all hG2_V (hG_tail 2) (hG_head 2) hG2_val).1 (by rw [hG2_E]; decide), ?_, fun _ => ?_⟩
          · refine exSw_sparsified_of_eq hS12R.1 (by rw [hG2_E, hS12R.2.1]; decide) (fun e he => ?_) rfl ?_
            · have : e = 4 := by rw [hS12R.2.1] at he; simpa using he
              subst this; simp [hS12R.2.2.1, hS12R.2.2.2, r01, r03, hG_tail 2, hG_head 2, exSwG0]
            · simp [MGraph.m, hG2_E, hS12R.2.1]; norm_num
          · exact rBound _ 2 (by simp [exSwL0])
    · intro t ht1 ht2 j hj
      rcases (by omega : t = 1 ∨ t = 2) with rfl | rfl <;>
        rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · rw [show (1 : ℕ) - 1 = 0 from rfl, hPost0, hPost1, hPre1]
        dsimp only
        rw [hLJ0, hLJ0, hSJ0, hSJ0]
        simp only [show (1 : ℕ) ≠ 0 by omega, ↓reduceIte]
        exact ⟨by simp [exSwL0, exSwL01, exSwF0, exSwF01], fun _ _ _ _ => rfl,
          fun _ _ ⟨_, hu, h⟩ => by dsimp only [exSwDyn] at hu; simp at hu; subst hu; simp [Update.Inserts] at h,
          hB01, rfl⟩
      · rw [show (1 : ℕ) - 1 = 0 from rfl, hPost0, hPost1, hPre1]
        dsimp only
        rw [hLJ1, hLJ1, hSJ1, hSJ1]
        simp only [show (0 : ℕ) ≤ 1 by omega, show (1 : ℕ) ≤ 1 by omega, show (1 : ℕ) ≠ 0 by omega,
          true_or, ↓reduceIte]
        exact ⟨by simp [exSwL0], fun _ _ _ _ => trivial,
          fun _ _ ⟨_, hu, h⟩ => by dsimp only [exSwDyn] at hu; simp at hu; subst hu; simp [Update.Inserts] at h,
          hB11, rfl⟩
      · rw [show (2 : ℕ) - 1 = 1 from rfl, hPost1, hPost2, hPre2]
        dsimp only
        rw [hLJ0, hLJ0, hSJ0, hSJ0]
        simp only [show (1 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 0 by omega, ↓reduceIte]
        exact ⟨fun _ h => h, fun _ _ _ _ => trivial,
          fun _ _ ⟨_, hu, h⟩ => by dsimp only [exSwDyn] at hu; simp at hu; subst hu; simp [Update.Inserts] at h,
          hB02, rfl⟩
      · rw [show (2 : ℕ) - 1 = 1 from rfl, hPost1, hPost2, hPre2]
        dsimp only
        rw [hLJ1, hLJ1, hSJ1, hSJ1]
        cases hr : b01
        · simp only [Bool.false_eq_true, show (1 : ℕ) ≤ 1 by omega, show ¬(2 ≤ 1) by omega,
            show (1 : ℕ) ≠ 0 by omega, true_or, or_self, ↓reduceIte]
          exact ⟨by simp [exSwL0, exSwLempty, exSwFempty], fun _ _ _ _ => rfl,
            fun _ _ ⟨_, hu, h⟩ => by dsimp only [exSwDyn] at hu; simp at hu; subst hu; simp [Update.Inserts] at h,
            hB12, rfl⟩
        · simp only [show (1 : ℕ) ≤ 1 by omega, show (1 : ℕ) ≠ 0 by omega,
            true_or, or_true, ↓reduceIte]
          exact ⟨fun _ h => h, fun _ _ _ _ => trivial,
            fun _ _ ⟨_, hu, h⟩ => by dsimp only [exSwDyn] at hu; simp at hu; subst hu; simp [Update.Inserts] at h,
            hB12R, rfl⟩
    · intro r _ p j' _
      set st' := List.foldl exSwRestartTool.restart (exSwRestartTool.runAfterUpdate 2 20 4 exSwDyn restarts r).1 p
      have hC : exSwRestartTool.cost (exSwRestartTool.restart st' j') = exSwRestartTool.cost st' + 1 := by
        rcases st' with ⟨_, _, _, _, _, _⟩; rfl
      refine ⟨fun _ _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩, by rw [hC]; omega, ?_⟩
      rw [hC, Nat.cast_add, Nat.cast_one]
      simp only [exSwParams, pow_one, show ((20 : ℕ) : ℝ) + 1 = 21 by norm_num]
      push_cast
      rw [show (20 : ℝ) + 4 + 2 = 26 by norm_num]
      nlinarith [hlog26]
    · intro s₀ t hst ht j hj hFresh _
      have hU11 : (Finset.Icc 1 1).sum (fun s => (exSwDyn.U s).length) = 1 := by decide
      have hU12 : (Finset.Icc 1 2).sum (fun s => (exSwDyn.U s).length) = 2 := by decide
      have hU22 : (Finset.Icc 2 2).sum (fun s => (exSwDyn.U s).length) = 1 := by decide
      have h30 : exSwParams.γ_r 20 * (((20 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) + 0) = 30 := by
        simp [exSwParams]; norm_num
      have h33 : exSwParams.γ_r 20 * (((20 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) + ((1 : ℕ) : ℝ)) = 33 := by
        simp [exSwParams]; norm_num
      have h36 : exSwParams.γ_r 20 * (((20 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) + ((2 : ℕ) : ℝ)) = 36 := by
        simp [exSwParams]; norm_num
      have hE01_dec : exSwSInit.batchEnc exSwU11 = 1 := by
        simp [MGraph.batchEnc, MGraph.updateEnc, exSwU11]
      have hE02_dec : S01.batchEnc exSwU02 = 1 := by
        simp [MGraph.batchEnc, MGraph.updateEnc, exSwU02]
      have hE12R_dec : S11.batchEnc [.delete 1] = 1 := by
        simp [MGraph.batchEnc, MGraph.updateEnc]
      rcases (by omega : s₀ = 0 ∨ s₀ = 1 ∨ s₀ = 2) with rfl | rfl | rfl <;>
        rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl <;>
        rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      all_goals try omega
      · simp only [Finset.Icc_eq_empty_of_lt (by omega : 0 < 0 + 1), Finset.sum_empty,
          Nat.cast_zero, mul_zero, le_refl, true_and]
        norm_num [exSwParams]
      · simp only [Finset.Icc_eq_empty_of_lt (by omega : 0 < 0 + 1), Finset.sum_empty,
          Nat.cast_zero, mul_zero, le_refl, true_and]
        norm_num [exSwParams]
      · rw [show (0 : ℕ) + 1 = 1 from rfl, hU11]
        refine ⟨by rw [Finset.Icc_self, Finset.sum_singleton]; simp [hPre1, exSwParams, exSwU01], ?_⟩
        rw [Finset.Icc_self, Finset.sum_singleton, show (1 : ℕ) - 1 = 0 from rfl, hPost0, hPre1, hSJ0]
        simp only [↓reduceIte]
        rw [h33]
        have : (exSwSInit.batchEnc exSwU01 : ℝ) ≤ 7 := by exact_mod_cast hEnc01
        linarith
      · rw [show (0 : ℕ) + 1 = 1 from rfl, hU11]
        refine ⟨by rw [Finset.Icc_self, Finset.sum_singleton]; simp [hPre1, exSwParams, exSwU11], ?_⟩
        rw [Finset.Icc_self, Finset.sum_singleton, show (1 : ℕ) - 1 = 0 from rfl, hPost0, hPre1, hSJ1]
        simp only [show (1 : ℕ) ≠ 0 by omega, ↓reduceIte, hE01_dec, h33]
        norm_num
      · rw [show (0 : ℕ) + 1 = 1 from rfl, hU12]
        refine ⟨by
          rw [Finset.sum_Icc_succ_top (by omega), Finset.Icc_self, Finset.sum_singleton]
          simp [hPre1, hPre2, exSwParams, exSwU01, exSwU02]; norm_num, ?_⟩
        rw [Finset.sum_Icc_succ_top (by omega), Finset.Icc_self, Finset.sum_singleton,
          show (1 : ℕ) - 1 = 0 from rfl, show (2 : ℕ) - 1 = 1 from rfl, hPost0, hPost1, hPre1, hPre2]
        dsimp only
        rw [hSJ0, hSJ0]
        simp only [↓reduceIte, hE02_dec]
        rw [h36]
        have : (exSwSInit.batchEnc exSwU01 : ℝ) ≤ 7 := by exact_mod_cast hEnc01
        push_cast; linarith
      · rw [show (0 : ℕ) + 1 = 1 from rfl, hU12]
        cases hr : b01
        · refine ⟨by
            rw [Finset.sum_Icc_succ_top (by omega), Finset.Icc_self, Finset.sum_singleton]
            simp [hPre1, hPre2, hr, exSwParams, exSwU11, exSwU12]; norm_num, ?_⟩
          rw [Finset.sum_Icc_succ_top (by omega), Finset.Icc_self, Finset.sum_singleton,
            show (1 : ℕ) - 1 = 0 from rfl, show (2 : ℕ) - 1 = 1 from rfl, hPost0, hPost1, hPre1, hPre2]
          dsimp only
          rw [hSJ1, hSJ1]
          simp only [show (1 : ℕ) ≠ 0 by omega, hr, Bool.false_eq_true, ↓reduceIte, hE01_dec]
          rw [h36]
          have : (S11.batchEnc exSwU12 : ℝ) ≤ 11 := by exact_mod_cast hEnc12
          push_cast; linarith
        · refine ⟨by
            rw [Finset.sum_Icc_succ_top (by omega), Finset.Icc_self, Finset.sum_singleton]
            simp [hPre1, hPre2, hr, exSwParams, exSwU11], ?_⟩
          rw [Finset.sum_Icc_succ_top (by omega), Finset.Icc_self, Finset.sum_singleton,
            show (1 : ℕ) - 1 = 0 from rfl, show (2 : ℕ) - 1 = 1 from rfl, hPost0, hPost1, hPre1, hPre2]
          dsimp only
          rw [hSJ1, hSJ1]
          simp only [show (1 : ℕ) ≠ 0 by omega, hr, ↓reduceIte, hE01_dec, hE12R_dec, h36]
          norm_num
      · simp only [Finset.Icc_eq_empty_of_lt (by omega : 1 < 1 + 1), Finset.sum_empty,
          Nat.cast_zero, mul_zero, le_refl, true_and]
        norm_num [exSwParams]
      · simp only [Finset.Icc_eq_empty_of_lt (by omega : 1 < 1 + 1), Finset.sum_empty,
          Nat.cast_zero, mul_zero, le_refl, true_and]
        norm_num [exSwParams]
      · rw [show (1 : ℕ) + 1 = 2 from rfl, hU22]
        refine ⟨by rw [Finset.Icc_self, Finset.sum_singleton]; simp [hPre2, exSwParams, exSwU02], ?_⟩
        rw [Finset.Icc_self, Finset.sum_singleton, show (2 : ℕ) - 1 = 1 from rfl, hPost1, hPre2, hSJ0]
        simp only [↓reduceIte, hE02_dec, h33]
        norm_num
      · have hr : b01 = true := by
          rcases hFresh with h | h1
          · omega
          · simp [b01, h1]
        rw [show (1 : ℕ) + 1 = 2 from rfl, hU22]
        refine ⟨by rw [Finset.Icc_self, Finset.sum_singleton]; simp [hPre2, hr, exSwParams], ?_⟩
        rw [Finset.Icc_self, Finset.sum_singleton, show (2 : ℕ) - 1 = 1 from rfl, hPost1, hPre2, hSJ1]
        simp only [show (1 : ℕ) ≠ 0 by omega, hr, ↓reduceIte, hE12R_dec, h33]
        norm_num
      · simp only [Finset.Icc_eq_empty_of_lt (by omega : 2 < 2 + 1), Finset.sum_empty,
          Nat.cast_zero, mul_zero, le_refl, true_and]
        norm_num [exSwParams]
      · simp only [Finset.Icc_eq_empty_of_lt (by omega : 2 < 2 + 1), Finset.sum_empty,
          Nat.cast_zero, mul_zero, le_refl, true_and]
        norm_num [exSwParams]
    · intro s₀ hs₀ j hj
      refine ⟨10, fun t ht => ?_⟩
      have hcoreC : ∀ s e, exSwRestartTool.coreCFrom 2 20 4 exSwDyn restarts (fun _ _ => 0) s₀ j s e = 0 :=
        fun s e => by simp [SparseCoreRestartTool.coreCFrom, passSparseCoreC, passCoreC]
      refine ⟨fun _ _ => Finset.sum_eq_zero fun _ _ => by simp [SparseCoreRestartTool.coreInstanceFrom, hcoreC],
        ⟨fun _ _ => Finset.sum_eq_zero fun _ _ => by simp [SparseCoreRestartTool.coreInstanceFrom, hcoreC],
          fun e he => by
            simp only [SparseCoreRestartTool.coreInstanceFrom] at he
            rw [hcoreC, mul_zero, abs_zero, hcoreW s₀ hs₀ t ht j hj e he]; norm_num⟩,
        fun e he t' ht' hNotIns => by
          by_cases he' : e ∈ (exSwRestartTool.S
              (exSwRestartTool.runAfterRestarts 2 20 4 exSwDyn restarts (s₀ + t')) j).E
          · rw [hcoreW s₀ hs₀ t ht j hj e (by simpa [SparseCoreRestartTool.coreInstanceFrom] using he),
              hcoreW s₀ hs₀ t' (le_trans ht' ht) j hj e he']; norm_num
          · exfalso
            simp only [SparseCoreRestartTool.coreInstanceFrom] at he
            rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;>
              rcases (by omega : s₀ = 0 ∨ s₀ = 1 ∨ s₀ = 2) with rfl | rfl | rfl <;>
              rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl <;>
              rcases (by omega : t' = 0 ∨ t' = 1 ∨ t' = 2) with rfl | rfl | rfl
            all_goals try (exfalso; omega)
            all_goals try (simp only [Nat.zero_add, Nat.add_zero] at he he'; try simp only [show (1 : ℕ) + 1 = 2 from rfl] at he he')
            · simp [hPost0] at he he'; exact he' he
            · rw [hPost1] at he; rw [hPost0] at he'; rw [hSJ0] at he he'
              rw [hS01.2.1] at he; change e ∉ exSwSInit.E at he'
              rcases Finset.mem_insert.mp he with rfl | he1
              · exact he' (by simp [exSwSInit])
              · rcases Finset.mem_insert.mp he1 with rfl | he2
                · exact hNotIns 1 (by omega) (by omega) (.insert 3 2 3)
                    (by simp [SparseCoreRestartTool.coreInstanceFrom, hPre1, exSwU01]) rfl
                · simp only [Finset.mem_singleton] at he2; subst he2; exact he' (by simp [exSwSInit])
            · simp [hPost1] at he he'; exact he' he
            · rw [hPost2] at he; rw [hPost0] at he'; rw [hSJ0] at he he'
              rw [hS02.2.1] at he; change e ∉ exSwSInit.E at he'
              rcases Finset.mem_insert.mp he with rfl | he1
              · exact hNotIns 1 (by omega) (by omega) (.insert 3 2 3)
                  (by simp [SparseCoreRestartTool.coreInstanceFrom, hPre1, exSwU01]) rfl
              · simp only [Finset.mem_singleton] at he1; subst he1; exact he' (by simp [exSwSInit])
            · rw [hPost2] at he; rw [hPost1] at he'; rw [hSJ0] at he he'
              rw [hS02.2.1] at he; rw [hS01.2.1] at he'
              rcases Finset.mem_insert.mp he with rfl | he1
              · exact he' (by decide)
              · simp only [Finset.mem_singleton] at he1; subst he1; exact he' (by decide)
            · simp [hPost2] at he he'; exact he' he
            · simp [hPost1] at he he'; exact he' he
            · rw [hPost2] at he; rw [hPost1] at he'; rw [hSJ0] at he he'
              rw [hS02.2.1] at he; rw [hS01.2.1] at he'
              rcases Finset.mem_insert.mp he with rfl | he1
              · exact he' (by decide)
              · simp only [Finset.mem_singleton] at he1; subst he1; exact he' (by decide)
            · simp [hPost2] at he he'; exact he' he
            · simp [hPost2] at he he'; exact he' he
            · simp [hPost0] at he he'; exact he' he
            · rw [hPost1] at he; rw [hPost0] at he'; rw [hSJ1] at he he'
              rw [hS11.2.1] at he; change e ∉ exSwSInit.E at he'
              rcases Finset.mem_insert.mp he with rfl | he1
              · exact he' (by simp [exSwSInit])
              · simp only [Finset.mem_singleton] at he1; subst he1; exact he' (by simp [exSwSInit])
            · simp [hPost1] at he he'; exact he' he
            · cases hr : b01
              · rw [hPost2] at he; rw [hPost0] at he'; rw [hSJ1] at he he'
                simp only [hr, Bool.false_eq_true, ↓reduceIte] at he
                rw [hS12.2.1] at he; change e ∉ exSwSInit.E at he'
                rcases Finset.mem_insert.mp he with rfl | he1
                · exact hNotIns 2 (by omega) (by omega) (.insert 2 0 1)
                    (by simp [SparseCoreRestartTool.coreInstanceFrom, hPre2, hr, exSwU12]) rfl
                · rcases Finset.mem_insert.mp he1 with rfl | he2
                  · exact hNotIns 2 (by omega) (by omega) (.insert 3 2 3)
                      (by simp [SparseCoreRestartTool.coreInstanceFrom, hPre2, hr, exSwU12]) rfl
                  · simp only [Finset.mem_singleton] at he2; subst he2; exact he' (by simp [exSwSInit])
              · rw [hPost2] at he; rw [hPost0] at he'; rw [hSJ1] at he he'
                simp only [hr, ↓reduceIte] at he
                rw [hS12R.2.1] at he; change e ∉ exSwSInit.E at he'
                have : e = 4 := by simpa using he
                subst this; exact he' (by simp [exSwSInit])
            · cases hr : b01
              · rw [hPost2] at he; rw [hPost1] at he'; rw [hSJ1] at he he'
                simp only [hr, Bool.false_eq_true, ↓reduceIte] at he
                rw [hS12.2.1] at he; rw [hS11.2.1] at he'
                rcases Finset.mem_insert.mp he with rfl | he1
                · exact hNotIns 2 (by omega) (by omega) (.insert 2 0 1)
                    (by simp [SparseCoreRestartTool.coreInstanceFrom, hPre2, hr, exSwU12]) rfl
                · rcases Finset.mem_insert.mp he1 with rfl | he2
                  · exact hNotIns 2 (by omega) (by omega) (.insert 3 2 3)
                      (by simp [SparseCoreRestartTool.coreInstanceFrom, hPre2, hr, exSwU12]) rfl
                  · simp only [Finset.mem_singleton] at he2; subst he2; exact he' (by decide)
              · rw [hPost2] at he; rw [hPost1] at he'; rw [hSJ1] at he he'
                simp only [hr, ↓reduceIte] at he
                rw [hS12R.2.1] at he; rw [hS11.2.1] at he'
                have : e = 4 := by simpa using he
                subst this; exact he' (by decide)
            · simp [hPost2] at he he'; exact he' he
            · simp [hPost1] at he he'; exact he' he
            · cases hr : b01
              · rw [hPost2] at he; rw [hPost1] at he'; rw [hSJ1] at he he'
                simp only [hr, Bool.false_eq_true, ↓reduceIte] at he
                rw [hS12.2.1] at he; rw [hS11.2.1] at he'
                rcases Finset.mem_insert.mp he with rfl | he1
                · exact hNotIns 1 (by omega) (by omega) (.insert 2 0 1)
                    (by simp [SparseCoreRestartTool.coreInstanceFrom, hPre2, hr, exSwU12]) rfl
                · rcases Finset.mem_insert.mp he1 with rfl | he2
                  · exact hNotIns 1 (by omega) (by omega) (.insert 3 2 3)
                      (by simp [SparseCoreRestartTool.coreInstanceFrom, hPre2, hr, exSwU12]) rfl
                  · simp only [Finset.mem_singleton] at he2; subst he2; exact he' (by decide)
              · rw [hPost2] at he; rw [hPost1] at he'; rw [hSJ1] at he he'
                simp only [hr, ↓reduceIte] at he
                rw [hS12R.2.1] at he; rw [hS11.2.1] at he'
                have : e = 4 := by simpa using he
                subst this; exact he' (by decide)
            · simp [hPost2] at he he'; exact he' he
            · simp [hPost2] at he he'; exact he' he,
        fun e he => by
          simp only [SparseCoreRestartTool.coreInstanceFrom] at he ⊢
          rw [hcoreW s₀ hs₀ t ht j hj e he]
          unfold coreLen; rw [hwstr3 (s₀ + t) (by omega) j hj]
          exact ⟨by norm_num, hlog6, by simp [exSwDyn], by simpa [exSwDyn] using hlog3⟩⟩
    · rw [hPost2]
      dsimp only [exSwRestartTool, exSwParams]
      rw [show (2 + 1 : ℕ) = 3 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_one]
      change ((3 + (c0 + c1 + c2) : ℕ) : ℝ) ≤
        10 * ((20 : ℝ) + 1) * ((2 : ℝ) + ((c0 + c1 + c2 : ℕ) : ℝ)) * 3 *
          Real.log ((20 : ℝ) + 4 + 2) ^ 1
      rw [show (20 : ℝ) + 4 + 2 = 26 by norm_num, pow_one]
      push_cast
      have hcnn : (0 : ℝ) ≤ (c0 : ℝ) + (c1 : ℝ) + (c2 : ℝ) := by positivity
      nlinarith [hlog26]
    · intro t ht e _
      rw [Finset.sum_range_succ, Finset.sum_range_one, hwstr3 t ht 0 (by omega), hwstr3 t ht 1 (by omega)]
      norm_num
    · intro _ _ _ _ _ _; rfl
    · intro t ht1 ht2 j hj e he u hu hIns
      rcases (by omega : t = 1 ∨ t = 2) with rfl | rfl <;>
        rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · rw [hPost0] at he; dsimp only [exSwRestartTool] at he
        have : u = .delete 0 ∨ u = .split 2 3 {4} {4} ∨ u = .insert 3 2 3 := by
          simpa [hPre1, exSwU01] using hu
        rcases this with rfl | rfl | rfl <;> (simp [Update.Inserts, exSwSInit] at hIns he; try omega)
      · have : u = .delete 0 := by simpa [hPre1, exSwU11] using hu
        subst this; simp [Update.Inserts] at hIns
      · have : u = .delete 1 := by simpa [hPre2, exSwU02] using hu
        subst this; simp [Update.Inserts] at hIns
      · rw [hPost1] at he; dsimp only [exSwRestartTool] at he
        simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte] at he
        rw [hS11.2.1] at he
        rw [hPre2] at hu
        cases hr : b01
        · simp only [hr, Bool.false_eq_true, ↓reduceIte] at hu
          have : u = .delete 1 ∨ u = .split 0 1 {4} {4} ∨ u = .insert 2 0 1 ∨
              u = .split 2 3 {4} {4} ∨ u = .insert 3 2 3 := by
            simpa [exSwU12] using hu
          rcases this with rfl | rfl | rfl | rfl | rfl <;> (simp [Update.Inserts] at hIns he; try omega)
        · simp only [hr, ↓reduceIte] at hu
          have : u = .delete 1 := by simpa using hu
          subst this; simp [Update.Inserts] at hIns
  · let restarts : ℕ → List ℕ := fun r => if r = 1 then [1] else []
    let b : ℕ → ℕ := fun s => if s ≤ 1 then 0 else 1
    have hPre0 : exSwRestartTool.runAfterUpdate 2 20 4 exSwDyn restarts 0 =
        ((0, exSwSInit, exSwSInit, false, false, 0), fun _ => []) := rfl
    have hPost0 : exSwRestartTool.runAfterRestarts 2 20 4 exSwDyn restarts 0 =
        (0, exSwSInit, exSwSInit, false, false, 0) := by
      rw [SparseCoreRestartTool.runAfterRestarts, hPre0]
      change List.foldl exSwRestartTool.restart _ [] = _
      exact List.foldl_nil
    have hPre1 : exSwRestartTool.runAfterUpdate 2 20 4 exSwDyn restarts 1 =
        ((1, S01, S11, false, false, 0), fun j => if j = 0 then exSwU01 else exSwU11) := by
      rw [exSwRestartTool.runAfterUpdate_succ 2 20 4 exSwDyn restarts 0, hPost0]
      dsimp only [exSwRestartTool]
      exact Prod.ext rfl (funext fun j => by by_cases hj : j = 0 <;> simp [hj])
    have hPost1 : exSwRestartTool.runAfterRestarts 2 20 4 exSwDyn restarts 1 =
        (1, S01, S11, true, false, 1) := by
      rw [SparseCoreRestartTool.runAfterRestarts, hPre1]
      simp [exSwRestartTool_foldl_restart, restarts]; rfl
    have hPre2 : exSwRestartTool.runAfterUpdate 2 20 4 exSwDyn restarts 2 =
        ((2, S02, S12R, true, true, 1), fun j => if j = 0 then exSwU02 else [.delete 1]) := by
      rw [exSwRestartTool.runAfterUpdate_succ 2 20 4 exSwDyn restarts 1, hPost1]
      dsimp only [exSwRestartTool]
      exact Prod.ext (by simp [S02, S12R]) (funext fun j => by by_cases hj : j = 0 <;> simp [hj])
    have h1 : ((exSwRestartTool.runAfterUpdate 2 20 4 exSwDyn restarts 1).2 (b 1)).length = 3 := by
      simp [b, hPre1, exSwU01]
    have h2 : ((exSwRestartTool.runAfterUpdate 2 20 4 exSwDyn restarts 2).2 (b 2)).length = 1 := by
      simp [b, hPre2]
    have hSum : (Finset.Icc 1 2).sum (fun s =>
        ((exSwRestartTool.runAfterUpdate 2 20 4 exSwDyn restarts s).2 (b s)).length) = 4 := by
      rw [Finset.sum_Icc_succ_top (by omega), Finset.Icc_self, Finset.sum_singleton, h1, h2]
    refine ⟨hSum, ?_⟩
    have hRHS : (Finset.Icc 1 2).sum (fun s => (exSwDyn.U s).length) = 2 := by decide
    rw [hSum, hRHS]
    norm_num [exSwParams]
