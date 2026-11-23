module

public import MinCostFlow.Chain.Ordered.Algorithm2Facts
import MinCostFlow.Chain.Ordered.ShiftPreserves
import MinCostFlow.Chain.Ordered.FindCycleProofs
import MinCostFlow.Chain.Ordered.Lemma5_11
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Unconditional loop invariants for Algorithm 2 with orders

This file proves the unconditional preservation lemmas for the inner shift loop of Algorithm 2 with
orders (`Ordered.algorithm2_loopWith` and `Ordered.algorithm2_loop`, paper Algorithm 2,
`jtree.tex` lines 757–772):

* `algorithm2_loopWith_preserves` / `algorithm2_loop_preserves`: preservation of `Ordered.ChainInv`,
  `Ordered.ChainBudgetInvWith`, top-level `(G 0, ℓ, g)`, `rebuildCount`, shift-count bounds,
  `branD < k`, link-cut tree operation counts, and `IsCirculation` for returned directions, by
  well-founded induction on `shiftRemainingBudget`.
* `algorithm2_loopWith_rec_props` / `algorithm2_loop_rec_props`: preservation of `recUpdates` and
  `ChainRecBound` across the shift loop.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

/-- Unconditional invariant preservation for `Ordered.algorithm2_loopWith` across all shift steps
before termination. -/
lemma algorithm2_loopWith_preserves {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden) (κ : ℝ)
    (extG : MGraph) (e2i i2e : ℕ → ℕ) (nf : ℕ) (g' ℓ' : ℕ → ℝ)
    (ch : ChainState cfg.T cfg.P) (branD : ℕ) (passes : Fin (cfg.P.d + 1) → ℕ)
    (lctOps : ℕ) (overflow : ℝ)
    (hInv : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch)
    (hBud : ChainBudgetInvWith cfg.TP cfg.LP cfg.N₀ ch overflow)
    (hShBound : ∀ i : Fin (cfg.P.d + 1),
      (ch.shiftCount i.val : ℝ) ≤ gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch.rebuildCount i.val)
    (hBranD : branD < cfg.P.k)
    (hFresh : FreshInv extG (ch.G 0) e2i i2e nf) (hℓR : LenInRange (max 0 cfg.Ψ) (ch.G 0) ch.ℓ) :
    let res := algorithm2_loopWith cfg κ extG e2i g' ℓ' ch branD passes lctOps
    let ch' := res.1
    let branD' := res.2.1
    let lctOps' := res.2.2.2.1
    let optΔ := res.2.2.2.2
    ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch' ∧
    ChainBudgetInvWith cfg.TP cfg.LP cfg.N₀ ch' overflow ∧
    ch'.G 0 = ch.G 0 ∧
    ch'.ℓ = ch.ℓ ∧
    ch'.g = ch.g ∧
    ch'.rebuildCount = ch.rebuildCount ∧
    (∀ i : Fin (cfg.P.d + 1), ch.shiftCount i.val ≤ ch'.shiftCount i.val) ∧
    (∀ i : Fin (cfg.P.d + 1),
      (ch'.shiftCount i.val : ℝ) ≤ gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch'.rebuildCount i.val) ∧
    branD' < cfg.P.k ∧
    lctOps' ≤ lctOps + 2 * (Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) + 2) *
      (1 + ∑ j ∈ Finset.range (cfg.P.d + 1), (ch'.shiftCount j - ch.shiftCount j)) ∧
    (∀ Δ, optΔ = some Δ → extG.IsCirculation Δ) := by
  have hvp0 : IsValidPair (ch.G 0) ch.ℓ (fun _ => 0) (fun _ => 0) :=
    ⟨fun _ _ => by simp [MGraph.demand], fun _ _ => by simp⟩
  have hFC := findCycle_spec_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P
    hV.hσ_mwu_mono hV.hTP hV.hLP hV.hMWU hV.hEmb hV.hγM₀ hV.hγk hInv hvp0
  set fc := algorithm1_findCycle ch
  set offTree := (walkEdges fc.2.1 \ ch.toTreeChain.chainTree.E).card
  have hoff_le : offTree ≤ Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) + 1 := by
    have h1 : (offTree : ℝ) ≤ 1 + cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) := hFC.2.2.1
    have h2 : (offTree : ℝ) ≤ ((Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) + 1 : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.le_ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2))]
    exact_mod_cast h2
  have hstepOps : 2 * (offTree + 1) ≤ 2 * (Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) + 2) := by omega
  set Ψ_g := alg2PsiGame cfg.Ψ cfg.P.M₀
  set Δ_ext := liftEdgeFn extG e2i fc.1
  set lctOps' := lctOps + 2 * (offTree + 1)
  have hfc_eq : (walkEdges (algorithm1_findCycle ch).2.1 \ ch.toTreeChain.chainTree.E).card = offTree := rfl
  rw [algorithm2_loopWith]
  dsimp only
  by_cases hGood : extG.inner g' Δ_ext / extG.lnorm ℓ' Δ_ext ≤ -(κ * cfg.α)
  · rw [dite_eq_left_iff.mpr fun h => absurd hGood h]
    refine ⟨hInv, hBud, rfl, rfl, rfl, rfl, fun _ => le_refl _, hShBound, hBranD, ?_, ?_⟩
    · dsimp only
      simp only [Nat.sub_self, Finset.sum_const_zero, add_zero, mul_one]
      rw [hfc_eq]
      omega
    · dsimp only
      rintro Δ hΔ
      injection hΔ with hΔ
      rw [← hΔ]
      exact hFresh.isCirculation_lift hFC.1
  · rw [dite_eq_right_iff.mpr fun h => absurd h hGood]
    cases hElig : findEligibleLevel cfg.P.d Ψ_g passes with
    | none =>
      refine ⟨hInv, hBud, rfl, rfl, rfl, rfl, fun _ => le_refl _, hShBound, hBranD, ?_,
        fun _ h => by simp at h⟩
      dsimp only
      simp only [Nat.sub_self, Finset.sum_const_zero, add_zero, mul_one]
      rw [hfc_eq]
      omega
    | some i =>
      dsimp only
      by_cases hCap : (ch.shiftCount i.val : ℝ) + 1 ≤ gameShiftBound cfg.P Ψ_g ch.rebuildCount i.val
      · rw [dite_eq_left_iff.mpr fun h => absurd hCap h]
        have hi_le : i.val ≤ cfg.P.d := Nat.lt_succ_iff.mp i.isLt
        have hS := shift_preserves_with_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P
          hV.hTP hV.hLP hV.hT hV.hL hV.hγM₀ hV.hγk hInv hℓR hBud i.val hi_le
        dsimp only at hS
        rcases hS with ⟨hInv1, hBud1, hG01, hℓ1, hg1, hSh1, hReb1, _, _⟩
        set ch1 := (algorithm1_shift cfg.T cfg.L cfg.P ch i.val).1
        have hShBound1 : ∀ j : Fin (cfg.P.d + 1),
            (ch1.shiftCount j.val : ℝ) ≤ gameShiftBound cfg.P Ψ_g ch1.rebuildCount j.val := by
          intro j
          rw [hSh1, hReb1]
          dsimp only
          by_cases hji : j.val = i.val
          · rw [ite_eq_left_iff.mpr fun h => absurd hji h, hji]
            push_cast
            exact hCap
          · rw [ite_eq_right_iff.mpr fun h => absurd h hji]
            exact hShBound j
        have hBranD1 : (if i.val < cfg.P.d then 0 else (branD + 1) % cfg.P.k) < cfg.P.k := by
          by_cases hi : i.val < cfg.P.d
          · rw [ite_eq_left_iff.mpr fun h => absurd hi h]; exact cfg.P.hk
          · rw [ite_eq_right_iff.mpr fun h => absurd h hi]; exact Nat.mod_lt _ cfg.P.hk
        have hFresh1 : FreshInv extG (ch1.G 0) e2i i2e nf := by
          rw [hG01]; exact hFresh
        have ih := algorithm2_loopWith_preserves hV κ extG e2i i2e nf g' ℓ' ch1
          (if i.val < cfg.P.d then 0 else (branD + 1) % cfg.P.k)
          (fun j => if i < j then 0
            else if j = i then (if ((if i.val < cfg.P.d then ch.bran i.val else branD) + 1) % cfg.P.k = 0 then passes i + 1 else passes i)
            else passes j)
          lctOps' overflow hInv1 hBud1 hShBound1 hBranD1 hFresh1 (by rw [hG01, hℓ1]; exact hℓR)
        dsimp only at ih
        rcases ih with ⟨hInvF, hBudF, hG0F, hℓF, hgF, hRebF, hShLeF, hShBF, hBranDF, hOpsF, hCircF⟩
        dsimp only [lctOps'] at hInvF hBudF hG0F hℓF hgF hRebF hShLeF hShBF hBranDF hOpsF hCircF
        have hle_sh : ∀ j, ch.shiftCount j ≤ ch1.shiftCount j := fun j => by
          rw [hSh1]; dsimp only
          by_cases hji : j = i.val
          · rw [ite_eq_left_iff.mpr fun h => absurd hji h, hji]; omega
          · rw [ite_eq_right_iff.mpr fun h => absurd h hji]
        refine ⟨hInvF, hBudF, hG0F.trans hG01, hℓF.trans hℓ1, hgF.trans hg1, hRebF.trans hReb1,
          fun j => le_trans (hle_sh j.val) (hShLeF j),
          hShBF, hBranDF, ?_, hCircF⟩
        have hsum_tot :
            ∑ j ∈ Finset.range (cfg.P.d + 1),
              ((algorithm2_loopWith cfg κ extG e2i g' ℓ' ch1
                (if i.val < cfg.P.d then 0 else (branD + 1) % cfg.P.k)
                (fun j => if i < j then 0
                  else if j = i then (if ((if i.val < cfg.P.d then ch.bran i.val else branD) + 1) % cfg.P.k = 0 then passes i + 1 else passes i)
                  else passes j) (lctOps + 2 * (offTree + 1))).1.shiftCount j - ch.shiftCount j) =
            1 + ∑ j ∈ Finset.range (cfg.P.d + 1),
              ((algorithm2_loopWith cfg κ extG e2i g' ℓ' ch1
                (if i.val < cfg.P.d then 0 else (branD + 1) % cfg.P.k)
                (fun j => if i < j then 0
                  else if j = i then (if ((if i.val < cfg.P.d then ch.bran i.val else branD) + 1) % cfg.P.k = 0 then passes i + 1 else passes i)
                  else passes j) (lctOps + 2 * (offTree + 1))).1.shiftCount j - ch1.shiftCount j) := by
          set chF := (algorithm2_loopWith cfg κ extG e2i g' ℓ' ch1
            (if i.val < cfg.P.d then 0 else (branD + 1) % cfg.P.k)
            (fun j => if i < j then 0
              else if j = i then (if ((if i.val < cfg.P.d then ch.bran i.val else branD) + 1) % cfg.P.k = 0 then passes i + 1 else passes i)
              else passes j) (lctOps + 2 * (offTree + 1))).1
          have hadd : ∀ j ∈ Finset.range (cfg.P.d + 1),
              chF.shiftCount j - ch.shiftCount j =
                (chF.shiftCount j - ch1.shiftCount j) + (ch1.shiftCount j - ch.shiftCount j) := by
            intro j hj
            have hle1 : ch.shiftCount j ≤ ch1.shiftCount j := hle_sh j
            have hle2 : ch1.shiftCount j ≤ chF.shiftCount j :=
              hShLeF ⟨j, Finset.mem_range.mp hj⟩
            omega
          rw [Finset.sum_congr rfl hadd, Finset.sum_add_distrib]
          have hs1 : ∑ j ∈ Finset.range (cfg.P.d + 1), (ch1.shiftCount j - ch.shiftCount j) = 1 := by
            have hmem : i.val ∈ Finset.range (cfg.P.d + 1) := Finset.mem_range.mpr i.isLt
            have hterm : ∀ j ∈ Finset.range (cfg.P.d + 1),
                (ch1.shiftCount j - ch.shiftCount j) = if j = i.val then 1 else 0 := by
              intro j _; rw [hSh1]; dsimp only
              by_cases hji : j = i.val
              · rw [ite_eq_left_iff.mpr fun h => absurd hji h, ite_eq_left_iff.mpr fun h => absurd hji h, hji]
                simp
              · rw [ite_eq_right_iff.mpr fun h => absurd h hji, ite_eq_right_iff.mpr fun h => absurd h hji]
                simp
            rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' _ _ (fun _ => 1),
              ite_eq_left_iff.mpr fun h => absurd hmem h]
          omega
        have hmult :
            2 * (Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) + 2) *
              (1 + (1 + ∑ j ∈ Finset.range (cfg.P.d + 1),
                ((algorithm2_loopWith cfg κ extG e2i g' ℓ' ch1
                  (if i.val < cfg.P.d then 0 else (branD + 1) % cfg.P.k)
                  (fun j => if i < j then 0
                    else if j = i then (if ((if i.val < cfg.P.d then ch.bran i.val else branD) + 1) % cfg.P.k = 0 then passes i + 1 else passes i)
                    else passes j) (lctOps + 2 * (offTree + 1))).1.shiftCount j - ch1.shiftCount j))) =
            2 * (Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) + 2) +
              2 * (Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) + 2) *
                (1 + ∑ j ∈ Finset.range (cfg.P.d + 1),
                  ((algorithm2_loopWith cfg κ extG e2i g' ℓ' ch1
                    (if i.val < cfg.P.d then 0 else (branD + 1) % cfg.P.k)
                    (fun j => if i < j then 0
                      else if j = i then (if ((if i.val < cfg.P.d then ch.bran i.val else branD) + 1) % cfg.P.k = 0 then passes i + 1 else passes i)
                      else passes j) (lctOps + 2 * (offTree + 1))).1.shiftCount j - ch1.shiftCount j)) := by
          ring
        rw [hsum_tot, hmult]
        linarith [hOpsF, hstepOps]
      · rw [dite_eq_right_iff.mpr fun h => absurd h hCap]
        refine ⟨hInv, hBud, rfl, rfl, rfl, rfl, fun _ => le_refl _, hShBound, hBranD, ?_,
          fun _ h => by simp at h⟩
        dsimp only
        simp only [Nat.sub_self, Finset.sum_const_zero, add_zero, mul_one]
        rw [hfc_eq]
        omega
termination_by shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch
decreasing_by
  simpa using shiftRemainingBudget_lt_of_step ch i hCap

/-- Unconditional invariant preservation for `Ordered.algorithm2_loop`. -/
lemma algorithm2_loop_preserves {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    (extG : MGraph) (e2i i2e : ℕ → ℕ) (nf : ℕ) (g' ℓ' : ℕ → ℝ)
    (ch : ChainState cfg.T cfg.P) (branD : ℕ) (passes : Fin (cfg.P.d + 1) → ℕ)
    (lctOps : ℕ) (overflow : ℝ)
    (hInv : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch)
    (hBud : ChainBudgetInvWith cfg.TP cfg.LP cfg.N₀ ch overflow)
    (hShBound : ∀ i : Fin (cfg.P.d + 1),
      (ch.shiftCount i.val : ℝ) ≤ gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch.rebuildCount i.val)
    (hBranD : branD < cfg.P.k)
    (hFresh : FreshInv extG (ch.G 0) e2i i2e nf) (hℓR : LenInRange (max 0 cfg.Ψ) (ch.G 0) ch.ℓ) :
    let res := algorithm2_loop cfg extG e2i g' ℓ' ch branD passes lctOps
    let ch' := res.1
    let branD' := res.2.1
    let lctOps' := res.2.2.2.1
    let optΔ := res.2.2.2.2
    ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch' ∧
    ChainBudgetInvWith cfg.TP cfg.LP cfg.N₀ ch' overflow ∧
    ch'.G 0 = ch.G 0 ∧
    ch'.ℓ = ch.ℓ ∧
    ch'.g = ch.g ∧
    ch'.rebuildCount = ch.rebuildCount ∧
    (∀ i : Fin (cfg.P.d + 1), ch.shiftCount i.val ≤ ch'.shiftCount i.val) ∧
    (∀ i : Fin (cfg.P.d + 1),
      (ch'.shiftCount i.val : ℝ) ≤ gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch'.rebuildCount i.val) ∧
    branD' < cfg.P.k ∧
    lctOps' ≤ lctOps + 2 * (Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) + 2) *
      (1 + ∑ j ∈ Finset.range (cfg.P.d + 1), (ch'.shiftCount j - ch.shiftCount j)) ∧
    (∀ Δ, optΔ = some Δ → extG.IsCirculation Δ) :=
  algorithm2_loopWith_preserves hV (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀)
    extG e2i i2e nf g' ℓ' ch branD passes lctOps overflow hInv hBud hShBound hBranD hFresh hℓR

/-- `Ordered.algorithm2_loopWith` preserves `recUpdates` and `ChainRecBound`. -/
lemma algorithm2_loopWith_rec_props (cfg : Alg2Config) (κ : ℝ)
    (extG : MGraph) (e2i : ℕ → ℕ) (g' ℓ' : ℕ → ℝ)
    (ch : ChainState cfg.T cfg.P) (branD : ℕ) (passes : Fin (cfg.P.d + 1) → ℕ)
    (lctOps : ℕ) :
    let res := algorithm2_loopWith cfg κ extG e2i g' ℓ' ch branD passes lctOps
    res.1.recUpdates = ch.recUpdates ∧
    ∀ {factor : ℝ}, 0 ≤ factor → ChainRecBound cfg.P factor ch → ChainRecBound cfg.P factor res.1 := by
  set fc := algorithm1_findCycle ch
  set offTree := (walkEdges fc.2.1 \ ch.toTreeChain.chainTree.E).card
  set Ψ_g := alg2PsiGame cfg.Ψ cfg.P.M₀
  set Δ_ext := liftEdgeFn extG e2i fc.1
  set lctOps' := lctOps + 2 * (offTree + 1)
  rw [algorithm2_loopWith]
  dsimp only
  by_cases hGood : extG.inner g' Δ_ext / extG.lnorm ℓ' Δ_ext ≤ -(κ * cfg.α)
  · rw [dite_eq_left_iff.mpr fun h => absurd hGood h]
    exact ⟨rfl, fun _ hR => hR⟩
  · rw [dite_eq_right_iff.mpr fun h => absurd h hGood]
    cases hElig : findEligibleLevel cfg.P.d Ψ_g passes with
    | none => exact ⟨rfl, fun _ hR => hR⟩
    | some i =>
      dsimp only
      by_cases hCap : (ch.shiftCount i.val : ℝ) + 1 ≤ gameShiftBound cfg.P Ψ_g ch.rebuildCount i.val
      · rw [dite_eq_left_iff.mpr fun h => absurd hCap h]
        set ch1 := (algorithm1_shift cfg.T cfg.L cfg.P ch i.val).1
        have hShRecEq : ch1.recUpdates = ch.recUpdates := by
          dsimp only [ch1, algorithm1_shift]
          split_ifs <;> rfl
        have ih := algorithm2_loopWith_rec_props cfg κ extG e2i g' ℓ' ch1
          (if i.val < cfg.P.d then 0 else (branD + 1) % cfg.P.k)
          (fun j => if i < j then 0
            else if j = i then (if ((if i.val < cfg.P.d then ch.bran i.val else branD) + 1) % cfg.P.k = 0 then passes i + 1 else passes i)
            else passes j)
          lctOps'
        dsimp only at ih
        refine ⟨ih.1.trans hShRecEq, fun hf hR => ih.2 hf ?_⟩
        exact shift_preserves_chainRecBound cfg.T cfg.L cfg.P hf hR (Nat.lt_succ_iff.mp i.isLt)
      · rw [dite_eq_right_iff.mpr fun h => absurd h hCap]
        exact ⟨rfl, fun _ hR => hR⟩
termination_by shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch
decreasing_by
  simpa using shiftRemainingBudget_lt_of_step ch i hCap

/-- `Ordered.algorithm2_loop` preserves `recUpdates` and `ChainRecBound`. -/
lemma algorithm2_loop_rec_props (cfg : Alg2Config)
    (extG : MGraph) (e2i : ℕ → ℕ) (g' ℓ' : ℕ → ℝ)
    (ch : ChainState cfg.T cfg.P) (branD : ℕ) (passes : Fin (cfg.P.d + 1) → ℕ)
    (lctOps : ℕ) :
    let res := algorithm2_loop cfg extG e2i g' ℓ' ch branD passes lctOps
    res.1.recUpdates = ch.recUpdates ∧
    ∀ {factor : ℝ}, 0 ≤ factor → ChainRecBound cfg.P factor ch → ChainRecBound cfg.P factor res.1 :=
  algorithm2_loopWith_rec_props cfg (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀)
    extG e2i g' ℓ' ch branD passes lctOps

end MinCostFlow.Chain.Ordered
