module

public import MinCostFlow.ExpanderDecomp.Statement
import all MinCostFlow.Expander.ExpanderDecomp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The `(1, 200)` twin of `expanderDecomp_of_cited`

Proves `expanderDecomp_of_used`, the twin of `MinCostFlow.Expander.expanderDecomp_of_cited`
specialized to `(a, b) = (1, 200)` and taking `ExpanderDecompositionUsed` instead of
`Cited.ExpanderDecomposition`. It keeps the same existential output shape
`(K, cr, C₀, K_cost, P, c_w, citedOut, citedCost)` so that downstream consumers using
`decompModel` and `decompModelCost` at `(1, 200)` can switch directly to
`ExpanderDecompositionUsed`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander WordRAM

/-- Twin of `MinCostFlow.Expander.expanderDecomp_of_cited` at `(a, b) = (1, 200)`:
given `ExpanderDecompositionUsed`, there exist constants `K, cr, C₀, K_cost > 0`, a Word-RAM
program `P`, word-size constant `c_w`, and witness functions
`citedOut : ℕ → ℕ → Graph → List ℕ` and `citedCost : ℕ → ℕ → Graph → ℕ` such that:
1. On every valid loopless graph `G` with `thresholdB1 cr ≤ G.m`, `P` halts on
   `G.encode ++ [1, 200, rOf G.m]` with output `citedOut 1 200 G` and cost `citedCost 1 200 G`
   meeting the `ExpanderDecompositionUsed` cost bound.
2. On every valid loopless graph `G`, `label := decompModel citedOut (thresholdB1 cr) 1 200 G`
   is a `(1 / 200, phiB1 K cr 1 200 G.m)`-expander decomposition of `G`, has at most
   `(1 / 200) * G.m` crossing edges, and has operation count
   `decompModelCost citedCost (thresholdB1 cr) 1 200 G` bounded by
   `K_cost * (G.n + (200 / 1)^2 * (G.m + 2) * exp(C₀ * log(G.m + 2)^{2/3} * log(log(G.m + 2) + 2)))`. -/
theorem expanderDecomp_of_used (hDec : ExpanderDecompositionUsed) :
    ∃ (K cr C₀ K_cost : ℝ) (P : WordRAM.Program) (c_w : ℕ)
      (citedOut : ℕ → ℕ → Graph → List ℕ) (citedCost : ℕ → ℕ → Graph → ℕ),
      0 < K ∧ 0 < cr ∧ 0 < C₀ ∧ 0 < K_cost ∧
      (∀ G : Graph, G.IsValid → G.IsLoopless →
        thresholdB1 cr ≤ G.m →
        WordRAM.RunsTo (WordRAM.wordSize c_w (G.encode ++ [1, 200, rOf G.m])) P
          (G.encode ++ [1, 200, rOf G.m]) (fun _ => false) (citedOut 1 200 G) (citedCost 1 200 G) ∧
        (citedCost 1 200 G : ℝ) ≤ K * (G.n + ((G.m : ℝ) + 2) ^ (1 + K / rOf G.m) *
          Real.log ((G.m : ℝ) + 2) ^ (K * (rOf G.m : ℝ) ^ 2) /
            (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) ^ 2)) ∧
      ∀ G : Graph, G.IsValid → G.IsLoopless →
        let label := decompModel citedOut (thresholdB1 cr) 1 200 G
        let cost := decompModelCost citedCost (thresholdB1 cr) 1 200 G
        IsExpanderDecomposition G (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) (phiB1 K cr 1 200 G.m) label ∧
        ((G.edges.filter fun e => decide (label.getD e.1 0 ≠ label.getD e.2 0)).length : ℝ) ≤
          (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) * G.m ∧
        (cost : ℝ) ≤
          K_cost * ((G.n : ℝ) + (((200 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) ^ 2 * ((G.m : ℝ) + 2) *
            Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
              Real.log (Real.log ((G.m : ℝ) + 2) + 2))) := by
  classical
  rcases hDec with ⟨K, cr, P, c, hK, hcr, hspec⟩
  obtain ⟨C₀, hC₀_pos, _, hC₀_mul⟩ := subpoly_exp_bounds hK hcr
  let citedOut : ℕ → ℕ → Graph → List ℕ := fun a b G =>
    if h : a = 1 ∧ b = 200 ∧ G.IsValid ∧ G.IsLoopless ∧ thresholdB1 cr ≤ G.m then
      Classical.choose (hspec G h.2.2.1 h.2.2.2.1 h.2.2.2.2 (fun _ => false))
    else []
  let citedCost : ℕ → ℕ → Graph → ℕ := fun a b G =>
    if h : a = 1 ∧ b = 200 ∧ G.IsValid ∧ G.IsLoopless ∧ thresholdB1 cr ≤ G.m then
      Classical.choose (Classical.choose_spec
        (hspec G h.2.2.1 h.2.2.2.1 h.2.2.2.2 (fun _ => false)))
    else 0
  have hrun_spec : ∀ G (h : G.IsValid ∧ G.IsLoopless ∧ thresholdB1 cr ≤ G.m),
      WordRAM.RunsTo (WordRAM.wordSize c (G.encode ++ [1, 200, rOf G.m])) P
        (G.encode ++ [1, 200, rOf G.m]) (fun _ => false) (citedOut 1 200 G) (citedCost 1 200 G) ∧
      IsExpanderDecomposition G (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ))
        ((((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) /
          (K * Real.log ((G.m : ℝ) + 2) ^ (K * (rOf G.m : ℝ) ^ 2)))
        (citedOut 1 200 G) ∧
      (citedCost 1 200 G : ℝ) ≤ K * (G.n + ((G.m : ℝ) + 2) ^ (1 + K / rOf G.m) *
        Real.log ((G.m : ℝ) + 2) ^ (K * (rOf G.m : ℝ) ^ 2) /
          (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) ^ 2) := by
    intro G h
    have h1200 : (1 : ℕ) = 1 ∧ (200 : ℕ) = 200 ∧ G.IsValid ∧ G.IsLoopless ∧ thresholdB1 cr ≤ G.m :=
      ⟨rfl, rfl, h.1, h.2.1, h.2.2⟩
    have hout : citedOut 1 200 G =
        Classical.choose (hspec G h.1 h.2.1 h.2.2 (fun _ => false)) := by
      dsimp only [citedOut]
      exact dite_eq_left_of_eq_true (eq_true h1200)
    have hcost_eq : citedCost 1 200 G =
        Classical.choose (Classical.choose_spec
          (hspec G h.1 h.2.1 h.2.2 (fun _ => false))) := by
      dsimp only [citedCost]
      exact dite_eq_left_of_eq_true (eq_true h1200)
    rw [hout, hcost_eq]
    exact Classical.choose_spec (Classical.choose_spec
      (hspec G h.1 h.2.1 h.2.2 (fun _ => false)))
  let K_cost : ℝ := max (K + 1) ((thresholdB1 cr : ℝ) + 1)
  have hK_cost : 0 < K_cost := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  refine ⟨K, cr, C₀, K_cost, P, c, citedOut, citedCost, hK, hcr, hC₀_pos, hK_cost, ?_, ?_⟩
  · intro G hGv hGl hm
    have hprop := hrun_spec G ⟨hGv, hGl, hm⟩
    exact ⟨hprop.1, hprop.2.2⟩
  · intro G hGv hGl
    dsimp only [decompModel, decompModelCost]
    have hL_pos : 0 < Real.log ((G.m : ℝ) + 2) :=
      Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) G.m])
    have hexp_ge1 : 1 ≤ Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
        Real.log (Real.log ((G.m : ℝ) + 2) + 2)) := by
      apply Real.one_le_exp
      have : 0 ≤ Real.log (Real.log ((G.m : ℝ) + 2) + 2) := Real.log_nonneg (by linarith)
      positivity
    have hba_ge1 : (1 : ℝ) ≤ ((200 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) := by norm_num
    have hm_le_term : (G.m : ℝ) ≤ (((200 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) ^ 2 * ((G.m : ℝ) + 2) *
        Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
          Real.log (Real.log ((G.m : ℝ) + 2) + 2)) := by
      calc (G.m : ℝ) ≤ (G.m : ℝ) + 2 := by linarith
        _ = 1 * ((G.m : ℝ) + 2) * 1 := by ring
        _ ≤ (((200 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) ^ 2 * ((G.m : ℝ) + 2) *
            Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
              Real.log (Real.log ((G.m : ℝ) + 2) + 2)) := by
            apply mul_le_mul _ hexp_ge1 (by norm_num) (by positivity)
            exact mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    by_cases hm : thresholdB1 cr ≤ G.m
    · have hcond : G.IsValid ∧ G.IsLoopless ∧ 1 ≤ 1 ∧ 1 ≤ 200 ∧ thresholdB1 cr ≤ G.m :=
        ⟨hGv, hGl, le_rfl, by norm_num, hm⟩
      simp only [hcond, and_self, ↓reduceIte]
      have hprop := hrun_spec G ⟨hGv, hGl, hm⟩
      set out := citedOut 1 200 G
      obtain ⟨_, hdecomp, hcost⟩ := hprop
      have hdecomp' : IsExpanderDecomposition G (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ))
          (phiB1 K cr 1 200 G.m) out := by
        refine ⟨hdecomp.1, fun X hX => ?_, hdecomp.2.2⟩
        exact isConductanceExpanderOn_mono (phiB1_le_cor K cr 1 200 G.m) (hdecomp.2.1 X hX)
      have hcut_edges :
          ((G.edges.filter fun e => decide (out.getD e.1 0 ≠ out.getD e.2 0)).length : ℝ) ≤
            (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) * G.m := by
        have hsum := sum_cut_partsOf hGv out
        have hvol := vol_verts_of_isValid hGv
        have hle := hdecomp.2.2
        rw [hvol] at hle
        have hsum_r : (∑ X ∈ partsOf G out, (G.cut X : ℝ)) =
            2 * ((G.edges.filter fun e => decide (out.getD e.1 0 ≠ out.getD e.2 0)).length : ℝ) := by
          exact_mod_cast hsum
        rw [hsum_r] at hle
        push_cast at hle ⊢
        linarith
      refine ⟨hdecomp', hcut_edges, ?_⟩
      have hpow_split : ((G.m : ℝ) + 2) ^ (1 + K / (rOf G.m : ℝ)) =
          ((G.m : ℝ) + 2) * ((G.m : ℝ) + 2) ^ (K / (rOf G.m : ℝ)) := by
        rw [Real.rpow_add (by positivity), Real.rpow_one]
      have hcost1 : ((G.m : ℝ) + 2) ^ (1 + K / (rOf G.m : ℝ)) *
          Real.log ((G.m : ℝ) + 2) ^ (K * (rOf G.m : ℝ) ^ 2) /
            (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) ^ 2 ≤
          (((200 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) ^ 2 * ((G.m : ℝ) + 2) *
            Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
              Real.log (Real.log ((G.m : ℝ) + 2) + 2)) := by
        rw [hpow_split, div_eq_mul_inv]
        have hinv_sq : ((((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) ^ 2)⁻¹ =
            (((200 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) ^ 2 := by
          norm_num
        rw [hinv_sq]
        have hmul := hC₀_mul G.m hm
        calc ((G.m : ℝ) + 2) * ((G.m : ℝ) + 2) ^ (K / (rOf G.m : ℝ)) *
              Real.log ((G.m : ℝ) + 2) ^ (K * (rOf G.m : ℝ) ^ 2) *
              (((200 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) ^ 2
            = (((200 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) ^ 2 * ((G.m : ℝ) + 2) *
                (((G.m : ℝ) + 2) ^ (K / (rOf G.m : ℝ)) *
                  Real.log ((G.m : ℝ) + 2) ^ (K * (rOf G.m : ℝ) ^ 2)) := by ring
          _ ≤ (((200 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) ^ 2 * ((G.m : ℝ) + 2) *
                Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
                  Real.log (Real.log ((G.m : ℝ) + 2) + 2)) := by
                exact mul_le_mul_of_nonneg_left hmul (by positivity)
      have hcited_le : (citedCost 1 200 G : ℝ) ≤
          K * ((G.n : ℝ) + (((200 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) ^ 2 * ((G.m : ℝ) + 2) *
            Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
              Real.log (Real.log ((G.m : ℝ) + 2) + 2))) :=
        le_trans hcost (mul_le_mul_of_nonneg_left (add_le_add le_rfl hcost1) hK.le)
      have hK1_le : K + 1 ≤ K_cost := le_max_left _ _
      have hrhs_nn : 0 ≤ (G.n : ℝ) + (((200 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) ^ 2 * ((G.m : ℝ) + 2) *
          Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
            Real.log (Real.log ((G.m : ℝ) + 2) + 2)) := by positivity
      calc ((citedCost 1 200 G + G.n + G.m : ℕ) : ℝ)
          = (citedCost 1 200 G : ℝ) + ((G.n : ℝ) + (G.m : ℝ)) := by push_cast; ring
        _ ≤ K * ((G.n : ℝ) + (((200 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) ^ 2 * ((G.m : ℝ) + 2) *
              Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
                Real.log (Real.log ((G.m : ℝ) + 2) + 2))) +
            1 * ((G.n : ℝ) + (((200 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) ^ 2 * ((G.m : ℝ) + 2) *
              Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
                Real.log (Real.log ((G.m : ℝ) + 2) + 2))) := by linarith
        _ = (K + 1) * ((G.n : ℝ) + (((200 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) ^ 2 * ((G.m : ℝ) + 2) *
              Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
                Real.log (Real.log ((G.m : ℝ) + 2) + 2))) := by ring
        _ ≤ K_cost * ((G.n : ℝ) + (((200 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) ^ 2 * ((G.m : ℝ) + 2) *
              Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
                Real.log (Real.log ((G.m : ℝ) + 2) + 2))) :=
            mul_le_mul_of_nonneg_right hK1_le hrhs_nn
    · have hcond : ¬ (G.IsValid ∧ G.IsLoopless ∧ 1 ≤ 1 ∧ 1 ≤ 200 ∧ thresholdB1 cr ≤ G.m) := by
        intro h; exact hm h.2.2.2.2
      simp only [hcond, ↓reduceIte]
      have hlen : (compLabels G).length = G.n := compLabels_length G
      have hexp_part : ∀ X ∈ partsOf G (compLabels G),
          G.IsConductanceExpanderOn X (phiB1 K cr 1 200 G.m) := by
        intro X hX
        apply isConductanceExpanderOn_mono (by unfold phiB1; exact min_le_left _ _)
        intro S hSX hSne hSXne
        have hcut1 : (1 : ℝ) ≤ G.cutIn X S := by
          exact_mod_cast cutIn_ge_one_of_part_compLabels hGv hX hSX hSne hSXne
        have hsum_v : G.volIn X S + G.volIn X (X \ S) = 2 * (G.inside X).length :=
          volIn_add_volIn_sdiff G X S hSX
        have hmin_le : min (G.volIn X S) (G.volIn X (X \ S)) ≤ G.m := by
          have hlen_m := inside_length_le_m G X
          omega
        have hm_lt : G.m < thresholdB1 cr := by omega
        have hmin_r : min (G.volIn X S : ℝ) (G.volIn X (X \ S) : ℝ) ≤
            (thresholdB1 cr : ℝ) + 1 := by
          have : (min (G.volIn X S) (G.volIn X (X \ S)) : ℝ) ≤ (thresholdB1 cr : ℝ) + 1 := by
            exact_mod_cast
              (by omega : min (G.volIn X S) (G.volIn X (X \ S)) ≤ thresholdB1 cr + 1)
          exact_mod_cast this
        calc (1 / ((thresholdB1 cr : ℝ) + 1)) * min (G.volIn X S : ℝ) (G.volIn X (X \ S) : ℝ)
            ≤ (1 / ((thresholdB1 cr : ℝ) + 1)) * ((thresholdB1 cr : ℝ) + 1) := by
              apply mul_le_mul_of_nonneg_left hmin_r (by positivity)
          _ = 1 := by field_simp
          _ ≤ G.cutIn X S := hcut1
      have hsum_cut : (∑ X ∈ partsOf G (compLabels G), (G.cut X : ℝ)) ≤
          (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) * (G.vol G.verts : ℝ) := by
        have hzero : ∑ X ∈ partsOf G (compLabels G), (G.cut X : ℝ) = 0 := by
          apply Finset.sum_eq_zero
          intro X hX
          simp [cut_part_compLabels_eq_zero hGv hX]
        rw [hzero]
        positivity
      have hcut_edges : ((G.edges.filter fun e =>
          decide ((compLabels G).getD e.1 0 ≠ (compLabels G).getD e.2 0)).length : ℝ) ≤
          (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) * G.m := by
        have hsum := sum_cut_partsOf hGv (compLabels G)
        have hzero_cut : ∑ X ∈ partsOf G (compLabels G), G.cut X = 0 := by
          apply Finset.sum_eq_zero
          intro X hX
          exact cut_part_compLabels_eq_zero hGv hX
        rw [hzero_cut] at hsum
        have hlen_zero : (G.edges.filter fun e =>
            decide ((compLabels G).getD e.1 0 ≠ (compLabels G).getD e.2 0)).length = 0 := by omega
        rw [hlen_zero]
        simp only [Nat.cast_zero]
        positivity
      refine ⟨⟨hlen, hexp_part, hsum_cut⟩, hcut_edges, ?_⟩
      have hm_lt : G.m ≤ thresholdB1 cr := by omega
      have hnat_le : G.n + G.m + G.n * G.m ≤ (thresholdB1 cr + 1) * G.n + G.m := by
        have hmul : G.n * G.m ≤ G.n * thresholdB1 cr := Nat.mul_le_mul_left G.n hm_lt
        nlinarith
      have hreal_le : ((G.n + G.m + G.n * G.m : ℕ) : ℝ) ≤
          ((thresholdB1 cr : ℝ) + 1) * (G.n : ℝ) + (G.m : ℝ) := by
        exact_mod_cast hnat_le
      have hthr_ge1 : (1 : ℝ) ≤ (thresholdB1 cr : ℝ) + 1 := by
        have := Nat.cast_nonneg (α := ℝ) (thresholdB1 cr)
        linarith
      have hthr_le : (thresholdB1 cr : ℝ) + 1 ≤ K_cost := le_max_right _ _
      calc ((G.n + G.m + G.n * G.m : ℕ) : ℝ)
          ≤ ((thresholdB1 cr : ℝ) + 1) * (G.n : ℝ) + (G.m : ℝ) := hreal_le
        _ ≤ ((thresholdB1 cr : ℝ) + 1) * (G.n : ℝ) +
              ((thresholdB1 cr : ℝ) + 1) * ((((200 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) ^ 2 *
                ((G.m : ℝ) + 2) * Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
                  Real.log (Real.log ((G.m : ℝ) + 2) + 2))) := by
              have : (G.m : ℝ) ≤ ((thresholdB1 cr : ℝ) + 1) * (G.m : ℝ) :=
                le_mul_of_one_le_left (Nat.cast_nonneg _) hthr_ge1
              nlinarith
        _ = ((thresholdB1 cr : ℝ) + 1) * ((G.n : ℝ) + (((200 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) ^ 2 *
              ((G.m : ℝ) + 2) * Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
                Real.log (Real.log ((G.m : ℝ) + 2) + 2))) := by ring
        _ ≤ K_cost * ((G.n : ℝ) + (((200 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) ^ 2 * ((G.m : ℝ) + 2) *
              Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
                Real.log (Real.log ((G.m : ℝ) + 2) + 2))) :=
            mul_le_mul_of_nonneg_right hthr_le (by positivity)

end MinCostFlow.ExpanderDecomp
