module

public import MinCostFlow.IPM.MinRatioSpec
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The unconditional movement bound for unreported edges

Definition 4.5 (page 14) reports exactly the edges whose accumulated
absolute movement since their last report reaches the threshold.
Telescoping the implicit flow and applying the triangle inequality
therefore bounds its displacement from the last reported coordinate.
This bound holds for rejected target guesses too: it uses only Detect's
unconditional specification and positivity of the stored length.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- The difference of two implicit flow prefixes is exactly the sum of
actual scaled increments on the intervening interval. -/
theorem minRatioFlow_sub_eq_sum (A : MinRatioDataStructure) (D : DynamicInstance)
    (eta : ℕ → ℝ) (op : ℕ → Bool) (s t e : ℕ) (hst : s≤t) :
    minRatioFlow A D eta op t e-minRatioFlow A D eta op s e=
      ∑ j∈Finset.Ioc s t,minRatioIncrement A D eta op j e := by
  have hsets : Finset.Ioc s t=Finset.Ico (s+1) (t+1) := by
    ext j
    simp only [Finset.mem_Ioc,Finset.mem_Ico]
    omega
  rw [hsets,Finset.sum_Ico_eq_sub _ (by omega)]
  rfl

/-- At a valid Detect stage, every unreported edge has weighted flow
displacement below the threshold since its actual `last_e`. This is the
cache-displacement implication used in the adaptation of Chen et al.,
arXiv:2203.00671v2, Lemma 9.1 (page 70), to Definition 4.5. -/
theorem minRatio_unreported_movement_on (A : MinRatioDataStructure) (κ α Ψ eps : ℝ)
    (D : DynamicInstance)
    (eta : ℕ → ℝ) (op : ℕ → Bool) (T t e : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hA : MinRatioSpecOn A κ α Ψ eps D eta op T) (ht : t+1≤T) (hop : op (t+1)=false)
    (he : e∈(D.G (t+1)).E)
    (hne : e∉(A.detect (minRatioState A D eta op t)).1) :
    D.ℓ (t+1) e * |minRatioFlow A D eta op (t+1) e-
      minRatioFlow A D eta op (minRatioLast A D eta op t e) e|<eps := by
  have hdetect := hA.2.2 t ht hop
  have hbelow : D.ℓ (t+1) e *
      ∑ j∈Finset.Ioc (minRatioLast A D eta op t e) (t+1),
        |minRatioIncrement A D eta op j e|<eps := by
    apply lt_of_not_ge
    intro hh
    apply hne
    rw [hdetect]
    exact Finset.mem_filter.mpr ⟨he,hh⟩
  have hlast := minRatioLast_le A D eta op t e
  have hell := (hvalid.2.1 (t+1) ht).2 e he
  rw [minRatioFlow_sub_eq_sum A D eta op _ _ _ (by omega)]
  exact (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hell.le).trans_lt hbelow

/-- At a valid Detect stage, every unreported edge has weighted flow
displacement below the threshold since its actual `last_e`. This is the
cache-displacement implication used in the adaptation of Chen et al.,
arXiv:2203.00671v2, Lemma 9.1 (page 70), to Definition 4.5. -/
theorem minRatio_unreported_movement (A : MinRatioDataStructure) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpec A κ α Ψ eps) (D : DynamicInstance)
    (eta : ℕ → ℝ) (op : ℕ → Bool) (T t e : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (ht : t+1≤T) (hop : op (t+1)=false)
    (he : e∈(D.G (t+1)).E)
    (hne : e∉(A.detect (minRatioState A D eta op t)).1) :
    D.ℓ (t+1) e * |minRatioFlow A D eta op (t+1) e-
      minRatioFlow A D eta op (minRatioLast A D eta op t e) e|<eps :=
  minRatio_unreported_movement_on A κ α Ψ eps D eta op T t e hvalid (hA D eta op T hvalid)
    ht hop he hne

/-- On a fixed graph the same displacement bound applies directly to
Query before and after the last report, by its unconditional semantics. -/
theorem minRatio_unreported_query_displacement_on (A : MinRatioDataStructure) (κ α Ψ eps : ℝ)
    (D : DynamicInstance)
    (eta : ℕ → ℝ) (op : ℕ → Bool) (T t e : ℕ) (G : MGraph)
    (hvalid : MinRatioHistoryValid D op T) (hA : MinRatioSpecOn A κ α Ψ eps D eta op T) (ht : t+1≤T) (hop : op (t+1)=false)
    (hG : ∀ j≤T,D.G j=G) (he : e∈G.E)
    (hne : e∉(A.detect (minRatioState A D eta op t)).1) :
    D.ℓ (t+1) e * |A.query (minRatioState A D eta op (t+1)) e-
      A.query (minRatioState A D eta op (minRatioLast A D eta op t e)) e|<eps := by
  have hlast := minRatioLast_le A D eta op t e
  have hlastT : minRatioLast A D eta op t e≤T := by omega
  have hcurrent : e∈(D.G (t+1)).E := by rw [hG _ ht]; exact he
  have hold : e∈(D.G (minRatioLast A D eta op t e)).E := by rw [hG _ hlastT]; exact he
  have hqueries := hA.1
  rw [hqueries _ ht e hcurrent,hqueries _ hlastT e hold]
  exact minRatio_unreported_movement_on A κ α Ψ eps D eta op T t e hvalid hA ht hop hcurrent hne

/-- On a fixed graph the same displacement bound applies directly to
Query before and after the last report, by its unconditional semantics. -/
theorem minRatio_unreported_query_displacement (A : MinRatioDataStructure) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpec A κ α Ψ eps) (D : DynamicInstance)
    (eta : ℕ → ℝ) (op : ℕ → Bool) (T t e : ℕ) (G : MGraph)
    (hvalid : MinRatioHistoryValid D op T) (ht : t+1≤T) (hop : op (t+1)=false)
    (hG : ∀ j≤T,D.G j=G) (he : e∈G.E)
    (hne : e∉(A.detect (minRatioState A D eta op t)).1) :
    D.ℓ (t+1) e * |A.query (minRatioState A D eta op (t+1)) e-
      A.query (minRatioState A D eta op (minRatioLast A D eta op t e)) e|<eps :=
  minRatio_unreported_query_displacement_on A κ α Ψ eps D eta op T t e G hvalid (hA D eta op T hvalid)
    ht hop hG he hne

end MinCostFlow.IPM.Machine
