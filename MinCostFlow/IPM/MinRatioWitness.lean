module

public import MinCostFlow.IPM.MinRatioSpec
import Mathlib.Tactic.Linarith

/-!
# A hidden witness supplies a permitted min-ratio circulation

Definition 4.4 (page 14) bounds `|ℓ c|` by the positive vector `w` and
`⟨g,c⟩ / ‖w‖₁` by `-α`. Consequently the same circulation has ratio at
most `-α` with respect to its actual length, and at most `-κα` for
`0 < κ ≤ 1`. This proves that the circulation requirement of Definition
4.5 can be met without assuming its conclusion as a hidden-stability field.
-/

noncomputable section
public section
namespace MinCostFlow.IPM

/-- A hidden stable prefix supplies a circulation of the ratio required
by Definition 4.5 (page 14). -/
theorem hiddenStable_has_direction (D : DynamicInstance) (T : ℕ) (α Ψ κ : ℝ)
    (ha : 0 < α) (hk : κ ≤ 1) (h : D.HiddenStable T α Ψ) :
    ∃ d : ℕ → ℝ, (D.G T).IsCirculation d ∧
      (D.G T).inner (D.g T) d / (D.G T).lnorm (D.ℓ T) d ≤ -κ*α := by
  obtain ⟨c, w, hcw⟩ := h
  have ht := hcw T le_rfl
  let G := D.G T
  have hw0 : 0 ≤ G.norm1 (w T) := Finset.sum_nonneg fun e _ => abs_nonneg _
  have hwpos : 0 < G.norm1 (w T) := by
    by_contra hn
    have hz := le_antisymm (not_lt.mp hn) hw0
    have hh := ht.2.2.1
    change G.inner (D.g T) (c T) / G.norm1 (w T) ≤ -α at hh
    rw [hz, div_zero] at hh
    linarith only [hh, ha]
  have hdot := (div_le_iff₀ hwpos).mp ht.2.2.1
  have hdotneg : G.inner (D.g T) (c T) < 0 :=
    lt_of_le_of_lt hdot (mul_neg_of_neg_of_pos (neg_neg_of_pos ha) hwpos)
  have hlpos : ∀ e ∈ G.E, 0 < D.ℓ T e := fun e he => (ht.2.2.2.2 e he).2.2.1
  have hlen0 : 0 ≤ G.lnorm (D.ℓ T) (c T) :=
    Finset.sum_nonneg fun e he => mul_nonneg (hlpos e he).le (abs_nonneg _)
  have hlenpos : 0 < G.lnorm (D.ℓ T) (c T) := by
    by_contra hn
    have hz := le_antisymm (not_lt.mp hn) hlen0
    have hc0 : ∀ e ∈ G.E, c T e = 0 := by
      intro e he
      have hsingle : D.ℓ T e*|c T e| ≤ G.lnorm (D.ℓ T) (c T) :=
        Finset.single_le_sum (fun j hj => mul_nonneg (hlpos j hj).le (abs_nonneg _)) he
      rw [hz] at hsingle
      have hp : D.ℓ T e*|c T e| = 0 := le_antisymm hsingle
        (mul_nonneg (hlpos e he).le (abs_nonneg _))
      exact abs_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left (hlpos e he).ne')
    have hd0 : G.inner (D.g T) (c T) = 0 :=
      Finset.sum_eq_zero (fun e he => by rw [hc0 e he, mul_zero])
    rw [hd0] at hdotneg
    exact (lt_irrefl 0) hdotneg
  have hlenle : G.lnorm (D.ℓ T) (c T) ≤ G.norm1 (w T) := by
    apply Finset.sum_le_sum
    intro e he
    have hp := ht.2.1.2 e he
    rw [abs_mul, abs_of_pos (hlpos e he)] at hp
    exact hp.trans (le_abs_self _)
  refine ⟨c T, ht.1, (div_le_iff₀ hlenpos).mpr ?_⟩
  have hh := mul_le_mul_of_nonpos_left hlenle (neg_nonpos.mpr ha.le)
  have hkα : -α ≤ -κ*α := by nlinarith only [hk, ha.le]
  exact (hdot.trans hh).trans (mul_le_mul_of_nonneg_right hkα hlenpos.le)

/-- A mathematical circulation selector. It chooses a qualifying
circulation when one exists and otherwise returns zero. Its input is
only the current graph, gradient, and lengths. -/
@[expose] def chooseMinRatioDirection (G : MGraph) (g ℓ : ℕ → ℝ) (κ α : ℝ) : ℕ → ℝ := by
  classical
  exact if h : ∃ d : ℕ → ℝ, G.IsCirculation d ∧ G.inner g d / G.lnorm ℓ d ≤ -κ*α then
    Classical.choose h else fun _ => 0

/-- The selector always returns a circulation, including on prefixes
without a hidden stability witness. -/
theorem chooseMinRatioDirection_circulation (G : MGraph) (g ℓ : ℕ → ℝ) (κ α : ℝ) :
    G.IsCirculation (chooseMinRatioDirection G g ℓ κ α) := by
  classical
  unfold chooseMinRatioDirection
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · intro v _
    simp only [MGraph.demand, mul_zero, Finset.sum_const_zero]

/-- On a hidden stable prefix, the mathematical selector satisfies the
ratio bound of Definition 4.5. -/
theorem chooseMinRatioDirection_quality (D : DynamicInstance) (T : ℕ) (α Ψ κ : ℝ)
    (ha : 0 < α) (hk : κ ≤ 1) (h : D.HiddenStable T α Ψ) :
    (D.G T).inner (D.g T) (chooseMinRatioDirection (D.G T) (D.g T) (D.ℓ T) κ α) /
      (D.G T).lnorm (D.ℓ T) (chooseMinRatioDirection (D.G T) (D.g T) (D.ℓ T) κ α) ≤ -κ*α := by
  classical
  have hex := hiddenStable_has_direction D T α Ψ κ ha hk h
  unfold chooseMinRatioDirection
  rw [dite_eq_left hex]
  exact (Classical.choose_spec hex).2

end MinCostFlow.IPM
