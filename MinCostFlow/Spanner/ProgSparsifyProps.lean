module

public import MinCostFlow.Spanner.ProgSparsifyW
public import MinCostFlow.Spanner.Theorem81Local

@[expose] public section

/-!
# The Output of the Sparsify Core in Property Form

The `PathDS` contract does not fix which paths it returns, so the embeddings that Tasks 2 and 3
compute need not equal the ones of the model `sparsify`. What we can say is that they have the
properties that Theorem 8.1 asks for. This file shows that the output built from them in the
same way as the model (the kept edges, `J̃`, and the composed embeddings) has these properties.
It feeds the common witness data of `sparsifyCoreOut_commonWD` into `theorem_8_1_core`.

The main result is `sparsifyCoreOut_props`.
-/

namespace MinCostFlow.Spanner

open WordRAM Cited

/-- After the three tasks, the output built from the program's embeddings `embWJ` and `embJW`
has the properties of Theorem 8.1: `J̃` is a valid subgraph of `J` on the kept edges, the three
embeddings are embeddings, and the congestion and length bounds hold with the round counts
`η₁ ≤ eta1Bound` and `η₂ ≤ eta2Bound` of the run. -/
theorem sparsifyCoreOut_props {impl : SpannerToolImpl} {inp : Task1Input}
    {mem mem3 : ℕ → ℕ} {v3 w : ℕ} (hS : SparsifyCoreOut impl inp mem mem3 v3 w)
    (hJ : inp.J.IsValid) (hembJH : IsEmbedding inp.J inp.H' inp.embJH) :
    ∃ (wd : WitnessData) (embWJ embJW : ℕ → Walk) (η₁ η₂ : ℕ),
      η₁ ≤ eta1Bound wd inp.J ∧ η₂ ≤ eta2Bound inp.J ∧
      IsEmbedding wd.W inp.J embWJ ∧ IsEmbedding inp.J wd.W embJW ∧
      let keptEdges := ((List.range wd.W.m).flatMap fun eW => (embWJ eW).edges).dedup
      let Jtilde : Graph := ⟨inp.J.n, keptEdges.map fun j => inp.J.edges.getD j (0, 0)⟩
      let embWJtilde : ℕ → Walk := fun eW => (embWJ eW).mapEdges keptEdges.idxOf
      let embJHtilde := restrictEmb inp.embJH keptEdges
      let embJJtilde := compose wd.W embWJtilde embJW
      keptEdges.Nodup ∧
      (∀ j ∈ keptEdges, j < inp.J.m) ∧
      Jtilde.n = inp.J.n ∧
      Jtilde.m = keptEdges.length ∧
      Jtilde.IsValid ∧
      IsEmbedding wd.W Jtilde embWJtilde ∧
      IsEmbedding Jtilde inp.H' embJHtilde ∧
      IsEmbedding inp.J Jtilde embJJtilde ∧
      vcong inp.J inp.H' (fun _ => 1) (compose Jtilde embJHtilde embJJtilde) ≤
        (((η₁ : ℝ) + 1 / 2) * ((η₂ : ℝ) + 1 / 2)) * wd.τ₁ * wd.τ₂ ∧
      vcong inp.J inp.H' (fun _ => 1) (compose Jtilde embJHtilde embJJtilde) ≤
        (((eta1Bound wd inp.J : ℝ) + 1 / 2) * ((eta2Bound inp.J : ℝ) + 1 / 2)) * wd.τ₁ * wd.τ₂ ∧
      (length inp.J embJJtilde : ℝ) ≤ wd.γ_ExpPath ^ 2 ∧
      (length inp.J (compose Jtilde embJHtilde embJJtilde) : ℝ) ≤
        wd.γ_ExpPath ^ 2 * (length inp.J inp.embJH : ℝ) ∧
      (Jtilde.m : ℝ) ≤ (wd.W.m : ℝ) * wd.γ_ExpPath := by
  obtain ⟨wd₂, wd₃, embWJ, embJW, hW, hwW, hEmb2, hEmb3, -, -, -, hγ, -, -, hτ₂, -, η₁, η₂,
    -, hη1, hη2, hvc2, hlen2, hec3, hlen3, hpos, hWn, hτ₂pos⟩ := sparsifyCoreOut_commonWD hS
  have hEmb3' : IsEmbedding inp.J wd₂.W embJW := hW ▸ hEmb3
  have hec : econg inp.J wd₂.W (fun _ => 1) wd₂.wW embJW ≤ ((η₂ : ℝ) + 1 / 2) * wd₂.τ₂ := by
    refine econg_le_iff.mpr ⟨by positivity, fun eH heH => ?_⟩
    have heH3 : eH < wd₃.W.m := by rw [← hW]; exact heH
    have h := hec3 eH heH3
    unfold econgAt at h ⊢
    rw [hwW eH heH, hτ₂]
    exact h
  have hlen3' : (length inp.J embJW : ℝ) ≤ wd₂.γ_ExpPath := hγ ▸ hlen3
  refine ⟨wd₂, embWJ, embJW, η₁, η₂, hη1, hη2, hEmb2, hEmb3', ?_⟩
  exact theorem_8_1_core inp.H' inp.J wd₂.W wd₂.wW inp.embJH embWJ embJW hWn hJ hembJH hEmb2
    hEmb3' hpos
    (add_nonneg (Nat.cast_nonneg _) (by norm_num))
    (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (by norm_num))
    (add_nonneg (Nat.cast_nonneg _) (by norm_num))
    (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (by norm_num))
    (add_le_add (Nat.cast_le.mpr hη1) le_rfl)
    (add_le_add (Nat.cast_le.mpr hη2) le_rfl)
    hvc2 hec hlen2 hlen3'

end MinCostFlow.Spanner
