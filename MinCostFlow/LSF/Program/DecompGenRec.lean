module

public import MinCostFlow.LSF.Program.DecompGenSpec

/-!
# The bottom-up decomposition with given child lists

A program visits the children of each vertex in the order of its child lists `L u`. `progDecomp`
is the decomposition it builds: the pair (pieces, open bag) of `u` is `goodDecomp_step` applied
to the pairs of the children. The extra argument is a fuel bound, and any fuel at least the size
of the subtree of `u` works (`progDecomp_good`). At the root this gives `GoodDecomp`, and so
`IsTreeDecompSpec` through `isTreeDecompSpec_of_good` (`progDecomp_isTreeDecompSpec`).
-/

@[expose] public section

namespace MinCostFlow.LSF.Program.DecompGen

open MinCostFlow MinCostFlow.LSF

/-- The pieces and the open bag of `u`, built bottom-up with child lists `L` and fuel `k`. -/
noncomputable def progDecomp (ν : ℕ → ℝ) (θ : ℝ) (L : ℕ → List ℕ) :
    ℕ → ℕ → Finset (Finset ℕ) × Finset ℕ
  | 0, u => (∅, {u})
  | k + 1, u =>
    (stepPieces ν θ u (fun c => (progDecomp ν θ L k c).1) (fun c => (progDecomp ν θ L k c).2) (L u),
     stepBag ν θ u (fun c => (progDecomp ν θ L k c).2) (L u))

lemma progDecomp_succ (ν : ℕ → ℝ) (θ : ℝ) (L : ℕ → List ℕ) (k u : ℕ) :
    progDecomp ν θ L (k + 1) u =
      (stepPieces ν θ u (fun c => (progDecomp ν θ L k c).1) (fun c => (progDecomp ν θ L k c).2)
        (L u), stepBag ν θ u (fun c => (progDecomp ν θ L k c).2) (L u)) := rfl

/-- Child lists that list the children of every vertex once. -/
def IsChildLists (T : MGraph) (r : ℕ) (L : ℕ → List ℕ) : Prop :=
  ∀ u ∈ T.V, (L u).Nodup ∧ ∀ c, c ∈ L u ↔ c ∈ childSet T r u

theorem progDecomp_good {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    (ν : ℕ → ℝ) (hν : ∀ v ∈ T.V, 0 ≤ ν v) (θ : ℝ) (hθ : 0 < θ) (hν_le : ∀ v ∈ T.V, ν v ≤ θ)
    {L : ℕ → List ℕ} (hL : IsChildLists T r L) :
    ∀ k u, u ∈ T.V → (subtree T r u).card ≤ k →
      GoodDecomp T r ν θ u (progDecomp ν θ L k u).1 (progDecomp ν θ L k u).2 := by
  classical
  intro k
  induction k with
  | zero =>
    intro u hu hk
    have hmem : u ∈ subtree T r u := mem_subtree_iff.mpr ⟨hu, isAncestor_refl T r u⟩
    have := Finset.card_pos.mpr ⟨u, hmem⟩
    omega
  | succ k ih =>
    intro u hu hk
    rw [progDecomp_succ]
    refine goodDecomp_step hT ν hν θ hθ hν_le hu (L u) (hL u hu).1 (hL u hu).2 _ _ ?_
    intro c hc
    have hcC : c ∈ (subtree T r u \ {u}).filter (fun c => parent T r c = u) := by
      have := ((hL u hu).2 c).mp hc
      rw [childSet] at this
      convert this
    have hsub := subtree_child_subset hT hcC
    have hcV : c ∈ T.V := (mem_subtree_iff.mp (Finset.mem_sdiff.mp
      (Finset.mem_filter.mp hcC).1).1).1
    have hlt : (subtree T r c).card < (subtree T r u).card := by
      have hu_mem : u ∈ subtree T r u := mem_subtree_iff.mpr ⟨hu, isAncestor_refl T r u⟩
      refine Finset.card_lt_card ⟨fun x hx => Finset.sdiff_subset (hsub hx), fun h => ?_⟩
      have := hsub (h hu_mem)
      simp at this
    exact ih c hcV (by omega)

/-- Unit weights and parameter `decompParam G₀ k`: the pair at the root gives `W_T`. -/
theorem progDecomp_isTreeDecompSpec {G₀ T₀ : MGraph} {r : ℕ} (hG₀ : G₀.IsValid)
    (hT₀ : IsRootedTree T₀ r) (hTV : T₀.V = G₀.V) (hV2 : 2 ≤ G₀.V.card)
    (hE : G₀.E.Nonempty) {k : ℝ} (hk : 0 < k) {L : ℕ → List ℕ} (hL : IsChildLists T₀ r L) :
    let ν := decompNu G₀ (fun _ => 1) (decompParam G₀ k)
    let θ := decompTheta G₀ (fun _ => 1) (decompParam G₀ k)
    IsTreeDecompSpec G₀ T₀ k
      (finalDecomp G₀ (fun _ => 1) (decompParam G₀ k) T₀ r
        (progDecomp ν θ L T₀.V.card r).1 (progDecomp ν θ L T₀.V.card r).2) := by
  classical
  intro ν θ
  have hw : ∀ e ∈ G₀.E, (0 : ℝ) ≤ (fun _ => (1 : ℝ)) e := fun _ _ => zero_le_one
  have hθ : 0 < θ := by
    have hm : (0 : ℝ) < (G₀.E.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hE)
    have hp := decompParam_pos (G₀ := G₀) hk
    simp only [θ, decompTheta, Finset.sum_const, nsmul_eq_mul, mul_one]
    positivity
  have hν : ∀ v ∈ T₀.V, 0 ≤ ν v := by
    intro v _
    simp only [ν, decompNu]
    split_ifs
    · exact le_rfl
    · exact vWeight_nonneg hw v
  have hν_le : ∀ v ∈ T₀.V, ν v ≤ θ := by
    intro v hv
    show (if v ∈ decompHeavy G₀ (fun _ => 1) (decompParam G₀ k) then 0
      else vWeight G₀ (fun _ => 1) v) ≤ decompTheta G₀ (fun _ => 1) (decompParam G₀ k)
    split_ifs with hvH
    · exact le_of_lt hθ
    · rw [decompHeavy, Finset.mem_filter] at hvH
      by_contra hlt
      exact hvH ⟨hTV ▸ hv, lt_of_not_ge hlt⟩
  have hroot : (subtree T₀ r r).card ≤ T₀.V.card :=
    Finset.card_le_card (fun _ hx => (mem_subtree_iff.mp hx).1)
  exact isTreeDecompSpec_of_good hG₀ hT₀ hTV hV2 hE hk
    (progDecomp_good hT₀ ν hν θ hθ hν_le hL _ r hT₀.2 hroot)

end MinCostFlow.LSF.Program.DecompGen
