module

public import MinCostFlow.LowStretch.PSums
public import MinCostFlow.LowStretch.PTest

/-!
# The five sums are the sums of region growing

The entries `j < n` of the petal search are the active pairs `pr j` of the cluster, with ends in
the super-vertices `ea j = sv (pu (pr j))` and `eb j = sv (pv (pr j))`. When the settled
super-vertices `ℓ` are exactly those of the petal `W`, the five sums `ESum` of `PSums` give the
count `I`, the sum `C` and the sum `V'` of `PTest` (`esum_link`):
`ESum 0 = I`, `ESum 1 = C + ESum 2` and `ESum 3 = V' + ESum 4`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace Cl

open Classical

variable {G : PG} {P : Par} {c : Cl}

/-- What the link needs: the entries are the active pairs, and the settled list `ℓ` and the
allowed nodes match the petal `W` and the set `Y`. -/
structure ELink (G : PG) (P : Par) (c : Cl) (Y W : Finset ℕ) (pd : PD) (sv : ℕ → ℕ)
    (n : ℕ) (pr ea eb : ℕ → ℕ) (ok : ℕ → Prop) (δ : ℕ → ℕ) (ℓ : List ℕ) : Prop where
  img : (Finset.range n).image pr = c.act G P
  inj : Set.InjOn pr ↑(Finset.range n)
  hea : ∀ j < n, ea j = sv (G.pu (pr j))
  heb : ∀ j < n, eb j = sv (G.pv (pr j))
  okY : ∀ j < n, (ok (ea j) ↔ G.pu (pr j) ∈ Y) ∧ (ok (eb j) ↔ G.pv (pr j) ∈ Y)
  inW : ∀ j < n, (ea j ∈ ℓ ↔ G.pu (pr j) ∈ W) ∧ (eb j ∈ ℓ ↔ G.pv (pr j) ∈ W)
  WY : W ⊆ Y
  ent : ∀ a ∈ W, c.ent G Y pd a = δ (sv a)

variable {Y W : Finset ℕ} {pd : PD} {sv : ℕ → ℕ} {n : ℕ} {pr ea eb : ℕ → ℕ} {ok : ℕ → Prop}
  {δ : ℕ → ℕ} {ℓ : List ℕ}

/-- A sum over the entries is a sum over the active pairs. -/
theorem ELink.sum_eq (hE : c.ELink G P Y W pd sv n pr ea eb ok δ ℓ) (f : ℕ → ℕ)
    (Q : ℕ → Prop) :
    ∑ j ∈ Finset.range n, (if Q (pr j) then f (pr j) else 0) =
      ∑ p ∈ (c.act G P).filter Q, f p := by
  rw [Finset.sum_filter, ← hE.img, Finset.sum_image hE.inj]

theorem efst_of {j : ℕ} (h1 : ea j ∈ ℓ) (h2 : eb j ∉ ℓ) : efst ea eb ℓ j = ea j := by
  unfold efst
  rw [if_pos]
  have := idxOf_lt_of_mem h1
  rw [idxOf_of_not_mem h2]; omega

theorem efst_of' {j : ℕ} (h1 : ea j ∉ ℓ) (h2 : eb j ∈ ℓ) : efst ea eb ℓ j = eb j := by
  unfold efst
  rw [if_neg]
  have := idxOf_lt_of_mem h2
  rw [idxOf_of_not_mem h1]; omega

/-- **The link.** -/
theorem esum_link (hE : c.ELink G P Y W pd sv n pr ea eb ok δ ℓ) (wt : ℕ → ℕ) :
    ESum ea eb (wt ∘ pr) ok δ n ℓ 0 = ((c.act G P).filter (Inside G W ·)).card ∧
    ESum ea eb (wt ∘ pr) ok δ n ℓ 1 =
      ∑ p ∈ (c.act G P).filter (Leaves G Y W ·), wt p + ESum ea eb (wt ∘ pr) ok δ n ℓ 2 ∧
    ESum ea eb (wt ∘ pr) ok δ n ℓ 3 =
      ∑ p ∈ (c.act G P).filter (Leaves G Y W ·), wt p * c.ent G Y pd (inEnd G W p) +
        ESum ea eb (wt ∘ pr) ok δ n ℓ 4 := by
  have hb : ∀ j < n, EBoth ea eb ℓ j ↔ Inside G W (pr j) := fun j hj => by
    unfold EBoth Inside; rw [(hE.inW j hj).1, (hE.inW j hj).2]
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.card_eq_sum_ones, ← hE.sum_eq (fun _ => 1) (Inside G W ·)]
    unfold ESum
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    simp only [eTerm, hb j hj']
  · rw [← hE.sum_eq wt (Leaves G Y W ·)]
    unfold ESum
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    obtain ⟨a1, a2⟩ := hE.inW j hj'
    obtain ⟨o1, o2⟩ := hE.okY j hj'
    have hWY := hE.WY
    simp only [eTerm, EOne, EBoth, Leaves, Function.comp, Finset.mem_sdiff, a1, a2, o1, o2]
    by_cases h1 : G.pu (pr j) ∈ W <;> by_cases h2 : G.pv (pr j) ∈ W <;>
      by_cases h3 : G.pu (pr j) ∈ Y <;> by_cases h4 : G.pv (pr j) ∈ Y <;>
      simp_all [Finset.subset_iff]
  · rw [← hE.sum_eq (fun p => wt p * c.ent G Y pd (inEnd G W p)) (Leaves G Y W ·)]
    unfold ESum
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    obtain ⟨a1, a2⟩ := hE.inW j hj'
    obtain ⟨o1, o2⟩ := hE.okY j hj'
    have hWY := hE.WY
    have hea := hE.hea j hj'
    have heb := hE.heb j hj'
    by_cases h1 : G.pu (pr j) ∈ W <;> by_cases h2 : G.pv (pr j) ∈ W
    · simp only [eTerm, EOne, EBoth, Leaves, Function.comp, Finset.mem_sdiff, a1, a2, o1, o2, h1,
        h2, hWY h1, hWY h2]
      simp
    · have e1 : ea j ∈ ℓ := a1.mpr h1
      have e2 : eb j ∉ ℓ := fun h => h2 (a2.mp h)
      have hf := efst_of e1 e2
      have hin : inEnd G W (pr j) = G.pu (pr j) := by unfold inEnd; rw [if_pos h1]
      rw [show eTerm ea eb (wt ∘ pr) ok δ ℓ j 3 = if EOne ea eb ok ℓ j then
        wt (pr j) * δ (efst ea eb ℓ j) else 0 from rfl,
        show eTerm ea eb (wt ∘ pr) ok δ ℓ j 4 = if EBoth ea eb ℓ j then
        wt (pr j) * δ (efst ea eb ℓ j) else 0 from rfl, hf, hin, hE.ent _ h1, ← hea]
      simp only [EOne, EBoth, Leaves, Finset.mem_sdiff, a1, a2, o1, o2, h1, h2, hWY h1]
      by_cases h4 : G.pv (pr j) ∈ Y <;> simp [h4]
    · have e1 : ea j ∉ ℓ := fun h => h1 (a1.mp h)
      have e2 : eb j ∈ ℓ := a2.mpr h2
      have hf := efst_of' e1 e2
      have hin : inEnd G W (pr j) = G.pv (pr j) := by unfold inEnd; rw [if_neg h1]
      rw [show eTerm ea eb (wt ∘ pr) ok δ ℓ j 3 = if EOne ea eb ok ℓ j then
        wt (pr j) * δ (efst ea eb ℓ j) else 0 from rfl,
        show eTerm ea eb (wt ∘ pr) ok δ ℓ j 4 = if EBoth ea eb ℓ j then
        wt (pr j) * δ (efst ea eb ℓ j) else 0 from rfl, hf, hin, hE.ent _ h2, ← heb]
      simp only [EOne, EBoth, Leaves, Finset.mem_sdiff, a1, a2, o1, o2, h1, h2, hWY h2]
      by_cases h3 : G.pu (pr j) ∈ Y <;> simp [h3]
    · simp only [eTerm, EOne, EBoth, Leaves, Function.comp, Finset.mem_sdiff, a1, a2, o1, o2, h1,
        h2]
      simp

/-- Every vertex of the petal of radius `r` is reached within `r`. -/
theorem ent_le_of_carve {r : ℕ} {a : ℕ} (ha : a ∈ c.carve G Y (pd.withR r)) :
    c.ent G Y (pd.withR r) a ≤ r := by
  simp only [carve, Finset.mem_filter] at ha
  obtain ⟨k, hk, hD⟩ := ha.2
  exact (Nat.sInf_le hD).trans hk

end Cl

end MinCostFlow.LowStretch
