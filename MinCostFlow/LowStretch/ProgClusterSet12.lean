module

public import MinCostFlow.LowStretch.ProgClusterSet11

/-!
# The setup of a cluster: the shape of the petal graph

Facts of `PW.Ok` about the shape of the graph that `pgP` builds, with `LO = OFF` and
`HI = OFF + 1`: the ranges end below `MM = 2 nA + s` (`PGA.hi_le`), the non-slot arcs come from
entries below `nA` (`PGA.ordA`, from the sums of `pgPC` with a test function), the ranges with
one extra cell each fit in `2 nA + 2 s` (`PGA.budget`), and the cost of an arc is a function of
its class when every cost is the cost of its class (`PGA.classes`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace PGA

/-- Monotone offsets end below their last value. -/
theorem hi_le {OFF : ℕ} {mem' : ℕ → ℕ} {s MM : ℕ}
    (hmono : ∀ u < s + 1, mem' (OFF + u) ≤ mem' (OFF + 1 + u)) (hlast : mem' (OFF + s) = MM) :
    ∀ v < s + 1, mem' (OFF + 1 + v) ≤ MM ∨ v = s := by
  intro v hv
  by_cases hvs : v = s
  · exact Or.inr hvs
  · left
    have key : ∀ k, v + 1 + k ≤ s → mem' (OFF + (v + 1)) ≤ mem' (OFF + (v + 1 + k)) := by
      intro k
      induction k with
      | zero => intro _; exact le_rfl
      | succ k ih =>
        intro hk
        have h1 := ih (by omega)
        have h2 := hmono (v + 1 + k) (by omega)
        rw [show OFF + 1 + (v + 1 + k) = OFF + (v + 1 + (k + 1)) by omega] at h2
        omega
    have := key (s - (v + 1)) (by omega)
    rw [show v + 1 + (s - (v + 1)) = s by omega, hlast] at this
    rw [show OFF + 1 + v = OFF + (v + 1) by omega]
    exact this

/-- **The non-slot arcs come from entries below `nA`.** -/
theorem ordA {OFF HD ORD nA s : ℕ} {mem' : ℕ → ℕ} {ea eb : ℕ → ℕ}
    (hsum : ∀ u < s, ∀ Fs : ℕ → ℕ → ℕ,
      ∑ k ∈ Finset.Ico (mem' (OFF + u)) (mem' (OFF + 1 + u) - 1),
          Fs (mem' (HD + k)) (mem' (ORD + k) / 2) =
        ∑ j ∈ (Finset.range nA).filter (ea · = u), Fs (eb j) j +
        ∑ j ∈ (Finset.range nA).filter (eb · = u), Fs (ea j) j) :
    ∀ u < s, ∀ k, mem' (OFF + u) ≤ k → k < mem' (OFF + 1 + u) - 1 → mem' (ORD + k) / 2 < nA := by
  intro u hu k hk1 hk2
  have h := hsum u hu (fun _ i => if i < nA then 0 else 1)
  have h0 : ∑ j ∈ (Finset.range nA).filter (ea · = u),
        (fun _ i => if i < nA then 0 else 1) (eb j) j +
      ∑ j ∈ (Finset.range nA).filter (eb · = u), (fun _ i => if i < nA then 0 else 1) (ea j) j
        = 0 := by
    refine Nat.add_eq_zero_iff.mpr ⟨Finset.sum_eq_zero fun j hj => ?_,
      Finset.sum_eq_zero fun j hj => ?_⟩ <;>
      simp only [Finset.mem_filter, Finset.mem_range] at hj <;> simp [hj.1]
  rw [h0, Finset.sum_eq_zero_iff] at h
  have := h k (Finset.mem_Ico.mpr ⟨hk1, hk2⟩)
  by_contra hc
  rw [if_neg hc] at this
  exact absurd this one_ne_zero

/-- The sum of the range sizes telescopes. -/
theorem sum_ranges {OFF : ℕ} {mem' : ℕ → ℕ} {s : ℕ}
    (hmono : ∀ u < s, mem' (OFF + u) ≤ mem' (OFF + 1 + u)) :
    ∑ u ∈ Finset.range s, (mem' (OFF + 1 + u) - mem' (OFF + u) + 1) =
      mem' (OFF + s) - mem' OFF + s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, ih fun u hu => hmono u (by omega)]
    have h1 := hmono s (by omega)
    have h2 : mem' OFF ≤ mem' (OFF + s) := by
      have key : ∀ k ≤ s, mem' OFF ≤ mem' (OFF + k) := by
        intro k
        induction k with
        | zero => intro _; simp
        | succ k ih' =>
          intro hk
          have := hmono k (by omega)
          rw [show OFF + 1 + k = OFF + (k + 1) by omega] at this
          have := ih' (by omega); omega
      exact key s le_rfl
    rw [show OFF + 1 + s = OFF + (s + 1) by omega] at h1 ⊢
    omega

/-- **The budget of the ranges.** -/
theorem budget {OFF : ℕ} {mem' : ℕ → ℕ} {s nA A : ℕ}
    (hmono : ∀ u < s + 1, mem' (OFF + u) ≤ mem' (OFF + 1 + u)) (h0 : mem' OFF = 0)
    (hlast : mem' (OFF + s) = 2 * nA + s) (hA : 2 * nA + 2 * s ≤ A) :
    ∑ u ∈ Finset.range s, (mem' (OFF + 1 + u) - mem' (OFF + u) + 1) ≤ A := by
  rw [sum_ranges fun u hu => hmono u (by omega), hlast, h0]
  omega

/-- **The cost is a function of the class**, when every cost is the cost of its class. -/
theorem classes {CS CL MM lθ : ℕ} {mem' : ℕ → ℕ}
    (h : ∀ k < MM, mem' (CS + k) = cofK lθ (mem' (CL + k))) :
    ∀ k < MM, ∀ k' < MM, mem' (CL + k) = mem' (CL + k') → mem' (CS + k) = mem' (CS + k') :=
  fun k hk k' hk' he => by rw [h k hk, h k' hk', he]

end PGA

end MinCostFlow.LowStretch
