module

public import MinCostFlow.LowStretch.Tree
public import Mathlib.Tactic.Ring

/-!
# The radius of the tree

In the tree a pair `p` has length `ω_p / 2`. This is at most its length in any cluster where it
is not light, so the tree is never longer than the metric of a cluster, except on light pairs.
We prove, for every cluster of a run with `A = 4B + 4`:
* every vertex `y` is joined to the center by a walk in the tree of length at most
  `2 d(x0, y) + A · |X| · θ` (Lemma 13 of [AN19]);
* the target is joined to the center by a walk in the tree of length at most
  `d(x0, t) + A · |X| · θ` (Claim 12).

The term `A · |X| · θ` pays for the reset children. A reset child has a small radius
(`Δ < B · |X| · θ`), and its new metric is at most twice the old one plus `|X| · θ`. The errors of
the pieces along a path to the center add up to at most `A · θ` times the size of the cluster,
because the pieces are disjoint.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

variable {G : PG} {P : Par}

/-- The constant of the radius bound. -/
def Par.A (P : Par) : ℕ := 4 * P.B + 4

/-- The length of a pair in the tree. -/
def PG.hl (G : PG) (p : ℕ) : ℕ := G.pω p / 2

/-- `TW T a b l`: a walk from `a` to `b` along pairs of `T`, of tree length at most `l`. -/
def TW (G : PG) (T : List ℕ) (a b l : ℕ) : Prop :=
  ∃ ps, G.IsWalk Set.univ {p | p ∈ T} a b ps ∧ PG.wlen G.hl ps ≤ l

namespace TW

theorem refl (T : List ℕ) (a l : ℕ) : TW G T a a l := ⟨[], .nil (Set.mem_univ a), by simp⟩

theorem mono {T T' : List ℕ} {a b l l' : ℕ} (h : TW G T a b l) (hT : ∀ p ∈ T, p ∈ T')
    (hl : l ≤ l') : TW G T' a b l' :=
  let ⟨ps, hps, hle⟩ := h
  ⟨ps, hps.mono le_rfl fun p hp => hT p hp, hle.trans hl⟩

theorem trans {T : List ℕ} {a b c l l' : ℕ} (h₁ : TW G T a b l) (h₂ : TW G T b c l') :
    TW G T a c (l + l') :=
  let ⟨ps, hps, h1⟩ := h₁
  let ⟨qs, hqs, h2⟩ := h₂
  ⟨ps ++ qs, hps.append hqs, by rw [PG.wlen_append]; omega⟩

theorem pair {T : List ℕ} {p a b : ℕ} (hp : p ∈ T) (hj : G.Joins p a b) :
    TW G T a b (G.hl p) :=
  ⟨[p], .cons (Set.mem_univ a) hp hj (.nil (Set.mem_univ b)), by simp⟩

end TW

/-- The two radius bounds of a cluster with tree `T`. -/
def RadOk (G : PG) (P : Par) (c : Cl) (T : List ℕ) : Prop :=
  (∀ y ∈ c.X, TW G T c.x0 y (2 * c.d G c.x0 y + P.A * c.X.card * c.θ)) ∧
    TW G T c.x0 c.t (c.d G c.x0 c.t + P.A * c.X.card * c.θ)

/-- A reset child, seen from the cluster before the reset: the bounds hold in the old metric. -/
theorem Next.radOk (hGo : G.Ok) {r c' : Cl} {T : List ℕ} (hn : Next G P r c') (hr : r.Good G)
    (h : RadOk G P c' T) : RadOk G P r T := by
  rcases hn with ⟨rfl, -⟩ | ⟨hlt, hX, hx, ht, -, -, hθ4, -, -, -⟩
  · exact h
  have key : ∀ y ∈ r.X, c'.d G c'.x0 y ≤ 2 * r.d G r.x0 y + r.X.card * r.θ := by
    intro y hy
    obtain ⟨ps, hps, hl⟩ := G.exists_walk_dist (r.len G) (hr.conn.2 y hy)
    have := Cl.d_le_of_walk (c' := c') (f := fun p => 2 * r.len G p) (θ := r.θ)
      (a := c'.x0) (b := y) (ps := ps) (by rw [hX, hx]; exact hps) (fun p _ => by
        have h1 := Cl.len_le (c := c') (G := G) p
        have he := PG.pω_even hGo p
        by_cases hl : G.pω p < r.θ
        · omega
        · have := Cl.half_le_len (c := r) (G := G) (p := p) (by omega)
          omega)
    rw [PG.wlen_mul, hl, hX] at this
    exact this
  have hsmall : ∀ y ∈ r.X, r.d G r.x0 y < P.B * r.X.card * r.θ :=
    fun y hy => lt_of_le_of_lt (Cl.d_le_Δ hy) hlt
  set a := r.X.card with ha
  have hY : 4 * (P.A * a * c'.θ) ≤ P.A * a * r.θ := by
    have := Nat.mul_le_mul_left (P.A * a) hθ4
    have e : P.A * a * (4 * c'.θ) = 4 * (P.A * a * c'.θ) := by ring
    omega
  have hA : P.A * a * r.θ = 4 * (P.B * a * r.θ) + 4 * (a * r.θ) := by unfold Par.A; ring
  have hXc : c'.X.card = a := by rw [hX]
  have h1 := h.1
  rw [hx, hX, ← ha] at h1
  have hpart : ∀ y ∈ r.X, TW G T r.x0 y (2 * r.d G r.x0 y + P.A * a * r.θ) := by
    intro y hy
    refine (h1 y hy).mono (fun _ h => h) ?_
    have hk := key y hy
    rw [hx] at hk
    have := hsmall y hy
    omega
  refine ⟨hpart, ?_⟩
  have htX : r.t ∈ r.X := by
    have := hr.high.hv_mem (i := 0) (Nat.zero_le _)
    rwa [Cl.hv_zero] at this
  refine (h1 r.t htX).mono (fun _ h => h) ?_
  have hk := key r.t htX
  rw [hx] at hk
  have := hsmall r.t htX
  rw [← ha]
  omega

end MinCostFlow.LowStretch
