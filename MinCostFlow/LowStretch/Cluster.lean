module

public import MinCostFlow.LowStretch.WalkShort
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Group.Nat

/-!
# Clusters and their metric

A cluster is a set of vertices `X` with a center `x0`, a target `t`, the set `half` of pairs whose
weight has been halved so far, a threshold `θ`, and a highway `hw` from the target to the
center. Pairs lighter than `θ` are *light*: inside the cluster they have length `0`, as if they
were contracted. Every other pair has its weight, or half of it when it is in `half`.

The program contracts the light pairs for real, so that they cost nothing at this level. In the
mathematics it is simpler to keep them with length `0`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace PG

/-- The pair graph is well formed: ends are vertices, different, and weights are even and
positive. -/
def Ok (G : PG) : Prop :=
  ∀ p < G.m, G.pu p < G.n ∧ G.pv p < G.n ∧ G.pu p ≠ G.pv p ∧ 2 ∣ G.pω p ∧ 0 < G.pω p

end PG

/-- A cluster. -/
structure Cl where
  /-- The vertices. -/
  X : Finset ℕ
  /-- The center. -/
  x0 : ℕ
  /-- The target. -/
  t : ℕ
  /-- The pairs halved so far. -/
  half : Finset ℕ
  /-- Pairs lighter than this have length `0`. -/
  θ : ℕ
  /-- The highway: a walk from the target to the center. -/
  hw : List ℕ

namespace Cl

variable (G : PG) (c : Cl)

/-- The length of pair `p` in the cluster. -/
def len (p : ℕ) : ℕ :=
  if G.pω p < c.θ then 0 else if p ∈ c.half then G.pω p / 2 else G.pω p

/-- The distance in the cluster. -/
noncomputable def d (a b : ℕ) : ℕ := G.dist ↑c.X (c.len G) a b

/-- The radius around the center. -/
noncomputable def Δ : ℕ := c.X.sup fun y => c.d G c.x0 y

/-- The light pairs. -/
def light : Set ℕ := {p | G.pω p < c.θ}

/-- `a` and `b` are joined inside `X` by light pairs. They then lie in the same contracted
vertex. -/
def LConn (a b : ℕ) : Prop := ∃ ps, G.IsWalk ↑c.X (c.light G) a b ps

/-- Pair `p` is active for the constant `Q`: both ends in `X`, not joined by light pairs, and
`ω² ≤ Q · Δ · θ`. The product `Δ · θ` shrinks by a factor `3/4` from a cluster to each child, so
a pair is active in only a few clusters, and these come one after the other. -/
def Active (Q p : ℕ) : Prop :=
  p < G.m ∧ G.pu p ∈ c.X ∧ G.pv p ∈ c.X ∧ ¬ c.LConn G (G.pu p) (G.pv p) ∧
    G.pω p ^ 2 ≤ Q * (c.Δ G * c.θ)

/-- The cluster is connected: every vertex is joined to the center inside `X`. -/
def Conn : Prop := c.x0 ∈ c.X ∧ ∀ y ∈ c.X, G.Reach ↑c.X c.x0 y

variable {G c}

theorem len_le (p : ℕ) : c.len G p ≤ G.pω p := by
  unfold len; split_ifs <;> omega

theorem len_eq_zero_of_light {p : ℕ} (h : G.pω p < c.θ) : c.len G p = 0 := by
  simp [len, h]

/-- A pair that is not light has at least half its weight as length. -/
theorem half_le_len {p : ℕ} (h : c.θ ≤ G.pω p) : G.pω p / 2 ≤ c.len G p := by
  unfold len; split_ifs <;> omega

theorem d_le_Δ {y : ℕ} (hy : y ∈ c.X) : c.d G c.x0 y ≤ c.Δ G :=
  Finset.le_sup (f := fun y => c.d G c.x0 y) hy

theorem exists_eq_Δ (hX : c.X.Nonempty) : ∃ y ∈ c.X, c.d G c.x0 y = c.Δ G := by
  obtain ⟨y, hy, he⟩ := Finset.exists_mem_eq_sup c.X hX fun y => c.d G c.x0 y
  exact ⟨y, hy, he.symm⟩

end Cl

/-- How the lengths of a later cluster `c'` compare with those of `c`: a pair that is light in `c`
gets at most `θ` of `c`, and every other pair gets at most its length in `c`. -/
theorem Cl.len_le_add {G : PG} {c c' : Cl} (hθ : c'.θ ≤ c.θ) (hh : c.half ⊆ c'.half) (p : ℕ) :
    c'.len G p ≤ c.len G p + (if G.pω p < c.θ then c.θ else 0) := by
  unfold Cl.len
  by_cases h1 : G.pω p < c.θ
  · simp only [h1, ite_true, zero_add]
    split_ifs <;> omega
  · have h2 : ¬ G.pω p < c'.θ := by omega
    simp only [h1, h2, ite_false, add_zero]
    by_cases h3 : p ∈ c.half
    · simp [h3, hh h3]
    · split_ifs <;> omega

/-- The basic error bound. Let `c'` be a cluster inside `X` of `c` with smaller threshold and more
halved pairs. A walk in `X'` whose pairs have length at most `f p + θ` in `c'` gives a distance
in `c'` of at most the `f`-length of the walk plus `|X'| θ`. -/
theorem Cl.d_le_of_walk {G : PG} {c' : Cl} {f : ℕ → ℕ} {θ : ℕ} {a b : ℕ} {ps : List ℕ}
    (hw : G.IsWalk ↑c'.X Set.univ a b ps) (hf : ∀ p ∈ ps, c'.len G p ≤ f p + θ) :
    c'.d G a b ≤ PG.wlen f ps + c'.X.card * θ := by
  obtain ⟨qs, hsub, hq, hlen⟩ := hw.exists_short
  have h1 : PG.wlen (c'.len G) qs ≤ PG.wlen f qs + qs.length * θ := by
    have key : ∀ rs : List ℕ, (∀ p ∈ rs, c'.len G p ≤ f p + θ) →
        PG.wlen (c'.len G) rs ≤ PG.wlen f rs + rs.length * θ := by
      intro rs hrs
      induction rs with
      | nil => simp
      | cons p rs ih =>
        simp only [PG.wlen_cons, List.length_cons]
        have := hrs p (List.mem_cons_self ..)
        have := ih fun q hq => hrs q (List.mem_cons_of_mem _ hq)
        rw [Nat.add_mul, one_mul]; omega
    exact key qs fun p hp => hf p (hsub.subset hp)
  have h2 : PG.wlen f qs ≤ PG.wlen f ps := by
    unfold PG.wlen
    exact (hsub.map f).sum_le_sum (fun _ _ => Nat.zero_le _)
  calc c'.d G a b ≤ PG.wlen (c'.len G) qs := PG.dist_le hq
    _ ≤ PG.wlen f qs + qs.length * θ := h1
    _ ≤ PG.wlen f ps + c'.X.card * θ := by
      have : qs.length * θ ≤ c'.X.card * θ := Nat.mul_le_mul_right _ (by omega)
      omega

end MinCostFlow.LowStretch
