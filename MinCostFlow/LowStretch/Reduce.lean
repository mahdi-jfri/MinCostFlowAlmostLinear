module

public import MinCostFlow.LowStretch.Root
public import MinCostFlow.Statement.Cited.AbrahamNeiman

/-!
# From the weighted graph to the pair graph

Every edge of the weighted graph becomes a pair. Its weight `w` is rounded down to a power of
`2` and multiplied by `2^σ`: `ω = 2^(⌊log₂ w⌋ + σ)`. With `2^σ > 8 B n`, every pair is heavier
than `8 B n`, as the existence proofs need. A walk in the tree has, in the graph, weight at most
`4 / 2^σ` times its tree length `∑ ω/2`, and an edge has weight at least `ω / 2^σ`. So the stretch
of the tree in the graph is at most `4` times its stretch in the pair graph (`stretch_le`).

The constants depend on `n` and `m` only:
* `a = ⌊log₂(n + 2)⌋ + 1` and `L = ⌊log₂(2a + 2)⌋ + 1`, so that `2^(2^L) ≥ (n + 2)²`;
* `B = 4 L (2^L + 3)`, `Q = 512 B n²`, `κ = ⌊m / n²⌋ + 1`, and the volume weight `1` for every pair.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open MinCostFlow.Cited

/-- The pair graph of `G` with shift `σ`. -/
def toPG (G : WGraph) (σ : ℕ) : PG :=
  ⟨G.n, G.edges.map fun e => (e.1, e.2.1, 2 ^ (Nat.log 2 e.2.2 + σ))⟩

namespace toPG

variable {G : WGraph} {σ : ℕ}

@[simp] theorem n_eq : (toPG G σ).n = G.n := rfl

@[simp] theorem m_eq : (toPG G σ).m = G.m := by simp [toPG, PG.m, WGraph.m]

theorem get {p : ℕ} (hp : p < G.m) :
    (toPG G σ).pairs.getD p (0, 0, 0) =
      ((G.edges[p]'hp).1, (G.edges[p]'hp).2.1, 2 ^ (Nat.log 2 (G.edges[p]'hp).2.2 + σ)) := by
  unfold toPG
  simp only
  rw [List.getD_eq_getElem _ _ (by simpa [WGraph.m] using hp), List.getElem_map]
  rfl

theorem pu_eq {p : ℕ} (hp : p < G.m) : (toPG G σ).pu p = (G.edges[p]'hp).1 := by
  unfold PG.pu; rw [get hp]

theorem pv_eq {p : ℕ} (hp : p < G.m) : (toPG G σ).pv p = (G.edges[p]'hp).2.1 := by
  unfold PG.pv; rw [get hp]

theorem pω_eq {p : ℕ} (hp : p < G.m) :
    (toPG G σ).pω p = 2 ^ (Nat.log 2 (G.edges[p]'hp).2.2 + σ) := by
  unfold PG.pω; rw [get hp]

theorem ok (hV : G.graph.IsValid) (hL : G.graph.IsLoopless) (hσ : 1 ≤ σ) : (toPG G σ).Ok := by
  intro p hp
  rw [m_eq] at hp
  have hmem : G.edges[p]'hp ∈ G.edges := List.getElem_mem _
  have hv := hV _ (List.mem_map.mpr ⟨_, hmem, rfl⟩)
  have hl := hL _ (List.mem_map.mpr ⟨_, hmem, rfl⟩)
  simp only at hv hl
  rw [pu_eq hp, pv_eq hp, pω_eq hp]
  refine ⟨hv.1, hv.2, hl, ?_, by positivity⟩
  exact dvd_pow_self 2 (by omega)

/-- `Joins` in the pair graph is the end condition of `IsWalkIn`. -/
theorem joins_iff {j u x : ℕ} (h : j < G.m) :
    (toPG G σ).Joins j u x ↔
      ((G.edges[j]'h).1 = u ∧ (G.edges[j]'h).2.1 = x ∨ (G.edges[j]'h).1 = x ∧ (G.edges[j]'h).2.1 = u) := by
  unfold PG.Joins
  rw [pu_eq h, pv_eq h]
  simp [h]

/-- A walk of the graph is a walk of the pair graph. -/
theorem walk_of {T : List ℕ} (hV : G.graph.IsValid) {u v : ℕ} {es : List ℕ}
    (h : G.IsWalkIn T u v es) (hv : v < G.n) :
    (toPG G σ).IsWalk ↑(Finset.range G.n) {p | p ∈ T} u v es := by
  induction h with
  | nil u => exact .nil (by simpa using hv)
  | @cons u x v j es hj hjm hend rest ih =>
    have hmem : G.edges[j]'hjm ∈ G.edges := List.getElem_mem _
    have he := hV _ (List.mem_map.mpr ⟨_, hmem, rfl⟩)
    simp only [WGraph.graph] at he
    have hu : u < G.n := by rcases hend with ⟨h1, -⟩ | ⟨-, h2⟩ <;> omega
    exact .cons (by simpa using hu) hj ((joins_iff hjm).mpr hend) (ih hv)

/-- A walk of the pair graph is a walk of the graph. -/
theorem walk_to {T : List ℕ} {V : Set ℕ} {u v : ℕ} {es : List ℕ}
    (h : (toPG G σ).IsWalk V {p | p ∈ T} u v es) : G.IsWalkIn T u v es := by
  induction h with
  | nil _ => exact .nil _
  | @cons a b c p ps _ hp hj _ ih =>
    have hpm : p < G.m := by have := hj.1; rwa [m_eq] at this
    exact .cons hp hpm ((joins_iff hpm).mp hj) ih

/-- The graph weight of a tree walk is at most `4 / 2^σ` times its tree length. -/
theorem weight_le {V : Set ℕ} {T : List ℕ} {u v : ℕ} {es : List ℕ}
    (h : (toPG G σ).IsWalk V {p | p ∈ T} u v es) (hσ : 1 ≤ σ) :
    2 ^ σ * G.weightOf es ≤ 4 * PG.wlen (toPG G σ).hl es := by
  induction h with
  | nil _ => simp [WGraph.weightOf]
  | @cons a b c p ps _ hp hj _ ih =>
    have hpm : p < G.m := by have := hj.1; rwa [m_eq] at this
    simp only [WGraph.weightOf, List.map_cons, List.sum_cons, PG.wlen_cons] at ih ⊢
    have hw : (G.edges.getD p (0, 0, 0)).2.2 = (G.edges[p]'hpm).2.2 := by
      rw [List.getD_eq_getElem _ _ hpm]
    rw [hw]
    have hl : (toPG G σ).hl p = 2 ^ (Nat.log 2 (G.edges[p]'hpm).2.2 + σ) / 2 := by
      unfold PG.hl; rw [pω_eq hpm]
    rw [hl]
    have h1 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (G.edges[p]'hpm).2.2
    have h2 : 2 ^ (Nat.log 2 (G.edges[p]'hpm).2.2 + σ) / 2 =
        2 ^ Nat.log 2 (G.edges[p]'hpm).2.2 * 2 ^ (σ - 1) := by
      rw [show Nat.log 2 (G.edges[p]'hpm).2.2 + σ = Nat.log 2 (G.edges[p]'hpm).2.2 + (σ - 1) + 1
        by omega, pow_succ, Nat.mul_div_cancel _ (by norm_num), pow_add]
    rw [h2]
    have h3 : 2 ^ σ = 2 * 2 ^ (σ - 1) := by
      rw [← pow_succ']; congr 1; omega
    have h4 : 2 ^ σ * (G.edges[p]'hpm).2.2 ≤ 4 * (2 ^ Nat.log 2 (G.edges[p]'hpm).2.2 * 2 ^ (σ - 1)) := by
      rw [h3, pow_succ] at *
      have : (G.edges[p]'hpm).2.2 ≤ 2 ^ Nat.log 2 (G.edges[p]'hpm).2.2 * 2 := by omega
      calc 2 * 2 ^ (σ - 1) * (G.edges[p]'hpm).2.2
          ≤ 2 * 2 ^ (σ - 1) * (2 ^ Nat.log 2 (G.edges[p]'hpm).2.2 * 2) :=
            Nat.mul_le_mul_left _ this
        _ = 4 * (2 ^ Nat.log 2 (G.edges[p]'hpm).2.2 * 2 ^ (σ - 1)) := by ring
    rw [Nat.mul_add, Nat.mul_add]
    omega

end toPG

end MinCostFlow.LowStretch
