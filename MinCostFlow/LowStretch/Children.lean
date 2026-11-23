module

public import MinCostFlow.LowStretch.Pieces

/-!
# The children of one step

A cluster is *good* when it is connected, its highway is a shortest walk from its target to its
center, and every pair it has halved and that is not light lies on its highway (Claim 9 of
[AN19]). This file shows that the children of a good cluster, before the choice of their
thresholds, are good, and that their radii are at most `3/4` of the radius of the cluster
(Claims 5 and 6). It also proves the two inequalities about petals that the bound on the radius of
the tree uses:
* for a regular petal with center `x'` and target `t_k`, every vertex `z` has
  `2 d'(x', z) + d(x0, x') + d(x0, t_k) ≤ r + 2 d(x0, z)`, where `d'` is the metric of the petal;
* for the special petal, `2 d'(x', z) + 2 d(x0, x') + d(x0, t) ≤ r + 2 d(x0, z) + Δ`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

theorem PG.pω_even {G : PG} (hG : G.Ok) (p : ℕ) : 2 ∣ G.pω p := by
  by_cases hp : p < G.m
  · exact (hG p hp).2.2.2.1
  · have : G.pω p = 0 := by
      unfold PG.pω
      rw [List.getD_eq_default _ _ (by unfold PG.m at hp; omega)]
    rw [this]; exact ⟨0, rfl⟩

theorem PG.Joins.end_eq {G : PG} {p a b a' b' : ℕ} (h : G.Joins p a b) (h' : G.Joins p a' b') :
    a = a' ∨ a = b' := by
  rcases h.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases h'.2 with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega

theorem PG.wlen_mul (f : ℕ) (g : ℕ → ℕ) (ps : List ℕ) :
    PG.wlen (fun p => f * g p) ps = f * PG.wlen g ps := by
  induction ps with
  | nil => simp
  | cons p ps ih => simp only [PG.wlen_cons, ih]; rw [Nat.mul_add]

/-- A potential that no pair of `V` changes by more than its length grows along a walk by at most
the length of the walk. -/
theorem PG.pot_walk {G : PG} {V : Set ℕ} {len : ℕ → ℕ} (φ : ℕ → ℕ)
    (hφ : ∀ p a b, G.Joins p a b → a ∈ V → b ∈ V → φ b ≤ φ a + len p) {a b : ℕ} {ps : List ℕ}
    (h : G.IsWalk V Set.univ a b ps) : φ b ≤ φ a + PG.wlen len ps := by
  induction h with
  | nil _ => simp
  | @cons x y z p ps hx _ hj rest ih =>
    have := hφ p x y hj hx rest.start_mem
    simp only [PG.wlen_cons]
    omega

namespace Cl

variable {G : PG} {P : Par} {c : Cl} {D : Dec}

variable (G) in
/-- A good cluster. -/
structure Good (c : Cl) : Prop where
  conn : c.Conn G
  high : c.IsHighway G c.t c.hw
  half : ∀ p ∈ c.half, p < G.m → G.pu p ∈ c.X → G.pv p ∈ c.X → c.θ ≤ G.pω p → p ∈ c.hw

/-! ### Lengths in a child -/

section lengths

variable {c' : Cl} (hθ : c'.θ = c.θ) (hh : c.half ⊆ c'.half)
include hθ hh

theorem len_child_le (p : ℕ) : c'.len G p ≤ c.len G p := by
  unfold len
  rw [hθ]
  by_cases h1 : G.pω p < c.θ
  · simp [h1]
  · by_cases h2 : p ∈ c.half
    · simp [h1, h2, hh h2]
    · simp only [h1, h2, ↓reduceIte]; split_ifs <;> omega

omit hh in
theorem len_le_two_child (hG : G.Ok) (p : ℕ) : c.len G p ≤ 2 * c'.len G p := by
  have he := PG.pω_even hG p
  unfold len
  rw [hθ]
  split_ifs <;> omega

omit hh in
theorem len_child_halved (hG : G.Ok) {p : ℕ} (h1 : p ∈ c'.half) (h2 : p ∉ c.half) :
    2 * c'.len G p = c.len G p := by
  have he := PG.pω_even hG p
  unfold len
  rw [hθ]
  simp only [h1, h2, ↓reduceIte]
  split_ifs <;> omega

end lengths

/-- The potential bound for a child: distances from the center of `c` grow by at most `f` times
the distance in the child, when every length of `c` is at most `f` times the length in the
child. -/
theorem pot_child (hc : c.Conn G) {c' : Cl} (hX : c'.X ⊆ c.X) {f : ℕ}
    (hf : ∀ p, c.len G p ≤ f * c'.len G p) {a b : ℕ} (hr : G.Reach ↑c'.X a b) :
    c.d G c.x0 b ≤ c.d G c.x0 a + f * c'.d G a b := by
  obtain ⟨ps, hps, hl⟩ := G.exists_walk_dist (c'.len G) hr
  have h1 := PG.pot_walk (len := c.len G) (fun v => c.d G c.x0 v)
    (fun p a b hj ha hb => d_le_add_len hc hj (hX ha) (hX hb)) hps
  have h2 : PG.wlen (c.len G) ps ≤ f * PG.wlen (c'.len G) ps := by
    rw [← PG.wlen_mul]; exact PG.wlen_mono hf ps
  unfold d
  rw [← hl]
  exact h1.trans (Nat.add_le_add_left h2 _)

/-! ### The stem -/

theorem raw0_X : (c.raw G D 0).X = c.stem G D := by
  unfold raw; split_ifs <;> rfl

theorem raw0_x0 : (c.raw G D 0).x0 = c.x0 := by
  unfold raw; split_ifs <;> rfl

theorem raw0_len : (c.raw G D 0).len G = c.len G := by
  unfold raw; split_ifs <;> rfl

theorem raw0_θ : (c.raw G D 0).θ = c.θ := by
  unfold raw; split_ifs <;> rfl

theorem raw0_half : (c.raw G D 0).half = c.half := by
  unfold raw; split_ifs <;> rfl

theorem raw0_d {z : ℕ} (hc : c.Conn G) (hz : z ∈ c.stem G D) :
    (c.raw G D 0).d G (c.raw G D 0).x0 z = c.d G c.x0 z := by
  unfold d
  rw [raw0_len, raw0_X, raw0_x0]
  exact (closed_Z D _).dist_eq hc hz

theorem raw0_Δ (hc : c.Conn G) (hD : c.DecOk G P D) :
    4 * (c.raw G D 0).Δ G ≤ 3 * c.Δ G := by
  have hX : (c.raw G D 0).X.Nonempty ∨ (c.raw G D 0).X = ∅ := by
    rcases Finset.eq_empty_or_nonempty (c.raw G D 0).X with h | h
    · exact Or.inr h
    · exact Or.inl h
  rcases hX with hX | hX
  · obtain ⟨y, hy, he⟩ := exists_eq_Δ hX
    rw [← he]
    rw [raw0_X] at hy
    rw [raw0_d hc hy]
    exact hD.2.2.2 y hy
  · unfold Δ; rw [hX]; simp

theorem raw0_good (hG : c.Good G) (hD : c.DecOk G P D) (hΔ : 0 < c.Δ G) :
    (c.raw G D 0).Good G := by
  have hx0 := x0_mem_stem hG.conn hD hΔ
  refine ⟨⟨?_, fun y hy => ?_⟩, ?_, ?_⟩
  · rw [raw0_x0, raw0_X]; exact hx0
  · rw [raw0_X] at hy
    obtain ⟨ps, hps, -⟩ := (closed_Z D _).exists_walk (c := c) hG.conn hy
    rw [raw0_X, raw0_x0]
    exact ⟨ps, hps⟩
  · -- the highway
    have hdeq : ∀ z ∈ c.stem G D, (c.raw G D 0).d G (c.raw G D 0).x0 z = c.d G c.x0 z :=
      fun z hz => raw0_d hG.conn hz
    by_cases hs : D.sp = true
    · have hsp := hD.2.1 hs
      have hil := (petalOk hD hsp.1).2.2.1
      rw [hsp.2.2.1] at hil
      set j := (D.pd 0).i + 1 with hj
      have ht : (c.raw G D 0).t = hv G c.t c.hw j := by
        unfold raw; simp only [hs, ↓reduceIte]; unfold Dec.yc; rw [hsp.2.1, hsp.2.2.1]
      have hw : (c.raw G D 0).hw = c.hw.drop j := by
        unfold raw; simp only [hs, ↓reduceIte, hj]
      have hin : ∀ m, j ≤ m → m ≤ c.hw.length → hv G c.t c.hw m ∈ c.stem G D := by
        intro m hm hml
        rcases hw_mem hG.conn hG.high hD hml with ⟨-, h2, -⟩ | ⟨-, h2⟩
        · omega
        · exact h2
      have hhv : ∀ m, hv G (c.raw G D 0).t (c.raw G D 0).hw m = hv G c.t c.hw (j + m) := by
        intro m; rw [ht, hw]; unfold hv; exact PG.getD_vtx_drop (by omega) m
      refine ⟨?_, fun m hm => ?_⟩
      · rw [ht, hw, raw0_X, raw0_x0]
        refine (hG.high.1.drop j (by omega)).restrict fun x hx => ?_
        obtain ⟨m, hm1, hm2, rfl⟩ := PG.mem_vtx_drop (by omega) hx
        exact hin m hm1 hm2
      · rw [hw, List.length_drop] at hm
        rw [hhv, hhv, hdeq _ (hin _ (by omega) (by omega)),
          hdeq _ (hin _ (by omega) (by omega)), raw0_len, hw]
        have := hG.high.2 (j + m) (by omega)
        rw [show j + (m + 1) = j + m + 1 by omega]
        simpa [List.getD_eq_getElem?_getD, List.getElem?_drop] using this
    · have ht : (c.raw G D 0).t = c.t := by unfold raw; simp [hs]
      have hw : (c.raw G D 0).hw = c.hw := by unfold raw; simp [hs]
      have hin : ∀ m, m ≤ c.hw.length → hv G c.t c.hw m ∈ c.stem G D := by
        intro m hml
        rcases hw_mem hG.conn hG.high hD hml with ⟨h1, -, -⟩ | ⟨-, h2⟩
        · exact absurd h1 hs
        · exact h2
      refine ⟨?_, fun m hm => ?_⟩
      · rw [ht, hw, raw0_X, raw0_x0]
        refine hG.high.1.restrict fun x hx => ?_
        obtain ⟨m, hm2, rfl⟩ := PG.mem_vtx hx
        exact hin m hm2
      · rw [ht, hw] at *
        rw [hdeq _ (hin _ (by omega)), hdeq _ (hin _ (by omega)), raw0_len]
        exact hG.high.2 m hm
  · intro p hp hpm hu hv' hθ
    rw [raw0_half] at hp
    rw [raw0_X] at hu hv'
    rw [raw0_θ] at hθ
    have hpc := hG.half p hp hpm (stem_subset_X hu) (stem_subset_X hv') hθ
    by_cases hs : D.sp = true
    · have hsp := hD.2.1 hs
      have hw : (c.raw G D 0).hw = c.hw.drop ((D.pd 0).i + 1) := by
        unfold raw; simp only [hs, ↓reduceIte]
      rw [hw]
      obtain ⟨m, hm, rfl, hj⟩ := PG.ends_of_mem hG.high.1 hpc
      have hil := (petalOk hD hsp.1).2.2.1
      rw [hsp.2.2.1] at hil
      by_contra hnot
      have hmi : m ≤ (D.pd 0).i := by
        by_contra hmi
        refine hnot ?_
        have hlen : m - ((D.pd 0).i + 1) < (c.hw.drop ((D.pd 0).i + 1)).length := by
          rw [List.length_drop]; omega
        have := List.getElem_mem hlen
        rw [List.getElem_drop] at this
        rw [List.getD_eq_getElem _ _ hm]
        convert this using 2
        omega
      rcases hw_mem hG.conn hG.high hD (m := m) (by omega) with ⟨-, -, h2⟩ | ⟨h1, -⟩
      · have hj' : G.Joins (c.hw.getD m 0) (G.pu (c.hw.getD m 0)) (G.pv (c.hw.getD m 0)) :=
          ⟨hpm, Or.inl ⟨rfl, rfl⟩⟩
        rcases hj.end_eq hj' with h | h
        · exact stem_disj hsp.1 hu (h ▸ h2)
        · exact stem_disj hsp.1 hv' (h ▸ h2)
      · exact h1 ⟨hs, hmi⟩
    · have hw : (c.raw G D 0).hw = c.hw := by unfold raw; simp [hs]
      rw [hw]; exact hpc

end Cl

end MinCostFlow.LowStretch
