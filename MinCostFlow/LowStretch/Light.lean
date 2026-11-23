module

public import MinCostFlow.LowStretch.Inv

/-!
# Light pairs are never cut

A light pair costs nothing in the arc graph (its shifted length is `0`), so a petal that holds one
end of it also holds the other end, if that end is still available. Hence the vertices of a walk
of light pairs are either all in `Z k` or all outside it, for every `k`, and so they all lie in
one piece. Two consequences: a pair whose ends are joined by light pairs is never cut, and a child
that keeps the threshold of its parent sees the same light connections inside its piece.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

variable {G : PG} {P : Par}

namespace Cl

variable {c : Cl} {D : Dec}

/-- A petal that holds one end of a light pair holds the other end, if it is available. -/
theorem carve_light (hc : c.Conn G) {Y : Finset ℕ} (hY : Y ⊆ c.X) {pd : PD} {p a b : ℕ}
    (hj : G.Joins p a b) (hl : G.pω p < c.θ) (ha : a ∈ c.carve G Y pd) (hb : b ∈ Y) :
    b ∈ c.carve G Y pd := by
  obtain ⟨haY, k, hk, hdr⟩ := mem_carve.mp ha
  have h0 : c.len G p = 0 := len_eq_zero_of_light hl
  have h1 := d_le_add_len hc hj.symm (hY hb) (hY haY)
  have hw : c.wbar G p a b = 0 := by unfold wbar; omega
  have := DR.step hdr (Arc.normal (c := c) (t := pd.tj) (hw := pd.hw) hj) (by simpa using hb)
  rw [hw] at this
  simp only [rc, ↓reduceIte, Nat.add_zero] at this
  exact mem_carve.mpr ⟨hb, k, hk, this⟩

theorem carve_light_walk (hc : c.Conn G) {Y : Finset ℕ} (hY : Y ⊆ c.X) {pd : PD} {a b : ℕ}
    {ps : List ℕ} (hw : G.IsWalk ↑Y (c.light G) a b ps) (ha : a ∈ c.carve G Y pd) :
    b ∈ c.carve G Y pd := by
  induction hw with
  | nil _ => exact ha
  | cons _ hp hj rest ih => exact ih (carve_light hc hY hj hp ha rest.start_mem)

/-- The vertices of a light walk are all in `Z k` or all outside it. -/
theorem light_Z (hc : c.Conn G) {a b : ℕ} {ps : List ℕ} (hw : G.IsWalk ↑c.X (c.light G) a b ps)
    (k : ℕ) : (∀ v ∈ G.vtx a ps, v ∈ c.Z G D k) ∨ (∀ v ∈ G.vtx a ps, v ∉ c.Z G D k) := by
  induction k with
  | zero => exact Or.inl fun v hv => hw.vtx_subset v hv
  | succ k ih =>
    rcases ih with h | h
    · have hwk : G.IsWalk ↑(c.Z G D k) (c.light G) a b ps := hw.restrict fun v hv => h v hv
      have hYk := Z_subset_X (c := c) (G := G) D k
      -- membership in petal `k` is the same for all vertices of the walk
      have hall : ∀ v ∈ G.vtx a ps, (v ∈ c.W G D k ↔ a ∈ c.W G D k) := by
        intro v hv
        obtain ⟨j, hj, rfl⟩ := PG.mem_vtx hv
        have hpre := (hwk.take j hj)
        constructor
        · intro hvW; exact carve_light_walk hc hYk hpre.reverse hvW
        · intro haW; exact carve_light_walk hc hYk hpre haW
      by_cases ha : a ∈ c.W G D k
      · right
        intro v hv hvZ
        rw [Z_succ] at hvZ
        exact (Finset.mem_sdiff.mp hvZ).2 ((hall v hv).mpr ha)
      · left
        intro v hv
        rw [Z_succ]
        exact Finset.mem_sdiff.mpr ⟨h v hv, fun hvW => ha ((hall v hv).mp hvW)⟩
    · right
      intro v hv hvZ
      exact h v hv (Z_antitone D (Nat.le_succ k) hvZ)

theorem mem_W_iff {k v : ℕ} : v ∈ c.W G D k ↔ v ∈ c.Z G D k ∧ v ∉ c.Z G D (k + 1) := by
  rw [Z_succ]
  constructor
  · intro h; exact ⟨W_subset D k h, fun h' => (Finset.mem_sdiff.mp h').2 h⟩
  · rintro ⟨h1, h2⟩; by_contra h3; exact h2 (Finset.mem_sdiff.mpr ⟨h1, h3⟩)

/-- The vertices of a light walk all lie in one piece. -/
theorem light_piece (hc : c.Conn G) {a b : ℕ} {ps : List ℕ}
    (hw : G.IsWalk ↑c.X (c.light G) a b ps) (j : ℕ) :
    (∀ v ∈ G.vtx a ps, v ∈ (c.raw G D j).X) ∨ (∀ v ∈ G.vtx a ps, v ∉ (c.raw G D j).X) := by
  cases j with
  | zero =>
    rw [raw0_X]
    exact light_Z (D := D) hc hw _
  | succ k =>
    rw [rawP_X]
    rcases light_Z (D := D) hc hw k with h1 | h1
    · rcases light_Z (D := D) hc hw (k + 1) with h2 | h2
      · right; intro v hv hW; exact (mem_W_iff.mp hW).2 (h2 v hv)
      · left; intro v hv; exact mem_W_iff.mpr ⟨h1 v hv, h2 v hv⟩
    · right; intro v hv hW; exact h1 v hv (mem_W_iff.mp hW).1

theorem start_mem_vtx (a : ℕ) (ps : List ℕ) : a ∈ G.vtx a ps := by
  cases ps <;> simp [PG.vtx]

theorem end_mem_vtx {a b : ℕ} {V Pr : Set ℕ} {ps : List ℕ} (hw : G.IsWalk V Pr a b ps) :
    b ∈ G.vtx a ps := by
  have h := hw.getD_length
  rw [← h, List.getD_eq_getElem _ _ (by rw [PG.IsWalk.length_vtx]; omega)]
  exact List.getElem_mem _

/-- Two vertices joined by light pairs lie in the same pieces. -/
theorem lconn_piece (hc : c.Conn G) {a b : ℕ} (h : c.LConn G a b) (j : ℕ) :
    a ∈ (c.raw G D j).X ↔ b ∈ (c.raw G D j).X := by
  obtain ⟨ps, hw⟩ := h
  rcases light_piece (D := D) hc hw j with h1 | h1
  · exact ⟨fun _ => h1 b (end_mem_vtx hw), fun _ => h1 a (start_mem_vtx a ps)⟩
  · exact ⟨fun ha => absurd ha (h1 a (start_mem_vtx a ps)),
      fun hb => absurd hb (h1 b (end_mem_vtx hw))⟩

/-- Inside a piece, light connections of the cluster are light connections of the piece. -/
theorem lconn_child (hc : c.Conn G) {a b : ℕ} (h : c.LConn G a b) {j : ℕ}
    (ha : a ∈ (c.raw G D j).X) : ∃ ps, G.IsWalk ↑(c.raw G D j).X (c.light G) a b ps := by
  obtain ⟨ps, hw⟩ := h
  rcases light_piece (D := D) hc hw j with h1 | h1
  · exact ⟨ps, hw.restrict h1⟩
  · exact absurd ha (h1 a (start_mem_vtx a ps))

end Cl

end MinCostFlow.LowStretch
