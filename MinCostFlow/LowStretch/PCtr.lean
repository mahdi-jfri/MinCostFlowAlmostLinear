module

public import MinCostFlow.LowStretch.Arcs
public import MinCostFlow.LowStretch.DijAbs

/-!
# Petals grown on the super-vertices

The program grows a petal by Dijkstra on the super-vertices of the cluster, not on its vertices.
This file shows that this gives the costs `DR` of the petal metric, under two conditions on the
arc graph `g` of the super-vertices (map `sv`).
* Every arc of `g` comes from an arc of the petal metric between vertices of the two
  super-vertices, with the same cost (`reach_sound`).
* Every arc of the petal metric of cost at most `R` either stays inside a super-vertex or has an
  arc of `g` with the same cost (`reach_complete`).

Moving inside a super-vertex is free: its vertices are joined by light pairs, which have
length `0` and keep the distance to the center (`DR.light`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace Cl

variable {G : PG} {c : Cl}

/-- One light pair keeps the cost. -/
theorem DR.light_step (hc : c.Conn G) {t : ℕ} {hw : List ℕ} {Y : Finset ℕ} (hY : Y ⊆ c.X)
    {p a b k : ℕ} (hdr : c.DR G t hw ↑Y a k) (hp : p ∈ c.light G) (hj : G.Joins p a b)
    (hb : b ∈ Y) : c.DR G t hw ↑Y b k := by
  have ha : a ∈ Y := hdr.mem
  have h0 : c.len G p = 0 := c.len_eq_zero_of_light hp
  have h1 := d_le_add_len hc hj (hY ha) (hY hb)
  have h2 := d_le_add_len hc hj.symm (hY hb) (hY ha)
  exact step_zero hdr hj (by simpa using hb) (by omega)

/-- A light walk inside `X` keeps the cost, when `Y` is closed under light walks. -/
theorem DR.light (hc : c.Conn G) {t : ℕ} {hw : List ℕ} {Y : Finset ℕ} (hY : Y ⊆ c.X)
    (hcl : ∀ a ∈ Y, ∀ b ∈ c.X, c.LConn G a b → b ∈ Y) {a b k : ℕ}
    (hdr : c.DR G t hw ↑Y a k) (hab : c.LConn G a b) : c.DR G t hw ↑Y b k := by
  obtain ⟨ps, hwk⟩ := hab
  induction hwk with
  | nil _ => exact hdr
  | @cons a' b' c' p ps ha hp hj rest ih =>
    have hb' : b' ∈ Y := by
      have hbX : b' ∈ c.X := by
        cases rest with
        | nil h => exact h
        | cons h _ _ _ => exact h
      exact hcl a' hdr.mem b' hbX ⟨[p], .cons ha hp hj (.nil (by exact_mod_cast hbX))⟩
    exact ih (DR.light_step hc hY hdr hp hj hb')

/-- **Soundness.** A walk of `g` from the super-vertex of the target gives the same cost to every
vertex of `Y` in its last super-vertex. -/
theorem reach_sound (hc : c.Conn G) {t : ℕ} {hw : List ℕ} {Y : Finset ℕ} (hY : Y ⊆ c.X)
    (hcl : ∀ a ∈ Y, ∀ b ∈ c.X, c.LConn G a b → b ∈ Y) {sv : ℕ → ℕ}
    (hsv : ∀ a ∈ c.X, ∀ b ∈ c.X, sv a = sv b → c.LConn G a b) {g : AG}
    (hs : ∀ u v k, (u = sv t ∨ g.ok u) → g.Arc u v k →
      ∃ a ∈ Y, ∃ b ∈ Y, sv a = u ∧ sv b = v ∧ c.Arc G t hw a b k)
    (ht : t ∈ Y) {u k : ℕ} (h : g.Reach (sv t) u k) :
    ∀ v ∈ Y, sv v = u → c.DR G t hw ↑Y v k := by
  induction h with
  | refl =>
    intro v hv hsvv
    exact DR.light hc hY hcl (DR.start (by simpa using ht)) (hsv t (hY ht) v (hY hv) hsvv.symm)
  | @step u' v' k' c' hr harc ih =>
    intro v hv hsvv
    have hu' : u' = sv t ∨ g.ok u' := by
      cases hr with
      | refl => exact Or.inl rfl
      | step _ ha => obtain ⟨_, _, _, _, _, hok⟩ := ha; exact Or.inr hok
    obtain ⟨a, ha, b, hb, hsa, hsb, harc'⟩ := hs u' v' c' hu' harc
    have hda := ih a ha hsa
    have hdb : c.DR G t hw ↑Y b (k' + c') := DR.step hda harc' (by simpa using hb)
    exact DR.light hc hY hcl hdb (hsv b (hY hb) v (hY hv) (hsb.trans hsvv.symm))

/-- **Completeness.** A directed walk of cost at most `R` to `v` gives a walk of `g` of at most
the same cost to the super-vertex of `v`. -/
theorem reach_complete {t : ℕ} {hw : List ℕ} {Y : Finset ℕ} {sv : ℕ → ℕ} {g : AG} {R : ℕ}
    (hcomp : ∀ a ∈ Y, ∀ b ∈ Y, ∀ k, c.Arc G t hw a b k → k ≤ R →
      sv a = sv b ∨ g.Arc (sv a) (sv b) k)
    {v k : ℕ} (h : c.DR G t hw ↑Y v k) (hk : k ≤ R) : ∃ k' ≤ k, g.Reach (sv t) (sv v) k' := by
  induction h with
  | start _ => exact ⟨0, le_rfl, AG.Reach.refl⟩
  | @step a b k k' ha harc hb ih =>
    obtain ⟨k1, hk1, hr⟩ := ih (by omega)
    have haY : a ∈ Y := by simpa using ha.mem
    have hbY : b ∈ Y := by simpa using hb
    rcases hcomp a haY b hbY k' harc (by omega) with e | harc'
    · exact ⟨k1, by omega, e ▸ hr⟩
    · exact ⟨k1 + k', by omega, AG.Reach.step hr harc'⟩

end Cl

end MinCostFlow.LowStretch
