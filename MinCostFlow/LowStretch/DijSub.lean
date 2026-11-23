module

public import MinCostFlow.LowStretch.DijAbs

/-!
# Changing arcs that Dijkstra has not looked at

The petal search turns on the highway slot of a node while it runs Dijkstra. This is safe when
the node is not settled yet: the invariant only speaks about the arcs of settled vertices, and
walks only gain arcs. `AG.Sub g g' d` says that `g'` has every arc of `g` and the same arcs at
the settled vertices of `d`. Then the invariant and the parents move from `g` to `g'`
(`AG.Inv.sub`, `AG.ParInv.sub`). Turning on one arc of a vertex that is not settled gives such a
`g'` (`AG.sub_update`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace AG

/-- `g'` has every arc of `g`, and the same arcs as `g` at the settled vertices of `d`. -/
structure Sub (g g' : AG) (d : DS) : Prop where
  arc : ∀ u v c, g.Arc u v c → g'.Arc u v c
  lo : ∀ u, d.sett u → g'.lo u = g.lo u
  hi : ∀ u, d.sett u → g'.hi u = g.hi u
  hd : ∀ u, d.sett u → ∀ k, g.lo u ≤ k → k < g.hi u → g'.hd k = g.hd k
  cs : ∀ u, d.sett u → ∀ k, g.lo u ≤ k → k < g.hi u → g'.cs k = g.cs k
  ok : ∀ v, g'.ok v ↔ g.ok v

theorem Reach.sub {g g' : AG} (h : ∀ u v c, g.Arc u v c → g'.Arc u v c) {s v k : ℕ}
    (hr : g.Reach s v k) : g'.Reach s v k := by
  induction hr with
  | refl => exact .refl
  | step _ ha ih => exact .step ih (h _ _ _ ha)

variable {g g' : AG} {d : DS}

theorem Sub.refl (g : AG) (d : DS) : Sub g g d :=
  ⟨fun _ _ _ h => h, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl,
    fun _ => Iff.rfl⟩

theorem Sub.trans {g'' : AG} (h1 : Sub g g' d) (h2 : Sub g' g'' d) : Sub g g'' d where
  arc u v c h := h2.arc u v c (h1.arc u v c h)
  lo u hu := (h2.lo u hu).trans (h1.lo u hu)
  hi u hu := (h2.hi u hu).trans (h1.hi u hu)
  hd u hu k k1 k2 := by
    rw [← h1.lo u hu] at k1; rw [← h1.hi u hu] at k2
    rw [h2.hd u hu k k1 k2, h1.hd u hu k (by rwa [h1.lo u hu] at k1) (by rwa [h1.hi u hu] at k2)]
  cs u hu k k1 k2 := by
    have k1' := k1; have k2' := k2
    rw [← h1.lo u hu] at k1'; rw [← h1.hi u hu] at k2'
    rw [h2.cs u hu k k1' k2', h1.cs u hu k k1 k2]
  ok v := (h2.ok v).trans (h1.ok v)

/-- Fewer settled vertices. -/
theorem Sub.anti {d' : DS} (h : Sub g g' d) (hs : ∀ u, d'.sett u → d.sett u) : Sub g g' d' :=
  ⟨h.arc, fun u hu => h.lo u (hs u hu), fun u hu => h.hi u (hs u hu),
    fun u hu => h.hd u (hs u hu), fun u hu => h.cs u (hs u hu), h.ok⟩

theorem Inv.sub {s INF cur pos : ℕ} (hs : Sub g g' d) (h : g.Inv s INF cur pos d) :
    g'.Inv s INF cur pos d where
  arcs u hu k h1 h2 hc hok := by
    rw [hs.lo u hu] at h1
    rw [hs.hi u hu] at h2
    rw [hs.hd u hu k h1 h2] at hok ⊢
    rw [hs.cs u hu k h1 h2]
    exact h.arcs u hu k h1 h2 hc ((hs.ok _).mp hok)
  queued := h.queued
  keys := h.keys
  settled_le := h.settled_le
  reach x hx := (h.reach x hx).sub hs.arc
  src := h.src
  L_lt := h.L_lt
  tent_le := h.tent_le
  cur_L := h.cur_L

theorem ParInv.sub {s INF : ℕ} {par parc : ℕ → ℕ} (hs : Sub g g' d)
    (hp : g.ParInv s INF d par parc) : g'.ParInv s INF d par parc := by
  intro x hx hlt
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp x hx hlt
  refine ⟨h1, by rw [hs.lo _ h1]; exact h2, by rw [hs.hi _ h1]; exact h3,
    by rw [hs.hd _ h1 _ h2 h3]; exact h4, (hs.ok x).mpr h5, by rw [hs.cs _ h1 _ h2 h3]; exact h6⟩

/-- **Turning on one arc.** Arc `k0` of `g` has a head that is not allowed, and no settled
vertex owns it. Giving it a new head keeps every arc of `g` and the arcs of the settled
vertices. -/
theorem sub_update (g : AG) (d : DS) {k0 v0 : ℕ} (hk0 : ¬ g.ok (g.hd k0))
    (hns : ∀ u, d.sett u → ¬ (g.lo u ≤ k0 ∧ k0 < g.hi u)) :
    Sub g { g with hd := Function.update g.hd k0 v0 } d where
  arc u v c := by
    rintro ⟨k, k1, k2, rfl, rfl, hok⟩
    have hk : k ≠ k0 := fun e => hk0 (e ▸ hok)
    exact ⟨k, k1, k2, by simp [Function.update_of_ne hk], rfl, hok⟩
  lo _ _ := rfl
  hi _ _ := rfl
  hd u hu k k1 k2 := by
    have hk : k ≠ k0 := fun e => hns u hu ⟨e ▸ k1, e ▸ k2⟩
    simp [Function.update_of_ne hk]
  cs _ _ _ _ _ := rfl
  ok _ := Iff.rfl

end AG

end MinCostFlow.LowStretch
