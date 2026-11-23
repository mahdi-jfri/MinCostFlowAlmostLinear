module

public import MinCostFlow.LowStretch.PCtr
public import MinCostFlow.LowStretch.Grow

/-!
# What a run of the petal search knows about the petal

The petal search runs Dijkstra on an arc graph `g` of super-vertices (map `sv`) from the
super-vertex of the target. `PLink` collects what the arc graph must satisfy: its arcs come from
arcs of the petal metric (`snd`), and every arc of the petal metric of cost at most `Rm` that
leaves a super-vertex is an arc of `g` (`cmp`).

Then, while the least key of the queue is `K`, for every radius `r` with `L ≤ r < K` (`L` the key
of the last settled node) the petal of radius `r` is the set of vertices of `Y` whose
super-vertex is settled (`PLink.carve_eq`). The cost of reaching a settled vertex is its
tentative cost (`PLink.ent_eq`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace Cl

variable {G : PG} {c : Cl}

/-- The arc graph `g` of super-vertices represents the petal metric from `t` inside `Y`, for
costs up to `Rm`. -/
structure PLink (G : PG) (c : Cl) (t : ℕ) (hw : List ℕ) (Y : Finset ℕ) (sv : ℕ → ℕ) (g : AG)
    (Rm : ℕ) : Prop where
  conn : c.Conn G
  hY : Y ⊆ c.X
  ht : t ∈ Y
  hcl : ∀ a ∈ Y, ∀ b ∈ c.X, c.LConn G a b → b ∈ Y
  hsv : ∀ a ∈ c.X, ∀ b ∈ c.X, sv a = sv b → c.LConn G a b
  snd : ∀ u v k, (u = sv t ∨ g.ok u) → g.Arc u v k →
    ∃ a ∈ Y, ∃ b ∈ Y, sv a = u ∧ sv b = v ∧ c.Arc G t hw a b k
  cmp : ∀ a ∈ Y, ∀ b ∈ Y, ∀ k, c.Arc G t hw a b k → k ≤ Rm → sv a = sv b ∨ g.Arc (sv a) (sv b) k

variable {t : ℕ} {hw : List ℕ} {Y : Finset ℕ} {sv : ℕ → ℕ} {g : AG} {Rm : ℕ}
  {INF cur pos K : ℕ} {d : DS}

/-- A settled super-vertex: every vertex of `Y` in it is reached at its tentative cost. -/
theorem PLink.dr_sett (hL : PLink G c t hw Y sv g Rm) (hinv : g.Inv (sv t) INF cur pos d)
    {a : ℕ} (ha : a ∈ Y) (hs : d.sett (sv a)) : c.DR G t hw ↑Y a (d.tent (sv a)) :=
  reach_sound hL.conn hL.hY hL.hcl hL.hsv hL.snd hL.ht (hinv.reach_sett hs) a ha rfl

/-- A walk of the petal metric of cost at most `Rm` to a vertex whose super-vertex is not settled
costs at least `K`; to one whose super-vertex is settled, at least its tentative cost. -/
theorem PLink.path (hL : PLink G c t hw Y sv g Rm) (hinv : g.Inv (sv t) INF cur pos d)
    (hdone : d.sett cur → g.hi cur ≤ pos) (hK : K ≤ INF) (hLK : d.L ≤ K)
    (hQ : ∀ e ∈ d.Q, K ≤ e.1) {a k : ℕ} (hD : c.DR G t hw ↑Y a k) (hk : k ≤ Rm) :
    (d.sett (sv a) → d.tent (sv a) ≤ k) ∧ (¬ d.sett (sv a) → K ≤ k) := by
  obtain ⟨k', hk', hr⟩ := reach_complete (g := g) (sv := sv) hL.cmp hD hk
  have := hinv.path hdone hK hLK hQ hr
  exact ⟨fun h => (this.1 h).trans hk', fun h => (this.2 h).trans hk'⟩

/-- **The petal is the settled part.** -/
theorem PLink.petal_iff (hL : PLink G c t hw Y sv g Rm) (hinv : g.Inv (sv t) INF cur pos d)
    (hdone : d.sett cur → g.hi cur ≤ pos) (hK : K ≤ INF) (hLK : d.L ≤ K)
    (hQ : ∀ e ∈ d.Q, K ≤ e.1) {r : ℕ} (hr : r < K) (hdr : d.L ≤ r) (hrR : r ≤ Rm) {a : ℕ}
    (ha : a ∈ Y) : a ∈ c.Petal G t hw ↑Y r ↔ d.sett (sv a) := by
  constructor
  · rintro ⟨k, hk, hD⟩
    by_contra hns
    have := (hL.path hinv hdone hK hLK hQ hD (hk.trans hrR)).2 hns
    omega
  · intro hs
    exact ⟨_, (hinv.settled_le _ hs).trans hdr, hL.dr_sett hinv ha hs⟩

open Classical in
/-- The carved petal of radius `r`, for `L ≤ r < K`. -/
theorem PLink.carve_eq (hL : PLink G c t hw Y sv g Rm) (hinv : g.Inv (sv t) INF cur pos d)
    (hdone : d.sett cur → g.hi cur ≤ pos) (hK : K ≤ INF) (hLK : d.L ≤ K)
    (hQ : ∀ e ∈ d.Q, K ≤ e.1) {pd : PD} (hpt : pd.tj = t) (hph : pd.hw = hw) {r : ℕ}
    (hr : r < K) (hdr : d.L ≤ r) (hrR : r ≤ Rm) :
    c.carve G Y (pd.withR r) = Y.filter (fun a => d.sett (sv a)) := by
  ext a
  simp only [carve, Finset.mem_filter, PD.withR, hpt, hph]
  constructor
  · rintro ⟨ha, hp⟩
    exact ⟨ha, (hL.petal_iff hinv hdone hK hLK hQ hr hdr hrR ha).mp hp⟩
  · rintro ⟨ha, hs⟩
    exact ⟨ha, (hL.petal_iff hinv hdone hK hLK hQ hr hdr hrR ha).mpr hs⟩

/-- The petal is the same for all radii in `[L, K - 1]`. -/
theorem PLink.carve_same (hL : PLink G c t hw Y sv g Rm) (hinv : g.Inv (sv t) INF cur pos d)
    (hdone : d.sett cur → g.hi cur ≤ pos) (hK : K ≤ INF) (hLK : d.L ≤ K)
    (hQ : ∀ e ∈ d.Q, K ≤ e.1) {pd : PD} (hpt : pd.tj = t) (hph : pd.hw = hw) (hKR : K ≤ Rm + 1)
    {r r' : ℕ} (hr : r < K) (hdr : d.L ≤ r) (hr' : r' < K) (hdr' : d.L ≤ r') :
    c.carve G Y (pd.withR r) = c.carve G Y (pd.withR r') := by
  rw [hL.carve_eq hinv hdone hK hLK hQ hpt hph hr hdr (by omega),
    hL.carve_eq hinv hdone hK hLK hQ hpt hph hr' hdr' (by omega)]

/-- **The cost of reaching a settled vertex** is the tentative cost of its super-vertex. -/
theorem PLink.ent_eq (hL : PLink G c t hw Y sv g Rm) (hinv : g.Inv (sv t) INF cur pos d)
    (hdone : d.sett cur → g.hi cur ≤ pos) (hK : K ≤ INF) (hLK : d.L ≤ K)
    (hQ : ∀ e ∈ d.Q, K ≤ e.1) {pd : PD} (hpt : pd.tj = t) (hph : pd.hw = hw) {a : ℕ}
    (ha : a ∈ Y) (hs : d.sett (sv a)) (hR : d.tent (sv a) ≤ Rm) :
    c.ent G Y pd a = d.tent (sv a) := by
  have hD := hL.dr_sett hinv ha hs
  rw [← hpt, ← hph] at hD
  unfold ent
  refine le_antisymm (Nat.sInf_le hD) (le_csInf ⟨_, hD⟩ fun k hk => ?_)
  by_cases hkR : k ≤ Rm
  · rw [hpt, hph] at hk
    exact (hL.path hinv hdone hK hLK hQ hk hkR).1 hs
  · omega

end Cl

end MinCostFlow.LowStretch
