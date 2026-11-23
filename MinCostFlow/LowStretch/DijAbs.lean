module

public import Mathlib.Data.List.Basic
public import Mathlib.Order.Basic
public import Mathlib.Tactic.Linarith

/-!
# Dijkstra, as steps on an abstract state

The program runs Dijkstra twice per cluster: once for the distances from the center, and once per
petal for the costs from its target. Both runs are the same steps on the same kind of state, so
we prove the steps correct once, here, without memory.

A graph is given in arc form (`AG`): the arcs of `u` are the indices `k` with `lo u ≤ k < hi u`,
and arc `k` goes to `hd k` with cost `cs k`. Arcs into a vertex outside `ok` are ignored. The
state (`DS`) has a tentative cost `tent` for each vertex, the settled vertices, the queue `Q` of
entries `(key, vertex)`, and the key `L` of the last settled vertex. The value `INF` stands for
"not reached".

There are three steps: drop a stale entry (`Inv.drop`), settle the vertex of a least entry
(`Inv.settle`), and relax one arc of the vertex settled last (`Inv.relax`). They keep the
invariant `Inv`. The main result is `Inv.path`: for a bound `K` on the queue, every walk from the
source to `v` costs at least `tent v` if `v` is settled, and at least `K` if not. So when the
queue is empty, the settled vertices are the reachable ones with their exact costs, and when the
least key is above `r`, the settled vertices are exactly those of cost at most `r`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

/-- A graph in arc form. -/
structure AG where
  /-- The first arc of a vertex. -/
  lo : ℕ → ℕ
  /-- One past the last arc of a vertex. -/
  hi : ℕ → ℕ
  /-- The head of an arc. -/
  hd : ℕ → ℕ
  /-- The cost of an arc. -/
  cs : ℕ → ℕ
  /-- The allowed heads. -/
  ok : ℕ → Prop

/-- The state of a run of Dijkstra. -/
structure DS where
  /-- The tentative costs. -/
  tent : ℕ → ℕ
  /-- The settled vertices. -/
  sett : ℕ → Prop
  /-- The queue. -/
  Q : List (ℕ × ℕ)
  /-- The key of the last settled vertex. -/
  L : ℕ

namespace AG

variable (g : AG)

/-- An arc from `u` to `v` of cost `c`. -/
def Arc (u v c : ℕ) : Prop :=
  ∃ k, g.lo u ≤ k ∧ k < g.hi u ∧ g.hd k = v ∧ g.cs k = c ∧ g.ok v

/-- `Reach s v k`: a walk from `s` to `v` of cost `k`. -/
inductive Reach (s : ℕ) : ℕ → ℕ → Prop
  | refl : Reach s s 0
  | step {u v k c : ℕ} : Reach s u k → g.Arc u v c → Reach s v (k + c)

/-- The invariant, while the arcs of `cur` below `pos` have been relaxed. -/
structure Inv (s INF cur pos : ℕ) (d : DS) : Prop where
  arcs : ∀ u, d.sett u → ∀ k, g.lo u ≤ k → k < g.hi u → (u = cur → k < pos) → g.ok (g.hd k) →
    d.tent (g.hd k) ≤ d.tent u + g.cs k
  queued : ∀ x, ¬ d.sett x → d.tent x < INF → (d.tent x, x) ∈ d.Q
  keys : ∀ e ∈ d.Q, d.L ≤ e.1 ∧ d.tent e.2 ≤ e.1 ∧ e.1 < INF
  settled_le : ∀ u, d.sett u → d.tent u ≤ d.L
  reach : ∀ x, d.tent x < INF → g.Reach s x (d.tent x)
  src : d.tent s = 0
  L_lt : d.L < INF
  tent_le : ∀ x, d.tent x ≤ INF
  cur_L : d.sett cur → d.tent cur = d.L

variable {g}

/-- The first state: only the source has a cost, and it is queued. -/
theorem inv_init {s INF : ℕ} (hINF : 0 < INF) :
    g.Inv s INF s 0
      { tent := Function.update (fun _ => INF) s 0, sett := (fun _ => False), Q := [(0, s)], L := 0 } := by
  refine ⟨fun u hu => hu.elim, fun x _ hx => ?_, fun e he => ?_, fun u hu => hu.elim, fun x hx => ?_,
    by simp, hINF, fun x => ?_, fun h => h.elim⟩
  · by_cases hxs : x = s
    · subst hxs; simp
    · simp [Function.update_of_ne hxs] at hx
  · simp only [List.mem_singleton] at he
    subst he
    simp [hINF]
  · by_cases hxs : x = s
    · subst hxs; simp only [Function.update_self]; exact Reach.refl
    · simp [Function.update_of_ne hxs] at hx
  · by_cases hxs : x = s
    · subst hxs; simp
    · simp [Function.update_of_ne hxs]

/-- **Drop** an entry whose vertex is settled or whose key is above the tentative cost. -/
theorem Inv.drop {s INF cur pos : ℕ} {d : DS} (h : g.Inv s INF cur pos d) {e : ℕ × ℕ}
    (hstale : d.sett e.2 ∨ d.tent e.2 < e.1) {Q' : List (ℕ × ℕ)} (h1 : ∀ e' ∈ Q', e' ∈ d.Q)
    (h2 : ∀ e' ∈ d.Q, e' ≠ e → e' ∈ Q') :
    g.Inv s INF cur pos { d with Q := Q' } := by
  refine ⟨h.arcs, fun x hx hxi => ?_, fun e' he' => h.keys e' (h1 e' he'),
    h.settled_le, h.reach, h.src, h.L_lt, h.tent_le, h.cur_L⟩
  have hq := h.queued x hx hxi
  refine h2 _ hq ?_
  intro hc
  rw [← hc] at hstale
  rcases hstale with h1 | h1
  · exact hx h1
  · exact lt_irrefl _ h1

/-- **Settle** the vertex of a least entry, once the arcs of the last settled vertex are done. -/
theorem Inv.settle {s INF cur pos : ℕ} {d : DS} (h : g.Inv s INF cur pos d)
    (hdone : d.sett cur → g.hi cur ≤ pos) {e : ℕ × ℕ} (he : e ∈ d.Q)
    (hmin : ∀ e' ∈ d.Q, e.1 ≤ e'.1) (hx : ¬ d.sett e.2) (hk : d.tent e.2 = e.1)
    {Q' : List (ℕ × ℕ)} (h1 : ∀ e' ∈ Q', e' ∈ d.Q) (h2 : ∀ e' ∈ d.Q, e' ≠ e → e' ∈ Q') :
    g.Inv s INF e.2 (g.lo e.2)
      { tent := d.tent, sett := (fun u => d.sett u ∨ u = e.2), Q := Q', L := e.1 } := by
  have hkey := h.keys e he
  refine ⟨fun u hu k hk1 hk2 hcu hok => ?_, fun x hx hxi => ?_, fun e' he' => ?_,
    fun u hu => ?_, h.reach, h.src, hkey.2.2, h.tent_le, fun _ => hk⟩
  · rcases hu with hu | rfl
    · refine h.arcs u hu k hk1 hk2 (fun hc => ?_) hok
      subst hc
      exact lt_of_lt_of_le hk2 (hdone hu)
    · exact absurd (hcu rfl) (by omega)
  · simp only [not_or] at hx
    refine h2 _ (h.queued x hx.1 hxi) ?_
    intro hc
    exact hx.2 (by rw [← hc])
  · have he'' := h1 e' he'
    exact ⟨hmin e' he'', (h.keys e' he'').2⟩
  · rcases hu with hu | rfl
    · exact (h.settled_le u hu).trans hkey.1
    · exact hk.le

/-- **Relax** arc `j` of the vertex settled last: if it gives a smaller cost to its head, the head
takes that cost and is queued with it. -/
theorem Inv.relax {s INF cur j : ℕ} {d : DS} (h : g.Inv s INF cur j d) (hcur : d.sett cur)
    (hj1 : g.lo cur ≤ j) (hj2 : j < g.hi cur) :
    (g.ok (g.hd j) ∧ d.tent cur + g.cs j < d.tent (g.hd j) → ∀ Q' : List (ℕ × ℕ),
      (∀ e ∈ Q', e ∈ d.Q ∨ e = (d.tent cur + g.cs j, g.hd j)) → (∀ e ∈ d.Q, e ∈ Q') →
      (d.tent cur + g.cs j, g.hd j) ∈ Q' →
      g.Inv s INF cur (j + 1)
        { d with
          tent := Function.update d.tent (g.hd j) (d.tent cur + g.cs j)
          Q := Q' }) ∧
    (¬ (g.ok (g.hd j) ∧ d.tent cur + g.cs j < d.tent (g.hd j)) → g.Inv s INF cur (j + 1) d) := by
  have hcL := h.cur_L hcur
  constructor
  · rintro ⟨hok, hlt⟩ Q' hQ1 hQ2 hQ3
    set v := g.hd j
    set t' := d.tent cur + g.cs j
    -- the head is not settled: a settled vertex has cost at most `L`
    have hv : ¬ d.sett v := by
      intro hv
      have := h.settled_le v hv
      omega
    have hvc : v ≠ cur := fun hc => hv (hc ▸ hcur)
    have hvlt : t' < INF := lt_of_lt_of_le hlt (h.tent_le v)
    refine ⟨fun u hu k hk1 hk2 hcu hok' => ?_, fun x hx hxi => ?_, fun e he => ?_,
      fun u hu => ?_, fun x hx => ?_, ?_, h.L_lt, fun x => ?_, fun _ => ?_⟩
    · have huv : u ≠ v := fun hc => hv (hc ▸ hu)
      simp only [Function.update_of_ne huv]
      by_cases hkj : u = cur ∧ k = j
      · obtain ⟨rfl, rfl⟩ := hkj
        show Function.update d.tent v t' v ≤ t'
        rw [Function.update_self]
      · have hold := h.arcs u hu k hk1 hk2 (fun hc => by
          have := hcu hc
          by_contra hc'
          exact hkj ⟨hc, by omega⟩) hok'
        by_cases hkv : g.hd k = v
        · rw [hkv, Function.update_self]
          rw [hkv] at hold
          omega
        · rw [Function.update_of_ne hkv]; exact hold
    · by_cases hxv : x = v
      · rw [hxv]; dsimp only; rw [Function.update_self]; exact hQ3
      · simp only [Function.update_of_ne hxv] at hxi ⊢
        exact hQ2 _ (h.queued x hx hxi)
    · rcases hQ1 e he with he | rfl
      swap
      · dsimp only
        rw [Function.update_self]
        exact ⟨by omega, le_rfl, hvlt⟩
      · have := h.keys e he
        refine ⟨this.1, ?_, this.2.2⟩
        dsimp only
        by_cases hev : e.2 = v
        · rw [hev, Function.update_self]; rw [hev] at this; omega
        · rw [Function.update_of_ne hev]; exact this.2.1
    · have huv : u ≠ v := fun hc => hv (hc ▸ hu)
      simp only [Function.update_of_ne huv]
      exact h.settled_le u hu
    · by_cases hxv : x = v
      · subst hxv
        simp only [Function.update_self]
        have hr := h.reach cur (by omega)
        exact Reach.step hr ⟨j, hj1, hj2, rfl, rfl, hok⟩
      · simp only [Function.update_of_ne hxv] at hx ⊢
        exact h.reach x hx
    · have hsv : s ≠ v := by
        intro hc
        have := h.src
        rw [← hc] at hlt
        omega
      show Function.update d.tent v t' s = 0
      rw [Function.update_of_ne hsv]; exact h.src
    · dsimp only
      by_cases hxv : x = v
      · subst hxv; simp only [Function.update_self]; omega
      · rw [Function.update_of_ne hxv]; exact h.tent_le x
    · dsimp only
      rw [Function.update_of_ne (Ne.symm hvc)]; exact hcL
  · intro hno
    refine ⟨fun u hu k hk1 hk2 hcu hok => ?_, h.queued, h.keys, h.settled_le, h.reach, h.src,
      h.L_lt, h.tent_le, h.cur_L⟩
    by_cases hkj : u = cur ∧ k = j
    · obtain ⟨rfl, rfl⟩ := hkj
      by_contra hc
      exact hno ⟨hok, by omega⟩
    · exact h.arcs u hu k hk1 hk2 (fun hc => by
        have := hcu hc
        by_contra hc'
        exact hkj ⟨hc, by omega⟩) hok

/-- An arc that is not relaxed yet does not matter once all arcs of `cur` are done. -/
theorem Inv.full {s INF cur pos : ℕ} {d : DS} (h : g.Inv s INF cur pos d)
    (hdone : d.sett cur → g.hi cur ≤ pos) :
    ∀ u, d.sett u → ∀ k, g.lo u ≤ k → k < g.hi u → g.ok (g.hd k) →
      d.tent (g.hd k) ≤ d.tent u + g.cs k := by
  intro u hu k hk1 hk2 hok
  refine h.arcs u hu k hk1 hk2 (fun hc => ?_) hok
  subst hc
  exact lt_of_lt_of_le hk2 (hdone hu)

/-- **The main property.** Let `K` be at most `INF`, at least `L`, and at most every key of the
queue. Then every walk from `s` to a settled `v` costs at least `tent v`, and every walk to a
vertex that is not settled costs at least `K`. -/
theorem Inv.path {s INF cur pos : ℕ} {d : DS} (h : g.Inv s INF cur pos d)
    (hdone : d.sett cur → g.hi cur ≤ pos) {K : ℕ} (hK : K ≤ INF) (hLK : d.L ≤ K)
    (hQ : ∀ e ∈ d.Q, K ≤ e.1) {v k : ℕ} (hr : g.Reach s v k) :
    (d.sett v → d.tent v ≤ k) ∧ (¬ d.sett v → K ≤ k) := by
  have hfull := h.full hdone
  -- an unsettled vertex with a cost below `INF` is queued, so its cost is at least `K`
  have hun : ∀ x, ¬ d.sett x → K ≤ d.tent x := by
    intro x hx
    by_cases hxi : d.tent x < INF
    · exact hQ _ (h.queued x hx hxi)
    · push Not at hxi; omega
  induction hr with
  | refl =>
    refine ⟨fun _ => by rw [h.src], fun hs => ?_⟩
    have := hun s hs
    rw [h.src] at this
    exact this
  | @step u v k c _ ha ih =>
    obtain ⟨j, hj1, hj2, rfl, rfl, hok⟩ := ha
    by_cases hu : d.sett u
    · have h1 := ih.1 hu
      have h2 := hfull u hu j hj1 hj2 hok
      refine ⟨fun _ => by omega, fun hv => ?_⟩
      have := hun _ hv
      omega
    · have h1 := ih.2 hu
      refine ⟨fun hv => ?_, fun _ => by omega⟩
      have := h.settled_le _ hv
      omega

/-- A settled vertex is reached at its cost. -/
theorem Inv.reach_sett {s INF cur pos : ℕ} {d : DS} (h : g.Inv s INF cur pos d) {v : ℕ}
    (hv : d.sett v) : g.Reach s v (d.tent v) :=
  h.reach v (lt_of_le_of_lt (h.settled_le v hv) h.L_lt)

/-! ### Parents

The program also records, for each vertex with a cost, the vertex and the arc that gave this cost.
Then the parents lead back to the source along arcs whose costs add up (`ParInv`). -/

/-- Every vertex `x` other than the source with a cost below `INF` has a settled parent `par x`,
and arc `parc x` of the parent goes to `x` and gives its cost. -/
def ParInv (s INF : ℕ) (d : DS) (par parc : ℕ → ℕ) : Prop :=
  ∀ x, x ≠ s → d.tent x < INF → d.sett (par x) ∧ g.lo (par x) ≤ parc x ∧ parc x < g.hi (par x) ∧
    g.hd (parc x) = x ∧ g.ok x ∧ d.tent (par x) + g.cs (parc x) = d.tent x

theorem parInv_init {s INF : ℕ} (par parc : ℕ → ℕ) :
    g.ParInv s INF
      { tent := Function.update (fun _ => INF) s 0, sett := (fun _ => False), Q := [(0, s)], L := 0 }
      par parc := by
  intro x hx hlt
  simp [Function.update_of_ne hx] at hlt

/-- The parents survive a change of the queue and of the key, and more settled vertices. -/
theorem ParInv.mono {s INF : ℕ} {d d' : DS} {par parc : ℕ → ℕ} (h : g.ParInv s INF d par parc)
    (ht : d'.tent = d.tent) (hs : ∀ u, d.sett u → d'.sett u) : g.ParInv s INF d' par parc := by
  intro x hx hlt
  rw [ht] at hlt ⊢
  obtain ⟨h1, h2⟩ := h x hx hlt
  exact ⟨hs _ h1, h2⟩

/-- The parents after an improving relax step of arc `j` of `cur`. -/
theorem ParInv.relax {s INF cur j : ℕ} {d : DS} {par parc : ℕ → ℕ} (hp : g.ParInv s INF d par parc)
    (h : g.Inv s INF cur j d) (hcur : d.sett cur) (hj1 : g.lo cur ≤ j) (hj2 : j < g.hi cur)
    (hok : g.ok (g.hd j)) (hlt : d.tent cur + g.cs j < d.tent (g.hd j)) (Q' : List (ℕ × ℕ)) :
    g.ParInv s INF
      { d with tent := Function.update d.tent (g.hd j) (d.tent cur + g.cs j), Q := Q' }
      (Function.update par (g.hd j) cur) (Function.update parc (g.hd j) j) := by
  have hcL := h.cur_L hcur
  have hv : ¬ d.sett (g.hd j) := by
    intro hv
    have := h.settled_le _ hv
    omega
  have hvc : g.hd j ≠ cur := fun hc => hv (hc ▸ hcur)
  intro x hx hxlt
  by_cases hxv : x = g.hd j
  · subst hxv
    simp only [Function.update_self]
    exact ⟨hcur, hj1, hj2, trivial, hok, by rw [Function.update_of_ne (Ne.symm hvc)]⟩
  · simp only [Function.update_of_ne hxv] at hxlt ⊢
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp x hx hxlt
    have hpv : par x ≠ g.hd j := fun hc => hv (hc ▸ h1)
    exact ⟨h1, h2, h3, h4, h5, by rw [Function.update_of_ne hpv]; exact h6⟩

end AG

end MinCostFlow.LowStretch
