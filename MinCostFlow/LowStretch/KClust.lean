module

public import MinCostFlow.LowStretch.KTree
public import MinCostFlow.LowStretch.Root
public import MinCostFlow.LowStretch.Volume

/-!
# Clusters made of Kruskal nodes

The program keeps every cluster as a set of whole `θ`-nodes of the Kruskal tree, where `θ` is the
threshold of the cluster (`KT.Sat`). This file shows why this is enough.
* Inside such a cluster, two vertices are joined by light pairs exactly when they have the same
  `θ`-node (`Cl.lconn_iff`). So the `θ`-nodes are the super-vertices.
* Petals, what is left after a petal, and resets keep the property (`KT.Sat.carve`,
  `KT.Sat.diff`, `KT.Sat.mono`).

Here `T.top x v` is the `x`-node of the vertex `v`: the highest node above `v` of weight below
`x`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace KT

variable {T : KT} {G : PG}

open Classical in
/-- The `x`-node of `v`. -/
noncomputable def top (T : KT) (x v : ℕ) : ℕ :=
  T.par^[Nat.findGreatest (fun i => T.mw (T.par^[i] v) < x) T.N] v

theorem isTop_top (h : T.Ok G) {x v : ℕ} (hv : v < G.n) (hx : 1 ≤ x) : T.IsTop x v (T.top x v) := by
  classical
  set i := Nat.findGreatest (fun i => T.mw (T.par^[i] v) < x) T.N with hi
  have h0 : T.mw (T.par^[0] v) < x := by
    simp only [Function.iterate_zero, id_eq]; rw [h.leaf_mw v hv]; omega
  have hs : T.mw (T.par^[i] v) < x := Nat.findGreatest_spec (P := fun i => T.mw (T.par^[i] v) < x)
    (Nat.zero_le _) h0
  have hiN : i ≤ T.N := Nat.findGreatest_le _
  refine ⟨⟨i, rfl⟩, hs, fun hk => ?_⟩
  rcases Nat.lt_or_ge i T.N with hlt | hge
  · have := Nat.findGreatest_is_greatest (P := fun i => T.mw (T.par^[i] v) < x)
      (show i < i + 1 by omega) (by omega)
    rw [Function.iterate_succ_apply'] at this
    exact not_lt.mp this
  · have e : i = T.N := le_antisymm hiN hge
    have hN := h.n_lt
    have : T.par^[i] v = T.N - 1 := by rw [e]; exact reach_root h (by omega)
    unfold top at hk
    rw [← hi, this] at hk
    omega

theorem IsTop.eq_top (h : T.Ok G) {x v k : ℕ} (hv : v < G.n) (hx : 1 ≤ x) (ht : T.IsTop x v k) :
    k = T.top x v := by
  have hN := h.n_lt
  exact ht.unique h (by omega) (isTop_top h hv hx)

theorem top_lt_N (h : T.Ok G) {x v : ℕ} (hv : v < G.n) (hx : 1 ≤ x) : T.top x v < T.N := by
  have hN := h.n_lt
  exact (isTop_top h hv hx).1.lt_N h (by omega)

/-- Every node has a vertex below it. -/
theorem exists_leaf (h : T.Ok G) : ∀ k < T.N, ∃ v < G.n, T.Under v k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases hkn : k < G.n
    · exact ⟨k, hkn, Under.refl k⟩
    push Not at hkn
    obtain ⟨hp1, -, -, hlt1, -⟩ := h.ch k hkn hk
    obtain ⟨v, hv, hu⟩ := ih _ hlt1 (by omega)
    exact ⟨v, hv, hu.trans (by have := Under.par (T := T) (T.ch1 k); rwa [hp1] at this)⟩

/-- No vertex lies below both children of a node. -/
theorem not_under_both (h : T.Ok G) {k v : ℕ} (hkn : G.n ≤ k) (hk : k < T.N)
    (h1 : T.Under v (T.ch1 k)) (h2 : T.Under v (T.ch2 k)) : False := by
  obtain ⟨hp1, hp2, hne, hlt1, hlt2⟩ := h.ch k hkn hk
  have hN := h.n_lt
  rcases Under.total h1 h2 with hu | hu
  · have := (hu.par_of_ne h hne).le h (by rw [hp1]; omega)
    rw [hp1] at this
    omega
  · have := (hu.par_of_ne h (Ne.symm hne)).le h (by rw [hp2]; omega)
    rw [hp2] at this
    omega

/-- **A pair leaving a node is at least as heavy as the parent of the node.** -/
theorem cross_le (h : T.Ok G) (hG : ∀ p < G.m, G.pu p < G.n ∧ G.pv p < G.n) {p u v c : ℕ}
    (hp : p < G.m) (hj : G.Joins p u v) (hu : T.Under u c) (hv : ¬ T.Under v c)
    (hc : c + 1 < T.N) : T.mw (T.par c) ≤ G.pω p := by
  have h1 := hG p hp
  obtain ⟨l, hl1, hl2, hlw⟩ := exists_lca h hp h1.1 h1.2
  have hN := h.n_lt
  have key : T.Under u l ∧ T.Under v l ∧ u < T.N := by
    rcases hj.2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [← e1, ← e2]; exact ⟨hl1, hl2, by omega⟩
    · rw [← e1, ← e2]; exact ⟨hl2, hl1, by omega⟩
  obtain ⟨hul, hvl, huN⟩ := key
  rcases Under.total hu hul with hcl | hlc
  · have hne : c ≠ l := fun e => hv (e ▸ hvl)
    have := (hcl.par_of_ne h hne).mw_le h (par_lt_N h (by omega))
    omega
  · exact absurd (hvl.trans hlc) hv

/-- A walk from below `c` to outside `c` has a pair that leaves `c`. -/
theorem exists_cross {V Pr : Set ℕ} {a b : ℕ} {ps : List ℕ} (hw : G.IsWalk V Pr a b ps) {c : ℕ}
    (ha : T.Under a c) (hb : ¬ T.Under b c) :
    ∃ p ∈ ps, ∃ u v, G.Joins p u v ∧ T.Under u c ∧ ¬ T.Under v c := by
  induction hw with
  | nil => exact absurd ha hb
  | @cons a b' b'' p qs _ _ hj _ ih =>
    by_cases hb' : T.Under b' c
    · obtain ⟨q, hq, u, v, hq'⟩ := ih hb' hb
      exact ⟨q, List.mem_cons_of_mem _ hq, u, v, hq'⟩
    · exact ⟨p, List.mem_cons_self, a, b', hj, ha, hb'⟩

/-- `IsTop` for a lower bound sits below `IsTop` for a higher bound. -/
theorem IsTop.under_of_le (h : T.Ok G) {x x' v k k' : ℕ} (hv : v < T.N) (hxx : x' ≤ x)
    (h' : T.IsTop x' v k') (ht : T.IsTop x v k) : T.Under k' k := by
  rcases Under.total h'.1 ht.1 with hu | hu
  · exact hu
  · by_cases hne : k = k'
    · rw [hne]; exact Under.refl _
    have hkN := ht.1.lt_N h hv
    have hk1 : k + 1 < T.N := by
      have := hu.le h hkN
      have := h'.1.lt_N h hv
      omega
    have := (hu.par_of_ne h hne).mw_le h (par_lt_N h hkN)
    have := ht.2.2 hk1
    have := h'.2.1
    omega

/-- The set `X` is a union of `x`-nodes. -/
def Sat (T : KT) (G : PG) (x : ℕ) (X : Finset ℕ) : Prop :=
  ∀ a ∈ X, ∀ v, v < G.n → T.Under v (T.top x a) → v ∈ X

/-- A union of `x`-nodes is a union of `x'`-nodes for `x' ≤ x`. -/
theorem Sat.mono (h : T.Ok G) {x x' : ℕ} {X : Finset ℕ} (hs : T.Sat G x X)
    (hXn : X ⊆ Finset.range G.n) (hx' : 1 ≤ x') (hxx : x' ≤ x) : T.Sat G x' X := by
  intro a ha v hv hu
  have han : a < G.n := Finset.mem_range.mp (hXn ha)
  have hN := h.n_lt
  have := (isTop_top h han hx').under_of_le h (by omega) hxx (isTop_top h han (by omega))
  exact hs a ha v hv (hu.trans this)

/-- **Light pairs inside an `x`-node.** Two vertices of one `x`-node are joined by a walk inside
the node whose pairs weigh at most the weight of the node. -/
theorem walk_in_top (h : T.Ok G) (hG : ∀ p < G.m, G.pu p < G.n ∧ G.pv p < G.n) {x a b : ℕ}
    (hx : 1 ≤ x) (ha : a < G.n) (hb : b < G.n) (he : T.top x a = T.top x b) :
    ∃ ps, G.IsWalk (T.leaves G (T.top x a)) {p | G.pω p ≤ T.mw (T.top x a)} a b ps :=
  walk_of_under h hG _ (top_lt_N h ha hx) a b ha hb (isTop_top h ha hx).1
    (by rw [he]; exact (isTop_top h hb hx).1)

/-- A light walk keeps the `x`-node. -/
theorem top_eq_of_walk (h : T.Ok G) (hG : ∀ p < G.m, G.pu p < G.n ∧ G.pv p < G.n) {V : Set ℕ}
    {x a b : ℕ} {ps : List ℕ} (hw : G.IsWalk V {p | G.pω p < x} a b ps) (hx : 1 ≤ x)
    (ha : a < G.n) (hb : b < G.n) : T.top x a = T.top x b :=
  (top_of_walk h hG hw (isTop_top h ha hx)).eq_top h hb hx

end KT

namespace Cl

open KT

variable {T : KT} {G : PG} {c : Cl}

/-- **Light connections are the `θ`-nodes.** In a cluster that is a union of `θ`-nodes, two
vertices are joined by light pairs inside `X` exactly when they have the same `θ`-node. -/
theorem lconn_iff (h : T.Ok G) (hG : ∀ p < G.m, G.pu p < G.n ∧ G.pv p < G.n)
    (hs : T.Sat G c.θ c.X) (hXn : c.X ⊆ Finset.range G.n) (hθ : 1 ≤ c.θ) {a b : ℕ}
    (ha : a ∈ c.X) (hb : b ∈ c.X) : c.LConn G a b ↔ T.top c.θ a = T.top c.θ b := by
  have han : a < G.n := Finset.mem_range.mp (hXn ha)
  have hbn : b < G.n := Finset.mem_range.mp (hXn hb)
  constructor
  · rintro ⟨ps, hps⟩
    exact top_eq_of_walk h hG hps hθ han hbn
  · intro he
    obtain ⟨ps, hps⟩ := walk_in_top h hG hθ han hbn he
    refine ⟨ps, hps.mono (fun v hv => hs a ha v hv.1 hv.2) fun p hp => ?_⟩
    have := (isTop_top h han hθ).2.1
    exact lt_of_le_of_lt hp this

/-- A light pair inside a union of `θ`-nodes can be replaced by a walk inside `X` whose pairs are
lighter than `θ` and weigh at most the weight of the `θ`-node. -/
theorem light_replace (h : T.Ok G) (hG : ∀ p < G.m, G.pu p < G.n ∧ G.pv p < G.n)
    (hs : T.Sat G c.θ c.X) (hXn : c.X ⊆ Finset.range G.n) (hθ : 1 ≤ c.θ) {p a b : ℕ}
    (hj : G.Joins p a b) (hl : G.pω p < c.θ) (ha : a ∈ c.X) (hb : b ∈ c.X) :
    ∃ ps, G.IsWalk ↑c.X {q | G.pω q < c.θ ∧ G.pω q ≤ T.mw (T.top c.θ a)} a b ps := by
  have han : a < G.n := Finset.mem_range.mp (hXn ha)
  have hbn : b < G.n := Finset.mem_range.mp (hXn hb)
  have he : T.top c.θ a = T.top c.θ b :=
    top_eq_of_walk h hG (V := ↑c.X) (ps := [p]) (.cons ha hl hj (.nil hb)) hθ han hbn
  obtain ⟨ps, hps⟩ := walk_in_top h hG hθ han hbn he
  have := (isTop_top h han hθ).2.1
  refine ⟨ps, hps.mono (fun v hv => hs a ha v hv.1 hv.2) fun q hq => ?_⟩
  exact ⟨lt_of_le_of_lt hq this, hq⟩

end Cl

namespace KT

variable {T : KT} {G : PG} {c : Cl}

/-- A petal carved from a union of `θ`-nodes is a union of `θ`-nodes. -/
theorem Sat.carve (h : T.Ok G) (hG : ∀ p < G.m, G.pu p < G.n ∧ G.pv p < G.n) (hc : c.Conn G)
    {Y : Finset ℕ} (hY : Y ⊆ c.X) (hXn : c.X ⊆ Finset.range G.n) (hθ : 1 ≤ c.θ)
    (hs : T.Sat G c.θ Y) (pd : PD) : T.Sat G c.θ (c.carve G Y pd) := by
  intro a ha v hv hu
  have haY := Cl.carve_subset Y pd ha
  have han : a < G.n := Finset.mem_range.mp (hXn (hY haY))
  have he : T.top c.θ a = T.top c.θ v :=
    (IsTop.of_common h (by have := h.n_lt; omega) (isTop_top h han hθ) (isTop_top h han hθ).1 hu
      (isTop_top h han hθ).2.1).eq_top h hv hθ
  obtain ⟨ps, hps⟩ := walk_in_top h hG hθ han hv he
  have hw : G.IsWalk ↑Y (c.light G) a v ps :=
    hps.mono (fun z hz => hs a haY z hz.1 hz.2) fun q hq =>
      lt_of_le_of_lt hq (isTop_top h han hθ).2.1
  exact Cl.carve_light_walk hc hY hw ha

/-- What is left after carving a petal from a union of `θ`-nodes is a union of `θ`-nodes. -/
theorem Sat.diff (h : T.Ok G) (hG : ∀ p < G.m, G.pu p < G.n ∧ G.pv p < G.n) (hc : c.Conn G)
    {Y : Finset ℕ} (hY : Y ⊆ c.X) (hXn : c.X ⊆ Finset.range G.n) (hθ : 1 ≤ c.θ)
    (hs : T.Sat G c.θ Y) (pd : PD) : T.Sat G c.θ (Y \ c.carve G Y pd) := by
  intro a ha v hv hu
  obtain ⟨haY, hac⟩ := Finset.mem_sdiff.mp ha
  have hvY := hs a haY v hv hu
  refine Finset.mem_sdiff.mpr ⟨hvY, fun hvc => hac ?_⟩
  have han : a < G.n := Finset.mem_range.mp (hXn (hY haY))
  have he : T.top c.θ a = T.top c.θ v :=
    (IsTop.of_common h (by have := h.n_lt; omega) (isTop_top h han hθ) (isTop_top h han hθ).1 hu
      (isTop_top h han hθ).2.1).eq_top h hv hθ
  obtain ⟨ps, hps⟩ := walk_in_top h hG hθ han hv he
  have hw : G.IsWalk ↑Y (c.light G) v a ps.reverse :=
    (hps.mono (fun z hz => hs a haY z hz.1 hz.2) fun q hq =>
      lt_of_le_of_lt hq (isTop_top h han hθ).2.1).reverse
  exact Cl.carve_light_walk hc hY hw hvc

end KT

end MinCostFlow.LowStretch
