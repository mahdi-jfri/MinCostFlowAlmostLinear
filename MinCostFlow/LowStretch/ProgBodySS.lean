module

public import MinCostFlow.LowStretch.ClRep
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# A cluster with `s` super-vertices has at least `s - 1` stored pairs

The cost of the body pays its per-node work from the stored pairs, so it needs
`s ≤ |S| + 1` (`Rec.Ok.nodes_le`). The reason: the super-vertices are joined by stored pairs.
A shortest walk from the center to a vertex has length at most the radius `Δ`, so each of its
pairs is either light (inside one super-vertex) or no longer than `Δ`. A pair that joins two
super-vertices and is not stored is longer than `Δ` (`Rec.Ok.heavy`), so the pairs of the walk
that change the super-vertex are stored. Hence the graph `Rec.svG` on the super-vertices, with
an edge for each stored pair, is connected, and a connected graph on `s` vertices has at least
`s - 1` edges (`SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one`). Each edge comes from
a stored pair, so there are at most `|S|` edges.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace Rec

variable {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec}

/-- The graph of the super-vertices: two of them are adjacent when a stored pair joins them. -/
def svG (T : KT) (G : PG) (c : Cl) (R : Rec) : SimpleGraph (Fin R.nodes.length) where
  Adj u v := u ≠ v ∧ ∃ p ∈ R.S.map Prod.fst, ∃ a ∈ c.X, ∃ b ∈ c.X, G.Joins p a b ∧
    R.sv T c a = u.val ∧ R.sv T c b = v.val
  symm := ⟨fun u v ⟨hne, p, hp, a, ha, b, hb, hj, e1, e2⟩ =>
    ⟨Ne.symm hne, p, hp, b, hb, a, ha, hj.symm, e2, e1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem svG_adj {u v : Fin R.nodes.length} : (svG T G c R).Adj u v ↔ u ≠ v ∧
    ∃ p ∈ R.S.map Prod.fst, ∃ a ∈ c.X, ∃ b ∈ c.X, G.Joins p a b ∧
      R.sv T c a = u.val ∧ R.sv T c b = v.val := Iff.rfl

/-- Walks no longer than the radius stay connected in `svG`. -/
theorem Ok.svG_walk (h : R.Ok T G P c) {a y : ℕ} {ps : List ℕ}
    (hw : G.IsWalk ↑c.X Set.univ a y ps) (hl : ∀ p ∈ ps, c.len G p ≤ c.Δ G) :
    ∀ u v : Fin R.nodes.length, u.val = R.sv T c a → v.val = R.sv T c y →
      (svG T G c R).Reachable u v := by
  induction hw with
  | nil ha =>
    intro u v hu hv
    rw [show u = v from Fin.ext (hu.trans hv.symm)]
  | @cons a b y p qs ha _ hj hrest ih =>
    intro u v hu hv
    have hb : b ∈ c.X := hrest.start_mem
    have ih' := ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))
      ⟨R.sv T c b, h.sv_lt hb⟩ v rfl hv
    by_cases hab : R.sv T c a = R.sv T c b
    · rw [show u = ⟨R.sv T c b, h.sv_lt hb⟩ from Fin.ext (hu.trans hab)]
      exact ih'
    · have hL : ¬ c.LConn G a b := fun hL => hab ((h.sv_iff ha hb).mpr hL)
      have hS : p ∈ R.S.map Prod.fst := by
        by_contra hS
        have := h.heavy (le_refl _) hj ha hb hL (fun hp => hS hp.1)
        have := hl p List.mem_cons_self
        omega
      refine SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable (svG_adj.mpr ?_)) ih'
      refine ⟨fun e => hab ?_, p, hS, a, ha, b, hb, hj, hu.symm, rfl⟩
      rw [← hu, e]

/-- Every super-vertex holds a vertex of the cluster. -/
theorem Ok.exists_in_node (h : R.Ok T G P c) (u : Fin R.nodes.length) :
    ∃ y ∈ c.X, R.sv T c y = u.val := by
  have hmem : R.nodes[u.val] ∈ R.nodes := List.getElem_mem u.isLt
  obtain ⟨v, hv, hu⟩ := KT.exists_leaf h.tree _ (h.node_lt _ hmem)
  have htop := h.node_top _ hmem v hv hu
  refine ⟨v, (h.X_iff v).mpr ⟨hv, htop ▸ hmem⟩, ?_⟩
  unfold sv
  rw [htop]
  exact h.nodup.idxOf_getElem _ u.isLt

/-- `svG` is connected. -/
theorem Ok.svG_connected (h : R.Ok T G P c) (hs : 0 < R.nodes.length) :
    (svG T G c R).Connected := by
  have hc := h.inv.good.conn
  have hr : ∀ u : Fin R.nodes.length,
      (svG T G c R).Reachable ⟨R.sv T c c.x0, h.sv_lt hc.1⟩ u := fun u => by
    obtain ⟨y, hy, hyu⟩ := h.exists_in_node u
    obtain ⟨ps, hps, hlen⟩ := PG.exists_walk_dist (c.len G) (hc.2 y hy)
    have hd := c.d_le_Δ (G := G) hy
    have hle : ∀ p ∈ ps, c.len G p ≤ c.Δ G := fun p hp => by
      have := PG.le_wlen (len := c.len G) hp
      unfold Cl.d at hd
      omega
    exact h.svG_walk hps hle _ u rfl hyu.symm
  have : Nonempty (Fin R.nodes.length) := ⟨⟨0, hs⟩⟩
  exact ⟨fun u v => (hr u).symm.trans (hr v)⟩

/-- A number as a super-vertex (`0` when it is too large). -/
def toFin {s : ℕ} (hs : 0 < s) (x : ℕ) : Fin s := if hx : x < s then ⟨x, hx⟩ else ⟨0, hs⟩

theorem toFin_val {s : ℕ} (hs : 0 < s) (u : Fin s) : toFin hs u.val = u := by
  simp [toFin, u.isLt]

/-- The edge of a stored pair, as an element of `Sym2`. -/
noncomputable def svEdge (T : KT) (G : PG) (c : Cl) (R : Rec) (hs : 0 < R.nodes.length)
    (i : Fin R.S.length) : Sym2 (Fin R.nodes.length) :=
  s(toFin hs (R.sv T c (G.pu (R.S[i]).1)), toFin hs (R.sv T c (G.pv (R.S[i]).1)))

/-- **At most `|S| + 1` super-vertices.** -/
theorem Ok.nodes_le (h : R.Ok T G P c) : R.nodes.length ≤ R.S.length + 1 := by
  rcases Nat.eq_zero_or_pos R.nodes.length with hs | hs
  · omega
  have hcon := (h.svG_connected hs).card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hcon
  classical
  have hsub : (svG T G c R).edgeSet ⊆ ↑(Finset.univ.image (svEdge T G c R hs)) := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
    obtain ⟨-, p, hp, a, ha, b, hb, ⟨-, hj⟩, e1, e2⟩ := svG_adj.mp he
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    simp only [List.getElem_map] at hj
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
    refine ⟨⟨i, by simpa using hi⟩, ?_⟩
    have ei : (R.S[(⟨i, by simpa using hi⟩ : Fin R.S.length)]).1 = (R.S[i]'(by simpa using hi)).1 :=
      rfl
    unfold svEdge
    rw [ei]
    dsimp only at e1 e2
    rcases hj with ⟨ea, eb⟩ | ⟨ea, eb⟩
    · rw [ea, eb, e1, e2, toFin_val, toFin_val]
    · rw [ea, eb, e1, e2, toFin_val, toFin_val, Sym2.eq_swap]
  have h1 : Nat.card (svG T G c R).edgeSet ≤ (Finset.univ.image (svEdge T G c R hs)).card := by
    rw [← Set.ncard_coe_finset, Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  have h2 := Finset.card_image_le (s := Finset.univ) (f := svEdge T G c R hs)
  rw [Finset.card_univ, Fintype.card_fin] at h2
  omega

end Rec

end MinCostFlow.LowStretch
