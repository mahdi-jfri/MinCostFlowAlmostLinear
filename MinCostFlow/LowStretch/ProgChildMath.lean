module

public import MinCostFlow.LowStretch.ProgChildRec

/-!
# The child of each node, in mathematics

The child step works on the nodes of a cluster `c` (its super-vertices, by local index). Each
node lies in exactly one piece of the step `D`, since the pieces are unions of `θ`-nodes. The
program writes the number of that piece to an array `CHX` (`chxP`): `k + 1` for the nodes of
petal `k`, and `0` for the others. This file shows that the others are the nodes of the stem, so
that a vertex lies in piece `k` exactly when its node has `CHX = k` (`Rec.Ok.chx_iff`). Then the
nodes of piece `k` are the nodes with key `k` (`Rec.Ok.mem_chxNodes`), and the active pairs of
`c` inside piece `k` are those whose two ends have key `k` (`Rec.Ok.act_raw_iff`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open KT

variable {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {D : Cl.Dec}

namespace Cl

/-- Every vertex lies in some piece. -/
theorem exists_raw {v : ℕ} (hv : v ∈ c.X) : ∃ k < D.nch, v ∈ (c.raw G D k).X := by
  have := (mem_Z_iff (c := c) (G := G) (D := D) (k := 0) (z := v) (Nat.zero_le _)).mp hv
  rcases this with h | ⟨j, -, hj, h⟩
  · exact ⟨0, by unfold Dec.nch; omega, by rw [raw0_X]; exact h⟩
  · exact ⟨j + 1, by unfold Dec.nch; omega, h⟩

/-- A vertex lies in only one piece. -/
theorem raw_unique {v k1 k2 : ℕ} (hk1 : k1 < D.nch) (hk2 : k2 < D.nch)
    (h1 : v ∈ (c.raw G D k1).X) (h2 : v ∈ (c.raw G D k2).X) : k1 = k2 := by
  rcases Nat.lt_trichotomy k1 k2 with h | h | h
  · exact (raw_disj hk2 h h1 h2).elim
  · exact h
  · exact (raw_disj hk1 h h2 h1).elim

end Cl

namespace Rec

/-- Two vertices with the same node lie in the same pieces. -/
theorem Ok.raw_of_sv (h : R.Ok T G P c) {a b : ℕ} (ha : a ∈ c.X) (hb : b ∈ c.X)
    (he : R.sv T c a = R.sv T c b) (k : ℕ) (hak : a ∈ (c.raw G D k).X) :
    b ∈ (c.raw G D k).X := by
  have ht : T.top c.θ a = T.top c.θ b := by
    rw [← h.get_sv ha, ← h.get_sv hb]; simp only [he]
  exact Cl.sat_raw h k a hak b (h.n_of_mem hb) (by rw [ht]; exact
    (isTop_top h.tree (h.n_of_mem hb) h.inv.one_le).1)

/-- Every node is the node of a vertex. -/
theorem Ok.exists_of_node (h : R.Ok T G P c) {u : ℕ} (hu : u < R.nodes.length) :
    ∃ v ∈ c.X, R.sv T c v = u := by
  have hk : R.nodes[u] ∈ R.nodes := List.getElem_mem hu
  obtain ⟨v, hv, hvu⟩ := exists_leaf h.tree _ (h.node_lt _ hk)
  have ht := h.node_top _ hk v hv hvu
  have hvX : v ∈ c.X := (h.X_iff v).mpr ⟨hv, by rw [ht]; exact hk⟩
  refine ⟨v, hvX, ?_⟩
  unfold sv
  rw [ht]
  exact List.Nodup.idxOf_getElem h.nodup u hu

/-- **The key of a node is its piece.** Let `chx` give `k + 1` to the nodes of the settled list
of petal `k`, and `0` to the nodes in no list. Then a vertex lies in piece `k` exactly when its
node has key `k`. -/
theorem Ok.chx_iff (h : R.Ok T G P c) {X : PetL} {mem : ℕ → ℕ} (hP : X.Ok T G P c R D mem)
    {chx : ℕ → ℕ} (hc1 : ∀ k < X.nP, ∀ u ∈ X.nodesOf mem k, chx u = k + 1)
    (hc0 : ∀ u, (∀ k < X.nP, u ∉ X.nodesOf mem k) → chx u = 0) {v : ℕ} (hv : v ∈ c.X) {k : ℕ}
    (hk : k < D.nch) : v ∈ (c.raw G D k).X ↔ chx (R.sv T c v) = k := by
  obtain ⟨k0, hk0, hv0⟩ := Cl.exists_raw (G := G) (D := D) hv
  have hval : chx (R.sv T c v) = k0 := by
    cases k0 with
    | succ j =>
      have hj : j < X.nP := by rw [hP.nP]; unfold Cl.Dec.nch at hk0; omega
      exact hc1 j hj _ ((hP.nodes j hj _).mpr ⟨v, hv0, rfl⟩)
    | zero =>
      refine hc0 _ fun j hj hm => ?_
      obtain ⟨v', hv', he⟩ := (hP.nodes j hj _).mp hm
      have hjl : j < D.ps.length := by rw [← hP.nP]; exact hj
      have := h.raw_of_sv (D := D) (Cl.W_subset_X j hv') hv he (j + 1) hv'
      rw [Cl.raw0_X] at hv0
      exact Cl.stem_disj hjl hv0 this
  rw [hval]
  constructor
  · intro hvk; exact Cl.raw_unique hk0 hk hv0 hvk
  · rintro rfl; exact hv0

/-- The node of a vertex of piece `k` has key `k`, and a node with key `k < nch` is the node of a
vertex of piece `k`. -/
theorem Ok.node_chx_iff (h : R.Ok T G P c) {X : PetL} {mem : ℕ → ℕ}
    (hP : X.Ok T G P c R D mem) {chx : ℕ → ℕ}
    (hc1 : ∀ k < X.nP, ∀ u ∈ X.nodesOf mem k, chx u = k + 1)
    (hc0 : ∀ u, (∀ k < X.nP, u ∉ X.nodesOf mem k) → chx u = 0) {u : ℕ}
    (hu : u < R.nodes.length) {k : ℕ} (hk : k < D.nch) :
    chx u = k ↔ ∃ v ∈ (c.raw G D k).X, R.sv T c v = u := by
  obtain ⟨v, hv, rfl⟩ := h.exists_of_node hu
  constructor
  · intro he; exact ⟨v, (h.chx_iff hP hc1 hc0 hv hk).mpr he, rfl⟩
  · rintro ⟨v', hv', he⟩
    have hv'X := Cl.raw_X_subset k hv'
    rw [← he]
    exact (h.chx_iff hP hc1 hc0 hv'X hk).mp hv'

/-- The keys are below the number of children. -/
theorem Ok.chx_lt (h : R.Ok T G P c) {X : PetL} {mem : ℕ → ℕ} (hP : X.Ok T G P c R D mem)
    {chx : ℕ → ℕ} (hc1 : ∀ k < X.nP, ∀ u ∈ X.nodesOf mem k, chx u = k + 1)
    (hc0 : ∀ u, (∀ k < X.nP, u ∉ X.nodesOf mem k) → chx u = 0) {u : ℕ}
    (hu : u < R.nodes.length) : chx u < D.nch := by
  obtain ⟨v, hv, rfl⟩ := h.exists_of_node hu
  obtain ⟨k0, hk0, hv0⟩ := Cl.exists_raw (G := G) (D := D) hv
  rw [(h.chx_iff hP hc1 hc0 hv hk0).mp hv0]
  exact hk0

/-- **The nodes of piece `k`.** The Kruskal nodes of the local indices with key `k` are the
`θ`-nodes of the vertices of piece `k`. -/
theorem Ok.mem_chxNodes (h : R.Ok T G P c) {X : PetL} {mem : ℕ → ℕ}
    (hP : X.Ok T G P c R D mem) {chx : ℕ → ℕ}
    (hc1 : ∀ k < X.nP, ∀ u ∈ X.nodesOf mem k, chx u = k + 1)
    (hc0 : ∀ u, (∀ k < X.nP, u ∉ X.nodesOf mem k) → chx u = 0) {k : ℕ} (hk : k < D.nch)
    (j : ℕ) : j ∈ (grp chx R.nodes.length k).map (fun u => R.nodes.getD u 0) ↔
      ∃ a ∈ (c.raw G D k).X, T.top c.θ a = j := by
  simp only [List.mem_map, grp, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨u, ⟨hu, hck⟩, rfl⟩
    obtain ⟨v, hv, rfl⟩ := (h.node_chx_iff hP hc1 hc0 hu hk).mp hck
    have hvX := Cl.raw_X_subset k hv
    refine ⟨v, hv, ?_⟩
    rw [List.getD_eq_getElem _ _ (h.sv_lt hvX), h.get_sv hvX]
  · rintro ⟨a, ha, rfl⟩
    have haX := Cl.raw_X_subset k ha
    refine ⟨R.sv T c a, ⟨h.sv_lt haX, (h.chx_iff hP hc1 hc0 haX hk).mp ha⟩, ?_⟩
    rw [List.getD_eq_getElem _ _ (h.sv_lt haX), h.get_sv haX]

theorem Ok.chxNodes_nodup (h : R.Ok T G P c) (chx : ℕ → ℕ) (k : ℕ) :
    ((grp chx R.nodes.length k).map (fun u => R.nodes.getD u 0)).Nodup := by
  refine List.Nodup.map_on (fun u hu v hv he => ?_) (List.Nodup.filter _ List.nodup_range)
  simp only [grp, List.mem_filter, List.mem_range] at hu hv
  rw [List.getD_eq_getElem _ _ hu.1, List.getD_eq_getElem _ _ hv.1] at he
  exact (List.Nodup.getElem_inj_iff h.nodup).mp he

/-- **The active pairs of piece `k`** are the active pairs of `c` whose two ends have nodes with
key `k`. -/
theorem Ok.act_raw_iff (h : R.Ok T G P c) {X : PetL} {mem : ℕ → ℕ}
    (hP : X.Ok T G P c R D mem) {chx : ℕ → ℕ}
    (hc1 : ∀ k < X.nP, ∀ u ∈ X.nodesOf mem k, chx u = k + 1)
    (hc0 : ∀ u, (∀ k < X.nP, u ∉ X.nodesOf mem k) → chx u = 0) {k : ℕ} (hk : k < D.nch)
    {p : ℕ} (hp : p ∈ c.act G P) :
    (G.pu p ∈ (c.raw G D k).X ∧ G.pv p ∈ (c.raw G D k).X) ↔
      (chx (R.sv T c (G.pu p)) = chx (R.sv T c (G.pv p)) ∧ chx (R.sv T c (G.pu p)) = k) := by
  obtain ⟨-, hu, hv, -⟩ := Cl.mem_act.mp hp
  rw [h.chx_iff hP hc1 hc0 hu hk, h.chx_iff hP hc1 hc0 hv hk]
  constructor
  · rintro ⟨e1, e2⟩; exact ⟨e1.trans e2.symm, e1⟩
  · rintro ⟨e1, e2⟩; exact ⟨e2, e1 ▸ e2⟩

end Rec

/-! ### Half flags and highways of the children -/

/-- Piece `k` is a regular petal: its highway is halved. -/
def Cl.Dec.Reg (D : Cl.Dec) (k : ℕ) : Prop := k ≠ 0 ∧ ¬ (D.sp = true ∧ k = 1)

instance (D : Cl.Dec) (k : ℕ) : Decidable (D.Reg k) := by unfold Cl.Dec.Reg; infer_instance

namespace Cl

/-- **The halved pairs of a piece.** A pair that is not light is halved in piece `k` exactly when
it is halved in `c`, or piece `k` is a regular petal and the pair lies on its highway. -/
theorem mem_raw_half {k p : ℕ} (hθ : c.θ ≤ G.pω p) :
    p ∈ (c.raw G D k).half ↔
      p ∈ c.half ∨ (D.Reg k ∧ p ∈ (c.raw G D k).hw.filter (fun q => c.θ ≤ G.pω q)) := by
  cases k with
  | zero =>
    rw [raw0_half]
    exact ⟨Or.inl, fun h => h.elim id fun h => absurd rfl h.1.1⟩
  | succ j =>
    rw [rawP_half, rawP_hw]
    unfold Cl.Dec.Reg
    by_cases hs : D.sp = true ∧ j = 0
    · rw [ite_eq_left hs]
      exact ⟨Or.inl, fun h => h.elim id fun h => absurd ⟨hs.1, by omega⟩ h.1.2⟩
    · rw [ite_eq_right hs, Finset.mem_union, List.mem_toFinset, List.mem_filter]
      have : ¬ (D.sp = true ∧ j + 1 = 1) := fun h' => hs ⟨h'.1, by omega⟩
      simp only [this, not_false_eq_true, ne_eq, Nat.add_one_ne_zero, and_true, true_and,
        decide_eq_true_eq, hθ]

/-- The flags of a stored highway for another set of halved pairs. -/
theorem hwE_half (t : ℕ) (hw : List ℕ) (θ : ℕ) (half half' : Finset ℕ) :
    hwE G t hw θ half' = (hwE G t hw θ half).map
      (fun e => (e.1, if e.1 ∈ half' then 1 else 0, e.2.2)) := by
  unfold hwE
  rw [List.map_map]
  rfl

/-- Each entry of a stored highway joins its two ends, which lie on the walk. -/
theorem hwE_joins {V Pr : Set ℕ} {t x : ℕ} {hw : List ℕ} (hwk : G.IsWalk V Pr t x hw) {θ : ℕ}
    {half : Finset ℕ} {e : ℕ × ℕ × ℕ × ℕ} (he : e ∈ hwE G t hw θ half) :
    G.Joins e.1 e.2.2.1 e.2.2.2 ∧ e.2.2.1 ∈ V ∧ e.2.2.2 ∈ V := by
  unfold hwE at he
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp he
  have hml : m < hw.length := List.mem_range.mp (List.mem_filter.mp hm).1
  exact ⟨hwk.joins_getD hml, hwk.getD_mem (by omega), hwk.getD_mem (by omega)⟩

end Cl

namespace Rec

/-- The tree path of piece `k`. -/
noncomputable def walkK (T : KT) (G : PG) (c : Cl) (R : Rec) (D : Cl.Dec) (X : PetL)
    (mem : ℕ → ℕ) (k : ℕ) : List ℕ :=
  parWalk mem X.PAR (R.sv T c (mem (X.CT + k)))
    (Cl.hwE G (c.raw G D k).t (c.raw G D k).hw c.θ c.half).length

/-- The nodes of the tree path of piece `k` are nodes of vertices of piece `k`, at the end of
their parent arc, which joins the two ends stored with it. -/
theorem Ok.walk_mem (h : R.Ok T G P c) (hX : 2 ≤ c.X.card) (hD : c.DecOk G P D) {X : PetL}
    {mem : ℕ → ℕ} (hP : X.Ok T G P c R D mem) {k : ℕ} (hk : k < D.nch) {u : ℕ}
    (hu : u ∈ walkK T G c R D X mem k) :
    mem (X.PA + u) ∈ (c.raw G D k).X ∧ mem (X.PB + u) ∈ (c.raw G D k).X ∧
      G.Joins (mem (X.PP + u)) (mem (X.PA + u)) (mem (X.PB + u)) ∧
      u = R.sv T c (mem (X.PA + u)) := by
  obtain ⟨hmap, hnode, -⟩ := hP.walk k hk
  have hgood := Cl.raw_good h.inv.good hD (h.inv.Δ_pos h.hB hX) h.hGo hk
  have hent : X.ent mem u ∈ Cl.hwE G (c.raw G D k).t (c.raw G D k).hw c.θ c.half := by
    rw [← hmap]; exact List.mem_map_of_mem hu
  obtain ⟨hj, ha, hb⟩ := Cl.hwE_joins hgood.high.1 hent
  exact ⟨ha, hb, hj, hnode u hu⟩

/-- The pairs of the highway of piece `k` without light pairs are the parent arcs of its tree
path. -/
theorem hw_filter_eq {X : PetL} {mem : ℕ → ℕ} (hP : X.Ok T G P c R D mem) {k : ℕ}
    (hk : k < D.nch) :
    (c.raw G D k).hw.filter (fun q => c.θ ≤ G.pω q) =
      (walkK T G c R D X mem k).map (fun u => mem (X.PP + u)) := by
  rw [← Cl.hwE_fst G (c.raw G D k).t (c.raw G D k).hw c.θ c.half, ← (hP.walk k hk).1, List.map_map]
  rfl

/-- **The highway test.** A pair inside piece `k` lies on its highway (without light pairs)
exactly when one of its ends has a node on the tree path whose parent arc is the pair. -/
theorem Ok.hw_test (h : R.Ok T G P c) (hX : 2 ≤ c.X.card) (hD : c.DecOk G P D) {X : PetL}
    {mem : ℕ → ℕ} (hP : X.Ok T G P c R D mem) {k : ℕ} (hk : k < D.nch) {p : ℕ} (hpm : p < G.m) :
    p ∈ (c.raw G D k).hw.filter (fun q => c.θ ≤ G.pω q) ↔
      (R.sv T c (G.pu p) ∈ walkK T G c R D X mem k ∧ mem (X.PP + R.sv T c (G.pu p)) = p) ∨
      (R.sv T c (G.pv p) ∈ walkK T G c R D X mem k ∧ mem (X.PP + R.sv T c (G.pv p)) = p) := by
  rw [hw_filter_eq hP hk, List.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨-, -, ⟨-, hj⟩, hn⟩ := h.walk_mem hX hD hP hk hu
    rcases hj with ⟨e1, -⟩ | ⟨-, e2⟩
    · left; rw [e1, ← hn]; exact ⟨hu, rfl⟩
    · right; rw [e2, ← hn]; exact ⟨hu, rfl⟩
  · rintro (⟨hu, he⟩ | ⟨hu, he⟩)
    · exact ⟨_, hu, he⟩
    · exact ⟨_, hu, he⟩

end Rec

end MinCostFlow.LowStretch
