module

public import MinCostFlow.LowStretch.ClArcs

/-!
# A record without the invariant

A raw child of a cluster need not meet the invariant `Cl.Inv` (its radius may be too small for
its threshold, which is why it is reset). The child step still runs Dijkstra on it to find its
radius. `Rec.OkW` is `Rec.Ok` without the invariant: it keeps the facts on the nodes and the
stored pairs, asks `1 ≤ θ` and that the cluster is good, and replaces the active pairs by what
Dijkstra needs of them: a pair between two super-vertices that is not stored weighs more than
four times the radius (`heavy4`). The lemmas of `ClRep` and `ClArcs` that the arc builder and
Dijkstra use are proved again for `Rec.OkW`, with the same proofs (`Rec.arcP_outW`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace Rec

variable (T : KT) (G : PG) (P : Par) (c : Cl) (R : Rec)

/-- The record `R` holds the cluster `c`, without the invariant of the clusters of a run. -/
structure OkW : Prop where
  good : c.Good G
  one_le : 1 ≤ c.θ
  tree : T.Ok G
  hG : ∀ p < G.m, G.pu p < G.n ∧ G.pv p < G.n
  hGo : G.Ok
  nodup : R.nodes.Nodup
  node_lt : ∀ k ∈ R.nodes, k < T.N
  node_top : ∀ k ∈ R.nodes, ∀ v < G.n, T.Under v k → T.top c.θ v = k
  X_iff : ∀ v, v ∈ c.X ↔ v < G.n ∧ T.top c.θ v ∈ R.nodes
  S_ok : ∀ e ∈ R.S, e.1 < G.m ∧ G.pu e.1 ∈ c.X ∧ G.pv e.1 ∈ c.X ∧
    T.top c.θ (G.pu e.1) ≠ T.top c.θ (G.pv e.1) ∧ e.2 ≤ 1 ∧ (e.2 = 1 ↔ e.1 ∈ c.half)
  S_nodup : (R.S.map Prod.fst).Nodup
  heavy4 : ∀ p < G.m, G.pu p ∈ c.X → G.pv p ∈ c.X → ¬ c.LConn G (G.pu p) (G.pv p) →
    p ∉ R.S.map Prod.fst → 4 * c.Δ G < G.pω p

variable {T G P c R}

theorem OkW.n_of_mem (h : R.OkW T G c) {v : ℕ} (hv : v ∈ c.X) : v < G.n := ((h.X_iff v).mp hv).1

theorem OkW.top_mem (h : R.OkW T G c) {v : ℕ} (hv : v ∈ c.X) : T.top c.θ v ∈ R.nodes :=
  ((h.X_iff v).mp hv).2

/-- The vertex set is a union of `θ`-nodes. -/
theorem OkW.sat (h : R.OkW T G c) : T.Sat G c.θ c.X := by
  intro a ha v hv hu
  have hk := h.top_mem ha
  exact (h.X_iff v).mpr ⟨hv, by rw [h.node_top _ hk v hv hu]; exact hk⟩

theorem OkW.sub (h : R.OkW T G c) : c.X ⊆ Finset.range G.n := fun _ hv =>
  Finset.mem_range.mpr (h.n_of_mem hv)

theorem OkW.sv_lt (h : R.OkW T G c) {v : ℕ} (hv : v ∈ c.X) : R.sv T c v < R.nodes.length :=
  List.idxOf_lt_length_of_mem (h.top_mem hv)

/-- The local index names the node. -/
theorem OkW.get_sv (h : R.OkW T G c) {v : ℕ} (hv : v ∈ c.X) :
    R.nodes[R.sv T c v]'(h.sv_lt hv) = T.top c.θ v :=
  List.getElem_idxOf (h.sv_lt hv)

/-- **Local indices are the light classes.** -/
theorem OkW.sv_iff (h : R.OkW T G c) {a b : ℕ} (ha : a ∈ c.X) (hb : b ∈ c.X) :
    R.sv T c a = R.sv T c b ↔ c.LConn G a b := by
  rw [Cl.lconn_iff h.tree h.hG h.sat h.sub h.one_le ha hb]
  constructor
  · intro e
    rw [← h.get_sv ha, ← h.get_sv hb]
    simp only [e]
  · intro e
    unfold sv; rw [e]

/-- A pair inside `X` that joins two super-vertices and is not active is heavy: `4 Δ < ω`. -/

theorem OkW.not_light (h : R.OkW T G c) {p a b : ℕ} (hj : G.Joins p a b) (ha : a ∈ c.X)
    (hb : b ∈ c.X) (hnl : ¬ c.LConn G a b) : c.θ ≤ G.pω p := by
  by_contra hl
  push Not at hl
  exact hnl ⟨[p], .cons ha hl hj (.nil hb)⟩

/-- **Pairs that are not stored are long.** A pair inside `X` that joins two super-vertices and is
not stored, or is stored but longer than a bound `D ≥ Δ`, is longer than the radius. -/
theorem OkW.heavy (h : R.OkW T G c) {D : ℕ} (hD : c.Δ G ≤ D) {p a b : ℕ} (hj : G.Joins p a b)
    (ha : a ∈ c.X) (hb : b ∈ c.X) (hnl : ¬ c.LConn G a b)
    (hp : ¬ (p ∈ R.S.map Prod.fst ∧ c.len G p ≤ D)) : c.Δ G < c.len G p := by
  have hθ := h.not_light hj ha hb hnl
  by_cases hS : p ∈ R.S.map Prod.fst
  · have : ¬ c.len G p ≤ D := fun hl => hp ⟨hS, hl⟩
    omega
  · obtain ⟨hm, hj'⟩ := hj
    have hlen := Cl.half_le_len (c := c) (G := G) hθ
    have hnl' : ¬ c.LConn G (G.pu p) (G.pv p) := by
      rcases hj' with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2]; exact hnl
      · rw [e1, e2]; rintro ⟨ps, hps⟩; exact hnl ⟨ps.reverse, hps.reverse⟩
    have hu : G.pu p ∈ c.X := by rcases hj' with ⟨e1, -⟩ | ⟨e1, -⟩ <;> rw [e1] <;> assumption
    have hv : G.pv p ∈ c.X := by rcases hj' with ⟨-, e2⟩ | ⟨-, e2⟩ <;> rw [e2] <;> assumption
    have := h.heavy4 p hm hu hv hnl' hS
    obtain ⟨-, -, -, h2, -⟩ := h.hGo p hm
    omega

/-- **The stored pairs carry Dijkstra.** An arc graph whose arcs are the stored pairs of length at
most `D ≥ Δ` between local indices, in both directions, sits on the cluster as `Cl.Ctr` asks. -/
theorem OkW.ctr (h : R.OkW T G c) {D : ℕ} (hD : c.Δ G ≤ D) {g : AG}
    (hg : ∀ u v k, g.Arc u v k ↔ ∃ p ∈ R.S.map Prod.fst, c.len G p ≤ D ∧ ∃ a ∈ c.X, ∃ b ∈ c.X,
      G.Joins p a b ∧ R.sv T c a = u ∧ R.sv T c b = v ∧ k = c.len G p) :
    c.Ctr G g (R.sv T c) {p | p ∈ R.S.map Prod.fst ∧ c.len G p ≤ D} where
  sv_iff a ha b hb := h.sv_iff ha hb
  arc_iff u v k := by
    rw [hg]
    constructor
    · rintro ⟨p, hp, hl, rest⟩; exact ⟨p, ⟨hp, hl⟩, rest⟩
    · rintro ⟨p, ⟨hp, hl⟩, rest⟩; exact ⟨p, hp, hl, rest⟩
  heavy p a b hj ha hb hnl hp := h.heavy hD hj ha hb hnl hp


variable {F : AF} {mem : ℕ → ℕ}

theorem getD_memW {j : ℕ} (hj : j < R.S.length) : R.S.getD j (0, 0) ∈ R.S := by
  rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj

/-- The facts about stored entry `j`. -/
theorem OkW.entry (h : R.OkW T G c) {j : ℕ} (hj : j < R.S.length) :
    (R.S.getD j (0, 0)).1 < G.m ∧ G.pu (R.S.getD j (0, 0)).1 ∈ c.X ∧
      G.pv (R.S.getD j (0, 0)).1 ∈ c.X ∧
      T.top c.θ (G.pu (R.S.getD j (0, 0)).1) ≠ T.top c.θ (G.pv (R.S.getD j (0, 0)).1) ∧
      (R.S.getD j (0, 0)).2 ≤ 1 ∧
      ((R.S.getD j (0, 0)).2 = 1 ↔ (R.S.getD j (0, 0)).1 ∈ c.half) :=
  h.S_ok _ (getD_memW hj)

/-- Two vertices with different nodes are not joined by light pairs. -/
theorem OkW.not_lconn (h : R.OkW T G c) {a b : ℕ} (ha : a ∈ c.X) (hb : b ∈ c.X)
    (hne : T.top c.θ a ≠ T.top c.θ b) : ¬ c.LConn G a b := by
  rw [← h.sv_iff ha hb]
  intro e
  apply hne
  rw [← h.get_sv ha, ← h.get_sv hb]
  simp only [e]

/-- A stored pair is not light. -/
theorem OkW.theta_le (h : R.OkW T G c) {j : ℕ} (hj : j < R.S.length) :
    c.θ ≤ G.pω (R.S.getD j (0, 0)).1 := by
  obtain ⟨hm, hu, hv, hne, -⟩ := h.entry hj
  exact h.not_light ⟨hm, Or.inl ⟨rfl, rfl⟩⟩ hu hv (h.not_lconn hu hv hne)

theorem Mem.pr_eqW (hM : Mem T G c R F mem) {j : ℕ} (hj : j < F.nS) :
    F.pr mem j = (R.S.getD j (0, 0)).1 := hM.pr j (hM.nS ▸ hj)

theorem Mem.fl_eqW (hM : Mem T G c R F mem) {j : ℕ} (hj : j < F.nS) :
    F.fl mem j = (R.S.getD j (0, 0)).2 := hM.fl j (hM.nS ▸ hj)

/-- The exponent of a stored pair is at least that of `θ`, and at least `1`. -/
theorem Mem.exp_geW (hM : Mem T G c R F mem) (h : R.OkW T G c) {j : ℕ} (hj : j < F.nS) :
    F.lθ ≤ mem (F.EXP + F.pr mem j) ∧ 1 ≤ mem (F.EXP + F.pr mem j) := by
  have hj' : j < R.S.length := hM.nS ▸ hj
  obtain ⟨hm, -⟩ := h.entry hj'
  have hθ := h.theta_le hj'
  rw [← hM.pr_eqW hj] at hm hθ
  rw [hM.ex _ hm, hM.th] at hθ
  refine ⟨(Nat.pow_le_pow_iff_right (by norm_num)).mp hθ, ?_⟩
  obtain ⟨-, -, -, h2, -⟩ := h.hGo _ hm
  rw [hM.ex _ hm] at h2
  by_contra h0
  have e : mem (F.EXP + F.pr mem j) = 0 := by omega
  rw [e] at h2
  norm_num at h2

/-- **The length is the length in the cluster.** -/
theorem Mem.ln_eqW (hM : Mem T G c R F mem) (h : R.OkW T G c) {j : ℕ} (hj : j < F.nS) :
    F.ln mem j = c.len G (F.pr mem j) := by
  have hj' : j < R.S.length := hM.nS ▸ hj
  obtain ⟨hm, -, -, -, hf1, hf2⟩ := h.entry hj'
  have hθ := h.theta_le hj'
  rw [← hM.pr_eqW hj] at hm hθ hf2
  rw [← hM.fl_eqW hj] at hf1 hf2
  unfold AF.ln Cl.len
  rw [if_neg (by omega), hM.pw _ hm, Nat.shiftRight_eq_div_pow]
  by_cases hh : F.pr mem j ∈ c.half
  · rw [if_pos hh, hf2.mpr hh]
  · rw [if_neg hh]
    have : F.fl mem j = 0 := by
      by_contra h0; exact hh (hf2.mp (by omega))
    rw [this]; simp

/-- A kept item has length `2 ^ (E - f)`. -/
theorem Mem.ln_powW (hM : Mem T G c R F mem) (h : R.OkW T G c) {j : ℕ} (hj : j < F.nS) :
    F.ln mem j = 2 ^ (mem (F.EXP + F.pr mem j) - F.fl mem j) := by
  have hj' : j < R.S.length := hM.nS ▸ hj
  obtain ⟨hm, -, -, -, hf1, -⟩ := h.entry hj'
  rw [← hM.pr_eqW hj] at hm
  rw [← hM.fl_eqW hj] at hf1
  have he := (hM.exp_geW h hj).2
  unfold AF.ln
  rw [hM.pw _ hm, hM.ex _ hm, Nat.shiftRight_eq_div_pow,
    Nat.pow_div (by omega) (by norm_num)]

/-- The class of a kept item is at least `1`. -/
theorem Mem.cl_posW (hM : Mem T G c R F mem) (h : R.OkW T G c) {j : ℕ} (hj : j < F.nS) :
    1 ≤ F.cl mem j := by
  have hj' : j < R.S.length := hM.nS ▸ hj
  obtain ⟨-, -, -, -, hf1, -⟩ := h.entry hj'
  rw [← hM.fl_eqW hj] at hf1
  have := (hM.exp_geW h hj).1
  unfold AF.cl; omega

theorem Mem.cl_addW (hM : Mem T G c R F mem) (h : R.OkW T G c) {j : ℕ} (hj : j < F.nS) :
    F.cl mem j + F.lθ = mem (F.EXP + F.pr mem j) - F.fl mem j + 2 := by
  have hj' : j < R.S.length := hM.nS ▸ hj
  obtain ⟨-, -, -, -, hf1, -⟩ := h.entry hj'
  rw [← hM.fl_eqW hj] at hf1
  have := (hM.exp_geW h hj)
  unfold AF.cl; omega

/-- A kept item has length `2 ^ (cl + lθ - 2)`. -/
theorem Mem.ln_clW (hM : Mem T G c R F mem) (h : R.OkW T G c) {j : ℕ} (hj : j < F.nS) :
    F.ln mem j = 2 ^ (F.cl mem j + F.lθ - 2) := by
  have hj' : j < R.S.length := hM.nS ▸ hj
  obtain ⟨-, -, -, -, hf1, -⟩ := h.entry hj'
  rw [← hM.fl_eqW hj] at hf1
  have := (hM.exp_geW h hj)
  rw [hM.ln_powW h hj]
  unfold AF.cl
  congr 1; omega

/-- **The class fixes the cost.** -/
theorem Mem.cs_eqW (hM : Mem T G c R F mem) (h : R.OkW T G c) {j j' : ℕ} (hj : j < F.nS)
    (hj' : j' < F.nS) (he : F.cc mem j = F.cc mem j') : F.cs mem j = F.cs mem j' := by
  unfold AF.cc at he
  unfold AF.cs
  have p1 := hM.cl_posW h hj
  have p2 := hM.cl_posW h hj'
  split_ifs at he ⊢ with k1 k2 k2
  · rw [hM.ln_clW h hj, hM.ln_clW h hj', he]
  · omega
  · omega
  · rfl

/-- **The classes are few.** If `4 D < 2 ^ (J + lθ)`, every class is below `J`. -/
theorem Mem.cc_ltW (hM : Mem T G c R F mem) (h : R.OkW T G c) {J : ℕ}
    (hJ : 4 * F.D < 2 ^ (J + F.lθ)) (hJ1 : 1 ≤ J) {j : ℕ} (hj : j < F.nS) : F.cc mem j < J := by
  unfold AF.cc
  split_ifs with hk
  · have hl := hM.ln_clW h hj
    have p := hM.cl_addW h hj
    unfold AF.keep at hk
    have h1 : 2 ^ (F.cl mem j + F.lθ) ≤ 4 * F.D := by
      have e : 2 ^ (F.cl mem j + F.lθ) = 4 * 2 ^ (F.cl mem j + F.lθ - 2) := by
        rw [show F.cl mem j + F.lθ = (F.cl mem j + F.lθ - 2) + 2 by omega, pow_add]
        simp only [show F.cl mem j + F.lθ - 2 + 2 - 2 = F.cl mem j + F.lθ - 2 by omega]
        ring
      rw [e, ← hl]; omega
    have := lt_of_le_of_lt h1 hJ
    have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
    omega
  · omega

/-- The local index of the first end of an item. -/
theorem Mem.ea_eqW (hM : Mem T G c R F mem) (h : R.OkW T G c) {j : ℕ} (hj : j < F.nS) :
    F.ea mem j = R.sv T c (G.pu (F.pr mem j)) := by
  have hj' : j < R.S.length := hM.nS ▸ hj
  obtain ⟨hm, hu, -⟩ := h.entry hj'
  rw [← hM.pr_eqW hj] at hm hu
  unfold AF.ea
  rw [(hM.ends _ hm).1, hM.loc _ hu]

/-- The local index of the second end of an item. -/
theorem Mem.eb_eqW (hM : Mem T G c R F mem) (h : R.OkW T G c) {j : ℕ} (hj : j < F.nS) :
    F.eb mem j = R.sv T c (G.pv (F.pr mem j)) := by
  have hj' : j < R.S.length := hM.nS ▸ hj
  obtain ⟨hm, -, hv, -⟩ := h.entry hj'
  rw [← hM.pr_eqW hj] at hm hv
  unfold AF.eb
  rw [(hM.ends _ hm).2, hM.loc _ hv]

theorem Mem.ea_ltW (hM : Mem T G c R F mem) (h : R.OkW T G c) {j : ℕ} (hj : j < F.nS) :
    F.ea mem j < F.s := by
  have hj' : j < R.S.length := hM.nS ▸ hj
  obtain ⟨-, hu, -⟩ := h.entry hj'
  rw [← hM.pr_eqW hj] at hu
  rw [hM.ea_eqW h hj, hM.s]; exact h.sv_lt hu

theorem Mem.eb_ltW (hM : Mem T G c R F mem) (h : R.OkW T G c) {j : ℕ} (hj : j < F.nS) :
    F.eb mem j < F.s := by
  have hj' : j < R.S.length := hM.nS ▸ hj
  obtain ⟨-, -, hv, -⟩ := h.entry hj'
  rw [← hM.pr_eqW hj] at hv
  rw [hM.eb_eqW h hj, hM.s]; exact h.sv_lt hv

/-- **The arcs are the stored pairs of length at most `D`.** -/
theorem Mem.arc_iffW (hM : Mem T G c R F mem) (h : R.OkW T G c) (u v k : ℕ) :
    (∃ j < F.nS, F.keep mem j ∧
      ((F.ea mem j = u ∧ F.eb mem j = v) ∨ (F.eb mem j = u ∧ F.ea mem j = v)) ∧
      F.ln mem j = k) ↔
    ∃ p ∈ R.S.map Prod.fst, c.len G p ≤ F.D ∧ ∃ a ∈ c.X, ∃ b ∈ c.X,
      G.Joins p a b ∧ R.sv T c a = u ∧ R.sv T c b = v ∧ k = c.len G p := by
  constructor
  · rintro ⟨j, hj, hk, hc, hl⟩
    have hj' : j < R.S.length := hM.nS ▸ hj
    obtain ⟨hm, hu, hv, -⟩ := h.entry hj'
    rw [← hM.pr_eqW hj] at hm hu hv
    unfold AF.keep at hk
    rw [hM.ln_eqW h hj] at hk hl
    refine ⟨F.pr mem j, ?_, hk, ?_⟩
    · rw [hM.pr_eqW hj]
      exact List.mem_map.mpr ⟨_, getD_mem hj', rfl⟩
    rw [hM.ea_eqW h hj, hM.eb_eqW h hj] at hc
    rcases hc with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact ⟨_, hu, _, hv, ⟨hm, Or.inl ⟨rfl, rfl⟩⟩, e1, e2, hl.symm⟩
    · exact ⟨_, hv, _, hu, ⟨hm, Or.inr ⟨rfl, rfl⟩⟩, e1, e2, hl.symm⟩
  · rintro ⟨p, hp, hk, a, ha, b, hb, ⟨hm, hjn⟩, e1, e2, hl⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
    obtain ⟨j, hj', hje⟩ := List.mem_iff_getElem.mp he
    have hj : j < F.nS := hM.nS ▸ hj'
    have hpr : F.pr mem j = e.1 := by
      rw [hM.pr_eqW hj, List.getD_eq_getElem _ _ hj', hje]
    refine ⟨j, hj, ?_, ?_, ?_⟩
    · unfold AF.keep; rw [hM.ln_eqW h hj, hpr]; exact hk
    · rw [hM.ea_eqW h hj, hM.eb_eqW h hj, hpr]
      rcases hjn with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact Or.inl ⟨e1, e2⟩
      · rw [h1, h2]; exact Or.inr ⟨e1, e2⟩
    · rw [hM.ln_eqW h hj, hpr, hl]



/-- **What `arcP` leaves, for Dijkstra.** After `arcP` on the record `R`, the graph sits on the
cluster as `Cl.Ctr` asks, its nodes are the local indices, and the arcs meet the conditions of
`DL.Shape` that concern them. -/
theorem arcP_outW {w : ℕ} {A : AP} {mem mem' : ℕ → ℕ} {v : ℕ}
    (hpost : (arcPC w).post A.args mem v mem') (hM : Mem T G c R A.toAF mem) (h : R.OkW T G c)
    (hD : c.Δ G ≤ A.D) :
    c.Ctr G (A.g mem') (R.sv T c) {p | p ∈ R.S.map Prod.fst ∧ c.len G p ≤ A.D} ∧
    (∀ u, (A.g mem').ok u ↔ u ∈ Finset.range A.s) ∧
    (∀ u < A.s, (A.g mem').lo u ≤ (A.g mem').hi u ∧ (A.g mem').hi u ≤ 2 * A.nS) ∧
    (∀ k < 2 * A.nS, mem' (A.HD + k) < A.s + 1 ∧ mem' (A.CS + k) ≤ A.D ∧
      ∃ j < A.nS, mem' (A.CL + k) = A.toAF.cc mem j) ∧
    (∀ k < 2 * A.nS, ∀ k' < 2 * A.nS, mem' (A.CL + k) = mem' (A.CL + k') →
      mem' (A.CS + k) = mem' (A.CS + k')) ∧
    ∑ u ∈ Finset.range A.s, ((A.g mem').hi u - (A.g mem').lo u + 1) ≤ 2 * A.nS + A.s := by
  obtain ⟨harc, hper, h0, hmono, hlast, hmk1, hmk2, -⟩ := hpost A rfl
  have hea : ∀ j < A.nS, A.toAF.ea mem j < A.s := fun j hj => hM.ea_ltW h hj
  have heb : ∀ j < A.nS, A.toAF.eb mem j < A.s := fun j hj => hM.eb_ltW h hj
  refine ⟨h.ctr hD fun u v k => (harc u v k).trans (hM.arc_iffW h u v k), fun u => ?_,
    fun u hu => ?_, fun k hk => ?_, fun k hk k' hk' he => ?_, ?_⟩
  · simp only [AP.g, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      by_contra hc
      have e : u = A.s := by omega
      rw [e, hmk2] at h2; omega
    · intro hu; exact ⟨by omega, hmk1 u hu⟩
  · simp only [AP.g, if_pos (show u < A.s + 1 by omega)]
    refine ⟨hmono u (by omega), ?_⟩
    have := AP.off_mono hmono (show u + 1 ≤ A.s + 1 by omega) le_rfl
    rw [show A.OFF + 1 + u = A.OFF + (u + 1) by omega]
    rw [show A.OFF + 1 + A.s = A.OFF + (A.s + 1) by omega] at hlast
    omega
  · obtain ⟨j, hj, hh, hc, hl⟩ := hper k hk
    refine ⟨?_, ?_, j, hj, hl⟩
    · rcases hh with e | e <;> rw [e] <;> simp only [AF.ta, AF.tb] <;> split_ifs
      · have := hea j hj; omega
      · show A.s < A.s + 1; omega
      · have := heb j hj; omega
      · show A.s < A.s + 1; omega
    · rw [hc]; unfold AF.cs; split_ifs with hk
      · exact hk
      · exact Nat.zero_le _
  · obtain ⟨j, hj, -, hc, hl⟩ := hper k hk
    obtain ⟨j', hj', -, hc', hl'⟩ := hper k' hk'
    rw [hc, hc']
    rw [hl, hl'] at he
    exact hM.cs_eqW h hj hj' he
  · have e : ∀ u ∈ Finset.range A.s, (A.g mem').hi u - (A.g mem').lo u + 1 =
        (mem' (A.OFF + 1 + u) - mem' (A.OFF + u)) + 1 := fun u hu => by
      have hu' : u < A.s + 1 := by simp at hu; omega
      simp only [AP.g, if_pos hu']
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, AP.sum_deg hmono (by omega)]
    have := AP.off_mono hmono (show A.s ≤ A.s + 1 by omega) le_rfl
    rw [show A.OFF + 1 + A.s = A.OFF + (A.s + 1) by omega] at hlast
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
    omega




/-- A record of a cluster of a run meets `OkW`. -/
theorem Ok.toW (h : R.Ok T G P c) : R.OkW T G c :=
  ⟨h.inv.good, h.inv.one_le, h.tree, h.hG, h.hGo, h.nodup, h.node_lt, h.node_top, h.X_iff,
    h.S_ok, h.S_nodup, fun p hm hu hv hnl hS => h.heavy4 hm hu hv hnl fun hp => hS (h.act_sub p hp)⟩

/-- Every local index names a node of a vertex. -/
theorem OkW.exists_of_node (h : R.OkW T G c) {u : ℕ} (hu : u < R.nodes.length) :
    ∃ v ∈ c.X, R.sv T c v = u := by
  have hk : R.nodes[u] ∈ R.nodes := List.getElem_mem hu
  obtain ⟨v, hv, hvu⟩ := KT.exists_leaf h.tree _ (h.node_lt _ hk)
  have ht := h.node_top _ hk v hv hvu
  have hvX : v ∈ c.X := (h.X_iff v).mpr ⟨hv, by rw [ht]; exact hk⟩
  refine ⟨v, hvX, ?_⟩
  unfold sv
  rw [ht]
  exact List.Nodup.idxOf_getElem h.nodup u hu

/-- **The radius from the end of Dijkstra.** At the end of a run from the node of the center on
an arc graph that sits on the cluster (`Cl.Ctr`), with an empty queue and `INF` above the radius,
the largest tentative cost over the local indices is the radius. -/
theorem OkW.sup_tent (h : R.OkW T G c) {g : AG} {S : Set ℕ} (hctr : c.Ctr G g (R.sv T c) S)
    {INF cur pos : ℕ} {d : DS} (hi : g.Inv (R.sv T c c.x0) INF cur pos d)
    (hdone : d.sett cur → g.hi cur ≤ pos) (hQ : d.Q = []) (hINF : c.Δ G < INF) {f : ℕ → ℕ}
    (hf : ∀ u < R.nodes.length, f u = d.tent u) :
    (Finset.range R.nodes.length).sup f = c.Δ G := by
  refine le_antisymm (Finset.sup_le fun u hu => ?_) (Finset.sup_le fun y hy => ?_)
  · have hu' := Finset.mem_range.mp hu
    obtain ⟨y, hy, rfl⟩ := h.exists_of_node hu'
    rw [hf _ hu', (hctr.tent_eq h.good.conn hi hdone hQ hINF hy).2]
    exact c.d_le_Δ hy
  · have hs := h.sv_lt hy
    have e : c.d G c.x0 y = f (R.sv T c y) := by
      rw [hf _ hs, (hctr.tent_eq h.good.conn hi hdone hQ hINF hy).2]
    rw [e]
    exact Finset.le_sup (f := f) (Finset.mem_range.mpr hs)

end Rec

end MinCostFlow.LowStretch
