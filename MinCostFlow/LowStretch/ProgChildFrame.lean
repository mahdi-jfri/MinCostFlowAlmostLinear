module

public import MinCostFlow.LowStretch.ProgChildSpec
public import MinCostFlow.LowStretch.ProgChildMath

/-!
# Frames for the child step

The child step writes the records of the children one after the other. Writing child `k` must not
change what the records of the earlier children read. Two facts give this.
* A record read by `RecAt` stays in memory when the cells it reads keep their values
  (`RecAt.congr_blk`): its block, its arrays, the input arrays, and the label and local index of each
  of its vertices.
* The local indices that two different pieces write sit at different heads (`Rec.Ok.hd_ne`): two
  nodes with one head lie on one path of the merge tree (`KT.hd_eq`), and each piece is a union
  of `θ`-nodes, so such nodes would share a vertex.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM KT

/-- The record block read at `BK` does not change when its nine words do not. -/
theorem RecL.read_congr_blk {M M' : ℕ → ℕ} {BK : ℕ} (hb : ∀ i < 9, M' (BK + i) = M (BK + i)) :
    RecL.read M' BK = RecL.read M BK := by
  unfold RecL.read
  have e0 := hb 0 (by omega); simp only [Nat.add_zero] at e0
  rw [e0, hb 1 (by omega), hb 2 (by omega), hb 3 (by omega), hb 4 (by omega), hb 5 (by omega),
    hb 6 (by omega), hb 7 (by omega), hb 8 (by omega)]

/-- **A record stays in memory** when the cells that `RecAt` reads keep their values. -/
theorem RecAt.congr_blk {T : KT} {G : PG} {c : Cl} {R : Rec} {E : GlobL} {BK : ℕ} {M M' : ℕ → ℕ}
    (h : RecAt T G c R E (RecL.read M BK) M) (hb : ∀ i < 9, M' (BK + i) = M (BK + i))
    (hreg : ∀ r ∈ (RecL.read M BK).regs, ∀ a, r.1 ≤ a → a < r.1 + r.2 → M' a = M a)
    (hin : ∀ p < G.m, M' (E.IN + 3 * p) = M (E.IN + 3 * p) ∧
      M' (E.IN + 3 * p + 1) = M (E.IN + 3 * p + 1))
    (hpw : ∀ p < G.m, M' (E.PW + p) = M (E.PW + p))
    (hex : ∀ p < G.m, M' (E.EXP + p) = M (E.EXP + p))
    (hlab : ∀ v ∈ c.X, M' (E.LAB + v) = M (E.LAB + v))
    (hloc : ∀ v ∈ c.X, M' (E.LOC + M (E.LAB + v)) = M (E.LOC + M (E.LAB + v))) :
    RecAt T G c R E (RecL.read M' BK) M' := by
  rw [RecL.read_congr_blk hb]
  set L := RecL.read M BK
  have hA := h.arcs
  have hS : ∀ a, L.SA ≤ a → a < L.SA + 2 * L.nS → M' a = M a :=
    hreg (L.SA, 2 * L.nS) (by simp [RecL.regs])
  have hN : ∀ a, L.NA ≤ a → a < L.NA + L.s → M' a = M a :=
    hreg (L.NA, L.s) (by simp [RecL.regs])
  have hH : ∀ a, L.HW ≤ a → a < L.HW + 4 * L.nH → M' a = M a :=
    hreg (L.HW, 4 * L.nH) (by simp [RecL.regs])
  have hnS : L.nS = R.S.length := hA.nS
  have hs : L.s = R.nodes.length := hA.s
  refine ⟨⟨hA.nS, hA.s, fun j hj => ?_, fun j hj => ?_, fun p hp => ?_, fun p hp => ?_,
    fun p hp => ?_, fun v hv => ?_, hA.th⟩, fun i hi => ?_, h.x0, h.t, h.nH, fun j hj => ?_,
    fun v hv => ?_⟩
  · show M' (L.SA + 2 * j) = _
    rw [hS _ (by omega) (by omega)]; exact hA.pr j hj
  · show M' (L.SA + 2 * j + 1) = _
    rw [hS _ (by omega) (by omega)]; exact hA.fl j hj
  · show M' (E.IN + 3 * p) = _ ∧ M' (E.IN + 3 * p + 1) = _
    rw [(hin p hp).1, (hin p hp).2]; exact hA.ends p hp
  · show M' (E.PW + p) = _
    rw [hpw p hp]; exact hA.pw p hp
  · show _ = 2 ^ M' (E.EXP + p)
    rw [hex p hp]; exact hA.ex p hp
  · show M' (E.LOC + M' (E.LAB + v)) = _
    rw [hlab v hv, hloc v hv]; exact hA.loc v hv
  · rw [hN _ (by omega) (by omega)]; exact h.nodes i hi
  · obtain ⟨e1, e2, e3, e4⟩ := h.hw j hj
    rw [hH _ (by omega) (by omega), hH _ (by omega) (by omega), hH _ (by omega) (by omega),
      hH _ (by omega) (by omega)]
    exact ⟨e1, e2, e3, e4⟩
  · rw [hlab v hv]; exact h.lab v hv

namespace Rec

variable {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {D : Cl.Dec}

/-- **Different pieces write different heads.** A node between a vertex of piece `j` and its
`θ`-node, and a node between a vertex of piece `k ≠ j` and its `θ`-node, have different heads. -/
theorem Ok.hd_ne (h : R.Ok T G P c) {j k : ℕ} (hj : j < D.nch) (hk : k < D.nch) (hjk : j ≠ k)
    {v v' u u' : ℕ} (hv : v ∈ (c.raw G D j).X) (hv' : v' ∈ (c.raw G D k).X)
    (hu : T.Under v u) (hut : T.Under u (T.top c.θ v)) (hu' : T.Under v' u')
    (hu't : T.Under u' (T.top c.θ v')) : T.hd G u ≠ T.hd G u' := by
  intro he
  have hN := h.tree.n_lt
  have hvn : v < G.n := h.n_of_mem (Cl.raw_X_subset j hv)
  have hvn' : v' < G.n := h.n_of_mem (Cl.raw_X_subset k hv')
  have huN : u < T.N := hu.lt_N h.tree (by omega)
  have huN' : u' < T.N := hu'.lt_N h.tree (by omega)
  have hsj := Cl.sat_raw (D := D) h j
  have hsk := Cl.sat_raw (D := D) h k
  rcases hd_eq h.tree huN huN' he with hc | hc
  · have : v ∈ (c.raw G D k).X := hsk v' hv' v hvn
      ((hu.trans hc).trans hu't)
    exact hjk (Cl.raw_unique hj hk hv this)
  · have : v' ∈ (c.raw G D j).X := hsj v hv v' hvn'
      ((hu'.trans hc).trans hut)
    exact hjk (Cl.raw_unique hk hj hv' this).symm

end Rec

end MinCostFlow.LowStretch
