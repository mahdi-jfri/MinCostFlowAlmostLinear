module

public import MinCostFlow.LowStretch.ProgChildOkW
public import MinCostFlow.LowStretch.ProgDijRun
public import MinCostFlow.LowStretch.ProgAct

/-!
# Dijkstra on the record of a raw child: the graph

The child step runs Dijkstra on the record of each raw child to find its radius. This file shows
that the graph that `arcP` builds from a record that meets `Rec.OkW` has the shape that
`dijRun` asks for (`Rec.shape_arcP`), once the stamps `TS` lie after the arrays of `arcP` and the
queue after the stamps, and the queue has room for `2 nS + s + 1` entries.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace Rec

variable {T : KT} {G : PG} {c : Cl} {R : Rec}

/-- **The graph of `arcP` has the shape that Dijkstra asks for.** -/
theorem shape_arcP {w : ℕ} {A : AP} {mem mem' : ℕ → ℕ} {v m n NL : ℕ}
    (hpre : A.Pre w mem m n NL) (hpost : (arcPC w).post A.args mem v mem')
    (hM : Mem T G c R A.toAF mem) (h : R.OkW T G c) (hD : c.Δ G ≤ A.D)
    {J Aq INF TS Dq rs : ℕ} (hJ : 4 * A.D < 2 ^ (J + A.lθ)) (hJ1 : 1 ≤ J)
    (hcap : 2 * A.nS + A.s + 1 ≤ Aq) (hTS : A.OK + A.s + 1 ≤ TS) (hDq : TS + 5 * (A.s + 1) ≤ Dq)
    (hfits : PQFits w Dq J Aq INF) (hINF : 0 < INF) (hINFw : INF + A.D < 2 ^ w)
    (hrs : rs < 2 ^ w) (hos : A.os < 2 ^ w) :
    (A.toDL Dq J Aq INF TS rs).Shape w mem' (Finset.range A.s) := by
  obtain ⟨-, hok, harcs, hheads, hcls, hsum⟩ := arcP_outW hpost hM h hD
  have l5 := hpre.l5
  have l6 := hpre.l6
  have l7 := hpre.l7
  have l8 := hpre.l8
  have l9 := hpre.l9
  have l10 := hpre.l10
  have l11 := hpre.l11
  refine ⟨fun u => ?_, fun u hu => ?_, fun k hk => ?_, fun k hk k' hk' he => ?_, ?_, ?_, hfits,
    hrs, hos, hINF⟩
  · rw [AP.toDL_g]; exact hok u
  · rw [AP.toDL_g]; exact harcs u (Finset.mem_range.mp hu)
  · have hk' : k < 2 * A.nS := hk
    obtain ⟨h1, h2, j, hj, h3⟩ := hheads k hk'
    show mem' (A.HD + k) < A.s + 1 ∧ mem' (A.CL + k) < J ∧ INF + mem' (A.CS + k) < 2 ^ w
    refine ⟨h1, ?_, by omega⟩
    rw [h3]
    exact hM.cc_ltW h hJ hJ1 hj
  · exact hcls k hk k' hk' he
  · have e : ∀ u ∈ Finset.range A.s, (A.toDL Dq J Aq INF TS rs).deg mem' u ≤
        (A.g mem').hi u - (A.g mem').lo u + 1 := fun u _ => by
      unfold DL.deg; rw [AP.toDL_g]; omega
    have := Finset.sum_le_sum e
    show _ ≤ Aq
    omega
  · show A.OFF + (A.s + 1) ≤ TS ∧ A.OFF + 1 + (A.s + 1) ≤ TS ∧ A.HD + 2 * A.nS ≤ TS ∧
      A.CS + 2 * A.nS ≤ TS ∧ A.CL + 2 * A.nS ≤ TS ∧ A.OK + (A.s + 1) ≤ TS ∧
      TS + 5 * (A.s + 1) ≤ Dq
    omega


/-- **The radius from the end of the run.** At the end of `dijRun` from the node of the center
on the graph of `arcP` (unchanged since `arcP` ended, below the stamps), the largest tentative
cost of the local indices, as `maxP` reads it, is the radius. -/
theorem draw_result {w : ℕ} {A : AP} {mem mem' mem0 mem'' : ℕ → ℕ} {v : ℕ}
    (hpost : (arcPC w).post A.args mem v mem') (hM : Mem T G c R A.toAF mem) (h : R.OkW T G c)
    (hD : c.Δ G ≤ A.D) {Dq J Aq INF TS rs Rr : ℕ} (hINF : c.Δ G < INF)
    (hg : (A.toDL Dq J Aq INF TS rs).g mem0 = A.g mem')
    {x : RunX}
    (hrun : RunI w ⟨A.toDL Dq J Aq INF TS rs, Finset.range A.s, R.sv T c c.x0, Rr⟩ mem0 x mem'')
    (hempty : ∀ cl, x.2.1 cl = []) :
    (Finset.range A.s).sup (tvOf mem'' TS (A.s + 1) rs INF) = c.Δ G := by
  obtain ⟨hctr, -⟩ := arcP_outW hpost hM h hD
  obtain ⟨-, hrep, hinv, hdone, -⟩ := hrun
  rw [hg] at hinv hdone
  have hQ : x.1.Q = [] := by
    rw [hrep.Q]
    refine List.eq_nil_iff_forall_not_mem.mpr fun e he => ?_
    obtain ⟨cl, -, hcl⟩ := mem_pqAll.mp he
    rw [hempty cl] at hcl
    exact List.not_mem_nil hcl
  have hs : A.s = R.nodes.length := hM.s
  have key := h.sup_tent hctr hinv hdone hQ hINF (f := tvOf mem'' TS (A.s + 1) rs INF)
    fun u hu => by
      rw [hrep.tent u, if_pos (by rw [Finset.mem_range, hs]; exact hu)]
      rfl
  rw [← key, hs]

/-- **The cost cells at the end of the run.** In the setting of `draw_result`, each node `u < s`
holds the stamp `rs` and a cost below `INF`, so `maxP` reads words. -/
theorem draw_cells {w : ℕ} {A : AP} {mem mem' mem0 mem'' : ℕ → ℕ} {v : ℕ}
    (hpost : (arcPC w).post A.args mem v mem') (hM : Mem T G c R A.toAF mem) (h : R.OkW T G c)
    (hD : c.Δ G ≤ A.D) {Dq J Aq INF TS rs Rr : ℕ} (hINF : c.Δ G < INF)
    (hg : (A.toDL Dq J Aq INF TS rs).g mem0 = A.g mem')
    {x : RunX}
    (hrun : RunI w ⟨A.toDL Dq J Aq INF TS rs, Finset.range A.s, R.sv T c c.x0, Rr⟩ mem0 x mem'')
    (hempty : ∀ cl, x.2.1 cl = []) {u : ℕ} (hu : u < A.s) :
    mem'' (TS + (A.s + 1) + u) < INF := by
  obtain ⟨hctr, -⟩ := arcP_outW hpost hM h hD
  obtain ⟨-, hrep, hinv, hdone, -⟩ := hrun
  rw [hg] at hinv hdone
  have hQ : x.1.Q = [] := by
    rw [hrep.Q]
    refine List.eq_nil_iff_forall_not_mem.mpr fun e he => ?_
    obtain ⟨cl, -, hcl⟩ := mem_pqAll.mp he
    rw [hempty cl] at hcl
    exact List.not_mem_nil hcl
  have hs : A.s = R.nodes.length := hM.s
  obtain ⟨y, hy, rfl⟩ := h.exists_of_node (hs ▸ hu)
  have ht := (hctr.tent_eq h.good.conn hinv hdone hQ hINF hy).2
  have hle := c.d_le_Δ (G := G) hy
  rw [hrep.tent, if_pos (Finset.mem_range.mpr hu)] at ht
  unfold DL.tentOf at ht
  change (if mem'' (TS + _) = rs then mem'' (TS + (A.s + 1) + _) else INF) = _ at ht
  split_ifs at ht
  · omega
  · omega

end Rec

end MinCostFlow.LowStretch
