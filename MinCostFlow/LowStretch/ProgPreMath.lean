module

public import MinCostFlow.LowStretch.ProgEntrySpec

/-!
# The record of the first cluster is correct

The `x`-nodes of the merge tree (`KT.IsNode`) are the nodes `top x v` of the vertices
(`KT.isNode_top`, `KT.IsNode.top_eq`). Two different `x`-nodes do not lie one below the other,
so their heavy-path heads differ (`KT.IsNode.hd_ne`). With these facts the record `rootRec`
holds the first cluster (`rootRec_ok`): its nodes are the `θ`-nodes, and every active pair joins
two different `θ`-nodes, since its ends are not joined by light pairs (`lconn_iff`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open MinCostFlow.Cited

namespace KT

variable {T : KT} {G : PG} {x k v : ℕ}

theorem IsNode.isTop (hk : T.IsNode x k) (hu : T.Under v k) : T.IsTop x v k :=
  ⟨hu, hk.2.1, hk.2.2⟩

/-- The `x`-node of a vertex is an `x`-node. -/
theorem isNode_top (h : T.Ok G) (hv : v < G.n) (hx : 1 ≤ x) : T.IsNode x (T.top x v) :=
  ⟨top_lt_N h hv hx, (isTop_top h hv hx).2.1, (isTop_top h hv hx).2.2⟩

/-- An `x`-node above a vertex is its `x`-node. -/
theorem IsNode.top_eq (h : T.Ok G) (hk : T.IsNode x k) (hv : v < G.n) (hx : 1 ≤ x)
    (hu : T.Under v k) : T.top x v = k :=
  ((hk.isTop hu).eq_top h hv hx).symm

/-- An `x`-node does not lie below another `x`-node. -/
theorem IsNode.not_under (h : T.Ok G) {a b : ℕ} (ha : T.IsNode x a) (hb : T.IsNode x b)
    (hne : a ≠ b) : ¬ T.Under a b := by
  intro hu
  have hab : a < b := lt_of_le_of_ne (hu.le h ha.1) hne
  have h1 : a + 1 < T.N := by have := hb.1; omega
  have h2 := (hu.par_of_ne h hne).mw_le h (par_lt_N h ha.1)
  have h3 := ha.2.2 h1
  have h4 := hb.2.1
  omega

/-- Two different `x`-nodes have different heads. -/
theorem IsNode.hd_ne (h : T.Ok G) {a b : ℕ} (ha : T.IsNode x a) (hb : T.IsNode x b)
    (hne : a ≠ b) : T.hd G a ≠ T.hd G b := by
  intro he
  rcases hd_eq h ha.1 hb.1 he with hu | hu
  · exact ha.not_under h hb hne hu
  · exact hb.not_under h ha (Ne.symm hne) hu

end KT

variable {G : WGraph} {T : KT}

theorem one_le_rootθ : 1 ≤ rootθ T G := one_le_thr _ _ _

@[simp] theorem rootCl_θ : (rootCl T G).θ = rootθ T G := rfl

@[simp] theorem rootCl_X : (rootCl T G).X = Finset.range G.n := rfl

theorem mem_rootRec_nodes {k : ℕ} :
    k ∈ (rootRec T G).nodes ↔ T.IsNode (rootθ T G) k := by
  classical
  simp only [rootRec, List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

theorem mem_rootRec_S {e : ℕ × ℕ} :
    e ∈ (rootRec T G).S ↔ e.2 = 0 ∧ e.1 < G.m ∧
      T.top (rootθ T G) ((pgOf G).pu e.1) ≠ T.top (rootθ T G) ((pgOf G).pv e.1) := by
  classical
  obtain ⟨p, f⟩ := e
  simp only [rootRec, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq,
    Prod.mk.injEq]
  constructor
  · rintro ⟨q, ⟨hq, hne⟩, rfl, rfl⟩
    exact ⟨rfl, hq, hne⟩
  · rintro ⟨rfl, hq, hne⟩
    exact ⟨p, ⟨hq, hne⟩, rfl, rfl⟩

theorem rootRec_S_fst :
    (rootRec T G).S.map Prod.fst = (List.range G.m).filter fun p =>
      decide (T.top (rootθ T G) ((pgOf G).pu p) ≠ T.top (rootθ T G) ((pgOf G).pv p)) := by
  classical
  simp only [rootRec, List.map_map]
  exact List.map_id'' (fun _ => rfl) _ |>.trans (by congr 1)

/-- **The record of the first cluster holds it.** -/
theorem rootRec_ok (hA : Allowed G) (hn : 2 ≤ G.n) (hT : T.Ok (pgOf G)) :
    (rootRec T G).Ok T (pgOf G) (par G.n G.m) (rootCl T G) := by
  classical
  have hP := hA.fit
  have hG : ∀ p < (pgOf G).m, (pgOf G).pu p < (pgOf G).n ∧ (pgOf G).pv p < (pgOf G).n :=
    fun p hp => ⟨(hP.ok p hp).1, (hP.ok p hp).2.1⟩
  have hθ := one_le_rootθ (T := T) (G := G)
  have hnG : (pgOf G).n = G.n := rfl
  have hmG : (pgOf G).m = G.m := by simp [pgOf]
  refine ⟨root_inv hT hG hP.B hP.ω (root_conn hA.valid hA.conn) hn, hT, hG, hP.ok, hP.B, hP.Q,
    (List.nodup_range).filter _, fun k hk => (mem_rootRec_nodes.mp hk).1,
    fun k hk v hv hu => (mem_rootRec_nodes.mp hk).top_eq hT hv hθ hu, fun v => ?_,
    fun e he => ?_, ?_, fun p hp => ?_, by simp [rootRec, rootCl, root]⟩
  · simp only [rootCl_X, Finset.mem_range, mem_rootRec_nodes]
    exact ⟨fun hv => ⟨hv, KT.isNode_top hT hv hθ⟩, fun h => h.1⟩
  · obtain ⟨h2, hm, hne⟩ := mem_rootRec_S.mp he
    have hm' : e.1 < (pgOf G).m := by rw [hmG]; exact hm
    refine ⟨hm', ?_, ?_, hne, by omega, ?_⟩
    · exact Finset.mem_range.mpr (hG _ hm').1
    · exact Finset.mem_range.mpr (hG _ hm').2
    · simp [h2, rootCl, root]
  · rw [rootRec_S_fst]; exact (List.nodup_range).filter _
  · obtain ⟨hpm, hu, hv, hl, -⟩ := (Finset.mem_filter.mp hp).2
    rw [rootRec_S_fst, List.mem_filter, List.mem_range, decide_eq_true_eq]
    refine ⟨by rw [← hmG]; exact hpm, fun he => hl ?_⟩
    refine (Cl.lconn_iff hT hG (fun a _ v hv _ => Finset.mem_range.mpr hv) (fun v hv => hv) hθ hu hv).mpr
      he

end MinCostFlow.LowStretch
