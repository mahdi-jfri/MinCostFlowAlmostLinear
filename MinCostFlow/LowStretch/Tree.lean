module

public import MinCostFlow.LowStretch.Inv

/-!
# A run gives a tree

The list of pairs that a run returns has `|X| - 1` different pairs, each with both ends in `X`
(Claim 11 of [AN19]). The trees of the children lie in disjoint pieces, so they share no pair.
A portal joins its petal to a later piece, so it lies in no piece, and two portals are different
because the inner end of the earlier one lies in neither end of the later one.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

variable {G : PG} {P : Par}

namespace Cl

variable {c : Cl} {D : Dec}

theorem portal_joins (hD : c.DecOk G P D) {k : ℕ} (hk : k < D.ps.length) :
    G.Joins (D.portal k) (D.xc G k) (D.yc G k) :=
  (petalOk hD hk).2.1.joins (petalOk hD hk).2.2.1

theorem yc_not_mem_W (hD : c.DecOk G P D) {k : ℕ} (hk : k < D.ps.length) :
    D.yc G k ∉ c.W G D k := by
  have := yc_mem hD hk
  rw [Z_succ] at this
  exact (Finset.mem_sdiff.mp this).2

/-- Two pieces that share a vertex are the same piece. -/
theorem raw_eq_of_mem {j k : ℕ} (hj : j < D.nch) (hk : k < D.nch) {z : ℕ}
    (hzj : z ∈ (c.raw G D j).X) (hzk : z ∈ (c.raw G D k).X) : j = k := by
  rcases lt_trichotomy j k with h | h | h
  · exact (raw_disj hk h hzj hzk).elim
  · exact h
  · exact (raw_disj hj h hzk hzj).elim

theorem portal_inj (hD : c.DecOk G P D) {j k : ℕ} (hj : j < D.ps.length) (hk : k < D.ps.length)
    (he : D.portal j = D.portal k) : j = k := by
  by_contra hne
  wlog hjk : j < k generalizing j k
  · exact this hk hj he.symm (Ne.symm hne) (by omega)
  have h1 := portal_joins hD hj
  have h2 := portal_joins hD hk
  rw [he] at h1
  have hx : D.xc G j ∈ c.W G D j := xc_mem hD hj
  rcases h1.end_eq h2 with h | h
  · exact W_disj hjk hx (h ▸ xc_mem hD hk)
  · have hy := yc_mem hD hk
    rw [← h] at hy
    have := Z_antitone (c := c) (G := G) D (show j + 1 ≤ k + 1 by omega) hy
    rw [Z_succ] at this
    exact (Finset.mem_sdiff.mp this).2 hx

end Cl

theorem length_flatMap_range (Ts : ℕ → List ℕ) (n : ℕ) :
    ((List.range n).flatMap Ts).length = ∑ k ∈ Finset.range n, (Ts k).length := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, List.flatMap_append, Finset.sum_range_succ, ih]

/-- The tree of a run: its pairs have both ends in `X`, are different, and there are `|X| - 1` of
them. -/
theorem Run.tree (hGo : G.Ok) (hB : 1 ≤ P.B) {c : Cl} {T : List ℕ} (h : Run G P c T)
    (hc : c.Inv G P) :
    (∀ p ∈ T, p < G.m ∧ G.pu p ∈ c.X ∧ G.pv p ∈ c.X) ∧ T.Nodup ∧ T.length + 1 = c.X.card := by
  induction h with
  | @leaf c hX =>
    refine ⟨by simp, List.nodup_nil, ?_⟩
    have := Finset.card_pos.mpr ⟨_, hc.good.conn.1⟩
    simp; omega
  | @node c D cs Ts hX hD hn hr ih =>
    have hΔ := hc.Δ_pos hB hX
    have hinv : ∀ k < D.nch, (cs k).Inv G P := fun k hk =>
      Cl.child_inv hGo hB hc hX hD hk (hn k hk)
    have ih' := fun k hk => ih k hk (hinv k hk)
    have hXk : ∀ k < D.nch, (cs k).X = (c.raw G D k).X := fun k hk => (hn k hk).X_eq
    have hlen : D.ps.length + 1 = D.nch := rfl
    -- the pairs of the children lie in their pieces
    have hin : ∀ k < D.nch, ∀ p ∈ Ts k, p < G.m ∧ G.pu p ∈ (c.raw G D k).X ∧
        G.pv p ∈ (c.raw G D k).X := fun k hk p hp => by
      rw [← hXk k hk]; exact (ih' k hk).1 p hp
    have hport : ∀ p ∈ D.portals, ∃ k < D.ps.length, D.portal k = p := by
      intro p hp
      unfold Cl.Dec.portals at hp
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
      exact ⟨k, List.mem_range.mp hk, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨k, hk, hpk⟩ := List.mem_flatMap.mp hp
        have hk := List.mem_range.mp hk
        obtain ⟨h1, h2, h3⟩ := hin k hk p hpk
        exact ⟨h1, Cl.raw_X_subset k h2, Cl.raw_X_subset k h3⟩
      · obtain ⟨k, hk, rfl⟩ := hport p hp
        have hj := Cl.portal_joins hD hk
        have hx := Cl.W_subset_X k (Cl.xc_mem hD hk)
        have hy := Cl.Z_subset_X D _ (Cl.yc_mem hD hk)
        refine ⟨hj.1, ?_, ?_⟩ <;> rcases hj.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all
    · rw [List.nodup_append]
      refine ⟨?_, ?_, ?_⟩
      · rw [List.nodup_flatMap]
        refine ⟨fun k hk => (ih' k (List.mem_range.mp hk)).2.1, ?_⟩
        refine List.Pairwise.imp_of_mem ?_ (List.pairwise_lt_range (n := D.nch))
        intro j k hj hk hjk
        rw [Function.onFun, List.disjoint_left]
        intro p hpj hpk
        have hj' := List.mem_range.mp hj
        have hk' := List.mem_range.mp hk
        have := Cl.raw_eq_of_mem hj' hk' (hin j hj' p hpj).2.1 (hin k hk' p hpk).2.1
        omega
      · unfold Cl.Dec.portals
        refine List.Nodup.map_on ?_ List.nodup_range
        intro j hj k hk he
        exact Cl.portal_inj hD (List.mem_range.mp hj) (List.mem_range.mp hk) he
      · intro p hp1 q hp2 hpq
        subst hpq
        obtain ⟨j, hj, hpj⟩ := List.mem_flatMap.mp hp1
        have hj := List.mem_range.mp hj
        obtain ⟨k, hk, rfl⟩ := hport p hp2
        obtain ⟨-, hu, hv⟩ := hin j hj _ hpj
        have hjn := Cl.portal_joins hD hk
        have hx : D.xc G k ∈ (c.raw G D j).X := by
          rcases hjn.2 with ⟨h1, -⟩ | ⟨-, h1⟩ <;> rw [← h1] <;> assumption
        have hy : D.yc G k ∈ (c.raw G D j).X := by
          rcases hjn.2 with ⟨-, h1⟩ | ⟨h1, -⟩ <;> rw [← h1] <;> assumption
        have e := Cl.raw_eq_of_mem hj (show k + 1 < D.nch by omega) hx (Cl.xc_mem hD hk)
        subst e
        exact Cl.yc_not_mem_W hD hk hy
    · rw [List.length_append, length_flatMap_range]
      have hs := Cl.sum_card_raw (c := c) (G := G) (D := D)
      have e : ∑ k ∈ Finset.range D.nch, (c.raw G D k).X.card =
          ∑ k ∈ Finset.range D.nch, ((Ts k).length + 1) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [← hXk k (Finset.mem_range.mp hk)]
        exact ((ih' k (Finset.mem_range.mp hk)).2.2).symm
      rw [e, Finset.sum_add_distrib] at hs
      simp only [Finset.sum_const, Finset.card_range] at hs
      have h1 : D.nch • 1 = D.nch := by simp
      rw [h1] at hs
      unfold Cl.Dec.portals
      rw [List.length_map, List.length_range]
      omega

end MinCostFlow.LowStretch
