module

public import MinCostFlow.LowStretch.CountVisTree
public import MinCostFlow.LowStretch.Volume3
public import MinCostFlow.LowStretch.Work

/-!
# The count with the splits of the resets

`Counted a c N` pays each cluster `a (|act| + 1)`. A reset of a child also does work for the merge
nodes it splits: it relabels the leaves of their light children and looks at the pairs grouped
at them, which become visible (`KT.visW`). These pairs need not be active, so `Counted` cannot
pay for them. `CountedV` adds `a · visW` for each child. Its node step also asks that each raw
child be a union of `θ`-nodes of the cluster (`KT.Sat`), as the design keeps it.

Each merge node is split at most once along the whole run. The nodes that a cluster `c` may
still split are the merge nodes of weight below `c.θ` above a vertex of `c` (`KT.hid`). Splitting
moves a node out of this set, and the sets of the children are disjoint because the children are
disjoint unions of `θ`-nodes (`sum_vis_le`). So a `CountedV` count is a `Counted` count plus at
most `a` times the total `KT.visTot` of all splits (`CountedV.counted`), which is at most
`a (n (log n + 1) + m + N)` (`CountedV.le_visTot`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open Cl

variable {G : PG} {P : Par}

/-- `CountedV T a c N`: the run below `c` costs at most `N`, when each cluster costs `a` times one
plus its number of active pairs, and each reset of a child costs `a` times the work of its
splits. -/
inductive CountedV (G : PG) (P : Par) (T : KT) (a : ℕ) : Cl → ℕ → Prop
  | leaf {c : Cl} {N : ℕ} : c.X.card ≤ 1 → N ≤ a → CountedV G P T a c N
  | node {c : Cl} {N : ℕ} (D : Dec) (cs : ℕ → Cl) (Ns : ℕ → ℕ) :
      2 ≤ c.X.card → c.DecOk G P D → (∀ k < D.nch, Next G P (c.raw G D k) (cs k)) →
      (∀ k < D.nch, T.Sat G c.θ (c.raw G D k).X) →
      (∀ k < D.nch, CountedV G P T a (cs k) (Ns k)) →
      N ≤ a * ((c.act G P).card + 1) +
        ∑ k ∈ Finset.range D.nch, (a * T.visW G (c.raw G D k) (cs k).θ + Ns k) →
      CountedV G P T a c N

namespace KT

variable {T : KT}

open Classical in
/-- The merge nodes that the cluster `c` may still split. -/
noncomputable def hid (T : KT) (G : PG) (c : Cl) : Finset ℕ :=
  (T.merges G).filter fun u => T.mw u < c.θ ∧ ∃ v ∈ c.X, T.Under v u

/-- Their total split work. -/
noncomputable def hidW (T : KT) (G : PG) (c : Cl) : ℕ := ∑ u ∈ T.hid G c, T.splitW G u

theorem hidW_le_visTot (c : Cl) : T.hidW G c ≤ T.visTot G := by
  classical
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

end KT

namespace Cl

variable {T : KT} {c : Cl} {D : Dec} {cs : ℕ → Cl}

/-- What a node of the sets of child `k` satisfies. -/
def InChild (T : KT) (G : PG) (c r : Cl) (u : ℕ) : Prop :=
  u ∈ T.merges G ∧ T.mw u < c.θ ∧ ∃ v ∈ r.X, T.Under v u

theorem inChild_disj (hT : T.Ok G) (hsub : c.X ⊆ Finset.range G.n) (hθ : 1 ≤ c.θ)
    (hsat : ∀ k < D.nch, T.Sat G c.θ (c.raw G D k).X) {j k u : ℕ} (hk : k < D.nch) (hjk : j < k)
    (hj : InChild T G c (c.raw G D j) u) (hk' : InChild T G c (c.raw G D k) u) : False := by
  obtain ⟨-, hmw, vk, hvk, hvku⟩ := hk'
  obtain ⟨-, -, vj, hvj, hvju⟩ := hj
  have hvkn : vk < G.n := Finset.mem_range.mp (hsub (raw_X_subset k hvk))
  have hvjn : vj < G.n := Finset.mem_range.mp (hsub (raw_X_subset j hvj))
  have htop := KT.under_top hT hvkn hθ hvku hmw
  have := hsat k hk vk hvk vj hvjn (hvju.trans htop)
  exact raw_disj hk hjk hvj this

/-- **The splits of the children** and what the children may still split fit in what the
cluster may still split. -/
theorem sum_vis_le (hT : T.Ok G) (hsub : c.X ⊆ Finset.range G.n) (hθ : 1 ≤ c.θ)
    (hn : ∀ k < D.nch, Next G P (c.raw G D k) (cs k))
    (hsat : ∀ k < D.nch, T.Sat G c.θ (c.raw G D k).X) :
    ∑ k ∈ Finset.range D.nch, (T.visW G (c.raw G D k) (cs k).θ + T.hidW G (cs k)) ≤
      T.hidW G c := by
  classical
  set A : ℕ → Finset ℕ := fun k => T.splitSet G (c.raw G D k) (cs k).θ ∪ T.hid G (cs k) with hA
  have hin : ∀ k < D.nch, ∀ u ∈ A k, InChild T G c (c.raw G D k) u := by
    intro k hk u hu
    have hθk := (hn k hk).θ_le
    rw [raw_θ] at hθk
    rcases Finset.mem_union.mp hu with hu | hu
    · simp only [KT.splitSet, Finset.mem_filter, Finset.mem_range] at hu
      obtain ⟨huN, hun, -, v, hv, hvu, hut⟩ := hu
      rw [raw_θ] at hut
      have hvn : v < G.n := Finset.mem_range.mp (hsub (raw_X_subset k hv))
      have ht := KT.isTop_top hT hvn hθ
      have := hut.mw_le hT huN
      have := ht.2.1
      refine ⟨by simp [KT.merges, huN, hun], by omega, v, hv, hvu⟩
    · simp only [KT.hid, Finset.mem_filter] at hu
      obtain ⟨hm, hmw, v, hv, hvu⟩ := hu
      rw [(hn k hk).X_eq] at hv
      exact ⟨hm, by omega, v, hv, hvu⟩
  have hsplit : ∀ k < D.nch, T.visW G (c.raw G D k) (cs k).θ + T.hidW G (cs k) =
      ∑ u ∈ A k, T.splitW G u := by
    intro k _
    rw [KT.visW_eq, KT.hidW, hA, Finset.sum_union]
    rw [Finset.disjoint_left]
    intro u h1 h2
    simp only [KT.splitSet, Finset.mem_filter] at h1
    simp only [KT.hid, Finset.mem_filter] at h2
    omega
  rw [Finset.sum_congr rfl fun k hk => hsplit k (Finset.mem_range.mp hk)]
  rw [← Finset.sum_biUnion]
  · refine Finset.sum_le_sum_of_subset fun u hu => ?_
    obtain ⟨k, hk, hu⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨hm, hmw, v, hv, hvu⟩ := hin k (Finset.mem_range.mp hk) u hu
    simp only [KT.hid, Finset.mem_filter]
    exact ⟨hm, hmw, v, raw_X_subset k hv, hvu⟩
  · intro j hj k hk hjk
    simp only [Finset.coe_range, Set.mem_Iio] at hj hk
    rw [Function.onFun, Finset.disjoint_left]
    intro u h1 h2
    rcases Nat.lt_or_gt_of_ne hjk with h | h
    · exact inChild_disj hT hsub hθ hsat hk h (hin j hj u h1) (hin k hk u h2)
    · exact inChild_disj hT hsub hθ hsat hj h (hin k hk u h2) (hin j hj u h1)

end Cl

/-- **A `CountedV` count is a `Counted` count plus `a` times what `c` may still split.** -/
theorem CountedV.counted (hGo : G.Ok) (hB : 1 ≤ P.B) {T : KT} (hT : T.Ok G) {a : ℕ} {c : Cl}
    {N : ℕ} (h : CountedV G P T a c N) (hc : c.Inv G P) :
    ∃ N0, Counted G P a c N0 ∧ N ≤ N0 + a * T.hidW G c := by
  induction h with
  | @leaf c N hX hN => exact ⟨N, Counted.leaf hX hN, by omega⟩
  | @node c N D cs Ns hX hD hn hsat _ hN ih =>
    have hinv : ∀ k < D.nch, (cs k).Inv G P := fun k hk => child_inv hGo hB hc hX hD hk (hn k hk)
    have hex : ∀ k, ∃ M, k < D.nch → Counted G P a (cs k) M ∧ Ns k ≤ M + a * T.hidW G (cs k) := by
      intro k
      by_cases hk : k < D.nch
      · obtain ⟨M, hM⟩ := ih k hk (hinv k hk)
        exact ⟨M, fun _ => hM⟩
      · exact ⟨0, fun h => absurd h hk⟩
    choose M hM using hex
    refine ⟨a * ((c.act G P).card + 1) + ∑ k ∈ Finset.range D.nch, M k,
      Counted.node D cs M hX hD hn (fun k hk => (hM k hk).1) le_rfl, ?_⟩
    have hvis := sum_vis_le hT hc.sub hc.one_le hn hsat
    have hle : ∑ k ∈ Finset.range D.nch, (a * T.visW G (c.raw G D k) (cs k).θ + Ns k) ≤
        ∑ k ∈ Finset.range D.nch, (M k + a * (T.visW G (c.raw G D k) (cs k).θ +
          T.hidW G (cs k))) := by
      refine Finset.sum_le_sum fun k hk => ?_
      have := (hM k (Finset.mem_range.mp hk)).2
      rw [Nat.mul_add]; omega
    have e : ∑ k ∈ Finset.range D.nch, (M k + a * (T.visW G (c.raw G D k) (cs k).θ +
        T.hidW G (cs k))) = ∑ k ∈ Finset.range D.nch, M k + a * ∑ k ∈ Finset.range D.nch,
          (T.visW G (c.raw G D k) (cs k).θ + T.hidW G (cs k)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    have := Nat.mul_le_mul_left a hvis
    omega

/-- **The count with the splits** is a `Counted` count plus at most `a` times the total of all
splits. -/
theorem CountedV.le_visTot (hGo : G.Ok) (hB : 1 ≤ P.B) {T : KT} (hT : T.Ok G)
    (hG : ∀ p < G.m, G.pu p < G.n ∧ G.pv p < G.n) {a : ℕ} {c : Cl} {N : ℕ}
    (h : CountedV G P T a c N) (hc : c.Inv G P) :
    ∃ N0, Counted G P a c N0 ∧ N ≤ N0 + a * (G.n * (Nat.log 2 G.n + 1) + G.m + T.N) := by
  obtain ⟨N0, h0, hN⟩ := h.counted hGo hB hT hc
  refine ⟨N0, h0, hN.trans (Nat.add_le_add_left (Nat.mul_le_mul_left a
    ((KT.hidW_le_visTot c).trans (KT.visTot_le hT hG))) _)⟩

end MinCostFlow.LowStretch
