module

public import MinCostFlow.HierPaths.BuildCall
public import MinCostFlow.HierPaths.Substitute
public import MinCostFlow.HierPaths.BuildErase
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Sibling connectors at one group

Sibling connectors: at a group `X` with host `G[X]`, for every two children `Y = ch a` and
`Z = ch b` with `a < b`, make one full-routing call (`lemma1Route`, see `lemma_1`) from `Y` to `Z`. Its
matching, each pair with the walk that the embedding gives it, is the list of *connectors* of the
pair `(a, b)` (`siblingConns`).

Main results:
* `siblingConns_perfect`: since the children have equal size and the call has deficit `0`, the
  matching is perfect: its first ends are exactly `Y`, its second ends exactly `Z`, each once.
* `siblingConns_walk`: every connector walk is an edge walk of `G` between the two ends of its pair,
  inside `X`, with at most `d_X = routePathLen Δ b̂ L` edges.
* `occLoad_allConns_le`: the walks of all pairs together use each host edge at most
  `k² · d_X · R_X` times, where `R_X = routeCong Δ b̂ L`; and at most `k² · R_X` times when every
  connector walk repeats no edge (`occLoad_allConns_le_of_nodup`).

The router's interface (`RouteMatchedSpec`) bounds the congestion by the number of walks through
an edge, not by occurrences, and a walk of the router may repeat an edge. So each connector walk
is shortcut to a walk that repeats no edge (`erase`, `BuildErase.lean`). Then a walk through an
edge uses it once, and the load is `k² R_X` (`occLoad_allConns_le_cong`).
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- The pairs `(a, b)` with `a < b < k`. -/
def pairsBelow (k : ℕ) : List (ℕ × ℕ) :=
  (List.range k).flatMap fun b => (List.range b).map fun a => (a, b)

/-- The connectors of a matched outcome: each edge of the flattened matching with its walk. -/
def connOf (E : List (ℕ × ℕ)) : RouteResult → List ((ℕ × ℕ) × List ℕ)
  | .matched M emb => (List.range M.flatten.length).map fun i =>
      (edgeAt M.flatten i, erase E (edgeAt M.flatten i).1 (emb i))
  | .cut _ => []

/-- The connectors of the pair of children `(a, b)`: one full-routing call from `ch a` to
`ch b`. -/
def siblingConns (route : RouterFn) (G : Graph) (X : Finset ℕ) (Δ L : ℕ) (ch : ℕ → Finset ℕ)
    (a b : ℕ) : List ((ℕ × ℕ) × List ℕ) :=
  connOf G.edges (lemma1Route route G X [(ch a, ch b)] Δ L).1

/-- All connectors of the group, as a family of walks with their start terminals. -/
def allConns (route : RouterFn) (G : Graph) (X : Finset ℕ) (Δ L : ℕ) (ch : ℕ → Finset ℕ)
    (k : ℕ) : List (ℕ × List ℕ) :=
  (pairsBelow k).flatMap fun p => (siblingConns route G X Δ L ch p.1 p.2).map fun c => (c.1.1, c.2)

/-- The router's preconditions on the host alone. -/
def HostPre (G : Graph) (X : Finset ℕ) (Δ L : ℕ) : Prop :=
  X ⊆ Finset.range G.n ∧ (∀ e ∈ G.inside X, e.1 ≠ e.2) ∧ 1 ≤ Δ ∧
    (∀ v ∈ X, G.degIn X v ≤ Δ) ∧ 1 ≤ L ∧ X.card < 2 ^ L

/-- `k` children of `X` of equal size `s ≥ 1`, pairwise disjoint. -/
def IsChildren (X : Finset ℕ) (ch : ℕ → Finset ℕ) (k s : ℕ) : Prop :=
  1 ≤ s ∧ (∀ c < k, ch c ⊆ X ∧ (ch c).card = s) ∧
    ∀ c < k, ∀ c' < k, c ≠ c' → Disjoint (ch c) (ch c')

end MinCostFlow.HierPaths

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- Listing the entries of a list by index gives the list back. -/
theorem map_range_getD {α : Type*} (l : List α) (d : α) :
    (List.range l.length).map (fun i => l.getD i d) = l := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getElem?_eq_getElem h2]

/-- The router's preconditions for the single pair `(ch a, ch b)`. -/
theorem routerPre_pair {G : Graph} {X : Finset ℕ} {Δ L : ℕ} (hH : HostPre G X Δ L)
    {ch : ℕ → Finset ℕ} {k s : ℕ} (hch : IsChildren X ch k s) {a b : ℕ} (ha : a < k) (hb : b < k)
    (hab : a ≠ b) : RouterPre G X [(ch a, ch b)] Δ L := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hH
  obtain ⟨_, hsz, hd⟩ := hch
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, ?_⟩
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    exact ⟨(hsz a ha).1, (hsz b hb).1, by rw [(hsz a ha).2, (hsz b hb).2]⟩
  · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.pairwise_cons,
      List.mem_singleton, forall_eq]
    exact ⟨hd a ha b hb hab, by simp⟩

/-- The facts of one connector call, from `call_facts`. -/
theorem pair_call {route : RouterFn} {routeCost : RouterCostFn}
    (hrouter : IsMatchingPlayer route routeCost) {G : Graph} {X : Finset ℕ} {Δ L : ℕ}
    (hH : HostPre G X Δ L) {ch : ℕ → Finset ℕ} {k s : ℕ} (hch : IsChildren X ch k s)
    {β : ℝ} (hβ : 0 < β) (hexp : G.IsExpansionExpanderOn X β) {bh : ℕ}
    (hbh : max 2 (2 / β) ≤ (bh : ℝ)) {a b : ℕ} (ha : a < k) (hb : b < k) (hab : a ≠ b) :
    ∃ M₀ emb, siblingConns route G X Δ L ch a b =
        (List.range M₀.length).map (fun i => (edgeAt M₀ i, emb i)) ∧
      (∀ e ∈ M₀, e.1 ∈ ch a ∧ e.2 ∈ ch b) ∧ (M₀.map Prod.fst).Nodup ∧
      (M₀.map Prod.snd).Nodup ∧ M₀.length = s ∧
      IsEmbeddingOn (Graph.mk G.n M₀) G X emb ∧
      (∀ j < M₀.length, (emb j).length ≤ routePathLen Δ bh L) ∧
      (∀ i < G.m, congestion (Graph.mk G.n M₀) emb i ≤ routeCong Δ bh L) ∧
      (∀ j < M₀.length, (emb j).Nodup) := by
  obtain ⟨C, hC⟩ := hrouter.cost_bound
  have hpre := routerPre_pair hH hch ha hb hab
  obtain ⟨h1, h2, h3, h4, h5, h6, hv⟩ := hpre
  have hC' : ∀ b', 2 ≤ b' → routeCost G X [(ch a, ch b)] Δ L b' 0 ≤
      routeBound C G X [(ch a, ch b)] Δ L b' :=
    fun b' hb' => hC G X _ Δ L b' 0 h1 h2 h3 h4 h5 h6 hb' hv
  obtain ⟨M, emb, b', hr, hs, hfull, _, hemb, hlen, hcong, _⟩ :=
    call_facts hrouter hC' ⟨h1, h2, h3, h4, h5, h6, hv⟩ (by simp) hβ hexp hbh
  have hM1 : M.length = 1 := hs.1
  obtain ⟨M₀, rfl⟩ : ∃ M₀, M = [M₀] := by
    match M, hM1 with
    | [M₀], _ => exact ⟨M₀, rfl⟩
  have hflat : [M₀].flatten = M₀ := by simp
  have hi := hs.2.1 0 (by simp)
  simp only [List.getD_cons_zero, List.getElem_cons_zero] at hi
  have hf := hfull 0 (by simp)
  simp only [List.getD_cons_zero, List.getElem_cons_zero] at hf
  rw [hflat] at hemb hlen hcong
  -- the walks, shortcut to walks that repeat no edge
  set emb' : ℕ → List ℕ := fun j => erase G.edges (edgeAt M₀ j).1 (emb j)
  have hin : ∀ j < M₀.length, insideB X (edgeAt (Graph.mk G.n M₀).edges j) = true := by
    intro j hj
    have hmem : edgeAt M₀ j ∈ M₀ := by
      unfold edgeAt; rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
    have h := hi.1 _ hmem
    have hsz := hch.2.1
    simp [insideB, (hsz a ha).1 h.1, (hsz b hb).1 h.2]
  have hsp : ∀ j < M₀.length, IsEdgeWalk G.edges (edgeAt M₀ j).1 (edgeAt M₀ j).2 (emb' j) ∧
      (emb' j).Sublist (emb j) ∧ (emb' j).Nodup := by
    intro j hj
    obtain ⟨h1, h2, _, h4⟩ := erase_spec _ _ _ _ le_rfl (hemb j hj (hin j hj)).1
    exact ⟨h1, h2, h4⟩
  refine ⟨M₀, emb', ?_, hi.1, hi.2.1, hi.2.2, ?_, ?_, ?_, ?_, fun j hj => (hsp j hj).2.2⟩
  · unfold siblingConns
    rw [hr]
    simp only [connOf, hflat, emb']
  · rw [hf, (IsChildren.card hch ha)]
  · intro j hj hin'
    exact ⟨(hsp j hj).1, fun i' hi' => (hemb j hj hin').2 i' ((hsp j hj).2.1.subset hi')⟩
  · exact fun j hj => (hsp j hj).2.1.length_le.trans (hlen j hj)
  · intro i hi'
    refine le_trans ?_ (hcong i hi')
    unfold congestion
    apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    exact ⟨hj.1, (hsp j hj.1).2.1.subset hj.2⟩
where
  IsChildren.card {X : Finset ℕ} {ch : ℕ → Finset ℕ} {k s : ℕ} (h : IsChildren X ch k s) {c : ℕ}
      (hc : c < k) : (ch c).card = s := (h.2.1 c hc).2

/-- **Connectors, perfect matching.** The first ends of the connectors of `(a, b)` are exactly the
members of `ch a`, each once, and their second ends are exactly the members of `ch b`, each
once. -/
theorem siblingConns_perfect {route : RouterFn} {routeCost : RouterCostFn}
    (hrouter : IsMatchingPlayer route routeCost) {G : Graph} {X : Finset ℕ} {Δ L : ℕ}
    (hH : HostPre G X Δ L) {ch : ℕ → Finset ℕ} {k s : ℕ} (hch : IsChildren X ch k s)
    {β : ℝ} (hβ : 0 < β) (hexp : G.IsExpansionExpanderOn X β) {bh : ℕ}
    (hbh : max 2 (2 / β) ≤ (bh : ℝ)) {a b : ℕ} (ha : a < k) (hb : b < k) (hab : a ≠ b) :
    let cs := siblingConns route G X Δ L ch a b
    cs.length = s ∧ (cs.map fun c => c.1.1).Nodup ∧ (cs.map fun c => c.1.1).toFinset = ch a ∧
      (cs.map fun c => c.1.2).Nodup ∧ (cs.map fun c => c.1.2).toFinset = ch b := by
  obtain ⟨M₀, emb, heq, hends, hnd1, hnd2, hlen, -⟩ :=
    pair_call hrouter hH hch hβ hexp hbh ha hb hab
  have hfst : ((List.range M₀.length).map (fun i => (edgeAt M₀ i, emb i))).map
      (fun c => c.1.1) = M₀.map Prod.fst := by
    rw [List.map_map]
    conv_rhs => rw [← map_range_getD M₀ (0, 0)]
    rw [List.map_map]
    rfl
  have hsnd : ((List.range M₀.length).map (fun i => (edgeAt M₀ i, emb i))).map
      (fun c => c.1.2) = M₀.map Prod.snd := by
    rw [List.map_map]
    conv_rhs => rw [← map_range_getD M₀ (0, 0)]
    rw [List.map_map]
    rfl
  have hsz := hch.2.1
  simp only
  rw [heq, hfst, hsnd]
  refine ⟨by simp [hlen], hnd1, ?_, hnd2, ?_⟩
  · apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hy)
      exact (hends e he).1
    · rw [List.toFinset_card_of_nodup hnd1, List.length_map, hlen, (hsz a ha).2]
  · apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hy)
      exact (hends e he).2
    · rw [List.toFinset_card_of_nodup hnd2, List.length_map, hlen, (hsz b hb).2]

/-- **Connectors, walks.** Every connector walk of `(a, b)` is an edge walk of `G` between the two
ends of its pair, its edges lie inside `X`, and it has at most `routePathLen Δ b̂ L` edges. -/
theorem siblingConns_walk {route : RouterFn} {routeCost : RouterCostFn}
    (hrouter : IsMatchingPlayer route routeCost) {G : Graph} {X : Finset ℕ} {Δ L : ℕ}
    (hH : HostPre G X Δ L) {ch : ℕ → Finset ℕ} {k s : ℕ} (hch : IsChildren X ch k s)
    {β : ℝ} (hβ : 0 < β) (hexp : G.IsExpansionExpanderOn X β) {bh : ℕ}
    (hbh : max 2 (2 / β) ≤ (bh : ℝ)) {a b : ℕ} (ha : a < k) (hb : b < k) (hab : a ≠ b) :
    ∀ c ∈ siblingConns route G X Δ L ch a b,
      IsEdgeWalk G.edges c.1.1 c.1.2 c.2 ∧ (∀ i ∈ c.2, insideB X (edgeAt G.edges i) = true) ∧
        c.2.length ≤ routePathLen Δ bh L := by
  obtain ⟨M₀, emb, heq, hends, -, -, -, hemb, hlen, -⟩ :=
    pair_call hrouter hH hch hβ hexp hbh ha hb hab
  intro c hc
  rw [heq] at hc
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
  have hj' : j < M₀.length := List.mem_range.mp hj
  have hmem : edgeAt M₀ j ∈ M₀ := by
    unfold edgeAt; rw [List.getD_eq_getElem _ _ hj']; exact List.getElem_mem hj'
  have hin : insideB X (edgeAt (Graph.mk G.n M₀).edges j) = true := by
    have h := hends _ hmem
    have hsz := hch.2.1
    simp [insideB, (hsz a ha).1 h.1, (hsz b hb).1 h.2]
  obtain ⟨hw, hall⟩ := hemb j hj' hin
  exact ⟨hw, hall, hlen j hj'⟩

/-- A count in a list is at most its length, and zero when the entry is absent. -/
private theorem count_le_ite (w : List ℕ) (i : ℕ) :
    w.count i ≤ if i ∈ w then w.length else 0 := by
  split_ifs with h
  · exact List.count_le_length
  · rw [List.count_eq_zero_of_not_mem h]

/-- The occurrences of edge `i` in the connector walks of one pair: at most `d · R`, and at most
`R` when no walk repeats an edge. -/
theorem occLoad_siblingConns_le {route : RouterFn} {routeCost : RouterCostFn}
    (hrouter : IsMatchingPlayer route routeCost) {G : Graph} {X : Finset ℕ} {Δ L : ℕ}
    (hH : HostPre G X Δ L) {ch : ℕ → Finset ℕ} {k s : ℕ} (hch : IsChildren X ch k s)
    {β : ℝ} (hβ : 0 < β) (hexp : G.IsExpansionExpanderOn X β) {bh : ℕ}
    (hbh : max 2 (2 / β) ≤ (bh : ℝ)) {a b : ℕ} (ha : a < k) (hb : b < k) (hab : a ≠ b)
    {i : ℕ} (hi : i < G.m) :
    occLoad ((siblingConns route G X Δ L ch a b).map fun c => (c.1.1, c.2)) i ≤
        routePathLen Δ bh L * routeCong Δ bh L ∧
      ((∀ c ∈ siblingConns route G X Δ L ch a b, c.2.Nodup) →
        occLoad ((siblingConns route G X Δ L ch a b).map fun c => (c.1.1, c.2)) i ≤
          routeCong Δ bh L) := by
  obtain ⟨M₀, emb, heq, -, -, -, -, -, hlen, hcong, -⟩ :=
    pair_call hrouter hH hch hβ hexp hbh ha hb hab
  have hc := hcong i hi
  unfold congestion Graph.m at hc
  simp only at hc
  have hcard : ((List.range M₀.length).filter fun j => decide (i ∈ emb j)).length =
      ((Finset.range M₀.length).filter fun j => i ∈ emb j).card := by
    rw [length_filter_eq_card_range _ _ 0]
    simp only [List.length_range]
    congr 1
    apply Finset.filter_congr
    intro j hj
    rw [List.getD_eq_getElem _ _ (by simpa using hj)]
    simp
  have hocc : occLoad ((siblingConns route G X Δ L ch a b).map fun c => (c.1.1, c.2)) i =
      ((List.range M₀.length).map fun j => (emb j).count i).sum := by
    rw [heq]
    unfold occLoad
    simp [List.map_map, Function.comp_def]
  have hgen : ∀ (l : List ℕ) (d : ℕ), (∀ j ∈ l, (emb j).count i ≤ d) →
      (l.map fun j => (emb j).count i).sum ≤ (l.filter fun j => decide (i ∈ emb j)).length * d := by
    intro l d h
    induction l with
    | nil => simp
    | cons x l ih =>
      have hx := h x List.mem_cons_self
      have ih' := ih fun j hj => h j (List.mem_cons_of_mem _ hj)
      simp only [List.map_cons, List.sum_cons, List.filter_cons]
      by_cases hxi : i ∈ emb x
      · simp only [hxi, decide_true, ite_true, List.length_cons, Nat.succ_mul]
        omega
      · simp only [hxi, decide_false, Bool.false_eq_true, ite_false]
        rw [List.count_eq_zero_of_not_mem hxi]
        omega
  have hfil : ((List.range M₀.length).filter fun j => decide (i ∈ emb j)).length ≤
      routeCong Δ bh L := by rw [hcard]; exact hc
  constructor
  · rw [hocc]
    refine le_trans (hgen _ (routePathLen Δ bh L) fun j hj =>
      le_trans List.count_le_length (hlen j (List.mem_range.mp hj))) ?_
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_left _ hfil
  · intro hnd
    rw [hocc]
    refine le_trans (hgen _ 1 fun j hj => ?_) (by rw [Nat.mul_one]; exact hfil)
    have hmem : (edgeAt M₀ j, emb j) ∈ siblingConns route G X Δ L ch a b := by
      rw [heq]; exact List.mem_map.mpr ⟨j, hj, rfl⟩
    exact List.nodup_iff_count_le_one.mp (hnd _ hmem) i

/-- The load of a concatenated family is the sum of the loads. -/
theorem occLoad_flatMap {α : Type*} (l : List α) (f : α → List (ℕ × List ℕ)) (i : ℕ) :
    occLoad (l.flatMap f) i = (l.map fun x => occLoad (f x) i).sum := by
  induction l with
  | nil => simp [occLoad]
  | cons x l ih =>
    rw [List.flatMap_cons, List.map_cons, List.sum_cons, ← ih]
    simp [occLoad, List.map_append, List.sum_append]

/-- There are at most `k²` pairs `a < b < k`, each with both entries below `k` and different. -/
theorem pairsBelow_spec (k : ℕ) :
    (pairsBelow k).length ≤ k * k ∧ ∀ p ∈ pairsBelow k, p.1 < k ∧ p.2 < k ∧ p.1 < p.2 := by
  constructor
  · unfold pairsBelow
    rw [List.length_flatMap]
    have : ∀ b ∈ List.range k, ((List.range b).map fun a => (a, b)).length ≤ k := by
      intro b hb
      simp only [List.length_map, List.length_range]
      exact (List.mem_range.mp hb).le
    calc ((List.range k).map fun b => ((List.range b).map fun a => (a, b)).length).sum
        ≤ ((List.range k).map fun _ => k).sum := List.sum_le_sum this
      _ = k * k := by simp
  · intro p hp
    simp only [pairsBelow, List.mem_flatMap, List.mem_range, List.mem_map] at hp
    obtain ⟨b, hb, a, ha, rfl⟩ := hp
    exact ⟨by omega, hb, ha⟩

/-- **Connectors, load.** All connector walks of the group together use each host edge at most
`k² · d_X · R_X` times. -/
theorem occLoad_allConns_le {route : RouterFn} {routeCost : RouterCostFn}
    (hrouter : IsMatchingPlayer route routeCost) {G : Graph} {X : Finset ℕ} {Δ L : ℕ}
    (hH : HostPre G X Δ L) {ch : ℕ → Finset ℕ} {k s : ℕ} (hch : IsChildren X ch k s)
    {β : ℝ} (hβ : 0 < β) (hexp : G.IsExpansionExpanderOn X β) {bh : ℕ}
    (hbh : max 2 (2 / β) ≤ (bh : ℝ)) {i : ℕ} (hi : i < G.m) :
    occLoad (allConns route G X Δ L ch k) i ≤
      k * k * (routePathLen Δ bh L * routeCong Δ bh L) := by
  unfold allConns
  rw [occLoad_flatMap]
  obtain ⟨hlen, hp⟩ := pairsBelow_spec k
  calc ((pairsBelow k).map fun p =>
        occLoad ((siblingConns route G X Δ L ch p.1 p.2).map fun c => (c.1.1, c.2)) i).sum
      ≤ ((pairsBelow k).map fun _ => routePathLen Δ bh L * routeCong Δ bh L).sum := by
        apply List.sum_le_sum
        intro p hpm
        obtain ⟨h1, h2, h3⟩ := hp p hpm
        exact (occLoad_siblingConns_le hrouter hH hch hβ hexp hbh h1 h2 (by omega) hi).1
    _ = (pairsBelow k).length * (routePathLen Δ bh L * routeCong Δ bh L) := by simp
    _ ≤ k * k * (routePathLen Δ bh L * routeCong Δ bh L) := Nat.mul_le_mul_right _ hlen

/-- **Connectors, load for walks without repeated edges.** If no connector walk repeats an edge, all
connector walks of the group together use each host edge at most `k² · R_X` times. -/
theorem occLoad_allConns_le_of_nodup {route : RouterFn} {routeCost : RouterCostFn}
    (hrouter : IsMatchingPlayer route routeCost) {G : Graph} {X : Finset ℕ} {Δ L : ℕ}
    (hH : HostPre G X Δ L) {ch : ℕ → Finset ℕ} {k s : ℕ} (hch : IsChildren X ch k s)
    {β : ℝ} (hβ : 0 < β) (hexp : G.IsExpansionExpanderOn X β) {bh : ℕ}
    (hbh : max 2 (2 / β) ≤ (bh : ℝ))
    (hnd : ∀ p ∈ pairsBelow k, ∀ c ∈ siblingConns route G X Δ L ch p.1 p.2, c.2.Nodup)
    {i : ℕ} (hi : i < G.m) :
    occLoad (allConns route G X Δ L ch k) i ≤ k * k * routeCong Δ bh L := by
  unfold allConns
  rw [occLoad_flatMap]
  obtain ⟨hlen, hp⟩ := pairsBelow_spec k
  calc ((pairsBelow k).map fun p =>
        occLoad ((siblingConns route G X Δ L ch p.1 p.2).map fun c => (c.1.1, c.2)) i).sum
      ≤ ((pairsBelow k).map fun _ => routeCong Δ bh L).sum := by
        apply List.sum_le_sum
        intro p hpm
        obtain ⟨h1, h2, h3⟩ := hp p hpm
        exact (occLoad_siblingConns_le hrouter hH hch hβ hexp hbh h1 h2 (by omega) hi).2
          (hnd p hpm)
    _ = (pairsBelow k).length * routeCong Δ bh L := by simp
    _ ≤ k * k * routeCong Δ bh L := Nat.mul_le_mul_right _ hlen

/-- The connector walks repeat no edge: they are shortcut by `erase`. -/
theorem siblingConns_nodup {route : RouterFn} {routeCost : RouterCostFn}
    (hrouter : IsMatchingPlayer route routeCost) {G : Graph} {X : Finset ℕ} {Δ L : ℕ}
    (hH : HostPre G X Δ L) {ch : ℕ → Finset ℕ} {k s : ℕ} (hch : IsChildren X ch k s)
    {β : ℝ} (hβ : 0 < β) (hexp : G.IsExpansionExpanderOn X β) {bh : ℕ}
    (hbh : max 2 (2 / β) ≤ (bh : ℝ)) {a b : ℕ} (ha : a < k) (hb : b < k) (hab : a ≠ b) :
    ∀ c ∈ siblingConns route G X Δ L ch a b, c.2.Nodup := by
  obtain ⟨M₀, emb, heq, -, -, -, -, -, -, -, hnd⟩ :=
    pair_call hrouter hH hch hβ hexp hbh ha hb hab
  intro c hc
  rw [heq] at hc
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
  exact hnd j (List.mem_range.mp hj)

/-- **Connectors, load of one pair.** The connector walks of one pair use each host edge at most
`R_X` times. -/
theorem occLoad_siblingConns_le_cong {route : RouterFn} {routeCost : RouterCostFn}
    (hrouter : IsMatchingPlayer route routeCost) {G : Graph} {X : Finset ℕ} {Δ L : ℕ}
    (hH : HostPre G X Δ L) {ch : ℕ → Finset ℕ} {k s : ℕ} (hch : IsChildren X ch k s)
    {β : ℝ} (hβ : 0 < β) (hexp : G.IsExpansionExpanderOn X β) {bh : ℕ}
    (hbh : max 2 (2 / β) ≤ (bh : ℝ)) {a b : ℕ} (ha : a < k) (hb : b < k) (hab : a ≠ b)
    {i : ℕ} (hi : i < G.m) :
    occLoad ((siblingConns route G X Δ L ch a b).map fun c => (c.1.1, c.2)) i ≤
      routeCong Δ bh L :=
  (occLoad_siblingConns_le hrouter hH hch hβ hexp hbh ha hb hab hi).2
    (siblingConns_nodup hrouter hH hch hβ hexp hbh ha hb hab)

/-- **Connectors, load with the congestion bound.** All connector walks of the group together use each host edge at most
`k² · R_X` times. -/
theorem occLoad_allConns_le_cong {route : RouterFn} {routeCost : RouterCostFn}
    (hrouter : IsMatchingPlayer route routeCost) {G : Graph} {X : Finset ℕ} {Δ L : ℕ}
    (hH : HostPre G X Δ L) {ch : ℕ → Finset ℕ} {k s : ℕ} (hch : IsChildren X ch k s)
    {β : ℝ} (hβ : 0 < β) (hexp : G.IsExpansionExpanderOn X β) {bh : ℕ}
    (hbh : max 2 (2 / β) ≤ (bh : ℝ)) {i : ℕ} (hi : i < G.m) :
    occLoad (allConns route G X Δ L ch k) i ≤ k * k * routeCong Δ bh L := by
  obtain ⟨_, hp⟩ := pairsBelow_spec k
  refine occLoad_allConns_le_of_nodup hrouter hH hch hβ hexp hbh (fun p hpm => ?_) hi
  obtain ⟨h1, h2, h3⟩ := hp p hpm
  exact siblingConns_nodup hrouter hH hch hβ hexp hbh h1 h2 (by omega)

end MinCostFlow.HierPaths
