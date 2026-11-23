module

public import MinCostFlow.LastLevelProgram.FixedPoint
import Mathlib.Data.Nat.Size
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import MinCostFlow.LSF.Walks

/-!
# Properties of the representative graph for Definition 5.8 (pages 19–20)

The chosen edge names preserve endpoint pairs and do not increase lengths.
The number of edges depends only on the endpoint pairs, so changing the
lengths affects neither the round count nor its model cost.
-/

open MinCostFlow.SparseCore MinCostFlow.LSF

public section

namespace MinCostFlow.LastLevelProgram

theorem representative_mem {G : MGraph} {ℓ : ℕ → ℝ} {f : ℕ}
    (hf : f ∈ (representativeGraph G ℓ).E) :
    f ∈ nonLoopEdges G ∧ f = shortestEdge G ℓ (edgePairKey G f) := by
  obtain ⟨_, hp, rfl⟩ := Finset.mem_image.mp hf
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨hm, hk, _⟩ := shortestEdge_spec (ℓ := ℓ) he
  exact ⟨hm, congrArg (shortestEdge G ℓ) hk.symm⟩

/-- At most one representative edge has any given endpoint pair. -/
theorem representativeGraph_edge_eq_of_key {G : MGraph} {ℓ : ℕ → ℝ} {e f : ℕ}
    (he : e ∈ (representativeGraph G ℓ).E) (hf : f ∈ (representativeGraph G ℓ).E)
    (hkey : edgePairKey G e = edgePairKey G f) : e = f :=
  (representative_mem he).2.trans
    ((congrArg (shortestEdge G ℓ) hkey).trans (representative_mem hf).2.symm)

/-- The simple representative graph is a valid subgraph. -/
theorem representativeGraph_subgraph {G : MGraph} (hG : G.IsValid) (ℓ : ℕ → ℝ) :
    G.IsSubgraph (representativeGraph G ℓ) := by
  have he : (representativeGraph G ℓ).E ⊆ G.E :=
    fun _ hf => (Finset.mem_filter.mp (representative_mem hf).1).1
  refine ⟨?_, he, fun _ _ => ⟨rfl, rfl⟩⟩
  intro v hv
  obtain ⟨f, hf, hmem⟩ := Finset.mem_biUnion.mp hv
  have hend := hG f (he hf)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl
  · exact hend.1
  · exact hend.2

/-- The ends of every representative belong to the representative graph. -/
theorem representativeGraph_valid (G : MGraph) (ℓ : ℕ → ℝ) :
    (representativeGraph G ℓ).IsValid := by
  intro e he
  exact ⟨Finset.mem_biUnion.mpr ⟨e, he, by simp [representativeGraph]⟩, Finset.mem_biUnion.mpr ⟨e, he, by simp [representativeGraph]⟩⟩

/-- Every non-loop edge has a representative of at most its own length. -/
theorem representativeGraph_shortest {G : MGraph} {ℓ : ℕ → ℝ} {e : ℕ}
    (he : e ∈ nonLoopEdges G) :
    let f := shortestEdge G ℓ (edgePairKey G e)
    f ∈ (representativeGraph G ℓ).E ∧ edgePairKey G f = edgePairKey G e ∧ ℓ f ≤ ℓ e := by
  obtain ⟨_, hkey, horder⟩ := shortestEdge_spec (ℓ := ℓ) he
  exact ⟨Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ he), hkey,
    horder.elim (fun h => h.le) (fun h => h.1.le)⟩

/-- A shortest class member with the smallest name among ties is the
representative selected by the fixed-point tool. -/
theorem eq_shortestEdge_of_minimal {G : MGraph} {ℓ : ℕ → ℝ} {e : ℕ}
    (he : e ∈ nonLoopEdges G)
    (hmin : ∀ f ∈ nonLoopEdges G, edgePairKey G f = edgePairKey G e →
      ℓ e ≤ ℓ f ∧ (ℓ e = ℓ f → e ≤ f)) :
    e = shortestEdge G ℓ (edgePairKey G e) := by
  let f := shortestEdge G ℓ (edgePairKey G e)
  obtain ⟨hf,hkey,horder⟩ := shortestEdge_spec (ℓ := ℓ) he
  obtain ⟨hle,hname⟩ := hmin f hf hkey
  rcases horder with hlt | ⟨heq,hrev⟩
  · exact False.elim (not_lt_of_ge hle hlt)
  · exact Nat.le_antisymm (hname heq.symm) hrev

/-- Replacing each non-loop edge by its shortest representative keeps
every original connection. A loop contributes a length-zero walk. -/
theorem representativeGraph_connected {G : MGraph} {u v : ℕ}
    (ℓ : ℕ → ℝ) (h : G.Connected u v) :
    (representativeGraph G ℓ).Connected u v := by
  let H := representativeGraph G ℓ
  have edgeConnect (e : ℕ) (he : e ∈ G.E) : H.Connected (G.tail e) (G.head e) := by
    by_cases hloop : G.tail e = G.head e
    · exact ⟨[], hloop ▸ MGraph.IsWalk.nil _⟩
    · have he' : e ∈ nonLoopEdges G := Finset.mem_filter.mpr ⟨he, hloop⟩
      obtain ⟨hf, hkey, _⟩ := representativeGraph_shortest (ℓ := ℓ) he'
      let f := shortestEdge G ℓ (edgePairKey G e)
      change f ∈ H.E at hf
      change edgePairKey G f = edgePairKey G e at hkey
      have hc : H.Connected (G.tail f) (G.head f) := connected_of_edge hf
      have hcKey : H.Connected (edgePairKey G f).1 (edgePairKey G f).2 := by
        rcases le_total (G.tail f) (G.head f) with hle | hle
        · simpa only [edgePairKey, min_eq_left hle, max_eq_right hle] using hc
        · simpa only [edgePairKey, min_eq_right hle, max_eq_left hle] using connected_symm hc
      rw [hkey] at hcKey
      rcases le_total (G.tail e) (G.head e) with hle | hle
      · simpa only [edgePairKey, min_eq_left hle, max_eq_right hle] using hcKey
      · simpa only [edgePairKey, min_eq_right hle, max_eq_left hle] using connected_symm hcKey
  obtain ⟨path, hp⟩ := h
  induction hp with
  | nil => exact ⟨[], .nil _⟩
  | @cons a b x rest he hs _ ih =>
    apply connected_trans _ ih
    rw [← hs]
    rcases x with ⟨e, flip⟩
    cases flip
    · exact connected_symm (edgeConnect e he)
    · exact edgeConnect e he

/-- On a connected input with a non-loop edge, every original vertex
is also a representative vertex. -/
theorem representativeGraph_vertices_eq {G : MGraph} (ℓ : ℕ → ℝ)
    (hG : G.IsValid) (hne : (nonLoopEdges G).Nonempty)
    (hc : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v) :
    (representativeGraph G ℓ).V = G.V := by
  let H := representativeGraph G ℓ
  have hsub := (representativeGraph_subgraph hG ℓ).1
  apply Finset.Subset.antisymm hsub
  intro v hv
  obtain ⟨e,he⟩ := hne
  obtain ⟨hf,_,_⟩ := representativeGraph_shortest (ℓ := ℓ) he
  let f := shortestEdge G ℓ (edgePairKey G e)
  have hu : G.tail f ∈ H.V := (representativeGraph_valid G ℓ f hf).1
  obtain ⟨path,hpath⟩ := representativeGraph_connected ℓ (hc v hv _ (hsub hu))
  cases hpath with
  | nil => exact hu
  | @cons a b x rest he' hs _ =>
    rw [← hs]
    obtain ⟨ht,hh⟩ := representativeGraph_valid G ℓ x.1 he'
    rcases x with ⟨e',flip⟩
    cases flip
    · exact hh
    · exact ht

/-- Each representative edge corresponds to a distinct key among the
original non-loop edges. -/
theorem representativeGraph_m (G : MGraph) (ℓ : ℕ → ℝ) :
    (representativeGraph G ℓ).m = ((nonLoopEdges G).image (edgePairKey G)).card := by
  apply Finset.card_image_of_injOn
  intro p hp q hq heq
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hq
  exact ((shortestEdge_spec (ℓ := ℓ) he).2.1.symm.trans
    (congrArg (edgePairKey G) heq)).trans (shortestEdge_spec (ℓ := ℓ) hf).2.1

/-- The deterministic representative graph has at most one edge per
ordered pair of its vertices. -/
theorem representativeGraph_m_le_sq (G : MGraph) (ℓ : ℕ → ℝ) :
    (representativeGraph G ℓ).m ≤ (representativeGraph G ℓ).n ^ 2 := by
  let H := representativeGraph G ℓ
  have hinj : Set.InjOn (edgePairKey G) (↑H.E : Set ℕ) := by
    intro e he f hf hkey
    exact (representative_mem he).2.trans
      ((congrArg (shortestEdge G ℓ) hkey).trans (representative_mem hf).2.symm)
  have hsubset : H.E.image (edgePairKey G) ⊆ H.V ×ˢ H.V := by
    intro p hp
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨ht, hh⟩ := representativeGraph_valid G ℓ e he
    change G.tail e ∈ H.V at ht
    change G.head e ∈ H.V at hh
    rw [Finset.mem_product]
    rcases le_total (G.tail e) (G.head e) with h | h
    · simpa only [edgePairKey, min_eq_left h, max_eq_right h] using And.intro ht hh
    · simpa only [edgePairKey, min_eq_right h, max_eq_left h] using And.intro hh ht
  calc
    H.m = (H.E.image (edgePairKey G)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (H.V ×ˢ H.V).card := Finset.card_le_card hsubset
    _ = H.n ^ 2 := by rw [Finset.card_product, sq]; rfl

/-- Every representative vertex is incident to a representative edge. -/
theorem representativeGraph_n_le_twice_m (G : MGraph) (ℓ : ℕ → ℝ) :
    (representativeGraph G ℓ).n ≤ 2 * (representativeGraph G ℓ).m := by
  rw [mul_comm]
  exact Finset.card_biUnion_le_card_mul _ _ _ fun _ _ => Finset.card_le_two

/-- A zero representative count is exactly the case where the input has
no non-loop edge. The rebuild uses this count to select its empty branch. -/
theorem representativeGraph_m_eq_zero_iff (G : MGraph) (ℓ : ℕ → ℝ) :
    (representativeGraph G ℓ).m = 0 ↔ ¬ (nonLoopEdges G).Nonempty := by
  rw [representativeGraph_m]
  constructor
  · intro hz hn
    obtain ⟨e,he⟩ := hn
    have hm := Finset.card_pos.mpr
      (show ((nonLoopEdges G).image (edgePairKey G)).Nonempty from
        ⟨edgePairKey G e,Finset.mem_image_of_mem _ he⟩)
    exact (Nat.ne_of_gt hm) hz
  · intro hn
    have he : nonLoopEdges G = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [he]

/-- Every retained edge has two distinct ends in the representative graph. -/
theorem representativeGraph_two_le_n (G : MGraph) (ℓ : ℕ → ℝ)
    (hm : 0 < (representativeGraph G ℓ).m) : 2 ≤ (representativeGraph G ℓ).n := by
  let H := representativeGraph G ℓ
  obtain ⟨e,he⟩ := Finset.card_pos.mp hm
  have hne := (Finset.mem_filter.mp (representative_mem he).1).2
  obtain ⟨ht,hh⟩ := representativeGraph_valid G ℓ e he
  have hsub : ({G.tail e,G.head e} : Finset ℕ) ⊆ H.V := by
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact ht
    · exact hh
  change 2 ≤ H.V.card
  simpa [hne] using Finset.card_le_card hsub

/-- The precision needs at most three times the edge-count bit length, plus
a constant that depends on the LSST bound. -/
theorem representativeGraph_weightPrecision_le (C : ℝ) (G : MGraph) (ℓ : ℕ → ℝ) :
    weightPrecision C (representativeGraph G ℓ) ≤
      (1024 * (⌈max 1 C⌉₊ : ℕ)).size + 3 * ((representativeGraph G ℓ).m + 1).size := by
  let H := representativeGraph G ℓ
  let B : ℕ := 1024 * ⌈max 1 C⌉₊
  let M : ℕ := H.m + 1
  have hn : (H.n : ℝ) ≤ 2 * H.m := by exact_mod_cast representativeGraph_n_le_twice_m G ℓ
  have hlog0 : 0 ≤ Real.log ((H.n : ℝ) + 2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) H.n])
  have hlog : Real.log ((H.n : ℝ) + 2) ≤ 2 * (M : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < H.n + 2 by positivity)
    dsimp [M]
    push_cast
    linarith
  have hC : max 1 C ≤ (⌈max 1 C⌉₊ : ℕ) := Nat.le_ceil _
  have hreal : 2 * roundedScale C H ≤ ((B * M^3 : ℕ) : ℝ) := by
    have hW : lastW C H ≤ ((⌈max 1 C⌉₊ : ℕ) : ℝ) * (2 * (M : ℝ))^2 :=
      mul_le_mul hC (pow_le_pow_left₀ hlog0 hlog 2) (sq_nonneg _) (Nat.cast_nonneg _)
    have hM : (H.m : ℝ) ≤ M := by simp [M]
    have hp := mul_le_mul hW hM (Nat.cast_nonneg H.m) (by positivity)
    refine (mul_le_mul_of_nonneg_left (roundedScale_bounds C H).2 zero_le_two).trans ?_
    dsimp only [lastRho, B]
    push_cast
    nlinarith only [hp]
  have hc : (⌈2 * roundedScale C H⌉₊ : ℕ) ≤ B * M^3 := Nat.ceil_le.mpr hreal
  have hp : B * M^3 < 2 ^ (B.size + 3 * M.size) := by
    rw [pow_add, Nat.mul_comm 3 M.size, pow_mul]
    exact Nat.mul_lt_mul_of_lt_of_le (Nat.lt_size_self B)
      (Nat.pow_le_pow_left (Nat.lt_size_self M).le _) (by positivity)
  rw [weightPrecision_eq_ceil]
  exact Nat.size_le.mpr (hc.trans_lt hp)

/-- A sortable key for a named edge. Endpoint pairs are consecutive
after sorting, and the low digit recovers the original edge name. -/
@[expose] def representativeSortKey (G : MGraph) (vCap eCap e : ℕ) : ℕ :=
  (vCap*(edgePairKey G e).1+(edgePairKey G e).2)*eCap+e

/-- Decode the edge name and both entries of its endpoint key. -/
theorem representativeSortKey_decode (G : MGraph) (vCap eCap e : ℕ)
    (he : e < eCap) (hv : (edgePairKey G e).2 < vCap) :
    representativeSortKey G vCap eCap e % eCap = e ∧
      ((representativeSortKey G vCap eCap e / eCap) / vCap,
        (representativeSortKey G vCap eCap e / eCap) % vCap) = edgePairKey G e := by
  have he' : 0 < eCap := Nat.zero_lt_of_lt he
  have hv' : 0 < vCap := Nat.zero_lt_of_lt hv
  let key := vCap*(edgePairKey G e).1+(edgePairKey G e).2
  have hd : representativeSortKey G vCap eCap e / eCap = key := by
    change (key*eCap+e)/eCap = key
    rw [Nat.mul_comm key eCap,Nat.mul_add_div he',Nat.div_eq_of_lt he,Nat.add_zero]
  constructor
  · change (key*eCap+e)%eCap = e
    rw [Nat.mul_comm key eCap,Nat.mul_add_mod,Nat.mod_eq_of_lt he]
  · rw [hd]
    congr 1
    · dsimp [key]
      rw [Nat.mul_add_div hv',Nat.div_eq_of_lt hv,Nat.add_zero]
      rfl
    · dsimp [key]
      rw [Nat.mul_add_mod,Nat.mod_eq_of_lt hv]
      rfl

/-- A word that holds the product of the two vertex capacities and the
edge capacity can hold every key used by the representative sorter. -/
theorem representativeSortKey_lt (G : MGraph) (vCap eCap e : ℕ)
    (ht : G.tail e < vCap) (hh : G.head e < vCap) (he : e < eCap) :
    representativeSortKey G vCap eCap e < vCap*vCap*eCap := by
  have hhi : (edgePairKey G e).2 < vCap := max_lt ht hh
  have hlo : (edgePairKey G e).1 < vCap := (min_le_left _ _).trans_lt ht
  have hmul := Nat.mul_le_mul_left vCap (Nat.succ_le_of_lt hlo)
  rw [Nat.mul_succ] at hmul
  have hpair : vCap*(edgePairKey G e).1+(edgePairKey G e).2 < vCap*vCap := by omega
  have hwide := Nat.mul_le_mul_right eCap (Nat.succ_le_of_lt hpair)
  rw [Nat.succ_mul] at hwide
  unfold representativeSortKey
  omega

/-- Within a parallel class, the sort key orders edges by name. -/
theorem representativeSortKey_le_iff_of_sameClass {G : MGraph} {vCap eCap e f : ℕ}
    (h : edgePairKey G e = edgePairKey G f) :
    representativeSortKey G vCap eCap e ≤ representativeSortKey G vCap eCap f ↔ e ≤ f := by
  simp only [representativeSortKey, h, Nat.add_le_add_iff_left]

/-- Between two sorted keys from the same endpoint pair, every
valid edge key has that pair. One scan can therefore finish a parallel
class before moving to the next one. -/
theorem representativeSortKey_between {G : MGraph} {vCap eCap a b c : ℕ}
    (ha : a < eCap) (hb : b < eCap) (hc : c < eCap)
    (hav : (edgePairKey G a).2 < vCap) (hbv : (edgePairKey G b).2 < vCap)
    (hab : representativeSortKey G vCap eCap a ≤ representativeSortKey G vCap eCap b)
    (hbc : representativeSortKey G vCap eCap b ≤ representativeSortKey G vCap eCap c)
    (heq : edgePairKey G a = edgePairKey G c) :
    edgePairKey G b = edgePairKey G a := by
  let q := fun e => representativeSortKey G vCap eCap e / eCap
  have hq (e : ℕ) (he : e < eCap) :
      q e = vCap*(edgePairKey G e).1+(edgePairKey G e).2 := by
    dsimp [q,representativeSortKey]
    rw [Nat.mul_comm _ eCap,Nat.mul_add_div (Nat.zero_lt_of_lt he),Nat.div_eq_of_lt he,Nat.add_zero]
  have hac : q a = q c := by rw [hq a ha,hq c hc,heq]
  have hba : q b = q a :=
    le_antisymm ((Nat.div_le_div_right hbc).trans_eq hac.symm) (Nat.div_le_div_right hab)
  calc
    edgePairKey G b = (q b / vCap,q b % vCap) :=
      (representativeSortKey_decode G vCap eCap b hb hbv).2.symm
    _ = (q a / vCap,q a % vCap) := by rw [hba]
    _ = edgePairKey G a := (representativeSortKey_decode G vCap eCap a ha hav).2

/-- Filtering sorted keys to a fixed class gives a list ordered by edge name. -/
theorem representativeClass_pairwise {G : MGraph} {vCap eCap : ℕ}
    {edges : List ℕ} (ends : ℕ × ℕ)
    (hs : edges.Pairwise (fun e f => representativeSortKey G vCap eCap e ≤
      representativeSortKey G vCap eCap f)) :
    (edges.filter fun e => decide (edgePairKey G e = ends)).Pairwise (· ≤ ·) := by
  have hf := hs.filter (fun e => decide (edgePairKey G e = ends))
  apply List.Pairwise.imp_of_mem (l := edges.filter fun e => decide (edgePairKey G e = ends)) _ hf
  intro e f he hf' h
  have he' : edgePairKey G e = ends := of_decide_eq_true (List.mem_filter.mp he).2
  have hf'' : edgePairKey G f = ends := of_decide_eq_true (List.mem_filter.mp hf').2
  exact (representativeSortKey_le_iff_of_sameClass (he'.trans hf''.symm)).mp h

/-- All edges parallel to the first edge are in the initial class. -/
theorem representativeClass_takeWhile_eq_filter {G : MGraph} {vCap eCap first : ℕ}
    (edges : List ℕ) (hfirst : first < eCap) (hvfirst : (edgePairKey G first).2 < vCap)
    (hvalid : ∀ e ∈ edges, e < eCap ∧ (edgePairKey G e).2 < vCap)
    (hs : (first :: edges).Pairwise (fun e f => representativeSortKey G vCap eCap e ≤
      representativeSortKey G vCap eCap f)) :
    (edges.takeWhile fun e => decide (edgePairKey G e = edgePairKey G first)) =
      edges.filter (fun e => decide (edgePairKey G e = edgePairKey G first)) := by
  induction edges with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨hle,hrest⟩ := List.pairwise_cons.mp hs
    have htail : ∀ f ∈ rest, f < eCap ∧ (edgePairKey G f).2 < vCap :=
      fun f hf => hvalid f (List.mem_cons_of_mem _ hf)
    by_cases h : edgePairKey G e = edgePairKey G first
    · have hs' := List.pairwise_cons.mpr
        ⟨fun f hf => hle f (List.mem_cons_of_mem _ hf),(List.pairwise_cons.mp hrest).2⟩
      simp [h,ih htail hs']
    · have hnone : ∀ f ∈ rest, edgePairKey G f ≠ edgePairKey G first := by
        intro f hf heq
        obtain ⟨heb,hev⟩ := hvalid e (by simp)
        exact h (representativeSortKey_between hfirst heb (htail f hf).1 hvfirst hev
          (hle e (by simp)) ((List.pairwise_cons.mp hrest).1 f hf) heq.symm)
      have hempty : rest.filter (fun f => decide (edgePairKey G f = edgePairKey G first)) = [] :=
        List.filter_eq_nil_iff.mpr (fun f hf => by simp [hnone f hf])
      simp [h,hempty]

/-- Dropping the initial class removes exactly the edges parallel to
the first edge and preserves every edge of the other classes. -/
theorem representativeClass_mem_dropWhile {G : MGraph} {vCap eCap first : ℕ}
    (edges : List ℕ) (hfirst : first < eCap) (hvfirst : (edgePairKey G first).2 < vCap)
    (hvalid : ∀ e ∈ edges, e < eCap ∧ (edgePairKey G e).2 < vCap)
    (hs : (first :: edges).Pairwise (fun e f => representativeSortKey G vCap eCap e ≤
      representativeSortKey G vCap eCap f)) (e : ℕ) :
    e ∈ edges.dropWhile (fun f => decide (edgePairKey G f = edgePairKey G first)) ↔
      e ∈ edges ∧ edgePairKey G e ≠ edgePairKey G first := by
  let p := fun f => decide (edgePairKey G f = edgePairKey G first)
  have hsub : List.Sublist (edges.dropWhile p) edges := List.dropWhile_sublist p
  change e ∈ edges.dropWhile p ↔ _
  constructor
  · intro hmem
    refine ⟨hsub.subset hmem,?_⟩
    cases hrest : edges.dropWhile p with
    | nil => simp [hrest] at hmem
    | cons f rest =>
      have hhead := List.head?_dropWhile_not p edges
      rw [hrest] at hhead
      have hfne : edgePairKey G f ≠ edgePairKey G first := by simpa [p] using hhead
      rw [hrest] at hmem hsub
      rcases List.mem_cons.mp hmem with rfl | hr
      · exact hfne
      · intro heq
        have hf := hsub.subset (List.mem_cons_self ..)
        have hef := hsub.subset (List.mem_cons_of_mem _ hr)
        obtain ⟨hfb,hfv⟩ := hvalid f hf
        have hsorted := (List.pairwise_cons.mp hs).2.sublist hsub
        exact hfne (representativeSortKey_between hfirst hfb (hvalid e hef).1 hvfirst hfv
          ((List.pairwise_cons.mp hs).1 f hf) ((List.pairwise_cons.mp hsorted).1 e hr) heq.symm)
  · rintro ⟨hmem,hne⟩
    have hsplit : edges.takeWhile p ++ edges.dropWhile p = edges := List.takeWhile_append_dropWhile
    rw [← hsplit,List.mem_append] at hmem
    rcases hmem with ht | hd
    · exact False.elim (hne (of_decide_eq_true (List.all_eq_true.mp List.all_takeWhile e ht)))
    · exact hd

end MinCostFlow.LastLevelProgram
