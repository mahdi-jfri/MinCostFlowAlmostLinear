module

public import MinCostFlow.ExpanderDecomp.RouteBFSLoop
import MinCostFlow.Expander.GraphHelpers
import Mathlib.Tactic.Linarith

/-!
# Shortest-path optimality and ball-prefix corollaries of local layered BFS

This file re-exports the local multi-source layered BFS (`RouteBFSBase.lean`, `RouteBFSLoop.lean`)
and proves its shortest-path optimality corollaries (for `ShortPathBlock`) and
ball-prefix boundary bounds (for `growBall`).
-/

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-! ### Shortest-path optimality and ball-prefix corollaries -/

/-- Any walk in `G[V]` from `S ∩ V` of length `ℓ` satisfies:
* if `ℓ ≤ res.maxReached`, its endpoint `v` has `res.dist v = some r` with `r ≤ ℓ`;
* if `res.exhausted = true`, its endpoint `v` has `res.dist v = some r` with `r ≤ ℓ` and
  `r ≤ res.maxReached`. -/
theorem bfsLayers_dist_le_of_walk (G : Graph) {X V : Finset ℕ} (hVX : V ⊆ X)
    (S : Finset ℕ) (maxDist : ℕ) (stopSet : Finset ℕ)
    {s v : ℕ} {es : List ℕ} (hs : s ∈ S ∩ V) (hw : IsEdgeWalkIn G V s v es) :
    let res := bfsLayers (adjOf G X) V S maxDist stopSet
    (es.length ≤ res.maxReached → ∃ r ≤ es.length, res.dist v = some r) ∧
    (res.exhausted = true → ∃ r ≤ es.length, r ≤ res.maxReached ∧ res.dist v = some r) := by
  have hspec := bfsLayers_spec G hVX S maxDist stopSet
  set res := bfsLayers (adjOf G X) V S maxDist stopSet
  rcases hspec with ⟨_, _, _, _, hdist_vis, _, hdist_zero, _, hclosed, hexh, _, _, _, _⟩
  -- Induct on the reversed walk so we step from the start `s` forward.
  have hrev_len : es.reverse.length = es.length := List.length_reverse
  suffices h : ∀ {v' : ℕ} {rs : List ℕ}, IsEdgeWalkIn G V s v' rs.reverse →
      (rs.length ≤ res.maxReached → ∃ r ≤ rs.length, res.dist v' = some r) ∧
      (res.exhausted = true → ∃ r ≤ rs.length, r ≤ res.maxReached ∧ res.dist v' = some r) by
    have h0 := h (rs := es.reverse) (by simpa using hw)
    simpa [hrev_len] using h0
  intro v' rs
  induction rs generalizing v' with
  | nil =>
    intro hw'
    cases hw'.1 with
    | nil =>
      have h0 : res.dist s = some 0 := (hdist_zero s).mpr hs
      exact ⟨fun _ => ⟨0, le_refl _, h0⟩, fun _ => ⟨0, le_refl _, Nat.zero_le _, h0⟩⟩
  | cons j rs ih =>
    intro hw'
    simp only [List.reverse_cons] at hw'
    -- Split `rs.reverse ++ [j]` into `rs.reverse` and `[j]`.
    have hsp := hw'.split_at (r := rs.length) (by simp)
    obtain ⟨x, _, hpre, hsuf⟩ := hsp
    have hpre' : IsEdgeWalkIn G V s x rs.reverse := by
      simpa [List.take_append_of_le_length] using hpre
    have hsuf' : IsEdgeWalkIn G V x v' [j] := by
      simpa [List.drop_append_of_le_length] using hsuf
    -- Extract the single edge `j` from `x` to `v'` as an entry of `adjOf G X x`.
    have hadj : (v', j) ∈ adjOf G X x ∧ v' ∈ V := by
      rcases hsuf' with ⟨hstep, hin⟩
      cases hstep with
      | cons hj hend hnil =>
        cases hnil
        have hinj : insideB V (edgeAt G.edges j) = true := hin j List.mem_cons_self
        have hinX : insideB X (edgeAt G.edges j) = true := by
          unfold insideB at hinj ⊢
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hinj ⊢
          exact ⟨hVX hinj.1, hVX hinj.2⟩
        have hv'V : v' ∈ V := by
          unfold insideB at hinj
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hinj
          rcases hend with ⟨_, h2⟩ | ⟨h1, _⟩
          · exact h2 ▸ hinj.2
          · exact h1 ▸ hinj.1
        exact ⟨(mem_adjOf_iff G X x v' j).mpr ⟨hj, hinX, hend⟩, hv'V⟩
    obtain ⟨ih1, ih2⟩ := ih hpre'
    constructor
    · intro hle
      have hle' : rs.length ≤ res.maxReached := by simp at hle; omega
      obtain ⟨r, hr_le, hdx⟩ := ih1 hle'
      have hr_lt : r < res.maxReached := by simp at hle; omega
      obtain ⟨r', hr'_le, hdv'⟩ := hclosed x v' j r hr_lt hdx hadj.1 hadj.2
      exact ⟨r', by simp; omega, hdv'⟩
    · intro he
      obtain ⟨r, hr_le, hr_max, hdx⟩ := ih2 he
      by_cases hlt : r < res.maxReached
      · obtain ⟨r', hr'_le, hdv'⟩ := hclosed x v' j r hlt hdx hadj.1 hadj.2
        have hv'vis : v' ∈ res.visited := (hdist_vis v').mpr ⟨r', by omega, hdv'⟩
        obtain ⟨r'', hr''_max, hdv''⟩ := (hdist_vis v').mp hv'vis
        have hr_eq : r' = r'' := Option.some.inj (hdv'.symm.trans hdv'')
        exact ⟨r', by simp; omega, hr_eq ▸ hr''_max, hdv'⟩
      · have hxvis : x ∈ res.visited := (hdist_vis x).mpr ⟨r, hr_max, hdx⟩
        have hv'vis : v' ∈ res.visited := hexh he x hxvis v' j hadj.1 hadj.2
        obtain ⟨r', hr'_max, hdv'⟩ := (hdist_vis v').mp hv'vis
        exact ⟨r', by simp; omega, hr'_max, hdv'⟩

/-- If `bfsLayers` does not hit `stopSet`, then there is no walk of length `≤ maxDist` in `G[V]`
from `S ∩ V` to `stopSet ∩ V`. -/
theorem bfsLayers_no_short_walk_of_hitStop_false (G : Graph) {X V : Finset ℕ} (hVX : V ⊆ X)
    (S : Finset ℕ) (maxDist : ℕ) (stopSet : Finset ℕ)
    (hfalse : (bfsLayers (adjOf G X) V S maxDist stopSet).hitStop = false)
    {s t : ℕ} {es : List ℕ} (hs : s ∈ S ∩ V) (ht : t ∈ stopSet ∩ V)
    (hw : IsEdgeWalkIn G V s t es) :
    maxDist < es.length := by
  by_contra hle
  push Not at hle
  have hspec := bfsLayers_spec G hVX S maxDist stopSet
  set res := bfsLayers (adjOf G X) V S maxDist stopSet
  obtain ⟨_, _, _, _, hdist_vis, _, _, _, _, _, _, _, hnohit, _⟩ := hspec
  obtain ⟨ht_not_vis, hor⟩ := hnohit hfalse
  obtain ⟨h1, h2⟩ := bfsLayers_dist_le_of_walk G hVX S maxDist stopSet hs hw
  rcases hor with he | hmax
  · obtain ⟨r, _, hrmax, hdt⟩ := h2 he
    exact ht_not_vis t ht ((hdist_vis t).mpr ⟨r, hrmax, hdt⟩)
  · obtain ⟨r, hrle, hdt⟩ := h1 (hmax.symm ▸ hle)
    exact ht_not_vis t ht ((hdist_vis t).mpr ⟨r, hmax.symm ▸ le_trans hrle hle, hdt⟩)

/-- If `bfsLayers` hits `stopSet`, then `res.maxReached` is the exact shortest-path distance from
`S ∩ V` to `stopSet ∩ V` in `G[V]`: no walk has length `< res.maxReached`. -/
theorem bfsLayers_min_dist_of_hitStop_true (G : Graph) {X V : Finset ℕ} (hVX : V ⊆ X)
    (S : Finset ℕ) (maxDist : ℕ) (stopSet : Finset ℕ)
    (htrue : (bfsLayers (adjOf G X) V S maxDist stopSet).hitStop = true)
    {s t : ℕ} {es : List ℕ} (hs : s ∈ S ∩ V) (ht : t ∈ stopSet ∩ V)
    (hw : IsEdgeWalkIn G V s t es) :
    (bfsLayers (adjOf G X) V S maxDist stopSet).maxReached ≤ es.length := by
  by_contra hlt
  push Not at hlt
  have hspec := bfsLayers_spec G hVX S maxDist stopSet
  set res := bfsLayers (adjOf G X) V S maxDist stopSet
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hhit, _, _⟩ := hspec
  obtain ⟨_, _, hno_earlier⟩ := hhit htrue
  obtain ⟨h1, _⟩ := bfsLayers_dist_le_of_walk G hVX S maxDist stopSet hs hw
  obtain ⟨r, hrle, hdt⟩ := h1 (Nat.le_of_lt hlt)
  exact hno_earlier t ht r (lt_of_le_of_lt hrle hlt) hdt

/-! ### Ball-prefix properties for `growBall` -/

private lemma mem_foldr_toFinset_iff (ls : List (List ℕ)) (v : ℕ) :
    v ∈ ls.foldr (fun L acc => L.toFinset ∪ acc) ∅ ↔ ∃ L ∈ ls, v ∈ L := by
  induction ls with
  | nil => simp
  | cons L rest ih =>
    simp only [List.foldr_cons, Finset.mem_union, List.mem_toFinset, ih, List.mem_cons,
      exists_eq_or_imp]

theorem mem_ballPrefix_iff (G : Graph) {X V : Finset ℕ} (hVX : V ⊆ X)
    (S : Finset ℕ) (maxDist : ℕ) (stopSet : Finset ℕ) (j : ℕ) (v : ℕ) :
    v ∈ ballPrefix (bfsLayers (adjOf G X) V S maxDist stopSet).layers j ↔
      ∃ r ≤ j, r < (bfsLayers (adjOf G X) V S maxDist stopSet).layers.length ∧
        (bfsLayers (adjOf G X) V S maxDist stopSet).dist v = some r := by
  have hspec := bfsLayers_spec G hVX S maxDist stopSet
  set res := bfsLayers (adjOf G X) V S maxDist stopSet
  obtain ⟨_, _, _, hlayers_mem, _, _, _, _, _, _, _, _, _, _⟩ := hspec
  unfold ballPrefix
  rw [mem_foldr_toFinset_iff]
  constructor
  · rintro ⟨L, hL, hvL⟩
    rw [List.mem_iff_getElem] at hL
    obtain ⟨r, hr, rfl⟩ := hL
    have hlt_take : r < min (j + 1) res.layers.length := by simpa using hr
    have hr1 : r ≤ j := by omega
    have hr2 : r < res.layers.length := by omega
    rw [List.getElem_take] at hvL
    exact ⟨r, hr1, hr2, (hlayers_mem r hr2 v).mp hvL⟩
  · rintro ⟨r, hr1, hr2, hdv⟩
    have hr_take : r < (res.layers.take (j + 1)).length := by simp; omega
    refine ⟨(res.layers.take (j + 1))[r]'hr_take, List.getElem_mem hr_take, ?_⟩
    rw [List.getElem_take]
    exact (hlayers_mem r hr2 v).mpr hdv

theorem ballPrefix_subset_visited (G : Graph) {X V : Finset ℕ} (hVX : V ⊆ X)
    (S : Finset ℕ) (maxDist : ℕ) (stopSet : Finset ℕ) (j : ℕ) :
    ballPrefix (bfsLayers (adjOf G X) V S maxDist stopSet).layers j ⊆
      (bfsLayers (adjOf G X) V S maxDist stopSet).visited := by
  intro v hv
  set res := bfsLayers (adjOf G X) V S maxDist stopSet
  have hspec := bfsLayers_spec G hVX S maxDist stopSet
  obtain ⟨_, _, _, _, hdist_vis, _, _, _, _, _, hlen, _, _, _⟩ := hspec
  rw [mem_ballPrefix_iff G hVX S maxDist stopSet j v] at hv
  obtain ⟨r, _, hr_len, hdv⟩ := hv
  change r < res.layers.length at hr_len
  change res.dist v = some r at hdv
  have hne : (S ∩ V).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have h0 : res.layers = [] := by
      unfold res bfsLayers
      have hsort : (S ∩ V).sort (· ≤ ·) = [] := by simp [hemp]
      simp [hsort]
    rw [h0] at hr_len
    simp at hr_len
  have hmax : r ≤ res.maxReached := by
    have hlen' : res.layers.length = res.maxReached + 1 := hlen hne
    omega
  exact (hdist_vis v).mpr ⟨r, hmax, hdv⟩

/-- If BFS stops because `exhausted = true`, then `res.visited` has zero cut in `G[V]`. -/
theorem cutIn_visited_eq_zero_of_exhausted (G : Graph) {X V : Finset ℕ} (hVX : V ⊆ X)
    (S : Finset ℕ) (maxDist : ℕ) (stopSet : Finset ℕ)
    (he : (bfsLayers (adjOf G X) V S maxDist stopSet).exhausted = true) :
    G.cutIn V (bfsLayers (adjOf G X) V S maxDist stopSet).visited = 0 := by
  have hspec := bfsLayers_spec G hVX S maxDist stopSet
  set res := bfsLayers (adjOf G X) V S maxDist stopSet
  obtain ⟨_, _, _, _, _, _, _, _, _, hexh, _, _, _, _⟩ := hspec
  rw [cutIn_eq_card]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j hj
  rw [Finset.mem_range] at hj
  rintro ⟨hinV, hcr⟩
  unfold insideB at hinV
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hinV
  have hinX : insideB X (edgeAt G.edges j) = true := by
    unfold insideB
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hVX hinV.1, hVX hinV.2⟩
  unfold crossesB at hcr
  rw [bne_iff_ne] at hcr
  by_cases h1 : (edgeAt G.edges j).1 ∈ res.visited
  · have h2 : (edgeAt G.edges j).2 ∉ res.visited := by
      intro h2; exact hcr (by simp [h1, h2])
    have hadj : ((edgeAt G.edges j).2, j) ∈ adjOf G X (edgeAt G.edges j).1 :=
      (mem_adjOf_iff G X _ _ j).mpr ⟨hj, hinX, Or.inl ⟨rfl, rfl⟩⟩
    exact h2 (hexh he _ h1 _ j hadj hinV.2)
  · have h2 : (edgeAt G.edges j).2 ∈ res.visited := by
      by_contra h2; exact hcr (by simp [h1, h2])
    have hadj : ((edgeAt G.edges j).1, j) ∈ adjOf G X (edgeAt G.edges j).2 :=
      (mem_adjOf_iff G X _ _ j).mpr ⟨hj, hinX, Or.inr ⟨rfl, rfl⟩⟩
    exact h1 (hexh he _ h2 _ j hadj hinV.1)

/-- For `j + 1 < res.layers.length`, every edge of `G[V]` crossing `ballPrefix res.layers j`
has its outside endpoint in `res.layers[j + 1]`, so the cut is at most the volume of layer
`j + 1` in `G[V]`. -/
theorem cutIn_ballPrefix_le_volIn_next_layer (G : Graph) {X V : Finset ℕ} (hVX : V ⊆ X)
    (S : Finset ℕ) (maxDist : ℕ) (stopSet : Finset ℕ)
    {j : ℕ} (hj : j + 1 < (bfsLayers (adjOf G X) V S maxDist stopSet).layers.length) :
    G.cutIn V (ballPrefix (bfsLayers (adjOf G X) V S maxDist stopSet).layers j) ≤
      G.volIn V ((bfsLayers (adjOf G X) V S maxDist stopSet).layers[j + 1]'hj).toFinset := by
  set res := bfsLayers (adjOf G X) V S maxDist stopSet
  have hspec := bfsLayers_spec G hVX S maxDist stopSet
  obtain ⟨_, _, _, hlayers_mem, _, _, _, _, hclosed, _, hlen, _, _, _⟩ := hspec
  change G.cutIn V (ballPrefix res.layers j) ≤ G.volIn V (res.layers[j + 1]'hj).toFinset
  have hne : (S ∩ V).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have h0 : res.layers = [] := by
      unfold res bfsLayers
      have hsort : (S ∩ V).sort (· ≤ ·) = [] := by simp [hemp]
      simp [hsort]
    rw [h0] at hj
    simp at hj
  have hmax : j < res.maxReached := by
    have hlen' : res.layers.length = res.maxReached + 1 := hlen hne
    omega
  rw [cutIn_eq_sum_map, volIn_eq_sum_map]
  -- Every edge of `G.inside V` crossing `ballPrefix j` has an endpoint in `res.layers[j + 1]`.
  rw [← insideEdgesIdx_map_snd]
  simp only [List.map_map]
  apply sum_map_le_sum_map
  intro ie hie
  rw [mem_insideEdgesIdx_iff] at hie
  obtain ⟨hidx, he_eq, hinV⟩ := hie
  simp only [Function.comp_apply]
  have hinX : insideB X (edgeAt G.edges ie.1) = true := by
    rw [← he_eq]
    unfold insideB at hinV ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hinV ⊢
    exact ⟨hVX hinV.1, hVX hinV.2⟩
  unfold insideB at hinV
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hinV
  by_cases h1 : ie.2.1 ∈ ballPrefix res.layers j <;>
    by_cases h2 : ie.2.2 ∈ ballPrefix res.layers j
  · simp [h1, h2]
  · -- `ie.2.1 ∈ ballPrefix j`, `ie.2.2 ∉ ballPrefix j` => `ie.2.2 ∈ res.layers[j + 1]`
    have h1' := (mem_ballPrefix_iff G hVX S maxDist stopSet j ie.2.1).mp h1
    obtain ⟨r1, hr1_le, _, hd1⟩ := h1'
    have hadj : (ie.2.2, ie.1) ∈ adjOf G X ie.2.1 :=
      (mem_adjOf_iff G X ie.2.1 ie.2.2 ie.1).mpr ⟨hidx, hinX, Or.inl (by rw [← he_eq]; exact ⟨rfl, rfl⟩)⟩
    obtain ⟨r2, hr2_le, hd2⟩ := hclosed ie.2.1 ie.2.2 ie.1 r1 (lt_of_le_of_lt hr1_le hmax) hd1 hadj hinV.2
    have hr2_eq : r2 = j + 1 := by
      by_contra hne2
      have hr2_le_j : r2 ≤ j := by omega
      exact h2 ((mem_ballPrefix_iff G hVX S maxDist stopSet j ie.2.2).mpr
        ⟨r2, hr2_le_j, by omega, hd2⟩)
    have hmem2 : ie.2.2 ∈ (res.layers[j + 1]'hj).toFinset := by
      rw [List.mem_toFinset, hlayers_mem (j + 1) hj ie.2.2, ← hr2_eq]
      exact hd2
    simp [h1, h2, hmem2]
  · -- Symmetric: `ie.2.2 ∈ ballPrefix j`, `ie.2.1 ∉ ballPrefix j` => `ie.2.1 ∈ res.layers[j + 1]`
    have h2' := (mem_ballPrefix_iff G hVX S maxDist stopSet j ie.2.2).mp h2
    obtain ⟨r2, hr2_le, _, hd2⟩ := h2'
    have hadj : (ie.2.1, ie.1) ∈ adjOf G X ie.2.2 :=
      (mem_adjOf_iff G X ie.2.2 ie.2.1 ie.1).mpr ⟨hidx, hinX, Or.inr (by rw [← he_eq]; exact ⟨rfl, rfl⟩)⟩
    obtain ⟨r1, hr1_le, hd1⟩ := hclosed ie.2.2 ie.2.1 ie.1 r2 (lt_of_le_of_lt hr2_le hmax) hd2 hadj hinV.1
    have hr1_eq : r1 = j + 1 := by
      by_contra hne1
      have hr1_le_j : r1 ≤ j := by omega
      exact h1 ((mem_ballPrefix_iff G hVX S maxDist stopSet j ie.2.1).mpr
        ⟨r1, hr1_le_j, by omega, hd1⟩)
    have hmem1 : ie.2.1 ∈ (res.layers[j + 1]'hj).toFinset := by
      rw [List.mem_toFinset, hlayers_mem (j + 1) hj ie.2.1, ← hr1_eq]
      exact hd1
    simp [h1, h2, hmem1]
  · simp [h1, h2]

end MinCostFlow.ExpanderDecomp
