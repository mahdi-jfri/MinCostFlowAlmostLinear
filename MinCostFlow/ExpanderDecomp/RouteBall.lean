module

public import MinCostFlow.ExpanderDecomp.RouteBFS
import MinCostFlow.Expander.GraphHelpers
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Integer ball growing

Given nonempty disjoint terminal sets `S, T ⊆ V ⊆ X` whose distance in `H[V]` exceeds
`d = 2 h L` (with `h = 16 Δ b`, maximum degree `≤ Δ`, and `|V| < 2^L`), `growBall` runs two
local multi-source BFS traversals up to radius `h L` (from `S` and from `T`), selects the
smaller radius-`h L` ball (size at most `|V| / 2`), and scans complete layers incrementally
while maintaining the exact boundary count `H.cutIn V cur`.

By the integer binomial inequality `2 * h^h ≤ (h + 1)^h` (`two_mul_pow_le_succ_pow`), some
prefix ball `B` satisfies:
* `S ⊆ B ∨ T ⊆ B`,
* `B ⊆ V` and `2 * B.card ≤ V.card`,
* `16 * b * H.cutIn V B ≤ B.card`.

The exact step count is bounded by `8 * (|X| + (H.inside X).length + 1)`, independent of `h L`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited

/-- Count incidences of `u` into `cur` and into `V \ insert u cur` in one scan of `adj u`,
returning `(inCnt, outCnt, steps)`. -/
def countIncidence (V cur : Finset ℕ) (u : ℕ) : List (ℕ × ℕ) → ℕ × ℕ × ℕ
  | [] => (0, 0, 0)
  | (w, _) :: rest =>
    let r := countIncidence V cur u rest
    let inAdd := if w ∈ cur then 1 else 0
    let outAdd := if w ∈ V ∧ w ∉ insert u cur then 1 else 0
    (r.1 + inAdd, r.2.1 + outAdd, r.2.2 + 1)

/-- Insert all vertices of one BFS layer into `cur`, updating the exact cut `bd = H.cutIn V cur`
and accumulating step cost. -/
def addLayerToBall (adj : ℕ → List (ℕ × ℕ)) (V : Finset ℕ) :
    List ℕ → Finset ℕ → ℕ → ℕ → Finset ℕ × ℕ × ℕ
  | [], cur, bd, cost => (cur, bd, cost)
  | u :: rest, cur, bd, cost =>
    let r := countIncidence V cur u (adj u)
    let bd' := bd + r.2.1 - r.1
    addLayerToBall adj V rest (insert u cur) bd' (cost + r.2.2 + 1)

/-- Scan complete BFS layers, stopping at the first layer whose prefix ball `cur` satisfies
`16 * b * bd ≤ cur.card`. Returns `(ball, cost)`. -/
def scanBallLayers (adj : ℕ → List (ℕ × ℕ)) (V : Finset ℕ) (b : ℕ) :
    List (List ℕ) → Finset ℕ → ℕ → ℕ → Finset ℕ × ℕ
  | [], cur, _bd, cost => (cur, cost + 1)
  | L :: rest, cur, bd, cost =>
    let a := addLayerToBall adj V L cur bd cost
    let cur' := a.1
    let bd' := a.2.1
    let cost' := a.2.2 + 1
    if 16 * b * bd' ≤ cur'.card then
      (cur', cost')
    else
      scanBallLayers adj V b rest cur' bd' cost'

/-- Result of ball growing. -/
structure BallResult where
  /-- The low-boundary ball `B ⊆ V`. -/
  ball : Finset ℕ
  /-- Exact operation count of the ball-growing step. -/
  cost : ℕ

/-- Ball growing: two radius-`h L` BFS traversals from `S` and `T` in `H[V]` followed
by an incremental layer scan on the smaller ball. -/
def growBall (adj : ℕ → List (ℕ × ℕ)) (V S T : Finset ℕ) (b h L : ℕ) : BallResult :=
  let bfsS := bfsLayers adj V S (h * L) ∅
  let bfsT := bfsLayers adj V T (h * L) ∅
  let bfs := if bfsS.visited.card ≤ bfsT.visited.card then bfsS else bfsT
  let res := scanBallLayers adj V b bfs.layers ∅ 0 (bfsS.cost + bfsT.cost + 1)
  { ball := res.1, cost := res.2 }

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-! ### Incremental boundary tracking -/

private lemma countIncidence_spec (V cur : Finset ℕ) (u : ℕ) (l : List (ℕ × ℕ)) :
    let r := countIncidence V cur u l
    r.1 = (l.filter fun p => decide (p.1 ∈ cur)).length ∧
    r.2.1 = (l.filter fun p => decide (p.1 ∈ V) && decide (p.1 ∉ insert u cur)).length ∧
    r.2.2 = l.length := by
  induction l with
  | nil => simp [countIncidence]
  | cons p rest ih =>
    rcases p with ⟨w, e⟩
    simp only [countIncidence, List.filter_cons, List.length_cons]
    rcases ih with ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, by omega⟩
    · by_cases hw : w ∈ cur <;> simp [hw, h1]
    · by_cases hwV : w ∈ V <;> by_cases hwI : w ∈ insert u cur <;> simp [hwV, hwI, h2]

private lemma addLayerToBall_spec (H : Graph) {X V : Finset ℕ} (hVX : V ⊆ X)
    (L : List ℕ) (hL_nd : L.Nodup) (hL_sub : ∀ u ∈ L, u ∈ V)
    (cur : Finset ℕ) (hcurV : cur ⊆ V) (hdisj : Disjoint cur L.toFinset)
    (cost : ℕ) :
    let a := addLayerToBall (adjOf H X) V L cur (H.cutIn V cur) cost
    a.1 = cur ∪ L.toFinset ∧
    a.2.1 = H.cutIn V (cur ∪ L.toFinset) ∧
    a.2.2 = cost + L.length + ∑ u ∈ L.toFinset, (adjOf H X u).length := by
  induction L generalizing cur cost with
  | nil =>
    simp [addLayerToBall]
  | cons u rest ih =>
    simp only [addLayerToBall]
    rw [List.nodup_cons] at hL_nd
    have huV : u ∈ V := hL_sub u List.mem_cons_self
    have hrest_sub : ∀ x ∈ rest, x ∈ V := fun x hx => hL_sub x (List.mem_cons_of_mem _ hx)
    have huNotCur : u ∉ cur := Finset.disjoint_right.mp hdisj (by simp)
    have hcount := countIncidence_spec V cur u (adjOf H X u)
    set r := countIncidence V cur u (adjOf H X u)
    have hcut_eq : H.cutIn V (insert u cur) = H.cutIn V cur + r.2.1 - r.1 := by
      have hid := cutIn_insert_add_in_eq H hVX hcurV huV huNotCur
      rw [← hcount.1, ← hcount.2.1] at hid
      omega
    have hdisj' : Disjoint (insert u cur) rest.toFinset := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [List.mem_toFinset] at hx2
      rcases Finset.mem_insert.mp hx1 with rfl | hx1
      · exact hL_nd.1 hx2
      · exact Finset.disjoint_left.mp hdisj hx1 (List.mem_toFinset.mpr (List.mem_cons_of_mem _ hx2))
    have hcurV' : insert u cur ⊆ V := Finset.insert_subset_iff.mpr ⟨huV, hcurV⟩
    rw [← hcut_eq]
    have hrec := ih hL_nd.2 hrest_sub (insert u cur) hcurV' hdisj' (cost + r.2.2 + 1)
    rcases hrec with ⟨h1, h2, h3⟩
    have hunion : insert u cur ∪ rest.toFinset = cur ∪ (u :: rest).toFinset := by
      ext x; simp [Finset.mem_union, Finset.mem_insert, List.mem_toFinset]
    have hsum : ∑ x ∈ (u :: rest).toFinset, (adjOf H X x).length =
        (adjOf H X u).length + ∑ x ∈ rest.toFinset, (adjOf H X x).length := by
      rw [List.toFinset_cons, Finset.sum_insert (by simpa using hL_nd.1)]
    refine ⟨by rw [h1, hunion], by rw [h2, hunion], ?_⟩
    rw [h3, hcount.2.2, hsum, List.length_cons]
    omega

/-- Scanning `ls` maintains exact cuts, stops at the first qualifying prefix if one exists,
and has linear cost in the vertices and degrees of `ls`. -/
private lemma scanBallLayers_spec (H : Graph) {X V : Finset ℕ} (hVX : V ⊆ X) (b : ℕ)
    (ls : List (List ℕ))
    (hnd : ∀ L ∈ ls, L.Nodup)
    (hne : ∀ L ∈ ls, L ≠ [])
    (hsub : ∀ L ∈ ls, ∀ u ∈ L, u ∈ V)
    (hpw : ls.Pairwise fun L₁ L₂ => Disjoint L₁.toFinset L₂.toFinset)
    (cur : Finset ℕ) (hcurV : cur ⊆ V)
    (hdisj : ∀ L ∈ ls, Disjoint cur L.toFinset)
    (cost : ℕ)
    (hex : ∃ k < ls.length,
      let S := cur ∪ (ls.take (k + 1)).foldr (fun L acc => L.toFinset ∪ acc) ∅
      16 * b * H.cutIn V S ≤ S.card) :
    let res := scanBallLayers (adjOf H X) V b ls cur (H.cutIn V cur) cost
    (∃ k < ls.length,
      res.1 = cur ∪ (ls.take (k + 1)).foldr (fun L acc => L.toFinset ∪ acc) ∅ ∧
      16 * b * H.cutIn V res.1 ≤ res.1.card) ∧
    res.2 ≤ cost + (ls.map fun L => 2 * L.length + ∑ u ∈ L.toFinset, (adjOf H X u).length).sum + 1 := by
  induction ls generalizing cur cost with
  | nil =>
    obtain ⟨k, hk, _⟩ := hex
    simp at hk
  | cons L rest ih =>
    simp only [scanBallLayers]
    rw [List.pairwise_cons] at hpw
    have hL_nd : L.Nodup := hnd L List.mem_cons_self
    have hL_ne : L ≠ [] := hne L List.mem_cons_self
    have hL_pos : 1 ≤ L.length := List.length_pos_iff.mpr hL_ne
    have hL_sub : ∀ u ∈ L, u ∈ V := hsub L List.mem_cons_self
    have hL_disj : Disjoint cur L.toFinset := hdisj L List.mem_cons_self
    have hadd := addLayerToBall_spec H hVX L hL_nd hL_sub cur hcurV hL_disj cost
    set a := addLayerToBall (adjOf H X) V L cur (H.cutIn V cur) cost with ha_def
    rcases hadd with ⟨ha1, ha2, ha3⟩
    by_cases hgood : 16 * b * a.2.1 ≤ a.1.card
    · simp only [hgood, ↓reduceIte]
      refine ⟨⟨0, by simp, ?_, ?_⟩, ?_⟩
      · simp [ha1]
      · rw [ha2, ← ha1] at hgood
        exact hgood
      · simp only [List.map_cons, List.sum_cons, ha3]
        omega
    · simp only [hgood, ↓reduceIte]
      have hcur'V : cur ∪ L.toFinset ⊆ V :=
        Finset.union_subset hcurV (fun u hu => hL_sub u (List.mem_toFinset.mp hu))
      have hdisj' : ∀ M ∈ rest, Disjoint (cur ∪ L.toFinset) M.toFinset := by
        intro M hM
        exact Finset.disjoint_union_left.mpr
          ⟨hdisj M (List.mem_cons_of_mem _ hM), hpw.1 M hM⟩
      have hex' : ∃ k < rest.length,
          let S := (cur ∪ L.toFinset) ∪ (rest.take (k + 1)).foldr (fun M acc => M.toFinset ∪ acc) ∅
          16 * b * H.cutIn V S ≤ S.card := by
        obtain ⟨k, hk, hgk⟩ := hex
        cases k with
        | zero =>
          simp only [List.take_succ_cons, List.take_zero, List.foldr_cons, List.foldr_nil,
            Finset.union_empty] at hgk
          rw [← ha2, ← ha1] at hgk
          exact absurd hgk hgood
        | succ k' =>
          simp only [List.length_cons, Nat.add_lt_add_iff_right] at hk
          refine ⟨k', hk, ?_⟩
          simp only [List.take_succ_cons, List.foldr_cons] at hgk
          simpa [Finset.union_assoc] using hgk
      have hrec := ih
        (fun M hM => hnd M (List.mem_cons_of_mem _ hM))
        (fun M hM => hne M (List.mem_cons_of_mem _ hM))
        (fun M hM => hsub M (List.mem_cons_of_mem _ hM))
        hpw.2 (cur ∪ L.toFinset) hcur'V hdisj' (a.2.2 + 1) hex'
      rw [ha1, ha2]
      rcases hrec with ⟨⟨k', hk', hball_eq, hball_good⟩, hcost_rec⟩
      refine ⟨⟨k' + 1, by simp [hk'], ?_, hball_good⟩, ?_⟩
      · rw [hball_eq]
        simp [Finset.union_assoc]
      · simp only [List.map_cons, List.sum_cons]
        omega

/-! ### Exponential layer growth contradiction -/

/-- If `bfsLayers` from a nonempty `S ⊆ V` finishes with `stopSet = ∅` on a graph of max degree
`≤ Δ` and `|V| < 2^L`, then some prefix `ballPrefix bfs.layers k` (`k < bfs.layers.length`)
satisfies `16 * b * H.cutIn V (ballPrefix bfs.layers k) ≤ (ballPrefix bfs.layers k).card`. -/
private lemma exists_sparse_ballPrefix (H : Graph) {X V S : Finset ℕ} (hVX : V ⊆ X)
    (hSV : S ⊆ V) (hSne : S.Nonempty)
    {Δ b L : ℕ} (hΔ : 1 ≤ Δ) (hb : 1 ≤ b) (_hL : 1 ≤ L)
    (hdeg : ∀ v ∈ V, H.degIn V v ≤ Δ)
    (hcard : V.card < 2 ^ L) :
    let bfs := bfsLayers (adjOf H X) V S (routeH Δ b * L) ∅
    ∃ k < bfs.layers.length,
      16 * b * H.cutIn V (ballPrefix bfs.layers k) ≤ (ballPrefix bfs.layers k).card := by
  set h := routeH Δ b
  set bfs := bfsLayers (adjOf H X) V S (h * L) ∅ with hbfs_def
  have hspec := bfsLayers_spec H hVX S (h * L) ∅
  rcases hspec with ⟨hvisV, _, hnd, hlayers_mem, hdist_vis, _, hdist_zero, _, _, _, hlen_fn, _,
    hnohit, _⟩
  have hS0 : S ∩ V = S := Finset.inter_eq_left.mpr hSV
  have hS0ne : (S ∩ V).Nonempty := hS0.symm ▸ hSne
  have hlen : bfs.layers.length = bfs.maxReached + 1 := hlen_fn hS0ne
  change ∀ v, v ∈ bfs.visited ↔ ∃ r ≤ bfs.maxReached, bfs.dist v = some r at hdist_vis
  -- Since `stopSet = ∅`, `hitStop = false`.
  have hhit_false : bfs.hitStop = false := by
    cases hh : bfs.hitStop
    · rfl
    · exfalso
      have hspec2 := bfsLayers_spec H hVX S (h * L) ∅
      obtain ⟨_, ⟨t, ht, _⟩, _⟩ := hspec2.2.2.2.2.2.2.2.2.2.2.2.1 hh
      simp at ht
  obtain ⟨_, hor⟩ := hnohit hhit_false
  change bfs.exhausted = true ∨ bfs.maxReached = h * L at hor
  -- Case A: exhausted -> the full visited set has cut 0!
  rcases hor with hexh | hmax_eq
  · refine ⟨bfs.maxReached, by omega, ?_⟩
    have hfull : ballPrefix bfs.layers bfs.maxReached = bfs.visited := by
      ext v
      rw [mem_ballPrefix_iff H hVX S (h * L) ∅ bfs.maxReached v]
      change (∃ r ≤ bfs.maxReached, r < bfs.layers.length ∧ bfs.dist v = some r) ↔ v ∈ bfs.visited
      rw [hdist_vis v]
      constructor
      · rintro ⟨r, hr1, _, hdv⟩; exact ⟨r, hr1, hdv⟩
      · rintro ⟨r, hr1, hdv⟩; exact ⟨r, hr1, by omega, hdv⟩
    rw [hfull, cutIn_visited_eq_zero_of_exhausted H hVX S (h * L) ∅ hexh]
    simp
  · -- Case B: reached full radius `h * L`. Prove by contradiction using `(h + 1)^h ≥ 2 * h^h`!
    by_contra hnone
    dsimp only at hnone
    push Not at hnone
    -- First show `ballPrefix (j + 1)` splits disjointly into `ballPrefix j` and `layers[j + 1]`.
    have hstep_card : ∀ j (hj : j + 1 < bfs.layers.length),
        (ballPrefix bfs.layers (j + 1)).card =
          (ballPrefix bfs.layers j).card + (bfs.layers[j + 1]'hj).toFinset.card := by
      intro j hj
      have hunion : ballPrefix bfs.layers (j + 1) =
          ballPrefix bfs.layers j ∪ (bfs.layers[j + 1]'hj).toFinset := by
        ext v
        simp only [Finset.mem_union, List.mem_toFinset]
        rw [mem_ballPrefix_iff H hVX S (h * L) ∅ (j + 1) v,
          mem_ballPrefix_iff H hVX S (h * L) ∅ j v]
        change (∃ r ≤ j + 1, r < bfs.layers.length ∧ bfs.dist v = some r) ↔
          (∃ r ≤ j, r < bfs.layers.length ∧ bfs.dist v = some r) ∨ v ∈ bfs.layers[j + 1]'hj
        rw [hlayers_mem (j + 1) hj v]
        constructor
        · rintro ⟨r, hr1, hr2, hdv⟩
          by_cases hEq : r = j + 1
          · exact Or.inr (hEq ▸ hdv)
          · exact Or.inl ⟨r, by omega, hr2, hdv⟩
        · rintro (⟨r, hr1, hr2, hdv⟩ | hdv)
          · exact ⟨r, by omega, hr2, hdv⟩
          · exact ⟨j + 1, le_refl _, hj, hdv⟩
      have hdisj : Disjoint (ballPrefix bfs.layers j) (bfs.layers[j + 1]'hj).toFinset := by
        rw [Finset.disjoint_left]
        intro v hv1 hv2
        rw [mem_ballPrefix_iff H hVX S (h * L) ∅ j v] at hv1
        change ∃ r ≤ j, r < bfs.layers.length ∧ bfs.dist v = some r at hv1
        obtain ⟨r, hr1, _, hdv⟩ := hv1
        rw [List.mem_toFinset, hlayers_mem (j + 1) hj v] at hv2
        rw [hdv] at hv2
        have : r = j + 1 := Option.some.inj hv2
        omega
      rw [hunion, Finset.card_union_of_disjoint hdisj]
    -- One-step growth: `(h + 1) * |B_j| ≤ h * |B_{j + 1}|` for all `j < h * L`.
    have hgrow_step : ∀ j < h * L,
        (h + 1) * (ballPrefix bfs.layers j).card ≤ h * (ballPrefix bfs.layers (j + 1)).card := by
      intro j hj
      have hj1 : j + 1 < bfs.layers.length := by omega
      have hlt : (ballPrefix bfs.layers j).card < 16 * b * H.cutIn V (ballPrefix bfs.layers j) :=
        hnone j (by omega)
      have hcut_vol : H.cutIn V (ballPrefix bfs.layers j) ≤
          H.volIn V (bfs.layers[j + 1]'hj1).toFinset :=
        cutIn_ballPrefix_le_volIn_next_layer H hVX S (h * L) ∅ hj1
      have hLsubV : (bfs.layers[j + 1]'hj1).toFinset ⊆ V := by
        intro v hv
        rw [List.mem_toFinset, hlayers_mem (j + 1) hj1 v] at hv
        exact hvisV ((hdist_vis v).mpr ⟨j + 1, by omega, hv⟩)
      have hvol_le : H.volIn V (bfs.layers[j + 1]'hj1).toFinset ≤
          Δ * (bfs.layers[j + 1]'hj1).toFinset.card :=
        volIn_le_mul_card hLsubV hdeg
      have hcard_eq := hstep_card j hj1
      have h1 : (ballPrefix bfs.layers j).card ≤
          16 * b * (Δ * (bfs.layers[j + 1]'hj1).toFinset.card) := by
        have hm := Nat.mul_le_mul_left (16 * b) (le_trans hcut_vol hvol_le)
        omega
      have hh_def : 16 * b * (Δ * (bfs.layers[j + 1]'hj1).toFinset.card) =
          h * (bfs.layers[j + 1]'hj1).toFinset.card := by
        unfold h routeH; ring
      rw [hh_def] at h1
      have hmul_eq : (h + 1) * (ballPrefix bfs.layers j).card =
          h * (ballPrefix bfs.layers j).card + (ballPrefix bfs.layers j).card := by ring
      have hrhs_eq : h * (ballPrefix bfs.layers (j + 1)).card =
          h * (ballPrefix bfs.layers j).card + h * (bfs.layers[j + 1]'hj1).toFinset.card := by
        rw [hcard_eq]; ring
      omega
    -- Induct to `j = h * L`:
    have hgrow : ∀ j ≤ h * L,
        (h + 1) ^ j * (ballPrefix bfs.layers 0).card ≤ h ^ j * (ballPrefix bfs.layers j).card := by
      intro j hj
      induction j with
      | zero => simp
      | succ j ih =>
        have ih' := ih (by omega)
        have hst := hgrow_step j (by omega)
        calc
          (h + 1) ^ (j + 1) * (ballPrefix bfs.layers 0).card
              = (h + 1) * ((h + 1) ^ j * (ballPrefix bfs.layers 0).card) := by
                rw [Nat.pow_succ]; ring
          _ ≤ (h + 1) * (h ^ j * (ballPrefix bfs.layers j).card) :=
                Nat.mul_le_mul_left (h + 1) ih'
          _ = h ^ j * ((h + 1) * (ballPrefix bfs.layers j).card) := by ring
          _ ≤ h ^ j * (h * (ballPrefix bfs.layers (j + 1)).card) :=
                Nat.mul_le_mul_left (h ^ j) hst
          _ = h ^ (j + 1) * (ballPrefix bfs.layers (j + 1)).card := by
                rw [Nat.pow_succ]; ring
    have hfinal := hgrow (h * L) (le_refl _)
    -- Show `1 ≤ (ballPrefix bfs.layers 0).card`
    have h0_eq : ballPrefix bfs.layers 0 = S := by
      ext v
      rw [mem_ballPrefix_iff H hVX S (h * L) ∅ 0 v]
      change (∃ r ≤ 0, r < bfs.layers.length ∧ bfs.dist v = some r) ↔ v ∈ S
      rw [← hS0, ← hdist_zero v]
      constructor
      · rintro ⟨r, hr0, _, hdv⟩
        have : r = 0 := by omega
        exact this ▸ hdv
      · intro hdv
        exact ⟨0, le_refl _, by omega, hdv⟩
    have h0_pos : 1 ≤ (ballPrefix bfs.layers 0).card := by
      rw [h0_eq]; exact Finset.one_le_card.mpr hSne
    have hhh : 1 ≤ h := routeH_pos hΔ hb
    have hbin : 2 * h ^ h ≤ (h + 1) ^ h := two_mul_pow_le_succ_pow hhh
    have hpowL : 2 ^ L * h ^ (h * L) ≤ (h + 1) ^ (h * L) := by
      calc
        2 ^ L * h ^ (h * L) = 2 ^ L * (h ^ h) ^ L := by rw [Nat.pow_mul]
        _ = (2 * h ^ h) ^ L := (Nat.mul_pow 2 (h ^ h) L).symm
        _ ≤ ((h + 1) ^ h) ^ L := Nat.pow_le_pow_left hbin L
        _ = (h + 1) ^ (h * L) := (Nat.pow_mul (h + 1) h L).symm
    have hle_V : (ballPrefix bfs.layers (h * L)).card ≤ V.card :=
      Finset.card_le_card (le_trans (ballPrefix_subset_visited H hVX S (h * L) ∅ (h * L)) hvisV)
    have hchain : 2 ^ L * h ^ (h * L) ≤ V.card * h ^ (h * L) := by
      calc
        2 ^ L * h ^ (h * L) ≤ (h + 1) ^ (h * L) := hpowL
        _ ≤ (h + 1) ^ (h * L) * (ballPrefix bfs.layers 0).card := Nat.le_mul_of_pos_right _ h0_pos
        _ ≤ h ^ (h * L) * (ballPrefix bfs.layers (h * L)).card := hfinal
        _ ≤ h ^ (h * L) * V.card := Nat.mul_le_mul_left _ hle_V
        _ = V.card * h ^ (h * L) := Nat.mul_comm _ _
    have hpos_pow : 0 < h ^ (h * L) := Nat.pow_pos hhh
    have h2L_le : 2 ^ L ≤ V.card := Nat.le_of_mul_le_mul_right hchain hpos_pow
    omega

/-! ### Main specification of `growBall` -/

private lemma sum_layers_cost_le (H : Graph) {X V : Finset ℕ} (hVX : V ⊆ X)
    (ls : List (List ℕ))
    (hnd : ∀ L ∈ ls, L.Nodup)
    (hsub : ∀ L ∈ ls, ∀ u ∈ L, u ∈ V)
    (hpw : ls.Pairwise fun L₁ L₂ => Disjoint L₁.toFinset L₂.toFinset) :
    (ls.map fun L => 2 * L.length + ∑ u ∈ L.toFinset, (adjOf H X u).length).sum ≤
      2 * X.card + 2 * (H.inside X).length := by
  have hsum : ∀ (U : Finset ℕ), (∀ L ∈ ls, L.toFinset ⊆ U) →
      (ls.map fun L => 2 * L.length + ∑ u ∈ L.toFinset, (adjOf H X u).length).sum ≤
        2 * U.card + ∑ u ∈ U, (adjOf H X u).length := by
    induction ls with
    | nil => intro U _; simp
    | cons L rest ih =>
      intro U hU
      rw [List.pairwise_cons] at hpw
      have hL_nd : L.Nodup := hnd L List.mem_cons_self
      have hLU : L.toFinset ⊆ U := hU L List.mem_cons_self
      have hrest_sub : ∀ M ∈ rest, M.toFinset ⊆ U \ L.toFinset := by
        intro M hM
        rw [Finset.subset_sdiff]
        exact ⟨hU M (List.mem_cons_of_mem _ hM), (hpw.1 M hM).symm⟩
      have hrec := ih (fun M hM => hnd M (List.mem_cons_of_mem _ hM))
        (fun M hM => hsub M (List.mem_cons_of_mem _ hM)) hpw.2 (U \ L.toFinset) hrest_sub
      have hcard_split : (U \ L.toFinset).card + L.toFinset.card = U.card :=
        Finset.card_sdiff_add_card_eq_card hLU
      have hL_card : L.toFinset.card = L.length := List.toFinset_card_of_nodup hL_nd
      have hsum_split : ∑ u ∈ U \ L.toFinset, (adjOf H X u).length +
          ∑ u ∈ L.toFinset, (adjOf H X u).length = ∑ u ∈ U, (adjOf H X u).length := by
        rw [← Finset.sum_union disjoint_sdiff_self_left, Finset.sdiff_union_of_subset hLU]
      simp only [List.map_cons, List.sum_cons]
      omega
  have hsubX : ∀ L ∈ ls, L.toFinset ⊆ X := by
    intro L hL u hu
    exact hVX (hsub L hL u (List.mem_toFinset.mp hu))
  have h1 := hsum X hsubX
  rw [sum_adjOf_length H X] at h1
  exact h1

/-- **`growBall` specification.**
Suppose `S, T` are nonempty disjoint subsets of `V ⊆ X` with no walk of length `≤ 2 h L` in
`H[V]`, where `h = routeH Δ b`, `∀ v ∈ V, H.degIn V v ≤ Δ`, and `V.card < 2^L`. Then `growBall`
returns a ball `B ⊆ V` such that:
1. `S ⊆ B ∨ T ⊆ B`,
2. `2 * B.card ≤ V.card`,
3. `16 * b * H.cutIn V B ≤ B.card`,
4. `res.cost ≤ 8 * (X.card + (H.inside X).length + 1)`. -/
theorem growBall_spec (H : Graph) {X V S T : Finset ℕ} (hVX : V ⊆ X)
    (hSV : S ⊆ V) (hTV : T ⊆ V) (hSne : S.Nonempty) (hTne : T.Nonempty)
    {Δ b L : ℕ} (hΔ : 1 ≤ Δ) (hb : 1 ≤ b) (hL : 1 ≤ L)
    (hdeg : ∀ v ∈ V, H.degIn V v ≤ Δ)
    (hcard : V.card < 2 ^ L)
    (hfar : ∀ s ∈ S, ∀ t ∈ T, ∀ es, IsEdgeWalkIn H V s t es → 2 * routeH Δ b * L < es.length) :
    let res := growBall (adjOf H X) V S T b (routeH Δ b) L
    res.ball ⊆ V ∧
    (S ⊆ res.ball ∨ T ⊆ res.ball) ∧
    2 * res.ball.card ≤ V.card ∧
    16 * b * H.cutIn V res.ball ≤ res.ball.card ∧
    res.cost ≤ 8 * (X.card + (H.inside X).length + 1) := by
  unfold growBall
  dsimp only
  set h := routeH Δ b
  set bfsS := bfsLayers (adjOf H X) V S (h * L) ∅ with hS_def
  set bfsT := bfsLayers (adjOf H X) V T (h * L) ∅ with hT_def
  have hspecS := bfsLayers_spec H hVX S (h * L) ∅
  have hspecT := bfsLayers_spec H hVX T (h * L) ∅
  -- Disjointness of the two radius-`h L` balls:
  have hdisjST : Disjoint bfsS.visited bfsT.visited := by
    rw [Finset.disjoint_left]
    intro v hvS hvT
    obtain ⟨r1, hr1_le, hd1⟩ := (hspecS.2.2.2.2.1 v).mp hvS
    obtain ⟨r2, hr2_le, hd2⟩ := (hspecT.2.2.2.2.1 v).mp hvT
    obtain ⟨s, hs, es1, hlen1, hw1⟩ := hspecS.2.2.2.2.2.2.2.1 v r1 hd1
    obtain ⟨t, ht, es2, hlen2, hw2⟩ := hspecT.2.2.2.2.2.2.2.1 v r2 hd2
    have hcomb : IsEdgeWalkIn H V s t (es1 ++ es2.reverse) := hw1.append hw2.reverse
    have hgt := hfar s (Finset.mem_inter.mp hs).1 t (Finset.mem_inter.mp ht).1 _ hcomb
    have hmax1 : bfsS.maxReached ≤ h * L := hspecS.2.1
    have hmax2 : bfsT.maxReached ≤ h * L := hspecT.2.1
    simp only [List.length_append, List.length_reverse, hlen1, hlen2] at hgt
    have h2hL : 2 * h * L = h * L + h * L := by ring
    omega
  have hsum_balls : bfsS.visited.card + bfsT.visited.card ≤ V.card := by
    rw [← Finset.card_union_of_disjoint hdisjST]
    exact Finset.card_le_card (Finset.union_subset hspecS.1 hspecT.1)
  -- Helper that handles either chosen side (`S` or `T`):
  have hside : ∀ (A : Finset ℕ), A ⊆ V → A.Nonempty →
      let bfs := bfsLayers (adjOf H X) V A (h * L) ∅
      2 * bfs.visited.card ≤ V.card →
      let res := scanBallLayers (adjOf H X) V b bfs.layers ∅ 0 (bfsS.cost + bfsT.cost + 1)
      res.1 ⊆ V ∧ A ⊆ res.1 ∧ 2 * res.1.card ≤ V.card ∧
        16 * b * H.cutIn V res.1 ≤ res.1.card ∧
        res.2 ≤ 8 * (X.card + (H.inside X).length + 1) := by
    intro A hAV hAne bfs hhalf
    have hspecA := bfsLayers_spec H hVX A (h * L) ∅
    have hA0 : A ∩ V = A := Finset.inter_eq_left.mpr hAV
    have hA0ne : (A ∩ V).Nonempty := hA0.symm ▸ hAne
    have hlayers_sub : ∀ M ∈ bfs.layers, ∀ u ∈ M, u ∈ V := by
      intro M hM u hu
      rw [List.mem_iff_getElem] at hM
      obtain ⟨r, hr, rfl⟩ := hM
      have hdu : bfs.dist u = some r := (hspecA.2.2.2.1 r hr u).mp hu
      have hlenA : bfs.layers.length = bfs.maxReached + 1 := hspecA.2.2.2.2.2.2.2.2.2.2.1 hA0ne
      have hr_le : r ≤ bfs.maxReached := by omega
      exact hspecA.1 ((hspecA.2.2.2.2.1 u).mpr ⟨r, hr_le, hdu⟩)
    have hlayers_pw : bfs.layers.Pairwise fun L₁ L₂ => Disjoint L₁.toFinset L₂.toFinset := by
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      rw [Finset.disjoint_left]
      intro u hu1 hu2
      rw [List.mem_toFinset, hspecA.2.2.2.1 i hi u] at hu1
      rw [List.mem_toFinset, hspecA.2.2.2.1 j hj u] at hu2
      rw [hu1] at hu2
      have : i = j := Option.some.inj hu2
      omega
    have hex_ball := exists_sparse_ballPrefix H hVX hAV hAne hΔ hb hL hdeg hcard
    have hex' : ∃ k < bfs.layers.length,
        let S' := ∅ ∪ (bfs.layers.take (k + 1)).foldr (fun M acc => M.toFinset ∪ acc) ∅
        16 * b * H.cutIn V S' ≤ S'.card := by
      obtain ⟨k, hk, hgk⟩ := hex_ball
      refine ⟨k, hk, ?_⟩
      simpa [ballPrefix] using hgk
    have hcut0 : H.cutIn V ∅ = 0 := by simp [Graph.cutIn]
    have hscan := scanBallLayers_spec H hVX b bfs.layers hspecA.2.2.1
      (bfsLayers_layers_nonempty (adjOf H X) V A (h * L) ∅)
      hlayers_sub hlayers_pw ∅ (Finset.empty_subset _) (by simp) (bfsS.cost + bfsT.cost + 1) hex'
    rw [hcut0] at hscan
    rcases hscan with ⟨⟨k, hk, hball_eq, hball_good⟩, hcost_scan⟩
    have hball_pref : (scanBallLayers (adjOf H X) V b bfs.layers ∅ 0
        (bfsS.cost + bfsT.cost + 1)).1 = ballPrefix bfs.layers k := by
      simpa [ballPrefix] using hball_eq
    have hsub_vis : ballPrefix bfs.layers k ⊆ bfs.visited :=
      ballPrefix_subset_visited H hVX A (h * L) ∅ k
    have hsub_V : ballPrefix bfs.layers k ⊆ V := le_trans hsub_vis hspecA.1
    have hA_sub : A ⊆ ballPrefix bfs.layers k := by
      intro u hu
      rw [mem_ballPrefix_iff H hVX A (h * L) ∅ k u]
      have hd0 : bfs.dist u = some 0 := (hspecA.2.2.2.2.2.2.1 u).mpr (hA0.symm ▸ hu)
      exact ⟨0, Nat.zero_le _, Nat.zero_lt_of_lt hk, hd0⟩
    have hcard_half : 2 * (ballPrefix bfs.layers k).card ≤ V.card := by
      have hle := Finset.card_le_card hsub_vis
      omega
    have hsum_le := sum_layers_cost_le H hVX bfs.layers hspecA.2.2.1 hlayers_sub hlayers_pw
    have hcS : bfsS.cost ≤ 3 * X.card + 2 * (H.inside X).length + 2 :=
      hspecS.2.2.2.2.2.2.2.2.2.2.2.2.2
    have hcT : bfsT.cost ≤ 3 * X.card + 2 * (H.inside X).length + 2 :=
      hspecT.2.2.2.2.2.2.2.2.2.2.2.2.2
    refine ⟨hball_pref ▸ hsub_V, hball_pref ▸ hA_sub, hball_pref ▸ hcard_half, hball_good, ?_⟩
    omega
  by_cases hle : bfsS.visited.card ≤ bfsT.visited.card
  · simp only [hle, ↓reduceIte]
    have hs := hside S hSV hSne (by change 2 * bfsS.visited.card ≤ V.card; omega)
    exact ⟨hs.1, Or.inl hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2⟩
  · simp only [hle, ↓reduceIte]
    have ht := hside T hTV hTne (by change 2 * bfsT.visited.card ≤ V.card; omega)
    exact ⟨ht.1, Or.inr ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2⟩

end MinCostFlow.ExpanderDecomp
