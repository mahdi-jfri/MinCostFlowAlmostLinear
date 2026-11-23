module

public import MinCostFlow.ExpanderDecomp.RouteBFS
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Cursor-based layered DFS blocking pass

This file defines the iterative cursor-based DFS blocking pass (`dfsStep`, `dfsSources`,
`dfsBlock`), its decreasing potential `dfsPot`, vertex accounting `routedVerts`, and proves
the DFS invariants (`DeadClosed`, `DFSInv`) and linear-time specification (`dfsSources_spec`)
used by `shortPathBlock` in `RouteShortPath.lean`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited

/-- Mutable state of one DFS blocking pass. -/
structure DFSState where
  /-- Vertices already committed to accepted paths in this phase. -/
  used : Finset ℕ
  /-- Vertices proved unable to reach `T` in this phase's layered DAG. -/
  dead : Finset ℕ
  /-- Remaining unexamined adjacency list for each vertex. -/
  cursor : ℕ → List (ℕ × ℕ)
  /-- Accepted routed pairs `((s, t), es)` collected in this phase. -/
  paths : List ((ℕ × ℕ) × List ℕ)
  /-- Exact operation count of the DFS pass. -/
  cost : ℕ

/-- Vertices currently on the DFS stack, from tip `u` down to the root source. -/
def stackVerts (u : ℕ) (trail : List (ℕ × ℕ)) : List ℕ :=
  u :: trail.map Prod.fst

/-- Consecutive `(parent, child)` vertex pairs along the DFS stack. -/
def stackEdges : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ)
  | _, [] => []
  | u, (p, _) :: rest => (p, u) :: stackEdges p rest

/-- Union of all vertices visited by a list of routed walks. -/
def routedVerts (G : Graph) (paths : List ((ℕ × ℕ) × List ℕ)) : Finset ℕ :=
  paths.foldr (fun p acc => (walkVerts G.edges p.1.1 p.2).toFinset ∪ acc) ∅

/-- Iterative cursor-based DFS from one source `s` in the layered graph up to depth `j`. -/
def dfsStep (V T : Finset ℕ) (dist : ℕ → Option ℕ) (j s : ℕ) :
    ℕ → ℕ → ℕ → List (ℕ × ℕ) → DFSState → DFSState
  | 0, _, _, _, st => st
  | fuel + 1, u, r, trail, st =>
    if u ∈ T then
      let es := (trail.map Prod.snd).reverse
      let vs := stackVerts u trail
      { used := st.used ∪ vs.toFinset
        dead := st.dead
        cursor := st.cursor
        paths := ((s, u), es) :: st.paths
        cost := st.cost + vs.length + 1 }
    else if r = j then
      let st1 := { st with dead := insert u st.dead, cost := st.cost + 1 }
      match trail with
      | [] => st1
      | (p, _) :: rest => dfsStep V T dist j s fuel p (r - 1) rest st1
    else
      match st.cursor u with
      | [] =>
        let st1 := { st with dead := insert u st.dead, cost := st.cost + 1 }
        match trail with
        | [] => st1
        | (p, _) :: rest => dfsStep V T dist j s fuel p (r - 1) rest st1
      | (w, e) :: rest =>
        let st1 := { st with cursor := Function.update st.cursor u rest, cost := st.cost + 1 }
        if w ∈ V ∧ w ∉ st.used ∧ w ∉ st.dead ∧ r < j ∧ dist w = some (r + 1) then
          dfsStep V T dist j s fuel w (r + 1) ((u, e) :: trail) st1
        else
          dfsStep V T dist j s fuel u r trail st1

/-- Run `dfsStep` over every source in `sources`, sharing `used`, `dead`, and `cursor`. -/
def dfsSources (V T : Finset ℕ) (dist : ℕ → Option ℕ) (j fuel : ℕ) :
    List ℕ → DFSState → DFSState
  | [], st => st
  | s :: rest, st =>
    let st0 := { st with cost := st.cost + 1 }
    if s ∈ st.used ∨ s ∈ st.dead then
      dfsSources V T dist j fuel rest st0
    else
      let st1 := dfsStep V T dist j s fuel s 0 [] st0
      dfsSources V T dist j fuel rest st1

/-- Potential that strictly decreases at every recursive step of `dfsStep`. -/
def dfsPot (V : Finset ℕ) (st : DFSState) : ℕ :=
  (∑ v ∈ V, (st.cursor v).length) + (V \ st.dead).card

/-- One DFS blocking pass across all sources `S ∩ V`. -/
def dfsBlock (adj : ℕ → List (ℕ × ℕ)) (V S T : Finset ℕ) (dist : ℕ → Option ℕ)
    (j : ℕ) : DFSState :=
  let init : DFSState := { used := ∅, dead := ∅, cursor := adj, paths := [], cost := 0 }
  let fuel := dfsPot V init + 1
  dfsSources V T dist j fuel ((S ∩ V).sort (· ≤ ·)) init


/-- Closure of `dead`: no dead vertex is in `T`, and every layered edge out of a dead vertex
(at level `r < j`) goes into `used ∪ dead`. -/
def DeadClosed (G : Graph) (X V T : Finset ℕ) (dist : ℕ → Option ℕ) (j : ℕ)
    (used dead : Finset ℕ) : Prop :=
  ∀ w ∈ dead, w ∉ T ∧
    ∀ p ∈ adjOf G X w, p.1 ∈ V → ∀ r < j, dist w = some r → dist p.1 = some (r + 1) →
      p.1 ∈ used ∪ dead

/-- Invariant on `DFSState` between sources (empty stack). -/
structure DFSInv (G : Graph) (X V S T : Finset ℕ) (dist : ℕ → Option ℕ) (j : ℕ)
    (st : DFSState) : Prop where
  used_sub : st.used ⊆ V
  dead_sub : st.dead ⊆ V
  dead_closed : DeadClosed G X V T dist j st.used st.dead
  cursor_inv : ∀ w ∈ V, ∃ pref, adjOf G X w = pref ++ st.cursor w ∧
    ∀ p ∈ pref, p.1 ∈ V → ∀ r < j, dist w = some r → dist p.1 = some (r + 1) →
      w ∉ st.used → p.1 ∈ st.used ∪ st.dead
  used_eq : st.used = routedVerts G st.paths
  paths_valid : ∀ p ∈ st.paths,
    p.1.1 ∈ S ∩ V ∧ p.1.2 ∈ T ∩ V ∧ p.2.length = j ∧ IsSimpleWalkIn G V p.1.1 p.1.2 p.2
  paths_disj : st.paths.Pairwise fun p q =>
    Disjoint (walkVerts G.edges p.1.1 p.2).toFinset (walkVerts G.edges q.1.1 q.2).toFinset

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited

/-! ### Helper lemmas for `dfsPot` and `routedVerts` -/

private lemma dfsPot_update_tail (V : Finset ℕ) (st : DFSState) {u w e : ℕ}
    {rest : List (ℕ × ℕ)} (huV : u ∈ V) (hcur : st.cursor u = (w, e) :: rest) :
    dfsPot V { st with cursor := Function.update st.cursor u rest, cost := st.cost + 1 } + 1 =
      dfsPot V st := by
  unfold dfsPot
  dsimp only
  have hsum :
      ∑ v ∈ V, (Function.update st.cursor u rest v).length + 1 =
        ∑ v ∈ V, (st.cursor v).length := by
    rw [← Finset.add_sum_erase _ _ huV, ← Finset.add_sum_erase _ (fun v => (st.cursor v).length) huV]
    have hrest : ∑ v ∈ V.erase u, (Function.update st.cursor u rest v).length =
        ∑ v ∈ V.erase u, (st.cursor v).length := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hv)]
    rw [hrest, Function.update_self, hcur, List.length_cons]
    omega
  omega

private lemma dfsPot_insert_dead (V : Finset ℕ) (st : DFSState) {u : ℕ}
    (huV : u ∈ V) (huD : u ∉ st.dead) :
    dfsPot V { st with dead := insert u st.dead, cost := st.cost + 1 } + 1 = dfsPot V st := by
  unfold dfsPot
  dsimp only
  have hmem : u ∈ V \ st.dead := Finset.mem_sdiff.mpr ⟨huV, huD⟩
  have heq : V \ insert u st.dead = (V \ st.dead).erase u := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, not_or]
    tauto
  rw [heq, Finset.card_erase_of_mem hmem]
  have hpos : 1 ≤ (V \ st.dead).card := Finset.one_le_card.mpr ⟨u, hmem⟩
  omega

private lemma routedVerts_cons (G : Graph) (p : (ℕ × ℕ) × List ℕ)
    (ps : List ((ℕ × ℕ) × List ℕ)) :
    routedVerts G (p :: ps) = (walkVerts G.edges p.1.1 p.2).toFinset ∪ routedVerts G ps :=
  rfl

theorem routedVerts_append (G : Graph) (ps qs : List ((ℕ × ℕ) × List ℕ)) :
    routedVerts G (ps ++ qs) = routedVerts G ps ∪ routedVerts G qs := by
  induction ps with
  | nil => simp [routedVerts]
  | cons p rest ih =>
    simp only [List.cons_append, routedVerts_cons, ih, Finset.union_assoc]

theorem mem_routedVerts_iff (G : Graph) (ps : List ((ℕ × ℕ) × List ℕ)) (v : ℕ) :
    v ∈ routedVerts G ps ↔ ∃ p ∈ ps, v ∈ walkVerts G.edges p.1.1 p.2 := by
  induction ps with
  | nil => simp [routedVerts]
  | cons p rest ih =>
    simp only [routedVerts_cons, Finset.mem_union, List.mem_toFinset, ih, List.mem_cons,
      exists_eq_or_imp]

theorem card_routedVerts_le (G : Graph) (d : ℕ) (ps : List ((ℕ × ℕ) × List ℕ))
    (hlen : ∀ p ∈ ps, p.2.length ≤ d) :
    (routedVerts G ps).card ≤ (d + 1) * ps.length := by
  induction ps with
  | nil => simp [routedVerts]
  | cons p rest ih =>
    simp only [routedVerts_cons, List.length_cons]
    have h1 := Finset.card_union_le (walkVerts G.edges p.1.1 p.2).toFinset (routedVerts G rest)
    have h2 : (walkVerts G.edges p.1.1 p.2).toFinset.card ≤ d + 1 := by
      calc (walkVerts G.edges p.1.1 p.2).toFinset.card
          ≤ (walkVerts G.edges p.1.1 p.2).length := List.toFinset_card_le _
        _ = p.2.length + 1 := walkVerts_length G.edges p.1.1 p.2
        _ ≤ d + 1 := Nat.add_le_add_right (hlen p List.mem_cons_self) 1
    have h3 := ih fun q hq => hlen q (List.mem_cons_of_mem _ hq)
    have hmul : (d + 1) * (rest.length + 1) = (d + 1) * rest.length + (d + 1) := by ring
    omega

/-! ### Layered trail and DFS invariants -/

/-- `TrailValid G X V dist s u r trail` says that `trail` descends from `u` (at level `r`)
step-by-step down to source `s` (at level `0`) along valid edges in `adjOf G X`. -/
private inductive TrailValid (G : Graph) (X : Finset ℕ) (dist : ℕ → Option ℕ) (s : ℕ) :
    ℕ → ℕ → List (ℕ × ℕ) → Prop
  | nil (hdist : dist s = some 0) : TrailValid G X dist s s 0 []
  | cons {u p e r : ℕ} {rest : List (ℕ × ℕ)}
      (hadj : (u, e) ∈ adjOf G X p)
      (hdist : dist u = some (r + 1))
      (hrest : TrailValid G X dist s p r rest) :
      TrailValid G X dist s u (r + 1) ((p, e) :: rest)

private lemma TrailValid.dist_eq {G : Graph} {X : Finset ℕ} {dist : ℕ → Option ℕ} {s u r : ℕ}
    {trail : List (ℕ × ℕ)} (h : TrailValid G X dist s u r trail) :
    dist u = some r := by
  cases h with
  | nil h0 => exact h0
  | cons _ hd _ => exact hd

private lemma TrailValid.length_eq {G : Graph} {X : Finset ℕ} {dist : ℕ → Option ℕ} {s u r : ℕ}
    {trail : List (ℕ × ℕ)} (h : TrailValid G X dist s u r trail) :
    trail.length = r := by
  induction h with
  | nil => rfl
  | cons _ _ _ ih => simp [ih]

private lemma TrailValid.dist_lt_of_mem_parents {G : Graph} {X : Finset ℕ} {dist : ℕ → Option ℕ}
    {s u r : ℕ} {trail : List (ℕ × ℕ)} (h : TrailValid G X dist s u r trail)
    {w : ℕ} (hw : w ∈ trail.map Prod.fst) :
    ∃ k < r, dist w = some k := by
  induction h with
  | nil => simp at hw
  | @cons u' p' e' r' rest' _ _ hrest ih =>
    simp only [List.map_cons, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact ⟨r', Nat.lt_succ_self _, hrest.dist_eq⟩
    · obtain ⟨k, hk, hdk⟩ := ih hw
      exact ⟨k, Nat.lt_succ_of_lt hk, hdk⟩

private lemma TrailValid.nodup_stackVerts {G : Graph} {X : Finset ℕ} {dist : ℕ → Option ℕ}
    {s u r : ℕ} {trail : List (ℕ × ℕ)} (h : TrailValid G X dist s u r trail) :
    (stackVerts u trail).Nodup := by
  induction h with
  | nil => simp [stackVerts]
  | @cons u' p' e' r' rest' _ hdist hrest ih =>
    unfold stackVerts
    rw [List.nodup_cons]
    refine ⟨?_, ih⟩
    intro hmem
    have hlt : ∃ k < r' + 1, dist u' = some k := by
      simp only [List.map_cons, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact ⟨r', Nat.lt_succ_self _, hrest.dist_eq⟩
      · obtain ⟨k, hk, hdk⟩ := hrest.dist_lt_of_mem_parents hmem
        exact ⟨k, Nat.lt_succ_of_lt hk, hdk⟩
    obtain ⟨k, hk, hdk⟩ := hlt
    rw [hdist] at hdk
    have : r' + 1 = k := Option.some.inj hdk
    omega

private lemma TrailValid.root_mem_stackVerts {G : Graph} {X : Finset ℕ} {dist : ℕ → Option ℕ}
    {s u r : ℕ} {trail : List (ℕ × ℕ)} (h : TrailValid G X dist s u r trail) :
    s ∈ stackVerts u trail := by
  induction h with
  | nil => simp [stackVerts]
  | cons _ _ _ ih =>
    unfold stackVerts at ih ⊢
    exact List.mem_cons_of_mem _ ih

private lemma TrailValid.mem_stackEdges_fst_lt {G : Graph} {X : Finset ℕ} {dist : ℕ → Option ℕ}
    {s u r : ℕ} {trail : List (ℕ × ℕ)} (h : TrailValid G X dist s u r trail)
    {x y : ℕ} (hxy : (x, y) ∈ stackEdges u trail) :
    x ∈ trail.map Prod.fst ∧ ∃ k < r, dist x = some k := by
  induction h with
  | nil => simp [stackEdges] at hxy
  | @cons u' p' e' r' rest' _ _ hrest ih =>
    simp only [stackEdges, List.mem_cons, Prod.mk.injEq] at hxy
    rcases hxy with ⟨rfl, rfl⟩ | hxy
    · exact ⟨by simp, r', Nat.lt_succ_self _, hrest.dist_eq⟩
    · obtain ⟨hm, k, hk, hdk⟩ := ih hxy
      exact ⟨List.mem_cons_of_mem _ hm, k, Nat.lt_succ_of_lt hk, hdk⟩

private lemma walkVerts_append (E : List (ℕ × ℕ)) {u x : ℕ} {es₁ es₂ : List ℕ}
    (h1 : IsEdgeWalk E u x es₁) :
    walkVerts E u (es₁ ++ es₂) = (walkVerts E u es₁).dropLast ++ walkVerts E x es₂ := by
  induction h1 with
  | nil u => simp [walkVerts]
  | cons hj hend hrest ih =>
    rename_i u' x' v' j' es'
    simp only [List.cons_append, walkVerts, walkStep_of_hend hend, ih]
    cases es' with
    | nil => simp [walkVerts]
    | cons j'' es'' => simp [walkVerts]

private lemma TrailValid.to_walk {G : Graph} {X V : Finset ℕ} {dist : ℕ → Option ℕ}
    {s u r : ℕ} {trail : List (ℕ × ℕ)} (h : TrailValid G X dist s u r trail)
    (hsub : ∀ w ∈ stackVerts u trail, w ∈ V) :
    IsEdgeWalkIn G V s u (trail.map Prod.snd).reverse ∧
    walkVerts G.edges s (trail.map Prod.snd).reverse = (stackVerts u trail).reverse := by
  induction h with
  | nil =>
    exact ⟨IsEdgeWalkIn.nil G V s, rfl⟩
  | @cons u' p' e' r' rest' hadj _ hrest ih =>
    have hu'V : u' ∈ V := hsub u' (by simp [stackVerts])
    have hp'sub : ∀ w ∈ stackVerts p' rest', w ∈ V :=
      fun w hw => hsub w (List.mem_cons_of_mem _ hw)
    have hp'V : p' ∈ V := hp'sub p' (by simp [stackVerts])
    obtain ⟨hw_rest, hv_rest⟩ := ih hp'sub
    have hstep : IsEdgeWalkIn G V p' u' [e'] :=
      IsEdgeWalkIn.cons_of_adj hadj hp'V hu'V (IsEdgeWalkIn.nil G V u')
    have hw_all : IsEdgeWalkIn G V s u' ((rest'.map Prod.snd).reverse ++ [e']) :=
      hw_rest.append hstep
    refine ⟨by simpa using hw_all, ?_⟩
    simp only [List.map_cons, List.reverse_cons]
    rw [walkVerts_append G.edges hw_rest.1, hv_rest]
    have hstep_verts : walkVerts G.edges p' [e'] = [p', u'] := by
      rcases hstep.1 with _ | ⟨_, hend, hnil⟩
      cases hnil
      simp [walkVerts, walkStep_of_hend hend]
    rw [hstep_verts]
    have hne : (stackVerts p' rest').reverse ≠ [] := by simp [stackVerts]
    have hlast : (stackVerts p' rest').reverse.getLast hne = p' := by
      simp [stackVerts]
    have hdrop : (stackVerts p' rest').reverse.dropLast ++ [p'] = (stackVerts p' rest').reverse := by
      have h := List.dropLast_append_getLast hne
      rwa [hlast] at h
    calc
      (stackVerts p' rest').reverse.dropLast ++ [p', u']
          = ((stackVerts p' rest').reverse.dropLast ++ [p']) ++ [u'] := by simp
      _ = (stackVerts p' rest').reverse ++ [u'] := by rw [hdrop]
      _ = (stackVerts u' ((p', e') :: rest')).reverse := by simp [stackVerts]


/-- Invariant during `dfsStep` with active stack `(u, r, trail)`. -/
private structure StackInv (G : Graph) (X V S T : Finset ℕ) (dist : ℕ → Option ℕ) (j s : ℕ)
    (u r : ℕ) (trail : List (ℕ × ℕ)) (st : DFSState) : Prop where
  used_sub : st.used ⊆ V
  dead_sub : st.dead ⊆ V
  dead_closed : DeadClosed G X V T dist j st.used st.dead
  r_le : r ≤ j
  s_mem : s ∈ S ∩ V
  trail_valid : TrailValid G X dist s u r trail
  stack_avail : ∀ w ∈ stackVerts u trail, w ∈ V ∧ w ∉ st.used ∧ w ∉ st.dead
  cursor_inv : ∀ w ∈ V, ∃ pref, adjOf G X w = pref ++ st.cursor w ∧
    ∀ p ∈ pref, p.1 ∈ V → ∀ rw < j, dist w = some rw → dist p.1 = some (rw + 1) →
      w ∉ st.used → p.1 ∈ st.used ∪ st.dead ∨ (w, p.1) ∈ stackEdges u trail
  used_eq : st.used = routedVerts G st.paths
  paths_valid : ∀ p ∈ st.paths,
    p.1.1 ∈ S ∩ V ∧ p.1.2 ∈ T ∩ V ∧ p.2.length = j ∧ IsSimpleWalkIn G V p.1.1 p.1.2 p.2
  paths_disj : st.paths.Pairwise fun p q =>
    Disjoint (walkVerts G.edges p.1.1 p.2).toFinset (walkVerts G.edges q.1.1 q.2).toFinset

private lemma dfsStep_spec (G : Graph) (X V S T : Finset ℕ) (dist : ℕ → Option ℕ) (j s : ℕ)
    (hno_early_T : ∀ t ∈ T ∩ V, ∀ r < j, dist t ≠ some r)
    (fuel u r : ℕ) (trail : List (ℕ × ℕ)) (st : DFSState)
    (hfuel : dfsPot V st < fuel)
    (hinv : StackInv G X V S T dist j s u r trail st) :
    let st' := dfsStep V T dist j s fuel u r trail st
    DFSInv G X V S T dist j st' ∧
    st.used ⊆ st'.used ∧
    st.dead ⊆ st'.dead ∧
    s ∈ st'.used ∪ st'.dead ∧
    dfsPot V st' ≤ dfsPot V st ∧
    st'.cost + dfsPot V st' + 2 * (V.card - st'.used.card) ≤
      st.cost + dfsPot V st + 2 * (V.card - st.used.card) := by
  induction fuel generalizing u r trail st with
  | zero => exact absurd hfuel (Nat.not_lt_zero _)
  | succ fuel ih =>
    simp only [dfsStep]
    have hu_avail := hinv.stack_avail u (by simp [stackVerts])
    rcases hu_avail with ⟨huV, huUsed, huDead⟩
    -- Case 1: `u ∈ T` -> found a path!
    by_cases huT : u ∈ T
    · simp only [huT, ↓reduceIte]
      have hr_eq : r = j := by
        by_contra hne
        have hlt : r < j := lt_of_le_of_ne hinv.r_le hne
        exact hno_early_T u (Finset.mem_inter.mpr ⟨huT, huV⟩) r hlt hinv.trail_valid.dist_eq
      set es := (trail.map Prod.snd).reverse
      set vs := stackVerts u trail
      have hvs_subV : ∀ w ∈ vs, w ∈ V := fun w hw => (hinv.stack_avail w hw).1
      have hvs_not_used : Disjoint st.used vs.toFinset := by
        rw [Finset.disjoint_right]
        intro w hw
        rw [List.mem_toFinset] at hw
        exact (hinv.stack_avail w hw).2.1
      have hvs_nd : vs.Nodup := hinv.trail_valid.nodup_stackVerts
      obtain ⟨hwalk, hverts⟩ := hinv.trail_valid.to_walk hvs_subV
      have hwalk_verts_nd : (walkVerts G.edges s es).Nodup := by
        rw [hverts]; exact List.nodup_reverse.mpr hvs_nd
      have hverts_finset : (walkVerts G.edges s es).toFinset = vs.toFinset := by
        rw [hverts]; ext x; simp [vs]
      have hes_len : es.length = j := by
        simp [es, hinv.trail_valid.length_eq, hr_eq]
      have hused'_sub : st.used ∪ vs.toFinset ⊆ V :=
        Finset.union_subset hinv.used_sub (fun w hw => hvs_subV w (List.mem_toFinset.mp hw))
      have hcard_used' : (st.used ∪ vs.toFinset).card = st.used.card + vs.length := by
        rw [Finset.card_union_of_disjoint hvs_not_used, List.toFinset_card_of_nodup hvs_nd]
      have hcard_le : (st.used ∪ vs.toFinset).card ≤ V.card := Finset.card_le_card hused'_sub
      have hvs_pos : 1 ≤ vs.length := by simp [vs, stackVerts]
      have hdfsInv : DFSInv G X V S T dist j
          { used := st.used ∪ vs.toFinset, dead := st.dead, cursor := st.cursor,
            paths := ((s, u), es) :: st.paths, cost := st.cost + vs.length + 1 } :=
        { used_sub := hused'_sub
          dead_sub := hinv.dead_sub
          dead_closed := fun w hw => by
            obtain ⟨hwT, hstep⟩ := hinv.dead_closed w hw
            refine ⟨hwT, fun p hp hpV r' hr' hdw hdp => ?_⟩
            have hm := hstep p hp hpV r' hr' hdw hdp
            simp only [Finset.mem_union] at hm ⊢
            tauto
          cursor_inv := fun w hwV => by
            obtain ⟨pref, hEq, hpref⟩ := hinv.cursor_inv w hwV
            refine ⟨pref, hEq, fun p hp hpV rw hrw hdw hdp hwNotUsed' => ?_⟩
            have hwNotUsed : w ∉ st.used := fun h => hwNotUsed' (Finset.mem_union_left _ h)
            have hwNotVs : w ∉ vs := fun h => hwNotUsed' (Finset.mem_union_right _ (List.mem_toFinset.mpr h))
            rcases hpref p hp hpV rw hrw hdw hdp hwNotUsed with h1 | h2
            · simp only [Finset.mem_union] at h1 ⊢; tauto
            · obtain ⟨hm_par, _⟩ := hinv.trail_valid.mem_stackEdges_fst_lt h2
              exact absurd (List.mem_cons_of_mem _ hm_par) hwNotVs
          used_eq := by
            rw [routedVerts_cons, hverts_finset, ← hinv.used_eq, Finset.union_comm]
          paths_valid := fun p hp => by
            rcases List.mem_cons.mp hp with rfl | hp
            · exact ⟨hinv.s_mem, Finset.mem_inter.mpr ⟨huT, huV⟩, hes_len, hwalk, hwalk_verts_nd⟩
            · exact hinv.paths_valid p hp
          paths_disj := by
            rw [List.pairwise_cons]
            refine ⟨fun q hq => ?_, hinv.paths_disj⟩
            rw [hverts_finset, Finset.disjoint_left]
            intro w hw1 hw2
            rw [List.mem_toFinset] at hw2
            have hwUsed : w ∈ st.used := by
              rw [hinv.used_eq, mem_routedVerts_iff]
              exact ⟨q, hq, hw2⟩
            exact Finset.disjoint_left.mp hvs_not_used hwUsed hw1 }
      refine ⟨hdfsInv, Finset.subset_union_left, Finset.Subset.refl _, ?_, le_refl _, ?_⟩
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (List.mem_toFinset.mpr hinv.trail_valid.root_mem_stackVerts))
      · dsimp only [dfsPot]
        omega
    · simp only [huT, ↓reduceIte]
      -- Helper to close both "mark `u` dead and backtrack" branches (`r = j` or `cursor u = []`):
      have hbacktrack :
          (∀ p ∈ adjOf G X u, p.1 ∈ V → ∀ rw < j, dist u = some rw → dist p.1 = some (rw + 1) →
            p.1 ∈ st.used ∪ st.dead) →
          let st1 : DFSState := { st with dead := insert u st.dead, cost := st.cost + 1 }
          let res := match (motive := List (ℕ × ℕ) → DFSState) trail with
            | [] => st1
            | (p, _) :: rest => dfsStep V T dist j s fuel p (r - 1) rest st1
          DFSInv G X V S T dist j res ∧
          st.used ⊆ res.used ∧
          st.dead ⊆ res.dead ∧
          s ∈ res.used ∪ res.dead ∧
          dfsPot V res ≤ dfsPot V st ∧
          res.cost + dfsPot V res + 2 * (V.card - res.used.card) ≤
            st.cost + dfsPot V st + 2 * (V.card - st.used.card) := by
        intro hu_closed
        set st1 : DFSState := { st with dead := insert u st.dead, cost := st.cost + 1 }
        have hpot1 : dfsPot V st1 + 1 = dfsPot V st := dfsPot_insert_dead V st huV huDead
        have hdead1_sub : st1.dead ⊆ V := Finset.insert_subset_iff.mpr ⟨huV, hinv.dead_sub⟩
        have hdead1_closed : DeadClosed G X V T dist j st1.used st1.dead := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · refine ⟨huT, fun p hp hpV rw hrw hdw hdp => ?_⟩
            have hm := hu_closed p hp hpV rw hrw hdw hdp
            simp only [st1, Finset.mem_union, Finset.mem_insert] at hm ⊢
            tauto
          · obtain ⟨hwT, hstep⟩ := hinv.dead_closed w hw
            refine ⟨hwT, fun p hp hpV rw hrw hdw hdp => ?_⟩
            have hm := hstep p hp hpV rw hrw hdw hdp
            simp only [st1, Finset.mem_union, Finset.mem_insert] at hm ⊢
            tauto
        have hst1_card : st1.used.card = st.used.card := rfl
        have hst1_cost : st1.cost = st.cost + 1 := rfl
        rcases hinv with ⟨hused_sub, hdead_sub, hdead_closed, hr_le, hs_mem, htv, hstack_avail,
          hcursor_inv, hused_eq, hpaths_valid, hpaths_disj⟩
        cases htv with
        | nil =>
          dsimp only
          have hdfsInv : DFSInv G X V S T dist j st1 :=
            { used_sub := hused_sub
              dead_sub := hdead1_sub
              dead_closed := hdead1_closed
              cursor_inv := fun w hwV => by
                obtain ⟨pref, hEq, hpref⟩ := hcursor_inv w hwV
                refine ⟨pref, hEq, fun p hp hpV rw hrw hdw hdp hwNotUsed => ?_⟩
                rcases hpref p hp hpV rw hrw hdw hdp hwNotUsed with h1 | h2
                · simp only [st1, Finset.mem_union, Finset.mem_insert] at h1 ⊢; tauto
                · simp [stackEdges] at h2
              used_eq := hused_eq
              paths_valid := hpaths_valid
              paths_disj := hpaths_disj }
          refine ⟨hdfsInv, Finset.Subset.refl _, Finset.subset_insert _ _, ?_, by omega, by omega⟩
          exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
        | @cons _ p e r' rest hadj_pu hdu_succ hrest =>
          dsimp only
          have hstack1_avail : ∀ w ∈ stackVerts p rest, w ∈ V ∧ w ∉ st1.used ∧ w ∉ st1.dead := by
            intro w hw
            have hw0 := hstack_avail w (List.mem_cons_of_mem _ hw)
            refine ⟨hw0.1, hw0.2.1, ?_⟩
            intro hwD1
            rcases Finset.mem_insert.mp hwD1 with rfl | hwD0
            · have hnd := (TrailValid.cons hadj_pu hdu_succ hrest).nodup_stackVerts
              exact (List.nodup_cons.mp hnd).1 hw
            · exact hw0.2.2 hwD0
          have hstack1_inv : StackInv G X V S T dist j s p r' rest st1 :=
            { used_sub := hused_sub
              dead_sub := hdead1_sub
              dead_closed := hdead1_closed
              r_le := by omega
              s_mem := hs_mem
              trail_valid := hrest
              stack_avail := hstack1_avail
              cursor_inv := fun w hwV => by
                obtain ⟨pref, hEq, hpref⟩ := hcursor_inv w hwV
                refine ⟨pref, hEq, fun q hq hqV rw hrw hdw hdq hwNotUsed => ?_⟩
                rcases hpref q hq hqV rw hrw hdw hdq hwNotUsed with h1 | h2
                · left; simp only [st1, Finset.mem_union, Finset.mem_insert] at h1 ⊢; tauto
                · simp only [stackEdges, List.mem_cons, Prod.mk.injEq] at h2
                  rcases h2 with ⟨rfl, rfl⟩ | h2
                  · left; exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
                  · exact Or.inr h2
              used_eq := hused_eq
              paths_valid := hpaths_valid
              paths_disj := hpaths_disj }
          have hrec := ih p r' rest st1 (by omega) hstack1_inv
          rcases hrec with ⟨h1, h2, h3, h4, h5, h6⟩
          have hsub_eq : r' + 1 - 1 = r' := rfl
          rw [hsub_eq]
          refine ⟨h1, h2, le_trans (Finset.subset_insert _ _) h3, h4, by omega, by omega⟩
      -- Case 2: `r = j` (and `u ∉ T`) -> backtrack immediately!
      by_cases hrj : r = j
      · simp only [eq_true hrj, ↓reduceIte]
        exact hbacktrack fun _ _ _ rw hrw hdw _ => by
          rw [hinv.trail_valid.dist_eq, hrj] at hdw
          have : j = rw := Option.some.inj hdw
          omega
      · simp only [eq_false hrj, ↓reduceIte]
        have hr_lt : r < j := lt_of_le_of_ne hinv.r_le hrj
        -- Case 3: inspect `st.cursor u`:
        cases hcur : st.cursor u with
        | nil =>
          dsimp only
          apply hbacktrack
          intro p hp hpV rw hrw hdw hdp
          obtain ⟨pref, hEq, hpref⟩ := hinv.cursor_inv u huV
          rw [hcur, List.append_nil] at hEq
          have hp_pref : p ∈ pref := hEq ▸ hp
          rcases hpref p hp_pref hpV rw hrw hdw hdp huUsed with h1 | h2
          · exact h1
          · obtain ⟨_, k, hk, hdu'⟩ := hinv.trail_valid.mem_stackEdges_fst_lt h2
            rw [hinv.trail_valid.dist_eq] at hdu'
            have : r = k := Option.some.inj hdu'
            omega
        | cons we rest =>
          rcases we with ⟨w, e⟩
          dsimp only
          set st1 : DFSState :=
            { st with cursor := Function.update st.cursor u rest, cost := st.cost + 1 }
          have hpot1 : dfsPot V st1 + 1 = dfsPot V st :=
            dfsPot_update_tail V st huV hcur
          -- Subcase 3a: valid layered step `(w, e)` -> push onto stack!
          by_cases hpush : w ∈ V ∧ w ∉ st.used ∧ w ∉ st.dead ∧ r < j ∧ dist w = some (r + 1)
          · simp only [eq_true hpush, ↓reduceIte]
            rcases hpush with ⟨hwV, hwUsed, hwDead, _, hdw⟩
            have hadj_uw : (w, e) ∈ adjOf G X u := by
              obtain ⟨pref, hEq, _⟩ := hinv.cursor_inv u huV
              rw [hEq, hcur]
              exact List.mem_append_right _ List.mem_cons_self
            have htv1 : TrailValid G X dist s w (r + 1) ((u, e) :: trail) :=
              TrailValid.cons hadj_uw hdw hinv.trail_valid
            have hstack1_inv : StackInv G X V S T dist j s w (r + 1) ((u, e) :: trail) st1 :=
              { used_sub := hinv.used_sub
                dead_sub := hinv.dead_sub
                dead_closed := hinv.dead_closed
                r_le := by omega
                s_mem := hinv.s_mem
                trail_valid := htv1
                stack_avail := fun x hx => by
                  rcases List.mem_cons.mp hx with rfl | hx
                  · exact ⟨hwV, hwUsed, hwDead⟩
                  · exact hinv.stack_avail x hx
                cursor_inv := fun x hxV => by
                  obtain ⟨pref, hEq, hpref⟩ := hinv.cursor_inv x hxV
                  by_cases hxu : x = u
                  · subst hxu
                    refine ⟨pref ++ [(w, e)], ?_, ?_⟩
                    · simp only [st1, Function.update_self, List.append_assoc, List.singleton_append]
                      rw [← hcur, hEq]
                    · intro q hq hqV rx hrx hdx hdq hxNotUsed
                      rcases List.mem_append.mp hq with hq | hq
                      · rcases hpref q hq hqV rx hrx hdx hdq hxNotUsed with h1 | h2
                        · exact Or.inl h1
                        · exact Or.inr (List.mem_cons_of_mem _ h2)
                      · simp only [List.mem_singleton] at hq
                        subst hq
                        exact Or.inr List.mem_cons_self
                  · refine ⟨pref, ?_, ?_⟩
                    · simp only [st1, Function.update_of_ne hxu]; exact hEq
                    · intro q hq hqV rx hrx hdx hdq hxNotUsed
                      rcases hpref q hq hqV rx hrx hdx hdq hxNotUsed with h1 | h2
                      · exact Or.inl h1
                      · exact Or.inr (List.mem_cons_of_mem _ h2)
                used_eq := hinv.used_eq
                paths_valid := hinv.paths_valid
                paths_disj := hinv.paths_disj }
            have hrec := ih w (r + 1) ((u, e) :: trail) st1 (by omega) hstack1_inv
            rcases hrec with ⟨h1, h2, h3, h4, h5, h6⟩
            have hst1_card : st1.used.card = st.used.card := rfl
            have hst1_cost : st1.cost = st.cost + 1 := rfl
            exact ⟨h1, h2, h3, h4, by omega, by omega⟩
          · -- Subcase 3b: skip `(w, e)` and continue at `(u, r, trail)`!
            simp only [eq_false hpush, ↓reduceIte]
            have hstack1_inv : StackInv G X V S T dist j s u r trail st1 :=
              { used_sub := hinv.used_sub
                dead_sub := hinv.dead_sub
                dead_closed := hinv.dead_closed
                r_le := hinv.r_le
                s_mem := hinv.s_mem
                trail_valid := hinv.trail_valid
                stack_avail := hinv.stack_avail
                cursor_inv := fun x hxV => by
                  obtain ⟨pref, hEq, hpref⟩ := hinv.cursor_inv x hxV
                  by_cases hxu : x = u
                  · subst hxu
                    refine ⟨pref ++ [(w, e)], ?_, ?_⟩
                    · simp only [st1, Function.update_self, List.append_assoc, List.singleton_append]
                      rw [← hcur, hEq]
                    · intro q hq hqV rx hrx hdx hdq hxNotUsed
                      rcases List.mem_append.mp hq with hq | hq
                      · exact hpref q hq hqV rx hrx hdx hdq hxNotUsed
                      · simp only [List.mem_singleton] at hq
                        subst hq
                        left
                        rw [hinv.trail_valid.dist_eq] at hdx
                        have hr_eq : r = rx := Option.some.inj hdx
                        subst hr_eq
                        by_contra hnot
                        rw [Finset.mem_union, not_or] at hnot
                        exact hpush ⟨hqV, hnot.1, hnot.2, hr_lt, hdq⟩
                  · refine ⟨pref, ?_, hpref⟩
                    simp only [st1, Function.update_of_ne hxu]; exact hEq
                used_eq := hinv.used_eq
                paths_valid := hinv.paths_valid
                paths_disj := hinv.paths_disj }
            have hrec := ih u r trail st1 (by omega) hstack1_inv
            rcases hrec with ⟨h1, h2, h3, h4, h5, h6⟩
            have hst1_card : st1.used.card = st.used.card := rfl
            have hst1_cost : st1.cost = st.cost + 1 := rfl
            exact ⟨h1, h2, h3, h4, by omega, by omega⟩

theorem dfsSources_spec (G : Graph) (X V S T : Finset ℕ) (dist : ℕ → Option ℕ) (j fuel : ℕ)
    (hdist_zero : ∀ v, dist v = some 0 ↔ v ∈ S ∩ V)
    (hno_early_T : ∀ t ∈ T ∩ V, ∀ r < j, dist t ≠ some r)
    (sources : List ℕ) (hsources : ∀ s ∈ sources, s ∈ S ∩ V)
    (st : DFSState) (hfuel : dfsPot V st < fuel)
    (hinv : DFSInv G X V S T dist j st) :
    let st' := dfsSources V T dist j fuel sources st
    DFSInv G X V S T dist j st' ∧
    st.used ⊆ st'.used ∧
    st.dead ⊆ st'.dead ∧
    (∀ s ∈ sources, s ∈ st'.used ∪ st'.dead) ∧
    st'.cost + dfsPot V st' + 2 * (V.card - st'.used.card) ≤
      st.cost + sources.length + dfsPot V st + 2 * (V.card - st.used.card) := by
  induction sources generalizing st with
  | nil =>
    simp only [dfsSources, List.length_nil]
    exact ⟨hinv, Finset.Subset.refl _, Finset.Subset.refl _, by simp, by omega⟩
  | cons s rest ih =>
    simp only [dfsSources]
    set st0 : DFSState := { st with cost := st.cost + 1 }
    have hpot0 : dfsPot V st0 = dfsPot V st := rfl
    have hst0_card : st0.used.card = st.used.card := rfl
    have hst0_cost : st0.cost = st.cost + 1 := rfl
    have hsSV : s ∈ S ∩ V := hsources s List.mem_cons_self
    have hsV : s ∈ V := (Finset.mem_inter.mp hsSV).2
    have hrest_sub : ∀ s' ∈ rest, s' ∈ S ∩ V := fun s' hs' => hsources s' (List.mem_cons_of_mem _ hs')
    by_cases hskip : s ∈ st.used ∨ s ∈ st.dead
    · simp only [hskip, ↓reduceIte]
      have hinv0 : DFSInv G X V S T dist j st0 :=
        { used_sub := hinv.used_sub
          dead_sub := hinv.dead_sub
          dead_closed := hinv.dead_closed
          cursor_inv := hinv.cursor_inv
          used_eq := hinv.used_eq
          paths_valid := hinv.paths_valid
          paths_disj := hinv.paths_disj }
      have hrec := ih hrest_sub st0 (by omega) hinv0
      rcases hrec with ⟨h1, h2, h3, h4, h5⟩
      refine ⟨h1, h2, h3, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · rcases hskip with hsU | hsD
          · exact Finset.mem_union_left _ (h2 hsU)
          · exact Finset.mem_union_right _ (h3 hsD)
        · exact h4 x hx
      · simp only [List.length_cons]
        omega
    · simp only [hskip, ↓reduceIte]
      rw [not_or] at hskip
      have hst0_inv : StackInv G X V S T dist j s s 0 [] st0 :=
        { used_sub := hinv.used_sub
          dead_sub := hinv.dead_sub
          dead_closed := hinv.dead_closed
          r_le := Nat.zero_le _
          s_mem := hsSV
          trail_valid := TrailValid.nil ((hdist_zero s).mpr hsSV)
          stack_avail := fun w hw => by
            simp only [stackVerts, List.map_nil, List.mem_singleton] at hw
            subst hw
            exact ⟨hsV, hskip.1, hskip.2⟩
          cursor_inv := fun w hwV => by
            obtain ⟨pref, hEq, hpref⟩ := hinv.cursor_inv w hwV
            exact ⟨pref, hEq, fun p hp hpV rw hrw hdw hdp hwU =>
              Or.inl (hpref p hp hpV rw hrw hdw hdp hwU)⟩
          used_eq := hinv.used_eq
          paths_valid := hinv.paths_valid
          paths_disj := hinv.paths_disj }
      have hstep := dfsStep_spec G X V S T dist j s hno_early_T fuel s 0 [] st0 (by omega) hst0_inv
      set st1 := dfsStep V T dist j s fuel s 0 [] st0
      rcases hstep with ⟨hinv1, hsubU1, hsubD1, hsIn1, hpot1, hcost1⟩
      have hrec := ih hrest_sub st1 (by omega) hinv1
      rcases hrec with ⟨h1, h2, h3, h4, h5⟩
      refine ⟨h1, le_trans hsubU1 h2, le_trans hsubD1 h3, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · rcases Finset.mem_union.mp hsIn1 with hsU | hsD
          · exact Finset.mem_union_left _ (h2 hsU)
          · exact Finset.mem_union_right _ (h3 hsD)
        · exact h4 x hx
      · simp only [List.length_cons]
        omega


end MinCostFlow.ExpanderDecomp
