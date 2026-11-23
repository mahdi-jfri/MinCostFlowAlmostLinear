module

public import MinCostFlow.MinRatio.PathTreeContract

/-!
# Ready edges and ready summaries

An edge is ready when its value has a non-negative detector. Find-ready must decide whether any
edge of the whole forest is ready. This file gives the facts that let it look only at the roots
of the auxiliary trees:

* a summary of a list of values reports a ready value exactly when some value in the list is
  ready (`sumReady_listSummary`);
* the value that an expose shows for a node is the value paired with the node in the forest's
  list of evaluated pairs (`lctExpose_val_mem_forestPairs`).

The root of an auxiliary tree keeps the summary of all evaluated pairs of its tree
(`SubtreeInv`), so the forest has a ready edge exactly when some root summary is ready, as long
as only edges carry values.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathTree

open MinCostFlow.MinRatio MinCostFlow.LinkCut

/-- A summary reports a ready value: its detector maximum exists and is non-negative. -/
def SumReady (s : PathSummary) : Prop := ∃ z, s.detector = some z ∧ 0 ≤ z

/-- An evaluated pair holds a ready value. -/
def PairReady (p : ℕ × Option PathEdgeValue) : Prop := ∃ v, p.2 = some v ∧ 0 ≤ v.detector

theorem detectorMax_ready (a b : Option ℤ) :
    (∃ z, detectorMax a b = some z ∧ 0 ≤ z) ↔
      (∃ z, a = some z ∧ 0 ≤ z) ∨ (∃ z, b = some z ∧ 0 ≤ z) := by
  cases a with
  | none => simp [detectorMax]
  | some x =>
    cases b with
    | none => simp [detectorMax]
    | some y =>
      simp only [detectorMax, Option.some.injEq, exists_eq_left']
      constructor
      · intro h; by_cases hx : 0 ≤ x
        · exact Or.inl hx
        · exact Or.inr (by rcases le_total x y with hxy | hxy <;> simp_all [max_eq_left, max_eq_right])
      · rintro (h | h)
        · exact le_trans h (le_max_left _ _)
        · exact le_trans h (le_max_right _ _)

/-- A summary of a list is ready exactly when some pair of the list is ready. -/
theorem sumReady_listSummary (ps : List (ℕ × Option PathEdgeValue)) :
    SumReady (pathPayload.listSummary ps) ↔ ∃ p ∈ ps, PairReady p := by
  induction ps with
  | nil => simp [SumReady, pathPayload, PathSummary.empty]
  | cons p rest ih =>
    obtain ⟨id, v⟩ := p
    rw [LctPayload.listSummary_cons]
    change (∃ z, detectorMax (PathSummary.single v).detector
      (pathPayload.listSummary rest).detector = some z ∧ 0 ≤ z) ↔ _
    rw [detectorMax_ready]
    change _ ∨ SumReady _ ↔ _
    rw [ih]
    simp only [List.mem_cons, exists_eq_or_imp]
    apply or_congr_left
    cases v with
    | none => simp [PathSummary.single, PathSummary.empty, PairReady]
    | some e => simp [PathSummary.single, PairReady]

/-- The value an expose shows for `x` is the value paired with `x` in the forest's pairs. -/
theorem lctExpose_val_mem_forestPairs {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} (W : LctInvWith pathPayload s trees free depth)
    {tv : AuxTree} {x : ℕ} (htv : tv ∈ trees) (hx : x ∈ tv.toList) :
    (x, ((lctExpose pathPayload s x).splay.nodes x).val) ∈
      forestPairs pathPayload s.splay trees := by
  obtain ⟨trees', Lv, hmem, -, -, -, hpairs, -, -, -, -, -⟩ :=
    lctExpose_spec pathPayload_laws W htv hx
  refine hpairs.subset ?_
  unfold forestPairs
  refine List.mem_flatMap.mpr ⟨_, hmem, ?_⟩
  simp only [SplayState.evalPairs, Bool.false_eq_true, ↓reduceIte, List.mem_append,
    List.mem_singleton]
  refine Or.inl (Or.inr ?_)
  rw [pathPayload_laws.actVal_id]
  rfl

theorem forestPairs_fst_perm (s : SplayState (Option PathEdgeValue) PathSummary PathTag)
    (ts : List AuxTree) :
    ((forestPairs pathPayload s ts).map Prod.fst).Perm (ts.flatMap AuxTree.toList) := by
  induction ts with
  | nil => simp [forestPairs]
  | cons t rest ih =>
    simp only [forestPairs, List.flatMap_cons, List.map_append] at ih ⊢
    have ht : ((SplayState.evalPairs pathPayload s t false pathPayload.idTag).map
        Prod.fst).Perm t.toList := by
      rw [SplayState.evalPairs_map_fst]
      exact t.evalInorder_perm _ _
    exact ht.append ih

theorem pair_unique {β γ : Type*} {l : List (β × γ)} (hnd : (l.map Prod.fst).Nodup)
    {x : β} {y₁ y₂ : γ} (h1 : (x, y₁) ∈ l) (h2 : (x, y₂) ∈ l) : y₁ = y₂ := by
  induction l with
  | nil => simp at h1
  | cons p rest ih =>
    rcases p with ⟨k, v⟩
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp h1 with h1eq | h1' <;> rcases List.mem_cons.mp h2 with h2eq | h2'
    · exact (congrArg Prod.snd h1eq).trans (congrArg Prod.snd h2eq).symm
    · exfalso; rw [← h1eq] at hnd; exact hnd.1 (List.mem_map.mpr ⟨(x, y₂), h2', rfl⟩)
    · exfalso; rw [← h2eq] at hnd; exact hnd.1 (List.mem_map.mpr ⟨(x, y₁), h1', rfl⟩)
    · exact ih hnd.2 h1' h2'

/-- An evaluated pair holds a value only if the node stores one. -/
theorem evalPairs_some_stored (s : SplayState (Option PathEdgeValue) PathSummary PathTag) :
    ∀ (t : AuxTree) (flip : Bool) (acc : PathTag) {y : ℕ} {v : PathEdgeValue},
      (y, some v) ∈ SplayState.evalPairs pathPayload s t flip acc →
        (s.nodes y).val ≠ none
  | .leaf, _, _, _, _, h => by simp [SplayState.evalPairs] at h
  | .node id l r, flip, acc, y, v, h => by
    simp only [SplayState.evalPairs] at h
    split_ifs at h <;>
    · simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at h
      rcases h with (h | ⟨rfl, hv⟩) | h
      · exact evalPairs_some_stored s _ _ _ h
      · intro hn; simp [hn, pathPayload] at hv
      · exact evalPairs_some_stored s _ _ _ h

/-- Only edges hold values. Every reachable state has this property. -/
def ValsOnEdges (s : PathTreeState) : Prop :=
  ∀ x, isVertex s.n x → (s.splay.nodes x).val = none

/-- Some edge of the forest is ready exactly when the summary at the root of some auxiliary tree
is ready. -/
theorem exists_ready_iff {s : PathTreeState} {trees : List AuxTree} {free : List ℕ}
    {depth : ℕ → ℕ} (W : LctInvWith pathPayload s trees free depth) (hE : ValsOnEdges s) :
    (∃ x, pathTreeReady s x) ↔ ∃ t ∈ trees, SumReady (s.splay.nodes t.rootId).sum := by
  have hnd : ((forestPairs pathPayload s.splay trees).map Prod.fst).Nodup :=
    (forestPairs_fst_perm _ _).nodup_iff.mpr W.activeNodup
  -- the root summary of a tree is the summary of its pairs
  have hroot : ∀ t ∈ trees, (s.splay.nodes t.rootId).sum =
      pathPayload.listSummary (SplayState.evalPairs pathPayload s.splay t false
        pathPayload.idTag) := by
    intro t ht
    have hsub := (W.treesInv t ht).sub
    cases t with
    | leaf => exact absurd rfl (W.treesNonEmpty _ ht)
    | node id l r => exact hsub.2.2.2.2.2.2.1
  constructor
  · rintro ⟨x, -, ⟨trees₀, free₀, depth₀, W₀, hxa⟩, v, hv, hd⟩
    have hxa' : x ∈ trees.flatMap AuxTree.toList :=
      (LctInvWith_canon_perm W).2.1.subset ((LctInvWith_canon_perm W₀).2.1.symm.subset hxa)
    obtain ⟨tv, htv, hxt⟩ := List.mem_flatMap.mp hxa'
    have hm := lctExpose_val_mem_forestPairs W htv hxt
    rw [hv] at hm
    obtain ⟨t, ht, hpt⟩ := List.mem_flatMap.mp hm
    refine ⟨t, ht, ?_⟩
    rw [hroot t ht, sumReady_listSummary]
    exact ⟨_, hpt, v, rfl, hd⟩
  · rintro ⟨t, ht, hr⟩
    rw [hroot t ht, sumReady_listSummary] at hr
    obtain ⟨⟨y, w⟩, hp, v, rfl, hd⟩ := hr
    have hyt : y ∈ t.toList := by
      have := List.mem_map_of_mem (f := Prod.fst) hp
      rw [SplayState.evalPairs_map_fst] at this
      exact (t.evalInorder_perm _ _).subset this
    have hya : y ∈ trees.flatMap AuxTree.toList := List.mem_flatMap.mpr ⟨t, ht, hyt⟩
    have hval : (s.splay.nodes y).val ≠ none := evalPairs_some_stored _ _ _ _ hp
    have hnode := W.activeValid y hya
    have hedge : isEdgeSlot s.n y := by
      by_cases hv' : isVertex s.n y
      · exact absurd (hE y hv') hval
      · unfold isVertex at hv'; unfold isNode at hnode; exact ⟨by omega, hnode.2⟩
    refine ⟨y, hedge, ⟨trees, free, depth, W, hya⟩, v, ?_, hd⟩
    exact pair_unique hnd (lctExpose_val_mem_forestPairs W ht hyt)
      (List.mem_flatMap.mpr ⟨t, ht, hp⟩)

end MinCostFlow.LinkCut.PathTree
