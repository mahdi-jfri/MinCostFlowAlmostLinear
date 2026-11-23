module

public import MinCostFlow.LinkCut.PathTree.FindModel
public import MinCostFlow.LinkCut.PathTree.Acc
import MinCostFlow.LinkCut.ForestReversals

/-!
# The invariant of the ready index

Find-ready keeps a stack `S` of node ids. The invariant (`ReadyIdx`) is that the root of every
auxiliary tree with a ready summary is on the stack. Find-ready looks at the top entry `x` and
tests it with `ValidRoot`, which reads only the record of `x`: `x` is a node, it has parent `0`,
its summary is ready, and it has a child or a path parent.

* `validRoot_root`: a valid entry is the root of an auxiliary tree. This needs that free slots
  have no children and no path parent (`FreeShape`), since a free slot may keep an old summary.
* `root_validRoot`: the root of an auxiliary tree with a ready summary is valid. A root with no
  child and no path parent is a whole represented tree by itself, so it is a vertex, and a
  vertex holds no value.
* `readyIdx_pop`: an invalid top entry can be dropped.
* `readyIdx_step`: after a change of state where every new root is noted (`RootAcc`), the
  invariant holds for the stack with the noted nodes added.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathTree

open MinCostFlow.MinRatio MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen

/-- The root of every auxiliary tree with a ready summary is on the stack. -/
def ReadyIdx (s : PathTreeState) (trees : List AuxTree) (S : List ℕ) : Prop :=
  ∀ t ∈ trees, pathRs (s.splay.nodes t.rootId).sum = true → t.rootId ∈ S

/-- Free slots have no children and no path parent. -/
def FreeShape (s : PathTreeState) (free : List ℕ) : Prop :=
  ∀ e ∈ free, (s.splay.nodes e).left = 0 ∧ (s.splay.nodes e).right = 0 ∧
    (s.splay.nodes e).ppar = 0

/-- The test find-ready makes on the top entry `x` of the stack. -/
def ValidRoot (s : PathTreeState) (x : ℕ) : Prop :=
  1 ≤ x ∧ x < 2 * s.n ∧ (s.splay.nodes x).par = 0 ∧ pathRs (s.splay.nodes x).sum = true ∧
    ((s.splay.nodes x).left ≠ 0 ∨ (s.splay.nodes x).right ≠ 0 ∨ (s.splay.nodes x).ppar ≠ 0)

theorem validRoot_root {s : PathTreeState} {trees : List AuxTree} {free : List ℕ}
    {depth : ℕ → ℕ} (W : LctInvWith pathPayload s trees free depth) (hF : FreeShape s free)
    {x : ℕ} (hx : ValidRoot s x) : ∃ t ∈ trees, t.rootId = x := by
  obtain ⟨hx1, hx2, hp, -, hlr⟩ := hx
  have hact : x ∈ trees.flatMap AuxTree.toList := by
    by_cases hv : x ≤ s.n
    · exact isVertex_mem_active W ⟨hx1, hv⟩
    · have he : isEdgeSlot s.n x := ⟨by omega, hx2⟩
      by_contra hna
      have hfree := (not_congr (W.partitionSlots x he)).mp hna
      push_neg at hfree
      obtain ⟨h1, h2, h3⟩ := hF x hfree
      rcases hlr with h | h | h <;> exact h (by assumption)
  obtain ⟨t, ht, hxt⟩ := List.mem_flatMap.mp hact
  exact ⟨t, ht, (W.root_of_par_zero ht hxt hp).symm⟩

theorem root_validRoot {s : PathTreeState} {trees : List AuxTree} {free : List ℕ}
    {depth : ℕ → ℕ} (W : LctInvWith pathPayload s trees free depth) (hE : ValsOnEdges s)
    {t : AuxTree} (ht : t ∈ trees) (hr : pathRs (s.splay.nodes t.rootId).sum = true) :
    ValidRoot s t.rootId := by
  have hsub := (W.treesInv t ht).sub
  cases t with
  | leaf => exact absurd rfl (W.treesNonEmpty _ ht)
  | node r a b =>
    simp only [AuxTree.rootId] at hr ⊢
    have hra : r ∈ trees.flatMap AuxTree.toList :=
      List.mem_flatMap.mpr ⟨_, ht, by simp [AuxTree.toList]⟩
    have hnode := W.activeValid r hra
    obtain ⟨hr0, hl, hrr, hp, -, -, hsum, hsa, hsb⟩ := hsub
    refine ⟨hnode.1, hnode.2, hp, hr, ?_⟩
    by_contra hno
    push_neg at hno
    obtain ⟨h1, h2, h3⟩ := hno
    have ha : a = .leaf := by
      cases a with
      | leaf => rfl
      | node id _ _ => simp [AuxTree.rootId] at hl; exact absurd (hl ▸ h1) hsa.1
    have hb : b = .leaf := by
      cases b with
      | leaf => rfl
      | node id _ _ => simp [AuxTree.rootId] at hrr; exact absurd (hrr ▸ h2) hsb.1
    subst ha hb
    have hpar0 : inducedSubPar pathPayload s.splay trees r = 0 := by
      rw [inducedSubPar_eq_of_mem W.activeNodup ht (by simp [AuxTree.toList])]
      simp [treeIds, SplayState.evalPairs, chainPred, AuxTree.rootId, h3]
    have hv := isVertex_of_par_zero W hra hpar0
    have hnone := hE r hv
    rw [hsum, pathRs_iff, sumReady_listSummary] at hr
    obtain ⟨p, hp', v, hv', -⟩ := hr
    simp [SplayState.evalPairs, hnone] at hp'
    rw [hp'] at hv'
    simp [pathPayload_laws.actVal_id] at hv'

theorem readyIdx_pop {s : PathTreeState} {trees : List AuxTree} {free : List ℕ}
    {depth : ℕ → ℕ} (W : LctInvWith pathPayload s trees free depth) (hE : ValsOnEdges s)
    {S : List ℕ} {x : ℕ} (hI : ReadyIdx s trees (S ++ [x])) (hx : ¬ ValidRoot s x) :
    ReadyIdx s trees S := by
  intro t ht hr
  have h := hI t ht hr
  rcases List.mem_append.mp h with h | h
  · exact h
  · rw [List.mem_singleton] at h
    exact absurd (h ▸ root_validRoot W hE ht hr) hx

/-- One change of state where every new root is noted. -/
theorem readyIdx_step {s s' : PathTreeState} {trees trees' : List AuxTree}
    {free free' : List ℕ} {depth depth' : ℕ → ℕ}
    (W : LctInvWith pathPayload s trees free depth)
    (W' : LctInvWith pathPayload s' trees' free' depth') {N : ℕ → Prop}
    (hacc : RootAcc s.splay s'.splay N)
    (hact : ∀ z ∈ trees'.flatMap AuxTree.toList, z ∈ trees.flatMap AuxTree.toList ∨ N z)
    {S S' : List ℕ} (hI : ReadyIdx s trees S) (hS : S ⊆ S') (hN : ∀ z, N z → z ∈ S') :
    ReadyIdx s' trees' S' := by
  intro t' ht' hr
  have hsub := (W'.treesInv t' ht').sub
  have hp0 : (s'.splay.nodes t'.rootId).par = 0 := by
    cases t' with
    | leaf => exact absurd rfl (W'.treesNonEmpty _ ht')
    | node r a b => exact hsub.2.2.2.1
  rcases hacc _ hp0 with h | ⟨hp, hsum⟩
  · exact hN _ h
  have hra : t'.rootId ∈ trees'.flatMap AuxTree.toList := by
    refine List.mem_flatMap.mpr ⟨t', ht', AuxTree.rootId_mem (W'.treesNonEmpty _ ht')⟩
  rcases hact _ hra with h | h
  · obtain ⟨t, ht, hzt⟩ := List.mem_flatMap.mp h
    have heq := W.root_of_par_zero ht hzt hp
    rw [hsum, heq] at hr
    rw [heq]
    exact hS (hI t ht hr)
  · exact hN _ h

/-- `FreeShape` after a change of state: a free slot of the new state was free before and did
not change, or has the shape itself. -/
theorem freeShape_step {s s' : PathTreeState} {free free' : List ℕ} {M : ℕ → Prop}
    (hF : FreeShape s free) (hk : Keep s.splay s'.splay M)
    (h : ∀ e ∈ free', (e ∈ free ∧ ¬ M e) ∨ ((s'.splay.nodes e).left = 0 ∧
      (s'.splay.nodes e).right = 0 ∧ (s'.splay.nodes e).ppar = 0)) :
    FreeShape s' free' := by
  intro e he
  rcases h e he with ⟨he', hM⟩ | h'
  · rw [hk e hM]; exact hF e he'
  · exact h'

/-- A free slot is not active. -/
theorem not_active_of_free {s : PathTreeState} {trees : List AuxTree} {free : List ℕ}
    {depth : ℕ → ℕ} (W : LctInvWith pathPayload s trees free depth) {e : ℕ} (he : e ∈ free) :
    e ∉ trees.flatMap AuxTree.toList :=
  fun ha => (W.partitionSlots e (W.freeValid e he)).mp ha he

/-- An operation that changes only active nodes and keeps the free list keeps `FreeShape`. -/
theorem freeShape_keep {s s' : PathTreeState} {trees : List AuxTree} {free : List ℕ}
    {depth : ℕ → ℕ} (W : LctInvWith pathPayload s trees free depth) (hF : FreeShape s free)
    (hk : Keep s.splay s'.splay (fun z => z ∈ trees.flatMap AuxTree.toList)) :
    FreeShape s' free :=
  freeShape_step hF hk fun e he => Or.inl ⟨he, not_active_of_free W he⟩

end MinCostFlow.LinkCut.PathTree
