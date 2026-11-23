module

public import MinCostFlow.LinkCut.PathTree.Ready
public import MinCostFlow.LinkCut.PathTree.Descend

/-!
# The descent for the Section 6 payload

This file fixes the two tests of the descent for `pathPayload`: a summary is ready when its
detector maximum exists and is non-negative (`pathRs`), and a value is ready when it exists and
its detector is non-negative (`pathRv`). They meet `ReadyLaw` by `sumReady_listSummary`.

The main fact is `descend_ready`: in a state that meets the invariants, a descent from the root
of an auxiliary tree with a ready summary stops at an edge `y` that is ready in the sense of the
contract, and exposing `y` after the descent gives `lctExpose s y`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathTree

open MinCostFlow.MinRatio MinCostFlow.LinkCut

/-- A summary is ready: its detector maximum exists and is non-negative. -/
def pathRs (s : PathSummary) : Bool :=
  match s.detector with
  | some z => decide (0 ≤ z)
  | none => false

/-- A value is ready: it exists and its detector is non-negative. -/
def pathRv (v : Option PathEdgeValue) : Bool :=
  match v with
  | some e => decide (0 ≤ e.detector)
  | none => false

theorem pathRs_iff (s : PathSummary) : pathRs s = true ↔ SumReady s := by
  unfold pathRs SumReady
  cases s.detector <;> simp

theorem pathRv_iff (v : Option PathEdgeValue) :
    pathRv v = true ↔ ∃ e, v = some e ∧ 0 ≤ e.detector := by
  unfold pathRv
  cases v <;> simp

theorem pathReadyLaw : ReadyLaw pathPayload pathRs pathRv := by
  intro ps
  rw [pathRs_iff, sumReady_listSummary]
  simp only [PairReady, pathRv_iff]

/-- A list without duplicates whose entries are nodes has at most `2 n` entries. -/
theorem length_le_of_isNode {n : ℕ} {L : List ℕ} (hnd : L.Nodup) (h : ∀ x ∈ L, isNode n x) :
    L.length ≤ 2 * n := by
  have hsub : L.toFinset ⊆ Finset.Ico 1 (2 * n) := by
    intro x hx
    have := h x (List.mem_toFinset.mp hx)
    unfold isNode at this
    simp only [Finset.mem_Ico]; omega
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd] at this
  simp at this; omega

/-- The descent from a root with a ready summary stops at an edge that is ready, and the expose
of that edge after the descent is `lctExpose s y`. -/
theorem descend_ready {s : PathTreeState} {trees : List AuxTree} {free : List ℕ}
    {depth : ℕ → ℕ} (W : LctInvWith pathPayload s trees free depth) (hE : ValsOnEdges s)
    {t : AuxTree} (ht : t ∈ trees) (hrs : pathRs (s.splay.nodes t.rootId).sum = true)
    {D' : SplayState (Option PathEdgeValue) PathSummary PathTag} {y : ℕ}
    (hd : descend pathPayload pathRs pathRv s.splay (2 * s.n + 1) t.rootId = (D', y)) :
    pathTreeReady s y ∧ lctExpose pathPayload { s with splay := D' } y =
      lctExpose pathPayload s y ∧
      SplayState.splay pathPayload D' (2 * s.n + 1) y =
        SplayState.splay pathPayload s.splay (2 * s.n + 1) y := by
  have htinv := W.treesInv t ht
  have hne := W.treesNonEmpty t ht
  have hF : t.countNodes ≤ 2 * s.n + 1 := by
    have hsub : t.toList ⊆ trees.flatMap AuxTree.toList := fun z hz =>
      List.mem_flatMap.mpr ⟨t, ht, hz⟩
    have := length_le_of_isNode htinv.nodup (fun x hx => W.activeValid x (hsub hx))
    rw [AuxTree.length_toList] at this
    omega
  obtain ⟨hyt, hpair, hrdy, -, hsplay, -⟩ :=
    descend_root pathPayload_laws pathReadyLaw htinv hne hrs hF hd
  refine ⟨?_, lctExpose_of_splay_eq s hsplay, hsplay⟩
  obtain ⟨v, hv, hd0⟩ := (pathRv_iff _).mp hrdy
  have hya : y ∈ trees.flatMap AuxTree.toList := List.mem_flatMap.mpr ⟨t, ht, hyt⟩
  have hnd : ((forestPairs pathPayload s.splay trees).map Prod.fst).Nodup :=
    (forestPairs_fst_perm _ _).nodup_iff.mpr W.activeNodup
  have hpf : (y, some v) ∈ forestPairs pathPayload s.splay trees := by
    rw [← hv]; exact List.mem_flatMap.mpr ⟨t, ht, hpair⟩
  have hval : (s.splay.nodes y).val ≠ none := by
    rw [hv] at hpair
    exact evalPairs_some_stored _ _ _ _ hpair
  have hnode := W.activeValid y hya
  have hedge : isEdgeSlot s.n y := by
    by_cases hv' : isVertex s.n y
    · exact absurd (hE y hv') hval
    · unfold isVertex at hv'; unfold isNode at hnode; exact ⟨by omega, hnode.2⟩
  refine ⟨hedge, ⟨trees, free, depth, W, hya⟩, v, ?_, hd0⟩
  exact pair_unique hnd (lctExpose_val_mem_forestPairs W ht hyt) hpf

end MinCostFlow.LinkCut.PathTree
