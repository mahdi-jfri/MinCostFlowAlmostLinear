module

public import MinCostFlow.LinkCut.Gen.FindReady
public import MinCostFlow.LinkCut.PathTree.IdxInv

/-!
# Find-ready meets its contract in the model

`findLoop_spec`: if every ready root is on the stack (`ReadyIdx`), then find-ready either
returns `0`, leaves the state as it was, and no edge is ready; or it returns a ready edge `y`,
and the new state is `lctExpose s y`. In the second case the new stack is a stack that meets
`ReadyIdx` for `s`, with the nodes the expose notes added.

The search pops only entries that fail the test, and such an entry is not a ready root
(`readyIdx_pop`). An entry that passes the test is the root of an auxiliary tree with a ready
summary (`validRoot_root`), so the descent from it finds a ready edge (`descend_ready`).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathTree

open MinCostFlow.MinRatio MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen

theorem exposeNotes_of_splay_eq {α σ τ : Type*} {P : LctPayload α σ τ} (st : LctState α σ τ)
    {D : SplayState α σ τ} {y : ℕ}
    (h : SplayState.splay P D (2 * st.n + 1) y = SplayState.splay P st.splay (2 * st.n + 1) y)
    (S : List ℕ) : exposeNotes P { st with splay := D } y S = exposeNotes P st y S := by
  unfold exposeNotes exposeStart
  simp only
  rw [h]

theorem findLoop_spec {s : PathTreeState} {trees : List AuxTree} {free : List ℕ}
    {depth : ℕ → ℕ} (W : LctInvWith pathPayload s trees free depth) (hE : ValsOnEdges s)
    (hF : FreeShape s free) :
    ∀ R : List ℕ, ReadyIdx s trees R.reverse →
      ((findLoop pathPayload pathRs pathRv s R).2.2 = 0 ∧
          (findLoop pathPayload pathRs pathRv s R).1 = s ∧
          (findLoop pathPayload pathRs pathRv s R).2.1 = [] ∧ ¬ ∃ x, pathTreeReady s x) ∨
        ((findLoop pathPayload pathRs pathRv s R).2.2 ≠ 0 ∧
          pathTreeReady s (findLoop pathPayload pathRs pathRv s R).2.2 ∧
          (findLoop pathPayload pathRs pathRv s R).1 =
            lctExpose pathPayload s (findLoop pathPayload pathRs pathRv s R).2.2 ∧
          ∃ S', ReadyIdx s trees S' ∧ (findLoop pathPayload pathRs pathRv s R).2.1 =
            exposeNotes pathPayload s (findLoop pathPayload pathRs pathRv s R).2.2 S')
  | [], hI => by
    left
    refine ⟨rfl, rfl, rfl, ?_⟩
    rw [exists_ready_iff W hE]
    rintro ⟨t, ht, hr⟩
    exact absurd (hI t ht ((pathRs_iff _).mpr hr)) (by simp)
  | x :: R, hI => by
    rw [List.reverse_cons] at hI
    by_cases hv : ValidG pathRs s.n s.splay x
    · right
      have hv' : ValidRoot s x := hv
      obtain ⟨t, ht, rfl⟩ := validRoot_root W hF hv'
      have hd : descend pathPayload pathRs pathRv s.splay (2 * s.n + 1) t.rootId =
          ((descend pathPayload pathRs pathRv s.splay (2 * s.n + 1) t.rootId).1,
            (descend pathPayload pathRs pathRv s.splay (2 * s.n + 1) t.rootId).2) := rfl
      obtain ⟨hready, hexp, hsplay⟩ := descend_ready W hE ht hv'.2.2.2.1 hd
      have hloop : findLoop pathPayload pathRs pathRv s (t.rootId :: R) =
          (lctExpose pathPayload (descState pathPayload pathRs pathRv s t.rootId)
              (descNode pathPayload pathRs pathRv s t.rootId),
            exposeNotes pathPayload (descState pathPayload pathRs pathRv s t.rootId)
              (descNode pathPayload pathRs pathRv s t.rootId) (t.rootId :: R).reverse,
            descNode pathPayload pathRs pathRv s t.rootId) := by
        simp [findLoop, hv]
      rw [hloop]
      refine ⟨(pathTreeReady_bounds hready).1, hready, hexp, (t.rootId :: R).reverse, ?_, ?_⟩
      · rw [List.reverse_cons]; exact hI
      · exact exposeNotes_of_splay_eq s hsplay _
    · have hloop : findLoop pathPayload pathRs pathRv s (x :: R) =
          findLoop pathPayload pathRs pathRv s R := by
        simp [findLoop, hv]
      rw [hloop]
      exact findLoop_spec W hE hF R (readyIdx_pop W hE hI hv)

end MinCostFlow.LinkCut.PathTree
