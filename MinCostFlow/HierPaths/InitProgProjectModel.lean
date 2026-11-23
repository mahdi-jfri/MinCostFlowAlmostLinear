module

public import MinCostFlow.HierPaths.InitProgFlatPassModel

/-!
# Streaming the two columns of a projected walk

A labelled root edge emits one word in each column. The edge column gets the
label, and the vertex column gets the owner before the step. If any edge was
emitted the vertex column ends with the owner after the final step.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- Emit one word for each labelled step, in the selected column. -/
def initProjectWords (S : StaticData) (verts : Bool) : ℕ → List ℕ → List ℕ
  | _, [] => []
  | u, e :: es =>
    let next := initProjectWords S verts (otherEnd (S.H.host 0 0).edges e u) es
    match S.label e with
    | none => next
    | some k => (if verts then S.owner u else k) :: next

theorem initProjectWords_edges (S : StaticData) (u : ℕ) (es : List ℕ) :
    initProjectWords S false u es = es.filterMap S.label := by
  induction es generalizing u with
  | nil => rfl
  | cons e es ih =>
    rw [initProjectWords, List.filterMap_cons]
    cases S.label e <;> simp [ih]

theorem initProjectWords_length (S : StaticData) (verts : Bool) (u : ℕ) (es : List ℕ) :
    (initProjectWords S verts u es).length = (es.filterMap S.label).length := by
  induction es generalizing u with
  | nil => rfl
  | cons e es ih =>
    rw [initProjectWords, List.filterMap_cons]
    cases S.label e <;> simp [ih]

private theorem owner_otherEnd {G : Graph} {S : StaticData} {u v e : ℕ} {es : List ℕ}
    (hP : IsProjection G (S.H.host 0 0).edges S.owner S.label)
    (hW : IsEdgeWalk (S.H.host 0 0).edges u v (e :: es)) (he : S.label e = none) :
    S.owner u = S.owner (otherEnd (S.H.host 0 0).edges e u) := by
  have h := (hP e (hW.lt_length e List.mem_cons_self)).2.2.1 he
  rcases ends_of_isEdgeWalk_cons hW with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rwa [h₁, h₂] at h
  · rw [h₁, h₂] at h
    exact h.symm

private theorem owner_eq_of_unlabelled {S : StaticData} {G : Graph}
    (hP : IsProjection G (S.H.host 0 0).edges S.owner S.label)
    {u v : ℕ} {es : List ℕ} (hW : IsEdgeWalk (S.H.host 0 0).edges u v es)
    (he : es.filterMap S.label = []) : S.owner u = S.owner v := by
  induction es generalizing u with
  | nil =>
    cases hW
    rfl
  | cons e es ih =>
    have hl : S.label e = none := by
      rw [List.filterMap_cons] at he
      cases h : S.label e <;> simp [h] at he ⊢
    have hr : es.filterMap S.label = [] := by simpa [hl] using he
    exact (owner_otherEnd hP hW hl).trans (ih (isEdgeWalk_tail_otherEnd hW) hr)

/-- The streaming vertex words give both the start and end owner of every
nonempty projected walk, with the intermediate owners in traversal order. -/
theorem initProjectWords_verts {S : StaticData} {G : Graph}
    (hP : IsProjection G (S.H.host 0 0).edges S.owner S.label) :
    ∀ {u v es}, IsEdgeWalk (S.H.host 0 0).edges u v es →
      let ws := initProjectWords S true u es
      (projectWalk (S.H.host 0 0).edges S.owner S.label u es).verts =
        if ws.isEmpty then [] else ws ++ [S.owner v] := by
  intro u v es hW
  induction es generalizing u with
  | nil => rfl
  | cons e es ih =>
    let z := otherEnd (S.H.host 0 0).edges e u
    let P := projectWalk (S.H.host 0 0).edges S.owner S.label z es
    let ws := initProjectWords S true z es
    have ht := isEdgeWalk_tail_otherEnd hW
    have hPverts : P.verts = if ws.isEmpty then [] else ws ++ [S.owner v] := ih ht
    rw [projectWalk, initProjectWords]
    cases he : S.label e with
    | none =>
      change P.verts = if ws.isEmpty then [] else ws ++ [S.owner v]
      exact hPverts
    | some k =>
      change ((Walk.single (S.owner u) (S.owner z) k).append P).verts =
        S.owner u :: (ws ++ [S.owner v])
      cases hws : ws with
      | nil =>
        have hlen := initProjectWords_length S true z es
        rw [← show ws = initProjectWords S true z es from rfl, hws, List.length_nil,
          eq_comm, List.length_eq_zero_iff] at hlen
        have hempty : P.edges = [] := (edges_projectWalk _ _ _ _ _).trans hlen
        have hv : S.owner z = S.owner v := owner_eq_of_unlabelled hP ht hlen
        simp [Walk.append, Walk.single, hempty, hv]
      | cons a tail =>
        have hlen := initProjectWords_length S true z es
        rw [← show ws = initProjectWords S true z es from rfl, hws] at hlen
        have hnon : P.edges ≠ [] := by
          intro h
          have hnil : es.filterMap S.label = [] :=
            (edges_projectWalk _ _ _ _ _).symm.trans h
          simp [hnil] at hlen
        have hz : a = S.owner z := by
          have hout := projectWalk_isWalk hP ht
          have hown : S.owner z < G.n := by
            have hh := hP e (hW.lt_length e List.mem_cons_self)
            rcases ends_of_isEdgeWalk_cons hW with ⟨_, h₂⟩ | ⟨h₁, _⟩
            · rw [show z = _ from h₂.symm]
              exact hh.2.1
            · rw [show z = _ from h₁.symm]
              exact hh.1
          obtain ⟨_, _, h | h⟩ := hout hown
          · exact (hnon h.2.1).elim
          · have hhead := h.2.2.1
            change P.verts.head? = some (S.owner z) at hhead
            simpa [hPverts, hws] using hhead
        simp [Walk.append, Walk.single, hnon, hPverts, hws, hz]

end MinCostFlow.HierPaths

end
