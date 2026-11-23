module

public import MinCostFlow.HierPaths.QueryRoute
public import MinCostFlow.HierPaths.LiveSupport
public import MinCostFlow.HierPaths.LoopErase

import Mathlib.Tactic.Ring

/-!
# The query `GetPath`

`GetPath(w, w')` joins two live vertices by a path that uses no deleted edge and no pruned vertex.
It reads the support entry under the cursor of each endpoint. Each entry gives
a walk from the endpoint to the owner of a surviving terminal (`supportWalk_spec`). The routing recursion
(`route_spec`) joins the two terminals, the second attachment is reversed, and chronological loop
erasure (`loopErase`) removes repeated vertices.

The main results:

* `getPathOf_spec`: for any live support entries of `w` and `w'`, the result is a walk from `w`
  to `w'` with no repeated vertex, no deleted edge and no pruned vertex, with at most
  `(2 ^ L + 1) · λ` edges, and the query takes at most `6 · 2 ^ L · (λ + 1)` steps;
* `getPath_spec`: the same for the entries under the support cursors, for any history in which
  terminals are only lost. This is the postcondition of operation `1` of `pathDSDataStructure`
  (`Spanner/PathDSContract.lean`) for the model, with `L` the leaf depth `h`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

namespace ConnectorSystem

variable (C : ConnectorSystem) (grp : ℕ → ℕ → ℕ) (pick : ℕ → ℕ → ℕ → ℕ)

/-- The walk that `GetPath` builds before loop erasure, from the support entries `x` of `w` and
`x'` of `w'`: the attachment of `w`, the routing recursion `route` from the root, and the reversed attachment of
`w'`. -/
def joinWalk (L : ℕ) (x x' : SupportEntry) : Walk :=
  (C.supportWalk x).append
    ((C.route grp pick L 0 (C.entryTerm x) (C.entryTerm x')).append (C.supportWalk x').reverse)

/-- `GetPath` for the support entries `x` and `x'`. -/
def getPathOf (L : ℕ) (x x' : SupportEntry) : Walk :=
  loopErase (C.joinWalk grp pick L x x')

/-- The step count of `GetPath` for the support entries `x` and `x'`: two cursor reads, copying
the two attachments, the routing recursion, and the stack version of loop erasure. -/
def queryOpsOf (L : ℕ) (x x' : SupportEntry) : ℕ :=
  2 + (C.supportWalk x).edges.length + (C.supportWalk x').edges.length +
    C.routeOps grp pick L 0 (C.entryTerm x) (C.entryTerm x') +
    eraseOps ((C.joinWalk grp pick L x x').verts.headD 0) [] (Walk.steps (C.joinWalk grp pick L x x'))

/-- The support entry under the cursor of `w` after time `t`. -/
def cursorEntry (surv : ℕ → Finset ℕ) (t w : ℕ) : SupportEntry :=
  (C.supportArray w).getD (C.supportCursor surv w t) default

/-- `GetPath(w, w')` after time `t`, with the leaf depth `L`. -/
def getPath (surv : ℕ → Finset ℕ) (t L w w' : ℕ) : Walk :=
  C.getPathOf grp pick L (C.cursorEntry surv t w) (C.cursorEntry surv t w')

/-- The step count of `GetPath(w, w')` after time `t`. -/
def queryOps (surv : ℕ → Finset ℕ) (t L w w' : ℕ) : ℕ :=
  C.queryOpsOf grp pick L (C.cursorEntry surv t w) (C.cursorEntry surv t w')

end ConnectorSystem

end MinCostFlow.HierPaths

end

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

namespace ConnectorSystem

variable (C : ConnectorSystem) (grp : ℕ → ℕ → ℕ) (pick : ℕ → ℕ → ℕ → ℕ)

private theorem supportWalk_length_le {w : ℕ} {x : SupportEntry} (hx : x ∈ C.supportArray w)
    {lam : ℕ} (hlam : ∀ c < C.numConn, (C.walk c).edges.length ≤ lam) :
    (C.supportWalk x).edges.length ≤ lam := by
  rcases (C.mem_supportArray).mp hx with ⟨t, _, _, rfl⟩ | ⟨c, hc, pos, _, rfl⟩
  · simp [supportWalk, Walk.empty]
  · rw [supportWalk, edges_reverse, List.length_reverse]
    exact (length_edges_prefix_le _ _).trans (hlam c hc)

private theorem not_pruned_of_live {G : Graph} {surv : Finset ℕ} {x : ℕ}
    (hx : x ∈ C.liveSet G surv) : x ∉ C.prunedSet G surv := by
  rw [mem_prunedSet]
  exact fun h => h.2 hx

public section

/-- `GetPath` for live support entries `x` of `w` and `x'` of `w'`: the result is a walk from `w`
to `w'` with no repeated vertex, no deleted edge and no pruned vertex, with at most
`(2 ^ L + 1) · λ` edges, and the query takes at most `6 · 2 ^ L · (λ + 1)` steps. The hypotheses
are those of `route_spec`, with all terminals in one group at depth `0` (`hroot`). -/
theorem getPathOf_spec {G : Graph} (hG : G.IsValid) (hfit : C.FitsGraph G) {D surv : Finset ℕ}
    (hrule : C.ReverseIndexRule D surv) (hsurv : surv ⊆ Finset.range C.numTerm)
    (hpick : C.IsConnectorChoice grp pick surv) {L lam : ℕ}
    (hroot : ∀ u ∈ surv, ∀ v ∈ surv, grp 0 u = grp 0 v)
    (hleaf : ∀ u ∈ surv, ∀ v ∈ surv, grp L u = grp L v → u = v)
    (hlam : ∀ c < C.numConn, (C.walk c).edges.length ≤ lam)
    {w w' : ℕ} (hw : w < G.n) (hw' : w' < G.n) {x x' : SupportEntry}
    (hx : x ∈ C.supportArray w) (hxl : C.entryLive surv x = true)
    (hx' : x' ∈ C.supportArray w') (hxl' : C.entryLive surv x' = true) :
    (C.getPathOf grp pick L x x').IsWalk G w w' ∧
      (C.getPathOf grp pick L x x').verts.Nodup ∧
      (∀ e ∈ (C.getPathOf grp pick L x x').edges, e ∉ D) ∧
      (∀ y ∈ (C.getPathOf grp pick L x x').verts, y ∉ C.prunedSet G surv) ∧
      (C.getPathOf grp pick L x x').edges.length ≤ (2 ^ L + 1) * lam ∧
      C.queryOpsOf grp pick L x x' ≤ 6 * 2 ^ L * (lam + 1) := by
  obtain ⟨ht, hW1, hW1e, hW1v, -, -⟩ := C.supportWalk_spec hG hfit hrule hw hx hxl
  obtain ⟨ht', hW2, hW2e, hW2v, -, -⟩ := C.supportWalk_spec hG hfit hrule hw' hx' hxl'
  obtain ⟨hR, hRe, hRv, hRl⟩ := C.route_spec grp pick hG hfit hrule hsurv hpick hleaf hlam L 0
    (C.entryTerm x) (C.entryTerm x') (zero_add L) ht ht' (hroot _ ht _ ht')
  have hl1 := C.supportWalk_length_le hx hlam
  have hl2 := C.supportWalk_length_le hx' hlam
  set J := C.joinWalk grp pick L x x' with hJ
  have hJw : J.IsWalk G w w' :=
    Walk.isWalk_append hW1 (Walk.isWalk_append hR (Walk.isWalk_reverse hW2))
  have hJe : ∀ e ∈ J.edges, e ∉ D := by
    intro e he
    rw [hJ, joinWalk, edges_append, edges_append, edges_reverse] at he
    rcases List.mem_append.mp he with he | he
    · exact hW1e e he
    rcases List.mem_append.mp he with he | he
    · exact hRe e he
    · exact hW2e e (List.mem_reverse.mp he)
  have hJv : ∀ y ∈ J.verts, y ∈ C.liveSet G surv := by
    intro y hy
    rw [hJ, joinWalk] at hy
    rcases mem_verts_append hy with hy | hy
    · exact hW1v y hy
    rcases mem_verts_append hy with hy | hy
    · exact hRv y hy
    · rw [verts_reverse, List.mem_reverse] at hy
      exact hW2v y hy
  have hJl : J.edges.length ≤ (2 ^ L + 1) * lam := by
    rw [hJ, joinWalk, length_edges_append, length_edges_append, edges_reverse,
      List.length_reverse]
    have hp : 1 ≤ 2 ^ L := Nat.one_le_two_pow
    have h1 : (2 ^ L + 1) * lam = (2 ^ L - 1) * lam + lam + lam := by
      have : 2 ^ L + 1 = (2 ^ L - 1) + 1 + 1 := by omega
      rw [this, Nat.add_mul, Nat.add_mul, one_mul]
    omega
  obtain ⟨hPw, hPn⟩ := isWalk_loopErase hJw
  refine ⟨hPw, hPn, fun e he => hJe e (edges_loopErase_subset hJw e he),
    fun y hy => C.not_pruned_of_live (hJv y (verts_loopErase_subset hJw y hy)),
    (length_edges_loopErase_le hJw).trans hJl, ?_⟩
  have hops := C.routeOps_le grp pick hfit hpick hlam L 0 _ _ ht ht' (hroot _ ht _ ht')
  have her := eraseOps_le J (J.verts.headD 0)
  unfold queryOpsOf
  rw [← hJ]
  set A := 2 ^ L
  have hA : 1 ≤ A := Nat.one_le_two_pow
  have hAl : lam ≤ A * lam := Nat.le_mul_of_pos_left _ hA
  have e1 : A * (lam + 3) = A * lam + 3 * A := by ring
  have e2 : (A + 1) * lam = A * lam + lam := by ring
  have e3 : 6 * A * (lam + 1) = 6 * (A * lam) + 6 * A := by ring
  rw [e2] at hJl
  rw [e1] at hops
  rw [e3]
  omega

/-- The support entry under the cursor of a vertex that is not pruned lies in its support array
and is live. -/
theorem cursorEntry_live {G : Graph} {surv : ℕ → Finset ℕ}
    (hanti : ∀ t, surv (t + 1) ⊆ surv t) (hsurv : ∀ t, surv t ⊆ Finset.range C.numTerm)
    {w : ℕ} (hw : w < G.n) {t : ℕ} (hnp : w ∉ C.prunedSet G (surv t)) :
    C.cursorEntry surv t w ∈ C.supportArray w ∧ C.entryLive (surv t) (C.cursorEntry surv t w) =
      true := by
  have hlt : C.supportCursor surv w t < (C.supportArray w).length := by
    rcases Nat.lt_or_ge (C.supportCursor surv w t) (C.supportArray w).length with h | h
    · exact h
    · have hle : C.supportCursor surv w t ≤ (C.supportArray w).length := cursorAt_le t
      exact absurd ((C.supportCursor_eq_iff hanti hsurv hw t).mp (le_antisymm hle h)) hnp
  refine ⟨?_, ?_⟩
  · rw [cursorEntry, List.getD_eq_getElem _ _ hlt]
    exact List.getElem_mem hlt
  · exact cursorAt_valid (valid := fun t i =>
      C.entryLive (surv t) ((C.supportArray w).getD i default)) t hlt

/-- The postcondition of `GetPath` (operation `1` of `pathDSDataStructure`) for the model: for
two vertices `w`, `w'` of `G` that are not pruned after time `t`, `GetPath(w, w')` is a walk from
`w` to `w'` with no repeated vertex, no deleted edge and no pruned vertex, with at most
`(2 ^ L + 1) · λ` edges, and it takes at most `6 · 2 ^ L · (λ + 1)` steps. Terminals are only
lost over time (`hanti`), and at time `t` the hypotheses of `route_spec` hold. -/
theorem getPath_spec {G : Graph} (hG : G.IsValid) (hfit : C.FitsGraph G) {D : Finset ℕ}
    {surv : ℕ → Finset ℕ} (hanti : ∀ t, surv (t + 1) ⊆ surv t)
    (hsurv : ∀ t, surv t ⊆ Finset.range C.numTerm) {t L lam : ℕ}
    (hrule : C.ReverseIndexRule D (surv t)) (hpick : C.IsConnectorChoice grp pick (surv t))
    (hroot : ∀ u ∈ surv t, ∀ v ∈ surv t, grp 0 u = grp 0 v)
    (hleaf : ∀ u ∈ surv t, ∀ v ∈ surv t, grp L u = grp L v → u = v)
    (hlam : ∀ c < C.numConn, (C.walk c).edges.length ≤ lam)
    {w w' : ℕ} (hw : w ∈ G.verts \ C.prunedSet G (surv t))
    (hw' : w' ∈ G.verts \ C.prunedSet G (surv t)) :
    (C.getPath grp pick surv t L w w').IsWalk G w w' ∧
      (C.getPath grp pick surv t L w w').verts.Nodup ∧
      (∀ e ∈ (C.getPath grp pick surv t L w w').edges, e ∉ D) ∧
      (∀ y ∈ (C.getPath grp pick surv t L w w').verts, y ∉ C.prunedSet G (surv t)) ∧
      (C.getPath grp pick surv t L w w').edges.length ≤ (2 ^ L + 1) * lam ∧
      C.queryOps grp pick surv t L w w' ≤ 6 * 2 ^ L * (lam + 1) := by
  rw [Finset.mem_sdiff, Graph.verts, Finset.mem_range] at hw hw'
  obtain ⟨hx, hxl⟩ := C.cursorEntry_live hanti hsurv hw.1 hw.2
  obtain ⟨hx', hxl'⟩ := C.cursorEntry_live hanti hsurv hw'.1 hw'.2
  exact C.getPathOf_spec grp pick hG hfit hrule (hsurv t) hpick hroot hleaf hlam hw.1 hw'.1
    hx hxl hx' hxl'

end

end ConnectorSystem

end MinCostFlow.HierPaths
