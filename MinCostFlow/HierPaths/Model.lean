module

public import MinCostFlow.HierPaths.ModelPick
public import MinCostFlow.HierPaths.PotentialParams
public import MinCostFlow.HierPaths.HierParams

/-!
# The whole model of the path data structure

This file joins the parts. A `HierModel` holds the static arrays (`StaticArrays`), the map
`pairIdx` from two siblings to their pair array, and the bounds `ξ`, `κ`, `λ`. `HierModel.Spec`
is what `Init` must deliver about them (the arrays meet their specifications, the pair arrays
hold perfect matchings, each vertex owns at least its degree in terminals, connector walks have at
most `λ` edges), and `HierModel.Fits` says that the bounds fit the numbers of
`HierPaths/Params.lean`. The static construction and `Init` build a `HierModel` meeting both.

A model state pairs the dynamic state `DelState` with the abstract state `PathDSAbsState`, and
`HierModel.Rel` ties them: the deleted edges agree and `Vhat` is the pruned set. For parameters
`p` with `phiOutDen = gExp = gQuery = Γ` and `gDel = 1` (`IsHierParams`, met by `hierParams`):

* `rel_init`: `Init` needs only `Spec`, `Fits`, `Valid`, `Vhat = ∅` and `deleted = ∅`; then the
  initial dynamic state is related to the abstract state;
* `model_delete`: from `s.Valid p` and the precondition of operation `0`, `Delete` gives the
  abstract part of its postcondition (everything except the memory layout of the output list),
  and the relation again;
* `model_getPath`: from `s.Valid p` and the precondition of operation `1`, `GetPath` gives the
  abstract part of its postcondition, with at most `γ_ExpPath = Γ` edges.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

/-- The parameters of the hierarchy: `phiOutDen = gExp = gQuery = Γ` and `gDel = 1`. -/
def IsHierParams (a : ℕ) (p : PathDSParams) : Prop :=
  (∀ d M, p.phiOutDen d M = gammaHP a d M) ∧ (∀ d M, p.gExp d M = gammaHP a d M) ∧
    (∀ d M, p.gDel d M = 1) ∧ (∀ d M, p.gQuery d M = gammaHP a d M)

/-- The static part of the model. -/
structure HierModel where
  /-- The static arrays. -/
  A : StaticArrays
  /-- The pair array of two siblings. -/
  pairIdx : ℕ → ℕ → ℕ → ℕ
  /-- The bound on the reverse lists. -/
  ξ : ℕ
  /-- The bound on the connectors of a terminal. -/
  κ : ℕ
  /-- The bound on the connector walks. -/
  lam : ℕ

/-- What `Init` must deliver about the static part, for the input graph `G`. -/
structure HierModel.Spec (H : HierModel) (G : Graph) : Prop where
  arrays : H.A.Spec G H.ξ H.κ
  pairs : H.A.PairSpec H.pairIdx
  deg : ∀ w < G.n, G.deg w ≤ (H.A.C.ownedBy w).card
  walkLen : ∀ c < H.A.C.numConn, (H.A.C.walk c).edges.length ≤ H.lam

/-- The bounds of the static part fit the numbers of `HierPaths/Params.lean` for `a`, `d` and the
edge count `m`. -/
structure HierModel.Fits (H : HierModel) (a d m : ℕ) : Prop where
  depth : leafDepth H.A.x H.A.b ≤ depthOf m
  conns : H.κ ≤ depthOf m * branchOf m
  xi : H.ξ ≤ xiOf a d m
  lam : H.lam ≤ lamOf a d m

/-- A model state: the dynamic state and the abstract state. -/
structure ModelState where
  /-- The dynamic state. -/
  st : DelState
  /-- The abstract state. -/
  abs : PathDSAbsState

/-- The relation between the model state and the static part, for the constant `a`. -/
structure HierModel.Rel (H : HierModel) (a : ℕ) (ms : ModelState) : Prop where
  spec : H.Spec ms.abs.G
  fits : H.Fits a (Nat.ceil (1 / ms.abs.φ_in)) ms.abs.G.m
  inv : H.A.DelInv ms.abs.G ms.st
  deleted : ms.abs.deleted = ms.st.deleted
  vhat : ms.abs.Vhat = H.A.C.prunedSet ms.abs.G (H.A.surv ms.st)

namespace HierModel

variable (H : HierModel)

/-- The model of `Delete(e)`. -/
def delete (ms : ModelState) (e : ℕ) : ModelState :=
  ⟨H.A.deleteState ms.st e,
    { ms.abs with
      deleted := insert e ms.abs.deleted
      Vhat := H.A.C.prunedSet ms.abs.G (H.A.surv (H.A.deleteState ms.st e)) }⟩

/-- The output list of `Delete(e)`. -/
def deleteList (ms : ModelState) (e : ℕ) : List ℕ :=
  H.A.deleteOut ms.st e

/-- The support entry under the cursor of `w`. -/
def entryAt (st : DelState) (w : ℕ) : SupportEntry :=
  (H.A.C.supportArray w).getD (st.supCur w) default

/-- The model of `GetPath(u, v)`. -/
def getPath (ms : ModelState) (u v : ℕ) : Walk :=
  H.A.C.getPathOf (groupOf H.A.x H.A.b) (H.A.pick H.pairIdx ms.st) (leafDepth H.A.x H.A.b)
    (H.entryAt ms.st u) (H.entryAt ms.st v)

/-- The step count of the model of `GetPath(u, v)`. -/
def getPathOps (ms : ModelState) (u v : ℕ) : ℕ :=
  H.A.C.queryOpsOf (groupOf H.A.x H.A.b) (H.A.pick H.pairIdx ms.st) (leafDepth H.A.x H.A.b)
    (H.entryAt ms.st u) (H.entryAt ms.st v)

end HierModel

end MinCostFlow.HierPaths

end

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

public section

/-- `hierParams` has the parameters of the hierarchy. -/
theorem isHierParams_hierParams (a : ℕ) {K_init K_del K_query : ℝ} {hK_init : 0 ≤ K_init}
    {hK_del : 0 ≤ K_del} {hK_query : 0 ≤ K_query} {K_bounds cw : ℕ} {hcw_pos : 1 ≤ cw}
    {boundsSpace : ℕ → ℕ → ℕ} {initSpace delSpace querySpace : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}
    {C_space c_space : ℕ} {hC_space : 1 ≤ C_space} {hb hi hd hq} :
    IsHierParams a (hierParams a K_init K_del K_query hK_init hK_del hK_query K_bounds cw hcw_pos
      boundsSpace initSpace delSpace querySpace C_space c_space hC_space hb hi hd hq) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

namespace HierModel

variable (H : HierModel)

/-- What `Init` must give: with `Spec`, `Fits`, `Valid`, `Vhat = ∅` and `deleted = ∅`, the
initial dynamic state is related to the abstract state. -/
theorem rel_init {a : ℕ} {p : PathDSParams} {s : PathDSAbsState} (hspec : H.Spec s.G)
    (hfits : H.Fits a (Nat.ceil (1 / s.φ_in)) s.G.m) (hvalid : s.Valid p) (hV : s.Vhat = ∅)
    (hD : s.deleted = ∅) : H.Rel a ⟨DelState.init, s⟩ := by
  obtain ⟨_, _, _, _, _, hdeg1, _⟩ := hvalid
  refine ⟨hspec, hfits, H.A.delInv_init hspec.arrays, by rw [hD]; rfl, ?_⟩
  have hsurv : H.A.surv DelState.init = Finset.range H.A.C.numTerm := by
    simp [StaticArrays.surv, DelState.init, LossState.init]
  show s.Vhat = H.A.C.prunedSet s.G (H.A.surv DelState.init)
  rw [hV, hsurv, H.A.C.prunedSet_initial]
  intro w hw
  have h1 := (hdeg1 w hw).trans (hspec.deg w hw)
  obtain ⟨t, ht⟩ := Finset.card_pos.mp h1
  exact ⟨t, ((H.A.C.mem_ownedBy).mp ht).1, ((H.A.C.mem_ownedBy).mp ht).2⟩

/-- The model of operation `0`: from `s.Valid p` and the precondition of `Delete(e)`, the abstract
part of the postcondition holds, with `Vhat` the pruned set, and the relation holds again. -/
theorem model_delete {a : ℕ} {p : PathDSParams} (hp : IsHierParams a p) {ms : ModelState}
    (hrel : H.Rel a ms) (hvalid : ms.abs.Valid p) {e : ℕ} (he : e < ms.abs.G.m) :
    (H.delete ms e).abs.phiNum = ms.abs.phiNum ∧ (H.delete ms e).abs.phiDen = ms.abs.phiDen ∧
      (H.delete ms e).abs.M = ms.abs.M ∧ (H.delete ms e).abs.G = ms.abs.G ∧
      (H.delete ms e).abs.deleted = insert e ms.abs.deleted ∧
      ms.abs.Vhat ⊆ (H.delete ms e).abs.Vhat ∧ (H.delete ms e).abs.Valid p ∧
      (H.deleteList ms e).Nodup ∧
      (H.deleteList ms e).toFinset = (H.delete ms e).abs.Vhat \ ms.abs.Vhat ∧
      H.Rel a (H.delete ms e) := by
  obtain ⟨h1, h2, hGv, h4, h5, h6, h7, h8, h9, _⟩ := hvalid
  have hA := hrel.spec.arrays
  obtain ⟨hinv', hdel', hnd, hout⟩ := H.A.delete_spec hA hGv hrel.inv e
  have hlive := H.A.delete_live_facts hA hGv hrel.inv e
  have hrel' : H.Rel a (H.delete ms e) :=
    ⟨hrel.spec, hrel.fits, hinv', by
      show insert e ms.abs.deleted = (H.A.deleteState ms.st e).deleted
      rw [hdel', hrel.deleted], rfl⟩
  have hsubV : ms.abs.Vhat ⊆ (H.delete ms e).abs.Vhat := by
    rw [hrel.vhat]; exact hlive.1
  refine ⟨rfl, rfl, rfl, rfl, rfl, hsubV, ?_, hnd, ?_, hrel'⟩
  · refine ⟨h1, h2, hGv, h4, h5, h6, h7, ?_, ?_, ?_⟩
    · exact Finset.sdiff_subset
    · show insert e ms.abs.deleted ⊆ Finset.range ms.abs.G.m
      exact Finset.insert_subset (Finset.mem_range.mpr he) h9
    · have hφ : (H.delete ms e).abs.φ_in = ms.abs.φ_in := rfl
      have hcard : (H.delete ms e).abs.deleted = (H.A.deleteState ms.st e).deleted :=
        hrel'.deleted
      show (ms.abs.G.vol (H.A.C.prunedSet ms.abs.G (H.A.surv (H.A.deleteState ms.st e))) : ℝ) ≤
        p.γ_del (H.delete ms e).abs.φ_in (H.delete ms e).abs.M *
          ((H.delete ms e).abs.deleted.card : ℝ) / p.φ_out (H.delete ms e).abs.φ_in ms.abs.M
      rw [hcard, hφ]
      exact H.A.vol_prunedSet_le_valid hA hinv' hrel.spec.deg h5 hrel.fits.depth p ms.abs.φ_in
        hrel.fits.xi (by simp [PathDSParams.γ_del, hp.2.2.1])
        (by simp [PathDSParams.φ_out, hp.1])
  · rw [deleteList, hout, hrel.vhat]; rfl

/-- The model of operation `1`: from `s.Valid p` and the precondition of `GetPath(u, v)`, the
abstract part of the postcondition holds, with at most `γ_ExpPath = Γ` edges. -/
theorem model_getPath {a : ℕ} {p : PathDSParams} (hp : IsHierParams a p) {ms : ModelState}
    (hrel : H.Rel a ms) (hvalid : ms.abs.Valid p) {u v : ℕ}
    (hu : u ∈ ms.abs.G.verts \ ms.abs.Vhat) (hv : v ∈ ms.abs.G.verts \ ms.abs.Vhat) :
    (H.getPath ms u v).IsWalk ms.abs.G u v ∧ (H.getPath ms u v).verts.Nodup ∧
      (∀ e ∈ (H.getPath ms u v).edges, e ∉ ms.abs.deleted) ∧
      (∀ x ∈ (H.getPath ms u v).verts, x ∉ ms.abs.Vhat) ∧
      ((H.getPath ms u v).edges.length : ℝ) ≤ p.γ_ExpPath ms.abs.φ_in ms.abs.M ∧
      H.getPathOps ms u v ≤ 6 * 2 ^ leafDepth H.A.x H.A.b * (H.lam + 1) := by
  obtain ⟨_, _, hGv, _, h5, _⟩ := hvalid
  have hA := hrel.spec.arrays
  have hinv := hrel.inv
  rw [hrel.vhat] at hu hv ⊢
  rw [hrel.deleted]
  -- The entries under the cursors are live entries of the support arrays.
  have hentry : ∀ w ∈ ms.abs.G.verts \ H.A.C.prunedSet ms.abs.G (H.A.surv ms.st),
      w < ms.abs.G.n ∧ H.entryAt ms.st w ∈ H.A.C.supportArray w ∧
        H.A.C.entryLive (H.A.surv ms.st) (H.entryAt ms.st w) = true := by
    intro w hw
    rw [Finset.mem_sdiff, Graph.verts, Finset.mem_range] at hw
    have hc := hinv.supCur w hw.1
    have hlt : ms.st.supCur w < (H.A.C.supportArray w).length := by
      rcases Nat.lt_or_ge (ms.st.supCur w) (H.A.C.supportArray w).length with h | h
      · exact h
      · exact absurd ((H.A.supCur_eq_len_iff hinv hw.1).mp (le_antisymm hc.1 h)) hw.2
    have hval := hc.2.2 hlt
    refine ⟨hw.1, ?_, ?_⟩
    · rw [entryAt, List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem hlt
    · exact hval
  obtain ⟨hun, hux, hul⟩ := hentry u hu
  obtain ⟨hvn, hvx, hvl⟩ := hentry v hv
  have hb := hA.b_pos
  have hroot : ∀ t ∈ H.A.surv ms.st, ∀ t' ∈ H.A.surv ms.st,
      groupOf H.A.x H.A.b 0 t = groupOf H.A.x H.A.b 0 t' := by
    intro t ht t' ht'
    have h1 := ((H.A.mem_surv).mp ht).1
    have h2 := ((H.A.mem_surv).mp ht').1
    rw [hA.numTerm_eq] at h1 h2
    rw [groupOf_zero h1, groupOf_zero h2]
  have hleaf : ∀ t ∈ H.A.surv ms.st, ∀ t' ∈ H.A.surv ms.st,
      groupOf H.A.x H.A.b (leafDepth H.A.x H.A.b) t =
        groupOf H.A.x H.A.b (leafDepth H.A.x H.A.b) t' → t = t' := by
    intro t _ t' _ h
    rwa [ConnectorSystem.groupOf_leafDepth hb, ConnectorSystem.groupOf_leafDepth hb] at h
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := H.A.C.getPathOf_spec (groupOf H.A.x H.A.b)
    (H.A.pick H.pairIdx ms.st) hGv hA.fits hinv.rule (H.A.surv_subset ms.st)
    (H.A.C.isConnectorChoice_of_sibling (H.A.isSiblingChoice_pick hA hrel.spec.pairs hinv))
    hroot hleaf hrel.spec.walkLen hun hvn hux hul hvx hvl
  refine ⟨p1, p2, p3, p4, ?_, p6⟩
  have hexp : p.γ_ExpPath ms.abs.φ_in ms.abs.M =
      (gammaHP a (Nat.ceil (1 / ms.abs.φ_in)) ms.abs.M : ℝ) := by
    simp [PathDSParams.γ_ExpPath, hp.2.1]
  rw [hexp]
  have hlen : (H.getPath ms u v).edges.length ≤ gammaHP a (Nat.ceil (1 / ms.abs.φ_in)) ms.abs.M := by
    refine p5.trans (le_trans ?_ (pathLen_le_gamma a _ h5))
    unfold pathLen
    exact Nat.mul_le_mul (Nat.add_le_add_right
      (Nat.pow_le_pow_right (by norm_num) hrel.fits.depth) 1) hrel.fits.lam
  exact_mod_cast hlen

end HierModel

end

end MinCostFlow.HierPaths
