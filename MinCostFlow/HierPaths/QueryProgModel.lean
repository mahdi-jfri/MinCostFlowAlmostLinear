module

public import MinCostFlow.HierPaths.QueryProgMain

/-!
# The walk in the GetPath buffers

The two attachment calls and the route call fill the buffers with the steps of the walk
before loop erasure. These lemmas give its length and identify the erased stack.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open Cited Spanner

/-- The length held in the support entry counts the copied steps. -/
theorem length_attachmentCopy_steps (C : ConnectorSystem) {G : Graph} (hC : C.FitsGraph G)
    {v : ℕ} {entry : SupportEntry} (he : entry ∈ C.supportArray v) (fwd : Bool) :
    (Walk.steps (attachmentCopy C fwd entry)).length = attachmentLength entry := by
  cases entry with
  | term t => rfl
  | onWalk c k =>
    by_cases hz : k = 0
    · subst k; rfl
    obtain ⟨_, hV, hk⟩ := support_onWalk_bounds C hC he
    have hVk : k + 1 ≤ (C.walk c).verts.length := by omega
    have hkeep : ((C.walk c).verts.take (k + 1)).length =
        ((C.walk c).edges.take k).length + 1 := by
      simp [List.length_take, min_eq_left hk, min_eq_left hVk]
    simp only [attachmentCopy, hz, ↓reduceIte, attachmentLength]
    rw [length_steps_copyWalk hkeep, List.length_take, min_eq_left hk]

namespace HierConcrete

/-- The walk before loop erasure, using the pair tables read by the program. -/
def queryInputWalk (X : HierConcrete) (u v : ℕ) : Walk :=
  X.H.A.C.joinWalk (groupOf X.H.A.x X.H.A.b) X.tablePick X.depth
    (X.H.entryAt X.ms.st u) (X.H.entryAt X.ms.st v)

/-- The vertex under a live cursor has a support entry and its terminal survives. -/
theorem query_support {a v : ℕ} (X : HierConcrete) (h : X.H.Rel a X.ms)
    (hG : X.ms.abs.G.IsValid) (hv : v ∈ X.ms.abs.G.verts \ X.ms.abs.Vhat) :
    v < X.n ∧ X.H.entryAt X.ms.st v ∈ X.H.A.C.supportArray v ∧
      X.H.A.C.entryLive (X.H.A.surv X.ms.st) (X.H.entryAt X.ms.st v) = true ∧
      X.H.A.C.entryTerm (X.H.entryAt X.ms.st v) ∈ X.H.A.surv X.ms.st ∧
      (X.H.A.C.supportWalk (X.H.entryAt X.ms.st v)).IsWalk X.ms.abs.G v
        (X.H.A.C.owner (X.H.A.C.entryTerm (X.H.entryAt X.ms.st v))) := by
  rw [h.vhat, Finset.mem_sdiff, Graph.verts, Finset.mem_range] at hv
  have hc := h.inv.supCur v hv.1
  have hidx : X.ms.st.supCur v < (X.H.A.C.supportArray v).length := by
    exact lt_of_le_of_ne hc.1 fun he => hv.2 ((X.H.A.supCur_eq_len_iff h.inv hv.1).mp he)
  have hmem : X.H.entryAt X.ms.st v ∈ X.H.A.C.supportArray v := by
    rw [HierModel.entryAt, List.getD_eq_getElem _ _ hidx]
    exact List.getElem_mem hidx
  have hlive := hc.2.2 hidx
  obtain ⟨ht, hw, _⟩ := X.H.A.C.supportWalk_spec hG h.spec.arrays.fits h.inv.rule hv.1 hmem hlive
  exact ⟨hv.1, hmem, hlive, ht, hw⟩

/-- The terminal group at the root contains every surviving terminal. -/
theorem query_same_root {a t t' : ℕ} (X : HierConcrete) (h : X.H.Rel a X.ms)
    (ht : t ∈ X.H.A.surv X.ms.st) (ht' : t' ∈ X.H.A.surv X.ms.st) :
    groupOf X.H.A.x X.H.A.b 0 t = groupOf X.H.A.x X.H.A.b 0 t' := by
  have h₁ := (X.H.A.mem_surv.mp ht).1
  have h₂ := (X.H.A.mem_surv.mp ht').1
  rw [h.spec.arrays.numTerm_eq] at h₁ h₂
  rw [groupOf_zero h₁, groupOf_zero h₂]

/-- The support attachments and stored route produce a walk within the scratch capacity. -/
theorem queryInputWalk_spec {a u v : ℕ} (X : HierConcrete) (h : X.H.Rel a X.ms)
    (hG : X.ms.abs.G.IsValid)
    (hu : u ∈ X.ms.abs.G.verts \ X.ms.abs.Vhat) (hv : v ∈ X.ms.abs.G.verts \ X.ms.abs.Vhat) :
    (X.queryInputWalk u v).IsWalk X.ms.abs.G u v ∧
      (X.queryInputWalk u v).edges.length ≤ X.queryCapacity ∧
      loopErase (X.queryInputWalk u v) = X.H.getPath X.ms u v := by
  obtain ⟨_, hmemU, _, ht, hU⟩ := X.query_support h hG hu
  obtain ⟨_, hmemV, _, ht', hV⟩ := X.query_support h hG hv
  have hr := X.query_same_root h ht ht'
  have hleaf : ∀ t ∈ X.H.A.surv X.ms.st, ∀ t' ∈ X.H.A.surv X.ms.st,
      groupOf X.H.A.x X.H.A.b X.depth t = groupOf X.H.A.x X.H.A.b X.depth t' → t = t' := by
    intro t _ t' _ hgroup
    change groupOf _ _ (leafDepth _ _) _ = groupOf _ _ (leafDepth _ _) _ at hgroup
    rwa [ConnectorSystem.groupOf_leafDepth h.spec.arrays.b_pos,
      ConnectorSystem.groupOf_leafDepth h.spec.arrays.b_pos] at hgroup
  obtain ⟨hRoute, _, _, hRouteLen⟩ := X.H.A.C.route_spec _ X.tablePick hG h.spec.arrays.fits
    h.inv.rule (X.H.A.surv_subset X.ms.st)
    (X.tablePick_isConnectorChoice h.spec.arrays h.spec.pairs h.inv)
    hleaf h.spec.walkLen X.depth 0 _ _ (Nat.zero_add _) ht ht' hr
  have hlen : ∀ {w e}, e ∈ X.H.A.C.supportArray w → (X.H.A.C.supportWalk e).edges.length ≤ X.H.lam := by
    intro w e he
    cases e with
    | term t => exact Nat.zero_le _
    | onWalk c k =>
      have hc := (support_onWalk_bounds X.H.A.C h.spec.arrays.fits he).1
      rw [ConnectorSystem.supportWalk, edges_reverse, List.length_reverse]
      exact (length_edges_prefix_le _ _).trans (h.spec.walkLen c hc)
  have hULen := hlen hmemU
  have hVLen := hlen hmemV
  refine ⟨Walk.isWalk_append hU (Walk.isWalk_append hRoute (Walk.isWalk_reverse hV)), ?_, ?_⟩
  · unfold queryInputWalk ConnectorSystem.joinWalk queryCapacity
    rw [length_edges_append, length_edges_append, edges_reverse, List.length_reverse]
    have hpow : 1 ≤ 2 ^ X.depth := Nat.one_le_two_pow
    have hsplit : 2 ^ X.depth + 1 = (2 ^ X.depth - 1) + 1 + 1 := by omega
    rw [hsplit, Nat.add_mul, Nat.add_mul, Nat.one_mul]
    omega
  · unfold queryInputWalk HierModel.getPath ConnectorSystem.getPathOf ConnectorSystem.joinWalk
    rw [(X.tablePick_route_eq h.spec.arrays h.spec.pairs h.inv X.depth 0 _ _
      (Nat.zero_add _).le ht ht' hr).1]
    rfl

/-- The two attachment calls and the route call fill the buffers in the order of the walk. -/
theorem queryInputWalk_steps {a u v : ℕ} (X : HierConcrete) (h : X.H.Rel a X.ms)
    (hG : X.ms.abs.G.IsValid)
    (hu : u ∈ X.ms.abs.G.verts \ X.ms.abs.Vhat) (hv : v ∈ X.ms.abs.G.verts \ X.ms.abs.Vhat) :
    let eu := X.H.entryAt X.ms.st u
    let ev := X.H.entryAt X.ms.st v
    Walk.steps (X.queryInputWalk u v) =
      Walk.steps (attachmentCopy X.H.A.C false eu) ++
        (routeSteps X.H.A.C X.H.A.x X.H.A.b X.tablePick X.depth 0
          (X.H.A.C.entryTerm eu) (X.H.A.C.entryTerm ev) ++
          Walk.steps (attachmentCopy X.H.A.C true ev)) := by
  dsimp only
  obtain ⟨_, hmemU, _, ht, hU⟩ := X.query_support h hG hu
  obtain ⟨_, hmemV, _, ht', _⟩ := X.query_support h hG hv
  have hChoice := X.tablePick_isConnectorChoice h.spec.arrays h.spec.pairs h.inv
  have hReady := X.H.A.C.routeReady_of_choice _ _ hChoice X.depth 0 _ _ ht ht'
    (X.query_same_root h ht ht')
  have hStored : ∀ c < X.H.A.C.numConn, WellFormed (X.H.A.C.walk c) := fun c hc =>
    IsWalk.wellFormed (h.spec.arrays.fits.2 c hc).2.2
  have hRoute := X.H.A.C.wellFormed_route_ready _ _ hStored X.depth 0 _ _ hReady
  unfold queryInputWalk ConnectorSystem.joinWalk routeSteps
  rw [steps_append (IsWalk.wellFormed hU), steps_append hRoute,
    attachmentCopy_eq _ h.spec.arrays.fits hmemU, attachmentCopy_eq _ h.spec.arrays.fits hmemV]
  rfl

/-- The loop erasure of the input walk is the walk written from the erased step stack.
For an empty input the stack is empty and the start register still holds the query vertex. -/
theorem queryInputWalk_erase {a u v : ℕ} (X : HierConcrete) (h : X.H.Rel a X.ms)
    (hG : X.ms.abs.G.IsValid)
    (hu : u ∈ X.ms.abs.G.verts \ X.ms.abs.Vhat) (hv : v ∈ X.ms.abs.G.verts \ X.ms.abs.Vhat) :
    ofSteps u (arrFrom u [] (Walk.steps (X.queryInputWalk u v))) = X.H.getPath X.ms u v := by
  obtain ⟨hw, _, hpath⟩ := X.queryInputWalk_spec h hG hu hv
  rw [← hpath]
  rcases hw.2.2 with ⟨heV, heE, _⟩ | ⟨_, _, hhead, _⟩
  · have hempty : X.queryInputWalk u v = Walk.empty := by
      cases h : X.queryInputWalk u v
      simp [h, Walk.empty] at heV heE ⊢
      exact ⟨heV, heE⟩
    simp [hempty, Walk.steps, Walk.empty, arrFrom, ofSteps, loopErase]
  · obtain ⟨tail, hV⟩ : ∃ tail, (X.queryInputWalk u v).verts = u :: tail := by
      cases h : (X.queryInputWalk u v).verts with
      | nil => simp [h] at hhead
      | cons v' tail =>
        simp only [h, List.head?_cons, Option.some.injEq] at hhead
        exact ⟨tail, by rw [hhead]⟩
    rw [loopErase_eq_eraseOut _ hV, Walk.steps, hV, List.tail_cons]

/-- The step lists supplied to the eraser have the same size and their vertices lie in the graph. -/
theorem queryInputWalk_stepBounds {a u v : ℕ} (X : HierConcrete) (h : X.H.Rel a X.ms)
    (hG : X.ms.abs.G.IsValid)
    (hu : u ∈ X.ms.abs.G.verts \ X.ms.abs.Vhat) (hv : v ∈ X.ms.abs.G.verts \ X.ms.abs.Vhat) :
    let ss := Walk.steps (X.queryInputWalk u v)
    ss.length ≤ X.queryCapacity ∧ (∀ q ∈ ss, q.2 < X.n) := by
  obtain ⟨hw, hcap, _⟩ := X.queryInputWalk_spec h hG hu hv
  dsimp only
  constructor
  · rw [Walk.steps, List.length_zip]
    exact (Nat.min_le_left _ _).trans hcap
  · intro q hq
    apply Walk.isWalk_verts_lt hG hw q.2
    exact List.mem_of_mem_tail (List.of_mem_zip hq).2

end HierConcrete

end MinCostFlow.HierPaths
