module

public import MinCostFlow.Bundle.Runs

/-!
# Bundle updates

Deleting an epoch edge removes both of its ends. An insertion is handled by
the overlay. A split assigns one bundle vertex to each run.
-/

@[expose] public section

namespace MinCostFlow.Bundle

/-- The arc property is independent of the representative. -/
theorem IsArc.of_isRotated {α : Type*} {p : α → Bool} {xs ys : List α}
    (h : IsArc p xs) (hr : ys.IsRotated xs) : IsArc p ys := by
  obtain ⟨u, v, hrot, hu, hv⟩ := h
  exact ⟨u, v, hr.trans hrot, hu, hv⟩

/-- Changing the test outside the order does not affect arcs. -/
theorem IsArc.congr_on {α : Type*} {p q : α → Bool} {xs : List α}
    (h : IsArc p xs) (he : ∀ x ∈ xs, p x = q x) : IsArc q xs := by
  obtain ⟨u, v, hr, hu, hv⟩ := h
  refine ⟨u, v, hr, ?_, ?_⟩
  · intro x hx
    rw [← he x (hr.perm.mem_iff.mpr (List.mem_append_left v hx))]
    exact hu x hx
  · intro x hx
    rw [← he x (hr.perm.mem_iff.mpr (List.mem_append_right u hx))]
    exact hv x hx

/-- Remove an edge from the epoch input, keeping empty bundle vertices. -/
def BundleState.deleteEdge (B : BundleState) (e : ℕ) : List Update × BundleState :=
  (if e ∈ B.edges then [.delete e] else [], { B with edges := B.edges.erase e })

/-- Deleting an edge preserves the bundle partition by restricting its arcs. -/
theorem BundleState.deleteEdge_spec {C : MGraph} {ρ : Rotation C}
    {e k β : ℕ} {σ : Rotation (C.applyUpdate (.delete e))}
    (B : BundleState) (h : B.IsPartition ρ k) (hσ : RotationStep β (.delete e) ρ σ) :
    let out := B.deleteEdge e
    out.2.IsPartition σ k ∧ B.graph.BatchIsValid out.1 ∧
    out.2.graph = B.graph.applyBatch out.1 ∧ out.1.length ≤ 1 ∧
    out.2.vertices = B.vertices := by
  intro out
  have hE : out.2.edges = B.edges.erase e := rfl
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · refine ⟨?_, h.2.1, ?_, ?_⟩
    · intro f hf
      obtain ⟨hne, hf⟩ := Finset.mem_erase.mp hf
      exact Finset.mem_erase.mpr ⟨hne, h.1 hf⟩
    · intro x hx
      have hx' : x ∈ edgeEnds B.edges :=
        (mem_edgeEnds _ _).mpr (Finset.mem_erase.mp ((mem_edgeEnds _ _).mp hx)).2
      exact h.2.2.1 x hx'
    · intro b hb
      obtain ⟨hs, ha⟩ := h.2.2.2 b hb
      have hsub : out.2.ends b ⊆ B.ends b := by
        intro x hx
        simp only [BundleState.ends, Finset.mem_filter, mem_edgeEnds, hE, Finset.mem_erase] at hx ⊢
        exact ⟨hx.1.2, hx.2⟩
      refine ⟨(Finset.card_le_card hsub).trans hs, ?_⟩
      let q : End → Bool := fun x => x.1 != e
      let p : End → Bool := fun x => decide (x.1 ∈ B.edges)
      let xs := ((ρ.order (B.parent b)).filter p).filter q
      have hnext : (restrictedEnds σ out.2.edges (B.parent b)).IsRotated xs := by
        have hr := isRotated_filter (fun x : End => decide (x.1 ∈ B.edges.erase e))
          (hσ (B.parent b))
        have hfilter : ((ρ.order (B.parent b)).filter q).filter
            (fun x => decide (x.1 ∈ B.edges.erase e)) = xs := by
          rw [List.filter_filter]
          unfold xs
          rw [List.filter_filter]
          congr 1
          funext x
          apply Bool.eq_iff_iff.mpr
          simp [p, q, Finset.mem_erase, and_comm]
        rw [hfilter] at hr
        exact hr
      apply IsArc.of_isRotated _ hnext
      apply (ha.filter q).congr_on
      intro x hx
      have hne : x.1 ≠ e := bne_iff_ne.mp (List.mem_filter.mp hx).2
      apply Bool.eq_iff_iff.mpr
      simp [BundleState.ends, mem_edgeEnds, hne, out, BundleState.deleteEdge]
  · by_cases he : e ∈ B.edges <;>
      simp [out, BundleState.deleteEdge, he, MGraph.BatchIsValid, MGraph.UpdateIsValid, BundleState.graph]
  · by_cases he : e ∈ B.edges
    · simp [out, BundleState.deleteEdge, he, BundleState.graph, MGraph.applyBatch, MGraph.applyUpdate]
    · simp [out, BundleState.deleteEdge, he, BundleState.graph, MGraph.applyBatch]
  · by_cases he : e ∈ B.edges <;> simp [out, BundleState.deleteEdge, he]

/-- Choose the linear representative of a proper bundle starting with its
first end. A bundle covering the whole order uses the given start. -/
noncomputable def bundleOrder (xs : List End) (inside : End → Bool) : List End :=
  open Classical in
  if xs.all inside then xs
  else if h : IsArc inside xs then h.choose else []

/-- The chosen bundle is the inside segment of a rotation. -/
theorem bundleOrder_spec {xs : List End} {inside : End → Bool} (h : IsArc inside xs) :
    ∃ outside : List End, xs.IsRotated (bundleOrder xs inside ++ outside) ∧
      (∀ x ∈ bundleOrder xs inside, inside x = true) ∧
      (∀ x ∈ outside, inside x = false) := by
  by_cases hall : xs.all inside
  · refine ⟨[], ?_, ?_, by simp⟩
    · simp [bundleOrder, hall, List.IsRotated.refl]
    · simpa [bundleOrder, hall] using List.all_eq_true.mp hall
  · simpa [bundleOrder, hall, h] using h.choose_spec

/-- The split operations for one bundle after its runs have been identified.
The first run keeps the bundle name. Subsequent runs receive consecutive
fresh names starting at `next`. -/
def bundleRunUpdates (b next : ℕ) (runs : List (List End)) : List Update :=
  (runs.drop 1).zipIdx next |>.map fun (run, fresh) =>
    .split b fresh
      ((run.filter Prod.snd).map Prod.fst).toFinset
      ((run.filter fun x => !x.2).map Prod.fst).toFinset

/-- A split plans each bundle independently and reserves distinct names for
the new runs, leaving empty bundles at the old core vertex. -/
noncomputable def bundleSplitPlan {C : MGraph} (ρ : Rotation C) (B : BundleState)
    (v : ℕ) (moved : End → Bool) : List (ℕ × List (List End)) :=
  let xs := restrictedEnds ρ B.edges v
  ((B.vertices.filter fun b => B.parent b = v).sort (· ≤ ·)).map fun b =>
    let inside : End → Bool := fun x => decide (B.bundleOf x = b)
    let ys := bundleOrder xs inside
    (b, bundleRuns moved (xs.all inside) ys)

/-- Among the admitted ends at a core vertex, the assignment to a bundle
selects an arc of that vertex's restricted rotation. -/
theorem BundleState.restricted_arc_assigned {C : MGraph} {ρ : Rotation C}
    {B : BundleState} {k b : ℕ} (h : B.IsPartition ρ k) (hb : b ∈ B.vertices) :
    IsArc (fun x => decide (B.bundleOf x = b)) (restrictedEnds ρ B.edges (B.parent b)) := by
  apply ((h.2.2.2 b hb).2).congr_on
  intro x hx
  have he := (mem_restrictedEnds ρ h.1 _ _).mp hx
  apply Bool.eq_iff_iff.mpr
  simp [BundleState.ends, mem_edgeEnds, he.1]

/-- Planned runs have size at most the cap and are arcs on their sides
of an ordered core split. -/
theorem bundleSplitPlan_runs_spec {C : MGraph} {ρ : Rotation C} {B : BundleState}
    {k v : ℕ} (h : B.IsPartition ρ k) (moved : End → Bool) {b : ℕ}
    {runs : List (List End)} (hb : (b, runs) ∈ bundleSplitPlan ρ B v moved)
    {run : List End} (hrun : run ∈ runs) :
    run.length ≤ k ∧ ∃ side : Bool, (∀ x ∈ run, moved x = side) ∧
      IsArc (fun x => run.contains x) ((restrictedEnds ρ B.edges v).filter
        fun x => moved x == side) := by
  let xs := restrictedEnds ρ B.edges v
  let inside : End → Bool := fun x => decide (B.bundleOf x = b)
  have hxnodup : xs.Nodup := (ρ.nodup _).filter _
  obtain ⟨b', hb', he⟩ := List.mem_map.mp hb
  obtain ⟨hbb, hruns⟩ := Prod.mk.inj he
  subst b'
  rw [← hruns] at hrun
  change run ∈ bundleRuns moved (xs.all inside) (bundleOrder xs inside) at hrun
  have hbv := Finset.mem_filter.mp ((Finset.mem_sort (· ≤ ·)).mp hb')
  have hsize := (h.2.2.2 b hbv.1).1
  have harc' : IsArc inside xs := by
    have ha := BundleState.restricted_arc_assigned h hbv.1
    rw [hbv.2] at ha
    exact ha
  obtain ⟨outside, hrot, him, _⟩ := bundleOrder_spec harc'
  have horder : (bundleOrder xs inside).length ≤ k := by
    have hn := (List.nodup_append.mp (hrot.perm.nodup_iff.mp hxnodup)).1
    have hs : (bundleOrder xs inside).toFinset ⊆ B.ends b := by
      intro x hx
      have hx' := List.mem_toFinset.mp hx
      have hx₀ := hrot.perm.mem_iff.mpr (List.mem_append_left outside hx')
      have he := (mem_restrictedEnds ρ h.1 _ _).mp hx₀
      apply Finset.mem_filter.mpr
      exact ⟨(mem_edgeEnds _ _).mpr he.1, of_decide_eq_true (him x hx')⟩
    rw [← List.toFinset_card_of_nodup hn]
    exact (Finset.card_le_card hs).trans hsize
  by_cases hall : xs.all inside
  · have hr : bundleOrder xs inside = xs := by simp [bundleOrder, hall]
    rw [hr, show xs.all inside = true from hall] at hrun
    obtain ⟨hle, hs⟩ := fullBundleRun_restrict_arc moved hxnodup hrun
    rw [hr] at horder
    exact ⟨hle.trans horder, hs⟩
  · have hf : xs.all inside = false := Bool.eq_false_iff.mpr hall
    rw [hf] at hrun
    obtain ⟨hle, hs⟩ := linearRun_restrict_arc moved hxnodup hrot hrun
    exact ⟨hle.trans horder, hs⟩

/-- Assign the runs of one bundle consecutive fresh names and emit their splits. -/
def bundleSplitFoldStep (v v' : ℕ) (moved : End → Bool) :
    List Update × BundleState → ℕ × List (List End) → List Update × BundleState
  | (ops, state), (b, runs) =>
    let next := state.vertices.sup id + 1
    let newOps := bundleRunUpdates b next runs
    let after := state.graph.applyBatch newOps
    let parent := fun w =>
      let run := if w = b then runs.head? else if next ≤ w then runs[w - next + 1]? else none
      match run with
      | none => state.parent w
      | some ys => if ys.head?.any moved then v' else v
    (ops ++ newOps, { vertices := after.V, edges := after.E, parent := parent
                      bundleOf := after.src })

/-- Apply the planned bundle splits, remapping each run to the appropriate
side of the core split. The edge set stays fixed. -/
noncomputable def BundleState.split {C : MGraph} (B : BundleState) (ρ : Rotation C)
    (v v' : ℕ) (St Sh : Finset ℕ) : List Update × BundleState :=
  let moved := splitEnds St Sh
  (bundleSplitPlan ρ B v moved).foldl (bundleSplitFoldStep v v' moved) ([], B)

/-- A core insertion stays outside the epoch input and preserves all
bundles. -/
theorem BundleState.insert_preserves {C : MGraph} {ρ : Rotation C}
    {e a b k β : ℕ} {σ : Rotation (C.applyUpdate (.insert e a b))}
    {B : BundleState} (h : B.IsPartition ρ k) (hu : C.UpdateIsValid (.insert e a b))
    (hσ : RotationStep β (.insert e a b) ρ σ) : B.IsPartition σ k := by
  have hEn : e ∉ B.edges := fun he => hu.1 (h.1 he)
  refine ⟨fun _ he => Finset.mem_insert_of_mem (h.1 he), h.2.1, ?_, ?_⟩
  · intro x hx
    obtain ⟨h₁, h₂⟩ := h.2.2.1 x hx
    have hne : x.1 ≠ e := fun he => hEn (he ▸ (mem_edgeEnds _ _).mp hx)
    refine ⟨h₁, h₂.trans ?_⟩
    obtain ⟨f, side⟩ := x
    cases side <;> simp [MGraph.applyUpdate, MGraph.src, hne, Function.update_of_ne]
  · intro v hv
    obtain ⟨hsize, harc⟩ := h.2.2.2 v hv
    refine ⟨hsize, ?_⟩
    let p : End → Bool := fun x => decide (x.1 ∈ B.edges)
    let w := B.parent v
    have hh := isRotated_filter p (hσ w)
    have he : (((σ.order w).filter fun x => x.1 != e).filter p) = (σ.order w).filter p := by
      rw [List.filter_filter]
      congr 1
      funext x
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, bne_iff_ne, p, decide_eq_true_eq]
      exact ⟨fun h => h.1, fun h => ⟨h, fun hx => hEn (hx ▸ h)⟩⟩
    rw [he] at hh
    exact harc.of_isRotated hh

/-- Translate one primitive core update to epoch input updates. -/
noncomputable def bundleStep {C : MGraph} (B : BundleState) (ρ : Rotation C) :
    Update → List Update × BundleState
  | .insert .. => ([], B)
  | .delete e => B.deleteEdge e
  | .split v v' St Sh => B.split ρ v v' St Sh

/-- As many splits are emitted as there are runs after the first. -/
theorem bundleRunUpdates_length (b next : ℕ) (runs : List (List End)) :
    (bundleRunUpdates b next runs).length = runs.length - 1 := by
  simp [bundleRunUpdates]

/-- Rebuilding a bundle graph from its endpoint assignment recovers the graph. -/
theorem bundleGraph_of_applied (C : MGraph) (par : ℕ → ℕ) :
    ({ vertices := C.V, edges := C.E, bundleOf := C.src, parent := par } : BundleState).graph = C := by
  cases C
  rfl

/-- The final bundle graph is obtained by applying exactly the emitted
primitive updates. -/
theorem bundleStep_graph {C : MGraph} (B : BundleState) (ρ : Rotation C) (u : Update) :
    (bundleStep B ρ u).2.graph = B.graph.applyBatch (bundleStep B ρ u).1 := by
  cases u with
  | insert => rfl
  | delete e =>
    by_cases he : e ∈ B.edges
    · simp [bundleStep, BundleState.deleteEdge, he, BundleState.graph, MGraph.applyBatch, MGraph.applyUpdate]
    · simp [bundleStep, BundleState.deleteEdge, he, BundleState.graph, MGraph.applyBatch]
  | split v v' St Sh =>
    simp only [bundleStep, BundleState.split]
    generalize bundleSplitPlan ρ B v (splitEnds St Sh) = plan
    let step := bundleSplitFoldStep v v' (splitEnds St Sh)
    have h : ∀ (s : List Update × BundleState), s.2.graph = B.graph.applyBatch s.1 →
        (plan.foldl step s).2.graph = B.graph.applyBatch (plan.foldl step s).1 := by
      induction plan with
      | nil => exact fun _ hs => hs
      | cons p rest ih =>
        intro s hs
        simp only [List.foldl_cons]
        apply ih
        obtain ⟨ops, state⟩ := s
        obtain ⟨b, runs⟩ := p
        simp only [step, bundleSplitFoldStep, bundleGraph_of_applied]
        rw [hs]
        simp only [MGraph.applyBatch, List.foldl_append]
    exact h _ rfl

end MinCostFlow.Bundle
