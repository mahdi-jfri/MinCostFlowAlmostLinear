module

public import MinCostFlow.Bundle.Update
import MinCostFlow.SparseCore.GraphHelpers

/-!
# Validity of the emitted splits

One bundle's runs are disjoint. A split moves just the ends of that run,
so the remaining runs still lie at the old bundle vertex. Splitting one
bundle also leaves the ends of all other bundles in place.
-/

public section

namespace MinCostFlow.Bundle

open MinCostFlow.SparseCore

private def runSplit (b fresh : ℕ) (run : List End) : Update :=
  .split b fresh ((run.filter Prod.snd).map Prod.fst).toFinset
    ((run.filter fun x => !x.2).map Prod.fst).toFinset

private theorem mem_run_side (e : ℕ) (side : Bool) (run : List End) :
    e ∈ ((run.filter fun x => x.2 == side).map Prod.fst).toFinset ↔ (e, side) ∈ run := by
  simp only [List.mem_toFinset, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨⟨f, b⟩, ⟨hm, hb⟩, hf⟩
    simp only at hb hf
    simpa only [hb, hf] using hm
  · intro h
    exact ⟨(e, side), ⟨h, rfl⟩, rfl⟩

private theorem runSplit_src_of_not_mem (C : MGraph) (b fresh : ℕ) (run : List End)
    (x : End) (h : x ∉ run ∨ C.src x ≠ b) :
    (C.applyUpdate (runSplit b fresh run)).src x = C.src x := by
  obtain ⟨e, side⟩ := x
  have hside := mem_run_side e side run
  cases side
  · change (e ∈ ((run.filter fun x => !x.2).map Prod.fst).toFinset ↔ (e, false) ∈ run) at hside
    simp only [runSplit, MGraph.applyUpdate, MGraph.src, Bool.false_eq_true, ↓reduceIte, hside]
    split
    · rename_i he
      exact False.elim (h.elim (fun hn => hn he.1) (fun hn => hn he.2))
    · rfl
  · change (e ∈ ((run.filter Prod.snd).map Prod.fst).toFinset ↔ (e, true) ∈ run) at hside
    simp only [runSplit, MGraph.applyUpdate, MGraph.src, ↓reduceIte, hside]
    split
    · rename_i he
      exact False.elim (h.elim (fun hn => hn he.1) (fun hn => hn he.2))
    · rfl

private theorem runSplit_valid (C : MGraph) {b fresh : ℕ} (run : List End)
    (hb : b ∈ C.V) (hf : fresh ∉ C.V)
    (hEnds : ∀ x ∈ run, x.1 ∈ C.E ∧ C.src x = b) :
    C.UpdateIsValid (runSplit b fresh run) := by
  refine ⟨hb, hf, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_union.mp he with ht | hh
    · exact (hEnds (e, true) ((mem_run_side e true run).mp ht)).1
    · exact (hEnds (e, false) ((mem_run_side e false run).mp hh)).1
  · intro e he
    rcases Finset.mem_union.mp he with ht | hh
    · exact Or.inl (hEnds (e, true) ((mem_run_side e true run).mp ht)).2
    · exact Or.inr (hEnds (e, false) ((mem_run_side e false run).mp hh)).2

private theorem splitRuns_spec (C : MGraph) (b next : ℕ) (runs : List (List End))
    (hb : b ∈ C.V) (hFresh : ∀ x ∈ C.V, x < next) (hn : runs.flatten.Nodup)
    (hEnds : ∀ x ∈ runs.flatten, x.1 ∈ C.E ∧ C.src x = b) :
    let U := (runs.zipIdx next).map fun (run, fresh) => runSplit b fresh run
    C.BatchIsValid U ∧
    C.V ⊆ (C.applyBatch U).V ∧ (C.applyBatch U).E = C.E ∧
    ∀ x : End, C.src x ≠ b → (C.applyBatch U).src x = C.src x := by
  induction runs generalizing C next with
  | nil => exact ⟨trivial, Finset.Subset.rfl, rfl, fun _ _ => rfl⟩
  | cons run runs ih =>
    let u := runSplit b next run
    let C' := C.applyUpdate u
    have hV : C'.V = insert next C.V := rfl
    have hE : C'.E = C.E := rfl
    have hsub : C.V ⊆ C'.V := fun _ h => Finset.mem_insert_of_mem h
    have hf' : ∀ x ∈ C'.V, x < next + 1 := by
      intro x hx
      rw [hV] at hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Nat.lt_succ_self _
      · exact (hFresh _ hx).trans (Nat.lt_succ_self _)
    rw [List.flatten_cons, List.nodup_append] at hn
    have hs : ∀ x ∈ runs.flatten, x.1 ∈ C'.E ∧ C'.src x = b := by
      intro x hx
      have he := hEnds x (List.mem_append_right _ hx)
      have hn' : x ∉ run := fun h => hn.2.2 x h x hx rfl
      exact ⟨he.1, (runSplit_src_of_not_mem C b next run x (Or.inl hn')).trans he.2⟩
    obtain ⟨hv, hvs, hes, hNo⟩ := ih C' (next + 1) (hsub hb) hf' hn.2.1 hs
    have hu := runSplit_valid C run hb (fun h => (Nat.lt_irrefl _) (hFresh _ h))
      (fun x hx => hEnds x (List.mem_append_left _ hx))
    refine ⟨⟨hu, hv⟩, hsub.trans hvs, hes.trans hE, ?_⟩
    intro x hx
    have hh := runSplit_src_of_not_mem C b next run x (Or.inr hx)
    have hx' : C'.src x ≠ b := by rw [hh]; exact hx
    exact (hNo x hx').trans hh

private theorem plan_nodup {C : MGraph} (B : BundleState) (ρ : Rotation C) (v : ℕ)
    (p : End → Bool) : ((bundleSplitPlan ρ B v p).map Prod.fst).Nodup := by
  simp [bundleSplitPlan, List.map_map, Function.comp_def, Finset.sort_nodup]

/-- Each plan entry partitions exactly the admitted ends of its bundle. -/
theorem bundleSplitPlan_entry {C : MGraph} {B : BundleState} {ρ : Rotation C} {k v : ℕ}
    (h : B.IsPartition ρ k) (p : End → Bool) {b : ℕ} {runs : List (List End)}
    (hEntry : (b, runs) ∈ bundleSplitPlan ρ B v p) :
    b ∈ B.vertices ∧ runs.flatten.Nodup ∧
    ∀ x, x ∈ runs.flatten ↔ x.1 ∈ B.edges ∧ B.bundleOf x = b := by
  obtain ⟨b', hb', he⟩ := List.mem_map.mp hEntry
  obtain ⟨hbb, hruns⟩ := Prod.mk.inj he
  subst b'
  let xs := restrictedEnds ρ B.edges v
  let inside : End → Bool := fun x => decide (B.bundleOf x = b)
  change bundleRuns p (xs.all inside) (bundleOrder xs inside) = runs at hruns
  have hb := Finset.mem_filter.mp ((Finset.mem_sort (· ≤ ·)).mp hb')
  have ha : IsArc inside xs := by
    have hh := BundleState.restricted_arc_assigned h hb.1
    rw [hb.2] at hh
    exact hh
  have hn : xs.Nodup := (ρ.nodup _).filter _
  have hcover (x : End) (hx : x.1 ∈ B.edges ∧ B.bundleOf x = b) : x ∈ xs := by
    apply (mem_restrictedEnds ρ h.1 v x).mpr
    have he := (h.2.2.1 x ((mem_edgeEnds _ _).mpr hx.1)).2
    rw [hx.2, hb.2] at he
    exact ⟨hx.1, he.symm⟩
  refine ⟨hb.1, ?_⟩
  by_cases hall : xs.all inside
  · have hr : runs.flatten = cycleRunStart p xs := by
      rw [← hruns]
      simp [bundleRuns, bundleOrder, hall, linearRuns_flatten]
    rw [hr]
    have hp := (cycleRunStart_isRotated p xs).perm
    refine ⟨hp.nodup_iff.mp hn, ?_⟩
    intro x
    constructor
    · intro hx
      have hm := hp.mem_iff.mpr hx
      exact ⟨((mem_restrictedEnds ρ h.1 v x).mp hm).1,
        of_decide_eq_true (List.all_eq_true.mp hall x hm)⟩
    · intro hx
      exact hp.mem_iff.mp (hcover x hx)
  · obtain ⟨outside, hrot, hin, hout⟩ := bundleOrder_spec ha
    have hr : runs.flatten = bundleOrder xs inside := by
      rw [← hruns]
      simp [bundleRuns, Bool.eq_false_iff.mpr hall, linearRuns_flatten]
    rw [hr]
    refine ⟨(List.nodup_append.mp (hrot.perm.nodup_iff.mp hn)).1, ?_⟩
    intro x
    constructor
    · intro hx
      have hm := hrot.perm.mem_iff.mpr (List.mem_append_left outside hx)
      exact ⟨((mem_restrictedEnds ρ h.1 v x).mp hm).1, of_decide_eq_true (hin x hx)⟩
    · intro hx
      have htest : inside x = true := by simp [inside, hx.2]
      rcases List.mem_append.mp (hrot.perm.mem_iff.mp (hcover x hx)) with hm | hm
      · exact hm
      · exact False.elim (Bool.noConfusion (htest.symm.trans (hout x hm)))

private theorem splitFold_valid (v v' : ℕ) (p : End → Bool) (G : MGraph)
    (plan : List (ℕ × List (List End))) (s : List Update × BundleState)
    (hbase : s.2.graph = G.applyBatch s.1) (hv : G.BatchIsValid s.1)
    (hn : (plan.map Prod.fst).Nodup)
    (hEntries : ∀ (b : ℕ) (runs : List (List End)), (b, runs) ∈ plan →
      b ∈ s.2.vertices ∧ runs.flatten.Nodup ∧
      ∀ x ∈ runs.flatten, x.1 ∈ s.2.edges ∧ s.2.bundleOf x = b) :
    G.BatchIsValid (plan.foldl (bundleSplitFoldStep v v' p) s).1 := by
  induction plan generalizing s with
  | nil => exact hv
  | cons q qs ih =>
    obtain ⟨b, runs⟩ := q
    obtain ⟨ops, st⟩ := s
    let next := st.vertices.sup id + 1
    let U := bundleRunUpdates b next runs
    let s' := bundleSplitFoldStep v v' p (ops, st) (b, runs)
    have hnext : ∀ x ∈ st.graph.V, x < next :=
      fun _ hx => Nat.lt_succ_of_le (Finset.le_sup (f := id) hx)
    obtain ⟨hb, hrun, hEnds⟩ := hEntries b runs (by simp)
    have hsub : (runs.drop 1).flatten ⊆ runs.flatten := by
      rw [List.flatten_eq_flatMap, List.flatten_eq_flatMap]
      intro x hx
      obtain ⟨run, hr, hm⟩ := List.mem_flatMap.mp hx
      exact List.mem_flatMap_of_mem ((List.drop_sublist 1 runs).subset hr) hm
    have hnd : (runs.drop 1).flatten.Nodup := by
      rw [List.flatten_eq_flatMap] at hrun ⊢
      exact List.Nodup.sublist ((List.drop_sublist 1 runs).flatMap _) hrun
    have hs (x : End) : st.graph.src x = st.bundleOf x := by
      obtain ⟨e, side⟩ := x
      cases side <;> rfl
    have hf := splitRuns_spec st.graph b next (runs.drop 1) hb hnext hnd
      (fun x hx => let he := hEnds x (hsub hx); ⟨he.1, (hs x).trans he.2⟩)
    change st.graph.BatchIsValid U ∧ st.graph.V ⊆ (st.graph.applyBatch U).V ∧
      (st.graph.applyBatch U).E = st.graph.E ∧
      ∀ x : End, st.graph.src x ≠ b → (st.graph.applyBatch U).src x = st.graph.src x at hf
    simp only [List.map_cons, List.nodup_cons] at hn
    have hv' : G.BatchIsValid s'.1 := by
      change G.BatchIsValid (ops ++ U)
      rw [batchIsValid_append]
      exact ⟨hv, hbase ▸ hf.1⟩
    have hbase' : s'.2.graph = G.applyBatch s'.1 := by
      rw [show s'.1 = ops ++ U from rfl, applyBatch_append, ← hbase]
      exact bundleGraph_of_applied _ _
    rw [List.foldl_cons]
    apply ih s' hbase' hv' hn.2
    intro c ys hc
    obtain ⟨hcv, hy, hx⟩ := hEntries c ys (by simp [hc])
    have hcne : c ≠ b := fun h => hn.1 (h ▸ List.mem_map_of_mem hc)
    refine ⟨hf.2.1 hcv, hy, ?_⟩
    intro x hxy
    obtain ⟨hex, hsx⟩ := hx x hxy
    have hEq : st.graph.src x = c := (hs x).trans hsx
    have he : x.1 ∈ (st.graph.applyBatch U).E := hf.2.2.1.symm ▸ hex
    exact ⟨he, (hf.2.2.2 x (fun h => hcne (hEq.symm.trans h))).trans hEq⟩

/-- The run splits form a valid bundle-graph update batch. -/
theorem BundleState.split_valid {C : MGraph} {ρ : Rotation C} {B : BundleState}
    {k v v' : ℕ} {St Sh : Finset ℕ} (h : B.IsPartition ρ k) :
    B.graph.BatchIsValid (B.split ρ v v' St Sh).1 := by
  unfold BundleState.split
  exact splitFold_valid v v' _ B.graph _ ([], B) rfl trivial
    (plan_nodup B ρ v _) (fun _ _ he => by
      obtain ⟨hb, hn, hEnds⟩ := bundleSplitPlan_entry h _ he
      exact ⟨hb, hn, fun x hx => (hEnds x).mp hx⟩)


private theorem runSplit_src_of_mem (C : MGraph) (b fresh : ℕ) (run : List End)
    (x : End) (hx : x ∈ run) (hb : C.src x = b) :
    (C.applyUpdate (runSplit b fresh run)).src x = fresh := by
  obtain ⟨e, side⟩ := x
  cases side
  · change C.head e = b at hb
    simp [runSplit, MGraph.applyUpdate, MGraph.src, hx, hb]
  · change C.tail e = b at hb
    simp [runSplit, MGraph.applyUpdate, MGraph.src, hx, hb]

private theorem applyRuns_src_unchanged (C : MGraph) (b next : ℕ) (runs : List (List End))
    (x : End) (h : x ∉ runs.flatten ∨ C.src x ≠ b) :
    (C.applyBatch ((runs.zipIdx next).map fun (run, fresh) => runSplit b fresh run)).src x =
      C.src x := by
  induction runs generalizing C next with
  | nil => rfl
  | cons run runs ih =>
    have h₁ : x ∉ run ∨ C.src x ≠ b :=
      h.imp_left fun hn hx => hn (List.mem_append_left runs.flatten hx)
    have hsrc := runSplit_src_of_not_mem C b next run x h₁
    have h₂ : x ∉ runs.flatten ∨ (C.applyUpdate (runSplit b next run)).src x ≠ b := by
      rw [hsrc]
      exact h.imp_left fun hn hx => hn (List.mem_append_right run hx)
    simpa only [List.zipIdx_cons, List.map_cons, MGraph.applyBatch, List.foldl_cons] using
      (ih _ (next + 1) h₂).trans hsrc

private theorem applyRuns_src_member (C : MGraph) (b next : ℕ) (runs : List (List End))
    (x : End) (hb : C.src x = b) (hnext : b < next) (hn : runs.flatten.Nodup)
    (i : ℕ) (hi : i < runs.length) (hx : x ∈ runs[i]) :
    (C.applyBatch ((runs.zipIdx next).map fun (run, fresh) => runSplit b fresh run)).src x =
      next + i := by
  induction runs generalizing C next i with
  | nil => simp at hi
  | cons run runs ih =>
    simp only [List.flatten_cons, List.nodup_append] at hn
    let C' := C.applyUpdate (runSplit b next run)
    cases i with
    | zero =>
      have hm : x ∈ run := hx
      have hsrc : C'.src x = next := runSplit_src_of_mem C b next run x hm hb
      have hne : C'.src x ≠ b := fun h => (Nat.ne_of_lt hnext) (h.symm.trans hsrc)
      simpa only [List.zipIdx_cons, List.map_cons, MGraph.applyBatch, List.foldl_cons,
        Nat.add_zero] using (applyRuns_src_unchanged C' b (next + 1) runs x (Or.inr hne)).trans hsrc
    | succ i =>
      have hi' : i < runs.length := Nat.lt_of_succ_lt_succ hi
      have hm : x ∈ runs[i] := hx
      have hw : x ∈ runs.flatten := by
        rw [List.flatten_eq_flatMap]
        exact List.mem_flatMap_of_mem (f := id) (List.getElem_mem hi') hm
      have hnot : x ∉ run := fun h => hn.2.2 x h x hw rfl
      have hsrc : C'.src x = b := (runSplit_src_of_not_mem C b next run x (Or.inl hnot)).trans hb
      simpa only [List.zipIdx_cons, List.map_cons, MGraph.applyBatch, List.foldl_cons,
        Nat.add_right_comm next 1, Nat.succ_eq_add_one, Nat.add_assoc] using
        ih C' (next + 1) hsrc (hnext.trans (Nat.lt_succ_self _)) hn.2.1 i hi' hm

/-- Each noninitial run acquires the fresh bundle name assigned to it. -/
theorem bundleRunUpdates_src_member (C : MGraph) (b next : ℕ) (runs : List (List End))
    (x : End) (hb : C.src x = b) (hnext : b < next) (hn : (runs.drop 1).flatten.Nodup)
    (i : ℕ) (hi : i < (runs.drop 1).length) (hx : x ∈ (runs.drop 1)[i]) :
    (C.applyBatch (bundleRunUpdates b next runs)).src x = next + i :=
  applyRuns_src_member C b next (runs.drop 1) x hb hnext hn i hi hx

/-- The initial run keeps the bundle name, and ends at other vertices
keep their names. -/
theorem bundleRunUpdates_src_unchanged (C : MGraph) (b next : ℕ) (runs : List (List End))
    (x : End) (h : x ∉ (runs.drop 1).flatten ∨ C.src x ≠ b) :
    (C.applyBatch (bundleRunUpdates b next runs)).src x = C.src x :=
  applyRuns_src_unchanged C b next (runs.drop 1) x h


private theorem applyRuns_V_mem (C : MGraph) (b next : ℕ) (runs : List (List End)) (w : ℕ) :
    w ∈ (C.applyBatch ((runs.zipIdx next).map fun (run, fresh) => runSplit b fresh run)).V ↔
      w ∈ C.V ∨ ∃ i < runs.length, w = next + i := by
  induction runs generalizing C next with
  | nil => simp [MGraph.applyBatch]
  | cons run runs ih =>
    let C' := C.applyUpdate (runSplit b next run)
    change w ∈ (C'.applyBatch ((runs.zipIdx (next + 1)).map fun (r, f) => runSplit b f r)).V ↔ _
    rw [ih]
    change w ∈ insert next C.V ∨ _ ↔ _
    simp only [Finset.mem_insert, List.length_cons]
    constructor
    · rintro ((rfl | hw) | ⟨i, hi, rfl⟩)
      · exact Or.inr ⟨0, by omega, by simp⟩
      · exact Or.inl hw
      · exact Or.inr ⟨i + 1, by omega, by omega⟩
    · rintro (hw | ⟨i, hi, rfl⟩)
      · exact Or.inl (Or.inr hw)
      · cases i with
        | zero => exact Or.inl (Or.inl (Nat.add_zero _))
        | succ i => exact Or.inr ⟨i, by omega, by omega⟩

/-- The emitted run splits keep all old vertices and add exactly the
fresh names of the noninitial runs. -/
theorem bundleRunUpdates_V_mem (C : MGraph) (b next : ℕ) (runs : List (List End)) (w : ℕ) :
    w ∈ (C.applyBatch (bundleRunUpdates b next runs)).V ↔
      w ∈ C.V ∨ ∃ i < (runs.drop 1).length, w = next + i :=
  applyRuns_V_mem C b next (runs.drop 1) w

private theorem applyRuns_edges (C : MGraph) (b next : ℕ) (runs : List (List End)) :
    (C.applyBatch ((runs.zipIdx next).map fun (run, fresh) => runSplit b fresh run)).E = C.E := by
  induction runs generalizing C next with
  | nil => rfl
  | cons run runs ih => exact ih (C.applyUpdate (runSplit b next run)) (next + 1)

/-- Splitting runs leaves the same edge names in the bundle graph. -/
theorem bundleRunUpdates_edges (C : MGraph) (b next : ℕ) (runs : List (List End)) :
    (C.applyBatch (bundleRunUpdates b next runs)).E = C.E :=
  applyRuns_edges C b next (runs.drop 1)


/-- The run updates are valid when the corresponding ends all lie at the
bundle being split and the new names are fresh. -/
theorem bundleRunUpdates_valid (C : MGraph) (b next : ℕ) (runs : List (List End))
    (hb : b ∈ C.V) (hfresh : ∀ c ∈ C.V, c < next)
    (hn : runs.flatten.Nodup)
    (hEnds : ∀ x ∈ runs.flatten, x.1 ∈ C.E ∧ C.src x = b) :
    C.BatchIsValid (bundleRunUpdates b next runs) := by
  have hsub : (runs.drop 1).flatten.Sublist runs.flatten := by
    rw [List.flatten_eq_flatMap, List.flatten_eq_flatMap]
    exact (List.drop_sublist 1 runs).flatMap _
  exact (splitRuns_spec C b next (runs.drop 1) hb hfresh (List.Nodup.sublist hsub hn)
    (fun x hx => hEnds x (hsub.subset hx))).1

end MinCostFlow.Bundle
