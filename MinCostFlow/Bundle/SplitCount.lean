module

public import MinCostFlow.Bundle.Update
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Counting bundle splits

Each new run after the first is charged to an internal boundary pair.
A pair belongs to at most one bundle because its first end belongs to
only one bundle.
-/

public section

namespace MinCostFlow.Bundle

private def pathPairs {α : Type*} (a : α) (xs : List α) (b : α) : List (α × α) :=
  match xs with
  | [] => [(a, b)]
  | x :: xs => (a, x) :: pathPairs x xs b

private def cyclicPairs {α : Type*} : List α → List (α × α)
  | [] => []
  | x :: xs => pathPairs x xs x

private def linearPairs {α : Type*} : List α → List (α × α)
  | [] | [_] => []
  | x :: y :: ys => (x, y) :: linearPairs (y :: ys)

private def changes {α : Type*} (p : α → Bool) (xy : α × α) : Bool :=
  p xy.1 != p xy.2

private theorem pathPairs_join {α : Type*} (a b c : α) (xs ys : List α) :
    pathPairs a (xs ++ b :: ys) c = pathPairs a xs b ++ pathPairs b ys c := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simp [pathPairs, ih]

private theorem cyclicPairs_append {α : Type*} (xs ys : List α) :
    (cyclicPairs (xs ++ ys)).Perm (cyclicPairs (ys ++ xs)) := by
  cases xs with
  | nil => simp
  | cons x xs =>
    cases ys with
    | nil => simp
    | cons y ys =>
      simp only [List.cons_append, cyclicPairs, pathPairs_join]
      exact List.perm_append_comm

private theorem cyclicPairs_rotated {α : Type*} {xs ys : List α}
    (h : xs.IsRotated ys) : (cyclicPairs xs).Perm (cyclicPairs ys) := by
  obtain ⟨n, hn, rfl⟩ := List.isRotated_iff_mod.mp h
  rw [List.rotate_eq_drop_append_take hn]
  conv_lhs => rw [← List.take_append_drop n xs]
  exact cyclicPairs_append _ _

private theorem linearPairs_sublist_path {α : Type*} (a : α) (xs ys : List α) (b : α) :
    (linearPairs (a :: xs)).Sublist (pathPairs a (xs ++ ys) b) := by
  induction xs generalizing a with
  | nil => exact List.nil_sublist _
  | cons x xs ih => exact (ih x).cons_cons _

private theorem linearPairs_subset_cyclic {α : Type*} {xs inside outside : List α}
    (h : xs.IsRotated (inside ++ outside)) : linearPairs inside ⊆ cyclicPairs xs := by
  intro pair hp
  apply (cyclicPairs_rotated h).mem_iff.mpr
  cases inside with
  | nil => simp [linearPairs] at hp
  | cons a ys => exact (linearPairs_sublist_path a ys outside a).subset hp

private theorem pathPairs_fst {α : Type*} (a b : α) (xs : List α) :
    (pathPairs a xs b).map Prod.fst = a :: xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simp [pathPairs, ih]

private theorem cyclicPairs_nodup {α : Type*} {xs : List α} (hn : xs.Nodup) :
    (cyclicPairs xs).Nodup := by
  cases xs with
  | nil => exact List.nodup_nil
  | cons a ys =>
    apply List.Nodup.of_map (f := Prod.fst)
    rwa [cyclicPairs, pathPairs_fst]

private theorem linearPairs_fst_mem {α : Type*} {xs : List α} {pair : α × α}
    (h : pair ∈ linearPairs xs) : pair.1 ∈ xs := by
  cases xs with
  | nil => simp [linearPairs] at h
  | cons a ys =>
    have hp := (linearPairs_sublist_path a ys [] a).subset h
    rw [List.append_nil] at hp
    rw [← pathPairs_fst a a ys]
    exact List.mem_map_of_mem hp

private theorem pathPairs_count {α : Type*} (p : α → Bool) (a b : α) (xs : List α) :
    ((pathPairs a xs b).filter (changes p)).length = pathBdry p a xs b := by
  induction xs generalizing a with
  | nil => by_cases h : p a = p b <;> simp [pathPairs, List.filter_cons, changes, pathBdry, bne_iff_ne, h]
  | cons x xs ih =>
    by_cases h : p a = p x <;> simp [pathPairs, List.filter_cons, changes, pathBdry, bne_iff_ne, h, ih, Nat.add_comm]

private theorem cyclicPairs_count {α : Type*} (p : α → Bool) (xs : List α) :
    ((cyclicPairs xs).filter (changes p)).length = cycBdry p xs := by
  cases xs with
  | nil => rfl
  | cons a ys => exact pathPairs_count p a a ys

private theorem linearPairs_count {α : Type*} (p : α → Bool) (xs : List α) :
    ((linearPairs xs).filter (changes p)).length = linearBdry p xs := by
  suffices h : ∀ (ys : List α) (a : α),
      ((linearPairs (a :: ys)).filter (changes p)).length = linearBdry p (a :: ys) by
    cases xs with
    | nil => rfl
    | cons a ys => exact h ys a
  intro ys
  induction ys with
  | nil => intro a; rfl
  | cons x ys ih =>
    intro a
    by_cases h : p a = p x <;> simp [linearPairs, List.filter_cons, changes, linearBdry, bne_iff_ne, h, ih, Nat.add_comm]

private theorem pieces_le_of_internal_pairs {α ι : Type*} [DecidableEq α]
    (p : α → Bool) (xs : List α) (hn : xs.Nodup)
    (ids : Finset ι) (segment : ι → List α) (label : α → ι)
    (hseg : ∀ i ∈ ids, ∃ out, xs.IsRotated (segment i ++ out))
    (hlab : ∀ i ∈ ids, ∀ x ∈ segment i, label x = i) :
    (ids.sum fun i => (linearRuns p (segment i)).length - 1) ≤ cycBdry p xs := by
  classical
  let pairs := fun i => ((linearPairs (segment i)).filter (changes p)).toFinset
  let all := ((cyclicPairs xs).filter (changes p)).toFinset
  have hnd := cyclicPairs_nodup hn
  have hsub : ∀ i ∈ ids, pairs i ⊆ all := by
    intro i hi xy hxy
    obtain ⟨out, hrot⟩ := hseg i hi
    obtain ⟨hm, hchange⟩ := List.mem_filter.mp (List.mem_toFinset.mp hxy)
    exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨linearPairs_subset_cyclic hrot hm, hchange⟩)
  have hdisj : (ids : Set ι).PairwiseDisjoint pairs := by
    intro i hi j hj hne
    change Disjoint (pairs i) (pairs j)
    rw [Finset.disjoint_left]
    intro xy hxi hxj
    have hfirst (i : ι) (hi : i ∈ ids) (hm : xy ∈ pairs i) : label xy.1 = i :=
      hlab i hi xy.1 (linearPairs_fst_mem (List.mem_of_mem_filter (List.mem_toFinset.mp hm)))
    exact hne ((hfirst i hi hxi).symm.trans (hfirst j hj hxj))
  have hc : ∀ i ∈ ids, (pairs i).card = (linearRuns p (segment i)).length - 1 := by
    intro i hi
    obtain ⟨out, hr⟩ := hseg i hi
    have hd := (List.nodup_append.mp (hr.perm.nodup_iff.mp hn)).1
    have hlin : (linearPairs (segment i)).Nodup := by
      cases hsi : segment i with
      | nil => exact List.nodup_nil
      | cons a ys =>
        rw [hsi] at hd
        have hnd' : (pathPairs a ys a).Nodup := cyclicPairs_nodup hd
        apply List.Nodup.sublist _ hnd'
        simpa only [List.append_nil] using linearPairs_sublist_path a ys [] a
    exact (List.toFinset_card_of_nodup (hlin.filter _)).trans
      ((linearPairs_count p (segment i)).trans (linearRuns_count p (segment i)).symm)
  calc
    (ids.sum fun i => (linearRuns p (segment i)).length - 1) = ids.sum fun i => (pairs i).card :=
      Finset.sum_congr rfl (fun i hi => (hc i hi).symm)
    _ = (ids.biUnion pairs).card := (Finset.card_biUnion hdisj).symm
    _ ≤ all.card := Finset.card_le_card (Finset.biUnion_subset.mpr hsub)
    _ = cycBdry p xs := (List.toFinset_card_of_nodup (hnd.filter _)).trans (cyclicPairs_count p xs)


private theorem bundleSplitFold_length (v v' : ℕ) (p : End → Bool)
    (plan : List (ℕ × List (List End))) (s : List Update × BundleState) :
    (plan.foldl (bundleSplitFoldStep v v' p) s).1.length =
      s.1.length + (plan.map fun q => q.2.length - 1).sum := by
  induction plan generalizing s with
  | nil => simp
  | cons q qs ih =>
    obtain ⟨b, runs⟩ := q
    obtain ⟨ops, st⟩ := s
    simp only [List.foldl_cons, ih, bundleSplitFoldStep, List.length_append,
      bundleRunUpdates_length, List.map_cons, List.sum_cons, Nat.add_assoc]

/-- The number of splits emitted for a core split is at most the boundary
count in the original core rotation. -/
theorem BundleState.split_length_le {C : MGraph} {ρ : Rotation C} {B : BundleState}
    {k v v' : ℕ} {St Sh : Finset ℕ} (h : B.IsPartition ρ k) :
    (B.split ρ v v' St Sh).1.length ≤ cycBdry (splitEnds St Sh) (ρ.order v) := by
  let p := splitEnds St Sh
  let ids := B.vertices.filter fun b => B.parent b = v
  let xs := restrictedEnds ρ B.edges v
  let inside (b : ℕ) (x : End) : Bool := decide (B.bundleOf x = b)
  let segment (b : ℕ) : List End :=
    if xs.all (inside b) then cycleRunStart p xs else bundleOrder xs (inside b)
  have hArc (b : ℕ) (hb : b ∈ ids) : IsArc (inside b) xs := by
    have hbv := Finset.mem_filter.mp hb
    have ha := BundleState.restricted_arc_assigned h hbv.1
    rw [hbv.2] at ha
    exact ha
  have hseg (b : ℕ) (hb : b ∈ ids) : ∃ out, xs.IsRotated (segment b ++ out) := by
    by_cases hs : xs.all (inside b)
    · refine ⟨[], ?_⟩
      simpa [segment, hs] using cycleRunStart_isRotated p xs
    · obtain ⟨out, hr, _⟩ := bundleOrder_spec (hArc b hb)
      exact ⟨out, by simpa [segment, hs] using hr⟩
  have hlabel (b : ℕ) (hb : b ∈ ids) (x : End) (hx : x ∈ segment b) : B.bundleOf x = b := by
    by_cases hs : xs.all (inside b)
    · have hm : x ∈ cycleRunStart p xs := by simpa [segment, hs] using hx
      exact of_decide_eq_true (List.all_eq_true.mp hs x
        ((cycleRunStart_isRotated p xs).perm.mem_iff.mpr hm))
    · obtain ⟨_, _, hmem, _⟩ := bundleOrder_spec (hArc b hb)
      exact of_decide_eq_true (hmem x (by simpa [segment, hs] using hx))
  have hcounts := pieces_le_of_internal_pairs p xs ((ρ.nodup v).filter _)
    ids segment B.bundleOf hseg hlabel
  have heq (b : ℕ) :
      bundleRuns p (xs.all (inside b)) (bundleOrder xs (inside b)) =
        linearRuns p (segment b) := by
    by_cases hs : xs.all (inside b) <;> simp [bundleRuns, bundleOrder, segment, hs]
  have hList : ((ids.sort (· ≤ ·)).map (fun b => (linearRuns p (segment b)).length - 1)).sum =
      ids.sum (fun b => (linearRuns p (segment b)).length - 1) := by
    change (((ids.sort (· ≤ ·)).map _).sum) = (ids.val.map _).sum
    rw [← Finset.sort_eq ids (· ≤ ·)]
    rfl
  apply Nat.le_trans _ (cycBdry_filter_le p (fun x => decide (x.1 ∈ B.edges)) (ρ.order v))
  unfold BundleState.split
  rw [bundleSplitFold_length]
  simp only [List.length_nil, Nat.zero_add]
  change (((ids.sort (· ≤ ·)).map (fun b =>
    (b, bundleRuns p (xs.all (inside b)) (bundleOrder xs (inside b))))).map
      (fun q => q.2.length - 1)).sum ≤ cycBdry p xs
  simp only [List.map_map, Function.comp_def, heq, hList]
  exact hcounts


private theorem apply_runs_vertex_growth (C : MGraph) (b next : ℕ) (runs : List (List End))
    (hfresh : ∀ x ∈ C.V, x < next) :
    (C.applyBatch ((runs.zipIdx next).map fun (run, fresh) =>
      .split b fresh ((run.filter Prod.snd).map Prod.fst).toFinset
        ((run.filter fun x => !x.2).map Prod.fst).toFinset)).V.card = C.V.card + runs.length := by
  induction runs generalizing C next with
  | nil => rfl
  | cons run runs ih =>
    let u := Update.split b next ((run.filter Prod.snd).map Prod.fst).toFinset
      ((run.filter fun x => !x.2).map Prod.fst).toFinset
    have hv : (C.applyUpdate u).V = insert next C.V := rfl
    have hnext : ∀ x ∈ (C.applyUpdate u).V, x < next + 1 := by
      intro x hx
      rw [hv] at hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Nat.lt_succ_self _
      · exact (hfresh x hx).trans (Nat.lt_succ_self _)
    have hcard : (C.applyUpdate u).V.card = C.V.card + 1 := by
      rw [hv, Finset.card_insert_of_notMem (fun h => (Nat.lt_irrefl _) (hfresh _ h))]
    simp only [List.zipIdx_cons, List.map_cons, MGraph.applyBatch, List.foldl_cons]
    have hh := ih (C.applyUpdate u) (next + 1) hnext
    rw [hcard] at hh
    simpa only [MGraph.applyBatch, List.length_cons, Nat.add_right_comm C.V.card, Nat.add_assoc] using hh

private theorem bundleSplitFold_vertices (v v' : ℕ) (p : End → Bool)
    (plan : List (ℕ × List (List End))) (s : List Update × BundleState) :
    (plan.foldl (bundleSplitFoldStep v v' p) s).2.vertices.card =
      s.2.vertices.card + (plan.map fun q => q.2.length - 1).sum := by
  induction plan generalizing s with
  | nil => simp
  | cons q qs ih =>
    obtain ⟨b, runs⟩ := q
    obtain ⟨ops, st⟩ := s
    let next := st.vertices.sup id + 1
    have hnext : ∀ x ∈ st.graph.V, x < next :=
      fun _ hx => Nat.lt_succ_of_le (Finset.le_sup (f := id) hx)
    have hsingle := apply_runs_vertex_growth st.graph b next (runs.drop 1) hnext
    change (st.graph.applyBatch (bundleRunUpdates b next runs)).V.card =
      st.vertices.card + (runs.drop 1).length at hsingle
    rw [List.length_drop] at hsingle
    simp only [List.foldl_cons, ih, bundleSplitFoldStep, List.map_cons, List.sum_cons]
    rw [hsingle, Nat.add_assoc]

/-- Each emitted bundle split increases the vertex count by one. -/
theorem BundleState.split_vertex_growth {C : MGraph} (B : BundleState) (ρ : Rotation C)
    (v v' : ℕ) (St Sh : Finset ℕ) :
    (B.split ρ v v' St Sh).2.vertices.card =
      B.vertices.card + (B.split ρ v v' St Sh).1.length := by
  simp only [BundleState.split, bundleSplitFold_length, bundleSplitFold_vertices,
    List.length_nil, Nat.zero_add]

end MinCostFlow.Bundle
