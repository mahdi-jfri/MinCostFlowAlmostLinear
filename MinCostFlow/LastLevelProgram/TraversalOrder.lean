module

public import MinCostFlow.LSF.TreeOps
import Mathlib.Data.List.Sort

/-!
# Parent-first orders for the distance pass

A parent has strictly smaller depth than its nonroot child. Sorting by
depth gives a witness that every parent can be visited before its child.
-/

public section

namespace MinCostFlow.LastLevelProgram

open LSF

/-- In an enumeration by nondecreasing depth, each nonroot vertex has
either the root as its parent or a parent earlier in the list. -/
theorem parent_before_child {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    (order : List ℕ) (hmem : ∀ x, x ∈ order ↔ x ∈ T.V ∧ x ≠ r)
    (hsorted : order.Pairwise fun a b => depth T r a ≤ depth T r b)
    (i : ℕ) (hi : i < order.length) :
    parent T r order[i] = r ∨ ∃ j, ∃ hj : j < order.length,
      j < i ∧ order[j] = parent T r order[i] := by
  obtain ⟨hu,hne⟩ := (hmem order[i]).1 (List.getElem_mem hi)
  by_cases hp : parent T r order[i] = r
  · exact Or.inl hp
  · have hpar := (hmem _).2 ⟨parent_mem hT hu,hp⟩
    obtain ⟨j,hj,heq⟩ := List.mem_iff_getElem.mp hpar
    have hdepth := depth_parent hT hu hne
    refine Or.inr ⟨j,hj,?_,heq⟩
    by_contra h
    rcases Nat.eq_or_lt_of_le (Nat.le_of_not_gt h) with hij | hij
    · subst j
      rw [← heq] at hdepth
      omega
    · have hd := List.pairwise_iff_getElem.mp hsorted i j hi hj hij
      rw [heq] at hd
      omega

/-- There is a parent-first enumeration covering exactly the nonroot
vertices, with no repetition. -/
theorem exists_parent_first_order {T : MGraph} {r : ℕ} (hT : IsRootedTree T r) :
    ∃ order : List ℕ, order.Nodup ∧ (∀ x, x ∈ order ↔ x ∈ T.V ∧ x ≠ r) ∧
      ∀ i, ∀ hi : i < order.length,
        parent T r order[i] = r ∨ ∃ j, ∃ hj : j < order.length,
          j < i ∧ order[j] = parent T r order[i] := by
  let orig := (T.V.erase r).toList
  let order := orig.mergeSort (fun a b => decide (depth T r a ≤ depth T r b))
  have hmem (x : ℕ) : x ∈ order ↔ x ∈ T.V ∧ x ≠ r := by
    simp [order,orig,Finset.mem_erase,and_comm]
  have hsort : order.Pairwise (fun a b => depth T r a ≤ depth T r b) := by
    simpa only [decide_eq_true_eq] using
      (List.pairwise_mergeSort (le := fun a b => decide (depth T r a ≤ depth T r b))
        (by intro a b c; simp; exact Nat.le_trans)
        (by intro a b; simp; exact Nat.le_total _ _) orig)
  exact ⟨order,(List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _),
    hmem,parent_before_child hT order hmem hsort⟩

/-- A tree incidence whose neighbor is different from the current
vertex's parent leads to a child and identifies that child's parent edge. -/
theorem treeIncidence_child_of_ne_parent {T : MGraph} {r u v e : ℕ}
    (hT : IsRootedTree T r) (he : e ∈ T.E)
    (hends : (T.tail e = u ∧ T.head e = v) ∨ (T.tail e = v ∧ T.head e = u))
    (hne : v ≠ parent T r u) :
    parent T r v = u ∧ parentEdge T r v = e ∧ v ≠ r := by
  obtain h | h := edge_parent_orientation hT he
  · rcases hends with ⟨hu,hv⟩ | ⟨hv,hu⟩ <;> rw [hu,hv] at h
    · exact False.elim (hne h.1.symm)
    · exact h
  · rcases hends with ⟨hu,hv⟩ | ⟨hv,hu⟩ <;> rw [hu,hv] at h
    · exact h
    · exact False.elim (hne h.1.symm)

/-- A set of processed vertices that contains the root and is closed
under children already contains every tree vertex. -/
theorem treeTraversal_complete {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    (processed : Set ℕ) (hr : r ∈ processed)
    (hclosed : ∀ u ∈ T.V, u ≠ r → parent T r u ∈ processed → u ∈ processed) :
    ∀ u ∈ T.V, u ∈ processed := by
  have go (d : ℕ) : ∀ u ∈ T.V, depth T r u = d → u ∈ processed := by
    induction d with
    | zero =>
      intro u hu hd
      have hroot : depth T r r = 0 := by simp [depth,forestPath_self hT.isForest]
      have he := (isAncestor_eq_iff_depth hT hu (isAncestor_root hT hu)).mp (hroot.trans hd.symm)
      rwa [← he]
    | succ d ih =>
      intro u hu hd
      by_cases he : u = r
      · rwa [he]
      · have hp := Nat.succ.inj ((depth_parent hT hu he).trans hd)
        exact hclosed u hu he (ih _ (parent_mem hT hu) hp)
  exact fun u hu => go _ u hu rfl

/-- A child of the vertex currently being scanned cannot already appear
in the queue if its parent has not yet been processed. -/
theorem treeTraversal_child_fresh {T : MGraph} {r current child : ℕ}
    (queued processed : Set ℕ) (hc : child ≠ r) (hp : parent T r child = current)
    (hcurrent : current ∉ processed)
    (hqueued : ∀ u ∈ queued, u = r ∨ parent T r u ∈ processed) :
    child ∉ queued := by
  intro h
  rcases hqueued child h with he | he
  · exact hc he
  · exact hcurrent (hp ▸ he)

/-- The parent comparison never skips a child, including at the root
where the parent pointer points to the root itself. -/
theorem treeChild_ne_parent {T : MGraph} {r x : ℕ} (hT : IsRootedTree T r)
    (hx : x ∈ T.V) (hne : x ≠ r) :
    x ≠ parent T r (parent T r x) := by
  let p := parent T r x
  have hp := parent_mem hT hx
  have hd := depth_parent hT hx hne
  intro he
  by_cases hpr : p = r
  · have hroot : parent T r r = r := by simp [parent,forestPath_self hT.isForest]
    change x = parent T r p at he
    rw [hpr,hroot] at he
    exact hne he
  · have hd' := depth_parent hT hp hpr
    change depth T r (parent T r p) + 1 = depth T r p at hd'
    change x = parent T r p at he
    rw [← he] at hd'
    change depth T r p + 1 = depth T r x at hd
    omega


/-- Moving the current vertex to the processed prefix and appending its
children preserves unique discovery and the parent characterization
of the discovered set. -/
theorem treeTraversal_queue_step {T : MGraph} {r current : ℕ}
    (done todo children : List ℕ)
    (hnodup : (done ++ current::todo).Nodup)
    (hqueued : ∀ x, x ∈ done ++ current::todo ↔
      x ∈ T.V ∧ (x = r ∨ parent T r x ∈ done))
    (hchildren : ∀ x, x ∈ children ↔ x ∈ T.V ∧ x ≠ r ∧ parent T r x = current)
    (hchildNodup : children.Nodup) :
    ((done ++ [current]) ++ (todo ++ children)).Nodup ∧
    ∀ x, x ∈ (done ++ [current]) ++ (todo ++ children) ↔
      x ∈ T.V ∧ (x = r ∨ parent T r x ∈ done ++ [current]) := by
  have hcur : current ∉ done := by
    have hd := (List.nodup_append.mp hnodup).2.2
    intro hc
    exact hd current hc current (by simp) rfl
  have hdisjoint : ∀ x ∈ done ++ current::todo, ∀ y ∈ children, x ≠ y := by
    intro x hx y hy he
    subst y
    obtain ⟨_,hnot,hparent⟩ := (hchildren x).1 hy
    rcases ((hqueued x).1 hx).2 with hr | hp
    · exact hnot hr
    · exact hcur (hparent ▸ hp)
  have heq : (done ++ [current]) ++ (todo ++ children) =
      (done ++ current::todo) ++ children := by simp [List.append_assoc]
  rw [heq]
  refine ⟨List.nodup_append.mpr ⟨hnodup,hchildNodup,hdisjoint⟩,?_⟩
  intro x
  rw [List.mem_append,hqueued,hchildren,List.mem_append,List.mem_singleton]
  constructor
  · rintro (⟨hx,hr | hp⟩ | ⟨hx,_,hp⟩)
    · exact ⟨hx,Or.inl hr⟩
    · exact ⟨hx,Or.inr (Or.inl hp)⟩
    · exact ⟨hx,Or.inr (Or.inr hp)⟩
  · rintro ⟨hx,hr | hp | hp⟩
    · exact Or.inl ⟨hx,Or.inl hr⟩
    · exact Or.inl ⟨hx,Or.inr hp⟩
    · by_cases hr : x = r
      · exact Or.inl ⟨hx,Or.inl hr⟩
      · exact Or.inr ⟨hx,hr,hp⟩

/-- Every nonroot queue entry has its parent at a smaller index. -/
@[expose] def TreeQueueParentOrder (T : MGraph) (r : ℕ) (queue : List ℕ) : Prop :=
  ∀ i, ∀ hi : i < queue.length, queue[i] ≠ r →
    ∃ j, ∃ hj : j < queue.length, j < i ∧ queue[j] = parent T r queue[i]

/-- Appending the current vertex's children keeps every parent before
its child in the discovery order. -/
theorem treeQueueParentOrder_step {T : MGraph} {r current : ℕ}
    (done todo children : List ℕ)
    (horder : TreeQueueParentOrder T r (done ++ current::todo))
    (hp : ∀ child ∈ children, parent T r child = current) :
    TreeQueueParentOrder T r ((done ++ current::todo) ++ children) := by
  let old := done ++ current::todo
  intro i hi hne
  by_cases hio : i < old.length
  · have he : (old ++ children)[i] = old[i]'hio := List.getElem_append_left hio
    obtain ⟨j,hj,hji,hpar⟩ := horder i hio (fun h => hne (he.trans h))
    have hj' : j < (old ++ children).length := by simp [List.length_append]; omega
    refine ⟨j,hj',hji,?_⟩
    rw [List.getElem_append_left hj,he]
    exact hpar
  · have hc : (old ++ children)[i] ∈ children := by
      rw [List.getElem_append_right (Nat.le_of_not_gt hio)]
      exact List.getElem_mem _
    have hj : done.length < old.length := by simp [old]
    have hj' : done.length < (old ++ children).length := by
      simp only [List.length_append]
      omega
    refine ⟨done.length,hj',by omega,?_⟩
    rw [List.getElem_append_left hj,hp _ hc]
    simp [old,List.getElem_append_right]

/-- Once the queue is empty, the processed list enumerates all vertices
of the rooted tree. -/
theorem treeTraversal_queue_finished {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    (done : List ℕ)
    (hqueued : ∀ x, x ∈ done ↔ x ∈ T.V ∧ (x = r ∨ parent T r x ∈ done)) :
    ∀ x, x ∈ done ↔ x ∈ T.V := by
  have hp : ∀ x ∈ T.V, x ∈ done :=
    treeTraversal_complete hT {x | x ∈ done}
      ((hqueued r).2 ⟨hT.2,Or.inl rfl⟩)
      (fun x hx _ hpar => (hqueued x).2 ⟨hx,Or.inr hpar⟩)
  exact fun x => ⟨fun h => ((hqueued x).1 h).1,hp x⟩

/-- Process a queue for at most the given number of vertex visits. -/
def treeQueueOrder (children : ℕ → List ℕ) : ℕ → List ℕ → List ℕ → List ℕ
  | 0, done, _ => done
  | _+1, done, [] => done
  | fuel+1, done, current::todo =>
    treeQueueOrder children fuel (done++[current]) (todo++children current)

/-- Starting from a valid queue, one visit per remaining vertex suffices
to enumerate all vertices in parent-first discovery order. -/
theorem treeQueueOrder_spec {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    (children : ℕ → List ℕ)
    (hchild : ∀ u ∈ T.V, ∀ x, x ∈ children u ↔ x ∈ T.V ∧ x ≠ r ∧ parent T r x = u)
    (hnc : ∀ u ∈ T.V, (children u).Nodup)
    (fuel : ℕ) (done todo : List ℕ) (hf : T.V.card ≤ done.length+fuel)
    (hn : (done++todo).Nodup) (ho : TreeQueueParentOrder T r (done++todo))
    (hq : ∀ x, x ∈ done++todo ↔ x ∈ T.V ∧ (x = r ∨ parent T r x ∈ done)) :
    let out := treeQueueOrder children fuel done todo
    out.Nodup ∧ TreeQueueParentOrder T r out ∧ (∀ x, x ∈ out ↔ x ∈ T.V) := by
  induction fuel generalizing done todo with
  | zero =>
    have hsub : (done++todo).toFinset ⊆ T.V := by
      intro x hx
      exact ((hq x).1 (List.mem_toFinset.mp hx)).1
    have hsize := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hn,List.length_append] at hsize
    have ht : todo = [] := List.length_eq_zero_iff.mp (by omega)
    subst todo
    have hq' : ∀ x, x ∈ done ↔ x ∈ T.V ∧ (x = r ∨ parent T r x ∈ done) := by
      simpa using hq
    exact ⟨by simpa [treeQueueOrder] using hn,by simpa [treeQueueOrder] using ho,
      treeTraversal_queue_finished hT done hq'⟩
  | succ fuel ih =>
    cases todo with
    | nil =>
      have hq' : ∀ x, x ∈ done ↔ x ∈ T.V ∧ (x = r ∨ parent T r x ∈ done) := by
        simpa using hq
      exact ⟨by simpa [treeQueueOrder] using hn,by simpa [treeQueueOrder] using ho,
      treeTraversal_queue_finished hT done hq'⟩
    | cons current todo =>
      have hcur : current ∈ T.V := ((hq current).1 (by simp)).1
      obtain ⟨hn',hq'⟩ := treeTraversal_queue_step done todo (children current)
        hn hq (hchild current hcur) (hnc current hcur)
      have ho' := treeQueueParentOrder_step done todo (children current) ho
        (fun x hx => ((hchild current hcur x).1 hx).2.2)
      have he : (done++[current]) ++ (todo++children current) =
          (done++current::todo) ++ children current := by simp [List.append_assoc]
      rw [← he] at ho'
      exact ih (done++[current]) (todo++children current)
        (by simp only [List.length_append,List.length_singleton]; omega) hn' ho' hq'

/-- The queue starts with the root and yields a complete traversal. -/
theorem treeQueueOrder_from_root {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    (children : ℕ → List ℕ)
    (hchild : ∀ u ∈ T.V, ∀ x, x ∈ children u ↔ x ∈ T.V ∧ x ≠ r ∧ parent T r x = u)
    (hnc : ∀ u ∈ T.V, (children u).Nodup) :
    let out := treeQueueOrder children T.V.card [] [r]
    out.Nodup ∧ TreeQueueParentOrder T r out ∧ (∀ x, x ∈ out ↔ x ∈ T.V) := by
  apply treeQueueOrder_spec hT children hchild hnc _ [] [r]
  · simp
  · simp
  · intro i hi hne
    have hz : i = 0 := by simpa using hi
    subst i
    exact False.elim (hne rfl)
  · intro x
    simp only [List.nil_append,List.mem_singleton,List.not_mem_nil,or_false]
    exact ⟨fun h => ⟨h.symm ▸ hT.2,h⟩,And.right⟩

/-- The completed parent-first queue starts with the root. Its tail is
the nonroot order needed by the distance pass. -/
theorem treeQueueParentOrder_split_root {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    (order : List ℕ) (hn : order.Nodup) (ho : TreeQueueParentOrder T r order)
    (hc : ∀ x, x ∈ order ↔ x ∈ T.V) :
    ∃ children, order = r::children ∧ children.Nodup ∧
      (∀ x, x ∈ children ↔ x ∈ T.V ∧ x ≠ r) ∧
      ∀ i, ∀ hi : i < children.length,
        parent T r children[i] = r ∨
          ∃ j, ∃ hj : j < children.length, j < i ∧ children[j] = parent T r children[i] := by
  cases order with
  | nil => exact False.elim (List.not_mem_nil ((hc r).2 hT.2))
  | cons x children =>
    have hzero : 0 < (x::children).length := by simp
    have hroot : x = r := by
      by_contra hne
      obtain ⟨j,_,hj,_⟩ := ho 0 hzero hne
      omega
    subst x
    obtain ⟨hr,hn'⟩ := List.nodup_cons.mp hn
    refine ⟨children,rfl,hn',?_,?_⟩
    · intro x
      constructor
      · intro hx
        exact ⟨(hc x).1 (List.mem_cons_of_mem _ hx),fun h => hr (h ▸ hx)⟩
      · intro ⟨hx,hne⟩
        exact (List.mem_cons.mp ((hc x).2 hx)).resolve_left hne
    · intro i hi
      have hi' : i+1 < (r::children).length := by simpa using hi
      have hne : (r::children)[i+1] ≠ r := by
        intro he
        have hmem := List.getElem_mem (l := children) hi
        apply hr
        rwa [show children[i] = r from he] at hmem
      obtain ⟨j,hj,hji,he⟩ := ho (i+1) hi' hne
      cases j with
      | zero => exact Or.inl he.symm
      | succ j =>
        have hj' : j < children.length := by simpa using hj
        exact Or.inr ⟨j,hj',by omega,he⟩
end MinCostFlow.LastLevelProgram
