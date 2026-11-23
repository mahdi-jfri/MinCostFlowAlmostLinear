module

public import MinCostFlow.LastLevelProgram.TraversalAdjacency
public import MinCostFlow.LastLevelProgram.TraversalOrder
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Counting adjacency records in the tree traversal

Each selected edge contributes one record at each of its two distinct
endpoints. Summed over the compact vertices, the scan lengths count
exactly twice the selected edge count.
-/

public section

namespace MinCostFlow.LastLevelProgram

open scoped BigOperators

/-- The incidence list grows by one exactly at the two edge endpoints. -/
theorem treeIncidenceList_length_succ (records : ℕ) (u v : ℕ → ℕ) (x k : ℕ) :
    (treeIncidenceList records u v x (k+1)).length =
      (treeIncidenceList records u v x k).length +
        (if x = u k ∨ x = v k then 1 else 0) := by
  by_cases hu : x = u k
  · simp [treeIncidenceList,hu]
  · by_cases hv : x = v k
    · simp only [treeIncidenceList,ite_eq_right hu,ite_eq_left hv,List.length_cons,ite_eq_left (Or.inr hv : x = u k ∨ x = v k)]
    · simp [treeIncidenceList,hu,hv]

/-- Scanning every vertex once reads exactly two records per selected
tree edge. This count also applies when the tree has one vertex. -/
theorem treeIncidenceList_sum_length (records n k : ℕ) (u v : ℕ → ℕ)
    (hends : ∀ i < k, u i < n ∧ v i < n ∧ u i ≠ v i) :
    ∑ x ∈ Finset.range n, (treeIncidenceList records u v x k).length = 2*k := by
  induction k with
  | zero => simp [treeIncidenceList]
  | succ k ih =>
    obtain ⟨hu,hv,hne⟩ := hends k (Nat.lt_succ_self _)
    have hcounts (x : ℕ) : (if x = u k ∨ x = v k then 1 else 0 : ℕ) =
        (if x = u k then 1 else 0) + (if x = v k then 1 else 0) := by
      by_cases hx : x = u k
      · simp [hx,hne]
      · by_cases hy : x = v k <;> simp [hx,hy,Ne.symm hne]
    simp only [treeIncidenceList_length_succ,hcounts,Finset.sum_add_distrib]
    rw [ih fun i hi => hends i (hi.trans (Nat.lt_succ_self _))]
    simp [hu,hv,Nat.mul_succ]

/-- The reverse insertion list contains all and only this vertex's
incidences. Distinct endpoints keep the two cases disjoint. -/
theorem mem_treeIncidenceList {records k vertex ptr : ℕ} {u v : ℕ → ℕ}
    (hends : ∀ i < k, u i ≠ v i) :
    ptr ∈ treeIncidenceList records u v vertex k ↔ treeIncidenceFor records u v k vertex ptr := by
  induction k with
  | zero => simp [treeIncidenceList,treeIncidenceFor]
  | succ k ih =>
    have hprev := ih (fun i hi => hends i (hi.trans (Nat.lt_succ_self _)))
    have hne := hends k (Nat.lt_succ_self _)
    have hsplit : treeIncidenceFor records u v (k+1) vertex ptr ↔
        ((u k = vertex ∧ ptr = records+6*k) ∨ (v k = vertex ∧ ptr = records+6*k+3)) ∨
          treeIncidenceFor records u v k vertex ptr := by
      constructor
      · rintro ⟨i,hi,h⟩
        rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hi) with hik | hik
        · subst i
          exact Or.inl h
        · exact Or.inr ⟨i,hik,h⟩
      · rintro (h | ⟨i,hi,h⟩)
        · exact ⟨k,Nat.lt_succ_self _,h⟩
        · exact ⟨i,hi.trans (Nat.lt_succ_self _),h⟩
    rw [hsplit,treeIncidenceList]
    by_cases hu : vertex = u k
    · subst vertex
      simp [hprev,Ne.symm hne]
    · by_cases hv : vertex = v k
      · subst vertex
        simp [hprev,hu,hne]
      · simp [hprev,hu,hv,Ne.symm hu,Ne.symm hv]

/-- A vertex's incidence list contains no repeated record address. -/
theorem treeIncidenceList_nodup (records k vertex : ℕ) (u v : ℕ → ℕ)
    (hends : ∀ i < k, u i ≠ v i) :
    (treeIncidenceList records u v vertex k).Nodup := by
  induction k with
  | zero => simp [treeIncidenceList]
  | succ k ih =>
    have hp : ∀ i < k, u i ≠ v i := fun i hi => hends i (hi.trans (Nat.lt_succ_self _))
    have hnew (d : ℕ) (hd : d = 0 ∨ d = 3) :
        records+6*k+d ∉ treeIncidenceList records u v vertex k := by
      intro h
      obtain ⟨i,hi,hi'⟩ := (mem_treeIncidenceList hp).mp h
      rcases hi' with ⟨_,he⟩ | ⟨_,he⟩ <;> rcases hd with rfl | rfl <;> omega
    rw [treeIncidenceList]
    split
    · exact List.nodup_cons.mpr ⟨by simpa using hnew 0 (Or.inl rfl),ih hp⟩
    · split
      · exact List.nodup_cons.mpr ⟨hnew 3 (Or.inr rfl),ih hp⟩
      · exact ih hp

open LSF in
/-- The incidence list of the parent contains a record for each child
and its parent edge. -/
theorem treeIncidenceList_child {T : MGraph} {r x : ℕ} (hT : IsRootedTree T r)
    (hx : x ∈ T.V) (hne : x ≠ r)
    (mem : ℕ → ℕ) (adj records n k : ℕ) (edge : ℕ → ℕ)
    (ha : adj+n ≤ records)
    (hends : ∀ i < k, T.tail (edge i) < n ∧ T.head (edge i) < n ∧ T.tail (edge i) ≠ T.head (edge i))
    (hcover : ∀ e ∈ T.E, ∃ i < k, edge i = e) :
    let u := T.tail ∘ edge
    let v := T.head ∘ edge
    let out := originalTreeAdjacencyMemory mem adj records u v edge k
    ∃ ptr ∈ treeIncidenceList records u v (parent T r x) k,
      out ptr = x ∧ out (ptr+1) = parentEdge T r x := by
  intro u v out
  obtain ⟨i,hi,he⟩ := hcover _ (parentEdge_mem hT hx hne)
  obtain ⟨hu,hv,hn⟩ := hends i hi
  obtain ⟨h0,h1,h3,h4⟩ := originalTreeAdjacencyMemory_fields mem adj records n u v edge ha k
    (fun j hj => ⟨(hends j hj).1,(hends j hj).2.1⟩) i hi
  have hm (ptr : ℕ) := mem_treeIncidenceList (ptr := ptr) (records := records) (u := u) (v := v)
    (vertex := parent T r x) (fun j hj => (hends j hj).2.2)
  have hpair := parentEdge_endpoints hT hx hne
  rw [← he] at hpair
  have htmem : u i = x ∨ u i = parent T r x := by
    change T.tail (edge i) = x ∨ T.tail (edge i) = parent T r x
    have hh : T.tail (edge i) ∈ ({x,parent T r x} : Set ℕ) := by rw [← hpair]; simp
    simpa using hh
  have hhmem : v i = x ∨ v i = parent T r x := by
    change T.head (edge i) = x ∨ T.head (edge i) = parent T r x
    have hh : T.head (edge i) ∈ ({x,parent T r x} : Set ℕ) := by rw [← hpair]; simp
    simpa using hh
  change u i ≠ v i at hn
  have hcases : (u i = x ∧ v i = parent T r x) ∨ (u i = parent T r x ∧ v i = x) := by
    rcases htmem with h | h <;> rcases hhmem with h' | h'
    · exact False.elim (hn (h.trans h'.symm))
    · exact Or.inl ⟨h,h'⟩
    · exact Or.inr ⟨h,h'⟩
    · exact False.elim (hn (h.trans h'.symm))
  obtain h | h := hcases
  · have ht : u i = x := h.1
    have hh : v i = parent T r x := h.2
    refine ⟨records+6*i+3,(hm _).mpr ⟨i,hi,Or.inr ⟨hh,rfl⟩⟩,h3.trans ht,?_⟩
    exact h4.trans he
  · have ht : u i = parent T r x := h.1
    have hh : v i = x := h.2
    exact ⟨records+6*i,(hm _).mpr ⟨i,hi,Or.inl ⟨ht,rfl⟩⟩,h0.trans hh,h1.trans he⟩

/-- Distinct selected edge indices ensure that a nonparent neighbor
appears once. Its parent edge determines the corresponding record. -/
theorem treeIncidenceList_children_nodup
    (mem : ℕ → ℕ) (adj records n k vertex parent : ℕ) (u v edge : ℕ → ℕ)
    (ha : adj+n ≤ records) (hends : ∀ i < k, u i < n ∧ v i < n ∧ u i ≠ v i)
    (hinj : ∀ i < k, ∀ j < k, edge i = edge j → i = j)
    (incoming : ℕ → ℕ)
    (hchild : ∀ ptr ∈ treeIncidenceList records u v vertex k,
      let out := originalTreeAdjacencyMemory mem adj records u v edge k
      out ptr ≠ parent → incoming (out ptr) = out (ptr+1)) :
    let out := originalTreeAdjacencyMemory mem adj records u v edge k
    ((treeIncidenceList records u v vertex k).filter (fun ptr => out ptr != parent) |>.map out).Nodup := by
  intro out
  have hne i hi := (hends i hi).2.2
  apply List.Nodup.map_on _ ((treeIncidenceList_nodup records k vertex u v hne).filter _)
  intro a ha' b hb' heq
  obtain ⟨haIn,haNe⟩ := List.mem_filter.mp ha'
  obtain ⟨hbIn,hbNe⟩ := List.mem_filter.mp hb'
  have hfield (ptr : ℕ) (hptr : ptr ∈ treeIncidenceList records u v vertex k) :
      ∃ i < k, out (ptr+1) = edge i ∧
        ((u i = vertex ∧ ptr = records+6*i) ∨ (v i = vertex ∧ ptr = records+6*i+3)) := by
    obtain ⟨i,hi,hor⟩ := (mem_treeIncidenceList hne).mp hptr
    obtain ⟨_,h1,_,h4⟩ := originalTreeAdjacencyMemory_fields mem adj records n u v edge ha k
      (fun j hj => ⟨(hends j hj).1,(hends j hj).2.1⟩) i hi
    refine ⟨i,hi,?_,hor⟩
    rcases hor with ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact h1
    · exact h4
  obtain ⟨i,hi,haE,haO⟩ := hfield a haIn
  obtain ⟨j,hj,hbE,hbO⟩ := hfield b hbIn
  have hae := hchild a haIn (by simpa using haNe)
  have hbe := hchild b hbIn (by simpa using hbNe)
  change incoming (out a) = out (a+1) at hae
  change incoming (out b) = out (b+1) at hbe
  have hij : i = j := hinj i hi j hj
    (haE.symm.trans (hae.symm.trans ((congrArg incoming heq).trans (hbe.trans hbE))))
  subst j
  rcases haO with ⟨h,rfl⟩ | ⟨h,rfl⟩ <;> rcases hbO with ⟨h',rfl⟩ | ⟨h',rfl⟩
  · rfl
  · exact False.elim (hne i hi (h.trans h'.symm))
  · exact False.elim (hne i hi (h'.trans h.symm))
  · rfl

open LSF in
/-- Every nonparent record identifies a child and its incoming edge. -/
theorem treeIncidenceList_child_fields {T : MGraph} {r current : ℕ}
    (hT : IsRootedTree T r) (mem : ℕ → ℕ) (adj records n k : ℕ) (edge : ℕ → ℕ)
    (ha : adj+n ≤ records)
    (hends : ∀ i < k, T.tail (edge i) < n ∧ T.head (edge i) < n ∧ T.tail (edge i) ≠ T.head (edge i))
    (hin : ∀ i < k, edge i ∈ T.E) :
    let u := T.tail ∘ edge
    let v := T.head ∘ edge
    let out := originalTreeAdjacencyMemory mem adj records u v edge k
    ∀ ptr ∈ treeIncidenceList records u v current k, out ptr ≠ parent T r current →
      out ptr ∈ T.V ∧ out ptr ≠ r ∧ parent T r (out ptr) = current ∧
        parentEdge T r (out ptr) = out (ptr+1) := by
  intro u v out ptr hp hn
  obtain ⟨i,hi,ht | ht⟩ := (mem_treeIncidenceList (fun j hj => (hends j hj).2.2)).mp hp
  all_goals
    have he := hin i hi
    have hv := hT.isForest.1 _ he
    obtain ⟨h0,h1,h3,h4⟩ := originalTreeAdjacencyMemory_fields mem adj records n u v edge ha k
      (fun j hj => ⟨(hends j hj).1,(hends j hj).2.1⟩) i hi
    obtain ⟨ht,rfl⟩ := ht
  · change out (records+6*i) = v i at h0
    change out (records+6*i+1) = edge i at h1
    rw [h0] at hn ⊢
    rw [h1]
    obtain ⟨hp',he',hr⟩ := treeIncidence_child_of_ne_parent hT he (Or.inl ⟨ht,rfl⟩) hn
    exact ⟨hv.2,hr,hp',he'⟩
  · change out (records+6*i+3) = u i at h3
    change out (records+6*i+3+1) = edge i at h4
    rw [h3] at hn ⊢
    rw [h4]
    obtain ⟨hp',he',hr⟩ := treeIncidence_child_of_ne_parent hT he (Or.inr ⟨rfl,ht⟩) hn
    exact ⟨hv.1,hr,hp',he'⟩

open LSF in
/-- The nonparent neighbor list contains precisely the children of a vertex. -/
theorem mem_treeIncidenceList_children {T : MGraph} {r current child : ℕ}
    (hT : IsRootedTree T r) (mem : ℕ → ℕ) (adj records n k : ℕ) (edge : ℕ → ℕ)
    (ha : adj+n ≤ records)
    (hends : ∀ i < k, T.tail (edge i) < n ∧ T.head (edge i) < n ∧ T.tail (edge i) ≠ T.head (edge i))
    (hcover : ∀ e, e ∈ T.E ↔ ∃ i < k, edge i = e) :
    let u := T.tail ∘ edge
    let v := T.head ∘ edge
    let out := originalTreeAdjacencyMemory mem adj records u v edge k
    child ∈ ((treeIncidenceList records u v current k).filter
      (fun ptr => out ptr != parent T r current)).map out ↔
      child ∈ T.V ∧ child ≠ r ∧ parent T r child = current := by
  intro u v out
  constructor
  · intro h
    obtain ⟨ptr,hp,heq⟩ := List.mem_map.mp h
    obtain ⟨hp,hne⟩ := List.mem_filter.mp hp
    have hn : out ptr ≠ parent T r current := by simpa using hne
    obtain ⟨hv,hr,hpar,_⟩ := treeIncidenceList_child_fields (current := current) hT
      mem adj records n k edge ha hends (fun i hi => (hcover _).2 ⟨i,hi,rfl⟩) ptr hp hn
    exact heq ▸ ⟨hv,hr,hpar⟩
  · rintro ⟨hv,hne,hpar⟩
    obtain ⟨ptr,hp,hv',_⟩ := treeIncidenceList_child hT hv hne mem adj records n k edge ha hends
      (fun e he => (hcover e).1 he)
    rw [hpar] at hp
    change out ptr = child at hv'
    have hn := treeChild_ne_parent hT hv hne
    rw [hpar] at hn
    exact List.mem_map.mpr ⟨ptr,List.mem_filter.mpr ⟨hp,by rw [hv']; simpa using hn⟩,hv'⟩

end MinCostFlow.LastLevelProgram
