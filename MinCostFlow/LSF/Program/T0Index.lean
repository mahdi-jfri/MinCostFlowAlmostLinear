module

public import MinCostFlow.LSF.Program.T0Edges
public import MinCostFlow.LSF.Program.RootTreeBase
public import MinCostFlow.LSF.TreeOps
import Mathlib.Tactic.Linarith

/-!
# `T₀` as index arrays

The rooting procedure works on vertices `0, …, n - 1` and edges `0, …, tM - 1`. Here we connect
it with the tree `T₀`, whose vertices are the entries of `vList` and whose edges have the IDs
`fid 0, …, fid (tM - 1)`. `T0IndexArrays` says that edge `i` of the arrays is edge `fid i` of
`T₀` and joins the vertices with indices `tl i` and `hd i`.

* `rtReach_of_spanning`: if `T₀` is a spanning tree, every index is reachable from every other
  one along the arrays, which is what the rooting procedure needs.
* `t0IndexArrays_of_lift`: the arrays written by `t0EdgesProc` satisfy `T0IndexArrays`, given
  what `lsst_decode_lift` says about the output of the `[AN19]` call and what the copy arrays
  hold (`CopyArraysAt`).
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF

@[expose] public section

/-- Edge `i < tM` of the arrays is edge `fid i` of `T₀`, from the vertex with index `tl i` to
the vertex with index `hd i`; every edge of `T₀` is listed exactly once. -/
structure T0IndexArrays (T₀ : MGraph) (vList : List ℕ) (tM : ℕ) (fid tl hd : ℕ → ℕ) :
    Prop where
  fid_mem : ∀ i < tM, fid i ∈ T₀.E
  fid_cover : ∀ f ∈ T₀.E, ∃ i < tM, fid i = f
  fid_inj : ∀ i < tM, ∀ j < tM, fid i = fid j → i = j
  tl_lt : ∀ i < tM, tl i < vList.length
  hd_lt : ∀ i < tM, hd i < vList.length
  tail_eq : ∀ i < tM, T₀.tail (fid i) = vList.getD (tl i) 0
  head_eq : ∀ i < tM, T₀.head (fid i) = vList.getD (hd i) 0

private lemma idx_eq_of_getD {vList : List ℕ} (hnd : vList.Nodup) {a b : ℕ}
    (ha : a < vList.length) (hb : b < vList.length) (h : vList.getD a 0 = vList.getD b 0) :
    a = b := by
  rw [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hb] at h
  exact (hnd.getElem_inj_iff).mp h

/-- A walk of `T₀` gives a chain of adjacent indices. -/
lemma rtReach_of_walk {T₀ : MGraph} {vList : List ℕ} {tM : ℕ} {fid tl hd : ℕ → ℕ}
    (hA : T0IndexArrays T₀ vList tM fid tl hd) (hnd : vList.Nodup) {u v : ℕ}
    {P : List (ℕ × Bool)} (hP : T₀.IsWalk u v P) :
    ∀ a < vList.length, ∀ x < vList.length, vList.getD a 0 = u → vList.getD x 0 = v →
      Relation.ReflTransGen (rtAdj tM tl hd) a x := by
  induction hP with
  | nil u =>
    intro a ha x hx hau hxu
    rw [idx_eq_of_getD hnd ha hx (hau.trans hxu.symm)]
  | @cons u v y P hy hsrc _ ih =>
    intro a ha x hx hau hxv
    obtain ⟨i, hi, hfi⟩ := hA.fid_cover _ hy
    have htl := hA.tl_lt i hi
    have hhd := hA.hd_lt i hi
    by_cases hdir : y.2 = true
    · have hsrc' : T₀.tail (fid i) = u := by rw [hfi]; simpa [MGraph.src, hdir] using hsrc
      have hdst : T₀.dst y = T₀.head (fid i) := by rw [hfi]; simp [MGraph.dst, hdir]
      have hai : a = tl i :=
        idx_eq_of_getD hnd ha htl (by rw [hau, ← hsrc', hA.tail_eq i hi])
      subst hai
      refine Relation.ReflTransGen.head ⟨i, hi, Or.inl ⟨rfl, rfl⟩⟩ ?_
      exact ih (hd i) hhd x hx (by rw [hdst, hA.head_eq i hi]) hxv
    · have hsrc' : T₀.head (fid i) = u := by rw [hfi]; simpa [MGraph.src, hdir] using hsrc
      have hdst : T₀.dst y = T₀.tail (fid i) := by rw [hfi]; simp [MGraph.dst, hdir]
      have hai : a = hd i :=
        idx_eq_of_getD hnd ha hhd (by rw [hau, ← hsrc', hA.head_eq i hi])
      subst hai
      refine Relation.ReflTransGen.head ⟨i, hi, Or.inr ⟨rfl, rfl⟩⟩ ?_
      exact ih (tl i) htl x hx (by rw [hdst, hA.tail_eq i hi]) hxv

/-- In a spanning tree every index is reachable from every other one. -/
lemma rtReach_of_spanning {T₀ : MGraph} {vList : List ℕ} {tM : ℕ} {fid tl hd : ℕ → ℕ}
    (hA : T0IndexArrays T₀ vList tM fid tl hd) (hnd : vList.Nodup)
    (hST : ∀ u ∈ T₀.V, ∀ v ∈ T₀.V, T₀.Connected u v)
    (hV : ∀ u, u ∈ vList ↔ u ∈ T₀.V) {a : ℕ} (ha : a < vList.length) :
    ∀ x < vList.length, Relation.ReflTransGen (rtAdj tM tl hd) a x := by
  intro x hx
  have hmem : ∀ b < vList.length, vList.getD b 0 ∈ T₀.V := fun b hb => by
    rw [List.getD_eq_getElem _ _ hb, ← hV]; exact List.getElem_mem hb
  obtain ⟨P, hP⟩ := hST _ (hmem a ha) _ (hmem x hx)
  exact rtReach_of_walk hA hnd hP a ha x hx rfl rfl

/-- What the copy arrays hold for each copy `q` of an edge of `G₀`: its edge, and the indices of
its ends. `cl` is the list of copies (`copyList`). -/
def CopyArraysAt (mem : ℕ → ℕ) (copyTailPtr copyHeadPtr copyOrigIdxPtr : ℕ) (G₀ : MGraph)
    (vList : List ℕ) (cl : List (ℕ × ℕ)) : Prop :=
  ∀ q < cl.length,
    mem (copyOrigIdxPtr + q) = (cl.getD q (0, 0)).1 ∧
    mem (copyTailPtr + q) < vList.length ∧
    vList.getD (mem (copyTailPtr + q)) 0 = G₀.tail (cl.getD q (0, 0)).1 ∧
    mem (copyHeadPtr + q) < vList.length ∧
    vList.getD (mem (copyHeadPtr + q)) 0 = G₀.head (cl.getD q (0, 0)).1

private lemma getElem_flatMap_pair (L : List (ℕ × ℕ)) :
    ∀ k (hk : k < L.length),
      (L.flatMap fun p => [p.1, p.2]).getD (2 * k) 0 = L[k].1 ∧
      (L.flatMap fun p => [p.1, p.2]).getD (2 * k + 1) 0 = L[k].2 := by
  induction L with
  | nil => intro k hk; simp at hk
  | cons p L ih =>
    intro k hk
    rcases k with _ | k
    · simp
    · have h := ih k (by simpa using hk)
      simp only [List.flatMap_cons, List.getElem_cons_succ]
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, show 2 * k + 2 + 1 = 2 * k + 1 + 2 by ring]
      simpa using h

private lemma length_flatMap_pair (L : List (ℕ × ℕ)) :
    (L.flatMap fun p => [p.1, p.2]).length = 2 * L.length := by
  induction L with
  | nil => simp
  | cons p L ih => simp [List.flatMap_cons, ih]; ring

/-- The arrays written by `t0EdgesProc` describe `T₀`. The hypotheses are the facts of
`lsst_decode_lift` about the output lists `origEdges` and `bridgePairs` and about `T₀`. -/
theorem t0IndexArrays_of_lift {G₀ T₀ : MGraph} {vList : List ℕ} {cl : List (ℕ × ℕ)}
    {origEdges : List ℕ} {bridgePairs : List (ℕ × ℕ)} {zeros : List ℕ} {eCap : ℕ}
    {mem mem' : ℕ → ℕ}
    {outOrigPtr outBridgePtr copyTailPtr copyHeadPtr copyOrigIdxPtr usedBridgePtr ubLen
      tOrigPtr tTailPtr tHeadPtr : ℕ}
    (hzeros : zeros = zeroPositions mem usedBridgePtr ubLen)
    (hvLen : vList.length = G₀.n)
    (heCap : ∀ e ∈ G₀.E, e < eCap)
    (hcopy : CopyArraysAt mem copyTailPtr copyHeadPtr copyOrigIdxPtr G₀ vList cl)
    (horigAt : ListAt mem outOrigPtr origEdges)
    (hbrAt : ListAt mem outBridgePtr (bridgePairs.flatMap fun p => [p.1, p.2]))
    (hoLt : ∀ q ∈ origEdges, q < cl.length)
    (hoInj : ∀ i₁ (hi₁ : i₁ < origEdges.length) i₂ (hi₂ : i₂ < origEdges.length),
      (cl.getD (origEdges[i₁]'hi₁) (0, 0)).1 = (cl.getD (origEdges[i₂]'hi₂) (0, 0)).1 →
        i₁ = i₂)
    (hoE : ∀ q ∈ origEdges, (cl.getD q (0, 0)).1 ∈ G₀.E)
    (hbLt : ∀ p ∈ bridgePairs, p.1 < G₀.n ∧ p.2 < G₀.n)
    (hbZ : bridgePairs.length ≤ zeros.length)
    (hTE : T₀.E = ((origEdges.map fun q => (cl.getD q (0, 0)).1) ++
      ((zeros.take bridgePairs.length).map fun z => eCap + z)).toFinset)
    (hTo : ∀ i (hi : i < origEdges.length),
      T₀.tail (cl.getD (origEdges[i]'hi) (0, 0)).1 = G₀.tail (cl.getD (origEdges[i]'hi) (0, 0)).1 ∧
      T₀.head (cl.getD (origEdges[i]'hi) (0, 0)).1 = G₀.head (cl.getD (origEdges[i]'hi) (0, 0)).1)
    (hTb : ∀ k (hk : k < bridgePairs.length),
      T₀.tail (eCap + zeros.getD k 0) = vList.getD (bridgePairs.getD k (0, 0)).1 0 ∧
      T₀.head (eCap + zeros.getD k 0) = vList.getD (bridgePairs.getD k (0, 0)).2 0)
    (hpost : (∀ i < origEdges.length,
      mem' (tOrigPtr + i) = mem (copyOrigIdxPtr + mem (outOrigPtr + i)) ∧
      mem' (tTailPtr + i) = mem (copyTailPtr + mem (outOrigPtr + i)) ∧
      mem' (tHeadPtr + i) = mem (copyHeadPtr + mem (outOrigPtr + i))) ∧
    (∀ k < bridgePairs.length,
      mem' (tOrigPtr + (origEdges.length + k)) =
        eCap + (zeroPositions mem usedBridgePtr ubLen).getD k 0 ∧
      mem' (tTailPtr + (origEdges.length + k)) = mem (outBridgePtr + 2 * k) ∧
      mem' (tHeadPtr + (origEdges.length + k)) = mem (outBridgePtr + 2 * k + 1))) :
    T0IndexArrays T₀ vList (origEdges.length + bridgePairs.length)
      (fun i => mem' (tOrigPtr + i)) (fun i => mem' (tTailPtr + i))
      (fun i => mem' (tHeadPtr + i)) := by
  subst hzeros
  obtain ⟨hpo, hpb⟩ := hpost
  set nO := origEdges.length
  set zeros := zeroPositions mem usedBridgePtr ubLen
  -- the ID list
  set L := (origEdges.map fun q => (cl.getD q (0, 0)).1) ++
      ((zeros.take bridgePairs.length).map fun z => eCap + z) with hL
  have hLlen : L.length = nO + bridgePairs.length := by
    simp [hL, nO, List.length_take, min_eq_left hbZ]
  have hfidL : ∀ i < nO + bridgePairs.length, mem' (tOrigPtr + i) = L.getD i 0 := by
    intro i hi
    by_cases hio : i < nO
    · rw [(hpo i hio).1, horigAt i hio, (hcopy _ (hoLt _ (List.getElem_mem _))).1,
        List.getD_eq_getElem L _ (by rw [hLlen]; omega)]
      simp only [hL]
      rw [List.getElem_append_left (by simpa using hio)]
      simp
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hio)
      have hkb : k < bridgePairs.length := by omega
      have hkz : k < zeros.length := by omega
      rw [(hpb k hkb).1, List.getD_eq_getElem L _ (by rw [hLlen]; omega)]
      simp only [hL]
      rw [List.getElem_append_right (by simp [nO])]
      simp [nO, List.getElem?_eq_getElem hkz]
  -- the ID list has no repeats
  have hLnd : L.Nodup := by
    rw [hL, List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.nodup_iff_injective_get]
      intro a b hab
      simp only [List.get_eq_getElem, List.getElem_map] at hab
      exact Fin.ext (by simpa using hoInj a (by simpa using a.2) b (by simpa using b.2) hab)
    · exact ((zeroPositions_nodup _ _ _).sublist (List.take_sublist _ _)).map
        (fun a b h => by simpa using h)
    · intro a ha b hb hab
      simp only [List.mem_map] at ha hb
      obtain ⟨q, hq, rfl⟩ := ha
      obtain ⟨z, -, rfl⟩ := hb
      have := heCap _ (hoE q hq)
      omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hfidL i hi, hTE, List.mem_toFinset, List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  · intro f hf
    rw [hTE, List.mem_toFinset] at hf
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hf
    exact ⟨i, by omega, by rw [hfidL i (by omega), List.getD_eq_getElem _ _ hi]⟩
  · intro i hi j hj h
    rw [hfidL i hi, hfidL j hj, List.getD_eq_getElem _ _ (by omega),
      List.getD_eq_getElem _ _ (by omega)] at h
    exact (hLnd.getElem_inj_iff).mp h
  · intro i hi
    by_cases hio : i < nO
    · rw [(hpo i hio).2.1, horigAt i hio]
      exact (hcopy _ (hoLt _ (List.getElem_mem _))).2.1
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hio)
      have hk : k < bridgePairs.length := by omega
      rw [(hpb k hk).2.1, hbrAt (2 * k) (by rw [length_flatMap_pair]; omega),
        ← List.getD_eq_getElem _ 0, (getElem_flatMap_pair bridgePairs k hk).1, hvLen]
      exact (hbLt _ (List.getElem_mem hk)).1
  · intro i hi
    by_cases hio : i < nO
    · rw [(hpo i hio).2.2, horigAt i hio]
      exact (hcopy _ (hoLt _ (List.getElem_mem _))).2.2.2.1
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hio)
      have hk : k < bridgePairs.length := by omega
      rw [(hpb k hk).2.2, show outBridgePtr + 2 * k + 1 = outBridgePtr + (2 * k + 1) by ring,
        hbrAt (2 * k + 1) (by rw [length_flatMap_pair]; omega),
        ← List.getD_eq_getElem _ 0, (getElem_flatMap_pair bridgePairs k hk).2, hvLen]
      exact (hbLt _ (List.getElem_mem hk)).2
  · intro i hi
    by_cases hio : i < nO
    · rw [(hpo i hio).1, (hpo i hio).2.1, horigAt i hio,
        (hcopy _ (hoLt _ (List.getElem_mem _))).1, (hcopy _ (hoLt _ (List.getElem_mem _))).2.2.1]
      exact (hTo i hio).1
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hio)
      have hk : k < bridgePairs.length := by omega
      rw [(hpb k hk).1, (hpb k hk).2.1, hbrAt (2 * k) (by rw [length_flatMap_pair]; omega),
        ← List.getD_eq_getElem _ 0, (getElem_flatMap_pair bridgePairs k hk).1, (hTb k hk).1,
        List.getD_eq_getElem _ _ hk]
  · intro i hi
    by_cases hio : i < nO
    · rw [(hpo i hio).1, (hpo i hio).2.2, horigAt i hio,
        (hcopy _ (hoLt _ (List.getElem_mem _))).1,
        (hcopy _ (hoLt _ (List.getElem_mem _))).2.2.2.2]
      exact (hTo i hio).2
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hio)
      have hk : k < bridgePairs.length := by omega
      rw [(hpb k hk).1, (hpb k hk).2.2,
        show outBridgePtr + 2 * k + 1 = outBridgePtr + (2 * k + 1) by ring,
        hbrAt (2 * k + 1) (by rw [length_flatMap_pair]; omega),
        ← List.getD_eq_getElem _ 0, (getElem_flatMap_pair bridgePairs k hk).2, (hTb k hk).2,
        List.getD_eq_getElem _ _ hk]

end

end MinCostFlow.LSF.Program
