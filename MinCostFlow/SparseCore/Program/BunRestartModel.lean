module

public import MinCostFlow.SparseCore.Program.BunRestartIface
public import MinCostFlow.SparseCore.Program.BundleInitMain

/-!
# The restart of the bundles: facts about the model (`BunRestartModel`)

The restart cuts the tours of the core vertices into chunks only at the core vertices that carry
an end of a listed slot (the list `rList`), not at all core vertices. This file shows that this
gives the same chunks, and gives the bounds that the cost of the restart needs.

* `initPrefixSlots_restrict`: a vertex without an end in `E` adds no chunk, so the chunks over a
  sorted sublist `r` of the sorted core vertices that keeps every vertex with an end in `E` are the
  chunks over all core vertices.
* `initPrefixSlots_length_le`: there are at most `2 |E|` chunks (each chunk holds an end of `E`).
* `sum_order_length_le`: the tour lists of distinct vertices hold at most `2 m` ends in all.
* `tableAfterInitSlots_bunAgree`: the slot that P5's initialization builds on `rList` agrees with
  `initBundleFor` (`bundleInitSlots_eq_initBundleFor`, P5).
-/

namespace MinCostFlow.SparseCore.Program.Restart

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

public section

private lemma initialChunks_nil (k : ℕ) : initialChunks k ([] : List End) = [] := by
  simp [initialChunks]

/-- A vertex whose tour list has no end of `E` adds no chunk: filtering such vertices out of the
list of vertices keeps the chunks. -/
theorem initPrefixSlots_filter {cord : ℕ → List End} {l : List ℕ} {P : ℕ → Bool}
    {E : Finset ℕ} {k : ℕ} (h : ∀ v ∈ l, P v = false → ∀ x ∈ cord v, x.1 ∉ E) :
    initPrefixSlots cord (l.filter P) E k = initPrefixSlots cord l E k := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    have ih' := ih fun u hu => h u (List.mem_cons_of_mem _ hu)
    unfold initPrefixSlots at ih' ⊢
    by_cases hPv : P v = true
    · rw [List.filter_cons_of_pos hPv, List.flatMap_cons, List.flatMap_cons, ih']
    · have hPv' : P v = false := by simpa using hPv
      have hnil : (cord v).filter (fun x => decide (x.1 ∈ E)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx
        simpa using h v List.mem_cons_self hPv' x hx
      rw [List.filter_cons_of_neg hPv, List.flatMap_cons, hnil, initialChunks_nil, List.map_nil, List.nil_append,
        ih']

/-- **Restricting the vertices.** Let `l` and `r` be strictly increasing, with every vertex of `r`
in `l`, and every vertex of `l` with an end in `E` in `r`. Then the chunks over `r` are the chunks
over `l`. -/
theorem initPrefixSlots_restrict {cord : ℕ → List End} {l r : List ℕ} {E : Finset ℕ} {k : ℕ}
    (hl : l.Pairwise (· < ·)) (hr : r.Pairwise (· < ·)) (hsub : ∀ v ∈ r, v ∈ l)
    (hcov : ∀ v ∈ l, ∀ x ∈ cord v, x.1 ∈ E → v ∈ r) :
    initPrefixSlots cord r E k = initPrefixSlots cord l E k := by
  have hfil : r = l.filter fun v => decide (v ∈ r) := by
    refine List.SortedLT.eq_of_mem_iff (List.sortedLT_iff_pairwise.mpr hr)
      (List.sortedLT_iff_pairwise.mpr (hl.filter _)) fun a => ?_
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun ha => ⟨hsub a ha, ha⟩, fun ha => ha.2⟩
  conv_lhs => rw [hfil]
  refine initPrefixSlots_filter fun v hv hPv x hx hxE => ?_
  have := hcov v hv x hx hxE
  simp [this] at hPv

private lemma ceil_div_le_self {n k : ℕ} (hk : 1 ≤ k) : (n + k - 1) / k ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact le_of_eq (Nat.div_eq_of_lt (by omega))
  · apply Nat.div_le_of_le_mul
    have hkn : k * n = (k - 1) * (n - 1) + (k - 1) + n := by
      obtain ⟨a, rfl⟩ : ∃ a, k = a + 1 := ⟨k - 1, by omega⟩
      obtain ⟨b, rfl⟩ : ∃ b, n = b + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    omega

private lemma sum_map_le {α : Type*} (l : List α) (f g : α → ℕ) (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a List.mem_cons_self) (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- A list without repeats of ends of edges of `E` has at most `2 |E|` entries. -/
theorem length_le_of_nodup_ends {L : List End} {E : Finset ℕ} (hnd : L.Nodup)
    (hE : ∀ x ∈ L, x.1 ∈ E) : L.length ≤ 2 * E.card := by
  rw [← List.toFinset_card_of_nodup hnd, ← card_edgeEnds]
  exact Finset.card_le_card fun x hx => (mem_edgeEnds E x).mpr (hE x (List.mem_toFinset.mp hx))

/-- **There are at most `2 |E|` chunks:** each chunk is nonempty and the chunks hold distinct ends
of `E`. -/
theorem initPrefixSlots_length_le {cord : ℕ → List End} {rList : List ℕ} {E : Finset ℕ}
    {k : ℕ} (hk : 1 ≤ k) (hr_nd : rList.Nodup) (hcord_nd : ∀ w ∈ rList, (cord w).Nodup)
    (hcord_disj : ∀ w₁ w₂ x, x ∈ cord w₁ → x ∈ cord w₂ → w₁ = w₂) :
    (initPrefixSlots cord rList E k).length ≤ 2 * E.card := by
  set f : ℕ → List End := fun v => (cord v).filter fun x => decide (x.1 ∈ E)
  have hlen : (initPrefixSlots cord rList E k).length =
      (rList.map fun v => (initialChunks k (f v)).length).sum := by
    simp only [initPrefixSlots, List.length_flatMap, List.length_map, f]
  have hle : (rList.map fun v => (initialChunks k (f v)).length).sum ≤ (rList.flatMap f).length := by
    rw [List.length_flatMap]
    refine sum_map_le _ _ _ fun v _ => ?_
    rw [initialChunks_length_eq]
    exact ceil_div_le_self hk
  have hnd : (rList.flatMap f).Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun w hw => (hcord_nd w hw).filter _, ?_⟩
    exact hr_nd.imp fun hne =>
      List.disjoint_left.mpr fun x hx1 hx2 =>
        hne (hcord_disj _ _ x (List.mem_filter.mp hx1).1 (List.mem_filter.mp hx2).1)
  have hE : ∀ x ∈ rList.flatMap f, x.1 ∈ E := by
    intro x hx
    obtain ⟨v, -, hxv⟩ := List.mem_flatMap.mp hx
    simpa using (List.mem_filter.mp hxv).2
  rw [hlen]
  exact le_trans hle (length_le_of_nodup_ends hnd hE)

/-- **The tour lists of distinct vertices hold at most `2 m` ends.** -/
theorem sum_order_length_le {C : MGraph} (ρ : Rotation C) {rList : List ℕ} (hnd : rList.Nodup) :
    (rList.map fun v => (ρ.order v).length).sum ≤ 2 * C.m := by
  rw [← List.length_flatMap]
  refine length_le_of_nodup_ends ?_ fun x hx => ?_
  · rw [List.nodup_flatMap]
    refine ⟨fun v _ => ρ.nodup v, hnd.imp fun hne => List.disjoint_left.mpr fun x hx1 hx2 => ?_⟩
    exact hne (((ρ.mem_order _ x).mp hx1).2.symm.trans ((ρ.mem_order _ x).mp hx2).2)
  · obtain ⟨v, -, hxv⟩ := List.mem_flatMap.mp hx
    exact ((ρ.mem_order v x).mp hxv).1

/-- The core graph has at most the edges of the graph. -/
theorem coreGraph_m_le (G : MGraph) (L : LSF) : (coreGraph G L).m ≤ G.m :=
  Finset.card_le_card Finset.sdiff_subset

/-- **The new slot agrees with `initBundleFor`.** Let `cord` be the core rotation of `cs` and
`ord`, and let `rList` be strictly increasing, made of core vertices, and hold every vertex whose
tour list has an end of `E = slotEdgesOf assigns j`. Then P5's initialization on `rList` gives in
slot `j` a bundle state that agrees with `initBundleFor cs ord E k`. -/
theorem tableAfterInitSlots_bunAgree {slotCap : ℕ} {cs : CompLSFState} {ord cord : ℕ → List End}
    {k : ℕ} (hk : 1 ≤ k) (hC : CoreCordOf cs ord cord) {S₀ : BundleTableState slotCap}
    {specs assigns : List (ℕ × ℕ)} {rList : List ℕ} {j : Fin slotCap}
    (hj : j.1 ∈ specs.map Prod.fst) (hE : slotEdgesOf assigns j.1 ⊆ (coreGraph cs.G cs.lsf).E)
    (hr : rList.Pairwise (· < ·)) (hrsub : ∀ v ∈ rList, v ∈ (coreGraph cs.G cs.lsf).V)
    (hcov : ∀ v x, x ∈ cord v → x.1 ∈ slotEdgesOf assigns j.1 → v ∈ rList) :
    ∃ B', tableAfterInitSlots S₀ specs assigns cord rList k j = some B' ∧
      BunAgree B' (initBundleFor cs ord (slotEdgesOf assigns j.1) k) := by
  obtain ⟨C_lsst, ℓ₀, hI, ρG, hρ, hcord⟩ := hC
  obtain ⟨B, hB, hV, hEq, hP, hbo, -⟩ :=
    bundleInitSlots_eq_initBundleFor (S₀ := S₀) hI ord ρG hρ hk hj hE
  set ρ := coreRotation (L := cs.lsf) ρG hI.hG_val (compLSF_RF_isRSF hI)
  have hsame : tableAfterInitSlots S₀ specs assigns cord rList k j =
      tableAfterInitSlots S₀ specs assigns ρ.order
        ((coreGraph cs.G cs.lsf).V.sort (· ≤ ·)) k j := by
    unfold tableAfterInitSlots
    simp only [hj, ↓reduceIte, hcord]
    congr 2
    refine initPrefixSlots_restrict (Finset.sortedLT_sort _).pairwise hr
      (fun v hv => (Finset.mem_sort _).mpr (hrsub v hv)) fun v _ x hx hxE => ?_
    exact hcov v x (hcord ▸ hx) hxE
  refine ⟨B, hsame.trans hB, hV, hEq, hP, fun x hx => hbo x ?_⟩
  rw [hEq] at hx
  have hEq' := (initBundleFor_eq_initBundleState hI ρG hρ (slotEdgesOf assigns j.1) k)
  rw [hEq'] at hx
  exact hx

end

end MinCostFlow.SparseCore.Program.Restart
