module

public import MinCostFlow.SparseCore.Program.BunRestartSort
public import MinCostFlow.SparseCore.Program.BunRestartClear
public import MinCostFlow.SparseCore.Program.BundleInitMain

/-!
# The restart of the bundles: facts on the core and on the lists (`BunRestartCore`)

* `coreCord_facts`: the tour lists `cord` of the core rotation have no repeats, hold the ends of
  core edges at their source, and hold at most `2 m` ends over distinct vertices.
* `edgeTot_le_card`: the listed slots, whose edge sets are disjoint, have at most `|U|` edges in all
  when all their edges lie in `U`.
* `brOwn`: the owner of a key, the source of its end in the core graph (`brOwn_spec`).
* `brPairsOf_eq_allPairs`, `readPairs_eq_of`: the pairs that phase C writes are `allPairs`.
-/

namespace MinCostFlow.SparseCore.Program.Restart

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

@[expose] public section

/-- The owner of the key `k`: the vertex of the core graph of `cs` where its end starts. -/
noncomputable def brOwn (cs : CompLSFState) (k : ℕ) : ℕ := (coreGraph cs.G cs.lsf).src (endOfKey k)

end

public section

variable {cs : CompLSFState} {ord cord : ℕ → List End}

/-- **The tour lists of the core rotation.** They have no repeats, hold an end exactly when its
edge is a core edge and the list is that of its source, hold only ends at core vertices, and hold
at most `2 m` ends over distinct vertices. -/
theorem coreCord_facts (hC : CoreCordOf cs ord cord) :
    (∀ v, (cord v).Nodup) ∧
      (∀ v x, x ∈ cord v ↔ x.1 ∈ (coreGraph cs.G cs.lsf).E ∧ (coreGraph cs.G cs.lsf).src x = v) ∧
      (∀ v x, x ∈ cord v → v ∈ (coreGraph cs.G cs.lsf).V) ∧
      ∀ rList : List ℕ, rList.Nodup → (rList.map fun v => (cord v).length).sum ≤ 2 * cs.G.m := by
  obtain ⟨C_lsst, ℓ₀, hI, ρG, -, hcord⟩ := hC
  set ρ := coreRotation (L := cs.lsf) ρG hI.hG_val (compLSF_RF_isRSF hI)
  subst hcord
  have hval := coreGraph_isValid (L := cs.lsf) hI.hG_val (compLSF_RF_isRSF hI)
  refine ⟨ρ.nodup, ρ.mem_order, fun v x hx => ?_, fun rList hnd => ?_⟩
  · obtain ⟨hxE, hsrc⟩ := (ρ.mem_order v x).mp hx
    obtain ⟨ht, hh⟩ := hval x.1 hxE
    rw [← hsrc]
    unfold MGraph.src
    split_ifs
    · exact ht
    · exact hh
  · exact (sum_order_length_le ρ hnd).trans
      (Nat.mul_le_mul_left 2 (coreGraph_m_le cs.G cs.lsf))

/-- **The owner of a key.** If the edge of the key `k` is a core edge, then its end lies in the
tour list of `brOwn cs k` and in no other. -/
theorem brOwn_spec (hC : CoreCordOf cs ord cord) {k : ℕ}
    (hk : k / 2 ∈ (coreGraph cs.G cs.lsf).E) :
    endOfKey k ∈ cord (brOwn cs k) ∧ ∀ v', endOfKey k ∈ cord v' → v' = brOwn cs k := by
  have hmem := (coreCord_facts hC).2.1
  refine ⟨(hmem _ _).mpr ⟨hk, rfl⟩, fun v' hv' => ?_⟩
  exact ((hmem v' _).mp hv').2.symm

variable {slotCap : ℕ} {S : Fin slotCap → Option BundleState} {slots : List ℕ}

/-- The listed slots have at most `|U|` edges in all when their edge sets are disjoint and lie in
`U`. -/
theorem edgeTot_le_card (hnd : slots.Nodup)
    (hdisj : ∀ s₁ ∈ slots, ∀ s₂ ∈ slots, s₁ ≠ s₂ →
      Disjoint (slotB S s₁).edges (slotB S s₂).edges)
    {U : Finset ℕ} (hsub : ∀ s ∈ slots, (slotB S s).edges ⊆ U) : edgeTot S slots ≤ U.card := by
  classical
  unfold edgeTot
  rw [← List.sum_toFinset _ hnd, ← Finset.card_biUnion]
  · exact Finset.card_le_card (Finset.biUnion_subset.mpr fun s hs =>
      hsub s (List.mem_toFinset.mp hs))
  · intro s₁ hs₁ s₂ hs₂ hne
    exact hdisj s₁ (List.mem_toFinset.mp hs₁) s₂ (List.mem_toFinset.mp hs₂) hne

/-- `bundleReadPairs` reads back a list of pairs stored with stride `2`. -/
theorem readPairs_eq_of {mem : ℕ → ℕ} {a : ℕ} {L : List (ℕ × ℕ)}
    (h : ∀ j < L.length, mem (a + 2 * j) = (L.getD j (0, 0)).1 ∧
      mem (a + 2 * j + 1) = (L.getD j (0, 0)).2) :
    bundleReadPairs mem a L.length = L := by
  apply List.ext_getElem (by simp [bundleReadPairs])
  intro j h1 h2
  obtain ⟨e1, e2⟩ := h j h2
  rw [List.getD_eq_getElem _ _ h2] at e1 e2
  simp only [bundleReadPairs, List.getElem_map, List.getElem_range]
  rw [e1, e2]

/-- `bundleReadPairs` depends only on the memory it reads. -/
theorem readPairs_congr' {mem mem' : ℕ → ℕ} {a n : ℕ}
    (h : ∀ j < n, mem' (a + 2 * j) = mem (a + 2 * j) ∧
      mem' (a + 2 * j + 1) = mem (a + 2 * j + 1)) :
    bundleReadPairs mem' a n = bundleReadPairs mem a n := by
  unfold bundleReadPairs
  refine List.map_congr_left fun j hj => ?_
  obtain ⟨e1, e2⟩ := h j (List.mem_range.mp hj)
  rw [e1, e2]

variable {vCap eCap tbl : ℕ} {m : BundleTableMeta slotCap} {mem : ℕ → ℕ}

/-- **The pairs of phase C.** If the memory `M` agrees with `mem` on the edge slots, the pairs
`brPairsOf` of the keys of the listed slots are `allPairs`. -/
theorem brPairsOf_eq_allPairs (hrep : BundleTableRepAt slotCap vCap eCap tbl S m mem)
    (hact : ∀ s ∈ slots, ∃ hs : s < slotCap, ∃ B, S ⟨s, hs⟩ = some B)
    (heC : ∀ s ∈ slots, ∀ e ∈ (slotB S s).edges, e < eCap) {M : ℕ → ℕ}
    (hM : ∀ e < eCap, M (btEdgeSlotBase tbl slotCap + e) = mem (btEdgeSlotBase tbl slotCap + e)) :
    brPairsOf tbl slotCap M (allKeys eCap tbl S m mem slots) =
      allPairs eCap tbl S m mem slots := by
  rw [← progPairs_eq hrep hact heC]
  unfold brPairsOf
  refine List.map_congr_left fun k hk => ?_
  have hk2 := allKeys_lt hrep hact (List.mem_filter.mp hk).1
  rw [hM _ (by omega)]

end

end MinCostFlow.SparseCore.Program.Restart
