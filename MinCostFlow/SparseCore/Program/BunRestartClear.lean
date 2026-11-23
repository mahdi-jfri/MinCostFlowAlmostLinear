module

public import MinCostFlow.SparseCore.Program.BunRestartIface
public import MinCostFlow.SparseCore.Program.BunRestartKeys

/-!
# The restart of the bundles: the cleared table (`BunRestartClear`)

After phase D, the listed slots are empty in memory: their slot pointers and the edge slots of
their edges are `0`. `clear_rep` shows that the memory then represents the table `clearS S slots`,
where the listed slots are empty, with the blocks `clearM m slots`. P5's initialization of slots
starts from this table.

`bunSlotNB_restart` is the bookkeeping of the potential: if two tables agree outside the listed
slots, their bundle counts differ only by those of the listed slots.
-/

namespace MinCostFlow.SparseCore.Program.Restart

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

@[expose] public section

/-- The table `S` with the listed slots emptied. -/
def clearS {slotCap : ℕ} (S : Fin slotCap → Option BundleState) (slots : List ℕ) :
    Fin slotCap → Option BundleState :=
  fun j => if j.1 ∈ slots then none else S j

/-- The blocks `m` with those of the listed slots removed. -/
def clearM {slotCap : ℕ} (m : BundleTableMeta slotCap) (slots : List ℕ) :
    BundleTableMeta slotCap :=
  ⟨fun j => if j.1 ∈ slots then none else m.slotBlocks j⟩

/-- The bundle count of slot `s` (`0` if `s` is not a slot or the slot is inactive). -/
def slotNB {slotCap : ℕ} (S : Fin slotCap → Option BundleState) (s : ℕ) : ℕ :=
  if hs : s < slotCap then bunSlotNB S ⟨s, hs⟩ else 0

end

public section

variable {slotCap vCap eCap tbl : ℕ} {S : Fin slotCap → Option BundleState}
  {m : BundleTableMeta slotCap} {slots : List ℕ} {mem : ℕ → ℕ}

theorem clearS_some {j : Fin slotCap} {B : BundleState} (h : clearS S slots j = some B) :
    j.1 ∉ slots ∧ S j = some B := by
  unfold clearS at h
  by_cases hj : j.1 ∈ slots
  · simp [hj] at h
  · simp only [hj, ite_false] at h
    exact ⟨hj, h⟩

theorem clearM_foot {a : ℕ} (h : bundleTableFoot eCap tbl (clearM m slots) a) :
    bundleTableFoot eCap tbl m a := by
  rcases h with h | ⟨j, p, c, hm, h1, h2⟩
  · exact Or.inl h
  · refine Or.inr ⟨j, p, c, ?_, h1, h2⟩
    unfold clearM at hm
    by_cases hj : j.1 ∈ slots
    · simp [hj] at hm
    · simpa [hj] using hm

/-- **The cleared table.** Let `mem` represent `S` with blocks `m`, and let `mem'` agree with `mem`
on the footprint of the table outside the slot pointers and the edge slots. Let `mem'` hold `0`
in the slot pointers of the listed slots and in the edge slots of their edges, and agree with
`mem` in the other slot pointers and edge slots. Then `mem'` represents `clearS S slots` with
blocks `clearM m slots`. -/
theorem clear_rep (hrep : BundleTableRepAt slotCap vCap eCap tbl S m mem) {mem' : ℕ → ℕ}
    (hfr : ∀ a, bundleTableFoot eCap tbl m a →
      ¬ (btSlotPtrBase tbl ≤ a ∧ a < btEdgeSlotBase tbl slotCap + eCap) → mem' a = mem a)
    (hptr : ∀ s < slotCap, s ∉ slots → mem' (btSlotPtrBase tbl + s) = mem (btSlotPtrBase tbl + s))
    (hptr0 : ∀ s ∈ slots, mem' (btSlotPtrBase tbl + s) = 0)
    (hes : ∀ e < eCap, (∀ s ∈ slots, e ∉ (slotB S s).edges) →
      mem' (btEdgeSlotBase tbl slotCap + e) = mem (btEdgeSlotBase tbl slotCap + e))
    (hes0 : ∀ s ∈ slots, ∀ e ∈ (slotB S s).edges, mem' (btEdgeSlotBase tbl slotCap + e) = 0) :
    BundleTableRepAt slotCap vCap eCap tbl (clearS S slots) (clearM m slots) mem' := by
  rcases hrep with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    hdisjE, hedgeSlot, hendBun, hslots, hdisjB, hscrS, hscrE, hcur0⟩
  have hhdr : ∀ off < btHdrSize, mem' (tbl + off) = mem (tbl + off) := fun off hoff =>
    hfr _ (btHeader_in_foot hoff) (by unfold btHdrSize at hoff; unfold btSlotPtrBase; omega)
  have hhi : ∀ a, bundleTableFoot eCap tbl m a → btEdgeSlotBase tbl slotCap + eCap ≤ a →
      mem' a = mem a := fun a ha hle => hfr a ha (by omega)
  -- An edge of an unlisted active slot is in no listed slot.
  have hnot : ∀ (j : Fin slotCap) (B : BundleState), j.1 ∉ slots → S j = some B →
      ∀ e ∈ B.edges, ∀ s ∈ slots, e ∉ (slotB S s).edges := by
    intro j B hj hSj e he s hs hes'
    unfold slotB at hes'
    by_cases hsc : s < slotCap
    · simp only [hsc, ↓reduceDIte] at hes'
      rcases hS2 : S ⟨s, hsc⟩ with _ | B₂
      · rw [hS2] at hes'; simp [emptyBun] at hes'
      · rw [hS2] at hes'
        have hne : j ≠ ⟨s, hsc⟩ := fun h' => hj (h' ▸ hs)
        exact Finset.disjoint_left.mp (hdisjE j ⟨s, hsc⟩ hne B B₂ hSj hS2) he hes'
    · simp [hsc, emptyBun] at hes'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hhdr btOffSlotCap (by decide)]; exact h0
  · rw [hhdr btOffVCap (by decide)]; exact h1
  · rw [hhdr btOffECap (by decide)]; exact h2
  · rw [hhdr btOffSlotPtr (by decide)]; exact h3
  · rw [hhdr btOffEdgeSlot (by decide)]; exact h4
  · rw [hhdr btOffEndBundle (by decide)]; exact h5
  · rw [hhdr btOffEndPrev (by decide)]; exact h6
  · rw [hhdr btOffEndNext (by decide)]; exact h7
  · rw [hhdr btOffSlotTouched (by decide)]; exact h8
  · rw [hhdr btOffSlotDelHead (by decide)]; exact h9
  · rw [hhdr btOffSlotDelNext (by decide)]; exact h10
  · rw [hhdr btOffSlotCandHead (by decide)]; exact h11
  · intro j₁ j₂ hne B₁ B₂ hB₁ hB₂
    exact hdisjE j₁ j₂ hne B₁ B₂ (clearS_some hB₁).2 (clearS_some hB₂).2
  · intro e he
    refine ⟨fun j B hj heB => ?_, fun hnone => ?_⟩
    · obtain ⟨hjn, hSj⟩ := clearS_some hj
      rw [hes e he (hnot j B hjn hSj e heB)]
      exact (hedgeSlot e he).1 j B hSj heB
    · by_cases hZ : ∃ s ∈ slots, e ∈ (slotB S s).edges
      · obtain ⟨s, hs, hes'⟩ := hZ
        exact hes0 s hs e hes'
      · simp only [not_exists, not_and] at hZ
        rw [hes e he hZ]
        refine (hedgeSlot e he).2 fun j B hSj heB => ?_
        by_cases hj : j.1 ∈ slots
        · have hB : slotB S j.1 = B := slotB_eq j.2 hSj
          exact hZ j.1 hj (hB ▸ heB)
        · exact hnone j B (by simp [clearS, hj, hSj]) heB
  · intro j B hj x hx
    obtain ⟨-, hSj⟩ := clearS_some hj
    have heB : x.1 ∈ B.edges := (mem_edgeEnds _ _).mp hx
    have hlt : endKey x < 2 * eCap := by
      have hslot := hslots j
      rw [hSj] at hslot
      cases hm : m.slotBlocks j with
      | none => rw [hm] at hslot; exact False.elim hslot
      | some pb =>
        rw [hm] at hslot
        have he_lt := hslot.2.1.choose_spec.2.2.1 x.1 heB
        rcases x with ⟨e, side⟩
        cases side <;> simp [endKey] <;> omega
    rw [hhi _ (btEndBundle_in_foot hlt) (by unfold btEndBundleBase btEdgeSlotBase; omega)]
    exact hendBun j B hSj x hx
  · intro j
    by_cases hj : j.1 ∈ slots
    · simp only [clearS, clearM, hj, ite_true]
      exact hptr0 j.1 hj
    · simp only [clearS, clearM, hj, ite_false]
      have hslot := hslots j
      cases hS : S j with
      | none =>
        rw [hS] at hslot
        cases hm : m.slotBlocks j with
        | none =>
          rw [hm] at hslot
          rw [hptr j.1 j.2 hj]; exact hslot
        | some pb => rw [hm] at hslot; exact False.elim hslot
      | some B =>
        rw [hS] at hslot
        cases hm : m.slotBlocks j with
        | none => rw [hm] at hslot; exact False.elim hslot
        | some pb =>
          rcases pb with ⟨p, bunCap⟩
          rw [hm] at hslot
          refine ⟨(hptr j.1 j.2 hj).trans hslot.1, ?_, hslot.2.2⟩
          have hdis := hslot.2.2
          refine hslot.2.1.of_agree (fun a ha1 ha2 => (hfr a
            (Or.inr ⟨j, p, bunCap, hm, ha1, ha2⟩) (by
              unfold btSlotPtrBase btEdgeSlotBase
              unfold bundleTableFixedSize at hdis
              omega)).symm)
            (fun k hk => (hhi _ (btEndPrev_in_foot hk)
              (by unfold btEndPrevBase btEdgeSlotBase; omega)).symm)
            (fun k hk => (hhi _ (btEndNext_in_foot hk)
              (by unfold btEndNextBase btEdgeSlotBase; omega)).symm)
  · intro j₁ j₂ hne p₁ c₁ p₂ c₂ hm₁ hm₂
    unfold clearM at hm₁ hm₂
    by_cases hj₁ : j₁.1 ∈ slots
    · simp [hj₁] at hm₁
    · by_cases hj₂ : j₂.1 ∈ slots
      · simp [hj₂] at hm₂
      · simp only [hj₁, hj₂, ite_false] at hm₁ hm₂
        exact hdisjB j₁ j₂ hne p₁ c₁ p₂ c₂ hm₁ hm₂
  · intro s hs
    obtain ⟨s1, s2, s3⟩ := hscrS s hs
    refine ⟨?_, ?_, ?_⟩
    · rw [hhi _ (btSlotTouched_in_foot hs) (by unfold btSlotTouchedBase btEdgeSlotBase; omega)]
      exact s1
    · rw [hhi _ (btSlotDelHead_in_foot hs) (by unfold btSlotDelHeadBase btEdgeSlotBase; omega)]
      exact s2
    · rw [hhi _ (btSlotCandHead_in_foot hs)
        (by unfold btSlotCandHeadBase btEdgeSlotBase; omega)]
      exact s3
  · intro e he
    rw [hhi _ (btSlotDelNext_in_foot he) (by unfold btSlotDelNextBase btEdgeSlotBase; omega)]
    exact hscrE e he
  · intro s hs
    exact ⟨(hhi _ (btCurBun_in_foot hs) (by unfold btCurBunBase btEdgeSlotBase; omega)).trans (hcur0 s hs).1,
      (hhi _ (btCurTag_in_foot hs) (by unfold btCurTagBase btEdgeSlotBase; omega)).trans (hcur0 s hs).2⟩

/-! ## The bundle counts -/

theorem sum_listed (hnd : slots.Nodup) (hlt : ∀ s ∈ slots, s < slotCap) (f : ℕ → ℕ) :
    ∑ j : Fin slotCap, (if j.1 ∈ slots then f j.1 else 0) = (slots.map f).sum := by
  rw [Fin.sum_univ_eq_sum_range (fun x => if x ∈ slots then f x else 0), ← Finset.sum_filter,
    ← List.sum_toFinset f hnd]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_range, List.mem_toFinset]
  exact ⟨fun h => h.2, fun h => ⟨hlt x h, h⟩⟩

/-- **Bookkeeping of the bundle counts.** If `T` agrees with `S` outside the listed slots, then
the bundle counts of `T` plus those of the listed slots of `S` equal the bundle counts of `S` plus
those of the listed slots of `T`. -/
theorem bunSlotNB_restart (hnd : slots.Nodup) (hlt : ∀ s ∈ slots, s < slotCap)
    {T : Fin slotCap → Option BundleState} (hag : ∀ j : Fin slotCap, j.1 ∉ slots → T j = S j) :
    ∑ j, bunSlotNB T j + (slots.map (slotNB S)).sum =
      ∑ j, bunSlotNB S j + (slots.map (slotNB T)).sum := by
  have hsplit : ∀ U : Fin slotCap → Option BundleState, ∑ j, bunSlotNB U j =
      ∑ j : Fin slotCap, (if j.1 ∈ slots then slotNB U j.1 else 0) +
        ∑ j : Fin slotCap, (if j.1 ∈ slots then 0 else bunSlotNB U j) := by
    intro U
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j.1 ∈ slots
    · simp [hj, slotNB, j.2]
    · simp [hj]
  have hout : ∑ j : Fin slotCap, (if j.1 ∈ slots then 0 else bunSlotNB T j) =
      ∑ j : Fin slotCap, (if j.1 ∈ slots then 0 else bunSlotNB S j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j.1 ∈ slots
    · simp [hj]
    · simp only [hj, ite_false]
      unfold bunSlotNB
      rw [hag j hj]
  rw [hsplit T, hsplit S, sum_listed hnd hlt, sum_listed hnd hlt, hout]
  omega

/-- The bundle count of an active slot is its number of bundle vertices. -/
theorem slotNB_eq_slotB {s : ℕ} (hs : s < slotCap) {B : BundleState} (hB : S ⟨s, hs⟩ = some B) :
    slotNB S s = (slotB S s).vertices.card := by
  simp [slotNB, hs, bunSlotNB, hB, slotB_eq hs hB]

end

end MinCostFlow.SparseCore.Program.Restart
