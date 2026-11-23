module

public import MinCostFlow.MinRatio.WireChainCoreBranchBExitOutKFBL

/-!
# The zone form of `BranchBDoneSlots.refresh` (`WireChainCoreBranchBExitLayZone`)

When an exit of the Branch B loop rebuilds the levels from `fr` on in `[hi, cur)` and then
refreshes the stretch descriptor of level `fr - 1` at `cur + 5` (advancing the heap pointer to
`cur + 7`), the select data of all finished levels `i < fr` stays in the two-interval zone
`BranchBSelZone lo hi cur (cur + 7) = [lo, hi) ∪ [cur, cur + 7)` off all core footprints:
* for `i < j = fr - 1`, all lists, batch, and descriptor stay in `[lo, hi)` off all cores;
* for `i = j = fr - 1`, the lists and batch stay in `[lo, hi)` off all cores, and the refreshed
  descriptor lies at `[cur + 5, cur + 7) ⊆ [cur, cur + 7)` off all cores.

* `BranchBDoneSlots.refreshZone`: the zone form of `BranchBDoneSlots.refresh`, taking the same
  hypotheses.
* `branchBExitZone_frame`: moves the zone form across a step that keeps all core footprints, all
  slots, and `[lo, hX)` (such as `collectTermForestStmt` writing to `newPtrs + d < lo`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain DynSpanner.Program SparseCore.Program Bundle

/-- The zone form of `BranchBDoneSlots.refresh`: under the same hypotheses, every finished level
`i < j + 1` has its select data (lists, batch, descriptor) in `BranchBSelZone lo hi cur (cur + 7)`
off all new core footprints, and its stretch table rows in `foot' i` or `[lo, cur + 7)`. -/
theorem BranchBDoneSlots.refreshZone {w P d lo hi cur selBase j Lw : ℕ} {Lmax : ℕ → ℕ}
    {foot foot' : ℕ → ℕ → Prop} {mem mem' : ℕ → ℕ} {D : ℕ → LevelDiffLists} {G : ℕ → MGraph}
    {U : ℕ → List Update} {E : ℕ → Finset ℕ} {vals : ℕ → ℕ → ℝ}
    (hDone : BranchBDoneSlots w P d Lmax foot lo hi selBase mem j D G U E vals)
    (hLists : SelOutLevelListsAt w (fun x => ∀ r < d, ¬ foot r x) lo hi mem
      (selBase + 1 + 12 * j) (D j) (G j) (U j))
    (hj : j < d) (hlohi : lo ≤ hi) (hhi : hi ≤ cur)
    (hFootSame : ∀ r < j, ∀ x, foot' r x ↔ foot r x)
    (hFootOther : ∀ r < d, r ≠ j → ∀ x, foot' r x → foot r x ∨ (hi ≤ x ∧ x < cur))
    (hFootNew : ∀ x, foot' j x → foot j x ∨ (hi ≤ x ∧ x < cur + 5))
    (hFootLt : ∀ r < d, ∀ x, foot r x → x < hi)
    (hDisj : ∀ r < d, r ≠ j → ∀ x, foot r x → ¬ foot j x)
    (hSlotLo : selBase + 1 + 12 * d ≤ lo)
    (hSlotOff : ∀ r < d, ∀ i < 12 * d, ¬ foot r (selBase + 1 + i))
    (hKeep : ∀ x < hi, ¬ foot j x → x ≠ selBase + 1 + 12 * j + 8 →
      x ≠ selBase + 1 + 12 * j + 9 →
      (lo ≤ x ∨ (∃ r < j, foot r x) ∨ (selBase + 1 ≤ x ∧ x < selBase + 1 + 12 * d)) →
      mem' x = mem x)
    (h8 : mem' (selBase + 1 + 12 * j + 8) = cur + 5)
    (h9 : mem' (selBase + 1 + 12 * j + 9) = Lw) (hLw : Lw ≤ Lmax j)
    (hSV : StretchValuesAt mem' (cur + 5) 4 Lw P (E j) (vals j))
    (hT0 : SelOutTableAt w (foot' j) cur (cur + 5) mem' (cur + 5) Lw (E j))
    (hT1 : SelOutTableAt w (foot' j) cur (cur + 5) mem' (cur + 5 + 1) Lw (E j)) :
    ∀ i < j + 1,
      SelOutLevelMemAt w P (Lmax i)
        (fun x => BranchBSelZone lo hi cur (cur + 7) x ∧ ∀ r < d, ¬ foot' r x)
        (fun x => foot' i x ∨ (lo ≤ x ∧ x < cur + 7))
        lo (cur + 7) mem' (selBase + 1 + 12 * i) (D i) (G i) (U i) (E i) (vals i) := by
  have hReg : ∀ r < d, ∀ x, lo ≤ x → x < hi → foot' r x → foot r x := fun r _ x _ h2 hf => by
    by_cases hrj : r = j
    · subst hrj
      rcases hFootNew x hf with h' | h'
      · exact h'
      · omega
    · rcases hFootOther r (by omega) hrj x hf with h' | h'
      · exact h'
      · omega
  have hGood : ∀ x, lo ≤ x → x < hi → (∀ r < d, ¬ foot r x) →
      BranchBSelZone lo hi cur (cur + 7) x ∧ ∀ r < d, ¬ foot' r x :=
    fun x h1 h2 hn => ⟨Or.inl ⟨h1, h2⟩, fun r hr hf => hn r hr (hReg r hr x h1 h2 hf)⟩
  have hHigh : ∀ x, cur ≤ x → ¬ foot' j x → ∀ r < d, ¬ foot' r x := fun x hx hn r hr hf => by
    by_cases hrj : r = j
    · subst hrj; exact hn hf
    · rcases hFootOther r hr hrj x hf with h' | h'
      · have := hFootLt r hr x h'; omega
      · omega
  have hRows : ∀ {a : ℕ}, SelOutTableAt w (foot' j) cur (cur + 5) mem' a Lw (E j) →
      SelOutRowsAt w (fun x => foot' j x ∨ (lo ≤ x ∧ x < cur + 7)) (cur + 7) mem' a Lw (E j) :=
    fun {a} hT =>
      ⟨hT.1, fun e he => ⟨by have := (hT.2 e he).1; omega, fun t ht =>
        (hT.2 e he).2 t ht |>.imp id fun ⟨h1, h2⟩ => ⟨by omega, by omega⟩⟩⟩
  intro i hi_lt
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi_lt with hi_lt | hi_eq
  · refine (hDone i hi_lt).transfer (fun k hk12 => ?_) (fun a ha => ?_) hGood
      (fun a ha => ha.imp (hFootSame i hi_lt a).mpr fun ⟨h1, h2, _⟩ => ⟨h1, by omega⟩)
      le_rfl (by omega)
    · refine hKeep _ (by omega) ?_ (by omega) (by omega) (Or.inr (Or.inr ⟨by omega, by omega⟩))
      have := hSlotOff j hj (12 * i + k) (by omega)
      rwa [← Nat.add_assoc] at this
    · rcases ha with ⟨h1, h2, hg⟩ | hf | ⟨h1, h2, hg⟩
      · exact hKeep a h2 (hg j hj) (by omega) (by omega) (Or.inl h1)
      · have := hFootLt i (by omega) a hf
        refine hKeep a this (hDisj i (by omega) (by omega) a hf) ?_ ?_
          (Or.inr (Or.inl ⟨i, hi_lt, hf⟩))
        · rintro rfl
          exact hSlotOff i (by omega) (12 * j + 8) (by omega)
            (by rw [show selBase + 1 + (12 * j + 8) = selBase + 1 + 12 * j + 8 by omega]; exact hf)
        · rintro rfl
          exact hSlotOff i (by omega) (12 * j + 9) (by omega)
            (by rw [show selBase + 1 + (12 * j + 9) = selBase + 1 + 12 * j + 9 by omega]; exact hf)
      · exact hKeep a h2 (hg j hj) (by omega) (by omega) (Or.inl h1)
  · subst i
    refine SelOutLevelMemAt.of_lists
      (hLists.transfer (fun k hk12 h8' h9' => ?_) (fun a h1 h2 hg => ?_) hGood le_rfl
        (by omega)) ?_ (by rw [h9]; exact hLw) (by rw [h8, h9]; exact hSV)
      (by rw [h8, h9]; exact hRows hT0) (by rw [h8, h9]; exact hRows hT1)
    · refine hKeep _ (by omega) ?_ (by omega) (by omega) (Or.inr (Or.inr ⟨by omega, by omega⟩))
      have := hSlotOff j hj (12 * j + k) (by omega)
      rwa [← Nat.add_assoc] at this
    · exact hKeep a h2 (hg j hj) (by omega) (by omega) (Or.inl h1)
    · rw [h8]
      refine ⟨by omega, le_rfl, fun t ht => ⟨Or.inr ⟨by omega, by omega⟩, hHigh _ (by omega) fun hf => ?_⟩⟩
      rcases hFootNew _ hf with h' | h'
      · have := hFootLt j hj _ h'; omega
      · omega

/-- Move the zone form of the finished slots across a step that keeps the footprints, the slots,
and the region `[lo, hX)`. -/
theorem branchBExitZone_frame {w P d lo hS hT hX selBase n : ℕ} {Lmax : ℕ → ℕ}
    {foot foot' : ℕ → ℕ → Prop} {mem mem' : ℕ → ℕ} {D : ℕ → LevelDiffLists} {G : ℕ → MGraph}
    {U : ℕ → List Update} {E : ℕ → Finset ℕ} {vals : ℕ → ℕ → ℝ}
    (h : ∀ j < n, SelOutLevelMemAt w P (Lmax j)
      (fun x => BranchBSelZone lo hS hT hX x ∧ ∀ r < d, ¬ foot r x)
      (fun x => foot j x ∨ (lo ≤ x ∧ x < hX))
      lo hX mem (selBase + 1 + 12 * j) (D j) (G j) (U j) (E j) (vals j))
    (hn : n ≤ d)
    (hFootEq : ∀ r < d, ∀ x, foot' r x ↔ foot r x)
    (hKeep : ∀ a, (∃ j < n, foot j a) ∨ (lo ≤ a ∧ a < hX) → mem' a = mem a)
    (hSlots : ∀ j < n, ∀ i < 12,
      mem' (selBase + 1 + 12 * j + i) = mem (selBase + 1 + 12 * j + i)) :
    ∀ j < n, SelOutLevelMemAt w P (Lmax j)
      (fun x => BranchBSelZone lo hS hT hX x ∧ ∀ r < d, ¬ foot' r x)
      (fun x => foot' j x ∨ (lo ≤ x ∧ x < hX))
      lo hX mem' (selBase + 1 + 12 * j) (D j) (G j) (U j) (E j) (vals j) := by
  intro j hj
  refine (h j hj).transfer (hSlots j hj) (fun a ha => hKeep a ?_)
    (fun a _ _ ⟨hz, hf⟩ => ⟨hz, fun r hr h' => hf r hr ((hFootEq r hr a).mp h')⟩)
    (fun a ha => ha.imp (hFootEq j (lt_of_lt_of_le hj hn) a).mpr id)
    le_rfl le_rfl
  rcases ha with ⟨h1, h2, _⟩ | hf | ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact Or.inl ⟨j, hj, hf⟩
  · exact Or.inr ⟨h1, h2⟩

end MinCostFlow.MinRatio
