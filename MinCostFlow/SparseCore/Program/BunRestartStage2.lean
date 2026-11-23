module

public import MinCostFlow.SparseCore.Program.BunRestartStage1

/-!
# The restart of the bundles: phase D and the sort (`BunRestartStage2`)

`brStage2_runs` runs phase D and the sort step after phases A to C. Afterwards, the memory
represents the cleared table (`clear_rep`), the tour still holds `cord`, and `rList`, the owners
sorted without repeats, is at `h + 6 n + 8 E`.
-/

namespace MinCostFlow.SparseCore.Program.Restart

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

public section

/-- A list read by `bundleReadPairs` gives the words at its addresses. -/
theorem readPairs_getD {mem : ℕ → ℕ} {a n : ℕ} {L : List (ℕ × ℕ)} (h : bundleReadPairs mem a n = L)
    {j : ℕ} (hj : j < n) :
    mem (a + 2 * j) = (L.getD j (0, 0)).1 ∧ mem (a + 2 * j + 1) = (L.getD j (0, 0)).2 := by
  subst h
  rw [List.getD_eq_getElem _ _ (by simp [bundleReadPairs]; omega)]
  simp [bundleReadPairs]

variable {w vCap eCap : ℕ} {p : Program} {ω : ℕ → Bool}
  {TS : BundleTourSpec} {bTourList bTourLen bOwner : ℕ}
  {htour : BundleTourAt TS w vCap eCap p bTourList bTourLen bOwner}
  {slotCap tbl tourH slotsPtr h : ℕ} {slots : List ℕ} {S : Fin slotCap → Option BundleState}
  {m : BundleTableMeta slotCap} {cord : ℕ → List End} {tx₀ : htour.rep.τ}
  {cs : CompLSFState} {ord : ℕ → List End} {mem : ℕ → ℕ}

/-- **Phase D and the sort.** From the state after phase C (as `brStage1_runs` gives it), phase D
and the sort step end with the cleared table, the tour in the same concrete state, the specs and
the pairs kept, and `rList` (the owners sorted without repeats) at `h + 6 n + 8 E` with its length
in register `26`. -/
theorem brStage2_runs (C : BRCtx htour slotCap tbl tourH slotsPtr h slots S m cord tx₀ cs ord mem)
    {bSort : ℕ} (hpSort : p.HasAt bSort (sortProcs bSort)) {stC : State} {txC : htour.rep.τ}
    (hfit : h + 6 * slots.length + 10 * edgeTot S slots < 2 ^ w)
    (hR : BRRegs stC.regs tbl tourH slots.length slotsPtr h slotCap eCap)
    (hL : BRRegsL stC.regs h slots.length (edgeTot S slots))
    (h19 : h + 6 * slots.length + 10 * edgeTot S slots ≤ stC.regs 19)
    (hz : ZeroFrom stC.mem (stC.regs 19))
    (hspecs : bundleReadPairs stC.mem (h + 4 * slots.length) slots.length = brSpecs S slots)
    (hpairs : bundleReadPairs stC.mem (h + 6 * slots.length + 2 * edgeTot S slots) (edgeTot S slots) =
      allPairs eCap tbl S m mem slots)
    (hown : ListAt stC.mem (h + 6 * slots.length + 4 * edgeTot S slots)
      ((allKeys eCap tbl S m mem slots).map (brOwn cs)))
    (hrepT : htour.rep.rep tourH cord txC stC.mem)
    (hfootT : ∀ a, htour.rep.foot tourH txC a → htour.rep.foot tourH tx₀ a ∨
      (h + 6 * slots.length + 10 * edgeTot S slots ≤ a ∧ a < stC.regs 19))
    (hlow : ∀ a < h, ¬ htour.rep.foot tourH tx₀ a → stC.mem a = mem a) :
    ∃ stD stS cD cS rList, Runs w p ω brPhaseD stC .normal stD cD ∧
      Runs w p ω (brSortStmt bSort) stD .normal stS cS ∧
      BRRegs stS.regs tbl tourH slots.length slotsPtr h slotCap eCap ∧
      BRRegsL stS.regs h slots.length (edgeTot S slots) ∧ stS.regs 19 = stC.regs 19 ∧
      stS.regs 26 = rList.length ∧
      rList.Pairwise (· < ·) ∧
      (∀ v, v ∈ rList ↔ v ∈ (allKeys eCap tbl S m mem slots).map (brOwn cs)) ∧
      rList.length ≤ 2 * edgeTot S slots ∧
      ListAt stS.mem (h + 6 * slots.length + 8 * edgeTot S slots) rList ∧
      BundleTableRepAt slotCap vCap eCap tbl (clearS S slots) (clearM m slots) stS.mem ∧
      htour.rep.rep tourH cord txC stS.mem ∧
      htour.rep.phi tourH txC stS.mem = htour.rep.phi tourH txC stC.mem ∧
      bundleReadPairs stS.mem (h + 4 * slots.length) slots.length = brSpecs S slots ∧
      bundleReadPairs stS.mem (h + 6 * slots.length + 2 * edgeTot S slots) (edgeTot S slots) =
        allPairs eCap tbl S m mem slots ∧
      ZeroFrom stS.mem (stS.regs 19) ∧
      (∀ a < h, ¬ bundleTableFoot eCap tbl m a → ¬ htour.rep.foot tourH tx₀ a →
        stS.mem a = mem a) ∧
      stS.mem (btBunCapAddr tbl slotCap eCap) = mem (btBunCapAddr tbl slotCap eCap) ∧
      cD ≤ 30 * edgeTot S slots + 30 * slots.length + 20 ∧
      cS ≤ 400 * edgeTot S slots * (Nat.log 2 (2 * edgeTot S slots + 1) + 1) +
        90 * edgeTot S slots + 100 := by
  set n := slots.length with hn
  set E := edgeTot S slots with hE
  set P := allPairs eCap tbl S m mem slots with hP
  have hw := C.hw
  have hPlen : P.length = E := allPairs_length C.rep C.act'
  have hPmem : ∀ x ∈ P, x.2 ∈ slots ∧ x.1 ∈ (slotB S x.2).edges := fun x hx =>
    (mem_allPairs C.rep C.act').mp hx
  have hPe : ∀ x ∈ P, btEdgeSlotBase tbl slotCap + x.1 < h := fun x hx =>
    C.footT _ (btEdgeSlot_in_foot (C.edge_facts (hPmem x hx).1 (hPmem x hx).2).1)
  have hsl : ∀ s ∈ slots, s < slotCap ∧ btSlotPtrBase tbl + s < h := fun s hs => by
    obtain ⟨hsc, -⟩ := C.act' s hs
    exact ⟨hsc, C.footT _ (btSlotPtr_in_foot hsc)⟩
  have hslen : (brSpecs S slots).length = n := by simp [brSpecs, hn]
  have htblh : btEdgeSlotBase tbl slotCap + eCap ≤ h := by
    have := C.footT (tbl + (bundleTableFixedSize slotCap eCap - 1))
      (Or.inl ⟨Nat.le_add_right _ _, by unfold bundleTableFixedSize; omega⟩)
    unfold bundleTableFixedSize at this
    unfold btEdgeSlotBase
    omega
  obtain ⟨stD, cD, hrD, hregD, hfrD, hzE, hzS, hcD⟩ := brPhaseD_runs (p := p) (ω := ω) (P := P)
    hR hL rfl hw hfit hPlen (fun j hj => (readPairs_getD hpairs hj).1) hPe
    (fun i hi => by
      have := (readPairs_getD hspecs hi).1
      rw [this, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
      simp [brSpecs])
    hsl
  -- The memory that phase D changes lies in the edge slots and slot pointers.
  have hzone : ∀ a, (∃ x ∈ P, a = btEdgeSlotBase tbl slotCap + x.1) ∨
      (∃ s ∈ slots, a = btSlotPtrBase tbl + s) →
      btSlotPtrBase tbl ≤ a ∧ a < btEdgeSlotBase tbl slotCap + eCap := by
    rintro a (⟨x, hx, rfl⟩ | ⟨s, hs, rfl⟩)
    · have := (C.edge_facts (hPmem x hx).1 (hPmem x hx).2).1
      unfold btSlotPtrBase btEdgeSlotBase; omega
    · have := (hsl s hs).1
      unfold btSlotPtrBase btEdgeSlotBase; omega
  have hkeepD : ∀ a, ¬ (btSlotPtrBase tbl ≤ a ∧ a < btEdgeSlotBase tbl slotCap + eCap) →
      stD.mem a = stC.mem a := fun a ha =>
    hfrD a (fun x hx h' => ha (hzone a (Or.inl ⟨x, hx, h'⟩)))
      (fun s hs h' => ha (hzone a (Or.inr ⟨s, hs, h'⟩)))
  have hlowT : ∀ a < h, ¬ bundleTableFoot eCap tbl m a → ¬ htour.rep.foot tourH tx₀ a →
      stD.mem a = mem a := by
    intro a ha hnt hnr
    rw [hkeepD a fun h' => hnt (by
      have : a = btSlotPtrBase tbl + (a - btSlotPtrBase tbl) := by omega
      by_cases hlt : a - btSlotPtrBase tbl < slotCap
      · rw [this]; exact btSlotPtr_in_foot hlt
      · have : a = btEdgeSlotBase tbl slotCap + (a - btEdgeSlotBase tbl slotCap) := by
          unfold btEdgeSlotBase btSlotPtrBase at *; omega
        rw [this]; exact btEdgeSlot_in_foot (by unfold btEdgeSlotBase btSlotPtrBase at *; omega))]
    exact hlow a ha hnr
  -- The cleared table.
  have hclear : BundleTableRepAt slotCap vCap eCap tbl (clearS S slots) (clearM m slots)
      stD.mem := by
    refine clear_rep C.rep (fun a ha hna => (hkeepD a hna).trans
      (hlow a (C.footT a ha) (C.disj a ha))) (fun s hs hsn => ?_) hzS (fun e he hne => ?_) ?_
    · have hfoot := btSlotPtr_in_foot (m := m) (eCap := eCap) (tbl := tbl) hs
      rw [hfrD _ (fun x hx => by
          have := (C.edge_facts (hPmem x hx).1 (hPmem x hx).2).1
          unfold btSlotPtrBase btEdgeSlotBase; omega)
        (fun s' hs' h' => hsn (by have : s = s' := by omega
                                  exact this ▸ hs'))]
      exact hlow _ (C.footT _ hfoot) (C.disj _ hfoot)
    · have hfoot := btEdgeSlot_in_foot (m := m) (tbl := tbl) (slotCap := slotCap) he
      rw [hfrD _ (fun x hx h' => hne x.2 (hPmem x hx).1 (by
          have : e = x.1 := by omega
          exact this ▸ (hPmem x hx).2))
        (fun s hs => by have := (hsl s hs).1; unfold btSlotPtrBase btEdgeSlotBase; omega)]
      exact hlow _ (C.footT _ hfoot) (C.disj _ hfoot)
    · intro s hs e he
      exact hzE (e, s) ((mem_allPairs C.rep C.act').mpr ⟨hs, he⟩)
  -- The sort.
  have hLD : BRRegsL stD.regs h n E := hL.of_eq fun r hr => hregD r (by omega) (by omega)
  have hownD : ListAt stD.mem (h + 6 * n + 4 * E)
      ((allKeys eCap tbl S m mem slots).map (brOwn cs)) :=
    listAt_congr' hown fun j _ => hkeepD _ (by omega)
  have hownLen : ((allKeys eCap tbl S m mem slots).map (brOwn cs)).length = 2 * E := by
    rw [List.length_map, allKeys_length C.rep C.act']
  have hownW : ∀ x ∈ (allKeys eCap tbl S m mem slots).map (brOwn cs), x < 2 ^ w := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    have := (C.keys_ok k hk).2.1
    have := C.vCap_le
    omega
  obtain ⟨stS, cS, rList, hrS, hlt, hmemR, hlenR, hlistR, h26, hregS, hfrS, hcS⟩ :=
    brSort_runs (p := p) (ω := ω) hpSort hLD hw hfit hownLen hownD hownW
  -- What the two steps keep.
  have hkeepS : ∀ a, ¬ (btSlotPtrBase tbl ≤ a ∧ a < btEdgeSlotBase tbl slotCap + eCap) →
      (a < h + 6 * n + 4 * E ∨ h + 6 * n + 10 * E ≤ a) → stS.mem a = stC.mem a :=
    fun a h1 h2 => (hfrS a h2).trans (hkeepD a h1)
  have hregs : ∀ r, r ≠ 10 → r ≠ 11 → r ≠ 21 → r ≠ 26 → stS.regs r = stC.regs r :=
    fun r h1 h2 h3 h4 => (hregS r h3 h4).trans (hregD r h1 h2)
  have hr19 : stS.regs 19 = stC.regs 19 := hregs 19 (by omega) (by omega) (by omega) (by omega)
  have hfootLoc : ∀ a, htour.rep.foot tourH txC a → stC.mem a = stS.mem a := by
    intro a ha
    refine (hkeepS a ?_ ?_).symm
    · rcases hfootT a ha with h0 | h0
      · intro hin
        have hes : btEdgeSlotBase tbl slotCap = btSlotPtrBase tbl + slotCap := by
          unfold btEdgeSlotBase btSlotPtrBase; omega
        by_cases hlt' : a < btEdgeSlotBase tbl slotCap
        · have : a = btSlotPtrBase tbl + (a - btSlotPtrBase tbl) := by omega
          exact C.disj a (this ▸ btSlotPtr_in_foot (by omega)) h0
        · have hlt'' : a - btEdgeSlotBase tbl slotCap < eCap := by omega
          have : a = btEdgeSlotBase tbl slotCap + (a - btEdgeSlotBase tbl slotCap) := by omega
          exact C.disj a (this ▸ btEdgeSlot_in_foot hlt'') h0
      · omega
    · rcases hfootT a ha with h0 | h0
      · exact Or.inl (by have := C.footR a h0; omega)
      · exact Or.inr h0.1
  obtain ⟨hrepS, hphiS⟩ := htour.rep_local tourH cord txC stC.mem stS.mem hfootLoc
  refine ⟨stD, stS, cD, cS, rList, hrD, hrS,
    hR.of_eq fun r hr => hregs r (by omega) (by omega) (by omega) (by omega),
    hL.of_eq fun r hr => hregs r (by omega) (by omega) (by omega) (by omega),
    hr19, h26, hlt, hmemR, hlenR, hlistR, ?_, hrepS hrepT, hphiS.symm, ?_, ?_, ?_, ?_, ?_, hcD, hcS⟩
  · exact hclear.of_agree fun a ha => (hfrS a (Or.inl (by
      have := C.footT a (clearM_foot ha); omega))).symm
  · rw [← hspecs]
    exact readPairs_congr' fun j hj => ⟨hkeepS _ (by omega) (by omega),
      hkeepS _ (by omega) (by omega)⟩
  · rw [← hpairs]
    exact readPairs_congr' fun j hj => ⟨hkeepS _ (by omega) (by omega),
      hkeepS _ (by omega) (by omega)⟩
  · intro a ha
    rw [hr19] at ha
    rw [hkeepS a (by omega) (by omega)]
    exact hz a ha
  · intro a ha hnt hnr
    rw [hfrS a (Or.inl (by omega))]
    exact hlowT a ha hnt hnr
  · have hbc_foot := btBunCap_in_foot (tbl := tbl) (slotCap := slotCap) (eCap := eCap) (m := m)
    have hbc_lt := C.footT _ hbc_foot
    rw [hkeepS _ (by unfold btBunCapAddr btSlotPtrBase btEdgeSlotBase; omega) (Or.inl (by omega))]
    exact hlow _ hbc_lt (C.disj _ hbc_foot)

end

end MinCostFlow.SparseCore.Program.Restart
