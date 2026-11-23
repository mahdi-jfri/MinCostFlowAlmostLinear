module

public import MinCostFlow.SparseCore.Program.BundleStepScanPassA

/-!
# Memory invariant lemmas for Phase 2 Pass B (`BundleStepScanPassBPost`)

Defines `PassBMemInv` (the memory-only loop invariant of `bundleStepScanPassBStmt`) and proves
its four transitions: initialization from Pass A (`passBMemInv_init`), seen-only zeroing
(`passBMemInv_zeroSeen`), new-candidate enqueue (`passBMemInv_enq`), and final assembly into
`BundleTableAfterScan` (`passBMemInv_to_afterScan`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section
open Classical

/-- Memory invariant maintained across iterations `t ≤ xs.length` of Pass B. -/
noncomputable def PassBMemInv {slotCap : ℕ} (_vCap eCap tbl touchedBufPtr : ℕ)
    (S₀ : BundleTableState slotCap) (D : Finset ℕ) (m : BundleTableMeta slotCap)
    (cand₀ : Fin slotCap → Finset ℕ) (xs : List End) (mem₀ : ℕ → ℕ)
    (t : ℕ) (touched : List ℕ) (mem : ℕ → ℕ) : Prop :=
  let S := tableDelEdges S₀ D
  let candT := passBCands S xs t cand₀
  (∀ a, ¬ isPassBAddr eCap tbl touchedBufPtr m a → mem a = mem₀ a) ∧
  touched.Nodup ∧ (∀ s ∈ touched, s < slotCap) ∧
  (∀ s < slotCap, mem (btSlotTouchedBase tbl slotCap eCap + s) = if s ∈ touched then 1 else 0) ∧
  ListAt mem touchedBufPtr touched ∧
  (∀ j : Fin slotCap, match S₀ j with
    | none => j.1 ∉ touched
    | some B₀ => j.1 ∈ touched ↔ (B₀.edges ∩ D).Nonempty ∨ (candT j).Nonempty) ∧
  (∀ j : Fin slotCap, match S j, m.slotBlocks j with
    | none, none => mem (btSlotCandHeadBase tbl slotCap eCap + j.1) = 0
    | some _, some (p, cap) =>
        (∀ b < cap, mem (bsSeenBase p cap + b) =
          if seenVisited S xs t j b then 0 else seenCount S xs j b) ∧
        (∀ b < cap, mem (bsInCandBase p cap + b) = if b ∈ candT j then 1 else 0) ∧
        (∃ cL : List ℕ,
          IsSinglyLinkedList mem (bsCandNextBase p cap)
            (btSlotCandHeadBase tbl slotCap eCap + j.1) cap cL ∧
          ∀ b, b ∈ cL ↔ b ∈ candT j) ∧
        (∀ b < cap, b ∉ candT j → mem (bsCandNextBase p cap + b) = 0)
    | _, _ => False)

end

public section
open Classical

private lemma block_addr_in_foot {slotCap eCap tbl p cap a : ℕ} {m : BundleTableMeta slotCap}
    {j : Fin slotCap} (hm : m.slotBlocks j = some (p, cap))
    (h1 : p ≤ a) (h2 : a < p + bundleSlotBlockSize cap) :
    bundleTableCoreFoot eCap tbl m a :=
  Or.inr ⟨j, p, cap, hm, h1, h2⟩

/-- Initializes `PassBMemInv` at `t = 0` from `BundleTableAfterScan` and Pass A's postcondition. -/
lemma passBMemInv_init {slotCap vCap eCap tbl touchedBufPtr : ℕ}
    {S₀ : BundleTableState slotCap} {D : Finset ℕ} {m : BundleTableMeta slotCap}
    {cand₀ : Fin slotCap → Finset ℕ} {touched₀ : List ℕ} {xs : List End} {mem₀ memA : ℕ → ℕ}
    (htouch_disj_foot : ∀ a, touchedBufPtr ≤ a → a < touchedBufPtr + slotCap →
      ¬ bundleTableCoreFoot eCap tbl m a)
    (hafter₀ : BundleTableAfterScan slotCap vCap eCap tbl S₀ D m cand₀ touched₀ mem₀)
    (htouch₀ : ListAt mem₀ touchedBufPtr touched₀)
    (hseenA : ∀ j : Fin slotCap, ∀ B p cap, tableDelEdges S₀ D j = some B →
      m.slotBlocks j = some (p, cap) →
      ∀ b < cap, memA (bsSeenBase p cap + b) = seenCount (tableDelEdges S₀ D) xs j b)
    (hfrA : ∀ a, ¬ isSeenAddr m a → memA a = mem₀ a) :
    PassBMemInv vCap eCap tbl touchedBufPtr S₀ D m cand₀ xs mem₀ 0 touched₀ memA := by
  set S := tableDelEdges S₀ D
  rcases hafter₀ with ⟨_, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, hslots, hdisjB, htnd₀, htlt₀, htflag₀, hdelL₀, _⟩
  have hcand0_eq : passBCands S xs 0 cand₀ = cand₀ := by
    funext j; unfold passBCands; cases hSj : S j with
    | none => rfl
    | some B =>
      have hemp : (B.vertices.filter fun b => seenVisited S xs 0 j b ∧ seenCount S xs j b < (B.ends b).card) = ∅ := by
        ext b; simp [seenVisited, hSj]
      simp [hemp]
  have hnotSeen_of_notB : ∀ a, ¬ isPassBAddr eCap tbl touchedBufPtr m a → ¬ isSeenAddr m a :=
    fun a hnb ⟨j, p, cap, b, hm, hb, heq⟩ => hnb (Or.inl ⟨j, p, cap, b, hm, hb, Or.inl heq⟩)
  have hstA_fixed_ro : ∀ a, tbl ≤ a → a < tbl + bundleTableCoreSize slotCap eCap → memA a = mem₀ a :=
    fun a ha1 ha2 => hfrA a fun ⟨j, p, cap, b, hm, hb, heq⟩ => by
      have hj := hslots j
      cases hSj : tableDelEdges S₀ D j with
      | none => simp only [hSj, hm] at hj
      | some B =>
        simp only [hSj, hm] at hj
        have hdj : p + (3 + 6 * cap) ≤ tbl ∨ tbl + (14 + 7 * slotCap + 8 * eCap) ≤ p := hj.2.2
        unfold bundleTableCoreSize at ha2; unfold bsSeenBase at heq
        clear * - ha1 ha2 hdj hb heq; omega
  refine ⟨fun a hnb => hfrA a (hnotSeen_of_notB a hnb), htnd₀, htlt₀,
    fun s hs => (hstA_fixed_ro _ (by unfold btSlotTouchedBase; omega)
      (by unfold btSlotTouchedBase bundleTableCoreSize; omega)).trans (htflag₀ s hs),
    fun i hi => by
      have hlt : touched₀.length ≤ slotCap := by
        have hc := Finset.card_le_card (show touched₀.toFinset ⊆ Finset.range slotCap from
          fun x hx => Finset.mem_range.mpr (htlt₀ x (List.mem_toFinset.mp hx)))
        simpa [List.toFinset_card_of_nodup htnd₀] using hc
      rw [hfrA _ (fun ⟨j, p, cap, b, hm, hb, heq⟩ => by
        have hfoot : bundleTableCoreFoot eCap tbl m (bsSeenBase p cap + b) :=
          block_addr_in_foot hm (by unfold bsSeenBase; omega) (by unfold bsSeenBase bundleSlotBlockSize; omega)
        exact htouch_disj_foot (touchedBufPtr + i) (by omega) (by omega) (heq ▸ hfoot))]
      exact htouch₀ i hi,
    fun j => by
      rw [hcand0_eq]; have hj := hdelL₀ j
      cases hSj : S₀ j with
      | none => rw [hSj] at hj; exact hj.2
      | some B₀ => rw [hSj] at hj; exact hj.1,
    fun j => by
      rw [hcand0_eq]; have hj := hslots j
      have hj_lt : j.1 < slotCap := j.2
      cases hSj : tableDelEdges S₀ D j with
      | none =>
        simp only [hSj] at hj ⊢
        cases hm : m.slotBlocks j with
        | none =>
          simp only [hm] at hj ⊢
          exact (hstA_fixed_ro _ (by unfold btSlotCandHeadBase; omega)
            (by unfold btSlotCandHeadBase bundleTableCoreSize; clear * - hj_lt; omega)).trans hj.2.1
        | some _ => simp only [hm] at hj
      | some B =>
        simp only [hSj] at hj ⊢
        cases hm : m.slotBlocks j with
        | none => simp only [hm] at hj
        | some pb =>
          rcases pb with ⟨p, cap⟩; simp only [hm] at hj ⊢
          obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hic, _, ⟨cL, hcL_sll, hcL_mem⟩, hcN0⟩ := hj.2.1
          have hnotSeen_ic : ∀ b < cap, ¬ isSeenAddr m (bsInCandBase p cap + b) := by
            rintro b hb ⟨j', p', cap', b', hm', hb', heq⟩
            by_cases hjj : j' = j
            · subst j'; rw [hm] at hm'; cases hm'; unfold bsInCandBase bsSeenBase at heq; omega
            · have hdj := hdisjB j' j hjj p' cap' p cap hm' hm
              unfold bundleSlotBlockSize at hdj; unfold bsInCandBase bsSeenBase at heq
              clear * - hdj hb hb' heq; omega
          have hnotSeen_cn : ∀ b < cap, ¬ isSeenAddr m (bsCandNextBase p cap + b) := by
            rintro b hb ⟨j', p', cap', b', hm', hb', heq⟩
            by_cases hjj : j' = j
            · subst j'; rw [hm] at hm'; cases hm'; unfold bsCandNextBase bsSeenBase at heq; omega
            · have hdj := hdisjB j' j hjj p' cap' p cap hm' hm
              unfold bundleSlotBlockSize at hdj; unfold bsCandNextBase bsSeenBase at heq
              clear * - hdj hb hb' heq; omega
          refine ⟨fun b hb => by
              have hnv : ¬ seenVisited S xs 0 j b := by simp [seenVisited, S, hSj]
              simpa [S, hnv] using hseenA j B p cap hSj hm b hb,
            fun b hb => (hfrA _ (hnotSeen_ic b hb)).trans (hic b hb),
            ⟨cL, hcL_sll.of_agree
              (hstA_fixed_ro _ (by unfold btSlotCandHeadBase; omega)
                (by unfold btSlotCandHeadBase bundleTableCoreSize; clear * - hj_lt; omega))
              (fun x hx => hfrA _ (hnotSeen_cn x (hcL_sll.mem_lt x hx))), hcL_mem⟩,
            fun b hb hnot => (hfrA _ (hnotSeen_cn b hb)).trans (hcN0 b hb hnot)⟩⟩

/-- Preserves `PassBMemInv` when zeroing `bsSeenBase p cap + b` without changing `passBCands`. -/
lemma passBMemInv_zeroSeen {slotCap vCap eCap tbl touchedBufPtr t p cap b : ℕ}
    {S₀ : BundleTableState slotCap} {D : Finset ℕ} {m : BundleTableMeta slotCap}
    {cand₀ : Fin slotCap → Finset ℕ} {touched : List ℕ} {xs : List End}
    {js : Fin slotCap} {mem₀ mem : ℕ → ℕ}
    (htouch_disj_foot : ∀ a, touchedBufPtr ≤ a → a < touchedBufPtr + slotCap →
      ¬ bundleTableCoreFoot eCap tbl m a)
    (hdisjB : ∀ j₁ j₂ : Fin slotCap, j₁ ≠ j₂ → ∀ p₁ c₁ p₂ c₂,
      m.slotBlocks j₁ = some (p₁, c₁) → m.slotBlocks j₂ = some (p₂, c₂) →
      p₁ + bundleSlotBlockSize c₁ ≤ p₂ ∨ p₂ + bundleSlotBlockSize c₂ ≤ p₁)
    (hp_disj_tbl : p + bundleSlotBlockSize cap ≤ tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ p)
    (hm_js : m.slotBlocks js = some (p, cap)) (hb_cap : b < cap)
    (hvis_now : seenVisited (tableDelEdges S₀ D) xs (t + 1) js b)
    (hvis_other : ∀ (j' : Fin slotCap) b', (j' ≠ js ∨ b' ≠ b) →
      (seenVisited (tableDelEdges S₀ D) xs (t + 1) j' b' ↔
        seenVisited (tableDelEdges S₀ D) xs t j' b'))
    (hcand_eq : passBCands (tableDelEdges S₀ D) xs (t + 1) cand₀ =
      passBCands (tableDelEdges S₀ D) xs t cand₀)
    (hInv : PassBMemInv vCap eCap tbl touchedBufPtr S₀ D m cand₀ xs mem₀ t touched mem) :
    PassBMemInv vCap eCap tbl touchedBufPtr S₀ D m cand₀ xs mem₀ (t + 1) touched
      (Function.update mem (bsSeenBase p cap + b) 0) := by
  set a_seen := bsSeenBase p cap + b
  have hp_disj_tbl' : p + (3 + 6 * cap) ≤ tbl ∨ tbl + (14 + 7 * slotCap + 8 * eCap) ≤ p := hp_disj_tbl
  rcases hInv with ⟨hfr, htnd, htlt, htflag, htouch, hdelT, hslotsT⟩
  refine ⟨fun a hnb => by
      have hne : a ≠ a_seen := fun h => hnb (Or.inl ⟨js, p, cap, b, hm_js, hb_cap, Or.inl h⟩)
      rw [Function.update_of_ne hne]; exact hfr a hnb,
    htnd, htlt,
    fun s hs => by
      have hne : btSlotTouchedBase tbl slotCap eCap + s ≠ a_seen := by
        unfold a_seen; unfold btSlotTouchedBase bsSeenBase; clear * - hp_disj_tbl' hs hb_cap; omega
      rw [Function.update_of_ne hne]; exact htflag s hs,
    fun idx hidx => by
      have hle : touched.length ≤ slotCap := by
        have hc := Finset.card_le_card (show touched.toFinset ⊆ Finset.range slotCap from
          fun y hy => Finset.mem_range.mpr (htlt y (List.mem_toFinset.mp hy)))
        simpa [List.toFinset_card_of_nodup htnd] using hc
      have hne : touchedBufPtr + idx ≠ a_seen := fun h => by
        have hfoot : bundleTableCoreFoot eCap tbl m a_seen :=
          block_addr_in_foot hm_js (by unfold a_seen bsSeenBase; omega) (by unfold a_seen bsSeenBase bundleSlotBlockSize; omega)
        exact htouch_disj_foot (touchedBufPtr + idx) (by omega) (by omega) (h ▸ hfoot)
      rw [Function.update_of_ne hne]; exact htouch idx hidx,
    fun j' => by rw [hcand_eq]; exact hdelT j',
    fun j' => by
      rw [hcand_eq]; have hj' := hslotsT j'
      have hj'_lt : j'.1 < slotCap := j'.2
      cases hSj' : tableDelEdges S₀ D j' with
      | none =>
        rw [hSj'] at hj'; cases hm' : m.slotBlocks j' with
        | none =>
          rw [hm'] at hj'
          have hne : btSlotCandHeadBase tbl slotCap eCap + j'.1 ≠ a_seen := by
            unfold a_seen; unfold btSlotCandHeadBase bsSeenBase; clear * - hp_disj_tbl' hj'_lt hb_cap; omega
          rw [Function.update_of_ne hne]; exact hj'
        | some _ => rw [hm'] at hj'; exact False.elim hj'
      | some B' =>
        rw [hSj'] at hj'; cases hm' : m.slotBlocks j' with
        | none => rw [hm'] at hj'; exact False.elim hj'
        | some pb' =>
          rcases pb' with ⟨p', cap'⟩; rw [hm'] at hj'
          have hne_ic' : ∀ b' < cap', bsInCandBase p' cap' + b' ≠ a_seen := fun b' hb' => by
            by_cases hjj : j' = js
            · subst j'; rw [hm_js] at hm'; cases hm'; unfold a_seen; unfold bsInCandBase bsSeenBase; omega
            · have hdj := hdisjB j' js hjj p' cap' p cap hm' hm_js
              unfold bundleSlotBlockSize at hdj; unfold a_seen; unfold bsInCandBase bsSeenBase
              clear * - hdj hb' hb_cap; omega
          have hne_cn' : ∀ b' < cap', bsCandNextBase p' cap' + b' ≠ a_seen := fun b' hb' => by
            by_cases hjj : j' = js
            · subst j'; rw [hm_js] at hm'; cases hm'; unfold a_seen; unfold bsCandNextBase bsSeenBase; omega
            · have hdj := hdisjB j' js hjj p' cap' p cap hm' hm_js
              unfold bundleSlotBlockSize at hdj; unfold a_seen; unfold bsCandNextBase bsSeenBase
              clear * - hdj hb' hb_cap; omega
          have hne_ch' : btSlotCandHeadBase tbl slotCap eCap + j'.1 ≠ a_seen := by
            unfold a_seen; unfold btSlotCandHeadBase bsSeenBase; clear * - hp_disj_tbl' hj'_lt hb_cap; omega
          refine ⟨fun b' hb' => ?_,
            fun b' hb' => by rw [Function.update_of_ne (hne_ic' b' hb')]; exact hj'.2.1 b' hb',
            ?_,
            fun b' hb' hnot => by rw [Function.update_of_ne (hne_cn' b' hb')]; exact hj'.2.2.2 b' hb' hnot⟩
          · by_cases hjb : j' = js ∧ b' = b
            · rcases hjb with ⟨rfl, rfl⟩; rw [hm_js] at hm'; cases hm'
              simp [a_seen, hvis_now]
            · have hne : bsSeenBase p' cap' + b' ≠ a_seen := by
                by_cases hjj : j' = js
                · subst j'; rw [hm_js] at hm'; cases hm'
                  have hbb : b' ≠ b := fun h => hjb ⟨rfl, h⟩
                  unfold a_seen; unfold bsSeenBase; omega
                · have hdj := hdisjB j' js hjj p' cap' p cap hm' hm_js
                  unfold bundleSlotBlockSize at hdj; unfold a_seen; unfold bsSeenBase
                  clear * - hdj hb' hb_cap; omega
              have hv_iff := hvis_other j' b' (not_and_or.mp hjb)
              rw [Function.update_of_ne hne]; simp only [hv_iff]
              exact hj'.1 b' hb'
          · obtain ⟨cL', hcL'_sll, hcL'_mem⟩ := hj'.2.2.1
            exact ⟨cL', hcL'_sll.of_agree (Function.update_of_ne hne_ch' _ _)
              (fun y hy => Function.update_of_ne (hne_cn' y (hcL'_sll.mem_lt y hy)) _ _), hcL'_mem⟩⟩

/-- Preserves `PassBMemInv` when zeroing `seen[b]` AND enqueueing brand-new candidate `b` into `js`. -/
lemma passBMemInv_enq {slotCap vCap eCap tbl touchedBufPtr t p cap b : ℕ}
    {S₀ : BundleTableState slotCap} {D : Finset ℕ} {m : BundleTableMeta slotCap}
    {cand₀ : Fin slotCap → Finset ℕ} {touched : List ℕ} {xs : List End}
    {js : Fin slotCap} {B : BundleState} {mem₀ mem memf : ℕ → ℕ}
    (htouch_disj_foot : ∀ a, touchedBufPtr ≤ a → a < touchedBufPtr + slotCap →
      ¬ bundleTableCoreFoot eCap tbl m a)
    (hdisjB : ∀ j₁ j₂ : Fin slotCap, j₁ ≠ j₂ → ∀ p₁ c₁ p₂ c₂,
      m.slotBlocks j₁ = some (p₁, c₁) → m.slotBlocks j₂ = some (p₂, c₂) →
      p₁ + bundleSlotBlockSize c₁ ≤ p₂ ∨ p₂ + bundleSlotBlockSize c₂ ≤ p₁)
    (hblks_disj_tbl : ∀ j : Fin slotCap, ∀ p' c', m.slotBlocks j = some (p', c') →
      p' + bundleSlotBlockSize c' ≤ tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ p')
    (hSjs : tableDelEdges S₀ D js = some B)
    (hm_js : m.slotBlocks js = some (p, cap)) (hb_cap : b < cap)
    (hnot_c : b ∉ passBCands (tableDelEdges S₀ D) xs t cand₀ js)
    (hvis_now : seenVisited (tableDelEdges S₀ D) xs (t + 1) js b)
    (hvis_other : ∀ (j' : Fin slotCap) b', (j' ≠ js ∨ b' ≠ b) →
      (seenVisited (tableDelEdges S₀ D) xs (t + 1) j' b' ↔
        seenVisited (tableDelEdges S₀ D) xs t j' b'))
    (hcand_step : ∀ j', passBCands (tableDelEdges S₀ D) xs (t + 1) cand₀ j' =
      if j' = js then insert b (passBCands (tableDelEdges S₀ D) xs t cand₀ js)
      else passBCands (tableDelEdges S₀ D) xs t cand₀ j')
    (hInv : PassBMemInv vCap eCap tbl touchedBufPtr S₀ D m cand₀ xs mem₀ t touched mem)
    (hmemf_eq :
      let mem_e3 :=
        Function.update
          (Function.update
            (Function.update
              (Function.update mem (bsSeenBase p cap + b) 0)
              (bsInCandBase p cap + b) 1)
            (bsCandNextBase p cap + b) (mem (btSlotCandHeadBase tbl slotCap eCap + js.1)))
          (btSlotCandHeadBase tbl slotCap eCap + js.1) (b + 1)
      (js.1 ∈ touched → memf = mem_e3) ∧
      (js.1 ∉ touched → memf = Function.update
        (Function.update mem_e3 (btSlotTouchedBase tbl slotCap eCap + js.1) 1)
        (touchedBufPtr + touched.length) js.1)) :
    let touched' := if js.1 ∈ touched then touched else touched ++ [js.1]
    PassBMemInv vCap eCap tbl touchedBufPtr S₀ D m cand₀ xs mem₀ (t + 1) touched' memf := by
  intro touched'
  have hjs_lt : js.1 < slotCap := js.2
  have hp_disj_tbl' : p + (3 + 6 * cap) ≤ tbl ∨ tbl + (14 + 7 * slotCap + 8 * eCap) ≤ p :=
    hblks_disj_tbl js p cap hm_js
  rcases hInv with ⟨hfr, htnd, htlt, htflag, htouch, hdelT, hslotsT⟩
  set a_seen := bsSeenBase p cap + b
  set a_ic := bsInCandBase p cap + b
  set a_cn := bsCandNextBase p cap + b
  set a_ch := btSlotCandHeadBase tbl slotCap eCap + js.1
  set a_tf := btSlotTouchedBase tbl slotCap eCap + js.1
  set a_tb := touchedBufPtr + touched.length
  set mem_e3 := Function.update (Function.update (Function.update
    (Function.update mem a_seen 0) a_ic 1) a_cn (mem a_ch)) a_ch (b + 1)
  have htlen_lt_of_not : js.1 ∉ touched → touched.length < slotCap := fun hmt => by
    have hsub : touched.toFinset ⊂ Finset.range slotCap :=
      Finset.ssubset_iff_subset_ne.mpr
        ⟨fun y hy => Finset.mem_range.mpr (htlt y (List.mem_toFinset.mp hy)),
         fun heq => hmt (List.mem_toFinset.mp (heq ▸ Finset.mem_range.mpr hjs_lt))⟩
    have := Finset.card_lt_card hsub
    rwa [List.toFinset_card_of_nodup htnd, Finset.card_range] at this
  have hsf_e3_foot : ∀ a, bundleTableCoreFoot eCap tbl m a → a ≠ a_tf → memf a = mem_e3 a :=
    fun a ha hntf => by
      by_cases hmt : js.1 ∈ touched
      · rw [hmemf_eq.1 hmt]
      · have hlt := htlen_lt_of_not hmt
        have hntb : a ≠ a_tb := fun h => htouch_disj_foot a (by unfold a_tb at h; omega) (by unfold a_tb at h; omega) ha
        rw [hmemf_eq.2 hmt, Function.update_of_ne hntb, Function.update_of_ne hntf]
  have hsf_st_foot : ∀ a, bundleTableCoreFoot eCap tbl m a →
      a ≠ a_seen → a ≠ a_ic → a ≠ a_cn → a ≠ a_ch → a ≠ a_tf → memf a = mem a :=
    fun a ha h1 h2 h3 h4 h5 => by
      rw [hsf_e3_foot a ha h5]
      simp only [mem_e3, Function.update_of_ne h4, Function.update_of_ne h3,
        Function.update_of_ne h2, Function.update_of_ne h1]
  have hne_tf_ch : a_tf ≠ a_ch := by unfold a_tf a_ch btSlotTouchedBase btSlotCandHeadBase; clear * - hjs_lt; omega
  have hne_tf_cn : a_tf ≠ a_cn := by unfold a_tf a_cn btSlotTouchedBase bsCandNextBase; clear * - hp_disj_tbl' hjs_lt hb_cap; omega
  have hne_tf_ic : a_tf ≠ a_ic := by unfold a_tf a_ic btSlotTouchedBase bsInCandBase; clear * - hp_disj_tbl' hjs_lt hb_cap; omega
  have hne_tf_seen : a_tf ≠ a_seen := by unfold a_tf a_seen btSlotTouchedBase bsSeenBase; clear * - hp_disj_tbl' hjs_lt hb_cap; omega
  have hne_ch_cn : a_ch ≠ a_cn := by unfold a_ch a_cn btSlotCandHeadBase bsCandNextBase; clear * - hp_disj_tbl' hjs_lt hb_cap; omega
  have hne_ch_ic : a_ch ≠ a_ic := by unfold a_ch a_ic btSlotCandHeadBase bsInCandBase; clear * - hp_disj_tbl' hjs_lt hb_cap; omega
  have hne_ch_seen : a_ch ≠ a_seen := by unfold a_ch a_seen btSlotCandHeadBase bsSeenBase; clear * - hp_disj_tbl' hjs_lt hb_cap; omega
  have hne_cn_ic : a_cn ≠ a_ic := by unfold a_cn a_ic bsCandNextBase bsInCandBase; omega
  have hne_cn_seen : a_cn ≠ a_seen := by unfold a_cn a_seen bsCandNextBase bsSeenBase; omega
  have hne_ic_seen : a_ic ≠ a_seen := by unfold a_ic a_seen bsInCandBase bsSeenBase; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a hnb
    have hne_s : a ≠ a_seen := fun h => hnb (Or.inl ⟨js, p, cap, b, hm_js, hb_cap, Or.inl h⟩)
    have hne_i : a ≠ a_ic := fun h => hnb (Or.inl ⟨js, p, cap, b, hm_js, hb_cap, Or.inr (Or.inl h)⟩)
    have hne_c : a ≠ a_cn := fun h => hnb (Or.inl ⟨js, p, cap, b, hm_js, hb_cap, Or.inr (Or.inr h)⟩)
    have hne_h : a ≠ a_ch := fun h => hnb (Or.inr (Or.inl ⟨js.1, hjs_lt, Or.inl h⟩))
    have hne_f : a ≠ a_tf := fun h => hnb (Or.inr (Or.inl ⟨js.1, hjs_lt, Or.inr h⟩))
    have he3 : memf a = mem_e3 a := by
      by_cases hmt : js.1 ∈ touched
      · rw [hmemf_eq.1 hmt]
      · have hlt := htlen_lt_of_not hmt
        have hne_b : a ≠ a_tb := fun h => hnb (Or.inr (Or.inr ⟨by unfold a_tb at h; omega, by unfold a_tb at h; omega⟩))
        rw [hmemf_eq.2 hmt, Function.update_of_ne hne_b, Function.update_of_ne hne_f]
    rw [he3]
    simp only [mem_e3, Function.update_of_ne hne_h, Function.update_of_ne hne_c,
      Function.update_of_ne hne_i, Function.update_of_ne hne_s]
    exact hfr a hnb
  · dsimp only [touched']; split_ifs with hmt
    · exact htnd
    · rw [List.nodup_append]
      exact ⟨htnd, List.nodup_singleton _, fun y hy z hz hyz => hmt (by simp at hz; rwa [← hz, ← hyz])⟩
  · intro s hs; dsimp only [touched'] at hs; split_ifs at hs
    · exact htlt s hs
    · rcases List.mem_append.mp hs with h1 | h2
      · exact htlt s h1
      · simp at h2; rw [h2]; exact hjs_lt
  · intro s hs
    have hfoot_s : bundleTableCoreFoot eCap tbl m (btSlotTouchedBase tbl slotCap eCap + s) :=
      Or.inl ⟨by unfold btSlotTouchedBase; omega, by unfold btSlotTouchedBase bundleTableCoreSize; omega⟩
    by_cases hss : s = js.1
    · subst s
      have hin : js.1 ∈ touched' := by dsimp only [touched']; split_ifs with h <;> simp [h]
      simp only [hin, ↓reduceIte]; change memf a_tf = 1
      by_cases hmt : js.1 ∈ touched
      · rw [hmemf_eq.1 hmt]
        simp only [mem_e3, Function.update_of_ne hne_tf_ch, Function.update_of_ne hne_tf_cn,
          Function.update_of_ne hne_tf_ic, Function.update_of_ne hne_tf_seen]
        simpa [a_tf, hmt] using htflag js.1 hjs_lt
      · have hlt := htlen_lt_of_not hmt
        have hntb : a_tf ≠ a_tb := fun h => htouch_disj_foot a_tf (by unfold a_tb at h; omega) (by unfold a_tb at h; omega) hfoot_s
        rw [hmemf_eq.2 hmt, Function.update_of_ne hntb, Function.update_self]
    · have hiff : s ∈ touched' ↔ s ∈ touched := by dsimp only [touched']; split_ifs <;> simp [hss]
      rw [hsf_st_foot _ hfoot_s
        (by unfold btSlotTouchedBase a_seen bsSeenBase; clear * - hp_disj_tbl' hs hb_cap; omega)
        (by unfold btSlotTouchedBase a_ic bsInCandBase; clear * - hp_disj_tbl' hs hb_cap; omega)
        (by unfold btSlotTouchedBase a_cn bsCandNextBase; clear * - hp_disj_tbl' hs hb_cap; omega)
        (by unfold btSlotTouchedBase a_ch btSlotCandHeadBase; clear * - hs; omega)
        (by unfold a_tf; omega)]
      simpa [hiff] using htflag s hs
  · have htlen_le : touched.length ≤ slotCap := by
      have hc := Finset.card_le_card (show touched.toFinset ⊆ Finset.range slotCap from
        fun y hy => Finset.mem_range.mpr (htlt y (List.mem_toFinset.mp hy)))
      simpa [List.toFinset_card_of_nodup htnd] using hc
    have hf_ch : bundleTableCoreFoot eCap tbl m a_ch :=
      Or.inl ⟨by unfold a_ch btSlotCandHeadBase; omega, by unfold a_ch btSlotCandHeadBase bundleTableCoreSize; clear * - hjs_lt; omega⟩
    have hf_tf : bundleTableCoreFoot eCap tbl m a_tf :=
      Or.inl ⟨by unfold a_tf btSlotTouchedBase; omega, by unfold a_tf btSlotTouchedBase bundleTableCoreSize; clear * - hjs_lt; omega⟩
    have hf_cn : bundleTableCoreFoot eCap tbl m a_cn :=
      block_addr_in_foot hm_js (by unfold a_cn bsCandNextBase; omega) (by unfold a_cn bsCandNextBase bundleSlotBlockSize; omega)
    have hf_ic : bundleTableCoreFoot eCap tbl m a_ic :=
      block_addr_in_foot hm_js (by unfold a_ic bsInCandBase; omega) (by unfold a_ic bsInCandBase bundleSlotBlockSize; omega)
    have hf_seen : bundleTableCoreFoot eCap tbl m a_seen :=
      block_addr_in_foot hm_js (by unfold a_seen bsSeenBase; omega) (by unfold a_seen bsSeenBase bundleSlotBlockSize; omega)
    intro idx hidx
    dsimp only [touched'] at hidx ⊢
    split_ifs at hidx ⊢ with hmt
    · have hnf := htouch_disj_foot (touchedBufPtr + idx) (by omega) (by omega)
      have hne_ch : touchedBufPtr + idx ≠ a_ch := fun h => hnf (h ▸ hf_ch)
      have hne_cn : touchedBufPtr + idx ≠ a_cn := fun h => hnf (h ▸ hf_cn)
      have hne_ic : touchedBufPtr + idx ≠ a_ic := fun h => hnf (h ▸ hf_ic)
      have hne_seen : touchedBufPtr + idx ≠ a_seen := fun h => hnf (h ▸ hf_seen)
      rw [hmemf_eq.1 hmt]
      simp only [mem_e3, Function.update_of_ne hne_ch, Function.update_of_ne hne_cn,
        Function.update_of_ne hne_ic, Function.update_of_ne hne_seen]
      exact htouch idx hidx
    · simp only [List.length_append, List.length_singleton] at hidx
      by_cases hlt_i : idx < touched.length
      · rw [List.getElem_append_left hlt_i]
        have hnf := htouch_disj_foot (touchedBufPtr + idx) (by omega) (by omega)
        have hne_tf : touchedBufPtr + idx ≠ a_tf := fun h => hnf (h ▸ hf_tf)
        have hne_ch : touchedBufPtr + idx ≠ a_ch := fun h => hnf (h ▸ hf_ch)
        have hne_cn : touchedBufPtr + idx ≠ a_cn := fun h => hnf (h ▸ hf_cn)
        have hne_ic : touchedBufPtr + idx ≠ a_ic := fun h => hnf (h ▸ hf_ic)
        have hne_seen : touchedBufPtr + idx ≠ a_seen := fun h => hnf (h ▸ hf_seen)
        rw [hmemf_eq.2 hmt, Function.update_of_ne (by unfold a_tb; omega),
          Function.update_of_ne hne_tf]
        simp only [mem_e3, Function.update_of_ne hne_ch, Function.update_of_ne hne_cn,
          Function.update_of_ne hne_ic, Function.update_of_ne hne_seen]
        exact htouch idx hlt_i
      · have heq : idx = touched.length := by omega
        subst heq; rw [List.getElem_append_right (le_refl _)]
        simp only [Nat.sub_self, List.getElem_singleton]
        rw [hmemf_eq.2 hmt]; exact Function.update_self _ _ _
  · intro j'; have hj' := hdelT j'; rw [hcand_step j']
    by_cases hjj : j' = js
    · subst j'; simp only [↓reduceIte]
      have hS₀_some : ∃ B₀, S₀ js = some B₀ := by
        simp only [tableDelEdges, Option.map_eq_some_iff] at hSjs
        rcases hSjs with ⟨B₀, h0, _⟩; exact ⟨B₀, h0⟩
      rcases hS₀_some with ⟨B₀, hS₀j⟩
      rw [hS₀j] at hj' ⊢
      exact ⟨fun _ => Or.inr ⟨b, Finset.mem_insert_self b _⟩,
        fun _ => by dsimp only [touched']; split_ifs with h <;> simp [h]⟩
    · simp only [hjj, ↓reduceIte]
      have hiff : j'.1 ∈ touched' ↔ j'.1 ∈ touched := by
        dsimp only [touched']; split_ifs <;> simp [Fin.val_ne_of_ne hjj]
      cases hS₀j : S₀ j' with
      | none => rw [hS₀j] at hj'; rwa [hiff]
      | some B₀ => rw [hS₀j] at hj'; rwa [hiff]
  · intro j'; have hj' := hslotsT j'; rw [hcand_step j']
    have hj'_lt : j'.1 < slotCap := j'.2
    by_cases hjj : j' = js
    · subst j'; simp only [↓reduceIte]; rw [hSjs, hm_js] at hj' ⊢
      rcases hj' with ⟨hjs_seen, hjs_ic, ⟨cL, hcL_sll, hcL_mem⟩, hjs_cn0⟩
      refine ⟨fun b' hb' => ?_, fun b' hb' => ?_, ?_, fun b' hb' hnot => ?_⟩
      · by_cases hbb : b' = b
        · subst b'
          have hf : bundleTableCoreFoot eCap tbl m a_seen :=
            block_addr_in_foot hm_js (by unfold a_seen bsSeenBase; omega) (by unfold a_seen bsSeenBase bundleSlotBlockSize; omega)
          change memf a_seen = _
          rw [hsf_e3_foot a_seen hf hne_tf_seen.symm]
          simp only [mem_e3, Function.update_of_ne hne_ch_seen.symm, Function.update_of_ne hne_cn_seen.symm,
            Function.update_of_ne hne_ic_seen.symm, Function.update_self, hvis_now, ↓reduceIte]
        · have hf : bundleTableCoreFoot eCap tbl m (bsSeenBase p cap + b') :=
            block_addr_in_foot hm_js (by unfold bsSeenBase; omega) (by unfold bsSeenBase bundleSlotBlockSize; omega)
          rw [hsf_st_foot _ hf (by unfold a_seen bsSeenBase; omega)
            (by unfold a_ic bsSeenBase bsInCandBase; omega)
            (by unfold a_cn bsSeenBase bsCandNextBase; omega)
            (by unfold a_ch bsSeenBase btSlotCandHeadBase; clear * - hp_disj_tbl' hjs_lt hb'; omega)
            (by unfold a_tf bsSeenBase btSlotTouchedBase; clear * - hp_disj_tbl' hjs_lt hb'; omega)]
          simp only [hvis_other js b' (Or.inr hbb)]
          exact hjs_seen b' hb'
      · by_cases hbb : b' = b
        · subst b'; simp only [Finset.mem_insert_self, ↓reduceIte]
          have hf : bundleTableCoreFoot eCap tbl m a_ic :=
            block_addr_in_foot hm_js (by unfold a_ic bsInCandBase; omega) (by unfold a_ic bsInCandBase bundleSlotBlockSize; omega)
          change memf a_ic = 1
          rw [hsf_e3_foot a_ic hf hne_tf_ic.symm]
          simp only [mem_e3, Function.update_of_ne hne_ch_ic.symm, Function.update_of_ne hne_cn_ic.symm, Function.update_self]
        · have hf : bundleTableCoreFoot eCap tbl m (bsInCandBase p cap + b') :=
            block_addr_in_foot hm_js (by unfold bsInCandBase; omega) (by unfold bsInCandBase bundleSlotBlockSize; omega)
          rw [hsf_st_foot _ hf (by unfold a_seen bsInCandBase bsSeenBase; omega)
            (by unfold a_ic bsInCandBase; omega)
            (by unfold a_cn bsInCandBase bsCandNextBase; omega)
            (by unfold a_ch bsInCandBase btSlotCandHeadBase; clear * - hp_disj_tbl' hjs_lt hb'; omega)
            (by unfold a_tf bsInCandBase btSlotTouchedBase; clear * - hp_disj_tbl' hjs_lt hb'; omega)]
          simpa [Finset.mem_insert, hbb] using hjs_ic b' hb'
      · refine ⟨b :: cL, ?_, fun b' => by simp [List.mem_cons, hcL_mem, Finset.mem_insert]⟩
        have hf_ch : bundleTableCoreFoot eCap tbl m a_ch :=
          Or.inl ⟨by unfold a_ch btSlotCandHeadBase; omega, by unfold a_ch btSlotCandHeadBase bundleTableCoreSize; clear * - hjs_lt; omega⟩
        have hf_cn : bundleTableCoreFoot eCap tbl m a_cn :=
          block_addr_in_foot hm_js (by unfold a_cn bsCandNextBase; omega) (by unfold a_cn bsCandNextBase bundleSlotBlockSize; omega)
        have hch_v : memf a_ch = b + 1 := by
          rw [hsf_e3_foot a_ch hf_ch hne_tf_ch.symm]; exact Function.update_self _ _ _
        have hcn_v : memf a_cn = mem a_ch := by
          rw [hsf_e3_foot a_cn hf_cn hne_tf_cn.symm]
          simp only [mem_e3, Function.update_of_ne hne_ch_cn.symm, Function.update_self]
        exact hcL_sll.cons hb_cap (fun h => hnot_c ((hcL_mem b).mp h)) hch_v hcn_v fun y hy => by
          have hylt := hcL_sll.mem_lt y hy
          have hne_y : y ≠ b := fun h => hnot_c ((hcL_mem b).mp (h ▸ hy))
          have hf_y : bundleTableCoreFoot eCap tbl m (bsCandNextBase p cap + y) :=
            block_addr_in_foot hm_js (by unfold bsCandNextBase; omega) (by unfold bsCandNextBase bundleSlotBlockSize; omega)
          exact hsf_st_foot _ hf_y
            (by unfold a_seen bsCandNextBase bsSeenBase; omega)
            (by unfold a_ic bsCandNextBase bsInCandBase; omega)
            (by unfold a_cn bsCandNextBase; omega)
            (by unfold a_ch bsCandNextBase btSlotCandHeadBase; clear * - hp_disj_tbl' hjs_lt hylt; omega)
            (by unfold a_tf bsCandNextBase btSlotTouchedBase; clear * - hp_disj_tbl' hjs_lt hylt; omega)
      · have hbb : b' ≠ b := fun h => hnot (h ▸ Finset.mem_insert_self _ _)
        have hnot' : b' ∉ passBCands (tableDelEdges S₀ D) xs t cand₀ js := fun h => hnot (Finset.mem_insert_of_mem h)
        have hf : bundleTableCoreFoot eCap tbl m (bsCandNextBase p cap + b') :=
          block_addr_in_foot hm_js (by unfold bsCandNextBase; omega) (by unfold bsCandNextBase bundleSlotBlockSize; omega)
        rw [hsf_st_foot _ hf (by unfold a_seen bsCandNextBase bsSeenBase; omega)
          (by unfold a_ic bsCandNextBase bsInCandBase; omega)
          (by unfold a_cn bsCandNextBase; omega)
          (by unfold a_ch bsCandNextBase btSlotCandHeadBase; clear * - hp_disj_tbl' hjs_lt hb'; omega)
          (by unfold a_tf bsCandNextBase btSlotTouchedBase; clear * - hp_disj_tbl' hjs_lt hb'; omega)]
        exact hjs_cn0 b' hb' hnot'
    · simp only [hjj, ↓reduceIte]
      have hf_ch : bundleTableCoreFoot eCap tbl m (btSlotCandHeadBase tbl slotCap eCap + j'.1) :=
        Or.inl ⟨by unfold btSlotCandHeadBase; omega, by unfold btSlotCandHeadBase bundleTableCoreSize; clear * - hj'_lt; omega⟩
      have hch_eq : memf (btSlotCandHeadBase tbl slotCap eCap + j'.1) =
          mem (btSlotCandHeadBase tbl slotCap eCap + j'.1) :=
        hsf_st_foot _ hf_ch
          (by unfold a_seen btSlotCandHeadBase bsSeenBase; clear * - hp_disj_tbl' hj'_lt hb_cap; omega)
          (by unfold a_ic btSlotCandHeadBase bsInCandBase; clear * - hp_disj_tbl' hj'_lt hb_cap; omega)
          (by unfold a_cn btSlotCandHeadBase bsCandNextBase; clear * - hp_disj_tbl' hj'_lt hb_cap; omega)
          (by unfold a_ch; exact fun h => hjj (Fin.ext (by omega)))
          (by unfold a_tf btSlotCandHeadBase btSlotTouchedBase; clear * - hjs_lt; omega)
      cases hSj' : tableDelEdges S₀ D j' with
      | none =>
        rw [hSj'] at hj'; cases hm' : m.slotBlocks j' with
        | none => rw [hm'] at hj'; exact hch_eq.trans hj'
        | some _ => rw [hm'] at hj'; exact False.elim hj'
      | some B' =>
        rw [hSj'] at hj'; cases hm' : m.slotBlocks j' with
        | none => rw [hm'] at hj'; exact False.elim hj'
        | some pb' =>
          rcases pb' with ⟨p', cap'⟩; rw [hm'] at hj'
          have hdj' : p' + (3 + 6 * cap') ≤ p ∨ p + (3 + 6 * cap) ≤ p' := hdisjB j' js hjj p' cap' p cap hm' hm_js
          have hp'_disj_tbl' : p' + (3 + 6 * cap') ≤ tbl ∨ tbl + (14 + 7 * slotCap + 8 * eCap) ≤ p' :=
            hblks_disj_tbl j' p' cap' hm'
          have hblk_eq : ∀ off < bundleSlotBlockSize cap', memf (p' + off) = mem (p' + off) :=
            fun off hoff => by
              have hoff' : off < 3 + 6 * cap' := hoff
              exact hsf_st_foot _ (bsAddr_in_coreFoot hm' hoff)
                (by unfold a_seen bsSeenBase; clear * - hdj' hoff' hb_cap; omega)
                (by unfold a_ic bsInCandBase; clear * - hdj' hoff' hb_cap; omega)
                (by unfold a_cn bsCandNextBase; clear * - hdj' hoff' hb_cap; omega)
                (by unfold a_ch btSlotCandHeadBase; clear * - hp'_disj_tbl' hoff' hjs_lt; omega)
                (by unfold a_tf btSlotTouchedBase; clear * - hp'_disj_tbl' hoff' hjs_lt; omega)
          refine ⟨fun b' hb' => by
              have hs' := hblk_eq (3 + 3 * cap' + b') (by unfold bundleSlotBlockSize; omega)
              simp only [hvis_other j' b' (Or.inl hjj)]
              simpa [bsSeenBase, Nat.add_assoc] using hs'.trans (by simpa [bsSeenBase, Nat.add_assoc] using hj'.1 b' hb'),
            fun b' hb' => by
              have hi' := hblk_eq (3 + 4 * cap' + b') (by unfold bundleSlotBlockSize; omega)
              simpa [bsInCandBase, Nat.add_assoc] using hi'.trans (by simpa [bsInCandBase, Nat.add_assoc] using hj'.2.1 b' hb'),
            ?_,
            fun b' hb' hnot => by
              have hc' := hblk_eq (3 + 5 * cap' + b') (by unfold bundleSlotBlockSize; omega)
              simpa [bsCandNextBase, Nat.add_assoc] using hc'.trans (by simpa [bsCandNextBase, Nat.add_assoc] using hj'.2.2.2 b' hb' hnot)⟩
          obtain ⟨cL', hcL'_sll, hcL'_mem⟩ := hj'.2.2.1
          exact ⟨cL', hcL'_sll.of_agree hch_eq fun y hy => by
            have hylt := hcL'_sll.mem_lt y hy
            simpa [bsCandNextBase, Nat.add_assoc] using hblk_eq (3 + 5 * cap' + y) (by unfold bundleSlotBlockSize; omega),
            hcL'_mem⟩

/-- Converts `PassBMemInv` at `t = xs.length` back into full `BundleTableAfterScan` + `ListAt` + frame. -/
lemma passBMemInv_to_afterScan {slotCap vCap eCap tbl touchedBufPtr : ℕ}
    {S₀ : BundleTableState slotCap} {D : Finset ℕ} {m : BundleTableMeta slotCap}
    {cand₀ : Fin slotCap → Finset ℕ} {touched₀ touched_end : List ℕ} {xs : List End}
    {mem₀ mem_end : ℕ → ℕ}
    (htouch_disj_foot : ∀ a, touchedBufPtr ≤ a → a < touchedBufPtr + slotCap →
      ¬ bundleTableCoreFoot eCap tbl m a)
    (hafter₀ : BundleTableAfterScan slotCap vCap eCap tbl S₀ D m cand₀ touched₀ mem₀)
    (hInv : PassBMemInv vCap eCap tbl touchedBufPtr S₀ D m cand₀ xs mem₀ xs.length touched_end mem_end) :
    let S := tableDelEdges S₀ D
    BundleTableAfterScan slotCap vCap eCap tbl S₀ D m (passBCands S xs xs.length cand₀) touched_end mem_end ∧
    ListAt mem_end touchedBufPtr touched_end ∧
    (∀ a, ¬ bundleTableCoreFoot eCap tbl m a →
      (a < touchedBufPtr ∨ touchedBufPtr + slotCap ≤ a) → mem_end a = mem₀ a) := by
  intro S
  rcases hafter₀ with ⟨ar0, ar1, ar2, ar3, ar4, ar5, ar6, ar7, ar8, ar9, ar10, ar11,
    hdisjE, hedgeSlot, hendBun, hslots, hdisjB, _, _, _, hdelL₀, hdelN₀⟩
  rcases hInv with ⟨hfr_end, htnd_e, htlt_e, htflag_e, htouch_e, hdelT_e, hslotsT_e⟩
  have hnotB_fixed_ro : ∀ a, tbl ≤ a → a < tbl + bundleTableCoreSize slotCap eCap →
      (∀ s < slotCap, a ≠ btSlotCandHeadBase tbl slotCap eCap + s ∧
        a ≠ btSlotTouchedBase tbl slotCap eCap + s) →
      ¬ isPassBAddr eCap tbl touchedBufPtr m a := by
    intro a ha1 ha2 hns hB
    rcases hB with ⟨j, p, cap, b, hm, hb, hcase⟩ | ⟨s, hs, hcase⟩ | ⟨ht1, ht2⟩
    · have hj := hslots j
      cases hSj : tableDelEdges S₀ D j with
      | none => simp only [hSj, hm] at hj
      | some B =>
        simp only [hSj, hm] at hj
        have hdj : p + (3 + 6 * cap) ≤ tbl ∨ tbl + (14 + 7 * slotCap + 8 * eCap) ≤ p := hj.2.2
        unfold bundleTableCoreSize at ha2
        rcases hcase with rfl | rfl | rfl
        · unfold bsSeenBase at ha1 ha2; clear * - ha1 ha2 hdj hb; omega
        · unfold bsInCandBase at ha1 ha2; clear * - ha1 ha2 hdj hb; omega
        · unfold bsCandNextBase at ha1 ha2; clear * - ha1 ha2 hdj hb; omega
    · rcases hcase with rfl | rfl
      · exact (hns s hs).1 rfl
      · exact (hns s hs).2 rfl
    · exact htouch_disj_foot a ht1 ht2 (Or.inl ⟨ha1, ha2⟩)
  have hnotB_blk_ro : ∀ (j : Fin slotCap) p cap a, m.slotBlocks j = some (p, cap) →
      p ≤ a → a < p + 3 + 3 * cap → ¬ isPassBAddr eCap tbl touchedBufPtr m a := by
    intro j p cap a hm ha1 ha2 hB
    have hfoot_a : bundleTableCoreFoot eCap tbl m a := Or.inr ⟨j, p, cap, hm, ha1, by unfold bundleSlotBlockSize; omega⟩
    rcases hB with ⟨j', p', cap', b', hm', hb', hcase⟩ | ⟨s, hs, hcase⟩ | ⟨ht1, ht2⟩
    · by_cases hjj : j' = j
      · subst j'; rw [hm] at hm'; cases hm'
        rcases hcase with rfl | rfl | rfl
        · unfold bsSeenBase at ha1 ha2; omega
        · unfold bsInCandBase at ha1 ha2; omega
        · unfold bsCandNextBase at ha1 ha2; omega
      · have hdj := hdisjB j' j hjj p' cap' p cap hm' hm
        unfold bundleSlotBlockSize at hdj
        rcases hcase with rfl | rfl | rfl
        · unfold bsSeenBase at ha1 ha2; clear * - hdj ha1 ha2 hb'; omega
        · unfold bsInCandBase at ha1 ha2; clear * - hdj ha1 ha2 hb'; omega
        · unfold bsCandNextBase at ha1 ha2; clear * - hdj ha1 ha2 hb'; omega
    · have hj := hslots j
      cases hSj : tableDelEdges S₀ D j with
      | none => simp only [hSj, hm] at hj
      | some B =>
        simp only [hSj, hm] at hj
        have hdj : p + (3 + 6 * cap) ≤ tbl ∨ tbl + (14 + 7 * slotCap + 8 * eCap) ≤ p := hj.2.2
        rcases hcase with rfl | rfl
        · unfold btSlotCandHeadBase at ha1 ha2; clear * - hdj ha1 ha2 hs; omega
        · unfold btSlotTouchedBase at ha1 ha2; clear * - hdj ha1 ha2 hs; omega
    · exact htouch_disj_foot a ht1 ht2 hfoot_a
  have hnotB_out : ∀ a, ¬ bundleTableCoreFoot eCap tbl m a →
      (a < touchedBufPtr ∨ touchedBufPtr + slotCap ≤ a) → ¬ isPassBAddr eCap tbl touchedBufPtr m a := by
    intro a hnf hout hB
    rcases hB with ⟨j, p, cap, b, hm, hb, hcase⟩ | ⟨s, hs, hcase⟩ | ⟨ht1, ht2⟩
    · rcases hcase with rfl | rfl | rfl
      · exact hnf (block_addr_in_foot hm (by unfold bsSeenBase; omega) (by unfold bsSeenBase bundleSlotBlockSize; omega))
      · exact hnf (block_addr_in_foot hm (by unfold bsInCandBase; omega) (by unfold bsInCandBase bundleSlotBlockSize; omega))
      · exact hnf (block_addr_in_foot hm (by unfold bsCandNextBase; omega) (by unfold bsCandNextBase bundleSlotBlockSize; omega))
    · rcases hcase with rfl | rfl
      · exact hnf (Or.inl ⟨by unfold btSlotCandHeadBase; omega, by unfold btSlotCandHeadBase bundleTableCoreSize; omega⟩)
      · exact hnf (Or.inl ⟨by unfold btSlotTouchedBase; omega, by unfold btSlotTouchedBase bundleTableCoreSize; omega⟩)
    · omega
  have hhdr_e : ∀ off < 12, mem_end (tbl + off) = mem₀ (tbl + off) := fun off hoff =>
    hfr_end _ (hnotB_fixed_ro _ (by omega) (by unfold bundleTableCoreSize; omega)
      fun s _ => ⟨by unfold btSlotCandHeadBase; omega, by unfold btSlotTouchedBase; omega⟩)
  refine ⟨⟨(hhdr_e 0 (by decide)).trans ar0, (hhdr_e 1 (by decide)).trans ar1,
      (hhdr_e 2 (by decide)).trans ar2, (hhdr_e 3 (by decide)).trans ar3,
      (hhdr_e 4 (by decide)).trans ar4, (hhdr_e 5 (by decide)).trans ar5,
      (hhdr_e 6 (by decide)).trans ar6, (hhdr_e 7 (by decide)).trans ar7,
      (hhdr_e 8 (by decide)).trans ar8, (hhdr_e 9 (by decide)).trans ar9,
      (hhdr_e 10 (by decide)).trans ar10, (hhdr_e 11 (by decide)).trans ar11,
      hdisjE, ?_, ?_, ?_, hdisjB, htnd_e, htlt_e, htflag_e, ?_, ?_⟩,
    htouch_e, fun a hnf hout => hfr_end a (hnotB_out a hnf hout)⟩
  · intro e he
    rw [hfr_end _ (hnotB_fixed_ro _ (by unfold btEdgeSlotBase; omega)
      (by unfold btEdgeSlotBase bundleTableCoreSize; omega)
      fun s _ => ⟨by unfold btEdgeSlotBase btSlotCandHeadBase; omega,
        by unfold btEdgeSlotBase btSlotTouchedBase; omega⟩)]
    exact hedgeSlot e he
  · intro j B hSj x hx
    have hkx : endKey x < 2 * eCap := by
      have hj := hslots j
      have hSj' : tableDelEdges S₀ D j = some B := hSj
      simp only [hSj'] at hj
      cases hm : m.slotBlocks j with
      | none => simp only [hm] at hj
      | some pb =>
        simp only [hm] at hj; have he_lt := hj.2.1.choose_spec.2.2.1 x.1 ((mem_edgeEnds _ _).mp hx)
        rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
    rw [hfr_end _ (hnotB_fixed_ro _ (by unfold btEndBundleBase; omega)
      (by unfold btEndBundleBase bundleTableCoreSize; omega)
      fun s _ => ⟨by unfold btEndBundleBase btSlotCandHeadBase; omega,
        by unfold btEndBundleBase btSlotTouchedBase; omega⟩)]
    exact hendBun j B hSj x hx
  · intro j
    have hj_lt : j.1 < slotCap := j.2
    have hptr_e : mem_end (btSlotPtrBase tbl + j.1) = mem₀ (btSlotPtrBase tbl + j.1) :=
      hfr_end _ (hnotB_fixed_ro _ (by unfold btSlotPtrBase; omega)
        (by unfold btSlotPtrBase bundleTableCoreSize; clear * - hj_lt; omega)
        fun s _ => ⟨by unfold btSlotPtrBase btSlotCandHeadBase; clear * - hj_lt; omega,
          by unfold btSlotPtrBase btSlotTouchedBase; clear * - hj_lt; omega⟩)
    have hj0 := hslots j; have hjT := hslotsT_e j
    cases hSj : tableDelEdges S₀ D j with
    | none =>
      simp only [S, hSj] at hj0 hjT ⊢
      cases hm : m.slotBlocks j with
      | none =>
        simp only [hm] at hj0 hjT ⊢
        exact ⟨hptr_e.trans hj0.1, hjT, by simp [passBCands, hSj, hj0.2.2]⟩
      | some _ => simp only [hm] at hj0
    | some B =>
      simp only [S, hSj] at hj0 hjT ⊢
      cases hm : m.slotBlocks j with
      | none => simp only [hm] at hj0
      | some pb =>
        rcases pb with ⟨p, cap⟩; simp only [hm] at hj0 hjT ⊢
        obtain ⟨hptr0, ⟨nB, hV, hnB, hE, hbo, hpar0, h0, h1, h2, hdll, hpar, htail, _, _, hc0_lt, _, _⟩, hdj⟩ := hj0
        have hblk_ro : ∀ off < 3 + 3 * cap, mem_end (p + off) = mem₀ (p + off) := fun off hoff =>
          hfr_end _ (hnotB_blk_ro j p cap _ hm (by omega) (by omega))
        have hprev_e : ∀ k < 2 * eCap, mem_end (btEndPrevBase tbl slotCap eCap + k) =
            mem₀ (btEndPrevBase tbl slotCap eCap + k) := fun k hk =>
          hfr_end _ (hnotB_fixed_ro _ (by unfold btEndPrevBase; omega)
            (by unfold btEndPrevBase bundleTableCoreSize; omega)
            fun s _ => ⟨by unfold btEndPrevBase btSlotCandHeadBase; omega,
              by unfold btEndPrevBase btSlotTouchedBase; omega⟩)
        have hnext_e : ∀ k < 2 * eCap, mem_end (btEndNextBase tbl slotCap eCap + k) =
            mem₀ (btEndNextBase tbl slotCap eCap + k) := fun k hk =>
          hfr_end _ (hnotB_fixed_ro _ (by unfold btEndNextBase; omega)
            (by unfold btEndNextBase bundleTableCoreSize; omega)
            fun s _ => ⟨by unfold btEndNextBase btSlotCandHeadBase; omega,
              by unfold btEndNextBase btSlotTouchedBase; omega⟩)
        refine ⟨hptr_e.trans hptr0, ⟨nB, hV, hnB, hE, hbo, hpar0,
          (hblk_ro bsOffBunCap (by unfold bsOffBunCap; omega)).trans h0,
          (hblk_ro bsOffNB (by unfold bsOffNB; omega)).trans h1,
          (hblk_ro bsOffNE (by unfold bsOffNE; omega)).trans h2,
          fun b hb => ?_, fun b hb hem => ?_, fun b hge hlt => ?_,
          fun b hb => ?_, hjT.2.1, fun b hb => ?_, hjT.2.2.1, hjT.2.2.2⟩, hdj⟩
        · obtain ⟨L, hL, hsz, hmem⟩ := hdll b hb
          have hb_cap : b < cap := lt_of_lt_of_le hb hnB
          have hhd := hblk_ro (3 + b) (by omega)
          have hsz' := hblk_ro (3 + cap + b) (by omega)
          exact ⟨L, hL.of_agree (by simpa [bsHeadBase, Nat.add_assoc] using hhd)
            (fun k hk => hprev_e k (hL.2.1 k hk)) (fun k hk => hnext_e k (hL.2.1 k hk)),
            by simpa [bsSizeBase, Nat.add_assoc] using hsz'.trans (by simpa [bsSizeBase, Nat.add_assoc] using hsz),
            hmem⟩
        · have hb_cap : b < cap := lt_of_lt_of_le hb hnB
          have hpa := hblk_ro (3 + 2 * cap + b) (by omega)
          simpa [bsParentBase, Nat.add_assoc] using hpa.trans (by simpa [bsParentBase, Nat.add_assoc] using hpar b hb hem)
        · obtain ⟨t1, t2, t3⟩ := htail b hge hlt
          have ht1 := hblk_ro (3 + b) (by omega)
          have ht2 := hblk_ro (3 + cap + b) (by omega)
          have ht3 := hblk_ro (3 + 2 * cap + b) (by omega)
          exact ⟨by simpa [bsHeadBase, Nat.add_assoc] using ht1.trans (by simpa [bsHeadBase, Nat.add_assoc] using t1),
            by simpa [bsSizeBase, Nat.add_assoc] using ht2.trans (by simpa [bsSizeBase, Nat.add_assoc] using t2),
            by simpa [bsParentBase, Nat.add_assoc] using ht3.trans (by simpa [bsParentBase, Nat.add_assoc] using t3)⟩
        · rw [hjT.1 b hb]
          split_ifs with hv
          · rfl
          · exact seenCount_eq_zero_of_not_visited hv
        · simp only [passBCands, hSj, Finset.mem_union, Finset.mem_filter] at hb
          rcases hb with h0 | ⟨hbV, _⟩
          · exact hc0_lt b h0
          · exact Finset.mem_range.mp (hV ▸ hbV)
  · intro j; have hj0 := hdelL₀ j; have hjT := hdelT_e j
    have hj_lt : j.1 < slotCap := j.2
    have hdh_e : mem_end (btSlotDelHeadBase tbl slotCap eCap + j.1) = mem₀ (btSlotDelHeadBase tbl slotCap eCap + j.1) :=
      hfr_end _ (hnotB_fixed_ro _ (by unfold btSlotDelHeadBase; omega)
        (by unfold btSlotDelHeadBase bundleTableCoreSize; clear * - hj_lt; omega)
        fun s hs => ⟨by unfold btSlotDelHeadBase btSlotCandHeadBase; clear * - hj_lt hs; omega,
          by unfold btSlotDelHeadBase btSlotTouchedBase; clear * - hj_lt hs; omega⟩)
    cases hSj : S₀ j with
    | none => rw [hSj] at hj0 hjT; exact ⟨hdh_e.trans hj0.1, hjT⟩
    | some B₀ =>
      rw [hSj] at hj0 hjT
      obtain ⟨_, dL, hdL_sll, hdL_mem⟩ := hj0
      exact ⟨hjT, dL, hdL_sll.of_agree hdh_e fun y hy =>
        hfr_end _ (hnotB_fixed_ro _ (by unfold btSlotDelNextBase; omega)
          (by unfold btSlotDelNextBase bundleTableCoreSize; have := hdL_sll.mem_lt y hy; omega)
          fun s _ => ⟨by unfold btSlotDelNextBase btSlotCandHeadBase; have := hdL_sll.mem_lt y hy; omega,
            by unfold btSlotDelNextBase btSlotTouchedBase; have := hdL_sll.mem_lt y hy; omega⟩),
        hdL_mem⟩
  · intro e he hnot
    rw [hfr_end _ (hnotB_fixed_ro _ (by unfold btSlotDelNextBase; omega)
      (by unfold btSlotDelNextBase bundleTableCoreSize; omega)
      fun s _ => ⟨by unfold btSlotDelNextBase btSlotCandHeadBase; omega,
        by unfold btSlotDelNextBase btSlotTouchedBase; omega⟩)]
    exact hdelN₀ e he hnot

end

end MinCostFlow.SparseCore.Program
