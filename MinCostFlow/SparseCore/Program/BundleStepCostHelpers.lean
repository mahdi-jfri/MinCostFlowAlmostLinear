module

public import MinCostFlow.SparseCore.Program.BundleStepDefs

/-!
# Scanned-end cap comparison, Phase 3 cost absorption, and step loop helpers (`BundleStepCostHelpers`)

Provides helper lemmas used by `BundleStepMain`:
* `slotScannedEnds_le_slotCandEndsSum`, `slotScannedEnds_le_totalNonMaxLen`: connect
  `slotScannedEnds` to `slotCandEndsSum` and `totalNonMaxLen`.
* `sum_slotDelCnt_le_card`, `touched_len_le_delCount_add_totalNonMaxLen`,
  `bundleStepEmitTotalCost_le_absorbed`, `bundleStep_cost_combine`: absorb all Phase 3 scanned-end,
  candidate-sorting, and per-touched-slot work into `bundleStepCost TS eCap delCount gs +
  bundleScanPotMul TS eCap * totalNonMaxLen`.
* `scanEnds_nil_of_not_touched`, `readGroups_agree_outside_foot`, `bundleStep_curScan_step`:
  invariant preservation helpers for `bundleStep_runs`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner
open MinCostFlow.DynSpanner.Program

public section

/-- `slotScannedEnds` is bounded by `slotCandEndsSum` (so any headroom invariant bounding
`B₀.vertices.card + slotCandEndsSum ≤ bunCap` immediately discharges the weaker `hcap_ok`). -/
lemma slotScannedEnds_le_slotCandEndsSum {slotCap : ℕ} {S₀ : BundleTableState slotCap}
    {D : Finset ℕ} {j : Fin slotCap} {B₀ : BundleState} {cord' : ℕ → List End}
    {src' : End → ℕ} {gs : List (List ℕ)} {maxIdxs : List ℕ}
    (hS₀j : S₀ j = some B₀)
    (hval : ScanValidForSlot { B₀ with edges := B₀.edges \ D } src'
      (addCandsForGroups (tableDelEdges S₀ D) cord' gs maxIdxs (fun _ => ∅) gs.length j)
      (addScanEndsForGroups (tableDelEdges S₀ D) cord' gs maxIdxs (fun _ => ∅) (fun _ => [])
        gs.length j)) :
    slotScannedEnds S₀ D cord' gs maxIdxs j ≤
      slotCandEndsSum S₀ D
        (addCandsForGroups (tableDelEdges S₀ D) cord' gs maxIdxs (fun _ => ∅) gs.length) j := by
  unfold slotScannedEnds slotCandEndsSum
  rw [hS₀j]
  exact scanValidForSlot_len_le_candEndsSum hval

/-- `slotScannedEnds` for any single slot is bounded by `totalNonMaxLen`. -/
lemma slotScannedEnds_le_totalNonMaxLen {slotCap : ℕ} {S₀ : BundleTableState slotCap}
    {D : Finset ℕ}
    (hdisj₀ : ∀ j₁ j₂ : Fin slotCap, j₁ ≠ j₂ → ∀ B₁ B₂,
      S₀ j₁ = some B₁ → S₀ j₂ = some B₂ → Disjoint B₁.edges B₂.edges)
    (cord' : ℕ → List End) (gs : List (List ℕ)) (maxIdxs : List ℕ) (j : Fin slotCap) :
    slotScannedEnds S₀ D cord' gs maxIdxs j ≤ totalNonMaxLen cord' gs maxIdxs := by
  have hsum := addScanEndsForGroups_sum_le (D := D) hdisj₀ cord' gs maxIdxs (fun _ => ∅)
  have hle : slotScannedEnds S₀ D cord' gs maxIdxs j ≤
      ∑ i : Fin slotCap,
        (addScanEndsForGroups (tableDelEdges S₀ D) cord' gs maxIdxs (fun _ => ∅) (fun _ => [])
          gs.length i).length :=
    Finset.single_le_sum (f := fun i : Fin slotCap =>
      (addScanEndsForGroups (tableDelEdges S₀ D) cord' gs maxIdxs (fun _ => ∅) (fun _ => [])
        gs.length i).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  exact hle.trans hsum

private lemma touched_map_sum_le_fin_sum {slotCap : ℕ} (f : Fin slotCap → ℕ)
    {touched : List ℕ} (hnd : touched.Nodup) (hlt : ∀ s ∈ touched, s < slotCap) :
    (touched.map fun s => if hs : s < slotCap then f ⟨s, hs⟩ else 0).sum ≤
      ∑ j : Fin slotCap, f j := by
  have hgo : ∀ (l : List ℕ), l.Nodup → (∀ s ∈ l, s < slotCap) →
      (l.map fun s => if hs : s < slotCap then f ⟨s, hs⟩ else 0).sum =
        ∑ j ∈ (Finset.univ.filter fun j : Fin slotCap => j.1 ∈ l), f j := by
    intro l
    induction l with
    | nil => intro _ _; simp
    | cons a tl ih =>
      intro hnd' hlt'
      obtain ⟨ha_not, htl_nd⟩ := List.nodup_cons.mp hnd'
      have ha_lt : a < slotCap := hlt' a List.mem_cons_self
      set ja : Fin slotCap := ⟨a, ha_lt⟩
      have hfilt : (Finset.univ.filter fun j : Fin slotCap => j.1 ∈ a :: tl) =
          insert ja (Finset.univ.filter fun j : Fin slotCap => j.1 ∈ tl) := by
        ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons,
          Finset.mem_insert, Fin.ext_iff, ja]
      have hnot_in : ja ∉ Finset.univ.filter (fun j : Fin slotCap => j.1 ∈ tl) := by
        simp [ja, ha_not]
      rw [List.map_cons, List.sum_cons, dite_eq_left ha_lt, hfilt, Finset.sum_insert hnot_in,
        ih htl_nd (fun s hs => hlt' s (List.mem_cons_of_mem _ hs))]
  rw [hgo touched hnd hlt]
  exact Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _

lemma sum_slotDelCnt_le_card {slotCap : ℕ} {S₀ : BundleTableState slotCap} {D : Finset ℕ}
    (hdisj₀ : ∀ j₁ j₂ : Fin slotCap, j₁ ≠ j₂ → ∀ B₁ B₂,
      S₀ j₁ = some B₁ → S₀ j₂ = some B₂ → Disjoint B₁.edges B₂.edges) :
    (∑ j : Fin slotCap, slotDelCnt S₀ D j) ≤ D.card := by
  classical
  let sets : Fin slotCap → Finset ℕ := fun j =>
    match S₀ j with
    | none => ∅
    | some B₀ => B₀.edges ∩ D
  have hcard : ∀ j : Fin slotCap, slotDelCnt S₀ D j = (sets j).card := fun j => by
    unfold slotDelCnt sets; cases S₀ j <;> simp
  simp_rw [hcard]
  have hpwd : (↑(Finset.univ : Finset (Fin slotCap)) : Set (Fin slotCap)).PairwiseDisjoint sets := by
    intro j₁ _ j₂ _ hne
    simp only [Function.onFun, sets]
    cases h1 : S₀ j₁ with
    | none => simp
    | some B₁ =>
      cases h2 : S₀ j₂ with
      | none => simp
      | some B₂ =>
        exact (hdisj₀ j₁ j₂ hne B₁ B₂ h1 h2).mono Finset.inter_subset_left Finset.inter_subset_left
  rw [← Finset.card_biUnion hpwd]
  refine Finset.card_le_card fun e he => ?_
  obtain ⟨j, _, hej⟩ := Finset.mem_biUnion.mp he
  dsimp only [sets] at hej
  cases hS : S₀ j with
  | none => rw [hS] at hej; exact False.elim (Finset.notMem_empty _ hej)
  | some B₀ => rw [hS] at hej; exact (Finset.mem_inter.mp hej).2

/-- Every touched slot has either a deleted edge or a scanned candidate end, so
`touched.length ≤ delCount + totalNonMaxLen`. -/
lemma touched_len_le_delCount_add_totalNonMaxLen {slotCap delCount : ℕ}
    {S₀ : BundleTableState slotCap} {D : Finset ℕ} {cord' : ℕ → List End}
    {gs : List (List ℕ)} {maxIdxs touched : List ℕ}
    (hdisj₀ : ∀ j₁ j₂ : Fin slotCap, j₁ ≠ j₂ → ∀ B₁ B₂,
      S₀ j₁ = some B₁ → S₀ j₂ = some B₂ → Disjoint B₁.edges B₂.edges)
    (hD_le : D.card ≤ delCount)
    (hnd : touched.Nodup) (hlt : ∀ s ∈ touched, s < slotCap)
    (htouch_ne : ∀ s ∈ touched, ∀ (hs : s < slotCap),
      0 < slotDelCnt S₀ D ⟨s, hs⟩ ∨
        0 < slotScannedEnds S₀ D cord' gs maxIdxs ⟨s, hs⟩) :
    touched.length ≤ delCount + totalNonMaxLen cord' gs maxIdxs := by
  have h1 : touched.length ≤
      (touched.map fun s => if hs : s < slotCap then
        slotDelCnt S₀ D ⟨s, hs⟩ + slotScannedEnds S₀ D cord' gs maxIdxs ⟨s, hs⟩
      else 0).sum := by
    have hgo : ∀ l : List ℕ, (∀ s ∈ l, ∀ (hs : s < slotCap),
        0 < slotDelCnt S₀ D ⟨s, hs⟩ ∨ 0 < slotScannedEnds S₀ D cord' gs maxIdxs ⟨s, hs⟩) →
        (∀ s ∈ l, s < slotCap) →
        l.length ≤ (l.map fun s => if hs : s < slotCap then
          slotDelCnt S₀ D ⟨s, hs⟩ + slotScannedEnds S₀ D cord' gs maxIdxs ⟨s, hs⟩
        else 0).sum := by
      intro l; induction l with
      | nil => intro _ _; simp
      | cons a tl ih =>
        intro hne' hlt'
        have ha_lt := hlt' a List.mem_cons_self
        have ha_pos := hne' a List.mem_cons_self ha_lt
        have htl := ih (fun s hs => hne' s (List.mem_cons_of_mem _ hs))
          (fun s hs => hlt' s (List.mem_cons_of_mem _ hs))
        simp only [List.length_cons, List.map_cons, List.sum_cons, dite_eq_left ha_lt]
        omega
    exact hgo touched htouch_ne hlt
  have h2 := touched_map_sum_le_fin_sum
    (fun j : Fin slotCap => slotDelCnt S₀ D j + slotScannedEnds S₀ D cord' gs maxIdxs j) hnd hlt
  rw [Finset.sum_add_distrib] at h2
  have hdel := (sum_slotDelCnt_le_card hdisj₀).trans hD_le
  have hscan := addScanEndsForGroups_sum_le (D := D) hdisj₀ cord' gs maxIdxs (fun _ => ∅)
  change (∑ j : Fin slotCap, slotScannedEnds S₀ D cord' gs maxIdxs j) ≤
    totalNonMaxLen cord' gs maxIdxs at hscan
  omega

/-- Absorbs all Phase 3 scanned-end and candidate-sorting costs across touched slots into
`300 * delCount * (log(delCount+1)+1) + 550 * touched.length +
 ((2 * TS.mul + 900) * ordStoreLog eCap + 3350) * totalNonMaxLen`. -/
lemma bundleStepEmitTotalCost_le_absorbed {TS : BundleTourSpec} {eCap slotCap delCount : ℕ}
    {S₀ : BundleTableState slotCap} {D : Finset ℕ} {cord' : ℕ → List End}
    {gs : List (List ℕ)} {maxIdxs touched : List ℕ}
    (hdisj₀ : ∀ j₁ j₂ : Fin slotCap, j₁ ≠ j₂ → ∀ B₁ B₂,
      S₀ j₁ = some B₁ → S₀ j₂ = some B₂ → Disjoint B₁.edges B₂.edges)
    (hD_le : D.card ≤ delCount)
    (hnd : touched.Nodup) (hlt : ∀ s ∈ touched, s < slotCap)
    (hcand_le : ∀ s ∈ touched, ∀ (hs : s < slotCap),
      slotCandCnt (addCandsForGroups (tableDelEdges S₀ D) cord' gs maxIdxs (fun _ => ∅) gs.length)
        ⟨s, hs⟩ ≤ slotScannedEnds S₀ D cord' gs maxIdxs ⟨s, hs⟩)
    (hscan_le_2e : ∀ s ∈ touched, ∀ (hs : s < slotCap),
      slotScannedEnds S₀ D cord' gs maxIdxs ⟨s, hs⟩ ≤ 2 * eCap) :
    let candSet := addCandsForGroups (tableDelEdges S₀ D) cord' gs maxIdxs (fun _ => ∅) gs.length
    let scanLen := slotScannedEnds S₀ D cord' gs maxIdxs
    bundleStepEmitTotalCost TS eCap S₀ D candSet scanLen touched ≤
      300 * delCount * (Nat.log 2 (delCount + 1) + 1) + 550 * touched.length +
      ((2 * TS.mul + 900) * ordStoreLog eCap + 3350) * totalNonMaxLen cord' gs maxIdxs := by
  intro candSet scanLen
  set Ldel := Nat.log 2 (delCount + 1) + 1
  set K := (2 * TS.mul + 900) * ordStoreLog eCap + 3350
  have hslot_le : ∀ s ∈ touched, ∀ (hs : s < slotCap),
      bundleStepEmitSlotCost TS eCap (slotDelCnt S₀ D ⟨s, hs⟩) (slotCandCnt candSet ⟨s, hs⟩)
        (scanLen ⟨s, hs⟩) ≤
      300 * Ldel * slotDelCnt S₀ D ⟨s, hs⟩ + K * scanLen ⟨s, hs⟩ + 550 := by
    intro s hs_in hs
    set d := slotDelCnt S₀ D ⟨s, hs⟩
    set c := slotCandCnt candSet ⟨s, hs⟩
    set M := scanLen ⟨s, hs⟩
    have hd_le_del : d ≤ delCount := by
      have h1 : d ≤ ∑ j : Fin slotCap, slotDelCnt S₀ D j :=
        Finset.single_le_sum (f := slotDelCnt S₀ D) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
      exact h1.trans ((sum_slotDelCnt_le_card hdisj₀).trans hD_le)
    have hlog_d : Nat.log 2 (d + 1) + 1 ≤ Ldel :=
      Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1
    have hterm_d : 300 * d * (Nat.log 2 (d + 1) + 1) ≤ 300 * Ldel * d := by
      calc 300 * d * (Nat.log 2 (d + 1) + 1) ≤ 300 * d * Ldel := Nat.mul_le_mul_left _ hlog_d
        _ = 300 * Ldel * d := by ring
    have hc_le_M : c ≤ M := hcand_le s hs_in hs
    have hM_le_2e : M ≤ 2 * eCap := hscan_le_2e s hs_in hs
    have hlog_c : Nat.log 2 (c + 1) + 1 ≤ ordStoreLog eCap + 2 :=
      nat_log_le_ordStoreLog (hc_le_M.trans hM_le_2e)
    have hlog_M : Nat.log 2 (2 * M + 1) + 1 ≤ ordStoreLog eCap + 2 :=
      nat_log_two_mul_le_ordStoreLog hM_le_2e
    have hterm_c : 300 * c * (Nat.log 2 (c + 1) + 1) ≤ (300 * ordStoreLog eCap + 600) * M := by
      calc 300 * c * (Nat.log 2 (c + 1) + 1)
          ≤ 300 * M * (ordStoreLog eCap + 2) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hc_le_M) hlog_c
        _ = (300 * ordStoreLog eCap + 600) * M := by ring
    have hterm_c500 : 500 * c ≤ 500 * M := Nat.mul_le_mul_left 500 hc_le_M
    have hterm_M : (2 * TS.mul * ordStoreLog eCap + 600 * (Nat.log 2 (2 * M + 1) + 1) + 1050) * M ≤
        ((2 * TS.mul + 600) * ordStoreLog eCap + 2250) * M := by
      calc (2 * TS.mul * ordStoreLog eCap + 600 * (Nat.log 2 (2 * M + 1) + 1) + 1050) * M
          ≤ (2 * TS.mul * ordStoreLog eCap + 600 * (ordStoreLog eCap + 2) + 1050) * M :=
            Nat.mul_le_mul_right M (by omega)
        _ = ((2 * TS.mul + 600) * ordStoreLog eCap + 2250) * M := by ring
    have hK_split : K * M =
        (300 * ordStoreLog eCap + 600) * M + 500 * M +
        ((2 * TS.mul + 600) * ordStoreLog eCap + 2250) * M := by
      dsimp only [K]; ring
    unfold bundleStepEmitSlotCost
    change 300 * d * (Nat.log 2 (d + 1) + 1) + 300 * c * (Nat.log 2 (c + 1) + 1) +
        (2 * TS.mul * ordStoreLog eCap + 600 * (Nat.log 2 (2 * M + 1) + 1) + 1050) * M +
        500 * c + 550 ≤ 300 * Ldel * d + K * M + 550
    omega
  have hsum_le : bundleStepEmitTotalCost TS eCap S₀ D candSet scanLen touched ≤
      (touched.map fun s => if hs : s < slotCap then
        300 * Ldel * slotDelCnt S₀ D ⟨s, hs⟩ + K * scanLen ⟨s, hs⟩
      else 0).sum + 550 * touched.length := by
    have hgo : ∀ l : List ℕ, (∀ s ∈ l, ∀ (hs : s < slotCap),
        bundleStepEmitSlotCost TS eCap (slotDelCnt S₀ D ⟨s, hs⟩) (slotCandCnt candSet ⟨s, hs⟩)
          (scanLen ⟨s, hs⟩) ≤
        300 * Ldel * slotDelCnt S₀ D ⟨s, hs⟩ + K * scanLen ⟨s, hs⟩ + 550) →
        bundleStepEmitTotalCost TS eCap S₀ D candSet scanLen l ≤
        (l.map fun s => if hs : s < slotCap then
          300 * Ldel * slotDelCnt S₀ D ⟨s, hs⟩ + K * scanLen ⟨s, hs⟩
        else 0).sum + 550 * l.length := by
      intro l; induction l with
      | nil => intro _; simp [bundleStepEmitTotalCost]
      | cons a tl ih =>
        intro hpt
        unfold bundleStepEmitTotalCost at ih ⊢
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        have htl := ih fun s hs => hpt s (List.mem_cons_of_mem _ hs)
        by_cases ha : a < slotCap
        · simp only [ha, ↓reduceDIte]
          have h1 := hpt a List.mem_cons_self ha
          omega
        · simp only [ha, ↓reduceDIte]; omega
    exact hgo touched hslot_le
  have hfin := touched_map_sum_le_fin_sum
    (fun j : Fin slotCap => 300 * Ldel * slotDelCnt S₀ D j + K * scanLen j) hnd hlt
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hfin
  have hdel_mul : 300 * Ldel * (∑ j : Fin slotCap, slotDelCnt S₀ D j) ≤ 300 * delCount * Ldel := by
    calc 300 * Ldel * (∑ j : Fin slotCap, slotDelCnt S₀ D j)
        ≤ 300 * Ldel * delCount := Nat.mul_le_mul_left _ ((sum_slotDelCnt_le_card hdisj₀).trans hD_le)
      _ = 300 * delCount * Ldel := by ring
  have hscan_mul : K * (∑ j : Fin slotCap, scanLen j) ≤ K * totalNonMaxLen cord' gs maxIdxs :=
    Nat.mul_le_mul_left K (addScanEndsForGroups_sum_le (D := D) hdisj₀ cord' gs maxIdxs (fun _ => ∅))
  omega

/-- Combines Phase 1, Phase 2, and Phase 3 costs into `bundleStepCost TS eCap delCount gs +
bundleScanPotMul TS eCap * totalNonMaxLen`. -/
lemma bundleStep_cost_combine {TS : BundleTourSpec} {eCap slotCap vCap tbl delCount cD cS cE
    phi₀ phiS phiE : ℕ}
    {S₀ : BundleTableState slotCap} {D : Finset ℕ} {m : BundleTableMeta slotCap}
    {cord' : ℕ → List End} {src' : End → ℕ} {gs : List (List ℕ)} {maxIdxs touched : List ℕ}
    {mem₀ memS : ℕ → ℕ}
    (hrep0 : BundleTableRepAt slotCap vCap eCap tbl S₀ m mem₀)
    (hafterS : BundleTableAfterScan slotCap vCap eCap tbl S₀ D m
      (addCandsForGroups (tableDelEdges S₀ D) cord' gs maxIdxs (fun _ => ∅) gs.length) touched memS)
    (hD_le : D.card ≤ delCount)
    (hval_all : ∀ j B₀, S₀ j = some B₀ →
      ScanValidForSlot { B₀ with edges := B₀.edges \ D } src'
        (addCandsForGroups (tableDelEdges S₀ D) cord' gs maxIdxs (fun _ => ∅) gs.length j)
        (addScanEndsForGroups (tableDelEdges S₀ D) cord' gs maxIdxs (fun _ => ∅) (fun _ => [])
          gs.length j) ∧
      (∀ b ∈ addCandsForGroups (tableDelEdges S₀ D) cord' gs maxIdxs (fun _ => ∅) gs.length j,
        ∃ t ∈ addScanEndsForGroups (tableDelEdges S₀ D) cord' gs maxIdxs (fun _ => ∅) (fun _ => [])
          gs.length j, t.1 = b) ∧
      (addCandsForGroups (tableDelEdges S₀ D) cord' gs maxIdxs (fun _ => ∅) gs.length j).card ≤
        (addScanEndsForGroups (tableDelEdges S₀ D) cord' gs maxIdxs (fun _ => ∅) (fun _ => [])
          gs.length j).length)
    (hcD : cD ≤ 398 * delCount + 65)
    (hcS : cS + phiS ≤ bundleStepScanCost TS eCap gs +
      (TS.mul * ordStoreLog eCap + 360) * totalNonMaxLen cord' gs maxIdxs + phi₀)
    (hcE : cE + phiE ≤
      bundleStepEmitTotalCost TS eCap S₀ D
        (addCandsForGroups (tableDelEdges S₀ D) cord' gs maxIdxs (fun _ => ∅) gs.length)
        (slotScannedEnds S₀ D cord' gs maxIdxs) touched +
      44 * touched.length + 7 + phiS) :
    3 + (9 + (4 + (2 + (cD + 5 + (3 + (cS + 8 + (3 + (3 + (cE + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1 +
      70 * touched.length + phiE ≤
      bundleStepCost TS eCap delCount gs +
      bundleScanPotMul TS eCap * totalNonMaxLen cord' gs maxIdxs + phi₀ := by
  have hdisj₀ := hrep0.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hndT := hafterS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hltT := hafterS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hslot_some : ∀ s ∈ touched, ∀ (hs : s < slotCap), ∃ B₀, S₀ ⟨s, hs⟩ = some B₀ := by
    intro s hsm hs
    have hdj := hafterS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ⟨s, hs⟩
    cases hS0 : S₀ ⟨s, hs⟩ with
    | none => rw [hS0] at hdj; exact False.elim (hdj.2 hsm)
    | some B₀ => exact ⟨B₀, rfl⟩
  have htouch_le := touched_len_le_delCount_add_totalNonMaxLen (cord' := cord') (gs := gs)
    (maxIdxs := maxIdxs) hdisj₀ hD_le hndT hltT fun s hsm hs => by
      obtain ⟨B₀, hS0⟩ := hslot_some s hsm hs
      have hdj := hafterS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ⟨s, hs⟩
      rw [hS0] at hdj
      rcases hdj.1.mp hsm with hDne | hCne
      · left; simp [slotDelCnt, hS0, Finset.card_pos.mpr hDne]
      · right
        have h1 := (hval_all ⟨s, hs⟩ B₀ hS0).2.2
        have h2 := Finset.card_pos.mpr hCne
        unfold slotScannedEnds; omega
  have hemit_abs := bundleStepEmitTotalCost_le_absorbed (TS := TS) (eCap := eCap) (cord' := cord')
    (gs := gs) (maxIdxs := maxIdxs) hdisj₀ hD_le hndT hltT
    (fun s hsm hs => by obtain ⟨B₀, hS0⟩ := hslot_some s hsm hs; exact (hval_all ⟨s, hs⟩ B₀ hS0).2.2)
    (fun s hsm hs => by
      obtain ⟨B₀, hS0⟩ := hslot_some s hsm hs
      have hE_lt : ∀ e ∈ B₀.edges \ D, e < eCap := fun e he => by
        have hsj := hrep0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ⟨s, hs⟩
        rw [hS0] at hsj
        cases hm : m.slotBlocks ⟨s, hs⟩ with
        | none => rw [hm] at hsj; exact False.elim hsj
        | some pb => rw [hm] at hsj; exact hsj.2.1.choose_spec.2.2.1 e (Finset.mem_sdiff.mp he).1
      exact scanValidForSlot_len_le_two_eCap (hval_all ⟨s, hs⟩ B₀ hS0).1 hE_lt)
  have hmul_pot : (TS.mul * ordStoreLog eCap + 360) * totalNonMaxLen cord' gs maxIdxs +
      ((2 * TS.mul + 900) * ordStoreLog eCap + 3350) * totalNonMaxLen cord' gs maxIdxs +
      664 * totalNonMaxLen cord' gs maxIdxs ≤
      bundleScanPotMul TS eCap * totalNonMaxLen cord' gs maxIdxs := by
    have h1 : (TS.mul * ordStoreLog eCap + 360) * totalNonMaxLen cord' gs maxIdxs +
        ((2 * TS.mul + 900) * ordStoreLog eCap + 3350) * totalNonMaxLen cord' gs maxIdxs +
        664 * totalNonMaxLen cord' gs maxIdxs =
        ((3 * TS.mul + 900) * ordStoreLog eCap + 4374) * totalNonMaxLen cord' gs maxIdxs := by ring
    rw [h1]; unfold bundleScanPotMul; exact Nat.mul_le_mul_right _ (by omega)
  unfold bundleStepCost; clear * - hcD hcS hcE htouch_le hemit_abs hmul_pot; omega

/-- Untouched slots have empty scanned-end lists after Phase 2. -/
lemma scanEnds_nil_of_not_touched {slotCap vCap eCap tbl : ℕ}
    {S₀ : BundleTableState slotCap} {D : Finset ℕ} {m : BundleTableMeta slotCap}
    {cord' : ℕ → List End} {src' : End → ℕ} {gs : List (List ℕ)} {maxIdxs touched : List ℕ}
    {memS : ℕ → ℕ}
    (hafterS : BundleTableAfterScan slotCap vCap eCap tbl S₀ D m
      (addCandsForGroups (tableDelEdges S₀ D) cord' gs maxIdxs (fun _ => ∅) gs.length) touched memS)
    (hval_all : ∀ j B₀, S₀ j = some B₀ →
      ScanValidForSlot { B₀ with edges := B₀.edges \ D } src'
        (addCandsForGroups (tableDelEdges S₀ D) cord' gs maxIdxs (fun _ => ∅) gs.length j)
        (addScanEndsForGroups (tableDelEdges S₀ D) cord' gs maxIdxs (fun _ => ∅) (fun _ => [])
          gs.length j))
    {s : ℕ} (hs : s < slotCap) (hnot : s ∉ touched) :
    addScanEndsForGroups (tableDelEdges S₀ D) cord' gs maxIdxs (fun _ => ∅) (fun _ => [])
      gs.length ⟨s, hs⟩ = [] := by
  cases hEq : addScanEndsForGroups (tableDelEdges S₀ D) cord' gs maxIdxs (fun _ => ∅) (fun _ => [])
      gs.length ⟨s, hs⟩ with
  | nil => rfl
  | cons t rest =>
    exfalso
    have ht_mem : t ∈ addScanEndsForGroups (tableDelEdges S₀ D) cord' gs maxIdxs (fun _ => ∅) (fun _ => [])
        gs.length ⟨s, hs⟩ := hEq ▸ List.mem_cons_self
    have hdj := hafterS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ⟨s, hs⟩
    cases hS0 : S₀ ⟨s, hs⟩ with
    | none =>
      rcases t with ⟨b, w', k⟩
      obtain ⟨B', hSj', _⟩ := (addScanEndsForGroups_mem_iff gs.length (le_refl _)).mp ht_mem
      simp [tableDelEdges, hS0] at hSj'
    | some B₀ =>
      have htb := ((hval_all ⟨s, hs⟩ B₀ hS0).2.1 t ht_mem).1
      rw [hS0] at hdj
      exact hnot (hdj.1.mpr (Or.inr ⟨t.1, htb⟩))

/-- `readGroups` is unchanged whenever memory agrees outside `bundleTableFoot`. -/
lemma readGroups_agree_outside_foot {slotCap eCap tbl : ℕ} {m : BundleTableMeta slotCap}
    {mem₀ mem₁ : ℕ → ℕ} {ptr g : ℕ}
    (hagree : ∀ a, ¬ bundleTableFoot eCap tbl m a → mem₁ a = mem₀ a)
    (hdisj : ∀ a, ptr ≤ a → a < ptr + groupsWords (readGroups mem₀ ptr g) →
      ¬ bundleTableFoot eCap tbl m a) :
    readGroups mem₁ ptr g = readGroups mem₀ ptr g := by
  induction g generalizing ptr with
  | zero => rfl
  | succ g ih =>
    have hlen_w : 1 + mem₀ ptr + groupsWords (readGroups mem₀ (ptr + 1 + mem₀ ptr) g) =
        groupsWords (readGroups mem₀ ptr (g + 1)) := by simp [readGroups, groupsWords]
    have hhd : mem₁ ptr = mem₀ ptr := hagree ptr (hdisj ptr (le_refl _) (by omega))
    simp only [readGroups, hhd]
    congr 1
    · apply List.map_congr_left; intro j hj
      have hj_lt : j < mem₀ ptr := List.mem_range.mp hj
      exact hagree (ptr + 1 + j) (hdisj _ (by omega) (by omega))
    · exact ih fun a ha1 ha2 => hdisj a (by omega) (by omega)

/-- Preserves the per-slot scanned-end list / cleared-head invariant across one Phase 3 step. -/
lemma bundleStep_curScan_step {slotCap eCap tbl s outI h₀ hS hCur hNext batchPtr totalWords i : ℕ}
    {m : BundleTableMeta slotCap} {touched : List ℕ} {scanEnds : Fin slotCap → List (ℕ × ℕ × ℕ)}
    {footPrev footNext : ℕ → Prop} {memPrev memNext : ℕ → ℕ}
    (hndT : touched.Nodup) (hi : i < touched.length) (hs_eq : touched[i]'hi = s)
    (hs_lt : s < slotCap) (hh₀_le : h₀ ≤ hS) (hhS_le : hS ≤ hCur) (hbp_lo : hCur ≤ batchPtr)
    (hfoot_lt : ∀ a, bundleTableFoot eCap tbl m a → a < h₀)
    (hout_disj_foot : ∀ a, outI ≤ a → a < outI + 3 → ¬ bundleTableFoot eCap tbl m a)
    (hout_lt : outI + 3 ≤ h₀)
    (hnot_core_hi : ∀ a, tbl + bundleTableCoreSize slotCap eCap ≤ a →
      a < tbl + bundleTableFixedSize slotCap eCap → ¬ bundleTableCoreFoot eCap tbl m a)
    (htf_disj_tbl : ∀ a, footPrev a → ¬ bundleTableFoot eCap tbl m a)
    (htfN : ∀ a, footNext a → footPrev a ∨ (batchPtr + totalWords ≤ a ∧ a < hNext))
    (hcurB0_s : memNext (btCurBunBase tbl slotCap eCap + s) = 0)
    (hcurT0_s : memNext (btCurTagBase tbl slotCap eCap + s) = 0)
    (hfr : ∀ a < hCur, ¬ bundleTableCoreFoot eCap tbl m a →
      a ≠ btCurBunBase tbl slotCap eCap + s → a ≠ btCurTagBase tbl slotCap eCap + s →
      (a < outI ∨ outI + 3 ≤ a) → ¬ footPrev a → memNext a = memPrev a)
    (hprev : ∀ s' (hs' : s' < slotCap),
      if s' ∈ touched.drop i then
        ScanNodesAt eCap memPrev h₀ hS (memPrev (btCurBunBase tbl slotCap eCap + s')) (scanEnds ⟨s', hs'⟩) ∧
        ScanNodesIn memPrev (fun a => ¬ footPrev a)
          (memPrev (btCurBunBase tbl slotCap eCap + s')) (scanEnds ⟨s', hs'⟩) ∧
        memPrev (btCurTagBase tbl slotCap eCap + s') = (scanEnds ⟨s', hs'⟩).length
      else
        memPrev (btCurBunBase tbl slotCap eCap + s') = 0 ∧
        memPrev (btCurTagBase tbl slotCap eCap + s') = 0) :
    ∀ s' (hs' : s' < slotCap),
      if s' ∈ touched.drop (i + 1) then
        ScanNodesAt eCap memNext h₀ hS (memNext (btCurBunBase tbl slotCap eCap + s')) (scanEnds ⟨s', hs'⟩) ∧
        ScanNodesIn memNext (fun a => ¬ footNext a)
          (memNext (btCurBunBase tbl slotCap eCap + s')) (scanEnds ⟨s', hs'⟩) ∧
        memNext (btCurTagBase tbl slotCap eCap + s') = (scanEnds ⟨s', hs'⟩).length
      else
        memNext (btCurBunBase tbl slotCap eCap + s') = 0 ∧
        memNext (btCurTagBase tbl slotCap eCap + s') = 0 := by
  intro s' hs'
  by_cases hss : s' = s
  · subst hss
    have hnot_next : s' ∉ touched.drop (i + 1) := by
      have hnd_drop : (touched.drop i).Nodup := hndT.sublist (List.drop_sublist _ _)
      rw [List.drop_eq_getElem_cons hi, hs_eq, List.nodup_cons] at hnd_drop
      exact hnd_drop.1
    simp only [hnot_next, ↓reduceIte]
    exact ⟨hcurB0_s, hcurT0_s⟩
  · have hcb_ft := btCurBun_in_foot (m := m) (tbl := tbl) (eCap := eCap) hs'
    have hct_ft := btCurTag_in_foot (m := m) (tbl := tbl) (eCap := eCap) hs'
    have hcb_nc : ¬ bundleTableCoreFoot eCap tbl m (btCurBunBase tbl slotCap eCap + s') :=
      hnot_core_hi _ (by unfold btCurBunBase bundleTableCoreSize; omega)
        (by unfold btCurBunBase bundleTableFixedSize; omega)
    have hct_nc : ¬ bundleTableCoreFoot eCap tbl m (btCurTagBase tbl slotCap eCap + s') :=
      hnot_core_hi _ (by unfold btCurTagBase bundleTableCoreSize; omega)
        (by unfold btCurTagBase bundleTableFixedSize; omega)
    have hcb_eq : memNext (btCurBunBase tbl slotCap eCap + s') = memPrev (btCurBunBase tbl slotCap eCap + s') :=
      hfr _ (lt_of_lt_of_le (hfoot_lt _ hcb_ft) (by omega)) hcb_nc
        (by omega) (by unfold btCurBunBase btCurTagBase; omega)
        (by by_contra h; push Not at h; exact hout_disj_foot _ (by omega) (by omega) hcb_ft)
        (fun hf => htf_disj_tbl _ hf hcb_ft)
    have hct_eq : memNext (btCurTagBase tbl slotCap eCap + s') = memPrev (btCurTagBase tbl slotCap eCap + s') :=
      hfr _ (lt_of_lt_of_le (hfoot_lt _ hct_ft) (by omega)) hct_nc
        (by unfold btCurBunBase btCurTagBase; omega) (by omega)
        (by by_contra h; push Not at h; exact hout_disj_foot _ (by omega) (by omega) hct_ft)
        (fun hf => htf_disj_tbl _ hf hct_ft)
    have hmem_iff : s' ∈ touched.drop (i + 1) ↔ s' ∈ touched.drop i := by
      rw [List.drop_eq_getElem_cons hi, hs_eq, List.mem_cons]
      exact ⟨Or.inr, fun h => h.resolve_left hss⟩
    have hpr := hprev s' hs'
    by_cases hmem' : s' ∈ touched.drop (i + 1)
    · have hmem_i : s' ∈ touched.drop i := hmem_iff.mp hmem'
      simp only [hmem', ↓reduceIte]
      simp only [hmem_i, ↓reduceIte] at hpr
      rw [hcb_eq, hct_eq]
      obtain ⟨h1, h2⟩ := scanNodesAt_mono_of_in (Q := fun a => ¬ footNext a) hpr.1 hpr.2.1 (le_refl _)
        (fun a ha1 ha2 hnt => hfr a (by omega)
          (fun hf => by have := hfoot_lt a (bundleTableCoreFoot_subset_foot hf); omega)
          (by have := hfoot_lt _ (btCurBun_in_foot hs_lt); omega)
          (by have := hfoot_lt _ (btCurTag_in_foot hs_lt); omega)
          (Or.inr (by omega)) hnt)
        (fun a _ ha2 hnt hf => by rcases htfN a hf with h0 | ⟨h1', _⟩; exact hnt h0; omega)
      exact ⟨h1, h2, hpr.2.2⟩
    · have hnot_i : s' ∉ touched.drop i := fun h => hmem' (hmem_iff.mpr h)
      simp only [hmem', ↓reduceIte]
      simp only [hnot_i, ↓reduceIte] at hpr
      exact ⟨hcb_eq.trans hpr.1, hct_eq.trans hpr.2⟩

end

end MinCostFlow.SparseCore.Program
