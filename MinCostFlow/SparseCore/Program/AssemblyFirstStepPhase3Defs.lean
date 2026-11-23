module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepDelTriples
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepGroupsProg
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepGroupsModel
public import MinCostFlow.SparseCore.Program.AssemblyFirstTourStepProof
public import MinCostFlow.SparseCore.Program.AssemblyFirstTourPot
public import MinCostFlow.SparseCore.Program.TourAsmBridge
public import MinCostFlow.SparseCore.Program.AssemblyReemb
public import MinCostFlow.SparseCore.Program.BundleCapHeadroomStep

import WordRAM.Tactic

/-!
# Phase 3 end-to-end verification (`AssemblyFirstStepPhase3Proof`)

Chains the four sub-calls of Phase 3 (`asmFirstPhase3Stmt`):
1. `fDelTriples` (`asmFirstBuildDelTriples_runs`): builds `readDelTriples` on `tr.cs.RF` before the
   tour update.
2. `fBuildGroups` (`asmFirstBuildGroups_runs`): builds `readGroups` for `splitGroupsOf` from P4's
   `SplitEntriesAt` in `O(m log m + 1)` time with zero tour queries.
3. `fTourStep` (`asmFirstTourBlockStep_runs`): advances `tourAsmRep` from `(ord, tr.cs.RF, mk)` to
   `(ord', info.state.cs.RF, mk')`, emitting `OutSplitListsAt` at `splitPtr`.
4. `fBunStep` (`bunTableHeadroom_step_runs` via `asmFirstBunStepModel_runs`): advances
   `bunTableHeadroomRep` from `S₀` to `tableAfterStepRuns tr.cs tr.k ord' U S₀`, telescopes the
   smaller-side scan work into `asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)`,
   and writes the touched-slot update descriptors (`SmallBatchAt`) at `outDescPtr`.

Writes `[splitPtr, outDescPtr]` at `[h, h + 2)` and returns `hEnd`, with a pure polynomial space
bound free of `limbMul` and exact untouched-slot empty-batch characterization for Phase 4.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

/-! ## 1. Procedure and space bounds -/

@[expose] public section

/-- **Phase 3 composite procedure**,
`[bunH, slotCap, vCap, tourH, batch, words, edits, editWords, spPtr, delEdgesPtr, nDel, h]`:
reserves `[h, h + 2)` for `[splitPtr, outDescPtr]`, runs `fDelTriples`, `fBuildGroups`,
`fTourStep`, and `fBunStep`, writes `[splitPtr, outDescPtr]` at `[h, h + 2)`, and returns `hEnd`. -/
def asmFirstPhase3Stmt (fDelTriples fBuildGroups fTourStep fBunStep : ℕ) : Stmt :=
  .assign 12 (.bin .add (.reg 11) (.const 2)) ;;
  .call 13 fDelTriples [.reg 0, .reg 3, .reg 9, .reg 10, .reg 12] ;;
  .call 14 fBuildGroups [.reg 8, .reg 2, .reg 13] ;;
  .call 15 fTourStep [.reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 14] ;;
  .assign 16 (.load (.reg 13)) ;;
  .assign 17 (.load (.bin .add (.reg 13) (.const 1))) ;;
  .assign 18 (.bin .add (.bin .add (.reg 15) (.const 1)) (.bin .mul (.const 3) (.reg 1))) ;;
  .call 19 fBunStep [.reg 0, .reg 3, .reg 10, .reg 12, .reg 16, .reg 17, .reg 15, .reg 18] ;;
  .store (.reg 11) (.load (.reg 14)) ;;
  .store (.bin .add (.reg 11) (.const 1)) (.reg 15) ;;
  .ret (.reg 19)

/-- Pure polynomial upper bound on `bundleStepSpace tourBundleSpec` (free of `limbMul`). -/
def phase3BunStepSpaceBound (slotCap vCap eCap : ℕ) : ℕ :=
  22 * (2 * vCap + 12 * vCap * eCap + slotCap * eCap + slotCap + 1)

/-- Total heap space bound of `asmFirstPhase3Stmt` (free of `limbMul`). -/
def asmFirstPhase3Space (slotCap vCap eCap words editWords nDel : ℕ) : ℕ :=
  2 + buildDelTriplesSpace tourBundleSpec nDel +
  buildGroupsSpace vCap vCap +
  tourBlockStepSpace vCap eCap words editWords +
  (1 + 3 * slotCap) +
  phase3BunStepSpaceBound slotCap vCap eCap

end

public section

theorem asmFirstPhase3Stmt_noRand (f1 f2 f3 f4 : ℕ) :
    (asmFirstPhase3Stmt f1 f2 f3 f4).NoRand := by
  simp [asmFirstPhase3Stmt, Stmt.NoRand]

/-! ## 2. Pure monotonicity, batch-encoding, and space lemmas -/

lemma outSplitListsAt_mono {mem₁ mem₂ : ℕ → ℕ} {top₁ top₂ : ℕ} {avoid₁ avoid₂ : ℕ → Prop}
    {keep E₀ : Finset ℕ} (htop : top₁ ≤ top₂)
    (hmem : ∀ x < top₁, ¬ avoid₁ x → mem₂ x = mem₁ x)
    (hav : ∀ x < top₁, avoid₂ x → avoid₁ x) :
    ∀ {a : ℕ} {G : MGraph} {P : List Update} {Ys : List (List End)},
      OutSplitListsAt mem₁ top₁ avoid₁ keep E₀ a G P Ys →
      OutSplitListsAt mem₂ top₂ avoid₂ keep E₀ a G P Ys := by
  intro a G P Ys h
  induction P generalizing a G Ys with
  | nil =>
    cases Ys with
    | nil => exact h
    | cons _ _ => cases h
  | cons u rest ih =>
    cases u with
    | insert _ _ _ => cases Ys <;> cases h
    | delete _ => cases Ys <;> cases h
    | split v v' St Sh =>
      cases Ys with
      | nil => cases h
      | cons Y Ys' =>
        rcases h with ⟨hpos, ha5, hav5, hm0, hm1, hm2, hEL, hEL_top, hEL_av, hnd, hE0, hkeep, htail⟩
        have ha_eq : ∀ i < 5, mem₂ (a + i) = mem₁ (a + i) := fun i hi =>
          hmem (a + i) (by omega) (hav5 i hi)
        have hm0' : mem₂ a = v := by simpa using (ha_eq 0 (by omega)).trans hm0
        have hm1' : mem₂ (a + 1) = v' := (ha_eq 1 (by omega)).trans hm1
        have hm2' : mem₂ (a + 2) ≤ 1 := by rw [ha_eq 2 (by omega)]; exact hm2
        have hm3' : mem₂ (a + 3) = mem₁ (a + 3) := ha_eq 3 (by omega)
        have hm4' : mem₂ (a + 4) = mem₁ (a + 4) := ha_eq 4 (by omega)
        refine ⟨hpos, by omega, fun i hi h2 => hav5 i hi (hav _ (by omega) h2),
          hm0', hm1', hm2', ?_, by rw [hm3']; omega,
          fun i hi h2 => hEL_av i hi (hav _ (by rw [hm3'] at h2; omega) (by rwa [hm3'] at h2)),
          hnd, hE0, by rw [ha_eq 2 (by omega)]; exact hkeep,
          by rw [hm4']; exact ih htail⟩
        rw [hm3']
        refine ⟨(hmem _ (by omega) (hEL_av 0 (by omega))).trans hEL.1, fun i hi => ?_⟩
        rw [show mem₁ (a + 3) + 1 + i = mem₁ (a + 3) + (i + 1) by omega]
        exact (hmem _ (by omega) (hEL_av (i + 1) (by omega))).trans
          (by rw [show mem₁ (a + 3) + (i + 1) = mem₁ (a + 3) + 1 + i by omega]; exact hEL.2 i hi)

lemma batchSplitCount_le_batchEnc : ∀ (G : MGraph) (U : List Update),
    batchSplitCount U ≤ G.batchEnc U
  | _, [] => Nat.zero_le _
  | G, u :: rest => by
    have ih := batchSplitCount_le_batchEnc (G.applyUpdate u) rest
    unfold batchSplitCount at ih ⊢
    simp only [List.countP_cons, MGraph.batchEnc]
    cases u <;> simp [isSplit, MGraph.updateEnc] <;> omega

lemma addCandsForGroups_none_eq_empty {slotCap : ℕ} {S : BundleTableState slotCap}
    {cord' : ℕ → List End} {gs : List (List ℕ)} {maxIdxs : List ℕ}
    {j : Fin slotCap} (hnone : S j = none) :
    ∀ k, addCandsForGroups S cord' gs maxIdxs (fun _ => ∅) k j = ∅ := by
  have hpref : ∀ (G : List ℕ) (mIdx : ℕ) (c : Fin slotCap → Finset ℕ) (t : ℕ),
      c j = ∅ → addCandsForGroupPrefix S cord' G mIdx c t j = ∅ := by
    intro G mIdx c t; induction t with
    | zero => intro hc; exact hc
    | succ t ih =>
      intro hc; simp only [addCandsForGroupPrefix]
      split_ifs
      · exact ih hc
      · simp [addCandsForList, passBCands, hnone, ih hc]
      · exact ih hc
  intro k; induction k with
  | zero => rfl
  | succ k ih => exact hpref _ _ _ _ ih

lemma bundleStepSpace_le_phase3 {slotCap vCap eCap : ℕ}
    {S₀ : BundleTableState slotCap} {D : Finset ℕ}
    {cord' : ℕ → List End} {src' : End → ℕ} {gs : List (List ℕ)} {maxIdxs touched : List ℕ}
    (hdisj₀ : ∀ j₁ j₂ : Fin slotCap, j₁ ≠ j₂ → ∀ B₁ B₂,
      S₀ j₁ = some B₁ → S₀ j₂ = some B₂ → Disjoint B₁.edges B₂.edges)
    (hB_cap : ∀ j B₀, S₀ j = some B₀ → ∀ e ∈ B₀.edges, e < eCap)
    (hcord'_nd : ∀ v, (cord' v).Nodup)
    (hcord'_cap : ∀ v x, x ∈ cord' v → x.1 < eCap)
    (hgs_nd : ∀ G ∈ gs, G.Nodup)
    (hgs_disj : ∀ i (hi : i < gs.length) j' (hj' : j' < gs.length), i ≠ j' →
      Disjoint gs[i].toFinset gs[j'].toFinset)
    (hgs_tot : groupsTotalLen gs ≤ 2 * vCap)
    (hmax_lt : ∀ gi (hgi : gi < gs.length), maxIdxs.getD gi 0 < gs[gi].length)
    (htch_nd : touched.Nodup) (htch_lt : ∀ s ∈ touched, s < slotCap)
    (hsrc_iff : ∀ j B₀, S₀ j = some B₀ → ∀ x ∈ Bundle.edgeEnds (B₀.edges \ D), ∀ w, x ∈ cord' w ↔ src' x = w)
    (hbin : ∀ j B₀, S₀ j = some B₀ → ∀ b ∈ B₀.vertices,
      2 ≤ (finalRootsOf B₀ (B₀.edges \ D) src' b).card →
        ∃ gi, ∃ (hgi : gi < gs.length),
          ∀ x ∈ survivingEnds B₀ (B₀.edges \ D) b, src' x ∈ gs[gi].toFinset) :
    let candSet := addCandsForGroups (tableDelEdges S₀ D) cord' gs maxIdxs (fun _ => ∅) gs.length
    let scanLen := slotScannedEnds S₀ D cord' gs maxIdxs
    bundleStepSpace tourBundleSpec S₀ D candSet scanLen cord' gs touched ≤
      phase3BunStepSpaceBound slotCap vCap eCap := by
  intro candSet scanLen
  have hlin := bundleStepSpace_le_linear (TS := tourBundleSpec) (cT := 3) (S₀ := S₀) (D := D)
    (candSet := candSet) (scanLen := scanLen) (cord' := cord') (gs := gs) (touched := touched)
    tourBundleSpec_listSpace_le
  dsimp only at hlin
  have hcord_len : ∀ v, (cord' v).length ≤ 2 * eCap := fun v => by
    have hsub : (cord' v).toFinset ⊆ Finset.range eCap ×ˢ (Finset.univ : Finset Bool) := fun x hx => by
      rw [Finset.mem_product, Finset.mem_range]
      exact ⟨hcord'_cap v x (List.mem_toFinset.mp hx), Finset.mem_univ _⟩
    rw [← List.toFinset_card_of_nodup (hcord'_nd v)]
    exact (Finset.card_le_card hsub).trans (by simp [Finset.card_product]; omega)
  have htotEnds : (gs.map fun G => (G.map fun w => (cord' w).length).sum).sum ≤ 4 * vCap * eCap := by
    have haux : ∀ (l : List (List ℕ)),
        (l.map fun G => (G.map fun w => (cord' w).length).sum).sum ≤ groupsTotalLen l * (2 * eCap) := by
      intro l; induction l with
      | nil => simp [groupsTotalLen]
      | cons G rest ih =>
        have hG : (G.map fun w => (cord' w).length).sum ≤ G.length * (2 * eCap) := by
          clear ih; induction G with
          | nil => simp
          | cons w ws ihG => simp only [List.map_cons, List.sum_cons, List.length_cons]; have := hcord_len w; nlinarith
        simp only [List.map_cons, List.sum_cons, groupsTotalLen] at ih ⊢; nlinarith
    have := haux gs; nlinarith
  have hnonMax_le : totalNonMaxLen cord' gs maxIdxs ≤ 4 * vCap * eCap := by
    have h1 : totalNonMaxLen cord' gs maxIdxs ≤
        (gs.map fun G => (G.map fun w => (cord' w).length).sum).sum := by
      unfold totalNonMaxLen
      have haux : ∀ (l : List (List ℕ)) (ms : List ℕ),
          (∑ gi ∈ Finset.range l.length,
            ∑ j ∈ (Finset.range (l.getD gi []).length).erase (ms.getD gi 0),
              (cord' ((l.getD gi []).getD j 0)).length) ≤
          (l.map fun G => (G.map fun w => (cord' w).length).sum).sum := by
        intro l ms
        have hsum_eq : (l.map fun G => (G.map fun w => (cord' w).length).sum).sum =
            ∑ gi ∈ Finset.range l.length,
              ∑ j ∈ Finset.range (l.getD gi []).length, (cord' ((l.getD gi []).getD j 0)).length := by
          clear ms; induction l using List.reverseRecOn with
          | nil => simp
          | append_singleton xs x ih =>
            rw [List.map_append, List.map_singleton, List.sum_append, List.sum_singleton,
              List.length_append, List.length_singleton, Finset.sum_range_succ, ih]
            congr 1
            · refine Finset.sum_congr rfl fun gi hgi => ?_
              have hlt := Finset.mem_range.mp hgi
              rw [List.getD_eq_getElem (xs ++ [x]) [] (by rw [List.length_append]; omega), List.getElem_append_left hlt,
                List.getD_eq_getElem xs [] hlt]
            · rw [List.getD_eq_getElem (xs ++ [x]) [] (by rw [List.length_append, List.length_singleton]; omega),
                List.getElem_append_right (le_refl _)]
              simp only [Nat.sub_self, List.getElem_cons_zero]
              clear ih; induction x using List.reverseRecOn with
              | nil => simp
              | append_singleton ys y ihy =>
                rw [List.map_append, List.map_singleton, List.sum_append, List.sum_singleton,
                  List.length_append, List.length_singleton, Finset.sum_range_succ, ihy]
                congr 1
                · refine Finset.sum_congr rfl fun j hj => ?_
                  have hlt := Finset.mem_range.mp hj
                  rw [List.getD_eq_getElem (ys ++ [y]) 0 (by rw [List.length_append]; omega), List.getElem_append_left hlt,
                    List.getD_eq_getElem ys 0 hlt]
                · rw [List.getD_eq_getElem (ys ++ [y]) 0 (by rw [List.length_append, List.length_singleton]; omega),
                    List.getElem_append_right (le_refl _)]
                  simp only [Nat.sub_self, List.getElem_cons_zero]
        rw [hsum_eq]
        exact Finset.sum_le_sum fun gi _ => Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
      exact haux gs maxIdxs
    omega
  have hsum_list_le : ∀ (f : Fin slotCap → ℕ),
      (touched.map fun s => if hs : s < slotCap then f ⟨s, hs⟩ else 0).sum ≤ ∑ j : Fin slotCap, f j := by
    intro f
    have haux : ∀ (l : List ℕ), l.Nodup → (∀ s ∈ l, s < slotCap) →
        (l.map fun s => if hs : s < slotCap then f ⟨s, hs⟩ else 0).sum =
          ∑ j ∈ Finset.univ.filter (fun j : Fin slotCap => j.1 ∈ l), f j := by
      intro l; induction l with
      | nil => intro _ _; simp
      | cons s ts ih =>
        intro hnd hlt
        rcases List.nodup_cons.mp hnd with ⟨hns, hnd'⟩
        have hs : s < slotCap := hlt s List.mem_cons_self
        have hfilt : Finset.univ.filter (fun j : Fin slotCap => j.1 ∈ s :: ts) =
            insert ⟨s, hs⟩ (Finset.univ.filter (fun j : Fin slotCap => j.1 ∈ ts)) := by
          ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons,
            Finset.mem_insert, Fin.ext_iff]
        have hnot : (⟨s, hs⟩ : Fin slotCap) ∉ Finset.univ.filter (fun j : Fin slotCap => j.1 ∈ ts) := by
          simp [hns]
        rw [List.map_cons, List.sum_cons, dite_eq_left hs, hfilt, Finset.sum_insert hnot,
          ih hnd' (fun x hx => hlt x (List.mem_cons_of_mem _ hx))]
    rw [haux touched htch_nd htch_lt]
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hscan_sum : (∑ j : Fin slotCap, scanLen j) ≤ totalNonMaxLen cord' gs maxIdxs :=
    addScanEndsForGroups_sum_le hdisj₀ cord' gs maxIdxs (fun _ => ∅)
  have htotScan : (touched.map fun s => if hs : s < slotCap then scanLen ⟨s, hs⟩ else 0).sum ≤ 4 * vCap * eCap :=
    (hsum_list_le scanLen).trans (hscan_sum.trans hnonMax_le)
  have hcand_le_scan : ∀ j : Fin slotCap, slotCandCnt candSet j ≤ scanLen j := fun j => by
    cases hS : S₀ j with
    | none =>
      have h0 : candSet j = ∅ := addCandsForGroups_none_eq_empty (by simp [tableDelEdges, hS]) gs.length
      simp [slotCandCnt, h0]
    | some B₀ =>
      exact (scanValidForSlot_of_scan hS hgs_nd hgs_disj (fun _ _ w _ => hcord'_nd w)
        hmax_lt (hsrc_iff j B₀ hS) (hbin j B₀ hS)).2.2
  have htotCands : (touched.map fun s => if hs : s < slotCap then slotCandCnt candSet ⟨s, hs⟩ else 0).sum ≤
      4 * vCap * eCap :=
    (hsum_list_le (slotCandCnt candSet)).trans
      ((Finset.sum_le_sum fun j _ => hcand_le_scan j).trans (hscan_sum.trans hnonMax_le))
  have htch_len : touched.length ≤ slotCap := by
    have hsub : touched.toFinset ⊆ Finset.range slotCap := fun s hs =>
      Finset.mem_range.mpr (htch_lt s (List.mem_toFinset.mp hs))
    rw [← List.toFinset_card_of_nodup htch_nd]
    exact (Finset.card_le_card hsub).trans (by simp)
  have htotDels : (touched.map fun s => if hs : s < slotCap then slotDelCnt S₀ D ⟨s, hs⟩ else 0).sum ≤
      slotCap * eCap := by
    have hdel_le : ∀ j : Fin slotCap, slotDelCnt S₀ D j ≤ eCap := fun j => by
      unfold slotDelCnt; cases hS : S₀ j with
      | none => exact Nat.zero_le _
      | some B₀ =>
        have hsub : B₀.edges ∩ D ⊆ Finset.range eCap := fun e he =>
          Finset.mem_range.mpr (hB_cap j B₀ hS e (Finset.mem_inter.mp he).1)
        exact (Finset.card_le_card hsub).trans (by simp)
    have haux : ∀ (l : List ℕ),
        (l.map fun s => if hs : s < slotCap then slotDelCnt S₀ D ⟨s, hs⟩ else 0).sum ≤ l.length * eCap := by
      intro l; induction l with
      | nil => simp
      | cons s ts ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        split_ifs with hs
        · have := hdel_le ⟨s, hs⟩; nlinarith
        · nlinarith
    exact (haux touched).trans (Nat.mul_le_mul_right eCap htch_len)
  have hqs : tourBundleSpec.querySpace = 1 := rfl
  unfold phase3BunStepSpaceBound
  rw [hqs] at hlin
  nlinarith

/-! ## 3. Model-level P5 step wrapper exposing `touched.Nodup`, `< slotCap`, and untouched-empty -/

theorem asmFirstBunStepModel_runs {TS : BundleTourSpec} {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {w slotCap vCap eCap tbl tourH delCount delPtr groupPtr outDescPtr h₀ pos : ℕ}
    {p : Program} {b bTourList bTourLen bTourOwner : ℕ} {ω : ℕ → Bool}
    (hp : p.HasAt b (bundleProcs b bTourList bTourLen bTourOwner))
    (htour : BundleTourAt TS w vCap eCap p bTourList bTourLen bTourOwner)
    {tr : BundleTreeState L} {U : List Update} {ord ord' : ℕ → List End}
    {slotOf : Finset ℕ × ℤ → ℕ} {P : Finset (Finset ℕ × ℤ)}
    {S₀ : BundleTableState slotCap} {m : BundleTableMeta slotCap}
    {dels : List (ℕ × ℕ × ℕ)} {gs : List (List ℕ)} {R_old R_new : Finset ℕ} {oldRoots : List ℕ}
    {cord : ℕ → List End} {tx₀ : htour.rep.τ} {mem₀ : ℕ → ℕ}
    (hD_eq : (dels.map Prod.fst).toFinset = batchDeletes U)
    (hinv0 : bunRestartInv vCap eCap S₀ cord)
    (hMatch0 : ∀ q ∈ P, ∃ (hs : slotOf q < slotCap) (B : BundleState),
      S₀ ⟨slotOf q, hs⟩ = some B ∧ BunAgree B (tr.bun q))
    (hready : ∀ j B₀, S₀ j = some B₀ → BundleStepReady tr.cs B₀ tr.k ord ord' U)
    (hcord'_bounds : ∀ v x, x ∈ outCoreOrder (stepBundleTree sparsify tr U ord ord').state ord' v →
      v < vCap ∧ x.1 < eCap)
    (hw16 : 16 ≤ 2 ^ w) (htourH_w : tourH < 2 ^ w)
    (hpk_w : vCap * (2 * eCap) < 2 ^ w)
    (htbl_w : tbl + bundleTableFixedSize slotCap eCap < 2 ^ w)
    (hblks_w : ∀ js : Fin slotCap, ∀ q c, m.slotBlocks js = some (q, c) →
      q + bundleSlotBlockSize c < 2 ^ w)
    (hdel_w : delPtr + 3 * delCount < 2 ^ w)
    (hgrp_w : groupPtr + groupsWords gs < 2 ^ w)
    (hout_w : outDescPtr + 1 + 3 * slotCap < 2 ^ w)
    (hfoot_lt : ∀ a, (bunTableHeadroomRep slotCap vCap eCap tr.k).foot tbl m a → a < h₀)
    (hdel_lt : delPtr + 3 * delCount ≤ h₀)
    (hgrp_lt : groupPtr + groupsWords gs ≤ h₀)
    (hout_lt : outDescPtr + 1 + 3 * slotCap ≤ h₀)
    (hdel_disj_foot : ∀ a, delPtr ≤ a → a < delPtr + 3 * delCount →
      ¬ (bunTableHeadroomRep slotCap vCap eCap tr.k).foot tbl m a)
    (hgrp_disj_foot : ∀ a, groupPtr ≤ a → a < groupPtr + groupsWords gs →
      ¬ (bunTableHeadroomRep slotCap vCap eCap tr.k).foot tbl m a)
    (hout_disj_foot : ∀ a, outDescPtr ≤ a → a < outDescPtr + 1 + 3 * slotCap →
      ¬ (bunTableHeadroomRep slotCap vCap eCap tr.k).foot tbl m a)
    (htfoot_lt : ∀ a, htour.rep.foot tourH tx₀ a → a < h₀)
    (htfoot_disj_tbl : ∀ a, htour.rep.foot tourH tx₀ a →
      ¬ (bunTableHeadroomRep slotCap vCap eCap tr.k).foot tbl m a)
    (htfoot_disj_grp : ∀ a, htour.rep.foot tourH tx₀ a → a < groupPtr ∨ groupPtr + groupsWords gs ≤ a)
    (htfoot_disj_out : ∀ a, htour.rep.foot tourH tx₀ a → a < outDescPtr ∨ outDescPtr + 1 + 3 * slotCap ≤ a)
    (hzero : ZeroFrom mem₀ h₀)
    (htrep : htour.rep.rep tourH (outCoreOrder (stepBundleTree sparsify tr U ord ord').state ord') tx₀ mem₀)
    (hrep0 : (bunTableHeadroomRep slotCap vCap eCap tr.k).rep tbl S₀ m mem₀)
    (hdels_len : dels.length = delCount)
    (hdels_mem : readDelTriples mem₀ delPtr delCount = dels)
    (hdels_lt : ∀ trD ∈ dels, trD.1 < eCap ∧ trD.2.1 < 2 ^ w ∧ trD.2.2 < 2 ^ w)
    (hdels_par : ∀ i (hi : i < dels.length), dels[i].1 ∉ delPrefixSet dels i →
      ∀ (j : Fin slotCap) (B : BundleState), S₀ j = some B →
        dels[i].1 ∈ B.edges →
        dels[i].2.1 = B.parent (B.bundleOf (dels[i].1, true)) ∧
        dels[i].2.2 = B.parent (B.bundleOf (dels[i].1, false)))
    (hgs_mem : readGroups mem₀ groupPtr gs.length = gs)
    (hgs_pos : ∀ G ∈ gs, 0 < G.length)
    (hgs_lt : ∀ G ∈ gs, ∀ v ∈ G, v < vCap ∧ v < 2 ^ w)
    (hgs_nd : ∀ G ∈ gs, G.Nodup)
    (hgs_sub : ∀ G ∈ gs, ∀ v ∈ G, v ∈ R_new)
    (hgs_disj : ∀ i (hi : i < gs.length) j (hj : j < gs.length), i ≠ j →
      Disjoint gs[i].toFinset gs[j].toFinset)
    (hold_len : oldRoots.length = gs.length)
    (hold_nd : oldRoots.Nodup)
    (hold_sub : ∀ r ∈ oldRoots, r ∈ R_old)
    {addG : ℕ → ℕ} {addR : ℕ → ℕ} {maxLen : ℕ}
    (hgroup_sum_le : ∀ gi (hgi : gi < gs.length),
      (∑ v ∈ gs[gi].toFinset, (outCoreOrder (stepBundleTree sparsify tr U ord ord').state ord' v).length) ≤
        (cord (oldRoots[gi]'(by omega))).length + addG gi ∧
      (cord (oldRoots[gi]'(by omega))).length + addG gi ≤ maxLen)
    (hrest_le : ∀ r ∈ R_new, (∀ gi (hgi : gi < gs.length), r ∉ gs[gi].toFinset) →
      r ∈ R_old ∧ r ∉ oldRoots ∧
        (outCoreOrder (stepBundleTree sparsify tr U ord ord').state ord' r).length ≤ (cord r).length + addR r ∧
        (cord r).length + addR r ≤ maxLen)
    (hbundle_in_group : ∀ j B₀, S₀ j = some B₀ → ∀ bun ∈ B₀.vertices,
      2 ≤ (finalRootsOf B₀ (B₀.edges \ batchDeletes U)
        (coreGraph (compLSFBatch tr.cs U).G (compLSFBatch tr.cs U).lsf).src bun).card →
        ∃ gi, ∃ (hgi : gi < gs.length),
          ∀ x ∈ survivingEnds B₀ (B₀.edges \ batchDeletes U) bun,
            (coreGraph (compLSFBatch tr.cs U).G (compLSFBatch tr.cs U).lsf).src x ∈ gs[gi].toFinset)
    (hh_sp : ∀ (maxIdxs : List ℕ) (touched : List ℕ),
      maxIdxs.length = gs.length →
      (∀ gi (hgi : gi < gs.length), maxIdxs.getD gi 0 < gs[gi].length) →
      touched.Nodup → (∀ s ∈ touched, s < slotCap) →
      let cord' := outCoreOrder (stepBundleTree sparsify tr U ord ord').state ord'
      let candSet := addCandsForGroups (tableDelEdges S₀ (batchDeletes U)) cord' gs maxIdxs (fun _ => ∅) gs.length
      let scanLen := slotScannedEnds S₀ (batchDeletes U) cord' gs maxIdxs
      h₀ + bundleStepSpace TS S₀ (batchDeletes U) candSet scanLen cord' gs touched < 2 ^ w) :
    let info := stepBundleTree sparsify tr U ord ord'
    let cord' := outCoreOrder info.state ord'
    let S' := tableAfterStepRuns tr.cs tr.k ord' U S₀
    let U_grp := (Finset.range gs.length).biUnion fun gi => (gs.getD gi []).toFinset
    let totalAdded := (∑ gi ∈ Finset.range gs.length, addG gi) + ∑ r ∈ R_new \ U_grp, addR r
    ∃ body, p.procs[b + bundleIdxStep]? = some body ∧ ∃ st' c h' tx' maxIdxs touched,
      let candSet := addCandsForGroups (tableDelEdges S₀ (batchDeletes U)) cord' gs maxIdxs (fun _ => ∅) gs.length
      let scanLen := slotScannedEnds S₀ (batchDeletes U) cord' gs maxIdxs
      Runs w p ω body
        (startState [tbl, tourH, delCount, delPtr, gs.length, groupPtr, outDescPtr, h₀] mem₀ pos)
        (.returned h') st' c ∧
      (∀ gi (hgi : gi < gs.length), maxIdxs.getD gi 0 < gs[gi].length) ∧
      touched.Nodup ∧ (∀ s ∈ touched, s < slotCap) ∧
      (∀ j B₀, S₀ j = some B₀ → j.1 ∉ touched → (bundleCompStep tr.cs B₀ tr.k ord ord' U).1 = []) ∧
      (∀ j : Fin slotCap, S₀ j = none → j.1 ∉ touched) ∧
      (bunTableHeadroomRep slotCap vCap eCap tr.k).rep tbl S' m st'.mem ∧
      htour.rep.rep tourH cord' tx' st'.mem ∧
      bunRestartInv vCap eCap S' cord' ∧
      (∀ q ∈ P, ∃ (hs : slotOf q < slotCap) (B' : BundleState),
        S' ⟨slotOf q, hs⟩ = some B' ∧ BunAgree B' (info.state.bun q)) ∧
      h₀ ≤ h' ∧ h' ≤ h₀ + bundleStepSpace TS S₀ (batchDeletes U) candSet scanLen cord' gs touched ∧
      ZeroFrom st'.mem h' ∧
      (∀ a, htour.rep.foot tourH tx' a → htour.rep.foot tourH tx₀ a ∨ (h₀ ≤ a ∧ a < h')) ∧
      st'.mem outDescPtr = touched.length ∧
      (∀ i (hi : i < touched.length),
        let s := touched[i]'hi
        ∃ (hs : s < slotCap) (batchPtr totalWords : ℕ),
          st'.mem (outDescPtr + 1 + 3 * i) = s ∧
          st'.mem (outDescPtr + 1 + 3 * i + 1) = batchPtr ∧
          st'.mem (outDescPtr + 1 + 3 * i + 2) = totalWords ∧
          h₀ ≤ batchPtr ∧ batchPtr + totalWords ≤ h' ∧
          ∀ B₀, S₀ ⟨s, hs⟩ = some B₀ →
            SmallBatchAt st'.mem batchPtr B₀.graph (bundleCompStep tr.cs B₀ tr.k ord ord' U).1 totalWords) ∧
      (∀ a < h₀, ¬ (bunTableHeadroomRep slotCap vCap eCap tr.k).foot tbl m a →
        (a < outDescPtr ∨ outDescPtr + 1 + 3 * slotCap ≤ a) →
        ¬ htour.rep.foot tourH tx₀ a → st'.mem a = mem₀ a) ∧
      c + 70 * touched.length + (bunTableHeadroomRep slotCap vCap eCap tr.k).phi tbl m st'.mem +
          bundleScanPotMul TS eCap * tourPot R_new cord' + htour.rep.phi tourH tx' st'.mem ≤
        bundleStepCost TS eCap delCount gs +
        bunPhiMul * (∑ j : Fin slotCap, match S₀ j with
          | none => 0
          | some B₀ => batchSplitCount (bundleCompStep tr.cs B₀ tr.k ord ord' U).1) +
        (bunTableHeadroomRep slotCap vCap eCap tr.k).phi tbl m mem₀ +
        bundleScanPotMul TS eCap * (tourPot R_old cord + totalAdded * (Nat.log 2 maxLen + 2)) +
        htour.rep.phi tourH tx₀ mem₀ := by
  intro info cord' S' U_grp totalAdded
  set src' := (coreGraph (compLSFBatch tr.cs U).G (compLSFBatch tr.cs U).lsf).src
  have hcord'_nd : ∀ v, (cord' v).Nodup := fun v => by
    unfold cord' outCoreOrder
    split_ifs with hex
    · exact (coreRotation (L := info.state.cs.lsf)
        hex.choose_spec.choose_spec.choose_spec.choose
        hex.choose_spec.choose_spec.choose.hG_val
        (compLSF_RF_isRSF hex.choose_spec.choose_spec.choose)).nodup v
    · exact List.nodup_nil
  have hsrc_iff : ∀ j B₀, S₀ j = some B₀ →
      ∀ x ∈ Bundle.edgeEnds (B₀.edges \ batchDeletes U), ∀ v, x ∈ cord' v ↔ src' x = v := by
    intro j B₀ hS₀ x hx v
    obtain ⟨C_lsst, ℓ₀, hI, ρ, σ, _, hσ, _, hU, _⟩ := hready j B₀ hS₀
    have hI' := compLSFBatch_inv hI hU
    let σ' : Rotation info.state.cs.G := (compLSFBatch_G tr.cs U).symm ▸ σ
    have hσ' : σ'.order = ord' := by
      dsimp only [σ']
      have hcast : ∀ {G H : MGraph} (he : G = H) (τ : Rotation G), (he ▸ τ : Rotation H).order = τ.order := by
        intro G H he τ; cases he; rfl
      exact (hcast _ σ).trans hσ
    have hpart := (bundleRunsStep_spec (hready j B₀ hS₀)).1.1 σ' hI'.hG_val (compLSF_RF_isRSF hI') hσ'
    have hxE : x.1 ∈ (coreGraph info.state.cs.G info.state.cs.lsf).E := by
      have hsub := hpart.1
      have hEeq := (bundleRunsStep_spec (hready j B₀ hS₀)).2.2.2.2.1
      rw [hEeq] at hsub
      exact hsub ((Bundle.mem_edgeEnds _ _).mp hx)
    exact outCoreOrder_mem_iff_src hI' σ' hσ' hxE v
  obtain ⟨body, hbody, st', c, h', tx', maxIdxs, touched, hrun, hmaxLen, hmaxSpec,
    hndT, hltT, htouchIff, hhLo, hhHi, hzf, htr', htf', hrep', hout0, hdescs, hfr, hc⟩ :=
    bunTableHeadroom_step_runs (pos := pos) (ω := ω) (cord' := cord') (src' := src')
      hp htour hw16 htourH_w hpk_w htbl_w hblks_w hdel_w hgrp_w hout_w
      hfoot_lt hdel_lt hgrp_lt hout_lt hdel_disj_foot hgrp_disj_foot hout_disj_foot
      htfoot_lt htfoot_disj_tbl htfoot_disj_grp htfoot_disj_out hzero htrep hrep0
      hdels_len hdels_mem hdels_lt hdels_par hgs_mem hgs_pos hgs_lt hgs_nd hgs_disj
      (fun _ _ v _ x hx => (hcord'_bounds v x hx).2) (fun _ _ v _ => hcord'_nd v)
      (fun j B₀ hS₀ x hx => (hcord'_bounds (src' x) x ((hsrc_iff j B₀ hS₀ x (hD_eq ▸ hx) (src' x)).mpr rfl)).1)
      (fun j B₀ hS₀ x hx => (hsrc_iff j B₀ hS₀ x (hD_eq ▸ hx) (src' x)).mpr rfl)
      (fun j B₀ hS₀ x hx v' hv' => ((hsrc_iff j B₀ hS₀ x (hD_eq ▸ hx) v').mp hv').symm)
      (by simpa only [hD_eq] using hbundle_in_group)
      (by simpa only [hD_eq] using hh_sp)
  simp only [hD_eq] at hhHi hrep' hdescs hc htouchIff
  set candSet := addCandsForGroups (tableDelEdges S₀ (batchDeletes U)) cord' gs maxIdxs (fun _ => ∅) gs.length
  have hcand_eq : ∀ j B₀, S₀ j = some B₀ →
      candSet j = (exactSplitCands B₀ (B₀.edges \ batchDeletes U) src').toFinset := fun j B₀ hS₀ =>
    scanCands_eq_exactSplitCands hS₀ hgs_nd (fun _ _ v _ => hcord'_nd v)
      (fun gi hgi => (hmaxSpec gi hgi).1) (hsrc_iff j B₀ hS₀) (hbundle_in_group j B₀ hS₀)
  have hrep_runs : BundleTableRepAt slotCap vCap eCap tbl S' m st'.mem :=
    tableAfterStep_congr_runs hrep0.1 hready hcand_eq hrep'.1
  have hH' := bunTableHeadroomInv_tableAfterStepRuns hrep0.1 hrep0.2.2 hready
  have hinv' : bunRestartInv vCap eCap S' cord' :=
    bunRestartInv_tableAfterStepRuns hinv0 hready hcord'_bounds
  have hMatch' : ∀ q ∈ P, ∃ (hs : slotOf q < slotCap) (B' : BundleState),
      S' ⟨slotOf q, hs⟩ = some B' ∧ BunAgree B' (info.state.bun q) := by
    intro q hq
    obtain ⟨hs, B₀, hS₀, hag⟩ := hMatch0 q hq
    refine ⟨hs, (bundleRunsStep tr.cs B₀ tr.k ord' U).2, by simp [S', tableAfterStepRuns, hS₀], ?_⟩
    have hr := hready ⟨slotOf q, hs⟩ B₀ hS₀
    have hcomp := bunAgree_bundleCompStep_eq hag hr
    simpa only [info, stepBundleTree, bundleCompStep_eq hr] using hcomp.2
  have hbatch_eq : ∀ j B₀, S₀ j = some B₀ →
      slotBatchOf S₀ (batchDeletes U) src' candSet j = (bundleCompStep tr.cs B₀ tr.k ord ord' U).1 := by
    intro j B₀ hS₀
    have hr := hready j B₀ hS₀
    have heq := bundleStepEmitSlot_eq_bundleRunsStep hr (hcand_eq j B₀ hS₀)
    rw [bundleCompStep_eq hr, heq.1]
    simp only [slotBatchOf, hS₀]; rfl
  have huntouched : ∀ j B₀, S₀ j = some B₀ → j.1 ∉ touched →
      (bundleCompStep tr.cs B₀ tr.k ord ord' U).1 = [] := by
    intro j B₀ hS₀ hnt
    have hiff := htouchIff j
    rw [hS₀] at hiff
    have hD0 : B₀.edges ∩ batchDeletes U = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp fun h => hnt (hiff.mpr (Or.inl h))
    have hC0 : candSet j = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp fun h => hnt (hiff.mpr (Or.inr h))
    rw [← hbatch_eq j B₀ hS₀]
    simp [slotBatchOf, hS₀, hD0, hC0, byRootSplitFold]
  have hsum_splits : (∑ j : Fin slotCap, batchSplitCount (slotBatchOf S₀ (batchDeletes U) src' candSet j)) =
      ∑ j : Fin slotCap, match S₀ j with
        | none => 0
        | some B₀ => batchSplitCount (bundleCompStep tr.cs B₀ tr.k ord ord' U).1 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    cases hS : S₀ j with
    | none => simp [slotBatchOf, hS, batchSplitCount]
    | some B₀ => rw [hbatch_eq j B₀ hS]
  have hdrop := scanNonMaxSum_le_tourPot_drop_with_adds hold_len hold_nd hold_sub hgs_nd hgs_sub hgs_disj
    hmaxSpec hgroup_sum_le hrest_le
  have hmul := Nat.mul_le_mul_left (bundleScanPotMul TS eCap) hdrop
  rw [Nat.mul_add] at hmul
  have htouchNone : ∀ j : Fin slotCap, S₀ j = none → j.1 ∉ touched := by
    intro j hS₀
    have hiff := htouchIff j
    rw [hS₀] at hiff
    exact hiff
  refine ⟨body, hbody, st', c, h', tx', maxIdxs, touched, hrun,
    fun gi hgi => (hmaxSpec gi hgi).1, hndT, hltT, huntouched, htouchNone,
    ⟨hrep_runs, hrep'.2.1, hH'⟩, htr', hinv', hMatch', hhLo, hhHi, hzf, htf', hout0, ?_, hfr, ?_⟩
  · intro i hi
    obtain ⟨hs, bp, tw, h0, h1, h2, hlo, hhi, hbat⟩ := hdescs i hi
    refine ⟨hs, bp, tw, h0, h1, h2, hlo, hhi, fun B₀ hS₀ => ?_⟩
    rw [← hbatch_eq ⟨touched[i]'hi, hs⟩ B₀ hS₀]
    exact (hbat B₀ hS₀).1
  · rw [hsum_splits] at hc
    dsimp only [totalAdded, U_grp]
    omega


end

end MinCostFlow.SparseCore.Program
