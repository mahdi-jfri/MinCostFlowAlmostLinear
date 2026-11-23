module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepPhase1Proof
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitSpan
public import MinCostFlow.SparseCore.Program.AssemblyFirstNewPairs
public import MinCostFlow.SparseCore.Program.BundleCapHeadroomStep
public import MinCostFlow.SparseCore.Program.BunRestartModel

import WordRAM.Tactic

/-!
# First-phase step Phase 2 program, model lemmas, and spanner activation (`AssemblyFirstStepNewActProg`)

Provides the deterministic Word-RAM procedures and model foundations for lazily initializing newly
active components (`info.newlyActive`) before P2's tour step:

1. `bucketCode_inv` and `bucketCode_injective`: explicit bijection between `ℤ` and `ℕ`.
2. Inactive-component core-edge lemmas (`inactive_comp_root_unique`, `inactive_comp_cord_iff`,
   `inactive_comp_edge_disj_active`): for `C ∈ components tr.cs.G₀ \ tr.activeComps` under
   `CompLSFInv`, `AsmFirstInactiveCompInv`, `AsmFirstCrossInactiveInv`, and `RestartScurModelInv`,
   `r_c = tr.cs.RF.root v` is the unique root of `C`, lies in `C`, and `outCoreOrder tr ord r_c`
   contains both ends of every core edge of `C` and no other edges; moreover those core edges are
   disjoint from all currently active bundles.
3. Deterministic procedures `asmFirstInitOneCompStmt` (single newly active component: root query,
   `tourOp 4`, sort/dedup edges and bucket codes, binary search, update `csl`/`ctH`/`slotsPtr`/
   `ASM_SD_NSLOTS`, call P5 `bundleInitSlotsStmt` once) and `asmFirstNewActStmt` (loop over
   `newComps`, then call `asmFirstInitSpanBody` on newly added slots `[nSlots0 .. nSlots1)`).
4. `asmFirstStepActivateSpans_runs`: lifts `asmFirstInitSpanBody` (`AssemblyFirstInitSpan.lean`)
   to an arbitrary pre-existing bucket-spanner table `(S6, x6)`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

/-! ## 1. Bijection `bucketCode : ℤ → ℕ` -/

@[expose] public section

/-- Explicit inverse of `bucketCode : ℤ → ℕ`. -/
def bucketCodeInv (k : ℕ) : ℤ :=
  if k % 2 = 0 then ((k / 2 : ℕ) : ℤ) else -(((k + 1) / 2 : ℕ) : ℤ)

end

public section

theorem bucketCodeInv_left (b : ℤ) : bucketCodeInv (bucketCode b) = b := by
  unfold bucketCodeInv bucketCode
  split_ifs with h1 h2 h3 <;> omega

theorem bucketCodeInv_right (k : ℕ) : bucketCode (bucketCodeInv k) = k := by
  unfold bucketCode bucketCodeInv
  split_ifs with h1 h2 h3 <;> omega

theorem bucketCode_injective : Function.Injective bucketCode :=
  Function.LeftInverse.injective bucketCodeInv_left

/-! ## 2. Inactive-component single-root and core-edge lemmas -/

/-- Under `CompLSFInv`, an inactive component `C ∈ components cs.G₀` with `(cs.compSt C).R.card = 1`
has a unique root `r_c = cs.RF.root v` (for any `v ∈ (cs.compSt C).G.V`), satisfying `r_c ∈ C`,
`r_c ∈ cs.RF.R`, and `cs.RF.root u = r_c ↔ u ∈ (cs.compSt C).G.V` for all `u ∈ cs.G.V`. -/
theorem inactive_comp_root_unique {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {C : Finset ℕ} (hC : C ∈ components cs.G₀)
    (hR1 : (cs.compSt C).R.card = 1) {v : ℕ} (hv : v ∈ (cs.compSt C).G.V) :
    let r_c := cs.RF.root v
    (cs.compSt C).R = {r_c} ∧ r_c ∈ C ∧ r_c ∈ cs.RF.R ∧
    (∀ u ∈ (cs.compSt C).G.V, cs.RF.root u = r_c) ∧
    (∀ u ∈ cs.G.V, cs.RF.root u = r_c → u ∈ (cs.compSt C).G.V) := by
  intro r_c
  have hLC := (hI.hCompLSF C hC).1
  have hG0C : (cs.compSt C).G₀ = compGraph cs.G₀ C := (hI.hCompLSF C hC).2.1
  have hRS_C := lsfInv_to_RS hLC
  have hspec_v := rootedForest_root_spec hRS_C hv
  have hrc_eq : r_c = (cs.compSt C).RF.root v := compLSF_RF_root_eq hI hC hv
  have hrc_in_RC : r_c ∈ (cs.compSt C).R := hrc_eq ▸ hspec_v.1
  have hReq : (cs.compSt C).R = {r_c} :=
    (Finset.eq_singleton_iff_unique_mem.mpr ⟨hrc_in_RC, fun x hx => by
      have hcard := Finset.card_eq_one.mp hR1
      rcases hcard with ⟨y, hy⟩
      rw [hy] at hrc_in_RC hx
      exact (Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hrc_in_RC).symm⟩)
  have hr₀_in_C : (cs.compSt C).r₀ ∈ C := by
    have h1 : (cs.compSt C).r₀ ∈ (cs.compSt C).G₀.V :=
      hLC.hTV ▸ hLC.hR₀_sub hLC.hr₀_base
    rw [hG0C] at h1
    exact h1
  have hr₀_in_RC : (cs.compSt C).r₀ ∈ (cs.compSt C).R :=
    Finset.mem_union_left _ (subset_upClosure hLC.hr₀_base)
  have hrc_in_C : r_c ∈ C := by
    rw [hReq, Finset.mem_singleton] at hr₀_in_RC
    exact hr₀_in_RC ▸ hr₀_in_C
  have hrc_in_R : r_c ∈ cs.RF.R :=
    Finset.mem_biUnion.mpr ⟨C, hC, hrc_in_RC⟩
  have hroot_all : ∀ u ∈ (cs.compSt C).G.V, cs.RF.root u = r_c := by
    intro u hu
    rw [compLSF_RF_root_eq hI hC hu]
    have hsu : (cs.compSt C).RF.root u ∈ (cs.compSt C).R := (rootedForest_root_spec hRS_C hu).1
    rw [hReq, Finset.mem_singleton] at hsu
    exact hsu
  have hroot_only : ∀ u ∈ cs.G.V, cs.RF.root u = r_c → u ∈ (cs.compSt C).G.V := by
    intro u hu hru
    rw [← hI.hV_eq, Finset.mem_biUnion] at hu
    rcases hu with ⟨C', hC', huC'⟩
    by_cases hEq : C' = C
    · exact hEq ▸ huC'
    · have hru' := compLSF_RF_root_eq hI hC' huC'
      have hmem' : (cs.compSt C').RF.root u ∈ (cs.compSt C').R :=
        (rootedForest_root_spec (lsfInv_to_RS (hI.hCompLSF C' hC').1) huC').1
      have hV' : r_c ∈ (cs.compSt C').G.V := by
        rw [← hru, hru']; exact lsfInv_R_sub_V (hI.hCompLSF C' hC').1 hmem'
      have hV : r_c ∈ (cs.compSt C).G.V := lsfInv_R_sub_V hLC hrc_in_RC
      exact absurd hV (Finset.disjoint_left.mp (hI.hV_disj C' hC' C hC hEq) hV')
  exact ⟨hReq, hrc_in_C, hrc_in_R, hroot_all, hroot_only⟩

/-- For an inactive component `C`, the core rotation list `outCoreOrder tr ord r_c` at its unique
root `r_c` holds both ends of every core edge of `C` and nothing else, and every core edge of `C`
has both endpoints at `r_c` (so `r_c` is the sole core vertex incident to its edges). -/
theorem inactive_comp_cord_iff {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {depth : ℕ}
    {tr : BundleTreeState depth} {ord : ℕ → List End}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (ρ : Rotation tr.cs.G) (hρ : ρ.order = ord)
    {C : Finset ℕ} (hC : C ∈ components tr.cs.G₀) (hNotAct : C ∉ tr.activeComps)
    (hR1 : (tr.cs.compSt C).R.card = 1)
    (hCross : AsmFirstCrossInactiveInv tr)
    {v : ℕ} (hv : v ∈ (tr.cs.compSt C).G.V) :
    let r_c := tr.cs.RF.root v
    let cord := outCoreOrder tr ord
    let coreE_C := (coreGraph tr.cs.G tr.cs.lsf).E.filter fun e =>
      (coreGraph tr.cs.G tr.cs.lsf).tail e ∈ C
    (∀ x, x ∈ cord r_c ↔ x.1 ∈ coreE_C) ∧
    (∀ v' x, x ∈ cord v' → x.1 ∈ coreE_C → v' = r_c) ∧
    (∀ e ∈ coreE_C, e ∈ (tr.cs.compSt C).G.E ∧ e ∉ tr.cs.crossEdges) := by
  intro r_c cord coreE_C
  obtain ⟨hReq, hrc_C, hrc_R, hroot_all, hroot_only⟩ :=
    inactive_comp_root_unique hI hC hR1 hv
  have hCr := hCross C hC hNotAct
  have hC_sub_V : C ⊆ (tr.cs.compSt C).G.V := by
    have hLC := (hI.hCompLSF C hC).1
    have hG0C : (tr.cs.compSt C).G₀ = compGraph tr.cs.G₀ C := (hI.hCompLSF C hC).2.1
    intro u hu
    have hu0 : u ∈ (tr.cs.compSt C).G₀.V := by rw [hG0C]; exact hu
    rw [hLC.hGV_eq]
    exact Finset.mem_union_left _ (hLC.hTV.symm ▸ hu0)
  have hedge_in_C : ∀ e ∈ (coreGraph tr.cs.G tr.cs.lsf).E,
      (tr.cs.RF.root (tr.cs.G.tail e) = r_c ∨ tr.cs.RF.root (tr.cs.G.head e) = r_c) →
      e ∈ (tr.cs.compSt C).G.E ∧ e ∉ tr.cs.crossEdges ∧
      tr.cs.RF.root (tr.cs.G.tail e) = r_c ∧ tr.cs.RF.root (tr.cs.G.head e) = r_c := by
    intro e he hside
    have heG : e ∈ tr.cs.G.E := (Finset.mem_sdiff.mp he).1
    have hval := hI.hG_val e heG
    have hnc : e ∉ tr.cs.crossEdges := by
      intro hcr
      rcases hside with ht | hh
      · exact (hCr.2 e hcr).1 (hroot_only _ hval.1 ht)
      · exact (hCr.2 e hcr).2 (hroot_only _ hval.2 hh)
    obtain ⟨C', hC', heC'⟩ := hI.hEdge_cover e heG hnc
    have hends := hI.hNonCross_ends C' hC' e heC' hnc
    have hvC' := (hI.hCompLSF C' hC').1.hG_val e heC'
    have hEq : C' = C := by
      by_contra hne
      rcases hside with ht | hh
      · exact Finset.disjoint_left.mp (hI.hV_disj C' hC' C hC hne)
          (hends.1 ▸ hvC'.1) (hroot_only _ hval.1 ht)
      · exact Finset.disjoint_left.mp (hI.hV_disj C' hC' C hC hne)
          (hends.2 ▸ hvC'.2) (hroot_only _ hval.2 hh)
    subst hEq
    exact ⟨heC', hnc, hroot_all _ (hends.1 ▸ hvC'.1), hroot_all _ (hends.2 ▸ hvC'.2)⟩
  have hmem_coreE : ∀ e, e ∈ coreE_C ↔
      e ∈ (coreGraph tr.cs.G tr.cs.lsf).E ∧ (coreGraph tr.cs.G tr.cs.lsf).tail e = r_c := by
    intro e
    simp only [coreE_C, Finset.mem_filter]
    constructor
    · rintro ⟨he, htC⟩
      have hroot_r : (coreGraph tr.cs.G tr.cs.lsf).tail e ∈ (tr.cs.compSt C).R := by
        have h1 : (coreGraph tr.cs.G tr.cs.lsf).tail e ∈ tr.cs.RF.R :=
          (rootedForest_root_spec (compLSF_RF_isRSF hI)
            (hI.hG_val e (Finset.mem_sdiff.mp he).1).1).1
        have h1' : (coreGraph tr.cs.G tr.cs.lsf).tail e ∈
            (components tr.cs.G₀).biUnion (fun C' => (tr.cs.compSt C').R) := h1
        rw [Finset.mem_biUnion] at h1'
        rcases h1' with ⟨C', hC', hrC'⟩
        by_cases hEq : C' = C
        · exact hEq ▸ hrC'
        · exact absurd (hC_sub_V htC)
            (Finset.disjoint_left.mp (hI.hV_disj C' hC' C hC hEq)
              (lsfInv_R_sub_V (hI.hCompLSF C' hC').1 hrC'))
      rw [hReq, Finset.mem_singleton] at hroot_r
      exact ⟨he, hroot_r⟩
    · rintro ⟨he, htr⟩
      exact ⟨he, htr ▸ hrc_C⟩
  have hRS_lsf : tr.cs.lsf.F.IsRootedSpanningForestOf tr.cs.G := compLSF_RF_isRSF hI
  have hcord_iff : ∀ v' x, x ∈ cord v' ↔
      x.1 ∈ (coreGraph tr.cs.G tr.cs.lsf).E ∧ (coreGraph tr.cs.G tr.cs.lsf).src x = v' := by
    intro v' x
    have hcore_rot : cord = (coreRotation (L := tr.cs.lsf) ρ hI.hG_val hRS_lsf).order := by
      have hok : TourCordOK ord tr.cs.RF cord := by
        classical
        have hex : ∃ (C : ℝ) (ℓ : ℕ → ℝ) (_ : CompLSFInv C ℓ tr.cs) (ρ' : Rotation tr.cs.G),
            ρ'.order = ord := ⟨C_lsst, ℓ₀, hI, ρ, hρ⟩
        exact ⟨tr.cs, ⟨hex.choose, hex.choose_spec.choose, hex.choose_spec.choose_spec.choose,
          hex.choose_spec.choose_spec.choose_spec.choose,
          hex.choose_spec.choose_spec.choose_spec.choose_spec,
          by simp only [cord, outCoreOrder, hex, ↓reduceDIte]⟩, rfl⟩
      funext u
      rw [tourCordOK_eq_coreTour hok u, ← hρ]
      exact coreTour_eq_coreRotation (L := tr.cs.lsf) ρ hI.hG_val hRS_lsf u
    rw [hcore_rot]
    exact (coreRotation (L := tr.cs.lsf) ρ hI.hG_val hRS_lsf).mem_order v' x
  refine ⟨fun x => ?_, fun v' x hx heC => ?_, fun e heC => ?_⟩
  · rw [hcord_iff, hmem_coreE]
    constructor
    · rintro ⟨he, hsrc⟩
      have hside : tr.cs.RF.root (tr.cs.G.tail x.1) = r_c ∨
          tr.cs.RF.root (tr.cs.G.head x.1) = r_c := by
        cases h2 : x.2
        · right; simpa [MGraph.src, coreGraph, CompLSFState.lsf, h2] using hsrc
        · left; simpa [MGraph.src, coreGraph, CompLSFState.lsf, h2] using hsrc
      exact ⟨he, (hedge_in_C x.1 he hside).2.2.1⟩
    · rintro ⟨he, htr⟩
      have h2 := hedge_in_C x.1 he (Or.inl htr)
      refine ⟨he, ?_⟩
      cases hx2 : x.2
      · simpa [MGraph.src, coreGraph, CompLSFState.lsf, hx2] using h2.2.2.2
      · simpa [MGraph.src, coreGraph, CompLSFState.lsf, hx2] using h2.2.2.1
  · rw [hcord_iff] at hx
    rw [hmem_coreE] at heC
    have h2 := hedge_in_C x.1 heC.1 (Or.inl heC.2)
    rw [← hx.2]
    cases hx2 : x.2
    · simpa [MGraph.src, coreGraph, CompLSFState.lsf, hx2] using h2.2.2.2
    · simpa [MGraph.src, coreGraph, CompLSFState.lsf, hx2] using h2.2.2.1
  · rw [hmem_coreE] at heC
    have h2 := hedge_in_C e heC.1 (Or.inl heC.2)
    exact ⟨h2.1, h2.2.1⟩

/-- Every core edge of an inactive component `C` is disjoint from every currently active bundle. -/
theorem inactive_comp_edge_disj_active {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {depth : ℕ}
    {tr : BundleTreeState depth} (hI : CompLSFInv C_lsst ℓ₀ tr.cs)
    (hMod : RestartScurModelInv tr)
    {C : Finset ℕ} (hC : C ∈ components tr.cs.G₀) (hNotAct : C ∉ tr.activeComps)
    {e : ℕ} (heC : e ∈ (tr.cs.compSt C).G.E) (hnc : e ∉ tr.cs.crossEdges)
    {C' : Finset ℕ} (hC' : C' ∈ tr.activeComps) {b' : ℤ} (hb' : b' ∈ tr.activeBuckets C') :
    e ∉ (tr.bun (C', b')).edges := by
  intro hmem
  have hC'0 : C' ∈ components tr.cs.G₀ := hMod.1 hC'
  have heC' : e ∈ (tr.cs.compSt C').G.E := (hMod.2.2.2.2 C' hC' b' hb').2.1 hmem
  have hne : C ≠ C' := fun h => hNotAct (h ▸ hC')
  have ht1 : tr.cs.G.tail e ∈ (tr.cs.compSt C).G.V := by
    rw [← (hI.hNonCross_ends C hC e heC hnc).1]
    exact ((hI.hCompLSF C hC).1.hG_val e heC).1
  have ht2 : tr.cs.G.tail e ∈ (tr.cs.compSt C').G.V := by
    rw [← (hI.hNonCross_ends C' hC'0 e heC' hnc).1]
    exact ((hI.hCompLSF C' hC'0).1.hG_val e heC').1
  exact Finset.disjoint_left.mp (hI.hV_disj C hC C' hC'0 hne) ht1 ht2

end

/-! ## 3. Deterministic Word-RAM procedures for Phase 2 -/

@[expose] public section

/-- Preparation prefix of the nonempty (`len > 0`) branch: builds `uniqE`, `uniqB`, `specs`,
`assigns`, `csl`, `rPtr`, updates `ctH`, `ASM_SD_NSLOTS`, `lazySlotPtr`, and loads `bunH` into `r29`. -/
def asmFirstInitOneCompPrepStmt (bSort : ℕ) : Stmt :=
  .assign 11 (.reg 8) ;;
  .assign 12 (.bin .add (.reg 11) (.reg 9)) ;;
  .assign 13 (.bin .add (.reg 12) (.reg 9)) ;;
  forRange 14 (.const 0) (.reg 9)
    (.store (.bin .add (.reg 11) (.reg 14))
      (.bin .div (.load (.bin .add (.bin .add (.reg 6) (.const 1)) (.reg 14))) (.const 2))) ;;
  .call 27 (bSort + sortIdxMergeSort) [.reg 11, .reg 9, .reg 12] ;;
  .call 15 (bSort + sortIdxDedup) [.reg 11, .reg 9, .reg 13] ;;
  .assign 16 (.load (.bin .add (.reg 0) (.const ASM_SD_BKT))) ;;
  .assign 17 (.bin .add (.reg 13) (.reg 15)) ;;
  .assign 18 (.bin .add (.reg 17) (.reg 15)) ;;
  .assign 19 (.bin .add (.reg 18) (.reg 15)) ;;
  forRange 14 (.const 0) (.reg 15)
    (.assign 25 (.load (.bin .add (.reg 13) (.reg 14))) ;;
     .store (.bin .add (.reg 17) (.reg 14)) (.load (.bin .add (.reg 16) (.reg 25)))) ;;
  .call 27 (bSort + sortIdxMergeSort) [.reg 17, .reg 15, .reg 18] ;;
  .call 20 (bSort + sortIdxDedup) [.reg 17, .reg 15, .reg 19] ;;
  .assign 21 (.bin .add (.reg 19) (.reg 20)) ;;
  .assign 22 (.bin .add (.reg 21) (.reg 20)) ;;
  .assign 23 (.load (.bin .add (.reg 0) (.const ASM_SD_NSLOTS))) ;;
  forRange 14 (.const 0) (.reg 15)
    (.assign 25 (.load (.bin .add (.reg 13) (.reg 14))) ;;
     .assign 26 (.load (.bin .add (.reg 16) (.reg 25))) ;;
     .call 27 (bSort + sortIdxBinSearch) [.reg 19, .reg 20, .reg 26] ;;
     .assign 28 (.load (.bin .add (.reg 21) (.reg 27))) ;;
     .store (.bin .add (.reg 21) (.reg 27)) (.bin .add (.reg 28) (.const 1)) ;;
     .store (.bin .add (.reg 22) (.bin .mul (.const 2) (.reg 14))) (.reg 25) ;;
     .store (.bin .add (.bin .add (.reg 22) (.bin .mul (.const 2) (.reg 14))) (.const 1))
       (.bin .add (.reg 23) (.reg 27))) ;;
  .assign 24 (.bin .add (.reg 22) (.bin .mul (.const 2) (.reg 15))) ;;
  .assign 25 (.bin .add (.reg 24) (.bin .mul (.const 2) (.reg 20))) ;;
  .assign 26 (.bin .add (.reg 25) (.bin .mul (.const 2) (.reg 20))) ;;
  .assign 28 (.load (.bin .add (.reg 0) (.const ASM_SD_SLOTS))) ;;
  forRange 14 (.const 0) (.reg 20)
    (.assign 29 (.bin .add (.reg 23) (.reg 14)) ;;
     .assign 27 (.load (.bin .add (.reg 21) (.reg 14))) ;;
     .store (.bin .add (.reg 24) (.bin .mul (.const 2) (.reg 14))) (.reg 29) ;;
     .store (.bin .add (.bin .add (.reg 24) (.bin .mul (.const 2) (.reg 14))) (.const 1))
       (.bin .mul (.const 4) (.reg 27)) ;;
     .assign 27 (.load (.bin .add (.reg 19) (.reg 14))) ;;
     .store (.bin .add (.reg 25) (.bin .mul (.const 2) (.reg 14))) (.reg 27) ;;
     .store (.bin .add (.bin .add (.reg 25) (.bin .mul (.const 2) (.reg 14))) (.const 1))
       (.reg 29) ;;
     .store (.bin .add (.reg 28) (.reg 29)) (.reg 29)) ;;
  .store (.bin .add (.bin .add (.reg 10) (.bin .mul (.const 3) (.reg 2))) (.const 1)) (.reg 25) ;;
  .store (.bin .add (.bin .add (.reg 10) (.bin .mul (.const 3) (.reg 2))) (.const 2)) (.reg 20) ;;
  .store (.bin .add (.reg 0) (.const ASM_SD_NSLOTS)) (.bin .add (.reg 23) (.reg 20)) ;;
  .store (.reg 4) (.reg 13) ;;
  .store (.bin .add (.reg 4) (.const 1)) (.reg 15) ;;
  .store (.reg 26) (.reg 7) ;;
  .assign 29 (.load (.bin .add (.reg 0) (.const ASM_SD_BUN)))

/-- Nonempty (`len > 0`) branch of `asmFirstInitOneCompStmt`. -/
def asmFirstInitOneCompElseStmt (bSort fInitSlots : ℕ) : Stmt :=
  asmFirstInitOneCompPrepStmt bSort ;;
  .call 27 fInitSlots [.reg 29, .reg 1, .reg 20, .reg 24, .reg 15, .reg 22, .const 1, .reg 26,
    .bin .add (.reg 26) (.const 1)] ;;
  .ret (.reg 27)

/-- **Single newly active component initializer**, `[restH, tourH, c, v, lazySlotPtr, h]`:
1. Calls `fVertRoot [tourH, v, h]` to store `r_c = tr.cs.RF.root v` at `h` (`rPtr = h`, `h1 = h + 1`).
2. Calls `fTourList [tourH, r_c, h1]` to write `EndListAt` of `cord r_c` at `h1` (`len = mem[h1]`).
3. If `len = 0`, sets `ctH[3*c + 1] := h2`, `ctH[3*c + 2] := 0`, `lazySlotPtr[0..1] := [h2, 0]`,
   and returns `h2`.
4. Otherwise runs `asmFirstInitOneCompElseStmt`. -/
def asmFirstInitOneCompStmt (fVertRoot fTourList bSort fInitSlots : ℕ) : Stmt :=
  .call 6 fVertRoot [.reg 1, .reg 3, .reg 5] ;;
  .assign 7 (.load (.reg 5)) ;;
  .call 8 fTourList [.reg 1, .reg 7, .reg 6] ;;
  .assign 9 (.load (.reg 6)) ;;
  .assign 10 (.load (.bin .add (.reg 0) (.const ASM_SD_CT))) ;;
  .cond (.bin .eq (.reg 9) (.const 0))
    (.store (.bin .add (.bin .add (.reg 10) (.bin .mul (.const 3) (.reg 2))) (.const 1)) (.reg 8) ;;
     .store (.bin .add (.bin .add (.reg 10) (.bin .mul (.const 3) (.reg 2))) (.const 2)) (.const 0) ;;
     .store (.reg 4) (.reg 8) ;;
     .store (.bin .add (.reg 4) (.const 1)) (.const 0) ;;
     .ret (.reg 8))
    (asmFirstInitOneCompElseStmt bSort fInitSlots)

/-- **Phase 2 top-level driver**, `[restH, tourH, newCompsPtr, nNew, h]`:
allocates `lazyTbl` at `[h, h + 2 * nNew)`, loops `i = 0..nNew-1` calling `fInitOne` on each
`(c, v)` pair from `newCompsPtr`, then if `nSlots1 > nSlots0` calls `fInitSpan`
(`asmFirstInitSpanBody`) on the newly added slots `[nSlots0 .. nSlots1)`. Returns final heap. -/
def asmFirstNewActStmt (fInitOne fInitSpan : ℕ) : Stmt :=
  .assign 5 (.load (.bin .add (.reg 0) (.const ASM_SD_NSLOTS))) ;;
  .assign 6 (.bin .add (.reg 4) (.bin .mul (.const 2) (.reg 3))) ;;
  forRange 7 (.const 0) (.reg 3)
    (.assign 8 (.load (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 7)))) ;;
     .assign 9 (.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 7))) (.const 1))) ;;
     .call 6 fInitOne [.reg 0, .reg 1, .reg 8, .reg 9,
       .bin .add (.reg 4) (.bin .mul (.const 2) (.reg 7)), .reg 6]) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const ASM_SD_NSLOTS))) ;;
  .cond (.bin .lt (.reg 5) (.reg 8))
    (.assign 9 (.bin .sub (.reg 8) (.reg 5)) ;;
     .assign 10 (.load (.bin .add (.reg 0) (.const ASM_SD_BUN))) ;;
     .assign 11 (.load (.bin .add (.reg 0) (.const ASM_SD_SPAN))) ;;
     .assign 12 (.bin .add (.load (.bin .add (.reg 0) (.const ASM_SD_SLOTS))) (.reg 5)) ;;
     .assign 13 (.load (.bin .add (.reg 0) (.const ASM_SD_SPLIT))) ;;
     .assign 14 (.load (.bin .add (.reg 0) (.const ASM_SD_SPV))) ;;
     .assign 15 (.load (.bin .add (.reg 0) (.const ASM_SD_SPE))) ;;
     .assign 16 (.load (.bin .add (.reg 0) (.const ASM_SD_SPL))) ;;
     .call 6 fInitSpan [.reg 10, .reg 1, .reg 11, .const 0, .reg 9, .reg 12, .reg 6,
       .const 0, .const 0, .reg 13, .reg 14, .reg 15, .reg 16])
    .nop ;;
  .ret (.reg 6)

/-- Space bound for one call to `asmFirstInitOneCompStmt` on a component with `len = (cord r_c).length`,
`m_C` core edges, and `r` active buckets. -/
def newActOneSpace (TS : BundleTourSpec) (rQ len m_C r : ℕ) : ℕ :=
  rQ + 2 * TS.listSpace len + 3 * len + 30 * m_C + 10 * r + 1

end

public section

theorem asmFirstInitOneCompStmt_noRand (fVertRoot fTourList bSort fInitSlots : ℕ) :
    (asmFirstInitOneCompStmt fVertRoot fTourList bSort fInitSlots).NoRand := by
  simp [asmFirstInitOneCompStmt, asmFirstInitOneCompElseStmt, asmFirstInitOneCompPrepStmt,
    forRange, forUp, Stmt.NoRand]

theorem asmFirstNewActStmt_noRand (fInitOne fInitSpan : ℕ) :
    (asmFirstNewActStmt fInitOne fInitSpan).NoRand := by
  simp [asmFirstNewActStmt, forRange, forUp, Stmt.NoRand]

/-! ## 4. Generalization of `asmFirstInitSpan_runs` to an arbitrary existing spanner table -/

/-- **General run of `asmFirstInitSpanBody` on an existing bucket-spanner table `(S6, x6)`**:
exports the bundle graphs of `slots` (all currently `none` or arbitrary — `restartLoop_triple`
activates every slot in `slots` on `asmFirstInitSlotGraph S s`), updates `(S6, x6)` to
`spanAfter S6 (asmFirstInitSlotGraph S) slots`, preserves all memory below `h` outside
`bucketFoot spanTbl x6`, and meets the amortized bank/cost bound. -/
theorem asmFirstStepActivateSpans_runs {P : DSParams} {cap fExp bExport bSpan : ℕ}
    {p : Program} {ω : ℕ → Bool}
    (hfE : p.procs[fExp]? = some (asmFirstInitExpBody bExport))
    (hpExport : p.HasAt bExport [bundleExportGraphStmt])
    (hp : p.HasAt bSpan (bucketSpannerProcs P.impl bSpan))
    {slotCap vCap eCap bunTbl tourH spanTbl x3 slotsPtr h x7 x8 pos : ℕ} {slots : List ℕ}
    {S : Fin slotCap → Option BundleState} {m : BundleTableMeta slotCap}
    {S6 : BucketSpannerState cap} {x6 : BucketSpannerMeta P.L cap} {mem : ℕ → ℕ}
    (hw : 16 ≤ 2 ^ P.w) (hLW : P.L < 2 ^ P.w) (hSplitW : P.splitBound < 2 ^ P.w)
    (hVW : P.vCap < 2 ^ P.w) (hEW : P.eCap < 2 ^ P.w)
    (hrep : BundleTableRepAt slotCap vCap eCap bunTbl S m mem)
    (hfoot : ∀ a, bundleTableFoot eCap bunTbl m a → a < h)
    (hact : ∀ s ∈ slots, ∃ hs : s < slotCap, ∃ B, S ⟨s, hs⟩ = some B)
    (hlist : ListAt mem slotsPtr slots) (hsl : slotsPtr + slots.length ≤ h)
    (hz : ZeroFrom mem h)
    (htblw : bunTbl + bundleTableFixedSize slotCap eCap < 2 ^ P.w)
    (hok : ∀ s ∈ slots, SpanGraphOK P (asmFirstInitSlotGraph S s))
    (hcap : ∀ s ∈ slots, s < cap)
    (hrep6 : (bucketSpannerRep P cap).rep spanTbl S6 x6 mem)
    (hfoot6 : ∀ a, (bucketSpannerRep P cap).foot spanTbl x6 a → a < h)
    (hspanL : ∀ a, slotsPtr ≤ a → a < slotsPtr + slots.length →
      ¬ (bucketSpannerRep P cap).foot spanTbl x6 a)
    (hfit : h + 6 * slots.length + 10 * edgeTot S slots +
      (slots.map fun s => bundleExportSpace (slotB S s)).sum +
      (slots.map fun s => spanActivateSpace P (asmFirstInitSlotGraph S s)).sum < 2 ^ P.w) :
    ∃ o st' c x6', Runs P.w p ω (asmFirstInitSpanBody fExp (bSpan + bsIdxOp0 + 0))
        (startState [bunTbl, tourH, spanTbl, x3, slots.length, slotsPtr, h, x7, x8, P.splitBound,
          P.vCap, P.eCap, P.L] mem pos) o st' c ∧
      (bucketSpannerRep P cap).rep spanTbl
        (spanAfter S6 (asmFirstInitSlotGraph S) slots) x6' st'.mem ∧
      (∀ a, (bucketSpannerRep P cap).foot spanTbl x6' a →
        (bucketSpannerRep P cap).foot spanTbl x6 a ∨ (h ≤ a ∧ a < o.value)) ∧
      (∀ a < h, ¬ (bucketSpannerRep P cap).foot spanTbl x6 a → st'.mem a = mem a) ∧
      h ≤ o.value ∧
      o.value ≤ h + 6 * slots.length + 10 * edgeTot S slots +
        (slots.map fun s => bundleExportSpace (slotB S s)).sum +
        (slots.map fun s => spanActivateSpace P (asmFirstInitSlotGraph S s)).sum ∧
      ZeroFrom st'.mem o.value ∧
      c + specPhi P (spanAfter S6 (asmFirstInitSlotGraph S) slots) ≤
        specPhi P S6 +
        (slots.map fun s => bundleExportCost (slotB S s)).sum +
        (slots.map fun s => spanActivateCost P (asmFirstInitSlotGraph S s)).sum +
        200 * slots.length + 200 := by
  set g := asmFirstInitSlotGraph S with hg
  set st0 := startState [bunTbl, tourH, spanTbl, x3, slots.length, slotsPtr, h, x7, x8, P.splitBound,
    P.vCap, P.eCap, P.L] mem pos with hst0
  obtain ⟨o5, st5, c5, hrun5, hov5, hz5, -, hexp5, hfr5, hc5⟩ :=
    asmFirstInitExp_runs (w := P.w) (p := p) (ω := ω) (tourH := tourH) (pos := pos) hpExport hw
      hrep hfoot hact hlist hsl hz (by omega) htblw
  set h1 := o5.value with hh1def
  set st1 : State := { st5 with regs := Function.update st0.regs 13 h1 } with hst1
  have hcall5 : Runs P.w p ω (.call 13 fExp [.reg 0, .reg 1, .reg 4, .reg 5, .reg 6]) st0
      .normal st1 (argsSize [.reg 0, .reg 1, .reg 4, .reg 5, .reg 6] + c5 + 1) :=
    runs_call_iff.mpr ⟨[bunTbl, tourH, slots.length, slotsPtr, h], _, o5, st5, c5,
      by simp [evalArgs, Expr.eval, hst0, startState], hfE, hrun5, rfl, rfl, rfl⟩
  have hlist5 : ListAt st5.mem slotsPtr slots := fun i hi => by
    rw [hfr5 _ (by omega)]; exact hlist i hi
  have hrep6_5 : (bucketSpannerRep P cap).rep spanTbl S6 x6 st5.mem :=
    (bucketSpannerRep_local P cap spanTbl S6 x6 mem st5.mem
      fun a ha => (hfr5 a (hfoot6 a ha)).symm).1 hrep6
  have LH : LoopHyps P cap st1.regs spanTbl slotsPtr h h1 S6 x6 g slots st5.mem :=
    { hR2 := by simp [hst1, hst0, startState]
      hR4 := by simp [hst1, hst0, startState]
      hR5 := by simp [hst1, hst0, startState]
      hR6 := by simp [hst1, hst0, startState]
      hR9 := by simp [hst1, hst0, startState]
      hR10 := by simp [hst1, hst0, startState]
      hR11 := by simp [hst1, hst0, startState]
      hR12 := by simp [hst1, hst0, startState]
      hw16 := hw, hL := hLW, hSplit := hSplitW, hV := hVW, hE := hEW
      hlist := hlist5, hlist_h := hsl, hlist_free := hspanL
      hh1 := by omega, hexp := fun i hi => ⟨_, hexp5 i hi, rfl⟩
      hok := hok, hact := hcap, hrep := hrep6_5
      hfoot := fun a ha => by have := hfoot6 a ha; omega
      hz := hz5, hspace := by omega }
  obtain ⟨oL, st2, cL, hrunL, hpostL, hcL⟩ :=
    restartLoop_triple hp LH st1 ω ⟨rfl, fun _ _ => rfl, by simp [hst1]⟩
  cases oL with
  | returned u => exact absurd hpostL (by simp)
  | normal =>
  obtain ⟨-, -, hc1, hc2, hz2, hfr2, hph, x6n, hrep6n, hft6n⟩ := hpostL
  rw [List.take_length] at hrep6n
  have hsum := sum_range_getD (fun s => spanActivateSpace P (g s)) slots
  have hLc := loopCost_le P S6 g slots hph
  rw [List.take_length, List.take_zero, spanAfter_nil] at hLc
  simp only [Expr.size_reg, Expr.size_const, Nat.sub_zero] at hcL
  have hret : Runs P.w p ω (.ret (.reg 13)) st2 (.returned (st2.regs 13)) st2 2 :=
    runs_ret_iff.mpr ⟨_, by simp [Expr.eval], rfl, rfl, rfl⟩
  have t1 := runs_seq_iff.mpr (Or.inr ⟨st2, _, _, hrunL, hret, rfl⟩)
  have t2 := runs_seq_iff.mpr (Or.inr ⟨st1, _, _, hcall5, t1, rfl⟩)
  refine ⟨_, _, _, x6n, t2, hrep6n, ?_, ?_, ?_, ?_, hz2, ?_⟩
  · intro a ha
    rcases hft6n a ha with h6 | ⟨hle, hlt⟩
    · exact Or.inl h6
    · exact Or.inr ⟨by omega, hlt⟩
  · intro a ha hn'
    rw [hfr2 a (by omega) hn', hfr5 a ha]
  · show h ≤ st2.regs 13; omega
  · show st2.regs 13 ≤ _; rw [hsum] at hc2; omega
  · simp only [argsSize, Expr.size] at hcL ⊢; omega

end

end MinCostFlow.SparseCore.Program
