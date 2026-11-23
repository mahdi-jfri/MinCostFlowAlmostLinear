module

public import MinCostFlow.SparseCore.Program.CompBatchStepCommon

/-!
# Generic Per-Component to Global Forest-Cut Lifting (`CompBatchStepLift`)

Provides shared pure graph/forest lemmas used by all three single-update step verifiers
(`CompBatchStepIns`, `CompBatchStepDel`, `CompBatchStepSplit`):
* Monotonicity of `applyLSFUpdate` on `R_orig`, `RF.R`, and `RF.F.E`.
* `compRF_cuts_lift_one_insDel`: lifts a single-component cut log to global `cs.RF` for
  same-component `.insert` or `.delete`.
* `compRF_cuts_lift_two_insDel`: lifts two distinct components' cut logs to global `cs.RF` for
  cross-component `.insert` or `.delete`.
* `compRF_cuts_lift_split`: lifts a single-component cut log for `.split v v' St Sh` to global
  `cs.RF`, exposing the exact hypotheses of `compForestCutsValid_of_splitRoot`.
* `compStep_cnts_le_of_lift` and `compStep_cutBuf_disj`: buffer-index separation helpers for
  two-component dispatches.
-/

namespace MinCostFlow.SparseCore.Program

open MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore

@[expose] public section

/-! ## 1. `applyLSFUpdate` monotonicity -/

lemma compApplyLSFUpdate_R_orig_sub (S : LSFState) (u : Update) :
    S.R_orig ⊆ (applyLSFUpdate S u).R_orig := by
  have hTH : (applyLSFUpdate S u).TH = S.TH := by cases u <;> rfl
  have hr₀ : (applyLSFUpdate S u).r₀ = S.r₀ := by cases u <;> rfl
  have hbase : S.R₀_base ⊆ (applyLSFUpdate S u).R₀_base := by
    cases u with
    | insert _ _ _ => exact Finset.subset_union_left
    | delete _ => exact Finset.subset_union_left
    | split _ _ _ _ =>
      dsimp only [applyLSFUpdate]; split_ifs
      · exact Finset.subset_insert _ _
      · exact Finset.Subset.refl _
  intro x hx
  rw [LSFState.R_orig, hTH, hr₀, mem_upClosure_iff]
  rw [LSFState.R_orig, mem_upClosure_iff] at hx
  obtain ⟨w, hw, haw⟩ := hx
  exact ⟨w, hbase hw, haw⟩

lemma compApplyLSFUpdate_R_sub (S : LSFState) (u : Update) :
    S.RF.R ⊆ (applyLSFUpdate S u).RF.R := by
  have hiso : S.isolatedVerts ⊆ (applyLSFUpdate S u).isolatedVerts := by
    cases u with
    | insert _ _ _ => exact Finset.Subset.refl _
    | delete _ => exact Finset.Subset.refl _
    | split _ _ _ _ => exact Finset.subset_insert _ _
  exact Finset.union_subset_union (compApplyLSFUpdate_R_orig_sub S u) hiso

lemma compApplyLSFUpdate_RF_E_sub {S : LSFState} (hInv : LSFStructInv S) (u : Update) :
    (applyLSFUpdate S u).RF.F.E ⊆ S.RF.F.E := by
  have hT₀ : (applyLSFUpdate S u).T₀ = S.T₀ := by cases u <;> rfl
  have hr₀ : (applyLSFUpdate S u).r₀ = S.r₀ := by cases u <;> rfl
  have hπ : (applyLSFUpdate S u).π = S.π := by cases u <;> rfl
  have hTH : (applyLSFUpdate S u).TH = hldAuxTree S.T₀ S.r₀ := by cases u <;> rfl
  have hR₀' : (applyLSFUpdate S u).R₀_base ⊆ S.T₀.V := by
    cases u with
    | insert _ _ _ => exact Finset.union_subset hInv.hR₀_sub (fun _ hx => (Finset.mem_filter.mp hx).2)
    | delete _ => exact Finset.union_subset hInv.hR₀_sub (fun _ hx => (Finset.mem_filter.mp hx).2)
    | split _ _ _ _ =>
      dsimp only [applyLSFUpdate]; split_ifs with hv
      · exact Finset.insert_subset_iff.mpr ⟨hv, hInv.hR₀_sub⟩
      · exact hInv.hR₀_sub
  have hbf1 : IsBranchFree S.T₀ S.r₀ S.R_orig := upClosure_isBranchFree hInv.hT₀ hInv.hR₀_sub
  have hbf2 : IsBranchFree S.T₀ S.r₀ (applyLSFUpdate S u).R_orig := by
    have : (applyLSFUpdate S u).R_orig = upClosure (hldAuxTree S.T₀ S.r₀) S.r₀ (applyLSFUpdate S u).R₀_base := by
      rw [LSFState.R_orig, hTH, hr₀]
    rw [this]; exact upClosure_isBranchFree hInv.hT₀ hR₀'
  have hdel := deletedEdges_mono hInv.hT₀ hbf1 hbf2 ⟨S.r₀, hInv.r₀_mem_R_orig⟩
    (compApplyLSFUpdate_R_orig_sub S u) S.π hInv.hord
  intro e he
  dsimp only [LSFState.RF, forestGivenRoots] at he ⊢
  rw [hT₀, hr₀, hπ] at he
  exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp he).1, fun hd => (Finset.mem_sdiff.mp he).2 (hdel hd)⟩

/-! ## 2. Global cut-lifting for single- and two-component `.insert` / `.delete` -/

private lemma compRF_F_disj {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {D₁ D₂ : Finset ℕ}
    (hD₁ : D₁ ∈ components cs.G₀) (hD₂ : D₂ ∈ components cs.G₀) (hne : D₁ ≠ D₂)
    {f : ℕ} (hf1 : f ∈ (cs.compSt D₁).RF.F.E) : f ∉ (cs.compSt D₂).RF.F.E := by
  intro hf2
  have hRS1 := lsfInv_to_RS (hI.hCompLSF D₁ hD₁).1
  have hRS2 := lsfInv_to_RS (hI.hCompLSF D₂ hD₂).1
  have ht1 := hRS1.2.1 ▸ (hRS1.1.1 f hf1).1
  have ht2 := hRS2.2.1 ▸ (hRS2.1.1 f hf2).1
  have hteq : (cs.compSt D₁).RF.F.tail f = (cs.compSt D₂).RF.F.tail f :=
    ((compLSF_RF_sub_comp hI hD₁).2.2 f hf1).1.trans ((compLSF_RF_sub_comp hI hD₂).2.2 f hf2).1.symm
  exact Finset.disjoint_left.mp (hI.hV_disj D₁ hD₁ D₂ hD₂ hne) ht1 (hteq ▸ ht2)

/-- Lift a single component's cut log to global `cs.RF` for a same-component `.insert` or `.delete`. -/
lemma compRF_cuts_lift_one_insDel {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {numComps vCap eCap : ℕ}
    {compOf : Fin numComps → Finset ℕ}
    {edgeC1 edgeC2 gtVert ghVert : ℕ → ℕ} {gtList ghList : ℕ → List ℕ}
    {cs : CompLSFState} {u u_c : Update} {c : Fin numComps} {cuts : List (ℕ × ℕ)}
    (hI : CompLSFInv C_lsst ℓ₀ cs)
    (hT : CompEdgeTrack numComps vCap eCap compOf edgeC1 edgeC2 gtVert ghVert gtList ghList cs)
    (hu : cs.G.UpdateIsValid u)
    (hSelf : (compLSFStepSingle cs u).compSt (compOf c) = applyLSFUpdate (cs.compSt (compOf c)) u_c)
    (hOther : ∀ D ∈ components cs.G₀, D ≠ compOf c → (compLSFStepSingle cs u).compSt D = cs.compSt D)
    (hVc : ((compLSFStepSingle cs u).compSt (compOf c)).G.V = (cs.compSt (compOf c)).G.V)
    (hEf : 1 ≤ (compGraph cs.G₀ (compOf c)).m →
      let Sc := cs.compSt (compOf c)
      let Sc' := applyLSFUpdate Sc u_c
      CompForestCutsValid vCap Sc.RF cuts ∧
      (cuts.map Prod.fst).Nodup ∧ (cuts.map Prod.fst).toFinset = Sc.RF.F.E \ Sc'.RF.F.E ∧
      (cuts.map Prod.snd).Nodup ∧ (cuts.map Prod.snd).toFinset = Sc'.RF.R \ Sc.RF.R)
    (hIso : (compGraph cs.G₀ (compOf c)).m = 0 → cuts = []) :
    let cs' := compLSFStepSingle cs u
    CompForestCutsValid vCap cs.RF cuts ∧
    (cuts.map Prod.fst).Nodup ∧
    (cuts.map Prod.fst).toFinset = cs.RF.F.E \ cs'.RF.F.E ∧
    cs'.RF.F.E ⊆ cs.RF.F.E ∧
    (cuts.map Prod.snd).Nodup ∧
    (cuts.map Prod.snd).toFinset = cs'.RF.R \ cs.RF.R ∧
    cs.RF.R ⊆ cs'.RF.R := by
  classical
  intro cs'
  have hCmem : compOf c ∈ components cs.G₀ := hT.compOf_mem c
  have hI' : CompLSFInv C_lsst ℓ₀ cs' := compLSFInv_step hI hu
  have hE_c_sub : (cs'.compSt (compOf c)).RF.F.E ⊆ (cs.compSt (compOf c)).RF.F.E := by
    rw [hSelf]; exact compApplyLSFUpdate_RF_E_sub (LSFInvWith.toStructInv (hI.hCompLSF _ hCmem).1) _
  have hR_c_sub : (cs.compSt (compOf c)).RF.R ⊆ (cs'.compSt (compOf c)).RF.R := by
    rw [hSelf]; exact compApplyLSFUpdate_R_sub _ _
  have hEsub : cs'.RF.F.E ⊆ cs.RF.F.E := fun f hf => by
    obtain ⟨D, hD, hfD⟩ := Finset.mem_biUnion.mp hf
    refine Finset.mem_biUnion.mpr ⟨D, hD, ?_⟩
    by_cases hDc : D = compOf c
    · subst hDc; exact hE_c_sub hfD
    · rw [hOther D hD hDc] at hfD; exact hfD
  have hRsub : cs.RF.R ⊆ cs'.RF.R := fun r hr => by
    obtain ⟨D, hD, hrD⟩ := Finset.mem_biUnion.mp hr
    refine Finset.mem_biUnion.mpr ⟨D, hD, ?_⟩
    by_cases hDc : D = compOf c
    · subst hDc; exact hR_c_sub hrD
    · rw [hOther D hD hDc]; exact hrD
  have hEdiff : cs.RF.F.E \ cs'.RF.F.E =
      (cs.compSt (compOf c)).RF.F.E \ (cs'.compSt (compOf c)).RF.F.E := by
    ext f; simp only [Finset.mem_sdiff, CompLSFState.RF, Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨D, hD, hfD⟩, hnot⟩
      have hDc : D = compOf c := by
        by_contra hne; exact hnot ⟨D, hD, by rw [hOther D hD hne]; exact hfD⟩
      subst hDc; exact ⟨hfD, fun hf' => hnot ⟨compOf c, hCmem, hf'⟩⟩
    · rintro ⟨hf, hfnot⟩
      refine ⟨⟨compOf c, hCmem, hf⟩, ?_⟩
      rintro ⟨D, hD, hfD⟩
      by_cases hDc : D = compOf c
      · exact hfnot (hDc ▸ hfD)
      · rw [hOther D hD hDc] at hfD; exact compRF_F_disj hI hD hCmem hDc hfD hf
  have hRdiff : cs'.RF.R \ cs.RF.R =
      (cs'.compSt (compOf c)).RF.R \ (cs.compSt (compOf c)).RF.R := by
    ext r; simp only [Finset.mem_sdiff, CompLSFState.RF, Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨D, hD, hrD⟩, hnot⟩
      have hDc : D = compOf c := by
        by_contra hne; exact hnot ⟨D, hD, by rw [hOther D hD hne] at hrD; exact hrD⟩
      subst hDc; exact ⟨hrD, fun hr' => hnot ⟨compOf c, hCmem, hr'⟩⟩
    · rintro ⟨hr, hrnot⟩
      refine ⟨⟨compOf c, hCmem, hr⟩, ?_⟩
      rintro ⟨D, hD, hrD⟩
      by_cases hDc : D = compOf c
      · exact hrnot (hDc ▸ hrD)
      · have hrV_D : r ∈ (cs.compSt D).G.V := (lsfInv_to_RS (hI.hCompLSF D hD).1).2.2.1 hrD
        have hrV_c : r ∈ (cs'.compSt (compOf c)).G.V := (lsfInv_to_RS (hI'.hCompLSF _ hCmem).1).2.2.1 hr
        exact Finset.disjoint_left.mp (hI.hV_disj D hD (compOf c) hCmem hDc) hrV_D (hVc ▸ hrV_c)
  by_cases hpos : 1 ≤ (compGraph cs.G₀ (compOf c)).m
  · obtain ⟨hval, hndE, hsE, hndR, hsR⟩ := hEf hpos
    exact ⟨compForestCutsValid_comp_to_global hI hT c hval, hndE,
      by rw [hEdiff, hSelf]; exact hsE, hEsub, hndR, by rw [hRdiff, hSelf]; exact hsR, hRsub⟩
  · have hm0 : (compGraph cs.G₀ (compOf c)).m = 0 := by omega
    obtain rfl := hIso hm0
    obtain ⟨hE0, hR0, _⟩ := isoComp_props hI hCmem hm0
    obtain ⟨hE0', hR0', _⟩ := isoComp_props hI' hCmem hm0
    refine ⟨trivial, List.nodup_nil, by rw [hEdiff, hE0, hE0']; simp, hEsub, List.nodup_nil, ?_, hRsub⟩
    rw [hRdiff]; change ∅ = (cs'.compSt (compOf c)).R \ (cs.compSt (compOf c)).R
    rw [hR0', hR0, hVc]; simp

/-- Lift two distinct components' cut logs (`c1 ≠ c2`) to global `cs.RF` for a cross-component
`.insert` (where each component's forest edges and roots match the single self-loop `.insert`
followed by `.delete`). -/
lemma compRF_cuts_lift_two_insDel {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {numComps vCap eCap : ℕ}
    {compOf : Fin numComps → Finset ℕ}
    {edgeC1 edgeC2 gtVert ghVert : ℕ → ℕ} {gtList ghList : ℕ → List ℕ}
    {cs : CompLSFState} {u u1 u2 : Update} {c1 c2 : Fin numComps} {cuts1 cuts2 : List (ℕ × ℕ)}
    (hI : CompLSFInv C_lsst ℓ₀ cs)
    (hT : CompEdgeTrack numComps vCap eCap compOf edgeC1 edgeC2 gtVert ghVert gtList ghList cs)
    (hu : cs.G.UpdateIsValid u) (hne : c1 ≠ c2)
    (hFE1 : ((compLSFStepSingle cs u).compSt (compOf c1)).RF.F.E =
      (applyLSFUpdate (cs.compSt (compOf c1)) u1).RF.F.E)
    (hR1 : ((compLSFStepSingle cs u).compSt (compOf c1)).RF.R =
      (applyLSFUpdate (cs.compSt (compOf c1)) u1).RF.R)
    (hFE2 : ((compLSFStepSingle cs u).compSt (compOf c2)).RF.F.E =
      (applyLSFUpdate (cs.compSt (compOf c2)) u2).RF.F.E)
    (hR2 : ((compLSFStepSingle cs u).compSt (compOf c2)).RF.R =
      (applyLSFUpdate (cs.compSt (compOf c2)) u2).RF.R)
    (hOther : ∀ D ∈ components cs.G₀, D ≠ compOf c1 → D ≠ compOf c2 →
      (compLSFStepSingle cs u).compSt D = cs.compSt D)
    (hV1 : ((compLSFStepSingle cs u).compSt (compOf c1)).G.V = (cs.compSt (compOf c1)).G.V)
    (hV2 : ((compLSFStepSingle cs u).compSt (compOf c2)).G.V = (cs.compSt (compOf c2)).G.V)
    (hEf1 : 1 ≤ (compGraph cs.G₀ (compOf c1)).m →
      let Sc := cs.compSt (compOf c1)
      let Sc' := applyLSFUpdate Sc u1
      CompForestCutsValid vCap Sc.RF cuts1 ∧
      (cuts1.map Prod.fst).Nodup ∧ (cuts1.map Prod.fst).toFinset = Sc.RF.F.E \ Sc'.RF.F.E ∧
      (cuts1.map Prod.snd).Nodup ∧ (cuts1.map Prod.snd).toFinset = Sc'.RF.R \ Sc.RF.R)
    (hIso1 : (compGraph cs.G₀ (compOf c1)).m = 0 → cuts1 = [])
    (hEf2 : 1 ≤ (compGraph cs.G₀ (compOf c2)).m →
      let Sc := cs.compSt (compOf c2)
      let Sc' := applyLSFUpdate Sc u2
      CompForestCutsValid vCap Sc.RF cuts2 ∧
      (cuts2.map Prod.fst).Nodup ∧ (cuts2.map Prod.fst).toFinset = Sc.RF.F.E \ Sc'.RF.F.E ∧
      (cuts2.map Prod.snd).Nodup ∧ (cuts2.map Prod.snd).toFinset = Sc'.RF.R \ Sc.RF.R)
    (hIso2 : (compGraph cs.G₀ (compOf c2)).m = 0 → cuts2 = []) :
    let cs' := compLSFStepSingle cs u
    let cuts := cuts1 ++ cuts2
    CompForestCutsValid vCap cs.RF cuts ∧
    (cuts.map Prod.fst).Nodup ∧
    (cuts.map Prod.fst).toFinset = cs.RF.F.E \ cs'.RF.F.E ∧
    cs'.RF.F.E ⊆ cs.RF.F.E ∧
    (cuts.map Prod.snd).Nodup ∧
    (cuts.map Prod.snd).toFinset = cs'.RF.R \ cs.RF.R ∧
    cs.RF.R ⊆ cs'.RF.R := by
  classical
  intro cs' cuts
  have hC1 : compOf c1 ∈ components cs.G₀ := hT.compOf_mem c1
  have hC2 : compOf c2 ∈ components cs.G₀ := hT.compOf_mem c2
  have hCne : compOf c1 ≠ compOf c2 := fun h => hne (hT.hBij.1 h)
  have hI' : CompLSFInv C_lsst ℓ₀ cs' := compLSFInv_step hI hu
  have hPart : ∀ (c : Fin numComps) (cts : List (ℕ × ℕ)),
      ((cs'.compSt (compOf c)).G.V = (cs.compSt (compOf c)).G.V) →
      (1 ≤ (compGraph cs.G₀ (compOf c)).m →
        CompForestCutsValid vCap (cs.compSt (compOf c)).RF cts ∧
        (cts.map Prod.fst).Nodup ∧
        (cts.map Prod.fst).toFinset = (cs.compSt (compOf c)).RF.F.E \ (cs'.compSt (compOf c)).RF.F.E ∧
        (cts.map Prod.snd).Nodup ∧
        (cts.map Prod.snd).toFinset = (cs'.compSt (compOf c)).RF.R \ (cs.compSt (compOf c)).RF.R) →
      ((compGraph cs.G₀ (compOf c)).m = 0 → cts = []) →
      CompForestCutsValid vCap (cs.compSt (compOf c)).RF cts ∧
      (cts.map Prod.fst).Nodup ∧
      (cts.map Prod.fst).toFinset = (cs.compSt (compOf c)).RF.F.E \ (cs'.compSt (compOf c)).RF.F.E ∧
      (cts.map Prod.snd).Nodup ∧
      (cts.map Prod.snd).toFinset = (cs'.compSt (compOf c)).RF.R \ (cs.compSt (compOf c)).RF.R := by
    intro c cts hVeq hE hIs
    by_cases hp : 1 ≤ (compGraph cs.G₀ (compOf c)).m
    · exact hE hp
    · have hm0 : (compGraph cs.G₀ (compOf c)).m = 0 := by omega
      obtain rfl := hIs hm0
      obtain ⟨hE0, hR0, _⟩ := isoComp_props hI (hT.compOf_mem c) hm0
      obtain ⟨hE0', hR0', _⟩ := isoComp_props hI' (hT.compOf_mem c) hm0
      exact ⟨trivial, List.nodup_nil, by rw [hE0, hE0']; simp, List.nodup_nil,
        by change ∅ = (cs'.compSt (compOf c)).R \ (cs.compSt (compOf c)).R; rw [hR0', hR0, hVeq]; simp⟩
  obtain ⟨hval1, hndE1, hsE1, hndR1, hsR1⟩ :=
    hPart c1 cuts1 hV1 (by rw [hFE1, hR1]; exact hEf1) hIso1
  obtain ⟨hval2, hndE2, hsE2, hndR2, hsR2⟩ :=
    hPart c2 cuts2 hV2 (by rw [hFE2, hR2]; exact hEf2) hIso2
  have hE1_sub : (cs'.compSt (compOf c1)).RF.F.E ⊆ (cs.compSt (compOf c1)).RF.F.E := by
    rw [hFE1]; exact compApplyLSFUpdate_RF_E_sub (LSFInvWith.toStructInv (hI.hCompLSF _ hC1).1) _
  have hE2_sub : (cs'.compSt (compOf c2)).RF.F.E ⊆ (cs.compSt (compOf c2)).RF.F.E := by
    rw [hFE2]; exact compApplyLSFUpdate_RF_E_sub (LSFInvWith.toStructInv (hI.hCompLSF _ hC2).1) _
  have hR1_sub : (cs.compSt (compOf c1)).RF.R ⊆ (cs'.compSt (compOf c1)).RF.R := by
    rw [hR1]; exact compApplyLSFUpdate_R_sub _ _
  have hR2_sub : (cs.compSt (compOf c2)).RF.R ⊆ (cs'.compSt (compOf c2)).RF.R := by
    rw [hR2]; exact compApplyLSFUpdate_R_sub _ _
  have hEsub : cs'.RF.F.E ⊆ cs.RF.F.E := fun f hf => by
    obtain ⟨D, hD, hfD⟩ := Finset.mem_biUnion.mp hf
    refine Finset.mem_biUnion.mpr ⟨D, hD, ?_⟩
    by_cases h1 : D = compOf c1
    · subst h1; exact hE1_sub hfD
    · by_cases h2 : D = compOf c2
      · subst h2; exact hE2_sub hfD
      · rw [hOther D hD h1 h2] at hfD; exact hfD
  have hRsub : cs.RF.R ⊆ cs'.RF.R := fun r hr => by
    obtain ⟨D, hD, hrD⟩ := Finset.mem_biUnion.mp hr
    refine Finset.mem_biUnion.mpr ⟨D, hD, ?_⟩
    by_cases h1 : D = compOf c1
    · subst h1; exact hR1_sub hrD
    · by_cases h2 : D = compOf c2
      · subst h2; exact hR2_sub hrD
      · rw [hOther D hD h1 h2]; exact hrD
  have hEdiff : cs.RF.F.E \ cs'.RF.F.E =
      ((cs.compSt (compOf c1)).RF.F.E \ (cs'.compSt (compOf c1)).RF.F.E) ∪
      ((cs.compSt (compOf c2)).RF.F.E \ (cs'.compSt (compOf c2)).RF.F.E) := by
    ext f; simp only [Finset.mem_sdiff, Finset.mem_union, CompLSFState.RF, Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨D, hD, hfD⟩, hnot⟩
      by_cases h1 : D = compOf c1
      · subst h1; left; exact ⟨hfD, fun h => hnot ⟨compOf c1, hC1, h⟩⟩
      · by_cases h2 : D = compOf c2
        · subst h2; right; exact ⟨hfD, fun h => hnot ⟨compOf c2, hC2, h⟩⟩
        · exact absurd ⟨D, hD, by rw [hOther D hD h1 h2]; exact hfD⟩ hnot
    · rintro (⟨hf1, hnot1⟩ | ⟨hf2, hnot2⟩)
      · refine ⟨⟨compOf c1, hC1, hf1⟩, ?_⟩
        rintro ⟨D, hD, hfD⟩
        by_cases h1 : D = compOf c1
        · exact hnot1 (h1 ▸ hfD)
        · by_cases h2 : D = compOf c2
          · subst h2; exact compRF_F_disj hI hC1 hC2 hCne hf1 (hE2_sub hfD)
          · rw [hOther D hD h1 h2] at hfD; exact compRF_F_disj hI hC1 hD (Ne.symm h1) hf1 hfD
      · refine ⟨⟨compOf c2, hC2, hf2⟩, ?_⟩
        rintro ⟨D, hD, hfD⟩
        by_cases h2 : D = compOf c2
        · exact hnot2 (h2 ▸ hfD)
        · by_cases h1 : D = compOf c1
          · subst h1; exact compRF_F_disj hI hC2 hC1 hCne.symm hf2 (hE1_sub hfD)
          · rw [hOther D hD h1 h2] at hfD; exact compRF_F_disj hI hC2 hD (Ne.symm h2) hf2 hfD
  have hRdiff : cs'.RF.R \ cs.RF.R =
      ((cs'.compSt (compOf c1)).RF.R \ (cs.compSt (compOf c1)).RF.R) ∪
      ((cs'.compSt (compOf c2)).RF.R \ (cs.compSt (compOf c2)).RF.R) := by
    ext r; simp only [Finset.mem_sdiff, Finset.mem_union, CompLSFState.RF, Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨D, hD, hrD⟩, hnot⟩
      by_cases h1 : D = compOf c1
      · subst h1; left; exact ⟨hrD, fun h => hnot ⟨compOf c1, hC1, h⟩⟩
      · by_cases h2 : D = compOf c2
        · subst h2; right; exact ⟨hrD, fun h => hnot ⟨compOf c2, hC2, h⟩⟩
        · exact absurd ⟨D, hD, by rw [hOther D hD h1 h2] at hrD; exact hrD⟩ hnot
    · rintro (⟨hr1, hnot1⟩ | ⟨hr2, hnot2⟩)
      · refine ⟨⟨compOf c1, hC1, hr1⟩, ?_⟩
        rintro ⟨D, hD, hrD⟩
        by_cases h1 : D = compOf c1
        · exact hnot1 (h1 ▸ hrD)
        · have hrV1 : r ∈ (cs.compSt (compOf c1)).G.V := hV1 ▸ (lsfInv_to_RS (hI'.hCompLSF _ hC1).1).2.2.1 hr1
          have hrVD : r ∈ (cs.compSt D).G.V := (lsfInv_to_RS (hI.hCompLSF D hD).1).2.2.1 hrD
          exact Finset.disjoint_left.mp (hI.hV_disj _ hC1 D hD (Ne.symm h1)) hrV1 hrVD
      · refine ⟨⟨compOf c2, hC2, hr2⟩, ?_⟩
        rintro ⟨D, hD, hrD⟩
        by_cases h2 : D = compOf c2
        · exact hnot2 (h2 ▸ hrD)
        · have hrV2 : r ∈ (cs.compSt (compOf c2)).G.V := hV2 ▸ (lsfInv_to_RS (hI'.hCompLSF _ hC2).1).2.2.1 hr2
          have hrVD : r ∈ (cs.compSt D).G.V := (lsfInv_to_RS (hI.hCompLSF D hD).1).2.2.1 hrD
          exact Finset.disjoint_left.mp (hI.hV_disj _ hC2 D hD (Ne.symm h2)) hrV2 hrVD
  have hndE : (cuts.map Prod.fst).Nodup := by
    rw [List.map_append, List.nodup_append]
    refine ⟨hndE1, hndE2, fun f1 hf1 f2 hf2 heq => ?_⟩
    subst heq
    exact compRF_F_disj hI hC1 hC2 hCne
      (Finset.mem_sdiff.mp (hsE1 ▸ List.mem_toFinset.mpr hf1)).1
      (Finset.mem_sdiff.mp (hsE2 ▸ List.mem_toFinset.mpr hf2)).1
  have hndR : (cuts.map Prod.snd).Nodup := by
    rw [List.map_append, List.nodup_append]
    refine ⟨hndR1, hndR2, fun r1 hr1 r2 hr2 heq => ?_⟩
    subst heq
    have h1 : r1 ∈ (cs.compSt (compOf c1)).G.V :=
      hV1 ▸ (lsfInv_to_RS (hI'.hCompLSF _ hC1).1).2.2.1
        (Finset.mem_sdiff.mp (hsR1 ▸ List.mem_toFinset.mpr hr1)).1
    have h2 : r1 ∈ (cs.compSt (compOf c2)).G.V :=
      hV2 ▸ (lsfInv_to_RS (hI'.hCompLSF _ hC2).1).2.2.1
        (Finset.mem_sdiff.mp (hsR2 ▸ List.mem_toFinset.mpr hr2)).1
    exact Finset.disjoint_left.mp (hI.hV_disj _ hC1 _ hC2 hCne) h1 h2
  exact ⟨compForestCutsValid_two_comps_to_global hI hT hne hval1 hval2,
    hndE, by rw [List.map_append, List.toFinset_append, hsE1, hsE2, hEdiff], hEsub,
    hndR, by rw [List.map_append, List.toFinset_append, hsR1, hsR2, hRdiff], hRsub⟩

/-! ## 3. Global cut-lifting for `.split v v' St Sh` -/

/-- Lift a single component's cut log for `.split v v' St Sh` to global `cs.RF`, providing both
`LSFChange` accounting (`v'` separated from `cuts.map Prod.snd`) and all preconditions of
`compForestCutsValid_of_splitRoot`. -/
lemma compRF_cuts_lift_split {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {numComps vCap eCap : ℕ}
    {compOf : Fin numComps → Finset ℕ}
    {edgeC1 edgeC2 gtVert ghVert : ℕ → ℕ} {gtList ghList : ℕ → List ℕ}
    {cs : CompLSFState} {v v' : ℕ} {St Sh : Finset ℕ} {cv : Fin numComps} {cuts : List (ℕ × ℕ)}
    (hI : CompLSFInv C_lsst ℓ₀ cs)
    (hT : CompEdgeTrack numComps vCap eCap compOf edgeC1 edgeC2 gtVert ghVert gtList ghList cs)
    (hu : cs.G.UpdateIsValid (.split v v' St Sh))
    (hv : v ∈ (cs.compSt (compOf cv)).G.V)
    (hEf : 1 ≤ (compGraph cs.G₀ (compOf cv)).m →
      let Sc := cs.compSt (compOf cv)
      let StC := Sc.G.E.filter fun e => e ∈ St ∧ Sc.G.tail e = v ∧ cs.G.tail e = v
      let ShC := Sc.G.E.filter fun e => e ∈ Sh ∧ Sc.G.head e = v ∧ cs.G.head e = v
      let Sc' := applyLSFUpdate Sc (.split v v' StC ShC)
      CompForestCutsValid vCap Sc.RF cuts ∧
      (cuts.map Prod.fst).Nodup ∧ (cuts.map Prod.fst).toFinset = Sc.RF.F.E \ Sc'.RF.F.E ∧
      (cuts.map Prod.snd).Nodup ∧
      Sc'.RF.R = insert v' (Sc.RF.R ∪ (cuts.map Prod.snd).toFinset) ∧
      v' ∉ Sc.RF.R ∪ (cuts.map Prod.snd).toFinset ∧
      (cuts.map Prod.snd).toFinset = Sc'.RF.R.erase v' \ Sc.RF.R)
    (hIso : (compGraph cs.G₀ (compOf cv)).m = 0 → cuts = []) :
    let cs' := compLSFStepSingle cs (.split v v' St Sh)
    let RF_mid := cuts.foldl compApplyForestCut cs.RF
    CompForestCutsValid vCap cs.RF cuts ∧
    (cuts.map Prod.fst).Nodup ∧
    (cuts.map Prod.fst).toFinset = cs.RF.F.E \ cs'.RF.F.E ∧
    cs'.RF.F.E ⊆ cs.RF.F.E ∧
    (cuts.map Prod.snd).Nodup ∧
    v' ∉ cs.RF.R ∧ v' ∈ cs'.RF.R ∧ v' ∉ cuts.map Prod.snd ∧
    (cuts.map Prod.snd).toFinset = cs'.RF.R.erase v' \ cs.RF.R ∧
    cs.RF.R ⊆ cs'.RF.R ∧
    RF_mid.F.IsValid ∧ v ∈ RF_mid.R ∧ v ∈ RF_mid.F.V ∧ v' ∉ RF_mid.F.V ∧
    cs'.RF.F.V = insert v' RF_mid.F.V ∧
    cs'.RF.F.E = RF_mid.F.E ∧
    cs'.RF.R = insert v' RF_mid.R ∧
    (∀ e ∈ RF_mid.F.E, unsplitMap v v' (cs'.RF.F.tail e) = RF_mid.F.tail e ∧
      unsplitMap v v' (cs'.RF.F.head e) = RF_mid.F.head e) := by
  classical
  intro cs' RF_mid
  have hCv : compOf cv ∈ components cs.G₀ := hT.compOf_mem cv
  have hI' : CompLSFInv C_lsst ℓ₀ cs' := compLSFInv_step hI hu
  have hOther : ∀ D ∈ components cs.G₀, D ≠ compOf cv → cs'.compSt D = cs.compSt D := by
    intro D hD hne
    have hvD : v ∉ (cs.compSt D).G.V := fun h =>
      Finset.disjoint_left.mp (hI.hV_disj D hD (compOf cv) hCv hne) h hv
    change applyLSFBatch (cs.compSt D) (projCompUpdateG cs.G (cs.compSt D).G (.split v v' St Sh)) = _
    simp [projCompUpdateG, hvD, applyLSFBatch]
  set Sc := cs.compSt (compOf cv)
  set StC := Sc.G.E.filter fun e => e ∈ St ∧ Sc.G.tail e = v ∧ cs.G.tail e = v
  set ShC := Sc.G.E.filter fun e => e ∈ Sh ∧ Sc.G.head e = v ∧ cs.G.head e = v
  have hSelf : cs'.compSt (compOf cv) = applyLSFUpdate Sc (.split v v' StC ShC) := by
    change applyLSFBatch Sc (projCompUpdateG cs.G Sc.G (.split v v' St Sh)) = _
    simp [projCompUpdateG, hv, applyLSFBatch, StC, ShC]
  have hv'_not_V : v' ∉ cs.G.V := hu.2.1
  have hv'_not_R : v' ∉ cs.RF.R := fun h => hv'_not_V ((compLSF_RF_isRSF hI).2.2.1 h)
  have hv'_mem_R_cv : v' ∈ (cs'.compSt (compOf cv)).RF.R := by
    rw [hSelf]; exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
  have hv'_mem_R : v' ∈ cs'.RF.R := Finset.mem_biUnion.mpr ⟨compOf cv, hCv, hv'_mem_R_cv⟩
  have hE_c_sub : (cs'.compSt (compOf cv)).RF.F.E ⊆ Sc.RF.F.E := by
    rw [hSelf]; exact compApplyLSFUpdate_RF_E_sub (LSFInvWith.toStructInv (hI.hCompLSF _ hCv).1) _
  have hR_c_sub : Sc.RF.R ⊆ (cs'.compSt (compOf cv)).RF.R := by
    rw [hSelf]; exact compApplyLSFUpdate_R_sub _ _
  have hEsub : cs'.RF.F.E ⊆ cs.RF.F.E := fun f hf => by
    obtain ⟨D, hD, hfD⟩ := Finset.mem_biUnion.mp hf
    refine Finset.mem_biUnion.mpr ⟨D, hD, ?_⟩
    by_cases hDcv : D = compOf cv
    · subst hDcv; exact hE_c_sub hfD
    · rw [hOther D hD hDcv] at hfD; exact hfD
  have hRsub : cs.RF.R ⊆ cs'.RF.R := fun r hr => by
    obtain ⟨D, hD, hrD⟩ := Finset.mem_biUnion.mp hr
    refine Finset.mem_biUnion.mpr ⟨D, hD, ?_⟩
    by_cases hDcv : D = compOf cv
    · subst hDcv; exact hR_c_sub hrD
    · rw [hOther D hD hDcv]; exact hrD
  have hEdiff : cs.RF.F.E \ cs'.RF.F.E = Sc.RF.F.E \ (cs'.compSt (compOf cv)).RF.F.E := by
    ext f; simp only [Finset.mem_sdiff, CompLSFState.RF, Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨D, hD, hfD⟩, hnot⟩
      have hDc : D = compOf cv := by
        by_contra hne; exact hnot ⟨D, hD, by rw [hOther D hD hne]; exact hfD⟩
      subst hDc; exact ⟨hfD, fun hf' => hnot ⟨compOf cv, hCv, hf'⟩⟩
    · rintro ⟨hf, hfnot⟩
      refine ⟨⟨compOf cv, hCv, hf⟩, ?_⟩
      rintro ⟨D, hD, hfD⟩
      by_cases hDc : D = compOf cv
      · exact hfnot (hDc ▸ hfD)
      · rw [hOther D hD hDc] at hfD; exact compRF_F_disj hI hD hCv hDc hfD hf
  have hRdiff_erase : cs'.RF.R.erase v' \ cs.RF.R = (cs'.compSt (compOf cv)).RF.R.erase v' \ Sc.RF.R := by
    ext r; simp only [Finset.mem_sdiff, Finset.mem_erase, CompLSFState.RF, Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨hrne, ⟨D, hD, hrD⟩⟩, hnot⟩
      have hDc : D = compOf cv := by
        by_contra hne; exact hnot ⟨D, hD, by rw [hOther D hD hne] at hrD; exact hrD⟩
      subst hDc; exact ⟨⟨hrne, hrD⟩, fun hr' => hnot ⟨compOf cv, hCv, hr'⟩⟩
    · rintro ⟨⟨hrne, hr⟩, hrnot⟩
      refine ⟨⟨hrne, ⟨compOf cv, hCv, hr⟩⟩, ?_⟩
      rintro ⟨D, hD, hrD⟩
      by_cases hDc : D = compOf cv
      · subst hDc; exact hrnot hrD
      · have hrV_D : r ∈ (cs.compSt D).G.V := (lsfInv_to_RS (hI.hCompLSF D hD).1).2.2.1 hrD
        have hrV_c' : r ∈ (cs'.compSt (compOf cv)).G.V := (lsfInv_to_RS (hI'.hCompLSF _ hCv).1).2.2.1 hr
        have hrV_c : r ∈ Sc.G.V := by
          have hV' : (cs'.compSt (compOf cv)).G.V = insert v' Sc.G.V := by rw [hSelf]; rfl
          exact (Finset.mem_insert.mp (hV' ▸ hrV_c')).resolve_left hrne
        exact Finset.disjoint_left.mp (hI.hV_disj D hD (compOf cv) hCv hDc) hrV_D hrV_c
  -- Obtain component-level cut properties (both edgeful and isolated cases)
  have hPart : CompForestCutsValid vCap Sc.RF cuts ∧
      (cuts.map Prod.fst).Nodup ∧ (cuts.map Prod.fst).toFinset = Sc.RF.F.E \ (cs'.compSt (compOf cv)).RF.F.E ∧
      (cuts.map Prod.snd).Nodup ∧ v' ∉ cuts.map Prod.snd ∧
      (cuts.map Prod.snd).toFinset = (cs'.compSt (compOf cv)).RF.R.erase v' \ Sc.RF.R := by
    by_cases hpos : 1 ≤ (compGraph cs.G₀ (compOf cv)).m
    · obtain ⟨h1, h2, h3, h4, _, h6, h7⟩ := hEf hpos
      rw [← hSelf] at h3 h7
      exact ⟨h1, h2, h3, h4, fun hm => h6 (Finset.mem_union_right _ (List.mem_toFinset.mpr hm)), h7⟩
    · have hm0 : (compGraph cs.G₀ (compOf cv)).m = 0 := by omega
      obtain rfl := hIso hm0
      obtain ⟨hE0, hR0, _⟩ := isoComp_props hI hCv hm0
      obtain ⟨hE0', hR0', _⟩ := isoComp_props hI' hCv hm0
      have hV' : (cs'.compSt (compOf cv)).G.V = insert v' Sc.G.V := by rw [hSelf]; rfl
      refine ⟨trivial, List.nodup_nil, by rw [hE0, hE0']; simp, List.nodup_nil, by simp, ?_⟩
      change ∅ = ((cs'.compSt (compOf cv)).R.erase v') \ Sc.R
      rw [hR0', hR0, hV']
      ext r; simp only [Finset.notMem_empty, false_iff, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
      rintro ⟨⟨hne, rfl | h⟩, hnot⟩
      · exact hne rfl
      · exact hnot h
  obtain ⟨hval_c, hndE, hsE_c, hndR, hv'_not_cuts, hsR_c⟩ := hPart
  have hval_g : CompForestCutsValid vCap cs.RF cuts := compForestCutsValid_comp_to_global hI hT cv hval_c
  have hsE : (cuts.map Prod.fst).toFinset = cs.RF.F.E \ cs'.RF.F.E := hsE_c.trans hEdiff.symm
  have hsR : (cuts.map Prod.snd).toFinset = cs'.RF.R.erase v' \ cs.RF.R := hsR_c.trans hRdiff_erase.symm
  have hRF_mid_V : RF_mid.F.V = cs.RF.F.V := compApplyForestCut_foldl_V _ _
  have hRF_mid_E : RF_mid.F.E = cs'.RF.F.E := by
    rw [compApplyForestCut_foldl_E, hsE]
    ext f; simp only [Finset.mem_sdiff]; constructor
    · rintro ⟨h1, h2⟩; by_contra hc; exact h2 ⟨h1, hc⟩
    · intro h; exact ⟨hEsub h, fun h' => h'.2 h⟩
  have hRF_mid_R : cs'.RF.R = insert v' RF_mid.R := by
    rw [compApplyForestCut_foldl_R, hsR]
    ext r; simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_sdiff, Finset.mem_erase]
    constructor
    · intro hr; by_cases hr' : r = v'; exact Or.inl hr'; by_cases hro : r ∈ cs.RF.R
      exact Or.inr (Or.inl hro); exact Or.inr (Or.inr ⟨⟨hr', hr⟩, hro⟩)
    · rintro (rfl | hro | ⟨⟨_, hr⟩, _⟩)
      · exact hv'_mem_R
      · exact hRsub hro
      · exact hr
  have hv_mem_R' : v ∈ cs'.RF.R := by
    -- Either `v ∈ Sc.T₀.V` (then `origVert v = v` so `v ∈ R_orig'`) or `v ∈ Sc.isolatedVerts ⊆ Sc'.isolatedVerts`
    have hInvC := LSFInvWith.toStructInv (hI.hCompLSF _ hCv).1
    refine Finset.mem_biUnion.mpr ⟨compOf cv, hCv, ?_⟩
    rw [hSelf]
    rcases Finset.mem_union.mp (hInvC.hGV_eq ▸ hv) with hvT0 | hvIso
    · refine Finset.mem_union_left _ ?_
      have horig : Sc.origVert v = v := (hI.hCompLSF _ hCv).1.horig_id v hvT0
      have hbase : v ∈ (applyLSFUpdate Sc (.split v v' StC ShC)).R₀_base := by
        dsimp only [applyLSFUpdate]; rw [horig, ite_eq_left hvT0]; exact Finset.mem_insert_self _ _
      exact subset_upClosure hbase
    · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hvIso)
  have hv_ne_v' : v ≠ v' := fun h => hv'_not_V (h ▸ hu.1)
  have hv_mem_RF_mid : v ∈ RF_mid.R := (Finset.mem_insert.mp (hRF_mid_R ▸ hv_mem_R')).resolve_left hv_ne_v'
  have hRF_mid_val : RF_mid.F.IsValid := by
    intro e he
    have he0 : e ∈ cs.RF.F.E := hEsub (hRF_mid_E ▸ he)
    have hval0 := (compLSF_RF_isRSF hI).1.1 e he0
    rw [hRF_mid_V, compApplyForestCut_foldl_tail, compApplyForestCut_foldl_head]
    exact hval0
  have hends : ∀ e ∈ RF_mid.F.E,
      unsplitMap v v' (cs'.RF.F.tail e) = RF_mid.F.tail e ∧
      unsplitMap v v' (cs'.RF.F.head e) = RF_mid.F.head e := by
    intro e he
    rw [compApplyForestCut_foldl_tail, compApplyForestCut_foldl_head]
    have he0 : e ∈ cs.RF.F.E := hEsub (hRF_mid_E ▸ he)
    have hne_v' : cs.G.tail e ≠ v' ∧ cs.G.head e ≠ v' := by
      have hv0 := (compLSF_RF_isRSF hI).1.1 e he0
      exact ⟨fun h => hv'_not_V (h ▸ hv0.1), fun h => hv'_not_V (h ▸ hv0.2)⟩
    constructor
    · change unsplitMap v v' (if e ∈ St ∧ cs.G.tail e = v then v' else cs.G.tail e) = cs.G.tail e
      split_ifs with h
      · simp [unsplitMap, h.2]
      · simp [unsplitMap, hne_v'.1]
    · change unsplitMap v v' (if e ∈ Sh ∧ cs.G.head e = v then v' else cs.G.head e) = cs.G.head e
      split_ifs with h
      · simp [unsplitMap, h.2]
      · simp [unsplitMap, hne_v'.2]
  exact ⟨hval_g, hndE, hsE, hEsub, hndR, hv'_not_R, hv'_mem_R, hv'_not_cuts, hsR, hRsub,
    hRF_mid_val, hv_mem_RF_mid, hRF_mid_V ▸ hu.1, hRF_mid_V ▸ hv'_not_V,
    by rw [hRF_mid_V]; rfl, hRF_mid_E.symm, hRF_mid_R, hends⟩

/-! ## 4. Cut-count capacity and two-dispatch cut-buffer helpers -/

lemma compStep_cnts_le_of_lift {cnt : ℕ} {R R' : Finset ℕ} {cuts : List (ℕ × ℕ)}
    (hcnt : cnt ≤ R.card) (hRsub : R ⊆ R')
    (hndR : (cuts.map Prod.snd).Nodup) (hsR : (cuts.map Prod.snd).toFinset = R' \ R) :
    cnt + cuts.length ≤ R'.card := by
  have hlen : cuts.length = (R' \ R).card := by
    rw [← hsR, List.toFinset_card_of_nodup hndR, List.length_map]
  have hcard : (R' \ R).card + R.card = R'.card := Finset.card_sdiff_add_card_eq_card hRsub
  omega

lemma compStep_cnts_le_of_lift_split {cnt v' : ℕ} {R R' : Finset ℕ} {cuts : List (ℕ × ℕ)}
    (hcnt : cnt ≤ R.card) (hRsub : R ⊆ R') (hv'_not : v' ∉ R)
    (hndR : (cuts.map Prod.snd).Nodup) (hsR : (cuts.map Prod.snd).toFinset = R'.erase v' \ R) :
    cnt + cuts.length ≤ R'.card := by
  have hlen : cuts.length = (R'.erase v' \ R).card := by
    rw [← hsR, List.toFinset_card_of_nodup hndR, List.length_map]
  have hsub_er : R ⊆ R'.erase v' := fun r hr =>
    Finset.mem_erase.mpr ⟨fun h => hv'_not (h ▸ hr), hRsub hr⟩
  have hcard : (R'.erase v' \ R).card + R.card = (R'.erase v').card :=
    Finset.card_sdiff_add_card_eq_card hsub_er
  have her_le : (R'.erase v').card ≤ R'.card := Finset.card_le_card (Finset.erase_subset _ _)
  omega

/-- Index-separation helper for two-stage cut logging (`cuts1`, then `cuts2`): every entry written
in stage 1 lies strictly outside all ranges written in stage 2. -/
lemma compStep_cutBuf_disj {k vCap cntBase : ℕ} {cnts : Fin k → ℕ}
    {cuts1 cuts2 : Fin k → List (ℕ × ℕ)}
    (hcap : ∀ j : Fin k, cnts j + (cuts1 j).length + (cuts2 j).length ≤ vCap)
    (j : Fin k) {i : ℕ} (hi : i < (cuts1 j).length) :
    let rootsBase := cntBase + k
    let fDelBase := cntBase + k + k * vCap
    let cnts1 := fun j' : Fin k => cnts j' + (cuts1 j').length
    let aR := rootsBase + j.1 * vCap + (cnts j + i)
    let aF := fDelBase + j.1 * vCap + (cnts j + i)
    (∀ j0 : Fin k, aR ≠ cntBase + j0.1 ∧ aF ≠ cntBase + j0.1) ∧
    (∀ j0 : Fin k, (aR < rootsBase + j0.1 * vCap + cnts1 j0 ∨
        rootsBase + j0.1 * vCap + cnts1 j0 + (cuts2 j0).length ≤ aR) ∧
      (aF < rootsBase + j0.1 * vCap + cnts1 j0 ∨
        rootsBase + j0.1 * vCap + cnts1 j0 + (cuts2 j0).length ≤ aF)) ∧
    (∀ j0 : Fin k, (aR < fDelBase + j0.1 * vCap + cnts1 j0 ∨
        fDelBase + j0.1 * vCap + cnts1 j0 + (cuts2 j0).length ≤ aR) ∧
      (aF < fDelBase + j0.1 * vCap + cnts1 j0 ∨
        fDelBase + j0.1 * vCap + cnts1 j0 + (cuts2 j0).length ≤ aF)) ∧
    aR < cntBase + k + 2 * (k * vCap) ∧
    aF < cntBase + k + 2 * (k * vCap) := by
  intro rootsBase fDelBase cnts1 aR aF
  have hj_lt : cnts j + i < vCap := by have := hcap j; omega
  have hj_mul : (j.1 + 1) * vCap ≤ k * vCap := Nat.mul_le_mul_right vCap (by have := j.2; omega)
  rw [Nat.add_mul, Nat.one_mul] at hj_mul
  refine ⟨fun j0 => ⟨by have := j0.2; dsimp only [aR, rootsBase]; omega,
      by have := j0.2; dsimp only [aF, fDelBase]; omega⟩,
    fun j0 => ⟨?_, Or.inr ?_⟩, fun j0 => ⟨Or.inl ?_, ?_⟩,
    by dsimp only [aR, rootsBase]; omega, by dsimp only [aF, fDelBase]; omega⟩
  · by_cases hj : j0 = j
    · subst hj; left; dsimp only [aR, cnts1]; omega
    · have hne : j0.1 ≠ j.1 := fun h => hj (Fin.ext h)
      have hj0_cap : cnts1 j0 + (cuts2 j0).length ≤ vCap := hcap j0
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · right
        have h := Nat.mul_le_mul_right vCap (show j0.1 + 1 ≤ j.1 by omega)
        rw [Nat.add_mul, Nat.one_mul] at h; dsimp only [aR]; omega
      · left
        have h := Nat.mul_le_mul_right vCap (show j.1 + 1 ≤ j0.1 by omega)
        rw [Nat.add_mul, Nat.one_mul] at h; dsimp only [aR]; omega
  · have hj0_cap : cnts1 j0 + (cuts2 j0).length ≤ vCap := hcap j0
    have h := Nat.mul_le_mul_right vCap (show j0.1 + 1 ≤ k by have := j0.2; omega)
    rw [Nat.add_mul, Nat.one_mul] at h; dsimp only [aF, rootsBase, fDelBase]; omega
  · dsimp only [aR, rootsBase, fDelBase]; omega
  · by_cases hj : j0 = j
    · subst hj; left; dsimp only [aF, cnts1]; omega
    · have hne : j0.1 ≠ j.1 := fun h => hj (Fin.ext h)
      have hj0_cap : cnts1 j0 + (cuts2 j0).length ≤ vCap := hcap j0
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · right
        have h := Nat.mul_le_mul_right vCap (show j0.1 + 1 ≤ j.1 by omega)
        rw [Nat.add_mul, Nat.one_mul] at h; dsimp only [aF]; omega
      · left
        have h := Nat.mul_le_mul_right vCap (show j.1 + 1 ≤ j0.1 by omega)
        rw [Nat.add_mul, Nat.one_mul] at h; dsimp only [aF]; omega

/-- Transport `CompEdgeTrack` across two branches sharing `G₀`, `G`, `crossEdges`, and per-component
graphs `(cs.compSt (compOf c)).G`. -/
lemma compEdgeTrack_of_same_graph {numComps vCap eCap : ℕ} {compOf : Fin numComps → Finset ℕ}
    {edgeC1 edgeC2 gtVert ghVert : ℕ → ℕ} {gtList ghList : ℕ → List ℕ} {cs₁ cs₂ : CompLSFState}
    (hT : CompEdgeTrack numComps vCap eCap compOf edgeC1 edgeC2 gtVert ghVert gtList ghList cs₁)
    (hG₀ : cs₂.G₀ = cs₁.G₀) (hG : cs₂.G = cs₁.G) (hCr : cs₂.crossEdges = cs₁.crossEdges)
    (hCG : ∀ c : Fin numComps, (cs₂.compSt (compOf c)).G = (cs₁.compSt (compOf c)).G) :
    CompEdgeTrack numComps vCap eCap compOf edgeC1 edgeC2 gtVert ghVert gtList ghList cs₂ := by
  refine ⟨⟨hT.hBij.1, fun C => hG₀.symm ▸ hT.hBij.2 C⟩,
    fun v hv => hT.hVlt v (hG ▸ hv), fun e he => hT.hElt e (hG ▸ he), fun e he => ?_,
    hT.hGT, hT.hGH⟩
  obtain ⟨c1, c2, h1, h2, h3, h4, h5, h6, h7⟩ := hT.hEdge e (hG ▸ he)
  exact ⟨c1, c2, h1, h2, by rw [hG, hCG c1]; exact h3, by rw [hG, hCG c2]; exact h4,
    fun c => by rw [hCG c]; exact h5 c, by rw [hCr]; exact h6,
    fun h => by rw [hG, hCG c1]; exact h7 h⟩

end

end MinCostFlow.SparseCore.Program
