module

public import MinCostFlow.SparseCore.CompLSF
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Dynamic invariants and MWU/LSF bridge for `CompLSF`

Builds on `CompLSF.lean` to prove:
1. `CompLSFInv C_lsst ℓ₀ cs` preserved from `initCompLSF` across `compLSFStepSingle` and
   `compLSFBatch`.
2. Disjoint-union forest validity (`compLSF_T_isForest`, `compLSF_RF_isRSF`, `compLSF_RF_root_eq`)
   and `CompLSFInv.to_Holds`.
3. `CompLSFState` connected root bound, decremental `F.E`, `wstr` immutability, `≤ 2` touched
   components per update (`touchedTiny_batch_card_le`), and `compLSF_mwu_bound` from
   `lemma_5_5_online`.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow MinCostFlow.LSF MinCostFlow.Chain

@[expose] public section

/-! ## 1. Dynamic invariant `CompLSFInv` -/

/-- Dynamic invariant for component-wise LSF maintenance `CompLSFState`. -/
structure CompLSFInv (C_lsst : ℝ) (ℓ₀ : ℕ → ℝ) (cs : CompLSFState) : Prop where
  hG₀_val : cs.G₀.IsValid
  hG_val : cs.G.IsValid
  hV₀ : cs.G₀.V.Nonempty
  hk : 1 ≤ cs.k
  hℓ₀ : ∀ e ∈ cs.G₀.E, 0 < ℓ₀ e
  hCompLSF : ∀ C ∈ components cs.G₀,
    LSFInvAny (mwuK0 C_lsst) ℓ₀ (cs.compSt C) ∧ (cs.compSt C).G₀ = compGraph cs.G₀ C ∧
      (cs.compSt C).k = (cs.k : ℝ)
  hV_disj : ∀ C₁ ∈ components cs.G₀, ∀ C₂ ∈ components cs.G₀, C₁ ≠ C₂ →
    Disjoint (cs.compSt C₁).G.V (cs.compSt C₂).G.V
  hV_eq : (components cs.G₀).biUnion (fun C => (cs.compSt C).G.V) = cs.G.V
  hCE_sub : ∀ C ∈ components cs.G₀, (cs.compSt C).G.E ⊆ cs.G.E
  hCross_sub : cs.crossEdges ⊆ cs.insertedGlobal
  hIns_sub : cs.insertedGlobal ⊆ cs.G.E
  hCompIns_sub : ∀ C ∈ components cs.G₀, (cs.compSt C).insertedEdges ⊆ cs.insertedGlobal
  hNonCross_ends : ∀ C ∈ components cs.G₀, ∀ e ∈ (cs.compSt C).G.E, e ∉ cs.crossEdges →
    (cs.compSt C).G.tail e = cs.G.tail e ∧ (cs.compSt C).G.head e = cs.G.head e
  hNonIns_notCross : ∀ C ∈ components cs.G₀, ∀ e ∈ (cs.compSt C).G.E,
    e ∉ (cs.compSt C).insertedEdges → e ∉ cs.crossEdges
  hEdge_cover : ∀ e ∈ cs.G.E, e ∉ cs.crossEdges → ∃ C ∈ components cs.G₀, e ∈ (cs.compSt C).G.E
  hEdge_atMostTwo : ∀ e, ((components cs.G₀).filter fun C => e ∈ (cs.compSt C).G.E).card ≤ 2
  hIns_wstr_R : ∀ e ∈ cs.insertedGlobal, cs.wstrGlobal e = 1 ∧
    (∃ C₁ ∈ components cs.G₀, cs.G.tail e ∈ (cs.compSt C₁).R) ∧
    (∃ C₂ ∈ components cs.G₀, cs.G.head e ∈ (cs.compSt C₂).R)
  hWstr_surv : ∀ e ∈ cs.G.E, e ∉ cs.insertedGlobal →
    ∃ C ∈ components cs.G₀, e ∈ (cs.compSt C).G.E ∧ e ∉ (cs.compSt C).insertedEdges ∧
      cs.wstrGlobal e = (cs.compSt C).wstr e
  hF_sub_compE : ∀ C ∈ components cs.G₀, (cs.compSt C).RF.F.E ⊆ compEdgeSet cs.G₀ C
  hCE_ins : ∀ C ∈ components cs.G₀, ∀ e ∈ (cs.compSt C).G.E,
    e ∈ cs.insertedGlobal → e ∈ (cs.compSt C).insertedEdges
  hCompE_notCross : ∀ C ∈ components cs.G₀, ∀ e ∈ (cs.compSt C).G.E, e ∉ cs.crossEdges

/-- Under `CompLSFInv`, every edge present in a component graph `G_C` has identical endpoints in
`G_C` and in the global graph `cs.G` (no ghost ends). -/
lemma CompLSFInv.compEnds_eq {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {C : Finset ℕ} (hC : C ∈ components cs.G₀)
    {e : ℕ} (he : e ∈ (cs.compSt C).G.E) :
    (cs.compSt C).G.tail e = cs.G.tail e ∧ (cs.compSt C).G.head e = cs.G.head e :=
  hI.hNonCross_ends C hC e he (hI.hCompE_notCross C hC e he)

/-- Applying `[.insert e a a, .delete e]` to a valid `LSFState` forces `a ∈ S'.R`, restores `S.G.E`
and all existing edge endpoints (no ghost ends), restores `S.insertedEdges`, and adds zero extra
roots on the `.delete e` step (`S'.R = (applyLSFUpdate S (.insert e a a)).R`). -/
lemma applyLSFBatch_insert_delete_selfLoop {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} {S : LSFState}
    (hI : LSFInvWith thresh K_σ ℓ₀ S) {e a : ℕ} (he : e ∉ S.G.E) (ha : a ∈ S.G.V) :
    let S₁ := applyLSFUpdate S (.insert e a a)
    let S' := applyLSFBatch S [.insert e a a, .delete e]
    S.G.BatchIsValid [.insert e a a, .delete e] ∧
    S'.G.V = S.G.V ∧
    S'.G.E = S.G.E ∧
    (∀ f ∈ S.G.E, S'.G.tail f = S.G.tail f ∧ S'.G.head f = S.G.head f) ∧
    S'.insertedEdges = S.insertedEdges ∧
    a ∈ S'.R ∧
    S'.R = S₁.R := by
  classical
  intro S₁ S'
  have hval1 : S.G.UpdateIsValid (.insert e a a) := ⟨he, ha, ha⟩
  have hval2 : (S.G.applyUpdate (.insert e a a)).UpdateIsValid (.delete e) :=
    Finset.mem_insert_self e S.G.E
  have hBV : S.G.BatchIsValid [.insert e a a, .delete e] := ⟨hval1, hval2, trivial⟩
  have hV_eq : S'.G.V = S.G.V := rfl
  have hE_eq : S'.G.E = S.G.E := by
    change (insert e S.G.E).erase e = S.G.E
    exact Finset.erase_insert he
  have hends : ∀ f ∈ S.G.E, S'.G.tail f = S.G.tail f ∧ S'.G.head f = S.G.head f := by
    intro f hf
    have hne : f ≠ e := fun h => he (h ▸ hf)
    exact ⟨by simp [S', applyLSFBatch, applyLSFUpdate, MGraph.applyUpdate, hne],
      by simp [S', applyLSFBatch, applyLSFUpdate, MGraph.applyUpdate, hne]⟩
  have hins_eq : S'.insertedEdges = S.insertedEdges := by
    change (insert e S.insertedEdges).erase e = S.insertedEdges
    exact Finset.erase_insert (fun h => he (hI.hins_sub h))
  have hR_orig_eq : S'.R_orig = S₁.R_orig := by
    have horig_a : S₁.origVert (S₁.G.tail e) = S.origVert a ∧
        S₁.origVert (S₁.G.head e) = S.origVert a := by
      have ht : S₁.G.tail e = a := by simp [S₁, applyLSFUpdate, MGraph.applyUpdate]
      have hh : S₁.G.head e = a := by simp [S₁, applyLSFUpdate, MGraph.applyUpdate]
      exact ⟨by rw [ht]; rfl, by rw [hh]; rfl⟩
    have hadd_sub : ({S₁.origVert (S₁.G.tail e), S₁.origVert (S₁.G.head e)} : Finset ℕ).filter
        (fun x => x ∈ S₁.T₀.V) ⊆ S₁.R_orig := by
      intro x hx
      rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hx
      have hxa : x = S.origVert a := by
        rcases hx.1 with h | h <;> [exact h.trans horig_a.1; exact h.trans horig_a.2]
      subst hxa
      rcases Finset.mem_union.mp (hI.hGV_eq ▸ ha) with haT | haIso
      · rw [hI.horig_id a haT]
        exact subset_upClosure (Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨Finset.mem_insert_self a _, haT⟩))
      · have haS : S.origVert a ∈ S.R_orig := hI.horig_split a haIso
        obtain ⟨u, hu, hanc⟩ := mem_upClosure_iff.mp haS
        exact mem_upClosure_iff.mpr ⟨u, Finset.mem_union_left _ hu, hanc⟩
    ext w
    change w ∈ upClosure S₁.TH S₁.r₀ (S₁.R₀_base ∪
      ({S₁.origVert (S₁.G.tail e), S₁.origVert (S₁.G.head e)} : Finset ℕ).filter
        (fun x => x ∈ S₁.T₀.V)) ↔ w ∈ S₁.R_orig
    constructor
    · intro hw
      obtain ⟨u, hu, hanc⟩ := mem_upClosure_iff.mp hw
      rcases Finset.mem_union.mp hu with hu1 | hu2
      · exact mem_upClosure_iff.mpr ⟨u, hu1, hanc⟩
      · obtain ⟨v, hv, hanc2⟩ := mem_upClosure_iff.mp (hadd_sub hu2)
        have hvT : v ∈ S.T₀.V := by
          rcases Finset.mem_union.mp hv with hv1 | hv2
          · exact hI.hR₀_sub hv1
          · exact (Finset.mem_filter.mp hv2).2
        have hvTH : v ∈ S₁.TH.V := hvT
        exact mem_upClosure_iff.mpr ⟨v, hv, isAncestor_trans (hldAuxTree_isRootedTree hI.hT₀) hvTH hanc hanc2⟩
    · intro hw
      obtain ⟨u, hu, hanc⟩ := mem_upClosure_iff.mp hw
      exact mem_upClosure_iff.mpr ⟨u, Finset.mem_union_left _ hu, hanc⟩
  have hR_eq : S'.R = S₁.R := by
    change S'.R_orig ∪ S'.isolatedVerts = S₁.R_orig ∪ S₁.isolatedVerts
    rw [hR_orig_eq]; rfl
  have ha_mem_R : a ∈ S'.R := by
    rw [hR_eq]
    rcases Finset.mem_union.mp (hI.hGV_eq ▸ ha) with haT | haIso
    · exact Finset.mem_union_left _ (subset_upClosure (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_insert_self a _, haT⟩)))
    · exact Finset.mem_union_right _ haIso
  exact ⟨hBV, hV_eq, hE_eq, hends, hins_eq, ha_mem_R, hR_eq⟩

lemma lsfInv_congr_len {thresh K_σ : ℝ} {ℓ₀ ℓ₁ : ℕ → ℝ} {S : LSFState}
    (hI : LSFInvWith thresh K_σ ℓ₀ S) (hEq : ∀ e ∈ S.G₀.E, ℓ₀ e = ℓ₁ e) :
    LSFInvWith thresh K_σ ℓ₁ S := by
  have hsafe : safeLen S.G₀ ℓ₀ = safeLen S.G₀ ℓ₁ := safeLen_eq_of_eq_on_E hEq
  exact
    { hG₀_val := hI.hG₀_val
      hG_val := hI.hG_val
      hV₀ := hI.hV₀
      hk := hI.hk
      hℓ₀ := fun e he => hEq e he ▸ hI.hℓ₀ e he
      hT₀ := hI.hT₀
      hTV := hI.hTV
      hr₀_base := hI.hr₀_base
      hR₀_sub := hI.hR₀_sub
      hord := hI.hord
      hTG₀ := hI.hTG₀
      hTp₀ := hI.hTp₀
      hpi_br := hI.hpi_br
      hT_cur_forest := hI.hT_cur_forest
      hT_cur_V := hI.hT_cur_V
      hT_cur_E := hI.hT_cur_E
      hF_sub_G := hI.hF_sub_G
      horig_id := hI.horig_id
      horig_split := hI.horig_split
      horig_T := hI.horig_T
      horig_G_nins := hI.horig_G_nins
      hunsplit_F := hI.hunsplit_F
      hdisj_iso := hI.hdisj_iso
      hGV_eq := hI.hGV_eq
      hins_sub := hI.hins_sub
      hins_wstr := hI.hins_wstr
      horig_del := hI.horig_del
      hsurv_edge := by simpa only [hsafe] using hI.hsurv_edge
      hwstr_bound := hI.hwstr_bound
      hthresh_bd := hI.hthresh_bd
      hdeg_le := hI.hdeg_le
      hb_W := hI.hb_W
      hW_props := hI.hW_props }

lemma compLSFInv_initWith {lsfInit : LSFInit} {C_lsst : ℝ} {k j : ℕ}
    (hInit : IsValidLSFInitFor lsfInit C_lsst k j)
    {G₀ : MGraph} (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    {ℓ₀ : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) (hk : 1 ≤ k) :
    CompLSFInv C_lsst ℓ₀ (initCompLSFWith lsfInit G₀ ℓ₀ k j) := by
  classical
  set ℓs := safeLen G₀ ℓ₀
  have hspecC : ∀ C ∈ components G₀,
      LSFInvAny (mwuK0 C_lsst) ℓ₀ (lsfInit (compGraph G₀ C) ℓs k j) ∧
      (lsfInit (compGraph G₀ C) ℓs k j).G₀ = compGraph G₀ C ∧
      (lsfInit (compGraph G₀ C) ℓs k j).G = compGraph G₀ C ∧
      (lsfInit (compGraph G₀ C) ℓs k j).k = (k : ℝ) ∧
      (lsfInit (compGraph G₀ C) ℓs k j).insertedEdges = ∅ ∧
      (compGraph G₀ C).IsSubgraph (lsfInit (compGraph G₀ C) ℓs k j).RF.F := by
    intro C hC
    have hGC_val := compGraph_isValid hG₀ hC
    have hGC_ne := compGraph_nonempty hC
    have hℓC : ∀ e ∈ (compGraph G₀ C).E, 0 < ℓs e := fun e he => by
      have heG : e ∈ G₀.E := Finset.filter_subset _ _ he
      rw [show ℓs e = ℓ₀ e from safeLen_eq_of_mem ℓ₀ heG]
      exact hℓ₀ e heG
    obtain ⟨hI, hG₀_eq, hG_eq, hk_eq, _, hins_eq, _, _, _⟩ := hInit (compGraph G₀ C) ℓs hGC_val hGC_ne hℓC hk
    have hI' : LSFInvAny (mwuK0 C_lsst) ℓ₀ (lsfInit (compGraph G₀ C) ℓs k j) :=
      lsfInvAny_of_with (lsfInv_congr_len hI fun e he => by
        rw [hG₀_eq] at he
        exact safeLen_eq_of_mem ℓ₀ (Finset.filter_subset _ _ he))
    exact ⟨hI', hG₀_eq, hG_eq, hk_eq, hins_eq, by have hF := hI.hF_sub_G; rwa [hG_eq] at hF⟩
  refine ⟨hG₀, hG₀, hV₀, hk, hℓ₀, ?_, ?_, ?_, ?_, Finset.Subset.rfl, Finset.empty_subset _,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro C hC
    exact ⟨(hspecC C hC).1, (hspecC C hC).2.1, (hspecC C hC).2.2.2.1⟩
  · intro C₁ hC₁ C₂ hC₂ hne
    dsimp only [initCompLSFWith] at *
    rw [(hspecC C₁ hC₁).2.2.1, (hspecC C₂ hC₂).2.2.1]
    exact components_V_pairwiseDisjoint G₀ hC₁ hC₂ hne
  · calc (components G₀).biUnion (fun C => (lsfInit (compGraph G₀ C) ℓs k j).G.V)
        = (components G₀).biUnion id :=
          Finset.biUnion_congr rfl fun C hC => by rw [(hspecC C hC).2.2.1]; rfl
      _ = G₀.V := components_biUnion_V G₀
  · intro C hC
    dsimp only [initCompLSFWith] at *
    rw [(hspecC C hC).2.2.1]
    exact Finset.filter_subset _ _
  · intro C hC
    change (lsfInit (compGraph G₀ C) ℓs k j).insertedEdges ⊆ ∅
    rw [(hspecC C hC).2.2.2.2.1]
  · intro C hC e he _
    change e ∈ (lsfInit (compGraph G₀ C) ℓs k j).G.E at he
    change (lsfInit (compGraph G₀ C) ℓs k j).G.tail e = G₀.tail e ∧
      (lsfInit (compGraph G₀ C) ℓs k j).G.head e = G₀.head e
    rw [(hspecC C hC).2.2.1] at he ⊢
    exact ⟨rfl, rfl⟩
  · intro _ _ _ _ _ he; exact Finset.notMem_empty _ he
  · intro e he _
    have h := (components_biUnion_compEdgeSet G₀ hG₀).symm ▸ he
    rw [Finset.mem_biUnion] at h
    rcases h with ⟨C, hC, heC⟩
    exact ⟨C, hC, (hspecC C hC).2.2.1 ▸ heC⟩
  · intro e
    by_cases he : e ∈ G₀.E
    · have hsub : (components G₀).filter (fun C =>
          e ∈ ((initCompLSFWith lsfInit G₀ ℓ₀ k j).compSt C).G.E) ⊆
          {compOf G₀ (G₀.tail e)} := by
        intro C hC
        rw [Finset.mem_filter] at hC
        have hC₁ : C ∈ components G₀ := hC.1
        have heC : e ∈ compEdgeSet G₀ C := by
          have heG := hC.2
          change e ∈ (lsfInit (compGraph G₀ C) ℓs k j).G.E at heG
          rw [(hspecC C hC₁).2.2.1] at heG
          exact heG
        rw [compEdgeSet, Finset.mem_filter] at heC
        rw [Finset.mem_singleton]
        rcases Finset.mem_image.mp hC₁ with ⟨u, _, rfl⟩
        exact compOf_eq_of_connected (mem_compOf_iff.mp heC.2).2
      exact le_trans (Finset.card_le_card hsub) (by simp)
    · have hemp : (components G₀).filter (fun C =>
          e ∈ ((initCompLSFWith lsfInit G₀ ℓ₀ k j).compSt C).G.E) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro C hC
        rw [Finset.mem_filter] at hC
        have heC : e ∈ compEdgeSet G₀ C := by
          have heG := hC.2
          change e ∈ (lsfInit (compGraph G₀ C) ℓs k j).G.E at heG
          rw [(hspecC C hC.1).2.2.1] at heG
          exact heG
        exact he (Finset.filter_subset _ _ heC)
      change ((components G₀).filter fun C =>
        e ∈ ((initCompLSFWith lsfInit G₀ ℓ₀ k j).compSt C).G.E).card ≤ 2
      rw [hemp]; simp
  · intro e he; exact absurd he (Finset.notMem_empty _)
  · intro e he _
    have hbi := (components_biUnion_compEdgeSet G₀ hG₀).symm ▸ he
    rw [Finset.mem_biUnion] at hbi
    rcases hbi with ⟨C, hC, heC⟩
    have hex : ∃ C ∈ components G₀, e ∈ compEdgeSet G₀ C := ⟨C, hC, heC⟩
    have hspec := hex.choose_spec
    have hCeq : hex.choose = C := by
      by_contra hne
      exact Finset.disjoint_left.mp (compEdgeSet_pairwiseDisjoint G₀ hspec.1 hC hne) hspec.2 heC
    refine ⟨C, hC, (hspecC C hC).2.2.1 ▸ heC, ?_, ?_⟩
    · change e ∉ (lsfInit (compGraph G₀ C) ℓs k j).insertedEdges
      rw [(hspecC C hC).2.2.2.2.1]; exact Finset.notMem_empty _
    · dsimp only [initCompLSFWith]
      split_ifs
      rw [hCeq]
  · intro C hC
    exact (hspecC C hC).2.2.2.2.2.2.1
  · intro _ _ _ _ he
    exact absurd he (Finset.notMem_empty _)
  · intro _ _ _ _ he
    exact absurd he (Finset.notMem_empty _)

lemma compLSFInv_init
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) {C_lsst : ℝ}
    (hLSST : HasLSSTSpec oracle C_lsst)
    {G₀ : MGraph} (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    {ℓ₀ : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e)
    {k : ℕ} (hk : 1 ≤ k) (j : ℕ) :
    CompLSFInv C_lsst ℓ₀ (initCompLSF oracle C_lsst G₀ ℓ₀ k j) :=
  compLSFInv_initWith (initLSFOnline_isValidLSFInitFor hLSST k j) hG₀ hV₀ hℓ₀ hk

lemma projCompUpdateG_valid {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {u : Update} (hu : cs.G.UpdateIsValid u)
    {C : Finset ℕ} (hC : C ∈ components cs.G₀) :
    (cs.compSt C).G.BatchIsValid (projCompUpdateG cs.G (cs.compSt C).G u) := by
  classical
  cases u with
  | delete e =>
    dsimp only [projCompUpdateG]
    split_ifs with he
    · exact ⟨he, trivial⟩
    · exact trivial
  | insert e a b =>
    dsimp only [projCompUpdateG]
    have hne : e ∉ (cs.compSt C).G.E := fun h => hu.1 (hI.hCE_sub C hC h)
    split_ifs with h1 h2 h3
    · exact ⟨⟨hne, h1.1, h1.2⟩, trivial⟩
    · exact ⟨⟨hne, h2, h2⟩, Finset.mem_insert_self _ _, trivial⟩
    · exact ⟨⟨hne, h3, h3⟩, Finset.mem_insert_self _ _, trivial⟩
    · exact trivial
  | split v v' St Sh =>
    dsimp only [projCompUpdateG]
    split_ifs with hv
    · refine ⟨⟨hv, ?_, ?_, ?_⟩, trivial⟩
      · intro hv'
        apply hu.2.1
        rw [← hI.hV_eq]
        exact Finset.mem_biUnion.mpr ⟨C, hC, hv'⟩
      · exact Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      · intro e he
        rcases Finset.mem_union.mp he with heT | heH
        · left; exact (Finset.mem_filter.mp heT).2.2.1
        · right; exact (Finset.mem_filter.mp heH).2.2.1
    · exact trivial

lemma compLSFInv_step {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {u : Update} (hu : cs.G.UpdateIsValid u) :
    CompLSFInv C_lsst ℓ₀ (compLSFStepSingle cs u) := by
  classical
  set cs' := compLSFStepSingle cs u
  have hG'_val : cs'.G.IsValid := applyUpdate_isValid hI.hG_val hu
  have hC_step : ∀ C ∈ components cs.G₀,
      LSFInvAny (mwuK0 C_lsst) ℓ₀ (cs'.compSt C) ∧
      (cs'.compSt C).G = (cs.compSt C).G.applyBatch (projCompUpdateG cs.G (cs.compSt C).G u) ∧
      (cs'.compSt C).G₀ = compGraph cs.G₀ C ∧
      (cs'.compSt C).k = (cs.k : ℝ) ∧
      (cs'.compSt C).R ⊇ (cs.compSt C).R ∧
      (cs'.compSt C).RF.F.E ⊆ (cs.compSt C).RF.F.E := by
    intro C hC
    have hCI := (hI.hCompLSF C hC).1
    have hBV := projCompUpdateG_valid hI hu hC
    have hB := applyLSFBatch_inv_with (projCompUpdateG cs.G (cs.compSt C).G u) hCI hBV
    exact ⟨lsfInvAny_of_with hB.1, hB.2.1, hB.2.2.1.trans (hI.hCompLSF C hC).2.1,
      hB.2.2.2.2.2.2.1.trans (hI.hCompLSF C hC).2.2, hB.2.2.2.2.2.2.2.2.1, hB.2.2.2.2.2.2.2.2.2.1⟩
  have hV_del : ∀ e₀ C, C ∈ components cs.G₀ → u = .delete e₀ →
      (cs'.compSt C).G.V = (cs.compSt C).G.V := fun e₀ C hC heq => by
    rw [(hC_step C hC).2.1, heq]; dsimp only [projCompUpdateG]; split_ifs <;> rfl
  have hV_ins : ∀ e₀ a b C, C ∈ components cs.G₀ → u = .insert e₀ a b →
      (cs'.compSt C).G.V = (cs.compSt C).G.V := fun e₀ a b C hC heq => by
    rw [(hC_step C hC).2.1, heq]; dsimp only [projCompUpdateG]; split_ifs <;> rfl
  have hV_split : ∀ v v' St Sh C, C ∈ components cs.G₀ → u = .split v v' St Sh →
      (cs'.compSt C).G.V =
        if v ∈ (cs.compSt C).G.V then insert v' (cs.compSt C).G.V else (cs.compSt C).G.V :=
    fun v v' St Sh C hC heq => by
      rw [(hC_step C hC).2.1, heq]; dsimp only [projCompUpdateG]; split_ifs <;> rfl
  have hV_disj' : ∀ C₁ ∈ components cs.G₀, ∀ C₂ ∈ components cs.G₀, C₁ ≠ C₂ →
      Disjoint (cs'.compSt C₁).G.V (cs'.compSt C₂).G.V := by
    intro C₁ hC₁ C₂ hC₂ hne
    have hd := hI.hV_disj C₁ hC₁ C₂ hC₂ hne
    cases u with
    | delete e₀ => rw [hV_del e₀ C₁ hC₁ rfl, hV_del e₀ C₂ hC₂ rfl]; exact hd
    | insert e₀ a b => rw [hV_ins e₀ a b C₁ hC₁ rfl, hV_ins e₀ a b C₂ hC₂ rfl]; exact hd
    | split v v' St Sh =>
      rw [hV_split v v' St Sh C₁ hC₁ rfl, hV_split v v' St Sh C₂ hC₂ rfl]
      have hv'_notin : ∀ C ∈ components cs.G₀, v' ∉ (cs.compSt C).G.V := fun C hC hv' =>
        hu.2.1 (hI.hV_eq ▸ Finset.mem_biUnion.mpr ⟨C, hC, hv'⟩)
      by_cases h1 : v ∈ (cs.compSt C₁).G.V <;> by_cases h2 : v ∈ (cs.compSt C₂).G.V
      · exact absurd h2 (Finset.disjoint_left.mp hd h1)
      · rw [ite_eq_left_iff.mpr (fun h => absurd h1 h),
          ite_eq_right_iff.mpr (fun h => absurd h h2), Finset.disjoint_insert_left]
        exact ⟨hv'_notin C₂ hC₂, hd⟩
      · rw [ite_eq_right_iff.mpr (fun h => absurd h h1),
          ite_eq_left_iff.mpr (fun h => absurd h2 h), Finset.disjoint_insert_right]
        exact ⟨hv'_notin C₁ hC₁, hd⟩
      · simp only [h1, h2, ↓reduceIte]; exact hd
  have hV_eq' : (components cs.G₀).biUnion (fun C => (cs'.compSt C).G.V) = cs'.G.V := by
    ext x
    simp only [Finset.mem_biUnion]
    cases u with
    | delete e₀ =>
      change (∃ C ∈ components cs.G₀, x ∈ (cs'.compSt C).G.V) ↔ x ∈ cs.G.V
      have heq : (∃ C ∈ components cs.G₀, x ∈ (cs'.compSt C).G.V) ↔
          ∃ C ∈ components cs.G₀, x ∈ (cs.compSt C).G.V :=
        exists_congr fun C => and_congr_right fun hC => by rw [hV_del e₀ C hC rfl]
      rw [heq, ← hI.hV_eq, Finset.mem_biUnion]
    | insert e₀ a b =>
      change (∃ C ∈ components cs.G₀, x ∈ (cs'.compSt C).G.V) ↔ x ∈ cs.G.V
      have heq : (∃ C ∈ components cs.G₀, x ∈ (cs'.compSt C).G.V) ↔
          ∃ C ∈ components cs.G₀, x ∈ (cs.compSt C).G.V :=
        exists_congr fun C => and_congr_right fun hC => by rw [hV_ins e₀ a b C hC rfl]
      rw [heq, ← hI.hV_eq, Finset.mem_biUnion]
    | split v v' St Sh =>
      change (∃ C ∈ components cs.G₀, x ∈ (cs'.compSt C).G.V) ↔ x ∈ insert v' cs.G.V
      have hvG : v ∈ cs.G.V := hu.1
      rw [← hI.hV_eq, Finset.mem_biUnion] at hvG
      rcases hvG with ⟨C₀, hC₀, hvC₀⟩
      constructor
      · rintro ⟨C, hC, hx⟩
        rw [hV_split v v' St Sh C hC rfl] at hx
        split_ifs at hx
        · rcases Finset.mem_insert.mp hx with rfl | hxC
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hI.hV_eq ▸ Finset.mem_biUnion.mpr ⟨C, hC, hxC⟩)
        · exact Finset.mem_insert_of_mem (hI.hV_eq ▸ Finset.mem_biUnion.mpr ⟨C, hC, hx⟩)
      · intro hx
        rw [Finset.mem_insert] at hx
        rcases hx with hxv | hxG
        · subst hxv
          refine ⟨C₀, hC₀, ?_⟩
          rw [hV_split v x St Sh C₀ hC₀ rfl, ite_eq_left_iff.mpr fun h => absurd hvC₀ h]
          exact Finset.mem_insert_self _ _
        · rw [← hI.hV_eq, Finset.mem_biUnion] at hxG
          rcases hxG with ⟨C, hC, hxC⟩
          refine ⟨C, hC, ?_⟩
          rw [hV_split v v' St Sh C hC rfl]
          split_ifs
          · exact Finset.mem_insert_of_mem hxC
          · exact hxC
  have hCE_sub' : ∀ C ∈ components cs.G₀, (cs'.compSt C).G.E ⊆ cs'.G.E := by
    intro C hC e he
    rw [(hC_step C hC).2.1] at he
    cases u with
    | delete e₀ =>
      dsimp only [projCompUpdateG] at he
      split_ifs at he
      · simp only [MGraph.applyBatch, List.foldl_cons, List.foldl_nil, MGraph.applyUpdate,
          Finset.mem_erase] at he
        change e ∈ cs.G.E.erase e₀
        exact Finset.mem_erase.mpr ⟨he.1, hI.hCE_sub C hC he.2⟩
      · have hne : e ≠ e₀ := fun h => by subst h; exact absurd he (by assumption)
        exact Finset.mem_erase.mpr ⟨hne, hI.hCE_sub C hC he⟩
    | insert e₀ a b =>
      dsimp only [projCompUpdateG] at he
      split_ifs at he
      · rcases Finset.mem_insert.mp he with rfl | heC
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hI.hCE_sub C hC heC)
      · have heC : e ∈ (cs.compSt C).G.E := by
          simp only [MGraph.applyBatch, List.foldl_cons, List.foldl_nil, MGraph.applyUpdate,
            Finset.mem_erase, Finset.mem_insert] at he
          exact he.2.resolve_left he.1
        exact Finset.mem_insert_of_mem (hI.hCE_sub C hC heC)
      · have heC : e ∈ (cs.compSt C).G.E := by
          simp only [MGraph.applyBatch, List.foldl_cons, List.foldl_nil, MGraph.applyUpdate,
            Finset.mem_erase, Finset.mem_insert] at he
          exact he.2.resolve_left he.1
        exact Finset.mem_insert_of_mem (hI.hCE_sub C hC heC)
      · exact Finset.mem_insert_of_mem (hI.hCE_sub C hC he)
    | split v v' St Sh =>
      dsimp only [projCompUpdateG] at he
      split_ifs at he
      · exact hI.hCE_sub C hC he
      · exact hI.hCE_sub C hC he
  have hCross_sub' : cs'.crossEdges ⊆ cs'.insertedGlobal := by
    intro e he
    cases u with
    | delete e₀ =>
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp he).1,
        hI.hCross_sub (Finset.mem_erase.mp he).2⟩
    | insert e₀ a b =>
      dsimp only [cs', compLSFStepSingle, updateInserted] at he ⊢
      split_ifs at he
      · exact Finset.mem_insert_of_mem (hI.hCross_sub he)
      · rcases Finset.mem_insert.mp he with rfl | heC
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hI.hCross_sub heC)
    | split _ _ _ _ => exact hI.hCross_sub he
  have hIns_sub' : cs'.insertedGlobal ⊆ cs'.G.E := by
    intro e he
    cases u with
    | delete e₀ =>
      have h := Finset.mem_erase.mp he
      exact Finset.mem_erase.mpr ⟨h.1, hI.hIns_sub h.2⟩
    | insert e₀ a b =>
      rcases Finset.mem_insert.mp he with rfl | heI
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hI.hIns_sub heI)
    | split _ _ _ _ => exact hI.hIns_sub he
  have hCompIns_sub' : ∀ C ∈ components cs.G₀, (cs'.compSt C).insertedEdges ⊆ cs'.insertedGlobal := by
    intro C hC e he
    have hins := (applyLSFBatch_insertedEdges (projCompUpdateG cs.G (cs.compSt C).G u)
      (cs.compSt C)).symm ▸ he
    cases u with
    | delete e₀ =>
      dsimp only [projCompUpdateG] at hins
      split_ifs at hins with heC
      · rw [List.foldl_cons, List.foldl_nil, updateInserted, Finset.mem_erase] at hins
        exact Finset.mem_erase.mpr ⟨hins.1, hI.hCompIns_sub C hC hins.2⟩
      · have he_sub : e ∈ (cs.compSt C).insertedEdges := hins
        have hne : e ≠ e₀ := fun h => heC (h ▸ (hI.hCompLSF C hC).1.hins_sub he_sub)
        exact Finset.mem_erase.mpr ⟨hne, hI.hCompIns_sub C hC he_sub⟩
    | insert e₀ a b =>
      dsimp only [projCompUpdateG] at hins
      split_ifs at hins
      · rcases Finset.mem_insert.mp hins with rfl | hmem
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hI.hCompIns_sub C hC hmem)
      · have hmem : e ∈ (cs.compSt C).insertedEdges := by
          simp only [List.foldl_cons, List.foldl_nil, updateInserted, Finset.mem_erase,
            Finset.mem_insert] at hins
          exact hins.2.resolve_left hins.1
        exact Finset.mem_insert_of_mem (hI.hCompIns_sub C hC hmem)
      · have hmem : e ∈ (cs.compSt C).insertedEdges := by
          simp only [List.foldl_cons, List.foldl_nil, updateInserted, Finset.mem_erase,
            Finset.mem_insert] at hins
          exact hins.2.resolve_left hins.1
        exact Finset.mem_insert_of_mem (hI.hCompIns_sub C hC hmem)
      · exact Finset.mem_insert_of_mem (hI.hCompIns_sub C hC hins)
    | split v v' St Sh =>
      dsimp only [projCompUpdateG] at hins
      split_ifs at hins
      · exact hI.hCompIns_sub C hC hins
      · exact hI.hCompIns_sub C hC hins
  have hNonCross_ends' : ∀ C ∈ components cs.G₀, ∀ e ∈ (cs'.compSt C).G.E,
      e ∉ cs'.crossEdges →
      (cs'.compSt C).G.tail e = cs'.G.tail e ∧ (cs'.compSt C).G.head e = cs'.G.head e := by
    intro C hC e he hnc
    rw [(hC_step C hC).2.1] at he ⊢
    cases u with
    | delete e₀ =>
      dsimp only [projCompUpdateG] at he ⊢
      have hne : e ≠ e₀ := by
        intro h; subst h
        split_ifs at he
        · exact (Finset.mem_erase.mp he).1 rfl
        · exact absurd he (by assumption)
      have heC : e ∈ (cs.compSt C).G.E := by
        split_ifs at he
        · exact (Finset.mem_erase.mp he).2
        · exact he
      have hnc_old : e ∉ cs.crossEdges := fun hc =>
        hnc (Finset.mem_erase.mpr ⟨hne, hc⟩)
      have hend := hI.hNonCross_ends C hC e heC hnc_old
      split_ifs <;> exact hend
    | insert e₀ a b =>
      dsimp only [projCompUpdateG] at he ⊢
      by_cases he₀ : e = e₀
      · subst he₀
        have he_new : e ∉ (cs.compSt C).G.E := fun h => hu.1 (hI.hCE_sub C hC h)
        have hnc_same : ∃ C₁ ∈ components cs.G₀, a ∈ (cs.compSt C₁).G.V ∧ b ∈ (cs.compSt C₁).G.V := by
          by_contra hnone
          apply hnc
          change e ∈ if ∃ C ∈ components cs.G₀, a ∈ (cs.compSt C).G.V ∧ b ∈ (cs.compSt C).G.V
            then cs.crossEdges else insert e cs.crossEdges
          simp only [hnone, ↓reduceIte, Finset.mem_insert, true_or]
        rcases hnc_same with ⟨C₁, hC₁, ha₁, hb₁⟩
        have hCC₁ : C = C₁ := by
          by_contra hneC
          have hd := hI.hV_disj C hC C₁ hC₁ hneC
          split_ifs at he with h1 h2 h3
          · exact Finset.disjoint_left.mp hd h1.1 ha₁
          · exact Finset.disjoint_left.mp hd h2 ha₁
          · exact Finset.disjoint_left.mp hd h3 hb₁
          · exact he_new he
        subst hCC₁
        simp only [ha₁, hb₁, and_self, ↓reduceIte, MGraph.applyBatch, List.foldl_cons,
          List.foldl_nil, cs', compLSFStepSingle, MGraph.applyUpdate, Function.update_self]
      · have hnc_old : e ∉ cs.crossEdges := fun hc => by
          apply hnc
          change e ∈ if ∃ C ∈ components cs.G₀, a ∈ (cs.compSt C).G.V ∧ b ∈ (cs.compSt C).G.V
            then cs.crossEdges else insert e₀ cs.crossEdges
          split_ifs
          · exact hc
          · exact Finset.mem_insert_of_mem hc
        have heC : e ∈ (cs.compSt C).G.E := by
          split_ifs at he
          · exact (Finset.mem_insert.mp he).resolve_left he₀
          · simp only [MGraph.applyBatch, List.foldl_cons, List.foldl_nil, MGraph.applyUpdate,
              Finset.mem_erase, Finset.mem_insert] at he
            exact he.2.resolve_left he₀
          · simp only [MGraph.applyBatch, List.foldl_cons, List.foldl_nil, MGraph.applyUpdate,
              Finset.mem_erase, Finset.mem_insert] at he
            exact he.2.resolve_left he₀
          · exact he
        have hend := hI.hNonCross_ends C hC e heC hnc_old
        change _ = (cs.G.applyUpdate (.insert e₀ a b)).tail e ∧
          _ = (cs.G.applyUpdate (.insert e₀ a b)).head e
        split_ifs <;> simp [MGraph.applyBatch, MGraph.applyUpdate, he₀, hend]
    | split v v' St Sh =>
      have heC : e ∈ (cs.compSt C).G.E := by
        dsimp only [projCompUpdateG] at he
        split_ifs at he <;> exact he
      have hend := hI.hNonCross_ends C hC e heC hnc
      dsimp only [projCompUpdateG]
      change _ = (cs.G.applyUpdate (.split v v' St Sh)).tail e ∧
        _ = (cs.G.applyUpdate (.split v v' St Sh)).head e
      split_ifs with hv
      · simp only [MGraph.applyBatch, List.foldl_cons, List.foldl_nil, MGraph.applyUpdate,
          Finset.mem_filter]
        refine ⟨?_, ?_⟩
        · by_cases ht : e ∈ St ∧ cs.G.tail e = v
          · simp only [heC, ht, hend.1, and_self, ↓reduceIte]
          · simp only [hend.1]
            rw [ite_eq_right_iff.mpr (fun h => absurd ⟨h.1.2.1, h.2⟩ ht)]
            exact (ite_eq_right_iff.mpr (fun h => absurd h ht)).symm
        · by_cases hh : e ∈ Sh ∧ cs.G.head e = v
          · simp only [heC, hh, hend.2, and_self, ↓reduceIte]
          · simp only [hend.2]
            rw [ite_eq_right_iff.mpr (fun h => absurd ⟨h.1.2.1, h.2⟩ hh)]
            exact (ite_eq_right_iff.mpr (fun h => absurd h hh)).symm
      · simp only [MGraph.applyBatch, List.foldl_nil, MGraph.applyUpdate]
        have hth := (hI.hCompLSF C hC).1.hG_val e heC
        rw [hend.1, hend.2] at hth
        have ht_ne : cs.G.tail e ≠ v := fun h => hv (h ▸ hth.1)
        have hh_ne : cs.G.head e ≠ v := fun h => hv (h ▸ hth.2)
        simp only [ht_ne, hh_ne, and_false, ↓reduceIte]
        exact hend
  have hNonIns_notCross' : ∀ C ∈ components cs.G₀, ∀ e ∈ (cs'.compSt C).G.E,
      e ∉ (cs'.compSt C).insertedEdges → e ∉ cs'.crossEdges := by
    intro C hC e he hni hc
    have he_upd := (hC_step C hC).2.1 ▸ he
    have hins_eq : (cs'.compSt C).insertedEdges =
        (projCompUpdateG cs.G (cs.compSt C).G u).foldl updateInserted (cs.compSt C).insertedEdges :=
      applyLSFBatch_insertedEdges (projCompUpdateG cs.G (cs.compSt C).G u) (cs.compSt C)
    rw [hins_eq] at hni
    cases u with
    | delete e₀ =>
      dsimp only [projCompUpdateG] at he_upd hni
      have hne : e ≠ e₀ := (Finset.mem_erase.mp hc).1
      have hc₀ : e ∈ cs.crossEdges := (Finset.mem_erase.mp hc).2
      split_ifs at he_upd hni with hdel
      · have he_old : e ∈ (cs.compSt C).G.E := (Finset.mem_erase.mp he_upd).2
        have hni_old : e ∉ (cs.compSt C).insertedEdges := fun hm =>
          hni (by rw [List.foldl_cons, List.foldl_nil, updateInserted]; exact Finset.mem_erase.mpr ⟨hne, hm⟩)
        exact hI.hNonIns_notCross C hC e he_old hni_old hc₀
      · exact hI.hNonIns_notCross C hC e he_upd hni hc₀
    | insert e₀ a b =>
      by_cases he₀ : e = e₀
      · subst he₀
        dsimp only [projCompUpdateG] at he_upd hni
        split_ifs at he_upd hni
        · exact hni (by simp [updateInserted])
        · simp [MGraph.applyBatch, MGraph.applyUpdate] at he_upd
        · simp [MGraph.applyBatch, MGraph.applyUpdate] at he_upd
        · exact hu.1 (hI.hCE_sub C hC (by simpa [MGraph.applyBatch] using he_upd))
      · have hc₀ : e ∈ cs.crossEdges := by
          change e ∈ if ∃ C ∈ components cs.G₀, a ∈ (cs.compSt C).G.V ∧ b ∈ (cs.compSt C).G.V
            then cs.crossEdges else insert e₀ cs.crossEdges at hc
          split_ifs at hc
          · exact hc
          · exact (Finset.mem_insert.mp hc).resolve_left he₀
        dsimp only [projCompUpdateG] at he_upd hni
        split_ifs at he_upd hni
        all_goals
          have he_old : e ∈ (cs.compSt C).G.E := by
            simp only [MGraph.applyBatch, List.foldl_cons, List.foldl_nil, MGraph.applyUpdate,
              Finset.mem_erase, Finset.mem_insert, he₀, false_or, ne_eq, not_false_eq_true,
              true_and] at he_upd
            exact he_upd
          have hni_old : e ∉ (cs.compSt C).insertedEdges := fun hm =>
            hni (by simp [updateInserted, he₀, hm])
          exact hI.hNonIns_notCross C hC e he_old hni_old hc₀
    | split v v' St Sh =>
      dsimp only [projCompUpdateG] at he_upd hni
      split_ifs at he_upd hni
      · exact hI.hNonIns_notCross C hC e he_upd hni hc
      · exact hI.hNonIns_notCross C hC e he_upd hni hc
  have hEdge_cover' : ∀ e ∈ cs'.G.E, e ∉ cs'.crossEdges →
      ∃ C ∈ components cs.G₀, e ∈ (cs'.compSt C).G.E := by
    intro e he hnc
    cases u with
    | delete e₀ =>
      have hm := Finset.mem_erase.mp he
      have hnc₀ : e ∉ cs.crossEdges := fun hc => hnc (Finset.mem_erase.mpr ⟨hm.1, hc⟩)
      obtain ⟨C, hC, heC⟩ := hI.hEdge_cover e hm.2 hnc₀
      refine ⟨C, hC, ?_⟩
      rw [(hC_step C hC).2.1]
      dsimp only [projCompUpdateG]
      split_ifs
      · exact Finset.mem_erase.mpr ⟨hm.1, heC⟩
      · exact heC
    | insert e₀ a b =>
      by_cases he₀ : e = e₀
      · subst he₀
        have hex : ∃ C ∈ components cs.G₀, a ∈ (cs.compSt C).G.V ∧ b ∈ (cs.compSt C).G.V := by
          by_contra hnone
          apply hnc
          change e ∈ if ∃ C ∈ components cs.G₀, a ∈ (cs.compSt C).G.V ∧ b ∈ (cs.compSt C).G.V
            then cs.crossEdges else insert e cs.crossEdges
          simp only [hnone, ↓reduceIte, Finset.mem_insert, true_or]
        rcases hex with ⟨C, hC, haC, hbC⟩
        refine ⟨C, hC, ?_⟩
        rw [(hC_step C hC).2.1]
        dsimp only [projCompUpdateG]
        simp [haC, hbC, MGraph.applyBatch, MGraph.applyUpdate]
      · have he₀G : e ∈ cs.G.E := (Finset.mem_insert.mp he).resolve_left he₀
        have hnc₀ : e ∉ cs.crossEdges := fun hc => by
          apply hnc
          change e ∈ if ∃ C ∈ components cs.G₀, a ∈ (cs.compSt C).G.V ∧ b ∈ (cs.compSt C).G.V
            then cs.crossEdges else insert e₀ cs.crossEdges
          split_ifs
          · exact hc
          · exact Finset.mem_insert_of_mem hc
        obtain ⟨C, hC, heC⟩ := hI.hEdge_cover e he₀G hnc₀
        refine ⟨C, hC, ?_⟩
        rw [(hC_step C hC).2.1]
        dsimp only [projCompUpdateG]
        split_ifs <;> simp [heC, he₀, MGraph.applyBatch, MGraph.applyUpdate]
    | split v v' St Sh =>
      obtain ⟨C, hC, heC⟩ := hI.hEdge_cover e he hnc
      refine ⟨C, hC, ?_⟩
      rw [(hC_step C hC).2.1]
      dsimp only [projCompUpdateG]
      split_ifs <;> exact heC
  have hEdge_atMostTwo' : ∀ e, ((components cs.G₀).filter fun C => e ∈ (cs'.compSt C).G.E).card ≤ 2 := by
    intro e
    cases u with
    | delete e₀ =>
      refine le_trans (Finset.card_le_card fun C hC => ?_) (hI.hEdge_atMostTwo e)
      rw [Finset.mem_filter] at hC ⊢
      refine ⟨hC.1, ?_⟩
      have he_upd := (hC_step C hC.1).2.1 ▸ hC.2
      dsimp only [projCompUpdateG] at he_upd
      split_ifs at he_upd
      · exact (Finset.mem_erase.mp he_upd).2
      · exact he_upd
    | insert e₀ a b =>
      by_cases he₀ : e = e₀
      · subst he₀
        have haG := hu.2.1
        have hbG := hu.2.2
        rw [← hI.hV_eq, Finset.mem_biUnion] at haG hbG
        rcases haG with ⟨Ca, hCa, haCa⟩
        rcases hbG with ⟨Cb, hCb, hbCb⟩
        have hsub : ((components cs.G₀).filter fun C => e ∈ (cs'.compSt C).G.E) ⊆ {Ca, Cb} := by
          intro C hC
          rw [Finset.mem_filter] at hC
          have he_upd := (hC_step C hC.1).2.1 ▸ hC.2
          dsimp only [projCompUpdateG] at he_upd
          rw [Finset.mem_insert, Finset.mem_singleton]
          split_ifs at he_upd with h1 h2 h3
          · left; by_contra hne
            exact Finset.disjoint_left.mp (hI.hV_disj C hC.1 Ca hCa hne) h1.1 haCa
          · left; by_contra hne
            exact Finset.disjoint_left.mp (hI.hV_disj C hC.1 Ca hCa hne) h2 haCa
          · right; by_contra hne
            exact Finset.disjoint_left.mp (hI.hV_disj C hC.1 Cb hCb hne) h3 hbCb
          · exact absurd he_upd (fun h => hu.1 (hI.hCE_sub C hC.1 h))
        exact le_trans (Finset.card_le_card hsub) (Finset.card_le_two)
      · have hfilt : ((components cs.G₀).filter fun C => e ∈ (cs'.compSt C).G.E) =
            ((components cs.G₀).filter fun C => e ∈ (cs.compSt C).G.E) := by
          ext C
          simp only [Finset.mem_filter]
          refine and_congr_right fun hC => ?_
          rw [(hC_step C hC).2.1]
          dsimp only [projCompUpdateG]
          split_ifs <;> simp [MGraph.applyBatch, MGraph.applyUpdate, he₀]
        rw [hfilt]
        exact hI.hEdge_atMostTwo e
    | split v v' St Sh =>
      have hfilt : ((components cs.G₀).filter fun C => e ∈ (cs'.compSt C).G.E) =
            ((components cs.G₀).filter fun C => e ∈ (cs.compSt C).G.E) := by
        ext C
        simp only [Finset.mem_filter]
        refine and_congr_right fun hC => ?_
        rw [(hC_step C hC).2.1]
        dsimp only [projCompUpdateG]
        split_ifs <;> rfl
      rw [hfilt]
      exact hI.hEdge_atMostTwo e
  have hIns_wstr_R' : ∀ e ∈ cs'.insertedGlobal, cs'.wstrGlobal e = 1 ∧
      (∃ C₁ ∈ components cs.G₀, cs'.G.tail e ∈ (cs'.compSt C₁).R) ∧
      (∃ C₂ ∈ components cs.G₀, cs'.G.head e ∈ (cs'.compSt C₂).R) := by
    intro e he
    cases u with
    | delete e₀ =>
      have hm := Finset.mem_erase.mp he
      have hw := hI.hIns_wstr_R e hm.2
      refine ⟨hw.1, ?_, ?_⟩
      · rcases hw.2.1 with ⟨C₁, hC₁, hR₁⟩
        exact ⟨C₁, hC₁, (hC_step C₁ hC₁).2.2.2.2.1 hR₁⟩
      · rcases hw.2.2 with ⟨C₂, hC₂, hR₂⟩
        exact ⟨C₂, hC₂, (hC_step C₂ hC₂).2.2.2.2.1 hR₂⟩
    | insert e₀ a b =>
      by_cases he₀ : e = e₀
      · subst he₀
        have haG := hu.2.1
        have hbG := hu.2.2
        rw [← hI.hV_eq, Finset.mem_biUnion] at haG hbG
        rcases haG with ⟨C₁, hC₁, ha₁⟩
        rcases hbG with ⟨C₂, hC₂, hb₂⟩
        have haR : a ∈ (cs'.compSt C₁).R := by
          change a ∈ (applyLSFBatch (cs.compSt C₁) (projCompUpdateG cs.G (cs.compSt C₁).G (.insert e a b))).R
          dsimp only [projCompUpdateG]
          have he_not1 : e ∉ (cs.compSt C₁).G.E := fun h => hu.1 (hI.hCE_sub C₁ hC₁ h)
          by_cases hb₁ : b ∈ (cs.compSt C₁).G.V
          · simp only [ha₁, hb₁, and_self, ↓reduceIte, applyLSFBatch, List.foldl_cons, List.foldl_nil]
            have hi₁ := (applyLSFUpdate_inv_with (u := .insert e a b) (hI.hCompLSF C₁ hC₁).1 ⟨he_not1, ha₁, hb₁⟩).1.hins_wstr
            have hmem : e ∈ (applyLSFUpdate (cs.compSt C₁) (.insert e a b)).insertedEdges := by
              simp [applyLSFUpdate]
            simpa [applyLSFUpdate, MGraph.applyUpdate] using (hi₁ e hmem).2.1
          · simp only [ha₁, hb₁, and_false, ↓reduceIte]
            exact (applyLSFBatch_insert_delete_selfLoop (hI.hCompLSF C₁ hC₁).1 he_not1 ha₁).2.2.2.2.2.1
        have hbR : b ∈ (cs'.compSt C₂).R := by
          change b ∈ (applyLSFBatch (cs.compSt C₂) (projCompUpdateG cs.G (cs.compSt C₂).G (.insert e a b))).R
          dsimp only [projCompUpdateG]
          have he_not2 : e ∉ (cs.compSt C₂).G.E := fun h => hu.1 (hI.hCE_sub C₂ hC₂ h)
          by_cases ha₂ : a ∈ (cs.compSt C₂).G.V
          · simp only [ha₂, hb₂, and_self, ↓reduceIte, applyLSFBatch, List.foldl_cons, List.foldl_nil]
            have hi₂ := (applyLSFUpdate_inv_with (u := .insert e a b) (hI.hCompLSF C₂ hC₂).1 ⟨he_not2, ha₂, hb₂⟩).1.hins_wstr
            have hmem : e ∈ (applyLSFUpdate (cs.compSt C₂) (.insert e a b)).insertedEdges := by
              simp [applyLSFUpdate]
            simpa [applyLSFUpdate, MGraph.applyUpdate] using (hi₂ e hmem).2.2
          · simp only [ha₂, hb₂, false_and, ↓reduceIte]
            exact (applyLSFBatch_insert_delete_selfLoop (hI.hCompLSF C₂ hC₂).1 he_not2 hb₂).2.2.2.2.2.1
        refine ⟨Function.update_self _ _ _, ⟨C₁, hC₁, ?_⟩, ⟨C₂, hC₂, ?_⟩⟩
        · simpa [cs', compLSFStepSingle, MGraph.applyUpdate] using haR
        · simpa [cs', compLSFStepSingle, MGraph.applyUpdate] using hbR
      · have he₀I : e ∈ cs.insertedGlobal := (Finset.mem_insert.mp he).resolve_left he₀
        have hw := hI.hIns_wstr_R e he₀I
        have ht_eq : cs'.G.tail e = cs.G.tail e := by
          simp [cs', compLSFStepSingle, MGraph.applyUpdate, Function.update_of_ne he₀]
        have hh_eq : cs'.G.head e = cs.G.head e := by
          simp [cs', compLSFStepSingle, MGraph.applyUpdate, Function.update_of_ne he₀]
        refine ⟨?_, ?_, ?_⟩
        · simpa [cs', compLSFStepSingle, Function.update_of_ne he₀] using hw.1
        · rcases hw.2.1 with ⟨C₁, hC₁, hR₁⟩
          exact ⟨C₁, hC₁, ht_eq ▸ (hC_step C₁ hC₁).2.2.2.2.1 hR₁⟩
        · rcases hw.2.2 with ⟨C₂, hC₂, hR₂⟩
          exact ⟨C₂, hC₂, hh_eq ▸ (hC_step C₂ hC₂).2.2.2.2.1 hR₂⟩
    | split v v' St Sh =>
      have hw := hI.hIns_wstr_R e he
      have hv'_in : ∀ C ∈ components cs.G₀, v ∈ (cs.compSt C).G.V → v' ∈ (cs'.compSt C).R := by
        intro C hC hvC
        have hp : projCompUpdateG cs.G (cs.compSt C).G (.split v v' St Sh) =
            [.split v v'
              ((cs.compSt C).G.E.filter fun f => f ∈ St ∧ (cs.compSt C).G.tail f = v ∧ cs.G.tail f = v)
              ((cs.compSt C).G.E.filter fun f => f ∈ Sh ∧ (cs.compSt C).G.head f = v ∧ cs.G.head f = v)] := by
          simp [projCompUpdateG, hvC]
        change v' ∈ (applyLSFBatch (cs.compSt C) _).R
        rw [hp, applyLSFBatch, List.foldl_cons, List.foldl_nil]
        exact Finset.mem_union_right _ (by simp [applyLSFUpdate])
      refine ⟨hw.1, ?_, ?_⟩
      · rcases hw.2.1 with ⟨C₁, hC₁, hR₁⟩
        refine ⟨C₁, hC₁, ?_⟩
        change (cs.G.applyUpdate (.split v v' St Sh)).tail e ∈ (cs'.compSt C₁).R
        dsimp only [MGraph.applyUpdate]
        split_ifs with ht
        · have hvC₁ : v ∈ (cs.compSt C₁).G.V :=
            lsfInv_R_sub_V (hI.hCompLSF C₁ hC₁).1 (ht.2 ▸ hR₁)
          exact hv'_in C₁ hC₁ hvC₁
        · exact (hC_step C₁ hC₁).2.2.2.2.1 hR₁
      · rcases hw.2.2 with ⟨C₂, hC₂, hR₂⟩
        refine ⟨C₂, hC₂, ?_⟩
        change (cs.G.applyUpdate (.split v v' St Sh)).head e ∈ (cs'.compSt C₂).R
        dsimp only [MGraph.applyUpdate]
        split_ifs with hh
        · have hvC₂ : v ∈ (cs.compSt C₂).G.V :=
            lsfInv_R_sub_V (hI.hCompLSF C₂ hC₂).1 (hh.2 ▸ hR₂)
          exact hv'_in C₂ hC₂ hvC₂
        · exact (hC_step C₂ hC₂).2.2.2.2.1 hR₂
  have hWstr_surv' : ∀ e ∈ cs'.G.E, e ∉ cs'.insertedGlobal →
      ∃ C ∈ components cs.G₀, e ∈ (cs'.compSt C).G.E ∧ e ∉ (cs'.compSt C).insertedEdges ∧
        cs'.wstrGlobal e = (cs'.compSt C).wstr e := by
    intro e he hni
    have he_old : e ∈ cs.G.E := by
      cases u with
      | delete e₀ => exact (Finset.mem_erase.mp he).2
      | insert e₀ a b =>
        rcases Finset.mem_insert.mp he with rfl | hmem
        · exact absurd (Finset.mem_insert_self _ _) hni
        · exact hmem
      | split _ _ _ _ => exact he
    have hni_old : e ∉ cs.insertedGlobal := by
      intro hm
      cases u with
      | delete e₀ =>
        exact hni (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp he).1, hm⟩)
      | insert e₀ _ _ =>
        exact hni (Finset.mem_insert_of_mem hm)
      | split _ _ _ _ => exact hni hm
    obtain ⟨C, hC, heC, hniC, hwC⟩ := hI.hWstr_surv e he_old hni_old
    refine ⟨C, hC, ?_, ?_, ?_⟩
    · rw [(hC_step C hC).2.1]
      cases u with
      | delete e₀ =>
        have hne : e ≠ e₀ := (Finset.mem_erase.mp he).1
        dsimp only [projCompUpdateG]
        split_ifs
        · exact Finset.mem_erase.mpr ⟨hne, heC⟩
        · exact heC
      | insert e₀ a b =>
        have hne : e ≠ e₀ := fun h => hni (h ▸ Finset.mem_insert_self _ _)
        dsimp only [projCompUpdateG]
        split_ifs <;> simp [heC, hne, MGraph.applyBatch, MGraph.applyUpdate]
      | split v v' St Sh =>
        dsimp only [projCompUpdateG]
        split_ifs <;> exact heC
    · have hins_eq : (cs'.compSt C).insertedEdges =
          (projCompUpdateG cs.G (cs.compSt C).G u).foldl updateInserted (cs.compSt C).insertedEdges :=
        applyLSFBatch_insertedEdges (projCompUpdateG cs.G (cs.compSt C).G u) (cs.compSt C)
      rw [hins_eq]
      cases u with
      | delete e₀ =>
        dsimp only [projCompUpdateG]
        split_ifs
        · simp [updateInserted, hniC]
        · exact hniC
      | insert e₀ a b =>
        have hne : e ≠ e₀ := fun h => hni (h ▸ Finset.mem_insert_self _ _)
        dsimp only [projCompUpdateG]
        split_ifs <;> simp [updateInserted, hniC, hne]
      | split v v' St Sh =>
        dsimp only [projCompUpdateG]
        split_ifs <;> exact hniC
    · cases u with
      | delete e₀ =>
        change cs.wstrGlobal e = (applyLSFBatch (cs.compSt C) _).wstr e
        dsimp only [projCompUpdateG]
        split_ifs <;> simp [applyLSFBatch, applyLSFUpdate, hwC]
      | insert e₀ a b =>
        have hne : e ≠ e₀ := fun h => hni (h ▸ Finset.mem_insert_self _ _)
        change Function.update cs.wstrGlobal e₀ 1 e = (applyLSFBatch (cs.compSt C) _).wstr e
        rw [Function.update_of_ne hne, hwC]
        dsimp only [projCompUpdateG]
        split_ifs <;> simp [applyLSFBatch, applyLSFUpdate, Function.update_of_ne hne]
      | split v v' St Sh =>
        change cs.wstrGlobal e = (applyLSFBatch (cs.compSt C) _).wstr e
        dsimp only [projCompUpdateG]
        split_ifs <;> simp [applyLSFBatch, applyLSFUpdate, hwC]
  have hF_sub_compE' : ∀ C ∈ components cs.G₀, (cs'.compSt C).RF.F.E ⊆ compEdgeSet cs'.G₀ C := by
    intro C hC
    exact Finset.Subset.trans (hC_step C hC).2.2.2.2.2 (hI.hF_sub_compE C hC)
  have hCE_ins' : ∀ C ∈ components cs.G₀, ∀ e ∈ (cs'.compSt C).G.E,
      e ∈ cs'.insertedGlobal → e ∈ (cs'.compSt C).insertedEdges := by
    intro C hC e he hins
    have he_upd := (hC_step C hC).2.1 ▸ he
    have hins_eq : (cs'.compSt C).insertedEdges =
        (projCompUpdateG cs.G (cs.compSt C).G u).foldl updateInserted (cs.compSt C).insertedEdges :=
      applyLSFBatch_insertedEdges (projCompUpdateG cs.G (cs.compSt C).G u) (cs.compSt C)
    rw [hins_eq]
    cases u with
    | delete e₀ =>
      have hm := Finset.mem_erase.mp hins
      dsimp only [projCompUpdateG] at he_upd ⊢
      split_ifs at he_upd ⊢
      · have he_old := (Finset.mem_erase.mp he_upd).2
        rw [List.foldl_cons, List.foldl_nil, updateInserted]
        exact Finset.mem_erase.mpr ⟨hm.1, hI.hCE_ins C hC e he_old hm.2⟩
      · exact hI.hCE_ins C hC e he_upd hm.2
    | insert e₀ a b =>
      by_cases he₀ : e = e₀
      · subst he₀
        dsimp only [projCompUpdateG] at he_upd ⊢
        split_ifs at he_upd ⊢
        · exact Finset.mem_insert_self _ _
        · simp [MGraph.applyBatch, MGraph.applyUpdate] at he_upd
        · simp [MGraph.applyBatch, MGraph.applyUpdate] at he_upd
        · exact absurd he_upd (fun h => hu.1 (hI.hCE_sub C hC h))
      · have hm := (Finset.mem_insert.mp hins).resolve_left he₀
        dsimp only [projCompUpdateG] at he_upd ⊢
        split_ifs at he_upd ⊢
        all_goals
          have he_old : e ∈ (cs.compSt C).G.E := by
            simp only [MGraph.applyBatch, List.foldl_cons, List.foldl_nil, MGraph.applyUpdate,
              Finset.mem_erase, Finset.mem_insert, he₀, false_or, ne_eq, not_false_eq_true,
              true_and] at he_upd
            exact he_upd
          have hmem_old : e ∈ (cs.compSt C).insertedEdges := hI.hCE_ins C hC e he_old hm
          simp [updateInserted, he₀, hmem_old]
    | split v v' St Sh =>
      dsimp only [projCompUpdateG] at he_upd ⊢
      split_ifs at he_upd ⊢ <;> exact hI.hCE_ins C hC e he_upd hins
  have hCompE_notCross' : ∀ C ∈ components cs.G₀, ∀ e ∈ (cs'.compSt C).G.E, e ∉ cs'.crossEdges := by
    intro C hC e he hcr
    have he_upd := (hC_step C hC).2.1 ▸ he
    cases u with
    | delete e₀ =>
      have hne : e ≠ e₀ := (Finset.mem_erase.mp hcr).1
      have hcr₀ : e ∈ cs.crossEdges := (Finset.mem_erase.mp hcr).2
      dsimp only [projCompUpdateG] at he_upd
      split_ifs at he_upd
      · exact hI.hCompE_notCross C hC e (Finset.mem_erase.mp he_upd).2 hcr₀
      · exact hI.hCompE_notCross C hC e he_upd hcr₀
    | insert e₀ a b =>
      dsimp only [projCompUpdateG] at he_upd
      by_cases he₀ : e = e₀
      · subst he₀
        split_ifs at he_upd with h1
        · have hex : ∃ D ∈ components cs.G₀, a ∈ (cs.compSt D).G.V ∧ b ∈ (cs.compSt D).G.V :=
            ⟨C, hC, h1.1, h1.2⟩
          change e ∈ (if ∃ D ∈ components cs.G₀, a ∈ (cs.compSt D).G.V ∧ b ∈ (cs.compSt D).G.V
            then cs.crossEdges else insert e cs.crossEdges) at hcr
          rw [ite_eq_left hex] at hcr
          exact hu.1 (hI.hIns_sub (hI.hCross_sub hcr))
        · simp [MGraph.applyBatch, MGraph.applyUpdate] at he_upd
        · simp [MGraph.applyBatch, MGraph.applyUpdate] at he_upd
        · exact hu.1 (hI.hCE_sub C hC he_upd)
      · have hcr₀ : e ∈ cs.crossEdges := by
          change e ∈ (if ∃ D ∈ components cs.G₀, a ∈ (cs.compSt D).G.V ∧ b ∈ (cs.compSt D).G.V
            then cs.crossEdges else insert e₀ cs.crossEdges) at hcr
          split_ifs at hcr
          · exact hcr
          · exact (Finset.mem_insert.mp hcr).resolve_left he₀
        have he_old : e ∈ (cs.compSt C).G.E := by
          split_ifs at he_upd <;>
            (simp only [MGraph.applyBatch, List.foldl_cons, List.foldl_nil, MGraph.applyUpdate,
              Finset.mem_erase, Finset.mem_insert, he₀, false_or, ne_eq, not_false_eq_true,
              true_and] at he_upd; exact he_upd)
        exact hI.hCompE_notCross C hC e he_old hcr₀
    | split v v' St Sh =>
      dsimp only [projCompUpdateG] at he_upd
      split_ifs at he_upd <;> exact hI.hCompE_notCross C hC e he_upd hcr
  exact ⟨hI.hG₀_val, hG'_val, hI.hV₀, hI.hk, hI.hℓ₀,
    fun C hC => ⟨(hC_step C hC).1, (hC_step C hC).2.2.1, (hC_step C hC).2.2.2.1⟩,
    hV_disj', hV_eq', hCE_sub', hCross_sub', hIns_sub', hCompIns_sub',
    hNonCross_ends', hNonIns_notCross', hEdge_cover', hEdge_atMostTwo',
    hIns_wstr_R', hWstr_surv', hF_sub_compE', hCE_ins', hCompE_notCross'⟩

lemma compLSFBatch_step_props {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} :
    ∀ (U : List Update) {cs : CompLSFState},
      CompLSFInv C_lsst ℓ₀ cs → cs.G.BatchIsValid U →
      let cs' := compLSFBatch cs U
      CompLSFInv C_lsst ℓ₀ cs' ∧
      cs'.G = cs.G.applyBatch U ∧
      (∀ C ∈ components cs.G₀,
        cs'.compSt C = applyLSFBatch (cs.compSt C) (projCompBatchG cs.G (cs.compSt C).G U) ∧
        (cs'.compSt C).G = (cs.compSt C).G.applyBatch (projCompBatchG cs.G (cs.compSt C).G U) ∧
        (cs.compSt C).G.BatchIsValid (projCompBatchG cs.G (cs.compSt C).G U) ∧
        (cs.compSt C).R ⊆ (cs'.compSt C).R ∧
        (cs'.compSt C).RF.F.E ⊆ (cs.compSt C).RF.F.E) ∧
      cs'.RF.F.E ⊆ cs.RF.F.E ∧
      cs.RF.R ⊆ cs'.RF.R
  | [], cs, hI, _ => by
    refine ⟨hI, rfl, fun C hC => ⟨rfl, rfl, trivial, Finset.Subset.rfl, Finset.Subset.rfl⟩,
      Finset.Subset.rfl, Finset.Subset.rfl⟩
  | u :: rest, cs, hI, ⟨hu, hrest⟩ => by
    have h1 := compLSFInv_step hI hu
    set cs1 := compLSFStepSingle cs u
    have ih := compLSFBatch_step_props rest h1 hrest
    have hcs1_G₀ : cs1.G₀ = cs.G₀ := rfl
    have hcs1_G : cs1.G = cs.G.applyUpdate u := rfl
    refine ⟨ih.1, ih.2.1, fun C hC => ?_, ?_, ?_⟩
    · have hBV1 := projCompUpdateG_valid hI hu hC
      have hC1 := applyLSFBatch_inv_with (projCompUpdateG cs.G (cs.compSt C).G u)
        (hI.hCompLSF C hC).1 hBV1
      have hihC := ih.2.2.1 C (hcs1_G₀ ▸ hC)
      have hG1C : (cs1.compSt C).G =
          (cs.compSt C).G.applyBatch (projCompUpdateG cs.G (cs.compSt C).G u) := hC1.2.1
      dsimp only [projCompBatchG]
      rw [← hcs1_G, ← hG1C]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · change _ = List.foldl applyLSFUpdate (cs.compSt C) _
        rw [List.foldl_append]; exact hihC.1
      · change ((compLSFBatch cs1 rest).compSt C).G =
            (cs.compSt C).G.applyBatch
              (projCompUpdateG cs.G (cs.compSt C).G u ++ projCompBatchG cs1.G (cs1.compSt C).G rest)
        rw [applyBatch_append, ← hG1C]; exact hihC.2.1
      · exact batchIsValid_append.mpr ⟨hBV1, hG1C ▸ hihC.2.2.1⟩
      · exact Finset.Subset.trans hC1.2.2.2.2.2.2.2.2.1 hihC.2.2.2.1
      · exact Finset.Subset.trans hihC.2.2.2.2 hC1.2.2.2.2.2.2.2.2.2.1
    · change (compLSFBatch cs1 rest).RF.F.E ⊆ cs.RF.F.E
      intro e he
      change e ∈ (components (compLSFBatch cs1 rest).G₀).biUnion
          (fun C => ((compLSFBatch cs1 rest).compSt C).RF.F.E) at he
      rw [compLSFBatch_G₀] at he
      rw [Finset.mem_biUnion] at he
      rcases he with ⟨C, hC, heC⟩
      have hC₀ : C ∈ components cs.G₀ := hcs1_G₀ ▸ hC
      have hBV1 := projCompUpdateG_valid hI hu hC₀
      have hC1 := applyLSFBatch_inv_with (projCompUpdateG cs.G (cs.compSt C).G u)
        (hI.hCompLSF C hC₀).1 hBV1
      have he1 : e ∈ (cs1.compSt C).RF.F.E := (ih.2.2.1 C hC).2.2.2.2 heC
      change e ∈ (components cs.G₀).biUnion (fun C => (cs.compSt C).RF.F.E)
      exact Finset.mem_biUnion.mpr ⟨C, hC₀, hC1.2.2.2.2.2.2.2.2.2.1 he1⟩
    · change cs.RF.R ⊆ (compLSFBatch cs1 rest).RF.R
      intro r hr
      change r ∈ (components cs.G₀).biUnion (fun C => (cs.compSt C).R) at hr
      rw [Finset.mem_biUnion] at hr
      rcases hr with ⟨C, hC, hrC⟩
      have hBV1 := projCompUpdateG_valid hI hu hC
      have hC1 := applyLSFBatch_inv_with (projCompUpdateG cs.G (cs.compSt C).G u)
        (hI.hCompLSF C hC).1 hBV1
      have hr1 : r ∈ (cs1.compSt C).R := hC1.2.2.2.2.2.2.2.2.1 hrC
      change r ∈ (components (compLSFBatch cs1 rest).G₀).biUnion
          (fun C => ((compLSFBatch cs1 rest).compSt C).R)
      rw [compLSFBatch_G₀]
      exact Finset.mem_biUnion.mpr ⟨C, hcs1_G₀ ▸ hC, (ih.2.2.1 C (hcs1_G₀ ▸ hC)).2.2.2.1 hr1⟩

end

end MinCostFlow.SparseCore
