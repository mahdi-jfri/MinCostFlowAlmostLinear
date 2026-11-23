module

public import MinCostFlow.ExpanderDecomp.OuterProgRecChild
import MinCostFlow.ExpanderDecomp.OuterProgRecWitPrefix
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Witness-Branch Verification for `outerDecompRecProc` (`OuterProgRecWit`)

Proves `recWitness_runs` by composing `recWitnessPrefix_runs`, `recWitness_mid_runs`,
`recChild_runs`, and `progRecSpec_witness_combine`.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander MinCostFlow.ExplicitExpander

lemma recWitness_runs {M r w C_core C_rt C_sp routeC : ℕ}
    {pProg : Program} {idx : OuterRecIndices} {G : Graph}
    {paramAddr locAddr labelsAddr nextLblAddr hRoot : ℕ}
    (env : RecGlobalEnv ParamConfig.default M r w G paramAddr locAddr labelsAddr nextLblAddr hRoot)
    (hSub : RecSubprocs M r w pProg idx C_core C_rt C_sp routeC)
    {ω : ℕ → Bool} {eBound : ℕ}
    (hIH : RecIH ParamConfig.default M r w C_core C_rt C_sp routeC pProg idx G
      paramAddr locAddr labelsAddr nextLblAddr hRoot ω eBound)
    {H : CompactSubgraph} {vertsAddr edgesAddr h h3 nl₀ c3 : ℕ} {st st3 : State}
    {W_out F_out : List (ℕ × ℕ)}
    (heBound : H.edges.length ≤ eBound + 1)
    (hRep : H.Represents G H.vertSet) (hXV : H.vertSet ⊆ G.verts)
    (hSorted : H.verts.Pairwise (· < ·)) (hXdeg : ∀ v ∈ H.vertSet, 1 ≤ G.degIn H.vertSet v)
    (heM : H.edges.length ≤ M) (hQlt : QOut ParamConfig.default M r < H.edges.length)
    (hGameSpec : OuterGameOutcomeSpec ParamConfig.default M r H.edges.length
      (portGraph cloud G H.vertSet) (.witness W_out F_out))
    (hRoot_le : hRoot ≤ h)
    (hVA_h : vertsAddr + H.verts.length ≤ h) (hEA_h : edgesAddr + 2 * H.edges.length ≤ h)
    (hdLV : DisjointRange locAddr G.n vertsAddr H.verts.length)
    (hdLbV : DisjointRange labelsAddr G.n vertsAddr H.verts.length)
    (hdNV : DisjointRange nextLblAddr 1 vertsAddr H.verts.length)
    (hdLE : DisjointRange locAddr G.n edgesAddr (2 * H.edges.length))
    (hdLbE : DisjointRange labelsAddr G.n edgesAddr (2 * H.edges.length))
    (hdNE : DisjointRange nextLblAddr 1 edgesAddr (2 * H.edges.length))
    (hPB : OuterParamBlockAt st.mem paramAddr ParamConfig.default G.n M r)
    (hV : ListAt st.mem vertsAddr H.verts) (hE : EdgesAt st.mem edgesAddr H.edges)
    (hloc0 : ∀ u < G.n, st.mem (locAddr + u) = 0)
    (hnl : st.mem nextLblAddr = nl₀) (hnl_le : nl₀ + H.verts.length ≤ G.n)
    (hSpace : h + recTreeSpace (DOut ParamConfig.default M r)
      (recPerEdgeSpace ParamConfig.default C_sp M r routeC)
      (recPerWitSpace ParamConfig.default M r) H.edges.length < 2 ^ w)
    (hr0 : st.regs 0 = H.verts.length) (hr1 : st.regs 1 = vertsAddr)
    (hr2 : st.regs 2 = H.edges.length) (hr3 : st.regs 3 = edgesAddr)
    (hr4 : st.regs 4 = paramAddr) (hr5 : st.regs 5 = locAddr)
    (hr6 : st.regs 6 = labelsAddr) (hr7 : st.regs 7 = nextLblAddr)
    (h3_r10 : st3.regs 10 = h) (h3_r15 : st3.regs 15 = h3)
    (h3_r14_le : st3.regs 14 + 4 ≤ h3) (h3_ge : h + 2 * H.edges.length ≤ h3)
    (h3_le : h3 ≤ h + 2 * H.edges.length + (2 + 20 * H.edges.length) +
      portGraphWorkSpace H.verts.length H.edges.length + portGraphHeapSpace H.edges.length + 4 +
      outerGameSpace C_sp M r H.edges.length
        (outerGameMaxCost ParamConfig.default M r routeC H.edges.length))
    (hZero3 : ZeroFrom st3.mem h3)
    (hOwn3 : ListAt st3.mem h (portOwnersList H.edges))
    (hOut3 : OuterGameOutAt st3.mem (st3.regs 14) h h3 H.edges.length (.witness W_out F_out))
    (h3_regs : ∀ r' ≤ 9, st3.regs r' = st.regs r')
    (h3_belowH : ∀ a < h, st3.mem a = st.mem a)
    (hc3 : c3 ≤ outerGameStepBound C_core C_rt r H.edges.length
        (outerGameMaxCost ParamConfig.default M r routeC H.edges.length) +
      portGraphCost H.verts.length H.edges.length + 70) :
    ∃ h' st' c,
      Runs w pProg ω (recWitnessStmt idx) st3 (.returned h') st' c ∧
      RecNodePost ParamConfig.default M r C_core C_rt C_sp routeC G locAddr labelsAddr nextLblAddr
        h H st.mem nl₀ h' st'.mem (c3 + c + 20) := by
  let cfg := ParamConfig.default
  set k := H.verts.length
  set e := H.edges.length
  set Λ := Lambda cfg M r
  set L := LParam M
  set lc := outerGameMaxCost cfg M r routeC e
  have he_eq : (G.inside H.vertSet).length = e := congrArg List.length hRep.2.2.symm
  have he1 : 1 ≤ e := by unfold QOut at hQlt; omega
  have hk_le_2e : k ≤ 2 * e := by
    have := verts_length_le_two_mul_edges hRep hXdeg; omega
  have hlc_le : lc ≤ e * modelPerEdge cfg M r routeC := outerGameMaxCost_le_modelPerEdge he1
  have hnode_sp := recNode_space_le (cfg := cfg) (C_sp := C_sp) he1 heM hk_le_2e hlc_le
  have hL4 : 4 ≤ L := four_le_LParam M
  have hLam1 : 1 ≤ Λ := one_le_Lambda cfg M r
  have hD1 : 1 ≤ DOut cfg M r := one_le_DOut cfg M r
  have hb1 : 1 ≤ bOut cfg M := one_le_bOut cfg M
  -- Mathematical witness guarantees from `hGameSpec`
  rcases hGameSpec with ⟨hW_exp, hF_valid, hF_len_tz, hF_deg, emb, hemb, hcong⟩
  change (Graph.mk (2 * e) W_out).IsExpansionExpanderOn (Finset.range (2 * e))
      (1 / (2 * (PParam cfg M r : ℝ))) at hW_exp
  change F_out.length ≤ tParam M * (e / DOut cfg M r) at hF_len_tz
  set mF := F_out.length
  have hmF_le_e : mF ≤ e :=
    le_trans hF_len_tz (tParam_mul_div_DOut_le cfg env.hA60 M r e)
  set F' := contractEdges G H.vertSet F_out
  set mF' := F'.length
  have hmF'_le_mF : mF' ≤ mF := (List.length_filter_le _ _).trans (by simp [mF])
  have hmF'_le_e : mF' ≤ e := le_trans hmF'_le_mF hmF_le_e
  -- Buffer addresses above `h3`
  set f'Addr := h3
  set rhoAddr := f'Addr + 2 * mF
  set rAddr := rhoAddr + 2
  set restVAddr := rAddr + k
  set restEAddr := restVAddr + k
  set actRestAddr := restEAddr + 2 * e
  set rfWorkAddr := actRestAddr + k
  set h4 := rfWorkAddr + rfWorkBound k e mF' Λ L
  have hrf_sp := rfArith_le_witSpace (cfg := cfg) (M := M) (r := r) he1 heM hk_le_2e hmF'_le_e env.h2M_L
  have hrfWork_mF_le : rfWorkBound k e mF Λ L ≤ e * recPerWitSpace cfg M r :=
    (rfArith_le_witSpace he1 heM hk_le_2e hmF_le_e env.h2M_L).2
  have hrfAddr_le : rfWorkAddr + 3 ≤ h + e * recPerEdgeSpace cfg C_sp M r routeC := by
    dsimp only [rfWorkAddr, actRestAddr, restEAddr, restVAddr, rAddr, rhoAddr, f'Addr]
    linarith only [h3_le, hnode_sp, hmF_le_e]
  have hd1 : 1 ≤ recDepthBound (DOut cfg M r) e := by
    cases heq : e with
    | zero => exfalso; linarith only [he1, heq]
    | succ b => rw [recDepthBound]; simp [hD1]
  have hTree_ew : e * recPerEdgeSpace cfg C_sp M r routeC + e * recPerWitSpace cfg M r ≤
      recTreeSpace (DOut cfg M r) (recPerEdgeSpace cfg C_sp M r routeC) (recPerWitSpace cfg M r) e := by
    unfold recTreeSpace
    have h1 : 1 * e * recPerEdgeSpace cfg C_sp M r routeC ≤
        recDepthBound (DOut cfg M r) e * e * recPerEdgeSpace cfg C_sp M r routeC :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right e hd1)
    rw [one_mul] at h1
    have h2 : e * recPerWitSpace cfg M r ≤ 2 * e * recPerWitSpace cfg M r :=
      Nat.mul_le_mul_right _ (by linarith only [])
    linarith only [h1, h2]
  have hSpace' : h + recTreeSpace (DOut cfg M r) (recPerEdgeSpace cfg C_sp M r routeC)
      (recPerWitSpace cfg M r) e < 2 ^ w := hSpace
  have hrfEnd_lt : rfWorkAddr + e * recPerWitSpace cfg M r + 3 < 2 ^ w := by
    linarith only [hrfAddr_le, hTree_ew, hSpace']
  have hrf_eq_full : rfWorkAddr = h3 + 2 * mF + 2 + 3 * k + 2 * e := by
    dsimp only [rfWorkAddr, actRestAddr, restEAddr, restVAddr, rAddr, rhoAddr, f'Addr]; ring
  have hPre := recWitnessPrefix_runs env hSub.hContract hRep hRoot_le hPB hr0 hr2 hr4
    h3_r10 h3_r15 h3_r14_le h3_ge hOwn3 hOut3 h3_regs h3_belowH (by rw [he_eq]; exact hF_valid) (by
      have : h3 + 2 * mF + 2 + 3 * k + 2 * e + rfWorkBound k e mF Λ L =
          rfWorkAddr + rfWorkBound k e mF Λ L := by linarith only [hrf_eq_full]
      linarith only [this, hrfWork_mF_le, hrfEnd_lt]) (ω := ω)
  rcases hPre with ⟨st34, h34_19, h34_20, h34_24, h34_25, h34_26, h34_27, h34_29, h34_33, h34_34,
    h34_r0_9, h34_F', h34_rho0, h34_rho1, h34_fr, hPreChain⟩
  have hsubV : ∀ u ∈ H.verts, u < G.n := fun u hu =>
    Finset.mem_range.mp (hXV (List.mem_toFinset.mpr hu))
  have hF'_inX : ∀ ed ∈ F', ed.1 ∈ H.vertSet ∧ ed.2 ∈ H.vertSet := fun ed hed => by
    have hmem := (List.mem_filter.mp hed).1
    rcases List.mem_map.mp hmem with ⟨ep, hep, rfl⟩
    have h12 : ep.1 < 2 * e ∧ ep.2 < 2 * e := hF_valid ep hep
    have ho_in : ∀ p < 2 * e, portOwner G H.vertSet p ∈ H.vertSet := fun p hp => by
      have hlen : (portOwnersList H.edges).length = 2 * e := portOwnersList_length H.edges
      rw [← portOwnersList_getD_eq_portOwner hRep.2.2.symm hp,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlen ▸ hp), Option.getD_some]
      have hmem_p : (portOwnersList H.edges)[p]'(hlen ▸ hp) ∈ portOwnersList (G.inside H.vertSet) := by
        rw [← hRep.2.2]; exact List.getElem_mem _
      exact mem_portOwnersList_inside hmem_p
    exact ⟨ho_in ep.1 h12.1, ho_in ep.2 h12.2⟩
  have hE_inX : ∀ ed ∈ H.edges, ed.1 ∈ H.vertSet ∧ ed.2 ∈ H.vertSet := fun ed hed => by
    rw [hRep.2.2] at hed; exact (mem_inside_iff.mp hed).2
  have hPreRF := outerWitness_pre_removeFake cloud_isCloudExpander hXdeg
    (by rw [he_eq]; exact hW_exp) (by rw [he_eq]; exact hF_valid)
    (by rw [he_eq]; exact hF_deg) (by rw [he_eq]; exact hemb) hcong
  rw [← hRep.2.2] at hPreRF
  have hMid := recWitness_mid_runs env hSub.hRF hSub.hSetDiff hRep hXV he1 heM hk_le_2e
    hmF'_le_mF hmF'_le_e hRoot_le hVA_h hEA_h hdLV hdLbV hdNV hdLE hV hE hloc0 hnl hnl_le
    hr0 hr1 hr2 hr3 hr5 hr6 hr7 h3_ge hZero3 h3_belowH hF'_inX hE_inX hPreRF
    h34_19 h34_20 h34_24 (by dsimp only [restVAddr, rAddr, rhoAddr, f'Addr] at h34_25 ⊢; exact h34_25)
    (by dsimp only [restEAddr, restVAddr, rAddr, rhoAddr, f'Addr] at h34_26 ⊢; linarith only [h34_26])
    h34_27
    (by dsimp only [actRestAddr, restEAddr, restVAddr, rAddr, rhoAddr, f'Addr] at h34_29 ⊢; linarith only [h34_29])
    (by dsimp only [rfWorkAddr, actRestAddr, restEAddr, restVAddr, rAddr, rhoAddr, f'Addr] at h34_33 ⊢; linarith only [h34_33])
    (by change st34.regs 34 = h3 + 2 * mF + 2 + k + k + 2 * e + k + rfWorkBound k e mF' Λ L at h34_34
        rw [h34_34]; ring)
    h34_r0_9 h34_F' h34_rho0 h34_rho1 h34_fr
    (by have : h3 + 2 * mF + 2 + 3 * k + 2 * e + e * recPerWitSpace cfg M r + 3 =
          rfWorkAddr + e * recPerWitSpace cfg M r + 3 := by linarith only [hrf_eq_full]
        linarith only [this, hrfEnd_lt]) (ω := ω)
  rcases hMid with ⟨stSD, R_list, cRF, cWC, cSD, hkR_le, hR_nd, hRX, hRF_spec,
    hSD_30, hSD_25, hSD_26, hSD_29, hSD_34, hSD_r0_9, hSD_restV, hSD_Rlbl, hSD_nl,
    hSD_loc0, hSD_zero, hSD_belowH, hcRF, hcWC, hcSD, hMidChain⟩
  set kR := R_list.length
  set R := R_list.toFinset
  change R ⊆ H.vertSet at hRX
  obtain ⟨hRcond_raw, _, _, hRvol_raw⟩ := hRF_spec G.n hsubV
  have hF'_len_tz : F'.length ≤ tParam M * ((G.inside H.vertSet).length / DOut cfg M r) := by
    rw [he_eq]; exact le_trans hmF'_le_mF hF_len_tz
  have hPostRF := outerWitness_post_removeFake env.hA60 hRX (by rw [he_eq]; exact he1) hF'_len_tz
    (by rw [hRep.2.2] at hRcond_raw; exact hRcond_raw)
    (by rw [hRep.2.2] at hRvol_raw; exact hRvol_raw)
  rcases hPostRF with ⟨hRne, hRcond, h35⟩
  obtain ⟨h16_rest, hshR_in, hltR_in, h15_ret, h16_cut⟩ :=
    edge_shrink_witness G hRX hb1 hD1 (by rw [he_eq]; exact he1) h35
  have hrepR := CompactSubgraph.restrict_represents hRep (Finset.sdiff_subset (s := H.vertSet) (t := R))
  have hstR := CompactSubgraph.stripIsolated_spec hrepR
  set isoRest := (H.restrict (H.vertSet \ R)).stripIsolated.1
  set actRest := (H.restrict (H.vertSet \ R)).stripIsolated.2
  have heRest_in : actRest.edges = G.inside (H.vertSet \ R) := hstR.2.2.2.2.2.1.trans hrepR.2.2
  have heRest_eq : (H.restrict (H.vertSet \ R)).edges.length = (G.inside (H.vertSet \ R)).length :=
    congrArg List.length hrepR.2.2
  have heRest_act : actRest.edges.length = (H.restrict (H.vertSet \ R)).edges.length :=
    congrArg List.length hstR.2.2.2.2.2.1
  have htree_w := recTreeSpace_witness_step (D := DOut cfg M r)
    (perE := recPerEdgeSpace cfg C_sp M r routeC) (perW := recPerWitSpace cfg M r)
    (e := e) (eRest := (H.restrict (H.vertSet \ R)).edges.length)
    hD1 he1
    (by rw [heRest_eq, ← he_eq]
        exact le_trans (Nat.mul_le_mul_right _ (by linarith only [hb1] : 16 ≤ 32 * bOut cfg M)) h16_rest)
    (by rw [heRest_eq, ← he_eq]; exact hshR_in)
  have hkRest_lt : 1 + (H.restrict (H.vertSet \ R)).verts.length ≤ k := by
    have h1 : (H.restrict (H.vertSet \ R)).verts.toFinset.card + R.card = H.verts.toFinset.card := by
      rw [hrepR.2.1]; exact Finset.card_sdiff_add_card_eq_card hRX
    have hRpos : 1 ≤ R.card := Finset.Nonempty.card_pos hRne
    rw [List.toFinset_card_of_nodup hrepR.1, List.toFinset_card_of_nodup hRep.1] at h1
    linarith only [h1, hRpos]
  have hh_r : h ≤ rAddr :=
    le_trans (le_trans (Nat.le_add_right _ _) h3_ge) (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
  have hh_restV : h ≤ restVAddr := le_trans hh_r (Nat.le_add_right _ _)
  have hh_restE : h ≤ restEAddr := le_trans hh_restV (Nat.le_add_right _ _)
  have hh_actRest : h ≤ actRestAddr := le_trans hh_restE (Nat.le_add_right _ _)
  have hh4_ge_h : h ≤ h4 := le_trans hh_actRest (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
  have hSD_PB : OuterParamBlockAt stSD.mem paramAddr cfg G.n M r := by
    have hp : ∀ j < 12, stSD.mem (paramAddr + j) = st.mem (paramAddr + j) := fun j hj =>
      hSD_belowH _ (lt_of_lt_of_le (Nat.add_lt_add_left hj paramAddr) (le_trans env.hparH hRoot_le))
        (fun u hu => by have huN := Finset.mem_range.mp (hXV (hRX hu)); rcases env.hdPLb with h1 | h1 <;> linarith only [hj, huN, h1])
        (by rcases env.hdPN with h1 | h1 <;> linarith only [hj, h1])
        (fun u hu => by have huN := hsubV u hu; rcases env.hdPL with h1 | h1 <;> linarith only [hj, huN, h1])
    exact ⟨by rw [hp 0 (by decide)]; exact hPB.1, by rw [hp 1 (by decide)]; exact hPB.2.1,
      by rw [hp 2 (by decide)]; exact hPB.2.2.1, by rw [hp 3 (by decide)]; exact hPB.2.2.2.1,
      by rw [hp 4 (by decide)]; exact hPB.2.2.2.2.1, by rw [hp 5 (by decide)]; exact hPB.2.2.2.2.2.1,
      by rw [hp 6 (by decide)]; exact hPB.2.2.2.2.2.2.1, by rw [hp 7 (by decide)]; exact hPB.2.2.2.2.2.2.2.1,
      by rw [hp 8 (by decide)]; exact hPB.2.2.2.2.2.2.2.2.1, by rw [hp 9 (by decide)]; exact hPB.2.2.2.2.2.2.2.2.2.1,
      by rw [hp 10 (by decide)]; exact hPB.2.2.2.2.2.2.2.2.2.2.1, by rw [hp 11 (by decide)]; exact hPB.2.2.2.2.2.2.2.2.2.2.2⟩
  have hSD_E : EdgesAt stSD.mem edgesAddr H.edges := fun i hi => by
    have hm : ∀ j < 2 * e, stSD.mem (edgesAddr + j) = st.mem (edgesAddr + j) := fun j hj =>
      hSD_belowH (edgesAddr + j) (lt_of_lt_of_le (Nat.add_lt_add_left hj edgesAddr) hEA_h)
        (fun u hu => by have huN := Finset.mem_range.mp (hXV (hRX hu)); rcases hdLbE with h1 | h1 <;> linarith only [hj, huN, h1])
        (by rcases hdNE with h1 | h1 <;> linarith only [hj, h1])
        (fun u hu => by have huN := hsubV u hu; rcases hdLE with h1 | h1 <;> linarith only [hj, huN, h1])
    exact ⟨by rw [hm (2 * i) (by linarith only [hi])]; exact (hE i hi).1,
           by rw [Nat.add_assoc, hm (2 * i + 1) (by linarith only [hi]), ← Nat.add_assoc]; exact (hE i hi).2⟩
  have hrfB_le := hrf_sp.2
  have hh4_le_wit : h4 ≤ rfWorkAddr + e * recPerWitSpace cfg M r := by
    dsimp only [h4]; linarith only [hrfB_le]
  have hh4_tree : h4 + recTreeSpace (DOut cfg M r) (recPerEdgeSpace cfg C_sp M r routeC)
      (recPerWitSpace cfg M r) (H.restrict (H.vertSet \ R)).edges.length < 2 ^ w := by
    linarith only [hh4_le_wit, hrfAddr_le, htree_w, hSpace']
  have hltR : (H.restrict (H.vertSet \ R)).edges.length < e := by
    rw [heRest_eq, ← he_eq]; exact hltR_in
  have hChR := recChild_runs env hSub hIH hRep hXV hSorted Finset.sdiff_subset
    (Nat.le_of_lt_succ (lt_of_lt_of_le hltR heBound)) (le_trans (le_of_lt hltR) heM)
    (rK := 30) (rV := 25) (rE := 26) (rAct := 29) (rRest := 31) (rStrip := 32) (rH := 34)
    (by decide) (by decide) (by decide)
    (edgesAddr := edgesAddr) (vSAddr := restVAddr) (eSAddr := restEAddr)
    (actSAddr := actRestAddr) (hCur := h4) (nl₀ := nl₀ + 1) (st := stSD)
    (le_trans hRoot_le hh4_ge_h)
    (le_trans hEA_h hh4_ge_h)
    (by dsimp only [h4, rfWorkAddr, actRestAddr, restEAddr]; linarith only [hkRest_lt])
    (by dsimp only [h4, rfWorkAddr, actRestAddr]; linarith only [])
    (by dsimp only [h4, rfWorkAddr]; linarith only [hkRest_lt])
    hdLE
    (Or.inr (le_trans hEA_h hh_restE))
    (Or.inr (by dsimp only [restEAddr]; linarith only [hkRest_lt]))
    (Or.inr (by dsimp only [actRestAddr, restEAddr]; linarith only [hkRest_lt]))
    (Or.inr (by dsimp only [actRestAddr]; linarith only []))
    (le_trans hRoot_le hh_restV)
    (le_trans hRoot_le hh_restE)
    (le_trans hRoot_le hh_actRest)
    hSD_PB hSD_restV hSD_E hSD_loc0 hSD_nl (by linarith only [hkRest_lt, hnl_le]) hSD_zero hh4_tree
    (by rw [hSD_r0_9 2 (by decide), hr2]) (by rw [hSD_r0_9 3 (by decide), hr3])
    (by rw [hSD_r0_9 4 (by decide), hr4]) (by rw [hSD_r0_9 5 (by decide), hr5])
    (by rw [hSD_r0_9 6 (by decide), hr6]) (by rw [hSD_r0_9 7 (by decide), hr7])
    hSD_30 hSD_25 hSD_26 hSD_29 hSD_34
  rcases hChR with ⟨stEnd, h5, cCh, oRest, hrunCh, hoRSpec, hoRLbl, hoRNl, hh5_ge, hh5_le,
    hZero5, hloc5, hCh_fr, hCh_34, _, hcCh⟩
  have hRet : Runs w pProg ω (.ret (.reg 34)) stEnd (.returned h5) stEnd 2 :=
    runs_ret_iff.mpr ⟨h5, by simp [Expr.eval, hCh_34], rfl, rfl, by simp [Expr.size]⟩
  rcases runs_seq_iff.mp hrunCh with ⟨_, _, _, hno, _⟩ | ⟨stCa, cCa, cCbc, hCa, hCbc, rfl⟩
  · cases hno
  rcases runs_seq_iff.mp hCbc with ⟨_, _, _, hno, _⟩ | ⟨stCb, cCb, cCc, hCb, hCc, rfl⟩
  · cases hno
  have hTailRun :=
    runs_seq_iff.mpr (Or.inr ⟨stCa, cCa, _, hCa,
      runs_seq_iff.mpr (Or.inr ⟨stCb, cCb, _, hCb,
        runs_seq_iff.mpr (Or.inr ⟨stEnd, cCc, 2, hCc, hRet, rfl⟩), rfl⟩), rfl⟩)
  have hRestRun := hMidChain _ _ _ _ hTailRun
  rcases hPreChain _ _ _ _ hRestRun with ⟨cTot, hrunAll, hcTot⟩
  have hRLbl_end : LabelsMatchParts stEnd.mem labelsAddr R [R] nl₀ (nl₀ + 1) :=
    labelsMatchParts_const hRne fun u hu => by
      have huN : u < G.n := Finset.mem_range.mp (hXV (hRX hu))
      have hu_h : labelsAddr + u < h := lt_of_lt_of_le (Nat.add_lt_add_left huN labelsAddr) (le_trans env.hlblH hRoot_le)
      rw [hCh_fr (labelsAddr + u) (lt_of_lt_of_le hu_h hh4_ge_h)
            (Or.inl (lt_of_lt_of_le hu_h hh_restE)) (Or.inl (lt_of_lt_of_le hu_h hh_actRest))
            (fun v hv => by
              have huv : u ≠ v := fun h => (Finset.mem_sdiff.mp hv).2 (h ▸ hu)
              intro heq; exact huv (Nat.add_left_cancel heq))
            (by rcases env.hdLbN with h1 | h1 <;> linarith only [huN, h1])]
      exact hSD_Rlbl u hu
  have hAllLbl : LabelsMatchParts stEnd.mem labelsAddr H.vertSet
      ([R] ++ ((isoRest.map fun v => ({v} : Finset ℕ)) ++ oRest.parts))
      nl₀ (stEnd.mem nextLblAddr) := by
    rw [← Finset.union_sdiff_of_subset hRX]
    exact labelsMatchParts_union disjoint_sdiff_self_right hRLbl_end hoRLbl
  have hSpec := progRecSpec_witness_combine (actRest := actRest) (R := R)
    hRep hRX hRne he1 hRcond hstR.1 hstR.2.1 hstR.2.2.1 hstR.2.2.2.2.1 heRest_in
    (by rw [heRest_act, heRest_eq]; change 16 * DOut cfg M r * _ ≤ (16 * DOut cfg M r - 1) * e; rw [← he_eq]; exact hshR_in)
    (by linarith only [heRest_act, hltR])
    (by change 15 * e ≤ _; rw [← he_eq]; exact h15_ret)
    (by change _ ≤ e; rw [← he_eq]; exact h16_cut) hoRSpec
  have hkRest_eq : (H.restrict (H.vertSet \ R)).verts.length = k - kR := by
    have h1 : (H.restrict (H.vertSet \ R)).verts.toFinset.card + R.card = H.verts.toFinset.card := by
      rw [hrepR.2.1]; exact Finset.card_sdiff_add_card_eq_card hRX
    rw [List.toFinset_card_of_nodup hrepR.1, List.toFinset_card_of_nodup hR_nd,
        List.toFinset_card_of_nodup hRep.1] at h1
    exact Nat.eq_sub_of_add_eq h1
  refine ⟨h5, stEnd, cTot, hrunAll, _, hSpec, hAllLbl, by linarith only [hoRNl, hkRest_lt], le_trans hh4_ge_h hh5_ge,
    by rw [heRest_act] at hh5_le; linarith only [hh5_le, hh4_le_wit, hrfAddr_le, htree_w], hZero5, hloc5, ?_, ?_⟩
  · intro a ha haLb haN
    rw [hCh_fr a (lt_of_lt_of_le ha hh4_ge_h) (Or.inl (lt_of_lt_of_le ha hh_restE))
          (Or.inl (lt_of_lt_of_le ha hh_actRest))
          (fun u hu => haLb u (Finset.sdiff_subset hu)) haN]
    by_cases haL : ∃ u ∈ H.verts, a = locAddr + u
    · rcases haL with ⟨u, hu, rfl⟩
      rw [hSD_loc0 u (hsubV u hu), hloc0 u (hsubV u hu)]
    · push Not at haL
      exact hSD_belowH a ha (fun u hu => haLb u (hRX hu)) haN haL
  · dsimp only
    simp only [portGraphCost, outerGameStepBound] at hc3
    exact recWitness_cost_aux (C_core := C_core) (C_rt := C_rt) (M := M) (r := r) (routeC := routeC)
      (e := e) (k := k) (kR := kR) (mF := mF) (mF' := mF') (eRest := actRest.edges.length)
      (lc := lc)
      he1 hk_le_2e hkR_le hmF_le_e hmF'_le_e (by linarith only [heRest_act, hltR]) hlc_le
      (progRemoveFakeCost_le_trim hk_le_2e hmF'_le_e heM he1 hLam1)
      hc3 hcTot hcRF hcWC hcSD (by rw [← hkRest_eq]; exact hcCh)


end MinCostFlow.ExpanderDecomp
