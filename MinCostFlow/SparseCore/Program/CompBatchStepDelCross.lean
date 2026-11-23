module

public import MinCostFlow.SparseCore.Program.CompBatchStepDelBase
import WordRAM.Tactic

/-!
# Edge-Deletion Step: Cross-Component Branch (`CompBatchStepDelCross`)

Verifies `compStepDelCrossStmt` (cross-component deletion `c1 ≠ c2`). Since cross-inserts are
projected to insert-then-delete self-loops, cross-edges never live in any component graph, so
`compStepDelCrossStmt` is `.nop` (`cost = 1`), leaving all components, cut logs, and touched sets
unchanged.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
  MinCostFlow.DynSpanner.Program

@[expose] public section

set_option maxHeartbeats 800000 in
open Classical in
/-- Verification of `compStepDelCrossStmt` starting from the post-prefix state `stP` when `e` is a
cross-edge (absent from every component graph). -/
lemma compStepDelCross_runs {W : LSFWindowImpl}
    {w k b bErase bMark bDisp uPtr heap cntBase updBuf e : ℕ}
    {p : Program} {S : CompLSFFamily k} {x : CompLSFMeta k}
    {touched : List ℕ} {cnts : Fin k → ℕ} {mem : ℕ → ℕ} {ω : ℕ → Bool}
    (hrep : CompLSFRepDirty W k b S x touched mem)
    (htouch_nd : touched.Nodup)
    (htouch_lt : ∀ c ∈ touched, c < x.numComps)
    (hu_valid : (S ⟨0, hrep.1⟩).G.UpdateIsValid (.delete e))
    (hcr : e ∈ (S ⟨0, hrep.1⟩).crossEdges)
    (hend_heap : x.endAddr ≤ heap)
    (hheap_cnt : heap + 1 + touched.length + 2 ≤ cntBase)
    (hcnt_buf : cntBase + k + 2 * (k * x.vCap) ≤ updBuf)
    (hz : ZeroFrom mem updBuf)
    (hcnt_touch : mem heap = touched.length)
    (hlist_touch : ListAt mem (heap + 1) touched)
    (hcnts_m : ∀ j : Fin k, mem (cntBase + j.1) = cnts j)
    (hcnts_le : ∀ j : Fin k, cnts j ≤ (S j).RF.R.card)
    {stP : State}
    (hstP_r1 : stP.regs 1 = uPtr)
    (hstP_mem : stP.mem = Function.update (Function.update mem
      (compIsCrossBase b x.vCap x.eCap + e) 0) (compIsInsBase b x.vCap x.eCap + e) 0) :
    let cs0 := S ⟨0, hrep.1⟩
    let S' : CompLSFFamily k := fun j => compLSFStepSingle (S j) (.delete e)
    let rootsBase := cntBase + k
    let fDelBase := cntBase + k + k * x.vCap
    ∃ st' cost, ∃ (x' : CompLSFMeta k) (touched' : List ℕ) (cuts : Fin k → List (ℕ × ℕ)),
      Runs w p ω (compStepDelCrossStmt bErase bMark bDisp) stP .normal st' cost ∧
      st'.regs 1 = uPtr ∧
      x'.vCap = x.vCap ∧ x'.eCap = x.eCap ∧ x'.L_w = x.L_w ∧
      x'.numComps = x.numComps ∧ x'.numEdgeful = x.numEdgeful ∧
      x'.m0Total = x.m0Total ∧ x'.endAddr = x.endAddr ∧ HEq x'.compOf x.compOf ∧
      CompLSFRepDirty W k b S' x' touched' st'.mem ∧
      touched'.Nodup ∧ (∀ c ∈ touched', c < x.numComps) ∧
      touched'.length ≤ touched.length + 2 ∧
      (∀ c : Fin x.numComps, c.1 ∈ touched' ↔
        c.1 ∈ touched ∨ x.compOf c ∈ touchedComps cs0 (.delete e)) ∧
      st'.mem heap = touched'.length ∧
      ListAt st'.mem (heap + 1) touched' ∧
      (∀ j : Fin k,
        st'.mem (cntBase + j.1) = cnts j + (cuts j).length ∧
        (∀ i (hi : i < (cuts j).length),
          st'.mem (rootsBase + j.1 * x.vCap + (cnts j + i)) = (cuts j)[i].2 ∧
          st'.mem (fDelBase + j.1 * x.vCap + (cnts j + i)) = (cuts j)[i].1) ∧
        CompForestCutsValid x.vCap (S j).RF (cuts j) ∧
        ((cuts j).map Prod.fst).Nodup ∧
        ((cuts j).map Prod.fst).toFinset = (S j).RF.F.E \ (S' j).RF.F.E ∧
        (S' j).RF.F.E ⊆ (S j).RF.F.E ∧
        ((cuts j).map Prod.snd).Nodup ∧
        ((cuts j).map Prod.snd).toFinset = (S' j).RF.R \ (S j).RF.R ∧
        (S j).RF.R ⊆ (S' j).RF.R ∧
        cnts j + (cuts j).length ≤ (S' j).RF.R.card) ∧
      (∀ a,
        (a < b ∨ x.endAddr ≤ a) →
        a ≠ heap → (a < heap + 1 + touched.length ∨ heap + 1 + touched.length + 2 ≤ a) →
        (∀ j : Fin k, a ≠ cntBase + j.1) →
        (∀ j : Fin k, a < rootsBase + j.1 * x.vCap + cnts j ∨
          rootsBase + j.1 * x.vCap + cnts j + (cuts j).length ≤ a) →
        (∀ j : Fin k, a < fDelBase + j.1 * x.vCap + cnts j ∨
          fDelBase + j.1 * x.vCap + cnts j + (cuts j).length ≤ a) →
        a < updBuf → st'.mem a = mem a) ∧
      ZeroFrom st'.mem updBuf ∧
      cost + 120 * (∑ j : Fin k, (cuts j).length) + compPhi b x' st'.mem ≤
        compPhi b x mem + 480 +
        k * ((touchedComps cs0 (.delete e)).filter fun C =>
              1 ≤ (compGraph cs0.G₀ C).m).sum (fun C =>
          lsfBatchCostFactor * ((1 + projUpdWords mem cs0 C uPtr (.delete e)) * x.L_w + 1) +
          lsfBatchCostFactor * (projUpdWords mem cs0 C uPtr (.delete e) * x.L_w)) := by
  intro cs0 S' rootsBase fDelBase
  obtain ⟨hk, hhW, hLinW, hPfpW, hLw, hhLw, heCap1, hnumC, hnumEf, hTE, hhdr, ⟨ℓ₀, hBr⟩,
    hm0Tot, hT, hCompMeta, hEfMeta, hVComp, hEdgeC, hFlags, hGhost, hTM, hOne, hWins, hDisj⟩ := hrep
  have hI0 : CompLSFInv W.C_lsst ℓ₀ cs0 := (hBr ⟨0, hk⟩).1
  have hS_G : ∀ j : Fin k, (S j).G = cs0.G := fun j => (hBr j).2.2.1
  have heCap : e < x.eCap := hT.hElt e hu_valid
  have he_not_comp : ∀ j : Fin k, ∀ C ∈ components (S j).G₀, e ∉ ((S j).compSt C).G.E := by
    intro j C hC heC
    have hcrj : e ∈ (S j).crossEdges := (hBr j).2.2.2.2.1.symm ▸ hcr
    exact (hBr j).1.hCompE_notCross C hC e heC hcrj
  have hcomp_eq : ∀ j : Fin k, ∀ C ∈ components (S j).G₀,
      (S' j).compSt C = (S j).compSt C := by
    intro j C hC
    change applyLSFBatch ((S j).compSt C) (projCompUpdateG (S j).G ((S j).compSt C).G (.delete e)) = _
    rw [projCompUpdateG, ite_eq_right (he_not_comp j C hC)]; rfl
  have htouch_none : ∀ c : Fin x.numComps, x.compOf c ∉ touchedComps cs0 (.delete e) := by
    intro c hmem
    have hne := (Finset.mem_filter.mp hmem).2
    have henot := he_not_comp ⟨0, hk⟩ (x.compOf c) (hT.compOf_mem c)
    simp [projCompUpdateG] at hne
    exact henot hne
  have hmP_fr : ∀ z, z ≠ compIsCrossBase b x.vCap x.eCap + e → z ≠ compIsInsBase b x.vCap x.eCap + e →
      stP.mem z = mem z := fun z h1 h2 => by
    rw [hstP_mem, Function.update_of_ne h2, Function.update_of_ne h1]
  have hmP_lt_cr : ∀ z < compIsCrossBase b x.vCap x.eCap, stP.mem z = mem z := fun z hz' =>
    hmP_fr z (by omega) (by dsimp only [compIsInsBase]; omega)
  have hmP_ge_g : ∀ z, compGhostBase b x.vCap x.eCap ≤ z → stP.mem z = mem z := fun z hz' =>
    hmP_fr z (by dsimp only [compGhostBase, compIsInsBase] at hz'; omega)
      (by dsimp only [compGhostBase] at hz'; omega)
  have hge_g_end : compGhostBase b x.vCap x.eCap ≤ x.endAddr := by
    have : compGhostBase b x.vCap x.eCap ≤ compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
      dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compGhostBase, compIsInsBase,
        compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase,
        compEdgefulBase, compVCompBase, compHdrSize]; omega
    omega
  have hBr' : ∀ j : Fin k,
      CompLSFInv W.C_lsst ℓ₀ (S' j) ∧ (S' j).G₀ = (S' ⟨0, hk⟩).G₀ ∧
      (S' j).G = (S' ⟨0, hk⟩).G ∧ (S' j).k = k ∧
      (S' j).crossEdges = (S' ⟨0, hk⟩).crossEdges ∧
      (S' j).insertedGlobal = (S' ⟨0, hk⟩).insertedGlobal ∧
      (∀ c : Fin x.numComps, ((S' j).compSt (x.compOf c)).G = ((S' ⟨0, hk⟩).compSt (x.compOf c)).G) := by
    intro j
    have hIj := (hBr j).1; have hu_j := (hS_G j).symm ▸ hu_valid; have hG0j := (hBr j).2.1
    refine ⟨compLSFInv_step hIj hu_j, hG0j, by simp [S', compLSFStepSingle, hS_G j, cs0],
      (hBr j).2.2.2.1, by simp [S', compLSFStepSingle, (hBr j).2.2.2.2.1],
      by simp [S', compLSFStepSingle, (hBr j).2.2.2.2.2.1], fun c => ?_⟩
    rw [hcomp_eq j _ (hG0j.symm ▸ hT.compOf_mem c), hcomp_eq ⟨0, hk⟩ _ (hT.compOf_mem c)]
    exact (hBr j).2.2.2.2.2.2 c
  have hT' := compEdgeTrack_step_delete hI0 hT hu_valid
  have hrep' : CompLSFRepDirty W k b S' x touched stP.mem := by
    refine ⟨hk, hhW, hLinW, hPfpW, hLw, hhLw, heCap1, hnumC, hnumEf, hTE,
      compHeaderAt_of_agree hhdr (fun z _ hz2 => hmP_lt_cr z (by
        dsimp only [compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base,
          compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize] at hz2 ⊢; omega)),
      ⟨ℓ₀, hBr'⟩, hm0Tot, hT', ?_, hEfMeta, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hDisj⟩
    · intro c; have hc_lt : c.1 < x.numComps := c.2; obtain ⟨h1, h2, h3, h4⟩ := hCompMeta c
      refine ⟨(hmP_lt_cr _ (by dsimp only [compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase]; omega)).trans h1,
        (hmP_lt_cr _ (by dsimp only [compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base]; omega)).trans h2,
        (hmP_lt_cr _ (by dsimp only [compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base]; omega)).trans h3,
        fun hpos => ?_⟩
      obtain ⟨ec, he1, he2, he3⟩ := h4 hpos
      exact ⟨ec, he1, (hmP_lt_cr _ (by dsimp only [compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase]; omega)).trans he2, he3⟩
    · intro c v hv
      rw [hcomp_eq ⟨0, hk⟩ _ (hT.compOf_mem c)] at hv
      have hv_lt : v < x.vCap := hT.hVlt v (hI0.hV_eq ▸ Finset.mem_biUnion.mpr ⟨x.compOf c, hT.compOf_mem c, hv⟩)
      exact (hmP_lt_cr _ (by dsimp only [compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase]; omega)).trans (hVComp c v hv)
    · intro f hf
      have hf0 : f ∈ cs0.G.E := Finset.erase_subset _ _ hf
      have hf_lt : f < x.eCap := hT.hElt f hf0
      exact ⟨(hmP_lt_cr _ (by dsimp only [compIsCrossBase, compEdgeC2Base]; omega)).trans (hEdgeC f hf0).1,
        (hmP_lt_cr _ (by dsimp only [compIsCrossBase]; omega)).trans (hEdgeC f hf0).2⟩
    · intro f hf
      change stP.mem (compIsCrossBase b x.vCap x.eCap + f) = (if f ∈ cs0.crossEdges.erase e then 1 else 0) ∧
        stP.mem (compIsInsBase b x.vCap x.eCap + f) = (if f ∈ cs0.insertedGlobal.erase e then 1 else 0)
      by_cases hfe : f = e
      · subst hfe; simp only [Finset.notMem_erase, ↓reduceIte, hstP_mem]
        exact ⟨by rw [Function.update_of_ne (by dsimp only [compIsInsBase]; omega), Function.update_self],
          Function.update_self _ _ _⟩
      · rw [hmP_fr _ (by omega) (by dsimp only [compIsInsBase]; omega),
            hmP_fr _ (by dsimp only [compIsInsBase]; omega) (by omega)]
        simp [hfe, (hFlags f hf).1, (hFlags f hf).2, cs0]
    · set gPtr := compGhostBase b x.vCap x.eCap
      refine ⟨fun v hv => ?_, fun f hf hcrf => ?_⟩
      · obtain ⟨h1, h2, h3, h4⟩ := hGhost.1 v hv
        exact ⟨h1.of_agree (hmP_ge_g _ (by dsimp only [ghostTHeadBase]; omega))
            (fun f _ => hmP_ge_g _ (by dsimp only [ghostTPrevBase]; omega))
            (fun f _ => hmP_ge_g _ (by dsimp only [ghostTNextBase]; omega)),
          (hmP_ge_g _ (by dsimp only [ghostTCntBase]; omega)).trans h2,
          h3.of_agree (hmP_ge_g _ (by dsimp only [ghostHHeadBase]; omega))
            (fun f _ => hmP_ge_g _ (by dsimp only [ghostHPrevBase]; omega))
            (fun f _ => hmP_ge_g _ (by dsimp only [ghostHNextBase]; omega)),
          (hmP_ge_g _ (by dsimp only [ghostHCntBase]; omega)).trans h4⟩
      · have hf0 : f ∈ cs0.G.E := Finset.erase_subset _ _ hf
        have hcr0 : f ∈ cs0.crossEdges := Finset.erase_subset _ _ hcrf
        exact ⟨(hmP_ge_g _ (by dsimp only [ghostTVertBase]; omega)).trans (hGhost.2 f hf0 hcr0).1,
          (hmP_ge_g _ (by dsimp only [ghostHVertBase]; omega)).trans (hGhost.2 f hf0 hcr0).2⟩
    · intro c hc
      exact (hmP_ge_g _ (by dsimp only [compTouchMarkBase, compGhostSize]; omega)).trans (hTM c hc)
    · exact ⟨(hmP_ge_g _ (by dsimp only [compOneLimbBase, compTouchMarkBase, compGhostSize]; omega)).trans hOne.1,
        fun i h1 h2 => (hmP_ge_g _ (by dsimp only [compOneLimbBase, compTouchMarkBase, compGhostSize]; omega)).trans (hOne.2 i h1 h2)⟩
    · intro ec j
      obtain ⟨hslot, hrep_ec, hv, he, hL, hge, hle⟩ := hWins ec j
      have hge_g_win : compGhostBase b x.vCap x.eCap ≤ x.winHandle ec j := by
        have : compGhostBase b x.vCap x.eCap ≤ compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
          dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compGhostBase, compIsInsBase,
            compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase,
            compEdgefulBase, compVCompBase, compHdrSize]; omega
        omega
      refine ⟨(hmP_ge_g _ (by dsimp only [compHandlesBase, compStaticSize, compGhostBase, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega)).trans hslot,
        ?_, hv, he, hL, hge, hle⟩
      rw [hcomp_eq j _ ((hBr j).2.1.symm ▸ hT.compOf_mem (x.edgefulComp ec))]
      exact (lsfRep_local W.h _ _ _ mem stP.mem fun z hz => (hmP_ge_g z (le_trans hge_g_win hz.1)).symm).1 hrep_ec
  have hphi_eq : compPhi b x stP.mem = compPhi b x mem := by
    rw [compPhi_eq_sum_dirty hrep', compPhi_eq_sum_dirty ⟨hk, hhW, hLinW, hPfpW, hLw, hhLw, heCap1,
      hnumC, hnumEf, hTE, hhdr, ⟨ℓ₀, hBr⟩, hm0Tot, hT, hCompMeta, hEfMeta, hVComp, hEdgeC, hFlags,
      hGhost, hTM, hOne, hWins, hDisj⟩]
    refine Finset.sum_congr rfl fun ec _ => Finset.sum_congr rfl fun j _ => ?_
    obtain ⟨_, _, _, _, _, hge, _⟩ := hWins ec j
    have hge_g_win : compGhostBase b x.vCap x.eCap ≤ x.winHandle ec j := by
      have : compGhostBase b x.vCap x.eCap ≤ compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
        dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compGhostBase, compIsInsBase,
          compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase,
          compEdgefulBase, compVCompBase, compHdrSize]; omega
      omega
    exact lsfPhi_congr fun z hz1 _ => hmP_ge_g z (le_trans hge_g_win hz1)
  have hRF_E_eq : ∀ j : Fin k, (S' j).RF.F.E = (S j).RF.F.E := fun j => by
    change ((components (S' j).G₀).biUnion fun C => ((S' j).compSt C).RF.F.E) =
      ((components (S j).G₀).biUnion fun C => ((S j).compSt C).RF.F.E)
    exact Finset.biUnion_congr rfl fun C hC => by rw [hcomp_eq j C hC]
  have hRF_R_eq : ∀ j : Fin k, (S' j).RF.R = (S j).RF.R := fun j => by
    change ((components (S' j).G₀).biUnion fun C => ((S' j).compSt C).RF.R) =
      ((components (S j).G₀).biUnion fun C => ((S j).compSt C).RF.R)
    exact Finset.biUnion_congr rfl fun C hC => by rw [hcomp_eq j C hC]
  refine ⟨stP, 1, x, touched, fun _ => [], runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩,
    hstP_r1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, HEq.rfl, hrep',
    htouch_nd, htouch_lt, by omega,
    fun c => ⟨Or.inl, fun h => h.elim id (fun hc => absurd hc (htouch_none c))⟩,
    (hmP_ge_g heap (by omega)).trans hcnt_touch,
    fun i hi => (hmP_ge_g (heap + 1 + i) (by omega)).trans (hlist_touch i hi),
    fun j => ⟨by simpa using (hmP_ge_g (cntBase + j.1) (by omega)).trans (hcnts_m j),
      fun _ hi => by simp at hi, trivial, List.nodup_nil, by rw [hRF_E_eq j]; simp,
      by rw [hRF_E_eq j], List.nodup_nil, by rw [hRF_R_eq j]; simp, by rw [hRF_R_eq j],
      by rw [hRF_R_eq j]; simpa using hcnts_le j⟩,
    fun z hout _ _ _ _ _ _ => by
      rcases hout with hlt | hge'
      · exact hmP_lt_cr z (by dsimp only [compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega)
      · exact hmP_ge_g z (by omega),
    fun z hz' => (hmP_ge_g z (by omega)).trans (hz z hz'),
    by rw [hphi_eq]; simp; omega⟩

end

end MinCostFlow.SparseCore.Program
