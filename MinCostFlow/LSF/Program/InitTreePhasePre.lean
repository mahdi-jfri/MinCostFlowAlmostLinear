module

public import MinCostFlow.LSF.Program.InitTreePre
public import MinCostFlow.LSF.Program.InitTreeLSSTLift

/-!
# The pre of the whole tree phase in the init driver

`treePhase_pre_of` gives the pre of `treePhaseContract` at the places of `InitPlaces.lean`. The
copies part is `treeCopies_pre_of`. For the `[AN19]` part, the number `M` of copies is at most
`2 m₀`, so the arrays sized for `2 m₀` copies hold them (`treeLsst_layout`), and the limb count
computed for `2 m₀` edges is large enough for `M` edges (`lsstLSimMin_mono_m`).
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.WideWord

@[expose] public section

/-- The `26` arguments of the tree phase, at the places of the driver. -/
def treeArgsV (V : InitVals) (lenArr wtArr : ℕ) : List ℕ :=
  treeCopyArgsV V lenArr wtArr ++ [V.outOrig, V.outBridge, V.outHdr, V.tOrig, V.tTail, V.tHead]

lemma treePhaseCopyArgs_treeArgsV (V : InitVals) (lenArr wtArr : ℕ) :
    treePhaseCopyArgs (treeArgsV V lenArr wtArr) = treeCopyArgsV V lenArr wtArr := rfl

lemma treePhaseLsstArgs_treeArgsV (V : InitVals) (lenArr wtArr M L_sim : ℕ) :
    treePhaseLsstArgs (treeArgsV V lenArr wtArr) M L_sim =
      [V.n0, M, V.copyTail, V.copyHead, V.copyLen, V.copyWt, V.L_in, L_sim, V.outOrig,
        V.outBridge, V.outHdr, V.lsstHeap, V.copyOrig, V.usedBridge, 2 * V.m0 + V.n0, V.eCap,
        V.tOrig, V.tTail, V.tHead] := rfl

/-- The arrays of the `[AN19]` stage, for `M ≤ 2 m₀` copies. -/
lemma treeLsst_layout (V : InitVals) {M : ℕ} (hM : M ≤ 2 * V.m0) :
    V.copyTail + M ≤ V.copyHead ∧ V.copyHead + M ≤ V.copyLen ∧
    V.copyLen + M * V.L_in ≤ V.copyWt ∧ V.copyWt + M * V.L_in ≤ V.copyOrig ∧
    V.copyOrig + M ≤ V.outOrig ∧ V.outOrig + V.n0 ≤ V.outBridge ∧
    V.outBridge + 2 * V.n0 ≤ V.outHdr ∧ V.outHdr + 2 ≤ V.usedBridge ∧
    V.usedBridge + (2 * V.m0 + V.n0) ≤ V.tOrig ∧ V.tOrig + V.n0 ≤ V.tTail ∧
    V.tTail + V.n0 ≤ V.tHead ∧ V.tHead + V.n0 ≤ V.lsstHeap := by
  obtain ⟨-, -, -, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, -⟩ :=
    V.scratch_order
  have hML : M * V.L_in ≤ 2 * V.m0 * V.L_in := Nat.mul_le_mul_right _ hM
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem treePhase_pre_of {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ} {w h : ℕ} {G₀ : MGraph}
    {v ℓ₀ : ℕ → ℝ} {P_fp : ℕ} {vList eList : List ℕ} (V : InitVals) {lenArr wtArr : ℕ}
    {mem : ℕ → ℕ}
    (hh : 1 ≤ h) (hhw : 3 * h + 2 ≤ w) (hLin : 1 ≤ V.L_in) (h2L : 2 ≤ h * V.L_in)
    (hPd : h ∣ P_fp) (hG : G₀.IsValid) (hm : G₀.E.card = V.m0)
    (hn : G₀.n = V.n0) (hn1 : 1 ≤ V.n0) (hK : V.K_w = kWidthOf V.m0 V.L_in)
    (hdg : DynGraphAt mem V.gPtr V.vCap V.eCap G₀)
    (heLen : eList.length = V.m0) (heNd : eList.Nodup) (heE : ∀ e, e ∈ eList ↔ e ∈ G₀.E)
    (heL : ListAt mem (dgEListBase V.gPtr V.vCap V.eCap) eList)
    (hvLen : vList.length = V.n0) (hvNd : vList.Nodup) (hvV : ∀ u, u ∈ vList ↔ u ∈ G₀.V)
    (hvI : ∀ i (hi : i < vList.length), mem (V.vIdx + vList[i]) = i + 1)
    (hlenB : ∀ e ∈ G₀.E, lenArr + e * V.L_in + V.L_in ≤ V.b)
    (hwtB : ∀ e ∈ G₀.E, wtArr + e * V.L_in + V.L_in ≤ V.b)
    (hlv : ∀ e ∈ G₀.E, Num.Valid mem (lenArr + e * V.L_in) h V.L_in ∧
      Num.fixVal mem (lenArr + e * V.L_in) h V.L_in P_fp = ℓ₀ e ∧ 0 < ℓ₀ e)
    (hwv : ∀ e ∈ G₀.E, Num.Valid mem (wtArr + e * V.L_in) h V.L_in ∧
      Num.fixVal mem (wtArr + e * V.L_in) h V.L_in P_fp = v e ∧ 0 < v e)
    (hz : ZeroFrom mem V.lsstHeap)
    (hsp : V.lsstHeap + V.m0 * multQNatStepSpace V.K_w < 2 ^ w)
    (hec : V.eCap + (2 * V.m0 + V.n0) + V.eCap < 2 ^ w)
    (hc : 1 ≤ c_AN) (hl1 : 16 * (2 * V.m0) + 6 < 2 ^ w) (hl2 : 16 < 2 ^ w) (hl3 : c_AN < 2 ^ w)
    (hl4 : h < 2 ^ w) (hl5 : kWidthOf (2 * V.m0) V.L_in < 2 ^ w)
    (hl6 : Nat.log 2 (16 * (2 * V.m0) + 6) + kWidthOf (2 * V.m0) V.L_in * h + 3 < 2 ^ w)
    (hl7 : w'Max c_AN 0 (2 * V.m0) V.L_in h < 2 ^ w)
    (hspL : V.lsstHeap + lsstSpace Q_AN K_AN V.n0 (2 * V.m0)
      (lsstLSimMin c_AN 0 (2 * V.m0) V.L_in h) h < 2 ^ w) :
    (treePhaseContract Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp vList eList).pre
      (treeArgsV V lenArr wtArr) mem := by
  have hpre := treeCopies_pre_of (ℓ₀ := ℓ₀) (v := v) (P_fp := P_fp) V hh hhw hLin h2L hPd hG hm
    hn hK hdg heLen heNd heE heL hvLen hvNd hvV hvI hlenB hwtB hlv hwv hz hsp hec
  refine ⟨rfl, hpre, ⟨2 * V.m0, V.L_in, rfl, hl1, hl2, hl3, hl4, hl5, hl6, hl7⟩,
    show 2 * V.m0 + V.n0 < 2 ^ w by omega, ?_⟩
  intro mem₁ hpost
  rw [treePhaseCopyArgs_treeArgsV] at hpost
  obtain ⟨g0Ptr', eListPtr', lenArr', wtArr', L_in', m0', K_w', qNatPtr', lsstHeap', vIdxBase',
    n0', eCap', multPtr', copyTailPtr', copyHeadPtr', copyLenPtr', copyWtPtr', copyOrigIdxPtr',
    copySubIdxPtr', usedBridgePtr', heq, -, hMle, -, hTl, hHd, hCA, hLen, hWt, hmark, hz₁,
    -⟩ := hpost
  simp only [treeCopyArgsV, List.cons.injEq, and_true] at heq
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl⟩ := heq
  rw [treePhaseLsstArgs_treeArgsV]
  have hM : treePhaseM G₀ v vList eList ≤ 2 * V.m0 := hMle
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩ := treeLsst_layout V hM
  have hLs1 : 1 ≤ lsstLSimMin c_AN 0 (2 * V.m0) V.L_in h :=
    le_trans (by unfold kWidthOf; omega) (le_max_left _ _)
  have hspM := lsstSpace_mono_m (Q_AN := Q_AN) (K_AN := K_AN) (n := V.n0) hLs1 hh hM
  have hne : G₀.V.Nonempty :=
    ⟨vList[0]'(by omega), (hvV _).mp (List.getElem_mem _)⟩
  refine ⟨V.n0, treePhaseM G₀ v vList eList, V.copyTail, V.copyHead, V.copyLen, V.copyWt, V.L_in,
    lsstLSimMin c_AN 0 (2 * V.m0) V.L_in h, V.outOrig, V.outBridge, V.outHdr, V.lsstHeap,
    V.copyOrig, V.usedBridge, 2 * V.m0 + V.n0, V.eCap, V.tOrig, V.tTail, V.tHead, rfl, hc, hh,
    hhw, hLin, hG, hne, fun e he => (hlv e he).2.2, fun e he => (hwv e he).2.2,
    hvLen.trans hn.symm, hvNd, hvV, heLen.trans hm.symm, heNd, heE, hdg.2.2.1, hn.symm, rfl,
    by rw [hm, hn], lsstLSimMin_mono_m (n := G₀.n) hM, hTl, hHd, hCA, hLen, hWt,
    fun z hz' => by rw [hm]; exact hmark z hz', l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11,
    l12, by omega, hz₁, by omega⟩

end

end MinCostFlow.LSF.Program
