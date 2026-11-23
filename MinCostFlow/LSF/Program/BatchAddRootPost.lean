module

public import MinCostFlow.LSF.Program.BatchAddRootBase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Post-Pop `LSFRep` and Potential Assembly (`BatchAddRootPost`)

Proves `addOrigRootPopStep_post`, assembling the updated `(LSFRep h).rep`, `SameStaticConcrete`,
frame preservation, and amortized potential bound after cutting one `π`-minimum edge and
relabeling the split component.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

open Classical in
/-- Post-BFS state preservation and potential-drop step for one iteration of `addOrigRootPopStepStmt`:
combines `fancAt_after_splitCompBFS`, frame preservation for all LSF sub-blocks and `thStack`,
and `phi_drop_addRoot_cut`. -/
lemma addOrigRootPopStep_post {w b zIdx oldCid rC oldSize cutE a b' : ℕ}
    {S : LSFState} {x : LSFConcrete} {rest : List ℕ} {mem0 mem1 mem2 mem3 : ℕ → ℕ}
    (hend_ltw : x.endAddr b < 2 ^ w)
    (hrep : (LSFRep x.h).rep b S x mem0)
    (hzIdx_lt : zIdx < x.n0)
    (hz_not : x.vList[zIdx]! ∉ S.R_orig)
    (hold_eq : mem0 (fCompIdBase (lsfFAncPtr b x.vCap x.eCap x.n0 x.tM) x.vCap + x.vList[zIdx]!) = oldCid)
    (_hold_eq' : oldCid = x.compId (x.vList[zIdx]!))
    (hold_act : oldCid ∈ x.activeCids)
    (hrC_eq : rC = x.compRoot oldCid)
    (holdSz_eq : oldSize = x.compSize oldCid)
    (hconn_zrC : S.RF.F.Connected (x.vList[zIdx]!) rC)
    (hRorig' : ({ S with R₀_base := insert (x.vList[zIdx]!) S.R₀_base } : LSFState).R_orig =
      insert (x.vList[zIdx]!) S.R_orig)
    (hz_not_R : x.vList[zIdx]! ∉ S.R)
    (hR' : ({ S with R₀_base := insert (x.vList[zIdx]!) S.R₀_base } : LSFState).R =
      insert (x.vList[zIdx]!) S.R)
    (hInv' : LSFStructInv { S with R₀_base := insert (x.vList[zIdx]!) S.R₀_base })
    (hcut_mem : cutE ∈ S.RF.F.E)
    (hF'_eq : ({ S with R₀_base := insert (x.vList[zIdx]!) S.R₀_base } : LSFState).RF.F =
      S.RF.F.applyUpdate (.delete cutE))
    (_ha_eq : a = S.RF.F.tail cutE) (_hb'_eq : b' = S.RF.F.head cutE)
    (haV : a ∈ ({ S with R₀_base := insert (x.vList[zIdx]!) S.R₀_base } : LSFState).RF.F.V)
    (hbV : b' ∈ ({ S with R₀_base := insert (x.vList[zIdx]!) S.R₀_base } : LSFState).RF.F.V)
    (hnot_ab : ¬ ({ S with R₀_base := insert (x.vList[zIdx]!) S.R₀_base } : LSFState).RF.F.Connected a b')
    (hpart_V : ∀ v ∈ ({ S with R₀_base := insert (x.vList[zIdx]!) S.R₀_base } : LSFState).RF.F.V,
      (({ S with R₀_base := insert (x.vList[zIdx]!) S.R₀_base } : LSFState).RF.F.Connected v a ∨
        ({ S with R₀_base := insert (x.vList[zIdx]!) S.R₀_base } : LSFState).RF.F.Connected v b') ↔
      (v = x.vList[zIdx]! ∨ (v ∈ S.RF.F.V ∧ S.RF.F.Connected v rC)))
    (hother_conn : ∀ v ∈ ({ S with R₀_base := insert (x.vList[zIdx]!) S.R₀_base } : LSFState).RF.F.V,
      ¬ ({ S with R₀_base := insert (x.vList[zIdx]!) S.R₀_base } : LSFState).RF.F.Connected v a →
      ¬ ({ S with R₀_base := insert (x.vList[zIdx]!) S.R₀_base } : LSFState).RF.F.Connected v b' →
      v ∈ S.RF.F.V ∧ ∀ w ∈ S.RF.F.V,
        (({ S with R₀_base := insert (x.vList[zIdx]!) S.R₀_base } : LSFState).RF.F.Connected v w ↔
          S.RF.F.Connected v w))
    (hother_disj : ∀ v ∈ ({ S with R₀_base := insert (x.vList[zIdx]!) S.R₀_base } : LSFState).RF.F.V,
      ∀ w ∈ ({ S with R₀_base := insert (x.vList[zIdx]!) S.R₀_base } : LSFState).RF.F.V,
      (({ S with R₀_base := insert (x.vList[zIdx]!) S.R₀_base } : LSFState).RF.F.Connected v a ∨
        ({ S with R₀_base := insert (x.vList[zIdx]!) S.R₀_base } : LSFState).RF.F.Connected v b') →
      ¬ ({ S with R₀_base := insert (x.vList[zIdx]!) S.R₀_base } : LSFState).RF.F.Connected w a →
      ¬ ({ S with R₀_base := insert (x.vList[zIdx]!) S.R₀_base } : LSFState).RF.F.Connected w b' →
      ¬ ({ S with R₀_base := insert (x.vList[zIdx]!) S.R₀_base } : LSFState).RF.F.Connected v w)
    (hroots_sep :
      (({ S with R₀_base := insert (x.vList[zIdx]!) S.R₀_base } : LSFState).RF.F.Connected rC a ∧
        ({ S with R₀_base := insert (x.vList[zIdx]!) S.R₀_base } : LSFState).RF.F.Connected (x.vList[zIdx]!) b') ∨
      (({ S with R₀_base := insert (x.vList[zIdx]!) S.R₀_base } : LSFState).RF.F.Connected rC b' ∧
        ({ S with R₀_base := insert (x.vList[zIdx]!) S.R₀_base } : LSFState).RF.F.Connected (x.vList[zIdx]!) a))
    (hstk_rest : StackMemAt mem0 (auxThStackBase (lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w) x.vCap x.n0) rest)
    (hdgF1 : DynGraphAt mem1 (lsfDgFPtr b x.vCap x.eCap x.tM) x.vCap (fECap x.eCap x.n0)
      ({ S with R₀_base := insert (x.vList[zIdx]!) S.R₀_base } : LSFState).RF.F)
    (hfr1 : ∀ addr, addr < lsfDgFPtr b x.vCap x.eCap x.tM ∨
      lsfDgFPtr b x.vCap x.eCap x.tM + dynGraphSize x.vCap (fECap x.eCap x.n0) ≤ addr → mem1 addr = mem0 addr)
    (hmem2_def : mem2 = Function.update
      (Function.update
        (Function.update
          (Function.update mem1 (fIsRootBase (lsfFAncPtr b x.vCap x.eCap x.n0 x.tM) + x.vList[zIdx]!) 1)
          (fRListBase (lsfFAncPtr b x.vCap x.eCap x.n0 x.tM) x.vCap + S.RF.R.card) (x.vList[zIdx]!))
        (lsfFAncPtr b x.vCap x.eCap x.n0 x.tM + fOffRCount) (S.RF.R.card + 1))
      (b + lsfOffRCount) (S.RF.R.card + 1))
    (hnewSum_eq : oldSize =
      (({ S with R₀_base := insert (x.vList[zIdx]!) S.R₀_base } : LSFState).RF.F.V.filter
        fun v => ({ S with R₀_base := insert (x.vList[zIdx]!) S.R₀_base } : LSFState).RF.F.Connected v a).card +
      (({ S with R₀_base := insert (x.vList[zIdx]!) S.R₀_base } : LSFState).RF.F.V.filter
        fun v => ({ S with R₀_base := insert (x.vList[zIdx]!) S.R₀_base } : LSFState).RF.F.Connected v b').card)
    (hpost_bfs : (splitCompBFSContract w
        ({ S with R₀_base := insert (x.vList[zIdx]!) S.R₀_base } : LSFState).RF.F).post
      [lsfDgFPtr b x.vCap x.eCap x.tM, lsfFAncPtr b x.vCap x.eCap x.n0 x.tM,
       lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w, x.vCap, fECap x.eCap x.n0, x.n0,
       a, b', oldCid, rC, x.vList[zIdx]!, oldSize] mem2 0 mem3) :
    let z := x.vList[zIdx]!
    let S' : LSFState := { S with R₀_base := insert z S.R₀_base }
    let mSmall := min (S'.RF.F.E.filter fun e => S'.RF.F.Connected (S'.RF.F.tail e) a).card
                      (S'.RF.F.E.filter fun e => S'.RF.F.Connected (S'.RF.F.tail e) b').card
    ∃ x',
      SameStaticConcrete x x' ∧
      (LSFRep x.h).rep b S' x' mem3 ∧
      (∀ a_addr, a_addr < b ∨ x.endAddr b ≤ a_addr → mem3 a_addr = mem0 a_addr) ∧
      StackMemAt mem3 (auxThStackBase (lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w) x.vCap x.n0) rest ∧
      lsfPhi b x' mem3 + 500 * auxLogCap x.n0 + 1400 + 1100 * mSmall ≤ lsfPhi b x mem0 := by
  intro z S' mSmall
  set vCap := x.vCap; set eCap := x.eCap; set n0 := x.n0; set tM := x.tM; set L_w := x.L_w
  set eCapF := fECap eCap n0
  set dgFPtr := lsfDgFPtr b vCap eCap tM
  set fAncPtr := lsfFAncPtr b vCap eCap n0 tM
  set auxPtr := lsfAuxPtr b vCap eCap n0 tM L_w
  set thStackBase := auxThStackBase auxPtr vCap n0
  have hlay := addRoot_layout hend_ltw
  have h_b_dgF : b + lsfHdrSize ≤ dgFPtr := by dsimp only [dgFPtr, vCap, eCap, tM]; omega
  have h_dgF_fAnc : dgFPtr + dynGraphSize vCap eCapF ≤ fAncPtr := by
    dsimp only [dgFPtr, fAncPtr, eCapF, vCap, eCap, n0, tM]; omega
  have h_fAnc_aux : fAncPtr + fAncSize vCap ≤ auxPtr := by
    dsimp only [fAncPtr, auxPtr, vCap, eCap, n0, tM, L_w]; omega
  have h_aux_end : auxPtr + auxSize vCap n0 ≤ x.endAddr b := by
    dsimp only [auxPtr, vCap, eCap, n0, tM, L_w]; omega
  have h_b_fAnc : b + lsfHdrSize ≤ fAncPtr := by clear * - h_b_dgF h_dgF_fAnc; omega
  have h_fAnc_end : fCompSizeBase fAncPtr vCap + vCap = fAncPtr + fAncSize vCap :=
    fAnc_end_eq fAncPtr vCap
  have h_qB_aux : auxQBufBBase auxPtr vCap n0 + vCap ≤ auxPtr + auxSize vCap n0 := by
    clear * - vCap; dsimp [auxQBufBBase, auxQBufABase, auxIsOrigVertBase, auxOrigVertBase, auxThParentBase,
      auxUpMinIdxBase, auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase,
      auxVListBase, auxVIdxBase, auxSize]; omega
  have h_aux_qA : auxPtr ≤ auxQBufABase auxPtr vCap n0 := by
    clear * - vCap; dsimp [auxQBufABase, auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase,
      auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase,
      auxVIdxBase]; omega
  have hrep_orig := hrep
  rcases hrep with ⟨hxH, hh1, hLin, hLw, hkn, hkeq, hInv, hn0, hm0, htM, hnv, hme, htn, hn1,
    hvT_lt, heG_lt, hhdr, hdgG, hT, hdgF, hFAnc, hW, hwstr, hAux⟩
  have hFAnc_copy := hFAnc
  have hAux_copy := hAux
  rcases hAux with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hvLen, _, hvMem, _⟩
  rcases hFAnc with ⟨_, hIsR_ptr, hRL_ptr, hCid_ptr, hCR_ptr, hCS_ptr,
    _, hrL_len, _, _, _, _, _, _, hact_spec, hcid_mem⟩
  have hz_get : x.vList[zIdx]'(by omega) = z := (getElem!_pos x.vList zIdx (by omega)).symm
  have hzT : z ∈ S.T₀.V := hz_get ▸ (hvMem _).mp (List.getElem_mem _)
  have hz_vCap : z < vCap := hvT_lt z hzT
  have hz_F : z ∈ S.RF.F.V := hInv.RF_V_eq ▸ hInv.hGV_eq ▸ Finset.mem_union_left _ hzT
  obtain ⟨_, _, hrC_R, hcid_rC, _, _, _⟩ := hact_spec oldCid hold_act
  rw [← hrC_eq] at hrC_R hcid_rC
  have hrC_F : rC ∈ S.RF.F.V := hInv.RF_V_eq ▸ hInv.to_RF_spanning.2.2.1 hrC_R
  have hrCnt_lt : S.RF.R.card < vCap := by
    have hsub : insert z S.RF.R ⊆ Finset.range vCap := fun v hv => by
      rw [Finset.mem_insert] at hv
      rcases hv with rfl | hvR
      · exact Finset.mem_range.mpr hz_vCap
      · exact Finset.mem_range.mpr (hdgF.2.1 v (hInv.RF_V_eq ▸ hInv.to_RF_spanning.2.2.1 hvR))
    have hc := (Finset.card_le_card hsub).trans_eq (Finset.card_range vCap)
    have hz_not_RF : z ∉ S.RF.R := hz_not_R
    rw [Finset.card_insert_of_notMem hz_not_RF] at hc; omega
  have hmem1_fAnc : ∀ a_addr, fAncPtr ≤ a_addr → mem1 a_addr = mem0 a_addr :=
    fun a_addr ha => hfr1 a_addr (Or.inr (by clear * - h_dgF_fAnc ha; omega))
  have hmem2_eq : ∀ a_addr,
      a_addr ≠ b + lsfOffRCount → a_addr ≠ fAncPtr + fOffRCount →
      a_addr ≠ fRListBase fAncPtr vCap + S.RF.R.card → a_addr ≠ fIsRootBase fAncPtr + z →
      mem2 a_addr = mem1 a_addr := fun a_addr h1 h2 h3 h4 => by
    rw [hmem2_def]
    rw [Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h3, Function.update_of_ne h4]
  have hdgF2 : DynGraphAt mem2 dgFPtr vCap eCapF S'.RF.F :=
    hdgF1.of_agree fun a_addr ha1 ha2 => hmem2_eq a_addr
      (by clear * - h_b_dgF ha1; dsimp [lsfOffRCount, lsfHdrSize] at h_b_dgF ⊢; omega)
      (by clear * - h_dgF_fAnc ha2; dsimp [fOffRCount]; omega)
      (by clear * - h_dgF_fAnc ha2; dsimp [fRListBase, fIsRootBase]; omega)
      (by clear * - h_dgF_fAnc ha2; dsimp [fIsRootBase]; omega)
  have hmem2_ge_cid : ∀ a_addr, fCompIdBase fAncPtr vCap ≤ a_addr → mem2 a_addr = mem0 a_addr :=
    fun a_addr ha => (hmem2_eq a_addr
      (by clear * - h_b_fAnc ha; dsimp [fCompIdBase, fRListBase, fIsRootBase, lsfOffRCount, lsfHdrSize] at h_b_fAnc ha ⊢; omega)
      (by clear * - ha; dsimp [fCompIdBase, fRListBase, fIsRootBase, fOffRCount, fAncHdrSize] at ha ⊢; omega)
      (by clear * - hrCnt_lt ha; dsimp [fCompIdBase, fRListBase, fIsRootBase] at ha ⊢; omega)
      (by clear * - hz_vCap ha; dsimp [fCompIdBase, fRListBase, fIsRootBase] at ha ⊢; omega)).trans
      (hmem1_fAnc a_addr (by clear * - ha; dsimp [fCompIdBase, fRListBase, fIsRootBase] at ha ⊢; omega))
  have hmem2_aux : ∀ a_addr, auxPtr ≤ a_addr → mem2 a_addr = mem0 a_addr := fun a_addr ha =>
    hmem2_ge_cid a_addr (by clear * - h_fAnc_aux ha; dsimp [fCompIdBase, fRListBase, fIsRootBase, fAncSize] at h_fAnc_aux ha ⊢; omega)
  have hmem2_fHdr : ∀ off, 1 ≤ off → off < fAncHdrSize → mem2 (fAncPtr + off) = mem0 (fAncPtr + off) :=
    fun off ho1 ho2 => (hmem2_eq _
      (by clear * - h_b_fAnc; dsimp [lsfOffRCount, lsfHdrSize] at h_b_fAnc ⊢; omega)
      (by clear * - ho1; dsimp [fOffRCount]; omega)
      (by clear * - ho2; dsimp [fRListBase, fIsRootBase, fAncHdrSize] at ho2 ⊢; omega)
      (by clear * - ho2; dsimp [fIsRootBase, fAncHdrSize] at ho2 ⊢; omega)).trans
      (hmem1_fAnc _ (Nat.le_add_right _ _))
  have hRF_sep : ∀ r₁ ∈ S.RF.R, ∀ r₂ ∈ S.RF.R, r₁ ≠ r₂ → ¬ S.RF.F.Connected r₁ r₂ := by
    intro r₁ hr1 r₂ hr2 hne hconn
    obtain ⟨r, _, huniq⟩ := hInv.to_RF_spanning.2.2.2.1 r₁ (hInv.to_RF_spanning.2.2.1 hr1)
    exact hne ((huniq r₁ ⟨hr1, connected_refl S.RF.F r₁⟩).trans (huniq r₂ ⟨hr2, hconn⟩).symm)
  have hcs_le_qA : fCompSizeBase fAncPtr vCap + vCap ≤ auxQBufABase auxPtr vCap n0 := by
    clear * - h_fAnc_end h_fAnc_aux h_aux_qA; omega
  have hV'_eq_V : S'.RF.F.V = S.RF.F.V := by rw [hF'_eq]; rfl
  have hmid_hdr : mem2 (fAncPtr + fOffRCount) = S.RF.R.card + 1 ∧
      mem2 (fAncPtr + fOffIsRootPtr) = fIsRootBase fAncPtr ∧
      mem2 (fAncPtr + fOffRListPtr) = fRListBase fAncPtr vCap ∧
      mem2 (fAncPtr + fOffCompIdPtr) = fCompIdBase fAncPtr vCap ∧
      mem2 (fAncPtr + fOffCompRootPtr) = fCompRootBase fAncPtr vCap ∧
      mem2 (fAncPtr + fOffCompSizePtr) = fCompSizeBase fAncPtr vCap :=
    ⟨by rw [hmem2_def, Function.update_of_ne (by clear * - h_b_fAnc; dsimp [lsfOffRCount, fOffRCount, lsfHdrSize] at h_b_fAnc ⊢; omega), Function.update_self],
      (hmem2_fHdr fOffIsRootPtr (by decide) (by decide)).trans hIsR_ptr,
      (hmem2_fHdr fOffRListPtr (by decide) (by decide)).trans hRL_ptr,
      (hmem2_fHdr fOffCompIdPtr (by decide) (by decide)).trans hCid_ptr,
      (hmem2_fHdr fOffCompRootPtr (by decide) (by decide)).trans hCR_ptr,
      (hmem2_fHdr fOffCompSizePtr (by decide) (by decide)).trans hCS_ptr⟩
  have hmid_isRoot : ∀ v < vCap, mem2 (fIsRootBase fAncPtr + v) = if v = z then 1 else mem0 (fIsRootBase fAncPtr + v) := by
    intro v hv
    by_cases hvz : v = z
    · subst hvz; simp only [↓reduceIte]
      rw [hmem2_def, Function.update_of_ne (by clear * - h_b_fAnc; dsimp [fIsRootBase, lsfOffRCount, lsfHdrSize] at h_b_fAnc ⊢; omega),
        Function.update_of_ne (by clear * - vCap; dsimp [fIsRootBase, fOffRCount, fAncHdrSize]; omega),
        Function.update_of_ne (by clear * - hv; dsimp [fIsRootBase, fRListBase]; omega),
        Function.update_self]
    · simp only [hvz, ↓reduceIte]
      exact (hmem2_eq _
        (by clear * - h_b_fAnc; dsimp [fIsRootBase, lsfOffRCount, lsfHdrSize] at h_b_fAnc ⊢; omega)
        (by clear * - vCap; dsimp [fIsRootBase, fOffRCount, fAncHdrSize]; omega)
        (by clear * - hv; dsimp [fIsRootBase, fRListBase]; omega)
        (by clear * - hvz; omega)).trans (hmem1_fAnc _ (by clear * - vCap; dsimp [fIsRootBase]; omega))
  have hmid_rList : (∀ i < x.rList.length,
      mem2 (fRListBase fAncPtr vCap + i) = mem0 (fRListBase fAncPtr vCap + i)) ∧
      mem2 (fRListBase fAncPtr vCap + x.rList.length) = z := by
    refine ⟨fun i hi => ?_, ?_⟩
    · exact (hmem2_eq _
        (by clear * - h_b_fAnc; dsimp [fRListBase, fIsRootBase, lsfOffRCount, lsfHdrSize] at h_b_fAnc ⊢; omega)
        (by clear * - vCap; dsimp [fRListBase, fIsRootBase, fOffRCount, fAncHdrSize]; omega)
        (by clear * - hi hrL_len; omega)
        (by clear * - hz_vCap; dsimp [fRListBase, fIsRootBase]; omega)).trans
        (hmem1_fAnc _ (by clear * - vCap; dsimp [fRListBase, fIsRootBase]; omega))
    · rw [hrL_len, hmem2_def,
        Function.update_of_ne (by clear * - h_b_fAnc; dsimp [fRListBase, fIsRootBase, lsfOffRCount, lsfHdrSize] at h_b_fAnc ⊢; omega),
        Function.update_of_ne (by clear * - vCap; dsimp [fRListBase, fIsRootBase, fOffRCount, fAncHdrSize]; omega),
        Function.update_self]
  have hmid_compId : ∀ v < vCap, mem2 (fCompIdBase fAncPtr vCap + v) =
      if v = z then oldCid else mem0 (fCompIdBase fAncPtr vCap + v) := by
    intro v hv
    rw [hmem2_ge_cid _ (Nat.le_add_right _ _)]
    by_cases hvz : v = z
    · subst hvz; simp only [↓reduceIte]; exact hold_eq
    · simp only [hvz, ↓reduceIte]
  obtain ⟨compId', compRoot', compSize', Csmall, Cbig, hCpair, hCle, hFAnc',
    _, hsz'_Cs, hsz'_Cb, hsz'_oth⟩ :=
    fancAt_after_splitCompBFS hFAnc_copy hRF_sep
      (fun v hv => hdgF.2.1 v (hV'_eq_V ▸ hv)) (by rw [hV'_eq_V])
      (by intro v hv; rw [hV'_eq_V]; rw [Finset.mem_insert] at hv
          rcases hv with rfl | hvR
          · exact hz_F
          · exact hInv.RF_V_eq ▸ hInv.to_RF_spanning.2.2.1 hvR)
      hz_not_R hz_vCap (hV'_eq_V ▸ hz_F) (hV'_eq_V ▸ hrC_F) hold_act hrC_eq.symm haV hbV hnot_ab
      hpart_V hother_conn hother_disj hroots_sep hmid_hdr hmid_isRoot hmid_rList hmid_compId
      (fun c _ => hmem2_ge_cid _ (by clear * - vCap; dsimp [fCompRootBase, fCompIdBase, fAncPtr, vCap, eCap, n0, tM]; omega))
      (fun c _ => hmem2_ge_cid _ (by clear * - vCap; dsimp [fCompSizeBase, fCompRootBase, fCompIdBase, fAncPtr, vCap, eCap, n0, tM]; omega))
      hpost_bfs hcs_le_qA
  have hfr3 : ∀ a_addr, ¬ (fCompIdBase fAncPtr vCap ≤ a_addr ∧ a_addr < fCompSizeBase fAncPtr vCap + vCap) →
      ¬ (auxQBufABase auxPtr vCap n0 ≤ a_addr ∧ a_addr < auxQBufBBase auxPtr vCap n0 + vCap) →
      mem3 a_addr = mem2 a_addr := by
    rcases hpost_bfs with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hargs_b, _, hfr_b, _⟩
    simp only [List.cons.injEq, and_true] at hargs_b
    rcases hargs_b with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact hfr_b
  let x' : LSFConcrete :=
    { x with rList := x.rList ++ [z], compId := compId', compRoot := compRoot',
             compSize := compSize', activeCids := insert z x.activeCids }
  have hsame : SameStaticConcrete x x' := SameStaticConcrete.refl x
  have hmem3_outside_end : ∀ a_addr, a_addr < b ∨ x.endAddr b ≤ a_addr → mem3 a_addr = mem0 a_addr := by
    intro a_addr ha
    have h1 : mem3 a_addr = mem2 a_addr := hfr3 a_addr
      (fun hc => by clear * - ha h_b_fAnc h_fAnc_aux h_aux_end h_fAnc_end hc; dsimp [fCompIdBase, fRListBase, fIsRootBase] at hc; omega)
      (fun hc => by clear * - ha h_b_fAnc h_fAnc_aux h_aux_end h_qB_aux h_aux_qA hc; omega)
    have h2 : mem2 a_addr = mem1 a_addr := hmem2_eq a_addr
      (by clear * - ha h_b_fAnc h_fAnc_aux h_aux_end; dsimp [lsfOffRCount, lsfHdrSize] at h_b_fAnc ⊢; omega)
      (by clear * - ha h_b_fAnc h_fAnc_aux h_aux_end; dsimp [fOffRCount, fAncSize, fAncHdrSize] at h_fAnc_aux ⊢; omega)
      (by clear * - ha h_b_fAnc h_fAnc_aux h_aux_end hrCnt_lt; dsimp [fRListBase, fIsRootBase, fAncSize] at h_fAnc_aux ⊢; omega)
      (by clear * - ha h_b_fAnc h_fAnc_aux h_aux_end hz_vCap; dsimp [fIsRootBase, fAncSize] at h_fAnc_aux ⊢; omega)
    have h3 : mem1 a_addr = mem0 a_addr := hfr1 a_addr (by clear * - ha h_b_dgF h_dgF_fAnc h_fAnc_aux h_aux_end; omega)
    exact h1.trans (h2.trans h3)
  have hmem3_below_fAnc : ∀ a_addr < fAncPtr, a_addr ≠ b + lsfOffRCount →
      ¬ (dgFPtr ≤ a_addr ∧ a_addr < dgFPtr + dynGraphSize vCap eCapF) →
      mem3 a_addr = mem0 a_addr := fun a_addr ha hne hnotF => by
    have h1 : mem3 a_addr = mem2 a_addr := hfr3 a_addr
      (fun hc => by clear * - ha hc; dsimp [fCompIdBase, fRListBase, fIsRootBase] at hc; omega)
      (fun hc => by clear * - ha h_fAnc_aux h_aux_qA hc; omega)
    have h2 : mem2 a_addr = mem1 a_addr := hmem2_eq a_addr hne
      (by clear * - ha; dsimp [fOffRCount]; omega)
      (by clear * - ha; dsimp [fRListBase, fIsRootBase]; omega)
      (by clear * - ha; dsimp [fIsRootBase]; omega)
    have h3 : mem1 a_addr = mem0 a_addr := hfr1 a_addr (by clear * - hnotF; omega)
    exact h1.trans (h2.trans h3)
  have hhdr' : lsfHeaderAt mem3 b S' x' := by
    have hhd_other : ∀ off < lsfHdrSize, off ≠ lsfOffRCount → mem3 (b + off) = mem0 (b + off) :=
      fun off hoff hne => hmem3_below_fAnc (b + off) (by clear * - h_b_fAnc hoff; omega)
        (by clear * - hne; omega) (by clear * - h_b_dgF hoff; omega)
    have hrcnt' : mem3 (b + lsfOffRCount) = S'.R.card := by
      have h1 : mem3 (b + lsfOffRCount) = mem2 (b + lsfOffRCount) := hfr3 _
        (fun hc => by clear * - h_b_fAnc hc; dsimp [fCompIdBase, fRListBase, fIsRootBase, lsfOffRCount, lsfHdrSize] at h_b_fAnc hc; omega)
        (fun hc => by clear * - h_b_fAnc h_fAnc_aux h_aux_qA hc; dsimp [lsfOffRCount, lsfHdrSize, fAncSize] at h_b_fAnc h_fAnc_aux hc ⊢; omega)
      rw [h1, hmem2_def, Function.update_self, hR', Finset.card_insert_of_notMem hz_not_R]; rfl
    rcases hhdr with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      _, h17, h18, h19, h20, h21, h22, h23⟩
    refine ⟨(hhd_other _ (by decide) (by decide)).trans h0, (hhd_other _ (by decide) (by decide)).trans h1,
      (hhd_other _ (by decide) (by decide)).trans h2, (hhd_other _ (by decide) (by decide)).trans h3,
      (hhd_other _ (by decide) (by decide)).trans h4, (hhd_other _ (by decide) (by decide)).trans h5,
      (hhd_other _ (by decide) (by decide)).trans h6, (hhd_other _ (by decide) (by decide)).trans h7,
      (hhd_other _ (by decide) (by decide)).trans h8, (hhd_other _ (by decide) (by decide)).trans h9,
      (hhd_other _ (by decide) (by decide)).trans h10, (hhd_other _ (by decide) (by decide)).trans h11,
      (hhd_other _ (by decide) (by decide)).trans h12, (hhd_other _ (by decide) (by decide)).trans h13,
      (hhd_other _ (by decide) (by decide)).trans h14, (hhd_other _ (by decide) (by decide)).trans h15,
      hrcnt', (hhd_other _ (by decide) (by decide)).trans h17,
      (hhd_other _ (by decide) (by decide)).trans h18, (hhd_other _ (by decide) (by decide)).trans h19,
      (hhd_other _ (by decide) (by decide)).trans h20, (hhd_other _ (by decide) (by decide)).trans h21,
      (hhd_other _ (by decide) (by decide)).trans h22, (hhd_other _ (by decide) (by decide)).trans h23⟩
  have hdgF3 : DynGraphAt mem3 dgFPtr vCap eCapF S'.RF.F :=
    hdgF2.of_agree fun a_addr ha1 ha2 => hfr3 a_addr
      (fun hc => by clear * - h_dgF_fAnc ha2 hc; dsimp [fCompIdBase, fRListBase, fIsRootBase] at hc; omega)
      (fun hc => by clear * - h_dgF_fAnc h_fAnc_aux h_aux_qA ha2 hc; omega)
  have hmem3_between : ∀ a_addr, fAncPtr + fAncSize vCap ≤ a_addr → a_addr < auxPtr →
      mem3 a_addr = mem0 a_addr := fun a_addr ha1 ha2 => by
    have h1 : mem3 a_addr = mem2 a_addr := hfr3 a_addr
      (fun hc => by clear * - h_fAnc_end ha1 hc; omega)
      (fun hc => by clear * - h_aux_qA ha2 hc; omega)
    exact h1.trans (hmem2_ge_cid a_addr (by clear * - ha1; dsimp [fCompIdBase, fRListBase, fIsRootBase, fAncSize] at ha1 ⊢; omega))
  have hAux3 : AuxAt mem3 auxPtr vCap n0 tM S' x.tOrigList x.vList
      x.t0Parent x.t0ParentTreeIdx x.t0Depth x.thParent x.upV x.upMinIdx :=
    auxAt_of_agree_except_qBuf hAux_copy hvT_lt rfl rfl rfl rfl rfl fun a_addr ha1 _ hnotQ =>
      (hfr3 a_addr (fun hc => by clear * - h_fAnc_aux h_fAnc_end ha1 hc; omega) hnotQ).trans
        (hmem2_aux a_addr ha1)
  have hmem3_above_aux : ∀ a_addr, auxPtr + auxSize vCap n0 ≤ a_addr →
      mem3 a_addr = mem0 a_addr := fun a_addr ha1 => by
    have h1 : mem3 a_addr = mem2 a_addr := hfr3 a_addr
      (fun hc => by clear * - h_fAnc_aux h_fAnc_end ha1 hc; omega)
      (fun hc => by clear * - h_qB_aux ha1 hc; omega)
    exact h1.trans (hmem2_aux a_addr (by clear * - ha1; omega))
  have hstk3 : StackMemAt mem3 thStackBase rest :=
    stackMemAt_of_agree hstk_rest fun j hj => by
      have hge : auxQBufBBase auxPtr vCap n0 + vCap ≤ thStackBase + j := by
        clear * - vCap; dsimp [thStackBase, auxThStackBase, auxVisBBase, auxVisABase]; omega
      have hge_aux : auxPtr ≤ thStackBase + j := by
        clear * - vCap; dsimp [thStackBase, auxThStackBase, auxVisBBase, auxVisABase,
          auxQBufBBase, auxQBufABase, auxIsOrigVertBase, auxOrigVertBase, auxThParentBase,
          auxUpMinIdxBase, auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase,
          auxVListBase, auxVIdxBase]; omega
      have h1 : mem3 (thStackBase + j) = mem2 (thStackBase + j) := hfr3 _
        (fun hc => by clear * - h_fAnc_aux h_fAnc_end hge_aux hc; omega)
        (fun hc => Nat.not_lt.mpr hge hc.2)
      exact h1.trans (hmem2_aux _ hge_aux)
  have hFAnc3 : FAncAt mem3 fAncPtr vCap S'.RF x'.rList x'.compId x'.compRoot x'.compSize x'.activeCids := by
    have hRF'_eq : S'.RF = { F := S'.RF.F, R := insert z S.RF.R } := by
      cases h1 : S'.RF with
      | mk F_v R_v =>
        have hR_v : R_v = insert z S.RF.R := by
          have : S'.RF.R = S'.R := rfl
          rw [h1] at this; exact this.trans hR'
        subst hR_v; rfl
    rw [hRF'_eq]; exact hFAnc'
  have hrep3 : (LSFRep x.h).rep b S' x' mem3 :=
    ⟨hxH, hh1, hLin, hLw, hkn, hkeq, hInv', hn0, hm0, htM, hnv, hme, htn, hn1, hvT_lt, heG_lt,
      hhdr',
      hdgG.of_agree (fun a_addr ha1 ha2 => hmem3_below_fAnc a_addr
        (by clear * - hlay ha2 h_dgF_fAnc; dsimp only [dgFPtr, fAncPtr, eCapF, vCap, eCap, n0, tM] at h_dgF_fAnc ⊢; omega)
        (by clear * - hlay ha1; dsimp [lsfOffRCount, lsfHdrSize] at hlay ha1 ⊢; omega)
        (by clear * - hlay ha2; dsimp only [dgFPtr, vCap, eCap, tM]; omega)),
      hT.of_agree (fun a_addr ha1 ha2 => hmem3_below_fAnc a_addr
        (by clear * - hlay ha2 h_dgF_fAnc; dsimp only [dgFPtr, fAncPtr, eCapF, vCap, eCap, n0, tM] at h_dgF_fAnc ⊢; omega)
        (by clear * - hlay ha1; dsimp [lsfOffRCount, lsfHdrSize] at hlay ha1 ⊢; omega)
        (by clear * - hlay ha2; dsimp only [dgFPtr, vCap, eCap, tM]; omega)),
      hdgF3, hFAnc3,
      hW.of_agree (fun a_addr ha1 ha2 => hmem3_between a_addr
        (by clear * - hlay ha1; dsimp only [fAncPtr, vCap, eCap, n0, tM]; omega)
        (by clear * - hlay ha2; dsimp only [auxPtr, vCap, eCap, n0, tM, L_w]; omega)),
      hwstr.of_agree
        (fun a_addr ha1 _ => hmem3_above_aux a_addr (by clear * - hlay ha1; dsimp only [auxPtr, vCap, eCap, n0, tM, L_w]; omega))
        (fun a_addr ha1 _ => hmem3_above_aux a_addr (by clear * - hlay ha1; dsimp only [auxPtr, vCap, eCap, n0, tM, L_w]; omega)),
      hAux3⟩
  have hphi_drop : lsfPhi b x' mem3 + 500 * auxLogCap n0 + 1400 + 1100 * mSmall ≤ lsfPhi b x mem0 := by
    rw [lsfPhi_eq_semantic hrep3, lsfPhi_eq_semantic hrep_orig]
    let E_small := S'.RF.F.E.filter fun e => S'.RF.F.tail e ∈ Csmall
    have hEs_card : E_small.card = mSmall := by
      have hcard_Cs : Csmall.card = E_small.card + 1 := by
        rcases hCpair with ⟨hCs, _⟩ | ⟨hCs, _⟩
        · have hEs_eq : E_small = S'.RF.F.E.filter fun e => S'.RF.F.Connected (S'.RF.F.tail e) a := by
            ext e; simp only [E_small, hCs, Finset.mem_filter]
            exact ⟨fun ⟨he, _, hc⟩ => ⟨he, hc⟩, fun ⟨he, hc⟩ => ⟨he, (hInv'.to_RF_spanning.1.1 e he).1, hc⟩⟩
          rw [hCs, hEs_eq]; exact forest_comp_card_eq_edges_succ hInv'.to_RF_spanning.1 haV
        · have hEs_eq : E_small = S'.RF.F.E.filter fun e => S'.RF.F.Connected (S'.RF.F.tail e) b' := by
            ext e; simp only [E_small, hCs, Finset.mem_filter]
            exact ⟨fun ⟨he, _, hc⟩ => ⟨he, hc⟩, fun ⟨he, hc⟩ => ⟨he, (hInv'.to_RF_spanning.1.1 e he).1, hc⟩⟩
          rw [hCs, hEs_eq]; exact forest_comp_card_eq_edges_succ hInv'.to_RF_spanning.1 hbV
      have hEA_card : (S'.RF.F.V.filter fun v => S'.RF.F.Connected v a).card =
          (S'.RF.F.E.filter fun e => S'.RF.F.Connected (S'.RF.F.tail e) a).card + 1 :=
        forest_comp_card_eq_edges_succ hInv'.to_RF_spanning.1 haV
      have hEB_card : (S'.RF.F.V.filter fun v => S'.RF.F.Connected v b').card =
          (S'.RF.F.E.filter fun e => S'.RF.F.Connected (S'.RF.F.tail e) b').card + 1 :=
        forest_comp_card_eq_edges_succ hInv'.to_RF_spanning.1 hbV
      rcases hCpair with ⟨hCs, hCb⟩ | ⟨hCs, hCb⟩
      · have hle : (S'.RF.F.E.filter fun e => S'.RF.F.Connected (S'.RF.F.tail e) a).card ≤
            (S'.RF.F.E.filter fun e => S'.RF.F.Connected (S'.RF.F.tail e) b').card := by
          rw [hCs, hCb, hEA_card, hEB_card] at hCle; omega
        have hm : mSmall = (S'.RF.F.E.filter fun e => S'.RF.F.Connected (S'.RF.F.tail e) a).card :=
          Nat.min_eq_left hle
        rw [hCs, hEA_card] at hcard_Cs
        exact (Nat.succ.inj hcard_Cs).symm.trans hm.symm
      · have hle : (S'.RF.F.E.filter fun e => S'.RF.F.Connected (S'.RF.F.tail e) b').card ≤
            (S'.RF.F.E.filter fun e => S'.RF.F.Connected (S'.RF.F.tail e) a).card := by
          rw [hCs, hCb, hEA_card, hEB_card] at hCle; omega
        have hm : mSmall = (S'.RF.F.E.filter fun e => S'.RF.F.Connected (S'.RF.F.tail e) b').card :=
          Nat.min_eq_right hle
        rw [hCs, hEB_card] at hcard_Cs
        exact (Nat.succ.inj hcard_Cs).symm.trans hm.symm
    have hRorig'_le : S'.R_orig.card ≤ n0 := by
      dsimp only [n0]; rw [← hn0]
      exact (Finset.card_le_card hInv'.R_orig_sub).trans_eq (congrArg Finset.card hInv.hTV)
    have hE'_eq : S'.RF.F.E = S.RF.F.E.erase cutE := by rw [hF'_eq]; rfl
    have htail_eq : ∀ e, S'.RF.F.tail e = S.RF.F.tail e := fun e => by rw [hF'_eq]; rfl
    have hsum_eq : Csmall.card + Cbig.card = oldSize := by
      rw [hnewSum_eq]
      rcases hCpair with ⟨hCs, hCb⟩ | ⟨hCs, hCb⟩
      · rw [hCs, hCb]
      · rw [hCs, hCb, Nat.add_comm]
    have hcid_of_conn : ∀ u ∈ S.RF.F.V, S.RF.F.Connected u rC → x.compId u = oldCid := by
      intro u hu hcc_r
      obtain ⟨heq, hact, hcc⟩ := hcid_mem u hu
      rw [heq] at hact hcc
      have hcr_eq : x.compRoot (x.compId u) = rC := by
        by_contra hne
        exact hRF_sep _ (hact_spec _ hact).2.2.1 _ hrC_R hne (connected_trans (connected_symm hcc) hcc_r)
      have h1' := (hact_spec _ hact).2.2.2.1
      rw [hcr_eq] at h1'; exact h1'.symm.trans hcid_rC
    have hmono : ∀ e ∈ S'.RF.F.E, x'.compSize (x'.compId (S'.RF.F.tail e)) ≤
        x.compSize (x.compId (S.RF.F.tail e)) := by
      intro e he
      have huF' := (hInv'.to_RF_spanning.1.1 e he).1
      have huF : S.RF.F.tail e ∈ S.RF.F.V := hV'_eq_V ▸ (htail_eq e ▸ huF')
      by_cases huS : S'.RF.F.tail e ∈ Csmall
      · have h1 := (hsz'_Cs _ huF' huS).1
        have hconn_ab : S'.RF.F.Connected (S'.RF.F.tail e) a ∨ S'.RF.F.Connected (S'.RF.F.tail e) b' := by
          rcases hCpair with ⟨hCs, _⟩ | ⟨hCs, _⟩
          · rw [hCs] at huS; exact Or.inl (Finset.mem_filter.mp huS).2
          · rw [hCs] at huS; exact Or.inr (Finset.mem_filter.mp huS).2
        have hu_conn : S.RF.F.Connected (S.RF.F.tail e) rC := by
          rcases (hpart_V _ huF').mp hconn_ab with hEq | ⟨_, hc⟩
          · rw [← htail_eq e, hEq]; exact hconn_zrC
          · rwa [← htail_eq e]
        show compSize' (compId' (S'.RF.F.tail e)) ≤ x.compSize (x.compId (S.RF.F.tail e))
        rw [h1, hcid_of_conn _ huF hu_conn, ← holdSz_eq]; omega
      · by_cases huB : S'.RF.F.tail e ∈ Cbig
        · have h1 := hsz'_Cb _ huF' huB
          have hconn_ab : S'.RF.F.Connected (S'.RF.F.tail e) a ∨ S'.RF.F.Connected (S'.RF.F.tail e) b' := by
            rcases hCpair with ⟨_, hCb⟩ | ⟨_, hCb⟩
            · rw [hCb] at huB; exact Or.inr (Finset.mem_filter.mp huB).2
            · rw [hCb] at huB; exact Or.inl (Finset.mem_filter.mp huB).2
          have hu_conn : S.RF.F.Connected (S.RF.F.tail e) rC := by
            rcases (hpart_V _ huF').mp hconn_ab with hEq | ⟨_, hc⟩
            · rw [← htail_eq e, hEq]; exact hconn_zrC
            · rwa [← htail_eq e]
          show compSize' (compId' (S'.RF.F.tail e)) ≤ x.compSize (x.compId (S.RF.F.tail e))
          rw [h1, hcid_of_conn _ huF hu_conn, ← holdSz_eq]; omega
        · have h1 := (hsz'_oth _ huF' huS huB).2
          show compSize' (compId' (S'.RF.F.tail e)) ≤ x.compSize (x.compId (S.RF.F.tail e))
          rw [h1, htail_eq e]
    have hdrop : ∀ e ∈ E_small, 2 ≤ x'.compSize (x'.compId (S'.RF.F.tail e)) ∧
        2 * (x'.compSize (x'.compId (S'.RF.F.tail e)) - 1) ≤ x.compSize (x.compId (S.RF.F.tail e)) - 1 := by
      intro e he
      obtain ⟨heF', huS⟩ := Finset.mem_filter.mp he
      have huF' := (hInv'.to_RF_spanning.1.1 e heF').1
      have hvF' := (hInv'.to_RF_spanning.1.1 e heF').2
      have hne_end : S'.RF.F.tail e ≠ S'.RF.F.head e := by
        intro hEq
        exact hInv'.to_RF_spanning.1.2 [(e, true)] ⟨by simp, by simp, S'.RF.F.tail e,
          .cons heF' rfl (show S'.RF.F.IsWalk (S'.RF.F.head e) (S'.RF.F.tail e) [] from hEq ▸ .nil _)⟩
      have hvS : S'.RF.F.head e ∈ Csmall := by
        have hconn_uv : S'.RF.F.Connected (S'.RF.F.head e) (S'.RF.F.tail e) :=
          ⟨[(e, false)], .cons heF' rfl (.nil _)⟩
        rcases hCpair with ⟨hCs, _⟩ | ⟨hCs, _⟩ <;>
          (rw [hCs] at huS ⊢; exact Finset.mem_filter.mpr ⟨hvF', connected_trans hconn_uv (Finset.mem_filter.mp huS).2⟩)
      have hCs_ge2 : 2 ≤ Csmall.card :=
        Finset.one_lt_card.mpr ⟨S'.RF.F.tail e, huS, S'.RF.F.head e, hvS, hne_end⟩
      have h1 := (hsz'_Cs _ huF' huS).1
      have huF : S.RF.F.tail e ∈ S.RF.F.V := hV'_eq_V ▸ (htail_eq e ▸ huF')
      have hu_conn : S.RF.F.Connected (S.RF.F.tail e) rC := by
        have hconn_ab : S'.RF.F.Connected (S'.RF.F.tail e) a ∨ S'.RF.F.Connected (S'.RF.F.tail e) b' := by
          rcases hCpair with ⟨hCs, _⟩ | ⟨hCs, _⟩
          · rw [hCs] at huS; exact Or.inl (Finset.mem_filter.mp huS).2
          · rw [hCs] at huS; exact Or.inr (Finset.mem_filter.mp huS).2
        rcases (hpart_V _ huF').mp hconn_ab with hEq | ⟨_, hc⟩
        · rw [← htail_eq e, hEq]; exact hconn_zrC
        · rwa [← htail_eq e]
      show 2 ≤ compSize' (compId' (S'.RF.F.tail e)) ∧
        2 * (compSize' (compId' (S'.RF.F.tail e)) - 1) ≤ x.compSize (x.compId (S.RF.F.tail e)) - 1
      rw [h1, hcid_of_conn _ huF hu_conn, ← holdSz_eq]
      exact ⟨hCs_ge2, by omega⟩
    rw [← hEs_card]
    exact phi_drop_addRoot_cut hRorig' hz_not hRorig'_le hE'_eq hcut_mem
      (Finset.filter_subset _ _) hmono hdrop
  exact ⟨x', hsame, hrep3, hmem3_outside_end, hstk3, hphi_drop⟩

end

end MinCostFlow.LSF.Program
