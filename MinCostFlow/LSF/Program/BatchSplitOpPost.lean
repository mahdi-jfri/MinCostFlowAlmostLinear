module

public import MinCostFlow.LSF.Program.BatchSplitOpBase
import Mathlib.Tactic.Linarith

/-!
# Post-Split `LSFRep` and Frame Assembly (`BatchSplitOpPost`)

Assembles `(LSFRep h).rep b S' x' mem7` and the outside-footprint frame equation after the final
two stores (`origVert[v'] := vOrig`, `isOrigVert[v'] := 0`) of `lsfSplitUpdateProc`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

lemma lsfSplitUpdate_assemble_rep
    {h b v v' rCnt : ℕ} {St Sh : Finset ℕ}
    {S : LSFState} {x x1 : LSFConcrete}
    {compId' compRoot' compSize' : ℕ → ℕ}
    {mem1 mem2 mem3 mem4 mem5 mem6 : ℕ → ℕ}
    (hsame1 : SameStaticConcrete x x1)
    (hrep1 : (LSFRep h).rep b { S with R₀_base := insert (S.origVert v) S.R₀_base } x1 mem1)
    (hInv' : LSFStructInv (applyLSFUpdate S (.split v v' St Sh)))
    (hv'_not_R1 : v' ∉ ({ S with R₀_base := insert (S.origVert v) S.R₀_base }).R)
    (hR' : (applyLSFUpdate S (.split v v' St Sh)).R =
      insert v' ({ S with R₀_base := insert (S.origVert v) S.R₀_base }).R)
    (hv'_not_T0 : v' ∉ (applyLSFUpdate S (.split v v' St Sh)).T₀.V)
    (hv'_cap : v' < x.vCap)
    (hrCnt_def : rCnt = ({ S with R₀_base := insert (S.origVert v) S.R₀_base }).R.card)
    (hrCnt_lt_vc : rCnt < x.vCap)
    (hfr_dgF : ∀ a, a < lsfDgFPtr b x.vCap x.eCap x.tM ∨
      lsfDgFPtr b x.vCap x.eCap x.tM + dynGraphSize x.vCap (fECap x.eCap x.n0) ≤ a → mem2 a = mem1 a)
    (hmem3_out : ∀ a,
      a ≠ fIsRootBase (lsfFAncPtr b x.vCap x.eCap x.n0 x.tM) + v' →
      a ≠ fRListBase (lsfFAncPtr b x.vCap x.eCap x.n0 x.tM) x.vCap + rCnt →
      a ≠ lsfFAncPtr b x.vCap x.eCap x.n0 x.tM + fOffRCount →
      a ≠ b + lsfOffRCount →
      a ≠ fCompIdBase (lsfFAncPtr b x.vCap x.eCap x.n0 x.tM) x.vCap + v' →
      mem3 a = mem2 a)
    (hmem3_rcnt : mem3 (b + lsfOffRCount) = rCnt + 1)
    (hmem3_aux : ∀ a, lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w ≤ a →
      a < lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w + auxSize x.vCap x.n0 → mem3 a = mem1 a)
    (hfr_bfs : ∀ a,
      ¬ (fCompIdBase (lsfFAncPtr b x.vCap x.eCap x.n0 x.tM) x.vCap ≤ a ∧
        a < fCompSizeBase (lsfFAncPtr b x.vCap x.eCap x.n0 x.tM) x.vCap + x.vCap) →
      ¬ (auxQBufABase (lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w) x.vCap x.n0 ≤ a ∧
        a < auxQBufBBase (lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w) x.vCap x.n0 + x.vCap) →
      mem4 a = mem3 a)
    (hfr_bfs_below_cid : ∀ a, a < fCompIdBase (lsfFAncPtr b x.vCap x.eCap x.n0 x.tM) x.vCap →
      mem4 a = mem3 a)
    (hmem4_out_b : ∀ a, a < b ∨ x.endAddr b ≤ a → mem4 a = mem1 a)
    (hfr_ts : ∀ a, a < lsfTBlockPtr b x.vCap x.eCap ∨
      lsfTBlockPtr b x.vCap x.eCap + tBlockSize x.vCap x.eCap x.tM ≤ a → mem5 a = mem4 a)
    (hfr_dgG : ∀ a, a < lsfDgGPtr b ∨
      lsfDgGPtr b + dynGraphSize x.vCap x.eCap ≤ a → mem6 a = mem5 a)
    (hdgG6_raw : DynGraphAt mem6 (lsfDgGPtr b) x.vCap x.eCap (applyLSFUpdate S (.split v v' St Sh)).G)
    (hT5_raw : TBlockAt mem5 (lsfTBlockPtr b x.vCap x.eCap) x.vCap x.eCap x.tM
      (applyLSFUpdate S (.split v v' St Sh)).G (applyLSFUpdate S (.split v v' St Sh)).T_cur
      (applyLSFUpdate S (.split v v' St Sh)).T₀ (applyLSFUpdate S (.split v v' St Sh)).π x.tOrigList)
    (hdgF3 : DynGraphAt mem3 (lsfDgFPtr b x.vCap x.eCap x.tM) x.vCap (fECap x.eCap x.n0)
      (applyLSFUpdate S (.split v v' St Sh)).RF.F)
    (hFAnc4_raw : FAncAt mem4 (lsfFAncPtr b x1.vCap x1.eCap x1.n0 x1.tM) x1.vCap
      (applyLSFUpdate S (.split v v' St Sh)).RF
      (x1.rList ++ [v']) compId' compRoot' compSize' (insert v' x1.activeCids))
    (hVis4 : ∀ u < x.vCap,
      mem4 (auxVisABase (lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w) x.vCap x.n0 + u) = 0 ∧
      mem4 (auxVisBBase (lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w) x.vCap x.n0 + u) = 0) :
    let x' : LSFConcrete :=
      { x1 with
        rList := x1.rList ++ [v']
        compId := compId'
        compRoot := compRoot'
        compSize := compSize'
        activeCids := insert v' x1.activeCids }
    let mem7 : ℕ → ℕ :=
      Function.update
        (Function.update mem6
          (auxOrigVertBase (lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w) x.vCap x.n0 + v') (S.origVert v))
        (auxIsOrigVertBase (lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w) x.vCap x.n0 + v') 0
    (LSFRep h).rep b (applyLSFUpdate S (.split v v' St Sh)) x' mem7 ∧
    (∀ a, a < b ∨ x.endAddr b ≤ a → mem7 a = mem1 a) := by
  classical
  intro x'
  set vCap := x.vCap; set eCap := x.eCap; set n0 := x.n0; set tM := x.tM; set L_w := x.L_w
  set eCapF := fECap eCap n0
  set dgGPtr := lsfDgGPtr b
  set tPtr := lsfTBlockPtr b vCap eCap
  set dgFPtr := lsfDgFPtr b vCap eCap tM
  set fAncPtr := lsfFAncPtr b vCap eCap n0 tM
  set wPtr := lsfWBlockPtr b vCap eCap n0 tM
  set auxPtr := lsfAuxPtr b vCap eCap n0 tM L_w
  set wstrNumPtr := lsfWstrNumPtr b vCap eCap n0 tM
  set wstrDenPtr := lsfWstrDenPtr b vCap eCap n0 tM L_w
  set origBase := auxOrigVertBase auxPtr vCap n0
  set isOrigBase := auxIsOrigVertBase auxPtr vCap n0
  set vOrig := S.origVert v
  set S₁ := { S with R₀_base := insert vOrig S.R₀_base }
  set S' := applyLSFUpdate S (.split v v' St Sh)
  rcases lsfBlock_disjoint' b vCap eCap n0 tM L_w with ⟨hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, hl9⟩
  change b + lsfHdrSize = dgGPtr at hl1
  have hb_lt_dgF : b + 24 ≤ dgFPtr := by dsimp [lsfHdrSize] at hl1; omega
  change dgGPtr + dynGraphSize vCap eCap = tPtr at hl2
  change tPtr + tBlockSize vCap eCap tM = dgFPtr at hl3
  change dgFPtr + dynGraphSize vCap eCapF = fAncPtr at hl4
  change fAncPtr + fAncSize vCap = wPtr at hl5
  change wPtr + wBlockSize n0 = auxPtr at hl6
  change auxPtr + auxSize vCap n0 = wstrNumPtr at hl7
  change wstrNumPtr + eCap * L_w = wstrDenPtr at hl8
  change wstrDenPtr + eCap * L_w = lsfEndAddr b vCap eCap n0 tM L_w at hl9
  have hfAnc_bds :
      fAncPtr + fOffRCount < fIsRootBase fAncPtr ∧
      fIsRootBase fAncPtr + vCap = fRListBase fAncPtr vCap ∧
      fRListBase fAncPtr vCap + vCap = fCompIdBase fAncPtr vCap ∧
      fCompIdBase fAncPtr vCap + vCap = fCompRootBase fAncPtr vCap ∧
      fCompRootBase fAncPtr vCap + vCap = fCompSizeBase fAncPtr vCap ∧
      fCompSizeBase fAncPtr vCap + vCap = fAncPtr + fAncSize vCap := by
    dsimp only [fIsRootBase, fRListBase, fCompIdBase, fCompRootBase, fCompSizeBase,
      fOffRCount, fAncHdrSize, fAncSize]; omega
  have haux_bds :
      auxPtr + auxHdrSize ≤ origBase ∧
      origBase + vCap = isOrigBase ∧
      isOrigBase + vCap = auxQBufABase auxPtr vCap n0 ∧
      auxQBufABase auxPtr vCap n0 + vCap = auxQBufBBase auxPtr vCap n0 ∧
      auxQBufBBase auxPtr vCap n0 + vCap = auxVisABase auxPtr vCap n0 ∧
      auxVisABase auxPtr vCap n0 + vCap = auxVisBBase auxPtr vCap n0 ∧
      auxVisBBase auxPtr vCap n0 + vCap ≤ auxPtr + auxSize vCap n0 := by
    dsimp only [origBase, isOrigBase, auxOrigVertBase, auxIsOrigVertBase, auxQBufABase,
      auxQBufBBase, auxVisABase, auxVisBBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase,
      auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase,
      auxHdrSize, auxSize]; omega
  have hend_eq : x.endAddr b = lsfEndAddr b vCap eCap n0 tM L_w := rfl
  have hx1_vc : x1.vCap = vCap := hsame1.1
  have hx1_ec : x1.eCap = eCap := hsame1.2.1
  have hx1_n0 : x1.n0 = n0 := hsame1.2.2.1
  have hx1_tM : x1.tM = tM := hsame1.2.2.2.2.1
  have hx1_Lw : x1.L_w = L_w := hsame1.2.2.2.2.2.2.2.2.1
  have hx1_tL : x1.tOrigList = x.tOrigList := hsame1.2.2.2.2.2.2.2.2.2.2.1
  rcases hrep1 with ⟨hxH1, hh1_1, hLin1, hLw1, hkn1, hkeq1, _, hn0_1, hm0_1, htM1, hnv1, hme1, htn1,
    hn1_1, hvT_lt1, heG_lt1, hhdr1, hdgG1, hT1, hdgF1, hFAnc1, hW1, hwstr1, hAux1⟩
  have horig_v' : vOrig = S'.origVert v' := by
    simp [S', vOrig, applyLSFUpdate]
  have horig_other : ∀ u, u ≠ v' → S'.origVert u = S₁.origVert u := fun u hu => by
    simp [S', S₁, applyLSFUpdate, Function.update_of_ne hu]
  let mem7 : ℕ → ℕ := Function.update (Function.update mem6 (origBase + v') vOrig) (isOrigBase + v') 0
  -- Assemble `(LSFRep h).rep b S' x' mem7`
  have hmem7_below_aux : ∀ a, a < auxPtr → mem7 a = mem6 a := fun a ha => by
    dsimp only [mem7]
    rw [Function.update_of_ne (by clear * - ha haux_bds; omega),
      Function.update_of_ne (by clear * - ha haux_bds; omega)]
  have hmem7_above_aux : ∀ a, auxPtr + auxSize vCap n0 ≤ a → mem7 a = mem6 a := fun a ha => by
    dsimp only [mem7]
    rw [Function.update_of_ne (by clear * - ha haux_bds hv'_cap; omega),
      Function.update_of_ne (by clear * - ha haux_bds hv'_cap; omega)]
  have hmem7_ge_dgF_below_aux : ∀ a, dgFPtr ≤ a → a < auxPtr → mem7 a = mem4 a := fun a ha1 ha2 =>
    (hmem7_below_aux a ha2).trans
      ((hfr_dgG a (Or.inr (by clear * - ha1 hl2 hl3; omega))).trans
        (hfr_ts a (Or.inr (by clear * - ha1 hl3; omega))))
  have hfr_all7 : ∀ a, a < b ∨ x.endAddr b ≤ a → mem7 a = mem1 a := fun a ha => by
    have h76 : mem7 a = mem6 a := by
      rcases ha with h | h
      · exact hmem7_below_aux a (by clear * - h hl1 hl2 hl3 hl4 hl5 hl6; omega)
      · exact hmem7_above_aux a (by clear * - h hl7 hl8 hl9 hend_eq; omega)
    have h65 : mem6 a = mem5 a := hfr_dgG a (by
      clear * - ha hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hend_eq; rcases ha with h | h <;> [left; right] <;> omega)
    have h54 : mem5 a = mem4 a := hfr_ts a (by
      clear * - ha hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hend_eq; rcases ha with h | h <;> [left; right] <;> omega)
    exact h76.trans (h65.trans (h54.trans (hmem4_out_b a ha)))
  have hhdr7 : lsfHeaderAt mem7 b S' x' := by
    have hhd_other : ∀ off < lsfHdrSize, off ≠ lsfOffRCount → mem7 (b + off) = mem1 (b + off) := by
      intro off hoff hne
      have h76 := hmem7_below_aux (b + off) (by clear * - hoff hl1 hl2 hl3 hl4 hl5 hl6; omega)
      have h65 := hfr_dgG (b + off) (Or.inl (by clear * - hoff hl1; omega))
      have h54 := hfr_ts (b + off) (Or.inl (by clear * - hoff hl1 hl2; omega))
      have h43 := hfr_bfs_below_cid (b + off) (by clear * - hoff hl1 hl2 hl3 hl4 hfAnc_bds; omega)
      have h32 := hmem3_out (b + off)
        (by clear * - hoff hl1 hl2 hl3 hl4 hfAnc_bds; omega)
        (by clear * - hoff hl1 hl2 hl3 hl4 hfAnc_bds; omega)
        (by clear * - hoff hl1 hl2 hl3 hl4 hfAnc_bds; omega)
        (by clear * - hne; omega)
        (by clear * - hoff hl1 hl2 hl3 hl4 hfAnc_bds; omega)
      exact h76.trans (h65.trans (h54.trans (h43.trans (h32.trans
        (hfr_dgF _ (Or.inl (by clear * - hoff hl1 hl2 hl3; omega)))))))
    have hrcnt7 : mem7 (b + lsfOffRCount) = S'.R.card := by
      have hlt_hdr : lsfOffRCount < lsfHdrSize := by decide
      have h76 := hmem7_below_aux (b + lsfOffRCount) (by clear * - hlt_hdr hl1 hl2 hl3 hl4 hl5 hl6; omega)
      have h65 := hfr_dgG (b + lsfOffRCount) (Or.inl (by clear * - hlt_hdr hl1; omega))
      have h54 := hfr_ts (b + lsfOffRCount) (Or.inl (by clear * - hlt_hdr hl1 hl2; omega))
      have h43 := hfr_bfs_below_cid (b + lsfOffRCount) (by clear * - hlt_hdr hl1 hl2 hl3 hl4 hfAnc_bds; omega)
      have h3v : mem3 (b + lsfOffRCount) = rCnt + 1 := hmem3_rcnt
      have h73 : mem7 (b + lsfOffRCount) = rCnt + 1 :=
        h76.trans (h65.trans (h54.trans (h43.trans h3v)))
      rw [h73, hrCnt_def, hR', Finset.card_insert_of_notMem hv'_not_R1]
    rcases hhdr1 with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      _, h17, h18, h19, h20, h21, h22, h23⟩
    refine ⟨(hhd_other _ (by decide) (by decide)).trans h0, (hhd_other _ (by decide) (by decide)).trans h1,
      (hhd_other _ (by decide) (by decide)).trans h2, (hhd_other _ (by decide) (by decide)).trans h3,
      (hhd_other _ (by decide) (by decide)).trans h4, (hhd_other _ (by decide) (by decide)).trans h5,
      (hhd_other _ (by decide) (by decide)).trans h6, (hhd_other _ (by decide) (by decide)).trans h7,
      (hhd_other _ (by decide) (by decide)).trans h8, (hhd_other _ (by decide) (by decide)).trans h9,
      (hhd_other _ (by decide) (by decide)).trans h10, (hhd_other _ (by decide) (by decide)).trans h11,
      (hhd_other _ (by decide) (by decide)).trans h12, (hhd_other _ (by decide) (by decide)).trans h13,
      (hhd_other _ (by decide) (by decide)).trans h14, (hhd_other _ (by decide) (by decide)).trans h15,
      hrcnt7, (hhd_other _ (by decide) (by decide)).trans h17,
      (hhd_other _ (by decide) (by decide)).trans h18, (hhd_other _ (by decide) (by decide)).trans h19,
      (hhd_other _ (by decide) (by decide)).trans h20, (hhd_other _ (by decide) (by decide)).trans h21,
      (hhd_other _ (by decide) (by decide)).trans h22, (hhd_other _ (by decide) (by decide)).trans h23⟩
  have hdgG7 : DynGraphAt mem7 (lsfDgGPtr b) x'.vCap x'.eCap S'.G := by
    change DynGraphAt mem7 dgGPtr x1.vCap x1.eCap S'.G
    rw [hx1_vc, hx1_ec]
    have h6' : DynGraphAt mem6 dgGPtr vCap eCap S'.G := by
      simpa only [dgBatchTarget, show (1 : ℕ) ≠ 0 by decide, ↓reduceIte, S', applyLSFUpdate] using hdgG6_raw
    exact h6'.of_agree fun a _ ha2 => hmem7_below_aux a (by clear * - ha2 hl2 hl3 hl4 hl5 hl6; omega)
  have hT7 : TBlockAt mem7 (lsfTBlockPtr b x'.vCap x'.eCap) x'.vCap x'.eCap x'.tM
      S'.G S'.T_cur S'.T₀ S'.π x'.tOrigList := by
    change TBlockAt mem7 (lsfTBlockPtr b x1.vCap x1.eCap) x1.vCap x1.eCap x1.tM S'.G S'.T_cur S'.T₀ S'.π x1.tOrigList
    rw [hx1_vc, hx1_ec, hx1_tM, hx1_tL]
    exact hT5_raw.of_agree fun a ha1 ha2 =>
      (hmem7_below_aux a (by clear * - ha2 hl3 hl4 hl5 hl6; omega)).trans
        (hfr_dgG a (Or.inr (by clear * - ha1 hl2; omega)))
  have hdgF7 : DynGraphAt mem7 (lsfDgFPtr b x'.vCap x'.eCap x'.tM) x'.vCap (fECap x'.eCap x'.n0) S'.RF.F := by
    change DynGraphAt mem7 (lsfDgFPtr b x1.vCap x1.eCap x1.tM) x1.vCap (fECap x1.eCap x1.n0) S'.RF.F
    rw [hx1_vc, hx1_ec, hx1_n0, hx1_tM]
    exact hdgF3.of_agree fun a ha1 ha2 =>
      (hmem7_ge_dgF_below_aux a ha1 (by clear * - ha2 hl4 hl5 hl6; omega)).trans
        (hfr_bfs_below_cid a (by clear * - ha2 hl4 hfAnc_bds; omega))
  have hFAnc7 : FAncAt mem7 (lsfFAncPtr b x'.vCap x'.eCap x'.n0 x'.tM) x'.vCap S'.RF
      x'.rList x'.compId x'.compRoot x'.compSize x'.activeCids :=
    hFAnc4_raw.of_agree fun a ha1 ha2 => by
      change a ≥ lsfFAncPtr b x1.vCap x1.eCap x1.n0 x1.tM at ha1
      change a < lsfFAncPtr b x1.vCap x1.eCap x1.n0 x1.tM + fAncSize x1.vCap at ha2
      rw [hx1_vc, hx1_ec, hx1_n0, hx1_tM] at ha1 ha2
      exact hmem7_ge_dgF_below_aux a (by clear * - ha1 hl4; omega) (by clear * - ha2 hl5 hl6; omega)
  have hW7 : WBlockAt mem7 (lsfWBlockPtr b x'.vCap x'.eCap x'.n0 x'.tM) x'.n0 S'.W_init
      (forestGivenRoots S'.T₀ S'.r₀ (upClosure (hldAuxTree S'.T₀ S'.r₀) S'.r₀ S'.R₀_init) S'.π) :=
    hW1.of_agree fun a ha1 ha2 => by
      change lsfWBlockPtr b x1.vCap x1.eCap x1.n0 x1.tM ≤ a at ha1
      change a < lsfWBlockPtr b x1.vCap x1.eCap x1.n0 x1.tM + wBlockSize x1.n0 at ha2
      rw [hx1_vc, hx1_ec, hx1_n0, hx1_tM] at ha1 ha2
      have h74 := hmem7_ge_dgF_below_aux a (by clear * - ha1 hl4 hl5; omega) (by clear * - ha2 hl6; omega)
      have h43 := hfr_bfs a (fun ⟨_, h2⟩ => by clear * - ha1 h2 hl5 hfAnc_bds; omega)
        (fun ⟨h1, _⟩ => by clear * - ha2 h1 hl6 haux_bds; omega)
      have h32 := hmem3_out a
        (by clear * - ha1 hl5 hfAnc_bds hv'_cap; omega)
        (by clear * - ha1 hl5 hfAnc_bds hrCnt_lt_vc; omega)
        (by clear * - ha1 hl5 hfAnc_bds; omega)
        (by dsimp only [lsfOffRCount]; clear * - ha1 hl4 hl5 hb_lt_dgF; omega)
        (by clear * - ha1 hl5 hfAnc_bds hv'_cap; omega)
      exact h74.trans (h43.trans (h32.trans (hfr_dgF a (Or.inr (by clear * - ha1 hl4 hl5; omega)))))
  have hwstr7 : WstrAt mem7 (lsfWstrNumPtr b x'.vCap x'.eCap x'.n0 x'.tM)
      (lsfWstrDenPtr b x'.vCap x'.eCap x'.n0 x'.tM x'.L_w) x'.eCap x'.h x'.L_w S'.G S'.wstr := by
    have hge_wN : ∀ a, wstrNumPtr ≤ a → mem7 a = mem1 a := fun a ha => by
      have h76 := hmem7_above_aux a (by clear * - ha hl7; omega)
      have h65 := hfr_dgG a (Or.inr (by clear * - ha hl2 hl3 hl4 hl5 hl6 hl7; omega))
      have h54 := hfr_ts a (Or.inr (by clear * - ha hl3 hl4 hl5 hl6 hl7; omega))
      have h43 := hfr_bfs a
        (fun ⟨_, h2⟩ => by clear * - ha h2 hl5 hl6 hl7 hfAnc_bds; omega)
        (fun ⟨_, h2⟩ => by clear * - ha h2 hl7 haux_bds; omega)
      have h32 := hmem3_out a
        (by clear * - ha hl5 hl6 hl7 hfAnc_bds hv'_cap; omega)
        (by clear * - ha hl5 hl6 hl7 hfAnc_bds hrCnt_lt_vc; omega)
        (by clear * - ha hl5 hl6 hl7 hfAnc_bds; omega)
        (by dsimp only [lsfOffRCount]; clear * - ha hl4 hl5 hl6 hl7 hb_lt_dgF; omega)
        (by clear * - ha hl5 hl6 hl7 hfAnc_bds hv'_cap; omega)
      exact h76.trans (h65.trans (h54.trans (h43.trans (h32.trans
        (hfr_dgF a (Or.inr (by clear * - ha hl4 hl5 hl6 hl7; omega)))))))
    have hw1' : WstrAt mem7 (lsfWstrNumPtr b x1.vCap x1.eCap x1.n0 x1.tM)
        (lsfWstrDenPtr b x1.vCap x1.eCap x1.n0 x1.tM x1.L_w) x1.eCap x1.h x1.L_w S₁.G S₁.wstr :=
      hwstr1.of_agree
        (fun a ha1 _ => by
          rw [hx1_vc, hx1_ec, hx1_n0, hx1_tM] at ha1; exact hge_wN a ha1)
        (fun a ha1 _ => by
          rw [hx1_vc, hx1_ec, hx1_n0, hx1_tM, hx1_Lw] at ha1
          exact hge_wN a (by clear * - ha1 hl8; omega))
    exact ⟨hw1'.1, hw1'.2.1, hw1'.2.2⟩
  have hAux7 : AuxAt mem7 (lsfAuxPtr b x'.vCap x'.eCap x'.n0 x'.tM x'.L_w) x'.vCap x'.n0 x'.tM S'
      x'.tOrigList x'.vList x'.t0Parent x'.t0ParentTreeIdx x'.t0Depth x'.thParent x'.upV x'.upMinIdx := by
    -- Only `origBase + v'`, `isOrigBase + v'`, and `[auxQBufABase, auxVisBBase + vCap)` changed in `auxPtr`
    have haux_pre_orig : ∀ a, auxPtr ≤ a → a < origBase → mem7 a = mem1 a := fun a ha1 ha2 => by
      have h76 : mem7 a = mem6 a := by
        dsimp only [mem7]
        rw [Function.update_of_ne (by clear * - ha2 haux_bds; omega),
          Function.update_of_ne (by clear * - ha2; omega)]
      have h65 := hfr_dgG a (Or.inr (by clear * - ha1 hl2 hl3 hl4 hl5 hl6; omega))
      have h54 := hfr_ts a (Or.inr (by clear * - ha1 hl3 hl4 hl5 hl6; omega))
      have h43 := hfr_bfs a
        (fun ⟨_, h2⟩ => by clear * - ha1 h2 hl5 hl6 hfAnc_bds; omega)
        (fun ⟨h1, _⟩ => by clear * - ha2 h1 haux_bds; omega)
      exact h76.trans (h65.trans (h54.trans (h43.trans (hmem3_aux a ha1 (by clear * - ha2 haux_bds; omega)))))
    have hAux1' : AuxAt mem1 auxPtr vCap n0 tM S₁ x1.tOrigList x1.vList
        x1.t0Parent x1.t0ParentTreeIdx x1.t0Depth x1.thParent x1.upV x1.upMinIdx := by
      simpa only [hx1_vc, hx1_ec, hx1_n0, hx1_tM, hx1_Lw] using hAux1
    have hhd_aux : ∀ off < auxHdrSize, mem7 (auxPtr + off) = mem1 (auxPtr + off) := fun off hoff =>
      haux_pre_orig _ (Nat.le_add_right _ _) (by clear * - hoff haux_bds; omega)
    rcases hAux1' with ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13,
      ha14, ha15, ha16, hvlen, hvnd, hvmem, htlen, hvLA, hvIdx, hvIdx0, hr0lt, hr0v, hp, hpe, hd,
      hup, hth, hthR0, hdR0, ht0Edge, hUpProp, hThProp, hIsOrig, hOrig, _⟩
    have hr0_eq : mem7 (auxPtr + auxOffR0Idx) = mem1 (auxPtr + auxOffR0Idx) := hhd_aux _ (by decide)
    have haux_sub_bds :
        auxPtr ≤ auxVIdxBase auxPtr ∧
        auxVIdxBase auxPtr + vCap = auxVListBase auxPtr vCap ∧
        auxVListBase auxPtr vCap + n0 = auxT0ParentBase auxPtr vCap n0 ∧
        auxT0ParentBase auxPtr vCap n0 + n0 = auxT0ParentTreeIdxBase auxPtr vCap n0 ∧
        auxT0ParentTreeIdxBase auxPtr vCap n0 + n0 = auxT0DepthBase auxPtr vCap n0 ∧
        auxT0DepthBase auxPtr vCap n0 + n0 = auxUpVBase auxPtr vCap n0 ∧
        auxUpVBase auxPtr vCap n0 + n0 * auxLogCap n0 = auxUpMinIdxBase auxPtr vCap n0 ∧
        auxUpMinIdxBase auxPtr vCap n0 + n0 * auxLogCap n0 = auxThParentBase auxPtr vCap n0 ∧
        auxThParentBase auxPtr vCap n0 + n0 = origBase := by
      dsimp only [origBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase,
        auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase]
      clear * -; omega
    change AuxAt mem7 (lsfAuxPtr b x1.vCap x1.eCap x1.n0 x1.tM x1.L_w) x1.vCap x1.n0 x1.tM S'
      x1.tOrigList x1.vList x1.t0Parent x1.t0ParentTreeIdx x1.t0Depth x1.thParent x1.upV x1.upMinIdx
    rw [hx1_vc, hx1_ec, hx1_n0, hx1_tM, hx1_Lw]
    change AuxAt mem7 auxPtr vCap n0 tM S'
      x1.tOrigList x1.vList x1.t0Parent x1.t0ParentTreeIdx x1.t0Depth x1.thParent x1.upV x1.upMinIdx
    refine ⟨(hhd_aux _ (by decide)).trans ha0, (hhd_aux _ (by decide)).trans ha1,
      (hhd_aux _ (by decide)).trans ha2, (hhd_aux _ (by decide)).trans ha3,
      (hhd_aux _ (by decide)).trans ha4, (hhd_aux _ (by decide)).trans ha5,
      (hhd_aux _ (by decide)).trans ha6, (hhd_aux _ (by decide)).trans ha7,
      (hhd_aux _ (by decide)).trans ha8, (hhd_aux _ (by decide)).trans ha9,
      (hhd_aux _ (by decide)).trans ha10, (hhd_aux _ (by decide)).trans ha11,
      (hhd_aux _ (by decide)).trans ha12, (hhd_aux _ (by decide)).trans ha13,
      (hhd_aux _ (by decide)).trans ha14, (hhd_aux _ (by decide)).trans ha15,
      (hhd_aux _ (by decide)).trans ha16, hvlen, hvnd, hvmem, htlen,
      fun i hi => (haux_pre_orig _ (by clear * - haux_sub_bds; omega)
        (by clear * - hi hvlen haux_sub_bds; omega)).trans (hvLA i hi),
      fun i hi => (haux_pre_orig _ (by clear * - haux_sub_bds; omega)
        (by have hvlt := hvT_lt1 _ ((hvmem _).mp (List.getElem_mem hi)); rw [hx1_vc] at hvlt
            clear * - hvlt haux_sub_bds; omega)).trans (hvIdx i hi),
      fun u hu huNot => (haux_pre_orig _ (by clear * - haux_sub_bds; omega)
        (by clear * - hu haux_sub_bds; omega)).trans (hvIdx0 u hu huNot),
      hr0_eq ▸ hr0lt, hr0_eq ▸ hr0v,
      fun i hi => by
        rw [haux_pre_orig _ (by clear * - haux_sub_bds; omega) (by clear * - hi haux_sub_bds; omega)]; exact hp i hi,
      fun i hi => by
        rw [haux_pre_orig _ (by clear * - haux_sub_bds; omega) (by clear * - hi haux_sub_bds; omega)]; exact hpe i hi,
      fun i hi => (haux_pre_orig _ (by clear * - haux_sub_bds; omega)
        (by clear * - hi haux_sub_bds; omega)).trans (hd i hi),
      fun i hi j hj => by
        have hij_lt : i * auxLogCap n0 + j < n0 * auxLogCap n0 := by
          calc i * auxLogCap n0 + j < (i + 1) * auxLogCap n0 := by
                clear * - hj; rw [Nat.succ_mul]; omega
            _ ≤ n0 * auxLogCap n0 := Nat.mul_le_mul_right _ hi
        rw [haux_pre_orig _ (by clear * - haux_sub_bds; omega) (by clear * - hij_lt haux_sub_bds; omega),
          haux_pre_orig _ (by clear * - haux_sub_bds; omega) (by clear * - hij_lt haux_sub_bds; omega)]
        exact hup i hi j hj,
      fun i hi => by
        rw [haux_pre_orig _ (by clear * - haux_sub_bds; omega) (by clear * - hi haux_sub_bds; omega)]; exact hth i hi,
      hr0_eq ▸ hthR0, hr0_eq ▸ hdR0, hr0_eq ▸ ht0Edge, hUpProp, hr0_eq ▸ hThProp,
      fun u hu => ?_, fun u hu hu_lt => ?_, fun u hu => ?_⟩
    · -- `isOrigVert[u]`
      by_cases huv' : u = v'
      · subst u
        have hv'_notT : v' ∉ S'.T₀.V := hv'_not_T0
        dsimp only [mem7]; rw [Function.update_self, ite_eq_right hv'_notT]
      · have h41 : mem4 (isOrigBase + u) = mem1 (isOrigBase + u) :=
          (hfr_bfs _ (fun ⟨_, h2⟩ => by clear * - h2 hl5 hl6 hfAnc_bds haux_bds; omega)
            (fun ⟨h1, _⟩ => by clear * - h1 hu haux_bds; omega)).trans
            (hmem3_aux _ (by clear * - haux_bds; omega) (by clear * - hu haux_bds; omega))
        dsimp only [mem7]
        rw [Function.update_of_ne (by clear * - huv'; omega),
          Function.update_of_ne (by clear * - haux_bds hv'_cap; omega),
          hfr_dgG _ (Or.inr (by clear * - hl2 hl3 hl4 hl5 hl6 haux_bds; omega)),
          hfr_ts _ (Or.inr (by clear * - hl3 hl4 hl5 hl6 haux_bds; omega)), h41]
        exact hIsOrig u hu
    · -- `origVert[u]`
      by_cases huv' : u = v'
      · subst u
        dsimp only [mem7]
        rw [Function.update_of_ne (by clear * - haux_bds hv'_cap; omega), Function.update_self]
        exact horig_v'
      · have hu1 : u ∈ S₁.G.V := (Finset.mem_insert.mp hu).resolve_left huv'
        have h41 : mem4 (origBase + u) = mem1 (origBase + u) :=
          (hfr_bfs _ (fun ⟨_, h2⟩ => by clear * - h2 hl5 hl6 hfAnc_bds haux_bds; omega)
            (fun ⟨h1, _⟩ => by clear * - h1 hu_lt haux_bds; omega)).trans
            (hmem3_aux _ (by clear * - haux_bds; omega) (by clear * - hu_lt haux_bds; omega))
        dsimp only [mem7]
        rw [Function.update_of_ne (by clear * - haux_bds hu_lt; omega),
          Function.update_of_ne (by clear * - huv'; omega),
          hfr_dgG _ (Or.inr (by clear * - hl2 hl3 hl4 hl5 hl6 haux_bds; omega)),
          hfr_ts _ (Or.inr (by clear * - hl3 hl4 hl5 hl6 haux_bds; omega)), h41]
        rw [horig_other u huv']; exact hOrig u hu1 hu_lt
    · -- `visA`, `visB` remain `0`
      have hvA7 : mem7 (auxVisABase auxPtr vCap n0 + u) = mem4 (auxVisABase auxPtr vCap n0 + u) := by
        dsimp only [mem7]
        rw [Function.update_of_ne (by clear * - haux_bds hv'_cap; omega),
          Function.update_of_ne (by clear * - haux_bds hv'_cap; omega),
          hfr_dgG _ (Or.inr (by clear * - hl2 hl3 hl4 hl5 hl6 haux_bds; omega)),
          hfr_ts _ (Or.inr (by clear * - hl3 hl4 hl5 hl6 haux_bds; omega))]
      have hvB7 : mem7 (auxVisBBase auxPtr vCap n0 + u) = mem4 (auxVisBBase auxPtr vCap n0 + u) := by
        dsimp only [mem7]
        rw [Function.update_of_ne (by clear * - haux_bds hv'_cap; omega),
          Function.update_of_ne (by clear * - haux_bds hv'_cap; omega),
          hfr_dgG _ (Or.inr (by clear * - hl2 hl3 hl4 hl5 hl6 haux_bds; omega)),
          hfr_ts _ (Or.inr (by clear * - hl3 hl4 hl5 hl6 haux_bds; omega))]
      rw [hvA7, hvB7]; exact hVis4 u hu
  have hrep7 : (LSFRep h).rep b S' x' mem7 :=
    ⟨hxH1, hh1_1, hLin1, hLw1, hkn1, hkeq1, hInv', hn0_1, hm0_1, htM1, hnv1, hme1, htn1,
      hn1_1, hvT_lt1, heG_lt1, hhdr7, hdgG7, hT7, hdgF7, hFAnc7, hW7, hwstr7, hAux7⟩
  exact ⟨hrep7, hfr_all7⟩

end

end MinCostFlow.LSF.Program
