module

public import MinCostFlow.SparseCore.Program.LSFWindowRepackDg
public import MinCostFlow.SparseCore.Program.LSFWindowRepackT
public import MinCostFlow.SparseCore.Program.LSFWindowRepackFAnc
public import MinCostFlow.SparseCore.Program.LSFWindowRepackW
public import MinCostFlow.SparseCore.Program.LSFWindowRepackAux
import WordRAM.Tactic

/-!
# Full Single-Handle Sparse Repack Verification (`LSFWindowRepack`)

Proves `repackOneLSFProc_runs`: given a guest `(LSFRep h).rep h_g S x_g` in host memory shifted by
`guestBase` (at initialization where `S.G.V = S.T₀.V` and `S.G.m ≤ x_g.m0`), `repackOneLSFProc`
repacks the entire handle into fresh zeroed host memory starting at `dst` with host capacities
`(vCap_h, eCap_h, L_w_h)` in time `≤ repackOneLSFCost x_g.n0 x_g.m0 x_g.L_w` (completely
independent of `vCap_h`, `eCap_h`, and `L_w_h`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program
open MinCostFlow.DynSpanner.Program MinCostFlow.Num

/-- Memory after writing the 21 non-zero header words of an `LSFRep` handle at `dst`. -/
private def lsfHdrMem (m : ℕ → ℕ) (dst vCap_h eCap_h n0 m0 tM L_w_h h P_fp L_in rCnt r0 k_nat : ℕ) :
    ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update (Function.update
  (Function.update (Function.update (Function.update (Function.update (Function.update
  (Function.update (Function.update (Function.update (Function.update (Function.update
  (Function.update (Function.update (Function.update (Function.update (Function.update
  (Function.update m
    (dst + lsfOffVCap) vCap_h)
    (dst + lsfOffECap) eCap_h)
    (dst + lsfOffN0) n0)
    (dst + lsfOffM0) m0)
    (dst + lsfOffDgGPtr) (lsfDgGPtr dst))
    (dst + lsfOffTPtr) (lsfTBlockPtr dst vCap_h eCap_h))
    (dst + lsfOffDgFPtr) (lsfDgFPtr dst vCap_h eCap_h tM))
    (dst + lsfOffFAncPtr) (lsfFAncPtr dst vCap_h eCap_h n0 tM))
    (dst + lsfOffWPtr) (lsfWBlockPtr dst vCap_h eCap_h n0 tM))
    (dst + lsfOffWstrNumPtr) (lsfWstrNumPtr dst vCap_h eCap_h n0 tM))
    (dst + lsfOffWstrDenPtr) (lsfWstrDenPtr dst vCap_h eCap_h n0 tM L_w_h))
    (dst + lsfOffLW) L_w_h)
    (dst + lsfOffHLimb) h)
    (dst + lsfOffPFp) P_fp)
    (dst + lsfOffLIn) L_in)
    (dst + lsfOffRCount) rCnt)
    (dst + lsfOffAuxPtr) (lsfAuxPtr dst vCap_h eCap_h n0 tM L_w_h))
    (dst + lsfOffEnd) (lsfEndAddr dst vCap_h eCap_h n0 tM L_w_h))
    (dst + lsfOffR0) r0)
    (dst + lsfOffKNat) k_nat)
    (dst + lsfOffTM) tM

private lemma lsfHdrMem_out {m : ℕ → ℕ}
    {dst vCap_h eCap_h n0 m0 tM L_w_h h P_fp L_in rCnt r0 k_nat a : ℕ}
    (ha : a < dst ∨ dst + lsfHdrSize ≤ a) :
    lsfHdrMem m dst vCap_h eCap_h n0 m0 tM L_w_h h P_fp L_in rCnt r0 k_nat a = m a := by
  have h1 : ∀ k < lsfHdrSize, a ≠ dst + k := fun k hk => by omega
  unfold lsfHdrMem
  repeat rw [Function.update_of_ne (h1 _ (by decide))]

private lemma lsfHdrMem_headerAt {m : ℕ → ℕ} {dst vCap_h eCap_h L_w_h : ℕ}
    {S : LSFState} {x_g : LSFConcrete}
    (hz15 : m (dst + lsfOffThresh) = 0) (hz17 : m (dst + lsfOffNumUpd) = 0)
    (hz23 : m (dst + lsfOffRes) = 0) :
    lsfHeaderAt (lsfHdrMem m dst vCap_h eCap_h x_g.n0 x_g.m0 x_g.tM L_w_h
      x_g.h x_g.P_fp x_g.L_in S.R.card S.r₀ x_g.k_nat) dst S
      { x_g with vCap := vCap_h, eCap := eCap_h, L_w := L_w_h } := by
  have hne : ∀ {j k : ℕ}, j ≠ k → dst + j ≠ dst + k := fun h => by omega
  dsimp only [lsfHeaderAt]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    unfold lsfHdrMem <;>
    repeat (first | exact Function.update_self _ _ _ | exact hz15 | exact hz17 | exact hz23
                  | rw [Function.update_of_ne (hne (by decide))])

private lemma wstrAt_shift {mem : ℕ → ℕ} {guestBase num den eCap h L_w : ℕ}
    {G : MGraph} {wstr : ℕ → ℝ}
    (hW : WstrAt (fun a => mem (guestBase + a)) num den eCap h L_w G wstr) :
    WstrAt mem (guestBase + num) (guestBase + den) eCap h L_w G wstr := by
  rcases hW with ⟨hhL, hL, hE⟩
  refine ⟨hhL, hL, fun e he => ?_⟩
  rcases hE e he with ⟨hlt, hVN, hVD, hIN, hID, hval⟩
  have hN_eq : ∀ i < L_w, mem (guestBase + num + e * L_w + i) =
      mem (guestBase + (num + e * L_w + i)) := fun i _ => by congr 1; omega
  have hD_eq : ∀ i < L_w, mem (guestBase + den + e * L_w + i) =
      mem (guestBase + (den + e * L_w + i)) := fun i _ => by congr 1; omega
  have hVN' : Valid mem (guestBase + num + e * L_w) h L_w := fun i hi => by
    rw [hN_eq i hi]; exact hVN i hi
  have hVD' : Valid mem (guestBase + den + e * L_w) h L_w := fun i hi => by
    rw [hD_eq i hi]; exact hVD i hi
  have hiN : intVal mem (guestBase + num + e * L_w) h L_w =
      intVal (fun a => mem (guestBase + a)) (num + e * L_w) h L_w := intVal_congr hN_eq
  have hiD : intVal mem (guestBase + den + e * L_w) h L_w =
      intVal (fun a => mem (guestBase + a)) (den + e * L_w) h L_w := intVal_congr hD_eq
  rw [hiN, hiD]
  exact ⟨hlt, hVN', hVD', hIN, hID, hval⟩

set_option maxHeartbeats 1200000 in
lemma repackOneLSFProc_runs {w h : ℕ} {p : Program}
    {bRep bCopy bLog : ℕ} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    {guestBase h_g dst vCap_h eCap_h L_w_h : ℕ} {S : LSFState} {x_g : LSFConcrete}
    (hw : 20 < 2 ^ w)
    (hRep : p.HasAt bRep (repackProcs bRep bCopy bLog))
    (hCopy : MeetsContract w p bCopy (memCopyContract w))
    (hLog : MeetsContract w p bLog log2Contract)
    (hMemW : ∀ a, guestBase + h_g ≤ a → a < guestBase + x_g.endAddr h_g → mem a < 2 ^ w)
    (hLSF : (LSFRep h).rep h_g S x_g (fun a => mem (guestBase + a)))
    (hGV_eq : S.G.V = S.T₀.V) (hGm_le : S.G.m ≤ x_g.m0)
    (hvCap : x_g.vCap ≤ vCap_h) (heCap : x_g.eCap ≤ eCap_h) (hLw : x_g.L_w ≤ L_w_h)
    (hsrc_w : guestBase + x_g.endAddr h_g < 2 ^ w)
    (hdst_w : lsfEndAddr dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h < 2 ^ w)
    (hLwh_w : L_w_h < 2 ^ w)
    (hdisj : guestBase + x_g.endAddr h_g ≤ dst)
    (hzero : ∀ a, dst ≤ a → a < lsfEndAddr dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h → mem a = 0) :
    ∃ st' c,
      Runs w p ω
        (repackOneLSFProc bLog (bRep + 0) (bRep + 1) (bRep + 2) (bRep + 3) (bRep + 4) (bRep + 5))
        (startState [guestBase, h_g, dst, vCap_h, eCap_h, L_w_h] mem pos)
        (.returned (lsfEndAddr dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h)) st' c ∧
      (LSFRep h).rep dst S { x_g with vCap := vCap_h, eCap := eCap_h, L_w := L_w_h } st'.mem ∧
      (∀ a, a < dst ∨ lsfEndAddr dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h ≤ a → st'.mem a = mem a) ∧
      c ≤ repackOneLSFCost x_g.n0 x_g.m0 x_g.L_w := by
  set endH := lsfEndAddr dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h
  set x_h : LSFConcrete := { x_g with vCap := vCap_h, eCap := eCap_h, L_w := L_w_h }
  suffices hmain : ∃ o st' c,
      Runs w p ω
        (repackOneLSFProc bLog (bRep + 0) (bRep + 1) (bRep + 2) (bRep + 3) (bRep + 4) (bRep + 5))
        (startState [guestBase, h_g, dst, vCap_h, eCap_h, L_w_h] mem pos) o st' c ∧
      (o = .returned endH ∧ (LSFRep h).rep dst S x_h st'.mem ∧
        (∀ a, a < dst ∨ endH ≤ a → st'.mem a = mem a)) ∧
      c ≤ repackOneLSFCost x_g.n0 x_g.m0 x_g.L_w by
    rcases hmain with ⟨_, st', c, hrun, ⟨rfl, h1, h2⟩, hc⟩
    exact ⟨st', c, hrun, h1, h2, hc⟩
  rcases hLSF with ⟨hxH, hh1, hLin1, hLwg1, hkn1, hkEq, hInv, hn0Eq, hm0Eq, htMEq,
    hn0_le, hm0_le, htM_le, hn0_pos, hvT_lt, heG0_lt,
    hhdrG, hdgG, hT_g, hdgF, hFAnc_g, hW_g, hWstr_g, hAux_g⟩
  have hpDg : p.procs[bRep + 0]? = some repackDynGraphProc :=
    hRep.get (i := 0) (by rw [repackProcs_length]; decide)
  have hpT : p.procs[bRep + 1]? = some (repackTBlockProc bCopy (bRep + 0)) :=
    hRep.get (i := 1) (by rw [repackProcs_length]; decide)
  have hpFAnc : p.procs[bRep + 2]? = some (repackFAncProc bCopy) :=
    hRep.get (i := 2) (by rw [repackProcs_length]; decide)
  have hpW : p.procs[bRep + 3]? = some (repackWBlockProc bCopy) :=
    hRep.get (i := 3) (by rw [repackProcs_length]; decide)
  have hpWstr : p.procs[bRep + 4]? = some (repackWstrProc bCopy) :=
    hRep.get (i := 4) (by rw [repackProcs_length]; decide)
  have hpAux : p.procs[bRep + 5]? = some (repackAuxProc bCopy bLog) :=
    hRep.get (i := 5) (by rw [repackProcs_length]; decide)
  -- Sub-block layout identities at guest and host
  have hg_hdr := lsfHdr_lt_end h_g x_g.vCap x_g.eCap x_g.n0 x_g.tM x_g.L_w
  have hg_dgG := lsfDgG_sub_end h_g x_g.vCap x_g.eCap x_g.n0 x_g.tM x_g.L_w
  have hg_T := lsfTBlock_sub_end h_g x_g.vCap x_g.eCap x_g.n0 x_g.tM x_g.L_w
  have hg_dgF := lsfDgF_sub_end h_g x_g.vCap x_g.eCap x_g.n0 x_g.tM x_g.L_w
  have hg_FAnc := lsfFAnc_sub_end h_g x_g.vCap x_g.eCap x_g.n0 x_g.tM x_g.L_w
  have hg_W := lsfWBlock_sub_end h_g x_g.vCap x_g.eCap x_g.n0 x_g.tM x_g.L_w
  have hg_Wstr := lsfWstr_sub_end h_g x_g.vCap x_g.eCap x_g.n0 x_g.tM x_g.L_w
  have hh_hdr := lsfHdr_lt_end dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h
  have hh_dgG := lsfDgG_sub_end dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h
  have hh_T := lsfTBlock_sub_end dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h
  have hh_dgF := lsfDgF_sub_end dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h
  have hh_FAnc := lsfFAnc_sub_end dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h
  have hh_W := lsfWBlock_sub_end dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h
  have hh_Wstr := lsfWstr_sub_end dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h
  have hend_g : x_g.endAddr h_g = lsfEndAddr h_g x_g.vCap x_g.eCap x_g.n0 x_g.tM x_g.L_w := rfl
  -- Guest header reads in host address space
  have hgh : ∀ off < lsfHdrSize, guestBase + h_g + off < guestBase + x_g.endAddr h_g :=
    fun off hoff => by omega
  have hghW : ∀ off < lsfHdrSize, mem (guestBase + h_g + off) < 2 ^ w :=
    fun off hoff => hMemW _ (by omega) (hgh off hoff)
  rcases hhdrG with ⟨_, _, hgN0, hgM0, hgDgGP, hgTP, hgDgFP, hgFAncP, hgWP, hgWstrNP, hgWstrDP,
    hgLW, hgHLimb, hgPFp, hgLIn, _, hgRCnt, _, hgAuxP, _, hgR0, hgKNat, hgTM, _⟩
  have hGn_eq : S.G.n = x_g.n0 := by
    dsimp [MGraph.n]; rw [hGV_eq, hInv.hTV]; exact hn0Eq
  have hFn_eq : S.RF.F.n = x_g.n0 := by
    dsimp [MGraph.n]; rw [hInv.RF_V_eq]; exact hGn_eq
  have hFm_le : S.RF.F.m ≤ x_g.n0 := by
    have h1 := hInv.RF_E_card_le; dsimp [MGraph.m]; omega
  have hIso_emp : S.isolatedVerts = ∅ := by
    ext v; simp only [Finset.notMem_empty, iff_false]
    intro hv
    have hvG : v ∈ S.G.V := by rw [hInv.hGV_eq]; exact Finset.mem_union_right _ hv
    exact Finset.disjoint_left.mp hInv.hdisj_iso (hGV_eq ▸ hvG) hv
  have hRC_le : S.RF.R.card ≤ x_g.n0 := by
    have h1 : S.R.card = S.R_orig.card + S.isolatedVerts.card := hInv.R_card_eq
    rw [hIso_emp, Finset.card_empty, Nat.add_zero] at h1
    have h2 : S.R_orig.card ≤ S.T₀.V.card := Finset.card_le_card hInv.R_orig_sub
    have h3 : S.T₀.V.card = x_g.n0 := by rw [hInv.hTV]; exact hn0Eq
    change S.R.card ≤ x_g.n0; omega
  have hoffs : lsfOffVCap = 0 ∧ lsfOffECap = 1 ∧ lsfOffN0 = 2 ∧ lsfOffM0 = 3 ∧
      lsfOffDgGPtr = 4 ∧ lsfOffTPtr = 5 ∧ lsfOffDgFPtr = 6 ∧ lsfOffFAncPtr = 7 ∧
      lsfOffWPtr = 8 ∧ lsfOffWstrNumPtr = 9 ∧ lsfOffWstrDenPtr = 10 ∧ lsfOffLW = 11 ∧
      lsfOffHLimb = 12 ∧ lsfOffPFp = 13 ∧ lsfOffLIn = 14 ∧ lsfOffRCount = 16 ∧
      lsfOffAuxPtr = 18 ∧ lsfOffEnd = 19 ∧ lsfOffR0 = 20 ∧ lsfOffKNat = 21 ∧
      lsfOffTM = 22 ∧ lsfHdrSize = 24 ∧ tHdrSize = 8 ∧ fAncHdrSize = 6 ∧ auxHdrSize = 20 := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  -- Key size bounds below 2 ^ w for intermediate expressions
  have hvCap_w : vCap_h < 2 ^ w := by
    dsimp [endH, lsfEndAddr, lsfStaticSize, dynGraphSize] at hdst_w; omega
  have heCap_w : eCap_h < 2 ^ w := by
    dsimp [endH, lsfEndAddr, lsfStaticSize, dynGraphSize] at hdst_w; omega
  have hn0_w : x_g.n0 + 1 < 2 ^ w := by
    dsimp [endH, lsfEndAddr, lsfStaticSize, dynGraphSize] at hdst_w; omega
  have htM_w : x_g.tM < 2 ^ w := by omega
  have hfECap_w : fECap eCap_h x_g.n0 < 2 ^ w := by
    dsimp [endH, lsfEndAddr, lsfStaticSize, dynGraphSize, fECap] at hdst_w ⊢; omega
  have hlogCap_w : auxLogCap x_g.n0 < 2 ^ w := by
    have : 1 * auxLogCap x_g.n0 ≤ x_g.n0 * auxLogCap x_g.n0 :=
      Nat.mul_le_mul_right _ hn0_pos
    dsimp [endH, lsfEndAddr, lsfStaticSize, auxSize] at hdst_w; omega
  have haux_w : auxSize vCap_h x_g.n0 < 2 ^ w := by
    dsimp [endH, lsfEndAddr, lsfStaticSize] at hdst_w; omega
  have hhld_w : hldDepthBound x_g.n0 + 2 < 2 ^ w := by
    dsimp [auxSize] at haux_w; omega
  have hwstrMul_w : eCap_h * L_w_h < 2 ^ w := by
    dsimp [endH, lsfEndAddr, lsfStaticSize] at hdst_w; omega
  have hdgG_sz_w : dynGraphSize vCap_h eCap_h < 2 ^ w := by
    dsimp [endH, lsfEndAddr, lsfStaticSize] at hdst_w; omega
  have htB_sz_w : tBlockSize vCap_h eCap_h x_g.tM < 2 ^ w := by
    dsimp [endH, lsfEndAddr, lsfStaticSize] at hdst_w; omega
  have hdgF_sz_w : dynGraphSize vCap_h (fECap eCap_h x_g.n0) < 2 ^ w := by
    dsimp [endH, lsfEndAddr, lsfStaticSize] at hdst_w; omega
  have hfAnc_sz_w : fAncSize vCap_h < 2 ^ w := by
    dsimp [endH, lsfEndAddr, lsfStaticSize] at hdst_w; omega
  have hwB_sz_w : wBlockSize x_g.n0 < 2 ^ w := by
    dsimp [endH, lsfEndAddr, lsfStaticSize] at hdst_w; omega
  refine runs_start_le ?_
  unfold repackOneLSFProc startState
  refine runs_seq_assign_flat (v := guestBase + h_g) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := x_g.n0) (by
    have hv : mem (guestBase + h_g + lsfOffN0) = x_g.n0 := by simpa [Nat.add_assoc] using hgN0
    eval_expr) ?_
  refine runs_seq_assign_flat (v := x_g.m0) (by
    have hv : mem (guestBase + h_g + lsfOffM0) = x_g.m0 := by simpa [Nat.add_assoc] using hgM0
    have hw0 := hghW lsfOffM0 (by decide)
    eval_expr) ?_
  refine runs_seq_assign_flat (v := x_g.tM) (by
    have hv : mem (guestBase + h_g + lsfOffTM) = x_g.tM := by simpa [Nat.add_assoc] using hgTM
    eval_expr) ?_
  refine runs_seq_assign_flat (v := x_g.L_w) (by
    have hv : mem (guestBase + h_g + lsfOffLW) = x_g.L_w := by simpa [Nat.add_assoc] using hgLW
    eval_expr) ?_
  -- Destination sub-block pointers
  refine runs_seq_assign_flat (v := lsfDgGPtr dst) (by dsimp [lsfDgGPtr]; eval_expr) ?_
  refine runs_seq_assign_flat (v := lsfTBlockPtr dst vCap_h eCap_h) (by
    have h1 : 4 + 7 * vCap_h + 9 * eCap_h = dynGraphSize vCap_h eCap_h := rfl
    have h2 : lsfDgGPtr dst + (4 + 7 * vCap_h + 9 * eCap_h) = lsfTBlockPtr dst vCap_h eCap_h := rfl
    dsimp [dynGraphSize] at hdgG_sz_w; rw [← h2]; eval_expr) ?_
  refine runs_seq_assign_flat (v := lsfDgFPtr dst vCap_h eCap_h x_g.tM) (by
    have h1 : tHdrSize + (4 + 7 * vCap_h + 9 * (2 * x_g.tM + 1)) + 4 * x_g.tM + eCap_h + (4 + 2 * x_g.tM) =
        tBlockSize vCap_h eCap_h x_g.tM := rfl
    have h2 : lsfTBlockPtr dst vCap_h eCap_h +
        (tHdrSize + (4 + 7 * vCap_h + 9 * (2 * x_g.tM + 1)) + 4 * x_g.tM + eCap_h + (4 + 2 * x_g.tM)) =
        lsfDgFPtr dst vCap_h eCap_h x_g.tM := rfl
    dsimp [tBlockSize, dynGraphSize] at htB_sz_w; rw [← h2]; eval_expr) ?_
  refine runs_seq_assign_flat (v := fECap eCap_h x_g.n0) (by dsimp [fECap] at hfECap_w ⊢; eval_expr) ?_
  refine runs_seq_assign_flat (v := lsfFAncPtr dst vCap_h eCap_h x_g.n0 x_g.tM) (by
    have h1 : 4 + 7 * vCap_h + 9 * fECap eCap_h x_g.n0 = dynGraphSize vCap_h (fECap eCap_h x_g.n0) := rfl
    have h2 : lsfDgFPtr dst vCap_h eCap_h x_g.tM + (4 + 7 * vCap_h + 9 * fECap eCap_h x_g.n0) =
        lsfFAncPtr dst vCap_h eCap_h x_g.n0 x_g.tM := rfl
    dsimp [dynGraphSize] at hdgF_sz_w; rw [← h2]; eval_expr) ?_
  refine runs_seq_assign_flat (v := lsfWBlockPtr dst vCap_h eCap_h x_g.n0 x_g.tM) (by
    have h1 : fAncHdrSize + 5 * vCap_h = fAncSize vCap_h := rfl
    have h2 : lsfFAncPtr dst vCap_h eCap_h x_g.n0 x_g.tM + (fAncHdrSize + 5 * vCap_h) =
        lsfWBlockPtr dst vCap_h eCap_h x_g.n0 x_g.tM := rfl
    dsimp [fAncSize] at hfAnc_sz_w; rw [← h2]; eval_expr) ?_
  refine runs_seq_assign_flat (v := lsfAuxPtr dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h) (by
    have h1 : 9 + 5 * x_g.n0 = wBlockSize x_g.n0 := by dsimp [wBlockSize, wHdrSize]; omega
    have h2 : lsfWBlockPtr dst vCap_h eCap_h x_g.n0 x_g.tM + (9 + 5 * x_g.n0) =
        lsfAuxPtr dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h := by
      dsimp [lsfAuxPtr]; rw [h1]
    dsimp [wBlockSize, wHdrSize] at hwB_sz_w; rw [← h2]; eval_expr) ?_
  -- Two bLog calls for auxLogCap and hldDepthBound
  refine runs_seq_call_flat hLog (by eval_expr)
    (by intro v hv; simp at hv; subst hv; omega) ⟨x_g.n0 + 1, rfl, by omega⟩
    (fun rL1 mL1 posL1 hpL1 => ?_)
  rcases hpL1 with ⟨_, haL1, hmL1, hrL1⟩; cases haL1; subst mL1; subst hrL1
  refine runs_seq_assign_flat (v := auxLogCap x_g.n0) (by dsimp [auxLogCap] at hlogCap_w ⊢; eval_expr) ?_
  refine runs_seq_call_flat hLog (by eval_expr)
    (by intro v hv; simp at hv; subst hv; omega) ⟨x_g.n0, rfl, hn0_pos⟩
    (fun rL2 mL2 posL2 hpL2 => ?_)
  rcases hpL2 with ⟨_, haL2, hmL2, hrL2⟩; cases haL2; subst mL2; subst hrL2
  have hlog_le_hld : Nat.log 2 x_g.n0 + 2 ≤ hldDepthBound x_g.n0 := by
    dsimp [hldDepthBound]; exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  refine runs_seq_assign_flat (v := Nat.log 2 x_g.n0 + 1) (by
    have : Nat.log 2 x_g.n0 + 1 < 2 ^ w := by omega
    eval_expr) ?_
  refine runs_seq_assign_flat (v := auxSize vCap_h x_g.n0) (by
    have h1 : (Nat.log 2 x_g.n0 + 1) * (Nat.log 2 x_g.n0 + 1 + 1) = hldDepthBound x_g.n0 := rfl
    have h2 : auxHdrSize + 7 * vCap_h + 5 * x_g.n0 + 2 * (x_g.n0 * auxLogCap x_g.n0) +
        ((Nat.log 2 x_g.n0 + 1) * (Nat.log 2 x_g.n0 + 1 + 1) + 2) + (4 + x_g.n0) =
        auxSize vCap_h x_g.n0 := by dsimp [auxSize]; rw [h1]
    have h3 : Nat.log 2 x_g.n0 + 1 + 1 < 2 ^ w := by omega
    have h4 : (Nat.log 2 x_g.n0 + 1) * (Nat.log 2 x_g.n0 + 1 + 1) < 2 ^ w := by rw [h1]; omega
    have h5 : (Nat.log 2 x_g.n0 + 1) * (Nat.log 2 x_g.n0 + 1 + 1) + 2 < 2 ^ w := by rw [h1]; omega
    dsimp [auxSize] at haux_w; rw [← h2]; eval_expr) ?_
  refine runs_seq_assign_flat (v := lsfWstrNumPtr dst vCap_h eCap_h x_g.n0 x_g.tM) (by
    have h1 : lsfAuxPtr dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h + auxSize vCap_h x_g.n0 =
        lsfWstrNumPtr dst vCap_h eCap_h x_g.n0 x_g.tM := hh_Wstr.2.1
    rw [← h1]; eval_expr) ?_
  refine runs_seq_assign_flat (v := lsfWstrDenPtr dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h) (by
    have h1 : lsfWstrNumPtr dst vCap_h eCap_h x_g.n0 x_g.tM + eCap_h * L_w_h =
        lsfWstrDenPtr dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h := hh_Wstr.2.2.1
    rw [← h1]; eval_expr) ?_
  refine runs_seq_assign_flat (v := endH) (by
    have h1 : lsfWstrDenPtr dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h + eCap_h * L_w_h = endH :=
      hh_Wstr.2.2.2
    rw [← h1]; eval_expr) ?_
  -- Store 21 header words (chunked so memory lookups stay fast)
  refine runs_seq_store_flat (x := dst + lsfOffVCap) (v := vCap_h) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dst + lsfOffECap) (v := eCap_h) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dst + lsfOffN0) (v := x_g.n0) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dst + lsfOffM0) (v := x_g.m0) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dst + lsfOffDgGPtr) (v := lsfDgGPtr dst) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dst + lsfOffTPtr) (v := lsfTBlockPtr dst vCap_h eCap_h) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dst + lsfOffDgFPtr) (v := lsfDgFPtr dst vCap_h eCap_h x_g.tM) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dst + lsfOffFAncPtr) (v := lsfFAncPtr dst vCap_h eCap_h x_g.n0 x_g.tM) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dst + lsfOffWPtr) (v := lsfWBlockPtr dst vCap_h eCap_h x_g.n0 x_g.tM) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dst + lsfOffWstrNumPtr) (v := lsfWstrNumPtr dst vCap_h eCap_h x_g.n0 x_g.tM) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dst + lsfOffWstrDenPtr) (v := lsfWstrDenPtr dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dst + lsfOffLW) (v := L_w_h) (by eval_expr) (by eval_expr) ?_
  set mem12 := Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update mem
      (dst + lsfOffVCap) vCap_h) (dst + lsfOffECap) eCap_h) (dst + lsfOffN0) x_g.n0)
      (dst + lsfOffM0) x_g.m0) (dst + lsfOffDgGPtr) (lsfDgGPtr dst))
      (dst + lsfOffTPtr) (lsfTBlockPtr dst vCap_h eCap_h))
      (dst + lsfOffDgFPtr) (lsfDgFPtr dst vCap_h eCap_h x_g.tM))
      (dst + lsfOffFAncPtr) (lsfFAncPtr dst vCap_h eCap_h x_g.n0 x_g.tM))
      (dst + lsfOffWPtr) (lsfWBlockPtr dst vCap_h eCap_h x_g.n0 x_g.tM))
      (dst + lsfOffWstrNumPtr) (lsfWstrNumPtr dst vCap_h eCap_h x_g.n0 x_g.tM))
      (dst + lsfOffWstrDenPtr) (lsfWstrDenPtr dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h))
      (dst + lsfOffLW) L_w_h
  have hm12_lt : ∀ a < dst, mem12 a = mem a := fun a ha => by
    dsimp only [mem12]; repeat rw [Function.update_of_ne (by omega)]
  refine runs_seq_store_flat (x := dst + lsfOffHLimb) (v := x_g.h) (by eval_expr) (by
    have hlt := hgh lsfOffHLimb (by decide)
    have hw0 := hghW lsfOffHLimb (by decide)
    have hv : mem12 (guestBase + h_g + lsfOffHLimb) = x_g.h := by
      rw [hm12_lt _ (by omega), Nat.add_assoc]; exact hgHLimb
    eval_expr) ?_
  refine runs_seq_store_flat (x := dst + lsfOffPFp) (v := x_g.P_fp) (by eval_expr) (by
    have hlt := hgh lsfOffPFp (by decide)
    have hw0 := hghW lsfOffPFp (by decide)
    have hv : Function.update mem12 (dst + lsfOffHLimb) x_g.h (guestBase + h_g + lsfOffPFp) = x_g.P_fp := by
      rw [Function.update_of_ne (by omega), hm12_lt _ (by omega), Nat.add_assoc]; exact hgPFp
    eval_expr) ?_
  refine runs_seq_store_flat (x := dst + lsfOffLIn) (v := x_g.L_in) (by eval_expr) (by
    have hlt := hgh lsfOffLIn (by decide)
    have hw0 := hghW lsfOffLIn (by decide)
    have hv : Function.update (Function.update mem12 (dst + lsfOffHLimb) x_g.h) (dst + lsfOffPFp) x_g.P_fp
        (guestBase + h_g + lsfOffLIn) = x_g.L_in := by
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hm12_lt _ (by omega), Nat.add_assoc]; exact hgLIn
    eval_expr) ?_
  refine runs_seq_store_flat (x := dst + lsfOffRCount) (v := S.R.card) (by eval_expr) (by
    have hlt := hgh lsfOffRCount (by decide)
    have hw0 := hghW lsfOffRCount (by decide)
    have hv : Function.update (Function.update (Function.update mem12 (dst + lsfOffHLimb) x_g.h)
        (dst + lsfOffPFp) x_g.P_fp) (dst + lsfOffLIn) x_g.L_in
        (guestBase + h_g + lsfOffRCount) = S.R.card := by
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), hm12_lt _ (by omega), Nat.add_assoc]; exact hgRCnt
    eval_expr) ?_
  refine runs_seq_store_flat (x := dst + lsfOffAuxPtr) (v := lsfAuxPtr dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h)
    (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dst + lsfOffEnd) (v := endH) (by eval_expr) (by eval_expr) ?_
  set mem18 := Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update mem12
      (dst + lsfOffHLimb) x_g.h) (dst + lsfOffPFp) x_g.P_fp) (dst + lsfOffLIn) x_g.L_in)
      (dst + lsfOffRCount) S.R.card) (dst + lsfOffAuxPtr) (lsfAuxPtr dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h))
      (dst + lsfOffEnd) endH
  have hm18_lt : ∀ a < dst, mem18 a = mem a := fun a ha => by
    dsimp only [mem18]; repeat rw [Function.update_of_ne (by omega)]
    exact hm12_lt a ha
  refine runs_seq_store_flat (x := dst + lsfOffR0) (v := S.r₀) (by eval_expr) (by
    have hlt := hgh lsfOffR0 (by decide)
    have hw0 := hghW lsfOffR0 (by decide)
    have hv : mem18 (guestBase + h_g + lsfOffR0) = S.r₀ := by
      rw [hm18_lt _ (by omega), Nat.add_assoc]; exact hgR0
    eval_expr) ?_
  refine runs_seq_store_flat (x := dst + lsfOffKNat) (v := x_g.k_nat) (by eval_expr) (by
    have hlt := hgh lsfOffKNat (by decide)
    have hw0 := hghW lsfOffKNat (by decide)
    have hv : Function.update mem18 (dst + lsfOffR0) S.r₀ (guestBase + h_g + lsfOffKNat) = x_g.k_nat := by
      rw [Function.update_of_ne (by omega), hm18_lt _ (by omega), Nat.add_assoc]; exact hgKNat
    eval_expr) ?_
  refine runs_seq_store_flat (x := dst + lsfOffTM) (v := x_g.tM) (by eval_expr) (by eval_expr) ?_
  set mem0 := lsfHdrMem mem dst vCap_h eCap_h x_g.n0 x_g.m0 x_g.tM L_w_h
    x_g.h x_g.P_fp x_g.L_in S.R.card S.r₀ x_g.k_nat
  change ∃ o st' c, Runs w p ω _ ⟨mem0, _, _⟩ o st' c ∧ _
  have hm0_out : ∀ a, a < dst ∨ dst + lsfHdrSize ≤ a → mem0 a = mem a := fun a ha =>
    lsfHdrMem_out ha
  have hm0_hdr : lsfHeaderAt mem0 dst S x_h :=
    lsfHdrMem_headerAt (hzero _ (by omega) (by dsimp [lsfOffThresh]; omega))
      (hzero _ (by omega) (by dsimp [lsfOffNumUpd]; omega))
      (hzero _ (by omega) (by dsimp [lsfOffRes]; omega))
  -- 1. Load srcDgGPtr and repack dgG
  refine runs_seq_assign_flat (v := guestBase + lsfDgGPtr h_g) (by
    have hv : mem0 (guestBase + h_g + lsfOffDgGPtr) = lsfDgGPtr h_g := by
      rw [hm0_out (guestBase + h_g + lsfOffDgGPtr) (Or.inl (by omega)), Nat.add_assoc]; exact hgDgGP
    eval_expr) ?_
  refine runs_seq_call_body_flat
    (P_call := fun _ st1 => DynGraphAt st1.mem (lsfDgGPtr dst) vCap_h eCap_h S.G ∧
      ∀ a, a < lsfDgGPtr dst ∨ lsfDgGPtr dst + dynGraphSize vCap_h eCap_h ≤ a → st1.mem a = mem0 a)
    hpDg (vs := [guestBase + lsfDgGPtr h_g, lsfDgGPtr dst, vCap_h, eCap_h]) (by eval_expr)
    (by
      have hdgG_m0 : DynGraphAt mem0 (guestBase + lsfDgGPtr h_g) x_g.vCap x_g.eCap S.G :=
        (dynGraphAt_shift hdgG).of_agree fun a ha1 ha2 => hm0_out a (Or.inl (by omega))
      obtain ⟨st1, c1, hr1, hdgG1, hfr1, hc1⟩ :=
        repackDynGraphProc_runs (dst := lsfDgGPtr dst) hw
          (fun a ha1 ha2 => by rw [hm0_out a (Or.inl (by omega))]; exact hMemW a (by omega) (by omega))
          hdgG_m0 hvCap heCap (by omega) (by omega) (Or.inl (by omega))
          (fun a ha1 ha2 => (hm0_out a (Or.inr (by omega))).trans (hzero a (by omega) (by omega)))
      exact ⟨0, st1, c1, hr1, ⟨hdgG1, hfr1⟩, hc1⟩)
    (fun _ st1 hP1 => ?_)
  rcases hP1 with ⟨hdgG1, hfr1⟩
  have hm1_lt : ∀ a < dst, st1.mem a = mem a := fun a ha =>
    (hfr1 a (Or.inl (by omega))).trans (hm0_out a (Or.inl ha))
  have hm1_ge : ∀ a, lsfTBlockPtr dst vCap_h eCap_h ≤ a → st1.mem a = mem a := fun a ha =>
    (hfr1 a (Or.inr (by omega))).trans (hm0_out a (Or.inr (by omega)))
  -- 2. Repack TBlock
  refine runs_seq_call_body_flat
    (P_call := fun _ st2 =>
      TBlockAt st2.mem (lsfTBlockPtr dst vCap_h eCap_h) vCap_h eCap_h x_g.tM S.G S.T_cur S.T₀ S.π x_g.tOrigList ∧
      ∀ a, a < lsfTBlockPtr dst vCap_h eCap_h ∨
        lsfTBlockPtr dst vCap_h eCap_h + tBlockSize vCap_h eCap_h x_g.tM ≤ a → st2.mem a = st1.mem a)
    hpT (vs := [guestBase + lsfTBlockPtr h_g x_g.vCap x_g.eCap, lsfTBlockPtr dst vCap_h eCap_h, vCap_h, eCap_h, guestBase])
    (by
      have hv : st1.mem (guestBase + h_g + lsfOffTPtr) = lsfTBlockPtr h_g x_g.vCap x_g.eCap := by
        rw [hm1_lt (guestBase + h_g + lsfOffTPtr) (by omega), Nat.add_assoc]; exact hgTP
      eval_expr)
    (by
      have hT_m1 : TBlockAt (fun a => st1.mem (guestBase + a)) (lsfTBlockPtr h_g x_g.vCap x_g.eCap)
          x_g.vCap x_g.eCap x_g.tM S.G S.T_cur S.T₀ S.π x_g.tOrigList :=
        hT_g.of_agree fun a ha1 ha2 => hm1_lt (guestBase + a) (by omega)
      obtain ⟨st2, c2, hr2, hT2, hfr2, hc2⟩ :=
        repackTBlockProc_runs hw hCopy hpDg
          (fun a ha1 ha2 => by rw [hm1_lt a (by omega)]; exact hMemW a (by omega) (by omega))
          hT_m1 hvCap heCap (by omega) (by omega) (Or.inl (by omega))
          (fun a ha1 ha2 => (hm1_ge a ha1).trans (hzero a (by omega) (by omega)))
      exact ⟨0, st2, c2, hr2, ⟨hT2, hfr2⟩, hc2⟩)
    (fun _ st2 hP2 => ?_)
  rcases hP2 with ⟨hT2, hfr2⟩
  have hm2_lt : ∀ a < dst, st2.mem a = mem a := fun a ha =>
    (hfr2 a (Or.inl (by omega))).trans (hm1_lt a ha)
  have hm2_ge : ∀ a, lsfDgFPtr dst vCap_h eCap_h x_g.tM ≤ a → st2.mem a = mem a := fun a ha =>
    (hfr2 a (Or.inr (by omega))).trans (hm1_ge a (by omega))
  -- 3. Load srcDgFPtr and repack dgF
  refine runs_seq_assign_flat (v := guestBase + lsfDgFPtr h_g x_g.vCap x_g.eCap x_g.tM) (by
    have hv : st2.mem (guestBase + h_g + lsfOffDgFPtr) = lsfDgFPtr h_g x_g.vCap x_g.eCap x_g.tM := by
      rw [hm2_lt (guestBase + h_g + lsfOffDgFPtr) (by omega), Nat.add_assoc]; exact hgDgFP
    eval_expr) ?_
  refine runs_seq_call_body_flat
    (P_call := fun _ st3 =>
      DynGraphAt st3.mem (lsfDgFPtr dst vCap_h eCap_h x_g.tM) vCap_h (fECap eCap_h x_g.n0) S.RF.F ∧
      ∀ a, a < lsfDgFPtr dst vCap_h eCap_h x_g.tM ∨
        lsfDgFPtr dst vCap_h eCap_h x_g.tM + dynGraphSize vCap_h (fECap eCap_h x_g.n0) ≤ a → st3.mem a = st2.mem a)
    hpDg (vs := [guestBase + lsfDgFPtr h_g x_g.vCap x_g.eCap x_g.tM,
      lsfDgFPtr dst vCap_h eCap_h x_g.tM, vCap_h, fECap eCap_h x_g.n0]) (by eval_expr)
    (by
      have hdgF_m2 : DynGraphAt st2.mem (guestBase + lsfDgFPtr h_g x_g.vCap x_g.eCap x_g.tM)
          x_g.vCap (fECap x_g.eCap x_g.n0) S.RF.F :=
        (dynGraphAt_shift hdgF).of_agree fun a ha1 ha2 => hm2_lt a (by omega)
      obtain ⟨st3, c3, hr3, hdgF3, hfr3, hc3⟩ :=
        repackDynGraphProc_runs (dst := lsfDgFPtr dst vCap_h eCap_h x_g.tM)
          (eCap_d := fECap eCap_h x_g.n0) hw
          (fun a ha1 ha2 => by rw [hm2_lt a (by omega)]; exact hMemW a (by omega) (by omega))
          hdgF_m2 hvCap (by dsimp [fECap]; omega) (by omega) (by omega) (Or.inl (by omega))
          (fun a ha1 ha2 => (hm2_ge a ha1).trans (hzero a (by omega) (by omega)))
      exact ⟨0, st3, c3, hr3, ⟨hdgF3, hfr3⟩, hc3⟩)
    (fun _ st3 hP3 => ?_)
  rcases hP3 with ⟨hdgF3, hfr3⟩
  have hm3_lt : ∀ a < dst, st3.mem a = mem a := fun a ha =>
    (hfr3 a (Or.inl (by omega))).trans (hm2_lt a ha)
  have hm3_ge : ∀ a, lsfFAncPtr dst vCap_h eCap_h x_g.n0 x_g.tM ≤ a → st3.mem a = mem a := fun a ha =>
    (hfr3 a (Or.inr (by omega))).trans (hm2_ge a (by omega))
  -- 4. Repack FAnc
  refine runs_seq_call_body_flat
    (P_call := fun _ st4 =>
      FAncAt st4.mem (lsfFAncPtr dst vCap_h eCap_h x_g.n0 x_g.tM) vCap_h S.RF
        x_g.rList x_g.compId x_g.compRoot x_g.compSize x_g.activeCids ∧
      ∀ a, a < lsfFAncPtr dst vCap_h eCap_h x_g.n0 x_g.tM ∨
        lsfFAncPtr dst vCap_h eCap_h x_g.n0 x_g.tM + fAncSize vCap_h ≤ a → st4.mem a = st3.mem a)
    hpFAnc (vs := [guestBase + lsfFAncPtr h_g x_g.vCap x_g.eCap x_g.n0 x_g.tM,
      guestBase + lsfDgFPtr h_g x_g.vCap x_g.eCap x_g.tM,
      lsfFAncPtr dst vCap_h eCap_h x_g.n0 x_g.tM, vCap_h, guestBase])
    (by
      have hv : st3.mem (guestBase + h_g + lsfOffFAncPtr) = lsfFAncPtr h_g x_g.vCap x_g.eCap x_g.n0 x_g.tM := by
        rw [hm3_lt (guestBase + h_g + lsfOffFAncPtr) (by omega), Nat.add_assoc]; exact hgFAncP
      eval_expr)
    (by
      have hFAnc_m3 : FAncAt (fun a => st3.mem (guestBase + a))
          (lsfFAncPtr h_g x_g.vCap x_g.eCap x_g.n0 x_g.tM) x_g.vCap S.RF
          x_g.rList x_g.compId x_g.compRoot x_g.compSize x_g.activeCids :=
        hFAnc_g.of_agree fun a ha1 ha2 => hm3_lt (guestBase + a) (by omega)
      have hdgF_m3 : DynGraphAt (fun a => st3.mem (guestBase + a))
          (lsfDgFPtr h_g x_g.vCap x_g.eCap x_g.tM) x_g.vCap (fECap x_g.eCap x_g.n0) S.RF.F :=
        hdgF.of_agree fun a ha1 ha2 => hm3_lt (guestBase + a) (by omega)
      have hR_sub : S.RF.R ⊆ S.RF.F.V := by
        intro v hv
        rw [hInv.RF_V_eq, hInv.hGV_eq]
        change v ∈ S.R_orig ∪ S.isolatedVerts at hv
        rcases Finset.mem_union.mp hv with hv1 | hv2
        · exact Finset.mem_union_left _ (hInv.R_orig_sub hv1)
        · exact Finset.mem_union_right _ hv2
      obtain ⟨st4, c4, hr4, hFAnc4, hfr4, hc4⟩ :=
        repackFAncProc_runs hw hCopy
          (fun a ha => by
            rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
              · rw [hm3_lt a (by omega)]; exact hMemW a (by omega) (by omega))
          hFAnc_m3 hdgF_m3 hR_sub hvCap (by omega) (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega))
          (fun a ha1 ha2 => (hm3_ge a ha1).trans (hzero a (by omega) (by omega)))
      exact ⟨0, st4, c4, hr4, ⟨hFAnc4, hfr4⟩, hc4⟩)
    (fun _ st4 hP4 => ?_)
  rcases hP4 with ⟨hFAnc4, hfr4⟩
  have hm4_lt : ∀ a < dst, st4.mem a = mem a := fun a ha =>
    (hfr4 a (Or.inl (by omega))).trans (hm3_lt a ha)
  have hm4_ge : ∀ a, lsfWBlockPtr dst vCap_h eCap_h x_g.n0 x_g.tM ≤ a → st4.mem a = mem a := fun a ha =>
    (hfr4 a (Or.inr (by omega))).trans (hm3_ge a (by omega))
  -- 5. Repack WBlock
  refine runs_seq_call_body_flat
    (P_call := fun _ st5 =>
      WBlockAt st5.mem (lsfWBlockPtr dst vCap_h eCap_h x_g.n0 x_g.tM) x_g.n0 S.W_init
        (forestGivenRoots S.T₀ S.r₀ (upClosure (hldAuxTree S.T₀ S.r₀) S.r₀ S.R₀_init) S.π) ∧
      ∀ a, a < lsfWBlockPtr dst vCap_h eCap_h x_g.n0 x_g.tM ∨
        lsfWBlockPtr dst vCap_h eCap_h x_g.n0 x_g.tM + wBlockSize x_g.n0 ≤ a → st5.mem a = st4.mem a)
    hpW (vs := [guestBase + lsfWBlockPtr h_g x_g.vCap x_g.eCap x_g.n0 x_g.tM,
      lsfWBlockPtr dst vCap_h eCap_h x_g.n0 x_g.tM, x_g.n0])
    (by
      have hv : st4.mem (guestBase + h_g + lsfOffWPtr) = lsfWBlockPtr h_g x_g.vCap x_g.eCap x_g.n0 x_g.tM := by
        rw [hm4_lt (guestBase + h_g + lsfOffWPtr) (by omega), Nat.add_assoc]; exact hgWP
      eval_expr)
    (by
      have hW_m4 : WBlockAt (fun a => st4.mem (guestBase + a))
          (lsfWBlockPtr h_g x_g.vCap x_g.eCap x_g.n0 x_g.tM) x_g.n0 S.W_init
          (forestGivenRoots S.T₀ S.r₀ (upClosure (hldAuxTree S.T₀ S.r₀) S.r₀ S.R₀_init) S.π) :=
        hW_g.of_agree fun a ha1 ha2 => hm4_lt (guestBase + a) (by omega)
      obtain ⟨st5, c5, hr5, hW5, hfr5, hc5⟩ :=
        repackWBlockProc_runs (dstW := lsfWBlockPtr dst vCap_h eCap_h x_g.n0 x_g.tM) hw hCopy
          (fun a ha1 ha2 => by rw [hm4_lt a (by omega)]; exact hMemW a (by omega) (by omega))
          hW_m4 (by omega) (by omega) (Or.inl (by omega))
      exact ⟨0, st5, c5, hr5, ⟨hW5, hfr5⟩, hc5⟩)
    (fun _ st5 hP5 => ?_)
  rcases hP5 with ⟨hW5, hfr5⟩
  have hm5_lt : ∀ a < dst, st5.mem a = mem a := fun a ha =>
    (hfr5 a (Or.inl (by omega))).trans (hm4_lt a ha)
  have hm5_ge : ∀ a, lsfAuxPtr dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h ≤ a → st5.mem a = mem a := fun a ha =>
    (hfr5 a (Or.inr (by omega))).trans (hm4_ge a (by omega))
  -- 6. Repack Wstr
  refine runs_seq_call_body_flat
    (P_call := fun _ st6 =>
      WstrAt st6.mem (lsfWstrNumPtr dst vCap_h eCap_h x_g.n0 x_g.tM)
        (lsfWstrDenPtr dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h) eCap_h x_g.h L_w_h S.G S.wstr ∧
      ∀ a, a < lsfWstrNumPtr dst vCap_h eCap_h x_g.n0 x_g.tM ∨
        (lsfWstrNumPtr dst vCap_h eCap_h x_g.n0 x_g.tM + eCap_h * L_w_h ≤ a ∧
          a < lsfWstrDenPtr dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h) ∨
        lsfWstrDenPtr dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h + eCap_h * L_w_h ≤ a → st6.mem a = st5.mem a)
    hpWstr (vs := [guestBase + lsfDgGPtr h_g,
      guestBase + lsfWstrNumPtr h_g x_g.vCap x_g.eCap x_g.n0 x_g.tM,
      guestBase + lsfWstrDenPtr h_g x_g.vCap x_g.eCap x_g.n0 x_g.tM x_g.L_w,
      x_g.L_w,
      lsfWstrNumPtr dst vCap_h eCap_h x_g.n0 x_g.tM,
      lsfWstrDenPtr dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h, L_w_h])
    (by
      have hvN : st5.mem (guestBase + h_g + lsfOffWstrNumPtr) = lsfWstrNumPtr h_g x_g.vCap x_g.eCap x_g.n0 x_g.tM := by
        rw [hm5_lt (guestBase + h_g + lsfOffWstrNumPtr) (by omega), Nat.add_assoc]; exact hgWstrNP
      have hvD : st5.mem (guestBase + h_g + lsfOffWstrDenPtr) = lsfWstrDenPtr h_g x_g.vCap x_g.eCap x_g.n0 x_g.tM x_g.L_w := by
        rw [hm5_lt (guestBase + h_g + lsfOffWstrDenPtr) (by omega), Nat.add_assoc]; exact hgWstrDP
      eval_expr)
    (by
      have hdgG_m5 : DynGraphAt st5.mem (guestBase + lsfDgGPtr h_g) x_g.vCap x_g.eCap S.G :=
        (dynGraphAt_shift hdgG).of_agree fun a ha1 ha2 => hm5_lt a (by omega)
      have hWstr_m5 : WstrAt st5.mem (guestBase + lsfWstrNumPtr h_g x_g.vCap x_g.eCap x_g.n0 x_g.tM)
          (guestBase + lsfWstrDenPtr h_g x_g.vCap x_g.eCap x_g.n0 x_g.tM x_g.L_w)
          x_g.eCap x_g.h x_g.L_w S.G S.wstr :=
        (wstrAt_shift hWstr_g).of_agree
          (fun a ha1 ha2 => hm5_lt a (by omega)) (fun a ha1 ha2 => hm5_lt a (by omega))
      obtain ⟨st6, c6, hr6, hWstr6, hfr6, hc6⟩ :=
        repackWstrProc_runs
          (dstNum := lsfWstrNumPtr dst vCap_h eCap_h x_g.n0 x_g.tM)
          (dstDen := lsfWstrDenPtr dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h)
          hw hCopy (hxH ▸ hh1) hLw heCap hdgG_m5 hWstr_m5
          (by omega) (by omega) (by omega) (by omega) (by omega) hLwh_w
          (by omega) ⟨by omega, by omega, by omega⟩
          (fun a ha1 ha2 => (hm5_ge a (by omega)).trans (hzero a (by omega) (by omega)))
          (fun a ha1 ha2 => (hm5_ge a (by omega)).trans (hzero a (by omega) (by omega)))
      exact ⟨0, st6, c6, hr6, ⟨hWstr6, hfr6⟩, hc6⟩)
    (fun _ st6 hP6 => ?_)
  rcases hP6 with ⟨hWstr6, hfr6⟩
  have hm6_lt : ∀ a < dst, st6.mem a = mem a := fun a ha =>
    (hfr6 a (Or.inl (by omega))).trans (hm5_lt a ha)
  have hm6_aux : ∀ a, lsfAuxPtr dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h ≤ a →
      a < lsfWstrNumPtr dst vCap_h eCap_h x_g.n0 x_g.tM → st6.mem a = mem a := fun a ha1 ha2 =>
    (hfr6 a (Or.inl ha2)).trans (hm5_ge a ha1)
  -- 7. Repack Aux
  refine runs_seq_call_body_flat
    (P_call := fun _ st7 =>
      AuxAt st7.mem (lsfAuxPtr dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h) vCap_h x_g.n0 x_g.tM S
        x_g.tOrigList x_g.vList x_g.t0Parent x_g.t0ParentTreeIdx x_g.t0Depth x_g.thParent x_g.upV x_g.upMinIdx ∧
      ∀ a, a < lsfAuxPtr dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h ∨
        lsfAuxPtr dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h + auxSize vCap_h x_g.n0 ≤ a → st7.mem a = st6.mem a)
    hpAux (vs := [guestBase + lsfAuxPtr h_g x_g.vCap x_g.eCap x_g.n0 x_g.tM x_g.L_w,
      lsfAuxPtr dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h, vCap_h, x_g.n0, guestBase])
    (by
      have hvA : st6.mem (guestBase + h_g + lsfOffAuxPtr) = lsfAuxPtr h_g x_g.vCap x_g.eCap x_g.n0 x_g.tM x_g.L_w := by
        rw [hm6_lt (guestBase + h_g + lsfOffAuxPtr) (by omega), Nat.add_assoc]; exact hgAuxP
      eval_expr)
    (by
      have hAux_m6 : AuxAt (fun a => st6.mem (guestBase + a))
          (lsfAuxPtr h_g x_g.vCap x_g.eCap x_g.n0 x_g.tM x_g.L_w) x_g.vCap x_g.n0 x_g.tM S
          x_g.tOrigList x_g.vList x_g.t0Parent x_g.t0ParentTreeIdx x_g.t0Depth x_g.thParent
          x_g.upV x_g.upMinIdx :=
        hAux_g.of_agree (fun a ha1 ha2 => hm6_lt (guestBase + a) (by omega)) hvT_lt
      obtain ⟨st7, c7, hr7, hAux7, hfr7, hc7⟩ :=
        repackAuxProc_runs (dstAux := lsfAuxPtr dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h) hw hCopy hLog
          (fun a ha1 ha2 => by rw [hm6_lt a (by omega)]; exact hMemW a (by omega) (by omega))
          hAux_m6 hGV_eq hn0_pos hvCap hvT_lt (by omega) (by omega) (Or.inl (by omega))
          (fun a ha1 ha2 => (hm6_aux a ha1 (by omega)).trans (hzero a (by omega) (by omega)))
      exact ⟨0, st7, c7, hr7, ⟨hAux7, hfr7⟩, hc7⟩)
    (fun _ st7 hP7 => ?_)
  rcases hP7 with ⟨hAux7, hfr7⟩
  -- Return endH and assemble (LSFRep h).rep dst S x_h st7.mem
  refine runs_ret_le (by eval_expr) ⟨rfl, ?_, fun a ha => ?_⟩ ?_
  · -- Assemble (LSFRep h).rep dst S x_h st7.mem via of_agree on the 8 disjoint sub-blocks
    have hfr7_lo : ∀ a < lsfAuxPtr dst vCap_h eCap_h x_g.n0 x_g.tM L_w_h, st7.mem a = st6.mem a :=
      fun a ha => hfr7 a (Or.inl ha)
    have hfr6_lo : ∀ a < lsfWstrNumPtr dst vCap_h eCap_h x_g.n0 x_g.tM, st6.mem a = st5.mem a :=
      fun a ha => hfr6 a (Or.inl ha)
    have hfr5_lo : ∀ a < lsfWBlockPtr dst vCap_h eCap_h x_g.n0 x_g.tM, st5.mem a = st4.mem a :=
      fun a ha => hfr5 a (Or.inl ha)
    have hfr4_lo : ∀ a < lsfFAncPtr dst vCap_h eCap_h x_g.n0 x_g.tM, st4.mem a = st3.mem a :=
      fun a ha => hfr4 a (Or.inl ha)
    have hfr3_lo : ∀ a < lsfDgFPtr dst vCap_h eCap_h x_g.tM, st3.mem a = st2.mem a :=
      fun a ha => hfr3 a (Or.inl ha)
    have hfr2_lo : ∀ a < lsfTBlockPtr dst vCap_h eCap_h, st2.mem a = st1.mem a :=
      fun a ha => hfr2 a (Or.inl ha)
    have hfr1_lo : ∀ a < lsfDgGPtr dst, st1.mem a = mem0 a := fun a ha => hfr1 a (Or.inl ha)
    refine ⟨hxH, hh1, hLin1, le_trans hLwg1 hLw, hkn1, hkEq, hInv, hn0Eq, hm0Eq, htMEq,
      le_trans hn0_le hvCap, le_trans hm0_le heCap, htM_le, hn0_pos,
      fun v hv => lt_of_lt_of_le (hvT_lt v hv) hvCap,
      fun e he => lt_of_lt_of_le (heG0_lt e he) heCap,
      hm0_hdr.of_agree fun a _ ha2 =>
        (hfr7_lo a (by omega)).trans ((hfr6_lo a (by omega)).trans ((hfr5_lo a (by omega)).trans
          ((hfr4_lo a (by omega)).trans ((hfr3_lo a (by omega)).trans
            ((hfr2_lo a (by omega)).trans (hfr1_lo a (by omega))))))),
      hdgG1.of_agree fun a _ ha2 =>
        (hfr7_lo a (by omega)).trans ((hfr6_lo a (by omega)).trans ((hfr5_lo a (by omega)).trans
          ((hfr4_lo a (by omega)).trans ((hfr3_lo a (by omega)).trans (hfr2_lo a (by omega)))))),
      hT2.of_agree fun a _ ha2 =>
        (hfr7_lo a (by omega)).trans ((hfr6_lo a (by omega)).trans ((hfr5_lo a (by omega)).trans
          ((hfr4_lo a (by omega)).trans (hfr3_lo a (by omega))))),
      hdgF3.of_agree fun a _ ha2 =>
        (hfr7_lo a (by omega)).trans ((hfr6_lo a (by omega)).trans ((hfr5_lo a (by omega)).trans
          (hfr4_lo a (by omega)))),
      hFAnc4.of_agree fun a _ ha2 =>
        (hfr7_lo a (by omega)).trans ((hfr6_lo a (by omega)).trans (hfr5_lo a (by omega))),
      hW5.of_agree fun a _ ha2 => (hfr7_lo a (by omega)).trans (hfr6_lo a (by omega)),
      hWstr6.of_agree (fun a ha1 _ => hfr7 a (Or.inr (by omega)))
        (fun a ha1 _ => hfr7 a (Or.inr (by omega))),
      hAux7⟩
  · -- Global frame outside [dst, endH)
    rcases ha with hlt | hge
    · exact (hfr7 a (Or.inl (by omega))).trans (hm6_lt a hlt)
    · exact (hfr7 a (Or.inr (by omega))).trans
        ((hfr6 a (Or.inr (Or.inr (by omega)))).trans (hm5_ge a (by omega)))
  · -- Total cost ≤ repackOneLSFCost x_g.n0 x_g.m0 x_g.L_w
    simp only [repackOneLSFCost, log2Contract, List.getD_cons_zero, argsSize, Expr.size]
    have hlog1 : Nat.log 2 (x_g.n0 + 1) ≤ x_g.n0 * auxLogCap x_g.n0 := by
      have h1 : Nat.log 2 (x_g.n0 + 1) ≤ auxLogCap x_g.n0 := Nat.le_succ _
      have h2 : auxLogCap x_g.n0 ≤ x_g.n0 * auxLogCap x_g.n0 := by
        simpa using Nat.mul_le_mul_right (auxLogCap x_g.n0) hn0_pos
      exact le_trans h1 h2
    have hlog2 : Nat.log 2 x_g.n0 ≤ x_g.n0 * auxLogCap x_g.n0 :=
      le_trans (Nat.log_mono_right (Nat.le_succ x_g.n0)) hlog1
    have hmul_w : S.G.m * (40 * x_g.L_w + 70) ≤ 40 * (x_g.m0 * x_g.L_w) + 70 * x_g.m0 := by
      have h1 : S.G.m * (40 * x_g.L_w + 70) ≤ x_g.m0 * (40 * x_g.L_w + 70) :=
        Nat.mul_le_mul_right _ hGm_le
      have h2 : x_g.m0 * (40 * x_g.L_w + 70) = 40 * (x_g.m0 * x_g.L_w) + 70 * x_g.m0 := by ring
      omega
    have h1n : 120 * x_g.n0 * auxLogCap x_g.n0 = 120 * (x_g.n0 * auxLogCap x_g.n0) := by ring
    have h1m : 50 * x_g.m0 * x_g.L_w = 50 * (x_g.m0 * x_g.L_w) := by ring
    omega

end MinCostFlow.SparseCore.Program
