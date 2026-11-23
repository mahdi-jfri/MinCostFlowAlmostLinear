module

public import MinCostFlow.LSF.Program.BatchUpdateOps
public import MinCostFlow.LSF.Program.BatchTBlockSplit
import Mathlib.Tactic.Linarith

/-!
# Vertex-Split Procedure Definitions and Helper Lemmas (`BatchSplitOpBase`)

Defines `lsfSplitUpdateProc`, proves `lsfSplitUpdateProc_noRand`, the post-split `FAncAt`/potential
lemma `split_post_fanc_and_phi`, and the 16-assignment register-loading prefix
`lsfSplitUpdate_prefix`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## Procedure definition -/

/-- Apply one canonical vertex split encoded at `updPtr` (`[b, updPtr]`), returning `5 + kt + kh`. -/
def lsfSplitUpdateProc (idxAddRoot idxDgUpd idxBFS idxTSplit : ℕ) : Stmt :=
  .assign 2 (.load (.bin .add (.reg 0) (.const lsfOffVCap))) ;;
  .assign 3 (.load (.bin .add (.reg 0) (.const lsfOffECap))) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const lsfOffN0))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const lsfOffTM))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const lsfOffDgGPtr))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const lsfOffTPtr))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const lsfOffDgFPtr))) ;;
  .assign 9 (.load (.bin .add (.reg 0) (.const lsfOffFAncPtr))) ;;
  .assign 10 (.load (.bin .add (.reg 0) (.const lsfOffAuxPtr))) ;;
  .assign 11 (.load (.bin .add (.reg 1) (.const 1))) ;;
  .assign 12 (.load (.bin .add (.reg 1) (.const 2))) ;;
  .assign 13 (.load (.bin .add (.reg 1) (.const 3))) ;;
  .assign 14 (.load (.bin .add (.reg 1) (.const 4))) ;;
  .assign 15 (.load (.bin .add (.reg 10) (.const auxOffOrigVertPtr))) ;;
  .assign 16 (.load (.bin .add (.reg 10) (.const auxOffIsOrigVertPtr))) ;;
  .assign 17 (.load (.bin .add (.reg 15) (.reg 11))) ;;
  .call 18 idxAddRoot [.reg 0, .reg 17] ;;
  .assign 18 (.load (.bin .add (.reg 9) (.const fOffIsRootPtr))) ;;
  .assign 19 (.load (.bin .add (.reg 9) (.const fOffRListPtr))) ;;
  .assign 20 (.load (.bin .add (.reg 9) (.const fOffCompIdPtr))) ;;
  .assign 21 (.load (.bin .add (.reg 9) (.const fOffCompSizePtr))) ;;
  .assign 22 (.load (.bin .add (.reg 9) (.const fOffRCount))) ;;
  .assign 23 (.load (.bin .add (.reg 20) (.reg 11))) ;;
  .assign 24 (.load (.bin .add (.reg 21) (.reg 23))) ;;
  .call 25 idxDgUpd [.reg 8, .reg 1, .const 0] ;;
  .store (.bin .add (.reg 18) (.reg 12)) (.const 1) ;;
  .store (.bin .add (.reg 19) (.reg 22)) (.reg 12) ;;
  .store (.bin .add (.reg 9) (.const fOffRCount)) (.bin .add (.reg 22) (.const 1)) ;;
  .store (.bin .add (.reg 0) (.const lsfOffRCount)) (.bin .add (.reg 22) (.const 1)) ;;
  .store (.bin .add (.reg 20) (.reg 12)) (.reg 23) ;;
  .call 25 idxBFS
    [.reg 8, .reg 9, .reg 10, .reg 2,
     .bin .add (.bin .mul (.const 3) (.reg 3)) (.reg 4), .reg 4,
     .reg 11, .reg 12, .reg 23, .reg 11, .reg 12, .bin .add (.reg 24) (.const 1)] ;;
  .call 25 idxTSplit [.reg 7, .reg 1, .reg 2, .reg 3, .reg 5] ;;
  .call 25 idxDgUpd [.reg 6, .reg 1, .const 1] ;;
  .store (.bin .add (.reg 15) (.reg 12)) (.reg 17) ;;
  .store (.bin .add (.reg 16) (.reg 12)) (.const 0) ;;
  .ret (.bin .add (.bin .add (.const 5) (.reg 13)) (.reg 14))

lemma lsfSplitUpdateProc_noRand (idxAddRoot idxDgUpd idxBFS idxTSplit : ℕ) :
    (lsfSplitUpdateProc idxAddRoot idxDgUpd idxBFS idxTSplit).NoRand := by
  dsimp [lsfSplitUpdateProc]; trivial

/-! ## Helper: post-split `LSFRep` and potential drop -/

lemma lsfBlock_disjoint' (b vCap eCap n0 tM L_w : ℕ) :
    b + lsfHdrSize = lsfDgGPtr b ∧
    lsfDgGPtr b + dynGraphSize vCap eCap = lsfTBlockPtr b vCap eCap ∧
    lsfTBlockPtr b vCap eCap + tBlockSize vCap eCap tM = lsfDgFPtr b vCap eCap tM ∧
    lsfDgFPtr b vCap eCap tM + dynGraphSize vCap (fECap eCap n0) = lsfFAncPtr b vCap eCap n0 tM ∧
    lsfFAncPtr b vCap eCap n0 tM + fAncSize vCap = lsfWBlockPtr b vCap eCap n0 tM ∧
    lsfWBlockPtr b vCap eCap n0 tM + wBlockSize n0 = lsfAuxPtr b vCap eCap n0 tM L_w ∧
    lsfAuxPtr b vCap eCap n0 tM L_w + auxSize vCap n0 = lsfWstrNumPtr b vCap eCap n0 tM ∧
    lsfWstrNumPtr b vCap eCap n0 tM + eCap * L_w = lsfWstrDenPtr b vCap eCap n0 tM L_w ∧
    lsfWstrDenPtr b vCap eCap n0 tM L_w + eCap * L_w = lsfEndAddr b vCap eCap n0 tM L_w := by
  dsimp only [lsfDgGPtr, lsfTBlockPtr, lsfDgFPtr, lsfFAncPtr, lsfWBlockPtr,
    lsfAuxPtr, lsfWstrNumPtr, lsfWstrDenPtr, lsfEndAddr, lsfStaticSize]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  omega

lemma runs_seq_of_runs_le' {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {s1 s2 : Stmt} {st st1 : State} {c1 k T : ℕ} {Q : Outcome → State → Prop}
    (h1 : Runs w p ω s1 st .normal st1 c1)
    (h2 : ∃ o st' c2, Runs w p ω s2 st1 o st' c2 ∧ Q o st' ∧ (k + c1 + 1) + c2 ≤ T) :
    ∃ o st' c, Runs w p ω (s1 ;; s2) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases h2 with ⟨o, st', c2, hr2, hQ, hc⟩
  exact ⟨o, st', c1 + c2 + 1, runs_seq_iff.mpr (Or.inr ⟨st1, c1, c2, h1, hr2, rfl⟩), hQ, by omega⟩

lemma sameStatic_endAddr' {b : ℕ} {x x' : LSFConcrete} (hs : SameStaticConcrete x x') :
    x'.endAddr b = x.endAddr b := by
  dsimp only [LSFConcrete.endAddr]
  rw [hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2.2.2.2.1]

open Classical in
/-- Pure post-BFS assembly for a vertex split: builds updated `x'` satisfying `SameStaticConcrete x1 x'`,
`FAncAt` on `S'.RF`, and the exact `phi_drop_split` inequality paying `1100 * mSmall`. -/
lemma split_post_fanc_and_phi
    {w h b v v' oldCid oldSize : ℕ} {St Sh : Finset ℕ}
    {S : LSFState} {x1 : LSFConcrete} {mem1 mem2 mem3 mem4 : ℕ → ℕ}
    (hInv : LSFStructInv S)
    (hu_valid : S.G.UpdateIsValid (.split v v' St Sh))
    (hv'_cap : v' < x1.vCap)
    (hrep1 : (LSFRep h).rep b { S with R₀_base := insert (S.origVert v) S.R₀_base } x1 mem1)
    (holdCid_eq : x1.compId v = oldCid)
    (holdSz_eq : x1.compSize oldCid = oldSize)
    (hmem2_out_dgF : ∀ a, a < lsfDgFPtr b x1.vCap x1.eCap x1.tM ∨
      lsfDgFPtr b x1.vCap x1.eCap x1.tM + dynGraphSize x1.vCap (fECap x1.eCap x1.n0) ≤ a →
      mem2 a = mem1 a)
    (hmem3_def : mem3 = Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update mem2 (fIsRootBase (lsfFAncPtr b x1.vCap x1.eCap x1.n0 x1.tM) + v') 1)
            (fRListBase (lsfFAncPtr b x1.vCap x1.eCap x1.n0 x1.tM) x1.vCap +
              ({ S with R₀_base := insert (S.origVert v) S.R₀_base } : LSFState).R.card) v')
          (lsfFAncPtr b x1.vCap x1.eCap x1.n0 x1.tM + fOffRCount)
          (({ S with R₀_base := insert (S.origVert v) S.R₀_base } : LSFState).R.card + 1))
        (b + lsfOffRCount)
        (({ S with R₀_base := insert (S.origVert v) S.R₀_base } : LSFState).R.card + 1))
      (fCompIdBase (lsfFAncPtr b x1.vCap x1.eCap x1.n0 x1.tM) x1.vCap + v') oldCid)
    (hbfs_post : (splitCompBFSContract w (applyLSFUpdate S (.split v v' St Sh)).RF.F).post
      [lsfDgFPtr b x1.vCap x1.eCap x1.tM, lsfFAncPtr b x1.vCap x1.eCap x1.n0 x1.tM,
       lsfAuxPtr b x1.vCap x1.eCap x1.n0 x1.tM x1.L_w, x1.vCap, fECap x1.eCap x1.n0, x1.n0,
       v, v', oldCid, v, v', oldSize + 1] mem3 0 mem4) :
    let S' : LSFState := applyLSFUpdate S (.split v v' St Sh)
    let mSmall := min
      (S'.RF.F.E.filter fun e => S'.RF.F.Connected (S'.RF.F.tail e) v).card
      (S'.RF.F.E.filter fun e => S'.RF.F.Connected (S'.RF.F.tail e) v').card
    ∃ (compId' compRoot' compSize' : ℕ → ℕ),
      let x' : LSFConcrete :=
        { x1 with
          rList := x1.rList ++ [v']
          compId := compId'
          compRoot := compRoot'
          compSize := compSize'
          activeCids := insert v' x1.activeCids }
      SameStaticConcrete x1 x' ∧
      FAncAt mem4 (lsfFAncPtr b x1.vCap x1.eCap x1.n0 x1.tM) x1.vCap S'.RF
        x'.rList x'.compId x'.compRoot x'.compSize x'.activeCids ∧
      (500 * auxLogCap x1.n0 * (x1.n0 - S'.R_orig.card) + 1400 * S'.RF.F.E.card +
        1100 * ∑ e ∈ S'.RF.F.E, Nat.log 2 (max 1 (x'.compSize (x'.compId (S'.RF.F.tail e)) - 1))) +
        1100 * mSmall ≤
      lsfPhi b x1 mem1 := by
  classical
  intro S' mSmall
  set S₁ : LSFState := { S with R₀_base := insert (S.origVert v) S.R₀_base }
  set vCap := x1.vCap; set eCap := x1.eCap; set n0 := x1.n0; set tM := x1.tM; set L_w := x1.L_w
  set eCapF := fECap eCap n0
  set dgGPtr := lsfDgGPtr b
  set tPtr := lsfTBlockPtr b vCap eCap
  set dgFPtr := lsfDgFPtr b vCap eCap tM
  set fAncPtr := lsfFAncPtr b vCap eCap n0 tM
  set wPtr := lsfWBlockPtr b vCap eCap n0 tM
  set auxPtr := lsfAuxPtr b vCap eCap n0 tM L_w
  rcases lsfBlock_disjoint' b vCap eCap n0 tM L_w with ⟨hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, hl9⟩
  change b + lsfHdrSize = dgGPtr at hl1
  have hb_lt_fAnc : b + 24 ≤ fAncPtr := by dsimp [lsfHdrSize] at hl1; omega
  change dgGPtr + dynGraphSize vCap eCap = tPtr at hl2
  change tPtr + tBlockSize vCap eCap tM = dgFPtr at hl3
  have hb_lt_dgF : b + 24 ≤ dgFPtr := by dsimp [lsfHdrSize] at hl1; omega
  change dgFPtr + dynGraphSize vCap eCapF = fAncPtr at hl4
  change fAncPtr + fAncSize vCap = wPtr at hl5
  change wPtr + wBlockSize n0 = auxPtr at hl6
  have hstep := applyLSFUpdate_split_step hInv hu_valid
  obtain ⟨_, hInv₁, hInv', hRorig', hv_R1, hv'_not_R1, hR', hFres_congr, hv_F', hv'_F', hnot_vv',
    hpart_V, hother_conn, hother_disj, hroots_sep, hsum_eq⟩ := hstep
  have hrep1_copy := hrep1
  rcases hrep1 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hdgF1, hFAnc1, _, _, _⟩
  have hFAnc1_copy := hFAnc1
  rcases hFAnc1 with ⟨hRcnt1, hIsR1, hRL1, hCid1, hCR1, hCS1, _, hrL_len, _, _, _, _, _,
    _, hact_spec, hcid_mem⟩
  have hRF1_sep : ∀ r₁ ∈ S₁.RF.R, ∀ r₂ ∈ S₁.RF.R, r₁ ≠ r₂ → ¬ S₁.RF.F.Connected r₁ r₂ := by
    intro r₁ hr1 r₂ hr2 hne hcc
    obtain ⟨r, _, huniq⟩ := hInv₁.to_RF_spanning.2.2.2.1 r₁ (hInv₁.to_RF_spanning.2.2.1 hr1)
    exact hne ((huniq r₁ ⟨hr1, connected_refl _ _⟩).trans (huniq r₂ ⟨hr2, hcc⟩).symm)
  have hv_F1 : v ∈ S₁.RF.F.V := hInv₁.RF_V_eq ▸ hu_valid.1
  have hv'_not_F1 : v' ∉ S₁.RF.F.V := hInv₁.RF_V_eq ▸ hu_valid.2.1
  have hF'_V_eq : S'.RF.F.V = insert v' S₁.RF.F.V := rfl
  have hF'_E_eq : S'.RF.F.E = S₁.RF.F.E := by
    show (forestGivenRoots S'.T₀ S'.r₀ S'.R_orig S'.π).E = (forestGivenRoots S₁.T₀ S₁.r₀ S₁.R_orig S₁.π).E
    rw [hRorig']; rfl
  have hF'_vCap : ∀ u ∈ S'.RF.F.V, u < vCap := by
    intro u hu; rw [hF'_V_eq, Finset.mem_insert] at hu
    rcases hu with rfl | hu
    · exact hv'_cap
    · exact hdgF1.2.1 u hu
  have hV_sub : S₁.RF.F.V ⊆ S'.RF.F.V := by rw [hF'_V_eq]; exact Finset.subset_insert _ _
  have hR'_sub_V : insert v' S₁.RF.R ⊆ S'.RF.F.V := by
    change insert v' S₁.R ⊆ S'.RF.F.V
    rw [← hR']
    intro u hu
    exact hInv'.RF_V_eq ▸ hInv'.to_RF_spanning.2.2.1 hu
  have hold_act : oldCid ∈ x1.activeCids := by
    obtain ⟨heq, hact, _⟩ := hcid_mem v hv_F1
    rw [heq] at hact
    exact holdCid_eq ▸ hact
  have hcr_v : x1.compRoot oldCid = v := by
    obtain ⟨heq, _, hc_v⟩ := hcid_mem v hv_F1
    rw [heq, holdCid_eq] at hc_v
    have hr_R := (hact_spec oldCid hold_act).2.2.1
    by_contra hne
    exact hRF1_sep _ hr_R _ hv_R1 hne (connected_symm hc_v)
  have holdSz_card : oldSize = (S₁.RF.F.V.filter fun u => S₁.RF.F.Connected u v).card := by
    rw [← holdSz_eq, (hact_spec oldCid hold_act).2.2.2.2.2.2, hcr_v]
  -- mem2 agrees with mem1 on `fAncPtr` and `b`
  have hmem2_fAnc : ∀ a, fAncPtr ≤ a → a < fAncPtr + fAncSize vCap → mem2 a = mem1 a := fun a ha1 _ =>
    hmem2_out_dgF a (Or.inr (by omega))
  have hmem3_fAnc_other : ∀ a, a ≠ fIsRootBase fAncPtr + v' →
      a ≠ fRListBase fAncPtr vCap + S₁.R.card → a ≠ fAncPtr + fOffRCount →
      a ≠ b + lsfOffRCount → a ≠ fCompIdBase fAncPtr vCap + v' → mem3 a = mem2 a := by
    intro a h1 h2 h3 h4 h5
    rw [hmem3_def, Function.update_of_ne h5, Function.update_of_ne h4,
      Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
  have hrCnt_lt_vc : S₁.R.card < vCap := by
    have hsub : S₁.R ⊆ (Finset.range vCap).erase v' := by
      intro x hx
      refine Finset.mem_erase.mpr ⟨fun hEq => hv'_not_R1 (hEq ▸ hx),
        Finset.mem_range.mpr (hdgF1.2.1 x (hInv₁.RF_V_eq ▸ hInv₁.to_RF_spanning.2.2.1 hx))⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hv'_cap), Finset.card_range] at hc
    omega
  have hmid_hdr : mem3 (fAncPtr + fOffRCount) = S₁.RF.R.card + 1 ∧
      mem3 (fAncPtr + fOffIsRootPtr) = fIsRootBase fAncPtr ∧
      mem3 (fAncPtr + fOffRListPtr) = fRListBase fAncPtr vCap ∧
      mem3 (fAncPtr + fOffCompIdPtr) = fCompIdBase fAncPtr vCap ∧
      mem3 (fAncPtr + fOffCompRootPtr) = fCompRootBase fAncPtr vCap ∧
      mem3 (fAncPtr + fOffCompSizePtr) = fCompSizeBase fAncPtr vCap := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hmem3_def,
        Function.update_of_ne (by dsimp [fCompIdBase, fRListBase, fIsRootBase, fOffRCount, fAncHdrSize]; omega),
        Function.update_of_ne (by dsimp [lsfOffRCount, lsfHdrSize, fOffRCount] at *; omega),
        Function.update_self]; rfl
    · exact (hmem3_fAnc_other _ (by dsimp [fIsRootBase, fOffIsRootPtr, fAncHdrSize]; omega)
        (by dsimp [fRListBase, fIsRootBase, fOffIsRootPtr, fAncHdrSize]; omega)
        (by dsimp [fOffIsRootPtr, fOffRCount]; omega)
        (by dsimp [lsfOffRCount, lsfHdrSize, fOffIsRootPtr]; omega)
        (by dsimp [fCompIdBase, fRListBase, fIsRootBase, fOffIsRootPtr, fAncHdrSize]; omega)).trans
        ((hmem2_fAnc _ (by omega) (by dsimp [fAncSize, fOffIsRootPtr, fAncHdrSize]; omega)).trans hIsR1)
    · exact (hmem3_fAnc_other _ (by dsimp [fIsRootBase, fOffRListPtr, fAncHdrSize]; omega)
        (by dsimp [fRListBase, fIsRootBase, fOffRListPtr, fAncHdrSize]; omega)
        (by dsimp [fOffRListPtr, fOffRCount]; omega)
        (by dsimp [lsfOffRCount, lsfHdrSize, fOffRListPtr]; omega)
        (by dsimp [fCompIdBase, fRListBase, fIsRootBase, fOffRListPtr, fAncHdrSize]; omega)).trans
        ((hmem2_fAnc _ (by omega) (by dsimp [fAncSize, fOffRListPtr, fAncHdrSize]; omega)).trans hRL1)
    · exact (hmem3_fAnc_other _ (by dsimp [fIsRootBase, fOffCompIdPtr, fAncHdrSize]; omega)
        (by dsimp [fRListBase, fIsRootBase, fOffCompIdPtr, fAncHdrSize]; omega)
        (by dsimp [fOffCompIdPtr, fOffRCount]; omega)
        (by dsimp [lsfOffRCount, lsfHdrSize, fOffCompIdPtr]; omega)
        (by dsimp [fCompIdBase, fRListBase, fIsRootBase, fOffCompIdPtr, fAncHdrSize]; omega)).trans
        ((hmem2_fAnc _ (by omega) (by dsimp [fAncSize, fOffCompIdPtr, fAncHdrSize]; omega)).trans hCid1)
    · exact (hmem3_fAnc_other _ (by dsimp [fIsRootBase, fOffCompRootPtr, fAncHdrSize]; omega)
        (by dsimp [fRListBase, fIsRootBase, fOffCompRootPtr, fAncHdrSize]; omega)
        (by dsimp [fOffCompRootPtr, fOffRCount]; omega)
        (by dsimp [lsfOffRCount, lsfHdrSize, fOffCompRootPtr]; omega)
        (by dsimp [fCompIdBase, fRListBase, fIsRootBase, fOffCompRootPtr, fAncHdrSize]; omega)).trans
        ((hmem2_fAnc _ (by omega) (by dsimp [fAncSize, fOffCompRootPtr, fAncHdrSize]; omega)).trans hCR1)
    · exact (hmem3_fAnc_other _ (by dsimp [fIsRootBase, fOffCompSizePtr, fAncHdrSize]; omega)
        (by dsimp [fRListBase, fIsRootBase, fOffCompSizePtr, fAncHdrSize]; omega)
        (by dsimp [fOffCompSizePtr, fOffRCount]; omega)
        (by dsimp [lsfOffRCount, lsfHdrSize, fOffCompSizePtr]; omega)
        (by dsimp [fCompIdBase, fRListBase, fIsRootBase, fOffCompSizePtr, fAncHdrSize]; omega)).trans
        ((hmem2_fAnc _ (by omega) (by dsimp [fAncSize, fOffCompSizePtr, fAncHdrSize]; omega)).trans hCS1)
  have hmid_isRoot : ∀ u < vCap,
      mem3 (fIsRootBase fAncPtr + u) = if u = v' then 1 else mem1 (fIsRootBase fAncPtr + u) := by
    intro u hu
    by_cases huv' : u = v'
    · subst huv'; simp only [↓reduceIte]
      rw [hmem3_def,
        Function.update_of_ne (by dsimp [fCompIdBase, fRListBase, fIsRootBase]; omega),
        Function.update_of_ne (by dsimp [lsfOffRCount, lsfHdrSize, fIsRootBase]; omega),
        Function.update_of_ne (by dsimp [fOffRCount, fIsRootBase, fAncHdrSize]; omega),
        Function.update_of_ne (by dsimp [fRListBase, fIsRootBase]; omega),
        Function.update_self]
    · simp only [huv', ↓reduceIte]
      exact (hmem3_fAnc_other _ (by omega) (by dsimp [fRListBase, fIsRootBase]; omega)
        (by dsimp [fOffRCount, fIsRootBase, fAncHdrSize]; omega)
        (by dsimp [lsfOffRCount, lsfHdrSize, fIsRootBase]; omega)
        (by dsimp [fCompIdBase, fRListBase, fIsRootBase]; omega)).trans
        (hmem2_fAnc _ (by dsimp [fIsRootBase]; omega) (by dsimp [fIsRootBase, fAncSize]; omega))
  have hrL_len' : x1.rList.length = S₁.R.card := hrL_len
  have hmid_rList : (∀ i < x1.rList.length,
        mem3 (fRListBase fAncPtr vCap + i) = mem1 (fRListBase fAncPtr vCap + i)) ∧
      mem3 (fRListBase fAncPtr vCap + x1.rList.length) = v' := by
    refine ⟨fun i hi => ?_, ?_⟩
    · exact (hmem3_fAnc_other _ (by dsimp [fRListBase, fIsRootBase]; omega)
        (by omega) (by dsimp [fOffRCount, fRListBase, fIsRootBase, fAncHdrSize]; omega)
        (by dsimp [lsfOffRCount, lsfHdrSize, fRListBase, fIsRootBase]; omega)
        (by dsimp [fCompIdBase, fRListBase]; omega)).trans
        (hmem2_fAnc _ (by dsimp [fRListBase, fIsRootBase]; omega)
          (by dsimp [fRListBase, fIsRootBase, fAncSize]; omega))
    · rw [hrL_len']
      rw [hmem3_def,
        Function.update_of_ne (by dsimp [fCompIdBase, fRListBase]; omega),
        Function.update_of_ne (by dsimp [lsfOffRCount, lsfHdrSize, fRListBase, fIsRootBase]; omega),
        Function.update_of_ne (by dsimp [fOffRCount, fRListBase, fIsRootBase, fAncHdrSize]; omega),
        Function.update_self]
  have hmid_compId : ∀ u < vCap,
      mem3 (fCompIdBase fAncPtr vCap + u) = if u = v' then oldCid else mem1 (fCompIdBase fAncPtr vCap + u) := by
    intro u hu
    by_cases huv' : u = v'
    · subst huv'; simp only [↓reduceIte]; rw [hmem3_def, Function.update_self]
    · simp only [huv', ↓reduceIte]
      exact (hmem3_fAnc_other _ (by dsimp [fCompIdBase, fRListBase, fIsRootBase]; omega)
        (by dsimp [fCompIdBase, fRListBase]; omega)
        (by dsimp [fOffRCount, fCompIdBase, fRListBase, fIsRootBase, fAncHdrSize]; omega)
        (by dsimp [lsfOffRCount, lsfHdrSize, fCompIdBase, fRListBase, fIsRootBase]; omega)
        (by omega)).trans
        (hmem2_fAnc _ (by dsimp [fCompIdBase, fRListBase, fIsRootBase]; omega)
          (by dsimp [fCompIdBase, fRListBase, fIsRootBase, fAncSize]; omega))
  have hmid_compRoot : ∀ c < vCap,
      mem3 (fCompRootBase fAncPtr vCap + c) = mem1 (fCompRootBase fAncPtr vCap + c) := fun c hc =>
    (hmem3_fAnc_other _ (by dsimp [fCompRootBase, fCompIdBase, fRListBase, fIsRootBase]; omega)
      (by dsimp [fCompRootBase, fCompIdBase, fRListBase]; omega)
      (by dsimp [fOffRCount, fCompRootBase, fCompIdBase, fRListBase, fIsRootBase, fAncHdrSize]; omega)
      (by dsimp [lsfOffRCount, lsfHdrSize, fCompRootBase, fCompIdBase, fRListBase, fIsRootBase]; omega)
      (by dsimp [fCompRootBase, fCompIdBase]; omega)).trans
      (hmem2_fAnc _ (by dsimp [fCompRootBase, fCompIdBase, fRListBase, fIsRootBase]; omega)
        (by dsimp [fCompRootBase, fCompIdBase, fRListBase, fIsRootBase, fAncSize]; omega))
  have hmid_compSize : ∀ c < vCap,
      mem3 (fCompSizeBase fAncPtr vCap + c) = mem1 (fCompSizeBase fAncPtr vCap + c) := fun c hc =>
    (hmem3_fAnc_other _ (by dsimp [fCompSizeBase, fCompRootBase, fCompIdBase, fRListBase, fIsRootBase]; omega)
      (by dsimp [fCompSizeBase, fCompRootBase, fCompIdBase, fRListBase]; omega)
      (by dsimp [fOffRCount, fCompSizeBase, fCompRootBase, fCompIdBase, fRListBase, fIsRootBase, fAncHdrSize]; omega)
      (by dsimp [lsfOffRCount, lsfHdrSize, fCompSizeBase, fCompRootBase, fCompIdBase, fRListBase, fIsRootBase]; omega)
      (by dsimp [fCompSizeBase, fCompRootBase, fCompIdBase]; omega)).trans
      (hmem2_fAnc _ (by dsimp [fCompSizeBase, fCompRootBase, fCompIdBase, fRListBase, fIsRootBase]; omega)
        (by dsimp [fCompSizeBase, fCompRootBase, fCompIdBase, fRListBase, fIsRootBase, fAncSize]; omega))
  have hcs_le_qA : fCompSizeBase fAncPtr vCap + vCap ≤ auxQBufABase auxPtr vCap n0 := by
    have h1 : fCompSizeBase fAncPtr vCap + vCap = fAncPtr + fAncSize vCap := by
      dsimp [fCompSizeBase, fCompRootBase, fCompIdBase, fRListBase, fIsRootBase, fAncSize]; omega
    have h2 : auxPtr ≤ auxQBufABase auxPtr vCap n0 := by
      dsimp [auxQBufABase, auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase,
        auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase]
      omega
    omega
  obtain ⟨compId', compRoot', compSize', Csmall, Cbig, hCpair, hCle, hFAnc_raw,
    _, hsz'_Cs, hsz'_Cb, hsz'_oth⟩ :=
    fancAt_after_splitCompBFS hFAnc1_copy hRF1_sep hF'_vCap hV_sub hR'_sub_V
      hv'_not_R1 hv'_cap hv'_F' hv_F' hold_act hcr_v hv_F' hv'_F' hnot_vv'
      hpart_V hother_conn hother_disj hroots_sep
      hmid_hdr hmid_isRoot hmid_rList hmid_compId hmid_compRoot hmid_compSize
      hbfs_post hcs_le_qA
  have hRF'_eq : ({ F := S'.RF.F, R := insert v' S₁.RF.R } : RootedForest) = S'.RF := by
    cases h : S'.RF with
    | mk F' R' =>
      have hR_eq : insert v' S₁.RF.R = R' := by
        have : S'.RF.R = insert v' S₁.RF.R := hR'; rw [h] at this; exact this.symm
      simp [hR_eq]
  have hFAnc4 : FAncAt mem4 fAncPtr vCap S'.RF (x1.rList ++ [v']) compId' compRoot' compSize'
      (insert v' x1.activeCids) := hRF'_eq ▸ hFAnc_raw
  -- Potential drop via `phi_drop_split`
  set E_small := S'.RF.F.E.filter fun e => S'.RF.F.tail e ∈ Csmall
  have hEs_card : E_small.card = mSmall := by
    have hcard_Cs : Csmall.card = E_small.card + 1 := by
      rcases hCpair with ⟨hCs, _⟩ | ⟨hCs, _⟩
      · have hEs_eq : E_small = S'.RF.F.E.filter fun e => S'.RF.F.Connected (S'.RF.F.tail e) v := by
          ext e; simp only [E_small, hCs, Finset.mem_filter]
          exact ⟨fun ⟨he, _, hc⟩ => ⟨he, hc⟩, fun ⟨he, hc⟩ => ⟨he, (hInv'.to_RF_spanning.1.1 e he).1, hc⟩⟩
        rw [hCs, hEs_eq]; exact forest_comp_card_eq_edges_succ hInv'.to_RF_spanning.1 hv_F'
      · have hEs_eq : E_small = S'.RF.F.E.filter fun e => S'.RF.F.Connected (S'.RF.F.tail e) v' := by
          ext e; simp only [E_small, hCs, Finset.mem_filter]
          exact ⟨fun ⟨he, _, hc⟩ => ⟨he, hc⟩, fun ⟨he, hc⟩ => ⟨he, (hInv'.to_RF_spanning.1.1 e he).1, hc⟩⟩
        rw [hCs, hEs_eq]; exact forest_comp_card_eq_edges_succ hInv'.to_RF_spanning.1 hv'_F'
    have hEA_card : (S'.RF.F.V.filter fun u => S'.RF.F.Connected u v).card =
        (S'.RF.F.E.filter fun e => S'.RF.F.Connected (S'.RF.F.tail e) v).card + 1 :=
      forest_comp_card_eq_edges_succ hInv'.to_RF_spanning.1 hv_F'
    have hEB_card : (S'.RF.F.V.filter fun u => S'.RF.F.Connected u v').card =
        (S'.RF.F.E.filter fun e => S'.RF.F.Connected (S'.RF.F.tail e) v').card + 1 :=
      forest_comp_card_eq_edges_succ hInv'.to_RF_spanning.1 hv'_F'
    rcases hCpair with ⟨hCs, hCb⟩ | ⟨hCs, hCb⟩
    · have hle : (S'.RF.F.E.filter fun e => S'.RF.F.Connected (S'.RF.F.tail e) v).card ≤
          (S'.RF.F.E.filter fun e => S'.RF.F.Connected (S'.RF.F.tail e) v').card := by
        rw [hCs, hCb, hEA_card, hEB_card] at hCle; omega
      have hm : mSmall = (S'.RF.F.E.filter fun e => S'.RF.F.Connected (S'.RF.F.tail e) v).card :=
        Nat.min_eq_left hle
      rw [hCs, hEA_card] at hcard_Cs
      exact (Nat.succ.inj hcard_Cs).symm.trans hm.symm
    · have hle : (S'.RF.F.E.filter fun e => S'.RF.F.Connected (S'.RF.F.tail e) v').card ≤
          (S'.RF.F.E.filter fun e => S'.RF.F.Connected (S'.RF.F.tail e) v).card := by
        rw [hCs, hCb, hEA_card, hEB_card] at hCle; omega
      have hm : mSmall = (S'.RF.F.E.filter fun e => S'.RF.F.Connected (S'.RF.F.tail e) v').card :=
        Nat.min_eq_right hle
      rw [hCs, hEB_card] at hcard_Cs
      exact (Nat.succ.inj hcard_Cs).symm.trans hm.symm
  have hsum_CsCb : Csmall.card + Cbig.card = oldSize + 1 := by
    rw [holdSz_card, hsum_eq]
    rcases hCpair with ⟨hCs, hCb⟩ | ⟨hCs, hCb⟩
    · rw [hCs, hCb]
    · rw [hCs, hCb, Nat.add_comm]
  have hCs_ge1 : 1 ≤ Csmall.card := by
    rcases hCpair with ⟨hCs, _⟩ | ⟨hCs, _⟩
    · rw [hCs]; exact Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨hv_F', connected_refl _ v⟩⟩
    · rw [hCs]; exact Finset.card_pos.mpr ⟨v', Finset.mem_filter.mpr ⟨hv'_F', connected_refl _ v'⟩⟩
  have hcid_of_conn : ∀ u ∈ S₁.RF.F.V, S₁.RF.F.Connected u v → x1.compId u = oldCid := by
    intro u hu hcc_v
    obtain ⟨heq, hact, hcc⟩ := hcid_mem u hu
    rw [heq] at hact hcc
    have hcr_eq : x1.compRoot (x1.compId u) = v := by
      by_contra hne
      exact hRF1_sep _ (hact_spec _ hact).2.2.1 _ hv_R1 hne (connected_trans (connected_symm hcc) hcc_v)
    have h1' := (hact_spec _ hact).2.2.2.1
    rw [hcr_eq] at h1'; exact h1'.symm.trans holdCid_eq
  have htail_rel : ∀ e ∈ S'.RF.F.E,
      (S'.RF.F.tail e = v' ∧ S₁.RF.F.tail e = v) ∨ S'.RF.F.tail e = S₁.RF.F.tail e := by
    intro e he
    have hteq : S'.RF.F.tail e =
        (S₁.RF.F.applyUpdate (.split v v' (St ∩ S₁.RF.F.E) (Sh ∩ S₁.RF.F.E))).tail e :=
      (hFres_congr.2.2 e (hFres_congr.2.1.symm ▸ he)).1.symm
    rw [hteq]
    dsimp only [MGraph.applyUpdate]
    split_ifs with h
    · exact Or.inl ⟨rfl, h.2⟩
    · exact Or.inr rfl
  have hold_sz_of_in : ∀ e ∈ S'.RF.F.E,
      (S'.RF.F.Connected (S'.RF.F.tail e) v ∨ S'.RF.F.Connected (S'.RF.F.tail e) v') →
      x1.compSize (x1.compId (S₁.RF.F.tail e)) = oldSize := by
    intro e he hconn
    have huF' := (hInv'.to_RF_spanning.1.1 e he).1
    rcases htail_rel e he with ⟨_, h1⟩ | hEq
    · rw [h1, holdCid_eq, holdSz_eq]
    · rcases (hpart_V _ huF').mp hconn with hv'e | ⟨hu1, hcc1⟩
      · exfalso; exact hv'_not_F1 (hv'e ▸ hEq ▸ (hInv₁.to_RF_spanning.1.1 e (hF'_E_eq ▸ he)).1)
      · rw [← hEq, hcid_of_conn _ hu1 hcc1, holdSz_eq]
  have hmono : ∀ e ∈ S'.RF.F.E,
      compSize' (compId' (S'.RF.F.tail e)) ≤ x1.compSize (x1.compId (S₁.RF.F.tail e)) := by
    intro e he
    have huF' := (hInv'.to_RF_spanning.1.1 e he).1
    by_cases huS : S'.RF.F.tail e ∈ Csmall
    · have hconn : S'.RF.F.Connected (S'.RF.F.tail e) v ∨ S'.RF.F.Connected (S'.RF.F.tail e) v' := by
        rcases hCpair with ⟨hCs, _⟩ | ⟨hCs, _⟩ <;> rw [hCs] at huS
        · exact Or.inl (Finset.mem_filter.mp huS).2
        · exact Or.inr (Finset.mem_filter.mp huS).2
      rw [(hsz'_Cs _ huF' huS).1, hold_sz_of_in e he hconn]; omega
    · by_cases huB : S'.RF.F.tail e ∈ Cbig
      · have hconn : S'.RF.F.Connected (S'.RF.F.tail e) v ∨ S'.RF.F.Connected (S'.RF.F.tail e) v' := by
          rcases hCpair with ⟨_, hCb⟩ | ⟨_, hCb⟩ <;> rw [hCb] at huB
          · exact Or.inr (Finset.mem_filter.mp huB).2
          · exact Or.inl (Finset.mem_filter.mp huB).2
        rw [hsz'_Cb _ huF' huB, hold_sz_of_in e he hconn]; omega
      · have hnot_v' : S'.RF.F.tail e ≠ v' := by
          intro hEq
          rcases hCpair with ⟨hCs, hCb⟩ | ⟨hCs, hCb⟩
          · exact huB (by rw [hEq, hCb]; exact Finset.mem_filter.mpr ⟨hv'_F', connected_refl _ v'⟩)
          · exact huS (by rw [hEq, hCs]; exact Finset.mem_filter.mpr ⟨hv'_F', connected_refl _ v'⟩)
        have hEq : S'.RF.F.tail e = S₁.RF.F.tail e := (htail_rel e he).resolve_left fun h => hnot_v' h.1
        rw [(hsz'_oth _ huF' huS huB).2, hEq]
  have hdrop : ∀ e ∈ E_small,
      2 ≤ compSize' (compId' (S'.RF.F.tail e)) ∧
      2 * (compSize' (compId' (S'.RF.F.tail e)) - 1) ≤ x1.compSize (x1.compId (S₁.RF.F.tail e)) - 1 := by
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
    have hconn : S'.RF.F.Connected (S'.RF.F.tail e) v ∨ S'.RF.F.Connected (S'.RF.F.tail e) v' := by
      rcases hCpair with ⟨hCs, _⟩ | ⟨hCs, _⟩ <;> rw [hCs] at huS
      · exact Or.inl (Finset.mem_filter.mp huS).2
      · exact Or.inr (Finset.mem_filter.mp huS).2
    rw [(hsz'_Cs _ huF' huS).1, hold_sz_of_in e heF' hconn]
    exact ⟨hCs_ge2, by omega⟩
  refine ⟨compId', compRoot', compSize', ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩, hFAnc4, ?_⟩
  rw [lsfPhi_eq_semantic hrep1_copy, ← hRorig', ← hF'_E_eq, ← hEs_card]
  exact phi_drop_split (Finset.filter_subset _ _) hmono hdrop

/-! ## Verification of `lsfSplitUpdateProc` -/

lemma step_assign_load {w r x v T : ℕ} {p : Program} {ω : ℕ → Bool} {eAddr : Expr} {s : Stmt}
    {st : State} {Q : Outcome → State → Prop}
    (he : eAddr.eval w st = some x) (hm : st.mem x = v)
    (hs : ∃ o st' c, Runs w p ω s { st with regs := Function.update st.regs r v } o st' c ∧
      Q o st' ∧ c ≤ T) :
    ∃ o st' c, Runs w p ω (.assign r (.load eAddr) ;; s) st o st' c ∧
      Q o st' ∧ c ≤ T + eAddr.size + 4 := by
  have h := runs_seq_assign_le (k := 0) (T := T + eAddr.size + 4) (Q := Q)
    (Expr.eval_load_of_eq he hm) (by
      rcases hs with ⟨o, st', c, hrun, hQ, hc⟩
      exact ⟨o, st', c, hrun, hQ, by dsimp only [Expr.size]; omega⟩)
  rcases h with ⟨o, st', c, hrun, hQ, hc⟩
  exact ⟨o, st', c, hrun, hQ, by omega⟩

lemma lsfSplitUpdate_prefix {w b updPtr vCap eCap n0 tM dgGPtr tPtr dgFPtr fAncPtr
    auxPtr v v' kt kh origBase isOrigBase vOrig T : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {pos : ℕ} {rest : Stmt}
    {Q : Outcome → State → Prop}
    (hb_off : ∀ k < lsfHdrSize, k < 2 ^ w ∧ b + k < 2 ^ w)
    (hu_off : ∀ k ≤ 4, k < 2 ^ w ∧ updPtr + k < 2 ^ w)
    (ha_off : ∀ k < auxHdrSize, k < 2 ^ w ∧ auxPtr + k < 2 ^ w)
    (horig_v : origBase + v < 2 ^ w)
    (hvc : mem (b + lsfOffVCap) = vCap) (hec : mem (b + lsfOffECap) = eCap)
    (hn0 : mem (b + lsfOffN0) = n0) (htM : mem (b + lsfOffTM) = tM)
    (hdgG : mem (b + lsfOffDgGPtr) = dgGPtr) (htP : mem (b + lsfOffTPtr) = tPtr)
    (hdgF : mem (b + lsfOffDgFPtr) = dgFPtr) (hfA : mem (b + lsfOffFAncPtr) = fAncPtr)
    (haux : mem (b + lsfOffAuxPtr) = auxPtr)
    (hv : mem (updPtr + 1) = v) (hv' : mem (updPtr + 2) = v')
    (hkt : mem (updPtr + 3) = kt) (hkh : mem (updPtr + 4) = kh)
    (horig : mem (auxPtr + auxOffOrigVertPtr) = origBase)
    (hisOrig : mem (auxPtr + auxOffIsOrigVertPtr) = isOrigBase)
    (hvOrig : mem (origBase + v) = vOrig)
    (hrest : ∃ o st' c,
      Runs w p ω rest
        { mem := mem
          regs := Function.update (Function.update (Function.update (Function.update (Function.update
            (Function.update (Function.update (Function.update (Function.update (Function.update
            (Function.update (Function.update (Function.update (Function.update (Function.update
            (Function.update (startState [b, updPtr] mem pos).regs
              2 vCap) 3 eCap) 4 n0) 5 tM) 6 dgGPtr) 7 tPtr) 8 dgFPtr) 9 fAncPtr) 10 auxPtr)
              11 v) 12 v') 13 kt) 14 kh) 15 origBase) 16 isOrigBase) 17 vOrig
          pos := pos }
        o st' c ∧ Q o st' ∧ c ≤ T) :
    ∃ o st' c,
      Runs w p ω
        (.assign 2 (.load (.bin .add (.reg 0) (.const lsfOffVCap))) ;;
         .assign 3 (.load (.bin .add (.reg 0) (.const lsfOffECap))) ;;
         .assign 4 (.load (.bin .add (.reg 0) (.const lsfOffN0))) ;;
         .assign 5 (.load (.bin .add (.reg 0) (.const lsfOffTM))) ;;
         .assign 6 (.load (.bin .add (.reg 0) (.const lsfOffDgGPtr))) ;;
         .assign 7 (.load (.bin .add (.reg 0) (.const lsfOffTPtr))) ;;
         .assign 8 (.load (.bin .add (.reg 0) (.const lsfOffDgFPtr))) ;;
         .assign 9 (.load (.bin .add (.reg 0) (.const lsfOffFAncPtr))) ;;
         .assign 10 (.load (.bin .add (.reg 0) (.const lsfOffAuxPtr))) ;;
         .assign 11 (.load (.bin .add (.reg 1) (.const 1))) ;;
         .assign 12 (.load (.bin .add (.reg 1) (.const 2))) ;;
         .assign 13 (.load (.bin .add (.reg 1) (.const 3))) ;;
         .assign 14 (.load (.bin .add (.reg 1) (.const 4))) ;;
         .assign 15 (.load (.bin .add (.reg 10) (.const auxOffOrigVertPtr))) ;;
         .assign 16 (.load (.bin .add (.reg 10) (.const auxOffIsOrigVertPtr))) ;;
         .assign 17 (.load (.bin .add (.reg 15) (.reg 11))) ;;
         rest)
        (startState [b, updPtr] mem pos) o st' c ∧
      Q o st' ∧ 0 + c ≤ T + 160 := by
  let rg0 := (startState [b, updPtr] mem pos).regs
  let rg1 := Function.update rg0 2 vCap
  let rg2 := Function.update rg1 3 eCap
  let rg3 := Function.update rg2 4 n0
  let rg4 := Function.update rg3 5 tM
  let rg5 := Function.update rg4 6 dgGPtr
  let rg6 := Function.update rg5 7 tPtr
  let rg7 := Function.update rg6 8 dgFPtr
  let rg8 := Function.update rg7 9 fAncPtr
  let rg9 := Function.update rg8 10 auxPtr
  let rg10 := Function.update rg9 11 v
  let rg11 := Function.update rg10 12 v'
  let rg12 := Function.update rg11 13 kt
  let rg13 := Function.update rg12 14 kh
  let rg14 := Function.update rg13 15 origBase
  let rg15 := Function.update rg14 16 isOrigBase
  have h0_0 : rg0 0 = b := by simp [rg0, startState]
  have h0_1 : rg0 1 = updPtr := by simp [rg0, startState]
  have h1_0 : rg1 0 = b := (Function.update_of_ne (by decide) _ _).trans h0_0
  have h2_0 : rg2 0 = b := (Function.update_of_ne (by decide) _ _).trans h1_0
  have h3_0 : rg3 0 = b := (Function.update_of_ne (by decide) _ _).trans h2_0
  have h4_0 : rg4 0 = b := (Function.update_of_ne (by decide) _ _).trans h3_0
  have h5_0 : rg5 0 = b := (Function.update_of_ne (by decide) _ _).trans h4_0
  have h6_0 : rg6 0 = b := (Function.update_of_ne (by decide) _ _).trans h5_0
  have h7_0 : rg7 0 = b := (Function.update_of_ne (by decide) _ _).trans h6_0
  have h8_0 : rg8 0 = b := (Function.update_of_ne (by decide) _ _).trans h7_0
  have h1_1 : rg1 1 = updPtr := (Function.update_of_ne (by decide) _ _).trans h0_1
  have h2_1 : rg2 1 = updPtr := (Function.update_of_ne (by decide) _ _).trans h1_1
  have h3_1 : rg3 1 = updPtr := (Function.update_of_ne (by decide) _ _).trans h2_1
  have h4_1 : rg4 1 = updPtr := (Function.update_of_ne (by decide) _ _).trans h3_1
  have h5_1 : rg5 1 = updPtr := (Function.update_of_ne (by decide) _ _).trans h4_1
  have h6_1 : rg6 1 = updPtr := (Function.update_of_ne (by decide) _ _).trans h5_1
  have h7_1 : rg7 1 = updPtr := (Function.update_of_ne (by decide) _ _).trans h6_1
  have h8_1 : rg8 1 = updPtr := (Function.update_of_ne (by decide) _ _).trans h7_1
  have h9_1 : rg9 1 = updPtr := (Function.update_of_ne (by decide) _ _).trans h8_1
  have h10_1 : rg10 1 = updPtr := (Function.update_of_ne (by decide) _ _).trans h9_1
  have h11_1 : rg11 1 = updPtr := (Function.update_of_ne (by decide) _ _).trans h10_1
  have h12_1 : rg12 1 = updPtr := (Function.update_of_ne (by decide) _ _).trans h11_1
  have h9_10 : rg9 10 = auxPtr := Function.update_self 10 auxPtr rg8
  have h10_10 : rg10 10 = auxPtr := (Function.update_of_ne (by decide) _ _).trans h9_10
  have h11_10 : rg11 10 = auxPtr := (Function.update_of_ne (by decide) _ _).trans h10_10
  have h12_10 : rg12 10 = auxPtr := (Function.update_of_ne (by decide) _ _).trans h11_10
  have h13_10 : rg13 10 = auxPtr := (Function.update_of_ne (by decide) _ _).trans h12_10
  have h14_10 : rg14 10 = auxPtr := (Function.update_of_ne (by decide) _ _).trans h13_10
  have h10_11 : rg10 11 = v := Function.update_self 11 v rg9
  have h11_11 : rg11 11 = v := (Function.update_of_ne (by decide) _ _).trans h10_11
  have h12_11 : rg12 11 = v := (Function.update_of_ne (by decide) _ _).trans h11_11
  have h13_11 : rg13 11 = v := (Function.update_of_ne (by decide) _ _).trans h12_11
  have h14_11 : rg14 11 = v := (Function.update_of_ne (by decide) _ _).trans h13_11
  have h15_11 : rg15 11 = v := (Function.update_of_ne (by decide) _ _).trans h14_11
  have h14_15 : rg14 15 = origBase := Function.update_self 15 origBase rg13
  have h15_15 : rg15 15 = origBase := (Function.update_of_ne (by decide) _ _).trans h14_15
  have mkAddC : ∀ {rg : ℕ → ℕ} {i val k : ℕ}, rg i = val → k < 2 ^ w → val + k < 2 ^ w →
      Expr.eval w { mem := mem, regs := rg, pos := pos } (.bin .add (.reg i) (.const k)) =
        some (val + k) := fun hi hk hvk => by
    simp only [Expr.eval, BinOp.eval, hi, hk, hvk, ↓reduceIte]
  have s16 := step_assign_load (st := { mem := mem, regs := rg15, pos := pos }) (r := 17)
    (eAddr := .bin .add (.reg 15) (.reg 11))
    (by simp only [Expr.eval, BinOp.eval, h15_15, h15_11, horig_v, ↓reduceIte]) hvOrig hrest
  have s15 := step_assign_load (st := { mem := mem, regs := rg14, pos := pos }) (r := 16)
    (mkAddC h14_10 (ha_off auxOffIsOrigVertPtr (by decide)).1 (ha_off auxOffIsOrigVertPtr (by decide)).2) hisOrig s16
  have s14 := step_assign_load (st := { mem := mem, regs := rg13, pos := pos }) (r := 15)
    (mkAddC h13_10 (ha_off auxOffOrigVertPtr (by decide)).1 (ha_off auxOffOrigVertPtr (by decide)).2) horig s15
  have s13 := step_assign_load (st := { mem := mem, regs := rg12, pos := pos }) (r := 14)
    (mkAddC h12_1 (hu_off 4 (by decide)).1 (hu_off 4 (by decide)).2) hkh s14
  have s12 := step_assign_load (st := { mem := mem, regs := rg11, pos := pos }) (r := 13)
    (mkAddC h11_1 (hu_off 3 (by decide)).1 (hu_off 3 (by decide)).2) hkt s13
  have s11 := step_assign_load (st := { mem := mem, regs := rg10, pos := pos }) (r := 12)
    (mkAddC h10_1 (hu_off 2 (by decide)).1 (hu_off 2 (by decide)).2) hv' s12
  have s10 := step_assign_load (st := { mem := mem, regs := rg9, pos := pos }) (r := 11)
    (mkAddC h9_1 (hu_off 1 (by decide)).1 (hu_off 1 (by decide)).2) hv s11
  have s9 := step_assign_load (st := { mem := mem, regs := rg8, pos := pos }) (r := 10)
    (mkAddC h8_0 (hb_off lsfOffAuxPtr (by decide)).1 (hb_off lsfOffAuxPtr (by decide)).2) haux s10
  have s8 := step_assign_load (st := { mem := mem, regs := rg7, pos := pos }) (r := 9)
    (mkAddC h7_0 (hb_off lsfOffFAncPtr (by decide)).1 (hb_off lsfOffFAncPtr (by decide)).2) hfA s9
  have s7 := step_assign_load (st := { mem := mem, regs := rg6, pos := pos }) (r := 8)
    (mkAddC h6_0 (hb_off lsfOffDgFPtr (by decide)).1 (hb_off lsfOffDgFPtr (by decide)).2) hdgF s8
  have s6 := step_assign_load (st := { mem := mem, regs := rg5, pos := pos }) (r := 7)
    (mkAddC h5_0 (hb_off lsfOffTPtr (by decide)).1 (hb_off lsfOffTPtr (by decide)).2) htP s7
  have s5 := step_assign_load (st := { mem := mem, regs := rg4, pos := pos }) (r := 6)
    (mkAddC h4_0 (hb_off lsfOffDgGPtr (by decide)).1 (hb_off lsfOffDgGPtr (by decide)).2) hdgG s6
  have s4 := step_assign_load (st := { mem := mem, regs := rg3, pos := pos }) (r := 5)
    (mkAddC h3_0 (hb_off lsfOffTM (by decide)).1 (hb_off lsfOffTM (by decide)).2) htM s5
  have s3 := step_assign_load (st := { mem := mem, regs := rg2, pos := pos }) (r := 4)
    (mkAddC h2_0 (hb_off lsfOffN0 (by decide)).1 (hb_off lsfOffN0 (by decide)).2) hn0 s4
  have s2 := step_assign_load (st := { mem := mem, regs := rg1, pos := pos }) (r := 3)
    (mkAddC h1_0 (hb_off lsfOffECap (by decide)).1 (hb_off lsfOffECap (by decide)).2) hec s3
  have s1 := step_assign_load (st := { mem := mem, regs := rg0, pos := pos }) (r := 2)
    (mkAddC h0_0 (hb_off lsfOffVCap (by decide)).1 (hb_off lsfOffVCap (by decide)).2) hvc s2
  rcases s1 with ⟨o, st', c, hrun, hQ, hc⟩
  exact ⟨o, st', c, hrun, hQ, by dsimp only [Expr.size] at hc; omega⟩


end

end MinCostFlow.LSF.Program
