module

public import MinCostFlow.LSF.Program.BatchAddRoot
public import MinCostFlow.LSF.Program.BatchSplitMath
public import MinCostFlow.LSF.Program.BatchTBlockOps
import Mathlib.Tactic.Linarith

/-!
# Edge-Insert and Edge-Delete Procedures for Dynamic LSF (`BatchUpdateOps`)

Implements and verifies the edge-insertion and edge-deletion sub-procedures of LSF dynamic batch
updates (`Lemma 5.4`, `arXiv:2309.16629v1` page 17 and Appendix A.1 page 48):

* `lsfInsertUpdateProc` (`[b, e, u, v]`, returns `4`): closes `u` and `v` (when original vertices)
  in `T_H` via `addOrigRoot`, inserts `(e, u, v)` into `dgG` and `TBlock`, and sets `wstr[e] = 1`
  via `lsfSetWstrOne` in amortized time `O(L_w)`.
* `lsfDeleteUpdateProc` (`[b, e]`, returns `2`): reads endpoints `(u, v)` of `e` in `dgG`, closes
  `origVert u` and `origVert v` in `T_H` via `addOrigRoot`, deletes `e` from `dgG`, and updates
  `TBlock` in amortized time `O(1)`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## Procedure definitions -/

/-- Apply one edge insertion `.insert e u v` (`[b, e, u, v]`), returning `4`. -/
def lsfInsertUpdateProc (idxAddRoot idxDgIns idxTIns idxSetWstr : ℕ) : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.const lsfOffVCap))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const lsfOffECap))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const lsfOffTM))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const lsfOffDgGPtr))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const lsfOffTPtr))) ;;
  .assign 9 (.load (.bin .add (.reg 0) (.const lsfOffWstrNumPtr))) ;;
  .assign 10 (.load (.bin .add (.reg 0) (.const lsfOffWstrDenPtr))) ;;
  .assign 11 (.load (.bin .add (.reg 0) (.const lsfOffLW))) ;;
  .assign 12 (.load (.bin .add (.reg 0) (.const lsfOffAuxPtr))) ;;
  .assign 13 (.load (.bin .add (.reg 12) (.const auxOffIsOrigVertPtr))) ;;
  .cond (.load (.bin .add (.reg 13) (.reg 2)))
    (.call 14 idxAddRoot [.reg 0, .reg 2])
    .nop ;;
  .cond (.load (.bin .add (.reg 13) (.reg 3)))
    (.call 14 idxAddRoot [.reg 0, .reg 3])
    .nop ;;
  .call 14 idxDgIns [.reg 7, .reg 1, .reg 2, .reg 3] ;;
  .call 14 idxTIns [.reg 8, .reg 4, .reg 5, .reg 6, .reg 1, .reg 2, .reg 3] ;;
  .call 14 idxSetWstr [.reg 9, .reg 10, .reg 1, .reg 11] ;;
  .ret (.const 4)

lemma lsfInsertUpdateProc_noRand (idxAddRoot idxDgIns idxTIns idxSetWstr : ℕ) :
    (lsfInsertUpdateProc idxAddRoot idxDgIns idxTIns idxSetWstr).NoRand := by
  dsimp [lsfInsertUpdateProc]; trivial

/-- Apply one edge deletion `.delete e` (`[b, e]`), returning `2`. -/
def lsfDeleteUpdateProc (idxAddRoot idxDgDel idxTDel : ℕ) : Stmt :=
  .assign 2 (.load (.bin .add (.reg 0) (.const lsfOffVCap))) ;;
  .assign 3 (.load (.bin .add (.reg 0) (.const lsfOffECap))) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const lsfOffTM))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const lsfOffDgGPtr))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const lsfOffTPtr))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const lsfOffAuxPtr))) ;;
  .assign 8 (.load (.bin .add (.reg 7) (.const auxOffOrigVertPtr))) ;;
  .assign 9 (.bin .add (.bin .add (.reg 5) (.const 4)) (.bin .mul (.const 4) (.reg 2))) ;;
  .assign 10 (.bin .add (.bin .add (.bin .add (.reg 5) (.const 4)) (.bin .mul (.const 7) (.reg 2)))
    (.bin .mul (.const 3) (.reg 3))) ;;
  .assign 11 (.bin .add (.bin .add (.bin .add (.reg 5) (.const 4)) (.bin .mul (.const 7) (.reg 2)))
    (.bin .mul (.const 4) (.reg 3))) ;;
  .assign 12 (.load (.bin .add (.reg 9) (.load (.bin .add (.reg 10) (.reg 1))))) ;;
  .assign 13 (.load (.bin .add (.reg 9) (.load (.bin .add (.reg 11) (.reg 1))))) ;;
  .assign 14 (.load (.bin .add (.reg 8) (.reg 12))) ;;
  .assign 15 (.load (.bin .add (.reg 8) (.reg 13))) ;;
  .call 16 idxAddRoot [.reg 0, .reg 14] ;;
  .call 16 idxAddRoot [.reg 0, .reg 15] ;;
  .call 16 idxDgDel [.reg 5, .reg 1] ;;
  .call 16 idxTDel [.reg 6, .reg 2, .reg 3, .reg 4, .reg 1, .reg 12, .reg 13] ;;
  .ret (.const 2)

lemma lsfDeleteUpdateProc_noRand (idxAddRoot idxDgDel idxTDel : ℕ) :
    (lsfDeleteUpdateProc idxAddRoot idxDgDel idxTDel).NoRand := by
  dsimp [lsfDeleteUpdateProc]; trivial

/-! ## Layout helpers for `SameStaticConcrete` -/

private lemma lsfBlock_disjoint (b vCap eCap n0 tM L_w : ℕ) :
    let dgGPtr := lsfDgGPtr b
    let tPtr := lsfTBlockPtr b vCap eCap
    let dgFPtr := lsfDgFPtr b vCap eCap tM
    let fAncPtr := lsfFAncPtr b vCap eCap n0 tM
    let wPtr := lsfWBlockPtr b vCap eCap n0 tM
    let auxPtr := lsfAuxPtr b vCap eCap n0 tM L_w
    let wstrNumPtr := lsfWstrNumPtr b vCap eCap n0 tM
    let wstrDenPtr := lsfWstrDenPtr b vCap eCap n0 tM L_w
    let endAddr := lsfEndAddr b vCap eCap n0 tM L_w
    b + lsfHdrSize = dgGPtr ∧
    dgGPtr + dynGraphSize vCap eCap = tPtr ∧
    tPtr + tBlockSize vCap eCap tM = dgFPtr ∧
    dgFPtr + dynGraphSize vCap (fECap eCap n0) = fAncPtr ∧
    fAncPtr + fAncSize vCap = wPtr ∧
    wPtr + wBlockSize n0 = auxPtr ∧
    auxPtr + auxSize vCap n0 = wstrNumPtr ∧
    wstrNumPtr + eCap * L_w = wstrDenPtr ∧
    wstrDenPtr + eCap * L_w = endAddr := by
  dsimp only [lsfDgGPtr, lsfTBlockPtr, lsfDgFPtr, lsfFAncPtr, lsfWBlockPtr,
    lsfAuxPtr, lsfWstrNumPtr, lsfWstrDenPtr, lsfEndAddr, lsfStaticSize]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  omega

private lemma SameStaticConcrete.vCap_eq {x x' : LSFConcrete} (hs : SameStaticConcrete x x') : x'.vCap = x.vCap := hs.1
private lemma SameStaticConcrete.eCap_eq {x x' : LSFConcrete} (hs : SameStaticConcrete x x') : x'.eCap = x.eCap := hs.2.1
private lemma SameStaticConcrete.n0_eq {x x' : LSFConcrete} (hs : SameStaticConcrete x x') : x'.n0 = x.n0 := hs.2.2.1
private lemma SameStaticConcrete.tM_eq {x x' : LSFConcrete} (hs : SameStaticConcrete x x') : x'.tM = x.tM := hs.2.2.2.2.1
private lemma SameStaticConcrete.L_w_eq {x x' : LSFConcrete} (hs : SameStaticConcrete x x') : x'.L_w = x.L_w := hs.2.2.2.2.2.2.2.2.1
private lemma SameStaticConcrete.tOrigList_eq {x x' : LSFConcrete} (hs : SameStaticConcrete x x') : x'.tOrigList = x.tOrigList := hs.2.2.2.2.2.2.2.2.2.2.1
private lemma SameStaticConcrete.vList_eq {x x' : LSFConcrete} (hs : SameStaticConcrete x x') : x'.vList = x.vList := hs.2.2.2.2.2.2.2.2.2.2.2.1

private lemma sameStatic_endAddr {b : ℕ} {x x' : LSFConcrete} (hs : SameStaticConcrete x x') :
    x'.endAddr b = x.endAddr b := by
  dsimp only [LSFConcrete.endAddr]
  rw [hs.vCap_eq, hs.eCap_eq, hs.n0_eq, hs.tM_eq, hs.L_w_eq]

private lemma runs_seq_of_runs_le' {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {s₁ s₂ : Stmt} {st st₁ : State} {c₁ k T : ℕ} {Q : Outcome → State → Prop}
    (hr₁ : Runs w p ω s₁ st .normal st₁ c₁)
    (hrest : ∃ o st' c₂, Runs w p ω s₂ st₁ o st' c₂ ∧ Q o st' ∧ (k + c₁ + 1) + c₂ ≤ T) :
    ∃ o st' c, Runs w p ω (.seq s₁ s₂) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases hrest with ⟨o, st', c₂, hr₂, hq, hc⟩
  exact ⟨o, st', c₁ + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, hr₁, hr₂, rfl⟩), hq, by omega⟩

/-! ## Verification of `lsfInsertUpdateProc` -/

theorem lsfInsertUpdate_runs
    {w h b e u v idxAddRoot idxMinUp idxDgDelF idxBFS idxDgIns idxTIns idxSetWstr : ℕ}
    {p : Program} {ω : ℕ → Bool} {S : LSFState} {x : LSFConcrete} {mem : ℕ → ℕ} {pos : ℕ}
    (hw16 : 16 ≤ 2 ^ w) (hend_ltw : x.endAddr b < 2 ^ w)
    (hrep : (LSFRep h).rep b S x mem)
    (hu_valid : S.G.UpdateIsValid (.insert e u v))
    (he_cap : e < x.eCap)
    (hpAdd : p.procs[idxAddRoot]? = some (addOrigRootProc idxMinUp idxDgDelF idxBFS))
    (hMinUp : ∀ S₀, MeetsContract w p idxMinUp (minEdgeUpContract w S₀ x.vList x.tOrigList))
    (hDgDelF : ∀ F, MeetsContract w p idxDgDelF (dgDeleteEdgeContract w x.vCap (fECap x.eCap x.n0) F))
    (hBFS : ∀ F, MeetsContract w p idxBFS (splitCompBFSContract w F))
    (hDgIns : ∀ G, MeetsContract w p idxDgIns (dgInsertEdgeContract w x.vCap x.eCap G))
    (hTIns : ∀ G T_cur, MeetsContract w p idxTIns
      (lsfTBlockInsertContract w x.vCap x.eCap x.tM G T_cur S.T₀ S.π x.tOrigList))
    (hSetWstr : MeetsContract w p idxSetWstr (lsfSetWstrOneContract w h)) :
    ∃ st' c x',
      Runs w p ω (lsfInsertUpdateProc idxAddRoot idxDgIns idxTIns idxSetWstr)
        (startState [b, e, u, v] mem pos) (.returned 4) st' c ∧
      SameStaticConcrete x x' ∧
      (LSFRep h).rep b (applyLSFUpdate S (.insert e u v)) x' st'.mem ∧
      (∀ a, a < b ∨ x.endAddr b ≤ a → st'.mem a = mem a) ∧
      c + lsfPhi b x' st'.mem ≤ 50 * x.L_w + 2400 + lsfPhi b x mem := by
  classical
  set vCap := x.vCap; set eCap := x.eCap; set n0 := x.n0; set tM := x.tM; set L_w := x.L_w
  set dgGPtr := lsfDgGPtr b
  set tPtr := lsfTBlockPtr b vCap eCap
  set dgFPtr := lsfDgFPtr b vCap eCap tM
  set fAncPtr := lsfFAncPtr b vCap eCap n0 tM
  set wPtr := lsfWBlockPtr b vCap eCap n0 tM
  set auxPtr := lsfAuxPtr b vCap eCap n0 tM L_w
  set wstrNumPtr := lsfWstrNumPtr b vCap eCap n0 tM
  set wstrDenPtr := lsfWstrDenPtr b vCap eCap n0 tM L_w
  set isOrigBase := auxIsOrigVertBase auxPtr vCap n0
  have hlay := lsfBlock_disjoint b vCap eCap n0 tM L_w
  have hend_eq : x.endAddr b = lsfEndAddr b vCap eCap n0 tM L_w := rfl
  have hrep_orig := hrep
  rcases hrep with ⟨hxH, hh1, hLin, hLw, hkn, hkeq, hInv, hn0, hm0, htM, hnv, hme, htn, hn1,
    hvT_lt, heG_lt, hhdr, hdgG, hT, hdgF, hFAnc, hW, hwstr, hAux⟩
  have huG : u ∈ S.G.V := hu_valid.2.1
  have hvG : v ∈ S.G.V := hu_valid.2.2
  have he_notG : e ∉ S.G.E := hu_valid.1
  have hu_lt : u < vCap := hdgG.2.1 u huG
  have hv_lt : v < vCap := hdgG.2.1 v hvG
  have hb_hdr_ltw : b + lsfHdrSize < 2 ^ w := by
    have := hlay.1; have := hlay.2.1; have := hlay.2.2.1; have := hlay.2.2.2.1
    have := hlay.2.2.2.2.1; have := hlay.2.2.2.2.2.1; have := hlay.2.2.2.2.2.2.1
    have := hlay.2.2.2.2.2.2.2.1; have := hlay.2.2.2.2.2.2.2.2; omega
  have hdgG_end_ltw : dgGPtr + dynGraphSize vCap eCap < 2 ^ w := by
    have := hlay.2.1; have := hlay.2.2.1; have := hlay.2.2.2.1
    have := hlay.2.2.2.2.1; have := hlay.2.2.2.2.2.1; have := hlay.2.2.2.2.2.2.1
    have := hlay.2.2.2.2.2.2.2.1; have := hlay.2.2.2.2.2.2.2.2; omega
  have htPtr_end_ltw : tPtr + tBlockSize vCap eCap tM < 2 ^ w := by
    have := hlay.2.2.1; have := hlay.2.2.2.1; have := hlay.2.2.2.2.1
    have := hlay.2.2.2.2.2.1; have := hlay.2.2.2.2.2.2.1; have := hlay.2.2.2.2.2.2.2.1
    have := hlay.2.2.2.2.2.2.2.2; omega
  have haux_end_ltw : auxPtr + auxSize vCap n0 < 2 ^ w := by
    have := hlay.2.2.2.2.2.2.1; have := hlay.2.2.2.2.2.2.2.1
    have := hlay.2.2.2.2.2.2.2.2; omega
  have hwstrN_end_ltw : wstrNumPtr + eCap * L_w < 2 ^ w := by
    have := hlay.2.2.2.2.2.2.2.1; have := hlay.2.2.2.2.2.2.2.2; omega
  have hwstrD_end_ltw : wstrDenPtr + eCap * L_w < 2 ^ w := by
    have := hlay.2.2.2.2.2.2.2.2; omega
  have hvCap_ltw : vCap < 2 ^ w := by dsimp [dynGraphSize] at hdgG_end_ltw; omega
  have heCap_ltw : eCap < 2 ^ w := by dsimp [dynGraphSize] at hdgG_end_ltw; omega
  have htM_ltw : tM < 2 ^ w := by omega
  have hLw_ltw : L_w < 2 ^ w := by
    have : 1 * L_w ≤ eCap * L_w := Nat.mul_le_mul_right L_w (by omega)
    omega
  have hisOrig_end_ltw : isOrigBase + vCap < 2 ^ w := by
    dsimp [isOrigBase, auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase,
      auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase,
      auxVIdxBase, auxSize] at haux_end_ltw ⊢
    omega
  have he_ltw : e < 2 ^ w := by omega
  have hu_ltw : u < 2 ^ w := by omega
  have hv_ltw : v < 2 ^ w := by omega
  have hfactor := applyLSFUpdate_insert_eq hInv hu_valid
  set S₁ : LSFState := if u ∈ S.T₀.V then { S with R₀_base := insert u S.R₀_base } else S
  set S₂ : LSFState := if v ∈ S.T₀.V then { S₁ with R₀_base := insert v S₁.R₀_base } else S₁
  set S' : LSFState := applyLSFUpdate S (.insert e u v)
  have hInv₁ : LSFStructInv S₁ := hfactor.1
  have hInv₂ : LSFStructInv S₂ := hfactor.2.1
  have hInv' : LSFStructInv S' := hfactor.2.2.1
  have hRorig' : S'.R_orig = S₂.R_orig := hfactor.2.2.2.2.1
  have hR' : S'.R = S₂.R := hfactor.2.2.2.2.2.1
  have hRF' : S'.RF = S₂.RF := hfactor.2.2.2.2.2.2
  have hS1_T0 : S₁.T₀ = S.T₀ := by dsimp [S₁]; split_ifs <;> rfl
  have hS2_G : S₂.G = S.G := by dsimp [S₂, S₁]; split_ifs <;> rfl
  have hS2_T0 : S₂.T₀ = S.T₀ := by dsimp [S₂, S₁]; split_ifs <;> rfl
  have hS2_Tcur : S₂.T_cur = S.T_cur := by dsimp [S₂, S₁]; split_ifs <;> rfl
  have hS2_pi : S₂.π = S.π := by dsimp [S₂, S₁]; split_ifs <;> rfl
  have hS2_wstr : S₂.wstr = S.wstr := by dsimp [S₂, S₁]; split_ifs <;> rfl
  have hS2_orig : S₂.origVert = S.origVert := by dsimp [S₂, S₁]; split_ifs <;> rfl
  have hS2_W : S₂.W_init = S.W_init := by dsimp [S₂, S₁]; split_ifs <;> rfl
  have hS2_r0 : S₂.r₀ = S.r₀ := by dsimp [S₂, S₁]; split_ifs <;> rfl
  have hS2_R0i : S₂.R₀_init = S.R₀_init := by dsimp [S₂, S₁]; split_ifs <;> rfl
  have hS2_G0 : S₂.G₀ = S.G₀ := by dsimp [S₂, S₁]; split_ifs <;> rfl
  have hS2_k : S₂.k = S.k := by dsimp [S₂, S₁]; split_ifs <;> rfl
  -- Shared continuation after both conditional `addOrigRoot` calls
  have hafter_v : ∀ (mem2 : ℕ → ℕ) (regs2 : ℕ → ℕ) (pos2 : ℕ) (x2 : LSFConcrete),
      SameStaticConcrete x x2 →
      (LSFRep h).rep b S₂ x2 mem2 →
      (∀ a, a < b ∨ x.endAddr b ≤ a → mem2 a = mem a) →
      regs2 0 = b → regs2 1 = e → regs2 2 = u → regs2 3 = v →
      regs2 4 = vCap → regs2 5 = eCap → regs2 6 = tM → regs2 7 = dgGPtr →
      regs2 8 = tPtr → regs2 9 = wstrNumPtr → regs2 10 = wstrDenPtr → regs2 11 = L_w →
      ∃ st' c,
        Runs w p ω
          (.call 14 idxDgIns [.reg 7, .reg 1, .reg 2, .reg 3] ;;
           .call 14 idxTIns [.reg 8, .reg 4, .reg 5, .reg 6, .reg 1, .reg 2, .reg 3] ;;
           .call 14 idxSetWstr [.reg 9, .reg 10, .reg 1, .reg 11] ;;
           .ret (.const 4))
          { mem := mem2, regs := regs2, pos := pos2 } (.returned 4) st' c ∧
        (LSFRep h).rep b S' x2 st'.mem ∧
        (∀ a, a < b ∨ x.endAddr b ≤ a → st'.mem a = mem a) ∧
        lsfPhi b x2 st'.mem = lsfPhi b x2 mem2 ∧
        c ≤ 50 * L_w + 1700 := by
    intro mem2 regs2 pos2 x2 hsame2 hrep2 hfr2 hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8 hr9 hr10 hr11
    have hrep2_copy := hrep2
    rcases hrep2 with ⟨hxH2, hh1_2, hLin2, hLw2, hkn2, hkeq2, _, hn0_2, hm0_2, htM2, hnv2, hme2, htn2,
      hn1_2, hvT_lt2, heG_lt2, hhdr2, hdgG2, hT2, hdgF2, hFAnc2, hW2, hwstr2, hAux2⟩
    have hx2_vc : x2.vCap = vCap := hsame2.vCap_eq
    have hx2_ec : x2.eCap = eCap := hsame2.eCap_eq
    have hx2_n0 : x2.n0 = n0 := hsame2.n0_eq
    have hx2_tM : x2.tM = tM := hsame2.tM_eq
    have hx2_Lw : x2.L_w = L_w := hsame2.L_w_eq
    have hx2_tL : x2.tOrigList = x.tOrigList := hsame2.tOrigList_eq
    have hdgG2' : DynGraphAt mem2 dgGPtr vCap eCap S₂.G := by
      simpa only [hx2_vc, hx2_ec] using hdgG2
    have hT2' : TBlockAt mem2 tPtr vCap eCap tM S₂.G S₂.T_cur S.T₀ S.π x.tOrigList := by
      simpa only [hx2_vc, hx2_ec, hx2_tM, hx2_tL, hS2_T0, hS2_pi, tPtr] using hT2
    suffices hgoal : ∃ o st' c,
        Runs w p ω
          (.call 14 idxDgIns [.reg 7, .reg 1, .reg 2, .reg 3] ;;
           .call 14 idxTIns [.reg 8, .reg 4, .reg 5, .reg 6, .reg 1, .reg 2, .reg 3] ;;
           .call 14 idxSetWstr [.reg 9, .reg 10, .reg 1, .reg 11] ;;
           .ret (.const 4))
          { mem := mem2, regs := regs2, pos := pos2 } o st' c ∧
        (o = .returned 4 ∧ (LSFRep h).rep b S' x2 st'.mem ∧
          (∀ a, a < b ∨ x.endAddr b ≤ a → st'.mem a = mem a)) ∧
        0 + c ≤ 50 * L_w + 1700 by
      rcases hgoal with ⟨_, st', c, hrun, ⟨rfl, hrep', hfr'⟩, hc⟩
      have hphi_eq : lsfPhi b x2 st'.mem = lsfPhi b x2 mem2 := by
        rw [lsfPhi_eq_semantic hrep', lsfPhi_eq_semantic hrep2_copy, hRorig', hRF']
      exact ⟨st', c, hrun, hrep', hfr', hphi_eq, by omega⟩
    -- Step 1: dgInsertEdge(dgGPtr, e, u, v)
    have hpre_ins : (dgInsertEdgeContract w vCap eCap S₂.G).pre [dgGPtr, e, u, v] mem2 :=
      ⟨dgGPtr, e, u, v, rfl, hw16, hdgG_end_ltw, hS2_G.symm ▸ huG, hS2_G.symm ▸ hvG, hdgG2'⟩
    refine runs_seq_call_le (hDgIns S₂.G) (by eval_expr)
      (by intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with rfl | rfl | rfl | rfl <;> omega)
      hpre_ins ?_
    intro ret1 mem3 pos3 hpost1
    rcases hpost1 with ⟨_, _, _, _, hEq1, _, hdgG3_raw, hfr_dgG⟩
    simp only [List.cons.injEq, and_true] at hEq1
    rcases hEq1 with ⟨rfl, rfl, rfl, rfl⟩
    have hdgG3 : DynGraphAt mem3 dgGPtr vCap eCap S'.G := by
      have hcond : e < eCap ∧ e ∉ S₂.G.E := ⟨he_cap, hS2_G.symm ▸ he_notG⟩
      rw [ite_eq_left hcond] at hdgG3_raw
      simpa only [S', applyLSFUpdate, hS2_G] using hdgG3_raw
    -- Step 2: lsfTBlockInsert(tPtr, vCap, eCap, tM, e, u, v)
    have hT3_pre : TBlockAt mem3 tPtr vCap eCap tM S₂.G S₂.T_cur S.T₀ S.π x.tOrigList :=
      hT2'.of_agree fun a ha1 _ => hfr_dgG a (Or.inr (by omega))
    have hpre_tIns : (lsfTBlockInsertContract w vCap eCap tM S₂.G S₂.T_cur S.T₀ S.π x.tOrigList).pre
        [tPtr, vCap, eCap, tM, e, u, v] mem3 :=
      ⟨tPtr, e, u, v, rfl, hw16, htPtr_end_ltw, hS2_G.symm ▸ hu_valid, he_cap,
        hInv₂.hT_cur_forest.1, hInv₂.hT_cur_V, hS2_T0 ▸ hInv₂.hT_cur_E, hT3_pre⟩
    refine runs_seq_call_le (hTIns S₂.G S₂.T_cur) (by eval_expr)
      (by intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
      hpre_tIns ?_
    intro ret2 mem4 pos4 hpost2
    rcases hpost2 with ⟨_, _, _, _, hEq2, _, hT4_raw, hfr_T⟩
    simp only [List.cons.injEq, true_and, and_true] at hEq2
    rcases hEq2 with ⟨rfl, rfl, rfl, rfl⟩
    -- Step 3: lsfSetWstrOne(wstrNumPtr, wstrDenPtr, e, L_w)
    have he1L : (e + 1) * L_w ≤ eCap * L_w := Nat.mul_le_mul_right L_w he_cap
    have hpre_wstr : (lsfSetWstrOneContract w h).pre [wstrNumPtr, wstrDenPtr, e, L_w] mem4 :=
      ⟨wstrNumPtr, wstrDenPtr, e, L_w, rfl, hw16, hh1, hLw, by simpa only [hxH2, hx2_Lw] using hwstr2.1,
        by omega, by omega, Or.inl (by omega)⟩
    refine runs_seq_call_le hSetWstr (by eval_expr)
      (by intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with rfl | rfl | rfl | rfl <;> omega)
      hpre_wstr ?_
    intro ret3 mem5 pos5 hpost3
    rcases hpost3 with ⟨_, _, _, _, hEq3, _, hVN5, hVD5, hIN5, hID5, hfr_wstr⟩
    simp only [List.cons.injEq, and_true] at hEq3
    rcases hEq3 with ⟨rfl, rfl, rfl, rfl⟩
    -- Assemble `(LSFRep h).rep b S' x2 mem5`
    have hfr_wstr_below : ∀ a, a < wstrNumPtr → mem5 a = mem4 a := fun a ha =>
      hfr_wstr a (fun ⟨h1, _⟩ => by omega) (fun ⟨h1, _⟩ => by omega)
    have hfr_45_below_dgG : ∀ a, a < dgGPtr → mem5 a = mem2 a := fun a ha =>
      (hfr_wstr_below a (by omega)).trans ((hfr_T a (Or.inl (by omega))).trans (hfr_dgG a (Or.inl ha)))
    have hfr_45_mid : ∀ a, dgFPtr ≤ a → a < wstrNumPtr → mem5 a = mem2 a := fun a ha1 ha2 =>
      (hfr_wstr_below a ha2).trans ((hfr_T a (Or.inr (by omega))).trans (hfr_dgG a (Or.inr (by omega))))
    have hfr_all : ∀ a, a < b ∨ x.endAddr b ≤ a → mem5 a = mem a := by
      intro a ha
      have h54 : mem5 a = mem4 a := hfr_wstr a
        (fun ⟨h1, h2⟩ => by rcases ha with h | h <;> omega)
        (fun ⟨h1, h2⟩ => by rcases ha with h | h <;> omega)
      have h43 : mem4 a = mem3 a := hfr_T a (by rcases ha with h | h <;> [left; right] <;> omega)
      have h32 : mem3 a = mem2 a := hfr_dgG a (by rcases ha with h | h <;> [left; right] <;> omega)
      exact h54.trans (h43.trans (h32.trans (hfr2 a ha)))
    have hhdr5 : lsfHeaderAt mem5 b S' x2 := by
      have h1 : lsfHeaderAt mem5 b S₂ x2 := hhdr2.of_agree fun a _ ha2 => hfr_45_below_dgG a (by omega)
      have hr0' : S'.r₀ = S₂.r₀ := hS2_r0.symm
      simpa only [lsfHeaderAt, hR', hr0'] using h1
    have hdgG5 : DynGraphAt mem5 (lsfDgGPtr b) x2.vCap x2.eCap S'.G := by
      rw [hx2_vc, hx2_ec]
      exact hdgG3.of_agree fun a _ ha2 => (hfr_wstr_below a (by omega)).trans (hfr_T a (Or.inl (by omega)))
    have hT5 : TBlockAt mem5 (lsfTBlockPtr b x2.vCap x2.eCap) x2.vCap x2.eCap x2.tM
        S'.G S'.T_cur S'.T₀ S'.π x2.tOrigList := by
      rw [hx2_vc, hx2_ec, hx2_tM, hx2_tL]
      have hT4' : TBlockAt mem4 tPtr vCap eCap tM S'.G S'.T_cur S'.T₀ S'.π x.tOrigList := by
        simpa only [S', applyLSFUpdate, hS2_G, hS2_Tcur] using hT4_raw
      exact hT4'.of_agree fun a _ ha2 => hfr_wstr_below a (by omega)
    have hdgF5 : DynGraphAt mem5 (lsfDgFPtr b x2.vCap x2.eCap x2.tM) x2.vCap (fECap x2.eCap x2.n0) S'.RF.F := by
      rw [hRF']
      exact hdgF2.of_agree fun a ha1 ha2 => by
        rw [hx2_vc, hx2_ec, hx2_tM] at ha1
        rw [hx2_vc, hx2_ec, hx2_n0, hx2_tM] at ha2
        exact hfr_45_mid a ha1 (by omega)
    have hFAnc5 : FAncAt mem5 (lsfFAncPtr b x2.vCap x2.eCap x2.n0 x2.tM) x2.vCap S'.RF
        x2.rList x2.compId x2.compRoot x2.compSize x2.activeCids := by
      rw [hRF']
      exact hFAnc2.of_agree fun a ha1 ha2 => by
        rw [hx2_vc, hx2_ec, hx2_n0, hx2_tM] at ha1 ha2
        exact hfr_45_mid a (by omega) (by omega)
    have hW5 : WBlockAt mem5 (lsfWBlockPtr b x2.vCap x2.eCap x2.n0 x2.tM) x2.n0 S'.W_init
        (forestGivenRoots S'.T₀ S'.r₀ (upClosure (hldAuxTree S'.T₀ S'.r₀) S'.r₀ S'.R₀_init) S'.π) := by
      have h1 : WBlockAt mem5 (lsfWBlockPtr b x2.vCap x2.eCap x2.n0 x2.tM) x2.n0 S₂.W_init
          (forestGivenRoots S₂.T₀ S₂.r₀ (upClosure (hldAuxTree S₂.T₀ S₂.r₀) S₂.r₀ S₂.R₀_init) S₂.π) :=
        hW2.of_agree fun a ha1 ha2 => by
          rw [hx2_vc, hx2_ec, hx2_n0, hx2_tM] at ha1 ha2
          exact hfr_45_mid a (by omega) (by omega)
      simpa only [S', applyLSFUpdate, hS2_W, hS2_T0, hS2_r0, hS2_R0i, hS2_pi] using h1
    have hwstr5 : WstrAt mem5 (lsfWstrNumPtr b x2.vCap x2.eCap x2.n0 x2.tM)
        (lsfWstrDenPtr b x2.vCap x2.eCap x2.n0 x2.tM x2.L_w) x2.eCap x2.h x2.L_w S'.G S'.wstr := by
      rw [hx2_vc, hx2_ec, hx2_n0, hx2_tM, hx2_Lw, hxH2]
      have hw4 : WstrAt mem4 wstrNumPtr wstrDenPtr eCap h L_w S₂.G S₂.wstr := by
        have hw2' : WstrAt mem2 wstrNumPtr wstrDenPtr eCap h L_w S₂.G S₂.wstr := by
          simpa only [hx2_vc, hx2_ec, hx2_n0, hx2_tM, hx2_Lw, hxH2] using hwstr2
        exact hw2'.of_agree
          (fun a ha1 _ => (hfr_T a (Or.inr (by omega))).trans (hfr_dgG a (Or.inr (by omega))))
          (fun a ha1 _ => (hfr_T a (Or.inr (by omega))).trans (hfr_dgG a (Or.inr (by omega))))
      have hres := wstrAt_after_setOne hw4 he_cap hVN5 hVD5 hIN5 hID5
        (Or.inl (by omega)) hfr_wstr (u := u) (v := v)
      simpa only [S', applyLSFUpdate, hS2_G, hS2_wstr] using hres
    have hAux5 : AuxAt mem5 (lsfAuxPtr b x2.vCap x2.eCap x2.n0 x2.tM x2.L_w) x2.vCap x2.n0 x2.tM S'
        x2.tOrigList x2.vList x2.t0Parent x2.t0ParentTreeIdx x2.t0Depth x2.thParent x2.upV x2.upMinIdx := by
      have hAux_m5 : AuxAt mem5 (lsfAuxPtr b x2.vCap x2.eCap x2.n0 x2.tM x2.L_w) x2.vCap x2.n0 x2.tM S₂
          x2.tOrigList x2.vList x2.t0Parent x2.t0ParentTreeIdx x2.t0Depth x2.thParent x2.upV x2.upMinIdx :=
        hAux2.of_agree (fun a ha1 ha2 => by
          rw [hx2_vc, hx2_ec, hx2_n0, hx2_tM, hx2_Lw] at ha1 ha2
          exact hfr_45_mid a (by omega) (by omega)) hvT_lt2
      have hGV' : S'.G.V = S₂.G.V := by dsimp [S', applyLSFUpdate, MGraph.applyUpdate]; rw [hS2_G]
      have hTH' : S'.TH = S₂.TH := by simp only [LSFState.TH, S', applyLSFUpdate, hS2_T0, hS2_r0]
      have hT0' : S'.T₀ = S₂.T₀ := hS2_T0.symm
      have hr0' : S'.r₀ = S₂.r₀ := hS2_r0.symm
      have hpi' : S'.π = S₂.π := hS2_pi.symm
      have horig' : S'.origVert = S₂.origVert := hS2_orig.symm
      simpa only [AuxAt, hT0', hr0', hpi', hTH', hGV', horig'] using hAux_m5
    have hrep5 : (LSFRep h).rep b S' x2 mem5 :=
      ⟨hxH2, hh1_2, hLin2, hLw2, hkn2, hS2_k ▸ hkeq2, hInv', hS2_G0 ▸ hn0_2, hS2_G0 ▸ hm0_2,
        hS2_T0 ▸ htM2, hnv2, hme2, htn2, hn1_2, hS2_T0 ▸ hvT_lt2, hS2_G0 ▸ heG_lt2,
        hhdr5, hdgG5, hT5, hdgF5, hFAnc5, hW5, hwstr5, hAux5⟩
    refine runs_ret_le (v := 4) (by eval_expr) ⟨rfl, hrep5, hfr_all⟩ ?_
    have hc1 : (dgInsertEdgeContract w vCap eCap S₂.G).cost [dgGPtr, e, u, v] mem2 = 450 := rfl
    have hc2 : (lsfTBlockInsertContract w vCap eCap tM S₂.G S₂.T_cur S.T₀ S.π x.tOrigList).cost
        [tPtr, vCap, eCap, tM, e, u, v] mem3 = 1100 := rfl
    have hc3 : (lsfSetWstrOneContract w h).cost [wstrNumPtr, wstrDenPtr, e, L_w] mem4 = 50 * L_w + 50 := rfl
    rw [hc1, hc2, hc3]
    dsimp only [argsSize, Expr.size]
    omega
  -- Continuation after the first conditional `addOrigRoot(b, u)`
  have hafter_u : ∀ (mem1 : ℕ → ℕ) (regs1 : ℕ → ℕ) (pos1 : ℕ) (x1 : LSFConcrete),
      SameStaticConcrete x x1 →
      (LSFRep h).rep b S₁ x1 mem1 →
      (∀ a, a < b ∨ x.endAddr b ≤ a → mem1 a = mem a) →
      regs1 0 = b → regs1 1 = e → regs1 2 = u → regs1 3 = v →
      regs1 4 = vCap → regs1 5 = eCap → regs1 6 = tM → regs1 7 = dgGPtr →
      regs1 8 = tPtr → regs1 9 = wstrNumPtr → regs1 10 = wstrDenPtr → regs1 11 = L_w →
      regs1 13 = isOrigBase →
      ∃ st' c x2,
        Runs w p ω
          (.cond (.load (.bin .add (.reg 13) (.reg 3)))
             (.call 14 idxAddRoot [.reg 0, .reg 3]) .nop ;;
           .call 14 idxDgIns [.reg 7, .reg 1, .reg 2, .reg 3] ;;
           .call 14 idxTIns [.reg 8, .reg 4, .reg 5, .reg 6, .reg 1, .reg 2, .reg 3] ;;
           .call 14 idxSetWstr [.reg 9, .reg 10, .reg 1, .reg 11] ;;
           .ret (.const 4))
          { mem := mem1, regs := regs1, pos := pos1 } (.returned 4) st' c ∧
        SameStaticConcrete x x2 ∧
        (LSFRep h).rep b S' x2 st'.mem ∧
        (∀ a, a < b ∨ x.endAddr b ≤ a → st'.mem a = mem a) ∧
        c + lsfPhi b x2 st'.mem ≤ 50 * L_w + 2000 + lsfPhi b x1 mem1 := by
    intro mem1 regs1 pos1 x1 hsame1 hrep1 hfr1 hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8 hr9 hr10 hr11 hr13
    have hAux1 := hrep1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have hisOrig_v : mem1 (isOrigBase + v) = if v ∈ S.T₀.V then 1 else 0 := by
      have h1 := hAux1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 v
        (hsame1.vCap_eq.symm ▸ hv_lt)
      simpa only [isOrigBase, auxPtr, vCap, eCap, n0, tM, L_w, hsame1.vCap_eq, hsame1.eCap_eq,
        hsame1.n0_eq, hsame1.tM_eq, hsame1.L_w_eq, hS1_T0] using h1
    have heval_v : (Expr.load (.bin .add (.reg 13) (.reg 3))).eval w
        { mem := mem1, regs := regs1, pos := pos1 } = some (if v ∈ S.T₀.V then 1 else 0) :=
      Expr.eval_load_of_eq (by eval_expr) hisOrig_v
    by_cases hvT : v ∈ S.T₀.V
    · have heval_v1 : (Expr.load (.bin .add (.reg 13) (.reg 3))).eval w
          { mem := mem1, regs := regs1, pos := pos1 } = some 1 := by simpa [hvT] using heval_v
      have hMinUp1 : ∀ S₀, MeetsContract w p idxMinUp (minEdgeUpContract w S₀ x1.vList x1.tOrigList) := by
        rw [hsame1.vList_eq, hsame1.tOrigList_eq]; exact hMinUp
      have hDgDelF1 : ∀ F, MeetsContract w p idxDgDelF (dgDeleteEdgeContract w x1.vCap (fECap x1.eCap x1.n0) F) := by
        rw [hsame1.vCap_eq, hsame1.eCap_eq, hsame1.n0_eq]; exact hDgDelF
      obtain ⟨st2, c_ar, x2, hrun_ar, hregs2, hsame12, hrep2_raw, hfr_ar, hc_ar⟩ :=
        addOrigRoot_call_runs (r := 14) (args := [.reg 0, .reg 3]) (st := { mem := mem1, regs := regs1, pos := pos1 })
          hpAdd (by eval_expr) hw16 (sameStatic_endAddr hsame1 ▸ hend_ltw) hrep1 (hS1_T0.symm ▸ hvT)
          hMinUp1 hDgDelF1 hBFS
      have hrep2 : (LSFRep h).rep b S₂ x2 st2.mem := by simpa only [S₂, hvT, ↓reduceIte] using hrep2_raw
      have hsame2 : SameStaticConcrete x x2 := hsame1.trans hsame12
      have hfr2 : ∀ a, a < b ∨ x.endAddr b ≤ a → st2.mem a = mem a := fun a ha =>
        (hfr_ar a (sameStatic_endAddr hsame1 ▸ ha)).trans (hfr1 a ha)
      obtain ⟨st', c_rest, hrun_rest, hrep', hfr', hphi_eq, hc_rest⟩ :=
        hafter_v st2.mem st2.regs st2.pos x2 hsame2 hrep2 hfr2
          (by rw [hregs2, Function.update_of_ne (by decide)]; exact hr0)
          (by rw [hregs2, Function.update_of_ne (by decide)]; exact hr1)
          (by rw [hregs2, Function.update_of_ne (by decide)]; exact hr2)
          (by rw [hregs2, Function.update_of_ne (by decide)]; exact hr3)
          (by rw [hregs2, Function.update_of_ne (by decide)]; exact hr4)
          (by rw [hregs2, Function.update_of_ne (by decide)]; exact hr5)
          (by rw [hregs2, Function.update_of_ne (by decide)]; exact hr6)
          (by rw [hregs2, Function.update_of_ne (by decide)]; exact hr7)
          (by rw [hregs2, Function.update_of_ne (by decide)]; exact hr8)
          (by rw [hregs2, Function.update_of_ne (by decide)]; exact hr9)
          (by rw [hregs2, Function.update_of_ne (by decide)]; exact hr10)
          (by rw [hregs2, Function.update_of_ne (by decide)]; exact hr11)
      have hcond_run : Runs w p ω
          (.cond (.load (.bin .add (.reg 13) (.reg 3))) (.call 14 idxAddRoot [.reg 0, .reg 3]) .nop)
          { mem := mem1, regs := regs1, pos := pos1 } .normal st2
          ((Expr.load (.bin .add (.reg 13) (.reg 3))).size + c_ar + 1) :=
        runs_cond_iff.mpr ⟨1, c_ar, heval_v1, by simpa using hrun_ar, rfl⟩
      refine ⟨st', _, x2, runs_seq_iff.mpr (Or.inr ⟨st2, _, c_rest, hcond_run, hrun_rest, rfl⟩),
        hsame2, hrep', hfr', ?_⟩
      dsimp only [argsSize, Expr.size] at hc_ar ⊢
      omega
    · have heval_v0 : (Expr.load (.bin .add (.reg 13) (.reg 3))).eval w
          { mem := mem1, regs := regs1, pos := pos1 } = some 0 := by simpa [hvT] using heval_v
      have hrep2 : (LSFRep h).rep b S₂ x1 mem1 := by simpa only [S₂, hvT, ↓reduceIte] using hrep1
      obtain ⟨st', c_rest, hrun_rest, hrep', hfr', hphi_eq, hc_rest⟩ :=
        hafter_v mem1 regs1 pos1 x1 hsame1 hrep2 hfr1 hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8 hr9 hr10 hr11
      have hcond_run : Runs w p ω
          (.cond (.load (.bin .add (.reg 13) (.reg 3))) (.call 14 idxAddRoot [.reg 0, .reg 3]) .nop)
          { mem := mem1, regs := regs1, pos := pos1 } .normal { mem := mem1, regs := regs1, pos := pos1 }
          ((Expr.load (.bin .add (.reg 13) (.reg 3))).size + 1 + 1) :=
        runs_cond_iff.mpr ⟨0, 1, heval_v0, by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
      refine ⟨st', _, x1, runs_seq_iff.mpr (Or.inr ⟨_, _, c_rest, hcond_run, hrun_rest, rfl⟩),
        hsame1, hrep', hfr', ?_⟩
      dsimp only [Expr.size]; omega
  -- Main prefix: load header fields and run the first conditional `addOrigRoot(b, u)`
  have hst0_r : (startState [b, e, u, v] mem pos).regs 0 = b ∧
      (startState [b, e, u, v] mem pos).regs 1 = e ∧
      (startState [b, e, u, v] mem pos).regs 2 = u ∧
      (startState [b, e, u, v] mem pos).regs 3 = v := by simp [startState]
  rcases hst0_r with ⟨hr0, hr1, hr2, hr3⟩
  have hhd_m := hhdr
  have hisOrig_ptr_m : mem (auxPtr + auxOffIsOrigVertPtr) = isOrigBase :=
    hAux.2.2.2.2.2.2.2.2.2.2.1
  have hisOrig_u : mem (isOrigBase + u) = if u ∈ S.T₀.V then 1 else 0 :=
    hAux.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 u hu_lt
  -- Direct prefix state `st0` after the 10 header/aux loads
  have hb24 : b + 24 < 2 ^ w := hb_hdr_ltw
  have haux20 : auxPtr + 20 < 2 ^ w := by dsimp [auxSize, auxHdrSize] at haux_end_ltw; omega
  let st0 : State :=
    { mem := mem
      regs := Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update (Function.update
          (startState [b, e, u, v] mem pos).regs
          4 vCap) 5 eCap) 6 tM) 7 dgGPtr) 8 tPtr) 9 wstrNumPtr) 10 wstrDenPtr)
          11 L_w) 12 auxPtr) 13 isOrigBase
      pos := pos }
  have hr0_0 : st0.regs 0 = b := by dsimp [st0]; simp [hr0]
  have hr0_1 : st0.regs 1 = e := by dsimp [st0]; simp [hr1]
  have hr0_2 : st0.regs 2 = u := by dsimp [st0]; simp [hr2]
  have hr0_3 : st0.regs 3 = v := by dsimp [st0]; simp [hr3]
  have hr0_4 : st0.regs 4 = vCap := by dsimp [st0]; simp
  have hr0_5 : st0.regs 5 = eCap := by dsimp [st0]; simp
  have hr0_6 : st0.regs 6 = tM := by dsimp [st0]; simp
  have hr0_7 : st0.regs 7 = dgGPtr := by dsimp [st0]; simp
  have hr0_8 : st0.regs 8 = tPtr := by dsimp [st0]; simp
  have hr0_9 : st0.regs 9 = wstrNumPtr := by dsimp [st0]; simp
  have hr0_10 : st0.regs 10 = wstrDenPtr := by dsimp [st0]; simp
  have hr0_11 : st0.regs 11 = L_w := by dsimp [st0]; simp
  have hr0_13 : st0.regs 13 = isOrigBase := by dsimp [st0]; simp
  have heval_u : (Expr.load (.bin .add (.reg 13) (.reg 2))).eval w st0 = some (if u ∈ S.T₀.V then 1 else 0) :=
    Expr.eval_load_of_eq (by eval_expr) hisOrig_u
  have htail : ∃ st' c_tail x',
      Runs w p ω
        (.cond (.load (.bin .add (.reg 13) (.reg 2))) (.call 14 idxAddRoot [.reg 0, .reg 2]) .nop ;;
         .cond (.load (.bin .add (.reg 13) (.reg 3))) (.call 14 idxAddRoot [.reg 0, .reg 3]) .nop ;;
         .call 14 idxDgIns [.reg 7, .reg 1, .reg 2, .reg 3] ;;
         .call 14 idxTIns [.reg 8, .reg 4, .reg 5, .reg 6, .reg 1, .reg 2, .reg 3] ;;
         .call 14 idxSetWstr [.reg 9, .reg 10, .reg 1, .reg 11] ;;
         .ret (.const 4))
        st0 (.returned 4) st' c_tail ∧
      SameStaticConcrete x x' ∧
      (LSFRep h).rep b S' x' st'.mem ∧
      (∀ a, a < b ∨ x.endAddr b ≤ a → st'.mem a = mem a) ∧
      c_tail + lsfPhi b x' st'.mem ≤ 50 * L_w + 2290 + lsfPhi b x mem := by
    by_cases huT : u ∈ S.T₀.V
    · have heval_u1 : (Expr.load (.bin .add (.reg 13) (.reg 2))).eval w st0 = some 1 := by
        simpa [huT] using heval_u
      obtain ⟨st1, c_ar1, x1, hrun_ar1, hregs1, hsame1, hrep1_raw, hfr_ar1, hc_ar1⟩ :=
        addOrigRoot_call_runs (r := 14) (args := [.reg 0, .reg 2]) (st := st0)
          hpAdd (by eval_expr) hw16 hend_ltw hrep_orig huT hMinUp hDgDelF hBFS
      have hrep1 : (LSFRep h).rep b S₁ x1 st1.mem := by simpa only [S₁, huT, ↓reduceIte] using hrep1_raw
      obtain ⟨st', c_rest, x', hrun_rest, hsame', hrep', hfr', hc_rest⟩ :=
        hafter_u st1.mem st1.regs st1.pos x1 hsame1 hrep1 (fun a ha => hfr_ar1 a ha)
          (by rw [hregs1, Function.update_of_ne (by decide), hr0_0])
          (by rw [hregs1, Function.update_of_ne (by decide), hr0_1])
          (by rw [hregs1, Function.update_of_ne (by decide), hr0_2])
          (by rw [hregs1, Function.update_of_ne (by decide), hr0_3])
          (by rw [hregs1, Function.update_of_ne (by decide), hr0_4])
          (by rw [hregs1, Function.update_of_ne (by decide), hr0_5])
          (by rw [hregs1, Function.update_of_ne (by decide), hr0_6])
          (by rw [hregs1, Function.update_of_ne (by decide), hr0_7])
          (by rw [hregs1, Function.update_of_ne (by decide), hr0_8])
          (by rw [hregs1, Function.update_of_ne (by decide), hr0_9])
          (by rw [hregs1, Function.update_of_ne (by decide), hr0_10])
          (by rw [hregs1, Function.update_of_ne (by decide), hr0_11])
          (by rw [hregs1, Function.update_of_ne (by decide), hr0_13])
      have hcond1 : Runs w p ω
          (.cond (.load (.bin .add (.reg 13) (.reg 2))) (.call 14 idxAddRoot [.reg 0, .reg 2]) .nop)
          st0 .normal st1 ((Expr.load (.bin .add (.reg 13) (.reg 2))).size + c_ar1 + 1) :=
        runs_cond_iff.mpr ⟨1, c_ar1, heval_u1, by simpa using hrun_ar1, rfl⟩
      refine ⟨st', _, x', runs_seq_iff.mpr (Or.inr ⟨st1, _, c_rest, hcond1, hrun_rest, rfl⟩),
        hsame', hrep', hfr', ?_⟩
      dsimp only [st0, argsSize, Expr.size] at hc_ar1 ⊢; omega
    · have heval_u0 : (Expr.load (.bin .add (.reg 13) (.reg 2))).eval w st0 = some 0 := by
        simpa [huT] using heval_u
      have hrep1 : (LSFRep h).rep b S₁ x st0.mem := by
        simpa only [S₁, huT, ↓reduceIte] using hrep_orig
      obtain ⟨st', c_rest, x', hrun_rest, hsame', hrep', hfr', hc_rest⟩ :=
        hafter_u st0.mem st0.regs st0.pos x (SameStaticConcrete.refl x) hrep1 (fun _ _ => rfl)
          hr0_0 hr0_1 hr0_2 hr0_3 hr0_4 hr0_5 hr0_6 hr0_7 hr0_8 hr0_9 hr0_10 hr0_11 hr0_13
      have hcond1 : Runs w p ω
          (.cond (.load (.bin .add (.reg 13) (.reg 2))) (.call 14 idxAddRoot [.reg 0, .reg 2]) .nop)
          st0 .normal st0 ((Expr.load (.bin .add (.reg 13) (.reg 2))).size + 1 + 1) :=
        runs_cond_iff.mpr ⟨0, 1, heval_u0, by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
      refine ⟨st', _, x', runs_seq_iff.mpr (Or.inr ⟨st0, _, c_rest, hcond1, hrun_rest, rfl⟩),
        hsame', hrep', hfr', ?_⟩
      dsimp only [st0, Expr.size] at hc_rest ⊢; omega
  rcases htail with ⟨st', c_tail, x', hrun_tail, hsame', hrep', hfr', hc_tail⟩
  suffices hmain : ∃ o st'' c,
      Runs w p ω (lsfInsertUpdateProc idxAddRoot idxDgIns idxTIns idxSetWstr)
        (startState [b, e, u, v] mem pos) o st'' c ∧
      (o = .returned 4 ∧ st'' = st') ∧
      0 + c ≤ c_tail + 110 by
    rcases hmain with ⟨_, st'', c, hrun, ⟨rfl, hst⟩, hc⟩
    exact ⟨st', c, x', hst ▸ hrun, hsame', hrep', hfr', by omega⟩
  dsimp only [lsfInsertUpdateProc]
  refine runs_seq_assign_le (v := vCap)
    (Expr.eval_load_of_eq (show Expr.eval w (startState [b, e, u, v] mem pos)
      (.bin .add (.reg 0) (.const lsfOffVCap)) = some (b + lsfOffVCap) by
        simp only [Expr.eval, BinOp.eval, lsfOffVCap, hr0,
          show 0 < 2 ^ w by omega, show b + 0 < 2 ^ w by omega, ↓reduceIte]) hhd_m.1) ?_
  refine runs_seq_assign_le (v := eCap) (Expr.eval_load_of_eq (by dsimp [lsfOffECap]; eval_expr) hhd_m.2.1) ?_
  refine runs_seq_assign_le (v := tM) (Expr.eval_load_of_eq (by dsimp [lsfOffTM]; eval_expr) hhd_m.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) ?_
  refine runs_seq_assign_le (v := dgGPtr) (Expr.eval_load_of_eq (by dsimp [lsfOffDgGPtr]; eval_expr) hhd_m.2.2.2.2.1) ?_
  refine runs_seq_assign_le (v := tPtr) (Expr.eval_load_of_eq (by dsimp [lsfOffTPtr]; eval_expr) hhd_m.2.2.2.2.2.1) ?_
  refine runs_seq_assign_le (v := wstrNumPtr) (Expr.eval_load_of_eq (by dsimp [lsfOffWstrNumPtr]; eval_expr) hhd_m.2.2.2.2.2.2.2.2.2.1) ?_
  refine runs_seq_assign_le (v := wstrDenPtr) (Expr.eval_load_of_eq (by dsimp [lsfOffWstrDenPtr]; eval_expr) hhd_m.2.2.2.2.2.2.2.2.2.2.1) ?_
  refine runs_seq_assign_le (v := L_w) (Expr.eval_load_of_eq (by dsimp [lsfOffLW]; eval_expr) hhd_m.2.2.2.2.2.2.2.2.2.2.2.1) ?_
  refine runs_seq_assign_le (v := auxPtr) (Expr.eval_load_of_eq (by dsimp [lsfOffAuxPtr]; eval_expr) hhd_m.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) ?_
  refine runs_seq_assign_le (v := isOrigBase) (Expr.eval_load_of_eq (by dsimp [auxOffIsOrigVertPtr]; eval_expr) hisOrig_ptr_m) ?_
  refine ⟨.returned 4, st', c_tail, hrun_tail, ⟨rfl, rfl⟩, ?_⟩
  dsimp only [Expr.size]; clear * -; omega

/-! ## Verification of `lsfDeleteUpdateProc` -/

theorem lsfDeleteUpdate_runs
    {w h b e idxAddRoot idxMinUp idxDgDelF idxBFS idxDgDelG idxTDel : ℕ}
    {p : Program} {ω : ℕ → Bool} {S : LSFState} {x : LSFConcrete} {mem : ℕ → ℕ} {pos : ℕ}
    (hw16 : 16 ≤ 2 ^ w) (hend_ltw : x.endAddr b < 2 ^ w)
    (hrep : (LSFRep h).rep b S x mem)
    (he_inG : e ∈ S.G.E)
    (hpAdd : p.procs[idxAddRoot]? = some (addOrigRootProc idxMinUp idxDgDelF idxBFS))
    (hMinUp : ∀ S₀, MeetsContract w p idxMinUp (minEdgeUpContract w S₀ x.vList x.tOrigList))
    (hDgDelF : ∀ F, MeetsContract w p idxDgDelF (dgDeleteEdgeContract w x.vCap (fECap x.eCap x.n0) F))
    (hBFS : ∀ F, MeetsContract w p idxBFS (splitCompBFSContract w F))
    (hDgDelG : ∀ G, MeetsContract w p idxDgDelG (dgDeleteEdgeContract w x.vCap x.eCap G))
    (hTDel : ∀ G T_cur, MeetsContract w p idxTDel
      (lsfTBlockDeleteContract w x.vCap x.eCap x.tM G T_cur S.T₀ S.π x.tOrigList)) :
    ∃ st' c x',
      Runs w p ω (lsfDeleteUpdateProc idxAddRoot idxDgDelG idxTDel)
        (startState [b, e] mem pos) (.returned 2) st' c ∧
      SameStaticConcrete x x' ∧
      (LSFRep h).rep b (applyLSFUpdate S (.delete e)) x' st'.mem ∧
      (∀ a, a < b ∨ x.endAddr b ≤ a → st'.mem a = mem a) ∧
      c + lsfPhi b x' st'.mem ≤ 2400 + lsfPhi b x mem := by
  classical
  set vCap := x.vCap; set eCap := x.eCap; set n0 := x.n0; set tM := x.tM; set L_w := x.L_w
  set dgGPtr := lsfDgGPtr b
  set tPtr := lsfTBlockPtr b vCap eCap
  set dgFPtr := lsfDgFPtr b vCap eCap tM
  set fAncPtr := lsfFAncPtr b vCap eCap n0 tM
  set wPtr := lsfWBlockPtr b vCap eCap n0 tM
  set auxPtr := lsfAuxPtr b vCap eCap n0 tM L_w
  set wstrNumPtr := lsfWstrNumPtr b vCap eCap n0 tM
  set wstrDenPtr := lsfWstrDenPtr b vCap eCap n0 tM L_w
  set origBase := auxOrigVertBase auxPtr vCap n0
  have hlay := lsfBlock_disjoint b vCap eCap n0 tM L_w
  have hend_eq : x.endAddr b = lsfEndAddr b vCap eCap n0 tM L_w := rfl
  have hrep_orig := hrep
  rcases hrep with ⟨hxH, hh1, hLin, hLw, hkn, hkeq, hInv, hn0, hm0, htM, hnv, hme, htn, hn1,
    hvT_lt, heG_lt, hhdr, hdgG, hT, hdgF, hFAnc, hW, hwstr, hAux⟩
  set u := S.G.tail e
  set v := S.G.head e
  set uOrig := S.origVert u
  set vOrig := S.origVert v
  have huG : u ∈ S.G.V := (hInv.hG_val e he_inG).1
  have hvG : v ∈ S.G.V := (hInv.hG_val e he_inG).2
  have he_cap : e < eCap := hdgG.2.2.1 e he_inG
  have hu_lt : u < vCap := hdgG.2.1 u huG
  have hv_lt : v < vCap := hdgG.2.1 v hvG
  have hfactor := applyLSFUpdate_delete_eq hInv he_inG
  set S₁ : LSFState := { S with R₀_base := insert uOrig S.R₀_base }
  set S₂ : LSFState := { S₁ with R₀_base := insert vOrig S₁.R₀_base }
  set S' : LSFState := applyLSFUpdate S (.delete e)
  have huT : uOrig ∈ S.T₀.V := hfactor.1
  have hvT : vOrig ∈ S.T₀.V := hfactor.2.1
  have hInv' : LSFStructInv S' := hfactor.2.2.2.2.1
  have hRorig' : S'.R_orig = S₂.R_orig := hfactor.2.2.2.2.2.2.1
  have hR' : S'.R = S₂.R := hfactor.2.2.2.2.2.2.2.1
  have hRF' : S'.RF = S₂.RF := hfactor.2.2.2.2.2.2.2.2
  have huOrig_lt : uOrig < vCap := hvT_lt uOrig huT
  have hvOrig_lt : vOrig < vCap := hvT_lt vOrig hvT
  have hb_hdr_ltw : b + lsfHdrSize < 2 ^ w := by
    have := hlay.1; have := hlay.2.1; have := hlay.2.2.1; have := hlay.2.2.2.1
    have := hlay.2.2.2.2.1; have := hlay.2.2.2.2.2.1; have := hlay.2.2.2.2.2.2.1
    have := hlay.2.2.2.2.2.2.2.1; have := hlay.2.2.2.2.2.2.2.2; omega
  have hdgG_end_ltw : dgGPtr + dynGraphSize vCap eCap < 2 ^ w := by
    have := hlay.2.1; have := hlay.2.2.1; have := hlay.2.2.2.1
    have := hlay.2.2.2.2.1; have := hlay.2.2.2.2.2.1; have := hlay.2.2.2.2.2.2.1
    have := hlay.2.2.2.2.2.2.2.1; have := hlay.2.2.2.2.2.2.2.2; omega
  have htPtr_end_ltw : tPtr + tBlockSize vCap eCap tM < 2 ^ w := by
    have := hlay.2.2.1; have := hlay.2.2.2.1; have := hlay.2.2.2.2.1
    have := hlay.2.2.2.2.2.1; have := hlay.2.2.2.2.2.2.1; have := hlay.2.2.2.2.2.2.2.1
    have := hlay.2.2.2.2.2.2.2.2; omega
  have haux_end_ltw : auxPtr + auxSize vCap n0 < 2 ^ w := by
    have := hlay.2.2.2.2.2.2.1; have := hlay.2.2.2.2.2.2.2.1
    have := hlay.2.2.2.2.2.2.2.2; omega
  have hvCap_ltw : vCap < 2 ^ w := by dsimp [dynGraphSize] at hdgG_end_ltw; omega
  have heCap_ltw : eCap < 2 ^ w := by dsimp [dynGraphSize] at hdgG_end_ltw; omega
  have htM_ltw : tM < 2 ^ w := by omega
  have he_ltw : e < 2 ^ w := by omega
  have hu_ltw : u < 2 ^ w := by omega
  have hv_ltw : v < 2 ^ w := by omega
  have huOrig_ltw : uOrig < 2 ^ w := by omega
  have hvOrig_ltw : vOrig < 2 ^ w := by omega
  have horig_end_ltw : origBase + vCap < 2 ^ w := by
    dsimp [origBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase, auxT0DepthBase,
      auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase, auxSize] at haux_end_ltw ⊢
    omega
  -- Read endpoints `u, v` from `dgG`
  set s_u := mem (dgETailSlotBase dgGPtr vCap eCap + e)
  set s_v := mem (dgEHeadSlotBase dgGPtr vCap eCap + e)
  have hsu_eq : s_u = mem (dgExtToIntBase dgGPtr vCap + u) :=
    (hdgG.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e he_inG).1
  have hsv_eq : s_v = mem (dgExtToIntBase dgGPtr vCap + v) :=
    (hdgG.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e he_inG).2
  have hsu_lt : s_u < vCap := by rw [hsu_eq]; exact hdgG.2.1 _ (hdgG.2.2.2.2.2.2.2.2.2.1 u huG).1
  have hsv_lt : s_v < vCap := by rw [hsv_eq]; exact hdgG.2.1 _ (hdgG.2.2.2.2.2.2.2.2.2.1 v hvG).1
  have hu_mem : mem (dgIntToExtBase dgGPtr vCap + s_u) = u := by
    rw [hsu_eq]; exact (hdgG.2.2.2.2.2.2.2.2.2.1 u huG).2
  have hv_mem : mem (dgIntToExtBase dgGPtr vCap + s_v) = v := by
    rw [hsv_eq]; exact (hdgG.2.2.2.2.2.2.2.2.2.1 v hvG).2
  have horig_ptr_m : mem (auxPtr + auxOffOrigVertPtr) = origBase :=
    hAux.2.2.2.2.2.2.2.2.2.1
  have huOrig_m : mem (origBase + u) = uOrig :=
    hAux.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 u huG hu_lt
  have hvOrig_m : mem (origBase + v) = vOrig :=
    hAux.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 v hvG hv_lt
  have hdg_bases_ltw : dgIntToExtBase dgGPtr vCap + vCap < 2 ^ w ∧
      dgETailSlotBase dgGPtr vCap eCap + eCap < 2 ^ w ∧
      dgEHeadSlotBase dgGPtr vCap eCap + eCap < 2 ^ w := by
    dsimp [dgIntToExtBase, dgETailSlotBase, dgEHeadSlotBase, dynGraphSize] at hdgG_end_ltw ⊢
    omega
  have hb24 : b + 24 < 2 ^ w := hb_hdr_ltw
  have haux20 : auxPtr + 20 < 2 ^ w := by dsimp [auxSize, auxHdrSize] at haux_end_ltw; omega
  have h4v : 4 * vCap < 2 ^ w := by dsimp [dynGraphSize] at hdgG_end_ltw; omega
  have h7v : 7 * vCap < 2 ^ w := by dsimp [dynGraphSize] at hdgG_end_ltw; omega
  have h3e : 3 * eCap < 2 ^ w := by dsimp [dynGraphSize] at hdgG_end_ltw; omega
  have h4e : 4 * eCap < 2 ^ w := by dsimp [dynGraphSize] at hdgG_end_ltw; omega
  have hg4 : dgGPtr + 4 < 2 ^ w := by dsimp [dynGraphSize] at hdgG_end_ltw; omega
  have hg47 : dgGPtr + 4 + 7 * vCap < 2 ^ w := by dsimp [dynGraphSize] at hdgG_end_ltw; omega
  have hg473 : dgGPtr + 4 + 7 * vCap + 3 * eCap < 2 ^ w := by dsimp [dynGraphSize] at hdgG_end_ltw; omega
  have hg474 : dgGPtr + 4 + 7 * vCap + 4 * eCap < 2 ^ w := by dsimp [dynGraphSize] at hdgG_end_ltw; omega
  have hr0 : (startState [b, e] mem pos).regs 0 = b := by simp [startState]
  have hr1 : (startState [b, e] mem pos).regs 1 = e := by simp [startState]
  let st0 : State :=
    { mem := mem
      regs := Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update
          (startState [b, e] mem pos).regs
          2 vCap) 3 eCap) 4 tM) 5 dgGPtr) 6 tPtr) 7 auxPtr) 8 origBase)
          9 (dgIntToExtBase dgGPtr vCap)) 10 (dgETailSlotBase dgGPtr vCap eCap))
          11 (dgEHeadSlotBase dgGPtr vCap eCap)) 12 u) 13 v) 14 uOrig) 15 vOrig
      pos := pos }
  have hr0_0 : st0.regs 0 = b := by dsimp [st0]; simp [hr0]
  have hr0_1 : st0.regs 1 = e := by dsimp [st0]; simp [hr1]
  have hr0_2 : st0.regs 2 = vCap := by dsimp [st0]; simp
  have hr0_3 : st0.regs 3 = eCap := by dsimp [st0]; simp
  have hr0_4 : st0.regs 4 = tM := by dsimp [st0]; simp
  have hr0_5 : st0.regs 5 = dgGPtr := by dsimp [st0]; simp
  have hr0_6 : st0.regs 6 = tPtr := by dsimp [st0]; simp
  have hr0_12 : st0.regs 12 = u := by dsimp [st0]; simp
  have hr0_13 : st0.regs 13 = v := by dsimp [st0]; simp
  have hr0_14 : st0.regs 14 = uOrig := by dsimp [st0]; simp
  have hr0_15 : st0.regs 15 = vOrig := by dsimp [st0]; simp
  -- Call 1: addOrigRoot(b, uOrig)
  obtain ⟨st1, c1, x1, hrun1, hregs1, hsame1, hrep1, hfr1, hc1⟩ :=
    addOrigRoot_call_runs (r := 16) (args := [.reg 0, .reg 14]) (st := st0)
      hpAdd (by eval_expr) hw16 hend_ltw hrep_orig huT hMinUp hDgDelF hBFS
  -- Call 2: addOrigRoot(b, vOrig)
  have hMinUp1 : ∀ S₀, MeetsContract w p idxMinUp (minEdgeUpContract w S₀ x1.vList x1.tOrigList) := by
    rw [hsame1.vList_eq, hsame1.tOrigList_eq]; exact hMinUp
  have hDgDelF1 : ∀ F, MeetsContract w p idxDgDelF (dgDeleteEdgeContract w x1.vCap (fECap x1.eCap x1.n0) F) := by
    rw [hsame1.vCap_eq, hsame1.eCap_eq, hsame1.n0_eq]; exact hDgDelF
  have hargs2 : evalArgs w st1 [.reg 0, .reg 15] = some [b, vOrig] := by
    have h0 : st1.regs 0 = b := by rw [hregs1, Function.update_of_ne (by decide), hr0_0]
    have h15 : st1.regs 15 = vOrig := by rw [hregs1, Function.update_of_ne (by decide), hr0_15]
    eval_expr
  obtain ⟨st2, c2, x2, hrun2, hregs2, hsame12, hrep2, hfr2, hc2⟩ :=
    addOrigRoot_call_runs (r := 16) (args := [.reg 0, .reg 15]) (st := st1)
      hpAdd hargs2 hw16 (sameStatic_endAddr hsame1 ▸ hend_ltw) hrep1 hvT hMinUp1 hDgDelF1 hBFS
  have hsame2 : SameStaticConcrete x x2 := hsame1.trans hsame12
  have hx2_vc : x2.vCap = vCap := hsame2.vCap_eq
  have hx2_ec : x2.eCap = eCap := hsame2.eCap_eq
  have hx2_n0 : x2.n0 = n0 := hsame2.n0_eq
  have hx2_tM : x2.tM = tM := hsame2.tM_eq
  have hx2_Lw : x2.L_w = L_w := hsame2.L_w_eq
  have hx2_tL : x2.tOrigList = x.tOrigList := hsame2.tOrigList_eq
  have hrep2_copy := hrep2
  rcases hrep2 with ⟨hxH2, hh1_2, hLin2, hLw2, hkn2, hkeq2, _, hn0_2, hm0_2, htM2, hnv2, hme2, htn2,
    hn1_2, hvT_lt2, heG_lt2, hhdr2, hdgG2, hT2, hdgF2, hFAnc2, hW2, hwstr2, hAux2⟩
  suffices hmain : ∃ o st' c,
      Runs w p ω (lsfDeleteUpdateProc idxAddRoot idxDgDelG idxTDel)
        (startState [b, e] mem pos) o st' c ∧
      (o = .returned 2 ∧ (LSFRep h).rep b S' x2 st'.mem ∧
        (∀ a, a < b ∨ x.endAddr b ≤ a → st'.mem a = mem a) ∧
        lsfPhi b x2 st'.mem = lsfPhi b x2 st2.mem) ∧
      0 + c ≤ c1 + c2 + 1850 by
    rcases hmain with ⟨_, st', c, hrun, ⟨rfl, hrep', hfr', hphi_eq⟩, hc⟩
    refine ⟨st', c, x2, hrun, hsame2, hrep', hfr', ?_⟩
    dsimp only [st0, argsSize, Expr.size] at hc1 hc2
    clear * - hc hc1 hc2 hphi_eq
    omega
  dsimp only [lsfDeleteUpdateProc]
  refine runs_seq_assign_le (v := vCap)
    (Expr.eval_load_of_eq (show Expr.eval w (startState [b, e] mem pos)
      (.bin .add (.reg 0) (.const lsfOffVCap)) = some (b + lsfOffVCap) by
        simp only [Expr.eval, BinOp.eval, lsfOffVCap, hr0,
          show 0 < 2 ^ w by omega, show b + 0 < 2 ^ w by omega, ↓reduceIte]) hhdr.1) ?_
  refine runs_seq_assign_le (v := eCap) (Expr.eval_load_of_eq (by dsimp [lsfOffECap]; eval_expr) hhdr.2.1) ?_
  refine runs_seq_assign_le (v := tM) (Expr.eval_load_of_eq (by dsimp [lsfOffTM]; eval_expr) hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) ?_
  refine runs_seq_assign_le (v := dgGPtr) (Expr.eval_load_of_eq (by dsimp [lsfOffDgGPtr]; eval_expr) hhdr.2.2.2.2.1) ?_
  refine runs_seq_assign_le (v := tPtr) (Expr.eval_load_of_eq (by dsimp [lsfOffTPtr]; eval_expr) hhdr.2.2.2.2.2.1) ?_
  refine runs_seq_assign_le (v := auxPtr) (Expr.eval_load_of_eq (by dsimp [lsfOffAuxPtr]; eval_expr) hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) ?_
  refine runs_seq_assign_le (v := origBase) (Expr.eval_load_of_eq (by dsimp [auxOffOrigVertPtr]; eval_expr) horig_ptr_m) ?_
  refine runs_seq_assign_le (v := dgIntToExtBase dgGPtr vCap) (by dsimp [dgIntToExtBase]; eval_expr) ?_
  refine runs_seq_assign_le (v := dgETailSlotBase dgGPtr vCap eCap) (by dsimp [dgETailSlotBase]; eval_expr) ?_
  refine runs_seq_assign_le (v := dgEHeadSlotBase dgGPtr vCap eCap) (by dsimp [dgEHeadSlotBase]; eval_expr) ?_
  refine runs_seq_assign_le (v := u) ?_ ?_
  · refine Expr.eval_load_of_eq (Expr.eval_bin (by eval_expr)
      (Expr.eval_load_of_eq (v := s_u) (by eval_expr) rfl) (by dsimp [BinOp.eval]; omega)) hu_mem
  refine runs_seq_assign_le (v := v) ?_ ?_
  · refine Expr.eval_load_of_eq (Expr.eval_bin (by eval_expr)
      (Expr.eval_load_of_eq (v := s_v) (by eval_expr) rfl) (by dsimp [BinOp.eval]; omega)) hv_mem
  refine runs_seq_assign_le (v := uOrig) (Expr.eval_load_of_eq (by eval_expr) huOrig_m) ?_
  refine runs_seq_assign_le (v := vOrig) (Expr.eval_load_of_eq (by eval_expr) hvOrig_m) ?_
  refine runs_seq_of_runs_le' hrun1 ?_
  refine runs_seq_of_runs_le' hrun2 ?_
  have hr2_1 : st2.regs 1 = e := by rw [hregs2, Function.update_of_ne (by decide), hregs1, Function.update_of_ne (by decide), hr0_1]
  have hr2_2 : st2.regs 2 = vCap := by rw [hregs2, Function.update_of_ne (by decide), hregs1, Function.update_of_ne (by decide), hr0_2]
  have hr2_3 : st2.regs 3 = eCap := by rw [hregs2, Function.update_of_ne (by decide), hregs1, Function.update_of_ne (by decide), hr0_3]
  have hr2_4 : st2.regs 4 = tM := by rw [hregs2, Function.update_of_ne (by decide), hregs1, Function.update_of_ne (by decide), hr0_4]
  have hr2_5 : st2.regs 5 = dgGPtr := by rw [hregs2, Function.update_of_ne (by decide), hregs1, Function.update_of_ne (by decide), hr0_5]
  have hr2_6 : st2.regs 6 = tPtr := by rw [hregs2, Function.update_of_ne (by decide), hregs1, Function.update_of_ne (by decide), hr0_6]
  have hr2_12 : st2.regs 12 = u := by rw [hregs2, Function.update_of_ne (by decide), hregs1, Function.update_of_ne (by decide), hr0_12]
  have hr2_13 : st2.regs 13 = v := by rw [hregs2, Function.update_of_ne (by decide), hregs1, Function.update_of_ne (by decide), hr0_13]
  have hdgG2' : DynGraphAt st2.mem dgGPtr vCap eCap S₂.G := by simpa only [hx2_vc, hx2_ec] using hdgG2
  have hpre_del : (dgDeleteEdgeContract w vCap eCap S₂.G).pre [dgGPtr, e] st2.mem :=
    ⟨dgGPtr, e, rfl, hw16, hdgG_end_ltw, hdgG2'⟩
  refine runs_seq_call_le (hDgDelG S₂.G) (by eval_expr)
    (by intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl <;> omega)
    hpre_del ?_
  intro ret3 mem3 pos3 hpost3
  rcases hpost3 with ⟨_, _, hEq3, _, hdgG3_raw, hfr_dgG⟩
  simp only [List.cons.injEq, and_true] at hEq3
  rcases hEq3 with ⟨rfl, rfl⟩
  have hdgG3 : DynGraphAt mem3 dgGPtr vCap eCap S'.G := by
    have he2 : e ∈ S₂.G.E := he_inG
    simpa only [he2, ↓reduceIte, S', applyLSFUpdate] using hdgG3_raw
  have hT2' : TBlockAt st2.mem tPtr vCap eCap tM S₂.G S₂.T_cur S.T₀ S.π x.tOrigList := by
    simpa only [hx2_vc, hx2_ec, hx2_tM, hx2_tL, tPtr] using hT2
  have hT3_pre : TBlockAt mem3 tPtr vCap eCap tM S₂.G S₂.T_cur S.T₀ S.π x.tOrigList :=
    hT2'.of_agree fun a ha1 _ => hfr_dgG a (Or.inr (by omega))
  have hpre_tDel : (lsfTBlockDeleteContract w vCap eCap tM S₂.G S₂.T_cur S.T₀ S.π x.tOrigList).pre
      [tPtr, vCap, eCap, tM, e, u, v] mem3 :=
    ⟨tPtr, e, u, v, rfl, hw16, htPtr_end_ltw, hInv.hG_val, he_inG, rfl, rfl, he_cap, hT3_pre⟩
  refine runs_seq_call_le (hTDel S₂.G S₂.T_cur) (by eval_expr)
    (by intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    hpre_tDel ?_
  intro ret4 mem4 pos4 hpost4
  rcases hpost4 with ⟨_, _, _, _, hEq4, _, hT4_raw, hfr_T⟩
  simp only [List.cons.injEq, true_and, and_true] at hEq4
  rcases hEq4 with ⟨rfl, rfl, rfl, rfl⟩
  have hfr_34_out : ∀ a, a < dgGPtr ∨ dgFPtr ≤ a → mem4 a = st2.mem a := fun a ha => by
    rcases ha with h | h
    · exact (hfr_T a (Or.inl (by omega))).trans (hfr_dgG a (Or.inl h))
    · exact (hfr_T a (Or.inr (by omega))).trans (hfr_dgG a (Or.inr (by omega)))
  have hfr_all : ∀ a, a < b ∨ x.endAddr b ≤ a → mem4 a = mem a := fun a ha =>
    (hfr_34_out a (by rcases ha with h | h <;> [left; right] <;> omega)).trans
      ((hfr2 a (sameStatic_endAddr hsame1 ▸ ha)).trans (hfr1 a ha))
  have hhdr4 : lsfHeaderAt mem4 b S' x2 := by
    have h1 : lsfHeaderAt mem4 b S₂ x2 := hhdr2.of_agree fun a _ ha2 => hfr_34_out a (Or.inl (by omega))
    have hr0' : S'.r₀ = S₂.r₀ := rfl
    simpa only [lsfHeaderAt, hR', hr0'] using h1
  have hdgG4 : DynGraphAt mem4 (lsfDgGPtr b) x2.vCap x2.eCap S'.G := by
    rw [hx2_vc, hx2_ec]
    exact hdgG3.of_agree fun a _ ha2 => hfr_T a (Or.inl (by omega))
  have hT4 : TBlockAt mem4 (lsfTBlockPtr b x2.vCap x2.eCap) x2.vCap x2.eCap x2.tM
      S'.G S'.T_cur S'.T₀ S'.π x2.tOrigList := by
    rw [hx2_vc, hx2_ec, hx2_tM, hx2_tL]; exact hT4_raw
  have hdgF4 : DynGraphAt mem4 (lsfDgFPtr b x2.vCap x2.eCap x2.tM) x2.vCap (fECap x2.eCap x2.n0) S'.RF.F := by
    rw [hRF']
    exact hdgF2.of_agree fun a ha1 _ => by
      rw [hx2_vc, hx2_ec, hx2_tM] at ha1; exact hfr_34_out a (Or.inr ha1)
  have hFAnc4 : FAncAt mem4 (lsfFAncPtr b x2.vCap x2.eCap x2.n0 x2.tM) x2.vCap S'.RF
      x2.rList x2.compId x2.compRoot x2.compSize x2.activeCids := by
    rw [hRF']
    exact hFAnc2.of_agree fun a ha1 _ => by
      rw [hx2_vc, hx2_ec, hx2_n0, hx2_tM] at ha1; exact hfr_34_out a (Or.inr (by omega))
  have hW4 : WBlockAt mem4 (lsfWBlockPtr b x2.vCap x2.eCap x2.n0 x2.tM) x2.n0 S'.W_init
      (forestGivenRoots S'.T₀ S'.r₀ (upClosure (hldAuxTree S'.T₀ S'.r₀) S'.r₀ S'.R₀_init) S'.π) :=
    hW2.of_agree fun a ha1 _ => by
      rw [hx2_vc, hx2_ec, hx2_n0, hx2_tM] at ha1; exact hfr_34_out a (Or.inr (by omega))
  have hwstr4 : WstrAt mem4 (lsfWstrNumPtr b x2.vCap x2.eCap x2.n0 x2.tM)
      (lsfWstrDenPtr b x2.vCap x2.eCap x2.n0 x2.tM x2.L_w) x2.eCap x2.h x2.L_w S'.G S'.wstr := by
    have hw4_S2 : WstrAt mem4 (lsfWstrNumPtr b x2.vCap x2.eCap x2.n0 x2.tM)
        (lsfWstrDenPtr b x2.vCap x2.eCap x2.n0 x2.tM x2.L_w) x2.eCap x2.h x2.L_w S₂.G S₂.wstr :=
      hwstr2.of_agree
        (fun a ha1 _ => by rw [hx2_vc, hx2_ec, hx2_n0, hx2_tM] at ha1; exact hfr_34_out a (Or.inr (by omega)))
        (fun a ha1 _ => by rw [hx2_vc, hx2_ec, hx2_n0, hx2_tM, hx2_Lw] at ha1; exact hfr_34_out a (Or.inr (by omega)))
    exact ⟨hw4_S2.1, hw4_S2.2.1, fun f hf => hw4_S2.2.2 f (Finset.mem_of_mem_erase hf)⟩
  have hAux4 : AuxAt mem4 (lsfAuxPtr b x2.vCap x2.eCap x2.n0 x2.tM x2.L_w) x2.vCap x2.n0 x2.tM S'
      x2.tOrigList x2.vList x2.t0Parent x2.t0ParentTreeIdx x2.t0Depth x2.thParent x2.upV x2.upMinIdx := by
    have hAux_m4 : AuxAt mem4 (lsfAuxPtr b x2.vCap x2.eCap x2.n0 x2.tM x2.L_w) x2.vCap x2.n0 x2.tM S₂
        x2.tOrigList x2.vList x2.t0Parent x2.t0ParentTreeIdx x2.t0Depth x2.thParent x2.upV x2.upMinIdx :=
      hAux2.of_agree (fun a ha1 _ => by
        rw [hx2_vc, hx2_ec, hx2_n0, hx2_tM, hx2_Lw] at ha1; exact hfr_34_out a (Or.inr (by omega))) hvT_lt2
    have hGV' : S'.G.V = S₂.G.V := rfl
    have hT0' : S'.T₀ = S₂.T₀ := rfl
    have hr0' : S'.r₀ = S₂.r₀ := rfl
    have hpi' : S'.π = S₂.π := rfl
    have hTH' : S'.TH = S₂.TH := rfl
    have horig' : S'.origVert = S₂.origVert := rfl
    simpa only [AuxAt, hGV', hT0', hr0', hpi', hTH', horig'] using hAux_m4
  have hrep4 : (LSFRep h).rep b S' x2 mem4 :=
    ⟨hxH2, hh1_2, hLin2, hLw2, hkn2, hkeq2, hInv', hn0_2, hm0_2, htM2, hnv2, hme2, htn2,
      hn1_2, hvT_lt2, heG_lt2, hhdr4, hdgG4, hT4, hdgF4, hFAnc4, hW4, hwstr4, hAux4⟩
  have hphi_eq : lsfPhi b x2 mem4 = lsfPhi b x2 st2.mem := by
    rw [lsfPhi_eq_semantic hrep4, lsfPhi_eq_semantic hrep2_copy, hRorig', hRF']
  refine runs_ret_le (v := 2) (by eval_expr) ⟨rfl, hrep4, hfr_all, hphi_eq⟩ ?_
  have hc3 : (dgDeleteEdgeContract w vCap eCap S₂.G).cost [dgGPtr, e] st2.mem = 450 := rfl
  have hc4 : (lsfTBlockDeleteContract w vCap eCap tM S₂.G S₂.T_cur S.T₀ S.π x.tOrigList).cost
      [tPtr, vCap, eCap, tM, e, u, v] mem3 = 1100 := rfl
  rw [hc3, hc4]; dsimp only [argsSize, Expr.size]; clear * -; omega

end

end MinCostFlow.LSF.Program
