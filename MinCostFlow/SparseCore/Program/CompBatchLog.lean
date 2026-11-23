module

public import MinCostFlow.SparseCore.Program.CompCutLog
public import MinCostFlow.LSF.Program.LSFModule
import Mathlib.Tactic.Linarith

/-!
# Pre-Batch Forest-Cut Logger for Single Component Updates (`CompBatchLog`)

Defines `compPreLogProc` (`args = [hWin, updPtr, rootsBuf, fDelBuf, cntPtr]`, returning `0`):
dispatches on the tag of a single encoded update `u_c` at `updPtr` and runs `compLogAddOrigRootProc`
on the exact vertices that `lsfApplyBatchProc` will close in `T_H`, recording every `(cutE, newRoot)`
forest cut in order BEFORE calling `lsfApplyBatchProc`.

Because `applyLSFUpdate S_pre u_c = applyLSFUpdate S u_c`, the subsequent call to
`lsfApplyBatchProc` hits the `O(1)` fast path of `addOrigRootProc`, performs no further forest
edge deletions, and reaches the exact target state `applyLSFUpdate S u_c`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## 1. Pre-log procedure -/

def compPreLogInsStmt (bLogAdd : ℕ) : Stmt :=
  .assign 7 (.load (.bin .add (.reg 1) (.const 2))) ;;
  .assign 8 (.load (.bin .add (.reg 1) (.const 3))) ;;
  .assign 9 (.load (.bin .add (.reg 6) (.const auxOffIsOrigVertPtr))) ;;
  .cond (.load (.bin .add (.reg 9) (.reg 7)))
    (.call 10 bLogAdd [.reg 0, .reg 7, .reg 2, .reg 3, .reg 4]) .nop ;;
  .cond (.load (.bin .add (.reg 9) (.reg 8)))
    (.call 10 bLogAdd [.reg 0, .reg 8, .reg 2, .reg 3, .reg 4]) .nop

def compPreLogDelStmt (bLogAdd : ℕ) : Stmt :=
  .assign 7 (.load (.bin .add (.reg 1) (.const 1))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const lsfOffVCap))) ;;
  .assign 9 (.load (.bin .add (.reg 0) (.const lsfOffECap))) ;;
  .assign 10 (.load (.bin .add (.reg 0) (.const lsfOffDgGPtr))) ;;
  .assign 11 (.load (.bin .add (.reg 6) (.const auxOffOrigVertPtr))) ;;
  .assign 12 (.bin .add (.bin .add (.reg 10) (.const 4)) (.bin .mul (.const 4) (.reg 8))) ;;
  .assign 13 (.bin .add (.bin .add (.bin .add (.reg 10) (.const 4)) (.bin .mul (.const 7) (.reg 8)))
    (.bin .mul (.const 3) (.reg 9))) ;;
  .assign 14 (.bin .add (.bin .add (.bin .add (.reg 10) (.const 4)) (.bin .mul (.const 7) (.reg 8)))
    (.bin .mul (.const 4) (.reg 9))) ;;
  .assign 15 (.load (.bin .add (.reg 11) (.load (.bin .add (.reg 12) (.load (.bin .add (.reg 13) (.reg 7))))))) ;;
  .assign 16 (.load (.bin .add (.reg 11) (.load (.bin .add (.reg 12) (.load (.bin .add (.reg 14) (.reg 7))))))) ;;
  .call 17 bLogAdd [.reg 0, .reg 15, .reg 2, .reg 3, .reg 4] ;;
  .call 17 bLogAdd [.reg 0, .reg 16, .reg 2, .reg 3, .reg 4]

def compPreLogSplitStmt (bLogAdd : ℕ) : Stmt :=
  .assign 7 (.load (.bin .add (.reg 1) (.const 1))) ;;
  .assign 8 (.load (.bin .add (.reg 6) (.const auxOffOrigVertPtr))) ;;
  .assign 9 (.load (.bin .add (.reg 8) (.reg 7))) ;;
  .call 10 bLogAdd [.reg 0, .reg 9, .reg 2, .reg 3, .reg 4]

/-- `args = [hWin, updPtr, rootsBuf, fDelBuf, cntPtr]`: closes the `T_H`-ancestors of the vertices
touched by the single encoded update at `updPtr` inside window `hWin` via `bLogAdd`, appending
every `(cutE, newRoot)` forest cut to `(fDelBuf, rootsBuf)` and incrementing `*cntPtr`. Returns `0`. -/
def compPreLogProc (bLogAdd : ℕ) : Stmt :=
  .assign 5 (.load (.reg 1)) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const lsfOffAuxPtr))) ;;
  .cond (.bin .eq (.reg 5) (.const 0)) (compPreLogInsStmt bLogAdd)
    (.cond (.bin .eq (.reg 5) (.const 1)) (compPreLogDelStmt bLogAdd) (compPreLogSplitStmt bLogAdd)) ;;
  .ret (.const 0)

lemma compPreLogProc_noRand (bLogAdd : ℕ) : (compPreLogProc bLogAdd).NoRand := by
  dsimp [compPreLogProc, compPreLogInsStmt, compPreLogDelStmt, compPreLogSplitStmt]; trivial

/-! ## 2. Pure state-factoring helpers -/

private lemma lsfOrigVert_mem_T0 {S : LSFState} (hInv : LSFStructInv S) {u : ℕ} (hu : u ∈ S.G.V) :
    S.origVert u ∈ S.T₀.V := by
  rcases Finset.mem_union.mp (hInv.hGV_eq ▸ hu) with hT | hI
  · rw [hInv.horig_id u hT]; exact hT
  · exact upClosure_subset (hldAuxTree_isRootedTree hInv.hT₀) hInv.hR₀_sub (hInv.horig_split u hI)

/-! ## 3. Verification of `compPreLogProc` -/

set_option maxHeartbeats 800000 in
open Classical in
/-- Verification of `compPreLogProc` for any single valid update `u_c` encoded at `updPtr`. -/
theorem compPreLog_runs {w h hWin updPtr len rootsBuf fDelBuf cntPtr cap cnt bLogAdd bLsf : ℕ}
    {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ} {p : Program} {ω : ℕ → Bool}
    {S : LSFState} {x : LSFConcrete} {u_c : Update} {mem : ℕ → ℕ} {pos : ℕ}
    (hpLsf : p.HasAt bLsf (lsfModuleProcs Q_AN c_AN K_AN bLsf h))
    (hpLogAdd : p.procs[bLogAdd]? = some (compLogAddOrigRootProc
      (lsfBaseBat Q_AN bLsf + 0) (lsfBaseDg bLsf + 7 + dgIdxDeleteEdge) (lsfBaseBat Q_AN bLsf + 1)))
    (hw16 : 16 ≤ 2 ^ w) (hend_ltw : x.endAddr hWin < 2 ^ w) (hupd_ltw : updPtr + len < 2 ^ w)
    (hdisj_upd : ∀ i < len, updPtr + i < hWin ∨ x.endAddr hWin ≤ updPtr + i)
    (hdisj_ubuf : ∀ i < len, updPtr + i ≠ cntPtr ∧
      (updPtr + i < rootsBuf ∨ rootsBuf + cap ≤ updPtr + i) ∧
      (updPtr + i < fDelBuf ∨ fDelBuf + cap ≤ updPtr + i))
    (hbuf : CutLogBufOk w hWin (x.endAddr hWin) rootsBuf fDelBuf cntPtr cap)
    (hcnt_m : mem cntPtr = cnt)
    (hrep : (LSFRep h).rep hWin S x mem)
    (hUpdAt : UpdateAt mem updPtr S.G u_c len)
    (hu_valid : S.G.UpdateIsValid u_c)
    (hcap : cnt + ((applyLSFUpdate S u_c).R_orig \ S.R_orig).card ≤ cap) :
    ∃ st' c x' S_pre cuts,
      Runs w p ω (compPreLogProc bLogAdd)
        (startState [hWin, updPtr, rootsBuf, fDelBuf, cntPtr] mem pos) (.returned 0) st' c ∧
      SameStaticConcrete x x' ∧
      (LSFRep h).rep hWin S_pre x' st'.mem ∧
      S_pre.G = S.G ∧
      applyLSFUpdate S_pre u_c = applyLSFUpdate S u_c ∧
      S_pre.RF.F.E = (applyLSFUpdate S u_c).RF.F.E ∧
      (match u_c with
       | .split _ v' _ _ => (applyLSFUpdate S u_c).RF.R = insert v' S_pre.RF.R ∧ v' ∉ S_pre.RF.R
       | _ => (applyLSFUpdate S u_c).RF.R = S_pre.RF.R) ∧
      cuts.length ≤ ((applyLSFUpdate S u_c).R_orig \ S.R_orig).card ∧
      st'.mem cntPtr = cnt + cuts.length ∧
      (∀ i (hi : i < cuts.length),
        st'.mem (rootsBuf + (cnt + i)) = cuts[i].2 ∧ st'.mem (fDelBuf + (cnt + i)) = cuts[i].1) ∧
      (∀ a, (a < hWin ∨ x.endAddr hWin ≤ a) → a ≠ cntPtr →
        (a < rootsBuf + cnt ∨ rootsBuf + cnt + cuts.length ≤ a) →
        (a < fDelBuf + cnt ∨ fDelBuf + cnt + cuts.length ≤ a) →
        st'.mem a = mem a) ∧
      CompForestCutsValid x.vCap S.RF cuts ∧
      cuts.foldl compApplyForestCut S.RF = S_pre.RF ∧
      (cuts.map Prod.fst).Nodup ∧
      (cuts.map Prod.fst).toFinset = S.RF.F.E \ S_pre.RF.F.E ∧
      (cuts.map Prod.snd).Nodup ∧
      (cuts.map Prod.snd).toFinset = S_pre.RF.R \ S.RF.R ∧
      c + 120 * cuts.length + lsfPhi hWin x' st'.mem ≤ 750 + lsfPhi hWin x mem := by
  have M := lsfModuleHasAt_of_hasAt hpLsf
  have hDg := lsfHasAt_dg M.hShared
  have hOps := dgReloc_hasAt_ops hDg
  have hEdge := dgReloc_hasAt_edge hDg
  have gBat : ∀ (i : ℕ) (hi : i < 10), p.procs[lsfBaseBat Q_AN bLsf + i]? =
      some ((lsfProcsBat Q_AN bLsf)[i]'(by rw [lsfProcsBat_length]; exact hi)) :=
    fun i hi => M.hBat.get (by rw [lsfProcsBat_length]; exact hi)
  have hMinUp : ∀ S₀, MeetsContract w p (lsfBaseBat Q_AN bLsf + 0)
      (minEdgeUpContract w S₀ x.vList x.tOrigList) := fun _ => minEdgeUp_meetsContract (gBat 0 (by decide))
  have hDgDelF : ∀ F, MeetsContract w p (lsfBaseDg bLsf + 7 + dgIdxDeleteEdge)
      (dgDeleteEdgeContract w x.vCap (fECap x.eCap x.n0) F) := fun _ => dgDeleteEdge_meetsContract hEdge hOps
  have hBFS : ∀ F, MeetsContract w p (lsfBaseBat Q_AN bLsf + 1) (splitCompBFSContract w F) :=
    fun _ => splitCompBFS_meetsContract (gBat 1 (by decide))
  have hrep_orig := hrep
  rcases hrep with ⟨hxH, hh1, hLin, hLw, hkn, hkeq, hInv, hn0, hm0, htM, hnv, hme, htn, hn1,
    hvT_lt, heG_lt, hhdr, hdgG, hT, hdgF, hFAnc, hW, hwstr, hAux⟩
  set vCap := x.vCap; set eCap := x.eCap; set n0 := x.n0; set tM := x.tM; set L_w := x.L_w
  set dgGPtr := lsfDgGPtr hWin
  set auxPtr := lsfAuxPtr hWin vCap eCap n0 tM L_w
  set origBase := auxOrigVertBase auxPtr vCap n0
  set isOrigBase := auxIsOrigVertBase auxPtr vCap n0
  rcases addRoot_layout hend_ltw with ⟨hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, hl9, _, _⟩
  have hb_hdr_ltw : hWin + lsfHdrSize < 2 ^ w := by dsimp only [vCap, eCap, n0, tM, L_w, dgGPtr, auxPtr] at *; omega
  have hdgG_ltw : dgGPtr + dynGraphSize vCap eCap < 2 ^ w := by dsimp only [vCap, eCap, n0, tM, L_w, dgGPtr, auxPtr] at *; omega
  have haux_ltw : auxPtr + auxSize vCap n0 < 2 ^ w := by dsimp only [vCap, eCap, n0, tM, L_w, dgGPtr, auxPtr] at *; omega
  have hlen_ge2 : 2 ≤ len := by
    cases u_c with
    | insert _ _ _ => rcases hUpdAt with ⟨rfl, _⟩; omega
    | delete _ => rcases hUpdAt with ⟨rfl, _⟩; omega
    | split _ _ _ _ => rcases hUpdAt with ⟨_, _, _, _, _, _, rfl, _⟩ | ⟨_, _, _, _, _, _, rfl, _⟩ <;> omega
  have ⟨hw0, hw1, hw2, hw3, hw4, hWin_ltw⟩ : (0 : ℕ) < 2 ^ w ∧ 1 < 2 ^ w ∧ 2 < 2 ^ w ∧ 3 < 2 ^ w ∧ 4 < 2 ^ w ∧ hWin < 2 ^ w :=
    ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  have haux_hdr_ltw : auxPtr + auxHdrSize < 2 ^ w := by dsimp [auxSize, auxHdrSize] at haux_ltw ⊢; omega
  have haux_ptr_m : mem (hWin + lsfOffAuxPtr) = auxPtr := hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have haux_orig_ptr : mem (auxPtr + auxOffOrigVertPtr) = origBase := hAux.2.2.2.2.2.2.2.2.2.1
  have haux_isorig_ptr : mem (auxPtr + auxOffIsOrigVertPtr) = isOrigBase := hAux.2.2.2.2.2.2.2.2.2.2.1
  have hIsOrig_mem := hAux.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hOrig_mem := hAux.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have horig_end_ltw : origBase + vCap < 2 ^ w := by
    dsimp [origBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase, auxT0DepthBase,
      auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase, auxSize] at haux_ltw ⊢; omega
  have hisOrig_end_ltw : isOrigBase + vCap < 2 ^ w := by
    dsimp [isOrigBase, auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase,
      auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase, auxSize] at haux_ltw ⊢; omega
  -- Helper to call `bLogAdd` on `(hWin, u, rootsBuf, fDelBuf, cntPtr)`
  have hcall_log : ∀ {S1 : LSFState} {x1 : LSFConcrete} {m1 : ℕ → ℕ} {pos1 c_in u_v : ℕ},
      SameStaticConcrete x x1 → (LSFRep h).rep hWin S1 x1 m1 → u_v ∈ S1.T₀.V →
      m1 cntPtr = c_in →
      c_in + (({ S1 with R₀_base := insert u_v S1.R₀_base } : LSFState).R_orig \ S1.R_orig).card ≤ cap →
      ∃ st1 c1 x2 cuts1,
        Runs w p ω (compLogAddOrigRootProc (lsfBaseBat Q_AN bLsf + 0)
          (lsfBaseDg bLsf + 7 + dgIdxDeleteEdge) (lsfBaseBat Q_AN bLsf + 1))
          (startState [hWin, u_v, rootsBuf, fDelBuf, cntPtr] m1 pos1) (.returned 0) st1 c1 ∧
        SameStaticConcrete x1 x2 ∧
        (LSFRep h).rep hWin { S1 with R₀_base := insert u_v S1.R₀_base } x2 st1.mem ∧
        st1.mem cntPtr = c_in + cuts1.length ∧
        (∀ i (hi : i < cuts1.length),
          st1.mem (rootsBuf + (c_in + i)) = cuts1[i].2 ∧ st1.mem (fDelBuf + (c_in + i)) = cuts1[i].1) ∧
        (∀ a, (a < hWin ∨ x.endAddr hWin ≤ a) → a ≠ cntPtr →
          (a < rootsBuf + c_in ∨ rootsBuf + c_in + cuts1.length ≤ a) →
          (a < fDelBuf + c_in ∨ fDelBuf + c_in + cuts1.length ≤ a) → st1.mem a = m1 a) ∧
        CompForestCutsValid x.vCap S1.RF cuts1 ∧
        cuts1.foldl compApplyForestCut S1.RF = ({ S1 with R₀_base := insert u_v S1.R₀_base } : LSFState).RF ∧
        (cuts1.map Prod.fst).Nodup ∧
        (cuts1.map Prod.fst).toFinset = S1.RF.F.E \ ({ S1 with R₀_base := insert u_v S1.R₀_base } : LSFState).RF.F.E ∧
        (cuts1.map Prod.snd).Nodup ∧
        (cuts1.map Prod.snd).toFinset = ({ S1 with R₀_base := insert u_v S1.R₀_base } : LSFState).RF.R \ S1.RF.R ∧
        c1 + 120 * cuts1.length + lsfPhi hWin x2 st1.mem ≤ 280 + lsfPhi hWin x1 m1 := by
    intro S1 x1 m1 pos1 c_in u_v hs1 hr1 hu1 hc1 hcap1
    have hend1 : x1.endAddr hWin < 2 ^ w := hs1.endAddr hWin ▸ hend_ltw
    have hbuf1 : CutLogBufOk w hWin (x1.endAddr hWin) rootsBuf fDelBuf cntPtr cap := hs1.endAddr hWin ▸ hbuf
    obtain ⟨st1, c1, x2, cuts1, hrun1, hs2, hr2, hcnt1, hlog1, hfr1, hv1, hf1, hndE1, hsE1, hndR1, hsR1, hc_bd⟩ :=
      compLogAddOrigRoot_runs (pos := pos1) (ω := ω) hw16 hend1 hbuf1 hc1 hr1 hu1 hcap1
        (by rw [hs1.2.2.2.2.2.2.2.2.2.2.2.1, hs1.2.2.2.2.2.2.2.2.2.2.1]; exact hMinUp)
        (by rw [hs1.1, hs1.2.1, hs1.2.2.1]; exact hDgDelF) hBFS
    exact ⟨st1, c1, x2, cuts1, hrun1, hs2, hr2, hcnt1, hlog1,
      fun a ha => hfr1 a (by rw [hs1.endAddr hWin]; exact ha),
      hs1.1 ▸ hv1, hf1, hndE1, hsE1, hndR1, hsR1, hc_bd⟩
  cases u_c with
  | insert e a b_v =>
    rcases hUpdAt with ⟨rfl, hLA⟩
    have hm0 : mem updPtr = 0 := by simpa using hLA 0 (by simp)
    have hm2 : mem (updPtr + 2) = a := by simpa using hLA 2 (by simp)
    have hm3 : mem (updPtr + 3) = b_v := by simpa using hLA 3 (by simp)
    have ha_lt : a < vCap := hdgG.2.1 a hu_valid.2.1
    have hb_lt : b_v < vCap := hdgG.2.1 b_v hu_valid.2.2
    have hfactor := applyLSFUpdate_insert_eq hInv hu_valid
    set S1 : LSFState := if a ∈ S.T₀.V then { S with R₀_base := insert a S.R₀_base } else S
    set S2 : LSFState := if b_v ∈ S.T₀.V then { S1 with R₀_base := insert b_v S1.R₀_base } else S1
    have hS1_T0 : S1.T₀ = S.T₀ := by dsimp [S1]; split_ifs <;> rfl
    have hS2_G : S2.G = S.G := by dsimp [S2, S1]; split_ifs <;> rfl
    have hR0 : S2.R₀_base = S.R₀_base ∪ ({a, b_v} : Finset ℕ).filter (· ∈ S.T₀.V) := by
      ext z; dsimp only [S2, S1]
      by_cases ha : a ∈ S.T₀.V <;> by_cases hb : b_v ∈ S.T₀.V <;>
        simp only [ha, hb, ite_true, ite_false, Finset.mem_union, Finset.mem_insert,
          Finset.mem_filter, Finset.mem_singleton]
      · exact ⟨fun h => by rcases h with rfl | rfl | h; exact Or.inr ⟨Or.inr rfl, hb⟩; exact Or.inr ⟨Or.inl rfl, ha⟩; exact Or.inl h,
          fun h => by rcases h with h | ⟨rfl | rfl, _⟩; exact Or.inr (Or.inr h); exact Or.inr (Or.inl rfl); exact Or.inl rfl⟩
      · exact ⟨fun h => by rcases h with rfl | h; exact Or.inr ⟨Or.inl rfl, ha⟩; exact Or.inl h,
          fun h => by rcases h with h | ⟨rfl | rfl, hz⟩; exact Or.inr h; exact Or.inl rfl; exact absurd hz hb⟩
      · exact ⟨fun h => by rcases h with rfl | h; exact Or.inr ⟨Or.inr rfl, hb⟩; exact Or.inl h,
          fun h => by rcases h with h | ⟨rfl | rfl, hz⟩; exact Or.inr h; exact absurd hz ha; exact Or.inl rfl⟩
      · exact ⟨fun h => Or.inl h, fun h => by rcases h with h | ⟨rfl | rfl, hz⟩; exact h; exact absurd hz ha; exact absurd hz hb⟩
    have hS2_Rorig : (applyLSFUpdate S (.insert e a b_v)).R_orig = S2.R_orig := by
      have hT0 : S2.T₀ = S.T₀ := by dsimp [S2, S1]; split_ifs <;> rfl
      have hR0_eq : ({ S with R₀_base := S.R₀_base ∪ ({a, b_v} : Finset ℕ).filter (· ∈ S.T₀.V) } : LSFState).R_orig = S2.R_orig := by
        dsimp only [LSFState.R_orig, LSFState.TH]; rw [hR0]; dsimp only [S2, S1]; split_ifs <;> rfl
      dsimp only [applyLSFUpdate, LSFState.R_orig, LSFState.TH] at hR0_eq ⊢; exact hR0_eq
    have hRorig_sub1 : S1.R_orig \ S.R_orig ⊆ (applyLSFUpdate S (.insert e a b_v)).R_orig \ S.R_orig := by
      intro z hz; rw [Finset.mem_sdiff] at hz ⊢; refine ⟨?_, hz.2⟩
      rw [hS2_Rorig]; dsimp only [S2]; split_ifs with hbT
      · obtain ⟨v0, hv0, hzv0⟩ := mem_upClosure_iff.mp hz.1
        exact mem_upClosure_iff.mpr ⟨v0, Finset.mem_insert_of_mem hv0, hzv0⟩
      · exact hz.1
    have happ_eq : applyLSFUpdate S2 (.insert e a b_v) = applyLSFUpdate S (.insert e a b_v) := by
      have hR0' : S2.R₀_base ∪ ({a, b_v} : Finset ℕ).filter (· ∈ S2.T₀.V) =
          S.R₀_base ∪ ({a, b_v} : Finset ℕ).filter (· ∈ S.T₀.V) := by
        have hT0 : S2.T₀ = S.T₀ := by dsimp [S2, S1]; split_ifs <;> rfl
        rw [hT0, hR0]; ext z; simp [Finset.mem_union]
      dsimp only [applyLSFUpdate]; rw [hR0']
      have hS2_eq : S2 = { S with R₀_base := S2.R₀_base } := by dsimp only [S2, S1]; split_ifs <;> rfl
      conv_lhs => rw [hS2_eq]
    -- Step 1: conditional call on `a`
    have hstep1 : ∀ (stA : State), stA.mem = mem →
        stA.regs 0 = hWin → stA.regs 2 = rootsBuf → stA.regs 3 = fDelBuf → stA.regs 4 = cntPtr →
        stA.regs 7 = a → stA.regs 8 = b_v → stA.regs 9 = isOrigBase →
        ∃ st1 c1 x1 cuts1,
          Runs w p ω (.cond (.load (.bin .add (.reg 9) (.reg 7)))
            (.call 10 bLogAdd [.reg 0, .reg 7, .reg 2, .reg 3, .reg 4]) .nop) stA .normal st1 c1 ∧
          st1.regs 0 = hWin ∧ st1.regs 2 = rootsBuf ∧ st1.regs 3 = fDelBuf ∧ st1.regs 4 = cntPtr ∧
          st1.regs 8 = b_v ∧ st1.regs 9 = isOrigBase ∧
          SameStaticConcrete x x1 ∧ (LSFRep h).rep hWin S1 x1 st1.mem ∧
          st1.mem cntPtr = cnt + cuts1.length ∧
          (∀ i (hi : i < cuts1.length),
            st1.mem (rootsBuf + (cnt + i)) = cuts1[i].2 ∧ st1.mem (fDelBuf + (cnt + i)) = cuts1[i].1) ∧
          (∀ addr, (addr < hWin ∨ x.endAddr hWin ≤ addr) → addr ≠ cntPtr →
            (addr < rootsBuf + cnt ∨ rootsBuf + cnt + cuts1.length ≤ addr) →
            (addr < fDelBuf + cnt ∨ fDelBuf + cnt + cuts1.length ≤ addr) → st1.mem addr = mem addr) ∧
          CompForestCutsValid x.vCap S.RF cuts1 ∧ cuts1.foldl compApplyForestCut S.RF = S1.RF ∧
          (cuts1.map Prod.fst).Nodup ∧ (cuts1.map Prod.fst).toFinset = S.RF.F.E \ S1.RF.F.E ∧
          (cuts1.map Prod.snd).Nodup ∧ (cuts1.map Prod.snd).toFinset = S1.RF.R \ S.RF.R ∧
          c1 + 120 * cuts1.length + lsfPhi hWin x1 st1.mem ≤ 300 + lsfPhi hWin x mem := by
      intro stA hmA hr0 hr2 hr3 hr4 hr7 hr8 hr9
      by_cases haT : a ∈ S.T₀.V
      · have hcond : (Expr.load (.bin .add (.reg 9) (.reg 7))).eval w stA = some 1 :=
          Expr.eval_load_of_eq (x := isOrigBase + a)
            (by simp [Expr.eval, BinOp.eval, hr9, hr7, show isOrigBase + a < 2 ^ w by omega])
            (by rw [hmA]; exact (hIsOrig_mem a ha_lt).trans (ite_eq_left haT))
        have hcap1 : cnt + (({ S with R₀_base := insert a S.R₀_base } : LSFState).R_orig \ S.R_orig).card ≤ cap := by
          have h1 : ({ S with R₀_base := insert a S.R₀_base } : LSFState) = S1 := by simp [S1, haT]
          rw [h1]; exact le_trans (Nat.add_le_add_left (Finset.card_le_card hRorig_sub1) cnt) hcap
        obtain ⟨st1, c1, x1, cuts1, hr1, hs1, hrep1, hcnt1, hlog1, hfr1, hv1, hf1, hndE1, hsE1, hndR1, hsR1, hc1⟩ :=
          hcall_log (SameStaticConcrete.refl x) hrep_orig haT hcnt_m hcap1
        have hS1_eq : ({ S with R₀_base := insert a S.R₀_base } : LSFState) = S1 := by simp [S1, haT]
        rw [hS1_eq] at hrep1 hf1 hsE1 hsR1
        let st1' : State := { mem := st1.mem, regs := Function.update stA.regs 10 0, pos := st1.pos }
        have hcall : Runs w p ω (.call 10 bLogAdd [.reg 0, .reg 7, .reg 2, .reg 3, .reg 4]) stA .normal st1' (5 + c1 + 1) :=
          runs_call_iff.mpr ⟨[hWin, a, rootsBuf, fDelBuf, cntPtr], _, .returned 0, st1, c1,
            by simp [evalArgs, Expr.eval, hr0, hr7, hr2, hr3, hr4], hpLogAdd, hmA ▸ hr1, rfl, rfl, by simp [argsSize, Expr.size]⟩
        exact ⟨st1', 4 + (5 + c1 + 1) + 1, x1, cuts1,
          runs_cond_iff.mpr ⟨1, 5 + c1 + 1, hcond, by simpa using hcall, by simp [Expr.size]⟩,
          by simp [st1', hr0], by simp [st1', hr2], by simp [st1', hr3], by simp [st1', hr4],
          by simp [st1', hr8], by simp [st1', hr9], hs1, hrep1, hcnt1, hlog1, hfr1, hv1, hf1,
          hndE1, hsE1, hndR1, hsR1, by dsimp only [st1']; omega⟩
      · have hcond : (Expr.load (.bin .add (.reg 9) (.reg 7))).eval w stA = some 0 :=
          Expr.eval_load_of_eq (x := isOrigBase + a)
            (by simp [Expr.eval, BinOp.eval, hr9, hr7, show isOrigBase + a < 2 ^ w by omega])
            (by rw [hmA]; exact (hIsOrig_mem a ha_lt).trans (ite_eq_right haT))
        have hS1_eq : S1 = S := by simp [S1, haT]
        rw [hS1_eq]
        exact ⟨stA, 6, x, [],
          runs_cond_iff.mpr ⟨0, 1, hcond, by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by simp [Expr.size]⟩,
          hr0, hr2, hr3, hr4, hr8, hr9, SameStaticConcrete.refl x, hmA ▸ hrep_orig, hmA ▸ hcnt_m,
          fun _ hi => by simp at hi, fun _ _ _ _ _ => hmA ▸ rfl, trivial, rfl,
          List.nodup_nil, by simp, List.nodup_nil, by simp, by simp [hmA]⟩
    -- Step 2: conditional call on `b_v`
    have hstep2 : ∀ (st1 : State) (x1 : LSFConcrete) (cuts1 : List (ℕ × ℕ)),
        st1.regs 0 = hWin → st1.regs 2 = rootsBuf → st1.regs 3 = fDelBuf → st1.regs 4 = cntPtr →
        st1.regs 8 = b_v → st1.regs 9 = isOrigBase →
        SameStaticConcrete x x1 → (LSFRep h).rep hWin S1 x1 st1.mem →
        st1.mem cntPtr = cnt + cuts1.length →
        cuts1.length ≤ (S1.R_orig \ S.R_orig).card →
        ∃ st2 c2 x2 cuts2,
          Runs w p ω (.cond (.load (.bin .add (.reg 9) (.reg 8)))
            (.call 10 bLogAdd [.reg 0, .reg 8, .reg 2, .reg 3, .reg 4]) .nop) st1 .normal st2 c2 ∧
          SameStaticConcrete x x2 ∧ (LSFRep h).rep hWin S2 x2 st2.mem ∧
          st2.mem cntPtr = cnt + cuts1.length + cuts2.length ∧
          (∀ i (hi : i < cuts2.length),
            st2.mem (rootsBuf + (cnt + cuts1.length + i)) = cuts2[i].2 ∧
            st2.mem (fDelBuf + (cnt + cuts1.length + i)) = cuts2[i].1) ∧
          (∀ addr, (addr < hWin ∨ x.endAddr hWin ≤ addr) → addr ≠ cntPtr →
            (addr < rootsBuf + (cnt + cuts1.length) ∨ rootsBuf + (cnt + cuts1.length) + cuts2.length ≤ addr) →
            (addr < fDelBuf + (cnt + cuts1.length) ∨ fDelBuf + (cnt + cuts1.length) + cuts2.length ≤ addr) →
            st2.mem addr = st1.mem addr) ∧
          CompForestCutsValid x.vCap S1.RF cuts2 ∧ cuts2.foldl compApplyForestCut S1.RF = S2.RF ∧
          (cuts2.map Prod.fst).Nodup ∧ (cuts2.map Prod.fst).toFinset = S1.RF.F.E \ S2.RF.F.E ∧
          (cuts2.map Prod.snd).Nodup ∧ (cuts2.map Prod.snd).toFinset = S2.RF.R \ S1.RF.R ∧
          c2 + 120 * cuts2.length + lsfPhi hWin x2 st2.mem ≤ 300 + lsfPhi hWin x1 st1.mem := by
      intro st1 x1 cuts1 hr0 hr2 hr3 hr4 hr8 hr9 hs1 hrep1 hcnt1 hlen1
      have hAux1 := hrep1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      have hIsOrig1 := hAux1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have haux_eq1 : lsfAuxPtr hWin x1.vCap x1.eCap x1.n0 x1.tM x1.L_w = auxPtr := by
        rw [hs1.1, hs1.2.1, hs1.2.2.1, hs1.2.2.2.2.1, hs1.2.2.2.2.2.2.2.2.1]
      have hiso_eq1 : auxIsOrigVertBase (lsfAuxPtr hWin x1.vCap x1.eCap x1.n0 x1.tM x1.L_w) x1.vCap x1.n0 = isOrigBase := by
        rw [haux_eq1, hs1.1, hs1.2.2.1]
      by_cases hbT : b_v ∈ S.T₀.V
      · have hcond : (Expr.load (.bin .add (.reg 9) (.reg 8))).eval w st1 = some 1 :=
          Expr.eval_load_of_eq (x := isOrigBase + b_v)
            (by simp [Expr.eval, BinOp.eval, hr9, hr8, show isOrigBase + b_v < 2 ^ w by omega])
            (by rw [← hiso_eq1, hIsOrig1 b_v (hs1.1.symm ▸ hb_lt), hS1_T0, ite_eq_left hbT])
        have hS2_eq : ({ S1 with R₀_base := insert b_v S1.R₀_base } : LSFState) = S2 := by simp [S2, hbT]
        have hcap2 : cnt + cuts1.length + (({ S1 with R₀_base := insert b_v S1.R₀_base } : LSFState).R_orig \ S1.R_orig).card ≤ cap := by
          rw [hS2_eq]
          have hdisj_r : Disjoint (S1.R_orig \ S.R_orig) (S2.R_orig \ S1.R_orig) := by
            rw [Finset.disjoint_left]; intro z hz1 hz2; exact (Finset.mem_sdiff.mp hz2).2 (Finset.mem_sdiff.mp hz1).1
          have hunion_sub : (S1.R_orig \ S.R_orig) ∪ (S2.R_orig \ S1.R_orig) ⊆
              (applyLSFUpdate S (.insert e a b_v)).R_orig \ S.R_orig := by
            intro z hz; rw [Finset.mem_union] at hz
            rcases hz with hz1 | hz2
            · exact hRorig_sub1 hz1
            · rw [Finset.mem_sdiff] at hz2 ⊢
              refine ⟨hS2_Rorig.symm ▸ hz2.1, fun hzS => hz2.2 ?_⟩
              dsimp only [S1]; split_ifs
              · obtain ⟨v0, hv0, hzv0⟩ := mem_upClosure_iff.mp hzS
                exact mem_upClosure_iff.mpr ⟨v0, Finset.mem_insert_of_mem hv0, hzv0⟩
              · exact hzS
          have hcard_le := Finset.card_le_card hunion_sub
          rw [Finset.card_union_of_disjoint hdisj_r] at hcard_le; omega
        obtain ⟨st2, c2, x2, cuts2, hr2', hs2, hrep2, hcnt2, hlog2, hfr2, hv2, hf2, hndE2, hsE2, hndR2, hsR2, hc2⟩ :=
          hcall_log hs1 hrep1 (hS1_T0.symm ▸ hbT) hcnt1 hcap2
        rw [hS2_eq] at hrep2 hf2 hsE2 hsR2
        let st2' : State := { mem := st2.mem, regs := Function.update st1.regs 10 0, pos := st2.pos }
        have hcall : Runs w p ω (.call 10 bLogAdd [.reg 0, .reg 8, .reg 2, .reg 3, .reg 4]) st1 .normal st2' (5 + c2 + 1) :=
          runs_call_iff.mpr ⟨[hWin, b_v, rootsBuf, fDelBuf, cntPtr], _, .returned 0, st2, c2,
            by simp [evalArgs, Expr.eval, hr0, hr8, hr2, hr3, hr4], hpLogAdd, hr2', rfl, rfl, by simp [argsSize, Expr.size]⟩
        exact ⟨st2', 4 + (5 + c2 + 1) + 1, x2, cuts2,
          runs_cond_iff.mpr ⟨1, 5 + c2 + 1, hcond, by simpa using hcall, by simp [Expr.size]⟩,
          hs1.trans hs2, hrep2, hcnt2, hlog2, hfr2, hv2, hf2, hndE2, hsE2, hndR2, hsR2, by dsimp only [st2']; omega⟩
      · have hcond : (Expr.load (.bin .add (.reg 9) (.reg 8))).eval w st1 = some 0 :=
          Expr.eval_load_of_eq (x := isOrigBase + b_v)
            (by simp [Expr.eval, BinOp.eval, hr9, hr8, show isOrigBase + b_v < 2 ^ w by omega])
            (by rw [← hiso_eq1, hIsOrig1 b_v (hs1.1.symm ▸ hb_lt), hS1_T0, ite_eq_right hbT])
        have hS2_eq : S2 = S1 := by simp [S2, hbT]
        rw [hS2_eq]
        exact ⟨st1, 6, x1, [],
          runs_cond_iff.mpr ⟨0, 1, hcond, by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by simp [Expr.size]⟩,
          hs1, hrep1, by simpa using hcnt1, fun _ hi => by simp at hi, fun _ _ _ _ _ => rfl,
          trivial, rfl, List.nodup_nil, by simp, List.nodup_nil, by simp, by simp⟩
    -- Stitch prefix + step1 + step2 + ret 0
    let stIn := startState [hWin, updPtr, rootsBuf, fDelBuf, cntPtr] mem pos
    let s1 : State := { stIn with regs := Function.update stIn.regs 5 0 }; let s2 : State := { s1 with regs := Function.update s1.regs 6 auxPtr }
    let s3 : State := { s2 with regs := Function.update s2.regs 7 a }; let s4 : State := { s3 with regs := Function.update s3.regs 8 b_v }
    let s5 : State := { s4 with regs := Function.update s4.regs 9 isOrigBase }
    have hp1 : Runs w p ω (.assign 5 (.load (.reg 1))) stIn .normal s1 3 :=
      runs_assign_iff.mpr ⟨0, Expr.eval_load_of_eq (by simp [stIn, Expr.eval, startState]) hm0, rfl, rfl, by simp [Expr.size]⟩
    have hp2 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 0) (.const lsfOffAuxPtr)))) s1 .normal s2 5 :=
      runs_assign_iff.mpr ⟨auxPtr, Expr.eval_load_of_eq (by
        simp [s1, stIn, Expr.eval, BinOp.eval, startState,
          show lsfOffAuxPtr < 2 ^ w by dsimp [lsfOffAuxPtr, lsfHdrSize] at hb_hdr_ltw ⊢; omega,
          show hWin + lsfOffAuxPtr < 2 ^ w by dsimp [lsfOffAuxPtr, lsfHdrSize] at hb_hdr_ltw ⊢; omega]) haux_ptr_m,
        rfl, rfl, by simp [Expr.size]⟩
    have hp3 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 1) (.const 2)))) s2 .normal s3 5 :=
      runs_assign_iff.mpr ⟨a, Expr.eval_load_of_eq (by simp [s2, s1, stIn, Expr.eval, BinOp.eval, startState, hw2, show updPtr + 2 < 2 ^ w by omega]) hm2,
        rfl, rfl, by simp [Expr.size]⟩
    have hp4 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 1) (.const 3)))) s3 .normal s4 5 :=
      runs_assign_iff.mpr ⟨b_v, Expr.eval_load_of_eq (by simp [s3, s2, s1, stIn, Expr.eval, BinOp.eval, startState, hw3, show updPtr + 3 < 2 ^ w by omega]) hm3,
        rfl, rfl, by simp [Expr.size]⟩
    have hp5 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 6) (.const auxOffIsOrigVertPtr)))) s4 .normal s5 5 :=
      runs_assign_iff.mpr ⟨isOrigBase, Expr.eval_load_of_eq (by
        simp [s4, s3, s2, Expr.eval, BinOp.eval,
          show auxOffIsOrigVertPtr < 2 ^ w by dsimp [auxOffIsOrigVertPtr, auxHdrSize] at haux_hdr_ltw ⊢; omega,
          show auxPtr + auxOffIsOrigVertPtr < 2 ^ w by dsimp [auxOffIsOrigVertPtr, auxHdrSize] at haux_hdr_ltw ⊢; omega]) haux_isorig_ptr,
        rfl, rfl, by simp [Expr.size]⟩
    obtain ⟨st1, c1, x1, cuts1, hr1, hr1_0, hr1_2, hr1_3, hr1_4, hr1_8, hr1_9, hs1, hrep1,
      hcnt1, hlog1, hfr1, hv1, hf1, hndE1, hsE1, hndR1, hsR1, hc1⟩ :=
      hstep1 s5 rfl (by simp [s5, s4, s3, s2, s1, stIn, startState]) (by simp [s5, s4, s3, s2, s1, stIn, startState])
        (by simp [s5, s4, s3, s2, s1, stIn, startState]) (by simp [s5, s4, s3, s2, s1, stIn, startState])
        (by simp [s5, s4, s3]) (by simp [s5, s4]) (by simp [s5])
    have hlen1 : cuts1.length ≤ (S1.R_orig \ S.R_orig).card := by
      have hcard := (List.toFinset_card_of_nodup hndR1).symm
      rw [List.length_map] at hcard; rw [hcard, hsR1]
      refine Finset.card_le_card (fun z hz => ?_)
      have hiso1 : S1.isolatedVerts = S.isolatedVerts := by dsimp [S1]; split_ifs <;> rfl
      simp only [LSFState.RF, LSFState.R, Finset.mem_sdiff, Finset.mem_union, hiso1] at hz ⊢
      exact ⟨by rcases hz.1 with h | h; exact h; exact absurd (Or.inr h) hz.2, fun h => hz.2 (Or.inl h)⟩
    obtain ⟨st2, c2, x2, cuts2, hr2, hs2, hrep2, hcnt2, hlog2, hfr2, hv2, hf2, hndE2, hsE2, hndR2, hsR2, hc2⟩ :=
      hstep2 st1 x1 cuts1 hr1_0 hr1_2 hr1_3 hr1_4 hr1_8 hr1_9 hs1 hrep1 hcnt1 hlen1
    have hthen : Runs w p ω (compPreLogInsStmt bLogAdd) s2 .normal st2 (c1 + c2 + 19) :=
      runs_seq_iff.mpr (Or.inr ⟨s3, 5, c1 + c2 + 13, hp3,
        runs_seq_iff.mpr (Or.inr ⟨s4, 5, c1 + c2 + 7, hp4,
          runs_seq_iff.mpr (Or.inr ⟨s5, 5, c1 + c2 + 1, hp5,
            runs_seq_iff.mpr (Or.inr ⟨st1, c1, c2, hr1, hr2, by omega⟩), by omega⟩), by omega⟩), by omega⟩)
    have hcond : Runs w p ω (.cond (.bin .eq (.reg 5) (.const 0)) (compPreLogInsStmt bLogAdd)
        (.cond (.bin .eq (.reg 5) (.const 1)) (compPreLogDelStmt bLogAdd) (compPreLogSplitStmt bLogAdd)))
        s2 .normal st2 (c1 + c2 + 23) :=
      runs_cond_iff.mpr ⟨1, c1 + c2 + 19, by simp [s2, s1, Expr.eval, BinOp.eval, hw0, hw1],
        by simpa using hthen, by simp [Expr.size]; omega⟩
    have hret : Runs w p ω (.ret (.const 0)) st2 (.returned 0) st2 2 :=
      runs_ret_iff.mpr ⟨0, by simp [Expr.eval, hw0], rfl, rfl, by simp [Expr.size]⟩
    have hfull : Runs w p ω (compPreLogProc bLogAdd) stIn (.returned 0) st2 (c1 + c2 + 36) :=
      runs_seq_iff.mpr (Or.inr ⟨s1, 3, c1 + c2 + 32, hp1,
        runs_seq_iff.mpr (Or.inr ⟨s2, 5, c1 + c2 + 26, hp2,
          runs_seq_iff.mpr (Or.inr ⟨st2, c1 + c2 + 23, 2, hcond, hret, by omega⟩), by omega⟩), by omega⟩)
    obtain ⟨hvc, hfc, hndEc, hsEc, hndRc, hsRc⟩ :=
      compPreLog_two_cuts_combine hv1 hf1 hndE1 hsE1 hndR1 hsR1 hv2 hf2 hndE2 hsE2 hndR2 hsR2
    have hlen_le : (cuts1 ++ cuts2).length ≤ ((applyLSFUpdate S (.insert e a b_v)).R_orig \ S.R_orig).card := by
      have hcard := (List.toFinset_card_of_nodup hndRc).symm
      rw [List.length_map] at hcard; rw [hcard, hsRc]
      refine Finset.card_le_card (fun z hz => ?_)
      have hiso2 : S2.isolatedVerts = S.isolatedVerts := by dsimp [S2, S1]; split_ifs <;> rfl
      rw [hS2_Rorig]; simp only [LSFState.RF, LSFState.R, Finset.mem_sdiff, Finset.mem_union, hiso2] at hz ⊢
      exact ⟨by rcases hz.1 with h | h; exact h; exact absurd (Or.inr h) hz.2, fun h => hz.2 (Or.inl h)⟩
    have hRF_ins : (applyLSFUpdate S (.insert e a b_v)).RF = S2.RF := by
      have hf : S2.isolatedVerts = S.isolatedVerts ∧ S2.T₀ = S.T₀ ∧ S2.T_cur = S.T_cur ∧ S2.r₀ = S.r₀ ∧ S2.π = S.π := by
        dsimp [S2, S1]; split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      dsimp only [LSFState.RF, LSFState.R]
      rw [hS2_Rorig]; dsimp only [applyLSFUpdate]; rw [hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2]
    have hcnt_tot : cnt + cuts1.length + cuts2.length ≤ cap := by
      simp only [List.length_append] at hlen_le; omega
    refine ⟨st2, c1 + c2 + 36, x2, S2, cuts1 ++ cuts2, hfull, hs2, hrep2, hS2_G, happ_eq,
      by rw [hRF_ins], congrArg RootedForest.R hRF_ins, hlen_le,
      by simp [hcnt2, Nat.add_assoc], ?_, ?_, hvc, hfc, hndEc, hsEc, hndRc, hsRc, ?_⟩
    · intro i hi
      by_cases h1 : i < cuts1.length
      · have hfr_r := hfr2 (rootsBuf + (cnt + i)) (by rcases hbuf with ⟨_, h, _⟩; omega)
          (by rcases hbuf with ⟨_, _, _, _, h, _⟩; omega) (Or.inl (by omega))
          (by rcases hbuf with ⟨_, _, _, h, _⟩; omega)
        have hfr_f := hfr2 (fDelBuf + (cnt + i)) (by rcases hbuf with ⟨_, _, h, _⟩; omega)
          (by rcases hbuf with ⟨_, _, _, _, _, h, _⟩; omega)
          (by rcases hbuf with ⟨_, _, _, h, _⟩; omega) (Or.inl (by omega))
        simpa [List.getElem_append_left h1] using ⟨hfr_r.trans (hlog1 i h1).1, hfr_f.trans (hlog1 i h1).2⟩
      · have h2 : i - cuts1.length < cuts2.length := by simp at hi; omega
        have heq := hlog2 (i - cuts1.length) h2
        rw [show cnt + cuts1.length + (i - cuts1.length) = cnt + i by omega] at heq
        simpa [List.getElem_append_right (by omega : cuts1.length ≤ i)] using heq
    · intro addr ha hnc hnr hnf
      simp only [List.length_append] at hnr hnf
      exact (hfr2 addr ha hnc (by omega) (by omega)).trans (hfr1 addr ha hnc (by omega) (by omega))
    · simp only [List.length_append]; omega
  | delete e =>
    rcases hUpdAt with ⟨rfl, hLA⟩
    have hm0 : mem updPtr = 1 := by simpa using hLA 0 (by simp)
    have hm1 : mem (updPtr + 1) = e := by simpa using hLA 1 (by simp)
    have heG : e ∈ S.G.E := hu_valid
    have he_lt : e < eCap := hdgG.2.2.1 e heG
    set u := S.G.tail e; set v := S.G.head e
    have huG : u ∈ S.G.V := (hInv.hG_val e heG).1
    have hvG : v ∈ S.G.V := (hInv.hG_val e heG).2
    have hu_lt : u < vCap := hdgG.2.1 u huG
    have hv_lt : v < vCap := hdgG.2.1 v hvG
    set u0 := S.origVert u; set v0 := S.origVert v
    have hu0T : u0 ∈ S.T₀.V := lsfOrigVert_mem_T0 hInv huG
    have hv0T : v0 ∈ S.T₀.V := lsfOrigVert_mem_T0 hInv hvG
    have hEndSlot := hdgG.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e heG
    have hExtU := hdgG.2.2.2.2.2.2.2.2.2.1 u huG
    have hExtV := hdgG.2.2.2.2.2.2.2.2.2.1 v hvG
    have hu_read : mem (dgIntToExtBase dgGPtr vCap + mem (dgETailSlotBase dgGPtr vCap eCap + e)) = u := by
      rw [hEndSlot.1]; exact hExtU.2
    have hv_read : mem (dgIntToExtBase dgGPtr vCap + mem (dgEHeadSlotBase dgGPtr vCap eCap + e)) = v := by
      rw [hEndSlot.2]; exact hExtV.2
    have hu0_read : mem (origBase + u) = u0 := hOrig_mem u huG hu_lt
    have hv0_read : mem (origBase + v) = v0 := hOrig_mem v hvG hv_lt
    set S1 : LSFState := { S with R₀_base := insert u0 S.R₀_base }
    set S2 : LSFState := { S1 with R₀_base := insert v0 S1.R₀_base }
    have hS1_T0 : S1.T₀ = S.T₀ := rfl
    have hS2_G : S2.G = S.G := rfl
    have hR0_2 : S2.R₀_base = S.R₀_base ∪ ({u0, v0} : Finset ℕ).filter (· ∈ S.T₀.V) := by
      ext z; simp only [S2, S1, Finset.mem_union, Finset.mem_insert, Finset.mem_filter, Finset.mem_singleton]
      exact ⟨fun h => by rcases h with rfl | rfl | h; exact Or.inr ⟨Or.inr rfl, hv0T⟩; exact Or.inr ⟨Or.inl rfl, hu0T⟩; exact Or.inl h,
        fun h => by rcases h with h | ⟨rfl | rfl, _⟩; exact Or.inr (Or.inr h); exact Or.inr (Or.inl rfl); exact Or.inl rfl⟩
    have happ_eq : applyLSFUpdate S2 (.delete e) = applyLSFUpdate S (.delete e) := by
      have h1 : S.R₀_base ∪ ({u0, v0} : Finset ℕ).filter (· ∈ S.T₀.V) ∪ ({u0, v0} : Finset ℕ).filter (· ∈ S.T₀.V) =
          S.R₀_base ∪ ({u0, v0} : Finset ℕ).filter (· ∈ S.T₀.V) := by ext z; simp [Finset.mem_union]
      dsimp only [applyLSFUpdate]; rw [hR0_2]; dsimp only [S2, S1]; rw [h1]
    have hRF_del : (applyLSFUpdate S (.delete e)).RF = S2.RF := by
      dsimp only [applyLSFUpdate, LSFState.RF, LSFState.R, LSFState.R_orig, LSFState.TH]
      rw [hR0_2]
    have hRorig_sub1 : S1.R_orig \ S.R_orig ⊆ (applyLSFUpdate S (.delete e)).R_orig \ S.R_orig := by
      intro z hz; rw [Finset.mem_sdiff] at hz ⊢; refine ⟨?_, hz.2⟩
      have hEq : (applyLSFUpdate S (.delete e)).R_orig = S2.R_orig := by
        dsimp only [applyLSFUpdate, LSFState.R_orig, LSFState.TH]; rw [hR0_2]
      rw [hEq]
      obtain ⟨w0, hw0, hzw0⟩ := mem_upClosure_iff.mp hz.1
      exact mem_upClosure_iff.mpr ⟨w0, Finset.mem_insert_of_mem hw0, hzw0⟩
    have hcap1 : cnt + (S1.R_orig \ S.R_orig).card ≤ cap :=
      le_trans (Nat.add_le_add_left (Finset.card_le_card hRorig_sub1) cnt) hcap
    obtain ⟨st1, c1, x1, cuts1, hr1, hs1, hrep1, hcnt1, hlog1, hfr1, hv1, hf1, hndE1, hsE1, hndR1, hsR1, hc1⟩ :=
      hcall_log (SameStaticConcrete.refl x) hrep_orig hu0T hcnt_m hcap1
    have hlen1 : cuts1.length ≤ (S1.R_orig \ S.R_orig).card := by
      have hcard := (List.toFinset_card_of_nodup hndR1).symm
      rw [List.length_map] at hcard; rw [hcard, hsR1]
      refine Finset.card_le_card (fun z hz => ?_)
      simp only [LSFState.RF, LSFState.R, Finset.mem_sdiff, Finset.mem_union] at hz ⊢
      exact ⟨by rcases hz.1 with h | h; exact h; exact absurd (Or.inr h) hz.2, fun h => hz.2 (Or.inl h)⟩
    have hcap2 : cnt + cuts1.length + (S2.R_orig \ S1.R_orig).card ≤ cap := by
      have hdisj_r : Disjoint (S1.R_orig \ S.R_orig) (S2.R_orig \ S1.R_orig) := by
        rw [Finset.disjoint_left]; intro z hz1 hz2; exact (Finset.mem_sdiff.mp hz2).2 (Finset.mem_sdiff.mp hz1).1
      have hEq : (applyLSFUpdate S (.delete e)).R_orig = S2.R_orig := by
        dsimp only [applyLSFUpdate, LSFState.R_orig, LSFState.TH]; rw [hR0_2]
      have hunion_sub : (S1.R_orig \ S.R_orig) ∪ (S2.R_orig \ S1.R_orig) ⊆
          (applyLSFUpdate S (.delete e)).R_orig \ S.R_orig := by
        intro z hz; rw [Finset.mem_union] at hz; rcases hz with hz1 | hz2
        · exact hRorig_sub1 hz1
        · rw [Finset.mem_sdiff] at hz2 ⊢
          refine ⟨hEq.symm ▸ hz2.1, fun hzS => hz2.2 ?_⟩
          obtain ⟨w0, hw0, hzw0⟩ := mem_upClosure_iff.mp hzS
          exact mem_upClosure_iff.mpr ⟨w0, Finset.mem_insert_of_mem hw0, hzw0⟩
      have hcard_le := Finset.card_le_card hunion_sub
      rw [Finset.card_union_of_disjoint hdisj_r] at hcard_le; omega
    obtain ⟨st2, c2, x2, cuts2, hr2, hs2, hrep2, hcnt2, hlog2, hfr2, hv2, hf2, hndE2, hsE2, hndR2, hsR2, hc2⟩ :=
      hcall_log hs1 hrep1 hv0T hcnt1 hcap2
    have hdgG_sz : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
    have hInt_w : dgIntToExtBase dgGPtr vCap < 2 ^ w := by dsimp [dgIntToExtBase]; omega
    have hET_w : dgETailSlotBase dgGPtr vCap eCap < 2 ^ w := by dsimp [dgETailSlotBase]; omega
    have hEH_w : dgEHeadSlotBase dgGPtr vCap eCap < 2 ^ w := by dsimp [dgEHeadSlotBase]; omega
    have hSlotU_lt : mem (dgETailSlotBase dgGPtr vCap eCap + e) < vCap := hEndSlot.1.symm ▸ hdgG.2.1 _ hExtU.1
    have hSlotV_lt : mem (dgEHeadSlotBase dgGPtr vCap eCap + e) < vCap := hEndSlot.2.symm ▸ hdgG.2.1 _ hExtV.1
    let stIn := startState [hWin, updPtr, rootsBuf, fDelBuf, cntPtr] mem pos
    -- Run the delete branch cleanly via explicit state steps
    have hrun_del : ∃ stF cF, Runs w p ω (compPreLogProc bLogAdd) stIn (.returned 0) stF cF ∧
        stF.mem = st2.mem ∧ cF ≤ c1 + c2 + 130 := by
      let s1 : State := { stIn with regs := Function.update stIn.regs 5 1 }; let s2 : State := { s1 with regs := Function.update s1.regs 6 auxPtr }
      let s3 : State := { s2 with regs := Function.update s2.regs 7 e }; let s4 : State := { s3 with regs := Function.update s3.regs 8 vCap }
      let s5 : State := { s4 with regs := Function.update s4.regs 9 eCap }; let s6 : State := { s5 with regs := Function.update s5.regs 10 dgGPtr }
      let s7 : State := { s6 with regs := Function.update s6.regs 11 origBase }; let s8 : State := { s7 with regs := Function.update s7.regs 12 (dgIntToExtBase dgGPtr vCap) }
      let s9 : State := { s8 with regs := Function.update s8.regs 13 (dgETailSlotBase dgGPtr vCap eCap) }; let s10 : State := { s9 with regs := Function.update s9.regs 14 (dgEHeadSlotBase dgGPtr vCap eCap) }
      let s11 : State := { s10 with regs := Function.update s10.regs 15 u0 }; let s12 : State := { s11 with regs := Function.update s11.regs 16 v0 }
      let s13 : State := { mem := st1.mem, regs := Function.update s12.regs 17 0, pos := st1.pos }; let s14 : State := { mem := st2.mem, regs := Function.update s13.regs 17 0, pos := st2.pos }
      have hp1 : Runs w p ω (.assign 5 (.load (.reg 1))) stIn .normal s1 3 :=
        runs_assign_iff.mpr ⟨1, Expr.eval_load_of_eq (by simp [stIn, Expr.eval, startState]) hm0, rfl, rfl, by simp [Expr.size]⟩
      have hp2 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 0) (.const lsfOffAuxPtr)))) s1 .normal s2 5 :=
        runs_assign_iff.mpr ⟨auxPtr, Expr.eval_load_of_eq (by
          simp [s1, stIn, Expr.eval, BinOp.eval, startState,
            show lsfOffAuxPtr < 2 ^ w by dsimp [lsfOffAuxPtr, lsfHdrSize] at hb_hdr_ltw ⊢; omega,
            show hWin + lsfOffAuxPtr < 2 ^ w by dsimp [lsfOffAuxPtr, lsfHdrSize] at hb_hdr_ltw ⊢; omega]) haux_ptr_m,
          rfl, rfl, by simp [Expr.size]⟩
      have hp3 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 1) (.const 1)))) s2 .normal s3 5 :=
        runs_assign_iff.mpr ⟨e, Expr.eval_load_of_eq (by simp [s2, s1, stIn, Expr.eval, BinOp.eval, startState, hw1, show updPtr + 1 < 2 ^ w by omega]) hm1,
          rfl, rfl, by simp [Expr.size]⟩
      have hp4 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 0) (.const lsfOffVCap)))) s3 .normal s4 5 :=
        runs_assign_iff.mpr ⟨vCap, Expr.eval_load_of_eq (by
          simp [s3, s2, s1, stIn, Expr.eval, BinOp.eval, startState,
            show lsfOffVCap < 2 ^ w by dsimp [lsfOffVCap, lsfHdrSize] at hb_hdr_ltw ⊢; omega,
            show hWin + lsfOffVCap < 2 ^ w by dsimp [lsfOffVCap, lsfHdrSize] at hb_hdr_ltw ⊢; omega]) hhdr.1,
          rfl, rfl, by simp [Expr.size]⟩
      have hp5 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 0) (.const lsfOffECap)))) s4 .normal s5 5 :=
        runs_assign_iff.mpr ⟨eCap, Expr.eval_load_of_eq (by
          simp [s4, s3, s2, s1, stIn, Expr.eval, BinOp.eval, startState,
            show lsfOffECap < 2 ^ w by dsimp [lsfOffECap, lsfHdrSize] at hb_hdr_ltw ⊢; omega,
            show hWin + lsfOffECap < 2 ^ w by dsimp [lsfOffECap, lsfHdrSize] at hb_hdr_ltw ⊢; omega]) hhdr.2.1,
          rfl, rfl, by simp [Expr.size]⟩
      have hp6 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 0) (.const lsfOffDgGPtr)))) s5 .normal s6 5 :=
        runs_assign_iff.mpr ⟨dgGPtr, Expr.eval_load_of_eq (by
          simp [s5, s4, s3, s2, s1, stIn, Expr.eval, BinOp.eval, startState,
            show lsfOffDgGPtr < 2 ^ w by dsimp [lsfOffDgGPtr, lsfHdrSize] at hb_hdr_ltw ⊢; omega,
            show hWin + lsfOffDgGPtr < 2 ^ w by dsimp [lsfOffDgGPtr, lsfHdrSize] at hb_hdr_ltw ⊢; omega]) hhdr.2.2.2.2.1,
          rfl, rfl, by simp [Expr.size]⟩
      have hp7 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 6) (.const auxOffOrigVertPtr)))) s6 .normal s7 5 :=
        runs_assign_iff.mpr ⟨origBase, Expr.eval_load_of_eq (by
          simp [s6, s5, s4, s3, s2, Expr.eval, BinOp.eval,
            show auxOffOrigVertPtr < 2 ^ w by dsimp [auxOffOrigVertPtr, auxHdrSize] at haux_hdr_ltw ⊢; omega,
            show auxPtr + auxOffOrigVertPtr < 2 ^ w by dsimp [auxOffOrigVertPtr, auxHdrSize] at haux_hdr_ltw ⊢; omega]) haux_orig_ptr,
          rfl, rfl, by simp [Expr.size]⟩
      have hp8 : Runs w p ω (.assign 12 (.bin .add (.bin .add (.reg 10) (.const 4)) (.bin .mul (.const 4) (.reg 8)))) s7 .normal s8 8 :=
        runs_assign_iff.mpr ⟨dgIntToExtBase dgGPtr vCap, by
          simp [s7, s6, s5, s4, Expr.eval, BinOp.eval, dgIntToExtBase, hw4,
            show dgGPtr + 4 < 2 ^ w by omega, show 4 * vCap < 2 ^ w by omega,
            show dgGPtr + 4 + 4 * vCap < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
      have hp9 : Runs w p ω (.assign 13 (.bin .add (.bin .add (.bin .add (.reg 10) (.const 4)) (.bin .mul (.const 7) (.reg 8)))
          (.bin .mul (.const 3) (.reg 9)))) s8 .normal s9 12 :=
        runs_assign_iff.mpr ⟨dgETailSlotBase dgGPtr vCap eCap, by
          simp [s8, s7, s6, s5, s4, Expr.eval, BinOp.eval, dgETailSlotBase, hw4, hw3,
            show (7 : ℕ) < 2 ^ w by omega, show dgGPtr + 4 < 2 ^ w by omega, show 7 * vCap < 2 ^ w by omega,
            show dgGPtr + 4 + 7 * vCap < 2 ^ w by omega, show 3 * eCap < 2 ^ w by omega,
            show dgGPtr + 4 + 7 * vCap + 3 * eCap < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
      have hp10 : Runs w p ω (.assign 14 (.bin .add (.bin .add (.bin .add (.reg 10) (.const 4)) (.bin .mul (.const 7) (.reg 8)))
          (.bin .mul (.const 4) (.reg 9)))) s9 .normal s10 12 :=
        runs_assign_iff.mpr ⟨dgEHeadSlotBase dgGPtr vCap eCap, by
          simp [s9, s8, s7, s6, s5, s4, Expr.eval, BinOp.eval, dgEHeadSlotBase, hw4,
            show (7 : ℕ) < 2 ^ w by omega, show dgGPtr + 4 < 2 ^ w by omega, show 7 * vCap < 2 ^ w by omega,
            show dgGPtr + 4 + 7 * vCap < 2 ^ w by omega, show 4 * eCap < 2 ^ w by omega,
            show dgGPtr + 4 + 7 * vCap + 4 * eCap < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
      have hs10_r : s10.regs 7 = e ∧ s10.regs 11 = origBase ∧ s10.regs 12 = dgIntToExtBase dgGPtr vCap ∧
          s10.regs 13 = dgETailSlotBase dgGPtr vCap eCap ∧ s10.regs 14 = dgEHeadSlotBase dgGPtr vCap eCap :=
        ⟨by simp [s10, s9, s8, s7, s6, s5, s4, s3], by simp [s10, s9, s8, s7],
         by simp [s10, s9, s8], by simp [s10, s9], by simp [s10]⟩
      have hp11 : Runs w p ω (.assign 15 (.load (.bin .add (.reg 11) (.load (.bin .add (.reg 12) (.load (.bin .add (.reg 13) (.reg 7)))))))) s10 .normal s11 11 :=
        runs_assign_iff.mpr ⟨u0, Expr.eval_load_of_eq (by
          refine Expr.eval_bin (by simp [Expr.eval, hs10_r.2.1]) (Expr.eval_load_of_eq (by
            refine Expr.eval_bin (by simp [Expr.eval, hs10_r.2.2.1]) (Expr.eval_load_of_eq (by
              simp [Expr.eval, BinOp.eval, hs10_r.1, hs10_r.2.2.2.1,
                show dgETailSlotBase dgGPtr vCap eCap + e < 2 ^ w by dsimp [dgETailSlotBase]; omega]) rfl)
              (by dsimp [BinOp.eval, dgIntToExtBase]; omega)) hu_read)
            (by dsimp [BinOp.eval]; omega)) hu0_read, rfl, rfl, by simp [Expr.size]⟩
      have hp12 : Runs w p ω (.assign 16 (.load (.bin .add (.reg 11) (.load (.bin .add (.reg 12) (.load (.bin .add (.reg 14) (.reg 7)))))))) s11 .normal s12 11 :=
        runs_assign_iff.mpr ⟨v0, Expr.eval_load_of_eq (by
          refine Expr.eval_bin (by simp [s11, Expr.eval, hs10_r.2.1]) (Expr.eval_load_of_eq (by
            refine Expr.eval_bin (by simp [s11, Expr.eval, hs10_r.2.2.1]) (Expr.eval_load_of_eq (by
              simp [s11, Expr.eval, BinOp.eval, hs10_r.1, hs10_r.2.2.2.2,
                show dgEHeadSlotBase dgGPtr vCap eCap + e < 2 ^ w by dsimp [dgEHeadSlotBase]; omega]) rfl)
              (by dsimp [BinOp.eval, dgIntToExtBase]; omega)) hv_read)
            (by dsimp [BinOp.eval]; omega)) hv0_read, rfl, rfl, by simp [Expr.size]⟩
      have hs12_r : s12.regs 0 = hWin ∧ s12.regs 2 = rootsBuf ∧ s12.regs 3 = fDelBuf ∧ s12.regs 4 = cntPtr ∧
          s12.regs 15 = u0 ∧ s12.regs 16 = v0 :=
        ⟨by simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, stIn, startState],
         by simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, stIn, startState],
         by simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, stIn, startState],
         by simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, stIn, startState],
         by simp [s12, s11], by simp [s12]⟩
      have hc_1 : Runs w p ω (.call 17 bLogAdd [.reg 0, .reg 15, .reg 2, .reg 3, .reg 4]) s12 .normal s13 (5 + c1 + 1) :=
        runs_call_iff.mpr ⟨[hWin, u0, rootsBuf, fDelBuf, cntPtr], _, .returned 0, st1, c1,
          by simp [evalArgs, Expr.eval, hs12_r.1, hs12_r.2.1, hs12_r.2.2.1, hs12_r.2.2.2.1, hs12_r.2.2.2.2.1],
          hpLogAdd, hr1, rfl, rfl, by simp [argsSize, Expr.size]⟩
      have hc_2 : Runs w p ω (.call 17 bLogAdd [.reg 0, .reg 16, .reg 2, .reg 3, .reg 4]) s13 .normal s14 (5 + c2 + 1) :=
        runs_call_iff.mpr ⟨[hWin, v0, rootsBuf, fDelBuf, cntPtr], _, .returned 0, st2, c2,
          by simp [s13, evalArgs, Expr.eval, hs12_r.1, hs12_r.2.1, hs12_r.2.2.1, hs12_r.2.2.2.1, hs12_r.2.2.2.2.2],
          hpLogAdd, hr2, rfl, rfl, by simp [argsSize, Expr.size]⟩
      have hbody : Runs w p ω (compPreLogDelStmt bLogAdd) s2 .normal s14 (c1 + c2 + 102) :=
        runs_seq_iff.mpr (Or.inr ⟨s3, 5, c1 + c2 + 96, hp3,
        runs_seq_iff.mpr (Or.inr ⟨s4, 5, c1 + c2 + 90, hp4,
        runs_seq_iff.mpr (Or.inr ⟨s5, 5, c1 + c2 + 84, hp5,
        runs_seq_iff.mpr (Or.inr ⟨s6, 5, c1 + c2 + 78, hp6,
        runs_seq_iff.mpr (Or.inr ⟨s7, 5, c1 + c2 + 72, hp7,
        runs_seq_iff.mpr (Or.inr ⟨s8, 8, c1 + c2 + 63, hp8,
        runs_seq_iff.mpr (Or.inr ⟨s9, 12, c1 + c2 + 50, hp9,
        runs_seq_iff.mpr (Or.inr ⟨s10, 12, c1 + c2 + 37, hp10,
        runs_seq_iff.mpr (Or.inr ⟨s11, 11, c1 + c2 + 25, hp11,
        runs_seq_iff.mpr (Or.inr ⟨s12, 11, c1 + c2 + 13, hp12,
        runs_seq_iff.mpr (Or.inr ⟨s13, 5 + c1 + 1, 5 + c2 + 1, hc_1, hc_2, by omega⟩),
          by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩)
      have hcond2 : Runs w p ω (.cond (.bin .eq (.reg 5) (.const 1)) (compPreLogDelStmt bLogAdd) (compPreLogSplitStmt bLogAdd))
          s2 .normal s14 (c1 + c2 + 106) :=
        runs_cond_iff.mpr ⟨1, c1 + c2 + 102, by simp [s2, s1, Expr.eval, BinOp.eval, hw1], by simpa using hbody, by simp [Expr.size]; omega⟩
      have hcond1 : Runs w p ω (.cond (.bin .eq (.reg 5) (.const 0)) (compPreLogInsStmt bLogAdd)
          (.cond (.bin .eq (.reg 5) (.const 1)) (compPreLogDelStmt bLogAdd) (compPreLogSplitStmt bLogAdd)))
          s2 .normal s14 (c1 + c2 + 110) :=
        runs_cond_iff.mpr ⟨0, c1 + c2 + 106, by simp [s2, s1, Expr.eval, BinOp.eval, hw0], by simpa using hcond2, by simp [Expr.size]; omega⟩
      have hret : Runs w p ω (.ret (.const 0)) s14 (.returned 0) s14 2 :=
        runs_ret_iff.mpr ⟨0, by simp [Expr.eval, hw0], rfl, rfl, by simp [Expr.size]⟩
      have hfull : Runs w p ω (compPreLogProc bLogAdd) stIn (.returned 0) s14 (c1 + c2 + 123) :=
        runs_seq_iff.mpr (Or.inr ⟨s1, 3, c1 + c2 + 119, hp1,
          runs_seq_iff.mpr (Or.inr ⟨s2, 5, c1 + c2 + 113, hp2,
            runs_seq_iff.mpr (Or.inr ⟨s14, c1 + c2 + 110, 2, hcond1, hret, by omega⟩), by omega⟩), by omega⟩)
      exact ⟨s14, c1 + c2 + 123, hfull, rfl, by omega⟩
    obtain ⟨stF, cF, hfull, hmF, hcF⟩ := hrun_del
    obtain ⟨hvc, hfc, hndEc, hsEc, hndRc, hsRc⟩ :=
      compPreLog_two_cuts_combine hv1 hf1 hndE1 hsE1 hndR1 hsR1 hv2 hf2 hndE2 hsE2 hndR2 hsR2
    have hlen_le : (cuts1 ++ cuts2).length ≤ ((applyLSFUpdate S (.delete e)).R_orig \ S.R_orig).card := by
      have hcard := (List.toFinset_card_of_nodup hndRc).symm
      rw [List.length_map] at hcard; rw [hcard, hsRc]
      refine Finset.card_le_card (fun z hz => ?_)
      have hR2_eq : S2.R_orig = (applyLSFUpdate S (.delete e)).R_orig := by
        dsimp only [applyLSFUpdate, LSFState.R_orig, LSFState.TH]; rw [hR0_2]
      rw [← hR2_eq]; simp only [LSFState.RF, LSFState.R, Finset.mem_sdiff, Finset.mem_union] at hz ⊢
      exact ⟨by rcases hz.1 with h | h; exact h; exact absurd (Or.inr h) hz.2, fun h => hz.2 (Or.inl h)⟩
    have hcnt_tot : cnt + cuts1.length + cuts2.length ≤ cap := by
      simp only [List.length_append] at hlen_le; omega
    refine ⟨stF, cF, x2, S2, cuts1 ++ cuts2, hfull, hs1.trans hs2, hmF ▸ hrep2, hS2_G, happ_eq,
      by rw [hRF_del], congrArg RootedForest.R hRF_del, hlen_le, by rw [hmF, hcnt2]; simp [Nat.add_assoc], ?_, ?_,
      hvc, hfc, hndEc, hsEc, hndRc, hsRc, ?_⟩
    · intro i hi
      rw [hmF]
      by_cases h1 : i < cuts1.length
      · have hfr_r := hfr2 (rootsBuf + (cnt + i)) (by rcases hbuf with ⟨_, h, _⟩; omega)
          (by rcases hbuf with ⟨_, _, _, _, h, _⟩; omega) (Or.inl (by omega))
          (by rcases hbuf with ⟨_, _, _, h, _⟩; omega)
        have hfr_f := hfr2 (fDelBuf + (cnt + i)) (by rcases hbuf with ⟨_, _, h, _⟩; omega)
          (by rcases hbuf with ⟨_, _, _, _, _, h, _⟩; omega)
          (by rcases hbuf with ⟨_, _, _, h, _⟩; omega) (Or.inl (by omega))
        simpa [List.getElem_append_left h1] using ⟨hfr_r.trans (hlog1 i h1).1, hfr_f.trans (hlog1 i h1).2⟩
      · have h2 : i - cuts1.length < cuts2.length := by simp at hi; omega
        have heq := hlog2 (i - cuts1.length) h2
        rw [show cnt + cuts1.length + (i - cuts1.length) = cnt + i by omega] at heq
        simpa [List.getElem_append_right (by omega : cuts1.length ≤ i)] using heq
    · intro addr ha hnc hnr hnf
      rw [hmF]; simp only [List.length_append] at hnr hnf
      exact (hfr2 addr ha hnc (by omega) (by omega)).trans (hfr1 addr ha hnc (by omega) (by omega))
    · rw [hmF]; simp only [List.length_append]; omega
  | split v v' St Sh =>
    have hUpd_info : (mem updPtr = 2 ∨ mem updPtr = 3) ∧ mem (updPtr + 1) = v := by
      rcases hUpdAt with ⟨Lt, Lh, _, _, _, _, _, hLA⟩ | ⟨Lt, Lh, _, _, _, _, _, hLA⟩
      · exact ⟨Or.inl (by simpa using hLA 0 (by simp)), by simpa using hLA 1 (by simp)⟩
      · exact ⟨Or.inr (by simpa using hLA 0 (by simp)), by simpa using hLA 1 (by simp)⟩
    obtain ⟨htag_23, hm1⟩ := hUpd_info
    set tag := mem updPtr
    have htag0 : tag ≠ 0 := by rcases htag_23 with h | h <;> omega
    have htag1 : tag ≠ 1 := by rcases htag_23 with h | h <;> omega
    have hvG : v ∈ S.G.V := hu_valid.1
    have hv_lt : v < vCap := hdgG.2.1 v hvG
    set vOrig := S.origVert v
    have hvOrigT : vOrig ∈ S.T₀.V := lsfOrigVert_mem_T0 hInv hvG
    have hvOrig_m : mem (origBase + v) = vOrig := hOrig_mem v hvG hv_lt
    set S1 : LSFState := { S with R₀_base := insert vOrig S.R₀_base }
    have hstep_sp := applyLSFUpdate_split_step hInv hu_valid
    have happ_eq : applyLSFUpdate S1 (.split v v' St Sh) = applyLSFUpdate S (.split v v' St Sh) := by
      have hvOrigT' : S.origVert v ∈ S.T₀.V := hvOrigT
      dsimp only [applyLSFUpdate, S1, vOrig]; congr 1; simp [hvOrigT']
    have hRorig_sp : (applyLSFUpdate S (.split v v' St Sh)).R_orig = S1.R_orig := hstep_sp.2.2.2.1
    have hcap1 : cnt + (S1.R_orig \ S.R_orig).card ≤ cap := by rwa [← hRorig_sp]
    obtain ⟨st1, c1, x1, cuts1, hr1, hs1, hrep1, hcnt1, hlog1, hfr1, hv1, hf1, hndE1, hsE1, hndR1, hsR1, hc1⟩ :=
      hcall_log (SameStaticConcrete.refl x) hrep_orig hvOrigT hcnt_m hcap1
    let stIn := startState [hWin, updPtr, rootsBuf, fDelBuf, cntPtr] mem pos
    let s1 : State := { stIn with regs := Function.update stIn.regs 5 tag }; let s2 : State := { s1 with regs := Function.update s1.regs 6 auxPtr }
    let s3 : State := { s2 with regs := Function.update s2.regs 7 v }; let s4 : State := { s3 with regs := Function.update s3.regs 8 origBase }
    let s5 : State := { s4 with regs := Function.update s4.regs 9 vOrig }; let s6 : State := { mem := st1.mem, regs := Function.update s5.regs 10 0, pos := st1.pos }
    have hp1 : Runs w p ω (.assign 5 (.load (.reg 1))) stIn .normal s1 3 :=
      runs_assign_iff.mpr ⟨tag, Expr.eval_load_of_eq (by simp [stIn, Expr.eval, startState]) rfl, rfl, rfl, by simp [Expr.size]⟩
    have hp2 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 0) (.const lsfOffAuxPtr)))) s1 .normal s2 5 :=
      runs_assign_iff.mpr ⟨auxPtr, Expr.eval_load_of_eq (by
        simp [s1, stIn, Expr.eval, BinOp.eval, startState,
          show lsfOffAuxPtr < 2 ^ w by dsimp [lsfOffAuxPtr, lsfHdrSize] at hb_hdr_ltw ⊢; omega,
          show hWin + lsfOffAuxPtr < 2 ^ w by dsimp [lsfOffAuxPtr, lsfHdrSize] at hb_hdr_ltw ⊢; omega]) haux_ptr_m,
        rfl, rfl, by simp [Expr.size]⟩
    have hp3 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 1) (.const 1)))) s2 .normal s3 5 :=
      runs_assign_iff.mpr ⟨v, Expr.eval_load_of_eq (by simp [s2, s1, stIn, Expr.eval, BinOp.eval, startState, hw1, show updPtr + 1 < 2 ^ w by omega]) hm1,
        rfl, rfl, by simp [Expr.size]⟩
    have hp4 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 6) (.const auxOffOrigVertPtr)))) s3 .normal s4 5 :=
      runs_assign_iff.mpr ⟨origBase, Expr.eval_load_of_eq (by
        simp [s3, s2, Expr.eval, BinOp.eval,
          show auxOffOrigVertPtr < 2 ^ w by dsimp [auxOffOrigVertPtr, auxHdrSize] at haux_hdr_ltw ⊢; omega,
          show auxPtr + auxOffOrigVertPtr < 2 ^ w by dsimp [auxOffOrigVertPtr, auxHdrSize] at haux_hdr_ltw ⊢; omega]) haux_orig_ptr,
        rfl, rfl, by simp [Expr.size]⟩
    have hp5 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 8) (.reg 7)))) s4 .normal s5 5 :=
      runs_assign_iff.mpr ⟨vOrig, Expr.eval_load_of_eq (by simp [s4, s3, Expr.eval, BinOp.eval, show origBase + v < 2 ^ w by omega]) hvOrig_m,
        rfl, rfl, by simp [Expr.size]⟩
    have hc_1 : Runs w p ω (.call 10 bLogAdd [.reg 0, .reg 9, .reg 2, .reg 3, .reg 4]) s5 .normal s6 (5 + c1 + 1) :=
      runs_call_iff.mpr ⟨[hWin, vOrig, rootsBuf, fDelBuf, cntPtr], _, .returned 0, st1, c1,
        by simp [s5, s4, s3, s2, s1, stIn, evalArgs, Expr.eval, startState], hpLogAdd, hr1, rfl, rfl, by simp [argsSize, Expr.size]⟩
    have hbody : Runs w p ω (compPreLogSplitStmt bLogAdd) s2 .normal s6 (c1 + 24) :=
      runs_seq_iff.mpr (Or.inr ⟨s3, 5, c1 + 18, hp3,
        runs_seq_iff.mpr (Or.inr ⟨s4, 5, c1 + 12, hp4,
          runs_seq_iff.mpr (Or.inr ⟨s5, 5, 5 + c1 + 1, hp5, hc_1, by omega⟩), by omega⟩), by omega⟩)
    have hcond2 : Runs w p ω (.cond (.bin .eq (.reg 5) (.const 1)) (compPreLogDelStmt bLogAdd) (compPreLogSplitStmt bLogAdd))
        s2 .normal s6 (c1 + 28) :=
      runs_cond_iff.mpr ⟨0, c1 + 24, by simp [s2, s1, Expr.eval, BinOp.eval, hw1, htag1], by simpa using hbody, by simp [Expr.size]; omega⟩
    have hcond1 : Runs w p ω (.cond (.bin .eq (.reg 5) (.const 0)) (compPreLogInsStmt bLogAdd)
        (.cond (.bin .eq (.reg 5) (.const 1)) (compPreLogDelStmt bLogAdd) (compPreLogSplitStmt bLogAdd)))
        s2 .normal s6 (c1 + 32) :=
      runs_cond_iff.mpr ⟨0, c1 + 28, by simp [s2, s1, Expr.eval, BinOp.eval, hw0, htag0], by simpa using hcond2, by simp [Expr.size]; omega⟩
    have hret : Runs w p ω (.ret (.const 0)) s6 (.returned 0) s6 2 :=
      runs_ret_iff.mpr ⟨0, by simp [Expr.eval, hw0], rfl, rfl, by simp [Expr.size]⟩
    have hfull : Runs w p ω (compPreLogProc bLogAdd) stIn (.returned 0) s6 (c1 + 45) :=
      runs_seq_iff.mpr (Or.inr ⟨s1, 3, c1 + 41, hp1,
        runs_seq_iff.mpr (Or.inr ⟨s2, 5, c1 + 35, hp2,
          runs_seq_iff.mpr (Or.inr ⟨s6, c1 + 32, 2, hcond1, hret, by omega⟩), by omega⟩), by omega⟩)
    have hFE_sp : S1.RF.F.E = (applyLSFUpdate S (.split v v' St Sh)).RF.F.E := by
      dsimp only [LSFState.RF]; rw [hRorig_sp]; rfl
    have hlen_le : cuts1.length ≤ ((applyLSFUpdate S (.split v v' St Sh)).R_orig \ S.R_orig).card := by
      have hcard := (List.toFinset_card_of_nodup hndR1).symm
      rw [List.length_map] at hcard; rw [hcard, hsR1, hRorig_sp]
      refine Finset.card_le_card (fun z hz => ?_)
      simp only [LSFState.RF, LSFState.R, Finset.mem_sdiff, Finset.mem_union] at hz ⊢
      exact ⟨by rcases hz.1 with h | h; exact h; exact absurd (Or.inr h) hz.2, fun h => hz.2 (Or.inl h)⟩
    exact ⟨s6, c1 + 45, x1, S1, cuts1, hfull, hs1, hrep1, rfl, happ_eq, hFE_sp,
      ⟨hstep_sp.2.2.2.2.2.2.1, hstep_sp.2.2.2.2.2.1⟩, hlen_le, hcnt1, hlog1, hfr1, hv1, hf1, hndE1, hsE1, hndR1, hsR1,
      by dsimp only [s6]; omega⟩

end

end MinCostFlow.SparseCore.Program

