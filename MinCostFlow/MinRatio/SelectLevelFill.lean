module

public import MinCostFlow.MinRatio.SelectRegionSkeleton
public import MinCostFlow.MinRatio.SelectCoreLenFill
public import MinCostFlow.MinRatio.SelectBlocksRefill
public import MinCostFlow.LastLevelProgram.Readout
import WordRAM.Tactic

/-!
# Populating the terminal select level block (`SelectLevelFill`)

Provides bounded-frame helpers for `SelBlocksDataAt` (`setLast_below`, `setF_below`,
`setEmb_below`) and verifies `selectFillLastLevelBody`, which populates `B.lastGPtr`, `B.fPtr d`,
and `B.lenPtr d` (at precision `P + pLast`, `Lw = L`) from `srcGd` and
`LastLevelProgram.lastLevelRepresentation` at `termHandle` in `O(m_d * L^2 + n_d + m_{F_d})` steps
and `O(m_d * L + m_{F_d})` scratch words, with zero extra readout hypotheses.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program SparseCore.Program
open MinCostFlow.LastLevelProgram

/-! ## 1. Bounded-frame helpers for `SelBlocksDataAt` -/

private lemma regBlk_bounds {B : SelectBlocksLoc} {j a : ℕ} (hj : j ≤ B.d) (ha : B.regBlk j a) :
    B.base ≤ a ∧ a < B.endAddr := by
  have h1 := B.blk_le_last hj
  unfold SelectBlocksLoc.regBlk SelectBlocksLoc.fPtr at ha
  unfold SelectBlocksLoc.fPtr at h1
  unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr
  exact ⟨by omega, by omega⟩

/-- Update `B.lastGPtr` inside `SelBlocksDataAt` using only agreement below `scratch` (`B.endAddr ≤ scratch`). -/
theorem SelBlocksDataAt.setLast_below {mem mem' : ℕ → ℕ} {B : SelectBlocksLoc} {P pLast scratch : ℕ}
    {D : SelBlocksData} {Gd' : MGraph} (h : SelBlocksDataAt mem B P D pLast)
    (hEnd : B.endAddr ≤ scratch)
    (hag : ∀ a < scratch, ¬ B.regLast a → mem' a = mem a)
    (hLast' : SelPartLast mem' B Gd') :
    SelBlocksDataAt mem' B P { D with Gd := Gd' } pLast := by
  obtain ⟨hF, hPhi, hLen, hEmb, _, hG0⟩ := h
  exact ⟨fun j' hj' => (hF j' hj').of_agree fun a ha =>
      hag a (lt_of_lt_of_le (regBlk_bounds hj' (B.regF_blk ha)).2 hEnd)
        (B.regBlk_not_last hj' (B.regF_blk ha)),
    fun j' hj' => (hPhi j' hj').of_agree fun a ha =>
      hag a (lt_of_lt_of_le (regBlk_bounds hj' (B.regPhi_blk ha)).2 hEnd)
        (B.regBlk_not_last hj' (B.regPhi_blk ha)),
    fun j' hj' => (hLen j' hj').of_agree fun a ha =>
      hag a (lt_of_lt_of_le (regBlk_bounds hj' (B.regLen_blk ha)).2 hEnd)
        (B.regBlk_not_last hj' (B.regLen_blk ha)),
    fun j' hj' => (hEmb j' hj').of_agree fun a ha =>
      hag a (lt_of_lt_of_le (regBlk_bounds hj'.le (B.regEmb_blk ha)).2 hEnd)
        (B.regBlk_not_last hj'.le (B.regEmb_blk ha)),
    hLast',
    hG0.of_agree fun a ha => hag a (lt_of_lt_of_le ha.2 hEnd) (fun h' => B.regLast_not_g0 h' ha)⟩

/-- Update `B.fPtr j` inside `SelBlocksDataAt` using only agreement below `scratch` (`B.endAddr ≤ scratch`). -/
theorem SelBlocksDataAt.setF_below {mem mem' : ℕ → ℕ} {B : SelectBlocksLoc} {P j pLast scratch : ℕ}
    {D : SelBlocksData} {F' : MGraph} (h : SelBlocksDataAt mem B P D pLast) (hj : j ≤ B.d)
    (hEnd : B.endAddr ≤ scratch)
    (hag : ∀ a < scratch, ¬ B.regF j a → mem' a = mem a)
    (hF' : SelPartF mem' B j F') :
    SelBlocksDataAt mem' B P { D with F := Function.update D.F j F' } pLast := by
  obtain ⟨hF0, hPhi, hLen, hEmb, hLast, hG0⟩ := h
  refine ⟨fun j' hj' => ?_,
    fun j' hj' => (hPhi j' hj').of_agree fun a ha =>
      hag a (lt_of_lt_of_le (regBlk_bounds hj' (B.regPhi_blk ha)).2 hEnd)
        (fun h' => B.regF_not_phi h' ha),
    fun j' hj' => (hLen j' hj').of_agree fun a ha =>
      hag a (lt_of_lt_of_le (regBlk_bounds hj' (B.regLen_blk ha)).2 hEnd)
        (fun h' => B.regF_not_len h' ha),
    fun j' hj' => (hEmb j' hj').of_agree fun a ha =>
      hag a (lt_of_lt_of_le (regBlk_bounds hj'.le (B.regEmb_blk ha)).2 hEnd)
        (fun h' => B.regF_not_emb h' ha),
    hLast.of_agree fun a ha =>
      hag a (by unfold SelectBlocksLoc.regLast at ha; unfold SelectBlocksLoc.endAddr at hEnd; omega)
        (fun h' => B.regBlk_not_last hj (B.regF_blk h') ha),
    hG0.of_agree fun a ha =>
      hag a (lt_of_lt_of_le ha.2 hEnd) (fun h' => B.regBlk_not_g0 hj (B.regF_blk h') ha)⟩
  by_cases hjj : j' = j
  · subst hjj; simpa using hF'
  · simp only [Function.update_of_ne hjj]
    exact (hF0 j' hj').of_agree fun a ha =>
      hag a (lt_of_lt_of_le (regBlk_bounds hj' (B.regF_blk ha)).2 hEnd)
        (fun h' => B.regF_disj (Ne.symm hjj) h' ha)

/-- Update `B.lenPtr j` inside `SelBlocksDataAt` using only agreement below `scratch` (`B.endAddr ≤ scratch`). -/
theorem SelBlocksDataAt.setLen_below {mem mem' : ℕ → ℕ} {B : SelectBlocksLoc} {P j pLast scratch : ℕ}
    {D : SelBlocksData} {E' : Finset ℕ} {lenj' : ℕ → ℝ} (h : SelBlocksDataAt mem B P D pLast)
    (hj : j ≤ B.d) (hEnd : B.endAddr ≤ scratch)
    (hag : ∀ a < scratch, ¬ B.regLen j a → mem' a = mem a)
    (hLen' : SelPartLen mem' B P j E' lenj' pLast) :
    SelBlocksDataAt mem' B P
      { D with E := Function.update D.E j E', len := Function.update D.len j lenj' } pLast := by
  obtain ⟨hF, hPhi, hLen0, hEmb, hLast, hG0⟩ := h
  refine ⟨fun j' hj' => (hF j' hj').of_agree fun a ha =>
      hag a (lt_of_lt_of_le (regBlk_bounds hj' (B.regF_blk ha)).2 hEnd)
        (fun h' => B.regF_not_len ha h'),
    fun j' hj' => (hPhi j' hj').of_agree fun a ha =>
      hag a (lt_of_lt_of_le (regBlk_bounds hj' (B.regPhi_blk ha)).2 hEnd)
        (fun h' => B.regPhi_not_len ha h'),
    fun j' hj' => ?_,
    fun j' hj' => (hEmb j' hj').of_agree fun a ha =>
      hag a (lt_of_lt_of_le (regBlk_bounds hj'.le (B.regEmb_blk ha)).2 hEnd)
        (fun h' => B.regLen_not_emb h' ha),
    hLast.of_agree fun a ha =>
      hag a (by unfold SelectBlocksLoc.regLast at ha; unfold SelectBlocksLoc.endAddr at hEnd; omega)
        (fun h' => B.regBlk_not_last hj (B.regLen_blk h') ha),
    hG0.of_agree fun a ha =>
      hag a (lt_of_lt_of_le ha.2 hEnd) (fun h' => B.regBlk_not_g0 hj (B.regLen_blk h') ha)⟩
  by_cases hjj : j' = j
  · subst hjj; simpa using hLen'
  · simp only [Function.update_of_ne hjj]
    exact (hLen0 j' hj').of_agree fun a ha =>
      hag a (lt_of_lt_of_le (regBlk_bounds hj' (B.regLen_blk ha)).2 hEnd)
        (fun h' => B.regLen_disj (Ne.symm hjj) h' ha)

/-- Update `B.embPtr j` inside `SelBlocksDataAt` using only agreement below `scratch` (`B.endAddr ≤ scratch`). -/
theorem SelBlocksDataAt.setEmb_below {mem mem' : ℕ → ℕ} {B : SelectBlocksLoc} {P j pLast scratch : ℕ}
    {D : SelBlocksData} {E' : Finset ℕ} {emb' : Embedding} (h : SelBlocksDataAt mem B P D pLast)
    (hj : j < B.d) (hEnd : B.endAddr ≤ scratch)
    (hag : ∀ a < scratch, ¬ B.regEmb j a → mem' a = mem a)
    (hEmb' : SelPartEmb mem' B j E' emb') :
    SelBlocksDataAt mem' B P
      { D with coreE := Function.update D.coreE j E', emb := Function.update D.emb j emb' } pLast := by
  obtain ⟨hF, hPhi, hLen, hEmb0, hLast, hG0⟩ := h
  refine ⟨fun j' hj' => (hF j' hj').of_agree fun a ha =>
      hag a (lt_of_lt_of_le (regBlk_bounds hj' (B.regF_blk ha)).2 hEnd)
        (fun h' => B.regF_not_emb ha h'),
    fun j' hj' => (hPhi j' hj').of_agree fun a ha =>
      hag a (lt_of_lt_of_le (regBlk_bounds hj' (B.regPhi_blk ha)).2 hEnd)
        (fun h' => B.regPhi_not_emb ha h'),
    fun j' hj' => (hLen j' hj').of_agree fun a ha =>
      hag a (lt_of_lt_of_le (regBlk_bounds hj' (B.regLen_blk ha)).2 hEnd)
        (fun h' => B.regLen_not_emb ha h'),
    fun j' hj' => ?_,
    hLast.of_agree fun a ha =>
      hag a (by unfold SelectBlocksLoc.regLast at ha; unfold SelectBlocksLoc.endAddr at hEnd; omega)
        (fun h' => B.regBlk_not_last hj.le (B.regEmb_blk h') ha),
    hG0.of_agree fun a ha =>
      hag a (lt_of_lt_of_le ha.2 hEnd) (fun h' => B.regBlk_not_g0 hj.le (B.regEmb_blk h') ha)⟩
  by_cases hjj : j' = j
  · subst hjj; simpa using hEmb'
  · simp only [Function.update_of_ne hjj]
    exact (hEmb0 j' hj').of_agree fun a ha =>
      hag a (lt_of_lt_of_le (regBlk_bounds hj'.le (B.regEmb_blk ha)).2 hEnd)
        (fun h' => B.regEmb_disj (Ne.symm hjj) h' ha)

/-! ## 2. `selectFillLastLevelBody`: populate `G_d`, `F_d`, `len_d` at level `d` -/

/-- Populate `B.lastGPtr`, `B.fPtr d`, and `B.lenPtr d` (`shift = pLast`, `Lw = L`) at terminal
level `d` from `srcGd` and `LastLevelProgram.lastLevelRepresentation` at `termHandle`.
Arguments: `[metaBase, d, termHandle, termBran, prevLen, L, pLast, srcGd, scratch]` (`reg 0..8`).
Returns the new scratch pointer. -/
def selectFillLastLevelBody (dgCopyProc coreLenProc : ℕ) : Stmt :=
  .assign 9 (.bin .add (.reg 1) (.const 1)) ;; -- d + 1
  .assign 10 (.bin .add (.reg 0) (.const 2)) ;; -- tb
  .assign 11 (.load (.bin .add (.bin .add (.reg 10) (.reg 9)) (.reg 1))) ;; -- vCap
  .assign 12 (.load (.bin .add (.bin .add (.reg 10) (.bin .mul (.const 2) (.reg 9))) (.reg 1))) ;; -- eCap
  .assign 13 (.load (.bin .add (.bin .add (.reg 10) (.bin .mul (.const 4) (.reg 9))) (.reg 1))) ;; -- lenD
  .assign 14 (.load (.bin .add (.bin .add (.reg 10) (.bin .mul (.const 6) (.reg 9))) (.reg 1))) ;; -- fD
  .assign 15 (.load (.bin .add (.reg 10) (.reg 1))) ;; -- lastGPtr
  .call 16 dgCopyProc [.reg 15, .reg 7, .reg 8] ;; -- sc1 (copy G_d -> B.lastGPtr)
  .assign 17 (.load (.bin .add (.bin .add (.reg 2) (.const 1)) (.reg 3))) ;; -- brBase
  .assign 18 (.load (.bin .add (.reg 17) (.const 1))) ;; -- fBase
  .assign 19 (.load (.bin .add (.reg 17) (.const 3))) ;; -- stDesc
  .call 16 dgCopyProc [.reg 14, .reg 18, .reg 16] ;; -- sc2 (copy F_d -> B.fPtr d)
  .assign 22 (.load (.bin .add (.reg 15) (.const 3))) ;; -- m_d = G_d.m
  .cond (.reg 22)
    (.assign 20 (.load (.reg 19)) ;; -- numBase
     .assign 21 (.load (.bin .add (.reg 19) (.const 1))) ;; -- denBase
     .assign 23 (.bin .add (.bin .add (.bin .add (.reg 15) (.const 4)) (.bin .mul (.const 7) (.reg 11)))
       (.reg 12)) ;; -- dgEListBase lastGPtr vCap eCap
     .call 16 coreLenProc [.reg 4, .reg 20, .reg 21, .reg 13, .reg 23, .reg 22, .reg 5, .reg 5,
       .reg 6, .reg 16] ;;
     .ret (.reg 16))
    (.ret (.reg 16))

theorem selectFillLastLevelBody_noRand (dgCopyProc coreLenProc : ℕ) :
    (selectFillLastLevelBody dgCopyProc coreLenProc).NoRand := by
  simp [selectFillLastLevelBody, Stmt.NoRand]

/-- Scratch space bound for `selectFillLastLevelBody`. -/
def selectFillLastLevelSpace (mGd mFd L : ℕ) : ℕ :=
  3 * mGd + 3 * mFd + mGd * selCoreLenEdgeSpace L L

/-- Step cost bound for `selectFillLastLevelBody`. -/
def selectFillLastLevelCost (nOldG mOldG nOldF mOldF nGd mGd nFd mFd L : ℕ) : ℕ :=
  dgCopyRefillCost nOldG mOldG nGd mGd + dgCopyRefillCost nOldF mOldF nFd mFd +
    mGd * (selCoreLenEdgeCost L L + 40) + 320

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program SparseCore.Program
open MinCostFlow.LastLevelProgram

/-! ## 3. Verification of `selectFillLastLevelBody` -/

set_option maxHeartbeats 800000 in
/-- Two-sided version of `selectFillLastLevel_runs`: populates `B.lastGPtr`, `B.fPtr B.d`, and
`B.lenPtr B.d` (at precision `P + pLast`) when the terminal collection `[termHandle, limit)` lies
either strictly below `B.base` (as during Init) or inside `[B.endAddr, scratch)` (as after a deep
shift). -/
theorem selectFillLastLevel_runs_disj
    {w P pLast dgCopyProc coreLenProc : ℕ}
    {B : SelectBlocksLoc}
    {metaBase termHandle termBran prevLen srcGd srcVCap srcECap vcLast ecLast limit scratch pos : ℕ}
    {solverG : ℕ → ℕ} {D : SelBlocksData} {Gd : MGraph} {lastK : ℕ} {lastLSFs : ℕ → LSF}
    {prevVal : ℕ → ℝ} {mem : ℕ → ℕ} {p : Program} {ω : ℕ → Bool}
    (hw16 : 16 < 2 ^ w) (hpLastW : pLast < 2 ^ w) (hLkW : B.Lk < 2 ^ w)
    (htab : SelectMetaTableAt mem (selectMlocOf B metaBase solverG pLast))
    (hblk : SelBlocksDataAt mem B P D pLast)
    (hMetaLe : metaBase + selectLevelMetaSize B.d ≤ B.base)
    (hEndSc : B.endAddr ≤ scratch)
    (hSrcG : DynGraphAt mem srcGd srcVCap srcECap Gd)
    (hSrcDisj : srcGd + dynGraphSize srcVCap srcECap ≤ B.base ∨ B.endAddr ≤ srcGd)
    (hSrcSc : srcGd + dynGraphSize srcVCap srcECap ≤ scratch)
    (hGdV : ∀ v ∈ Gd.V, v < B.vCap) (hGdE : ∀ e ∈ Gd.E, e < B.eCap)
    (hTermRep : (lastLevelRepresentation vcLast ecLast 4 B.Lk P Gd.E).rep termHandle (lastK, lastLSFs) limit mem)
    (hBranLt : termBran < lastK)
    (hTermDisj : limit ≤ B.base ∨ (B.endAddr ≤ termHandle ∧ limit ≤ scratch))
    (hFdV : ∀ v ∈ (lastLSFs termBran).F.F.V, v < B.vCap)
    (hFdE : ∀ e ∈ (lastLSFs termBran).F.F.E, e < B.eCap)
    (hPrevLe : prevLen + B.eCap * B.Lk ≤ scratch)
    (hPrevDisj : prevLen + B.eCap * B.Lk ≤ B.lenPtr B.d ∨ B.embPtr B.d ≤ prevLen)
    (hPrevOffF : prevLen + B.eCap * B.Lk ≤ B.fPtr B.d ∨ B.phiPtr B.d ≤ prevLen)
    (hPrevOffLast : prevLen + B.eCap * B.Lk ≤ B.lastGPtr ∨ B.g0Ptr ≤ prevLen)
    (hPrevVal : EdgeValuesAt mem prevLen 4 B.Lk P Gd.E prevVal)
    (hLenFit : ∀ e ∈ Gd.E,
      Num.Fits 4 B.Lk (Num.intVal mem (prevLen + e * B.Lk) 4 B.Lk * (2 : ℤ) ^ pLast) ∧
      ∃ q : ℤ, Num.Fits 4 B.Lk q ∧
        (q : ℝ) / (2 : ℝ) ^ (P + pLast) = (lastLSFs termBran).wstr e * prevVal e)
    (hDgCopyG : MeetsContract w p dgCopyProc
      (dgCopyRefillContract w B.vCap B.eCap srcVCap srcECap D.Gd Gd))
    (hDgCopyF : MeetsContract w p dgCopyProc
      (dgCopyRefillContract w B.vCap B.eCap vcLast ecLast (D.F B.d) (lastLSFs termBran).F.F))
    (hCoreLen : ∀ eL : List ℕ, MeetsContract w p coreLenProc (selCoreLenFillContract w P B.eCap eL))
    (hz : ZeroFrom mem scratch)
    (hroom : scratch + selectFillLastLevelSpace Gd.m (lastLSFs termBran).F.F.m B.Lk < 2 ^ w) :
    ∃ sc3 cost out,
      Runs w p ω (selectFillLastLevelBody dgCopyProc coreLenProc)
        (startState [metaBase, B.d, termHandle, termBran, prevLen, B.Lk, pLast, srcGd, scratch] mem pos)
        (.returned sc3) out cost ∧
      sc3 = scratch + selectFillLastLevelSpace Gd.m (lastLSFs termBran).F.F.m B.Lk ∧
      SelBlocksDataAt out.mem B P
        { D with
          Gd := Gd
          F := Function.update D.F B.d (lastLSFs termBran).F.F
          E := Function.update D.E B.d Gd.E
          len := Function.update D.len B.d (fun e => (lastLSFs termBran).wstr e * prevVal e) } pLast ∧
      ZeroFrom out.mem sc3 ∧
      (∀ a < scratch, ¬ B.regLast a → ¬ B.regF B.d a → ¬ B.regLen B.d a → out.mem a = mem a) ∧
      cost ≤ selectFillLastLevelCost D.Gd.n D.Gd.m (D.F B.d).n (D.F B.d).m
        Gd.n Gd.m (lastLSFs termBran).F.F.n (lastLSFs termBran).F.F.m B.Lk := by
  have hw1 : 1 < 2 ^ w := by omega
  have hBaseLeEnd : B.base ≤ B.endAddr := by rw [B.endAddr_eq]; omega
  have hBlkD := B.blk_le_last (le_refl B.d)
  have hBaseLeFD : B.base ≤ B.fPtr B.d := by unfold SelectBlocksLoc.fPtr; omega
  have hFDEnd : B.fPtr B.d + dynGraphSize B.vCap B.eCap = B.phiPtr B.d := rfl
  have hLenDEnd : B.lenPtr B.d + B.eCap * B.Lk = B.embPtr B.d := rfl
  have hFDLeLenD : B.phiPtr B.d ≤ B.lenPtr B.d := by unfold SelectBlocksLoc.lenPtr; omega
  have hEmbDLeLast : B.embPtr B.d ≤ B.lastGPtr := by
    unfold SelectBlocksLoc.embPtr SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr
    unfold SelectBlocksLoc.levelSize at hBlkD
    omega
  have hLastEnd : B.lastGPtr + dynGraphSize B.vCap B.eCap = B.g0Ptr := rfl
  have hG0End : B.g0Ptr + B.eCap * B.Lk = B.endAddr := rfl
  have hDgSz : dynGraphSize B.vCap B.eCap = 4 + 7 * B.vCap + 9 * B.eCap := rfl
  have hMetaSz : selectLevelMetaSize B.d = 2 + 8 * (B.d + 1) := rfl
  have hrow := htab.2.2 B.d (le_refl _)
  have hvCapM : mem (metaBase + 2 + (B.d + 1) + B.d) = B.vCap := by
    simpa [smEntryAddr, smTableOff, selectMlocOf] using hrow.2.1
  have heCapM : mem (metaBase + 2 + 2 * (B.d + 1) + B.d) = B.eCap := by
    simpa [smEntryAddr, smTableOff, selectMlocOf] using hrow.2.2.1
  have hlenDM : mem (metaBase + 2 + 4 * (B.d + 1) + B.d) = B.lenPtr B.d := by
    simpa [smEntryAddr, smTableOff, selectMlocOf] using hrow.2.2.2.2.1
  have hfDM : mem (metaBase + 2 + 6 * (B.d + 1) + B.d) = B.fPtr B.d := by
    simpa [smEntryAddr, smTableOff, selectMlocOf] using hrow.2.2.2.2.2.2.1
  have hlastGM : mem (metaBase + 2 + B.d) = B.lastGPtr := by
    simpa [smEntryAddr, smTableOff, selectMlocOf] using hrow.1
  obtain ⟨hTermLo, hPref⟩ := hTermRep
  obtain ⟨hBW, hLSF⟩ := hPref.2.2 termBran hBranLt
  set brBase := mem (termHandle + 1 + termBran)
  set fBase := mem (brBase + 1)
  set stDesc := mem (brBase + 3)
  set numBase := mem stDesc
  set denBase := mem (stDesc + 1)
  have hLimSc : limit ≤ scratch := by rcases hTermDisj with h | ⟨_, h⟩ <;> omega
  have hTermOff : ∀ a, termHandle ≤ a → a < limit → a < scratch ∧ (a < B.base ∨ B.endAddr ≤ a) := by
    intro a h1 h2; rcases hTermDisj with h | ⟨h3, h4⟩ <;> exact ⟨by omega, by omega⟩
  have hTermSlotOff := hTermOff (termHandle + 1 + termBran) (by omega) (by omega)
  have hBrBaseLo : termHandle + 1 + lastK ≤ brBase := hBW.1
  have hBrBaseHi : brBase + 4 ≤ limit := hBW.2.1
  have hfBaseLo : termHandle + 1 + lastK ≤ fBase := hBW.2.2.2.2.1
  have hfBaseHi : fBase + dynGraphSize vcLast ecLast ≤ limit := hBW.2.2.2.2.2.1
  have hStDescLo : termHandle + 1 + lastK ≤ stDesc := hBW.2.2.2.2.2.2.2.2.1
  have hStDescHi : stDesc + 2 ≤ limit := hBW.2.2.2.2.2.2.2.2.2.1
  have hNumLo : ∀ e ∈ Gd.E, termHandle + 1 + lastK ≤ numBase + e * B.Lk := fun e _ => by
    have hlo : termHandle + 1 + lastK ≤ numBase := hBW.2.2.2.2.2.2.2.2.2.2.1
    omega
  have hNumHi : ∀ e ∈ Gd.E, numBase + e * B.Lk + B.Lk ≤ limit := fun e he =>
    hBW.2.2.2.2.2.2.2.2.2.2.2.2.1 e he
  have hDenLo : ∀ e ∈ Gd.E, termHandle + 1 + lastK ≤ denBase + e * B.Lk := fun e _ => by
    have hlo : termHandle + 1 + lastK ≤ denBase := hBW.2.2.2.2.2.2.2.2.2.2.2.1
    omega
  have hDenHi : ∀ e ∈ Gd.E, denBase + e * B.Lk + B.Lk ≤ limit := fun e he =>
    hBW.2.2.2.2.2.2.2.2.2.2.2.2.2 e he
  have hSpDef : selectFillLastLevelSpace Gd.m (lastLSFs termBran).F.F.m B.Lk =
      3 * Gd.m + 3 * (lastLSFs termBran).F.F.m + Gd.m * selCoreLenEdgeSpace B.Lk B.Lk := rfl
  have hGdMLe : Gd.m ≤ B.eCap := by
    unfold MGraph.m
    calc Gd.E.card ≤ (Finset.range B.eCap).card :=
          Finset.card_le_card fun e he => Finset.mem_range.mpr (hGdE e he)
      _ = B.eCap := Finset.card_range _
  let DTarget : SelBlocksData :=
    { D with
      Gd := Gd
      F := Function.update D.F B.d (lastLSFs termBran).F.F
      E := Function.update D.E B.d Gd.E
      len := Function.update D.len B.d (fun e => (lastLSFs termBran).wstr e * prevVal e) }
  obtain ⟨o, out, cost, hrun, hpost, hcost⟩ :=
    (show ∃ o out cost,
      Runs w p ω (selectFillLastLevelBody dgCopyProc coreLenProc)
        (startState [metaBase, B.d, termHandle, termBran, prevLen, B.Lk, pLast, srcGd, scratch] mem pos)
        o out cost ∧
      (o = .returned (scratch + selectFillLastLevelSpace Gd.m (lastLSFs termBran).F.F.m B.Lk) ∧
        SelBlocksDataAt out.mem B P DTarget pLast ∧
        ZeroFrom out.mem (scratch + selectFillLastLevelSpace Gd.m (lastLSFs termBran).F.F.m B.Lk) ∧
        (∀ a < scratch, ¬ B.regLast a → ¬ B.regF B.d a → ¬ B.regLen B.d a → out.mem a = mem a)) ∧
      cost ≤ selectFillLastLevelCost D.Gd.n D.Gd.m (D.F B.d).n (D.F B.d).m
        Gd.n Gd.m (lastLSFs termBran).F.F.n (lastLSFs termBran).F.F.m B.Lk by
      apply runs_start_le
      dsimp only [startState]
      unfold selectFillLastLevelBody
      refine runs_seq_assign_flat (v := B.d + 1) (by eval_expr) ?_
      refine runs_seq_assign_flat (v := metaBase + 2) (by eval_expr) ?_
      refine runs_seq_assign_flat (v := B.vCap)
        (by simp [Expr.eval, BinOp.eval, hvCapM, show metaBase + 2 + (B.d + 1) < 2 ^ w by omega,
          show metaBase + 2 + (B.d + 1) + B.d < 2 ^ w by omega]) ?_
      refine runs_seq_assign_flat (v := B.eCap)
        (by simp [Expr.eval, BinOp.eval, heCapM, show 2 < 2 ^ w by omega,
          show 2 * (B.d + 1) < 2 ^ w by omega, show metaBase + 2 + 2 * (B.d + 1) < 2 ^ w by omega,
          show metaBase + 2 + 2 * (B.d + 1) + B.d < 2 ^ w by omega]) ?_
      refine runs_seq_assign_flat (v := B.lenPtr B.d)
        (by simp [Expr.eval, BinOp.eval, hlenDM, show 4 < 2 ^ w by omega,
          show 4 * (B.d + 1) < 2 ^ w by omega, show metaBase + 2 + 4 * (B.d + 1) < 2 ^ w by omega,
          show metaBase + 2 + 4 * (B.d + 1) + B.d < 2 ^ w by omega]) ?_
      refine runs_seq_assign_flat (v := B.fPtr B.d)
        (by simp [Expr.eval, BinOp.eval, hfDM, show 6 < 2 ^ w by omega,
          show 6 * (B.d + 1) < 2 ^ w by omega, show metaBase + 2 + 6 * (B.d + 1) < 2 ^ w by omega,
          show metaBase + 2 + 6 * (B.d + 1) + B.d < 2 ^ w by omega]) ?_
      refine runs_seq_assign_flat (v := B.lastGPtr)
        (by simp [Expr.eval, BinOp.eval, hlastGM, show metaBase + 2 + B.d < 2 ^ w by omega]) ?_
      -- Step 1: copy `G_d` from `srcGd` into `B.lastGPtr`
      refine runs_seq_call_le hDgCopyG (vs := [B.lastGPtr, srcGd, scratch])
        (by eval_expr)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro v (rfl|rfl|rfl) <;> omega)
        ⟨B.lastGPtr, srcGd, scratch, rfl, hw16, by omega, hSrcSc,
          by rcases hSrcDisj with h | h <;> [left; right] <;> omega,
          hblk.2.2.2.2.1, hSrcG, hGdV, hGdE, hz, by omega⟩ ?_
      intro sc1 mem1 pos1 hp1
      obtain ⟨hsc1Eq, hGd1, hz1, hfr1⟩ := hp1
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hsc1Eq hfr1
      subst hsc1Eq
      have hFr1OffBlocks : ∀ a < scratch, (a < B.base ∨ B.endAddr ≤ a) → mem1 a = mem a := fun a ha hoff =>
        hfr1 a ha (by rcases hoff with h | h <;> [left; right] <;> omega)
      have hblk1 : SelBlocksDataAt mem1 B P { D with Gd := Gd } pLast :=
        hblk.setLast_below hEndSc (fun a ha hnr => hfr1 a ha (by unfold SelectBlocksLoc.regLast at hnr; omega)) hGd1
      have hFBaseDG1 : DynGraphAt mem1 fBase vcLast ecLast (lastLSFs termBran).F.F :=
        DynGraphAt.of_agree hLSF.2.1 fun a ha1 ha2 =>
          hFr1OffBlocks a (by omega) (hTermOff a (by omega) (by omega)).2
      -- Step 2: load `brBase`, `fBase`, `stDesc`, then copy `F_d` into `B.fPtr B.d`
      have hbr1 : mem1 (termHandle + 1 + termBran) = brBase :=
        hFr1OffBlocks _ hTermSlotOff.1 hTermSlotOff.2
      have hf1 : mem1 (brBase + 1) = fBase :=
        hFr1OffBlocks (brBase + 1) (by omega) (hTermOff (brBase + 1) (by omega) (by omega)).2
      have hst1 : mem1 (brBase + 3) = stDesc :=
        hFr1OffBlocks (brBase + 3) (by omega) (hTermOff (brBase + 3) (by omega) (by omega)).2
      refine runs_seq_assign_flat (v := brBase)
        (by simp [Expr.eval, BinOp.eval, hw1, show termHandle + 1 < 2 ^ w by omega,
          show termHandle + 1 + termBran < 2 ^ w by omega, hbr1]) ?_
      refine runs_seq_assign_flat (v := fBase)
        (by simp [Expr.eval, BinOp.eval, hw1, show brBase + 1 < 2 ^ w by omega, hf1]) ?_
      refine runs_seq_assign_flat (v := stDesc)
        (by simp [Expr.eval, BinOp.eval, show 3 < 2 ^ w by omega, show brBase + 3 < 2 ^ w by omega, hst1]) ?_
      refine runs_seq_call_le hDgCopyF (vs := [B.fPtr B.d, fBase, scratch + 3 * Gd.m])
        (by eval_expr)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro v (rfl|rfl|rfl) <;> omega)
        ⟨B.fPtr B.d, fBase, scratch + 3 * Gd.m, rfl, hw16, by omega, by omega,
          by rcases hTermDisj with h | ⟨h3, _⟩ <;> [left; right] <;> omega,
          hblk1.1 B.d (le_refl _), hFBaseDG1, hFdV, hFdE, hz1, by omega⟩ ?_
      intro sc2 mem2 pos2 hp2
      obtain ⟨hsc2Eq, hFd2, hz2, hfr2⟩ := hp2
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hsc2Eq hfr2
      subst hsc2Eq
      have hFr2OffBlocks : ∀ a < scratch, (a < B.base ∨ B.endAddr ≤ a) → mem2 a = mem a := fun a ha hoff =>
        (hfr2 a (by omega) (by rcases hoff with h | h <;> [left; right] <;> omega)).trans
          (hFr1OffBlocks a ha hoff)
      have hblk2 : SelBlocksDataAt mem2 B P
          { D with Gd := Gd, F := Function.update D.F B.d (lastLSFs termBran).F.F } pLast :=
        hblk1.setF_below (le_refl B.d) (by omega)
          (fun a ha hnr => hfr2 a ha (by unfold SelectBlocksLoc.regF at hnr; omega)) hFd2
      have hGd2 : DynGraphAt mem2 B.lastGPtr B.vCap B.eCap Gd := hblk2.2.2.2.2.1
      have hGd2M : mem2 (B.lastGPtr + 3) = Gd.m := by simpa [dgMOff] using hGd2.2.2.2.2.2.2.1
      refine runs_seq_assign_flat (v := Gd.m)
        (by simp [Expr.eval, BinOp.eval, show 3 < 2 ^ w by omega,
          show B.lastGPtr + 3 < 2 ^ w by omega, hGd2M]) ?_
      -- Step 3: if `Gd.m > 0`, load `numBase`/`denBase` and call `selCoreLenFill`
      by_cases hm0 : Gd.m = 0
      · have hGdEmpty : Gd.E = ∅ := Finset.card_eq_zero.mp hm0
        have hSpEq : scratch + 3 * Gd.m + 3 * (lastLSFs termBran).F.F.m =
            scratch + selectFillLastLevelSpace Gd.m (lastLSFs termBran).F.F.m B.Lk := by
          rw [hSpDef, hm0]; simp
        refine WordRAM.runs_cond_le (v := 0) (by simp [Expr.eval, hm0]) (fun h => absurd rfl h) fun _ =>
          WordRAM.runs_ret_le (v := scratch + selectFillLastLevelSpace Gd.m (lastLSFs termBran).F.F.m B.Lk)
            (by simp [Expr.eval, hSpEq]) ?_ ?_
        · refine ⟨rfl, ?_, hSpEq ▸ hz2, fun a ha hnl hnf _ => ?_⟩
          · have hLenEmpty : SelPartLen mem2 B P B.d Gd.E (fun e => (lastLSFs termBran).wstr e * prevVal e) pLast :=
              ⟨hGdE, fun e he => absurd he (by rw [hGdEmpty]; exact Finset.notMem_empty e)⟩
            exact hblk2.setLen_below (le_refl B.d) (by omega) (fun _ _ _ => rfl) hLenEmpty
          · exact (hfr2 a (by omega) (by unfold SelectBlocksLoc.regF at hnf; omega)).trans
              (hfr1 a ha (by unfold SelectBlocksLoc.regLast at hnl; omega))
        · simp only [selectFillLastLevelCost, dgCopyRefillContract, Expr.size, argsSize, hm0]
          omega
      · -- `Gd.m > 0`, so `Gd.E` is nonempty, bounding `numBase < 2 ^ w` and `denBase < 2 ^ w`
        obtain ⟨e0, he0⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hm0)
        have hNumLt : numBase < 2 ^ w := by have := hNumHi e0 he0; omega
        have hDenLt : denBase < 2 ^ w := by have := hDenHi e0 he0; omega
        obtain ⟨eL, heL_len, _heL_nd, heL_mem, heL_at, _⟩ := hGd2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hPrev2 : ∀ e ∈ eL, ∀ t < B.Lk, mem2 (prevLen + e * B.Lk + t) = mem (prevLen + e * B.Lk + t) := by
          intro e he t ht
          have heCap : e < B.eCap := hGdE e ((heL_mem e).mp he)
          have hmul : e * B.Lk + t < B.eCap * B.Lk := by
            have := Nat.mul_le_mul_right B.Lk (Nat.succ_le_of_lt heCap)
            rw [Nat.succ_mul] at this; omega
          exact (hfr2 _ (by omega) (by omega)).trans (hfr1 _ (by omega) (by omega))
        have hPrevVal2 : EdgeValuesAt mem2 prevLen 4 B.Lk P Gd.E prevVal :=
          EdgeValuesAt.congr hPrevVal fun e he t ht => hPrev2 e ((heL_mem e).mpr he) t ht
        have hStDesc0Off := hTermOff stDesc (by omega) (by omega)
        have hStDesc1Off := hTermOff (stDesc + 1) (by omega) (by omega)
        have hStr2 : StretchValuesAt mem2 stDesc 4 B.Lk P Gd.E (lastLSFs termBran).wstr := by
          intro e he
          obtain ⟨hNV, hDV, hDPos, hRat⟩ := hLSF.2.2.2 e he
          have heqN : ∀ t < B.Lk, mem2 (mem2 stDesc + e * B.Lk + t) = mem (mem stDesc + e * B.Lk + t) := by
            intro t ht
            rw [hFr2OffBlocks stDesc hStDesc0Off.1 hStDesc0Off.2]
            have hLo := hNumLo e he; have hHi := hNumHi e he
            exact hFr2OffBlocks _ (by omega) (hTermOff _ (by omega) (by omega)).2
          have heqD : ∀ t < B.Lk, mem2 (mem2 (stDesc + 1) + e * B.Lk + t) = mem (mem (stDesc + 1) + e * B.Lk + t) := by
            intro t ht
            rw [hFr2OffBlocks (stDesc + 1) hStDesc1Off.1 hStDesc1Off.2]
            have hLo := hDenLo e he; have hHi := hDenHi e he
            exact hFr2OffBlocks _ (by omega) (hTermOff _ (by omega) (by omega)).2
          refine ⟨fun t ht => (heqN t ht) ▸ hNV t ht, fun t ht => (heqD t ht) ▸ hDV t ht, ?_, ?_⟩
          · unfold Num.fixVal; rw [Num.intVal_congr heqD]; exact hDPos
          · unfold Num.fixVal; rw [Num.intVal_congr heqN, Num.intVal_congr heqD]; exact hRat
        have hCLPre : (selCoreLenFillContract w P B.eCap eL).pre
            [prevLen, numBase, denBase, B.lenPtr B.d, dgEListBase B.lastGPtr B.vCap B.eCap,
              eL.length, B.Lk, B.Lk, pLast, scratch + 3 * Gd.m + 3 * (lastLSFs termBran).F.F.m] mem2 := by
          refine ⟨prevLen, numBase, denBase, B.lenPtr B.d, dgEListBase B.lastGPtr B.vCap B.eCap,
            B.Lk, B.Lk, pLast, scratch + 3 * Gd.m + 3 * (lastLSFs termBran).F.F.m, rfl,
            hw16, by omega, by omega, by omega,
            by unfold dgEListBase; omega,
            by rcases hPrevDisj with h | h <;> [left; right] <;> omega,
            Or.inr (by unfold dgEListBase; omega),
            heL_at, fun e he => hGdE e ((heL_mem e).mp he), fun e he => ?_, hz2, by rw [heL_len]; omega⟩
          have heG : e ∈ Gd.E := (heL_mem e).mp he
          have hNLo := hNumLo e heG; have hNHi := hNumHi e heG
          have hDLo := hDenLo e heG; have hDHi := hDenHi e heG
          have hst0 : mem2 stDesc = numBase := hFr2OffBlocks stDesc hStDesc0Off.1 hStDesc0Off.2
          have hst1 : mem2 (stDesc + 1) = denBase := hFr2OffBlocks (stDesc + 1) hStDesc1Off.1 hStDesc1Off.2
          obtain ⟨hNumV, hDenV, hDenPos, hRatio⟩ := hst0 ▸ hst1 ▸ hStr2 e heG
          obtain ⟨hPrevV, hPrevEq⟩ := hPrevVal2 e heG
          obtain ⟨hFitSh, q, hqFit, hqEq⟩ := hLenFit e heG
          have hIntEq : Num.intVal mem2 (prevLen + e * B.Lk) 4 B.Lk =
              Num.intVal mem (prevLen + e * B.Lk) 4 B.Lk :=
            Num.intVal_congr (hPrev2 e he)
          refine ⟨by omega, by omega,
            by rcases hTermDisj with h | ⟨h3, _⟩ <;> [left; right] <;> omega,
            by rcases hTermDisj with h | ⟨h3, _⟩ <;> [left; right] <;> omega,
            hPrevV, hNumV, hDenV, hDenPos, hIntEq ▸ hFitSh, q, hqFit, ?_⟩
          rw [hqEq, selCoreLenVal, hRatio, hPrevEq]
        have hSpEq : scratch + 3 * Gd.m + 3 * (lastLSFs termBran).F.F.m + Gd.m * selCoreLenEdgeSpace B.Lk B.Lk =
            scratch + selectFillLastLevelSpace Gd.m (lastLSFs termBran).F.F.m B.Lk := by
          rw [hSpDef]; omega
        refine WordRAM.runs_cond_le (v := Gd.m) (by simp [Expr.eval]) ?_ (fun h => absurd h hm0)
        intro _
        have hst0M : mem2 stDesc = numBase := hFr2OffBlocks stDesc hStDesc0Off.1 hStDesc0Off.2
        have hst1M : mem2 (stDesc + 1) = denBase := hFr2OffBlocks (stDesc + 1) hStDesc1Off.1 hStDesc1Off.2
        refine runs_seq_assign_flat (v := numBase) (by simp [Expr.eval, hst0M]) ?_
        refine runs_seq_assign_flat (v := denBase)
          (by simp [Expr.eval, BinOp.eval, hw1, hst1M, show stDesc + 1 < 2 ^ w by omega]) ?_
        refine runs_seq_assign_flat (v := dgEListBase B.lastGPtr B.vCap B.eCap)
          (by simp [Expr.eval, BinOp.eval, show 4 < 2 ^ w by omega, show 7 < 2 ^ w by omega,
            show B.lastGPtr + 4 < 2 ^ w by omega, show 7 * B.vCap < 2 ^ w by omega,
            show B.lastGPtr + 4 + 7 * B.vCap < 2 ^ w by omega,
            show B.lastGPtr + 4 + 7 * B.vCap + B.eCap = dgEListBase B.lastGPtr B.vCap B.eCap from rfl,
            show dgEListBase B.lastGPtr B.vCap B.eCap < 2 ^ w by unfold dgEListBase; omega]) ?_
        refine runs_seq_call_le (hCoreLen eL)
          (vs := [prevLen, numBase, denBase, B.lenPtr B.d, dgEListBase B.lastGPtr B.vCap B.eCap,
            eL.length, B.Lk, B.Lk, pLast, scratch + 3 * Gd.m + 3 * (lastLSFs termBran).F.F.m])
          (by simp [evalArgs, Expr.eval, heL_len])
          (by simp only [List.mem_cons, List.not_mem_nil, or_false]
              rintro v (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)
              · omega
              · exact hNumLt
              · exact hDenLt
              · omega
              · unfold dgEListBase; omega
              · omega
              · exact hLkW
              · exact hLkW
              · exact hpLastW
              · omega)
          hCLPre ?_
        intro sc3 mem3 pos3 hp3
        have hp3' := hp3
        obtain ⟨_, _, _, _, _, _, _, _, _, hargs3, hsc3Eq, _, hz3, hfr3, _⟩ := hp3
        simp only [List.cons.injEq] at hargs3
        obtain ⟨rfl, rfl, rfl, rfl, rfl, -, rfl, rfl, rfl, rfl, -⟩ := hargs3
        have hsc3Fin : sc3 = scratch + selectFillLastLevelSpace Gd.m (lastLSFs termBran).F.F.m B.Lk := by
          rw [hsc3Eq, heL_len, hSpEq]
        have hShiftEq : (if B.d < B.d then 0 else pLast) = pLast := by simp
        have hblk3 : SelBlocksDataAt mem3 B P DTarget pLast :=
          selCoreLenFill_setLen (pLast := pLast) (Lw := B.Lk)
            (hShiftEq.symm ▸ hp3') hblk2 (le_refl B.d) (by omega)
            (fun e he => (hPrevVal2 e ((heL_mem e).mp he)).2)
            (fun e he => (hst0M ▸ hst1M ▸ hStr2 e ((heL_mem e).mp he)).2.2.2)
            (fun e he => hGdE e ((heL_mem e).mp he))
            (fun e he => Or.inl ((heL_mem e).mpr he))
            (fun _ _ _ => rfl)
            (fun e he hnot => absurd ((heL_mem e).mpr he) hnot)
        refine WordRAM.runs_ret_le (v := scratch + selectFillLastLevelSpace Gd.m (lastLSFs termBran).F.F.m B.Lk)
          (by simp [Expr.eval, hsc3Fin]) ?_ ?_
        · refine ⟨rfl, hblk3, hsc3Fin ▸ hz3, fun a ha hnl hnf hnlen => ?_⟩
          have h3 := hfr3 a (by omega) (by unfold SelectBlocksLoc.regLen at hnlen; omega)
          have h2 := hfr2 a (by omega) (by unfold SelectBlocksLoc.regF at hnf; omega)
          have h1 := hfr1 a ha (by unfold SelectBlocksLoc.regLast at hnl; omega)
          exact h3.trans (h2.trans h1)
        · simp only [selectFillLastLevelCost, dgCopyRefillContract, selCoreLenFillContract,
            List.getD_cons_zero, List.getD_cons_succ, heL_len, Expr.size, argsSize]
          omega)
  rcases hpost with ⟨rfl, hblkOut, hzOut, hfrOut⟩
  exact ⟨_, cost, out, hrun, rfl, hblkOut, hzOut, hfrOut, hcost⟩

/-- `selectFillLastLevelBody` populates `B.lastGPtr`, `B.fPtr B.d`, and `B.lenPtr B.d`
(at precision `P + pLast`), updating `SelBlocksDataAt` while preserving all other parts and all
memory `< scratch` outside `B.regLast`, `B.regF B.d`, and `B.regLen B.d`. -/
theorem selectFillLastLevel_runs
    {w P pLast dgCopyProc coreLenProc : ℕ}
    {B : SelectBlocksLoc}
    {metaBase termHandle termBran prevLen srcGd srcVCap srcECap vcLast ecLast limit scratch pos : ℕ}
    {solverG : ℕ → ℕ} {D : SelBlocksData} {Gd : MGraph} {lastK : ℕ} {lastLSFs : ℕ → LSF}
    {prevVal : ℕ → ℝ} {mem : ℕ → ℕ} {p : Program} {ω : ℕ → Bool}
    (hw16 : 16 < 2 ^ w) (hpLastW : pLast < 2 ^ w) (hLkW : B.Lk < 2 ^ w)
    (htab : SelectMetaTableAt mem (selectMlocOf B metaBase solverG pLast))
    (hblk : SelBlocksDataAt mem B P D pLast)
    (hMetaLe : metaBase + selectLevelMetaSize B.d ≤ B.base)
    (hEndSc : B.endAddr ≤ scratch)
    (hSrcG : DynGraphAt mem srcGd srcVCap srcECap Gd)
    (hSrcDisj : srcGd + dynGraphSize srcVCap srcECap ≤ B.base ∨ B.endAddr ≤ srcGd)
    (hSrcSc : srcGd + dynGraphSize srcVCap srcECap ≤ scratch)
    (hGdV : ∀ v ∈ Gd.V, v < B.vCap) (hGdE : ∀ e ∈ Gd.E, e < B.eCap)
    (hTermRep : (lastLevelRepresentation vcLast ecLast 4 B.Lk P Gd.E).rep termHandle (lastK, lastLSFs) limit mem)
    (hBranLt : termBran < lastK)
    (hLimitLe : limit ≤ B.base)
    (hFdV : ∀ v ∈ (lastLSFs termBran).F.F.V, v < B.vCap)
    (hFdE : ∀ e ∈ (lastLSFs termBran).F.F.E, e < B.eCap)
    (hPrevLe : prevLen + B.eCap * B.Lk ≤ scratch)
    (hPrevDisj : prevLen + B.eCap * B.Lk ≤ B.lenPtr B.d ∨ B.embPtr B.d ≤ prevLen)
    (hPrevOffF : prevLen + B.eCap * B.Lk ≤ B.fPtr B.d ∨ B.phiPtr B.d ≤ prevLen)
    (hPrevOffLast : prevLen + B.eCap * B.Lk ≤ B.lastGPtr ∨ B.g0Ptr ≤ prevLen)
    (hPrevVal : EdgeValuesAt mem prevLen 4 B.Lk P Gd.E prevVal)
    (hLenFit : ∀ e ∈ Gd.E,
      Num.Fits 4 B.Lk (Num.intVal mem (prevLen + e * B.Lk) 4 B.Lk * (2 : ℤ) ^ pLast) ∧
      ∃ q : ℤ, Num.Fits 4 B.Lk q ∧
        (q : ℝ) / (2 : ℝ) ^ (P + pLast) = (lastLSFs termBran).wstr e * prevVal e)
    (hDgCopyG : MeetsContract w p dgCopyProc
      (dgCopyRefillContract w B.vCap B.eCap srcVCap srcECap D.Gd Gd))
    (hDgCopyF : MeetsContract w p dgCopyProc
      (dgCopyRefillContract w B.vCap B.eCap vcLast ecLast (D.F B.d) (lastLSFs termBran).F.F))
    (hCoreLen : ∀ eL : List ℕ, MeetsContract w p coreLenProc (selCoreLenFillContract w P B.eCap eL))
    (hz : ZeroFrom mem scratch)
    (hroom : scratch + selectFillLastLevelSpace Gd.m (lastLSFs termBran).F.F.m B.Lk < 2 ^ w) :
    ∃ sc3 cost out,
      Runs w p ω (selectFillLastLevelBody dgCopyProc coreLenProc)
        (startState [metaBase, B.d, termHandle, termBran, prevLen, B.Lk, pLast, srcGd, scratch] mem pos)
        (.returned sc3) out cost ∧
      sc3 = scratch + selectFillLastLevelSpace Gd.m (lastLSFs termBran).F.F.m B.Lk ∧
      SelBlocksDataAt out.mem B P
        { D with
          Gd := Gd
          F := Function.update D.F B.d (lastLSFs termBran).F.F
          E := Function.update D.E B.d Gd.E
          len := Function.update D.len B.d (fun e => (lastLSFs termBran).wstr e * prevVal e) } pLast ∧
      ZeroFrom out.mem sc3 ∧
      (∀ a < scratch, ¬ B.regLast a → ¬ B.regF B.d a → ¬ B.regLen B.d a → out.mem a = mem a) ∧
      cost ≤ selectFillLastLevelCost D.Gd.n D.Gd.m (D.F B.d).n (D.F B.d).m
        Gd.n Gd.m (lastLSFs termBran).F.F.n (lastLSFs termBran).F.F.m B.Lk :=
  selectFillLastLevel_runs_disj hw16 hpLastW hLkW htab hblk hMetaLe hEndSc hSrcG hSrcDisj hSrcSc
    hGdV hGdE hTermRep hBranLt (Or.inl hLimitLe) hFdV hFdE hPrevLe hPrevDisj hPrevOffF hPrevOffLast
    hPrevVal hLenFit hDgCopyG hDgCopyF hCoreLen hz hroom

end MinCostFlow.MinRatio
