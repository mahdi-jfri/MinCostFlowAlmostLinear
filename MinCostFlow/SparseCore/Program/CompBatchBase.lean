module

public import MinCostFlow.SparseCore.Program.CompContract
public import MinCostFlow.SparseCore.Program.CompGhostOps
public import MinCostFlow.LSF.Program.LSFModule
import WordRAM.Tactic

/-!
# Batch-Update Primitives and Multi-Branch LSF Dispatcher (`CompBatchBase`)

Provides the building blocks for `op 0` (batch update) of `compLSFDS`:
* `CompLSFRepDirty`: intermediate representation invariant allowing a list `touched` of marked
  components in `touchMark`, coinciding with `CompLSFRepAt` when `touched = []`.
* `compCopySliceStmt` and `compCopySlice_runs`: `O(len + 1)` contiguous slice copy.
* `lsfApplyBatch_single_runs_of_hasAt`: calls `lsfModuleProcs`'s exact `lsfApplyBatchProc` at
  `bLsf + lsfIdxBatch` on a 1-update canonical batch, preserving `SameStaticConcrete` (hence
  `vCap`, `eCap`, `L_w`, and `endAddr`).
* `compDispatchOneProc` and `compDispatchOne_runs`: dispatches a 1-update projected batch across
  all `k` branches of one edgeful component via `bLsfBatch`, then zeroes the scratch buffer via
  `compZeroRangeProc`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

/-! ## 1. Dirty-mark representation invariant -/

/-- Representation invariant identical to `CompLSFRepAt` except that `touchMark[c] = 1` for
`c ∈ touched` and `0` otherwise. For `touched = []` it coincides with `CompLSFRepAt`. -/
def CompLSFRepDirty (W : LSFWindowImpl) (k b : ℕ) (S : CompLSFFamily k) (x : CompLSFMeta k)
    (touched : List ℕ) (mem : ℕ → ℕ) : Prop :=
  ∃ hk : 1 ≤ k, x.h = W.h ∧ x.L_in = W.L_in ∧ x.P_fp = W.P_fp ∧
  1 ≤ x.L_w ∧ 2 ≤ x.h * x.L_w ∧ 1 ≤ x.eCap ∧
  x.numComps ≤ x.vCap ∧ x.numEdgeful ≤ x.m0Total ∧
  compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k ≤ x.endAddr ∧
  compHeaderAt mem b x ∧
  (∃ ℓ₀ : ℕ → ℝ, ∀ j : Fin k,
    CompLSFInv W.C_lsst ℓ₀ (S j) ∧
    (S j).G₀ = (S ⟨0, hk⟩).G₀ ∧
    (S j).G = (S ⟨0, hk⟩).G ∧
    (S j).k = k ∧
    (S j).crossEdges = (S ⟨0, hk⟩).crossEdges ∧
    (S j).insertedGlobal = (S ⟨0, hk⟩).insertedGlobal ∧
    (∀ c : Fin x.numComps, ((S j).compSt (x.compOf c)).G =
      ((S ⟨0, hk⟩).compSt (x.compOf c)).G)) ∧
  let cs0 := S ⟨0, hk⟩
  cs0.G₀.m = x.m0Total ∧
  CompEdgeTrack x.numComps x.vCap x.eCap x.compOf x.edgeC1 x.edgeC2 x.gtVert x.ghVert
    x.gtList x.ghList cs0 ∧
  (∀ c : Fin x.numComps,
    let Gc0 := compGraph cs0.G₀ (x.compOf c)
    mem (compEdgefulBase b x.vCap + c.1) = (if 1 ≤ Gc0.m then 1 else 0) ∧
    mem (compN0Base b x.vCap + c.1) = Gc0.n ∧
    mem (compM0Base b x.vCap + c.1) = Gc0.m ∧
    (1 ≤ Gc0.m → ∃ ec : Fin x.numEdgeful,
      x.edgefulIdx c = ec.1 ∧ mem (compEdgefulIdxBase b x.vCap + c.1) = ec.1 ∧
      x.edgefulComp ec = c)) ∧
  (∀ ec : Fin x.numEdgeful,
    1 ≤ (compGraph cs0.G₀ (x.compOf (x.edgefulComp ec))).m ∧
    x.edgefulIdx (x.edgefulComp ec) = ec.1) ∧
  (∀ c : Fin x.numComps, ∀ v ∈ (cs0.compSt (x.compOf c)).G.V,
    mem (compVCompBase b + v) = c.1) ∧
  (∀ e ∈ cs0.G.E,
    mem (compEdgeC1Base b x.vCap + e) = x.edgeC1 e ∧
    mem (compEdgeC2Base b x.vCap x.eCap + e) = x.edgeC2 e) ∧
  (∀ e < x.eCap,
    mem (compIsCrossBase b x.vCap x.eCap + e) = (if e ∈ cs0.crossEdges then 1 else 0) ∧
    mem (compIsInsBase b x.vCap x.eCap + e) = (if e ∈ cs0.insertedGlobal then 1 else 0)) ∧
  (let gPtr := compGhostBase b x.vCap x.eCap
   (∀ v < x.vCap,
     IsDoublyLinkedList mem (ghostTPrevBase gPtr x.vCap) (ghostTNextBase gPtr x.vCap x.eCap)
       (ghostTHeadBase gPtr + v) x.eCap (x.gtList v) ∧
     mem (ghostTCntBase gPtr x.vCap + v) = (x.gtList v).length ∧
     IsDoublyLinkedList mem (ghostHPrevBase gPtr x.vCap x.eCap) (ghostHNextBase gPtr x.vCap x.eCap)
       (ghostHHeadBase gPtr x.vCap + v) x.eCap (x.ghList v) ∧
     mem (ghostHCntBase gPtr x.vCap + v) = (x.ghList v).length) ∧
   (∀ e ∈ cs0.G.E, e ∈ cs0.crossEdges →
     mem (ghostTVertBase gPtr x.vCap x.eCap + e) = x.gtVert e ∧
     mem (ghostHVertBase gPtr x.vCap x.eCap + e) = x.ghVert e)) ∧
  (∀ c < x.vCap, mem (compTouchMarkBase b x.vCap x.eCap + c) = if c ∈ touched then 1 else 0) ∧
  (mem (compOneLimbBase b x.vCap x.eCap) = 1 ∧
   ∀ i, 1 ≤ i → i < x.L_w → mem (compOneLimbBase b x.vCap x.eCap + i) = 0) ∧
  (∀ (ec : Fin x.numEdgeful) (j : Fin k),
    let hWin := x.winHandle ec j
    let xWin := x.winConc ec j
    mem (compHandlesBase b x.vCap x.eCap x.L_w + (ec.1 * k + j.1)) = hWin ∧
    (LSFRep W.h).rep hWin ((S j).compSt (x.compOf (x.edgefulComp ec))) xWin mem ∧
    xWin.vCap = x.vCap ∧ xWin.eCap = x.eCap ∧ xWin.L_w = x.L_w ∧
    compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k ≤ hWin ∧
    xWin.endAddr hWin ≤ x.endAddr) ∧
  (∀ (ec₁ ec₂ : Fin x.numEdgeful) (j₁ j₂ : Fin k),
    (ec₁ ≠ ec₂ ∨ j₁ ≠ j₂) →
    ∀ a, (LSFRep W.h).foot (x.winHandle ec₁ j₁) (x.winConc ec₁ j₁) a →
      ¬ (LSFRep W.h).foot (x.winHandle ec₂ j₂) (x.winConc ec₂ j₂) a)

lemma compLSFRepDirty_nil_iff {W : LSFWindowImpl} {k b : ℕ} {S : CompLSFFamily k}
    {x : CompLSFMeta k} {mem : ℕ → ℕ} :
    CompLSFRepDirty W k b S x [] mem ↔ CompLSFRepAt W k b S x mem := by
  simp [CompLSFRepDirty, CompLSFRepAt]

lemma compPhi_eq_sum_dirty {W : LSFWindowImpl} {k b : ℕ} {S : CompLSFFamily k}
    {x : CompLSFMeta k} {touched : List ℕ} {mem : ℕ → ℕ}
    (hrep : CompLSFRepDirty W k b S x touched mem) :
    compPhi b x mem =
      ∑ ec : Fin x.numEdgeful, ∑ j : Fin k, lsfPhi (x.winHandle ec j) (x.winConc ec j) mem := by
  rcases hrep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hWins, _⟩
  unfold compPhi
  refine Finset.sum_congr rfl fun ec _ => Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨_, _, _, _, _, hge, hle⟩ := hWins ec j
  have hb_le_te : b ≤ compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
    dsimp only [compTablesEnd, compHandlesBase, compStaticSize]; omega
  rw [ite_eq_left ⟨le_trans hb_le_te hge, hle⟩]

/-! ## 2. Contiguous slice copy statement -/

/-- Copy `reg rLen` words from `[reg rSrc, reg rSrc + reg rLen)` to `[reg rDst, reg rDst + reg rLen)`
using scratch registers `rIdx` and `rTmp`. -/
def compCopySliceStmt (rSrc rDst rLen rIdx rTmp : ℕ) : Stmt :=
  .assign rIdx (.const 0) ;;
  .loop (.bin .lt (.reg rIdx) (.reg rLen))
    (.assign rTmp (.load (.bin .add (.reg rSrc) (.reg rIdx))) ;;
     .store (.bin .add (.reg rDst) (.reg rIdx)) (.reg rTmp) ;;
     .assign rIdx (.bin .add (.reg rIdx) (.const 1)))

lemma compCopySliceStmt_noRand (rSrc rDst rLen rIdx rTmp : ℕ) :
    (compCopySliceStmt rSrc rDst rLen rIdx rTmp).NoRand := by
  simp [compCopySliceStmt, Stmt.NoRand]

lemma compCopySlice_runs {w rSrc rDst rLen rIdx rTmp src dst len : ℕ} {p : Program}
    {ω : ℕ → Bool} {st : State}
    (hnd : [rSrc, rDst, rLen, rIdx, rTmp].Nodup)
    (hw16 : 16 ≤ 2 ^ w) (hsrc_w : src + len < 2 ^ w) (hdst_w : dst + len < 2 ^ w)
    (hdisj : src + len ≤ dst ∨ dst + len ≤ src)
    (hrSrc : st.regs rSrc = src) (hrDst : st.regs rDst = dst) (hrLen : st.regs rLen = len) :
    ∃ st' c,
      Runs w p ω (compCopySliceStmt rSrc rDst rLen rIdx rTmp) st .normal st' c ∧
      (∀ r, r ≠ rIdx → r ≠ rTmp → st'.regs r = st.regs r) ∧
      (∀ i < len, st'.mem (dst + i) = st.mem (src + i)) ∧
      (∀ a, a < dst ∨ dst + len ≤ a → st'.mem a = st.mem a) ∧
      c ≤ 25 * len + 10 := by
  have hw0 : (0 : ℕ) < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  rcases hnd with ⟨⟨_, _, hSI, hST⟩, ⟨_, hDI, hDT⟩, ⟨hLI, hLT⟩, ⟨hIT, _⟩⟩
  let st0 : State := { st with regs := Function.update st.regs rIdx 0 }
  have hinit : Runs w p ω (.assign rIdx (.const 0)) st .normal st0 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hw0], rfl, rfl, by simp [Expr.size]⟩
  have hloop : ∀ rem i (s : State), i ≤ len → len - i = rem →
      s.regs rSrc = src → s.regs rDst = dst → s.regs rLen = len → s.regs rIdx = i →
      (∀ r, r ≠ rIdx → r ≠ rTmp → s.regs r = st.regs r) →
      (∀ k < i, s.mem (dst + k) = st.mem (src + k)) →
      (∀ a, a < dst ∨ dst + i ≤ a → s.mem a = st.mem a) →
      ∃ st' c,
        Runs w p ω (.loop (.bin .lt (.reg rIdx) (.reg rLen))
          (.assign rTmp (.load (.bin .add (.reg rSrc) (.reg rIdx))) ;;
           .store (.bin .add (.reg rDst) (.reg rIdx)) (.reg rTmp) ;;
           .assign rIdx (.bin .add (.reg rIdx) (.const 1)))) s .normal st' c ∧
        (∀ r, r ≠ rIdx → r ≠ rTmp → st'.regs r = st.regs r) ∧
        (∀ k < len, st'.mem (dst + k) = st.mem (src + k)) ∧
        (∀ a, a < dst ∨ dst + len ≤ a → st'.mem a = st.mem a) ∧
        c ≤ 25 * rem + 6 := by
    intro rem
    induction rem with
    | zero =>
      intro i s hi hrem hS hD hL hI hregs hcp hfr
      have hieq : i = len := by omega
      subst hieq
      exact ⟨s, 4, runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hI, hL],
        rfl, rfl, by simp [Expr.size]⟩), hregs, hcp, hfr, by omega⟩
    | succ rem ih =>
      intro i s hi hrem hS hD hL hI hregs hcp hfr
      have hilt : i < len := by omega
      have hsrc_eq : s.mem (src + i) = st.mem (src + i) := hfr (src + i) (by omega)
      let s1 : State := { s with regs := Function.update s.regs rTmp (st.mem (src + i)) }
      let s2 : State := { s1 with mem := Function.update s1.mem (dst + i) (st.mem (src + i)) }
      let s3 : State := { s2 with regs := Function.update s2.regs rIdx (i + 1) }
      have hs1 : Runs w p ω (.assign rTmp (.load (.bin .add (.reg rSrc) (.reg rIdx)))) s .normal s1 5 :=
        runs_assign_iff.mpr ⟨st.mem (src + i),
          Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, hS, hI, show src + i < 2 ^ w by omega]) hsrc_eq,
          rfl, rfl, by simp [Expr.size]⟩
      have hs2 : Runs w p ω (.store (.bin .add (.reg rDst) (.reg rIdx)) (.reg rTmp)) s1 .normal s2 5 :=
        runs_store_iff.mpr ⟨dst + i, st.mem (src + i),
          by simp [s1, Expr.eval, BinOp.eval, Function.update_of_ne hDT, Function.update_of_ne hIT,
            hD, hI, show dst + i < 2 ^ w by omega],
          by simp [s1, Expr.eval], rfl, rfl, by simp [Expr.size]⟩
      have hs3 : Runs w p ω (.assign rIdx (.bin .add (.reg rIdx) (.const 1))) s2 .normal s3 4 :=
        runs_assign_iff.mpr ⟨i + 1,
          by simp [s2, s1, Expr.eval, BinOp.eval, Function.update_of_ne hIT, hI, hw1,
            show i + 1 < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
      have hbody : Runs w p ω _ s .normal s3 16 :=
        runs_seq_iff.mpr (Or.inr ⟨s1, 5, 10, hs1, runs_seq_iff.mpr (Or.inr ⟨s2, 5, 4, hs2, hs3, rfl⟩), rfl⟩)
      have hregs3 : ∀ r, r ≠ rIdx → r ≠ rTmp → s3.regs r = st.regs r := fun r h1 h2 => by
        dsimp only [s3, s2, s1]; rw [Function.update_of_ne h1, Function.update_of_ne h2]; exact hregs r h1 h2
      obtain ⟨st', c', hr', hregs', hcp', hfr', hc'⟩ := ih (i + 1) s3 (by omega) (by omega)
        (by rw [hregs3 rSrc hSI hST, hrSrc]) (by rw [hregs3 rDst hDI hDT, hrDst])
        (by rw [hregs3 rLen hLI hLT, hrLen]) (by simp [s3]) hregs3
        (fun k hk => by
          dsimp only [s3, s2, s1]
          by_cases hki : k = i
          · subst hki; exact Function.update_self _ _ _
          · rw [Function.update_of_ne (by omega)]; exact hcp k (by omega))
        (fun a ha => by
          dsimp only [s3, s2, s1]; rw [Function.update_of_ne (by omega)]; exact hfr a (by omega))
      refine ⟨st', 3 + 16 + c' + 1,
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, s3, 16, c',
          by simp [Expr.eval, BinOp.eval, hI, hL, hilt, hw1], by decide, hbody, hr', by simp [Expr.size]⟩)),
        hregs', hcp', hfr', by omega⟩
  obtain ⟨st', c', hr', hregs', hcp', hfr', hc'⟩ := hloop len 0 st0 (Nat.zero_le _) (Nat.sub_zero _)
    (by simp [st0, Function.update_of_ne hSI, hrSrc])
    (by simp [st0, Function.update_of_ne hDI, hrDst])
    (by simp [st0, Function.update_of_ne hLI, hrLen])
    (by simp [st0])
    (fun r h1 _ => by simp [st0, Function.update_of_ne h1])
    (fun _ h => by omega) (fun _ _ => rfl)
  exact ⟨st', 2 + c' + 1, runs_seq_iff.mpr (Or.inr ⟨st0, 2, c', hinit, hr', rfl⟩),
    hregs', hcp', hfr', by omega⟩

/-! ## 3. Exact 1-update call to `lsfModuleProcs`'s `lsfApplyBatchProc` preserving `SameStaticConcrete` -/

/-- Canonical-split side condition matching `lsfSplitUpdate_runs`. -/
def IsCanonUpd (G : MGraph) : Update → Prop
  | .insert _ _ _ => True
  | .delete _ => True
  | .split v _ St Sh => (∀ e ∈ St, e ∈ G.E ∧ G.tail e = v) ∧ (∀ e ∈ Sh, e ∈ G.E ∧ G.head e = v)

/-- Runs `lsfModuleProcs`'s exact `lsfApplyBatchProc` at `bLsf + lsfIdxBatch` on a 1-update
canonical batch `[u]` at `bufPtr`, returning `SameStaticConcrete x x'` (hence preserving `vCap`,
`eCap`, `L_w`, and `endAddr`), exact `applyLSFUpdate S u`, exact frame, and amortized cost bound. -/
theorem lsfApplyBatch_single_runs_of_hasAt {w h bLsf c_AN hWin bufPtr heap len : ℕ}
    {p Q_AN : Program} {K_AN : ℝ} {S : LSFState} {x : LSFConcrete} {u : Update}
    {mem : ℕ → ℕ} (pos : ℕ) (ω : ℕ → Bool)
    (hp : p.HasAt bLsf (lsfModuleProcs Q_AN c_AN K_AN bLsf h))
    (hw16 : 16 ≤ 2 ^ w) (hLw : 1 ≤ x.L_w)
    (hend_ltw : x.endAddr hWin < 2 ^ w) (hheap_ltw : heap < 2 ^ w)
    (hbuf_le : bufPtr + (1 + len) ≤ heap)
    (hdisj : ∀ i < 1 + len, bufPtr + i < hWin ∨ x.endAddr hWin ≤ bufPtr + i)
    (hwords : ∀ i < 1 + len, mem (bufPtr + i) < 2 ^ w)
    (hrep : (LSFRep h).rep hWin S x mem)
    (hnum : mem bufPtr = 1)
    (hUpdAt : UpdateAt mem (bufPtr + 1) S.G u len)
    (hu_valid : S.G.UpdateIsValid u)
    (hu_caps : UpdateWithinCaps x.vCap x.eCap u)
    (hu_can : IsCanonUpd S.G u) :
    ∃ body, p.procs[bLsf + lsfIdxBatch]? = some body ∧
      ∃ st' c x',
        Runs w p ω body (startState [hWin, bufPtr, heap] mem pos) (.returned heap) st' c ∧
        SameStaticConcrete x x' ∧
        (LSFRep h).rep hWin (applyLSFUpdate S u) x' st'.mem ∧
        (∀ a, a < hWin ∨ x.endAddr hWin ≤ a → st'.mem a = mem a) ∧
        c + lsfPhi hWin x' st'.mem ≤
          lsfBatchCostFactor * ((1 + len) * x.L_w + 1) + lsfPhi hWin x mem := by
  have M := lsfModuleHasAt_of_hasAt hp
  have hDg := lsfHasAt_dg M.hShared
  have hOps := dgReloc_hasAt_ops hDg
  have hEdge := dgReloc_hasAt_edge hDg
  have hSplit := dgReloc_hasAt_split hDg
  have hBatch := dgReloc_hasAt_batch hDg
  have gBat : ∀ (i : ℕ) (hi : i < 10), p.procs[lsfBaseBat Q_AN bLsf + i]? =
      some ((lsfProcsBat Q_AN bLsf)[i]'(by rw [lsfProcsBat_length]; exact hi)) :=
    fun i hi => M.hBat.get (by rw [lsfProcsBat_length]; exact hi)
  have hpIns := gBat 7 (by decide)
  have hpDel := gBat 8 (by decide)
  have hpSplit := gBat 9 (by decide)
  have hpAdd := gBat 2 (by decide)
  have hMinUp : ∀ S₀, MeetsContract w p (lsfBaseBat Q_AN bLsf + 0)
      (minEdgeUpContract w S₀ x.vList x.tOrigList) := fun _ => minEdgeUp_meetsContract (gBat 0 (by decide))
  have hDgDelF : ∀ F, MeetsContract w p (lsfBaseDg bLsf + 7 + dgIdxDeleteEdge)
      (dgDeleteEdgeContract w x.vCap (fECap x.eCap x.n0) F) := fun _ => dgDeleteEdge_meetsContract hEdge hOps
  have hDgInsG : ∀ G, MeetsContract w p (lsfBaseDg bLsf + 7 + dgIdxInsertEdge)
      (dgInsertEdgeContract w x.vCap x.eCap G) := fun _ => dgInsertEdge_meetsContract hEdge hOps
  have hDgDelG : ∀ G, MeetsContract w p (lsfBaseDg bLsf + 7 + dgIdxDeleteEdge)
      (dgDeleteEdgeContract w x.vCap x.eCap G) := fun _ => dgDeleteEdge_meetsContract hEdge hOps
  have hBFS : ∀ F, MeetsContract w p (lsfBaseBat Q_AN bLsf + 1) (splitCompBFSContract w F) :=
    fun _ => splitCompBFS_meetsContract (gBat 1 (by decide))
  have hTIns : ∀ G T_cur, MeetsContract w p (lsfBaseBat Q_AN bLsf + 4)
      (lsfTBlockInsertContract w x.vCap x.eCap x.tM G T_cur S.T₀ S.π x.tOrigList) := fun _ _ =>
    lsfTBlockInsert_meetsContract (gBat 4 (by decide)) (fun _ => dgInsertEdge_meetsContract hEdge hOps)
  have hTDel : ∀ G T_cur, MeetsContract w p (lsfBaseBat Q_AN bLsf + 5)
      (lsfTBlockDeleteContract w x.vCap x.eCap x.tM G T_cur S.T₀ S.π x.tOrigList) := fun _ _ =>
    lsfTBlockDelete_meetsContract (gBat 5 (by decide)) (fun _ => dgDeleteEdge_meetsContract hEdge hOps)
  have hSetWstr : MeetsContract w p (lsfBaseBat Q_AN bLsf + 3) (lsfSetWstrOneContract w h) :=
    lsfSetWstrOne_meetsContract (gBat 3 (by decide))
  have hw0 : (0 : ℕ) < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hlen_ge2 : 2 ≤ len := updateAt_len_ge_two hUpdAt
  have hb_ltw : hWin < 2 ^ w := by
    have := lsfHdr_lt_end hWin x.vCap x.eCap x.n0 x.tM x.L_w
    dsimp [LSFConcrete.endAddr] at hend_ltw; omega
  have hbp1_ltw : bufPtr + 1 < 2 ^ w := by omega
  have hlen_ltw : len < 2 ^ w := by omega
  -- Execute the 1-update body: branch on `u`
  let sIns : Stmt :=
    .assign 7 (.load (.bin .add (.reg 5) (.const 1))) ;;
    .assign 8 (.load (.bin .add (.reg 5) (.const 2))) ;;
    .assign 9 (.load (.bin .add (.reg 5) (.const 3))) ;;
    .call 10 (lsfBaseBat Q_AN bLsf + 7) [.reg 0, .reg 7, .reg 8, .reg 9]
  let sDel : Stmt :=
    .assign 7 (.load (.bin .add (.reg 5) (.const 1))) ;;
    .call 10 (lsfBaseBat Q_AN bLsf + 8) [.reg 0, .reg 7]
  let sSp : Stmt := .call 10 (lsfBaseBat Q_AN bLsf + 9) [.reg 0, .reg 5]
  let sCond2 : Stmt := .cond (.bin .eq (.reg 6) (.const 1)) sDel sSp
  let sCond1 : Stmt := .cond (.bin .eq (.reg 6) (.const 0)) sIns sCond2
  let sLoopBody : Stmt :=
    .assign 6 (.load (.reg 5)) ;; sCond1 ;;
    .assign 5 (.bin .add (.reg 5) (.reg 10)) ;;
    .assign 4 (.bin .add (.reg 4) (.const 1))
  have hstep : ∃ st_u c_u x',
      Runs w p ω sLoopBody
        { mem := mem, regs := Function.update (Function.update (Function.update
            (startState [hWin, bufPtr, heap] mem pos).regs 3 1) 4 0) 5 (bufPtr + 1), pos := pos }
        .normal st_u c_u ∧
      st_u.regs 2 = heap ∧ st_u.regs 3 = 1 ∧ st_u.regs 4 = 1 ∧
      SameStaticConcrete x x' ∧
      (LSFRep h).rep hWin (applyLSFUpdate S u) x' st_u.mem ∧
      (∀ a, a < hWin ∨ x.endAddr hWin ≤ a → st_u.mem a = mem a) ∧
      c_u + lsfPhi hWin x' st_u.mem ≤ 3000 * len + 50 * x.L_w + 2500 + lsfPhi hWin x mem := by
    let st0 : State :=
      { mem := mem, regs := Function.update (Function.update (Function.update
          (startState [hWin, bufPtr, heap] mem pos).regs 3 1) 4 0) 5 (bufPtr + 1), pos := pos }
    have hr0 : st0.regs 0 = hWin := by simp [st0, startState]
    have hr2 : st0.regs 2 = heap := by simp [st0, startState]
    have hr3 : st0.regs 3 = 1 := by simp [st0]
    have hr4 : st0.regs 4 = 0 := by simp [st0]
    have hr5 : st0.regs 5 = bufPtr + 1 := by simp [st0]
    cases u with
    | insert e a b =>
      rcases hUpdAt with ⟨rfl, hLA⟩
      have hm0 : mem (bufPtr + 1) = 0 := by simpa using hLA 0 (by simp)
      have hm1 : mem (bufPtr + 1 + 1) = e := by simpa using hLA 1 (by simp)
      have hm2 : mem (bufPtr + 1 + 2) = a := by simpa using hLA 2 (by simp)
      have hm3 : mem (bufPtr + 1 + 3) = b := by simpa using hLA 3 (by simp)
      have he_w : e < 2 ^ w := by rw [← hm1, Nat.add_assoc]; exact hwords 2 (by omega)
      have ha_w : a < 2 ^ w := by rw [← hm2, Nat.add_assoc]; exact hwords 3 (by omega)
      have hb_w : b < 2 ^ w := by rw [← hm3, Nat.add_assoc]; exact hwords 4 (by omega)
      obtain ⟨stI, cI, x', hrI, hsame, hrep', hfr', hcI⟩ :=
        lsfInsertUpdate_runs (ω := ω) (pos := pos) hw16 hend_ltw hrep hu_valid hu_caps
          hpAdd hMinUp hDgDelF hBFS hDgInsG hTIns hSetWstr
      let s1 : State := { st0 with regs := Function.update st0.regs 6 0 }
      let s2 : State := { s1 with regs := Function.update s1.regs 7 e }
      let s3 : State := { s2 with regs := Function.update s2.regs 8 a }
      let s4 : State := { s3 with regs := Function.update s3.regs 9 b }
      let s5 : State := { mem := stI.mem, regs := Function.update s4.regs 10 4, pos := stI.pos }
      let s6 : State := { s5 with regs := Function.update s5.regs 5 (bufPtr + 1 + 4) }
      let s7 : State := { s6 with regs := Function.update s6.regs 4 1 }
      have h1 : Runs w p ω (.assign 6 (.load (.reg 5))) st0 .normal s1 3 :=
        runs_assign_iff.mpr ⟨0, Expr.eval_load_of_eq (by simp [Expr.eval, hr5]) hm0, rfl, rfl, by simp [Expr.size]⟩
      have h2 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 5) (.const 1)))) s1 .normal s2 5 :=
        runs_assign_iff.mpr ⟨e, Expr.eval_load_of_eq (by simp [s1, Expr.eval, BinOp.eval, hr5, hw1, show bufPtr + 1 + 1 < 2 ^ w by omega]) hm1, rfl, rfl, by simp [Expr.size]⟩
      have h3 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 5) (.const 2)))) s2 .normal s3 5 :=
        runs_assign_iff.mpr ⟨a, Expr.eval_load_of_eq (by simp [s2, s1, Expr.eval, BinOp.eval, hr5, hw2, show bufPtr + 1 + 2 < 2 ^ w by omega]) hm2, rfl, rfl, by simp [Expr.size]⟩
      have h4 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 5) (.const 3)))) s3 .normal s4 5 :=
        runs_assign_iff.mpr ⟨b, Expr.eval_load_of_eq (by simp [s3, s2, s1, Expr.eval, BinOp.eval, hr5, hw3, show bufPtr + 1 + 3 < 2 ^ w by omega]) hm3, rfl, rfl, by simp [Expr.size]⟩
      have h5 : Runs w p ω (.call 10 (lsfBaseBat Q_AN bLsf + 7) [.reg 0, .reg 7, .reg 8, .reg 9]) s4 .normal s5 (4 + cI + 1) :=
        runs_call_iff.mpr ⟨[hWin, e, a, b], _, .returned 4, stI, cI,
          by simp [s4, s3, s2, s1, evalArgs, Expr.eval, hr0], hpIns, hrI, rfl, rfl, by simp [argsSize, Expr.size]⟩
      have hthen : Runs w p ω sIns s1 .normal s5 (cI + 23) :=
        runs_seq_iff.mpr (Or.inr ⟨s2, 5, cI + 17, h2,
          runs_seq_iff.mpr (Or.inr ⟨s3, 5, cI + 11, h3,
            runs_seq_iff.mpr (Or.inr ⟨s4, 5, 4 + cI + 1, h4, h5, by omega⟩), by omega⟩), by omega⟩)
      have hcond : Runs w p ω sCond1 s1 .normal s5 (cI + 27) :=
        runs_cond_iff.mpr ⟨1, cI + 23, by simp [s1, Expr.eval, BinOp.eval, hw0, hw1],
          by simpa using hthen, by simp [Expr.size]; omega⟩
      have h6 : Runs w p ω (.assign 5 (.bin .add (.reg 5) (.reg 10))) s5 .normal s6 4 :=
        runs_assign_iff.mpr ⟨bufPtr + 1 + 4,
          by simp [s5, s4, s3, s2, s1, Expr.eval, BinOp.eval, hr5, show bufPtr + 1 + 4 < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
      have h7 : Runs w p ω (.assign 4 (.bin .add (.reg 4) (.const 1))) s6 .normal s7 4 :=
        runs_assign_iff.mpr ⟨1, by simp [s6, s5, s4, s3, s2, s1, Expr.eval, BinOp.eval, hr4, hw1],
          rfl, rfl, by simp [Expr.size]⟩
      refine ⟨s7, cI + 41, x',
        runs_seq_iff.mpr (Or.inr ⟨s1, 3, cI + 37, h1,
          runs_seq_iff.mpr (Or.inr ⟨s5, cI + 27, 9, hcond,
            runs_seq_iff.mpr (Or.inr ⟨s6, 4, 4, h6, h7, by omega⟩), by omega⟩), by omega⟩),
        by simp [s7, s6, s5, s4, s3, s2, s1, hr2], by simp [s7, s6, s5, s4, s3, s2, s1, hr3],
        by simp [s7], hsame, hrep', hfr', by dsimp only [s7, s6, s5]; omega⟩
    | delete e =>
      rcases hUpdAt with ⟨rfl, hLA⟩
      have hm0 : mem (bufPtr + 1) = 1 := by simpa using hLA 0 (by simp)
      have hm1 : mem (bufPtr + 1 + 1) = e := by simpa using hLA 1 (by simp)
      obtain ⟨stD, cD, x', hrD, hsame, hrep', hfr', hcD⟩ :=
        lsfDeleteUpdate_runs (ω := ω) (pos := pos) hw16 hend_ltw hrep hu_valid
          hpAdd hMinUp hDgDelF hBFS hDgDelG hTDel
      let s1 : State := { st0 with regs := Function.update st0.regs 6 1 }
      let s2 : State := { s1 with regs := Function.update s1.regs 7 e }
      let s3 : State := { mem := stD.mem, regs := Function.update s2.regs 10 2, pos := stD.pos }
      let s4 : State := { s3 with regs := Function.update s3.regs 5 (bufPtr + 1 + 2) }
      let s5 : State := { s4 with regs := Function.update s4.regs 4 1 }
      have h1 : Runs w p ω (.assign 6 (.load (.reg 5))) st0 .normal s1 3 :=
        runs_assign_iff.mpr ⟨1, Expr.eval_load_of_eq (by simp [Expr.eval, hr5]) hm0, rfl, rfl, by simp [Expr.size]⟩
      have h2 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 5) (.const 1)))) s1 .normal s2 5 :=
        runs_assign_iff.mpr ⟨e, Expr.eval_load_of_eq (by simp [s1, Expr.eval, BinOp.eval, hr5, hw1, show bufPtr + 1 + 1 < 2 ^ w by omega]) hm1, rfl, rfl, by simp [Expr.size]⟩
      have h3 : Runs w p ω (.call 10 (lsfBaseBat Q_AN bLsf + 8) [.reg 0, .reg 7]) s2 .normal s3 (2 + cD + 1) :=
        runs_call_iff.mpr ⟨[hWin, e], _, .returned 2, stD, cD,
          by simp [s2, s1, evalArgs, Expr.eval, hr0], hpDel, hrD, rfl, rfl, by simp [argsSize, Expr.size]⟩
      have hcond2 : Runs w p ω sCond2 s1 .normal s3 (cD + 13) :=
        runs_cond_iff.mpr ⟨1, cD + 9, by simp [s1, Expr.eval, BinOp.eval, hw1],
          by simpa using (runs_seq_iff.mpr (Or.inr ⟨s2, 5, 2 + cD + 1, h2, h3, by omega⟩) :
            Runs w p ω sDel s1 .normal s3 (cD + 9)), by simp [Expr.size]; omega⟩
      have hcond1 : Runs w p ω sCond1 s1 .normal s3 (cD + 17) :=
        runs_cond_iff.mpr ⟨0, cD + 13, by simp [s1, Expr.eval, BinOp.eval, hw0],
          by simpa using hcond2, by simp [Expr.size]; omega⟩
      have h4 : Runs w p ω (.assign 5 (.bin .add (.reg 5) (.reg 10))) s3 .normal s4 4 :=
        runs_assign_iff.mpr ⟨bufPtr + 1 + 2,
          by simp [s3, s2, s1, Expr.eval, BinOp.eval, hr5, show bufPtr + 1 + 2 < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
      have h5 : Runs w p ω (.assign 4 (.bin .add (.reg 4) (.const 1))) s4 .normal s5 4 :=
        runs_assign_iff.mpr ⟨1, by simp [s4, s3, s2, s1, Expr.eval, BinOp.eval, hr4, hw1],
          rfl, rfl, by simp [Expr.size]⟩
      refine ⟨s5, cD + 31, x',
        runs_seq_iff.mpr (Or.inr ⟨s1, 3, cD + 27, h1,
          runs_seq_iff.mpr (Or.inr ⟨s3, cD + 17, 9, hcond1,
            runs_seq_iff.mpr (Or.inr ⟨s4, 4, 4, h4, h5, by omega⟩), by omega⟩), by omega⟩),
        by simp [s5, s4, s3, s2, s1, hr2], by simp [s5, s4, s3, s2, s1, hr3],
        by simp [s5], hsame, hrep', hfr', by dsimp only [s5, s4, s3]; omega⟩
    | split v v' St Sh =>
      have htag : mem (bufPtr + 1) = 2 ∨ mem (bufPtr + 1) = 3 := by
        rcases hUpdAt with ⟨_, _, _, _, _, _, _, hLA⟩ | ⟨_, _, _, _, _, _, _, hLA⟩
        · left; simpa using hLA 0 (by simp)
        · right; simpa using hLA 0 (by simp)
      have hDgUpdF : ∀ G H, MeetsContract w p (lsfBaseDg bLsf + 12 + dgIdxApplyUpdate)
          (dgApplyUpdateContract w x.vCap (fECap x.eCap x.n0) G H (.split v v' St Sh) len) :=
        fun _ _ => dgApplyUpdate_meetsContract hBatch hEdge hSplit hOps
      have hDgUpdG : ∀ G, MeetsContract w p (lsfBaseDg bLsf + 12 + dgIdxApplyUpdate)
          (dgApplyUpdateContract w x.vCap x.eCap G G (.split v v' St Sh) len) :=
        fun _ => dgApplyUpdate_meetsContract hBatch hEdge hSplit hOps
      have hTSplit : ∀ G T_cur, MeetsContract w p (lsfBaseBat Q_AN bLsf + 6)
          (lsfTBlockSplitContract w x.vCap x.eCap x.tM G T_cur S.T₀ S.π x.tOrigList v v' St Sh len) :=
        fun _ _ => lsfTBlockSplit_meetsContract (gBat 6 (by decide))
          (fun _ => dgAddVertex_meetsContract hOps)
          (fun _ _ _ _ _ => dgMoveSlotLoop_meetsContract hSplit hOps)
      obtain ⟨stS, cS, x', hrS, hsame, hrep', hfr', hcS⟩ :=
        lsfSplitUpdate_runs (ω := ω) (pos := pos) hw16 hend_ltw (by omega)
          (fun i hi => by simpa [Nat.add_assoc] using hdisj (1 + i) (by omega))
          (fun i hi => by simpa [Nat.add_assoc] using hwords (1 + i) (by omega))
          hrep hu_valid hu_caps hu_can.1 hu_can.2 hUpdAt
          hpAdd hMinUp hDgDelF hDgUpdF hDgUpdG hBFS hTSplit
      let tag := mem (bufPtr + 1)
      let s1 : State := { st0 with regs := Function.update st0.regs 6 tag }
      let s2 : State := { mem := stS.mem, regs := Function.update s1.regs 10 len, pos := stS.pos }
      let s3 : State := { s2 with regs := Function.update s2.regs 5 (bufPtr + 1 + len) }
      let s4 : State := { s3 with regs := Function.update s3.regs 4 1 }
      have h1 : Runs w p ω (.assign 6 (.load (.reg 5))) st0 .normal s1 3 :=
        runs_assign_iff.mpr ⟨tag, Expr.eval_load_of_eq (by simp [Expr.eval, hr5]) rfl, rfl, rfl, by simp [Expr.size]⟩
      have h2 : Runs w p ω (.call 10 (lsfBaseBat Q_AN bLsf + 9) [.reg 0, .reg 5]) s1 .normal s2 (2 + cS + 1) :=
        runs_call_iff.mpr ⟨[hWin, bufPtr + 1], _, .returned len, stS, cS,
          by simp [s1, evalArgs, Expr.eval, hr0, hr5], hpSplit, hrS, rfl, rfl, by simp [argsSize, Expr.size]⟩
      have htag0 : tag ≠ 0 := by rcases htag with h | h <;> omega
      have htag1 : tag ≠ 1 := by rcases htag with h | h <;> omega
      have hcond2 : Runs w p ω sCond2 s1 .normal s2 (cS + 7) :=
        runs_cond_iff.mpr ⟨0, 2 + cS + 1, by simp [s1, Expr.eval, BinOp.eval, hw1, htag1],
          by simpa using h2, by simp [Expr.size]; omega⟩
      have hcond1 : Runs w p ω sCond1 s1 .normal s2 (cS + 11) :=
        runs_cond_iff.mpr ⟨0, cS + 7, by simp [s1, Expr.eval, BinOp.eval, hw0, htag0],
          by simpa using hcond2, by simp [Expr.size]; omega⟩
      have h3 : Runs w p ω (.assign 5 (.bin .add (.reg 5) (.reg 10))) s2 .normal s3 4 :=
        runs_assign_iff.mpr ⟨bufPtr + 1 + len,
          by simp [s2, s1, Expr.eval, BinOp.eval, hr5, show bufPtr + 1 + len < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
      have h4 : Runs w p ω (.assign 4 (.bin .add (.reg 4) (.const 1))) s3 .normal s4 4 :=
        runs_assign_iff.mpr ⟨1, by simp [s3, s2, s1, Expr.eval, BinOp.eval, hr4, hw1],
          rfl, rfl, by simp [Expr.size]⟩
      refine ⟨s4, cS + 25, x',
        runs_seq_iff.mpr (Or.inr ⟨s1, 3, cS + 21, h1,
          runs_seq_iff.mpr (Or.inr ⟨s2, cS + 11, 9, hcond1,
            runs_seq_iff.mpr (Or.inr ⟨s3, 4, 4, h3, h4, by omega⟩), by omega⟩), by omega⟩),
        by simp [s4, s3, s2, s1, hr2], by simp [s4, s3, s2, s1, hr3],
        by simp [s4], hsame, hrep', hfr', by dsimp only [s4, s3, s2]; omega⟩
  obtain ⟨st_u, c_u, x', hrun_u, hru2, hru3, hru4, hsame, hrep', hfr', hcu⟩ := hstep
  -- Wrap with 3 prefix assigns + 1-iteration loop + `ret heap`
  let stA := startState [hWin, bufPtr, heap] mem pos
  let st1 : State := { stA with regs := Function.update stA.regs 3 1 }
  let st2 : State := { st1 with regs := Function.update st1.regs 4 0 }
  let st3 : State := { st2 with regs := Function.update st2.regs 5 (bufPtr + 1) }
  have hp1 : Runs w p ω (.assign 3 (.load (.reg 1))) stA .normal st1 3 :=
    runs_assign_iff.mpr ⟨1, Expr.eval_load_of_eq (by simp [stA, Expr.eval, startState]) hnum, rfl, rfl, by simp [Expr.size]⟩
  have hp2 : Runs w p ω (.assign 4 (.const 0)) st1 .normal st2 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hw0], rfl, rfl, by simp [Expr.size]⟩
  have hp3 : Runs w p ω (.assign 5 (.bin .add (.reg 1) (.const 1))) st2 .normal st3 4 :=
    runs_assign_iff.mpr ⟨bufPtr + 1, by simp [st2, st1, stA, Expr.eval, BinOp.eval, startState, hw1, hbp1_ltw],
      rfl, rfl, by simp [Expr.size]⟩
  have hloop_end : Runs w p ω (.loop (.bin .lt (.reg 4) (.reg 3)) sLoopBody) st_u .normal st_u 4 :=
    runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hru3, hru4], rfl, rfl, by simp [Expr.size]⟩)
  have hloop : Runs w p ω (.loop (.bin .lt (.reg 4) (.reg 3)) sLoopBody) st3 .normal st_u (3 + c_u + 4 + 1) :=
    runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st_u, c_u, 4,
      by simp [st3, st2, st1, Expr.eval, BinOp.eval, hw1], by decide, hrun_u, hloop_end, by simp [Expr.size]⟩))
  have hret : Runs w p ω (.ret (.reg 2)) st_u (.returned heap) st_u 2 :=
    runs_ret_iff.mpr ⟨heap, by simp [Expr.eval, hru2], rfl, rfl, by simp [Expr.size]⟩
  have hfull : Runs w p ω (lsfApplyBatchProc (lsfBaseBat Q_AN bLsf + 7)
      (lsfBaseBat Q_AN bLsf + 8) (lsfBaseBat Q_AN bLsf + 9)) stA (.returned heap) st_u (c_u + 23) :=
    runs_seq_iff.mpr (Or.inr ⟨st1, 3, c_u + 19, hp1,
      runs_seq_iff.mpr (Or.inr ⟨st2, 2, c_u + 16, hp2,
        runs_seq_iff.mpr (Or.inr ⟨st3, 4, c_u + 11, hp3,
          runs_seq_iff.mpr (Or.inr ⟨st_u, 3 + c_u + 4 + 1, 2, hloop, hret, by omega⟩), by omega⟩),
        by omega⟩), by omega⟩)
  have hcost_le : 3000 * len + 50 * x.L_w + 2525 ≤ lsfBatchCostFactor * ((1 + len) * x.L_w + 1) := by
    dsimp only [lsfBatchCostFactor]
    have h1 : len ≤ len * x.L_w := Nat.le_mul_of_pos_right len hLw
    have h2 : (1 + len) * x.L_w = x.L_w + len * x.L_w := by ring
    omega
  exact ⟨_, M.hBatch, st_u, c_u + 23, x', hfull, hsame, hrep', hfr', by omega⟩


end

end MinCostFlow.SparseCore.Program
