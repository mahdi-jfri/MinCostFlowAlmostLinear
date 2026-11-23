module

public import MinCostFlow.MinRatio.SelectGraphRefill
public import MinCostFlow.MinRatio.SolverSelectBlocks
public import MinCostFlow.MinRatio.SelectPhiFill
public import MinCostFlow.MinRatio.SelectCoreLenPerEdge
import WordRAM.Tactic

/-!
# Rebuilding level `d`'s select block (`SelectLevelDRebuild`)

Provides the deterministic Word-RAM procedure `selectRebuildLevelDBlocksBody` and its verification
`selectRebuildLevelDBlocks_runs`, shared by `ShiftTerm`, `ShiftDeep`, and `Update` (whenever
`firstReb ≤ d`):

* `selectRebuildLevelDBlocksBody`: given `[root, metaBase, L, scratch]`, reads `F_d` and its
  stretch descriptor from `tok.termHandle + 1 + lastBran`, refills `B.fPtr d` via
  `dgRefillFromDynGraph`, fills `B.phiPtr d` via `selectPhiFill`, and fills `B.lenPtr d` at
  precision `P + pLast` via `selCoreLenFill` (reading `C.chainLen ℓ d` from `B.lenPtr (d - 1)`).
* `selectRebuildLevelDBlocks_runs`: updates `D.F d`, `D.V d`, `D.φ d`, `D.E d`, `D.len d` in
  `SelBlocksDataAt` (preserving all other levels, `SelectMetaTableAt`, `SelectHeapAt`, and the
  solver's foot), establishes `SelectPotInv` on the new `φ`, and bounds scratch and steps by
  `levelDBlocksSpace` and `levelDBlocksCost`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program LastLevelProgram SparseCore.Program

/-! ## Rebuilding level `d`'s select block (`B.fPtr d`, `B.phiPtr d`, `B.lenPtr d`) -/

/-- Scratch space used by `selectRebuildLevelDBlocksBody`. -/
def levelDBlocksSpace (d nF mF mG L : ℕ) : ℕ :=
  3 * mF + selectPhiFillSpace d nF L + mG * selCoreLenEdgeSpace L L

/-- Step cost bound of `selectRebuildLevelDBlocksBody`. -/
def levelDBlocksCost (d nOld mOld nNew mNew mG L : ℕ) : ℕ :=
  dgRefillFromDynGraphCost nOld mOld nNew mNew +
    selectPhiFillCost d nNew L +
    mG * (selCoreLenEdgeCost L L + 40) + 320

/-- Rebuild level `d`'s select block (`B.fPtr d`, `B.phiPtr d`, `B.lenPtr d`) from
`tok.termHandle + 1 + lastBran` (`[root, metaBase, L, scratch] → nextScratch`). -/
def selectRebuildLevelDBlocksBody (refillDGProc phiFillProc coreLenFillProc : ℕ) : Stmt :=
  .assign 4 (.load (.reg 0)) ;;
  .assign 6 (.load (.bin .add (.reg 4) (.const 11))) ;;
  .assign 7 (.load (.bin .add (.bin .add (.reg 4) (.const 18)) (.reg 6))) ;;
  .assign 8 (.load (.bin .add (.bin .add (.bin .add (.reg 4) (.const 18))
    (.bin .add (.reg 6) (.const 1))) (.reg 6))) ;;
  .assign 9 (.load (.bin .add (.bin .add (.reg 7) (.const 1)) (.reg 8))) ;;
  .assign 10 (.load (.bin .add (.reg 9) (.const 1))) ;;
  .assign 11 (.load (.bin .add (.reg 9) (.const 3))) ;;
  .assign 12 (.load (.reg 11)) ;;
  .assign 13 (.load (.bin .add (.reg 11) (.const 1))) ;;
  .assign 14 (.bin .add (.reg 6) (.const 1)) ;;
  .assign 15 (.bin .add (.reg 1) (.const smTableOff)) ;;
  .assign 16 (.load (.bin .add (.reg 15) (.reg 6))) ;;
  .assign 17 (.load (.bin .add (.bin .add (.reg 15) (.reg 14)) (.reg 6))) ;;
  .assign 18 (.load (.bin .add (.bin .add (.reg 15) (.bin .mul (.const 2) (.reg 14))) (.reg 6))) ;;
  .assign 19 (.load (.bin .add (.bin .add (.reg 15) (.bin .mul (.const 4) (.reg 14))) (.reg 6))) ;;
  .assign 20 (.load (.bin .add (.bin .add (.reg 15) (.bin .mul (.const 6) (.reg 14))) (.reg 6))) ;;
  .assign 21 (.load (.bin .add (.bin .add (.reg 15) (.bin .mul (.const 7) (.reg 14))) (.reg 6))) ;;
  .assign 22 (.load (.bin .add (.bin .add (.reg 15) (.bin .mul (.const 4) (.reg 14)))
    (.bin .sub (.reg 6) (.const 1)))) ;;
  .assign 23 (.bin .add (.bin .add (.bin .add (.reg 16) (.const 4))
    (.bin .mul (.const 7) (.reg 17))) (.reg 18)) ;;
  .assign 24 (.load (.bin .add (.reg 16) (.const 3))) ;;
  .call 25 refillDGProc [.reg 20, .reg 10, .reg 3] ;;
  .call 26 phiFillProc [.reg 1, .reg 6, .reg 2, .reg 25] ;;
  .call 27 coreLenFillProc
    [.reg 22, .reg 12, .reg 13, .reg 19, .reg 23, .reg 24, .reg 2, .reg 2, .reg 21, .reg 26] ;;
  .ret (.reg 27)

theorem selectRebuildLevelDBlocksBody_noRand (refillDGProc phiFillProc coreLenFillProc : ℕ) :
    (selectRebuildLevelDBlocksBody refillDGProc phiFillProc coreLenFillProc).NoRand := by
  simp [selectRebuildLevelDBlocksBody, Stmt.NoRand]

/-- Helper: updating `φ` at level `d` in `SelBlocksDataAt` from `selectPhiFillContract.post`
when `B.endAddr ≤ scratch`. -/
theorem selPhiFill_setPhi_below {w P j pLast scratch ret : ℕ} {B : SelectBlocksLoc}
    {mloc : SelectLevelMetaLoc} {C : TreeChain} {G : MGraph} {g ℓ : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ} {φ : ℕ → ℕ → ℝ} {D : SelBlocksData} {mem mem' : ℕ → ℕ}
    (hblk : SelBlocksDataAt mem B P D pLast) (hj : j ≤ B.d) (hBEnd : B.endAddr ≤ scratch)
    (hmlocP : mloc.phiPtr j = B.phiPtr j ∧ mloc.vCap j = B.vCap ∧ mloc.Lk = B.Lk)
    (hVcap : ∀ v ∈ (C.G j).V, v < B.vCap)
    (hpost : (selectPhiFillContract w 4 P mloc C G g ℓ σ σ_mwu γ_ℓ γ_c φ).post
      [mloc.metaBase, j, mloc.Lk, scratch] mem ret mem') :
    ∃ φj : ℕ → ℝ,
      SelBlocksDataAt mem' B P
        { D with V := Function.update D.V j (C.G j).V, φ := Function.update D.φ j φj } pLast ∧
      SelectPotInvAt C g (Function.update φ j φj) j ∧
      (∀ v ∈ (C.activeLSF j).F.F.V, ∃ r ∈ (C.activeLSF j).F.F.V,
        (C.activeLSF j).F.F.Connected v r ∧
        φj v = walkInner (potGrad C g φ j) ((C.activeLSF j).F.F.forestPath v r)) := by
  obtain ⟨_, _, _, hfr, φj, hEV, _, hPot, hWalk⟩ := hpost
  simp only [List.getD_cons_zero, List.getD_cons_succ, hmlocP.1, hmlocP.2.1, hmlocP.2.2] at hfr hEV
  let memMid : ℕ → ℕ := fun a => if a < scratch then mem' a else mem a
  have hEVmid : EdgeValuesAt memMid (B.phiPtr j) 4 B.Lk P (C.G j).V φj := by
    refine EdgeValuesAt.congr hEV fun v hv t ht => ?_
    have hblkEnd := B.blk_le_last hj
    have hEnd := B.blkEnd_eq j; have hPhi := B.phiPtr_eq j
    have hm : v * B.Lk + t < B.vCap * B.Lk := by
      have := Nat.mul_le_mul_right B.Lk (Nat.succ_le_of_lt (hVcap v hv))
      rw [Nat.succ_mul] at this; omega
    have hlt : B.phiPtr j + v * B.Lk + t < scratch := by
      unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr at hBEnd; omega
    simp [memMid, hlt]
  have hmid := selPhiFill_setPhi hblk hj hVcap hEVmid (fun a ha => by
    by_cases hlt : a < scratch
    · simp only [memMid, hlt, ↓reduceIte]; exact hfr a hlt ha
    · simp [memMid, hlt])
  exact ⟨φj, hmid.of_agree fun a _ ha2 => by simp [memMid, lt_of_lt_of_le ha2 hBEnd], hPot, hWalk⟩

private lemma runs_seq_call_direct {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ}
    {args : List Expr} {body s : Stmt} {mem regs : ℕ → ℕ} {pos : ℕ} {vs : List ℕ}
    {ret c k T : ℕ} {stCall : State} {Q : Outcome → State → Prop}
    (hproc : p.procs[f]? = some body)
    (hargs : evalArgs w ⟨mem, regs, pos⟩ args = some vs)
    (hcall : Runs w p ω body (startState vs mem pos) (.returned ret) stCall c)
    (hrest : ∃ o st' c', Runs w p ω s ⟨stCall.mem, Function.update regs r ret, stCall.pos⟩ o st' c' ∧
      Q o st' ∧ (k + argsSize args + c + 2) + c' ≤ T) :
    ∃ o st' cTotal, Runs w p ω (.call r f args ;; s) ⟨mem, regs, pos⟩ o st' cTotal ∧
      Q o st' ∧ k + cTotal ≤ T := by
  obtain ⟨o, st', c', hrun', hq, hc⟩ := hrest
  refine ⟨o, st', (argsSize args + c + 1) + c' + 1,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _,
      runs_call_iff.mpr ⟨vs, body, .returned ret, stCall, c, hargs, hproc, hcall, rfl, rfl, rfl⟩,
      hrun', rfl⟩), hq, by omega⟩

private structure LevelDRegs (R : ℕ → ℕ)
    (root metaBase L scratch handle d termHandle lastBran branHdr newFSrc stDesc numBase denBase
      lastGPtr vCap eCap lenD fD pLast prevLen eListPtr mD : ℕ) : Prop where
  r0 : R 0 = root
  r1 : R 1 = metaBase
  r2 : R 2 = L
  r3 : R 3 = scratch
  r4 : R 4 = handle
  r6 : R 6 = d
  r7 : R 7 = termHandle
  r8 : R 8 = lastBran
  r9 : R 9 = branHdr
  r10 : R 10 = newFSrc
  r11 : R 11 = stDesc
  r12 : R 12 = numBase
  r13 : R 13 = denBase
  r14 : R 14 = d + 1
  r15 : R 15 = metaBase + smTableOff
  r16 : R 16 = lastGPtr
  r17 : R 17 = vCap
  r18 : R 18 = eCap
  r19 : R 19 = lenD
  r20 : R 20 = fD
  r21 : R 21 = pLast
  r22 : R 22 = prevLen
  r23 : R 23 = eListPtr
  r24 : R 24 = mD

private theorem levelD_setup_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {pos k T : ℕ}
    {root metaBase L scratch handle d termHandle lastBran branHdr newFSrc stDesc numBase denBase
      lastGPtr vCap eCap lenD fD pLast prevLen mD : ℕ}
    {Q : Outcome → State → Prop} {rest : Stmt}
    (hw18 : 18 < 2 ^ w) (hdPos : 0 < d)
    (_hrootW : root < 2 ^ w) (hmetaW : metaBase + smTableOff + 7 * (d + 1) + d < 2 ^ w)
    (hhandleW : handle + 18 + (d + 1) + d < 2 ^ w)
    (htermW : termHandle + 1 + lastBran < 2 ^ w) (hbranW : branHdr + 3 < 2 ^ w)
    (hstW : stDesc + 1 < 2 ^ w) (hlastW : lastGPtr + 4 + 7 * vCap + eCap < 2 ^ w)
    (h0 : mem root = handle) (h1 : mem (handle + 11) = d)
    (h2 : mem (handle + 18 + d) = termHandle)
    (h3 : mem (handle + 18 + (d + 1) + d) = lastBran)
    (h4 : mem (termHandle + 1 + lastBran) = branHdr)
    (h5 : mem (branHdr + 1) = newFSrc) (h6 : mem (branHdr + 3) = stDesc)
    (h7 : mem stDesc = numBase) (h8 : mem (stDesc + 1) = denBase)
    (h9 : mem (metaBase + smTableOff + d) = lastGPtr)
    (h10 : mem (metaBase + smTableOff + (d + 1) + d) = vCap)
    (h11 : mem (metaBase + smTableOff + 2 * (d + 1) + d) = eCap)
    (h12 : mem (metaBase + smTableOff + 4 * (d + 1) + d) = lenD)
    (h13 : mem (metaBase + smTableOff + 6 * (d + 1) + d) = fD)
    (h14 : mem (metaBase + smTableOff + 7 * (d + 1) + d) = pLast)
    (h15 : mem (metaBase + smTableOff + 4 * (d + 1) + (d - 1)) = prevLen)
    (h16 : mem (lastGPtr + 3) = mD)
    (hrest : ∀ R2 : ℕ → ℕ,
      LevelDRegs R2 root metaBase L scratch handle d termHandle lastBran branHdr newFSrc stDesc
        numBase denBase lastGPtr vCap eCap lenD fD pLast prevLen
        (dgEListBase lastGPtr vCap eCap) mD →
      ∃ o st' c', Runs w p ω rest ⟨mem, R2, pos⟩ o st' c' ∧ Q o st' ∧ (k + 180) + c' ≤ T) :
    ∃ o st' c', Runs w p ω
      (.assign 4 (.load (.reg 0)) ;;
       .assign 6 (.load (.bin .add (.reg 4) (.const 11))) ;;
       .assign 7 (.load (.bin .add (.bin .add (.reg 4) (.const 18)) (.reg 6))) ;;
       .assign 8 (.load (.bin .add (.bin .add (.bin .add (.reg 4) (.const 18))
         (.bin .add (.reg 6) (.const 1))) (.reg 6))) ;;
       .assign 9 (.load (.bin .add (.bin .add (.reg 7) (.const 1)) (.reg 8))) ;;
       .assign 10 (.load (.bin .add (.reg 9) (.const 1))) ;;
       .assign 11 (.load (.bin .add (.reg 9) (.const 3))) ;;
       .assign 12 (.load (.reg 11)) ;;
       .assign 13 (.load (.bin .add (.reg 11) (.const 1))) ;;
       .assign 14 (.bin .add (.reg 6) (.const 1)) ;;
       .assign 15 (.bin .add (.reg 1) (.const smTableOff)) ;;
       .assign 16 (.load (.bin .add (.reg 15) (.reg 6))) ;;
       .assign 17 (.load (.bin .add (.bin .add (.reg 15) (.reg 14)) (.reg 6))) ;;
       .assign 18 (.load (.bin .add (.bin .add (.reg 15) (.bin .mul (.const 2) (.reg 14))) (.reg 6))) ;;
       .assign 19 (.load (.bin .add (.bin .add (.reg 15) (.bin .mul (.const 4) (.reg 14))) (.reg 6))) ;;
       .assign 20 (.load (.bin .add (.bin .add (.reg 15) (.bin .mul (.const 6) (.reg 14))) (.reg 6))) ;;
       .assign 21 (.load (.bin .add (.bin .add (.reg 15) (.bin .mul (.const 7) (.reg 14))) (.reg 6))) ;;
       .assign 22 (.load (.bin .add (.bin .add (.reg 15) (.bin .mul (.const 4) (.reg 14)))
         (.bin .sub (.reg 6) (.const 1)))) ;;
       .assign 23 (.bin .add (.bin .add (.bin .add (.reg 16) (.const 4))
         (.bin .mul (.const 7) (.reg 17))) (.reg 18)) ;;
       .assign 24 (.load (.bin .add (.reg 16) (.const 3))) ;;
       rest) (startState [root, metaBase, L, scratch] mem pos) o st' c' ∧ Q o st' ∧ k + c' ≤ T := by
  dsimp only [startState]
  refine runs_seq_assign_flat (v := handle) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := d) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := termHandle) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := lastBran) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := branHdr) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := newFSrc) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := stDesc) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := numBase) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := denBase) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := d + 1) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := metaBase + smTableOff) (by unfold smTableOff at *; eval_expr) ?_
  refine runs_seq_assign_flat (v := lastGPtr) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := vCap) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := eCap) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := lenD) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := fD) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := pLast) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := prevLen) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := dgEListBase lastGPtr vCap eCap) (by unfold dgEListBase; eval_expr) ?_
  refine runs_seq_assign_flat (v := mD) (by eval_expr) ?_
  refine (fun ⟨o, st', c', hrun, hq, hc⟩ =>
    ⟨o, st', c', hrun, hq, by simp only [Expr.size] at *; omega⟩) (hrest _
      ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
        by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
        by simp, by simp, by simp, by simp⟩)

set_option maxHeartbeats 600000 in
/-- Verification of `selectRebuildLevelDBlocksBody` on a solver state whose `SelBlocksDataAt`
already matches `model` on `G_d`, `g`, and all levels `< d`, with `B.fPtr d` holding `oldF`
and `tok.termHandle` holding `model.chain.lastLSFs`. Updates `B.fPtr d`, `B.phiPtr d`, `B.lenPtr d`
to `model.chain`, preserves all memory outside those three regions and `[scratch, nextScratch)`,
and establishes `SelectBlocksAt` and `SelectPotInv` for `model.chain`! -/
theorem selectRebuildLevelDBlocks_runs
    {w L P m V psi k epsExp drainUnit vCap eCap pLast root scratch pos
      refillDGProc phiFillProc coreLenFillProc coreLenEdgeProc : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {ω : ℕ → Bool}
    {B : SelectBlocksLoc} {loc : SelectHeapLoc} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {mem : ℕ → ℕ} {D : SelBlocksData}
    {G₀ : MGraph} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hpFill : p.procs[coreLenFillProc]? = some (selCoreLenFillBody coreLenEdgeProc))
    (hEdge : MeetsContract w p coreLenEdgeProc (selCoreLenEdgeContract w P))
    (hRefill :
      let newF := (model.chain.lastLSFs model.chain.lastBran).F.F
      MeetsContract w p refillDGProc
        (dgRefillFromDynGraphContract w B.vCap B.eCap tok.vcLast tok.ecLast (D.F cfg.P.d) newF))
    (hPhiFill :
      let mloc := selectMlocOf B loc.metaPtr (solverLevelG tok mem) pLast
      MeetsContract w p phiFillProc
        (selectPhiFillContract w 4 P mloc model.chain.toTreeChain G₀ model.chain.g model.chain.ℓ
          σ σ_mwu γ_ℓ γ_c D.φ))
    (hw16 : 16 < 2 ^ w) (hw10 : 10 ≤ w)
    (hBd : B.d = cfg.P.d) (hBv : B.vCap = vCap) (hBe : B.eCap = eCap) (hBLk : B.Lk = L)
    (hreg : SelectRegion loc.hb loc B loc.metaPtr)
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hcaps : SolverLevelCapsInv P V vCap eCap model tok mem)
    (htab : SelectMetaTableAt mem (selectMlocOf B loc.metaPtr (solverLevelG tok mem) pLast))
    (hD : SelBlocksDataAt mem B P D pLast)
    (hDPre :
      (∀ j < cfg.P.d, D.V j = (model.chain.G j).V ∧ D.E j = (model.chain.G j).E ∧
        D.F j = (model.chain.toTreeChain.activeLSF j).F.F ∧
        D.len j = model.chain.toTreeChain.chainLen model.chain.ℓ (j + 1) ∧
        D.coreE j = (model.chain.toTreeChain.activeCore j).E ∧
        D.emb j = model.chain.toTreeChain.activeEmb j) ∧
      D.Gd = model.chain.G cfg.P.d ∧ D.E0 = (model.chain.G 0).E ∧ D.g = model.chain.g)
    (hPotPre : ∀ j < cfg.P.d, SelectPotInvAt model.chain.toTreeChain model.chain.g D.φ j)
    (hH : model.chain.toTreeChain.Holds G₀ model.chain.ℓ σ σ_mwu γ_ℓ γ_c)
    (hBranLt : model.chain.lastBran < model.chain.lastK)
    (hGdCap : (∀ v ∈ (model.chain.G cfg.P.d).V, v < B.vCap) ∧
      (∀ e ∈ (model.chain.G cfg.P.d).E, e < B.eCap))
    (hFitsE : ∀ e ∈ (model.chain.lastLSFs model.chain.lastBran).F.F.E,
      PotGradEvalFits 4 L P model.chain.toTreeChain model.chain.g D.φ cfg.P.d e)
    (hFitsW : ForestWalkFits 4 L P (model.chain.lastLSFs model.chain.lastBran).F.F
      (potGrad model.chain.toTreeChain model.chain.g D.φ cfg.P.d))
    (hLenFits : ∀ e ∈ (model.chain.G cfg.P.d).E,
      let prev := model.chain.toTreeChain.chainLen model.chain.ℓ cfg.P.d e
      let cur := model.chain.toTreeChain.chainLen model.chain.ℓ (cfg.P.d + 1) e
      (∃ qp : ℤ, Num.Fits 4 L (qp * (2 : ℤ) ^ pLast) ∧ (qp : ℝ) / (2 : ℝ) ^ P = prev) ∧
      (∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ (P + pLast) = cur))
    (hoff : ∀ a, loc.hb ≤ a → a < B.endAddr →
      ¬ (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a)
    (hbelow : ∀ a,
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a ∨
        (loc.hb ≤ a ∧ a < B.endAddr) → a < scratch)
    (hpLastW : pLast < 2 ^ w) (hLW : L < 2 ^ w)
    (hz : ZeroFrom mem scratch)
    (hroom :
      let newF := (model.chain.lastLSFs model.chain.lastBran).F.F
      scratch + levelDBlocksSpace cfg.P.d newF.n newF.m (model.chain.G cfg.P.d).m L < 2 ^ w) :
    let newF := (model.chain.lastLSFs model.chain.lastBran).F.F
    let mloc := selectMlocOf B loc.metaPtr (solverLevelG tok mem) pLast
    ∃ (nextScratch cost : ℕ) (out : State) (φd' : ℕ → ℝ),
      Runs w p ω (selectRebuildLevelDBlocksBody refillDGProc phiFillProc coreLenFillProc)
        (startState [root, loc.metaPtr, L, scratch] mem pos) (.returned nextScratch) out cost ∧
      scratch ≤ nextScratch ∧
      nextScratch ≤ scratch + levelDBlocksSpace cfg.P.d newF.n newF.m (model.chain.G cfg.P.d).m L ∧
      cost ≤ levelDBlocksCost cfg.P.d (D.F cfg.P.d).n (D.F cfg.P.d).m newF.n newF.m
        (model.chain.G cfg.P.d).m L ∧
      SelectMetaTableAt out.mem mloc ∧
      SelectBlocksAt out.mem B P model.chain.toTreeChain model.chain.g model.chain.ℓ
        (Function.update D.φ cfg.P.d φd') pLast ∧
      SelectPotInv model.chain.toTreeChain model.chain.g (Function.update D.φ cfg.P.d φd') ∧
      (∀ v ∈ newF.V, ∃ r ∈ newF.V, newF.Connected v r ∧
        φd' v = walkInner (potGrad model.chain.toTreeChain model.chain.g D.φ cfg.P.d)
          (newF.forestPath v r)) ∧
      ZeroFrom out.mem nextScratch ∧
      (∀ a < scratch, (a < B.fPtr cfg.P.d ∨ B.embPtr cfg.P.d ≤ a) → out.mem a = mem a) := by
  dsimp only
  set d := cfg.P.d
  set C := model.chain.toTreeChain
  set newF := (model.chain.lastLSFs model.chain.lastBran).F.F
  set mloc := selectMlocOf B loc.metaPtr (solverLevelG tok mem) pLast
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  have hC_d : C.d = d := rfl
  have hC_activeD : C.activeLSF d = model.chain.lastLSFs model.chain.lastBran := by
    simp [C, TreeChain.activeLSF, ChainState.toTreeChain, d]
  have hC_activeF : (C.activeLSF d).F.F = newF := by rw [hC_activeD]
  obtain ⟨hlo1, hlo2, hlo3, hlo4⟩ := hreg.bounds
  have hlo3' : loc.metaPtr + selectLevelMetaSize d ≤ B.base := by rw [← hBd]; exact le_of_eq hlo3
  have hEndPos : loc.hb < B.endAddr := by
    have : 0 < selectHeapSize loc.cap loc.d loc.Lk := by unfold selectHeapSize shHdrSize; omega
    rw [loc.endAddr_eq] at hlo2; omega
  have hBEnd : B.endAddr ≤ scratch := by
    have := hbelow (B.endAddr - 1) (Or.inr ⟨by omega, by omega⟩); omega
  have hmetaEnd : loc.metaPtr + selectLevelMetaSize d ≤ B.endAddr := by
    rw [← hBd]; omega
  -- Extract solver header and terminal collection facts from `hrep`
  have hrep0 := hrep
  obtain ⟨hRootDir, _hDetHdr, _hNumHdr, hInitPar, _hFreshInv, _hFreshTab, _hExtLtM,
    _hCapsG0, _hSched, _hOffReady, _hTreeN, _hLct, _hTreeRep, _hAccounts, _hCores,
    hTermPtr, hTermBran, hTermRep, _hWire, hTags⟩ := hrep
  obtain ⟨hOwnTag, hT1, hT2, _hT3, hT4, _hT5, _hT6, _hT7, _hT8, _hT9, _hT10, _hT11, _hT12, _hT13,
    _hT14, _hT15, _hT16, _hT1718, hT19, _hT20, _hT21⟩ := hTags
  have hFootOfTag : ∀ a, tok.tag a ≠ 0 → Rrep.foot root tok a := fun a h => Or.inl (hOwnTag a h)
  have hTagLt : ∀ a, tok.tag a ≠ 0 → a < scratch := fun a h => hbelow a (Or.inl (hFootOfTag a h))
  have hRoot0 : mem root = tok.handle := by simpa using hRootDir 0 (by simp)
  have hRoot1 : mem (root + 1) = tok.table := by simpa using hRootDir 1 (by simp)
  have hHd11 : mem (tok.handle + 11) = d := by
    have := hInitPar 2 (by simp); simpa [Nat.add_assoc] using this
  have hRootW : root + 1 < scratch := hTagLt (root + 1) (by rw [hT1 1 (by omega)]; decide)
  have hHd11W : tok.handle + 11 < scratch := hTagLt (tok.handle + 11) (by rw [hT2 11 (by omega)]; decide)
  have hTPtrW : tok.handle + 18 + d < scratch :=
    hTagLt _ (by rw [hT4 d (by omega)]; decide)
  have hTBranW : tok.handle + 18 + (d + 1) + d < scratch := by
    have h4 := hT4 (2 * d + 1) (by omega)
    have : tok.handle + 18 + (2 * d + 1) = tok.handle + 18 + (d + 1) + d := by omega
    rw [this] at h4
    exact hTagLt _ (by rw [h4]; decide)
  have hTermFoot : ∀ a, tok.termHandle ≤ a → a < tok.termTok → Rrep.foot root tok a :=
    fun a h1 h2 => hFootOfTag a (by rw [hT19 a ⟨h1, h2⟩]; decide)
  have hTermTokLe : tok.termTok ≤ scratch := by
    by_cases hlt : tok.termHandle < tok.termTok
    · have := hbelow (tok.termTok - 1) (Or.inl (hTermFoot _ (by omega) (by omega))); omega
    · have := hTermRep.1; omega
  have hTermDisj : ∀ a, tok.termHandle ≤ a → a < tok.termTok → ¬ (loc.hb ≤ a ∧ a < B.endAddr) :=
    fun a h1 h2 ho => hoff a ho.1 ho.2 (hTermFoot a h1 h2)
  obtain ⟨hBW, hLSF⟩ := hTermRep.2.2.2 model.chain.lastBran hBranLt
  set branHdr := mem (tok.termHandle + 1 + model.chain.lastBran)
  set newFSrc := mem (branHdr + 1)
  set stDesc := mem (branHdr + 3)
  set numBase := mem stDesc
  set denBase := mem (stDesc + 1)
  obtain ⟨hBW_fl, hBW_lim, _, _, hFSrc_lo, hFSrc_hi, _, _, hSt_lo, hSt_hi,
    hNum_lo, hDen_lo, hNum_hi, hDen_hi⟩ := hBW
  have hTermBase : tok.termHandle + 1 + model.chain.lastK ≤ tok.termTok := hTermRep.1
  -- Disjointness between `newFSrc` (`tag 19`) and `B.fPtr d` (`sg.owned`)
  have hFD_in : loc.hb ≤ B.fPtr d ∧ B.fPtr d + dynGraphSize B.vCap B.eCap ≤ B.endAddr := by
    have h1 := B.blk_le_last (show d ≤ B.d by omega)
    have h2 := B.blkEnd_eq d; have h3 := B.phiPtr_eq d
    unfold SelectBlocksLoc.fPtr SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr at *; omega
  have hFD_disj_FSrc : B.fPtr d + dynGraphSize B.vCap B.eCap ≤ newFSrc ∨
      newFSrc + dynGraphSize tok.vcLast tok.ecLast ≤ B.fPtr d := by
    by_contra h; push Not at h
    let a := max (B.fPtr d) newFSrc
    have ha1 : tok.termHandle ≤ a := le_trans (by omega) (le_max_right _ _)
    have ha2 : a < tok.termTok :=
      lt_of_lt_of_le (max_lt h.2 (by unfold dynGraphSize; omega)) hFSrc_hi
    have ha3 : loc.hb ≤ a := le_trans hFD_in.1 (le_max_left _ _)
    have ha4 : a < B.endAddr :=
      lt_of_lt_of_le (max_lt (by unfold dynGraphSize; omega) h.1) hFD_in.2
    exact hTermDisj a ha1 ha2 ⟨ha3, ha4⟩
  -- `newF` vertices and edges are subsets of `G_d` (hence `< B.vCap, B.eCap`)
  have hNewFSub : newF.V ⊆ (model.chain.G d).V ∧ newF.E ⊆ (model.chain.G d).E := by
    have hsub := C.forestsAreSubgraphs_of_holds hH d le_rfl
    rw [hC_activeF] at hsub
    exact ⟨hsub.1, hsub.2.1⟩
  have hNewFV : ∀ v ∈ newF.V, v < B.vCap := fun v hv => hGdCap.1 v (hNewFSub.1 hv)
  have hNewFE : ∀ e ∈ newF.E, e < B.eCap := fun e he => hGdCap.2 e (hNewFSub.2 he)
  -- Metadata table entries at level `d` (and `d - 1` when `d > 0`)
  have hEntD := htab.2.2 d (show d ≤ mloc.d by simp [mloc, selectMlocOf, hBd])
  have hLastG_eq : mem (smEntryAddr loc.metaPtr d 0 d) = B.lastGPtr := by
    simpa [mloc, selectMlocOf, hBd] using hEntD.1
  have hVCap_eq : mem (smEntryAddr loc.metaPtr d 1 d) = B.vCap := by
    simpa [mloc, selectMlocOf, hBd] using hEntD.2.1
  have hECap_eq : mem (smEntryAddr loc.metaPtr d 2 d) = B.eCap := by
    simpa [mloc, selectMlocOf, hBd] using hEntD.2.2.1
  have hLenD_eq : mem (smEntryAddr loc.metaPtr d 4 d) = B.lenPtr d := by
    simpa [mloc, selectMlocOf, hBd] using hEntD.2.2.2.2.1
  have hFD_eq : mem (smEntryAddr loc.metaPtr d 6 d) = B.fPtr d := by
    simpa [mloc, selectMlocOf, hBd] using hEntD.2.2.2.2.2.2.1
  have hPLast_eq : mem (smEntryAddr loc.metaPtr d 7 d) = pLast := by
    simpa [mloc, selectMlocOf, hBd] using hEntD.2.2.2.2.2.2.2
  -- Previous length pointer `B.lenPtr (d - 1)` (`0 < d` from `cfg.P.hd`)
  have hdPos : 0 < d := cfg.P.hd
  have hPrevLen_eq : mem (smEntryAddr loc.metaPtr d 4 (d - 1)) = B.lenPtr (d - 1) := by
    have hEntPrev := htab.2.2 (d - 1) (show d - 1 ≤ mloc.d by simp [mloc, selectMlocOf, hBd])
    simpa [mloc, selectMlocOf, hBd] using hEntPrev.2.2.2.2.1
  have hGdSubPrev : (model.chain.G d).E ⊆ (model.chain.G (d - 1)).E :=
    fun e he => C.G_E_subset_of_le hH (by omega) le_rfl he
  have hPrevLenEV : EdgeValuesAt mem (B.lenPtr (d - 1)) 4 L P (model.chain.G d).E
      (C.chainLen model.chain.ℓ d) := by
    have hDprev := hDPre.1 (d - 1) (by omega)
    have hLP := (hD.2.2.1 (d - 1) (by rw [hBd]; omega)).2
    have hprec : coreLenPrec B.d P pLast (d - 1) = P := by
      unfold coreLenPrec; rw [hBd]; simp [show d - 1 < d by omega]
    rw [hprec, hBLk, hDprev.2.1, hDprev.2.2.2.1, Nat.sub_add_cancel hdPos] at hLP
    exact fun e he => hLP e (hGdSubPrev he)
  -- Live edge list of `G_d` at `B.lastGPtr`
  have hLastG : DynGraphAt mem B.lastGPtr B.vCap B.eCap (model.chain.G d) :=
    hDPre.2.1 ▸ hD.2.2.2.2.1
  obtain ⟨eL, heLen, _, heMem, heAt, _⟩ := hLastG.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLastGM : mem (B.lastGPtr + 3) = (model.chain.G d).m := hLastG.2.2.2.2.2.2.1
  -- Word bounds for register loads
  have hdW : d + 1 < 2 ^ w := by
    have : selectLevelMetaSize d = 2 + 8 * (d + 1) := rfl; omega
  have hMetaEndW : loc.metaPtr + selectLevelMetaSize d < 2 ^ w := by omega
  have hSmW : ∀ blk ≤ 7, ∀ j ≤ d, smEntryAddr loc.metaPtr d blk j < 2 ^ w := fun blk hb j hj => by
    have hm := Nat.mul_le_mul_right (d + 1) hb
    unfold smEntryAddr smTableOff selectLevelMetaSize at *; omega
  have hLastGEnd : B.lastGPtr + dynGraphSize B.vCap B.eCap ≤ B.endAddr := by
    unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr; omega
  have hBlkD : B.fPtr d + B.levelSize ≤ B.lastGPtr := B.blk_le_last (hBd.symm ▸ le_rfl)
  have hBlkDEnd := B.blkEnd_eq d
  have hPhiDEq := B.phiPtr_eq d
  have hLenDEq := B.lenPtr_eq d
  have hEmbDEq := B.embPtr_eq d
  have hPrevBlk : B.fPtr (d - 1) + B.levelSize ≤ B.fPtr d := B.blk_le_of_lt (by omega)
  have hPrevLenEq := B.lenPtr_eq (d - 1)
  have hPrevEmbEq := B.embPtr_eq (d - 1)
  have hPrevEnd := B.blkEnd_eq (d - 1)
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hw6 : 6 < 2 ^ w := by omega
  have hw7 : 7 < 2 ^ w := by omega
  have hw11 : 11 < 2 ^ w := by omega
  have hw18 : 18 < 2 ^ w := by omega
  have hMetaSub : ∀ a, LevelMetaFoot tok a → Rrep.foot root tok a := fun a ha =>
    LevelMetaFoot.mem_foot hrep0 ha
  -- Execute `selectRebuildLevelDBlocksBody`
  have hSpD : levelDBlocksSpace d newF.n newF.m (model.chain.G d).m L =
      3 * newF.m + selectPhiFillSpace d newF.n L +
        (model.chain.G d).m * selCoreLenEdgeSpace L L := rfl
  have hEvalSm : ∀ blk ≤ 7, ∀ j ≤ d,
      loc.metaPtr + smTableOff + (blk * (d + 1) + j) = smEntryAddr loc.metaPtr d blk j :=
    fun _ _ _ _ => by unfold smEntryAddr; omega
  have hRun : ∃ o st' cost,
      Runs w p ω (selectRebuildLevelDBlocksBody refillDGProc phiFillProc coreLenFillProc)
        (startState [root, loc.metaPtr, L, scratch] mem pos) o st' cost ∧
      (∃ nextScratch φd',
        o = .returned nextScratch ∧
        scratch ≤ nextScratch ∧
        nextScratch ≤ scratch + levelDBlocksSpace d newF.n newF.m (model.chain.G d).m L ∧
        SelectMetaTableAt st'.mem mloc ∧
        SelectBlocksAt st'.mem B P C model.chain.g model.chain.ℓ
          (Function.update D.φ d φd') pLast ∧
        SelectPotInv C model.chain.g (Function.update D.φ d φd') ∧
        (∀ v ∈ newF.V, ∃ r ∈ newF.V, newF.Connected v r ∧
          φd' v = walkInner (potGrad C model.chain.g D.φ d) (newF.forestPath v r)) ∧
        ZeroFrom st'.mem nextScratch ∧
        (∀ a < scratch, (a < B.fPtr d ∨ B.embPtr d ≤ a) → st'.mem a = mem a)) ∧
      cost ≤ levelDBlocksCost d (D.F d).n (D.F d).m newF.n newF.m (model.chain.G d).m L := by
    apply runs_start_le
    unfold selectRebuildLevelDBlocksBody
    refine levelD_setup_runs (handle := tok.handle) (d := d) (termHandle := tok.termHandle)
      (lastBran := model.chain.lastBran) (branHdr := branHdr) (newFSrc := newFSrc)
      (stDesc := stDesc) (numBase := numBase) (denBase := denBase)
      (lastGPtr := B.lastGPtr) (vCap := B.vCap) (eCap := B.eCap)
      (lenD := B.lenPtr d) (fD := B.fPtr d) (pLast := pLast) (prevLen := B.lenPtr (d - 1))
      (mD := (model.chain.G d).m)
      (by omega) hdPos (by omega)
      (by unfold smTableOff selectLevelMetaSize at *; omega) (by omega) (by omega) (by omega)
      (by omega) (by unfold dynGraphSize at hLastGEnd; omega)
      hRoot0 hHd11 hTermPtr hTermBran rfl rfl rfl rfl rfl
      (by simpa [smEntryAddr] using hLastG_eq)
      (by simpa [smEntryAddr, Nat.add_assoc] using hVCap_eq)
      (by simpa [smEntryAddr, Nat.add_assoc] using hECap_eq)
      (by simpa [smEntryAddr, Nat.add_assoc] using hLenD_eq)
      (by simpa [smEntryAddr, Nat.add_assoc] using hFD_eq)
      (by simpa [smEntryAddr, Nat.add_assoc] using hPLast_eq)
      (by simpa [smEntryAddr, Nat.add_assoc] using hPrevLen_eq)
      hLastGM ?_
    intro R2 hR2
    -- Step 1: refill `B.fPtr d` from `newFSrc`
    refine runs_seq_call_flat hRefill (vs := [B.fPtr d, newFSrc, scratch])
      (by have := hR2.r20; have := hR2.r10; have := hR2.r3; eval_expr) (by wram_words)
      ⟨B.fPtr d, newFSrc, scratch, rfl, hw16, by omega, by omega, hFD_disj_FSrc,
        hD.1 d (hBd.symm ▸ le_rfl), hLSF.2.1, hNewFV, hNewFE, hz, by omega⟩ ?_
    intro sc1 mem1 pos1 hp1
    have hD1 : SelBlocksDataAt mem1 B P { D with F := Function.update D.F d newF } pLast :=
      dgRefillFromDynGraph_setF hD (hBd.symm ▸ le_rfl) hBEnd ⟨rfl, rfl⟩ hp1
    dsimp only [dgRefillFromDynGraphContract] at hp1
    obtain ⟨dst, src, sc, hEq1, hsc1Eq, hFD1, hz1, hfr1⟩ := hp1
    simp only [List.cons.injEq, and_true] at hEq1
    obtain ⟨hDst, -, hSc⟩ := hEq1
    rw [← hDst] at hFD1 hfr1
    rw [← hSc] at hsc1Eq hfr1
    clear dst src sc hDst hSc
    have hfr1Meta : ∀ a, loc.metaPtr ≤ a → a < loc.metaPtr + selectLevelMetaSize d →
        mem1 a = mem a := fun a h1 h2 =>
      hfr1 a (by omega) (Or.inl (by unfold SelectBlocksLoc.fPtr; omega))
    have htab1 : SelectMetaTableAt mem1 mloc :=
      htab.of_agree fun a h1 h2 => hfr1Meta a h1 (by simpa [mloc, selectMlocOf, hBd] using h2)
    have hcaps1 : SolverLevelCapsInv P V vCap eCap model tok mem1 :=
      hcaps.preserve rfl hcaps.1.2.1
        (fun a ha => ⟨rfl, hfr1 a (hbelow a (Or.inl (hMetaSub a ha))) (by
          by_contra hc; push Not at hc
          exact hoff a (by omega) (by omega) (hMetaSub a ha))⟩)
        (fun j hj => (SolverLevelMetaAt.atCaps hcaps.1 hcaps.2 j hj).2.2.1)
        rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl
    have hG1eq : ∀ j < d, solverLevelG tok mem1 j = solverLevelG tok mem j := fun j hj => by
      unfold solverLevelG
      have htag : tok.tag (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) = 22 + cfg.P.d := by
        have := hcaps.1.2.2.2.2.1 (cfg.P.d + j) (by omega); simpa [Nat.add_assoc] using this
      exact hfr1 _ (hbelow _ (Or.inl (hMetaSub _ (Or.inr (Or.inr (Or.inl htag)))))) (by
        by_contra hc; push Not at hc
        exact hoff _ (by omega) (by omega) (hMetaSub _ (Or.inr (Or.inr (Or.inl htag)))))
    have hmloc1Eq : selectMlocOf B loc.metaPtr (solverLevelG tok mem1) pLast = mloc := by
      unfold mloc selectMlocOf
      congr 1
      · funext j; split_ifs with h
        · exact hG1eq j (hBd ▸ h)
        · rfl
      · funext j; split_ifs with h1 h2
        · exact hG1eq (j + 1) (hBd ▸ h1)
        · rfl
        · rfl
    have hPhiHyps := selectPhiFill_hyps_of_blocks (L := L) (P := P) (V := V) (vCap := vCap)
      (eCap := eCap) (pLast := pLast) (j := d) (hi := sc1) hBd hBv hBe le_rfl hreg
      (hmloc1Eq.symm ▸ htab1) hD1 ⟨hDPre.2.2.1, hDPre.2.2.2⟩ (fun k hk => (hDPre.1 k hk).1)
      hcaps1 hMetaSub hoff (fun a ha => lt_of_lt_of_le (hbelow a ha) (by omega))
    rw [hmloc1Eq] at hPhiHyps
    have hE0Cap : ∀ e ∈ (C.G 0).E, e < mloc.eCap 0 := fun e he => by
      have h0 := (hD1.2.2.2.2.2).1 e (hDPre.2.2.1.symm ▸ he)
      simpa [mloc, selectMlocOf] using h0
    -- Step 2: fill `B.phiPtr d` via `selectPhiFill`
    have hPhiEntD := htab1.2.2 d (hBd.symm ▸ le_rfl)
    refine runs_seq_call_flat hPhiFill (vs := [loc.metaPtr, d, L, sc1])
      (by have := hR2.r1; have := hR2.r6; have := hR2.r2; eval_expr) (by wram_words)
      ⟨d, sc1, by simp [mloc, selectMlocOf, hBLk], hw16, by decide, by omega, hH, le_rfl,
        hE0Cap, hPhiEntD.2.2.2.1, hPhiEntD.2.2.2.2.2.2.1,
        by simpa [mloc, selectMlocOf, hC_activeF] using hFD1,
        hPhiHyps.1, hPhiHyps.2.1, hPhiHyps.2.2,
        by simpa [mloc, selectMlocOf, hBLk, hC_activeF] using hFitsE,
        by simpa [mloc, selectMlocOf, hBLk, hC_activeF] using hFitsW,
        hz1, by simp [mloc, selectMlocOf, hBLk, hC_activeF]; omega⟩ ?_
    intro sc2 mem2 pos2 hp2
    have hPhiPost := hp2
    obtain ⟨φd', hD2, hPotD, hFillD⟩ := selPhiFill_setPhi_below (j := d) (scratch := sc1)
      hD1 (hBd.symm ▸ le_rfl) (by omega)
      ⟨rfl, rfl, hBLk.symm⟩ hGdCap.1 (by simpa [mloc, selectMlocOf, hBLk] using hPhiPost)
    dsimp only [selectPhiFillContract] at hp2
    obtain ⟨hsc2Lo, hsc2Hi, hz2, hfr2, _⟩ := hp2
    simp only [List.getD_cons_zero, List.getD_cons_succ, mloc, selectMlocOf, hBLk, hC_activeF]
      at hsc2Lo hsc2Hi hfr2
    -- Step 3: fill `B.lenPtr d` via `selCoreLenFill_runs_perEdge`
    have hLenDEqL : B.lenPtr d = B.phiPtr d + B.vCap * L := by rw [← hBLk, hLenDEq, hPhiDEq]
    have hEmbDEqL : B.embPtr d = B.lenPtr d + B.eCap * L := by rw [← hBLk, hEmbDEq, hLenDEq]
    have hPrevEmbEqL : B.embPtr (d - 1) = B.lenPtr (d - 1) + B.eCap * L := by
      rw [← hBLk, hPrevEmbEq, hPrevLenEq]
    have hSc2Ge : scratch ≤ sc2 := by omega
    have hSc2End : B.endAddr ≤ sc2 := by omega
    have hNumLo : tok.termHandle ≤ numBase := by change tok.termHandle ≤ mem (mem (branHdr + 3)); omega
    have hDenLo : tok.termHandle ≤ denBase := by change tok.termHandle ≤ mem (mem (branHdr + 3) + 1); omega
    have hNumHi : ∀ e ∈ (model.chain.G d).E, numBase + e * L + L ≤ tok.termTok := hNum_hi
    have hDenHi : ∀ e ∈ (model.chain.G d).E, denBase + e * L + L ≤ tok.termTok := hDen_hi
    have hStLo : tok.termHandle ≤ stDesc := by change tok.termHandle ≤ mem (branHdr + 3); omega
    have hStHi : stDesc + 2 ≤ tok.termTok := hSt_hi
    have heLenCap : eL.length ≤ B.eCap := by
      rw [heLen]; have hsub : (model.chain.G d).E ⊆ Finset.range B.eCap :=
        fun e he => Finset.mem_range.mpr (hGdCap.2 e he)
      simpa [MGraph.m, Finset.card_range] using Finset.card_le_card hsub
    have hDGEnd : dgEListBase B.lastGPtr B.vCap B.eCap + eL.length ≤ B.endAddr := by
      unfold dgEListBase; unfold dynGraphSize at hLastGEnd; omega
    have hDGLo : B.lastGPtr ≤ dgEListBase B.lastGPtr B.vCap B.eCap := by unfold dgEListBase; omega
    have hKeepBefore : ∀ a < scratch, (a < B.fPtr d ∨ B.lenPtr d ≤ a) → mem2 a = mem a :=
      fun a ha hout => by
        rw [hfr2 a (by omega) (by omega), hfr1 a ha (by omega)]
    have htab2 : SelectMetaTableAt mem2 mloc :=
      htab.of_agree fun a h1 h2 => by
        simp only [mloc, selectMlocOf, hBd] at h1 h2
        exact hKeepBefore a (by omega) (Or.inl (by unfold SelectBlocksLoc.fPtr; omega))
    have heAt2 : ListAt mem2 (dgEListBase B.lastGPtr B.vCap B.eCap) eL := fun i hi => by
      rw [hKeepBefore _ (by omega) (Or.inr (by omega))]
      exact heAt i hi
    have hPrevEV2 : EdgeValuesAt mem2 (B.lenPtr (d - 1)) 4 L P (model.chain.G d).E
        (C.chainLen model.chain.ℓ d) := by
      refine EdgeValuesAt.congr hPrevLenEV fun e he t ht => ?_
      have heEnd := ent_end_pe (L := L) (hGdCap.2 e he)
      exact hKeepBefore _ (by omega) (Or.inl (by omega))
    have hKeepTerm : ∀ a, tok.termHandle ≤ a → a < tok.termTok → mem2 a = mem a :=
      fun a h1 h2 => hKeepBefore a (by omega) (by
        by_contra hc; push Not at hc; exact hTermDisj a h1 h2 ⟨by omega, by omega⟩)
    have hNumEq2 : mem2 stDesc = numBase := hKeepTerm stDesc hStLo (by omega)
    have hDenEq2 : mem2 (stDesc + 1) = denBase := hKeepTerm (stDesc + 1) (by omega) (by omega)
    have hStWstr2 : StretchValuesAt mem2 stDesc 4 L P (model.chain.G d).E
        (C.activeLSF d).wstr := by
      rw [hC_activeD]
      have hSt0 : StretchValuesAt mem stDesc 4 L P (model.chain.G d).E
          (model.chain.lastLSFs model.chain.lastBran).wstr := hLSF.2.2.2
      intro e he
      obtain ⟨vn, vd, hdp, hq⟩ := hSt0 e he
      have hne := hNumHi e he; have hde := hDenHi e he
      have hnk : ∀ t < L, mem2 (numBase + e * L + t) = mem (numBase + e * L + t) := fun t ht =>
        hKeepTerm _ (by omega) (by omega)
      have hdk : ∀ t < L, mem2 (denBase + e * L + t) = mem (denBase + e * L + t) := fun t ht =>
        hKeepTerm _ (by omega) (by omega)
      rw [hNumEq2, hDenEq2]
      refine ⟨fun t ht => (hnk t ht) ▸ vn t ht, fun t ht => (hdk t ht) ▸ vd t ht, ?_, ?_⟩
      · unfold Num.fixVal; rw [Num.intVal_congr hdk]; exact hdp
      · unfold Num.fixVal; rw [Num.intVal_congr hnk, Num.intVal_congr hdk]; exact hq
    have hEntryOk : ∀ e ∈ eL, SelCoreLenEntryOk P pLast L L mem2 (B.lenPtr (d - 1))
        numBase denBase e := fun e heL => by
      have heG : e ∈ (model.chain.G d).E := (heMem e).mp heL
      obtain ⟨vp, hfp⟩ := hPrevEV2 e heG
      obtain ⟨vn, vd, hdp, hq⟩ := hStWstr2 e heG
      rw [hNumEq2] at vn hq
      rw [hDenEq2] at vd hdp hq
      obtain ⟨⟨qp, hqpFit, hqpVal⟩, ⟨q, hqFit, hqVal⟩⟩ := hLenFits e heG
      have hIntEq : Num.intVal mem2 (B.lenPtr (d - 1) + e * L) 4 L = qp := by
        have h1 : (Num.intVal mem2 (B.lenPtr (d - 1) + e * L) 4 L : ℝ) / (2 : ℝ) ^ P =
            (qp : ℝ) / (2 : ℝ) ^ P := by
          rw [← Num.fixVal, hfp, hqpVal]
        have h2p : (2 : ℝ) ^ P ≠ 0 := pow_ne_zero P (by norm_num)
        exact_mod_cast (div_left_inj' h2p).mp h1
      refine ⟨vp, vn, vd, hdp, hIntEq ▸ hqpFit, q, hqFit, ?_⟩
      rw [hqVal, selCoreLenVal, hq, hfp]
      rfl
    have hLenDisjTerm : ∀ e ∈ eL,
        (numBase + e * L + L ≤ sc2 ∧
          (numBase + e * L + L ≤ B.lenPtr d ∨ B.lenPtr d + B.eCap * L ≤ numBase + e * L)) ∧
        (denBase + e * L + L ≤ sc2 ∧
          (denBase + e * L + L ≤ B.lenPtr d ∨ B.lenPtr d + B.eCap * L ≤ denBase + e * L)) := by
      intro e heL
      have heG := (heMem e).mp heL
      have hne := hNumHi e heG; have hde := hDenHi e heG
      refine ⟨⟨by omega, ?_⟩, ⟨by omega, ?_⟩⟩
      · by_contra hc; push Not at hc
        by_cases hL0 : L = 0
        · rw [hL0] at hc; omega
        · let a := max (numBase + e * L) (B.lenPtr d)
          exact hTermDisj a (le_trans (by omega) (le_max_left _ _))
            (lt_of_lt_of_le (max_lt (by omega) hc.1) hne)
            ⟨le_trans (by omega) (le_max_right _ _),
              lt_of_lt_of_le (max_lt hc.2 (by
                have := hGdCap.2 e heG
                have : 0 < B.eCap * L := Nat.mul_pos (by omega) (Nat.pos_of_ne_zero hL0)
                omega)) (by omega)⟩
      · by_contra hc; push Not at hc
        by_cases hL0 : L = 0
        · rw [hL0] at hc; omega
        · let a := max (denBase + e * L) (B.lenPtr d)
          exact hTermDisj a (le_trans (by omega) (le_max_left _ _))
            (lt_of_lt_of_le (max_lt (by omega) hc.1) hde)
            ⟨le_trans (by omega) (le_max_right _ _),
              lt_of_lt_of_le (max_lt hc.2 (by
                have := hGdCap.2 e heG
                have : 0 < B.eCap * L := Nat.mul_pos (by omega) (Nat.pos_of_ne_zero hL0)
                omega)) (by omega)⟩
    have hCallFill := selCoreLenFill_runs_perEdge (w := w) (P := P) (eCap := B.eCap)
      (edgeProc := coreLenEdgeProc) (prevBase := B.lenPtr (d - 1))
      (numBase := numBase) (denBase := denBase) (dst := B.lenPtr d)
      (listPtr := dgEListBase B.lastGPtr B.vCap B.eCap) (L := L) (Lw := L)
      (shift := pLast) (heap := sc2) (pos := pos2) (L_list := eL) (p := p) (ω := ω) (mem := mem2)
      hEdge hw16 hLW hLW hpLastW (by unfold dynGraphSize at hLastGEnd; omega) (by omega)
      (by omega) (Or.inr (by omega))
      heAt2 (fun e he => hGdCap.2 e ((heMem e).mp he))
      (fun e he => by
        have heEnd := ent_end_pe (L := L) (hGdCap.2 e ((heMem e).mp he))
        exact ⟨by omega, Or.inl (by omega)⟩)
      (fun e he => (hLenDisjTerm e he).1)
      (fun e he => (hLenDisjTerm e he).2)
      hEntryOk hz2 (by rw [heLen]; omega)
    obtain ⟨out3, c3, hRun3, hc3, hDone3, hz3, hfr3, _⟩ := hCallFill
    have hsc3Eq : sc2 + eL.length * selCoreLenEdgeSpace L L =
        sc2 + (model.chain.G d).m * selCoreLenEdgeSpace L L := by rw [heLen]
    refine runs_seq_call_direct hpFill
      (vs := [B.lenPtr (d - 1), numBase, denBase, B.lenPtr d,
        dgEListBase B.lastGPtr B.vCap B.eCap, (model.chain.G d).m, L, L, pLast, sc2])
      (by have := hR2.r22; have := hR2.r12; have := hR2.r13; have := hR2.r19
          have := hR2.r23; have := hR2.r24; have := hR2.r2; have := hR2.r21; eval_expr)
      (by rw [← heLen]; exact hRun3) ?_
    refine WordRAM.runs_ret_le (v := sc2 + (model.chain.G d).m * selCoreLenEdgeSpace L L)
      (by rw [← hsc3Eq]; eval_expr) ?_ ?_
    · -- Assemble final postcondition
      have hfrAll : ∀ a < scratch, (a < B.fPtr d ∨ B.embPtr d ≤ a) → out3.mem a = mem a :=
        fun a ha hout => by
          rw [hfr3 a (by omega) (by omega),
            hfr2 a (by omega) (by omega), hfr1 a ha (by omega)]
      have htab3 : SelectMetaTableAt out3.mem mloc :=
        htab.of_agree fun a h1 h2 => by
          simp only [mloc, selectMlocOf, hBd] at h1 h2
          exact hfrAll a (by omega) (Or.inl (by unfold SelectBlocksLoc.fPtr; omega))
      have hLenD3 : SelPartLen out3.mem B P d (model.chain.G d).E
          (C.chainLen model.chain.ℓ (d + 1)) pLast := by
        refine ⟨hGdCap.2, fun e he => ?_⟩
        obtain ⟨hv, hf⟩ := hDone3 e ((heMem e).mpr he)
        have hprec : coreLenPrec B.d P pLast d = P + pLast := by
          unfold coreLenPrec; rw [hBd]; simp
        rw [hprec, hBLk]
        refine ⟨hv, hf.trans ?_⟩
        rw [selCoreLenVal]
        obtain ⟨_, _, _, hq⟩ := hStWstr2 e he
        rw [hNumEq2, hDenEq2] at hq
        rw [hq, (hPrevEV2 e he).2]
        rfl
      have hD3 : SelBlocksDataAt out3.mem B P
          { D with
            V := Function.update D.V d (model.chain.G d).V
            E := Function.update D.E d (model.chain.G d).E
            F := Function.update D.F d newF
            φ := Function.update D.φ d φd'
            len := Function.update D.len d (C.chainLen model.chain.ℓ (d + 1)) } pLast := by
        let memMid : ℕ → ℕ := fun a => if a < sc2 then out3.mem a else mem2 a
        have hLenMid : SelPartLen memMid B P d (model.chain.G d).E
            (C.chainLen model.chain.ℓ (d + 1)) pLast := by
          refine hLenD3.of_agree fun a ha => ?_
          have hlt : a < sc2 := by
            unfold SelectBlocksLoc.regLen at ha
            unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr at hBEnd; omega
          simp [memMid, hlt]
        have hmid := hD2.setLen (hBd.symm ▸ le_rfl) (fun a ha => by
          by_cases hlt : a < sc2
          · simp only [memMid, hlt, ↓reduceIte]
            exact hfr3 a hlt (by unfold SelectBlocksLoc.regLen SelectBlocksLoc.embPtr at ha; omega)
          · simp [memMid, hlt]) hLenMid
        exact hmid.of_agree fun a _ ha2 => by
          have hlt : a < sc2 := lt_of_lt_of_le ha2 hSc2End
          simp [memMid, hlt]
      have hBlkFin : SelectBlocksAt out3.mem B P C model.chain.g model.chain.ℓ
          (Function.update D.φ d φd') pLast := by
        rw [selectBlocksAt_iff_data]
        obtain ⟨hF3, hPhi3, hLen3, hEmb3, hLast3, hG03⟩ := hD3
        refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_,
          by simpa [C, ChainState.toTreeChain, SelBlocksData.ofChain, hBd, hDPre.2.1] using hLast3,
          by simpa [C, ChainState.toTreeChain, SelBlocksData.ofChain, hDPre.2.2.1, hDPre.2.2.2] using hG03⟩
        · have hj' : j ≤ d := hBd ▸ hj
          by_cases hjd : j = d
          · subst hjd; simpa [SelBlocksData.ofChain, hC_activeF] using hF3 d hj
          · simpa [SelBlocksData.ofChain, Function.update_of_ne hjd,
              (hDPre.1 j (by omega)).2.2.1] using hF3 j hj
        · have hj' : j ≤ d := hBd ▸ hj
          by_cases hjd : j = d
          · subst hjd; simpa [C, ChainState.toTreeChain, SelBlocksData.ofChain] using hPhi3 d hj
          · simpa [C, ChainState.toTreeChain, SelBlocksData.ofChain, Function.update_of_ne hjd,
              (hDPre.1 j (by omega)).1] using hPhi3 j hj
        · have hj' : j ≤ d := hBd ▸ hj
          by_cases hjd : j = d
          · subst hjd; simpa [C, ChainState.toTreeChain, SelBlocksData.ofChain] using hLen3 d hj
          · simpa [C, ChainState.toTreeChain, SelBlocksData.ofChain, Function.update_of_ne hjd,
              (hDPre.1 j (by omega)).2.1, (hDPre.1 j (by omega)).2.2.2.1] using hLen3 j hj
        · have hj' : j < d := hBd ▸ hj
          simpa [SelBlocksData.ofChain, (hDPre.1 j hj').2.2.2.2.1,
            (hDPre.1 j hj').2.2.2.2.2] using hEmb3 j hj
      exact ⟨sc2 + (model.chain.G d).m * selCoreLenEdgeSpace L L, φd', rfl,
        by omega, by omega, htab3, hBlkFin,
        fun j hj => by
          rw [hC_d] at hj
          by_cases hjd : j = d
          · subst hjd; exact hPotD
          · exact (selectPotInvAt_update_of_lt C model.chain.g D.φ φd' (by omega)).mpr
              (hPotPre j (by omega)),
        by simpa [hC_activeF] using hFillD,
        by rw [← hsc3Eq]; exact hz3, hfrAll⟩
    · simp only [dgRefillFromDynGraphContract, selectPhiFillContract, levelDBlocksCost,
        List.getD_cons_zero, List.getD_cons_succ, hC_activeF, hBLk, mloc, selectMlocOf,
        argsSize, Expr.size]
      rw [heLen] at hc3
      omega
  obtain ⟨o, st', cost, hrun, ⟨nextScratch, φd', rfl, hlo, hhi, htab', hblk', hpot', hfill', hz', hfr'⟩,
    hcost⟩ := hRun
  exact ⟨nextScratch, cost, st', φd', hrun, hlo, hhi, hcost, htab', hblk', hpot', hfill', hz', hfr'⟩

end MinCostFlow.MinRatio
