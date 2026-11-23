module

public import MinCostFlow.MinRatio.UpdateAssemblyPrep
import WordRAM.Tactic

/-!
# Pieces of the `Update` assembly

The good-cycle branch of `solverUpdateBody` (`solverUpdateGoodBranch_runs`), the arithmetic that
adds the costs and spaces of the steps up to `updateSpaceBound` and `updateBudgetBound`, and the
two outcomes of the ordered `Update` model. `solverUpdateBody_runs` in `UpdateAssembly.lean` uses
all of them.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine

/-- Good-cycle branch of `solverUpdateBody` (after `updateCycleLoopBody` sets `foundBit = 1`).
Separated into its own lemma to keep proof terms small and fast to check. -/
theorem solverUpdateGoodBranch_runs
    {w m V psi k epsExp drainUnit
      copyWords subtract goodApply initTree goodNormOut applyPaths applyOffTree
      pathNorm pathFlowTag explicitRouteUpdate offTreePush isNeg maxEdges maxPaths
      root heap descOut zeroBlock etaCopy h0 h5 : ℕ}
    {F : MinRatioFormat w} {cfg : Alg2Config} {G : MGraph}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} (hlocalCore : Rcore.Local)
    {opTree : ℕ → ℕ} {p : Program} {ω : ℕ → Bool} {s12 : State}
    {modelLoop : Alg2State cfg} {tokL : SolverToken cfg F.limbs Rcore}
    {B_bound R_bound B1 R1 request inner norm : ℤ} {edges : List (ℕ × Bool)} {paths : List (ℕ × ℕ)}
    {Δ : ℕ → ℝ}
    (hfmt4 : F.fmt.limbBits = 4)
    (hCopy : MeetsContract w p copyWords (copyWordsContract w))
    (hSub : MeetsContract w p subtract (Num.subtractContract w 4))
    (hGoodApply : p.procs[goodApply]? = some (updateGoodApplyBody goodNormOut applyPaths applyOffTree))
    (hGoodNorm : p.procs[goodNormOut]? = some (updateGoodNormOutBody pathNorm copyWords pathFlowTag))
    (hApplyPaths : p.procs[applyPaths]? = some (updateGoodApplyPathsBody (opTree 2)))
    (hApplyOff : p.procs[applyOffTree]? = some (updateGoodApplyOffTreeBody explicitRouteUpdate offTreePush))
    (hNorm : ∀ req mag, MeetsContract w p pathNorm (pathNormalizationContract w 4 req mag))
    (hTag : ∀ mult, MeetsContract w p pathFlowTag (pathFlowTagContract w 4 mult))
    (hTreeImpl : (LinkCut.PathProg.pathRep 4 F.limbs LinkCut.PathProg.pathC).Implements w p initTree opTree
      (pathTreeMachineContract F.fmt F.limbs LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc F.limbs)))
    (hRoute : ExplicitRouteUpdateSpec w F.limbs p explicitRouteUpdate)
    (hPush : p.procs[offTreePush]? = some (offTreePushBody isNeg))
    (hIsNeg : MeetsContract w p isNeg (Num.isNegativeContract w 4))
    (hBridge : GoodCycleNumericBridge F cfg G m V psi k epsExp drainUnit
      Rcore maxEdges maxPaths B_bound R_bound)
    (hExtEq : modelLoop.extG = G)
    (hFitsLoop : MinRatioStateFits (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)) G 4 F.limbs F.fmt.precision modelLoop)
    (hflowLoop : ∀ e ∈ G.E, |modelLoop.flow e| ≤ (2 : ℝ) ^ F.rangeExponent)
    (hκα : (2 : ℝ) ^ (-(F.rangeExponent : ℤ)) ≤ (1 / (2 : ℝ) ^ k) * cfg.α)
    (hprec : 5 * F.rangeExponent + Nat.size m + 30 ≤ F.fmt.precision)
    (hglBounds : ∀ e ∈ G.E,
      |modelLoop.extg e| ≤ (2 : ℝ) ^ F.rangeExponent ∧
      (2 : ℝ) ^ (-(F.rangeExponent : ℤ)) ≤ modelLoop.extℓ e ∧
      modelLoop.extℓ e ≤ (2 : ℝ) ^ F.rangeExponent)
    (hrepL : (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp drainUnit
      Rcore).rep root modelLoop tokL s12.mem)
    (hnumL : PathTreeNumericInv tokL.tree tokL.trees B1 R1)
    (hoffL : OffTreeRecInv modelLoop F.limbs s12.mem tokL.edgeRecords B1)
    (hB1Le : B1 ≤ B_bound) (hR1Le : R1 ≤ R_bound)
    (hdescL : CycleDescriptorAt modelLoop F.limbs F.fmt.precision s12.mem (s12.mem (descOut + 1)) h5 inner norm edges paths)
    (hedMax : edges.length ≤ maxEdges) (hptMax : paths.length ≤ maxPaths)
    (htagEd : ∀ x < 2 * edges.length, tokL.tag (s12.mem (s12.mem (descOut + 1) + 2) + x) = 0)
    (htagPt : ∀ x < 2 * paths.length, tokL.tag (s12.mem (s12.mem (descOut + 1) + 4) + x) = 0)
    (htag18 : ∀ a, tokL.tag a = 18 → a < s12.mem (descOut + 1))
    (hΔEq : Δ = liftEdgeFn modelLoop.extG modelLoop.extToInt (algorithm1_findCycle modelLoop.chain).1)
    (hΔGood : modelLoop.extG.inner modelLoop.extg Δ / modelLoop.extG.lnorm modelLoop.extℓ Δ ≤
      -((1 / (2 : ℝ) ^ k) * cfg.α))
    (hetaAt : PathIntAt s12.mem etaCopy 4 F.limbs request)
    (hreqLo : (2 : ℝ) ^ (-(F.rangeExponent : ℤ)) ≤ (request : ℝ) / (2 : ℝ) ^ F.fmt.precision)
    (hreqHi : (request : ℝ) / (2 : ℝ) ^ F.fmt.precision ≤ (2 : ℝ) ^ F.rangeExponent)
    (hzeroBlockL : PathIntAt s12.mem zeroBlock 4 F.limbs 0)
    (hzL : ZeroFrom s12.mem h5)
    (hfootRange : ∀ a, (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp drainUnit
      Rcore).foot root tokL a → a < heap ∨ (h0 ≤ a ∧ a < h5))
    (hregs : s12.regs 0 = root ∧ s12.regs 5 = heap ∧ s12.regs 7 = F.limbs ∧
      s12.regs 13 = descOut ∧ s12.regs 15 = zeroBlock ∧ s12.regs 16 = h5 ∧ s12.regs 31 = etaCopy)
    (hlayout : heap + 1 + 2 * F.limbs = descOut ∧ descOut + 2 ≤ zeroBlock ∧
      zeroBlock + F.limbs = etaCopy ∧ etaCopy + F.limbs ≤ h0 ∧ h0 ≤ h5 ∧
      h0 ≤ s12.mem (descOut + 1) ∧ s12.mem (descOut + 1) + 6 ≤ h5)
    (hw15 : 15 < 2 ^ w) (hPW : F.fmt.precision < 2 ^ w)
    (h2nW : 2 * G.n + 1 < 2 ^ w) (hlogW : Nat.log 2 (2 * G.n + 1) ≤ 4 * F.limbs)
    (hsizeM : Nat.size m ≤ F.rangeExponent + 8)
    (hmaxEP : maxEdges + maxPaths < 2 ^ (3 * F.rangeExponent + 20))
    (hcapTreeB : 2 * ((2 * G.n + 1 : ℕ) : ℤ) *
      ((B_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision)) +
        (R_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision))) <
      (Num.capacity 4 F.limbs : ℤ))
    (hcapOffB : B_bound + (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision) <
      (Num.capacity 4 F.limbs : ℤ))
    (hroom : h5 + 2 * F.limbs + goodApplySpace F.limbs maxPaths maxEdges + 2 < 2 ^ w) :
    let L := F.limbs
    let P := F.fmt.precision
    let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
    let mult := pathMultiplier P request (-inner)
    let actual := -(((mult : ℝ) / (2 : ℝ) ^ P) * ((inner : ℝ) / (2 : ℝ) ^ P))
    let inc : ℕ → ℝ := fun e =>
      if e ∈ modelLoop.extG.E then -(actual / modelLoop.extG.inner modelLoop.extg Δ) * Δ e else 0
    let modelEnd : Alg2State cfg :=
      { modelLoop with
        flow := fun e => modelLoop.flow e + inc e
        detectAccum := fun e => modelLoop.detectAccum e + |inc e| }
    let goodBranch : Stmt :=
      .assign 23 (.load (.bin .add (.reg 13) (.const 1))) ;;
      .assign 24 (.load (.reg 23)) ;;
      .assign 25 (.load (.bin .add (.reg 23) (.const 2))) ;;
      .assign 26 (.load (.bin .add (.reg 23) (.const 3))) ;;
      .assign 27 (.load (.bin .add (.reg 23) (.const 4))) ;;
      .assign 28 (.load (.bin .add (.reg 23) (.const 5))) ;;
      .assign 29 (.bin .add (.reg 16) (.reg 7)) ;;
      .call 16 subtract [.reg 15, .reg 24, .reg 7, .reg 16] ;;
      .call 16 goodApply [.reg 0, .reg 31, .reg 29, .reg 25, .reg 26, .reg 27, .reg 28, .reg 5, .reg 16] ;;
      .ret (.reg 16)
    ∃ hEnd cGood out tokEnd,
      Runs w p ω goodBranch s12 (.returned hEnd) out cGood ∧
      out.mem heap = 1 ∧
      ScalarAt out.mem (heap + 1) 4 (2 * L) (2 * P) actual ∧
      NormalizationWithin ((request : ℝ) / (2 : ℝ) ^ P) actual ∧
      MinRatioStateFits (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)) G 4 L P modelEnd ∧
      Rrep.rep root modelEnd tokEnd out.mem ∧
      PreservesLevelMeta tokL tokEnd s12.mem out.mem ∧
      tokEnd.intCap = tokL.intCap ∧
      ZeroFrom out.mem hEnd ∧ h5 + 2 * L ≤ hEnd ∧
      hEnd ≤ h5 + 2 * L + goodApplySpace L maxPaths maxEdges ∧
      (∀ a < h5, (a < heap ∨ heap + 1 + 2 * L ≤ a) → ¬ Rrep.foot root tokL a → out.mem a = s12.mem a) ∧
      (∀ a, Rrep.foot root tokEnd a → Rrep.foot root tokL a ∨ (h5 + 2 * L ≤ a ∧ a < hEnd)) ∧
      cGood + Rrep.phi root tokEnd out.mem ≤
        updateGoodBranchBudget L G.n maxEdges maxPaths drainUnit + Rrep.phi root tokL s12.mem ∧
      ∃ B R : ℤ, PathTreeNumericInv tokEnd.tree tokEnd.trees B R ∧
        B ≤ B_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + P) ∧
        R ≤ R_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + P) ∧
        tokEnd.edgeRecords = tokL.edgeRecords ∧
        ∀ j < tokL.intCap, out.mem (tokL.edgeRecords + j) = s12.mem (tokL.edgeRecords + j) := by
  dsimp only
  let L := F.limbs
  let P := F.fmt.precision
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  have hlocR := solverStateRep_local cfg L P m V psi k epsExp drainUnit hlocalCore
  have hP4 : 4 ∣ P := hfmt4 ▸ F.fmt.precision_aligned
  have hExtN : modelLoop.extG.n = G.n := by rw [hExtEq]
  obtain ⟨hr0, hr5, hr7, hr13, hr15, hr16, hr31⟩ := hregs
  obtain ⟨hl1, hl2, hl3, hl4, hl5, hcurLo, hcurHi⟩ := hlayout
  let curDesc := s12.mem (descOut + 1)
  let innerPtr := s12.mem curDesc
  let edgesBase := s12.mem (curDesc + 2)
  let pathsBase := s12.mem (curDesc + 4)
  have ⟨hedLen, hptLen, h6d, hiLo, _, heLo, hpLo, hiE, _, heE, hpE, _, hinnerAt, _, _, _, hedgesAt, hpathsAt, _⟩ := hdescL
  change curDesc ≤ innerPtr at hiLo
  change curDesc ≤ edgesBase at heLo
  change curDesc ≤ pathsBase at hpLo
  change innerPtr + L ≤ h5 at hiE
  change edgesBase + 2 * edges.length ≤ h5 at heE
  change pathsBase + 2 * paths.length ≤ h5 at hpE
  change ExplicitEdgesAt s12.mem edgesBase edges at hedgesAt
  change PathEndpointsAt s12.mem pathsBase paths at hpathsAt
  obtain ⟨hcapLPos, h2nWL, hlogWL, hmagPos, hfitMag, hstep, hfitMult, hfitAbs,
      hconn, hcapTree, hBend, hRend, hFitsEnd, address, old, haddr, hdisjAddr, hfitOff, haccBridge⟩ :=
    hBridge root etaCopy heap curDesc h5 s12.mem modelLoop tokL B1 R1 request inner norm edges paths
      hfmt4 hExtEq hFitsLoop hflowLoop hκα hprec hglBounds hrepL hnumL hoffL hB1Le hR1Le hdescL
      hedMax hptMax htag18
      (fun a ha => by rcases hfootRange a ha with h | ⟨h1, h2⟩ <;> exact ⟨by omega, by omega⟩)
      (hΔEq ▸ hΔGood) hetaAt hreqLo hreqHi h2nW hlogW hsizeM hmaxEP hcapTreeB hcapOffB
  let magPtr := h5 + L
  let h6 := h5 + 2 * L
  have hLW : L < 2 ^ w := F.parameters_fit.1
  have hh5W : h5 < 2 ^ w := by omega
  have hh6W : h6 < 2 ^ w := by dsimp only [h6, L] at hroom ⊢; omega
  let sG1 : State := { s12 with regs := Function.update s12.regs 23 curDesc }
  let sG2 : State := { sG1 with regs := Function.update sG1.regs 24 innerPtr }
  let sG3 : State := { sG2 with regs := Function.update sG2.regs 25 edgesBase }
  let sG4 : State := { sG3 with regs := Function.update sG3.regs 26 edges.length }
  let sG5 : State := { sG4 with regs := Function.update sG4.regs 27 pathsBase }
  let sG6 : State := { sG5 with regs := Function.update sG5.regs 28 paths.length }
  let sG7 : State := { sG6 with regs := Function.update sG6.regs 29 magPtr }
  have rG1 : Runs w p ω (.assign 23 (.load (.bin .add (.reg 13) (.const 1)))) s12 .normal sG1 5 :=
    runs_assign_iff.mpr ⟨curDesc, by
      simp [Expr.eval, BinOp.eval, hr13, show 1 < 2 ^ w by omega, show descOut + 1 < 2 ^ w by omega, curDesc],
      rfl, rfl, rfl⟩
  have rG2 : Runs w p ω (.assign 24 (.load (.reg 23))) sG1 .normal sG2 3 :=
    runs_assign_iff.mpr ⟨innerPtr, by simp [Expr.eval, sG1, innerPtr], rfl, rfl, rfl⟩
  have rG3 : Runs w p ω (.assign 25 (.load (.bin .add (.reg 23) (.const 2)))) sG2 .normal sG3 5 :=
    runs_assign_iff.mpr ⟨edgesBase, by
      simp [Expr.eval, BinOp.eval, sG2, sG1, show 2 < 2 ^ w by omega, show curDesc + 2 < 2 ^ w by omega, edgesBase],
      rfl, rfl, rfl⟩
  have rG4 : Runs w p ω (.assign 26 (.load (.bin .add (.reg 23) (.const 3)))) sG3 .normal sG4 5 :=
    runs_assign_iff.mpr ⟨edges.length, by
      simp [Expr.eval, BinOp.eval, sG3, sG2, sG1, show 3 < 2 ^ w by omega, show curDesc + 3 < 2 ^ w by omega, curDesc, hedLen],
      rfl, rfl, rfl⟩
  have rG5 : Runs w p ω (.assign 27 (.load (.bin .add (.reg 23) (.const 4)))) sG4 .normal sG5 5 :=
    runs_assign_iff.mpr ⟨pathsBase, by
      simp [Expr.eval, BinOp.eval, sG4, sG3, sG2, sG1, show 4 < 2 ^ w by omega, show curDesc + 4 < 2 ^ w by omega, pathsBase],
      rfl, rfl, rfl⟩
  have rG6 : Runs w p ω (.assign 28 (.load (.bin .add (.reg 23) (.const 5)))) sG5 .normal sG6 5 :=
    runs_assign_iff.mpr ⟨paths.length, by
      simp [Expr.eval, BinOp.eval, sG5, sG4, sG3, sG2, sG1, show 5 < 2 ^ w by omega, show curDesc + 5 < 2 ^ w by omega, curDesc, hptLen],
      rfl, rfl, rfl⟩
  have rG7 : Runs w p ω (.assign 29 (.bin .add (.reg 16) (.reg 7))) sG6 .normal sG7 4 :=
    runs_assign_iff.mpr ⟨magPtr, by
      simp [Expr.eval, BinOp.eval, sG6, sG5, sG4, sG3, sG2, sG1, hr16, hr7,
        show magPtr < 2 ^ w by dsimp only [magPtr, h6] at hh6W ⊢; omega, magPtr, L],
      rfl, rfl, rfl⟩
  -- Call `subtract [zeroBlock, innerPtr, L, h5]`
  obtain ⟨bSub, hbSub, oSub, stSub, cSub, hrSub, ⟨hretSub, _, _, hfrSub, hzSub, ⟨hmagVal, hmagInt⟩⟩, hcSub⟩ :=
    hSub [zeroBlock, innerPtr, L, h5] s12.mem sG7.pos ω
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl <;> (dsimp only [L] at hiE hl3 hl4 ⊢; omega))
      ⟨⟨zeroBlock, innerPtr, L, h5, rfl, by dsimp only [L] at hl3 hl4 ⊢; omega, hiE, hzeroBlockL.1, hinnerAt.1⟩, hzL,
        by change h5 + 2 * L < 2 ^ w; exact hh6W⟩
  change cSub ≤ 74 * L + 42 at hcSub
  change oSub.value = h6 at hretSub
  change ∀ x < h5, stSub.mem x = s12.mem x at hfrSub
  have hzSub' : ZeroFrom stSub.mem h6 := by rw [← hretSub]; exact hzSub
  have hmagAt : PathIntAt stSub.mem magPtr 4 L (-inner) := by
    refine ⟨by simpa [magPtr, heapArg] using hmagVal, ?_⟩
    change Num.intVal stSub.mem (h5 + L) 4 L = -inner
    have h0' : Num.intVal stSub.mem (h5 + L) 4 L =
        Num.wrap 4 L (Num.intVal s12.mem zeroBlock 4 L - Num.intVal s12.mem innerPtr 4 L) := by
      simpa [heapArg] using hmagInt
    rw [h0', hzeroBlockL.2, hinnerAt.2, zero_sub]; exact Num.wrap_of_fits hfitMag
  let sG8 : State := { regs := Function.update sG7.regs 16 h6, mem := stSub.mem, pos := stSub.pos }
  have rCallSub : Runs w p ω (.call 16 subtract [.reg 15, .reg 24, .reg 7, .reg 16]) sG7 .normal sG8 (cSub + 5) :=
    runs_call_iff.mpr ⟨[zeroBlock, innerPtr, L, h5], bSub, oSub, stSub, cSub,
      by simp [evalArgs, Expr.eval, sG7, sG6, sG5, sG4, sG3, sG2, sG1, hr15, hr7, hr16, L],
      hbSub, hrSub, rfl, by simp [sG8, hretSub], by simp [argsSize, Expr.size]; omega⟩
  have hfootL_ltH5 (a : ℕ) (ha : Rrep.foot root tokL a) : a < h5 := by
    rcases hfootRange a ha with hlt | ⟨_, hhi⟩ <;> omega
  have hagLSub (a : ℕ) (ha : Rrep.foot root tokL a) : s12.mem a = stSub.mem a := (hfrSub a (hfootL_ltH5 a ha)).symm
  have hrepSub : Rrep.rep root modelLoop tokL stSub.mem := (hlocR root modelLoop tokL s12.mem stSub.mem hagLSub).1 hrepL
  have hphiSub : Rrep.phi root tokL stSub.mem = Rrep.phi root tokL s12.mem :=
    ((hlocR root modelLoop tokL s12.mem stSub.mem hagLSub).2).symm
  have hbelowSub (a : ℕ) (ha : Rrep.foot root tokL a) : a < h6 ∧ (a < heap ∨ heap + 1 + 2 * L ≤ a) := by
    rcases hfootRange a ha with hlt | ⟨hlo, hhi⟩
    · exact ⟨by dsimp only [h6]; omega, Or.inl hlt⟩
    · exact ⟨by dsimp only [h6]; omega, Or.inr (by dsimp only [L]; omega)⟩
  have hetaAtSub : PathIntAt stSub.mem etaCopy 4 L request := hetaAt.congr fun j hj =>
    hfrSub (etaCopy + j) (by omega)
  have hedgesAtSub : ExplicitEdgesAt stSub.mem edgesBase edges := hedgesAt.congr fun x hx1 hx2 =>
    hfrSub x (by omega)
  have hpathsAtSub : PathEndpointsAt stSub.mem pathsBase paths := fun j hj => by
    rw [hfrSub _ (by omega), hfrSub _ (by omega)]; exact hpathsAt j hj
  have ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, htagsL⟩ := hrepL
  obtain ⟨hOwnL, _, _, _, _, _, _, _, _, _, _, _, _, t13L, _, t15L, _⟩ := htagsL
  have hlt5 {a v : ℕ} (ht : tokL.tag a = v) (hv : v ≠ 0) : a < h5 := hfootL_ltH5 a (Or.inl (hOwnL a (ht ▸ hv)))
  have haddrSub : ∀ ei ∈ edges.map Prod.fst, ei < tokL.intCap ∧
      stSub.mem (tokL.edgeRecords + ei) = address ei ∧
      PathEdgeAt stSub.mem (address ei) 4 L (some (old ei)) ∧
      (∀ x < 2 + 4 * L, tokL.tag (address ei + x) = 18) ∧
      address ei + 2 + 4 * L ≤ edgesBase := fun ei hei => by
    obtain ⟨h1e, h2e, h3e, h4e, h5e⟩ := haddr ei hei
    refine ⟨h1e, (hfrSub _ (hlt5 (t13L ei h1e) (by decide))).trans h2e,
      h3e.congr (fun a ha1 ha2 => by
        have ht18 : tokL.tag a = 18 := by have := h4e (a - address ei) (by omega); rwa [Nat.add_sub_of_le ha1] at this
        exact hfrSub a (hlt5 ht18 (by decide))),
      h4e, h5e⟩
  have hgoodSpLe : goodApplySpace L paths.length edges.length ≤ goodApplySpace L maxPaths maxEdges := by
    unfold goodApplySpace explicitRouteSpace
    have h1 := Nat.mul_le_mul_right (pathApplySpace L) hptMax
    have h2' := Nat.mul_le_mul_right (17 * L + 3) hedMax; omega
  let mult := pathMultiplier P request (-inner)
  let actual := -(((mult : ℝ) / (2 : ℝ) ^ P) * ((inner : ℝ) / (2 : ℝ) ^ P))
  let inc : ℕ → ℝ := fun e =>
    if e ∈ modelLoop.extG.E then -(actual / modelLoop.extG.inner modelLoop.extg Δ) * Δ e else 0
  have haccBridgeSub : ∀ (mem' : ℕ → ℕ) (trees' : List AuxTree) (depth' : ℕ → ℕ),
      let s' := applyPathsFold tokL.tree (PathTag.ofFlow mult) paths
      LctInvWith pathPayload s' trees' tokL.free depth' →
      (∀ ei ∈ edges.map Prod.fst,
        PathEdgeAt mem' (address ei) 4 L (some (updatedOffTreeVal edges old mult ei)) ∧
        (0 ≤ (updatedOffTreeVal edges old mult ei).detector → mem' (tokL.inOffReady + ei) = 1)) →
      (∀ a < h6, (a < heap ∨ heap + 1 + 2 * L ≤ a) →
        (∀ ei ∈ edges.map Prod.fst, a < address ei + 2 + 2 * L ∨ address ei + 2 + 4 * L ≤ a) →
        tokL.tag a ≠ 1 → tokL.tag a ≠ 14 → tokL.tag a ≠ 15 → tokL.tag a ≠ 16 → mem' a = stSub.mem a) →
      (∀ j < tokL.intCap, stSub.mem (tokL.inOffReady + j) = 1 → mem' (tokL.inOffReady + j) = 1) →
      (∀ j < tokL.intCap, j ∉ edges.map Prod.fst → mem' (tokL.inOffReady + j) = stSub.mem (tokL.inOffReady + j)) →
      SolverEdgeAccountsAt
        { modelLoop with
          flow := fun e => modelLoop.flow e + inc e
          detectAccum := fun e => modelLoop.detectAccum e + |inc e| }
        L P mem' tokL.slots tokL.names tokL.slotThresholds tokL.edgeThresholds tokL.edgeRecords
        tokL.inOffReady tokL.intCap s' trees' ∧
      TreeEditNamedSlots s' trees' modelLoop.chain.toTreeChain.chainTree
        (fun f => mem' (tokL.slots + f)) (fun k => mem' (tokL.names + k)) ∧
      SolverEdgeOrientInv L P modelLoop mem' tokL.slots tokL.edgeRecords s' trees' := by
    intro mem' trees' depth' s' hlct' hupd' hfr' hmono' hpres'
    simpa [inc, hΔEq] using haccBridge mem' trees' depth' hlct' hupd'
      (fun a ha hdisj hno h1t h14t h15t h16t =>
        (hfr' a (by dsimp only [h6]; omega) hdisj hno h1t h14t h15t h16t).trans (hfrSub a ha))
      (fun j hj h1j => hmono' j hj ((hfrSub _ (hlt5 (t15L j hj) (by decide))).trans h1j))
      (fun j hj hnot => (hpres' j hj hnot).trans (hfrSub _ (hlt5 (t15L j hj) (by decide))))
  obtain ⟨hEnd, cGA, stGA, tokEnd, hrGA, hout1, houtScal, hnormWithin, hrepEnd, hpresGA, hintCapGA, hnumEnd, hzEnd,
      hhEndLo, hhEndHi, hfrGA, hftGA, hcGA, hrecGA, hptrGA⟩ :=
    updateGoodApplyBody_runs (w := w) (L := L) (P := P) (m := m) (V := V) (psi := psi) (k := k)
      (epsExp := epsExp) (drainUnit := drainUnit) (initTree := initTree) (goodNormOut := goodNormOut)
      (applyPaths := applyPaths) (applyOffTree := applyOffTree) (pathNorm := pathNorm)
      (copyWords := copyWords) (pathFlowTag := pathFlowTag) (explicitRouteUpdate := explicitRouteUpdate)
      (offTreePush := offTreePush) (isNeg := isNeg) (root := root) (eta := etaCopy) (magPtr := magPtr)
      (edgesBase := edgesBase) (pathsBase := pathsBase) (outHeap := heap) (workHeap := h6) (pos := sG8.pos)
      (fmt := F.fmt) (opTree := opTree) (p := p) (ω := ω) (mem := stSub.mem) (model := modelLoop)
      (tok := tokL) (request := request) (magnitude := -inner) (edges := edges) (paths := paths)
      (address := address) (old := old) (inc := inc) (B := B1) (R := R1)
      hlocalCore hfmt4 hGoodNorm hApplyPaths hApplyOff (hNorm request (-inner)) hCopy
      (hTag mult) hTreeImpl (fun dst h1 h2 h3 h4 => hRoute edgesBase tokL.edgeRecords dst
        (h6 + Num.fixedDivideSpace L - L) edges address old mult h1 h2 h3 h4 hdisjAddr hfitOff) hPush hIsNeg hrepSub hnumL hbelowSub hP4 hPW (by omega) hLW
      hcapLPos h2nWL hlogWL hmagPos hstep (by dsimp only [h6, L] at hl4 ⊢; omega) (by dsimp only [magPtr, h6]; omega)
      (by dsimp only [h6]; omega) (by dsimp only [h6]; omega) (by dsimp only [h6, L] at hl1 hl2 hl3 hl4 ⊢; omega)
      (fun x hx => ⟨htagEd x hx, Or.inr (by dsimp only [L] at hl1 hl2 hl3 hl4 ⊢; omega)⟩)
      (fun x hx => ⟨htagPt x hx, Or.inr (by dsimp only [L] at hl1 hl2 hl3 hl4 ⊢; omega)⟩)
      hetaAtSub hmagAt hedgesAtSub hpathsAtSub hfitMult hfitAbs hconn haddrSub hcapTree hzSub'
      (by dsimp only [h6, L] at hroom hgoodSpLe ⊢; omega) haccBridgeSub
  let sG9 : State := { regs := Function.update sG8.regs 16 hEnd, mem := stGA.mem, pos := stGA.pos }
  have rCallGA : Runs w p ω
      (.call 16 goodApply [.reg 0, .reg 31, .reg 29, .reg 25, .reg 26, .reg 27, .reg 28, .reg 5, .reg 16])
      sG8 .normal sG9 (cGA + 10) :=
    runs_call_iff.mpr ⟨[root, etaCopy, magPtr, edgesBase, edges.length, pathsBase, paths.length, heap, h6],
      updateGoodApplyBody goodNormOut applyPaths applyOffTree, .returned hEnd, stGA, cGA,
      by simp [evalArgs, Expr.eval, sG8, sG7, sG6, sG5, sG4, sG3, sG2, sG1, hr0, hr31, hr5],
      hGoodApply, hrGA, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
  have rRetGA : Runs w p ω (.ret (.reg 16)) sG9 (.returned hEnd) sG9 2 :=
    runs_ret_iff.mpr ⟨hEnd, by simp [Expr.eval, sG9], rfl, rfl, rfl⟩
  have rGoodSeq : Runs w p ω _ s12 (.returned hEnd) sG9
      (5 + (3 + (5 + (5 + (5 + (5 + (4 + ((cSub + 5) + ((cGA + 10) + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨sG1, 5, _, rG1,
    runs_seq_iff.mpr (Or.inr ⟨sG2, 3, _, rG2,
    runs_seq_iff.mpr (Or.inr ⟨sG3, 5, _, rG3,
    runs_seq_iff.mpr (Or.inr ⟨sG4, 5, _, rG4,
    runs_seq_iff.mpr (Or.inr ⟨sG5, 5, _, rG5,
    runs_seq_iff.mpr (Or.inr ⟨sG6, 5, _, rG6,
    runs_seq_iff.mpr (Or.inr ⟨sG7, 4, _, rG7,
    runs_seq_iff.mpr (Or.inr ⟨sG8, cSub + 5, _, rCallSub,
    runs_seq_iff.mpr (Or.inr ⟨sG9, cGA + 10, 2, rCallGA, rRetGA, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hnegNeg : -(-inner) = inner := neg_neg inner
  have hPresMeta : PreservesLevelMeta tokL tokEnd s12.mem sG9.mem :=
    PreservesLevelMeta.trans
      ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ ha => ha, fun a ht =>
        ⟨rfl, hfrSub a (hfootL_ltH5 a (Or.inl (hOwnL a ht.tag_ne_zero)))⟩⟩ hpresGA
  refine ⟨hEnd, _, sG9, tokEnd, rGoodSeq, hout1,
    by simpa [actual, hnegNeg] using houtScal,
    by simpa [actual, hnegNeg] using hnormWithin,
    by simpa [inc, hΔEq] using hFitsEnd,
    hrepEnd, hPresMeta, hintCapGA, hzEnd, hhEndLo, by dsimp only [h6, L] at hhEndHi hgoodSpLe ⊢; omega,
    fun a ha hdisj hnf => (hfrGA a (by dsimp only [h6]; omega) hdisj hnf).trans (hfrSub a ha), hftGA, ?_, _, _, hnumEnd, hBend, hRend,
    hrecGA, fun j hj => (hptrGA j hj).trans (hfrSub _ (hlt5 (t13L j hj) (by decide)))⟩
  change _ + Rrep.phi root tokEnd stGA.mem ≤
    updateGoodBranchBudget L G.n maxEdges maxPaths drainUnit + Rrep.phi root tokL s12.mem
  change cGA + Rrep.phi root tokEnd stGA.mem ≤ _ + Rrep.phi root tokL stSub.mem at hcGA
  rw [hphiSub, hExtN] at hcGA
  have hptMul := Nat.mul_le_mul_right (pathTreeBudget LinkCut.PathProg.pathC L G.n + 45) hptMax
  have hedMul : edges.length * (136 * edges.length + 152 * L ^ 2 + 561 * L + drainUnit + 960) ≤
      maxEdges * (136 * maxEdges + 152 * L ^ 2 + 561 * L + drainUnit + 960) :=
    Nat.mul_le_mul hedMax (by omega)
  dsimp only [updateGoodBranchBudget] at hcSub hcGA hptMul hedMul ⊢
  omega

theorem updateSpaceBound_good_le
    {heap L m d nf uLen N findSpace shiftSpace maxEdges maxPaths refreshSpace h0 h3 h4 h5 hEnd : ℕ}
    (hh0 : heap + 1 + 2 * L + 2 + (d + 2) + L + L + 2 * (4 * uLen + 1) + 2 * (m * L) = h0)
    (hh3 : h3 ≤ h0 + 12 * (nf + uLen) + 2 * (4 * uLen + 1))
    (hh4 : h4 ≤ h3 + refreshSpace)
    (hh5 : h5 ≤ h4 + (N + 1) * cycleLoopIterSpace L findSpace shiftSpace)
    (hhEnd : hEnd ≤ h5 + 2 * L + goodApplySpace L maxPaths maxEdges) :
    hEnd ≤ heap + updateSpaceBound L m d nf uLen N findSpace shiftSpace maxEdges maxPaths refreshSpace := by
  unfold updateSpaceBound
  omega

theorem updateBudgetBound_fail_le
    {L d n intCap nf uLen N findBudget shiftBudget maxEdges maxPaths drainUnit refreshBudget
      cPrep cR cL cFail phi0 phiR phiL X : ℕ}
    (hcPrep : cPrep ≤ (if intCap < nf + uLen then 102 * intCap + 34 * (nf + uLen) + 270 else 50) +
      17 * L + 298 * uLen + 260 + (uLen * (34 * L + 100) + 50))
    (hcR : cR + phiR ≤ refreshBudget + phi0)
    (hcL : cL + phiL + X ≤ (N + 1) * cycleLoopIterBudget L d findBudget shiftBudget + 80 + phiR)
    (hcFail : cFail ≤ 17 * L + 40) :
    (cPrep + ((cR + 7) + (7 + ((cL + 7) + (3 + (1 + ((cFail + 5) + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + phiL + X ≤
      updateBudgetBound L d n intCap nf uLen N findBudget shiftBudget maxEdges maxPaths drainUnit refreshBudget +
      phi0 := by
  unfold updateBudgetBound updateGoodBranchBudget
  split_ifs at hcPrep ⊢ <;> omega

theorem updateBudgetBound_good_le
    {L d n intCap nf uLen N findBudget shiftBudget maxEdges maxPaths drainUnit refreshBudget
      cPrep cR cL cGood phi0 phiR phiL phiEnd X : ℕ}
    (hcPrep : cPrep ≤ (if intCap < nf + uLen then 102 * intCap + 34 * (nf + uLen) + 270 else 50) +
      17 * L + 298 * uLen + 260 + (uLen * (34 * L + 100) + 50))
    (hcR : cR + phiR ≤ refreshBudget + phi0)
    (hcL : cL + phiL + X ≤ (N + 1) * cycleLoopIterBudget L d findBudget shiftBudget + 80 + phiR)
    (hcGood : cGood + phiEnd ≤ updateGoodBranchBudget L n maxEdges maxPaths drainUnit + phiL) :
    (cPrep + ((cR + 7) + (7 + ((cL + 7) + (3 + (1 + cGood + 1) + 1) + 1) + 1) + 1) + 1) + phiEnd + X ≤
      updateBudgetBound L d n intCap nf uLen N findBudget shiftBudget maxEdges maxPaths drainUnit refreshBudget +
      phi0 := by
  unfold updateBudgetBound
  split_ifs at hcPrep ⊢ <;> omega

theorem algorithm2_updateWith_eq_of_loop (cfg : Alg2Config) (κ : ℝ)
    (model : Alg2State cfg) (U : List Update) (gVec lVec : ℕ → ℝ) (actual : ℝ) :
    let model1 := alg2PreLoopState cfg model U gVec lVec
    let loopRes := Chain.Ordered.algorithm2_loopWith cfg κ model1.extG model1.extToInt
      model1.extg model1.extℓ model1.chain model1.branD model1.passes model1.lctUpdateOps
    let modelLoop : Alg2State cfg :=
      { model1 with
        chain := loopRes.1
        branD := loopRes.2.1
        passes := loopRes.2.2.1
        lctUpdateOps := loopRes.2.2.2.1 }
    Chain.Ordered.algorithm2_updateWith cfg κ model U gVec lVec actual =
      match loopRes.2.2.2.2 with
      | none => (modelLoop, none)
      | some Δ =>
        let inc : ℕ → ℝ := fun e =>
          if e ∈ modelLoop.extG.E then -(actual / modelLoop.extG.inner modelLoop.extg Δ) * Δ e else 0
        ({ modelLoop with
          flow := fun e => modelLoop.flow e + inc e
          detectAccum := fun e => modelLoop.detectAccum e + |inc e| }, some Δ) := rfl

theorem algorithm2_dsWithFailureWith_update_none (cfg : Alg2Config) (κ : ℝ)
    (model : Alg2State cfg) (U : List Update) (gVec lVec : ℕ → ℝ) (actual : ℝ)
    (hOpt : (Chain.Ordered.algorithm2_loopWith cfg κ (alg2PreLoopState cfg model U gVec lVec).extG
      (alg2PreLoopState cfg model U gVec lVec).extToInt
      (alg2PreLoopState cfg model U gVec lVec).extg
      (alg2PreLoopState cfg model U gVec lVec).extℓ
      (alg2PreLoopState cfg model U gVec lVec).chain
      (alg2PreLoopState cfg model U gVec lVec).branD
      (alg2PreLoopState cfg model U gVec lVec).passes
      (alg2PreLoopState cfg model U gVec lVec).lctUpdateOps).2.2.2.2 = none) :
    let model1 := alg2PreLoopState cfg model U gVec lVec
    let loopRes := Chain.Ordered.algorithm2_loopWith cfg κ model1.extG model1.extToInt
      model1.extg model1.extℓ model1.chain model1.branD model1.passes model1.lctUpdateOps
    (Chain.Ordered.algorithm2_dsWithFailureWith cfg κ).update model U gVec lVec actual =
      ({ model1 with
        chain := loopRes.1
        branD := loopRes.2.1
        passes := loopRes.2.2.1
        lctUpdateOps := loopRes.2.2.2.1 }, none) := by
  dsimp only
  change Chain.Ordered.algorithm2_updateWith cfg κ model U gVec lVec actual = _
  rw [algorithm2_updateWith_eq_of_loop]
  dsimp only
  rw [hOpt]
  rfl

theorem algorithm2_dsWithFailureWith_update_some (cfg : Alg2Config) (κ : ℝ)
    (model : Alg2State cfg) (U : List Update) (gVec lVec : ℕ → ℝ) (actual : ℝ) (Δ : ℕ → ℝ)
    (hOpt : (Chain.Ordered.algorithm2_loopWith cfg κ (alg2PreLoopState cfg model U gVec lVec).extG
      (alg2PreLoopState cfg model U gVec lVec).extToInt
      (alg2PreLoopState cfg model U gVec lVec).extg
      (alg2PreLoopState cfg model U gVec lVec).extℓ
      (alg2PreLoopState cfg model U gVec lVec).chain
      (alg2PreLoopState cfg model U gVec lVec).branD
      (alg2PreLoopState cfg model U gVec lVec).passes
      (alg2PreLoopState cfg model U gVec lVec).lctUpdateOps).2.2.2.2 = some Δ) :
    let model1 := alg2PreLoopState cfg model U gVec lVec
    let loopRes := Chain.Ordered.algorithm2_loopWith cfg κ model1.extG model1.extToInt
      model1.extg model1.extℓ model1.chain model1.branD model1.passes model1.lctUpdateOps
    let modelLoop : Alg2State cfg :=
      { model1 with
        chain := loopRes.1
        branD := loopRes.2.1
        passes := loopRes.2.2.1
        lctUpdateOps := loopRes.2.2.2.1 }
    let inc : ℕ → ℝ := fun e =>
      if e ∈ modelLoop.extG.E then -(actual / modelLoop.extG.inner modelLoop.extg Δ) * Δ e else 0
    (Chain.Ordered.algorithm2_dsWithFailureWith cfg κ).update model U gVec lVec actual =
      ({ modelLoop with
        flow := fun e => modelLoop.flow e + inc e
        detectAccum := fun e => modelLoop.detectAccum e + |inc e| }, some Δ) := by
  dsimp only
  change Chain.Ordered.algorithm2_updateWith cfg κ model U gVec lVec actual = _
  rw [algorithm2_updateWith_eq_of_loop]
  dsimp only
  rw [hOpt]
  rfl

private theorem updateLoop_lvlM_N0 (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (ℓ' g' : ℕ → ℝ) :
    ∀ rem idx (st : ChainState T P) curG curU curEnc,
      (Chain.Ordered.updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU curEnc).1.lvlM = st.lvlM ∧
      (Chain.Ordered.updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU curEnc).1.N₀ = st.N₀
  | 0, _, st, curG, curU, _ => by
    dsimp only [Chain.Ordered.updateLoop]
    split_ifs <;> exact ⟨rfl, rfl⟩
  | rem + 1, idx, st, curG, curU, curEnc => by
    dsimp only [Chain.Ordered.updateLoop]
    split_ifs
    · dsimp only [Chain.Ordered.algorithm1_rebuild]
      split_ifs <;> exact ⟨rfl, rfl⟩
    · exact updateLoop_lvlM_N0 T L TP P N₀ ℓ' g' rem (idx + 1) _ _ _ 0

/-- `alg2PreLoopState` preserves the chain's level size bounds `lvlM` and `N₀`. -/
theorem alg2PreLoopState_lvlM_N0 (cfg : Alg2Config) (model : Alg2State cfg)
    (U : List Update) (gVec lVec : ℕ → ℝ) :
    (alg2PreLoopState cfg model U gVec lVec).chain.lvlM = model.chain.lvlM ∧
    (alg2PreLoopState cfg model U gVec lVec).chain.N₀ = model.chain.N₀ :=
  updateLoop_lvlM_N0 cfg.T cfg.L cfg.TP cfg.P cfg.N₀ _ _ cfg.P.d 0 _ _ _ _

/-- Telescopes the refresh and cycle-loop credit inequalities into the form expected by
`updateBudgetBound_fail_le` and `updateBudgetBound_good_le`. -/
theorem update_credit_telescope {cfg : Alg2Config} {L B0 N0 N1 toolMul treeMul
    cR cL refBud phi0 phiR phiL : ℕ}
    {model : Alg2State cfg} {U : List Update} {gVec lVec : ℕ → ℝ} {k : ℕ}
    (hMono : toolMul = 0 ∨ ToolCostMono cfg.T)
    (hcR : cR + phiR ≤ refBud +
      toolMul * ((alg2PreLoopState cfg model U gVec lVec).chain.totalRuntime -
        model.chain.totalRuntime) +
      treeMul * ((alg2PreLoopState cfg model U gVec lVec).chain.totalTreeUpdates -
        model.chain.totalTreeUpdates) + phi0)
    (hcL :
      let model1 := alg2PreLoopState cfg model U gVec lVec
      let loopRes := Chain.Ordered.algorithm2_loopWith cfg (1 / (2 : ℝ) ^ k) model1.extG
        model1.extToInt model1.extg model1.extℓ model1.chain model1.branD model1.passes
        model1.lctUpdateOps
      cL + phiL + N1 * B0 +
          toolMul * model1.chain.totalRuntime + treeMul * model1.chain.totalTreeUpdates ≤
        (N0 + 1) * B0 + 80 + phiR +
          toolMul * loopRes.1.totalRuntime + treeMul * loopRes.1.totalTreeUpdates) :
    let model1 := alg2PreLoopState cfg model U gVec lVec
    let loopRes := Chain.Ordered.algorithm2_loopWith cfg (1 / (2 : ℝ) ^ k) model1.extG
      model1.extToInt model1.extg model1.extℓ model1.chain model1.branD model1.passes
      model1.lctUpdateOps
    let d1 := (toolMul * loopRes.1.totalRuntime + treeMul * loopRes.1.totalTreeUpdates) -
      (toolMul * model1.chain.totalRuntime + treeMul * model1.chain.totalTreeUpdates)
    let d0 := (toolMul * loopRes.1.totalRuntime + treeMul * loopRes.1.totalTreeUpdates) -
      (toolMul * model.chain.totalRuntime + treeMul * model.chain.totalTreeUpdates)
    cR + (phiR + d1) ≤ refBud + (phi0 + d0) ∧
    cL + phiL + N1 * B0 ≤ (N0 + 1) * B0 + 80 + (phiR + d1) ∧
    toolMul * model.chain.totalRuntime + treeMul * model.chain.totalTreeUpdates + d0 =
      toolMul * loopRes.1.totalRuntime + treeMul * loopRes.1.totalTreeUpdates := by
  dsimp only
  let model1 := alg2PreLoopState cfg model U gVec lVec
  let loopRes := Chain.Ordered.algorithm2_loopWith cfg (1 / (2 : ℝ) ^ k) model1.extG
    model1.extToInt model1.extg model1.extℓ model1.chain model1.branD model1.passes
    model1.lctUpdateOps
  have hRt1 : toolMul * model.chain.totalRuntime ≤ toolMul * model1.chain.totalRuntime := by
    rcases hMono with rfl | hM
    · simp
    · exact Nat.mul_le_mul_left _
        (algorithm1_update_totalRuntime_mono hM cfg.L cfg.TP cfg.P cfg.N₀ model.chain _ _ _)
  have hTu1 : treeMul * model.chain.totalTreeUpdates ≤ treeMul * model1.chain.totalTreeUpdates :=
    Nat.mul_le_mul_left _
      (algorithm1_update_totalTreeUpdates_mono cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain _ _ _)
  have hRt2 : toolMul * model1.chain.totalRuntime ≤ toolMul * loopRes.1.totalRuntime := by
    rcases hMono with rfl | hM
    · simp
    · exact Nat.mul_le_mul_left _
        (algorithm2_loopWith_mono hM (1 / (2 : ℝ) ^ k) model1.extG model1.extToInt
          model1.extg model1.extℓ model1.chain model1.branD model1.passes model1.lctUpdateOps).1
  have hTu2 : treeMul * model1.chain.totalTreeUpdates ≤ treeMul * loopRes.1.totalTreeUpdates :=
    Nat.mul_le_mul_left _
      (algorithm2_loopWith_totalTreeUpdates_mono cfg (1 / (2 : ℝ) ^ k) model1.extG model1.extToInt
        model1.extg model1.extℓ model1.chain model1.branD model1.passes model1.lctUpdateOps)
  have hSub1 : toolMul * (model1.chain.totalRuntime - model.chain.totalRuntime) +
        toolMul * model.chain.totalRuntime = toolMul * model1.chain.totalRuntime := by
    rcases hMono with rfl | hM
    · simp
    · rw [← Nat.mul_add]; congr 1
      exact Nat.sub_add_cancel
        (algorithm1_update_totalRuntime_mono hM cfg.L cfg.TP cfg.P cfg.N₀ model.chain _ _ _)
  have hSub2 : treeMul * (model1.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
        treeMul * model.chain.totalTreeUpdates = treeMul * model1.chain.totalTreeUpdates := by
    rw [← Nat.mul_add]; congr 1
    exact Nat.sub_add_cancel
      (algorithm1_update_totalTreeUpdates_mono cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain _ _ _)
  have hB_le_C : toolMul * model1.chain.totalRuntime + treeMul * model1.chain.totalTreeUpdates ≤
      toolMul * loopRes.1.totalRuntime + treeMul * loopRes.1.totalTreeUpdates :=
    Nat.add_le_add hRt2 hTu2
  have hAC : toolMul * model.chain.totalRuntime + treeMul * model.chain.totalTreeUpdates ≤
      toolMul * loopRes.1.totalRuntime + treeMul * loopRes.1.totalTreeUpdates :=
    (Nat.add_le_add hRt1 hTu1).trans hB_le_C
  have hadd1 := Nat.sub_add_cancel hB_le_C
  have hadd2 := Nat.sub_add_cancel hAC
  dsimp only [model1, loopRes] at hcR hcL hRt1 hTu1 hRt2 hTu2 hSub1 hSub2 hB_le_C hAC hadd1 hadd2 ⊢
  exact ⟨by omega, by omega, by omega⟩

end MinCostFlow.MinRatio

end
