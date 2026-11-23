module

public import MinCostFlow.MinRatio.WireEvalBase
import WordRAM.Tactic

/-!
# Path-summary accumulation loop for `evalCycleBody`

Proves `evalPathsLoop_runs`: Loop 1 of `evalCycleBody` (`WireEvalBase.lean`) iterates over
`paths`, calls `opTree 3` (`PathSummary`) and `Num.add` on each path, and accumulates the
signed gradient and unsigned length sums while preserving `LctInvWith`, `PathTreeNumericInv`,
`TreeEditNamedSlots`, and every tree edge's accounts and orientation.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut LinkCut.PathTree LinkCut.PathProg Chain

private theorem lctPathSummary_fst_n (s : PathTreeState) (u v : ℕ) :
    (lctPathSummary pathPayload s u v).1.n = s.n := rfl

theorem evalPathsLoop_runs
    {w L P m V psi k epsExp drainUnit initTree root pathsBase workHeap maxEdges maxPaths : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)}
    {opTree : ℕ → ℕ} {numAdd : ℕ} {p : Program} {ω : ℕ → Bool}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore}
    {paths : List (ℕ × ℕ)} {B R : ℤ}
    (hfmt4 : fmt.limbBits = 4)
    (hTreeImpl : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).Implements w p initTree opTree
      (pathTreeMachineContract fmt L LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc L)))
    (hAdd : MeetsContract w p numAdd (Num.addContract w 4))
    (hw10 : 10 ≤ w)
    (hrep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok (fun _ => 0) ∨ True)
    (hpathsMax : paths.length ≤ maxPaths)
    (hpathsEnd : pathsBase + 2 * paths.length ≤ workHeap)
    (hcapE : 2 * (((maxEdges + maxPaths * model.extG.n : ℕ) : ℤ) * B) < (Num.capacity 4 L : ℤ))
    (hcapT : 2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ))
    (hlogW : Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L)
    (hroom : workHeap + evalCycleSpace L maxEdges maxPaths < 2 ^ w) :
    let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
    let F := model.chain.toTreeChain.chainTree
    let E0 := F.E ∩ (model.chain.G 0).E
    ∀ (rem : ℕ) (st : State) (s : PathTreeState) (trees : List AuxTree) (depth : ℕ → ℕ)
      (treeTok : Rtree.τ) (curInner curNorm : ℤ) (innerPtr normPtr curHeap : ℕ),
      let j := paths.length - rem
      rem ≤ paths.length →
      st.regs 1 = st.regs 1 →
      st.regs 3 = pathsBase → st.regs 4 = paths.length → st.regs 5 = workHeap →
      st.regs 7 = tok.treeHeap → st.regs 8 = L →
      st.regs 10 = innerPtr → st.regs 11 = normPtr → st.regs 12 = curHeap → st.regs 13 = j →
      tok.treeHeap < 2 ^ w → s.n = model.extG.n → 2 * s.n + 1 < 2 ^ w →
      LctInvWith pathPayload s trees tok.free depth →
      PathTreeNumericInv s trees B R →
      Rtree.rep tok.treeHeap s treeTok st.mem →
      (∀ a, Rtree.foot tok.treeHeap treeTok a → a < workHeap) →
      (∀ x < 2 * paths.length, ¬ Rtree.foot tok.treeHeap treeTok (pathsBase + x)) →
      PathEndpointsAt st.mem pathsBase paths →
      (∀ q ∈ paths, q.1 < model.extG.n ∧ q.2 < model.extG.n ∧ F.Connected q.1 q.2) →
      F.IsForest →
      (∀ e ∈ F.E, e < tok.intCap ∧ F.tail e < model.extG.n ∧ F.head e < model.extG.n ∧ F.tail e ≠ F.head e) →
      FreshInv model.extG (model.chain.G 0) model.extToInt model.intToExt model.nextFresh →
      TreeEditNamedSlots s trees F (fun ei => st.mem (tok.slots + ei)) (fun sl => st.mem (tok.names + sl)) →
      (∀ e ∈ F.E, ¬ Rtree.foot tok.treeHeap treeTok (tok.slots + e) ∧ tok.slots + e < workHeap) →
      (∀ sl < 2 * model.extG.n, ¬ Rtree.foot tok.treeHeap treeTok (tok.names + sl) ∧ tok.names + sl < workHeap) →
      (∀ e ∈ E0, ∀ val : PathEdgeValue,
        (st.mem (tok.slots + e), some val) ∈ forestPairs pathPayload s.splay trees →
        (val.originalGradient : ℝ) / (2 : ℝ) ^ P = model.extg (model.intToExt e) ∧
        (val.length : ℝ) / (2 : ℝ) ^ P = model.extℓ (model.intToExt e) ∧
        (val.forward = true →
          inducedSubPar pathPayload s.splay trees (vid (F.head e)) = st.mem (tok.slots + e) ∧
          inducedSubPar pathPayload s.splay trees (st.mem (tok.slots + e)) = vid (F.tail e)) ∧
        (val.forward = false →
          inducedSubPar pathPayload s.splay trees (vid (F.tail e)) = st.mem (tok.slots + e) ∧
          inducedSubPar pathPayload s.splay trees (st.mem (tok.slots + e)) = vid (F.head e))) →
      (∀ e ∈ E0, ∃ val : PathEdgeValue,
        (st.mem (tok.slots + e), some val) ∈ forestPairs pathPayload s.splay trees) →
      (∀ e ∈ F.E, e ∉ E0 → ∀ val : PathEdgeValue,
        (st.mem (tok.slots + e), some val) ∉ forestPairs pathPayload s.splay trees) →
      (innerPtr = workHeap ∨ workHeap + 2 * L ≤ innerPtr) →
      (normPtr = workHeap + L ∨ workHeap + 2 * L ≤ normPtr) →
      innerPtr + L ≤ curHeap → normPtr + L ≤ curHeap →
      workHeap + 2 * L ≤ curHeap →
      curHeap ≤ workHeap + 2 * L + j * (pathApplySpace L + 4 * L) →
      PathIntAt st.mem innerPtr 4 L curInner →
      PathIntAt st.mem normPtr 4 L curNorm →
      |curInner| ≤ ((j * model.extG.n : ℕ) : ℤ) * B →
      |curNorm| ≤ ((j * model.extG.n : ℕ) : ℤ) * B →
      ZeroFrom st.mem curHeap →
      ∃ out cost s' trees' depth' treeTok' addGrad addLen innerPtr' normPtr' curHeap',
        Runs w p ω
          (.loop (.bin .lt (.reg 13) (.reg 4))
            ((.assign 14 (.bin .add (.load (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 13)))) (.const 1)) ;;
              .assign 15 (.bin .add (.load (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 13))) (.const 1))) (.const 1)) ;;
              .assign 16 (.reg 12) ;;
              .call 12 (opTree 3) [.reg 7, .reg 14, .reg 15, .reg 16] ;;
              .assign 12 (.bin .add (.reg 12) (.bin .mul (.const 2) (.reg 8))) ;;
              .assign 17 (.reg 12) ;;
              .call 12 numAdd [.reg 10, .reg 16, .reg 8, .reg 12] ;;
              .assign 10 (.reg 17) ;;
              .assign 17 (.reg 12) ;;
              .assign 16 (.bin .add (.reg 16) (.reg 8)) ;;
              .call 12 numAdd [.reg 11, .reg 16, .reg 8, .reg 12] ;;
              .assign 11 (.reg 17)) ;;
             .assign 13 (.bin .add (.reg 13) (.const 1))))
          st .normal out cost ∧
        (∀ r, r ≤ 9 → out.regs r = st.regs r) ∧
        out.regs 10 = innerPtr' ∧ out.regs 11 = normPtr' ∧ out.regs 12 = curHeap' ∧
        (innerPtr' = workHeap ∨ workHeap + 2 * L ≤ innerPtr') ∧
        (normPtr' = workHeap + L ∨ workHeap + 2 * L ≤ normPtr') ∧
        innerPtr' + L ≤ curHeap' ∧ normPtr' + L ≤ curHeap' ∧
        curHeap ≤ curHeap' ∧ curHeap' ≤ workHeap + 2 * L + paths.length * (pathApplySpace L + 4 * L) ∧
        PathIntAt out.mem innerPtr' 4 L (curInner + addGrad) ∧
        PathIntAt out.mem normPtr' 4 L (curNorm + addLen) ∧
        (addGrad : ℝ) / (2 : ℝ) ^ P =
          ((paths.drop j).map fun q => ∑ e ∈ E0,
            model.extg (model.intToExt e) * walkFlow (F.forestPath q.1 q.2) e).sum ∧
        (addLen : ℝ) / (2 : ℝ) ^ P =
          ((paths.drop j).map fun q => ∑ e ∈ E0,
            model.extℓ (model.intToExt e) * |walkFlow (F.forestPath q.1 q.2) e|).sum ∧
        |curInner + addGrad| ≤ ((paths.length * model.extG.n : ℕ) : ℤ) * B ∧
        |curNorm + addLen| ≤ ((paths.length * model.extG.n : ℕ) : ℤ) * B ∧
        s'.n = model.extG.n ∧
        LctInvWith pathPayload s' trees' tok.free depth' ∧
        PathTreeNumericInv s' trees' B R ∧
        Rtree.rep tok.treeHeap s' treeTok' out.mem ∧
        TreeEditNamedSlots s' trees' F (fun ei => st.mem (tok.slots + ei)) (fun sl => st.mem (tok.names + sl)) ∧
        (∀ sl val, (sl, some val) ∈ forestPairs pathPayload s'.splay trees' →
          ∃ val0, (sl, some val0) ∈ forestPairs pathPayload s.splay trees) ∧
        (∀ e ∈ E0, ∀ val : PathEdgeValue,
          (st.mem (tok.slots + e), some val) ∈ forestPairs pathPayload s.splay trees →
          ∃ val' : PathEdgeValue,
            (st.mem (tok.slots + e), some val') ∈ forestPairs pathPayload s'.splay trees' ∧
            val'.originalFlow = val.originalFlow ∧
            val'.originalGradient = val.originalGradient ∧
            val'.length = val.length ∧
            val'.detector = val.detector ∧
            (val'.forward = true →
              inducedSubPar pathPayload s'.splay trees' (vid (F.head e)) = st.mem (tok.slots + e) ∧
              inducedSubPar pathPayload s'.splay trees' (st.mem (tok.slots + e)) = vid (F.tail e)) ∧
            (val'.forward = false →
              inducedSubPar pathPayload s'.splay trees' (vid (F.tail e)) = st.mem (tok.slots + e) ∧
              inducedSubPar pathPayload s'.splay trees' (st.mem (tok.slots + e)) = vid (F.head e))) ∧
        ZeroFrom out.mem curHeap' ∧
        (∀ a < workHeap, ¬ Rtree.foot tok.treeHeap treeTok a → out.mem a = st.mem a) ∧
        cost + Rtree.phi tok.treeHeap treeTok' out.mem ≤
          rem * (25 * (LinkCut.PathProg.pathC * (L + 1) ^ 2) * (4 * L + 1) + 76 * L + 170) + 4 +
          Rtree.phi tok.treeHeap treeTok st.mem := by
  intro Rtree F E0 rem
  have hw1024 : 1024 ≤ 2 ^ w := by
    calc (1024 : ℕ) = 2 ^ 10 := by decide
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw10
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hLW : L < 2 ^ w := by dsimp only [evalCycleSpace] at hroom; omega
  have h2LW : 2 * L < 2 ^ w := by dsimp only [evalCycleSpace] at hroom; omega
  induction rem with
  | zero =>
    intro st s trees depth treeTok curInner curNorm innerPtr normPtr curHeap j hrem _ hr3 hr4 hr5
      hr7 hr8 hr10 hr11 hr12 hr13 _ hsn _ hW hnum hrep _ _ _ _ _ _ _ hns _ _ hor _ _
      hInPos hNoPos hInLe hNoLe hHeapLo hHeapHi hInAt hNoAt hInBd hNoBd hz
    have hjEq : j = paths.length := by dsimp only [j]; omega
    have hdrop : paths.drop j = [] := List.drop_eq_nil_of_le (by omega)
    have hcond0 : (Expr.bin .lt (.reg 13) (.reg 4)).eval w st = some 0 := by
      simp [Expr.eval, BinOp.eval, hr13, hr4, hjEq, show 0 < 2 ^ w by omega]
    refine ⟨st, 4, s, trees, depth, treeTok, 0, 0, innerPtr, normPtr, curHeap,
      runs_loop_iff.mpr (Or.inl ⟨hcond0, rfl, rfl, by simp [Expr.size]⟩),
      fun _ _ => rfl, hr10, hr11, hr12, hInPos, hNoPos, hInLe, hNoLe, le_rfl,
      by rw [hjEq] at hHeapHi; exact hHeapHi,
      by simpa using hInAt, by simpa using hNoAt,
      by simp [hdrop], by simp [hdrop],
      by simpa [hjEq] using hInBd, by simpa [hjEq] using hNoBd,
      hsn, hW, hnum, hrep, hns, fun _ val hp => ⟨val, hp⟩, fun e he val hp => ?_, hz, fun _ _ _ => rfl, by omega⟩
    obtain ⟨_, _, hft, hff⟩ := hor e he val hp
    exact ⟨val, hp, rfl, rfl, rfl, rfl, hft, hff⟩
  | succ rem ih =>
    intro st s trees depth treeTok curInner curNorm innerPtr normPtr curHeap j hrem _ hr3 hr4 hr5
      hr7 hr8 hr10 hr11 hr12 hr13 htreeW hsn h2nW hW hnum hrep hfoot hsepP hends hpathsOk
      hF hV hfresh hns hslotsOk hnamesOk hor hhasVal hnoVal
      hInPos hNoPos hInLe hNoLe hHeapLo hHeapHi hInAt hNoAt hInBd hNoBd hz
    have hjLt : j < paths.length := by dsimp only [j]; omega
    have hremNext : paths.length - rem = j + 1 := by dsimp only [j]; omega
    have hstepBound : workHeap + 2 * L + (j + 1) * (pathApplySpace L + 4 * L) < 2 ^ w := by
      have hm1 : (j + 1) * (pathApplySpace L + 4 * L) ≤ maxPaths * (pathApplySpace L + 4 * L) :=
        Nat.mul_le_mul_right _ (by omega)
      dsimp only [evalCycleSpace] at hroom; omega
    have hcurW : curHeap < 2 ^ w := by
      have hm : j * (pathApplySpace L + 4 * L) ≤ (j + 1) * (pathApplySpace L + 4 * L) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    obtain ⟨hmU, hmV⟩ := hends j hjLt
    obtain ⟨huLt, hvLt, hconnJ⟩ := hpathsOk (paths[j]'hjLt) (List.getElem_mem hjLt)
    let u := (paths[j]'hjLt).1
    let v := (paths[j]'hjLt).2
    let u1 := vid u
    let v1 := vid v
    have hu1W : u1 < 2 ^ w := by dsimp only [u1, vid, u]; omega
    have hv1W : v1 < 2 ^ w := by dsimp only [v1, vid, v]; omega
    have hu1W' : u + 1 < 2 ^ w := hu1W
    have hv1W' : v + 1 < 2 ^ w := hv1W
    have h2jW : 2 * j < 2 ^ w := by omega
    have hp2jW : pathsBase + 2 * j < 2 ^ w := by omega
    have hp2j1W : pathsBase + 2 * j + 1 < 2 ^ w := by omega
    -- Step 1: load `u1`, `v1`, `sumPtr := curHeap`
    let s1 : State := { st with regs := Function.update st.regs 14 u1 }
    let s2 : State := { s1 with regs := Function.update s1.regs 15 v1 }
    let s3 : State := { s2 with regs := Function.update s2.regs 16 curHeap }
    have r1 : Runs w p ω (.assign 14 (.bin .add (.load (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 13)))) (.const 1)))
        st .normal s1 9 :=
      runs_assign_iff.mpr ⟨u1, by
        simp [Expr.eval, BinOp.eval, hr3, hr13, hw2, hw1, h2jW, hp2jW, hmU, hu1W', u1, vid, u], rfl, rfl, rfl⟩
    have r2 : Runs w p ω (.assign 15 (.bin .add (.load (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 13))) (.const 1))) (.const 1)))
        s1 .normal s2 11 :=
      runs_assign_iff.mpr ⟨v1, by
        simp [Expr.eval, BinOp.eval, s1, hr3, hr13, hw2, hw1, h2jW, hp2jW, hp2j1W, hmV, hv1W', v1, vid, v], rfl, rfl, rfl⟩
    have r3 : Runs w p ω (.assign 16 (.reg 12)) s2 .normal s3 2 :=
      runs_assign_iff.mpr ⟨curHeap, by simp [Expr.eval, s2, s1, hr12], rfl, rfl, rfl⟩
    -- Step 2: call `opTree 3` (`PathSummary`)
    have hfitCur : pathTreeFits 4 L s := hnum.fits hW (hsn.symm ▸ hcapT)
    have hconnT : pathTreeConnected s u1 v1 :=
      treeEditNamedSlots_connected hW hns (fun e he => ⟨hsn.symm ▸ (hV e he).2.1, hsn.symm ▸ (hV e he).2.2.1⟩)
        (hsn.symm ▸ huLt) (hsn.symm ▸ hvLt) hconnJ
    obtain ⟨tu, htu, huIn⟩ := List.mem_flatMap.mp (hW.verticesActive u (hsn.symm ▸ huLt))
    obtain ⟨trees1, depth1, hW1, hnum1⟩ := pathTreeNumericInv_summary hW hnum htu huIn
      (show isVertex s.n u1 from ⟨by dsimp [u1, vid]; omega, by dsimp [u1, vid]; omega⟩)
      (show isVertex s.n v1 from ⟨by dsimp [v1, vid]; omega, by dsimp [v1, vid]; omega⟩)
    have hnextN : (lctPathSummary pathPayload s u1 v1).1.n = s.n := lctPathSummary_fst_n s u1 v1
    have hfitNext : pathTreeFits 4 L (lctPathSummary pathPayload s u1 v1).1 :=
      hnum1.fits hW1 (by rw [hnextN, hsn]; exact hcapT)
    have hpre3 : (pathTreeMachineContract fmt L LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc L)).pre
        3 s [tok.treeHeap, u1, v1, curHeap] s3.mem := by
      refine ⟨⟨trees, tok.free, depth, hW⟩, hfmt4.symm ▸ hfitCur, h2nW,
        hfmt4.symm ▸ (hsn.symm ▸ hlogW), tok.treeHeap, u1, v1, curHeap, rfl,
        ⟨by dsimp [u1, vid]; omega, by dsimp [u1, vid]; omega⟩,
        ⟨by dsimp [v1, vid]; omega, by dsimp [v1, vid]; omega⟩, hconnT, hfmt4.symm ▸ hfitNext⟩
    have hroom3 : curHeap + LinkCut.PathProg.pathAlloc L 3 s.n [tok.treeHeap, u1, v1, curHeap] < 2 ^ w := by
      simp only [LinkCut.PathProg.pathAlloc, show (3 : ℕ) ≠ 7 by decide, ↓reduceIte]
      rw [Nat.add_mul, one_mul] at hstepBound
      dsimp only [pathApplySpace] at hHeapHi hstepBound ⊢; omega
    obtain ⟨sNext, cTree, after, treeTok1, ret1, hrTree, hrep1, hpost1, hresp1, hcTree⟩ :=
      pathTree_runs_call (ω := ω) (st := s3) (reg := 12) (i := 3) (b := tok.treeHeap)
        (args := [.reg 7, .reg 14, .reg 15, .reg 16]) (vs := [tok.treeHeap, u1, v1, curHeap])
        hTreeImpl (by simp [evalArgs, Expr.eval, s3, s2, s1, hr7])
        (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl | rfl | rfl <;> omega)
        rfl hrep hpre3 (fun a ha => by
          simp only [heapArg, List.getLastD_cons, List.getLastD_nil]
          exact lt_of_lt_of_le (hfoot a ha) (by omega)) hz hroom3
    have hsNextEq : sNext = (lctPathSummary pathPayload s u1 v1).1 := hpost1.1
    have hsumAt : PathSummaryAt after.mem curHeap 4 L (lctPathSummary pathPayload s u1 v1).2 := by
      rw [← hfmt4]; exact hpost1.2
    subst hsNextEq
    let sum := (lctPathSummary pathPayload s u1 v1).2
    let s1Tree := (lctPathSummary pathPayload s u1 v1).1
    -- Foot of `treeTok1` is identical to foot of `treeTok`
    have hfoot1_eq : ∀ a, Rtree.foot tok.treeHeap treeTok1 a ↔ Rtree.foot tok.treeHeap treeTok a := by
      intro a
      have h1 : treeTok1.1 = s1Tree := hrep1.1
      have h0 : treeTok.1 = s := hrep.1
      change (tok.treeHeap ≤ a ∧ a < arenaEnd tok.treeHeap treeTok1.1.n L) ↔
        (tok.treeHeap ≤ a ∧ a < arenaEnd tok.treeHeap treeTok.1.n L)
      rw [h1, h0, hnextN]
    -- Apply `lctPathSummary_step_account`
    have hE_s : ValsOnEdges s := hrep.2.2.vals
    let gInt : ℕ → ℤ := fun e => if h : e ∈ E0 then (hhasVal e h).choose.originalGradient else 0
    let ℓInt : ℕ → ℤ := fun e => if h : e ∈ E0 then (hhasVal e h).choose.length else 0
    have hvals_s : ∀ e ∈ E0, ∀ val : PathEdgeValue,
        (st.mem (tok.slots + e), some val) ∈ forestPairs pathPayload s.splay trees →
        val.originalGradient = gInt e ∧ val.length = ℓInt e ∧
        |val.gradient| ≤ B ∧ |val.length| ≤ B ∧
        (val.forward = true →
          inducedSubPar pathPayload s.splay trees (vid (F.head e)) = st.mem (tok.slots + e) ∧
          inducedSubPar pathPayload s.splay trees (st.mem (tok.slots + e)) = vid (F.tail e)) ∧
        (val.forward = false →
          inducedSubPar pathPayload s.splay trees (vid (F.tail e)) = st.mem (tok.slots + e) ∧
          inducedSubPar pathPayload s.splay trees (st.mem (tok.slots + e)) = vid (F.head e)) := by
      intro e he val hp
      have huq := forestPairs_val_unique hW hp (hhasVal e he).choose_spec
      have hbd := hnum.2.2.2.1 _ val hp
      have ho := hor e he val hp
      refine ⟨by dsimp [gInt]; rw [dite_eq_left_of_eq_true (eq_true he), huq],
        by dsimp [ℓInt]; rw [dite_eq_left_of_eq_true (eq_true he), huq],
        hbd.1, hbd.2.1, ho.2.2.1, ho.2.2.2⟩
    obtain ⟨hns1, hpreSome1, hor1, hsumG_eq, hsumL_eq, hsumG_bd, hsumL_bd⟩ :=
      lctPathSummary_step_account hW hE_s hns hF Finset.inter_subset_left
        (fun e he => ⟨hsn.symm ▸ (hV e he).2.1, hsn.symm ▸ (hV e he).2.2.1, (hV e he).2.2.2⟩)
        (hsn.symm ▸ huLt) (hsn.symm ▸ hvLt) hconnJ hnum.1 hvals_s hhasVal hnoVal hW1
    -- Advance `curHeap := ret1 + 2 * L`
    obtain ⟨hret1Lo, hret1Hi, hz1, hfr1, _⟩ := hresp1
    change curHeap ≤ ret1 at hret1Lo
    change ret1 ≤ curHeap + LinkCut.PathProg.pathAlloc L 3 s.n [tok.treeHeap, u1, v1, curHeap] at hret1Hi
    simp only [LinkCut.PathProg.pathAlloc, show (3 : ℕ) ≠ 7 by decide, ↓reduceIte] at hret1Hi
    change ∀ a < curHeap, ¬ Rtree.foot tok.treeHeap treeTok a → after.mem a = st.mem a at hfr1
    let heap1 := ret1 + 2 * L
    have hheap1_le : heap1 + 2 * L ≤ workHeap + 2 * L + (j + 1) * (pathApplySpace L + 4 * L) := by
      rw [Nat.add_mul, one_mul]; dsimp only [heap1, pathApplySpace] at hHeapHi hret1Hi ⊢; omega
    have hheap1W : heap1 < 2 ^ w := by omega
    have hret1W : ret1 < 2 ^ w := by omega
    let s4 : State := { after with regs := Function.update s3.regs 12 ret1 }
    let s5 : State := { s4 with regs := Function.update s4.regs 12 heap1 }
    let s6 : State := { s5 with regs := Function.update s5.regs 17 heap1 }
    have r5 : Runs w p ω (.assign 12 (.bin .add (.reg 12) (.bin .mul (.const 2) (.reg 8)))) s4 .normal s5 6 :=
      runs_assign_iff.mpr ⟨heap1, by
        simp [Expr.eval, BinOp.eval, s4, s3, s2, s1, hr8, hw2, h2LW, hheap1W, heap1], rfl, rfl, rfl⟩
    have r6 : Runs w p ω (.assign 17 (.reg 12)) s5 .normal s6 2 :=
      runs_assign_iff.mpr ⟨heap1, by simp [Expr.eval, s5], rfl, rfl, rfl⟩
    -- `innerPtr` and `normPtr` blocks preserved across `opTree 3` (since they are `≥ workHeap > Rtree.foot`)
    have hInAt1 : PathIntAt after.mem innerPtr 4 L curInner :=
      hInAt.congr fun i hi => hfr1 (innerPtr + i) (by omega) (fun hf => by have := hfoot _ hf; omega)
    have hNoAt1 : PathIntAt after.mem normPtr 4 L curNorm :=
      hNoAt.congr fun i hi => hfr1 (normPtr + i) (by omega) (fun hf => by have := hfoot _ hf; omega)
    -- Step 3: first `numAdd [innerPtr, sumPtr, L, heap1]`
    have hInSumBd : |curInner + sum.gradient| ≤ (((j + 1) * model.extG.n : ℕ) : ℤ) * B := by
      rw [hsn] at hsumG_bd
      calc |curInner + sum.gradient| ≤ |curInner| + |sum.gradient| := abs_add_le _ _
        _ ≤ ((j * model.extG.n : ℕ) : ℤ) * B + (model.extG.n : ℤ) * B := add_le_add hInBd hsumG_bd
        _ = (((j + 1) * model.extG.n : ℕ) : ℤ) * B := by push_cast; ring
    have hInSumFits : Num.Fits 4 L (curInner + sum.gradient) := by
      refine fits_of_abs_le hInSumBd ?_
      have hle : (((j + 1) * model.extG.n : ℕ) : ℤ) ≤ ((maxEdges + maxPaths * model.extG.n : ℕ) : ℤ) := by
        have hnat : (j + 1) * model.extG.n ≤ maxEdges + maxPaths * model.extG.n :=
          le_trans (Nat.mul_le_mul_right _ (by omega)) (Nat.le_add_left _ _)
        exact_mod_cast hnat
      have hmul := mul_le_mul_of_nonneg_right hle hnum.1
      omega
    obtain ⟨bAdd1, hbAdd1, oAdd1, stAdd1, cAdd1, hrAdd1, hpostAdd1, hcAdd1⟩ :=
      hAdd [innerPtr, curHeap, L, heap1] s6.mem s6.pos ω
        (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl | rfl | rfl <;> omega)
        ⟨innerPtr, curHeap, L, heap1, rfl,
          ⟨innerPtr, curHeap, L, 0, heap1, rfl, by omega, by omega, by decide, hInAt1.1, hsumAt.1.1⟩,
          by simp only [heapArg, List.getLastD_cons, List.getLastD_nil, s6, s5, s4]; exact hz1.mono (by dsimp only [heap1]; omega),
          by change heap1 + L < 2 ^ w; omega⟩
    obtain ⟨hretAdd1, _, _, hfrAdd1, hzAdd1, hlistAdd1⟩ := hpostAdd1
    change oAdd1.value = heap1 + L at hretAdd1
    change ∀ x < heap1, stAdd1.mem x = after.mem x at hfrAdd1
    change ZeroFrom stAdd1.mem oAdd1.value at hzAdd1
    change ListAt stAdd1.mem heap1 (Num.digits 4 L (Num.unsignedVal after.mem innerPtr 4 L +
      Num.unsignedVal after.mem curHeap 4 L + 0)) at hlistAdd1
    have hadd1Val := Num.addCarry_value hlistAdd1
    have hInAt2 : PathIntAt stAdd1.mem heap1 4 L (curInner + sum.gradient) := by
      refine ⟨hadd1Val.1, ?_⟩
      rw [hadd1Val.2, hInAt1.2, hsumAt.1.2, Int.natCast_zero, add_zero, Num.wrap_of_fits hInSumFits]
    have hcAdd1' : cAdd1 ≤ 38 * L + 15 := hcAdd1
    let heap2 := heap1 + L
    have hheap2W : heap2 < 2 ^ w := by omega
    let s7 : State := { stAdd1 with regs := Function.update s6.regs 12 heap2 }
    let s8 : State := { s7 with regs := Function.update s7.regs 10 heap1 }
    let s9 : State := { s8 with regs := Function.update s8.regs 17 heap2 }
    let s10 : State := { s9 with regs := Function.update s9.regs 16 (curHeap + L) }
    have r7 : Runs w p ω (.call 12 numAdd [.reg 10, .reg 16, .reg 8, .reg 12]) s6 .normal s7 (4 + cAdd1 + 1) :=
      runs_call_iff.mpr ⟨[innerPtr, curHeap, L, heap1], bAdd1, oAdd1, stAdd1, cAdd1,
        by simp [evalArgs, Expr.eval, s6, s5, s4, s3, s2, s1, hr10, hr8], hbAdd1, hrAdd1,
        rfl, by simp [s7, hretAdd1, heap2], by simp [argsSize, Expr.size]⟩
    have r8 : Runs w p ω (.assign 10 (.reg 17)) s7 .normal s8 2 :=
      runs_assign_iff.mpr ⟨heap1, by simp [Expr.eval, s7, s6], rfl, rfl, rfl⟩
    have r9 : Runs w p ω (.assign 17 (.reg 12)) s8 .normal s9 2 :=
      runs_assign_iff.mpr ⟨heap2, by simp [Expr.eval, s8, s7], rfl, rfl, rfl⟩
    have r10 : Runs w p ω (.assign 16 (.bin .add (.reg 16) (.reg 8))) s9 .normal s10 4 :=
      runs_assign_iff.mpr ⟨curHeap + L, by
        simp [Expr.eval, BinOp.eval, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr8, show curHeap + L < 2 ^ w by omega],
        rfl, rfl, rfl⟩
    -- Step 4: second `numAdd [normPtr, sumPtr + L, L, heap2]`
    have hNoAt2 : PathIntAt stAdd1.mem normPtr 4 L curNorm :=
      hNoAt1.congr fun i hi => hfrAdd1 (normPtr + i) (by omega)
    have hSumLenAt2 : PathIntAt stAdd1.mem (curHeap + L) 4 L sum.length :=
      hsumAt.2.1.congr fun i hi => hfrAdd1 (curHeap + L + i) (by omega)
    have hNoSumBd : |curNorm + sum.length| ≤ (((j + 1) * model.extG.n : ℕ) : ℤ) * B := by
      rw [hsn] at hsumL_bd
      calc |curNorm + sum.length| ≤ |curNorm| + |sum.length| := abs_add_le _ _
        _ ≤ ((j * model.extG.n : ℕ) : ℤ) * B + (model.extG.n : ℤ) * B := add_le_add hNoBd hsumL_bd
        _ = (((j + 1) * model.extG.n : ℕ) : ℤ) * B := by push_cast; ring
    have hNoSumFits : Num.Fits 4 L (curNorm + sum.length) := by
      refine fits_of_abs_le hNoSumBd ?_
      have hle : (((j + 1) * model.extG.n : ℕ) : ℤ) ≤ ((maxEdges + maxPaths * model.extG.n : ℕ) : ℤ) := by
        have hnat : (j + 1) * model.extG.n ≤ maxEdges + maxPaths * model.extG.n :=
          le_trans (Nat.mul_le_mul_right _ (by omega)) (Nat.le_add_left _ _)
        exact_mod_cast hnat
      have hmul := mul_le_mul_of_nonneg_right hle hnum.1
      omega
    obtain ⟨bAdd2, hbAdd2, oAdd2, stAdd2, cAdd2, hrAdd2, hpostAdd2, hcAdd2⟩ :=
      hAdd [normPtr, curHeap + L, L, heap2] s10.mem s10.pos ω
        (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl | rfl | rfl <;> omega)
        ⟨normPtr, curHeap + L, L, heap2, rfl,
          ⟨normPtr, curHeap + L, L, 0, heap2, rfl, by omega, by omega, by decide, hNoAt2.1, hSumLenAt2.1⟩,
          by dsimp only [heapArg, s10, s9, s8, s7, heap2]; rw [← hretAdd1]; exact hzAdd1,
          by change heap2 + L < 2 ^ w; omega⟩
    obtain ⟨hretAdd2, _, _, hfrAdd2, hzAdd2, hlistAdd2⟩ := hpostAdd2
    change oAdd2.value = heap2 + L at hretAdd2
    change ∀ x < heap2, stAdd2.mem x = stAdd1.mem x at hfrAdd2
    change ZeroFrom stAdd2.mem oAdd2.value at hzAdd2
    change ListAt stAdd2.mem heap2 (Num.digits 4 L (Num.unsignedVal stAdd1.mem normPtr 4 L +
      Num.unsignedVal stAdd1.mem (curHeap + L) 4 L + 0)) at hlistAdd2
    have hadd2Val := Num.addCarry_value hlistAdd2
    have hNoAt3 : PathIntAt stAdd2.mem heap2 4 L (curNorm + sum.length) := by
      refine ⟨hadd2Val.1, ?_⟩
      rw [hadd2Val.2, hNoAt2.2, hSumLenAt2.2, Int.natCast_zero, add_zero, Num.wrap_of_fits hNoSumFits]
    have hInAt3 : PathIntAt stAdd2.mem heap1 4 L (curInner + sum.gradient) :=
      hInAt2.congr fun i hi => hfrAdd2 (heap1 + i) (by omega)
    have hcAdd2' : cAdd2 ≤ 38 * L + 15 := hcAdd2
    let heap3 := heap2 + L
    let s11 : State := { stAdd2 with regs := Function.update s10.regs 12 heap3 }
    let s12 : State := { s11 with regs := Function.update s11.regs 11 heap2 }
    let s13 : State := { s12 with regs := Function.update s12.regs 13 (j + 1) }
    have r11 : Runs w p ω (.call 12 numAdd [.reg 11, .reg 16, .reg 8, .reg 12]) s10 .normal s11 (4 + cAdd2 + 1) :=
      runs_call_iff.mpr ⟨[normPtr, curHeap + L, L, heap2], bAdd2, oAdd2, stAdd2, cAdd2,
        by simp [evalArgs, Expr.eval, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr11, hr8],
        hbAdd2, hrAdd2, rfl, by simp [s11, hretAdd2, heap3], by simp [argsSize, Expr.size]⟩
    have r12 : Runs w p ω (.assign 11 (.reg 17)) s11 .normal s12 2 :=
      runs_assign_iff.mpr ⟨heap2, by simp [Expr.eval, s11, s10, s9], rfl, rfl, rfl⟩
    have r13 : Runs w p ω (.assign 13 (.bin .add (.reg 13) (.const 1))) s12 .normal s13 4 :=
      runs_assign_iff.mpr ⟨j + 1, by
        simp [Expr.eval, BinOp.eval, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1,
          hr13, hw1, show j + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
    -- Assemble one loop iteration
    have rBody : Runs w p ω
        ((.assign 14 (.bin .add (.load (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 13)))) (.const 1)) ;;
          .assign 15 (.bin .add (.load (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 13))) (.const 1))) (.const 1)) ;;
          .assign 16 (.reg 12) ;;
          .call 12 (opTree 3) [.reg 7, .reg 14, .reg 15, .reg 16] ;;
          .assign 12 (.bin .add (.reg 12) (.bin .mul (.const 2) (.reg 8))) ;;
          .assign 17 (.reg 12) ;;
          .call 12 numAdd [.reg 10, .reg 16, .reg 8, .reg 12] ;;
          .assign 10 (.reg 17) ;;
          .assign 17 (.reg 12) ;;
          .assign 16 (.bin .add (.reg 16) (.reg 8)) ;;
          .call 12 numAdd [.reg 11, .reg 16, .reg 8, .reg 12] ;;
          .assign 11 (.reg 17)) ;;
         .assign 13 (.bin .add (.reg 13) (.const 1))) st .normal s13 _ :=
      runs_seq_iff.mpr (Or.inr ⟨s12, _, 4,
        runs_seq_iff.mpr (Or.inr ⟨s1, 9, _, r1,
        runs_seq_iff.mpr (Or.inr ⟨s2, 11, _, r2,
        runs_seq_iff.mpr (Or.inr ⟨s3, 2, _, r3,
        runs_seq_iff.mpr (Or.inr ⟨s4, cTree, _, hrTree,
        runs_seq_iff.mpr (Or.inr ⟨s5, 6, _, r5,
        runs_seq_iff.mpr (Or.inr ⟨s6, 2, _, r6,
        runs_seq_iff.mpr (Or.inr ⟨s7, 4 + cAdd1 + 1, _, r7,
        runs_seq_iff.mpr (Or.inr ⟨s8, 2, _, r8,
        runs_seq_iff.mpr (Or.inr ⟨s9, 2, _, r9,
        runs_seq_iff.mpr (Or.inr ⟨s10, 4, _, r10,
        runs_seq_iff.mpr (Or.inr ⟨s11, 4 + cAdd2 + 1, 2, r11, r12, rfl⟩), rfl⟩), rfl⟩), rfl⟩),
          rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), r13, rfl⟩)
    -- Transfer memory invariants to `s13`
    have hmem_lt (a : ℕ) (ha : a < workHeap) (hnf : ¬ Rtree.foot tok.treeHeap treeTok a) :
        s13.mem a = st.mem a :=
      (hfrAdd2 a (by omega)).trans ((hfrAdd1 a (by omega)).trans (hfr1 a (by omega) hnf))
    have hrep2 : Rtree.rep tok.treeHeap s1Tree treeTok1 s13.mem := by
      have hloc := pathRep_local 4 L LinkCut.PathProg.pathC tok.treeHeap s1Tree treeTok1 after.mem s13.mem
        (fun a ha => by
          have haW := hfoot a ((hfoot1_eq a).mp ha)
          exact ((hfrAdd2 a (by omega)).trans (hfrAdd1 a (by omega))).symm)
      exact hloc.1 hrep1
    have hphi2 : Rtree.phi tok.treeHeap treeTok1 s13.mem = Rtree.phi tok.treeHeap treeTok1 after.mem := by
      have hloc := pathRep_local 4 L LinkCut.PathProg.pathC tok.treeHeap s1Tree treeTok1 after.mem s13.mem
        (fun a ha => by
          have haW := hfoot a ((hfoot1_eq a).mp ha)
          exact ((hfrAdd2 a (by omega)).trans (hfrAdd1 a (by omega))).symm)
      exact hloc.2.symm
    have hslots13 : ∀ e ∈ F.E, s13.mem (tok.slots + e) = st.mem (tok.slots + e) := fun e he =>
      hmem_lt _ (hslotsOk e he).2 (hslotsOk e he).1
    have hnames13 : ∀ sl < 2 * model.extG.n, s13.mem (tok.names + sl) = st.mem (tok.names + sl) := fun sl hsl =>
      hmem_lt _ (hnamesOk sl hsl).2 (hnamesOk sl hsl).1
    have hns13 : TreeEditNamedSlots s1Tree trees1 F (fun ei => s13.mem (tok.slots + ei))
        (fun sl => s13.mem (tok.names + sl)) := by
      refine ⟨fun e he => ?_, fun sl hsl hs => ?_, fun e he => ?_⟩
      · rw [hslots13 e he]
        obtain ⟨h1, h2, h3⟩ := hns1.forward e he
        have hslLt : st.mem (tok.slots + e) < 2 * model.extG.n := by
          unfold isEdgeSlot at h2; rw [hnextN, hsn] at h2; omega
        rw [hnames13 _ hslLt]
        exact ⟨h1, h2, h3⟩
      · have hslLt : sl < 2 * model.extG.n := by
          unfold isEdgeSlot at hs; rw [hnextN, hsn] at hs; omega
        rw [hnames13 sl hslLt]
        obtain ⟨heE, hse⟩ := hns1.inverse sl hsl hs
        rw [hslots13 _ heE]
        exact ⟨heE, hse⟩
      · rw [hslots13 e he]; exact hns1.endpoints e he
    have hor13 : ∀ e ∈ E0, ∀ val : PathEdgeValue,
        (s13.mem (tok.slots + e), some val) ∈ forestPairs pathPayload s1Tree.splay trees1 →
        (val.originalGradient : ℝ) / (2 : ℝ) ^ P = model.extg (model.intToExt e) ∧
        (val.length : ℝ) / (2 : ℝ) ^ P = model.extℓ (model.intToExt e) ∧
        (val.forward = true →
          inducedSubPar pathPayload s1Tree.splay trees1 (vid (F.head e)) = s13.mem (tok.slots + e) ∧
          inducedSubPar pathPayload s1Tree.splay trees1 (s13.mem (tok.slots + e)) = vid (F.tail e)) ∧
        (val.forward = false →
          inducedSubPar pathPayload s1Tree.splay trees1 (vid (F.tail e)) = s13.mem (tok.slots + e) ∧
          inducedSubPar pathPayload s1Tree.splay trees1 (s13.mem (tok.slots + e)) = vid (F.head e)) := by
      intro e he val hp
      have heF : e ∈ F.E := Finset.inter_subset_left he
      rw [hslots13 e heF] at hp ⊢
      obtain ⟨val0, hp0⟩ := hhasVal e he
      obtain ⟨hg0, hl0, hft0, hff0⟩ := hor e he val0 hp0
      obtain ⟨val1, hp1, _, hgr1, hlen1, _, hft1, hff1⟩ := hor1 e heF val0 hp0 ⟨hft0, hff0⟩
      have heq := forestPairs_val_unique hW1 hp hp1
      subst heq
      exact ⟨by rw [hgr1]; exact hg0, by rw [hlen1]; exact hl0, hft1, hff1⟩
    have hhasVal13 : ∀ e ∈ E0, ∃ val : PathEdgeValue,
        (s13.mem (tok.slots + e), some val) ∈ forestPairs pathPayload s1Tree.splay trees1 := by
      intro e he
      have heF : e ∈ F.E := Finset.inter_subset_left he
      rw [hslots13 e heF]
      obtain ⟨val0, hp0⟩ := hhasVal e he
      obtain ⟨_, _, hft0, hff0⟩ := hor e he val0 hp0
      obtain ⟨val1, hp1, _⟩ := hor1 e heF val0 hp0 ⟨hft0, hff0⟩
      exact ⟨val1, hp1⟩
    have hnoVal13 : ∀ e ∈ F.E, e ∉ E0 → ∀ val : PathEdgeValue,
        (s13.mem (tok.slots + e), some val) ∉ forestPairs pathPayload s1Tree.splay trees1 := by
      intro e heF hnot val hp
      rw [hslots13 e heF] at hp
      obtain ⟨val0, hp0⟩ := hpreSome1 _ val hp
      exact hnoVal e heF hnot val0 hp0
    have hends13 : PathEndpointsAt s13.mem pathsBase paths := fun idx hidx => by
      have hm1 := hmem_lt (pathsBase + 2 * idx) (by omega) (hsepP (2 * idx) (by omega))
      have hm2 := hmem_lt (pathsBase + 2 * idx + 1) (by omega) (by
        rw [Nat.add_assoc]; exact hsepP (2 * idx + 1) (by omega))
      exact ⟨hm1.trans (hends idx hidx).1, hm2.trans (hends idx hidx).2⟩
    -- Recurse on `rem`
    obtain ⟨out, cRest, s', trees', depth', treeTok', addGradR, addLenR, innerPtr', normPtr', curHeap',
        hrRest, hregsRest, hr10', hr11', hr12', hInPos', hNoPos', hInLe', hNoLe', hHeapLo', hHeapHi',
        hInAt', hNoAt', haddGR, haddLR, hInBd', hNoBd', hsn', hW', hnum', hrep', hns', hpreSomeRest, horRest,
        hz', hfrRest, hcRest⟩ :=
      ih s13 s1Tree trees1 depth1 treeTok1 (curInner + sum.gradient) (curNorm + sum.length)
        heap1 heap2 heap3 (by omega) rfl
        (by simp [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr3])
        (by simp [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr4])
        (by simp [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr5])
        (by simp [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr7])
        (by simp [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr8])
        (by simp [s13, s12, s11, s10, s9, s8]) (by simp [s13, s12])
        (by simp [s13, s12, s11]) (by simp [s13, hremNext])
        htreeW (hnextN.trans hsn) (hnextN.symm ▸ h2nW) hW1 hnum1 hrep2
        (fun a ha => hfoot a ((hfoot1_eq a).mp ha))
        (fun x hx hf => hsepP x hx ((hfoot1_eq _).mp hf))
        hends13 hpathsOk hF hV hfresh hns13
        (fun e he => ⟨fun hf => (hslotsOk e he).1 ((hfoot1_eq _).mp hf), (hslotsOk e he).2⟩)
        (fun sl hsl => ⟨fun hf => (hnamesOk sl hsl).1 ((hfoot1_eq _).mp hf), (hnamesOk sl hsl).2⟩)
        hor13 hhasVal13 hnoVal13 (Or.inr (by omega)) (Or.inr (by omega))
        (by dsimp only [heap3, heap2]; omega) (by dsimp only [heap3, heap2]; omega)
        (by dsimp only [heap3, heap2, heap1]; omega)
        (by rw [hremNext]; dsimp only [heap3, heap2]; omega)
        hInAt3 hNoAt3 (by rw [hremNext]; exact hInSumBd) (by rw [hremNext]; exact hNoSumBd)
        (by dsimp only [s13, s12, s11, heap3]; rw [← hretAdd2]; exact hzAdd2)
    -- Loop step
    have hcond1 : (Expr.bin .lt (.reg 13) (.reg 4)).eval w st = some 1 := by
      simp [Expr.eval, BinOp.eval, hr13, hr4, hjLt, hw1]
    have hrLoop : Runs w p ω _ st .normal out
        (3 + (9 + (11 + (2 + (cTree + (6 + (2 + (4 + cAdd1 + 1 + (2 + (2 + (4 + (4 + cAdd2 + 1 + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1 + 4 + 1) + cRest + 1) :=
      runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, s13, _, cRest, hcond1, by decide, rBody, hrRest,
        by simp [Expr.size]⟩))
    -- Combine `sum.gradient + addGradR` and `sum.length + addLenR`
    have hdropSplit : paths.drop j = (paths[j]'hjLt) :: paths.drop (j + 1) :=
      List.drop_eq_getElem_cons hjLt
    have hsumG_div : (sum.gradient : ℝ) / (2 : ℝ) ^ P =
        ∑ e ∈ E0, model.extg (model.intToExt e) * walkFlow (F.forestPath u v) e := by
      rw [hsumG_eq, Finset.sum_div]
      refine Finset.sum_congr rfl fun e he => ?_
      have hge : (gInt e : ℝ) / (2 : ℝ) ^ P = model.extg (model.intToExt e) := by
        dsimp only [gInt]; rw [dite_eq_left_of_eq_true (eq_true he)]
        exact (hor e he _ (hhasVal e he).choose_spec).1
      rw [mul_div_right_comm, hge]
    have hsumL_div : (sum.length : ℝ) / (2 : ℝ) ^ P =
        ∑ e ∈ E0, model.extℓ (model.intToExt e) * |walkFlow (F.forestPath u v) e| := by
      rw [hsumL_eq, Finset.sum_div]
      refine Finset.sum_congr rfl fun e he => ?_
      have hle : (ℓInt e : ℝ) / (2 : ℝ) ^ P = model.extℓ (model.intToExt e) := by
        dsimp only [ℓInt]; rw [dite_eq_left_of_eq_true (eq_true he)]
        exact (hor e he _ (hhasVal e he).choose_spec).2.1
      rw [mul_div_right_comm, hle]
    have htotG : ((sum.gradient + addGradR : ℤ) : ℝ) / (2 : ℝ) ^ P =
        ((paths.drop j).map fun q => ∑ e ∈ E0,
          model.extg (model.intToExt e) * walkFlow (F.forestPath q.1 q.2) e).sum := by
      rw [hdropSplit, List.map_cons, List.sum_cons, Int.cast_add, add_div, hsumG_div, ← hremNext, haddGR]
    have htotL : ((sum.length + addLenR : ℤ) : ℝ) / (2 : ℝ) ^ P =
        ((paths.drop j).map fun q => ∑ e ∈ E0,
          model.extℓ (model.intToExt e) * |walkFlow (F.forestPath q.1 q.2) e|).sum := by
      rw [hdropSplit, List.map_cons, List.sum_cons, Int.cast_add, add_div, hsumL_div, ← hremNext, haddLR]
    -- Re-express `hns'` and `horRest` in terms of `st.mem`
    have hnsFin : TreeEditNamedSlots s' trees' F (fun ei => st.mem (tok.slots + ei))
        (fun sl => st.mem (tok.names + sl)) := by
      refine ⟨fun e he => ?_, fun sl hsl hs => ?_, fun e he => ?_⟩
      · obtain ⟨h1, h2, h3⟩ := hns'.forward e he
        rw [hslots13 e he] at h1 h2 h3
        have hslLt : st.mem (tok.slots + e) < 2 * model.extG.n := by
          unfold isEdgeSlot at h2; rw [hsn'] at h2; omega
        rw [hnames13 _ hslLt] at h3
        exact ⟨h1, h2, h3⟩
      · have hslLt : sl < 2 * model.extG.n := by
          unfold isEdgeSlot at hs; rw [hsn'] at hs; omega
        obtain ⟨heE, hse⟩ := hns'.inverse sl hsl hs
        rw [hnames13 sl hslLt] at heE hse
        rw [hslots13 _ heE] at hse
        exact ⟨heE, hse⟩
      · have he' := hns'.endpoints e he
        rw [hslots13 e he] at he'; exact he'
    have horFin : ∀ e ∈ E0, ∀ val : PathEdgeValue,
        (st.mem (tok.slots + e), some val) ∈ forestPairs pathPayload s.splay trees →
        ∃ val' : PathEdgeValue,
          (st.mem (tok.slots + e), some val') ∈ forestPairs pathPayload s'.splay trees' ∧
          val'.originalFlow = val.originalFlow ∧ val'.originalGradient = val.originalGradient ∧
          val'.length = val.length ∧ val'.detector = val.detector ∧
          (val'.forward = true →
            inducedSubPar pathPayload s'.splay trees' (vid (F.head e)) = st.mem (tok.slots + e) ∧
            inducedSubPar pathPayload s'.splay trees' (st.mem (tok.slots + e)) = vid (F.tail e)) ∧
          (val'.forward = false →
            inducedSubPar pathPayload s'.splay trees' (vid (F.tail e)) = st.mem (tok.slots + e) ∧
            inducedSubPar pathPayload s'.splay trees' (st.mem (tok.slots + e)) = vid (F.head e)) := by
      intro e he val hp
      have heF : e ∈ F.E := Finset.inter_subset_left he
      obtain ⟨_, _, hft0, hff0⟩ := hor e he val hp
      obtain ⟨val1, hp1, hfl1, hgr1, hlen1, hdet1, _⟩ := hor1 e heF val hp ⟨hft0, hff0⟩
      rw [← hslots13 e heF] at hp1
      obtain ⟨val', hp', hfl', hgr', hlen', hdet', hft', hff'⟩ := horRest e he val1 hp1
      rw [hslots13 e heF] at hp' hft' hff'
      exact ⟨val', hp', hfl'.trans hfl1, hgr'.trans hgr1, hlen'.trans hlen1, hdet'.trans hdet1, hft', hff'⟩
    -- Cost accounting
    have htreeBud : pathTreeBudget LinkCut.PathProg.pathC L s.n ≤
        25 * (LinkCut.PathProg.pathC * (L + 1) ^ 2) * (4 * L + 1) := by
      unfold pathTreeBudget
      apply Nat.mul_le_mul_left
      rw [hsn]; omega
    have hargSz : argsSize [.reg 7, .reg 14, .reg 15, .reg 16] = 4 := by simp [argsSize, Expr.size]
    rw [hargSz] at hcTree
    refine ⟨out, _, s', trees', depth', treeTok', sum.gradient + addGradR, sum.length + addLenR,
      innerPtr', normPtr', curHeap', hrLoop,
      fun r hr => (hregsRest r hr).trans (by simp [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1,
        Function.update_of_ne (show r ≠ 10 by omega), Function.update_of_ne (show r ≠ 11 by omega),
        Function.update_of_ne (show r ≠ 12 by omega), Function.update_of_ne (show r ≠ 13 by omega),
        Function.update_of_ne (show r ≠ 14 by omega), Function.update_of_ne (show r ≠ 15 by omega),
        Function.update_of_ne (show r ≠ 16 by omega), Function.update_of_ne (show r ≠ 17 by omega)]),
      hr10', hr11', hr12', hInPos', hNoPos', hInLe', hNoLe',
      le_trans (by dsimp only [heap3, heap2, heap1]; omega) hHeapLo', hHeapHi',
      by rw [← add_assoc]; exact hInAt', by rw [← add_assoc]; exact hNoAt',
      htotG, htotL, by rw [← add_assoc]; exact hInBd', by rw [← add_assoc]; exact hNoBd',
      hsn', hW', hnum', hrep', hnsFin,
      fun sl val hp => let ⟨v1, hp1⟩ := hpreSomeRest sl val hp; hpreSome1 sl v1 hp1,
      horFin, hz',
      fun a ha hnf => (hfrRest a ha (fun hf => hnf ((hfoot1_eq a).mp hf))).trans (hmem_lt a ha hnf),
      ?_⟩
    rw [Nat.add_mul, one_mul]
    dsimp only [Rtree, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1] at hcTree hcRest hphi2 ⊢
    rw [hphi2] at hcRest
    omega


end MinCostFlow.MinRatio
