module

public import MinCostFlow.MinRatio.WireEvalPaths
public import MinCostFlow.MinRatio.WireEvalEdges
import WordRAM.Tactic

/-!
# Cycle route evaluator (`OrdCycleRouteEvalSpecW`)

Assembles `evalPathsLoop_runs` (`WireEvalPaths.lean`), `evalEdgesLoop_runs` and
`solverStateRep_after_eval` (`WireEvalEdges.lean`), `evalCopyLoop_runs` (`WireEvalBase.lean`),
and `evalCycle_route_algebra` (`WireEvalMath.lean`) to prove `evalCycleBody_meets_spec`:
`evalCycleBody` implements `OrdCycleRouteEvalSpecW`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut LinkCut.PathTree LinkCut.PathProg Chain

/-! ### Main theorem: `evalCycleBody_meets_spec` -/

/-- **The cycle route evaluator meets `OrdCycleRouteEvalSpecW`.** -/
theorem evalCycleBody_meets_spec
    {w L P m V psi k epsExp drainUnit initTree evalCycleProc numAdd numSub maxEdges maxPaths : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)}
    {opTree : ℕ → ℕ} {p : Program}
    (hlocalCore : Rcore.Local)
    (hfmt4 : fmt.limbBits = 4)
    (hw10 : 10 ≤ w)
    (hAt : p.procs[evalCycleProc]? = some (evalCycleBody (opTree 3) numAdd numSub))
    (hTreeImpl : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).Implements w p initTree opTree
      (pathTreeMachineContract fmt L LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc L)))
    (hAdd : MeetsContract w p numAdd (Num.addContract w 4))
    (hSub : MeetsContract w p numSub (Num.subtractContract w 4)) :
    OrdCycleRouteEvalSpecW w L P m V psi k epsExp drainUnit cfg Rcore p evalCycleProc
      (evalCycleSpace L maxEdges maxPaths) (evalCycleBudget L maxEdges maxPaths) maxEdges maxPaths := by
  refine ⟨evalCycleBody (opTree 3) numAdd numSub, hAt, ?_⟩
  intro root edgesBase pathsBase workHeap pos ω mem model tok B R edges paths Δ
    hrep hnum hoff hBd hcapE hcapT hlogW hlenNN hedMax hptMax hnodup hEdAt hPtAt hRoute
    hedEnd hptEnd hnfEd hnfPt hbelow hz hroom
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
  let F := model.chain.toTreeChain.chainTree
  have hrep0 := hrep
  obtain ⟨hrootDir, hdetect, hnumHdr, _, hfresh, _, _, _, _, _, htn, hlct, htrep, hedgeAcc,
    _, _, _, _, hwire, htags⟩ := hrep
  obtain ⟨hOwn, t1, t2, _, _, _, _, _, _, t9, t10, _, _, t13, _, _, t16, t1718, _⟩ := htags
  have hw1024 : 1024 ≤ 2 ^ w := by
    calc (1024 : ℕ) = 2 ^ 10 := by decide
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw10
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw5 : 5 < 2 ^ w := by omega
  have hw10W : 10 < 2 ^ w := by omega
  have hworkW : workHeap < 2 ^ w := by dsimp only [evalCycleSpace] at hroom; omega
  have hLW : L < 2 ^ w := by dsimp only [evalCycleSpace] at hroom; omega
  have h2LW : 2 * L < 2 ^ w := by dsimp only [evalCycleSpace] at hroom; omega
  have hworkLW : workHeap + L < 2 ^ w := by dsimp only [evalCycleSpace] at hroom; omega
  have hwork2LW : workHeap + 2 * L < 2 ^ w := by dsimp only [evalCycleSpace] at hroom; omega
  have hroot0 : mem root = tok.handle := by simpa using hrootDir 0 (by simp)
  have hroot10 : mem (root + 10) = tok.edgeRecords := by simpa using hrootDir 10 (by simp)
  have hhandle0 : mem tok.handle = tok.treeHeap := by simpa using hdetect 0 (by simp)
  have hhandle5 : mem (tok.handle + 5) = L := by simpa [Nat.add_assoc] using hnumHdr 0 (by simp)
  have hroot10W : root + 10 < 2 ^ w :=
    lt_trans (hbelow _ (Or.inl (hOwn _ (by rw [t1 10 (by omega)]; decide)))) hworkW
  have hh5W : tok.handle + 5 < 2 ^ w :=
    lt_trans (hbelow _ (Or.inl (hOwn _ (by rw [t2 5 (by omega)]; decide)))) hworkW
  have htreeFoot0 : Rtree.foot tok.treeHeap tok.treeTok tok.treeHeap := by
    refine ⟨le_rfl, ?_⟩; unfold arenaEnd arenaNb; omega
  have htreeW : tok.treeHeap < 2 ^ w :=
    lt_trans (hbelow _ (Or.inr (Or.inl htreeFoot0))) hworkW
  have h2nW : 2 * tok.tree.n + 1 < 2 ^ w := by
    have ha : tok.treeHeap + (2 * tok.tree.n + 1) < arenaEnd tok.treeHeap tok.tree.n L := by
      unfold arenaEnd arenaNb recW treeLimbs; omega
    have hf : Rtree.foot tok.treeHeap tok.treeTok (tok.treeHeap + (2 * tok.tree.n + 1)) := by
      change tok.treeHeap ≤ _ ∧ _ < arenaEnd tok.treeHeap tok.treeTok.1.n L
      rw [htrep.1]; exact ⟨by omega, ha⟩
    have := hbelow _ (Or.inr (Or.inl hf))
    omega
  -- Preamble setup
  let s0 := startState [root, edgesBase, edges.length, pathsBase, paths.length, workHeap] mem pos
  let s1 : State := { s0 with regs := Function.update s0.regs 6 tok.handle }
  let s2 : State := { s1 with regs := Function.update s1.regs 7 tok.treeHeap }
  let s3 : State := { s2 with regs := Function.update s2.regs 8 L }
  let s4 : State := { s3 with regs := Function.update s3.regs 9 tok.edgeRecords }
  let s5 : State := { s4 with regs := Function.update s4.regs 10 workHeap }
  let s6 : State := { s5 with regs := Function.update s5.regs 11 (workHeap + L) }
  let s7 : State := { s6 with regs := Function.update s6.regs 12 (workHeap + 2 * L) }
  let s8 : State := { s7 with regs := Function.update s7.regs 13 0 }
  have r1 : Runs w p ω (.assign 6 (.load (.reg 0))) s0 .normal s1 3 :=
    runs_assign_iff.mpr ⟨tok.handle, by simp [Expr.eval, s0, startState, hroot0], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 7 (.load (.reg 6))) s1 .normal s2 3 :=
    runs_assign_iff.mpr ⟨tok.treeHeap, by simp [Expr.eval, s1, s0, startState, hhandle0], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 6) (.const 5)))) s2 .normal s3 5 :=
    runs_assign_iff.mpr ⟨L, by simp [Expr.eval, BinOp.eval, s2, s1, s0, startState, hw5, hh5W, hhandle5], rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 0) (.const 10)))) s3 .normal s4 5 :=
    runs_assign_iff.mpr ⟨tok.edgeRecords, by
      simp [Expr.eval, BinOp.eval, s3, s2, s1, s0, startState, hw10W, hroot10W, hroot10], rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 10 (.reg 5)) s4 .normal s5 2 :=
    runs_assign_iff.mpr ⟨workHeap, by simp [Expr.eval, s4, s3, s2, s1, s0, startState], rfl, rfl, rfl⟩
  have r6 : Runs w p ω (.assign 11 (.bin .add (.reg 5) (.reg 8))) s5 .normal s6 4 :=
    runs_assign_iff.mpr ⟨workHeap + L, by
      simp [Expr.eval, BinOp.eval, s5, s4, s3, s2, s1, s0, startState, hworkLW], rfl, rfl, rfl⟩
  have r7 : Runs w p ω (.assign 12 (.bin .add (.reg 5) (.bin .mul (.const 2) (.reg 8)))) s6 .normal s7 6 :=
    runs_assign_iff.mpr ⟨workHeap + 2 * L, by
      simp [Expr.eval, BinOp.eval, s6, s5, s4, s3, s2, s1, s0, startState, hw2, h2LW, hwork2LW], rfl, rfl, rfl⟩
  have r8 : Runs w p ω (.assign 13 (.const 0)) s7 .normal s8 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  -- Loop 1 (`evalPathsLoop`) over `E0 = F.E ∩ (model.chain.G 0).E`
  let E0 := F.E ∩ (model.chain.G 0).E
  have horInit : ∀ e ∈ E0, ∀ val : PathEdgeValue,
      (mem (tok.slots + e), some val) ∈ forestPairs pathPayload tok.tree.splay tok.trees →
      (val.originalGradient : ℝ) / (2 : ℝ) ^ P = model.extg (model.intToExt e) ∧
      (val.length : ℝ) / (2 : ℝ) ^ P = model.extℓ (model.intToExt e) ∧
      (val.forward = true →
        inducedSubPar pathPayload tok.tree.splay tok.trees (vid (F.head e)) = mem (tok.slots + e) ∧
        inducedSubPar pathPayload tok.tree.splay tok.trees (mem (tok.slots + e)) = vid (F.tail e)) ∧
      (val.forward = false →
        inducedSubPar pathPayload tok.tree.splay tok.trees (vid (F.tail e)) = mem (tok.slots + e) ∧
        inducedSubPar pathPayload tok.tree.splay tok.trees (mem (tok.slots + e)) = vid (F.head e)) := by
    intro e he val hp
    obtain ⟨heF, heG⟩ := Finset.mem_inter.mp he
    obtain ⟨heq, heExt⟩ := hfresh.hRight e heG
    have hgl := hwire.2.2.2.2 (model.intToExt e) heExt
    dsimp only at hgl
    rw [heq, ite_eq_left heF] at hgl
    exact hgl val hp
  have hhasValInit : ∀ e ∈ E0, ∃ val : PathEdgeValue,
      (mem (tok.slots + e), some val) ∈ forestPairs pathPayload tok.tree.splay tok.trees := by
    intro e he
    obtain ⟨heF, heG⟩ := Finset.mem_inter.mp he
    obtain ⟨heq, heExt⟩ := hfresh.hRight e heG
    have hbr := (hedgeAcc.1 (model.intToExt e) heExt).2.2
    rw [heq, ite_eq_left heF] at hbr
    obtain ⟨_, _, _, _, val, _, hp, _⟩ := hbr
    exact ⟨val, hp⟩
  have hnoValInit : ∀ e ∈ F.E, e ∉ E0 → ∀ val : PathEdgeValue,
      (mem (tok.slots + e), some val) ∉ forestPairs pathPayload tok.tree.splay tok.trees := by
    intro e heF hnot val hp
    obtain ⟨_, hsl, hnm⟩ := hwire.2.2.2.1.forward e heF
    obtain ⟨_, _, _, heExt, he2i⟩ := hedgeAcc.2 _ val hsl hp
    rw [hnm] at heExt he2i
    have heG : e ∈ (model.chain.G 0).E := by
      rw [← he2i, hfresh.hE]; exact Finset.mem_image_of_mem _ heExt
    exact hnot (Finset.mem_inter.mpr ⟨heF, heG⟩)
  obtain ⟨stP, cP, s', trees', depth', treeTok', treeGrad, treeLen, innerPtr1, normPtr1, heap1,
      hrP, hregsP, hr10P, hr11P, hr12P, hInPos1, hNoPos1, hInLe1, hNoLe1, hHeap1Lo, hHeap1Hi,
      hInAt1, hNoAt1, htreeG_eq, htreeL_eq, hInBd1, hNoBd1, hsn', hW', hnum', hrepTree1,
      hns1, hpreSome1, hor1, hzP, hfrP, hcP⟩ :=
    evalPathsLoop_runs (m := m) (V := V) (psi := psi) (k := k) (epsExp := epsExp)
      (drainUnit := drainUnit) (root := root)
      hfmt4 hTreeImpl hAdd hw10 (Or.inr trivial) hptMax hptEnd hcapE hcapT hlogW hroom
      paths.length s8 tok.tree tok.trees tok.depth tok.treeTok 0 0 workHeap (workHeap + L)
      (workHeap + 2 * L) le_rfl rfl
      (by simp [s8, s7, s6, s5, s4, s3, s2, s1, s0, startState])
      (by simp [s8, s7, s6, s5, s4, s3, s2, s1, s0, startState])
      (by simp [s8, s7, s6, s5, s4, s3, s2, s1, s0, startState])
      (by simp [s8, s7, s6, s5, s4, s3, s2]) (by simp [s8, s7, s6, s5, s4, s3])
      (by simp [s8, s7, s6, s5]) (by simp [s8, s7, s6]) (by simp [s8, s7])
      (by simp [s8]) htreeW htn h2nW hlct hnum htrep
      (fun a ha => hbelow a (Or.inr (Or.inl ha)))
      (fun x hx hf => hnfPt x hx (Or.inr (Or.inl hf)))
      hPtAt hRoute.2.1 hwire.2.2.1.1 hwire.2.2.1.2 hfresh hwire.2.2.2.1
      (fun e he => ⟨fun hf => by have := t9 e (hwire.2.2.1.2 e he).1; have := t16 _ hf; omega,
        hbelow _ (Or.inl (hOwn _ (by rw [t9 e (hwire.2.2.1.2 e he).1]; decide)))⟩)
      (fun sl hsl => ⟨fun hf => by have := t10 sl (htn.symm ▸ hsl); have := t16 _ hf; omega,
        hbelow _ (Or.inl (hOwn _ (by rw [t10 sl (htn.symm ▸ hsl)]; decide)))⟩)
      horInit hhasValInit hnoValInit (Or.inl rfl) (Or.inl rfl) (by omega) (by omega) le_rfl (by simp)
      (pathIntAt_zero hz le_rfl) (pathIntAt_zero hz (by omega))
      (by simp) (by simp) (hz.mono (by omega))
  simp only [Nat.sub_self, List.drop_zero, zero_add] at hInAt1 hNoAt1 htreeG_eq htreeL_eq hInBd1 hNoBd1
  -- Loop 2 (`evalEdgesLoop`)
  let s9 : State := { stP with regs := Function.update stP.regs 13 0 }
  have r9 : Runs w p ω (.assign 13 (.const 0)) stP .normal s9 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hEdAtP : ExplicitEdgesAt stP.mem edgesBase edges :=
    hEdAt.congr fun y hlo hhi =>
      hfrP y (by omega) (fun hf => by
        have hy : edgesBase + (y - edgesBase) = y := by omega
        rw [← hy] at hf; exact hnfEd (y - edgesBase) (by omega) (Or.inr (Or.inl hf)))
  have hEdOkP : ∀ x ∈ edges,
      tok.edgeRecords + x.1 < workHeap ∧
      stP.mem (tok.edgeRecords + x.1) + 2 + 4 * L ≤ workHeap ∧
      ∃ val : PathEdgeValue,
        PathEdgeAt stP.mem (stP.mem (tok.edgeRecords + x.1)) 4 L (some val) ∧
        val.forward = true ∧
        (val.originalGradient : ℝ) / (2 : ℝ) ^ P = model.extg (model.intToExt x.1) ∧
        (val.length : ℝ) / (2 : ℝ) ^ P = model.extℓ (model.intToExt x.1) ∧
        |val.gradient| ≤ B ∧ |val.length| ≤ B := by
    intro x hx
    obtain ⟨hxG, hxNotF⟩ := Finset.mem_sdiff.mp (hRoute.1 x hx)
    obtain ⟨heq, heExt⟩ := hfresh.hRight x.1 hxG
    have heiCap := (hedgeAcc.1 (model.intToExt x.1) heExt).1
    rw [heq] at heiCap
    have herLt : tok.edgeRecords + x.1 < workHeap :=
      hbelow _ (Or.inl (hOwn _ (by rw [t13 x.1 heiCap]; decide)))
    have hptrEq : stP.mem (tok.edgeRecords + x.1) = mem (tok.edgeRecords + x.1) :=
      hfrP _ herLt (fun hf => by have := t13 x.1 heiCap; have := t16 _ hf; omega)
    have hrecLt : mem (tok.edgeRecords + x.1) + 2 + 4 * L ≤ workHeap := by
      have hlast := (t1718 (model.intToExt x.1) heExt).2 (heq.symm ▸ hxNotF) (1 + 4 * L) (by omega)
      rw [heq] at hlast
      have hlt := hbelow _ (Or.inl (hOwn _ (by rw [hlast]; decide)))
      omega
    have hbr := (hedgeAcc.1 (model.intToExt x.1) heExt).2.2
    rw [heq, ite_eq_right hxNotF] at hbr
    obtain ⟨_, val, _, hrecAt, _⟩ := hbr
    have hgl := hwire.2.2.2.2 (model.intToExt x.1) heExt
    dsimp only at hgl; rw [heq, ite_eq_right hxNotF] at hgl
    obtain ⟨hfwd, hgr, hln⟩ := hgl val hrecAt
    have hbd := hBd (model.intToExt x.1) heExt (heq.symm ▸ hxNotF) val (heq.symm ▸ hrecAt)
    rw [hptrEq]
    refine ⟨herLt, hrecLt, val, hrecAt.congr (fun z zlo zhi => by
      have ht18 : tok.tag z = 18 := by
        have hz_eq : mem (tok.edgeRecords + x.1) + (z - mem (tok.edgeRecords + x.1)) = z := by omega
        rw [← hz_eq]
        have := (t1718 (model.intToExt x.1) heExt).2 (heq.symm ▸ hxNotF) (z - mem (tok.edgeRecords + x.1)) (by omega)
        rwa [heq] at this
      exact hfrP z (hbelow z (Or.inl (hOwn z (by rw [ht18]; decide))))
        (fun hf => by have := t16 z hf; omega)), hfwd, hgr, hln, hbd.1, hbd.2.1⟩
  have hInBd1' : |treeGrad| ≤ ((maxPaths * model.extG.n + 0 : ℕ) : ℤ) * B := by
    have hle : ((paths.length * model.extG.n : ℕ) : ℤ) ≤ ((maxPaths * model.extG.n + 0 : ℕ) : ℤ) := by
      exact_mod_cast (show paths.length * model.extG.n ≤ maxPaths * model.extG.n + 0 by
        rw [Nat.add_zero]; exact Nat.mul_le_mul_right _ hptMax)
    exact hInBd1.trans (mul_le_mul_of_nonneg_right hle hnum.1)
  have hNoBd1' : |treeLen| ≤ ((maxPaths * model.extG.n + 0 : ℕ) : ℤ) * B := by
    have hle : ((paths.length * model.extG.n : ℕ) : ℤ) ≤ ((maxPaths * model.extG.n + 0 : ℕ) : ℤ) := by
      exact_mod_cast (show paths.length * model.extG.n ≤ maxPaths * model.extG.n + 0 by
        rw [Nat.add_zero]; exact Nat.mul_le_mul_right _ hptMax)
    exact hNoBd1.trans (mul_le_mul_of_nonneg_right hle hnum.1)
  obtain ⟨stE, cE, edgeGrad, edgeLen, innerPtr2, normPtr2, heap2, hrE,
      hr5E, hr8E, hr10E, hr11E, hr12E, hInPos2, hNoPos2, hInLe2, hNoLe2, hHeap2Lo, hHeap2Hi,
      hInAt2, hNoAt2, hedgeG_eq, hedgeL_eq, hzE, hfrE, hcE⟩ :=
    evalEdgesLoop_runs (heapAfterPaths := heap1) hAdd hSub hw10 hnum.1 hedMax hedEnd hHeap1Lo
      (hHeap1Hi.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hptMax) _)) hcapE hroom
      edges.length s9 treeGrad treeLen innerPtr1 normPtr1 heap1 le_rfl
      (by simp [s9, hregsP 1 (by decide), s8, s7, s6, s5, s4, s3, s2, s1, s0, startState])
      (by simp [s9, hregsP 2 (by decide), s8, s7, s6, s5, s4, s3, s2, s1, s0, startState])
      (by simp [s9, hregsP 5 (by decide), s8, s7, s6, s5, s4, s3, s2, s1, s0, startState])
      (by simp [s9, hregsP 8 (by decide), s8, s7, s6, s5, s4, s3])
      (by simp [s9, hregsP 9 (by decide), s8, s7, s6, s5, s4])
      (by simp [s9, hr10P]) (by simp [s9, hr11P]) (by simp [s9, hr12P]) (by simp [s9])
      hEdAtP hEdOkP hInPos1 hNoPos1 hInLe1 hNoLe1 le_rfl (by simp)
      hInAt1 hNoAt1 (by simpa using hInBd1') (by simpa using hNoBd1') hzP
  simp only [Nat.sub_self, List.drop_zero] at hedgeG_eq hedgeL_eq
  -- Final in-place copies to `workHeap` and `workHeap + L`
  have hheap2Hi : heap2 ≤ workHeap + evalCycleSpace L maxEdges maxPaths := by
    have hm1 : paths.length * (pathApplySpace L + 4 * L) ≤ maxPaths * (pathApplySpace L + 4 * L) :=
      Nat.mul_le_mul_right _ hptMax
    have hm2 : edges.length * (3 * L) ≤ maxEdges * (3 * L) := Nat.mul_le_mul_right _ hedMax
    dsimp only [evalCycleSpace]; omega
  have hheap2W : heap2 < 2 ^ w := by omega
  obtain ⟨stC1, cC1, hrC1, hcp1, hfrC1, hregsC1, hcC1⟩ :=
    evalCopyLoop_runs (L := L) (dst := workHeap) (src := innerPtr2) (p := p) (ω := ω)
      (dstReg := 5) (srcReg := 10) (st := stE) hr8E hr5E hr10E
      (by decide) (by decide) (by decide) (by decide) hw1 hworkLW (by omega)
      (by rcases hInPos2 with h | h <;> [exact Or.inl h; exact Or.inr (by omega)])
  let s10 : State := { stC1 with regs := Function.update stC1.regs 14 (workHeap + L) }
  have r10 : Runs w p ω (.assign 14 (.bin .add (.reg 5) (.reg 8))) stC1 .normal s10 4 :=
    runs_assign_iff.mpr ⟨workHeap + L, by
      simp [Expr.eval, BinOp.eval, hregsC1 5 (by decide), hr5E, hregsC1 8 (by decide), hr8E, hworkLW],
      rfl, rfl, rfl⟩
  obtain ⟨stC2, cC2, hrC2, hcp2, hfrC2, hregsC2, hcC2⟩ :=
    evalCopyLoop_runs (L := L) (dst := workHeap + L) (src := normPtr2) (p := p) (ω := ω)
      (dstReg := 14) (srcReg := 11) (st := s10)
      (by simp [s10, hregsC1 8 (by decide), hr8E]) (by simp [s10])
      (by simp [s10, hregsC1 11 (by decide), hr11E])
      (by decide) (by decide) (by decide) (by decide) hw1 (by omega) (by omega)
      (by rcases hNoPos2 with h | h <;> [exact Or.inl h; exact Or.inr (by omega)])
  have rRet : Runs w p ω (.ret (.reg 12)) stC2 (.returned heap2) stC2 2 :=
    runs_ret_iff.mpr ⟨heap2, by
      simp [Expr.eval, hregsC2 12 (by decide), s10, hregsC1 12 (by decide), hr12E], rfl, rfl, rfl⟩
  have hrPaths : Runs w p ω (evalPathsLoop (opTree 3) numAdd) s7 .normal stP (2 + cP + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s8, 2, cP, r8, hrP, rfl⟩)
  have hrEdges : Runs w p ω (evalEdgesLoop numAdd numSub) stP .normal stE (2 + cE + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s9, 2, cE, r9, hrE, rfl⟩)
  have rFull : Runs w p ω (evalCycleBody (opTree 3) numAdd numSub) s0 (.returned heap2) stC2 _ :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 3, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 3, _, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 5, _, r3,
    runs_seq_iff.mpr (Or.inr ⟨s4, 5, _, r4,
    runs_seq_iff.mpr (Or.inr ⟨s5, 2, _, r5,
    runs_seq_iff.mpr (Or.inr ⟨s6, 4, _, r6,
    runs_seq_iff.mpr (Or.inr ⟨s7, 6, _, r7,
    runs_seq_iff.mpr (Or.inr ⟨stP, 2 + cP + 1, _, hrPaths,
    runs_seq_iff.mpr (Or.inr ⟨stE, 2 + cE + 1, _, hrEdges,
    runs_seq_iff.mpr (Or.inr ⟨stC1, cC1, _, hrC1,
    runs_seq_iff.mpr (Or.inr ⟨s10, 4, _, r10,
    runs_seq_iff.mpr (Or.inr ⟨stC2, cC2, 2, hrC2, rRet, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
      rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  -- Final memory facts
  have hinnerOut : PathIntAt stC2.mem workHeap 4 L (treeGrad + edgeGrad) :=
    hInAt2.congr fun i hi => (hfrC2 (workHeap + i) (Or.inl (by omega))).trans (hcp1 i hi)
  have hnormOut : PathIntAt stC2.mem (workHeap + L) 4 L (treeLen + edgeLen) :=
    hNoAt2.congr fun i hi => (hcp2 i hi).trans (hfrC1 (normPtr2 + i) (by
      rcases hNoPos2 with rfl | hle <;> exact Or.inr (by omega)))
  have hfrAll : ∀ a < workHeap, ¬ Rtree.foot tok.treeHeap tok.treeTok a → stC2.mem a = mem a :=
    fun a ha hnf => (hfrC2 a (Or.inl (by omega))).trans ((hfrC1 a (Or.inl ha)).trans
      ((hfrE a (by omega)).trans (hfrP a ha hnf)))
  have hzAll : ZeroFrom stC2.mem heap2 := fun a ha =>
    (hfrC2 a (Or.inr (by omega))).trans ((hfrC1 a (Or.inr (by omega))).trans (hzE a ha))
  -- Algebra from `WireEvalMath`
  obtain ⟨hinnerEq, hnormEq, hnormNN⟩ :=
    evalCycle_route_algebra hfresh hRoute hnodup hlenNN htreeG_eq htreeL_eq hedgeG_eq hedgeL_eq
  -- Re-establish `solverStateRep`, `OffTreeRecInv`, `OffTreeRecBound`
  have hrepTreeFin : Rtree.rep tok.treeHeap s' treeTok' stC2.mem := by
    have hloc := pathRep_local 4 L LinkCut.PathProg.pathC tok.treeHeap s' treeTok' stP.mem stC2.mem
      (fun a ha => by
        have haW : a < workHeap := by
          have : Rtree.foot tok.treeHeap tok.treeTok a := by
            change tok.treeHeap ≤ a ∧ a < arenaEnd tok.treeHeap tok.treeTok.1.n L
            change tok.treeHeap ≤ a ∧ a < arenaEnd tok.treeHeap treeTok'.1.n L at ha
            rw [htrep.1, htn]; rwa [hrepTree1.1, hsn'] at ha
          exact hbelow a (Or.inr (Or.inl this))
        exact ((hfrC2 a (Or.inl (by omega))).trans ((hfrC1 a (Or.inl haW)).trans (hfrE a (by omega)))).symm)
    exact hloc.1 hrepTree1
  have hphiTreeFin : Rtree.phi tok.treeHeap treeTok' stC2.mem = Rtree.phi tok.treeHeap treeTok' stP.mem := by
    have hloc := pathRep_local 4 L LinkCut.PathProg.pathC tok.treeHeap s' treeTok' stP.mem stC2.mem
      (fun a ha => by
        have haW : a < workHeap := by
          have : Rtree.foot tok.treeHeap tok.treeTok a := by
            change tok.treeHeap ≤ a ∧ a < arenaEnd tok.treeHeap tok.treeTok.1.n L
            change tok.treeHeap ≤ a ∧ a < arenaEnd tok.treeHeap treeTok'.1.n L at ha
            rw [htrep.1, htn]; rwa [hrepTree1.1, hsn'] at ha
          exact hbelow a (Or.inr (Or.inl this))
        exact ((hfrC2 a (Or.inl (by omega))).trans ((hfrC1 a (Or.inl haW)).trans (hfrE a (by omega)))).symm)
    exact hloc.2.symm
  obtain ⟨hrepFin, hfootFin, hphiCores⟩ :=
    solverStateRep_after_eval hlocalCore hrep0 hbelow hsn' hW' hrepTreeFin hfrAll hns1 hpreSome1 hor1
  let tok' : SolverToken cfg L Rcore := { tok with tree := s', trees := trees', depth := depth', treeTok := treeTok' }
  have hag1318 : ∀ a, (tok.tag a = 13 ∨ tok.tag a = 18) → stC2.mem a = mem a := fun a ha => by
    have hnz : tok.tag a ≠ 0 := by rcases ha with h | h <;> omega
    have hne16 : tok.tag a ≠ 16 := by rcases ha with h | h <;> omega
    exact hfrAll a (hbelow a (Or.inl (hOwn a hnz))) (fun hf => hne16 (t16 a hf))
  have hoffFin : OffTreeRecInv model L stC2.mem tok.edgeRecords B :=
    offTreeRecInv_of_agree hrep0 hoff hag1318
  have hBdFin : OffTreeRecBound model L stC2.mem tok.edgeRecords B :=
    offTreeRecBound_of_agree hrep0 hBd hag1318
  have htag0 : ∀ a, ¬ Rrep.foot root tok a → tok'.tag a = 0 := fun a hnf => by
    by_contra hnz; exact hnf (Or.inl (hOwn a hnz))
  have hPresMeta : PreservesLevelMeta tok tok' mem stC2.mem := by
    refine ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ ha => ha, fun a ht => ?_⟩
    have hnz : tok.tag a ≠ 0 := by rcases ht with h | h | h | h <;> omega
    have hne16 : tok.tag a ≠ 16 := by rcases ht with h | h | h | h <;> omega
    exact ⟨rfl, hfrAll a (hbelow a (Or.inl (hOwn a hnz))) (fun hf => hne16 (t16 a hf))⟩
  refine ⟨heap2, _, stC2, tok', treeGrad + edgeGrad, treeLen + edgeLen, rFull,
    by omega, hheap2Hi, rfl, rfl, hnormNN, hinnerOut, hnormOut, hinnerEq, hnormEq,
    fun x hx => htag0 _ (hnfEd x hx), fun x hx => htag0 _ (hnfPt x hx), fun _ h => h,
    hrepFin, hPresMeta, hnum', hoffFin, hBdFin, hzAll,
    fun a ha hnf => hfrAll a ha (fun hf => hnf (Or.inr (Or.inl hf))),
    fun a ha => Or.inl ((hfootFin a).mp ha), ?_⟩
  -- Final cost bound
  have hphiSum : (∑ i : Fin cfg.P.d, Rcore.phi (tok'.coreHandle i.val) (tok'.coreTok i.val) stC2.mem) =
      ∑ i : Fin cfg.P.d, Rcore.phi (tok.coreHandle i.val) (tok.coreTok i.val) mem :=
    Finset.sum_congr rfl fun i _ => hphiCores i.val i.isLt
  have hmP : paths.length * (25 * (LinkCut.PathProg.pathC * (L + 1) ^ 2) * (4 * L + 1) + 76 * L + 170) ≤
      maxPaths * (25 * (LinkCut.PathProg.pathC * (L + 1) ^ 2) * (4 * L + 1) + 76 * L + 170) :=
    Nat.mul_le_mul_right _ hptMax
  have hmE : edges.length * (112 * L + 180) ≤ maxEdges * (112 * L + 180) :=
    Nat.mul_le_mul_right _ hedMax
  dsimp only [Rrep, Rtree, solverStateRep, tok', evalCycleBudget, s8, s7, s6, s5, s4, s3, s2, s1, s0, startState] at hcP hphiTreeFin ⊢
  rw [hphiTreeFin, hphiSum]
  omega

end MinCostFlow.MinRatio
