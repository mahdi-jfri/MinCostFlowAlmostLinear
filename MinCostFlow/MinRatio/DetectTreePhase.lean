module

public import MinCostFlow.MinRatio.DetectTreePhaseBase
import WordRAM.Tactic

/-!
# Tree-phase reporting execution for `Detect`

Proves `detectTreeStep_runs`, `detectTreeLoop_runs`, and `detectTreePhaseBody_runs`,
showing that `detectTreePhaseBody` finds and resets every ready tree edge in
`treeReadySet model` without duplicates, preserves `PathTreeNumericInv`, and runs in
amortized time `O((|treeReadySet| + 1) * pathTreeBudget)`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine

/-- One step of `detectTreeStep` either reports and resets a ready tree edge
(decrementing `rem` and preserving `cont = 1`), or detects exhaustion (`rem = 0`, setting
`cont = 0`). -/
private theorem detectTreeStep_runs {w m V psi k epsExp drainUnit treeInit reset : ℕ}
    {F : MinRatioFormat w} {cfg : Alg2Config} {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)}
    {p : Program} {ω : ℕ → Bool} {opTree : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg F.limbs Rcore} {mem₀ : ℕ → ℕ}
    {root base heap₀ : ℕ} {B R : ℤ} {rem phi : ℕ} {s : State}
    (hfmt4 : F.fmt.limbBits = 4)
    (hrep : (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp drainUnit Rcore).rep
      root model tok mem₀)
    (hbelow : ∀ a, (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp drainUnit Rcore).foot
      root tok a → a < base)
    (hTreeImpl : (LinkCut.PathProg.pathRep 4 F.limbs LinkCut.PathProg.pathC).Implements w p
      treeInit opTree
      (pathTreeMachineContract F.fmt F.limbs LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc F.limbs)))
    (hReset : ∀ edge th, MeetsContract w p reset (detectResetContract w 4 edge th))
    (heps : 0 < cfg.ε) (hlen : ∀ e ∈ model.extG.E, 0 < model.extℓ e)
    (hcapB : 2 * ((2 * tok.tree.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 F.limbs : ℤ))
    (hthrB : ∀ e ∈ model.extG.E, |detectorThreshold F.fmt.precision cfg.ε (model.extℓ e)| ≤ B)
    (hfitThr : ∀ e ∈ model.extG.E,
      Num.Fits 4 F.limbs (-detectorThreshold F.fmt.precision cfg.ε (model.extℓ e)))
    (htreeWord : 2 * tok.tree.n + 1 < 2 ^ w)
    (htreeWidth : Nat.log 2 (2 * tok.tree.n + 1) ≤ 4 * F.limbs)
    (hbaseHeap : base + 1 + m ≤ heap₀)
    (hroom : heap₀ + ((treeReadySet model).card + 1) * detectTreeRoundSpace F.limbs < 2 ^ w)
    (hw10 : 10 < 2 ^ w) (hLpos : 0 < F.limbs)
    (hInv : TreePhaseInv (P := F.fmt.precision) (m := m) model tok mem₀ root base heap₀ B R
      1 rem phi s) :
    ∃ out cost cont' rem' phi',
      Runs w p ω (detectTreeStep (opTree 6) (opTree 4) (opTree 5) reset) s .normal out cost ∧
      TreePhaseInv (P := F.fmt.precision) (m := m) model tok mem₀ root base heap₀ B R
        cont' rem' phi' out ∧
      ((cont' = 1 ∧ 0 < rem ∧ rem' = rem - 1 ∧
          cost + phi' ≤ detectTreeStepBudget F.limbs tok.tree.n + phi) ∨
       (cont' = 0 ∧ rem = 0 ∧ rem' = 0 ∧
          cost + phi' ≤ detectTreeFinalBudget F.limbs tok.tree.n + phi)) := by
  let L := F.limbs
  let P := F.fmt.precision
  let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
  obtain ⟨treeRep, curHeap, curTree, curTrees, curTreeTok,
    hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr11,
    hnd, hsub, hremEq, hlist, hcurLo, hcurHi, hzCur, hcn, hlct, hnum, htrep, hphiEq,
    hfootCur, hframeCur, htreeAcc, htreeRev, hns⟩ := hInv
  have hrep0 := hrep
  obtain ⟨_, _, _, _, hfreshInv, hfreshTab, hextM, _, _, _, _, _, _, hedgeAcc, _, _, _, _, _, htags⟩ := hrep
  obtain ⟨hOwn, _, _, _, _, _, _, _, t8, t9, t10, t11, t12, _, _, _, t16, t1718, _, _, _⟩ := htags
  have hltB {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) : a < base :=
    hbelow a (Or.inl (hOwn a (ht ▸ hv)))
  have hlenAddRem : treeRep.length + rem = (treeReadySet model).card := by
    rw [← hremEq, Finset.card_sdiff_of_subset hsub, List.toFinset_card_of_nodup hnd]
    have := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd] at this; omega
  have hcurStepW : curHeap + detectTreeRoundSpace F.limbs < 2 ^ w := by
    have h1 : (treeRep.length + 1) * detectTreeRoundSpace F.limbs ≤
        ((treeReadySet model).card + 1) * detectTreeRoundSpace F.limbs :=
      Nat.mul_le_mul_right _ (by omega)
    have hcurHi' : curHeap ≤ heap₀ + treeRep.length * detectTreeRoundSpace F.limbs := by
      simpa using hcurHi
    rw [Nat.add_mul, one_mul] at h1
    omega
  have hcurW : curHeap < 2 ^ w := by unfold detectTreeRoundSpace at hcurStepW; omega
  have hbaseW : base < 2 ^ w := by omega
  have hLW : L < 2 ^ w := F.parameters_fit.1
  have htreeHeapFoot : Rtree.foot tok.treeHeap tok.treeTok tok.treeHeap := by
    refine ⟨le_rfl, ?_⟩; unfold LinkCut.PathProg.arenaEnd LinkCut.PathProg.arenaNb; omega
  have htreeHeapW : tok.treeHeap < 2 ^ w :=
    lt_trans (hbelow tok.treeHeap (Or.inr (Or.inl htreeHeapFoot))) hbaseW
  have hfootLtCur : ∀ a, Rtree.foot tok.treeHeap curTreeTok a → a < curHeap := fun a ha => by
    rcases hfootCur a ha with h0 | ⟨_, hhi⟩
    · exact lt_of_lt_of_le (hbelow a (Or.inr (Or.inl h0))) (by omega)
    · exact hhi
  have hcapCur : 2 * ((2 * curTree.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ) := by
    rw [hcn]; exact hcapB
  have hpre6 : (pathTreeMachineContract F.fmt L LinkCut.PathProg.pathC
      (LinkCut.PathProg.pathAlloc L)).pre 6 curTree [tok.treeHeap, curHeap] s.mem := by
    refine ⟨⟨curTrees, tok.free, tok.depth, hlct⟩, hfmt4 ▸ hnum.fits hlct hcapCur,
      hcn ▸ htreeWord, hfmt4 ▸ (hcn ▸ htreeWidth), tok.treeHeap, curHeap, rfl, ?_⟩
    intro x hx
    exact hfmt4 ▸ pathTreeFits_expose_of_numeric hlct hnum hcapCur hx.2.1
  have hroom6 : curHeap + (pathTreeMachineContract F.fmt L LinkCut.PathProg.pathC
      (LinkCut.PathProg.pathAlloc L)).space 6 curTree [tok.treeHeap, curHeap] s.mem < 2 ^ w := by
    change curHeap + LinkCut.PathProg.pathAlloc L 6 curTree.n [tok.treeHeap, curHeap] < 2 ^ w
    unfold LinkCut.PathProg.pathAlloc
    unfold detectTreeRoundSpace at hcurStepW
    dsimp only [L]
    simp only [show (6 : ℕ) ≠ 7 by decide, ↓reduceIte]; omega
  obtain ⟨body6, hbody6, o1, st1, c1, hr6Call, tree1, treeTok1, hrep1, hpost6,
    ⟨hlo1, hhi1, hz1, hfr1, hft1⟩, hc1⟩ :=
    hTreeImpl.2.2 6 tok.treeHeap curTree curTreeTok [tok.treeHeap, curHeap] s.mem s.pos ω
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl <;> assumption)
      rfl htrep hpre6 hfootLtCur hzCur hroom6
  change curHeap ≤ o1.value at hlo1
  change o1.value ≤ curHeap + LinkCut.PathProg.pathAlloc L 6 curTree.n [tok.treeHeap, curHeap] at hhi1
  change ZeroFrom st1.mem o1.value at hz1
  change ∀ a < curHeap, ¬ Rtree.foot tok.treeHeap curTreeTok a → st1.mem a = s.mem a at hfr1
  change ∀ a, Rtree.foot tok.treeHeap treeTok1 a →
    Rtree.foot tok.treeHeap curTreeTok a ∨ (curHeap ≤ a ∧ a < o1.value) at hft1
  have hhi1' : o1.value ≤ curHeap + (20 * LinkCut.PathProg.treeLimbs F.limbs + 100) := by
    unfold LinkCut.PathProg.pathAlloc at hhi1
    simpa [show (6 : ℕ) ≠ 7 by decide, L] using hhi1
  have hret1W : o1.value < 2 ^ w := by unfold detectTreeRoundSpace at hcurStepW; omega
  let s1 : State := { regs := Function.update s.regs 12 o1.value, mem := st1.mem, pos := st1.pos }
  have rCall6 : Runs w p ω (.call 12 (opTree 6) [.reg 6, .reg 4]) s .normal s1 (c1 + 3) :=
    runs_call_iff.mpr ⟨[tok.treeHeap, curHeap], body6, o1, st1, c1,
      by simp [evalArgs, Expr.eval, hr6, hr4], hbody6, hr6Call, rfl, rfl,
      by simp [argsSize, Expr.size]; omega⟩
  let slot := st1.mem curHeap
  let s2 : State := { s1 with regs := Function.update s1.regs 10 slot }
  let s3 : State := { s2 with regs := Function.update s2.regs 4 o1.value }
  have rLoadSlot : Runs w p ω (.assign 10 (.load (.reg 4))) s1 .normal s2 3 :=
    runs_assign_iff.mpr ⟨slot, by simp [Expr.eval, s1, hr4, slot], rfl, rfl, rfl⟩
  have rSetHeap1 : Runs w p ω (.assign 4 (.reg 12)) s2 .normal s3 2 :=
    runs_assign_iff.mpr ⟨o1.value, by simp [Expr.eval, s2, s1], rfl, rfl, rfl⟩
  have hft1_0 : ∀ a, Rtree.foot tok.treeHeap treeTok1 a →
      Rtree.foot tok.treeHeap tok.treeTok a ∨ (heap₀ ≤ a ∧ a < o1.value) := fun a ha => by
    rcases hft1 a ha with hprev | ⟨h1, h2⟩
    · rcases hfootCur a hprev with h0 | ⟨h1, h2⟩
      · exact Or.inl h0
      · exact Or.inr ⟨h1, lt_of_lt_of_le h2 hlo1⟩
    · exact Or.inr ⟨le_trans hcurLo h1, h2⟩
  have hfr1_0 : ∀ a < heap₀, ¬ Rtree.foot tok.treeHeap tok.treeTok a →
      (a < base + 1 ∨ base + 1 + treeRep.length ≤ a) → st1.mem a = mem₀ a := fun a ha hnf hnr => by
    have hnfCur : ¬ Rtree.foot tok.treeHeap curTreeTok a := fun hc => by
      rcases hfootCur a hc with h0 | ⟨h1, _⟩
      · exact hnf h0
      · omega
    exact (hfr1 a (lt_of_lt_of_le ha hcurLo) hnfCur).trans (hframeCur a ha hnf hnr)
  have hmemT1 {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) (hv16 : v ≠ 16) : st1.mem a = mem₀ a := by
    have haB : a < base := hltB ht hv
    exact hfr1_0 a (by omega) (fun hf => hv16 (ht.symm.trans (t16 a hf))) (Or.inl (by omega))
  -- Split on `hpost6`: exhausted (`slot = 0`) vs ready (`slot ≠ 0`)
  rcases hpost6 with ⟨hslot0, rfl, hnoReady⟩ | ⟨slot', hslotEq, hready, rfl⟩
  · exact detectTreeStep_exhausted hrep0 hbelow heps hlen hbaseHeap hw10 rfl rfl rfl
      hr0 hr1 hr2 hr3 hr5 hr6 hr7 hr8 hr9 hnd hsub hremEq hlist hcurLo hcurHi hcn hlct hnum
      hphiEq hfootCur htreeAcc htreeRev hns rCall6 rLoadSlot rSetHeap1 hrep1 hlo1 hhi1' hz1 hfr1
      hft1_0 hfr1_0 hc1 hslot0 hnoReady
  · -- Ready branch: `slot = slot' ≠ 0`
    have hslotEq' : slot = slot' := hslotEq
    subst slot'
    have hslotBounds := pathTreeReady_bounds hready
    have hslotNz : slot ≠ 0 := hslotBounds.1
    have hslotLt : slot < 2 * tok.tree.n := hcn ▸ hslotBounds.2
    have hslotW : slot < 2 ^ w := by omega
    obtain ⟨hisSlot, vReady, hpairReady, hdetReady⟩ := (pathTreeReady_iff_forestPairs hlct slot).mp hready
    obtain ⟨heiCap, heiInT, hslEq, heE, he2i⟩ := htreeRev slot vReady hisSlot hpairReady
    let ei := mem₀ (tok.names + slot)
    let e := model.intToExt ei
    have hslotMem : slot ∈ curTrees.flatMap AuxTree.toList := pathTree_forestPair_mem_active hpairReady
    obtain ⟨t0, ht0, hsl0⟩ := List.mem_flatMap.mp hslotMem
    obtain ⟨trees1, left1, ht1, hlct1, _, _, hperm1, _⟩ := lctExpose_spec pathPayload_laws hlct ht0 hsl0
    obtain ⟨ts1Num, hlct1Num, hnum1Raw⟩ := pathTreeNumericInv_expose hlct hnum ht0 hsl0
    have hnum1 : PathTreeNumericInv (lctExpose pathPayload curTree slot) trees1 B R :=
      hnum1Raw.relabel hlct1Num hlct1
    obtain ⟨valAcc, acc, hpairAcc, hflowAcc, haccEq, hdetAcc, hgradAcc, hlenAcc, hfwdTAcc, hfwdFAcc⟩ :=
      htreeAcc e heE (he2i.symm ▸ heiInT)
    have hvalEq : valAcc = vReady := by
      have hpairAcc' : (slot, some valAcc) ∈ forestPairs pathPayload curTree.splay curTrees := by
        rw [he2i, hslEq] at hpairAcc; exact hpairAcc
      have h1 := pathTreeExpose_value_of_forestPair hlct hpairAcc'
      have h2 := pathTreeExpose_value_of_forestPair hlct hpairReady
      exact Option.some.inj (h1.symm.trans h2)
    subst hvalEq
    have hpend : e ∈ (algorithm2_detect cfg model).1 \ treeRep.toFinset :=
      (detect_residual_pending model heE heps (hlen e heE) haccEq hdetAcc).mp hdetReady
    obtain ⟨heDet, heNotRep⟩ := Finset.mem_sdiff.mp hpend
    have heTR : e ∈ treeReadySet model := mem_treeReadySet_iff.mpr ⟨heDet, he2i ▸ heiInT⟩
    obtain ⟨hndNext, hsubNext, hremNext⟩ := treeReady_snoc hnd hsub heTR heNotRep
    have hlenNextLeM : (treeRep ++ [e]).length ≤ m := treeRep_length_le_m hextM hndNext hsubNext
    have hlenLtM : treeRep.length < m := by
      simp only [List.length_append, List.length_singleton] at hlenNextLeM; omega
    have hnamesW : tok.names + slot < 2 ^ w := lt_trans (hltB (t10 slot hslotLt) (by decide)) hbaseW
    have hnamesEq : st1.mem (tok.names + slot) = ei := hmemT1 (t10 slot hslotLt) (by decide) (by decide)
    have hinvW : tok.inverse + ei < 2 ^ w := lt_trans (hltB (t8 ei heiCap) (by decide)) hbaseW
    have hinvEq : st1.mem (tok.inverse + ei) = e :=
      (hmemT1 (t8 ei heiCap) (by decide) (by decide)).trans (hfreshTab.2.2 ei heiCap)
    let cursor := base + 1 + treeRep.length
    have hcursorLtHeap0 : cursor < heap₀ := by omega
    have hcursorW : cursor < 2 ^ w := by omega
    have hcursorNextW : cursor + 1 < 2 ^ w := by omega
    let s4 : State := { s3 with regs := Function.update s3.regs 13 ei }
    let s5 : State := { s4 with regs := Function.update s4.regs 14 e }
    let s6 : State := { s5 with mem := Function.update s5.mem cursor e }
    let s7 : State := { s6 with regs := Function.update s6.regs 3 (cursor + 1) }
    have rEi : Runs w p ω (.assign 13 (.load (.bin .add (.reg 7) (.reg 10)))) s3 .normal s4 5 :=
      runs_assign_iff.mpr ⟨ei, by
        simp [Expr.eval, BinOp.eval, s3, s2, s1, hr7, hnamesW, hnamesEq, ei], rfl, rfl, rfl⟩
    have rE : Runs w p ω (.assign 14 (.load (.bin .add (.reg 8) (.reg 13)))) s4 .normal s5 5 :=
      runs_assign_iff.mpr ⟨e, by
        simp [Expr.eval, BinOp.eval, s4, s3, s2, s1, hr8, hinvW, hinvEq, e], rfl, rfl, rfl⟩
    have rStore : Runs w p ω (.store (.reg 3) (.reg 14)) s5 .normal s6 3 :=
      runs_store_iff.mpr ⟨cursor, e, by simp [Expr.eval, s5, s4, s3, s2, s1, hr3, cursor],
        by simp [Expr.eval, s5], rfl, rfl, rfl⟩
    have rInc : Runs w p ω (.assign 3 (.bin .add (.reg 3) (.const 1))) s6 .normal s7 4 :=
      runs_assign_iff.mpr ⟨cursor + 1, by
        simp [Expr.eval, BinOp.eval, s6, s5, s4, s3, s2, s1, hr3, cursor,
          show 1 < 2 ^ w by omega, hcursorNextW], rfl, rfl, rfl⟩
    have hcursorNotFoot1 : ¬ Rtree.foot tok.treeHeap treeTok1 cursor := fun hc => by
      rcases hft1_0 cursor hc with h0 | ⟨h1, _⟩
      · have := hbelow cursor (Or.inr (Or.inl h0)); omega
      · omega
    have hrep1_s7 : Rtree.rep tok.treeHeap (lctExpose pathPayload curTree slot) treeTok1 s7.mem :=
      (LinkCut.PathProg.pathRep_local 4 L LinkCut.PathProg.pathC tok.treeHeap _ treeTok1
        st1.mem s7.mem (fun a ha => by
          simp [s7, s6, s5, s4, s3, s2, s1,
            Function.update_of_ne (show a ≠ cursor from fun h => hcursorNotFoot1 (h ▸ ha))])).1 hrep1
    have hphi1_s7 : Rtree.phi tok.treeHeap treeTok1 s7.mem =
        Rtree.phi tok.treeHeap treeTok1 st1.mem :=
      (LinkCut.PathProg.pathRep_local 4 L LinkCut.PathProg.pathC tok.treeHeap
        (lctExpose pathPayload curTree slot) treeTok1
        st1.mem s7.mem (fun a ha => by
          simp [s7, s6, s5, s4, s3, s2, s1,
            Function.update_of_ne (show a ≠ cursor from fun h => hcursorNotFoot1 (h ▸ ha))])).2.symm
    have hz1_s7 : ZeroFrom s7.mem o1.value := fun a ha => by
      simp only [s7, s6, s5, s4, s3, s2, s1, Function.update_of_ne (show a ≠ cursor by omega)]
      exact hz1 a ha
    let readHeap := o1.value
    have htree1N : (lctExpose pathPayload curTree slot).n = tok.tree.n := hcn
    have hcap1 : 2 * ((2 * (lctExpose pathPayload curTree slot).n + 1 : ℕ) : ℤ) * (B + R) <
        (Num.capacity 4 L : ℤ) := by rw [htree1N]; exact hcapB
    have hslotMem1 : slot ∈ trees1.flatMap AuxTree.toList :=
      List.mem_flatMap.mpr ⟨AuxTree.node slot left1 .leaf, ht1, by simp [AuxTree.toList]⟩
    have hAct1 : pathTreeActive (lctExpose pathPayload curTree slot) slot :=
      ⟨trees1, tok.free, tok.depth, hlct1, hslotMem1⟩
    have hpre4 : (pathTreeMachineContract F.fmt L LinkCut.PathProg.pathC
        (LinkCut.PathProg.pathAlloc L)).pre 4 (lctExpose pathPayload curTree slot)
        [tok.treeHeap, slot, readHeap] s7.mem :=
      ⟨⟨trees1, tok.free, tok.depth, hlct1⟩, hfmt4 ▸ hnum1.fits hlct1 hcap1,
        htree1N ▸ htreeWord, hfmt4 ▸ (htree1N ▸ htreeWidth),
        tok.treeHeap, slot, readHeap, rfl, hAct1,
        hfmt4 ▸ pathTreeFits_expose_of_numeric hlct1 hnum1 hcap1 hAct1⟩
    have hfoot1LtRead : ∀ a, Rtree.foot tok.treeHeap treeTok1 a → a < readHeap := fun a ha => by
      rcases hft1_0 a ha with h0 | ⟨_, h2⟩
      · exact lt_of_lt_of_le (hbelow a (Or.inr (Or.inl h0))) (by omega)
      · exact h2
    have hroom4 : readHeap + (pathTreeMachineContract F.fmt L LinkCut.PathProg.pathC
        (LinkCut.PathProg.pathAlloc L)).space 4 (lctExpose pathPayload curTree slot)
        [tok.treeHeap, slot, readHeap] s7.mem < 2 ^ w := by
      simp only [pathTreeMachineContract, LinkCut.PathProg.pathAlloc,
        show (4 : ℕ) ≠ 7 by decide, ↓reduceIte]
      unfold detectTreeRoundSpace at hcurStepW
      dsimp only [L]; omega
    obtain ⟨body4, hbody4, o2, st2, c2, hr4Call, tree2, treeTok2, hrep2, ⟨htree2Eq, hreadAt⟩,
      ⟨hlo2, hhi2, hz2, hfr2, hft2⟩, hc2⟩ :=
      hTreeImpl.2.2 4 tok.treeHeap (lctExpose pathPayload curTree slot) treeTok1
        [tok.treeHeap, slot, readHeap] s7.mem s7.pos ω
        (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl | rfl <;> assumption)
        rfl hrep1_s7 hpre4 hfoot1LtRead hz1_s7 hroom4
    change tree2 = lctExpose pathPayload (lctExpose pathPayload curTree slot) slot at htree2Eq
    subst htree2Eq
    change readHeap ≤ o2.value at hlo2
    change ZeroFrom st2.mem o2.value at hz2
    change ∀ a < readHeap, ¬ Rtree.foot tok.treeHeap treeTok1 a → st2.mem a = s7.mem a at hfr2
    change ∀ a, Rtree.foot tok.treeHeap treeTok2 a →
      Rtree.foot tok.treeHeap treeTok1 a ∨ (readHeap ≤ a ∧ a < o2.value) at hft2
    have hhi2' : o2.value ≤ readHeap + (20 * LinkCut.PathProg.treeLimbs F.limbs + 100) := by
      simpa [pathTreeMachineContract, LinkCut.PathProg.pathAlloc, heapArg,
        show (4 : ℕ) ≠ 7 by decide, L] using hhi2
    let s8 : State := { regs := Function.update s7.regs 12 o2.value, mem := st2.mem, pos := st2.pos }
    have rCall4 : Runs w p ω (.call 12 (opTree 4) [.reg 6, .reg 10, .reg 4]) s7 .normal s8 (c2 + 4) :=
      runs_call_iff.mpr ⟨[tok.treeHeap, slot, readHeap], body4, o2, st2, c2,
        by simp [evalArgs, Expr.eval, s7, s6, s5, s4, s3, s2, s1, hr6, readHeap], hbody4, hr4Call,
        rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
    let readEnd := readHeap + 2 + 4 * L
    have hrecLeAlloc := recordWords_le_pathAlloc F.limbs
    have hreadEndW : readEnd < 2 ^ w := by unfold detectTreeRoundSpace at hcurStepW; dsimp only [readEnd, L]; omega
    let s9 : State := { s8 with regs := Function.update s8.regs 15 readEnd }
    have rReadEnd : Runs w p ω (.assign 15 (.bin .add (.bin .add (.reg 4) (.const 2))
        (.bin .mul (.const 4) (.reg 5)))) s8 .normal s9 8 :=
      runs_assign_iff.mpr ⟨readEnd, by
        simp [Expr.eval, BinOp.eval, s8, s7, s6, s5, s4, s3, s2, s1, hr5,
          show 2 < 2 ^ w by omega, show 4 < 2 ^ w by omega,
          show o1.value + 2 < 2 ^ w by omega, show 4 * F.limbs < 2 ^ w by omega,
          show o1.value + 2 + 4 * F.limbs < 2 ^ w by omega, readEnd, readHeap, L],
        rfl, rfl, rfl⟩
    let resetHeap := max o2.value readEnd
    have hresetGe2 : o2.value ≤ resetHeap := le_max_left _ _
    have hresetGeEnd : readEnd ≤ resetHeap := le_max_right _ _
    have hresetHi : resetHeap ≤ readHeap + (20 * LinkCut.PathProg.treeLimbs F.limbs + 100) :=
      max_le hhi2' (by dsimp only [readEnd, L]; omega)
    have hresetW : resetHeap < 2 ^ w := by unfold detectTreeRoundSpace at hcurStepW; omega
    have hresetNextW : resetHeap + (2 + 4 * L) < 2 ^ w := by
      unfold detectTreeRoundSpace at hcurStepW; dsimp only [L]; omega
    let s10 : State := { s9 with regs := Function.update s9.regs 12 resetHeap }
    obtain ⟨cM, hcM, rMax⟩ := detectTreeMax_runs (w := w) (p := p) (ω := ω) (s := s9)
      (a := o2.value) (b := readEnd) (by simp [s9, s8]) (by simp [s9]) (by omega)
    have hslThrW : tok.slotThresholds + slot < 2 ^ w :=
      lt_trans (hltB (t11 slot hslotLt) (by decide)) hbaseW
    have hft2_0 : ∀ a, Rtree.foot tok.treeHeap treeTok2 a →
        Rtree.foot tok.treeHeap tok.treeTok a ∨ (heap₀ ≤ a ∧ a < o2.value) := fun a ha => by
      rcases hft2 a ha with h1 | ⟨h1, h2⟩
      · rcases hft1_0 a h1 with h0 | ⟨ha1, ha2⟩
        · exact Or.inl h0
        · exact Or.inr ⟨ha1, lt_of_lt_of_le ha2 hlo2⟩
      · exact Or.inr ⟨le_trans hcurLo (le_trans hlo1 h1), h2⟩
    have hfr2_0 : ∀ a < heap₀, ¬ Rtree.foot tok.treeHeap tok.treeTok a →
        (a < base + 1 ∨ base + 1 + treeRep.length + 1 ≤ a) → st2.mem a = mem₀ a := fun a ha hnf hnr => by
      have hnf1 : ¬ Rtree.foot tok.treeHeap treeTok1 a := fun hc => by
        rcases hft1_0 a hc with h0 | ⟨h1, _⟩
        · exact hnf h0
        · omega
      have hneCur : a ≠ cursor := by omega
      have h2 := hfr2 a (lt_of_lt_of_le ha (le_trans hcurLo hlo1)) hnf1
      rw [h2]
      simp only [s7, s6, s5, s4, s3, s2, s1, Function.update_of_ne hneCur]
      exact hfr1_0 a ha hnf (by omega)
    have hmemT2 {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) (hv16 : v ≠ 16) : st2.mem a = mem₀ a := by
      have haB : a < base := hltB ht hv
      exact hfr2_0 a (by omega) (fun hf => hv16 (ht.symm.trans (t16 a hf))) (Or.inl (by omega))
    let thrPtr := mem₀ (tok.edgeThresholds + ei)
    have hbrT0 := (hedgeAcc.1 e heE).2.2
    rw [he2i, ite_eq_left heiInT] at hbrT0
    have hslThrEq : st2.mem (tok.slotThresholds + slot) = thrPtr := by
      rw [hmemT2 (t11 slot hslotLt) (by decide) (by decide)]
      simpa [hslEq, thrPtr] using hbrT0.2.2.2.1
    have hthrAt2 : PathIntAt st2.mem thrPtr 4 L (detectorThreshold P cfg.ε (model.extℓ e)) := by
      have hthrAt0 : PathIntAt mem₀ thrPtr 4 L (detectorThreshold P cfg.ε (model.extℓ e)) := by
        have h0 := (hedgeAcc.1 e heE).2.1; dsimp only [e] at h0; rw [he2i] at h0; exact h0
      refine hthrAt0.congr (fun j hj => ?_)
      have ht17 := (t1718 e heE).1 j hj
      rw [he2i] at ht17
      exact hmemT2 ht17 (by decide) (by decide)
    have hthrEndB : thrPtr + L ≤ base := by
      have hlast := (t1718 e heE).1 (L - 1) (by dsimp only [L]; omega)
      rw [he2i] at hlast
      have := hltB hlast (by decide); dsimp only [thrPtr, ei, L] at *; omega
    have hthrW : thrPtr < 2 ^ w := by omega
    let s11 : State := { s10 with regs := Function.update s10.regs 16 thrPtr }
    have rThr : Runs w p ω (.assign 16 (.load (.bin .add (.reg 9) (.reg 10)))) s10 .normal s11 5 :=
      runs_assign_iff.mpr ⟨thrPtr, by
        simp [Expr.eval, BinOp.eval, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr9,
          hslThrW, hslThrEq, thrPtr], rfl, rfl, rfl⟩
    have hval2Eq : ((lctExpose pathPayload (lctExpose pathPayload curTree slot) slot).splay.nodes slot).val =
        some valAcc := by
      have hpair1 : (slot, some valAcc) ∈ forestPairs pathPayload
          (lctExpose pathPayload curTree slot).splay trees1 := hperm1.mem_iff.mpr hpairReady
      exact pathTreeExpose_value_of_forestPair hlct1 hpair1
    have hreadAt' : PathEdgeAt st2.mem readHeap 4 L (some valAcc) := by
      simpa [heapArg, hfmt4, hval2Eq] using hreadAt
    let hthrVal := detectorThreshold P cfg.ε (model.extℓ e)
    obtain ⟨bodyR, hbodyR, oR, stR, cR, hrRCall, ⟨_, _, _, _, hargsR, hretR, hnewEdgeAt, hfrR, hzR⟩, hcR⟩ :=
      hReset valAcc hthrVal [readHeap, thrPtr, L, resetHeap] st2.mem s11.pos ω
        (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl | rfl | rfl <;> assumption)
        ⟨readHeap, thrPtr, L, resetHeap, rfl, by omega, by omega, by omega, hresetNextW,
          hreadAt', hthrAt2, hfitThr e heE, fun a ha => hz2 a (le_trans hresetGe2 ha)⟩
    simp only [List.cons.injEq, and_true] at hargsR
    rcases hargsR with ⟨rfl, rfl, rfl, rfl⟩
    let writeHeap := resetHeap + (2 + 4 * L)
    let newVal : PathEdgeValue := { valAcc with detector := -hthrVal }
    let s12 : State := { regs := Function.update s11.regs 17 oR.value, mem := stR.mem, pos := stR.pos }
    have rCallR : Runs w p ω (.call 17 reset [.reg 4, .reg 16, .reg 5, .reg 12])
        s11 .normal s12 (cR + 5) :=
      runs_call_iff.mpr ⟨[readHeap, thrPtr, L, resetHeap], bodyR, oR, stR, cR,
        by simp [evalArgs, Expr.eval, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr5, L, readHeap, thrPtr, resetHeap],
        hbodyR, hrRCall, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
    have hcR' : cR ≤ 87 * L + 96 := by simpa [detectResetContract] using hcR
    have hfoot2LtReset : ∀ a, Rtree.foot tok.treeHeap treeTok2 a → a < resetHeap := fun a ha => by
      rcases hft2_0 a ha with h0 | ⟨_, h2⟩
      · exact lt_of_lt_of_le (hbelow a (Or.inr (Or.inl h0))) (by omega)
      · exact lt_of_lt_of_le h2 hresetGe2
    have hrep2_R : Rtree.rep tok.treeHeap
        (lctExpose pathPayload (lctExpose pathPayload curTree slot) slot) treeTok2 stR.mem :=
      (LinkCut.PathProg.pathRep_local 4 L LinkCut.PathProg.pathC tok.treeHeap _ treeTok2
        st2.mem stR.mem (fun a ha => (hfrR a (hfoot2LtReset a ha)).symm)).1 hrep2
    have hphi2_R : Rtree.phi tok.treeHeap treeTok2 stR.mem =
        Rtree.phi tok.treeHeap treeTok2 st2.mem :=
      (LinkCut.PathProg.pathRep_local 4 L LinkCut.PathProg.pathC tok.treeHeap
        (lctExpose pathPayload (lctExpose pathPayload curTree slot) slot) treeTok2
        st2.mem stR.mem (fun a ha => (hfrR a (hfoot2LtReset a ha)).symm)).2.symm
    have hslotIn1 : slot ∈ (AuxTree.node slot left1 .leaf).toList := by simp [AuxTree.toList]
    obtain ⟨trees2, left2, ht2, hlct2, _, _, hperm2, _⟩ :=
      lctExpose_spec pathPayload_laws hlct1 ht1 hslotIn1
    obtain ⟨ts2Num, hlct2Num, hnum2Raw⟩ :=
      pathTreeNumericInv_expose hlct1 hnum1 ht1 hslotIn1
    have hnum2 : PathTreeNumericInv (lctExpose pathPayload (lctExpose pathPayload curTree slot) slot)
        trees2 B R := hnum2Raw.relabel hlct2Num hlct2
    have hnewValB : ∀ v, some newVal = some v →
        |v.gradient| ≤ B ∧ |v.length| ≤ B ∧ |v.flow| ≤ B ∧ |v.detector| ≤ B := by
      intro v hv
      cases Option.some.inj hv
      obtain ⟨hg, hl, hf, _⟩ := hnum.2.2.2.1 slot valAcc hpairReady
      exact ⟨hg, hl, hf, by simpa [newVal, abs_neg] using hthrB e heE⟩
    obtain ⟨trees3, hlct3, hpair3⟩ := pathTreeReport_forestPairs hlct hslotMem (some newVal)
    have hslotIn2 : slot ∈ (AuxTree.node slot left2 .leaf).toList := by simp [AuxTree.toList]
    obtain ⟨ts3Num, hlct3Num, hnum3Raw⟩ :=
      pathTreeNumericInv_write hlct2 hnum2 ht2 hslotIn2 hnewValB
    have hnum3 : PathTreeNumericInv
        (pathTreeWrite (lctExpose pathPayload (lctExpose pathPayload curTree slot) slot) slot (some newVal))
        trees3 B R := hnum3Raw.relabel hlct3Num hlct3
    have htree2N : (lctExpose pathPayload (lctExpose pathPayload curTree slot) slot).n = tok.tree.n := hcn
    have htree3N : (pathTreeWrite (lctExpose pathPayload (lctExpose pathPayload curTree slot) slot)
        slot (some newVal)).n = tok.tree.n := hcn
    have hcap2 : 2 * ((2 * (lctExpose pathPayload (lctExpose pathPayload curTree slot) slot).n + 1 : ℕ) : ℤ) *
        (B + R) < (Num.capacity 4 L : ℤ) := by rw [htree2N]; exact hcapB
    have hcap3 : 2 * ((2 * (pathTreeWrite (lctExpose pathPayload (lctExpose pathPayload curTree slot) slot)
        slot (some newVal)).n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ) := by
      rw [htree3N]; exact hcapB
    have hreadNew : readPathEdge stR.mem resetHeap 4 L = some newVal := readPathEdge_eq hnewEdgeAt
    have hpre5 : (pathTreeMachineContract F.fmt L LinkCut.PathProg.pathC
        (LinkCut.PathProg.pathAlloc L)).pre 5
        (lctExpose pathPayload (lctExpose pathPayload curTree slot) slot)
        [tok.treeHeap, slot, resetHeap, writeHeap] stR.mem := by
      refine ⟨⟨trees2, tok.free, tok.depth, hlct2⟩, hfmt4 ▸ hnum2.fits hlct2 hcap2,
        htree2N ▸ htreeWord, hfmt4 ▸ (htree2N ▸ htreeWidth),
        tok.treeHeap, slot, resetHeap, writeHeap, rfl, htree2N ▸ (hcn ▸ hisSlot),
        ⟨trees2, tok.free, tok.depth, hlct2,
          List.mem_flatMap.mpr ⟨AuxTree.node slot left2 .leaf, ht2, by simp [AuxTree.toList]⟩⟩,
        le_rfl, ?_, ?_, ?_⟩
      · rw [hfmt4, hreadNew]; exact hnewEdgeAt
      · rw [hfmt4, hreadNew]; rfl
      · rw [hfmt4, hreadNew]; exact hnum3.fits hlct3 hcap3
    have hfoot2LtWrite : ∀ a, Rtree.foot tok.treeHeap treeTok2 a → a < writeHeap := fun a ha =>
      lt_of_lt_of_le (hfoot2LtReset a ha) (Nat.le_add_right _ _)
    have hroom5 : writeHeap + (pathTreeMachineContract F.fmt L LinkCut.PathProg.pathC
        (LinkCut.PathProg.pathAlloc L)).space 5
        (lctExpose pathPayload (lctExpose pathPayload curTree slot) slot)
        [tok.treeHeap, slot, resetHeap, writeHeap] stR.mem < 2 ^ w := by
      simp only [pathTreeMachineContract, LinkCut.PathProg.pathAlloc,
        show (5 : ℕ) ≠ 7 by decide, ↓reduceIte]
      unfold detectTreeRoundSpace at hcurStepW
      dsimp only [writeHeap, L]; omega
    obtain ⟨body5, hbody5, o3, st3, c3, hr5Call, tree3, treeTok3, hrep3, hpost5,
      ⟨hlo3, hhi3, hz3, hfr3, hft3⟩, hc3⟩ :=
      hTreeImpl.2.2 5 tok.treeHeap
        (lctExpose pathPayload (lctExpose pathPayload curTree slot) slot) treeTok2
        [tok.treeHeap, slot, resetHeap, writeHeap] stR.mem s12.pos ω
        (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl | rfl | rfl <;> assumption)
        rfl hrep2_R hpre5 hfoot2LtWrite (by simpa [heapArg, writeHeap, hretR] using hzR) hroom5
    change tree3 = pathTreeWrite (lctExpose pathPayload (lctExpose pathPayload curTree slot) slot)
      slot (readPathEdge stR.mem resetHeap F.fmt.limbBits L) at hpost5
    rw [hfmt4, hreadNew] at hpost5
    subst hpost5
    change writeHeap ≤ o3.value at hlo3
    change ZeroFrom st3.mem o3.value at hz3
    change ∀ a < writeHeap, ¬ Rtree.foot tok.treeHeap treeTok2 a → st3.mem a = stR.mem a at hfr3
    change ∀ a, Rtree.foot tok.treeHeap treeTok3 a →
      Rtree.foot tok.treeHeap treeTok2 a ∨ (writeHeap ≤ a ∧ a < o3.value) at hft3
    have hhi3' : o3.value ≤ writeHeap + (20 * LinkCut.PathProg.treeLimbs F.limbs + 100) := by
      simpa [pathTreeMachineContract, LinkCut.PathProg.pathAlloc, heapArg,
        show (5 : ℕ) ≠ 7 by decide, L] using hhi3
    let s13 : State := { regs := Function.update s12.regs 4 o3.value, mem := st3.mem, pos := st3.pos }
    have rCall5 : Runs w p ω (.call 4 (opTree 5) [.reg 6, .reg 10, .reg 12, .reg 17])
        s12 .normal s13 (c3 + 5) :=
      runs_call_iff.mpr ⟨[tok.treeHeap, slot, resetHeap, writeHeap], body5, o3, st3, c3,
        by simp [evalArgs, Expr.eval, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr6,
          hretR, writeHeap, resetHeap],
        hbody5, hr5Call, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
    let branchCost := 5 + (5 + (3 + (4 + ((c2 + 4) + (8 + (cM + (5 + ((cR + 5) + (c3 + 5) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1
    have rBranch : Runs w p ω
        (.assign 13 (.load (.bin .add (.reg 7) (.reg 10))) ;;
         .assign 14 (.load (.bin .add (.reg 8) (.reg 13))) ;;
         .store (.reg 3) (.reg 14) ;;
         .assign 3 (.bin .add (.reg 3) (.const 1)) ;;
         .call 12 (opTree 4) [.reg 6, .reg 10, .reg 4] ;;
         .assign 15 (.bin .add (.bin .add (.reg 4) (.const 2)) (.bin .mul (.const 4) (.reg 5))) ;;
         .cond (.bin .lt (.reg 12) (.reg 15)) (.assign 12 (.reg 15)) .nop ;;
         .assign 16 (.load (.bin .add (.reg 9) (.reg 10))) ;;
         .call 17 reset [.reg 4, .reg 16, .reg 5, .reg 12] ;;
         .call 4 (opTree 5) [.reg 6, .reg 10, .reg 12, .reg 17])
        s3 .normal s13 branchCost :=
      runs_seq_iff.mpr (Or.inr ⟨s4, _, _, rEi,
        runs_seq_iff.mpr (Or.inr ⟨s5, _, _, rE,
        runs_seq_iff.mpr (Or.inr ⟨s6, _, _, rStore,
        runs_seq_iff.mpr (Or.inr ⟨s7, _, _, rInc,
        runs_seq_iff.mpr (Or.inr ⟨s8, _, _, rCall4,
        runs_seq_iff.mpr (Or.inr ⟨s9, _, _, rReadEnd,
        runs_seq_iff.mpr (Or.inr ⟨s10, _, _, rMax,
        runs_seq_iff.mpr (Or.inr ⟨s11, _, _, rThr,
        runs_seq_iff.mpr (Or.inr ⟨s12, _, _, rCallR, rCall5, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    have rCond : Runs w p ω (.cond (.reg 10)
        (.assign 13 (.load (.bin .add (.reg 7) (.reg 10))) ;;
         .assign 14 (.load (.bin .add (.reg 8) (.reg 13))) ;;
         .store (.reg 3) (.reg 14) ;;
         .assign 3 (.bin .add (.reg 3) (.const 1)) ;;
         .call 12 (opTree 4) [.reg 6, .reg 10, .reg 4] ;;
         .assign 15 (.bin .add (.bin .add (.reg 4) (.const 2)) (.bin .mul (.const 4) (.reg 5))) ;;
         .cond (.bin .lt (.reg 12) (.reg 15)) (.assign 12 (.reg 15)) .nop ;;
         .assign 16 (.load (.bin .add (.reg 9) (.reg 10))) ;;
         .call 17 reset [.reg 4, .reg 16, .reg 5, .reg 12] ;;
         .call 4 (opTree 5) [.reg 6, .reg 10, .reg 12, .reg 17])
        (.assign 11 (.const 0))) s3 .normal s13 (branchCost + 2) :=
      runs_cond_iff.mpr ⟨slot, branchCost, by simp [Expr.eval, s3, s2],
        by simp only [hslotNz, ↓reduceIte]; exact rBranch, by simp [Expr.size]; omega⟩
    have rStep : Runs w p ω (detectTreeStep (opTree 6) (opTree 4) (opTree 5) reset)
        s .normal s13 ((c1 + 3) + (3 + (2 + (branchCost + 2) + 1) + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨s1, _, _, rCall6,
        runs_seq_iff.mpr (Or.inr ⟨s2, _, _, rLoadSlot,
        runs_seq_iff.mpr (Or.inr ⟨s3, _, _, rSetHeap1, rCond, rfl⟩), rfl⟩), rfl⟩)
    have hft3_0 : ∀ a, Rtree.foot tok.treeHeap treeTok3 a →
        Rtree.foot tok.treeHeap tok.treeTok a ∨ (heap₀ ≤ a ∧ a < o3.value) := fun a ha => by
      rcases hft3 a ha with h2 | ⟨h1, h2⟩
      · rcases hft2_0 a h2 with h0 | ⟨ha1, ha2⟩
        · exact Or.inl h0
        · exact Or.inr ⟨ha1, lt_of_lt_of_le ha2 (by omega)⟩
      · exact Or.inr ⟨by omega, h2⟩
    have hfr3_2 : ∀ a < heap₀, ¬ Rtree.foot tok.treeHeap tok.treeTok a → st3.mem a = st2.mem a := fun a ha hnf => by
      have hnf2 : ¬ Rtree.foot tok.treeHeap treeTok2 a := fun hc => by
        rcases hft2_0 a hc with h0 | ⟨h1, _⟩
        · exact hnf h0
        · omega
      exact (hfr3 a (by omega) hnf2).trans (hfrR a (by omega))
    have hfr3_0 : ∀ a < heap₀, ¬ Rtree.foot tok.treeHeap tok.treeTok a →
        (a < base + 1 ∨ base + 1 + (treeRep ++ [e]).length ≤ a) → st3.mem a = mem₀ a := fun a ha hnf hnr => by
      simp only [List.length_append, List.length_singleton] at hnr
      exact (hfr3_2 a ha hnf).trans (hfr2_0 a ha hnf (by omega))
    refine ⟨s13, (c1 + 3) + (3 + (2 + (branchCost + 2) + 1) + 1) + 1,
      1, rem - 1, Rtree.phi tok.treeHeap treeTok3 st3.mem, rStep, ?_, Or.inl ⟨rfl, by omega, rfl, ?_⟩⟩
    · refine ⟨treeRep ++ [e], o3.value,
        pathTreeWrite (lctExpose pathPayload (lctExpose pathPayload curTree slot) slot) slot (some newVal),
        trees3, treeTok3,
        by simp [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr0],
        by simp [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr1],
        by simp [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr2],
        by simp [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, cursor,
          List.length_append, Nat.add_assoc],
        by simp [s13],
        by simp [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr5],
        by simp [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr6],
        by simp [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr7],
        by simp [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr8],
        by simp [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr9],
        by simp [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr11],
        hndNext, hsubNext, by omega, ?_, by omega, ?_, hz3, htree3N, hlct3, hnum3, hrep3, rfl,
        hft3_0, hfr3_0, ?_, ?_, ?_⟩
      · intro idx hidx
        have haddrLt : base + 1 + idx < heap₀ := by omega
        have hnf0 : ¬ Rtree.foot tok.treeHeap tok.treeTok (base + 1 + idx) := fun hc => by
          have := hbelow _ (Or.inr (Or.inl hc)); omega
        rw [hfr3_2 _ haddrLt hnf0]
        have hnf1 : ¬ Rtree.foot tok.treeHeap treeTok1 (base + 1 + idx) := fun hc => by
          rcases hft1_0 _ hc with h0 | ⟨h1, _⟩
          · exact hnf0 h0
          · omega
        rw [hfr2 _ (by omega) hnf1]
        by_cases hlt : idx < treeRep.length
        · have hne : base + 1 + idx ≠ cursor := by omega
          simp only [s7, s6, s5, s4, s3, s2, s1, Function.update_of_ne hne,
            List.getElem_append_left hlt]
          have hnfC : ¬ Rtree.foot tok.treeHeap curTreeTok (base + 1 + idx) := fun hc => by
            rcases hfootCur _ hc with h0 | ⟨h1, _⟩
            · exact hnf0 h0
            · omega
          exact (hfr1 _ (by omega) hnfC).trans (hlist idx hlt)
        · have hidxEq : idx = treeRep.length := by
            simp only [List.length_append, List.length_singleton] at hidx; omega
          subst hidxEq
          simp [s7, s6, cursor]
      · rw [Nat.sub_self, Nat.add_zero] at hcurHi ⊢
        simp only [List.length_append, List.length_singleton, Nat.add_mul, one_mul]
        unfold detectTreeRoundSpace at hcurHi ⊢; dsimp only [writeHeap, L] at *; omega
      · have hpar1 := inducedSubPar_expose_witness hlct hslotMem hlct1
        have hpar2 := inducedSubPar_expose_witness hlct1 hslotMem1 hlct2
        have hpar3 := inducedSubPar_write_witness hlct2
          (List.mem_flatMap.mpr ⟨AuxTree.node slot left2 .leaf, ht2, hslotIn2⟩) hlct3
        have hparAll : inducedSubPar pathPayload
            (pathTreeWrite (lctExpose pathPayload (lctExpose pathPayload curTree slot) slot) slot (some newVal)).splay
            trees3 = inducedSubPar pathPayload curTree.splay curTrees :=
          hpar3.trans (hpar2.trans hpar1)
        intro e' he'E; dsimp only; intro he'InT
        by_cases hEq : e' = e
        · subst hEq
          have hslE : mem₀ (tok.slots + model.extToInt e) = slot := by rw [he2i, hslEq]
          rw [hslE]
          refine ⟨newVal, 0, (hpair3 slot (some newVal)).mpr (Or.inl ⟨rfl, rfl⟩), hflowAcc, ?_, ?_,
            hgradAcc, hlenAcc, ?_, ?_⟩
          · simp [resetReported]
          · simp [newVal, hthrVal, P]
          · intro hf; rw [hparAll]; simpa [hslE] using hfwdTAcc hf
          · intro hf; rw [hparAll]; simpa [hslE] using hfwdFAcc hf
        · obtain ⟨v', a', hp', hfl', hac', hd', hg', hl', hft', hff'⟩ := htreeAcc e' he'E he'InT
          have hneSlot : mem₀ (tok.slots + model.extToInt e') ≠ slot := fun h => by
            have hbr' := (hedgeAcc.1 e' he'E).2.2
            rw [ite_eq_left he'InT] at hbr'
            have hnm' : mem₀ (tok.names + slot) = model.extToInt e' := by rw [← h]; exact hbr'.2.2.1
            have heiEq : model.extToInt e' = model.extToInt e := hnm'.symm.trans he2i.symm
            exact hEq ((hfreshInv.hLeft e' he'E).symm.trans
              (congrArg model.intToExt heiEq |>.trans (hfreshInv.hLeft e heE)))
          refine ⟨v', a', (hpair3 _ _).mpr (Or.inr ⟨hneSlot, hp'⟩), hfl', ?_, hd', hg', hl',
            fun hf => by rw [hparAll]; exact hft' hf, fun hf => by rw [hparAll]; exact hff' hf⟩
          simpa [resetReported, hEq] using hac'
      · intro sl' v' hsl' hp'
        rcases (hpair3 sl' (some v')).mp hp' with ⟨rfl, _⟩ | ⟨_, hpOld⟩
        · exact ⟨heiCap, heiInT, hslEq, heE, he2i⟩
        · exact htreeRev sl' v' (htree3N.symm ▸ hsl') hpOld
      · have hns1 := treeEditNamedSlots_expose_witness hns hlct hslotMem hlct1
        have hns2 := treeEditNamedSlots_expose_witness hns1 hlct1 hslotMem1 hlct2
        exact treeEditNamedSlots_write_witness hns2 hlct2
          (List.mem_flatMap.mpr ⟨AuxTree.node slot left2 .leaf, ht2, hslotIn2⟩) hlct3
    · dsimp only [detectTreeStepBudget, branchCost]
      change c1 + Rtree.phi tok.treeHeap treeTok1 st1.mem ≤
        pathTreeBudget LinkCut.PathProg.pathC L curTree.n + Rtree.phi tok.treeHeap curTreeTok s.mem at hc1
      change c2 + Rtree.phi tok.treeHeap treeTok2 st2.mem ≤
        pathTreeBudget LinkCut.PathProg.pathC L (lctExpose pathPayload curTree slot).n +
          Rtree.phi tok.treeHeap treeTok1 s7.mem at hc2
      change c3 + Rtree.phi tok.treeHeap treeTok3 st3.mem ≤
        pathTreeBudget LinkCut.PathProg.pathC L
            (lctExpose pathPayload (lctExpose pathPayload curTree slot) slot).n +
          Rtree.phi tok.treeHeap treeTok2 stR.mem at hc3
      rw [hcn, hphiEq] at hc1
      rw [htree1N, hphi1_s7] at hc2
      rw [htree2N, hphi2_R] at hc3
      dsimp only [L, Rtree] at hc1 hc2 hc3 hcR' ⊢
      omega

/-- Running `.loop (.reg 11) (detectTreeStep ...)` from `TreePhaseInv ... 1 rem phi`
terminates in `rem + 1` iterations with `cont = 0` and `rem = 0`. -/
private theorem detectTreeLoop_runs {w m V psi k epsExp drainUnit treeInit reset : ℕ}
    {F : MinRatioFormat w} {cfg : Alg2Config} {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)}
    {p : Program} {ω : ℕ → Bool} {opTree : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg F.limbs Rcore} {mem₀ : ℕ → ℕ}
    {root base heap₀ : ℕ} {B R : ℤ}
    (hfmt4 : F.fmt.limbBits = 4)
    (hrep : (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp drainUnit Rcore).rep
      root model tok mem₀)
    (hbelow : ∀ a, (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp drainUnit Rcore).foot
      root tok a → a < base)
    (hTreeImpl : (LinkCut.PathProg.pathRep 4 F.limbs LinkCut.PathProg.pathC).Implements w p
      treeInit opTree
      (pathTreeMachineContract F.fmt F.limbs LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc F.limbs)))
    (hReset : ∀ edge th, MeetsContract w p reset (detectResetContract w 4 edge th))
    (heps : 0 < cfg.ε) (hlen : ∀ e ∈ model.extG.E, 0 < model.extℓ e)
    (hcapB : 2 * ((2 * tok.tree.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 F.limbs : ℤ))
    (hthrB : ∀ e ∈ model.extG.E, |detectorThreshold F.fmt.precision cfg.ε (model.extℓ e)| ≤ B)
    (hfitThr : ∀ e ∈ model.extG.E,
      Num.Fits 4 F.limbs (-detectorThreshold F.fmt.precision cfg.ε (model.extℓ e)))
    (htreeWord : 2 * tok.tree.n + 1 < 2 ^ w)
    (htreeWidth : Nat.log 2 (2 * tok.tree.n + 1) ≤ 4 * F.limbs)
    (hbaseHeap : base + 1 + m ≤ heap₀)
    (hroom : heap₀ + ((treeReadySet model).card + 1) * detectTreeRoundSpace F.limbs < 2 ^ w)
    (hw10 : 10 < 2 ^ w) (hLpos : 0 < F.limbs) :
    ∀ rem phi s,
      TreePhaseInv (P := F.fmt.precision) (m := m) model tok mem₀ root base heap₀ B R 1 rem phi s →
      ∃ out cost phi',
        Runs w p ω (.loop (.reg 11) (detectTreeStep (opTree 6) (opTree 4) (opTree 5) reset))
          s .normal out cost ∧
        TreePhaseInv (P := F.fmt.precision) (m := m) model tok mem₀ root base heap₀ B R 0 0 phi' out ∧
        cost + phi' ≤ rem * (detectTreeStepBudget F.limbs tok.tree.n + 2) +
          detectTreeFinalBudget F.limbs tok.tree.n + 4 + phi := by
  intro rem
  induction rem with
  | zero =>
    intro phi s hInv
    have hr11 : s.regs 11 = 1 := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h11, _⟩ := hInv; exact h11
    obtain ⟨mid, c1, cont', rem', phi', hrStep, hInv', hbr⟩ :=
      detectTreeStep_runs hfmt4 hrep hbelow hTreeImpl hReset heps hlen hcapB hthrB hfitThr
        htreeWord htreeWidth hbaseHeap hroom hw10 hLpos hInv
    rcases hbr with ⟨_, hpos, _, _⟩ | ⟨rfl, _, rfl, hc1⟩
    · omega
    · have hr11' : mid.regs 11 = 0 := by
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h11, _⟩ := hInv'; exact h11
      have rExit : Runs w p ω (.loop (.reg 11) (detectTreeStep (opTree 6) (opTree 4) (opTree 5) reset))
          mid .normal mid 2 :=
        runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, hr11'], rfl, by simp [Expr.size]⟩)
      refine ⟨mid, c1 + 2 + 2, phi', runs_loop_iff.mpr (Or.inr (Or.inr
        ⟨1, mid, c1, 2, by simp [Expr.eval, hr11], by decide, hrStep, rExit, by simp [Expr.size]; omega⟩)),
        hInv', by omega⟩
  | succ k ih =>
    intro phi s hInv
    have hr11 : s.regs 11 = 1 := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h11, _⟩ := hInv; exact h11
    obtain ⟨mid, c1, cont', rem', phi1, hrStep, hInv1, hbr⟩ :=
      detectTreeStep_runs hfmt4 hrep hbelow hTreeImpl hReset heps hlen hcapB hthrB hfitThr
        htreeWord htreeWidth hbaseHeap hroom hw10 hLpos hInv
    rcases hbr with ⟨rfl, _, hrem', hc1⟩ | ⟨_, h0, _, _⟩
    · have hremK : rem' = k := by omega
      subst hremK
      obtain ⟨out, cRest, phi', hrRest, hInvOut, hcRest⟩ := ih phi1 mid hInv1
      refine ⟨out, c1 + cRest + 2, phi', runs_loop_iff.mpr (Or.inr (Or.inr
        ⟨1, mid, c1, cRest, by simp [Expr.eval, hr11], by decide, hrStep, hrRest,
          by simp [Expr.size]; omega⟩)), hInvOut, ?_⟩
      rw [Nat.succ_mul]; omega
    · omega

/-- Full tree phase of `Detect`: emits all ready tree edges in `treeReadySet model` without
duplicates into `base + 1 ..`, resets their LCT detectors to `-detectorThreshold`, preserves
`PathTreeNumericInv _ _ B R`, and bounds amortized cost by
`(treeReadySet model).card * (detectTreeStepBudget L n + 2) + detectTreeFinalBudget L n + 7`. -/
theorem detectTreePhaseBody_runs {w m V psi k epsExp drainUnit treeInit reset : ℕ}
    {F : MinRatioFormat w} {cfg : Alg2Config} {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)}
    {p : Program} {ω : ℕ → Bool} {opTree : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg F.limbs Rcore} {st : State}
    {root base heap₀ : ℕ} {B R : ℤ}
    (hfmt4 : F.fmt.limbBits = 4)
    (hrep : (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp drainUnit Rcore).rep
      root model tok st.mem)
    (hbelow : ∀ a, (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp drainUnit Rcore).foot
      root tok a → a < base)
    (hTreeImpl : (LinkCut.PathProg.pathRep 4 F.limbs LinkCut.PathProg.pathC).Implements w p
      treeInit opTree
      (pathTreeMachineContract F.fmt F.limbs LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc F.limbs)))
    (hReset : ∀ edge th, MeetsContract w p reset (detectResetContract w 4 edge th))
    (heps : 0 < cfg.ε) (hlen : ∀ e ∈ model.extG.E, 0 < model.extℓ e)
    (hnum : PathTreeNumericInv tok.tree tok.trees B R)
    (hcapB : 2 * ((2 * tok.tree.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 F.limbs : ℤ))
    (hthrB : ∀ e ∈ model.extG.E, |detectorThreshold F.fmt.precision cfg.ε (model.extℓ e)| ≤ B)
    (hfitThr : ∀ e ∈ model.extG.E,
      Num.Fits 4 F.limbs (-detectorThreshold F.fmt.precision cfg.ε (model.extℓ e)))
    (htreeWord : 2 * tok.tree.n + 1 < 2 ^ w)
    (htreeWidth : Nat.log 2 (2 * tok.tree.n + 1) ≤ 4 * F.limbs)
    (hr0 : st.regs 0 = root) (hr1 : st.regs 1 = base) (hr2 : st.regs 2 = m)
    (hr3 : st.regs 3 = base + 1) (hr4 : st.regs 4 = heap₀) (hr5 : st.regs 5 = F.limbs)
    (hr6 : st.regs 6 = tok.treeHeap) (hr7 : st.regs 7 = tok.names)
    (hr8 : st.regs 8 = tok.inverse) (hr9 : st.regs 9 = tok.slotThresholds)
    (hbaseHeap : base + 1 + m ≤ heap₀) (hz0 : ZeroFrom st.mem heap₀)
    (hroom : heap₀ + ((treeReadySet model).card + 1) * detectTreeRoundSpace F.limbs < 2 ^ w)
    (hw10 : 10 < 2 ^ w) (hLpos : 0 < F.limbs) :
    let L := F.limbs
    let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
    ∃ out cost treeRep curHeap curTree curTrees curTreeTok,
      Runs w p ω (detectTreePhaseBody (opTree 6) (opTree 4) (opTree 5) reset) st .normal out cost ∧
      cost + Rtree.phi tok.treeHeap curTreeTok out.mem ≤
        (treeReadySet model).card * (detectTreeStepBudget L tok.tree.n + 2) +
          detectTreeFinalBudget L tok.tree.n + 7 + Rtree.phi tok.treeHeap tok.treeTok st.mem ∧
      out.regs 0 = root ∧ out.regs 1 = base ∧ out.regs 2 = m ∧
      out.regs 3 = base + 1 + treeRep.length ∧ out.regs 4 = curHeap ∧ out.regs 5 = L ∧
      treeRep.Nodup ∧ treeRep.toFinset = treeReadySet model ∧
      ListAt out.mem (base + 1) treeRep ∧
      heap₀ ≤ curHeap ∧
      curHeap ≤ heap₀ + ((treeReadySet model).card + 1) * detectTreeRoundSpace L ∧
      ZeroFrom out.mem curHeap ∧
      curTree.n = tok.tree.n ∧
      LctInvWith pathPayload curTree curTrees tok.free tok.depth ∧
      PathTreeNumericInv curTree curTrees B R ∧
      Rtree.rep tok.treeHeap curTree curTreeTok out.mem ∧
      (∀ a, Rtree.foot tok.treeHeap curTreeTok a →
        Rtree.foot tok.treeHeap tok.treeTok a ∨ (heap₀ ≤ a ∧ a < curHeap)) ∧
      (∀ a < heap₀, ¬ Rtree.foot tok.treeHeap tok.treeTok a →
        (a < base + 1 ∨ base + 1 + treeRep.length ≤ a) → out.mem a = st.mem a) ∧
      (∀ e ∈ model.extG.E,
        let ei := model.extToInt e
        ei ∈ model.chain.toTreeChain.chainTree.E →
        let slot := st.mem (tok.slots + ei)
        ∃ val : PathEdgeValue, ∃ account : ℤ,
          (slot, some val) ∈ forestPairs pathPayload curTree.splay curTrees ∧
          (val.originalFlow : ℝ) / (2 : ℝ) ^ F.fmt.precision = model.flow e ∧
          (account : ℝ) / (2 : ℝ) ^ F.fmt.precision =
            (algorithm2_detect cfg model).2.detectAccum e ∧
          val.detector = account - detectorThreshold F.fmt.precision cfg.ε (model.extℓ e) ∧
          (val.originalGradient : ℝ) / (2 : ℝ) ^ F.fmt.precision = model.extg e ∧
          (val.length : ℝ) / (2 : ℝ) ^ F.fmt.precision = model.extℓ e ∧
          (val.forward = true →
            inducedSubPar pathPayload curTree.splay curTrees (vid (model.chain.toTreeChain.chainTree.head ei)) = slot ∧
            inducedSubPar pathPayload curTree.splay curTrees slot = vid (model.chain.toTreeChain.chainTree.tail ei)) ∧
          (val.forward = false →
            inducedSubPar pathPayload curTree.splay curTrees (vid (model.chain.toTreeChain.chainTree.tail ei)) = slot ∧
            inducedSubPar pathPayload curTree.splay curTrees slot = vid (model.chain.toTreeChain.chainTree.head ei))) ∧
      (∀ slot val, isEdgeSlot curTree.n slot →
        (slot, some val) ∈ forestPairs pathPayload curTree.splay curTrees →
        let ei := st.mem (tok.names + slot)
        let e := model.intToExt ei
        ei < tok.intCap ∧ ei ∈ model.chain.toTreeChain.chainTree.E ∧
        st.mem (tok.slots + ei) = slot ∧ e ∈ model.extG.E ∧ model.extToInt e = ei) ∧
      TreeEditNamedSlots curTree curTrees model.chain.toTreeChain.chainTree
        (fun f => st.mem (tok.slots + f)) (fun k => st.mem (tok.names + k)) := by
  dsimp only
  let L := F.limbs
  let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
  have hrep0 := hrep
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hlct0, htrep0, hedgeAcc, _, _, _, _, hwire0, _⟩ := hrep
  let st1 : State := { st with regs := Function.update st.regs 11 1 }
  have rSet1 : Runs w p ω (.assign 11 (.const 1)) st .normal st1 2 :=
    runs_assign_iff.mpr ⟨1, by simp [Expr.eval, show 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hInv0 : TreePhaseInv (P := F.fmt.precision) (m := m) model tok st.mem root base heap₀ B R
      1 (treeReadySet model).card (Rtree.phi tok.treeHeap tok.treeTok st.mem) st1 := by
    refine ⟨[], heap₀, tok.tree, tok.trees, tok.treeTok,
      by simp [st1, hr0], by simp [st1, hr1], by simp [st1, hr2], by simp [st1, hr3],
      by simp [st1, hr4], by simp [st1, hr5], by simp [st1, hr6], by simp [st1, hr7],
      by simp [st1, hr8], by simp [st1, hr9], by simp [st1], List.nodup_nil,
      by simp, by simp, fun _ h => by simp at h, le_rfl, by simp, hz0, rfl, hlct0, hnum,
      htrep0, rfl, fun _ ha => Or.inl ha, fun _ _ _ _ => rfl, ?_, hedgeAcc.2, hwire0.2.2.2.1⟩
    intro e heE; dsimp only; intro heInT
    have hbr := (hedgeAcc.1 e heE).2.2
    rw [ite_eq_left heInT] at hbr
    obtain ⟨_, _, _, _, val, acc, hp, hfl, hac, hd⟩ := hbr
    have hgl := hwire0.2.2.2.2 e heE; dsimp only at hgl; rw [ite_eq_left heInT] at hgl
    obtain ⟨hgrad, hlen, hft, hff⟩ := hgl val hp
    exact ⟨val, acc, hp, hfl, by simpa [resetReported] using hac, hd, hgrad, hlen, hft, hff⟩
  obtain ⟨out, cLoop, phi', hrLoop, hInvOut, hcLoop⟩ :=
    detectTreeLoop_runs hfmt4 hrep0 hbelow hTreeImpl hReset heps hlen hcapB hthrB hfitThr
      htreeWord htreeWidth hbaseHeap hroom hw10 hLpos
      (treeReadySet model).card (Rtree.phi tok.treeHeap tok.treeTok st.mem) st1 hInv0
  obtain ⟨treeRep, curHeap, curTree, curTrees, curTreeTok,
    ho0, ho1, ho2, ho3, ho4, ho5, _, _, _, _, _,
    hnd, hsub, hdiff0, hlist, hcurLo, hcurHi, hzCur, hcn, hlct, hnumOut, htrepOut, hphiOut,
    hfootOut, hframeOut, htreeAccOut, htreeRevOut, hnsOut⟩ := hInvOut
  have hfinEq : treeRep.toFinset = treeReadySet model := by
    have hsub2 : treeReadySet model ⊆ treeRep.toFinset :=
      Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hdiff0)
    exact Finset.Subset.antisymm hsub hsub2
  have hlenEq : treeRep.length = (treeReadySet model).card := by
    rw [← List.toFinset_card_of_nodup hnd, hfinEq]
  refine ⟨out, 2 + cLoop + 1, treeRep, curHeap, curTree, curTrees, curTreeTok,
    runs_seq_iff.mpr (Or.inr ⟨st1, 2, cLoop, rSet1, hrLoop, rfl⟩),
    by dsimp only [L, Rtree] at hcLoop ⊢; rw [hphiOut]; omega,
    ho0, ho1, ho2, ho3, ho4, ho5,
    hnd, hfinEq, hlist, hcurLo, by rw [← hlenEq]; simpa using hcurHi,
    hzCur, hcn, hlct, hnumOut, htrepOut, hfootOut, hframeOut, ?_, htreeRevOut, hnsOut⟩
  intro e heE heInT
  obtain ⟨val, acc, hp, hfl, hac, hd, hg, hl⟩ := htreeAccOut e heE heInT
  exact ⟨val, acc, hp, hfl,
    hac.trans (hfinEq ▸ resetReported_treeReadySet_eq model heE heInT), hd, hg, hl⟩

end MinCostFlow.MinRatio
