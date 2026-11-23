module

public import MinCostFlow.MinRatio.WireSelectCancelState
import WordRAM.Tactic

/-!
# Verification of one `(i, j)` pair-cancellation step (`cancelPairStep_runs`)

Verifies the body of one `(i, j)` pair test inside `cancelPairInnerBody` (`WireSelectQuery.lean`,
Algorithm 2, page 29): four guarded `opTree 3` (`PathSummary`) calls on `(a, b)`, `(c, d)`,
`(a, d)`, `(c, b)`, followed by `pathCompareExchangeBody` and the conditional flag store
`mem[flagPtr] := 1`. Maintains `CancelState` with zero footprint growth, `≤ 4 * pathApplySpace L + 2 * L`
scratch words, and `≤ 4 * pathTreeBudget + 117 * L + 370` amortized steps.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine SparseCore.Program DynSpanner.Program LinkCut.PathProg

set_option maxHeartbeats 600000 in
/-- Executes one `(i, j)` pair comparison + conditional destination swap in `cancelPairInnerBody`
(up to the recursive `.call 17 self`). -/
theorem cancelPairStep_runs
    {w L P m V psi k epsExp drainUnit initTree cmpExch
      root descBase pathsBase K i j flagPtr work size
      levelsEnd0 intCap0 handle0 treeHeap0 maxEdges maxPaths : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {opTree : ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {loc : SelectHeapLoc}
    {ω : ℕ → Bool} {mem : ℕ → ℕ} {pos : ℕ} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {B R : ℤ} {pathsInit paths : List (ℕ × ℕ)}
    {route : ℕ → List (ℕ × ℕ)} {steps : ℕ}
    (hw16 : 16 < 2 ^ w)
    (hfmt4 : fmt.limbBits = 4)
    (hlocalCore : Rcore.Local)
    (hTreeImpl : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).Implements w p initTree opTree
      (pathTreeMachineContract fmt L LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc L)))
    (hCmpExch : ∀ ab cd ad cb : ℤ,
      MeetsContract w p cmpExch (pathCompareExchangeContract w 4 ab cd ad cb))
    (hFsub : model.chain.toTreeChain.chainTree.E ⊆ (model.chain.G 0).E)
    (hlogW : Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L)
    (hmaxE1 : 1 ≤ maxEdges) (hmaxEP : 2 * maxEdges ≤ maxPaths)
    (hcapE : 2 * (((maxEdges + maxPaths * model.extG.n : ℕ) : ℤ) * B) < (Num.capacity 4 L : ℤ))
    (hcapT : 2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ))
    (hlocEnd : loc.endAddr ≤ descBase)
    (h2nW : 2 * model.extG.n + 1 < 2 ^ w) (htreeHW : treeHeap0 < 2 ^ w)
    (hroom : work + (4 * pathApplySpace L + 2 * L) < 2 ^ w)
    (hij : i < j) (hj : j < K)
    (hS : CancelState P m V psi k epsExp drainUnit loc root descBase pathsBase K flagPtr size model B R pathsInit
      levelsEnd0 intCap0 handle0 treeHeap0 mem tok paths route steps work) :
    let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
    let F := model.chain.toTreeChain.chainTree
    let ℓint := fun ei => model.extℓ (model.intToExt ei)
    let hi : i < paths.length := hS.hlen.symm ▸ hij.trans hj
    let hj' : j < paths.length := hS.hlen.symm ▸ hj
    let a := (paths[i]'hi).1; let b := (paths[i]'hi).2
    let c := (paths[j]'hj').1; let d := (paths[j]'hj').2
    ∃ (work' cStep : ℕ) (st' : State) (tok' : SolverToken cfg L Rcore)
      (paths' : List (ℕ × ℕ)) (route' : ℕ → List (ℕ × ℕ)) (steps' : ℕ),
      Runs w p ω
        (.assign 8 (.load (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 4)))) ;;
         .assign 9 (.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 4))) (.const 1))) ;;
         .assign 10 (.load (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 5)))) ;;
         .assign 11 (.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 5))) (.const 1))) ;;
         .assign 12 (.reg 7) ;;
         .call 7 (opTree 3) [.reg 0, .bin .add (.reg 8) (.const 1), .bin .add (.reg 9) (.const 1), .reg 7] ;;
         .assign 18 (.bin .add (.reg 12) (.bin .mul (.const 2) (.reg 1))) ;;
         .cond (.bin .lt (.reg 7) (.reg 18)) (.assign 7 (.reg 18)) .nop ;;
         .assign 13 (.reg 7) ;;
         .call 7 (opTree 3) [.reg 0, .bin .add (.reg 10) (.const 1), .bin .add (.reg 11) (.const 1), .reg 7] ;;
         .assign 18 (.bin .add (.reg 13) (.bin .mul (.const 2) (.reg 1))) ;;
         .cond (.bin .lt (.reg 7) (.reg 18)) (.assign 7 (.reg 18)) .nop ;;
         .assign 14 (.reg 7) ;;
         .call 7 (opTree 3) [.reg 0, .bin .add (.reg 8) (.const 1), .bin .add (.reg 11) (.const 1), .reg 7] ;;
         .assign 18 (.bin .add (.reg 14) (.bin .mul (.const 2) (.reg 1))) ;;
         .cond (.bin .lt (.reg 7) (.reg 18)) (.assign 7 (.reg 18)) .nop ;;
         .assign 15 (.reg 7) ;;
         .call 7 (opTree 3) [.reg 0, .bin .add (.reg 10) (.const 1), .bin .add (.reg 9) (.const 1), .reg 7] ;;
         .assign 18 (.bin .add (.reg 15) (.bin .mul (.const 2) (.reg 1))) ;;
         .cond (.bin .lt (.reg 7) (.reg 18)) (.assign 7 (.reg 18)) .nop ;;
         .call 16 cmpExch
           [.bin .add (.reg 12) (.reg 1),
            .bin .add (.reg 13) (.reg 1),
            .bin .add (.reg 14) (.reg 1),
            .bin .add (.reg 15) (.reg 1),
            .reg 1,
            .bin .add (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 4))) (.const 1),
            .bin .add (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 5))) (.const 1),
            .reg 7] ;;
         .assign 7 (.bin .add (.reg 7) (.bin .mul (.const 2) (.reg 1))) ;;
         .cond (.reg 16) (.store (.reg 6) (.const 1)) .nop)
        (startState [treeHeap0, L, pathsBase, K, i, j, flagPtr, work] mem pos) .normal st' cStep ∧
      st'.regs 0 = treeHeap0 ∧ st'.regs 1 = L ∧ st'.regs 2 = pathsBase ∧ st'.regs 3 = K ∧
      st'.regs 4 = i ∧ st'.regs 5 = j ∧ st'.regs 6 = flagPtr ∧ st'.regs 7 = work' ∧
      work ≤ work' ∧ work' ≤ work + (4 * pathApplySpace L + 2 * L) ∧
      CancelState P m V psi k epsExp drainUnit loc root descBase pathsBase K flagPtr size model B R pathsInit
        levelsEnd0 intCap0 handle0 treeHeap0 st'.mem tok' paths' route' steps' work' ∧
      PreservesLevelMeta tok tok' mem st'.mem ∧
      (∀ x < flagPtr, (x < pathsBase ∨ pathsBase + 2 * K ≤ x) →
        ¬ Rrep.foot root tok x → st'.mem x = mem x) ∧
      (∀ x, Rrep.foot root tok' x → Rrep.foot root tok x) ∧
      ((walkLength ℓint (F.forestPath a d) + walkLength ℓint (F.forestPath c b) <
          walkLength ℓint (F.forestPath a b) + walkLength ℓint (F.forestPath c d) ∧
        st'.mem flagPtr = 1 ∧ steps' = steps + 1) ∨
       (walkLength ℓint (F.forestPath a b) + walkLength ℓint (F.forestPath c d) ≤
          walkLength ℓint (F.forestPath a d) + walkLength ℓint (F.forestPath c b) ∧
        st'.mem flagPtr = mem flagPtr ∧ paths' = paths ∧ route' = route ∧ steps' = steps)) ∧
      cStep + Rrep.phi root tok' st'.mem ≤
        4 * pathTreeBudget LinkCut.PathProg.pathC L model.extG.n + 117 * L + 370 +
          Rrep.phi root tok mem := by
  dsimp only
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  let F := model.chain.toTreeChain.chainTree
  let ℓint := fun ei => model.extℓ (model.intToExt ei)
  have hi : i < paths.length := by rw [hS.hlen]; exact hij.trans hj
  have hj' : j < paths.length := by rw [hS.hlen]; exact hj
  set a := (paths[i]'hi).1; set b := (paths[i]'hi).2
  set c := (paths[j]'hj').1; set d := (paths[j]'hj').2
  have hpi := hS.hPtOk paths[i] (List.getElem_mem hi)
  have hpj := hS.hPtOk paths[j] (List.getElem_mem hj')
  have hac : F.Connected a c := hS.hSameComp _ (List.getElem_mem hi) _ (List.getElem_mem hj')
  have had : F.Connected a d := MGraph.connected_trans hac hpj.2.2
  have hcb : F.Connected c b := MGraph.connected_trans (MGraph.connected_symm hac) hpi.2.2
  have hSpaceDef : pathApplySpace L = 20 * LinkCut.PathProg.treeLimbs L + 100 := rfl
  have h2LleSpace : 2 * L ≤ pathApplySpace L := by
    rw [hSpaceDef]; unfold LinkCut.PathProg.treeLimbs; omega
  have hdescWork : descBase ≤ work := by
    have := hS.hDescLtPt; have := hS.hPtLt; have := hS.hFlagLt; omega
  have hLW : L < 2 ^ w := by omega
  have hTreeStep : ∀ {u v s0 : ℕ} {mA : ℕ → ℕ} {tA : SolverToken cfg L Rcore} {posA : ℕ}
      (htH : tA.treeHeap = treeHeap0)
      (hrA : Rrep.rep root model tA mA)
      (hnumA : PathTreeNumericInv tA.tree tA.trees B R)
      (hoffA : OffTreeRecInv model L mA tA.edgeRecords B)
      (hBdA : OffTreeRecBound model L mA tA.edgeRecords B)
      (hMatchA : SelectHeapMatchesChain mA loc 4 P model.chain.toTreeChain model.chain.g model.chain.ℓ size)
      (hlocDA : ∀ x, loc.hb ≤ x → x < loc.endAddr → ¬ Rrep.foot root tA x)
      (hbelA : ∀ x, Rrep.foot root tA x → x < s0)
      (hdscA : descBase ≤ s0)
      (ht18A : ∀ x, tA.tag x = 18 → x < descBase)
      (hzA : ZeroFrom mA s0)
      (hrmA : s0 + pathApplySpace L < 2 ^ w)
      (huA : u < model.extG.n) (hvA : v < model.extG.n) (hcA : F.Connected u v),
      ∃ (bT : Stmt) (oT : Outcome) (stT : State) (cT : ℕ) (tB : SolverToken cfg L Rcore) (zVal : ℤ),
        p.procs[opTree 3]? = some bT ∧
        Runs w p ω bT (startState [treeHeap0, u + 1, v + 1, s0] mA posA) oT stT cT ∧
        s0 ≤ oT.value ∧
        s0 + 2 * L ≤ max oT.value (s0 + 2 * L) ∧
        max oT.value (s0 + 2 * L) ≤ s0 + pathApplySpace L ∧
        PathIntAt stT.mem (s0 + L) 4 L zVal ∧
        (zVal : ℝ) / (2 : ℝ) ^ P = walkLength ℓint (F.forestPath u v) ∧
        |zVal| ≤ (model.extG.n : ℤ) * B ∧
        tB.levelsEnd = tA.levelsEnd ∧ tB.intCap = tA.intCap ∧
        tB.handle = tA.handle ∧ tB.treeHeap = treeHeap0 ∧
        (∀ x, tB.tag x = 18 → x < descBase) ∧
        Rrep.rep root model tB stT.mem ∧
        PreservesLevelMeta tA tB mA stT.mem ∧
        SelectHeapMatchesChain stT.mem loc 4 P model.chain.toTreeChain model.chain.g model.chain.ℓ size ∧
        PathTreeNumericInv tB.tree tB.trees B R ∧
        OffTreeRecInv model L stT.mem tB.edgeRecords B ∧
        OffTreeRecBound model L stT.mem tB.edgeRecords B ∧
        ZeroFrom stT.mem (max oT.value (s0 + 2 * L)) ∧
        (∀ x < s0, ¬ Rrep.foot root tA x → stT.mem x = mA x) ∧
        (∀ x, Rrep.foot root tB x → Rrep.foot root tA x) ∧
        cT + Rrep.phi root tB stT.mem ≤
          pathTreeBudget LinkCut.PathProg.pathC L model.extG.n + Rrep.phi root tA mA := by
    intro u v s0 mA tA posA htH hrA hnumA hoffA hBdA hMatchA hlocDA hbelA hdscA ht18A hzA hrmA huA hvA hcA
    obtain ⟨bT, oT, stT, cT, tB, hbT, hrT, hLo, _, hPI, hLen, hAbs, hlev, hcap, hhdl, htHB,
      ht18B, hrB, hmetaB, hMatchB, hnumB, hoffB, hBdB, hzB, hWNLe, hFrB, hFtB, hCostB⟩ :=
      solverStateRep_update_treeSummary (loc := loc) hfmt4 hlocalCore hTreeImpl hrA hnumA hoffA hBdA
        hMatchA hFsub hlogW hcapT hlocEnd hlocDA hbelA hdscA ht18A hzA hrmA h2nW (htH ▸ htreeHW) huA hvA hcA
    exact ⟨bT, oT, stT, cT, tB, (lctPathSummary pathPayload tA.tree (vid u) (vid v)).2.length,
      hbT, htH ▸ hrT, hLo, le_max_right _ _, hWNLe, hPI, hLen, hAbs, hlev, hcap, hhdl,
      htHB.trans htH, ht18B, hrB, hmetaB, hMatchB, hnumB, hoffB, hBdB, hzB, hFrB, hFtB, hCostB⟩
  -- 1. Four `opTree 3` calls: `(a, b)`, `(c, d)`, `(a, d)`, `(c, b)`
  obtain ⟨b1, o1, st1, c1, tok1, ab, hb1, hr1, ho1Lo, hw1Lo, hw1Hi, hPI1, hEq1, hAbs1,
      hlev1, hcap1, hhdl1, htH1, ht18_1, hrep1, hmeta1, hMatch1, hnum1, hoff1, hBd1, hz1, hfr1, hft1, hc1⟩ :=
    hTreeStep (posA := pos) hS.htreeH hS.hrep hS.hnum hS.hoff hS.hBd hS.hMatch hS.hlocDisj hS.hbelow hdescWork
      hS.htag18 hS.hz (by omega) hpi.1 hpi.2.1 hpi.2.2
  set w1 := max o1.value (work + 2 * L)
  have hlocD1 : ∀ x, loc.hb ≤ x → x < loc.endAddr → ¬ Rrep.foot root tok1 x := fun x h1 h2 hf =>
    hS.hlocDisj x h1 h2 (hft1 x hf)
  have hbel1 : ∀ x, Rrep.foot root tok1 x → x < w1 := fun x hf =>
    lt_of_lt_of_le (hS.hbelow x (hft1 x hf)) (by omega)
  obtain ⟨b2, o2, st2, c2, tok2, cd, hb2, hr2, ho2Lo, hw2Lo, hw2Hi, hPI2, hEq2, hAbs2,
      hlev2, hcap2, hhdl2, htH2, ht18_2, hrep2, hmeta2, hMatch2, hnum2, hoff2, hBd2, hz2, hfr2, hft2, hc2⟩ :=
    hTreeStep (posA := st1.pos) htH1 hrep1 hnum1 hoff1 hBd1 hMatch1 hlocD1 hbel1 (by omega)
      ht18_1 hz1 (by omega) hpj.1 hpj.2.1 hpj.2.2
  set w2 := max o2.value (w1 + 2 * L)
  have hlocD2 : ∀ x, loc.hb ≤ x → x < loc.endAddr → ¬ Rrep.foot root tok2 x := fun x h1 h2 hf =>
    hlocD1 x h1 h2 (hft2 x hf)
  have hbel2 : ∀ x, Rrep.foot root tok2 x → x < w2 := fun x hf =>
    lt_of_lt_of_le (hbel1 x (hft2 x hf)) (by omega)
  obtain ⟨b3, o3, st3, c3, tok3, ad, hb3, hr3, ho3Lo, hw3Lo, hw3Hi, hPI3, hEq3, hAbs3,
      hlev3, hcap3, hhdl3, htH3, ht18_3, hrep3, hmeta3, hMatch3, hnum3, hoff3, hBd3, hz3, hfr3, hft3, hc3⟩ :=
    hTreeStep (posA := st2.pos) htH2 hrep2 hnum2 hoff2 hBd2 hMatch2 hlocD2 hbel2 (by omega)
      ht18_2 hz2 (by omega) hpi.1 hpj.2.1 had
  set w3 := max o3.value (w2 + 2 * L)
  have hlocD3 : ∀ x, loc.hb ≤ x → x < loc.endAddr → ¬ Rrep.foot root tok3 x := fun x h1 h2 hf =>
    hlocD2 x h1 h2 (hft3 x hf)
  have hbel3 : ∀ x, Rrep.foot root tok3 x → x < w3 := fun x hf =>
    lt_of_lt_of_le (hbel2 x (hft3 x hf)) (by omega)
  obtain ⟨b4, o4, st4, c4, tok4, cb, hb4, hr4, ho4Lo, hw4Lo, hw4Hi, hPI4, hEq4, hAbs4,
      hlev4, hcap4, hhdl4, htH4, ht18_4, hrep4, hmeta4, hMatch4, hnum4, hoff4, hBd4, hz4, hfr4, hft4, hc4⟩ :=
    hTreeStep (posA := st3.pos) htH3 hrep3 hnum3 hoff3 hBd3 hMatch3 hlocD3 hbel3 (by omega)
      ht18_3 hz3 (by omega) hpj.1 hpi.2.1 hcb
  set w4 := max o4.value (w3 + 2 * L)
  have hft04 : ∀ x, Rrep.foot root tok4 x → Rrep.foot root tok x := fun x hf =>
    hft1 x (hft2 x (hft3 x (hft4 x hf)))
  have hnotF4 : ∀ x, work ≤ x → ¬ Rrep.foot root tok1 x ∧ ¬ Rrep.foot root tok2 x ∧
      ¬ Rrep.foot root tok3 x ∧ ¬ Rrep.foot root tok4 x := fun x hx =>
    ⟨fun hf => by have := hS.hbelow x (hft1 x hf); omega,
     fun hf => by have := hS.hbelow x (hft1 x (hft2 x hf)); omega,
     fun hf => by have := hS.hbelow x (hft1 x (hft2 x (hft3 x hf))); omega,
     fun hf => by have := hS.hbelow x (hft04 x hf); omega⟩
  have hfr04 : ∀ x < work, ¬ Rrep.foot root tok x → st4.mem x = mem x := fun x hx hnf =>
    (hfr4 x (by omega) (fun hf => hnf (hft1 x (hft2 x (hft3 x hf))))).trans
      ((hfr3 x (by omega) (fun hf => hnf (hft1 x (hft2 x hf)))).trans
        ((hfr2 x (by omega) (fun hf => hnf (hft1 x hf))).trans (hfr1 x hx hnf)))
  -- All 4 `PathIntAt` blocks survive untouched in `st4.mem`
  have hPI1_4 : PathIntAt st4.mem (work + L) 4 L ab := hPI1.congr fun k hk =>
    (hfr4 _ (by omega) (hnotF4 _ (by omega)).2.2.1).trans
      ((hfr3 _ (by omega) (hnotF4 _ (by omega)).2.1).trans
        (hfr2 _ (by omega) (hnotF4 _ (by omega)).1))
  have hPI2_4 : PathIntAt st4.mem (w1 + L) 4 L cd := hPI2.congr fun k hk =>
    (hfr4 _ (by omega) (hnotF4 _ (by omega)).2.2.1).trans
      (hfr3 _ (by omega) (hnotF4 _ (by omega)).2.1)
  have hPI3_4 : PathIntAt st4.mem (w2 + L) 4 L ad := hPI3.congr fun k hk =>
    hfr4 _ (by omega) (hnotF4 _ (by omega)).2.2.1
  have hPtAt4 : PathEndpointsAt st4.mem pathsBase paths := fun k hk => by
    have hkK : k < K := hS.hlen ▸ hk
    have h0 := hS.hPtAt k hk
    exact ⟨(hfr04 _ (by have := hS.hPtLt; have := hS.hFlagLt; omega) (hS.hnfPt (2 * k) (by omega))).trans h0.1,
      (hfr04 _ (by have := hS.hPtLt; have := hS.hFlagLt; omega) (hS.hnfPt (2 * k + 1) (by omega))).trans h0.2⟩
  -- 2. Call `cmpExch` (`pathCompareExchangeContract w 4 ab cd ad cb`)
  have hFits1 : Num.Fits 4 L (ab + cd) :=
    fits_sum_two_paths hS.hnum.1 hmaxE1 hmaxEP hcapE hAbs1 hAbs2
  have hFits2 : Num.Fits 4 L (ad + cb) :=
    fits_sum_two_paths hS.hnum.1 hmaxE1 hmaxEP hcapE hAbs3 hAbs4
  have hCmpPre : (pathCompareExchangeContract w 4 ab cd ad cb).pre
      [work + L, w1 + L, w2 + L, w3 + L, L, pathsBase + 2 * i + 1, pathsBase + 2 * j + 1, w4] st4.mem := by
    refine ⟨work + L, w1 + L, w2 + L, w3 + L, L, pathsBase + 2 * i + 1, pathsBase + 2 * j + 1, w4,
      rfl, by have := hS.hPtLt; have := hS.hFlagLt; omega,
      by have := hS.hPtLt; have := hS.hFlagLt; omega,
      by rw [(hPtAt4 i hi).2]; exact lt_trans hpi.2.1 (by omega),
      by rw [(hPtAt4 j hj').2]; exact lt_trans hpj.2.1 (by omega),
      work + L, w1 + L, w2 + L, w3 + L, L, w4, rfl, by omega,
      by omega, by omega, by omega, by omega, hPI1_4, hPI2_4, hPI3_4, hPI4, hFits1, hFits2,
      hz4, by omega⟩
  obtain ⟨bCmp, hbCmp, oCmp, stCmp, cCmp, hrCmp, hCmpPost, hcCmp⟩ :=
    hCmpExch ab cd ad cb
      [work + L, w1 + L, w2 + L, w3 + L, L, pathsBase + 2 * i + 1, pathsBase + 2 * j + 1, w4]
      st4.mem st4.pos ω
      (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals (have := hS.hPtLt; have := hS.hFlagLt; omega))
      hCmpPre
  have hCmpPairs := pathCompareExchange_pairs hi hj'
    (by have := hS.hlen; have := hS.hPtLt; have := hS.hFlagLt; omega) hPtAt4 hCmpPost
  obtain ⟨_, _, _, _, _, _, _, _, hEqArgs, hCmpRet, hCmpFrRaw, hzCmp⟩ := hCmpPost
  simp only [List.cons.injEq, and_true] at hEqArgs
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hEqArgs
  have hCmpFr : ∀ x < w4, x ≠ pathsBase + 2 * i + 1 → x ≠ pathsBase + 2 * j + 1 →
      stCmp.mem x = st4.mem x := fun x hx hne1 hne2 => by
    rw [hCmpFrRaw x hx]
    split_ifs with h
    · rw [Function.update_of_ne hne2, Function.update_of_ne hne1]
    · rfl
  have hcCmpLe : cCmp ≤ 117 * L + 155 := by
    simpa [pathCompareExchangeContract, List.getD_cons_zero, List.getD_cons_succ] using hcCmp
  set bit := oCmp.value
  set w5 := w4 + 2 * L
  set memFinal := if bit ≠ 0 then Function.update stCmp.mem flagPtr 1 else stCmp.mem
  have hLtIff : ad + cb < ab + cd ↔
      walkLength ℓint (F.forestPath a d) + walkLength ℓint (F.forestPath c b) <
        walkLength ℓint (F.forestPath a b) + walkLength ℓint (F.forestPath c d) :=
    scaled_lt_iff (by rw [Int.cast_add, add_div, hEq3, hEq4])
      (by rw [Int.cast_add, add_div, hEq1, hEq2])
  -- 3. Stitch the full statement chain explicitly
  have hRunBody : ∃ (regsF : ℕ → ℕ) (cStep : ℕ),
      Runs w p ω
        (.assign 8 (.load (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 4)))) ;;
         .assign 9 (.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 4))) (.const 1))) ;;
         .assign 10 (.load (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 5)))) ;;
         .assign 11 (.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 5))) (.const 1))) ;;
         .assign 12 (.reg 7) ;;
         .call 7 (opTree 3) [.reg 0, .bin .add (.reg 8) (.const 1), .bin .add (.reg 9) (.const 1), .reg 7] ;;
         .assign 18 (.bin .add (.reg 12) (.bin .mul (.const 2) (.reg 1))) ;;
         .cond (.bin .lt (.reg 7) (.reg 18)) (.assign 7 (.reg 18)) .nop ;;
         .assign 13 (.reg 7) ;;
         .call 7 (opTree 3) [.reg 0, .bin .add (.reg 10) (.const 1), .bin .add (.reg 11) (.const 1), .reg 7] ;;
         .assign 18 (.bin .add (.reg 13) (.bin .mul (.const 2) (.reg 1))) ;;
         .cond (.bin .lt (.reg 7) (.reg 18)) (.assign 7 (.reg 18)) .nop ;;
         .assign 14 (.reg 7) ;;
         .call 7 (opTree 3) [.reg 0, .bin .add (.reg 8) (.const 1), .bin .add (.reg 11) (.const 1), .reg 7] ;;
         .assign 18 (.bin .add (.reg 14) (.bin .mul (.const 2) (.reg 1))) ;;
         .cond (.bin .lt (.reg 7) (.reg 18)) (.assign 7 (.reg 18)) .nop ;;
         .assign 15 (.reg 7) ;;
         .call 7 (opTree 3) [.reg 0, .bin .add (.reg 10) (.const 1), .bin .add (.reg 9) (.const 1), .reg 7] ;;
         .assign 18 (.bin .add (.reg 15) (.bin .mul (.const 2) (.reg 1))) ;;
         .cond (.bin .lt (.reg 7) (.reg 18)) (.assign 7 (.reg 18)) .nop ;;
         .call 16 cmpExch
           [.bin .add (.reg 12) (.reg 1),
            .bin .add (.reg 13) (.reg 1),
            .bin .add (.reg 14) (.reg 1),
            .bin .add (.reg 15) (.reg 1),
            .reg 1,
            .bin .add (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 4))) (.const 1),
            .bin .add (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 5))) (.const 1),
            .reg 7] ;;
         .assign 7 (.bin .add (.reg 7) (.bin .mul (.const 2) (.reg 1))) ;;
         .cond (.reg 16) (.store (.reg 6) (.const 1)) .nop)
        (startState [treeHeap0, L, pathsBase, K, i, j, flagPtr, work] mem pos) .normal
        ⟨memFinal, regsF, stCmp.pos⟩ cStep ∧
      regsF 0 = treeHeap0 ∧ regsF 1 = L ∧ regsF 2 = pathsBase ∧ regsF 3 = K ∧
      regsF 4 = i ∧ regsF 5 = j ∧ regsF 6 = flagPtr ∧ regsF 7 = w5 ∧
      cStep ≤ c1 + c2 + c3 + c4 + cCmp + 215 := by
    let s0 := startState [treeHeap0, L, pathsBase, K, i, j, flagPtr, work] mem pos
    let rg0 := s0.regs
    let rgL1 := Function.update rg0 8 a
    let rgL2 := Function.update rgL1 9 b
    let rgL3 := Function.update rgL2 10 c
    let rgL4 := Function.update rgL3 11 d
    have hPiAt := hS.hPtAt i hi
    have hPjAt := hS.hPtAt j hj'
    have h2K_W : pathsBase + 2 * K < 2 ^ w := by have := hS.hPtLt; have := hS.hFlagLt; omega
    have hrL1 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 4)))))
        s0 .normal ⟨mem, rgL1, pos⟩ 7 :=
      runs_assign_iff.mpr ⟨a, by
        simp [Expr.eval, BinOp.eval, s0, startState, show 2 < 2 ^ w by omega,
          show 2 * i < 2 ^ w by omega, show pathsBase + 2 * i < 2 ^ w by omega, hPiAt.1, a],
        rfl, rfl, rfl⟩
    have hrL2 : Runs w p ω (.assign 9 (.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 4))) (.const 1))))
        ⟨mem, rgL1, pos⟩ .normal ⟨mem, rgL2, pos⟩ 9 :=
      runs_assign_iff.mpr ⟨b, by
        simp [Expr.eval, BinOp.eval, rgL1, rg0, s0, startState, show 1 < 2 ^ w by omega,
          show 2 < 2 ^ w by omega, show 2 * i < 2 ^ w by omega, show pathsBase + 2 * i < 2 ^ w by omega,
          show pathsBase + 2 * i + 1 < 2 ^ w by omega, hPiAt.2, b],
        rfl, rfl, rfl⟩
    have hrL3 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 5)))))
        ⟨mem, rgL2, pos⟩ .normal ⟨mem, rgL3, pos⟩ 7 :=
      runs_assign_iff.mpr ⟨c, by
        simp [Expr.eval, BinOp.eval, rgL2, rgL1, rg0, s0, startState, show 2 < 2 ^ w by omega,
          show 2 * j < 2 ^ w by omega, show pathsBase + 2 * j < 2 ^ w by omega, hPjAt.1, c],
        rfl, rfl, rfl⟩
    have hrL4 : Runs w p ω (.assign 11 (.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 5))) (.const 1))))
        ⟨mem, rgL3, pos⟩ .normal ⟨mem, rgL4, pos⟩ 9 :=
      runs_assign_iff.mpr ⟨d, by
        simp [Expr.eval, BinOp.eval, rgL3, rgL2, rgL1, rg0, s0, startState, show 1 < 2 ^ w by omega,
          show 2 < 2 ^ w by omega, show 2 * j < 2 ^ w by omega, show pathsBase + 2 * j < 2 ^ w by omega,
          show pathsBase + 2 * j + 1 < 2 ^ w by omega, hPjAt.2, d],
        rfl, rfl, rfl⟩
    obtain ⟨rgG1, cG1, hrG1, hfrG1, hG1_12, hG1_7, hcG1⟩ :=
      cancelPairGuard_runs (L := L) (rgA := rgL4) (rS := 12) (rU := 8) (rV := 9) (uV := a) (vV := b) (s0 := work) (oV := o1.value)
        hw16
        (by simp [rgL4, rgL3, rgL2, rgL1, rg0, s0, startState])
        (by simp [rgL4, rgL3, rgL2, rgL1, rg0, s0, startState])
        (by simp [rgL4, rgL3, rgL2, rgL1, rg0, s0, startState])
        (by simp [rgL4, rgL3, rgL2, rgL1]) (by simp [rgL4, rgL3, rgL2])
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by omega) (by omega) (by omega) hb1 rfl rfl rfl hr1
    obtain ⟨rgG2, cG2, hrG2, hfrG2, hG2_13, hG2_7, hcG2⟩ :=
      cancelPairGuard_runs (L := L) (rgA := rgG1) (rS := 13) (rU := 10) (rV := 11) (uV := c) (vV := d) (s0 := w1) (oV := o2.value)
        hw16
        (by rw [hfrG1 0 (by decide) (by decide) (by decide)]; simp [rgL4, rgL3, rgL2, rgL1, rg0, s0, startState])
        (by rw [hfrG1 1 (by decide) (by decide) (by decide)]; simp [rgL4, rgL3, rgL2, rgL1, rg0, s0, startState])
        hG1_7
        (by rw [hfrG1 10 (by decide) (by decide) (by decide)]; simp [rgL4, rgL3])
        (by rw [hfrG1 11 (by decide) (by decide) (by decide)]; simp [rgL4])
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by omega) (by omega) (by omega) hb2 rfl rfl rfl hr2
    obtain ⟨rgG3, cG3, hrG3, hfrG3, hG3_14, hG3_7, hcG3⟩ :=
      cancelPairGuard_runs (L := L) (rgA := rgG2) (rS := 14) (rU := 8) (rV := 11) (uV := a) (vV := d) (s0 := w2) (oV := o3.value)
        hw16
        (by rw [hfrG2 0 (by decide) (by decide) (by decide), hfrG1 0 (by decide) (by decide) (by decide)]
            simp [rgL4, rgL3, rgL2, rgL1, rg0, s0, startState])
        (by rw [hfrG2 1 (by decide) (by decide) (by decide), hfrG1 1 (by decide) (by decide) (by decide)]
            simp [rgL4, rgL3, rgL2, rgL1, rg0, s0, startState])
        hG2_7
        (by rw [hfrG2 8 (by decide) (by decide) (by decide), hfrG1 8 (by decide) (by decide) (by decide)]
            simp [rgL4, rgL3, rgL2, rgL1])
        (by rw [hfrG2 11 (by decide) (by decide) (by decide), hfrG1 11 (by decide) (by decide) (by decide)]
            simp [rgL4])
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by omega) (by omega) (by omega) hb3 rfl rfl rfl hr3
    obtain ⟨rgG4, cG4, hrG4, hfrG4, hG4_15, hG4_7, hcG4⟩ :=
      cancelPairGuard_runs (L := L) (rgA := rgG3) (rS := 15) (rU := 10) (rV := 9) (uV := c) (vV := b) (s0 := w3) (oV := o4.value)
        hw16
        (by rw [hfrG3 0 (by decide) (by decide) (by decide), hfrG2 0 (by decide) (by decide) (by decide),
              hfrG1 0 (by decide) (by decide) (by decide)]
            simp [rgL4, rgL3, rgL2, rgL1, rg0, s0, startState])
        (by rw [hfrG3 1 (by decide) (by decide) (by decide), hfrG2 1 (by decide) (by decide) (by decide),
              hfrG1 1 (by decide) (by decide) (by decide)]
            simp [rgL4, rgL3, rgL2, rgL1, rg0, s0, startState])
        hG3_7
        (by rw [hfrG3 10 (by decide) (by decide) (by decide), hfrG2 10 (by decide) (by decide) (by decide),
              hfrG1 10 (by decide) (by decide) (by decide)]
            simp [rgL4, rgL3])
        (by rw [hfrG3 9 (by decide) (by decide) (by decide), hfrG2 9 (by decide) (by decide) (by decide),
              hfrG1 9 (by decide) (by decide) (by decide)]
            simp [rgL4, rgL3, rgL2])
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by omega) (by omega) (by omega) hb4 rfl rfl rfl hr4
    have hG4_keep : ∀ r, r ≤ 6 → rgG4 r = rgL4 r := fun r hr => by
      rw [hfrG4 r (by omega) (by omega) (by omega), hfrG3 r (by omega) (by omega) (by omega),
          hfrG2 r (by omega) (by omega) (by omega), hfrG1 r (by omega) (by omega) (by omega)]
    have hG4_0 : rgG4 0 = treeHeap0 := by rw [hG4_keep 0 (by omega)]; simp [rgL4, rgL3, rgL2, rgL1, rg0, s0, startState]
    have hG4_1 : rgG4 1 = L := by rw [hG4_keep 1 (by omega)]; simp [rgL4, rgL3, rgL2, rgL1, rg0, s0, startState]
    have hG4_2 : rgG4 2 = pathsBase := by rw [hG4_keep 2 (by omega)]; simp [rgL4, rgL3, rgL2, rgL1, rg0, s0, startState]
    have hG4_3 : rgG4 3 = K := by rw [hG4_keep 3 (by omega)]; simp [rgL4, rgL3, rgL2, rgL1, rg0, s0, startState]
    have hG4_4 : rgG4 4 = i := by rw [hG4_keep 4 (by omega)]; simp [rgL4, rgL3, rgL2, rgL1, rg0, s0, startState]
    have hG4_5 : rgG4 5 = j := by rw [hG4_keep 5 (by omega)]; simp [rgL4, rgL3, rgL2, rgL1, rg0, s0, startState]
    have hG4_6 : rgG4 6 = flagPtr := by rw [hG4_keep 6 (by omega)]; simp [rgL4, rgL3, rgL2, rgL1, rg0, s0, startState]
    have hG4_12 : rgG4 12 = work := by
      rw [hfrG4 12 (by decide) (by decide) (by decide), hfrG3 12 (by decide) (by decide) (by decide),
          hfrG2 12 (by decide) (by decide) (by decide), hG1_12]
    have hG4_13 : rgG4 13 = w1 := by
      rw [hfrG4 13 (by decide) (by decide) (by decide), hfrG3 13 (by decide) (by decide) (by decide), hG2_13]
    have hG4_14 : rgG4 14 = w2 := by
      rw [hfrG4 14 (by decide) (by decide) (by decide), hG3_14]
    let rgC := Function.update rgG4 16 bit
    let rgW := Function.update rgC 7 w5
    have hrCallCmp : Runs w p ω
        (.call 16 cmpExch
          [.bin .add (.reg 12) (.reg 1), .bin .add (.reg 13) (.reg 1),
           .bin .add (.reg 14) (.reg 1), .bin .add (.reg 15) (.reg 1),
           .reg 1,
           .bin .add (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 4))) (.const 1),
           .bin .add (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 5))) (.const 1),
           .reg 7])
        ⟨st4.mem, rgG4, st4.pos⟩ .normal ⟨stCmp.mem, rgC, stCmp.pos⟩ (cCmp + 29) := by
      refine runs_call_iff.mpr
        ⟨[work + L, w1 + L, w2 + L, w3 + L, L, pathsBase + 2 * i + 1, pathsBase + 2 * j + 1, w4],
         bCmp, oCmp, stCmp, cCmp, ?_, hbCmp, hrCmp, rfl, ?_, ?_⟩
      · simp [evalArgs, Expr.eval, BinOp.eval, hG4_1, hG4_2, hG4_4, hG4_5, hG4_7,
          hG4_12, hG4_13, hG4_14, hG4_15, show 1 < 2 ^ w by omega, show 2 < 2 ^ w by omega,
          show work + L < 2 ^ w by omega, show w1 + L < 2 ^ w by omega,
          show w2 + L < 2 ^ w by omega, show w3 + L < 2 ^ w by omega,
          show 2 * i < 2 ^ w by omega, show pathsBase + 2 * i < 2 ^ w by omega,
          show pathsBase + 2 * i + 1 < 2 ^ w by omega,
          show 2 * j < 2 ^ w by omega, show pathsBase + 2 * j < 2 ^ w by omega,
          show pathsBase + 2 * j + 1 < 2 ^ w by omega, w4]
      · rfl
      · simp [argsSize, Expr.size]; omega
    have hrAdv : Runs w p ω (.assign 7 (.bin .add (.reg 7) (.bin .mul (.const 2) (.reg 1))))
        ⟨stCmp.mem, rgC, stCmp.pos⟩ .normal ⟨stCmp.mem, rgW, stCmp.pos⟩ 6 :=
      runs_assign_iff.mpr ⟨w5, by
        simp [Expr.eval, BinOp.eval, rgC, hG4_7, hG4_1, show 2 < 2 ^ w by omega,
          show 2 * L < 2 ^ w by omega,
          show max o4.value (w3 + 2 * L) + 2 * L < 2 ^ w by change w4 + 2 * L < 2 ^ w; omega, w5, w4],
        rfl, rfl, rfl⟩
    have hrgW_16 : rgW 16 = bit := by simp [rgW, rgC]
    have hrgW_6 : rgW 6 = flagPtr := by simp [rgW, rgC, hG4_6]
    have hrFlag : ∃ cFl, Runs w p ω (.cond (.reg 16) (.store (.reg 6) (.const 1)) .nop)
        ⟨stCmp.mem, rgW, stCmp.pos⟩ .normal ⟨memFinal, rgW, stCmp.pos⟩ cFl ∧ cFl ≤ 6 := by
      by_cases hb0 : bit = 0
      · refine ⟨3, runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, hrgW_16, hb0],
          by simp [runs_nop_iff, memFinal, hb0], by simp [Expr.size]⟩, by omega⟩
      · refine ⟨5, runs_cond_iff.mpr ⟨bit, 3, by simp [Expr.eval, hrgW_16], ?_, by simp [Expr.size]⟩, by omega⟩
        rw [ite_eq_right hb0]
        refine runs_store_iff.mpr ⟨flagPtr, 1, by simp [Expr.eval, hrgW_6],
          by simp [Expr.eval, show 1 < 2 ^ w by omega], rfl, ?_, rfl⟩
        simp [memFinal, hb0]
    obtain ⟨cFl, hrFl, hcFl⟩ := hrFlag
    have hTail1 : Runs w p ω
        (.call 16 cmpExch _ ;; .assign 7 _ ;; .cond (.reg 16) (.store (.reg 6) (.const 1)) .nop)
        ⟨st4.mem, rgG4, st4.pos⟩ .normal ⟨memFinal, rgW, stCmp.pos⟩ ((cCmp + 29) + (6 + cFl + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrCallCmp,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrAdv, hrFl, rfl⟩), rfl⟩)
    have hTail2 := runs_appendStmt hrG4 hTail1
    have hTail3 := runs_appendStmt hrG3 hTail2
    have hTail4 := runs_appendStmt hrG2 hTail3
    have hTail5 := runs_appendStmt hrG1 hTail4
    have hFull :=
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrL1,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrL2,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrL3,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrL4, hTail5, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    refine ⟨rgW, _, hFull, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [rgW, rgC, hG4_0]
    · simp [rgW, rgC, hG4_1]
    · simp [rgW, rgC, hG4_2]
    · simp [rgW, rgC, hG4_3]
    · simp [rgW, rgC, hG4_4]
    · simp [rgW, rgC, hG4_5]
    · exact hrgW_6
    · simp [rgW]
    · clear hrL1 hrL2 hrL3 hrL4 hrG1 hrG2 hrG3 hrG4 hrCallCmp hrAdv hrFl hTail1 hTail2 hTail3 hTail4 hTail5 hFull
      omega
  obtain ⟨regsF, cStep, hRunSt, hrF0, hrF1, hrF2, hrF3, hrF4, hrF5, hrF6, hrF7, hcStep⟩ := hRunBody
  -- 4. Transport `Rrep.rep`, `Rrep.phi`, `SelectHeapMatchesChain`, `OffTreeRecInv/Bound`, and `ZeroFrom`
  have hMemFinalEq : ∀ x < w4, x ≠ pathsBase + 2 * i + 1 → x ≠ pathsBase + 2 * j + 1 → x ≠ flagPtr →
      memFinal x = st4.mem x := by
    intro x hx hne1 hne2 hneF
    have h1 : memFinal x = stCmp.mem x := by
      dsimp only [memFinal]; split_ifs with h
      · exact Function.update_of_ne hneF ..
      · rfl
    exact h1.trans (hCmpFr x hx hne1 hne2)
  have hFoot4Eq : ∀ x, Rrep.foot root tok4 x → memFinal x = st4.mem x := by
    intro x hx
    have hx0 : Rrep.foot root tok x := hft04 x hx
    have hltW : x < work := hS.hbelow x hx0
    have hne1 : x ≠ pathsBase + 2 * i + 1 := fun heq =>
      hS.hnfPt (2 * i + 1) (by omega) (heq ▸ hx0)
    have hne2 : x ≠ pathsBase + 2 * j + 1 := fun heq =>
      hS.hnfPt (2 * j + 1) (by omega) (heq ▸ hx0)
    have hneF : x ≠ flagPtr := fun heq => hS.hFlagDisj (heq ▸ hx0)
    exact hMemFinalEq x (by omega) hne1 hne2 hneF
  have hlocR := solverStateRep_local cfg L P m V psi k epsExp drainUnit hlocalCore
  have hloc4 := hlocR root model tok4 st4.mem memFinal (fun x hx => (hFoot4Eq x hx).symm)
  have hrepF : Rrep.rep root model tok4 memFinal := hloc4.1 hrep4
  have hphiF : Rrep.phi root tok4 memFinal = Rrep.phi root tok4 st4.mem := hloc4.2.symm
  have hMatchF : SelectHeapMatchesChain memFinal loc 4 P model.chain.toTreeChain model.chain.g model.chain.ℓ size :=
    hMatch4.of_agree fun x hx1 hx2 =>
      hMemFinalEq x (by have := hS.hDescLtPt; have := hS.hPtLt; have := hS.hFlagLt; omega)
        (by have := hS.hDescLtPt; omega) (by have := hS.hDescLtPt; omega)
        (by have := hS.hDescLtPt; have := hS.hPtLt; omega)
  have hTagOwn4 : ∀ x, (tok4.tag x = 13 ∨ tok4.tag x = 18) → memFinal x = st4.mem x := by
    have hrep4_0 := hrep4
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, htags4⟩ := hrep4_0
    intro x hx
    exact hFoot4Eq x (Or.inl (htags4.1 x (by rcases hx with h | h <;> rw [h] <;> decide)))
  have hoffF : OffTreeRecInv model L memFinal tok4.edgeRecords B :=
    offTreeRecInv_of_agree hrep4 hoff4 hTagOwn4
  have hBdF : OffTreeRecBound model L memFinal tok4.edgeRecords B :=
    offTreeRecBound_of_agree hrep4 hBd4 hTagOwn4
  have hzF : ZeroFrom memFinal w5 := fun x hx => by
    have hneF : x ≠ flagPtr := by have := hS.hFlagLt; omega
    have h1 : memFinal x = stCmp.mem x := by
      dsimp only [memFinal]; split_ifs with h
      · exact Function.update_of_ne hneF ..
      · rfl
    exact h1.trans (hzCmp x hx)
  have hFrFinal : ∀ x < flagPtr, (x < pathsBase ∨ pathsBase + 2 * K ≤ x) →
      ¬ Rrep.foot root tok x → memFinal x = mem x := by
    intro x hx hOut hnf
    have hne1 : x ≠ pathsBase + 2 * i + 1 := by omega
    have hne2 : x ≠ pathsBase + 2 * j + 1 := by omega
    have hneF : x ≠ flagPtr := by omega
    exact (hMemFinalEq x (by have := hS.hFlagLt; omega) hne1 hne2 hneF).trans
      (hfr04 x (by have := hS.hFlagLt; omega) hnf)
  have hCostFinal : cStep + Rrep.phi root tok4 memFinal ≤
      4 * pathTreeBudget LinkCut.PathProg.pathC L model.extG.n + 117 * L + 370 +
        Rrep.phi root tok mem := by
    rw [hphiF]; dsimp only [Rrep] at hc1 hc2 hc3 hc4 ⊢; omega
  have hMetaFinal : PreservesLevelMeta tok tok4 mem memFinal :=
    (((hmeta1.trans hmeta2).trans hmeta3).trans hmeta4).congr_mem_right
      fun x hx => hFoot4Eq x (LevelMetaFoot.mem_foot hrep4 hx)
  -- 5. Case split on swap outcome (`ad + cb < ab + cd`)
  by_cases hSwap : ad + cb < ab + cd
  · have hBit1 : bit = 1 := by rw [hCmpRet, ite_eq_left hSwap]
    have hFlag1 : memFinal flagPtr = 1 := by
      dsimp only [memFinal]; rw [ite_eq_left (by omega), Function.update_self]
    set paths' := (paths.set i (a, d)).set j (c, b)
    set route' := Function.update route (steps + 1) paths'
    have hPtAtF : PathEndpointsAt memFinal pathsBase paths' := by
      have hPtAtCmp : PathEndpointsAt stCmp.mem pathsBase paths' := by
        simpa only [ite_eq_left hSwap, PathEndpointsAt, PathPairsAt] using hCmpPairs.2
      intro idx hidx
      have hidxK : idx < K := by
        simp only [paths', List.length_set] at hidx
        have := hS.hlen; omega
      have h0 := hPtAtCmp idx hidx
      have hneA : pathsBase + 2 * idx ≠ flagPtr := by have := hS.hPtLt; omega
      have hneB : pathsBase + 2 * idx + 1 ≠ flagPtr := by have := hS.hPtLt; omega
      dsimp only [memFinal]
      rw [ite_eq_left (by omega), Function.update_of_ne hneA, Function.update_of_ne hneB]
      exact h0
    have hExt := validSwapSeq_extend hS.hHist hS.hRt hij hj' hS.hPtOk hS.hSameComp (hLtIff.mp hSwap)
    refine ⟨w5, cStep, ⟨memFinal, regsF, stCmp.pos⟩, tok4, paths', route', steps + 1,
      hRunSt, hrF0, hrF1, hrF2, hrF3, hrF4, hrF5, hrF6, hrF7,
      by omega, by omega, ?_, hMetaFinal, hFrFinal, hft04, Or.inl ⟨hLtIff.mp hSwap, hFlag1, rfl⟩, hCostFinal⟩
    exact
      { hrep := hrepF
        hMatch := hMatchF
        hnum := hnum4
        hoff := hoffF
        hBd := hBdF
        hPtAt := hPtAtF
        hlen := hExt.2.2.2.1.trans hS.hlen
        hPtOk := hExt.2.2.2.2.1
        hSameComp := hExt.2.2.2.2.2
        hHist := hExt.1
        hR0 := hExt.2.1.trans hS.hR0
        hRt := hExt.2.2.1
        hlev := hlev4.trans (hlev3.trans (hlev2.trans (hlev1.trans hS.hlev)))
        hcap := hcap4.trans (hcap3.trans (hcap2.trans (hcap1.trans hS.hcap)))
        hhdl := hhdl4.trans (hhdl3.trans (hhdl2.trans (hhdl1.trans hS.hhdl)))
        htreeH := htH4
        hnfPt := fun x hx hf => hS.hnfPt x hx (hft04 _ hf)
        hlocDisj := fun x h1 h2 hf => hS.hlocDisj x h1 h2 (hft04 _ hf)
        htag18 := ht18_4
        hbelow := fun x hf => lt_of_lt_of_le (hS.hbelow x (hft04 x hf)) (by omega)
        hz := hzF
        hFlagDisj := fun hf => hS.hFlagDisj (hft04 _ hf)
        hFlagLt := by have := hS.hFlagLt; omega
        hPtLt := hS.hPtLt
        hDescLtPt := hS.hDescLtPt }
  · have hBit0 : bit = 0 := by rw [hCmpRet, ite_eq_right hSwap]
    have hMemEqCmp : memFinal = stCmp.mem := by
      dsimp only [memFinal]; rw [ite_eq_right (by omega)]
    have hFlagKeep : memFinal flagPtr = mem flagPtr := by
      rw [hMemEqCmp]
      exact (hCmpFr flagPtr (by have := hS.hFlagLt; omega) (by have := hS.hPtLt; omega)
        (by have := hS.hPtLt; omega)).trans (hfr04 flagPtr hS.hFlagLt hS.hFlagDisj)
    have hPtAtF : PathEndpointsAt memFinal pathsBase paths := by
      rw [hMemEqCmp]; simpa only [ite_eq_right hSwap, PathEndpointsAt, PathPairsAt] using hCmpPairs.2
    have hLeReal : walkLength ℓint (F.forestPath a b) + walkLength ℓint (F.forestPath c d) ≤
        walkLength ℓint (F.forestPath a d) + walkLength ℓint (F.forestPath c b) :=
      not_lt.mp fun h => hSwap (hLtIff.mpr h)
    refine ⟨w5, cStep, ⟨memFinal, regsF, stCmp.pos⟩, tok4, paths, route, steps,
      hRunSt, hrF0, hrF1, hrF2, hrF3, hrF4, hrF5, hrF6, hrF7,
      by omega, by omega, ?_, hMetaFinal, hFrFinal, hft04, Or.inr ⟨hLeReal, hFlagKeep, rfl, rfl, rfl⟩, hCostFinal⟩
    exact
      { hrep := hrepF
        hMatch := hMatchF
        hnum := hnum4
        hoff := hoffF
        hBd := hBdF
        hPtAt := hPtAtF
        hlen := hS.hlen
        hPtOk := hS.hPtOk
        hSameComp := hS.hSameComp
        hHist := hS.hHist
        hR0 := hS.hR0
        hRt := hS.hRt
        hlev := hlev4.trans (hlev3.trans (hlev2.trans (hlev1.trans hS.hlev)))
        hcap := hcap4.trans (hcap3.trans (hcap2.trans (hcap1.trans hS.hcap)))
        hhdl := hhdl4.trans (hhdl3.trans (hhdl2.trans (hhdl1.trans hS.hhdl)))
        htreeH := htH4
        hnfPt := fun x hx hf => hS.hnfPt x hx (hft04 _ hf)
        hlocDisj := fun x h1 h2 hf => hS.hlocDisj x h1 h2 (hft04 _ hf)
        htag18 := ht18_4
        hbelow := fun x hf => lt_of_lt_of_le (hS.hbelow x (hft04 x hf)) (by omega)
        hz := hzF
        hFlagDisj := fun hf => hS.hFlagDisj (hft04 _ hf)
        hFlagLt := by have := hS.hFlagLt; omega
        hPtLt := hS.hPtLt
        hDescLtPt := hS.hDescLtPt }

end MinCostFlow.MinRatio
