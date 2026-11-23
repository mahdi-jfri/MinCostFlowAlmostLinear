module

public import MinCostFlow.MinRatio.WireFindCycleSpec
public import MinCostFlow.MinRatio.OrdFindCycleWired
import WordRAM.Tactic

/-!
# The wired cycle finder meets the corrected spec

`findCycleStepSpecW_wired`: the entry `ordFindCycleWiredBody` (`OrdFindCycleWired.lean`) meets
`FindCycleStepSpecW` (`WireFindCycleSpec.lean`) when its selector meets
`OrdCycleRouteSelectSpecW` and its evaluator meets `OrdCycleRouteEvalSpecW`. The proof follows
`findCycleStepSpec_wired` step by step. The selector gives distinct edge names, the bound
`OffTreeRecBound` and the capacity of the name tables, and the evaluator needs them. The final
two stores write only the two pointer words of the descriptor, so the record bound moves to the
final memory by `offTreeRecBound_of_agree`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine SparseCore.Program

/-- **The wired cycle finder meets the corrected spec.** `ordFindCycleWiredBody` meets
`FindCycleStepSpecW` when its two parts meet `OrdCycleRouteSelectSpecW` and
`OrdCycleRouteEvalSpecW`. The proof is that of `findCycleStepSpec_wired`, with the new facts
passed from the selector to the evaluator. -/
theorem findCycleStepSpecW_wired
    {w L P m V psi k epsExp drainUnit findCycleProc selectRouteProc evalCycleProc
      selectSpace selectBudget evalSpace evalBudget maxEdges maxPaths capExp limbMul capLimit : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program}
    (hlocal : Rcore.Local)
    (hAt : p.procs[findCycleProc]? = some (ordFindCycleWiredBody selectRouteProc evalCycleProc))
    (hSel : OrdCycleRouteSelectSpecW w L P m V psi k epsExp drainUnit capExp limbMul capLimit cfg Rcore p
      selectRouteProc selectSpace selectBudget maxEdges maxPaths)
    (hEval : OrdCycleRouteEvalSpecW w L P m V psi k epsExp drainUnit cfg Rcore p
      evalCycleProc evalSpace evalBudget maxEdges maxPaths)
    (hw6 : 6 < 2 ^ w) :
    FindCycleStepSpecW w L P m V psi k epsExp drainUnit capExp limbMul capLimit cfg Rcore p findCycleProc
      (6 + selectSpace + evalSpace) (selectBudget + evalBudget + 90) maxEdges maxPaths := by
  refine ⟨ordFindCycleWiredBody selectRouteProc evalCycleProc, hAt, ?_⟩
  intro root heap pos ω mem model tok B R hrep hnum hoff hBd hCapF hLv hcapE hcapT hlogW hlenNN hbelow hz hroom
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  have hlocR := solverStateRep_local cfg L P m V psi k epsExp drainUnit hlocal
  obtain ⟨bSel, hbSel, hSelRun⟩ := hSel
  obtain ⟨bEval, hbEval, hEvalRun⟩ := hEval
  have hrep0 := hrep
  obtain ⟨hrootDir, _, hnumHdr, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, htags⟩ := hrep
  obtain ⟨hOwn, t1, t2, _⟩ := htags
  have hheapW : heap < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hw5 : 5 < 2 ^ w := by omega
  have hroot0 : mem root = tok.handle := by simpa using hrootDir 0 (by simp)
  have hL5 : mem (tok.handle + 5) = L := by simpa [Nat.add_assoc] using hnumHdr 0 (by simp)
  have hh5Lt : tok.handle + 5 < 2 ^ w :=
    lt_trans (hbelow _ (Or.inl (hOwn _ (by rw [t2 5 (by omega)]; decide)))) hheapW
  let work0 := heap + 6
  let s0 := startState [root, heap] mem pos
  let s1 : State := { s0 with regs := Function.update s0.regs 10 root }
  let s2 : State := { s1 with regs := Function.update s1.regs 11 heap }
  let s3 : State := { s2 with regs := Function.update s2.regs 12 tok.handle }
  let s4 : State := { s3 with regs := Function.update s3.regs 13 L }
  let s5 : State := { s4 with regs := Function.update s4.regs 14 work0 }
  have r1 : Runs w p ω (.assign 10 (.reg 0)) s0 .normal s1 2 :=
    runs_assign_iff.mpr ⟨root, by simp [Expr.eval, s0, startState], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 11 (.reg 1)) s1 .normal s2 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, s1, s0, startState], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 12 (.load (.reg 10))) s2 .normal s3 3 :=
    runs_assign_iff.mpr ⟨tok.handle, by simp [Expr.eval, s2, s1, s0, startState, hroot0], rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 13 (.load (.bin .add (.reg 12) (.const 5)))) s3 .normal s4 5 :=
    runs_assign_iff.mpr ⟨L, by simp [Expr.eval, BinOp.eval, s3, s2, s1, s0, startState, hw5, hh5Lt, hL5], rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 14 (.bin .add (.reg 11) (.const 6))) s4 .normal s5 4 :=
    runs_assign_iff.mpr ⟨work0, by simp [Expr.eval, BinOp.eval, s4, s3, s2, hw6, show work0 < 2 ^ w by omega, work0],
      rfl, rfl, rfl⟩
  -- Step 1: call `selectRouteProc`
  obtain ⟨work1, cSel, stSel, tok1, edges, paths, hrSel, hw1Lo, hw1Hi, hlev1, hcap1, hedMax, hptMax,
      hnodup, heLo, heHi, heLen, hpLo, hpHi, hpLen, hEdAt, hPtAt, hRoute, hnfEd1, hnfPt1, htag18_1,
      hrep1, hmeta1, hnum1, hoff1, hBd1, hz1, hfr1, hft1, hcSel⟩ :=
    hSelRun root heap work0 s5.pos ω mem model tok B R hrep0 hnum hoff hBd hCapF hLv hbelow rfl hz
      (by omega)
  let edgesBase := stSel.mem (heap + 2)
  let pathsBase := stSel.mem (heap + 4)
  let s6 : State := { regs := Function.update s5.regs 15 work1, mem := stSel.mem, pos := stSel.pos }
  let s7 : State := { s6 with regs := Function.update s6.regs 16 edgesBase }
  let s8 : State := { s7 with regs := Function.update s7.regs 17 edges.length }
  let s9 : State := { s8 with regs := Function.update s8.regs 18 pathsBase }
  let s10 : State := { s9 with regs := Function.update s9.regs 19 paths.length }
  have r6 : Runs w p ω (.call 15 selectRouteProc [.reg 10, .reg 11, .reg 14]) s5 .normal s6 (cSel + 4) :=
    runs_call_iff.mpr ⟨[root, heap, work0], bSel, .returned work1, stSel, cSel,
      by simp [evalArgs, Expr.eval, s5, s4, s3, s2, s1], hbSel, hrSel, rfl, rfl,
      by simp [argsSize, Expr.size]; omega⟩
  have r7 : Runs w p ω (.assign 16 (.load (.bin .add (.reg 11) (.const 2)))) s6 .normal s7 5 :=
    runs_assign_iff.mpr ⟨edgesBase, by
      simp [Expr.eval, BinOp.eval, s6, s5, s4, s3, s2, hw2, show heap + 2 < 2 ^ w by omega, edgesBase],
      rfl, rfl, rfl⟩
  have r8 : Runs w p ω (.assign 17 (.load (.bin .add (.reg 11) (.const 3)))) s7 .normal s8 5 :=
    runs_assign_iff.mpr ⟨edges.length, by
      simp [Expr.eval, BinOp.eval, s7, s6, s5, s4, s3, s2, hw3, show heap + 3 < 2 ^ w by omega, heLen],
      rfl, rfl, rfl⟩
  have r9 : Runs w p ω (.assign 18 (.load (.bin .add (.reg 11) (.const 4)))) s8 .normal s9 5 :=
    runs_assign_iff.mpr ⟨pathsBase, by
      simp [Expr.eval, BinOp.eval, s8, s7, s6, s5, s4, s3, s2, hw4, show heap + 4 < 2 ^ w by omega, pathsBase],
      rfl, rfl, rfl⟩
  have r10 : Runs w p ω (.assign 19 (.load (.bin .add (.reg 11) (.const 5)))) s9 .normal s10 5 :=
    runs_assign_iff.mpr ⟨paths.length, by
      simp [Expr.eval, BinOp.eval, s9, s8, s7, s6, s5, s4, s3, s2, hw5, show heap + 5 < 2 ^ w by omega, hpLen],
      rfl, rfl, rfl⟩
  -- Step 2: call `evalCycleProc`
  have hfoot1_lt (a : ℕ) (ha : Rrep.foot root tok1 a) : a < work1 := by
    rcases hft1 a ha with h0 | ⟨_, hhi⟩
    · have := hbelow a h0; omega
    · exact hhi
  obtain ⟨nextHeap, cEval, stEval, tok2, inner, norm, hrEval, hnhLo, hnhHi, hlev2, hcap2,
      hnormNN, hinnerAt, hnormAt, hinnerEq, hnormEq, htagEd2, htagPt2, htag18_2,
      hrep2, hmeta2, hnum2, hoff2, hBd2, hz2, hfr2, hft2, hcEval⟩ :=
    hEvalRun root edgesBase pathsBase work1 s10.pos ω stSel.mem model tok1 B R edges paths
      hrep1 hnum1 hoff1 hBd1 hcapE hcapT hlogW hlenNN hedMax hptMax hnodup hEdAt hPtAt hRoute heHi hpHi hnfEd1
      hnfPt1 hfoot1_lt hz1 (by omega)
  let s11 : State := { regs := Function.update s10.regs 20 nextHeap, mem := stEval.mem, pos := stEval.pos }
  have r11 : Runs w p ω (.call 20 evalCycleProc [.reg 10, .reg 16, .reg 17, .reg 18, .reg 19, .reg 15])
      s10 .normal s11 (cEval + 7) :=
    runs_call_iff.mpr ⟨[root, edgesBase, edges.length, pathsBase, paths.length, work1], bEval,
      .returned nextHeap, stEval, cEval,
      by simp [evalArgs, Expr.eval, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1], hbEval, hrEval,
      rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
  -- Step 3: write `innerPtr := work1` at `heap` and `normPtr := work1 + L` at `heap + 1`
  let m12 := Function.update stEval.mem heap work1
  let m13 := Function.update m12 (heap + 1) (work1 + L)
  let s12 : State := { s11 with mem := m12 }
  let s13 : State := { s12 with mem := m13 }
  have r12 : Runs w p ω (.store (.reg 11) (.reg 15)) s11 .normal s12 3 :=
    runs_store_iff.mpr ⟨heap, work1,
      by simp [Expr.eval, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2],
      by simp [Expr.eval, s11, s10, s9, s8, s7, s6], rfl, rfl, rfl⟩
  have r13 : Runs w p ω (.store (.bin .add (.reg 11) (.const 1)) (.bin .add (.reg 15) (.reg 13)))
      s12 .normal s13 7 :=
    runs_store_iff.mpr ⟨heap + 1, work1 + L,
      by simp [Expr.eval, BinOp.eval, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, hw1, show heap + 1 < 2 ^ w by omega],
      by simp [Expr.eval, BinOp.eval, s12, s11, s10, s9, s8, s7, s6, s5, s4, show work1 + L < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have r14 : Runs w p ω (.ret (.reg 20)) s13 (.returned nextHeap) s13 2 :=
    runs_ret_iff.mpr ⟨nextHeap, by simp [Expr.eval, s13, s12, s11], rfl, rfl, rfl⟩
  have rFull : Runs w p ω (ordFindCycleWiredBody selectRouteProc evalCycleProc)
      s0 (.returned nextHeap) s13 _ :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 2, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 2, _, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 3, _, r3,
    runs_seq_iff.mpr (Or.inr ⟨s4, 5, _, r4,
    runs_seq_iff.mpr (Or.inr ⟨s5, 4, _, r5,
    runs_seq_iff.mpr (Or.inr ⟨s6, cSel + 4, _, r6,
    runs_seq_iff.mpr (Or.inr ⟨s7, 5, _, r7,
    runs_seq_iff.mpr (Or.inr ⟨s8, 5, _, r8,
    runs_seq_iff.mpr (Or.inr ⟨s9, 5, _, r9,
    runs_seq_iff.mpr (Or.inr ⟨s10, 5, _, r10,
    runs_seq_iff.mpr (Or.inr ⟨s11, cEval + 7, _, r11,
    runs_seq_iff.mpr (Or.inr ⟨s12, 3, _, r12,
    runs_seq_iff.mpr (Or.inr ⟨s13, 7, 2, r13, r14, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  -- `heap` and `heap + 1` are strictly outside `Rrep.foot root tok2` and `[work0, nextHeap)`
  have hfoot2_neH (a : ℕ) (ha : Rrep.foot root tok2 a) : a ≠ heap ∧ a ≠ heap + 1 := by
    rcases hft2 a ha with h1 | ⟨hlo, _⟩
    · rcases hft1 a h1 with h0 | ⟨hlo1, _⟩
      · have := hbelow a h0; omega
      · omega
    · omega
  have hneH_m13 (a : ℕ) (h0 : a ≠ heap) (h1 : a ≠ heap + 1) : s13.mem a = stEval.mem a := by
    change Function.update (Function.update stEval.mem heap work1) (heap + 1) (work1 + L) a = _
    rw [Function.update_of_ne h1, Function.update_of_ne h0]
  have hfoot1_notDesc (j : ℕ) (hj : j < 6) : ¬ Rrep.foot root tok1 (heap + j) := fun hf => by
    rcases hft1 _ hf with h0 | ⟨hlo, _⟩
    · have := hbelow _ h0; omega
    · omega
  have hloc2 := hlocR root model tok2 stEval.mem s13.mem (fun a ha => (hneH_m13 a (hfoot2_neH a ha).1 (hfoot2_neH a ha).2).symm)
  have hrepFin : Rrep.rep root model tok2 s13.mem := hloc2.1 hrep2
  have hphiFin : Rrep.phi root tok2 s13.mem = Rrep.phi root tok2 stEval.mem := hloc2.2.symm
  have hag13 : ∀ a, (tok2.tag a = 13 ∨ tok2.tag a = 18) → s13.mem a = stEval.mem a := by
    have hrep2_0 := hrep2
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, htags2⟩ := hrep2_0
    intro a ha
    have hfootA : Rrep.foot root tok2 a :=
      Or.inl (htags2.1 a (by rcases ha with h | h <;> rw [h] <;> decide))
    exact hneH_m13 a (hfoot2_neH a hfootA).1 (hfoot2_neH a hfootA).2
  have hoffFin : OffTreeRecInv model L s13.mem tok2.edgeRecords B :=
    offTreeRecInv_of_agree hrep2 hoff2 hag13
  have hBdFin : OffTreeRecBound model L s13.mem tok2.edgeRecords B :=
    offTreeRecBound_of_agree hrep2 hBd2 hag13
  have hm13_0 : s13.mem heap = work1 := by
    change Function.update (Function.update stEval.mem heap work1) (heap + 1) (work1 + L) heap = work1
    rw [Function.update_of_ne (by omega), Function.update_self]
  have hm13_1 : s13.mem (heap + 1) = work1 + L := by
    change Function.update (Function.update stEval.mem heap work1) (heap + 1) (work1 + L) (heap + 1) = work1 + L
    rw [Function.update_self]
  have hm13_2 : s13.mem (heap + 2) = edgesBase :=
    (hneH_m13 _ (by omega) (by omega)).trans (hfr2 (heap + 2) (by omega) (hfoot1_notDesc 2 (by omega)))
  have hm13_3 : s13.mem (heap + 3) = edges.length :=
    (hneH_m13 _ (by omega) (by omega)).trans ((hfr2 (heap + 3) (by omega) (hfoot1_notDesc 3 (by omega))).trans heLen)
  have hm13_4 : s13.mem (heap + 4) = pathsBase :=
    (hneH_m13 _ (by omega) (by omega)).trans (hfr2 (heap + 4) (by omega) (hfoot1_notDesc 4 (by omega)))
  have hm13_5 : s13.mem (heap + 5) = paths.length :=
    (hneH_m13 _ (by omega) (by omega)).trans ((hfr2 (heap + 5) (by omega) (hfoot1_notDesc 5 (by omega))).trans hpLen)
  have hdescFin : CycleDescriptorAt model L P s13.mem heap nextHeap inner norm edges paths := by
    refine ⟨hm13_3, hm13_5, by omega, by rw [hm13_0]; omega, by rw [hm13_1]; omega,
      by rw [hm13_2]; omega, by rw [hm13_4]; omega,
      by rw [hm13_0]; omega, by rw [hm13_1]; omega,
      by rw [hm13_2]; omega, by rw [hm13_4]; omega, hnormNN, ?_, ?_, hinnerEq, hnormEq, ?_, ?_, hRoute⟩
    · rw [hm13_0]; exact hinnerAt.congr (fun j hj => hneH_m13 _ (by omega) (by omega))
    · rw [hm13_1]; exact hnormAt.congr (fun j hj => hneH_m13 _ (by omega) (by omega))
    · rw [hm13_2]
      exact hEdAt.congr (fun x hlo hhi =>
        (hneH_m13 x (by omega) (by omega)).trans
          (hfr2 x (by omega) (by
            have hx : edgesBase + (x - edgesBase) = x := by omega
            rw [← hx]; exact hnfEd1 (x - edgesBase) (by omega))))
    · rw [hm13_4]
      intro i hi
      have h1 : s13.mem (pathsBase + 2 * i) = stSel.mem (pathsBase + 2 * i) :=
        (hneH_m13 _ (by omega) (by omega)).trans (hfr2 _ (by omega) (hnfPt1 (2 * i) (by omega)))
      have h2 : s13.mem (pathsBase + 2 * i + 1) = stSel.mem (pathsBase + 2 * i + 1) :=
        (hneH_m13 _ (by omega) (by omega)).trans
          (hfr2 _ (by omega) (by
            rw [Nat.add_assoc]; exact hnfPt1 (2 * i + 1) (by omega)))
      exact ⟨h1.trans (hPtAt i hi).1, h2.trans (hPtAt i hi).2⟩
  have hmetaFin : PreservesLevelMeta tok tok2 mem s13.mem :=
    (hmeta1.trans hmeta2).congr_mem_right fun a ha => by
      have hfootA : Rrep.foot root tok2 a := LevelMetaFoot.mem_foot hrep2 ha
      exact hneH_m13 a (hfoot2_neH a hfootA).1 (hfoot2_neH a hfootA).2
  refine ⟨nextHeap, _, s13, tok2, inner, norm, edges, paths, rFull,
    by omega, by omega, hlev2.trans hlev1, hcap2.trans hcap1, hedMax, hptMax,
    by rw [hm13_2]; exact htagEd2, by rw [hm13_4]; exact htagPt2,
    fun a ha => htag18_1 a (htag18_2 a ha),
    hdescFin, hrepFin, hmetaFin, hnum2, hoffFin, hBdFin, ?_, ?_, ?_, ?_⟩
  · intro a ha; exact (hneH_m13 a (by omega) (by omega)).trans (hz2 a ha)
  · intro a ha hnf
    have hnf1 : ¬ Rrep.foot root tok1 a := fun hf => by
      rcases hft1 a hf with h0 | ⟨hlo, _⟩
      · exact hnf h0
      · omega
    exact (hneH_m13 a (by omega) (by omega)).trans ((hfr2 a (by omega) hnf1).trans (hfr1 a ha hnf))
  · intro a ha
    rcases hft2 a ha with h1 | ⟨hlo, hhi⟩
    · rcases hft1 a h1 with h0 | ⟨hlo1, hhi1⟩
      · exact Or.inl h0
      · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, hhi⟩
  · dsimp only [Rrep] at hcSel hcEval hphiFin ⊢
    rw [hphiFin]; omega

end MinCostFlow.MinRatio
