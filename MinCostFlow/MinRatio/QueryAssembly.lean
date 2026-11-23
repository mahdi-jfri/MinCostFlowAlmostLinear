module

public import MinCostFlow.MinRatio.SolverRep
public import MinCostFlow.MinRatio.SolverLevelMetaPreserve
public import MinCostFlow.MinRatio.QueryReserved
import WordRAM.Tactic

/-!
# End-to-end Word-RAM Query assembly (`minRatioMachineContractWithV` op 1)

Implements Definition 4.5 `Query(e)` (`[root, e, heap]`) against `solverStateRep`
and `minRatioMachineContractWithV` operation 1. Translates external edge `e` via
`forward`, branches on `slots[e_int]`:
- If `slot ≠ 0` (tree edge): calls `pathTreeMachineContract` op 4 (`PointRead`) at
  `heap + L` and writes the original-direction scalar at `heap` via `queryReserved`.
- If `slot = 0` (off-tree edge): reads `edgeRecords[e_int]` and writes the
  original-direction scalar directly at `heap` via `queryResolved`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine

/-- Six-instruction Query prefix loading `handle`, `L`, `forward`, `e_int`, `slots`, `slot`. -/
@[expose] def queryPrefixBody : Stmt :=
  .assign 3 (.load (.reg 0)) ;;
  .assign 4 (.load (.bin .add (.reg 3) (.const 5))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const 3))) ;;
  .assign 6 (.load (.bin .add (.reg 5) (.reg 1))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const 6))) ;;
  .assign 8 (.load (.bin .add (.reg 7) (.reg 6)))

/-- Fixed deterministic Query entry procedure taking `[root, e, heap]` and returning the
new free heap pointer after writing the `L`-limb `ScalarAt` output at `heap`. -/
@[expose] def solverQueryBody (opPointRead queryResolved queryReserved : ℕ) : Stmt :=
  queryPrefixBody ;;
  .cond (.reg 8)
    (.assign 9 (.load (.reg 3)) ;;
     .assign 10 (.bin .add (.reg 2) (.reg 4)) ;;
     .call 11 opPointRead [.reg 9, .reg 8, .reg 10] ;;
     .assign 13 (.bin .add (.bin .add (.reg 10) (.const 2)) (.bin .mul (.const 4) (.reg 4))) ;;
     .cond (.bin .lt (.reg 11) (.reg 13))
       (.assign 11 (.reg 13))
       .nop ;;
     .call 12 queryReserved [.reg 10, .reg 4, .reg 2, .reg 11] ;;
     .ret (.reg 12))
    (.assign 9 (.load (.bin .add (.reg 0) (.const 10))) ;;
     .assign 10 (.load (.bin .add (.reg 9) (.reg 6))) ;;
     .call 11 queryResolved [.reg 10, .reg 4, .reg 2] ;;
     .ret (.reg 11))

theorem solverQueryBody_noRand (opPointRead queryResolved queryReserved : ℕ) :
    (solverQueryBody opPointRead queryResolved queryReserved).NoRand := by
  simp [solverQueryBody, queryPrefixBody, Stmt.NoRand]

private theorem listAt_congr' {mem mem' : ℕ → ℕ} {base : ℕ} {xs : List ℕ}
    (h : ListAt mem base xs) (hag : ∀ j < xs.length, mem' (base + j) = mem (base + j)) :
    ListAt mem' base xs := fun j hj => (hag j hj).trans (h j hj)

/-- Helper: running the 6-instruction Query prefix loads `handle, L, forward, ei, slots, slot`. -/
private theorem queryPrefix_runs {w root e heap pos handle L forward ei slots slot : ℕ}
    {p : Program} {mem : ℕ → ℕ} {ω : ℕ → Bool}
    (h3 : root + 3 < 2 ^ w) (h6 : root + 6 < 2 ^ w) (hh5 : handle + 5 < 2 ^ w)
    (hfwd : forward + e < 2 ^ w) (hsl : slots + ei < 2 ^ w)
    (hm0 : mem root = handle) (hm5 : mem (handle + 5) = L)
    (hm3 : mem (root + 3) = forward) (hmei : mem (forward + e) = ei)
    (hm6 : mem (root + 6) = slots) (hmsl : mem (slots + ei) = slot) :
    ∃ mid,
      Runs w p ω queryPrefixBody
        (startState [root, e, heap] mem pos) .normal mid 33 ∧
      mid.mem = mem ∧ mid.pos = pos ∧
      mid.regs 0 = root ∧ mid.regs 1 = e ∧ mid.regs 2 = heap ∧
      mid.regs 3 = handle ∧ mid.regs 4 = L ∧ mid.regs 5 = forward ∧
      mid.regs 6 = ei ∧ mid.regs 7 = slots ∧ mid.regs 8 = slot := by
  have hw3 : 3 < 2 ^ w := by omega
  have hw5 : 5 < 2 ^ w := by omega
  have hw6 : 6 < 2 ^ w := by omega
  let s0 := startState [root, e, heap] mem pos
  let s1 := { s0 with regs := Function.update s0.regs 3 handle }
  let s2 := { s1 with regs := Function.update s1.regs 4 L }
  let s3 := { s2 with regs := Function.update s2.regs 5 forward }
  let s4 := { s3 with regs := Function.update s3.regs 6 ei }
  let s5 := { s4 with regs := Function.update s4.regs 7 slots }
  let s6 := { s5 with regs := Function.update s5.regs 8 slot }
  have r1 : Runs w p ω (.assign 3 (.load (.reg 0))) s0 .normal s1 3 :=
    runs_assign_iff.mpr ⟨handle, by simp [Expr.eval, s0, startState, hm0], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 4 (.load (.bin .add (.reg 3) (.const 5)))) s1 .normal s2 5 :=
    runs_assign_iff.mpr ⟨L, by simp [Expr.eval, BinOp.eval, s1, s0, startState, hw5, hh5, hm5], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 0) (.const 3)))) s2 .normal s3 5 :=
    runs_assign_iff.mpr ⟨forward, by simp [Expr.eval, BinOp.eval, s2, s1, s0, startState, hw3, h3, hm3], rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 5) (.reg 1)))) s3 .normal s4 5 :=
    runs_assign_iff.mpr ⟨ei, by simp [Expr.eval, BinOp.eval, s3, s2, s1, s0, startState, hfwd, hmei], rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 0) (.const 6)))) s4 .normal s5 5 :=
    runs_assign_iff.mpr ⟨slots, by simp [Expr.eval, BinOp.eval, s4, s3, s2, s1, s0, startState, hw6, h6, hm6], rfl, rfl, rfl⟩
  have r6 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 7) (.reg 6)))) s5 .normal s6 5 :=
    runs_assign_iff.mpr ⟨slot, by simp [Expr.eval, BinOp.eval, s5, s4, s3, s2, s1, s0, startState, hsl, hmsl], rfl, rfl, rfl⟩
  refine ⟨s6, ?_, rfl, rfl,
    by simp [s6, s5, s4, s3, s2, s1, s0, startState],
    by simp [s6, s5, s4, s3, s2, s1, s0, startState],
    by simp [s6, s5, s4, s3, s2, s1, s0, startState],
    by simp [s6, s5, s4, s3, s2, s1], by simp [s6, s5, s4, s3, s2],
    by simp [s6, s5, s4, s3], by simp [s6, s5, s4], by simp [s6, s5], by simp [s6]⟩
  exact runs_seq_iff.mpr (Or.inr ⟨s1, 3, 29, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 5, 23, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 5, 17, r3,
    runs_seq_iff.mpr (Or.inr ⟨s4, 5, 11, r4,
    runs_seq_iff.mpr (Or.inr ⟨s5, 5, 5, r5, r6, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)

/-- Helper: updating `tree`, `trees`, `treeTok`, `owned`, and `tag` after `opTree 4` (`lctExpose`)
plus `queryReserved` preserves `solverStateRep` and every core's potential cleanly. -/
private theorem solverStateRep_after_queryExpose {cfg : Alg2Config}
    {L P m V psi k epsExp drainUnit : ℕ} {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)}
    (hlocalCore : Rcore.Local)
    {root heap ret slot : ℕ} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {mem mem' : ℕ → ℕ}
    {trees' : List AuxTree} {treeTok' : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ}
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hbelow : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a → a < heap)
    (hframe : ∀ a < heap, ¬ (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap tok.treeTok a →
      mem' a = mem a)
    (hfoot : ∀ a, (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap treeTok' a →
      (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap tok.treeTok a ∨
      (heap ≤ a ∧ a < ret))
    (hlct' : LctInvWith pathPayload (lctExpose pathPayload tok.tree slot) trees' tok.free tok.depth)
    (hslotMem : slot ∈ tok.trees.flatMap AuxTree.toList)
    (hperm : (forestPairs pathPayload (lctExpose pathPayload tok.tree slot).splay trees').Perm
      (forestPairs pathPayload tok.tree.splay tok.trees))
    (htreeRep' : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).rep
      tok.treeHeap (lctExpose pathPayload tok.tree slot) treeTok' mem') :
    let tok' : SolverToken cfg L Rcore :=
      { tok with
        tree := lctExpose pathPayload tok.tree slot
        trees := trees'
        treeTok := treeTok'
        owned := fun a => tok.owned a ∨ (heap ≤ a ∧ a < ret)
        tag := fun a => if heap ≤ a ∧ a < ret then 16 else tok.tag a }
    (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok' mem' ∧
    (∀ i < cfg.P.d, Rcore.phi (tok'.coreHandle i) (tok'.coreTok i) mem' =
      Rcore.phi (tok.coreHandle i) (tok.coreTok i) mem) := by
  dsimp only
  obtain ⟨hrootDir, hdetect, hnum, hchainP, hfreshInv, hfreshTab, hextM, hintCapE,
    hsched, hoffReady, htn, hlct0, _, hedgeAcc, hcores, htermH, htermBr, htermRep, hwire, htags⟩ := hrep
  obtain ⟨hOwn, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15,
    t16, t1718, t19, t20, t21⟩ := htags
  let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
  have hagT {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) (hv16 : v ≠ 16) : mem' a = mem a :=
    hframe a (hbelow a (Or.inl (hOwn a (ht ▸ hv)))) (fun hf => hv16 (ht.symm.trans (t16 a hf)))
  have htagKeep {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) :
      (if heap ≤ a ∧ a < ret then 16 else tok.tag a) = v := by
    have hlt : a < heap := hbelow a (Or.inl (hOwn a (ht ▸ hv)))
    rw [ite_eq_right (by omega)]; exact ht
  have hmem_et (j : ℕ) (hj : j < tok.intCap) : mem' (tok.edgeThresholds + j) = mem (tok.edgeThresholds + j) :=
    hagT (t12 j hj) (by decide) (by decide)
  have hmem_er (j : ℕ) (hj : j < tok.intCap) : mem' (tok.edgeRecords + j) = mem (tok.edgeRecords + j) :=
    hagT (t13 j hj) (by decide) (by decide)
  have htermLocal := LastLevelProgram.lastLevelRepresentation_local tok.vcLast tok.ecLast
    4 L P (model.chain.G cfg.P.d).E
  have hcore_ag (i : ℕ) (hi : i < cfg.P.d) (a : ℕ) (ha : Rcore.foot (tok.coreHandle i) (tok.coreTok i) a) :
      mem a = mem' a :=
    (hagT (t21 i hi a ha) (by omega) (by omega)).symm
  have hterm_ag (a : ℕ)
      (ha : (LastLevelProgram.lastLevelRepresentation tok.vcLast tok.ecLast 4 L P
        (model.chain.G cfg.P.d).E).foot tok.termHandle tok.termTok a) : mem a = mem' a :=
    (hagT (t19 a ((lastLevelRepresentation_foot_indep_P _ _ _ _ P 0 _ _ _ _).mp ha))
      (by decide) (by decide)).symm
  have htn' : (lctExpose pathPayload tok.tree slot).n = tok.tree.n := rfl
  refine ⟨⟨listAt_congr' hrootDir (fun j hj => hagT (t1 j (by simpa [List.length] using hj)) (by decide) (by decide)),
    listAt_congr' hdetect (fun j hj => hagT (t2 j (by simp [List.length] at hj; omega)) (by decide) (by decide)),
    listAt_congr' hnum (fun j hj => by
      have h1 : tok.handle + 5 + j = tok.handle + (5 + j) := by omega
      rw [h1]; exact hagT (t2 (5 + j) (by simp [List.length] at hj; omega)) (by decide) (by decide)),
    listAt_congr' hchainP (fun j hj => by
      have h1 : tok.handle + 9 + j = tok.handle + (9 + j) := by omega
      rw [h1]; exact hagT (t2 (9 + j) (by simp [List.length] at hj; omega)) (by decide) (by decide)),
    hfreshInv, ⟨(hagT t6 (by decide) (by decide)).trans hfreshTab.1,
      fun e he => (hagT (t7 e he) (by decide) (by decide)).trans (hfreshTab.2.1 e he),
      fun e he => (hagT (t8 e he) (by decide) (by decide)).trans (hfreshTab.2.2 e he)⟩,
    hextM, hintCapE,
    ⟨fun i => (hagT (t5 i.val (by omega)) (by decide) (by decide)).trans (hsched.1 i),
      fun i hi => by
        have h1 : tok.levelsEnd + (cfg.P.d + 1) + i = tok.levelsEnd + (cfg.P.d + 1 + i) := by omega
        rw [h1]; exact (hagT (t5 _ (by omega)) (by decide) (by decide)).trans (by rw [← h1]; exact hsched.2.1 i hi),
      fun i hi => by
        have h1 : tok.levelsEnd + 2 * (cfg.P.d + 1) + i = tok.levelsEnd + (2 * (cfg.P.d + 1) + i) := by omega
        rw [h1]; exact (hagT (t5 _ (by omega)) (by decide) (by decide)).trans (by rw [← h1]; exact hsched.2.2.1 i hi),
      fun i hi => by
        have h1 : tok.levelsEnd + 3 * (cfg.P.d + 1) + i = tok.levelsEnd + (3 * (cfg.P.d + 1) + i) := by omega
        rw [h1]; exact (hagT (t5 _ (by omega)) (by decide) (by decide)).trans (by rw [← h1]; exact hsched.2.2.2.1 i hi),
      (hagT (t5 (4 * (cfg.P.d + 1)) (by omega)) (by decide) (by decide)).trans hsched.2.2.2.2⟩,
    ?_, htn'.trans htn, hlct', htreeRep', ?_, ?_,
    (hagT (t4 cfg.P.d (by omega)) (by decide) (by decide)).trans htermH,
    by
      have h1 : tok.handle + 18 + (cfg.P.d + 1) + cfg.P.d = tok.handle + 18 + (2 * cfg.P.d + 1) := by omega
      rw [h1] at htermBr ⊢; exact (hagT (t4 _ (by omega)) (by decide) (by decide)).trans htermBr,
    (htermLocal tok.termHandle _ tok.termTok mem mem' hterm_ag).1 htermRep, ?_, ?_⟩,
    fun i hi => (hlocalCore (tok.coreHandle i) (chainLevelOrdAbs model.chain i) (tok.coreTok i)
      mem mem' (hcore_ag i hi)).2.symm⟩
  · obtain ⟨hcnt, hmemL, hdist, hbits, hrev⟩ := hoffReady
    refine ⟨hcnt, fun j hj => ?_, fun j₁ hj₁ j₂ hj₂ hne => ?_, fun e he => ?_, fun e he h1 => ?_⟩
    · rw [hagT (t14 j (lt_of_lt_of_le hj hcnt)) (by decide) (by decide)]
      exact ⟨(hmemL j hj).1, (hagT (t15 _ (hmemL j hj).1) (by decide) (by decide)).trans (hmemL j hj).2⟩
    · rw [hagT (t14 j₁ (lt_of_lt_of_le hj₁ hcnt)) (by decide) (by decide),
          hagT (t14 j₂ (lt_of_lt_of_le hj₂ hcnt)) (by decide) (by decide)]
      exact hdist j₁ hj₁ j₂ hj₂ hne
    · rw [hagT (t15 e he) (by decide) (by decide)]; exact hbits e he
    · rw [hagT (t15 e he) (by decide) (by decide)] at h1
      obtain ⟨j, hj, hje⟩ := hrev e he h1
      exact ⟨j, hj, (hagT (t14 j (lt_of_lt_of_le hj hcnt)) (by decide) (by decide)).trans hje⟩
  · refine ⟨fun e he => ?_, fun sl val hsl hp => ?_⟩
    · obtain ⟨heiCap, hthr, hbr⟩ := hedgeAcc.1 e he
      refine ⟨heiCap, ?_, ?_⟩
      · rw [hmem_et _ heiCap]
        exact hthr.congr (fun j hj => hagT ((t1718 e he).1 j hj) (by decide) (by decide))
      · split_ifs at hbr ⊢ with hin
        · obtain ⟨hsnz, his, hnm, hst, val, acc, hp, hfl, hac, hdet⟩ := hbr
          have hslLt : mem (tok.slots + model.extToInt e) < 2 * tok.tree.n := by
            unfold isEdgeSlot at his; omega
          rw [hagT (t9 _ heiCap) (by decide) (by decide), hmem_et _ heiCap]
          exact ⟨hsnz, by simpa [htn'] using his,
            (hagT (t10 _ hslLt) (by decide) (by decide)).trans hnm,
            (hagT (t11 _ hslLt) (by decide) (by decide)).trans hst,
            val, acc, hperm.mem_iff.mpr hp, hfl, hac, hdet⟩
        · obtain ⟨hs0, val, acc, hrec, hfl, hac, hdet, hpush⟩ := hbr
          rw [hmem_er _ heiCap]
          refine ⟨(hagT (t9 _ heiCap) (by decide) (by decide)).trans hs0, val, acc,
            hrec.congr (fun x hxlo hxhi => by
              have hx : x = mem (tok.edgeRecords + model.extToInt e) +
                  (x - mem (tok.edgeRecords + model.extToInt e)) := by omega
              rw [hx]
              exact hagT ((t1718 e he).2 hin _ (by omega)) (by decide) (by decide)),
            hfl, hac, hdet, fun hnn => (hagT (t15 _ heiCap) (by decide) (by decide)).trans (hpush hnn)⟩
    · have hsl' : isEdgeSlot tok.tree.n sl := by simpa [htn'] using hsl
      have hslLt : sl < 2 * tok.tree.n := by unfold isEdgeSlot at hsl'; omega
      obtain ⟨heiCap, hin, hse, heE, he2i⟩ := hedgeAcc.2 sl val hsl' (hperm.mem_iff.mp hp)
      rw [hagT (t10 sl hslLt) (by decide) (by decide)]
      exact ⟨heiCap, hin, (hagT (t9 _ heiCap) (by decide) (by decide)).trans hse, heE, he2i⟩
  · intro i hi
    obtain ⟨hh, hbr, hcr⟩ := hcores i hi
    refine ⟨(hagT (t4 i (by omega)) (by decide) (by decide)).trans hh,
      by
        have h1 : tok.handle + 18 + (cfg.P.d + 1) + i = tok.handle + 18 + (cfg.P.d + 1 + i) := by omega
        rw [h1] at hbr ⊢; exact (hagT (t4 _ (by omega)) (by decide) (by decide)).trans hbr,
      (hlocalCore (tok.coreHandle i) _ (tok.coreTok i) mem mem' (hcore_ag i hi)).1 hcr⟩
  · obtain ⟨htabW, hrgW, hsubCap, hnsW, hglW⟩ := hwire
    have hnsExp := treeEditNamedSlots_expose_witness hnsW hlct0 hslotMem hlct'
    have hparExp := inducedSubPar_expose_witness hlct0 hslotMem hlct'
    refine ⟨fun j hj => (hagT (t3 j hj) (by decide) (by decide)).trans (htabW j hj),
      hrgW.of_agree (fun a h1 h2 => hagT (t20 a h1 h2) (by decide) (by decide)), hsubCap,
      ⟨fun ei hei => by
          rw [hagT (t9 ei (hsubCap.2 ei hei).1) (by decide) (by decide)]
          have hfwd := hnsExp.forward ei hei
          have hslotLt : mem (tok.slots + ei) < 2 * tok.tree.n := by unfold isEdgeSlot at hfwd; omega
          exact ⟨hfwd.1, hfwd.2.1, (hagT (t10 _ hslotLt) (by decide) (by decide)).trans hfwd.2.2⟩,
        fun k hk hks => by
          have hkLt : k < 2 * tok.tree.n := by simpa [htn'] using hks.2
          rw [hagT (t10 k hkLt) (by decide) (by decide)]
          obtain ⟨hmem, hslot⟩ := hnsExp.inverse k hk hks
          exact ⟨hmem, (hagT (t9 _ (hsubCap.2 _ hmem).1) (by decide) (by decide)).trans hslot⟩,
        fun ei hei => by
          rw [hagT (t9 ei (hsubCap.2 ei hei).1) (by decide) (by decide)]; exact hnsExp.endpoints ei hei⟩,
      fun e he => by
        dsimp only
        have hgl := hglW e he; dsimp only at hgl
        have heiCap := (hedgeAcc.1 e he).1
        split_ifs at hgl ⊢ with hin
        · intro val hp
          rw [hagT (t9 _ heiCap) (by decide) (by decide)] at hp ⊢
          rw [hparExp]
          exact hgl val (hperm.mem_iff.mp hp)
        · intro val hpa
          rw [hmem_er _ heiCap] at hpa
          exact hgl val (hpa.congr fun x hlo hhi => by
            have hx : x = mem (tok.edgeRecords + model.extToInt e) +
                (x - mem (tok.edgeRecords + model.extToInt e)) := by omega
            rw [hx]; exact (hagT ((t1718 e he).2 hin _ (by omega)) (by decide) (by decide)).symm)⟩
  · refine ⟨fun a ha => by
      dsimp only at ha ⊢
      by_cases hnew : heap ≤ a ∧ a < ret
      · exact Or.inr hnew
      · rw [ite_eq_right hnew] at ha; exact Or.inl (hOwn a ha),
      fun j hj => htagKeep (t1 j hj) (by decide),
      fun j hj => htagKeep (t2 j hj) (by decide),
      fun j hj => htagKeep (t3 j hj) (by decide),
      fun j hj => htagKeep (t4 j hj) (by decide),
      fun j hj => htagKeep (t5 j hj) (by decide),
      htagKeep t6 (by decide),
      fun j hj => htagKeep (t7 j hj) (by decide),
      fun j hj => htagKeep (t8 j hj) (by decide),
      fun j hj => htagKeep (t9 j hj) (by decide),
      fun j hj => htagKeep (t10 j (by simpa [htn'] using hj)) (by decide),
      fun j hj => htagKeep (t11 j (by simpa [htn'] using hj)) (by decide),
      fun j hj => htagKeep (t12 j hj) (by decide),
      fun j hj => htagKeep (t13 j hj) (by decide),
      fun j hj => htagKeep (t14 j hj) (by decide),
      fun j hj => htagKeep (t15 j hj) (by decide),
      fun a ha => by
        dsimp only at ha ⊢
        rcases hfoot a ha with hold | hnew
        · exact htagKeep (t16 a hold) (by decide)
        · rw [ite_eq_left hnew],
      fun e he => by
        dsimp only
        have heiCap := (hedgeAcc.1 e he).1
        rw [hmem_et _ heiCap, hmem_er _ heiCap]
        exact ⟨fun j hj => htagKeep ((t1718 e he).1 j hj) (by decide),
          fun hnot j hj => htagKeep ((t1718 e he).2 hnot j hj) (by decide)⟩,
      fun a ha => htagKeep (t19 a ha) (by decide),
      fun a h1 h2 => htagKeep (t20 a h1 h2) (by decide),
      fun i hi a ha => htagKeep (t21 i hi a ha) (by omega)⟩

/-- End-to-end execution of `solverQueryBody` against `minRatioMachineContractWithV`
operation 1 (`Query`), preserving `solverStateRep` and bounding amortized cost by
`pathTreeBudget constant L model.extG.n + 53 * L + 160`. -/
theorem solverQueryBody_runs {w m V psi k epsExp drainUnit : ℕ}
    {F : MinRatioFormat w} {cfg : Alg2Config} {G : MGraph} {κ α : ℝ}
    {rate : ℕ → ℕ} {outerSpace : ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} (hlocalCore : Rcore.Local)
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    {treeInit queryResolved queryReserved root e heap pos : ℕ}
    {opTree : ℕ → ℕ} {model : Alg2State cfg}
    {tok : SolverToken cfg F.limbs Rcore}
    (hfmt4 : F.fmt.limbBits = 4)
    (hExtG : model.extG = G)
    (hTreeImpl : (LinkCut.PathProg.pathRep 4 F.limbs LinkCut.PathProg.pathC).Implements w p
      treeInit opTree
      (pathTreeMachineContract F.fmt F.limbs LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc F.limbs)))
    (hQRes : ∀ v, MeetsContract w p queryResolved
      (queryResolvedContract w 4 F.fmt.precision v))
    (hQResv : ∀ v, MeetsContract w p queryReserved
      (queryReservedContract w 4 F.fmt.precision v))
    (hrep : (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp drainUnit Rcore).rep
      root model tok mem)
    (hpre : (minRatioMachineContractWithV F (Chain.Ordered.algorithm2_dsWithFailureWith cfg κ) G m V κ α
      rate outerSpace).pre 1 model [root, e, heap] mem)
    (hbelow : ∀ a, (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp drainUnit Rcore).foot
      root tok a → a < heap)
    (hz : ZeroFrom mem heap)
    (hw10 : 10 < 2 ^ w)
    (htreeWord : 2 * tok.tree.n + 1 < 2 ^ w)
    (htreeWidth : Nat.log 2 (2 * tok.tree.n + 1) ≤ 4 * F.limbs)
    (hfits : pathTreeFits 4 F.limbs tok.tree)
    (hfitsExp : ∀ slot, pathTreeActive tok.tree slot →
      pathTreeFits 4 F.limbs (lctExpose pathPayload tok.tree slot))
    (hroom : heap + max (F.limbs + LinkCut.PathProg.pathAlloc F.limbs 4 tok.tree.n
        [tok.treeHeap, mem (tok.slots + model.extToInt e), heap + F.limbs])
        (2 + 5 * F.limbs) + F.limbs < 2 ^ w) :
    let R := solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp drainUnit Rcore
    ∃ ret cost out tok',
      Runs w p ω (solverQueryBody (opTree 4) queryResolved queryReserved)
        (startState [root, e, heap] mem pos) (.returned ret) out cost ∧
      (minRatioMachineContractWithV F (Chain.Ordered.algorithm2_dsWithFailureWith cfg κ) G m V κ α
        rate outerSpace).post 1 model [root, e, heap] mem model out.mem ∧
      R.rep root model tok' out.mem ∧
      PreservesLevelMeta tok tok' mem out.mem ∧
      tok'.intCap = tok.intCap ∧
      ZeroFrom out.mem ret ∧ heap ≤ ret ∧
      ret ≤ heap + max (F.limbs + LinkCut.PathProg.pathAlloc F.limbs 4 tok.tree.n
        [tok.treeHeap, mem (tok.slots + model.extToInt e), heap + F.limbs])
        (2 + 5 * F.limbs) + F.limbs ∧
      (∀ a < heap, ¬ R.foot root tok a → out.mem a = mem a) ∧
      (∀ a, R.foot root tok' a → R.foot root tok a ∨ (heap ≤ a ∧ a < ret)) ∧
      cost + R.phi root tok' out.mem ≤
        pathTreeBudget LinkCut.PathProg.pathC F.limbs model.extG.n +
          53 * F.limbs + 160 + R.phi root tok mem ∧
      (∀ B R : ℤ, PathTreeNumericInv tok.tree tok.trees B R →
        PathTreeNumericInv tok'.tree tok'.trees B R) ∧
      tok'.edgeRecords = tok.edgeRecords ∧
      (∀ j < tok.intCap, out.mem (tok.edgeRecords + j) = mem (tok.edgeRecords + j)) := by
  dsimp only
  let L := F.limbs
  let P := F.fmt.precision
  let R := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
  obtain ⟨hstateFits, hH, e', hpH, hargs, heG, hem⟩ := hpre
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl⟩ := hargs
  have heM : e ∈ model.extG.E := hExtG.symm ▸ heG
  obtain ⟨hmei, heiCap, hqEdge⟩ := solverStateRep_query_edge hrep heM
  have hrep0 := hrep
  obtain ⟨hrootDir, hdetect, _, _, _, _, _, _, _, _, htn, hlctInv, htreeRep, hedgeAcc, _, _, _, _,
    _, htags⟩ := hrep
  obtain ⟨hOwn, t1, t2, _, _, _, _, t7, _, t9, _, _, _, t13, _, _, t16, t1718, _, _, _⟩ := htags
  have hltT {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) : a < heap :=
    hbelow a (Or.inl (hOwn a (ht ▸ hv)))
  have hheapW : heap < 2 ^ w := by omega
  have hroot3W : root + 3 < 2 ^ w := lt_trans (hltT (t1 3 (by omega)) (by decide)) hheapW
  have hroot6W : root + 6 < 2 ^ w := lt_trans (hltT (t1 6 (by omega)) (by decide)) hheapW
  have hroot10W : root + 10 < 2 ^ w := lt_trans (hltT (t1 10 (by omega)) (by decide)) hheapW
  have hh5W : tok.handle + 5 < 2 ^ w := lt_trans (hltT (t2 5 (by omega)) (by decide)) hheapW
  have hfwdW : tok.forward + e < 2 ^ w := lt_trans (hltT (t7 e hem) (by decide)) hheapW
  have hslW : tok.slots + model.extToInt e < 2 ^ w := lt_trans (hltT (t9 _ heiCap) (by decide)) hheapW
  have hLW : L < 2 ^ w := F.parameters_fit.1
  have hm0 : mem root = tok.handle := by simpa using hrootDir 0 (by simp)
  have hm3 : mem (root + 3) = tok.forward := by simpa using hrootDir 3 (by simp)
  have hm6 : mem (root + 6) = tok.slots := by simpa using hrootDir 6 (by simp)
  have hm10 : mem (root + 10) = tok.edgeRecords := by simpa using hrootDir 10 (by simp)
  have hm5 : mem (tok.handle + 5) = L := by simpa using hdetect 5 (by simp)
  have hmtree : mem tok.handle = tok.treeHeap := by simpa using hdetect 0 (by simp)
  have hslotW : mem (tok.slots + model.extToInt e) < 2 ^ w := by
    by_cases hsnz : mem (tok.slots + model.extToInt e) ≠ 0
    · rw [ite_eq_left hsnz] at hqEdge
      have := hqEdge.1; unfold isEdgeSlot at this; omega
    · rw [not_not.mp hsnz]; omega
  obtain ⟨mid, hrPref, hmidMem, hmidPos, hmR0, hmR1, hmR2, hmR3, hmR4, _, hmR6, _, hmR8⟩ :=
    queryPrefix_runs (w := w) (e := e) (heap := heap) (p := p) (ω := ω) (pos := pos)
      hroot3W hroot6W hh5W hfwdW hslW hm0 hm5 hm3 hmei hm6 rfl
  have hvalFits (val : PathEdgeValue)
      (hflow : (val.originalFlow : ℝ) / (2 : ℝ) ^ P = algorithm2_query cfg model e) :
      Num.Fits 4 L val.originalFlow := by
    obtain ⟨z, hfz, hzval⟩ := hstateFits e heG
    change algorithm2_query cfg model e = (z : ℝ) / (2 : ℝ) ^ P at hzval
    have hsc : (2 : ℝ) ^ P ≠ 0 := by positivity
    have hzEq : val.originalFlow = z := Int.cast_inj.mp ((div_left_inj' hsc).mp (hflow.trans hzval))
    rw [hzEq]; exact hfmt4 ▸ hfz
  by_cases hsnz : mem (tok.slots + model.extToInt e) ≠ 0
  · -- Tree branch (`slot ≠ 0`)
    rw [ite_eq_left hsnz] at hqEdge
    obtain ⟨his, val, hvalExp, hflowVal⟩ := hqEdge
    let slot := mem (tok.slots + model.extToInt e)
    have hInTree : model.extToInt e ∈ model.chain.toTreeChain.chainTree.E := by
      by_contra hnot
      have hbr := (hedgeAcc.1 e heM).2.2
      rw [ite_eq_right hnot] at hbr
      exact hsnz hbr.1
    have hbrT := (hedgeAcc.1 e heM).2.2
    rw [ite_eq_left hInTree] at hbrT
    obtain ⟨_, _, _, _, val0, _, hpair0, _, _, _⟩ := hbrT
    have hslotMem : slot ∈ tok.trees.flatMap AuxTree.toList :=
      pathTree_forestPair_mem_active hpair0
    have hActive : pathTreeActive tok.tree slot := ⟨tok.trees, tok.free, tok.depth, hlctInv, hslotMem⟩
    obtain ⟨t0, ht0, hsl0⟩ := List.mem_flatMap.mp hslotMem
    obtain ⟨trees', _, _, hlct', _, _, hperm, _⟩ := lctExpose_spec pathPayload_laws hlctInv ht0 hsl0
    have htreeHeapFoot : Rtree.foot tok.treeHeap tok.treeTok tok.treeHeap := by
      refine ⟨le_rfl, ?_⟩
      unfold LinkCut.PathProg.arenaEnd LinkCut.PathProg.arenaNb
      omega
    have htreeHeapW : tok.treeHeap < 2 ^ w :=
      lt_trans (hbelow tok.treeHeap (Or.inr (Or.inl htreeHeapFoot))) hheapW
    let readHeap := heap + L
    have hroom' : heap + max (L + LinkCut.PathProg.pathAlloc L 4 tok.tree.n
        [tok.treeHeap, slot, readHeap]) (2 + 5 * L) + L < 2 ^ w := hroom
    have hreadHeapW : readHeap < 2 ^ w := by omega
    let s1 := { mid with regs := Function.update mid.regs 9 tok.treeHeap }
    let s2 := { s1 with regs := Function.update s1.regs 10 readHeap }
    have r9 : Runs w p ω (.assign 9 (.load (.reg 3))) mid .normal s1 3 :=
      runs_assign_iff.mpr ⟨tok.treeHeap, by
        simp [Expr.eval, hmR3, hmidMem, hmtree], rfl, rfl, rfl⟩
    have r10 : Runs w p ω (.assign 10 (.bin .add (.reg 2) (.reg 4))) s1 .normal s2 4 :=
      runs_assign_iff.mpr ⟨readHeap, by
        simp [Expr.eval, BinOp.eval, s1, hmR2, hmR4, readHeap, hreadHeapW], rfl, rfl, rfl⟩
    have htreeBelow : ∀ a, Rtree.foot tok.treeHeap tok.treeTok a → a < readHeap := fun a ha =>
      lt_of_lt_of_le (hbelow a (Or.inr (Or.inl ha))) (Nat.le_add_right heap L)
    have hzRead : ZeroFrom mem readHeap := fun a ha => hz a (by omega)
    have hpre4 : (pathTreeMachineContract F.fmt L LinkCut.PathProg.pathC
        (LinkCut.PathProg.pathAlloc L)).pre 4 tok.tree [tok.treeHeap, slot, readHeap] mem :=
      ⟨⟨tok.trees, tok.free, tok.depth, hlctInv⟩, hfmt4 ▸ hfits, htreeWord, hfmt4 ▸ htreeWidth,
        tok.treeHeap, slot, readHeap, rfl, hActive, hfmt4 ▸ hfitsExp slot hActive⟩
    have hEvalTreeArgs : ([Expr.reg 9, Expr.reg 8, Expr.reg 10].mapM (Expr.eval w s2)) =
        some [tok.treeHeap, slot, readHeap] := by
      simp [Expr.eval, s2, s1, hmR8, slot]
    have hTreeRoom : readHeap + LinkCut.PathProg.pathAlloc L 4 tok.tree.n
        [tok.treeHeap, slot, readHeap] < 2 ^ w := by
      have hmax := Nat.le_max_left (L + LinkCut.PathProg.pathAlloc L 4 tok.tree.n
        [tok.treeHeap, slot, readHeap]) (2 + 5 * L)
      omega
    obtain ⟨s', cTree, afterTree, treeTok', ret1, hrTree, htreeRep1, hpTree, hmTree, hcTree⟩ :=
      pathTree_runs_call (i := 4) (reg := 11) (st := s2) (ω := ω)
        (args := [.reg 9, .reg 8, .reg 10]) (vs := [tok.treeHeap, slot, readHeap])
        hTreeImpl hEvalTreeArgs (by wram_words) rfl (hmidMem.symm ▸ htreeRep)
        (hmidMem.symm ▸ hpre4) htreeBelow (hmidMem.symm ▸ hzRead)
        (by simpa [pathTreeMachineContract, heapArg] using hTreeRoom)
    obtain ⟨hs', hrecAt⟩ := hpTree
    change s' = lctExpose pathPayload tok.tree slot at hs'
    subst hs'
    have hrecVal : PathEdgeAt afterTree.mem readHeap 4 L (some val) := by
      change PathEdgeAt afterTree.mem readHeap F.fmt.limbBits L
        ((lctExpose pathPayload tok.tree slot).splay.nodes slot).val at hrecAt
      rw [hvalExp, hfmt4] at hrecAt
      exact hrecAt
    have hret1Lo : readHeap ≤ ret1 := hmTree.1
    have hret1Hi : ret1 ≤ readHeap + LinkCut.PathProg.pathAlloc L 4 tok.tree.n
        [tok.treeHeap, slot, readHeap] := hmTree.2.1
    have hret1W : ret1 < 2 ^ w := by omega
    let minWr := readHeap + 2 + 4 * L
    have hminWrLe : minWr ≤ heap + max (L + LinkCut.PathProg.pathAlloc L 4 tok.tree.n
        [tok.treeHeap, slot, readHeap]) (2 + 5 * L) := by
      have hmax := Nat.le_max_right (L + LinkCut.PathProg.pathAlloc L 4 tok.tree.n
        [tok.treeHeap, slot, readHeap]) (2 + 5 * L)
      omega
    have hminWrW : minWr < 2 ^ w := by omega
    have hw4 : 4 < 2 ^ w := by omega
    have hw2 : 2 < 2 ^ w := by omega
    have h4LW : 4 * L < 2 ^ w := by omega
    have hr2W : readHeap + 2 < 2 ^ w := by omega
    let after1 := { afterTree with regs := Function.update s2.regs 11 ret1 }
    let after2 := { after1 with regs := Function.update after1.regs 13 minWr }
    have r13 : Runs w p ω
        (.assign 13 (.bin .add (.bin .add (.reg 10) (.const 2)) (.bin .mul (.const 4) (.reg 4))))
        after1 .normal after2 8 :=
      runs_assign_iff.mpr ⟨minWr, by
        simp [Expr.eval, BinOp.eval, after1, s2, s1, hmR4, hw2, hw4, hr2W, h4LW, minWr, hminWrW],
        rfl, rfl, rfl⟩
    let wrHeap := max ret1 minWr
    have hwrHeapLe : wrHeap ≤ heap + max (L + LinkCut.PathProg.pathAlloc L 4 tok.tree.n
        [tok.treeHeap, slot, readHeap]) (2 + 5 * L) := by
      have hmax := Nat.le_max_left (L + LinkCut.PathProg.pathAlloc L 4 tok.tree.n
        [tok.treeHeap, slot, readHeap]) (2 + 5 * L)
      omega
    have hwrHeapW : wrHeap < 2 ^ w := by omega
    let after3 := { after2 with regs := Function.update after2.regs 11 wrHeap }
    have rMax : ∃ cMax, Runs w p ω
        (.cond (.bin .lt (.reg 11) (.reg 13)) (.assign 11 (.reg 13)) .nop)
        after2 .normal after3 cMax ∧ cMax ≤ 8 := by
      by_cases hlt : ret1 < minWr
      · have hwrEq : wrHeap = minWr := max_eq_right hlt.le
        refine ⟨6, runs_cond_iff.mpr ⟨1, 2, by
          have hwnz : ¬ w = 0 := fun h => by subst h; simp at hw10
          simp [Expr.eval, BinOp.eval, after2, after1, hlt, hwnz],
          by
            simp only [Nat.one_ne_zero, ite_false]
            exact runs_assign_iff.mpr ⟨minWr, by simp [Expr.eval, after2], rfl,
              by simp [after3, hwrEq], rfl⟩,
          rfl⟩, by omega⟩
      · have hwrEq : wrHeap = ret1 := max_eq_left (Nat.le_of_not_lt hlt)
        have ha3Eq : after3 = after2 := by
          dsimp only [after3, after2, after1]
          congr 1
          funext r
          by_cases hr : r = 11
          · subst hr; simp [hwrEq]
          · simp [Function.update_of_ne hr]
        refine ⟨5, runs_cond_iff.mpr ⟨0, 1, by
          simp [Expr.eval, BinOp.eval, after2, after1, hlt],
          by
            simp only [ite_true]
            rw [ha3Eq]
            exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩,
          rfl⟩, by omega⟩
    obtain ⟨cMax, hrMax, hcMax⟩ := rMax
    have hEvalWrArgs : ([Expr.reg 10, Expr.reg 4, Expr.reg 2, Expr.reg 11].mapM (Expr.eval w after3)) =
        some [readHeap, L, heap, wrHeap] := by
      simp [Expr.eval, after3, after2, after1, s2, s1, hmR4, hmR2]
    have hwrCall : ∃ o out cW,
        Runs w p ω (.call 12 queryReserved [.reg 10, .reg 4, .reg 2, .reg 11] ;; .ret (.reg 12))
          after3 o out cW ∧
        (∃ ret, o = .returned ret ∧
          (queryReservedContract w 4 P val).post [readHeap, L, heap, wrHeap] afterTree.mem ret out.mem) ∧
        cW ≤ 53 * L + 80 := by
      apply runs_start_le
      refine runs_seq_call_le (hQResv val) (vs := [readHeap, L, heap, wrHeap])
        hEvalWrArgs (by wram_words) ?_ ?_
      · refine ⟨readHeap, L, heap, wrHeap, rfl, by omega, by omega, by omega, hrecVal,
          hvalFits val hflowVal, fun a ha => hmTree.2.2.1 a (by omega), by omega⟩
      · intro ret mem₂ pos₂ hpost
        have hpost0 := hpost
        obtain ⟨_, _, _, _, heq, hretEq, _⟩ := hpost
        simp only [List.cons.injEq, and_true] at heq
        obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
        have hretW : ret < 2 ^ w := by omega
        refine runs_ret_le (v := ret) (by simp [Expr.eval]) ⟨ret, rfl, hpost0⟩ ?_
        simp [queryReservedContract, Expr.size, argsSize]
        omega
    obtain ⟨_, out, cW, hrW, ⟨ret, rfl, _, _, _, _, heqW, hretEq, hscalar, hframeW, hzW⟩, hcW⟩ := hwrCall
    simp only [List.cons.injEq, and_true] at heqW
    obtain ⟨rfl, rfl, rfl, rfl⟩ := heqW
    have htreeFoot_ret : ∀ a, Rtree.foot tok.treeHeap treeTok' a →
        Rtree.foot tok.treeHeap tok.treeTok a ∨ (heap ≤ a ∧ a < ret) := fun a ha =>
      (hmTree.2.2.2.2 a ha).imp_right (fun ⟨h1, h2⟩ => ⟨by change readHeap ≤ a at h1; omega,
        by change a < ret1 at h2; omega⟩)
    have htreeRepOut : Rtree.rep tok.treeHeap (lctExpose pathPayload tok.tree slot) treeTok' out.mem := by
      refine ((LinkCut.PathProg.pathRep_local 4 L LinkCut.PathProg.pathC) tok.treeHeap _ treeTok'
        afterTree.mem out.mem (fun a ha => ?_)).1 htreeRep1
      rcases hmTree.2.2.2.2 a ha with hold | ⟨hlo, hhi⟩
      · have hlt : a < heap := hbelow a (Or.inr (Or.inl hold))
        exact (hframeW a (by omega) (Or.inl hlt)).symm
      · change readHeap ≤ a at hlo; change a < ret1 at hhi
        exact (hframeW a (by omega) (Or.inr (by omega))).symm
    have htreePhiOut : Rtree.phi tok.treeHeap treeTok' out.mem =
        Rtree.phi tok.treeHeap treeTok' afterTree.mem := by
      refine ((LinkCut.PathProg.pathRep_local 4 L LinkCut.PathProg.pathC) tok.treeHeap
        (lctExpose pathPayload tok.tree slot) treeTok'
        afterTree.mem out.mem (fun a ha => ?_)).2.symm
      rcases hmTree.2.2.2.2 a ha with hold | ⟨hlo, hhi⟩
      · have hlt : a < heap := hbelow a (Or.inr (Or.inl hold))
        exact (hframeW a (by omega) (Or.inl hlt)).symm
      · change readHeap ≤ a at hlo; change a < ret1 at hhi
        exact (hframeW a (by omega) (Or.inr (by omega))).symm
    have hframeOut : ∀ a < heap, ¬ Rtree.foot tok.treeHeap tok.treeTok a → out.mem a = mem a := by
      intro a ha hnt
      have h1 : out.mem a = afterTree.mem a := hframeW a (by omega) (Or.inl ha)
      have h2 : afterTree.mem a = mem a := hmidMem ▸ hmTree.2.2.2.1 a (by change a < readHeap; omega) hnt
      exact h1.trans h2
    obtain ⟨hrepOut, hcorePhiOut⟩ := solverStateRep_after_queryExpose hlocalCore hrep0 hbelow
      hframeOut htreeFoot_ret hlct' hslotMem hperm htreeRepOut
    have hbranchRun : Runs w p ω
        (.assign 9 (.load (.reg 3)) ;;
         .assign 10 (.bin .add (.reg 2) (.reg 4)) ;;
         .call 11 (opTree 4) [.reg 9, .reg 8, .reg 10] ;;
         .assign 13 (.bin .add (.bin .add (.reg 10) (.const 2)) (.bin .mul (.const 4) (.reg 4))) ;;
         .cond (.bin .lt (.reg 11) (.reg 13)) (.assign 11 (.reg 13)) .nop ;;
         .call 12 queryReserved [.reg 10, .reg 4, .reg 2, .reg 11] ;;
         .ret (.reg 12)) mid (.returned ret) out
        (3 + (4 + (cTree + (8 + (cMax + cW + 1) + 1) + 1) + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨s1, 3, _, r9,
        runs_seq_iff.mpr (Or.inr ⟨s2, 4, _, r10,
          runs_seq_iff.mpr (Or.inr ⟨after1, cTree, _, hrTree,
            runs_seq_iff.mpr (Or.inr ⟨after2, 8, _, r13,
              runs_seq_iff.mpr (Or.inr ⟨after3, cMax, cW, hrMax, hrW, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    have hcondRun : Runs w p ω
        (.cond (.reg 8)
          (.assign 9 (.load (.reg 3)) ;;
           .assign 10 (.bin .add (.reg 2) (.reg 4)) ;;
           .call 11 (opTree 4) [.reg 9, .reg 8, .reg 10] ;;
           .assign 13 (.bin .add (.bin .add (.reg 10) (.const 2)) (.bin .mul (.const 4) (.reg 4))) ;;
           .cond (.bin .lt (.reg 11) (.reg 13)) (.assign 11 (.reg 13)) .nop ;;
           .call 12 queryReserved [.reg 10, .reg 4, .reg 2, .reg 11] ;;
           .ret (.reg 12))
          (.assign 9 (.load (.bin .add (.reg 0) (.const 10))) ;;
           .assign 10 (.load (.bin .add (.reg 9) (.reg 6))) ;;
           .call 11 queryResolved [.reg 10, .reg 4, .reg 2] ;;
           .ret (.reg 11))) mid (.returned ret) out
        (1 + (3 + (4 + (cTree + (8 + (cMax + cW + 1) + 1) + 1) + 1) + 1) + 1) :=
      runs_cond_iff.mpr ⟨slot, _, by simp [Expr.eval, hmR8, slot],
        by rw [ite_eq_right hsnz]; exact hbranchRun, rfl⟩
    let tok' : SolverToken cfg L Rcore :=
      { tok with
        tree := lctExpose pathPayload tok.tree slot
        trees := trees'
        treeTok := treeTok'
        owned := fun a => tok.owned a ∨ (heap ≤ a ∧ a < ret)
        tag := fun a => if heap ≤ a ∧ a < ret then 16 else tok.tag a }
    have hsumCore : (∑ i : Fin cfg.P.d, Rcore.phi (tok'.coreHandle i.val) (tok'.coreTok i.val) out.mem) =
        ∑ i : Fin cfg.P.d, Rcore.phi (tok.coreHandle i.val) (tok.coreTok i.val) mem :=
      Finset.sum_congr rfl fun i _ => hcorePhiOut i.val i.isLt
    have hcTree' : cTree + Rtree.phi tok.treeHeap treeTok' afterTree.mem ≤
        pathTreeBudget LinkCut.PathProg.pathC L tok.tree.n + Rtree.phi tok.treeHeap tok.treeTok mem + 6 := by
      have h1 : cTree + Rtree.phi tok.treeHeap treeTok' afterTree.mem ≤
          pathTreeBudget LinkCut.PathProg.pathC L tok.tree.n +
            Rtree.phi tok.treeHeap tok.treeTok s2.mem +
            argsSize [Expr.reg 9, Expr.reg 8, Expr.reg 10] + 1 := hcTree
      have hs2m : s2.mem = mem := hmidMem
      have harg : argsSize [Expr.reg 9, Expr.reg 8, Expr.reg 10] = 3 := by
        simp [argsSize, Expr.size]
      rw [hs2m, harg] at h1
      omega
    have hPresMeta : PreservesLevelMeta tok tok' mem out.mem := by
      refine ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ ha => Or.inl ha, fun a ht => ?_⟩
      have hnz : tok.tag a ≠ 0 := by rcases ht with h | h | h | h <;> omega
      have hne16 : tok.tag a ≠ 16 := by rcases ht with h | h | h | h <;> omega
      have hlt : a < heap := hbelow a (Or.inl (hOwn a hnz))
      exact ⟨by dsimp only [tok']; rw [ite_eq_right (by omega)],
        hframeOut a hlt (fun hf => hne16 (t16 a hf))⟩
    refine ⟨ret, 33 + (1 + (3 + (4 + (cTree + (8 + (cMax + cW + 1) + 1) + 1) + 1) + 1) + 1) + 1,
      out, tok',
      runs_seq_iff.mpr (Or.inr ⟨mid, 33, _, hrPref, hcondRun, rfl⟩),
      ⟨rfl, by
        change ScalarAt out.mem heap F.fmt.limbBits L P (algorithm2_query cfg model e)
        rw [← hflowVal, hfmt4]
        exact hscalar⟩,
      hrepOut, hPresMeta, rfl, hzW, by omega,
      by change ret ≤ heap + max (L + LinkCut.PathProg.pathAlloc L 4 tok.tree.n
          [tok.treeHeap, slot, readHeap]) (2 + 5 * L) + L; omega,
      fun a ha hnf => hframeOut a ha (fun ht => hnf (Or.inr (Or.inl ht))),
      fun a ha => by
        rcases ha with (ho | hnew) | htf | hcf
        · exact Or.inl (Or.inl ho)
        · exact Or.inr hnew
        · exact (htreeFoot_ret a htf).imp_left (fun h => Or.inr (Or.inl h))
        · exact Or.inl (Or.inr (Or.inr hcf)),
      ?_, fun B R hn => by
        obtain ⟨ts, WE, hnE⟩ := pathTreeNumericInv_expose hlctInv hn ht0 hsl0
        exact hnE.relabel WE hlct',
      rfl, fun j hj => hframeOut _ (hltT (t13 j hj) (by decide)) fun hf => by
        have h16 := t16 _ hf
        rw [t13 j hj] at h16
        exact absurd h16 (by decide)⟩
    change _ + (Rtree.phi tok.treeHeap treeTok' out.mem +
      (∑ i : Fin cfg.P.d, Rcore.phi (tok'.coreHandle i.val) (tok'.coreTok i.val) out.mem) +
      tok.offReadyCount * drainUnit) ≤
      pathTreeBudget LinkCut.PathProg.pathC L model.extG.n + 53 * L + 160 +
      (Rtree.phi tok.treeHeap tok.treeTok mem +
        (∑ i : Fin cfg.P.d, Rcore.phi (tok.coreHandle i.val) (tok.coreTok i.val) mem) +
        tok.offReadyCount * drainUnit)
    rw [htreePhiOut, hsumCore, ← htn]
    omega
  · -- Off-tree branch (`slot = 0`)
    have hs0 : mem (tok.slots + model.extToInt e) = 0 := not_not.mp hsnz
    rw [ite_eq_right hsnz] at hqEdge
    obtain ⟨val, hrec, hflowVal⟩ := hqEdge
    have hNotTree : model.extToInt e ∉ model.chain.toTreeChain.chainTree.E := by
      intro hin
      have hbr := (hedgeAcc.1 e heM).2.2
      rw [ite_eq_left hin] at hbr
      exact hbr.1 hs0
    let recPtr := mem (tok.edgeRecords + model.extToInt e)
    have hrecEnd : recPtr + 2 + 4 * L ≤ heap := by
      have hlast : recPtr + (2 + 4 * L - 1) < heap :=
        hltT ((t1718 e heM).2 hNotTree (2 + 4 * L - 1) (by omega)) (by decide)
      omega
    have herW : tok.edgeRecords + model.extToInt e < 2 ^ w :=
      lt_trans (hltT (t13 _ heiCap) (by decide)) hheapW
    have hrecPtrW : recPtr < 2 ^ w := by omega
    let s1 := { mid with regs := Function.update mid.regs 9 tok.edgeRecords }
    let s2 := { s1 with regs := Function.update s1.regs 10 recPtr }
    have r9 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 0) (.const 10)))) mid .normal s1 5 :=
      runs_assign_iff.mpr ⟨tok.edgeRecords, by
        simp [Expr.eval, BinOp.eval, hmR0, hmidMem, hw10, hroot10W, hm10], rfl, rfl, rfl⟩
    have r10 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 9) (.reg 6)))) s1 .normal s2 5 :=
      runs_assign_iff.mpr ⟨recPtr, by
        simp [Expr.eval, BinOp.eval, s1, hmR6, hmidMem, herW, recPtr], rfl, rfl, rfl⟩
    have hqCall : ∃ o out c,
        Runs w p ω (.call 11 queryResolved [.reg 10, .reg 4, .reg 2] ;; .ret (.reg 11)) s2 o out c ∧
        (∃ ret, o = .returned ret ∧
          (queryResolvedContract w 4 P val).post [recPtr, L, heap] mem ret out.mem) ∧
        c ≤ 36 * L + 57 := by
      apply runs_start_le
      refine runs_seq_call_le (hQRes val) (vs := [recPtr, L, heap])
        (by simp [evalArgs, Expr.eval, s2, s1, hmR4, hmR2]) (by wram_words) ?_ ?_
      · refine ⟨recPtr, L, heap, rfl, by omega, hrecEnd, hmidMem.symm ▸ hrec,
          hvalFits val hflowVal, hmidMem.symm ▸ hz, by omega⟩
      · intro ret mem₁ pos₁ hpost
        have hretEq : ret = heap + L := hpost.1
        have hretW : ret < 2 ^ w := by omega
        refine runs_ret_le (v := ret) (by simp [Expr.eval]) ⟨ret, rfl, hmidMem ▸ hpost⟩ ?_
        simp [queryResolvedContract, Expr.size, argsSize]
        omega
    obtain ⟨_, out, cQ, hrQ, ⟨ret, rfl, hretEq, hscalar, hframeQ, hzQ⟩, hcQ⟩ := hqCall
    have hbranchRun : Runs w p ω
        (.assign 9 (.load (.bin .add (.reg 0) (.const 10))) ;;
         .assign 10 (.load (.bin .add (.reg 9) (.reg 6))) ;;
         .call 11 queryResolved [.reg 10, .reg 4, .reg 2] ;;
         .ret (.reg 11)) mid (.returned ret) out (5 + (5 + cQ + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨s1, 5, 5 + cQ + 1, r9,
        runs_seq_iff.mpr (Or.inr ⟨s2, 5, cQ, r10, hrQ, rfl⟩), rfl⟩)
    have hcondRun : Runs w p ω
        (.cond (.reg 8)
          (.assign 9 (.load (.reg 3)) ;;
           .assign 10 (.bin .add (.reg 2) (.reg 4)) ;;
           .call 11 (opTree 4) [.reg 9, .reg 8, .reg 10] ;;
           .assign 13 (.bin .add (.bin .add (.reg 10) (.const 2)) (.bin .mul (.const 4) (.reg 4))) ;;
           .cond (.bin .lt (.reg 11) (.reg 13)) (.assign 11 (.reg 13)) .nop ;;
           .call 12 queryReserved [.reg 10, .reg 4, .reg 2, .reg 11] ;;
           .ret (.reg 12))
          (.assign 9 (.load (.bin .add (.reg 0) (.const 10))) ;;
           .assign 10 (.load (.bin .add (.reg 9) (.reg 6))) ;;
           .call 11 queryResolved [.reg 10, .reg 4, .reg 2] ;;
           .ret (.reg 11))) mid (.returned ret) out (1 + (5 + (5 + cQ + 1) + 1) + 1) :=
      runs_cond_iff.mpr ⟨0, 5 + (5 + cQ + 1) + 1, by simp [Expr.eval, hmR8, hs0],
        by simpa using hbranchRun, rfl⟩
    have hagFoot : ∀ a, R.foot root tok a → mem a = out.mem a :=
      fun a ha => (hframeQ a (hbelow a ha)).symm
    have hlocR := solverStateRep_local cfg L P m V psi k epsExp drainUnit hlocalCore
    have hrepOut : R.rep root model tok out.mem := (hlocR root model tok mem out.mem hagFoot).1 hrep0
    have hphiOut : R.phi root tok out.mem = R.phi root tok mem :=
      ((hlocR root model tok mem out.mem hagFoot).2).symm
    have hPresMeta : PreservesLevelMeta tok tok mem out.mem :=
      ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ ha => ha, fun a ht => by
        have hnz : tok.tag a ≠ 0 := by rcases ht with h | h | h | h <;> omega
        exact ⟨rfl, hframeQ a (hbelow a (Or.inl (hOwn a hnz)))⟩⟩
    refine ⟨ret, 33 + (1 + (5 + (5 + cQ + 1) + 1) + 1) + 1, out, tok,
      runs_seq_iff.mpr (Or.inr ⟨mid, 33, _, hrPref, hcondRun, rfl⟩),
      ⟨rfl, by
        change ScalarAt out.mem heap F.fmt.limbBits L P (algorithm2_query cfg model e)
        rw [← hflowVal, hfmt4]
        exact hscalar⟩,
      hrepOut, hPresMeta, rfl, hzQ, by change ret = heap + L at hretEq; omega,
      by change ret = heap + L at hretEq; omega,
      fun a ha _ => hframeQ a ha, fun a ha => Or.inl ha, ?_, fun _ _ hn => hn, rfl,
      fun j hj => hframeQ _ (hltT (t13 j hj) (by decide))⟩
    dsimp only [R, L, P] at hphiOut ⊢; rw [hphiOut]; omega

end MinCostFlow.MinRatio
