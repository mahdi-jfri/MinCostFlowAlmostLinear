module

public import MinCostFlow.MinRatio.DetectTreePhase
public import MinCostFlow.MinRatio.DetectOffTreeDrain
import WordRAM.Tactic

/-!
# End-to-end Word-RAM `Detect` assembly (`minRatioMachineContractWithV` op 2)

Implements Definition 4.5 `Detect()` (`[root, base]`) against `solverStateRep`
(with `drainUnit := detectOffTreeDrainUnit F.limbs`) and `minRatioMachineContractWithV`
operation 2:
1. Loads the handle, path tree, lookup tables, `m`, and `L` via `detectPrefixLoad`,
   setting `cursor := base + 1` and `curHeap := base + 1 + m`.
2. Runs `detectTreePhaseBody` to report and reset every ready tree edge in `treeReadySet model`.
3. Runs `detectOffTreeDrainBody` to drain `offReadyList`, emitting and resetting every
   live ready off-tree edge (whose scan cost cancels against the `tok.offReadyCount * drainUnit`
   potential drop in `solverStateRep.phi`).
4. Stores the total count `cursor - (base + 1)` at `mem base` and returns `curHeap`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine

/-- Fixed deterministic `Detect` entry procedure taking `[root, base]` and returning the
new free heap pointer after writing `DetectAt mem' base (algorithm2_detect cfg model).1`. -/
@[expose] def solverDetectBody (opFindReady opPointRead opPointWrite isNeg reset : ℕ) : Stmt :=
  detectPrefixLoad ;;
  detectTreePhaseBody opFindReady opPointRead opPointWrite reset ;;
  detectOffTreeDrainBody isNeg reset ;;
  .store (.reg 1) (.bin .sub (.reg 3) (.bin .add (.reg 1) (.const 1))) ;;
  .ret (.reg 4)

theorem solverDetectBody_noRand (opFindReady opPointRead opPointWrite isNeg reset : ℕ) :
    (solverDetectBody opFindReady opPointRead opPointWrite isNeg reset).NoRand := by
  simp [solverDetectBody, detectPrefixLoad, detectTreePhaseBody_noRand,
    detectOffTreeDrainBody_noRand, Stmt.NoRand]

private theorem listAt_congr'' {mem mem' : ℕ → ℕ} {base : ℕ} {xs : List ℕ}
    (h : ListAt mem base xs) (hag : ∀ j < xs.length, mem' (base + j) = mem (base + j)) :
    ListAt mem' base xs := fun j hj => (hag j hj).trans (h j hj)

/-- Intermediate `solverStateRep` after `detectTreePhaseBody`: tree edges have their
post-`Detect` accounts while off-tree edges still hold `model.detectAccum`. -/
theorem solverStateRep_after_treePhase {cfg : Alg2Config}
    {L P m V psi k epsExp drainUnit : ℕ} {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)}
    (hlocalCore : Rcore.Local)
    {root base heap₀ curHeap₁ : ℕ} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {mem mem₁ : ℕ → ℕ}
    {treeRep : List ℕ} {curTree : PathTreeState} {curTrees : List AuxTree}
    {curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ}
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hbelow : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a → a < base)
    (hbaseHeap : base + 1 + m ≤ heap₀)
    (hcn : curTree.n = tok.tree.n)
    (hlct : LctInvWith pathPayload curTree curTrees tok.free tok.depth)
    (htrep : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).rep tok.treeHeap curTree curTreeTok mem₁)
    (hfoot : ∀ a, (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap curTreeTok a →
      (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap tok.treeTok a ∨
        (heap₀ ≤ a ∧ a < curHeap₁))
    (hframe : ∀ a < heap₀, ¬ (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap tok.treeTok a →
      (a < base + 1 ∨ base + 1 + treeRep.length ≤ a) → mem₁ a = mem a)
    (htreeAcc : ∀ e ∈ model.extG.E,
      let ei := model.extToInt e
      ei ∈ model.chain.toTreeChain.chainTree.E →
      let slot := mem (tok.slots + ei)
      ∃ val : PathEdgeValue, ∃ account : ℤ,
        (slot, some val) ∈ forestPairs pathPayload curTree.splay curTrees ∧
        (val.originalFlow : ℝ) / (2 : ℝ) ^ P = model.flow e ∧
        (account : ℝ) / (2 : ℝ) ^ P = (algorithm2_detect cfg model).2.detectAccum e ∧
        val.detector = account - detectorThreshold P cfg.ε (model.extℓ e) ∧
        (val.originalGradient : ℝ) / (2 : ℝ) ^ P = model.extg e ∧
        (val.length : ℝ) / (2 : ℝ) ^ P = model.extℓ e ∧
        (val.forward = true →
          inducedSubPar pathPayload curTree.splay curTrees (vid (model.chain.toTreeChain.chainTree.head ei)) = slot ∧
          inducedSubPar pathPayload curTree.splay curTrees slot = vid (model.chain.toTreeChain.chainTree.tail ei)) ∧
        (val.forward = false →
          inducedSubPar pathPayload curTree.splay curTrees (vid (model.chain.toTreeChain.chainTree.tail ei)) = slot ∧
          inducedSubPar pathPayload curTree.splay curTrees slot = vid (model.chain.toTreeChain.chainTree.head ei)))
    (htreeRev : ∀ slot val, isEdgeSlot curTree.n slot →
      (slot, some val) ∈ forestPairs pathPayload curTree.splay curTrees →
      let ei := mem (tok.names + slot)
      let e := model.intToExt ei
      ei < tok.intCap ∧ ei ∈ model.chain.toTreeChain.chainTree.E ∧
      mem (tok.slots + ei) = slot ∧ e ∈ model.extG.E ∧ model.extToInt e = ei)
    (hns : TreeEditNamedSlots curTree curTrees model.chain.toTreeChain.chainTree
      (fun f => mem (tok.slots + f)) (fun k => mem (tok.names + k))) :
    let modelMid : Alg2State cfg :=
      { model with detectAccum := fun e =>
          if model.extToInt e ∈ model.chain.toTreeChain.chainTree.E then
            (algorithm2_detect cfg model).2.detectAccum e
          else model.detectAccum e }
    let tokMid : SolverToken cfg L Rcore :=
      { tok with
        tree := curTree
        trees := curTrees
        treeTok := curTreeTok
        owned := fun a => tok.owned a ∨ (heap₀ ≤ a ∧ a < curHeap₁)
        tag := fun a => if heap₀ ≤ a ∧ a < curHeap₁ then 16 else tok.tag a }
    (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root modelMid tokMid mem₁ ∧
    (∀ a, tokMid.tag a ≠ 0 → tokMid.tag a ≠ 16 → a < base) ∧
    (∀ i < cfg.P.d, Rcore.phi (tokMid.coreHandle i) (tokMid.coreTok i) mem₁ =
      Rcore.phi (tok.coreHandle i) (tok.coreTok i) mem) := by
  dsimp only
  obtain ⟨hrootDir, hdetect, hnum, hchainP, hfreshInv, hfreshTab, hextM, hintCapE,
    hsched, hoffReady, htn, _, _, hedgeAcc, hcores, htermH, htermBr, htermRep, hwire, htags⟩ := hrep
  obtain ⟨hOwn, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15,
    t16, t1718, t19, t20, t21⟩ := htags
  have hltB {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) : a < base :=
    hbelow a (Or.inl (hOwn a (ht ▸ hv)))
  have hagT {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) (hv16 : v ≠ 16) : mem₁ a = mem a := by
    have haB := hltB ht hv
    exact hframe a (by omega) (fun hf => hv16 (ht.symm.trans (t16 a hf))) (Or.inl (by omega))
  have htagKeep {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) :
      (if heap₀ ≤ a ∧ a < curHeap₁ then 16 else tok.tag a) = v := by
    have haB := hltB ht hv
    rw [ite_eq_right (by omega)]; exact ht
  have htermLocal := LastLevelProgram.lastLevelRepresentation_local tok.vcLast tok.ecLast
    4 L P (model.chain.G cfg.P.d).E
  have hcore_ag (i : ℕ) (hi : i < cfg.P.d) (a : ℕ) (ha : Rcore.foot (tok.coreHandle i) (tok.coreTok i) a) :
      mem a = mem₁ a := (hagT (t21 i hi a ha) (by omega) (by omega)).symm
  have hterm_ag (a : ℕ)
      (ha : (LastLevelProgram.lastLevelRepresentation tok.vcLast tok.ecLast 4 L P
        (model.chain.G cfg.P.d).E).foot tok.termHandle tok.termTok a) : mem a = mem₁ a :=
    (hagT (t19 a ((lastLevelRepresentation_foot_indep_P _ _ _ _ P 0 _ _ _ _).mp ha))
      (by decide) (by decide)).symm
  refine ⟨⟨listAt_congr'' hrootDir (fun j hj => hagT (t1 j (by simpa [List.length] using hj)) (by decide) (by decide)),
    listAt_congr'' hdetect (fun j hj => hagT (t2 j (by simp [List.length] at hj; omega)) (by decide) (by decide)),
    listAt_congr'' hnum (fun j hj => by
      have h1 : tok.handle + 5 + j = tok.handle + (5 + j) := by omega
      rw [h1]; exact hagT (t2 (5 + j) (by simp [List.length] at hj; omega)) (by decide) (by decide)),
    listAt_congr'' hchainP (fun j hj => by
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
    ?_, hcn.trans htn, hlct, htrep, ?_, ?_,
    (hagT (t4 cfg.P.d (by omega)) (by decide) (by decide)).trans htermH,
    by
      have h1 : tok.handle + 18 + (cfg.P.d + 1) + cfg.P.d = tok.handle + 18 + (2 * cfg.P.d + 1) := by omega
      rw [h1] at htermBr ⊢; exact (hagT (t4 _ (by omega)) (by decide) (by decide)).trans htermBr,
    (htermLocal tok.termHandle _ tok.termTok mem mem₁ hterm_ag).1 htermRep, ?_, ?_⟩,
    fun a hnz h16 => by
      by_cases hr : heap₀ ≤ a ∧ a < curHeap₁
      · rw [ite_eq_left hr] at h16; exact False.elim (h16 rfl)
      · rw [ite_eq_right hr] at hnz; exact hbelow a (Or.inl (hOwn a hnz)),
    fun i hi => (hlocalCore (tok.coreHandle i) (chainLevelOrdAbs model.chain i) (tok.coreTok i)
      mem mem₁ (hcore_ag i hi)).2.symm⟩
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
  · constructor
    · intro e heE; dsimp only
      obtain ⟨heiCap, hthr0, hbr0⟩ := hedgeAcc.1 e heE
      have hetEq : mem₁ (tok.edgeThresholds + model.extToInt e) =
          mem (tok.edgeThresholds + model.extToInt e) := hagT (t12 _ heiCap) (by decide) (by decide)
      have hslEq : mem₁ (tok.slots + model.extToInt e) = mem (tok.slots + model.extToInt e) :=
        hagT (t9 _ heiCap) (by decide) (by decide)
      have hioEq : mem₁ (tok.inOffReady + model.extToInt e) = mem (tok.inOffReady + model.extToInt e) :=
        hagT (t15 _ heiCap) (by decide) (by decide)
      refine ⟨heiCap, by rw [hetEq]; exact hthr0.congr (fun j hj => hagT ((t1718 e heE).1 j hj) (by decide) (by decide)), ?_⟩
      by_cases hin : model.extToInt e ∈ model.chain.toTreeChain.chainTree.E
      · rw [ite_eq_left hin] at hbr0 ⊢
        obtain ⟨hsnz, his, hnm, hst, _⟩ := hbr0
        have hisLt : mem (tok.slots + model.extToInt e) < 2 * tok.tree.n := his.2
        rw [hslEq]
        refine ⟨hsnz, hcn.symm ▸ his, (hagT (t10 _ hisLt) (by decide) (by decide)).trans hnm,
          (hagT (t11 _ hisLt) (by decide) (by decide)).trans (hst.trans hetEq.symm), ?_⟩
        obtain ⟨val, acc, hp, hfl, hac, hd, _, _⟩ := htreeAcc e heE hin
        exact ⟨val, acc, hp, hfl, by simpa [hin] using hac, hd⟩
      · rw [ite_eq_right hin] at hbr0 ⊢
        obtain ⟨hs0, val, acc, hrec0, hfl, hac, hd, hpush⟩ := hbr0
        have herEq : mem₁ (tok.edgeRecords + model.extToInt e) =
            mem (tok.edgeRecords + model.extToInt e) := hagT (t13 _ heiCap) (by decide) (by decide)
        refine ⟨hslEq.trans hs0, val, acc, ?_, hfl, by simpa [hin] using hac, hd,
          fun hn => hioEq.trans (hpush hn)⟩
        rw [herEq]
        exact hrec0.congr (fun a ha1 ha2 => by
          have haIdx : a = mem (tok.edgeRecords + model.extToInt e) + (a - mem (tok.edgeRecords + model.extToInt e)) := by omega
          rw [haIdx]; exact hagT ((t1718 e heE).2 hin _ (by omega)) (by decide) (by decide))
    · intro slot val his hp
      have hisLt : slot < 2 * tok.tree.n := hcn ▸ his.2
      have hnmEq : mem₁ (tok.names + slot) = mem (tok.names + slot) :=
        hagT (t10 slot hisLt) (by decide) (by decide)
      obtain ⟨h1, h2, h3, h4, h5⟩ := htreeRev slot val his hp
      dsimp only
      rw [hnmEq]
      exact ⟨h1, h2, (hagT (t9 _ h1) (by decide) (by decide)).trans h3, h4, h5⟩
  · intro i hi
    obtain ⟨hh, hbr, hcr⟩ := hcores i hi
    refine ⟨(hagT (t4 i (by omega)) (by decide) (by decide)).trans hh,
      by
        have h1 : tok.handle + 18 + (cfg.P.d + 1) + i = tok.handle + 18 + (cfg.P.d + 1 + i) := by omega
        rw [h1] at hbr ⊢; exact (hagT (t4 _ (by omega)) (by decide) (by decide)).trans hbr,
      (hlocalCore (tok.coreHandle i) _ (tok.coreTok i) mem mem₁ (hcore_ag i hi)).1 hcr⟩
  · obtain ⟨htabW, hrgW, hsubCap, _, hglW⟩ := hwire
    refine ⟨fun j hj => (hagT (t3 j hj) (by decide) (by decide)).trans (htabW j hj),
      hrgW.of_agree (fun a h1 h2 => hagT (t20 a h1 h2) (by decide) (by decide)), hsubCap,
      ⟨fun ei hei => by
          rw [hagT (t9 ei (hsubCap.2 ei hei).1) (by decide) (by decide)]
          have hfwd := hns.forward ei hei
          have hslotLt : mem (tok.slots + ei) < 2 * tok.tree.n := by unfold isEdgeSlot at hfwd; omega
          exact ⟨hfwd.1, hfwd.2.1, (hagT (t10 _ hslotLt) (by decide) (by decide)).trans hfwd.2.2⟩,
        fun k hk hks => by
          have hkLt : k < 2 * tok.tree.n := by simpa [hcn] using hks.2
          rw [hagT (t10 k hkLt) (by decide) (by decide)]
          obtain ⟨hmem, hslot⟩ := hns.inverse k hk hks
          exact ⟨hmem, (hagT (t9 _ (hsubCap.2 _ hmem).1) (by decide) (by decide)).trans hslot⟩,
        fun ei hei => by
          rw [hagT (t9 ei (hsubCap.2 ei hei).1) (by decide) (by decide)]; exact hns.endpoints ei hei⟩,
      fun e he => by
        dsimp only
        have heiCap := (hedgeAcc.1 e he).1
        split_ifs with hin
        · intro val hp
          rw [hagT (t9 _ heiCap) (by decide) (by decide)] at hp ⊢
          obtain ⟨val0, _, hp0, _, _, _, hgrad0, hlen0, hft0, hff0⟩ := htreeAcc e he hin
          have hvEq := forestPairs_val_unique hlct hp hp0
          subst hvEq; exact ⟨hgrad0, hlen0, hft0, hff0⟩
        · intro val hpa
          have hgl := hglW e he; dsimp only at hgl; rw [ite_eq_right hin] at hgl
          rw [hagT (t13 _ heiCap) (by decide) (by decide)] at hpa
          exact hgl val (hpa.congr fun x hlo hhi => by
            have hx : x = mem (tok.edgeRecords + model.extToInt e) +
                (x - mem (tok.edgeRecords + model.extToInt e)) := by omega
            rw [hx]; exact (hagT ((t1718 e he).2 hin _ (by omega)) (by decide) (by decide)).symm)⟩
  · refine ⟨fun a h => by
        dsimp only at h
        by_cases hr : heap₀ ≤ a ∧ a < curHeap₁
        · exact Or.inr hr
        · rw [ite_eq_right hr] at h; exact Or.inl (hOwn a h),
      fun j hj => htagKeep (t1 j hj) (by decide), fun j hj => htagKeep (t2 j hj) (by decide),
      fun j hj => htagKeep (t3 j hj) (by decide), fun j hj => htagKeep (t4 j hj) (by decide),
      fun j hj => htagKeep (t5 j hj) (by decide), htagKeep t6 (by decide),
      fun j hj => htagKeep (t7 j hj) (by decide), fun j hj => htagKeep (t8 j hj) (by decide),
      fun j hj => htagKeep (t9 j hj) (by decide),
      fun j hj => htagKeep (t10 j (hcn ▸ hj)) (by decide),
      fun j hj => htagKeep (t11 j (hcn ▸ hj)) (by decide),
      fun j hj => htagKeep (t12 j hj) (by decide), fun j hj => htagKeep (t13 j hj) (by decide),
      fun j hj => htagKeep (t14 j hj) (by decide), fun j hj => htagKeep (t15 j hj) (by decide),
      fun a ha => by
        rcases hfoot a ha with h0 | hr
        · exact htagKeep (t16 a h0) (by decide)
        · exact ite_eq_left hr,
      fun e he => ⟨fun j hj => by
          rw [hagT (t12 _ (hedgeAcc.1 e he).1) (by decide) (by decide)]
          exact htagKeep ((t1718 e he).1 j hj) (by decide),
        fun hnot j hj => by
          rw [hagT (t13 _ (hedgeAcc.1 e he).1) (by decide) (by decide)]
          exact htagKeep ((t1718 e he).2 hnot j hj) (by decide)⟩,
      fun a ha => htagKeep (t19 a ha) (by decide),
      fun a h1 h2 => htagKeep (t20 a h1 h2) (by decide),
      fun i hi a ha => htagKeep (t21 i hi a ha) (by omega)⟩

/-- Final `solverStateRep` after `detectOffTreeDrainBody` and storing the count at `mem base`. -/
theorem solverStateRep_after_offDrain {cfg : Alg2Config}
    {L P m V psi k epsExp drainUnit : ℕ} {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)}
    (hlocalCore : Rcore.Local)
    {root base heap₀ curHeap₁ curHeap₂ totalLen : ℕ} {model modelMid : Alg2State cfg}
    {tokMid : SolverToken cfg L Rcore} {mem₁ mem₂ : ℕ → ℕ} {offRep : List ℕ}
    (hModelMid : modelMid =
      { model with detectAccum := (fun e =>
          if model.extToInt e ∈ model.chain.toTreeChain.chainTree.E then
            (algorithm2_detect cfg model).2.detectAccum e
          else model.detectAccum e) })
    (hrepMid : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root modelMid tokMid mem₁)
    (hbelowMid : ∀ a, tokMid.tag a ≠ 0 → tokMid.tag a ≠ 16 → a < base)
    (hfoot16 : ∀ a, tokMid.tag a = 16 → a < base ∨ (heap₀ ≤ a ∧ a < curHeap₁))
    (hbaseHeap : base + 1 + m ≤ heap₀) (hlo1 : heap₀ ≤ curHeap₁)
    (heps : 0 < cfg.ε) (hlen : ∀ e ∈ model.extG.E, 0 < model.extℓ e)
    (hroot11 : mem₂ (root + 11) = 0)
    (hclrIO : ∀ e < tokMid.intCap, mem₂ (tokMid.inOffReady + e) = 0)
    (hoffIff : ∀ e, e ∈ offRep ↔ e ∈ model.extG.E ∧
      model.extToInt e ∉ model.chain.toTreeChain.chainTree.E ∧ e ∈ (algorithm2_detect cfg model).1)
    (hoffRec : ∀ e ∈ model.extG.E,
      let ei := model.extToInt e
      ei ∉ model.chain.toTreeChain.chainTree.E →
      if e ∈ offRep then
        curHeap₁ ≤ mem₂ (tokMid.edgeRecords + ei) ∧
        mem₂ (tokMid.edgeRecords + ei) + (2 + 4 * L) ≤ curHeap₂ ∧
        ∃ val : PathEdgeValue,
          PathEdgeAt mem₂ (mem₂ (tokMid.edgeRecords + ei)) 4 L (some val) ∧
          val.forward = true ∧
          (val.originalFlow : ℝ) / (2 : ℝ) ^ P = model.flow e ∧
          val.detector = -detectorThreshold P cfg.ε (model.extℓ e) ∧
          (val.originalGradient : ℝ) / (2 : ℝ) ^ P = model.extg e ∧
          (val.length : ℝ) / (2 : ℝ) ^ P = model.extℓ e
      else
        mem₂ (tokMid.edgeRecords + ei) = mem₁ (tokMid.edgeRecords + ei) ∧
        ∀ x < 2 + 4 * L, mem₂ (mem₁ (tokMid.edgeRecords + ei) + x) =
          mem₁ (mem₁ (tokMid.edgeRecords + ei) + x))
    (hframe : ∀ a < curHeap₁, a ≠ root + 11 →
      (a < base + 1 ∨ base + 1 + m ≤ a) →
      (a < tokMid.inOffReady ∨ tokMid.inOffReady + tokMid.intCap ≤ a) →
      (a < tokMid.edgeRecords ∨ tokMid.edgeRecords + tokMid.intCap ≤ a) →
      mem₂ a = mem₁ a) :
    let memOut := Function.update mem₂ base totalLen
    let tokFinal : SolverToken cfg L Rcore :=
      { tokMid with
        offReadyCount := 0
        owned := fun a => tokMid.owned a ∨ (curHeap₁ ≤ a ∧ a < curHeap₂)
        tag := fun a => if curHeap₁ ≤ a ∧ a < curHeap₂ then 18 else tokMid.tag a }
    (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root
      (algorithm2_detect cfg model).2 tokFinal memOut ∧
    (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).phi tokFinal.treeHeap tokFinal.treeTok memOut =
      (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).phi tokMid.treeHeap tokMid.treeTok mem₁ ∧
    (∀ i < cfg.P.d, Rcore.phi (tokFinal.coreHandle i) (tokFinal.coreTok i) memOut =
      Rcore.phi (tokMid.coreHandle i) (tokMid.coreTok i) mem₁) := by
  dsimp only
  subst hModelMid
  obtain ⟨hrootDir, hdetect, hnum, hchainP, hfreshInv, hfreshTab, hextM, hintCapE,
    hsched, _, htn, hlct, htrep, hedgeAcc, hcores, htermH, htermBr, htermRep, hwire, htags⟩ := hrepMid
  obtain ⟨hOwn, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15,
    t16, t1718, t19, t20, t21⟩ := htags
  have hltCur {a v : ℕ} (ht : tokMid.tag a = v) (hv : v ≠ 0) : a < curHeap₁ := by
    by_cases h16 : v = 16
    · rcases hfoot16 a (ht.trans h16) with h1 | ⟨_, h2⟩ <;> omega
    · have := hbelowMid a (ht ▸ hv) (ht ▸ h16); omega
  have hneBase {a v : ℕ} (ht : tokMid.tag a = v) (hv : v ≠ 0) : a ≠ base := by
    by_cases h16 : v = 16
    · rcases hfoot16 a (ht.trans h16) with h1 | ⟨h1, _⟩ <;> omega
    · have := hbelowMid a (ht ▸ hv) (ht ▸ h16); omega
  have hnotBuf {a v : ℕ} (ht : tokMid.tag a = v) (hv : v ≠ 0) : a < base + 1 ∨ base + 1 + m ≤ a := by
    by_cases h16 : v = 16
    · rcases hfoot16 a (ht.trans h16) with h1 | ⟨h1, _⟩
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    · exact Or.inl (by have := hbelowMid a (ht ▸ hv) (ht ▸ h16); omega)
  have hnotIO {a v : ℕ} (ht : tokMid.tag a = v) (hv15 : v ≠ 15) :
      a < tokMid.inOffReady ∨ tokMid.inOffReady + tokMid.intCap ≤ a := by
    by_contra h; push Not at h
    have h15 := t15 (a - tokMid.inOffReady) (by omega)
    rw [Nat.add_sub_of_le h.1] at h15; exact hv15 (ht.symm.trans h15)
  have hnotER {a v : ℕ} (ht : tokMid.tag a = v) (hv13 : v ≠ 13) :
      a < tokMid.edgeRecords ∨ tokMid.edgeRecords + tokMid.intCap ≤ a := by
    by_contra h; push Not at h
    have h13 := t13 (a - tokMid.edgeRecords) (by omega)
    rw [Nat.add_sub_of_le h.1] at h13; exact hv13 (ht.symm.trans h13)
  have hagT {a v : ℕ} (ht : tokMid.tag a = v) (hv : v ≠ 0) (hv13 : v ≠ 13) (hv15 : v ≠ 15)
      (hne11 : a ≠ root + 11) : Function.update mem₂ base totalLen a = mem₁ a := by
    rw [Function.update_of_ne (hneBase ht hv)]
    exact hframe a (hltCur ht hv) hne11 (hnotBuf ht hv) (hnotIO ht hv15) (hnotER ht hv13)
  have hagT1 {a v : ℕ} (ht : tokMid.tag a = v) (hv : v ≠ 0) (hv1 : v ≠ 1) (hv13 : v ≠ 13) (hv15 : v ≠ 15) :
      Function.update mem₂ base totalLen a = mem₁ a :=
    hagT ht hv hv13 hv15 (fun h => hv1 (ht.symm.trans (h ▸ t1 11 (by omega))))
  have htagKeep {a v : ℕ} (ht : tokMid.tag a = v) (hv : v ≠ 0) :
      (if curHeap₁ ≤ a ∧ a < curHeap₂ then 18 else tokMid.tag a) = v := by
    have := hltCur ht hv; rw [ite_eq_right (by omega)]; exact ht
  have htreeLocal := LinkCut.PathProg.pathRep_local 4 L LinkCut.PathProg.pathC
  have htree_ag (a : ℕ) (ha : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot
      tokMid.treeHeap tokMid.treeTok a) : mem₁ a = Function.update mem₂ base totalLen a :=
    (hagT1 (t16 a ha) (by decide) (by decide) (by decide) (by decide)).symm
  have hcore_ag (i : ℕ) (hi : i < cfg.P.d) (a : ℕ)
      (ha : Rcore.foot (tokMid.coreHandle i) (tokMid.coreTok i) a) :
      mem₁ a = Function.update mem₂ base totalLen a :=
    (hagT1 (t21 i hi a ha) (by omega) (by omega) (by omega) (by omega)).symm
  have htermLocal := LastLevelProgram.lastLevelRepresentation_local tokMid.vcLast tokMid.ecLast
    4 L P (model.chain.G cfg.P.d).E
  have hterm_ag (a : ℕ)
      (ha : (LastLevelProgram.lastLevelRepresentation tokMid.vcLast tokMid.ecLast 4 L P
        (model.chain.G cfg.P.d).E).foot tokMid.termHandle tokMid.termTok a) :
      mem₁ a = Function.update mem₂ base totalLen a :=
    (hagT1 (t19 a ((lastLevelRepresentation_foot_indep_P _ _ _ _ P 0 _ _ _ _).mp ha))
      (by decide) (by decide) (by decide) (by decide)).symm
  refine ⟨⟨?_,
    listAt_congr'' hdetect (fun j hj => hagT1 (t2 j (by simp [List.length] at hj; omega)) (by decide) (by decide) (by decide) (by decide)),
    listAt_congr'' hnum (fun j hj => by
      have h1 : tokMid.handle + 5 + j = tokMid.handle + (5 + j) := by omega
      rw [h1]; exact hagT1 (t2 (5 + j) (by simp [List.length] at hj; omega)) (by decide) (by decide) (by decide) (by decide)),
    listAt_congr'' hchainP (fun j hj => by
      have h1 : tokMid.handle + 9 + j = tokMid.handle + (9 + j) := by omega
      rw [h1]; exact hagT1 (t2 (9 + j) (by simp [List.length] at hj; omega)) (by decide) (by decide) (by decide) (by decide)),
    hfreshInv,
    ⟨(hagT1 t6 (by decide) (by decide) (by decide) (by decide)).trans hfreshTab.1,
      fun e he => (hagT1 (t7 e he) (by decide) (by decide) (by decide) (by decide)).trans (hfreshTab.2.1 e he),
      fun e he => (hagT1 (t8 e he) (by decide) (by decide) (by decide) (by decide)).trans (hfreshTab.2.2 e he)⟩,
    hextM, hintCapE,
    ⟨fun i => (hagT1 (t5 i.val (by omega)) (by decide) (by decide) (by decide) (by decide)).trans (hsched.1 i),
      fun i hi => by
        have h1 : tokMid.levelsEnd + (cfg.P.d + 1) + i = tokMid.levelsEnd + (cfg.P.d + 1 + i) := by omega
        rw [h1]; exact (hagT1 (t5 _ (by omega)) (by decide) (by decide) (by decide) (by decide)).trans (by rw [← h1]; exact hsched.2.1 i hi),
      fun i hi => by
        have h1 : tokMid.levelsEnd + 2 * (cfg.P.d + 1) + i = tokMid.levelsEnd + (2 * (cfg.P.d + 1) + i) := by omega
        rw [h1]; exact (hagT1 (t5 _ (by omega)) (by decide) (by decide) (by decide) (by decide)).trans (by rw [← h1]; exact hsched.2.2.1 i hi),
      fun i hi => by
        have h1 : tokMid.levelsEnd + 3 * (cfg.P.d + 1) + i = tokMid.levelsEnd + (3 * (cfg.P.d + 1) + i) := by omega
        rw [h1]; exact (hagT1 (t5 _ (by omega)) (by decide) (by decide) (by decide) (by decide)).trans (by rw [← h1]; exact hsched.2.2.2.1 i hi),
      (hagT1 (t5 (4 * (cfg.P.d + 1)) (by omega)) (by decide) (by decide) (by decide) (by decide)).trans hsched.2.2.2.2⟩,
    ⟨Nat.zero_le _, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
      fun e he => Or.inl (by rw [Function.update_of_ne (hneBase (t15 e he) (by decide))]; exact hclrIO e he),
      fun e he h1 => by
        rw [Function.update_of_ne (hneBase (t15 e he) (by decide)), hclrIO e he] at h1; omega⟩,
    htn, hlct, (htreeLocal tokMid.treeHeap tokMid.tree tokMid.treeTok mem₁ _ htree_ag).1 htrep,
    ?_, ?_,
    (hagT1 (t4 cfg.P.d (by omega)) (by decide) (by decide) (by decide) (by decide)).trans htermH,
    by
      have h1 : tokMid.handle + 18 + (cfg.P.d + 1) + cfg.P.d = tokMid.handle + 18 + (2 * cfg.P.d + 1) := by omega
      rw [h1] at htermBr ⊢; exact (hagT1 (t4 _ (by omega)) (by decide) (by decide) (by decide) (by decide)).trans htermBr,
    (htermLocal tokMid.termHandle _ tokMid.termTok mem₁ _ hterm_ag).1 htermRep, ?_, ?_⟩,
    (htreeLocal tokMid.treeHeap tokMid.tree tokMid.treeTok mem₁ _ htree_ag).2.symm,
    fun i hi => (hlocalCore (tokMid.coreHandle i) (chainLevelOrdAbs model.chain i) (tokMid.coreTok i)
      mem₁ _ (hcore_ag i hi)).2.symm⟩
  · intro j hj
    have hj16 : j < 16 := by simpa [List.length] using hj
    by_cases h11 : j = 11
    · subst h11
      rw [Function.update_of_ne (hneBase (t1 11 (by omega)) (by decide)), hroot11]; rfl
    · rw [hagT (t1 j hj16) (by decide) (by decide) (by decide) (by omega)]
      have h0 := hrootDir j hj
      interval_cases j <;> first | exact False.elim (h11 rfl) | simpa using h0
  · constructor
    · intro e heE; dsimp only [algorithm2_detect]
      have heE0 : e ∈ model.extG.E := by simpa [algorithm2_detect] using heE
      obtain ⟨heiCap, hthr1, hbr1⟩ := hedgeAcc.1 e heE0
      have hetEq : Function.update mem₂ base totalLen (tokMid.edgeThresholds + model.extToInt e) =
          mem₁ (tokMid.edgeThresholds + model.extToInt e) :=
        hagT1 (t12 _ heiCap) (by decide) (by decide) (by decide) (by decide)
      have hslEq : Function.update mem₂ base totalLen (tokMid.slots + model.extToInt e) =
          mem₁ (tokMid.slots + model.extToInt e) :=
        hagT1 (t9 _ heiCap) (by decide) (by decide) (by decide) (by decide)
      have hioZero : Function.update mem₂ base totalLen (tokMid.inOffReady + model.extToInt e) = 0 := by
        rw [Function.update_of_ne (hneBase (t15 _ heiCap) (by decide))]; exact hclrIO _ heiCap
      refine ⟨heiCap, by
        rw [hetEq]
        exact hthr1.congr (fun j hj => hagT1 ((t1718 e heE0).1 j hj) (by decide) (by decide) (by decide) (by decide)), ?_⟩
      by_cases hin : model.extToInt e ∈ model.chain.toTreeChain.chainTree.E
      · rw [ite_eq_left hin] at hbr1
        simp only [hin, ↓reduceIte]
        obtain ⟨hsnz, his, hnm, hst, val, acc, hp, hfl, hac, hd⟩ := hbr1
        have hisLt : mem₁ (tokMid.slots + model.extToInt e) < 2 * tokMid.tree.n := his.2
        rw [hslEq]
        exact ⟨hsnz, his, (hagT1 (t10 _ hisLt) (by decide) (by decide) (by decide) (by decide)).trans hnm,
          (hagT1 (t11 _ hisLt) (by decide) (by decide) (by decide) (by decide)).trans (hst.trans hetEq.symm),
          val, acc, hp, hfl, by simpa [algorithm2_detect, hin] using hac, hd⟩
      · rw [ite_eq_right hin] at hbr1
        simp only [hin, ↓reduceIte]
        obtain ⟨hs0, val1, acc1, hrec1, hfl1, hac1, hd1, _⟩ := hbr1
        have hrecO := hoffRec e heE0 hin
        have hneErB : tokMid.edgeRecords + model.extToInt e ≠ base := hneBase (t13 _ heiCap) (by decide)
        by_cases heIn : e ∈ offRep
        · rw [ite_eq_left heIn] at hrecO
          obtain ⟨hloR, hhiR, val2, hpa2, _, hfl2, hd2, _, _⟩ := hrecO
          have hdetE : e ∈ (algorithm2_detect cfg model).1 := ((hoffIff e).mp heIn).2.2
          have hacc0 : (algorithm2_detect cfg model).2.detectAccum e = 0 := by
            unfold algorithm2_detect at hdetE ⊢
            simp only [Finset.mem_filter] at hdetE
            simp [hdetE.1, hdetE.2]
          have hthrPos : 0 < detectorThreshold P cfg.ε (model.extℓ e) := by
            unfold detectorThreshold
            have hℓ := hlen e heE0
            exact Int.ceil_pos.mpr (by positivity)
          refine ⟨hslEq.trans hs0, val2, 0, ?_, hfl2,
            by simpa [algorithm2_detect] using hacc0.symm, by simp [hd2], fun hn => by omega⟩
          rw [Function.update_of_ne hneErB]
          exact hpa2.congr (fun a ha1 ha2 => by rw [Function.update_of_ne (by omega)])
        · rw [ite_eq_right heIn] at hrecO
          obtain ⟨hptrEq, hcellEq⟩ := hrecO
          have hnotDet : e ∉ (algorithm2_detect cfg model).1 := fun h =>
            heIn ((hoffIff e).mpr ⟨heE0, hin, h⟩)
          have haccKeep : (algorithm2_detect cfg model).2.detectAccum e = model.detectAccum e := by
            unfold algorithm2_detect at hnotDet ⊢
            simp only [Finset.mem_filter, not_and] at hnotDet
            simp [heE0, hnotDet heE0]
          have hneg : val1.detector < 0 := by
            by_contra hnn; push Not at hnn
            have := (detect_residual_pending model (reported := ∅) heE0 heps (hlen e heE0)
              (by simpa [resetReported, hin] using hac1) hd1).mp hnn
            exact hnotDet (by simpa using this)
          have haccKeep' : (if e ∈ {e ∈ model.extG.E | cfg.ε ≤ model.extℓ e * model.detectAccum e} then
              (0 : ℝ) else model.detectAccum e) = model.detectAccum e := haccKeep
          refine ⟨hslEq.trans hs0, val1, acc1, ?_, hfl1,
            by rw [haccKeep']; simpa [hin] using hac1, hd1, fun hn => by omega⟩
          rw [Function.update_of_ne hneErB, hptrEq]
          let ptr := mem₁ (tokMid.edgeRecords + model.extToInt e)
          have hrec1' : PathEdgeAt mem₁ ptr 4 L (some val1) := hrec1
          change PathEdgeAt (Function.update mem₂ base totalLen) ptr 4 L (some val1)
          exact hrec1'.congr (fun a ha1 ha2 => by
            have haIdx : a = ptr + (a - ptr) := by omega
            have hidxLt : a - ptr < 2 + 4 * L := by omega
            have ht18 : tokMid.tag a = 18 := by
              have ht := (t1718 e heE0).2 hin (a - ptr) hidxLt
              rwa [← haIdx] at ht
            have hneA : a ≠ base := hneBase ht18 (by decide)
            rw [Function.update_of_ne hneA, haIdx]; exact hcellEq (a - ptr) hidxLt)
    · intro slot val his hp
      have hisLt : slot < 2 * tokMid.tree.n := his.2
      have hnmEq : Function.update mem₂ base totalLen (tokMid.names + slot) = mem₁ (tokMid.names + slot) :=
        hagT1 (t10 slot hisLt) (by decide) (by decide) (by decide) (by decide)
      obtain ⟨h1, h2, h3, h4, h5⟩ := hedgeAcc.2 slot val his hp
      dsimp only
      rw [hnmEq]
      exact ⟨h1, h2, (hagT1 (t9 _ h1) (by decide) (by decide) (by decide) (by decide)).trans h3, h4, h5⟩
  · intro i hi
    obtain ⟨hh, hbr, hcr⟩ := hcores i hi
    refine ⟨(hagT1 (t4 i (by omega)) (by decide) (by decide) (by decide) (by decide)).trans hh,
      by
        have h1 : tokMid.handle + 18 + (cfg.P.d + 1) + i = tokMid.handle + 18 + (cfg.P.d + 1 + i) := by omega
        rw [h1] at hbr ⊢; exact (hagT1 (t4 _ (by omega)) (by decide) (by decide) (by decide) (by decide)).trans hbr,
      (hlocalCore (tokMid.coreHandle i) _ (tokMid.coreTok i) mem₁ _ (hcore_ag i hi)).1 hcr⟩
  · obtain ⟨htabW, hrgW, hsubCap, hnsW, hglW⟩ := hwire
    refine ⟨fun j hj => (hagT1 (t3 j hj) (by decide) (by decide) (by decide) (by decide)).trans (htabW j hj),
      hrgW.of_agree (fun a h1 h2 => hagT1 (t20 a h1 h2) (by decide) (by decide) (by decide) (by decide)),
      hsubCap,
      ⟨fun ei hei => by
          rw [hagT1 (t9 ei (hsubCap.2 ei hei).1) (by decide) (by decide) (by decide) (by decide)]
          have hfwd := hnsW.forward ei hei
          have hslotLt : mem₁ (tokMid.slots + ei) < 2 * tokMid.tree.n := by unfold isEdgeSlot at hfwd; omega
          exact ⟨hfwd.1, hfwd.2.1,
            (hagT1 (t10 _ hslotLt) (by decide) (by decide) (by decide) (by decide)).trans hfwd.2.2⟩,
        fun k hk hks => by
          have hkLt : k < 2 * tokMid.tree.n := hks.2
          rw [hagT1 (t10 k hkLt) (by decide) (by decide) (by decide) (by decide)]
          obtain ⟨hmem, hslot⟩ := hnsW.inverse k hk hks
          exact ⟨hmem, (hagT1 (t9 _ (hsubCap.2 _ hmem).1) (by decide) (by decide) (by decide) (by decide)).trans hslot⟩,
        fun ei hei => by
          rw [hagT1 (t9 ei (hsubCap.2 ei hei).1) (by decide) (by decide) (by decide) (by decide)]
          exact hnsW.endpoints ei hei⟩,
      fun e he => by
        have he0 : e ∈ model.extG.E := by simpa [algorithm2_detect] using he
        have heiCap := (hedgeAcc.1 e he0).1
        change if model.extToInt e ∈ model.chain.toTreeChain.chainTree.E then
          ∀ val, (Function.update mem₂ base totalLen (tokMid.slots + model.extToInt e), some val) ∈
              forestPairs pathPayload tokMid.tree.splay tokMid.trees →
            (val.originalGradient : ℝ) / (2 : ℝ) ^ P = model.extg e ∧
            (val.length : ℝ) / (2 : ℝ) ^ P = model.extℓ e ∧
            (val.forward = true →
              inducedSubPar pathPayload tokMid.tree.splay tokMid.trees (vid (model.chain.toTreeChain.chainTree.head (model.extToInt e))) =
                Function.update mem₂ base totalLen (tokMid.slots + model.extToInt e) ∧
              inducedSubPar pathPayload tokMid.tree.splay tokMid.trees
                (Function.update mem₂ base totalLen (tokMid.slots + model.extToInt e)) =
                vid (model.chain.toTreeChain.chainTree.tail (model.extToInt e))) ∧
            (val.forward = false →
              inducedSubPar pathPayload tokMid.tree.splay tokMid.trees (vid (model.chain.toTreeChain.chainTree.tail (model.extToInt e))) =
                Function.update mem₂ base totalLen (tokMid.slots + model.extToInt e) ∧
              inducedSubPar pathPayload tokMid.tree.splay tokMid.trees
                (Function.update mem₂ base totalLen (tokMid.slots + model.extToInt e)) =
                vid (model.chain.toTreeChain.chainTree.head (model.extToInt e)))
        else
          ∀ val, PathEdgeAt (Function.update mem₂ base totalLen)
              (Function.update mem₂ base totalLen (tokMid.edgeRecords + model.extToInt e)) 4 L (some val) →
            val.forward = true ∧
            (val.originalGradient : ℝ) / (2 : ℝ) ^ P = model.extg e ∧
            (val.length : ℝ) / (2 : ℝ) ^ P = model.extℓ e
        by_cases hin : model.extToInt e ∈ model.chain.toTreeChain.chainTree.E
        · rw [ite_eq_left hin]
          intro val hp
          rw [hagT1 (t9 _ heiCap) (by decide) (by decide) (by decide) (by decide)] at hp ⊢
          have hgl := hglW e he0; dsimp only at hgl; rw [ite_eq_left hin] at hgl
          exact hgl val hp
        · rw [ite_eq_right hin]
          intro val hpa
          have hneErB : tokMid.edgeRecords + model.extToInt e ≠ base := hneBase (t13 _ heiCap) (by decide)
          rw [Function.update_of_ne hneErB] at hpa
          have hrecO := hoffRec e he0 hin
          by_cases heIn : e ∈ offRep
          · rw [ite_eq_left heIn] at hrecO
            obtain ⟨hloR, hhiR, val2, hpa2, hfwd2, _, _, hgrad2, hlen2⟩ := hrecO
            have hpa2' : PathEdgeAt (Function.update mem₂ base totalLen)
                (mem₂ (tokMid.edgeRecords + model.extToInt e)) 4 L (some val2) :=
              hpa2.congr fun a ha1 ha2 => by rw [Function.update_of_ne (by omega)]
            obtain ⟨hfe, hge, hle⟩ := pathEdgeAt_fwd_grad_len_eq hpa hpa2'
            rw [hfe, hge, hle]; exact ⟨hfwd2, hgrad2, hlen2⟩
          · rw [ite_eq_right heIn] at hrecO
            obtain ⟨hptrEq, hcellEq⟩ := hrecO
            rw [hptrEq] at hpa
            have hgl := hglW e he0; dsimp only at hgl; rw [ite_eq_right hin] at hgl
            let ptr := mem₁ (tokMid.edgeRecords + model.extToInt e)
            exact hgl val (hpa.congr fun a ha1 ha2 => by
              have haIdx : a = ptr + (a - ptr) := by omega
              have hidxLt : a - ptr < 2 + 4 * L := by omega
              have ht18 : tokMid.tag a = 18 := by
                have ht := (t1718 e he0).2 hin (a - ptr) hidxLt; rwa [← haIdx] at ht
              rw [Function.update_of_ne (hneBase ht18 (by decide)), haIdx]
              exact (hcellEq (a - ptr) hidxLt).symm)⟩
  · refine ⟨fun a h => by
        dsimp only at h
        by_cases hr : curHeap₁ ≤ a ∧ a < curHeap₂
        · exact Or.inr hr
        · rw [ite_eq_right hr] at h; exact Or.inl (hOwn a h),
      fun j hj => htagKeep (t1 j hj) (by decide), fun j hj => htagKeep (t2 j hj) (by decide),
      fun j hj => htagKeep (t3 j hj) (by decide), fun j hj => htagKeep (t4 j hj) (by decide),
      fun j hj => htagKeep (t5 j hj) (by decide), htagKeep t6 (by decide),
      fun j hj => htagKeep (t7 j hj) (by decide), fun j hj => htagKeep (t8 j hj) (by decide),
      fun j hj => htagKeep (t9 j hj) (by decide), fun j hj => htagKeep (t10 j hj) (by decide),
      fun j hj => htagKeep (t11 j hj) (by decide), fun j hj => htagKeep (t12 j hj) (by decide),
      fun j hj => htagKeep (t13 j hj) (by decide), fun j hj => htagKeep (t14 j hj) (by decide),
      fun j hj => htagKeep (t15 j hj) (by decide), fun a ha => htagKeep (t16 a ha) (by decide),
      fun e he => by
        dsimp only [algorithm2_detect]
        have he0 : e ∈ model.extG.E := by simpa [algorithm2_detect] using he
        have heiCap := (hedgeAcc.1 e he0).1
        refine ⟨fun j hj => ?_, fun hnot j hj => ?_⟩
        · rw [hagT1 (t12 _ heiCap) (by decide) (by decide) (by decide) (by decide)]
          exact htagKeep ((t1718 e he0).1 j hj) (by decide)
        · rw [Function.update_of_ne (hneBase (t13 _ heiCap) (by decide))]
          have hrecO := hoffRec e he0 hnot
          by_cases heIn : e ∈ offRep
          · rw [ite_eq_left heIn] at hrecO
            have hhi : mem₂ (tokMid.edgeRecords + model.extToInt e) + j < curHeap₂ := by
              have := hrecO.2.1; omega
            exact ite_eq_left ⟨le_trans hrecO.1 (Nat.le_add_right _ _), hhi⟩
          · rw [ite_eq_right heIn] at hrecO
            rw [hrecO.1]; exact htagKeep ((t1718 e he0).2 hnot j hj) (by decide),
      fun a ha => htagKeep (t19 a ha) (by decide),
      fun a h1 h2 => htagKeep (t20 a h1 h2) (by decide),
      fun i hi a ha => htagKeep (t21 i hi a ha) (by omega)⟩

end MinCostFlow.MinRatio
