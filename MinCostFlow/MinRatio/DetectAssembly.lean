module

public import MinCostFlow.MinRatio.DetectAssemblyBase
public import MinCostFlow.MinRatio.SolverLevelMetaPreserve
public import MinCostFlow.MinRatio.DetectOffTreeDrainRun
import WordRAM.Tactic

/-!
# End-to-end Word-RAM `Detect` assembly (`minRatioMachineContractWithV` op 2)

Proves `solverDetectBody_runs` on top of `DetectAssemblyBase.lean`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine

/-- End-to-end Word-RAM `Detect` assembly: `solverDetectBody` meets `minRatioMachineContractWithV`
operation 2 (`Detect`), preserves `solverStateRep` (with `drainUnit := detectOffTreeDrainUnit F.limbs`)
and `PathTreeNumericInv`, and achieves amortized cost
`O((1 + |(algorithm2_detect cfg model).1|) * (pathTreeBudget + L))`. -/
theorem solverDetectBody_runs {w m V psi k epsExp treeInit isNeg reset : ℕ}
    {F : MinRatioFormat w} {cfg : Alg2Config} {G : MGraph} {κ α : ℝ}
    {rate : ℕ → ℕ} {outerSpace : ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} (hlocalCore : Rcore.Local)
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {opTree : ℕ → ℕ}
    {root base pos : ℕ} {model : Alg2State cfg}
    {tok : SolverToken cfg F.limbs Rcore} {B R : ℤ}
    (hfmt4 : F.fmt.limbBits = 4)
    (hExtRange : ∀ e < m, e ∈ model.extG.E)
    (hTreeImpl : (LinkCut.PathProg.pathRep 4 F.limbs LinkCut.PathProg.pathC).Implements w p
      treeInit opTree
      (pathTreeMachineContract F.fmt F.limbs LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc F.limbs)))
    (hIsNeg : MeetsContract w p isNeg (Num.isNegativeContract w 4))
    (hReset : ∀ edge th, MeetsContract w p reset (detectResetContract w 4 edge th))
    (heps : 0 < cfg.ε) (hlen : ∀ e ∈ model.extG.E, 0 < model.extℓ e)
    (hnum : PathTreeNumericInv tok.tree tok.trees B R)
    (hcapB : 2 * ((2 * tok.tree.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 F.limbs : ℤ))
    (hthrB : ∀ e ∈ model.extG.E, |detectorThreshold F.fmt.precision cfg.ε (model.extℓ e)| ≤ B)
    (hfitThr : ∀ e ∈ model.extG.E,
      Num.Fits 4 F.limbs (-detectorThreshold F.fmt.precision cfg.ε (model.extℓ e)))
    (hrep : (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) Rcore).rep root model tok mem)
    (hpre : (minRatioMachineContractWithV F (Chain.Ordered.algorithm2_dsWithFailureWith cfg κ) G m V κ α
      rate outerSpace).pre 2 model [root, base] mem)
    (hbelow : ∀ a, (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) Rcore).foot root tok a → a < base)
    (hz : ZeroFrom mem base)
    (hw13 : 13 < 2 ^ w) (hLpos : 0 < F.limbs)
    (htreeWord : 2 * tok.tree.n + 1 < 2 ^ w)
    (htreeWidth : Nat.log 2 (2 * tok.tree.n + 1) ≤ 4 * F.limbs)
    (hroom : base + 1 + m + ((algorithm2_detect cfg model).1.card + 1) *
      detectTreeRoundSpace F.limbs + tok.offReadyCount * (2 + 4 * F.limbs) < 2 ^ w) :
    let L := F.limbs
    let S := (algorithm2_detect cfg model).1
    let Rrep := solverStateRep cfg L F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit L) Rcore
    ∃ ret cost out tok',
      Runs w p ω (solverDetectBody (opTree 6) (opTree 4) (opTree 5) isNeg reset)
        (startState [root, base] mem pos) (.returned ret) out cost ∧
      (minRatioMachineContractWithV F (Chain.Ordered.algorithm2_dsWithFailureWith cfg κ) G m V κ α
        rate outerSpace).post 2 model [root, base] mem (algorithm2_detect cfg model).2 out.mem ∧
      Rrep.rep root (algorithm2_detect cfg model).2 tok' out.mem ∧
      PreservesLevelMeta tok tok' mem out.mem ∧
      tok'.intCap = tok.intCap ∧
      PathTreeNumericInv tok'.tree tok'.trees B R ∧
      ZeroFrom out.mem ret ∧ base ≤ ret ∧
      ret ≤ base + 1 + m + (S.card + 1) * detectTreeRoundSpace L +
        tok.offReadyCount * (2 + 4 * L) ∧
      (∀ a < base, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
      (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (base ≤ a ∧ a < ret)) ∧
      cost + Rrep.phi root tok' out.mem ≤
        (S.card + 1) * (detectTreeStepBudget L model.extG.n + 2) + 200 + Rrep.phi root tok mem ∧
      (OffTreeRecSep model L mem tok.edgeRecords →
        OffTreeRecSep (algorithm2_detect cfg model).2 L out.mem tok'.edgeRecords) := by
  dsimp only
  let L := F.limbs
  let P := F.fmt.precision
  let S := (algorithm2_detect cfg model).1
  let Rrep := solverStateRep cfg L P m V psi k epsExp (detectOffTreeDrainUnit L) Rcore
  let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
  have hrep0 := hrep
  obtain ⟨hrootDir, hdetect, _, _, _, _, hextM, _, _, _, htn, _, _, _, _, _, _, _, _, htags⟩ := hrep
  obtain ⟨hOwn, t1, t2, _, _, _, _, _, _, _, _, _, _, t13, _, t15, t16, _⟩ := htags
  have htrCardLe : (treeReadySet model).card ≤ S.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hroomTree : (base + 1 + m) + ((treeReadySet model).card + 1) * detectTreeRoundSpace L < 2 ^ w := by
    have := Nat.mul_le_mul_right (detectTreeRoundSpace L) (Nat.add_le_add_right htrCardLe 1)
    dsimp only [S, L] at *; omega
  have hh5W : tok.handle + 5 < 2 ^ w := by
    have := hbelow (tok.handle + 5) (Or.inl (hOwn _ (by rw [t2 5 (by omega)]; decide))); omega
  have hdet' : DetectHeaderAt mem tok.handle tok.treeHeap tok.names tok.inverse
      tok.slotThresholds m L (mem (tok.handle + 6)) (mem (tok.handle + 7)) := by
    have h6 : mem (tok.handle + 6) = tok.searchSpace := by simpa using hdetect 6 (by simp)
    have h7 : mem (tok.handle + 7) = tok.readSpace := by simpa using hdetect 7 (by simp)
    rw [h6, h7]; exact hdetect
  obtain ⟨mid0, hrPref, hmid0Mem, _, hm0r0, hm0r1, hm0r2, hm0r3, hm0r4, hm0r5,
    hm0r6, hm0r7, hm0r8, hm0r9⟩ :=
    detectPrefixLoad_runs (p := p) (ω := ω) (pos := pos) (base := base) (m := m) (L := L)
      hh5W (by omega) (by simpa using hrootDir 0 (by simp)) hdet'
  -- Phase 1: Tree reporting loop
  obtain ⟨mid1, cTree, treeRep, curHeap₁, curTree, curTrees, curTreeTok,
    hrTree, hcTree, hm1r0, hm1r1, hm1r2, hm1r3, hm1r4, hm1r5, htreeNd, htreeFin,
    htreeList, hcur1Lo, hcur1Hi, hz1, hcn, hlct1, hnum1, htrep1, hfoot1, hframe1,
    htreeAcc1, htreeRev1, hns1⟩ :=
    detectTreePhaseBody_runs (ω := ω) (st := mid0) (heap₀ := base + 1 + m) (B := B) (R := R)
      hfmt4 (hmid0Mem.symm ▸ hrep0) hbelow hTreeImpl hReset heps hlen hnum hcapB hthrB hfitThr
      htreeWord htreeWidth hm0r0 hm0r1 hm0r2 hm0r3 hm0r4 hm0r5 hm0r6 hm0r7 hm0r8 hm0r9
      le_rfl (fun a ha => hmid0Mem.symm ▸ hz a (by omega)) hroomTree (by omega) hLpos
  -- Build intermediate state `(modelMid, tokMid)`
  let modelMid : Alg2State cfg :=
    { model with detectAccum := fun e =>
        if model.extToInt e ∈ model.chain.toTreeChain.chainTree.E then
          (algorithm2_detect cfg model).2.detectAccum e
        else model.detectAccum e }
  let tokMid : SolverToken cfg L Rcore :=
    { tok with
      tree := curTree, trees := curTrees, treeTok := curTreeTok,
      owned := fun a => tok.owned a ∨ (base + 1 + m ≤ a ∧ a < curHeap₁),
      tag := fun a => if base + 1 + m ≤ a ∧ a < curHeap₁ then 16 else tok.tag a }
  obtain ⟨hrepMid, hbelowMid, hcorePhi1⟩ :=
    solverStateRep_after_treePhase hlocalCore hrep0 hbelow le_rfl hcn hlct1 htrep1 hfoot1
      (by simpa [hmid0Mem] using hframe1) (by simpa [hmid0Mem] using htreeAcc1)
      (by simpa [hmid0Mem] using htreeRev1) (by simpa [hmid0Mem] using hns1)
  have htreeSub : ∀ e ∈ treeRep, e ∈ modelMid.extG.E ∧
      modelMid.extToInt e ∈ modelMid.chain.toTreeChain.chainTree.E := fun e he => by
    have h1 : e ∈ treeReadySet model := by rw [← htreeFin, List.mem_toFinset]; exact he
    obtain ⟨h1a, h1b⟩ := Finset.mem_filter.mp h1
    exact ⟨(Finset.mem_filter.mp h1a).1, h1b⟩
  have htreeLenLeM : treeRep.length ≤ m :=
    treeRep_length_le_m hextM htreeNd (htreeFin ▸ Finset.Subset.refl _)
  have hroomOff : curHeap₁ + tokMid.offReadyCount * (2 + 4 * L) < 2 ^ w := by
    have := Nat.mul_le_mul_right (detectTreeRoundSpace L) (Nat.add_le_add_right htrCardLe 1)
    dsimp only [tokMid, S, L] at *; omega
  -- Phase 2: Off-tree pending-list drain
  obtain ⟨mid2, cOff, offRep, curHeap₂, hrOff, hcOff, hm2r0, hm2r1, hm2r3, hm2r4,
    hcur2Lo, hcur2Hi, hz2, hallNd, hallList, hroot11, hclrIO, hoffIffMid, hoffRecMid, hframe2,
    hsepOff⟩ :=
    detectOffTreeDrainBody_runs (ω := ω) (st := mid1) (model := modelMid) (tok := tokMid)
      (root := root) (base := base) (heap₀ := curHeap₁) (treeRep := treeRep)
      hrepMid hbelowMid hExtRange heps hlen hfitThr hIsNeg hReset
      hm1r0 hm1r1 hm1r2 hm1r3 hm1r4 hm1r5 (le_trans le_rfl hcur1Lo) htreeLenLeM htreeNd
      htreeList htreeSub hz1 hroomOff hw13 hLpos
  -- Translate `hoffIffMid` from `modelMid` back to `model`
  have hoffIff : ∀ e, e ∈ offRep ↔ e ∈ model.extG.E ∧
      model.extToInt e ∉ model.chain.toTreeChain.chainTree.E ∧ e ∈ S := fun e => by
    rw [hoffIffMid e]
    refine and_congr_right fun heE => and_congr_right fun hnotT => ?_
    simp only [S, algorithm2_detect, modelMid, Finset.mem_filter, ite_eq_right hnotT]
  -- Phase 3: Store total count at `mem base` and return `curHeap₂`
  let totalLen := (treeRep ++ offRep).length
  have htotLeM : totalLen ≤ m := by
    have hc : (treeRep ++ offRep).toFinset.card ≤ (Finset.range m).card :=
      Finset.card_le_card (fun e he => by
        rcases List.mem_append.mp (List.mem_toFinset.mp he) with ht | ho
        · exact Finset.mem_range.mpr (hextM e (htreeSub e ht).1)
        · exact Finset.mem_range.mpr (hextM e ((hoffIff e).mp ho).1))
    rw [List.toFinset_card_of_nodup hallNd, Finset.card_range] at hc; exact hc
  let out : State := { mid2 with mem := Function.update mid2.mem base totalLen }
  have hwnz : ¬ w = 0 := fun h => by subst h; simp at hw13
  have rStoreCnt : Runs w p ω (.store (.reg 1) (.bin .sub (.reg 3) (.bin .add (.reg 1) (.const 1))))
      mid2 .normal out 7 :=
    runs_store_iff.mpr ⟨base, totalLen, by simp [Expr.eval, hm2r1], by
      have hm2r3' : mid2.regs 3 = base + 1 + totalLen := hm2r3
      have htotLenW : totalLen < 2 ^ w := by omega
      simp only [Expr.eval, BinOp.eval, hm2r1, hm2r3', show 1 < 2 ^ w by omega,
        show base + 1 < 2 ^ w by omega, Nat.add_sub_cancel_left, htotLenW, ↓reduceIte],
      rfl, rfl, rfl⟩
  have rRet : Runs w p ω (.ret (.reg 4)) out (.returned curHeap₂) out 2 :=
    runs_ret_iff.mpr ⟨curHeap₂, by simp [Expr.eval, out, hm2r4], rfl, rfl, rfl⟩
  have hrFull : Runs w p ω (solverDetectBody (opTree 6) (opTree 4) (opTree 5) isNeg reset)
      (startState [root, base] mem pos) (.returned curHeap₂) out
      (47 + (cTree + (cOff + (7 + 2 + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨mid0, 47, _, hrPref,
      runs_seq_iff.mpr (Or.inr ⟨mid1, cTree, _, hrTree,
      runs_seq_iff.mpr (Or.inr ⟨mid2, cOff, _, hrOff,
      runs_seq_iff.mpr (Or.inr ⟨out, 7, 2, rStoreCnt, rRet, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  -- Final `solverStateRep` and potentials
  let tokFinal : SolverToken cfg L Rcore :=
    { tokMid with
      offReadyCount := 0,
      owned := fun a => tokMid.owned a ∨ (curHeap₁ ≤ a ∧ a < curHeap₂),
      tag := fun a => if curHeap₁ ≤ a ∧ a < curHeap₂ then 18 else tokMid.tag a }
  have hfoot16 : ∀ a, tokMid.tag a = 16 → a < base ∨ (base + 1 + m ≤ a ∧ a < curHeap₁) := fun a ha => by
    dsimp only [tokMid] at ha
    by_cases hr : base + 1 + m ≤ a ∧ a < curHeap₁
    · exact Or.inr hr
    · rw [ite_eq_right hr] at ha
      exact Or.inl (hbelow a (Or.inl (hOwn a (by rw [ha]; decide))))
  obtain ⟨hrepFinal, htreePhi2, hcorePhi2⟩ :=
    solverStateRep_after_offDrain hlocalCore (modelMid := modelMid) rfl hrepMid hbelowMid hfoot16
      le_rfl hcur1Lo heps hlen hroot11 hclrIO hoffIff hoffRecMid hframe2
  -- Prove `DetectAt out.mem base S`
  have hDetectAt : DetectAt out.mem base S := by
    refine ⟨treeRep ++ offRep, hallNd, ?_, ?_, ?_⟩
    · ext e
      rw [List.mem_toFinset, List.mem_append, ← List.mem_toFinset, htreeFin,
        mem_treeReadySet_iff, hoffIff e]
      constructor
      · rintro (⟨h1, _⟩ | ⟨_, _, h1⟩) <;> exact h1
      · intro h1
        by_cases hT : model.extToInt e ∈ model.chain.toTreeChain.chainTree.E
        · exact Or.inl ⟨h1, hT⟩
        · exact Or.inr ⟨mem_extG_of_mem_detect h1, hT, h1⟩
    · simp [out, totalLen]
    · intro j hj
      dsimp only [out]
      rw [Function.update_of_ne (by omega)]
      exact hallList j hj
  have hStateFits' : MinRatioStateFits (Chain.Ordered.algorithm2_dsWithFailureWith cfg κ) G
      F.fmt.limbBits F.limbs F.fmt.precision (algorithm2_detect cfg model).2 := hpre.1
  -- Frame below `base` and footprint growth
  have hframeFinal : ∀ a < base, ¬ Rrep.foot root tok a → out.mem a = mem a := fun a ha hnf => by
    have hnotTag (v : ℕ) (hv : v ≠ 0) : tok.tag a ≠ v := fun ht =>
      hnf (Or.inl (hOwn a (ht ▸ hv)))
    have hnfTree : ¬ Rtree.foot tok.treeHeap tok.treeTok a := fun h => hnf (Or.inr (Or.inl h))
    have hneBase : a ≠ base := by omega
    have hne11 : a ≠ root + 11 := fun h => hnotTag 1 (by decide) (h ▸ t1 11 (by omega))
    have hnotIO : a < tokMid.inOffReady ∨ tokMid.inOffReady + tokMid.intCap ≤ a := by
      by_contra h; push Not at h; dsimp only [tokMid] at h
      have h15 := t15 (a - tok.inOffReady) (by omega)
      rw [Nat.add_sub_of_le h.1] at h15; exact hnotTag 15 (by decide) h15
    have hnotER : a < tokMid.edgeRecords ∨ tokMid.edgeRecords + tokMid.intCap ≤ a := by
      by_contra h; push Not at h; dsimp only [tokMid] at h
      have h13 := t13 (a - tok.edgeRecords) (by omega)
      rw [Nat.add_sub_of_le h.1] at h13; exact hnotTag 13 (by decide) h13
    dsimp only [out]
    rw [Function.update_of_ne hneBase,
      hframe2 a (by omega) hne11 (Or.inl (by omega)) hnotIO hnotER,
      hframe1 a (by omega) hnfTree (Or.inl (by omega)), hmid0Mem]
  have hfootFinal : ∀ a, Rrep.foot root tokFinal a → Rrep.foot root tok a ∨ (base ≤ a ∧ a < curHeap₂) := by
    intro a ha
    rcases ha with (hown | htree | ⟨i, hi, hcore⟩)
    · rcases hown with (hown0 | ⟨h1, h2⟩) | ⟨h1, h2⟩
      · exact Or.inl (Or.inl hown0)
      · exact Or.inr ⟨by omega, lt_of_lt_of_le h2 hcur2Lo⟩
      · exact Or.inr ⟨by omega, h2⟩
    · rcases hfoot1 a htree with h0 | ⟨h1, h2⟩
      · exact Or.inl (Or.inr (Or.inl h0))
      · exact Or.inr ⟨by omega, lt_of_lt_of_le h2 hcur2Lo⟩
    · exact Or.inl (Or.inr (Or.inr ⟨i, hi, hcore⟩))
  -- Amortized cost telescoping (off-tree drain cancels against `tok.offReadyCount * drainUnit`)
  have hcoresSum : (∑ i : Fin cfg.P.d, Rcore.phi (tokFinal.coreHandle i.val) (tokFinal.coreTok i.val) out.mem) =
      (∑ i : Fin cfg.P.d, Rcore.phi (tok.coreHandle i.val) (tok.coreTok i.val) mem) :=
    Finset.sum_congr rfl fun i _ => (hcorePhi2 i.val i.isLt).trans (hcorePhi1 i.val i.isLt)
  have hcostFinal : (47 + (cTree + (cOff + (7 + 2 + 1) + 1) + 1) + 1) + Rrep.phi root tokFinal out.mem ≤
      (S.card + 1) * (detectTreeStepBudget L model.extG.n + 2) + 200 + Rrep.phi root tok mem := by
    change _ + (Rtree.phi tokFinal.treeHeap tokFinal.treeTok out.mem +
      (∑ i : Fin cfg.P.d, Rcore.phi (tokFinal.coreHandle i.val) (tokFinal.coreTok i.val) out.mem) +
      0 * detectOffTreeDrainUnit L) ≤
      (S.card + 1) * (detectTreeStepBudget L model.extG.n + 2) + 200 +
      (Rtree.phi tok.treeHeap tok.treeTok mem +
        (∑ i : Fin cfg.P.d, Rcore.phi (tok.coreHandle i.val) (tok.coreTok i.val) mem) +
        tok.offReadyCount * detectOffTreeDrainUnit L)
    have htreePhi2' : Rtree.phi tokFinal.treeHeap tokFinal.treeTok out.mem =
        Rtree.phi tok.treeHeap curTreeTok mid1.mem := htreePhi2
    rw [hcoresSum, htreePhi2', Nat.zero_mul, Nat.add_zero]
    rw [htn, hmid0Mem] at hcTree
    have hmul : (treeReadySet model).card * (detectTreeStepBudget L model.extG.n + 2) ≤
        S.card * (detectTreeStepBudget L model.extG.n + 2) :=
      Nat.mul_le_mul_right _ htrCardLe
    have hfinLe : detectTreeFinalBudget L model.extG.n ≤ detectTreeStepBudget L model.extG.n := by
      unfold detectTreeFinalBudget detectTreeStepBudget; omega
    rw [Nat.add_mul, one_mul]
    dsimp only [tokMid, tokFinal, L, Rtree] at hcTree hcOff hmul hfinLe ⊢
    omega
  have hPresMeta : PreservesLevelMeta tok tokFinal mem out.mem := by
    refine ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ ha => Or.inl (Or.inl ha), fun a ht => ?_⟩
    have hne : tok.tag a ≠ 0 ∧ tok.tag a ≠ 1 ∧ tok.tag a ≠ 13 ∧ tok.tag a ≠ 15 ∧ tok.tag a ≠ 16 := by
      rcases ht with h | h | h | h <;> rw [h] <;> exact ⟨by omega, by omega, by omega, by omega, by omega⟩
    have hlt : a < base := hbelow a (Or.inl (hOwn a hne.1))
    have htagEq : tokFinal.tag a = tok.tag a := by
      dsimp only [tokFinal, tokMid]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    have hnfTree : ¬ Rtree.foot tok.treeHeap tok.treeTok a := fun h => hne.2.2.2.2 (t16 a h)
    have hneBase : a ≠ base := by omega
    have hne11 : a ≠ root + 11 := fun h => hne.2.1 (h ▸ t1 11 (by omega))
    have hnotIO : a < tokMid.inOffReady ∨ tokMid.inOffReady + tokMid.intCap ≤ a := by
      by_contra h; push Not at h; dsimp only [tokMid] at h
      have h15 := t15 (a - tok.inOffReady) (by omega)
      rw [Nat.add_sub_of_le h.1] at h15; exact hne.2.2.2.1 h15
    have hnotER : a < tokMid.edgeRecords ∨ tokMid.edgeRecords + tokMid.intCap ≤ a := by
      by_contra h; push Not at h; dsimp only [tokMid] at h
      have h13 := t13 (a - tok.edgeRecords) (by omega)
      rw [Nat.add_sub_of_le h.1] at h13; exact hne.2.2.1 h13
    refine ⟨htagEq, ?_⟩
    dsimp only [out]
    rw [Function.update_of_ne hneBase,
      hframe2 a (by omega) hne11 (Or.inl (by omega)) hnotIO hnotER,
      hframe1 a (by omega) hnfTree (Or.inl (by omega)), hmid0Mem]
  -- The record pointers: the tree phase does not touch them (tag `13`, not in the tree foot),
  -- the drain keeps the blocks apart, and the final store is at `base`.
  have hptrLt (e : ℕ) (he : e ∈ model.extG.E) : tok.edgeRecords + model.extToInt e < base :=
    hbelow _ (Or.inl (hOwn _ (by rw [t13 _ (solverStateRep_extToInt_lt hrep0 he)]; decide)))
  have hsepOut : OffTreeRecSep model L mem tok.edgeRecords →
      OffTreeRecSep (algorithm2_detect cfg model).2 L out.mem tokFinal.edgeRecords := fun hsep0 => by
    have hsep1 : OffTreeRecSep model L mid1.mem tok.edgeRecords :=
      hsep0.of_agree fun e he => by
        have hnfTree : ¬ Rtree.foot tok.treeHeap tok.treeTok (tok.edgeRecords + model.extToInt e) :=
          fun h => by
            have h16 := t16 _ h
            rw [t13 _ (solverStateRep_extToInt_lt hrep0 he)] at h16
            exact absurd h16 (by decide)
        have hlt := hptrLt e he
        rw [hframe1 _ (by omega) hnfTree (Or.inl (by omega)), hmid0Mem]
    have hsep2 : OffTreeRecSep model L mid2.mem tok.edgeRecords := hsepOff hsep1
    have hsep3 : OffTreeRecSep model L out.mem tok.edgeRecords :=
      hsep2.of_agree fun e he => by
        dsimp only [out]
        rw [Function.update_of_ne (hptrLt e he).ne]
    exact hsep3
  refine ⟨curHeap₂, 47 + (cTree + (cOff + (7 + 2 + 1) + 1) + 1) + 1, out, tokFinal,
    hrFull, ⟨rfl, hDetectAt, hStateFits'⟩, hrepFinal, hPresMeta, rfl, hnum1,
    fun a ha => by dsimp only [out]; rw [Function.update_of_ne (by omega)]; exact hz2 a ha,
    by omega, ?_, hframeFinal, hfootFinal, hcostFinal, hsepOut⟩
  have hmulSp := Nat.mul_le_mul_right (detectTreeRoundSpace L) (Nat.add_le_add_right htrCardLe 1)
  dsimp only [tokMid, S, L] at hmulSp hcur1Hi hcur2Hi ⊢; omega

end MinCostFlow.MinRatio
