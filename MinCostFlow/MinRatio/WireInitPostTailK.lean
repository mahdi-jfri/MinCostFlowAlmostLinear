module

public import MinCostFlow.MinRatio.WireInitPostTailBaseK
import WordRAM.Tactic

/-!
# Post-tail execution with space and cost+potential bounds (`WireInitPostTailK`)

Composes `initPostTailStages123K_runs` and `initPostTailStage4K_runs` (`WireInitPostTailBaseK`)
with `initPostTailStoreRootDir` (`InitConcretePostTail`) to prove `solverInitPostTailBodyK_runs`
with exact space (`initPostTailSpace`) and cost + potential (`initPostTailCost`) bounds.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program SparseCore.Program LastLevelProgram

private theorem initPostTailStoreRootDirMeta_straight : IsStraightLine initPostTailStoreRootDirMeta := by
  simp [initPostTailStoreRootDirMeta, initPostTailStoreRootDirBody, IsStraightLine]

private theorem initPostTailStoreRootDirMeta_cost_le : straightLineCost initPostTailStoreRootDirMeta ≤ 150 := by decide

/-- Stage 5 of `solverInitPostTailBody`: runs `initPostTailStoreRootDirMeta` and preserves all
memory invariants and potentials above `root + 16`. -/
private theorem initPostTailStage5K_runs
    {w root table handle levelsEnd rootGraph
      forward inverse edgeThresholds freshCounter treeHeap treeEnd
      slots names slotThresholds edgeRecords offReadyList inOffReady threshHeap afterThresh finalHeap
      m ec0 V Ψ k epsExp coreDepth L P searchSpace readSpace linkSpace vcLast ecLast : ℕ}
    {T : SparseCoreRestartTool} {C : ChainParams}
    {Rcore : DSRep (SparseCoreOrdAbs T)} {Rtree : DSRep PathTreeState}
    {p : Program} {ω : ℕ → Bool} {st s3 s4 : State}
    {G : MGraph} {chain : ChainState T C} {B : ℤ} {thVal : ℕ → ℤ} {val : ℕ → PathEdgeValue}
    {thPtr recPtr : ℕ → ℕ}
    {sFin : PathTreeState} {yTree : Rtree.τ} {slotFin nameFin : ℕ → ℕ}
    {yCore : ℕ → Rcore.τ} {yTerm : ℕ} {metaStatic : ℕ → Prop}
    (PL : PTLayout w root table handle levelsEnd rootGraph
      forward inverse edgeThresholds freshCounter treeHeap treeEnd
      slots names slotThresholds edgeRecords offReadyList inOffReady threshHeap afterThresh
      m G.n ec0 L C.d linkSpace)
    (hlocalCore : Rcore.Local) (hlocalTree : Rtree.Local)
    (hhandleEq : handle = table + (4 * C.d + 4))
    (hfreshEq : freshCounter = levelsEnd + (4 * (C.d + 1) + 1))
    (hafterLe : afterThresh ≤ finalHeap)
    (hthPtrBounds : ∀ e < m, threshHeap ≤ thPtr e ∧ thPtr e + L ≤ afterThresh)
    (hrecPtrBounds : ∀ e < m, threshHeap ≤ recPtr e ∧ recPtr e + (2 + 4 * L) ≤ afterThresh)
    (hmetaBounds : ∀ a, metaStatic a → handle + 18 + (C.d + 1) + (C.d + 1) ≤ a ∧ a < levelsEnd)
    (hG : DynGraphAt st.mem rootGraph G.n ec0 G)
    (hdetect0 : DetectHeaderAt st.mem handle treeHeap forward inverse edgeThresholds m L searchSpace readSpace)
    (hnum0 : MinRatioNumericHeaderAt st.mem handle L P searchSpace readSpace)
    (hchain0 : SolverChainHeaderAt st.mem handle m V C.d C.k Ψ (root + 16) k epsExp coreDepth)
    (hfresh0 : FreshTablesAt st.mem forward inverse freshCounter m m id id m)
    (hsched0 : ∀ a, levelsEnd ≤ a → a < freshCounter → st.mem a = 0)
    (hz0 : ZeroFrom st.mem treeEnd)
    (hs3_h1 : s3.mem (handle + 1) = names) (hs3_h3 : s3.mem (handle + 3) = slotThresholds)
    (hs3_edges : ∀ e < m, s3.mem (edgeThresholds + e) = thPtr e ∧ s3.mem (edgeRecords + e) = recPtr e ∧
      PathIntAt s3.mem (thPtr e) 4 L (thVal e) ∧ PathEdgeAt s3.mem (recPtr e) 4 L (some (val e)))
    (hs3_frame : ∀ a < threshHeap, (a < edgeThresholds ∨ edgeThresholds + m ≤ a) →
      (a < edgeRecords ∨ edgeRecords + m ≤ a) → a ≠ handle + 1 → a ≠ handle + 3 →
      s3.mem a = st.mem a)
    (hs4_3 : s4.regs 3 = finalHeap)
    (hs4_69 : s4.regs 69 = rootGraph) (hs4_74 : s4.regs 74 = handle) (hs4_75 : s4.regs 75 = C.d)
    (hs4_81 : s4.regs 81 = forward) (hs4_82 : s4.regs 82 = inverse)
    (hs4_83 : s4.regs 83 = edgeThresholds) (hs4_84 : s4.regs 84 = m)
    (hs4_85 : s4.regs 85 = freshCounter) (hs4_86 : s4.regs 86 = edgeRecords)
    (hs4_87 : s4.regs 87 = slots) (hs4_88 : s4.regs 88 = names)
    (hs4_89 : s4.regs 89 = slotThresholds) (hs4_90 : s4.regs 90 = offReadyList)
    (hs4_91 : s4.regs 91 = inOffReady)
    (hinv4 : InitPathTreeInv Rtree treeHeap G chain.toTreeChain.chainTree val B
      slots names slotThresholds m thPtr chain.toTreeChain.chainTree.E
      sFin yTree slotFin nameFin finalHeap s4.mem)
    (hstat4 :
      let extraStatic := fun a => a < handle + 18 + (C.d + 1) + (C.d + 1) ∨
        metaStatic a ∨ (levelsEnd ≤ a ∧ a < treeHeap) ∨ (edgeRecords + m ≤ a ∧ a < afterThresh)
      ∀ a, InitChainStaticAddr rootGraph (handle + 18) (handle + 18 + (C.d + 1)) edgeRecords edgeThresholds
        C.d m L G chain.toTreeChain.chainTree recPtr extraStatic a → s4.mem a = s3.mem a)
    (hz4 : ZeroFrom s4.mem finalHeap)
    (htreeOut4 :
      let extraStatic := fun a => a < handle + 18 + (C.d + 1) + (C.d + 1) ∨
        metaStatic a ∨ (levelsEnd ≤ a ∧ a < treeHeap) ∨ (edgeRecords + m ≤ a ∧ a < afterThresh)
      ∀ a, Rtree.foot treeHeap yTree a →
        OutsideInitSlotTables slots names slotThresholds m G.n a ∧
        ¬ InitChainStaticAddr rootGraph (handle + 18) (handle + 18 + (C.d + 1)) edgeRecords edgeThresholds
            C.d m L G chain.toTreeChain.chainTree recPtr extraStatic a)
    (hcores4 :
      let extraStatic := fun a => a < handle + 18 + (C.d + 1) + (C.d + 1) ∨
        metaStatic a ∨ (levelsEnd ≤ a ∧ a < treeHeap) ∨ (edgeRecords + m ≤ a ∧ a < afterThresh)
      let Rterm := lastLevelRepresentation vcLast ecLast 4 L P (chain.G C.d).E
      OrdInitChainCoresK Rcore Rterm Rtree chain treeHeap (handle + 18) (handle + 18 + (C.d + 1))
        rootGraph edgeRecords edgeThresholds slots names slotThresholds m L finalHeap G recPtr extraStatic
        yCore yTerm yTree s4.mem) :
    let extraStatic := fun a => a < handle + 18 + (C.d + 1) + (C.d + 1) ∨
      metaStatic a ∨ (levelsEnd ≤ a ∧ a < treeHeap) ∨ (edgeRecords + m ≤ a ∧ a < afterThresh)
    let Rterm := lastLevelRepresentation vcLast ecLast 4 L P (chain.G C.d).E
    ∃ out c5,
      Runs w p ω initPostTailStoreRootDirMeta s4 .normal out c5 ∧
      out.regs 99 = finalHeap ∧
      SolverRootDirAt out.mem root handle table levelsEnd forward inverse freshCounter
        slots names slotThresholds edgeThresholds edgeRecords 0 offReadyList inOffReady rootGraph m ∧
      DetectHeaderAt out.mem handle treeHeap names inverse slotThresholds m L searchSpace readSpace ∧
      MinRatioNumericHeaderAt out.mem handle L P searchSpace readSpace ∧
      SolverChainHeaderAt out.mem handle m V C.d C.k Ψ (root + 16) k epsExp coreDepth ∧
      FreshTablesAt out.mem forward inverse freshCounter m m id id m ∧
      (∀ a, levelsEnd ≤ a → a < freshCounter → out.mem a = 0) ∧
      (∀ e < m, out.mem (inOffReady + e) = 0) ∧
      (∀ e < m, out.mem (edgeThresholds + e) = thPtr e ∧ out.mem (edgeRecords + e) = recPtr e ∧
        PathIntAt out.mem (thPtr e) 4 L (thVal e) ∧ PathEdgeAt out.mem (recPtr e) 4 L (some (val e))) ∧
      InitPathTreeInv Rtree treeHeap G chain.toTreeChain.chainTree val B
        slots names slotThresholds m thPtr chain.toTreeChain.chainTree.E
        sFin yTree slotFin nameFin finalHeap out.mem ∧
      ZeroFrom out.mem finalHeap ∧
      (∀ a < root, out.mem a = st.mem a) ∧
      (∀ a, root + 16 ≤ a → a < handle → out.mem a = st.mem a) ∧
      (∀ i < C.d, out.mem (handle + 18 + i) = st.mem (handle + 18 + i)) ∧
      (∀ a, metaStatic a → out.mem a = st.mem a) ∧
      DynGraphAt out.mem rootGraph G.n ec0 G ∧
      OrdInitChainCoresK Rcore Rterm Rtree chain treeHeap (handle + 18) (handle + 18 + (C.d + 1))
        rootGraph edgeRecords edgeThresholds slots names slotThresholds m L finalHeap G recPtr extraStatic
        yCore yTerm yTree out.mem ∧
      Rtree.phi treeHeap yTree out.mem = Rtree.phi treeHeap yTree s4.mem ∧
      (∑ i : Fin C.d, Rcore.phi (out.mem (handle + 18 + i.val)) (yCore i.val) out.mem) =
        (∑ i : Fin C.d, Rcore.phi (s4.mem (handle + 18 + i.val)) (yCore i.val) s4.mem) ∧
      c5 ≤ 150 := by
  intro extraStatic Rterm
  let levelTable := handle + 18
  let branchTable := handle + 18 + (C.d + 1)
  have hlev_le_th : levelsEnd ≤ edgeThresholds :=
    PL.lev_le_fc.trans ((Nat.le_of_lt PL.fc_lt_fwd).trans (PL.fwd_le_inv.trans PL.inv_le_th))
  have hlev_le_tree : levelsEnd ≤ treeHeap := hlev_le_th.trans PL.th_le_tree
  have hend_le_rec : treeEnd ≤ edgeRecords :=
    PL.end_le_slots.trans ((Nat.le_add_right slots m).trans (PL.slotsEnd_le_names.trans
      ((Nat.le_add_right names (2 * G.n)).trans (PL.namesEnd_le_st.trans
        ((Nat.le_add_right slotThresholds (2 * G.n)).trans PL.stEnd_le_rec)))))
  have hrec_le_thH : edgeRecords ≤ threshHeap :=
    (Nat.le_add_right edgeRecords m).trans (PL.recEnd_le_off.trans
      ((Nat.le_add_right offReadyList m).trans (PL.offEnd_le_inOff.trans
        ((Nat.le_add_right inOffReady m).trans PL.inOffEnd_le_thH))))
  have hlev_le_rec : levelsEnd ≤ edgeRecords := hlev_le_tree.trans (PL.tree_le_end.trans hend_le_rec)
  have hlev_le_thH : levelsEnd ≤ threshHeap := hlev_le_rec.trans hrec_le_thH
  have hroot16_le_lev : root + 16 ≤ levelsEnd := PL.root16_le_handle.trans ((Nat.le_add_right _ _).trans PL.handle17_le_lev)
  have hroot16_le_tree : root + 16 ≤ treeHeap := hroot16_le_lev.trans hlev_le_tree
  have hroot16_le_end : root + 16 ≤ treeEnd := hroot16_le_tree.trans PL.tree_le_end
  have hroot16_le_rec : root + 16 ≤ edgeRecords := hroot16_le_end.trans hend_le_rec
  have hroot16_le_thH : root + 16 ≤ threshHeap := hroot16_le_rec.trans hrec_le_thH
  have hroot16_lt_brEnd : root + 16 < handle + 18 + (C.d + 1) + (C.d + 1) :=
    lt_of_le_of_lt PL.root16_le_handle (lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 18))
      ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))
  have hframe3_below (a : ℕ) (ha : a < levelsEnd) (h1 : a ≠ handle + 1) (h3 : a ≠ handle + 3) :
      s3.mem a = st.mem a :=
    hs3_frame a (lt_of_lt_of_le ha hlev_le_thH) (Or.inl (lt_of_lt_of_le ha hlev_le_th))
      (Or.inl (lt_of_lt_of_le ha hlev_le_rec)) h1 h3
  have halphaS4 : s4.mem (handle + 14) = root + 16 := by
    have hlt1 : handle + 14 < handle + 18 + (C.d + 1) + (C.d + 1) :=
      lt_of_lt_of_le (Nat.add_lt_add_left (by decide : 14 < 18) handle)
        ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
    have hlt2 : handle + 14 < levelsEnd := lt_of_lt_of_le hlt1 PL.brEnd_le_lev
    rw [hstat4 (handle + 14) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlt1))))))),
      hframe3_below _ hlt2 (ne_of_gt (Nat.add_lt_add_left (by decide : 1 < 14) handle))
        (ne_of_gt (Nat.add_lt_add_left (by decide : 3 < 14) handle))]
    simpa [Nat.add_assoc] using hchain0 5 (by simp)
  obtain ⟨out, c5, hr5, hout99, hrootDir, houtFrame⟩ :=
    initPostTailStoreRootDirMeta_runs (w := w) (p := p) (ω := ω) (st := s4)
      hs4_3 hs4_69 hs4_74 hs4_75 hs4_81 hs4_82 hs4_83 hs4_84 hs4_85 hs4_86 hs4_87 hs4_88
      hs4_89 hs4_90 hs4_91 hhandleEq hfreshEq halphaS4 PL.root16_lt_w PL.handle14_lt_w PL.fc_lt_w PL.hw16
  have hc5 : c5 ≤ 150 := (straightLine_cost_eq initPostTailStoreRootDirMeta_straight hr5).symm ▸
    initPostTailStoreRootDirMeta_cost_le
  have houtAgreeGe (a : ℕ) (ha : root + 16 ≤ a) : out.mem a = s4.mem a := houtFrame a (Or.inr ha)
  have hlt16_static (a : ℕ) (hlt : a < root + 16) :
      InitChainStaticAddr rootGraph levelTable branchTable edgeRecords edgeThresholds
        C.d m L G chain.toTreeChain.chainTree recPtr extraStatic a :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (lt_trans hlt hroot16_lt_brEnd)))))))
  have htreeLocOut := hlocalTree treeHeap sFin yTree s4.mem out.mem (fun a ha =>
    (houtAgreeGe a (Nat.le_of_not_lt fun hlt => (htreeOut4 a ha).2 (hlt16_static a hlt))).symm)
  have hCoreOut (i : ℕ) (hi : i < C.d) :
      out.mem (levelTable + i) = s4.mem (levelTable + i) ∧
      out.mem (branchTable + i) = chain.bran i ∧
      Rcore.rep (out.mem (levelTable + i)) (chainLevelOrdAbs chain i) (yCore i) out.mem ∧
      Rcore.phi (out.mem (levelTable + i)) (yCore i) out.mem =
        Rcore.phi (s4.mem (levelTable + i)) (yCore i) s4.mem := by
    obtain ⟨hbr, hrep, hfoot⟩ := hcores4.1 i hi
    have hlv := houtAgreeGe (levelTable + i) (PL.root16_le_handle.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))
    have hbrG := houtAgreeGe (branchTable + i) (PL.root16_le_handle.trans
      ((Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))))
    have hloc := hlocalCore (s4.mem (levelTable + i)) (chainLevelOrdAbs chain i)
      (yCore i) s4.mem out.mem (fun a ha =>
        (houtAgreeGe a (Nat.le_of_not_lt fun hlt => (hfoot a ha).2.2.1 (hlt16_static a hlt))).symm)
    exact ⟨hlv, hbrG.trans hbr, by rw [hlv]; exact hloc.1 hrep, by rw [hlv]; exact hloc.2.symm⟩
  have hlvTermGe : root + 16 ≤ levelTable + C.d :=
    PL.root16_le_handle.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
  have hbrTermGe : root + 16 ≤ branchTable + C.d :=
    PL.root16_le_handle.trans ((Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))
  have hTermOut := (lastLevelRepresentation_local vcLast ecLast 4 L P (chain.G C.d).E)
    (s4.mem (levelTable + C.d)) (chain.lastK, chain.lastLSFs) yTerm s4.mem out.mem (fun a ha =>
      (houtAgreeGe a (Nat.le_of_not_lt fun hlt => (hcores4.2.2.2 a ha).2.2.1 (hlt16_static a hlt))).symm)
  have hhdrStat (k : ℕ) (hk : k < 18) :
      out.mem (handle + k) = s3.mem (handle + k) := by
    have h1 : handle + k < handle + 18 + (C.d + 1) + (C.d + 1) :=
      lt_of_lt_of_le (Nat.add_lt_add_left hk handle) ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
    rw [houtAgreeGe (handle + k) (PL.root16_le_handle.trans (Nat.le_add_right _ _)),
      hstat4 (handle + k) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1)))))))]
  have hhdrBelow (k : ℕ) (hk : k < 18) (h1 : k ≠ 1) (h3 : k ≠ 3) :
      out.mem (handle + k) = st.mem (handle + k) := by
    have hlt : handle + k < levelsEnd := lt_of_lt_of_le (Nat.add_lt_add_left hk handle) PL.handle17_le_lev
    rw [hhdrStat k hk, hframe3_below (handle + k) hlt
      (fun h => h1 (Nat.add_left_cancel h)) (fun h => h3 (Nat.add_left_cancel h))]
  refine ⟨out, c5, hr5, hout99, hrootDir, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun a ha => (houtAgreeGe a (hroot16_le_thH.trans (PL.thH_le_after.trans (hafterLe.trans ha)))).trans (hz4 a ha),
    ?_, ?_, ?_, ?_, ?_, ?_, htreeLocOut.2.symm, Finset.sum_congr rfl fun i _ => (hCoreOut i.val i.isLt).2.2.2, hc5⟩
  · intro j hj
    have hj8 : j < 8 := by simpa [List.length] using hj
    interval_cases j
    · exact (hhdrBelow 0 (by decide) (by decide) (by decide)).trans (hdetect0 0 (by simp))
    · exact (hhdrStat 1 (by decide)).trans hs3_h1
    · exact (hhdrBelow 2 (by decide) (by decide) (by decide)).trans (hdetect0 2 (by simp))
    · exact (hhdrStat 3 (by decide)).trans hs3_h3
    · exact (hhdrBelow 4 (by decide) (by decide) (by decide)).trans (hdetect0 4 (by simp))
    · exact (hhdrBelow 5 (by decide) (by decide) (by decide)).trans (hdetect0 5 (by simp))
    · exact (hhdrBelow 6 (by decide) (by decide) (by decide)).trans (hdetect0 6 (by simp))
    · exact (hhdrBelow 7 (by decide) (by decide) (by decide)).trans (hdetect0 7 (by simp))
  · intro j hj
    have hj4 : j < 4 := by simpa [List.length] using hj
    rw [Nat.add_assoc]
    exact (hhdrBelow (5 + j) (lt_trans (Nat.add_lt_add_left hj4 5) (by decide : 5 + 4 < 18))
      (ne_of_gt (lt_of_lt_of_le (by decide : 1 < 5) (Nat.le_add_right 5 j)))
      (ne_of_gt (lt_of_lt_of_le (by decide : 3 < 5) (Nat.le_add_right 5 j)))).trans
      (by simpa [Nat.add_assoc] using hnum0 j hj)
  · intro j hj
    have hj8 : j < 9 := by simpa [List.length] using hj
    rw [Nat.add_assoc]
    exact (hhdrBelow (9 + j) (lt_of_lt_of_le (Nat.add_lt_add_left hj8 9) (by decide : 9 + 9 ≤ 18))
      (ne_of_gt (lt_of_lt_of_le (by decide : 1 < 9) (Nat.le_add_right 9 j)))
      (ne_of_gt (lt_of_lt_of_le (by decide : 3 < 9) (Nat.le_add_right 9 j)))).trans
      (by simpa [Nat.add_assoc] using hchain0 j hj)
  · have hag (a : ℕ) (hlo : levelsEnd ≤ a) (hhi : a < edgeThresholds) : out.mem a = st.mem a := by
      have hhiTree : a < treeHeap := lt_of_lt_of_le hhi PL.th_le_tree
      have hhiRec : a < edgeRecords := lt_of_lt_of_le (lt_of_lt_of_le hhiTree PL.tree_le_end) hend_le_rec
      rw [houtAgreeGe a (hroot16_le_lev.trans hlo),
        hstat4 a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hlo, hhiTree⟩))))))))),
        hs3_frame a (lt_of_lt_of_le hhiRec hrec_le_thH) (Or.inl hhi) (Or.inl hhiRec)
          (ne_of_gt (lt_of_lt_of_le (lt_trans (Nat.add_lt_add_left (by decide : 1 < 16) handle) PL.handle16_lt_lev) hlo))
          (ne_of_gt (lt_of_lt_of_le (lt_trans (Nat.add_lt_add_left (by decide : 3 < 16) handle) PL.handle16_lt_lev) hlo))]
    obtain ⟨hfc, hfwd, hinv⟩ := hfresh0
    exact ⟨(hag freshCounter PL.lev_le_fc (lt_of_lt_of_le PL.fc_lt_fwd (PL.fwd_le_inv.trans PL.inv_le_th))).trans hfc,
      fun e he => (hag (forward + e) (PL.lev_le_fc.trans ((Nat.le_of_lt PL.fc_lt_fwd).trans (Nat.le_add_right _ _)))
        (lt_of_lt_of_le (Nat.add_lt_add_left he forward) (PL.fwdEnd_le_inv.trans PL.inv_le_th))).trans (hfwd e he),
      fun e he => (hag (inverse + e) (PL.lev_le_fc.trans ((Nat.le_of_lt PL.fc_lt_fwd).trans (PL.fwd_le_inv.trans (Nat.le_add_right _ _))))
        (lt_of_lt_of_le (Nat.add_lt_add_left he inverse) PL.invEnd_le_th)).trans (hinv e he)⟩
  · intro a hlo hhi
    have hltTh : a < edgeThresholds := lt_of_lt_of_le hhi ((Nat.le_of_lt PL.fc_lt_fwd).trans (PL.fwd_le_inv.trans PL.inv_le_th))
    have hhiTree : a < treeHeap := lt_of_lt_of_le hltTh PL.th_le_tree
    have hhiRec : a < edgeRecords := lt_of_lt_of_le (lt_of_lt_of_le hhiTree PL.tree_le_end) hend_le_rec
    rw [houtAgreeGe a (hroot16_le_lev.trans hlo),
      hstat4 a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hlo, hhiTree⟩))))))))),
      hs3_frame a (lt_of_lt_of_le hhiRec hrec_le_thH) (Or.inl hltTh) (Or.inl hhiRec)
        (ne_of_gt (lt_of_lt_of_le (lt_trans (Nat.add_lt_add_left (by decide : 1 < 16) handle) PL.handle16_lt_lev) hlo))
        (ne_of_gt (lt_of_lt_of_le (lt_trans (Nat.add_lt_add_left (by decide : 3 < 16) handle) PL.handle16_lt_lev) hlo))]
    exact hsched0 a hlo hhi
  · intro e he
    have hloRecEnd : edgeRecords + m ≤ inOffReady + e :=
      PL.recEnd_le_off.trans ((Nat.le_add_right _ _).trans (PL.offEnd_le_inOff.trans (Nat.le_add_right _ _)))
    have hhiThH : inOffReady + e < threshHeap :=
      lt_of_lt_of_le (Nat.add_lt_add_left he inOffReady) PL.inOffEnd_le_thH
    have hloEnd : treeEnd ≤ inOffReady + e := hend_le_rec.trans ((Nat.le_add_right _ _).trans hloRecEnd)
    rw [houtAgreeGe (inOffReady + e) (hroot16_le_end.trans hloEnd),
      hstat4 (inOffReady + e) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hloRecEnd, lt_of_lt_of_le hhiThH PL.thH_le_after⟩))))))))),
      hs3_frame (inOffReady + e) hhiThH
        (Or.inr (PL.thEnd_le_tree.trans (PL.tree_le_end.trans hloEnd)))
        (Or.inr hloRecEnd)
        (ne_of_gt (lt_of_lt_of_le (lt_trans (Nat.add_lt_add_left (by decide : 1 < 16) handle) PL.handle16_lt_lev)
          (hlev_le_tree.trans (PL.tree_le_end.trans hloEnd))))
        (ne_of_gt (lt_of_lt_of_le (lt_trans (Nat.add_lt_add_left (by decide : 3 < 16) handle) PL.handle16_lt_lev)
          (hlev_le_tree.trans (PL.tree_le_end.trans hloEnd))))]
    exact hz0 _ hloEnd
  · intro e he
    obtain ⟨htLo, htHi⟩ := hthPtrBounds e he
    obtain ⟨hrLo, hrHi⟩ := hrecPtrBounds e he
    obtain ⟨heTh, heRec, hThAt, hRecAt⟩ := hs3_edges e he
    have hrecEnd_le_thH : edgeRecords + m ≤ threshHeap :=
      PL.recEnd_le_off.trans ((Nat.le_add_right _ _).trans (PL.offEnd_le_inOff.trans
        ((Nat.le_add_right _ _).trans PL.inOffEnd_le_thH)))
    refine ⟨(houtAgreeGe _ (hroot16_le_lev.trans (hlev_le_th.trans (Nat.le_add_right _ _)))).trans
        ((hstat4 _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Nat.le_add_right _ _, Nat.add_lt_add_left he edgeThresholds⟩)))))).trans heTh),
      (houtAgreeGe _ (hroot16_le_rec.trans (Nat.le_add_right _ _))).trans
        ((hstat4 _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨Nat.le_add_right _ _, Nat.add_lt_add_left he edgeRecords⟩))))).trans heRec),
      hThAt.congr (fun j hj => by
        rw [houtAgreeGe _ (hroot16_le_thH.trans (htLo.trans (Nat.le_add_right _ _))),
          hstat4 _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨hrecEnd_le_thH.trans (htLo.trans (Nat.le_add_right _ _)),
             lt_of_lt_of_le (Nat.add_lt_add_left hj (thPtr e)) htHi⟩)))))))))]),
      hRecAt.congr (fun a hlo hhi =>
        (houtAgreeGe a (hroot16_le_thH.trans (hrLo.trans hlo))).trans
          (hstat4 a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨hrecEnd_le_thH.trans (hrLo.trans hlo),
             lt_of_lt_of_le (by rw [Nat.add_assoc] at hhi; exact hhi) hrHi⟩)))))))))))⟩
  · obtain ⟨hn, hsub', hrepT, hfootT, ⟨hslotT, hnameT⟩, hwt, hstT, hzrT⟩ := hinv4
    exact ⟨hn, hsub', htreeLocOut.1 hrepT, hfootT,
      ⟨fun e he => (houtAgreeGe _ (hroot16_le_end.trans (PL.end_le_slots.trans (Nat.le_add_right _ _)))).trans (hslotT e he),
       fun k hk => (houtAgreeGe _ (hroot16_le_end.trans (PL.end_le_slots.trans
         ((Nat.le_add_right _ _).trans (PL.slotsEnd_le_names.trans (Nat.le_add_right _ _)))))).trans (hnameT k hk)⟩,
      hwt, fun e he => (houtAgreeGe _ (hroot16_le_end.trans (PL.end_le_slots.trans
        ((Nat.le_add_right _ _).trans (PL.slotsEnd_le_names.trans ((Nat.le_add_right _ _).trans
          (PL.namesEnd_le_st.trans (Nat.le_add_right _ _)))))))).trans (hstT e he), hzrT⟩
  · intro a ha
    have ha16 : a < root + 16 := lt_of_lt_of_le ha (Nat.le_add_right _ _)
    have haHandle : a < handle := lt_of_lt_of_le ha16 PL.root16_le_handle
    rw [houtFrame a (Or.inl ha), hstat4 a (hlt16_static a ha16),
      hframe3_below a (lt_of_lt_of_le ha16 hroot16_le_lev)
        (ne_of_lt (lt_of_lt_of_le haHandle (Nat.le_add_right _ _)))
        (ne_of_lt (lt_of_lt_of_le haHandle (Nat.le_add_right _ _)))]
  · intro a hlo hhi
    have hltBr : a < handle + 18 + (C.d + 1) + (C.d + 1) :=
      lt_of_lt_of_le hhi ((Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))
    rw [houtAgreeGe a hlo, hstat4 a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hltBr))))))),
      hframe3_below a (lt_of_lt_of_le hltBr PL.brEnd_le_lev)
        (ne_of_lt (lt_of_lt_of_le hhi (Nat.le_add_right _ _)))
        (ne_of_lt (lt_of_lt_of_le hhi (Nat.le_add_right _ _)))]
  · intro i hi
    have hltBr : handle + 18 + i < handle + 18 + (C.d + 1) + (C.d + 1) := by omega
    have hge16 : root + 16 ≤ handle + 18 + i :=
      PL.root16_le_handle.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
    rw [houtAgreeGe _ hge16, hstat4 _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hltBr))))))),
      hframe3_below _ (lt_of_lt_of_le hltBr PL.brEnd_le_lev) (by omega) (by omega)]
  · intro a hms
    obtain ⟨hlo, hhi⟩ := hmetaBounds a hms
    have hge16 : root + 16 ≤ a :=
      PL.root16_le_handle.trans ((Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans hlo)))
    have hne1 : a ≠ handle + 1 :=
      ne_of_gt (lt_of_lt_of_le (Nat.add_lt_add_left (by decide : 1 < 18) handle)
        ((Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans hlo)))
    have hne3 : a ≠ handle + 3 :=
      ne_of_gt (lt_of_lt_of_le (Nat.add_lt_add_left (by decide : 3 < 18) handle)
        ((Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans hlo)))
    rw [houtAgreeGe a hge16, hstat4 a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hms)))))))),
      hframe3_below a hhi hne1 hne3]
  · exact dynGraphAt_of_agree hG (fun a hlo hhi => by
      have hhi' : a < handle := lt_of_lt_of_le hhi PL.rootG_end_le_handle
      have hltBr : a < handle + 18 + (C.d + 1) + (C.d + 1) :=
        lt_of_lt_of_le hhi' ((Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))
      exact ((houtAgreeGe a (PL.root16_le_rootG.trans hlo)).trans
          (hstat4 a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hltBr))))))))).trans
        (hframe3_below a (lt_of_lt_of_le hhi PL.rootG_end_le_lev)
          (ne_of_lt (lt_of_lt_of_le hhi' (Nat.le_add_right _ _)))
          (ne_of_lt (lt_of_lt_of_le hhi' (Nat.le_add_right _ _)))))
  · refine ⟨fun i hi => ?_, (houtAgreeGe (branchTable + C.d) hbrTermGe).trans hcores4.2.1,
      by rw [houtAgreeGe (levelTable + C.d) hlvTermGe]; exact hTermOut.1 hcores4.2.2.1, fun a ha => ?_⟩
    · obtain ⟨hlv, hbr, hrep, _⟩ := hCoreOut i hi
      refine ⟨hbr, hrep, fun a ha => ?_⟩
      rw [hlv] at ha
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (hcores4.1 i hi).2.2 a ha
      exact ⟨h1, h2, h3, h4, fun j hj hne hfj => h5 j hj hne (by rwa [(hCoreOut j hj).1] at hfj),
        fun hft => h6 (by rwa [houtAgreeGe (levelTable + C.d) hlvTermGe] at hft)⟩
    · rw [houtAgreeGe (levelTable + C.d) hlvTermGe] at ha
      obtain ⟨h1, h2, h3, h4, h5⟩ := hcores4.2.2.2 a ha
      exact ⟨h1, h2, h3, h4, fun j hj hfj => h5 j hj (by rwa [(hCoreOut j hj).1] at hfj)⟩

/-- End-to-end K-contract execution of `solverInitPostTailBody`:
populates per-edge thresholds and `PathEdgeAt` records, inserts `chain.toTreeChain.chainTree` into
the Section 6 path tree with `InitPathTreeInv` and `OrdInitChainCoresK`, writes `SolverRootDirAt`
at `[root, root + 16)`, and bounds total space (`initPostTailSpace`) and cost + potentials
(`initPostTailCost`). -/
theorem solverInitPostTailBodyK_runs
    {w shift divide negate copy bind initCore initTree
      root table handle levelsEnd rootGraph gradient lengths
      forward inverse edgeThresholds freshCounter treeHeap treeEnd
      m ec0 V Ψ k epsExp coreDepth L P searchSpace readSpace
      depth treeConst linkSpace capExp capLimit vcLast ecLast : ℕ}
    {fmt : Num.Format w} {T : SparseCoreRestartTool}
    {C : ChainParams} {P_sc : SparseCoreOrdParams}
    {coreAlloc : ℕ → List ℕ → ℕ}
    {lvlM : ℕ → ℕ} {treeAlloc : ℕ → ℕ → List ℕ → ℕ} {N₀ : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs T)} {Rtree : DSRep PathTreeState}
    {opCore opLast opTree : ℕ → ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    {G : MGraph} {len₀ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    {chain : ChainState T C} {B : ℤ}
    {xCore : ℕ → Rcore.τ} {xTerm : ℕ} {sTree : PathTreeState} {xTree : Rtree.τ}
    {metaStatic : ℕ → Prop}
    (lenInt : ℕ → ℕ) (gradInt : ℕ → ℤ)
    (hFour : fmt.limbBits = 4) (hPeq : fmt.precision = P)
    (hlocalCore : Rcore.Local)
    (hH : chain.toTreeChain.Holds G len₀ σ σ_mwu γ_ℓ γ_c)
    (hshift : MeetsContract w p shift (Num.shiftLeftContract w 4))
    (hdiv : MeetsContract w p divide (Num.fixedDivideContract w 4))
    (hneg : MeetsContract w p negate (Num.negateContract w 4))
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hbind : MeetsContract w p bind (pathSlotBindContract w))
    (hcoreImpl : ∀ i < C.d,
      Rcore.Implements w p initCore opCore
        (sparseCoreOrdMachineContractKFBL fmt L depth T (chain.G i) C.k (lvlM i) N₀ G.n ec0
          capExp P_sc coreAlloc) ∧
      SparseCoreReadoutFootAt fmt L depth T (chain.G i) C.k (lvlM i) N₀ G.n ec0 capExp P_sc
        coreAlloc Rcore p opCore)
    (hLastReadout : p.procs[opLast 0]? = some LastLevelProgram.readoutBody)
    (htreeImpl : Rtree.Implements w p initTree opTree (pathTreeMachineContract fmt L treeConst treeAlloc))
    (hcoreInput : ∀ i < C.d,
      SparseCoreOrdInput T C.k (lvlM i) N₀ (chain.scState i) (chain.G i) (chain.levelOrd i) (chain.updCount i))
    (h67 : st.regs 67 = L) (h68 : st.regs 68 = P) (h69 : st.regs 69 = rootGraph)
    (h70 : st.regs 70 = gradient) (h71 : st.regs 71 = lengths)
    (h74 : st.regs 74 = handle) (h75 : st.regs 75 = C.d)
    (h80 : st.regs 80 = treeHeap) (h81 : st.regs 81 = forward) (h82 : st.regs 82 = inverse)
    (h83 : st.regs 83 = edgeThresholds) (h84 : st.regs 84 = m) (h85 : st.regs 85 = freshCounter)
    (h99 : st.regs 99 = treeEnd)
    (hhandleEq : handle = table + (4 * C.d + 4))
    (hfreshEq : freshCounter = levelsEnd + (4 * (C.d + 1) + 1))
    (hrootLe : root + 16 ≤ rootGraph)
    (hrootGEnd : rootGraph + dynGraphSize G.n ec0 ≤ table)
    (hlevGe : handle + 18 + (C.d + 1) + (C.d + 1) ≤ levelsEnd)
    (hfwdEq : forward = freshCounter + 1)
    (hinvEq : inverse = forward + m)
    (hthEq : edgeThresholds = inverse + m)
    (htreeEq : treeHeap = edgeThresholds + m)
    (htreeLe : treeHeap ≤ treeEnd)
    (hlenBelow : lengths + m * L ≤ root) (hgradBelow : gradient + m * L ≤ root)
    (hG : DynGraphAt st.mem rootGraph G.n ec0 G) (hELt : ∀ e ∈ G.E, e < m) (hcap0 : G.n + ec0 + 2 ≤ capLimit)
    (hdetect0 : DetectHeaderAt st.mem handle treeHeap forward inverse edgeThresholds m L searchSpace readSpace)
    (hnum0 : MinRatioNumericHeaderAt st.mem handle L P searchSpace readSpace)
    (hchain0 : SolverChainHeaderAt st.mem handle m V C.d C.k Ψ (root + 16) k epsExp coreDepth)
    (hfresh0 : FreshTablesAt st.mem forward inverse freshCounter m m id id m)
    (hsched0 : ∀ a, levelsEnd ≤ a → a < freshCounter → st.mem a = 0)
    (hrepTree0 : Rtree.rep treeHeap sTree xTree st.mem)
    (hinitTreePost : (pathTreeMachineContract fmt L treeConst treeAlloc).initPost
      [G.n, L, treeHeap] st.mem sTree st.mem)
    (hfootTree0 : ∀ a, Rtree.foot treeHeap xTree a → treeHeap ≤ a ∧ a < treeEnd)
    (hcores0 : ∀ i < C.d,
      st.mem (handle + 18 + (C.d + 1) + i) = chain.bran i ∧
      Rcore.rep (st.mem (handle + 18 + i)) (chainLevelOrdAbs chain i) (xCore i) st.mem ∧
      (∀ a, Rcore.foot (st.mem (handle + 18 + i)) (xCore i) a →
        handle + 18 + (C.d + 1) + (C.d + 1) ≤ a ∧ a < levelsEnd ∧
        (∀ j < C.d, j ≠ i → ¬ Rcore.foot (st.mem (handle + 18 + j)) (xCore j) a) ∧
        ¬ (lastLevelRepresentation vcLast ecLast 4 L fmt.precision (chain.G C.d).E).foot
            (st.mem (handle + 18 + C.d)) xTerm a))
    (hlastBr0 : st.mem (handle + 18 + (C.d + 1) + C.d) = chain.lastBran)
    (hrepTerm0 : (lastLevelRepresentation vcLast ecLast 4 L fmt.precision (chain.G C.d).E).rep
      (st.mem (handle + 18 + C.d)) (chain.lastK, chain.lastLSFs) xTerm st.mem)
    (hfootTerm0 : ∀ a, (lastLevelRepresentation vcLast ecLast 4 L fmt.precision (chain.G C.d).E).foot
      (st.mem (handle + 18 + C.d)) xTerm a →
      handle + 18 + (C.d + 1) + (C.d + 1) ≤ a ∧ a < levelsEnd ∧
      (∀ j < C.d, ¬ Rcore.foot (st.mem (handle + 18 + j)) (xCore j) a))
    (hhandlesW : ∀ i ≤ C.d, st.mem (handle + 18 + i) < 2 ^ w ∧
      st.mem (handle + 18 + (C.d + 1) + i) < 2 ^ w)
    (hlenAt : ∀ e < m, 0 < lenInt e ∧ PathIntAt st.mem (lengths + e * L) 4 L (lenInt e))
    (hgradAt : ∀ e < m, PathIntAt st.mem (gradient + e * L) 4 L (gradInt e))
    (hfits : ∀ e < m,
      let ε := ((2 : ℤ) ^ (P - epsExp) : ℝ) / (2 : ℝ) ^ P
      let th := detectorThreshold P ε ((lenInt e : ℝ) / (2 : ℝ) ^ P)
      Num.Fits 4 L (-th) ∧ Num.Fits 4 L th)
    (hvalB : ∀ e ∈ chain.toTreeChain.chainTree.E,
      let ε := ((2 : ℤ) ^ (P - epsExp) : ℝ) / (2 : ℝ) ^ P
      let v := initialPathEdgeValue P ε (gradInt e) (lenInt e)
      |v.gradient| ≤ B ∧ |v.length| ≤ B ∧ |v.flow| ≤ B ∧ |v.detector| ≤ B)
    (hB : 0 ≤ B)
    (hcapB : 2 * ((2 * G.n + 1 : ℕ) : ℤ) * (B + 0) < (Num.capacity 4 L : ℤ))
    (hPdiv : 4 ∣ P) (hPword : P < 2 ^ w) (hLpos : 0 < L)
    (hleEps : epsExp ≤ P) (hfitEps : P - epsExp + 1 < 4 * L)
    (hvw : 2 * G.n + 1 < 2 ^ w) (hwidth : Nat.log 2 (2 * G.n + 1) ≤ 4 * L)
    (hdW : C.d < 2 ^ w) (hw17 : 17 < 2 ^ w)
    (hz : ZeroFrom st.mem treeEnd)
    (hlinkAlloc : ∀ e ∈ chain.toTreeChain.chainTree.E, ∀ cur,
      treeEnd + m + 2 * G.n + 2 * G.n + m + m + m + 3 * L + m * initEdgeRecordSpace L ≤ cur →
      cur ≤ treeEnd + initPostTailSpace m G.n L C.d linkSpace →
      treeAlloc 0 G.n [treeHeap, G.tail e + 1, G.head e + 1,
        treeEnd + m + 2 * G.n + 2 * G.n + m + m + m + 3 * L + e * initEdgeRecordSpace L +
          Num.fixedDivideSpace L + L, cur] ≤ linkSpace)
    (hroom : treeEnd + initPostTailSpace m G.n L C.d linkSpace < 2 ^ w)
    (hmetaStatic : ∀ a, metaStatic a →
      handle + 18 + (C.d + 1) + (C.d + 1) ≤ a ∧ a < levelsEnd ∧
      (∀ i < C.d, ¬ Rcore.foot (st.mem (handle + 18 + i)) (xCore i) a) ∧
      ¬ (lastLevelRepresentation vcLast ecLast 4 L fmt.precision (chain.G C.d).E).foot
          (st.mem (handle + 18 + C.d)) xTerm a) :
    let ε := ((2 : ℤ) ^ (P - epsExp) : ℝ) / (2 : ℝ) ^ P
    let slots := treeEnd
    let names := treeEnd + m
    let slotThresholds := treeEnd + m + 2 * G.n
    let edgeRecords := treeEnd + m + 2 * G.n + 2 * G.n
    let offReadyList := treeEnd + m + 2 * G.n + 2 * G.n + m
    let inOffReady := treeEnd + m + 2 * G.n + 2 * G.n + m + m
    let threshHeap := treeEnd + m + 2 * G.n + 2 * G.n + m + m + m
    let afterThresh := threshHeap + 3 * L + m * initEdgeRecordSpace L
    let thPtr := fun e => threshHeap + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L
    let recPtr := fun e => threshHeap + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L + L
    let val := fun e => initialPathEdgeValue P ε (gradInt e) (lenInt e)
    let extraStatic := fun a => a < handle + 18 + (C.d + 1) + (C.d + 1) ∨
      metaStatic a ∨ (levelsEnd ≤ a ∧ a < treeHeap) ∨ (edgeRecords + m ≤ a ∧ a < afterThresh)
    let Rterm := lastLevelRepresentation vcLast ecLast 4 L P (chain.G C.d).E
    ∃ out finalHeap cost sFin yTree slotFin nameFin yCore yTerm,
      Runs w p ω
        (solverInitPostTailBodyAt 18 shift divide negate copy (opCore 2) (opCore 3) (opLast 0) (opTree 0) bind)
        st .normal out cost ∧
      out.regs 99 = finalHeap ∧
      SolverRootDirAt out.mem root handle table levelsEnd forward inverse freshCounter
        slots names slotThresholds edgeThresholds edgeRecords 0 offReadyList inOffReady rootGraph m ∧
      DetectHeaderAt out.mem handle treeHeap names inverse slotThresholds m L searchSpace readSpace ∧
      MinRatioNumericHeaderAt out.mem handle L P searchSpace readSpace ∧
      SolverChainHeaderAt out.mem handle m V C.d C.k Ψ (root + 16) k epsExp coreDepth ∧
      FreshTablesAt out.mem forward inverse freshCounter m m id id m ∧
      (∀ a, levelsEnd ≤ a → a < freshCounter → out.mem a = 0) ∧
      (∀ e < m, out.mem (inOffReady + e) = 0) ∧
      (∀ e < m, out.mem (edgeThresholds + e) = thPtr e ∧ out.mem (edgeRecords + e) = recPtr e ∧
        PathIntAt out.mem (thPtr e) 4 L (detectorThreshold P ε ((lenInt e : ℝ) / (2 : ℝ) ^ P)) ∧
        PathEdgeAt out.mem (recPtr e) 4 L (some (val e))) ∧
      InitPathTreeInv Rtree treeHeap G chain.toTreeChain.chainTree val B
        slots names slotThresholds m thPtr chain.toTreeChain.chainTree.E
        sFin yTree slotFin nameFin finalHeap out.mem ∧
      ZeroFrom out.mem finalHeap ∧ afterThresh ≤ finalHeap ∧
      finalHeap ≤ treeEnd + initPostTailSpace m G.n L C.d linkSpace ∧
      (∀ a < root, out.mem a = st.mem a) ∧
      (∀ a, root + 16 ≤ a → a < handle → out.mem a = st.mem a) ∧
      (∀ i < C.d, out.mem (handle + 18 + i) = st.mem (handle + 18 + i)) ∧
      (∀ a, metaStatic a → out.mem a = st.mem a) ∧
      DynGraphAt out.mem rootGraph G.n ec0 G ∧
      (∀ a, Rtree.foot treeHeap yTree a →
        OutsideInitSlotTables slots names slotThresholds m G.n a ∧
        ¬ InitChainStaticAddr rootGraph (handle + 18) (handle + 18 + (C.d + 1)) edgeRecords edgeThresholds
            C.d m L G chain.toTreeChain.chainTree recPtr extraStatic a) ∧
      OrdInitChainCoresK Rcore Rterm Rtree chain treeHeap (handle + 18) (handle + 18 + (C.d + 1))
        rootGraph edgeRecords edgeThresholds slots names slotThresholds m L finalHeap G recPtr extraStatic
        yCore yTerm yTree out.mem ∧
      cost + Rtree.phi treeHeap yTree out.mem +
          (∑ i : Fin C.d, Rcore.phi (out.mem (handle + 18 + i.val)) (yCore i.val) out.mem) ≤
        initPostTailCost m G.n L C.d treeConst P_sc.readout +
          Rtree.phi treeHeap xTree st.mem +
          (∑ i : Fin C.d, Rcore.phi (st.mem (handle + 18 + i.val)) (xCore i.val) st.mem) := by
  subst hPeq
  intro ε slots names slotThresholds edgeRecords offReadyList inOffReady threshHeap afterThresh
    thPtr recPtr val extraStatic Rterm
  have hArith : PostTailArithK w root table handle levelsEnd rootGraph gradient lengths
      forward inverse edgeThresholds freshCounter treeHeap treeEnd m G.n ec0 L C.d linkSpace :=
    ⟨hrootLe, hrootGEnd, hhandleEq.symm, hlevGe, hfreshEq.symm, hfwdEq.symm, hinvEq.symm,
      hthEq.symm, htreeEq.symm, htreeLe, hlenBelow, hgradBelow, hroom, hw17⟩
  obtain ⟨s3, c123, hr123, hs3_0, hs3_3, hs3_9, hs3_10, hs3_11, hs3_19, hs3_20, hs3_22, hs3_23,
      hs3_24, hs3_29, hs3_30, hs3_31, hs3_34, hs3_69, hs3_74, hs3_75, hs3_81, hs3_82, hs3_83,
      hs3_84, hs3_85, hs3_86, hs3_87, hs3_88, hs3_89, hs3_90, hs3_91, hs3_h1, hs3_h3,
      hs3_edges, hs3_z, hs3_frame, hc123⟩ :=
    initPostTailStages123K_runs (w := w) (p := p) (ω := ω) (st := st) lenInt gradInt hArith
      hshift hdiv hneg hcopy h67 h68 h69 h70 h71 h74 h75 h80 h81 h82 h83 h84 h85 h99
      hG.2.2.2.2.1 hG.2.2.2.2.2.1 (by simpa [Nat.add_assoc] using hchain0 7 (by simp))
      hlenAt hgradAt hfits hPdiv hPword hLpos hleEps hfitEps hz
  have hsp : initEdgeRecordSpace L = Num.fixedDivideSpace L + 5 * L + 2 := rfl
  have hthPtrB (e : ℕ) (he : e < m) : threshHeap ≤ thPtr e ∧ thPtr e + L ≤ afterThresh := by
    have hmul : e * initEdgeRecordSpace L + initEdgeRecordSpace L ≤ m * initEdgeRecordSpace L := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (Nat.succ_le_of_lt he)
    dsimp only [thPtr, afterThresh]; omega
  have hrecPtrB (e : ℕ) (he : e < m) : threshHeap ≤ recPtr e ∧ recPtr e + (2 + 4 * L) ≤ afterThresh := by
    have hmul : e * initEdgeRecordSpace L + initEdgeRecordSpace L ≤ m * initEdgeRecordSpace L := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (Nat.succ_le_of_lt he)
    dsimp only [recPtr, afterThresh]; omega
  have hafterSpace : afterThresh + initLinkChainSpace C.d m linkSpace =
      treeEnd + initPostTailSpace m G.n L C.d linkSpace := by
    dsimp only [afterThresh, threshHeap, initPostTailSpace]; omega
  have hPL := mkPTLayout (w := w) (root := root) (table := table) (handle := handle)
    (levelsEnd := levelsEnd) (rootGraph := rootGraph) (forward := forward) (inverse := inverse)
    (edgeThresholds := edgeThresholds) (freshCounter := freshCounter) (treeHeap := treeHeap)
    (treeEnd := treeEnd) (slots := slots) (names := names) (slotThresholds := slotThresholds)
    (edgeRecords := edgeRecords) (offReadyList := offReadyList) (inOffReady := inOffReady)
    (threshHeap := threshHeap) (afterThresh := afterThresh) (m := m) (n := G.n) (ec0 := ec0) (L := L)
    (d := C.d) (linkSpace := linkSpace)
    hrootLe hrootGEnd hhandleEq hlevGe hfreshEq hfwdEq hinvEq hthEq htreeEq htreeLe
    rfl rfl rfl rfl rfl rfl rfl (by dsimp only [afterThresh]; omega)
    (hafterSpace.symm ▸ hroom) hw17
  obtain ⟨s4, finalHeap, c4, sFin, yTree, slotFin, nameFin, yCore, yTerm,
      hr4, hs4_3, hs4_regsHi, hinv4, hstat4, hz4, hafterLe, hfinHi, htreeOut4, hcores4, hc4⟩ :=
    initPostTailStage4K_runs hPL hFour rfl hH hbind hcoreImpl hLastReadout htreeImpl hcoreInput
      hthPtrB hrecPtrB (hafterSpace.symm ▸ hroom) hG hELt hcap0 hz
      hrepTree0 hinitTreePost hfootTree0 hcores0 hlastBr0 hrepTerm0 hfootTerm0 hhandlesW
      hs3_0 hs3_3 hs3_9 hs3_10 hs3_11 hs3_19 hs3_20 hs3_22 hs3_23 hs3_24 hs3_29 hs3_30 hs3_31 hs3_34
      hs3_edges hs3_z hs3_frame (fun _ _ => rfl) hvalB hB hcapB hvw hwidth hdW
      (fun e he cur hlo hhi => hlinkAlloc e he cur hlo (hafterSpace ▸ hhi)) hmetaStatic
  obtain ⟨out, c5, hr5, hout99, hrootDir, hdetect, hnum, hchain, hfresh, hsched, hoff, hedges,
      hinv, hzFin, hframeRoot, hframeBelowH, hframeLvl, hframeMeta, hDGOut, hcoresOut, hTreePhiOut, hCorePhiOut, hc5⟩ :=
    initPostTailStage5K_runs hPL hlocalCore htreeImpl.1 hhandleEq hfreshEq hafterLe hthPtrB hrecPtrB
      (fun a ha => ⟨(hmetaStatic a ha).1, (hmetaStatic a ha).2.1⟩)
      hG hdetect0 hnum0 hchain0 hfresh0 hsched0 hz hs3_h1 hs3_h3 hs3_edges hs3_frame
      hs4_3 ((hs4_regsHi 69 (by decide)).trans hs3_69) ((hs4_regsHi 74 (by decide)).trans hs3_74)
      ((hs4_regsHi 75 (by decide)).trans hs3_75) ((hs4_regsHi 81 (by decide)).trans hs3_81)
      ((hs4_regsHi 82 (by decide)).trans hs3_82) ((hs4_regsHi 83 (by decide)).trans hs3_83)
      ((hs4_regsHi 84 (by decide)).trans hs3_84) ((hs4_regsHi 85 (by decide)).trans hs3_85)
      ((hs4_regsHi 86 (by decide)).trans hs3_86) ((hs4_regsHi 87 (by decide)).trans hs3_87)
      ((hs4_regsHi 88 (by decide)).trans hs3_88) ((hs4_regsHi 89 (by decide)).trans hs3_89)
      ((hs4_regsHi 90 (by decide)).trans hs3_90) ((hs4_regsHi 91 (by decide)).trans hs3_91)
      hinv4 hstat4 hz4 htreeOut4 hcores4
  have hrFull : Runs w p ω
      (solverInitPostTailBodyAt 18 shift divide negate copy (opCore 2) (opCore 3) (opLast 0) (opTree 0) bind)
      st .normal out (c123 + (c4 + c5 + 1) + 1) := by
    unfold solverInitPostTailBodyAt
    rcases runs_seq_iff.mp hr123 with ⟨_, _, _, hbad, _⟩ | ⟨a1, k1, k23, hk1, hk23, hck1⟩; · cases hbad
    rcases runs_seq_iff.mp hk23 with ⟨_, _, _, hbad, _⟩ | ⟨a2, k2, k3, hk2, hk3, hck2⟩; · cases hbad
    have hsum : k1 + (k2 + (k3 + (c4 + c5 + 1) + 1) + 1) + 1 = c123 + (c4 + c5 + 1) + 1 := by omega
    rw [← hsum]
    exact runs_seq_iff.mpr (Or.inr ⟨a1, k1, _, hk1,
      runs_seq_iff.mpr (Or.inr ⟨a2, k2, _, hk2,
      runs_seq_iff.mpr (Or.inr ⟨s3, k3, _, hk3,
      runs_seq_iff.mpr (Or.inr ⟨s4, c4, c5, hr4, hr5, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  refine ⟨out, finalHeap, c123 + (c4 + c5 + 1) + 1, sFin, yTree, slotFin, nameFin, yCore, yTerm,
    hrFull, hout99, hrootDir, hdetect, hnum, hchain, hfresh, hsched, hoff, hedges,
    hinv, hzFin, hafterLe, hafterSpace ▸ hfinHi, hframeRoot, hframeBelowH, hframeLvl, hframeMeta, hDGOut, htreeOut4, hcoresOut, ?_⟩
  rw [hTreePhiOut, hCorePhiOut]
  dsimp only [initPostTailCost]
  omega

end MinCostFlow.MinRatio
