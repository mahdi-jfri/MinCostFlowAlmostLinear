module

public import MinCostFlow.MinRatio.WireTreeSyncLoop
public import MinCostFlow.MinRatio.TreeEditPack
public import MinCostFlow.MinRatio.ShiftBranch
public import MinCostFlow.MinRatio.UpdateCycleLoopBase

/-!
# Terminal-level shift phases and chain-tree algebra

Provides the deterministic Word-RAM phase procedures (`shiftTermSetupBranch`,
`shiftTermPackEdits`, `shiftTermSetupLoop`, `shiftTermChainBody`), their run lemmas, and the
chain-tree difference identities used to prove `ShiftTermChainSyncSpecW` in `WireShiftTerm.lean`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program

/-! ### Phase 1–3 helper statements -/

/-- Phase 1: load terminal branch table pointers and advance `lastBran` modulo `lastK`. -/
@[expose] def shiftTermSetupBranch : Stmt :=
  .assign 27 (.reg 0) ;;
  .assign 28 (.reg 1) ;;
  .assign 29 (.load (.reg 27)) ;;
  .assign 30 (.load (.bin .add (.reg 29) (.const 11))) ;;
  .assign 31 (.bin .add (.reg 29) (.const 18)) ;;
  .assign 32 (.load (.bin .add (.reg 31) (.reg 30))) ;;
  .assign 0 (.bin .add (.bin .add (.reg 31) (.bin .add (.reg 30) (.const 1))) (.reg 30)) ;;
  .assign 1 (.load (.reg 32)) ;;
  .assign 33 (.load (.reg 0)) ;;
  shiftBranch

theorem shiftTermSetupBranch_noRand : shiftTermSetupBranch.NoRand := by
  simp [shiftTermSetupBranch, shiftBranch_noRand, Stmt.NoRand]

/-- Phase 2: resolve old and new terminal forest `DynGraphAt` headers and pack their edge
difference at `heap` via `treeEditPackForFold`. -/
@[expose] def shiftTermPackEdits : Stmt :=
  .assign 34 (.load (.bin .add (.bin .add (.reg 32) (.const 1)) (.reg 33))) ;;
  .assign 34 (.load (.bin .add (.reg 34) (.const 1))) ;;
  .assign 35 (.load (.bin .add (.bin .add (.reg 32) (.const 1)) (.reg 2))) ;;
  .assign 35 (.load (.bin .add (.reg 35) (.const 1))) ;;
  .assign 36 (.load (.reg 34)) ;;
  .assign 37 (.load (.bin .add (.reg 34) (.const 1))) ;;
  .assign 6 (.reg 28) ;;
  .assign 7 (.const 0) ;;
  .assign 14 (.bin .add (.bin .add (.reg 34) (.const 4)) (.bin .mul (.const 7) (.reg 36))) ;;
  .assign 10 (.bin .add (.reg 14) (.reg 37)) ;;
  .assign 11 (.load (.bin .add (.reg 34) (.const 3))) ;;
  .assign 9 (.bin .add (.bin .add (.reg 35) (.const 4)) (.bin .mul (.const 7) (.reg 36))) ;;
  .assign 12 (.bin .add (.reg 9) (.reg 37)) ;;
  .assign 13 (.load (.bin .add (.reg 35) (.const 3))) ;;
  .assign 18 (.const 0) ;;
  treeEditPackForFold

theorem shiftTermPackEdits_noRand : shiftTermPackEdits.NoRand := by
  simp [shiftTermPackEdits, treeEditPackForFold, treeEditPackBoth, treeEditPackScan,
    treeEditPackStep, treeEditPackName, treeEditPackSwitch, treeEditPackAppend, Stmt.NoRand]

/-- Phase 3: load path-tree sync registers from the solver root directory and header. -/
@[expose] def shiftTermSetupLoop : Stmt :=
  .assign 0 (.load (.reg 29)) ;;
  .assign 1 (.reg 27) ;;
  .assign 2 (.load (.bin .add (.reg 29) (.const 5))) ;;
  .assign 3 (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 18))) ;;
  .assign 38 (.load (.bin .add (.reg 27) (.const 14))) ;;
  .assign 39 (.load (.reg 38)) ;;
  .assign 40 (.load (.bin .add (.reg 38) (.const 1))) ;;
  .assign 41 (.bin .add (.bin .add (.reg 38) (.const 4)) (.bin .mul (.const 7) (.reg 39))) ;;
  .assign 9 (.bin .add (.reg 41) (.bin .mul (.const 3) (.reg 40))) ;;
  .assign 10 (.bin .add (.reg 41) (.bin .mul (.const 4) (.reg 40))) ;;
  .assign 11 (.bin .add (.bin .add (.reg 38) (.const 4)) (.bin .mul (.const 4) (.reg 39))) ;;
  .assign 19 (.load (.bin .add (.reg 27) (.const 6))) ;;
  .assign 20 (.load (.bin .add (.reg 27) (.const 7))) ;;
  .assign 22 (.load (.bin .add (.reg 27) (.const 10))) ;;
  .assign 23 (.load (.bin .add (.reg 27) (.const 9))) ;;
  .assign 24 (.load (.bin .add (.reg 27) (.const 8))) ;;
  .assign 25 (.load (.bin .add (.reg 27) (.const 12))) ;;
  .assign 26 (.load (.bin .add (.reg 27) (.const 13)))

theorem shiftTermSetupLoop_noRand : shiftTermSetupLoop.NoRand := by
  simp [shiftTermSetupLoop, Stmt.NoRand]

/-- Complete deterministic Word-RAM body for `ShiftTermChainSyncSpecW` taking `[root, heap]`
and returning `nextHeap`. -/
@[expose] def shiftTermChainBody (readTree cutTree linkTree bind canonCopy isNeg : ℕ) : Stmt :=
  shiftTermSetupBranch ;;
  shiftTermPackEdits ;;
  shiftTermSetupLoop ;;
  wireTreeSyncLoop readTree cutTree linkTree bind canonCopy isNeg ;;
  .ret (.reg 3)

theorem shiftTermChainBody_noRand (readTree cutTree linkTree bind canonCopy isNeg : ℕ) :
    (shiftTermChainBody readTree cutTree linkTree bind canonCopy isNeg).NoRand := by
  simp [shiftTermChainBody, shiftTermSetupBranch_noRand, shiftTermPackEdits_noRand,
    shiftTermSetupLoop_noRand, wireTreeSyncLoop_noRand, Stmt.NoRand]

/-! ### Algebraic chain-tree helpers -/

private def tcDel? : TreeChange → Option ℕ
  | .delete e => some e
  | .insert _ => none

private def tcIns? : TreeChange → Option ℕ
  | .delete _ => none
  | .insert e => some e

private theorem list_eq_dels_append_ins : ∀ (L : List TreeChange),
    (∀ (p r : List TreeChange) (e d : ℕ), L = p ++ .insert e :: r → TreeChange.delete d ∉ r) →
    L = (L.filterMap tcDel?).map .delete ++ (L.filterMap tcIns?).map .insert
  | [], _ => rfl
  | .delete e :: rest, hno => by
    have ih := list_eq_dels_append_ins rest (fun p r e' d heq =>
      hno (.delete e :: p) r e' d (by simp [heq]))
    change TreeChange.delete e :: rest =
      TreeChange.delete e :: (rest.filterMap tcDel?).map .delete ++ (rest.filterMap tcIns?).map .insert
    rw [List.cons_append, ← ih]
  | .insert e :: rest, hno => by
    have hnoDel : ∀ d, TreeChange.delete d ∉ rest := fun d => hno [] rest e d rfl
    clear hno
    have hfmD : rest.filterMap tcDel? = [] := by
      induction rest with
      | nil => rfl
      | cons x xs ih =>
        cases x with
        | delete d => exact (hnoDel d List.mem_cons_self).elim
        | insert y => exact ih (fun d hd => hnoDel d (List.mem_cons_of_mem _ hd))
    have hfmI : (rest.filterMap tcIns?).map TreeChange.insert = rest := by
      clear hfmD
      induction rest with
      | nil => rfl
      | cons x xs ih =>
        cases x with
        | delete d => exact (hnoDel d List.mem_cons_self).elim
        | insert y =>
          change TreeChange.insert y :: (xs.filterMap tcIns?).map TreeChange.insert = _
          rw [ih (fun d hd => hnoDel d (List.mem_cons_of_mem _ hd))]
    change TreeChange.insert e :: rest =
      (rest.filterMap tcDel?).map .delete ++ TreeChange.insert e :: (rest.filterMap tcIns?).map .insert
    rw [hfmD, hfmI]; rfl

theorem treeEditDiff_union_disjoint {P A B : Finset ℕ} {edits : List TreeChange}
    (hdisj : Disjoint P (A ∪ B)) (hdiff : TreeEditDifference A B edits) :
    TreeEditDifference (P ∪ A) (P ∪ B) edits := by
  have hdisjA : Disjoint P A := hdisj.mono_right Finset.subset_union_left
  have hdisjB : Disjoint P B := hdisj.mono_right Finset.subset_union_right
  have hSplit : edits = (edits.filterMap tcDel?).map .delete ++ (edits.filterMap tcIns?).map .insert :=
    list_eq_dels_append_ins edits (fun p r e d heq =>
      (heq ▸ hdiff).no_delete_after_insert)
  have hpermD : (edits.filterMap tcDel?).Perm (A \ B).toList := by
    have hp := hdiff.perm.filterMap tcDel?
    have h1 : (diffTreeChanges A B).filterMap tcDel? = (A \ B).toList := by
      simp [diffTreeChanges, List.filterMap_append, List.filterMap_map, Function.comp_def, tcDel?]
    rwa [h1] at hp
  have hpermI : (edits.filterMap tcIns?).Perm (B \ A).toList := by
    have hp := hdiff.perm.filterMap tcIns?
    have h1 : (diffTreeChanges A B).filterMap tcIns? = (B \ A).toList := by
      simp [diffTreeChanges, List.filterMap_append, List.filterMap_map, Function.comp_def, tcIns?]
    rwa [h1] at hp
  let dels := edits.filterMap tcDel?
  let ins := edits.filterMap tcIns?
  let common := (P ∪ (A ∩ B)).toList
  have ho : (dels ++ common).Perm (P ∪ A).toList := by
    refine List.perm_of_nodup_nodup_toFinset_eq ?_ (Finset.nodup_toList _) ?_
    · refine List.nodup_append.mpr ⟨hpermD.nodup_iff.mpr (Finset.nodup_toList _),
        Finset.nodup_toList _, fun x hx y hy hxy => ?_⟩
      subst hxy
      have h1 : x ∈ A \ B := Finset.mem_toList.mp (hpermD.mem_iff.mp hx)
      have h2 : x ∈ P ∪ (A ∩ B) := Finset.mem_toList.mp hy
      rcases Finset.mem_union.mp h2 with hp | hab
      · exact Finset.disjoint_left.mp hdisjA hp (Finset.mem_sdiff.mp h1).1
      · exact (Finset.mem_sdiff.mp h1).2 (Finset.mem_inter.mp hab).2
    · ext x
      simp only [List.toFinset_append, Finset.mem_union, List.mem_toFinset, dels, hpermD.mem_iff,
        Finset.mem_toList, Finset.mem_sdiff, Finset.mem_inter, common]
      tauto
  have hn : (ins ++ common).Perm (P ∪ B).toList := by
    refine List.perm_of_nodup_nodup_toFinset_eq ?_ (Finset.nodup_toList _) ?_
    · refine List.nodup_append.mpr ⟨hpermI.nodup_iff.mpr (Finset.nodup_toList _),
        Finset.nodup_toList _, fun x hx y hy hxy => ?_⟩
      subst hxy
      have h1 : x ∈ B \ A := Finset.mem_toList.mp (hpermI.mem_iff.mp hx)
      have h2 : x ∈ P ∪ (A ∩ B) := Finset.mem_toList.mp hy
      rcases Finset.mem_union.mp h2 with hp | hab
      · exact Finset.disjoint_left.mp hdisjB hp (Finset.mem_sdiff.mp h1).1
      · exact (Finset.mem_sdiff.mp h1).2 (Finset.mem_inter.mp hab).1
    · ext x
      simp only [List.toFinset_append, Finset.mem_union, List.mem_toFinset, ins, hpermI.mem_iff,
        Finset.mem_toList, Finset.mem_sdiff, Finset.mem_inter, common]
      tauto
  have hfO : (dels ++ common).filter (fun e => decide (e ∉ P ∪ B)) = dels := by
    rw [List.filter_append]
    have h1 : dels.filter (fun e => decide (e ∉ P ∪ B)) = dels := List.filter_eq_self.mpr fun x hx => by
      have hmem := Finset.mem_toList.mp (hpermD.mem_iff.mp hx)
      simp only [decide_eq_true_eq, Finset.mem_union, not_or]
      exact ⟨fun hp => Finset.disjoint_left.mp hdisjA hp (Finset.mem_sdiff.mp hmem).1,
        (Finset.mem_sdiff.mp hmem).2⟩
    have h2 : common.filter (fun e => decide (e ∉ P ∪ B)) = [] := List.filter_eq_nil_iff.mpr fun x hx => by
      have hmem := Finset.mem_toList.mp hx
      simp only [decide_eq_true_eq, not_not, Finset.mem_union]
      rcases Finset.mem_union.mp hmem with hp | hab
      · exact Or.inl hp
      · exact Or.inr (Finset.mem_inter.mp hab).2
    rw [h1, h2, List.append_nil]
  have hfN : (ins ++ common).filter (fun e => decide (e ∉ P ∪ A)) = ins := by
    rw [List.filter_append]
    have h1 : ins.filter (fun e => decide (e ∉ P ∪ A)) = ins := List.filter_eq_self.mpr fun x hx => by
      have hmem := Finset.mem_toList.mp (hpermI.mem_iff.mp hx)
      simp only [decide_eq_true_eq, Finset.mem_union, not_or]
      exact ⟨fun hp => Finset.disjoint_left.mp hdisjB hp (Finset.mem_sdiff.mp hmem).1,
        (Finset.mem_sdiff.mp hmem).2⟩
    have h2 : common.filter (fun e => decide (e ∉ P ∪ A)) = [] := List.filter_eq_nil_iff.mpr fun x hx => by
      have hmem := Finset.mem_toList.mp hx
      simp only [decide_eq_true_eq, not_not, Finset.mem_union]
      rcases Finset.mem_union.mp hmem with hp | hab
      · exact Or.inl hp
      · exact Or.inr (Finset.mem_inter.mp hab).1
    rw [h1, h2, List.append_nil]
  have hres := treeEditDifference_of_filter ho hn
  rw [hfO, hfN, ← hSplit] at hres
  exact hres

theorem treeEditDiff_len_eq {A B : Finset ℕ} {edits : List TreeChange}
    (h : TreeEditDifference A B edits) :
    edits.length = (diffTreeChanges A B).length :=
  h.perm.length_eq

theorem treeEditDiff_len_le {A B : Finset ℕ} {edits : List TreeChange}
    (h : TreeEditDifference A B edits) :
    edits.length ≤ A.card + B.card := by
  rw [h.result.1]
  exact Nat.add_le_add (Finset.card_le_card Finset.sdiff_subset)
    (Finset.card_le_card Finset.sdiff_subset)

theorem termShift_chainTree_eq {cfg : Alg2Config} (model : Alg2State cfg) :
    let model' := alg2LoopShiftStep cfg model (Fin.last cfg.P.d)
    let pref := (Finset.range cfg.P.d).biUnion fun j => (model.chain.toTreeChain.activeLSF j).F.F.E
    model.chain.toTreeChain.chainTree.E = pref ∪ (model.chain.lastLSFs model.chain.lastBran).F.F.E ∧
    model'.chain.toTreeChain.chainTree.E =
      pref ∪ (model.chain.lastLSFs ((model.chain.lastBran + 1) % model.chain.lastK)).F.F.E := by
  intro model' pref
  have h1 : model.chain.toTreeChain.chainTree.E =
      pref ∪ (model.chain.lastLSFs model.chain.lastBran).F.F.E := by
    simp only [TreeChain.chainTree, TreeChain.chainTreeEdges, Finset.range_add_one,
      Finset.biUnion_insert, Finset.union_comm, pref]
    congr 1
    simp [TreeChain.activeLSF, ChainState.toTreeChain]
  have h2 : model'.chain.toTreeChain.chainTree.E =
      pref ∪ (model.chain.lastLSFs ((model.chain.lastBran + 1) % model.chain.lastK)).F.F.E := by
    change ((Finset.range (cfg.P.d + 1)).biUnion
        fun j => (model'.chain.toTreeChain.activeLSF j).F.F.E) = _
    rw [Finset.range_add_one, Finset.biUnion_insert, Finset.union_comm]
    congr 1
    · apply Finset.biUnion_congr rfl
      intro j hj
      have hjlt : j < cfg.P.d := Finset.mem_range.mp hj
      simp [model', alg2LoopShiftStep, Chain.Ordered.algorithm1_shift, TreeChain.activeLSF,
        ChainState.toTreeChain, hjlt]
    · simp [model', alg2LoopShiftStep, Chain.Ordered.algorithm1_shift, TreeChain.activeLSF,
        ChainState.toTreeChain]
  exact ⟨h1, h2⟩

theorem termShift_totalTreeUpdates {cfg : Alg2Config} (model : Alg2State cfg) :
    let model' := alg2LoopShiftStep cfg model (Fin.last cfg.P.d)
    model'.chain.totalTreeUpdates - model.chain.totalTreeUpdates =
      (diffTreeChanges model.chain.toTreeChain.chainTree.E
        model'.chain.toTreeChain.chainTree.E).length := by
  let stMid : ChainState cfg.T cfg.P :=
    { model.chain with
      lastBran := (model.chain.lastBran + 1) % model.chain.lastK
      shiftCount := fun j => if j = cfg.P.d then model.chain.shiftCount cfg.P.d + 1
        else model.chain.shiftCount j }
  let chLen := (diffTreeChanges model.chain.toTreeChain.chainTree.E stMid.toTreeChain.chainTree.E).length
  have h1 : (alg2LoopShiftStep cfg model (Fin.last cfg.P.d)).chain.totalTreeUpdates =
      model.chain.totalTreeUpdates + chLen := by
    simp only [alg2LoopShiftStep, Chain.Ordered.algorithm1_shift, Fin.val_last, lt_self_iff_false,
      ↓reduceDIte, ChainState.totalTreeUpdates, chLen, stMid]
    omega
  have h2 : (alg2LoopShiftStep cfg model (Fin.last cfg.P.d)).chain.toTreeChain = stMid.toTreeChain := by
    simp [alg2LoopShiftStep, Chain.Ordered.algorithm1_shift, ChainState.toTreeChain, stMid]
  change (alg2LoopShiftStep cfg model (Fin.last cfg.P.d)).chain.totalTreeUpdates -
      model.chain.totalTreeUpdates = _
  rw [h1, h2]
  exact Nat.add_sub_cancel_left _ _

/-! ### Phase execution lemmas -/

theorem shiftTermSetupBranch_runs {w root heap handle d termHandle lastK oldLastBran pos : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    (hhandle : mem root = handle)
    (hd : mem (handle + 11) = d)
    (hterm : mem (handle + 18 + d) = termHandle)
    (hlastK : mem termHandle = lastK)
    (holdBran : mem (handle + 18 + (d + 1) + d) = oldLastBran)
    (hbranLt : oldLastBran < lastK) (hlastKW : lastK < 2 ^ w)
    (_hrootW : root < 2 ^ w) (_hheapW : heap < 2 ^ w)
    (hLevelW : handle + 18 + (d + 1) + d < 2 ^ w) (_htermW : termHandle < 2 ^ w) :
    let levelTable := handle + 18
    let termBranAddr := levelTable + (d + 1) + d
    let newLastBran := (oldLastBran + 1) % lastK
    ∃ out c, Runs w p ω shiftTermSetupBranch (startState [root, heap] mem pos) .normal out c ∧
      c ≤ 60 ∧ out.mem = Function.update mem termBranAddr newLastBran ∧
      out.regs 27 = root ∧ out.regs 28 = heap ∧ out.regs 29 = handle ∧
      out.regs 30 = d ∧ out.regs 31 = levelTable ∧ out.regs 32 = termHandle ∧
      out.regs 33 = oldLastBran ∧ out.regs 2 = newLastBran := by
  intro levelTable termBranAddr newLastBran
  have hw1 : 1 < 2 ^ w := by omega
  have hw11 : 11 < 2 ^ w := by omega
  have hw17 : 18 < 2 ^ w := by omega
  let s0 := startState [root, heap] mem pos
  let s1 := { s0 with regs := Function.update s0.regs 27 root }
  let s2 := { s1 with regs := Function.update s1.regs 28 heap }
  let s3 := { s2 with regs := Function.update s2.regs 29 handle }
  let s4 := { s3 with regs := Function.update s3.regs 30 d }
  let s5 := { s4 with regs := Function.update s4.regs 31 levelTable }
  let s6 := { s5 with regs := Function.update s5.regs 32 termHandle }
  let s7 := { s6 with regs := Function.update s6.regs 0 termBranAddr }
  let s8 := { s7 with regs := Function.update s7.regs 1 lastK }
  let s9 := { s8 with regs := Function.update s8.regs 33 oldLastBran }
  have r1 : Runs w p ω (.assign 27 (.reg 0)) s0 .normal s1 2 :=
    runs_assign_iff.mpr ⟨root, by simp [Expr.eval, s0, startState], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 28 (.reg 1)) s1 .normal s2 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, s1, s0, startState], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 29 (.load (.reg 27))) s2 .normal s3 3 :=
    runs_assign_iff.mpr ⟨handle, by simp [Expr.eval, s2, s1, s0, startState, hhandle], rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 30 (.load (.bin .add (.reg 29) (.const 11)))) s3 .normal s4 5 :=
    runs_assign_iff.mpr ⟨d, by simp [Expr.eval, BinOp.eval, s3, s2, s1, s0, startState, hw11,
      show handle + 11 < 2 ^ w by omega, hd], rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 31 (.bin .add (.reg 29) (.const 18))) s4 .normal s5 4 :=
    runs_assign_iff.mpr ⟨levelTable, by simp [Expr.eval, BinOp.eval, s4, s3, hw17,
      show levelTable < 2 ^ w by omega, levelTable], rfl, rfl, rfl⟩
  have r6 : Runs w p ω (.assign 32 (.load (.bin .add (.reg 31) (.reg 30)))) s5 .normal s6 5 :=
    runs_assign_iff.mpr ⟨termHandle, by simp [Expr.eval, BinOp.eval, s5, s4, s3, s2, s1, s0,
      startState, show levelTable + d < 2 ^ w by omega, levelTable, hterm], rfl, rfl, rfl⟩
  have r7 : Runs w p ω (.assign 0 (.bin .add (.bin .add (.reg 31) (.bin .add (.reg 30) (.const 1))) (.reg 30)))
      s6 .normal s7 8 :=
    runs_assign_iff.mpr ⟨termBranAddr, by simp [Expr.eval, BinOp.eval, s6, s5, s4, hw1,
      show d + 1 < 2 ^ w by omega, show levelTable + (d + 1) < 2 ^ w by omega,
      show termBranAddr < 2 ^ w by omega, termBranAddr], rfl, rfl, rfl⟩
  have r8 : Runs w p ω (.assign 1 (.load (.reg 32))) s7 .normal s8 3 :=
    runs_assign_iff.mpr ⟨lastK, by simp [Expr.eval, s7, s6, s5, s4, s3, s2, s1, s0, startState,
      hlastK], rfl, rfl, rfl⟩
  have r9 : Runs w p ω (.assign 33 (.load (.reg 0))) s8 .normal s9 3 :=
    runs_assign_iff.mpr ⟨oldLastBran, by simp [Expr.eval, s8, s7, s6, s5, s4, s3, s2, s1, s0,
      startState, termBranAddr, levelTable, holdBran], rfl, rfl, rfl⟩
  obtain ⟨out, rSh, hmemSh, hr2Sh, hrKeepSh, _⟩ :=
    shiftBranch_runs (w := w) (p := p) (ω := ω) (st := s9) (addr := termBranAddr)
      (by simp [s9, s8, s7]) (by simp [s9, s8]) (by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, s0,
        startState, termBranAddr, levelTable, holdBran]) hbranLt hlastKW
  refine ⟨out, _,
    runs_seq_iff.mpr (Or.inr ⟨s1, 2, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 2, _, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 3, _, r3,
    runs_seq_iff.mpr (Or.inr ⟨s4, 5, _, r4,
    runs_seq_iff.mpr (Or.inr ⟨s5, 4, _, r5,
    runs_seq_iff.mpr (Or.inr ⟨s6, 5, _, r6,
    runs_seq_iff.mpr (Or.inr ⟨s7, 8, _, r7,
    runs_seq_iff.mpr (Or.inr ⟨s8, 3, _, r8,
    runs_seq_iff.mpr (Or.inr ⟨s9, 3, 14, r9, rSh, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    by omega, hmemSh,
    by rw [hrKeepSh 27 (by decide)]; simp [s9, s8, s7, s6, s5, s4, s3, s2, s1],
    by rw [hrKeepSh 28 (by decide)]; simp [s9, s8, s7, s6, s5, s4, s3, s2],
    by rw [hrKeepSh 29 (by decide)]; simp [s9, s8, s7, s6, s5, s4, s3],
    by rw [hrKeepSh 30 (by decide)]; simp [s9, s8, s7, s6, s5, s4],
    by rw [hrKeepSh 31 (by decide)]; simp [s9, s8, s7, s6, s5],
    by rw [hrKeepSh 32 (by decide)]; simp [s9, s8, s7, s6],
    by rw [hrKeepSh 33 (by decide)]; simp [s9], hr2Sh⟩

theorem shiftTermPackEdits_runs
    {w root heap handle termHandle oldLastBran newLastBran vcLast ecLast termTok : ℕ}
    {oldLastF newLastF : MGraph} {p : Program} {ω : ℕ → Bool} {st : State}
    (h27 : st.regs 27 = root) (h28 : st.regs 28 = heap) (h29 : st.regs 29 = handle)
    (h32 : st.regs 32 = termHandle) (h33 : st.regs 33 = oldLastBran) (h2 : st.regs 2 = newLastBran)
    (hTermLe : termTok ≤ heap)
    (hOldBrW : termHandle + 1 + oldLastBran < termTok)
    (hNewBrW : termHandle + 1 + newLastBran < termTok)
    (hOldBaseLo : st.mem (termHandle + 1 + oldLastBran) + 4 ≤ termTok)
    (hNewBaseLo : st.mem (termHandle + 1 + newLastBran) + 4 ≤ termTok)
    (hOldGLo : st.mem (st.mem (termHandle + 1 + oldLastBran) + 1) + dynGraphSize vcLast ecLast ≤ termTok)
    (hNewGLo : st.mem (st.mem (termHandle + 1 + newLastBran) + 1) + dynGraphSize vcLast ecLast ≤ termTok)
    (hOldG : DynGraphAt st.mem (st.mem (st.mem (termHandle + 1 + oldLastBran) + 1)) vcLast ecLast oldLastF)
    (hNewG : DynGraphAt st.mem (st.mem (st.mem (termHandle + 1 + newLastBran) + 1)) vcLast ecLast newLastF)
    (hRoom : heap + 2 * (oldLastF.m + newLastF.m) < 2 ^ w) (hw7 : 7 < 2 ^ w) :
    ∃ out c edits, Runs w p ω shiftTermPackEdits st .normal out c ∧
      c ≤ 41 * (oldLastF.m + newLastF.m) + 120 ∧
      TreeEditDifference oldLastF.E newLastF.E edits ∧
      TreeEditsAt out.mem heap edits ∧
      out.regs 6 = heap ∧ out.regs 18 = edits.length ∧
      out.regs 27 = root ∧ out.regs 29 = handle ∧
      ∀ a, a < heap ∨ heap + 2 * edits.length ≤ a → out.mem a = st.mem a := by
  let oldBr := st.mem (termHandle + 1 + oldLastBran)
  let oldBase := st.mem (oldBr + 1)
  let newBr := st.mem (termHandle + 1 + newLastBran)
  let newBase := st.mem (newBr + 1)
  have hOldBaseLo' : oldBr + 4 ≤ termTok := hOldBaseLo
  have hNewBaseLo' : newBr + 4 ≤ termTok := hNewBaseLo
  have hOldGLo' : oldBase + dynGraphSize vcLast ecLast ≤ termTok := hOldGLo
  have hNewGLo' : newBase + dynGraphSize vcLast ecLast ≤ termTok := hNewGLo
  have hw0 : 0 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hOldVC : st.mem oldBase = vcLast := by simpa [dgVCapOff] using hOldG.2.2.2.1
  have hOldEC : st.mem (oldBase + 1) = ecLast := by simpa [dgECapOff] using hOldG.2.2.2.2.1
  have hOldM : st.mem (oldBase + 3) = oldLastF.m := by simpa [dgMOff] using hOldG.2.2.2.2.2.2.1
  have hNewM : st.mem (newBase + 3) = newLastF.m := by simpa [dgMOff] using hNewG.2.2.2.2.2.2.1
  have h7vc : 7 * vcLast < 2 ^ w := by simp only [dynGraphSize] at hOldGLo'; omega
  have holdEP : oldBase + 4 + 7 * vcLast < 2 ^ w := by simp only [dynGraphSize] at hOldGLo'; omega
  have holdEL : oldBase + 4 + 7 * vcLast + ecLast < 2 ^ w := by simp only [dynGraphSize] at hOldGLo'; omega
  have hnewEP : newBase + 4 + 7 * vcLast < 2 ^ w := by simp only [dynGraphSize] at hNewGLo'; omega
  have hnewEL : newBase + 4 + 7 * vcLast + ecLast < 2 ^ w := by simp only [dynGraphSize] at hNewGLo'; omega
  let p1 := { st with regs := Function.update st.regs 34 oldBr }
  let p2 := { p1 with regs := Function.update p1.regs 34 oldBase }
  let p3 := { p2 with regs := Function.update p2.regs 35 newBr }
  let p4 := { p3 with regs := Function.update p3.regs 35 newBase }
  let p5 := { p4 with regs := Function.update p4.regs 36 vcLast }
  let p6 := { p5 with regs := Function.update p5.regs 37 ecLast }
  let p7 := { p6 with regs := Function.update p6.regs 6 heap }
  let p8 := { p7 with regs := Function.update p7.regs 7 0 }
  let p9 := { p8 with regs := Function.update p8.regs 14 (dgEPresBase oldBase vcLast) }
  let p10 := { p9 with regs := Function.update p9.regs 10 (dgEListBase oldBase vcLast ecLast) }
  let p11 := { p10 with regs := Function.update p10.regs 11 oldLastF.m }
  let p12 := { p11 with regs := Function.update p11.regs 9 (dgEPresBase newBase vcLast) }
  let p13 := { p12 with regs := Function.update p12.regs 12 (dgEListBase newBase vcLast ecLast) }
  let p14 := { p13 with regs := Function.update p13.regs 13 newLastF.m }
  let p15 := { p14 with regs := Function.update p14.regs 18 0 }
  have r1 : Runs w p ω (.assign 34 (.load (.bin .add (.bin .add (.reg 32) (.const 1)) (.reg 33)))) st .normal p1 7 :=
    runs_assign_iff.mpr ⟨oldBr, by simp [Expr.eval, BinOp.eval, h32, h33, hw1,
      show termHandle + 1 < 2 ^ w by omega, show termHandle + 1 + oldLastBran < 2 ^ w by omega, oldBr],
      rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 34 (.load (.bin .add (.reg 34) (.const 1)))) p1 .normal p2 5 :=
    runs_assign_iff.mpr ⟨oldBase, by simp [Expr.eval, BinOp.eval, p1, hw1,
      show oldBr + 1 < 2 ^ w by omega, oldBase], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 35 (.load (.bin .add (.bin .add (.reg 32) (.const 1)) (.reg 2)))) p2 .normal p3 7 :=
    runs_assign_iff.mpr ⟨newBr, by simp [Expr.eval, BinOp.eval, p2, p1, h32, h2, hw1,
      show termHandle + 1 < 2 ^ w by omega, show termHandle + 1 + newLastBran < 2 ^ w by omega, newBr],
      rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 35 (.load (.bin .add (.reg 35) (.const 1)))) p3 .normal p4 5 :=
    runs_assign_iff.mpr ⟨newBase, by simp [Expr.eval, BinOp.eval, p3, p2, p1, hw1,
      show newBr + 1 < 2 ^ w by omega, newBase], rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 36 (.load (.reg 34))) p4 .normal p5 3 :=
    runs_assign_iff.mpr ⟨vcLast, by simp [Expr.eval, p4, p3, p2, p1, hOldVC], rfl, rfl, rfl⟩
  have r6 : Runs w p ω (.assign 37 (.load (.bin .add (.reg 34) (.const 1)))) p5 .normal p6 5 :=
    runs_assign_iff.mpr ⟨ecLast, by simp [Expr.eval, BinOp.eval, p5, p4, p3, p2, p1, hw1,
      show oldBase + 1 < 2 ^ w by omega, hOldEC], rfl, rfl, rfl⟩
  have r7 : Runs w p ω (.assign 6 (.reg 28)) p6 .normal p7 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, p6, p5, p4, p3, p2, p1, h28], rfl, rfl, rfl⟩
  have r8 : Runs w p ω (.assign 7 (.const 0)) p7 .normal p8 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hw0], rfl, rfl, rfl⟩
  have r9 : Runs w p ω (.assign 14 (.bin .add (.bin .add (.reg 34) (.const 4)) (.bin .mul (.const 7) (.reg 36))))
      p8 .normal p9 8 :=
    runs_assign_iff.mpr ⟨dgEPresBase oldBase vcLast, by simp [Expr.eval, BinOp.eval, p8, p7, p6, p5,
      p4, p3, p2, hw4, hw7, h7vc, show oldBase + 4 < 2 ^ w by omega, holdEP, dgEPresBase],
      rfl, rfl, rfl⟩
  have r10 : Runs w p ω (.assign 10 (.bin .add (.reg 14) (.reg 37))) p9 .normal p10 4 :=
    runs_assign_iff.mpr ⟨dgEListBase oldBase vcLast ecLast, by simp [Expr.eval, BinOp.eval, p9, p8, p7, p6,
      dgEPresBase, dgEListBase, holdEL], rfl, rfl, rfl⟩
  have r11 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 34) (.const 3)))) p10 .normal p11 5 :=
    runs_assign_iff.mpr ⟨oldLastF.m, by simp [Expr.eval, BinOp.eval, p10, p9, p8, p7, p6, p5, p4, p3,
      p2, p1, hw3, show oldBase + 3 < 2 ^ w by omega, hOldM], rfl, rfl, rfl⟩
  have r12 : Runs w p ω (.assign 9 (.bin .add (.bin .add (.reg 35) (.const 4)) (.bin .mul (.const 7) (.reg 36))))
      p11 .normal p12 8 :=
    runs_assign_iff.mpr ⟨dgEPresBase newBase vcLast, by simp [Expr.eval, BinOp.eval, p11, p10, p9, p8,
      p7, p6, p5, p4, hw4, hw7, h7vc, show newBase + 4 < 2 ^ w by omega, hnewEP, dgEPresBase],
      rfl, rfl, rfl⟩
  have r13 : Runs w p ω (.assign 12 (.bin .add (.reg 9) (.reg 37))) p12 .normal p13 4 :=
    runs_assign_iff.mpr ⟨dgEListBase newBase vcLast ecLast, by simp [Expr.eval, BinOp.eval, p12, p11,
      p10, p9, p8, p7, p6, dgEPresBase, dgEListBase, hnewEL], rfl, rfl, rfl⟩
  have r14 : Runs w p ω (.assign 13 (.load (.bin .add (.reg 35) (.const 3)))) p13 .normal p14 5 :=
    runs_assign_iff.mpr ⟨newLastF.m, by simp [Expr.eval, BinOp.eval, p13, p12, p11, p10, p9, p8, p7,
      p6, p5, p4, p3, p2, p1, hw3, show newBase + 3 < 2 ^ w by omega, hNewM], rfl, rfl, rfl⟩
  have r15 : Runs w p ω (.assign 18 (.const 0)) p14 .normal p15 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hw0], rfl, rfl, rfl⟩
  have hp15_6 : p15.regs 6 = heap := by simp [p15, p14, p13, p12, p11, p10, p9, p8, p7]
  obtain ⟨out, cPk, edits, rPk, hcPk, hDiff, hEdAt, hout6, hout18, houtRegs, houtFrame⟩ :=
    treeEditPackForFold_graphs (w := w) (p := p) (ω := ω) (st := p15)
      (oldBase := oldBase) (newBase := newBase) (oldVC := vcLast) (newVC := vcLast) (ec := ecLast)
      (G := oldLastF) (H := newLastF) hOldG hNewG (by omega) (by omega)
      (fun a _ ha2 => Or.inl (by rw [hp15_6]; omega))
      (fun a _ ha2 => Or.inl (by rw [hp15_6]; omega))
      (by simp [p15, p14, p13, p12, p11, p10, p9, p8])
      (by simp [p15, p14, p13, p12])
      (by simp [p15, p14, p13, p12, p11, p10])
      (by simp [p15, p14, p13, p12, p11])
      (by simp [p15, p14, p13])
      (by simp [p15, p14])
      (by simp [p15, p14, p13, p12, p11, p10, p9])
      hw1 (by rw [hp15_6]; exact hRoom) (by simp [p15]; omega)
  refine ⟨out, _, edits,
    runs_seq_iff.mpr (Or.inr ⟨p1, 7, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨p2, 5, _, r2,
    runs_seq_iff.mpr (Or.inr ⟨p3, 7, _, r3,
    runs_seq_iff.mpr (Or.inr ⟨p4, 5, _, r4,
    runs_seq_iff.mpr (Or.inr ⟨p5, 3, _, r5,
    runs_seq_iff.mpr (Or.inr ⟨p6, 5, _, r6,
    runs_seq_iff.mpr (Or.inr ⟨p7, 2, _, r7,
    runs_seq_iff.mpr (Or.inr ⟨p8, 2, _, r8,
    runs_seq_iff.mpr (Or.inr ⟨p9, 8, _, r9,
    runs_seq_iff.mpr (Or.inr ⟨p10, 4, _, r10,
    runs_seq_iff.mpr (Or.inr ⟨p11, 5, _, r11,
    runs_seq_iff.mpr (Or.inr ⟨p12, 8, _, r12,
    runs_seq_iff.mpr (Or.inr ⟨p13, 4, _, r13,
    runs_seq_iff.mpr (Or.inr ⟨p14, 5, _, r14,
    runs_seq_iff.mpr (Or.inr ⟨p15, 2, cPk, r15, rPk, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
      rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    by omega, hDiff, by rwa [hout6, hp15_6] at hEdAt,
    hout6.trans hp15_6, by simpa [p15] using hout18,
    (houtRegs 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (by simp [p15, p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1, h27]),
    (houtRegs 29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (by simp [p15, p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1, h29]),
    fun a ha => houtFrame a (by rw [hp15_6]; exact ha)⟩

theorem shiftTermSetupLoop_runs
    {w root handle treeHeap L editPtr nEdits rootGraph nV rootECap
      slots names slotThr edgeThr edgeRec offList inOff : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (h6 : st.regs 6 = editPtr) (h18 : st.regs 18 = nEdits)
    (h27 : st.regs 27 = root) (h29 : st.regs 29 = handle)
    (hTreeH : st.mem handle = treeHeap) (hL : st.mem (handle + 5) = L)
    (hRG : st.mem (root + 14) = rootGraph) (hNV : st.mem rootGraph = nV)
    (hREC : st.mem (rootGraph + 1) = rootECap)
    (hSl : st.mem (root + 6) = slots) (hNm : st.mem (root + 7) = names)
    (hST : st.mem (root + 8) = slotThr) (hET : st.mem (root + 9) = edgeThr)
    (hER : st.mem (root + 10) = edgeRec) (hOL : st.mem (root + 12) = offList)
    (hIO : st.mem (root + 13) = inOff)
    (hRootW : root + 16 < 2 ^ w) (hHandleW : handle + 6 < 2 ^ w)
    (hEditW : editPtr + 2 * nEdits < 2 ^ w) (hRGW : rootGraph + dynGraphSize nV rootECap < 2 ^ w) :
    ∃ out c, Runs w p ω shiftTermSetupLoop st .normal out c ∧ c ≤ 120 ∧ out.mem = st.mem ∧
      out.regs 0 = treeHeap ∧ out.regs 1 = root ∧ out.regs 2 = L ∧
      out.regs 3 = editPtr + 2 * nEdits ∧ out.regs 6 = editPtr ∧ out.regs 18 = nEdits ∧
      out.regs 9 = dgETailSlotBase rootGraph nV rootECap ∧
      out.regs 10 = dgEHeadSlotBase rootGraph nV rootECap ∧
      out.regs 11 = dgIntToExtBase rootGraph nV ∧
      out.regs 19 = slots ∧ out.regs 20 = names ∧ out.regs 22 = edgeRec ∧
      out.regs 23 = edgeThr ∧ out.regs 24 = slotThr ∧ out.regs 25 = offList ∧
      out.regs 26 = inOff := by
  have h16 : 16 < 2 ^ w := by omega
  have h7nv : 7 * nV < 2 ^ w := by simp only [dynGraphSize] at hRGW; omega
  have h4nv : 4 * nV < 2 ^ w := by simp only [dynGraphSize] at hRGW; omega
  have h3ec : 3 * rootECap < 2 ^ w := by simp only [dynGraphSize] at hRGW; omega
  have h4ec : 4 * rootECap < 2 ^ w := by simp only [dynGraphSize] at hRGW; omega
  have hrg4 : rootGraph + 4 < 2 ^ w := by simp only [dynGraphSize] at hRGW; omega
  have hrg7 : rootGraph + 4 + 7 * nV < 2 ^ w := by simp only [dynGraphSize] at hRGW; omega
  have hrgT : rootGraph + 4 + 7 * nV + 3 * rootECap < 2 ^ w := by simp only [dynGraphSize] at hRGW; omega
  have hrgH : rootGraph + 4 + 7 * nV + 4 * rootECap < 2 ^ w := by simp only [dynGraphSize] at hRGW; omega
  have hrgI : rootGraph + 4 + 4 * nV < 2 ^ w := by simp only [dynGraphSize] at hRGW; omega
  let q1 := { st with regs := Function.update st.regs 0 treeHeap }
  let q2 := { q1 with regs := Function.update q1.regs 1 root }
  let q3 := { q2 with regs := Function.update q2.regs 2 L }
  let q4 := { q3 with regs := Function.update q3.regs 3 (editPtr + 2 * nEdits) }
  let q5 := { q4 with regs := Function.update q4.regs 38 rootGraph }
  let q6 := { q5 with regs := Function.update q5.regs 39 nV }
  let q7 := { q6 with regs := Function.update q6.regs 40 rootECap }
  let q8 := { q7 with regs := Function.update q7.regs 41 (rootGraph + 4 + 7 * nV) }
  let q9 := { q8 with regs := Function.update q8.regs 9 (dgETailSlotBase rootGraph nV rootECap) }
  let q10 := { q9 with regs := Function.update q9.regs 10 (dgEHeadSlotBase rootGraph nV rootECap) }
  let q11 := { q10 with regs := Function.update q10.regs 11 (dgIntToExtBase rootGraph nV) }
  let q12 := { q11 with regs := Function.update q11.regs 19 slots }
  let q13 := { q12 with regs := Function.update q12.regs 20 names }
  let q14 := { q13 with regs := Function.update q13.regs 22 edgeRec }
  let q15 := { q14 with regs := Function.update q14.regs 23 edgeThr }
  let q16 := { q15 with regs := Function.update q15.regs 24 slotThr }
  let q17 := { q16 with regs := Function.update q16.regs 25 offList }
  let q18 := { q17 with regs := Function.update q17.regs 26 inOff }
  have r1 : Runs w p ω (.assign 0 (.load (.reg 29))) st .normal q1 3 :=
    runs_assign_iff.mpr ⟨treeHeap, by simp [Expr.eval, h29, hTreeH], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 1 (.reg 27)) q1 .normal q2 2 :=
    runs_assign_iff.mpr ⟨root, by simp [Expr.eval, q1, h27], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 2 (.load (.bin .add (.reg 29) (.const 5)))) q2 .normal q3 5 :=
    runs_assign_iff.mpr ⟨L, by simp [Expr.eval, BinOp.eval, q2, q1, h29, show 5 < 2 ^ w by omega,
      show handle + 5 < 2 ^ w by omega, hL], rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 3 (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 18)))) q3 .normal q4 6 :=
    runs_assign_iff.mpr ⟨editPtr + 2 * nEdits, by simp [Expr.eval, BinOp.eval, q3, q2, q1, h6, h18,
      show 2 < 2 ^ w by omega, show 2 * nEdits < 2 ^ w by omega, hEditW], rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 38 (.load (.bin .add (.reg 27) (.const 14)))) q4 .normal q5 5 :=
    runs_assign_iff.mpr ⟨rootGraph, by simp [Expr.eval, BinOp.eval, q4, q3, q2, q1, h27,
      show 14 < 2 ^ w by omega, show root + 14 < 2 ^ w by omega, hRG], rfl, rfl, rfl⟩
  have r6 : Runs w p ω (.assign 39 (.load (.reg 38))) q5 .normal q6 3 :=
    runs_assign_iff.mpr ⟨nV, by simp [Expr.eval, q5, q4, q3, q2, q1, hNV], rfl, rfl, rfl⟩
  have r7 : Runs w p ω (.assign 40 (.load (.bin .add (.reg 38) (.const 1)))) q6 .normal q7 5 :=
    runs_assign_iff.mpr ⟨rootECap, by simp [Expr.eval, BinOp.eval, q6, q5, q4, q3, q2, q1,
      show 1 < 2 ^ w by omega, show rootGraph + 1 < 2 ^ w by omega, hREC], rfl, rfl, rfl⟩
  have r8 : Runs w p ω (.assign 41 (.bin .add (.bin .add (.reg 38) (.const 4)) (.bin .mul (.const 7) (.reg 39))))
      q7 .normal q8 8 :=
    runs_assign_iff.mpr ⟨rootGraph + 4 + 7 * nV, by simp [Expr.eval, BinOp.eval, q7, q6, q5,
      show 4 < 2 ^ w by omega, show 7 < 2 ^ w by omega, hrg4, h7nv, hrg7], rfl, rfl, rfl⟩
  have r9 : Runs w p ω (.assign 9 (.bin .add (.reg 41) (.bin .mul (.const 3) (.reg 40)))) q8 .normal q9 6 :=
    runs_assign_iff.mpr ⟨dgETailSlotBase rootGraph nV rootECap, by simp [Expr.eval, BinOp.eval, q8, q7,
      show 3 < 2 ^ w by omega, h3ec, hrgT, dgETailSlotBase], rfl, rfl, rfl⟩
  have r10 : Runs w p ω (.assign 10 (.bin .add (.reg 41) (.bin .mul (.const 4) (.reg 40)))) q9 .normal q10 6 :=
    runs_assign_iff.mpr ⟨dgEHeadSlotBase rootGraph nV rootECap, by simp [Expr.eval, BinOp.eval, q9, q8, q7,
      show 4 < 2 ^ w by omega, h4ec, hrgH, dgEHeadSlotBase], rfl, rfl, rfl⟩
  have r11 : Runs w p ω (.assign 11 (.bin .add (.bin .add (.reg 38) (.const 4)) (.bin .mul (.const 4) (.reg 39))))
      q10 .normal q11 8 :=
    runs_assign_iff.mpr ⟨dgIntToExtBase rootGraph nV, by simp [Expr.eval, BinOp.eval, q10, q9, q8, q7, q6, q5,
      show 4 < 2 ^ w by omega, hrg4, h4nv, hrgI, dgIntToExtBase], rfl, rfl, rfl⟩
  have r12 : Runs w p ω (.assign 19 (.load (.bin .add (.reg 27) (.const 6)))) q11 .normal q12 5 :=
    runs_assign_iff.mpr ⟨slots, by simp [Expr.eval, BinOp.eval, q11, q10, q9, q8, q7, q6, q5, q4, q3, q2, q1,
      h27, show 6 < 2 ^ w by omega, show root + 6 < 2 ^ w by omega, hSl], rfl, rfl, rfl⟩
  have r13 : Runs w p ω (.assign 20 (.load (.bin .add (.reg 27) (.const 7)))) q12 .normal q13 5 :=
    runs_assign_iff.mpr ⟨names, by simp [Expr.eval, BinOp.eval, q12, q11, q10, q9, q8, q7, q6, q5, q4, q3, q2, q1,
      h27, show 7 < 2 ^ w by omega, show root + 7 < 2 ^ w by omega, hNm], rfl, rfl, rfl⟩
  have r14 : Runs w p ω (.assign 22 (.load (.bin .add (.reg 27) (.const 10)))) q13 .normal q14 5 :=
    runs_assign_iff.mpr ⟨edgeRec, by simp [Expr.eval, BinOp.eval, q13, q12, q11, q10, q9, q8, q7, q6, q5, q4, q3, q2, q1,
      h27, show 10 < 2 ^ w by omega, show root + 10 < 2 ^ w by omega, hER], rfl, rfl, rfl⟩
  have r15 : Runs w p ω (.assign 23 (.load (.bin .add (.reg 27) (.const 9)))) q14 .normal q15 5 :=
    runs_assign_iff.mpr ⟨edgeThr, by simp [Expr.eval, BinOp.eval, q14, q13, q12, q11, q10, q9, q8, q7, q6, q5, q4, q3, q2, q1,
      h27, show 9 < 2 ^ w by omega, show root + 9 < 2 ^ w by omega, hET], rfl, rfl, rfl⟩
  have r16 : Runs w p ω (.assign 24 (.load (.bin .add (.reg 27) (.const 8)))) q15 .normal q16 5 :=
    runs_assign_iff.mpr ⟨slotThr, by simp [Expr.eval, BinOp.eval, q15, q14, q13, q12, q11, q10, q9, q8, q7, q6, q5, q4, q3, q2, q1,
      h27, show 8 < 2 ^ w by omega, show root + 8 < 2 ^ w by omega, hST], rfl, rfl, rfl⟩
  have r17 : Runs w p ω (.assign 25 (.load (.bin .add (.reg 27) (.const 12)))) q16 .normal q17 5 :=
    runs_assign_iff.mpr ⟨offList, by simp [Expr.eval, BinOp.eval, q16, q15, q14, q13, q12, q11, q10, q9, q8, q7, q6, q5, q4, q3, q2, q1,
      h27, show 12 < 2 ^ w by omega, show root + 12 < 2 ^ w by omega, hOL], rfl, rfl, rfl⟩
  have r18 : Runs w p ω (.assign 26 (.load (.bin .add (.reg 27) (.const 13)))) q17 .normal q18 5 :=
    runs_assign_iff.mpr ⟨inOff, by simp [Expr.eval, BinOp.eval, q17, q16, q15, q14, q13, q12, q11, q10, q9, q8, q7, q6, q5, q4, q3, q2, q1,
      h27, show 13 < 2 ^ w by omega, show root + 13 < 2 ^ w by omega, hIO], rfl, rfl, rfl⟩
  refine ⟨q18, _,
    runs_seq_iff.mpr (Or.inr ⟨q1, 3, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨q2, 2, _, r2,
    runs_seq_iff.mpr (Or.inr ⟨q3, 5, _, r3,
    runs_seq_iff.mpr (Or.inr ⟨q4, 6, _, r4,
    runs_seq_iff.mpr (Or.inr ⟨q5, 5, _, r5,
    runs_seq_iff.mpr (Or.inr ⟨q6, 3, _, r6,
    runs_seq_iff.mpr (Or.inr ⟨q7, 5, _, r7,
    runs_seq_iff.mpr (Or.inr ⟨q8, 8, _, r8,
    runs_seq_iff.mpr (Or.inr ⟨q9, 6, _, r9,
    runs_seq_iff.mpr (Or.inr ⟨q10, 6, _, r10,
    runs_seq_iff.mpr (Or.inr ⟨q11, 8, _, r11,
    runs_seq_iff.mpr (Or.inr ⟨q12, 5, _, r12,
    runs_seq_iff.mpr (Or.inr ⟨q13, 5, _, r13,
    runs_seq_iff.mpr (Or.inr ⟨q14, 5, _, r14,
    runs_seq_iff.mpr (Or.inr ⟨q15, 5, _, r15,
    runs_seq_iff.mpr (Or.inr ⟨q16, 5, _, r16,
    runs_seq_iff.mpr (Or.inr ⟨q17, 5, 5, r17, r18, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
      rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    by omega, rfl,
    by simp [q18, q17, q16, q15, q14, q13, q12, q11, q10, q9, q8, q7, q6, q5, q4, q3, q2, q1],
    by simp [q18, q17, q16, q15, q14, q13, q12, q11, q10, q9, q8, q7, q6, q5, q4, q3, q2],
    by simp [q18, q17, q16, q15, q14, q13, q12, q11, q10, q9, q8, q7, q6, q5, q4, q3],
    by simp [q18, q17, q16, q15, q14, q13, q12, q11, q10, q9, q8, q7, q6, q5, q4],
    by simp [q18, q17, q16, q15, q14, q13, q12, q11, q10, q9, q8, q7, q6, q5, q4, q3, q2, q1, h6],
    by simp [q18, q17, q16, q15, q14, q13, q12, q11, q10, q9, q8, q7, q6, q5, q4, q3, q2, q1, h18],
    by simp [q18, q17, q16, q15, q14, q13, q12, q11, q10, q9],
    by simp [q18, q17, q16, q15, q14, q13, q12, q11, q10],
    by simp [q18, q17, q16, q15, q14, q13, q12, q11],
    by simp [q18, q17, q16, q15, q14, q13, q12],
    by simp [q18, q17, q16, q15, q14, q13],
    by simp [q18, q17, q16, q15, q14],
    by simp [q18, q17, q16, q15],
    by simp [q18, q17, q16],
    by simp [q18, q17],
    by simp [q18]⟩

end MinCostFlow.MinRatio
