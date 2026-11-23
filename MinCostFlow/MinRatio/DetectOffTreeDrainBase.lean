module

public import MinCostFlow.MinRatio.SolverRep
public import MinCostFlow.MinRatio.DetectReset
public import MinCostFlow.Num.IsNegative
import WordRAM.Tactic

/-!
# Off-tree pending list drain definitions and helpers for `Detect`

Defines `detectOffTreeDrainStep`, `detectOffTreeDrainLoad`, `detectOffTreeDrainBody`,
the off-tree readiness predicate `IsOffTreeReady`, the loop invariant `DrainInv`, and
the directory-load and membership helpers used by `DetectOffTreeDrain`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine

/-- One iteration of the off-tree ready-list drain (`reg 14 = j`). -/
@[expose] def detectOffTreeDrainStep (isNeg reset : ℕ) : Stmt :=
  .assign 15 (.load (.bin .add (.reg 12) (.reg 14))) ;;
  .store (.bin .add (.reg 13) (.reg 15)) (.const 0) ;;
  .assign 16 (.load (.bin .add (.reg 7) (.reg 15))) ;;
  .cond (.bin .lt (.reg 16) (.reg 2))
    (.cond (.bin .eq (.load (.bin .add (.reg 6) (.reg 16))) (.reg 15))
      (.cond (.load (.bin .add (.reg 8) (.reg 15)))
        .nop
        (.assign 17 (.load (.bin .add (.reg 10) (.reg 15))) ;;
         .assign 18 (.bin .add (.bin .add (.reg 17) (.const 2))
           (.bin .mul (.const 3) (.reg 5))) ;;
         .call 19 isNeg [.reg 18, .reg 5] ;;
         .cond (.reg 19)
           .nop
           (.store (.reg 3) (.reg 16) ;;
            .assign 3 (.bin .add (.reg 3) (.const 1)) ;;
            .assign 20 (.load (.bin .add (.reg 9) (.reg 15))) ;;
            .call 21 reset [.reg 17, .reg 20, .reg 5, .reg 4] ;;
            .store (.bin .add (.reg 10) (.reg 15)) (.reg 4) ;;
            .assign 4 (.reg 21))))
      .nop)
    .nop

/-- Load the 8 directory pointers used by the off-tree drain loop. -/
@[expose] def detectOffTreeDrainLoad : Stmt :=
  .assign 6 (.load (.bin .add (.reg 0) (.const 3))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const 4))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const 6))) ;;
  .assign 9 (.load (.bin .add (.reg 0) (.const 9))) ;;
  .assign 10 (.load (.bin .add (.reg 0) (.const 10))) ;;
  .assign 11 (.load (.bin .add (.reg 0) (.const 11))) ;;
  .assign 12 (.load (.bin .add (.reg 0) (.const 12))) ;;
  .assign 13 (.load (.bin .add (.reg 0) (.const 13)))

/-- Complete deterministic off-tree pending-list drain for `Detect`. -/
@[expose] def detectOffTreeDrainBody (isNeg reset : ℕ) : Stmt :=
  detectOffTreeDrainLoad ;;
  forRange 14 (.const 0) (.reg 11) (detectOffTreeDrainStep isNeg reset) ;;
  .store (.bin .add (.reg 0) (.const 11)) (.const 0)

theorem detectOffTreeDrainBody_noRand (isNeg reset : ℕ) :
    (detectOffTreeDrainBody isNeg reset).NoRand := by
  simp [detectOffTreeDrainBody, detectOffTreeDrainLoad, detectOffTreeDrainStep,
    forRange, forUp, Stmt.NoRand]

/-- Predicate characterizing an internal edge ID `ei` that is live, off-tree, and ready
to be reported in `algorithm2_detect cfg model`. -/
@[expose] def IsOffTreeReady {cfg : Alg2Config} (model : Alg2State cfg) (ei : ℕ) : Prop :=
  let e := model.intToExt ei
  e ∈ model.extG.E ∧ model.extToInt e = ei ∧
    ei ∉ model.chain.toTreeChain.chainTree.E ∧ e ∈ (algorithm2_detect cfg model).1

/-- Per-iteration cost constant for `detectOffTreeDrainStep` (excluding `forRange` loop control). -/
@[expose] def detectOffTreeStepBudget (L : ℕ) : ℕ := 87 * L + 200

/-- Per-entry potential unit sufficient to pay for draining one `offReadyList` entry
(including `forRange` loop control overhead). -/
@[expose] def detectOffTreeDrainUnit (L : ℕ) : ℕ := 87 * L + 220

/-- Loop invariant for `detectOffTreeDrainBody` after processing the first `j` entries of
`offReadyList[0 .. tok.offReadyCount)`. -/
@[expose] def DrainInv {cfg : Alg2Config} {L P m : ℕ} {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)}
    (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (mem₀ : ℕ → ℕ)
    (root base heap₀ : ℕ) (treeRep : List ℕ) (j : ℕ) (s : State) : Prop :=
  ∃ (offRep : List ℕ) (curHeap : ℕ),
    s.regs 0 = root ∧ s.regs 1 = base ∧ s.regs 2 = m ∧
    s.regs 3 = base + 1 + (treeRep ++ offRep).length ∧
    s.regs 4 = curHeap ∧ s.regs 5 = L ∧
    s.regs 6 = tok.forward ∧ s.regs 7 = tok.inverse ∧ s.regs 8 = tok.slots ∧
    s.regs 9 = tok.edgeThresholds ∧ s.regs 10 = tok.edgeRecords ∧
    s.regs 11 = tok.offReadyCount ∧ s.regs 12 = tok.offReadyList ∧ s.regs 13 = tok.inOffReady ∧
    s.regs 14 = j ∧
    offRep.length ≤ j ∧
    (treeRep ++ offRep).length ≤ m ∧
    (treeRep ++ offRep).Nodup ∧
    ListAt s.mem (base + 1) (treeRep ++ offRep) ∧
    heap₀ ≤ curHeap ∧ curHeap ≤ heap₀ + j * (2 + 4 * L) ∧
    ZeroFrom s.mem curHeap ∧
    (∀ k < j, s.mem (tok.inOffReady + mem₀ (tok.offReadyList + k)) = 0) ∧
    (∀ k, j ≤ k → k < tok.offReadyCount →
      s.mem (tok.inOffReady + mem₀ (tok.offReadyList + k)) = 1) ∧
    (∀ e < tok.intCap, mem₀ (tok.inOffReady + e) = 0 → s.mem (tok.inOffReady + e) = 0) ∧
    (∀ e, e ∈ offRep ↔
      ∃ k < j, IsOffTreeReady model (mem₀ (tok.offReadyList + k)) ∧
        e = model.intToExt (mem₀ (tok.offReadyList + k))) ∧
    (∀ e ∈ model.extG.E,
      let ei := model.extToInt e
      ei ∉ model.chain.toTreeChain.chainTree.E →
      if e ∈ offRep then
        heap₀ ≤ s.mem (tok.edgeRecords + ei) ∧
        s.mem (tok.edgeRecords + ei) + (2 + 4 * L) ≤ curHeap ∧
        ∃ val : PathEdgeValue,
          PathEdgeAt s.mem (s.mem (tok.edgeRecords + ei)) 4 L (some val) ∧
          val.forward = true ∧
          (val.originalFlow : ℝ) / (2 : ℝ) ^ P = model.flow e ∧
          val.detector = -detectorThreshold P cfg.ε (model.extℓ e) ∧
          (val.originalGradient : ℝ) / (2 : ℝ) ^ P = model.extg e ∧
          (val.length : ℝ) / (2 : ℝ) ^ P = model.extℓ e
      else
        s.mem (tok.edgeRecords + ei) = mem₀ (tok.edgeRecords + ei) ∧
        ∀ x < 2 + 4 * L, s.mem (mem₀ (tok.edgeRecords + ei) + x) =
          mem₀ (mem₀ (tok.edgeRecords + ei) + x)) ∧
    (∀ a < heap₀,
      (a < base + 1 ∨ base + 1 + m ≤ a) →
      (a < tok.inOffReady ∨ tok.inOffReady + tok.intCap ≤ a) →
      (a < tok.edgeRecords ∨ tok.edgeRecords + tok.intCap ≤ a) →
      s.mem a = mem₀ a) ∧
    (∀ e₁ ∈ offRep, ∀ e₂ ∈ offRep, e₁ ≠ e₂ →
      s.mem (tok.edgeRecords + model.extToInt e₁) + (2 + 4 * L) ≤
          s.mem (tok.edgeRecords + model.extToInt e₂) ∨
        s.mem (tok.edgeRecords + model.extToInt e₂) + (2 + 4 * L) ≤
          s.mem (tok.edgeRecords + model.extToInt e₁))

/-- Loading the 8 directory pointers in `detectOffTreeDrainLoad` takes 47 steps. -/
theorem detectOffTreeDrainLoad_runs {w root : ℕ} {p : Program} {st : State} {ω : ℕ → Bool}
    {forward inverse slots edgeThresholds edgeRecords offReadyCount offReadyList inOffReady : ℕ}
    (h0 : st.regs 0 = root) (hw13 : 13 < 2 ^ w) (hroot13 : root + 13 < 2 ^ w)
    (hm3 : st.mem (root + 3) = forward) (hm4 : st.mem (root + 4) = inverse)
    (hm6 : st.mem (root + 6) = slots) (hm9 : st.mem (root + 9) = edgeThresholds)
    (hm10 : st.mem (root + 10) = edgeRecords) (hm11 : st.mem (root + 11) = offReadyCount)
    (hm12 : st.mem (root + 12) = offReadyList) (hm13 : st.mem (root + 13) = inOffReady) :
    ∃ mid,
      Runs w p ω detectOffTreeDrainLoad st .normal mid 47 ∧
      mid.mem = st.mem ∧ mid.pos = st.pos ∧
      (∀ r ≤ 5, mid.regs r = st.regs r) ∧
      mid.regs 6 = forward ∧ mid.regs 7 = inverse ∧ mid.regs 8 = slots ∧
      mid.regs 9 = edgeThresholds ∧ mid.regs 10 = edgeRecords ∧
      mid.regs 11 = offReadyCount ∧ mid.regs 12 = offReadyList ∧ mid.regs 13 = inOffReady := by
  let s1 := { st with regs := Function.update st.regs 6 forward }
  let s2 := { s1 with regs := Function.update s1.regs 7 inverse }
  let s3 := { s2 with regs := Function.update s2.regs 8 slots }
  let s4 := { s3 with regs := Function.update s3.regs 9 edgeThresholds }
  let s5 := { s4 with regs := Function.update s4.regs 10 edgeRecords }
  let s6 := { s5 with regs := Function.update s5.regs 11 offReadyCount }
  let s7 := { s6 with regs := Function.update s6.regs 12 offReadyList }
  let s8 := { s7 with regs := Function.update s7.regs 13 inOffReady }
  have r1 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 0) (.const 3)))) st .normal s1 5 :=
    runs_assign_iff.mpr ⟨forward, by
      simp [Expr.eval, BinOp.eval, h0, show 3 < 2 ^ w by omega, show root + 3 < 2 ^ w by omega, hm3],
      rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 0) (.const 4)))) s1 .normal s2 5 :=
    runs_assign_iff.mpr ⟨inverse, by
      simp [Expr.eval, BinOp.eval, s1, h0, show 4 < 2 ^ w by omega, show root + 4 < 2 ^ w by omega, hm4],
      rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 0) (.const 6)))) s2 .normal s3 5 :=
    runs_assign_iff.mpr ⟨slots, by
      simp [Expr.eval, BinOp.eval, s2, s1, h0, show 6 < 2 ^ w by omega, show root + 6 < 2 ^ w by omega, hm6],
      rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 0) (.const 9)))) s3 .normal s4 5 :=
    runs_assign_iff.mpr ⟨edgeThresholds, by
      simp [Expr.eval, BinOp.eval, s3, s2, s1, h0, show 9 < 2 ^ w by omega, show root + 9 < 2 ^ w by omega, hm9],
      rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 0) (.const 10)))) s4 .normal s5 5 :=
    runs_assign_iff.mpr ⟨edgeRecords, by
      simp [Expr.eval, BinOp.eval, s4, s3, s2, s1, h0, show 10 < 2 ^ w by omega, show root + 10 < 2 ^ w by omega, hm10],
      rfl, rfl, rfl⟩
  have r6 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 0) (.const 11)))) s5 .normal s6 5 :=
    runs_assign_iff.mpr ⟨offReadyCount, by
      simp [Expr.eval, BinOp.eval, s5, s4, s3, s2, s1, h0, show 11 < 2 ^ w by omega, show root + 11 < 2 ^ w by omega, hm11],
      rfl, rfl, rfl⟩
  have r7 : Runs w p ω (.assign 12 (.load (.bin .add (.reg 0) (.const 12)))) s6 .normal s7 5 :=
    runs_assign_iff.mpr ⟨offReadyList, by
      simp [Expr.eval, BinOp.eval, s6, s5, s4, s3, s2, s1, h0, show 12 < 2 ^ w by omega, show root + 12 < 2 ^ w by omega, hm12],
      rfl, rfl, rfl⟩
  have r8 : Runs w p ω (.assign 13 (.load (.bin .add (.reg 0) (.const 13)))) s7 .normal s8 5 :=
    runs_assign_iff.mpr ⟨inOffReady, by
      simp [Expr.eval, BinOp.eval, s7, s6, s5, s4, s3, s2, s1, h0, hw13, hroot13, hm13],
      rfl, rfl, rfl⟩
  refine ⟨s8, ?_, rfl, rfl, fun r hr => by
    simp [s8, s7, s6, s5, s4, s3, s2, s1,
      Function.update_of_ne (show r ≠ 13 by omega),
      Function.update_of_ne (show r ≠ 12 by omega),
      Function.update_of_ne (show r ≠ 11 by omega),
      Function.update_of_ne (show r ≠ 10 by omega),
      Function.update_of_ne (show r ≠ 9 by omega),
      Function.update_of_ne (show r ≠ 8 by omega),
      Function.update_of_ne (show r ≠ 7 by omega),
      Function.update_of_ne (show r ≠ 6 by omega)],
    by simp [s8, s7, s6, s5, s4, s3, s2, s1], by simp [s8, s7, s6, s5, s4, s3, s2],
    by simp [s8, s7, s6, s5, s4, s3], by simp [s8, s7, s6, s5, s4],
    by simp [s8, s7, s6, s5], by simp [s8, s7, s6], by simp [s8, s7], by simp [s8]⟩
  exact runs_seq_iff.mpr (Or.inr ⟨s1, 5, 41, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 5, 35, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 5, 29, r3,
    runs_seq_iff.mpr (Or.inr ⟨s4, 5, 23, r4,
    runs_seq_iff.mpr (Or.inr ⟨s5, 5, 17, r5,
    runs_seq_iff.mpr (Or.inr ⟨s6, 5, 11, r6,
    runs_seq_iff.mpr (Or.inr ⟨s7, 5, 5, r7, r8, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)

/-- Under `FreshTablesAt`, `e < m ∧ forward[e] = ei` (with `e = inverse[ei]`) holds iff
`model.intToExt ei` is live and maps back to `ei`. -/
theorem live_offtree_iff {cfg : Alg2Config} {model : Alg2State cfg} {m intCap : ℕ}
    {mem : ℕ → ℕ} {forward inverse freshCounter : ℕ}
    (hfreshTab : FreshTablesAt mem forward inverse freshCounter m intCap
      model.extToInt model.intToExt model.nextFresh)
    (hExtRange : ∀ e < m, e ∈ model.extG.E)
    (hExtLt : ∀ e ∈ model.extG.E, e < m)
    {ei : ℕ} (heiCap : ei < intCap) :
    let e := mem (inverse + ei)
    (e < m ∧ mem (forward + e) = ei) ↔
      (model.intToExt ei ∈ model.extG.E ∧ model.extToInt (model.intToExt ei) = ei) := by
  dsimp only
  have hinv : mem (inverse + ei) = model.intToExt ei := hfreshTab.2.2 ei heiCap
  rw [hinv]
  constructor
  · rintro ⟨hlt, hfwd⟩
    have heE : model.intToExt ei ∈ model.extG.E := hExtRange _ hlt
    rw [hfreshTab.2.1 _ hlt] at hfwd
    exact ⟨heE, hfwd⟩
  · rintro ⟨heE, he2i⟩
    have hlt : model.intToExt ei < m := hExtLt _ heE
    exact ⟨hlt, (hfreshTab.2.1 _ hlt).trans he2i⟩

/-- Cardinality bound `(xs ++ [e]).length ≤ m` for a duplicate-free list of edges in `E ⊆ [0, m)`. -/
theorem nodup_snoc_length_le {m e : ℕ} {E : Finset ℕ} {xs : List ℕ}
    (hExtLt : ∀ x ∈ E, x < m) (hsub : ∀ x ∈ xs, x ∈ E) (hnd : xs.Nodup)
    (heE : e ∈ E) (heNot : e ∉ xs) :
    (xs ++ [e]).length ≤ m := by
  have hnd' : (xs ++ [e]).Nodup := by
    rw [List.nodup_append]
    exact ⟨hnd, List.nodup_singleton e, fun a ha b hb => by
      simp only [List.mem_singleton] at hb; subst hb; intro h; exact heNot (h ▸ ha)⟩
  have hcard : (xs ++ [e]).length = (xs ++ [e]).toFinset.card :=
    (List.toFinset_card_of_nodup hnd').symm
  rw [hcard]
  have hsubR : (xs ++ [e]).toFinset ⊆ Finset.range m := by
    intro x hx
    rw [List.mem_toFinset, List.mem_append, List.mem_singleton] at hx
    rcases hx with h1 | rfl
    · exact Finset.mem_range.mpr (hExtLt x (hsub x h1))
    · exact Finset.mem_range.mpr (hExtLt x heE)
  exact le_trans (Finset.card_le_card hsubR) (by simp)

/-- Two `PathEdgeAt` witnesses at the same address agree on `originalFlow`. -/
theorem pathEdgeAt_originalFlow_eq {mem : ℕ → ℕ} {a h L : ℕ} {v₁ v₂ : PathEdgeValue}
    (h1 : PathEdgeAt mem a h L (some v₁)) (h2 : PathEdgeAt mem a h L (some v₂)) :
    v₁.originalFlow = v₂.originalFlow := by
  have hdir : (if v₁.forward then 1 else 0) = (if v₂.forward then 1 else 0) :=
    h1.2.1.symm.trans h2.2.1
  have hfl : v₁.flow = v₂.flow := h1.2.2.2.2.1.2.symm.trans h2.2.2.2.2.1.2
  unfold PathEdgeValue.originalFlow
  cases hd1 : v₁.forward <;> cases hd2 : v₂.forward <;> simp_all

/-- Non-emitting step closure for `DrainInv`: when `ei = mem₀ (offReadyList + j)` is not
off-tree ready and `st` clears only `inOffReady[ei]` while preserving `regs 0..14`,
`DrainInv` advances from `j` to `j + 1`. -/
theorem drainStep_skip_inv {cfg : Alg2Config} {L P m V psi k epsExp drainUnit : ℕ}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} {model : Alg2State cfg} {tok : SolverToken cfg L Rcore}
    {mem₀ : ℕ → ℕ} {root base heap₀ j : ℕ} {treeRep : List ℕ} {s st : State}
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem₀)
    (hbelow : ∀ a, tok.tag a ≠ 0 → tok.tag a ≠ 16 → a < base)
    (hbaseHeap : base + 1 + m ≤ heap₀)
    (hj : j < tok.offReadyCount)
    (hInv : DrainInv (P := P) (m := m) model tok mem₀ root base heap₀ treeRep j s)
    (hmemSt : st.mem = Function.update s.mem (tok.inOffReady + mem₀ (tok.offReadyList + j)) 0)
    (hregsSt : ∀ r ≤ 14, st.regs r = s.regs r)
    (hnotReady : ¬ IsOffTreeReady model (mem₀ (tok.offReadyList + j))) :
    DrainInv (P := P) (m := m) model tok mem₀ root base heap₀ treeRep (j + 1)
      { st with regs := Function.update st.regs 14 (j + 1) } ∧ st.regs 14 = j := by
  obtain ⟨offRep, curHeap, hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13,
    hr14, hoffLen, htotLen, hnd, hlist, hcurLo, hcurHi, hzCur, hclr, hkeep1, hzero0,
    hoffIff, hrecInv, hframe0, hsepR⟩ := hInv
  obtain ⟨_, _, _, _, _, _, _, _, _, hoffInv, _, _, _, hedgeAcc, _, _, _, _, _, htags⟩ := hrep
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, t13, _, t15, _, t1718, _, _, _⟩ := htags
  let ei := mem₀ (tok.offReadyList + j)
  have heiCap : ei < tok.intCap := (hoffInv.2.1 j hj).1
  have hltB {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) (hv16 : v ≠ 16 := by decide) : a < base :=
    hbelow a (ht ▸ hv) (ht ▸ hv16)
  refine ⟨⟨offRep, curHeap,
    by dsimp only; rw [Function.update_of_ne (by decide), hregsSt 0 (by decide)]; exact hr0,
    by dsimp only; rw [Function.update_of_ne (by decide), hregsSt 1 (by decide)]; exact hr1,
    by dsimp only; rw [Function.update_of_ne (by decide), hregsSt 2 (by decide)]; exact hr2,
    by dsimp only; rw [Function.update_of_ne (by decide), hregsSt 3 (by decide)]; exact hr3,
    by dsimp only; rw [Function.update_of_ne (by decide), hregsSt 4 (by decide)]; exact hr4,
    by dsimp only; rw [Function.update_of_ne (by decide), hregsSt 5 (by decide)]; exact hr5,
    by dsimp only; rw [Function.update_of_ne (by decide), hregsSt 6 (by decide)]; exact hr6,
    by dsimp only; rw [Function.update_of_ne (by decide), hregsSt 7 (by decide)]; exact hr7,
    by dsimp only; rw [Function.update_of_ne (by decide), hregsSt 8 (by decide)]; exact hr8,
    by dsimp only; rw [Function.update_of_ne (by decide), hregsSt 9 (by decide)]; exact hr9,
    by dsimp only; rw [Function.update_of_ne (by decide), hregsSt 10 (by decide)]; exact hr10,
    by dsimp only; rw [Function.update_of_ne (by decide), hregsSt 11 (by decide)]; exact hr11,
    by dsimp only; rw [Function.update_of_ne (by decide), hregsSt 12 (by decide)]; exact hr12,
    by dsimp only; rw [Function.update_of_ne (by decide), hregsSt 13 (by decide)]; exact hr13,
    by simp, by omega, htotLen, hnd, ?_, hcurLo, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    by rw [hregsSt 14 (by decide)]; exact hr14⟩
  · intro idx hidx
    have hne : base + 1 + idx ≠ tok.inOffReady + ei := by
      have := hltB (t15 ei heiCap) (by decide); omega
    simpa [hmemSt, ei, Function.update_of_ne hne] using hlist idx hidx
  · have : j * (2 + 4 * L) ≤ (j + 1) * (2 + 4 * L) := Nat.mul_le_mul_right _ (Nat.le_succ j)
    omega
  · intro a ha
    have hne : a ≠ tok.inOffReady + ei := by
      have := hltB (t15 ei heiCap) (by decide); omega
    simpa [hmemSt, ei, Function.update_of_ne hne] using hzCur a ha
  · intro k hk
    by_cases hkj : k = j
    · subst hkj; simp [hmemSt]
    · have hklt : k < j := by omega
      have hne : tok.inOffReady + mem₀ (tok.offReadyList + k) ≠ tok.inOffReady + ei := by
        intro heq; exact hoffInv.2.2.1 k (lt_trans hklt hj) j hj hkj (by omega)
      simpa [hmemSt, ei, Function.update_of_ne hne] using hclr k hklt
  · intro k hklo hkhi
    have hne : tok.inOffReady + mem₀ (tok.offReadyList + k) ≠ tok.inOffReady + ei := by
      intro heq; exact hoffInv.2.2.1 k hkhi j hj (by omega) (by omega)
    simpa [hmemSt, ei, Function.update_of_ne hne] using hkeep1 k (by omega) hkhi
  · intro x hx h0x
    by_cases hxei : x = ei
    · subst hxei; simp [hmemSt, ei]
    · simpa [hmemSt, ei, Function.update_of_ne (show tok.inOffReady + x ≠ tok.inOffReady + ei by omega)]
        using hzero0 x hx h0x
  · intro x; rw [hoffIff x]
    constructor
    · rintro ⟨k, hk, h1, h2⟩; exact ⟨k, by omega, h1, h2⟩
    · rintro ⟨k, hk, h1, h2⟩
      by_cases hkj : k = j
      · subst hkj; exact absurd h1 hnotReady
      · exact ⟨k, by omega, h1, h2⟩
  · intro x hx; dsimp only; intro hnotT
    have hrec := hrecInv x hx hnotT
    have hne13 : tok.edgeRecords + model.extToInt x ≠ tok.inOffReady + ei := fun h => by
      have h1 := t13 (model.extToInt x) (hedgeAcc.1 x hx).1
      have h2 := t15 ei heiCap; rw [h] at h1; omega
    split_ifs at hrec ⊢ with hxIn
    · obtain ⟨hlo, hhi, val, hpa, hfl, hdet, hgrad, hlen⟩ := hrec
      refine ⟨by simpa [hmemSt, ei, Function.update_of_ne hne13] using hlo,
        by simpa [hmemSt, ei, Function.update_of_ne hne13] using hhi,
        val, ?_, hfl, hdet, hgrad, hlen⟩
      rw [show st.mem (tok.edgeRecords + model.extToInt x) = s.mem (tok.edgeRecords + model.extToInt x) from
        by simp [hmemSt, ei, Function.update_of_ne hne13]]
      refine hpa.congr (fun a halo hahi => ?_)
      have hne : a ≠ tok.inOffReady + ei := by have := hltB (t15 ei heiCap) (by decide); omega
      simp [hmemSt, ei, Function.update_of_ne hne]
    · obtain ⟨heqP, hcell⟩ := hrec
      refine ⟨by simpa [hmemSt, ei, Function.update_of_ne hne13] using heqP, fun idx hidx => ?_⟩
      have hne : mem₀ (tok.edgeRecords + model.extToInt x) + idx ≠ tok.inOffReady + ei := fun h => by
        have h1 := (t1718 x hx).2 hnotT idx hidx
        have h2 := t15 ei heiCap; rw [h] at h1; omega
      simpa [hmemSt, ei, Function.update_of_ne hne] using hcell idx hidx
  · intro a ha h1 h2 h3
    have hne : a ≠ tok.inOffReady + ei := by omega
    simpa [hmemSt, ei, Function.update_of_ne hne] using hframe0 a ha h1 h2 h3
  · intro x hx y hy hxy
    have hpt (z : ℕ) (hz : z ∈ offRep) : st.mem (tok.edgeRecords + model.extToInt z) =
        s.mem (tok.edgeRecords + model.extToInt z) := by
      have hzE : z ∈ model.extG.E := by obtain ⟨_, _, hR, rfl⟩ := (hoffIff z).mp hz; exact hR.1
      have hne13 : tok.edgeRecords + model.extToInt z ≠ tok.inOffReady + ei := fun h => by
        have h1 := t13 (model.extToInt z) (hedgeAcc.1 z hzE).1
        have h2 := t15 ei heiCap; rw [h] at h1; omega
      simp [hmemSt, ei, Function.update_of_ne hne13]
    rw [hpt x hx, hpt y hy]
    exact hsepR x hx y hy hxy

end MinCostFlow.MinRatio
