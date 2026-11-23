module

public import MinCostFlow.DynSpanner.Program.GraphTranslateHelpersCopy

/-!
# The vertex phase of the forward translation

Part 2 of `GraphTranslateHelpers.lean`: the programs of the preparation phases, their
invariants, and the proof of the vertex phase (`gtForwardDyn_prepVPhase`). See
`GraphTranslateHelpers.lean` for the overview.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner

@[expose] public section


/-- Scratch word budget required by `gtForwardDynStmt`. -/
def gtFwdDynScratchLen (nJ mJ rawEsLen : ℕ) : ℕ :=
  3 * nJ + 6 * mJ + 5 * rawEsLen

/-- Vertex extraction and sorting phase of `gtForwardDynPrepStmt`. -/
def gtForwardDynPrepVStmt (bGT : ℕ) : Stmt :=
  .assign 5 (.load (.bin .add (.reg 1) (.const dgVCapOff))) ;;
  .assign 6 (.load (.bin .add (.reg 1) (.const dgECapOff))) ;;
  .assign 7 (.load (.bin .add (.reg 1) (.const dgNOff))) ;;
  .assign 8 (.load (.bin .add (.reg 1) (.const dgMOff))) ;;
  .assign 9 (.reg 3) ;;
  .assign 10 (.bin .add (.reg 9) (.reg 7)) ;;
  .assign 11 (.bin .add (.reg 10) (.reg 8)) ;;
  .assign 12 (.bin .add (.reg 11) (.reg 8)) ;;
  .assign 13 (.bin .add (.reg 12) (.reg 8)) ;;
  .assign 14 (.bin .add (.reg 1) (.bin .add (.const 4) (.reg 5))) ;;
  forRange 15 (.const 0) (.reg 7)
    (.store (.bin .add (.reg 13) (.reg 15)) (.load (.bin .add (.reg 14) (.reg 15)))) ;;
  .call 15 (bGT + gtIdxSortDedup) [.reg 13, .reg 7, .reg 9, .bin .add (.reg 13) (.reg 7)]

/-- Edge copy and sort-dedup sub-phase of `gtForwardDynPrepEStmt`. -/
def gtForwardDynPrepE1Stmt (bGT : ℕ) : Stmt :=
  .assign 14 (.bin .add (.reg 1) (.bin .add (.const 4)
    (.bin .add (.bin .mul (.const 7) (.reg 5)) (.reg 6)))) ;;
  forRange 15 (.const 0) (.reg 8)
    (.store (.bin .add (.reg 13) (.reg 15)) (.load (.bin .add (.reg 14) (.reg 15)))) ;;
  .call 15 (bGT + gtIdxSortDedup) [.reg 13, .reg 8, .reg 10, .bin .add (.reg 13) (.reg 8)]

/-- Tail/head endpoint lookup sub-phase of `gtForwardDynPrepEStmt`. -/
def gtForwardDynPrepE2Stmt (bOps : ℕ) : Stmt :=
  forRange 15 (.const 0) (.reg 8)
    (.assign 16 (.load (.bin .add (.reg 10) (.reg 15))) ;;
     .call 17 (bOps + dgIdxGetTail) [.reg 1, .reg 16] ;;
     .store (.bin .add (.reg 11) (.reg 15)) (.reg 17) ;;
     .call 17 (bOps + dgIdxGetHead) [.reg 1, .reg 16] ;;
     .store (.bin .add (.reg 12) (.reg 15)) (.reg 17))

/-- Edge extraction, sorting, and endpoint lookup phase of `gtForwardDynPrepStmt`. -/
def gtForwardDynPrepEStmt (bOps bGT : ℕ) : Stmt :=
  gtForwardDynPrepE1Stmt bGT ;; gtForwardDynPrepE2Stmt bOps

/-- First phase of `gtForwardDynStmt`: reads dynamic metadata for `J`, extracts and sorts
`jVs, jEs`, and populates `jTails, jHeads` into scratch. -/
def gtForwardDynPrepStmt (bOps bGT : ℕ) : Stmt :=
  gtForwardDynPrepVStmt bGT ;; gtForwardDynPrepEStmt bOps bGT

/-- Deterministic Word-RAM forward translator from dynamic `MGraph` handles:
`[hPtr, jPtr, mEmbPtr, scratchPtr, outPtr]`.
Extracts sorted `jVs, jEs` and `jTails, jHeads` from `DynGraphAt J` without mutating `J`,
and delegates to `gtForwardCoreStmt`. -/
def gtForwardDynStmt (bOps bGT bFwd : ℕ) : Stmt :=
  gtForwardDynPrepStmt bOps bGT ;;
  (.call 15 (bFwd + gtIdxForwardCore)
    [.reg 0, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 2, .reg 13, .reg 4] ;;
  .ret (.reg 15))

/-- Procedure block containing `gtForwardCoreStmt` and `gtForwardDynStmt`. -/
def gtForwardProcs (bOps bGT bEmit bFwd : ℕ) : List Stmt :=
  [gtForwardCoreStmt bGT bEmit, gtForwardDynStmt bOps bGT bFwd]

lemma gtForwardProcs_length (bOps bGT bEmit bFwd : ℕ) :
    (gtForwardProcs bOps bGT bEmit bFwd).length = 2 := rfl

lemma gtForwardProcs_noRand (bOps bGT bEmit bFwd : ℕ) :
    ∀ s ∈ gtForwardProcs bOps bGT bEmit bFwd, s.NoRand := by
  intro s hs
  simp only [gtForwardProcs, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · simp [gtForwardCoreStmt, gtForwardCoreScratchStmt, gtForwardCoreEmitStmt, Stmt.NoRand]
  · simp [gtForwardDynStmt, gtForwardDynPrepStmt, gtForwardDynPrepVStmt,
      gtForwardDynPrepEStmt, gtForwardDynPrepE1Stmt, gtForwardDynPrepE2Stmt,
      forRange, forUp, Stmt.NoRand]

/-- Precondition for `gtForwardDynPrepStmt`. -/
def gtDynPrepPre (w vCapJ eCapJ rawEsLen : ℕ) (J : MGraph)
    (hPtr jPtr mEmbPtr scratchPtr outPtr : ℕ) (mem : ℕ → ℕ) : State → Prop :=
  fun st =>
    16 ≤ 2 ^ w ∧
    hPtr < 2 ^ w ∧ jPtr + dynGraphSize vCapJ eCapJ < 2 ^ w ∧
    mEmbPtr < 2 ^ w ∧ outPtr < 2 ^ w ∧
    scratchPtr + gtFwdDynScratchLen J.n J.m rawEsLen < 2 ^ w ∧
    (∀ i < dynGraphSize vCapJ eCapJ,
      jPtr + i < scratchPtr ∨ scratchPtr + gtFwdDynScratchLen J.n J.m rawEsLen ≤ jPtr + i) ∧
    DynGraphAt mem jPtr vCapJ eCapJ J ∧
    st.mem = mem ∧
    st.regs 0 = hPtr ∧ st.regs 1 = jPtr ∧ st.regs 2 = mEmbPtr ∧
    st.regs 3 = scratchPtr ∧ st.regs 4 = outPtr

/-- Postcondition for `gtForwardDynPrepStmt`. -/
def gtDynPrepPost (J : MGraph) (rawEsLen : ℕ)
    (hPtr jPtr mEmbPtr scratchPtr outPtr : ℕ) (mem : ℕ → ℕ) : State → Prop :=
  fun st =>
    let jVs := vertsOf J.V
    let jEs := vertsOf J.E
    let jTails := jEs.map J.tail
    let jHeads := jEs.map J.head
    let jVsPtr := scratchPtr
    let jEsPtr := jVsPtr + J.n
    let jTailsPtr := jEsPtr + J.m
    let jHeadsPtr := jTailsPtr + J.m
    let coreScratch := jHeadsPtr + J.m
    st.regs 0 = hPtr ∧ st.regs 1 = jPtr ∧ st.regs 2 = mEmbPtr ∧
    st.regs 3 = scratchPtr ∧ st.regs 4 = outPtr ∧
    st.regs 7 = J.n ∧ st.regs 8 = J.m ∧
    st.regs 9 = jVsPtr ∧ st.regs 10 = jEsPtr ∧
    st.regs 11 = jTailsPtr ∧ st.regs 12 = jHeadsPtr ∧ st.regs 13 = coreScratch ∧
    ListAt st.mem jVsPtr jVs ∧
    ListAt st.mem jEsPtr jEs ∧
    ListAt st.mem jTailsPtr jTails ∧
    ListAt st.mem jHeadsPtr jHeads ∧
    ∀ addr, addr < scratchPtr ∨ scratchPtr + gtFwdDynScratchLen J.n J.m rawEsLen ≤ addr →
      st.mem addr = mem addr

/-- Mid-point invariant between `gtForwardDynPrepVStmt` and `gtForwardDynPrepEStmt`. -/
def gtDynPrepVMid (w vCapJ eCapJ rawEsLen : ℕ) (J : MGraph)
    (hPtr jPtr mEmbPtr scratchPtr outPtr : ℕ) (mem : ℕ → ℕ) : State → Prop :=
  fun st =>
    let jVs := vertsOf J.V
    let jVsPtr := scratchPtr
    let jEsPtr := jVsPtr + J.n
    let jTailsPtr := jEsPtr + J.m
    let jHeadsPtr := jTailsPtr + J.m
    let coreScratch := jHeadsPtr + J.m
    16 ≤ 2 ^ w ∧
    hPtr < 2 ^ w ∧ jPtr + dynGraphSize vCapJ eCapJ < 2 ^ w ∧
    mEmbPtr < 2 ^ w ∧ outPtr < 2 ^ w ∧
    scratchPtr + gtFwdDynScratchLen J.n J.m rawEsLen < 2 ^ w ∧
    (∀ i < dynGraphSize vCapJ eCapJ,
      jPtr + i < scratchPtr ∨ scratchPtr + gtFwdDynScratchLen J.n J.m rawEsLen ≤ jPtr + i) ∧
    DynGraphAt mem jPtr vCapJ eCapJ J ∧
    st.regs 0 = hPtr ∧ st.regs 1 = jPtr ∧ st.regs 2 = mEmbPtr ∧
    st.regs 3 = scratchPtr ∧ st.regs 4 = outPtr ∧
    st.regs 5 = vCapJ ∧ st.regs 6 = eCapJ ∧
    st.regs 7 = J.n ∧ st.regs 8 = J.m ∧
    st.regs 9 = jVsPtr ∧ st.regs 10 = jEsPtr ∧
    st.regs 11 = jTailsPtr ∧ st.regs 12 = jHeadsPtr ∧ st.regs 13 = coreScratch ∧
    ListAt st.mem jVsPtr jVs ∧
    ∀ addr, addr < scratchPtr ∨ scratchPtr + gtFwdDynScratchLen J.n J.m rawEsLen ≤ addr →
      st.mem addr = mem addr

theorem gtForwardDyn_prepVPhase {w vCapJ eCapJ rawEsLen : ℕ} {p : Program}
    {bSort bOps bGT : ℕ} {J : MGraph}
    {hPtr jPtr mEmbPtr scratchPtr outPtr : ℕ} {mem : ℕ → ℕ}
    (hpGT : p.HasAt bGT (gtProcs bSort bOps))
    (hpSort : p.HasAt bSort (sortProcs bSort)) :
    Triple w p
      (gtDynPrepPre w vCapJ eCapJ rawEsLen J hPtr jPtr mEmbPtr scratchPtr outPtr mem)
      (gtForwardDynPrepVStmt bGT)
      (normalPost (gtDynPrepVMid w vCapJ eCapJ rawEsLen J hPtr jPtr mEmbPtr scratchPtr outPtr mem))
      (fun _ => 250 * J.n * (Nat.log 2 (J.n + 1) + 1) + 300 * J.n + 400) := by
  intro st ω hPre
  rcases hPre with ⟨hw16, hlt_hP, hjB, hlt_mEP, hlt_outP, hscB, hdisjJ, hDynJ,
    hmemEq, hst_r0, hst_r1, hst_r2, hst_r3, hst_r4⟩
  subst hmemEq
  let jVs := vertsOf J.V
  let sLen := gtFwdDynScratchLen J.n J.m rawEsLen
  have hsLen_eq : sLen = 3 * J.n + 6 * J.m + 5 * rawEsLen := rfl
  have hscB' : scratchPtr + sLen < 2 ^ w := hscB
  rw [hsLen_eq] at hscB'
  have hjV_len : jVs.length = J.n := vertsOf_length J.V
  have hlt_scP : scratchPtr < 2 ^ w := by omega
  have hvCapJ_ltw : vCapJ < 2 ^ w := by unfold dynGraphSize at hjB; omega
  have hnJ_le : J.n ≤ vCapJ := dynGraph_n_le_vCap hDynJ
  have hmJ_le : J.m ≤ eCapJ := dynGraph_m_le_eCap hDynJ
  have hlt_nJ : J.n < 2 ^ w := by omega
  let jVsPtr := scratchPtr
  let jEsPtr := jVsPtr + J.n
  let jTailsPtr := jEsPtr + J.m
  let jHeadsPtr := jTailsPtr + J.m
  let coreScratch := jHeadsPtr + J.m
  have hjEsP_ltw : jEsPtr < 2 ^ w := by dsimp only [jEsPtr, jVsPtr]; omega
  have hjTP_ltw : jTailsPtr < 2 ^ w := by dsimp only [jTailsPtr, jEsPtr, jVsPtr]; omega
  have hjHP_ltw : jHeadsPtr < 2 ^ w := by dsimp only [jHeadsPtr, jTailsPtr, jEsPtr, jVsPtr]; omega
  have hcsP_ltw : coreScratch < 2 ^ w := by dsimp only [coreScratch, jHeadsPtr, jTailsPtr, jEsPtr, jVsPtr]; omega
  have h0_lt : (0 : ℕ) < 2 ^ w := by omega
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have h2_lt : (2 : ℕ) < 2 ^ w := by omega
  have h3_lt : (3 : ℕ) < 2 ^ w := by omega
  have h4_lt : (4 : ℕ) < 2 ^ w := by omega
  obtain ⟨hJvalid, hJVc, _, hmVC, hmEC, hmN, hmM, _,
    ⟨vL, hvL_len, hvL_nd, hvL_mem, hvL_at, _⟩, _⟩ := id hDynJ
  have h4vc_ltw : 4 + vCapJ < 2 ^ w := by unfold dynGraphSize at hjB; omega
  have hvListP_ltw : dgVListBase jPtr vCapJ < 2 ^ w := by
    dsimp [dgVListBase]; unfold dynGraphSize at hjB; omega
  have hdgVL_ltw : jPtr + (4 + vCapJ) < 2 ^ w := by
    dsimp [dgVListBase] at hvListP_ltw; omega
  have hcs_n_ltw : coreScratch + J.n < 2 ^ w := by
    dsimp only [coreScratch, jHeadsPtr, jTailsPtr, jEsPtr, jVsPtr]; omega
  have hcs2n_ltw : coreScratch + 2 * J.n < 2 ^ w := by
    dsimp only [coreScratch, jHeadsPtr, jTailsPtr, jEsPtr, jVsPtr]; omega
  have hjVC_off_ltw : jPtr + dgVCapOff < 2 ^ w := by unfold dgVCapOff dynGraphSize at *; omega
  have hjEC_off_ltw : jPtr + dgECapOff < 2 ^ w := by unfold dgECapOff dynGraphSize at *; omega
  have hjN_off_ltw : jPtr + dgNOff < 2 ^ w := by unfold dgNOff dynGraphSize at *; omega
  have hjM_off_ltw : jPtr + dgMOff < 2 ^ w := by unfold dgMOff dynGraphSize at *; omega
  dsimp only [gtForwardDynPrepVStmt]
  refine runs_start_le ?_
  -- 1. assign 5 := vCapJ, 6 := eCapJ, 7 := J.n, 8 := J.m
  refine runs_seq_assign_le (v := vCapJ)
    (by simp only [Expr.eval, BinOp.eval, Option.map_eq_some_iff, hst_r1, dgVCapOff, h0_lt, ↓reduceIte]
        exact ⟨jPtr + 0, ite_eq_left_iff.mpr fun h => False.elim (h (by unfold dgVCapOff at hjVC_off_ltw; exact hjVC_off_ltw)),
          by simpa [dgVCapOff] using hmVC⟩) ?_
  refine runs_seq_assign_le (v := eCapJ)
    (by simp only [Expr.eval, BinOp.eval, Option.map_eq_some_iff]
        simp (disch := decide) only [Function.update_of_ne, hst_r1]
        simp only [dgECapOff, h1_lt, ↓reduceIte]
        exact ⟨jPtr + 1, ite_eq_left_iff.mpr fun h => False.elim (h (by unfold dgECapOff at hjEC_off_ltw; exact hjEC_off_ltw)),
          by simpa [dgECapOff] using hmEC⟩) ?_
  refine runs_seq_assign_le (v := J.n)
    (by simp only [Expr.eval, BinOp.eval, Option.map_eq_some_iff]
        simp (disch := decide) only [Function.update_of_ne, hst_r1]
        simp only [dgNOff, h2_lt, ↓reduceIte]
        exact ⟨jPtr + 2, ite_eq_left_iff.mpr fun h => False.elim (h (by unfold dgNOff at hjN_off_ltw; exact hjN_off_ltw)),
          by simpa [dgNOff] using hmN⟩) ?_
  refine runs_seq_assign_le (v := J.m)
    (by simp only [Expr.eval, BinOp.eval, Option.map_eq_some_iff]
        simp (disch := decide) only [Function.update_of_ne, hst_r1]
        simp only [dgMOff, h3_lt, ↓reduceIte]
        exact ⟨jPtr + 3, ite_eq_left_iff.mpr fun h => False.elim (h (by unfold dgMOff at hjM_off_ltw; exact hjM_off_ltw)),
          by simpa [dgMOff] using hmM⟩) ?_
  -- 2. assign 9 := jVsPtr, 10 := jEsPtr, 11 := jTailsPtr, 12 := jHeadsPtr, 13 := coreScratch, 14 := dgVListBase
  refine runs_seq_assign_le (v := jVsPtr)
    (by simp only [Expr.eval]; simp (disch := decide) only [Function.update_of_ne, hst_r3]; rfl) ?_
  refine runs_seq_assign_le (v := jEsPtr)
    (by simp only [Expr.eval, BinOp.eval]; simp (disch := decide) only [Function.update_of_ne, Function.update_self]
        exact ite_eq_left_iff.mpr fun h => False.elim (h hjEsP_ltw)) ?_
  refine runs_seq_assign_le (v := jTailsPtr)
    (by simp only [Expr.eval, BinOp.eval]; simp (disch := decide) only [Function.update_of_ne, Function.update_self]
        exact ite_eq_left_iff.mpr fun h => False.elim (h hjTP_ltw)) ?_
  refine runs_seq_assign_le (v := jHeadsPtr)
    (by simp only [Expr.eval, BinOp.eval]; simp (disch := decide) only [Function.update_of_ne, Function.update_self]
        exact ite_eq_left_iff.mpr fun h => False.elim (h hjHP_ltw)) ?_
  refine runs_seq_assign_le (v := coreScratch)
    (by simp only [Expr.eval, BinOp.eval]; simp (disch := decide) only [Function.update_of_ne, Function.update_self]
        exact ite_eq_left_iff.mpr fun h => False.elim (h hcsP_ltw)) ?_
  refine runs_seq_assign_le (v := dgVListBase jPtr vCapJ)
    (by simp only [Expr.eval, BinOp.eval]
        simp (disch := decide) only [Function.update_of_ne, Function.update_self, hst_r1]
        simp only [h4_lt, h4vc_ltw, hdgVL_ltw, ↓reduceIte]
        rw [show jPtr + (4 + vCapJ) = dgVListBase jPtr vCapJ by dsimp [dgVListBase]; omega]) ?_
  let rOrigDyn : ℕ → ℕ := fun r =>
    match r with
    | 0 => hPtr | 1 => jPtr | 2 => mEmbPtr | 3 => scratchPtr | 4 => outPtr
    | 5 => vCapJ | 6 => eCapJ | 7 => J.n | 8 => J.m
    | 9 => jVsPtr | 10 => jEsPtr | 11 => jTailsPtr | 12 => jHeadsPtr | _ => coreScratch
  -- 3. Copy vL to coreScratch
  refine runs_seq_triple_le
    (gtCopyRange_triple 14 13 7 (by decide) (by decide) (by decide)
      (srcPtr := dgVListBase jPtr vCapJ) (dstPtr := coreScratch) (len := J.n) (L := vL)
      (mem := st.mem) (rOrig := rOrigDyn)
      h1_lt hlt_nJ
      (by dsimp [dgVListBase]; unfold dynGraphSize at hjB; omega)
      (by omega) hvL_len hvL_at
      (fun i hi j hj heq => by
        have hdj := hdisjJ (dgVListBase jPtr vCapJ + i - jPtr) (by
          dsimp [dgVListBase]; unfold dynGraphSize; omega)
        rw [show jPtr + (dgVListBase jPtr vCapJ + i - jPtr) = dgVListBase jPtr vCapJ + i by
          dsimp [dgVListBase]; omega] at hdj
        dsimp only [gtFwdDynScratchLen] at hdj
        dsimp only [coreScratch, jHeadsPtr, jTailsPtr, jEsPtr, jVsPtr] at heq
        rcases hdj with h | h <;> omega))
    ⟨rfl, by simp [Function.update_self],
      by simp (disch := decide) only [Function.update_of_ne, Function.update_self],
      by simp (disch := decide) only [Function.update_of_ne, Function.update_self],
      fun r hr => by
        rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨
            r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨ r = 12 ∨ r = 13) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp (disch := decide) only [Function.update_of_ne, Function.update_self,
            hst_r0, hst_r1, hst_r2, hst_r3, hst_r4, rOrigDyn]⟩
    ?_
  intro st1 ⟨_, _, _, _, hOrig1, hvCopy1, hfr1⟩
  have hfr1_out : ∀ addr, addr < scratchPtr ∨ scratchPtr + sLen ≤ addr → st1.mem addr = st.mem addr :=
    fun addr ha => hfr1 addr (by
      rcases ha with h | h
      · left; dsimp only [coreScratch, jHeadsPtr, jTailsPtr, jEsPtr, jVsPtr] at *; omega
      · right; rw [hsLen_eq] at h; dsimp only [coreScratch, jHeadsPtr, jTailsPtr, jEsPtr, jVsPtr]; omega)
  have hvAt1 : ListAt st1.mem coreScratch vL := fun i hi => hvCopy1 i (by omega) hi
  have hvL_w : ∀ x ∈ vL, x < 2 ^ w := fun x hx => by
    rw [hvL_mem] at hx
    exact lt_trans (hJVc x hx) hvCapJ_ltw
  -- 4. SortDedup vL -> jVsPtr (terminal call of gtForwardDynPrepVStmt)
  rcases runs_call_of_meetsContract (gtSortDedup_meetsContract (L := vL) (X := J.V) hpGT hpSort)
      (r := 15) (args := [.reg 13, .reg 7, .reg 9, .bin .add (.reg 13) (.reg 7)])
      (st := st1) (vs := [coreScratch, vL.length, jVsPtr, coreScratch + vL.length])
      (by have hr13 := hOrig1 13 (by omega)
          have hr7 := hOrig1 7 (by omega)
          have hr9 := hOrig1 9 (by omega)
          dsimp only [rOrigDyn] at hr13 hr7 hr9
          simp only [evalArgs, Expr.eval, BinOp.eval, hr13, hr7, hr9, hvL_len, hcs_n_ltw, ↓reduceIte])
      (by intro v hv
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl <;> omega)
      ⟨coreScratch, jVsPtr, coreScratch + vL.length, rfl, hw16,
        by omega, by omega, by omega,
        Or.inl (by omega), Or.inr (by dsimp only [coreScratch, jHeadsPtr, jTailsPtr, jEsPtr, jVsPtr]; omega),
        hvAt1, hvL_w, hvL_mem⟩ ω with
    ⟨st2, c2, lenV, hrun2, ⟨_, _, _, hargs2, hret2, hVAt2, hfr2⟩, hr2_self, hr2_other, hcost2⟩
  simp only [List.cons.injEq, and_true] at hargs2
  rcases hargs2 with ⟨rfl, _, rfl, rfl⟩
  refine ⟨.normal, st2, c2, hrun2, ?_, ?_⟩
  · have hfr2_out : ∀ addr, addr < scratchPtr ∨ scratchPtr + sLen ≤ addr → st2.mem addr = st.mem addr :=
      fun addr ha => by
        have ha1 : addr < coreScratch ∨ coreScratch + vL.length ≤ addr := by
          rcases ha with h | h
          · left; dsimp only [coreScratch, jHeadsPtr, jTailsPtr, jEsPtr, jVsPtr] at *; omega
          · right; rw [hsLen_eq] at h; dsimp only [coreScratch, jHeadsPtr, jTailsPtr, jEsPtr, jVsPtr]; omega
        have ha2 : addr < jVsPtr ∨ jVsPtr + (vertsOf J.V).length ≤ addr := by
          rw [hjV_len]
          rcases ha with h | h
          · left; dsimp only [jVsPtr] at *; omega
          · right; rw [hsLen_eq] at h; dsimp only [jVsPtr]; omega
        have ha3 : addr < coreScratch + vL.length ∨ coreScratch + vL.length + vL.length ≤ addr := by
          rcases ha with h | h
          · left; dsimp only [coreScratch, jHeadsPtr, jTailsPtr, jEsPtr, jVsPtr] at *; omega
          · right; rw [hsLen_eq] at h; dsimp only [coreScratch, jHeadsPtr, jTailsPtr, jEsPtr, jVsPtr]; omega
        exact (hfr2 addr ha1 ha3 ha2).trans (hfr1_out addr ha)
    have hr_upd : ∀ r < 14, st2.regs r = rOrigDyn r := fun r hr => by
      rw [hr2_other r (by omega)]; exact hOrig1 r hr
    refine ⟨hw16, hlt_hP, hjB, hlt_mEP, hlt_outP, hscB, hdisjJ, hDynJ,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hVAt2, hfr2_out⟩
    · have h := hr_upd 0 (by omega); dsimp only [rOrigDyn] at h; exact h
    · have h := hr_upd 1 (by omega); dsimp only [rOrigDyn] at h; exact h
    · have h := hr_upd 2 (by omega); dsimp only [rOrigDyn] at h; exact h
    · have h := hr_upd 3 (by omega); dsimp only [rOrigDyn] at h; exact h
    · have h := hr_upd 4 (by omega); dsimp only [rOrigDyn] at h; exact h
    · have h := hr_upd 5 (by omega); dsimp only [rOrigDyn] at h; exact h
    · have h := hr_upd 6 (by omega); dsimp only [rOrigDyn] at h; exact h
    · have h := hr_upd 7 (by omega); dsimp only [rOrigDyn] at h; exact h
    · have h := hr_upd 8 (by omega); dsimp only [rOrigDyn] at h; exact h
    · have h := hr_upd 9 (by omega); dsimp only [rOrigDyn] at h; exact h
    · have h := hr_upd 10 (by omega); dsimp only [rOrigDyn] at h; exact h
    · have h := hr_upd 11 (by omega); dsimp only [rOrigDyn] at h; exact h
    · have h := hr_upd 12 (by omega); dsimp only [rOrigDyn] at h; exact h
    · have h := hr_upd 13 (by omega); dsimp only [rOrigDyn] at h; exact h
  · dsimp only [gtSortDedupContract, argsSize, Expr.size] at hcost2 ⊢
    rw [hvL_len] at hcost2; omega

end

end MinCostFlow.DynSpanner.Program
