module

public import MinCostFlow.MinRatio.SelectNonRebuiltOps
public import MinCostFlow.MinRatio.SelectGraphRefill
public import MinCostFlow.MinRatio.SelectCoreList
public import MinCostFlow.MinRatio.SelectEmbCopy
public import MinCostFlow.MinRatio.SelectCoreLenPerEdge
public import MinCostFlow.MinRatio.SelectInteriorFill
public import MinCostFlow.MinRatio.WireSelectUpdate
import WordRAM.Tactic

/-!
# Per-level select-block update for non-rebuilt levels (`SelectUpdateNonRebuilt`)

Provides the deterministic Word-RAM procedure `selectUpdateNonRebuiltLevelBody` and its
verification `selectUpdateNonRebuiltLevel_runs` for updating a single non-rebuilt interior level
`j < min firstReb d` at an `Update`:

1. `selEmbUpdateFromListBody` (`[gPresBase, fPresBase, embTable, embPtr, eCap, slotSz, listPtr,
   listLen, scratch] → scratch + 2 * listLen`): filters a candidate edge list to surviving
   active-core edges `L ∩ (G.E \ F.E)` via `selFilterPresent` + `selFilterAbsent`, and copies their
   walks into `B.embPtr j` via `selEmbCopy` (`selEmbUpdateFromList_meetsContract`).
2. `selectUpdateNonRebuiltLevelBody`: given the 12-word slot of a non-rebuilt level `j`
   (`LevelDiffListsAt` + `(stDesc, stLw)` + `(uPtr, uWords)`), updates:
   * `B.fPtr j` via `dgApplyBatch (allowInsert = 0)` + `dgDeleteEdgeList` on `fDel`,
   * `B.phiPtr j` via `selBatchCopySplits` on `uPtr`,
   * `B.lenPtr j` via `selFilterPresent` on `uG` + `selCoreLenFill` at `shift = 0`,
   * `B.embPtr j` via `op 4` + three calls to `selEmbUpdateFromList` on `uG`, `fDel`, `reemb`.
3. `selectUpdateNonRebuiltLevel_runs`: updates `F j`, `V j`, `φ j`, `E j`, `len j`, `coreE j`,
   `emb j` in `SelBlocksDataAt` while preserving all other levels, `R.rep`, and full frame
   outside `R.foot handle x ∨ B.regBlk j`, with arbitrary placement of `R.foot` and `solverG j`
   disjoint from `[B.base, B.endAddr)` and below `scratch`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain MinCostFlow.DynSpanner DynSpanner.Program
open SparseCore SparseCore.Program

/-! ## 1. Filtered embedding-slot update from a candidate list -/

/-- Filter `listPtr[0..listLen)` to edges present in `G` (`gPresBase`) and absent from `F`
(`fPresBase`), copy their walks from `embTable` into `embPtr`, and return `scratch + 2 * listLen`
(`[gPresBase, fPresBase, embTable, embPtr, eCap, slotSz, listPtr, listLen, scratch]`). -/
def selEmbUpdateFromListBody (filterPres filterAbs embCopy : ℕ) : Stmt :=
  .call 9 filterPres [.reg 6, .reg 7, .reg 0, .reg 8] ;;
  .assign 10 (.bin .add (.reg 8) (.reg 7)) ;;
  .call 11 filterAbs [.reg 8, .reg 9, .reg 1, .reg 10] ;;
  .call 12 embCopy [.reg 2, .reg 3, .reg 4, .reg 5, .reg 10, .reg 11] ;;
  .ret (.bin .add (.reg 10) (.reg 7))

theorem selEmbUpdateFromListBody_noRand (filterPres filterAbs embCopy : ℕ) :
    (selEmbUpdateFromListBody filterPres filterAbs embCopy).NoRand := by
  simp [selEmbUpdateFromListBody, Stmt.NoRand]

/-- Step cost bound for `selEmbUpdateFromListBody`. -/
def selEmbUpdateFromListCost (len slotSz : ℕ) : ℕ :=
  len * (18 * slotSz + 160) + 120

/-- Contract for `selEmbUpdateFromListBody`. -/
def selEmbUpdateFromListContract (w vCap eCap : ℕ) (G F : MGraph) (L : List ℕ)
    (emb : Embedding) : Contract where
  pre args mem := ∃ gPtr fPtr embTable embPtr slotSz listPtr scratch,
    args = [dgEPresBase gPtr vCap, dgEPresBase fPtr vCap, embTable, embPtr, eCap, slotSz,
      listPtr, L.length, scratch] ∧
    16 < 2 ^ w ∧
    gPtr + dynGraphSize vCap eCap ≤ scratch ∧
    fPtr + dynGraphSize vCap eCap ≤ scratch ∧
    embPtr + eCap + eCap * slotSz ≤ scratch ∧
    listPtr + L.length ≤ scratch ∧
    DynGraphAt mem gPtr vCap eCap G ∧
    DynGraphAt mem fPtr vCap eCap F ∧
    ListAt mem listPtr L ∧
    (∀ e ∈ L, e < eCap) ∧
    (∀ e ∈ L, e ∈ G.E \ F.E →
      SelEmbSrcOk mem w embTable slotSz embPtr (embPtr + eCap + eCap * slotSz) emb e ∧
      embTable + e < scratch ∧
      mem (embTable + e) + (mWalkEncode (emb e)).length ≤ scratch) ∧
    ZeroFrom mem scratch ∧
    scratch + 2 * L.length < 2 ^ w
  post args mem ret mem' := ∃ gPtr fPtr embTable embPtr slotSz listPtr scratch,
    args = [dgEPresBase gPtr vCap, dgEPresBase fPtr vCap, embTable, embPtr, eCap, slotSz,
      listPtr, L.length, scratch] ∧
    ret = scratch + 2 * L.length ∧
    ZeroFrom mem' ret ∧
    (∀ e ∈ L, e ∈ G.E \ F.E →
      mem' (embPtr + e) = embPtr + eCap + e * slotSz ∧
      MWalkAt mem' (embPtr + eCap + e * slotSz) (emb e)) ∧
    (∀ a < scratch, (a < embPtr ∨ embPtr + eCap + eCap * slotSz ≤ a) → mem' a = mem a) ∧
    (∀ e < eCap, (e ∉ L ∨ e ∉ G.E \ F.E) →
      mem' (embPtr + e) = mem (embPtr + e) ∧
      ∀ t < slotSz, mem' (embPtr + eCap + e * slotSz + t) = mem (embPtr + eCap + e * slotSz + t))
  cost args _ := selEmbUpdateFromListCost L.length (args.getD 5 0)

/-! ## 2. Per-level non-rebuilt select-block update procedure -/

/-- Scratch space bound for `selectUpdateNonRebuiltLevelBody`. -/
def selectUpdateNonRebuiltSpace (uGLen fDelLen reembLen Lk Lw : ℕ) : ℕ :=
  uGLen + uGLen * selCoreLenEdgeSpace Lk Lw + 2 + 2 * (uGLen + fDelLen + reembLen)

/-- Step cost bound for `selectUpdateNonRebuiltLevelBody`. -/
def selectUpdateNonRebuiltCost (readoutCost uWords uLen uGLen fDelLen reembLen Lk Lw slotSz : ℕ) : ℕ :=
  (670 * uWords + 30) +
  (fDelLen * 490 + 20) +
  (uLen * (18 * Lk + 130) + 40) +
  (40 * uGLen + 20) +
  (uGLen * (selCoreLenEdgeCost Lk Lw + 40) + 20) +
  readoutCost +
  selEmbUpdateFromListCost uGLen slotSz +
  selEmbUpdateFromListCost fDelLen slotSz +
  selEmbUpdateFromListCost reembLen slotSz + 420

/-- Deterministic Word-RAM procedure `[metaBase, j, slot, handle, branch, prevLen, Lk, slotSz,
scratch] → nextScratch` updating `F_j`, `φ_j`, `len_j`, and `emb_j` for one non-rebuilt level
`j < min firstReb d`. -/
def selectUpdateNonRebuiltLevelBody (op4 dgApplyBatch delEdgeList batchCopySplits filterPres
    coreLenFill embUpdateFromList : ℕ) : Stmt :=
  .assign 9 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 10 (.bin .add (.reg 9) (.const 1)) ;;
  .assign 11 (.bin .add (.reg 0) (.const smTableOff)) ;;
  .assign 12 (.load (.bin .add (.reg 11) (.reg 1))) ;;
  .assign 13 (.load (.bin .add (.bin .add (.reg 11) (.reg 10)) (.reg 1))) ;;
  .assign 14 (.load (.bin .add (.bin .add (.reg 11) (.bin .mul (.const 2) (.reg 10))) (.reg 1))) ;;
  .assign 15 (.load (.bin .add (.bin .add (.reg 11) (.bin .mul (.const 3) (.reg 10))) (.reg 1))) ;;
  .assign 16 (.load (.bin .add (.bin .add (.reg 11) (.bin .mul (.const 4) (.reg 10))) (.reg 1))) ;;
  .assign 17 (.load (.bin .add (.bin .add (.reg 11) (.bin .mul (.const 5) (.reg 10))) (.reg 1))) ;;
  .assign 18 (.load (.bin .add (.bin .add (.reg 11) (.bin .mul (.const 6) (.reg 10))) (.reg 1))) ;;
  .assign 19 (.bin .add (.bin .add (.reg 12) (.const 4)) (.bin .mul (.const 7) (.reg 13))) ;;
  .assign 20 (.bin .add (.bin .add (.reg 18) (.const 4)) (.bin .mul (.const 7) (.reg 13))) ;;
  .assign 21 (.load (.reg 2)) ;;
  .assign 22 (.load (.bin .add (.reg 2) (.const 1))) ;;
  .assign 23 (.load (.bin .add (.reg 2) (.const 2))) ;;
  .assign 24 (.load (.bin .add (.reg 2) (.const 3))) ;;
  .assign 25 (.load (.bin .add (.reg 2) (.const 6))) ;;
  .assign 26 (.load (.bin .add (.reg 2) (.const 7))) ;;
  .assign 27 (.load (.bin .add (.reg 2) (.const 8))) ;;
  .assign 28 (.load (.bin .add (.reg 2) (.const 9))) ;;
  .assign 29 (.load (.bin .add (.reg 2) (.const 10))) ;;
  .assign 30 (.load (.reg 27)) ;;
  .assign 31 (.load (.bin .add (.reg 27) (.const 1))) ;;
  .call 32 dgApplyBatch [.reg 18, .reg 29, .const 0] ;;
  .call 32 delEdgeList [.reg 18, .reg 23, .reg 24] ;;
  .call 32 batchCopySplits [.reg 29, .reg 15, .reg 6] ;;
  .call 33 filterPres [.reg 21, .reg 22, .reg 19, .reg 8] ;;
  .assign 34 (.bin .add (.reg 8) (.reg 22)) ;;
  .call 35 coreLenFill
    [.reg 5, .reg 30, .reg 31, .reg 16, .reg 8, .reg 33, .reg 6, .reg 28, .const 0, .reg 34] ;;
  .call 36 op4 [.reg 3, .reg 4, .reg 12, .reg 35] ;;
  .assign 37 (.load (.reg 35)) ;;
  .call 38 embUpdateFromList
    [.reg 19, .reg 20, .reg 37, .reg 17, .reg 14, .reg 7, .reg 21, .reg 22, .reg 36] ;;
  .call 39 embUpdateFromList
    [.reg 19, .reg 20, .reg 37, .reg 17, .reg 14, .reg 7, .reg 23, .reg 24, .reg 38] ;;
  .call 40 embUpdateFromList
    [.reg 19, .reg 20, .reg 37, .reg 17, .reg 14, .reg 7, .reg 25, .reg 26, .reg 39] ;;
  .ret (.reg 40)

theorem selectUpdateNonRebuiltLevelBody_noRand (op4 dgApplyBatch delEdgeList batchCopySplits
    filterPres coreLenFill embUpdateFromList : ℕ) :
    (selectUpdateNonRebuiltLevelBody op4 dgApplyBatch delEdgeList batchCopySplits filterPres
      coreLenFill embUpdateFromList).NoRand := by
  simp [selectUpdateNonRebuiltLevelBody, Stmt.NoRand]

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain MinCostFlow.DynSpanner DynSpanner.Program
open SparseCore SparseCore.Program

/-! ## 3. Verification of `selEmbUpdateFromListBody` -/

/-- `selEmbUpdateFromListBody` meets `selEmbUpdateFromListContract`. -/
theorem selEmbUpdateFromList_meetsContract {w proc filterPres filterAbs embCopy vCap eCap : ℕ}
    {G F : MGraph} {L : List ℕ} {emb : Embedding} {p : Program}
    (hp : p.procs[proc]? = some (selEmbUpdateFromListBody filterPres filterAbs embCopy))
    (hPres : MeetsContract w p filterPres (selFilterPresentContract w L))
    (hAbs : ∀ L1 : List ℕ, MeetsContract w p filterAbs (selFilterAbsentContract w L1))
    (hEmb : ∀ L2 : List ℕ, MeetsContract w p embCopy (selEmbCopyContract w L2 emb)) :
    MeetsContract w p proc (selEmbUpdateFromListContract w vCap eCap G F L emb) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨gPtr, fPtr, embTable, embPtr, slotSz, listPtr, scratch, rfl, hw16, hgLe, hfLe,
    hembLe, hlistLe, hG, hF, hlist, hcapL, hsrcOk, hz, hroom⟩ := hpre
  have hDgSz : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  have hgPresDef : dgEPresBase gPtr vCap = gPtr + 4 + 7 * vCap := rfl
  have hfPresDef : dgEPresBase fPtr vCap = fPtr + 4 + 7 * vCap := rfl
  have hPresPre : (selFilterPresentContract w L).pre
      [listPtr, L.length, dgEPresBase gPtr vCap, scratch] mem := by
    refine ⟨listPtr, dgEPresBase gPtr vCap, scratch, rfl, hw16, by omega, by omega, Or.inl (by omega),
      hlist, fun e he => ?_⟩
    have heCap := hcapL e he
    have hbit := hG.2.2.2.2.2.2.2.2.2.2.2.1 e heCap
    refine ⟨by omega, by omega, ?_, Or.inl (by omega)⟩
    by_cases hE : e ∈ G.E <;> simp [hE] at hbit <;> omega
  apply runs_start_le
  unfold selEmbUpdateFromListBody
  refine runs_seq_call_le hPres (vs := [listPtr, L.length, dgEPresBase gPtr vCap, scratch])
    (by eval_expr) (by wram_words) hPresPre ?_
  intro cnt1 mem1 pos1 hpost1
  obtain ⟨_, _, _, hargs1, hcnt1, hL1At, hfr1⟩ := hpost1
  dsimp only [startState] at hcnt1 hL1At hfr1
  simp only [List.cons.injEq] at hargs1
  obtain ⟨rfl, -, rfl, rfl, -⟩ := hargs1
  set L1 := selPresent mem (dgEPresBase gPtr vCap) L
  have hL1Len : L1.length ≤ L.length := selPresent_length_le _ _ _
  have hL1Mem : ∀ e, e ∈ L1 ↔ e ∈ L ∧ e ∈ G.E := fun e =>
    mem_selPresent_iff hG hcapL e
  have hcnt1W : cnt1 < 2 ^ w := by omega
  have hbuf2W : scratch + L.length < 2 ^ w := by omega
  have hembTabW : embTable < 2 ^ w := hwords embTable (by simp)
  have hslotW : slotSz < 2 ^ w := hwords slotSz (by simp)
  refine runs_seq_assign_le (v := scratch + L.length) (by eval_expr) ?_
  have hAbsPre : (selFilterAbsentContract w L1).pre
      [scratch, L1.length, dgEPresBase fPtr vCap, scratch + L.length] mem1 := by
    refine ⟨scratch, dgEPresBase fPtr vCap, scratch + L.length, rfl, hw16, by omega, by omega,
      Or.inl (by omega), hL1At, fun e he => ?_⟩
    have heL := ((hL1Mem e).mp he).1
    have heCap := hcapL e heL
    have hbit0 := hF.2.2.2.2.2.2.2.2.2.2.2.1 e heCap
    have hbit1 : mem1 (dgEPresBase fPtr vCap + e) = mem (dgEPresBase fPtr vCap + e) :=
      hfr1 _ (Or.inl (by omega))
    refine ⟨by omega, by omega, ?_, Or.inl (by omega)⟩
    rw [hbit1]; by_cases hE : e ∈ F.E <;> simp [hE] at hbit0 <;> omega
  refine runs_seq_call_le (hAbs L1)
    (vs := [scratch, L1.length, dgEPresBase fPtr vCap, scratch + L.length])
    (by eval_expr) (by wram_words) hAbsPre ?_
  intro cnt2 mem2 pos2 hpost2
  obtain ⟨_, _, _, hargs2, hcnt2, hL2At, hfr2⟩ := hpost2
  dsimp only at hcnt2 hL2At hfr2
  simp only [List.cons.injEq] at hargs2
  obtain ⟨rfl, -, rfl, rfl, -⟩ := hargs2
  set L2 := selAbsent mem1 (dgEPresBase fPtr vCap) L1
  have hL2Len : L2.length ≤ L1.length := selAbsent_length_le _ _ _
  have hF1 : DynGraphAt mem1 fPtr vCap eCap F :=
    hF.of_agree fun a _ ha => hfr1 a (Or.inl (by omega))
  have hL2Mem : ∀ e, e ∈ L2 ↔ e ∈ L ∧ e ∈ G.E \ F.E := fun e => by
    change e ∈ selAbsent mem1 (dgEPresBase fPtr vCap) L1 ↔ _
    unfold selAbsent
    rw [List.mem_filter, hL1Mem e, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨heL, heG⟩, hbit⟩
      have heCap := hcapL e heL
      have hfp := hF1.2.2.2.2.2.2.2.2.2.2.2.1 e heCap
      refine ⟨heL, heG, fun heF => ?_⟩
      simp [heF] at hfp; simp [hfp] at hbit
    · rintro ⟨heL, heG, heF⟩
      have heCap := hcapL e heL
      have hfp := hF1.2.2.2.2.2.2.2.2.2.2.2.1 e heCap
      refine ⟨⟨heL, heG⟩, ?_⟩
      simp [heF] at hfp; simp [hfp]
  have hcnt2W : cnt2 < 2 ^ w := by omega
  have hretW : scratch + L.length + L.length < 2 ^ w := by omega
  have hmem2Lt : ∀ a < scratch, mem2 a = mem a := fun a ha =>
    (hfr2 a (Or.inl (by omega))).trans (hfr1 a (Or.inl ha))
  have hEmbPre : (selEmbCopyContract w L2 emb).pre
      [embTable, embPtr, eCap, slotSz, scratch + L.length, L2.length] mem2 := by
    refine ⟨embTable, embPtr, eCap, slotSz, scratch + L.length, rfl, hw16, by omega, by omega,
      Or.inr (by omega), hL2At, fun e he => ?_⟩
    obtain ⟨heL, heDiff⟩ := (hL2Mem e).mp he
    obtain ⟨⟨hslotLe, hmw, htabW, htabDisj, hwalkW, hwalkWords, hwalkDisj⟩, htabSc, hwalkSc⟩ :=
      hsrcOk e heL heDiff
    have htabEq : mem2 (embTable + e) = mem (embTable + e) := hmem2Lt _ htabSc
    refine ⟨hcapL e heL, hslotLe, ?_, htabW, htabDisj, by rw [htabEq]; exact hwalkW,
      fun t ht => by rw [htabEq, hmem2Lt _ (by omega)]; exact hwalkWords t ht,
      by rw [htabEq]; exact hwalkDisj⟩
    rw [htabEq]
    exact fun t ht => (hmem2Lt _ (by omega)).trans (hmw t ht)
  refine runs_seq_call_le (hEmb L2)
    (vs := [embTable, embPtr, eCap, slotSz, scratch + L.length, L2.length])
    (by eval_expr) (by wram_words) hEmbPre ?_
  intro _ mem3 pos3 hpost3
  obtain ⟨_, _, _, _, _, hargs3, _, hcopied, hfr3, hkeep3⟩ := hpost3
  dsimp only at hcopied hfr3 hkeep3
  simp only [List.cons.injEq] at hargs3
  obtain ⟨rfl, rfl, rfl, rfl, rfl, -⟩ := hargs3
  refine WordRAM.runs_ret_le (v := scratch + L.length + L.length) (by eval_expr) ?_ ?_
  · dsimp only [Outcome.value]
    refine ⟨gPtr, fPtr, embTable, embPtr, slotSz, listPtr, scratch, rfl, by omega, ?_, ?_, ?_, ?_⟩
    · intro a ha
      rw [hfr3 a (Or.inr (by omega)), hfr2 a (Or.inr (by omega)), hfr1 a (Or.inr (by omega))]
      exact hz a (by omega)
    · intro e heL heDiff
      exact hcopied e ((hL2Mem e).mpr ⟨heL, heDiff⟩)
    · intro a ha hout
      rw [hfr3 a hout, hmem2Lt a ha]
    · intro e heCap hnot
      have hnotL2 : e ∉ L2 := fun hm => by
        obtain ⟨h1, h2⟩ := (hL2Mem e).mp hm
        exact hnot.elim (fun h => h h1) (fun h => h h2)
      obtain ⟨hk1, hk2⟩ := hkeep3 e heCap hnotL2
      refine ⟨hk1.trans (hmem2Lt _ (by omega)), fun t ht => ?_⟩
      have hslotEnd : e * slotSz + slotSz ≤ eCap * slotSz := by
        have := Nat.mul_le_mul_right slotSz (Nat.succ_le_of_lt heCap)
        rw [Nat.succ_mul] at this; exact this
      exact (hk2 t ht).trans (hmem2Lt _ (by omega))
  · simp only [selEmbUpdateFromListContract, selEmbUpdateFromListCost,
      selFilterPresentContract, selFilterAbsentContract, selEmbCopyContract,
      List.getD_cons_zero, List.getD_cons_succ, Expr.size, argsSize]
    have h1 := Nat.mul_le_mul_right (18 * slotSz + 80) (le_trans hL2Len hL1Len)
    have hqEq : L.length * (18 * slotSz + 160) = L.length * (18 * slotSz + 80) + 80 * L.length := by
      ring
    omega

/-! ## 4. Continuation-style setup lemma for `selectUpdateNonRebuiltLevelBody` -/

/-- Register state after the 23 setup assignments of `selectUpdateNonRebuiltLevelBody`. -/
structure NonRebRegs (R : ℕ → ℕ) (metaBase j slot handle branch prevLen Lk slotSz scratch
    d gPtr vCap eCap phiPtr lenPtr embPtr fPtr uGPtr uGLen fDelPtr fDelLen reembPtr reembLen
    stDesc stLw uPtr numBase denBase : ℕ) : Prop where
  r0 : R 0 = metaBase
  r1 : R 1 = j
  r2 : R 2 = slot
  r3 : R 3 = handle
  r4 : R 4 = branch
  r5 : R 5 = prevLen
  r6 : R 6 = Lk
  r7 : R 7 = slotSz
  r8 : R 8 = scratch
  r12 : R 12 = gPtr
  r14 : R 14 = eCap
  r15 : R 15 = phiPtr
  r16 : R 16 = lenPtr
  r17 : R 17 = embPtr
  r18 : R 18 = fPtr
  r19 : R 19 = dgEPresBase gPtr vCap
  r20 : R 20 = dgEPresBase fPtr vCap
  r21 : R 21 = uGPtr
  r22 : R 22 = uGLen
  r23 : R 23 = fDelPtr
  r24 : R 24 = fDelLen
  r25 : R 25 = reembPtr
  r26 : R 26 = reembLen
  r28 : R 28 = stLw
  r29 : R 29 = uPtr
  r30 : R 30 = numBase
  r31 : R 31 = denBase

private lemma nonReb_step_c {w r : ℕ} {e : Expr} {s2 : Stmt} {st : State} {v c0 K : ℕ}
    {p : Program} {ω : ℕ → Bool} {Q : Outcome → State → ℕ → Prop}
    (he : Expr.eval w st e = some v)
    (h2 : ∃ o out c, Runs w p ω s2 ⟨st.mem, Function.update st.regs r v, st.pos⟩ o out c ∧
      ∃ cRest, Q o out (K + cRest) ∧ (c0 + e.size + 2) + c ≤ K + cRest) :
    ∃ o out c, Runs w p ω (.assign r e ;; s2) st o out c ∧
      ∃ cRest, Q o out (K + cRest) ∧ c0 + c ≤ K + cRest := by
  obtain ⟨o, out, c, hr2, cRest, hq, hc⟩ := h2
  refine ⟨o, out, (e.size + 1) + c + 1,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, runs_assign_iff.mpr ⟨v, he, rfl, rfl, rfl⟩, hr2, rfl⟩),
    cRest, hq, by omega⟩

private lemma nonReb_finish {w c0 K : ℕ} {rest : Stmt} {st : State}
    {p : Program} {ω : ℕ → Bool} {Q : Outcome → State → ℕ → Prop}
    (hc : c0 ≤ K)
    (h : ∃ o out c, Runs w p ω rest st o out c ∧ Q o out (K + c)) :
    ∃ o out c, Runs w p ω rest st o out c ∧ ∃ cRest, Q o out (K + cRest) ∧ c0 + c ≤ K + cRest := by
  obtain ⟨o, out, c, hr, hq⟩ := h
  exact ⟨o, out, c, hr, c, hq, by omega⟩

private lemma nonReb_finish_slot {w c0 K0 K : ℕ} {s : Stmt} {st : State}
    {p : Program} {ω : ℕ → Bool} {Q : Outcome → State → ℕ → Prop}
    (hc : c0 ≤ K0)
    (h : ∃ o out c, Runs w p ω s st o out c ∧ ∃ cRest, Q o out (K + cRest) ∧ K0 + c ≤ K + cRest) :
    ∃ o out c, Runs w p ω s st o out c ∧ ∃ cRest, Q o out (K + cRest) ∧ c0 + c ≤ K + cRest := by
  obtain ⟨o, out, c, hr, cRest, hq, hle⟩ := h
  exact ⟨o, out, c, hr, cRest, hq, by omega⟩

private structure NonRebMetaRegs (R : ℕ → ℕ) (metaBase j slot handle branch prevLen Lk slotSz
    scratch gPtr eCap phiPtr lenPtr embPtr fPtr vCap : ℕ) : Prop where
  r0 : R 0 = metaBase
  r1 : R 1 = j
  r2 : R 2 = slot
  r3 : R 3 = handle
  r4 : R 4 = branch
  r5 : R 5 = prevLen
  r6 : R 6 = Lk
  r7 : R 7 = slotSz
  r8 : R 8 = scratch
  r12 : R 12 = gPtr
  r14 : R 14 = eCap
  r15 : R 15 = phiPtr
  r16 : R 16 = lenPtr
  r17 : R 17 = embPtr
  r18 : R 18 = fPtr
  r19 : R 19 = dgEPresBase gPtr vCap
  r20 : R 20 = dgEPresBase fPtr vCap

set_option maxHeartbeats 600000 in
private theorem nonReb_setup_slot_runs {w metaBase j slot handle branch prevLen Lk slotSz scratch
    d gPtr vCap eCap phiPtr lenPtr embPtr fPtr uGPtr uGLen fDelPtr fDelLen reembPtr reembLen
    stDesc stLw uPtr numBase denBase pos : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem R1 : ℕ → ℕ} {rest : Stmt}
    {Q : Outcome → State → ℕ → Prop}
    (hw16 : 16 < 2 ^ w) (hSlotW : slot + 12 < 2 ^ w) (hStDescW : stDesc + 2 < 2 ^ w)
    (hValsW : uGPtr < 2 ^ w ∧ uGLen < 2 ^ w ∧ fDelPtr < 2 ^ w ∧ fDelLen < 2 ^ w ∧
      reembPtr < 2 ^ w ∧ reembLen < 2 ^ w ∧ stLw < 2 ^ w ∧ uPtr < 2 ^ w ∧
      numBase < 2 ^ w ∧ denBase < 2 ^ w)
    (hR1 : NonRebMetaRegs R1 metaBase j slot handle branch prevLen Lk slotSz scratch
      gPtr eCap phiPtr lenPtr embPtr fPtr vCap)
    (hRdSlot : mem slot = uGPtr ∧ mem (slot + 1) = uGLen ∧
      mem (slot + 2) = fDelPtr ∧ mem (slot + 3) = fDelLen ∧
      mem (slot + 6) = reembPtr ∧ mem (slot + 7) = reembLen ∧
      mem (slot + 8) = stDesc ∧ mem (slot + 9) = stLw ∧
      mem (slot + 10) = uPtr ∧ mem stDesc = numBase ∧ mem (stDesc + 1) = denBase)
    (hCont : ∀ R : ℕ → ℕ,
      NonRebRegs R metaBase j slot handle branch prevLen Lk slotSz scratch d gPtr vCap eCap
        phiPtr lenPtr embPtr fPtr uGPtr uGLen fDelPtr fDelLen reembPtr reembLen stDesc stLw uPtr
        numBase denBase →
      ∃ o out c, Runs w p ω rest ⟨mem, R, pos⟩ o out c ∧ Q o out (260 + c)) :
    ∃ o out c,
      Runs w p ω
        (.assign 21 (.load (.reg 2)) ;;
         .assign 22 (.load (.bin .add (.reg 2) (.const 1))) ;;
         .assign 23 (.load (.bin .add (.reg 2) (.const 2))) ;;
         .assign 24 (.load (.bin .add (.reg 2) (.const 3))) ;;
         .assign 25 (.load (.bin .add (.reg 2) (.const 6))) ;;
         .assign 26 (.load (.bin .add (.reg 2) (.const 7))) ;;
         .assign 27 (.load (.bin .add (.reg 2) (.const 8))) ;;
         .assign 28 (.load (.bin .add (.reg 2) (.const 9))) ;;
         .assign 29 (.load (.bin .add (.reg 2) (.const 10))) ;;
         .assign 30 (.load (.reg 27)) ;;
         .assign 31 (.load (.bin .add (.reg 27) (.const 1))) ;;
         rest)
        ⟨mem, R1, pos⟩ o out c ∧ ∃ cRest, Q o out (260 + cRest) ∧ 160 + c ≤ 260 + cRest := by
  rcases hValsW with ⟨h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  rcases hRdSlot with ⟨s0, s1, s2, s3, s6, s7, s8, s9, s10, sn, sd⟩
  have hr2 := hR1.r2
  refine nonReb_step_c (v := uGPtr) (by eval_expr) ?_
  refine nonReb_step_c (v := uGLen) (by eval_expr) ?_
  refine nonReb_step_c (v := fDelPtr) (by eval_expr) ?_
  refine nonReb_step_c (v := fDelLen) (by eval_expr) ?_
  refine nonReb_step_c (v := reembPtr) (by eval_expr) ?_
  refine nonReb_step_c (v := reembLen) (by eval_expr) ?_
  refine nonReb_step_c (v := stDesc) (by eval_expr) ?_
  refine nonReb_step_c (v := stLw) (by eval_expr) ?_
  refine nonReb_step_c (v := uPtr) (by eval_expr) ?_
  refine nonReb_step_c (v := numBase) (by eval_expr) ?_
  refine nonReb_step_c (v := denBase) (by eval_expr) ?_
  refine nonReb_finish (by simp only [Expr.size]; omega) (hCont _
    ⟨by simp [hR1.r0], by simp [hR1.r1], by simp [hR1.r2], by simp [hR1.r3], by simp [hR1.r4],
     by simp [hR1.r5], by simp [hR1.r6], by simp [hR1.r7], by simp [hR1.r8], by simp [hR1.r12],
     by simp [hR1.r14], by simp [hR1.r15], by simp [hR1.r16], by simp [hR1.r17], by simp [hR1.r18],
     by simp [hR1.r19], by simp [hR1.r20], by simp, by simp, by simp, by simp, by simp, by simp,
     by simp, by simp, by simp, by simp⟩)

set_option maxHeartbeats 600000 in
/-- Execute the 23 setup assignments of `selectUpdateNonRebuiltLevelBody` into an opaque register
file `R` satisfying `NonRebRegs`, charging at most `260` steps. -/
theorem nonReb_setup_runs {w metaBase j slot handle branch prevLen Lk slotSz scratch
    d gPtr vCap eCap phiPtr lenPtr embPtr fPtr uGPtr uGLen fDelPtr fDelLen reembPtr reembLen
    stDesc stLw uPtr numBase denBase pos : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {rest : Stmt}
    {Q : Outcome → State → ℕ → Prop}
    (hw16 : 16 < 2 ^ w)
    (hMetaW : metaBase + selectLevelMetaSize d < 2 ^ w)
    (hjLe : j ≤ d)
    (hSlotW : slot + 12 < 2 ^ w)
    (hStDescW : stDesc + 2 < 2 ^ w)
    (hGW : gPtr + dynGraphSize vCap eCap < 2 ^ w)
    (hFW : fPtr + dynGraphSize vCap eCap < 2 ^ w)
    (hValsW : phiPtr < 2 ^ w ∧ lenPtr < 2 ^ w ∧ embPtr < 2 ^ w ∧
      uGPtr < 2 ^ w ∧ uGLen < 2 ^ w ∧ fDelPtr < 2 ^ w ∧ fDelLen < 2 ^ w ∧
      reembPtr < 2 ^ w ∧ reembLen < 2 ^ w ∧ stLw < 2 ^ w ∧ uPtr < 2 ^ w ∧
      numBase < 2 ^ w ∧ denBase < 2 ^ w)
    (hRdMeta : mem (metaBase + 1) = d ∧
      mem (metaBase + 2 + j) = gPtr ∧
      mem (metaBase + 2 + (d + 1) + j) = vCap ∧
      mem (metaBase + 2 + 2 * (d + 1) + j) = eCap ∧
      mem (metaBase + 2 + 3 * (d + 1) + j) = phiPtr ∧
      mem (metaBase + 2 + 4 * (d + 1) + j) = lenPtr ∧
      mem (metaBase + 2 + 5 * (d + 1) + j) = embPtr ∧
      mem (metaBase + 2 + 6 * (d + 1) + j) = fPtr)
    (hRdSlot : mem slot = uGPtr ∧ mem (slot + 1) = uGLen ∧
      mem (slot + 2) = fDelPtr ∧ mem (slot + 3) = fDelLen ∧
      mem (slot + 6) = reembPtr ∧ mem (slot + 7) = reembLen ∧
      mem (slot + 8) = stDesc ∧ mem (slot + 9) = stLw ∧
      mem (slot + 10) = uPtr ∧ mem stDesc = numBase ∧ mem (stDesc + 1) = denBase)
    (hQmono : ∀ o out c₁ c₂, c₁ ≤ c₂ → Q o out c₂ → Q o out c₁)
    (hCont : ∀ R : ℕ → ℕ,
      NonRebRegs R metaBase j slot handle branch prevLen Lk slotSz scratch d gPtr vCap eCap
        phiPtr lenPtr embPtr fPtr uGPtr uGLen fDelPtr fDelLen reembPtr reembLen stDesc stLw uPtr
        numBase denBase →
      ∃ o out c, Runs w p ω rest ⟨mem, R, pos⟩ o out c ∧ Q o out (260 + c)) :
    ∃ o out c,
      Runs w p ω
        (.assign 9 (.load (.bin .add (.reg 0) (.const 1))) ;;
         .assign 10 (.bin .add (.reg 9) (.const 1)) ;;
         .assign 11 (.bin .add (.reg 0) (.const smTableOff)) ;;
         .assign 12 (.load (.bin .add (.reg 11) (.reg 1))) ;;
         .assign 13 (.load (.bin .add (.bin .add (.reg 11) (.reg 10)) (.reg 1))) ;;
         .assign 14 (.load (.bin .add (.bin .add (.reg 11) (.bin .mul (.const 2) (.reg 10))) (.reg 1))) ;;
         .assign 15 (.load (.bin .add (.bin .add (.reg 11) (.bin .mul (.const 3) (.reg 10))) (.reg 1))) ;;
         .assign 16 (.load (.bin .add (.bin .add (.reg 11) (.bin .mul (.const 4) (.reg 10))) (.reg 1))) ;;
         .assign 17 (.load (.bin .add (.bin .add (.reg 11) (.bin .mul (.const 5) (.reg 10))) (.reg 1))) ;;
         .assign 18 (.load (.bin .add (.bin .add (.reg 11) (.bin .mul (.const 6) (.reg 10))) (.reg 1))) ;;
         .assign 19 (.bin .add (.bin .add (.reg 12) (.const 4)) (.bin .mul (.const 7) (.reg 13))) ;;
         .assign 20 (.bin .add (.bin .add (.reg 18) (.const 4)) (.bin .mul (.const 7) (.reg 13))) ;;
         .assign 21 (.load (.reg 2)) ;;
         .assign 22 (.load (.bin .add (.reg 2) (.const 1))) ;;
         .assign 23 (.load (.bin .add (.reg 2) (.const 2))) ;;
         .assign 24 (.load (.bin .add (.reg 2) (.const 3))) ;;
         .assign 25 (.load (.bin .add (.reg 2) (.const 6))) ;;
         .assign 26 (.load (.bin .add (.reg 2) (.const 7))) ;;
         .assign 27 (.load (.bin .add (.reg 2) (.const 8))) ;;
         .assign 28 (.load (.bin .add (.reg 2) (.const 9))) ;;
         .assign 29 (.load (.bin .add (.reg 2) (.const 10))) ;;
         .assign 30 (.load (.reg 27)) ;;
         .assign 31 (.load (.bin .add (.reg 27) (.const 1))) ;;
         rest)
        (startState [metaBase, j, slot, handle, branch, prevLen, Lk, slotSz, scratch] mem pos)
        o out c ∧ Q o out c := by
  have hMetaSz : selectLevelMetaSize d = 2 + 8 * (d + 1) := rfl
  have hDgSz : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  have hTableOff : smTableOff = 2 := rfl
  rcases hValsW with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  rcases hRdMeta with ⟨m1, m2, m3, m4, m5, m6, m7, m8⟩
  have hStart : ∃ o out c, Runs w p ω
      (.assign 9 (.load (.bin .add (.reg 0) (.const 1))) ;;
       .assign 10 (.bin .add (.reg 9) (.const 1)) ;;
       .assign 11 (.bin .add (.reg 0) (.const smTableOff)) ;;
       .assign 12 (.load (.bin .add (.reg 11) (.reg 1))) ;;
       .assign 13 (.load (.bin .add (.bin .add (.reg 11) (.reg 10)) (.reg 1))) ;;
       .assign 14 (.load (.bin .add (.bin .add (.reg 11) (.bin .mul (.const 2) (.reg 10))) (.reg 1))) ;;
       .assign 15 (.load (.bin .add (.bin .add (.reg 11) (.bin .mul (.const 3) (.reg 10))) (.reg 1))) ;;
       .assign 16 (.load (.bin .add (.bin .add (.reg 11) (.bin .mul (.const 4) (.reg 10))) (.reg 1))) ;;
       .assign 17 (.load (.bin .add (.bin .add (.reg 11) (.bin .mul (.const 5) (.reg 10))) (.reg 1))) ;;
       .assign 18 (.load (.bin .add (.bin .add (.reg 11) (.bin .mul (.const 6) (.reg 10))) (.reg 1))) ;;
       .assign 19 (.bin .add (.bin .add (.reg 12) (.const 4)) (.bin .mul (.const 7) (.reg 13))) ;;
       .assign 20 (.bin .add (.bin .add (.reg 18) (.const 4)) (.bin .mul (.const 7) (.reg 13))) ;;
       .assign 21 (.load (.reg 2)) ;;
       .assign 22 (.load (.bin .add (.reg 2) (.const 1))) ;;
       .assign 23 (.load (.bin .add (.reg 2) (.const 2))) ;;
       .assign 24 (.load (.bin .add (.reg 2) (.const 3))) ;;
       .assign 25 (.load (.bin .add (.reg 2) (.const 6))) ;;
       .assign 26 (.load (.bin .add (.reg 2) (.const 7))) ;;
       .assign 27 (.load (.bin .add (.reg 2) (.const 8))) ;;
       .assign 28 (.load (.bin .add (.reg 2) (.const 9))) ;;
       .assign 29 (.load (.bin .add (.reg 2) (.const 10))) ;;
       .assign 30 (.load (.reg 27)) ;;
       .assign 31 (.load (.bin .add (.reg 27) (.const 1))) ;;
       rest)
      (startState [metaBase, j, slot, handle, branch, prevLen, Lk, slotSz, scratch] mem pos)
      o out c ∧ ∃ cRest, Q o out (260 + cRest) ∧ 0 + c ≤ 260 + cRest := by
    dsimp only [startState]
    refine nonReb_step_c (v := d) (by eval_expr) ?_
    refine nonReb_step_c (v := d + 1) (by eval_expr) ?_
    refine nonReb_step_c (v := metaBase + 2) (by unfold smTableOff; eval_expr) ?_
    refine nonReb_step_c (v := gPtr) (by eval_expr) ?_
    refine nonReb_step_c (v := vCap) (by eval_expr) ?_
    refine nonReb_step_c (v := eCap) (by eval_expr) ?_
    refine nonReb_step_c (v := phiPtr) (by eval_expr) ?_
    refine nonReb_step_c (v := lenPtr) (by eval_expr) ?_
    refine nonReb_step_c (v := embPtr) (by eval_expr) ?_
    refine nonReb_step_c (v := fPtr) (by eval_expr) ?_
    refine nonReb_step_c (v := dgEPresBase gPtr vCap) (by unfold dgEPresBase; eval_expr) ?_
    refine nonReb_step_c (v := dgEPresBase fPtr vCap) (by unfold dgEPresBase; eval_expr) ?_
    refine nonReb_finish_slot (by simp only [Expr.size]; omega)
      (nonReb_setup_slot_runs (d := d) hw16 hSlotW hStDescW
        ⟨h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
        ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
         by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩
        hRdSlot hCont)
  obtain ⟨o, out, c, hr, cRest, hq, hc⟩ := hStart
  exact ⟨o, out, c, hr, hQmono o out c (260 + cRest) (by omega) hq⟩

end MinCostFlow.MinRatio

end
