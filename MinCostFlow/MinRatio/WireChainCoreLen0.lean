module

public import MinCostFlow.MinRatio.WireCoreLenK
public import MinCostFlow.MinRatio.WireChainCoreBatch
public import MinCostFlow.DynSpanner.Program.DynGraphBatch
public import MinCostFlow.MinRatio.TreeEditLayout
import WordRAM.Tactic

/-!
# Incremental edge-length updates and active tree-edit filtering (`WireChainCoreLens`)

Provides three deterministic Word-RAM helper procedures used in `ordChainUpdateCoreBody`:
1. `wireUpdateLen0FromBatchBody`: updates `levelLens[0]` in-place at the inserted edges of `U_int`
   from the external length array `l` via `inverse` in `O(|U_int| · L)` steps and zero heap space.
2. `wireUpdateCoreLenFromBatchBody`: updates `levelLens[j]` (`j > 0`) in-place at the inserted
   edges of `U_j` (`SmallBatchAt`) via `wireCoreLenEdgeBody` in `O(|U_j| · (max L Lw)^2)` steps.
3. `wireFilterActiveEditsBody`: filters a packed `TreeEditsAt` buffer, retaining all insertions
   and only those deletions whose `slots[e] ≠ 0`, in `O(|edits|)` steps.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program MinCostFlow.IPM.Machine

/-! ### 1. Updating level-0 lengths from `U_int` (`wireUpdateLen0FromBatchBody`) -/

/-- Procedure `[uIntBuf, inverse, l, len0Ptr, L]` (`reg 0..4`): for each `.insert ei _ _` in the
edge-only batch at `uIntBuf`, copies `L` limbs from `l + inverse[ei] * L` to `len0Ptr + ei * L`. -/
@[expose] def wireUpdateLen0FromBatchBody (copyWords : ℕ) : Stmt :=
  .assign 5 (.load (.reg 0)) ;;
  .assign 6 (.bin .add (.reg 0) (.const 1)) ;;
  forRange 7 (.const 0) (.reg 5)
    (.assign 8 (.load (.reg 6)) ;;
     .cond (.bin .eq (.reg 8) (.const 0))
       (.assign 9 (.load (.bin .add (.reg 6) (.const 1))) ;;
        .assign 10 (.load (.bin .add (.reg 1) (.reg 9))) ;;
        .call 11 copyWords
          [.bin .add (.reg 2) (.bin .mul (.reg 10) (.reg 4)),
           .bin .add (.reg 3) (.bin .mul (.reg 9) (.reg 4)), .reg 4] ;;
        .assign 6 (.bin .add (.reg 6) (.const 4)))
       (.assign 6 (.bin .add (.reg 6) (.const 2)))) ;;
  .ret (.const 0)

theorem wireUpdateLen0FromBatchBody_noRand (copyWords : ℕ) :
    (wireUpdateLen0FromBatchBody copyWords).NoRand := by
  simp [wireUpdateLen0FromBatchBody, forRange, forUp, Stmt.NoRand]

@[expose] def edgeRecOff (U : List Update) (k : ℕ) : ℕ :=
  ((U.take k).flatMap updateWords).length

theorem edgeRecOff_succ {U : List Update} {k : ℕ} (hk : k < U.length) :
    edgeRecOff U (k + 1) = edgeRecOff U k + (updateWords U[k]).length := by
  unfold edgeRecOff
  rw [List.take_succ_eq_append_getElem hk, List.flatMap_append]
  simp

theorem edgeBatch_rec_word {mem : ℕ → ℕ} {a : ℕ} {U : List Update}
    (hb : IPM.Machine.BatchAt mem a U) {k : ℕ} (hk : k < U.length)
    {j : ℕ} (hj : j < (updateWords U[k]).length) :
    mem (a + 1 + edgeRecOff U k + j) = (updateWords U[k])[j] ∧
      1 + edgeRecOff U k + j < (batchWords U).length := by
  have hsplit : U = U.take k ++ U[k] :: U.drop (k + 1) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have hfl : U.flatMap updateWords =
      (U.take k).flatMap updateWords ++ (updateWords U[k] ++ (U.drop (k + 1)).flatMap updateWords) := by
    conv_lhs => rw [hsplit]
    rw [List.flatMap_append, List.flatMap_cons]
  have hidx : (edgeRecOff U k + j) + 1 < (batchWords U).length := by
    simp only [batchWords, List.length_cons, hfl, List.length_append, edgeRecOff]; omega
  refine ⟨?_, by omega⟩
  have hr := hb ((edgeRecOff U k + j) + 1) hidx
  rw [show a + 1 + edgeRecOff U k + j = a + ((edgeRecOff U k + j) + 1) by omega, hr]
  simp only [batchWords, List.getElem_cons_succ]
  have h1 : (U.flatMap updateWords)[edgeRecOff U k + j]'(by simp only [hfl, List.length_append, edgeRecOff]; omega) =
      ((U.take k).flatMap updateWords ++ (updateWords U[k] ++ (U.drop (k + 1)).flatMap updateWords))[edgeRecOff U k + j]'(by
        simp only [List.length_append, edgeRecOff]; omega) := by congr 1
  rw [h1, List.getElem_append_right (by dsimp [edgeRecOff]; omega)]
  simp only [edgeRecOff, Nat.add_sub_cancel_left]
  exact List.getElem_append_left hj

/-- Execute `wireUpdateLen0FromBatchBody`: updates `len0Ptr` in-place at every inserted edge of
`U_int`, preserving all memory outside `[len0Ptr, len0Ptr + eCap * L)`. -/
theorem wireUpdateLen0FromBatchBody_runs
    {w copyWords uIntBuf inverse l len0Ptr L P m eCap intCap pos : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {G0 : MGraph} {U_int : List Update}
    {i2e : ℕ → ℕ} {oldℓ newℓ : ℕ → ℝ}
    (hCopy : MeetsContract w p copyWords (copyWordsContract w))
    (hBatch : IPM.Machine.BatchAt mem uIntBuf U_int)
    (hEdgeOnly : ∀ u ∈ U_int, IsEdgeUpdate u)
    (hInv : ∀ u ∈ U_int, match u with
      | .insert ei _ _ => ei < intCap ∧ ei < eCap ∧ mem (inverse + ei) = i2e ei ∧ i2e ei < m ∧
          Num.Valid mem (l + i2e ei * L) 4 L ∧
          Num.fixVal mem (l + i2e ei * L) 4 L P = newℓ ei
      | _ => True)
    (hOldLen : EdgeValuesAt mem len0Ptr 4 L P G0.E oldℓ)
    (hAgreeOld : ∀ ei ∈ (G0.applyBatch U_int).E, (¬ ∃ u ∈ U_int, u.Inserts ei) →
      ei ∈ G0.E ∧ oldℓ ei = newℓ ei)
    (hMemIns : ∀ ei ∈ (G0.applyBatch U_int).E, (∃ u ∈ U_int, u.Inserts ei) →
      ∃ k, ∃ hk : k < U_int.length, U_int[k].Inserts ei)
    (hDisjBatch : uIntBuf + (batchWords U_int).length ≤ len0Ptr ∨ len0Ptr + eCap * L ≤ uIntBuf)
    (hDisjInv : 0 < eCap → (inverse + intCap ≤ len0Ptr ∨ len0Ptr + eCap * L ≤ inverse))
    (hDisjL : 0 < eCap → (l + m * L ≤ len0Ptr ∨ len0Ptr + eCap * L ≤ l))
    (hBatchW : uIntBuf + (batchWords U_int).length < 2 ^ w)
    (hInvW : inverse + intCap < 2 ^ w)
    (hLW : l + m * L < 2 ^ w)
    (hLenW : len0Ptr + eCap * L < 2 ^ w)
    (hLValW : L < 2 ^ w) (hw4 : 4 < 2 ^ w) :
    ∃ out cost,
      Runs w p ω (wireUpdateLen0FromBatchBody copyWords)
        (startState [uIntBuf, inverse, l, len0Ptr, L] mem pos) (.returned 0) out cost ∧
      cost ≤ U_int.length * (17 * L + 70) + 35 ∧
      EdgeValuesAt out.mem len0Ptr 4 L P (G0.applyBatch U_int).E newℓ ∧
      ∀ a, (a < len0Ptr ∨ len0Ptr + eCap * L ≤ a) → out.mem a = mem a := by
  have hw1 : 1 < 2 ^ w := by omega
  have hLenB0 : mem uIntBuf = U_int.length := by
    simpa [batchWords] using hBatch 0 (by simp [batchWords])
  have hULenW : U_int.length < 2 ^ w := by
    have h2 : ∀ L : List Update, (∀ u ∈ L, IsEdgeUpdate u) → 2 * L.length ≤ (L.flatMap updateWords).length := by
      intro L hL
      induction L with
      | nil => simp
      | cons u rest ih =>
        have hu := hL u List.mem_cons_self
        have hr := ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))
        cases u with
        | insert _ _ _ => simp only [List.flatMap_cons, List.length_append, updateWords, List.length_cons, List.length_nil]; omega
        | delete _ => simp only [List.flatMap_cons, List.length_append, updateWords, List.length_cons, List.length_nil]; omega
        | split _ _ _ _ => exact hu.elim
    have h2' := h2 U_int hEdgeOnly
    simp only [batchWords, List.length_cons] at hBatchW; omega
  let s0 := startState [uIntBuf, inverse, l, len0Ptr, L] mem pos
  let s1 := { s0 with regs := Function.update s0.regs 5 U_int.length }
  let s2 := { s1 with regs := Function.update s1.regs 6 (uIntBuf + 1) }
  have r1 : Runs w p ω (.assign 5 (.load (.reg 0))) s0 .normal s1 3 :=
    runs_assign_iff.mpr ⟨U_int.length, by simp [Expr.eval, s0, startState, hLenB0], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 6 (.bin .add (.reg 0) (.const 1))) s1 .normal s2 4 :=
    runs_assign_iff.mpr ⟨uIntBuf + 1, by
      simp [Expr.eval, BinOp.eval, s1, s0, startState, hw1,
        show uIntBuf + 1 < 2 ^ w by simp [batchWords] at hBatchW; omega], rfl, rfl, rfl⟩
  let Inv (i : ℕ) (s : State) : Prop :=
    s.regs 0 = uIntBuf ∧ s.regs 1 = inverse ∧ s.regs 2 = l ∧ s.regs 3 = len0Ptr ∧
    s.regs 4 = L ∧ s.regs 5 = U_int.length ∧ s.regs 6 = uIntBuf + 1 + edgeRecOff U_int i ∧
    s.regs 7 = i ∧
    (∀ a, (a < len0Ptr ∨ len0Ptr + eCap * L ≤ a) → s.mem a = mem a) ∧
    (∀ ei, ei < eCap → (¬ ∃ j, ∃ hj : j < U_int.length, j < i ∧ U_int[j].Inserts ei) →
      ∀ t < L, s.mem (len0Ptr + ei * L + t) = mem (len0Ptr + ei * L + t)) ∧
    (∀ j, j < i → ∀ hi : j < U_int.length, match U_int[j] with
      | .insert ei _ _ => Num.Valid s.mem (len0Ptr + ei * L) 4 L ∧
          Num.fixVal s.mem (len0Ptr + ei * L) 4 L P = newℓ ei
      | _ => True)
  let stepCost := 17 * L + 61
  have hloop := Triple.forRange_le (w := w) (p := p) (r := 7) (lo := .const 0) (hi := .reg 5)
    (P := fun s => s = s2) (Inv := Inv) (fun _ => stepCost) 0 U_int.length (Nat.zero_le _) hw1
    (fun _ => hULenW)
    (fun s hs => by
      subst hs
      refine ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega],
        by simp [s2, s1, s0, startState], by simp [s2, s1, s0, startState],
        by simp [s2, s1, s0, startState], by simp [s2, s1, s0, startState],
        by simp [s2, s1, s0, startState], by simp [s2, s1],
        by simp [s2, edgeRecOff], by simp, fun _ _ => rfl, fun _ _ _ _ _ => rfl,
        fun j hj _ => absurd hj (Nat.not_lt_zero _)⟩)
    (fun _ _ _ _ h => h.2.2.2.2.2.2.2.1)
    (fun _ s _ _ h => by simp [Expr.eval, h.2.2.2.2.2.1])
    (fun i _ hi => by
      intro s ω' hI
      obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, hFr, hKeep, hDone⟩ := hI
      have huE := hEdgeOnly U_int[i] (List.getElem_mem hi)
      have hRec0 := edgeBatch_rec_word hBatch hi (j := 0) (by
        cases h : U_int[i] with
        | insert _ _ _ => simp [updateWords]
        | delete _ => simp [updateWords]
        | split _ _ _ _ => rw [h] at huE; exact huE.elim)
      have hPtrOut : ∀ j < (updateWords U_int[i]).length,
          uIntBuf + 1 + edgeRecOff U_int i + j < len0Ptr ∨
          len0Ptr + eCap * L ≤ uIntBuf + 1 + edgeRecOff U_int i + j := fun j hj => by
        have hlt := (edgeBatch_rec_word hBatch hi hj).2
        rcases hDisjBatch with h | h <;> omega
      have hTagMem : s.mem (uIntBuf + 1 + edgeRecOff U_int i) = (updateWords U_int[i])[0]'(by
          cases h : U_int[i] with
          | insert _ _ _ => simp [updateWords]
          | delete _ => simp [updateWords]
          | split _ _ _ _ => rw [h] at huE; exact huE.elim) := by
        have hfr0 := hFr (uIntBuf + 1 + edgeRecOff U_int i) (by
          simpa using hPtrOut 0 (by
            cases h : U_int[i] with
            | insert _ _ _ => simp [updateWords]
            | delete _ => simp [updateWords]
            | split _ _ _ _ => rw [h] at huE; exact huE.elim))
        rw [hfr0]; simpa using hRec0.1
      cases hUi : U_int[i] with
      | split _ _ _ _ => rw [hUi] at huE; exact huE.elim
      | delete ei =>
        have hTagVal : s.mem (uIntBuf + 1 + edgeRecOff U_int i) = 1 := by
          rw [hTagMem]; simp [hUi, updateWords]
        let t1 := { s with regs := Function.update s.regs 8 1 }
        let t2 := { t1 with regs := Function.update t1.regs 6 (uIntBuf + 1 + edgeRecOff U_int (i + 1)) }
        have hOffNext : edgeRecOff U_int (i + 1) = edgeRecOff U_int i + 2 := by
          rw [edgeRecOff_succ hi, hUi]; simp [updateWords]
        have hNextW : uIntBuf + 1 + edgeRecOff U_int (i + 1) < 2 ^ w := by
          have := (edgeBatch_rec_word hBatch hi (j := 1) (by simp [hUi, updateWords])).2; omega
        have rt1 : Runs w p ω' (.assign 8 (.load (.reg 6))) s .normal t1 3 :=
          runs_assign_iff.mpr ⟨1, by simp [Expr.eval, h6, hTagVal], rfl, rfl, rfl⟩
        have rt2 : Runs w p ω' (.assign 6 (.bin .add (.reg 6) (.const 2))) t1 .normal t2 4 :=
          runs_assign_iff.mpr ⟨uIntBuf + 1 + edgeRecOff U_int (i + 1), by
            simp only [Expr.eval, BinOp.eval, t1, h6, show 2 < 2 ^ w by omega,
              show uIntBuf + 1 + edgeRecOff U_int i + 2 < 2 ^ w by omega, ↓reduceIte,
              Option.some.injEq, Function.update_of_ne (by decide : (6 : ℕ) ≠ 8)]
            omega, rfl, rfl, rfl⟩
        have rCond : Runs w p ω'
            (.cond (.bin .eq (.reg 8) (.const 0))
              (.assign 9 (.load (.bin .add (.reg 6) (.const 1))) ;;
               .assign 10 (.load (.bin .add (.reg 1) (.reg 9))) ;;
               .call 11 copyWords
                 [.bin .add (.reg 2) (.bin .mul (.reg 10) (.reg 4)),
                  .bin .add (.reg 3) (.bin .mul (.reg 9) (.reg 4)),
                  .reg 4] ;;
               .assign 6 (.bin .add (.reg 6) (.const 4)))
              (.assign 6 (.bin .add (.reg 6) (.const 2))))
            t1 .normal t2 8 :=
          runs_cond_iff.mpr ⟨0, 4, by simp [Expr.eval, BinOp.eval, t1, show (0 : ℕ) < 2 ^ w by omega],
            by simpa using rt2, by simp [Expr.size]⟩
        refine ⟨.normal, t2, 3 + 8 + 1, runs_seq_iff.mpr (Or.inr ⟨t1, 3, 8, rt1, rCond, rfl⟩),
          ⟨⟨by simp [t2, t1, h0], by simp [t2, t1, h1], by simp [t2, t1, h2], by simp [t2, t1, h3],
            by simp [t2, t1, h4], by simp [t2, t1, h5], by simp [t2], by simp,
            hFr, fun x hx hni t ht => hKeep x hx (fun ⟨j, hjLt, hj, hjI⟩ => hni ⟨j, hjLt, by omega, hjI⟩) t ht,
            fun j hj hjLt => by
              by_cases hji : j = i
              · subst hji; simp [hUi]
              · exact hDone j (by omega) hjLt⟩, by simp [t2, t1, h7]⟩, by dsimp [stepCost]; omega⟩
      | insert ei u v =>
        have hInvI := hInv (.insert ei u v) (hUi ▸ List.getElem_mem hi)
        obtain ⟨heiInt, heiCap, hInvMem, heLtM, hLV, hLF⟩ := hInvI
        have hTagVal : s.mem (uIntBuf + 1 + edgeRecOff U_int i) = 0 := by
          rw [hTagMem]; simp [hUi, updateWords]
        have hRec1 := edgeBatch_rec_word hBatch hi (j := 1) (by simp [hUi, updateWords])
        have hEiMem : s.mem (uIntBuf + 1 + edgeRecOff U_int i + 1) = ei := by
          rw [hFr _ (hPtrOut 1 (by simp [hUi, updateWords])), hRec1.1]; simp [hUi, updateWords]
        have hInvS : s.mem (inverse + ei) = i2e ei := by
          rw [hFr _ (by rcases hDisjInv (by omega) with h | h <;> omega)]; exact hInvMem
        have hOffNext : edgeRecOff U_int (i + 1) = edgeRecOff U_int i + 4 := by
          rw [edgeRecOff_succ hi, hUi]; simp [updateWords]
        have hNextW : uIntBuf + 1 + edgeRecOff U_int (i + 1) < 2 ^ w := by
          have := (edgeBatch_rec_word hBatch hi (j := 3) (by simp [hUi, updateWords])).2; omega
        have heLW : i2e ei * L + L ≤ m * L := by
          simpa [Nat.succ_mul] using Nat.mul_le_mul_right L (Nat.succ_le_of_lt heLtM)
        have heiLW : ei * L + L ≤ eCap * L := by
          simpa [Nat.succ_mul] using Nat.mul_le_mul_right L (Nat.succ_le_of_lt heiCap)
        let t1 := { s with regs := Function.update s.regs 8 0 }
        let t2 := { t1 with regs := Function.update t1.regs 9 ei }
        let t3 := { t2 with regs := Function.update t2.regs 10 (i2e ei) }
        have rt1 : Runs w p ω' (.assign 8 (.load (.reg 6))) s .normal t1 3 :=
          runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h6, hTagVal], rfl, rfl, rfl⟩
        have rt2 : Runs w p ω' (.assign 9 (.load (.bin .add (.reg 6) (.const 1)))) t1 .normal t2 5 :=
          runs_assign_iff.mpr ⟨ei, by
            simp [Expr.eval, BinOp.eval, t1, h6, hw1, show uIntBuf + 1 + edgeRecOff U_int i + 1 < 2 ^ w by omega,
              hEiMem], rfl, rfl, rfl⟩
        have rt3 : Runs w p ω' (.assign 10 (.load (.bin .add (.reg 1) (.reg 9)))) t2 .normal t3 5 :=
          runs_assign_iff.mpr ⟨i2e ei, by
            simp [Expr.eval, BinOp.eval, t2, t1, h1, show inverse + ei < 2 ^ w by omega, hInvS], rfl, rfl, rfl⟩
        have hCopyPre : (copyWordsContract w).pre [l + i2e ei * L, len0Ptr + ei * L, L] t3.mem := by
          refine ⟨l + i2e ei * L, len0Ptr + ei * L, L, rfl, hw1, by omega, by omega, ?_⟩
          rcases hDisjL (by omega) with h | h
          · exact Or.inr (by omega)
          · exact Or.inl (by omega)
        obtain ⟨t4, cCopy, _, rt4, hpCopy, _, ht4Regs, hcCopy⟩ :=
          runs_call_of_meetsContract (r := 11)
            (args := [.bin .add (.reg 2) (.bin .mul (.reg 10) (.reg 4)),
              .bin .add (.reg 3) (.bin .mul (.reg 9) (.reg 4)), .reg 4])
            hCopy (st := t3) (vs := [l + i2e ei * L, len0Ptr + ei * L, L])
            (by simp [evalArgs, Expr.eval, BinOp.eval, t3, t2, t1, h2, h3, h4,
              show i2e ei * L < 2 ^ w by omega, show l + i2e ei * L < 2 ^ w by omega,
              show ei * L < 2 ^ w by omega, show len0Ptr + ei * L < 2 ^ w by omega])
            (by simp [show l + i2e ei * L < 2 ^ w by omega, show len0Ptr + ei * L < 2 ^ w by omega, hLValW])
            hCopyPre ω'
        obtain ⟨_, _, _, hArgsC, _, hCopied, hFrCopy⟩ := hpCopy
        simp only [List.cons.injEq, and_true] at hArgsC
        obtain ⟨rfl, rfl, rfl⟩ := hArgsC
        let t5 := { t4 with regs := Function.update t4.regs 6 (uIntBuf + 1 + edgeRecOff U_int (i + 1)) }
        have rt5 : Runs w p ω' (.assign 6 (.bin .add (.reg 6) (.const 4))) t4 .normal t5 4 :=
          runs_assign_iff.mpr ⟨uIntBuf + 1 + edgeRecOff U_int (i + 1), by
            simp only [Expr.eval, BinOp.eval, ht4Regs 6 (by decide), t3, t2, t1, h6, hw4,
              show uIntBuf + 1 + edgeRecOff U_int i + 4 < 2 ^ w by omega, ↓reduceIte,
              Option.some.injEq, Function.update_of_ne (by decide : (6 : ℕ) ≠ 10),
              Function.update_of_ne (by decide : (6 : ℕ) ≠ 9),
              Function.update_of_ne (by decide : (6 : ℕ) ≠ 8)]
            omega, rfl, rfl, rfl⟩
        have rBranch : Runs w p ω' _ t1 .normal t5 (5 + (5 + (cCopy + 4 + 1) + 1) + 1) :=
          runs_seq_iff.mpr (Or.inr ⟨t2, 5, _, rt2,
            runs_seq_iff.mpr (Or.inr ⟨t3, 5, _, rt3,
              runs_seq_iff.mpr (Or.inr ⟨t4, cCopy, 4, rt4, rt5, rfl⟩),
              rfl⟩), rfl⟩)
        have rCond : Runs w p ω'
            (.cond (.bin .eq (.reg 8) (.const 0)) _ (.assign 6 (.bin .add (.reg 6) (.const 2))))
            t1 .normal t5 (3 + (5 + (5 + (cCopy + 4 + 1) + 1) + 1) + 1) :=
          runs_cond_iff.mpr ⟨1, _, by simp [Expr.eval, BinOp.eval, t1, hw1], by simpa using rBranch,
            by simp [Expr.size]⟩
        have hNewVal : Num.Valid t5.mem (len0Ptr + ei * L) 4 L ∧
            Num.fixVal t5.mem (len0Ptr + ei * L) 4 L P = newℓ ei := by
          have hag (k : ℕ) (hk : k < L) : t5.mem (len0Ptr + ei * L + k) = mem (l + i2e ei * L + k) :=
            (hCopied k hk).trans (hFr _ (by rcases hDisjL (by omega) with h | h <;> omega))
          refine ⟨fun k hk => by rw [hag k hk]; exact hLV k hk, ?_⟩
          rw [← hLF]; unfold Num.fixVal; congr 2; exact Num.intVal_congr hag
        have hStepCost : cCopy ≤ 17 * L + 22 := by
          simp only [copyWordsContract, argsSize, Expr.size] at hcCopy
          omega
        refine ⟨.normal, t5, _, runs_seq_iff.mpr (Or.inr ⟨t1, 3, _, rt1, rCond, rfl⟩),
          ⟨⟨by simp [t5, ht4Regs 0 (by decide), t3, t2, t1, h0],
            by simp [t5, ht4Regs 1 (by decide), t3, t2, t1, h1],
            by simp [t5, ht4Regs 2 (by decide), t3, t2, t1, h2],
            by simp [t5, ht4Regs 3 (by decide), t3, t2, t1, h3],
            by simp [t5, ht4Regs 4 (by decide), t3, t2, t1, h4],
            by simp [t5, ht4Regs 5 (by decide), t3, t2, t1, h5],
            by simp [t5], by simp,
            fun a ha => (hFrCopy a (by rcases ha with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)])).trans (hFr a ha),
            fun x hx hni t ht => by
              have hne : x ≠ ei := fun h => hni ⟨i, hi, Nat.lt_succ_self i, by simp [hUi, h, Update.Inserts]⟩
              have hout : len0Ptr + x * L + t < len0Ptr + ei * L ∨ len0Ptr + ei * L + L ≤ len0Ptr + x * L + t := by
                rcases lt_or_gt_of_ne hne with hlt | hgt
                · left; have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hlt); rw [Nat.succ_mul] at this; omega
                · right; have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hgt); rw [Nat.succ_mul] at this; omega
              exact (hFrCopy _ hout).trans (hKeep x hx (fun ⟨j, hjLt, hj, hjI⟩ => hni ⟨j, hjLt, by omega, hjI⟩) t ht),
            fun j hj hjLt => by
              by_cases hji : j = i
              · subst hji; simp only [hUi]; exact hNewVal
              · have hd := hDone j (by omega) hjLt
                cases hUj : U_int[j] with
                | delete _ => trivial
                | split _ _ _ _ => trivial
                | insert ej _ _ =>
                  simp only [hUj] at hd
                  by_cases heq : ej = ei
                  · subst heq; exact hNewVal
                  · have hout (t : ℕ) (ht : t < L) :
                        len0Ptr + ej * L + t < len0Ptr + ei * L ∨ len0Ptr + ei * L + L ≤ len0Ptr + ej * L + t := by
                      rcases lt_or_gt_of_ne heq with hlt | hgt
                      · left; have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hlt); rw [Nat.succ_mul] at this; omega
                      · right; have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hgt); rw [Nat.succ_mul] at this; omega
                    refine ⟨fun t ht => by rw [hFrCopy _ (hout t ht)]; exact hd.1 t ht, ?_⟩
                    rw [← hd.2]; unfold Num.fixVal; congr 2
                    exact Num.intVal_congr (fun t ht => hFrCopy _ (hout t ht))⟩,
          by simp [t5, ht4Regs 7 (by decide), t3, t2, t1, h7]⟩, by dsimp [stepCost]; omega⟩)
  obtain ⟨o, out, cLoop, rLoop, hout, hcLoop⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hout
  | normal =>
    obtain ⟨_, _, _, _, _, _, _, _, hFrEnd, hKeepEnd, hDoneEnd⟩ := hout
    have rRet : Runs w p ω (.ret (.const 0)) out (.returned 0) out 2 :=
      runs_ret_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
    have rAll := runs_seq_iff.mpr (Or.inr ⟨s1, 3, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 4, _, r2,
        runs_seq_iff.mpr (Or.inr ⟨out, cLoop, 2, rLoop, rRet, rfl⟩), rfl⟩), rfl⟩)
    refine ⟨out, _, rAll, ?_, ?_, hFrEnd⟩
    · have hrc : rangeCost (fun _ => stepCost) 0 U_int.length = U_int.length * stepCost := by simp [rangeCost]
      simp only [Expr.size, hrc] at hcLoop
      have hm : U_int.length * stepCost + U_int.length * 9 = U_int.length * (17 * L + 70) := by
        dsimp [stepCost]; ring
      omega
    · intro ei hei
      by_cases hIns : ∃ u ∈ U_int, u.Inserts ei
      · obtain ⟨k, hk, hkIns⟩ := hMemIns ei hei hIns
        have hd := hDoneEnd k hk hk
        cases hUk : U_int[k] with
        | delete _ => simp [hUk, Update.Inserts] at hkIns
        | split _ _ _ _ => simp [hUk, Update.Inserts] at hkIns
        | insert ej _ _ =>
          simp only [hUk, Update.Inserts] at hkIns hd
          subst hkIns; exact hd
      · obtain ⟨heG0, hEqL⟩ := hAgreeOld ei hei hIns
        have hNoJ : ¬ ∃ j, ∃ hj : j < U_int.length, j < U_int.length ∧ U_int[j].Inserts ei :=
          fun ⟨j, hj, _, hji⟩ => hIns ⟨U_int[j], List.getElem_mem hj, hji⟩
        have hag (t : ℕ) (ht : t < L) : out.mem (len0Ptr + ei * L + t) = mem (len0Ptr + ei * L + t) := by
          by_cases heiCap : ei < eCap
          · exact hKeepEnd ei heiCap hNoJ t ht
          · have hge : eCap * L ≤ ei * L := Nat.mul_le_mul_right L (Nat.le_of_not_lt heiCap)
            exact hFrEnd _ (Or.inr (by omega))
        refine ⟨fun t ht => by rw [hag t ht]; exact (hOldLen ei heG0).1 t ht, ?_⟩
        rw [← hEqL, ← (hOldLen ei heG0).2]; unfold Num.fixVal; congr 2
        exact Num.intVal_congr hag

end MinCostFlow.MinRatio
