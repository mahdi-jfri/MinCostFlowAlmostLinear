module

public import MinCostFlow.MinRatio.WireChainCoreOp0KFBL
public import MinCostFlow.MinRatio.WireSelectUpdate
public import MinCostFlow.SparseCore.Program.AssemblyContractLayout
import Mathlib.Tactic

/-!
# Select-block output helpers and `KFRBL` op `0` combiner (`WireChainCoreSelectOutKFBL`)

Provides the building blocks needed to expose the full 10-word per-level select-block update record
(`LevelDiffListsAt` + stretch table) from `ordChainUpdateCoreBody`:

1. `coreBatchTouchedEdges` and `wireCollectTouchedEdgesBody`: scans a `SmallBatchAt` buffer `U` in
   `≤ 60 * U.length + 35` steps and `U.length` words to collect every edge ID inserted (including
   re-insertions) or deleted by `U`, covering both `uG` and `uS` in `LevelDiffCovers`.
2. `reembListAt_of_readList`: bridges `BranchOutReembAt`'s `readList` predicate directly to
   `ReembListAt`.
3. `ordCoreUpdateKFRBLOut_runs`: combines `R.Implements` for `sparseCoreOrdMachineContractKFRBL`
   with `SparseCoreUpdateOutFootAt` (unchanged from `WireChainCoreOp0KFBL.lean`) via `Runs.det`
   to obtain both `BranchOutReembAt` (`reembPtr, reembLen`) and `BranchOutFChgAt` + placement +
   `edMul` output-edit bounds on the exact same run of `op 0`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.Chain.Ordered
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore MinCostFlow.SparseCore.Program

/-! ### 1. Collecting all touched (inserted or deleted) edges of a batch -/

/-- All edge IDs inserted (including re-insertions) or deleted by a batch `U`, in batch order. -/
@[expose] def coreBatchTouchedEdges : List Update → List ℕ
  | [] => []
  | .insert e _ _ :: rest => e :: coreBatchTouchedEdges rest
  | .delete e :: rest => e :: coreBatchTouchedEdges rest
  | .split _ _ _ _ :: rest => coreBatchTouchedEdges rest

theorem coreBatchTouchedEdges_length_le (U : List Update) :
    (coreBatchTouchedEdges U).length ≤ U.length := by
  induction U with
  | nil => simp [coreBatchTouchedEdges]
  | cons u rest ih => cases u <;> simp [coreBatchTouchedEdges] <;> omega

theorem coreBatchTouchedEdges_append (U₁ U₂ : List Update) :
    coreBatchTouchedEdges (U₁ ++ U₂) = coreBatchTouchedEdges U₁ ++ coreBatchTouchedEdges U₂ := by
  induction U₁ with
  | nil => rfl
  | cons u rest ih => cases u <;> simp [coreBatchTouchedEdges, ih]

theorem mem_coreBatchTouchedEdges_iff (e : ℕ) (U : List Update) :
    e ∈ coreBatchTouchedEdges U ↔ (∃ u v, Update.insert e u v ∈ U) ∨ Update.delete e ∈ U := by
  induction U with
  | nil => simp [coreBatchTouchedEdges]
  | cons u rest ih =>
    cases u with
    | insert e' u' v' =>
      simp only [coreBatchTouchedEdges, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨u'', v'', hm⟩ | hm)
        · exact Or.inl ⟨u', v', Or.inl rfl⟩
        · exact Or.inl ⟨u'', v'', Or.inr hm⟩
        · exact Or.inr (Or.inr hm)
      · rintro (⟨u'', v'', h | hm⟩ | (h | hm))
        · cases h; exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨u'', v'', hm⟩)
        · cases h
        · exact Or.inr (Or.inr hm)
    | delete e' =>
      simp only [coreBatchTouchedEdges, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨u'', v'', hm⟩ | hm)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl ⟨u'', v'', Or.inr hm⟩
        · exact Or.inr (Or.inr hm)
      · rintro (⟨u'', v'', h | hm⟩ | (h | hm))
        · cases h
        · exact Or.inr (Or.inl ⟨u'', v'', hm⟩)
        · cases h; exact Or.inl rfl
        · exact Or.inr (Or.inr hm)
    | split _ _ _ _ =>
      simp only [coreBatchTouchedEdges, List.mem_cons, ih]
      constructor
      · rintro (⟨u'', v'', hm⟩ | hm)
        · exact Or.inl ⟨u'', v'', Or.inr hm⟩
        · exact Or.inr (Or.inr hm)
      · rintro (⟨u'', v'', h | hm⟩ | (h | hm))
        · cases h
        · exact Or.inl ⟨u'', v'', hm⟩
        · cases h
        · exact Or.inr hm

theorem mem_coreBatchTouchedEdges_of_insert {e : ℕ} {U : List Update}
    (h : ∃ u ∈ U, Update.Inserts e u) : e ∈ coreBatchTouchedEdges U := by
  obtain ⟨u, hu, hIns⟩ := h
  cases u with
  | insert e' u' v' =>
    have he : e' = e := by simpa [Update.Inserts] using hIns
    subst he
    exact (mem_coreBatchTouchedEdges_iff e' U).mpr (Or.inl ⟨u', v', hu⟩)
  | delete _ => simp [Update.Inserts] at hIns
  | split _ _ _ _ => simp [Update.Inserts] at hIns

theorem mem_coreBatchTouchedEdges_of_symmDiff {G : MGraph} {U : List Update} {e : ℕ}
    (h : e ∈ (G.applyBatch U).E ↔ e ∉ G.E) : e ∈ coreBatchTouchedEdges U := by
  induction U generalizing G with
  | nil =>
    simp [MGraph.applyBatch] at h
  | cons u rest ih =>
    cases u with
    | insert e' u' v' =>
      by_cases he : e = e'
      · subst he; simp [coreBatchTouchedEdges]
      · simp only [coreBatchTouchedEdges, List.mem_cons]
        right
        refine ih (G := G.applyUpdate (.insert e' u' v')) ?_
        have hE : (e ∈ (G.applyUpdate (.insert e' u' v')).E) ↔ e ∈ G.E := by
          simp [MGraph.applyUpdate, he]
        simpa [MGraph.applyBatch, hE] using h
    | delete e' =>
      by_cases he : e = e'
      · subst he; simp [coreBatchTouchedEdges]
      · simp only [coreBatchTouchedEdges, List.mem_cons]
        right
        refine ih (G := G.applyUpdate (.delete e')) ?_
        have hE : (e ∈ (G.applyUpdate (.delete e')).E) ↔ e ∈ G.E := by
          simp [MGraph.applyUpdate, he]
        simpa [MGraph.applyBatch, hE] using h
    | split v v' inc Sh =>
      simp only [coreBatchTouchedEdges]
      refine ih (G := G.applyUpdate (.split v v' inc Sh)) ?_
      have hE : (G.applyUpdate (.split v v' inc Sh)).E = G.E := by
        simp [MGraph.applyUpdate]
      simpa [MGraph.applyBatch, hE] using h

/-- Procedure body `[batchPtr, outBuf] → cnt`: scans a `SmallBatchAt` buffer at `batchPtr`,
appending every inserted or deleted edge ID into `outBuf` and returning the count. -/
@[expose] def wireCollectTouchedEdgesBody : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.bin .add (.reg 0) (.const 1)) ;;
  .assign 4 (.const 0) ;;
  forRange 5 (.const 0) (.reg 2)
    (.assign 6 (.load (.reg 3)) ;;
     .cond (.bin .eq (.reg 6) (.const 0))
       (.assign 7 (.load (.bin .add (.reg 3) (.const 1))) ;;
        .store (.bin .add (.reg 1) (.reg 4)) (.reg 7) ;;
        .assign 4 (.bin .add (.reg 4) (.const 1)) ;;
        .assign 3 (.bin .add (.reg 3) (.const 4)))
       (.cond (.bin .eq (.reg 6) (.const 1))
          (.assign 7 (.load (.bin .add (.reg 3) (.const 1))) ;;
           .store (.bin .add (.reg 1) (.reg 4)) (.reg 7) ;;
           .assign 4 (.bin .add (.reg 4) (.const 1)) ;;
           .assign 3 (.bin .add (.reg 3) (.const 2)))
          (.assign 7 (.load (.bin .add (.reg 3) (.const 3))) ;;
           .assign 8 (.load (.bin .add (.reg 3) (.const 4))) ;;
           .assign 3 (.bin .add (.bin .add (.bin .add (.reg 3) (.const 5)) (.reg 7)) (.reg 8))))) ;;
  .ret (.reg 4)

theorem wireCollectTouchedEdgesBody_noRand : wireCollectTouchedEdgesBody.NoRand := by
  simp [wireCollectTouchedEdgesBody, forRange, forUp, Stmt.NoRand]

set_option maxHeartbeats 600000 in
/-- Running `wireCollectTouchedEdgesBody` on a `SmallBatchAt` buffer writes
`ListAt out.mem outBuf (coreBatchTouchedEdges U)` in `≤ 60 * U.length + 35` steps using at most
`U.length` words at `outBuf`. -/
theorem wireCollectTouchedEdgesBody_runs {w batchPtr outBuf totalWords pos : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {G : MGraph} {U : List Update}
    (hBatch : SmallBatchAt mem batchPtr G U totalWords)
    (_hBatchW : ∀ j < totalWords, mem (batchPtr + j) < 2 ^ w)
    (hBatchLe : batchPtr + totalWords ≤ outBuf)
    (hz : ZeroFrom mem outBuf)
    (hRoom : outBuf + U.length < 2 ^ w)
    (hw5 : 5 < 2 ^ w) :
    ∃ (out : State) (cost : ℕ),
      Runs w p ω wireCollectTouchedEdgesBody (startState [batchPtr, outBuf] mem pos)
        (.returned (coreBatchTouchedEdges U).length) out cost ∧
      cost ≤ 60 * U.length + 35 ∧
      ListAt out.mem outBuf (coreBatchTouchedEdges U) ∧
      ZeroFrom out.mem (outBuf + (coreBatchTouchedEdges U).length) ∧
      (∀ a < outBuf, out.mem a = mem a) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  obtain ⟨⟨hTotPos, hLen0, hBody0⟩, _⟩ := hBatch
  have hULenW : U.length < 2 ^ w := by omega
  let s0 := startState [batchPtr, outBuf] mem pos
  let s1 := { s0 with regs := Function.update s0.regs 2 U.length }
  let s2 := { s1 with regs := Function.update s1.regs 3 (batchPtr + 1) }
  let s3 := { s2 with regs := Function.update s2.regs 4 0 }
  have r1 : Runs w p ω (.assign 2 (.load (.reg 0))) s0 .normal s1 3 :=
    runs_assign_iff.mpr ⟨U.length, by simp [Expr.eval, s0, startState, hLen0], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 3 (.bin .add (.reg 0) (.const 1))) s1 .normal s2 4 :=
    runs_assign_iff.mpr ⟨batchPtr + 1, by
      simp [Expr.eval, BinOp.eval, s1, s0, startState, hw1, show batchPtr + 1 < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 4 (.const 0)) s2 .normal s3 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  let Inv : ℕ → State → Prop := fun i s =>
    ∃ ptr remW,
      let pref := coreBatchTouchedEdges (U.take i)
      s.regs 0 = batchPtr ∧ s.regs 1 = outBuf ∧ s.regs 2 = U.length ∧
      s.regs 3 = ptr ∧ s.regs 4 = pref.length ∧ s.regs 5 = i ∧
      batchPtr + 1 ≤ ptr ∧ ptr + remW = batchPtr + totalWords ∧
      BatchBodyAt mem ptr (G.applyBatch (U.take i)) (U.drop i) remW ∧
      ListAt s.mem outBuf pref ∧
      ZeroFrom s.mem (outBuf + pref.length) ∧
      (∀ a < outBuf, s.mem a = mem a)
  have hloop := Triple.forRange_le (w := w) (p := p) (r := 5) (lo := .const 0) (hi := .reg 2)
    (P := fun s => s = s3) (Inv := Inv) (fun _ => 45) 0 U.length (Nat.zero_le _) hw1
    (fun _ => hULenW)
    (fun s hs => by
      subst hs
      refine ⟨by simp [Expr.eval, Nat.two_pow_pos w],
        batchPtr + 1, totalWords - 1,
        by simp [s3, s2, s1, s0, startState], by simp [s3, s2, s1, s0, startState],
        by simp [s3, s2, s1], by simp [s3, s2], by simp [s3, coreBatchTouchedEdges], by simp,
        le_rfl, by omega, by simpa [MGraph.applyBatch] using hBody0,
        fun _ h => by simp [coreBatchTouchedEdges] at h,
        by simpa [s3, s2, s1, s0, startState, coreBatchTouchedEdges] using hz, fun _ _ => rfl⟩)
    (fun _ _ _ _ h => by rcases h with ⟨_, _, _, _, _, _, _, h5, _⟩; exact h5)
    (fun _ s _ _ h => by rcases h with ⟨_, _, _, _, h2, _⟩; simp [Expr.eval, h2])
    (fun i _ hi s ω' ⟨ptr, remW, h0, h1, h2, h3, h4, h5, hPtrLo, hPtrEnd, hBody, hList, hZ, hFr⟩ => by
      have hDrop : U.drop i = U[i] :: U.drop (i + 1) := List.drop_eq_getElem_cons hi
      rw [hDrop] at hBody
      obtain ⟨uLen, hULenLe, hUAt, hRest⟩ := hBody
      have hTakeSucc : U.take (i + 1) = U.take i ++ [U[i]] := List.take_succ_eq_append_getElem hi
      have hPrefLe : (coreBatchTouchedEdges (U.take i)).length ≤ i :=
        (coreBatchTouchedEdges_length_le _).trans (by simp [List.length_take, Nat.le_of_lt hi])
      have hGStep : G.applyBatch (U.take (i + 1)) = (G.applyBatch (U.take i)).applyUpdate U[i] := by
        unfold MGraph.applyBatch; rw [hTakeSucc, List.foldl_append]; rfl
      cases hu : U[i] with
      | insert e u v =>
        rw [hu] at hUAt
        obtain ⟨rfl, hLA⟩ := hUAt
        have hTag : mem ptr = 0 := by simpa using hLA 0 (by simp)
        have hE : mem (ptr + 1) = e := by simpa using hLA 1 (by simp)
        have hm0 : s.mem ptr = 0 := (hFr ptr (by omega)).trans hTag
        have hm1 : s.mem (ptr + 1) = e := (hFr (ptr + 1) (by omega)).trans hE
        let pref := coreBatchTouchedEdges (U.take i)
        let t1 := { s with regs := Function.update s.regs 6 0 }
        let t2 := { t1 with regs := Function.update t1.regs 7 e }
        let t3 := { t2 with mem := Function.update t2.mem (outBuf + pref.length) e }
        let t4 := { t3 with regs := Function.update t3.regs 4 (pref.length + 1) }
        let t5 := { t4 with regs := Function.update t4.regs 3 (ptr + 4) }
        have rt1 : Runs w p ω' (.assign 6 (.load (.reg 3))) s .normal t1 3 :=
          runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h3, hm0], rfl, rfl, rfl⟩
        have rt2 : Runs w p ω' (.assign 7 (.load (.bin .add (.reg 3) (.const 1)))) t1 .normal t2 5 :=
          runs_assign_iff.mpr ⟨e, by
            simp [Expr.eval, BinOp.eval, t1, h3, hw1, show ptr + 1 < 2 ^ w by omega, hm1],
            rfl, rfl, rfl⟩
        have rt3 : Runs w p ω' (.store (.bin .add (.reg 1) (.reg 4)) (.reg 7)) t2 .normal t3 5 :=
          runs_store_iff.mpr ⟨outBuf + pref.length, e, by
            have hOutPl : outBuf + (coreBatchTouchedEdges (U.take i)).length < 2 ^ w := by omega
            simp [Expr.eval, BinOp.eval, t2, t1, h1, h4, pref, hOutPl],
            by simp [Expr.eval, t2], rfl, rfl, rfl⟩
        have rt4 : Runs w p ω' (.assign 4 (.bin .add (.reg 4) (.const 1))) t3 .normal t4 4 :=
          runs_assign_iff.mpr ⟨pref.length + 1, by
            have hplW : (coreBatchTouchedEdges (U.take i)).length + 1 < 2 ^ w := by omega
            simp [Expr.eval, BinOp.eval, t3, t2, t1, h4, hw1, pref, hplW], rfl, rfl, rfl⟩
        have rt5 : Runs w p ω' (.assign 3 (.bin .add (.reg 3) (.const 4))) t4 .normal t5 4 :=
          runs_assign_iff.mpr ⟨ptr + 4, by
            simp [Expr.eval, BinOp.eval, t4, t3, t2, t1, h3, hw4, show ptr + 4 < 2 ^ w by omega],
            rfl, rfl, rfl⟩
        have rCond : Runs w p ω'
            (.cond (.bin .eq (.reg 6) (.const 0))
              (.assign 7 (.load (.bin .add (.reg 3) (.const 1))) ;;
               .store (.bin .add (.reg 1) (.reg 4)) (.reg 7) ;;
               .assign 4 (.bin .add (.reg 4) (.const 1)) ;;
               .assign 3 (.bin .add (.reg 3) (.const 4)))
              (.cond (.bin .eq (.reg 6) (.const 1))
                 (.assign 7 (.load (.bin .add (.reg 3) (.const 1))) ;;
                  .store (.bin .add (.reg 1) (.reg 4)) (.reg 7) ;;
                  .assign 4 (.bin .add (.reg 4) (.const 1)) ;;
                  .assign 3 (.bin .add (.reg 3) (.const 2)))
                 (.assign 7 (.load (.bin .add (.reg 3) (.const 3))) ;;
                  .assign 8 (.load (.bin .add (.reg 3) (.const 4))) ;;
                  .assign 3 (.bin .add (.bin .add (.bin .add (.reg 3) (.const 5)) (.reg 7)) (.reg 8)))))
            t1 .normal t5 25 :=
          runs_cond_iff.mpr ⟨1, 21, by simp [Expr.eval, BinOp.eval, t1, show 0 < 2 ^ w by omega, hw1],
            by simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]
               exact runs_seq_iff.mpr (Or.inr ⟨t2, 5, 15, rt2,
                 runs_seq_iff.mpr (Or.inr ⟨t3, 5, 9, rt3,
                   runs_seq_iff.mpr (Or.inr ⟨t4, 4, 4, rt4, rt5, rfl⟩), rfl⟩), rfl⟩),
            by simp [Expr.size]⟩
        have hNewPref : coreBatchTouchedEdges (U.take (i + 1)) = pref ++ [e] := by
          rw [hTakeSucc, coreBatchTouchedEdges_append, hu]; rfl
        refine ⟨.normal, t5, 29, runs_seq_iff.mpr (Or.inr ⟨t1, 3, 25, rt1, rCond, rfl⟩),
          ⟨⟨ptr + 4, remW - 4, by simp [t5, t4, t3, t2, t1, h0], by simp [t5, t4, t3, t2, t1, h1],
            by simp [t5, t4, t3, t2, t1, h2], by simp [t5],
            by simp [t5, t4, hNewPref, List.length_append], by simp [t5, t4, t3, t2, t1],
            by omega, by omega, hGStep.symm ▸ hRest, ?_, ?_, ?_⟩,
           by simp [t5, t4, t3, t2, t1, h5]⟩, by dsimp; omega⟩
        · rw [hNewPref]
          refine listAt_append.mpr ⟨hList.congr fun a ha1 ha2 => by
            simp [t5, t4, t3, t2, t1, Function.update_of_ne (by dsimp only [pref] at ha2 ⊢; omega : a ≠ outBuf + pref.length)],
            fun j hj => by
              have hj0 : j = 0 := by simp at hj; exact hj
              subst hj0; simp [t5, t4, t3]⟩
        · intro a ha; rw [hNewPref, List.length_append, List.length_singleton] at ha
          simp only [t5, t4, t3, t2, t1, Function.update_of_ne (by dsimp only [pref] at ha ⊢; omega : a ≠ outBuf + pref.length)]
          exact hZ a (by dsimp only [pref] at ha ⊢; omega)
        · intro a ha
          simp only [t5, t4, t3, t2, t1, Function.update_of_ne (by omega : a ≠ outBuf + pref.length)]
          exact hFr a ha
      | delete e =>
        rw [hu] at hUAt
        obtain ⟨rfl, hLA⟩ := hUAt
        have hTag : mem ptr = 1 := by simpa using hLA 0 (by simp)
        have hE : mem (ptr + 1) = e := by simpa using hLA 1 (by simp)
        have hm0 : s.mem ptr = 1 := (hFr ptr (by omega)).trans hTag
        have hm1 : s.mem (ptr + 1) = e := (hFr (ptr + 1) (by omega)).trans hE
        let pref := coreBatchTouchedEdges (U.take i)
        let t1 := { s with regs := Function.update s.regs 6 1 }
        let t2 := { t1 with regs := Function.update t1.regs 7 e }
        let t3 := { t2 with mem := Function.update t2.mem (outBuf + pref.length) e }
        let t4 := { t3 with regs := Function.update t3.regs 4 (pref.length + 1) }
        let t5 := { t4 with regs := Function.update t4.regs 3 (ptr + 2) }
        have rt1 : Runs w p ω' (.assign 6 (.load (.reg 3))) s .normal t1 3 :=
          runs_assign_iff.mpr ⟨1, by simp [Expr.eval, h3, hm0], rfl, rfl, rfl⟩
        have rt2 : Runs w p ω' (.assign 7 (.load (.bin .add (.reg 3) (.const 1)))) t1 .normal t2 5 :=
          runs_assign_iff.mpr ⟨e, by
            simp [Expr.eval, BinOp.eval, t1, h3, hw1, show ptr + 1 < 2 ^ w by omega, hm1],
            rfl, rfl, rfl⟩
        have rt3 : Runs w p ω' (.store (.bin .add (.reg 1) (.reg 4)) (.reg 7)) t2 .normal t3 5 :=
          runs_store_iff.mpr ⟨outBuf + pref.length, e, by
            have hOutPl : outBuf + (coreBatchTouchedEdges (U.take i)).length < 2 ^ w := by omega
            simp [Expr.eval, BinOp.eval, t2, t1, h1, h4, pref, hOutPl],
            by simp [Expr.eval, t2], rfl, rfl, rfl⟩
        have rt4 : Runs w p ω' (.assign 4 (.bin .add (.reg 4) (.const 1))) t3 .normal t4 4 :=
          runs_assign_iff.mpr ⟨pref.length + 1, by
            have hplW : (coreBatchTouchedEdges (U.take i)).length + 1 < 2 ^ w := by omega
            simp [Expr.eval, BinOp.eval, t3, t2, t1, h4, hw1, pref, hplW], rfl, rfl, rfl⟩
        have rt5 : Runs w p ω' (.assign 3 (.bin .add (.reg 3) (.const 2))) t4 .normal t5 4 :=
          runs_assign_iff.mpr ⟨ptr + 2, by
            simp [Expr.eval, BinOp.eval, t4, t3, t2, t1, h3, hw2, show ptr + 2 < 2 ^ w by omega],
            rfl, rfl, rfl⟩
        have rIn : Runs w p ω'
            (.cond (.bin .eq (.reg 6) (.const 1))
               (.assign 7 (.load (.bin .add (.reg 3) (.const 1))) ;;
                .store (.bin .add (.reg 1) (.reg 4)) (.reg 7) ;;
                .assign 4 (.bin .add (.reg 4) (.const 1)) ;;
                .assign 3 (.bin .add (.reg 3) (.const 2)))
               (.assign 7 (.load (.bin .add (.reg 3) (.const 3))) ;;
                .assign 8 (.load (.bin .add (.reg 3) (.const 4))) ;;
                .assign 3 (.bin .add (.bin .add (.bin .add (.reg 3) (.const 5)) (.reg 7)) (.reg 8))))
            t1 .normal t5 25 :=
          runs_cond_iff.mpr ⟨1, 21, by simp [Expr.eval, BinOp.eval, t1, hw1],
            by simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]
               exact runs_seq_iff.mpr (Or.inr ⟨t2, 5, 15, rt2,
                 runs_seq_iff.mpr (Or.inr ⟨t3, 5, 9, rt3,
                   runs_seq_iff.mpr (Or.inr ⟨t4, 4, 4, rt4, rt5, rfl⟩), rfl⟩), rfl⟩),
            by simp [Expr.size]⟩
        have rOut : Runs w p ω'
            (.cond (.bin .eq (.reg 6) (.const 0))
              (.assign 7 (.load (.bin .add (.reg 3) (.const 1))) ;;
               .store (.bin .add (.reg 1) (.reg 4)) (.reg 7) ;;
               .assign 4 (.bin .add (.reg 4) (.const 1)) ;;
               .assign 3 (.bin .add (.reg 3) (.const 4)))
              (.cond (.bin .eq (.reg 6) (.const 1))
                 (.assign 7 (.load (.bin .add (.reg 3) (.const 1))) ;;
                  .store (.bin .add (.reg 1) (.reg 4)) (.reg 7) ;;
                  .assign 4 (.bin .add (.reg 4) (.const 1)) ;;
                  .assign 3 (.bin .add (.reg 3) (.const 2)))
                 (.assign 7 (.load (.bin .add (.reg 3) (.const 3))) ;;
                  .assign 8 (.load (.bin .add (.reg 3) (.const 4))) ;;
                  .assign 3 (.bin .add (.bin .add (.bin .add (.reg 3) (.const 5)) (.reg 7)) (.reg 8)))))
            t1 .normal t5 29 :=
          runs_cond_iff.mpr ⟨0, 25, by simp [Expr.eval, BinOp.eval, t1, show 0 < 2 ^ w by omega],
            by simp only [↓reduceIte]; exact rIn, by simp [Expr.size]⟩
        have hNewPref : coreBatchTouchedEdges (U.take (i + 1)) = pref ++ [e] := by
          rw [hTakeSucc, coreBatchTouchedEdges_append, hu]; rfl
        refine ⟨.normal, t5, 33, runs_seq_iff.mpr (Or.inr ⟨t1, 3, 29, rt1, rOut, rfl⟩),
          ⟨⟨ptr + 2, remW - 2, by simp [t5, t4, t3, t2, t1, h0], by simp [t5, t4, t3, t2, t1, h1],
            by simp [t5, t4, t3, t2, t1, h2], by simp [t5],
            by simp [t5, t4, hNewPref, List.length_append], by simp [t5, t4, t3, t2, t1],
            by omega, by omega, hGStep.symm ▸ hRest, ?_, ?_, ?_⟩,
           by simp [t5, t4, t3, t2, t1, h5]⟩, by dsimp; omega⟩
        · rw [hNewPref]
          refine listAt_append.mpr ⟨hList.congr fun a ha1 ha2 => by
            simp [t5, t4, t3, t2, t1, Function.update_of_ne (by dsimp only [pref] at ha2 ⊢; omega : a ≠ outBuf + pref.length)],
            fun j hj => by
              have hj0 : j = 0 := by simp at hj; exact hj
              subst hj0; simp [t5, t4, t3]⟩
        · intro a ha; rw [hNewPref, List.length_append, List.length_singleton] at ha
          simp only [t5, t4, t3, t2, t1, Function.update_of_ne (by dsimp only [pref] at ha ⊢; omega : a ≠ outBuf + pref.length)]
          exact hZ a (by dsimp only [pref] at ha ⊢; omega)
        · intro a ha
          simp only [t5, t4, t3, t2, t1, Function.update_of_ne (by omega : a ≠ outBuf + pref.length)]
          exact hFr a ha
      | split v v' inc Sh =>
        rw [hu] at hUAt
        have hSp : ∃ tag, (tag = 2 ∨ tag = 3) ∧
            ∃ k1 k2, uLen = 5 + k1 + k2 ∧ mem ptr = tag ∧ mem (ptr + 3) = k1 ∧ mem (ptr + 4) = k2 := by
          rcases hUAt with ⟨Lt, Lh, _, _, _, _, rfl, hLA⟩ | ⟨Lt, Lh, _, _, _, _, rfl, hLA⟩
          · refine ⟨2, Or.inl rfl, Lt.length, Lh.length, rfl, ?_, ?_, ?_⟩
            · simpa using hLA 0 (by simp)
            · simpa using hLA 3 (by simp)
            · simpa using hLA 4 (by simp)
          · refine ⟨3, Or.inr rfl, Lt.length, Lh.length, rfl, ?_, ?_, ?_⟩
            · simpa using hLA 0 (by simp)
            · simpa using hLA 3 (by simp)
            · simpa using hLA 4 (by simp)
        obtain ⟨tag, hTag23, k1, k2, rfl, hTag, hK1, hK2⟩ := hSp
        have hm0 : s.mem ptr = tag := (hFr ptr (by omega)).trans hTag
        have hm3 : s.mem (ptr + 3) = k1 := (hFr (ptr + 3) (by omega)).trans hK1
        have hm4 : s.mem (ptr + 4) = k2 := (hFr (ptr + 4) (by omega)).trans hK2
        let t1 := { s with regs := Function.update s.regs 6 tag }
        let t2 := { t1 with regs := Function.update t1.regs 7 k1 }
        let t3 := { t2 with regs := Function.update t2.regs 8 k2 }
        let t4 := { t3 with regs := Function.update t3.regs 3 (ptr + 5 + k1 + k2) }
        have rt1 : Runs w p ω' (.assign 6 (.load (.reg 3))) s .normal t1 3 :=
          runs_assign_iff.mpr ⟨tag, by simp [Expr.eval, h3, hm0], rfl, rfl, rfl⟩
        have rt2 : Runs w p ω' (.assign 7 (.load (.bin .add (.reg 3) (.const 3)))) t1 .normal t2 5 :=
          runs_assign_iff.mpr ⟨k1, by
            simp [Expr.eval, BinOp.eval, t1, h3, show 3 < 2 ^ w by omega,
              show ptr + 3 < 2 ^ w by omega, hm3], rfl, rfl, rfl⟩
        have rt3 : Runs w p ω' (.assign 8 (.load (.bin .add (.reg 3) (.const 4)))) t2 .normal t3 5 :=
          runs_assign_iff.mpr ⟨k2, by
            simp [Expr.eval, BinOp.eval, t2, t1, h3, hw4,
              show ptr + 4 < 2 ^ w by omega, hm4], rfl, rfl, rfl⟩
        have rt4 : Runs w p ω' (.assign 3 (.bin .add (.bin .add (.bin .add (.reg 3) (.const 5)) (.reg 7)) (.reg 8)))
            t3 .normal t4 8 :=
          runs_assign_iff.mpr ⟨ptr + 5 + k1 + k2, by
            simp [Expr.eval, BinOp.eval, t3, t2, t1, h3, hw5,
              show ptr + 5 < 2 ^ w by omega, show ptr + 5 + k1 < 2 ^ w by omega,
              show ptr + 5 + k1 + k2 < 2 ^ w by omega], rfl, rfl, rfl⟩
        have hTne0 : tag ≠ 0 := by omega
        have hTne1 : tag ≠ 1 := by omega
        have rIn : Runs w p ω'
            (.cond (.bin .eq (.reg 6) (.const 1))
               (.assign 7 (.load (.bin .add (.reg 3) (.const 1))) ;;
                .store (.bin .add (.reg 1) (.reg 4)) (.reg 7) ;;
                .assign 4 (.bin .add (.reg 4) (.const 1)) ;;
                .assign 3 (.bin .add (.reg 3) (.const 2)))
               (.assign 7 (.load (.bin .add (.reg 3) (.const 3))) ;;
                .assign 8 (.load (.bin .add (.reg 3) (.const 4))) ;;
                .assign 3 (.bin .add (.bin .add (.bin .add (.reg 3) (.const 5)) (.reg 7)) (.reg 8))))
            t1 .normal t4 24 :=
          runs_cond_iff.mpr ⟨0, 20, by simp [Expr.eval, BinOp.eval, t1, hw1, hTne1],
            by simp only [↓reduceIte]
               exact runs_seq_iff.mpr (Or.inr ⟨t2, 5, 14, rt2,
                 runs_seq_iff.mpr (Or.inr ⟨t3, 5, 8, rt3, rt4, rfl⟩), rfl⟩),
            by simp [Expr.size]⟩
        have rOut : Runs w p ω'
            (.cond (.bin .eq (.reg 6) (.const 0))
              (.assign 7 (.load (.bin .add (.reg 3) (.const 1))) ;;
               .store (.bin .add (.reg 1) (.reg 4)) (.reg 7) ;;
               .assign 4 (.bin .add (.reg 4) (.const 1)) ;;
               .assign 3 (.bin .add (.reg 3) (.const 4)))
              (.cond (.bin .eq (.reg 6) (.const 1))
                 (.assign 7 (.load (.bin .add (.reg 3) (.const 1))) ;;
                  .store (.bin .add (.reg 1) (.reg 4)) (.reg 7) ;;
                  .assign 4 (.bin .add (.reg 4) (.const 1)) ;;
                  .assign 3 (.bin .add (.reg 3) (.const 2)))
                 (.assign 7 (.load (.bin .add (.reg 3) (.const 3))) ;;
                  .assign 8 (.load (.bin .add (.reg 3) (.const 4))) ;;
                  .assign 3 (.bin .add (.bin .add (.bin .add (.reg 3) (.const 5)) (.reg 7)) (.reg 8)))))
            t1 .normal t4 28 :=
          runs_cond_iff.mpr ⟨0, 24, by simp [Expr.eval, BinOp.eval, t1, show 0 < 2 ^ w by omega, hTne0],
            by simp only [↓reduceIte]; exact rIn, by simp [Expr.size]⟩
        have hNewPref : coreBatchTouchedEdges (U.take (i + 1)) = coreBatchTouchedEdges (U.take i) := by
          rw [hTakeSucc, coreBatchTouchedEdges_append, hu]; simp [coreBatchTouchedEdges]
        have hRest' : BatchBodyAt mem (ptr + 5 + k1 + k2) (G.applyBatch (U.take (i + 1)))
            (U.drop (i + 1)) (remW - (5 + k1 + k2)) := by
          rw [hGStep, show ptr + 5 + k1 + k2 = ptr + (5 + k1 + k2) by omega]; exact hRest
        refine ⟨.normal, t4, 32, runs_seq_iff.mpr (Or.inr ⟨t1, 3, 28, rt1, rOut, rfl⟩),
          ⟨⟨ptr + 5 + k1 + k2, remW - (5 + k1 + k2),
            by simp [t4, t3, t2, t1, h0], by simp [t4, t3, t2, t1, h1],
            by simp [t4, t3, t2, t1, h2], by simp [t4],
            by simp [t4, t3, t2, t1, h4, hNewPref], by simp [t4, t3, t2, t1],
            by omega, by omega, hRest',
            by simpa [t4, t3, t2, t1, hNewPref] using hList,
            by simpa [t4, t3, t2, t1, hNewPref] using hZ, hFr⟩,
           by simp [t4, t3, t2, t1, h5]⟩, by dsimp; omega⟩)
  obtain ⟨o, s4, cLoop, rLoop, hInv4, hcLoop⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hInv4
  | normal =>
    rcases hInv4 with ⟨_, _, _, _, _, _, h4, _, _, _, _, hList4, hZ4, hFr4⟩
    have hTakeAll : U.take U.length = U := List.take_of_length_le le_rfl
    rw [hTakeAll] at h4 hList4 hZ4
    have rRet : Runs w p ω (.ret (.reg 4)) s4 (.returned (coreBatchTouchedEdges U).length) s4 2 :=
      runs_ret_iff.mpr ⟨(coreBatchTouchedEdges U).length, by simp [Expr.eval, h4], rfl, rfl, rfl⟩
    refine ⟨s4, _, runs_seq_iff.mpr (Or.inr ⟨s1, 3, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 4, _, r2,
        runs_seq_iff.mpr (Or.inr ⟨s3, 2, _, r3,
          runs_seq_iff.mpr (Or.inr ⟨s4, cLoop, 2, rLoop, rRet, rfl⟩), rfl⟩), rfl⟩), rfl⟩),
      ?_, hList4, hZ4, hFr4⟩
    have hcBound : rangeCost (fun _ => 45) 0 U.length = 45 * U.length := by
      unfold rangeCost; simp [Nat.mul_comm]
    simp only [Expr.size, hcBound, Nat.sub_zero] at hcLoop
    omega

/-! ### 2. Bridging `BranchOutReembAt` to `ReembListAt` and combining `KFRBL` with `SparseCoreUpdateOutFootAt` -/

/-- `readList mem ptr len = xs` implies `ReembListAt mem ptr len xs`. -/
theorem reembListAt_of_readList {mem : ℕ → ℕ} {ptr len : ℕ} {xs : List ℕ}
    (h : readList mem ptr len = xs) : ReembListAt mem ptr len xs := by
  subst h
  refine ⟨(readList_length mem ptr len).symm, fun j hj => (readList_getElem mem ptr len j hj).symm⟩

/-- Execute `ordCoreUpdateStmt (op 0)` combining `R.Implements` under
`sparseCoreOrdMachineContractKFRBL` with `SparseCoreUpdateOutFootAt`, returning both
`BranchOutReembAt` (`reembPtr, reembLen` at `heap + 1 + 4 * k + 2 * j`) and all
`BranchOutFChgAt`, placement, and `edMul` guarantees on the exact same deterministic run. -/
theorem ordCoreUpdateKFRBLOut_runs
    {w L depth k M N vCap eCap capExp edMul handle graph batch words edits editWords lengths
      gradient heap : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {reemb : ToolReembFn tool}
    {initialGraph : MGraph} {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {a : SparseCoreOrdAbs tool} {x : R.τ}
    {p : Program} {init : ℕ} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (hImpl : R.Implements w p init op
      (sparseCoreOrdMachineContractKFRBL fmt L depth tool reemb initialGraph k M N vCap eCap capExp P
        allocation))
    (hOut : SparseCoreUpdateOutFootAt fmt L depth tool initialGraph k M N vCap eCap capExp P
      allocation edMul R p op)
    (hh : st.regs 3 = handle) (hg : st.regs 6 = graph)
    (hb : st.regs 10 = batch) (hbw : st.regs 11 = words)
    (he : st.regs 12 = edits) (hew : st.regs 13 = editWords)
    (hl : st.regs 7 = lengths) (hc : st.regs 8 = gradient) (hp : st.regs 4 = heap)
    (hwords : ∀ v ∈ [handle, graph, batch, words, edits, editWords, lengths, gradient, heap],
      v < 2 ^ w)
    (hrep : R.rep handle a x st.mem)
    (hpre : SparseCoreOrdUpdateAt fmt L tool k M N vCap eCap a
      [handle, graph, batch, words, edits, editWords, lengths, gradient, heap] st.mem)
    (hvalid : OrdEditsValidFor vCap eCap a.ord (readOrdEdits st.mem edits))
    (hblocks : OrdEditsForBatch a.G
      (ordUpdateBatch a [handle, graph, batch, words, edits, editWords, lengths, gradient, heap]
        st.mem) (readOrdEdits st.mem edits))
    (hfoot : ∀ addr, R.foot handle x addr → addr < heap) (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 0
      [handle, graph, batch, words, edits, editWords, lengths, gradient, heap] < 2 ^ w) :
    let args := [handle, graph, batch, words, edits, editWords, lengths, gradient, heap]
    let a' := ordUpdateNext fmt L a args st.mem
    let batches := (ordUpdateModel fmt L a args st.mem).2
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (ordCoreUpdateStmt (op 0)) st .normal out cost ∧
      out.regs 5 = ret ∧
      R.rep handle a' y out.mem ∧
      SparseCoreOrdInput tool k M N a'.st a'.G a'.ord a'.n ∧
      BranchOutAt out.mem heap k (tool.S a.st) batches (tool.rot a.st) (tool.rot a'.st) ∧
      BranchOutFChgAt w out.mem heap ret k (tool.lsfs a.st) (tool.lsfs a'.st) ∧
      (∀ j < k, ReembListAt out.mem
        (out.mem (heap + 1 + 4 * k + 2 * j)) (out.mem (heap + 2 + 4 * k + 2 * j))
        (reemb a.st (ordUpdateBatch a args st.mem) (ordUpdateOrder a args st.mem) j)) ∧
      (∀ j < k, OrdEditsForBatch (tool.S a.st j) (batches j)
        (readOrdEdits out.mem (out.mem (heap + 3 + 4 * j)))) ∧
      (∀ j < k, OrdEditsValidFor vCap eCap (tool.rot a.st j)
        (readOrdEdits out.mem (out.mem (heap + 3 + 4 * j)))) ∧
      (∀ j < k,
        let base := heap + 1 + 4 * j
        let bPtr := out.mem base
        let bW := out.mem (base + 1)
        let ePtr := out.mem (base + 2)
        let eW := out.mem (base + 3)
        heap + 1 + 4 * j + 3 < ret ∧
        heap ≤ bPtr ∧ bPtr + bW ≤ ret ∧
        heap ≤ ePtr ∧ ePtr + eW ≤ ret ∧
        (∀ t < bW, out.mem (bPtr + t) < 2 ^ w) ∧
        (∀ t < eW, out.mem (ePtr + t) < 2 ^ w) ∧
        (∀ t < bW, ¬ R.foot handle y (bPtr + t)) ∧
        (∀ t < eW, ¬ R.foot handle y (ePtr + t)) ∧
        (decodeBatch out.mem bPtr (tool.S a.st j)).1 = batches j ∧
        eW ≤ edMul * (tool.cost a'.st - tool.cost a.st +
          (words + editWords + 1) * SparseCore.bundleLogFactor M N)) ∧
      R.Respects (R.foot handle x) heap (allocation 0 args) st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤
        P.mul * (tool.cost a'.st - tool.cost a.st +
          (k + 1) * (words + editWords + 1) * SparseCore.bundleLogFactor M N) +
        R.phi handle x st.mem + 10 ∧
      ∀ r, r ≠ 5 → out.regs r = st.regs r := by
  intro args a' batches
  obtain ⟨out, ret, cost, y, hcall, hreg5, hrep', hIn', hBr, hFChg, hFor, hVal, hSlots,
    hResp, hCost, hRegs⟩ :=
    ordCoreUpdateKFBLOut_runs hOut hh hg hb hbw he hew hl hc hp hwords hrep hpre hvalid hblocks
      hfoot hz hroom
  obtain ⟨vargs, body1, o1, after1, c1, hargs1, hbody1, hrun1, _, hOutEq, _⟩ :=
    runs_call_iff.mp hcall
  have hArgsEq : vargs = args := by
    have hEval : evalArgs w st
        [.reg 3, .reg 6, .reg 10, .reg 11, .reg 12, .reg 13, .reg 7, .reg 8, .reg 4] = some args := by
      simp [evalArgs, Expr.eval, args, hh, hg, hb, hbw, he, hew, hl, hc, hp]
    exact Option.some.inj (hargs1.symm.trans hEval)
  subst hArgsEq
  have hDpre : (sparseCoreOrdMachineContractKFRBL fmt L depth tool reemb initialGraph k M N
      vCap eCap capExp P allocation).pre 0 a args st.mem :=
    ⟨⟨hpre, hvalid⟩, hblocks⟩
  obtain ⟨body2, hbody2, o2, st2, c2, hrun2, a2, y2, _, hpost2, _, _⟩ :=
    hImpl.2.2 0 handle a x args st.mem st.pos ω hwords rfl hrep hDpre hfoot hz hroom
  have hBodyEq : body2 = body1 := Option.some.inj (hbody2.symm.trans hbody1)
  subst hBodyEq
  obtain ⟨_, hstEq, _⟩ := hrun2.det hrun1
  have hMemEq : out.mem = st2.mem := by rw [hOutEq, ← hstEq]
  have hReemb : ∀ j < k, ReembListAt out.mem
      (out.mem (heap + 1 + 4 * k + 2 * j)) (out.mem (heap + 2 + 4 * k + 2 * j))
      (reemb a.st (ordUpdateBatch a args st.mem) (ordUpdateOrder a args st.mem) j) := fun j hj => by
    rw [hMemEq]
    exact reembListAt_of_readList (by simpa [heapArg, args] using hpost2.1.2 j hj)
  exact ⟨out, ret, cost, y, hcall, hreg5, hrep', hIn', hBr, hFChg, hReemb, hFor, hVal, hSlots,
    hResp, hCost, hRegs⟩

end MinCostFlow.MinRatio
