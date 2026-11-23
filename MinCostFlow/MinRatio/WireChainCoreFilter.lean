module

public import MinCostFlow.MinRatio.WireChainCoreBatch
public import MinCostFlow.MinRatio.TreeEditLayout
import WordRAM.Tactic

/-!
# Active tree-edit filter (`WireChainCoreFilter`)

Provides `wireFilterActiveEditsBody` (`NoRand`) and `wireFilterActiveEditsBody_runs`,
filtering a packed `TreeEditsAt` buffer to keep all insertions and only deletions with
`slots[e] ≠ 0` in `O(|edits|)` steps.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Chain

/-- Tag word of a `TreeChange` (`1` for insert, `0` for delete). -/
@[expose] def treeChangeTag : TreeChange → ℕ
  | .insert _ => 1
  | .delete _ => 0

/-- Edge ID carried by a `TreeChange`. -/
@[expose] def treeChangeEdge : TreeChange → ℕ
  | .insert e => e
  | .delete e => e

theorem treeEditsAt_getElem {mem : ℕ → ℕ} {base : ℕ} {edits : List TreeChange}
    (h : TreeEditsAt mem base edits) {i : ℕ} (hi : i < edits.length) :
    mem (base + 2 * i) = treeChangeTag edits[i] ∧
    mem (base + 2 * i + 1) = treeChangeEdge edits[i] := by
  induction edits generalizing base i with
  | nil => cases hi
  | cons c rest ih =>
    obtain ⟨hc, hr⟩ := treeEditsAt_cons h
    cases i with
    | zero =>
      cases c with
      | insert e =>
        exact ⟨by simpa [treeEditWords, treeChangeTag] using hc 0 (by simp [treeEditWords]),
          by simpa [treeEditWords, treeChangeEdge] using hc 1 (by simp [treeEditWords])⟩
      | delete e =>
        exact ⟨by simpa [treeEditWords, treeChangeTag] using hc 0 (by simp [treeEditWords]),
          by simpa [treeEditWords, treeChangeEdge] using hc 1 (by simp [treeEditWords])⟩
    | succ i' =>
      have := ih hr (Nat.lt_of_succ_lt_succ hi)
      simpa [show base + 2 + 2 * i' = base + 2 * (i' + 1) by omega] using this

theorem treeEditsAt_append_singleton {mem : ℕ → ℕ} {base : ℕ} {pref : List TreeChange}
    {c : TreeChange} (hPref : TreeEditsAt mem base pref)
    (hTag : mem (base + 2 * pref.length) = treeChangeTag c)
    (hEdge : mem (base + 2 * pref.length + 1) = treeChangeEdge c) :
    TreeEditsAt mem base (pref ++ [c]) := by
  rw [TreeEditsAt, List.flatMap_append, listAt_append, treeEditWords_length]
  refine ⟨hPref, ?_⟩
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  intro j hj
  cases c with
  | insert e =>
    simp only [treeEditWords, List.length_cons, List.length_nil] at hj
    interval_cases j
    · simpa [treeEditWords, treeChangeTag] using hTag
    · simpa [treeEditWords, treeChangeEdge, Nat.add_assoc] using hEdge
  | delete e =>
    simp only [treeEditWords, List.length_cons, List.length_nil] at hj
    interval_cases j
    · simpa [treeEditWords, treeChangeTag] using hTag
    · simpa [treeEditWords, treeChangeEdge, Nat.add_assoc] using hEdge

theorem treeEditsAt_of_agree {mem₁ mem₂ : ℕ → ℕ} {base : ℕ} {edits : List TreeChange}
    (h : TreeEditsAt mem₁ base edits)
    (hag : ∀ j < 2 * edits.length, mem₂ (base + j) = mem₁ (base + j)) :
    TreeEditsAt mem₂ base edits := fun j hj => by
  rw [treeEditWords_length] at hj
  exact (hag j hj).trans (h j (by rwa [treeEditWords_length]))

/-- Procedure `[editsPtr, nEdits, slots, outPtr]` (`reg 0..3`): copies all `.insert e` (`tag = 1`)
and all `.delete e` (`tag = 0`) with `mem[slots + e] ≠ 0` into `outPtr`, returning the count. -/
@[expose] def wireFilterActiveEditsBody : Stmt :=
  .assign 4 (.const 0) ;;
  forRange 5 (.const 0) (.reg 1)
    (.assign 6 (.load (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 5)))) ;;
     .assign 7 (.load (.bin .add (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 5))) (.const 1))) ;;
     .assign 8 (.const 0) ;;
     .cond (.bin .eq (.reg 6) (.const 1))
       (.assign 8 (.const 1))
       (.cond (.load (.bin .add (.reg 2) (.reg 7)))
         (.assign 8 (.const 1))
         .nop) ;;
     .cond (.reg 8)
       (.store (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 4))) (.reg 6) ;;
        .store (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 4))) (.const 1)) (.reg 7) ;;
        .assign 4 (.bin .add (.reg 4) (.const 1)))
       .nop) ;;
  .ret (.reg 4)

theorem wireFilterActiveEditsBody_noRand : wireFilterActiveEditsBody.NoRand := by
  simp [wireFilterActiveEditsBody, forRange, forUp, Stmt.NoRand]

/-- Execute `wireFilterActiveEditsBody`: filters `TreeEditsAt mem editsPtr edits` to
`filterActiveEdits active edits` at `outPtr` in `O(|edits|)` steps. -/
theorem wireFilterActiveEditsBody_runs
    {w editsPtr slots outPtr intCap pos : ℕ} {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    {edits : List TreeChange} {active : Finset ℕ}
    (hEdits : TreeEditsAt mem editsPtr edits)
    (hCap : ∀ c ∈ edits, treeChangeEdge c < intCap)
    (hSlots : ∀ e < intCap, mem (slots + e) ≠ 0 ↔ e ∈ active)
    (hEditsLe : editsPtr + 2 * edits.length ≤ outPtr)
    (hSlotsLe : slots + intCap ≤ outPtr)
    (hz : ZeroFrom mem outPtr)
    (hRoom : outPtr + 2 * edits.length < 2 ^ w) (hw2 : 2 < 2 ^ w) :
    let filtered := filterActiveEdits active edits
    ∃ out cost,
      Runs w p ω wireFilterActiveEditsBody
        (startState [editsPtr, edits.length, slots, outPtr] mem pos)
        (.returned filtered.length) out cost ∧
      cost ≤ 70 * edits.length + 25 ∧
      TreeEditsAt out.mem outPtr filtered ∧
      ZeroFrom out.mem (outPtr + 2 * filtered.length) ∧
      ∀ a < outPtr, out.mem a = mem a := by
  classical
  dsimp only
  have hw1 : 1 < 2 ^ w := by omega
  let s0 := startState [editsPtr, edits.length, slots, outPtr] mem pos
  let s1 := { s0 with regs := Function.update s0.regs 4 0 }
  have r1 : Runs w p ω (.assign 4 (.const 0)) s0 .normal s1 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  let Inv (i : ℕ) (s : State) : Prop :=
    let pref := filterActiveEdits active (edits.take i)
    s.regs 0 = editsPtr ∧ s.regs 1 = edits.length ∧ s.regs 2 = slots ∧ s.regs 3 = outPtr ∧
    s.regs 4 = pref.length ∧ s.regs 5 = i ∧
    TreeEditsAt s.mem outPtr pref ∧
    ZeroFrom s.mem (outPtr + 2 * pref.length) ∧
    ∀ a < outPtr, s.mem a = mem a
  let stepCost := 60
  have hloop := Triple.forRange_le (w := w) (p := p) (r := 5) (lo := .const 0) (hi := .reg 1)
    (P := fun s => s = s1) (Inv := Inv) (fun _ => stepCost) 0 edits.length (Nat.zero_le _) hw1
    (fun _ => by omega)
    (fun s hs => by
      subst hs
      refine ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega],
        by simp [s1, s0, startState], by simp [s1, s0, startState],
        by simp [s1, s0, startState], by simp [s1, s0, startState],
        by simp [s1, filterActiveEdits], by simp,
        fun _ h => absurd h (by simp [filterActiveEdits]),
        by simpa [s1, s0, startState, filterActiveEdits] using hz,
        fun _ _ => rfl⟩)
    (fun _ _ _ _ h => h.2.2.2.2.2.1)
    (fun _ s _ _ h => by simp [Expr.eval, h.2.1])
    (fun i _ hi => by
      intro s ω' hI
      obtain ⟨h0, h1, h2, h3, h4, h5, hAt, hzS, hFr⟩ := hI
      set pref := filterActiveEdits active (edits.take i)
      have hPrefLe : pref.length ≤ i :=
        (filterActiveEdits_length_le _ _).trans (by simp [List.length_take, le_of_lt hi])
      have hEdI := treeEditsAt_getElem hEdits hi
      have hEdgeLt : treeChangeEdge edits[i] < intCap := hCap edits[i] (List.getElem_mem hi)
      have hTagAt : s.mem (editsPtr + 2 * i) = treeChangeTag edits[i] :=
        (hFr _ (by omega)).trans hEdI.1
      have hEdgeAt : s.mem (editsPtr + 2 * i + 1) = treeChangeEdge edits[i] :=
        (hFr _ (by omega)).trans hEdI.2
      let t1 := { s with regs := Function.update s.regs 6 (treeChangeTag edits[i]) }
      let t2 := { t1 with regs := Function.update t1.regs 7 (treeChangeEdge edits[i]) }
      let t3 := { t2 with regs := Function.update t2.regs 8 0 }
      have rt1 : Runs w p ω' (.assign 6 (.load (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 5)))))
          s .normal t1 7 :=
        runs_assign_iff.mpr ⟨treeChangeTag edits[i], by
          simp [Expr.eval, BinOp.eval, h0, h5, hw2, show 2 * i < 2 ^ w by omega,
            show editsPtr + 2 * i < 2 ^ w by omega, hTagAt], rfl, rfl, rfl⟩
      have rt2 : Runs w p ω' (.assign 7 (.load (.bin .add (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 5))) (.const 1))))
          t1 .normal t2 9 :=
        runs_assign_iff.mpr ⟨treeChangeEdge edits[i], by
          simp [Expr.eval, BinOp.eval, t1, h0, h5, hw2, hw1, show 2 * i < 2 ^ w by omega,
            show editsPtr + 2 * i < 2 ^ w by omega, show editsPtr + 2 * i + 1 < 2 ^ w by omega, hEdgeAt],
          rfl, rfl, rfl⟩
      have rt3 : Runs w p ω' (.assign 8 (.const 0)) t2 .normal t3 2 :=
        runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
      have hKeepBit : ∀ b : Bool,
          (match edits[i] with | .delete e => decide (e ∈ active) | .insert _ => true) = b →
          ∃ t4 c4, Runs w p ω'
            (.cond (.bin .eq (.reg 6) (.const 1)) (.assign 8 (.const 1))
              (.cond (.load (.bin .add (.reg 2) (.reg 7))) (.assign 8 (.const 1)) .nop))
            t3 .normal t4 c4 ∧ c4 ≤ 13 ∧ t4.mem = s.mem ∧
            t4.regs 8 = (if b then 1 else 0) ∧ (∀ r ≠ 8, t4.regs r = t3.regs r) := by
        intro b hb
        cases hCi : edits[i] with
        | insert e =>
          have hbT : b = true := by rw [← hb, hCi]
          subst hbT
          have rSet : Runs w p ω' (.assign 8 (.const 1)) t3 .normal { t3 with regs := Function.update t3.regs 8 1 } 2 :=
            runs_assign_iff.mpr ⟨1, by simp [Expr.eval, hw1], rfl, rfl, rfl⟩
          refine ⟨{ t3 with regs := Function.update t3.regs 8 1 }, 6, ?_, by omega, rfl, by simp,
            fun r hr => Function.update_of_ne hr _ _⟩
          refine runs_cond_iff.mpr ⟨1, 2, by simp [Expr.eval, BinOp.eval, t3, t2, t1, hCi, treeChangeTag, hw1],
            by simpa using rSet, by simp [Expr.size]⟩
        | delete e =>
          have heLt : e < intCap := by simpa [hCi, treeChangeEdge] using hEdgeLt
          have hSlotEq : s.mem (slots + e) = mem (slots + e) := hFr _ (by omega)
          by_cases hAct : e ∈ active
          · have hbT : b = true := by rw [← hb, hCi]; simp [hAct]
            subst hbT
            have hNZ : s.mem (slots + e) ≠ 0 := by rw [hSlotEq]; exact (hSlots e heLt).mpr hAct
            have hCondInner : Runs w p ω' (.cond (.load (.bin .add (.reg 2) (.reg 7))) (.assign 8 (.const 1)) .nop)
                t3 .normal { t3 with regs := Function.update t3.regs 8 1 } 7 :=
              runs_cond_iff.mpr ⟨s.mem (slots + e), 2, by
                simp [Expr.eval, BinOp.eval, t3, t2, t1, h2, hCi, treeChangeEdge, show slots + e < 2 ^ w by omega],
                by simp only [hNZ, ↓reduceIte]
                   exact runs_assign_iff.mpr ⟨1, by simp [Expr.eval, hw1], rfl, rfl, rfl⟩,
                by simp [Expr.size]⟩
            refine ⟨{ t3 with regs := Function.update t3.regs 8 1 }, 11,
              runs_cond_iff.mpr ⟨0, 7, by simp [Expr.eval, BinOp.eval, t3, t2, t1, hCi, treeChangeTag, hw1],
                by simpa using hCondInner, by simp [Expr.size]⟩,
              by omega, rfl, by simp, fun r hr => Function.update_of_ne hr _ _⟩
          · have hbF : b = false := by rw [← hb, hCi]; simp [hAct]
            subst hbF
            have hZ : s.mem (slots + e) = 0 := by
              by_contra hne; exact hAct ((hSlots e heLt).mp (hSlotEq ▸ hne))
            have hCondInner : Runs w p ω' (.cond (.load (.bin .add (.reg 2) (.reg 7))) (.assign 8 (.const 1)) .nop)
                t3 .normal t3 6 :=
              runs_cond_iff.mpr ⟨0, 1, by
                simp [Expr.eval, BinOp.eval, t3, t2, t1, h2, hCi, treeChangeEdge,
                  show slots + e < 2 ^ w by omega, hZ],
                by simp [runs_nop_iff], by simp [Expr.size]⟩
            refine ⟨t3, 10,
              runs_cond_iff.mpr ⟨0, 6, by simp [Expr.eval, BinOp.eval, t3, t2, t1, hCi, treeChangeTag, hw1],
                by simpa using hCondInner, by simp [Expr.size]⟩,
              by omega, rfl, by simp [t3], fun _ _ => rfl⟩
      set keepB := match edits[i] with | .delete e => decide (e ∈ active) | .insert _ => true
      obtain ⟨t4, c4, rt4, hc4, ht4Mem, ht4_8, ht4Regs⟩ := hKeepBit keepB rfl
      have hTakeNext : filterActiveEdits active (edits.take (i + 1)) =
          if keepB then pref ++ [edits[i]] else pref := by
        simp only [filterActiveEdits, List.take_succ_eq_append_getElem hi, List.filter_append,
          List.filter_cons, List.filter_nil, pref, keepB]
        cases hCi : edits[i] with
        | insert _ => simp
        | delete e => by_cases he : e ∈ active <;> simp [he]
      let storeThen : Stmt :=
        .store (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 4))) (.reg 6) ;;
        .store (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 4))) (.const 1)) (.reg 7) ;;
        .assign 4 (.bin .add (.reg 4) (.const 1))
      cases hkb : keepB with
      | false =>
        have rStore : Runs w p ω' (.cond (.reg 8) storeThen .nop) t4 .normal t4 3 :=
          runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, ht4_8, hkb], by simp [runs_nop_iff], by simp [Expr.size]⟩
        have hInvN : Inv (i + 1) { t4 with regs := Function.update t4.regs 5 (i + 1) } := by
          dsimp only [Inv]; rw [hTakeNext, hkb]; simp only [Bool.false_eq_true, ↓reduceIte]
          exact ⟨by simp [ht4Regs 0 (by decide), t3, t2, t1, h0],
            by simp [ht4Regs 1 (by decide), t3, t2, t1, h1],
            by simp [ht4Regs 2 (by decide), t3, t2, t1, h2],
            by simp [ht4Regs 3 (by decide), t3, t2, t1, h3],
            by simp [ht4Regs 4 (by decide), t3, t2, t1, h4], by simp,
            ht4Mem.symm ▸ hAt, ht4Mem.symm ▸ hzS, fun a ha => ht4Mem.symm ▸ hFr a ha⟩
        refine ⟨.normal, t4, _,
          runs_seq_iff.mpr (Or.inr ⟨t1, 7, _, rt1,
            runs_seq_iff.mpr (Or.inr ⟨t2, 9, _, rt2,
              runs_seq_iff.mpr (Or.inr ⟨t3, 2, _, rt3,
                runs_seq_iff.mpr (Or.inr ⟨t4, c4, 3, rt4, rStore, rfl⟩), rfl⟩), rfl⟩), rfl⟩),
          ⟨hInvN, by simp [ht4Regs 5 (by decide), t3, t2, t1, h5]⟩, by dsimp [stepCost]; omega⟩
      | true =>
        let a0 := outPtr + 2 * pref.length
        let t5 := { t4 with mem := Function.update t4.mem a0 (treeChangeTag edits[i]) }
        let t6 := { t5 with mem := Function.update t5.mem (a0 + 1) (treeChangeEdge edits[i]) }
        let t7 := { t6 with regs := Function.update t6.regs 4 (pref.length + 1) }
        have rt5 : Runs w p ω' (.store (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 4))) (.reg 6))
            t4 .normal t5 7 :=
          runs_store_iff.mpr ⟨a0, treeChangeTag edits[i], by
            simp [Expr.eval, BinOp.eval, ht4Regs 3 (by decide), ht4Regs 4 (by decide), t3, t2, t1, h3, h4,
              hw2, show 2 * pref.length < 2 ^ w by omega, show a0 < 2 ^ w by dsimp [a0]; omega, a0],
            by simp [Expr.eval, ht4Regs 6 (by decide), t3, t2, t1], rfl, rfl, rfl⟩
        have rt6 : Runs w p ω' (.store (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 4))) (.const 1)) (.reg 7))
            t5 .normal t6 9 :=
          runs_store_iff.mpr ⟨a0 + 1, treeChangeEdge edits[i], by
            simp [Expr.eval, BinOp.eval, t5, ht4Regs 3 (by decide), ht4Regs 4 (by decide), t3, t2, t1, h3, h4,
              hw2, hw1, show 2 * pref.length < 2 ^ w by omega, show a0 < 2 ^ w by dsimp [a0]; omega,
              show a0 + 1 < 2 ^ w by dsimp [a0]; omega, a0],
            by simp [Expr.eval, t5, ht4Regs 7 (by decide), t3, t2, t1], rfl, rfl, rfl⟩
        have rt7 : Runs w p ω' (.assign 4 (.bin .add (.reg 4) (.const 1))) t6 .normal t7 4 :=
          runs_assign_iff.mpr ⟨pref.length + 1, by
            simp [Expr.eval, BinOp.eval, t6, t5, ht4Regs 4 (by decide), t3, t2, t1, h4, hw1,
              show pref.length + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
        have rStore : Runs w p ω' (.cond (.reg 8) storeThen .nop) t4 .normal t7 24 :=
          runs_cond_iff.mpr ⟨1, 22, by simp [Expr.eval, ht4_8, hkb],
            by simpa [storeThen] using runs_seq_iff.mpr (Or.inr ⟨t5, 7, _, rt5,
                runs_seq_iff.mpr (Or.inr ⟨t6, 9, 4, rt6, rt7, rfl⟩), rfl⟩),
            by simp [Expr.size]⟩
        have hInvN : Inv (i + 1) { t7 with regs := Function.update t7.regs 5 (i + 1) } := by
          dsimp only [Inv]; rw [hTakeNext, hkb]; simp only [↓reduceIte, List.length_append, List.length_singleton]
          refine ⟨by simp [t7, t6, t5, ht4Regs 0 (by decide), t3, t2, t1, h0],
            by simp [t7, t6, t5, ht4Regs 1 (by decide), t3, t2, t1, h1],
            by simp [t7, t6, t5, ht4Regs 2 (by decide), t3, t2, t1, h2],
            by simp [t7, t6, t5, ht4Regs 3 (by decide), t3, t2, t1, h3],
            by simp [t7], by simp, ?_, ?_, ?_⟩
          · refine treeEditsAt_append_singleton
              (treeEditsAt_of_agree hAt (fun j hj => by
                simp only [t7, t6, t5, Function.update_of_ne (by dsimp [a0]; omega : outPtr + j ≠ a0 + 1),
                  Function.update_of_ne (by dsimp [a0]; omega : outPtr + j ≠ a0), ht4Mem]))
              (by simp [t7, t6, t5, a0])
              (by simp [t7, t6, t5, a0])
          · intro a ha
            simp only [t7, t6, t5, Function.update_of_ne (by dsimp [a0]; omega : a ≠ a0 + 1),
              Function.update_of_ne (by dsimp [a0]; omega : a ≠ a0), ht4Mem]
            exact hzS a (by omega)
          · intro a ha
            simp only [t7, t6, t5, Function.update_of_ne (by dsimp [a0]; omega : a ≠ a0 + 1),
              Function.update_of_ne (by dsimp [a0]; omega : a ≠ a0), ht4Mem]
            exact hFr a ha
        refine ⟨.normal, t7, _,
          runs_seq_iff.mpr (Or.inr ⟨t1, 7, _, rt1,
            runs_seq_iff.mpr (Or.inr ⟨t2, 9, _, rt2,
              runs_seq_iff.mpr (Or.inr ⟨t3, 2, _, rt3,
                runs_seq_iff.mpr (Or.inr ⟨t4, c4, 24, rt4, rStore, rfl⟩), rfl⟩), rfl⟩), rfl⟩),
          ⟨hInvN, by simp [t7, t6, t5, ht4Regs 5 (by decide), t3, t2, t1, h5]⟩, by dsimp [stepCost]; omega⟩)
  obtain ⟨o, out, cLoop, rLoop, hout, hcLoop⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hout
  | normal =>
    obtain ⟨_, _, _, _, h4End, _, hAtEnd, hzEnd, hFrEnd⟩ := hout
    rw [List.take_length] at h4End hAtEnd hzEnd
    have rRet : Runs w p ω (.ret (.reg 4)) out (.returned (filterActiveEdits active edits).length) out 2 :=
      runs_ret_iff.mpr ⟨_, by simp [Expr.eval, h4End], rfl, rfl, rfl⟩
    have rAll := runs_seq_iff.mpr (Or.inr ⟨s1, 2, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨out, cLoop, 2, rLoop, rRet, rfl⟩), rfl⟩)
    refine ⟨out, _, rAll, ?_, hAtEnd, hzEnd, hFrEnd⟩
    have hrc : rangeCost (fun _ => stepCost) 0 edits.length = edits.length * stepCost := by simp [rangeCost]
    simp only [Expr.size, hrc] at hcLoop
    have hm : edits.length * stepCost + edits.length * 9 = 69 * edits.length := by dsimp [stepCost]; ring
    omega

end MinCostFlow.MinRatio
