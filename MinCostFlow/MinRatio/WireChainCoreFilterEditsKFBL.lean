module

public import MinCostFlow.MinRatio.WireChainCoreTreeCutsKFBL
import all MinCostFlow.MinRatio.TreeEditLayout
import WordRAM.Memory
import WordRAM.Tactic

/-!
# Drop the cuts of absent edges from an edit list (`WireChainCoreFilterEditsKFBL`)

The last sync of Branch B applies the edits from the old forests of the rebuilt levels to the new
ones. The edit packer writes them, but some of its cuts name edges that are no longer on the
tree: the deleted names of the batch, which the first sync of Branch B cut already. The batch
removed these names from the root graph, and every other edge of the old forests is still in it.
So the core keeps a cut only when its edge is present in the root graph, which one word of the
graph says (the presence array of `DynGraphAt`).

`wireFilterPresentEditsBody` copies an edit list and drops each cut whose presence word is `0`.
It keeps every link. `wireFilterPresentEditsBody_runs` gives its run: the output is
`filterPresentEdits pres edits`, in list order, at cost `70` per edit plus `20`, and no word below
the output buffer changes.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain DynSpanner.Program

/-- Keep every link, and a cut only when the presence word of its edge is not `0`. -/
@[expose] def keepPresentEdit (pres : ℕ → ℕ) : TreeChange → Bool
  | .insert _ => true
  | .delete e => pres e != 0

/-- The edits that `keepPresentEdit` keeps, in order. -/
@[expose] def filterPresentEdits (pres : ℕ → ℕ) (edits : List TreeChange) : List TreeChange :=
  edits.filter (keepPresentEdit pres)

theorem filterPresentEdits_length_le (pres : ℕ → ℕ) (edits : List TreeChange) :
    (filterPresentEdits pres edits).length ≤ edits.length :=
  List.length_filter_le _ _

/-- Procedure `[src, len, pres, outBuf]` (`regs 0..3`): for `i < len`, it reads the edit
`[tag, e]` at `src + 2 i` and copies it to `outBuf + 2 c` when `tag + mem (pres + e) ≠ 0`, where
`c` (`reg 4`) counts the kept edits. It returns the count. -/
@[expose] def wireFilterPresentEditsBody : Stmt :=
  .assign 4 (.const 0) ;;
  forRange 5 (.const 0) (.reg 1)
    (.assign 6 (.load (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 5)))) ;;
     .assign 7 (.load (.bin .add (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 5)))
       (.const 1))) ;;
     .assign 8 (.bin .add (.reg 6) (.load (.bin .add (.reg 2) (.reg 7)))) ;;
     .cond (.reg 8)
       (.store (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 4))) (.reg 6) ;;
        .store (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 4))) (.const 1))
          (.reg 7) ;;
        .assign 4 (.bin .add (.reg 4) (.const 1)))
       .nop) ;;
  .ret (.reg 4)

theorem wireFilterPresentEditsBody_noRand : wireFilterPresentEditsBody.NoRand := by
  simp [wireFilterPresentEditsBody, forRange, forUp, Stmt.NoRand]

/-- The record of edit `i` of a packed edit list. -/
theorem treeEditsAt_get {mem : ℕ → ℕ} {base : ℕ} {edits : List TreeChange}
    (h : TreeEditsAt mem base edits) {i : ℕ} (hi : i < edits.length) :
    ListAt mem (base + 2 * i) (treeEditWords edits[i]) := by
  have hsplit : edits.take i ++ edits[i] :: edits.drop (i + 1) = edits := by
    rw [← List.drop_eq_getElem_cons hi]; exact List.take_append_drop i edits
  unfold TreeEditsAt at h
  rw [← hsplit, List.flatMap_append, List.flatMap_cons] at h
  have h2 := (listAt_append.mp (listAt_append.mp h).2).1
  have hlen : ((edits.take i).flatMap treeEditWords).length = 2 * i := by
    rw [treeEditWords_length, List.length_take]; omega
  rwa [hlen] at h2

/-- A packed edit list grows by one edit, whose two words are written right after it. -/
theorem treeEditsAt_snoc {mem : ℕ → ℕ} {base tg e : ℕ} {cs : List TreeChange} {ch : TreeChange}
    (h : TreeEditsAt mem base cs) (hw : treeEditWords ch = [tg, e])
    (h0 : mem (base + 2 * cs.length) = tg) (h1 : mem (base + 2 * cs.length + 1) = e) :
    TreeEditsAt mem base (cs ++ [ch]) := by
  unfold TreeEditsAt at h ⊢
  rw [List.flatMap_append]
  refine listAt_append.mpr ⟨h, ?_⟩
  rw [treeEditWords_length]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hw]
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · simpa using h0
  · simpa using h1

theorem treeEditWords_cases (ch : TreeChange) :
    ∃ tg e, treeEditWords ch = [tg, e] ∧ tg ≤ 1 ∧
      ∀ pres : ℕ → ℕ, keepPresentEdit pres ch = (tg + pres e != 0) := by
  cases ch with
  | insert e => exact ⟨1, e, rfl, le_rfl, fun pres => by simp [keepPresentEdit]⟩
  | delete e => exact ⟨0, e, rfl, by omega, fun pres => by simp [keepPresentEdit]⟩

set_option maxHeartbeats 1000000 in
/-- The run of `wireFilterPresentEditsBody`. The edits lie at `src` below the zero buffer at
`outBuf`, and so do the presence words of their edges, which are at most `1`. Afterwards the
buffer holds `filterPresentEdits (fun e => mem (pres + e)) edits`, the words from its end on are
zero, and no word below `outBuf` changes. The cost is `70` per edit plus `20`. -/
theorem wireFilterPresentEditsBody_runs
    {w src len pres outBuf pos : ℕ} {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    {edits : List TreeChange}
    (hLen : edits.length = len) (hEd : TreeEditsAt mem src edits)
    (hSrcLe : src + 2 * len ≤ outBuf)
    (hPres : ∀ i (h : i < edits.length), ∀ tg e, treeEditWords edits[i] = [tg, e] →
      pres + e < outBuf ∧ mem (pres + e) ≤ 1)
    (hz : ZeroFrom mem outBuf)
    (hRoom : outBuf + 2 * len + 1 < 2 ^ w) (hw3 : 3 < 2 ^ w) :
    let kept := filterPresentEdits (fun e => mem (pres + e)) edits
    ∃ out cost,
      Runs w p ω wireFilterPresentEditsBody (startState [src, len, pres, outBuf] mem pos)
        (.returned kept.length) out cost ∧
      cost ≤ 70 * len + 20 ∧
      TreeEditsAt out.mem outBuf kept ∧
      ZeroFrom out.mem (outBuf + 2 * kept.length) ∧
      ∀ a < outBuf, out.mem a = mem a := by
  dsimp only
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hwne : w ≠ 0 := by rintro rfl; simp at hw1
  have hLenW : len < 2 ^ w := by omega
  let keep := keepPresentEdit (fun e => mem (pres + e))
  let s0 := startState [src, len, pres, outBuf] mem pos
  let s1 := { s0 with regs := Function.update s0.regs 4 0 }
  have r1 : Runs w p ω (.assign 4 (.const 0)) s0 .normal s1 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, Nat.two_pow_pos w], rfl, rfl, rfl⟩
  let Inv (i : ℕ) (s : State) : Prop :=
    let pref := (edits.take i).filter keep
    s.regs 0 = src ∧ s.regs 1 = len ∧ s.regs 2 = pres ∧ s.regs 3 = outBuf ∧
    s.regs 4 = pref.length ∧ s.regs 5 = i ∧
    TreeEditsAt s.mem outBuf pref ∧
    ZeroFrom s.mem (outBuf + 2 * pref.length) ∧
    ∀ a < outBuf, s.mem a = mem a
  have hloop := Triple.forRange_le (w := w) (p := p) (r := 5) (lo := .const 0) (hi := .reg 1)
    (P := fun s => s = s1) (Inv := Inv) (fun _ => 55) 0 len (Nat.zero_le _) hw1
    (fun _ => hLenW)
    (fun s hs => by
      subst hs
      refine ⟨by simp [Expr.eval, Nat.two_pow_pos w], ?_⟩
      refine ⟨by simp [s1, s0, startState], by simp [s1, s0, startState],
        by simp [s1, s0, startState], by simp [s1, s0, startState],
        by simp [s1], by simp, by simp [TreeEditsAt, ListAt],
        by simpa [s1, s0, startState] using hz, fun _ _ => rfl⟩)
    (fun _ _ _ _ h => h.2.2.2.2.2.1)
    (fun _ s _ _ h => by simp [Expr.eval, h.2.1])
    (fun i _ hi s ω' ⟨h0, h1, h2, h3, h4, h5, hList, hZ, hFr⟩ => by
      have hiE : i < edits.length := by omega
      set ch := edits[i] with hch
      set pref := (edits.take i).filter keep with hpref
      have hPrefLe : pref.length ≤ i := by
        have := List.length_filter_le keep (edits.take i)
        simp only [List.length_take] at this; omega
      obtain ⟨tg, e, htw, htg, hkeepEq⟩ := treeEditWords_cases ch
      have hRec := treeEditsAt_get hEd hiE
      rw [← hch, htw] at hRec
      have hmT : s.mem (src + 2 * i) = tg := by
        rw [hFr _ (by omega)]; simpa using hRec 0 (by simp)
      have hmE : s.mem (src + 2 * i + 1) = e := by
        rw [hFr _ (by omega)]; simpa using hRec 1 (by simp)
      obtain ⟨hPresLt, hPresLe⟩ := hPres i hiE tg e htw
      have hmP : s.mem (pres + e) = mem (pres + e) := hFr _ hPresLt
      have h2iW : 2 * i < 2 ^ w := by omega
      have hSrcW : src + 2 * i < 2 ^ w := by omega
      let t1 := { s with regs := Function.update s.regs 6 tg }
      let t2 := { t1 with regs := Function.update t1.regs 7 e }
      let t3 := { t2 with regs := Function.update t2.regs 8 (tg + mem (pres + e)) }
      have rt1 : Runs w p ω'
          (.assign 6 (.load (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 5))))) s .normal
            t1 7 :=
        runs_assign_iff.mpr ⟨tg, by
          simp [Expr.eval, BinOp.eval, h0, h5, hw2, h2iW, hSrcW, hmT], rfl, rfl, rfl⟩
      have rt2 : Runs w p ω'
          (.assign 7 (.load (.bin .add (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 5)))
            (.const 1)))) t1 .normal t2 9 :=
        runs_assign_iff.mpr ⟨e, by
          simp [Expr.eval, BinOp.eval, t1, h0, h5, hw2, hw1, h2iW, hSrcW,
            show src + 2 * i + 1 < 2 ^ w by omega, hmE], rfl, rfl, rfl⟩
      have rt3 : Runs w p ω'
          (.assign 8 (.bin .add (.reg 6) (.load (.bin .add (.reg 2) (.reg 7))))) t2 .normal
            t3 7 :=
        runs_assign_iff.mpr ⟨tg + mem (pres + e), by
          simp [Expr.eval, BinOp.eval, t2, t1, h2, show pres + e < 2 ^ w by omega, hmP,
            show tg + mem (pres + e) < 2 ^ w by omega], rfl, rfl, rfl⟩
      have hTake : (edits.take (i + 1)).filter keep =
          pref ++ (if keep ch then [ch] else []) := by
        rw [List.take_succ_eq_append_getElem hiE, List.filter_append, ← hch]
        cases hk : keep ch <;> simp [List.filter, hk, hpref]
      have hkeep : keep ch = (tg + mem (pres + e) != 0) := hkeepEq _
      by_cases hs : tg + mem (pres + e) = 0
      · -- the edit is dropped
        have hk : keep ch = false := by rw [hkeep, hs]; rfl
        have rC : Runs w p ω'
            (.cond (.reg 8)
              (.store (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 4))) (.reg 6) ;;
               .store (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 4)))
                 (.const 1)) (.reg 7) ;;
               .assign 4 (.bin .add (.reg 4) (.const 1)))
              .nop) t3 .normal t3 (1 + 1 + 1) :=
          runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, t3, hs],
            by simpa using (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩ :
              Runs w p ω' .nop t3 .normal t3 1), by simp [Expr.size]⟩
        refine ⟨.normal, t3, _, runs_seq_iff.mpr (Or.inr ⟨t1, 7, _, rt1,
          runs_seq_iff.mpr (Or.inr ⟨t2, 9, _, rt2,
            runs_seq_iff.mpr (Or.inr ⟨t3, 7, _, rt3, rC, rfl⟩), rfl⟩), rfl⟩), ⟨?_, ?_⟩,
          by dsimp only; omega⟩
        · dsimp only [Inv]
          rw [hTake, hk]
          simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
          exact ⟨by simp [t3, t2, t1, h0], by simp [t3, t2, t1, h1], by simp [t3, t2, t1, h2],
            by simp [t3, t2, t1, h3], by simp [t3, t2, t1, h4], by simp,
            hList, hZ, hFr⟩
        · simp [t3, t2, t1, h5]
      · -- the edit is kept
        have hk : keep ch = true := by rw [hkeep]; simpa using hs
        have hAW : outBuf + 2 * pref.length + 1 < 2 ^ w := by omega
        let t4 := { t3 with mem := Function.update t3.mem (outBuf + 2 * pref.length) tg }
        let t5 := { t4 with mem := Function.update t4.mem (outBuf + 2 * pref.length + 1) e }
        let t6 := { t5 with regs := Function.update t5.regs 4 (pref.length + 1) }
        have rS1 : Runs w p ω'
            (.store (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 4))) (.reg 6)) t3 .normal
              t4 7 :=
          runs_store_iff.mpr ⟨outBuf + 2 * pref.length, tg, by
            simp [Expr.eval, BinOp.eval, t3, t2, t1, h3, h4, hw2,
              show 2 * pref.length < 2 ^ w by omega,
              show outBuf + 2 * pref.length < 2 ^ w by omega],
            by simp [Expr.eval, t3, t2, t1], rfl, rfl, rfl⟩
        have rS2 : Runs w p ω'
            (.store (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 4))) (.const 1))
              (.reg 7)) t4 .normal t5 9 :=
          runs_store_iff.mpr ⟨outBuf + 2 * pref.length + 1, e, by
            simp [Expr.eval, BinOp.eval, t4, t3, t2, t1, h3, h4, hw2, hw1,
              show 2 * pref.length < 2 ^ w by omega,
              show outBuf + 2 * pref.length < 2 ^ w by omega, hAW],
            by simp [Expr.eval, t4, t3, t2, t1], rfl, rfl, rfl⟩
        have rA : Runs w p ω' (.assign 4 (.bin .add (.reg 4) (.const 1))) t5 .normal t6 4 :=
          runs_assign_iff.mpr ⟨pref.length + 1, by
            simp [Expr.eval, BinOp.eval, t5, t4, t3, t2, t1, h4, hw1,
              show pref.length + 1 < 2 ^ w by omega],
            rfl, rfl, rfl⟩
        have rC : Runs w p ω'
            (.cond (.reg 8)
              (.store (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 4))) (.reg 6) ;;
               .store (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 4)))
                 (.const 1)) (.reg 7) ;;
               .assign 4 (.bin .add (.reg 4) (.const 1)))
              .nop) t3 .normal t6 (1 + (7 + (9 + 4 + 1) + 1) + 1) :=
          runs_cond_iff.mpr ⟨tg + mem (pres + e), 7 + (9 + 4 + 1) + 1, by simp [Expr.eval, t3],
            by
              simp only [hs, ↓reduceIte]
              exact runs_seq_iff.mpr (Or.inr ⟨t4, 7, _, rS1,
                runs_seq_iff.mpr (Or.inr ⟨t5, 9, 4, rS2, rA, rfl⟩), rfl⟩),
            by simp [Expr.size]⟩
        refine ⟨.normal, t6, _, runs_seq_iff.mpr (Or.inr ⟨t1, 7, _, rt1,
          runs_seq_iff.mpr (Or.inr ⟨t2, 9, _, rt2,
            runs_seq_iff.mpr (Or.inr ⟨t3, 7, _, rt3, rC, rfl⟩), rfl⟩), rfl⟩), ⟨?_, ?_⟩,
          by dsimp only; omega⟩
        · dsimp only [Inv]
          rw [hTake, hk]
          simp only [↓reduceIte]
          refine ⟨by simp [t6, t5, t4, t3, t2, t1, h0], by simp [t6, t5, t4, t3, t2, t1, h1],
            by simp [t6, t5, t4, t3, t2, t1, h2], by simp [t6, t5, t4, t3, t2, t1, h3],
            by simp [t6], by simp [t6, t5, t4, t3, t2, t1], ?_, ?_, ?_⟩
          · refine treeEditsAt_snoc ?_ htw ?_ (by simp [t6, t5])
            · intro j hj
              have hjlt : j < 2 * pref.length := by rw [treeEditWords_length] at hj; exact hj
              rw [← hList j hj]
              simp only [t6, t5, t4, t3, t2, t1]
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            · simp only [t6, t5, t4]
              rw [Function.update_of_ne (by omega)]
              simp
          · intro a ha
            simp only [List.length_append, List.length_singleton] at ha
            simp only [t6, t5, t4, t3, t2, t1]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hZ a (by omega)
          · intro a ha
            simp only [t6, t5, t4, t3, t2, t1]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hFr a ha
        · simp [t6, t5, t4, t3, t2, t1, h5])
  obtain ⟨o, s2, cLoop, rLoop, hInv2, hcLoop⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hInv2
  | normal =>
    obtain ⟨_, _, _, _, h4, _, hList2, hZ2, hFr2⟩ := hInv2
    have hTakeAll : edits.take len = edits := List.take_of_length_le (by omega)
    rw [hTakeAll] at h4 hList2 hZ2
    have rRet : Runs w p ω (.ret (.reg 4)) s2 (.returned (edits.filter keep).length) s2 2 :=
      runs_ret_iff.mpr ⟨(edits.filter keep).length, by simp [Expr.eval, h4], rfl, rfl, rfl⟩
    have rAll : Runs w p ω wireFilterPresentEditsBody s0 (.returned (edits.filter keep).length)
        s2 (2 + (cLoop + 2 + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨s1, 2, _, r1,
        runs_seq_iff.mpr (Or.inr ⟨s2, cLoop, 2, rLoop, rRet, rfl⟩), rfl⟩)
    have hrc : rangeCost (fun _ => 55) 0 len = len * 55 := by simp [rangeCost]
    simp only [Expr.size, hrc] at hcLoop
    exact ⟨s2, _, rAll, by omega, hList2, hZ2, hFr2⟩

/-- The filtered packer output is the edit list of the last sync of Branch B. The packer goes
from `A` to `B`. The tree holds `A ∩ X` and a part `P` off both, where `X` is the set of present
edges: the presence word of an edge of `A` is not `0` exactly when it is in `X`, and `B ⊆ X`.
Dropping the cuts of absent edges gives the edits from `P ∪ (A ∩ X)` to `P ∪ B`. -/
theorem treeEditDifference_filterPresent {A B P X : Finset ℕ} {edits : List TreeChange}
    {pres : ℕ → ℕ} (hD : TreeEditDifference A B edits)
    (hPres : ∀ e ∈ A, pres e ≠ 0 ↔ e ∈ X) (hBX : B ⊆ X)
    (hPA : ∀ e ∈ P, e ∉ A) (hPB : ∀ e ∈ P, e ∉ B) :
    TreeEditDifference (P ∪ (A ∩ X)) (P ∪ B) (filterPresentEdits pres edits) := by
  unfold TreeEditDifference at hD ⊢
  obtain ⟨dels, ins, hdp, hip, rfl⟩ := hD
  have hdMem : ∀ e, e ∈ dels ↔ e ∈ A ∧ e ∉ B := fun e => by
    rw [hdp.mem_iff, Finset.mem_toList, Finset.mem_sdiff]
  have hiMem : ∀ e, e ∈ ins ↔ e ∈ B ∧ e ∉ A := fun e => by
    rw [hip.mem_iff, Finset.mem_toList, Finset.mem_sdiff]
  have hdNd : dels.Nodup := hdp.nodup_iff.mpr (Finset.nodup_toList _)
  have hiNd : ins.Nodup := hip.nodup_iff.mpr (Finset.nodup_toList _)
  refine ⟨dels.filter (fun e => pres e != 0), ins, ?_, ?_, ?_⟩
  · apply List.perm_of_nodup_nodup_toFinset_eq (hdNd.filter _) (Finset.nodup_toList _)
    ext e
    simp only [List.mem_toFinset, List.mem_filter, hdMem, Finset.toList_toFinset,
      Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter, bne_iff_ne, ne_eq]
    constructor
    · rintro ⟨⟨hA, hB⟩, hp⟩
      exact ⟨Or.inr ⟨hA, (hPres e hA).mp hp⟩, fun h => h.elim (fun hP => hPA e hP hA) hB⟩
    · rintro ⟨h1, h2⟩
      rcases h1 with hP | ⟨hA, hX⟩
      · exact absurd (Or.inl hP) h2
      · exact ⟨⟨hA, fun hB => h2 (Or.inr hB)⟩, (hPres e hA).mpr hX⟩
  · apply List.perm_of_nodup_nodup_toFinset_eq hiNd (Finset.nodup_toList _)
    ext e
    simp only [List.mem_toFinset, hiMem, Finset.toList_toFinset, Finset.mem_sdiff,
      Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro ⟨hB, hA⟩
      exact ⟨Or.inr hB, fun h => h.elim (fun hP => hPB e hP hB) (fun h => hA h.1)⟩
    · rintro ⟨h1, h2⟩
      rcases h1 with hP | hB
      · exact absurd (Or.inl hP) h2
      · exact ⟨hB, fun hA => h2 (Or.inr ⟨hA, hBX hB⟩)⟩
  · unfold filterPresentEdits
    rw [List.filter_append, List.filter_map, List.filter_map]
    have h1 : (keepPresentEdit pres ∘ TreeChange.delete) = (fun e => pres e != 0) := rfl
    have h2 : (keepPresentEdit pres ∘ TreeChange.insert) = (fun _ => true) := rfl
    rw [h1, h2, List.filter_true]

end MinCostFlow.MinRatio
