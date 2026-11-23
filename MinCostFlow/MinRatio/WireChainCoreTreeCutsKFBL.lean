module

public import MinCostFlow.MinRatio.TreeEditLayout
public import MinCostFlow.DynSpanner.Program.DynGraphLayout
public import MinCostFlow.Bundle.Ordered
import all MinCostFlow.MinRatio.TreeEditLayout
import WordRAM.Memory
import WordRAM.Tactic

/-!
# Tree cuts from a list of edges, skipping the edges off the tree (`WireChainCoreTreeCutsKFBL`)

In Branch B of the chain-update core, three lists of edges name the edges that leave the path
tree: the deleted names of the batch, the lists `fDel j` of the plain levels, and the old forests
of the rebuilt suffix (as the cuts that the edit packer writes). Some of their entries may be off
the tree already: a deleted name of the batch may be off every forest, and the sync of the batch
cuts its deleted names before the loop, so they are off the tree when the later lists name them.
An edge is on the tree exactly when its slot is not `0` (`SolverEdgeAccountsAt`).

So the core turns each list into tree cuts with one procedure, `wireEmitTreeCutsBody`. It reads
the entries `e_i = mem (src + stride * i + off)` for `i < len`, and appends the cut `[0, e_i]` to
the buffer at `outBuf` when the slot `mem (slots + e_i)` is not `0`. The stride and the offset let
it read a plain list (`stride = 1`, `off = 0`) and the edge words of a packed edit list
(`stride = 2`, `off = 1`) alike. The buffer is zero, so the procedure writes only the edge word of
each cut.

`wireEmitTreeCutsBody_runs` gives its run: the buffer then holds the cuts of the entries whose
slot is not `0`, in list order (`TreeEditsAt`), and no word below `outBuf` changes.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain DynSpanner.Program

/-- Procedure `[src, len, stride, off, slots, outBuf]` (`regs 0..5`): for `i < len`, it reads
`e = mem (src + stride * i + off)` and, when `mem (slots + e) ≠ 0`, writes `e` at
`outBuf + 2 c + 1`, where `c` (`reg 6`) counts the cuts so far. It returns the count. -/
@[expose] def wireEmitTreeCutsBody : Stmt :=
  .assign 6 (.const 0) ;;
  forRange 7 (.const 0) (.reg 1)
    (.assign 8 (.load (.bin .add (.bin .add (.reg 0) (.bin .mul (.reg 2) (.reg 7))) (.reg 3))) ;;
     .cond (.load (.bin .add (.reg 4) (.reg 8)))
       (.store (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 2) (.reg 6))) (.const 1))
          (.reg 8) ;;
        .assign 6 (.bin .add (.reg 6) (.const 1)))
       .nop) ;;
  .ret (.reg 6)

theorem wireEmitTreeCutsBody_noRand : wireEmitTreeCutsBody.NoRand := by
  simp [wireEmitTreeCutsBody, forRange, forUp, Stmt.NoRand]

/-- The edges of `es` whose slot is not `0`. -/
@[expose] def treeCutsOf (slot : ℕ → ℕ) (es : List ℕ) : List ℕ :=
  es.filter (fun e => slot e != 0)

theorem treeCutsOf_length_le (slot : ℕ → ℕ) (es : List ℕ) :
    (treeCutsOf slot es).length ≤ es.length :=
  List.length_filter_le _ _

theorem mem_treeCutsOf {slot : ℕ → ℕ} {es : List ℕ} {e : ℕ} :
    e ∈ treeCutsOf slot es ↔ e ∈ es ∧ slot e ≠ 0 := by
  simp [treeCutsOf, List.mem_filter]

theorem treeCutsOf_take_succ (slot : ℕ → ℕ) (es : List ℕ) {i : ℕ} (hi : i < es.length) :
    treeCutsOf slot (es.take (i + 1)) =
      treeCutsOf slot (es.take i) ++ (if slot es[i] = 0 then [] else [es[i]]) := by
  rw [List.take_succ_eq_append_getElem hi, treeCutsOf, List.filter_append]
  by_cases h : slot es[i] = 0 <;> simp [treeCutsOf, h]

/-- A buffer of cuts grows by one cut: the old cuts stay, and the new cut is the tag word `0` (a
zero word of the buffer) and the edge word `e`. -/
theorem treeEditsAt_snoc_delete {mem : ℕ → ℕ} {base : ℕ} {cs : List ℕ} {e : ℕ}
    (h : TreeEditsAt mem base (cs.map TreeChange.delete))
    (h0 : mem (base + 2 * cs.length) = 0) (h1 : mem (base + 2 * cs.length + 1) = e) :
    TreeEditsAt mem base ((cs ++ [e]).map TreeChange.delete) := by
  unfold TreeEditsAt at h ⊢
  rw [List.map_append, List.flatMap_append]
  refine listAt_append.mpr ⟨h, ?_⟩
  have hlen : ((cs.map TreeChange.delete).flatMap treeEditWords).length = 2 * cs.length := by
    rw [treeEditWords_length, List.length_map]
  rw [hlen]
  simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    treeEditWords]
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · simpa using h0
  · simpa using h1

/-- A list of cuts without repeats, all of edges of `E`, is the edit list from `E` to `E` less
those edges. -/
theorem treeEditDifference_cuts {E : Finset ℕ} {cs : List ℕ} (hnd : cs.Nodup)
    (hsub : ∀ e ∈ cs, e ∈ E) :
    TreeEditDifference E (E \ cs.toFinset) (cs.map TreeChange.delete) := by
  refine ⟨cs, [], ?_, ?_, by simp⟩
  · apply List.perm_of_nodup_nodup_toFinset_eq hnd (Finset.nodup_toList _)
    ext e
    simp only [List.mem_toFinset, Finset.toList_toFinset, Finset.mem_sdiff, not_and, not_not]
    exact ⟨fun h => ⟨hsub e h, fun _ => h⟩, fun h => h.2 h.1⟩
  · have : (E \ cs.toFinset) \ E = ∅ := by
      ext e; simp only [Finset.mem_sdiff, Finset.notMem_empty, iff_false]; tauto
    rw [this]; simp

theorem treeCutsOf_nodup {slot : ℕ → ℕ} {es : List ℕ} (h : es.Nodup) :
    (treeCutsOf slot es).Nodup :=
  h.filter _

set_option maxHeartbeats 800000 in
/-- The run of `wireEmitTreeCutsBody`. The entries `es` lie at `src + stride * i + off`, and the
slots that it reads and the entries lie below the zero buffer at `outBuf`. Afterwards the
buffer holds the cuts of `treeCutsOf (fun e => mem (slots + e)) es`, the words from the end of
the cuts on are zero, and no word below `outBuf` changes. The cost is `40` per entry plus `15`. -/
theorem wireEmitTreeCutsBody_runs
    {w src len stride off slots outBuf pos : ℕ} {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    {es : List ℕ}
    (hLen : es.length = len)
    (hEs : ∀ i (h : i < es.length), mem (src + stride * i + off) = es[i])
    (hAddrLt : ∀ i < len, src + stride * i + off < outBuf)
    (hSlotLt : ∀ e ∈ es, slots + e < outBuf)
    (hz : ZeroFrom mem outBuf)
    (hRoom : outBuf + 2 * len + 1 < 2 ^ w) (hw2 : 2 < 2 ^ w) :
    let cuts := treeCutsOf (fun e => mem (slots + e)) es
    ∃ out cost,
      Runs w p ω wireEmitTreeCutsBody
        (startState [src, len, stride, off, slots, outBuf] mem pos)
        (.returned cuts.length) out cost ∧
      cost ≤ 40 * len + 15 ∧
      TreeEditsAt out.mem outBuf (cuts.map TreeChange.delete) ∧
      ZeroFrom out.mem (outBuf + 2 * cuts.length) ∧
      ∀ a < outBuf, out.mem a = mem a := by
  dsimp only
  have hw1 : 1 < 2 ^ w := by omega
  have hwne : w ≠ 0 := by rintro rfl; simp at hw1
  have hLenW : len < 2 ^ w := by omega
  let slot : ℕ → ℕ := fun e => mem (slots + e)
  let s0 := startState [src, len, stride, off, slots, outBuf] mem pos
  let s1 := { s0 with regs := Function.update s0.regs 6 0 }
  have r1 : Runs w p ω (.assign 6 (.const 0)) s0 .normal s1 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, Nat.two_pow_pos w], rfl, rfl, rfl⟩
  let Inv (i : ℕ) (s : State) : Prop :=
    let pref := treeCutsOf slot (es.take i)
    s.regs 0 = src ∧ s.regs 1 = len ∧ s.regs 2 = stride ∧ s.regs 3 = off ∧
    s.regs 4 = slots ∧ s.regs 5 = outBuf ∧ s.regs 6 = pref.length ∧ s.regs 7 = i ∧
    TreeEditsAt s.mem outBuf (pref.map TreeChange.delete) ∧
    ZeroFrom s.mem (outBuf + 2 * pref.length) ∧
    ∀ a < outBuf, s.mem a = mem a
  have hloop := Triple.forRange_le (w := w) (p := p) (r := 7) (lo := .const 0) (hi := .reg 1)
    (P := fun s => s = s1) (Inv := Inv) (fun _ => 30) 0 len (Nat.zero_le _) hw1
    (fun _ => hLenW)
    (fun s hs => by
      subst hs
      refine ⟨by simp [Expr.eval, Nat.two_pow_pos w], ?_⟩
      refine ⟨by simp [s1, s0, startState], by simp [s1, s0, startState],
        by simp [s1, s0, startState], by simp [s1, s0, startState],
        by simp [s1, s0, startState], by simp [s1, s0, startState],
        by simp [s1, treeCutsOf], by simp, by simp [TreeEditsAt, ListAt, treeCutsOf],
        by simpa [s1, s0, startState, treeCutsOf] using hz, fun _ _ => rfl⟩)
    (fun _ _ _ _ h => h.2.2.2.2.2.2.2.1)
    (fun _ s _ _ h => by simp [Expr.eval, h.2.1])
    (fun i _ hi s ω' ⟨h0, h1, h2, h3, h4, h5, h6, h7, hList, hZ, hFr⟩ => by
      have hiE : i < es.length := by omega
      set e := es[i] with he
      set pref := treeCutsOf slot (es.take i) with hpref
      have hPrefLe : pref.length ≤ i := by
        have := treeCutsOf_length_le slot (es.take i)
        simp only [List.length_take] at this; omega
      have hAddr := hAddrLt i hi
      have hmE : s.mem (src + stride * i + off) = e := by
        rw [hFr _ hAddr]; exact hEs i hiE
      have heMem : e ∈ es := List.getElem_mem hiE
      have hSl := hSlotLt e heMem
      have hmSl : s.mem (slots + e) = slot e := hFr _ hSl
      have hMulW : stride * i < 2 ^ w := by omega
      have hSumW : src + stride * i < 2 ^ w := by omega
      let t1 := { s with regs := Function.update s.regs 8 e }
      have rt1 : Runs w p ω'
          (.assign 8 (.load (.bin .add (.bin .add (.reg 0) (.bin .mul (.reg 2) (.reg 7)))
            (.reg 3)))) s .normal t1 9 :=
        runs_assign_iff.mpr ⟨e, by
          simp [Expr.eval, BinOp.eval, h0, h2, h3, h7, hMulW, hSumW,
            show src + stride * i + off < 2 ^ w by omega, hmE], rfl, rfl, rfl⟩
      have hNewPref : treeCutsOf slot (es.take (i + 1)) =
          pref ++ (if slot e = 0 then [] else [e]) := treeCutsOf_take_succ slot es hiE
      by_cases hs : slot e = 0
      · -- off the tree: no cut
        have rC : Runs w p ω'
            (.cond (.load (.bin .add (.reg 4) (.reg 8)))
              (.store (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 2) (.reg 6))) (.const 1))
                (.reg 8) ;;
               .assign 6 (.bin .add (.reg 6) (.const 1)))
              .nop) t1 .normal t1 (4 + 1 + 1) :=
          runs_cond_iff.mpr ⟨0, 1, by
            simp [Expr.eval, BinOp.eval, t1, h4, show slots + e < 2 ^ w by omega, hmSl, hs],
            by simpa using (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩ :
              Runs w p ω' .nop t1 .normal t1 1), by simp [Expr.size]⟩
        refine ⟨.normal, t1, _, runs_seq_iff.mpr (Or.inr ⟨t1, 9, _, rt1, rC, rfl⟩), ⟨?_, ?_⟩,
          by dsimp only; omega⟩
        · dsimp only [Inv]
          rw [hNewPref, ite_eq_left hs, List.append_nil]
          exact ⟨by simp [t1, h0], by simp [t1, h1], by simp [t1, h2], by simp [t1, h3],
            by simp [t1, h4], by simp [t1, h5], by simp [t1, h6], by simp,
            hList, hZ, hFr⟩
        · simp [t1, h7]
      · -- on the tree: write the cut
        have hAW : outBuf + 2 * pref.length + 1 < 2 ^ w := by omega
        let t2 := { t1 with mem := Function.update t1.mem (outBuf + 2 * pref.length + 1) e }
        let t3 := { t2 with regs := Function.update t2.regs 6 (pref.length + 1) }
        have rS : Runs w p ω'
            (.store (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 2) (.reg 6))) (.const 1))
              (.reg 8)) t1 .normal t2 9 :=
          runs_store_iff.mpr ⟨outBuf + 2 * pref.length + 1, e, by
            simp [Expr.eval, BinOp.eval, t1, h5, h6, hw2, hwne,
              show 2 * pref.length < 2 ^ w by omega,
              show outBuf + 2 * pref.length < 2 ^ w by omega, hAW],
            by simp [Expr.eval, t1], rfl, rfl, rfl⟩
        have rA : Runs w p ω' (.assign 6 (.bin .add (.reg 6) (.const 1))) t2 .normal t3 4 :=
          runs_assign_iff.mpr ⟨pref.length + 1, by
            simp [Expr.eval, BinOp.eval, t2, t1, h6, hwne,
              show pref.length + 1 < 2 ^ w by omega],
            rfl, rfl, rfl⟩
        have rC : Runs w p ω'
            (.cond (.load (.bin .add (.reg 4) (.reg 8)))
              (.store (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 2) (.reg 6))) (.const 1))
                (.reg 8) ;;
               .assign 6 (.bin .add (.reg 6) (.const 1)))
              .nop) t1 .normal t3 (4 + (9 + 4 + 1) + 1) :=
          runs_cond_iff.mpr ⟨slot e, _, by
            simp [Expr.eval, BinOp.eval, t1, h4, show slots + e < 2 ^ w by omega, hmSl],
            by simpa [hs] using runs_seq_iff.mpr (Or.inr ⟨t2, 9, 4, rS, rA, rfl⟩),
            by simp [Expr.size]⟩
        have hZ0 : t3.mem (outBuf + 2 * pref.length) = 0 := by
          simp only [t3, t2, t1, Function.update_of_ne (show outBuf + 2 * pref.length ≠
            outBuf + 2 * pref.length + 1 by omega)]
          exact hZ _ le_rfl
        refine ⟨.normal, t3, _, runs_seq_iff.mpr (Or.inr ⟨t1, 9, _, rt1, rC, rfl⟩), ⟨?_, ?_⟩,
          by dsimp only; omega⟩
        · dsimp only [Inv]
          rw [hNewPref, ite_eq_right hs]
          refine ⟨by simp [t3, t2, t1, h0], by simp [t3, t2, t1, h1], by simp [t3, t2, t1, h2],
            by simp [t3, t2, t1, h3], by simp [t3, t2, t1, h4], by simp [t3, t2, t1, h5],
            by simp [t3], by simp [t3, t2, t1], ?_, ?_, ?_⟩
          · refine treeEditsAt_snoc_delete ?_ hZ0 (by simp [t3, t2])
            intro j hj
            have hjlt : j < 2 * pref.length := by
              rw [treeEditWords_length, List.length_map] at hj; exact hj
            rw [← hList j hj]
            simp only [t3, t2, t1]
            exact Function.update_of_ne (by omega) _ _
          · intro a ha
            simp only [List.length_append, List.length_singleton] at ha
            simp only [t3, t2, t1, Function.update_of_ne (show a ≠ outBuf + 2 * pref.length + 1
              by omega)]
            exact hZ a (by omega)
          · intro a ha
            simp only [t3, t2, t1, Function.update_of_ne (show a ≠ outBuf + 2 * pref.length + 1
              by omega)]
            exact hFr a ha
        · simp [t3, t2, t1, h7])
  obtain ⟨o, s2, cLoop, rLoop, hInv2, hcLoop⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hInv2
  | normal =>
    obtain ⟨_, _, _, _, _, _, h6, _, hList2, hZ2, hFr2⟩ := hInv2
    have hTakeAll : es.take len = es := List.take_of_length_le (by omega)
    rw [hTakeAll] at h6 hList2 hZ2
    have rRet : Runs w p ω (.ret (.reg 6)) s2 (.returned (treeCutsOf slot es).length) s2 2 :=
      runs_ret_iff.mpr ⟨(treeCutsOf slot es).length, by simp [Expr.eval, h6], rfl, rfl, rfl⟩
    have rAll : Runs w p ω wireEmitTreeCutsBody s0 (.returned (treeCutsOf slot es).length) s2
        (2 + (cLoop + 2 + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨s1, 2, _, r1,
        runs_seq_iff.mpr (Or.inr ⟨s2, cLoop, 2, rLoop, rRet, rfl⟩), rfl⟩)
    have hrc : rangeCost (fun _ => 30) 0 len = len * 30 := by simp [rangeCost]
    simp only [Expr.size, hrc] at hcLoop
    exact ⟨s2, _, rAll, by omega, hList2, hZ2, hFr2⟩

/-! ### The deleted names of a batch -/

/-- The edges that the deletions of a batch name, in order. -/
@[expose] def batchDeletedEdges : List Update → List ℕ
  | [] => []
  | .delete e :: rest => e :: batchDeletedEdges rest
  | .insert _ _ _ :: rest => batchDeletedEdges rest
  | .split _ _ _ _ :: rest => batchDeletedEdges rest

theorem batchDeletedEdges_length_le (U : List Update) :
    (batchDeletedEdges U).length ≤ U.length := by
  induction U with
  | nil => simp [batchDeletedEdges]
  | cons u rest ih => cases u <;> simp [batchDeletedEdges] <;> omega

theorem batchDeletedEdges_append (U₁ U₂ : List Update) :
    batchDeletedEdges (U₁ ++ U₂) = batchDeletedEdges U₁ ++ batchDeletedEdges U₂ := by
  induction U₁ with
  | nil => simp [batchDeletedEdges]
  | cons u rest ih => cases u <;> simp [batchDeletedEdges, ih]

theorem mem_batchDeletedEdges_iff (U : List Update) (e : ℕ) :
    e ∈ batchDeletedEdges U ↔ Update.delete e ∈ U := by
  induction U with
  | nil => simp [batchDeletedEdges]
  | cons u rest ih =>
    cases u with
    | delete e₀ =>
      simp only [batchDeletedEdges, List.mem_cons, ih, Update.delete.injEq]
    | insert _ _ _ => simp [batchDeletedEdges, ih]
    | split _ _ _ _ => simp [batchDeletedEdges, ih]

/-- Procedure `[batchPtr, outBuf]` (`regs 0..1`): scans an edge-only batch at `batchPtr`, writes
the edge of each deletion into `outBuf` as a plain list, and returns the count. An insertion
(tag `0`) takes four words and a deletion two; the procedure treats any other tag as a deletion,
so it is meant for batches without splits. -/
@[expose] def wireCollectDeletedEdgesBody : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.bin .add (.reg 0) (.const 1)) ;;
  .assign 4 (.const 0) ;;
  forRange 5 (.const 0) (.reg 2)
    (.assign 6 (.load (.reg 3)) ;;
     .cond (.bin .eq (.reg 6) (.const 0))
       (.assign 3 (.bin .add (.reg 3) (.const 4)))
       (.assign 7 (.load (.bin .add (.reg 3) (.const 1))) ;;
        .store (.bin .add (.reg 1) (.reg 4)) (.reg 7) ;;
        .assign 4 (.bin .add (.reg 4) (.const 1)) ;;
        .assign 3 (.bin .add (.reg 3) (.const 2)))) ;;
  .ret (.reg 4)

theorem wireCollectDeletedEdgesBody_noRand : wireCollectDeletedEdgesBody.NoRand := by
  simp [wireCollectDeletedEdgesBody, forRange, forUp, Stmt.NoRand]

set_option maxHeartbeats 800000 in
/-- The run of `wireCollectDeletedEdgesBody` on an edge-only batch: it writes
`batchDeletedEdges U` at `outBuf` in at most `50 |U| + 35` steps, and no word below `outBuf`
changes. -/
theorem wireCollectDeletedEdgesBody_runs
    {w batchPtr outBuf totalWords pos : ℕ} {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    {G : MGraph} {U : List Update}
    (hSmall : SmallBatchAt mem batchPtr G U totalWords)
    (hEdgeOnly : ∀ u ∈ U, Bundle.IsEdgeUpdate u)
    (hBatchW : ∀ j < totalWords, mem (batchPtr + j) < 2 ^ w)
    (hBatchLe : batchPtr + totalWords ≤ outBuf)
    (hz : ZeroFrom mem outBuf)
    (hRoom : outBuf + U.length < 2 ^ w)
    (hw5 : 5 < 2 ^ w) :
    let dels := batchDeletedEdges U
    ∃ out cost,
      Runs w p ω wireCollectDeletedEdgesBody
        (startState [batchPtr, outBuf] mem pos)
        (.returned dels.length) out cost ∧
      cost ≤ 50 * U.length + 35 ∧
      ListAt out.mem outBuf dels ∧
      ZeroFrom out.mem (outBuf + dels.length) ∧
      ∀ a < outBuf, out.mem a = mem a := by
  dsimp only
  have hw1 : 1 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  obtain ⟨⟨hTotPos, hLen0, hBody0⟩, _⟩ := hSmall
  have hULenW : U.length < 2 ^ w := by simpa [hLen0] using hBatchW 0 (by omega)
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
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, Nat.two_pow_pos w], rfl, rfl, rfl⟩
  let Inv (i : ℕ) (s : State) : Prop :=
    ∃ ptr remW,
      let pref := batchDeletedEdges (U.take i)
      s.regs 0 = batchPtr ∧ s.regs 1 = outBuf ∧ s.regs 2 = U.length ∧
      s.regs 3 = ptr ∧ s.regs 4 = pref.length ∧ s.regs 5 = i ∧
      batchPtr + 1 ≤ ptr ∧ ptr + remW = batchPtr + totalWords ∧
      BatchBodyAt mem ptr (G.applyBatch (U.take i)) (U.drop i) remW ∧
      ListAt s.mem outBuf pref ∧
      ZeroFrom s.mem (outBuf + pref.length) ∧
      ∀ a < outBuf, s.mem a = mem a
  have hloop := Triple.forRange_le (w := w) (p := p) (r := 5) (lo := .const 0) (hi := .reg 2)
    (P := fun s => s = s3) (Inv := Inv) (fun _ => 38) 0 U.length (Nat.zero_le _) hw1
    (fun _ => hULenW)
    (fun s hs => by
      subst hs
      refine ⟨by simp [Expr.eval, Nat.two_pow_pos w],
        batchPtr + 1, totalWords - 1,
        by simp [s3, s2, s1, s0, startState], by simp [s3, s2, s1, s0, startState],
        by simp [s3, s2, s1], by simp [s3, s2], by simp [s3, batchDeletedEdges], by simp,
        le_rfl, by omega, by simpa [MGraph.applyBatch] using hBody0,
        fun _ h => by simp [batchDeletedEdges] at h,
        by simpa [s3, s2, s1, s0, startState, batchDeletedEdges] using hz, fun _ _ => rfl⟩)
    (fun _ _ _ _ h => by rcases h with ⟨_, _, _, _, _, _, _, h5, _⟩; exact h5)
    (fun _ s _ _ h => by rcases h with ⟨_, _, _, _, h2, _⟩; simp [Expr.eval, h2])
    (fun i _ hi s ω' ⟨ptr, remW, h0, h1, h2, h3, h4, h5, hPtrLo, hPtrEnd, hBody, hList, hZ,
        hFr⟩ => by
      have hDrop : U.drop i = U[i] :: U.drop (i + 1) := List.drop_eq_getElem_cons hi
      rw [hDrop] at hBody
      obtain ⟨uLen, hULenLe, hUAt, hRest⟩ := hBody
      have hTakeSucc : U.take (i + 1) = U.take i ++ [U[i]] :=
        List.take_succ_eq_append_getElem hi
      have hPrefLe : (batchDeletedEdges (U.take i)).length ≤ i :=
        (batchDeletedEdges_length_le _).trans (by simp [List.length_take, Nat.le_of_lt hi])
      have hGStep : G.applyBatch (U.take (i + 1)) =
          (G.applyBatch (U.take i)).applyUpdate U[i] := by
        unfold MGraph.applyBatch
        rw [hTakeSucc, List.foldl_append]
        rfl
      have hEdge := hEdgeOnly U[i] (List.getElem_mem hi)
      cases hu : U[i] with
      | delete e =>
        rw [hu] at hUAt
        obtain ⟨rfl, hLA⟩ := hUAt
        have hTag : mem ptr = 1 := by simpa using hLA 0 (by simp)
        have hE : mem (ptr + 1) = e := by simpa using hLA 1 (by simp)
        have hm0 : s.mem ptr = 1 := (hFr ptr (by omega)).trans hTag
        have hm1 : s.mem (ptr + 1) = e := (hFr (ptr + 1) (by omega)).trans hE
        let pref := batchDeletedEdges (U.take i)
        let t1 := { s with regs := Function.update s.regs 6 1 }
        let t2 := { t1 with regs := Function.update t1.regs 7 e }
        let t3 := { t2 with mem := Function.update t2.mem (outBuf + pref.length) e }
        let t4 := { t3 with regs := Function.update t3.regs 4 (pref.length + 1) }
        let t5 := { t4 with regs := Function.update t4.regs 3 (ptr + 2) }
        have rt1 : Runs w p ω' (.assign 6 (.load (.reg 3))) s .normal t1 3 :=
          runs_assign_iff.mpr ⟨1, by simp [Expr.eval, h3, hm0], rfl, rfl, rfl⟩
        have rt2 : Runs w p ω' (.assign 7 (.load (.bin .add (.reg 3) (.const 1)))) t1 .normal
            t2 5 :=
          runs_assign_iff.mpr ⟨e, by
            simp [Expr.eval, BinOp.eval, t1, h3, hw1, show ptr + 1 < 2 ^ w by omega, hm1],
            rfl, rfl, rfl⟩
        have rt3 : Runs w p ω' (.store (.bin .add (.reg 1) (.reg 4)) (.reg 7)) t2 .normal t3 5 :=
          runs_store_iff.mpr ⟨outBuf + pref.length, e, by
            have hOutPl : outBuf + (batchDeletedEdges (U.take i)).length < 2 ^ w := by omega
            simp [Expr.eval, BinOp.eval, t2, t1, h1, h4, pref, hOutPl],
            by simp [Expr.eval, t2], rfl, rfl, rfl⟩
        have rt4 : Runs w p ω' (.assign 4 (.bin .add (.reg 4) (.const 1))) t3 .normal t4 4 :=
          runs_assign_iff.mpr ⟨pref.length + 1, by
            have hplW : (batchDeletedEdges (U.take i)).length + 1 < 2 ^ w := by omega
            simp [Expr.eval, BinOp.eval, t3, t2, t1, h4, hw1, pref, hplW], rfl, rfl, rfl⟩
        have rt5 : Runs w p ω' (.assign 3 (.bin .add (.reg 3) (.const 2))) t4 .normal t5 4 :=
          runs_assign_iff.mpr ⟨ptr + 2, by
            simp [Expr.eval, BinOp.eval, t4, t3, t2, t1, h3, show 2 < 2 ^ w by omega,
              show ptr + 2 < 2 ^ w by omega], rfl, rfl, rfl⟩
        have rCond : Runs w p ω'
            (.cond (.bin .eq (.reg 6) (.const 0))
              (.assign 3 (.bin .add (.reg 3) (.const 4)))
              (.assign 7 (.load (.bin .add (.reg 3) (.const 1))) ;;
               .store (.bin .add (.reg 1) (.reg 4)) (.reg 7) ;;
               .assign 4 (.bin .add (.reg 4) (.const 1)) ;;
               .assign 3 (.bin .add (.reg 3) (.const 2))))
            t1 .normal t5 (3 + (5 + (5 + (4 + 4 + 1) + 1) + 1) + 1) :=
          runs_cond_iff.mpr ⟨0, _, by simp [Expr.eval, BinOp.eval, t1, Nat.two_pow_pos w],
            by simpa only [↓reduceIte] using
              runs_seq_iff.mpr (Or.inr ⟨t2, 5, _, rt2,
                runs_seq_iff.mpr (Or.inr ⟨t3, 5, _, rt3,
                  runs_seq_iff.mpr (Or.inr ⟨t4, 4, 4, rt4, rt5, rfl⟩), rfl⟩), rfl⟩), rfl⟩
        have rstep : Runs w p ω' _ s .normal t5 _ :=
          runs_seq_iff.mpr (Or.inr ⟨t1, 3, _, rt1, rCond, rfl⟩)
        have hNewPref : batchDeletedEdges (U.take (i + 1)) = pref ++ [e] := by
          rw [hTakeSucc, batchDeletedEdges_append, hu]; rfl
        refine ⟨.normal, t5, _, rstep, ⟨⟨ptr + 2, remW - 2,
          by simp [t5, t4, t3, t2, t1, h0], by simp [t5, t4, t3, t2, t1, h1],
          by simp [t5, t4, t3, t2, t1, h2], by simp [t5],
          by rw [hNewPref]; simp [t5, t4, pref], by simp,
          by omega, by omega, by rw [hGStep]; exact hRest, ?_, ?_, ?_⟩,
          by simp [t5, t4, t3, t2, t1, h5]⟩, by dsimp only; omega⟩
        · rw [hNewPref]
          intro j hj
          simp only [List.length_append, List.length_singleton] at hj
          by_cases hlt : j < pref.length
          · rw [List.getElem_append_left hlt]
            change Function.update s.mem (outBuf + pref.length) e (outBuf + j) = pref[j]
            rw [Function.update_of_ne (by omega)]
            exact hList j hlt
          · have hjeq : j = pref.length := by omega
            subst hjeq
            simp [t5, t4, t3]
        · rw [hNewPref]; intro a ha
          simp only [List.length_append, List.length_singleton] at ha
          change Function.update s.mem (outBuf + pref.length) e a = 0
          rw [Function.update_of_ne (by omega)]
          exact hZ a (by dsimp only [pref] at ha; omega)
        · intro a ha
          change Function.update s.mem (outBuf + pref.length) e a = mem a
          rw [Function.update_of_ne (by omega)]
          exact hFr a ha
      | insert e u v =>
        rw [hu] at hUAt
        obtain ⟨rfl, hLA⟩ := hUAt
        have hTag : mem ptr = 0 := by simpa using hLA 0 (by simp)
        have hm0 : s.mem ptr = 0 := (hFr ptr (by omega)).trans hTag
        let t1 := { s with regs := Function.update s.regs 6 0 }
        let t2 := { t1 with regs := Function.update t1.regs 3 (ptr + 4) }
        have rt1 : Runs w p ω' (.assign 6 (.load (.reg 3))) s .normal t1 3 :=
          runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h3, hm0], rfl, rfl, rfl⟩
        have rt2 : Runs w p ω' (.assign 3 (.bin .add (.reg 3) (.const 4))) t1 .normal t2 4 :=
          runs_assign_iff.mpr ⟨ptr + 4, by
            simp [Expr.eval, BinOp.eval, t1, h3, hw4, show ptr + 4 < 2 ^ w by omega],
            rfl, rfl, rfl⟩
        have rCond : Runs w p ω'
            (.cond (.bin .eq (.reg 6) (.const 0))
              (.assign 3 (.bin .add (.reg 3) (.const 4)))
              (.assign 7 (.load (.bin .add (.reg 3) (.const 1))) ;;
               .store (.bin .add (.reg 1) (.reg 4)) (.reg 7) ;;
               .assign 4 (.bin .add (.reg 4) (.const 1)) ;;
               .assign 3 (.bin .add (.reg 3) (.const 2))))
            t1 .normal t2 (3 + 4 + 1) :=
          runs_cond_iff.mpr ⟨1, _, by simp [Expr.eval, BinOp.eval, t1, hw1, Nat.two_pow_pos w],
            by simpa using rt2, rfl⟩
        have rstep : Runs w p ω' _ s .normal t2 _ :=
          runs_seq_iff.mpr (Or.inr ⟨t1, 3, _, rt1, rCond, rfl⟩)
        have hNewPref : batchDeletedEdges (U.take (i + 1)) = batchDeletedEdges (U.take i) := by
          rw [hTakeSucc, batchDeletedEdges_append, hu]; simp [batchDeletedEdges]
        refine ⟨.normal, t2, _, rstep, ⟨⟨ptr + 4, remW - 4,
          by simp [t2, t1, h0], by simp [t2, t1, h1], by simp [t2, t1, h2], by simp [t2],
          by rw [hNewPref]; simp [t2, t1, h4], by simp, by omega, by omega,
          by rw [hGStep]; exact hRest, by rw [hNewPref]; exact hList,
          by rw [hNewPref]; exact hZ, hFr⟩, by simp [t2, t1, h5]⟩, by dsimp only; omega⟩
      | split v v' St Sh =>
        rw [hu] at hEdge
        exact hEdge.elim)
  obtain ⟨o, s4, cLoop, rLoop, hInv4, hcLoop⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hInv4
  | normal =>
    rcases hInv4 with ⟨_, _, _, _, _, _, h4, _, _, _, _, hList4, hZ4, hFr4⟩
    have hTakeAll : U.take U.length = U := List.take_of_length_le le_rfl
    rw [hTakeAll] at h4 hList4 hZ4
    have rRet : Runs w p ω (.ret (.reg 4)) s4 (.returned (batchDeletedEdges U).length) s4 2 :=
      runs_ret_iff.mpr ⟨(batchDeletedEdges U).length, by simp [Expr.eval, h4], rfl, rfl, rfl⟩
    have rAll : Runs w p ω wireCollectDeletedEdgesBody s0
        (.returned (batchDeletedEdges U).length) s4
        (3 + (4 + (2 + (cLoop + 2 + 1) + 1) + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨s1, 3, _, r1,
        runs_seq_iff.mpr (Or.inr ⟨s2, 4, _, r2,
          runs_seq_iff.mpr (Or.inr ⟨s3, 2, _, r3,
            runs_seq_iff.mpr (Or.inr ⟨s4, cLoop, 2, rLoop, rRet, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    have hrc : rangeCost (fun _ => 38) 0 U.length = U.length * 38 := by simp [rangeCost]
    simp only [Expr.size, hrc] at hcLoop
    exact ⟨s4, _, rAll, by omega, hList4, hZ4, hFr4⟩

end MinCostFlow.MinRatio
