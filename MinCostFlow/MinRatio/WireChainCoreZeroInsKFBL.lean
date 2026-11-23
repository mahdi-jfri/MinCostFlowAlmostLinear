module

public import MinCostFlow.MinRatio.WireChainCoreTreeCutsKFBL
public import MinCostFlow.MinRatio.WireChainCoreOp0KFBL
import WordRAM.Memory
import WordRAM.Tactic

/-!
# The slots of the inserted names are set to `0` (`WireChainCoreZeroInsKFBL`)

The path tree keeps a slot for each internal name: the slot is not `0` exactly when the name is on
the tree. The solver rep says this only for the live names. A name that a batch inserts is fresh,
so its slot word may hold anything. Branch B of the chain-update core must make these slots `0`
before it treats the new names as off-tree edges. Branch A sets all slots to `0`, but that costs
the table size, which Branch B cannot pay.

`wireZeroInsertSlotsBody` reads an edge-only batch and writes `0` at `slots + e` for each inserted
name `e`. `wireZeroInsertSlotsBody_runs` gives its run: those words are `0`, every other word is
kept, and the cost is at most `50` per update plus `35`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain DynSpanner.Program

/-- Procedure `[batchPtr, slots]` (`regs 0..1`): scans an edge-only batch at `batchPtr` and writes
`0` at `slots + e` for the edge `e` of each insertion. An insertion (tag `0`) takes four words and
a deletion two; the procedure treats any other tag as a deletion, so it is meant for batches
without splits. It returns `0`. -/
@[expose] def wireZeroInsertSlotsBody : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.bin .add (.reg 0) (.const 1)) ;;
  forRange 5 (.const 0) (.reg 2)
    (.assign 6 (.load (.reg 3)) ;;
     .cond (.bin .eq (.reg 6) (.const 0))
       (.assign 7 (.load (.bin .add (.reg 3) (.const 1))) ;;
        .store (.bin .add (.reg 1) (.reg 7)) (.const 0) ;;
        .assign 3 (.bin .add (.reg 3) (.const 4)))
       (.assign 3 (.bin .add (.reg 3) (.const 2)))) ;;
  .ret (.const 0)

theorem wireZeroInsertSlotsBody_noRand : wireZeroInsertSlotsBody.NoRand := by
  simp [wireZeroInsertSlotsBody, forRange, forUp, Stmt.NoRand]

/-- The inserted names of a prefix of the batch are inserted names of the batch. -/
theorem mem_batchInsertedEdges_of_take {U : List Update} {i e : ℕ}
    (he : e ∈ batchInsertedEdges (U.take i)) : e ∈ batchInsertedEdges U := by
  rw [← List.take_append_drop i U, batchInsertedEdges_append]
  exact List.mem_append_left _ he

set_option maxHeartbeats 800000 in
/-- The run of `wireZeroInsertSlotsBody` on an edge-only batch: the slot word of each inserted
name becomes `0`, every other word is kept, and the cost is at most `50 |U| + 35`. The slot words
of the inserted names must lie below the batch, so that the writes do not touch it. -/
theorem wireZeroInsertSlotsBody_runs
    {w batchPtr slots totalWords pos : ℕ} {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    {G : MGraph} {U : List Update}
    (hSmall : SmallBatchAt mem batchPtr G U totalWords)
    (hEdgeOnly : ∀ u ∈ U, Bundle.IsEdgeUpdate u)
    (hBatchW : ∀ j < totalWords, mem (batchPtr + j) < 2 ^ w)
    (hSlotLt : ∀ e ∈ batchInsertedEdges U, slots + e < batchPtr)
    (hRoom : batchPtr + totalWords < 2 ^ w)
    (hw5 : 5 < 2 ^ w) :
    ∃ out cost,
      Runs w p ω wireZeroInsertSlotsBody (startState [batchPtr, slots] mem pos)
        (.returned 0) out cost ∧
      cost ≤ 50 * U.length + 35 ∧
      (∀ e ∈ batchInsertedEdges U, out.mem (slots + e) = 0) ∧
      (∀ a, (∀ e ∈ batchInsertedEdges U, a ≠ slots + e) → out.mem a = mem a) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  obtain ⟨⟨hTotPos, hLen0, hBody0⟩, _⟩ := hSmall
  have hULenW : U.length < 2 ^ w := by simpa [hLen0] using hBatchW 0 (by omega)
  let s0 := startState [batchPtr, slots] mem pos
  let s1 := { s0 with regs := Function.update s0.regs 2 U.length }
  let s2 := { s1 with regs := Function.update s1.regs 3 (batchPtr + 1) }
  have r1 : Runs w p ω (.assign 2 (.load (.reg 0))) s0 .normal s1 3 :=
    runs_assign_iff.mpr ⟨U.length, by simp [Expr.eval, s0, startState, hLen0], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 3 (.bin .add (.reg 0) (.const 1))) s1 .normal s2 4 :=
    runs_assign_iff.mpr ⟨batchPtr + 1, by
      simp [Expr.eval, BinOp.eval, s1, s0, startState, hw1, show batchPtr + 1 < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  let Inv (i : ℕ) (s : State) : Prop :=
    ∃ ptr remW,
      let pref := batchInsertedEdges (U.take i)
      s.regs 0 = batchPtr ∧ s.regs 1 = slots ∧ s.regs 2 = U.length ∧
      s.regs 3 = ptr ∧ s.regs 5 = i ∧
      batchPtr + 1 ≤ ptr ∧ ptr + remW = batchPtr + totalWords ∧
      BatchBodyAt mem ptr (G.applyBatch (U.take i)) (U.drop i) remW ∧
      (∀ e ∈ pref, s.mem (slots + e) = 0) ∧
      (∀ a, (∀ e ∈ pref, a ≠ slots + e) → s.mem a = mem a)
  have hloop := Triple.forRange_le (w := w) (p := p) (r := 5) (lo := .const 0) (hi := .reg 2)
    (P := fun s => s = s2) (Inv := Inv) (fun _ => 30) 0 U.length (Nat.zero_le _) hw1
    (fun _ => hULenW)
    (fun s hs => by
      subst hs
      refine ⟨by simp [Expr.eval, Nat.two_pow_pos w],
        batchPtr + 1, totalWords - 1,
        by simp [s2, s1, s0, startState], by simp [s2, s1, s0, startState],
        by simp [s2, s1], by simp [s2], by simp,
        le_rfl, by omega, by simpa [MGraph.applyBatch] using hBody0,
        fun _ h => by simp [batchInsertedEdges] at h, fun _ _ => rfl⟩)
    (fun _ _ _ _ h => by rcases h with ⟨_, _, _, _, _, _, h5, _⟩; exact h5)
    (fun _ s _ _ h => by rcases h with ⟨_, _, _, _, h2, _⟩; simp [Expr.eval, h2])
    (fun i _ hi s ω' ⟨ptr, remW, h0, h1, h2, h3, h5, hPtrLo, hPtrEnd, hBody, hZero,
        hFr⟩ => by
      have hDrop : U.drop i = U[i] :: U.drop (i + 1) := List.drop_eq_getElem_cons hi
      rw [hDrop] at hBody
      obtain ⟨uLen, hULenLe, hUAt, hRest⟩ := hBody
      have hTakeSucc : U.take (i + 1) = U.take i ++ [U[i]] :=
        List.take_succ_eq_append_getElem hi
      have hGStep : G.applyBatch (U.take (i + 1)) =
          (G.applyBatch (U.take i)).applyUpdate U[i] := by
        unfold MGraph.applyBatch
        rw [hTakeSucc, List.foldl_append]
        rfl
      have hBatchKeep (a : ℕ) (ha : batchPtr ≤ a) : s.mem a = mem a :=
        hFr a (fun e he hEq => by
          have := hSlotLt e (mem_batchInsertedEdges_of_take he); omega)
      have hEdge := hEdgeOnly U[i] (List.getElem_mem hi)
      cases hu : U[i] with
      | delete e =>
        rw [hu] at hUAt
        obtain ⟨rfl, hLA⟩ := hUAt
        have hTag : mem ptr = 1 := by simpa using hLA 0 (by simp)
        have hm0 : s.mem ptr = 1 := (hBatchKeep ptr (by omega)).trans hTag
        let t1 := { s with regs := Function.update s.regs 6 1 }
        let t2 := { t1 with regs := Function.update t1.regs 3 (ptr + 2) }
        have rt1 : Runs w p ω' (.assign 6 (.load (.reg 3))) s .normal t1 3 :=
          runs_assign_iff.mpr ⟨1, by simp [Expr.eval, h3, hm0], rfl, rfl, rfl⟩
        have rt2 : Runs w p ω' (.assign 3 (.bin .add (.reg 3) (.const 2))) t1 .normal t2 4 :=
          runs_assign_iff.mpr ⟨ptr + 2, by
            simp [Expr.eval, BinOp.eval, t1, h3, show 2 < 2 ^ w by omega,
              show ptr + 2 < 2 ^ w by omega], rfl, rfl, rfl⟩
        have rCond : Runs w p ω'
            (.cond (.bin .eq (.reg 6) (.const 0))
              (.assign 7 (.load (.bin .add (.reg 3) (.const 1))) ;;
               .store (.bin .add (.reg 1) (.reg 7)) (.const 0) ;;
               .assign 3 (.bin .add (.reg 3) (.const 4)))
              (.assign 3 (.bin .add (.reg 3) (.const 2))))
            t1 .normal t2 (3 + 4 + 1) :=
          runs_cond_iff.mpr ⟨0, _, by simp [Expr.eval, BinOp.eval, t1, Nat.two_pow_pos w],
            by simpa only [↓reduceIte] using rt2, rfl⟩
        have rstep : Runs w p ω' _ s .normal t2 _ :=
          runs_seq_iff.mpr (Or.inr ⟨t1, 3, _, rt1, rCond, rfl⟩)
        have hNewPref : batchInsertedEdges (U.take (i + 1)) = batchInsertedEdges (U.take i) := by
          rw [hTakeSucc, batchInsertedEdges_append, hu]; simp [batchInsertedEdges]
        refine ⟨.normal, t2, _, rstep, ⟨⟨ptr + 2, remW - 2,
          by simp [t2, t1, h0], by simp [t2, t1, h1], by simp [t2, t1, h2], by simp [t2],
          by simp, by omega, by omega,
          by rw [hGStep]; exact hRest, by rw [hNewPref]; exact hZero,
          by rw [hNewPref]; exact hFr⟩, by simp [t2, t1, h5]⟩, by dsimp only; omega⟩
      | insert e u v =>
        rw [hu] at hUAt
        obtain ⟨rfl, hLA⟩ := hUAt
        have hTag : mem ptr = 0 := by simpa using hLA 0 (by simp)
        have hE : mem (ptr + 1) = e := by simpa using hLA 1 (by simp)
        have hm0 : s.mem ptr = 0 := (hBatchKeep ptr (by omega)).trans hTag
        have hm1 : s.mem (ptr + 1) = e := (hBatchKeep (ptr + 1) (by omega)).trans hE
        have hEIns : e ∈ batchInsertedEdges U := by
          rw [mem_batchInsertedEdges_iff]
          exact ⟨U[i], List.getElem_mem hi, by rw [hu]; rfl⟩
        have hSlotE := hSlotLt e hEIns
        let t1 := { s with regs := Function.update s.regs 6 0 }
        let t2 := { t1 with regs := Function.update t1.regs 7 e }
        let t3 := { t2 with mem := Function.update t2.mem (slots + e) 0 }
        let t4 := { t3 with regs := Function.update t3.regs 3 (ptr + 4) }
        have rt1 : Runs w p ω' (.assign 6 (.load (.reg 3))) s .normal t1 3 :=
          runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h3, hm0], rfl, rfl, rfl⟩
        have rt2 : Runs w p ω' (.assign 7 (.load (.bin .add (.reg 3) (.const 1)))) t1 .normal
            t2 5 :=
          runs_assign_iff.mpr ⟨e, by
            simp [Expr.eval, BinOp.eval, t1, h3, hw1, show ptr + 1 < 2 ^ w by omega, hm1],
            rfl, rfl, rfl⟩
        have rt3 : Runs w p ω' (.store (.bin .add (.reg 1) (.reg 7)) (.const 0)) t2 .normal
            t3 5 :=
          runs_store_iff.mpr ⟨slots + e, 0, by
            simp [Expr.eval, BinOp.eval, t2, t1, h1, show slots + e < 2 ^ w by omega],
            by simp [Expr.eval, Nat.two_pow_pos w], rfl, rfl, rfl⟩
        have rt4 : Runs w p ω' (.assign 3 (.bin .add (.reg 3) (.const 4))) t3 .normal t4 4 :=
          runs_assign_iff.mpr ⟨ptr + 4, by
            simp [Expr.eval, BinOp.eval, t3, t2, t1, h3, hw4, show ptr + 4 < 2 ^ w by omega],
            rfl, rfl, rfl⟩
        have rCond : Runs w p ω'
            (.cond (.bin .eq (.reg 6) (.const 0))
              (.assign 7 (.load (.bin .add (.reg 3) (.const 1))) ;;
               .store (.bin .add (.reg 1) (.reg 7)) (.const 0) ;;
               .assign 3 (.bin .add (.reg 3) (.const 4)))
              (.assign 3 (.bin .add (.reg 3) (.const 2))))
            t1 .normal t4 (3 + (5 + (5 + 4 + 1) + 1) + 1) :=
          runs_cond_iff.mpr ⟨1, _, by simp [Expr.eval, BinOp.eval, t1, hw1, Nat.two_pow_pos w],
            by simpa using
              runs_seq_iff.mpr (Or.inr ⟨t2, 5, _, rt2,
                runs_seq_iff.mpr (Or.inr ⟨t3, 5, 4, rt3, rt4, rfl⟩), rfl⟩), rfl⟩
        have rstep : Runs w p ω' _ s .normal t4 _ :=
          runs_seq_iff.mpr (Or.inr ⟨t1, 3, _, rt1, rCond, rfl⟩)
        have hNewPref : batchInsertedEdges (U.take (i + 1)) =
            batchInsertedEdges (U.take i) ++ [e] := by
          rw [hTakeSucc, batchInsertedEdges_append, hu]; rfl
        refine ⟨.normal, t4, _, rstep, ⟨⟨ptr + 4, remW - 4,
          by simp [t4, t3, t2, t1, h0], by simp [t4, t3, t2, t1, h1],
          by simp [t4, t3, t2, t1, h2], by simp [t4], by simp, by omega, by omega,
          by rw [hGStep]; exact hRest, ?_, ?_⟩, by simp [t4, t3, t2, t1, h5]⟩,
          by dsimp only; omega⟩
        · rw [hNewPref]
          intro e' he'
          change Function.update s.mem (slots + e) 0 (slots + e') = 0
          by_cases hee : slots + e' = slots + e
          · rw [hee]; simp
          · rw [Function.update_of_ne hee]
            rcases List.mem_append.mp he' with h | h
            · exact hZero e' h
            · simp only [List.mem_singleton] at h; subst h; exact absurd rfl hee
        · rw [hNewPref]
          intro a ha
          change Function.update s.mem (slots + e) 0 a = mem a
          rw [Function.update_of_ne (ha e (by simp))]
          exact hFr a (fun e' he' => ha e' (List.mem_append_left _ he'))
      | split v v' St Sh =>
        rw [hu] at hEdge
        exact hEdge.elim)
  obtain ⟨o, s4, cLoop, rLoop, hInv4, hcLoop⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hInv4
  | normal =>
    rcases hInv4 with ⟨_, _, _, _, _, _, _, _, _, _, hZ4, hFr4⟩
    have hTakeAll : U.take U.length = U := List.take_of_length_le le_rfl
    rw [hTakeAll] at hZ4 hFr4
    have rRet : Runs w p ω (.ret (.const 0)) s4 (.returned 0) s4 2 :=
      runs_ret_iff.mpr ⟨0, by simp [Expr.eval, Nat.two_pow_pos w], rfl, rfl, rfl⟩
    have rAll : Runs w p ω wireZeroInsertSlotsBody s0 (.returned 0) s4
        (3 + (4 + (cLoop + 2 + 1) + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨s1, 3, _, r1,
        runs_seq_iff.mpr (Or.inr ⟨s2, 4, _, r2,
          runs_seq_iff.mpr (Or.inr ⟨s4, cLoop, 2, rLoop, rRet, rfl⟩), rfl⟩), rfl⟩)
    have hrc : rangeCost (fun _ => 30) 0 U.length = U.length * 30 := by simp [rangeCost]
    simp only [Expr.size, hrc] at hcLoop
    exact ⟨s4, _, rAll, by omega, hZ4, hFr4⟩

end MinCostFlow.MinRatio
