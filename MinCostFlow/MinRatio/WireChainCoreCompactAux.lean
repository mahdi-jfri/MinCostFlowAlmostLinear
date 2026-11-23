module

public import MinCostFlow.MinRatio.WireRename
public import MinCostFlow.MinRatio.WireChainSpecs
public import MinCostFlow.DynSpanner.Program.DynGraphInit
public import MinCostFlow.Num.IsNegative
public import WordRAM.CopyWords
import WordRAM.Tactic

/-!
# Level-0 graph, length, and account compaction (`WireChainCoreCompact`)

After a level-0 rebuild renames live edges `e ∈ G.E` to `0 .. G.m - 1` via `level0RenameBody`
(leaving `compactUnrank G.E j` at `unrankPtr + j`), `wireCompactLevel0Body` compacts:
1. `edgeThresholds[0..G.m)` and `edgeRecords[0..G.m)` in place (`j ≤ compactUnrank G.E j`),
2. `newLen0` (`eCap * L` words) copied from `oldLen0 + unrank[j] * L`,
3. two fresh `DynGraphAt` copies of `G.compact` (`newRootGraph` at `root + 14` and
   `newLvlGraph0` at `levelMeta + d`), plus `levelMeta + 0 := newLen0`,
4. `inOffReady[0..intCap)` cleared and `offReadyList` rebuilt from `edgeRecords[0..G.m)`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Chain MinCostFlow.Chain.Ordered MinCostFlow.DynSpanner.Program

/-- Heap words allocated by `wireCompactLevel0Body`. -/
@[expose] def wireCompactLevel0Space (n eCap L mNew : ℕ) : ℕ :=
  eCap * L + 3 * mNew + 2 * dynGraphSize n eCap

/-- Step bound for `wireCompactLevel0Body`. -/
@[expose] def wireCompactLevel0Cost (n _eCap intCap L mNew : ℕ) : ℕ :=
  mNew * (17 * L + 1300) + 300 * n + 20 * intCap + 600

/-- Pass 1: compact `edgeThresholds` and `edgeRecords` in place using `unrankPtr`. -/
@[expose] def wireCompactTablesLoop : Stmt :=
  forRange 20 (.const 0) (.reg 3)
    (.assign 21 (.load (.bin .add (.reg 2) (.reg 20))) ;;
     .store (.bin .add (.reg 9) (.reg 20)) (.load (.bin .add (.reg 9) (.reg 21))) ;;
     .store (.bin .add (.reg 10) (.reg 20)) (.load (.bin .add (.reg 10) (.reg 21))))

/-- Pass 2: copy compacted level-0 edge lengths into `newLen0` (`reg 22 = heap`). -/
@[expose] def wireCompactLensLoop (copyWords : ℕ) : Stmt :=
  forRange 20 (.const 0) (.reg 3)
    (.assign 21 (.load (.bin .add (.reg 2) (.reg 20))) ;;
     .call 23 copyWords
       [.bin .add (.reg 1) (.bin .mul (.reg 21) (.reg 8)),
        .bin .add (.reg 22) (.bin .mul (.reg 20) (.reg 8)),
        .reg 8])

/-- Pass 3: build edge triples for `G.compact` and initialize `newRootGraph` & `newLvlGraph0`. -/
@[expose] def wireCompactGraphsStmt (dgInit : ℕ) : Stmt :=
  .assign 24 (.bin .add (.reg 22) (.bin .mul (.reg 16) (.reg 8))) ;;
  .assign 25 (.bin .add (.bin .add (.reg 13) (.const 4)) (.reg 15)) ;;
  .assign 26 (.load (.bin .add (.reg 13) (.const 2))) ;;
  forRange 20 (.const 0) (.reg 3)
    (.assign 21 (.load (.bin .add (.reg 2) (.reg 20))) ;;
     .store (.bin .add (.reg 24) (.bin .mul (.const 3) (.reg 20))) (.reg 20) ;;
     .store (.bin .add (.bin .add (.reg 24) (.bin .mul (.const 3) (.reg 20))) (.const 1))
       (.load (.bin .add (.reg 17) (.load (.bin .add (.reg 18) (.reg 21))))) ;;
     .store (.bin .add (.bin .add (.reg 24) (.bin .mul (.const 3) (.reg 20))) (.const 2))
       (.load (.bin .add (.reg 17) (.load (.bin .add (.reg 19) (.reg 21)))))) ;;
  .assign 27 (.bin .add (.reg 24) (.bin .mul (.const 3) (.reg 3))) ;;
  .call 23 dgInit [.reg 27, .reg 15, .reg 16, .reg 26, .reg 25, .reg 3, .reg 24] ;;
  .assign 28 (.bin .add (.bin .add (.const 4) (.bin .mul (.const 7) (.reg 15)))
    (.bin .mul (.const 9) (.reg 16))) ;;
  .assign 29 (.bin .add (.reg 27) (.reg 28)) ;;
  .call 23 dgInit [.reg 29, .reg 15, .reg 16, .reg 26, .reg 25, .reg 3, .reg 24] ;;
  .assign 30 (.bin .add (.reg 29) (.reg 28)) ;;
  .store (.bin .add (.reg 0) (.const 14)) (.reg 27) ;;
  .store (.reg 32) (.reg 22) ;;
  .store (.bin .add (.reg 32) (.reg 7)) (.reg 29)

/-- Pass 4: zero `inOffReady[0..intCap)` and reset `offReadyCount` at `root + 11` to `0` so
`wireTreeSyncLoop` can link `newF` before `wireRebuildOffReadyBody` populates off-tree ready edges. -/
@[expose] def wireCompactZeroOffReadyStmt : Stmt :=
  forRange 20 (.const 0) (.reg 14)
    (.store (.bin .add (.reg 12) (.reg 20)) (.const 0)) ;;
  .store (.bin .add (.reg 0) (.const 11)) (.const 0)

/-- Procedure `[root, oldLen0, unrankPtr, mNew, heap]` (`regs 0..4`): compacts all level-0
tables, lengths, and dynamic graphs and resets `inOffReady`/`offReadyCount` to `0`, returning `nextHeap`. -/
@[expose] def wireCompactLevel0Body (copyWords dgInit : ℕ) : Stmt :=
  .assign 5 (.load (.reg 0)) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 7 (.load (.bin .add (.reg 5) (.const 11))) ;;
  .assign 8 (.load (.bin .add (.reg 5) (.const 5))) ;;
  .assign 9 (.load (.bin .add (.reg 0) (.const 9))) ;;
  .assign 10 (.load (.bin .add (.reg 0) (.const 10))) ;;
  .assign 11 (.load (.bin .add (.reg 0) (.const 12))) ;;
  .assign 12 (.load (.bin .add (.reg 0) (.const 13))) ;;
  .assign 13 (.load (.bin .add (.reg 0) (.const 14))) ;;
  .assign 14 (.load (.bin .add (.reg 0) (.const 15))) ;;
  .assign 15 (.load (.reg 13)) ;;
  .assign 16 (.load (.bin .add (.reg 13) (.const 1))) ;;
  .assign 17 (.bin .add (.bin .add (.reg 13) (.const 4)) (.bin .mul (.const 4) (.reg 15))) ;;
  .assign 18 (.bin .add (.bin .add (.bin .add (.reg 13) (.const 4)) (.bin .mul (.const 7) (.reg 15)))
    (.bin .mul (.const 3) (.reg 16))) ;;
  .assign 19 (.bin .add (.reg 18) (.reg 16)) ;;
  .assign 32 (.bin .add (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 7))) (.const 2)) ;;
  .assign 22 (.reg 4) ;;
  wireCompactTablesLoop ;;
  wireCompactLensLoop copyWords ;;
  wireCompactGraphsStmt dgInit ;;
  wireCompactZeroOffReadyStmt ;;
  .ret (.reg 30)

theorem wireCompactLevel0Body_noRand (copyWords dgInit : ℕ) :
    (wireCompactLevel0Body copyWords dgInit).NoRand := by
  simp [wireCompactLevel0Body, wireCompactTablesLoop, wireCompactLensLoop,
    wireCompactGraphsStmt, wireCompactZeroOffReadyStmt, forRange, forUp, Stmt.NoRand]

/-- Helper: `j ≤ compactUnrank E j` for every `j`. -/
theorem le_compactUnrank_aux (E : Finset ℕ) (j : ℕ) : j ≤ compactUnrank E j := by
  by_cases h : j < E.card
  · have hle : compactRank E (compactUnrank E j) ≤ compactUnrank E j := by
      unfold compactRank
      calc (E.filter (· < compactUnrank E j)).card
          ≤ (Finset.range (compactUnrank E j)).card :=
            Finset.card_le_card (fun x hx => Finset.mem_range.mpr (Finset.mem_filter.mp hx).2)
        _ = compactUnrank E j := Finset.card_range _
    rwa [compactRank_unrank h] at hle
  · simp [compactUnrank, h]

/-- Addresses below `heap` modified by `wireCompactLevel0Body`. -/
@[expose] def InCompactMutable (root table d edgeThresholds edgeRecords offReadyList inOffReady intCap a : ℕ) : Prop :=
  let levelMeta := solverLevelMetaAddr table d
  a = root + 11 ∨ a = root + 14 ∨ a = levelMeta ∨ a = levelMeta + d ∨
  (edgeThresholds ≤ a ∧ a < edgeThresholds + intCap) ∨
  (edgeRecords ≤ a ∧ a < edgeRecords + intCap) ∨
  (offReadyList ≤ a ∧ a < offReadyList + intCap) ∨
  (inOffReady ≤ a ∧ a < inOffReady + intCap)

/-- Execute Pass 1 (`wireCompactTablesLoop`): compacts `edgeThresholds` and `edgeRecords` in place. -/
theorem wireCompactTablesLoop_runs
    {w unrankPtr edgeThresholds edgeRecords intCap : ℕ} {G : MGraph} {p : Program}
    {ω : ℕ → Bool} {st : State}
    (hr2 : st.regs 2 = unrankPtr) (hr3 : st.regs 3 = G.m)
    (hr9 : st.regs 9 = edgeThresholds) (hr10 : st.regs 10 = edgeRecords)
    (hUnr : ∀ j < G.m, st.mem (unrankPtr + j) = compactUnrank G.E j)
    (hCap : ∀ e ∈ G.E, e < intCap)
    (hDisj1 : edgeThresholds + intCap ≤ edgeRecords ∨ edgeRecords + intCap ≤ edgeThresholds)
    (hDisjU1 : unrankPtr + G.m ≤ edgeThresholds ∨ edgeThresholds + intCap ≤ unrankPtr)
    (hDisjU2 : unrankPtr + G.m ≤ edgeRecords ∨ edgeRecords + intCap ≤ unrankPtr)
    (hW1 : unrankPtr + G.m < 2 ^ w) (hW2 : edgeThresholds + intCap < 2 ^ w)
    (hW3 : edgeRecords + intCap < 2 ^ w) (hw1 : 1 < 2 ^ w) :
    ∃ out cost,
      Runs w p ω wireCompactTablesLoop st .normal out cost ∧
      cost ≤ 40 * G.m + 20 ∧
      (∀ r, r ≠ 20 → r ≠ 21 → out.regs r = st.regs r) ∧
      (∀ j < G.m, out.mem (edgeThresholds + j) = st.mem (edgeThresholds + compactUnrank G.E j) ∧
        out.mem (edgeRecords + j) = st.mem (edgeRecords + compactUnrank G.E j)) ∧
      (∀ a, (a < edgeThresholds ∨ edgeThresholds + G.m ≤ a) →
        (a < edgeRecords ∨ edgeRecords + G.m ≤ a) → out.mem a = st.mem a) := by
  have hmLe : G.m ≤ intCap := by
    have : G.E.card ≤ (Finset.range intCap).card :=
      Finset.card_le_card (fun e he => Finset.mem_range.mpr (hCap e he))
    simpa [MGraph.m] using this
  let Inv (j : ℕ) (s : State) : Prop :=
    j ≤ G.m ∧ s.regs 20 = j ∧
    (∀ r, r ≠ 20 → r ≠ 21 → s.regs r = st.regs r) ∧
    (∀ k < j, s.mem (edgeThresholds + k) = st.mem (edgeThresholds + compactUnrank G.E k) ∧
      s.mem (edgeRecords + k) = st.mem (edgeRecords + compactUnrank G.E k)) ∧
    (∀ a, (a < edgeThresholds ∨ edgeThresholds + j ≤ a) →
      (a < edgeRecords ∨ edgeRecords + j ≤ a) → s.mem a = st.mem a)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 20) (lo := .const 0) (hi := .reg 3)
    (P := fun s => s = st) (Inv := Inv) 30 0 G.m (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun s hs => by
      subst hs
      refine ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], Nat.zero_le _, by simp,
        fun r h20 _ => by simp [Function.update_of_ne h20], fun _ hk => by omega, fun _ _ _ => rfl⟩)
    (fun _ _ _ _ h => h.2.1)
    (fun _ s _ _ h => by simp [Expr.eval, (h.2.2.1 3 (by decide) (by decide)).trans hr3])
    (fun j _ hj s ω' ⟨_, hjr, hregs, hdone, hfr⟩ => by
      have h2 := (hregs 2 (by decide) (by decide)).trans hr2
      have h9 := (hregs 9 (by decide) (by decide)).trans hr9
      have h10 := (hregs 10 (by decide) (by decide)).trans hr10
      let u := compactUnrank G.E j
      have huMem : u ∈ G.E := compactUnrank_mem hj
      have huCap : u < intCap := hCap u huMem
      have hju : j ≤ u := le_compactUnrank_aux G.E j
      have huAt : s.mem (unrankPtr + j) = u :=
        (hfr _ (by rcases hDisjU1 with h | h <;> omega) (by rcases hDisjU2 with h | h <;> omega)).trans (hUnr j hj)
      have hetAt : s.mem (edgeThresholds + u) = st.mem (edgeThresholds + u) :=
        hfr _ (Or.inr (by omega)) (by rcases hDisj1 with h | h <;> omega)
      have herAt : s.mem (edgeRecords + u) = st.mem (edgeRecords + u) :=
        hfr _ (by rcases hDisj1 with h | h <;> omega) (Or.inr (by omega))
      let t1 := { s with regs := Function.update s.regs 21 u }
      let t2 := { t1 with mem := Function.update t1.mem (edgeThresholds + j) (st.mem (edgeThresholds + u)) }
      let t3 := { t2 with mem := Function.update t2.mem (edgeRecords + j) (st.mem (edgeRecords + u)) }
      have rt1 : Runs w p ω' (.assign 21 (.load (.bin .add (.reg 2) (.reg 20)))) s .normal t1 5 :=
        runs_assign_iff.mpr ⟨u, by simp [Expr.eval, BinOp.eval, h2, hjr, show unrankPtr + j < 2 ^ w by omega, huAt],
          rfl, rfl, rfl⟩
      have rt2 : Runs w p ω' (.store (.bin .add (.reg 9) (.reg 20)) (.load (.bin .add (.reg 9) (.reg 21))))
          t1 .normal t2 8 :=
        runs_store_iff.mpr ⟨edgeThresholds + j, st.mem (edgeThresholds + u),
          by simp [Expr.eval, BinOp.eval, t1, h9, hjr, show edgeThresholds + j < 2 ^ w by omega],
          by simp [Expr.eval, BinOp.eval, t1, h9, show edgeThresholds + u < 2 ^ w by omega, hetAt],
          rfl, rfl, rfl⟩
      have rt3 : Runs w p ω' (.store (.bin .add (.reg 10) (.reg 20)) (.load (.bin .add (.reg 10) (.reg 21))))
          t2 .normal t3 8 :=
        runs_store_iff.mpr ⟨edgeRecords + j, st.mem (edgeRecords + u),
          by simp [Expr.eval, BinOp.eval, t2, t1, h10, hjr, show edgeRecords + j < 2 ^ w by omega],
          by simp [Expr.eval, BinOp.eval, t2, t1, h10, show edgeRecords + u < 2 ^ w by omega,
            Function.update_of_ne (by rcases hDisj1 with h | h <;> omega : edgeRecords + u ≠ edgeThresholds + j), herAt],
          rfl, rfl, rfl⟩
      refine ⟨.normal, t3, 5 + (8 + 8 + 1) + 1,
        runs_seq_iff.mpr (Or.inr ⟨t1, 5, _, rt1, runs_seq_iff.mpr (Or.inr ⟨t2, 8, 8, rt2, rt3, rfl⟩), rfl⟩),
        ⟨⟨by omega, by simp, fun r h20 h21 => by simp [t3, t2, t1, Function.update_of_ne h20,
          Function.update_of_ne h21, hregs r h20 h21],
          fun k hk => by
            by_cases hkj : k = j
            · subst hkj
              exact ⟨by simp [t3, t2, Function.update_of_ne (by rcases hDisj1 with h | h <;> omega :
                edgeThresholds + k ≠ edgeRecords + k), u], by simp [t3, u]⟩
            · refine ⟨?_, ?_⟩
              · simp only [t3, t2, t1,
                  Function.update_of_ne (by rcases hDisj1 with h | h <;> omega : edgeThresholds + k ≠ edgeRecords + j),
                  Function.update_of_ne (by omega : edgeThresholds + k ≠ edgeThresholds + j)]
                exact (hdone k (by omega)).1
              · simp only [t3, t2, t1, Function.update_of_ne (by omega : edgeRecords + k ≠ edgeRecords + j),
                  Function.update_of_ne (by rcases hDisj1 with h | h <;> omega : edgeRecords + k ≠ edgeThresholds + j)]
                exact (hdone k (by omega)).2,
          fun a ha1 ha2 => by
            simp only [t3, t2, t1, Function.update_of_ne (by rcases ha2 with h | h <;> omega : a ≠ edgeRecords + j),
              Function.update_of_ne (by rcases ha1 with h | h <;> omega : a ≠ edgeThresholds + j)]
            exact hfr a (by rcases ha1 with h | h <;> omega) (by rcases ha2 with h | h <;> omega)⟩,
          by simp [t3, t2, t1, hjr]⟩, by dsimp only; omega⟩)
  obtain ⟨o, out, c, r, hOut, hc⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hOut
  | normal =>
    obtain ⟨_, _, hregs, hdone, hfr⟩ := hOut
    simp only [Expr.size] at hc
    exact ⟨out, c, r, by omega, hregs, hdone, hfr⟩

/-- Execute Pass 2 (`wireCompactLensLoop`): copies compacted level-0 edge lengths to `newLen0`. -/
theorem wireCompactLensLoop_runs
    {w copyWords oldLen0 unrankPtr newLen0 L P eCap oldLenECap : ℕ} {G : MGraph} {oldℓ : ℕ → ℝ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hCopy : MeetsContract w p copyWords (copyWordsContract w))
    (hr1 : st.regs 1 = oldLen0) (hr2 : st.regs 2 = unrankPtr) (hr3 : st.regs 3 = G.m)
    (hr8 : st.regs 8 = L) (hr22 : st.regs 22 = newLen0)
    (hUnr : ∀ j < G.m, st.mem (unrankPtr + j) = compactUnrank G.E j)
    (hOldLen : EdgeValuesAt st.mem oldLen0 4 L P G.E oldℓ)
    (hCap : ∀ e ∈ G.E, e < eCap)
    (hCapOld : ∀ e ∈ G.E, e < oldLenECap)
    (hOldLe : oldLen0 + oldLenECap * L ≤ newLen0) (hUnrLe : unrankPtr + G.m ≤ newLen0)
    (hz : ZeroFrom st.mem newLen0) (hW : newLen0 + eCap * L < 2 ^ w) (hw1 : 1 < 2 ^ w) :
    ∃ out cost,
      Runs w p ω (wireCompactLensLoop copyWords) st .normal out cost ∧
      cost ≤ G.m * (17 * L + 50) + 20 ∧
      (∀ r, r ≠ 20 → r ≠ 21 → r ≠ 23 → out.regs r = st.regs r) ∧
      EdgeValuesAt out.mem newLen0 4 L P G.compact.E (fun j => oldℓ (compactUnrank G.E j)) ∧
      ZeroFrom out.mem (newLen0 + eCap * L) ∧
      ∀ a < newLen0, out.mem a = st.mem a := by
  have hmLe : G.m ≤ eCap := by
    have : G.E.card ≤ (Finset.range eCap).card :=
      Finset.card_le_card (fun e he => Finset.mem_range.mpr (hCap e he))
    simpa [MGraph.m] using this
  let Inv (j : ℕ) (s : State) : Prop :=
    j ≤ G.m ∧ s.regs 20 = j ∧
    (∀ r, r ≠ 20 → r ≠ 21 → r ≠ 23 → s.regs r = st.regs r) ∧
    (∀ k < j, Num.Valid s.mem (newLen0 + k * L) 4 L ∧
      Num.fixVal s.mem (newLen0 + k * L) 4 L P = oldℓ (compactUnrank G.E k)) ∧
    ZeroFrom s.mem (newLen0 + j * L) ∧
    ∀ a < newLen0, s.mem a = st.mem a
  let stepCost := 17 * L + 40
  have hloop := Triple.forRange_le (w := w) (p := p) (r := 20) (lo := .const 0) (hi := .reg 3)
    (P := fun s => s = st) (Inv := Inv) (fun _ => stepCost) 0 G.m (Nat.zero_le _) hw1
    (fun _ => by omega)
    (fun s hs => by
      subst hs
      refine ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], Nat.zero_le _, by simp,
        fun r h20 _ _ => by simp [Function.update_of_ne h20], fun _ hk => by omega,
        by simpa using hz, fun _ _ => rfl⟩)
    (fun _ _ _ _ h => h.2.1)
    (fun _ s _ _ h => by simp [Expr.eval, (h.2.2.1 3 (by decide) (by decide) (by decide)).trans hr3])
    (fun j _ hj s ω' ⟨_, hjr, hregs, hdone, hzS, hfr⟩ => by
      have h1 := (hregs 1 (by decide) (by decide) (by decide)).trans hr1
      have h2 := (hregs 2 (by decide) (by decide) (by decide)).trans hr2
      have h8 := (hregs 8 (by decide) (by decide) (by decide)).trans hr8
      have h22 := (hregs 22 (by decide) (by decide) (by decide)).trans hr22
      let u := compactUnrank G.E j
      have huMem : u ∈ G.E := compactUnrank_mem hj
      have huCap : u < oldLenECap := hCapOld u huMem
      have hLW : L < 2 ^ w := by
        have h1e : 1 ≤ eCap := by omega
        have : L ≤ eCap * L := by simpa using Nat.mul_le_mul_right L h1e
        omega
      have huL : u * L + L ≤ oldLenECap * L := by
        simpa [Nat.succ_mul] using Nat.mul_le_mul_right L (Nat.succ_le_of_lt huCap)
      have hjL : j * L + L ≤ eCap * L := by
        simpa [Nat.succ_mul] using Nat.mul_le_mul_right L (by omega : j + 1 ≤ eCap)
      have huAt : s.mem (unrankPtr + j) = u := (hfr _ (by omega)).trans (hUnr j hj)
      let t1 := { s with regs := Function.update s.regs 21 u }
      have rt1 : Runs w p ω' (.assign 21 (.load (.bin .add (.reg 2) (.reg 20)))) s .normal t1 5 :=
        runs_assign_iff.mpr ⟨u, by simp [Expr.eval, BinOp.eval, h2, hjr, show unrankPtr + j < 2 ^ w by omega, huAt],
          rfl, rfl, rfl⟩
      have hPre : (copyWordsContract w).pre [oldLen0 + u * L, newLen0 + j * L, L] t1.mem :=
        ⟨oldLen0 + u * L, newLen0 + j * L, L, rfl, hw1, by omega, by omega, Or.inr (by omega)⟩
      obtain ⟨t2, cC, _, rt2, hpC, _, ht2Regs, hcC⟩ :=
        runs_call_of_meetsContract (r := 23)
          (args := [.bin .add (.reg 1) (.bin .mul (.reg 21) (.reg 8)),
            .bin .add (.reg 22) (.bin .mul (.reg 20) (.reg 8)), .reg 8])
          hCopy (st := t1) (vs := [oldLen0 + u * L, newLen0 + j * L, L])
          (by simp [evalArgs, Expr.eval, BinOp.eval, t1, h1, h8, h22, hjr,
            show u * L < 2 ^ w by omega, show oldLen0 + u * L < 2 ^ w by omega,
            show j * L < 2 ^ w by omega, show newLen0 + j * L < 2 ^ w by omega])
          (by simp [show oldLen0 + u * L < 2 ^ w by omega, show newLen0 + j * L < 2 ^ w by omega, hLW])
          hPre ω'
      obtain ⟨_, _, _, hArgsC, _, hCopied, hFrC⟩ := hpC
      simp only [List.cons.injEq, and_true] at hArgsC
      obtain ⟨rfl, rfl, rfl⟩ := hArgsC
      have hStepC : cC ≤ 17 * L + 22 := by simp only [copyWordsContract, argsSize, Expr.size] at hcC; omega
      have hNewJ : Num.Valid t2.mem (newLen0 + j * L) 4 L ∧
          Num.fixVal t2.mem (newLen0 + j * L) 4 L P = oldℓ u := by
        have hag (t : ℕ) (ht : t < L) : t2.mem (newLen0 + j * L + t) = st.mem (oldLen0 + u * L + t) :=
          (hCopied t ht).trans (hfr _ (by omega))
        refine ⟨fun t ht => by rw [hag t ht]; exact (hOldLen u huMem).1 t ht, ?_⟩
        rw [← (hOldLen u huMem).2]; unfold Num.fixVal; congr 2; exact Num.intVal_congr hag
      refine ⟨.normal, t2, 5 + cC + 1, runs_seq_iff.mpr (Or.inr ⟨t1, 5, cC, rt1, rt2, rfl⟩),
        ⟨⟨by omega, by simp, fun r h20 h21 h23 => by
            simp only [Function.update_of_ne h20]
            rw [ht2Regs r h23]
            simp [t1, Function.update_of_ne h21, hregs r h20 h21 h23],
          fun k hk => by
            by_cases hkj : k = j
            · subst hkj; exact hNewJ
            · have hkL : k * L + L ≤ j * L := by
                simpa [Nat.succ_mul] using Nat.mul_le_mul_right L (by omega : k + 1 ≤ j)
              have hag (t : ℕ) (ht : t < L) : t2.mem (newLen0 + k * L + t) = s.mem (newLen0 + k * L + t) :=
                hFrC _ (Or.inl (by omega))
              refine ⟨fun t ht => by rw [hag t ht]; exact (hdone k (by omega)).1 t ht, ?_⟩
              rw [← (hdone k (by omega)).2]; unfold Num.fixVal; congr 2; exact Num.intVal_congr hag,
          fun a ha => by
            rw [Nat.succ_mul] at ha
            rw [hFrC a (Or.inr (by omega))]; exact hzS a (by omega),
          fun a ha => (hFrC a (Or.inl (by omega))).trans (hfr a ha)⟩,
          by rw [ht2Regs 20 (by decide)]; simp [t1, hjr]⟩, by dsimp [stepCost]; omega⟩)
  obtain ⟨o, out, c, r, hOut, hc⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hOut
  | normal =>
    obtain ⟨_, _, hregs, hdone, hzE, hfr⟩ := hOut
    have hrc : rangeCost (fun _ => stepCost) 0 G.m = G.m * stepCost := by simp [rangeCost]
    simp only [Expr.size, hrc] at hc
    have hm : G.m * stepCost + G.m * 9 = G.m * (17 * L + 49) := by dsimp [stepCost]; ring
    have hmLe50 : G.m * (17 * L + 49) ≤ G.m * (17 * L + 50) := Nat.mul_le_mul_left _ (by omega)
    refine ⟨out, c, r, by omega, hregs, fun j hj => hdone j (by simpa [MGraph.compact, MGraph.m] using hj),
      fun a ha => hzE a (le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right L hmLe) _) ha), hfr⟩

/-- Execute Pass 3 (`wireCompactGraphsStmt`): builds edge triples for `G.compact`, runs `dgInit`
twice to allocate `newRootGraph` and `newLvlGraph0`, and updates `root + 14`, `levelMeta`, and
`levelMeta + d`. -/
theorem wireCompactGraphsStmt_runs
    {w dgInit root unrankPtr oldRootGraph newLen0 levelMeta d n eCap L : ℕ}
    {G : MGraph} {p : Program} {ω : ℕ → Bool} {st : State}
    (hDGInit : ∀ vL eTriples, MeetsContract w p dgInit (dgInitFromListsContract w n eCap G.compact vL eTriples))
    (hr0 : st.regs 0 = root) (hr2 : st.regs 2 = unrankPtr) (hr3 : st.regs 3 = G.m)
    (hr7 : st.regs 7 = d) (hr8 : st.regs 8 = L) (hr13 : st.regs 13 = oldRootGraph)
    (hr15 : st.regs 15 = n) (hr16 : st.regs 16 = eCap)
    (hr17 : st.regs 17 = dgIntToExtBase oldRootGraph n)
    (hr18 : st.regs 18 = dgETailSlotBase oldRootGraph n eCap)
    (hr19 : st.regs 19 = dgEHeadSlotBase oldRootGraph n eCap)
    (hr22 : st.regs 22 = newLen0) (hr32 : st.regs 32 = levelMeta)
    (hDG : DynGraphAt st.mem oldRootGraph n eCap G)
    (hUnr : ∀ j < G.m, st.mem (unrankPtr + j) = compactUnrank G.E j)
    (hCap : ∀ e ∈ G.E, e < eCap)
    (hRootLe : root + 16 ≤ newLen0) (hMetaLe : levelMeta + 2 * d ≤ newLen0)
    (hRGLe : oldRootGraph + dynGraphSize n eCap ≤ newLen0)
    (hUnrLe : unrankPtr + G.m ≤ newLen0)
    (hDisjRM : root + 14 < levelMeta ∨ levelMeta + 2 * d ≤ root + 14)
    (hdPos : 0 < d) (h16 : 16 ≤ 2 ^ w)
    (hz : ZeroFrom st.mem (newLen0 + eCap * L))
    (hRoom : newLen0 + wireCompactLevel0Space n eCap L G.m < 2 ^ w) :
    let newRootGraph := newLen0 + eCap * L + 3 * G.m
    let newLvlGraph0 := newRootGraph + dynGraphSize n eCap
    let nextHeap := newLen0 + wireCompactLevel0Space n eCap L G.m
    ∃ out cost,
      Runs w p ω (wireCompactGraphsStmt dgInit) st .normal out cost ∧
      cost ≤ 1100 * G.m + 300 * n + 300 ∧
      out.regs 30 = nextHeap ∧
      (∀ r, r ≠ 20 → r ≠ 21 → r ≠ 23 → r ≠ 24 → r ≠ 25 → r ≠ 26 → r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 →
        out.regs r = st.regs r) ∧
      DynGraphAt out.mem newRootGraph n eCap G.compact ∧
      DynGraphAt out.mem newLvlGraph0 n eCap G.compact ∧
      out.mem (root + 14) = newRootGraph ∧
      out.mem levelMeta = newLen0 ∧
      out.mem (levelMeta + d) = newLvlGraph0 ∧
      ZeroFrom out.mem nextHeap ∧
      ∀ a < newLen0 + eCap * L, a ≠ root + 14 → a ≠ levelMeta → a ≠ levelMeta + d → out.mem a = st.mem a := by
  dsimp only
  set ePtr := newLen0 + eCap * L
  set vPtr := oldRootGraph + 4 + n
  set newRootGraph := ePtr + 3 * G.m
  set dgSz := dynGraphSize n eCap
  set newLvlGraph0 := newRootGraph + dgSz
  set nextHeap := newLen0 + wireCompactLevel0Space n eCap L G.m
  have hNextEq : nextHeap = newLvlGraph0 + dgSz := by
    dsimp [nextHeap, newLvlGraph0, newRootGraph, ePtr, dgSz, wireCompactLevel0Space]; omega
  have hDgDef : dgSz = 4 + 7 * n + 9 * eCap := rfl
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hw7 : 7 < 2 ^ w := by omega
  have hw9 : 9 < 2 ^ w := by omega
  have hGValid : G.compact.IsValid := by
    intro j hj
    have huMem : compactUnrank G.E j ∈ G.E := compactUnrank_mem (by simpa [MGraph.compact, MGraph.m] using hj)
    exact hDG.1 _ huMem
  obtain ⟨vL, hvLen, _, hvMem, hvAt, _⟩ := hDG.2.2.2.2.2.2.2.2.1
  have hGnm : st.mem (oldRootGraph + 2) = G.n := by simpa [dgNOff] using hDG.2.2.2.2.2.1
  have hGnLe : G.n ≤ n := by
    have : G.V.card ≤ (Finset.range n).card := Finset.card_le_card (fun v hv => Finset.mem_range.mpr (hDG.2.1 v hv))
    simpa [MGraph.n] using this
  let s1 := { st with regs := Function.update st.regs 24 ePtr }
  let s2 := { s1 with regs := Function.update s1.regs 25 vPtr }
  let s3 := { s2 with regs := Function.update s2.regs 26 G.n }
  have r1 : Runs w p ω (.assign 24 (.bin .add (.reg 22) (.bin .mul (.reg 16) (.reg 8)))) st .normal s1 6 :=
    runs_assign_iff.mpr ⟨ePtr, by simp [Expr.eval, BinOp.eval, hr22, hr16, hr8,
      show eCap * L < 2 ^ w by omega, show ePtr < 2 ^ w by dsimp [ePtr]; omega, ePtr], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 25 (.bin .add (.bin .add (.reg 13) (.const 4)) (.reg 15))) s1 .normal s2 6 :=
    runs_assign_iff.mpr ⟨vPtr, by simp [Expr.eval, BinOp.eval, s1, hr13, hr15, hw4,
      show oldRootGraph + 4 < 2 ^ w by omega, show vPtr < 2 ^ w by dsimp [vPtr]; omega, vPtr], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 26 (.load (.bin .add (.reg 13) (.const 2)))) s2 .normal s3 5 :=
    runs_assign_iff.mpr ⟨G.n, by simp [Expr.eval, BinOp.eval, s2, s1, hr13, hw2,
      show oldRootGraph + 2 < 2 ^ w by omega, hGnm], rfl, rfl, rfl⟩
  let eTriples : List (ℕ × ℕ × ℕ) :=
    (List.range G.m).map fun j => (j, G.tail (compactUnrank G.E j), G.head (compactUnrank G.E j))
  let InvE (j : ℕ) (s : State) : Prop :=
    j ≤ G.m ∧ s.regs 20 = j ∧
    (∀ r, r ≠ 20 → r ≠ 21 → s.regs r = s3.regs r) ∧
    (∀ k < j, s.mem (ePtr + 3 * k) = k ∧
      s.mem (ePtr + 3 * k + 1) = G.tail (compactUnrank G.E k) ∧
      s.mem (ePtr + 3 * k + 2) = G.head (compactUnrank G.E k)) ∧
    ZeroFrom s.mem (ePtr + 3 * j) ∧
    ∀ a < ePtr, s.mem a = st.mem a
  have hloopE := Triple.forRange_const (w := w) (p := p) (r := 20) (lo := .const 0) (hi := .reg 3)
    (P := fun s => s = s3) (Inv := InvE) 50 0 G.m (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun s hs => by
      subst hs
      refine ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], Nat.zero_le _, by simp,
        fun r h20 _ => by simp [Function.update_of_ne h20], fun _ hk => by omega,
        by simpa [s3, s2, s1, ePtr] using hz, fun _ _ => rfl⟩)
    (fun _ _ _ _ h => h.2.1)
    (fun _ s _ _ h => by
      have h3s : s.regs 3 = G.m := (h.2.2.1 3 (by decide) (by decide)).trans (by simp [s3, s2, s1, hr3])
      simp [Expr.eval, h3s])
    (fun j _ hj s ω' ⟨_, hjr, hregs, hdone, hzS, hfr⟩ => by
      have h2 : s.regs 2 = unrankPtr := (hregs 2 (by decide) (by decide)).trans (by simp [s3, s2, s1, hr2])
      have h17 : s.regs 17 = dgIntToExtBase oldRootGraph n := (hregs 17 (by decide) (by decide)).trans (by simp [s3, s2, s1, hr17])
      have h18 : s.regs 18 = dgETailSlotBase oldRootGraph n eCap := (hregs 18 (by decide) (by decide)).trans (by simp [s3, s2, s1, hr18])
      have h19 : s.regs 19 = dgEHeadSlotBase oldRootGraph n eCap := (hregs 19 (by decide) (by decide)).trans (by simp [s3, s2, s1, hr19])
      have h24 : s.regs 24 = ePtr := (hregs 24 (by decide) (by decide)).trans (by simp [s3, s2, s1])
      let u := compactUnrank G.E j
      have huMem : u ∈ G.E := compactUnrank_mem hj
      have huCap : u < eCap := hCap u huMem
      have huV := hDG.1 u huMem
      have hSlots := hDG.2.2.2.2.2.2.2.2.2.2.2.2.2.1 u huMem
      have hExtT := hDG.2.2.2.2.2.2.2.2.2.1 (G.tail u) huV.1
      have hExtH := hDG.2.2.2.2.2.2.2.2.2.1 (G.head u) huV.2
      have htSlotLt : st.mem (dgETailSlotBase oldRootGraph n eCap + u) < n := hDG.2.1 _ (hSlots.1 ▸ hExtT.1)
      have hhSlotLt : st.mem (dgEHeadSlotBase oldRootGraph n eCap + u) < n := hDG.2.1 _ (hSlots.2 ▸ hExtH.1)
      have htSlotEq : s.mem (dgETailSlotBase oldRootGraph n eCap + u) = st.mem (dgETailSlotBase oldRootGraph n eCap + u) :=
        hfr _ (by unfold dgETailSlotBase; omega)
      have hhSlotEq : s.mem (dgEHeadSlotBase oldRootGraph n eCap + u) = st.mem (dgEHeadSlotBase oldRootGraph n eCap + u) :=
        hfr _ (by unfold dgEHeadSlotBase; omega)
      have htVal : s.mem (dgIntToExtBase oldRootGraph n + st.mem (dgETailSlotBase oldRootGraph n eCap + u)) = G.tail u := by
        rw [hfr _ (by unfold dgIntToExtBase; omega), hSlots.1, hExtT.2]
      have hhVal : s.mem (dgIntToExtBase oldRootGraph n + st.mem (dgEHeadSlotBase oldRootGraph n eCap + u)) = G.head u := by
        rw [hfr _ (by unfold dgIntToExtBase; omega), hSlots.2, hExtH.2]
      have huAt : s.mem (unrankPtr + j) = u := (hfr _ (by omega)).trans (hUnr j hj)
      let t1 := { s with regs := Function.update s.regs 21 u }
      let t2 := { t1 with mem := Function.update t1.mem (ePtr + 3 * j) j }
      let t3 := { t2 with mem := Function.update t2.mem (ePtr + 3 * j + 1) (G.tail u) }
      let t4 := { t3 with mem := Function.update t3.mem (ePtr + 3 * j + 2) (G.head u) }
      have rt1 : Runs w p ω' (.assign 21 (.load (.bin .add (.reg 2) (.reg 20)))) s .normal t1 5 :=
        runs_assign_iff.mpr ⟨u, by simp [Expr.eval, BinOp.eval, h2, hjr, show unrankPtr + j < 2 ^ w by omega, huAt],
          rfl, rfl, rfl⟩
      have rt2 : Runs w p ω' (.store (.bin .add (.reg 24) (.bin .mul (.const 3) (.reg 20))) (.reg 20)) t1 .normal t2 7 :=
        runs_store_iff.mpr ⟨ePtr + 3 * j, j, by
          simp [Expr.eval, BinOp.eval, t1, h24, hjr, hw3, show 3 * j < 2 ^ w by omega,
            show ePtr + 3 * j < 2 ^ w by omega],
          by simp [Expr.eval, t1, hjr], rfl, rfl, rfl⟩
      have rt3 : Runs w p ω'
          (.store (.bin .add (.bin .add (.reg 24) (.bin .mul (.const 3) (.reg 20))) (.const 1))
            (.load (.bin .add (.reg 17) (.load (.bin .add (.reg 18) (.reg 21)))))) t2 .normal t3 15 :=
        runs_store_iff.mpr ⟨ePtr + 3 * j + 1, G.tail u, by
          simp [Expr.eval, BinOp.eval, t2, t1, h24, hjr, hw3, hw1, show 3 * j < 2 ^ w by omega,
            show ePtr + 3 * j < 2 ^ w by omega, show ePtr + 3 * j + 1 < 2 ^ w by omega],
          by simp [Expr.eval, BinOp.eval, t2, t1, h17, h18,
            show dgETailSlotBase oldRootGraph n eCap + u < 2 ^ w by unfold dgETailSlotBase; omega,
            Function.update_of_ne (by unfold dgETailSlotBase; omega : dgETailSlotBase oldRootGraph n eCap + u ≠ ePtr + 3 * j),
            htSlotEq, show dgIntToExtBase oldRootGraph n + st.mem (dgETailSlotBase oldRootGraph n eCap + u) < 2 ^ w by
              unfold dgIntToExtBase; omega,
            Function.update_of_ne (by unfold dgIntToExtBase; omega :
              dgIntToExtBase oldRootGraph n + st.mem (dgETailSlotBase oldRootGraph n eCap + u) ≠ ePtr + 3 * j), htVal],
          rfl, rfl, rfl⟩
      have rt4 : Runs w p ω'
          (.store (.bin .add (.bin .add (.reg 24) (.bin .mul (.const 3) (.reg 20))) (.const 2))
            (.load (.bin .add (.reg 17) (.load (.bin .add (.reg 19) (.reg 21)))))) t3 .normal t4 15 :=
        runs_store_iff.mpr ⟨ePtr + 3 * j + 2, G.head u, by
          simp [Expr.eval, BinOp.eval, t3, t2, t1, h24, hjr, hw3, hw2, show 3 * j < 2 ^ w by omega,
            show ePtr + 3 * j < 2 ^ w by omega, show ePtr + 3 * j + 2 < 2 ^ w by omega],
          by simp [Expr.eval, BinOp.eval, t3, t2, t1, h17, h19,
            show dgEHeadSlotBase oldRootGraph n eCap + u < 2 ^ w by unfold dgEHeadSlotBase; omega,
            Function.update_of_ne (by unfold dgEHeadSlotBase; omega : dgEHeadSlotBase oldRootGraph n eCap + u ≠ ePtr + 3 * j + 1),
            Function.update_of_ne (by unfold dgEHeadSlotBase; omega : dgEHeadSlotBase oldRootGraph n eCap + u ≠ ePtr + 3 * j),
            hhSlotEq, show dgIntToExtBase oldRootGraph n + st.mem (dgEHeadSlotBase oldRootGraph n eCap + u) < 2 ^ w by
              unfold dgIntToExtBase; omega,
            Function.update_of_ne (by unfold dgIntToExtBase; omega :
              dgIntToExtBase oldRootGraph n + st.mem (dgEHeadSlotBase oldRootGraph n eCap + u) ≠ ePtr + 3 * j + 1),
            Function.update_of_ne (by unfold dgIntToExtBase; omega :
              dgIntToExtBase oldRootGraph n + st.mem (dgEHeadSlotBase oldRootGraph n eCap + u) ≠ ePtr + 3 * j), hhVal],
          rfl, rfl, rfl⟩
      refine ⟨.normal, t4, 5 + (7 + (15 + 15 + 1) + 1) + 1,
        runs_seq_iff.mpr (Or.inr ⟨t1, 5, _, rt1, runs_seq_iff.mpr (Or.inr ⟨t2, 7, _, rt2,
          runs_seq_iff.mpr (Or.inr ⟨t3, 15, 15, rt3, rt4, rfl⟩), rfl⟩), rfl⟩),
        ⟨⟨by omega, by simp, fun r h20 h21 => by simp [t4, t3, t2, t1, Function.update_of_ne h20,
          Function.update_of_ne h21, hregs r h20 h21],
          fun k hk => by
            by_cases hkj : k = j
            · subst hkj; exact ⟨by simp [t4, t3, t2], by simp [t4, t3, u], by simp [t4, u]⟩
            · have hd := hdone k (by omega)
              refine ⟨by simp only [t4, t3, t2, t1, Function.update_of_ne (by omega : ePtr + 3 * k ≠ ePtr + 3 * j + 2),
                  Function.update_of_ne (by omega : ePtr + 3 * k ≠ ePtr + 3 * j + 1),
                  Function.update_of_ne (by omega : ePtr + 3 * k ≠ ePtr + 3 * j)]; exact hd.1,
                by simp only [t4, t3, t2, t1, Function.update_of_ne (by omega : ePtr + 3 * k + 1 ≠ ePtr + 3 * j + 2),
                  Function.update_of_ne (by omega : ePtr + 3 * k + 1 ≠ ePtr + 3 * j + 1),
                  Function.update_of_ne (by omega : ePtr + 3 * k + 1 ≠ ePtr + 3 * j)]; exact hd.2.1,
                by simp only [t4, t3, t2, t1, Function.update_of_ne (by omega : ePtr + 3 * k + 2 ≠ ePtr + 3 * j + 2),
                  Function.update_of_ne (by omega : ePtr + 3 * k + 2 ≠ ePtr + 3 * j + 1),
                  Function.update_of_ne (by omega : ePtr + 3 * k + 2 ≠ ePtr + 3 * j)]; exact hd.2.2⟩,
          fun a ha => by
            simp only [t4, t3, t2, t1, Function.update_of_ne (by omega : a ≠ ePtr + 3 * j + 2),
              Function.update_of_ne (by omega : a ≠ ePtr + 3 * j + 1),
              Function.update_of_ne (by omega : a ≠ ePtr + 3 * j)]
            exact hzS a (by omega),
          fun a ha => by
            simp only [t4, t3, t2, t1, Function.update_of_ne (by omega : a ≠ ePtr + 3 * j + 2),
              Function.update_of_ne (by omega : a ≠ ePtr + 3 * j + 1),
              Function.update_of_ne (by omega : a ≠ ePtr + 3 * j)]
            exact hfr a ha⟩, by simp [t4, t3, t2, t1, hjr]⟩, by dsimp only; omega⟩)
  obtain ⟨o, s4, cE, rE, hS4, hcE⟩ := hloopE.runs ω rfl
  cases o with
  | returned _ => exact False.elim hS4
  | normal =>
    obtain ⟨_, _, hs4Regs, hTriplesAt, hz4, hFr4⟩ := hS4
    have hs4_r (r : ℕ) (h20 : r ≠ 20) (h21 : r ≠ 21) (h24 : r ≠ 24) (h25 : r ≠ 25) (h26 : r ≠ 26) :
        s4.regs r = st.regs r := by
      rw [hs4Regs r h20 h21]; simp [s3, s2, s1, Function.update_of_ne h26, Function.update_of_ne h25,
        Function.update_of_ne h24]
    let s5 := { s4 with regs := Function.update s4.regs 27 newRootGraph }
    have r5 : Runs w p ω (.assign 27 (.bin .add (.reg 24) (.bin .mul (.const 3) (.reg 3)))) s4 .normal s5 6 :=
      runs_assign_iff.mpr ⟨newRootGraph, by
        simp [Expr.eval, BinOp.eval, hs4Regs 24 (by decide) (by decide), hs4Regs 3 (by decide) (by decide),
          s3, s2, s1, hr3, hw3, show 3 * G.m < 2 ^ w by omega, show newRootGraph < 2 ^ w by dsimp [newRootGraph]; omega,
          newRootGraph], rfl, rfl, rfl⟩
    have hmLeECap : G.m ≤ eCap := by
      have : G.E.card ≤ (Finset.range eCap).card := Finset.card_le_card (fun e he => Finset.mem_range.mpr (hCap e he))
      simpa [MGraph.m] using this
    have hPreDG (gPtr : ℕ) (mCur : ℕ → ℕ) (hgGe : newRootGraph ≤ gPtr) (hgW : gPtr + dgSz < 2 ^ w)
        (hzCur : ZeroFrom mCur gPtr) (hag : ∀ a < newRootGraph, mCur a = s4.mem a) :
        (dgInitFromListsContract w n eCap G.compact vL eTriples).pre
          [gPtr, n, eCap, G.n, vPtr, G.m, ePtr] mCur := by
      refine ⟨gPtr, G.n, vPtr, G.m, ePtr, rfl, h16, hgW, hzCur, hGValid,
        fun v hv => hDG.2.1 v hv, fun e he => by simp only [MGraph.compact, Finset.mem_range] at he; dsimp only [MGraph.m] at hmLeECap; omega,
        hvLen, fun i hi => by rw [hag _ (by dsimp [vPtr, newRootGraph, ePtr]; omega), hFr4 _ (by dsimp [vPtr, ePtr]; omega)]; exact hvAt i hi,
        hvMem, fun i hi => by dsimp only [vPtr, newRootGraph, ePtr] at hgGe ⊢; omega,
        by simp [eTriples], by simp [eTriples, List.map_map, Function.comp_def, List.nodup_range],
        fun i hi => by
          have hiM : i < G.m := by simpa [eTriples] using hi
          refine ⟨by rw [hag _ (by dsimp [newRootGraph]; omega)]; simpa [eTriples] using (hTriplesAt i hiM).1,
            by rw [hag _ (by dsimp [newRootGraph]; omega)]; simpa [eTriples] using (hTriplesAt i hiM).2.1,
            by rw [hag _ (by dsimp [newRootGraph]; omega)]; simpa [eTriples] using (hTriplesAt i hiM).2.2⟩,
        fun t ht => by
          simp only [eTriples, List.mem_map, List.mem_range] at ht
          obtain ⟨j, hj, rfl⟩ := ht
          exact ⟨by simp [MGraph.compact, MGraph.m] at hj ⊢; exact hj, rfl, rfl⟩,
        fun e he => by
          simp only [MGraph.compact, Finset.mem_range] at he
          exact ⟨(e, G.tail (compactUnrank G.E e), G.head (compactUnrank G.E e)),
            by simp only [eTriples, List.mem_map, List.mem_range]; exact ⟨e, he, rfl⟩, rfl⟩,
        fun i hi => by dsimp only [newRootGraph] at hgGe; omega⟩
    obtain ⟨s6, cD1, _, r6, hpD1, _, hs6Regs, hcD1⟩ :=
      runs_call_of_meetsContract (r := 23) (args := [.reg 27, .reg 15, .reg 16, .reg 26, .reg 25, .reg 3, .reg 24])
        (hDGInit vL eTriples) (st := s5) (vs := [newRootGraph, n, eCap, G.n, vPtr, G.m, ePtr])
        (by simp [evalArgs, Expr.eval, s5, hs4Regs 15 (by decide) (by decide), hs4Regs 16 (by decide) (by decide),
          hs4Regs 26 (by decide) (by decide), hs4Regs 25 (by decide) (by decide), hs4Regs 3 (by decide) (by decide),
          hs4Regs 24 (by decide) (by decide), s3, s2, s1, hr15, hr16, hr3])
        (by simp [show newRootGraph < 2 ^ w by omega, show n < 2 ^ w by omega, show eCap < 2 ^ w by omega,
          show G.n < 2 ^ w by omega, show vPtr < 2 ^ w by dsimp [vPtr]; omega, show G.m < 2 ^ w by omega,
          show ePtr < 2 ^ w by omega])
        (hPreDG newRootGraph s5.mem le_rfl (by omega) hz4 (fun _ _ => rfl)) ω
    obtain ⟨_, _, _, _, _, hArgs1, _, hDG1, hFrD1, hz6⟩ := hpD1
    simp only [List.cons.injEq, and_true, true_and] at hArgs1
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hArgs1
    let s7 := { s6 with regs := Function.update s6.regs 28 dgSz }
    let s8 := { s7 with regs := Function.update s7.regs 29 newLvlGraph0 }
    have r7 : Runs w p ω (.assign 28 (.bin .add (.bin .add (.const 4) (.bin .mul (.const 7) (.reg 15)))
        (.bin .mul (.const 9) (.reg 16)))) s6 .normal s7 10 :=
      runs_assign_iff.mpr ⟨dgSz, by
        simp [Expr.eval, BinOp.eval, hs6Regs 15 (by decide), hs6Regs 16 (by decide), s5,
          hs4_r 15 (by decide) (by decide) (by decide) (by decide) (by decide),
          hs4_r 16 (by decide) (by decide) (by decide) (by decide) (by decide),
          hr15, hr16, hw4, hw7, hw9, show 7 * n < 2 ^ w by omega, show 4 + 7 * n < 2 ^ w by omega,
          show 9 * eCap < 2 ^ w by omega, show 4 + 7 * n + 9 * eCap < 2 ^ w by omega, hDgDef], rfl, rfl, rfl⟩
    have r8 : Runs w p ω (.assign 29 (.bin .add (.reg 27) (.reg 28))) s7 .normal s8 4 :=
      runs_assign_iff.mpr ⟨newLvlGraph0, by
        simp [Expr.eval, BinOp.eval, s7, hs6Regs 27 (by decide), s5,
          show newLvlGraph0 < 2 ^ w by omega, newLvlGraph0], rfl, rfl, rfl⟩
    obtain ⟨s9, cD2, _, r9, hpD2, _, hs9Regs, hcD2⟩ :=
      runs_call_of_meetsContract (r := 23) (args := [.reg 29, .reg 15, .reg 16, .reg 26, .reg 25, .reg 3, .reg 24])
        (hDGInit vL eTriples) (st := s8) (vs := [newLvlGraph0, n, eCap, G.n, vPtr, G.m, ePtr])
        (by simp [evalArgs, Expr.eval, s8, s7, hs6Regs 15 (by decide), hs6Regs 16 (by decide),
          hs6Regs 26 (by decide), hs6Regs 25 (by decide), hs6Regs 3 (by decide), hs6Regs 24 (by decide),
          s5, hs4Regs 15 (by decide) (by decide), hs4Regs 16 (by decide) (by decide),
          hs4Regs 26 (by decide) (by decide), hs4Regs 25 (by decide) (by decide),
          hs4Regs 3 (by decide) (by decide), hs4Regs 24 (by decide) (by decide), s3, s2, s1, hr15, hr16, hr3])
        (by simp [show newLvlGraph0 < 2 ^ w by omega, show n < 2 ^ w by omega, show eCap < 2 ^ w by omega,
          show G.n < 2 ^ w by omega, show vPtr < 2 ^ w by dsimp [vPtr]; omega, show G.m < 2 ^ w by omega,
          show ePtr < 2 ^ w by omega])
        (hPreDG newLvlGraph0 s8.mem (by omega) (by omega) hz6 (fun a ha => hFrD1 a (Or.inl ha))) ω
    obtain ⟨_, _, _, _, _, hArgs2, _, hDG2, hFrD2, hz9⟩ := hpD2
    simp only [List.cons.injEq, and_true, true_and] at hArgs2
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hArgs2
    let s10 := { s9 with regs := Function.update s9.regs 30 nextHeap }
    let s11 := { s10 with mem := Function.update s10.mem (root + 14) newRootGraph }
    let s12 := { s11 with mem := Function.update s11.mem levelMeta newLen0 }
    let s13 := { s12 with mem := Function.update s12.mem (levelMeta + d) newLvlGraph0 }
    have hs9_r (r : ℕ) (h20 : r ≠ 20) (h21 : r ≠ 21) (h23 : r ≠ 23) (h24 : r ≠ 24) (h25 : r ≠ 25)
        (h26 : r ≠ 26) (h27 : r ≠ 27) (h28 : r ≠ 28) (h29 : r ≠ 29) : s9.regs r = st.regs r := by
      rw [hs9Regs r h23]; simp only [s8, s7, Function.update_of_ne h29, Function.update_of_ne h28]
      rw [hs6Regs r h23]; simp only [s5, Function.update_of_ne h27]
      exact hs4_r r h20 h21 h24 h25 h26
    have r10 : Runs w p ω (.assign 30 (.bin .add (.reg 29) (.reg 28))) s9 .normal s10 4 :=
      runs_assign_iff.mpr ⟨nextHeap, by
        simp [Expr.eval, BinOp.eval, hs9Regs 29 (by decide), hs9Regs 28 (by decide), s8, s7,
          hNextEq, show newLvlGraph0 + dgSz < 2 ^ w by omega], rfl, rfl, rfl⟩
    have r11 : Runs w p ω (.store (.bin .add (.reg 0) (.const 14)) (.reg 27)) s10 .normal s11 5 :=
      runs_store_iff.mpr ⟨root + 14, newRootGraph, by
        simp [Expr.eval, BinOp.eval, s10, hs9_r 0 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide), hr0, show 14 < 2 ^ w by omega,
          show root + 14 < 2 ^ w by omega],
        by simp [Expr.eval, s10, hs9Regs 27 (by decide), s8, s7, hs6Regs 27 (by decide), s5], rfl, rfl, rfl⟩
    have r12 : Runs w p ω (.store (.reg 32) (.reg 22)) s11 .normal s12 3 :=
      runs_store_iff.mpr ⟨levelMeta, newLen0, by
        simp [Expr.eval, s11, s10, hs9_r 32 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide), hr32],
        by simp [Expr.eval, s11, s10, hs9_r 22 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide), hr22], rfl, rfl, rfl⟩
    have r13 : Runs w p ω (.store (.bin .add (.reg 32) (.reg 7)) (.reg 29)) s12 .normal s13 5 :=
      runs_store_iff.mpr ⟨levelMeta + d, newLvlGraph0, by
        simp [Expr.eval, BinOp.eval, s12, s11, s10,
          hs9_r 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          hs9_r 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          hr32, hr7, show levelMeta + d < 2 ^ w by omega],
        by simp [Expr.eval, s12, s11, s10, hs9Regs 29 (by decide), s8], rfl, rfl, rfl⟩
    have rAll := runs_seq_iff.mpr (Or.inr ⟨s1, 6, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 6, _, r2,
      runs_seq_iff.mpr (Or.inr ⟨s3, 5, _, r3,
      runs_seq_iff.mpr (Or.inr ⟨s4, cE, _, rE,
      runs_seq_iff.mpr (Or.inr ⟨s5, 6, _, r5,
      runs_seq_iff.mpr (Or.inr ⟨s6, cD1, _, r6,
      runs_seq_iff.mpr (Or.inr ⟨s7, 10, _, r7,
      runs_seq_iff.mpr (Or.inr ⟨s8, 4, _, r8,
      runs_seq_iff.mpr (Or.inr ⟨s9, cD2, _, r9,
      runs_seq_iff.mpr (Or.inr ⟨s10, 4, _, r10,
      runs_seq_iff.mpr (Or.inr ⟨s11, 5, _, r11,
      runs_seq_iff.mpr (Or.inr ⟨s12, 3, 5, r12, r13, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
      rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    have h13_above (a : ℕ) (ha : ePtr ≤ a) : s13.mem a = s9.mem a := by
      simp [s13, s12, s11, s10, Function.update_of_ne (by omega : a ≠ levelMeta + d),
        Function.update_of_ne (by omega : a ≠ levelMeta), Function.update_of_ne (by omega : a ≠ root + 14)]
    refine ⟨s13, _, rAll, ?_, by simp [s13, s12, s11, s10],
      fun r h20 h21 h23 h24 h25 h26 h27 h28 h29 h30 => by
        simp only [s13, s12, s11, s10, Function.update_of_ne h30]
        exact hs9_r r h20 h21 h23 h24 h25 h26 h27 h28 h29,
      hDG1.of_agree (fun a h1 h2 => (h13_above a (by omega)).trans (hFrD2 a (Or.inl (by omega)))),
      hDG2.of_agree (fun a h1 h2 => h13_above a (by omega)),
      by simp [s13, s12, s11, Function.update_of_ne (by rcases hDisjRM with h | h <;> omega : root + 14 ≠ levelMeta + d),
        Function.update_of_ne (by rcases hDisjRM with h | h <;> omega : root + 14 ≠ levelMeta)],
      by simp [s13, s12, Function.update_of_ne (by omega : levelMeta ≠ levelMeta + d)],
      by simp [s13],
      fun a ha => (h13_above a (by omega)).trans (hz9 a (by rw [← hNextEq]; exact ha)),
      fun a ha h1 h2 h3 => by
        simp only [s13, s12, s11, s10, Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
        exact (hFrD2 a (Or.inl (by omega))).trans ((hFrD1 a (Or.inl (by omega))).trans (hFr4 a ha))⟩
    · simp only [dgInitFromListsContract, argsSize, Expr.size, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some] at hcD1 hcD2 hcE
      omega

end MinCostFlow.MinRatio
