module

public import MinCostFlow.MinRatio.WireSelectHeapDel
import WordRAM.Tactic
import Mathlib.Data.Nat.Log

/-!
# Conditional level delete, bulk level clear, and relocatable select-heap module

Implements `heapDeleteIfLevelBody`, `heapClearLevelBody`, and `selectHeapOpsModule` (22 procs).
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num DynSpanner.Program

/-- Delete edge `e` (`reg 1`) iff `pos[e] ≠ 0 ∧ lvl[e] = lvl` (`reg 2`).
Arguments: `[hb, e, lvl, scratch]`. -/
def heapDeleteIfLevelBody (del : ℕ) : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.const shPosOff))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const shLvlOff))) ;;
  .assign 6 (.load (.bin .add (.reg 4) (.reg 1))) ;;
  .cond (.reg 6)
    (.assign 7 (.load (.bin .add (.reg 5) (.reg 1))) ;;
     .cond (.bin .eq (.reg 7) (.reg 2))
       (.call 8 del [.reg 0, .reg 1, .reg 3] ;; .ret (.reg 8))
       (.ret (.reg 3)))
    (.ret (.reg 3))

theorem heapDeleteIfLevelBody_noRand (del : ℕ) :
    (heapDeleteIfLevelBody del).NoRand := by
  simp [heapDeleteIfLevelBody, Stmt.NoRand]

/-- Step cost bound for `heapDeleteIfLevelBody`. -/
def heapDeleteIfLevelCost (cap Lk : ℕ) : ℕ :=
  heapDeleteCost cap Lk + 60

/-- Contract for `heapDeleteIfLevelBody`. -/
def heapDeleteIfLevelContract (w h : ℕ) (loc : SelectHeapLoc) (size : ℕ) : Contract where
  pre args mem :=
    ∃ e lvl scratch, args = [loc.hb, e, lvl, scratch] ∧
      16 < 2 ^ w ∧ loc.endAddr ≤ scratch ∧ e < loc.cap ∧ lvl ≤ loc.d ∧
      SelectHeapAt mem loc h size ∧
      ZeroFrom mem scratch ∧
      scratch + heapRebalanceSpace loc.cap loc.Lk < 2 ^ w
  post args mem ret mem' :=
    let e := args.getD 1 0
    let lvl := args.getD 2 0
    let scratch := args.getD 3 0
    let hit := mem (loc.posPtr + e) ≠ 0 ∧ mem (loc.lvlPtr + e) = lvl
    let size' := if hit then size - 1 else size
    scratch ≤ ret ∧ ret ≤ scratch + heapRebalanceSpace loc.cap loc.Lk ∧
    SelectHeapAt mem' loc h size' ∧
    ZeroFrom mem' ret ∧
    (hit → mem' (loc.posPtr + e) = 0) ∧
    (¬ hit → mem' (loc.posPtr + e) = mem (loc.posPtr + e) ∧
      mem' (loc.lvlPtr + e) = mem (loc.lvlPtr + e) ∧
      loc.readNum mem' h e = loc.readNum mem h e ∧
      loc.readDen mem' h e = loc.readDen mem h e) ∧
    (∀ e' < loc.cap, e' ≠ e →
      (mem' (loc.posPtr + e') ≠ 0 ↔ mem (loc.posPtr + e') ≠ 0) ∧
      mem' (loc.lvlPtr + e') = mem (loc.lvlPtr + e') ∧
      loc.readNum mem' h e' = loc.readNum mem h e' ∧
      loc.readDen mem' h e' = loc.readDen mem h e') ∧
    (∀ a < scratch, (a < loc.hb ∨ loc.numBase ≤ a) → mem' a = mem a)
  cost _ _ := heapDeleteIfLevelCost loc.cap loc.Lk

/-- Recursively delete every candidate at level `lvl` (`reg 1`) via `candHead[lvl]`.
Arguments: `[hb, lvl, scratch]`. -/
def heapClearLevelBody (self del : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const shCandHeadOff))) ;;
  .assign 4 (.load (.bin .add (.reg 3) (.reg 1))) ;;
  .cond (.bin .eq (.reg 4) (.const 0))
    (.ret (.reg 2))
    (.assign 5 (.bin .sub (.reg 4) (.const 1)) ;;
     .call 6 del [.reg 0, .reg 5, .reg 2] ;;
     .call 7 self [.reg 0, .reg 1, .reg 6] ;;
     .ret (.reg 7))

theorem heapClearLevelBody_noRand (self del : ℕ) :
    (heapClearLevelBody self del).NoRand := by
  simp [heapClearLevelBody, Stmt.NoRand]

/-- Number of active candidates at level `lvl` in memory `mem`. -/
def levelCandCount (mem : ℕ → ℕ) (loc : SelectHeapLoc) (lvl : ℕ) : ℕ :=
  ((Finset.range loc.cap).filter fun e =>
    mem (loc.posPtr + e) ≠ 0 ∧ mem (loc.lvlPtr + e) = lvl).card

/-- Scratch space bound for clearing `k` candidates at one level. -/
def heapClearLevelSpace (k cap Lk : ℕ) : ℕ :=
  k * heapRebalanceSpace cap Lk

/-- Step cost bound for clearing `k` candidates at one level. -/
def heapClearLevelCost (k cap Lk : ℕ) : ℕ :=
  k * (heapDeleteCost cap Lk + 60) + 40

/-- Contract for `heapClearLevelBody`: deletes every edge at level `lvl`, leaving every edge at
any other level untouched with identical level and key. -/
def heapClearLevelContract (w h : ℕ) (loc : SelectHeapLoc) : Contract where
  pre args mem :=
    ∃ lvl scratch size, args = [loc.hb, lvl, scratch] ∧
      16 < 2 ^ w ∧ loc.endAddr ≤ scratch ∧ lvl ≤ loc.d ∧
      SelectHeapAt mem loc h size ∧
      ZeroFrom mem scratch ∧
      scratch + heapClearLevelSpace (levelCandCount mem loc lvl) loc.cap loc.Lk < 2 ^ w
  post args mem ret mem' :=
    let lvl := args.getD 1 0
    let scratch := args.getD 2 0
    let cnt := levelCandCount mem loc lvl
    let size := mem loc.hb
    scratch ≤ ret ∧ ret ≤ scratch + heapClearLevelSpace cnt loc.cap loc.Lk ∧
    cnt ≤ size ∧
    SelectHeapAt mem' loc h (size - cnt) ∧
    ZeroFrom mem' ret ∧
    (∀ e < loc.cap, mem (loc.posPtr + e) ≠ 0 → mem (loc.lvlPtr + e) = lvl →
      mem' (loc.posPtr + e) = 0) ∧
    (∀ e < loc.cap, ¬ (mem (loc.posPtr + e) ≠ 0 ∧ mem (loc.lvlPtr + e) = lvl) →
      (mem' (loc.posPtr + e) ≠ 0 ↔ mem (loc.posPtr + e) ≠ 0) ∧
      mem' (loc.lvlPtr + e) = mem (loc.lvlPtr + e) ∧
      loc.readNum mem' h e = loc.readNum mem h e ∧
      loc.readDen mem' h e = loc.readDen mem h e) ∧
    (∀ a < scratch, (a < loc.hb ∨ loc.numBase ≤ a) → mem' a = mem a)
  cost args mem := heapClearLevelCost (levelCandCount mem loc (args.getD 1 0)) loc.cap loc.Lk

/-! ## 2. Relocatable 22-procedure select-heap module -/

/-- Relocatable 22-procedure module implementing all select-heap primitives starting at `b`:
- `b + 0 .. b + 11`: `keyCompareModule b h` (entry `b + 0`)
- `b + 12`: `copyLimbsToBody`
- `b + 13`: `candListConsBody`
- `b + 14`: `candListEraseBody`
- `b + 15`: `heapSiftUpBody (b + 15) b`
- `b + 16`: `heapSiftDownBody (b + 16) b`
- `b + 17`: `heapRebalanceBody b (b + 15) (b + 16)`
- `b + 18`: `heapUpsertBody (b + 12) (b + 15) (b + 17) (b + 13) (b + 14)`
- `b + 19`: `heapDeleteBody (b + 17) (b + 14)`
- `b + 20`: `heapDeleteIfLevelBody (b + 19)`
- `b + 21`: `heapClearLevelBody (b + 21) (b + 19)` -/
def selectHeapOpsModule (b h : ℕ) : List Stmt :=
  keyCompareModule b h ++
  [ copyLimbsToBody,
    candListConsBody,
    candListEraseBody,
    heapSiftUpBody (b + 15) b,
    heapSiftDownBody (b + 16) b,
    heapRebalanceBody b (b + 15) (b + 16),
    heapUpsertBody (b + 12) (b + 15) (b + 17) (b + 13) (b + 14),
    heapDeleteBody (b + 17) (b + 14),
    heapDeleteIfLevelBody (b + 19),
    heapClearLevelBody (b + 21) (b + 19) ]

theorem selectHeapOpsModule_length (b h : ℕ) : (selectHeapOpsModule b h).length = 22 := by
  simp [selectHeapOpsModule, keyCompareModule_length]

theorem selectHeapOpsModule_noRand (b h : ℕ) :
    ∀ s ∈ selectHeapOpsModule b h, s.NoRand := by
  intro s hs
  simp only [selectHeapOpsModule, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with hk | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact keyCompareModule_noRand b h s hk
  · exact copyLimbsToBody_noRand
  · exact candListConsBody_noRand
  · exact candListEraseBody_noRand
  · exact heapSiftUpBody_noRand ..
  · exact heapSiftDownBody_noRand ..
  · exact heapRebalanceBody_noRand ..
  · exact heapUpsertBody_noRand ..
  · exact heapDeleteBody_noRand ..
  · exact heapDeleteIfLevelBody_noRand ..
  · exact heapClearLevelBody_noRand ..

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num DynSpanner.Program

/-- `heapDeleteIfLevelBody` meets `heapDeleteIfLevelContract`. -/
theorem heapDeleteIfLevel_meetsContract {w h proc del : ℕ}
    {loc : SelectHeapLoc} {size : ℕ} {p : Program}
    (hp : p.procs[proc]? = some (heapDeleteIfLevelBody del))
    (hdel : MeetsContract w p del (heapDeleteContract w h loc size)) :
    MeetsContract w p proc (heapDeleteIfLevelContract w h loc size) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨e, lvl, scratch, rfl, hw16, hendLe, heCap, hlvlD, hat, hz, hroom⟩ := hpre
  obtain ⟨hhdr, hbij, hkeys, hord, hcand⟩ := hat
  have hhr := selectHeap_header_reads hhdr
  have hlvlHdr : mem (loc.hb + 6) = loc.lvlPtr := by simpa using hhdr 6 (by simp)
  have hlayout : loc.hb + 14 ≤ loc.posPtr ∧ loc.posPtr + loc.cap = loc.lvlPtr ∧
      loc.lvlPtr + loc.cap ≤ loc.endAddr := by
    have := loc.endAddr_eq
    unfold SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr SelectHeapLoc.arrPtr selectHeapSize shHdrSize at *
    omega
  have hw1 : 1 < 2 ^ w := by omega
  have hhbw : loc.hb < 2 ^ w := hwords loc.hb (by simp)
  have hew : e < 2 ^ w := hwords e (by simp)
  have hlvlw : lvl < 2 ^ w := hwords lvl (by simp)
  have hscw : scratch < 2 ^ w := hwords scratch (by simp)
  have hposW : loc.posPtr < 2 ^ w := by omega
  have hlvlPtrW : loc.lvlPtr < 2 ^ w := by omega
  have hposEW : mem (loc.posPtr + e) < 2 ^ w := by
    rcases hbij.2.2.2 e heCap with h0 | ⟨hle, _⟩; omega; have := hbij.1; omega
  apply runs_start_le
  dsimp only [startState]
  unfold heapDeleteIfLevelBody
  simp only [shPosOff, shLvlOff]
  refine runs_seq_assign_flat (v := loc.posPtr) (by eval_expr; exact hhr.2.2.2.1) ?_
  refine runs_seq_assign_flat (v := loc.lvlPtr) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := mem (loc.posPtr + e)) (by eval_expr) ?_
  by_cases hpos0 : mem (loc.posPtr + e) = 0
  · refine WordRAM.runs_cond_le (v := 0) (by simp [Expr.eval, hpos0]) (fun h => absurd rfl h) ?_
    intro _
    refine WordRAM.runs_ret_le (v := scratch) (by eval_expr) ?_ ?_
    · dsimp only [heapDeleteIfLevelContract]
      simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ, hpos0, ne_eq, not_true_eq_false, false_and, ↓reduceIte]
      exact ⟨le_rfl, Nat.le_add_right _ _, ⟨hhdr, hbij, hkeys, hord, hcand⟩, hz,
        fun h => h.elim, fun _ => ⟨trivial, trivial, trivial, trivial⟩,
        fun _ _ _ => ⟨trivial, trivial, trivial, trivial⟩, fun _ _ _ => trivial⟩
    · simp only [heapDeleteIfLevelContract, heapDeleteIfLevelCost, Expr.size]; omega
  · have hlvlEW : mem (loc.lvlPtr + e) < 2 ^ w := by
      have := (hkeys e heCap hpos0).1
      have := loc.endAddr_eq; unfold selectHeapSize shHdrSize at *; omega
    refine WordRAM.runs_cond_le (v := mem (loc.posPtr + e)) (by eval_expr) ?_ (fun h => absurd h hpos0)
    intro _
    refine runs_seq_assign_flat (v := mem (loc.lvlPtr + e)) (by eval_expr) ?_
    by_cases hsame : mem (loc.lvlPtr + e) = lvl
    · refine WordRAM.runs_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, hsame, hw1]) ?_ (fun h => absurd h (by decide))
      intro _
      refine runs_seq_call_flat hdel (vs := [loc.hb, e, scratch]) (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨e, scratch, rfl, hw16, hendLe, heCap, ⟨hhdr, hbij, hkeys, hord, hcand⟩, hz, hroom⟩
      · intro ret mem1 pos1 hp1
        obtain ⟨hlo1, hhi1, hat1, hz1, hpE1, hoth1, hfr1⟩ := hp1
        simp only [List.getD_cons_zero, List.getD_cons_succ] at hlo1 hhi1 hpE1 hoth1 hfr1
        have hretw : ret < 2 ^ w := by omega
        refine WordRAM.runs_ret_le (v := ret) (by eval_expr) ?_ ?_
        · dsimp only [heapDeleteIfLevelContract]
          simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ, hpos0, hsame,
            ne_eq, not_false_eq_true, and_self, ↓reduceIte] at hat1 ⊢
          exact ⟨hlo1, hhi1, hat1, hz1, fun _ => hpE1, fun h => (h trivial).elim, hoth1, hfr1⟩
        · simp only [heapDeleteIfLevelContract, heapDeleteIfLevelCost, heapDeleteContract,
            Expr.size, argsSize]; omega
    · refine WordRAM.runs_cond_le (v := 0) (by simp [Expr.eval, BinOp.eval, hsame, show 0 < 2 ^ w by omega])
        (fun h => absurd rfl h) ?_
      intro _
      refine WordRAM.runs_ret_le (v := scratch) (by eval_expr) ?_ ?_
      · dsimp only [heapDeleteIfLevelContract]
        simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ, hsame, and_false, ↓reduceIte]
        exact ⟨le_rfl, Nat.le_add_right _ _, ⟨hhdr, hbij, hkeys, hord, hcand⟩, hz,
          fun h => h.elim, fun _ => ⟨trivial, trivial, trivial, trivial⟩,
          fun _ _ _ => ⟨trivial, trivial, trivial, trivial⟩, fun _ _ _ => trivial⟩
      · simp only [heapDeleteIfLevelContract, heapDeleteIfLevelCost, Expr.size]; omega

/-- `heapClearLevelBody` meets `heapClearLevelContract` in
`O(|S_lvl| · (log(cap + 1) + 1) · (Lk^2 + 1))` steps. -/
theorem heapClearLevel_meetsContract {w h self del : ℕ} {loc : SelectHeapLoc} {p : Program}
    (hp : p.procs[self]? = some (heapClearLevelBody self del))
    (hdel : ∀ size, MeetsContract w p del (heapDeleteContract w h loc size)) :
    MeetsContract w p self (heapClearLevelContract w h loc) := by
  apply meetsContract_of_rec (fun args mem => levelCandCount mem loc (args.getD 1 0)) hp
  intro cntM ih args mem pos ω hwords hpre hcntEq
  obtain ⟨lvl, scratch, size, rfl, hw16, hendLe, hlvlD, hat, hz, hroom⟩ := hpre
  change levelCandCount mem loc lvl = cntM at hcntEq
  subst hcntEq
  obtain ⟨hhdr, hbij, hkeys, hord, hcand⟩ := hat
  have hhdSize : mem loc.hb = size := by simpa using hhdr 0 (by simp)
  have hchHdr : mem (loc.hb + 9) = loc.candHead := by simpa using hhdr 9 (by simp)
  have hchB : loc.hb + 14 ≤ loc.candHead ∧ loc.candHead + (loc.d + 1) ≤ loc.endAddr := by
    have := loc.endAddr_eq
    unfold SelectHeapLoc.candHead SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr
      SelectHeapLoc.arrPtr selectHeapSize shHdrSize at *
    omega
  obtain ⟨lists, hlists⟩ := hcand
  have hL := (hlists lvl hlvlD).1
  have hLiff := (hlists lvl hlvlD).2
  have hcntLeSize : levelCandCount mem loc lvl ≤ size := by
    have hsub : (Finset.range loc.cap).filter (fun e => mem (loc.posPtr + e) ≠ 0 ∧ mem (loc.lvlPtr + e) = lvl) ⊆
        (Finset.range size).image (fun p => mem (loc.arrPtr + p)) := by
      intro e he
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image] at he ⊢
      rcases hbij.2.2.2 e he.1 with h0 | ⟨hle, harr⟩
      · exact (he.2.1 h0).elim
      · exact ⟨mem (loc.posPtr + e) - 1, by omega, harr⟩
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))
  have hw1 : 1 < 2 ^ w := by omega
  have hhbw : loc.hb < 2 ^ w := hwords loc.hb (by simp)
  have hlvlw : lvl < 2 ^ w := hwords lvl (by simp)
  have hscw : scratch < 2 ^ w := hwords scratch (by simp)
  have hchW : loc.candHead < 2 ^ w := by omega
  let hd := mem (loc.candHead + lvl)
  have hhdW : hd < 2 ^ w := by
    cases hLc : lists lvl with
    | nil =>
      have : hd = 0 := by simpa [hd, hLc] using hL.2.2.1
      omega
    | cons e0 xs =>
      have hv : hd = e0 + 1 := by simpa [hd, hLc] using hL.2.2.1
      have he0 := hL.2.1 e0 (by simp [hLc])
      have := loc.endAddr_eq; unfold selectHeapSize shHdrSize at *; omega
  apply runs_start_le
  dsimp only [startState]
  unfold heapClearLevelBody
  simp only [shCandHeadOff]
  refine runs_seq_assign_flat (v := loc.candHead) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := hd) (by eval_expr) ?_
  by_cases hhd0 : hd = 0
  · have hLnil : lists lvl = [] := (hL.head_eq_zero_iff).mp hhd0
    have hcnt0 : levelCandCount mem loc lvl = 0 := by
      unfold levelCandCount
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro e he ⟨hnz, hl⟩
      have : e ∈ lists lvl := (hLiff e).mpr ⟨Finset.mem_range.mp he, hnz, hl⟩
      rw [hLnil] at this; simp at this
    refine WordRAM.runs_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, hhd0, hw1]) ?_ (fun h => absurd h (by decide))
    intro _
    refine WordRAM.runs_ret_le (v := scratch) (by eval_expr) ?_ ?_
    · dsimp only [heapClearLevelContract]
      simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ, hcnt0, hhdSize, Nat.sub_zero]
      exact ⟨le_rfl, Nat.le_add_right _ _, Nat.zero_le _, ⟨hhdr, hbij, hkeys, hord, ⟨lists, hlists⟩⟩,
        hz, fun e he hnz hl => by
          have : e ∈ lists lvl := (hLiff e).mpr ⟨he, hnz, hl⟩
          rw [hLnil] at this; simp at this,
        fun _ _ _ => ⟨trivial, trivial, trivial, trivial⟩, fun _ _ _ => trivial⟩
    · simp only [heapClearLevelContract, heapClearLevelCost, List.getD_cons_zero,
        List.getD_cons_succ, Expr.size]; omega
  · cases hLc : lists lvl with
    | nil =>
      have : hd = 0 := by simpa [hd, hLc] using hL.2.2.1
      exact (hhd0 this).elim
    | cons e0 xs =>
      have hv : hd = e0 + 1 := by simpa [hd, hLc] using hL.2.2.1
      obtain ⟨he0Cap, he0Pos, he0Lvl⟩ := (hLiff e0).mp (by simp [hLc])
      have hcntPos : 0 < levelCandCount mem loc lvl := by
        unfold levelCandCount
        exact Finset.card_pos.mpr ⟨e0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr he0Cap, he0Pos, he0Lvl⟩⟩
      have he0W : e0 < 2 ^ w := by omega
      have hspSplit : heapRebalanceSpace loc.cap loc.Lk +
          heapClearLevelSpace (levelCandCount mem loc lvl - 1) loc.cap loc.Lk =
          heapClearLevelSpace (levelCandCount mem loc lvl) loc.cap loc.Lk := by
        unfold heapClearLevelSpace
        have h1 : levelCandCount mem loc lvl = (levelCandCount mem loc lvl - 1) + 1 := by omega
        conv_rhs => rw [h1, Nat.add_mul, Nat.one_mul, Nat.add_comm]
      have hcostSplit : heapDeleteCost loc.cap loc.Lk + 60 +
          heapClearLevelCost (levelCandCount mem loc lvl - 1) loc.cap loc.Lk =
          heapClearLevelCost (levelCandCount mem loc lvl) loc.cap loc.Lk := by
        unfold heapClearLevelCost
        have h1 : levelCandCount mem loc lvl = (levelCandCount mem loc lvl - 1) + 1 := by omega
        conv_rhs => rw [h1, Nat.add_mul, Nat.one_mul]
        omega
      refine WordRAM.runs_cond_le (v := 0) (by simp [Expr.eval, BinOp.eval, hhd0, show 0 < 2 ^ w by omega])
        (fun h => absurd rfl h) ?_
      intro _
      refine runs_seq_assign_flat (v := e0) (by simp [Expr.eval, BinOp.eval, hv, hw1, he0W]) ?_
      refine runs_seq_call_flat (hdel size) (vs := [loc.hb, e0, scratch])
        (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨e0, scratch, rfl, hw16, hendLe, he0Cap, ⟨hhdr, hbij, hkeys, hord, ⟨lists, hlists⟩⟩,
          hz, by omega⟩
      · intro sc1 mem1 pos1 hp1
        obtain ⟨hlo1, hhi1, hat1, hz1, hpE0, hoth1, hfr1⟩ := hp1
        simp only [List.getD_cons_zero, List.getD_cons_succ, he0Pos, ↓reduceIte] at hlo1 hhi1 hat1 hpE0 hoth1 hfr1
        have hcnt1 : levelCandCount mem1 loc lvl = levelCandCount mem loc lvl - 1 := by
          unfold levelCandCount
          have heqF : (Finset.range loc.cap).filter (fun e => mem1 (loc.posPtr + e) ≠ 0 ∧ mem1 (loc.lvlPtr + e) = lvl) =
              ((Finset.range loc.cap).filter (fun e => mem (loc.posPtr + e) ≠ 0 ∧ mem (loc.lvlPtr + e) = lvl)).erase e0 := by
            ext e
            simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
            by_cases hee : e = e0
            · subst hee; simp [hpE0]
            · constructor
              · rintro ⟨heC, hnz, hl⟩
                exact ⟨hee, heC, (hoth1 e heC hee).1.mp hnz, (hoth1 e heC hee).2.1.symm.trans hl⟩
              · rintro ⟨_, heC, hnz, hl⟩
                exact ⟨heC, (hoth1 e heC hee).1.mpr hnz, (hoth1 e heC hee).2.1.trans hl⟩
          rw [heqF, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr he0Cap, he0Pos, he0Lvl⟩)]
        have hsc1W : sc1 < 2 ^ w := by omega
        have hhd1Size : mem1 loc.hb = size - 1 := by simpa using hat1.1 0 (by simp)
        refine runs_seq_call_flat ih (vs := [loc.hb, lvl, sc1]) (by eval_expr) (by wram_words) ?_ ?_
        · exact ⟨⟨lvl, sc1, size - 1, rfl, hw16, by omega, hlvlD, hat1, hz1, by rw [hcnt1]; omega⟩,
            by change levelCandCount mem1 loc lvl < levelCandCount mem loc lvl; omega⟩
        · intro ret mem2 pos2 hp2
          obtain ⟨hlo2, hhi2, hle2, hat2, hz2, hclr2, hkeep2, hfr2⟩ := hp2
          simp only [List.getD_cons_zero, List.getD_cons_succ, hcnt1, hhd1Size] at hlo2 hhi2 hle2 hat2 hclr2 hkeep2 hfr2
          have hretw : ret < 2 ^ w := by omega
          refine WordRAM.runs_ret_le (v := ret) (by eval_expr) ?_ ?_
          · dsimp only [heapClearLevelContract]
            simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ, hhdSize]
            have hszEq : size - 1 - (levelCandCount mem loc lvl - 1) = size - levelCandCount mem loc lvl := by omega
            rw [hszEq] at hat2
            refine ⟨by omega, by omega, hcntLeSize, hat2, hz2, ?_, ?_, ?_⟩
            · intro e he hnz hl
              by_cases hee : e = e0
              · subst e
                have hnot1 : ¬ (mem1 (loc.posPtr + e0) ≠ 0 ∧ mem1 (loc.lvlPtr + e0) = lvl) := by simp [hpE0]
                by_contra hnz2
                exact ((hkeep2 e0 he0Cap hnot1).1.mp hnz2) hpE0
              · exact hclr2 e he ((hoth1 e he hee).1.mpr hnz) ((hoth1 e he hee).2.1.trans hl)
            · intro e he hnot
              have hee : e ≠ e0 := fun h => hnot (h ▸ ⟨he0Pos, he0Lvl⟩)
              have hnot1 : ¬ (mem1 (loc.posPtr + e) ≠ 0 ∧ mem1 (loc.lvlPtr + e) = lvl) := by
                rintro ⟨hnz1, hl1⟩
                exact hnot ⟨(hoth1 e he hee).1.mp hnz1, (hoth1 e he hee).2.1.symm.trans hl1⟩
              obtain ⟨h1, h2, h3, h4⟩ := hkeep2 e he hnot1
              obtain ⟨g1, g2, g3, g4⟩ := hoth1 e he hee
              exact ⟨h1.trans g1, h2.trans g2, h3.trans g3, h4.trans g4⟩
            · intro a ha hout
              exact (hfr2 a (by omega) hout).trans (hfr1 a ha hout)
          · simp only [Contract.below, heapClearLevelContract, heapDeleteContract, List.getD_cons_zero,
              List.getD_cons_succ, hcnt1, Expr.size, argsSize]
            omega

/-- All 22 procedures in `selectHeapOpsModule b h` simultaneously satisfy their contracts from a
single `p.HasAt b (selectHeapOpsModule b h)` hypothesis. -/
theorem selectHeapOpsModule_meetsContracts {w h b : ℕ} {p : Program}
    (hh : 0 < h) (hw : 2 * h + 2 ≤ w) (hAt : p.HasAt b (selectHeapOpsModule b h))
    (loc : SelectHeapLoc) :
    MeetsContract w p (b + 0) (keyCompareContract w h) ∧
    MeetsContract w p (b + 12) (copyLimbsToContract w) ∧
    (∀ size lists, MeetsContract w p (b + 13) (candListConsContract w loc size lists)) ∧
    (∀ size lists, MeetsContract w p (b + 14) (candListEraseContract w loc size lists)) ∧
    (∀ size, MeetsContract w p (b + 15) (heapSiftUpContract w h loc size)) ∧
    (∀ size, MeetsContract w p (b + 16) (heapSiftDownContract w h loc size)) ∧
    (∀ size, MeetsContract w p (b + 17) (heapRebalanceContract w h loc size)) ∧
    (∀ size, MeetsContract w p (b + 18) (heapUpsertContract w h loc size)) ∧
    (∀ size, MeetsContract w p (b + 19) (heapDeleteContract w h loc size)) ∧
    (∀ size, MeetsContract w p (b + 20) (heapDeleteIfLevelContract w h loc size)) ∧
    MeetsContract w p (b + 21) (heapClearLevelContract w h loc) := by
  have hKC : p.HasAt b (keyCompareModule b h) := by
    intro i hi
    have hproc := hAt i (by simp [selectHeapOpsModule, keyCompareModule_length]; rw [keyCompareModule_length] at hi; omega)
    rw [hproc]; congr 1
    simp [selectHeapOpsModule, List.getElem_append_left hi]
  have hslot (k : ℕ) (hk : k < 10) :
      p.procs[b + (12 + k)]? = some
        (([copyLimbsToBody, candListConsBody, candListEraseBody,
           heapSiftUpBody (b + 15) b, heapSiftDownBody (b + 16) b,
           heapRebalanceBody b (b + 15) (b + 16),
           heapUpsertBody (b + 12) (b + 15) (b + 17) (b + 13) (b + 14),
           heapDeleteBody (b + 17) (b + 14),
           heapDeleteIfLevelBody (b + 19),
           heapClearLevelBody (b + 21) (b + 19)])[k]'(by simpa using hk)) := by
    have hproc := hAt (12 + k) (by rw [selectHeapOpsModule_length]; omega)
    rw [hproc]; congr 1
    unfold selectHeapOpsModule
    rw [List.getElem_append_right (by rw [keyCompareModule_length]; omega)]
    simp only [keyCompareModule_length, Nat.add_sub_cancel_left]
  have hcmp : MeetsContract w p b (keyCompareContract w h) := keyCompare_meetsContract hh hw hKC
  have hcp : MeetsContract w p (b + 12) (copyLimbsToContract w) := copyLimbsTo_meetsContract (hslot 0 (by omega))
  have hcons : ∀ size lists, MeetsContract w p (b + 13) (candListConsContract w loc size lists) :=
    fun size lists => candListCons_meetsContract (hslot 1 (by omega))
  have herase : ∀ size lists, MeetsContract w p (b + 14) (candListEraseContract w loc size lists) :=
    fun size lists => candListErase_meetsContract (hslot 2 (by omega))
  have hup : ∀ size, MeetsContract w p (b + 15) (heapSiftUpContract w h loc size) :=
    fun size => heapSiftUp_meetsContract (hslot 3 (by omega)) hcmp
  have hdown : ∀ size, MeetsContract w p (b + 16) (heapSiftDownContract w h loc size) :=
    fun size => heapSiftDown_meetsContract (hslot 4 (by omega)) hcmp
  have hrebal : ∀ size, MeetsContract w p (b + 17) (heapRebalanceContract w h loc size) :=
    fun size => heapRebalance_meetsContract (hslot 5 (by omega)) hcmp (hup size) (hdown size)
  have hups : ∀ size, MeetsContract w p (b + 18) (heapUpsertContract w h loc size) :=
    fun size => heapUpsert_meetsContract (hslot 6 (by omega)) hcp (hup (size + 1)) (hrebal size)
      hcons (herase size)
  have hdel : ∀ size, MeetsContract w p (b + 19) (heapDeleteContract w h loc size) :=
    fun size => heapDelete_meetsContract (hslot 7 (by omega)) (hrebal (size - 1)) (herase size)
  have hdelIf : ∀ size, MeetsContract w p (b + 20) (heapDeleteIfLevelContract w h loc size) :=
    fun size => heapDeleteIfLevel_meetsContract (hslot 8 (by omega)) (hdel size)
  have hclr : MeetsContract w p (b + 21) (heapClearLevelContract w h loc) :=
    heapClearLevel_meetsContract (hslot 9 (by omega)) hdel
  exact ⟨by simpa using hcmp, hcp, hcons, herase, hup, hdown, hrebal, hups, hdel, hdelIf, hclr⟩

end MinCostFlow.MinRatio
