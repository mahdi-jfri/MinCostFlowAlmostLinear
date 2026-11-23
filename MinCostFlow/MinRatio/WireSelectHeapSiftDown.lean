module

public import MinCostFlow.MinRatio.WireSelectHeapSiftUp
import WordRAM.Tactic
import Mathlib.Data.Nat.Log

/-!
# Word-RAM `siftDown` procedure for the indexed select-heap

Implements `heapSiftDownBody` (`args = [hb, k, scratch]`), which sifts heap position `k` downward
while `2 * k + 1 < size` and its better child beats `arr[k]` under `keyCompareContract`:
- Scratch space: at most `(Nat.log 2 size - Nat.log 2 (k + 1)) * (2 * keyCompareSpace Lk)` words.
- Time cost: at most `(Nat.log 2 size - Nat.log 2 (k + 1)) * (2 * keyCompareCost Lk + 240) + 60`
  steps.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num

/-! ## 1. `heapSiftDown`: recursive downward sifting -/

/-- Recursive `siftDown` body with arguments `[hb, k, scratch]`. Calls `cmp` (`keyCompareContract`)
and recurses via `self`. -/
def heapSiftDownBody (self cmp : ℕ) : Stmt :=
  .assign 3 (.load (.reg 0)) ;;
  .assign 4 (.bin .add (.bin .mul (.const 2) (.reg 1)) (.const 1)) ;;
  .cond (.bin .lt (.reg 4) (.reg 3))
    (.assign 5 (.load (.bin .add (.reg 0) (.const shLkOff))) ;;
     .assign 6 (.load (.bin .add (.reg 0) (.const shArrOff))) ;;
     .assign 7 (.load (.bin .add (.reg 0) (.const shPosOff))) ;;
     .assign 8 (.load (.bin .add (.reg 0) (.const shNumOff))) ;;
     .assign 9 (.load (.bin .add (.reg 0) (.const shDenOff))) ;;
     .assign 10 (.reg 4) ;;
     .assign 11 (.reg 2) ;;
     .assign 12 (.bin .add (.reg 4) (.const 1)) ;;
     .cond (.bin .lt (.reg 12) (.reg 3))
       (.assign 13 (.load (.bin .add (.reg 6) (.reg 12))) ;;
        .assign 14 (.load (.bin .add (.reg 6) (.reg 4))) ;;
        .call 15 cmp
          [.reg 13,
           .bin .add (.reg 8) (.bin .mul (.reg 13) (.reg 5)),
           .bin .add (.reg 9) (.bin .mul (.reg 13) (.reg 5)),
           .reg 14,
           .bin .add (.reg 8) (.bin .mul (.reg 14) (.reg 5)),
           .bin .add (.reg 9) (.bin .mul (.reg 14) (.reg 5)),
           .reg 5, .reg 11] ;;
        .assign 11 (.bin .add (.reg 11) (.bin .mul (.const 16) (.reg 5))) ;;
        .cond (.reg 15) (.assign 10 (.reg 12)) .nop)
       .nop ;;
     .assign 16 (.load (.bin .add (.reg 6) (.reg 10))) ;;
     .assign 17 (.load (.bin .add (.reg 6) (.reg 1))) ;;
     .call 18 cmp
       [.reg 16,
        .bin .add (.reg 8) (.bin .mul (.reg 16) (.reg 5)),
        .bin .add (.reg 9) (.bin .mul (.reg 16) (.reg 5)),
        .reg 17,
        .bin .add (.reg 8) (.bin .mul (.reg 17) (.reg 5)),
        .bin .add (.reg 9) (.bin .mul (.reg 17) (.reg 5)),
        .reg 5, .reg 11] ;;
     .assign 11 (.bin .add (.reg 11) (.bin .mul (.const 16) (.reg 5))) ;;
     .cond (.reg 18)
       (.store (.bin .add (.reg 6) (.reg 1)) (.reg 16) ;;
        .store (.bin .add (.reg 6) (.reg 10)) (.reg 17) ;;
        .store (.bin .add (.reg 7) (.reg 16)) (.bin .add (.reg 1) (.const 1)) ;;
        .store (.bin .add (.reg 7) (.reg 17)) (.bin .add (.reg 10) (.const 1)) ;;
        .call 19 self [.reg 0, .reg 10, .reg 11] ;;
        .ret (.reg 19))
       (.ret (.reg 11)))
    (.ret (.reg 2))

theorem heapSiftDownBody_noRand (self cmp : ℕ) : (heapSiftDownBody self cmp).NoRand := by
  simp [heapSiftDownBody, Stmt.NoRand]

/-- Depth bound for `siftDown` from index `k` in a heap of size `size`. -/
def heapSiftDownDepth (size k : ℕ) : ℕ :=
  Nat.log 2 size - Nat.log 2 (k + 1)

/-- Scratch space reserved by `heapSiftDownBody` from index `k` in a heap of size `size`. -/
def heapSiftDownSpace (size k Lk : ℕ) : ℕ :=
  heapSiftDownDepth size k * (2 * keyCompareSpace Lk)

/-- Step cost bound for `heapSiftDownBody` from index `k` in a heap of size `size`. -/
def heapSiftDownCost (size k Lk : ℕ) : ℕ :=
  heapSiftDownDepth size k * (2 * keyCompareCost Lk + 240) + 60

/-- Contract for `heapSiftDownBody` on a fixed heap block `loc` of size `size`. -/
def heapSiftDownContract (w h : ℕ) (loc : SelectHeapLoc) (size : ℕ) : Contract where
  pre args mem :=
    ∃ k scratch, args = [loc.hb, k, scratch] ∧
      16 < 2 ^ w ∧
      loc.endAddr ≤ scratch ∧
      SelectHeapHeaderAt mem loc size ∧
      SelectHeapBijection mem loc size ∧
      SelectHeapKeysValid mem loc h ∧
      SelectHeapCandLists mem loc ∧
      SelectHeapOrderExceptDown mem loc h size k ∧
      ZeroFrom mem scratch ∧
      scratch + heapSiftDownSpace size k loc.Lk < 2 ^ w
  post args mem ret mem' :=
    let k := args.getD 1 0
    let scratch := args.getD 2 0
    scratch ≤ ret ∧ ret ≤ scratch + heapSiftDownSpace size k loc.Lk ∧
    SelectHeapAt mem' loc h size ∧
    ZeroFrom mem' ret ∧
    (∀ a < scratch, (a < loc.arrPtr ∨ loc.lvlPtr ≤ a) → mem' a = mem a) ∧
    (∀ e < loc.cap, mem' (loc.posPtr + e) ≠ 0 ↔ mem (loc.posPtr + e) ≠ 0)
  cost args _ := heapSiftDownCost size (args.getD 1 0) loc.Lk

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num

private lemma log2_child_add_one {size k best : ℕ}
    (hbest_ge : 2 * k + 1 ≤ best) (hbest_lt : best < size) :
    heapSiftDownDepth size best + 1 ≤ heapSiftDownDepth size k := by
  unfold heapSiftDownDepth
  have hmul : 2 * (k + 1) ≤ best + 1 := by omega
  have hlog1 : Nat.log 2 (k + 1) + 1 = Nat.log 2 (2 * (k + 1)) := by
    rw [mul_comm, Nat.log_mul_base (by decide) (by omega)]
  have hlog2 : Nat.log 2 (2 * (k + 1)) ≤ Nat.log 2 (best + 1) := Nat.log_mono_right hmul
  have hlog3 : Nat.log 2 (best + 1) ≤ Nat.log 2 size := Nat.log_mono_right (by omega)
  omega

private lemma exceptDown_of_agree_lt {mem mem1 : ℕ → ℕ} {loc : SelectHeapLoc}
    {h size k scratch : ℕ} (hendLe : loc.endAddr ≤ scratch)
    (hf1 : ∀ x < scratch, mem1 x = mem x)
    (hbij : SelectHeapBijection mem loc size)
    (hedgeEq : ∀ e₁ e₂, e₁ < loc.cap → e₂ < loc.cap →
      loc.edgeBetter mem1 h e₁ e₂ = loc.edgeBetter mem h e₁ e₂)
    (hexc : SelectHeapOrderExceptDown mem loc h size k) :
    SelectHeapOrderExceptDown mem1 loc h size k := by
  have harr_lt (p : ℕ) (hp : p < loc.cap) : loc.arrPtr + p < scratch := by
    rw [loc.endAddr_eq] at hendLe; unfold SelectHeapLoc.arrPtr selectHeapSize shHdrSize at *; omega
  refine ⟨hexc.1, fun p hp0 hp hpp => ?_, fun hk0 c hc hck => ?_⟩
  · have := hbij.1
    rw [hf1 _ (harr_lt _ (by omega)), hf1 _ (harr_lt p (by omega)),
        hedgeEq _ _ (hbij.2.1 _ (by omega)) (hbij.2.1 p hp)]
    exact hexc.2.1 p hp0 hp hpp
  · have := hbij.1
    rw [hf1 _ (harr_lt _ (by omega)), hf1 _ (harr_lt c (by omega)),
        hedgeEq _ _ (hbij.2.1 _ (by omega)) (hbij.2.1 c hc)]
    exact hexc.2.2 hk0 c hc hck

/-! ## 2. Verification of `heapSiftDownBody` -/

/-- `heapSiftDownBody` meets `heapSiftDownContract` in `O(log(size + 1) · Lk^2)` time and
`O(log(size + 1) · Lk)` scratch space. -/
theorem heapSiftDown_meetsContract {w h self cmp : ℕ} {loc : SelectHeapLoc} {size : ℕ}
    {p : Program}
    (hp : p.procs[self]? = some (heapSiftDownBody self cmp))
    (hcmp : MeetsContract w p cmp (keyCompareContract w h)) :
    MeetsContract w p self (heapSiftDownContract w h loc size) := by
  apply meetsContract_of_rec (fun args _ => size - args.getD 1 0) hp
  intro mMeasure ih args mem pos ω hwords hpre hmEq
  obtain ⟨k, scratch, rfl, hw16, hendLe, hhdr, hbij, hkeys, hcand, hexc, hz, hroom⟩ := hpre
  change size - k = mMeasure at hmEq
  subst hmEq
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hhbw : loc.hb < 2 ^ w := hwords loc.hb (by simp)
  have hkw : k < 2 ^ w := hwords k (by simp)
  have hscw : scratch < 2 ^ w := hwords scratch (by simp)
  have hhdrR := selectHeap_header_reads hhdr
  have hsizeCap := hbij.1
  have hsizeW : size < 2 ^ w := by
    rw [loc.endAddr_eq] at hendLe; unfold selectHeapSize shHdrSize at hendLe; omega
  have hleftW : 2 * k + 1 < 2 ^ w := by
    have hk_lt : k < size := hexc.1
    rw [loc.endAddr_eq] at hendLe; unfold selectHeapSize shHdrSize at hendLe; omega
  apply runs_start_le
  dsimp only [startState]
  unfold heapSiftDownBody
  simp only [shLkOff, shArrOff, shPosOff, shNumOff, shDenOff]
  refine runs_seq_assign_flat (v := size) (by eval_expr; exact hhdrR.1) ?_
  refine runs_seq_assign_flat (v := 2 * k + 1) (by eval_expr) ?_
  by_cases hhasLeft : 2 * k + 1 < size
  · let left := 2 * k + 1
    let right := left + 1
    have hdepthStep : heapSiftDownDepth size left + 1 ≤ heapSiftDownDepth size k :=
      log2_child_add_one (by omega) hhasLeft
    have hspStep : 2 * keyCompareSpace loc.Lk + heapSiftDownSpace size left loc.Lk ≤
        heapSiftDownSpace size k loc.Lk := by
      unfold heapSiftDownSpace
      have hmul := Nat.mul_le_mul_right (2 * keyCompareSpace loc.Lk) hdepthStep
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm] at hmul; exact hmul
    have hcostStep : 2 * keyCompareCost loc.Lk + 240 + heapSiftDownCost size left loc.Lk ≤
        heapSiftDownCost size k loc.Lk := by
      unfold heapSiftDownCost
      have hmul := Nat.mul_le_mul_right (2 * keyCompareCost loc.Lk + 240) hdepthStep
      rw [Nat.add_mul, Nat.one_mul] at hmul; omega
    have hhdrLt : loc.hb + 14 ≤ loc.endAddr := by
      rw [loc.endAddr_eq]; unfold selectHeapSize shHdrSize; omega
    have h16Lkw : 16 * loc.Lk < 2 ^ w := by unfold keyCompareSpace at hspStep; omega
    have hLkw : loc.Lk < 2 ^ w := by omega
    have hrightW : right < 2 ^ w := by dsimp only [right, left]; omega
    have harrW : loc.arrPtr < 2 ^ w := by
      rw [loc.endAddr_eq] at hendLe; unfold SelectHeapLoc.arrPtr selectHeapSize shHdrSize at *; omega
    have hposW : loc.posPtr < 2 ^ w := by
      rw [loc.endAddr_eq] at hendLe; unfold SelectHeapLoc.posPtr SelectHeapLoc.arrPtr selectHeapSize shHdrSize at *; omega
    have hnumW : loc.numBase < 2 ^ w := by
      rw [loc.endAddr_eq] at hendLe; unfold SelectHeapLoc.numBase SelectHeapLoc.candNext
        SelectHeapLoc.candPrev SelectHeapLoc.candHead SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr
        SelectHeapLoc.arrPtr selectHeapSize shHdrSize at *; omega
    have hdenW : loc.denBase < 2 ^ w := by
      rw [loc.endAddr_eq] at hendLe; unfold SelectHeapLoc.denBase SelectHeapLoc.numBase
        SelectHeapLoc.candNext SelectHeapLoc.candPrev SelectHeapLoc.candHead SelectHeapLoc.lvlPtr
        SelectHeapLoc.posPtr SelectHeapLoc.arrPtr selectHeapSize shHdrSize at *; omega
    refine runs_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, hhasLeft, hw1]) ?_ (fun h => absurd h (by decide))
    intro _
    refine runs_seq_assign_flat (v := loc.Lk) (by eval_expr; exact hhdrR.2.1) ?_
    refine runs_seq_assign_flat (v := loc.arrPtr) (by eval_expr; exact hhdrR.2.2.1) ?_
    refine runs_seq_assign_flat (v := loc.posPtr) (by eval_expr; exact hhdrR.2.2.2.1) ?_
    refine runs_seq_assign_flat (v := loc.numBase) (by eval_expr; exact hhdrR.2.2.2.2.1) ?_
    refine runs_seq_assign_flat (v := loc.denBase) (by eval_expr; exact hhdrR.2.2.2.2.2) ?_
    refine runs_seq_assign_flat (v := left) (by eval_expr) ?_
    refine runs_seq_assign_flat (v := scratch) (by eval_expr) ?_
    refine runs_seq_assign_flat (v := right) (by eval_expr) ?_
    -- Shared continuation after selecting `best ∈ {left, right}` and advancing scratch to `sc1`
    have hcont : ∀ (best sc1 : ℕ) (memMid regsMid : ℕ → ℕ) (posMid : ℕ),
        regsMid 0 = loc.hb → regsMid 1 = k → regsMid 5 = loc.Lk →
        regsMid 6 = loc.arrPtr → regsMid 7 = loc.posPtr →
        regsMid 8 = loc.numBase → regsMid 9 = loc.denBase →
        regsMid 10 = best → regsMid 11 = sc1 →
        (best = left ∨ best = right) → best < size →
        (∀ c, 0 < c → c < size → (c - 1) / 2 = k → c ≠ best →
          loc.edgeBetter mem h (mem (loc.arrPtr + best)) (mem (loc.arrPtr + c)) = true) →
        scratch ≤ sc1 → sc1 ≤ scratch + 16 * loc.Lk →
        (∀ x < scratch, memMid x = mem x) →
        ZeroFrom memMid sc1 →
        ∃ ret out c,
          Runs w p ω
            (.assign 16 (.load (.bin .add (.reg 6) (.reg 10))) ;;
             .assign 17 (.load (.bin .add (.reg 6) (.reg 1))) ;;
             .call 18 cmp
               [.reg 16,
                .bin .add (.reg 8) (.bin .mul (.reg 16) (.reg 5)),
                .bin .add (.reg 9) (.bin .mul (.reg 16) (.reg 5)),
                .reg 17,
                .bin .add (.reg 8) (.bin .mul (.reg 17) (.reg 5)),
                .bin .add (.reg 9) (.bin .mul (.reg 17) (.reg 5)),
                .reg 5, .reg 11] ;;
             .assign 11 (.bin .add (.reg 11) (.bin .mul (.const 16) (.reg 5))) ;;
             .cond (.reg 18)
               (.store (.bin .add (.reg 6) (.reg 1)) (.reg 16) ;;
                .store (.bin .add (.reg 6) (.reg 10)) (.reg 17) ;;
                .store (.bin .add (.reg 7) (.reg 16)) (.bin .add (.reg 1) (.const 1)) ;;
                .store (.bin .add (.reg 7) (.reg 17)) (.bin .add (.reg 10) (.const 1)) ;;
                .call 19 self [.reg 0, .reg 10, .reg 11] ;;
                .ret (.reg 19))
               (.ret (.reg 11)))
            ⟨memMid, regsMid, posMid⟩ (.returned ret) out c ∧
          c ≤ keyCompareCost loc.Lk + heapSiftDownCost size best loc.Lk + 100 ∧
          scratch ≤ ret ∧ ret ≤ scratch + heapSiftDownSpace size k loc.Lk ∧
          SelectHeapAt out.mem loc h size ∧ ZeroFrom out.mem ret ∧
          (∀ a < scratch, (a < loc.arrPtr ∨ loc.lvlPtr ≤ a) → out.mem a = mem a) ∧
          (∀ e < loc.cap, out.mem (loc.posPtr + e) ≠ 0 ↔ mem (loc.posPtr + e) ≠ 0) := by
      intro best sc1 memMid regsMid posMid hr0 hr1 hr5 hr6 hr7 hr8 hr9 hr10 hr11
        hbestOr hbestLt hbeatSib hsc1Lo hsc1Hi hfrMid hzMid
      have hbest0 : 0 < best := by rcases hbestOr with rfl | rfl <;> omega
      have hbestPar : (best - 1) / 2 = k := by rcases hbestOr with rfl | rfl <;> omega
      have hbestGe : 2 * k + 1 ≤ best := by rcases hbestOr with rfl | rfl <;> omega
      have hdepthB : heapSiftDownDepth size best + 1 ≤ heapSiftDownDepth size k :=
        log2_child_add_one hbestGe hbestLt
      have hspB : 2 * keyCompareSpace loc.Lk + heapSiftDownSpace size best loc.Lk ≤
          heapSiftDownSpace size k loc.Lk := by
        unfold heapSiftDownSpace
        have hmul := Nat.mul_le_mul_right (2 * keyCompareSpace loc.Lk) hdepthB
        rw [Nat.add_mul, Nat.one_mul, Nat.add_comm] at hmul; exact hmul
      have hbestCap : best < loc.cap := lt_of_lt_of_le hbestLt hsizeCap
      have hkCap : k < loc.cap := lt_of_lt_of_le hexc.1 hsizeCap
      have hebCap := hbij.2.1 best hbestLt
      have hekCap := hbij.2.1 k hexc.1
      have hbdB := selectHeap_slot_bounds hebCap
      have hbdK := selectHeap_slot_bounds hekCap
      obtain ⟨hhdrM, hbijM, hkeysM, hcandM, hedgeMid⟩ :=
        selectHeap_struct_of_agree_lt hendLe hfrMid hhdr hbij hkeys hcand
      have hebM : memMid (loc.arrPtr + best) = mem (loc.arrPtr + best) := hfrMid _ (by omega)
      have hekM : memMid (loc.arrPtr + k) = mem (loc.arrPtr + k) := hfrMid _ (by omega)
      have hkeyB := hkeysM _ hebCap (by rw [← hebM]; exact hbijM.pos_arr_ne_zero hbestLt)
      have hkeyK := hkeysM _ hekCap (by rw [← hekM]; exact hbijM.pos_arr_ne_zero hexc.1)
      have hsc1w : sc1 < 2 ^ w := by unfold keyCompareSpace at hspB; omega
      have hsc2w : sc1 + 16 * loc.Lk < 2 ^ w := by unfold keyCompareSpace at hspB; omega
      have hbestw : best < 2 ^ w := by omega
      have hebw : mem (loc.arrPtr + best) < 2 ^ w := by omega
      have hekw : mem (loc.arrPtr + k) < 2 ^ w := by omega
      have hnbw : loc.numBase + mem (loc.arrPtr + best) * loc.Lk < 2 ^ w := by omega
      have hdbw : loc.denBase + mem (loc.arrPtr + best) * loc.Lk < 2 ^ w := by omega
      have hnkw : loc.numBase + mem (loc.arrPtr + k) * loc.Lk < 2 ^ w := by omega
      have hdkw : loc.denBase + mem (loc.arrPtr + k) * loc.Lk < 2 ^ w := by omega
      -- Establish the existential via `runs_start_le` with predicate `Q`
      suffices hQ : ∃ o st' c,
          Runs w p ω
            (.assign 16 (.load (.bin .add (.reg 6) (.reg 10))) ;;
             .assign 17 (.load (.bin .add (.reg 6) (.reg 1))) ;;
             .call 18 cmp
               [.reg 16,
                .bin .add (.reg 8) (.bin .mul (.reg 16) (.reg 5)),
                .bin .add (.reg 9) (.bin .mul (.reg 16) (.reg 5)),
                .reg 17,
                .bin .add (.reg 8) (.bin .mul (.reg 17) (.reg 5)),
                .bin .add (.reg 9) (.bin .mul (.reg 17) (.reg 5)),
                .reg 5, .reg 11] ;;
             .assign 11 (.bin .add (.reg 11) (.bin .mul (.const 16) (.reg 5))) ;;
             .cond (.reg 18)
               (.store (.bin .add (.reg 6) (.reg 1)) (.reg 16) ;;
                .store (.bin .add (.reg 6) (.reg 10)) (.reg 17) ;;
                .store (.bin .add (.reg 7) (.reg 16)) (.bin .add (.reg 1) (.const 1)) ;;
                .store (.bin .add (.reg 7) (.reg 17)) (.bin .add (.reg 10) (.const 1)) ;;
                .call 19 self [.reg 0, .reg 10, .reg 11] ;;
                .ret (.reg 19))
               (.ret (.reg 11)))
            ⟨memMid, regsMid, posMid⟩ o st' c ∧
          (∃ ret, o = .returned ret ∧
            scratch ≤ ret ∧ ret ≤ scratch + heapSiftDownSpace size k loc.Lk ∧
            SelectHeapAt st'.mem loc h size ∧ ZeroFrom st'.mem ret ∧
            (∀ a < scratch, (a < loc.arrPtr ∨ loc.lvlPtr ≤ a) → st'.mem a = mem a) ∧
            (∀ e < loc.cap, st'.mem (loc.posPtr + e) ≠ 0 ↔ mem (loc.posPtr + e) ≠ 0)) ∧
          0 + c ≤ keyCompareCost loc.Lk + heapSiftDownCost size best loc.Lk + 100 by
        obtain ⟨o, st', c, hrun, ⟨ret, rfl, hpost⟩, hc⟩ := hQ
        exact ⟨ret, st', c, hrun, by omega, hpost⟩
      refine runs_seq_assign_flat (v := mem (loc.arrPtr + best))
        (by simp [Expr.eval, BinOp.eval, hr6, hr10, show loc.arrPtr + best < 2 ^ w by omega, hebM]) ?_
      refine runs_seq_assign_flat (v := mem (loc.arrPtr + k))
        (by simp [Expr.eval, BinOp.eval, hr6, hr1, show loc.arrPtr + k < 2 ^ w by omega, hekM]) ?_
      refine runs_seq_call_flat hcmp
        (vs := [mem (loc.arrPtr + best), loc.numBase + mem (loc.arrPtr + best) * loc.Lk,
                loc.denBase + mem (loc.arrPtr + best) * loc.Lk,
                mem (loc.arrPtr + k), loc.numBase + mem (loc.arrPtr + k) * loc.Lk,
                loc.denBase + mem (loc.arrPtr + k) * loc.Lk, loc.Lk, sc1])
        (by simp [evalArgs, Expr.eval, BinOp.eval, hr5, hr8, hr9, hr11, hnbw, hdbw, hnkw, hdkw,
          show mem (loc.arrPtr + best) * loc.Lk < 2 ^ w by omega,
          show mem (loc.arrPtr + k) * loc.Lk < 2 ^ w by omega])
        (by wram_words) ?_ ?_
      · exact ⟨_, _, _, _, _, _, loc.Lk, sc1, rfl, by omega, by omega, by omega, by omega,
          hkeyB.2.1, hkeyB.2.2.1, hkeyK.2.1, hkeyK.2.2.1, hzMid,
          by unfold keyCompareSpace at hspB ⊢; omega⟩
      · intro bit2 mem2 pos2 hpCmp2
        obtain ⟨hbit2, hf2, hz2⟩ := hpCmp2
        change bit2 = (if loc.edgeBetter memMid h (mem (loc.arrPtr + best)) (mem (loc.arrPtr + k))
          then 1 else 0) at hbit2
        change (∀ x < sc1, mem2 x = memMid x) at hf2
        change ZeroFrom mem2 (sc1 + 16 * loc.Lk) at hz2
        have hf20 : ∀ x < scratch, mem2 x = mem x := fun x hx =>
          (hf2 x (lt_of_lt_of_le hx hsc1Lo)).trans (hfrMid x hx)
        have hbit2w : bit2 < 2 ^ w := by rw [hbit2]; split <;> omega
        obtain ⟨hhdr2, hbij2, hkeys2, hcand2, hedge2⟩ :=
          selectHeap_struct_of_agree_lt hendLe hf20 hhdr hbij hkeys hcand
        have hexc2 := exceptDown_of_agree_lt hendLe hf20 hbij hedge2 hexc
        rw [hedgeMid _ _ hebCap hekCap] at hbit2
        refine runs_seq_assign_flat (v := sc1 + 16 * loc.Lk)
          (by simp [Expr.eval, BinOp.eval, hr5, hr11, hw16, h16Lkw, hsc2w]) ?_
        refine runs_cond_le (v := bit2) (by eval_expr) ?_ ?_
        · intro hnz2
          have hbeatK : loc.edgeBetter mem h (mem (loc.arrPtr + best)) (mem (loc.arrPtr + k)) = true := by
            by_contra hnot; rw [Bool.eq_false_iff.mpr hnot] at hbit2; exact hnz2 hbit2
          have hbeatK2 : loc.edgeBetter mem2 h (mem2 (loc.arrPtr + best)) (mem2 (loc.arrPtr + k)) = true := by
            rw [hf20 _ (by omega), hf20 _ (by omega), hedge2 _ _ hebCap hekCap]; exact hbeatK
          have hbeatSib2 : ∀ c, c < size → (c - 1) / 2 = k → c ≠ best →
              loc.edgeBetter mem2 h (mem2 (loc.arrPtr + best)) (mem2 (loc.arrPtr + c)) = true := by
            intro c hc hcp hcb
            by_cases hc0 : c = 0
            · have hck : c = k := by omega
              subst hck; exact hbeatK2
            · rw [hf20 _ (by omega), hf20 _ (by omega), hedge2 _ _ hebCap (hbij.2.1 c hc)]
              exact hbeatSib c (Nat.pos_of_ne_zero hc0) hc hcp hcb
          have hne : k ≠ best := by omega
          refine runs_seq_store_flat (x := loc.arrPtr + k) (v := mem (loc.arrPtr + best))
            (by simp [Expr.eval, BinOp.eval, hr6, hr1, show loc.arrPtr + k < 2 ^ w by omega])
            (by eval_expr) ?_
          refine runs_seq_store_flat (x := loc.arrPtr + best) (v := mem (loc.arrPtr + k))
            (by simp [Expr.eval, BinOp.eval, hr6, hr10, show loc.arrPtr + best < 2 ^ w by omega])
            (by eval_expr) ?_
          refine runs_seq_store_flat (x := loc.posPtr + mem (loc.arrPtr + best)) (v := k + 1)
            (by simp [Expr.eval, BinOp.eval, hr7, show loc.posPtr + mem (loc.arrPtr + best) < 2 ^ w by omega])
            (by simp [Expr.eval, BinOp.eval, hr1, hw1, show k + 1 < 2 ^ w by omega]) ?_
          refine runs_seq_store_flat (x := loc.posPtr + mem (loc.arrPtr + k)) (v := best + 1)
            (by simp [Expr.eval, BinOp.eval, hr7, show loc.posPtr + mem (loc.arrPtr + k) < 2 ^ w by omega])
            (by simp [Expr.eval, BinOp.eval, hr10, hw1, show best + 1 < 2 ^ w by omega]) ?_
          have hmEq : Function.update
              (Function.update
                (Function.update
                  (Function.update mem2 (loc.arrPtr + k) (mem (loc.arrPtr + best)))
                  (loc.arrPtr + best) (mem (loc.arrPtr + k)))
                (loc.posPtr + mem (loc.arrPtr + best)) (k + 1))
              (loc.posPtr + mem (loc.arrPtr + k)) (best + 1) =
              heapSwapMem mem2 loc k best := by
            unfold heapSwapMem
            rw [hf20 (loc.arrPtr + k) (by omega), hf20 (loc.arrPtr + best) (by omega)]
          have hstruct3 := heapSwapMem_preserves_struct hhdr2 hbij2 hkeys2 hcand2 hexc.1 hbestLt hne
          have hexc3 := siftDown_swap_step hbij2 hexc2 hbest0 hbestLt hbestPar hbeatK2 hbeatSib2
          have hout3 (a : ℕ) (ha : a < loc.arrPtr ∨ loc.lvlPtr ≤ a) :
              heapSwapMem mem2 loc k best a = mem2 a :=
            heapSwapMem_eq_of_outside hkCap hbestCap (by rw [hf20 _ (by omega)]; exact hekCap)
              (by rw [hf20 _ (by omega)]; exact hebCap) ha
          have hz3 : ZeroFrom (heapSwapMem mem2 loc k best) (sc1 + 16 * loc.Lk) := fun a ha => by
            rw [hout3 a (Or.inr (by
              rw [loc.endAddr_eq] at hendLe
              unfold SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr SelectHeapLoc.arrPtr
                selectHeapSize shHdrSize at *; omega))]
            exact hz2 a ha
          refine runs_seq_call_flat ih (vs := [loc.hb, best, sc1 + 16 * loc.Lk])
            (by simp [evalArgs, Expr.eval, hr0, hr10]) (by wram_words) ?_ ?_
          · rw [hmEq]
            exact ⟨⟨best, sc1 + 16 * loc.Lk, rfl, hw16, by omega,
              hstruct3.1, hstruct3.2.1, hstruct3.2.2.1, hstruct3.2.2.2, hexc3, hz3,
              by unfold keyCompareSpace at hspB; omega⟩,
              by simp only [List.getD_cons_zero, List.getD_cons_succ]; omega⟩
          · intro ret mem4 pos4 hpostRec
            obtain ⟨hlo4, hhi4, hat4, hz4, hfr4, hpos4⟩ := hpostRec
            simp only [List.getD_cons_zero, List.getD_cons_succ] at hlo4 hhi4 hfr4 hpos4
            have hretw : ret < 2 ^ w := by unfold keyCompareSpace at hspB; omega
            refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
            · refine ⟨ret, rfl, by omega, by unfold keyCompareSpace at hspB; omega, hat4, hz4, ?_, ?_⟩
              · intro a ha hout
                exact (hfr4 a (by omega) hout).trans (by rw [hmEq, hout3 a hout, hf20 a ha])
              · intro e he
                rw [hpos4 e he, hmEq, heapSwapMem_pos hbij2 hexc.1 hbestLt he hne]
                rw [hf20 (loc.arrPtr + k) (by omega), hf20 (loc.arrPtr + best) (by omega),
                    hf20 (loc.posPtr + e) (by omega)]
                split_ifs with h1 h2
                · subst h1; simp [hbij.pos_arr_ne_zero hexc.1]
                · subst h2; simp [hbij.pos_arr_ne_zero hbestLt]
                · rfl
            · simp only [Contract.below, heapSiftDownContract, keyCompareContract, List.getD_cons_zero,
                List.getD_cons_succ, Expr.size, argsSize]
              omega
        · intro hz2b
          have hfalseK : loc.edgeBetter mem h (mem (loc.arrPtr + best)) (mem (loc.arrPtr + k)) = false := by
            by_contra hnot; rw [Bool.eq_true_of_not_eq_false hnot] at hbit2; simp only [↓reduceIte] at hbit2; omega
          have hstop : ∀ c, c < size → (c - 1) / 2 = k →
              loc.edgeBetter mem2 h (mem2 (loc.arrPtr + c)) (mem2 (loc.arrPtr + k)) = false := by
            intro c hc hcp
            rw [hf20 _ (by omega), hf20 _ (by omega), hedge2 _ _ (hbij.2.1 c hc) hekCap]
            by_cases hc0 : c = 0
            · have hck : c = k := by omega
              subst hck; exact keyBetter_irrefl _ _ _
            · by_cases hcb : c = best
              · subst hcb; exact hfalseK
              · have hsib := hbeatSib c (Nat.pos_of_ne_zero hc0) hc hcp hcb
                have hneBK : mem (loc.arrPtr + best) ≠ mem (loc.arrPtr + k) := fun h => by
                  have := hbij.arr_inj hbestLt hexc.1 h; omega
                have hkBeatB : loc.edgeBetter mem h (mem (loc.arrPtr + k)) (mem (loc.arrPtr + best)) = true := by
                  rcases keyBetter_total_of_ne (n₁ := loc.readNum mem h (mem (loc.arrPtr + k)))
                      (d₁ := loc.readDen mem h (mem (loc.arrPtr + k)))
                      (n₂ := loc.readNum mem h (mem (loc.arrPtr + best)))
                      (d₂ := loc.readDen mem h (mem (loc.arrPtr + best))) hneBK.symm with h1 | h2
                  · exact h1
                  · change loc.edgeBetter mem h (mem (loc.arrPtr + best)) (mem (loc.arrPtr + k)) = true at h2
                    rw [hfalseK] at h2; cases h2
                have hdK := (hkeys _ hekCap (hbij.pos_arr_ne_zero hexc.1)).2.2.2
                have hdB := (hkeys _ hebCap (hbij.pos_arr_ne_zero hbestLt)).2.2.2
                have hdC := (hkeys _ (hbij.2.1 c hc) (hbij.pos_arr_ne_zero hc)).2.2.2
                exact keyBetter_asymm (keyBetter_trans_pos hdK hdB hdC hkBeatB hsib)
          refine runs_ret_le (v := sc1 + 16 * loc.Lk) (by eval_expr) ?_ ?_
          · refine ⟨sc1 + 16 * loc.Lk, rfl, by omega, by unfold keyCompareSpace at hspB; omega,
              ⟨hhdr2, hbij2, hkeys2, selectHeapOrder_of_exceptDown_stop hbij2 hexc2 hstop, hcand2⟩,
              hz2, fun a ha _ => hf20 a ha, fun e he => by dsimp only; rw [hf20 _ (by omega)]⟩
          · simp only [keyCompareContract, List.getD_cons_zero,
              List.getD_cons_succ, Expr.size, argsSize]
            omega
    -- Branch on whether `right < size`
    by_cases hhasRight : right < size
    · have herCap := hbij.2.1 right hhasRight
      have helCap := hbij.2.1 left hhasLeft
      have hbdR := selectHeap_slot_bounds herCap
      have hbdL := selectHeap_slot_bounds helCap
      have hkeyR := hkeys _ herCap (hbij.pos_arr_ne_zero hhasRight)
      have hkeyL := hkeys _ helCap (hbij.pos_arr_ne_zero hhasLeft)
      have herw : mem (loc.arrPtr + right) < 2 ^ w := by omega
      have helw : mem (loc.arrPtr + left) < 2 ^ w := by omega
      have hnrw : loc.numBase + mem (loc.arrPtr + right) * loc.Lk < 2 ^ w := by omega
      have hdrw : loc.denBase + mem (loc.arrPtr + right) * loc.Lk < 2 ^ w := by omega
      have hnlw : loc.numBase + mem (loc.arrPtr + left) * loc.Lk < 2 ^ w := by omega
      have hdlw : loc.denBase + mem (loc.arrPtr + left) * loc.Lk < 2 ^ w := by omega
      have hsc1w : scratch + 16 * loc.Lk < 2 ^ w := by unfold keyCompareSpace at hspStep; omega
      have hdepthR : heapSiftDownDepth size right + 1 ≤ heapSiftDownDepth size k :=
        log2_child_add_one (by dsimp only [right, left]; omega) hhasRight
      have hcostR : 2 * keyCompareCost loc.Lk + 240 + heapSiftDownCost size right loc.Lk ≤
          heapSiftDownCost size k loc.Lk := by
        unfold heapSiftDownCost
        have hmul := Nat.mul_le_mul_right (2 * keyCompareCost loc.Lk + 240) hdepthR
        rw [Nat.add_mul, Nat.one_mul] at hmul; omega
      refine runs_seq_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, hhasRight, hw1]) ?_ (fun h => absurd h (by decide))
      intro _
      refine runs_seq_assoc_le ?_
      refine runs_seq_assign_flat (v := mem (loc.arrPtr + right)) (by eval_expr) ?_
      refine runs_seq_assoc_le ?_
      refine runs_seq_assign_flat (v := mem (loc.arrPtr + left)) (by eval_expr) ?_
      refine runs_seq_assoc_le ?_
      refine runs_seq_call_flat hcmp
        (vs := [mem (loc.arrPtr + right), loc.numBase + mem (loc.arrPtr + right) * loc.Lk,
                loc.denBase + mem (loc.arrPtr + right) * loc.Lk,
                mem (loc.arrPtr + left), loc.numBase + mem (loc.arrPtr + left) * loc.Lk,
                loc.denBase + mem (loc.arrPtr + left) * loc.Lk, loc.Lk, scratch])
        (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨_, _, _, _, _, _, loc.Lk, scratch, rfl, by omega, by omega, by omega, by omega,
          hkeyR.2.1, hkeyR.2.2.1, hkeyL.2.1, hkeyL.2.2.1, hz, by unfold keyCompareSpace at hspStep ⊢; omega⟩
      · intro bit1 mem1 pos1 hpCmp1
        obtain ⟨hbit1, hf1, hz1⟩ := hpCmp1
        change bit1 = (if loc.edgeBetter mem h (mem (loc.arrPtr + right)) (mem (loc.arrPtr + left))
          then 1 else 0) at hbit1
        change (∀ x < scratch, mem1 x = mem x) at hf1
        change ZeroFrom mem1 (scratch + 16 * loc.Lk) at hz1
        have hbit1w : bit1 < 2 ^ w := by rw [hbit1]; split <;> omega
        refine runs_seq_assoc_le ?_
        refine runs_seq_assign_flat (v := scratch + 16 * loc.Lk) (by eval_expr) ?_
        refine runs_seq_cond_le (v := bit1) (by eval_expr) ?_ ?_
        · intro hnz1
          have hrb : loc.edgeBetter mem h (mem (loc.arrPtr + right)) (mem (loc.arrPtr + left)) = true := by
            by_contra hnot; rw [Bool.eq_false_iff.mpr hnot] at hbit1; exact hnz1 hbit1
          refine runs_seq_assign_flat (v := right) (by eval_expr) ?_
          let regsR :=
            Function.update
              (Function.update
                (Function.update
                  (Function.update
                    (Function.update
                      (Function.update
                        (Function.update
                          (Function.update
                            (Function.update
                              (Function.update
                                (Function.update
                                  (Function.update
                                    (Function.update
                                      (Function.update
                                        (Function.update (fun i => [loc.hb, k, scratch].getD i 0) 3 size) 4 (2 * k + 1))
                                      5 loc.Lk) 6 loc.arrPtr) 7 loc.posPtr) 8 loc.numBase) 9 loc.denBase) 10 left)
                            11 scratch) 12 right) 13 (mem (loc.arrPtr + right))) 14 (mem (loc.arrPtr + left)))
                    15 bit1) 11 (scratch + 16 * loc.Lk)) 10 right
          obtain ⟨ret, out, cRest, hrRest, hcRest, hlo, hhi, hat, hzO, hfrO, hposO⟩ :=
            hcont right (scratch + 16 * loc.Lk) mem1 regsR pos1 (by simp [regsR]) (by simp [regsR]) (by simp [regsR])
              (by simp [regsR]) (by simp [regsR]) (by simp [regsR]) (by simp [regsR]) (by simp [regsR])
              (by simp [regsR]) (Or.inr rfl) hhasRight
              (fun c hc0 hc hcp hcr => by
                have hcl : c = left := by dsimp only [left, right] at hcr ⊢; omega
                subst hcl; exact hrb)
              (by omega) le_rfl hf1 hz1
          refine ⟨.returned ret, out, cRest, hrRest, ?_, ?_⟩
          · dsimp only [heapSiftDownContract]
            simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ]
            exact ⟨hlo, hhi, hat, hzO, hfrO, hposO⟩
          · simp only [heapSiftDownContract, keyCompareContract, List.getD_cons_zero,
              List.getD_cons_succ, Expr.size, argsSize]
            omega
        · intro hz1b
          have hrf : loc.edgeBetter mem h (mem (loc.arrPtr + right)) (mem (loc.arrPtr + left)) = false := by
            by_contra hnot; rw [Bool.eq_true_of_not_eq_false hnot] at hbit1; simp only [↓reduceIte] at hbit1; omega
          have hlb : loc.edgeBetter mem h (mem (loc.arrPtr + left)) (mem (loc.arrPtr + right)) = true := by
            have hneRL : mem (loc.arrPtr + right) ≠ mem (loc.arrPtr + left) := fun h => by
              have := hbij.arr_inj hhasRight hhasLeft h; omega
            rcases keyBetter_total_of_ne (n₁ := loc.readNum mem h (mem (loc.arrPtr + left)))
                (d₁ := loc.readDen mem h (mem (loc.arrPtr + left)))
                (n₂ := loc.readNum mem h (mem (loc.arrPtr + right)))
                (d₂ := loc.readDen mem h (mem (loc.arrPtr + right))) hneRL.symm with h1 | h2
            · exact h1
            · change loc.edgeBetter mem h (mem (loc.arrPtr + right)) (mem (loc.arrPtr + left)) = true at h2
              rw [hrf] at h2; cases h2
          refine runs_seq_nop_le ?_
          let regsL :=
            Function.update
              (Function.update
                (Function.update
                  (Function.update
                    (Function.update
                      (Function.update
                        (Function.update
                          (Function.update
                            (Function.update
                              (Function.update
                                (Function.update
                                  (Function.update
                                    (Function.update
                                      (Function.update (fun i => [loc.hb, k, scratch].getD i 0) 3 size) 4 (2 * k + 1))
                                    5 loc.Lk) 6 loc.arrPtr) 7 loc.posPtr) 8 loc.numBase) 9 loc.denBase) 10 left)
                          11 scratch) 12 right) 13 (mem (loc.arrPtr + right))) 14 (mem (loc.arrPtr + left)))
                  15 bit1) 11 (scratch + 16 * loc.Lk)
          obtain ⟨ret, out, cRest, hrRest, hcRest, hlo, hhi, hat, hzO, hfrO, hposO⟩ :=
            hcont left (scratch + 16 * loc.Lk) mem1 regsL pos1 (by simp [regsL]) (by simp [regsL]) (by simp [regsL])
              (by simp [regsL]) (by simp [regsL]) (by simp [regsL]) (by simp [regsL]) (by simp [regsL])
              (by simp [regsL]) (Or.inl rfl) hhasLeft
              (fun c hc0 hc hcp hcl => by
                have hcr : c = right := by dsimp only [left, right] at hcl ⊢; omega
                subst hcr; exact hlb)
              (by omega) le_rfl hf1 hz1
          refine ⟨.returned ret, out, cRest, hrRest, ?_, ?_⟩
          · dsimp only [heapSiftDownContract]
            simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ]
            exact ⟨hlo, hhi, hat, hzO, hfrO, hposO⟩
          · simp only [heapSiftDownContract, keyCompareContract, List.getD_cons_zero,
              List.getD_cons_succ, Expr.size, argsSize]
            omega
    · refine runs_seq_cond_le (v := 0) (by simp [Expr.eval, BinOp.eval, hhasRight, show 0 < 2 ^ w by omega]) (fun h => absurd rfl h) ?_
      intro _
      refine runs_seq_nop_le ?_
      let regsNoR :=
        Function.update
          (Function.update
            (Function.update
              (Function.update
                (Function.update
                  (Function.update
                    (Function.update
                      (Function.update
                        (Function.update (Function.update (fun i => [loc.hb, k, scratch].getD i 0) 3 size) 4 (2 * k + 1))
                        5 loc.Lk) 6 loc.arrPtr) 7 loc.posPtr) 8 loc.numBase) 9 loc.denBase) 10 left)
            11 scratch) 12 right
      obtain ⟨ret, out, cRest, hrRest, hcRest, hlo, hhi, hat, hzO, hfrO, hposO⟩ :=
        hcont left scratch mem regsNoR pos (by simp [regsNoR]) (by simp [regsNoR]) (by simp [regsNoR])
          (by simp [regsNoR]) (by simp [regsNoR]) (by simp [regsNoR]) (by simp [regsNoR]) (by simp [regsNoR])
          (by simp [regsNoR]) (Or.inl rfl) hhasLeft
          (fun c hc0 hc hcp hcl => by dsimp only [left, right] at hcl ⊢; omega)
          le_rfl (by omega) (fun _ _ => rfl) hz
      refine ⟨.returned ret, out, cRest, hrRest, ?_, ?_⟩
      · dsimp only [heapSiftDownContract]
        simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ]
        exact ⟨hlo, hhi, hat, hzO, hfrO, hposO⟩
      · simp only [heapSiftDownContract, List.getD_cons_zero,
          List.getD_cons_succ, Expr.size]
        omega
  · refine runs_cond_le (v := 0) (by simp [Expr.eval, BinOp.eval, hhasLeft, show 0 < 2 ^ w by omega]) (fun h => absurd rfl h) ?_
    intro _
    refine runs_ret_le (v := scratch) (by eval_expr) ?_ ?_
    · dsimp only [heapSiftDownContract]
      simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ]
      refine ⟨le_rfl, Nat.le_add_right _ _,
        ⟨hhdr, hbij, hkeys,
         selectHeapOrder_of_exceptDown_stop hbij hexc (fun c hc hcp => by
           by_cases hc0 : c = 0
           · have hck : c = k := by omega
             subst hck; exact keyBetter_irrefl _ _ _
           · omega), hcand⟩,
        hz, fun _ _ _ => trivial, fun _ _ => trivial⟩
    · simp only [heapSiftDownContract, heapSiftDownCost, Expr.size]
      omega

end MinCostFlow.MinRatio
