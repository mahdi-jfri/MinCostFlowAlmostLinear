module

public import MinCostFlow.MinRatio.WireSelectHeapLayout
public import MinCostFlow.MinRatio.WireSelectKeyComp
import WordRAM.Tactic
import Mathlib.Data.Nat.Log

/-!
# Word-RAM `siftUp` procedure and shared flat execution helpers for the select-heap

Implements `heapSiftUpBody` (`args = [hb, k, scratch]`), which bubbles heap position `k` upward
while `k > 0` and `arr[k]` beats `arr[(k - 1) / 2]` under `keyCompareContract`:
- Scratch space: at most `Nat.log 2 (k + 1) * keyCompareSpace Lk` words.
- Time cost: at most `Nat.log 2 (k + 1) * (keyCompareCost Lk + 140) + 40` steps.

Also exports shared flat-state symbolic-execution wrappers (`runs_seq_assign_flat`,
`runs_seq_store_flat`, `runs_seq_call_flat`) and heap memory-agreement helpers used by
`WireSelectHeapSiftDown` and `WireSelectHeapOps`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num

/-! ## 1. `heapSiftUp`: recursive upward sifting -/

/-- Recursive `siftUp` body with arguments `[hb, k, scratch]`. Calls `cmp` (`keyCompareContract`)
and recurses via `self`. -/
def heapSiftUpBody (self cmp : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0))
    (.ret (.reg 2))
    (.assign 3 (.bin .div (.bin .sub (.reg 1) (.const 1)) (.const 2)) ;;
     .assign 4 (.load (.bin .add (.reg 0) (.const shLkOff))) ;;
     .assign 5 (.load (.bin .add (.reg 0) (.const shArrOff))) ;;
     .assign 6 (.load (.bin .add (.reg 0) (.const shPosOff))) ;;
     .assign 7 (.load (.bin .add (.reg 0) (.const shNumOff))) ;;
     .assign 8 (.load (.bin .add (.reg 0) (.const shDenOff))) ;;
     .assign 9 (.load (.bin .add (.reg 5) (.reg 1))) ;;
     .assign 10 (.load (.bin .add (.reg 5) (.reg 3))) ;;
     .call 11 cmp
       [.reg 9,
        .bin .add (.reg 7) (.bin .mul (.reg 9) (.reg 4)),
        .bin .add (.reg 8) (.bin .mul (.reg 9) (.reg 4)),
        .reg 10,
        .bin .add (.reg 7) (.bin .mul (.reg 10) (.reg 4)),
        .bin .add (.reg 8) (.bin .mul (.reg 10) (.reg 4)),
        .reg 4, .reg 2] ;;
     .assign 12 (.bin .add (.reg 2) (.bin .mul (.const 16) (.reg 4))) ;;
     .cond (.reg 11)
       (.store (.bin .add (.reg 5) (.reg 3)) (.reg 9) ;;
        .store (.bin .add (.reg 5) (.reg 1)) (.reg 10) ;;
        .store (.bin .add (.reg 6) (.reg 9)) (.bin .add (.reg 3) (.const 1)) ;;
        .store (.bin .add (.reg 6) (.reg 10)) (.bin .add (.reg 1) (.const 1)) ;;
        .call 13 self [.reg 0, .reg 3, .reg 12] ;;
        .ret (.reg 13))
       (.ret (.reg 12)))

theorem heapSiftUpBody_noRand (self cmp : ℕ) : (heapSiftUpBody self cmp).NoRand := by
  simp [heapSiftUpBody, Stmt.NoRand]

/-- Scratch space reserved by `heapSiftUpBody` from index `k`. -/
def heapSiftUpSpace (k Lk : ℕ) : ℕ :=
  Nat.log 2 (k + 1) * keyCompareSpace Lk

/-- Step cost bound for `heapSiftUpBody` from index `k`. -/
def heapSiftUpCost (k Lk : ℕ) : ℕ :=
  Nat.log 2 (k + 1) * (keyCompareCost Lk + 140) + 40

/-- Contract for `heapSiftUpBody` on a fixed heap block `loc` of size `size`. -/
def heapSiftUpContract (w h : ℕ) (loc : SelectHeapLoc) (size : ℕ) : Contract where
  pre args mem :=
    ∃ k scratch, args = [loc.hb, k, scratch] ∧
      16 < 2 ^ w ∧
      loc.endAddr ≤ scratch ∧
      SelectHeapHeaderAt mem loc size ∧
      SelectHeapBijection mem loc size ∧
      SelectHeapKeysValid mem loc h ∧
      SelectHeapCandLists mem loc ∧
      SelectHeapOrderExceptUp mem loc h size k ∧
      ZeroFrom mem scratch ∧
      scratch + heapSiftUpSpace k loc.Lk < 2 ^ w
  post args mem ret mem' :=
    let k := args.getD 1 0
    let scratch := args.getD 2 0
    scratch ≤ ret ∧ ret ≤ scratch + heapSiftUpSpace k loc.Lk ∧
    SelectHeapAt mem' loc h size ∧
    ZeroFrom mem' ret ∧
    (∀ a < scratch, (a < loc.arrPtr ∨ loc.lvlPtr ≤ a) → mem' a = mem a) ∧
    (∀ e < loc.cap, mem' (loc.posPtr + e) ≠ 0 ↔ mem (loc.posPtr + e) ≠ 0)
  cost args _ := heapSiftUpCost (args.getD 1 0) loc.Lk

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num

/-! ## 2. Shared flat symbolic-execution helpers and memory-agreement lemmas -/

theorem runs_seq_assign_flat {w : ℕ} {p : Program} {ω : ℕ → Bool} {r : ℕ} {e : Expr}
    {s : Stmt} {mem regs : ℕ → ℕ} {pos v k T : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w ⟨mem, regs, pos⟩ = some v)
    (hrest : ∃ o st' c, Runs w p ω s ⟨mem, Function.update regs r v, pos⟩ o st' c ∧
      Q o st' ∧ (k + e.size + 2) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.assign r e) s) ⟨mem, regs, pos⟩ o st' c ∧ Q o st' ∧ k + c ≤ T :=
  runs_seq_assign_le he hrest

theorem runs_seq_store_flat {w : ℕ} {p : Program} {ω : ℕ → Bool} {a e : Expr}
    {s : Stmt} {mem regs : ℕ → ℕ} {pos x v k T : ℕ} {Q : Outcome → State → Prop}
    (ha : a.eval w ⟨mem, regs, pos⟩ = some x) (he : e.eval w ⟨mem, regs, pos⟩ = some v)
    (hrest : ∃ o st' c, Runs w p ω s ⟨Function.update mem x v, regs, pos⟩ o st' c ∧
      Q o st' ∧ (k + a.size + e.size + 2) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.store a e) s) ⟨mem, regs, pos⟩ o st' c ∧ Q o st' ∧ k + c ≤ T :=
  runs_seq_store_le ha he hrest

theorem runs_seq_call_flat {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ} {args : List Expr}
    {C : Contract} {s : Stmt} {mem regs : ℕ → ℕ} {pos : ℕ} {vs : List ℕ} {k T : ℕ}
    {Q : Outcome → State → Prop}
    (hf : MeetsContract w p f C)
    (hargs : evalArgs w ⟨mem, regs, pos⟩ args = some vs)
    (hwords : ∀ v ∈ vs, v < 2 ^ w)
    (hpre : C.pre vs mem)
    (hrest : ∀ v mem' pos', C.post vs mem v mem' →
      ∃ o st' c, Runs w p ω s ⟨mem', Function.update regs r v, pos'⟩ o st' c ∧
        Q o st' ∧ (k + argsSize args + C.cost vs mem + 2) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.call r f args) s) ⟨mem, regs, pos⟩ o st' c ∧ Q o st' ∧ k + c ≤ T :=
  runs_seq_call_le hf hargs hwords hpre hrest

theorem selectHeap_slot_bounds {loc : SelectHeapLoc} {e : ℕ} (he : e < loc.cap) :
    loc.numBase + e * loc.Lk + loc.Lk ≤ loc.endAddr ∧
    loc.denBase + e * loc.Lk + loc.Lk ≤ loc.endAddr ∧
    loc.arrPtr + loc.cap ≤ loc.endAddr ∧
    loc.posPtr + loc.cap ≤ loc.endAddr ∧
    loc.hb + shHdrSize ≤ loc.endAddr := by
  have hmul : (e + 1) * loc.Lk ≤ loc.cap * loc.Lk := Nat.mul_le_mul_right _ he
  rw [Nat.add_mul, Nat.one_mul] at hmul
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold SelectHeapLoc.endAddr SelectHeapLoc.denBase; omega
  · unfold SelectHeapLoc.endAddr; omega
  · rw [loc.endAddr_eq]; unfold SelectHeapLoc.arrPtr selectHeapSize shHdrSize; omega
  · rw [loc.endAddr_eq]; unfold SelectHeapLoc.posPtr SelectHeapLoc.arrPtr selectHeapSize shHdrSize; omega
  · rw [loc.endAddr_eq]; unfold selectHeapSize shHdrSize; omega

theorem selectHeap_header_reads {mem : ℕ → ℕ} {loc : SelectHeapLoc} {size : ℕ}
    (hhdr : SelectHeapHeaderAt mem loc size) :
    mem loc.hb = size ∧
    mem (loc.hb + 3) = loc.Lk ∧
    mem (loc.hb + 4) = loc.arrPtr ∧
    mem (loc.hb + 5) = loc.posPtr ∧
    mem (loc.hb + 7) = loc.numBase ∧
    mem (loc.hb + 8) = loc.denBase :=
  ⟨by simpa using hhdr 0 (by simp),
   by simpa using hhdr 3 (by simp),
   by simpa using hhdr 4 (by simp),
   by simpa using hhdr 5 (by simp),
   by simpa using hhdr 7 (by simp),
   by simpa using hhdr 8 (by simp)⟩

/-- Transport the four structural heap invariants and `edgeBetter` across memory agreement below
`scratch ≥ loc.endAddr`. -/
theorem selectHeap_struct_of_agree_lt {mem mem1 : ℕ → ℕ} {loc : SelectHeapLoc} {h size scratch : ℕ}
    (hendLe : loc.endAddr ≤ scratch) (hf1 : ∀ x < scratch, mem1 x = mem x)
    (hhdr : SelectHeapHeaderAt mem loc size) (hbij : SelectHeapBijection mem loc size)
    (hkeys : SelectHeapKeysValid mem loc h) (hcand : SelectHeapCandLists mem loc) :
    SelectHeapHeaderAt mem1 loc size ∧
    SelectHeapBijection mem1 loc size ∧
    SelectHeapKeysValid mem1 loc h ∧
    SelectHeapCandLists mem1 loc ∧
    (∀ e₁ e₂, e₁ < loc.cap → e₂ < loc.cap →
      loc.edgeBetter mem1 h e₁ e₂ = loc.edgeBetter mem h e₁ e₂) := by
  have harr_lt (p : ℕ) (hp : p < loc.cap) : loc.arrPtr + p < scratch := by
    rw [loc.endAddr_eq] at hendLe; unfold SelectHeapLoc.arrPtr selectHeapSize shHdrSize at *; omega
  have hpos_lt (e : ℕ) (he : e < loc.cap) : loc.posPtr + e < scratch := by
    rw [loc.endAddr_eq] at hendLe; unfold SelectHeapLoc.posPtr SelectHeapLoc.arrPtr selectHeapSize shHdrSize at *; omega
  have hlvl_lt (e : ℕ) (he : e < loc.cap) : loc.lvlPtr + e < scratch := by
    rw [loc.endAddr_eq] at hendLe; unfold SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr SelectHeapLoc.arrPtr selectHeapSize shHdrSize at *; omega
  have hch_lt (i : ℕ) (hi : i ≤ loc.d) : loc.candHead + i < scratch := by
    rw [loc.endAddr_eq] at hendLe; unfold SelectHeapLoc.candHead SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr SelectHeapLoc.arrPtr selectHeapSize shHdrSize at *; omega
  have hcp_lt (e : ℕ) (he : e < loc.cap) : loc.candPrev + e < scratch := by
    rw [loc.endAddr_eq] at hendLe; unfold SelectHeapLoc.candPrev SelectHeapLoc.candHead SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr SelectHeapLoc.arrPtr selectHeapSize shHdrSize at *; omega
  have hcn_lt (e : ℕ) (he : e < loc.cap) : loc.candNext + e < scratch := by
    rw [loc.endAddr_eq] at hendLe; unfold SelectHeapLoc.candNext SelectHeapLoc.candPrev SelectHeapLoc.candHead SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr SelectHeapLoc.arrPtr selectHeapSize shHdrSize at *; omega
  have hhdr1 : SelectHeapHeaderAt mem1 loc size := fun j hj => by
    have hlt : loc.hb + j < scratch := by
      rw [loc.endAddr_eq] at hendLe; unfold selectHeapSize shHdrSize at *; simp only [List.length_cons, List.length_nil] at hj; omega
    exact (hf1 _ hlt).trans (hhdr j hj)
  refine ⟨hhdr1, ?_, ?_, ?_, ?_⟩
  · refine ⟨hbij.1, fun p hp => by rw [hf1 _ (harr_lt p (lt_of_lt_of_le hp hbij.1))]; exact hbij.2.1 p hp,
      fun p hp => by
        rw [hf1 _ (harr_lt p (lt_of_lt_of_le hp hbij.1)), hf1 _ (hpos_lt _ (hbij.2.1 p hp))]
        exact hbij.2.2.1 p hp,
      fun e he => by
        rw [hf1 _ (hpos_lt e he)]
        rcases hbij.2.2.2 e he with h0 | ⟨hle, harr⟩
        · exact Or.inl h0
        · have := hbij.1; exact Or.inr ⟨hle, by rw [hf1 _ (harr_lt _ (by omega))]; exact harr⟩⟩
  · intro e he hnz
    have hbdE := selectHeap_slot_bounds he
    rw [hf1 _ (hpos_lt e he)] at hnz
    obtain ⟨hl, hvn, hvd, hdp⟩ := hkeys e he hnz
    refine ⟨(hf1 _ (hlvl_lt e he)).trans_le hl,
      fun j hj => (hf1 _ (by omega)).trans_lt (hvn j hj),
      fun j hj => (hf1 _ (by omega)).trans_lt (hvd j hj), ?_⟩
    unfold SelectHeapLoc.readDen; rw [Num.intVal_congr (fun j hj => hf1 _ (by omega))]; exact hdp
  · obtain ⟨lists, hlists⟩ := hcand
    refine ⟨lists, fun i hi => ?_⟩
    obtain ⟨hdll, hiff⟩ := hlists i hi
    refine ⟨hdll.of_agree (hf1 _ (hch_lt i hi)) (fun e he => hf1 _ (hcp_lt e (hdll.2.1 e he)))
      (fun e he => hf1 _ (hcn_lt e (hdll.2.1 e he))), fun e => ?_⟩
    rw [hiff e]
    constructor
    · rintro ⟨he, hnz, hl⟩; exact ⟨he, by rwa [hf1 _ (hpos_lt e he)], (hf1 _ (hlvl_lt e he)).trans hl⟩
    · rintro ⟨he, hnz, hl⟩; exact ⟨he, by rwa [← hf1 _ (hpos_lt e he)], (hf1 _ (hlvl_lt e he)).symm.trans hl⟩
  · intro e₁ e₂ he₁ he₂
    have hb1 := selectHeap_slot_bounds he₁; have hb2 := selectHeap_slot_bounds he₂
    unfold SelectHeapLoc.edgeBetter SelectHeapLoc.readNum SelectHeapLoc.readDen
    rw [Num.intVal_congr (fun j hj => hf1 _ (by omega)),
        Num.intVal_congr (fun j hj => hf1 _ (by omega)),
        Num.intVal_congr (fun j hj => hf1 _ (by omega)),
        Num.intVal_congr (fun j hj => hf1 _ (by omega))]

private lemma log2_parent_add_one {k : ℕ} (hk0 : 0 < k) :
    Nat.log 2 ((k - 1) / 2 + 1) + 1 = Nat.log 2 (k + 1) := by
  have hdiv : (k - 1) / 2 + 1 = (k + 1) / 2 := by omega
  rw [hdiv]
  have hlog := Nat.log_of_one_lt_of_le (b := 2) (by decide) (show 2 ≤ k + 1 by omega)
  omega

/-! ## 3. Verification of `heapSiftUpBody` -/

/-- `heapSiftUpBody` meets `heapSiftUpContract` in `O(log(k + 1) · Lk^2)` time and
`O(log(k + 1) · Lk)` scratch space. -/
theorem heapSiftUp_meetsContract {w h self cmp : ℕ} {loc : SelectHeapLoc} {size : ℕ}
    {p : Program}
    (hp : p.procs[self]? = some (heapSiftUpBody self cmp))
    (hcmp : MeetsContract w p cmp (keyCompareContract w h)) :
    MeetsContract w p self (heapSiftUpContract w h loc size) := by
  apply meetsContract_of_rec (fun args _ => args.getD 1 0) hp
  intro kMeasure ih args mem pos ω hwords hpre hkM
  obtain ⟨k, scratch, rfl, hw16, hendLe, hhdr, hbij, hkeys, hcand, hexc, hz, hroom⟩ := hpre
  change k = kMeasure at hkM
  subst hkM
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hhbw : loc.hb < 2 ^ w := hwords loc.hb (by simp)
  have hkw : k < 2 ^ w := hwords k (by simp)
  have hscw : scratch < 2 ^ w := hwords scratch (by simp)
  apply runs_start_le
  dsimp only [startState]
  unfold heapSiftUpBody
  simp only [shLkOff, shArrOff, shPosOff, shNumOff, shDenOff]
  by_cases hk0 : k = 0
  · subst hk0
    have htest : (Expr.bin .eq (.reg 1) (.const 0)).eval w
        ⟨mem, fun r => ([loc.hb, 0, scratch]).getD r 0, pos⟩ = some 1 := by
      simp [Expr.eval, BinOp.eval, hw1]
    refine runs_cond_le (v := 1) htest ?_ (fun h => absurd h (by decide))
    intro _
    refine runs_ret_le (v := scratch) (by eval_expr) ?_ ?_
    · dsimp only [heapSiftUpContract]
      simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ]
      refine ⟨le_rfl, Nat.le_add_right _ _,
        ⟨hhdr, hbij, hkeys, selectHeapOrder_of_exceptUp_stop hbij hexc (Or.inl rfl), hcand⟩,
        hz, fun _ _ _ => trivial, fun _ _ => trivial⟩
    · simp only [heapSiftUpContract, heapSiftUpCost, Expr.size]
      omega
  · have hkPos : 0 < k := Nat.pos_of_ne_zero hk0
    let par := (k - 1) / 2
    have hlogEq : Nat.log 2 (par + 1) + 1 = Nat.log 2 (k + 1) := log2_parent_add_one hkPos
    have hspStep : keyCompareSpace loc.Lk + heapSiftUpSpace par loc.Lk =
        heapSiftUpSpace k loc.Lk := by
      unfold heapSiftUpSpace
      rw [← hlogEq, Nat.add_mul, Nat.one_mul, Nat.add_comm]
    have hcostStep : keyCompareCost loc.Lk + 140 + heapSiftUpCost par loc.Lk =
        heapSiftUpCost k loc.Lk := by
      unfold heapSiftUpCost
      rw [← hlogEq, Nat.add_mul, Nat.one_mul]; omega
    have htest : (Expr.bin .eq (.reg 1) (.const 0)).eval w
        ⟨mem, fun r => ([loc.hb, k, scratch]).getD r 0, pos⟩ = some 0 := by
      simp [Expr.eval, BinOp.eval, hk0, show 0 < 2 ^ w by omega]
    refine runs_cond_le (v := 0) htest (fun h => absurd rfl h) ?_
    intro _
    have hpar_lt_k : par < k := by dsimp only [par]; omega
    have hpar_lt : par < size := lt_trans hpar_lt_k hexc.1
    have hne : par ≠ k := ne_of_lt hpar_lt_k
    have hparCap : par < loc.cap := lt_of_lt_of_le hpar_lt hbij.1
    have hkCap : k < loc.cap := lt_of_lt_of_le hexc.1 hbij.1
    have hekCap : mem (loc.arrPtr + k) < loc.cap := hbij.2.1 k hexc.1
    have hepCap : mem (loc.arrPtr + par) < loc.cap := hbij.2.1 par hpar_lt
    have hbdK := selectHeap_slot_bounds hekCap
    have hbdP := selectHeap_slot_bounds hepCap
    have hhdrLt : loc.hb + 14 ≤ loc.endAddr := hbdK.2.2.2.2
    have hhdrR := selectHeap_header_reads hhdr
    have hLkw : loc.Lk < 2 ^ w := by unfold keyCompareSpace at hspStep; omega
    have h16Lkw : 16 * loc.Lk < 2 ^ w := by unfold keyCompareSpace at hspStep; omega
    have hsc1w : scratch + 16 * loc.Lk < 2 ^ w := by unfold keyCompareSpace at hspStep; omega
    have hparw : par < 2 ^ w := by omega
    have harrW : loc.arrPtr < 2 ^ w := by omega
    have hposW : loc.posPtr < 2 ^ w := by omega
    have hnumW : loc.numBase < 2 ^ w := by omega
    have hdenW : loc.denBase < 2 ^ w := by omega
    have hekw : mem (loc.arrPtr + k) < 2 ^ w := by omega
    have hepw : mem (loc.arrPtr + par) < 2 ^ w := by omega
    have hnkw : loc.numBase + mem (loc.arrPtr + k) * loc.Lk < 2 ^ w := by omega
    have hdkw : loc.denBase + mem (loc.arrPtr + k) * loc.Lk < 2 ^ w := by omega
    have hnpw : loc.numBase + mem (loc.arrPtr + par) * loc.Lk < 2 ^ w := by omega
    have hdpw : loc.denBase + mem (loc.arrPtr + par) * loc.Lk < 2 ^ w := by omega
    have hkeyK := hkeys _ hekCap (hbij.pos_arr_ne_zero hexc.1)
    have hkeyP := hkeys _ hepCap (hbij.pos_arr_ne_zero hpar_lt)
    have hr3e : (Expr.bin .div (.bin .sub (.reg 1) (.const 1)) (.const 2)).eval w
        ⟨mem, fun r => ([loc.hb, k, scratch]).getD r 0, pos⟩ = some par := by
      simp [Expr.eval, BinOp.eval, hw1, hw2, show k - 1 < 2 ^ w by omega, hparw, par]
    refine runs_seq_assign_flat (v := par) hr3e ?_
    refine runs_seq_assign_flat (v := loc.Lk) (by eval_expr; exact hhdrR.2.1) ?_
    refine runs_seq_assign_flat (v := loc.arrPtr) (by eval_expr; exact hhdrR.2.2.1) ?_
    refine runs_seq_assign_flat (v := loc.posPtr) (by eval_expr; exact hhdrR.2.2.2.1) ?_
    refine runs_seq_assign_flat (v := loc.numBase) (by eval_expr; exact hhdrR.2.2.2.2.1) ?_
    refine runs_seq_assign_flat (v := loc.denBase) (by eval_expr; exact hhdrR.2.2.2.2.2) ?_
    refine runs_seq_assign_flat (v := mem (loc.arrPtr + k)) (by eval_expr) ?_
    refine runs_seq_assign_flat (v := mem (loc.arrPtr + par)) (by eval_expr) ?_
    refine runs_seq_call_flat hcmp
      (vs := [mem (loc.arrPtr + k), loc.numBase + mem (loc.arrPtr + k) * loc.Lk,
              loc.denBase + mem (loc.arrPtr + k) * loc.Lk,
              mem (loc.arrPtr + par), loc.numBase + mem (loc.arrPtr + par) * loc.Lk,
              loc.denBase + mem (loc.arrPtr + par) * loc.Lk, loc.Lk, scratch])
      (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨_, _, _, _, _, _, loc.Lk, scratch, rfl, by omega, by omega, by omega, by omega,
        hkeyK.2.1, hkeyK.2.2.1, hkeyP.2.1, hkeyP.2.2.1, hz, by unfold keyCompareSpace; omega⟩
    · intro bit mem1 pos1 hpostCmp
      obtain ⟨hbit, hf1, hz1⟩ := hpostCmp
      change bit = (if loc.edgeBetter mem h (mem (loc.arrPtr + k)) (mem (loc.arrPtr + par)) then 1 else 0) at hbit
      change (∀ x < scratch, mem1 x = mem x) at hf1
      change ZeroFrom mem1 (scratch + 16 * loc.Lk) at hz1
      have hbitw : bit < 2 ^ w := by rw [hbit]; split <;> omega
      obtain ⟨hhdr1, hbij1, hkeys1, hcand1, hedgeEq1⟩ :=
        selectHeap_struct_of_agree_lt hendLe hf1 hhdr hbij hkeys hcand
      have hexc1 : SelectHeapOrderExceptUp mem1 loc h size k := by
        refine ⟨hexc.1, fun p hp0 hp hpk => ?_, fun hk0' c hc hck => ?_⟩
        · have h1 := hbij.2.1 _ (by omega : (p - 1) / 2 < size)
          have h2 := hbij.2.1 p hp
          have := hbij.1
          rw [hf1 _ (by omega), hf1 _ (by omega), hedgeEq1 _ _ h1 h2]
          exact hexc.2.1 p hp0 hp hpk
        · have h1 := hbij.2.1 _ hpar_lt
          have h2 := hbij.2.1 c hc
          have := hbij.1
          rw [hf1 _ (by omega), hf1 _ (by omega), hedgeEq1 _ _ h1 h2]
          exact hexc.2.2 hk0' c hc hck
      refine runs_seq_assign_flat (v := scratch + 16 * loc.Lk) (by eval_expr) ?_
      refine runs_cond_le (v := bit) (by eval_expr) ?_ ?_
      · intro hnzBit
        have hbeat : loc.edgeBetter mem h (mem (loc.arrPtr + k)) (mem (loc.arrPtr + par)) = true := by
          by_contra hnot
          rw [Bool.eq_false_iff.mpr hnot] at hbit; exact hnzBit hbit
        have hbeat1 : loc.edgeBetter mem1 h (mem1 (loc.arrPtr + k)) (mem1 (loc.arrPtr + par)) = true := by
          rw [hf1 _ (by omega), hf1 _ (by omega), hedgeEq1 _ _ hekCap hepCap]; exact hbeat
        refine runs_seq_store_flat (by eval_expr) (by eval_expr) ?_
        refine runs_seq_store_flat (by eval_expr) (by eval_expr) ?_
        refine runs_seq_store_flat (by eval_expr) (by eval_expr) ?_
        refine runs_seq_store_flat (by eval_expr) (by eval_expr) ?_
        have hmEq : Function.update
            (Function.update
              (Function.update
                (Function.update mem1 (loc.arrPtr + par) (mem (loc.arrPtr + k)))
                (loc.arrPtr + k) (mem (loc.arrPtr + par)))
              (loc.posPtr + mem (loc.arrPtr + k)) (par + 1))
            (loc.posPtr + mem (loc.arrPtr + par)) (k + 1) =
            heapSwapMem mem1 loc par k := by
          unfold heapSwapMem
          rw [hf1 (loc.arrPtr + par) (by omega), hf1 (loc.arrPtr + k) (by omega)]
        have hstruct2 := heapSwapMem_preserves_struct hhdr1 hbij1 hkeys1 hcand1 hpar_lt hexc.1 hne
        have hexc2 := siftUp_swap_step hbij1 hkeys1 hexc1 hkPos hbeat1
        have hout2 (a : ℕ) (ha : a < loc.arrPtr ∨ loc.lvlPtr ≤ a) :
            heapSwapMem mem1 loc par k a = mem1 a :=
          heapSwapMem_eq_of_outside hparCap hkCap (by rw [hf1 _ (by omega)]; exact hepCap)
            (by rw [hf1 _ (by omega)]; exact hekCap) ha
        have hz2 : ZeroFrom (heapSwapMem mem1 loc par k) (scratch + 16 * loc.Lk) := fun a ha => by
          rw [hout2 a (Or.inr (by
            have := loc.endAddr_eq; unfold SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr
              SelectHeapLoc.arrPtr selectHeapSize shHdrSize at *; omega))]
          exact hz1 a ha
        refine runs_seq_call_flat ih (vs := [loc.hb, par, scratch + 16 * loc.Lk])
          (by eval_expr) (by wram_words) ?_ ?_
        · rw [hmEq]
          exact ⟨⟨par, scratch + 16 * loc.Lk, rfl, hw16, by omega,
            hstruct2.1, hstruct2.2.1, hstruct2.2.2.1, hstruct2.2.2.2, hexc2, hz2,
            by unfold keyCompareSpace at hspStep; omega⟩, hpar_lt_k⟩
        · intro ret mem3 pos3 hpostRec
          obtain ⟨hlo3, hhi3, hat3, hz3, hfr3, hpos3⟩ := hpostRec
          simp only [List.getD_cons_zero, List.getD_cons_succ] at hlo3 hhi3 hfr3 hpos3
          have hretw : ret < 2 ^ w := by unfold keyCompareSpace at hspStep; omega
          refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
          · dsimp only [heapSiftUpContract]
            simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ]
            refine ⟨by omega, by unfold keyCompareSpace at hspStep; omega, hat3, hz3, ?_, ?_⟩
            · intro a ha hout
              exact (hfr3 a (by omega) hout).trans (by rw [hmEq, hout2 a hout, hf1 a ha])
            · intro e he
              rw [hpos3 e he, hmEq, heapSwapMem_pos hbij1 hpar_lt hexc.1 he hne]
              rw [hf1 (loc.arrPtr + par) (by omega), hf1 (loc.arrPtr + k) (by omega),
                  hf1 (loc.posPtr + e) (by omega)]
              split_ifs with h1 h2
              · subst h1; simp [hbij.pos_arr_ne_zero hpar_lt]
              · subst h2; simp [hbij.pos_arr_ne_zero hexc.1]
              · rfl
          · simp only [Contract.below, heapSiftUpContract, keyCompareContract, List.getD_cons_zero,
              List.getD_cons_succ, Expr.size, argsSize]
            omega
      · intro hzBit
        have hfalse : loc.edgeBetter mem h (mem (loc.arrPtr + k)) (mem (loc.arrPtr + par)) = false := by
          by_contra hnot
          rw [Bool.eq_true_of_not_eq_false hnot] at hbit; simp only [↓reduceIte] at hbit; omega
        have hfalse1 : loc.edgeBetter mem1 h (mem1 (loc.arrPtr + k)) (mem1 (loc.arrPtr + par)) = false := by
          rw [hf1 _ (by omega), hf1 _ (by omega), hedgeEq1 _ _ hekCap hepCap]; exact hfalse
        refine runs_ret_le (v := scratch + 16 * loc.Lk) (by eval_expr) ?_ ?_
        · dsimp only [heapSiftUpContract]
          simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ]
          refine ⟨by omega, by unfold keyCompareSpace at hspStep; omega,
            ⟨hhdr1, hbij1, hkeys1, selectHeapOrder_of_exceptUp_stop hbij1 hexc1 (Or.inr hfalse1), hcand1⟩,
            hz1, fun a ha _ => hf1 a ha, fun e he => by
              have hbe := selectHeap_slot_bounds he; rw [hf1 _ (by omega)]⟩
        · simp only [heapSiftUpContract, keyCompareContract, List.getD_cons_zero,
            List.getD_cons_succ, Expr.size, argsSize]
          omega

end MinCostFlow.MinRatio
