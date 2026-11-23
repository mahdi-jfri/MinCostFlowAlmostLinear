module

public import MinCostFlow.MinRatio.WireSelectHeapRebal
import WordRAM.Tactic
import Mathlib.Data.Nat.Log

/-!
# Select-heap `heapUpsert` procedure

Implements and verifies `heapUpsertBody` (`[hb, e, lvl, nPtr, dPtr, scratch]`), inserting or
updating edge `e` at level `lvl` in `O((log(cap + 1) + 1) · (Lk^2 + 1))` steps.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num DynSpanner.Program

/-! ## 3. `heapUpsert`: insert or update key of edge `e` at level `lvl` -/

/-- Insert or update edge `e` at level `lvl` with `Lk`-limb signed key `(nPtr, dPtr)`.
Arguments: `[hb, e, lvl, nPtr, dPtr, scratch]`. -/
def heapUpsertBody (copyTo siftUp rebal candCons candErase : ℕ) : Stmt :=
  .assign 6 (.load (.bin .add (.reg 0) (.const shLkOff))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const shArrOff))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const shPosOff))) ;;
  .assign 9 (.load (.bin .add (.reg 0) (.const shLvlOff))) ;;
  .assign 10 (.load (.bin .add (.reg 0) (.const shNumOff))) ;;
  .assign 11 (.load (.bin .add (.reg 0) (.const shDenOff))) ;;
  .call 12 copyTo [.reg 3, .bin .add (.reg 10) (.bin .mul (.reg 1) (.reg 6)), .reg 6] ;;
  .call 12 copyTo [.reg 4, .bin .add (.reg 11) (.bin .mul (.reg 1) (.reg 6)), .reg 6] ;;
  .assign 13 (.load (.bin .add (.reg 8) (.reg 1))) ;;
  .cond (.bin .eq (.reg 13) (.const 0))
    (.assign 14 (.load (.reg 0)) ;;
     .store (.bin .add (.reg 7) (.reg 14)) (.reg 1) ;;
     .store (.bin .add (.reg 8) (.reg 1)) (.bin .add (.reg 14) (.const 1)) ;;
     .store (.bin .add (.reg 9) (.reg 1)) (.reg 2) ;;
     .store (.reg 0) (.bin .add (.reg 14) (.const 1)) ;;
     .call 12 candCons [.reg 0, .reg 2, .reg 1] ;;
     .call 15 siftUp [.reg 0, .reg 14, .reg 5] ;;
     .ret (.reg 15))
    (.assign 14 (.bin .sub (.reg 13) (.const 1)) ;;
     .assign 16 (.load (.bin .add (.reg 9) (.reg 1))) ;;
     .cond (.bin .eq (.reg 16) (.reg 2))
       .nop
       (.call 12 candErase [.reg 0, .reg 16, .reg 1] ;;
        .store (.bin .add (.reg 9) (.reg 1)) (.reg 2) ;;
        .call 12 candCons [.reg 0, .reg 2, .reg 1]) ;;
     .call 15 rebal [.reg 0, .reg 14, .reg 5] ;;
     .ret (.reg 15))

theorem heapUpsertBody_noRand (copyTo siftUp rebal candCons candErase : ℕ) :
    (heapUpsertBody copyTo siftUp rebal candCons candErase).NoRand := by
  simp [heapUpsertBody, Stmt.NoRand]

/-- Step cost bound for `heapUpsertBody`: `O((log(cap + 1) + 1) · (Lk^2 + 1))`. -/
def heapUpsertCost (cap Lk : ℕ) : ℕ :=
  36 * Lk + heapRebalanceCost cap Lk + 420

/-- Contract for `heapUpsertBody`: inserts `e` (if absent, increasing `size` by 1) or updates `e`'s
key and level (if present, keeping `size`), preserving every other edge's membership, level, and
key, and preserving all memory outside `[loc.hb, loc.endAddr)` and `[scratch, ret)`. -/
def heapUpsertContract (w h : ℕ) (loc : SelectHeapLoc) (size : ℕ) : Contract where
  pre args mem :=
    ∃ e lvl nPtr dPtr scratch, args = [loc.hb, e, lvl, nPtr, dPtr, scratch] ∧
      16 < 2 ^ w ∧ loc.endAddr ≤ scratch ∧
      e < loc.cap ∧ lvl ≤ loc.d ∧
      (mem (loc.posPtr + e) = 0 → size < loc.cap) ∧
      nPtr + loc.Lk ≤ scratch ∧ dPtr + loc.Lk ≤ scratch ∧
      (nPtr + loc.Lk ≤ loc.hb ∨ loc.endAddr ≤ nPtr) ∧
      (dPtr + loc.Lk ≤ loc.hb ∨ loc.endAddr ≤ dPtr) ∧
      Num.Valid mem nPtr h loc.Lk ∧ Num.Valid mem dPtr h loc.Lk ∧
      (∀ j < loc.Lk, mem (nPtr + j) < 2 ^ w) ∧ (∀ j < loc.Lk, mem (dPtr + j) < 2 ^ w) ∧
      0 < Num.intVal mem dPtr h loc.Lk ∧
      SelectHeapAt mem loc h size ∧
      ZeroFrom mem scratch ∧
      scratch + heapRebalanceSpace loc.cap loc.Lk < 2 ^ w
  post args mem ret mem' :=
    let e := args.getD 1 0
    let lvl := args.getD 2 0
    let nPtr := args.getD 3 0
    let dPtr := args.getD 4 0
    let scratch := args.getD 5 0
    let size' := if mem (loc.posPtr + e) = 0 then size + 1 else size
    scratch ≤ ret ∧ ret ≤ scratch + heapRebalanceSpace loc.cap loc.Lk ∧
    SelectHeapAt mem' loc h size' ∧
    ZeroFrom mem' ret ∧
    mem' (loc.posPtr + e) ≠ 0 ∧ mem' (loc.lvlPtr + e) = lvl ∧
    loc.readNum mem' h e = Num.intVal mem nPtr h loc.Lk ∧
    loc.readDen mem' h e = Num.intVal mem dPtr h loc.Lk ∧
    (∀ e' < loc.cap, e' ≠ e →
      (mem' (loc.posPtr + e') ≠ 0 ↔ mem (loc.posPtr + e') ≠ 0) ∧
      mem' (loc.lvlPtr + e') = mem (loc.lvlPtr + e') ∧
      loc.readNum mem' h e' = loc.readNum mem h e' ∧
      loc.readDen mem' h e' = loc.readDen mem h e') ∧
    (∀ a < scratch, (a < loc.hb ∨ loc.endAddr ≤ a) → mem' a = mem a)
  cost _ _ := heapUpsertCost loc.cap loc.Lk

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num DynSpanner.Program

/-! ## 6. Verification of `heapUpsertBody` -/

private lemma keyCompareSpace_le_heapRebalanceSpace (cap Lk : ℕ) :
    keyCompareSpace Lk ≤ heapRebalanceSpace cap Lk := by
  unfold heapRebalanceSpace
  have h2 : 1 ≤ 2 * Nat.log 2 (cap + 1) + 1 := by omega
  calc keyCompareSpace Lk = 1 * keyCompareSpace Lk := (Nat.one_mul _).symm
    _ ≤ (2 * Nat.log 2 (cap + 1) + 1) * keyCompareSpace Lk :=
        Nat.mul_le_mul_right _ h2

private lemma heapSiftUpSpace_le_heapRebalanceSpace {size cap Lk : ℕ} (h : size < cap) :
    heapSiftUpSpace size Lk ≤ heapRebalanceSpace cap Lk := by
  unfold heapSiftUpSpace heapRebalanceSpace
  have hlg : Nat.log 2 (size + 1) ≤ Nat.log 2 (cap + 1) := Nat.log_mono_right (by omega)
  exact Nat.mul_le_mul_right (keyCompareSpace Lk) (by omega)

private lemma heapSiftUpCost_le_heapRebalanceCost {size cap Lk : ℕ} (h : size < cap) :
    heapSiftUpCost size Lk ≤ heapRebalanceCost cap Lk := by
  unfold heapSiftUpCost heapRebalanceCost
  have hlg : Nat.log 2 (size + 1) ≤ Nat.log 2 (cap + 1) := Nat.log_mono_right (by omega)
  have h1 : Nat.log 2 (size + 1) * (keyCompareCost Lk + 140) ≤
      Nat.log 2 (size + 1) * (2 * keyCompareCost Lk + 240) :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : Nat.log 2 (size + 1) * (2 * keyCompareCost Lk + 240) ≤
      (Nat.log 2 (cap + 1) + 1) * (2 * keyCompareCost Lk + 240) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

private lemma selectHeap_layout_eqs (loc : SelectHeapLoc) :
    loc.hb + 14 = loc.arrPtr ∧ loc.arrPtr + loc.cap = loc.posPtr ∧
    loc.posPtr + loc.cap = loc.lvlPtr ∧ loc.lvlPtr + loc.cap = loc.candHead ∧
    loc.candHead + (loc.d + 1) = loc.candPrev ∧ loc.candPrev + loc.cap = loc.candNext ∧
    loc.candNext + loc.cap = loc.numBase ∧ loc.numBase + loc.cap * loc.Lk = loc.denBase ∧
    loc.denBase + loc.cap * loc.Lk = loc.endAddr := by
  unfold SelectHeapLoc.endAddr SelectHeapLoc.denBase SelectHeapLoc.numBase
    SelectHeapLoc.candNext SelectHeapLoc.candPrev SelectHeapLoc.candHead
    SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr SelectHeapLoc.arrPtr shHdrSize
  omega

private lemma selectHeap_hdr_bij_of_frame {loc : SelectHeapLoc} {size : ℕ} {m₁ m₂ : ℕ → ℕ}
    (hhdr : SelectHeapHeaderAt m₁ loc size) (hbij : SelectHeapBijection m₁ loc size)
    (hfr : ∀ a < loc.lvlPtr, m₂ a = m₁ a) :
    SelectHeapHeaderAt m₂ loc size ∧ SelectHeapBijection m₂ loc size := by
  have hlay := selectHeap_layout_eqs loc
  have hszLe := hbij.1
  refine ⟨fun j hj => by
    simp only [List.length_cons, List.length_nil] at hj
    exact (hfr _ (by omega)).trans (hhdr j (by simp only [List.length_cons, List.length_nil]; omega)),
    ⟨hszLe, fun p hp => by rw [hfr _ (by omega)]; exact hbij.2.1 p hp,
     fun p hp => by
       have hpCap := hbij.2.1 p hp
       have ha : m₂ (loc.arrPtr + p) = m₁ (loc.arrPtr + p) := hfr _ (by omega)
       rw [ha, hfr _ (by omega)]; exact hbij.2.2.1 p hp,
     fun e' he' => by
       rw [hfr _ (by omega)]
       rcases hbij.2.2.2 e' he' with h0 | ⟨hle, harr⟩
       · exact Or.inl h0
       · exact Or.inr ⟨hle, by rw [hfr _ (by omega)]; exact harr⟩⟩⟩

private lemma selectHeap_struct_of_cand_frame {loc : SelectHeapLoc} {h size : ℕ} {m₁ m₂ : ℕ → ℕ}
    (hhdr : SelectHeapHeaderAt m₁ loc size) (hbij : SelectHeapBijection m₁ loc size)
    (hkeys : SelectHeapKeysValid m₁ loc h)
    (hfr : ∀ a, (a < loc.candHead ∨ loc.numBase ≤ a) → m₂ a = m₁ a) :
    SelectHeapHeaderAt m₂ loc size ∧ SelectHeapBijection m₂ loc size ∧
      SelectHeapKeysValid m₂ loc h := by
  have hlay := selectHeap_layout_eqs loc
  obtain ⟨hhdr2, hbij2⟩ := selectHeap_hdr_bij_of_frame hhdr hbij (fun a ha => hfr a (Or.inl (by omega)))
  refine ⟨hhdr2, hbij2, fun e' he' hnz => ?_⟩
  have hbd' := selectHeap_slot_bounds he'
  rw [hfr _ (Or.inl (by omega))] at hnz
  obtain ⟨hl', hvn', hvd', hdp'⟩ := hkeys e' he' hnz
  refine ⟨by rw [hfr _ (Or.inl (by omega))]; exact hl',
    fun j hj => by rw [hfr _ (Or.inr (by omega))]; exact hvn' j hj,
    fun j hj => by rw [hfr _ (Or.inr (by omega))]; exact hvd' j hj, ?_⟩
  have hden : loc.readDen m₂ h e' = loc.readDen m₁ h e' :=
    Num.intVal_congr fun j hj => hfr _ (Or.inr (by omega))
  rw [hden]; exact hdp'

private lemma heapUpsert_insert_branch {w h siftUp candCons : ℕ} {loc : SelectHeapLoc}
    {size e lvl nPtr dPtr scratch pos k0 : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem mem2 regs2 : ℕ → ℕ}
    (hup : MeetsContract w p siftUp (heapSiftUpContract w h loc (size + 1)))
    (hcons : ∀ size' lists, MeetsContract w p candCons (candListConsContract w loc size' lists))
    (hw16 : 16 < 2 ^ w) (hendLe : loc.endAddr ≤ scratch)
    (heCap : e < loc.cap) (hlvlD : lvl ≤ loc.d) (hszLt : size < loc.cap)
    (hroom : scratch + heapRebalanceSpace loc.cap loc.Lk < 2 ^ w)
    (hat : SelectHeapAt mem loc h size) (hpos0 : mem (loc.posPtr + e) = 0)
    (hz2 : ZeroFrom mem2 scratch)
    (hmem2_out : ∀ a, (a < loc.numBase ∨ loc.endAddr ≤ a) → mem2 a = mem a)
    (hnumE2 : loc.readNum mem2 h e = Num.intVal mem nPtr h loc.Lk)
    (hdenE2 : loc.readDen mem2 h e = Num.intVal mem dPtr h loc.Lk)
    (hvnE2 : Num.Valid mem2 (loc.numBase + e * loc.Lk) h loc.Lk)
    (hvdE2 : Num.Valid mem2 (loc.denBase + e * loc.Lk) h loc.Lk)
    (hdPos : 0 < Num.intVal mem dPtr h loc.Lk)
    (hkeyOther2 : ∀ e' < loc.cap, e' ≠ e →
      loc.readNum mem2 h e' = loc.readNum mem h e' ∧
      loc.readDen mem2 h e' = loc.readDen mem h e')
    (hvnOther2 : ∀ e' < loc.cap, e' ≠ e → ∀ j < loc.Lk,
      mem2 (loc.numBase + e' * loc.Lk + j) = mem (loc.numBase + e' * loc.Lk + j))
    (hvdOther2 : ∀ e' < loc.cap, e' ≠ e → ∀ j < loc.Lk,
      mem2 (loc.denBase + e' * loc.Lk + j) = mem (loc.denBase + e' * loc.Lk + j))
    (hr0 : regs2 0 = loc.hb) (hr1 : regs2 1 = e) (hr2 : regs2 2 = lvl)
    (hr5 : regs2 5 = scratch) (hr7 : regs2 7 = loc.arrPtr)
    (hr8 : regs2 8 = loc.posPtr) (hr9 : regs2 9 = loc.lvlPtr)
    (hk0 : k0 + heapSiftUpCost size loc.Lk + 140 ≤ heapUpsertCost loc.cap loc.Lk) :
    ∃ o st' c, Runs w p ω
      (.assign 14 (.load (.reg 0)) ;;
       .store (.bin .add (.reg 7) (.reg 14)) (.reg 1) ;;
       .store (.bin .add (.reg 8) (.reg 1)) (.bin .add (.reg 14) (.const 1)) ;;
       .store (.bin .add (.reg 9) (.reg 1)) (.reg 2) ;;
       .store (.reg 0) (.bin .add (.reg 14) (.const 1)) ;;
       .call 12 candCons [.reg 0, .reg 2, .reg 1] ;;
       .call 15 siftUp [.reg 0, .reg 14, .reg 5] ;;
       .ret (.reg 15))
      ⟨mem2, regs2, pos⟩ o st' c ∧
      (heapUpsertContract w h loc size).post [loc.hb, e, lvl, nPtr, dPtr, scratch] mem o.value st'.mem ∧
      k0 + c ≤ (heapUpsertContract w h loc size).cost [loc.hb, e, lvl, nPtr, dPtr, scratch] mem := by
  obtain ⟨hhdr, hbij, hkeys, hord, hcand⟩ := hat
  have hhr := selectHeap_header_reads hhdr
  have hlayout := selectHeap_layout_eqs loc
  have hbdE := selectHeap_slot_bounds heCap
  have hw1 : 1 < 2 ^ w := (by omega)
  have hsz1W : size + 1 < 2 ^ w := (by omega)
  have hhd2 : mem2 loc.hb = size := (hmem2_out loc.hb (by omega)).trans hhr.1
  refine runs_seq_assign_flat (v := size)
    (by simp [Expr.eval, hr0, hhd2]) ?_
  refine runs_seq_store_flat (x := loc.arrPtr + size) (v := e)
    (by simp [Expr.eval, BinOp.eval, hr7, show loc.arrPtr + size < 2 ^ w by omega])
    (by simp [Expr.eval, hr1]) ?_
  refine runs_seq_store_flat (x := loc.posPtr + e) (v := size + 1)
    (by simp [Expr.eval, BinOp.eval, hr8, hr1, show loc.posPtr + e < 2 ^ w by omega])
    (by simp [Expr.eval, BinOp.eval, hw1, hsz1W]) ?_
  refine runs_seq_store_flat (x := loc.lvlPtr + e) (v := lvl)
    (by simp [Expr.eval, BinOp.eval, hr9, hr1, show loc.lvlPtr + e < 2 ^ w by omega])
    (by simp [Expr.eval, hr2]) ?_
  refine runs_seq_store_flat (x := loc.hb) (v := size + 1)
    (by simp [Expr.eval, hr0])
    (by simp [Expr.eval, BinOp.eval, hw1, hsz1W]) ?_
  set mem3 := Function.update
    (Function.update
      (Function.update
        (Function.update mem2 (loc.arrPtr + size) e)
        (loc.posPtr + e) (size + 1))
      (loc.lvlPtr + e) lvl)
    loc.hb (size + 1)
  have hm3_hb : mem3 loc.hb = size + 1 := by simp [mem3]
  have hm3_lvlE : mem3 (loc.lvlPtr + e) = lvl := by
    dsimp only [mem3]; rw [Function.update_of_ne (by omega), Function.update_self]
  have hm3_posE : mem3 (loc.posPtr + e) = size + 1 := by
    dsimp only [mem3]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
  have hm3_arrS : mem3 (loc.arrPtr + size) = e := by
    dsimp only [mem3]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_self]
  have hm3_out (a : ℕ) (h1 : a ≠ loc.hb) (h2 : a ≠ loc.arrPtr + size)
      (h3 : a ≠ loc.posPtr + e) (h4 : a ≠ loc.lvlPtr + e) : mem3 a = mem2 a := by
    dsimp only [mem3]
    rw [Function.update_of_ne h1, Function.update_of_ne h4,
        Function.update_of_ne h3, Function.update_of_ne h2]
  clear_value mem3
  have hhdr3 : SelectHeapHeaderAt mem3 loc (size + 1) := fun j hj => by
    simp only [List.length_cons, List.length_nil] at hj
    cases j with
    | zero => simpa using hm3_hb
    | succ m =>
      rw [hm3_out _ (by omega) (by omega) (by omega) (by omega), hmem2_out _ (by omega)]
      have h0 := hhdr (m + 1) (by simp only [List.length_cons, List.length_nil]; omega)
      simpa using h0
  have hne_arr (p : ℕ) (hp : p < size) : mem (loc.arrPtr + p) ≠ e := fun h => by
    have := hbij.pos_arr_ne_zero hp; rw [h] at this; exact this hpos0
  have hbij3 : SelectHeapBijection mem3 loc (size + 1) := by
    refine ⟨by omega, fun p hp => ?_, fun p hp => ?_, fun e' he' => ?_⟩
    · by_cases hps : p = size
      · subst p; rw [hm3_arrS]; exact heCap
      · rw [hm3_out _ (by omega) (by omega) (by omega) (by omega), hmem2_out _ (by omega)]
        exact hbij.2.1 p (by omega)
    · by_cases hps : p = size
      · subst p; rw [hm3_arrS, hm3_posE]
      · have hpe := hne_arr p (by omega)
        have hpCap := hbij.2.1 p (by omega)
        have ha3 : mem3 (loc.arrPtr + p) = mem (loc.arrPtr + p) :=
          (hm3_out _ (by omega) (by omega) (by omega) (by omega)).trans (hmem2_out _ (by omega))
        rw [ha3, hm3_out (loc.posPtr + mem (loc.arrPtr + p)) (by omega) (by omega) (by omega) (by omega),
            hmem2_out _ (by omega)]
        exact hbij.2.2.1 p (by omega)
    · by_cases hee : e' = e
      · subst e'; right; rw [hm3_posE]
        exact ⟨by omega, by simpa only [Nat.add_sub_cancel] using hm3_arrS⟩
      · rw [hm3_out (loc.posPtr + e') (by omega) (by omega) (by omega) (by omega), hmem2_out _ (by omega)]
        by_cases hp0 : mem (loc.posPtr + e') = 0
        · exact Or.inl hp0
        · rcases hbij.2.2.2 e' he' with h0 | ⟨hle, harr⟩
          · exact Or.inl h0
          · have := hbij.1
            exact Or.inr ⟨by omega, by
              rw [hm3_out _ (by omega) (by omega) (by omega) (by omega), hmem2_out _ (by omega)]; exact harr⟩
  have hkeys3 : SelectHeapKeysValid mem3 loc h := fun e' he' hnz => by
    have hbd' := selectHeap_slot_bounds he'
    have hnm : ∀ j < loc.Lk, mem3 (loc.numBase + e' * loc.Lk + j) = mem2 (loc.numBase + e' * loc.Lk + j) :=
      fun j hj => hm3_out _ (by omega) (by omega) (by omega) (by omega)
    have hdm : ∀ j < loc.Lk, mem3 (loc.denBase + e' * loc.Lk + j) = mem2 (loc.denBase + e' * loc.Lk + j) :=
      fun j hj => hm3_out _ (by omega) (by omega) (by omega) (by omega)
    by_cases hee : e' = e
    · subst e'
      refine ⟨by rw [hm3_lvlE]; exact hlvlD,
        fun j hj => (hnm j hj).trans_lt (hvnE2 j hj),
        fun j hj => (hdm j hj).trans_lt (hvdE2 j hj), ?_⟩
      have hden3 : loc.readDen mem3 h e = loc.readDen mem2 h e := Num.intVal_congr hdm
      rw [hden3, hdenE2]; exact hdPos
    · have hnz0 : mem (loc.posPtr + e') ≠ 0 := by
        rwa [hm3_out _ (by omega) (by omega) (by omega) (by omega), hmem2_out _ (by omega)] at hnz
      obtain ⟨hl', hvn', hvd', hdp'⟩ := hkeys e' he' hnz0
      refine ⟨by rw [hm3_out _ (by omega) (by omega) (by omega) (by omega), hmem2_out _ (by omega)]; exact hl',
        fun j hj => by rw [hnm j hj, hvnOther2 e' he' hee j hj]; exact hvn' j hj,
        fun j hj => by rw [hdm j hj, hvdOther2 e' he' hee j hj]; exact hvd' j hj, ?_⟩
      have hden3 : loc.readDen mem3 h e' = loc.readDen mem2 h e' := Num.intVal_congr hdm
      rw [hden3, (hkeyOther2 e' he' hee).2]; exact hdp'
  obtain ⟨lists, hlists⟩ := hcand
  have hdlls3 : ∀ i ≤ loc.d, IsDoublyLinkedList mem3 loc.candPrev loc.candNext (loc.candHead + i) loc.cap (lists i) :=
    fun i hi => (hlists i hi).1.of_agree
      (by rw [hm3_out _ (by omega) (by omega) (by omega) (by omega), hmem2_out _ (by omega)])
      (fun y hy => by
        have hyCap : y < loc.cap := (hlists i hi).1.2.1 y hy
        rw [hm3_out _ (by omega) (by omega) (by omega) (by omega), hmem2_out _ (by omega)])
      (fun y hy => by
        have hyCap : y < loc.cap := (hlists i hi).1.2.1 y hy
        rw [hm3_out _ (by omega) (by omega) (by omega) (by omega), hmem2_out _ (by omega)])
  have heNotLists : ∀ i ≤ loc.d, e ∉ lists i := fun i hi heM =>
    ((hlists i hi).2 e).mp heM |>.2.1 hpos0
  have hdisjLists : ∀ i j, i ≤ loc.d → j ≤ loc.d → i ≠ j → ∀ x, x ∈ lists i → x ∉ lists j :=
    fun i j hi hj hij x hxi hxj => hij (((hlists i hi).2 x).mp hxi |>.2.2.symm.trans (((hlists j hj).2 x).mp hxj).2.2)
  refine runs_seq_call_flat (hcons (size + 1) lists) (vs := [loc.hb, lvl, e])
    (by simp [evalArgs, Expr.eval, hr0, hr1, hr2]) (by wram_words) ?_ ?_
  · exact ⟨lvl, e, rfl, hw16, by omega, hlvlD, heCap, hhdr3, hdlls3, heNotLists, hdisjLists⟩
  · intro _ mem4 pos4 hp4
    obtain ⟨_, hdlls4, hfr4⟩ := hp4
    change (∀ a, (a < loc.candHead ∨ loc.numBase ≤ a) → mem4 a = mem3 a) at hfr4
    have hm4_ge_num (a : ℕ) (ha : loc.numBase ≤ a) : mem4 a = mem2 a :=
      (hfr4 a (Or.inr ha)).trans (hm3_out a (by omega) (by omega) (by omega) (by omega))
    have hm4_eq_mem (a : ℕ) (ha : a < loc.candHead) (h1 : a ≠ loc.hb) (h2 : a ≠ loc.arrPtr + size)
        (h3 : a ≠ loc.posPtr + e) (h4 : a ≠ loc.lvlPtr + e) : mem4 a = mem a :=
      (hfr4 a (Or.inl ha)).trans ((hm3_out a h1 h2 h3 h4).trans (hmem2_out a (Or.inl (by omega))))
    have hm4_posE : mem4 (loc.posPtr + e) = size + 1 := (hfr4 _ (Or.inl (by omega))).trans hm3_posE
    have hm4_lvlE : mem4 (loc.lvlPtr + e) = lvl := (hfr4 _ (Or.inl (by omega))).trans hm3_lvlE
    obtain ⟨hhdr4, hbij4, hkeys4⟩ := selectHeap_struct_of_cand_frame hhdr3 hbij3 hkeys3 hfr4
    have hcand4 : SelectHeapCandLists mem4 loc := by
      refine ⟨fun i => if i = lvl then e :: lists i else lists i, fun i hi => ⟨hdlls4 i hi, fun e' => ?_⟩⟩
      dsimp only
      by_cases hil : i = lvl
      · subst i; simp only [↓reduceIte, List.mem_cons]
        constructor
        · rintro (rfl | hmem)
          · exact ⟨heCap, by rw [hm4_posE]; omega, hm4_lvlE⟩
          · obtain ⟨he', hnz', hl'⟩ := ((hlists lvl hi).2 e').mp hmem
            have hee : e' ≠ e := fun h => hnz' (h ▸ hpos0)
            exact ⟨he', by rw [hm4_eq_mem _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hnz',
              by rw [hm4_eq_mem _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hl'⟩
        · rintro ⟨he', hnz', hl'⟩
          by_cases hee : e' = e
          · exact Or.inl hee
          · right; refine ((hlists lvl hi).2 e').mpr ⟨he', ?_, ?_⟩
            · rwa [hm4_eq_mem _ (by omega) (by omega) (by omega) (by omega) (by omega)] at hnz'
            · rwa [hm4_eq_mem _ (by omega) (by omega) (by omega) (by omega) (by omega)] at hl'
      · simp only [hil, ↓reduceIte, (hlists i hi).2 e']
        constructor
        · rintro ⟨he', hnz', hl'⟩
          have hee : e' ≠ e := fun h => hnz' (h ▸ hpos0)
          exact ⟨he', by rw [hm4_eq_mem _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hnz',
            by rw [hm4_eq_mem _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hl'⟩
        · rintro ⟨he', hnz', hl'⟩
          have hee : e' ≠ e := fun h => by subst e'; rw [hm4_lvlE] at hl'; exact hil hl'.symm
          exact ⟨he', by rwa [hm4_eq_mem _ (by omega) (by omega) (by omega) (by omega) (by omega)] at hnz',
            by rwa [hm4_eq_mem _ (by omega) (by omega) (by omega) (by omega) (by omega)] at hl'⟩
    have hexc4 : SelectHeapOrderExceptUp mem4 loc h (size + 1) size := by
      refine selectHeap_exceptUp_of_append hbij hord
        (fun p hp => hm4_eq_mem _ (by omega) (by omega) (by omega) (by omega) (by omega))
        (fun p hp q hq => ?_)
      have hpc := hbij.2.1 p hp; have hqc := hbij.2.1 q hq
      have hEq (e' : ℕ) (he' : e' < loc.cap) :
          loc.readNum mem4 h e' = loc.readNum mem2 h e' ∧
          loc.readDen mem4 h e' = loc.readDen mem2 h e' := by
        have hb' := selectHeap_slot_bounds he'
        exact ⟨Num.intVal_congr fun j hj => hm4_ge_num _ (by omega),
          Num.intVal_congr fun j hj => hm4_ge_num _ (by omega)⟩
      unfold SelectHeapLoc.edgeBetter
      rw [(hEq _ hpc).1, (hEq _ hpc).2, (hEq _ hqc).1, (hEq _ hqc).2,
          (hkeyOther2 _ hpc (hne_arr p hp)).1, (hkeyOther2 _ hpc (hne_arr p hp)).2,
          (hkeyOther2 _ hqc (hne_arr q hq)).1, (hkeyOther2 _ hqc (hne_arr q hq)).2]
    have hz4 : ZeroFrom mem4 scratch := fun a ha => (hm4_ge_num a (by omega)).trans (hz2 a ha)
    have hspUp := heapSiftUpSpace_le_heapRebalanceSpace hszLt (Lk := loc.Lk)
    refine runs_seq_call_flat hup (vs := [loc.hb, size, scratch])
      (by simp [evalArgs, Expr.eval, hr0, hr5]) (by wram_words) ?_ ?_
    · exact ⟨size, scratch, rfl, hw16, hendLe, hhdr4, hbij4, hkeys4, hcand4, hexc4, hz4, by omega⟩
    · intro ret mem5 pos5 hp5
      obtain ⟨hlo5, hhi5, hat5, hz5, hfr5, hpos5⟩ := hp5
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hlo5 hhi5 hfr5
      have hretw : ret < 2 ^ w := by omega
      refine WordRAM.runs_ret_le (v := ret) (by eval_expr) ?_ ?_
      · dsimp only [heapUpsertContract]
        simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ, hpos0, ↓reduceIte]
        refine ⟨hlo5, by omega, hat5, hz5, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hpos5 e heCap, hm4_posE]; omega
        · rw [hfr5 _ (by omega) (Or.inr (by omega)), hm4_lvlE]
        · exact (Num.intVal_congr fun j hj => (hfr5 _ (by omega) (Or.inr (by omega))).trans
            (hm4_ge_num _ (by omega))).trans hnumE2
        · exact (Num.intVal_congr fun j hj => (hfr5 _ (by omega) (Or.inr (by omega))).trans
            (hm4_ge_num _ (by omega))).trans hdenE2
        · intro e' he' hne
          have hbd' := selectHeap_slot_bounds he'
          refine ⟨(hpos5 e' he').trans (by rw [hm4_eq_mem _ (by omega) (by omega) (by omega) (by omega) (by omega)]),
            (hfr5 _ (by omega) (Or.inr (by omega))).trans
              (hm4_eq_mem _ (by omega) (by omega) (by omega) (by omega) (by omega)),
            (Num.intVal_congr fun j hj => (hfr5 _ (by omega) (Or.inr (by omega))).trans
              (hm4_ge_num _ (by omega))).trans (hkeyOther2 e' he' hne).1,
            (Num.intVal_congr fun j hj => (hfr5 _ (by omega) (Or.inr (by omega))).trans
              (hm4_ge_num _ (by omega))).trans (hkeyOther2 e' he' hne).2⟩
        · intro a ha hout
          exact (hfr5 a ha (by omega)).trans ((hfr4 a (by omega)).trans
            ((hm3_out a (by omega) (by omega) (by omega) (by omega)).trans (hmem2_out a (by omega))))
      · simp only [heapUpsertContract, candListConsContract, heapSiftUpContract,
          List.getD_cons_zero, List.getD_cons_succ, Expr.size, argsSize]
        omega

set_option maxHeartbeats 400000 in
/-- `heapUpsertBody` meets `heapUpsertContract` in `O((log(cap + 1) + 1) · (Lk^2 + 1))` steps. -/
theorem heapUpsert_meetsContract {w h proc copyTo siftUp rebal candCons candErase : ℕ}
    {loc : SelectHeapLoc} {size : ℕ} {p : Program}
    (hp : p.procs[proc]? = some (heapUpsertBody copyTo siftUp rebal candCons candErase))
    (hcopy : MeetsContract w p copyTo (copyLimbsToContract w))
    (hup : MeetsContract w p siftUp (heapSiftUpContract w h loc (size + 1)))
    (hrebal : MeetsContract w p rebal (heapRebalanceContract w h loc size))
    (hcons : ∀ size' lists, MeetsContract w p candCons (candListConsContract w loc size' lists))
    (herase : ∀ lists, MeetsContract w p candErase (candListEraseContract w loc size lists)) :
    MeetsContract w p proc (heapUpsertContract w h loc size) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨e, lvl, nPtr, dPtr, scratch, rfl, hw16, hendLe, heCap, hlvlD, hszCap, hnSc, hdSc,
    hnDisj, hdDisj, hvn, hvd, hnw, hdw, hdPos, hat, hz, hroom⟩ := hpre
  obtain ⟨hhdr, hbij, hkeys, hord, hcand⟩ := hat
  have hbdE := selectHeap_slot_bounds heCap
  have hhr := selectHeap_header_reads hhdr
  have hlvlHdr : mem (loc.hb + 6) = loc.lvlPtr := by simpa using hhdr 6 (by simp)
  have hlayout := selectHeap_layout_eqs loc
  have hw1 : 1 < 2 ^ w := (by omega)
  have hhbw : loc.hb < 2 ^ w := hwords loc.hb (by simp)
  have hew : e < 2 ^ w := hwords e (by simp)
  have hlvlw : lvl < 2 ^ w := hwords lvl (by simp)
  have hnpw : nPtr < 2 ^ w := hwords nPtr (by simp)
  have hdpw : dPtr < 2 ^ w := hwords dPtr (by simp)
  have hscw : scratch < 2 ^ w := hwords scratch (by simp)
  have hLkw : loc.Lk < 2 ^ w := by have hsp := keyCompareSpace_le_heapRebalanceSpace loc.cap loc.Lk; unfold keyCompareSpace at hsp; omega
  have harrW : loc.arrPtr < 2 ^ w := (by omega); have hposW : loc.posPtr < 2 ^ w := (by omega)
  have hlvlPtrW : loc.lvlPtr < 2 ^ w := (by omega); have hnumW : loc.numBase < 2 ^ w := (by omega)
  have hdenW : loc.denBase < 2 ^ w := (by omega); have heLkW : e * loc.Lk < 2 ^ w := (by omega)
  have hneW : loc.numBase + e * loc.Lk < 2 ^ w := (by omega); have hdeW : loc.denBase + e * loc.Lk < 2 ^ w := (by omega)
  have hslotDisj (e' : ℕ) (he' : e' < loc.cap) (hne : e' ≠ e) (j : ℕ) (hj : j < loc.Lk) :
      e' * loc.Lk + j < e * loc.Lk ∨ e * loc.Lk + loc.Lk ≤ e' * loc.Lk + j := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · left; have := Nat.mul_le_mul_right loc.Lk hlt; rw [Nat.succ_mul] at this; omega
    · right; have := Nat.mul_le_mul_right loc.Lk hgt; rw [Nat.succ_mul] at this; omega
  apply runs_start_le
  dsimp only [startState]
  unfold heapUpsertBody
  simp only [shLkOff, shArrOff, shPosOff, shLvlOff, shNumOff, shDenOff]
  refine runs_seq_assign_flat (v := loc.Lk) (by eval_expr; exact hhr.2.1) ?_
  refine runs_seq_assign_flat (v := loc.arrPtr) (by eval_expr; exact hhr.2.2.1) ?_
  refine runs_seq_assign_flat (v := loc.posPtr) (by eval_expr; exact hhr.2.2.2.1) ?_
  refine runs_seq_assign_flat (v := loc.lvlPtr) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := loc.numBase) (by eval_expr; exact hhr.2.2.2.2.1) ?_
  refine runs_seq_assign_flat (v := loc.denBase) (by eval_expr; exact hhr.2.2.2.2.2) ?_
  -- Copy numerator limbs into `numBase + e * Lk`
  refine runs_seq_call_flat hcopy (vs := [nPtr, loc.numBase + e * loc.Lk, loc.Lk])
    (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨nPtr, loc.numBase + e * loc.Lk, loc.Lk, rfl, hw1, by omega, by omega, by omega, hnw⟩
  · intro _ mem1 pos1 hp1
    obtain ⟨_, hcp1, hfr1⟩ := hp1
    change (∀ i < loc.Lk, mem1 (loc.numBase + e * loc.Lk + i) = mem (nPtr + i)) at hcp1
    change (∀ a, (a < loc.numBase + e * loc.Lk ∨ loc.numBase + e * loc.Lk + loc.Lk ≤ a) → mem1 a = mem a) at hfr1
    -- Copy denominator limbs into `denBase + e * Lk`
    refine runs_seq_call_flat hcopy (vs := [dPtr, loc.denBase + e * loc.Lk, loc.Lk])
      (by eval_expr) (by wram_words) ?_ ?_
    · refine ⟨dPtr, loc.denBase + e * loc.Lk, loc.Lk, rfl, hw1, by omega, by omega, by omega, ?_⟩
      intro i hi; rw [hfr1 _ (by omega)]; exact hdw i hi
    · intro _ mem2 pos2 hp2
      obtain ⟨_, hcp2, hfr2⟩ := hp2
      change (∀ i < loc.Lk, mem2 (loc.denBase + e * loc.Lk + i) = mem1 (dPtr + i)) at hcp2
      change (∀ a, (a < loc.denBase + e * loc.Lk ∨ loc.denBase + e * loc.Lk + loc.Lk ≤ a) → mem2 a = mem1 a) at hfr2
      have hmem2_out (a : ℕ) (ha : a < loc.numBase ∨ loc.endAddr ≤ a) : mem2 a = mem a :=
        (hfr2 a (by omega)).trans (hfr1 a (by omega))
      have hnumE2 : loc.readNum mem2 h e = Num.intVal mem nPtr h loc.Lk :=
        Num.intVal_congr fun i hi => (hfr2 _ (by omega)).trans (hcp1 i hi)
      have hdenE2 : loc.readDen mem2 h e = Num.intVal mem dPtr h loc.Lk :=
        Num.intVal_congr fun i hi => (hcp2 i hi).trans (hfr1 _ (by omega))
      have hvnE2 : Num.Valid mem2 (loc.numBase + e * loc.Lk) h loc.Lk := fun i hi => by
        rw [hfr2 _ (by omega), hcp1 i hi]; exact hvn i hi
      have hvdE2 : Num.Valid mem2 (loc.denBase + e * loc.Lk) h loc.Lk := fun i hi => by
        rw [hcp2 i hi, hfr1 _ (by omega)]; exact hvd i hi
      have hkeyOther2 (e' : ℕ) (he' : e' < loc.cap) (hne : e' ≠ e) :
          loc.readNum mem2 h e' = loc.readNum mem h e' ∧
          loc.readDen mem2 h e' = loc.readDen mem h e' := by
        constructor
        · refine Num.intVal_congr fun j hj => ?_
          have hdis := hslotDisj e' he' hne j hj
          exact (hfr2 _ (by have := selectHeap_slot_bounds he'; omega)).trans (hfr1 _ (by omega))
        · refine Num.intVal_congr fun j hj => ?_
          have hdis := hslotDisj e' he' hne j hj
          exact (hfr2 _ (by omega)).trans (hfr1 _ (by have := selectHeap_slot_bounds he'; omega))
      have hedgeOther2 (e₁ e₂ : ℕ) (h1 : e₁ < loc.cap) (h2 : e₂ < loc.cap)
          (hne1 : e₁ ≠ e) (hne2 : e₂ ≠ e) :
          loc.edgeBetter mem2 h e₁ e₂ = loc.edgeBetter mem h e₁ e₂ := by
        unfold SelectHeapLoc.edgeBetter
        rw [(hkeyOther2 e₁ h1 hne1).1, (hkeyOther2 e₁ h1 hne1).2,
            (hkeyOther2 e₂ h2 hne2).1, (hkeyOther2 e₂ h2 hne2).2]
      have hz2 : ZeroFrom mem2 scratch := fun a ha => (hmem2_out a (Or.inr (by omega))).trans (hz a ha)
      have hposE2 : mem2 (loc.posPtr + e) = mem (loc.posPtr + e) := hmem2_out _ (by omega)
      have hposEW : mem (loc.posPtr + e) < 2 ^ w := by
        rcases hbij.2.2.2 e heCap with h0 | ⟨hle, _⟩
        · omega
        · have := hbij.1; omega
      refine runs_seq_assign_flat (v := mem (loc.posPtr + e)) (by eval_expr) ?_
      -- Split on whether `e` is newly inserted (`pos[e] = 0`) or already present (`pos[e] ≠ 0`)
      by_cases hpos0 : mem (loc.posPtr + e) = 0
      · have hszLt : size < loc.cap := hszCap hpos0
        have hcostUp := heapSiftUpCost_le_heapRebalanceCost hszLt (Lk := loc.Lk)
        refine WordRAM.runs_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, hpos0, hw1])
          ?_ (fun h => absurd h (by decide))
        intro _
        apply heapUpsert_insert_branch hup hcons hw16 hendLe heCap hlvlD hszLt hroom
          ⟨hhdr, hbij, hkeys, hord, hcand⟩ hpos0 hz2 hmem2_out hnumE2 hdenE2 hvnE2 hvdE2 hdPos
          hkeyOther2
          (fun e' he' hne j hj => by
            have hdis := hslotDisj e' he' hne j hj
            have := selectHeap_slot_bounds he'
            exact (hfr2 _ (by omega)).trans (hfr1 _ (by omega)))
          (fun e' he' hne j hj => by
            have hdis := hslotDisj e' he' hne j hj
            have := selectHeap_slot_bounds he'
            exact (hfr2 _ (by omega)).trans (hfr1 _ (by omega)))
          (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
        simp only [heapUpsertCost, copyLimbsToContract, List.getD_cons_zero, List.getD_cons_succ,
          Expr.size, argsSize]
        omega
      · -- `pos[e] ≠ 0`: update existing edge at `k = pos[e] - 1`
        rcases hbij.2.2.2 e heCap with h0 | ⟨hkLe, harrK⟩
        · exact (hpos0 h0).elim
        let k := mem (loc.posPtr + e) - 1
        have hkLt : k < size := by omega
        have hkW : k < 2 ^ w := by have := hbij.1; omega
        have holdLvl := mem (loc.lvlPtr + e)
        have holdLvlD : mem (loc.lvlPtr + e) ≤ loc.d := (hkeys e heCap hpos0).1
        have holdLvlW : mem (loc.lvlPtr + e) < 2 ^ w := by omega
        have hlvlE2 : mem2 (loc.lvlPtr + e) = mem (loc.lvlPtr + e) := hmem2_out _ (by omega)
        refine WordRAM.runs_cond_le (v := 0) (by simp [Expr.eval, BinOp.eval, hpos0, show 0 < 2 ^ w by omega])
          (fun h => absurd rfl h) ?_
        intro _
        refine runs_seq_assign_flat (v := k) (by dsimp only [k]; eval_expr) ?_
        refine runs_seq_assign_flat (v := mem (loc.lvlPtr + e)) (by eval_expr) ?_
        -- Shared continuation after candidate-list level update: calls `rebal [hb, k, scratch]`
        have hcontRebal : ∀ (mem4 : ℕ → ℕ) (regs4 : ℕ → ℕ) (pos4 k0 : ℕ),
            regs4 0 = loc.hb → regs4 5 = scratch → regs4 14 = k →
            SelectHeapHeaderAt mem4 loc size →
            SelectHeapBijection mem4 loc size →
            SelectHeapCandLists mem4 loc →
            mem4 (loc.lvlPtr + e) = lvl →
            (∀ e' < loc.cap, e' ≠ e → mem4 (loc.lvlPtr + e') = mem (loc.lvlPtr + e')) →
            (∀ a, (a < loc.lvlPtr ∨ loc.numBase ≤ a) → mem4 a = mem2 a) →
            k0 + heapRebalanceCost loc.cap loc.Lk + 30 ≤ heapUpsertCost loc.cap loc.Lk →
            ∃ o st' c, Runs w p ω (.call 15 rebal [.reg 0, .reg 14, .reg 5] ;; .ret (.reg 15))
              ⟨mem4, regs4, pos4⟩ o st' c ∧
              (heapUpsertContract w h loc size).post [loc.hb, e, lvl, nPtr, dPtr, scratch] mem o.value st'.mem ∧
              k0 + c ≤ (heapUpsertContract w h loc size).cost [loc.hb, e, lvl, nPtr, dPtr, scratch] mem := by
          intro mem4 regs4 pos4 k0 hr0 hr5 hr14 hhdr4 hbij4 hcand4 hlvl4 hlvlOther4 hfr4 hk0
          have hkeys4 : SelectHeapKeysValid mem4 loc h := fun e' he' hnz => by
            have hbd' := selectHeap_slot_bounds he'
            have hnm : ∀ j < loc.Lk, mem4 (loc.numBase + e' * loc.Lk + j) = mem2 (loc.numBase + e' * loc.Lk + j) :=
              fun j hj => hfr4 _ (Or.inr (by omega))
            have hdm : ∀ j < loc.Lk, mem4 (loc.denBase + e' * loc.Lk + j) = mem2 (loc.denBase + e' * loc.Lk + j) :=
              fun j hj => hfr4 _ (Or.inr (by omega))
            by_cases hee : e' = e
            · subst e'
              refine ⟨by rw [hlvl4]; exact hlvlD,
                fun j hj => (hnm j hj).trans_lt (hvnE2 j hj),
                fun j hj => (hdm j hj).trans_lt (hvdE2 j hj), ?_⟩
              have hden4 : loc.readDen mem4 h e = loc.readDen mem2 h e := Num.intVal_congr hdm
              rw [hden4, hdenE2]; exact hdPos
            · have hnz0 : mem (loc.posPtr + e') ≠ 0 := by
                rwa [hfr4 _ (Or.inl (by omega)), hmem2_out _ (by omega)] at hnz
              obtain ⟨hl', hvn', hvd', hdp'⟩ := hkeys e' he' hnz0
              refine ⟨by rw [hlvlOther4 e' he' hee]; exact hl',
                fun j hj => by
                  have hdis := hslotDisj e' he' hee j hj
                  rw [hnm j hj, hfr2 _ (by omega), hfr1 _ (by omega)]; exact hvn' j hj,
                fun j hj => by
                  have hdis := hslotDisj e' he' hee j hj
                  rw [hdm j hj, hfr2 _ (by omega), hfr1 _ (by omega)]; exact hvd' j hj, ?_⟩
              have hden4 : loc.readDen mem4 h e' = loc.readDen mem2 h e' := Num.intVal_congr hdm
              rw [hden4, (hkeyOther2 e' he' hee).2]; exact hdp'
          have harr4 (p : ℕ) (hp : p < size) : mem4 (loc.arrPtr + p) = mem (loc.arrPtr + p) := by
            have := hbij.1; exact (hfr4 _ (Or.inl (by omega))).trans (hmem2_out _ (by omega))
          have hne_e (p : ℕ) (hp : p < size) (hpk : p ≠ k) : mem (loc.arrPtr + p) ≠ e := fun heq => by
            have := hbij.arr_inj hp hkLt (heq.trans harrK.symm); exact hpk this
          have hedge4 (p q : ℕ) (hp : p < size) (hq : q < size) (hpk : p ≠ k) (hqk : q ≠ k) :
              loc.edgeBetter mem4 h (mem4 (loc.arrPtr + p)) (mem4 (loc.arrPtr + q)) =
                loc.edgeBetter mem h (mem (loc.arrPtr + p)) (mem (loc.arrPtr + q)) := by
            rw [harr4 p hp, harr4 q hq]
            have hpc := hbij.2.1 p hp; have hqc := hbij.2.1 q hq
            have hEq (e' : ℕ) (he' : e' < loc.cap) :
                loc.readNum mem4 h e' = loc.readNum mem2 h e' ∧
                loc.readDen mem4 h e' = loc.readDen mem2 h e' := by
              have hb' := selectHeap_slot_bounds he'
              exact ⟨Num.intVal_congr fun j hj => hfr4 _ (Or.inr (by omega)),
                Num.intVal_congr fun j hj => hfr4 _ (Or.inr (by omega))⟩
            unfold SelectHeapLoc.edgeBetter
            rw [(hEq _ hpc).1, (hEq _ hpc).2, (hEq _ hqc).1, (hEq _ hqc).2]
            exact hedgeOther2 _ _ hpc hqc (hne_e p hp hpk) (hne_e q hq hqk)
          have hother4 : ∀ p, 0 < p → p < size → p ≠ k → (p - 1) / 2 ≠ k →
              loc.edgeBetter mem4 h (mem4 (loc.arrPtr + (p - 1) / 2)) (mem4 (loc.arrPtr + p)) = true := by
            intro p hp0 hp hpk hpp
            rw [hedge4 _ p (by omega) hp hpp hpk]; exact hord p hp0 hp
          have hskip4 : 0 < k → ∀ c < size, (c - 1) / 2 = k →
              loc.edgeBetter mem4 h (mem4 (loc.arrPtr + (k - 1) / 2)) (mem4 (loc.arrPtr + c)) = true := by
            intro hk0' c hc hck
            rw [hedge4 _ c (by omega) hc (by omega) (by omega)]
            exact selectHeapOrder_grandparent_beats_child hbij hkeys hord hk0' hkLt hc hck
          have hz4 : ZeroFrom mem4 scratch := fun a ha => (hfr4 a (Or.inr (by omega))).trans (hz2 a ha)
          refine runs_seq_call_flat hrebal (vs := [loc.hb, k, scratch])
            (by simp [evalArgs, Expr.eval, hr0, hr14, hr5]) (by wram_words) ?_ ?_
          · exact ⟨k, scratch, rfl, hw16, hendLe, hkLt, hhdr4, hbij4, hkeys4, hcand4, hother4, hskip4, hz4, hroom⟩
          · intro ret mem5 pos5 hp5
            obtain ⟨hlo5, hhi5, hat5, hz5, hfr5, hpos5⟩ := hp5
            simp only [List.getD_cons_zero, List.getD_cons_succ] at hlo5 hhi5 hfr5
            have hretw : ret < 2 ^ w := by omega
            refine WordRAM.runs_ret_le (v := ret) (by eval_expr) ?_ ?_
            · dsimp only [heapUpsertContract]
              simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ, hpos0, ↓reduceIte]
              refine ⟨hlo5, hhi5, hat5, hz5, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · rw [hpos5 e heCap, hfr4 _ (Or.inl (by omega)), hmem2_out _ (by omega)]; exact hpos0
              · rw [hfr5 _ (by omega) (Or.inr (by omega)), hlvl4]
              · exact (Num.intVal_congr fun j hj => (hfr5 _ (by omega) (Or.inr (by omega))).trans
                  (hfr4 _ (Or.inr (by omega)))).trans hnumE2
              · exact (Num.intVal_congr fun j hj => (hfr5 _ (by omega) (Or.inr (by omega))).trans
                  (hfr4 _ (Or.inr (by omega)))).trans hdenE2
              · intro e' he' hne
                have hbd' := selectHeap_slot_bounds he'
                refine ⟨(hpos5 e' he').trans (by rw [hfr4 _ (Or.inl (by omega)), hmem2_out _ (by omega)]),
                  (hfr5 _ (by omega) (Or.inr (by omega))).trans (hlvlOther4 e' he' hne),
                  (Num.intVal_congr fun j hj => (hfr5 _ (by omega) (Or.inr (by omega))).trans
                    (hfr4 _ (Or.inr (by omega)))).trans (hkeyOther2 e' he' hne).1,
                  (Num.intVal_congr fun j hj => (hfr5 _ (by omega) (Or.inr (by omega))).trans
                    (hfr4 _ (Or.inr (by omega)))).trans (hkeyOther2 e' he' hne).2⟩
              · intro a ha hout
                exact (hfr5 a ha (by omega)).trans ((hfr4 a (by omega)).trans (hmem2_out a (by omega)))
            · simp only [heapUpsertContract, heapRebalanceContract, Expr.size, argsSize]; omega
        -- Check whether `lvl` changed
        obtain ⟨hhdr2, hbij2⟩ := selectHeap_hdr_bij_of_frame hhdr hbij (fun a ha => hmem2_out a (Or.inl (by omega)))
        obtain ⟨lists, hlists⟩ := hcand
        have hdlls2 : ∀ i ≤ loc.d, IsDoublyLinkedList mem2 loc.candPrev loc.candNext (loc.candHead + i) loc.cap (lists i) :=
          fun i hi => (hlists i hi).1.of_agree (hmem2_out _ (by omega))
            (fun y hy => by have := (hlists i hi).1.2.1 y hy; exact hmem2_out _ (by omega))
            (fun y hy => by have := (hlists i hi).1.2.1 y hy; exact hmem2_out _ (by omega))
        by_cases hsameLvl : mem (loc.lvlPtr + e) = lvl
        · refine WordRAM.runs_seq_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, hsameLvl, hw1]) ?_ (fun h => absurd h (by decide))
          intro _
          refine runs_seq_nop_le ?_
          have hcand2 : SelectHeapCandLists mem2 loc :=
            ⟨lists, fun i hi => ⟨hdlls2 i hi, fun e' => by
              rw [(hlists i hi).2 e']; constructor
              · rintro ⟨he', hnz', hl'⟩; exact ⟨he', by rwa [hmem2_out _ (by omega)], (hmem2_out _ (by omega)).trans hl'⟩
              · rintro ⟨he', hnz', hl'⟩; exact ⟨he', by rwa [← hmem2_out _ (by omega)], (hmem2_out _ (by omega)).symm.trans hl'⟩⟩⟩
          apply hcontRebal mem2 _ pos2 _ (by simp) (by simp) (by simp) hhdr2 hbij2 hcand2
            (hlvlE2.trans hsameLvl) (fun e' he' _ => hmem2_out _ (by omega)) (fun _ _ => rfl)
            (by simp only [heapUpsertCost, copyLimbsToContract, List.getD_cons_zero, List.getD_cons_succ, Expr.size, argsSize]; omega)
        · refine WordRAM.runs_seq_cond_le (v := 0) (by simp [Expr.eval, BinOp.eval, hsameLvl, show 0 < 2 ^ w by omega])
            (fun h => absurd rfl h) ?_
          intro _
          have heMemOld : e ∈ lists (mem (loc.lvlPtr + e)) :=
            ((hlists _ holdLvlD).2 e).mpr ⟨heCap, hpos0, rfl⟩
          have hdisjLists : ∀ i j, i ≤ loc.d → j ≤ loc.d → i ≠ j → ∀ x, x ∈ lists i → x ∉ lists j :=
            fun i j hi hj hij x hxi hxj => hij (((hlists i hi).2 x).mp hxi |>.2.2.symm.trans (((hlists j hj).2 x).mp hxj).2.2)
          -- Call `candErase [hb, oldLvl, e]`
          refine runs_seq_assoc_le ?_
          refine runs_seq_call_flat (herase lists) (vs := [loc.hb, mem (loc.lvlPtr + e), e])
            (by eval_expr) (by wram_words) ?_ ?_
          · exact ⟨mem (loc.lvlPtr + e), e, rfl, hw16, by omega, holdLvlD, heCap, heMemOld, hhdr2, hdlls2, hdisjLists⟩
          · intro _ mem3 pos3 hp3
            obtain ⟨_, hdlls3, hfr3⟩ := hp3
            change (∀ a, (a < loc.candHead ∨ loc.numBase ≤ a) → mem3 a = mem2 a) at hfr3
            -- Store `lvl[e] := lvl`
            refine runs_seq_assoc_le ?_
            refine runs_seq_store_flat (by eval_expr) (by eval_expr) ?_
            set mem3b := Function.update mem3 (loc.lvlPtr + e) lvl
            have hm3b_lvlE : mem3b (loc.lvlPtr + e) = lvl := Function.update_self ..
            have hm3b_ne (a : ℕ) (hne : a ≠ loc.lvlPtr + e) : mem3b a = mem3 a := Function.update_of_ne hne ..
            clear_value mem3b
            let lists3 : ℕ → List ℕ := fun i => if i = mem (loc.lvlPtr + e) then (lists i).erase e else lists i
            have hhdr3b : SelectHeapHeaderAt mem3b loc size := fun j hj => by
              simp only [List.length_cons, List.length_nil] at hj
              exact (hm3b_ne _ (by omega)).trans ((hfr3 _ (Or.inl (by omega))).trans
                (hhdr2 j (by simp only [List.length_cons, List.length_nil]; omega)))
            have hdlls3b : ∀ i ≤ loc.d, IsDoublyLinkedList mem3b loc.candPrev loc.candNext (loc.candHead + i) loc.cap (lists3 i) :=
              fun i hi => (hdlls3 i hi).of_agree (hm3b_ne _ (by omega))
                (fun y hy => by have := (hdlls3 i hi).2.1 y hy; exact hm3b_ne _ (by omega))
                (fun y hy => by have := (hdlls3 i hi).2.1 y hy; exact hm3b_ne _ (by omega))
            have heNot3 : ∀ i ≤ loc.d, e ∉ lists3 i := fun i hi heM => by
              dsimp only [lists3] at heM
              by_cases hil : i = mem (loc.lvlPtr + e)
              · simp only [hil, ↓reduceIte] at heM
                have hnd := (hlists _ hi).1.1
                have := List.nodup_iff_count_le_one.mp hnd e
                have hc1 : List.count e ((lists (mem (loc.lvlPtr + e))).erase e) =
                    List.count e (lists (mem (loc.lvlPtr + e))) - 1 := List.count_erase_self
                have hpos : 0 < List.count e ((lists (mem (loc.lvlPtr + e))).erase e) :=
                  List.count_pos_iff.mpr heM
                rw [← hil] at hc1 hpos; omega
              · simp only [hil, ↓reduceIte] at heM
                exact hdisjLists i _ hi holdLvlD hil e heM heMemOld
            have hdisj3 : ∀ i j, i ≤ loc.d → j ≤ loc.d → i ≠ j → ∀ x, x ∈ lists3 i → x ∉ lists3 j := by
              intro i j hi hj hij x hxi hxj
              have h1 : x ∈ lists i := by
                dsimp only [lists3] at hxi; split_ifs at hxi; exact List.mem_of_mem_erase hxi; exact hxi
              have h2 : x ∈ lists j := by
                dsimp only [lists3] at hxj; split_ifs at hxj; exact List.mem_of_mem_erase hxj; exact hxj
              exact hdisjLists i j hi hj hij x h1 h2
            -- Call `candCons [hb, lvl, e]`
            refine runs_seq_call_flat (hcons size lists3) (vs := [loc.hb, lvl, e])
              (by eval_expr) (by wram_words) ?_ ?_
            · exact ⟨lvl, e, rfl, hw16, by omega, hlvlD, heCap, hhdr3b, hdlls3b, heNot3, hdisj3⟩
            · intro _ mem4 pos4 hp4
              obtain ⟨_, hdlls4, hfr4⟩ := hp4
              change (∀ a, (a < loc.candHead ∨ loc.numBase ≤ a) → mem4 a = mem3b a) at hfr4
              have hfr4_out (a : ℕ) (ha : a < loc.lvlPtr ∨ loc.numBase ≤ a) : mem4 a = mem2 a :=
                (hfr4 a (by omega)).trans ((hm3b_ne a (by omega)).trans (hfr3 a (by omega)))
              obtain ⟨hhdr4, hbij4⟩ := selectHeap_hdr_bij_of_frame hhdr2 hbij2 (fun a ha => hfr4_out a (Or.inl ha))
              have hlvl4 : mem4 (loc.lvlPtr + e) = lvl := (hfr4 _ (Or.inl (by omega))).trans hm3b_lvlE
              have hlvlOther4 (e' : ℕ) (he' : e' < loc.cap) (hne : e' ≠ e) :
                  mem4 (loc.lvlPtr + e') = mem (loc.lvlPtr + e') :=
                (hfr4 _ (Or.inl (by omega))).trans ((hm3b_ne _ (by omega)).trans
                  ((hfr3 _ (Or.inl (by omega))).trans (hmem2_out _ (by omega))))
              have hpos4 (e' : ℕ) (he' : e' < loc.cap) : mem4 (loc.posPtr + e') = mem (loc.posPtr + e') :=
                (hfr4_out _ (Or.inl (by omega))).trans (hmem2_out _ (by omega))
              have hcand4 : SelectHeapCandLists mem4 loc := by
                refine ⟨fun i => if i = lvl then e :: lists3 i else lists3 i, fun i hi => ⟨hdlls4 i hi, fun e' => ?_⟩⟩
                dsimp only
                by_cases hee : e' = e
                · subst e'
                  constructor
                  · intro hmem
                    by_cases hil : i = lvl
                    · exact ⟨heCap, by rw [hpos4 e heCap]; exact hpos0, hlvl4.trans hil.symm⟩
                    · simp only [hil, ↓reduceIte] at hmem; exact (heNot3 i hi hmem).elim
                  · rintro ⟨_, _, hl'⟩
                    have hil : i = lvl := hl'.symm.trans hlvl4
                    simp only [hil, ↓reduceIte, List.mem_cons, true_or]
                · have hmem3 : e' ∈ lists3 i ↔ e' ∈ lists i := by
                    dsimp only [lists3]; split_ifs
                    · exact List.mem_erase_of_ne hee
                    · exact Iff.rfl
                  have hmem4 : e' ∈ (if i = lvl then e :: lists3 i else lists3 i) ↔ e' ∈ lists i := by
                    split_ifs
                    · simp [hee, hmem3]
                    · exact hmem3
                  rw [hmem4, (hlists i hi).2 e']
                  constructor
                  · rintro ⟨he', hnz', hl'⟩
                    exact ⟨he', by rw [hpos4 e' he']; exact hnz', (hlvlOther4 e' he' hee).trans hl'⟩
                  · rintro ⟨he', hnz', hl'⟩
                    exact ⟨he', by rwa [hpos4 e' he'] at hnz', (hlvlOther4 e' he' hee).symm.trans hl'⟩
              apply hcontRebal mem4 _ pos4 _ (by simp) (by simp) (by simp) hhdr4 hbij4 hcand4
                hlvl4 hlvlOther4 hfr4_out
                (by simp only [heapUpsertCost, copyLimbsToContract, candListEraseContract,
                  candListConsContract, List.getD_cons_zero, List.getD_cons_succ, Expr.size, argsSize]; omega)

end MinCostFlow.MinRatio
