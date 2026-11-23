module

public import MinCostFlow.MinRatio.WireSelectHeapCand
import WordRAM.Tactic
import Mathlib.Data.Nat.Log

/-!
# Select-heap word copy, rebalance, and upsert procedures

Implements and verifies three deterministic Word-RAM procedures on `SelectHeapLoc`:
1. `copyLimbsToBody` (`[src, dst, L]`): copies `L` words from `src` to `dst` in `O(L)` steps
   with zero scratch allocation.
2. `heapRebalanceBody cmp siftUp siftDown` (`[hb, k, scratch]`): restores `SelectHeapOrder`
   after modifying slot `k < size` via at most one comparison against `parent(k)` and one
   `siftUp` or `siftDown` call (`O((log(cap + 1) + 1) * (Lk^2 + 1))` steps).
3. `heapUpsertBody copyTo siftUp rebal candCons candErase` (`[hb, e, lvl, nPtr, dPtr, scratch]`):
   inserts or updates edge `e` at level `lvl` with key `(nPtr, dPtr)` in
   `O((log(cap + 1) + 1) * (Lk^2 + 1))` steps, maintaining full `SelectHeapAt`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num DynSpanner.Program

/-! ## 1. In-place `L`-word copy `copyLimbsToBody` -/

/-- Copy `L` words from `src` (`reg 0`) to `dst` (`reg 1`), with `L` in `reg 2`. -/
def copyLimbsToBody : Stmt :=
  forRange 3 (.const 0) (.reg 2)
    (.store (.bin .add (.reg 1) (.reg 3))
      (.load (.bin .add (.reg 0) (.reg 3)))) ;;
  .ret (.const 0)

theorem copyLimbsToBody_noRand : copyLimbsToBody.NoRand := by
  simp [copyLimbsToBody, forRange, forUp, Stmt.NoRand]

/-- Contract for `copyLimbsToBody`: requires disjoint ranges `[src, src + L)` and `[dst, dst + L)`. -/
def copyLimbsToContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ src dst L, args = [src, dst, L] ∧
      1 < 2 ^ w ∧ src + L < 2 ^ w ∧ dst + L < 2 ^ w ∧
      (src + L ≤ dst ∨ dst + L ≤ src) ∧
      (∀ i < L, mem (src + i) < 2 ^ w)
  post args mem ret mem' :=
    let src := args.getD 0 0
    let dst := args.getD 1 0
    let L := args.getD 2 0
    ret = 0 ∧
    (∀ i < L, mem' (dst + i) = mem (src + i)) ∧
    (∀ a, (a < dst ∨ dst + L ≤ a) → mem' a = mem a)
  cost args _ := 18 * args.getD 2 0 + 16

/-! ## 2. Shared single-sift rebalance `heapRebalanceBody` -/

/-- Rebalance slot `k` (`reg 1`) of heap `hb` (`reg 0`) using scratch `reg 2`.
Tests `k = 0` or compares `arr[k]` with `arr[(k - 1) / 2]` to choose `siftUp` vs `siftDown`. -/
def heapRebalanceBody (cmp siftUp siftDown : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0))
    (.call 3 siftDown [.reg 0, .const 0, .reg 2] ;; .ret (.reg 3))
    (.assign 4 (.bin .div (.bin .sub (.reg 1) (.const 1)) (.const 2)) ;;
     .assign 5 (.load (.bin .add (.reg 0) (.const shLkOff))) ;;
     .assign 6 (.load (.bin .add (.reg 0) (.const shArrOff))) ;;
     .assign 7 (.load (.bin .add (.reg 0) (.const shNumOff))) ;;
     .assign 8 (.load (.bin .add (.reg 0) (.const shDenOff))) ;;
     .assign 9 (.load (.bin .add (.reg 6) (.reg 1))) ;;
     .assign 10 (.load (.bin .add (.reg 6) (.reg 4))) ;;
     .call 11 cmp
       [.reg 9,
        .bin .add (.reg 7) (.bin .mul (.reg 9) (.reg 5)),
        .bin .add (.reg 8) (.bin .mul (.reg 9) (.reg 5)),
        .reg 10,
        .bin .add (.reg 7) (.bin .mul (.reg 10) (.reg 5)),
        .bin .add (.reg 8) (.bin .mul (.reg 10) (.reg 5)),
        .reg 5, .reg 2] ;;
     .assign 12 (.bin .add (.reg 2) (.bin .mul (.const 16) (.reg 5))) ;;
     .cond (.reg 11)
       (.call 13 siftUp [.reg 0, .reg 1, .reg 12] ;; .ret (.reg 13))
       (.call 13 siftDown [.reg 0, .reg 1, .reg 12] ;; .ret (.reg 13)))

theorem heapRebalanceBody_noRand (cmp siftUp siftDown : ℕ) :
    (heapRebalanceBody cmp siftUp siftDown).NoRand := by
  simp [heapRebalanceBody, Stmt.NoRand]

/-- Scratch space bound for `heapRebalanceBody` on a heap of capacity `cap`. -/
def heapRebalanceSpace (cap Lk : ℕ) : ℕ :=
  (2 * Nat.log 2 (cap + 1) + 1) * keyCompareSpace Lk

/-- Step cost bound for `heapRebalanceBody` on a heap of capacity `cap`. -/
def heapRebalanceCost (cap Lk : ℕ) : ℕ :=
  (Nat.log 2 (cap + 1) + 1) * (2 * keyCompareCost Lk + 240) + keyCompareCost Lk + 160

/-- Contract for `heapRebalanceBody`: given a heap of size `size` satisfying all structural
invariants and heap order except possibly at `k < size` (with grandparent beating children of `k`),
restores full `SelectHeapAt`. -/
def heapRebalanceContract (w h : ℕ) (loc : SelectHeapLoc) (size : ℕ) : Contract where
  pre args mem :=
    ∃ k scratch, args = [loc.hb, k, scratch] ∧
      16 < 2 ^ w ∧ loc.endAddr ≤ scratch ∧ k < size ∧
      SelectHeapHeaderAt mem loc size ∧
      SelectHeapBijection mem loc size ∧
      SelectHeapKeysValid mem loc h ∧
      SelectHeapCandLists mem loc ∧
      (∀ p, 0 < p → p < size → p ≠ k → (p - 1) / 2 ≠ k →
        loc.edgeBetter mem h (mem (loc.arrPtr + (p - 1) / 2)) (mem (loc.arrPtr + p)) = true) ∧
      (0 < k → ∀ c < size, (c - 1) / 2 = k →
        loc.edgeBetter mem h (mem (loc.arrPtr + (k - 1) / 2)) (mem (loc.arrPtr + c)) = true) ∧
      ZeroFrom mem scratch ∧
      scratch + heapRebalanceSpace loc.cap loc.Lk < 2 ^ w
  post args mem ret mem' :=
    let scratch := args.getD 2 0
    scratch ≤ ret ∧ ret ≤ scratch + heapRebalanceSpace loc.cap loc.Lk ∧
    SelectHeapAt mem' loc h size ∧
    ZeroFrom mem' ret ∧
    (∀ a < scratch, (a < loc.arrPtr ∨ loc.lvlPtr ≤ a) → mem' a = mem a) ∧
    (∀ e < loc.cap, mem' (loc.posPtr + e) ≠ 0 ↔ mem (loc.posPtr + e) ≠ 0)
  cost _ _ := heapRebalanceCost loc.cap loc.Lk

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num DynSpanner.Program

/-! ## 4. Verification of `copyLimbsToBody` -/

/-- `copyLimbsToBody` meets `copyLimbsToContract` in `18 * L + 16` steps. -/
theorem copyLimbsTo_meetsContract {w proc : ℕ} {p : Program}
    (hp : p.procs[proc]? = some copyLimbsToBody) :
    MeetsContract w p proc (copyLimbsToContract w) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨src, dst, L, rfl, hw1, hsrcW, hdstW, hdisj, hvals⟩ := hpre
  have hloop := Triple.forRange_const (p := p) (r := 3) (lo := .const 0) (hi := .reg 2)
    (body := .store (.bin .add (.reg 1) (.reg 3)) (.load (.bin .add (.reg 0) (.reg 3))))
    (P := fun st => st = startState [src, dst, L] mem pos)
    (Inv := fun i st => st.regs 0 = src ∧ st.regs 1 = dst ∧ st.regs 2 = L ∧ st.regs 3 = i ∧
      (∀ j < i, st.mem (dst + j) = mem (src + j)) ∧
      (∀ a, (a < dst ∨ dst + i ≤ a) → st.mem a = mem a))
    9 0 L (Nat.zero_le L) hw1 (fun _ => by omega)
    (fun st hst => by subst st; exact ⟨by eval_expr, by simp [startState]⟩)
    (fun _ _ _ _ hi => hi.2.2.2.1)
    (fun _ st _ _ hi => by have h2 := hi.2.2.1; eval_expr)
    (fun i _ hi => by
      intro st ω' hst
      rcases hst with ⟨h0, h1, h2, h3, hcopy, hout⟩
      have hread : st.mem (src + i) = mem (src + i) := hout _ (by omega)
      have hvalW : mem (src + i) < 2 ^ w := hvals i hi
      apply runs_start_le
      refine runs_store_le (by eval_expr) (by eval_expr) ?_ ?_
      · change (_ ∧ _) ∧ _
        refine ⟨⟨by simpa using h0, by simpa using h1, by simpa using h2, by simp, ?_, ?_⟩, h3⟩
        · intro j hj
          dsimp only
          by_cases hji : j = i
          · subst hji; simp [hread]
          · rw [Function.update_of_ne (by omega)]; exact hcopy j (by omega)
        · intro a ha
          dsimp only
          rw [Function.update_of_ne (by omega)]; exact hout a (by omega)
      · wram_cost)
  apply runs_start_le
  unfold copyLimbsToBody
  refine runs_seq_triple_le hloop rfl ?_
  intro st1 ⟨h0, h1, h2, _, hcopy, hout⟩
  refine WordRAM.runs_ret_le (v := 0) (by simp [Expr.eval, show 0 < 2 ^ w by omega]) ?_ ?_
  · dsimp only [copyLimbsToContract]
    exact ⟨rfl, hcopy, hout⟩
  · simp only [copyLimbsToContract, List.getD_cons_zero, List.getD_cons_succ, Expr.size, Nat.sub_zero]
    omega

/-! ## 5. Verification of `heapRebalanceBody` -/

/-- `heapRebalanceBody` meets `heapRebalanceContract`. -/
theorem heapRebalance_meetsContract {w h proc cmp siftUp siftDown : ℕ}
    {loc : SelectHeapLoc} {size : ℕ} {p : Program}
    (hp : p.procs[proc]? = some (heapRebalanceBody cmp siftUp siftDown))
    (hcmp : MeetsContract w p cmp (keyCompareContract w h))
    (hup : MeetsContract w p siftUp (heapSiftUpContract w h loc size))
    (hdown : MeetsContract w p siftDown (heapSiftDownContract w h loc size)) :
    MeetsContract w p proc (heapRebalanceContract w h loc size) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨k, scratch, rfl, hw16, hendLe, hkLt, hhdr, hbij, hkeys, hcand, hother, hskip, hz, hroom⟩ := hpre
  have hlogK : Nat.log 2 (k + 1) ≤ Nat.log 2 (loc.cap + 1) :=
    Nat.log_mono_right (by have := hbij.1; omega)
  have hlogS : Nat.log 2 size ≤ Nat.log 2 (loc.cap + 1) :=
    Nat.log_mono_right (by have := hbij.1; omega)
  have hspUp : keyCompareSpace loc.Lk + heapSiftUpSpace k loc.Lk ≤ heapRebalanceSpace loc.cap loc.Lk := by
    unfold heapSiftUpSpace heapRebalanceSpace
    have := Nat.mul_le_mul_right (keyCompareSpace loc.Lk) hlogK
    nlinarith
  have hspDn : keyCompareSpace loc.Lk + heapSiftDownSpace size k loc.Lk ≤ heapRebalanceSpace loc.cap loc.Lk := by
    unfold heapSiftDownSpace heapSiftDownDepth heapRebalanceSpace
    have hle : Nat.log 2 size - Nat.log 2 (k + 1) ≤ Nat.log 2 (loc.cap + 1) := by omega
    have := Nat.mul_le_mul_right (2 * keyCompareSpace loc.Lk) hle
    nlinarith
  have hcostUp : keyCompareCost loc.Lk + heapSiftUpCost k loc.Lk + 90 ≤ heapRebalanceCost loc.cap loc.Lk := by
    unfold heapSiftUpCost heapRebalanceCost
    have hmul := Nat.mul_le_mul_right (2 * keyCompareCost loc.Lk + 240) hlogK
    have h1 : Nat.log 2 (k + 1) * (keyCompareCost loc.Lk + 140) ≤
        Nat.log 2 (k + 1) * (2 * keyCompareCost loc.Lk + 240) :=
      Nat.mul_le_mul_left _ (by omega)
    nlinarith
  have hcostDn : keyCompareCost loc.Lk + heapSiftDownCost size k loc.Lk + 90 ≤ heapRebalanceCost loc.cap loc.Lk := by
    unfold heapSiftDownCost heapSiftDownDepth heapRebalanceCost
    have hle : Nat.log 2 size - Nat.log 2 (k + 1) ≤ Nat.log 2 (loc.cap + 1) := by omega
    have := Nat.mul_le_mul_right (2 * keyCompareCost loc.Lk + 240) hle
    nlinarith
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hhbw : loc.hb < 2 ^ w := hwords loc.hb (by simp)
  have hkw : k < 2 ^ w := hwords k (by simp)
  have hscw : scratch < 2 ^ w := hwords scratch (by simp)
  apply runs_start_le
  dsimp only [startState]
  unfold heapRebalanceBody
  simp only [shLkOff, shArrOff, shNumOff, shDenOff]
  by_cases hk0 : k = 0
  · subst hk0
    refine WordRAM.runs_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, hw1]) ?_ (fun h => absurd h (by decide))
    intro _
    have hexcDn := (selectHeap_except_of_replaceAt hkLt hbij hkeys hother hskip).2 (Or.inl rfl)
    refine runs_seq_call_flat hdown (vs := [loc.hb, 0, scratch]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨0, scratch, rfl, hw16, hendLe, hhdr, hbij, hkeys, hcand, hexcDn, hz, by omega⟩
    · intro ret mem1 pos1 hpost
      obtain ⟨hlo, hhi, hat, hz1, hfr, hpos⟩ := hpost
      change scratch ≤ ret at hlo
      change ret ≤ scratch + heapSiftDownSpace size 0 loc.Lk at hhi
      have hretw : ret < 2 ^ w := by omega
      refine WordRAM.runs_ret_le (v := ret) (by eval_expr) ?_ ?_
      · dsimp only [heapRebalanceContract]
        simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ]
        exact ⟨hlo, by omega, hat, hz1, hfr, hpos⟩
      · simp only [heapRebalanceContract, heapSiftDownContract, List.getD_cons_zero,
          List.getD_cons_succ, Expr.size, argsSize]
        omega
  · have hkPos : 0 < k := Nat.pos_of_ne_zero hk0
    let par := (k - 1) / 2
    have hparLt : par < size := by omega
    have hekCap := hbij.2.1 k hkLt
    have hepCap := hbij.2.1 par hparLt
    have hbdK := selectHeap_slot_bounds hekCap
    have hbdP := selectHeap_slot_bounds hepCap
    have hhdrLt : loc.hb + 14 ≤ loc.endAddr := hbdK.2.2.2.2
    have hkCap : k < loc.cap := lt_of_lt_of_le hkLt hbij.1
    have hparCap : par < loc.cap := lt_of_lt_of_le hparLt hbij.1
    have hhdrR := selectHeap_header_reads hhdr
    have h16Lkw : 16 * loc.Lk < 2 ^ w := by unfold keyCompareSpace at hspUp; omega
    have hLkw : loc.Lk < 2 ^ w := by omega
    have hsc1w : scratch + 16 * loc.Lk < 2 ^ w := by unfold keyCompareSpace at hspUp; omega
    have hparw : par < 2 ^ w := by omega
    have harrW : loc.arrPtr < 2 ^ w := by omega
    have hnumW : loc.numBase < 2 ^ w := by omega
    have hdenW : loc.denBase < 2 ^ w := by omega
    have hekw : mem (loc.arrPtr + k) < 2 ^ w := by omega
    have hepw : mem (loc.arrPtr + par) < 2 ^ w := by omega
    have hnkw : loc.numBase + mem (loc.arrPtr + k) * loc.Lk < 2 ^ w := by omega
    have hdkw : loc.denBase + mem (loc.arrPtr + k) * loc.Lk < 2 ^ w := by omega
    have hnpw : loc.numBase + mem (loc.arrPtr + par) * loc.Lk < 2 ^ w := by omega
    have hdpw : loc.denBase + mem (loc.arrPtr + par) * loc.Lk < 2 ^ w := by omega
    have hkeyK := hkeys _ hekCap (hbij.pos_arr_ne_zero hkLt)
    have hkeyP := hkeys _ hepCap (hbij.pos_arr_ne_zero hparLt)
    refine WordRAM.runs_cond_le (v := 0) (by simp [Expr.eval, BinOp.eval, hk0, show 0 < 2 ^ w by omega])
      (fun h => absurd rfl h) ?_
    intro _
    refine runs_seq_assign_flat (v := par)
      (by simp [Expr.eval, BinOp.eval, hw1, hw2, show k - 1 < 2 ^ w by omega, hparw, par]) ?_
    refine runs_seq_assign_flat (v := loc.Lk) (by eval_expr; exact hhdrR.2.1) ?_
    refine runs_seq_assign_flat (v := loc.arrPtr) (by eval_expr; exact hhdrR.2.2.1) ?_
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
        hkeyK.2.1, hkeyK.2.2.1, hkeyP.2.1, hkeyP.2.2.1, hz, by unfold keyCompareSpace at hspUp ⊢; omega⟩
    · intro bit mem1 pos1 hpCmp
      obtain ⟨hbit, hf1, hz1⟩ := hpCmp
      change bit = (if loc.edgeBetter mem h (mem (loc.arrPtr + k)) (mem (loc.arrPtr + par)) then 1 else 0) at hbit
      change (∀ x < scratch, mem1 x = mem x) at hf1
      change ZeroFrom mem1 (scratch + 16 * loc.Lk) at hz1
      have hbitw : bit < 2 ^ w := by rw [hbit]; split <;> omega
      obtain ⟨hhdr1, hbij1, hkeys1, hcand1, hedge1⟩ :=
        selectHeap_struct_of_agree_lt hendLe hf1 hhdr hbij hkeys hcand
      have harr_lt (p : ℕ) (hp : p < size) : loc.arrPtr + p < scratch := by
        have := hbij.1; omega
      have hother1 : ∀ p, 0 < p → p < size → p ≠ k → (p - 1) / 2 ≠ k →
          loc.edgeBetter mem1 h (mem1 (loc.arrPtr + (p - 1) / 2)) (mem1 (loc.arrPtr + p)) = true := by
        intro p hp0 hp hpk hpp
        rw [hf1 _ (harr_lt _ (by omega)), hf1 _ (harr_lt p hp),
            hedge1 _ _ (hbij.2.1 _ (by omega)) (hbij.2.1 p hp)]
        exact hother p hp0 hp hpk hpp
      have hskip1 : 0 < k → ∀ c < size, (c - 1) / 2 = k →
          loc.edgeBetter mem1 h (mem1 (loc.arrPtr + (k - 1) / 2)) (mem1 (loc.arrPtr + c)) = true := by
        intro hk0' c hc hck
        rw [hf1 _ (harr_lt par hparLt), hf1 _ (harr_lt c hc), hedge1 _ _ hepCap (hbij.2.1 c hc)]
        exact hskip hk0' c hc hck
      refine runs_seq_assign_flat (v := scratch + 16 * loc.Lk) (by eval_expr) ?_
      refine WordRAM.runs_cond_le (v := bit) (by eval_expr) ?_ ?_
      · intro hnzBit
        have hbeat1 : loc.edgeBetter mem1 h (mem1 (loc.arrPtr + k)) (mem1 (loc.arrPtr + par)) = true := by
          rw [hf1 _ (harr_lt k hkLt), hf1 _ (harr_lt par hparLt), hedge1 _ _ hekCap hepCap]
          by_contra hnot; rw [Bool.eq_false_iff.mpr hnot] at hbit; exact hnzBit hbit
        have hexcUp := (selectHeap_except_of_replaceAt hkLt hbij1 hkeys1 hother1 hskip1).1 ⟨hkPos, hbeat1⟩
        refine runs_seq_call_flat hup (vs := [loc.hb, k, scratch + 16 * loc.Lk])
          (by eval_expr) (by wram_words) ?_ ?_
        · exact ⟨k, scratch + 16 * loc.Lk, rfl, hw16, by omega, hhdr1, hbij1, hkeys1, hcand1,
            hexcUp, hz1, by unfold keyCompareSpace at hspUp; omega⟩
        · intro ret mem2 pos2 hpost2
          obtain ⟨hlo2, hhi2, hat2, hz2, hfr2, hpos2⟩ := hpost2
          simp only [List.getD_cons_zero, List.getD_cons_succ] at hlo2 hhi2 hfr2 hpos2
          have hretw : ret < 2 ^ w := by unfold keyCompareSpace at hspUp; omega
          refine WordRAM.runs_ret_le (v := ret) (by eval_expr) ?_ ?_
          · dsimp only [heapRebalanceContract]
            simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ]
            exact ⟨by omega, by unfold keyCompareSpace at hspUp; omega, hat2, hz2,
              fun a ha hout => (hfr2 a (by omega) hout).trans (hf1 a ha),
              fun e he => (hpos2 e he).trans (by
                have hpe : loc.posPtr + e < scratch := by
                  have := selectHeap_slot_bounds he; omega
                rw [hf1 _ hpe])⟩
          · simp only [heapRebalanceContract, heapSiftUpContract, keyCompareContract,
              List.getD_cons_zero, List.getD_cons_succ, Expr.size, argsSize]
            omega
      · intro hzBit
        have hfalse1 : loc.edgeBetter mem1 h (mem1 (loc.arrPtr + k)) (mem1 (loc.arrPtr + par)) = false := by
          rw [hf1 _ (harr_lt k hkLt), hf1 _ (harr_lt par hparLt), hedge1 _ _ hekCap hepCap]
          by_contra hnot; rw [Bool.eq_true_of_not_eq_false hnot] at hbit; simp only [↓reduceIte] at hbit; omega
        have hexcDn := (selectHeap_except_of_replaceAt hkLt hbij1 hkeys1 hother1 hskip1).2 (Or.inr hfalse1)
        refine runs_seq_call_flat hdown (vs := [loc.hb, k, scratch + 16 * loc.Lk])
          (by eval_expr) (by wram_words) ?_ ?_
        · exact ⟨k, scratch + 16 * loc.Lk, rfl, hw16, by omega, hhdr1, hbij1, hkeys1, hcand1,
            hexcDn, hz1, by unfold keyCompareSpace at hspDn; omega⟩
        · intro ret mem2 pos2 hpost2
          obtain ⟨hlo2, hhi2, hat2, hz2, hfr2, hpos2⟩ := hpost2
          simp only [List.getD_cons_zero, List.getD_cons_succ] at hlo2 hhi2 hfr2 hpos2
          have hretw : ret < 2 ^ w := by unfold keyCompareSpace at hspDn; omega
          refine WordRAM.runs_ret_le (v := ret) (by eval_expr) ?_ ?_
          · dsimp only [heapRebalanceContract]
            simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ]
            exact ⟨by omega, by unfold keyCompareSpace at hspDn; omega, hat2, hz2,
              fun a ha hout => (hfr2 a (by omega) hout).trans (hf1 a ha),
              fun e he => (hpos2 e he).trans (by
                have hpe : loc.posPtr + e < scratch := by
                  have := selectHeap_slot_bounds he; omega
                rw [hf1 _ hpe])⟩
          · simp only [heapRebalanceContract, heapSiftDownContract, keyCompareContract,
              List.getD_cons_zero, List.getD_cons_succ, Expr.size, argsSize]
            omega

end MinCostFlow.MinRatio
