module

public import MinCostFlow.LSF.Program.Layout
public import MinCostFlow.LSF.Program.BlockRep
public import MinCostFlow.LSF.Program.BridgeLemmas
public import MinCostFlow.LSF.Program.Spec
public import MinCostFlow.DynSpanner.Program.DynGraphBatch
public import MinCostFlow.DynSpanner.Program.DynGraphInit
public import MinCostFlow.Num.Add
public import MinCostFlow.Num.Subtract
public import MinCostFlow.Num.Multiply
public import MinCostFlow.Num.IntegerDivide
public import MinCostFlow.Num.Less
public import MinCostFlow.Num.ShiftLeft
public import MinCostFlow.Num.Copy
public import MinCostFlow.Num.SignFacts
public import MinCostFlow.Num.ModulePlacement
public import MinCostFlow.Num.WordBounds

import WordRAM.Tactic
import Mathlib.Data.Nat.Log

/-!
# Relocatable Dynamic-Graph Bundle and Shared Word-RAM Utilities for `LSF`

Provides the relocatable dynamic-graph module `dgRelocProcs` and deterministic low-level
Word-RAM procedures shared by initialization, dynamic forest updates, and the MWU driver:

* `memCopyStmt` and `memFillStmt`: disjoint slice copy and constant fill.
* `wordToLimbsStmt`: stores a runtime machine word as `L` base-`2^h` limbs.
* `emitNatStmt`: writes a compile-time constant `val` (such as `defaultC_ceil K_AN`) as `L`
  limbs without assuming `val < 2^w`.
* `addToStmt` and `subFromStmt`: in-place two's-complement `L`-limb addition and subtraction
  with zero heap allocation.
* `log2Stmt`: deterministic `Nat.log 2 x` computation in `O(log x + 1)` time.
-/

namespace MinCostFlow.LSF.Program

open WordRAM
open MinCostFlow.DynSpanner.Program
open MinCostFlow.Num

@[expose] public section

/-! ## Relocatable Dynamic-Graph Bundle -/

/-- Relocatable dynamic-graph module bundle at base `bDg` (15 procedures). -/
def dgRelocProcs (bDg : ℕ) : List Stmt :=
  dgOpsProcs ++
  dgEdgeProcs bDg ++
  dgSplitProcs bDg (bDg + 9) ++
  dgBatchProcs bDg (bDg + 7) (bDg + 9) (bDg + 12)

lemma dgRelocProcs_length (bDg : ℕ) : (dgRelocProcs bDg).length = 15 := by
  simp [dgRelocProcs, dgOpsProcs_length, dgEdgeProcs_length, dgSplitProcs_length,
    dgBatchProcs_length]

lemma dgRelocProcs_noRand (bDg : ℕ) : ∀ s ∈ dgRelocProcs bDg, s.NoRand := by
  intro s hs
  simp only [dgRelocProcs, List.mem_append] at hs
  rcases hs with ((h | h) | h) | h
  · exact dgOpsProcs_noRand s h
  · exact dgEdgeProcs_noRand bDg s h
  · exact dgSplitProcs_noRand bDg (bDg + 9) s h
  · exact dgBatchProcs_noRand bDg (bDg + 7) (bDg + 9) (bDg + 12) s h

lemma dgReloc_hasAt_ops {p : Program} {bDg : ℕ} (hp : p.HasAt bDg (dgRelocProcs bDg)) :
    p.HasAt bDg dgOpsProcs :=
  MinCostFlow.Num.hasAt_append_left (by simpa [dgRelocProcs, List.append_assoc] using hp)

lemma dgReloc_hasAt_edge {p : Program} {bDg : ℕ} (hp : p.HasAt bDg (dgRelocProcs bDg)) :
    p.HasAt (bDg + 7) (dgEdgeProcs bDg) := by
  have h1 := MinCostFlow.Num.hasAt_append_right
    (by simpa [dgRelocProcs, List.append_assoc] using hp)
  rw [dgOpsProcs_length] at h1
  exact MinCostFlow.Num.hasAt_append_left h1

lemma dgReloc_hasAt_split {p : Program} {bDg : ℕ} (hp : p.HasAt bDg (dgRelocProcs bDg)) :
    p.HasAt (bDg + 9) (dgSplitProcs bDg (bDg + 9)) := by
  have h1 := MinCostFlow.Num.hasAt_append_right
    (by simpa [dgRelocProcs, List.append_assoc] using hp)
  rw [dgOpsProcs_length] at h1
  have h2 := MinCostFlow.Num.hasAt_append_right h1
  rw [dgEdgeProcs_length, Nat.add_assoc] at h2
  exact MinCostFlow.Num.hasAt_append_left h2

lemma dgReloc_hasAt_batch {p : Program} {bDg : ℕ} (hp : p.HasAt bDg (dgRelocProcs bDg)) :
    p.HasAt (bDg + 12) (dgBatchProcs bDg (bDg + 7) (bDg + 9) (bDg + 12)) := by
  have h1 := MinCostFlow.Num.hasAt_append_right
    (by simpa [dgRelocProcs, List.append_assoc] using hp)
  rw [dgOpsProcs_length] at h1
  have h2 := MinCostFlow.Num.hasAt_append_right h1
  rw [dgEdgeProcs_length, Nat.add_assoc] at h2
  have h3 := MinCostFlow.Num.hasAt_append_right h2
  rw [dgSplitProcs_length, Nat.add_assoc] at h3
  exact h3

/-! ## Utility Procedure Indices -/

def idxUtilMemCopy : ℕ := 0
def idxUtilMemFill : ℕ := 1
def idxUtilWordToLimbs : ℕ := 2
def idxUtilEmitDefaultC : ℕ := 3
def idxUtilAddTo : ℕ := 4
def idxUtilSubFrom : ℕ := 5
def idxUtilLog2 : ℕ := 6
def idxUtilKeyedMergeSort : ℕ := 7

/-! ## Slice Copy and Fill -/

/-- Copy `len` words from `src` to disjoint `dst`. Args: `[dst, src, len]`. -/
def memCopyStmt : Stmt :=
  forRange 3 (.const 0) (.reg 2)
    (.store (.bin .add (.reg 0) (.reg 3)) (.load (.bin .add (.reg 1) (.reg 3)))) ;;
  .ret (.const 0)

def memCopyContract (w : ℕ) : Contract where
  pre args _ := ∃ dst src len, args = [dst, src, len] ∧
    dst + len < 2 ^ w ∧ src + len < 2 ^ w ∧ (dst + len ≤ src ∨ src + len ≤ dst)
  post args mem ret mem' := ∃ dst src len, args = [dst, src, len] ∧ ret = 0 ∧
    (∀ i < len, mem' (dst + i) = mem (src + i)) ∧
    (∀ x, x < dst ∨ dst + len ≤ x → mem' x = mem x)
  cost args _ := 20 * args.getD 2 0 + 12

lemma memCopyStmt_noRand : memCopyStmt.NoRand := by
  simp [memCopyStmt, forRange, forUp, Stmt.NoRand]

/-- Verified contract for `memCopyStmt`. -/
theorem memCopy_meetsContract {w f : ℕ} {p : Program}
    (hw : 1 < 2 ^ w) (hp : p.procs[f]? = some memCopyStmt) :
    MeetsContract w p f (memCopyContract w) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨dst, src, len, rfl, hdw_bd, hsw_bd, hdisj⟩
  have hdw : dst < 2 ^ w := hwords dst (by simp)
  have hsw : src < 2 ^ w := hwords src (by simp)
  have hlw : len < 2 ^ w := hwords len (by simp)
  refine runs_start_le ?_
  unfold memCopyStmt
  let Inv : ℕ → State → Prop := fun i st =>
    st.regs 0 = dst ∧ st.regs 1 = src ∧ st.regs 2 = len ∧ st.regs 3 = i ∧
    (∀ j < i, st.mem (dst + j) = mem (src + j)) ∧
    (∀ x, x < dst ∨ dst + i ≤ x → st.mem x = mem x)
  have hloop : Triple w p (fun st => st = startState [dst, src, len] mem pos)
      (forRange 3 (.const 0) (.reg 2)
        (.store (.bin .add (.reg 0) (.reg 3)) (.load (.bin .add (.reg 1) (.reg 3)))))
      (normalPost (Inv len)) (fun _ => 20 * len + 7) := by
    refine (Triple.forRange_const 11 0 len (Nat.zero_le len) hw (fun _ => hlw)
      (fun st hst => by
        subst hst
        exact ⟨by eval_expr, by simp [startState], by simp [startState], by simp [startState],
          by simp, fun _ _ => by omega, fun _ _ => rfl⟩)
      (fun _ _ _ _ hi => hi.2.2.2.1)
      (fun _ st _ _ hi => by have h2 := hi.2.2.1; eval_expr)
      (fun i _ hilt st ω' hi => by
        rcases hi with ⟨h0, h1, h2, h3, hcp, hfr⟩
        have hlt_di : dst + i < 2 ^ w := by omega
        have hlt_si : src + i < 2 ^ w := by omega
        have hread : st.mem (src + i) = mem (src + i) := hfr (src + i) (by omega)
        refine runs_start_le (runs_store_le (by eval_expr) (by eval_expr) ?_ (by wram_cost))
        refine ⟨⟨h0, h1, h2, by simp, fun j hj => ?_, fun x hx => ?_⟩, h3⟩
        · dsimp only
          by_cases hji : j = i
          · subst j; simp [hread]
          · rw [Function.update_of_ne (by omega)]; exact hcp j (by omega)
        · dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hfr x (by omega))).mono_cost (fun _ _ => by dsimp [Expr.size]; omega)
  refine runs_seq_triple_le hloop rfl (fun st₁ hinv => ?_)
  rcases hinv with ⟨_, _, _, _, hcp, hfr⟩
  exact runs_ret_le (by eval_expr) ⟨dst, src, len, rfl, rfl, hcp, hfr⟩
    (by simp [memCopyContract, Expr.size])

/-- Fill `[dst, dst + len)` with constant `val`. Args: `[dst, len, val]`. -/
def memFillStmt : Stmt :=
  forRange 3 (.const 0) (.reg 1)
    (.store (.bin .add (.reg 0) (.reg 3)) (.reg 2)) ;;
  .ret (.const 0)

def memFillContract (w : ℕ) : Contract where
  pre args _ := ∃ dst len val, args = [dst, len, val] ∧ dst + len < 2 ^ w
  post args mem ret mem' := ∃ dst len val, args = [dst, len, val] ∧ ret = 0 ∧
    (∀ i < len, mem' (dst + i) = val) ∧
    (∀ x, x < dst ∨ dst + len ≤ x → mem' x = mem x)
  cost args _ := 16 * args.getD 1 0 + 12

lemma memFillStmt_noRand : memFillStmt.NoRand := by
  simp [memFillStmt, forRange, forUp, Stmt.NoRand]

/-- Verified contract for `memFillStmt`. -/
theorem memFill_meetsContract {w f : ℕ} {p : Program}
    (hw : 1 < 2 ^ w) (hp : p.procs[f]? = some memFillStmt) :
    MeetsContract w p f (memFillContract w) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨dst, len, val, rfl, hdw_bd⟩
  have hdw : dst < 2 ^ w := hwords dst (by simp)
  have hlw : len < 2 ^ w := hwords len (by simp)
  have hvw : val < 2 ^ w := hwords val (by simp)
  refine runs_start_le ?_
  unfold memFillStmt
  let Inv : ℕ → State → Prop := fun i st =>
    st.regs 0 = dst ∧ st.regs 1 = len ∧ st.regs 2 = val ∧ st.regs 3 = i ∧
    (∀ j < i, st.mem (dst + j) = val) ∧
    (∀ x, x < dst ∨ dst + i ≤ x → st.mem x = mem x)
  have hloop : Triple w p (fun st => st = startState [dst, len, val] mem pos)
      (forRange 3 (.const 0) (.reg 1)
        (.store (.bin .add (.reg 0) (.reg 3)) (.reg 2)))
      (normalPost (Inv len)) (fun _ => 16 * len + 7) := by
    refine (Triple.forRange_const 7 0 len (Nat.zero_le len) hw (fun _ => hlw)
      (fun st hst => by
        subst hst
        exact ⟨by eval_expr, by simp [startState], by simp [startState], by simp [startState],
          by simp, fun _ _ => by omega, fun _ _ => rfl⟩)
      (fun _ _ _ _ hi => hi.2.2.2.1)
      (fun _ st _ _ hi => by have h1 := hi.2.1; eval_expr)
      (fun i _ hilt st ω' hi => by
        rcases hi with ⟨h0, h1, h2, h3, hfl, hfr⟩
        have hlt_di : dst + i < 2 ^ w := by omega
        refine runs_start_le (runs_store_le (by eval_expr) (by eval_expr) ?_ (by wram_cost))
        refine ⟨⟨h0, h1, h2, by simp, fun j hj => ?_, fun x hx => ?_⟩, h3⟩
        · dsimp only
          by_cases hji : j = i
          · subst j; simp
          · rw [Function.update_of_ne (by omega)]; exact hfl j (by omega)
        · dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hfr x (by omega))).mono_cost (fun _ _ => by dsimp [Expr.size]; omega)
  refine runs_seq_triple_le hloop rfl (fun st₁ hinv => ?_)
  rcases hinv with ⟨_, _, _, _, hfl, hfr⟩
  exact runs_ret_le (by eval_expr) ⟨dst, len, val, rfl, rfl, hfl, hfr⟩
    (by simp [memFillContract, Expr.size])

/-! ## Encoding Runtime Words and Compile-Time Constants into Limbs -/

/-- Write runtime word `x` into `L` base-`2^h` limbs at `dst`. Args: `[dst, L, x]`. -/
def wordToLimbsStmt (h : ℕ) : Stmt :=
  .assign 4 (.reg 2) ;;
  forRange 3 (.const 0) (.reg 1)
    (.store (.bin .add (.reg 0) (.reg 3)) (.bin .mod (.reg 4) (.const (base h))) ;;
     .assign 4 (.bin .div (.reg 4) (.const (base h)))) ;;
  .ret (.const 0)

def wordToLimbsContract (w h : ℕ) : Contract where
  pre args _ := ∃ dst L x, args = [dst, L, x] ∧ 0 < h ∧ base h < 2 ^ w ∧ dst + L < 2 ^ w
  post args mem ret mem' := ∃ dst L x, args = [dst, L, x] ∧ ret = 0 ∧
    Valid mem' dst h L ∧
    unsignedVal mem' dst h L = x % capacity h L ∧
    (∀ z, z < dst ∨ dst + L ≤ z → mem' z = mem z)
  cost args _ := 25 * args.getD 1 0 + 20

lemma wordToLimbsStmt_noRand (h : ℕ) : (wordToLimbsStmt h).NoRand := by
  simp [wordToLimbsStmt, forRange, forUp, Stmt.NoRand]

private lemma unsignedVal_snoc_div_mod (mem : ℕ → ℕ) (dst h i x : ℕ)
    (hprev : unsignedVal mem dst h i = x % capacity h i)
    (hlast : mem (dst + i) = (x / capacity h i) % base h) :
    unsignedVal mem dst h (i + 1) = x % capacity h (i + 1) := by
  rw [unsignedVal_snoc, hprev, hlast, capacity_succ, Nat.mul_comm (base h)]
  exact (Nat.mod_mul).symm

/-- Verified contract for `wordToLimbsStmt`. -/
theorem wordToLimbs_meetsContract {w h f : ℕ} {p : Program}
    (hp : p.procs[f]? = some (wordToLimbsStmt h)) :
    MeetsContract w p f (wordToLimbsContract w h) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨dst, L, x, rfl, hh, hb, hdw_bd⟩
  have hdw : dst < 2 ^ w := hwords dst (by simp)
  have hlw : L < 2 ^ w := hwords L (by simp)
  have hxw : x < 2 ^ w := hwords x (by simp)
  have hw1 : 1 < 2 ^ w := lt_of_le_of_lt (Nat.succ_le_of_lt (base_pos h)) hb
  refine runs_start_le ?_
  unfold wordToLimbsStmt
  refine runs_seq_assign_le (v := x) (by eval_expr) ?_
  let Inv : ℕ → State → Prop := fun i st =>
    st.regs 0 = dst ∧ st.regs 1 = L ∧ st.regs 3 = i ∧ st.regs 4 = x / capacity h i ∧
    Valid st.mem dst h i ∧
    unsignedVal st.mem dst h i = x % capacity h i ∧
    (∀ z, z < dst ∨ dst + i ≤ z → st.mem z = mem z)
  have hloop : Triple w p
      (fun st => st = { (startState [dst, L, x] mem pos) with
        regs := Function.update (startState [dst, L, x] mem pos).regs 4 x })
      (forRange 3 (.const 0) (.reg 1)
        (.store (.bin .add (.reg 0) (.reg 3)) (.bin .mod (.reg 4) (.const (base h))) ;;
         .assign 4 (.bin .div (.reg 4) (.const (base h)))))
      (normalPost (Inv L)) (fun _ => 25 * L + 7) := by
    refine (Triple.forRange_const 16 0 L (Nat.zero_le L) hw1 (fun _ => hlw)
      (fun st hst => by
        subst hst
        exact ⟨by eval_expr, by simp [startState], by simp [startState], by simp,
          by simp [capacity], fun _ hi => by omega,
          by simp [unsignedVal, capacity, Nat.mod_one], fun _ _ => rfl⟩)
      (fun _ _ _ _ hi => hi.2.2.1)
      (fun _ st _ _ hi => by have h1 := hi.2.1; eval_expr)
      (fun i _ hilt st ω' hi => by
        rcases hi with ⟨h0, h1, h3, h4, hval, huv, hfr⟩
        have hlt_di : dst + i < 2 ^ w := by omega
        have hcur_w : x / capacity h i < 2 ^ w := lt_of_le_of_lt (Nat.div_le_self _ _) hxw
        have hmod_lt : (x / capacity h i) % base h < base h := Nat.mod_lt _ (base_pos h)
        have hmod_w : (x / capacity h i) % base h < 2 ^ w := lt_trans hmod_lt hb
        have hdiv_lt : (x / capacity h i) / base h < 2 ^ w :=
          lt_of_le_of_lt (Nat.div_le_self _ _) hcur_w
        refine runs_start_le (runs_seq_store_le (by eval_expr) (by eval_expr) ?_)
        refine runs_assign_le (v := (x / capacity h i) / base h) (by eval_expr) ?_ (by wram_cost)
        refine ⟨⟨h0, h1, by simp, ?_, fun j hj => ?_, ?_, fun z hz => ?_⟩, by simpa using h3⟩
        · dsimp only
          rw [Function.update_of_ne (by decide), Function.update_self,
            Nat.div_div_eq_div_mul, Nat.mul_comm, ← capacity_succ]
        · dsimp only
          by_cases hji : j = i
          · subst j; simpa using hmod_lt
          · rw [Function.update_of_ne (by omega)]; exact hval j (by omega)
        · refine unsignedVal_snoc_div_mod _ dst h i x ?_ (by simp)
          rw [← huv]
          exact unsignedVal_congr fun j hj => Function.update_of_ne (by omega) _ _
        · dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hfr z (by omega))).mono_cost (fun _ _ => by dsimp [Expr.size]; omega)
  refine runs_seq_triple_le hloop rfl (fun st₁ hinv => ?_)
  rcases hinv with ⟨_, _, _, _, hval, huv, hfr⟩
  exact runs_ret_le (by eval_expr) ⟨dst, L, x, rfl, rfl, hval, huv, hfr⟩
    (by simp [wordToLimbsContract, Expr.size]; omega)

/-- Base-`2^h` limbs of `n`, least-significant first. Returns `[]` if `h = 0` or `n = 0`. -/
def natLimbs (h n : ℕ) : List ℕ :=
  match h, n with
  | 0, _ => []
  | _, 0 => []
  | h + 1, n + 1 =>
    ((n + 1) % base (h + 1)) :: natLimbs (h + 1) ((n + 1) / base (h + 1))
termination_by n
decreasing_by
  exact Nat.div_lt_self (Nat.succ_pos _) (Nat.one_lt_pow (Nat.succ_ne_zero _) (by decide))

lemma natLimbs_lt {h n : ℕ} : ∀ d ∈ natLimbs h n, d < base h := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro d hd
    cases h with
    | zero => simp [natLimbs] at hd
    | succ h =>
      cases n with
      | zero => simp [natLimbs] at hd
      | succ n =>
        unfold natLimbs at hd
        rcases List.mem_cons.mp hd with rfl | hd'
        · exact Nat.mod_lt _ (base_pos (h + 1))
        · have hb : 1 < base (h + 1) := Nat.one_lt_pow (Nat.succ_ne_zero _) (by decide)
          exact ih _ (Nat.div_lt_self (Nat.succ_pos _) hb) d hd'

lemma natLimbs_listVal {h n : ℕ} (hh : 0 < h) : listVal h (natLimbs h n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases h with
    | zero => omega
    | succ h =>
      cases n with
      | zero => simp [natLimbs, listVal]
      | succ n =>
        unfold natLimbs
        have hb : 1 < base (h + 1) := Nat.one_lt_pow (Nat.succ_ne_zero _) (by decide)
        simp only [listVal, ih _ (Nat.div_lt_self (Nat.succ_pos _) hb)]
        exact Nat.mod_add_div (n + 1) (base (h + 1))

lemma natLimbs_length_le_iff {h n L : ℕ} (hh : 0 < h) :
    (natLimbs h n).length ≤ L ↔ n < capacity h L := by
  induction n using Nat.strong_induction_on generalizing L with
  | _ n ih =>
    cases h with
    | zero => omega
    | succ h =>
      cases n with
      | zero => simp [natLimbs, capacity_pos]
      | succ n =>
        unfold natLimbs
        have hb1 : 1 < base (h + 1) := Nat.one_lt_pow (Nat.succ_ne_zero _) (by decide)
        have hb0 : 0 < base (h + 1) := base_pos (h + 1)
        cases L with
        | zero =>
          simp only [List.length_cons, capacity_zero]
          omega
        | succ L =>
          simp only [List.length_cons, Nat.add_le_add_iff_right, capacity_succ]
          rw [ih _ (Nat.div_lt_self (Nat.succ_pos _) hb1) (L := L),
            Nat.div_lt_iff_lt_mul hb0, Nat.mul_comm]

/-- Straight-line stores writing `limbs` at `dst + idx, dst + idx + 1, ...`. -/
def emitStoresStmt : List ℕ → ℕ → Stmt
  | [], _ => .nop
  | d :: ds, idx =>
    .store (.bin .add (.reg 0) (.const idx)) (.const d) ;;
    emitStoresStmt ds (idx + 1)

lemma emitStoresStmt_noRand : ∀ ds idx, (emitStoresStmt ds idx).NoRand
  | [], _ => by simp [emitStoresStmt, Stmt.NoRand]
  | _ :: ds, idx => by simp [emitStoresStmt, Stmt.NoRand, emitStoresStmt_noRand ds (idx + 1)]

private lemma emitStores_triple {w dst idx : ℕ} {p : Program} (hw : 1 < 2 ^ w) :
    ∀ (ds : List ℕ) (mem₀ : ℕ → ℕ),
      (∀ d ∈ ds, d < 2 ^ w) →
      dst + idx + ds.length < 2 ^ w →
      Triple w p (fun st => st.regs 0 = dst ∧ st.mem = mem₀)
        (emitStoresStmt ds idx)
        (normalPost fun st => st.regs 0 = dst ∧
          (∀ j (hj : j < ds.length), st.mem (dst + idx + j) = ds[j]'hj) ∧
          (∀ z, z < dst + idx ∨ dst + idx + ds.length ≤ z → st.mem z = mem₀ z))
        (fun _ => 10 * ds.length + 2)
  | [], mem₀, _, _, st, ω, ⟨h0, hmem⟩ => by
    subst hmem
    exact runs_start_le (runs_nop_le ⟨h0, fun _ hj => by simp at hj, fun _ _ => rfl⟩
      (by simp only [List.length_nil]; omega))
  | d :: ds, mem₀, hd, hbd, st, ω, ⟨h0, hmem⟩ => by
    subst hmem
    simp only [List.length_cons] at hbd
    have hdw : d < 2 ^ w := hd d List.mem_cons_self
    have hidxw : idx < 2 ^ w := by omega
    have hdiw : dst + idx < 2 ^ w := by omega
    have hdw2 : dst < 2 ^ w := by omega
    let mem₁ := Function.update st.mem (dst + idx) d
    refine runs_start_le ?_
    unfold emitStoresStmt
    refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
    have ih := emitStores_triple hw ds mem₁ (w := w) (dst := dst) (idx := idx + 1) (p := p)
      (fun x hx => hd x (List.mem_cons_of_mem d hx)) (by omega)
    refine runs_triple_le ih ⟨by simp [h0], rfl⟩ (fun o st' h => ?_)
      (by simp only [List.length_cons]; wram_cost)
    cases o with
    | returned u => exact False.elim h
    | normal =>
      rcases h with ⟨h0', hset, hfr⟩
      refine ⟨h0', fun j hj => ?_, fun z hz => ?_⟩
      · cases j with
        | zero =>
          simpa using (hfr (dst + idx) (Or.inl (by omega))).trans (by simp [mem₁])
        | succ j =>
          have hj' : j < ds.length := by simp only [List.length_cons] at hj; omega
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hset j hj'
      · have hz' : z < dst + (idx + 1) ∨ dst + (idx + 1) + ds.length ≤ z := by
          simp only [List.length_cons] at hz; omega
        rw [hfr z hz']
        exact Function.update_of_ne (show z ≠ dst + idx by simp only [List.length_cons] at hz; omega)
          d st.mem

/-- Store compile-time constant `val` into `L` limbs at `dst`. Args: `[dst, L]`. -/
def emitNatStmt (val h : ℕ) : Stmt :=
  forRange 2 (.const 0) (.reg 1) (.store (.bin .add (.reg 0) (.reg 2)) (.const 0)) ;;
  emitStoresStmt (natLimbs h val) 0 ;;
  .ret (.const 0)

def emitNatContract (w val h : ℕ) : Contract where
  pre args _ := ∃ dst L, args = [dst, L] ∧ 0 < h ∧ base h < 2 ^ w ∧
    (natLimbs h val).length ≤ L ∧ dst + L < 2 ^ w
  post args mem ret mem' := ∃ dst L, args = [dst, L] ∧ ret = 0 ∧
    Valid mem' dst h L ∧
    unsignedVal mem' dst h L = val ∧
    (∀ z, z < dst ∨ dst + L ≤ z → mem' z = mem z)
  cost args _ := 16 * args.getD 1 0 + 10 * (natLimbs h val).length + 25

lemma emitNatStmt_noRand (val h : ℕ) : (emitNatStmt val h).NoRand := by
  simp [emitNatStmt, forRange, forUp, Stmt.NoRand, emitStoresStmt_noRand]

private lemma listAt_replicate_tail {mem : ℕ → ℕ} {dst len : ℕ} (ds : List ℕ)
    (hlen : ds.length ≤ len)
    (hhead : ∀ j (hj : j < ds.length), mem (dst + j) = ds[j]'hj)
    (htail : ∀ j, ds.length ≤ j → j < len → mem (dst + j) = 0) :
    ListAt mem dst (ds ++ List.replicate (len - ds.length) 0) := by
  intro i hi
  simp only [List.length_append, List.length_replicate] at hi
  by_cases hlt : i < ds.length
  · rw [List.getElem_append_left hlt]
    exact hhead i hlt
  · have hle : ds.length ≤ i := by omega
    rw [List.getElem_append_right hle]
    simp [htail i hle (by omega)]

private lemma listVal_append_zeros (h : ℕ) :
    ∀ (ds : List ℕ) (k : ℕ), listVal h (ds ++ List.replicate k 0) = listVal h ds
  | [], k => by
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [List.nil_append] at ih
      simp [List.replicate_succ, listVal, ih]
  | d :: ds, k => by
    simp [listVal, listVal_append_zeros h ds k]

/-- Verified contract for `emitNatStmt`. -/
theorem emitNat_meetsContract {w val h f : ℕ} {p : Program}
    (hp : p.procs[f]? = some (emitNatStmt val h)) :
    MeetsContract w p f (emitNatContract w val h) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨dst, L, rfl, hh, hb, hlen_le, hbd⟩
  have hdw : dst < 2 ^ w := hwords dst (by simp)
  have hlw : L < 2 ^ w := hwords L (by simp)
  have hw1 : 1 < 2 ^ w := lt_of_le_of_lt (Nat.succ_le_of_lt (base_pos h)) hb
  refine runs_start_le ?_
  unfold emitNatStmt
  let Inv0 : ℕ → State → Prop := fun i st =>
    st.regs 0 = dst ∧ st.regs 1 = L ∧ st.regs 2 = i ∧
    (∀ j < i, st.mem (dst + j) = 0) ∧
    (∀ z, z < dst ∨ dst + i ≤ z → st.mem z = mem z)
  have hloop : Triple w p (fun st => st = startState [dst, L] mem pos)
      (forRange 2 (.const 0) (.reg 1) (.store (.bin .add (.reg 0) (.reg 2)) (.const 0)))
      (normalPost (Inv0 L)) (fun _ => 16 * L + 7) := by
    refine (Triple.forRange_const 7 0 L (Nat.zero_le L) hw1 (fun _ => hlw)
      (fun st hst => by
        subst hst
        exact ⟨by eval_expr, by simp [startState], by simp [startState], by simp,
          fun _ hj => by omega, fun _ _ => rfl⟩)
      (fun _ _ _ _ hi => hi.2.2.1)
      (fun _ st _ _ hi => by have h1 := hi.2.1; eval_expr)
      (fun i _ hilt st ω' hi => by
        rcases hi with ⟨h0, h1, h2, hz, hfr⟩
        have hlt_di : dst + i < 2 ^ w := by omega
        refine runs_start_le (runs_store_le (by eval_expr) (by eval_expr) ?_ (by wram_cost))
        refine ⟨⟨h0, h1, by simp, fun j hj => ?_, fun z hz' => ?_⟩, h2⟩
        · dsimp only
          by_cases hji : j = i
          · subst j; simp
          · rw [Function.update_of_ne (by omega)]; exact hz j (by omega)
        · dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hfr z (by omega))).mono_cost (fun _ _ => by dsimp [Expr.size]; omega)
  refine runs_seq_triple_le hloop rfl (fun st₁ hinv => ?_)
  rcases hinv with ⟨h0, h1, _, hz, hfr⟩
  have hemit := emitStores_triple hw1 (natLimbs h val) st₁.mem (w := w) (dst := dst) (idx := 0)
    (p := p) (fun d hd => lt_trans (natLimbs_lt d hd) hb) (by omega)
  refine runs_seq_triple_le hemit ⟨h0, rfl⟩ (fun st₂ he => ?_)
  rcases he with ⟨_, hset, hfr₂⟩
  have hmem_tail : ∀ j, (natLimbs h val).length ≤ j → j < L → st₂.mem (dst + j) = 0 := by
    intro j hj_ge hj_lt
    rw [hfr₂ (dst + j) (Or.inr (by omega))]
    exact hz j hj_lt
  have hset' : ∀ j (hj : j < (natLimbs h val).length),
      st₂.mem (dst + j) = (natLimbs h val)[j]'hj := by
    intro j hj
    simpa using hset j hj
  have hlat := listAt_replicate_tail (natLimbs h val) hlen_le hset' hmem_tail
  have hlen_app : (natLimbs h val ++ List.replicate (L - (natLimbs h val).length) 0).length = L := by
    simp; omega
  have hval : Valid st₂.mem dst h L := by
    rw [← hlen_app]
    refine valid_listAt hlat fun x hx => ?_
    rcases List.mem_append.mp hx with hx | hx
    · exact natLimbs_lt x hx
    · have : x = 0 := List.eq_of_mem_replicate hx
      subst x; exact base_pos h
  have huv : unsignedVal st₂.mem dst h L = val := by
    rw [← hlen_app, unsignedVal_listAt hlat, listVal_append_zeros, natLimbs_listVal hh]
  have hfr_all : ∀ z, z < dst ∨ dst + L ≤ z → st₂.mem z = mem z := by
    intro z hz_out
    have h1 : st₂.mem z = st₁.mem z := hfr₂ z (by rcases hz_out with hlt | hge <;> omega)
    rw [h1]
    exact hfr z hz_out
  exact runs_ret_le (by eval_expr) ⟨dst, L, rfl, rfl, hval, huv, hfr_all⟩
    (by simp [emitNatContract, Expr.size]; omega)

/-! ## In-Place Two's-Complement Addition and Subtraction -/

/-- In-place addition `dst[0..L) += src[0..L)` modulo `capacity h L`. Args: `[dst, src, L]`. -/
def addToStmt (h : ℕ) : Stmt :=
  .assign 3 (.const 0) ;;
  forRange 4 (.const 0) (.reg 2)
    (.assign 5 (.bin .add (.bin .add (.load (.bin .add (.reg 0) (.reg 4)))
        (.load (.bin .add (.reg 1) (.reg 4)))) (.reg 3)) ;;
     .store (.bin .add (.reg 0) (.reg 4)) (.bin .mod (.reg 5) (.const (base h))) ;;
     .assign 3 (.bin .div (.reg 5) (.const (base h)))) ;;
  .ret (.const 0)

def addToContract (w h : ℕ) : Contract where
  pre args mem := ∃ dst src L, args = [dst, src, L] ∧ 0 < h ∧ 2 * h + 2 ≤ w ∧
    dst + L < 2 ^ w ∧ src + L < 2 ^ w ∧
    (dst + L ≤ src ∨ src + L ≤ dst) ∧ Valid mem dst h L ∧ Valid mem src h L
  post args mem ret mem' := ∃ dst src L, args = [dst, src, L] ∧ ret = 0 ∧
    Valid mem' dst h L ∧
    unsignedVal mem' dst h L = (unsignedVal mem dst h L + unsignedVal mem src h L) % capacity h L ∧
    intVal mem' dst h L = wrap h L (intVal mem dst h L + intVal mem src h L) ∧
    (∀ z, z < dst ∨ dst + L ≤ z → mem' z = mem z)
  cost args _ := 55 * args.getD 2 0 + 18

lemma addToStmt_noRand (h : ℕ) : (addToStmt h).NoRand := by
  simp [addToStmt, forRange, forUp, Stmt.NoRand]

private lemma addTo_snoc_eq {mem_old mem_new mem_src : ℕ → ℕ} {dst src h k c : ℕ}
    (hprev : unsignedVal mem_new dst h k + capacity h k * c =
      unsignedVal mem_old dst h k + unsignedVal mem_src src h k)
    (heq : ∀ j < k, mem_new (dst + j) = Function.update mem_new (dst + k)
      ((mem_old (dst + k) + mem_src (src + k) + c) % base h) (dst + j)) :
    unsignedVal (Function.update mem_new (dst + k)
      ((mem_old (dst + k) + mem_src (src + k) + c) % base h)) dst h k +
      capacity h k * ((mem_old (dst + k) + mem_src (src + k) + c) % base h) +
      capacity h (k + 1) * ((mem_old (dst + k) + mem_src (src + k) + c) / base h) =
      unsignedVal mem_old dst h (k + 1) + unsignedVal mem_src src h (k + 1) := by
  have hc : unsignedVal (Function.update mem_new (dst + k)
      ((mem_old (dst + k) + mem_src (src + k) + c) % base h)) dst h k =
      unsignedVal mem_new dst h k :=
    unsignedVal_congr fun j hj => (heq j hj).symm
  rw [hc, unsignedVal_snoc mem_old dst h k, unsignedVal_snoc mem_src src h k, capacity_succ]
  set s := mem_old (dst + k) + mem_src (src + k) + c
  have hdm : s % base h + base h * (s / base h) = s := Nat.mod_add_div s (base h)
  calc
    unsignedVal mem_new dst h k + capacity h k * (s % base h) +
        (base h * capacity h k) * (s / base h)
      = unsignedVal mem_new dst h k + capacity h k * (s % base h + base h * (s / base h)) := by ring
    _ = unsignedVal mem_new dst h k + capacity h k * s := by rw [hdm]
    _ = (unsignedVal mem_new dst h k + capacity h k * c) +
          capacity h k * mem_old (dst + k) + capacity h k * mem_src (src + k) := by ring
    _ = unsignedVal mem_old dst h k + capacity h k * mem_old (dst + k) +
          (unsignedVal mem_src src h k + capacity h k * mem_src (src + k)) := by rw [hprev]; ring

/-- Verified contract for `addToStmt`. -/
theorem addTo_meetsContract {w h f : ℕ} {p : Program}
    (hp : p.procs[f]? = some (addToStmt h)) :
    MeetsContract w p f (addToContract w h) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨dst, src, L, rfl, hh, hw2, hdw_bd, hsw_bd, hdisj, hvd, hvs⟩
  have hdw : dst < 2 ^ w := hwords dst (by simp)
  have hsw : src < 2 ^ w := hwords src (by simp)
  have hlw : L < 2 ^ w := hwords L (by simp)
  have hb := base_lt_word hw2
  have hb1 : 1 < base h := Nat.one_lt_pow (Nat.ne_of_gt hh) (by decide)
  have hw1 : 1 < 2 ^ w := lt_trans hb1 hb
  refine runs_start_le ?_
  unfold addToStmt
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  let Inv : ℕ → State → Prop := fun i st =>
    st.regs 0 = dst ∧ st.regs 1 = src ∧ st.regs 2 = L ∧ st.regs 4 = i ∧
    st.regs 3 ≤ 1 ∧ Valid st.mem dst h i ∧
    unsignedVal st.mem dst h i + capacity h i * st.regs 3 =
      unsignedVal mem dst h i + unsignedVal mem src h i ∧
    (∀ j, i ≤ j → j < L → st.mem (dst + j) = mem (dst + j)) ∧
    (∀ z, z < dst ∨ dst + i ≤ z → st.mem z = mem z)
  have hloop : Triple w p
      (fun st => st = { (startState [dst, src, L] mem pos) with
        regs := Function.update (startState [dst, src, L] mem pos).regs 3 0 })
      (forRange 4 (.const 0) (.reg 2)
        (.assign 5 (.bin .add (.bin .add (.load (.bin .add (.reg 0) (.reg 4)))
            (.load (.bin .add (.reg 1) (.reg 4)))) (.reg 3)) ;;
         .store (.bin .add (.reg 0) (.reg 4)) (.bin .mod (.reg 5) (.const (base h))) ;;
         .assign 3 (.bin .div (.reg 5) (.const (base h)))))
      (normalPost (Inv L)) (fun _ => 55 * L + 7) := by
    refine (Triple.forRange_const 45 0 L (Nat.zero_le L) hw1 (fun _ => hlw)
      (fun st hst => by
        subst hst
        exact ⟨by eval_expr, by simp [startState], by simp [startState], by simp [startState],
          by simp, by simp, fun _ hi => by omega, by simp [unsignedVal],
          fun j _ _ => rfl, fun _ _ => rfl⟩)
      (fun _ _ _ _ hi => hi.2.2.2.1)
      (fun _ st _ _ hi => by have h2 := hi.2.2.1; eval_expr)
      (fun i _ hilt st ω' hi => by
        rcases hi with ⟨h0, h1, h2, h4, hc1, hval, huv, htail, hfr⟩
        have hlt_di : dst + i < 2 ^ w := by omega
        have hlt_si : src + i < 2 ^ w := by omega
        have ha_eq : st.mem (dst + i) = mem (dst + i) := htail i le_rfl hilt
        have hs_eq : st.mem (src + i) = mem (src + i) := hfr (src + i) (by omega)
        have ha_lt : mem (dst + i) < base h := hvd i hilt
        have hs_lt : mem (src + i) < base h := hvs i hilt
        have hc_lt : st.regs 3 < base h := lt_of_le_of_lt hc1 hb1
        have hc_w : st.regs 3 < 2 ^ w := lt_trans hc_lt hb
        have hsum_lt : mem (dst + i) + mem (src + i) + st.regs 3 < 2 ^ w :=
          limb_add_lt_word hw2 ha_lt hs_lt hc_lt
        have hpart_lt : mem (dst + i) + mem (src + i) < 2 ^ w := by omega
        have hmod_lt : (mem (dst + i) + mem (src + i) + st.regs 3) % base h < base h :=
          Nat.mod_lt _ (base_pos h)
        have hmod_w : (mem (dst + i) + mem (src + i) + st.regs 3) % base h < 2 ^ w :=
          lt_trans hmod_lt hb
        have hdiv_le : (mem (dst + i) + mem (src + i) + st.regs 3) / base h ≤ 1 :=
          add_limb_carry_le_one ha_lt hs_lt hc1
        have hdiv_w : (mem (dst + i) + mem (src + i) + st.regs 3) / base h < 2 ^ w :=
          lt_of_le_of_lt hdiv_le hw1
        refine runs_start_le (runs_seq_assign_le (v := mem (dst + i) + mem (src + i) + st.regs 3)
          (by eval_expr) ?_)
        refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
        refine runs_assign_le (v := (mem (dst + i) + mem (src + i) + st.regs 3) / base h)
          (by eval_expr) ?_ (by wram_cost)
        refine ⟨⟨h0, h1, h2, by simp, by simp [hdiv_le], fun j hj => ?_, ?_, fun j hj1 hj2 => ?_,
            fun z hz => ?_⟩, by simpa using h4⟩
        · dsimp only
          by_cases hji : j = i
          · subst j; simpa using hmod_lt
          · rw [Function.update_of_ne (by omega)]; exact hval j (by omega)
        · dsimp only
          rw [Function.update_of_ne (by decide), Function.update_self, unsignedVal_snoc]
          simpa [Function.update_self] using addTo_snoc_eq (mem_old := mem) (mem_new := st.mem)
            (mem_src := mem) (dst := dst) (src := src) (h := h) (k := i) (c := st.regs 3) huv
            fun j hj => (Function.update_of_ne (by omega) _ _).symm
        · dsimp only
          rw [Function.update_of_ne (by omega)]
          exact htail j (by omega) hj2
        · dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hfr z (by omega))).mono_cost (fun _ _ => by dsimp [Expr.size]; omega)
  refine runs_seq_triple_le hloop rfl (fun st₁ hinv => ?_)
  rcases hinv with ⟨_, _, _, _, hc1, hval, huv, _, hfr⟩
  have hlt_cap : unsignedVal st₁.mem dst h L < capacity h L := unsignedVal_lt hval
  have hmod : unsignedVal st₁.mem dst h L =
      (unsignedVal mem dst h L + unsignedVal mem src h L) % capacity h L := by
    rw [← huv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt_cap]
  have hint : intVal st₁.mem dst h L = wrap h L (intVal mem dst h L + intVal mem src h L) := by
    have hres := residue_signedVal_add h L (unsignedVal mem dst h L) (unsignedVal mem src h L) 0
    simp only [Nat.cast_zero, add_zero] at hres
    simp only [intVal, wrap, hres, ← hmod]
  exact runs_ret_le (by eval_expr) ⟨dst, src, L, rfl, rfl, hval, hmod, hint, hfr⟩
    (by simp [addToContract, Expr.size]; omega)

/-- In-place subtraction `dst[0..L) -= src[0..L)` modulo `capacity h L`. Args: `[dst, src, L]`. -/
def subFromStmt (h : ℕ) : Stmt :=
  .assign 3 (.const 0) ;;
  forRange 4 (.const 0) (.reg 2)
    (.assign 5 (.load (.bin .add (.reg 0) (.reg 4))) ;;
     .assign 6 (.bin .add (.load (.bin .add (.reg 1) (.reg 4))) (.reg 3)) ;;
     .cond (.bin .lt (.reg 5) (.reg 6))
       (.store (.bin .add (.reg 0) (.reg 4))
          (.bin .sub (.bin .add (.reg 5) (.const (base h))) (.reg 6)) ;;
        .assign 3 (.const 1))
       (.store (.bin .add (.reg 0) (.reg 4)) (.bin .sub (.reg 5) (.reg 6)) ;;
        .assign 3 (.const 0))) ;;
  .ret (.const 0)

def subFromContract (w h : ℕ) : Contract where
  pre args mem := ∃ dst src L, args = [dst, src, L] ∧ 0 < h ∧ 2 * h + 2 ≤ w ∧
    dst + L < 2 ^ w ∧ src + L < 2 ^ w ∧
    (dst + L ≤ src ∨ src + L ≤ dst) ∧ Valid mem dst h L ∧ Valid mem src h L
  post args mem ret mem' := ∃ dst src L, args = [dst, src, L] ∧ ret = 0 ∧
    Valid mem' dst h L ∧
    intVal mem' dst h L = wrap h L (intVal mem dst h L - intVal mem src h L) ∧
    (∀ z, z < dst ∨ dst + L ≤ z → mem' z = mem z)
  cost args _ := 65 * args.getD 2 0 + 18

lemma subFromStmt_noRand (h : ℕ) : (subFromStmt h).NoRand := by
  simp [subFromStmt, forRange, forUp, Stmt.NoRand]

private lemma signedVal_sub_mod {h L u v u' : ℕ} (hu' : u' < capacity h L)
    (heq : (u' : ℤ) ≡ (u : ℤ) - (v : ℤ) [ZMOD (capacity h L : ℤ)]) :
    signedVal h L u' = wrap h L (signedVal h L u - signedVal h L v) := by
  have hsu : signedVal h L u ≡ (u : ℤ) [ZMOD (capacity h L : ℤ)] := by
    dsimp [signedVal]; split_ifs <;> simp [Int.ModEq]
  have hsv : signedVal h L v ≡ (v : ℤ) [ZMOD (capacity h L : ℤ)] := by
    dsimp [signedVal]; split_ifs <;> simp [Int.ModEq]
  have hsub : signedVal h L u - signedVal h L v ≡ (u : ℤ) - (v : ℤ) [ZMOD (capacity h L : ℤ)] :=
    hsu.sub hsv
  have hmod : (u' : ℤ) % (capacity h L : ℤ) =
      (signedVal h L u - signedVal h L v) % (capacity h L : ℤ) :=
    heq.trans hsub.symm
  have hres : residue h L (signedVal h L u - signedVal h L v) = u' := by
    dsimp [residue]
    rw [← hmod, Int.emod_eq_of_lt (by omega) (by omega)]
    exact Int.toNat_natCast u'
  simp [wrap, hres]

/-- Verified contract for `subFromStmt`. -/
theorem subFrom_meetsContract {w h f : ℕ} {p : Program}
    (hp : p.procs[f]? = some (subFromStmt h)) :
    MeetsContract w p f (subFromContract w h) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨dst, src, L, rfl, hh, hw2, hdw_bd, hsw_bd, hdisj, hvd, hvs⟩
  have hdw : dst < 2 ^ w := hwords dst (by simp)
  have hsw : src < 2 ^ w := hwords src (by simp)
  have hlw : L < 2 ^ w := hwords L (by simp)
  have hb := base_lt_word hw2
  have hb1 : 1 < base h := Nat.one_lt_pow (Nat.ne_of_gt hh) (by decide)
  have hw1 : 1 < 2 ^ w := lt_trans hb1 hb
  have h2base : 2 * base h < 2 ^ w := by
    have hpow : 2 * base h < 4 * base h ^ 2 := by
      have h1 : 1 ≤ base h := Nat.one_le_pow h 2 (by decide)
      nlinarith [base_pos h]
    have hpow2 : 4 * base h ^ 2 = 2 ^ (2 * h + 2) := by
      rw [base, ← pow_mul, pow_add]; ring
    exact lt_of_lt_of_le (hpow.trans_eq hpow2) (Nat.pow_le_pow_right (by decide) hw2)
  refine runs_start_le ?_
  unfold subFromStmt
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  let Inv : ℕ → State → Prop := fun i st =>
    st.regs 0 = dst ∧ st.regs 1 = src ∧ st.regs 2 = L ∧ st.regs 4 = i ∧
    st.regs 3 ≤ 1 ∧ Valid st.mem dst h i ∧
    (unsignedVal st.mem dst h i : ℤ) = (unsignedVal mem dst h i : ℤ) -
      (unsignedVal mem src h i : ℤ) + (st.regs 3 : ℤ) * (capacity h i : ℤ) ∧
    (∀ j, i ≤ j → j < L → st.mem (dst + j) = mem (dst + j)) ∧
    (∀ z, z < dst ∨ dst + i ≤ z → st.mem z = mem z)
  have hloop : Triple w p
      (fun st => st = { (startState [dst, src, L] mem pos) with
        regs := Function.update (startState [dst, src, L] mem pos).regs 3 0 })
      (forRange 4 (.const 0) (.reg 2)
        (.assign 5 (.load (.bin .add (.reg 0) (.reg 4))) ;;
         .assign 6 (.bin .add (.load (.bin .add (.reg 1) (.reg 4))) (.reg 3)) ;;
         .cond (.bin .lt (.reg 5) (.reg 6))
           (.store (.bin .add (.reg 0) (.reg 4))
              (.bin .sub (.bin .add (.reg 5) (.const (base h))) (.reg 6)) ;;
            .assign 3 (.const 1))
           (.store (.bin .add (.reg 0) (.reg 4)) (.bin .sub (.reg 5) (.reg 6)) ;;
            .assign 3 (.const 0))))
      (normalPost (Inv L)) (fun _ => 65 * L + 7) := by
    refine (Triple.forRange_const 55 0 L (Nat.zero_le L) hw1 (fun _ => hlw)
      (fun st hst => by
        subst hst
        exact ⟨by eval_expr, by simp [startState], by simp [startState], by simp [startState],
          by simp, by simp, fun _ hi => by omega, by simp [unsignedVal],
          fun j _ _ => rfl, fun _ _ => rfl⟩)
      (fun _ _ _ _ hi => hi.2.2.2.1)
      (fun _ st _ _ hi => by have h2 := hi.2.2.1; eval_expr)
      (fun i _ hilt st ω' hi => by
        rcases hi with ⟨h0, h1, h2, h4, hb_le, hval, huv, htail, hfr⟩
        have hlt_di : dst + i < 2 ^ w := by omega
        have hlt_si : src + i < 2 ^ w := by omega
        have ha_eq : st.mem (dst + i) = mem (dst + i) := htail i le_rfl hilt
        have hs_eq : st.mem (src + i) = mem (src + i) := hfr (src + i) (by omega)
        have ha_lt : mem (dst + i) < base h := hvd i hilt
        have hs_lt : mem (src + i) < base h := hvs i hilt
        have hd_le : mem (src + i) + st.regs 3 ≤ base h := by omega
        have hd_w : mem (src + i) + st.regs 3 < 2 ^ w := lt_of_le_of_lt hd_le hb
        have ha_w : mem (dst + i) < 2 ^ w := lt_trans ha_lt hb
        have hs_w : mem (src + i) < 2 ^ w := lt_trans hs_lt hb
        refine runs_start_le (runs_seq_assign_le (v := mem (dst + i)) (by eval_expr) ?_)
        refine runs_seq_assign_le (v := mem (src + i) + st.regs 3) (by eval_expr) ?_
        wram_step
        · have hab : mem (dst + i) < mem (src + i) + st.regs 3 := hcond
          have hsum_w : mem (dst + i) + base h < 2 ^ w := by omega
          have hdigit_lt : mem (dst + i) + base h - (mem (src + i) + st.regs 3) < base h := by omega
          have hdigit_w : mem (dst + i) + base h - (mem (src + i) + st.regs 3) < 2 ^ w :=
            lt_trans hdigit_lt hb
          refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
          refine runs_assign_le (v := 1) (by eval_expr) ?_ (by wram_cost)
          refine ⟨⟨h0, h1, h2, by simp, by simp, fun j hj => ?_, ?_, fun j hj1 hj2 => ?_,
              fun z hz => ?_⟩, by simpa using h4⟩
          · dsimp only
            by_cases hji : j = i
            · subst j; simpa using hdigit_lt
            · rw [Function.update_of_ne (by omega)]; exact hval j (by omega)
          · dsimp only
            rw [Function.update_of_ne (by decide), Function.update_self]
            have huc := unsignedVal_congr (mem := Function.update st.mem (dst + i)
                (mem (dst + i) + base h - (mem (src + i) + st.regs 3))) (mem' := st.mem)
                (a := dst) (a' := dst) (h := h) (L := i) fun j hj =>
                  Function.update_of_ne (by omega) _ _
            rw [unsignedVal_snoc, huc, Function.update_self,
              unsignedVal_snoc mem dst h i, unsignedVal_snoc mem src h i, capacity_succ]
            simp only [Nat.cast_one, one_mul, Nat.cast_add, Nat.cast_mul]
            have hge : mem (src + i) + st.regs 3 ≤ mem (dst + i) + base h := by omega
            zify [hge]
            rw [huv]
            ring
          · dsimp only
            rw [Function.update_of_ne (by omega)]
            exact htail j (by omega) hj2
          · dsimp only
            rw [Function.update_of_ne (by omega)]
            exact hfr z (by omega)
        · have hba : mem (src + i) + st.regs 3 ≤ mem (dst + i) := by omega
          have hdigit_lt : mem (dst + i) - (mem (src + i) + st.regs 3) < base h := by omega
          have hdigit_w : mem (dst + i) - (mem (src + i) + st.regs 3) < 2 ^ w :=
            lt_trans hdigit_lt hb
          refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
          refine runs_assign_le (v := 0) (by eval_expr) ?_ (by wram_cost)
          refine ⟨⟨h0, h1, h2, by simp, by simp, fun j hj => ?_, ?_, fun j hj1 hj2 => ?_,
              fun z hz => ?_⟩, by simpa using h4⟩
          · dsimp only
            by_cases hji : j = i
            · subst j; simpa using hdigit_lt
            · rw [Function.update_of_ne (by omega)]; exact hval j (by omega)
          · dsimp only
            rw [Function.update_of_ne (by decide), Function.update_self]
            have huc := unsignedVal_congr (mem := Function.update st.mem (dst + i)
                (mem (dst + i) - (mem (src + i) + st.regs 3))) (mem' := st.mem)
                (a := dst) (a' := dst) (h := h) (L := i) fun j hj =>
                  Function.update_of_ne (by omega) _ _
            rw [unsignedVal_snoc, huc, Function.update_self,
              unsignedVal_snoc mem dst h i, unsignedVal_snoc mem src h i, capacity_succ]
            simp only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_add, Nat.cast_mul]
            zify [hba]
            rw [huv]
            ring
          · dsimp only
            rw [Function.update_of_ne (by omega)]
            exact htail j (by omega) hj2
          · dsimp only
            rw [Function.update_of_ne (by omega)]
            exact hfr z (by omega))).mono_cost (fun _ _ => by dsimp [Expr.size]; omega)
  refine runs_seq_triple_le hloop rfl (fun st₁ hinv => ?_)
  rcases hinv with ⟨_, _, _, _, _, hval, huv, _, hfr⟩
  have hlt_cap : unsignedVal st₁.mem dst h L < capacity h L := unsignedVal_lt hval
  have heq_mod : (unsignedVal st₁.mem dst h L : ℤ) ≡
      (unsignedVal mem dst h L : ℤ) - (unsignedVal mem src h L : ℤ) [ZMOD (capacity h L : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨-(st₁.regs 3 : ℤ), ?_⟩
    linarith [huv]
  have hint : intVal st₁.mem dst h L = wrap h L (intVal mem dst h L - intVal mem src h L) :=
    signedVal_sub_mod hlt_cap heq_mod
  exact runs_ret_le (by eval_expr) ⟨dst, src, L, rfl, rfl, hval, hint, hfr⟩
    (by simp [subFromContract, Expr.size]; omega)

/-! ## Deterministic `Nat.log 2` -/

/-- Compute `Nat.log 2 x` in `O(Nat.log 2 x + 1)` time. Args: `[x]` (`1 ≤ x`). -/
def log2Stmt : Stmt :=
  .assign 1 (.const 0) ;;
  .assign 2 (.reg 0) ;;
  .loop (.bin .lt (.const 1) (.reg 2))
    (.assign 2 (.bin .div (.reg 2) (.const 2)) ;;
     .assign 1 (.bin .add (.reg 1) (.const 1))) ;;
  .ret (.reg 1)

def log2Contract : Contract where
  pre args _ := ∃ x, args = [x] ∧ 1 ≤ x
  post args mem ret mem' := ∃ x, args = [x] ∧ mem' = mem ∧ ret = Nat.log 2 x
  cost args _ := 20 * Nat.log 2 (args.getD 0 0) + 20

lemma log2Stmt_noRand : log2Stmt.NoRand := by
  simp [log2Stmt, Stmt.NoRand]

/-- Verified contract for `log2Stmt`. -/
theorem log2_meetsContract {w f : ℕ} {p : Program}
    (hw : 2 < 2 ^ w) (hp : p.procs[f]? = some log2Stmt) :
    MeetsContract w p f log2Contract := by
  have hw1 : 1 < 2 ^ w := by omega
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨x, rfl, hx1⟩
  have hxw : x < 2 ^ w := hwords x (by simp)
  have hx_lt_pow : Nat.log 2 x < w := Nat.log_lt_of_lt_pow (by omega) hxw
  have hwx : w < 2 ^ w := Nat.lt_two_pow_self
  refine runs_start_le ?_
  unfold log2Stmt
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_assign_le (v := x) (by eval_expr) ?_
  let Inv : State → Prop := fun st =>
    st.mem = mem ∧ 1 ≤ st.regs 2 ∧ st.regs 2 < 2 ^ w ∧
    st.regs 1 + Nat.log 2 (st.regs 2) = Nat.log 2 x
  have hloop : Triple w p Inv
      (.loop (.bin .lt (.const 1) (.reg 2))
        (.assign 2 (.bin .div (.reg 2) (.const 2)) ;;
         .assign 1 (.bin .add (.reg 1) (.const 1))))
      (normalPost fun st => st.mem = mem ∧ st.regs 1 = Nat.log 2 x)
      (fun st => 18 * Nat.log 2 (st.regs 2) + 4) := by
    refine (Triple.loop_const_normal
      (m := fun st => Nat.log 2 (st.regs 2))
      (condVal := fun st => if 1 < st.regs 2 then 1 else 0)
      (bodyBound := 14)
      (fun st hInv => by rcases hInv with ⟨_, _, hr2w, _⟩; eval_expr)
      (fun st hInv hv => by
        rcases hInv with ⟨hmem, hr2_ge, _, hsum⟩
        have hle1 : st.regs 2 ≤ 1 := by by_contra h; simp [show 1 < st.regs 2 by omega] at hv
        have hr2_eq : st.regs 2 = 1 := by omega
        rw [hr2_eq, Nat.log_one_right] at hsum
        exact ⟨hmem, by omega⟩)
      (fun st hInv hv s ω' hEq => by
        subst hEq
        rcases hInv with ⟨hmem, hr2_ge, hr2w, hsum⟩
        have hgt1 : 1 < s.regs 2 := by by_contra h; simp [h] at hv
        have hlog_eq : Nat.log 2 (s.regs 2) = Nat.log 2 (s.regs 2 / 2) + 1 :=
          Nat.log_of_one_lt_of_le (by decide) hgt1
        have hr1_lt : s.regs 1 + 1 < 2 ^ w := by
          have : 1 ≤ Nat.log 2 (s.regs 2) := by rw [hlog_eq]; omega
          omega
        have hdiv_w : s.regs 2 / 2 < 2 ^ w := lt_of_le_of_lt (Nat.div_le_self _ _) hr2w
        have h1_eval : (Expr.bin .add (.reg 1) (.const 1)).eval w
            { s with regs := Function.update s.regs 2 (s.regs 2 / 2) } =
            some (s.regs 1 + 1) := by
          have h1_eq : Function.update s.regs 2 (s.regs 2 / 2) 1 = s.regs 1 :=
            Function.update_of_ne (by decide : (1 : ℕ) ≠ 2) (s.regs 2 / 2) s.regs
          eval_expr
        refine runs_start_le ?_
        refine runs_seq_assign_le (v := s.regs 2 / 2) (by eval_expr) ?_
        refine runs_assign_le h1_eval ?_ (by wram_cost)
        refine ⟨⟨hmem, by
            simp only [Function.update_of_ne (by decide : (2 : ℕ) ≠ 1), Function.update_self]
            omega,
          by simp [Function.update_of_ne, hdiv_w], by
            simp only [Function.update_self, Function.update_of_ne (by decide : (2 : ℕ) ≠ 1)]
            omega⟩, ?_⟩
        dsimp only
        rw [Function.update_of_ne (by decide), Function.update_self, hlog_eq]
        omega)).mono_cost (fun st _ => by dsimp [Expr.size]; omega)
  refine runs_seq_triple_le hloop ⟨rfl, hx1, hxw, by simp⟩ (fun st₁ hinv => ?_)
  rcases hinv with ⟨hmem, hr1⟩
  have hr1w : st₁.regs 1 < 2 ^ w := by omega
  exact runs_ret_le (by eval_expr) ⟨x, rfl, hmem, hr1⟩
    (by simp [log2Contract, Expr.size]; omega)

end

end MinCostFlow.LSF.Program
