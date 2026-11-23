module

public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.Machine.WideWord.Limbs

/-!
# Basic multiword operations on the Word-RAM (part 1)

This file defines and verifies the `O(L)`-time multiword unsigned integer procedures over the
`LimbsAt` representation (`L` limbs of `h` bits each, `B = 2 ^ h`, with `1 ≤ h` and `2 * h + 2 ≤ w`):

* `mwZero`: zero an `L`-limb word
* `mwCopy`: copy an `L`-limb word (disjoint or identical)
* `mwIsZero`: test whether an `L`-limb word equals `0`
* `mwFromHost`: encode a host word `< 2 ^ (L * h)` into `L` limbs
* `mwEq`, `mwLt`: equality and strict inequality
* `mwBitOp` (`.and`, `.or`, `.xor`): bitwise operations

Addition, subtraction, `mwShl1AddBit`, and the bundled module `arithBasicModule` are in
`MinCostFlow.Machine.WideWord.ArithAddSub`.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM

/-! ### Procedure bodies -/

/-- Zero `L` (`reg 1`) words at `dst` (`reg 0`), then return `0`. -/
def mwZero : Stmt :=
  forRange 2 (.const 0) (.reg 1)
    (.store (.bin .add (.reg 0) (.reg 2)) (.const 0)) ;;
  .ret (.const 0)

/-- Copy `L` (`reg 2`) words from `src` (`reg 0`) to `dst` (`reg 1`), then return `0`.
Works for disjoint ranges or `src = dst`. -/
def mwCopy : Stmt :=
  forRange 3 (.const 0) (.reg 2)
    (.store (.bin .add (.reg 1) (.reg 3)) (.load (.bin .add (.reg 0) (.reg 3)))) ;;
  .ret (.const 0)

/-- Test whether the `L` (`reg 1`) words at `src` (`reg 0`) are all `0`. Returns `1` or `0`. -/
def mwIsZero : Stmt :=
  .assign 2 (.const 1) ;;
  forRange 3 (.const 0) (.reg 1)
    (.cond (.load (.bin .add (.reg 0) (.reg 3))) (.assign 2 (.const 0)) .nop) ;;
  .ret (.reg 2)

/-- Encode host word `val` (`reg 0`) into `L` (`reg 2`) limbs of base `B` (`reg 3`) at
`dst` (`reg 1`), then return `0`. -/
def mwFromHost : Stmt :=
  .assign 4 (.reg 0) ;;
  forRange 5 (.const 0) (.reg 2)
    (.store (.bin .add (.reg 1) (.reg 5)) (.bin .mod (.reg 4) (.reg 3)) ;;
     .assign 4 (.bin .div (.reg 4) (.reg 3))) ;;
  .ret (.const 0)

/-- Test equality of two `L` (`reg 2`) limb words at `a` (`reg 0`) and `b` (`reg 1`). -/
def mwEq : Stmt :=
  .assign 3 (.const 1) ;;
  forRange 4 (.const 0) (.reg 2)
    (.cond (.bin .eq (.load (.bin .add (.reg 0) (.reg 4))) (.load (.bin .add (.reg 1) (.reg 4))))
      .nop (.assign 3 (.const 0))) ;;
  .ret (.reg 3)

/-- Test `a < b` for two `L` (`reg 2`) limb words at `a` (`reg 0`) and `b` (`reg 1`). -/
def mwLt : Stmt :=
  .assign 3 (.const 0) ;;
  forRange 4 (.const 0) (.reg 2)
    (.assign 5 (.load (.bin .add (.reg 0) (.reg 4))) ;;
     .assign 6 (.load (.bin .add (.reg 1) (.reg 4))) ;;
     .cond (.bin .lt (.reg 5) (.reg 6))
       (.assign 3 (.const 1))
       (.cond (.bin .lt (.reg 6) (.reg 5)) (.assign 3 (.const 0)) .nop)) ;;
  .ret (.reg 3)

/-- Limbwise binary operation `op` (`and`, `or`, `xor`) on `L` (`reg 3`) limbs at `a` (`reg 0`)
and `b` (`reg 1`), writing to `dst` (`reg 2`). -/
def mwBitOp (op : BinOp) : Stmt :=
  forRange 4 (.const 0) (.reg 3)
    (.store (.bin .add (.reg 2) (.reg 4))
      (.bin op (.load (.bin .add (.reg 0) (.reg 4))) (.load (.bin .add (.reg 1) (.reg 4))))) ;;
  .ret (.const 0)

/-! ### Contracts -/

def mwZeroContract (w : ℕ) : Contract where
  pre args _ := ∃ dst L, args = [dst, L] ∧ 1 < 2 ^ w ∧ dst + L < 2 ^ w
  post args mem v mem' :=
    ∃ dst L, args = [dst, L] ∧ v = 0 ∧
      ListAt mem' dst (List.replicate L 0) ∧
      (∀ p, p < dst ∨ dst + L ≤ p → mem' p = mem p)
  cost args _ := match args with | [_, L] => 14 * L + 12 | _ => 0

def mwCopyContract (w : ℕ) : Contract where
  pre args _ :=
    ∃ src dst L, args = [src, dst, L] ∧ 1 < 2 ^ w ∧
      src + L < 2 ^ w ∧ dst + L < 2 ^ w ∧
      (dst + L ≤ src ∨ src + L ≤ dst ∨ src = dst)
  post args mem v mem' :=
    ∃ src dst L, args = [src, dst, L] ∧ v = 0 ∧
      (∀ i < L, mem' (dst + i) = mem (src + i)) ∧
      (∀ p, p < dst ∨ dst + L ≤ p → mem' p = mem p)
  cost args _ := match args with | [_, _, L] => 17 * L + 10 | _ => 0

def mwIsZeroContract (w : ℕ) : Contract where
  pre args _ := ∃ src L, args = [src, L] ∧ 1 < 2 ^ w ∧ src + L < 2 ^ w
  post args mem v mem' :=
    ∃ src L, args = [src, L] ∧ mem' = mem ∧
      v = (if ∀ i < L, mem (src + i) = 0 then 1 else 0)
  cost args _ := match args with | [_, L] => 16 * L + 14 | _ => 0

def mwFromHostContract (w : ℕ) : Contract where
  pre args _ :=
    ∃ val dst L h, args = [val, dst, L, 2 ^ h] ∧
      1 ≤ h ∧ 2 * h + 2 ≤ w ∧ dst + L < 2 ^ w
  post args mem v mem' :=
    ∃ val dst L h, args = [val, dst, L, 2 ^ h] ∧ v = 0 ∧
      (∀ i < L, mem' (dst + i) = (val / 2 ^ (i * h)) % 2 ^ h) ∧
      (∀ p, p < dst ∨ dst + L ≤ p → mem' p = mem p)
  cost args _ := match args with | [_, _, L, _] => 25 * L + 15 | _ => 0

def mwEqContract (w : ℕ) : Contract where
  pre args _ :=
    ∃ a b L, args = [a, b, L] ∧ 1 < 2 ^ w ∧ a + L < 2 ^ w ∧ b + L < 2 ^ w
  post args mem v mem' :=
    ∃ a b L, args = [a, b, L] ∧ mem' = mem ∧
      v = (if ∀ i < L, mem (a + i) = mem (b + i) then 1 else 0)
  cost args _ := match args with | [_, _, L] => 25 * L + 15 | _ => 0

def mwLtContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ a b L h x y, args = [a, b, L] ∧
      1 ≤ h ∧ 2 * h + 2 ≤ w ∧ a + L < 2 ^ w ∧ b + L < 2 ^ w ∧
      LimbsAt mem a L h x ∧ LimbsAt mem b L h y
  post args mem v mem' :=
    ∃ a b L, args = [a, b, L] ∧ mem' = mem ∧
      (∀ h x y, LimbsAt mem a L h x → LimbsAt mem b L h y → v = (if x < y then 1 else 0))
  cost args _ := match args with | [_, _, L] => 35 * L + 15 | _ => 0

def mwBitOpContract (w : ℕ) (op : BinOp) : Contract where
  pre args mem :=
    ∃ a b dst L h x y, args = [a, b, dst, L] ∧
      1 ≤ h ∧ 2 * h + 2 ≤ w ∧ a + L < 2 ^ w ∧ b + L < 2 ^ w ∧ dst + L < 2 ^ w ∧
      (dst + L ≤ a ∨ a + L ≤ dst) ∧ (dst + L ≤ b ∨ b + L ≤ dst) ∧
      LimbsAt mem a L h x ∧ LimbsAt mem b L h y
  post args mem v mem' :=
    ∃ a b dst L, args = [a, b, dst, L] ∧ v = 0 ∧
      (∀ h x y, LimbsAt mem a L h x → LimbsAt mem b L h y → LimbsAt mem' dst L h (op.eval x y)) ∧
      (∀ p, p < dst ∨ dst + L ≤ p → mem' p = mem p)
  cost args _ := match args with | [_, _, _, L] => 28 * L + 12 | _ => 0

/-! ### Shared word-bound helpers -/

theorem two_pow_h_lt_two_pow_w {h w : ℕ} (hw : 2 * h + 2 ≤ w) : 2 ^ h < 2 ^ w :=
  Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem two_mul_pow_h_lt_two_pow_w {h w : ℕ} (hw : 2 * h + 2 ≤ w) : 2 * 2 ^ h < 2 ^ w := by
  have h1 : 2 * 2 ^ h = 2 ^ (h + 1) := by rw [Nat.pow_succ']
  rw [h1]
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem one_lt_two_pow_of_le {h w : ℕ} (hh : 1 ≤ h) (hw : 2 * h + 2 ≤ w) : 1 < 2 ^ w :=
  Nat.one_lt_two_pow (by omega)

private theorem div_step_mod_pow {val h i : ℕ} :
    (val / 2 ^ (i * h)) / 2 ^ h = val / 2 ^ ((i + 1) * h) := by
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, show i * h + h = (i + 1) * h by ring]

private theorem lt_prefix_step {x y h i : ℕ} :
    let ax := (x / 2 ^ (i * h)) % 2 ^ h
    let ay := (y / 2 ^ (i * h)) % 2 ^ h
    (if x % 2 ^ ((i + 1) * h) < y % 2 ^ ((i + 1) * h) then 1 else 0) =
      if ax < ay then 1
      else if ay < ax then 0
      else if x % 2 ^ (i * h) < y % 2 ^ (i * h) then 1 else 0 := by
  intro ax ay
  rw [limb_step_prefix x h i, limb_step_prefix y h i]
  have hxm : x % 2 ^ (i * h) < 2 ^ (i * h) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hym : y % 2 ^ (i * h) < 2 ^ (i * h) := Nat.mod_lt _ (Nat.two_pow_pos _)
  rcases lt_trichotomy ax ay with hlt | heq | hgt
  · have hsum : x % 2 ^ (i * h) + 2 ^ (i * h) * ax < y % 2 ^ (i * h) + 2 ^ (i * h) * ay := by
      have h1 : x % 2 ^ (i * h) + 2 ^ (i * h) * ax < 2 ^ (i * h) * (ax + 1) := by
        rw [Nat.mul_add, Nat.mul_one]; omega
      have h2 : 2 ^ (i * h) * (ax + 1) ≤ 2 ^ (i * h) * ay := Nat.mul_le_mul_left _ hlt
      omega
    rw [ite_eq_left hsum, ite_eq_left hlt]
  · have hnot1 : ¬ ax < ay := by omega
    have hnot2 : ¬ ay < ax := by omega
    dsimp only [ax, ay] at heq hnot1 hnot2
    rw [heq, ite_eq_right hnot1, ite_eq_right hnot2]
    have hiff : x % 2 ^ (i * h) + 2 ^ (i * h) * ((y / 2 ^ (i * h)) % 2 ^ h) <
        y % 2 ^ (i * h) + 2 ^ (i * h) * ((y / 2 ^ (i * h)) % 2 ^ h) ↔
        x % 2 ^ (i * h) < y % 2 ^ (i * h) := by omega
    simp only [hiff]
  · have hnot1 : ¬ ax < ay := by omega
    have hsum : ¬ x % 2 ^ (i * h) + 2 ^ (i * h) * ax < y % 2 ^ (i * h) + 2 ^ (i * h) * ay := by
      have h1 : y % 2 ^ (i * h) + 2 ^ (i * h) * ay < 2 ^ (i * h) * (ay + 1) := by
        rw [Nat.mul_add, Nat.mul_one]; omega
      have h2 : 2 ^ (i * h) * (ay + 1) ≤ 2 ^ (i * h) * ax := Nat.mul_le_mul_left _ hgt
      omega
    rw [ite_eq_right hsum, ite_eq_right hnot1, ite_eq_left hgt]

theorem limbsAt_lt_iff {mem : ℕ → ℕ} {a b L h x y h' x' y' : ℕ}
    (hx : LimbsAt mem a L h x) (hy : LimbsAt mem b L h y)
    (hx' : LimbsAt mem a L h' x') (hy' : LimbsAt mem b L h' y') :
    x < y ↔ x' < y' := by
  suffices key : ∀ i ≤ L, (if x % 2 ^ (i * h) < y % 2 ^ (i * h) then 1 else 0) =
      (if x' % 2 ^ (i * h') < y' % 2 ^ (i * h') then 1 else 0) by
    have hL := key L le_rfl
    rw [Nat.mod_eq_of_lt hx.lt_pow, Nat.mod_eq_of_lt hy.lt_pow,
      Nat.mod_eq_of_lt hx'.lt_pow, Nat.mod_eq_of_lt hy'.lt_pow] at hL
    by_cases hxy : x < y <;> by_cases hxy' : x' < y' <;> simp [hxy, hxy'] at hL ⊢
  intro i hi
  induction i with
  | zero => simp [Nat.mod_one]
  | succ i ih =>
    have hiL : i < L := by omega
    rw [lt_prefix_step (x := x) (y := y) (h := h) (i := i),
      lt_prefix_step (x := x') (y := y') (h := h') (i := i)]
    have hax : (x / 2 ^ (i * h)) % 2 ^ h = (x' / 2 ^ (i * h')) % 2 ^ h' := by
      rw [← hx.getElem hiL, ← hx'.getElem hiL]
    have hay : (y / 2 ^ (i * h)) % 2 ^ h = (y' / 2 ^ (i * h')) % 2 ^ h' := by
      rw [← hy.getElem hiL, ← hy'.getElem hiL]
    rw [hax, hay, ih (by omega)]

/-! ### Contract proofs -/

theorem mwZero_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b [mwZero]) :
    MeetsContract w p b (mwZeroContract w) := by
  refine meetsContract_of_runs hp.head fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨dst, L, rfl, hw, hbound⟩
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 2) (lo := .const 0) (hi := .reg 1)
    (body := .store (.bin .add (.reg 0) (.reg 2)) (.const 0))
    (P := fun st => st = startState [dst, L] mem pos)
    (Inv := fun i st => st.regs 0 = dst ∧ st.regs 1 = L ∧ st.regs 2 = i ∧
      ListAt st.mem dst (List.replicate i 0) ∧ ∀ x, x < dst ∨ dst + i ≤ x → st.mem x = mem x)
    5 0 L (Nat.zero_le L) hw (fun _ => by omega)
    (fun st hst => by
      subst hst
      refine ⟨by eval_expr, ?_, ?_, ?_, listAt_nil _ _, fun _ _ => rfl⟩ <;> simp [startState])
    (fun _ st _ _ hi => hi.2.2.1)
    (fun _ st _ _ hi => by have h1 : st.regs 1 = L := hi.2.1; eval_expr)
    (fun i _ hilt => by
      intro st _ ⟨h0, h1, h2, hlist, hframe⟩
      refine ⟨.normal, { st with mem := Function.update st.mem (dst + i) 0 }, 5, ?_, ?_, by simp⟩
      · refine runs_store_iff.mpr ⟨dst + i, 0, by eval_expr, by eval_expr, rfl, rfl, by simp⟩
      · refine ⟨⟨h0, h1, by simp, ?_, ?_⟩, h2⟩
        · rw [List.replicate_succ']
          simpa [List.length_replicate] using hlist.snoc 0
        · intro x hx
          dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hframe x (by omega))
  refine runs_start_le ?_
  dsimp only [mwZero]
  refine runs_seq_triple_le hloop rfl ?_
  intro st₁ ⟨_, _, _, hlist, hframe⟩
  refine runs_ret_le (by eval_expr) ⟨dst, L, rfl, rfl, hlist, hframe⟩ ?_
  dsimp only [mwZeroContract, Expr.size_const, Expr.size_reg, Nat.sub_zero]
  omega

theorem mwCopy_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b [mwCopy]) :
    MeetsContract w p b (mwCopyContract w) := by
  refine meetsContract_of_runs hp.head fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨src, dst, L, rfl, hw, hsrc, hdst, hnov⟩
  have hL : L < 2 ^ w := hwords L (by simp)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 3) (lo := .const 0) (hi := .reg 2)
    (body := .store (.bin .add (.reg 1) (.reg 3)) (.load (.bin .add (.reg 0) (.reg 3))))
    (P := fun st => st = startState [src, dst, L] mem pos)
    (Inv := fun i st => st.regs 0 = src ∧ st.regs 1 = dst ∧ st.regs 2 = L ∧ st.regs 3 = i ∧
      (∀ j < i, st.mem (dst + j) = mem (src + j)) ∧
      (∀ x, x < dst ∨ dst + i ≤ x → st.mem x = mem x))
    8 0 L (Nat.zero_le L) hw (fun _ => hL)
    (fun st hst => by
      subst hst
      refine ⟨by eval_expr, ?_, ?_, ?_, ?_, fun _ h => False.elim (Nat.not_lt_zero _ h),
        fun _ _ => rfl⟩ <;> simp [startState])
    (fun _ st _ _ hi => hi.2.2.2.1)
    (fun _ st _ _ hi => by have h2 : st.regs 2 = L := hi.2.2.1; eval_expr)
    (fun i _ hilt => by
      intro st _ ⟨h0, h1, h2, h3, hcopied, hframe⟩
      have hsrc_mem : st.mem (src + i) = mem (src + i) := by
        rcases hnov with hnov | hnov | rfl
        · exact hframe (src + i) (by omega)
        · exact hframe (src + i) (by omega)
        · exact hframe (src + i) (by omega)
      refine ⟨.normal, { st with mem := Function.update st.mem (dst + i) (mem (src + i)) },
        8, ?_, ?_, by simp⟩
      · refine runs_store_iff.mpr
          ⟨dst + i, mem (src + i), by eval_expr, ?_, rfl, rfl, by simp⟩
        rw [← hsrc_mem]
        eval_expr
      · refine ⟨⟨h0, h1, h2, by simp, ?_, ?_⟩, h3⟩
        · intro j hj
          dsimp only
          by_cases hji : j = i
          · subst hji; rw [Function.update_self]
          · rw [Function.update_of_ne (by omega)]; exact hcopied j (by omega)
        · intro x hx
          dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hframe x (by omega))
  refine runs_start_le ?_
  dsimp only [mwCopy]
  refine runs_seq_triple_le hloop rfl ?_
  intro st₁ ⟨_, _, _, _, hcopied, hframe⟩
  refine runs_ret_le (by eval_expr) ⟨src, dst, L, rfl, rfl, hcopied, hframe⟩ ?_
  dsimp only [mwCopyContract, Expr.size_const, Expr.size_reg, Nat.sub_zero]
  omega

theorem mwIsZero_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b [mwIsZero]) :
    MeetsContract w p b (mwIsZeroContract w) := by
  refine meetsContract_of_runs hp.head fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨src, L, rfl, hw, hsrc⟩
  have hL : L < 2 ^ w := hwords L (by simp)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 3) (lo := .const 0) (hi := .reg 1)
    (body := .cond (.load (.bin .add (.reg 0) (.reg 3))) (.assign 2 (.const 0)) .nop)
    (P := fun st => st = { startState [src, L] mem pos with
      regs := Function.update (startState [src, L] mem pos).regs 2 1 })
    (Inv := fun i st => st.mem = mem ∧ st.regs 0 = src ∧ st.regs 1 = L ∧ st.regs 3 = i ∧
      st.regs 2 = (if ∀ j < i, mem (src + j) = 0 then 1 else 0))
    7 0 L (Nat.zero_le L) hw (fun _ => hL)
    (fun st hst => by
      subst hst
      refine ⟨by eval_expr, rfl, ?_, ?_, ?_, ?_⟩ <;> simp [startState])
    (fun _ st _ _ hi => hi.2.2.2.1)
    (fun _ st _ _ hi => by have h1 : st.regs 1 = L := hi.2.2.1; eval_expr)
    (fun i _ hilt => by
      intro st _ ⟨hmem, h0, h1, h3, h2⟩
      dsimp only
      refine runs_start_le ?_
      have he : (Expr.load (.bin .add (.reg 0) (.reg 3))).eval w st = some (mem (src + i)) := by
        rw [← hmem]
        eval_expr
      refine runs_cond_le he (fun hne => ?_) (fun heq => ?_)
      · refine runs_assign_le (by eval_expr) ?_ (by wram_cost)
        refine ⟨⟨hmem, h0, h1, ?_, ?_⟩, h3⟩
        · simp
        · have hnot : ¬ ∀ j < i + 1, mem (src + j) = 0 := fun h => hne (h i (by omega))
          simp only [Function.update_of_ne (by decide : (2 : ℕ) ≠ 3), Function.update_self]
          rw [ite_eq_right hnot]
      · refine runs_nop_le ?_ (by wram_cost)
        refine ⟨⟨hmem, h0, h1, ?_, ?_⟩, h3⟩
        · simp
        · simp only [Function.update_of_ne (by decide : (2 : ℕ) ≠ 3)]
          by_cases hprev : ∀ j < i, mem (src + j) = 0
          · have hnext : ∀ j < i + 1, mem (src + j) = 0 := fun j hj =>
              if hj_eq : j = i then hj_eq ▸ heq else hprev j (by omega)
            rw [ite_eq_left hprev] at h2
            rw [ite_eq_left hnext]
            exact h2
          · have hnext : ¬ ∀ j < i + 1, mem (src + j) = 0 := fun h =>
              hprev fun j hj => h j (by omega)
            rw [ite_eq_right hprev] at h2
            rw [ite_eq_right hnext]
            exact h2)
  refine runs_start_le ?_
  dsimp only [mwIsZero]
  wram_step
  · refine runs_seq_triple_le hloop rfl ?_
    intro st₁ ⟨hmem, _, _, _, h2⟩
    refine runs_ret_le (by eval_expr) ⟨src, L, rfl, hmem, h2⟩ ?_
    dsimp only [mwIsZeroContract, Expr.size_const, Expr.size_reg, Nat.sub_zero]
    omega

theorem mwFromHost_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b [mwFromHost]) :
    MeetsContract w p b (mwFromHostContract w) := by
  refine meetsContract_of_runs hp.head fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨val, dst, L, h, rfl, hh, hw2, hdst⟩
  have hw1 : 1 < 2 ^ w := one_lt_two_pow_of_le hh hw2
  have hval : val < 2 ^ w := hwords val (by simp)
  have hL : L < 2 ^ w := hwords L (by simp)
  have hB : 2 ^ h < 2 ^ w := two_pow_h_lt_two_pow_w hw2
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 5) (lo := .const 0) (hi := .reg 2)
    (body := .store (.bin .add (.reg 1) (.reg 5)) (.bin .mod (.reg 4) (.reg 3)) ;;
             .assign 4 (.bin .div (.reg 4) (.reg 3)))
    (P := fun st => st = { startState [val, dst, L, 2 ^ h] mem pos with
      regs := Function.update (startState [val, dst, L, 2 ^ h] mem pos).regs 4 val })
    (Inv := fun i st => st.regs 1 = dst ∧ st.regs 2 = L ∧ st.regs 3 = 2 ^ h ∧
      st.regs 4 = val / 2 ^ (i * h) ∧ st.regs 5 = i ∧
      (∀ j < i, st.mem (dst + j) = (val / 2 ^ (j * h)) % 2 ^ h) ∧
      (∀ p, p < dst ∨ dst + i ≤ p → st.mem p = mem p))
    15 0 L (Nat.zero_le L) hw1 (fun _ => hL)
    (fun st hst => by
      subst hst
      refine ⟨by eval_expr, ?_, ?_, ?_, ?_, ?_, fun _ hj => absurd hj (Nat.not_lt_zero _),
        fun _ _ => rfl⟩ <;> simp [startState])
    (fun _ st _ _ hi => hi.2.2.2.2.1)
    (fun _ st _ _ hi => by have h2 : st.regs 2 = L := hi.2.1; eval_expr)
    (fun i _ hilt => by
      intro st _ ⟨h1, h2, h3, h4, h5, hlim, hframe⟩
      have hcur_lt : val / 2 ^ (i * h) < 2 ^ w :=
        lt_of_le_of_lt (Nat.div_le_self _ _) hval
      refine runs_start_le ?_
      wram_step
      wram_step
      · refine ⟨⟨h1, h2, h3, ?_, ?_, ?_, ?_⟩, h5⟩
        · simp [div_step_mod_pow]
        · simp
        · intro j hj
          dsimp only
          by_cases hji : j = i
          · subst hji; simp
          · rw [Function.update_of_ne (by omega)]
            exact hlim j (by omega)
        · intro q hq
          dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hframe q (by omega)
      · wram_cost)
  refine runs_start_le ?_
  dsimp only [mwFromHost]
  wram_step
  · refine runs_seq_triple_le hloop rfl ?_
    intro st₁ ⟨_, _, _, _, _, hlim, hframe⟩
    refine runs_ret_le (by eval_expr) ⟨val, dst, L, h, rfl, rfl, hlim, hframe⟩ ?_
    dsimp only [mwFromHostContract, Expr.size_const, Expr.size_reg, Nat.sub_zero]
    omega

theorem mwEq_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b [mwEq]) :
    MeetsContract w p b (mwEqContract w) := by
  refine meetsContract_of_runs hp.head fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨a, b', L, rfl, hw, ha, hb⟩
  have hL : L < 2 ^ w := hwords L (by simp)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 4) (lo := .const 0) (hi := .reg 2)
    (body := .cond (.bin .eq (.load (.bin .add (.reg 0) (.reg 4)))
        (.load (.bin .add (.reg 1) (.reg 4))))
      .nop (.assign 3 (.const 0)))
    (P := fun st => st = { startState [a, b', L] mem pos with
      regs := Function.update (startState [a, b', L] mem pos).regs 3 1 })
    (Inv := fun i st => st.mem = mem ∧ st.regs 0 = a ∧ st.regs 1 = b' ∧ st.regs 2 = L ∧
      st.regs 4 = i ∧ st.regs 3 = (if ∀ j < i, mem (a + j) = mem (b' + j) then 1 else 0))
    15 0 L (Nat.zero_le L) hw (fun _ => hL)
    (fun st hst => by
      subst hst
      refine ⟨by eval_expr, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [startState])
    (fun _ st _ _ hi => hi.2.2.2.2.1)
    (fun _ st _ _ hi => by have h2 : st.regs 2 = L := hi.2.2.2.1; eval_expr)
    (fun i _ hilt => by
      intro st _ ⟨hmem, h0, h1, h2, h4, h3⟩
      dsimp only
      refine runs_start_le ?_
      have ha_m : st.mem (a + i) = mem (a + i) := by rw [hmem]
      have hb_m : st.mem (b' + i) = mem (b' + i) := by rw [hmem]
      have he : (Expr.bin .eq (.load (.bin .add (.reg 0) (.reg 4)))
          (.load (.bin .add (.reg 1) (.reg 4)))).eval w st =
          some (if mem (a + i) = mem (b' + i) then 1 else 0) := by
        refine Expr.eval_eq_op ?_ ?_ hw
        · exact Expr.eval_load_of_eq (by eval_expr) ha_m
        · exact Expr.eval_load_of_eq (by eval_expr) hb_m
      refine runs_cond_le he (fun hne => ?_) (fun heq => ?_)
      · have hlimb : mem (a + i) = mem (b' + i) := by
          by_contra hne'
          simp [hne'] at hne
        refine runs_nop_le ?_ (by wram_cost)
        refine ⟨⟨hmem, h0, h1, h2, ?_, ?_⟩, h4⟩
        · simp
        · simp only [Function.update_of_ne (by decide : (3 : ℕ) ≠ 4)]
          by_cases hprev : ∀ j < i, mem (a + j) = mem (b' + j)
          · have hnext : ∀ j < i + 1, mem (a + j) = mem (b' + j) := fun j hj =>
              if hj_eq : j = i then hj_eq ▸ hlimb else hprev j (by omega)
            rw [ite_eq_left hprev] at h3
            rw [ite_eq_left hnext]
            exact h3
          · have hnext : ¬ ∀ j < i + 1, mem (a + j) = mem (b' + j) := fun h =>
              hprev fun j hj => h j (by omega)
            rw [ite_eq_right hprev] at h3
            rw [ite_eq_right hnext]
            exact h3
      · have hlimb : mem (a + i) ≠ mem (b' + i) := by
          intro heq'
          simp [heq'] at heq
        refine runs_assign_le (by eval_expr) ?_ (by wram_cost)
        refine ⟨⟨hmem, h0, h1, h2, ?_, ?_⟩, h4⟩
        · simp
        · have hnot : ¬ ∀ j < i + 1, mem (a + j) = mem (b' + j) := fun h => hlimb (h i (by omega))
          simp only [Function.update_of_ne (by decide : (3 : ℕ) ≠ 4), Function.update_self]
          rw [ite_eq_right hnot])
  refine runs_start_le ?_
  dsimp only [mwEq]
  wram_step
  · refine runs_seq_triple_le hloop rfl ?_
    intro st₁ ⟨hmem, _, _, _, _, h3⟩
    refine runs_ret_le (by eval_expr) ⟨a, b', L, rfl, hmem, h3⟩ ?_
    dsimp only [mwEqContract, Expr.size_const, Expr.size_reg, Nat.sub_zero]
    omega

theorem mwLt_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b [mwLt]) :
    MeetsContract w p b (mwLtContract w) := by
  refine meetsContract_of_runs hp.head fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨a, b', L, h, x, y, rfl, hh, hw2, ha, hb, hx, hy⟩
  have hw1 : 1 < 2 ^ w := one_lt_two_pow_of_le hh hw2
  have hL : L < 2 ^ w := hwords L (by simp)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 4) (lo := .const 0) (hi := .reg 2)
    (body := .assign 5 (.load (.bin .add (.reg 0) (.reg 4))) ;;
             .assign 6 (.load (.bin .add (.reg 1) (.reg 4))) ;;
             .cond (.bin .lt (.reg 5) (.reg 6))
               (.assign 3 (.const 1))
               (.cond (.bin .lt (.reg 6) (.reg 5)) (.assign 3 (.const 0)) .nop))
    (P := fun st => st = { startState [a, b', L] mem pos with
      regs := Function.update (startState [a, b', L] mem pos).regs 3 0 })
    (Inv := fun i st => st.mem = mem ∧ st.regs 0 = a ∧ st.regs 1 = b' ∧ st.regs 2 = L ∧
      st.regs 4 = i ∧ st.regs 3 = (if x % 2 ^ (i * h) < y % 2 ^ (i * h) then 1 else 0))
    24 0 L (Nat.zero_le L) hw1 (fun _ => hL)
    (fun st hst => by
      subst hst
      refine ⟨by eval_expr, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [startState, Nat.mod_one])
    (fun _ st _ _ hi => hi.2.2.2.2.1)
    (fun _ st _ _ hi => by have h2 : st.regs 2 = L := hi.2.2.2.1; eval_expr)
    (fun i _ hilt => by
      intro st _ ⟨hmem, h0, h1, h2, h4, h3⟩
      dsimp only
      have ha_val : st.mem (a + i) = (x / 2 ^ (i * h)) % 2 ^ h := by
        rw [hmem]; exact hx.getElem hilt
      have hb_val : st.mem (b' + i) = (y / 2 ^ (i * h)) % 2 ^ h := by
        rw [hmem]; exact hy.getElem hilt
      refine runs_start_le ?_
      refine runs_seq_assign_le (Expr.eval_load_of_eq (by eval_expr) ha_val) ?_
      refine runs_seq_assign_le (Expr.eval_load_of_eq (by eval_expr) hb_val) ?_
      refine runs_cond_le (Expr.eval_lt_op (by eval_expr) (by eval_expr) hw1) (fun hne => ?_) (fun heq => ?_)
      · have hlt_a : (x / 2 ^ (i * h)) % 2 ^ h < (y / 2 ^ (i * h)) % 2 ^ h := by
          by_contra hnot; simp [hnot] at hne
        refine runs_assign_le (by eval_expr) ?_ (by wram_cost)
        refine ⟨⟨hmem, h0, h1, h2, ?_, ?_⟩, ?_⟩
        · simp
        · simp only [Function.update_of_ne (by decide : (3 : ℕ) ≠ 4), Function.update_self]
          rw [lt_prefix_step, ite_eq_left hlt_a]
        · simp [h4]
      · have hnot_a : ¬ (x / 2 ^ (i * h)) % 2 ^ h < (y / 2 ^ (i * h)) % 2 ^ h := by
          intro h; simp [h] at heq
        refine runs_cond_le (Expr.eval_lt_op (by eval_expr) (by eval_expr) hw1) (fun hne2 => ?_) (fun heq2 => ?_)
        · have hgt_a : (y / 2 ^ (i * h)) % 2 ^ h < (x / 2 ^ (i * h)) % 2 ^ h := by
            by_contra hnot; simp [hnot] at hne2
          refine runs_assign_le (by eval_expr) ?_ (by wram_cost)
          refine ⟨⟨hmem, h0, h1, h2, ?_, ?_⟩, ?_⟩
          · simp
          · simp only [Function.update_of_ne (by decide : (3 : ℕ) ≠ 4), Function.update_self]
            rw [lt_prefix_step, ite_eq_right hnot_a, ite_eq_left hgt_a]
          · simp [h4]
        · have hnot_b : ¬ (y / 2 ^ (i * h)) % 2 ^ h < (x / 2 ^ (i * h)) % 2 ^ h := by
            intro h; simp [h] at heq2
          refine runs_nop_le ?_ (by wram_cost)
          refine ⟨⟨hmem, h0, h1, h2, ?_, ?_⟩, ?_⟩
          · simp
          · simp only [Function.update_of_ne (by decide : (3 : ℕ) ≠ 4),
              Function.update_of_ne (by decide : (3 : ℕ) ≠ 6),
              Function.update_of_ne (by decide : (3 : ℕ) ≠ 5)]
            rw [lt_prefix_step, ite_eq_right hnot_a, ite_eq_right hnot_b]
            exact h3
          · simp [h4])
  refine runs_start_le ?_
  dsimp only [mwLt]
  wram_step
  · refine runs_seq_triple_le hloop rfl ?_
    intro st₁ ⟨hmem, _, _, _, _, h3⟩
    have hmod_x : x % 2 ^ (L * h) = x := Nat.mod_eq_of_lt hx.lt_pow
    have hmod_y : y % 2 ^ (L * h) = y := Nat.mod_eq_of_lt hy.lt_pow
    rw [hmod_x, hmod_y] at h3
    refine runs_ret_le (by eval_expr) ⟨a, b', L, rfl, hmem, fun h' x' y' hx' hy' => ?_⟩ ?_
    · dsimp only [Outcome.value]
      congr 1
      exact propext (limbsAt_lt_iff hx hy hx' hy')
    · dsimp only [mwLtContract, Expr.size_const, Expr.size_reg, Nat.sub_zero]
      omega

theorem mwBitOp_meetsContract {w : ℕ} {p : Program} {b : ℕ} {op : BinOp}
    (hop : op = .and ∨ op = .or ∨ op = .xor)
    (hp : p.HasAt b [mwBitOp op]) :
    MeetsContract w p b (mwBitOpContract w op) := by
  refine meetsContract_of_runs hp.head fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨a, b', dst, L, h, x, y, rfl, hh, hw2, ha, hb, hdst, hnova, hnovb, hx, hy⟩
  have hw1 : 1 < 2 ^ w := one_lt_two_pow_of_le hh hw2
  have hB : 2 ^ h < 2 ^ w := two_pow_h_lt_two_pow_w hw2
  have hL : L < 2 ^ w := hwords L (by simp)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 4) (lo := .const 0) (hi := .reg 3)
    (body := .store (.bin .add (.reg 2) (.reg 4))
      (.bin op (.load (.bin .add (.reg 0) (.reg 4))) (.load (.bin .add (.reg 1) (.reg 4)))))
    (P := fun st => st = startState [a, b', dst, L] mem pos)
    (Inv := fun i st => st.regs 0 = a ∧ st.regs 1 = b' ∧ st.regs 2 = dst ∧ st.regs 3 = L ∧
      st.regs 4 = i ∧
      (∀ j < i, st.mem (dst + j) = (op.eval x y / 2 ^ (j * h)) % 2 ^ h) ∧
      (∀ p, p < dst ∨ dst + i ≤ p → st.mem p = mem p))
    16 0 L (Nat.zero_le L) hw1 (fun _ => hL)
    (fun st hst => by
      subst hst
      refine ⟨by eval_expr, ?_, ?_, ?_, ?_, ?_, fun _ hj => absurd hj (Nat.not_lt_zero _),
        fun _ _ => rfl⟩ <;> simp [startState])
    (fun _ st _ _ hi => hi.2.2.2.2.1)
    (fun _ st _ _ hi => by have h3 : st.regs 3 = L := hi.2.2.2.1; eval_expr)
    (fun i _ hilt => by
      intro st _ ⟨h0, h1, h2, h3, h4, hlim, hframe⟩
      have ha_m : st.mem (a + i) = (x / 2 ^ (i * h)) % 2 ^ h := by
        rw [hframe (a + i) (by omega)]; exact hx.getElem hilt
      have hb_m : st.mem (b' + i) = (y / 2 ^ (i * h)) % 2 ^ h := by
        rw [hframe (b' + i) (by omega)]; exact hy.getElem hilt
      have hop_limb : op.eval ((x / 2 ^ (i * h)) % 2 ^ h) ((y / 2 ^ (i * h)) % 2 ^ h) =
          (op.eval x y / 2 ^ (i * h)) % 2 ^ h := by
        rcases hop with rfl | rfl | rfl
        · exact and_limb.symm
        · exact or_limb.symm
        · exact xor_limb.symm
      have hop_lt : op.eval ((x / 2 ^ (i * h)) % 2 ^ h) ((y / 2 ^ (i * h)) % 2 ^ h) < 2 ^ w := by
        rw [hop_limb]
        exact lt_trans (Nat.mod_lt _ (Nat.two_pow_pos _)) hB
      have haddr_eval : (Expr.bin .add (.reg 2) (.reg 4)).eval w st = some (dst + i) := by eval_expr
      have hval_eval : (Expr.bin op (.load (.bin .add (.reg 0) (.reg 4)))
          (.load (.bin .add (.reg 1) (.reg 4)))).eval w st =
          some (op.eval ((x / 2 ^ (i * h)) % 2 ^ h) ((y / 2 ^ (i * h)) % 2 ^ h)) :=
        Expr.eval_bin (Expr.eval_load_of_eq (by eval_expr) ha_m)
          (Expr.eval_load_of_eq (by eval_expr) hb_m) hop_lt
      refine runs_start_le ?_
      refine runs_store_le haddr_eval hval_eval ?_ (by wram_cost)
      refine ⟨⟨h0, h1, h2, h3, by simp, ?_, ?_⟩, h4⟩
      · intro j hj
        dsimp only
        by_cases hji : j = i
        · subst hji; rw [Function.update_self, hop_limb]
        · rw [Function.update_of_ne (by omega)]; exact hlim j (by omega)
      · intro q hq
        dsimp only
        rw [Function.update_of_ne (by omega)]; exact hframe q (by omega))
  refine runs_start_le ?_
  dsimp only [mwBitOp]
  refine runs_seq_triple_le hloop rfl ?_
  intro st₁ ⟨_, _, _, _, _, hlim, hframe⟩
  refine runs_ret_le (by eval_expr) ⟨a, b', dst, L, rfl, rfl, ?_, hframe⟩ ?_
  · intro h' x' y' hx' hy'
    refine limbsAt_iff_pointwise.mpr ⟨?_, fun j hj => ?_⟩
    · rcases hop with rfl | rfl | rfl
      · exact and_lt_two_pow_left hx'.lt_pow
      · exact or_lt_two_pow_both hx'.lt_pow hy'.lt_pow
      · exact xor_lt_two_pow_both hx'.lt_pow hy'.lt_pow
    · rw [hlim j hj]
      have ha_eq : (x / 2 ^ (j * h)) % 2 ^ h = (x' / 2 ^ (j * h')) % 2 ^ h' := by
        rw [← hx.getElem hj, ← hx'.getElem hj]
      have hb_eq : (y / 2 ^ (j * h)) % 2 ^ h = (y' / 2 ^ (j * h')) % 2 ^ h' := by
        rw [← hy.getElem hj, ← hy'.getElem hj]
      rcases hop with rfl | rfl | rfl <;> dsimp only [BinOp.eval]
      · rw [and_limb, ha_eq, hb_eq, ← and_limb]
      · rw [or_limb, ha_eq, hb_eq, ← or_limb]
      · rw [xor_limb, ha_eq, hb_eq, ← xor_limb]
  · dsimp only [mwBitOpContract, Expr.size_const, Expr.size_reg, Nat.sub_zero]
    omega

end MinCostFlow.WideWord
