module

public import WordRAM.Logic
public import WordRAM.Tactic
import WordRAM.Layout
public import MinCostFlow.Machine.WideWord.ArithBasic

/-!
# Basic multiword operations on the Word-RAM (part 2)

This file defines and verifies the remaining `O(L)`-time basic multiword procedures:

* `mwAdd`: addition modulo `2 ^ (L * h)`, returning the carry bit
* `mwRawSub`: borrow subtraction modulo `2 ^ (L * h)`, returning the final borrow bit
* `mwSub`: truncating natural-number subtraction
* `mwShl1AddBit`: in-place `2 * x + bit` modulo `2 ^ (L * h)`, returning the carry bit

It also bundles all 13 basic operations into `arithBasicModule b` with fixed procedure offsets
`idxZero` through `idxShl1AddBit` and provides `*_of_module` contract theorems.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM

/-! ### Procedure indices inside `arithBasicModule b` -/

def idxZero : ℕ := 0
def idxCopy : ℕ := 1
def idxIsZero : ℕ := 2
def idxFromHost : ℕ := 3
def idxEq : ℕ := 4
def idxLt : ℕ := 5
def idxAnd : ℕ := 6
def idxOr : ℕ := 7
def idxXor : ℕ := 8
def idxAdd : ℕ := 9
def idxRawSub : ℕ := 10
def idxSub : ℕ := 11
def idxShl1AddBit : ℕ := 12

/-! ### Procedure bodies -/

/-- Add `a` (`reg 0`) and `b` (`reg 1`) into `dst` (`reg 2`), `L` (`reg 3`) limbs of base
`B` (`reg 4`), returning the carry bit (`0` or `1`). -/
def mwAdd : Stmt :=
  .assign 5 (.const 0) ;;
  forRange 6 (.const 0) (.reg 3)
    (.assign 7 (.bin .add (.bin .add (.load (.bin .add (.reg 0) (.reg 6)))
        (.load (.bin .add (.reg 1) (.reg 6)))) (.reg 5)) ;;
     .cond (.bin .lt (.reg 7) (.reg 4))
       (.store (.bin .add (.reg 2) (.reg 6)) (.reg 7) ;; .assign 5 (.const 0))
       (.store (.bin .add (.reg 2) (.reg 6)) (.bin .sub (.reg 7) (.reg 4)) ;;
        .assign 5 (.const 1))) ;;
  .ret (.reg 5)

/-- Borrow-subtract `b` (`reg 1`) from `a` (`reg 0`) into `dst` (`reg 2`), `L` (`reg 3`) limbs
of base `B` (`reg 4`), returning the final borrow (`0` or `1`). Allows `dst = a`. -/
def mwRawSub : Stmt :=
  .assign 5 (.const 0) ;;
  forRange 6 (.const 0) (.reg 3)
    (.assign 7 (.load (.bin .add (.reg 0) (.reg 6))) ;;
     .assign 8 (.bin .add (.load (.bin .add (.reg 1) (.reg 6))) (.reg 5)) ;;
     .cond (.bin .lt (.reg 7) (.reg 8))
       (.store (.bin .add (.reg 2) (.reg 6)) (.bin .sub (.bin .add (.reg 4) (.reg 7)) (.reg 8)) ;;
        .assign 5 (.const 1))
       (.store (.bin .add (.reg 2) (.reg 6)) (.bin .sub (.reg 7) (.reg 8)) ;;
        .assign 5 (.const 0))) ;;
  .ret (.reg 5)

/-- Truncating subtraction `a - b` (`reg 0` minus `reg 1`) into `dst` (`reg 2`), `L` (`reg 3`)
limbs of base `B` (`reg 4`), placed at module base `b`. -/
def mwSub (base : ℕ) : Stmt :=
  .call 5 (base + idxLt) [.reg 0, .reg 1, .reg 3] ;;
  .cond (.reg 5)
    (.call 5 (base + idxZero) [.reg 2, .reg 3])
    (.call 5 (base + idxRawSub) [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4]) ;;
  .ret (.const 0)

/-- In-place `dst := (2 * dst + bit) % 2 ^ (L * h)` (`dst` in `reg 0`, `bit` in `reg 1`, `L` in
`reg 2`, `B = 2 ^ h` in `reg 3`), returning the carry bit (`0` or `1`). -/
def mwShl1AddBit : Stmt :=
  .assign 4 (.reg 1) ;;
  forRange 5 (.const 0) (.reg 2)
    (.assign 6 (.load (.bin .add (.reg 0) (.reg 5))) ;;
     .assign 7 (.bin .add (.bin .add (.reg 6) (.reg 6)) (.reg 4)) ;;
     .cond (.bin .lt (.reg 7) (.reg 3))
       (.store (.bin .add (.reg 0) (.reg 5)) (.reg 7) ;; .assign 4 (.const 0))
       (.store (.bin .add (.reg 0) (.reg 5)) (.bin .sub (.reg 7) (.reg 3)) ;;
        .assign 4 (.const 1))) ;;
  .ret (.reg 4)

/-- Module of all 13 basic multiword procedures placed at base index `b`. -/
def arithBasicModule (b : ℕ) : List Stmt :=
  [mwZero, mwCopy, mwIsZero, mwFromHost, mwEq, mwLt,
   mwBitOp .and, mwBitOp .or, mwBitOp .xor,
   mwAdd, mwRawSub, mwSub b, mwShl1AddBit]

theorem arithBasicModule_length (b : ℕ) : (arithBasicModule b).length = 13 := rfl

theorem arithBasicModule_noRand (b : ℕ) : ∀ s ∈ arithBasicModule b, s.NoRand := by
  intro s hs
  simp only [arithBasicModule, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [mwZero, mwCopy, mwIsZero, mwFromHost, mwEq, mwLt, mwBitOp, mwAdd, mwRawSub, mwSub,
      mwShl1AddBit, forRange, forUp, Stmt.NoRand]

/-! ### Contracts -/

def mwAddContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ a b dst L h x y, args = [a, b, dst, L, 2 ^ h] ∧
      1 ≤ h ∧ 2 * h + 2 ≤ w ∧ a + L < 2 ^ w ∧ b + L < 2 ^ w ∧ dst + L < 2 ^ w ∧
      (dst + L ≤ a ∨ a + L ≤ dst) ∧ (dst + L ≤ b ∨ b + L ≤ dst) ∧
      LimbsAt mem a L h x ∧ LimbsAt mem b L h y
  post args mem v mem' :=
    ∃ a b dst L h, args = [a, b, dst, L, 2 ^ h] ∧ v ≤ 1 ∧
      (∀ x y, LimbsAt mem a L h x → LimbsAt mem b L h y →
        v = (x + y) / 2 ^ (L * h) ∧ LimbsAt mem' dst L h ((x + y) % 2 ^ (L * h))) ∧
      (∀ p, p < dst ∨ dst + L ≤ p → mem' p = mem p)
  cost args _ := match args with | [_, _, _, L, _] => 36 * L + 15 | _ => 0

def mwRawSubContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ a b dst L h x y, args = [a, b, dst, L, 2 ^ h] ∧
      1 ≤ h ∧ 2 * h + 2 ≤ w ∧ a + L < 2 ^ w ∧ b + L < 2 ^ w ∧ dst + L < 2 ^ w ∧
      (dst + L ≤ a ∨ a + L ≤ dst ∨ dst = a) ∧ (dst + L ≤ b ∨ b + L ≤ dst) ∧
      LimbsAt mem a L h x ∧ LimbsAt mem b L h y
  post args mem v mem' :=
    ∃ a b dst L h, args = [a, b, dst, L, 2 ^ h] ∧ v ≤ 1 ∧
      (∀ x y, LimbsAt mem a L h x → LimbsAt mem b L h y →
        ∃ z, LimbsAt mem' dst L h z ∧ z + y = x + v * 2 ^ (L * h)) ∧
      (∀ p, p < dst ∨ dst + L ≤ p → mem' p = mem p)
  cost args _ := match args with | [_, _, _, L, _] => 40 * L + 15 | _ => 0

def mwSubContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ a b dst L h x y, args = [a, b, dst, L, 2 ^ h] ∧
      1 ≤ h ∧ 2 * h + 2 ≤ w ∧ a + L < 2 ^ w ∧ b + L < 2 ^ w ∧ dst + L < 2 ^ w ∧
      (dst + L ≤ a ∨ a + L ≤ dst) ∧ (dst + L ≤ b ∨ b + L ≤ dst) ∧
      LimbsAt mem a L h x ∧ LimbsAt mem b L h y
  post args mem v mem' :=
    ∃ a b dst L h, args = [a, b, dst, L, 2 ^ h] ∧ v = 0 ∧
      (∀ x y, LimbsAt mem a L h x → LimbsAt mem b L h y → LimbsAt mem' dst L h (x - y)) ∧
      (∀ p, p < dst ∨ dst + L ≤ p → mem' p = mem p)
  cost args _ := match args with | [_, _, _, L, _] => 78 * L + 48 | _ => 0

def mwShl1AddBitContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ dst bit L h x, args = [dst, bit, L, 2 ^ h] ∧
      bit ≤ 1 ∧ 1 ≤ h ∧ 2 * h + 2 ≤ w ∧ dst + L < 2 ^ w ∧
      LimbsAt mem dst L h x
  post args mem v mem' :=
    ∃ dst bit L h, args = [dst, bit, L, 2 ^ h] ∧ v ≤ 1 ∧
      (∀ x, LimbsAt mem dst L h x →
        v = (2 * x + bit) / 2 ^ (L * h) ∧ LimbsAt mem' dst L h ((2 * x + bit) % 2 ^ (L * h))) ∧
      (∀ p, p < dst ∨ dst + L ≤ p → mem' p = mem p)
  cost args _ := match args with | [_, _, L, _] => 38 * L + 15 | _ => 0

/-! ### Step helpers -/

private theorem add_step_carry_div {x y h i : ℕ} :
    let cx := x % 2 ^ (i * h)
    let cy := y % 2 ^ (i * h)
    let ax := (x / 2 ^ (i * h)) % 2 ^ h
    let ay := (y / 2 ^ (i * h)) % 2 ^ h
    let c := (cx + cy) / 2 ^ (i * h)
    let s := ax + ay + c
    x % 2 ^ ((i + 1) * h) + y % 2 ^ ((i + 1) * h) =
      (cx + cy) % 2 ^ (i * h) + 2 ^ (i * h) * s ∧
    (x % 2 ^ ((i + 1) * h) + y % 2 ^ ((i + 1) * h)) % 2 ^ ((i + 1) * h) =
      (cx + cy) % 2 ^ (i * h) + 2 ^ (i * h) * (s % 2 ^ h) ∧
    (x % 2 ^ ((i + 1) * h) + y % 2 ^ ((i + 1) * h)) / 2 ^ ((i + 1) * h) = s / 2 ^ h := by
  intro cx cy ax ay c s
  have hsplit : cx + cy = (cx + cy) % 2 ^ (i * h) + 2 ^ (i * h) * c :=
    (Nat.mod_add_div (cx + cy) (2 ^ (i * h))).symm
  have hpow : 2 ^ ((i + 1) * h) = 2 ^ (i * h) * 2 ^ h := by
    rw [← Nat.pow_add, show i * h + h = (i + 1) * h by ring]
  have hsum : x % 2 ^ ((i + 1) * h) + y % 2 ^ ((i + 1) * h) =
      (cx + cy) % 2 ^ (i * h) + 2 ^ (i * h) * s := by
    rw [limb_step_prefix x h i, limb_step_prefix y h i]
    calc cx + 2 ^ (i * h) * ax + (cy + 2 ^ (i * h) * ay)
        = (cx + cy) + 2 ^ (i * h) * (ax + ay) := by ring
      _ = ((cx + cy) % 2 ^ (i * h) + 2 ^ (i * h) * c) + 2 ^ (i * h) * (ax + ay) := by
            rw [← hsplit]
      _ = (cx + cy) % 2 ^ (i * h) + 2 ^ (i * h) * (ax + ay + c) := by ring
  have hrem_lt : (cx + cy) % 2 ^ (i * h) < 2 ^ (i * h) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hs_split : s = s % 2 ^ h + 2 ^ h * (s / 2 ^ h) := (Nat.mod_add_div s (2 ^ h)).symm
  have hdecomp : (cx + cy) % 2 ^ (i * h) + 2 ^ (i * h) * s =
      ((cx + cy) % 2 ^ (i * h) + 2 ^ (i * h) * (s % 2 ^ h)) +
      2 ^ ((i + 1) * h) * (s / 2 ^ h) := by
    conv_lhs => rw [hs_split]
    rw [hpow]
    ring
  have hlow_lt : (cx + cy) % 2 ^ (i * h) + 2 ^ (i * h) * (s % 2 ^ h) < 2 ^ ((i + 1) * h) := by
    have hm : s % 2 ^ h < 2 ^ h := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hmul : 2 ^ (i * h) * (s % 2 ^ h + 1) ≤ 2 ^ (i * h) * 2 ^ h :=
      Nat.mul_le_mul_left _ hm
    rw [← hpow] at hmul
    have : 2 ^ (i * h) * (s % 2 ^ h + 1) = 2 ^ (i * h) * (s % 2 ^ h) + 2 ^ (i * h) := by ring
    omega
  refine ⟨hsum, ?_, ?_⟩
  · rw [hsum, hdecomp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlow_lt]
  · rw [hsum, hdecomp, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlow_lt,
      Nat.zero_add]

private theorem shl1_step_carry_div {x bit h i : ℕ} :
    let prev := 2 * (x % 2 ^ (i * h)) + bit
    let c := prev / 2 ^ (i * h)
    let xi := (x / 2 ^ (i * h)) % 2 ^ h
    let s := xi + xi + c
    2 * (x % 2 ^ ((i + 1) * h)) + bit = prev % 2 ^ (i * h) + 2 ^ (i * h) * s ∧
    (2 * (x % 2 ^ ((i + 1) * h)) + bit) % 2 ^ ((i + 1) * h) =
      prev % 2 ^ (i * h) + 2 ^ (i * h) * (s % 2 ^ h) ∧
    (2 * (x % 2 ^ ((i + 1) * h)) + bit) / 2 ^ ((i + 1) * h) = s / 2 ^ h := by
  intro prev c xi s
  have hsplit : prev = prev % 2 ^ (i * h) + 2 ^ (i * h) * c :=
    (Nat.mod_add_div prev (2 ^ (i * h))).symm
  have hpow : 2 ^ ((i + 1) * h) = 2 ^ (i * h) * 2 ^ h := by
    rw [← Nat.pow_add, show i * h + h = (i + 1) * h by ring]
  have hsum : 2 * (x % 2 ^ ((i + 1) * h)) + bit = prev % 2 ^ (i * h) + 2 ^ (i * h) * s := by
    rw [limb_step_prefix x h i]
    calc 2 * (x % 2 ^ (i * h) + 2 ^ (i * h) * xi) + bit
        = prev + 2 ^ (i * h) * (xi + xi) := by ring
      _ = (prev % 2 ^ (i * h) + 2 ^ (i * h) * c) + 2 ^ (i * h) * (xi + xi) := by
            rw [← hsplit]
      _ = prev % 2 ^ (i * h) + 2 ^ (i * h) * s := by ring
  have hrem_lt : prev % 2 ^ (i * h) < 2 ^ (i * h) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hs_split : s = s % 2 ^ h + 2 ^ h * (s / 2 ^ h) := (Nat.mod_add_div s (2 ^ h)).symm
  have hdecomp : prev % 2 ^ (i * h) + 2 ^ (i * h) * s =
      (prev % 2 ^ (i * h) + 2 ^ (i * h) * (s % 2 ^ h)) + 2 ^ ((i + 1) * h) * (s / 2 ^ h) := by
    conv_lhs => rw [hs_split]
    rw [hpow]
    ring
  have hlow_lt : prev % 2 ^ (i * h) + 2 ^ (i * h) * (s % 2 ^ h) < 2 ^ ((i + 1) * h) := by
    have hm : s % 2 ^ h < 2 ^ h := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hmul : 2 ^ (i * h) * (s % 2 ^ h + 1) ≤ 2 ^ (i * h) * 2 ^ h :=
      Nat.mul_le_mul_left _ hm
    rw [← hpow] at hmul
    have : 2 ^ (i * h) * (s % 2 ^ h + 1) = 2 ^ (i * h) * (s % 2 ^ h) + 2 ^ (i * h) := by ring
    omega
  refine ⟨hsum, ?_, ?_⟩
  · rw [hsum, hdecomp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlow_lt]
  · rw [hsum, hdecomp, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlow_lt,
      Nat.zero_add]

/-! ### Contract proofs -/

theorem mwAdd_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b [mwAdd]) :
    MeetsContract w p b (mwAddContract w) := by
  refine meetsContract_of_runs hp.head fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨a, b', dst, L, h, x, y, rfl, hh, hw2, ha, hb, hdst, hnova, hnovb, hx, hy⟩
  have hw1 : 1 < 2 ^ w := one_lt_two_pow_of_le hh hw2
  have hB : 2 ^ h < 2 ^ w := two_pow_h_lt_two_pow_w hw2
  have h2B : 2 * 2 ^ h < 2 ^ w := two_mul_pow_h_lt_two_pow_w hw2
  have hL : L < 2 ^ w := hwords L (by simp)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 6) (lo := .const 0) (hi := .reg 3)
    (body :=
      .assign 7 (.bin .add (.bin .add (.load (.bin .add (.reg 0) (.reg 6)))
          (.load (.bin .add (.reg 1) (.reg 6)))) (.reg 5)) ;;
      .cond (.bin .lt (.reg 7) (.reg 4))
        (.store (.bin .add (.reg 2) (.reg 6)) (.reg 7) ;; .assign 5 (.const 0))
        (.store (.bin .add (.reg 2) (.reg 6)) (.bin .sub (.reg 7) (.reg 4)) ;;
         .assign 5 (.const 1)))
    (P := fun st => st = { startState [a, b', dst, L, 2 ^ h] mem pos with
      regs := Function.update (startState [a, b', dst, L, 2 ^ h] mem pos).regs 5 0 })
    (Inv := fun i st => st.regs 0 = a ∧ st.regs 1 = b' ∧ st.regs 2 = dst ∧ st.regs 3 = L ∧
      st.regs 4 = 2 ^ h ∧ st.regs 6 = i ∧
      st.regs 5 = (x % 2 ^ (i * h) + y % 2 ^ (i * h)) / 2 ^ (i * h) ∧ st.regs 5 ≤ 1 ∧
      (∀ j < i, st.mem (dst + j) = (((x % 2 ^ (i * h) + y % 2 ^ (i * h)) % 2 ^ (i * h)) / 2 ^ (j * h)) % 2 ^ h) ∧
      (∀ p, p < dst ∨ dst + i ≤ p → st.mem p = mem p))
    27 0 L (Nat.zero_le L) hw1 (fun _ => hL)
    (fun st hst => by
      subst hst
      refine ⟨by eval_expr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        fun _ hj => absurd hj (Nat.not_lt_zero _), fun _ _ => rfl⟩ <;>
        simp [startState, Nat.mod_one])
    (fun _ st _ _ hi => hi.2.2.2.2.2.1)
    (fun _ st _ _ hi => by have h3 : st.regs 3 = L := hi.2.2.2.1; eval_expr)
    (fun i _ hilt => by
      intro st _ ⟨h0, h1, h2, h3, h4, h6, h5, h5_le, hlim, hframe⟩
      dsimp only
      have ha_val : st.mem (a + i) = (x / 2 ^ (i * h)) % 2 ^ h := by
        rw [hframe (a + i) (by omega)]; exact hx.getElem hilt
      have hb_val : st.mem (b' + i) = (y / 2 ^ (i * h)) % 2 ^ h := by
        rw [hframe (b' + i) (by omega)]; exact hy.getElem hilt
      have ha_lt : (x / 2 ^ (i * h)) % 2 ^ h < 2 ^ h := Nat.mod_lt _ (Nat.two_pow_pos _)
      have hb_lt : (y / 2 ^ (i * h)) % 2 ^ h < 2 ^ h := Nat.mod_lt _ (Nat.two_pow_pos _)
      set s := (x / 2 ^ (i * h)) % 2 ^ h + (y / 2 ^ (i * h)) % 2 ^ h +
        (x % 2 ^ (i * h) + y % 2 ^ (i * h)) / 2 ^ (i * h)
      have h5' : st.regs 5 = (x % 2 ^ (i * h) + y % 2 ^ (i * h)) / 2 ^ (i * h) := h5
      have hs_lt : s < 2 ^ w := by omega
      have hsum_eval : (Expr.bin .add (.bin .add (.load (.bin .add (.reg 0) (.reg 6)))
          (.load (.bin .add (.reg 1) (.reg 6)))) (.reg 5)).eval w st = some s := by
        refine Expr.eval_add (Expr.eval_add (Expr.eval_load_of_eq (by eval_expr) ha_val)
          (Expr.eval_load_of_eq (by eval_expr) hb_val) (by omega)) (by eval_expr) hs_lt
      have hstep := add_step_carry_div (x := x) (y := y) (h := h) (i := i)
      dsimp only at hstep
      rcases hstep with ⟨_, hmod_step, hdiv_step⟩
      have hlim_next : ∀ j < i + 1, j < i →
          (((x % 2 ^ ((i + 1) * h) + y % 2 ^ ((i + 1) * h)) % 2 ^ ((i + 1) * h)) / 2 ^ (j * h)) % 2 ^ h =
          (((x % 2 ^ (i * h) + y % 2 ^ (i * h)) % 2 ^ (i * h)) / 2 ^ (j * h)) % 2 ^ h := by
        intro j hj hji
        have hl1 := toLimbs_mod ((x % 2 ^ (i * h) + y % 2 ^ (i * h)) % 2 ^ (i * h) + 2 ^ (i * h) * (s % 2 ^ h)) i h
        have hadd_mod : ((x % 2 ^ (i * h) + y % 2 ^ (i * h)) % 2 ^ (i * h) + 2 ^ (i * h) * (s % 2 ^ h)) % 2 ^ (i * h) =
            (x % 2 ^ (i * h) + y % 2 ^ (i * h)) % 2 ^ (i * h) := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_mod]
        rw [hadd_mod] at hl1
        have h2 := congrArg (fun l => l[j]?) hl1
        simp only [List.getElem?_eq_getElem, toLimbs_length, hji, toLimbs_getElem hji] at h2
        rw [hmod_step]
        exact Option.some.inj h2.symm
      have hlim_self : (((x % 2 ^ ((i + 1) * h) + y % 2 ^ ((i + 1) * h)) % 2 ^ ((i + 1) * h)) / 2 ^ (i * h)) % 2 ^ h =
          s % 2 ^ h := by
        rw [hmod_step, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
          Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _)), Nat.zero_add,
          Nat.mod_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _))]
      refine runs_start_le ?_
      refine runs_seq_assign_le hsum_eval ?_
      refine runs_cond_le (Expr.eval_lt_op (by eval_expr) (by eval_expr) hw1) (fun hne => ?_) (fun heq => ?_)
      · have hs_lt_B : s < 2 ^ h := by
          by_contra hnot; simp [hnot] at hne
        refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
        refine runs_assign_le (by eval_expr) ?_ (by wram_cost)
        have hc0 : s / 2 ^ h = 0 := Nat.div_eq_of_lt hs_lt_B
        have hs_mod : s % 2 ^ h = s := Nat.mod_eq_of_lt hs_lt_B
        refine ⟨⟨h0, h1, h2, h3, h4, ?_, ?_, by simp, ?_, ?_⟩, h6⟩
        · simp
        · dsimp only [s] at hdiv_step hc0
          simp [hdiv_step, hc0]
        · intro j hj
          dsimp only
          by_cases hji : j = i
          · subst hji; rw [Function.update_self]; dsimp only [s] at hlim_self hs_mod; rw [hlim_self, hs_mod]
          · rw [Function.update_of_ne (by omega)]
            rw [hlim_next j hj (by omega)]
            exact hlim j (by omega)
        · intro q hq
          dsimp only
          rw [Function.update_of_ne (by omega)]; exact hframe q (by omega)
      · have hB_le_s : 2 ^ h ≤ s := by
          by_contra hnot
          have hlt : s < 2 ^ h := Nat.not_le.mp hnot
          simp [hlt] at heq
        refine runs_seq_store_le (by eval_expr) (Expr.eval_sub (by eval_expr) (by eval_expr) hs_lt) ?_
        refine runs_assign_le (by eval_expr) ?_ (by wram_cost)
        have hc1 : s / 2 ^ h = 1 := by
          apply Nat.eq_of_le_of_lt_succ
          · exact Nat.div_pos hB_le_s (Nat.two_pow_pos _)
          · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]; omega
        have hs_mod : s % 2 ^ h = s - 2 ^ h := by
          have hdm := Nat.mod_add_div s (2 ^ h)
          rw [hc1] at hdm; omega
        refine ⟨⟨h0, h1, h2, h3, h4, ?_, ?_, by simp, ?_, ?_⟩, h6⟩
        · simp
        · dsimp only [s] at hdiv_step hc1
          simp [hdiv_step, hc1]
        · intro j hj
          dsimp only
          by_cases hji : j = i
          · subst hji; rw [Function.update_self]; dsimp only [s] at hlim_self hs_mod; rw [hlim_self, hs_mod]
          · rw [Function.update_of_ne (by omega)]
            rw [hlim_next j hj (by omega)]
            exact hlim j (by omega)
        · intro q hq
          dsimp only
          rw [Function.update_of_ne (by omega)]; exact hframe q (by omega))
  refine runs_start_le ?_
  dsimp only [mwAdd]
  wram_step
  · refine runs_seq_triple_le hloop rfl ?_
    intro st₁ ⟨_, _, _, _, _, _, h5, h5_le, hlim, hframe⟩
    have hmx : x % 2 ^ (L * h) = x := Nat.mod_eq_of_lt hx.lt_pow
    have hmy : y % 2 ^ (L * h) = y := Nat.mod_eq_of_lt hy.lt_pow
    rw [hmx, hmy] at h5 hlim
    have hlimbs : LimbsAt st₁.mem dst L h ((x + y) % 2 ^ (L * h)) :=
      limbsAt_iff_pointwise.mpr ⟨Nat.mod_lt _ (Nat.two_pow_pos _), hlim⟩
    refine runs_ret_le (by eval_expr)
      ⟨a, b', dst, L, h, rfl, h5_le, fun x' y' hx' hy' => by
        obtain rfl : x' = x := hx'.ext hx
        obtain rfl : y' = y := hy'.ext hy
        exact ⟨h5, hlimbs⟩, hframe⟩ ?_
    dsimp only [mwAddContract, Expr.size_const, Expr.size_reg, Nat.sub_zero]
    omega

theorem mwRawSub_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b [mwRawSub]) :
    MeetsContract w p b (mwRawSubContract w) := by
  refine meetsContract_of_runs hp.head fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨a, b', dst, L, h, x, y, rfl, hh, hw2, ha, hb, hdst, hnova, hnovb, hx, hy⟩
  have hw1 : 1 < 2 ^ w := one_lt_two_pow_of_le hh hw2
  have hB : 2 ^ h < 2 ^ w := two_pow_h_lt_two_pow_w hw2
  have h2B : 2 * 2 ^ h < 2 ^ w := two_mul_pow_h_lt_two_pow_w hw2
  have hL : L < 2 ^ w := hwords L (by simp)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 6) (lo := .const 0) (hi := .reg 3)
    (body :=
      .assign 7 (.load (.bin .add (.reg 0) (.reg 6))) ;;
      .assign 8 (.bin .add (.load (.bin .add (.reg 1) (.reg 6))) (.reg 5)) ;;
      .cond (.bin .lt (.reg 7) (.reg 8))
        (.store (.bin .add (.reg 2) (.reg 6)) (.bin .sub (.bin .add (.reg 4) (.reg 7)) (.reg 8)) ;;
         .assign 5 (.const 1))
        (.store (.bin .add (.reg 2) (.reg 6)) (.bin .sub (.reg 7) (.reg 8)) ;;
         .assign 5 (.const 0)))
    (P := fun st => st = { startState [a, b', dst, L, 2 ^ h] mem pos with
      regs := Function.update (startState [a, b', dst, L, 2 ^ h] mem pos).regs 5 0 })
    (Inv := fun i st => st.regs 0 = a ∧ st.regs 1 = b' ∧ st.regs 2 = dst ∧ st.regs 3 = L ∧
      st.regs 4 = 2 ^ h ∧ st.regs 6 = i ∧ st.regs 5 ≤ 1 ∧
      (∀ j < i, st.mem (dst + j) < 2 ^ h) ∧
      evalLimbs h (tab i (fun j => st.mem (dst + j))) + y % 2 ^ (i * h) =
        x % 2 ^ (i * h) + st.regs 5 * 2 ^ (i * h) ∧
      (∀ p, p < dst ∨ dst + i ≤ p → st.mem p = mem p))
    30 0 L (Nat.zero_le L) hw1 (fun _ => hL)
    (fun st hst => by
      subst hst
      refine ⟨by eval_expr, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        fun _ hj => absurd hj (Nat.not_lt_zero _),
        by simp [tab, evalLimbs, startState, Nat.mod_one], fun _ _ => rfl⟩ <;>
        simp [startState])
    (fun _ st _ _ hi => hi.2.2.2.2.2.1)
    (fun _ st _ _ hi => by have h3 : st.regs 3 = L := hi.2.2.2.1; eval_expr)
    (fun i _ hilt => by
      intro st _ ⟨h0, h1, h2, h3, h4, h6, h5_le, hlim_lt, heval, hframe⟩
      dsimp only
      have ha_val : st.mem (a + i) = (x / 2 ^ (i * h)) % 2 ^ h := by
        have hmem_eq : st.mem (a + i) = mem (a + i) := by
          rcases hnova with hnov | hnov | hEq
          · exact hframe (a + i) (by omega)
          · exact hframe (a + i) (by omega)
          · rw [← hEq]; exact hframe (dst + i) (by omega)
        rw [hmem_eq]; exact hx.getElem hilt
      have hb_val : st.mem (b' + i) = (y / 2 ^ (i * h)) % 2 ^ h := by
        rw [hframe (b' + i) (by omega)]; exact hy.getElem hilt
      set ai := (x / 2 ^ (i * h)) % 2 ^ h
      set bi := (y / 2 ^ (i * h)) % 2 ^ h
      have hai_lt : ai < 2 ^ h := Nat.mod_lt _ (Nat.two_pow_pos _)
      have hbi_lt : bi < 2 ^ h := Nat.mod_lt _ (Nat.two_pow_pos _)
      have hbi_sum_lt : bi + st.regs 5 < 2 ^ w := by omega
      have hpow_step : 2 ^ ((i + 1) * h) = 2 ^ (i * h) * 2 ^ h := by
        rw [← Nat.pow_add, show i * h + h = (i + 1) * h by ring]
      have htab_step : ∀ (d : ℕ) (f : ℕ → ℕ),
          (∀ j < i, f j = st.mem (dst + j)) → f i = d →
          evalLimbs h (tab (i + 1) f) = evalLimbs h (tab i (fun j => st.mem (dst + j))) + 2 ^ (i * h) * d := by
        intro d f hf_prev hf_i
        have htab_eq : tab (i + 1) f = tab i (fun j => st.mem (dst + j)) ++ [d] := by
          simp only [tab, List.range_succ, List.map_append, List.map_singleton, hf_i]
          congr 1
          exact List.map_congr_left fun j hj => hf_prev j (List.mem_range.mp hj)
        rw [htab_eq, evalLimbs_append]
        simp [tab, evalLimbs]
      refine runs_start_le ?_
      refine runs_seq_assign_le (Expr.eval_load_of_eq (by eval_expr) ha_val) ?_
      refine runs_seq_assign_le
        (Expr.eval_add (Expr.eval_load_of_eq (by eval_expr) hb_val) (by eval_expr) hbi_sum_lt) ?_
      refine runs_cond_le (Expr.eval_lt_op (by eval_expr) (by eval_expr) hw1) (fun hne => ?_) (fun heq => ?_)
      · have hlt : ai < bi + st.regs 5 := by
          by_contra hnot; simp [hnot] at hne
        refine runs_seq_store_le (by eval_expr)
          (Expr.eval_sub (Expr.eval_add (by eval_expr) (by eval_expr) (by omega))
            (by eval_expr) (by omega)) ?_
        refine runs_assign_le (by eval_expr) ?_ (by wram_cost)
        · have hd_lt : (2 ^ h + ai) - (bi + st.regs 5) < 2 ^ h := by omega
          refine ⟨⟨h0, h1, h2, h3, h4, ?_, by simp, ?_, ?_, ?_⟩, ?_⟩
          · simp
          · intro j hj
            dsimp only
            by_cases hji : j = i
            · subst hji; simpa using hd_lt
            · rw [Function.update_of_ne (by omega)]; exact hlim_lt j (by omega)
          · dsimp only
            rw [htab_step ((2 ^ h + ai) - (bi + st.regs 5)) _
              (fun j hj => Function.update_of_ne (by omega) _ _) (by simp)]
            rw [limb_step_prefix x h i, limb_step_prefix y h i, hpow_step]
            have hle_sub : bi + st.regs 5 ≤ 2 ^ h + ai := by omega
            have hmul_sub : 2 ^ (i * h) * ((2 ^ h + ai) - (bi + st.regs 5)) + 2 ^ (i * h) * bi =
                2 ^ (i * h) * (2 ^ h + ai) - 2 ^ (i * h) * st.regs 5 := by
              rw [Nat.mul_sub, Nat.mul_add (2 ^ (i * h)) bi (st.regs 5)]
              have h2 : 2 ^ (i * h) * bi + 2 ^ (i * h) * st.regs 5 ≤ 2 ^ (i * h) * (2 ^ h + ai) := by
                rw [← Nat.mul_add]
                exact Nat.mul_le_mul_left _ hle_sub
              omega
            have hmul_le : 2 ^ (i * h) * st.regs 5 ≤ 2 ^ (i * h) * (2 ^ h + ai) :=
              Nat.mul_le_mul_left _ (by omega)
            have hcomm : st.regs 5 * 2 ^ (i * h) = 2 ^ (i * h) * st.regs 5 := Nat.mul_comm _ _
            have hmul_add' : 2 ^ (i * h) * (2 ^ h + ai) = 2 ^ (i * h) * 2 ^ h + 2 ^ (i * h) * ai :=
              Nat.mul_add _ _ _
            calc evalLimbs h (tab i fun j => st.mem (dst + j)) +
                    2 ^ (i * h) * (2 ^ h + ai - (bi + st.regs 5)) +
                    (y % 2 ^ (i * h) + 2 ^ (i * h) * bi)
                = (evalLimbs h (tab i fun j => st.mem (dst + j)) + y % 2 ^ (i * h)) +
                    (2 ^ (i * h) * (2 ^ h + ai - (bi + st.regs 5)) + 2 ^ (i * h) * bi) := by ring
              _ = (x % 2 ^ (i * h) + 2 ^ (i * h) * st.regs 5) +
                    (2 ^ (i * h) * (2 ^ h + ai) - 2 ^ (i * h) * st.regs 5) := by
                    rw [heval, hcomm, hmul_sub]
              _ = x % 2 ^ (i * h) + 2 ^ (i * h) * ai + 1 * (2 ^ (i * h) * 2 ^ h) := by
                    rw [hmul_add'] at hmul_le ⊢; omega
          · intro q hq
            dsimp only
            rw [Function.update_of_ne (by omega)]; exact hframe q (by omega)
          · simp [h6]
      · have hle : bi + st.regs 5 ≤ ai := by
          by_contra hnot
          have : ai < bi + st.regs 5 := Nat.not_le.mp hnot
          simp [this] at heq
        refine runs_seq_store_le (by eval_expr)
          (Expr.eval_sub (by eval_expr) (by eval_expr) (by omega)) ?_
        refine runs_assign_le (by eval_expr) ?_ (by wram_cost)
        · have hd_lt : ai - (bi + st.regs 5) < 2 ^ h := by omega
          refine ⟨⟨h0, h1, h2, h3, h4, ?_, by simp, ?_, ?_, ?_⟩, ?_⟩
          · simp
          · intro j hj
            dsimp only
            by_cases hji : j = i
            · subst hji; simpa using hd_lt
            · rw [Function.update_of_ne (by omega)]; exact hlim_lt j (by omega)
          · dsimp only
            rw [htab_step (ai - (bi + st.regs 5)) _
              (fun j hj => Function.update_of_ne (by omega) _ _) (by simp)]
            rw [limb_step_prefix x h i, limb_step_prefix y h i]
            have hmul_sub : 2 ^ (i * h) * (ai - (bi + st.regs 5)) + 2 ^ (i * h) * bi =
                2 ^ (i * h) * ai - 2 ^ (i * h) * st.regs 5 := by
              rw [Nat.mul_sub, Nat.mul_add]
              have h2 : 2 ^ (i * h) * bi + 2 ^ (i * h) * st.regs 5 ≤ 2 ^ (i * h) * ai := by
                rw [← Nat.mul_add]
                exact Nat.mul_le_mul_left _ hle
              omega
            have hmul_le : 2 ^ (i * h) * st.regs 5 ≤ 2 ^ (i * h) * ai :=
              Nat.mul_le_mul_left _ (by omega)
            have hcomm : st.regs 5 * 2 ^ (i * h) = 2 ^ (i * h) * st.regs 5 := Nat.mul_comm _ _
            calc evalLimbs h (tab i fun j => st.mem (dst + j)) +
                    2 ^ (i * h) * (ai - (bi + st.regs 5)) +
                    (y % 2 ^ (i * h) + 2 ^ (i * h) * bi)
                = (evalLimbs h (tab i fun j => st.mem (dst + j)) + y % 2 ^ (i * h)) +
                    (2 ^ (i * h) * (ai - (bi + st.regs 5)) + 2 ^ (i * h) * bi) := by ring
              _ = (x % 2 ^ (i * h) + 2 ^ (i * h) * st.regs 5) +
                    (2 ^ (i * h) * ai - 2 ^ (i * h) * st.regs 5) := by
                    rw [heval, hcomm, hmul_sub]
              _ = x % 2 ^ (i * h) + 2 ^ (i * h) * ai + 0 * 2 ^ ((i + 1) * h) := by
                    omega
          · intro q hq
            dsimp only
            rw [Function.update_of_ne (by omega)]; exact hframe q (by omega)
          · simp [h6])
  refine runs_start_le ?_
  dsimp only [mwRawSub]
  wram_step
  · refine runs_seq_triple_le hloop rfl ?_
    intro st₁ ⟨_, _, _, _, _, _, h5_le, hlim_lt, heval, hframe⟩
    have hmx : x % 2 ^ (L * h) = x := Nat.mod_eq_of_lt hx.lt_pow
    have hmy : y % 2 ^ (L * h) = y := Nat.mod_eq_of_lt hy.lt_pow
    rw [hmx, hmy] at heval
    have hlimbs : LimbsAt st₁.mem dst L h (evalLimbs h (tab L (fun j => st₁.mem (dst + j)))) := by
      refine limbsAt_of_list ?_ (by simp [tab]) ?_
      · intro i hi
        simp only [tab, List.length_map, List.length_range] at hi
        simp [tab]
      · intro d hd
        simp only [tab, List.mem_map, List.mem_range] at hd
        rcases hd with ⟨j, hj, rfl⟩
        exact hlim_lt j hj
    refine runs_ret_le (by eval_expr)
      ⟨a, b', dst, L, h, rfl, h5_le, fun x' y' hx' hy' => by
        obtain rfl : x' = x := hx'.ext hx
        obtain rfl : y' = y := hy'.ext hy
        exact ⟨_, hlimbs, heval⟩, hframe⟩ ?_
    dsimp only [mwRawSubContract, Expr.size_const, Expr.size_reg, Nat.sub_zero]
    omega

theorem arithBasic_hasAt_single {p : Program} {b k : ℕ}
    (hp : p.HasAt b (arithBasicModule b)) (hk : k < (arithBasicModule b).length) :
    p.HasAt (b + k) [(arithBasicModule b)[k]'hk] := by
  intro i hi
  simp only [List.length_singleton, Nat.lt_one_iff] at hi
  subst hi
  simpa using hp k hk

theorem mwZero_of_module {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (arithBasicModule b)) :
    MeetsContract w p (b + idxZero) (mwZeroContract w) :=
  mwZero_meetsContract (arithBasic_hasAt_single hp (by simp [arithBasicModule, idxZero]))

theorem mwCopy_of_module {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (arithBasicModule b)) :
    MeetsContract w p (b + idxCopy) (mwCopyContract w) :=
  mwCopy_meetsContract (arithBasic_hasAt_single hp (by simp [arithBasicModule, idxCopy]))

theorem mwIsZero_of_module {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (arithBasicModule b)) :
    MeetsContract w p (b + idxIsZero) (mwIsZeroContract w) :=
  mwIsZero_meetsContract (arithBasic_hasAt_single hp (by simp [arithBasicModule, idxIsZero]))

theorem mwFromHost_of_module {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (arithBasicModule b)) :
    MeetsContract w p (b + idxFromHost) (mwFromHostContract w) :=
  mwFromHost_meetsContract (arithBasic_hasAt_single hp (by simp [arithBasicModule, idxFromHost]))

theorem mwEq_of_module {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (arithBasicModule b)) :
    MeetsContract w p (b + idxEq) (mwEqContract w) :=
  mwEq_meetsContract (arithBasic_hasAt_single hp (by simp [arithBasicModule, idxEq]))

theorem mwLt_of_module {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (arithBasicModule b)) :
    MeetsContract w p (b + idxLt) (mwLtContract w) :=
  mwLt_meetsContract (arithBasic_hasAt_single hp (by simp [arithBasicModule, idxLt]))

theorem mwAnd_of_module {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (arithBasicModule b)) :
    MeetsContract w p (b + idxAnd) (mwBitOpContract w .and) :=
  mwBitOp_meetsContract (Or.inl rfl)
    (arithBasic_hasAt_single hp (by simp [arithBasicModule, idxAnd]))

theorem mwOr_of_module {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (arithBasicModule b)) :
    MeetsContract w p (b + idxOr) (mwBitOpContract w .or) :=
  mwBitOp_meetsContract (Or.inr (Or.inl rfl))
    (arithBasic_hasAt_single hp (by simp [arithBasicModule, idxOr]))

theorem mwXor_of_module {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (arithBasicModule b)) :
    MeetsContract w p (b + idxXor) (mwBitOpContract w .xor) :=
  mwBitOp_meetsContract (Or.inr (Or.inr rfl))
    (arithBasic_hasAt_single hp (by simp [arithBasicModule, idxXor]))

theorem mwAdd_of_module {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (arithBasicModule b)) :
    MeetsContract w p (b + idxAdd) (mwAddContract w) :=
  mwAdd_meetsContract (arithBasic_hasAt_single hp (by simp [arithBasicModule, idxAdd]))

theorem mwRawSub_of_module {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (arithBasicModule b)) :
    MeetsContract w p (b + idxRawSub) (mwRawSubContract w) :=
  mwRawSub_meetsContract (arithBasic_hasAt_single hp (by simp [arithBasicModule, idxRawSub]))

theorem mwSub_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b (arithBasicModule b)) :
    MeetsContract w p (b + idxSub) (mwSubContract w) := by
  have hZero := mwZero_of_module (w := w) hp
  have hLt := mwLt_of_module (w := w) hp
  have hRaw := mwRawSub_of_module (w := w) hp
  have hSubProc : p.procs[b + idxSub]? = some (mwSub b) := by
    have := hp idxSub (by simp [arithBasicModule, idxSub])
    simpa [arithBasicModule, idxSub] using this
  refine meetsContract_of_runs hSubProc fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨a, b', dst, L, h, x, y, rfl, hh, hw2, ha, hb, hdst, hnova, hnovb, hx, hy⟩
  have hw1 : 1 < 2 ^ w := one_lt_two_pow_of_le hh hw2
  have ha_w : a < 2 ^ w := hwords a (by simp)
  have hb_w : b' < 2 ^ w := hwords b' (by simp)
  have hdst_w : dst < 2 ^ w := hwords dst (by simp)
  have hL_w : L < 2 ^ w := hwords L (by simp)
  have hB_w : 2 ^ h < 2 ^ w := two_pow_h_lt_two_pow_w hw2
  refine runs_start_le ?_
  dsimp only [mwSub]
  refine runs_seq_call_le hLt (by eval_expr) (by wram_words)
    ⟨a, b', L, h, x, y, rfl, hh, hw2, ha, hb, hx, hy⟩ ?_
  rintro v₁ mem₁ pos₁ ⟨a', b'', L', heq1, hmem1, hlt_spec⟩
  simp only [List.cons.injEq, and_true] at heq1
  rcases heq1 with ⟨rfl, rfl, rfl⟩
  have hv1 : v₁ = if x < y then 1 else 0 := hlt_spec h x y hx hy
  have hx1 : LimbsAt mem₁ a L h x := hmem1 ▸ hx
  have hy1 : LimbsAt mem₁ b' L h y := hmem1 ▸ hy
  wram_step
  · refine runs_seq_call_le hZero (by eval_expr) (by wram_words) ⟨dst, L, rfl, hw1, hdst⟩ ?_
    rintro v₂ mem₂ pos₂ ⟨dst', L', heq2, _, hlist, hframe⟩
    simp only [List.cons.injEq, and_true] at heq2
    rcases heq2 with ⟨rfl, rfl⟩
    have hlt : x < y := by by_contra hnot; simp [hv1, hnot] at hcond
    have hlimbs : LimbsAt mem₂ dst L h (x - y) := by
      rw [Nat.sub_eq_zero_of_le (le_of_lt hlt)]
      exact limbsAt_zero_iff.mpr hlist
    have hframe' : ∀ p, p < dst ∨ dst + L ≤ p → mem₂ p = mem p := by
      intro p hp'; rw [hframe p hp', hmem1]; rfl
    refine runs_ret_le (by eval_expr)
      ⟨a, b', dst, L, h, rfl, rfl, fun x' y' hx' hy' => by
        obtain rfl : x' = x := hx'.ext hx
        obtain rfl : y' = y := hy'.ext hy
        exact hlimbs, hframe'⟩ ?_
    dsimp only [mwSubContract, mwLtContract, mwZeroContract]
    wram_cost
  · refine runs_seq_call_le hRaw (by eval_expr) (by wram_words)
      ⟨a, b', dst, L, h, x, y, rfl, hh, hw2, ha, hb, hdst,
        Or.elim hnova Or.inl (fun h' => Or.inr (Or.inl h')), hnovb, hx1, hy1⟩ ?_
    rintro v₂ mem₂ pos₂ ⟨a', b'', dst', L', h', heq2, hv2_le, hsub_spec, hframe⟩
    simp only [List.cons.injEq, and_true] at heq2
    rcases heq2 with ⟨rfl, rfl, rfl, rfl, hBh⟩
    have hh' : h' = h := Nat.pow_right_injective (by norm_num : 2 ≤ 2) hBh.symm
    rw [hh'] at hsub_spec
    rcases hsub_spec x y hx1 hy1 with ⟨z', hlimbs, heq_z⟩
    have hle : y ≤ x := by
      by_contra hnot
      have : x < y := Nat.not_le.mp hnot
      simp [hv1, this] at hcond
    have hz_eq : z' = x - y := by
      have hz_lt : z' < 2 ^ (L * h) := hlimbs.lt_pow
      by_cases hv0 : v₂ = 0
      · subst hv0; omega
      · have : v₂ = 1 := by omega
        subst this; omega
    rw [hz_eq] at hlimbs
    have hframe' : ∀ p, p < dst ∨ dst + L ≤ p → mem₂ p = mem p := by
      intro p hp'; rw [hframe p hp', hmem1]; rfl
    refine runs_ret_le (by eval_expr)
      ⟨a, b', dst, L, h, rfl, rfl, fun x' y' hx' hy' => by
        obtain rfl : x' = x := hx'.ext hx
        obtain rfl : y' = y := hy'.ext hy
        exact hlimbs, hframe'⟩ ?_
    dsimp only [mwSubContract, mwLtContract, mwRawSubContract]
    wram_cost

theorem mwShl1AddBit_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b [mwShl1AddBit]) :
    MeetsContract w p b (mwShl1AddBitContract w) := by
  refine meetsContract_of_runs hp.head fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨dst, bit, L, h, x, rfl, hbit, hh, hw2, hdst, hx⟩
  have hw1 : 1 < 2 ^ w := one_lt_two_pow_of_le hh hw2
  have hB : 2 ^ h < 2 ^ w := two_pow_h_lt_two_pow_w hw2
  have h2B : 2 * 2 ^ h < 2 ^ w := two_mul_pow_h_lt_two_pow_w hw2
  have hL : L < 2 ^ w := hwords L (by simp)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 5) (lo := .const 0) (hi := .reg 2)
    (body :=
      .assign 6 (.load (.bin .add (.reg 0) (.reg 5))) ;;
      .assign 7 (.bin .add (.bin .add (.reg 6) (.reg 6)) (.reg 4)) ;;
      .cond (.bin .lt (.reg 7) (.reg 3))
        (.store (.bin .add (.reg 0) (.reg 5)) (.reg 7) ;; .assign 4 (.const 0))
        (.store (.bin .add (.reg 0) (.reg 5)) (.bin .sub (.reg 7) (.reg 3)) ;;
         .assign 4 (.const 1)))
    (P := fun st => st = { startState [dst, bit, L, 2 ^ h] mem pos with
      regs := Function.update (startState [dst, bit, L, 2 ^ h] mem pos).regs 4 bit })
    (Inv := fun i st => st.regs 0 = dst ∧ st.regs 2 = L ∧ st.regs 3 = 2 ^ h ∧
      st.regs 5 = i ∧
      st.regs 4 = (2 * (x % 2 ^ (i * h)) + bit) / 2 ^ (i * h) ∧ st.regs 4 ≤ 1 ∧
      (∀ j < i, st.mem (dst + j) = (((2 * (x % 2 ^ (i * h)) + bit) % 2 ^ (i * h)) / 2 ^ (j * h)) % 2 ^ h) ∧
      (∀ p, p < dst ∨ dst + i ≤ p → st.mem p = mem p))
    27 0 L (Nat.zero_le L) hw1 (fun _ => hL)
    (fun st hst => by
      subst hst
      refine ⟨by eval_expr, ?_, ?_, ?_, ?_, ?_, ?_,
        fun _ hj => absurd hj (Nat.not_lt_zero _), fun _ _ => rfl⟩ <;>
        simp [startState, hbit, Nat.mod_one])
    (fun _ st _ _ hi => hi.2.2.2.1)
    (fun _ st _ _ hi => by have h2 : st.regs 2 = L := hi.2.1; eval_expr)
    (fun i _ hilt => by
      intro st _ ⟨h0, h2, h3, h5, h4, h4_le, hlim, hframe⟩
      dsimp only
      have ha_val : st.mem (dst + i) = (x / 2 ^ (i * h)) % 2 ^ h := by
        rw [hframe (dst + i) (by omega)]; exact hx.getElem hilt
      have ha_lt : (x / 2 ^ (i * h)) % 2 ^ h < 2 ^ h := Nat.mod_lt _ (Nat.two_pow_pos _)
      set s := (x / 2 ^ (i * h)) % 2 ^ h + (x / 2 ^ (i * h)) % 2 ^ h +
        (2 * (x % 2 ^ (i * h)) + bit) / 2 ^ (i * h)
      have hstep := shl1_step_carry_div (x := x) (bit := bit) (h := h) (i := i)
      dsimp only at hstep
      rcases hstep with ⟨_, hmod_step, hdiv_step⟩
      have hlim_next : ∀ j < i + 1, j < i →
          (((2 * (x % 2 ^ ((i + 1) * h)) + bit) % 2 ^ ((i + 1) * h)) / 2 ^ (j * h)) % 2 ^ h =
          (((2 * (x % 2 ^ (i * h)) + bit) % 2 ^ (i * h)) / 2 ^ (j * h)) % 2 ^ h := by
        intro j hj hji
        have hl1 := toLimbs_mod ((2 * (x % 2 ^ (i * h)) + bit) % 2 ^ (i * h) + 2 ^ (i * h) * (s % 2 ^ h)) i h
        have hadd_mod : ((2 * (x % 2 ^ (i * h)) + bit) % 2 ^ (i * h) + 2 ^ (i * h) * (s % 2 ^ h)) % 2 ^ (i * h) =
            (2 * (x % 2 ^ (i * h)) + bit) % 2 ^ (i * h) := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_mod]
        rw [hadd_mod] at hl1
        have h2 := congrArg (fun l => l[j]?) hl1
        simp only [List.getElem?_eq_getElem, toLimbs_length, hji, toLimbs_getElem hji] at h2
        rw [hmod_step]
        exact Option.some.inj h2.symm
      have hlim_self :
          (((2 * (x % 2 ^ ((i + 1) * h)) + bit) % 2 ^ ((i + 1) * h)) / 2 ^ (i * h)) % 2 ^ h =
          s % 2 ^ h := by
        rw [hmod_step, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
          Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _)), Nat.zero_add,
          Nat.mod_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _))]
      refine runs_start_le ?_
      refine runs_seq_assign_le (Expr.eval_load_of_eq (by eval_expr) ha_val) ?_
      refine runs_seq_assign_le
        (Expr.eval_add (Expr.eval_add (by eval_expr) (by eval_expr) (by omega))
          (by eval_expr) (by omega)) ?_
      refine runs_cond_le (Expr.eval_lt_op (by eval_expr) (by eval_expr) hw1) (fun hne => ?_) (fun heq => ?_)
      · have hs_lt_B : s < 2 ^ h := by
          simpa [s] using hne
        refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
        refine runs_assign_le (by eval_expr) ?_ (by wram_cost)
        have hc0 : s / 2 ^ h = 0 := Nat.div_eq_of_lt hs_lt_B
        have hs_mod : s % 2 ^ h = s := Nat.mod_eq_of_lt hs_lt_B
        refine ⟨⟨h0, h2, h3, ?_, ?_, by simp, ?_, ?_⟩, ?_⟩
        · simp
        · dsimp only [s] at hdiv_step hc0
          simp [hdiv_step, hc0]
        · intro j hj
          dsimp only
          by_cases hji : j = i
          · subst hji; rw [Function.update_self]; dsimp only [s] at hlim_self hs_mod; rw [hlim_self, hs_mod]
          · rw [Function.update_of_ne (by omega)]
            rw [hlim_next j hj (by omega)]
            exact hlim j (by omega)
        · intro q hq
          dsimp only
          rw [Function.update_of_ne (by omega)]; exact hframe q (by omega)
        · simp [h5]
      · have hB_le_s : 2 ^ h ≤ s := by
          simpa [s] using heq
        refine runs_seq_store_le (by eval_expr) (Expr.eval_sub (by eval_expr) (by eval_expr) (by omega)) ?_
        refine runs_assign_le (by eval_expr) ?_ (by wram_cost)
        have hc1 : s / 2 ^ h = 1 := by
          apply Nat.eq_of_le_of_lt_succ
          · exact Nat.div_pos hB_le_s (Nat.two_pow_pos _)
          · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]; omega
        have hs_mod : s % 2 ^ h = s - 2 ^ h := by
          have hdm := Nat.mod_add_div s (2 ^ h)
          rw [hc1] at hdm; omega
        refine ⟨⟨h0, h2, h3, ?_, ?_, by simp, ?_, ?_⟩, ?_⟩
        · simp
        · dsimp only [s] at hdiv_step hc1
          simp [hdiv_step, hc1]
        · intro j hj
          dsimp only
          by_cases hji : j = i
          · subst hji; rw [Function.update_self]; dsimp only [s] at hlim_self hs_mod; rw [hlim_self, hs_mod]
          · rw [Function.update_of_ne (by omega)]
            rw [hlim_next j hj (by omega)]
            exact hlim j (by omega)
        · intro q hq
          dsimp only
          rw [Function.update_of_ne (by omega)]; exact hframe q (by omega)
        · simp [h5])
  refine runs_start_le ?_
  dsimp only [mwShl1AddBit]
  wram_step
  · refine runs_seq_triple_le hloop rfl ?_
    intro st₁ ⟨_, _, _, _, h4, h4_le, hlim, hframe⟩
    have hmx : x % 2 ^ (L * h) = x := Nat.mod_eq_of_lt hx.lt_pow
    rw [hmx] at h4 hlim
    have hlimbs : LimbsAt st₁.mem dst L h ((2 * x + bit) % 2 ^ (L * h)) :=
      limbsAt_iff_pointwise.mpr ⟨Nat.mod_lt _ (Nat.two_pow_pos _), hlim⟩
    refine runs_ret_le (by eval_expr)
      ⟨dst, bit, L, h, rfl, h4_le, fun x' hx' => by
        obtain rfl : x' = x := hx'.ext hx
        exact ⟨h4, hlimbs⟩, hframe⟩ ?_
    dsimp only [mwShl1AddBitContract, Expr.size_const, Expr.size_reg, Nat.sub_zero]
    omega

/-! ### Remaining module wrapper -/

theorem mwSub_of_module {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (arithBasicModule b)) :
    MeetsContract w p (b + idxSub) (mwSubContract w) :=
  mwSub_meetsContract hp

theorem mwShl1AddBit_of_module {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b (arithBasicModule b)) :
    MeetsContract w p (b + idxShl1AddBit) (mwShl1AddBitContract w) :=
  mwShl1AddBit_meetsContract (arithBasic_hasAt_single hp (by simp [arithBasicModule, idxShl1AddBit]))

end MinCostFlow.WideWord
