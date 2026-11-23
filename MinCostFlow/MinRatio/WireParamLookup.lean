module

public import WordRAM.Contract
public import WordRAM.Layout
public import WordRAM.Logic
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-!
# Bit-by-bit constant comparison and finite lookup dispatcher for parameter setup

Provides deterministic (`Stmt.NoRand`) Word-RAM building blocks for dispatching finitely many
small inputs `(m, V)` without ever embedding large constants in executed expressions:
1. `cmpConst r res tmp B`: compares `st.regs r` against an arbitrary constant `B : ℕ` using only
   `.const 0`, `.const 1`, and `.const 2`, storing `natCmp3 (st.regs r) B ∈ {0, 1, 2}` in `res`
   in `O(B.size)` steps with zero memory writes (requiring only `2 < 2 ^ w`).
2. `storeConstListAt base off xs`: writes the constant list `xs` at `st.regs base + off`.
3. `lookupEntries entries`: scans a finite list of `(m₀, v₀, xs)` records against `(reg 0, reg 1)`;
   on a match it writes `xs` at `reg 4` and immediately returns `reg 4 + xs.length`, and on a
   miss it finishes `.normal` preserving memory and all registers outside `{10, 11}`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- Three-way comparison on natural numbers: `0` for `<`, `1` for `=`, `2` for `>`. -/
@[expose] def natCmp3 (a b : ℕ) : ℕ :=
  if a < b then 0 else if a = b then 1 else 2

/-- Process `k` binary digits of `B` against `reg tmp`, updating `reg res`. -/
@[expose] def cmpConstLoop (res tmp : ℕ) : ℕ → ℕ → Stmt
  | 0, _ => .nop
  | k + 1, B =>
      .cond (.bin .lt (.bin .mod (.reg tmp) (.const 2)) (.const (B % 2)))
        (.assign res (.const 0))
        (.cond (.bin .lt (.const (B % 2)) (.bin .mod (.reg tmp) (.const 2)))
          (.assign res (.const 2))
          .nop) ;;
      .assign tmp (.bin .div (.reg tmp) (.const 2)) ;;
      cmpConstLoop res tmp k (B / 2)

/-- Compare `reg r` against an arbitrary constant `B : ℕ` using only constants `0, 1, 2`.
Writes `natCmp3 (st.regs r) B` to `reg res`, clobbering only `res` and `tmp`. -/
@[expose] def cmpConst (r res tmp B : ℕ) : Stmt :=
  .assign tmp (.reg r) ;;
  .assign res (.const 1) ;;
  cmpConstLoop res tmp B.size B ;;
  .cond (.bin .lt (.const 0) (.reg tmp)) (.assign res (.const 2)) .nop

theorem cmpConstLoop_noRand (res tmp k B : ℕ) : (cmpConstLoop res tmp k B).NoRand := by
  induction k generalizing B with
  | zero => simp [cmpConstLoop, Stmt.NoRand]
  | succ k ih => simp [cmpConstLoop, Stmt.NoRand, ih]

theorem cmpConst_noRand (r res tmp B : ℕ) : (cmpConst r res tmp B).NoRand := by
  simp [cmpConst, cmpConstLoop_noRand, Stmt.NoRand]

private lemma natCmp3_bit_step {lo loB bitX bitB j : ℕ}
    (hlo : lo < 2 ^ j) (hloB : loB < 2 ^ j) :
    natCmp3 (lo + bitX * 2 ^ j) (loB + bitB * 2 ^ j) =
      if bitX < bitB then 0 else if bitB < bitX then 2 else natCmp3 lo loB := by
  unfold natCmp3
  rcases lt_trichotomy bitX bitB with hlt | rfl | hgt
  · have hmul : (bitX + 1) * 2 ^ j ≤ bitB * 2 ^ j := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, one_mul] at hmul
    have hlt' : lo + bitX * 2 ^ j < loB + bitB * 2 ^ j := by omega
    simp [hlt, hlt']
  · simp
  · have hmul : (bitB + 1) * 2 ^ j ≤ bitX * 2 ^ j := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, one_mul] at hmul
    have hgt' : loB + bitB * 2 ^ j < lo + bitX * 2 ^ j := by omega
    simp [show ¬ bitX < bitB by omega, hgt, show ¬ lo + bitX * 2 ^ j < loB + bitB * 2 ^ j by omega,
      show lo + bitX * 2 ^ j ≠ loB + bitB * 2 ^ j by omega]

private lemma cmpConstLoop_runs {w res tmp : ℕ} {p : Program} {ω : ℕ → Bool}
    (hne : res ≠ tmp) (hw2 : 2 < 2 ^ w) :
    ∀ (k B j lo loB x : ℕ) (st : State),
      lo < 2 ^ j → loB < 2 ^ j →
      st.regs res = natCmp3 lo loB →
      st.regs tmp = x →
      x < 2 ^ w →
      ∃ out c, Runs w p ω (cmpConstLoop res tmp k B) st .normal out c ∧
        out.regs res = natCmp3 (lo + (x % 2 ^ k) * 2 ^ j) (loB + (B % 2 ^ k) * 2 ^ j) ∧
        out.regs tmp = x / 2 ^ k ∧
        out.mem = st.mem ∧ out.pos = st.pos ∧
        (∀ r, r ≠ res → r ≠ tmp → out.regs r = st.regs r) ∧
        c ≤ 30 * k + 1
  | 0, B, j, lo, loB, x, st, _, _, hres, htmp, _ => by
      refine ⟨st, 1, runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, ?_, ?_, rfl, rfl, fun _ _ _ => rfl, by omega⟩
      · simpa [Nat.mod_one] using hres
      · simpa using htmp
  | k + 1, B, j, lo, loB, x, st, hlo, hloB, hres, htmp, hxW => by
      have hw0 : 0 < 2 ^ w := by omega
      have hw1 : 1 < 2 ^ w := by omega
      have hxb2 : x % 2 < 2 ^ w := lt_trans (Nat.mod_lt x (by decide)) hw2
      have hBb2 : B % 2 < 2 ^ w := lt_trans (Nat.mod_lt B (by decide)) hw2
      have hxd2 : x / 2 < 2 ^ w := lt_of_le_of_lt (Nat.div_le_self x 2) hxW
      let acc1 := if x % 2 < B % 2 then 0 else if B % 2 < x % 2 then 2 else natCmp3 lo loB
      let s1 : State := { st with regs := Function.update st.regs res acc1 }
      have hcond1 : Expr.eval w st (.bin .lt (.bin .mod (.reg tmp) (.const 2)) (.const (B % 2))) =
          some (if x % 2 < B % 2 then 1 else 0) := by
        by_cases h : x % 2 < B % 2 <;>
          simp [Expr.eval, BinOp.eval, htmp, hw2, hxb2, hBb2, h, hw1, hw0]
      have hr1 : ∃ c1, Runs w p ω
          (.cond (.bin .lt (.bin .mod (.reg tmp) (.const 2)) (.const (B % 2)))
            (.assign res (.const 0))
            (.cond (.bin .lt (.const (B % 2)) (.bin .mod (.reg tmp) (.const 2)))
              (.assign res (.const 2)) .nop)) st .normal s1 c1 ∧ c1 ≤ 20 := by
        by_cases h1 : x % 2 < B % 2
        · refine ⟨8, runs_cond_iff.mpr ⟨1, 2, by simpa [h1] using hcond1,
            runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hw0], rfl,
              by simp [s1, acc1, h1], rfl⟩, rfl⟩, by omega⟩
        · have hcond2 : Expr.eval w st (.bin .lt (.const (B % 2)) (.bin .mod (.reg tmp) (.const 2))) =
              some (if B % 2 < x % 2 then 1 else 0) := by
            by_cases h2 : B % 2 < x % 2 <;>
              simp [Expr.eval, BinOp.eval, htmp, hw2, hxb2, hBb2, h2, hw1, hw0]
          by_cases h2 : B % 2 < x % 2
          · have hinner : Runs w p ω
                (.cond (.bin .lt (.const (B % 2)) (.bin .mod (.reg tmp) (.const 2)))
                  (.assign res (.const 2)) .nop) st .normal s1 8 :=
              runs_cond_iff.mpr ⟨1, 2, by simpa [h2] using hcond2,
                runs_assign_iff.mpr ⟨2, by simp [Expr.eval, hw2], rfl,
                  by simp [s1, acc1, h1, h2], rfl⟩, rfl⟩
            exact ⟨14, runs_cond_iff.mpr ⟨0, 8, by simpa [h1] using hcond1, hinner, rfl⟩, by omega⟩
          · have hs1eq : s1 = st := by
              cases st with | mk mem regs pos =>
              simp only [s1, acc1, h1, h2, ↓reduceIte, State.mk.injEq, true_and, and_true]
              funext r
              by_cases hr : r = res
              · subst hr; simpa using hres.symm
              · exact Function.update_of_ne hr _ _
            have hinner : Runs w p ω
                (.cond (.bin .lt (.const (B % 2)) (.bin .mod (.reg tmp) (.const 2)))
                  (.assign res (.const 2)) .nop) st .normal s1 7 :=
              runs_cond_iff.mpr ⟨0, 1, by simpa [h2] using hcond2,
                hs1eq ▸ runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
            exact ⟨13, runs_cond_iff.mpr ⟨0, 7, by simpa [h1] using hcond1, hinner, rfl⟩, by omega⟩
      obtain ⟨c1, hr1', hc1⟩ := hr1
      let s2 : State := { s1 with regs := Function.update s1.regs tmp (x / 2) }
      have hs1_tmp : s1.regs tmp = x := by
        simp [s1, Function.update_of_ne hne.symm, htmp]
      have hr2 : Runs w p ω (.assign tmp (.bin .div (.reg tmp) (.const 2))) s1 .normal s2 4 :=
        runs_assign_iff.mpr ⟨x / 2, by simp [Expr.eval, BinOp.eval, hs1_tmp, hw2, hxd2],
          rfl, rfl, rfl⟩
      have hlo' : lo + (x % 2) * 2 ^ j < 2 ^ (j + 1) := by
        have hlt : x % 2 ≤ 1 := by omega
        rw [pow_succ]; nlinarith
      have hloB' : loB + (B % 2) * 2 ^ j < 2 ^ (j + 1) := by
        have hlt : B % 2 ≤ 1 := by omega
        rw [pow_succ]; nlinarith
      have hacc1 : acc1 = natCmp3 (lo + (x % 2) * 2 ^ j) (loB + (B % 2) * 2 ^ j) :=
        (natCmp3_bit_step hlo hloB).symm
      have hs2_res : s2.regs res = natCmp3 (lo + (x % 2) * 2 ^ j) (loB + (B % 2) * 2 ^ j) := by
        simp [s2, s1, Function.update_of_ne hne, hacc1]
      obtain ⟨out, c3, hr3, hres3, htmp3, hmem3, hpos3, hkeep3, hc3⟩ :=
        cmpConstLoop_runs hne hw2 k (B / 2) (j + 1)
          (lo + (x % 2) * 2 ^ j) (loB + (B % 2) * 2 ^ j) (x / 2) s2
          hlo' hloB' hs2_res (by simp [s2]) hxd2
      refine ⟨out, c1 + (4 + c3 + 1) + 1,
        runs_seq_iff.mpr (Or.inr ⟨s1, c1, 4 + c3 + 1, hr1',
          runs_seq_iff.mpr (Or.inr ⟨s2, 4, c3, hr2, hr3, rfl⟩), rfl⟩),
        ?_, ?_, hmem3, hpos3, ?_, by omega⟩
      · have hxmod : x % 2 ^ (k + 1) = x % 2 + 2 * (x / 2 % 2 ^ k) := by
          rw [pow_succ', Nat.mod_mul]
        have hBmod : B % 2 ^ (k + 1) = B % 2 + 2 * (B / 2 % 2 ^ k) := by
          rw [pow_succ', Nat.mod_mul]
        have h1 : lo + (x % 2) * 2 ^ j + (x / 2 % 2 ^ k) * 2 ^ (j + 1) =
            lo + (x % 2 ^ (k + 1)) * 2 ^ j := by
          rw [hxmod, pow_succ']; ring
        have h2 : loB + (B % 2) * 2 ^ j + (B / 2 % 2 ^ k) * 2 ^ (j + 1) =
            loB + (B % 2 ^ (k + 1)) * 2 ^ j := by
          rw [hBmod, pow_succ']; ring
        rwa [h1, h2] at hres3
      · rw [htmp3, Nat.div_div_eq_div_mul, ← pow_succ']
      · intro r hr1 hr2
        exact (hkeep3 r hr1 hr2).trans (by simp [s2, s1, Function.update_of_ne hr1, Function.update_of_ne hr2])

/-- `cmpConst r res tmp B` writes `natCmp3 (st.regs r) B` to `res`, preserving memory and all
registers other than `res` and `tmp`, in at most `30 * B.size + 25` steps. -/
theorem cmpConst_runs {w r res tmp B x : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hne : res ≠ tmp) (hw2 : 2 < 2 ^ w) (hr : st.regs r = x) (hxW : x < 2 ^ w) :
    ∃ out c, Runs w p ω (cmpConst r res tmp B) st .normal out c ∧
      out.regs res = natCmp3 x B ∧
      out.mem = st.mem ∧ out.pos = st.pos ∧
      (∀ reg, reg ≠ res → reg ≠ tmp → out.regs reg = st.regs reg) ∧
      c ≤ 30 * B.size + 25 := by
  have hw0 : 0 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  let s1 : State := { st with regs := Function.update st.regs tmp x }
  let s2 : State := { s1 with regs := Function.update s1.regs res 1 }
  have hr1 : Runs w p ω (.assign tmp (.reg r)) st .normal s1 2 :=
    runs_assign_iff.mpr ⟨x, by simp [Expr.eval, hr], rfl, rfl, rfl⟩
  have hr2 : Runs w p ω (.assign res (.const 1)) s1 .normal s2 2 :=
    runs_assign_iff.mpr ⟨1, by simp [Expr.eval, hw1], rfl, rfl, rfl⟩
  have hs2_tmp : s2.regs tmp = x := by simp [s2, s1, Function.update_of_ne hne.symm]
  obtain ⟨s3, c3, hr3, hres3, htmp3, hmem3, hpos3, hkeep3, hc3⟩ :=
    cmpConstLoop_runs hne hw2 B.size B 0 0 0 x s2
      (by decide) (by decide) (by simp [s2, natCmp3]) hs2_tmp hxW
  have hBmod : B % 2 ^ B.size = B := Nat.mod_eq_of_lt (Nat.lt_size_self B)
  have hres3' : s3.regs res = natCmp3 (x % 2 ^ B.size) B := by
    simpa [hBmod] using hres3
  have hcond : Expr.eval w s3 (.bin .lt (.const 0) (.reg tmp)) =
      some (if 0 < x / 2 ^ B.size then 1 else 0) := by
    by_cases h : 0 < x / 2 ^ B.size <;>
      simp [Expr.eval, BinOp.eval, htmp3, hw0, hw1, h]
  by_cases hhi : 0 < x / 2 ^ B.size
  · let out : State := { s3 with regs := Function.update s3.regs res 2 }
    have hr4 : Runs w p ω (.cond (.bin .lt (.const 0) (.reg tmp)) (.assign res (.const 2)) .nop)
        s3 .normal out 6 :=
      runs_cond_iff.mpr ⟨1, 2, by simpa [hhi] using hcond,
        runs_assign_iff.mpr ⟨2, by simp [Expr.eval, hw2], rfl, rfl, rfl⟩, rfl⟩
    have hxgt : B < x := by
      have h1 : 2 ^ B.size ≤ x := by
        have := Nat.div_pos_iff.mp hhi
        exact this.2
      exact lt_of_lt_of_le (Nat.lt_size_self B) h1
    refine ⟨out, 2 + (2 + (c3 + 6 + 1) + 1) + 1,
      runs_seq_iff.mpr (Or.inr ⟨s1, 2, _, hr1,
        runs_seq_iff.mpr (Or.inr ⟨s2, 2, _, hr2,
          runs_seq_iff.mpr (Or.inr ⟨s3, c3, 6, hr3, hr4, rfl⟩), rfl⟩), rfl⟩),
      by simp [out, natCmp3, show ¬ x < B by omega, show x ≠ B by omega],
      hmem3, hpos3, ?_, by omega⟩
    intro reg hreg1 hreg2
    exact (by simp [out, Function.update_of_ne hreg1] : out.regs reg = s3.regs reg).trans
      ((hkeep3 reg hreg1 hreg2).trans (by simp [s2, s1, Function.update_of_ne hreg1, Function.update_of_ne hreg2]))
  · have hdiv0 : x / 2 ^ B.size = 0 := by omega
    have hxlt : x < 2 ^ B.size := by
      exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos B.size)).mp hdiv0
    have hxmod : x % 2 ^ B.size = x := Nat.mod_eq_of_lt hxlt
    have hr4 : Runs w p ω (.cond (.bin .lt (.const 0) (.reg tmp)) (.assign res (.const 2)) .nop)
        s3 .normal s3 5 :=
      runs_cond_iff.mpr ⟨0, 1, by simpa [hhi] using hcond,
        runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
    refine ⟨s3, 2 + (2 + (c3 + 5 + 1) + 1) + 1,
      runs_seq_iff.mpr (Or.inr ⟨s1, 2, _, hr1,
        runs_seq_iff.mpr (Or.inr ⟨s2, 2, _, hr2,
          runs_seq_iff.mpr (Or.inr ⟨s3, c3, 5, hr3, hr4, rfl⟩), rfl⟩), rfl⟩),
      by simpa [hxmod] using hres3', hmem3, hpos3, ?_, by omega⟩
    intro reg hreg1 hreg2
    exact (hkeep3 reg hreg1 hreg2).trans
      (by simp [s2, s1, Function.update_of_ne hreg1, Function.update_of_ne hreg2])

/-- Store a fixed list of constants starting at `st.regs base + off`. -/
@[expose] def storeConstListAt (base : ℕ) : ℕ → List ℕ → Stmt
  | _, [] => .nop
  | off, x :: xs =>
      .store (.bin .add (.reg base) (.const off)) (.const x) ;;
      storeConstListAt base (off + 1) xs

theorem storeConstListAt_noRand (base off : ℕ) (xs : List ℕ) :
    (storeConstListAt base off xs).NoRand := by
  induction xs generalizing off with
  | nil => simp [storeConstListAt, Stmt.NoRand]
  | cons x xs ih => simp [storeConstListAt, Stmt.NoRand, ih]

theorem storeConstListAt_runs {w base : ℕ} {p : Program} {ω : ℕ → Bool} :
    ∀ (off : ℕ) (xs : List ℕ) (st : State),
      (∀ x ∈ xs, x < 2 ^ w) →
      st.regs base + off + xs.length < 2 ^ w →
      ∃ out c, Runs w p ω (storeConstListAt base off xs) st .normal out c ∧
        ListAt out.mem (st.regs base + off) xs ∧
        (∀ a, a < st.regs base + off ∨ st.regs base + off + xs.length ≤ a → out.mem a = st.mem a) ∧
        out.regs = st.regs ∧ out.pos = st.pos ∧ c ≤ 8 * xs.length + 1
  | off, [], st, _, _ =>
      ⟨st, 1, runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by intro j hj; simp at hj,
        fun _ _ => rfl, rfl, rfl, by omega⟩
  | off, x :: xs, st, hxs, hroom => by
      have hxW : x < 2 ^ w := hxs x (by simp)
      have hoffW : off < 2 ^ w := by simp at hroom; omega
      have haddrW : st.regs base + off < 2 ^ w := by simp at hroom; omega
      let s1 := { st with mem := Function.update st.mem (st.regs base + off) x }
      have hr1 : Runs w p ω (.store (.bin .add (.reg base) (.const off)) (.const x)) st .normal s1 5 :=
        runs_store_iff.mpr ⟨st.regs base + off, x,
          by simp [Expr.eval, BinOp.eval, hoffW, haddrW],
          by simp [Expr.eval, hxW], rfl, rfl, rfl⟩
      obtain ⟨out, c2, hr2, hlist2, hframe2, hregs2, hpos2, hc2⟩ :=
        storeConstListAt_runs (w := w) (base := base) (p := p) (ω := ω) (off + 1) xs s1
          (fun y hy => hxs y (by simp [hy]))
          (by simp only [s1, List.length_cons] at hroom ⊢; omega)
      refine ⟨out, 5 + c2 + 1, runs_seq_iff.mpr (Or.inr ⟨s1, 5, c2, hr1, hr2, rfl⟩), ?_, ?_,
        hregs2, hpos2, by simp only [List.length_cons]; omega⟩
      · intro j hj
        cases j with
        | zero =>
          have hne : st.regs base + off < st.regs base + (off + 1) := by omega
          simpa [s1] using (hframe2 (st.regs base + off) (Or.inl hne)).trans (by simp [s1])
        | succ j' =>
          have hj' : j' < xs.length := by simpa using hj
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlist2 j' hj'
      · intro a ha
        simp only [List.length_cons] at ha
        rcases ha with hlt | hge
        · rw [hframe2 a (Or.inl (by dsimp [s1]; omega))]
          simp [s1, Function.update_of_ne (show a ≠ st.regs base + off by omega)]
        · rw [hframe2 a (Or.inr (by dsimp [s1]; omega))]
          simp [s1, Function.update_of_ne (show a ≠ st.regs base + off by omega)]

/-- Test one finite-table entry `(m₀, v₀, xs)` against `(reg 0, reg 1)`. On match, writes `xs` at
`reg 4` and returns `reg 4 + xs.length`; on miss, finishes `.normal` preserving memory and all
registers outside `{10, 11}`. -/
@[expose] def lookupOneEntry (m₀ v₀ : ℕ) (xs : List ℕ) : Stmt :=
  cmpConst 0 10 11 m₀ ;;
  .cond (.bin .eq (.reg 10) (.const 1))
    (cmpConst 1 10 11 v₀ ;;
     .cond (.bin .eq (.reg 10) (.const 1))
       (storeConstListAt 4 0 xs ;; .ret (.bin .add (.reg 4) (.const xs.length)))
       .nop)
    .nop

/-- Linear dispatcher scanning a finite list of `(m₀, v₀, xs)` entries. -/
@[expose] def lookupEntries : List (ℕ × ℕ × List ℕ) → Stmt
  | [] => .nop
  | (m₀, v₀, xs) :: rest => lookupOneEntry m₀ v₀ xs ;; lookupEntries rest

theorem lookupOneEntry_noRand (m₀ v₀ : ℕ) (xs : List ℕ) :
    (lookupOneEntry m₀ v₀ xs).NoRand := by
  simp [lookupOneEntry, cmpConst_noRand, storeConstListAt_noRand, Stmt.NoRand]

theorem lookupEntries_noRand (entries : List (ℕ × ℕ × List ℕ)) :
    (lookupEntries entries).NoRand := by
  induction entries with
  | nil => simp [lookupEntries, Stmt.NoRand]
  | cons e rest ih =>
      rcases e with ⟨m₀, v₀, xs⟩
      simp [lookupEntries, lookupOneEntry_noRand, ih, Stmt.NoRand]

/-- Static step-cost upper bound for one entry of `lookupEntries`. -/
@[expose] def lookupEntryCost (m₀ v₀ : ℕ) (xs : List ℕ) : ℕ :=
  30 * m₀.size + 30 * v₀.size + 8 * xs.length + 80

/-- Static step-cost upper bound for scanning all of `lookupEntries`. -/
@[expose] def lookupEntriesCost : List (ℕ × ℕ × List ℕ) → ℕ
  | [] => 1
  | (m₀, v₀, xs) :: rest => lookupEntryCost m₀ v₀ xs + lookupEntriesCost rest + 2

theorem lookupOneEntry_runs_miss {w m V m₀ v₀ : ℕ} {xs : List ℕ} {p : Program} {ω : ℕ → Bool}
    {st : State} (hw2 : 2 < 2 ^ w)
    (h0 : st.regs 0 = m) (h1 : st.regs 1 = V) (hmW : m < 2 ^ w) (hVW : V < 2 ^ w)
    (hmiss : m ≠ m₀ ∨ V ≠ v₀) :
    ∃ out c, Runs w p ω (lookupOneEntry m₀ v₀ xs) st .normal out c ∧
      out.mem = st.mem ∧ out.pos = st.pos ∧
      (∀ r, r ≠ 10 → r ≠ 11 → out.regs r = st.regs r) ∧
      c ≤ lookupEntryCost m₀ v₀ xs := by
  have hw0 : 0 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  obtain ⟨s1, c1, hr1, hs1_10, hmem1, hpos1, hkeep1, hc1⟩ :=
    cmpConst_runs (w := w) (r := 0) (res := 10) (tmp := 11) (B := m₀) (x := m)
      (p := p) (ω := ω) (st := st) (by decide) hw2 h0 hmW
  by_cases hm : m = m₀
  · have hV : V ≠ v₀ := hmiss.elim (fun h => (h hm).elim) id
    have h10_1 : s1.regs 10 = 1 := by simp [hs1_10, natCmp3, hm]
    have hs1_1 : s1.regs 1 = V := (hkeep1 1 (by decide) (by decide)).trans h1
    obtain ⟨s2, c2, hr2, hs2_10, hmem2, hpos2, hkeep2, hc2⟩ :=
      cmpConst_runs (w := w) (r := 1) (res := 10) (tmp := 11) (B := v₀) (x := V)
        (p := p) (ω := ω) (st := s1) (by decide) hw2 hs1_1 hVW
    have h10_ne1 : s2.regs 10 ≠ 1 := by
      rw [hs2_10]; unfold natCmp3; split_ifs <;> omega
    have hcond2 : Expr.eval w s2 (.bin .eq (.reg 10) (.const 1)) = some 0 := by
      simp [Expr.eval, BinOp.eval, hw1, hw0, h10_ne1]
    have hinner2 : Runs w p ω
        (.cond (.bin .eq (.reg 10) (.const 1))
          (storeConstListAt 4 0 xs ;; .ret (.bin .add (.reg 4) (.const xs.length))) .nop)
        s2 .normal s2 5 :=
      runs_cond_iff.mpr ⟨0, 1, hcond2, runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
    have hbranch : Runs w p ω
        (cmpConst 1 10 11 v₀ ;;
          .cond (.bin .eq (.reg 10) (.const 1))
            (storeConstListAt 4 0 xs ;; .ret (.bin .add (.reg 4) (.const xs.length))) .nop)
        s1 .normal s2 (c2 + 5 + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨s2, c2, 5, hr2, hinner2, rfl⟩)
    have hcond1 : Expr.eval w s1 (.bin .eq (.reg 10) (.const 1)) = some 1 := by
      simp [Expr.eval, BinOp.eval, h10_1, hw1]
    have houter : Runs w p ω
        (.cond (.bin .eq (.reg 10) (.const 1))
          (cmpConst 1 10 11 v₀ ;;
            .cond (.bin .eq (.reg 10) (.const 1))
              (storeConstListAt 4 0 xs ;; .ret (.bin .add (.reg 4) (.const xs.length))) .nop)
          .nop) s1 .normal s2 (3 + (c2 + 5 + 1) + 1) :=
      runs_cond_iff.mpr ⟨1, c2 + 5 + 1, hcond1, hbranch, rfl⟩
    refine ⟨s2, c1 + (3 + (c2 + 5 + 1) + 1) + 1,
      runs_seq_iff.mpr (Or.inr ⟨s1, c1, _, hr1, houter, rfl⟩),
      hmem2.trans hmem1, hpos2.trans hpos1,
      fun r hr10 hr11 => (hkeep2 r hr10 hr11).trans (hkeep1 r hr10 hr11), ?_⟩
    unfold lookupEntryCost; omega
  · have h10_ne1 : s1.regs 10 ≠ 1 := by
      rw [hs1_10]; unfold natCmp3; split_ifs <;> omega
    have hcond1 : Expr.eval w s1 (.bin .eq (.reg 10) (.const 1)) = some 0 := by
      simp [Expr.eval, BinOp.eval, hw1, hw0, h10_ne1]
    have houter : Runs w p ω
        (.cond (.bin .eq (.reg 10) (.const 1))
          (cmpConst 1 10 11 v₀ ;;
            .cond (.bin .eq (.reg 10) (.const 1))
              (storeConstListAt 4 0 xs ;; .ret (.bin .add (.reg 4) (.const xs.length))) .nop)
          .nop) s1 .normal s1 5 :=
      runs_cond_iff.mpr ⟨0, 1, hcond1, runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
    refine ⟨s1, c1 + 5 + 1,
      runs_seq_iff.mpr (Or.inr ⟨s1, c1, 5, hr1, houter, rfl⟩),
      hmem1, hpos1, hkeep1, ?_⟩
    unfold lookupEntryCost; omega

theorem lookupOneEntry_runs_hit {w m V heap : ℕ} {xs : List ℕ} {p : Program} {ω : ℕ → Bool}
    {st : State} (hw2 : 2 < 2 ^ w)
    (h0 : st.regs 0 = m) (h1 : st.regs 1 = V) (h4 : st.regs 4 = heap)
    (hmW : m < 2 ^ w) (hVW : V < 2 ^ w)
    (hxs : ∀ x ∈ xs, x < 2 ^ w) (hroom : heap + xs.length < 2 ^ w) :
    ∃ out c, Runs w p ω (lookupOneEntry m V xs) st (.returned (heap + xs.length)) out c ∧
      ListAt out.mem heap xs ∧
      (∀ a, a < heap ∨ heap + xs.length ≤ a → out.mem a = st.mem a) ∧
      c ≤ lookupEntryCost m V xs := by
  have hw1 : 1 < 2 ^ w := by omega
  obtain ⟨s1, c1, hr1, hs1_10, hmem1, _, hkeep1, hc1⟩ :=
    cmpConst_runs (w := w) (r := 0) (res := 10) (tmp := 11) (B := m) (x := m)
      (p := p) (ω := ω) (st := st) (by decide) hw2 h0 hmW
  have h10_1 : s1.regs 10 = 1 := by simp [hs1_10, natCmp3]
  have hs1_1 : s1.regs 1 = V := (hkeep1 1 (by decide) (by decide)).trans h1
  obtain ⟨s2, c2, hr2, hs2_10, hmem2, _, hkeep2, hc2⟩ :=
    cmpConst_runs (w := w) (r := 1) (res := 10) (tmp := 11) (B := V) (x := V)
      (p := p) (ω := ω) (st := s1) (by decide) hw2 hs1_1 hVW
  have hs2_10_1 : s2.regs 10 = 1 := by simp [hs2_10, natCmp3]
  have hs2_4 : s2.regs 4 = heap := (hkeep2 4 (by decide) (by decide)).trans
    ((hkeep1 4 (by decide) (by decide)).trans h4)
  obtain ⟨s3, c3, hr3, hlist3, hframe3, hregs3, _, hc3⟩ :=
    storeConstListAt_runs (w := w) (base := 4) (p := p) (ω := ω) 0 xs s2 hxs
      (by rw [hs2_4]; omega)
  have hlenW : xs.length < 2 ^ w := by omega
  have hr4 : Runs w p ω (.ret (.bin .add (.reg 4) (.const xs.length))) s3
      (.returned (heap + xs.length)) s3 4 :=
    runs_ret_iff.mpr ⟨heap + xs.length,
      by simp [Expr.eval, BinOp.eval, hregs3, hs2_4, hlenW, hroom], rfl, rfl, rfl⟩
  have hbody : Runs w p ω
      (storeConstListAt 4 0 xs ;; .ret (.bin .add (.reg 4) (.const xs.length)))
      s2 (.returned (heap + xs.length)) s3 (c3 + 4 + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s3, c3, 4, hr3, hr4, rfl⟩)
  have hcond2 : Expr.eval w s2 (.bin .eq (.reg 10) (.const 1)) = some 1 := by
    simp [Expr.eval, BinOp.eval, hs2_10_1, hw1]
  have hinner2 : Runs w p ω
      (.cond (.bin .eq (.reg 10) (.const 1))
        (storeConstListAt 4 0 xs ;; .ret (.bin .add (.reg 4) (.const xs.length))) .nop)
      s2 (.returned (heap + xs.length)) s3 (3 + (c3 + 4 + 1) + 1) :=
    runs_cond_iff.mpr ⟨1, c3 + 4 + 1, hcond2, hbody, rfl⟩
  have hbranch : Runs w p ω
      (cmpConst 1 10 11 V ;;
        .cond (.bin .eq (.reg 10) (.const 1))
          (storeConstListAt 4 0 xs ;; .ret (.bin .add (.reg 4) (.const xs.length))) .nop)
      s1 (.returned (heap + xs.length)) s3 (c2 + (3 + (c3 + 4 + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s2, c2, _, hr2, hinner2, rfl⟩)
  have hcond1 : Expr.eval w s1 (.bin .eq (.reg 10) (.const 1)) = some 1 := by
    simp [Expr.eval, BinOp.eval, h10_1, hw1]
  have houter : Runs w p ω
      (.cond (.bin .eq (.reg 10) (.const 1))
        (cmpConst 1 10 11 V ;;
          .cond (.bin .eq (.reg 10) (.const 1))
            (storeConstListAt 4 0 xs ;; .ret (.bin .add (.reg 4) (.const xs.length))) .nop)
        .nop) s1 (.returned (heap + xs.length)) s3
      (3 + (c2 + (3 + (c3 + 4 + 1) + 1) + 1) + 1) :=
    runs_cond_iff.mpr ⟨1, c2 + (3 + (c3 + 4 + 1) + 1) + 1, hcond1, hbranch, rfl⟩
  refine ⟨s3, c1 + (3 + (c2 + (3 + (c3 + 4 + 1) + 1) + 1) + 1) + 1,
    runs_seq_iff.mpr (Or.inr ⟨s1, c1, _, hr1, houter, rfl⟩),
    by simpa [hs2_4] using hlist3, ?_, ?_⟩
  · intro a ha
    have hf := hframe3 a (by simpa [hs2_4] using ha)
    exact hf.trans (by rw [hmem2, hmem1])
  · unfold lookupEntryCost; omega

/-- If no entry in `entries` has key `(m, V)`, `lookupEntries entries` finishes `.normal`
preserving memory and all registers outside `{10, 11}`. -/
theorem lookupEntries_runs_miss {w m V : ℕ} {p : Program} {ω : ℕ → Bool} :
    ∀ (entries : List (ℕ × ℕ × List ℕ)) (st : State),
      2 < 2 ^ w →
      st.regs 0 = m → st.regs 1 = V → m < 2 ^ w → V < 2 ^ w →
      (∀ e ∈ entries, m ≠ e.1 ∨ V ≠ e.2.1) →
      ∃ out c, Runs w p ω (lookupEntries entries) st .normal out c ∧
        out.mem = st.mem ∧ out.pos = st.pos ∧
        (∀ r, r ≠ 10 → r ≠ 11 → out.regs r = st.regs r) ∧
        c ≤ lookupEntriesCost entries
  | [], st, _, _, _, _, _, _ =>
      ⟨st, 1, runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl, rfl, fun _ _ _ => rfl, by simp [lookupEntriesCost]⟩
  | (m₀, v₀, xs) :: rest, st, hw2, h0, h1, hmW, hVW, hmiss => by
      obtain ⟨s1, c1, hr1, hmem1, hpos1, hkeep1, hc1⟩ :=
        lookupOneEntry_runs_miss (w := w) (m₀ := m₀) (v₀ := v₀) (xs := xs) (p := p) (ω := ω)
          hw2 h0 h1 hmW hVW (hmiss (m₀, v₀, xs) (by simp))
      obtain ⟨out, c2, hr2, hmem2, hpos2, hkeep2, hc2⟩ :=
        lookupEntries_runs_miss rest s1 hw2
          ((hkeep1 0 (by decide) (by decide)).trans h0)
          ((hkeep1 1 (by decide) (by decide)).trans h1)
          hmW hVW (fun e he => hmiss e (by simp [he]))
      refine ⟨out, c1 + c2 + 1, runs_seq_iff.mpr (Or.inr ⟨s1, c1, c2, hr1, hr2, rfl⟩),
        hmem2.trans hmem1, hpos2.trans hpos1,
        fun r hr10 hr11 => (hkeep2 r hr10 hr11).trans (hkeep1 r hr10 hr11), ?_⟩
      simp only [lookupEntriesCost]; omega

/-- If `(m, V, xs)` appears in `entries` with no earlier duplicate key matching `(m, V)`,
`lookupEntries entries` writes `xs` at `heap` and returns `heap + xs.length`. -/
theorem lookupEntries_runs_hit {w m V heap : ℕ} {xs : List ℕ} {p : Program} {ω : ℕ → Bool} :
    ∀ (entries : List (ℕ × ℕ × List ℕ)) (st : State),
      2 < 2 ^ w →
      st.regs 0 = m → st.regs 1 = V → st.regs 4 = heap →
      m < 2 ^ w → V < 2 ^ w →
      (m, V, xs) ∈ entries →
      (∀ e ∈ entries, e.1 = m → e.2.1 = V → e.2.2 = xs) →
      (∀ x ∈ xs, x < 2 ^ w) → heap + xs.length < 2 ^ w →
      ∃ out c, Runs w p ω (lookupEntries entries) st (.returned (heap + xs.length)) out c ∧
        ListAt out.mem heap xs ∧
        (∀ a, a < heap ∨ heap + xs.length ≤ a → out.mem a = st.mem a) ∧
        c ≤ lookupEntriesCost entries
  | [], _, _, _, _, _, _, _, hmem, _, _, _ => by simp at hmem
  | (m₀, v₀, ys) :: rest, st, hw2, h0, h1, h4, hmW, hVW, hmem, huniq, hxs, hroom => by
      by_cases hmatch : m = m₀ ∧ V = v₀
      · rcases hmatch with ⟨rfl, rfl⟩
        have hys : ys = xs := huniq (m, V, ys) (by simp) rfl rfl
        subst hys
        obtain ⟨out, c1, hr1, hlist1, hframe1, hc1⟩ :=
          lookupOneEntry_runs_hit (w := w) (p := p) (ω := ω) hw2 h0 h1 h4 hmW hVW hxs hroom
        refine ⟨out, c1 + 1, runs_seq_iff.mpr (Or.inl ⟨heap + ys.length, c1, hr1, rfl, rfl⟩),
          hlist1, hframe1, ?_⟩
        simp only [lookupEntriesCost]; omega
      · have hmiss : m ≠ m₀ ∨ V ≠ v₀ := by tauto
        have hmem' : (m, V, xs) ∈ rest := by
          rcases List.mem_cons.mp hmem with heq | hrest
          · cases heq; exact (hmatch ⟨rfl, rfl⟩).elim
          · exact hrest
        obtain ⟨s1, c1, hr1, hmem1, _, hkeep1, hc1⟩ :=
          lookupOneEntry_runs_miss (w := w) (m₀ := m₀) (v₀ := v₀) (xs := ys) (p := p) (ω := ω)
            hw2 h0 h1 hmW hVW hmiss
        obtain ⟨out, c2, hr2, hlist2, hframe2, hc2⟩ :=
          lookupEntries_runs_hit rest s1 hw2
            ((hkeep1 0 (by decide) (by decide)).trans h0)
            ((hkeep1 1 (by decide) (by decide)).trans h1)
            ((hkeep1 4 (by decide) (by decide)).trans h4)
            hmW hVW hmem' (fun e he => huniq e (by simp [he])) hxs hroom
        refine ⟨out, c1 + c2 + 1, runs_seq_iff.mpr (Or.inr ⟨s1, c1, c2, hr1, hr2, rfl⟩),
          hlist2, fun a ha => (hframe2 a ha).trans (by rw [hmem1]), ?_⟩
        simp only [lookupEntriesCost]; omega

end MinCostFlow.MinRatio

end
