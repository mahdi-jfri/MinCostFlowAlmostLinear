module

public import MinCostFlow.ExplicitExpander.ProgramCore
public import MinCostFlow.ExplicitExpander.Spec
public import MinCostFlow.Statement.Cited.ChuzhoyEtAl
public import WordRAM.Entry
import Mathlib.Tactic.Linarith

/-!
# Theorem 2.4 of [CGLNPS21]: an explicit expander in linear time

This file proves `Cited.ExplicitExpander`, Theorem 2.4 of Chuzhoy, Gao, Li, Nanongkai, Peng and
Saranurak (arXiv:1910.08025v2, page 15), as the theorem `explicitExpander`, with
`α₀ = 1/12`, word size constant `c = 4` and time constant `K = 400`.

The program `explicitProgram` reads `n` and

1. finds `m = ⌊√n⌋` by trying `m = 1, 2, …` (`sqrtLoop`, at most `n` rounds);
2. writes the edges of the Margulis part and then the other edges from address `2` on
   (`coreLoop_triple`, `pendLoop_triple` of `ProgramCore.lean`);
3. writes `n` and the number of edges at addresses `0` and `1`, and returns the length of the
   output.

The output is `(explicitGraph n).encode`, and `explicitGraph_spec` of `Spec.lean` gives the
properties of the graph. Every value fits in a word of size `wordSize 4 [n]`, since it is below
`16n + 48 ≤ (n + 3)^4`. The program has no `rand` statement, so its run does not depend on the
random bits.
-/

public section

namespace MinCostFlow.ExplicitExpander

open WordRAM MinCostFlow.Cited

/-- `while (m + 1)² < n + 1 do m := m + 1`, with `n` and `m` in registers `1` and `2`. -/
@[expose] def sqrtLoop : Stmt :=
  .loop (.bin .lt (.bin .mul (.bin .add (.reg 2) (.const 1)) (.bin .add (.reg 2) (.const 1)))
      (.bin .add (.reg 1) (.const 1)))
    (.assign 2 (.bin .add (.reg 2) (.const 1)))

/-- The body of the program. -/
@[expose] def mainBody : Stmt :=
  .seq (.assign 1 (.load (.const 0)))
  (.seq (.assign 2 (.const 1))
  (.seq sqrtLoop
  (.seq (.assign 3 (.bin .mul (.reg 2) (.reg 2)))
  (.seq (.assign 4 (.const 2))
  (.seq (forRange 5 (.const 0) (.reg 3) coreBody)
  (.seq (forRange 5 (.reg 3) (.reg 1) pendBody)
  (.seq (.store (.const 0) (.reg 1))
  (.seq (.store (.const 1) (.bin .div (.bin .sub (.reg 4) (.const 2)) (.const 2)))
  (.ret (.reg 4))))))))))

/-- The program that writes the explicit expander. -/
@[expose] def explicitProgram : Program := ⟨[mainBody]⟩

variable {w : ℕ}

private lemma succ_sq_le {k n : ℕ} (hk : 1 ≤ k) (h : k * k ≤ n) : (k + 1) * (k + 1) ≤ 4 * n := by
  nlinarith

/-- The loop `sqrtLoop` finds `⌊√n⌋`. -/
theorem sqrtLoop_triple (p : Program) {n : ℕ} (hW : 16 * n + 48 < 2 ^ w) :
    Triple w p (fun st => st.regs 1 = n ∧ 1 ≤ st.regs 2 ∧ st.regs 2 * st.regs 2 ≤ n) sqrtLoop
      (normalPost fun st => st.regs 1 = n ∧ st.regs 2 = Nat.sqrt n)
      (fun _ => 16 * n + 12) := by
  have hw : 1 < 2 ^ w := by omega
  have h := Triple.loop_const_normal (w := w) (p := p) (e := .bin .lt (.bin .mul
      (.bin .add (.reg 2) (.const 1)) (.bin .add (.reg 2) (.const 1)))
      (.bin .add (.reg 1) (.const 1)))
    (body := .assign 2 (.bin .add (.reg 2) (.const 1)))
    (Inv := fun st => st.regs 1 = n ∧ 1 ≤ st.regs 2 ∧ st.regs 2 * st.regs 2 ≤ n)
    (Q := fun st => st.regs 1 = n ∧ st.regs 2 = Nat.sqrt n)
    (fun st => n - st.regs 2)
    (fun st => if (st.regs 2 + 1) * (st.regs 2 + 1) < n + 1 then 1 else 0) 4
    (fun st ⟨h1, hk, hkn⟩ => by
      have hsq := succ_sq_le hk hkn
      have hk1 : st.regs 2 + 1 < 2 ^ w := by nlinarith
      exact Expr.eval_lt_op
        (Expr.eval_mul (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const hw) hk1)
          (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const hw) hk1) (by omega))
        (Expr.eval_add (Expr.eval_reg_of_eq h1) (Expr.eval_const hw) (by omega)) hw)
    (fun st ⟨h1, _, hkn⟩ hc => by
      refine ⟨h1, Nat.eq_sqrt.mpr ⟨hkn, ?_⟩⟩
      by_contra hlt
      simp only [show (st.regs 2 + 1) * (st.regs 2 + 1) < n + 1 by omega, ↓reduceIte] at hc
      exact one_ne_zero hc)
    (fun st ⟨h1, hk, hkn⟩ hc => by
      have hlt : (st.regs 2 + 1) * (st.regs 2 + 1) < n + 1 := by
        by_contra hlt
        simp only [hlt, ↓reduceIte, ne_eq, not_true_eq_false] at hc
      have hk1 : st.regs 2 + 1 ≤ n := by nlinarith
      intro s ω hs
      subst hs
      refine ⟨.normal, { s with regs := Function.update s.regs 2 (s.regs 2 + 1) }, 4,
        runs_assign_iff.mpr ⟨s.regs 2 + 1,
          Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const hw) (by omega), rfl, rfl,
          rfl⟩, ?_, le_rfl⟩
      simp only [normalPost, Function.update_self]
      refine ⟨⟨?_, by omega, by omega⟩, by omega⟩
      rw [Function.update_of_ne (by decide)]; exact h1)
  refine h.mono_cost fun st ⟨_, hk, _⟩ => ?_
  simp only [Expr.size]
  have : (11 + 4 + 1) * (n - st.regs 2) ≤ 16 * n := by
    rw [show 11 + 4 + 1 = 16 by rfl]
    exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  omega

/-- The run of the body: it returns the length of the output and leaves
`(explicitGraph n).encode` at address `0`. -/
theorem mainBody_runs {n : ℕ} (hn : 1 ≤ n) (hW : 16 * n + 48 < 2 ^ w) (ω : ℕ → Bool) :
    ∃ o st' c, Runs w explicitProgram ω mainBody (startState [1] (initMem [n]) 0) o st' c ∧
      (o = .returned (explicitGraph n).encode.length ∧
        ListAt st'.mem 0 (explicitGraph n).encode) ∧ c ≤ 300 * n + 100 := by
  have hw : 1 < 2 ^ w := by omega
  set m := Nat.sqrt n with hm
  have hm1 : 1 ≤ m := Nat.sqrt_pos.mpr hn
  have hN : m * m ≤ n := Nat.sqrt_le n
  have hmem0 : (startState [1] (initMem [n]) 0).mem 0 = n := by simp [startState, initMem]
  refine runs_start_le (runs_seq_assign_le (v := n)
    (Expr.eval_load_of_eq (Expr.eval_const (by omega)) hmem0) ?_)
  refine runs_seq_assign_le (v := 1) (Expr.eval_const hw) ?_
  refine runs_seq_triple_le (sqrtLoop_triple explicitProgram hW) ⟨?_, ?_, ?_⟩ ?_
  · simp only [Function.update_of_ne (show (1 : ℕ) ≠ 2 by decide), Function.update_self]
  · simp only [Function.update_self, le_refl]
  · simp only [Function.update_self]; omega
  intro st₁ ⟨h1, h2⟩
  refine runs_seq_assign_le (v := m * m)
    (Expr.eval_mul (Expr.eval_reg_of_eq h2) (Expr.eval_reg_of_eq h2) (by omega)) ?_
  refine runs_seq_assign_le (v := 2) (Expr.eval_const (by omega)) ?_
  have hE0 : EdgeState n m []
      ⟨st₁.mem, Function.update (Function.update st₁.regs 3 (m * m)) 4 2, st₁.pos⟩ := by
    refine ⟨?_, ?_, ?_, ?_, listAt_nil _ _⟩
    · simp only [Function.update_of_ne (show (1 : ℕ) ≠ 4 by decide),
        Function.update_of_ne (show (1 : ℕ) ≠ 3 by decide)]; exact h1
    · simp only [Function.update_of_ne (show (2 : ℕ) ≠ 4 by decide),
        Function.update_of_ne (show (2 : ℕ) ≠ 3 by decide)]; exact h2
    · simp only [Function.update_of_ne (show (3 : ℕ) ≠ 4 by decide), Function.update_self]
    · simp
  refine runs_seq_triple_le (coreLoop_triple explicitProgram hm1 hN hW) hE0 ?_
  intro st₂ hE2
  refine runs_seq_triple_le (pendLoop_triple explicitProgram hN hW) hE2 ?_
  intro st₃ ⟨h31, _, _, h34, hmem3⟩
  set E := coreEdges m ++ pendEdges (m * m) (n - m * m) with hE
  have hlenE : E.length ≤ 4 * (m * m) + (n - m * m) := by
    have := length_coreUpTo m (m * m)
    simp only [hE, List.length_append, pendEdges, List.length_map, List.length_range]
    exact Nat.add_le_add_right this _
  refine runs_seq_store_le (x := 0) (v := n) (Expr.eval_const (by omega))
    (Expr.eval_reg_of_eq h31) ?_
  refine runs_seq_store_le (x := 1) (v := E.length) (Expr.eval_const (by omega))
    (Expr.eval_eq_of_eq (Expr.eval_div (Expr.eval_sub (Expr.eval_reg_of_eq h34)
      (Expr.eval_const (by omega)) (by omega)) (Expr.eval_const (by omega)) (by omega))
      (by omega)) ?_
  have hencode : (explicitGraph n).encode = n :: E.length :: flatE E := rfl
  have hlen : (explicitGraph n).encode.length = 2 + 2 * E.length := by
    rw [hencode]; simp [flatE_length]; ring
  refine runs_ret_le (Expr.eval_reg_of_eq h34) ⟨?_, ?_⟩ ?_
  · rw [hlen]
  · rw [hencode, listAt_cons, listAt_cons]
    refine ⟨?_, ?_, ?_⟩
    · simp only [Function.update_of_ne (show (0 : ℕ) ≠ 1 by decide), Function.update_self]
    · simp only [Function.update_self]
    · exact (hmem3.update_lt (by omega)).update_lt (by omega)
  · simp only [Expr.size]
    omega

/-- The program has no `rand` statement. -/
theorem explicitProgram_isDeterministic : explicitProgram.IsDeterministic := by
  intro s hs
  simp only [explicitProgram, List.mem_singleton] at hs
  subst hs
  simp [mainBody, sqrtLoop, forRange, forUp, coreBody, pendBody, emitStmt, Stmt.NoRand]

private lemma word_bound (n : ℕ) : 16 * n + 48 < 2 ^ wordSize 4 [n] := by
  have h := pow_lt_two_pow_wordSize (c := 4) (by norm_num) [n]
  simp only [List.length_singleton, List.foldr_cons, List.foldr_nil, Nat.max_def] at h
  split_ifs at h with hn
  · have : n = 0 := by omega
    subst this
    norm_num at h ⊢
    omega
  · have h3 : 27 ≤ (1 + n + 2) ^ 3 := by
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ (1 + n + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have : 16 * n + 48 ≤ (1 + n + 2) ^ 4 := by
      rw [pow_succ]
      nlinarith
    omega

/-- **[CGLNPS21], Theorem 2.4**, proved: there is an explicit expander, with `α₀ = 1/12`, word size
constant `4` and time constant `400`. -/
theorem explicitExpander : Cited.ExplicitExpander := by
  refine ⟨alpha0, explicitProgram, 4, 400, by norm_num [alpha0], fun n hn ω => ?_⟩
  have hW := word_bound n
  obtain ⟨o, st', c, hrun, ⟨ho, hout⟩, hc⟩ := mainBody_runs (w := wordSize 4 [n]) hn.le hW ω
  subst ho
  refine ⟨(explicitGraph n).encode, c + 2,
    runsTo_of_entry (body := mainBody) rfl (by simp only [List.length_singleton]; omega) hrun
      rfl hout,
    ⟨explicitGraph n, rfl, explicitGraph_spec n hn⟩, ?_⟩
  have : c + 2 ≤ 400 * n := by omega
  exact_mod_cast this

end MinCostFlow.ExplicitExpander
