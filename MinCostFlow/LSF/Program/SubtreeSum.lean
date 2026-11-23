module

public import MinCostFlow.LSF.Program.SubtreeSumMath
public import MinCostFlow.LSF.Program.Utils
import Mathlib.Tactic.Linarith

/-!
# The subtree-sum procedure

`subtreeSumProc` replaces, for every vertex index `y < n`, the `K`-limb block at
`dPtr + y K` by the sum of the blocks of all descendants of `y`, modulo the capacity of a block.
It walks the top-down order `Q` from the back and adds the block of each `x = Q[k]`, `k ≥ 1`,
into the block of its parent (`SubtreeSumMath.lean` explains why this gives subtree sums).
The cost is `O(n K)`.

The parents and depths are read from memory, at `parPtr` and `depPtr`, so the result is stated
for the arrays `fun x => mem (parPtr + x)` and `fun x => mem (depPtr + x)`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow.Num

@[expose] public section

/-- One step: add the block of `x = Q[k]` (register `6` is `k`) into the block of its parent. -/
def subtreeSumBody (bAdd : ℕ) : Stmt :=
  .assign 7 (.load (.bin .add (.reg 1) (.reg 6))) ;;
  .assign 8 (.load (.bin .add (.reg 2) (.reg 7))) ;;
  .call 9 bAdd [.bin .add (.reg 4) (.bin .mul (.reg 8) (.reg 5)),
    .bin .add (.reg 4) (.bin .mul (.reg 7) (.reg 5)), .reg 5] ;;
  .assign 6 (.bin .sub (.reg 6) (.const 1))

/-- Args: `[n, qOrdPtr, parPtr, depPtr, dPtr, K]`. -/
def subtreeSumProc (bAdd : ℕ) : Stmt :=
  .assign 6 (.bin .sub (.reg 0) (.const 1)) ;;
  .loop (.reg 6) (subtreeSumBody bAdd) ;;
  .ret (.const 0)

lemma subtreeSumProc_noRand (bAdd : ℕ) : (subtreeSumProc bAdd).NoRand := by
  simp [subtreeSumProc, subtreeSumBody, Stmt.NoRand]

/-- The contract of `subtreeSumProc`. -/
def subtreeSumContract (w h : ℕ) : Contract where
  pre args mem := ∃ (n qOrdPtr parPtr depPtr dPtr K tM r : ℕ) (tl hd pe : ℕ → ℕ) (Q : List ℕ),
    args = [n, qOrdPtr, parPtr, depPtr, dPtr, K] ∧ 0 < h ∧ 2 * h + 2 ≤ w ∧ 0 < n ∧
    RootedArrays n tM r tl hd (fun x => mem (parPtr + x)) pe (fun x => mem (depPtr + x)) ∧
    TopDownOrder n r (fun x => mem (parPtr + x)) Q ∧ ListAt mem qOrdPtr Q ∧
    qOrdPtr + n ≤ dPtr ∧ parPtr + n ≤ dPtr ∧ depPtr + n ≤ dPtr ∧ dPtr + n * K < 2 ^ w ∧
    ∀ y < n, Valid mem (dPtr + y * K) h K
  post args mem ret mem' := ∃ (n qOrdPtr parPtr depPtr dPtr K : ℕ),
    args = [n, qOrdPtr, parPtr, depPtr, dPtr, K] ∧ ret = 0 ∧
    (∀ a, a < dPtr ∨ dPtr + n * K ≤ a → mem' a = mem a) ∧
    ∀ y < n, Valid mem' (dPtr + y * K) h K ∧
      (unsignedVal mem' (dPtr + y * K) h K : ℤ) % (capacity h K : ℤ) =
        (open Classical in ∑ z ∈ Finset.range n,
          if AncOf (fun x => mem (parPtr + x)) (fun x => mem (depPtr + x)) y z then
            (unsignedVal mem (dPtr + z * K) h K : ℤ) else 0) % (capacity h K : ℤ)
  cost args _ := args.getD 0 0 * (55 * args.getD 5 0 + 80) + 20

/-- Blocks of different indices are disjoint. -/
private lemma block_disj {a b K : ℕ} (hab : a ≠ b) (d : ℕ) :
    d + a * K + K ≤ d + b * K ∨ d + b * K + K ≤ d + a * K := by
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · left; have := Nat.mul_le_mul_right K (show a + 1 ≤ b by omega); nlinarith
  · right; have := Nat.mul_le_mul_right K (show b + 1 ≤ a by omega); nlinarith

private lemma block_end {a n K : ℕ} (ha : a < n) : a * K + K ≤ n * K := by
  have := Nat.mul_le_mul_right K (show a + 1 ≤ n by omega); nlinarith

theorem subtreeSum_meetsContract {w h : ℕ} {p : Program} {b bAdd : ℕ}
    (hp : p.procs[b]? = some (subtreeSumProc bAdd))
    (hAdd : MeetsContract w p bAdd (addToContract w h)) :
    MeetsContract w p b (subtreeSumContract w h) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, qOrdPtr, parPtr, depPtr, dPtr, K, tM, r, tl, hd, pe, Q, rfl, hh, hw2, hn, hR, hQ,
    hQat, hqd, hpd, hdd, hdW, hval⟩ := hpre
  set args := [n, qOrdPtr, parPtr, depPtr, dPtr, K] with hargs
  set par : ℕ → ℕ := fun x => mem (parPtr + x) with hpar
  set dep : ℕ → ℕ := fun x => mem (depPtr + x) with hdep
  set cap : ℤ := (capacity h K : ℤ) with hcap
  have hw1 : 1 < 2 ^ w := by have := Nat.one_lt_two_pow_iff.mpr (show w ≠ 0 by omega); omega
  have hKw : K < 2 ^ w := hwords K (by simp [hargs])
  let D₀ : ℕ → ℤ := fun z => (unsignedVal mem (dPtr + z * K) h K : ℤ)
  -- the loop invariant: positions above `k` are processed
  let Inv : ℕ → State → Prop := fun k st =>
    (∀ i < 6, st.regs i = args.getD i 0) ∧ st.regs 6 = k ∧ k < n ∧
    (∀ a, a < dPtr ∨ dPtr + n * K ≤ a → st.mem a = mem a) ∧
    ∀ y < n, Valid st.mem (dPtr + y * K) h K ∧
      (unsignedVal st.mem (dPtr + y * K) h K : ℤ) % cap =
        stageSum par dep Q n D₀ (k + 1) y % cap
  have hloop : ∀ k₀, Triple w p (Inv k₀) (.loop (.reg 6) (subtreeSumBody bAdd))
      (normalPost (Inv 0)) (fun _ => (55 * K + 80) * k₀ + 3) := by
    intro k₀
    refine Triple.loop_inv (Inv := Inv) (condVal := fun st => st.regs 6) (fun k => k)
      (fun k => (55 * K + 80) * k + 3) ?_ ?_ ?_ k₀
    · intro k st _; eval_expr
    · rintro k st hI h0
      rw [hI.2.1] at h0; subst h0
      exact ⟨hI, by simp⟩
    · rintro k st ⟨hregs, h6, hkn, hfr, hD⟩ hne
      rw [h6] at hne
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      refine ⟨55 * K + 78, ?_⟩
      intro s ω' hs; subst s
      have r1 : st.regs 1 = qOrdPtr := hregs 1 (by omega)
      have r2 : st.regs 2 = parPtr := hregs 2 (by omega)
      have r4 : st.regs 4 = dPtr := hregs 4 (by omega)
      have r5 : st.regs 5 = K := hregs 5 (by omega)
      have hkQ : k' + 1 < Q.length := by rw [hQ.len]; exact hkn
      set x := Q[k' + 1] with hx
      have hxn : x < n := hQ.lt x (List.getElem_mem _)
      have hxr : x ≠ r := by
        intro h
        have h0 := hQ.head_eq hn
        rw [← h0, hx] at h
        have := (hQ.nodup.getElem_inj_iff).mp h
        omega
      have hmx : st.mem (qOrdPtr + (k' + 1)) = x := by
        rw [hfr _ (Or.inl (by omega))]; exact hQat _ hkQ
      have hpn : par x < n := hR.par_lt x hxn
      have hmp : st.mem (parPtr + x) = par x := hfr _ (Or.inl (by omega))
      have hpx : par x ≠ x := by
        intro h
        have := (hR.step x hxn hxr).2.2
        rw [h] at this; omega
      have hbx := block_end (K := K) hxn
      have hbp := block_end (K := K) hpn
      have hqw : qOrdPtr + (k' + 1) < 2 ^ w := by omega
      have hpw : parPtr + x < 2 ^ w := by omega
      have hm1 : x * K < 2 ^ w := by omega
      have hm2 : par x * K < 2 ^ w := by omega
      refine runs_start_le ?_
      unfold subtreeSumBody
      refine runs_seq_assign_le (v := x) (by rw [← hmx]; eval_expr) ?_
      refine runs_seq_assign_le (v := par x) (by rw [← hmp]; eval_expr) ?_
      refine runs_seq_call_le (vs := [dPtr + par x * K, dPtr + x * K, K]) hAdd
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
          (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))
        (by
          intro v hv
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl <;> omega)
        ⟨dPtr + par x * K, dPtr + x * K, K, rfl, hh, hw2, by omega, by omega,
          by have := block_disj hpx dPtr (K := K); omega, (hD _ hpn).1, (hD _ hxn).1⟩ ?_
      rintro v mem₁ pos₁ ⟨dst, src, L, heq, -, hv1, hu1, -, hfr1⟩
      simp only [List.cons.injEq, and_true] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      refine runs_assign_le (v := k') (by show _ = some (k' + 1 - 1); eval_expr) ⟨k', ⟨?_, by simp,
        by omega, ?_, ?_⟩, by omega, ?_⟩ ?_
      · intro i hi
        simp only [Function.update_of_ne (show i ≠ 6 by omega),
          Function.update_of_ne (show i ≠ 9 by omega), Function.update_of_ne (show i ≠ 8 by omega),
          Function.update_of_ne (show i ≠ 7 by omega)]
        exact hregs i hi
      · intro a ha
        dsimp only
        rw [hfr1 a (by rcases ha with ha | ha <;> [left; right] <;> omega)]
        exact hfr a ha
      · intro y hy
        have hstep := stageSum_step hR hQ D₀ (k := k' + 1) (by omega) hkQ y
        by_cases hyp : y = par x
        · subst hyp
          dsimp only
          refine ⟨hv1, ?_⟩
          rw [hu1, Int.natCast_emod, hstep, if_pos rfl]
          push_cast
          rw [Int.emod_emod_of_dvd _ (dvd_refl _), Int.add_emod, (hD _ hpn).2, (hD _ hxn).2,
            ← Int.add_emod]
        · have hdisj := block_disj hyp dPtr (K := K)
          have hagree : ∀ i < K, mem₁ (dPtr + y * K + i) = st.mem (dPtr + y * K + i) :=
            fun i hi => hfr1 _ (by omega)
          dsimp only
          refine ⟨fun i hi => by rw [hagree i hi]; exact (hD y hy).1 i hi, ?_⟩
          rw [unsignedVal_congr (a' := dPtr + y * K) (mem' := st.mem) hagree, (hD y hy).2,
            hstep, if_neg hyp, add_zero]
      · simp only [Expr.size_reg, Expr.size_const, Expr.size_bin, Expr.size_load]
        ring_nf; omega
      · simp [argsSize, addToContract, Expr.size]
        omega
  -- the whole procedure
  have hR0 : ∀ i < 6, (startState args mem pos).regs i = args.getD i 0 := by
    intro i hi
    interval_cases i <;> simp [startState, hargs]
  refine runs_start_le ?_
  unfold subtreeSumProc
  refine runs_seq_assign_le (v := n - 1) (by
    have := hR0 0 (by omega); eval_expr) ?_
  refine runs_seq_triple_le (hloop (n - 1)) ⟨fun i hi => ?_, by simp, by omega,
    fun a _ => rfl, fun y hy => ⟨hval y hy, ?_⟩⟩ ?_
  · simp only [Function.update_of_ne (show i ≠ 6 by omega)]; exact hR0 i hi
  · rw [show n - 1 + 1 = n by omega, stageSum_last hR hQ D₀ hy]; rfl
  rintro st ⟨-, -, -, hfr, hD⟩
  refine runs_ret_le (v := 0) (by eval_expr) ⟨n, qOrdPtr, parPtr, depPtr, dPtr, K, rfl, rfl, hfr,
    fun y hy => ⟨(hD y hy).1, ?_⟩⟩ ?_
  · rw [(hD y hy).2, stageSum_one hR hQ hn D₀ y]
  · simp only [subtreeSumContract, hargs, List.getD_cons_zero, List.getD_cons_succ,
      Expr.size_const, Expr.size_reg, Expr.size_bin]
    have hmul : (55 * K + 80) * (n - 1) + (55 * K + 80) = n * (55 * K + 80) := by
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; ring
    omega

end

end MinCostFlow.LSF.Program
