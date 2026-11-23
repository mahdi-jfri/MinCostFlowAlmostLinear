module

public import MinCostFlow.LowStretch.ProgPStep

/-!
# The loop of the petal search

The petal search calls `pstep` while it returns `1` (`psLoop`). Each call either tests a radius,
moves the bucket pointer, or runs one step of Dijkstra. The loop ends when a radius passes (the
result is the radius plus `2`) or the queue is empty (the result is `0`).

This file proves the loop for any invariant `Ψ` of the ghost values that `pstep` keeps
(`psLoop_spec`). The invariant of the actual search, and the proof that it is kept, come later.
The cost is paid by a potential `μ`: each call that returns `1` must lower it by at least the
cost of the call.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The registers `k, …, k + n - 1`. -/
def regsFrom : ℕ → ℕ → List Expr
  | _, 0 => []
  | k, n + 1 => .reg k :: regsFrom (k + 1) n

theorem argsSize_regsFrom (k n : ℕ) : argsSize (regsFrom k n) = n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => simp only [regsFrom, argsSize_cons, Expr.size, ih]; omega

/-- Reading the registers `k, …, k + |A| - 1` gives `A`. -/
theorem evalArgs_regsFrom {w : ℕ} {st : State} (A : List ℕ) (k : ℕ)
    (h : ∀ i < A.length, st.regs (k + i) = A.getD i 0) :
    evalArgs w st (regsFrom k A.length) = some A := by
  induction A generalizing k with
  | nil => rfl
  | cons a A ih =>
    have h0 := h 0 (by simp)
    have h1 : ∀ i < A.length, st.regs (k + 1 + i) = A.getD i 0 := fun i hi => by
      have := h (i + 1) (by simp; omega)
      rw [show k + (i + 1) = k + 1 + i by omega] at this
      simpa using this
    simp only [List.length_cons, regsFrom, evalArgs, Expr.eval, ih (k + 1) h1]
    simp only [Nat.add_zero, List.getD_cons_zero] at h0
    rw [h0]

/-- The loop of the petal search. Procedure `bPS` is `pstep`, and its result is in register
`32`. -/
def psLoop (bPS : ℕ) : Stmt :=
  .loop (.bin .eq (.reg 32) (.const 1)) (.call 32 bPS (regsFrom 0 32))

section Loop

variable {w : ℕ} {α : Type} (A : List ℕ) (Xf : α → PSG) (Ψ : α → (ℕ → ℕ) → Prop)

/-- The invariant of `psLoop`. The ghost value is `none` once `pstep` returned a value other
than `1`; then the last call started from a memory that met `Ψ`. -/
def PLI : Option α → State → Prop
  | some a, st => (∀ i < 32, st.regs i = A.getD i 0) ∧ st.regs 32 = 1 ∧ Ψ a st.mem
  | none, st => (∀ i < 32, st.regs i = A.getD i 0) ∧ st.regs 32 ≠ 1 ∧
      ∃ a mem, Ψ a mem ∧ (Xf a).Post mem w (st.regs 32) st.mem

/-- The measure of the loop. -/
def plm (μ : α → ℕ) : Option α → ℕ
  | some a => μ a + 1
  | none => 0

/-- The cost left in the loop. -/
def plrem (μ : α → ℕ) : Option α → ℕ
  | some a => μ a + 100
  | none => 10

theorem regs_upd32 {st : State} {v : ℕ} (hR : ∀ i < 32, st.regs i = A.getD i 0) :
    ∀ i < 32, Function.update st.regs 32 v i = A.getD i 0 :=
  fun i hi => by rw [Function.update_of_ne (by omega), hR i hi]

/-- **The loop.** If `Ψ` gives the precondition of `pstep`, pays for each call, and is kept by
each call that returns `1`, then the loop ends after a call that returns another value. -/
theorem psLoop_spec {p : Program} {bPS : ℕ} (hPS : MeetsContract w p bPS (pstepC w))
    (μ : α → ℕ) (hw1 : 1 < 2 ^ w) (hlen : A.length = 32) (hwA : ∀ x ∈ A, x < 2 ^ w)
    (hargs : ∀ a, (Xf a).args = A)
    (hpre : ∀ a mem, Ψ a mem → (Xf a).Pre mem w)
    (hpay : ∀ a mem, Ψ a mem → pstepCost A mem ≤ μ a)
    (hstep : ∀ a mem mem', Ψ a mem → (Xf a).Post mem w 1 mem' →
      ∃ a', Ψ a' mem' ∧ μ a' + pstepCost A mem + 50 ≤ μ a)
    (x0 : Option α) :
    Triple w p (PLI (w := w) A Xf Ψ x0) (psLoop bPS) (normalPost (PLI (w := w) A Xf Ψ none))
      (fun _ => plrem μ x0) := by
  refine Triple.loop_inv (plm μ) (plrem μ)
    (condVal := fun st => if st.regs 32 = 1 then 1 else 0) ?_ ?_ ?_ x0
  · intro a st _
    simp only [Expr.eval, if_pos hw1, BinOp.eval_eq]
    split_ifs <;> simp_all
  · intro a st hI h0
    cases a with
    | none => exact ⟨hI, by simp [Expr.size, plrem]⟩
    | some x => simp [hI.2.1] at h0
  · intro a st hI hne
    cases a with
    | none => exact absurd hne (by beta_reduce; simp [hI.2.1])
    | some x =>
      obtain ⟨hregs, -, hx⟩ := hI
      refine ⟨pstepCost A st.mem + 33, ?_⟩
      intro st' ω hst
      subst hst
      have hev : evalArgs w st' (regsFrom 0 32) = some A := by
        rw [← hlen]; exact evalArgs_regsFrom A 0 fun i hi => by rw [Nat.zero_add]; exact hregs i (by omega)
      have hpr : (pstepC w).pre A st'.mem := ⟨Xf x, (hargs x).symm, hpre x _ hx⟩
      refine runs_start_le (runs_call_le (k := 0) hPS hev hwA hpr fun v mem' pos' hpost => ?_)
      have hp := hpost (Xf x) ⟨(hargs x).symm, hpre x _ hx⟩
      have hc : (pstepC w).cost A st'.mem = pstepCost A st'.mem := rfl
      refine ⟨?_, by rw [hc, argsSize_regsFrom]; beta_reduce; omega⟩
      by_cases hv : v = 1
      · subst hv
        obtain ⟨x', hx', hpot⟩ := hstep x _ _ hx hp
        refine ⟨some x', ⟨regs_upd32 A hregs, by simp, hx'⟩, by simp only [plm]; omega, ?_⟩
        simp only [plrem, Expr.size]
        omega
      · refine ⟨none, ⟨regs_upd32 A hregs, by simpa using hv, x, st'.mem, hx, by simpa using hp⟩,
          by simp [plm], ?_⟩
        have := hpay x _ hx
        simp only [plrem, Expr.size]
        omega

end Loop

end MinCostFlow.LowStretch
