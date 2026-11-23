module

public import MinCostFlow.LowStretch.ProgPLoop
public import MinCostFlow.LowStretch.ProgAmort

/-!
# The loop of the petal search, with an amortized cost

`psLoop_spec` bounds the cost of the loop by the measure `μ` of its first state. Here the bound
is the drop of `μ`: the cost plus the measure `μ a` of the last state before the final call is at
most `μ a₀` plus the cost of that call plus a constant (`psLoop_amort`). It holds for each bit
stream `ω`, as a run.

The ghost value is `Sum.inl a` while `pstep` returns `1`, and `Sum.inr r` after the final call,
where `r` is what is left of the budget.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

section Loop

variable {w : ℕ} {α : Type} (A : List ℕ) (Xf : α → PSG) (Ψ : α → (ℕ → ℕ) → Prop) (μ : α → ℕ)

/-- The invariant. After the final call, the last state `a` met `Ψ` and `μ a` is at most what is
left plus the cost of the final call. -/
def PLA : α ⊕ ℕ → State → Prop
  | .inl a, st => (∀ i < 32, st.regs i = A.getD i 0) ∧ st.regs 32 = 1 ∧ Ψ a st.mem
  | .inr r, st => (∀ i < 32, st.regs i = A.getD i 0) ∧ st.regs 32 ≠ 1 ∧
      ∃ a mem, Ψ a mem ∧ (Xf a).Post mem w (st.regs 32) st.mem ∧ μ a ≤ r + pstepCost A mem

/-- The measure. -/
def plaM : α ⊕ ℕ → ℕ
  | .inl a => μ a + 1
  | .inr _ => 0

/-- The budget. -/
def plaR : α ⊕ ℕ → ℕ
  | .inl a => μ a + 100
  | .inr r => r + 10

/-- **The loop, amortized.** -/
theorem psLoop_amort {p : Program} {bPS : ℕ} (hPS : MeetsContract w p bPS (pstepC w))
    (hw1 : 1 < 2 ^ w) (hlen : A.length = 32) (hwA : ∀ x ∈ A, x < 2 ^ w)
    (hargs : ∀ a, (Xf a).args = A)
    (hpre : ∀ a mem, Ψ a mem → (Xf a).Pre mem w)
    (hpay : ∀ a mem, Ψ a mem → pstepCost A mem ≤ μ a)
    (hstep : ∀ a mem mem', Ψ a mem → (Xf a).Post mem w 1 mem' →
      ∃ a', Ψ a' mem' ∧ μ a' + pstepCost A mem + 50 ≤ μ a)
    (ω : ℕ → Bool) (a₀ : α) (st : State) (hI : PLA (w := w) A Xf Ψ μ (.inl a₀) st) :
    ∃ o st' c, Runs w p ω (psLoop bPS) st o st' c ∧
      ∃ r, (o = .normal ∧ PLA (w := w) A Xf Ψ μ (.inr r) st') ∧ c + r ≤ μ a₀ + 100 := by
  refine runs_loop_amort (Fin := fun o st r => o = .normal ∧ PLA (w := w) A Xf Ψ μ (.inr r) st)
    (plaM μ) (plaR μ) (condVal := fun st => if st.regs 32 = 1 then 1 else 0) ?_ ?_ ?_ (.inl a₀)
    st hI
  · intro a st _
    simp only [Expr.eval, if_pos hw1, BinOp.eval_eq]
    split_ifs <;> simp_all
  · intro a st hI h0
    cases a with
    | inr r => exact ⟨r, ⟨rfl, hI⟩, by simp only [Expr.size, plaR]; omega⟩
    | inl x => simp [hI.2.1] at h0
  · intro a st hI hne
    cases a with
    | inr r => exact absurd hne (by beta_reduce; simp [hI.2.1])
    | inl x =>
      obtain ⟨hregs, -, hx⟩ := hI
      have hev : evalArgs w st (regsFrom 0 32) = some A := by
        rw [← hlen]; exact evalArgs_regsFrom A 0 fun i hi => by rw [Nat.zero_add]; exact hregs i (by omega)
      have hpr : (pstepC w).pre A st.mem := ⟨Xf x, (hargs x).symm, hpre x _ hx⟩
      obtain ⟨st', c, v, hrun, hpost, hr, hother, hcost⟩ :=
        runs_call_of_meetsContract (r := 32) hPS hev hwA hpr ω
      have hp := hpost (Xf x) ⟨(hargs x).symm, hpre x _ hx⟩
      have hc : (pstepC w).cost A st.mem = pstepCost A st.mem := rfl
      rw [hc, argsSize_regsFrom] at hcost
      have hregs' : ∀ i < 32, st'.regs i = A.getD i 0 := fun i hi => by
        rw [hother i (by omega)]; exact hregs i hi
      refine ⟨.normal, st', c, hrun, ?_⟩
      by_cases hv : v = 1
      · subst hv
        obtain ⟨x', hx', hpot⟩ := hstep x _ _ hx hp
        refine ⟨.inl x', ⟨hregs', hr, hx'⟩, by simp only [plaM]; omega, ?_⟩
        simp only [plaR, Expr.size]
        omega
      · have := hpay x _ hx
        refine ⟨.inr (μ x - pstepCost A st.mem), ⟨hregs', by rw [hr]; exact hv, x, st.mem, hx,
          by rw [hr]; exact hp, by omega⟩, by simp [plaM], ?_⟩
        simp only [plaR, Expr.size]
        omega

end Loop

end MinCostFlow.LowStretch
