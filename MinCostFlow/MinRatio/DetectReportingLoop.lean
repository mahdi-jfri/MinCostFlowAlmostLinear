module

public import WordRAM.Logic

/-!
# Termination and amortized cost of Detect reporting

The proof of Theorem 5.1 (pages 29–30) charges the search and reset
work to the number of reported edges. Every successful round
removes one pending report. The final search exits the loop.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM

/-- Search, then report a nonzero slot or finish when search returns zero. -/
@[expose] def detectReportingLoop (search report finish : Stmt) : Stmt :=
  .loop (.const 1) (search ;; .cond (.reg 3) report finish)

/-- The loop body uses only the randomness behavior of its linked statements. -/
theorem detectReportingLoop_noRand {search report finish : Stmt}
    (hs : search.NoRand) (hr : report.NoRand) (hf : finish.NoRand) :
    (detectReportingLoop search report finish).NoRand := by
  simp [detectReportingLoop, Stmt.NoRand, hs, hr, hf]

/-- One successful round per pending report plus the final failed
search gives the loop cost. The tree potentials telescope across
rounds, even when the search chooses different ready slots. -/
theorem detectReportingLoop_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {search report finish : Stmt} {Inv : ℕ → ℕ → State → Prop}
    {Done : ℕ → ℕ → State → Prop}
    (hw : 1 < 2 ^ w) (stepBudget finalBudget : ℕ)
    (hstep : ∀ remaining potential st, Inv remaining potential st →
      ∃ outcome out cost,
        Runs w p ω (search ;; .cond (.reg 3) report finish) st outcome out cost ∧
        match outcome with
        | .normal => ∃ nextPotential, 0 < remaining ∧
            Inv (remaining - 1) nextPotential out ∧ cost + nextPotential ≤ stepBudget + potential
        | .returned ret => ∃ nextPotential, remaining = 0 ∧
            Done ret nextPotential out ∧ cost + nextPotential ≤ finalBudget + potential)
    {remaining potential : ℕ} {st : State} (hin : Inv remaining potential st) :
    ∃ ret out cost finalPotential,
      Runs w p ω (detectReportingLoop search report finish) st (.returned ret) out cost ∧
      Done ret finalPotential out ∧
      cost + finalPotential ≤ remaining * (stepBudget + 2) + finalBudget + 2 + potential := by
  induction remaining generalizing potential st with
  | zero =>
    obtain ⟨o, out, cost, hrun, hnext⟩ := hstep 0 potential st hin
    cases o with
    | normal => obtain ⟨_, hpos, _, _⟩ := hnext; omega
    | returned ret =>
      obtain ⟨phi, _, hdone, hcost⟩ := hnext
      refine ⟨ret, out, cost + 2, phi, ?_, hdone, by omega⟩
      exact runs_loop_iff.mpr (Or.inr (Or.inl
        ⟨1, ret, cost, by simp [Expr.eval, hw], by decide, hrun, rfl, by simp [Expr.size]; omega⟩))
  | succ k ih =>
    obtain ⟨o, next, cost, hrun, hnext⟩ := hstep (k + 1) potential st hin
    cases o with
    | returned ret => obtain ⟨_, hz, _, _⟩ := hnext; omega
    | normal =>
      obtain ⟨phi, _, hin', hcost⟩ := hnext
      have hinK : Inv k phi next := hin'
      obtain ⟨ret, out, rest, finalPhi, hrun', hdone, hrest⟩ := ih hinK
      refine ⟨ret, out, cost + rest + 2, finalPhi, ?_, hdone, ?_⟩
      · exact runs_loop_iff.mpr (Or.inr (Or.inr
          ⟨1, next, cost, rest, by simp [Expr.eval, hw], by decide, hrun, hrun',
            by simp [Expr.size]; omega⟩))
      · rw [Nat.succ_mul]
        omega

end MinCostFlow.MinRatio
