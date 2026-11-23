module

public import WordRAM.Logic

/-!
# A register frame rule

A statement that writes only registers below `n` (in its assignments, random draws and calls)
leaves every register `r ≥ n` unchanged. The scan of `Delete` keeps its loop counter in
registers `25` and up, and the failure step writes only registers below `25`, so this rule
carries the counter across the failure step.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- `s` writes only registers below `n`. -/
def Stmt.WritesBelow (n : ℕ) : Stmt → Prop
  | .nop => True
  | .assign r _ => r < n
  | .store _ _ => True
  | .rand r => r < n
  | .seq s t => Stmt.WritesBelow n s ∧ Stmt.WritesBelow n t
  | .cond _ s t => Stmt.WritesBelow n s ∧ Stmt.WritesBelow n t
  | .loop _ body => Stmt.WritesBelow n body
  | .call r _ _ => r < n
  | .ret _ => True

theorem exec_regs_of_writesBelow {w : ℕ} {p : Program} {ω : ℕ → Bool} {n : ℕ} :
    ∀ (fuel : ℕ) (s : Stmt) (st : State) {o : Outcome} {st' : State} {c : ℕ},
      Stmt.WritesBelow n s → exec w p ω fuel s st = some (o, st', c) →
      ∀ r, n ≤ r → st'.regs r = st.regs r
  | 0, _, _, _, _, _, _, h, _, _ => by simp [exec] at h
  | fuel + 1, s, st, o, st', c, hs, h, r, hr => by
    cases s with
    | nop => simp [exec] at h; rw [← h.2.1]
    | assign r' e =>
      simp only [exec] at h
      split at h
      · simp at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.2.1]
        simp only [Stmt.WritesBelow] at hs
        simp [Function.update_apply, show r ≠ r' by omega]
    | store a e =>
      simp only [exec] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.2.1]
      · simp at h
    | rand r' =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2.1]
      simp only [Stmt.WritesBelow] at hs
      simp [Function.update_apply, show r ≠ r' by omega]
    | seq s t =>
      simp only [exec] at h
      obtain ⟨hs1, hs2⟩ := hs
      split at h
      · simp at h
      · rename_i v st1 c1 heq
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.2.1]
        exact exec_regs_of_writesBelow fuel s st hs1 heq r hr
      · rename_i st1 c1 heq
        split at h
        · simp at h
        · rename_i o2 st2 c2 heq2
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.2.1, exec_regs_of_writesBelow fuel t st1 hs2 heq2 r hr,
            exec_regs_of_writesBelow fuel s st hs1 heq r hr]
    | cond e s t =>
      simp only [exec] at h
      obtain ⟨hs1, hs2⟩ := hs
      split at h
      · simp at h
      · rename_i v _
        split at h
        · simp at h
        · rename_i o1 st1 c1 heq
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.2.1]
          by_cases hv : v = 0
          · rw [if_pos hv] at heq; exact exec_regs_of_writesBelow fuel t st hs2 heq r hr
          · rw [if_neg hv] at heq; exact exec_regs_of_writesBelow fuel s st hs1 heq r hr
    | loop e body =>
      simp only [exec] at h
      split at h
      · simp at h
      · rename_i v _
        split_ifs at h with hv
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.2.1]
        · split at h
          · simp at h
          · rename_i u st1 c1 heq
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            rw [← h.2.1]
            exact exec_regs_of_writesBelow fuel body st hs heq r hr
          · rename_i st1 c1 heq
            split at h
            · simp at h
            · rename_i o2 st2 c2 heq2
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              rw [← h.2.1, exec_regs_of_writesBelow fuel (.loop e body) st1 hs heq2 r hr,
                exec_regs_of_writesBelow fuel body st hs heq r hr]
    | call r' f args =>
      simp only [exec] at h
      split at h
      · split at h
        · simp at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.2.1]
          simp only [Stmt.WritesBelow] at hs
          simp [Function.update_apply, show r ≠ r' by omega]
      · simp at h
    | ret e =>
      simp only [exec] at h
      split at h
      · simp at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.2.1]

/-- **The register frame rule.** -/
theorem Triple.regs_frame {w : ℕ} {p : Program} {P : State → Prop} {s : Stmt}
    {Q : Outcome → State → Prop} {T : State → ℕ} {n : ℕ} (hs : Stmt.WritesBelow n s)
    (ht : Triple w p P s Q T) (R : ℕ → ℕ) :
    Triple w p (fun st => P st ∧ ∀ r, n ≤ r → st.regs r = R r) s
      (fun o st' => Q o st' ∧ ∀ r, n ≤ r → st'.regs r = R r) T := by
  intro st ω hst
  obtain ⟨o, st', c, ⟨fuel, hrun⟩, hq, hc⟩ := ht st ω hst.1
  exact ⟨o, st', c, ⟨fuel, hrun⟩, ⟨hq, fun r hr =>
    (exec_regs_of_writesBelow fuel s st hs hrun r hr).trans (hst.2 r hr)⟩, hc⟩

end MinCostFlow.HierPaths

end
