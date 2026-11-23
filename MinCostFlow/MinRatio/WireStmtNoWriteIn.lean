module

public import MinCostFlow.MinRatio.WireShiftDeepPhases
import WordRAM.Tactic

/-!
# Statements that never write a given set of registers (`WireStmtNoWriteIn`)

A run lemma often says only which high registers a part keeps. When a later part reads a low
register that an earlier part does not touch, we need the fact from the program text. The
predicate `stmtNoWriteIn S s` says that `s` has no assignment, call or random draw into a
register of `S`. `runs_regs_of_noWriteIn` turns it into the fact that every run of `s` keeps the
registers of `S`. This is `runs_regs_ge_of_noWriteGe` (`WireChainCoreSyncDefs.lean`) for any set.

* `collectLSFForestsLoop_noWriteIn`: the forest collection loop writes only the registers
  `2, 3, 4, 5, 6, 19`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- The statement `s` never writes a register of the set `S`. -/
@[expose] def stmtNoWriteIn (S : ℕ → Prop) : Stmt → Prop
  | .nop => True
  | .assign r _ => ¬ S r
  | .store _ _ => True
  | .seq s₁ s₂ => stmtNoWriteIn S s₁ ∧ stmtNoWriteIn S s₂
  | .cond _ s₁ s₂ => stmtNoWriteIn S s₁ ∧ stmtNoWriteIn S s₂
  | .loop _ s => stmtNoWriteIn S s
  | .call r _ _ => ¬ S r
  | .ret _ => True
  | .rand r => ¬ S r

/-- Every run of a statement that never writes a register of `S` keeps those registers. -/
theorem runs_regs_of_noWriteIn {w : ℕ} {S : ℕ → Prop} {p : Program} {ω : ℕ → Bool}
    {s : Stmt} {st out : State} {o : Outcome} {c : ℕ}
    (hr : Runs w p ω s st o out c) (hnw : stmtNoWriteIn S s) :
    ∀ r, S r → out.regs r = st.regs r := by
  obtain ⟨f, hf⟩ := hr
  revert hnw
  induction f generalizing s st out o c with
  | zero => simp [exec] at hf
  | succ f ih =>
    intro hnw
    cases s with
    | nop => simp [exec] at hf; rcases hf with ⟨_, rfl, _⟩; intro _ _; rfl
    | assign reg e =>
      dsimp only [stmtNoWriteIn] at hnw
      simp only [exec] at hf
      cases he : e.eval w st <;> simp [he] at hf
      rcases hf with ⟨_, rfl, _⟩
      intro r hr
      exact Function.update_of_ne (fun h => hnw (by rw [← h]; exact hr)) _ _
    | store a e =>
      simp only [exec] at hf
      cases ha : a.eval w st <;> simp [ha] at hf
      cases he : e.eval w st <;> simp [he] at hf
      rcases hf with ⟨_, rfl, _⟩; intro _ _; rfl
    | rand reg =>
      dsimp only [stmtNoWriteIn] at hnw
      simp only [exec] at hf; rcases hf with ⟨_, rfl, _⟩
      intro r hr
      exact Function.update_of_ne (fun h => hnw (by rw [← h]; exact hr)) _ _
    | ret e =>
      simp only [exec] at hf
      cases he : e.eval w st <;> simp [he] at hf
      rcases hf with ⟨_, rfl, _⟩; intro _ _; rfl
    | seq s₁ s₂ =>
      simp only [exec] at hf
      cases h1 : exec w p ω f s₁ st with
      | none => simp [h1] at hf
      | some res₁ =>
        rcases res₁ with ⟨o₁, st₁, c₁⟩; simp only [h1] at hf
        cases o₁ with
        | returned v => simp at hf; rcases hf with ⟨_, rfl, _⟩; exact ih h1 hnw.1
        | normal =>
          cases h2 : exec w p ω f s₂ st₁ with
          | none => simp [h2] at hf
          | some res₂ =>
            rcases res₂ with ⟨o₂, st₂, c₂⟩; simp [h2] at hf
            rcases hf with ⟨_, rfl, _⟩
            intro r hr; exact (ih h2 hnw.2 r hr).trans (ih h1 hnw.1 r hr)
    | cond e s₁ s₂ =>
      simp only [exec] at hf
      cases he : e.eval w st <;> simp [he] at hf
      rename_i v
      cases hbr : exec w p ω f (if v = 0 then s₂ else s₁) st with
      | none => simp [hbr] at hf
      | some res =>
        rcases res with ⟨o', st', c'⟩; simp [hbr] at hf
        rcases hf with ⟨_, rfl, _⟩
        split_ifs at hbr with hv
        · exact ih hbr hnw.2
        · exact ih hbr hnw.1
    | loop e body =>
      simp only [exec] at hf
      cases he : e.eval w st <;> simp [he] at hf
      rename_i v
      by_cases hv : v = 0
      · simp [hv] at hf; rcases hf with ⟨_, rfl, _⟩; intro _ _; rfl
      · simp only [hv, ↓reduceIte] at hf
        cases hb : exec w p ω f body st with
        | none => simp [hb] at hf
        | some res₁ =>
          rcases res₁ with ⟨o₁, st₁, c₁⟩; simp only [hb] at hf
          cases o₁ with
          | returned u => simp at hf; rcases hf with ⟨_, rfl, _⟩; exact ih hb hnw
          | normal =>
            cases hl : exec w p ω f (.loop e body) st₁ with
            | none => simp [hl] at hf
            | some res₂ =>
              rcases res₂ with ⟨o₂, st₂, c₂⟩; simp [hl] at hf
              rcases hf with ⟨_, rfl, _⟩
              intro r hr; exact (ih hl hnw r hr).trans (ih hb hnw r hr)
    | call reg fn args =>
      dsimp only [stmtNoWriteIn] at hnw
      simp only [exec] at hf
      cases ha : evalArgs w st args <;> simp [ha] at hf
      cases hp : p.procs[fn]? <;> simp [hp] at hf
      split at hf
      · cases hf
      · cases hf
        intro r hr
        exact Function.update_of_ne (fun h => hnw (by rw [← h]; exact hr)) _ _

/-- The forest collection loop writes only the registers `2, 3, 4, 5, 6, 19`. -/
theorem collectLSFForestsLoop_noWriteIn (readLSF dstReg : ℕ) :
    stmtNoWriteIn (fun r => r ≠ 2 ∧ r ≠ 3 ∧ r ≠ 4 ∧ r ≠ 5 ∧ r ≠ 6 ∧ r ≠ 19)
      (collectLSFForestsLoop readLSF dstReg) := by
  simp [collectLSFForestsLoop, forRange, forUp, ordCoreReadLSFStmt, stmtNoWriteIn]

end MinCostFlow.MinRatio

end
