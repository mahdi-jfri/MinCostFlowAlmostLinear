module

public import WordRAM.Contract

/-!
# Deterministic procedure executions do not depend on the random tape

The scaling layer runs a bounded circulation procedure in a canonical memory
region. Once that starting state is fixed, a program without random statements
has the same execution on every tape. This is the tape-independence fact needed
to compare a relocated execution with the selected canonical execution.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Changing the random tape does not change execution of a statement without
random instructions in a deterministic program. -/
theorem exec_eq_of_deterministic {w : ℕ} {p : Program} (hp : p.IsDeterministic)
    (ω ω' : ℕ → Bool) :
    ∀ fuel s st, s.NoRand → exec w p ω fuel s st = exec w p ω' fuel s st := by
  intro fuel
  induction fuel with
  | zero => intro s st _; rfl
  | succ n ih =>
    intro s st hs
    cases s with
    | nop => rfl
    | assign r e => rfl
    | store a e => rfl
    | rand r => exact hs.elim
    | ret e => rfl
    | seq s t =>
      have ht : ∀ st', exec w p ω n t st' = exec w p ω' n t st' := fun st' => ih t st' hs.2
      simp only [exec, ih s st hs.1, ht]
    | cond e s t =>
      have hb : ∀ v, exec w p ω n (if v = 0 then t else s) st =
          exec w p ω' n (if v = 0 then t else s) st := by
        intro v
        by_cases hv : v = 0
        · simpa only [hv, ↓reduceIte] using ih t st hs.2
        · simpa only [hv, ↓reduceIte] using ih s st hs.1
      simp only [exec, hb]
    | loop e body =>
      have hb : ∀ st', exec w p ω n body st' = exec w p ω' n body st' :=
        fun st' => ih body st' hs
      have hl : ∀ st', exec w p ω n (.loop e body) st' = exec w p ω' n (.loop e body) st' :=
        fun st' => ih (.loop e body) st' hs
      simp only [exec, hb, hl]
    | call r f args =>
      rcases hv : evalArgs w st args with _ | vs <;> rcases hf : p.procs[f]? with _ | body
      · simp only [exec, hv, hf]
      · simp only [exec, hv, hf]
      · simp only [exec, hv, hf]
      · have hb : ∀ st', exec w p ω n body st' = exec w p ω' n body st' :=
          fun st' => ih body st' (hp body (List.mem_of_getElem? hf))
        simp only [exec, hv, hf, hb]

/-- The same deterministic body run can be used on any random tape. -/
theorem runs_of_deterministic {w : ℕ} {p : Program} (hp : p.IsDeterministic)
    {ω ω' : ℕ → Bool} {s : Stmt} {st st' : State} {o : Outcome} {cost : ℕ}
    (hs : s.NoRand) (hr : Runs w p ω s st o st' cost) : Runs w p ω' s st o st' cost := by
  obtain ⟨fuel, hf⟩ := hr
  exact ⟨fuel, (exec_eq_of_deterministic hp ω' ω fuel s st hs).trans hf⟩

end MinCostFlow.Scaling.Machine
