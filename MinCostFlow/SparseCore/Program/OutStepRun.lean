module

public import MinCostFlow.SparseCore.Program.OutSmallSideProg

/-!
# Run lemmas with opaque states

The proofs of the output step chain many statements. A run lemma that names the next state as a
record update (`{ st with regs := Function.update … }`) makes terms grow with each step. The
lemmas of this file give the next state as an opaque `st'`, with equations for its memory and its
registers, so that a long chain stays small. They cover an assignment, a store, a call, a
conditional and a return.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM

variable {w : ℕ} {p : Program} {ω : ℕ → Bool}

theorem step_assign {st : State} {r : ℕ} {e : Expr} {v : ℕ} (he : e.eval w st = some v) :
    ∃ st' : State, Runs w p ω (.assign r e) st .normal st' (e.size + 1) ∧ st'.mem = st.mem ∧
      st'.regs r = v ∧ ∀ j, j ≠ r → st'.regs j = st.regs j :=
  ⟨_, runs_assign_of he, rfl, by simp, fun j hj => by simp [Function.update_of_ne hj]⟩

theorem step_store {st : State} {a e : Expr} {x v : ℕ} (ha : a.eval w st = some x)
    (he : e.eval w st = some v) :
    ∃ st' : State, Runs w p ω (.store a e) st .normal st' (a.size + e.size + 1) ∧
      st'.mem = Function.update st.mem x v ∧ st'.regs = st.regs :=
  ⟨_, runs_store_of ha he, rfl, rfl⟩

theorem step_call {st : State} {r f : ℕ} {args : List Expr} {vs : List ℕ} {body : Stmt}
    {o₁ : Outcome} {st₁ : State} {c₁ : ℕ} (hargs : evalArgs w st args = some vs)
    (hproc : p.procs[f]? = some body)
    (hrun : Runs w p ω body (startState vs st.mem st.pos) o₁ st₁ c₁) :
    ∃ st' : State, Runs w p ω (.call r f args) st .normal st' (argsSize args + c₁ + 1) ∧
      st'.mem = st₁.mem ∧ st'.regs r = o₁.value ∧ ∀ j, j ≠ r → st'.regs j = st.regs j :=
  ⟨_, runs_call_of hargs hproc hrun, rfl, by simp, fun j hj => by simp [Function.update_of_ne hj]⟩

theorem step_cond_true {st : State} {e : Expr} {s t : Stmt} {v : ℕ} {o : Outcome} {st' : State}
    {c : ℕ} (he : e.eval w st = some v) (hv : v ≠ 0) (hs : Runs w p ω s st o st' c) :
    Runs w p ω (.cond e s t) st o st' (e.size + c + 1) :=
  runs_cond_iff.mpr ⟨v, c, he, by simpa [hv] using hs, rfl⟩

theorem step_cond_false {st : State} {e : Expr} {s t : Stmt} {o : Outcome} {st' : State}
    {c : ℕ} (he : e.eval w st = some 0) (ht : Runs w p ω t st o st' c) :
    Runs w p ω (.cond e s t) st o st' (e.size + c + 1) :=
  runs_cond_iff.mpr ⟨0, c, he, by simpa using ht, rfl⟩

theorem step_nop {st : State} : Runs w p ω .nop st .normal st 1 :=
  runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩

theorem step_ret {st : State} {e : Expr} {v : ℕ} (he : e.eval w st = some v) :
    Runs w p ω (.ret e) st (.returned v) st (e.size + 1) :=
  runs_ret_iff.mpr ⟨v, he, rfl, rfl, rfl⟩

/-- A sequence whose first part returns does not run its second part. -/
theorem runs_seq_returned {s₁ s₂ : Stmt} {st st₁ : State} {u c₁ : ℕ}
    (h₁ : Runs w p ω s₁ st (.returned u) st₁ c₁) :
    Runs w p ω (.seq s₁ s₂) st (.returned u) st₁ (c₁ + 1) :=
  runs_seq_iff.mpr (Or.inl ⟨u, c₁, h₁, rfl, rfl⟩)

/-- The arguments of a call whose expressions all have values. -/
theorem evalArgs_two {st : State} {e₁ e₂ : Expr} {v₁ v₂ : ℕ} (h₁ : e₁.eval w st = some v₁)
    (h₂ : e₂.eval w st = some v₂) : evalArgs w st [e₁, e₂] = some [v₁, v₂] :=
  evalArgs_cons h₁ (evalArgs_cons h₂ (evalArgs_nil w st))

theorem evalArgs_three {st : State} {e₁ e₂ e₃ : Expr} {v₁ v₂ v₃ : ℕ}
    (h₁ : e₁.eval w st = some v₁) (h₂ : e₂.eval w st = some v₂) (h₃ : e₃.eval w st = some v₃) :
    evalArgs w st [e₁, e₂, e₃] = some [v₁, v₂, v₃] :=
  evalArgs_cons h₁ (evalArgs_two h₂ h₃)

theorem evalArgs_four {st : State} {e₁ e₂ e₃ e₄ : Expr} {v₁ v₂ v₃ v₄ : ℕ}
    (h₁ : e₁.eval w st = some v₁) (h₂ : e₂.eval w st = some v₂) (h₃ : e₃.eval w st = some v₃)
    (h₄ : e₄.eval w st = some v₄) :
    evalArgs w st [e₁, e₂, e₃, e₄] = some [v₁, v₂, v₃, v₄] :=
  evalArgs_cons h₁ (evalArgs_three h₂ h₃ h₄)

theorem evalArgs_five {st : State} {e₁ e₂ e₃ e₄ e₅ : Expr} {v₁ v₂ v₃ v₄ v₅ : ℕ}
    (h₁ : e₁.eval w st = some v₁) (h₂ : e₂.eval w st = some v₂) (h₃ : e₃.eval w st = some v₃)
    (h₄ : e₄.eval w st = some v₄) (h₅ : e₅.eval w st = some v₅) :
    evalArgs w st [e₁, e₂, e₃, e₄, e₅] = some [v₁, v₂, v₃, v₄, v₅] :=
  evalArgs_cons h₁ (evalArgs_four h₂ h₃ h₄ h₅)

end MinCostFlow.SparseCore.Program
