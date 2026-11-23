module

public import MinCostFlow.LSF.Program.CallSeq2

/-!
# Step sequences with contracts chosen along the way

In `CallSeq2.lean` the contract of each call is fixed in the list of steps. The contracts of the
later phases of the init driver depend on objects that only exist after the earlier calls, such
as the vertex list or the tree `T₀`. Since the program text does not contain the contracts, the
proof may pick each contract when it reaches the call.

`dseqStmt R ρ i steps` is the body (the same code as `seqStmt`). `SeqWP w p R ρ Q i steps regs
mem B` is a weakest precondition: it holds when each call has some contract that the procedure
meets, whose pre holds, and whose post (for every outcome) leads to the rest, and when at the end
the returned register and the memory satisfy `Q`. `runs_dseqStmt` turns it into a run.
-/

namespace MinCostFlow.LSF.Program

open WordRAM

@[expose] public section

/-- One step: a call of procedure `f` on the values of the expressions `es`, or an
assignment. -/
inductive DStep where
  | call (f : ℕ) (es : List Expr)
  | assign (e : Expr)

/-- The body: the steps in order, then `ret (reg ρ)`. Step `j` writes register `R + i + j`. -/
def dseqStmt (R ρ : ℕ) : ℕ → List DStep → Stmt
  | _, [] => .ret (.reg ρ)
  | i, .call f es :: rest => .call (R + i) f es ;; dseqStmt R ρ (i + 1) rest
  | i, .assign e :: rest => .assign (R + i) e ;; dseqStmt R ρ (i + 1) rest

lemma dseqStmt_noRand (R ρ i : ℕ) (steps : List DStep) : (dseqStmt R ρ i steps).NoRand := by
  induction steps generalizing i with
  | nil => trivial
  | cons st rest ih =>
    cases st with
    | call f es => exact ⟨trivial, ih (i + 1)⟩
    | assign e => exact ⟨trivial, ih (i + 1)⟩

/-- The values of argument expressions do not depend on the position of the coin stream. -/
lemma evalArgs_pos (w : ℕ) (mem regs : ℕ → ℕ) (pos : ℕ) (es : List Expr) :
    evalArgs w { mem := mem, regs := regs, pos := pos } es =
      evalArgs w { mem := mem, regs := regs, pos := 0 } es := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [evalArgs, eval_pos, ih]

/-- The values of the argument expressions `es` with registers `regs` and memory `mem`. -/
def evalArgsAt (w : ℕ) (regs mem : ℕ → ℕ) (es : List Expr) : Option (List ℕ) :=
  evalArgs w { mem := mem, regs := regs, pos := 0 } es

/-- The weakest precondition of the steps for a condition `P` on the registers, the memory and
the budget left after the last step. -/
def SeqWPR (w : ℕ) (p : Program) (R : ℕ) (P : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → Prop) :
    ℕ → List DStep → (ℕ → ℕ) → (ℕ → ℕ) → ℕ → Prop
  | _, [], regs, mem, B => P regs mem B
  | i, .call f es :: rest, regs, mem, B =>
    ∃ args, evalArgsAt w regs mem es = some args ∧ (∀ x ∈ args, x < 2 ^ w) ∧
      ∃ C : Contract, MeetsContract w p f C ∧
      C.pre args mem ∧ C.cost args mem + argsSize es + 2 ≤ B ∧
      ∀ v mem', C.post args mem v mem' →
        SeqWPR w p R P (i + 1) rest (Function.update regs (R + i) v) mem'
          (B - (C.cost args mem + argsSize es + 2))
  | i, .assign e :: rest, regs, mem, B =>
    ∃ v, evalAt w regs mem e = some v ∧ e.size + 2 ≤ B ∧
      SeqWPR w p R P (i + 1) rest (Function.update regs (R + i) v) mem (B - (e.size + 2))

/-- The weakest precondition of the body for the final condition `Q` on the returned value and
the memory. -/
def SeqWP (w : ℕ) (p : Program) (R ρ : ℕ) (Q : ℕ → (ℕ → ℕ) → Prop) (i : ℕ) (steps : List DStep)
    (regs mem : ℕ → ℕ) (B : ℕ) : Prop :=
  SeqWPR w p R (fun regs mem B => Q (regs ρ) mem ∧ 2 ≤ B) i steps regs mem B

theorem runs_dseqStmt {w R ρ : ℕ} {p : Program} {ω : ℕ → Bool} {Q : ℕ → (ℕ → ℕ) → Prop} :
    ∀ (steps : List DStep) (i : ℕ) (st : State) (B k : ℕ),
    SeqWP w p R ρ Q i steps st.regs st.mem B →
    ∃ o st' c, Runs w p ω (dseqStmt R ρ i steps) st o st' c ∧ Q o.value st'.mem ∧
      k + c ≤ k + B := by
  intro steps
  induction steps with
  | nil =>
    intro i st B k hB
    refine runs_ret_le (v := st.regs ρ) rfl hB.1 ?_
    have := hB.2
    simp only [Expr.size]
    omega
  | cons it rest ih =>
    intro i st B k hpre
    cases it with
    | call f es =>
      obtain ⟨args, hev, hw, C, hf, hC, hcost, hnext⟩ := hpre
      have hev' : evalArgs w st es = some args := by
        rw [show st = { mem := st.mem, regs := st.regs, pos := st.pos } from rfl, evalArgs_pos]
        exact hev
      refine runs_seq_call_le (vs := args) hf hev' hw hC ?_
      intro v mem' pos' hpost
      obtain ⟨o, st', c, hr, hQ, hc⟩ := ih (i + 1)
        { mem := mem', regs := Function.update st.regs (R + i) v, pos := pos' }
        (B - (C.cost args st.mem + argsSize es + 2))
        (k + argsSize es + C.cost args st.mem + 2)
        (hnext v mem' hpost)
      exact ⟨o, st', c, hr, hQ, by omega⟩
    | assign e =>
      obtain ⟨v, hv, hsz, hnext⟩ := hpre
      have he : e.eval w st = some v := by
        rw [show st = { mem := st.mem, regs := st.regs, pos := st.pos } from rfl, eval_pos]
        exact hv
      refine runs_seq_assign_le he ?_
      obtain ⟨o, st', c, hr, hQ, hc⟩ := ih (i + 1)
        { st with regs := Function.update st.regs (R + i) v } (B - (e.size + 2))
        (k + e.size + 2) hnext
      exact ⟨o, st', c, hr, hQ, by omega⟩

/-- A final condition that a larger budget keeps. -/
def UpClosed (P : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → Prop) : Prop :=
  ∀ r m b b', b ≤ b' → P r m b → P r m b'

lemma upClosed_wp (ρ : ℕ) (Q : ℕ → (ℕ → ℕ) → Prop) :
    UpClosed (fun regs mem B => Q (regs ρ) mem ∧ 2 ≤ B) :=
  fun _ _ _ _ hb h => ⟨h.1, by have := h.2; omega⟩

/-- A larger budget keeps `SeqWPR`, for a final condition that a larger budget keeps. -/
lemma SeqWPR.mono {w : ℕ} {p : Program} {R : ℕ} {P : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → Prop}
    (hP : UpClosed P) : ∀ {steps : List DStep} {i : ℕ} {regs mem : ℕ → ℕ} {B B' : ℕ},
    SeqWPR w p R P i steps regs mem B → B ≤ B' → SeqWPR w p R P i steps regs mem B'
  | [], _, _, _, _, _, h, hB => hP _ _ _ _ hB h
  | .call _ _ :: _, _, _, _, _, _, ⟨args, hev, hw, C, hf, hC, hc, hn⟩, hB =>
    ⟨args, hev, hw, C, hf, hC, by omega, fun v mem' hp => SeqWPR.mono hP (hn v mem' hp) (by omega)⟩
  | .assign _ :: _, _, _, _, _, _, ⟨v, hv, hs, hn⟩, hB =>
    ⟨v, hv, by omega, SeqWPR.mono hP hn (by omega)⟩

/-- A call step with the contract `C`, the arguments named, and a bound `c` on its cost. -/
lemma SeqWPR.call {w : ℕ} {p : Program} {R : ℕ} {P : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → Prop}
    (hP : UpClosed P) {i f : ℕ} {es : List Expr} {rest : List DStep} {regs mem : ℕ → ℕ} {B : ℕ}
    (C : Contract) (args : List ℕ) (c : ℕ) (hf : MeetsContract w p f C)
    (hargs : evalArgsAt w regs mem es = some args) (hw : ∀ x ∈ args, x < 2 ^ w)
    (hpre : C.pre args mem) (hc : C.cost args mem + argsSize es + 2 ≤ c) (hcB : c ≤ B)
    (hnext : ∀ v mem', C.post args mem v mem' →
      SeqWPR w p R P (i + 1) rest (Function.update regs (R + i) v) mem' (B - c)) :
    SeqWPR w p R P i (.call f es :: rest) regs mem B :=
  ⟨args, hargs, hw, C, hf, hpre, by omega, fun v mem' hp => SeqWPR.mono hP (hnext v mem' hp) (by omega)⟩

/-- An assignment step with value `v`, and a bound `c` on its cost. -/
lemma SeqWPR.assign {w : ℕ} {p : Program} {R : ℕ} {P : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → Prop}
    (hP : UpClosed P) {i : ℕ} {e : Expr} {rest : List DStep} {regs mem : ℕ → ℕ} {B : ℕ}
    (v c : ℕ) (hv : evalAt w regs mem e = some v) (hc : e.size + 2 ≤ c) (hcB : c ≤ B)
    (hnext : SeqWPR w p R P (i + 1) rest (Function.update regs (R + i) v) mem (B - c)) :
    SeqWPR w p R P i (.assign e :: rest) regs mem B :=
  ⟨v, hv, by omega, SeqWPR.mono hP hnext (by omega)⟩

/-- Steps in two parts. The first part ends in a condition `P` from which the second part runs. -/
lemma seqWPR_append {w : ℕ} {p : Program} {R : ℕ} {P Q : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → Prop}
    {s₂ : List DStep} :
    ∀ (s₁ : List DStep) {i : ℕ} {regs mem : ℕ → ℕ} {B : ℕ},
    (∀ regs' mem' B', P regs' mem' B' → SeqWPR w p R Q (i + s₁.length) s₂ regs' mem' B') →
    SeqWPR w p R P i s₁ regs mem B → SeqWPR w p R Q i (s₁ ++ s₂) regs mem B
  | [], i, _, _, _, hP, h => by simpa using hP _ _ _ h
  | .call f rs :: s₁, i, _, _, _, hP, ⟨args, hev, hw, C, hf, hC, hc, hn⟩ =>
    ⟨args, hev, hw, C, hf, hC, hc, fun v mem' hp =>
      seqWPR_append s₁ (fun r m b h => by
        have e : i + 1 + s₁.length = i + (DStep.call f rs :: s₁).length := by
          simp only [List.length_cons]; omega
        rw [e]; exact hP r m b h) (hn v mem' hp)⟩
  | .assign e :: s₁, i, _, _, _, hP, ⟨v, hv, hs, hn⟩ =>
    ⟨v, hv, hs, seqWPR_append s₁ (fun r m b h => by
        have e' : i + 1 + s₁.length = i + (DStep.assign e :: s₁).length := by
          simp only [List.length_cons]; omega
        rw [e']; exact hP r m b h) hn⟩

end

end MinCostFlow.LSF.Program
