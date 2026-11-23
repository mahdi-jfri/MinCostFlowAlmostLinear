module

public import MinCostFlow.LSF.Program.CallSeq

/-!
# Call sequences with assignments

`callSeqStmt` (`CallSeq.lean`) only calls. The init driver also computes places from numbers it
has read, and reads words from memory. `seqStmt R ρ i steps` runs a list of steps: a call step
calls a procedure on some registers, and an assignment step evaluates an expression (which may
read memory). Step `j` writes register `R + i + j`. The pre `SeqPre2` and the post `SeqPost2`
are those of `CallSeq.lean`, with one more case: an assignment step asks that its expression has
a value `v`, and continues with `v` in its register. An expression does not read the position of
the coin stream, so the value depends only on the registers and the memory (`eval_pos`).
-/

namespace MinCostFlow.LSF.Program

open WordRAM

@[expose] public section

/-- One step of a sequence. -/
inductive SeqStep where
  | call (f : ℕ) (rs : List ℕ) (C : Contract)
  | assign (e : Expr)

/-- The body: the steps in order, then `ret (reg ρ)`. Step `j` writes register `R + i + j`. -/
def seqStmt (R ρ : ℕ) : ℕ → List SeqStep → Stmt
  | _, [] => .ret (.reg ρ)
  | i, .call f rs _ :: rest => .call (R + i) f (rs.map Expr.reg) ;; seqStmt R ρ (i + 1) rest
  | i, .assign e :: rest => .assign (R + i) e ;; seqStmt R ρ (i + 1) rest

lemma seqStmt_noRand (R ρ i : ℕ) (steps : List SeqStep) : (seqStmt R ρ i steps).NoRand := by
  induction steps generalizing i with
  | nil => trivial
  | cons st rest ih =>
    cases st with
    | call f rs C => exact ⟨trivial, ih (i + 1)⟩
    | assign e => exact ⟨trivial, ih (i + 1)⟩

/-- The value of an expression does not depend on the position of the coin stream. -/
lemma eval_pos (w : ℕ) (mem regs : ℕ → ℕ) (pos : ℕ) (e : Expr) :
    e.eval w { mem := mem, regs := regs, pos := pos } =
      e.eval w { mem := mem, regs := regs, pos := 0 } := by
  induction e with
  | const k => rfl
  | reg r => rfl
  | load a ih => simp only [Expr.eval, ih]
  | bin op a b iha ihb => simp only [Expr.eval, iha, ihb]

/-- The value of `e` with registers `regs` and memory `mem`. -/
def evalAt (w : ℕ) (regs mem : ℕ → ℕ) (e : Expr) : Option ℕ :=
  e.eval w { mem := mem, regs := regs, pos := 0 }

/-- What the steps need, for all outcomes of the earlier calls. -/
def SeqPre2 (w R : ℕ) : ℕ → List SeqStep → (ℕ → ℕ) → (ℕ → ℕ) → ℕ → Prop
  | _, [], _, _, B => 2 ≤ B
  | i, .call _ rs C :: rest, regs, mem, B =>
    (∀ x ∈ rs.map regs, x < 2 ^ w) ∧ C.pre (rs.map regs) mem ∧
    C.cost (rs.map regs) mem + rs.length + 2 ≤ B ∧
    ∀ v mem', C.post (rs.map regs) mem v mem' →
      SeqPre2 w R (i + 1) rest (Function.update regs (R + i) v) mem'
        (B - (C.cost (rs.map regs) mem + rs.length + 2))
  | i, .assign e :: rest, regs, mem, B =>
    ∃ v, evalAt w regs mem e = some v ∧ e.size + 2 ≤ B ∧
      SeqPre2 w R (i + 1) rest (Function.update regs (R + i) v) mem (B - (e.size + 2))

/-- What the steps do. -/
def SeqPost2 (R ρ : ℕ) : ℕ → List SeqStep → (ℕ → ℕ) → (ℕ → ℕ) → ℕ → (ℕ → ℕ) → Prop
  | _, [], regs, mem, ret, mem' => mem' = mem ∧ ret = regs ρ
  | i, .call _ rs C :: rest, regs, mem, ret, mem' => ∃ v mem₁, C.post (rs.map regs) mem v mem₁ ∧
    SeqPost2 R ρ (i + 1) rest (Function.update regs (R + i) v) mem₁ ret mem'
  | i, .assign _ :: rest, regs, mem, ret, mem' => ∃ v,
    SeqPost2 R ρ (i + 1) rest (Function.update regs (R + i) v) mem ret mem'

/-- Every called procedure meets its contract. -/
def AllMeet2 (w : ℕ) (p : Program) (steps : List SeqStep) : Prop :=
  ∀ f rs C, SeqStep.call f rs C ∈ steps → MeetsContract w p f C

theorem runs_seqStmt {w R ρ : ℕ} {p : Program} {ω : ℕ → Bool} :
    ∀ (steps : List SeqStep) (i : ℕ) (st : State) (B k : ℕ), AllMeet2 w p steps →
    SeqPre2 w R i steps st.regs st.mem B →
    ∃ o st' c, Runs w p ω (seqStmt R ρ i steps) st o st' c ∧
      SeqPost2 R ρ i steps st.regs st.mem o.value st'.mem ∧ k + c ≤ k + B := by
  intro steps
  induction steps with
  | nil =>
    intro i st B k _ hB
    refine runs_ret_le (v := st.regs ρ) rfl ⟨rfl, rfl⟩ ?_
    · simp only [SeqPre2] at hB
      simp only [Expr.size]
      omega
  | cons it rest ih =>
    intro i st B k hall hpre
    have hrest : AllMeet2 w p rest := fun f rs C h => hall f rs C (List.mem_cons_of_mem _ h)
    cases it with
    | call f rs C =>
      obtain ⟨hw, hC, hcost, hnext⟩ := hpre
      have hf : MeetsContract w p f C := hall f rs C (List.mem_cons_self ..)
      refine runs_seq_call_le (vs := rs.map st.regs) hf (evalArgs_map_reg_seq _) hw hC ?_
      intro v mem' pos' hpost
      obtain ⟨o, st', c, hr, hseq, hc⟩ := ih (i + 1)
        { mem := mem', regs := Function.update st.regs (R + i) v, pos := pos' }
        (B - (C.cost (rs.map st.regs) st.mem + rs.length + 2))
        (k + argsSize (rs.map Expr.reg) + C.cost (rs.map st.regs) st.mem + 2) hrest
        (hnext v mem' hpost)
      refine ⟨o, st', c, hr, ⟨v, mem', hpost, hseq⟩, ?_⟩
      rw [argsSize_map_reg_seq] at hc ⊢
      omega
    | assign e =>
      obtain ⟨v, hv, hsz, hnext⟩ := hpre
      have he : e.eval w st = some v := by
        rw [show st = { mem := st.mem, regs := st.regs, pos := st.pos } from rfl, eval_pos]
        exact hv
      refine runs_seq_assign_le he ?_
      obtain ⟨o, st', c, hr, hseq, hc⟩ := ih (i + 1)
        { st with regs := Function.update st.regs (R + i) v } (B - (e.size + 2))
        (k + e.size + 2) hrest hnext
      exact ⟨o, st', c, hr, ⟨v, hseq⟩, by omega⟩

/-- The contract of a step sequence with cost bound `K`. -/
def seqContract (w R ρ : ℕ) (steps : List SeqStep) (K : List ℕ → (ℕ → ℕ) → ℕ) : Contract where
  pre args mem := SeqPre2 w R 0 steps (fun j => args.getD j 0) mem (K args mem)
  post args mem ret mem' := SeqPost2 R ρ 0 steps (fun j => args.getD j 0) mem ret mem'
  cost := K

theorem seq_meetsContract {w R ρ : ℕ} {p : Program} {b : ℕ} {steps : List SeqStep}
    {K : List ℕ → (ℕ → ℕ) → ℕ}
    (hp : p.procs[b]? = some (seqStmt R ρ 0 steps)) (hall : AllMeet2 w p steps) :
    MeetsContract w p b (seqContract w R ρ steps K) := by
  refine meetsContract_of_runs hp fun args mem pos ω _ hpre => ?_
  obtain ⟨o, st', c, hr, hseq, hc⟩ :=
    runs_seqStmt (ρ := ρ) (ω := ω) steps 0 (startState args mem pos) (K args mem) 0 hall hpre
  exact ⟨o, st', c, hr, hseq, by simpa [seqContract] using hc⟩

/-- A larger budget keeps `SeqPre2`. -/
lemma SeqPre2.mono {w R : ℕ} : ∀ {steps : List SeqStep} {i : ℕ} {regs mem : ℕ → ℕ} {B B' : ℕ},
    SeqPre2 w R i steps regs mem B → B ≤ B' → SeqPre2 w R i steps regs mem B'
  | [], _, _, _, _, _, h, hB => by simp only [SeqPre2] at h ⊢; omega
  | .call _ _ _ :: _, _, _, _, _, _, ⟨hw, hC, hc, hn⟩, hB =>
    ⟨hw, hC, by omega, fun v mem' hp => SeqPre2.mono (hn v mem' hp) (by omega)⟩
  | .assign _ :: _, _, _, _, _, _, ⟨v, hv, hs, hn⟩, hB =>
    ⟨v, hv, by omega, SeqPre2.mono hn (by omega)⟩

/-- A call step, with the arguments named and a bound `c` on its cost. -/
lemma SeqPre2.call {w R i f : ℕ} {rs : List ℕ} {C : Contract} {rest : List SeqStep}
    {regs mem : ℕ → ℕ} {B : ℕ}
    (args : List ℕ) (c : ℕ) (hargs : rs.map regs = args) (hw : ∀ x ∈ rs.map regs, x < 2 ^ w)
    (hpre : C.pre args mem) (hc : C.cost args mem + rs.length + 2 ≤ c) (hcB : c ≤ B)
    (hnext : ∀ v mem', C.post args mem v mem' →
      SeqPre2 w R (i + 1) rest (Function.update regs (R + i) v) mem' (B - c)) :
    SeqPre2 w R i (.call f rs C :: rest) regs mem B := by
  subst hargs
  exact ⟨hw, hpre, by omega, fun v mem' hp => SeqPre2.mono (hnext v mem' hp) (by omega)⟩

/-- An assignment step with value `v`, and a bound `c` on its cost. -/
lemma SeqPre2.assign {w R i : ℕ} {e : Expr} {rest : List SeqStep} {regs mem : ℕ → ℕ} {B : ℕ}
    (v c : ℕ) (hv : evalAt w regs mem e = some v) (hc : e.size + 2 ≤ c) (hcB : c ≤ B)
    (hnext : SeqPre2 w R (i + 1) rest (Function.update regs (R + i) v) mem (B - c)) :
    SeqPre2 w R i (.assign e :: rest) regs mem B :=
  ⟨v, hv, by omega, SeqPre2.mono hnext (by omega)⟩

end

end MinCostFlow.LSF.Program
