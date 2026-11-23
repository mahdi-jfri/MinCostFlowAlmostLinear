module

public import WordRAM.Logic
public import WordRAM.Tactic

/-!
# A procedure that runs calls one after the other

Many procedures of the initialization only call other procedures in a fixed order, each with
some of their registers as arguments. `callSeqStmt R i items` is such a body: call `j` of the list
reads the registers listed in `items[j].rs` and writes its result into register `R + i + j`. It
then returns register `ρ`.

`callSeqContract` states what such a body does when each callee meets its own contract
`items[j].C`. Its pre asks, call by call, that the arguments are words, that the pre of the callee
holds, and that the cost of the callee fits in the budget that is left; and it asks this for every
outcome that the posts of the earlier calls allow (`SeqPre`). Its post says that there are results
and memories after each call that the posts of the callees link (`SeqPost`). The registers are
threaded exactly: the register file at call `j` is the start file with the earlier results written
in. So no condition on register numbers is needed.
-/

namespace MinCostFlow.LSF.Program

open WordRAM

@[expose] public section

/-- One call of a sequence: the callee, the registers it reads, and its contract. -/
structure CallItem where
  f : ℕ
  rs : List ℕ
  C : Contract

/-- The body: the calls in order, then `ret (reg ρ)`. Call `j` writes register `R + i + j`. -/
def callSeqStmt (R ρ : ℕ) : ℕ → List CallItem → Stmt
  | _, [] => .ret (.reg ρ)
  | i, it :: rest => .call (R + i) it.f (it.rs.map Expr.reg) ;; callSeqStmt R ρ (i + 1) rest

lemma callSeqStmt_noRand (R ρ i : ℕ) (items : List CallItem) :
    (callSeqStmt R ρ i items).NoRand := by
  induction items generalizing i with
  | nil => trivial
  | cons it rest ih => exact ⟨trivial, ih (i + 1)⟩

/-- What the calls need: words as arguments, the pres of the callees, and a cost budget `B`, for
all outcomes of the earlier calls. -/
def SeqPre (w R : ℕ) : ℕ → List CallItem → (ℕ → ℕ) → (ℕ → ℕ) → ℕ → Prop
  | _, [], _, _, B => 2 ≤ B
  | i, it :: rest, regs, mem, B =>
    (∀ x ∈ it.rs.map regs, x < 2 ^ w) ∧ it.C.pre (it.rs.map regs) mem ∧
    it.C.cost (it.rs.map regs) mem + it.rs.length + 2 ≤ B ∧
    ∀ v mem', it.C.post (it.rs.map regs) mem v mem' →
      SeqPre w R (i + 1) rest (Function.update regs (R + i) v) mem'
        (B - (it.C.cost (it.rs.map regs) mem + it.rs.length + 2))

/-- What the calls do: the posts of the callees link results and memories after each call. -/
def SeqPost (R ρ : ℕ) : ℕ → List CallItem → (ℕ → ℕ) → (ℕ → ℕ) → ℕ → (ℕ → ℕ) → Prop
  | _, [], regs, mem, ret, mem' => mem' = mem ∧ ret = regs ρ
  | i, it :: rest, regs, mem, ret, mem' => ∃ v mem₁, it.C.post (it.rs.map regs) mem v mem₁ ∧
    SeqPost R ρ (i + 1) rest (Function.update regs (R + i) v) mem₁ ret mem'

/-- Every callee meets its contract. -/
def AllMeet (w : ℕ) (p : Program) (items : List CallItem) : Prop :=
  ∀ it ∈ items, MeetsContract w p it.f it.C

lemma evalArgs_map_reg_seq {w : ℕ} {st : State} (l : List ℕ) :
    evalArgs w st (l.map Expr.reg) = some (l.map st.regs) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [evalArgs, Expr.eval, ih]

lemma argsSize_map_reg_seq (l : List ℕ) : argsSize (l.map Expr.reg) = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [argsSize, Expr.size, ih]; omega

/-- Running the calls from a state whose registers are `regs`. -/
theorem runs_callSeq {w R ρ : ℕ} {p : Program} {ω : ℕ → Bool} :
    ∀ (items : List CallItem) (i : ℕ) (st : State) (B k : ℕ), AllMeet w p items →
    SeqPre w R i items st.regs st.mem B →
    ∃ o st' c, Runs w p ω (callSeqStmt R ρ i items) st o st' c ∧
      SeqPost R ρ i items st.regs st.mem o.value st'.mem ∧ k + c ≤ k + B := by
  intro items
  induction items with
  | nil =>
    intro i st B k _ hB
    refine runs_ret_le (v := st.regs ρ) rfl ⟨rfl, rfl⟩ ?_
    · simp only [SeqPre] at hB
      simp only [Expr.size]
      omega
  | cons it rest ih =>
    intro i st B k hall hpre
    obtain ⟨hw, hC, hcost, hnext⟩ := hpre
    have hf : MeetsContract w p it.f it.C := hall it (List.mem_cons_self ..)
    have hrest : AllMeet w p rest := fun it' h' => hall it' (List.mem_cons_of_mem _ h')
    refine runs_seq_call_le (vs := it.rs.map st.regs) hf (evalArgs_map_reg_seq _) hw hC ?_
    intro v mem' pos' hpost
    obtain ⟨o, st', c, hr, hseq, hc⟩ := ih (i + 1)
      { mem := mem', regs := Function.update st.regs (R + i) v, pos := pos' }
      (B - (it.C.cost (it.rs.map st.regs) st.mem + it.rs.length + 2))
      (k + argsSize (it.rs.map Expr.reg) + it.C.cost (it.rs.map st.regs) st.mem + 2) hrest
      (hnext v mem' hpost)
    refine ⟨o, st', c, hr, ⟨v, mem', hpost, hseq⟩, ?_⟩
    rw [argsSize_map_reg_seq] at hc ⊢
    omega

/-- A larger budget keeps `SeqPre`. -/
lemma SeqPre.mono {w R : ℕ} : ∀ {items : List CallItem} {i : ℕ} {regs mem : ℕ → ℕ} {B B' : ℕ},
    SeqPre w R i items regs mem B → B ≤ B' → SeqPre w R i items regs mem B'
  | [], _, _, _, _, _, h, hB => by simp only [SeqPre] at h ⊢; omega
  | _ :: _, _, _, _, _, _, ⟨hw, hC, hc, hn⟩, hB =>
    ⟨hw, hC, by omega, fun v mem' hp => SeqPre.mono (hn v mem' hp) (by omega)⟩

/-- One step of `SeqPre`, with the arguments named and a bound `c` on the cost of the call. -/
lemma SeqPre.cons {w R i : ℕ} {it : CallItem} {rest : List CallItem} {regs mem : ℕ → ℕ} {B : ℕ}
    (args : List ℕ) (c : ℕ) (hargs : it.rs.map regs = args) (hw : ∀ x ∈ it.rs.map regs, x < 2 ^ w)
    (hpre : it.C.pre args mem) (hc : it.C.cost args mem + it.rs.length + 2 ≤ c) (hcB : c ≤ B)
    (hnext : ∀ v mem', it.C.post args mem v mem' →
      SeqPre w R (i + 1) rest (Function.update regs (R + i) v) mem' (B - c)) :
    SeqPre w R i (it :: rest) regs mem B := by
  subst hargs
  exact ⟨hw, hpre, by omega, fun v mem' hp => SeqPre.mono (hnext v mem' hp) (by omega)⟩

/-- The arguments are words when each register read is a word. -/
lemma words_of_map {w : ℕ} {rs : List ℕ} {regs : ℕ → ℕ} (h : ∀ j ∈ rs, regs j < 2 ^ w) :
    ∀ x ∈ rs.map regs, x < 2 ^ w := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
  exact h j hj

/-- The contract of a call sequence with `n` arguments and cost bound `K`. -/
def callSeqContract (w R ρ : ℕ) (items : List CallItem) (K : List ℕ → (ℕ → ℕ) → ℕ) :
    Contract where
  pre args mem := SeqPre w R 0 items (fun j => args.getD j 0) mem (K args mem)
  post args mem ret mem' := SeqPost R ρ 0 items (fun j => args.getD j 0) mem ret mem'
  cost := K

theorem callSeq_meetsContract {w R ρ : ℕ} {p : Program} {b : ℕ} {items : List CallItem}
    {K : List ℕ → (ℕ → ℕ) → ℕ}
    (hp : p.procs[b]? = some (callSeqStmt R ρ 0 items)) (hall : AllMeet w p items) :
    MeetsContract w p b (callSeqContract w R ρ items K) := by
  refine meetsContract_of_runs hp fun args mem pos ω _ hpre => ?_
  obtain ⟨o, st', c, hr, hseq, hc⟩ :=
    runs_callSeq (ρ := ρ) (ω := ω) items 0 (startState args mem pos) (K args mem) 0 hall hpre
  exact ⟨o, st', c, hr, hseq, by simpa [callSeqContract] using hc⟩


/-! ## Storing one word -/

/-- Args: `[a, v]`. Stores `v` at address `a`. -/
def storeWordStmt : Stmt := .store (.reg 0) (.reg 1) ;; .ret (.const 0)

lemma storeWordStmt_noRand : storeWordStmt.NoRand := by simp [storeWordStmt, Stmt.NoRand]

/-- The contract of `storeWordStmt`. -/
def storeWordContract : Contract where
  pre args _ := ∃ a v, args = [a, v]
  post args mem ret mem' := ∃ a v, args = [a, v] ∧ ret = 0 ∧ mem' = Function.update mem a v
  cost _ _ := 10

theorem storeWord_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.procs[b]? = some storeWordStmt) : MeetsContract w p b storeWordContract := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨a, v, rfl⟩ := hpre
  refine runs_start_le ?_
  unfold storeWordStmt
  refine runs_seq_store_le (x := a) (v := v) rfl rfl ?_
  refine runs_ret_le (v := 0) ?_ ⟨a, v, rfl, rfl, rfl⟩ ?_
  · simp only [Expr.eval]
    exact if_pos (Nat.two_pow_pos w)
  · simp [storeWordContract, Expr.size]

end

end MinCostFlow.LSF.Program
