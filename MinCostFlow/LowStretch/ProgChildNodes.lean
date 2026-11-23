module

public import WordRAM.Logic
public import WordRAM.Tactic

/-!
# The super-vertices of a child and their local indices

`ncP` copies the super-vertices of a child into a new array and gives each its local index.
Entry `i` of the list at `SRC` is a local index of the parent, so the node is
`x i = NAX[SRC[i]]`. `ncP` writes `NAO[i] := x i` and `LOC[HEAD[x i]] := i` (`ncP_spec`). The
heads of the nodes are distinct, so each label gets the index of its own node. Each entry costs a
constant.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The numbers of `ncP`. -/
structure NCE where
  cnt : ℕ
  SRC : ℕ
  NAX : ℕ
  HEAD : ℕ
  LOC : ℕ
  NAO : ℕ
  mem0 : ℕ → ℕ

namespace NCE

variable (E : NCE)

/-- The arguments of `ncP`. -/
def args : List ℕ := [E.cnt, E.SRC, E.NAX, E.HEAD, E.LOC, E.NAO]

/-- The node of entry `i`. -/
def x (i : ℕ) : ℕ := E.mem0 (E.NAX + E.mem0 (E.SRC + i))

/-- The head of the node of entry `i`. -/
def hd (i : ℕ) : ℕ := E.mem0 (E.HEAD + E.x i)

/-- A cell outside the local indices `[LOC, LOC + N)`. -/
def Off (N a : ℕ) : Prop := a < E.LOC ∨ E.LOC + N ≤ a

/-- The precondition, for `N` local index cells: the cells read lie below `NAO` and outside the
local indices, the heads are distinct and below `N`, and the local indices lie below `NAO`. -/
structure Ok (w N : ℕ) : Prop where
  rd : ∀ i < E.cnt, (E.SRC + i < E.NAO ∧ E.Off N (E.SRC + i)) ∧
    (E.NAX + E.mem0 (E.SRC + i) < E.NAO ∧ E.Off N (E.NAX + E.mem0 (E.SRC + i))) ∧
    (E.HEAD + E.x i < E.NAO ∧ E.Off N (E.HEAD + E.x i)) ∧ E.hd i < N
  inj : ∀ i < E.cnt, ∀ j < E.cnt, E.hd i = E.hd j → i = j
  loc : E.LOC + N ≤ E.NAO
  room : E.NAO + E.cnt + 1 < 2 ^ w

/-- The cells changed after the entries before `j`. -/
def Out (j a : ℕ) : Prop := (E.NAO ≤ a ∧ a < E.NAO + j) ∨ ∃ i < j, a = E.LOC + E.hd i

/-- The memory after the entries before `j`. -/
def Done (j : ℕ) (M : ℕ → ℕ) : Prop :=
  (∀ i < j, M (E.NAO + i) = E.x i) ∧ (∀ i < j, M (E.LOC + E.hd i) = i) ∧
    ∀ a, ¬ E.Out j a → M a = E.mem0 a

/-- The registers that never change. -/
def R (st : State) : Prop :=
  st.regs 0 = E.cnt ∧ st.regs 1 = E.SRC ∧ st.regs 2 = E.NAX ∧ st.regs 3 = E.HEAD ∧
    st.regs 4 = E.LOC ∧ st.regs 5 = E.NAO

variable {E}

theorem R.of_regs {st st' : State} (h : E.R st)
    (he : ∀ r, r ≤ 5 → st'.regs r = st.regs r) : E.R st' := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h
  exact ⟨by rw [he 0 (by omega), a0], by rw [he 1 (by omega), a1], by rw [he 2 (by omega), a2],
    by rw [he 3 (by omega), a3], by rw [he 4 (by omega), a4], by rw [he 5 (by omega), a5]⟩

/-- The writes of entry `j` keep `Done`. -/
theorem Done.step {w N : ℕ} (h : E.Ok w N) {j : ℕ} {M : ℕ → ℕ} (hj : j < E.cnt)
    (hd : E.Done j M) :
    E.Done (j + 1) (Function.update (Function.update M (E.NAO + j) (E.x j)) (E.LOC + E.hd j) j) := by
  have hl := h.loc
  have hhj := (h.rd j hj).2.2.2
  obtain ⟨d1, d2, d3⟩ := hd
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun a ha => ?_⟩
  · rw [Function.update_of_ne (by omega)]
    by_cases hij : i = j
    · subst hij; exact Function.update_self _ _ _
    · rw [Function.update_of_ne (by omega)]; exact d1 i (by omega)
  · simp only [Function.update_apply]
    rcases Nat.lt_or_ge i j with hij | hij
    · have hne : E.hd i ≠ E.hd j := fun e => by have := h.inj i (by omega) j hj e; omega
      have hhi := (h.rd i (by omega)).2.2.2
      split_ifs <;> first | omega | exact d2 i hij
    · have : i = j := by omega
      subst this; simp
  · have h1 : ¬ (E.NAO ≤ a ∧ a < E.NAO + (j + 1)) := fun hh => ha (Or.inl hh)
    have h2 : a ≠ E.LOC + E.hd j := fun hh => ha (Or.inr ⟨j, by omega, hh⟩)
    have h3 : ¬ E.Out j a := fun hh => ha (by
      rcases hh with hh | ⟨i, hi, hh⟩
      · left; omega
      · right; exact ⟨i, by omega, hh⟩)
    simp only [Function.update_apply]
    split_ifs <;> first | omega | exact d3 a h3

end NCE

/-- One entry: the node, its head, and the two writes. -/
def ncIn : Stmt :=
  .seq (.assign 7 (.load (.bin .add (.reg 2) (.load (.bin .add (.reg 1) (.reg 6))))))
  (.seq (.assign 8 (.load (.bin .add (.reg 3) (.reg 7))))
  (.seq (.store (.bin .add (.reg 5) (.reg 6)) (.reg 7))
    (.store (.bin .add (.reg 4) (.reg 8)) (.reg 6))))

/-- `ncP` with `args = [cnt, SRC, NAX, HEAD, LOC, NAO]`. -/
def ncP : Stmt := .seq (forRange 6 (.const 0) (.reg 0) ncIn) (.ret (.const 0))

theorem ncP_noRand : ncP.NoRand := by
  simp [ncP, ncIn, forRange, forUp, Stmt.NoRand]

/-- The contract of `ncP`. -/
def ncC (w : ℕ) : Contract where
  pre args mem := ∃ E : NCE, ∃ N, args = E.args ∧ E.mem0 = mem ∧ E.Ok w N
  post args mem _ mem' := ∀ E : NCE, args = E.args → E.mem0 = mem → E.Done E.cnt mem'
  cost args _ := 60 * (args.getD 0 0 + 1)

namespace NCE

variable {w N : ℕ} {E : NCE}

/-- One entry of `ncP`. -/
theorem ncIn_runs {p : Program} (h : E.Ok w N) {st : State} (hR : E.R st) {j : ℕ}
    (h6 : st.regs 6 = j) (hj : j < E.cnt) (hd : E.Done j st.mem) (ω : ℕ → Bool) :
    ∃ o s' c, Runs w p ω ncIn st o s' c ∧
      (o = .normal ∧ E.R s' ∧ s'.regs 6 = j ∧ E.Done (j + 1) s'.mem) ∧ c ≤ 40 := by
  have hR' := hR
  have room := h.room
  have hl := h.loc
  obtain ⟨⟨r1, o1⟩, ⟨r2, o2⟩, ⟨r3, o3⟩, r4⟩ := h.rd j hj
  have lo : ∀ a, a < E.NAO → E.Off N a → st.mem a = E.mem0 a := fun a ha ho =>
    hd.2.2 a fun hout => by
      rcases hout with ⟨h1, -⟩ | ⟨i, hi, rfl⟩
      · omega
      · have := (h.rd i (by omega)).2.2.2; unfold Off at ho; omega
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := hR
  have m1 : st.mem (st.regs 1 + st.regs 6) = E.mem0 (E.SRC + j) := by
    rw [a1, h6]; exact lo _ r1 o1
  have m2 : st.mem (st.regs 2 + E.mem0 (E.SRC + j)) = E.x j := by
    rw [a2]; exact lo _ r2 o2
  have m3 : st.mem (st.regs 3 + E.x j) = E.hd j := by
    rw [a3]; exact lo _ r3 o3
  have b1 : st.regs 1 + st.regs 6 < 2 ^ w := by rw [a1, h6]; omega
  have b2 : st.regs 2 + E.mem0 (E.SRC + j) < 2 ^ w := by rw [a2]; omega
  have b3 : st.regs 3 + E.x j < 2 ^ w := by rw [a3]; omega
  have b4 : st.regs 5 + st.regs 6 < 2 ^ w := by rw [a5, h6]; omega
  have b5 : st.regs 4 + E.hd j < 2 ^ w := by rw [a4]; omega
  have c1 : st.regs 2 + st.mem (st.regs 1 + st.regs 6) < 2 ^ w := by rw [m1]; exact b2
  have c2 : st.regs 3 + st.mem (st.regs 2 + st.mem (st.regs 1 + st.regs 6)) < 2 ^ w := by
    rw [m1, m2]; exact b3
  have c3 : st.regs 4 + st.mem (st.regs 3 + st.mem (st.regs 2 + st.mem (st.regs 1 + st.regs 6)))
      < 2 ^ w := by rw [m1, m2, m3]; exact b5
  have e5 : st.regs 5 + st.regs 6 = E.NAO + j := by rw [a5, h6]
  have e4 : st.regs 4 = E.LOC := a4
  have hJ : st.regs 6 = j ∧ True := ⟨h6, trivial⟩
  clear a0 a1 a2 a3 a4 a5 h6 lo
  refine runs_start_le ?_
  dsimp only [ncIn]
  wram_run
  all_goals try wram_cost
  refine ⟨rfl, hR'.of_regs fun r hr => ?_, ?_, ?_⟩
  · simp only [Function.update_apply]
    split_ifs <;> first | omega | rfl
  · simpa using hJ.1
  simp only [m1]
  simp only [m2]
  simp only [m3, e5, e4]
  simp only [hJ.1]
  exact Done.step h hj hd

end NCE

theorem ncP_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [ncP]) :
    MeetsContract w p b (ncC w) := by
  intro args mem pos ω hwords hpre
  obtain ⟨E, N, rfl, hm, h⟩ := hpre
  subst hm
  have hproc : p.procs[b]? = some ncP := hp 0 (by simp)
  clear hp
  have room := h.room
  have hw1 : 1 < 2 ^ w := by omega
  have hloop := Triple.forRange_const (p := p) (r := 6) (lo := .const 0) (hi := .reg 0)
    (body := ncIn)
    (P := fun st => st = startState E.args E.mem0 pos)
    (Inv := fun j st => E.R st ∧ st.regs 6 = j ∧ E.Done j st.mem)
    40 0 E.cnt (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hst => by
      subst hst
      refine ⟨by eval_expr, NCE.R.of_regs (st := startState E.args E.mem0 pos)
        ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ fun r hr => ?_, by simp, fun i hi => by omega,
        fun i hi => by omega, fun a _ => rfl⟩
      simp only [Function.update_apply]; split_ifs <;> first | omega | rfl)
    (fun _ st _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by have := hI.1.1; eval_expr)
    (fun j _ hj st ω hI => by
      obtain ⟨hr, h6, hd⟩ := hI
      obtain ⟨o, s', c, hrun, ⟨rfl, hr', h6', hd'⟩, hc⟩ := NCE.ncIn_runs h hr h6 hj hd ω
      refine ⟨_, _, _, hrun, ⟨⟨hr'.of_regs fun r hr => ?_, by simp, hd'⟩, h6'⟩, hc⟩
      simp only [Function.update_apply]; split_ifs <;> first | omega | rfl)
  refine ⟨ncP, hproc, ?_⟩
  dsimp only [ncP]
  refine runs_start_le ?_
  refine runs_seq_triple_le hloop rfl (fun st hI => ?_)
  obtain ⟨-, -, hd⟩ := hI
  refine runs_ret_le (by eval_expr) ?_ ?_
  · intro E' he hm'
    have e : E' = E := by
      cases E; cases E'; simp only [NCE.args, List.cons.injEq] at he; simp_all
    subst e
    exact hd
  · simp only [ncC, NCE.args, Expr.size, List.getD_cons_zero] at *
    omega

end MinCostFlow.LowStretch
