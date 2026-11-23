module

public import WordRAM.Logic
public import WordRAM.Tactic

/-!
# The size and the largest weight of a child

For the super-vertices `NA[0], …, NA[cnt - 1]` of a child (Kruskal nodes), `smP` writes the sum
of their leaf counts `KSZ[x]` (the number of vertices of the child) at `OUT` and the largest of
their merge weights `KMW[x]` at `OUT + 1` (`smP_spec`). Both are what the reset rule reads. Each
node costs a constant.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The numbers of `smP`. -/
structure SME where
  cnt : ℕ
  NA : ℕ
  KSZ : ℕ
  KMW : ℕ
  OUT : ℕ
  mem0 : ℕ → ℕ

namespace SME

variable (E : SME)

/-- The arguments of `smP`. -/
def args : List ℕ := [E.cnt, E.NA, E.KSZ, E.KMW, E.OUT]

/-- The leaf count and the weight of node `i`. -/
def sz (i : ℕ) : ℕ := E.mem0 (E.KSZ + E.mem0 (E.NA + i))
def mw (i : ℕ) : ℕ := E.mem0 (E.KMW + E.mem0 (E.NA + i))

/-- The sum of the first `j` leaf counts and the largest of the first `j` weights. -/
def sum (j : ℕ) : ℕ := ∑ i ∈ Finset.range j, E.sz i
def mx (j : ℕ) : ℕ := (Finset.range j).sup E.mw

/-- The precondition: the cells read lie below `OUT` and the sum is a word. -/
structure Ok (w : ℕ) : Prop where
  rd : ∀ i < E.cnt, E.NA + i < E.OUT ∧ E.KSZ + E.mem0 (E.NA + i) < E.OUT ∧
    E.KMW + E.mem0 (E.NA + i) < E.OUT
  hsum : E.sum E.cnt < 2 ^ w
  room : E.OUT + E.cnt + 2 < 2 ^ w

/-- The registers that never change. -/
def R (st : State) : Prop :=
  st.regs 0 = E.cnt ∧ st.regs 1 = E.NA ∧ st.regs 2 = E.KSZ ∧ st.regs 3 = E.KMW ∧
    st.regs 4 = E.OUT ∧ st.mem = E.mem0

variable {E}

theorem R.of_regs {st st' : State} (h : E.R st)
    (he : ∀ r, r ≤ 4 → st'.regs r = st.regs r) (hm : st'.mem = st.mem) : E.R st' := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h
  exact ⟨by rw [he 0 (by omega), a0], by rw [he 1 (by omega), a1], by rw [he 2 (by omega), a2],
    by rw [he 3 (by omega), a3], by rw [he 4 (by omega), a4], by rw [hm, a5]⟩

theorem sum_mono {i j : ℕ} (h : i ≤ j) : E.sum i ≤ E.sum j :=
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr h)

end SME

/-- One node: add its leaf count, and keep the larger weight. -/
def smIn : Stmt :=
  .seq (.assign 8 (.load (.bin .add (.reg 1) (.reg 5))))
  (.seq (.assign 6 (.bin .add (.reg 6) (.load (.bin .add (.reg 2) (.reg 8)))))
  (.seq (.assign 9 (.load (.bin .add (.reg 3) (.reg 8))))
    (.cond (.bin .lt (.reg 7) (.reg 9)) (.assign 7 (.reg 9)) .nop)))

/-- `smP` with `args = [cnt, NA, KSZ, KMW, OUT]`. -/
def smP : Stmt :=
  .seq (.assign 6 (.const 0)) (.seq (.assign 7 (.const 0))
  (.seq (forRange 5 (.const 0) (.reg 0) smIn)
  (.seq (.store (.reg 4) (.reg 6)) (.seq (.store (.bin .add (.reg 4) (.const 1)) (.reg 7))
    (.ret (.const 0))))))

theorem smP_noRand : smP.NoRand := by
  simp [smP, smIn, forRange, forUp, Stmt.NoRand]

/-- The contract of `smP`. -/
def smC (w : ℕ) : Contract where
  pre args mem := ∃ E : SME, args = E.args ∧ E.mem0 = mem ∧ E.Ok w
  post args mem _ mem' := ∀ E : SME, args = E.args → E.mem0 = mem →
    mem' = Function.update (Function.update mem E.OUT (E.sum E.cnt)) (E.OUT + 1) (E.mx E.cnt)
  cost args _ := 50 * (args.getD 0 0 + 1)

namespace SME

variable {w : ℕ} {E : SME}

/-- One node of `smP`. -/
theorem smIn_runs {p : Program} (h : E.Ok w) {st : State} (hR : E.R st) {j : ℕ}
    (h5 : st.regs 5 = j) (h6 : st.regs 6 = E.sum j) (h7 : st.regs 7 = E.mx j) (hj : j < E.cnt)
    (ω : ℕ → Bool) :
    ∃ o s' c, Runs w p ω smIn st o s' c ∧
      (o = .normal ∧ E.R s' ∧ s'.regs 5 = j ∧ s'.regs 6 = E.sum (j + 1) ∧
        s'.regs 7 = E.mx (j + 1)) ∧ c ≤ 30 := by
  have hR' := hR
  obtain ⟨r1, r2, r3⟩ := h.rd j hj
  have hs := h.hsum
  have hsm := E.sum_mono (show j + 1 ≤ E.cnt by omega)
  have room := h.room
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := hR
  have m1 : st.mem (st.regs 1 + st.regs 5) = E.mem0 (E.NA + j) := by rw [a1, h5, a5]
  have m2 : st.mem (st.regs 2 + E.mem0 (E.NA + j)) = E.sz j := by rw [a2, a5]; rfl
  have m3 : st.mem (st.regs 3 + E.mem0 (E.NA + j)) = E.mw j := by rw [a3, a5]; rfl
  have esum : E.sum (j + 1) = E.sum j + E.sz j := Finset.sum_range_succ _ _
  have emx : E.mx (j + 1) = max (E.mx j) (E.mw j) := by
    unfold mx; rw [Finset.range_add_one, Finset.sup_insert, max_comm]
  have b1 : st.regs 1 + st.regs 5 < 2 ^ w := by rw [a1, h5]; omega
  have b2 : st.regs 2 + E.mem0 (E.NA + j) < 2 ^ w := by rw [a2]; omega
  have b3 : st.regs 3 + E.mem0 (E.NA + j) < 2 ^ w := by rw [a3]; omega
  have c1 : st.regs 2 + st.mem (st.regs 1 + st.regs 5) < 2 ^ w := by rw [m1]; exact b2
  have c2 : st.regs 3 + st.mem (st.regs 1 + st.regs 5) < 2 ^ w := by rw [m1]; exact b3
  have c3 : st.regs 6 + st.mem (st.regs 2 + st.mem (st.regs 1 + st.regs 5)) < 2 ^ w := by
    rw [m1, m2, h6]; omega
  have hJ : (st.regs 5 = j ∧ st.regs 6 = E.sum j ∧ st.regs 7 = E.mx j) ∧ True :=
    ⟨⟨h5, h6, h7⟩, trivial⟩
  clear a0 a1 a2 a3 a4 a5 h5 h6 h7
  refine runs_start_le ?_
  dsimp only [smIn]
  wram_run
  all_goals try wram_cost
  · refine ⟨rfl, hR'.of_regs (fun r hr => ?_) rfl, by simpa using hJ.1.1, ?_, ?_⟩
    · simp only [Function.update_apply]; split_ifs <;> first | omega | rfl
    · simp only [Function.update_apply, m1, m2, hJ.1.2.1, esum]; try simp
    · simp only [Function.update_apply, m1, m3] at hcond ⊢
      simp only [ite_true, emx, ← hJ.1.2.2]
      exact (max_eq_right hcond.le).symm
  · refine ⟨rfl, hR'.of_regs (fun r hr => ?_) rfl, by simpa using hJ.1.1, ?_, ?_⟩
    · simp only [Function.update_apply]; split_ifs <;> first | omega | rfl
    · simp only [Function.update_apply, m1, m2, hJ.1.2.1, esum]; try simp
    · simp only [Function.update_apply, m1, m3] at hcond ⊢
      simp only [emx, ← hJ.1.2.2]
      simp only [if_neg (show (7 : ℕ) ≠ 6 by omega), if_neg (show (7 : ℕ) ≠ 8 by omega)]
      exact (max_eq_left (not_lt.mp hcond)).symm

end SME

theorem smP_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [smP]) :
    MeetsContract w p b (smC w) := by
  intro args mem pos ω hwords hpre
  obtain ⟨E, rfl, hm, h⟩ := hpre
  subst hm
  have hproc : p.procs[b]? = some smP := hp 0 (by simp)
  clear hp
  have room := h.room
  have hw1 : 1 < 2 ^ w := by omega
  have hloop := Triple.forRange_const (p := p) (r := 5) (lo := .const 0) (hi := .reg 0)
    (body := smIn)
    (P := fun st => E.R st ∧ st.regs 6 = 0 ∧ st.regs 7 = 0)
    (Inv := fun j st => E.R st ∧ st.regs 5 = j ∧ st.regs 6 = E.sum j ∧ st.regs 7 = E.mx j)
    30 0 E.cnt (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hst => by
      obtain ⟨hr, h6, h7⟩ := hst
      refine ⟨by eval_expr, hr.of_regs (fun r hr => ?_) rfl, by simp, ?_, ?_⟩
      · simp only [Function.update_apply]; split_ifs <;> first | omega | rfl
      · simp only [Function.update_apply, if_neg (show (6 : ℕ) ≠ 5 by omega), h6]; rfl
      · simp only [Function.update_apply, if_neg (show (7 : ℕ) ≠ 5 by omega), h7]; rfl)
    (fun _ st _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by have := hI.1.1; eval_expr)
    (fun j _ hj st ω hI => by
      obtain ⟨hr, h5, h6, h7⟩ := hI
      obtain ⟨o, s', c, hrun, ⟨rfl, hr', h5', h6', h7'⟩, hc⟩ := SME.smIn_runs h hr h5 h6 h7 hj ω
      refine ⟨_, _, _, hrun, ⟨⟨hr'.of_regs (fun r hr => ?_) rfl, by simp, ?_, ?_⟩, h5'⟩, hc⟩
      · simp only [Function.update_apply]; split_ifs <;> first | omega | rfl
      · simp only [Function.update_apply, if_neg (show (6 : ℕ) ≠ 5 by omega), h6']
      · simp only [Function.update_apply, if_neg (show (7 : ℕ) ≠ 5 by omega), h7'])
  refine ⟨smP, hproc, ?_⟩
  dsimp only [smP]
  refine runs_start_le ?_
  refine runs_seq_assign_le (by eval_expr) ?_
  refine runs_seq_assign_le (by eval_expr) ?_
  refine runs_seq_triple_le hloop ⟨?_, by simp, by simp⟩ (fun st hI => ?_)
  · exact SME.R.of_regs (st := startState E.args E.mem0 pos) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      (fun r hr => by simp only [Function.update_apply]; split_ifs <;> first | omega | rfl) rfl
  obtain ⟨hr, -, h6, h7⟩ := hI
  have hr' := hr
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := hr
  have hs := h.hsum
  have b1 : st.regs 6 < 2 ^ w := by rw [h6]; exact hs
  have b2 : st.regs 4 + 1 < 2 ^ w := by rw [a4]; omega
  wram_run
  · intro E' he hm'
    have e : E' = E := by
      cases E; cases E'; simp only [SME.args, List.cons.injEq] at he; simp_all
    subst e
    dsimp only
    rw [a5]
  · simp only [smC, SME.args, Expr.size, List.getD_cons_zero] at *
    omega
