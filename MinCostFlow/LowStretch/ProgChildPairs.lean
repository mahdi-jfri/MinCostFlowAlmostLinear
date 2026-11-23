module

public import WordRAM.Logic
public import WordRAM.Tactic

/-!
# The stored pairs of a child

The active entries of a cluster are grouped by child (`csrB` on the keys of `keyP`). `pcP` copies
the group of a child into the stored pairs of its record. Entry `j` of the group is the active
entry `i = SRC[j]`, with pair `p = ACT[2i]` and flag `f = ACT[2i + 1]`. The new flag says whether
`p` is halved in the child: `f`, or `p` is the parent arc of the node `a` of one of its ends on
a marked highway (`HM[a] = 1` and `PP[a] = p`). The node of a vertex `v` is `LOC[LAB[v]]`. With
`keep = 0` all flags are `0`, as in the record of a reset child. `pcP` writes `p` and the flag at
`SA + 2 j` (`pcP_spec`). Each entry costs a constant.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The numbers of `pcP`. -/
structure PCE where
  cnt : ℕ
  SRC : ℕ
  ACT : ℕ
  IN : ℕ
  LAB : ℕ
  LOC : ℕ
  HM : ℕ
  PP : ℕ
  keep : ℕ
  SA : ℕ
  mem0 : ℕ → ℕ

namespace PCE

variable (E : PCE)

/-- The arguments of `pcP`. -/
def args : List ℕ := [E.cnt, E.SRC, E.ACT, E.IN, E.LAB, E.LOC, E.HM, E.PP, E.keep, E.SA]

/-- The active entry, the pair and the flag of entry `j`. -/
def it (j : ℕ) : ℕ := E.mem0 (E.SRC + j)
def pr (j : ℕ) : ℕ := E.mem0 (E.ACT + 2 * E.it j)
def fl (j : ℕ) : ℕ := E.mem0 (E.ACT + 2 * E.it j + 1)

/-- The ends of the pair of entry `j` and their nodes. -/
def eu (j : ℕ) : ℕ := E.mem0 (E.IN + 3 * E.pr j)
def ev (j : ℕ) : ℕ := E.mem0 (E.IN + 3 * E.pr j + 1)
def na (j : ℕ) : ℕ := E.mem0 (E.LOC + E.mem0 (E.LAB + E.eu j))
def nb (j : ℕ) : ℕ := E.mem0 (E.LOC + E.mem0 (E.LAB + E.ev j))

/-- The highway test at a node. -/
def tst (j a : ℕ) : ℕ := (if E.mem0 (E.PP + a) = E.pr j then 1 else 0) &&& E.mem0 (E.HM + a)

/-- The new flag of entry `j`. -/
def nf (j : ℕ) : ℕ := E.keep &&& (E.fl j ||| (E.tst j (E.na j) ||| E.tst j (E.nb j)))

/-- The precondition: every cell read lies below `SA`, and the marks and flags read are words. -/
structure Ok (w : ℕ) : Prop where
  rd : ∀ j < E.cnt, E.SRC + j < E.SA ∧ E.ACT + 2 * E.it j + 1 < E.SA ∧
    E.IN + 3 * E.pr j + 1 < E.SA ∧ E.LAB + E.eu j < E.SA ∧ E.LAB + E.ev j < E.SA ∧
    E.LOC + E.mem0 (E.LAB + E.eu j) < E.SA ∧ E.LOC + E.mem0 (E.LAB + E.ev j) < E.SA ∧
    E.HM + E.na j < E.SA ∧ E.HM + E.nb j < E.SA ∧ E.PP + E.na j < E.SA ∧ E.PP + E.nb j < E.SA
  words : ∀ j < E.cnt, E.fl j < 2 ^ w
  keep : E.keep < 2 ^ w
  room : E.SA + 2 * E.cnt + 1 < 2 ^ w

/-- The memory after the entries before `j`. -/
def Done (j : ℕ) (M : ℕ → ℕ) : Prop :=
  (∀ i < j, M (E.SA + 2 * i) = E.pr i ∧ M (E.SA + 2 * i + 1) = E.nf i) ∧
    ∀ a, (a < E.SA ∨ E.SA + 2 * j ≤ a) → M a = E.mem0 a

/-- The registers that never change. -/
def R (st : State) : Prop :=
  st.regs 0 = E.cnt ∧ st.regs 1 = E.SRC ∧ st.regs 2 = E.ACT ∧ st.regs 3 = E.IN ∧
    st.regs 4 = E.LAB ∧ st.regs 5 = E.LOC ∧ st.regs 6 = E.HM ∧ st.regs 7 = E.PP ∧
    st.regs 8 = E.keep ∧ st.regs 9 = E.SA

variable {E}

theorem R.of_regs {st st' : State} (h : E.R st)
    (he : ∀ r, r ≤ 9 → st'.regs r = st.regs r) : E.R st' := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
  exact ⟨by rw [he 0 (by omega), a0], by rw [he 1 (by omega), a1], by rw [he 2 (by omega), a2],
    by rw [he 3 (by omega), a3], by rw [he 4 (by omega), a4], by rw [he 5 (by omega), a5],
    by rw [he 6 (by omega), a6], by rw [he 7 (by omega), a7], by rw [he 8 (by omega), a8],
    by rw [he 9 (by omega), a9]⟩

theorem Done.step {j : ℕ} {M : ℕ → ℕ} (hd : E.Done j M) :
    E.Done (j + 1) (Function.update (Function.update M (E.SA + 2 * j) (E.pr j))
      (E.SA + 2 * j + 1) (E.nf j)) := by
  obtain ⟨d1, d2⟩ := hd
  refine ⟨fun i hi => ?_, fun a ha => ?_⟩
  · rcases Nat.lt_or_ge i j with hij | hij
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact d1 i hij
    · have : i = j := by omega
      subst this
      rw [Function.update_of_ne (by omega), Function.update_self, Function.update_self]
      exact ⟨rfl, rfl⟩
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact d2 a (by omega)

end PCE

/-- One entry of `pcP`. -/
def pcIn : Stmt :=
  .seq (.assign 11 (.load (.bin .add (.reg 1) (.reg 10))))
  (.seq (.assign 12 (.load (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 11)))))
  (.seq (.assign 13 (.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 11)))
    (.const 1))))
  (.seq (.assign 14 (.load (.bin .add (.reg 5) (.load (.bin .add (.reg 4)
    (.load (.bin .add (.reg 3) (.bin .mul (.const 3) (.reg 12)))))))))
  (.seq (.assign 15 (.load (.bin .add (.reg 5) (.load (.bin .add (.reg 4)
    (.load (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 3) (.reg 12))) (.const 1))))))))
  (.seq (.assign 16 (.bin .and (.bin .eq (.load (.bin .add (.reg 7) (.reg 14))) (.reg 12))
    (.load (.bin .add (.reg 6) (.reg 14)))))
  (.seq (.assign 17 (.bin .and (.bin .eq (.load (.bin .add (.reg 7) (.reg 15))) (.reg 12))
    (.load (.bin .add (.reg 6) (.reg 15)))))
  (.seq (.assign 18 (.bin .and (.reg 8) (.bin .or (.reg 13) (.bin .or (.reg 16) (.reg 17)))))
  (.seq (.store (.bin .add (.reg 9) (.bin .mul (.const 2) (.reg 10))) (.reg 12))
  ((.store (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 2) (.reg 10))) (.const 1))
    (.reg 18)))))))))))

/-- `pcP` with `args = [cnt, SRC, ACT, IN, LAB, LOC, HM, PP, keep, SA]`. -/
def pcP : Stmt := .seq (forRange 10 (.const 0) (.reg 0) pcIn) (.ret (.const 0))

theorem pcP_noRand : pcP.NoRand := by
  simp [pcP, pcIn, forRange, forUp, Stmt.NoRand]

/-- The contract of `pcP`. -/
def pcC (w : ℕ) : Contract where
  pre args mem := ∃ E : PCE, args = E.args ∧ E.mem0 = mem ∧ E.Ok w
  post args mem _ mem' := ∀ E : PCE, args = E.args → E.mem0 = mem → E.Done E.cnt mem'
  cost args _ := 200 * (args.getD 0 0 + 1)

namespace PCE

variable {w : ℕ} {E : PCE}

/-- One entry of `pcP`. -/
theorem pcIn_runs {p : Program} (h : E.Ok w) {st : State} (hR : E.R st) {j : ℕ}
    (h10 : st.regs 10 = j) (hj : j < E.cnt) (hd : E.Done j st.mem) (ω : ℕ → Bool) :
    ∃ o s' c, Runs w p ω pcIn st o s' c ∧
      (o = .normal ∧ E.R s' ∧ s'.regs 10 = j ∧ E.Done (j + 1) s'.mem) ∧ c ≤ 180 := by
  have hR' := hR
  have room := h.room
  have hkeep := h.keep
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11⟩ := h.rd j hj
  have lo : ∀ a, a < E.SA → st.mem a = E.mem0 a := fun a ha => hd.2 a (Or.inl ha)
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := hR
  have m1 : st.mem (st.regs 1 + st.regs 10) = E.it j := by rw [a1, h10]; exact lo _ r1
  have m2 : st.mem (st.regs 2 + 2 * E.it j) = E.pr j := by rw [a2]; exact lo _ (by omega)
  have m3 : st.mem (st.regs 2 + 2 * E.it j + 1) = E.fl j := by rw [a2]; exact lo _ r2
  have m4 : st.mem (st.regs 3 + 3 * E.pr j) = E.eu j := by rw [a3]; exact lo _ (by omega)
  have m5 : st.mem (st.regs 3 + 3 * E.pr j + 1) = E.ev j := by rw [a3]; exact lo _ r3
  have m6 : st.mem (st.regs 4 + E.eu j) = E.mem0 (E.LAB + E.eu j) := by rw [a4]; exact lo _ r4
  have m7 : st.mem (st.regs 4 + E.ev j) = E.mem0 (E.LAB + E.ev j) := by rw [a4]; exact lo _ r5
  have m8 : st.mem (st.regs 5 + E.mem0 (E.LAB + E.eu j)) = E.na j := by
    rw [a5]; exact lo _ r6
  have m9 : st.mem (st.regs 5 + E.mem0 (E.LAB + E.ev j)) = E.nb j := by
    rw [a5]; exact lo _ r7
  have m10 : st.mem (st.regs 6 + E.na j) = E.mem0 (E.HM + E.na j) := by rw [a6]; exact lo _ r8
  have m11 : st.mem (st.regs 6 + E.nb j) = E.mem0 (E.HM + E.nb j) := by rw [a6]; exact lo _ r9
  have m12 : st.mem (st.regs 7 + E.na j) = E.mem0 (E.PP + E.na j) := by rw [a7]; exact lo _ r10
  have m13 : st.mem (st.regs 7 + E.nb j) = E.mem0 (E.PP + E.nb j) := by rw [a7]; exact lo _ r11
  have b1 : st.regs 1 + st.regs 10 < 2 ^ w := by rw [a1, h10]; omega
  have b2 : st.regs 2 + 2 * E.it j + 1 < 2 ^ w := by rw [a2]; omega
  have b3 : st.regs 3 + 3 * E.pr j + 1 < 2 ^ w := by rw [a3]; omega
  have b4 : st.regs 4 + E.eu j < 2 ^ w := by rw [a4]; omega
  have b5 : st.regs 4 + E.ev j < 2 ^ w := by rw [a4]; omega
  have b6 : st.regs 5 + E.mem0 (E.LAB + E.eu j) < 2 ^ w := by rw [a5]; omega
  have b7 : st.regs 5 + E.mem0 (E.LAB + E.ev j) < 2 ^ w := by rw [a5]; omega
  have b8 : st.regs 7 + E.na j < 2 ^ w := by rw [a7]; omega
  have b9 : st.regs 7 + E.nb j < 2 ^ w := by rw [a7]; omega
  have b10 : st.regs 6 + E.na j < 2 ^ w := by rw [a6]; omega
  have b11 : st.regs 6 + E.nb j < 2 ^ w := by rw [a6]; omega
  have b12 : st.regs 9 + 2 * st.regs 10 + 1 < 2 ^ w := by rw [a9, h10]; omega
  have b13 : st.regs 8 < 2 ^ w := by rw [a8]; exact hkeep
  have c1 :
      st.regs 2 + 2 * st.mem (st.regs 1 + st.regs 10) + 1 < 2 ^ w := by
    rw [m1]; exact b2
  have c2 :
      st.regs 3 + 3 * st.mem (st.regs 2 + 2 * st.mem (st.regs 1 + st.regs 10)) + 1 < 2 ^ w := by
    rw [m1, m2]; exact b3
  have c3 :
      st.regs 4 + st.mem (st.regs 3 + 3 * st.mem (st.regs 2 + 2 * st.mem (st.regs 1 + st.regs 10))) < 2 ^ w := by
    rw [m1, m2, m4]; exact b4
  have c4 :
      st.regs 4 + st.mem (st.regs 3 + 3 * st.mem (st.regs 2 + 2 * st.mem (st.regs 1 + st.regs 10)) + 1) < 2 ^ w := by
    rw [m1, m2, m5]; exact b5
  have c5 :
      st.regs 5 + st.mem (st.regs 4 + st.mem (st.regs 3 + 3 * st.mem (st.regs 2 + 2 * st.mem (st.regs 1 + st.regs 10)))) < 2 ^ w := by
    rw [m1, m2, m4, m6]; exact b6
  have c6 :
      st.regs 5 + st.mem (st.regs 4 + st.mem (st.regs 3 + 3 * st.mem (st.regs 2 + 2 * st.mem (st.regs 1 + st.regs 10)) + 1)) < 2 ^ w := by
    rw [m1, m2, m5, m7]; exact b7
  have c7 :
      st.regs 7 + st.mem (st.regs 5 + st.mem (st.regs 4 + st.mem (st.regs 3 + 3 * st.mem (st.regs 2 + 2 * st.mem (st.regs 1 + st.regs 10))))) < 2 ^ w := by
    rw [m1, m2, m4, m6, m8]; exact b8
  have c8 :
      st.regs 7 + st.mem (st.regs 5 + st.mem (st.regs 4 + st.mem (st.regs 3 + 3 * st.mem (st.regs 2 + 2 * st.mem (st.regs 1 + st.regs 10)) + 1))) < 2 ^ w := by
    rw [m1, m2, m5, m7, m9]; exact b9
  have c11 :
      st.mem (st.regs 2 + 2 * st.mem (st.regs 1 + st.regs 10) + 1) < 2 ^ w := by
    rw [m1, m3]; exact h.words j hj
  have c12 :
      (if st.mem (st.regs 7 + st.mem (st.regs 5 + st.mem (st.regs 4 + st.mem (st.regs 3 + 3 * st.mem (st.regs 2 + 2 * st.mem (st.regs 1 + st.regs 10)))))) = st.mem (st.regs 2 + 2 * st.mem (st.regs 1 + st.regs 10)) then 1 else 0) < 2 ^ w := by
    split_ifs <;> omega
  have c13 :
      (if st.mem (st.regs 7 + st.mem (st.regs 5 + st.mem (st.regs 4 + st.mem (st.regs 3 + 3 * st.mem (st.regs 2 + 2 * st.mem (st.regs 1 + st.regs 10)) + 1)))) = st.mem (st.regs 2 + 2 * st.mem (st.regs 1 + st.regs 10)) then 1 else 0) < 2 ^ w := by
    split_ifs <;> omega
  have c12a :
      ((if st.mem (st.regs 7 + st.mem (st.regs 5 + st.mem (st.regs 4 + st.mem (st.regs 3 + 3 * st.mem (st.regs 2 + 2 * st.mem (st.regs 1 + st.regs 10)))))) = st.mem (st.regs 2 + 2 * st.mem (st.regs 1 + st.regs 10)) then 1 else 0) &&& st.mem (st.regs 6 + st.mem (st.regs 5 + st.mem (st.regs 4 + st.mem (st.regs 3 + 3 * st.mem (st.regs 2 + 2 * st.mem (st.regs 1 + st.regs 10))))))) < 2 ^ w := lt_of_le_of_lt Nat.and_le_left c12
  have c13a :
      ((if st.mem (st.regs 7 + st.mem (st.regs 5 + st.mem (st.regs 4 + st.mem (st.regs 3 + 3 * st.mem (st.regs 2 + 2 * st.mem (st.regs 1 + st.regs 10)) + 1)))) = st.mem (st.regs 2 + 2 * st.mem (st.regs 1 + st.regs 10)) then 1 else 0) &&& st.mem (st.regs 6 + st.mem (st.regs 5 + st.mem (st.regs 4 + st.mem (st.regs 3 + 3 * st.mem (st.regs 2 + 2 * st.mem (st.regs 1 + st.regs 10)) + 1))))) < 2 ^ w := lt_of_le_of_lt Nat.and_le_left c13
  have c14 :
      ((if st.mem (st.regs 7 + st.mem (st.regs 5 + st.mem (st.regs 4 + st.mem (st.regs 3 + 3 * st.mem (st.regs 2 + 2 * st.mem (st.regs 1 + st.regs 10)))))) = st.mem (st.regs 2 + 2 * st.mem (st.regs 1 + st.regs 10)) then 1 else 0) &&& st.mem (st.regs 6 + st.mem (st.regs 5 + st.mem (st.regs 4 + st.mem (st.regs 3 + 3 * st.mem (st.regs 2 + 2 * st.mem (st.regs 1 + st.regs 10))))))) ||| ((if st.mem (st.regs 7 + st.mem (st.regs 5 + st.mem (st.regs 4 + st.mem (st.regs 3 + 3 * st.mem (st.regs 2 + 2 * st.mem (st.regs 1 + st.regs 10)) + 1)))) = st.mem (st.regs 2 + 2 * st.mem (st.regs 1 + st.regs 10)) then 1 else 0) &&& st.mem (st.regs 6 + st.mem (st.regs 5 + st.mem (st.regs 4 + st.mem (st.regs 3 + 3 * st.mem (st.regs 2 + 2 * st.mem (st.regs 1 + st.regs 10)) + 1))))) < 2 ^ w := by
    exact Nat.or_lt_two_pow (lt_of_le_of_lt Nat.and_le_left c12) (lt_of_le_of_lt Nat.and_le_left c13)
  have c15 :
      st.regs 6 + st.mem (st.regs 5 + st.mem (st.regs 4 + st.mem (st.regs 3 + 3 * st.mem (st.regs 2 + 2 * st.mem (st.regs 1 + st.regs 10))))) < 2 ^ w := by
    rw [m1, m2, m4, m6, m8]; exact b10
  have c16 :
      st.regs 6 + st.mem (st.regs 5 + st.mem (st.regs 4 + st.mem (st.regs 3 + 3 * st.mem (st.regs 2 + 2 * st.mem (st.regs 1 + st.regs 10)) + 1))) < 2 ^ w := by
    rw [m1, m2, m5, m7, m9]; exact b11
  have e9 : st.regs 9 + 2 * st.regs 10 = E.SA + 2 * j := by rw [a9, h10]
  have e8 : st.regs 8 = E.keep := a8
  have hJ : st.regs 10 = j ∧ True := ⟨h10, trivial⟩
  clear a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 h10 lo
  refine runs_start_le ?_
  dsimp only [pcIn]
  wram_run
  all_goals try wram_cost
  refine ⟨rfl, hR'.of_regs fun r hr => ?_, ?_, ?_⟩
  · simp only [Function.update_apply]
    split_ifs <;> first | omega | rfl
  · simpa using hJ.1
  simp only [m1]
  simp only [m2, m3]
  simp only [m4, m5]
  simp only [m6, m7]
  simp only [m8, m9]
  simp only [m10, m11, m12, m13, e9, e8]
  exact Done.step hd

end PCE

theorem pcP_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [pcP]) :
    MeetsContract w p b (pcC w) := by
  intro args mem pos ω hwords hpre
  obtain ⟨E, rfl, hm, h⟩ := hpre
  subst hm
  have hproc : p.procs[b]? = some pcP := hp 0 (by simp)
  clear hp
  have room := h.room
  have hw1 : 1 < 2 ^ w := by omega
  have hloop := Triple.forRange_const (p := p) (r := 10) (lo := .const 0) (hi := .reg 0)
    (body := pcIn)
    (P := fun st => st = startState E.args E.mem0 pos)
    (Inv := fun j st => E.R st ∧ st.regs 10 = j ∧ E.Done j st.mem)
    180 0 E.cnt (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hst => by
      subst hst
      refine ⟨by eval_expr, PCE.R.of_regs (st := startState E.args E.mem0 pos)
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ fun r hr => ?_, by simp,
        fun i hi => by omega, fun a _ => rfl⟩
      simp only [Function.update_apply]; split_ifs <;> first | omega | rfl)
    (fun _ st _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by have := hI.1.1; eval_expr)
    (fun j _ hj st ω hI => by
      obtain ⟨hr, h10, hd⟩ := hI
      obtain ⟨o, s', c, hrun, ⟨rfl, hr', h10', hd'⟩, hc⟩ := PCE.pcIn_runs h hr h10 hj hd ω
      refine ⟨_, _, _, hrun, ⟨⟨hr'.of_regs fun r hr => ?_, by simp, hd'⟩, h10'⟩, hc⟩
      simp only [Function.update_apply]; split_ifs <;> first | omega | rfl)
  refine ⟨pcP, hproc, ?_⟩
  dsimp only [pcP]
  refine runs_start_le ?_
  refine runs_seq_triple_le hloop rfl (fun st hI => ?_)
  obtain ⟨-, -, hd⟩ := hI
  refine runs_ret_le (by eval_expr) ?_ ?_
  · intro E' he hm'
    have e : E' = E := by
      cases E; cases E'; simp only [PCE.args, List.cons.injEq] at he; simp_all
    subst e
    exact hd
  · simp only [pcC, PCE.args, Expr.size, List.getD_cons_zero] at *
    omega

end MinCostFlow.LowStretch
