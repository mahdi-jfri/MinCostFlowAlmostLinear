module

public import WordRAM.Logic
public import WordRAM.Tactic

/-!
# The keys of the active pairs

After the petals, each active pair `p` of a cluster is sent to the child that holds both of its
ends, if there is one. `keyP` writes, for the active entry `i` (pair `p = ACT[2i]`), the key
`KEY[i]`: the child `CHX[a]` of the node `a` of its first end when the node `b` of its second end
has the same child, and `nch` otherwise (`keyP_spec`). The node of a vertex `v` is read through
its label: `LOC[LAB[v]]`. Then `csrB` on the keys groups the active entries by child.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The numbers of `keyP`. -/
structure KYE where
  nA : ℕ
  ACT : ℕ
  IN : ℕ
  LAB : ℕ
  LOC : ℕ
  CHX : ℕ
  nch : ℕ
  KEY : ℕ
  mem0 : ℕ → ℕ

namespace KYE

variable (E : KYE)

/-- The arguments of `keyP`. -/
def args : List ℕ := [E.nA, E.ACT, E.IN, E.LAB, E.LOC, E.CHX, E.nch, E.KEY]

/-- The pair of active entry `i`. -/
def pr (i : ℕ) : ℕ := E.mem0 (E.ACT + 2 * i)

/-- The first and second end of the pair of entry `i`. -/
def eu (i : ℕ) : ℕ := E.mem0 (E.IN + 3 * E.pr i)
def ev (i : ℕ) : ℕ := E.mem0 (E.IN + 3 * E.pr i + 1)

/-- The node of a vertex, through its label. -/
def nd (v : ℕ) : ℕ := E.mem0 (E.LOC + E.mem0 (E.LAB + v))

/-- The child of the node of a vertex. -/
def ch (v : ℕ) : ℕ := E.mem0 (E.CHX + E.nd v)

/-- The key of entry `i`. -/
def key (i : ℕ) : ℕ := if E.ch (E.eu i) = E.ch (E.ev i) then E.ch (E.eu i) else E.nch

/-- The cells read for the end `v` lie below `KEY`. -/
def RdV (v : ℕ) : Prop := E.LAB + v < E.KEY ∧ E.LOC + E.mem0 (E.LAB + v) < E.KEY ∧
  E.CHX + E.nd v < E.KEY

/-- The precondition: every cell read lies below the keys, which fit in the words. -/
structure Ok (w : ℕ) : Prop where
  rd : ∀ i < E.nA, E.ACT + 2 * i < E.KEY ∧ E.IN + 3 * E.pr i + 1 < E.KEY ∧
    E.RdV (E.eu i) ∧ E.RdV (E.ev i)
  room : E.KEY + E.nA + 1 < 2 ^ w
  nch : E.nch < 2 ^ w

/-- The registers that never change. -/
def R (st : State) : Prop :=
  st.regs 0 = E.nA ∧ st.regs 1 = E.ACT ∧ st.regs 2 = E.IN ∧ st.regs 3 = E.LAB ∧
    st.regs 4 = E.LOC ∧ st.regs 5 = E.CHX ∧ st.regs 6 = E.nch ∧ st.regs 7 = E.KEY

variable {E}

theorem R.upd {st : State} (h : E.R st) {r : ℕ} (hr : 8 ≤ r) (v : ℕ) :
    E.R { st with regs := Function.update st.regs r v } := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Function.update_apply] <;> rwa [ite_eq_right (by omega)]

theorem R.mem {st : State} (h : E.R st) (M : ℕ → ℕ) : E.R { st with mem := M } := h

end KYE

/-- One entry: the pair, its two ends, the children of their nodes, and the key. -/
def keyIn : Stmt :=
  .seq (.assign 9 (.load (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 8)))))
  (.seq (.assign 10 (.load (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg 9)))))
  (.seq (.assign 11 (.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg 9)))
      (.const 1))))
  (.seq (.assign 10 (.load (.bin .add (.reg 4) (.load (.bin .add (.reg 3) (.reg 10))))))
  (.seq (.assign 11 (.load (.bin .add (.reg 4) (.load (.bin .add (.reg 3) (.reg 11))))))
  (.seq (.assign 10 (.load (.bin .add (.reg 5) (.reg 10))))
  (.seq (.assign 11 (.load (.bin .add (.reg 5) (.reg 11))))
    (.cond (.bin .eq (.reg 10) (.reg 11)) (.store (.bin .add (.reg 7) (.reg 8)) (.reg 10))
      (.store (.bin .add (.reg 7) (.reg 8)) (.reg 6)))))))))

/-- `keyP` with `args = [nA, ACT, IN, LAB, LOC, CHX, nch, KEY]`. -/
def keyP : Stmt := .seq (forRange 8 (.const 0) (.reg 0) keyIn) (.ret (.const 0))

theorem keyP_noRand : keyP.NoRand := by
  simp [keyP, keyIn, forRange, forUp, Stmt.NoRand]

/-- The contract of `keyP`. -/
def keyC (w : ℕ) : Contract where
  pre args mem := ∃ E : KYE, args = E.args ∧ E.mem0 = mem ∧ E.Ok w
  post args mem _ mem' := ∀ E : KYE, args = E.args → E.mem0 = mem →
    (∀ i < E.nA, mem' (E.KEY + i) = E.key i) ∧
    ∀ a, (a < E.KEY ∨ E.KEY + E.nA ≤ a) → mem' a = mem a
  cost args _ := 120 * (args.getD 0 0 + 1)

/-- One entry of `keyP`: it writes the key of entry `j` and changes no register below `8`. -/
theorem keyIn_runs {w : ℕ} {p : Program} {E : KYE} (h : E.Ok w) {st : State} (hR : E.R st)
    {j : ℕ} (h8 : st.regs 8 = j) (hj : j < E.nA) (lo : ∀ a < E.KEY, st.mem a = E.mem0 a)
    (ω : ℕ → Bool) :
    ∃ o s' c, Runs w p ω keyIn st o s' c ∧
      (o = .normal ∧ E.R s' ∧ s'.regs 8 = j ∧
        s'.mem = Function.update st.mem (E.KEY + j) (E.key j)) ∧ c ≤ 100 := by
  have hR' := hR
  have room := h.room
  have hnch := h.nch
  obtain ⟨r1, r2, ⟨u1, u2, u3⟩, ⟨v1, v2, v3⟩⟩ := h.rd j hj
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := hR
  have m1 : st.mem (st.regs 1 + 2 * st.regs 8) = E.pr j := by rw [a1, h8]; exact lo _ r1
  have m2 : st.mem (st.regs 2 + 3 * E.pr j) = E.eu j := by rw [a2]; exact lo _ (by omega)
  have m3 : st.mem (st.regs 2 + 3 * E.pr j + 1) = E.ev j := by rw [a2]; exact lo _ r2
  have m4 : st.mem (st.regs 3 + E.eu j) = E.mem0 (E.LAB + E.eu j) := by rw [a3]; exact lo _ u1
  have m5 : st.mem (st.regs 3 + E.ev j) = E.mem0 (E.LAB + E.ev j) := by rw [a3]; exact lo _ v1
  have m6 : st.mem (st.regs 4 + E.mem0 (E.LAB + E.eu j)) = E.nd (E.eu j) := by
    rw [a4]; exact lo _ u2
  have m7 : st.mem (st.regs 4 + E.mem0 (E.LAB + E.ev j)) = E.nd (E.ev j) := by
    rw [a4]; exact lo _ v2
  have m8 : st.mem (st.regs 5 + E.nd (E.eu j)) = E.ch (E.eu j) := by rw [a5]; exact lo _ u3
  have m9 : st.mem (st.regs 5 + E.nd (E.ev j)) = E.ch (E.ev j) := by rw [a5]; exact lo _ v3
  have b1 : st.regs 1 + 2 * st.regs 8 < 2 ^ w := by rw [a1, h8]; omega
  have b2 : st.regs 2 + 3 * E.pr j + 1 < 2 ^ w := by rw [a2]; omega
  have b3 : st.regs 3 + E.eu j < 2 ^ w := by rw [a3]; omega
  have b4 : st.regs 3 + E.ev j < 2 ^ w := by rw [a3]; omega
  have b5 : st.regs 4 + E.mem0 (E.LAB + E.eu j) < 2 ^ w := by rw [a4]; omega
  have b6 : st.regs 4 + E.mem0 (E.LAB + E.ev j) < 2 ^ w := by rw [a4]; omega
  have b7 : st.regs 5 + E.nd (E.eu j) < 2 ^ w := by rw [a5]; omega
  have b8 : st.regs 5 + E.nd (E.ev j) < 2 ^ w := by rw [a5]; omega
  have b9 : st.regs 7 + st.regs 8 < 2 ^ w := by rw [a7, h8]; omega
  have c1 : 3 * st.mem (st.regs 1 + 2 * st.regs 8) + 1 < 2 ^ w := by
    rw [m1]; omega
  have c2 : st.regs 2 + 3 * st.mem (st.regs 1 + 2 * st.regs 8) + 1 < 2 ^ w := by
    rw [m1]; exact b2
  have c4 : st.regs 3 + st.mem (st.regs 2 + 3 * st.mem (st.regs 1 + 2 * st.regs 8)) < 2 ^ w := by
    rw [m1, m2]; exact b3
  have c5 :
      st.regs 3 + st.mem (st.regs 2 + 3 * st.mem (st.regs 1 + 2 * st.regs 8) + 1) < 2 ^ w := by
    rw [m1, m3]; exact b4
  have c6 :
      st.regs 4 + st.mem (st.regs 3 + st.mem (st.regs 2 + 3 * st.mem (st.regs 1 + 2 * st.regs 8))) < 2 ^ w := by
    rw [m1, m2, m4]; exact b5
  have c7 :
      st.regs 4 + st.mem (st.regs 3 + st.mem (st.regs 2 + 3 * st.mem (st.regs 1 + 2 * st.regs 8) + 1)) < 2 ^ w := by
    rw [m1, m3, m5]; exact b6
  have c8 :
      st.regs 5 + st.mem (st.regs 4 + st.mem (st.regs 3 + st.mem (st.regs 2 + 3 * st.mem (st.regs 1 + 2 * st.regs 8)))) < 2 ^ w := by
    rw [m1, m2, m4, m6]; exact b7
  have c9 :
      st.regs 5 + st.mem (st.regs 4 + st.mem (st.regs 3 + st.mem (st.regs 2 + 3 * st.mem (st.regs 1 + 2 * st.regs 8) + 1))) < 2 ^ w := by
    rw [m1, m3, m5, m7]; exact b8
  have e7 : st.regs 7 + st.regs 8 = E.KEY + j := by rw [a7, h8]
  have e6 : st.regs 6 = E.nch := a6
  have hkey : E.key j = if E.ch (E.eu j) = E.ch (E.ev j) then E.ch (E.eu j) else E.nch := rfl
  have hj8 : st.regs 8 = j ∧ True := ⟨h8, trivial⟩
  clear a0 a1 a2 a3 a4 a5 a6 a7 h8 lo
  refine runs_start_le ?_
  dsimp only [keyIn]
  wram_run
  all_goals try wram_cost
  · refine ⟨rfl, hR'.mem _ |>.upd (by omega) _ |>.upd (by omega) _ |>.upd (by omega) _
      |>.upd (by omega) _ |>.upd (by omega) _ |>.upd (by omega) _ |>.upd (by omega) _ |>.mem _,
      by simpa using hj8.1, ?_⟩
    simp only [m1, m2, m3, m4, m5, m6, m7, m8, m9] at hcond ⊢
    simp only [hkey, e7, if_pos hcond]
  · refine ⟨rfl, hR'.mem _ |>.upd (by omega) _ |>.upd (by omega) _ |>.upd (by omega) _
      |>.upd (by omega) _ |>.upd (by omega) _ |>.upd (by omega) _ |>.upd (by omega) _ |>.mem _,
      by simpa using hj8.1, ?_⟩
    simp only [m1, m2, m3, m4, m5, m6, m7, m8, m9] at hcond ⊢
    simp only [hkey, e7, e6, if_neg hcond]

theorem keyP_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [keyP]) :
    MeetsContract w p b (keyC w) := by
  intro args mem pos ω hwords hpre
  obtain ⟨E, rfl, hm, h⟩ := hpre
  subst hm
  have hproc : p.procs[b]? = some keyP := hp 0 (by simp)
  clear hp
  have room := h.room
  have hnch := h.nch
  have hw1 : 1 < 2 ^ w := by omega
  -- the memory after the entries before `j`
  let Done : ℕ → (ℕ → ℕ) → Prop := fun j M =>
    (∀ i < j, M (E.KEY + i) = E.key i) ∧ ∀ a, (a < E.KEY ∨ E.KEY + j ≤ a) → M a = E.mem0 a
  have hloop := Triple.forRange_const (p := p) (r := 8) (lo := .const 0) (hi := .reg 0)
    (body := keyIn)
    (P := fun st => st = startState E.args E.mem0 pos)
    (Inv := fun j st => E.R st ∧ st.regs 8 = j ∧ Done j st.mem)
    100 0 E.nA (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hst => by
      subst hst
      refine ⟨by eval_expr, KYE.R.upd ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by omega) _,
        by simp, fun i hi => by omega, fun a _ => rfl⟩)
    (fun _ st _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by have := hI.1.1; eval_expr)
    (fun j _ hj st ω hI => by
      obtain ⟨hr, h8, hd1, hd2⟩ := hI
      obtain ⟨o, s', c, hrun, ⟨rfl, hr', h8', hm⟩, hc⟩ :=
        keyIn_runs h hr h8 hj (fun a ha => hd2 a (Or.inl ha)) ω
      refine ⟨_, _, _, hrun, ⟨⟨hr'.upd (by omega) _, by simp, ?_, fun a ha => ?_⟩, h8'⟩, hc⟩
      · intro i hi
        dsimp only
        rw [hm]
        by_cases hij : i = j
        · subst hij; exact Function.update_self _ _ _
        · rw [Function.update_of_ne (by omega)]; exact hd1 i (by omega)
      · dsimp only
        rw [hm, Function.update_of_ne (by omega)]; exact hd2 a (by omega))
  refine ⟨keyP, hproc, ?_⟩
  dsimp only [keyP]
  refine runs_start_le ?_
  refine runs_seq_triple_le hloop rfl (fun st hI => ?_)
  obtain ⟨-, -, hd1, hd2⟩ := hI
  refine runs_ret_le (by eval_expr) ?_ ?_
  · intro E' he hm'
    have e : E' = E := by
      cases E; cases E'; simp only [KYE.args, List.cons.injEq] at he; simp_all
    subst e
    exact ⟨hd1, hd2⟩
  · simp only [keyC, KYE.args, Expr.size, List.getD_cons_zero] at *
    omega
