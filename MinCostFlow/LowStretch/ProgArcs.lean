module

public import MinCostFlow.LowStretch.ProgCSR

/-!
# The arcs of a cluster: one item per direction of each stored pair

`arcFill` turns the stored pairs of a cluster into arc items. Stored pair number `j` is `p` with
half flag `f`. Its ends get their local indices through the labels: `a = LOC[LAB[pu p]]` and
`b = LOC[LAB[pv p]]`. Its length is `PW[p] >>> f`, and its class is `EXP[p] + 2 - f - lθ`. Item
`2j` is the arc from `a` to `b` and item `2j + 1` the arc back. A pair longer than `D` gives two
dummy items at the extra node `s`, of cost and class `0` (`arcFill_spec`).

Grouping the items by their tails (`csrB`) and copying them in that order then gives the arc
form that Dijkstra reads.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The addresses and numbers that `arcFill` uses. -/
structure AF where
  s : ℕ
  nS : ℕ
  SA : ℕ
  IN : ℕ
  PW : ℕ
  EXP : ℕ
  LAB : ℕ
  LOC : ℕ
  D : ℕ
  lθ : ℕ
  TL : ℕ
  HDt : ℕ
  CSt : ℕ
  CLt : ℕ

namespace AF

variable (F : AF) (mem : ℕ → ℕ)

def args : List ℕ :=
  [F.s, F.nS, F.SA, F.IN, F.PW, F.EXP, F.LAB, F.LOC, F.D, F.lθ, F.TL, F.HDt, F.CSt, F.CLt]

/-- The pair of stored entry `j`. -/
def pr (j : ℕ) : ℕ := mem (F.SA + 2 * j)

/-- The half flag of stored entry `j`. -/
def fl (j : ℕ) : ℕ := mem (F.SA + 2 * j + 1)

/-- The local index of the first end. -/
def ea (j : ℕ) : ℕ := mem (F.LOC + mem (F.LAB + mem (F.IN + 3 * F.pr mem j)))

/-- The local index of the second end. -/
def eb (j : ℕ) : ℕ := mem (F.LOC + mem (F.LAB + mem (F.IN + 3 * F.pr mem j + 1)))

/-- The length. -/
def ln (j : ℕ) : ℕ := mem (F.PW + F.pr mem j) >>> F.fl mem j

/-- The class. -/
def cl (j : ℕ) : ℕ := mem (F.EXP + F.pr mem j) + 2 - F.fl mem j - F.lθ

/-- The entry is kept: its length is at most `D`. -/
def keep (j : ℕ) : Prop := F.ln mem j ≤ F.D

open Classical in
/-- The tail of item `2j`. -/
noncomputable def ta (j : ℕ) : ℕ := if F.keep mem j then F.ea mem j else F.s

open Classical in
/-- The tail of item `2j + 1`. -/
noncomputable def tb (j : ℕ) : ℕ := if F.keep mem j then F.eb mem j else F.s

open Classical in
/-- The cost of both items. -/
noncomputable def cs (j : ℕ) : ℕ := if F.keep mem j then F.ln mem j else 0

open Classical in
/-- The class of both items. -/
noncomputable def cc (j : ℕ) : ℕ := if F.keep mem j then F.cl mem j else 0

/-- The memory after the first `i` entries: the items of entry `j < i`. -/
def Done (M : ℕ → ℕ) (i : ℕ) : Prop :=
  ∀ j < i, M (F.TL + 2 * j) = F.ta mem j ∧ M (F.TL + 2 * j + 1) = F.tb mem j ∧
    M (F.HDt + 2 * j) = F.tb mem j ∧ M (F.HDt + 2 * j + 1) = F.ta mem j ∧
    M (F.CSt + 2 * j) = F.cs mem j ∧ M (F.CSt + 2 * j + 1) = F.cs mem j ∧
    M (F.CLt + 2 * j) = F.cc mem j ∧ M (F.CLt + 2 * j + 1) = F.cc mem j

/-- The written cells. -/
def Out (a : ℕ) : Prop := F.TL ≤ a ∧ a < F.CLt + 2 * F.nS

end AF

/-- The body of the loop of `arcFill`, for entry `i` in register `14`. -/
def arcFillB : Stmt :=
  .seq (.assign 15 (.load (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 14)))))
  (.seq (.assign 16 (.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 14)))
    (.const 1))))
  (.seq (.assign 17 (.load (.bin .add (.reg 3) (.bin .mul (.const 3) (.reg 15)))))
  (.seq (.assign 18 (.load (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 3) (.reg 15)))
    (.const 1))))
  (.seq (.assign 17 (.load (.bin .add (.reg 7) (.load (.bin .add (.reg 6) (.reg 17))))))
  (.seq (.assign 18 (.load (.bin .add (.reg 7) (.load (.bin .add (.reg 6) (.reg 18))))))
  (.seq (.assign 19 (.bin .shiftRight (.load (.bin .add (.reg 4) (.reg 15))) (.reg 16)))
  (.seq (.assign 20 (.bin .sub (.bin .sub (.bin .add (.load (.bin .add (.reg 5) (.reg 15)))
    (.const 2)) (.reg 16)) (.reg 9)))
  (.seq (.cond (.bin .lt (.reg 8) (.reg 19))
    (.seq (.assign 17 (.reg 0)) (.seq (.assign 18 (.reg 0))
      (.seq (.assign 19 (.const 0)) (.assign 20 (.const 0)))))
    .nop)
  (.seq (.store (.bin .add (.reg 10) (.bin .mul (.const 2) (.reg 14))) (.reg 17))
  (.seq (.store (.bin .add (.bin .add (.reg 10) (.bin .mul (.const 2) (.reg 14))) (.const 1))
    (.reg 18))
  (.seq (.store (.bin .add (.reg 11) (.bin .mul (.const 2) (.reg 14))) (.reg 18))
  (.seq (.store (.bin .add (.bin .add (.reg 11) (.bin .mul (.const 2) (.reg 14))) (.const 1))
    (.reg 17))
  (.seq (.store (.bin .add (.reg 12) (.bin .mul (.const 2) (.reg 14))) (.reg 19))
  (.seq (.store (.bin .add (.bin .add (.reg 12) (.bin .mul (.const 2) (.reg 14))) (.const 1))
    (.reg 19))
  (.seq (.store (.bin .add (.reg 13) (.bin .mul (.const 2) (.reg 14))) (.reg 20))
    (.store (.bin .add (.bin .add (.reg 13) (.bin .mul (.const 2) (.reg 14))) (.const 1))
      (.reg 20)))))))))))))))))

/-- `arcFill` with `args = F.args`. -/
def arcFill : Stmt := .seq (forRange 14 (.const 0) (.reg 1) arcFillB) (.ret (.const 0))

theorem arcFill_noRand : arcFill.NoRand := by
  simp [arcFill, arcFillB, forRange, forUp, Stmt.NoRand]

/-- The precondition of `arcFill`: the stored pairs, their ends, labels and local indices are
words, and the four item arrays lie in order, after every array that is read. -/
structure AF.Pre (F : AF) (w : ℕ) (mem : ℕ → ℕ) (m n NL : ℕ) : Prop where
  pr_lt : ∀ j < F.nS, F.pr mem j < m
  fl_le : ∀ j < F.nS, F.fl mem j ≤ 1
  ends : ∀ p < m, mem (F.IN + 3 * p) < n ∧ mem (F.IN + 3 * p + 1) < n
  lab : ∀ j < F.nS, mem (F.LAB + mem (F.IN + 3 * F.pr mem j)) < NL ∧
    mem (F.LAB + mem (F.IN + 3 * F.pr mem j + 1)) < NL
  loc : ∀ j < F.nS, F.ea mem j < 2 ^ w ∧ F.eb mem j < 2 ^ w
  pw : ∀ p < m, mem (F.PW + p) < 2 ^ w
  ex : ∀ p < m, mem (F.EXP + p) + 2 < 2 ^ w
  l1 : F.TL + 2 * F.nS ≤ F.HDt
  l2 : F.HDt + 2 * F.nS ≤ F.CSt
  l3 : F.CSt + 2 * F.nS ≤ F.CLt
  l4 : F.CLt + 2 * F.nS < 2 ^ w
  rSA : F.SA + 2 * F.nS ≤ F.TL ∨ F.CLt + 2 * F.nS ≤ F.SA
  lSA : F.SA + 2 * F.nS < 2 ^ w
  rIN : F.IN + 3 * m ≤ F.TL
  rPW : F.PW + m ≤ F.TL
  rEXP : F.EXP + m ≤ F.TL
  rLAB : F.LAB + n ≤ F.TL
  rLOC : F.LOC + NL ≤ F.TL
  hs : F.s < 2 ^ w
  hw : 1 < 2 ^ w

/-- One entry of `arcFill`: the eight stores, given by their addresses and values. -/
theorem AF.Done.step {F : AF} {mem M : ℕ → ℕ} {i : ℕ} (hd : F.Done mem M i)
    (l1 : F.TL + 2 * F.nS ≤ F.HDt) (l2 : F.HDt + 2 * F.nS ≤ F.CSt)
    (l3 : F.CSt + 2 * F.nS ≤ F.CLt) (hi : i < F.nS)
    {A1 A2 A3 A4 A5 A6 A7 A8 V1 V2 V3 V4 V5 V6 V7 V8 : ℕ}
    (e1 : A1 = F.TL + 2 * i) (f1 : V1 = F.ta mem i)
    (e2 : A2 = F.TL + 2 * i + 1) (f2 : V2 = F.tb mem i)
    (e3 : A3 = F.HDt + 2 * i) (f3 : V3 = F.tb mem i)
    (e4 : A4 = F.HDt + 2 * i + 1) (f4 : V4 = F.ta mem i)
    (e5 : A5 = F.CSt + 2 * i) (f5 : V5 = F.cs mem i)
    (e6 : A6 = F.CSt + 2 * i + 1) (f6 : V6 = F.cs mem i)
    (e7 : A7 = F.CLt + 2 * i) (f7 : V7 = F.cc mem i)
    (e8 : A8 = F.CLt + 2 * i + 1) (f8 : V8 = F.cc mem i) :
    F.Done mem (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update M A1 V1) A2 V2) A3 V3)
      A4 V4) A5 V5) A6 V6) A7 V7) A8 V8) (i + 1) ∧
    ∀ a, ¬ F.Out a → Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update M A1 V1) A2 V2) A3 V3)
      A4 V4) A5 V5) A6 V6) A7 V7) A8 V8 a = M a := by
  subst A1 A2 A3 A4 A5 A6 A7 A8 V1 V2 V3 V4 V5 V6 V7 V8
  refine ⟨fun j hj => ?_, fun a ha => ?_⟩
  · by_cases e : j = i
    · subst e
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp (disch := omega) only [Function.update_of_ne, Function.update_self]
    · obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := hd j (by omega)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp (disch := omega) only [Function.update_of_ne] <;> assumption
  · unfold AF.Out at ha
    simp (disch := omega) only [Function.update_of_ne]

/-- The contract of `arcFill`. -/
def arcFillC (w : ℕ) : Contract where
  pre args mem := ∃ F : AF, ∃ m n NL, args = F.args ∧ F.Pre w mem m n NL
  post args mem _ mem' := ∀ F : AF, args = F.args →
    F.Done mem mem' F.nS ∧ ∀ a, ¬ F.Out a → mem' a = mem a
  cost args _ := 320 * args.getD 1 0 + 20

theorem AF.eq_of_args {F F' : AF} (h : F.args = F'.args) : F' = F := by
  cases F; cases F'; simp only [AF.args, List.cons.injEq] at h
  simp_all

set_option maxHeartbeats 4000000 in
theorem arcFill_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [arcFill]) :
    MeetsContract w p b (arcFillC w) := by
  intro args mem pos ω hwords hpre
  obtain ⟨F, m, n, NL, rfl, h⟩ := hpre
  have hproc : p.procs[b]? = some arcFill := hp 0 (by simp)
  clear hp
  have l1 := h.l1; have l2 := h.l2; have l3 := h.l3; have l4 := h.l4
  have rIN := h.rIN; have rPW := h.rPW; have rEXP := h.rEXP; have rLAB := h.rLAB
  have rLOC := h.rLOC; have hs := h.hs
  have hw1 : 1 < 2 ^ w := h.hw
  -- the registers that do not change
  let R : State → Prop := fun st => st.regs 0 = F.s ∧ st.regs 1 = F.nS ∧ st.regs 2 = F.SA ∧
    st.regs 3 = F.IN ∧ st.regs 4 = F.PW ∧ st.regs 5 = F.EXP ∧ st.regs 6 = F.LAB ∧
    st.regs 7 = F.LOC ∧ st.regs 8 = F.D ∧ st.regs 9 = F.lθ ∧ st.regs 10 = F.TL ∧
    st.regs 11 = F.HDt ∧ st.regs 12 = F.CSt ∧ st.regs 13 = F.CLt
  have hRu : ∀ st r v, R st → 14 ≤ r → R { st with regs := Function.update st.regs r v } := by
    intro st r v ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ hr
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Function.update_apply] <;> (rw [if_neg (by omega)]; assumption)
  have hRm : ∀ st M, R st → R { st with mem := M } := fun _ _ h => h
  let I : ℕ → State → Prop := fun i st => R st ∧ st.regs 14 = i ∧ F.Done mem st.mem i ∧
    ∀ a, ¬ F.Out a → st.mem a = mem a
  have hloop := Triple.forRange_const (p := p) (r := 14) (lo := .const 0) (hi := .reg 1)
    (body := arcFillB) (P := fun st => R st ∧ st.mem = mem) (Inv := I) 300 0 F.nS
    (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st ⟨hr, hm⟩ => ⟨by eval_expr, hRu st 14 0 hr (by omega), by simp,
      fun j hj => absurd hj (by omega), fun a _ => by simp [hm]⟩)
    (fun _ st _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by have := hI.1.2.1; eval_expr)
    (fun i _ hi st ω hI => by
      obtain ⟨hr, h14, hdone, hfr⟩ := hI
      have hr' := hr
      obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := hr
      have hpm := h.pr_lt i hi
      have hfl := h.fl_le i hi
      obtain ⟨hun, hvn⟩ := h.ends _ hpm
      have hlu := (h.lab i hi).1
      have hlv := (h.lab i hi).2
      -- the values read, from the memory at the start
      have nOut : ∀ a, (a < F.TL ∨ F.CLt + 2 * F.nS ≤ a) → ¬ F.Out a := by
        intro a ha ho; unfold AF.Out at ho; omega
      have eP : st.mem (F.SA + 2 * i) = F.pr mem i :=
        hfr _ (nOut _ (by rcases h.rSA with e | e <;> omega))
      have eF : st.mem (F.SA + 2 * i + 1) = F.fl mem i :=
        hfr _ (nOut _ (by rcases h.rSA with e | e <;> omega))
      have eU : st.mem (F.IN + 3 * F.pr mem i) = mem (F.IN + 3 * F.pr mem i) :=
        hfr _ (nOut _ (by omega))
      have eV : st.mem (F.IN + 3 * F.pr mem i + 1) = mem (F.IN + 3 * F.pr mem i + 1) :=
        hfr _ (nOut _ (by omega))
      have eLU : st.mem (F.LAB + mem (F.IN + 3 * F.pr mem i)) =
          mem (F.LAB + mem (F.IN + 3 * F.pr mem i)) := hfr _ (nOut _ (by omega))
      have eLV : st.mem (F.LAB + mem (F.IN + 3 * F.pr mem i + 1)) =
          mem (F.LAB + mem (F.IN + 3 * F.pr mem i + 1)) := hfr _ (nOut _ (by omega))
      have eA : st.mem (F.LOC + mem (F.LAB + mem (F.IN + 3 * F.pr mem i))) = F.ea mem i :=
        hfr _ (nOut _ (by omega))
      have eB : st.mem (F.LOC + mem (F.LAB + mem (F.IN + 3 * F.pr mem i + 1))) = F.eb mem i :=
        hfr _ (nOut _ (by omega))
      have eW : st.mem (F.PW + F.pr mem i) = mem (F.PW + F.pr mem i) := hfr _ (nOut _ (by omega))
      have eE : st.mem (F.EXP + F.pr mem i) = mem (F.EXP + F.pr mem i) :=
        hfr _ (nOut _ (by omega))
      have bA : F.ea mem i < 2 ^ w := (h.loc i hi).1
      have bB : F.eb mem i < 2 ^ w := (h.loc i hi).2
      have bW : mem (F.PW + F.pr mem i) < 2 ^ w := h.pw _ hpm
      have bE : mem (F.EXP + F.pr mem i) + 2 < 2 ^ w := h.ex _ hpm
      have hln : F.ln mem i = mem (F.PW + F.pr mem i) >>> F.fl mem i := rfl
      have hcl : F.cl mem i = mem (F.EXP + F.pr mem i) + 2 - F.fl mem i - F.lθ := rfl
      have hlSA := h.lSA
      have hrSA := h.rSA
      have bU : st.mem (st.regs 3 + 3 * st.mem (F.SA + 2 * i)) < n := by rw [a3, eP, eU]; exact hun
      have bV : st.mem (st.regs 3 + 3 * st.mem (F.SA + 2 * i) + 1) < n := by
        rw [a3, eP, eV]; exact hvn
      have bLU : st.mem (st.regs 6 + st.mem (st.regs 3 + 3 * st.mem (F.SA + 2 * i))) < NL := by
        rw [a6, a3, eP, eU, eLU]; exact hlu
      have bLV : st.mem (st.regs 6 + st.mem (st.regs 3 + 3 * st.mem (F.SA + 2 * i) + 1)) < NL := by
        rw [a6, a3, eP, eV, eLV]; exact hlv
      have bW' : st.mem (st.regs 4 + st.mem (F.SA + 2 * i)) < 2 ^ w := by rw [a4, eP, eW]; exact bW
      have bE' : st.mem (st.regs 5 + st.mem (F.SA + 2 * i)) + 2 < 2 ^ w := by
        rw [a5, eP, eE]; exact bE
      have bA' : st.mem (st.regs 7 + st.mem (st.regs 6 + st.mem (st.regs 3 + 3 *
          st.mem (F.SA + 2 * i)))) < 2 ^ w := by rw [a7, a6, a3, eP, eU, eLU, eA]; exact bA
      have bB' : st.mem (st.regs 7 + st.mem (st.regs 6 + st.mem (st.regs 3 + 3 *
          st.mem (F.SA + 2 * i) + 1))) < 2 ^ w := by rw [a7, a6, a3, eP, eV, eLV, eB]; exact bB
      have eA' : st.mem (st.regs 7 + st.mem (st.regs 6 + st.mem (st.regs 3 + 3 *
          st.mem (F.SA + 2 * i)))) = F.ea mem i := by rw [a7, a6, a3, eP, eU, eLU, eA]
      have eB' : st.mem (st.regs 7 + st.mem (st.regs 6 + st.mem (st.regs 3 + 3 *
          st.mem (F.SA + 2 * i) + 1))) = F.eb mem i := by rw [a7, a6, a3, eP, eV, eLV, eB]
      have eL' : st.mem (st.regs 4 + st.mem (F.SA + 2 * i)) >>>
          st.mem (st.regs 2 + 2 * st.regs 14 + 1) = F.ln mem i := by
        rw [a4, eP, eW, a2, h14, eF]; rfl
      have eC' : st.mem (st.regs 5 + st.mem (F.SA + 2 * i)) + 2 -
          st.mem (st.regs 2 + 2 * st.regs 14 + 1) - st.regs 9 = F.cl mem i := by
        rw [a5, eP, eE, a2, h14, eF, a9]; rfl
      have hRn : ∀ st' : State, (∀ r < 14, st'.regs r = st.regs r) → R st' := fun st' hs =>
        ⟨(hs 0 (by omega)).trans a0, (hs 1 (by omega)).trans a1, (hs 2 (by omega)).trans a2,
          (hs 3 (by omega)).trans a3, (hs 4 (by omega)).trans a4, (hs 5 (by omega)).trans a5,
          (hs 6 (by omega)).trans a6, (hs 7 (by omega)).trans a7, (hs 8 (by omega)).trans a8,
          (hs 9 (by omega)).trans a9, (hs 10 (by omega)).trans a10, (hs 11 (by omega)).trans a11,
          (hs 12 (by omega)).trans a12, (hs 13 (by omega)).trans a13⟩
      have key := AF.Done.step hdone l1 l2 l3 hi (M := st.mem) (A1 := _) (A2 := _) (A3 := _)
        (A4 := _) (A5 := _) (A6 := _) (A7 := _) (A8 := _) (V1 := _) (V2 := _) (V3 := _)
        (V4 := _) (V5 := _) (V6 := _) (V7 := _) (V8 := _) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        rfl rfl rfl rfl rfl rfl
      refine runs_start_le ?_
      dsimp only [arcFillB]
      wram_run
      · have hk : ¬ F.keep mem i := by
          unfold AF.keep; rw [a8, eL'] at hcond; exact Nat.not_le.mpr hcond
        refine ⟨⟨hRn _ (fun r hr => by simp only [Function.update_apply]; split_ifs <;> omega),
          by simp, ?_, fun a ha => ?_⟩, by simp [h14]⟩
        · convert key.1 using 2 <;>
            simp [AF.ta, AF.tb, AF.cs, AF.cc, hk, a0, a2, a3, a4, a5, a6, a7, a9, a10, a11, a12, a13, h14, eP, eF,
              eU, eV, eLU, eLV, eA, eB, eW, eE, ← hln, ← hcl]
        · refine Eq.trans ?_ ((key.2 a ha).trans (hfr a ha))
          congr 1 <;> simp [AF.ta, AF.tb, AF.cs, AF.cc, hk, a0, a2, a3, a4, a5, a6, a7, a9, a10, a11, a12, a13, h14, eP, eF,
              eU, eV, eLU, eLV, eA, eB, eW, eE, ← hln, ← hcl]
      · wram_cost
      · have hk : F.keep mem i := by
          unfold AF.keep; rw [a8, eL'] at hcond; exact Nat.not_lt.mp hcond
        refine ⟨⟨hRn _ (fun r hr => by simp only [Function.update_apply]; split_ifs <;> omega),
          by simp, ?_, fun a ha => ?_⟩, by simp [h14]⟩
        · convert key.1 using 2 <;>
            simp [AF.ta, AF.tb, AF.cs, AF.cc, hk, a0, a2, a3, a4, a5, a6, a7, a9, a10, a11, a12, a13, h14, eP, eF,
              eU, eV, eLU, eLV, eA, eB, eW, eE, ← hln, ← hcl]
        · refine Eq.trans ?_ ((key.2 a ha).trans (hfr a ha))
          congr 1 <;>
            simp [AF.ta, AF.tb, AF.cs, AF.cc, hk, a0, a2, a3, a4, a5, a6, a7, a9, a10, a11, a12, a13, h14, eP, eF,
              eU, eV, eLU, eLV, eA, eB, eW, eE, ← hln, ← hcl]
      · wram_cost)
  refine ⟨arcFill, hproc, ?_⟩
  dsimp only [arcFill]
  refine runs_start_le ?_
  refine runs_seq_triple_le hloop ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl⟩, rfl⟩ (fun st hI => ?_)
  obtain ⟨-, -, hdone, hfr⟩ := hI
  refine runs_ret_le (by eval_expr) (fun F' he => ?_) ?_
  · obtain rfl := AF.eq_of_args he
    exact ⟨hdone, hfr⟩
  · simp only [arcFillC, AF.args, List.getD_cons_zero, List.getD_cons_succ, Expr.size]
    omega


/-! ### Copying the items in the order of their tails -/

/-- The addresses that `arcCopy` uses. -/
structure AC where
  M : ℕ
  ORD : ℕ
  HDt : ℕ
  CSt : ℕ
  CLt : ℕ
  HD : ℕ
  CS : ℕ
  CL : ℕ
  OK : ℕ
  s : ℕ
  os : ℕ

namespace AC

def args (C : AC) : List ℕ := [C.M, C.ORD, C.HDt, C.CSt, C.CLt, C.HD, C.CS, C.CL, C.OK, C.s, C.os]

theorem eq_of_args {C C' : AC} (h : C.args = C'.args) : C' = C := by
  cases C; cases C'; simp only [AC.args, List.cons.injEq] at h
  simp_all

/-- The precondition: item numbers below `M`, and the written arrays after the read ones. -/
structure Pre (C : AC) (w : ℕ) (mem : ℕ → ℕ) : Prop where
  ord : ∀ j < C.M, mem (C.ORD + j) < C.M
  vHD : ∀ i < C.M, mem (C.HDt + i) < 2 ^ w
  vCS : ∀ i < C.M, mem (C.CSt + i) < 2 ^ w
  vCL : ∀ i < C.M, mem (C.CLt + i) < 2 ^ w
  r1 : C.ORD + C.M ≤ C.HD
  r2 : C.HDt + C.M ≤ C.HD
  r3 : C.CSt + C.M ≤ C.HD
  r4 : C.CLt + C.M ≤ C.HD
  l1 : C.HD + C.M ≤ C.CS
  l2 : C.CS + C.M ≤ C.CL
  l3 : C.CL + C.M ≤ C.OK
  l4 : C.OK + C.s + 1 < 2 ^ w
  los : C.os + 1 < 2 ^ w

/-- The written cells. -/
def Out (C : AC) (a : ℕ) : Prop := C.HD ≤ a ∧ a ≤ C.OK + C.s

/-- After the first `j` items. -/
def Done1 (C : AC) (mem M : ℕ → ℕ) (j : ℕ) : Prop :=
  ∀ k < j, M (C.HD + k) = mem (C.HDt + mem (C.ORD + k)) ∧
    M (C.CS + k) = mem (C.CSt + mem (C.ORD + k)) ∧ M (C.CL + k) = mem (C.CLt + mem (C.ORD + k))

end AC

theorem AC.Done1.step {C : AC} {mem M : ℕ → ℕ} {j : ℕ} (hd : C.Done1 mem M j)
    (l1 : C.HD + C.M ≤ C.CS) (l2 : C.CS + C.M ≤ C.CL) (hj : j < C.M)
    {A1 A2 A3 V1 V2 V3 : ℕ}
    (e1 : A1 = C.HD + j) (f1 : V1 = mem (C.HDt + mem (C.ORD + j)))
    (e2 : A2 = C.CS + j) (f2 : V2 = mem (C.CSt + mem (C.ORD + j)))
    (e3 : A3 = C.CL + j) (f3 : V3 = mem (C.CLt + mem (C.ORD + j))) :
    C.Done1 mem (Function.update (Function.update (Function.update M A1 V1) A2 V2) A3 V3) (j + 1) ∧
    ∀ a, a ≠ C.HD + j → a ≠ C.CS + j → a ≠ C.CL + j →
      Function.update (Function.update (Function.update M A1 V1) A2 V2) A3 V3 a = M a := by
  subst A1 A2 A3 V1 V2 V3
  refine ⟨fun k hk => ?_, fun a h1 h2 h3 => ?_⟩
  · by_cases e : k = j
    · subst e
      refine ⟨?_, ?_, ?_⟩ <;> simp (disch := omega) only [Function.update_of_ne, Function.update_self]
    · obtain ⟨d1, d2, d3⟩ := hd k (by omega)
      refine ⟨?_, ?_, ?_⟩ <;> simp (disch := omega) only [Function.update_of_ne] <;> assumption
  · simp (disch := omega) only [Function.update_of_ne]

/-- `arcCopy` with `args = C.args`. -/
def arcCopy : Stmt :=
  .seq (forRange 11 (.const 0) (.reg 0)
    (.seq (.assign 12 (.load (.bin .add (.reg 1) (.reg 11))))
    (.seq (.assign 13 (.load (.bin .add (.reg 2) (.reg 12))))
    (.seq (.assign 14 (.load (.bin .add (.reg 3) (.reg 12))))
    (.seq (.assign 15 (.load (.bin .add (.reg 4) (.reg 12))))
    (.seq (.store (.bin .add (.reg 5) (.reg 11)) (.reg 13))
    (.seq (.store (.bin .add (.reg 6) (.reg 11)) (.reg 14))
      (.store (.bin .add (.reg 7) (.reg 11)) (.reg 15)))))))))
  (.seq (forRange 11 (.const 0) (.reg 9) (.store (.bin .add (.reg 8) (.reg 11)) (.reg 10)))
  (.seq (.store (.bin .add (.reg 8) (.reg 9)) (.bin .add (.reg 10) (.const 1)))
  (.ret (.const 0))))

theorem arcCopy_noRand : arcCopy.NoRand := by simp [arcCopy, forRange, forUp, Stmt.NoRand]

/-- The contract of `arcCopy`. -/
def arcCopyC (w : ℕ) : Contract where
  pre args mem := ∃ C : AC, args = C.args ∧ C.Pre w mem
  post args mem _ mem' := ∀ C : AC, args = C.args →
    C.Done1 mem mem' C.M ∧ (∀ v < C.s, mem' (C.OK + v) = C.os) ∧ mem' (C.OK + C.s) = C.os + 1 ∧
    ∀ a, ¬ C.Out a → mem' a = mem a
  cost args _ := 80 * (args.getD 0 0 + args.getD 9 0) + 40

theorem arcCopy_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [arcCopy]) :
    MeetsContract w p b (arcCopyC w) := by
  intro args mem pos ω hwords hpre
  obtain ⟨C, rfl, h⟩ := hpre
  have hproc : p.procs[b]? = some arcCopy := hp 0 (by simp)
  clear hp
  have r1 := h.r1; have r2 := h.r2; have r3 := h.r3; have r4 := h.r4
  have l1 := h.l1; have l2 := h.l2; have l3 := h.l3; have l4 := h.l4; have los := h.los
  have hw1 : 1 < 2 ^ w := by omega
  let R : State → Prop := fun st => st.regs 0 = C.M ∧ st.regs 1 = C.ORD ∧ st.regs 2 = C.HDt ∧
    st.regs 3 = C.CSt ∧ st.regs 4 = C.CLt ∧ st.regs 5 = C.HD ∧ st.regs 6 = C.CS ∧
    st.regs 7 = C.CL ∧ st.regs 8 = C.OK ∧ st.regs 9 = C.s ∧ st.regs 10 = C.os
  have hRn : ∀ st st' : State, R st → (∀ r < 11, st'.regs r = st.regs r) → R st' :=
    fun st st' ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ hs =>
      ⟨(hs 0 (by omega)).trans a0, (hs 1 (by omega)).trans a1, (hs 2 (by omega)).trans a2,
        (hs 3 (by omega)).trans a3, (hs 4 (by omega)).trans a4, (hs 5 (by omega)).trans a5,
        (hs 6 (by omega)).trans a6, (hs 7 (by omega)).trans a7, (hs 8 (by omega)).trans a8,
        (hs 9 (by omega)).trans a9, (hs 10 (by omega)).trans a10⟩
  -- the copy loop
  let I1 : ℕ → State → Prop := fun j st => R st ∧ st.regs 11 = j ∧ C.Done1 mem st.mem j ∧
    ∀ a, (a < C.HD ∨ (C.HD + j ≤ a ∧ a < C.CS) ∨ (C.CS + j ≤ a ∧ a < C.CL) ∨ C.CL + j ≤ a) →
      st.mem a = mem a
  have hL1 := Triple.forRange_const (p := p) (r := 11) (lo := .const 0) (hi := .reg 0)
    (body := .seq (.assign 12 (.load (.bin .add (.reg 1) (.reg 11))))
    (.seq (.assign 13 (.load (.bin .add (.reg 2) (.reg 12))))
    (.seq (.assign 14 (.load (.bin .add (.reg 3) (.reg 12))))
    (.seq (.assign 15 (.load (.bin .add (.reg 4) (.reg 12))))
    (.seq (.store (.bin .add (.reg 5) (.reg 11)) (.reg 13))
    (.seq (.store (.bin .add (.reg 6) (.reg 11)) (.reg 14))
      (.store (.bin .add (.reg 7) (.reg 11)) (.reg 15))))))))
    (P := fun st => R st ∧ st.mem = mem) (Inv := I1) 60 0 C.M (Nat.zero_le _) hw1
    (fun _ => by omega)
    (fun st ⟨hr, hm⟩ => ⟨by eval_expr, hRn st _ hr (fun r hr => by
        simp only [Function.update_apply]; rw [if_neg (by omega)]), by simp,
      fun j hj => absurd hj (by omega), fun a _ => by simp [hm]⟩)
    (fun _ st _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by have := hI.1.1; eval_expr)
    (fun j _ hj st ω hI => by
      obtain ⟨hr, h11, hdone, hfr⟩ := hI
      have hr' := hr
      obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hr
      have hord := h.ord j hj
      have eO : st.mem (C.ORD + j) = mem (C.ORD + j) := hfr _ (Or.inl (by omega))
      have e1 : st.mem (C.HDt + mem (C.ORD + j)) = mem (C.HDt + mem (C.ORD + j)) :=
        hfr _ (Or.inl (by omega))
      have e2 : st.mem (C.CSt + mem (C.ORD + j)) = mem (C.CSt + mem (C.ORD + j)) :=
        hfr _ (Or.inl (by omega))
      have e3 : st.mem (C.CLt + mem (C.ORD + j)) = mem (C.CLt + mem (C.ORD + j)) :=
        hfr _ (Or.inl (by omega))
      have b1 := h.vHD _ hord
      have b2 := h.vCS _ hord
      have b3 := h.vCL _ hord
      have key := AC.Done1.step hdone l1 l2 hj (M := st.mem) (A1 := _) (A2 := _) (A3 := _)
        (V1 := _) (V2 := _) (V3 := _) rfl rfl rfl rfl rfl rfl
      refine runs_start_le ?_
      wram_run
      · refine ⟨⟨hRn st _ hr' (fun r hr => by simp only [Function.update_apply]; split_ifs <;> omega),
          by simp, ?_, fun a ha => ?_⟩, by simp [h11]⟩
        · convert key.1 using 2 <;> simp [a1, a2, a3, a4, a5, a6, a7, h11, eO, e1, e2, e3]
        · refine Eq.trans ?_ ((key.2 a (by omega) (by omega) (by omega)).trans
            (hfr a (by omega)))
          congr 1 <;> simp [a1, a2, a3, a4, a5, a6, a7, h11, eO, e1, e2, e3]
      · wram_cost)
  -- the marks
  let I2 : ℕ → State → Prop := fun v st => R st ∧ st.regs 11 = v ∧ C.Done1 mem st.mem C.M ∧
    (∀ u < v, st.mem (C.OK + u) = C.os) ∧
    ∀ a, (a < C.HD ∨ (C.CL + C.M ≤ a ∧ a < C.OK) ∨ C.OK + v ≤ a) → st.mem a = mem a
  have hL2 := Triple.forRange_const (p := p) (r := 11) (lo := .const 0) (hi := .reg 9)
    (body := .store (.bin .add (.reg 8) (.reg 11)) (.reg 10))
    (P := fun st => I1 C.M st) (Inv := I2) 10 0 C.s (Nat.zero_le _) hw1
    (fun _ => by omega)
    (fun st hP => ⟨by eval_expr, hRn st _ hP.1 (fun r hr => by
        simp only [Function.update_apply]; rw [if_neg (by omega)]), by simp, hP.2.2.1,
      fun u hu => absurd hu (by omega), fun a ha => hP.2.2.2 a (by omega)⟩)
    (fun _ st _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by have := hI.1.2.2.2.2.2.2.2.2.2.1; eval_expr)
    (fun v _ hv st ω hI => by
      obtain ⟨hr, h11, hdone, hmk, hfr⟩ := hI
      have hr' := hr
      obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hr
      refine runs_start_le ?_
      wram_run
      · refine ⟨⟨hRn st _ hr' (fun r hr => by simp only [Function.update_apply]; split_ifs <;> omega),
          by simp, fun k hk => ?_, fun u hu => ?_, fun a ha => ?_⟩, by simp [h11]⟩
        · obtain ⟨d1, d2, d3⟩ := hdone k hk
          refine ⟨?_, ?_, ?_⟩ <;>
            simp (disch := omega) only [a8, h11, Function.update_of_ne] <;> assumption
        · by_cases e : u = v
          · subst e; simp [a8, a10, h11]
          · simp (disch := omega) only [a8, h11, Function.update_of_ne]; exact hmk u (by omega)
        · simp (disch := omega) only [a8, h11, Function.update_of_ne]; exact hfr a (by omega)
      · wram_cost)
  refine ⟨arcCopy, hproc, ?_⟩
  dsimp only [arcCopy]
  refine runs_start_le ?_
  refine runs_seq_triple_le hL1 ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
    (fun st1 h1 => ?_)
  refine runs_seq_triple_le hL2 h1 (fun st2 h2 => ?_)
  obtain ⟨hr2, -, hd2, hm2, hf2⟩ := h2
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hr2
  wram_step
  refine runs_ret_le (by eval_expr) (fun C' he => ?_) ?_
  · obtain rfl := AC.eq_of_args he
    refine ⟨fun k hk => ?_, fun u hu => ?_, ?_, fun a ha => ?_⟩
    · obtain ⟨d1, d2, d3⟩ := hd2 k hk
      refine ⟨?_, ?_, ?_⟩ <;>
        simp (disch := omega) only [a8, a9, Function.update_of_ne] <;> assumption
    · simp (disch := omega) only [a8, a9, Function.update_of_ne]; exact hm2 u hu
    · simp [a8, a9, a10]
    · unfold AC.Out at ha
      simp (disch := omega) only [a8, a9, Function.update_of_ne]; exact hf2 a (by omega)
  · simp only [arcCopyC, AC.args, List.getD_cons_zero, List.getD_cons_succ, Expr.size]
    omega

end MinCostFlow.LowStretch
