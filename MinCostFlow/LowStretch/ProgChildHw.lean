module

public import MinCostFlow.LowStretch.ProgChildSpec

/-!
# The highway of a child, along the tree of the first run

The stored highway of a raw child is the path of the tree of the first run of Dijkstra, from the
node of its target to the node of its center (`PetL.Ok.walk`). `hwWalkP` follows this path with
the parent array `PAR` and writes, for the `j`-th node `u`, the four words
`PP[u], rg ||| PF[u], PA[u], PB[u]` at `HW + 4 j`, and the mark `HM[u] := rg`
(`hwWalkP_spec`). The flag `rg` is `1` for a regular petal, whose highway pairs are all halved,
and `0` otherwise. It returns the number of nodes of the path. Each node costs a constant.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The `i`-th node of the path from `u` is `parEnd`. -/
theorem mem_parWalk {mem : ℕ → ℕ} {PAR : ℕ} {u ℓ x : ℕ} :
    x ∈ parWalk mem PAR u ℓ ↔ ∃ i < ℓ, parEnd mem PAR u i = x := by
  induction ℓ generalizing u with
  | zero => simp [parWalk]
  | succ ℓ ih =>
    simp only [parWalk, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨0, by omega, rfl⟩
      · exact ⟨i + 1, by omega, by simp [parEnd, Function.iterate_succ_apply]⟩
    · rintro ⟨i, hi, rfl⟩
      cases i with
      | zero => exact Or.inl rfl
      | succ i => exact Or.inr ⟨i, by omega, by simp [parEnd, Function.iterate_succ_apply]⟩

theorem parEnd_succ (mem : ℕ → ℕ) (PAR u i : ℕ) :
    parEnd mem PAR u (i + 1) = mem (PAR + parEnd mem PAR u i) := by
  simp [parEnd, Function.iterate_succ_apply']

theorem parWalk_getD {mem : ℕ → ℕ} {PAR u ℓ i : ℕ} (hi : i < ℓ) :
    (parWalk mem PAR u ℓ).getD i 0 = parEnd mem PAR u i := by
  induction ℓ generalizing u i with
  | zero => omega
  | succ ℓ ih =>
    cases i with
    | zero => simp [parWalk, parEnd]
    | succ i =>
      simp only [parWalk, List.getD_cons_succ]
      rw [ih (by omega)]
      simp [parEnd, Function.iterate_succ_apply]

theorem length_parWalk (mem : ℕ → ℕ) (PAR u ℓ : ℕ) : (parWalk mem PAR u ℓ).length = ℓ := by
  induction ℓ generalizing u with
  | zero => rfl
  | succ ℓ ih => simp [parWalk, ih]

/-- The numbers of `hwWalkP`. -/
structure HWE where
  u0 : ℕ
  v0 : ℕ
  rg : ℕ
  PAR : ℕ
  PP : ℕ
  PF : ℕ
  PA : ℕ
  PB : ℕ
  HM : ℕ
  HW : ℕ
  mem0 : ℕ → ℕ

namespace HWE

variable (E : HWE)

/-- The arguments of `hwWalkP`. -/
def args : List ℕ := [E.u0, E.v0, E.rg, E.PAR, E.PP, E.PF, E.PA, E.PB, E.HM, E.HW]

/-- The `i`-th node of the path. -/
def nd (i : ℕ) : ℕ := parEnd E.mem0 E.PAR E.u0 i

/-- The precondition, for a path of `ℓ` nodes, all below `s`: the path ends at `v0`, which it does
not visit before; the arrays read lie below the marks, and the marks below the highway. -/
structure Ok (w s ℓ : ℕ) : Prop where
  hit : E.nd ℓ = E.v0
  ne : ∀ i < ℓ, E.nd i ≠ E.v0
  lt : ∀ i < ℓ, E.nd i < s
  rd : E.PAR + s ≤ E.HM ∧ E.PP + s ≤ E.HM ∧ E.PF + s ≤ E.HM ∧ E.PA + s ≤ E.HM ∧ E.PB + s ≤ E.HM
  hm : E.HM + s ≤ E.HW
  room : E.HW + 4 * ℓ + 4 < 2 ^ w
  rg : E.rg ≤ 1
  words : ∀ i < ℓ, E.mem0 (E.PF + E.nd i) < 2 ^ w

/-- The four words written for node `u`. -/
def ent (u : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (E.mem0 (E.PP + u), E.rg ||| E.mem0 (E.PF + u), E.mem0 (E.PA + u), E.mem0 (E.PB + u))

/-- The cells changed: the highway entries and the marks of the path. -/
def Out (ℓ a : ℕ) : Prop := (E.HW ≤ a ∧ a < E.HW + 4 * ℓ) ∨ ∃ i < ℓ, a = E.HM + E.nd i

/-- The memory after the first `j` nodes. -/
def Done (j : ℕ) (M : ℕ → ℕ) : Prop :=
  (∀ i < j, M (E.HW + 4 * i) = (E.ent (E.nd i)).1 ∧
    M (E.HW + 4 * i + 1) = (E.ent (E.nd i)).2.1 ∧
    M (E.HW + 4 * i + 2) = (E.ent (E.nd i)).2.2.1 ∧
    M (E.HW + 4 * i + 3) = (E.ent (E.nd i)).2.2.2) ∧
  (∀ i < j, M (E.HM + E.nd i) = E.rg) ∧
  ∀ a, ¬ E.Out j a → M a = E.mem0 a

/-- The registers that never change. -/
def R (st : State) : Prop :=
  st.regs 1 = E.v0 ∧ st.regs 2 = E.rg ∧ st.regs 3 = E.PAR ∧ st.regs 4 = E.PP ∧
    st.regs 5 = E.PF ∧ st.regs 6 = E.PA ∧ st.regs 7 = E.PB ∧ st.regs 8 = E.HM ∧ st.regs 9 = E.HW

variable {E}

theorem R.upd {st : State} (h : E.R st) {r : ℕ} (hr : r = 0 ∨ 10 ≤ r) (v : ℕ) :
    E.R { st with regs := Function.update st.regs r v } := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Function.update_apply] <;> rwa [ite_eq_right (by omega)]

theorem R.mem {st : State} (h : E.R st) (M : ℕ → ℕ) : E.R { st with mem := M } := h

theorem R.of_regs {st st' : State} (h : E.R st)
    (he : ∀ r, 1 ≤ r → r ≤ 9 → st'.regs r = st.regs r) : E.R st' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
  exact ⟨by rw [he 1 (by omega) (by omega), a1], by rw [he 2 (by omega) (by omega), a2],
    by rw [he 3 (by omega) (by omega), a3], by rw [he 4 (by omega) (by omega), a4],
    by rw [he 5 (by omega) (by omega), a5], by rw [he 6 (by omega) (by omega), a6],
    by rw [he 7 (by omega) (by omega), a7], by rw [he 8 (by omega) (by omega), a8],
    by rw [he 9 (by omega) (by omega), a9]⟩

end HWE

/-- One node: read its four words and its parent, write them, and move to the parent. -/
def hwIn : Stmt :=
  .seq (.assign 11 (.load (.bin .add (.reg 4) (.reg 0))))
  (.seq (.assign 12 (.bin .or (.reg 2) (.load (.bin .add (.reg 5) (.reg 0)))))
  (.seq (.assign 13 (.load (.bin .add (.reg 6) (.reg 0))))
  (.seq (.assign 14 (.load (.bin .add (.reg 7) (.reg 0))))
  (.seq (.assign 15 (.load (.bin .add (.reg 3) (.reg 0))))
  (.seq (.store (.bin .add (.reg 9) (.bin .mul (.const 4) (.reg 10))) (.reg 11))
  (.seq (.store (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 4) (.reg 10))) (.const 1))
      (.reg 12))
  (.seq (.store (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 4) (.reg 10))) (.const 2))
      (.reg 13))
  (.seq (.store (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 4) (.reg 10))) (.const 3))
      (.reg 14))
  (.seq (.store (.bin .add (.reg 8) (.reg 0)) (.reg 2))
  (.seq (.assign 0 (.reg 15))
  ((.assign 10 (.bin .add (.reg 10) (.const 1))))))))))))))

/-- The test of the loop: `1` while the node is not `v0`. -/
def hwTest : Expr := .bin .sub (.const 1) (.bin .eq (.reg 0) (.reg 1))

/-- `hwWalkP` with `args = [u0, v0, rg, PAR, PP, PF, PA, PB, HM, HW]`. -/
def hwWalkP : Stmt :=
  .seq (.assign 10 (.const 0)) (.seq (.loop hwTest hwIn) (.ret (.reg 10)))

theorem hwWalkP_noRand : hwWalkP.NoRand := by
  simp [hwWalkP, hwIn, Stmt.NoRand]

namespace HWE

variable {w s ℓ : ℕ} {E : HWE}

/-- The writes of one node keep `Done`. -/
theorem Done.step (h : E.Ok w s ℓ) {j : ℕ} {M : ℕ → ℕ} (hj : j < ℓ) (hd : E.Done j M) :
    E.Done (j + 1) (Function.update (Function.update (Function.update (Function.update
      (Function.update M (E.HW + 4 * j) (E.mem0 (E.PP + E.nd j))) (E.HW + 4 * j + 1)
        (E.rg ||| E.mem0 (E.PF + E.nd j))) (E.HW + 4 * j + 2) (E.mem0 (E.PA + E.nd j)))
        (E.HW + 4 * j + 3) (E.mem0 (E.PB + E.nd j))) (E.HM + E.nd j) E.rg) := by
  have hm := h.hm
  have hj' := h.lt j hj
  obtain ⟨d1, d2, d3⟩ := hd
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun a ha => ?_⟩
  · have hi' := h.lt i (by omega)
    simp only [Function.update_apply]
    rcases Nat.lt_or_ge i j with hij | hij
    · obtain ⟨e1, e2, e3, e4⟩ := d1 i hij
      refine ⟨?_, ?_, ?_, ?_⟩ <;> (split_ifs <;> first | omega | assumption)
    · have : i = j := by omega
      subst this
      refine ⟨?_, ?_, ?_, ?_⟩ <;> (split_ifs <;> first | omega | rfl)
  · simp only [Function.update_apply]
    rcases Nat.lt_or_ge i j with hij | hij
    · have hi' := h.lt i (by omega)
      have := d2 i hij
      split_ifs <;> first | omega | rfl | assumption
    · have : i = j := by omega
      subst this
      simp
  · have h1 : ¬ (E.HW ≤ a ∧ a < E.HW + 4 * (j + 1)) := fun hh => ha (Or.inl hh)
    have h2 : a ≠ E.HM + E.nd j := fun hh => ha (Or.inr ⟨j, by omega, hh⟩)
    have h3 : ¬ E.Out j a := fun hh => ha (by
      rcases hh with hh | ⟨i, hi, hh⟩
      · left; omega
      · right; exact ⟨i, by omega, hh⟩)
    simp only [Function.update_apply]
    split_ifs <;> first | omega | exact d3 a h3

/-- One node of the path. -/
theorem hwIn_runs {p : Program} (h : E.Ok w s ℓ) {st : State} (hR : E.R st) {j : ℕ}
    (hj : j < ℓ) (h0 : st.regs 0 = E.nd j) (h10 : st.regs 10 = j) (hd : E.Done j st.mem)
    (ω : ℕ → Bool) :
    ∃ o s' c, Runs w p ω hwIn st o s' c ∧
      (o = .normal ∧ E.R s' ∧ s'.regs 0 = E.nd (j + 1) ∧ s'.regs 10 = j + 1 ∧
        E.Done (j + 1) s'.mem) ∧ c ≤ 150 := by
  have hR' := hR
  obtain ⟨r1, r2, r3, r4, r5⟩ := h.rd
  have hm := h.hm
  have room := h.room
  have hlt := h.lt j hj
  have hrg := h.rg
  have lo : ∀ a < E.HM, st.mem a = E.mem0 a := fun a ha => hd.2.2 a fun hout => by
    rcases hout with ⟨h1, -⟩ | ⟨i, -, rfl⟩ <;> omega
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := hR
  have m1 : st.mem (st.regs 4 + st.regs 0) = E.mem0 (E.PP + E.nd j) := by
    rw [a4, h0]; exact lo _ (by omega)
  have m2 : st.mem (st.regs 5 + st.regs 0) = E.mem0 (E.PF + E.nd j) := by
    rw [a5, h0]; exact lo _ (by omega)
  have m3 : st.mem (st.regs 6 + st.regs 0) = E.mem0 (E.PA + E.nd j) := by
    rw [a6, h0]; exact lo _ (by omega)
  have m4 : st.mem (st.regs 7 + st.regs 0) = E.mem0 (E.PB + E.nd j) := by
    rw [a7, h0]; exact lo _ (by omega)
  have m5 : st.mem (st.regs 3 + st.regs 0) = E.nd (j + 1) := by
    rw [a3, h0, lo _ (by omega)]
    show _ = parEnd _ _ _ (j + 1)
    rw [parEnd_succ]; rfl
  have w2 : st.mem (st.regs 5 + st.regs 0) < 2 ^ w := by rw [m2]; exact h.words j hj
  have w0 : st.regs 2 < 2 ^ w := by rw [a2]; omega
  have b1 : st.regs 4 + st.regs 0 < 2 ^ w := by rw [a4, h0]; omega
  have b2 : st.regs 5 + st.regs 0 < 2 ^ w := by rw [a5, h0]; omega
  have b3 : st.regs 6 + st.regs 0 < 2 ^ w := by rw [a6, h0]; omega
  have b4 : st.regs 7 + st.regs 0 < 2 ^ w := by rw [a7, h0]; omega
  have b5 : st.regs 3 + st.regs 0 < 2 ^ w := by rw [a3, h0]; omega
  have b6 : st.regs 9 + 4 * st.regs 10 + 3 < 2 ^ w := by rw [a9, h10]; omega
  have b7 : st.regs 8 + st.regs 0 < 2 ^ w := by rw [a8, h0]; omega
  have b8 : st.regs 10 + 1 < 2 ^ w := by rw [h10]; omega
  have e9 : st.regs 9 + 4 * st.regs 10 = E.HW + 4 * j := by rw [a9, h10]
  have e8 : st.regs 8 + st.regs 0 = E.HM + E.nd j := by rw [a8, h0]
  have e2 : st.regs 2 = E.rg := a2
  have hJ : st.regs 10 = j ∧ True := ⟨h10, trivial⟩
  clear a1 a2 a3 a4 a5 a6 a7 a8 a9 h0 h10 lo
  refine runs_start_le ?_
  dsimp only [hwIn]
  wram_run
  all_goals try wram_cost
  refine ⟨rfl, hR'.of_regs fun r h1 h2 => ?_, ?_, ?_, ?_⟩
  · simp only [Function.update_apply]
    split_ifs <;> first | omega | rfl
  · simpa using m5
  · simpa using hJ.1
  simp only [m1, m2, m3, m4, e9, e8, e2]
  exact Done.step h hj hd

/-- The loop invariant after `j` nodes. -/
def LI (ℓ : ℕ) (j : ℕ) (st : State) : Prop :=
  E.R st ∧ (st.regs 0 = E.nd j ∧ st.regs 10 = j) ∧ j ≤ ℓ ∧ E.Done j st.mem

/-- **The walk.** Started with `args = E.args` on the memory `E.mem0`, `hwWalkP` returns the
length `ℓ` of the path, and the memory holds the entries and the marks of its nodes. -/
theorem hwWalkP_runs {p : Program} (h : E.Ok w s ℓ) (pos : ℕ) (ω : ℕ → Bool) :
    ∃ o s' c, Runs w p ω hwWalkP (startState E.args E.mem0 pos) o s' c ∧
      (o.value = ℓ ∧ E.Done ℓ s'.mem) ∧ c ≤ 160 * ℓ + 20 := by
  have room := h.room
  have hloop := Triple.loop_inv (w := w) (p := p) (e := hwTest) (body := hwIn)
    (Inv := LI (E := E) ℓ) (Q := normalPost (LI (E := E) ℓ ℓ))
    (fun j => ℓ - j) (fun j => (ℓ - j) * 160 + 10)
    (condVal := fun st => 1 - if st.regs 0 = st.regs 1 then 1 else 0)
    (fun j st hI => by
      have := hI.1.1
      unfold hwTest
      eval_expr)
    (fun j st hI hv => by
      obtain ⟨hr, ⟨h0, h10⟩, hjl, hd⟩ := hI
      have e : st.regs 0 = st.regs 1 := by
        by_contra hne; simp [hne] at hv
      have hj : j = ℓ := by
        by_contra hne
        exact h.ne j (by omega) (by rw [← h0, e, hr.1])
      subst hj
      refine ⟨⟨hr, ⟨h0, h10⟩, le_rfl, hd⟩, ?_⟩
      simp [hwTest])
    (fun j st hI hv => by
      obtain ⟨hr, ⟨h0, h10⟩, hjl, hd⟩ := hI
      have hj : j < ℓ := by
        by_contra hne
        have e : j = ℓ := by omega
        subst e
        have : st.regs 0 = st.regs 1 := by rw [h0, hr.1, h.hit]
        simp [this] at hv
      refine ⟨150, fun st' ω' hst => ?_⟩
      subst hst
      obtain ⟨o, s', c, hrun, ⟨rfl, hr', h0', h10', hd'⟩, hc⟩ := hwIn_runs h hr hj h0 h10 hd ω'
      refine ⟨_, _, _, hrun, ⟨j + 1, ⟨hr', ⟨h0', h10'⟩, hj, hd'⟩, by omega, ?_⟩, hc⟩
      simp only [hwTest, Expr.size]
      have : ℓ - j = (ℓ - (j + 1)) + 1 := by omega
      rw [this]; ring_nf; omega)
    0
  dsimp only [hwWalkP]
  refine runs_start_le ?_
  refine runs_seq_assign_le (by eval_expr) ?_
  refine runs_seq_triple_le hloop ?_ (fun st hI => ?_)
  · refine ⟨HWE.R.upd ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by omega) _,
      ⟨by simp [startState, HWE.args, nd, parEnd], by simp⟩, Nat.zero_le _,
      fun i hi => by omega, fun i hi => by omega, fun a _ => rfl⟩
  · obtain ⟨-, ⟨-, h10⟩, -, hd⟩ := hI
    refine runs_ret_le (by eval_expr) ⟨rfl, hd⟩ ?_
    simp only [hwTest, Expr.size]
    omega

end HWE

/-- The length of the path of `hwWalkP`: the first step at which the parent path from `u0` reaches
`v0`. -/
noncomputable def hwLenOf (args : List ℕ) (mem : ℕ → ℕ) : ℕ :=
  sInf {ℓ | parEnd mem (args.getD 3 0) (args.getD 0 0) ℓ = args.getD 1 0}

/-- The contract of `hwWalkP`. -/
noncomputable def hwC (w : ℕ) : Contract where
  pre args mem := ∃ E : HWE, ∃ s ℓ, args = E.args ∧ E.mem0 = mem ∧ E.Ok w s ℓ
  post args mem v mem' := ∀ E : HWE, ∀ s ℓ, args = E.args → E.mem0 = mem → E.Ok w s ℓ →
    v = ℓ ∧ E.Done ℓ mem'
  cost args mem := 160 * hwLenOf args mem + 20

namespace HWE

variable {w s ℓ : ℕ} {E : HWE}

theorem Ok.len (h : E.Ok w s ℓ) : hwLenOf E.args E.mem0 = ℓ := by
  have hmem : ℓ ∈ {ℓ | parEnd E.mem0 (E.args.getD 3 0) (E.args.getD 0 0) ℓ = E.args.getD 1 0} :=
    h.hit
  apply le_antisymm (Nat.sInf_le hmem)
  by_contra hlt
  have := Nat.sInf_mem ⟨ℓ, hmem⟩
  exact h.ne _ (by omega) this

theorem Ok.uniq {s' ℓ' : ℕ} (h : E.Ok w s ℓ) (h' : E.Ok w s' ℓ') : ℓ' = ℓ := by
  rw [← h.len, ← h'.len]

end HWE

theorem hwWalkP_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [hwWalkP]) :
    MeetsContract w p b (hwC w) := by
  intro args mem pos ω _ hpre
  obtain ⟨E, s, ℓ, rfl, rfl, h⟩ := hpre
  have hproc : p.procs[b]? = some hwWalkP := hp 0 (by simp)
  obtain ⟨o, s', c, hrun, ⟨hv, hd⟩, hc⟩ := HWE.hwWalkP_runs (p := p) h pos ω
  refine ⟨hwWalkP, hproc, o, s', c, hrun, fun E' s2 ℓ2 he hm h2 => ?_, ?_⟩
  · have e : E' = E := by
      cases E; cases E'; simp only [HWE.args, List.cons.injEq] at he; simp_all
    subst e
    have := h.uniq h2
    subst this
    exact ⟨hv, hd⟩
  · show c ≤ 160 * hwLenOf E.args E.mem0 + 20
    rw [h.len]; exact hc

end MinCostFlow.LowStretch
