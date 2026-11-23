module

public import MinCostFlow.LowStretch.ProgCSR
public import MinCostFlow.LowStretch.DedupMath

/-!
# Keeping one lightest pair per pair of ends

`ddP` scans the pairs grouped by their smaller end `u` (by `csrB`). In the first pass over the
group of `u` it finds, for each larger end `v`, a lightest pair from `u` to `v` (`DedupMath`).
In the second pass it writes these pairs to `OUT`. The result lists at most one pair per pair of
ends, and for every pair a pair with the same ends that is at least as light (`ddP_spec`).

Kruskal's algorithm then sorts only these pairs. There are at most `n²` of them, so the sort costs
`O(m log n)` even when `m` is much larger than `n²`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The numbers that `ddP` works with, and the memory at its start. -/
structure DDE where
  m : ℕ
  n : ℕ
  IN : ℕ
  PE : ℕ
  OFF : ℕ
  ORD : ℕ
  MARK : ℕ
  BEST : ℕ
  OUT : ℕ
  mem0 : ℕ → ℕ

namespace DDE

variable (E : DDE)

/-- The first end of pair `p`. -/
def pu (p : ℕ) : ℕ := E.mem0 (E.IN + 3 * p)
/-- The second end of pair `p`. -/
def pv (p : ℕ) : ℕ := E.mem0 (E.IN + 3 * p + 1)
/-- The smaller end. -/
def key (p : ℕ) : ℕ := min (E.pu p) (E.pv p)
/-- The larger end. -/
def oth (p : ℕ) : ℕ := E.pu p + E.pv p - E.key p
/-- The weight that decides which pair is kept. -/
def wt (p : ℕ) : ℕ := E.mem0 (E.PE + p)
/-- Where the group of `u` starts. -/
def o (u : ℕ) : ℕ := offOf E.key E.m u
/-- The group of `u`. -/
def g (u : ℕ) : List ℕ := grp E.key E.m u

/-- The precondition of `ddP`. -/
structure Ok (w : ℕ) : Prop where
  ends : ∀ p < E.m, E.pu p < E.n ∧ E.pv p < E.n
  off : ∀ u ≤ E.n, E.mem0 (E.OFF + u) = E.o u
  ord : ∀ u < E.n, ∀ j < (E.g u).length, E.mem0 (E.ORD + E.o u + j) = (E.g u).getD j 0
  wt_lt : ∀ p < E.m, E.wt p < 2 ^ w
  l1 : E.IN + 3 * E.m ≤ E.PE
  l2 : E.PE + E.m ≤ E.OFF
  l3 : E.OFF + E.n + 1 ≤ E.ORD
  l4 : E.ORD + E.m ≤ E.MARK
  l5 : E.MARK + E.n ≤ E.BEST
  l6 : E.BEST + E.n ≤ E.OUT
  l7 : E.OUT + E.m + 2 * E.n + 2 < 2 ^ w

/-- The registers that never change. -/
def R (st : State) : Prop :=
  st.regs 0 = E.m ∧ st.regs 1 = E.n ∧ st.regs 2 = E.IN ∧ st.regs 3 = E.PE ∧ st.regs 4 = E.OFF ∧
    st.regs 5 = E.ORD ∧ st.regs 6 = E.MARK ∧ st.regs 7 = E.BEST ∧ st.regs 8 = E.OUT

variable {E} {w : ℕ}

theorem R.upd {st : State} (h : E.R st) {r : ℕ} (hr : 9 ≤ r) (v : ℕ) :
    E.R { st with regs := Function.update st.regs r v } := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Function.update_apply] <;> (rw [if_neg (by omega)]; assumption)

theorem R.of {st st' : State} (h : E.R st) (hr : ∀ i < 9, st'.regs i = st.regs i) : E.R st' := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
  exact ⟨(hr 0 (by omega)).trans a0, (hr 1 (by omega)).trans a1, (hr 2 (by omega)).trans a2,
    (hr 3 (by omega)).trans a3, (hr 4 (by omega)).trans a4, (hr 5 (by omega)).trans a5,
    (hr 6 (by omega)).trans a6, (hr 7 (by omega)).trans a7, (hr 8 (by omega)).trans a8⟩

theorem R.mem {st : State} (h : E.R st) (M : ℕ → ℕ) : E.R { st with mem := M } := h

theorem key_le_oth {p : ℕ} : E.key p ≤ E.oth p := by simp only [key, oth]; omega

theorem oth_lt (h : E.Ok w) {p : ℕ} (hp : p < E.m) : E.oth p < E.n := by
  have := h.ends p hp; simp only [oth, key]; omega

theorem key_lt (h : E.Ok w) {p : ℕ} (hp : p < E.m) : E.key p < E.n := by
  have := h.ends p hp; simp only [key]; omega

theorem o_le (u : ℕ) : E.o u ≤ E.m := by
  unfold o offOf
  have := List.length_filter_le (fun i => decide (E.key i < u)) (List.range E.m)
  simpa using this

theorem o_succ (u : ℕ) : E.o (u + 1) = E.o u + (E.g u).length := offOf_succ _ _ _

theorem mem_g {u p : ℕ} : p ∈ E.g u ↔ p < E.m ∧ E.key p = u := by
  unfold g grp; simp

theorem getD_mem_g {u j : ℕ} (hj : j < (E.g u).length) : (E.g u).getD j 0 ∈ E.g u := by
  rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj

theorem g_nodup (u : ℕ) : (E.g u).Nodup := (List.nodup_range).filter _

theorem take_succ_g {u j : ℕ} (hj : j < (E.g u).length) :
    (E.g u).take (j + 1) = (E.g u).take j ++ [(E.g u).getD j 0] := by
  rw [List.getD_eq_getElem _ _ hj, List.take_add_one, List.getElem?_eq_getElem hj]; rfl

/-- Two pairs with the same smaller and larger end have the same ends. -/
theorem same_ends {p q : ℕ} (hk : E.key p = E.key q) (ho : E.oth p = E.oth q) :
    (E.pu p = E.pu q ∧ E.pv p = E.pv q) ∨ (E.pu p = E.pv q ∧ E.pv p = E.pu q) := by
  simp only [key, oth] at *; omega

end DDE

/-- The larger end of the pair in register `11`, whose smaller end is in register `9`. -/
def ddOth : Expr :=
  .bin .sub (.bin .add (.load (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg 11))))
    (.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg 11))) (.const 1)))) (.reg 9)

/-- The first pass over one group. -/
def ddB1 : Stmt :=
  .seq (.assign 11 (.load (.bin .add (.reg 5) (.reg 10))))
  (.seq (.assign 12 ddOth)
  (.cond (.bin .eq (.load (.bin .add (.reg 6) (.reg 12))) (.bin .add (.reg 9) (.const 1)))
    (.cond (.bin .lt (.load (.bin .add (.reg 3) (.reg 11)))
        (.load (.bin .add (.reg 3) (.load (.bin .add (.reg 7) (.reg 12))))))
      (.store (.bin .add (.reg 7) (.reg 12)) (.reg 11)) .nop)
    (.seq (.store (.bin .add (.reg 6) (.reg 12)) (.bin .add (.reg 9) (.const 1)))
      (.store (.bin .add (.reg 7) (.reg 12)) (.reg 11)))))

/-- The second pass over one group. -/
def ddB2 : Stmt :=
  .seq (.assign 11 (.load (.bin .add (.reg 5) (.reg 10))))
  (.seq (.assign 12 ddOth)
  (.cond (.bin .eq (.load (.bin .add (.reg 7) (.reg 12))) (.reg 11))
    (.seq (.store (.bin .add (.reg 8) (.reg 13)) (.reg 11))
      (.assign 13 (.bin .add (.reg 13) (.const 1))))
    .nop))

/-- The start and the end of the group of `u` (register `9`). -/
def ddLo : Expr := .load (.bin .add (.reg 4) (.reg 9))
def ddHi : Expr := .load (.bin .add (.bin .add (.reg 4) (.reg 9)) (.const 1))

/-- One group: both passes. -/
def ddGroup : Stmt := .seq (forRange 10 ddLo ddHi ddB1) (forRange 10 ddLo ddHi ddB2)

/-- `ddP` with `args = [m, n, IN, PE, OFF, ORD, MARK, BEST, OUT]`. -/
def ddP : Stmt :=
  .seq (forRange 15 (.const 0) (.reg 1) (.store (.bin .add (.reg 6) (.reg 15)) (.const 0)))
  (.seq (.assign 13 (.const 0))
  (.seq (forRange 9 (.const 0) (.reg 1) ddGroup)
  (.ret (.reg 13))))

theorem ddP_noRand : ddP.NoRand := by
  simp [ddP, ddGroup, ddB1, ddB2, forRange, forUp, Stmt.NoRand]

namespace DDE

variable {E : DDE} {w : ℕ} {p : Program}

/-- The invariant of the first pass over the group of `u`, after the pairs before `k`. `M0` is the
memory at the start of the group. -/
def I1 (E : DDE) (u : ℕ) (M0 : ℕ → ℕ) (c0 k : ℕ) (st : State) : Prop :=
  E.R st ∧ st.regs 9 = u ∧ st.regs 10 = k ∧ st.regs 13 = c0 ∧
    (∀ a, (a < E.MARK ∨ E.BEST + E.n ≤ a) → st.mem a = M0 a) ∧
    P1 E.oth E.wt E.n u E.MARK E.BEST ((E.g u).take (k - E.o u)) st.mem

/-- The facts about the pair at position `k` of the group of `u`. -/
theorem at_k (h : E.Ok w) {u k : ℕ} (hu : u < E.n) (hk1 : E.o u ≤ k) (hk2 : k < E.o (u + 1))
    {M : ℕ → ℕ} (hM : ∀ a < E.MARK, M a = E.mem0 a) :
    let q := (E.g u).getD (k - E.o u) 0
    M (E.ORD + k) = q ∧ q ∈ E.g u ∧ q < E.m ∧ E.key q = u ∧ E.oth q < E.n ∧
      M (E.IN + 3 * q) = E.pu q ∧ M (E.IN + 3 * q + 1) = E.pv q ∧ M (E.PE + q) = E.wt q ∧
      E.pu q + E.pv q - u = E.oth q ∧
      (E.g u).take (k + 1 - E.o u) = (E.g u).take (k - E.o u) ++ [q] := by
  intro q
  have hj : k - E.o u < (E.g u).length := by rw [o_succ] at hk2; omega
  have hq : q ∈ E.g u := getD_mem_g hj
  obtain ⟨hqm, hqk⟩ := mem_g.mp hq
  have hm := E.o_le (u + 1)
  have l1 := h.l1; have l2 := h.l2; have l3 := h.l3; have l4 := h.l4
  refine ⟨?_, hq, hqm, hqk, oth_lt h hqm, hM _ (by omega), hM _ (by omega), hM _ (by omega),
    by rw [← hqk]; rfl, ?_⟩
  · rw [hM _ (by omega)]
    have := h.ord u hu (k - E.o u) hj
    rw [show E.ORD + E.o u + (k - E.o u) = E.ORD + k by omega] at this
    exact this
  · rw [show k + 1 - E.o u = k - E.o u + 1 by omega]
    exact take_succ_g hj

theorem pass1 (h : E.Ok w) {u : ℕ} (hu : u < E.n) (M0 : ℕ → ℕ)
    (hM0 : ∀ a < E.MARK, M0 a = E.mem0 a) (c0 : ℕ) :
    Triple w p (fun st => E.R st ∧ st.regs 9 = u ∧ st.regs 13 = c0 ∧ st.mem = M0 ∧
        ∀ v < E.n, M0 (E.MARK + v) ≤ u)
      (forRange 10 ddLo ddHi ddB1) (normalPost (I1 E u M0 c0 (E.o (u + 1))))
      (fun _ => (E.o (u + 1) - E.o u) * (100 + ddHi.size + 8) + (ddLo.size + ddHi.size + 5)) := by
  have l1 := h.l1; have l2 := h.l2; have l3 := h.l3; have l4 := h.l4; have l5 := h.l5
  have l6 := h.l6; have l7 := h.l7
  have hom := E.o_le (u + 1)
  have hmono : E.o u ≤ E.o (u + 1) := by rw [o_succ]; omega
  have hw1 : 1 < 2 ^ w := by omega
  have hoff : ∀ x ≤ E.n, M0 (E.OFF + x) = E.o x := fun x hx => by
    rw [hM0 _ (by omega)]; exact h.off x hx
  refine Triple.forRange_const (Inv := I1 E u M0 c0) 100 (E.o u) (E.o (u + 1)) hmono hw1
    (fun _ => by omega) ?_ ?_ ?_ ?_
  · rintro st ⟨hr, h9, h13, hm, hmk⟩
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := hr
    have hlo : st.mem (E.OFF + u) = E.o u := by rw [hm]; exact hoff u hu.le
    refine ⟨by simp only [ddLo]; eval_expr, R.upd ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ (by omega) _, by simp [h9], by simp, by simp [h13],
      fun a _ => by simp [hm], ?_⟩
    simp only [Nat.sub_self, List.take_zero]
    exact P1.nil (fun v hv => by simpa [hm] using hmk v hv)
  · intro _ st _ _ hI; exact hI.2.2.1
  · intro _ st _ _ hI
    obtain ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩, h9, -, -, hfr, -⟩ := hI
    have : st.mem (E.OFF + u + 1) = E.o (u + 1) := by
      rw [hfr _ (by omega), show E.OFF + u + 1 = E.OFF + (u + 1) by omega]; exact hoff _ hu
    simp only [ddHi]; eval_expr
  · intro k hk1 hk2 st ω hI
    obtain ⟨hr, h9, h10, h13, hfr, hP⟩ := hI
    have hM : ∀ a < E.MARK, st.mem a = E.mem0 a := fun a ha => by rw [hfr a (Or.inl ha), hM0 a ha]
    have hat := at_k h hu hk1 hk2 hM
    set q := (E.g u).getD (k - E.o u) 0 with hqdef
    obtain ⟨eq1, hq, hqm, hqk, hoth, eu, ev, ewt, eo, etake⟩ := hat
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := hr
    obtain ⟨hmk, -, hbest⟩ := hP (E.oth q) hoth
    have hpu := (h.ends q hqm).1
    have hpv := (h.ends q hqm).2
    have hA : st.mem (st.regs 2 + 3 * st.mem (E.ORD + k)) = E.pu q := by rw [a2, eq1, eu]
    have hB : st.mem (st.regs 2 + 3 * st.mem (E.ORD + k) + 1) = E.pv q := by rw [a2, eq1, ev]
    have hidx7 : st.regs 7 + (st.mem (st.regs 2 + 3 * st.mem (E.ORD + k)) +
        st.mem (st.regs 2 + 3 * st.mem (E.ORD + k) + 1) - st.regs 9) = E.BEST + E.oth q := by
      omega
    have hidx6 : st.regs 6 + (st.mem (st.regs 2 + 3 * st.mem (E.ORD + k)) +
        st.mem (st.regs 2 + 3 * st.mem (E.ORD + k) + 1) - st.regs 9) = E.MARK + E.oth q := by
      omega
    have hBS : st.mem (st.regs 7 + (st.mem (st.regs 2 + 3 * st.mem (E.ORD + k)) +
        st.mem (st.regs 2 + 3 * st.mem (E.ORD + k) + 1) - st.regs 9)) =
        st.mem (E.BEST + E.oth q) := by rw [hidx7]
    have hMK : st.mem (st.regs 6 + (st.mem (st.regs 2 + 3 * st.mem (E.ORD + k)) +
        st.mem (st.regs 2 + 3 * st.mem (E.ORD + k) + 1) - st.regs 9)) =
        st.mem (E.MARK + E.oth q) := by rw [hidx6]
    have hidx7' : st.regs 7 + (st.mem (st.regs 2 + 3 * q) + st.mem (st.regs 2 + 3 * q + 1) -
        st.regs 9) = E.BEST + E.oth q := by have := hidx7; rw [eq1] at this; exact this
    have hidx6' : st.regs 6 + (st.mem (st.regs 2 + 3 * q) + st.mem (st.regs 2 + 3 * q + 1) -
        st.regs 9) = E.MARK + E.oth q := by have := hidx6; rw [eq1] at this; exact this
    have hbs : st.mem (E.MARK + E.oth q) = u + 1 → st.mem (E.BEST + E.oth q) < E.m := by
      intro hc
      exact (mem_g.mp (List.mem_of_mem_take (hbest hc).1)).1
    refine runs_start_le ?_
    dsimp only [ddB1, ddOth]
    have hRt : ∀ M : ℕ → ℕ, ∀ x y z ps,
        E.R ⟨M, Function.update (Function.update (Function.update st.regs 11 x) 12 y) 10 z, ps⟩ := by
      intro M x y z ps
      simp only [DDE.R]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [Function.update_apply, a0, a1, a2, a3, a4, a5, a6, a7, a8]
    wram_run
    all_goals (try wram_cost)
    · -- marked, and lighter
      rename_i hc1
      have hmq : st.mem (E.MARK + E.oth q) = u + 1 := by rw [hMK, h9] at hc1; exact hc1
      have hbq := hbs hmq
      have hlt : E.wt q < E.wt (st.mem (E.BEST + E.oth q)) := by
        rw [a3, eq1, hidx7', hM _ (by omega), hM _ (by omega)] at hcond; exact hcond
      have hP' := P1.hit hP hoth hmq l5
      rw [if_pos hlt] at hP'
      simp only [normalPost, eq1, hidx7']
      refine ⟨⟨hRt _ _ _ _ _, by simp [h9], by simp, by simp [h13], fun a ha => ?_, ?_⟩, by simp [h10]⟩
      · simp only [Function.update_apply]; rw [if_neg (by omega)]; exact hfr a ha
      · rw [etake]; exact hP'
    · -- marked, not lighter
      rename_i hc1
      have hmq : st.mem (E.MARK + E.oth q) = u + 1 := by rw [hMK, h9] at hc1; exact hc1
      have hbq := hbs hmq
      have hlt : ¬ E.wt q < E.wt (st.mem (E.BEST + E.oth q)) := by
        rw [a3, eq1, hidx7', hM _ (by omega), hM _ (by omega)] at hcond; exact hcond
      have hP' := P1.hit hP hoth hmq l5
      rw [if_neg hlt] at hP'
      simp only [normalPost]
      refine ⟨⟨hRt _ _ _ _ _, by simp [h9], by simp, by simp [h13], fun a ha => hfr a ha, ?_⟩,
        by simp [h10]⟩
      rw [etake]; exact hP'
    · -- not marked
      have hmq : st.mem (E.MARK + E.oth q) ≠ u + 1 := by rw [hMK, h9] at hcond; exact hcond
      have hP' := P1.new hP hoth hmq l5
      simp only [normalPost, eq1, hidx7', hidx6']
      refine ⟨⟨hRt _ _ _ _ _, by simp [h9], by simp, by simp [h13], fun a ha => ?_, ?_⟩, by simp [h10]⟩
      · simp only [Function.update_apply]; rw [if_neg (by omega), if_neg (by omega)]; exact hfr a ha
      · rw [etake, h9]; exact hP'

/-- The invariant of the second pass over the group of `u`, after the pairs before `k`. `M1` is
the memory after the first pass and `c0` the count before the group. -/
def I2 (E : DDE) (u : ℕ) (M1 : ℕ → ℕ) (c0 k : ℕ) (st : State) : Prop :=
  E.R st ∧ st.regs 9 = u ∧ st.regs 10 = k ∧ c0 ≤ st.regs 13 ∧ st.regs 13 ≤ c0 + (k - E.o u) ∧
    (∀ a, (a < E.OUT + c0 ∨ E.OUT + E.m ≤ a) → st.mem a = M1 a) ∧
    (∀ j, c0 ≤ j → j < st.regs 13 → st.mem (E.OUT + j) ∈ (E.g u).take (k - E.o u) ∧
      M1 (E.BEST + E.oth (st.mem (E.OUT + j))) = st.mem (E.OUT + j)) ∧
    (∀ q ∈ (E.g u).take (k - E.o u), M1 (E.BEST + E.oth q) = q →
      ∃ j, c0 ≤ j ∧ j < st.regs 13 ∧ st.mem (E.OUT + j) = q) ∧
    (∀ j1 j2, c0 ≤ j1 → j1 < st.regs 13 → c0 ≤ j2 → j2 < st.regs 13 →
      st.mem (E.OUT + j1) = st.mem (E.OUT + j2) → j1 = j2)

theorem not_mem_take {u j : ℕ} (hj : j < (E.g u).length) :
    (E.g u).getD j 0 ∉ (E.g u).take j := by
  have hnd : ((E.g u).take (j + 1)).Nodup := (g_nodup u).sublist (List.take_sublist _ _)
  rw [take_succ_g hj] at hnd
  intro hm
  exact (List.nodup_append.mp hnd).2.2 _ hm _ (by simp) rfl

theorem pass2 (h : E.Ok w) {u : ℕ} (hu : u < E.n) (M1 : ℕ → ℕ)
    (hM1 : ∀ a < E.MARK, M1 a = E.mem0 a) (c0 : ℕ) (hc0 : c0 ≤ E.o u) :
    Triple w p (fun st => E.R st ∧ st.regs 9 = u ∧ st.regs 13 = c0 ∧ st.mem = M1)
      (forRange 10 ddLo ddHi ddB2) (normalPost (I2 E u M1 c0 (E.o (u + 1))))
      (fun _ => (E.o (u + 1) - E.o u) * (100 + ddHi.size + 8) + (ddLo.size + ddHi.size + 5)) := by
  have l1 := h.l1; have l2 := h.l2; have l3 := h.l3; have l4 := h.l4; have l5 := h.l5
  have l6 := h.l6; have l7 := h.l7
  have hom := E.o_le (u + 1)
  have hmono : E.o u ≤ E.o (u + 1) := by rw [o_succ]; omega
  have hw1 : 1 < 2 ^ w := by omega
  have hoff : ∀ x ≤ E.n, M1 (E.OFF + x) = E.o x := fun x hx => by
    rw [hM1 _ (by omega)]; exact h.off x hx
  refine Triple.forRange_const (Inv := I2 E u M1 c0) 100 (E.o u) (E.o (u + 1)) hmono hw1
    (fun _ => by omega) ?_ ?_ ?_ ?_
  · rintro st ⟨hr, h9, h13, hm⟩
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := hr
    have hlo : st.mem (E.OFF + u) = E.o u := by rw [hm]; exact hoff u hu.le
    refine ⟨by simp only [ddLo]; eval_expr, R.upd ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ (by omega) _,
      by simp [h9], by simp, by simp [h13], by simp [h13], fun a _ => by simp [hm],
      fun j hj1 hj2 => by simp [h13] at hj2; omega, fun q hq => by simp at hq,
      fun j1 j2 h1 h2 => by simp [h13] at h2; omega⟩
  · intro _ st _ _ hI; exact hI.2.2.1
  · intro _ st _ _ hI
    obtain ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩, h9, -, -, -, hfr, -⟩ := hI
    have : st.mem (E.OFF + u + 1) = E.o (u + 1) := by
      rw [hfr _ (by omega), show E.OFF + u + 1 = E.OFF + (u + 1) by omega]; exact hoff _ hu
    simp only [ddHi]; eval_expr
  · intro k hk1 hk2 st ω hI
    obtain ⟨hr, h9, h10, hc1, hc2, hfr, hnew, hemit, hdist⟩ := hI
    have hM : ∀ a < E.MARK, st.mem a = E.mem0 a := fun a ha => by
      rw [hfr a (Or.inl (by omega)), hM1 a ha]
    have hat := at_k h hu hk1 hk2 hM
    set q := (E.g u).getD (k - E.o u) 0 with hqdef
    obtain ⟨eq1, hq, hqm, hqk, hoth, eu, ev, ewt, eo, etake⟩ := hat
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := hr
    have hpu := (h.ends q hqm).1
    have hpv := (h.ends q hqm).2
    have hnq : q ∉ (E.g u).take (k - E.o u) := not_mem_take (by rw [o_succ] at hk2; omega)
    have hA : st.mem (st.regs 2 + 3 * st.mem (E.ORD + k)) = E.pu q := by rw [a2, eq1, eu]
    have hB : st.mem (st.regs 2 + 3 * st.mem (E.ORD + k) + 1) = E.pv q := by rw [a2, eq1, ev]
    have hidx7 : st.regs 7 + (st.mem (st.regs 2 + 3 * st.mem (E.ORD + k)) +
        st.mem (st.regs 2 + 3 * st.mem (E.ORD + k) + 1) - st.regs 9) = E.BEST + E.oth q := by
      omega
    have hidx7' : st.regs 7 + (st.mem (st.regs 2 + 3 * q) + st.mem (st.regs 2 + 3 * q + 1) -
        st.regs 9) = E.BEST + E.oth q := by have := hidx7; rw [eq1] at this; exact this
    have hBSq : st.mem (E.BEST + E.oth q) = M1 (E.BEST + E.oth q) := hfr _ (Or.inl (by omega))
    have hRt : ∀ M : ℕ → ℕ, ∀ x y z ps,
        E.R ⟨M, Function.update (Function.update (Function.update st.regs 11 x) 12 y) 10 z, ps⟩ := by
      intro M x y z ps
      simp only [DDE.R]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [Function.update_apply, a0, a1, a2, a3, a4, a5, a6, a7, a8]
    have hc3 : st.regs 13 < E.m := by have := E.o_le (u + 1); omega
    refine runs_start_le ?_
    dsimp only [ddB2, ddOth]
    have hR0 : E.R st := ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩
    wram_run
    all_goals (try wram_cost)
    · -- emit
      have hb : M1 (E.BEST + E.oth q) = q := by rw [eq1, hidx7', hBSq] at hcond; exact hcond
      simp only [normalPost, eq1, a8]
      refine ⟨⟨hR0.of (fun i hi => by simp only [Function.update_apply]; split_ifs <;> omega),
        by simp [h9], by simp, by simp; omega, by simp; omega, fun a ha => ?_, fun j hj1 hj2 => ?_,
        fun q' hq' hq'b => ?_, fun j1 j2 h1 h2 h3 h4 h5 => ?_⟩, by simp [h10]⟩
      · simp only [Function.update_apply]; rw [if_neg (by omega)]; exact hfr a ha
      · simp only [Function.update_apply, if_neg (show (13 : ℕ) ≠ 10 by omega), if_pos rfl, ↓reduceIte] at hj2 ⊢
        rw [etake]
        by_cases hjc : j = st.regs 13
        · subst hjc; simp [hb]
        · rw [if_neg (by omega)]
          obtain ⟨m1, m2⟩ := hnew j hj1 (by omega)
          exact ⟨List.mem_append_left _ m1, m2⟩
      · simp only [Function.update_apply, if_neg (show (13 : ℕ) ≠ 10 by omega), if_pos rfl, ↓reduceIte]
        rw [etake] at hq'
        rcases List.mem_append.mp hq' with hq' | hq'
        · obtain ⟨j, hj1, hj2, hj3⟩ := hemit q' hq' hq'b
          exact ⟨j, hj1, by omega, by rw [if_neg (by omega)]; exact hj3⟩
        · simp at hq'; subst hq'
          exact ⟨st.regs 13, hc1, by omega, by simp⟩
      · simp only [Function.update_apply, if_neg (show (13 : ℕ) ≠ 10 by omega), if_pos rfl, ↓reduceIte] at h2 h4 h5
        by_cases e1 : j1 = st.regs 13 <;> by_cases e2 : j2 = st.regs 13
        · omega
        · rw [if_pos (by omega), if_neg (by omega)] at h5
          exact absurd (h5 ▸ (hnew j2 h3 (by omega)).1) hnq
        · rw [if_neg (by omega), if_pos (by omega)] at h5
          exact absurd (h5 ▸ (hnew j1 h1 (by omega)).1) hnq
        · rw [if_neg (by omega), if_neg (by omega)] at h5
          exact hdist j1 j2 h1 (by omega) h3 (by omega) h5
    · -- skip
      have hb : M1 (E.BEST + E.oth q) ≠ q := by rw [eq1, hidx7', hBSq] at hcond; exact hcond
      simp only [normalPost]
      refine ⟨⟨hR0.of (fun i hi => by simp only [Function.update_apply]; split_ifs <;> omega),
        by simp [h9], by simp, by simp; omega, by simp; omega, fun a ha => hfr a ha,
        fun j hj1 hj2 => ?_, fun q' hq' hq'b => ?_, fun j1 j2 h1 h2 h3 h4 h5 => ?_⟩, by simp [h10]⟩
      · simp only [Function.update_apply, if_neg (show (13 : ℕ) ≠ 10 by omega),
          if_neg (show (13 : ℕ) ≠ 12 by omega), if_neg (show (13 : ℕ) ≠ 11 by omega), ↓reduceIte] at hj2
        rw [etake]
        obtain ⟨m1, m2⟩ := hnew j hj1 hj2
        exact ⟨List.mem_append_left _ m1, m2⟩
      · simp only [Function.update_apply, if_neg (show (13 : ℕ) ≠ 10 by omega),
          if_neg (show (13 : ℕ) ≠ 12 by omega), if_neg (show (13 : ℕ) ≠ 11 by omega), ↓reduceIte]
        rw [etake] at hq'
        rcases List.mem_append.mp hq' with hq' | hq'
        · exact hemit q' hq' hq'b
        · simp at hq'; subst hq'; exact absurd hq'b hb
      · simp only [Function.update_apply, if_neg (show (13 : ℕ) ≠ 10 by omega),
          if_neg (show (13 : ℕ) ≠ 12 by omega), if_neg (show (13 : ℕ) ≠ 11 by omega), ↓reduceIte] at h2 h4
        exact hdist j1 j2 h1 h2 h3 h4 h5

/-- The invariant of the loop over the groups, before the group of `u`. -/
def OI (E : DDE) (u : ℕ) (st : State) : Prop :=
  E.R st ∧ st.regs 9 = u ∧ (∀ a, (a < E.MARK ∨ E.OUT + E.m ≤ a) → st.mem a = E.mem0 a) ∧
    (∀ v < E.n, st.mem (E.MARK + v) ≤ u) ∧ st.regs 13 ≤ E.o u ∧
    (∀ j < st.regs 13, st.mem (E.OUT + j) < E.m ∧ E.key (st.mem (E.OUT + j)) < u) ∧
    (∀ q < E.m, E.key q < u → ∃ j < st.regs 13, E.key (st.mem (E.OUT + j)) = E.key q ∧
      E.oth (st.mem (E.OUT + j)) = E.oth q ∧ E.wt (st.mem (E.OUT + j)) ≤ E.wt q) ∧
    (∀ j1 < st.regs 13, ∀ j2 < st.regs 13,
      E.key (st.mem (E.OUT + j1)) = E.key (st.mem (E.OUT + j2)) →
      E.oth (st.mem (E.OUT + j1)) = E.oth (st.mem (E.OUT + j2)) → j1 = j2)

/-- The cost of one group. -/
def gCost (E : DDE) (u : ℕ) : ℕ :=
  2 * ((E.o (u + 1) - E.o u) * (100 + ddHi.size + 8) + (ddLo.size + ddHi.size + 5)) + 1

theorem group (h : E.Ok w) {u : ℕ} (hu : u < E.n) :
    Triple w p (OI E u) ddGroup
      (normalPost fun st => OI E (u + 1) { st with regs := Function.update st.regs 9 (u + 1) } ∧
        st.regs 9 = u) (fun _ => gCost E u) := by
  have l1 := h.l1; have l2 := h.l2; have l3 := h.l3; have l4 := h.l4; have l5 := h.l5
  have l6 := h.l6; have l7 := h.l7
  intro st ω hI
  obtain ⟨hr, h9, hfr, hmk, hc, hout, hcov, hinj⟩ := hI
  have hM0 : ∀ a < E.MARK, st.mem a = E.mem0 a := fun a ha => hfr a (Or.inl ha)
  refine runs_start_le ?_
  dsimp only [ddGroup]
  refine runs_seq_triple_le (pass1 h hu st.mem hM0 (st.regs 13)) ⟨hr, h9, rfl, rfl, hmk⟩
    (fun st1 h1 => ?_)
  obtain ⟨hr1, h91, -, h131, hfr1, hP⟩ := h1
  have hM1 : ∀ a < E.MARK, st1.mem a = E.mem0 a := fun a ha => by
    rw [hfr1 a (Or.inl ha), hM0 a ha]
  refine runs_triple_le (pass2 h hu st1.mem hM1 (st.regs 13) hc) ⟨hr1, h91, h131, rfl⟩
    (fun o st2 hq => ?_) (by simp only [gCost]; omega)
  rcases o with _ | v
  swap
  · exact hq.elim
  have hI2 : I2 E u st1.mem (st.regs 13) (E.o (u + 1)) st2 := hq
  refine ⟨?_, hI2.2.1⟩
  obtain ⟨hr2, h92, -, hc1, hc2, hfr2, hnew, hemit, hdist⟩ := hI2
  have hlen : E.o (u + 1) - E.o u = (E.g u).length := by rw [o_succ]; omega
  rw [hlen] at hc2
  rw [hlen, List.take_of_length_le le_rfl] at hnew hemit hP
  have hom := E.o_le (u + 1)
  -- old entries keep their values
  have hold : ∀ j < st.regs 13, st2.mem (E.OUT + j) = st.mem (E.OUT + j) := fun j hj => by
    rw [hfr2 _ (Or.inl (by omega)), hfr1 _ (Or.inr (by omega))]
  refine ⟨hr2.upd (by omega) _, by simp, fun a ha => ?_, fun v hv => ?_, ?_, fun j hj => ?_,
    fun q hq hqk => ?_, fun j1 hj1 j2 hj2 hk ho => ?_⟩
  · rcases ha with ha | ha
    · rw [hfr2 a (Or.inl (by omega)), hM1 a ha]
    · rw [hfr2 a (Or.inr ha), hfr1 a (Or.inr (by omega))]; exact hfr a (Or.inr ha)
  · simp only
    rw [hfr2 _ (Or.inl (by omega))]
    exact (hP v hv).1
  · simp only [Function.update_apply, if_neg (show (13 : ℕ) ≠ 9 by omega)]
    rw [o_succ]; omega
  · simp only [Function.update_apply, if_neg (show (13 : ℕ) ≠ 9 by omega)] at hj ⊢
    by_cases hj0 : j < st.regs 13
    · rw [hold j hj0]
      obtain ⟨a1, a2⟩ := hout j hj0
      exact ⟨a1, by omega⟩
    · obtain ⟨m1, -⟩ := hnew j (by omega) hj
      obtain ⟨a1, a2⟩ := mem_g.mp m1
      exact ⟨a1, by omega⟩
  · simp only [Function.update_apply, if_neg (show (13 : ℕ) ≠ 9 by omega)]
    by_cases hqu : E.key q < u
    · obtain ⟨j, hj, e1, e2, e3⟩ := hcov q hq hqu
      exact ⟨j, by omega, by rw [hold j hj]; exact e1, by rw [hold j hj]; exact e2,
        by rw [hold j hj]; exact e3⟩
    · have hqk' : E.key q = u := by omega
      have hqg : q ∈ E.g u := mem_g.mpr ⟨hq, hqk'⟩
      have hv := oth_lt h hq
      obtain ⟨-, hiff, hbest⟩ := hP (E.oth q) hv
      have hm := hiff.mpr ⟨q, hqg, rfl⟩
      obtain ⟨b1, b2, b3⟩ := hbest hm
      obtain ⟨j, hj1, hj2, hj3⟩ := hemit _ b1 (by rw [b2])
      have hbk := (mem_g.mp b1).2
      exact ⟨j, hj2, by rw [hj3, hbk, hqk'], by rw [hj3, b2], by rw [hj3]; exact b3 q hqg rfl⟩
  · simp only [Function.update_apply, if_neg (show (13 : ℕ) ≠ 9 by omega)] at hj1 hj2
    have hkey : ∀ j < st2.regs 13, st.regs 13 ≤ j → E.key (st2.mem (E.OUT + j)) = u := fun j hj hj' =>
      (mem_g.mp (hnew j hj' hj).1).2
    by_cases e1 : j1 < st.regs 13 <;> by_cases e2 : j2 < st.regs 13
    · rw [hold j1 e1, hold j2 e2] at hk ho
      exact hinj j1 e1 j2 e2 hk ho
    · have := (hout j1 e1).2; rw [hold j1 e1] at hk; rw [hk, hkey j2 hj2 (by omega)] at this; omega
    · have := (hout j2 e2).2; rw [hold j2 e2] at hk; rw [← hk, hkey j1 hj1 (by omega)] at this
      omega
    · have b1 := (hnew j1 (by omega) hj1).2
      have b2 := (hnew j2 (by omega) hj2).2
      rw [ho] at b1
      exact hdist j1 j2 (by omega) hj1 (by omega) hj2 (b1.symm.trans b2)

theorem rangeCost_snoc (f : ℕ → ℕ) (N : ℕ) : rangeCost f 0 (N + 1) = rangeCost f 0 N + f N := by
  rw [rangeCost_zero_eq_range, rangeCost_zero_eq_range, List.range_succ, List.map_append,
    List.sum_append]
  simp

theorem rangeCost_tele (f : ℕ → ℕ) (hf : ∀ u, f u ≤ f (u + 1)) (a b N : ℕ) :
    rangeCost (fun u => a * (f (u + 1) - f u) + b) 0 N + a * f 0 ≤ a * f N + b * N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [rangeCost_snoc]
    have h1 : a * (f (N + 1) - f N) + a * f N = a * f (N + 1) := by
      rw [← Nat.mul_add]; congr 1; have := hf N; omega
    nlinarith

end DDE

/-- The numbers of `ddP` read from its arguments. -/
def DDE.ofArgs (args : List ℕ) (mem : ℕ → ℕ) : DDE :=
  ⟨args.getD 0 0, args.getD 1 0, args.getD 2 0, args.getD 3 0, args.getD 4 0, args.getD 5 0,
    args.getD 6 0, args.getD 7 0, args.getD 8 0, mem⟩

/-- The contract of `ddP`. It returns the number `c` of pairs it writes to `OUT`. -/
def ddC (w : ℕ) : Contract where
  pre args mem := args.length = 9 ∧ (DDE.ofArgs args mem).Ok w
  post args mem c mem' :=
    let E := DDE.ofArgs args mem
    c ≤ E.m ∧ (∀ j < c, mem' (E.OUT + j) < E.m) ∧
    (∀ q < E.m, ∃ j < c, E.key (mem' (E.OUT + j)) = E.key q ∧
      E.oth (mem' (E.OUT + j)) = E.oth q ∧ E.wt (mem' (E.OUT + j)) ≤ E.wt q) ∧
    (∀ j1 < c, ∀ j2 < c, E.key (mem' (E.OUT + j1)) = E.key (mem' (E.OUT + j2)) →
      E.oth (mem' (E.OUT + j1)) = E.oth (mem' (E.OUT + j2)) → j1 = j2) ∧
    ∀ a, (a < E.MARK ∨ E.OUT + E.m ≤ a) → mem' a = mem a
  cost args _ := 300 * (args.getD 0 0 + args.getD 1 0 + 1)

namespace DDE

theorem ddP_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [ddP]) :
    MeetsContract w p b (ddC w) := by
  intro args mem pos ω hwords ⟨hlen, h⟩
  have hargs0 : args = [args.getD 0 0, args.getD 1 0, args.getD 2 0, args.getD 3 0,
      args.getD 4 0, args.getD 5 0, args.getD 6 0, args.getD 7 0, args.getD 8 0] := by
    match args, hlen with
    | [a0, a1, a2, a3, a4, a5, a6, a7, a8], _ => rfl
  set E := DDE.ofArgs args mem with hE
  have hproc : p.procs[b]? = some ddP := hp 0 (by simp)
  clear hp
  have l1 := h.l1; have l2 := h.l2; have l3 := h.l3; have l4 := h.l4; have l5 := h.l5
  have l6 := h.l6; have l7 := h.l7
  have hw1 : 1 < 2 ^ w := by omega
  have hargs : args = [E.m, E.n, E.IN, E.PE, E.OFF, E.ORD, E.MARK, E.BEST, E.OUT] := hargs0
  have hR0 : E.R (startState args mem pos) := by
    rw [hargs]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hmem : E.mem0 = mem := rfl
  -- clearing the marks
  let IC : ℕ → State → Prop := fun i st => E.R st ∧ st.regs 15 = i ∧
    (∀ a, (a < E.MARK ∨ E.MARK + E.n ≤ a) → st.mem a = mem a) ∧ ∀ v < i, st.mem (E.MARK + v) = 0
  have hClr := Triple.forRange_const (p := p) (r := 15) (lo := .const 0) (hi := .reg 1)
    (body := .store (.bin .add (.reg 6) (.reg 15)) (.const 0))
    (P := fun st => E.R st ∧ st.mem = mem) (Inv := IC) 6 0 E.n (Nat.zero_le _) hw1
    (fun _ => by omega)
    (fun st ⟨hr, hm⟩ => ⟨by eval_expr, hr.upd (by omega) _, by simp, fun a _ => by simp [hm],
      fun v hv => absurd hv (by omega)⟩)
    (fun _ st _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by have := hI.1.2.1; eval_expr)
    (fun i _ hi st ω hI => by
      obtain ⟨hr, h15, hfr, hz⟩ := hI
      have hr' := hr
      obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := hr
      refine runs_start_le ?_
      wram_run
      · refine ⟨⟨hr'.upd (by omega) _, by simp, fun a ha => ?_, fun v hv => ?_⟩, h15⟩
        · simp only [Function.update_apply]
          rw [if_neg (by omega)]; exact hfr a ha
        · simp only [Function.update_apply]
          by_cases hvi : v = i
          · subst hvi; simp [a6, h15]
          · rw [if_neg (by omega)]; exact hz v (by omega)
      · wram_cost)
  have hOut := Triple.forRange_le (p := p) (r := 9) (lo := .const 0) (hi := .reg 1)
    (body := ddGroup) (P := fun st => OI E 0 { st with regs := Function.update st.regs 9 0 })
    (Inv := OI E) (gCost E) 0 E.n (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hP => ⟨by eval_expr, hP⟩)
    (fun _ st _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by have := hI.1.2.1; eval_expr)
    (fun u _ hu => group h hu)
  refine ⟨ddP, hproc, ?_⟩
  dsimp only [ddP]
  refine runs_start_le ?_
  refine runs_seq_triple_le hClr ⟨hR0, rfl⟩ (fun st1 h1 => ?_)
  obtain ⟨hr1, -, hfr1, hz1⟩ := h1
  wram_step
  refine runs_seq_triple_le hOut ?_ (fun st2 h2 => ?_)
  · refine ⟨(hr1.upd (by omega) _).upd (by omega) _, by simp, fun a ha => ?_, fun v hv => ?_,
      by simp [o, offOf_zero], fun j hj => by simp at hj, fun q _ hq => absurd hq (by omega),
      fun j1 hj1 => by simp at hj1⟩
    · exact hfr1 a (by omega)
    · simp only; rw [hz1 v hv]
  obtain ⟨⟨a0, -⟩, -, hfr2, -, hc2, hout2, hcov2, hinj2⟩ := h2
  refine runs_ret_le (by eval_expr) ⟨?_, fun j hj => (hout2 j hj).1,
    fun q hq => hcov2 q hq (key_lt h hq), hinj2, hfr2⟩ ?_
  · exact hc2.trans (E.o_le E.n)
  · have ht := rangeCost_tele E.o (fun u => by rw [o_succ]; omega) (2 * (100 + ddHi.size + 8))
      (2 * (ddLo.size + ddHi.size + 5) + 1) E.n
    have hgc : gCost E = fun u => 2 * (100 + ddHi.size + 8) * (E.o (u + 1) - E.o u) +
        (2 * (ddLo.size + ddHi.size + 5) + 1) := by
      funext u; simp only [gCost]; ring
    rw [← hgc] at ht
    have hon := E.o_le E.n
    simp only [ddC, ddHi, ddLo, Expr.size] at ht ⊢
    rw [hargs] at *
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    omega
end DDE

end MinCostFlow.LowStretch
