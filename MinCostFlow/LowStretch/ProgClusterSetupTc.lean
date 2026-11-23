module

public import MinCostFlow.LowStretch.ProgClusterSetupAc

/-!
# The setup of a cluster: the contracts of its tables

The setup writes six tables with the table loop `tabP` (`ProgPreLoop.lean`): two copies
(`cpE`), the halves (`halfE`), the exponents of the active entries (`expE`), and the tables
`P2`, `SQ` of the tests (`p2E`, `sqE`). This file states the contract of each, as an instance of
`tabC`, and proves it from `tabP_spec` (`suCpC_spec`, …). The precondition of each asks only that
the cells the expression reads lie outside the written range and that the values are words.

It also gives the addresses of the layout as numbers (`SuN.z_le_hS`), and the register state
`SuR` that the steps after `actP` start from.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-! ### The contracts of the tables -/

/-- The precondition of the copy with `args = [M, DST, SRC]`: the source lies below the
target. -/
def cpPre (w : ℕ) (args : List ℕ) (_ : ℕ → ℕ) : Prop :=
  ∃ M DST SRC, args = [M, DST, SRC] ∧ SRC + M ≤ DST ∧ SRC + M < 2 ^ w

/-- The copy: `DST[i] = SRC[i]`. -/
def cpF (args : List ℕ) (mem : ℕ → ℕ) (i : ℕ) : ℕ := mem (args.getD 2 0 + i)

/-- The contract of the copy. -/
def suCpC (w : ℕ) : Contract := tabC w cpE (cpPre w) cpF

theorem suCpC_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [tabP cpE]) :
    MeetsContract w p b (suCpC w) := by
  refine tabP_spec hp fun args mem hpre st hR h15 hfr => ?_
  obtain ⟨M, DST, SRC, rfl, h1, h2⟩ := hpre
  have e2 : st.regs 2 = SRC := hR 2 (by norm_num)
  simp only [List.getD_cons_zero, List.getD_cons_succ] at h15 hfr
  rw [cpE_eval e2 rfl (by omega), hfr _ (Or.inl (by omega))]
  rfl

/-- The precondition of the halves. -/
def halfPre (w : ℕ) (args : List ℕ) (_ : ℕ → ℕ) : Prop :=
  2 < 2 ^ w ∧ args.getD 0 0 < 2 ^ w

/-- The halves: `DST[i] = i / 2`. -/
def halfF (_ : List ℕ) (_ : ℕ → ℕ) (i : ℕ) : ℕ := i / 2

/-- The contract of the halves. -/
def suHalfC (w : ℕ) : Contract := tabC w halfE (halfPre w) halfF

theorem suHalfC_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [tabP halfE]) :
    MeetsContract w p b (suHalfC w) :=
  tabP_spec hp fun _ _ hpre _ _ h15 _ => by
    have := hpre.2
    exact halfE_eval rfl hpre.1 (by omega)

/-- The precondition of the exponents with `args = [M, DST, EG, ACT]`: the entries `ACT` and
the exponents `EG` lie below the target. -/
def expPre (w : ℕ) (args : List ℕ) (mem : ℕ → ℕ) : Prop :=
  ∃ M DST EG ACT, args = [M, DST, EG, ACT] ∧ ACT + 2 * M ≤ DST ∧ 2 < 2 ^ w ∧ DST < 2 ^ w ∧
    ∀ i < M, EG + mem (ACT + 2 * i) < DST

/-- The exponents: `DST[i] = EG[ACT[2 i]]`. -/
def expF (args : List ℕ) (mem : ℕ → ℕ) (i : ℕ) : ℕ :=
  mem (args.getD 2 0 + mem (args.getD 3 0 + 2 * i))

/-- The contract of the exponents. -/
def suExpC (w : ℕ) : Contract := tabC w expE (expPre w) expF

theorem suExpC_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [tabP expE]) :
    MeetsContract w p b (suExpC w) := by
  refine tabP_spec hp fun args mem hpre st hR h15 hfr => ?_
  obtain ⟨M, DST, EG, ACT, rfl, h1, h2, h4, h3⟩ := hpre
  simp only [List.getD_cons_zero, List.getD_cons_succ] at h15 hfr
  have e2 : st.regs 2 = EG := hR 2 (by norm_num)
  have e3 : st.regs 3 = ACT := hR 3 (by norm_num)
  have m1 : st.mem (ACT + 2 * st.regs 15) = mem (ACT + 2 * st.regs 15) :=
    hfr _ (Or.inl (by omega))
  have b1 := h3 _ h15
  rw [← m1] at b1
  rw [expE_eval e2 e3 rfl h2 (by omega) (by omega), hfr _ (Or.inl b1), m1]
  rfl

/-- The precondition of `P2` with `args = [M, DST, L, bw]`: `2 ^ 2 ^ L` is a word. -/
def p2Pre (w : ℕ) (args : List ℕ) (_ : ℕ → ℕ) : Prop := 2 ^ 2 ^ args.getD 2 0 < 2 ^ w

/-- `P2[i] = 2 ^ 2 ^ (L - i)`. -/
def p2F (args : List ℕ) (_ : ℕ → ℕ) (i : ℕ) : ℕ := 2 ^ 2 ^ (args.getD 2 0 - i)

/-- The contract of `P2`. -/
def suP2C (w : ℕ) : Contract := tabC w p2E (p2Pre w) p2F

theorem suP2C_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [tabP p2E]) :
    MeetsContract w p b (suP2C w) :=
  tabP_spec hp fun _ _ hpre _ hR _ _ => p2E_eval (hR 2 (by norm_num)) rfl hpre

/-- The precondition of `SQ` with `args = [M, DST, L, bw]`: `M ≤ L + 2`, and `2 ^ L + 3` and
`bw` are words. -/
def sqPre (w : ℕ) (args : List ℕ) (_ : ℕ → ℕ) : Prop :=
  args.getD 0 0 ≤ args.getD 2 0 + 2 ∧ 2 ^ args.getD 2 0 + 3 < 2 ^ w ∧ args.getD 3 0 < 2 ^ w

/-- `SQ[i] = bw / (2 ^ (L - (i - 1)) + 3)`. -/
def sqF (args : List ℕ) (_ : ℕ → ℕ) (i : ℕ) : ℕ :=
  args.getD 3 0 / (2 ^ (args.getD 2 0 - (i - 1)) + 3)

/-- The contract of `SQ`. -/
def suSqC (w : ℕ) : Contract := tabC w sqE (sqPre w) sqF

theorem suSqC_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [tabP sqE]) :
    MeetsContract w p b (suSqC w) :=
  tabP_spec hp fun _ _ hpre _ hR h15 _ => by
    have := hpre.1
    exact sqE_eval (hR 2 (by norm_num)) (hR 3 (by norm_num)) rfl (by omega) hpre.2.1 hpre.2.2

/-! ### The layout and the registers after `actP` -/

/-- Every address `z a b c k` of the layout with small coefficients is at most `hS`. -/
theorem SuN.z_le_hS (N : SuN) {a b c k : ℕ} (ha : a ≤ 23) (hb : b ≤ 26) (hc : c ≤ 2)
    (hk : k ≤ 16) : N.z a b c k ≤ N.hS := by
  have h1 : N.z a b c k ≤ N.D := by
    unfold SuN.D SuN.z
    have := Nat.mul_le_mul_right N.nS ha
    have := Nat.mul_le_mul_right N.s hb
    have := Nat.mul_le_mul_right N.L hc
    omega
  unfold SuN.hS SuN.r SuN.RR
  omega

/-- The registers of the setup after `actP`: the loads `V`, `Δ` in register `23`, `Z` in `24`,
`L` in `28` and the number `nA` of active entries in `30`, with the word facts that every
address of the layout needs. -/
structure SuR (w : ℕ) (V : SuV) (L Δ nA : ℕ) (st : State) : Prop where
  regs : V.Regs st
  r23 : st.regs 23 = Δ
  r24 : st.regs 24 = (V.N L).Z
  r28 : st.regs 28 = L
  r30 : st.regs 30 = nA
  hS : (V.N L).hS < 2 ^ w
  w20 : 2 ^ 20 < 2 ^ w
  nA_le : nA ≤ V.nS

namespace SuR

variable {w : ℕ} {V : SuV} {L Δ nA : ℕ} {st : State}

theorem upd (h : SuR w V L Δ nA st) {r : ℕ} (hr : 23 ≤ r) (h23 : r ≠ 23) (h24 : r ≠ 24)
    (h28 : r ≠ 28) (h30 : r ≠ 30) (v : ℕ) (M : ℕ → ℕ) (q : ℕ) :
    SuR w V L Δ nA { mem := M, regs := Function.update st.regs r v, pos := q } where
  regs := h.regs.upd hr v M q
  r23 := by dsimp only; rw [Function.update_of_ne (Ne.symm h23)]; exact h.r23
  r24 := by dsimp only; rw [Function.update_of_ne (Ne.symm h24)]; exact h.r24
  r28 := by dsimp only; rw [Function.update_of_ne (Ne.symm h28)]; exact h.r28
  r30 := by dsimp only; rw [Function.update_of_ne (Ne.symm h30)]; exact h.r30
  hS := h.hS
  w20 := h.w20
  nA_le := h.nA_le

theorem r (h : SuR w V L Δ nA st) {i : ℕ} (hi : i < 23) : st.regs i = V.vals.getD i 0 :=
  h.regs i hi

theorem r13 (h : SuR w V L Δ nA st) : st.regs 13 = (V.N L).s := h.regs 13 (by norm_num)

theorem r14 (h : SuR w V L Δ nA st) : st.regs 14 = (V.N L).nS := h.regs 14 (by norm_num)

theorem r11 (h : SuR w V L Δ nA st) : st.regs 11 = (V.N L).J := h.regs 11 (by norm_num)

/-- The value of an address `suZ a b c k`. -/
theorem z_eval (h : SuR w V L Δ nA st) {a b c k : ℕ} (ha : a ≤ 23) (hb : b ≤ 26) (hc : c ≤ 2)
    (hk : k ≤ 16) : (suZ a b c k).eval w st = some ((V.N L).z a b c k) :=
  suZ_eval h.r24 h.r14 h.r13 h.r28 h.w20 (by omega) (by omega) (by omega) (by omega) rfl
    (lt_of_le_of_lt ((V.N L).z_le_hS ha hb hc hk) h.hS)

theorem z_lt (h : SuR w V L Δ nA st) {a b c k : ℕ} (ha : a ≤ 23) (hb : b ≤ 26) (hc : c ≤ 2)
    (hk : k ≤ 16) : (V.N L).z a b c k < 2 ^ w :=
  lt_of_le_of_lt ((V.N L).z_le_hS ha hb hc hk) h.hS

end SuR

end MinCostFlow.LowStretch
