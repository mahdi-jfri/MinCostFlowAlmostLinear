module

public import WordRAM.Logic
public import WordRAM.Tactic

/-!
# The child of each node

The petal loop leaves the settled list of each petal: petal `k` is `PL[PO[k]], …,
PL[PO[k + 1] - 1]`. `chxP` writes `k + 1` to `CHX + u` for each node `u` of petal `k`
(`chxP_spec`). The memory from `CHX` on starts at zero, so the nodes of the stem keep `0`. The
lists of different petals have no common node. The cost is linear in the number of petals and in
the length of the lists.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The numbers of `chxP`. -/
structure CXE where
  nP : ℕ
  PL : ℕ
  PO : ℕ
  CHX : ℕ
  mem0 : ℕ → ℕ

namespace CXE

variable (E : CXE)

/-- The start of the list of petal `k`. -/
def o (k : ℕ) : ℕ := E.mem0 (E.PO + k)

/-- The node at position `j` of the lists. -/
def nd (j : ℕ) : ℕ := E.mem0 (E.PL + j)

/-- Position `j` lies in the list of petal `k`. -/
def In (k j : ℕ) : Prop := E.o k ≤ j ∧ j < E.o (k + 1)

/-- The precondition: the starts grow, the nodes are below `s`, the lists of two petals have no
common node, and the cells written lie above the lists. -/
structure Ok (w s : ℕ) : Prop where
  mono : ∀ k < E.nP, E.o k ≤ E.o (k + 1)
  nd_lt : ∀ k < E.nP, ∀ j, E.In k j → E.nd j < s
  disj : ∀ k1 < E.nP, ∀ k2 < E.nP, ∀ j1 j2, E.In k1 j1 → E.In k2 j2 → E.nd j1 = E.nd j2 →
    k1 = k2
  l1 : E.PL + E.o E.nP ≤ E.CHX
  l2 : E.PO + E.nP + 1 ≤ E.CHX
  l3 : E.CHX + s < 2 ^ w

/-- Position `j` of petal `k` has been handled before position `j0` of petal `k0`. -/
def W (k0 j0 k j : ℕ) : Prop := (k < k0 ∧ E.In k j) ∨ (k = k0 ∧ E.o k0 ≤ j ∧ j < j0)

/-- The memory after the positions before `j0` of petal `k0`. -/
def Done (M : ℕ → ℕ) (k0 j0 : ℕ) : Prop :=
  (∀ k j, E.W k0 j0 k j → M (E.CHX + E.nd j) = k + 1) ∧
    ∀ a, (∀ k j, E.W k0 j0 k j → a ≠ E.CHX + E.nd j) → M a = E.mem0 a

variable {E} {w s : ℕ}

theorem o_mono (h : E.Ok w s) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ E.nP) : E.o a ≤ E.o b := by
  induction b with
  | zero => have : a = 0 := by omega
            subst this; exact le_rfl
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le hab with e | e
    · rw [e]
    · have := ih (by omega) (by omega)
      have := h.mono b (by omega)
      omega

theorem o_le (h : E.Ok w s) {k : ℕ} (hk : k ≤ E.nP) : E.o k ≤ E.o E.nP := o_mono h hk le_rfl

theorem In.lt (h : E.Ok w s) {k j : ℕ} (hk : k < E.nP) (hj : E.In k j) : j < E.o E.nP := by
  have := o_le h (show k + 1 ≤ E.nP by omega)
  exact lt_of_lt_of_le hj.2 this

theorem W.lt (_h : E.Ok w s) {k0 j0 k j : ℕ} (hk0 : k0 < E.nP) (hj0 : j0 ≤ E.o (k0 + 1))
    (hw : E.W k0 j0 k j) : k < E.nP ∧ E.In k j := by
  rcases hw with ⟨h1, h2⟩ | ⟨rfl, h2, h3⟩
  · exact ⟨by omega, h2⟩
  · exact ⟨hk0, h2, by omega⟩

/-- The positions of petal `k0` all handled is the start of petal `k0 + 1`. -/
theorem W_next {k0 k j : ℕ} : E.W k0 (E.o (k0 + 1)) k j ↔ E.W (k0 + 1) (E.o (k0 + 1)) k j := by
  unfold W In
  constructor
  · rintro (⟨h1, h2⟩ | ⟨rfl, h2, h3⟩)
    · exact Or.inl ⟨by omega, h2⟩
    · exact Or.inl ⟨by omega, h2, h3⟩
  · rintro (⟨h1, h2⟩ | ⟨rfl, h2, h3⟩)
    · rcases Nat.lt_or_ge k k0 with hk | hk
      · exact Or.inl ⟨hk, h2⟩
      · have e : k = k0 := by omega
        subst e
        exact Or.inr ⟨rfl, h2.1, h2.2⟩
    · omega

theorem W_step {k0 j0 k j : ℕ} (hj0 : E.o k0 ≤ j0) :
    E.W k0 (j0 + 1) k j ↔ E.W k0 j0 k j ∨ (k = k0 ∧ j = j0) := by
  unfold W
  constructor
  · rintro (h | ⟨rfl, h2, h3⟩)
    · exact Or.inl (Or.inl h)
    · rcases Nat.lt_or_ge j j0 with hj | hj
      · exact Or.inl (Or.inr ⟨rfl, h2, hj⟩)
      · exact Or.inr ⟨rfl, by omega⟩
  · rintro ((h | ⟨rfl, h2, h3⟩) | ⟨rfl, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨rfl, h2, by omega⟩
    · exact Or.inr ⟨rfl, hj0, by omega⟩

/-- One store. -/
theorem Done.step (h : E.Ok w s) {M : ℕ → ℕ} {k0 j0 : ℕ} (hd : E.Done M k0 j0)
    (hk0 : k0 < E.nP) (hj0 : E.In k0 j0) :
    E.Done (Function.update M (E.CHX + E.nd j0) (k0 + 1)) k0 (j0 + 1) := by
  refine ⟨fun k j hw => ?_, fun a ha => ?_⟩
  · rcases (W_step hj0.1).mp hw with hw | ⟨rfl, rfl⟩
    · by_cases e : E.CHX + E.nd j = E.CHX + E.nd j0
      · rw [e, Function.update_self]
        obtain ⟨hk, hkj⟩ := hw.lt h hk0 (by have := hj0.2; omega)
        have := h.disj k hk k0 hk0 j j0 hkj hj0 (by omega)
        rw [this]
      · rw [Function.update_of_ne e]; exact hd.1 k j hw
    · exact Function.update_self _ _ _
  · have h1 : a ≠ E.CHX + E.nd j0 := ha k0 j0 ((W_step hj0.1).mpr (Or.inr ⟨rfl, rfl⟩))
    rw [Function.update_of_ne h1]
    exact hd.2 a fun k j hw => ha k j ((W_step hj0.1).mpr (Or.inl hw))

end CXE

/-- The inner body: `CHX[PL[j]] := k + 1`, with `k` in register `4` and `j` in register `5`. -/
def chxIn : Stmt :=
  .store (.bin .add (.reg 3) (.load (.bin .add (.reg 1) (.reg 5)))) (.bin .add (.reg 4) (.const 1))

/-- The start of the list of petal `k`. -/
def chxLo : Expr := .load (.bin .add (.reg 2) (.reg 4))

/-- The end of the list of petal `k`. -/
def chxHi : Expr := .load (.bin .add (.bin .add (.reg 2) (.reg 4)) (.const 1))

/-- `chxP` with `args = [nP, PL, PO, CHX]`. -/
def chxP : Stmt :=
  .seq (forRange 4 (.const 0) (.reg 0) (forRange 5 chxLo chxHi chxIn)) (.ret (.const 0))

theorem chxP_noRand : chxP.NoRand := by
  simp [chxP, chxIn, chxLo, chxHi, forRange, forUp, Stmt.NoRand]

/-- The contract of `chxP`. -/
def chxC (w : ℕ) : Contract where
  pre args mem := ∃ E : CXE, ∃ s, args = [E.nP, E.PL, E.PO, E.CHX] ∧ E.mem0 = mem ∧ E.Ok w s
  post args mem _ mem' := ∀ E : CXE, args = [E.nP, E.PL, E.PO, E.CHX] → E.mem0 = mem →
    (∀ k < E.nP, ∀ j, E.In k j → mem' (E.CHX + E.nd j) = k + 1) ∧
    ∀ a, (∀ k < E.nP, ∀ j, E.In k j → a ≠ E.CHX + E.nd j) → mem' a = mem a
  cost args mem := 40 * (mem (args.getD 2 0 + args.getD 0 0) - mem (args.getD 2 0) + args.getD 0 0 + 1)

namespace CXE

/-- The registers that never change. -/
def R (E : CXE) (st : State) : Prop :=
  st.regs 0 = E.nP ∧ st.regs 1 = E.PL ∧ st.regs 2 = E.PO ∧ st.regs 3 = E.CHX

theorem R.upd {E : CXE} {st : State} (h : E.R st) {r : ℕ} (hr : 4 ≤ r) (v : ℕ) :
    E.R { st with regs := Function.update st.regs r v } := by
  obtain ⟨a0, a1, a2, a3⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Function.update_apply] <;> rwa [ite_eq_right (by omega)]

private theorem tele (f : ℕ → ℕ) (N : ℕ) (hf : ∀ u < N, f u ≤ f (u + 1)) (a b : ℕ) :
    rangeCost (fun u => a * (f (u + 1) - f u) + b) 0 N + a * f 0 ≤ a * f N + b * N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [rangeCost_zero_eq_range, List.range_succ, List.map_append, List.sum_append,
      ← rangeCost_zero_eq_range]
    have := ih (fun u hu => hf u (by omega))
    have h1 : a * (f (N + 1) - f N) + a * f N = a * f (N + 1) := by
      rw [← Nat.mul_add]; congr 1; have := hf N (by omega); omega
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    nlinarith

end CXE

theorem chxP_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [chxP]) :
    MeetsContract w p b (chxC w) := by
  intro args mem pos ω hwords hpre
  obtain ⟨E, s, rfl, hm, h⟩ := hpre
  subst hm
  have hproc : p.procs[b]? = some chxP := hp 0 (by simp)
  clear hp
  have l1 := h.l1; have l2 := h.l2; have l3 := h.l3
  have hw1 : 1 < 2 ^ w := by omega
  have hoN := CXE.o_le h (le_refl E.nP)
  -- cells below `CHX` are never written
  have hlow : ∀ {M k0 j0}, E.Done M k0 j0 → ∀ a < E.CHX, M a = E.mem0 a := by
    intro M k0 j0 hd a ha
    exact hd.2 a fun k j _ => by omega
  -- the inner loop, for petal `k`
  have hinner : ∀ k < E.nP, Triple w p
      (fun st => E.R st ∧ st.regs 4 = k ∧ E.Done st.mem k (E.o k))
      (forRange 5 chxLo chxHi chxIn)
      (normalPost fun st => E.R st ∧ st.regs 4 = k ∧ E.Done st.mem k (E.o (k + 1)))
      (fun _ => (E.o (k + 1) - E.o k) * (20 + chxHi.size + 8) +
        (chxLo.size + chxHi.size + 5)) := by
    intro k hk
    have hmo := h.mono k hk
    have hk1 := CXE.o_le h (show k + 1 ≤ E.nP by omega)
    have := Triple.forRange_const (p := p) (r := 5) (lo := chxLo) (hi := chxHi) (body := chxIn)
      (P := fun st => E.R st ∧ st.regs 4 = k ∧ E.Done st.mem k (E.o k))
      (Inv := fun j st => E.R st ∧ st.regs 4 = k ∧ E.Done st.mem k j ∧ st.regs 5 = j)
      20 (E.o k) (E.o (k + 1)) hmo hw1 (fun _ => by omega)
      (fun st hP => by
        obtain ⟨hr, h4, hd⟩ := hP
        have hr' := hr
        obtain ⟨a0, a1, a2, a3⟩ := hr
        have e : st.mem (E.PO + k) = E.o k := by rw [hlow hd _ (by omega)]; rfl
        have b : st.regs 2 + st.regs 4 < 2 ^ w := by rw [a2, h4]; omega
        refine ⟨?_, hr'.upd (by omega) _, by simp [h4], hd, by simp⟩
        simp only [chxLo]
        eval_expr)
      (fun _ st _ _ hI => hI.2.2.2)
      (fun j st _ _ hI => by
        obtain ⟨⟨a0, a1, a2, a3⟩, h4, hd, -⟩ := hI
        have e : st.mem (E.PO + k + 1) = E.o (k + 1) := by
          rw [hlow hd _ (by omega)]; unfold CXE.o; rw [Nat.add_assoc]
        have b : st.regs 2 + st.regs 4 + 1 < 2 ^ w := by rw [a2, h4]; omega
        simp only [chxHi]
        eval_expr)
      (fun j hj1 hj2 st ω hI => by
        obtain ⟨hr, h4, hd, h5⟩ := hI
        have hr' := hr
        obtain ⟨a0, a1, a2, a3⟩ := hr
        have hIn : E.In k j := ⟨hj1, hj2⟩
        have hnd := h.nd_lt k hk j hIn
        have hjN : j < E.o E.nP := hIn.lt h hk
        have eN : st.mem (E.PL + j) = E.nd j := by rw [hlow hd _ (by omega)]; rfl
        have b1 : st.regs 1 + st.regs 5 < 2 ^ w := by rw [a1, h5]; omega
        have b2 : st.regs 3 + st.mem (st.regs 1 + st.regs 5) < 2 ^ w := by
          rw [a3, a1, h5, eN]; omega
        have b3 : st.regs 4 + 1 < 2 ^ w := by rw [h4]; omega
        refine runs_start_le ?_
        dsimp only [chxIn]
        wram_run
        · refine ⟨⟨hr'.upd (by omega) _, by simp [h4], ?_, by simp⟩, h5⟩
          dsimp only
          rw [eN]
          exact hd.step h hk hIn
        · wram_cost)
    refine this.strengthen_post ?_
    intro o st hq
    cases o with
    | returned v => exact hq.elim
    | normal => exact ⟨hq.1, hq.2.1, hq.2.2.1⟩
  have hloop := Triple.forRange_le (p := p) (r := 4) (lo := .const 0) (hi := .reg 0)
    (body := forRange 5 chxLo chxHi chxIn)
    (P := fun st => st = startState [E.nP, E.PL, E.PO, E.CHX] E.mem0 pos)
    (Inv := fun k st => E.R st ∧ st.regs 4 = k ∧ E.Done st.mem k (E.o k))
    (fun k => (E.o (k + 1) - E.o k) * (20 + chxHi.size + 8) + (chxLo.size + chxHi.size + 5))
    0 E.nP (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hst => by
      subst hst
      refine ⟨by eval_expr, CXE.R.upd ⟨rfl, rfl, rfl, rfl⟩ (by omega) _, by simp,
        fun k j hw => ?_, fun a _ => rfl⟩
      rcases hw with ⟨h1, -⟩ | ⟨-, h2, h3⟩ <;> omega)
    (fun _ st _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by have := hI.1.1; eval_expr)
    (fun k _ hk => (hinner k hk).strengthen_post fun o st hq => by
      cases o with
      | returned v => exact hq.elim
      | normal =>
        obtain ⟨hr, h4, hd⟩ := hq
        refine ⟨⟨hr.upd (by omega) _, by simp, ?_, fun a ha => ?_⟩, h4⟩
        · exact fun k' j hw => hd.1 k' j (CXE.W_next.mpr hw)
        · exact hd.2 a fun k' j hw => ha k' j (CXE.W_next.mp hw))
  refine ⟨chxP, hproc, ?_⟩
  dsimp only [chxP]
  refine runs_start_le ?_
  refine runs_seq_triple_le hloop rfl (fun st hI => ?_)
  obtain ⟨-, -, hd⟩ := hI
  refine runs_ret_le (by eval_expr) ?_ ?_
  · intro E' he hm'
    have e : E' = E := by
      cases E; cases E'; simp only [List.cons.injEq] at he; simp_all
    subst e
    refine ⟨fun k hk j hj => hd.1 k j (Or.inl ⟨hk, hj⟩), fun a ha => hd.2 a fun k j hw => ?_⟩
    rcases hw with ⟨h1, h2⟩ | ⟨-, h2, h3⟩
    · exact ha k h1 j h2
    · omega
  · have ht := CXE.tele E.o E.nP h.mono (20 + chxHi.size + 8) (chxLo.size + chxHi.size + 5)
    have hf : (fun k => (E.o (k + 1) - E.o k) * (20 + chxHi.size + 8) +
        (chxLo.size + chxHi.size + 5)) = (fun u => (20 + chxHi.size + 8) * (E.o (u + 1) - E.o u) +
        (chxLo.size + chxHi.size + 5)) := by
      funext u; ring
    rw [← hf] at ht
    have e0 : E.o E.nP = E.mem0 (E.PO + E.nP) := rfl
    have e1 : E.o 0 = E.mem0 E.PO := by unfold CXE.o; rw [Nat.add_zero]
    have hmo := CXE.o_mono h (Nat.zero_le E.nP) le_rfl
    simp only [chxC, chxHi, chxLo, Expr.size, List.getD_cons_zero, List.getD_cons_succ] at ht ⊢
    rw [← e0, ← e1]
    omega

end MinCostFlow.LowStretch
