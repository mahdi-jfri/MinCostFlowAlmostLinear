module

public import MinCostFlow.LowStretch.ProgTree

/-!
# The stored highway in the tree arrays

The special petal grows along the stored highway of the cluster, which need not be a path of the
tree of the first run. `hwFix` writes the stored highway over the tree arrays of `treeP`: for each
pair of the highway, at the node of its first end, the next node, the pair, its half flag, its
ends, and its length and class (`hwFix_spec`). Then the path of `PAR` from the target is the
stored highway, and the other nodes keep their tree parent. Along the highway the distance drops
by the length of each pair, so `PAR` still gives shortest walks to the center.

A highway pair is stored as four words: the pair, its half flag, its end at the side of the
target, and its other end.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The addresses that `hwFix` uses. -/
structure HF where
  nH : ℕ
  HW : ℕ
  LAB : ℕ
  LOC : ℕ
  PW : ℕ
  EXP : ℕ
  lθ : ℕ
  PAR : ℕ
  PP : ℕ
  PF : ℕ
  PA : ℕ
  PB : ℕ
  SCc : ℕ
  SCk : ℕ
  s : ℕ

namespace HF

variable (F : HF) (mem : ℕ → ℕ)

def args : List ℕ := [F.nH, F.HW, F.LAB, F.LOC, F.PW, F.EXP, F.lθ, F.PAR, F.PP, F.PF, F.PA, F.PB,
  F.SCc, F.SCk, F.s]

theorem eq_of_args {F F' : HF} (h : F.args = F'.args) : F' = F := by
  cases F; cases F'; simp only [HF.args, List.cons.injEq] at h
  simp_all

/-- The pair of highway entry `j`. -/
def hp (j : ℕ) : ℕ := mem (F.HW + 4 * j)
/-- Its half flag. -/
def hf (j : ℕ) : ℕ := mem (F.HW + 4 * j + 1)
/-- Its end at the side of the target. -/
def ha (j : ℕ) : ℕ := mem (F.HW + 4 * j + 2)
/-- Its other end. -/
def hb (j : ℕ) : ℕ := mem (F.HW + 4 * j + 3)
/-- The node of its end at the side of the target. -/
def nu (j : ℕ) : ℕ := mem (F.LOC + mem (F.LAB + F.ha mem j))
/-- The node of its other end. -/
def nv (j : ℕ) : ℕ := mem (F.LOC + mem (F.LAB + F.hb mem j))
/-- Its length. -/
def hl (j : ℕ) : ℕ := mem (F.PW + F.hp mem j) >>> F.hf mem j
/-- Its class. -/
def hk (j : ℕ) : ℕ := mem (F.EXP + F.hp mem j) + 2 - F.hf mem j - F.lθ

/-- The cells of entries below `i` hold their values. -/
def Done (M : ℕ → ℕ) (i : ℕ) : Prop :=
  ∀ j < i, M (F.PAR + F.nu mem j) = F.nv mem j ∧ M (F.PP + F.nu mem j) = F.hp mem j ∧
    M (F.PF + F.nu mem j) = F.hf mem j ∧ M (F.PA + F.nu mem j) = F.ha mem j ∧
    M (F.PB + F.nu mem j) = F.hb mem j ∧ M (F.SCc + F.nu mem j) = F.hl mem j ∧
    M (F.SCk + F.nu mem j) = F.hk mem j

/-- Cell `a` is not one of the cells of the entries below `i`. -/
def Free (i a : ℕ) : Prop :=
  ∀ j < i, a ≠ F.PAR + F.nu mem j ∧ a ≠ F.PP + F.nu mem j ∧ a ≠ F.PF + F.nu mem j ∧
    a ≠ F.PA + F.nu mem j ∧ a ≠ F.PB + F.nu mem j ∧ a ≠ F.SCc + F.nu mem j ∧
    a ≠ F.SCk + F.nu mem j

/-- The precondition: the nodes of the entries are distinct and below `s`, the written arrays
follow each other, and the cells that are read lie below them. -/
structure Pre (w : ℕ) : Prop where
  inj : ∀ j < F.nH, ∀ j' < F.nH, F.nu mem j = F.nu mem j' → j = j'
  nu_lt : ∀ j < F.nH, F.nu mem j < F.s
  l1 : F.PAR + F.s ≤ F.PP
  l2 : F.PP + F.s ≤ F.PF
  l3 : F.PF + F.s ≤ F.PA
  l4 : F.PA + F.s ≤ F.PB
  l5 : F.PB + F.s ≤ F.SCc
  l6 : F.SCc + F.s ≤ F.SCk
  l7 : F.SCk + F.s < 2 ^ w
  rHW : F.HW + 4 * F.nH ≤ F.PAR
  hw : 1 < 2 ^ w
  rd : ∀ j < F.nH, F.LAB + F.ha mem j < F.PAR ∧ F.LOC + mem (F.LAB + F.ha mem j) < F.PAR ∧
    F.LAB + F.hb mem j < F.PAR ∧ F.LOC + mem (F.LAB + F.hb mem j) < F.PAR ∧
    F.PW + F.hp mem j < F.PAR ∧ F.EXP + F.hp mem j < F.PAR ∧
    mem (F.PW + F.hp mem j) < 2 ^ w ∧ mem (F.EXP + F.hp mem j) + 2 < 2 ^ w

end HF

/-- One entry: its seven cells get their values, and nothing else changes. -/
theorem HF.Done.step {w : ℕ} {F : HF} {mem M M' : ℕ → ℕ} {i : ℕ} (hd : F.Done mem M i)
    (h : F.Pre mem w) (hi : i < F.nH)
    (h1 : M' (F.PAR + F.nu mem i) = F.nv mem i) (h2 : M' (F.PP + F.nu mem i) = F.hp mem i)
    (h3 : M' (F.PF + F.nu mem i) = F.hf mem i) (h4 : M' (F.PA + F.nu mem i) = F.ha mem i)
    (h5 : M' (F.PB + F.nu mem i) = F.hb mem i) (h6 : M' (F.SCc + F.nu mem i) = F.hl mem i)
    (h7 : M' (F.SCk + F.nu mem i) = F.hk mem i)
    (hfr : ∀ a, a ≠ F.PAR + F.nu mem i → a ≠ F.PP + F.nu mem i → a ≠ F.PF + F.nu mem i →
      a ≠ F.PA + F.nu mem i → a ≠ F.PB + F.nu mem i → a ≠ F.SCc + F.nu mem i →
      a ≠ F.SCk + F.nu mem i → M' a = M a) :
    F.Done mem M' (i + 1) := by
  have l1 := h.l1; have l2 := h.l2; have l3 := h.l3; have l4 := h.l4; have l5 := h.l5
  have l6 := h.l6
  intro j hj
  by_cases e : j = i
  · subst e; exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  · obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := hd j (by omega)
    have hne : F.nu mem j ≠ F.nu mem i := fun he => e (h.inj j (by omega) i hi he)
    have hj' := h.nu_lt j (by omega)
    have hi' := h.nu_lt i hi
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals
      first
      | (rw [hfr _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)];
          assumption)

theorem HF.Free.succ {F : HF} {mem : ℕ → ℕ} {i a : ℕ} (h : F.Free mem (i + 1) a) :
    F.Free mem i a ∧ a ≠ F.PAR + F.nu mem i ∧ a ≠ F.PP + F.nu mem i ∧ a ≠ F.PF + F.nu mem i ∧
      a ≠ F.PA + F.nu mem i ∧ a ≠ F.PB + F.nu mem i ∧ a ≠ F.SCc + F.nu mem i ∧
      a ≠ F.SCk + F.nu mem i :=
  ⟨fun j hj => h j (by omega), h i (by omega)⟩

/-- The body of `hwFix`, for entry `j` in register `15`. -/
def hwFixB : Stmt :=
  .seq (.assign 16 (.load (.bin .add (.reg 1) (.bin .mul (.const 4) (.reg 15)))))
  (.seq (.assign 17 (.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 4) (.reg 15)))
      (.const 1))))
  (.seq (.assign 18 (.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 4) (.reg 15)))
      (.const 2))))
  (.seq (.assign 19 (.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 4) (.reg 15)))
      (.const 3))))
  (.seq (.assign 20 (.load (.bin .add (.reg 3) (.load (.bin .add (.reg 2) (.reg 18))))))
  (.seq (.assign 21 (.load (.bin .add (.reg 3) (.load (.bin .add (.reg 2) (.reg 19))))))
  (.seq (.assign 22 (.bin .shiftRight (.load (.bin .add (.reg 4) (.reg 16))) (.reg 17)))
  (.seq (.assign 23 (.bin .sub (.bin .sub (.bin .add (.load (.bin .add (.reg 5) (.reg 16)))
      (.const 2)) (.reg 17)) (.reg 6)))
  (.seq (.store (.bin .add (.reg 7) (.reg 20)) (.reg 21))
  (.seq (.store (.bin .add (.reg 8) (.reg 20)) (.reg 16))
  (.seq (.store (.bin .add (.reg 9) (.reg 20)) (.reg 17))
  (.seq (.store (.bin .add (.reg 10) (.reg 20)) (.reg 18))
  (.seq (.store (.bin .add (.reg 11) (.reg 20)) (.reg 19))
  (.seq (.store (.bin .add (.reg 12) (.reg 20)) (.reg 22))
    (.store (.bin .add (.reg 13) (.reg 20)) (.reg 23)))))))))))))))

/-- `hwFix` with `args = F.args`. -/
def hwFix : Stmt := .seq (forRange 15 (.const 0) (.reg 0) hwFixB) (.ret (.const 0))

theorem hwFix_noRand : hwFix.NoRand := by
  simp [hwFix, hwFixB, forRange, forUp, Stmt.NoRand]

/-- The contract of `hwFix`. -/
def hwFixC (w : ℕ) : Contract where
  pre args mem := ∃ F : HF, args = F.args ∧ F.Pre mem w
  post args mem _ mem' := ∀ F : HF, args = F.args →
    F.Done mem mem' F.nH ∧ ∀ a, F.Free mem F.nH a → mem' a = mem a
  cost args _ := 250 * args.getD 0 0 + 20

end MinCostFlow.LowStretch

namespace MinCostFlow.LowStretch

open WordRAM

set_option maxHeartbeats 4000000 in
theorem hwFix_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [hwFix]) :
    MeetsContract w p b (hwFixC w) := by
  intro args mem pos ω hwords hpre
  obtain ⟨F, rfl, h⟩ := hpre
  have hproc : p.procs[b]? = some hwFix := hp 0 (by simp)
  clear hp
  have l1 := h.l1; have l2 := h.l2; have l3 := h.l3; have l4 := h.l4; have l5 := h.l5
  have l6 := h.l6; have l7 := h.l7; have rHW := h.rHW
  have hw1 : 1 < 2 ^ w := h.hw
  have hwA : ∀ a ∈ F.args, a < 2 ^ w := hwords
  simp only [HF.args, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hwA
  obtain ⟨wnH, wHW, wLAB, wLOC, wPW, wEXP, wlθ, wPAR, wPP, wPF, wPA, wPB, wSCc, wSCk, ws⟩ := hwA
  let R : State → Prop := fun st => st.regs 0 = F.nH ∧ st.regs 1 = F.HW ∧ st.regs 2 = F.LAB ∧
    st.regs 3 = F.LOC ∧ st.regs 4 = F.PW ∧ st.regs 5 = F.EXP ∧ st.regs 6 = F.lθ ∧
    st.regs 7 = F.PAR ∧ st.regs 8 = F.PP ∧ st.regs 9 = F.PF ∧ st.regs 10 = F.PA ∧
    st.regs 11 = F.PB ∧ st.regs 12 = F.SCc ∧ st.regs 13 = F.SCk ∧ st.regs 14 = F.s
  have hRu : ∀ st r v, R st → 15 ≤ r → R { st with regs := Function.update st.regs r v } := by
    intro st r v ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ hr
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Function.update_apply] <;> (rw [if_neg (by omega)]; assumption)
  let I : ℕ → State → Prop := fun i st => R st ∧ st.regs 15 = i ∧ F.Done mem st.mem i ∧
    ∀ a, F.Free mem i a → st.mem a = mem a
  have hloop := Triple.forRange_const (p := p) (r := 15) (lo := .const 0) (hi := .reg 0)
    (body := hwFixB) (P := fun st => R st ∧ st.mem = mem) (Inv := I) 200 0 F.nH
    (Nat.zero_le _) hw1 (fun _ => wnH)
    (fun st ⟨hr, hm⟩ => ⟨by eval_expr, hRu st 15 0 hr (by omega), by simp,
      fun j hj => absurd hj (by omega), fun a _ => by simp [hm]⟩)
    (fun _ st _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by have := hI.1.1; eval_expr)
    (fun i _ hi st ω hI => by
      obtain ⟨hr, h15, hdone, hfr⟩ := hI
      obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := hr
      have hRn : ∀ st' : State, (∀ r < 15, st'.regs r = st.regs r) → R st' := fun st' hs =>
        ⟨(hs 0 (by omega)).trans a0, (hs 1 (by omega)).trans a1, (hs 2 (by omega)).trans a2,
          (hs 3 (by omega)).trans a3, (hs 4 (by omega)).trans a4, (hs 5 (by omega)).trans a5,
          (hs 6 (by omega)).trans a6, (hs 7 (by omega)).trans a7, (hs 8 (by omega)).trans a8,
          (hs 9 (by omega)).trans a9, (hs 10 (by omega)).trans a10,
          (hs 11 (by omega)).trans a11, (hs 12 (by omega)).trans a12,
          (hs 13 (by omega)).trans a13, (hs 14 (by omega)).trans a14⟩
      have nOut : ∀ a, a < F.PAR → F.Free mem i a := by
        intro a ha j hj
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
      obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩ := h.rd i hi
      have hu := h.nu_lt i hi
      unfold HF.nu at hu
      have eP : st.mem (F.HW + 4 * i) = F.hp mem i := hfr _ (nOut _ (by omega))
      have eF : st.mem (F.HW + 4 * i + 1) = F.hf mem i := hfr _ (nOut _ (by omega))
      have eA : st.mem (F.HW + 4 * i + 2) = F.ha mem i := hfr _ (nOut _ (by omega))
      have eB : st.mem (F.HW + 4 * i + 3) = F.hb mem i := hfr _ (nOut _ (by omega))
      have eA1 : st.mem (F.LAB + F.ha mem i) = mem (F.LAB + F.ha mem i) := hfr _ (nOut _ r1)
      have eA2 : st.mem (F.LOC + mem (F.LAB + F.ha mem i)) = F.nu mem i := hfr _ (nOut _ r2)
      have eB1 : st.mem (F.LAB + F.hb mem i) = mem (F.LAB + F.hb mem i) := hfr _ (nOut _ r3)
      have eB2 : st.mem (F.LOC + mem (F.LAB + F.hb mem i)) = F.nv mem i := hfr _ (nOut _ r4)
      have eW : st.mem (F.PW + F.hp mem i) = mem (F.PW + F.hp mem i) := hfr _ (nOut _ r5)
      have eE : st.mem (F.EXP + F.hp mem i) = mem (F.EXP + F.hp mem i) := hfr _ (nOut _ r6)
      have hsh : mem (F.PW + F.hp mem i) >>> F.hf mem i ≤ mem (F.PW + F.hp mem i) := by
        rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _
      have c1 : F.HW + 4 * i + 3 < 2 ^ w := by omega
      have q0 : st.mem (st.regs 1 + 4 * st.regs 15) = F.hp mem i := by rw [a1, h15, eP]
      have q1 : st.mem (st.regs 1 + 4 * st.regs 15 + 1) = F.hf mem i := by rw [a1, h15, eF]
      have q2 : st.mem (st.regs 1 + 4 * st.regs 15 + 2) = F.ha mem i := by rw [a1, h15, eA]
      have q3 : st.mem (st.regs 1 + 4 * st.regs 15 + 3) = F.hb mem i := by rw [a1, h15, eB]
      have c2 : st.regs 2 + st.mem (st.regs 1 + 4 * st.regs 15 + 2) < 2 ^ w := by
        rw [a2, q2]; omega
      have c3 : st.regs 3 + st.mem (st.regs 2 + st.mem (st.regs 1 + 4 * st.regs 15 + 2)) < 2 ^ w := by
        rw [q2, a2, a3, eA1]; omega
      have c4 : st.regs 2 + st.mem (st.regs 1 + 4 * st.regs 15 + 3) < 2 ^ w := by
        rw [a2, q3]; omega
      have c5 : st.regs 3 + st.mem (st.regs 2 + st.mem (st.regs 1 + 4 * st.regs 15 + 3)) < 2 ^ w := by
        rw [q3, a2, a3, eB1]; omega
      have c6 : st.regs 4 + st.mem (st.regs 1 + 4 * st.regs 15) < 2 ^ w := by rw [a4, q0]; omega
      have c7 : st.regs 5 + st.mem (st.regs 1 + 4 * st.regs 15) < 2 ^ w := by rw [a5, q0]; omega
      have c8 : st.mem (st.regs 4 + st.mem (st.regs 1 + 4 * st.regs 15)) >>>
          st.mem (st.regs 1 + 4 * st.regs 15 + 1) < 2 ^ w := by rw [q0, q1, a4, eW]; omega
      have c9 : st.mem (st.regs 5 + st.mem (st.regs 1 + 4 * st.regs 15)) + 2 < 2 ^ w := by
        rw [q0, a5, eE]; omega
      have c8' : st.mem (st.regs 4 + st.mem (F.HW + 4 * i)) < 2 ^ w := by rw [a4, eP, eW]; omega
      have c9' : st.mem (st.regs 5 + st.mem (F.HW + 4 * i)) + 2 < 2 ^ w := by
        rw [a5, eP, eE]; omega
      have qU : st.mem (st.regs 3 + st.mem (st.regs 2 + st.mem (st.regs 1 + 4 * st.regs 15 + 2))) =
          F.nu mem i := by rw [q2, a2, a3, eA1, eA2]
      have qV : st.mem (st.regs 3 + st.mem (st.regs 2 + st.mem (st.regs 1 + 4 * st.regs 15 + 3))) =
          F.nv mem i := by rw [q3, a2, a3, eB1, eB2]
      have hu' := h.nu_lt i hi
      have d7 : st.regs 7 + st.mem (st.regs 3 + st.mem (st.regs 2 +
          st.mem (st.regs 1 + 4 * st.regs 15 + 2))) < 2 ^ w := by rw [qU, a7]; omega
      have d8 : st.regs 8 + st.mem (st.regs 3 + st.mem (st.regs 2 +
          st.mem (st.regs 1 + 4 * st.regs 15 + 2))) < 2 ^ w := by rw [qU, a8]; omega
      have d9 : st.regs 9 + st.mem (st.regs 3 + st.mem (st.regs 2 +
          st.mem (st.regs 1 + 4 * st.regs 15 + 2))) < 2 ^ w := by rw [qU, a9]; omega
      have d10 : st.regs 10 + st.mem (st.regs 3 + st.mem (st.regs 2 +
          st.mem (st.regs 1 + 4 * st.regs 15 + 2))) < 2 ^ w := by rw [qU, a10]; omega
      have d11 : st.regs 11 + st.mem (st.regs 3 + st.mem (st.regs 2 +
          st.mem (st.regs 1 + 4 * st.regs 15 + 2))) < 2 ^ w := by rw [qU, a11]; omega
      have d12 : st.regs 12 + st.mem (st.regs 3 + st.mem (st.regs 2 +
          st.mem (st.regs 1 + 4 * st.regs 15 + 2))) < 2 ^ w := by rw [qU, a12]; omega
      have d13 : st.regs 13 + st.mem (st.regs 3 + st.mem (st.regs 2 +
          st.mem (st.regs 1 + 4 * st.regs 15 + 2))) < 2 ^ w := by rw [qU, a13]; omega
      refine runs_start_le ?_
      dsimp only [hwFixB]
      wram_run
      all_goals first
        | wram_cost
        | omega
        | (refine ⟨⟨hRn _ (fun r hr => by simp (disch := omega) only [Function.update_of_ne]),
            by simp, ?_, fun a ha => ?_⟩, by simp [h15]⟩
           · refine HF.Done.step hdone h hi ?_ ?_ ?_ ?_ ?_ ?_ ?_
               (fun a n1 n2 n3 n4 n5 n6 n7 => ?_)
             all_goals simp (disch := omega) only [Function.update_of_ne, Function.update_self,
               a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, h15, eP, eF, eA, eB, eA1,
               eA2, eB1, eB2, eW, eE, HF.hl, HF.hk]
           · have hs := HF.Free.succ ha
             have ha' := hs.1
             have n1 := hs.2.1
             have n2 := hs.2.2.1
             have n3 := hs.2.2.2.1
             have n4 := hs.2.2.2.2.1
             have n5 := hs.2.2.2.2.2.1
             have n6 := hs.2.2.2.2.2.2.1
             have n7 := hs.2.2.2.2.2.2.2
             simp (disch := omega) only [Function.update_of_ne, a1, a2, a3, a7, a8, a9, a10, a11,
               a12, a13, h15, eA, eA1, eA2]
             exact hfr a ha'))
  refine ⟨hwFix, hproc, ?_⟩
  dsimp only [hwFix]
  refine runs_start_le ?_
  refine runs_seq_triple_le hloop ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl⟩, rfl⟩ (fun st hI => ?_)
  obtain ⟨-, -, hdone, hfr⟩ := hI
  refine runs_ret_le (by eval_expr) (fun F' he => ?_) ?_
  · obtain rfl := (HF.eq_of_args he).symm
    exact ⟨hdone, hfr⟩
  · simp only [hwFixC, HF.args, List.getD_cons_zero, List.getD_cons_succ, Expr.size]
    omega

end MinCostFlow.LowStretch
