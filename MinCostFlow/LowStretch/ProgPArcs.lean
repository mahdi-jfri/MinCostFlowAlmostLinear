module

public import MinCostFlow.LowStretch.ProgClog
public import MinCostFlow.LowStretch.ProgArcs

/-!
# The items of the petal graph

The petal graph has two items for each active pair (one for each direction) and one highway slot
for each node. `pfill` writes the pair items. The item from `a` to `b` along a pair of length
`ℓ` has the shifted length `x = d(a) + ℓ - d(b)`, where `d` is the distance of the node from the
center (array `DV`). Its cost is the rounded cost `rc θ x`, and its class is `rcK lθ x`, found
by `rclsP` with a binary search (`pfill_spec`). The class fixes the cost (`cofK_rcK`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The addresses and numbers that `pfill` uses. -/
structure PF where
  nA : ℕ
  AS : ℕ
  IN : ℕ
  PW : ℕ
  LAB : ℕ
  LOC : ℕ
  DV : ℕ
  lθ : ℕ
  Jc : ℕ
  TL : ℕ
  HDt : ℕ
  CSt : ℕ
  CLt : ℕ
  NI : ℕ

namespace PF

variable (F : PF) (mem : ℕ → ℕ)

def args : List ℕ :=
  [F.nA, F.AS, F.IN, F.PW, F.LAB, F.LOC, F.DV, F.lθ, F.Jc, F.TL, F.HDt, F.CSt, F.CLt, F.NI]

theorem eq_of_args {F F' : PF} (h : F.args = F'.args) : F' = F := by
  cases F; cases F'; simp only [PF.args, List.cons.injEq] at h
  simp_all

/-- The pair of active entry `j`. -/
def pr (j : ℕ) : ℕ := mem (F.AS + 2 * j)
/-- The half flag of active entry `j`. -/
def fl (j : ℕ) : ℕ := mem (F.AS + 2 * j + 1)
/-- The node of the first end. -/
def ea (j : ℕ) : ℕ := mem (F.LOC + mem (F.LAB + mem (F.IN + 3 * F.pr mem j)))
/-- The node of the second end. -/
def eb (j : ℕ) : ℕ := mem (F.LOC + mem (F.LAB + mem (F.IN + 3 * F.pr mem j + 1)))
/-- The length. -/
def ln (j : ℕ) : ℕ := mem (F.PW + F.pr mem j) >>> F.fl mem j
/-- The shifted length from the first end to the second. -/
def x1 (j : ℕ) : ℕ := mem (F.DV + F.ea mem j) + F.ln mem j - mem (F.DV + F.eb mem j)
/-- The shifted length from the second end to the first. -/
def x2 (j : ℕ) : ℕ := mem (F.DV + F.eb mem j) + F.ln mem j - mem (F.DV + F.ea mem j)
/-- The class of the item from the first end. -/
def k1 (j : ℕ) : ℕ := rcK F.lθ (F.x1 mem j)
/-- The class of the item from the second end. -/
def k2 (j : ℕ) : ℕ := rcK F.lθ (F.x2 mem j)

/-- The memory after the first `i` entries. -/
def Done (M : ℕ → ℕ) (i : ℕ) : Prop :=
  ∀ j < i, M (F.TL + 2 * j) = F.ea mem j ∧ M (F.TL + 2 * j + 1) = F.eb mem j ∧
    M (F.HDt + 2 * j) = F.eb mem j ∧ M (F.HDt + 2 * j + 1) = F.ea mem j ∧
    M (F.CSt + 2 * j) = cofK F.lθ (F.k1 mem j) ∧ M (F.CSt + 2 * j + 1) = cofK F.lθ (F.k2 mem j) ∧
    M (F.CLt + 2 * j) = F.k1 mem j ∧ M (F.CLt + 2 * j + 1) = F.k2 mem j

/-- The written cells. -/
def Out (a : ℕ) : Prop :=
  (F.TL ≤ a ∧ a < F.TL + 2 * F.nA) ∨ (F.HDt ≤ a ∧ a < F.HDt + 2 * F.nA) ∨
    (F.CSt ≤ a ∧ a < F.CSt + 2 * F.nA) ∨ (F.CLt ≤ a ∧ a < F.CLt + 2 * F.nA)

/-- The precondition of `pfill`. -/
structure Pre (w : ℕ) (m n NL NS : ℕ) : Prop where
  pr_lt : ∀ j < F.nA, F.pr mem j < m
  fl_le : ∀ j < F.nA, F.fl mem j ≤ 1
  ends : ∀ p < m, mem (F.IN + 3 * p) < n ∧ mem (F.IN + 3 * p + 1) < n
  lab : ∀ j < F.nA, mem (F.LAB + mem (F.IN + 3 * F.pr mem j)) < NL ∧
    mem (F.LAB + mem (F.IN + 3 * F.pr mem j + 1)) < NL
  loc : ∀ j < F.nA, F.ea mem j < NS ∧ F.eb mem j < NS
  pw : ∀ p < m, mem (F.PW + p) < 2 ^ w
  dv : ∀ u < NS, mem (F.DV + u) < 2 ^ w
  x1_le : ∀ j < F.nA, 2 * F.x1 mem j ≤ 2 ^ (F.lθ + (F.Jc - 1))
  x2_le : ∀ j < F.nA, 2 * F.x2 mem j ≤ 2 ^ (F.lθ + (F.Jc - 1))
  Jc1 : 1 ≤ F.Jc
  hJ : 2 ^ (F.lθ + F.Jc) < 2 ^ w
  hJ2 : F.lθ + F.Jc + 2 < 2 ^ w
  sum_lt : ∀ j < F.nA, mem (F.DV + F.ea mem j) + F.ln mem j < 2 ^ w ∧
    mem (F.DV + F.eb mem j) + F.ln mem j < 2 ^ w
  l1 : F.TL + F.NI ≤ F.HDt
  l2 : F.HDt + F.NI ≤ F.CSt
  l3 : F.CSt + F.NI ≤ F.CLt
  l4 : F.CLt + F.NI < 2 ^ w
  hNI : 2 * F.nA ≤ F.NI
  rAS : F.AS + 2 * F.nA ≤ F.TL
  rIN : F.IN + 3 * m ≤ F.TL
  rPW : F.PW + m ≤ F.TL
  rLAB : F.LAB + n ≤ F.TL
  rLOC : F.LOC + NL ≤ F.TL
  rDV : F.DV + NS ≤ F.TL
  NSw : NS < 2 ^ w

end PF

/-- One entry of `pfill`: the eight stores, given by their addresses and values. -/
theorem PF.Done.step {F : PF} {mem M : ℕ → ℕ} {i : ℕ} (hd : F.Done mem M i)
    (l1 : F.TL + F.NI ≤ F.HDt) (l2 : F.HDt + F.NI ≤ F.CSt) (l3 : F.CSt + F.NI ≤ F.CLt)
    (hNI : 2 * F.nA ≤ F.NI) (hi : i < F.nA)
    {A1 A2 A3 A4 A5 A6 A7 A8 V1 V2 V3 V4 V5 V6 V7 V8 : ℕ}
    (e1 : A1 = F.TL + 2 * i) (f1 : V1 = F.ea mem i)
    (e2 : A2 = F.TL + 2 * i + 1) (f2 : V2 = F.eb mem i)
    (e3 : A3 = F.HDt + 2 * i) (f3 : V3 = F.eb mem i)
    (e4 : A4 = F.HDt + 2 * i + 1) (f4 : V4 = F.ea mem i)
    (e5 : A5 = F.CSt + 2 * i) (f5 : V5 = cofK F.lθ (F.k1 mem i))
    (e6 : A6 = F.CSt + 2 * i + 1) (f6 : V6 = cofK F.lθ (F.k2 mem i))
    (e7 : A7 = F.CLt + 2 * i) (f7 : V7 = F.k1 mem i)
    (e8 : A8 = F.CLt + 2 * i + 1) (f8 : V8 = F.k2 mem i) :
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
  · unfold PF.Out at ha
    simp (disch := omega) only [Function.update_of_ne]

/-- The body of `pfill`, for entry `i` in register `14`. Procedure `bR` is `rclsP`. -/
def pfillB (bR : ℕ) : Stmt :=
  .seq (.assign 15 (.load (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 14)))))
  (.seq (.assign 16 (.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 14)))
    (.const 1))))
  (.seq (.assign 17 (.load (.bin .add (.reg 5) (.load (.bin .add (.reg 4)
    (.load (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg 15)))))))))
  (.seq (.assign 18 (.load (.bin .add (.reg 5) (.load (.bin .add (.reg 4)
    (.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg 15))) (.const 1))))))))
  (.seq (.assign 19 (.bin .shiftRight (.load (.bin .add (.reg 3) (.reg 15))) (.reg 16)))
  (.seq (.assign 20 (.bin .sub (.bin .add (.load (.bin .add (.reg 6) (.reg 17))) (.reg 19))
    (.load (.bin .add (.reg 6) (.reg 18)))))
  (.seq (.assign 21 (.bin .sub (.bin .add (.load (.bin .add (.reg 6) (.reg 18))) (.reg 19))
    (.load (.bin .add (.reg 6) (.reg 17)))))
  (.seq (.call 22 bR [.reg 7, .reg 20, .reg 8])
  (.seq (.call 23 bR [.reg 7, .reg 21, .reg 8])
  (.seq (.cond (.bin .eq (.reg 22) (.const 0)) (.assign 24 (.const 0))
    (.assign 24 (.bin .shiftLeft (.const 1) (.bin .sub (.bin .add (.reg 7) (.reg 22)) (.const 2)))))
  (.seq (.cond (.bin .eq (.reg 23) (.const 0)) (.assign 25 (.const 0))
    (.assign 25 (.bin .shiftLeft (.const 1) (.bin .sub (.bin .add (.reg 7) (.reg 23)) (.const 2)))))
  (.seq (.store (.bin .add (.reg 9) (.bin .mul (.const 2) (.reg 14))) (.reg 17))
  (.seq (.store (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 2) (.reg 14))) (.const 1))
    (.reg 18))
  (.seq (.store (.bin .add (.reg 10) (.bin .mul (.const 2) (.reg 14))) (.reg 18))
  (.seq (.store (.bin .add (.bin .add (.reg 10) (.bin .mul (.const 2) (.reg 14))) (.const 1))
    (.reg 17))
  (.seq (.store (.bin .add (.reg 11) (.bin .mul (.const 2) (.reg 14))) (.reg 24))
  (.seq (.store (.bin .add (.bin .add (.reg 11) (.bin .mul (.const 2) (.reg 14))) (.const 1))
    (.reg 25))
  (.seq (.store (.bin .add (.reg 12) (.bin .mul (.const 2) (.reg 14))) (.reg 22))
    (.store (.bin .add (.bin .add (.reg 12) (.bin .mul (.const 2) (.reg 14))) (.const 1))
      (.reg 23)))))))))))))))))))

/-- `pfill bR` with `args = F.args`. -/
def pfill (bR : ℕ) : Stmt := .seq (forRange 14 (.const 0) (.reg 0) (pfillB bR)) (.ret (.const 0))

theorem pfill_noRand (bR : ℕ) : (pfill bR).NoRand := by
  simp [pfill, pfillB, forRange, forUp, Stmt.NoRand]

/-- The contract of `pfill`. -/
def pfillC (w : ℕ) : Contract where
  pre args mem := ∃ F : PF, ∃ m n NL NS, args = F.args ∧ F.Pre mem w m n NL NS
  post args mem _ mem' := ∀ F : PF, args = F.args →
    F.Done mem mem' F.nA ∧ ∀ a, ¬ F.Out a → mem' a = mem a
  cost args _ := args.getD 0 0 * (80 * Nat.clog 2 (args.getD 8 0) + 500) + 20

/-- The cost of a class is `cofK`, as the shift computes it. -/
theorem shl_cofK {lθ k : ℕ} (hk : k ≠ 0) : 1 <<< (lθ + k - 2) = cofK lθ k := by
  simp [cofK, hk, Nat.shiftLeft_eq]

set_option maxHeartbeats 8000000 in
theorem pfill_spec {w : ℕ} {p : Program} {b bR : ℕ} (hp : p.HasAt b [pfill bR])
    (hR : MeetsContract w p bR (rclsC w)) : MeetsContract w p b (pfillC w) := by
  intro args mem pos ω hwords hpre
  obtain ⟨F, m, n, NL, NS, rfl, h⟩ := hpre
  have hproc : p.procs[b]? = some (pfill bR) := hp 0 (by simp)
  clear hp
  have l1 := h.l1; have l2 := h.l2; have l3 := h.l3; have l4 := h.l4; have hNI := h.hNI
  have rAS := h.rAS; have rIN := h.rIN; have rPW := h.rPW; have rLAB := h.rLAB
  have rLOC := h.rLOC; have rDV := h.rDV; have hJ := h.hJ; have hJ2 := h.hJ2
  have hJc1 := h.Jc1
  have hw1 : 1 < 2 ^ w := by omega
  let R : State → Prop := fun st => st.regs 0 = F.nA ∧ st.regs 1 = F.AS ∧ st.regs 2 = F.IN ∧
    st.regs 3 = F.PW ∧ st.regs 4 = F.LAB ∧ st.regs 5 = F.LOC ∧ st.regs 6 = F.DV ∧
    st.regs 7 = F.lθ ∧ st.regs 8 = F.Jc ∧ st.regs 9 = F.TL ∧ st.regs 10 = F.HDt ∧
    st.regs 11 = F.CSt ∧ st.regs 12 = F.CLt ∧ st.regs 13 = F.NI
  have hRu : ∀ st r v, R st → 14 ≤ r → R { st with regs := Function.update st.regs r v } := by
    intro st r v ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ hr
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Function.update_apply] <;> (rw [if_neg (by omega)]; assumption)
  let I : ℕ → State → Prop := fun i st => R st ∧ st.regs 14 = i ∧ F.Done mem st.mem i ∧
    ∀ a, ¬ F.Out a → st.mem a = mem a
  have hloop := Triple.forRange_const (p := p) (r := 14) (lo := .const 0) (hi := .reg 0)
    (body := pfillB bR) (P := fun st => R st ∧ st.mem = mem) (Inv := I)
    (80 * Nat.clog 2 F.Jc + 480) 0 F.nA (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st ⟨hr, hm⟩ => ⟨by eval_expr, hRu st 14 0 hr (by omega), by simp,
      fun j hj => absurd hj (by omega), fun a _ => by simp [hm]⟩)
    (fun _ st _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by have := hI.1.1; eval_expr)
    (fun i _ hi st ω hI => by
      obtain ⟨hr, h14, hdone, hfr⟩ := hI
      have hr' := hr
      obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := hr
      have hpm := h.pr_lt i hi
      have hfl := h.fl_le i hi
      obtain ⟨hun, hvn⟩ := h.ends _ hpm
      have hlu := (h.lab i hi).1
      have hlv := (h.lab i hi).2
      obtain ⟨hs1, hs2⟩ := h.sum_lt i hi
      have hx1 := h.x1_le i hi
      have hx2 := h.x2_le i hi
      have nOut : ∀ a, a < F.TL → ¬ F.Out a := by
        intro a ha ho; unfold PF.Out at ho; omega
      have eP : st.mem (F.AS + 2 * i) = F.pr mem i := hfr _ (nOut _ (by omega))
      have eF : st.mem (F.AS + 2 * i + 1) = F.fl mem i := hfr _ (nOut _ (by omega))
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
      have hea : F.ea mem i < NS := (h.loc i hi).1
      have heb : F.eb mem i < NS := (h.loc i hi).2
      have eW : st.mem (F.PW + F.pr mem i) = mem (F.PW + F.pr mem i) := hfr _ (nOut _ (by omega))
      have eDA : st.mem (F.DV + F.ea mem i) = mem (F.DV + F.ea mem i) := hfr _ (nOut _ (by omega))
      have eDB : st.mem (F.DV + F.eb mem i) = mem (F.DV + F.eb mem i) := hfr _ (nOut _ (by omega))
      have bW : mem (F.PW + F.pr mem i) < 2 ^ w := h.pw _ hpm
      have hln : F.ln mem i = mem (F.PW + F.pr mem i) >>> F.fl mem i := rfl
      have hlnw : F.ln mem i < 2 ^ w := lt_of_le_of_lt (shr_le _ _) bW
      have b1 : st.regs 4 + st.mem (st.regs 2 + 3 * st.mem (F.AS + 2 * i)) < 2 ^ w := by
        rw [a4, a2, eP, eU]; omega
      have b2 : st.regs 4 + st.mem (st.regs 2 + 3 * st.mem (F.AS + 2 * i) + 1) < 2 ^ w := by
        rw [a4, a2, eP, eV]; omega
      have eA' : st.mem (st.regs 5 + st.mem (st.regs 4 + st.mem (st.regs 2 + 3 *
          st.mem (F.AS + 2 * i)))) = F.ea mem i := by rw [a5, a4, a2, eP, eU, eLU, eA]
      have eB' : st.mem (st.regs 5 + st.mem (st.regs 4 + st.mem (st.regs 2 + 3 *
          st.mem (F.AS + 2 * i) + 1))) = F.eb mem i := by rw [a5, a4, a2, eP, eV, eLV, eB]
      have b3 : st.regs 5 + st.mem (st.regs 4 + st.mem (st.regs 2 + 3 * st.mem (F.AS + 2 * i))) <
          2 ^ w := by rw [a5, a4, a2, eP, eU, eLU]; omega
      have b4 : st.regs 5 + st.mem (st.regs 4 + st.mem (st.regs 2 + 3 *
          st.mem (F.AS + 2 * i) + 1)) < 2 ^ w := by rw [a5, a4, a2, eP, eV, eLV]; omega
      have b5 : st.mem (st.regs 3 + st.mem (F.AS + 2 * i)) < 2 ^ w := by rw [a3, eP, eW]; exact bW
      have eL' : st.mem (st.regs 3 + st.mem (F.AS + 2 * i)) >>>
          st.mem (st.regs 1 + 2 * st.regs 14 + 1) = F.ln mem i := by
        rw [a3, eP, eW, a1, h14, eF]; rfl
      have b6 : st.regs 6 + st.mem (st.regs 5 + st.mem (st.regs 4 + st.mem (st.regs 2 + 3 *
          st.mem (F.AS + 2 * i)))) < 2 ^ w := by rw [eA', a6]; omega
      have b7 : st.regs 6 + st.mem (st.regs 5 + st.mem (st.regs 4 + st.mem (st.regs 2 + 3 *
          st.mem (F.AS + 2 * i) + 1))) < 2 ^ w := by rw [eB', a6]; omega
      have eDA' : st.mem (st.regs 6 + st.mem (st.regs 5 + st.mem (st.regs 4 + st.mem (st.regs 2 +
          3 * st.mem (F.AS + 2 * i))))) = mem (F.DV + F.ea mem i) := by rw [eA', a6, eDA]
      have eDB' : st.mem (st.regs 6 + st.mem (st.regs 5 + st.mem (st.regs 4 + st.mem (st.regs 2 +
          3 * st.mem (F.AS + 2 * i) + 1)))) = mem (F.DV + F.eb mem i) := by rw [eB', a6, eDB]
      have b8 : st.mem (st.regs 6 + st.mem (st.regs 5 + st.mem (st.regs 4 + st.mem (st.regs 2 +
          3 * st.mem (F.AS + 2 * i))))) + st.mem (st.regs 3 + st.mem (F.AS + 2 * i)) >>>
          st.mem (st.regs 1 + 2 * st.regs 14 + 1) < 2 ^ w := by rw [eDA', eL']; exact hs1
      have b9 : st.mem (st.regs 6 + st.mem (st.regs 5 + st.mem (st.regs 4 + st.mem (st.regs 2 +
          3 * st.mem (F.AS + 2 * i) + 1)))) + st.mem (st.regs 3 + st.mem (F.AS + 2 * i)) >>>
          st.mem (st.regs 1 + 2 * st.regs 14 + 1) < 2 ^ w := by rw [eDB', eL']; exact hs2
      have hRn : ∀ st' : State, (∀ r < 14, st'.regs r = st.regs r) → R st' := fun st' hs =>
        ⟨(hs 0 (by omega)).trans a0, (hs 1 (by omega)).trans a1, (hs 2 (by omega)).trans a2,
          (hs 3 (by omega)).trans a3, (hs 4 (by omega)).trans a4, (hs 5 (by omega)).trans a5,
          (hs 6 (by omega)).trans a6, (hs 7 (by omega)).trans a7, (hs 8 (by omega)).trans a8,
          (hs 9 (by omega)).trans a9, (hs 10 (by omega)).trans a10, (hs 11 (by omega)).trans a11,
          (hs 12 (by omega)).trans a12, (hs 13 (by omega)).trans a13⟩
      have key := PF.Done.step hdone l1 l2 l3 hNI hi (M := st.mem) (A1 := _) (A2 := _) (A3 := _)
        (A4 := _) (A5 := _) (A6 := _) (A7 := _) (A8 := _) (V1 := _) (V2 := _) (V3 := _)
        (V4 := _) (V5 := _) (V6 := _) (V7 := _) (V8 := _) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        rfl rfl rfl rfl rfl rfl
      refine runs_start_le ?_
      dsimp only [pfillB]
      have hx1e : st.mem (st.regs 6 + st.mem (st.regs 5 + st.mem (st.regs 4 + st.mem (st.regs 2 +
          3 * st.mem (F.AS + 2 * i))))) + st.mem (st.regs 3 + st.mem (F.AS + 2 * i)) >>>
          st.mem (st.regs 1 + 2 * st.regs 14 + 1) - st.mem (st.regs 6 + st.mem (st.regs 5 +
          st.mem (st.regs 4 + st.mem (st.regs 2 + 3 * st.mem (F.AS + 2 * i) + 1)))) =
          F.x1 mem i := by rw [eDA', eDB', eL']; rfl
      have hx2e : st.mem (st.regs 6 + st.mem (st.regs 5 + st.mem (st.regs 4 + st.mem (st.regs 2 +
          3 * st.mem (F.AS + 2 * i) + 1)))) + st.mem (st.regs 3 + st.mem (F.AS + 2 * i)) >>>
          st.mem (st.regs 1 + 2 * st.regs 14 + 1) - st.mem (st.regs 6 + st.mem (st.regs 5 +
          st.mem (st.regs 4 + st.mem (st.regs 2 + 3 * st.mem (F.AS + 2 * i))))) =
          F.x2 mem i := by rw [eDA', eDB', eL']; rfl
      have hJx : 2 ^ (F.lθ + (F.Jc - 1)) < 2 ^ w :=
        lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by omega)) hJ
      wram_run
      · exact ⟨F.lθ, F.x1 mem i, F.Jc, by first | rfl | rw [hx1e], by omega, by omega, hJc1, hx1⟩
      intro v1 mem1 pos1 hpost1
      obtain ⟨hm1, hv1⟩ := hpost1
      obtain ⟨hk1, hk1lt⟩ := hv1 F.lθ (F.x1 mem i) F.Jc (by first | rfl | rw [hx1e])
      subst hm1
      have s1 : 1 <<< (st.regs 7 + v1 - 2) < 2 ^ w := by
        rw [Nat.one_shiftLeft]
        exact lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by rw [a7]; omega)) hJ
      wram_run
      · exact ⟨F.lθ, F.x2 mem i, F.Jc, by first | rfl | rw [hx2e], by omega, by omega, hJc1, hx2⟩
      intro v2 mem2 pos2 hpost2
      obtain ⟨hm2, hv2⟩ := hpost2
      obtain ⟨hk2, hk2lt⟩ := hv2 F.lθ (F.x2 mem i) F.Jc (by first | rfl | rw [hx2e])
      subst hm2
      have s2 : 1 <<< (st.regs 7 + v2 - 2) < 2 ^ w := by
        rw [Nat.one_shiftLeft]
        exact lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by rw [a7]; omega)) hJ
      have c1 : F.k1 mem i = v1 := hk1.symm
      have c2 : F.k2 mem i = v2 := hk2.symm
      wram_run
      all_goals first
        | (simp only [rclsC, List.getD_cons_succ, List.getD_cons_zero]; wram_cost)
        | (by_cases e1 : v1 = 0 <;> by_cases e2 : v2 = 0 <;> (try omega) <;>
          (refine ⟨⟨hRn _ (fun r hr => by simp (disch := omega) only [Function.update_of_ne]),
            by simp, ?_, fun a ha => ?_⟩, by simp [h14]⟩
           · convert key.1 using 2 <;> simp [c1, c2, cofK, e1, e2, Nat.one_shiftLeft, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, h14, eP, eF, eU, eV, eLU, eLV, eA, eB, eW]
           · refine Eq.trans ?_ ((key.2 a ha).trans (hfr a ha))
             congr 1 <;> simp [c1, c2, cofK, e1, e2, Nat.one_shiftLeft, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, h14, eP, eF, eU, eV, eLU, eLV, eA, eB, eW])))
  refine ⟨pfill bR, hproc, ?_⟩
  dsimp only [pfill]
  refine runs_start_le ?_
  refine runs_seq_triple_le hloop ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl⟩, rfl⟩ (fun st hI => ?_)
  obtain ⟨-, -, hdone, hfr⟩ := hI
  refine runs_ret_le (by eval_expr) (fun F' he => ?_) ?_
  · obtain rfl := PF.eq_of_args he
    exact ⟨hdone, hfr⟩
  · simp only [pfillC, PF.args, List.getD_cons_zero, List.getD_cons_succ, Expr.size]
    rw [Nat.sub_zero]
    have := Nat.mul_le_mul_left F.nA
      (show 80 * Nat.clog 2 F.Jc + 480 + 1 + 8 ≤ 80 * Nat.clog 2 F.Jc + 500 by omega)
    omega

end MinCostFlow.LowStretch
