module

public import MinCostFlow.HierPaths.InitBuild
public import MinCostFlow.HierPaths.InitCopy

/-!
# The writer of the owner section

Section 1 of the block of `Init` lists the owners of the `2^x` terminals, as section 1 of the
static output does (`initConcrete_section_owner`). In the static output at `h`, the offset
table has 7 words and section 0 is `[x, b]`, so `x` is at `h + 7` and the owners start at
`h + 10`. `ownerWriter fC` reads `x`, computes `2^x`, and copies the owners to `r6` with `copyUp`
(procedure `fC`). `ownerWriter_meetsContract` proves `SecContract` for it.
-/

@[expose] public section

noncomputable section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-- `r7 := mem (r4 + 7)` (that is `x`); `r8 := 1 <<< r7`; `r9 := copyUp(r6, r4 + 10, r8)`;
return `r9`. -/
def ownerWriter (fC : ℕ) : Stmt :=
  .seq (.assign 7 (.load (.bin .add (.reg 4) (.const 7))))
    (.seq (.assign 8 (.bin .shiftLeft (.const 1) (.reg 7)))
      (.seq (.call 9 fC [.reg 6, .bin .add (.reg 4) (.const 10), .reg 8]) (.ret (.reg 9))))

/-- The writer of the owner section as a `SecProc`. -/
def ownerSec (S : StaticData) (f : ℕ) : SecProc where
  f := f
  l _ := S.sections.getD 1 []
  cost _ := 17 * 2 ^ S.x + 60

theorem length_sections_one (S : StaticData) : (S.sections.getD 1 []).length = 2 ^ S.x := by
  simp [StaticData.sections, StaticData.numTerm]

/-- What the static output gives the writer: `x` at `h + 7`, the owners from `h + 10`, and at
least `9 + 2^x` words. -/
theorem staticOut_owner_facts {mem : ℕ → ℕ} {h : ℕ} {S : StaticData} (hS : StaticOut mem h S) :
    mem (h + 7) = S.x ∧ ListAt mem (h + 10) (S.sections.getD 1 []) ∧
      10 + 2 ^ S.x ≤ S.encode.length := by
  have h0 := listAt_csrList_get (k := 6) (f := fun i => S.sections.getD i []) hS (i := 0)
    (by omega)
  have h1 := listAt_csrList_get (k := 6) (f := fun i => S.sections.getD i []) hS (i := 1)
    (by omega)
  refine ⟨?_, ?_, ?_⟩
  · have := h0 0 (by simp [StaticData.sections])
    simpa [StaticData.sections] using this
  · have e : h + (6 + 1) + ((List.range 1).map fun j => (S.sections.getD j []).length).sum =
        h + 10 := by simp [StaticData.sections]
    rw [e] at h1
    exact h1
  · rw [StaticData.encode, length_layoutList]
    have hs : S.sections.length = 6 := by simp [StaticData.sections]
    rw [hs]
    have : (S.sections.map List.length).sum ≥ 3 + 2 ^ S.x := by
      simp [StaticData.sections, StaticData.numTerm]
    omega

/-- **The owner writer meets `SecContract`.** -/
theorem ownerWriter_meetsContract {w a : ℕ} {S : StaticData} {G : Graph} {p : Program}
    {f fC : ℕ} (hp : p.procs[f]? = some (ownerWriter fC))
    (hC : p.procs[fC]? = some copyUp) :
    MeetsContract w p f (SecContract w (buildInv w S a G) (ownerSec S f)) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨base, c, rfl, -, hI, hz, hc, hcw⟩ := hpre
  obtain ⟨gAddr, phiNum, phiDen, M, h, h₁, rfl, hSO, hlen, -, -, -, -, -, -⟩ := hI
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hc
  simp only [ownerSec, length_sections_one] at hcw
  obtain ⟨hx, hown, henc⟩ := staticOut_owner_facts hSO
  have hpos : 0 < 2 ^ S.x := Nat.two_pow_pos S.x
  have hw10 : 10 < 2 ^ w := by omega
  have hh10 : h + 10 < 2 ^ w := by omega
  have hsd : h + 10 + 2 ^ S.x ≤ c := by omega
  have hpx : 2 ^ S.x < 2 ^ w := by omega
  refine runs_start_le ?_
  unfold ownerWriter
  have h4 : (startState ([gAddr, phiNum, phiDen, M, h, h₁] ++ [c]) mem pos).regs 4 = h := rfl
  have h6 : (startState ([gAddr, phiNum, phiDen, M, h, h₁] ++ [c]) mem pos).regs 6 = c := rfl
  have hxw : S.x < w := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hpx
  have hxw' : S.x < 2 ^ w := hxw.trans (Nat.lt_two_pow_self)
  refine runs_seq_assign_le (v := S.x)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq h4)
      (Expr.eval_const (by omega)) (by omega)) hx) ?_
  refine runs_seq_assign_le (v := 2 ^ S.x)
    (by
      have e := Expr.eval_shiftLeft (w := w)
        (st := { startState ([gAddr, phiNum, phiDen, M, h, h₁] ++ [c]) mem pos with
          regs := Function.update (startState ([gAddr, phiNum, phiDen, M, h, h₁] ++ [c]) mem
            pos).regs 7 S.x })
        (a := .const 1) (b := .reg 7) (x := 1) (y := S.x) (Expr.eval_const (by omega))
        (Expr.eval_reg_of_eq (by simp)) (by rw [Nat.shiftLeft_eq, one_mul]; exact hpx)
      rw [Nat.shiftLeft_eq, one_mul] at e
      exact e) ?_
  refine runs_seq_call_le (copyUp_meetsContract (w := w) hC) (vs := [c, h + 10, 2 ^ S.x])
    (by simp [evalArgs, Expr.eval, Function.update, startState, hw10, hh10]) ?_
    ⟨c, h + 10, 2 ^ S.x, rfl, hsd, hcw, by omega⟩ ?_
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl <;> omega
  intro v mem₂ pos₂ hpost
  obtain ⟨_, _, _, hargs, hv, hcopy, hframe⟩ := hpost
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl⟩ := hargs
  refine runs_ret_le (v := v) (by simp [Expr.eval, Function.update]) ?_ ?_
  · refine ⟨[gAddr, phiNum, phiDen, M, h, h₁], c, rfl, ?_, ?_, ?_, ?_⟩
    · simp only [Outcome.value, ownerSec, length_sections_one]; exact hv
    · intro i hi
      simp only [ownerSec, length_sections_one] at hi
      show mem₂ (c + i) = _
      rw [hcopy i hi]
      exact hown i (by rw [length_sections_one]; exact hi)
    · intro y hy
      simp only [Outcome.value] at hy
      show mem₂ y = 0
      rw [hframe y (Or.inr (by omega))]
      exact hz y (by omega)
    · intro y hy
      exact hframe y (Or.inl hy)
  · simp only [SecContract, ownerSec, copyUpContract, List.getD_cons_succ, List.getD_cons_zero,
      argsSize, Expr.size]
    omega

/-! ### Sections of `2^x` zeros -/

/-- `r7 := mem (r4 + 7)` (that is `x`); `r8 := 1 <<< r7`; return `r6 + r8`. Memory from `r6` on
is zero, so this writes `2^x` zeros. -/
def zeroPowWriter : Stmt :=
  .seq (.assign 7 (.load (.bin .add (.reg 4) (.const 7))))
    (.seq (.assign 8 (.bin .shiftLeft (.const 1) (.reg 7))) (.ret (.bin .add (.reg 6) (.reg 8))))

/-- The writer of a section of `2^x` zeros as a `SecProc`. -/
def zeroPowSec (S : StaticData) (f : ℕ) : SecProc where
  f := f
  l _ := List.replicate (2 ^ S.x) 0
  cost _ := 30

/-- **The writer of `2^x` zeros meets `SecContract`.** -/
theorem zeroPowWriter_meetsContract {w a : ℕ} {S : StaticData} {G : Graph} {p : Program}
    {f : ℕ} (hp : p.procs[f]? = some zeroPowWriter) :
    MeetsContract w p f (SecContract w (buildInv w S a G) (zeroPowSec S f)) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨base, c, rfl, -, hI, hz, hc, hcw⟩ := hpre
  obtain ⟨gAddr, phiNum, phiDen, M, h, h₁, rfl, hSO, hlen, -, -, -, -, -, -⟩ := hI
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hc
  simp only [zeroPowSec, List.length_replicate] at hcw
  obtain ⟨hx, -, henc⟩ := staticOut_owner_facts hSO
  have hpos : 0 < 2 ^ S.x := Nat.two_pow_pos S.x
  have hpx : 2 ^ S.x < 2 ^ w := by omega
  have hxw : S.x < w := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hpx
  have hxw' : S.x < 2 ^ w := hxw.trans (Nat.lt_two_pow_self)
  refine runs_start_le ?_
  unfold zeroPowWriter
  have h4 : (startState ([gAddr, phiNum, phiDen, M, h, h₁] ++ [c]) mem pos).regs 4 = h := rfl
  refine runs_seq_assign_le (v := S.x)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq h4)
      (Expr.eval_const (by omega)) (by omega)) hx) ?_
  refine runs_seq_assign_le (v := 2 ^ S.x)
    (by
      have e := Expr.eval_shiftLeft (w := w)
        (st := { startState ([gAddr, phiNum, phiDen, M, h, h₁] ++ [c]) mem pos with
          regs := Function.update (startState ([gAddr, phiNum, phiDen, M, h, h₁] ++ [c]) mem
            pos).regs 7 S.x })
        (a := .const 1) (b := .reg 7) (x := 1) (y := S.x) (Expr.eval_const (by omega))
        (Expr.eval_reg_of_eq (by simp)) (by rw [Nat.shiftLeft_eq, one_mul]; exact hpx)
      rw [Nat.shiftLeft_eq, one_mul] at e
      exact e) ?_
  refine runs_ret_le (v := c + 2 ^ S.x)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [Function.update, startState]))
      (Expr.eval_reg_of_eq (by simp)) hcw) ?_ ?_
  · refine ⟨[gAddr, phiNum, phiDen, M, h, h₁], c, rfl, ?_, ?_, ?_, ?_⟩
    · simp [Outcome.value, zeroPowSec]
    · intro i hi
      simp only [zeroPowSec, List.length_replicate] at hi
      simp only [zeroPowSec, List.getElem_replicate]
      exact hz (c + i) (by omega)
    · intro y hy
      exact hz y (by simp [Outcome.value] at hy; omega)
    · intro y _
      rfl
  · simp only [SecContract, zeroPowSec, Expr.size]
    omega

/-- Sections 13 and 14 of the initial block (the failed and globally lost bits) are `2^x`
zeros. -/
theorem initConcrete_section_failed (S : StaticData) (a : ℕ) (s : PathDSAbsState) :
    (initConcrete S a s).sections.getD 13 [] = List.replicate (2 ^ S.x) 0 ∧
      (initConcrete S a s).sections.getD 14 [] = List.replicate (2 ^ S.x) 0 := by
  constructor <;>
  simp [HierConcrete.sections, initConcrete, DelState.init, LossState.init, bitsList,
    StaticData.model, staticArrays, connSystem, List.map_const']

/-! ### Sections of `n` or `m` zeros -/

/-- Return `r6 + mem (r0 + off)`: with the graph at `r0`, `off = 0` gives `n` and `off = 1`
gives `m`. Memory from `r6` on is zero, so this writes that many zeros. -/
def zeroGraphWriter (off : ℕ) : Stmt :=
  .ret (.bin .add (.reg 6) (.load (.bin .add (.reg 0) (.const off))))

/-- The writer of `L` zeros, `L = n` for `off = 0` and `L = m` for `off = 1`. -/
def zeroGraphSec (G : Graph) (off f : ℕ) : SecProc where
  f := f
  l _ := List.replicate ((Graph.encode G).getD off 0) 0
  cost _ := 30

/-- **The writer of `n` or `m` zeros meets `SecContract`.** -/
theorem zeroGraphWriter_meetsContract {w a : ℕ} {S : StaticData} {G : Graph} {p : Program}
    {f off : ℕ} (hoff : off < 2) (hp : p.procs[f]? = some (zeroGraphWriter off)) :
    MeetsContract w p f (SecContract w (buildInv w S a G) (zeroGraphSec G off f)) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨base, c, rfl, -, hI, hz, hc, hcw⟩ := hpre
  obtain ⟨gAddr, phiNum, phiDen, M, h, h₁, rfl, hSO, hlen, hG, hgh, -, -, -, -⟩ := hI
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hc
  simp only [zeroGraphSec, List.length_replicate] at hcw
  have hglen : 2 ≤ (Graph.encode G).length := by simp [Graph.encode]
  have hgo : off < (Graph.encode G).length := by omega
  have hread : mem (gAddr + off) = (Graph.encode G).getD off 0 := by
    rw [List.getD_eq_getElem _ _ hgo]
    exact hG off hgo
  have hw1 : gAddr + off < 2 ^ w := by omega
  refine runs_start_le ?_
  unfold zeroGraphWriter
  refine runs_ret_le (v := c + (Graph.encode G).getD off 0)
    (Expr.eval_add (Expr.eval_reg_of_eq rfl)
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq rfl)
        (Expr.eval_const (by omega)) hw1) hread) hcw) ?_ ?_
  · refine ⟨[gAddr, phiNum, phiDen, M, h, h₁], c, rfl, ?_, ?_, ?_, ?_⟩
    · simp [Outcome.value, zeroGraphSec]
    · intro i hi
      simp only [zeroGraphSec, List.length_replicate] at hi
      simp only [zeroGraphSec, List.getElem_replicate]
      exact hz (c + i) (by omega)
    · intro y hy
      exact hz y (by simp [Outcome.value] at hy; omega)
    · intro y _
      rfl
  · simp only [SecContract, zeroGraphSec, Expr.size]
    omega

/-- Sections 16, 17, 20 and 22 of the initial block are `m`, `n`, `n` and `n` zeros (the
deleted and pruned bits, the support cursors and a scratch area). -/
theorem initConcrete_sections_graph (S : StaticData) (a : ℕ) (phiNum phiDen M : ℕ) (G : Graph) :
    (initConcrete S a (initAbs phiNum phiDen M G)).sections.getD 16 [] =
        List.replicate ((Graph.encode G).getD 1 0) 0 ∧
      (initConcrete S a (initAbs phiNum phiDen M G)).sections.getD 17 [] =
        List.replicate ((Graph.encode G).getD 0 0) 0 ∧
      (initConcrete S a (initAbs phiNum phiDen M G)).sections.getD 20 [] =
        List.replicate ((Graph.encode G).getD 0 0) 0 ∧
      (initConcrete S a (initAbs phiNum phiDen M G)).sections.getD 22 [] =
        List.replicate ((Graph.encode G).getD 0 0) 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp [HierConcrete.sections, initConcrete, initAbs, DelState.init, bitsList, tabList,
    HierConcrete.n, HierConcrete.m, Graph.encode, List.map_const']

/-! ### The stack area -/

/-- `leafDepth x b = (x + b − 1) / b` without the sum `x + b`, which might not be a word:
`(x − 1) / b + [0 < x]`. -/
theorem leafDepth_eq_sub_div {x b : ℕ} (hb : 0 < b) :
    leafDepth x b = (x - 1) / b + (if 0 < x then 1 else 0) := by
  unfold leafDepth
  rcases x with _ | y
  · simp only [Nat.zero_add, Nat.zero_sub, Nat.zero_div, lt_irrefl, ite_false, Nat.add_zero]
    exact Nat.div_eq_of_lt (by omega)
  · simp only [Nat.add_sub_cancel, Nat.succ_pos, ite_true]
    rw [show y + 1 + b - 1 = y + b by omega, Nat.add_div_right y hb]

/-- `r7 := x`; `r8 := b`; `r9 := (r7 − 1) / r8 + [0 < r7]` (the leaf depth); return
`r6 + (r9 + 2) · 8`. Memory from `r6` on is zero, so this writes the zero stack area. -/
def stackWriter : Stmt :=
  .seq (.assign 7 (.load (.bin .add (.reg 4) (.const 7))))
    (.seq (.assign 8 (.load (.bin .add (.reg 4) (.const 8))))
      (.seq (.assign 9 (.bin .add (.bin .div (.bin .sub (.reg 7) (.const 1)) (.reg 8))
          (.bin .lt (.const 0) (.reg 7))))
        (.ret (.bin .add (.reg 6) (.bin .mul (.bin .add (.reg 9) (.const 2)) (.const 8))))))

/-- The writer of the stack area as a `SecProc`. -/
def stackSec (S : StaticData) (f : ℕ) : SecProc where
  f := f
  l _ := List.replicate ((leafDepth S.x S.b + 2) * 8) 0
  cost _ := 60

theorem staticOut_b {mem : ℕ → ℕ} {h : ℕ} {S : StaticData} (hS : StaticOut mem h S) :
    mem (h + 8) = S.b := by
  have h0 := listAt_csrList_get (k := 6) (f := fun i => S.sections.getD i []) hS (i := 0)
    (by omega)
  have := h0 1 (by simp [StaticData.sections])
  simpa [StaticData.sections] using this

/-- **The writer of the stack area meets `SecContract`.** -/
theorem stackWriter_meetsContract {w a : ℕ} {S : StaticData} {G : Graph} {p : Program}
    {f : ℕ} (hp : p.procs[f]? = some stackWriter) :
    MeetsContract w p f (SecContract w (buildInv w S a G) (stackSec S f)) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨base, c, rfl, -, hI, hz, hc, hcw⟩ := hpre
  obtain ⟨gAddr, phiNum, phiDen, M, h, h₁, rfl, hSO, hlen, -, -, -, -, hgood, -⟩ := hI
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hc
  simp only [stackSec, List.length_replicate] at hcw
  obtain ⟨hx, -, henc⟩ := staticOut_owner_facts hSO
  have hbm := staticOut_b hSO
  have hb := hgood.b_pos
  have hpos : 0 < 2 ^ S.x := Nat.two_pow_pos S.x
  have hpx : 2 ^ S.x < 2 ^ w := by omega
  have hxw : S.x < w := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hpx
  have hxw' : S.x < 2 ^ w := hxw.trans (Nat.lt_two_pow_self)
  have hD := leafDepth_eq_sub_div (x := S.x) hb
  set D := leafDepth S.x S.b with hDdef
  have hw8 : 8 < 2 ^ w := by omega
  have hh8 : h + 8 < 2 ^ w := by omega
  refine runs_start_le ?_
  unfold stackWriter
  refine runs_seq_assign_le (v := S.x)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := h) rfl)
      (Expr.eval_const (by omega)) (by omega)) hx) ?_
  refine runs_seq_assign_le (v := S.b)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := h)
      (by simp [Function.update]; rfl)) (Expr.eval_const (by omega)) (by omega)) hbm) ?_
  have hq : (S.x - 1) / S.b ≤ S.x - 1 := Nat.div_le_self _ _
  refine runs_seq_assign_le (v := D)
    (by
      rw [hD]
      refine Expr.eval_add (Expr.eval_div (Expr.eval_sub (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_const (by omega)) hxw') (Expr.eval_reg_of_eq (by simp)) (by omega))
        (Expr.eval_lt_op (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp))
          (by omega)) ?_
      split_ifs <;> omega) ?_
  refine runs_ret_le (v := c + (D + 2) * 8)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [Function.update]; rfl))
      (Expr.eval_mul (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_const (by omega)) (by omega)) (Expr.eval_const (by omega)) (by omega))
      hcw) ?_ ?_
  · refine ⟨[gAddr, phiNum, phiDen, M, h, h₁], c, rfl, ?_, ?_, ?_, ?_⟩
    · simp [Outcome.value, stackSec, hDdef]
    · intro i hi
      simp only [stackSec, List.length_replicate] at hi
      simp only [stackSec, List.getElem_replicate]
      exact hz (c + i) (by omega)
    · intro y hy
      exact hz y (by simp [Outcome.value] at hy; omega)
    · intro y _
      rfl
  · simp only [SecContract, stackSec, Expr.size]
    omega

/-- Section 23 of the initial block is the zero stack area of `(leafDepth + 2) · 8` words. -/
theorem initConcrete_section_stack (S : StaticData) (a : ℕ) (s : PathDSAbsState) :
    (initConcrete S a s).sections.getD 23 [] =
      List.replicate ((leafDepth S.x S.b + 2) * 8) 0 := by
  simp [HierConcrete.sections, HierConcrete.depth, stackWords, initConcrete, StaticData.model,
    staticArrays]

/-! ### The pair cursors -/

/-- As `stackWriter`, but return `r6 + ((r9 <<< r7) <<< r8)`, that is `r6` plus the number of
pairs `leafDepth · 2^x · 2^b`. -/
def pairCurWriter : Stmt :=
  .seq (.assign 7 (.load (.bin .add (.reg 4) (.const 7))))
    (.seq (.assign 8 (.load (.bin .add (.reg 4) (.const 8))))
      (.seq (.assign 9 (.bin .add (.bin .div (.bin .sub (.reg 7) (.const 1)) (.reg 8))
          (.bin .lt (.const 0) (.reg 7))))
        (.ret (.bin .add (.reg 6) (.bin .shiftLeft (.bin .shiftLeft (.reg 9) (.reg 7))
          (.reg 8))))))

/-- The writer of the pair cursors as a `SecProc`. -/
def pairCurSec (S : StaticData) (f : ℕ) : SecProc where
  f := f
  l _ := List.replicate (numPairsOf S.x S.b) 0
  cost _ := 60

/-- **The writer of the pair cursors meets `SecContract`.** -/
theorem pairCurWriter_meetsContract {w a : ℕ} {S : StaticData} {G : Graph} {p : Program}
    {f : ℕ} (hp : p.procs[f]? = some pairCurWriter) :
    MeetsContract w p f (SecContract w (buildInv w S a G) (pairCurSec S f)) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨base, c, rfl, -, hI, hz, hc, hcw⟩ := hpre
  obtain ⟨gAddr, phiNum, phiDen, M, h, h₁, rfl, hSO, hlen, -, -, -, -, hgood, -⟩ := hI
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hc
  simp only [pairCurSec, List.length_replicate] at hcw
  have hP0 : numPairsOf S.x S.b = leafDepth S.x S.b * 2 ^ S.x * 2 ^ S.b := rfl
  rw [hP0] at hcw
  obtain ⟨hx, -, henc⟩ := staticOut_owner_facts hSO
  have hbm := staticOut_b hSO
  have hb := hgood.b_pos
  have hpos : 0 < 2 ^ S.x := Nat.two_pow_pos S.x
  have hpx : 2 ^ S.x < 2 ^ w := by omega
  have hxw : S.x < w := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hpx
  have hxw' : S.x < 2 ^ w := hxw.trans (Nat.lt_two_pow_self)
  have hD := leafDepth_eq_sub_div (x := S.x) hb
  set D := leafDepth S.x S.b with hDdef
  have hw8 : 8 < 2 ^ w := by omega
  have hh8 : h + 8 < 2 ^ w := by omega
  refine runs_start_le ?_
  unfold pairCurWriter
  refine runs_seq_assign_le (v := S.x)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := h) rfl)
      (Expr.eval_const (by omega)) (by omega)) hx) ?_
  refine runs_seq_assign_le (v := S.b)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := h)
      (by simp [Function.update]; rfl)) (Expr.eval_const (by omega)) (by omega)) hbm) ?_
  have hq : (S.x - 1) / S.b ≤ S.x - 1 := Nat.div_le_self _ _
  refine runs_seq_assign_le (v := D)
    (by
      rw [hD]
      refine Expr.eval_add (Expr.eval_div (Expr.eval_sub (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_const (by omega)) hxw') (Expr.eval_reg_of_eq (by simp)) (by omega))
        (Expr.eval_lt_op (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp))
          (by omega)) ?_
      split_ifs <;> omega) ?_
  have hP : numPairsOf S.x S.b = D * 2 ^ S.x * 2 ^ S.b := rfl
  have hb1 : 1 ≤ 2 ^ S.b := Nat.one_le_two_pow
  have hDx : D * 2 ^ S.x ≤ D * 2 ^ S.x * 2 ^ S.b := Nat.le_mul_of_pos_right _ hb1
  have hc6 : c + D * 2 ^ S.x * 2 ^ S.b = c + (D <<< S.x) <<< S.b := by
    simp [Nat.shiftLeft_eq]
  refine runs_ret_le (v := c + D * 2 ^ S.x * 2 ^ S.b)
    (by
      rw [hc6]
      refine Expr.eval_add (Expr.eval_reg_of_eq ?_) (Expr.eval_shiftLeft
        (Expr.eval_shiftLeft (Expr.eval_reg_of_eq ?_) (Expr.eval_reg_of_eq ?_) ?_)
        (Expr.eval_reg_of_eq ?_) ?_) ?_
      all_goals first
        | (simp [Function.update]; done)
        | (simp [Function.update]; rfl)
        | (simp only [Nat.shiftLeft_eq]; omega)) ?_ ?_
  · refine ⟨[gAddr, phiNum, phiDen, M, h, h₁], c, rfl, ?_, ?_, ?_, ?_⟩
    · simp [Outcome.value, pairCurSec, hDdef, numPairsOf]
    · intro i hi
      simp only [pairCurSec, List.length_replicate] at hi
      simp only [pairCurSec, List.getElem_replicate]
      exact hz (c + i) (by omega)
    · intro y hy
      exact hz y (by simp [Outcome.value] at hy; omega)
    · intro y _
      rfl
  · simp only [SecContract, pairCurSec, Expr.size]
    omega

/-- Section 21 of the initial block is the zero pair cursors, `numPairs` words. -/
theorem initConcrete_section_pairCur (S : StaticData) (a : ℕ) (s : PathDSAbsState) :
    (initConcrete S a s).sections.getD 21 [] = List.replicate (numPairsOf S.x S.b) 0 := by
  simp [HierConcrete.sections, initConcrete, StaticData.model, staticArrays, DelState.init,
    tabList, List.map_const']

end MinCostFlow.HierPaths

end
