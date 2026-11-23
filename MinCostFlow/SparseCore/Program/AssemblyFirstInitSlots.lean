module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitSlotMath
public import MinCostFlow.DynSpanner.Program.SortOps
public import WordRAM.Logic
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# The slots of the active pairs at the init: the program (`AssemblyFirstInitSlots`)

The bundle side of a branch keeps the slots of the active pairs and, for each component, an active
flag and the list of its pairs (`AsmSdMapsAt`, `SlotMapOK`). P5's init of the slots also needs,
for each slot, its number of edges, and for each edge, its slot. This file writes the procedure
`slotListBody` that computes all of these at the init, following the arithmetic of
`AssemblyFirstInitSlotMath.lean`, and proves its first three loops.

The procedure takes `[graph, expPtr, cmpH, bktH, nComp, k, B, ctH, heap]`: the graph `G` in memory
form, P4's export, the array from vertices to components and the bucket array (both written
before), the number of components, the bundle cap `k`, a bound `B` above the bucket words, and the
table of the components (three words per component, fresh). It works in six loops.
1. Count the edges of each component: the edge `e` adds one to the word `ctH + 3 c` of the
   component `c` of its tail (`slotCount_loop`).
2. Turn each count `x` into the active flag `[0 < x] - [4 x < k]`, which is `1` exactly when
   `1 ≤ x` and `k ≤ 4 x` (`slotFlag_loop`).
3. Mark the edges of the forest of P4's export (`slotMark_loop`).
4. For each edge `e` outside the forest whose component `c` is active, append the key
   `c · B + bucket word` to the keys, and the pair `(e, key)` to the assignments.
5. Sort the keys and remove repeats: this is the list `D`. For each entry `j` of `D`, write the
   pair `(D[j] mod B, j)`, the slot `j` and the spec `(j, 0)`, and set the address of the list of
   the component `D[j] / B` and its length.
6. Replace the key of each assignment by its index in `D` (binary search), and add `4` to the spec
   of that slot.

From `heap` the procedure keeps two header words (the number of slots and of assignments), then
the marks (`eCap` words), the keys, the scratch of the sort, the list `D` (`m` words each), the
pairs (`2 m`), the slot list (`m + 1`), the specs (`2 m`) and the assignments (`2 m`). It returns
the end of these.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.DynSpanner.Program

/-! ## The procedure -/

/-- The setup, then `s`: registers `9 = vCap`, `10 = eCap`, `11 = m`, the bases of the edge list
(`12`), the tail slots (`13`) and the names of the slots (`14`) of `G`, the number (`15`) and the
start (`16`) of the edge triples of the forest of P4's export, and the bases of the arrays of the
procedure from `heap + 2` (`17` to `24`). -/
def slotListSetupThen (s : Stmt) : Stmt :=
  .assign 9 (.load (.reg 0)) ;;
  .assign 10 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 11 (.load (.bin .add (.reg 0) (.const 3))) ;;
  .assign 12 (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 7) (.reg 9)))
    (.reg 10)) ;;
  .assign 13 (.bin .add (.reg 12) (.bin .mul (.const 2) (.reg 10))) ;;
  .assign 14 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 4) (.reg 9))) ;;
  .assign 15 (.load (.bin .add (.load (.bin .add (.reg 1) (.const 1))) (.const 2))) ;;
  .assign 16 (.load (.bin .add (.load (.bin .add (.reg 1) (.const 1))) (.const 3))) ;;
  .assign 17 (.bin .add (.reg 8) (.const 2)) ;;
  .assign 18 (.bin .add (.reg 17) (.reg 10)) ;;
  .assign 19 (.bin .add (.reg 18) (.reg 11)) ;;
  .assign 20 (.bin .add (.reg 19) (.reg 11)) ;;
  .assign 21 (.bin .add (.reg 20) (.reg 11)) ;;
  .assign 22 (.bin .add (.reg 21) (.bin .mul (.const 2) (.reg 11))) ;;
  .assign 23 (.bin .add (.bin .add (.reg 22) (.reg 11)) (.const 1)) ;;
  .assign 24 (.bin .add (.reg 23) (.bin .mul (.const 2) (.reg 11))) ;;
  s

/-- Loop 1, round `i` (register `25`): the edge `e = eL[i]` (`26`), the address `ctH + 3 c` of the
count of the component `c` of its tail (`27`), and one more on that count. -/
def slotCountStep : Stmt :=
  .assign 26 (.load (.bin .add (.reg 12) (.reg 25))) ;;
  .assign 27 (.load (.bin .add (.reg 14) (.load (.bin .add (.reg 13) (.reg 26))))) ;;
  .assign 27 (.bin .add (.reg 7) (.bin .mul (.const 3) (.load (.bin .add (.reg 2) (.reg 27))))) ;;
  .store (.reg 27) (.bin .add (.load (.reg 27)) (.const 1))

/-- Loop 2, round `c`: the count `x` at `ctH + 3 c` becomes `[0 < x] - [4 x < k]`. -/
def slotFlagStep : Stmt :=
  .assign 26 (.bin .add (.reg 7) (.bin .mul (.const 3) (.reg 25))) ;;
  .assign 27 (.load (.reg 26)) ;;
  .store (.reg 26) (.bin .sub (.bin .lt (.const 0) (.reg 27))
    (.bin .lt (.bin .mul (.const 4) (.reg 27)) (.reg 5)))

/-- Loop 3, round `t`: mark the edge of the `t`-th triple of the forest. -/
def slotMarkStep : Stmt :=
  .store (.bin .add (.reg 17) (.load (.bin .add (.reg 16) (.bin .mul (.const 3) (.reg 25)))))
    (.const 1)

/-- Loop 4, round `i`: the edge `e = eL[i]` (`26`) and the component `c` of its tail (`27`). If
`e` is not marked and `c` is active, the key `c · B + bkt[e]` (`28`) goes to the keys at position
`nK` (register `29`), the pair `(e, key)` to the assignments, and `nK` goes up by one. -/
def slotKeyStep : Stmt :=
  .assign 26 (.load (.bin .add (.reg 12) (.reg 25))) ;;
  .assign 27 (.load (.bin .add (.reg 2)
    (.load (.bin .add (.reg 14) (.load (.bin .add (.reg 13) (.reg 26))))))) ;;
  .cond (.bin .mul (.bin .eq (.load (.bin .add (.reg 17) (.reg 26))) (.const 0))
      (.load (.bin .add (.reg 7) (.bin .mul (.const 3) (.reg 27)))))
    (.assign 28 (.bin .add (.bin .mul (.reg 27) (.reg 6)) (.load (.bin .add (.reg 3) (.reg 26)))) ;;
     .store (.bin .add (.reg 18) (.reg 29)) (.reg 28) ;;
     .store (.bin .add (.reg 24) (.bin .mul (.const 2) (.reg 29))) (.reg 26) ;;
     .store (.bin .add (.bin .add (.reg 24) (.const 1)) (.bin .mul (.const 2) (.reg 29))) (.reg 28) ;;
     .assign 29 (.bin .add (.reg 29) (.const 1)))
    .nop

/-- Loop 5, round `j`: the entry `x = D[j]` (`26`) and the address `ctH + 3 (x / B)` of its
component (`27`). Write the pair `(x mod B, j)`, the slot `j` and the spec word `j`; then the
address of the list of the component becomes `pairs + 2 (j - len)` and its length `len` goes up by
one. -/
def slotWalkStep : Stmt :=
  .assign 26 (.load (.bin .add (.reg 20) (.reg 25))) ;;
  .assign 27 (.bin .add (.reg 7) (.bin .mul (.const 3) (.bin .div (.reg 26) (.reg 6)))) ;;
  .store (.bin .add (.reg 21) (.bin .mul (.const 2) (.reg 25))) (.bin .mod (.reg 26) (.reg 6)) ;;
  .store (.bin .add (.bin .add (.reg 21) (.const 1)) (.bin .mul (.const 2) (.reg 25))) (.reg 25) ;;
  .store (.bin .add (.reg 22) (.reg 25)) (.reg 25) ;;
  .store (.bin .add (.reg 23) (.bin .mul (.const 2) (.reg 25))) (.reg 25) ;;
  .store (.bin .add (.reg 27) (.const 1)) (.bin .add (.reg 21) (.bin .mul (.const 2)
    (.bin .sub (.reg 25) (.load (.bin .add (.reg 27) (.const 2)))))) ;;
  .store (.bin .add (.reg 27) (.const 2)) (.bin .add (.load (.bin .add (.reg 27) (.const 2)))
    (.const 1))

/-- Loop 6, round `t`: the slot `s` of the key of assignment `t` (binary search in `D`, register
`26`) replaces the key, and the spec word of `s` goes up by `4`. -/
def slotAssignStep (bSort : ℕ) : Stmt :=
  .call 26 (bSort + sortIdxBinSearch) [.reg 20, .reg 30,
    .load (.bin .add (.bin .add (.reg 24) (.const 1)) (.bin .mul (.const 2) (.reg 25)))] ;;
  .store (.bin .add (.bin .add (.reg 24) (.const 1)) (.bin .mul (.const 2) (.reg 25))) (.reg 26) ;;
  .store (.bin .add (.bin .add (.reg 23) (.const 1)) (.bin .mul (.const 2) (.reg 26)))
    (.bin .add (.load (.bin .add (.bin .add (.reg 23) (.const 1)) (.bin .mul (.const 2) (.reg 26))))
      (.const 4))

/-- The part of the procedure after loop 3: loop 4, the sort and the removal of repeats, the two
header words, loops 5 and 6, and the return of the end of the arrays. -/
def slotListTail (bSort : ℕ) : Stmt :=
  .assign 29 (.const 0) ;;
  forRange 25 (.const 0) (.reg 11) slotKeyStep ;;
  .call 30 (bSort + sortIdxMergeSort) [.reg 18, .reg 29, .reg 19] ;;
  .call 30 (bSort + sortIdxDedup) [.reg 18, .reg 29, .reg 20] ;;
  .store (.reg 8) (.reg 30) ;;
  .store (.bin .add (.reg 8) (.const 1)) (.reg 29) ;;
  forRange 25 (.const 0) (.reg 30) slotWalkStep ;;
  forRange 25 (.const 0) (.reg 29) (slotAssignStep bSort) ;;
  .ret (.bin .add (.reg 24) (.bin .mul (.const 2) (.reg 11)))

/-- **The slots of the active pairs at the init**, `[graph, expPtr, cmpH, bktH, nComp, k, B, ctH,
heap]` (see the module docstring). -/
def slotListBody (bSort : ℕ) : Stmt :=
  slotListSetupThen
    (forRange 25 (.const 0) (.reg 11) slotCountStep ;;
     forRange 25 (.const 0) (.reg 4) slotFlagStep ;;
     forRange 25 (.const 0) (.reg 15) slotMarkStep ;;
     slotListTail bSort)

/-- The module: the procedure, then the sort procedures. -/
def slotListModule (b : ℕ) : List Stmt := slotListBody (b + 1) :: sortProcs (b + 1)

theorem slotListBody_noRand (bSort : ℕ) : (slotListBody bSort).NoRand := by
  simp [slotListBody, slotListSetupThen, slotListTail, slotCountStep, slotFlagStep, slotMarkStep,
    slotKeyStep, slotWalkStep, slotAssignStep, forRange, forUp, Stmt.NoRand]

theorem slotListModule_noRand (b : ℕ) : ∀ s ∈ slotListModule b, s.NoRand := by
  intro s hs
  simp only [slotListModule, List.mem_cons] at hs
  rcases hs with rfl | hs
  · exact slotListBody_noRand _
  · exact sortProcs_noRand _ s hs

/-- The words of the procedure from `heap`: two header words, `eCap` marks and `10 m + 1` words of
arrays. -/
def slotListSpace (eCap m : ℕ) : ℕ := eCap + 10 * m + 3

/-! ## Loop 1: the number of edges of each component -/

/-- The cells `ctH + 3 c` of the counts or flags of the components below `nComp`. -/
def SlotCtCell (ctH nComp a : ℕ) : Prop := ∃ c < nComp, a = ctH + 3 * c

/-- **Loop 1** counts the edges of each component: afterwards the word `ctH + 3 c` holds the number
of edges `e` of `eL` whose tail lies in component `c`, as given by the word `cmpH + tail e`. The
registers below `25` and above `28` do not change, nor the other cells. -/
theorem slotCount_loop {w : ℕ} {p : Program} {mem : ℕ → ℕ} {G : MGraph} {eL : List ℕ}
    {ctH nComp eLB tsB iteB cmpH : ℕ} (R : ℕ → ℕ)
    (heLA : ListAt mem eLB eL) (heL : eLB + eL.length ≤ ctH)
    (hE : ∀ e ∈ eL, tsB + e < ctH ∧ iteB + mem (tsB + e) < ctH ∧
      mem (iteB + mem (tsB + e)) = G.tail e ∧ cmpH + G.tail e < ctH ∧
      mem (cmpH + G.tail e) < nComp)
    (hz : ∀ c < nComp, mem (ctH + 3 * c) = 0)
    (hw : ctH + 3 * nComp + eL.length < 2 ^ w) (hw16 : 16 ≤ 2 ^ w)
    (hR2 : R 2 = cmpH) (hR7 : R 7 = ctH) (hR11 : R 11 = eL.length) (hR12 : R 12 = eLB)
    (hR13 : R 13 = tsB) (hR14 : R 14 = iteB) :
    Triple w p (fun st => st.mem = mem ∧ ∀ r, r < 25 ∨ 28 < r → st.regs r = R r)
      (forRange 25 (.const 0) (.reg 11) slotCountStep)
      (normalPost fun st => (∀ r, r < 25 ∨ 28 < r → st.regs r = R r) ∧
        (∀ a, ¬ SlotCtCell ctH nComp a → st.mem a = mem a) ∧
        ∀ c < nComp, st.mem (ctH + 3 * c) =
          (eL.filter fun e => mem (cmpH + G.tail e) = c).length)
      (fun _ => eL.length * 60 + 10) := by
  set m := eL.length with hm
  have hw1 : 1 < 2 ^ w := by omega
  let Inv : ℕ → State → Prop := fun i st =>
    (∀ r, r < 25 ∨ 28 < r → st.regs r = R r) ∧ st.regs 25 = i ∧
    (∀ a, ¬ SlotCtCell ctH nComp a → st.mem a = mem a) ∧
    ∀ c < nComp, st.mem (ctH + 3 * c) =
      ((eL.take i).filter fun e => mem (cmpH + G.tail e) = c).length
  have hstep : ∀ i, 0 ≤ i → i < m →
      Triple w p (Inv i) slotCountStep
        (normalPost fun st₁ =>
          Inv (i + 1) { st₁ with regs := Function.update st₁.regs 25 (i + 1) } ∧
            st₁.regs 25 = i)
        (fun _ => 50) := by
    intro i _ hi st ω' hI
    obtain ⟨hR, r25, hfr, hcnt⟩ := hI
    have r2 : st.regs 2 = cmpH := (hR 2 (by omega)).trans hR2
    have r7 : st.regs 7 = ctH := (hR 7 (by omega)).trans hR7
    have r12 : st.regs 12 = eLB := (hR 12 (by omega)).trans hR12
    have r13 : st.regs 13 = tsB := (hR 13 (by omega)).trans hR13
    have r14 : st.regs 14 = iteB := (hR 14 (by omega)).trans hR14
    have hiL : i < eL.length := hi
    set e := eL[i] with he_def
    have heM : e ∈ eL := List.getElem_mem hiL
    obtain ⟨h1, h2, h3, h4, h5⟩ := hE e heM
    have hlow : ∀ a, a < ctH → st.mem a = mem a := fun a ha =>
      hfr a fun ⟨c, _, hc⟩ => by omega
    set c := mem (cmpH + G.tail e) with hc_def
    have m1 : st.mem (eLB + i) = e := by rw [hlow _ (by omega)]; exact heLA i hiL
    have m2 : st.mem (tsB + e) = mem (tsB + e) := hlow _ h1
    have m3 : st.mem (iteB + mem (tsB + e)) = G.tail e := by rw [hlow _ h2]; exact h3
    have m4 : st.mem (cmpH + G.tail e) = c := hlow _ h4
    have hcnt_le : ((eL.take i).filter fun e => mem (cmpH + G.tail e) = c).length ≤ i := by
      refine (List.length_filter_le _ _).trans ?_
      simp only [List.length_take]; omega
    have m5 : st.mem (ctH + 3 * c) =
        ((eL.take i).filter fun e => mem (cmpH + G.tail e) = c).length := hcnt c h5
    refine runs_start_le ?_
    unfold slotCountStep
    refine runs_seq_assign_le (v := e) (Expr.eval_load_of_eq (by eval_expr) m1) ?_
    refine runs_seq_assign_le (v := G.tail e)
      (Expr.eval_load_of_eq (Expr.eval_add (by eval_expr)
        (Expr.eval_load_of_eq (by eval_expr) m2) (by omega)) m3) ?_
    refine runs_seq_assign_le (v := ctH + 3 * c)
      (Expr.eval_add (by eval_expr) (Expr.eval_mul (Expr.eval_const (by omega))
        (Expr.eval_load_of_eq (by eval_expr) m4) (by omega)) (by omega)) ?_
    refine runs_store_le (x := ctH + 3 * c)
      (v := ((eL.take i).filter fun e => mem (cmpH + G.tail e) = c).length + 1)
      (by eval_expr) (Expr.eval_add (Expr.eval_load_of_eq (by eval_expr) m5)
        (Expr.eval_const (by omega)) (by omega)) ?_ ?_
    · refine ⟨⟨fun r hr => ?_, by simp, fun a ha => ?_, fun c' hc' => ?_⟩, by simp [r25]⟩
      · have h25 : r ≠ 25 := by omega
        have h26 : r ≠ 26 := by omega
        have h27 : r ≠ 27 := by omega
        simp [h25, h26, h27, hR r hr]
      · dsimp only
        rw [Function.update_of_ne (fun h => ha ⟨c, h5, h⟩)]
        exact hfr a ha
      · dsimp only
        rw [List.take_add_one, List.filter_append, List.length_append]
        simp only [List.getElem?_eq_getElem hiL, Option.toList_some, ← he_def]
        by_cases hcc : c' = c
        · subst hcc
          rw [Function.update_self]
          simp [← hc_def]
        · rw [Function.update_of_ne (by omega), hcnt c' hc']
          have hne : ¬ mem (cmpH + G.tail e) = c' := fun h => hcc (by rw [← h])
          simp [hne]
    · simp only [Expr.size_reg, Expr.size_load, Expr.size_bin, Expr.size_const]
      omega
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 25) (lo := .const 0)
    (hi := .reg 11) (body := slotCountStep)
    (P := fun st => st.mem = mem ∧ ∀ r, r < 25 ∨ 28 < r → st.regs r = R r)
    (Inv := Inv) 50 0 m (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hP => ⟨Expr.eval_const (by omega), fun r hr => by
        simp [show r ≠ 25 by omega, hP.2 r hr], by simp,
      fun a _ => by simp [hP.1], fun c hc => by simp [hP.1, hz c hc]⟩)
    (fun _ _ _ _ hI => hI.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq ((hI.1 11 (by omega)).trans hR11)) hstep
  refine (hloop.conseq (fun st h => h) ?_ ?_)
  · intro o st' hQ
    cases o with
    | returned _ => exact hQ
    | normal =>
      obtain ⟨hR, -, hfr, hcnt⟩ := hQ
      refine ⟨hR, hfr, fun c hc => ?_⟩
      rw [hcnt c hc, List.take_of_length_le (le_refl _)]
  · intro st _
    simp only [Expr.size_reg, Expr.size_const]
    omega

/-! ## Loop 2: the active flags -/

/-- The flag of a count: `[0 < x] - [4 x < k]` is `1` exactly when `1 ≤ x` and `k ≤ 4 x`. -/
theorem slot_flag_eq (x k : ℕ) :
    (if 0 < x then 1 else 0) - (if 4 * x < k then 1 else 0) =
      if 1 ≤ x ∧ k ≤ 4 * x then 1 else 0 := by
  split_ifs <;> omega

/-- **Loop 2** turns each count `cnt c` at `ctH + 3 c` into the active flag of the component:
`1` when `1 ≤ cnt c` and `k ≤ 4 cnt c`, and `0` otherwise. -/
theorem slotFlag_loop {w : ℕ} {p : Program} {mem : ℕ → ℕ} {ctH nComp k : ℕ} (R : ℕ → ℕ)
    (cnt : ℕ → ℕ) (hcnt : ∀ c < nComp, mem (ctH + 3 * c) = cnt c)
    (hcntB : ∀ c < nComp, 4 * cnt c < 2 ^ w)
    (hw : ctH + 3 * nComp < 2 ^ w) (hw16 : 16 ≤ 2 ^ w)
    (hR4 : R 4 = nComp) (hR5 : R 5 = k) (hR7 : R 7 = ctH) :
    Triple w p (fun st => st.mem = mem ∧ ∀ r, r < 25 ∨ 28 < r → st.regs r = R r)
      (forRange 25 (.const 0) (.reg 4) slotFlagStep)
      (normalPost fun st => (∀ r, r < 25 ∨ 28 < r → st.regs r = R r) ∧
        (∀ a, ¬ SlotCtCell ctH nComp a → st.mem a = mem a) ∧
        ∀ c < nComp, st.mem (ctH + 3 * c) = if 1 ≤ cnt c ∧ k ≤ 4 * cnt c then 1 else 0)
      (fun _ => nComp * 40 + 10) := by
  have hw1 : 1 < 2 ^ w := by omega
  let Inv : ℕ → State → Prop := fun i st =>
    (∀ r, r < 25 ∨ 28 < r → st.regs r = R r) ∧ st.regs 25 = i ∧
    (∀ a, ¬ SlotCtCell ctH nComp a → st.mem a = mem a) ∧
    ∀ c < nComp, st.mem (ctH + 3 * c) =
      if c < i then (if 1 ≤ cnt c ∧ k ≤ 4 * cnt c then 1 else 0) else cnt c
  have hstep : ∀ i, 0 ≤ i → i < nComp →
      Triple w p (Inv i) slotFlagStep
        (normalPost fun st₁ =>
          Inv (i + 1) { st₁ with regs := Function.update st₁.regs 25 (i + 1) } ∧
            st₁.regs 25 = i)
        (fun _ => 30) := by
    intro i _ hi st ω' hI
    obtain ⟨hR, r25, hfr, hcur⟩ := hI
    have r5 : st.regs 5 = k := (hR 5 (by omega)).trans hR5
    have r7 : st.regs 7 = ctH := (hR 7 (by omega)).trans hR7
    have m1 : st.mem (ctH + 3 * i) = cnt i := by
      rw [hcur i hi]; simp
    have hx : (if 0 < cnt i then 1 else 0) < 2 ^ w := by split_ifs <;> omega
    refine runs_start_le ?_
    unfold slotFlagStep
    refine runs_seq_assign_le (v := ctH + 3 * i) (by eval_expr) ?_
    refine runs_seq_assign_le (v := cnt i) (Expr.eval_load_of_eq (by eval_expr) m1) ?_
    have hv := slot_flag_eq (cnt i) k
    refine runs_store_le (x := ctH + 3 * i)
      (v := if 1 ≤ cnt i ∧ k ≤ 4 * cnt i then 1 else 0) (by eval_expr)
      (Expr.eval_eq_of_eq (Expr.eval_sub (Expr.eval_lt_op (Expr.eval_const (by omega))
        (by eval_expr) hw1) (Expr.eval_lt_op (Expr.eval_mul (Expr.eval_const (by omega))
          (by eval_expr) (hcntB i hi)) (by eval_expr) hw1) hx) hv) ?_ ?_
    · refine ⟨⟨fun r hr => ?_, by simp, fun a ha => ?_, fun c hc => ?_⟩, by simp [r25]⟩
      · have h25 : r ≠ 25 := by omega
        have h26 : r ≠ 26 := by omega
        have h27 : r ≠ 27 := by omega
        simp [h25, h26, h27, hR r hr]
      · dsimp only
        rw [Function.update_of_ne (fun h => ha ⟨i, hi, h⟩)]
        exact hfr a ha
      · dsimp only
        by_cases hci : c = i
        · subst hci
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne (by omega), hcur c hc]
          by_cases hlt : c < i
          · simp [hlt, show c < i + 1 by omega]
          · simp [hlt, show ¬ c < i + 1 by omega]
    · simp only [Expr.size_reg, Expr.size_load, Expr.size_bin, Expr.size_const]
      omega
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 25) (lo := .const 0)
    (hi := .reg 4) (body := slotFlagStep)
    (P := fun st => st.mem = mem ∧ ∀ r, r < 25 ∨ 28 < r → st.regs r = R r)
    (Inv := Inv) 30 0 nComp (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hP => ⟨Expr.eval_const (by omega), fun r hr => by
        simp [show r ≠ 25 by omega, hP.2 r hr], by simp,
      fun a _ => by simp [hP.1], fun c hc => by simp [hP.1, hcnt c hc]⟩)
    (fun _ _ _ _ hI => hI.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq ((hI.1 4 (by omega)).trans hR4)) hstep
  refine (hloop.conseq (fun st h => h) ?_ ?_)
  · intro o st' hQ
    cases o with
    | returned _ => exact hQ
    | normal =>
      obtain ⟨hR, -, hfr, hcur⟩ := hQ
      exact ⟨hR, hfr, fun c hc => by rw [hcur c hc]; simp [hc]⟩
  · intro st _
    simp only [Expr.size_reg, Expr.size_const]
    omega

/-! ## Loop 3: the marks of the forest edges -/

/-- **Loop 3** marks the edges `fe` of the forest: the edge of the `t`-th triple at `fTrip` is
`fe[t]`, and afterwards the word `markH + e` is `1` for `e ∈ fe` and stays `0` for the other
`e < eCap`. Only the marks change. -/
theorem slotMark_loop {w : ℕ} {p : Program} {mem : ℕ → ℕ} {fTrip markH eCap : ℕ}
    {fe : List ℕ} (R : ℕ → ℕ)
    (hfe : ∀ t (ht : t < fe.length), mem (fTrip + 3 * t) = fe[t])
    (hfeLt : ∀ e ∈ fe, e < eCap) (hlay : fTrip + 3 * fe.length ≤ markH)
    (hz : ∀ e < eCap, mem (markH + e) = 0) (hw : markH + eCap < 2 ^ w) (hw16 : 16 ≤ 2 ^ w)
    (hR15 : R 15 = fe.length) (hR16 : R 16 = fTrip) (hR17 : R 17 = markH) :
    Triple w p (fun st => st.mem = mem ∧ ∀ r, r < 25 ∨ 28 < r → st.regs r = R r)
      (forRange 25 (.const 0) (.reg 15) slotMarkStep)
      (normalPost fun st => (∀ r, r < 25 ∨ 28 < r → st.regs r = R r) ∧
        (∀ a, (a < markH ∨ markH + eCap ≤ a) → st.mem a = mem a) ∧
        ∀ e < eCap, st.mem (markH + e) = if e ∈ fe then 1 else 0)
      (fun _ => fe.length * 21 + 10) := by
  have hw1 : 1 < 2 ^ w := by omega
  let Inv : ℕ → State → Prop := fun i st =>
    (∀ r, r < 25 ∨ 28 < r → st.regs r = R r) ∧ st.regs 25 = i ∧
    (∀ a, (a < markH ∨ markH + eCap ≤ a) → st.mem a = mem a) ∧
    ∀ e < eCap, st.mem (markH + e) = if e ∈ fe.take i then 1 else 0
  have hstep : ∀ i, 0 ≤ i → i < fe.length →
      Triple w p (Inv i) slotMarkStep
        (normalPost fun st₁ =>
          Inv (i + 1) { st₁ with regs := Function.update st₁.regs 25 (i + 1) } ∧
            st₁.regs 25 = i)
        (fun _ => 12) := by
    intro i _ hi st ω' hI
    obtain ⟨hR, r25, hfr, hcur⟩ := hI
    have r16 : st.regs 16 = fTrip := (hR 16 (by omega)).trans hR16
    have r17 : st.regs 17 = markH := (hR 17 (by omega)).trans hR17
    have heC : fe[i] < eCap := hfeLt _ (List.getElem_mem hi)
    have m1 : st.mem (fTrip + 3 * i) = fe[i] := by
      rw [hfr _ (Or.inl (by omega))]; exact hfe i hi
    refine runs_start_le ?_
    unfold slotMarkStep
    refine runs_store_le (x := markH + fe[i]) (v := 1)
      (Expr.eval_add (by eval_expr) (Expr.eval_load_of_eq (Expr.eval_add (by eval_expr)
        (Expr.eval_mul (Expr.eval_const (by omega)) (by eval_expr) (by omega)) (by omega)) m1)
        (by omega)) (Expr.eval_const hw1) ?_ ?_
    · refine ⟨⟨fun r hr => ?_, by simp, fun a ha => ?_, fun e he => ?_⟩, by simp [r25]⟩
      · simp [show r ≠ 25 by omega, hR r hr]
      · dsimp only
        rw [Function.update_of_ne (by omega)]
        exact hfr a ha
      · dsimp only
        rw [List.take_add_one]
        simp only [List.getElem?_eq_getElem hi, Option.toList_some, List.mem_append,
          List.mem_singleton]
        by_cases hee : e = fe[i]
        · rw [hee, Function.update_self]; simp
        · rw [Function.update_of_ne (by omega), hcur e he]
          simp [hee]
    · simp only [Expr.size_reg, Expr.size_load, Expr.size_bin, Expr.size_const]
      omega
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 25) (lo := .const 0)
    (hi := .reg 15) (body := slotMarkStep)
    (P := fun st => st.mem = mem ∧ ∀ r, r < 25 ∨ 28 < r → st.regs r = R r)
    (Inv := Inv) 12 0 fe.length (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hP => ⟨Expr.eval_const (by omega), fun r hr => by
        simp [show r ≠ 25 by omega, hP.2 r hr], by simp,
      fun a _ => by simp [hP.1], fun e he => by simp [hP.1, hz e he]⟩)
    (fun _ _ _ _ hI => hI.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq ((hI.1 15 (by omega)).trans hR15)) hstep
  refine (hloop.conseq (fun st h => h) ?_ ?_)
  · intro o st' hQ
    cases o with
    | returned _ => exact hQ
    | normal =>
      obtain ⟨hR, -, hfr, hcur⟩ := hQ
      exact ⟨hR, hfr, fun e he => by rw [hcur e he, List.take_of_length_le (le_refl _)]⟩
  · intro st _
    simp only [Expr.size_reg, Expr.size_const]
    omega

end MinCostFlow.SparseCore.Program
