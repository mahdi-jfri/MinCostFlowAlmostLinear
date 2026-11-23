module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitSlotKeys
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# The slots of the active pairs at the init: the walk over the slots (`AssemblyFirstInitSlotWalk`)

After the sort, the keys without repeats form the strictly increasing list `D` at `DH`. The slot
of a pair is the index of its key in `D`. This file proves the last two loops of `slotListBody`.

* Loop 5 walks `D` (`slotWalk_loop`). Entry `j` writes the pair `(D[j] mod B, j)`, the slot `j`
  and the spec word `j`. It also keeps, for each component `c`, the number of entries of `c` seen so
  far and the address of the list of `c`. Since `D` is sorted, the entries of `c` form one segment
  of `D` (`slotSeg_iff`), so the address is `pairsH + 2 · (start of the segment)`.
* Loop 6 walks the pairs `(e, key)` (`slotAssign_loop`). It finds the slot of each key by binary
  search in `D`, writes it in place of the key, and adds `4` to the spec word of that slot.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.DynSpanner.Program

/-! ## Counting the entries of a component -/

/-- The number of entries of component `c` among the first `j` entries of `D`. -/
def slotCntUpTo (D : List ℕ) (B c j : ℕ) : ℕ :=
  ((List.range j).filter fun t => decide (D.getD t 0 / B = c)).length

theorem slotCntUpTo_succ (D : List ℕ) (B c j : ℕ) :
    slotCntUpTo D B c (j + 1) = slotCntUpTo D B c j + if D.getD j 0 / B = c then 1 else 0 := by
  unfold slotCntUpTo
  rw [List.range_succ, List.filter_append, List.length_append, List.filter_cons, List.filter_nil]
  by_cases h : D.getD j 0 / B = c
  · rw [ite_eq_left (decide_eq_true h), ite_eq_left h]; rfl
  · rw [ite_eq_right (by simpa using h), ite_eq_right h]; rfl

theorem slotCntUpTo_le (D : List ℕ) (B c j : ℕ) : slotCntUpTo D B c j ≤ j :=
  (List.length_filter_le _ _).trans (by simp)

theorem slotCntUpTo_length (D : List ℕ) (B c : ℕ) :
    slotCntUpTo D B c D.length = slotSegLen D B c := rfl

/-- The numbers below `j` that are at least `s` are `j - s` many. -/
theorem range_filter_ge (s j : ℕ) :
    ((List.range j).filter fun t => decide (s ≤ t)).length = j - s := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih]
    by_cases h : s ≤ j
    · simp [h]; omega
    · simp [h]; omega

/-- In a strictly increasing `D`, if entry `j` has component `c`, then the entries of `c` before
`j` are those from the start of the segment of `c` (`slotSeg_iff`). -/
theorem slotCntUpTo_eq {D : List ℕ} (hs : D.Pairwise (· < ·)) (B c : ℕ) {j : ℕ}
    (hj : j < D.length) (hc : D.getD j 0 / B = c) :
    slotSegStart D B c ≤ j ∧ slotCntUpTo D B c j = j - slotSegStart D B c := by
  obtain ⟨h1, h2⟩ := (slotSeg_iff hs B c hj).mp hc
  refine ⟨h1, ?_⟩
  rw [← range_filter_ge]
  unfold slotCntUpTo
  congr 1
  apply List.filter_congr
  intro t ht
  rw [List.mem_range] at ht
  have h := slotSeg_iff hs B c (show t < D.length by omega)
  simp only [decide_eq_decide, h]
  constructor
  · exact fun h' => h'.1
  · exact fun h' => ⟨h', by omega⟩

/-! ## Loop 5: the pairs, the slots and the lists of the components -/

/-- The cells that loop 5 writes: the address and the length of each component list, the pairs,
the slots, and the first word of each spec. -/
def SlotWalkCell (ctH nComp pairsH slotsH specsH nD a : ℕ) : Prop :=
  (∃ c < nComp, a = ctH + 3 * c + 1 ∨ a = ctH + 3 * c + 2) ∨
    (pairsH ≤ a ∧ a < pairsH + 2 * nD) ∨ (slotsH ≤ a ∧ a < slotsH + nD) ∨
    ∃ j < nD, a = specsH + 2 * j

/-- **Loop 5.** For each entry `j` of `D`: the pair `(D[j] mod B, j)` at `pairsH + 2 j`, the slot
`j` at `slotsH + j` and the word `j` at `specsH + 2 j`. For each component `c`, the word
`ctH + 3 c + 2` ends at the length of the segment of `c` in `D`, and the word `ctH + 3 c + 1` at
the address `pairsH + 2 · start` of its pairs (or stays `0` when the segment is empty). -/
theorem slotWalk_loop {w : ℕ} {p : Program} {mem : ℕ → ℕ} {D : List ℕ}
    {DH ctH pairsH slotsH specsH nComp B : ℕ} (R : ℕ → ℕ)
    (hs : D.Pairwise (· < ·)) (hDA : ListAt mem DH D) (hDw : ∀ x ∈ D, x < 2 ^ w)
    (hDc : ∀ x ∈ D, x / B < nComp)
    (hz : ∀ c < nComp, mem (ctH + 3 * c + 1) = 0 ∧ mem (ctH + 3 * c + 2) = 0)
    (hct : ctH + 3 * nComp ≤ DH) (hDp : DH + D.length ≤ pairsH)
    (hps : pairsH + 2 * D.length ≤ slotsH) (hss : slotsH + D.length ≤ specsH)
    (hw : specsH + 2 * D.length < 2 ^ w) (hw16 : 16 ≤ 2 ^ w)
    (hR6 : R 6 = B) (hR7 : R 7 = ctH) (hR20 : R 20 = DH) (hR21 : R 21 = pairsH)
    (hR22 : R 22 = slotsH) (hR23 : R 23 = specsH) (hR30 : R 30 = D.length) :
    Triple w p (fun st => st.mem = mem ∧ ∀ r, r < 25 ∨ 28 < r → st.regs r = R r)
      (forRange 25 (.const 0) (.reg 30) slotWalkStep)
      (normalPost fun st => (∀ r, r < 25 ∨ 28 < r → st.regs r = R r) ∧
        (∀ a, ¬ SlotWalkCell ctH nComp pairsH slotsH specsH D.length a → st.mem a = mem a) ∧
        (∀ j (hj : j < D.length), st.mem (pairsH + 2 * j) = D[j] % B ∧
          st.mem (pairsH + 2 * j + 1) = j ∧ st.mem (slotsH + j) = j ∧
          st.mem (specsH + 2 * j) = j) ∧
        ∀ c < nComp, st.mem (ctH + 3 * c + 1) =
            (if 0 < slotSegLen D B c then pairsH + 2 * slotSegStart D B c else 0) ∧
          st.mem (ctH + 3 * c + 2) = slotSegLen D B c)
      (fun _ => D.length * 120 + 10) := by
  set nD := D.length with hnD
  have hw1 : 1 < 2 ^ w := by omega
  let Inv : ℕ → State → Prop := fun i st =>
    (∀ r, r < 25 ∨ 28 < r → st.regs r = R r) ∧ st.regs 25 = i ∧
    (∀ a, ¬ SlotWalkCell ctH nComp pairsH slotsH specsH nD a → st.mem a = mem a) ∧
    (∀ j (hj : j < nD), j < i → st.mem (pairsH + 2 * j) = D[j] % B ∧
      st.mem (pairsH + 2 * j + 1) = j ∧ st.mem (slotsH + j) = j ∧
      st.mem (specsH + 2 * j) = j) ∧
    (∀ j, i ≤ j → j < nD → st.mem (pairsH + 2 * j) = mem (pairsH + 2 * j) ∧
      st.mem (pairsH + 2 * j + 1) = mem (pairsH + 2 * j + 1) ∧
      st.mem (slotsH + j) = mem (slotsH + j) ∧ st.mem (specsH + 2 * j) = mem (specsH + 2 * j)) ∧
    ∀ c < nComp, st.mem (ctH + 3 * c + 1) =
        (if 0 < slotCntUpTo D B c i then pairsH + 2 * slotSegStart D B c else 0) ∧
      st.mem (ctH + 3 * c + 2) = slotCntUpTo D B c i
  have hstep : ∀ i, 0 ≤ i → i < nD →
      Triple w p (Inv i) slotWalkStep
        (normalPost fun st₁ =>
          Inv (i + 1) { st₁ with regs := Function.update st₁.regs 25 (i + 1) } ∧
            st₁.regs 25 = i)
        (fun _ => 110) := by
    intro i _ hi st ω' hI
    obtain ⟨hR, r25, hfr, hdone, hrest, hct'⟩ := hI
    have r6 : st.regs 6 = B := (hR 6 (by omega)).trans hR6
    have r7 : st.regs 7 = ctH := (hR 7 (by omega)).trans hR7
    have r20 : st.regs 20 = DH := (hR 20 (by omega)).trans hR20
    have r21 : st.regs 21 = pairsH := (hR 21 (by omega)).trans hR21
    have r22 : st.regs 22 = slotsH := (hR 22 (by omega)).trans hR22
    have r23 : st.regs 23 = specsH := (hR 23 (by omega)).trans hR23
    have hiL : i < D.length := hi
    set x := D[i] with hx_def
    have hxw : x < 2 ^ w := hDw x (List.getElem_mem hiL)
    set c := x / B with hc_def
    have hcn : c < nComp := hDc x (List.getElem_mem hiL)
    have hgetD : D.getD i 0 = x := by rw [List.getD_eq_getElem _ _ hiL]
    obtain ⟨hst, hcnt⟩ := slotCntUpTo_eq hs B c hiL (by rw [hgetD])
    set n := slotCntUpTo D B c i with hn_def
    have hni : n ≤ i := slotCntUpTo_le D B c i
    have m1 : st.mem (DH + i) = x := by
      rw [hfr _ (by
        rintro (⟨c', _, h | h⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨j, _, _⟩) <;> omega)]
      exact hDA i hiL
    have m2 : st.mem (ctH + 3 * c + 2) = n := (hct' c hcn).2
    refine runs_start_le ?_
    unfold slotWalkStep
    refine runs_seq_assign_le (v := x) (Expr.eval_load_of_eq (by eval_expr) m1) ?_
    refine runs_seq_assign_le (v := ctH + 3 * c)
      (Expr.eval_add (by eval_expr) (Expr.eval_mul (Expr.eval_const (by omega))
        (Expr.eval_div (by eval_expr) (by eval_expr) hxw) (by omega)) (by omega)) ?_
    refine runs_seq_store_le (x := pairsH + 2 * i) (v := x % B)
      (Expr.eval_add (by eval_expr) (Expr.eval_mul (Expr.eval_const (by omega)) (by eval_expr)
        (by omega)) (by omega)) (Expr.eval_mod (by eval_expr) (by eval_expr) hxw) ?_
    refine runs_seq_store_le (x := pairsH + 1 + 2 * i) (v := i)
      (Expr.eval_add (Expr.eval_add (by eval_expr) (Expr.eval_const (by omega)) (by omega))
        (Expr.eval_mul (Expr.eval_const (by omega)) (by eval_expr) (by omega)) (by omega))
      (by eval_expr) ?_
    refine runs_seq_store_le (x := slotsH + i) (v := i)
      (Expr.eval_add (by eval_expr) (by eval_expr) (by omega)) (by eval_expr) ?_
    refine runs_seq_store_le (x := specsH + 2 * i) (v := i)
      (Expr.eval_add (by eval_expr) (Expr.eval_mul (Expr.eval_const (by omega)) (by eval_expr)
        (by omega)) (by omega)) (by eval_expr) ?_
    -- the four stores above do not touch the words of the components
    have hd1 : ctH + 3 * c + 2 ≠ specsH + 2 * i := by omega
    have hd2 : ctH + 3 * c + 2 ≠ slotsH + i := by omega
    have hd3 : ctH + 3 * c + 2 ≠ pairsH + 1 + 2 * i := by omega
    have hd4 : ctH + 3 * c + 2 ≠ pairsH + 2 * i := by omega
    have m3 : (Function.update (Function.update (Function.update (Function.update st.mem
        (pairsH + 2 * i) (x % B)) (pairsH + 1 + 2 * i) i) (slotsH + i) i) (specsH + 2 * i) i)
        (ctH + 3 * c + 2) = n := by
      rw [Function.update_of_ne hd1, Function.update_of_ne hd2, Function.update_of_ne hd3,
        Function.update_of_ne hd4, m2]
    refine runs_seq_store_le (x := ctH + 3 * c + 1) (v := pairsH + 2 * (i - n))
      (Expr.eval_add (by eval_expr) (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_add (by eval_expr) (Expr.eval_mul (Expr.eval_const (by omega))
        (Expr.eval_sub (by eval_expr) (Expr.eval_load_of_eq
          (Expr.eval_add (by eval_expr) (Expr.eval_const (by omega)) (by omega)) m3) (by omega))
        (by omega)) (by omega)) ?_
    have m4 : (Function.update (Function.update (Function.update (Function.update
        (Function.update st.mem (pairsH + 2 * i) (x % B)) (pairsH + 1 + 2 * i) i) (slotsH + i) i)
        (specsH + 2 * i) i) (ctH + 3 * c + 1) (pairsH + 2 * (i - n))) (ctH + 3 * c + 2) = n := by
      rw [Function.update_of_ne (by omega), m3]
    refine runs_store_le (x := ctH + 3 * c + 2) (v := n + 1)
      (Expr.eval_add (by eval_expr) (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_add (Expr.eval_load_of_eq
        (Expr.eval_add (by eval_expr) (Expr.eval_const (by omega)) (by omega)) m4)
        (Expr.eval_const (by omega)) (by omega)) ?_ ?_
    · refine ⟨⟨fun r hr => ?_, by simp, fun a ha => ?_, fun j hj hji => ?_, fun j hji hj => ?_,
        fun c' hc' => ?_⟩, by simp [r25]⟩
      · simp [show r ≠ 25 by omega, show r ≠ 26 by omega, show r ≠ 27 by omega, hR r hr]
      · -- a cell outside the written ones
        have n1 : a ≠ ctH + 3 * c + 2 := fun h => ha (Or.inl ⟨c, hcn, Or.inr h⟩)
        have n2 : a ≠ ctH + 3 * c + 1 := fun h => ha (Or.inl ⟨c, hcn, Or.inl h⟩)
        have n3 : a ≠ specsH + 2 * i := fun h => ha (Or.inr (Or.inr (Or.inr ⟨i, hi, h⟩)))
        have n4 : a ≠ slotsH + i := fun h => ha (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
        have n5 : a ≠ pairsH + 1 + 2 * i := fun h => ha (Or.inr (Or.inl ⟨by omega, by omega⟩))
        have n6 : a ≠ pairsH + 2 * i := fun h => ha (Or.inr (Or.inl ⟨by omega, by omega⟩))
        dsimp only
        rw [Function.update_of_ne n1, Function.update_of_ne n2, Function.update_of_ne n3,
          Function.update_of_ne n4, Function.update_of_ne n5, Function.update_of_ne n6]
        exact hfr a ha
      · dsimp only
        by_cases hji' : j = i
        · subst hji'
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_self]
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              show pairsH + 2 * j + 1 = pairsH + 1 + 2 * j by omega, Function.update_self]
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_self]
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_self]
        · have hj' : j < i := by omega
          obtain ⟨e1, e2, e3, e4⟩ := hdone j hj hj'
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega), e1]
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega), e2]
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega), e3]
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega), e4]
      · dsimp only
        obtain ⟨e1, e2, e3, e4⟩ := hrest j (by omega) hj
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega), e1]
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega), e2]
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega), e3]
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega), e4]
      · dsimp only
        rw [slotCntUpTo_succ, hgetD]
        by_cases hcc : c' = c
        · subst hcc
          rw [ite_eq_left hc_def.symm]
          refine ⟨?_, ?_⟩
          · rw [Function.update_of_ne (by omega), Function.update_self, ite_eq_left (by omega)]
            omega
          · rw [Function.update_self]
        · have hxc : ¬ x / B = c' := fun h => hcc (by rw [← h])
          simp only [ite_eq_right hxc, Nat.add_zero]
          obtain ⟨e1, e2⟩ := hct' c' hc'
          refine ⟨?_, ?_⟩
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega), e1]
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega), e2]
    · simp only [Expr.size_reg, Expr.size_load, Expr.size_bin, Expr.size_const]
      omega
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 25) (lo := .const 0)
    (hi := .reg 30) (body := slotWalkStep)
    (P := fun st => st.mem = mem ∧ ∀ r, r < 25 ∨ 28 < r → st.regs r = R r)
    (Inv := Inv) 110 0 nD (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hP => ⟨Expr.eval_const (by omega), fun r hr => by
        simp [show r ≠ 25 by omega, hP.2 r hr], by simp,
      fun a _ => by simp [hP.1], fun j _ hj => absurd hj (Nat.not_lt_zero _),
      fun j _ _ => by simp [hP.1],
      fun c hc => by simp [hP.1, slotCntUpTo, (hz c hc).1, (hz c hc).2]⟩)
    (fun _ _ _ _ hI => hI.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq ((hI.1 30 (by omega)).trans hR30)) hstep
  refine (hloop.conseq (fun st h => h) ?_ ?_)
  · intro o st' hQ
    cases o with
    | returned _ => exact hQ
    | normal =>
      obtain ⟨hR, -, hfr, hdone, -, hct'⟩ := hQ
      exact ⟨hR, hfr, fun j hj => hdone j hj hj, fun c hc => by
        rw [← slotCntUpTo_length]; exact hct' c hc⟩
  · intro st _
    simp only [Expr.size_reg, Expr.size_const]
    omega

/-! ## Loop 6: the slot of each edge and the sizes of the slots -/

/-- The cells that loop 6 writes: the second word of each spec and of each assignment. -/
def SlotAssignCell (specsH nD asgH nK a : ℕ) : Prop :=
  (∃ s < nD, a = specsH + 2 * s + 1) ∨ ∃ t < nK, a = asgH + 2 * t + 1

/-- **Loop 6.** For each selected edge `S[t]`, the second word of its assignment changes from its
key to the index of the key in `D` (binary search), and the second word of the spec of that slot
goes up by `4`. In the end the spec word of slot `s` is `4` times the number of selected edges with
slot `s`. -/
theorem slotAssign_loop {w : ℕ} {p : Program} {mem : ℕ → ℕ} {D S : List ℕ}
    {DH specsH asgH bSort : ℕ} (keyOf : ℕ → ℕ) (R : ℕ → ℕ)
    (hpSort : p.HasAt bSort (sortProcs bSort))
    (hs : D.Pairwise (· < ·)) (hDA : ListAt mem DH D) (hDw : ∀ x ∈ D, x < 2 ^ w)
    (hkey : ∀ e ∈ S, keyOf e ∈ D)
    (hasg : ∀ t (ht : t < S.length), mem (asgH + 2 * t + 1) = keyOf S[t])
    (hspec : ∀ s < D.length, mem (specsH + 2 * s + 1) = 0)
    (hDs : DH + D.length ≤ specsH) (hsa : specsH + 2 * D.length ≤ asgH)
    (hw : asgH + 6 * S.length + 4 < 2 ^ w) (hw16 : 16 ≤ 2 ^ w)
    (hR20 : R 20 = DH) (hR23 : R 23 = specsH) (hR24 : R 24 = asgH) (hR29 : R 29 = S.length)
    (hR30 : R 30 = D.length) :
    Triple w p (fun st => st.mem = mem ∧ ∀ r, r < 25 ∨ 28 < r → st.regs r = R r)
      (forRange 25 (.const 0) (.reg 29) (slotAssignStep bSort))
      (normalPost fun st => (∀ r, r < 25 ∨ 28 < r → st.regs r = R r) ∧
        (∀ a, ¬ SlotAssignCell specsH D.length asgH S.length a → st.mem a = mem a) ∧
        (∀ t (ht : t < S.length), st.mem (asgH + 2 * t + 1) = D.idxOf (keyOf S[t])) ∧
        ∀ s < D.length, st.mem (specsH + 2 * s + 1) =
          4 * (S.filter fun e => D.idxOf (keyOf e) = s).length)
      (fun _ => S.length * (45 * (Nat.log 2 (D.length + 1) + 1) + 80) + 10) := by
  set nK := S.length with hnK
  have hw1 : 1 < 2 ^ w := by omega
  set K := 45 * (Nat.log 2 (D.length + 1) + 1) + 60 with hK
  let cntS : ℕ → ℕ → ℕ := fun t s => ((S.take t).filter fun e => D.idxOf (keyOf e) = s).length
  have hcnt_le : ∀ t s, cntS t s ≤ t := fun t s => by
    refine (List.length_filter_le _ _).trans ?_
    simp only [List.length_take]; omega
  let Inv : ℕ → State → Prop := fun i st =>
    (∀ r, r < 25 ∨ 28 < r → st.regs r = R r) ∧ st.regs 25 = i ∧
    (∀ a, ¬ SlotAssignCell specsH D.length asgH nK a → st.mem a = mem a) ∧
    (∀ u (hu : u < nK), st.mem (asgH + 2 * u + 1) =
      if u < i then D.idxOf (keyOf S[u]) else keyOf S[u]) ∧
    ∀ s < D.length, st.mem (specsH + 2 * s + 1) = 4 * cntS i s
  have hstep : ∀ i, 0 ≤ i → i < nK →
      Triple w p (Inv i) (slotAssignStep bSort)
        (normalPost fun st₁ =>
          Inv (i + 1) { st₁ with regs := Function.update st₁.regs 25 (i + 1) } ∧
            st₁.regs 25 = i)
        (fun _ => K) := by
    intro i _ hi st ω' hI
    obtain ⟨hR, r25, hfr, hasg', hspec'⟩ := hI
    have r20 : st.regs 20 = DH := (hR 20 (by omega)).trans hR20
    have r23 : st.regs 23 = specsH := (hR 23 (by omega)).trans hR23
    have r24 : st.regs 24 = asgH := (hR 24 (by omega)).trans hR24
    have r30 : st.regs 30 = D.length := (hR 30 (by omega)).trans hR30
    have hiL : i < S.length := hi
    set e := S[i] with he_def
    have hkD : keyOf e ∈ D := hkey e (List.getElem_mem hiL)
    have hkw : keyOf e < 2 ^ w := hDw _ hkD
    have m1 : st.mem (asgH + 1 + 2 * i) = keyOf e := by
      rw [show asgH + 1 + 2 * i = asgH + 2 * i + 1 by omega, hasg' i hi,
        ite_eq_right (lt_irrefl i)]
    have hDA' : ListAt st.mem DH D := hDA.congr fun k hk1 hk2 => hfr k (by
      rintro (⟨s, _, h⟩ | ⟨t, _, h⟩) <;> omega)
    have hbs := binSearch_meetsContract (w := w) (p := p) (b := bSort) (bSort := bSort) (L := D)
      (key := keyOf e) hpSort
    refine runs_start_le ?_
    unfold slotAssignStep
    refine runs_seq_call_le hbs (vs := [DH, D.length, keyOf e])
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add (by eval_expr)
          (Expr.eval_const (by omega)) (by omega)) (Expr.eval_mul (Expr.eval_const (by omega))
            (by eval_expr) (by omega)) (by omega)) m1) (evalArgs_nil _ _))))
      (by intro v hv; simp at hv; omega)
      ⟨DH, rfl, hw16, by omega, hs, hkD, hDA', hDw⟩ (fun v mem' pos' hpost => ?_)
    obtain ⟨a, hargs, hmem, hret, hlt⟩ := hpost
    subst hmem
    have hvs : v = D.idxOf (keyOf e) := hret
    have hcs : cntS i v ≤ i := hcnt_le i v
    have m2 : (Function.update st.mem (asgH + 1 + 2 * i) v) (specsH + 1 + 2 * v) =
        4 * cntS i v := by
      rw [Function.update_of_ne (by omega), show specsH + 1 + 2 * v = specsH + 2 * v + 1 by omega,
        hspec' v hlt]
    refine runs_seq_store_le (x := asgH + 1 + 2 * i) (v := v)
      (Expr.eval_add (Expr.eval_add (by eval_expr) (Expr.eval_const (by omega)) (by omega))
        (Expr.eval_mul (Expr.eval_const (by omega)) (by eval_expr) (by omega)) (by omega))
      (by eval_expr) ?_
    refine runs_store_le (x := specsH + 1 + 2 * v) (v := 4 * cntS i v + 4)
      (Expr.eval_add (Expr.eval_add (by eval_expr) (Expr.eval_const (by omega)) (by omega))
        (Expr.eval_mul (Expr.eval_const (by omega)) (by eval_expr) (by omega)) (by omega))
      (Expr.eval_add (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add (by eval_expr)
        (Expr.eval_const (by omega)) (by omega)) (Expr.eval_mul (Expr.eval_const (by omega))
          (by eval_expr) (by omega)) (by omega)) m2) (Expr.eval_const (by omega)) (by omega)) ?_ ?_
    · refine ⟨⟨fun r hr => ?_, by simp, fun a ha => ?_, fun u hu => ?_, fun s' hs' => ?_⟩,
        by simp [r25]⟩
      · simp [show r ≠ 25 by omega, show r ≠ 26 by omega, hR r hr]
      · have n1 : a ≠ specsH + 1 + 2 * v := fun h => ha (Or.inl ⟨v, hlt, by omega⟩)
        have n2 : a ≠ asgH + 1 + 2 * i := fun h => ha (Or.inr ⟨i, hi, by omega⟩)
        dsimp only
        rw [Function.update_of_ne n1, Function.update_of_ne n2]
        exact hfr a ha
      · dsimp only
        rw [Function.update_of_ne (by omega)]
        by_cases hui : u = i
        · subst hui
          rw [show asgH + 2 * u + 1 = asgH + 1 + 2 * u by omega, Function.update_self,
            ite_eq_left (by omega)]
          exact hvs
        · rw [Function.update_of_ne (by omega), hasg' u hu]
          by_cases hu' : u < i
          · rw [ite_eq_left hu', ite_eq_left (by omega)]
          · rw [ite_eq_right hu', ite_eq_right (by omega)]
      · dsimp only
        have hsucc : cntS (i + 1) s' = cntS i s' + if D.idxOf (keyOf e) = s' then 1 else 0 := by
          simp only [cntS]
          rw [take_succ_filter hiL]
          by_cases h : D.idxOf (keyOf e) = s'
          · simp [← he_def, h]
          · simp [← he_def, h]
        rw [hsucc]
        by_cases hss : s' = v
        · subst hss
          rw [show specsH + 2 * s' + 1 = specsH + 1 + 2 * s' by omega, Function.update_self,
            ite_eq_left hvs.symm]
          omega
        · have hne : ¬ D.idxOf (keyOf e) = s' := fun h => hss (h.symm.trans hvs.symm)
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hspec' s' hs',
            ite_eq_right hne, Nat.add_zero]
    · simp only [Expr.size_reg, Expr.size_load, Expr.size_bin, Expr.size_const, argsSize_cons,
        argsSize_nil, binSearchContract]
      omega
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 25) (lo := .const 0)
    (hi := .reg 29) (body := slotAssignStep bSort)
    (P := fun st => st.mem = mem ∧ ∀ r, r < 25 ∨ 28 < r → st.regs r = R r)
    (Inv := Inv) K 0 nK (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hP => ⟨Expr.eval_const (by omega), fun r hr => by
        simp [show r ≠ 25 by omega, hP.2 r hr], by simp,
      fun a _ => by simp [hP.1], fun u hu => by simp [hP.1, hasg u hu],
      fun s hs => by simp [hP.1, hspec s hs, cntS]⟩)
    (fun _ _ _ _ hI => hI.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq ((hI.1 29 (by omega)).trans hR29)) hstep
  refine (hloop.conseq (fun st h => h) ?_ ?_)
  · intro o st' hQ
    cases o with
    | returned _ => exact hQ
    | normal =>
      obtain ⟨hR, -, hfr, hasg', hspec'⟩ := hQ
      refine ⟨hR, hfr, fun t ht => by rw [hasg' t ht, ite_eq_left ht], fun s hs => ?_⟩
      rw [hspec' s hs]
      simp only [cntS]
      rw [hnK, List.take_length]
  · intro st _
    simp only [Expr.size_reg, Expr.size_const, Nat.sub_zero]
    have h1 : K + 1 + 8 ≤ 45 * (Nat.log 2 (D.length + 1) + 1) + 80 := by omega
    have h2 := Nat.mul_le_mul_left nK h1
    rw [hnK] at h2 ⊢
    omega

end MinCostFlow.SparseCore.Program
