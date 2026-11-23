module

public import WordRAM.Layout
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Scanning endpoint labels and demand magnitudes

The initial isolated-demand check in the reduction of Lemma C.1 of
Chen et al., arXiv:2203.00671v2, accepts a vertex when its endpoint label is
positive or its demand is zero. This read-only scan checks a contiguous
label table against the magnitude cells of canonical signed demands.
It returns the exact indicator, uses no random instruction, and costs at
most `100*vertexCount+20` steps.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Advance one label cell and one two-word signed demand record. -/
def isolatedScanContinue (self : ℕ) : Stmt :=
  .call 3 self [.bin .add (.reg 0) (.const 1), .bin .add (.reg 1) (.const 2),
    .bin .sub (.reg 2) (.const 1)] ;; .ret (.reg 3)

/-- Arguments `[labels,demandMagnitudes,vertexCount]`. -/
def isolatedScanBody (self : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 2) (.const 0)) (.ret (.const 1))
    (.cond (.bin .eq (.load (.reg 0)) (.const 0))
      (.cond (.bin .eq (.load (.reg 1)) (.const 0))
        (isolatedScanContinue self) (.ret (.const 0)))
      (isolatedScanContinue self))

/-- The read-only recursive scan occupies one procedure slot. -/
def isolatedScanModule (b : ℕ) : List Stmt := [isolatedScanBody b]

/-- Each row contains an endpoint label and an unsigned demand magnitude.
The two input tables have respective strides one and two. -/
def isolatedScanContract (w : ℕ) (rows : List (ℕ × ℕ)) : Contract where
  pre args mem := ∃ a b, args = [a, b, rows.length] ∧
    (∀ i (hi : i < rows.length), mem (a + i) = (rows[i]'hi).1) ∧
    (∀ i (hi : i < rows.length), mem (b + 2 * i) = (rows[i]'hi).2) ∧
    a + rows.length < 2 ^ w ∧ b + 2 * rows.length < 2 ^ w ∧
    (∀ r ∈ rows, r.1 < 2 ^ w ∧ r.2 < 2 ^ w) ∧ 2 < 2 ^ w
  post _ mem out mem' := mem' = mem ∧
    out = if ∀ r ∈ rows, 0 < r.1 ∨ r.2 = 0 then 1 else 0
  cost _ _ := 100 * rows.length + 20

/-- The scan never reads random bits. -/
theorem isolatedScanBody_noRand (self : ℕ) : (isolatedScanBody self).NoRand := by
  simp only [isolatedScanBody, isolatedScanContinue, Stmt.NoRand, and_self]

/-- The read-only machine scan computes exactly the isolated-demand test
on its two tables, with linear cost on every tape. -/
theorem isolatedScan_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (isolatedScanModule b)) (rows : List (ℕ × ℕ)) :
    MeetsContract w p b (isolatedScanContract w rows) := by
  induction rows with
  | nil =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨a, b', rfl, _, _, _, _, _, hw⟩ := hpre
    have hone : 1 < 2 ^ w := by omega
    apply runs_start_le
    unfold isolatedScanBody
    wram_step
    · refine runs_ret_le (by eval_expr) ?_ ?_
      · change mem = mem ∧ 1 = if ∀ r ∈ ([] : List (ℕ × ℕ)), 0 < r.1 ∨ r.2 = 0 then 1 else 0
        simp
      · simp only [isolatedScanContract, List.length_nil, Expr.size_bin, Expr.size_reg, Expr.size_const]
        omega
    · simp at hcond
  | cons r rows ih =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨a, b', rfl, hlabels, hmags, haend, hbend, hinput, hw⟩ := hpre
    have hl : mem a = r.1 := by
      have hh := hlabels 0 (by simp)
      change mem (a + 0) = r.1 at hh
      simpa only [Nat.add_zero] using hh
    have hm : mem b' = r.2 := by
      have hh := hmags 0 (by simp)
      change mem (b' + 2 * 0) = r.2 at hh
      simpa only [Nat.mul_zero, Nat.add_zero] using hh
    have hltail : ∀ i (hi : i < rows.length), mem (a + 1 + i) = (rows[i]'hi).1 := by
      intro i hi
      have hh := hlabels (i + 1) (by simp only [List.length_cons]; omega)
      change mem (a + (i + 1)) = (rows[i]'hi).1 at hh
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
    have hmtail : ∀ i (hi : i < rows.length), mem (b' + 2 + 2 * i) = (rows[i]'hi).2 := by
      intro i hi
      have hh := hmags (i + 1) (by simp only [List.length_cons]; omega)
      change mem (b' + 2 * (i + 1)) = (rows[i]'hi).2 at hh
      simpa only [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
    have ha : a < 2 ^ w := by simp only [List.length_cons] at haend; omega
    have ha1 : a + 1 < 2 ^ w := by simp only [List.length_cons] at haend; omega
    have hb : b' < 2 ^ w := by simp only [List.length_cons, Nat.mul_succ] at hbend; omega
    have hb2 : b' + 2 < 2 ^ w := by simp only [List.length_cons, Nat.mul_succ] at hbend; omega
    have hcount : (r :: rows).length < 2 ^ w := hwords _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
    have htailcount : rows.length < 2 ^ w := lt_trans (Nat.lt_succ_self _) hcount
    have hlabelword := (hinput r (List.mem_cons_self)).1
    have hmagword := (hinput r (List.mem_cons_self)).2
    have hone : 1 < 2 ^ w := by omega
    apply runs_start_le
    unfold isolatedScanBody
    wram_step
    · simp at hcond
    · wram_step
      · have hz : r.1 = 0 := by simpa [startState, hl, hm] using hcond
        wram_step
        · have hmz : r.2 = 0 := by simpa [startState, hl, hm] using hcond
          have hgood : 0 < r.1 ∨ r.2 = 0 := Or.inr hmz
          unfold isolatedScanContinue
          refine runs_seq_call_le ih (vs := [a + 1, b' + 2, rows.length]) ?_ ?_ ?_ ?_
          · have heq : (r :: rows).length - 1 = rows.length := rfl
            rw [← heq]; eval_expr
          · wram_words
          · exact ⟨a + 1, b' + 2, rfl, hltail, hmtail,
              by simp only [List.length_cons] at haend; omega,
              by simp only [List.length_cons, Nat.mul_succ] at hbend; omega,
              (fun r' hr' => hinput r' (List.mem_cons_of_mem r hr')), hw⟩
          · intro out mem' pos' hpost
            obtain ⟨hmem, hout⟩ := hpost
            change mem' = mem at hmem
            subst mem'
            change out = if ∀ r ∈ rows, 0 < r.1 ∨ r.2 = 0 then 1 else 0 at hout
            have houtword : out < 2 ^ w := by split_ifs at hout <;> omega
            refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
            · refine ⟨rfl, ?_⟩
              simpa only [List.forall_mem_cons, hgood, true_and, Outcome.value] using hout
            · simp only [isolatedScanContract, List.length_cons, argsSize_cons, argsSize_nil,
                Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]
              omega
        · have hmnz : r.2 ≠ 0 := by simpa [startState, hl, hm] using hcond
          have hbad : ¬ (0 < r.1 ∨ r.2 = 0) := by omega
          refine runs_ret_le (by eval_expr) ?_ ?_
          · refine ⟨rfl, ?_⟩
            simp only [List.forall_mem_cons, hbad, false_and, ↓reduceIte, Outcome.value]
          · simp only [isolatedScanContract, List.length_cons,
              Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]
            omega
      · have hnz : r.1 ≠ 0 := by simpa [startState, hl, hm] using hcond
        have hgood : 0 < r.1 ∨ r.2 = 0 := Or.inl (Nat.pos_of_ne_zero hnz)
        unfold isolatedScanContinue
        refine runs_seq_call_le ih (vs := [a + 1, b' + 2, rows.length]) ?_ ?_ ?_ ?_
        · have heq : (r :: rows).length - 1 = rows.length := rfl
          rw [← heq]; eval_expr
        · wram_words
        · exact ⟨a + 1, b' + 2, rfl, hltail, hmtail,
            by simp only [List.length_cons] at haend; omega,
            by simp only [List.length_cons, Nat.mul_succ] at hbend; omega,
            (fun r' hr' => hinput r' (List.mem_cons_of_mem r hr')), hw⟩
        · intro out mem' pos' hpost
          obtain ⟨hmem, hout⟩ := hpost
          change mem' = mem at hmem
          subst mem'
          change out = if ∀ r ∈ rows, 0 < r.1 ∨ r.2 = 0 then 1 else 0 at hout
          have houtword : out < 2 ^ w := by split_ifs at hout <;> omega
          refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
          · refine ⟨rfl, ?_⟩
            simpa only [List.forall_mem_cons, hgood, true_and, Outcome.value] using hout
          · simp only [isolatedScanContract, List.length_cons, argsSize_cons, argsSize_nil,
              Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]
            omega

/-- Arbitrary rows have a concrete pair of source tables satisfying all
scan premises together at a sufficiently large width. -/
theorem exists_isolatedScan_pre (rows : List (ℕ × ℕ)) :
    ∃ w mem, (∀ x ∈ [0, rows.length, rows.length], x < 2 ^ w) ∧
      (isolatedScanContract w rows).pre [0, rows.length, rows.length] mem := by
  let input := (rows.flatMap fun r => [r.1, r.2]) ++ [4 * rows.length + 10]
  let w := wordSize 1 input
  let mem := fun q => if q < rows.length then (rows.getD q (0, 0)).1
    else (rows.getD ((q - rows.length) / 2) (0, 0)).2
  have hlarge : 4 * rows.length + 10 < 2 ^ w :=
    lt_two_pow_wordSize_of_mem (by decide) (List.mem_append_right _ (List.mem_cons_self))
  refine ⟨w, mem, ?_, 0, rows.length, rfl, ?_, ?_, by omega, by omega, ?_, by omega⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> omega
  · intro i hi
    simp only [Nat.zero_add, mem, hi, ↓reduceIte, List.getD_eq_getElem _ _ hi]
  · intro i hi
    dsimp only [mem]
    have hn : ¬rows.length + 2 * i < rows.length := by omega
    have he : (rows.length + 2 * i - rows.length) / 2 = i := by omega
    rw [ite_eq_right hn, he, List.getD_eq_getElem _ _ hi]
  · intro r hr
    constructor
    · exact lt_two_pow_wordSize_of_mem (by decide)
        (List.mem_append_left _ (List.mem_flatMap.mpr ⟨r, hr, by simp⟩))
    · exact lt_two_pow_wordSize_of_mem (by decide)
        (List.mem_append_left _ (List.mem_flatMap.mpr ⟨r, hr, by simp⟩))

end MinCostFlow.Scaling.Machine
