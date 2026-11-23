module

public import MinCostFlow.Scaling.SignedCompareProgram
public import MinCostFlow.Scaling.InputLayout
import WordRAM.Tactic
import WordRAM.Memory
import WordRAM.Entry

/-!
# Checking lower and upper capacities

The general-flow reduction in Lemma C.1 of Chen et al., arXiv:2203.00671v2,
first rejects an edge whose lower capacity exceeds its upper capacity.
This procedure scans the statement's eight-word edge records. It invokes
the signed comparison procedure and stops at the first inconsistent pair.
It changes no memory and uses at most `200*edges.length+20` steps.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[firstEdge,edgeCount]`. -/
def capacityCheckBody (self compare : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 1))
    (.call 2 compare [.load (.bin .add (.reg 0) (.const 2)),
      .load (.bin .add (.reg 0) (.const 3)),
      .load (.bin .add (.reg 0) (.const 4)),
      .load (.bin .add (.reg 0) (.const 5))] ;;
    .cond (.bin .eq (.reg 2) (.const 0)) (.ret (.const 0))
      (.call 3 self [.bin .add (.reg 0) (.const 8),
        .bin .sub (.reg 1) (.const 1)] ;; .ret (.reg 3)))

/-- Recursive capacity checking and signed comparison. -/
def capacityCheckModule (b : ℕ) : List Stmt :=
  [capacityCheckBody b (b + 1), signedCompareBody]

/-- The scan returns the indicator of every lower capacity being at most
its upper capacity. -/
def capacityCheckContract (w : ℕ) (edges : List Edge) : Contract where
  pre args mem := ∃ a, args = [a, edges.length] ∧
    ListAt mem a (edges.flatMap Edge.encode) ∧
    a + 8 * edges.length < 2 ^ w ∧ 8 < 2 ^ w ∧
    ∀ x ∈ edges.flatMap Edge.encode, x < 2 ^ w
  post _ mem out mem' := mem' = mem ∧
    out = if ∀ e ∈ edges, e.lower ≤ e.upper then 1 else 0
  cost _ _ := 200 * edges.length + 20

/-- Neither capacity-checking procedure reads random bits. -/
theorem capacityCheckModule_noRand (b : ℕ) :
    ∀ body ∈ capacityCheckModule b, body.NoRand := by
  simp only [capacityCheckModule, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨by simp only [capacityCheckBody, Stmt.NoRand, and_self], signedCompareBody_noRand⟩

/-- The machine scans exactly the capacity inequalities in the general-flow
reduction, with unchanged memory and linear cost. -/
theorem capacityCheck_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (capacityCheckModule b)) (edges : List Edge) :
    MeetsContract w p b (capacityCheckContract w edges) := by
  have hcompare : p.HasAt (b + 1) signedCompareModule := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [capacityCheckModule, signedCompareModule, List.getElem_cons_succ,
      List.getElem_cons_zero, Nat.add_zero] using hp 1 (by simp [capacityCheckModule])
  induction edges with
  | nil =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨a, rfl, _, _, hw, _⟩ := hpre
    have hone : 1 < 2 ^ w := by omega
    apply runs_start_le
    unfold capacityCheckBody
    wram_step
    · refine runs_ret_le (by eval_expr) ?_ ?_
      · change mem = mem ∧ 1 = if ∀ e ∈ ([] : List Edge), e.lower ≤ e.upper then 1 else 0
        simp
      · simp only [capacityCheckContract, List.length_nil, Expr.size_bin,
          Expr.size_reg, Expr.size_const]
        omega
    · simp at hcond
  | cons e edges ih =>
    have hk := signedCompare_meetsContract (w := w) hcompare e.lower e.upper
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨a, rfl, hat, hend, hw, hinputwords⟩ := hpre
    have hone : 1 < 2 ^ w := by omega
    have ha : a < 2 ^ w := hwords _ (List.mem_cons_self)
    have hl : (e :: edges).length < 2 ^ w :=
      hwords _ (List.mem_cons_of_mem _ (List.mem_cons_self))
    have hsplit := listAt_append.mp hat
    change ListAt mem a e.encode ∧ ListAt mem (a + e.encode.length) (edges.flatMap Edge.encode) at hsplit
    have htail : ListAt mem (a + 8) (edges.flatMap Edge.encode) := by
      simpa only [edge_encode_length] using hsplit.2
    have hls : mem (a + 2) = if e.lower < 0 then 1 else 0 := by
      simpa only [Edge.encode, encodeInt, List.cons_append, List.nil_append,
        List.getElem_cons_succ, List.getElem_cons_zero] using hsplit.1 2 (by rw [edge_encode_length]; decide)
    have hlm : mem (a + 3) = e.lower.natAbs := by
      simpa only [Edge.encode, encodeInt, List.cons_append, List.nil_append,
        List.getElem_cons_succ, List.getElem_cons_zero] using hsplit.1 3 (by rw [edge_encode_length]; decide)
    have hus : mem (a + 4) = if e.upper < 0 then 1 else 0 := by
      simpa only [Edge.encode, encodeInt, List.cons_append, List.nil_append,
        List.getElem_cons_succ, List.getElem_cons_zero] using hsplit.1 4 (by rw [edge_encode_length]; decide)
    have hum : mem (a + 5) = e.upper.natAbs := by
      simpa only [Edge.encode, encodeInt, List.cons_append, List.nil_append,
        List.getElem_cons_succ, List.getElem_cons_zero] using hsplit.1 5 (by rw [edge_encode_length]; decide)
    have hcomparewords : ∀ x ∈ [if e.lower < 0 then 1 else 0, e.lower.natAbs,
        if e.upper < 0 then 1 else 0, e.upper.natAbs], x < 2 ^ w := by
      intro x hx
      apply hinputwords x
      apply List.mem_append_left
      simp only [Edge.encode, encodeInt, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl | rfl <;> tauto
    have htailwords : ∀ x ∈ edges.flatMap Edge.encode, x < 2 ^ w := by
      intro x hx
      exact hinputwords x (List.mem_append_right _ hx)
    have ha8 : a + 8 < 2 ^ w := by
      simp only [List.length_cons, Nat.mul_succ] at hend
      omega
    have ha2 : a + 2 < 2 ^ w := by omega
    have ha3 : a + 3 < 2 ^ w := by omega
    have ha4 : a + 4 < 2 ^ w := by omega
    have ha5 : a + 5 < 2 ^ w := by omega
    have hl' : (e :: edges).length - 1 = edges.length := rfl
    apply runs_start_le
    unfold capacityCheckBody
    wram_step
    · simp at hcond
    · refine runs_seq_call_le hk
        (vs := [if e.lower < 0 then 1 else 0, e.lower.natAbs,
          if e.upper < 0 then 1 else 0, e.upper.natAbs]) (by eval_expr) hcomparewords ⟨rfl, hone⟩ ?_
      intro compared memC posC hpostC
      obtain ⟨hmem, hcompared⟩ := hpostC
      change memC = mem at hmem
      subst memC
      change compared = if e.lower ≤ e.upper then 1 else 0 at hcompared
      have hcword : compared < 2 ^ w := by split_ifs at hcompared <;> omega
      wram_step
      · have hz : compared = 0 := by simpa [startState] using hcond
        have hbad : ¬ e.lower ≤ e.upper := by
          intro hg
          simp only [hg, ↓reduceIte] at hcompared
          omega
        refine runs_ret_le (by eval_expr) ?_ ?_
        · refine ⟨rfl, ?_⟩
          simp only [List.forall_mem_cons, hbad, false_and, ↓reduceIte, Outcome.value]
        · simp only [capacityCheckContract, signedCompareContract, Expr.size_bin,
            Expr.size_load, Expr.size_reg, Expr.size_const, argsSize_cons, argsSize_nil]
          omega
      · have hnz : compared ≠ 0 := by simpa [startState] using hcond
        have hgood : e.lower ≤ e.upper := by
          by_contra hn
          simp only [hn, ↓reduceIte] at hcompared
          exact hnz hcompared
        refine runs_seq_call_le ih (vs := [a + 8, edges.length]) ?_ ?_ ?_ ?_
        · rw [← hl']; eval_expr
        · wram_words
        · exact ⟨a + 8, rfl, htail, by simp only [List.length_cons, Nat.mul_succ] at hend; omega,
            hw, htailwords⟩
        · intro out memR posR hpostR
          obtain ⟨hmemR, hout⟩ := hpostR
          change memR = mem at hmemR
          subst memR
          change out = if ∀ e ∈ edges, e.lower ≤ e.upper then 1 else 0 at hout
          have houtword : out < 2 ^ w := by split_ifs at hout <;> omega
          refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
          · refine ⟨rfl, ?_⟩
            simpa only [List.forall_mem_cons, hgood, true_and, Outcome.value] using hout
          · simp only [capacityCheckContract, signedCompareContract, Expr.size_bin,
              Expr.size_load, Expr.size_reg, Expr.size_const, argsSize_cons, argsSize_nil,
              List.length_cons]
            omega

/-- The list scan tests exactly the indexed condition in
`FlowReduction.reduceToCirculation`. -/
theorem instance_capacity_order_iff (I : Instance) :
    (∀ e : Fin I.m, (I.edge e).lower ≤ (I.edge e).upper) ↔
      ∀ e ∈ I.edges, e.lower ≤ e.upper := by
  constructor
  · intro h e he
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
    exact h ⟨i, hi⟩
  · intro h e
    exact h (I.edge e) (List.getElem_mem e.isLt)

/-- A concrete stored edge list satisfies all scan preconditions at a
sufficiently large width. -/
theorem exists_capacityCheck_pre (edges : List Edge) :
    ∃ w, (∀ a ∈ [0, edges.length], a < 2 ^ w) ∧
      (capacityCheckContract w edges).pre [0, edges.length]
        (initMem (edges.flatMap Edge.encode)) := by
  let input := edges.flatMap Edge.encode ++ [8 * edges.length + 10]
  let w := wordSize 1 input
  have hlarge : 8 * edges.length + 10 < 2 ^ w :=
    lt_two_pow_wordSize_of_mem (by decide)
      (List.mem_append_right _ (List.mem_cons_self))
  refine ⟨w, ?_, 0, rfl, listAt_initMem _, by omega, by omega, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> omega
  · intro x hx
    exact lt_two_pow_wordSize_of_mem (by decide) (List.mem_append_left _ hx)

end MinCostFlow.Scaling.Machine
