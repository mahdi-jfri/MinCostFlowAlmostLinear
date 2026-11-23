module

public import MinCostFlow.Scaling.RoundedCostCalls
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Scanning the rounded residual edges

Cost scaling retains the residual graph's edge slots and replaces their
costs by rounded reduced costs. This procedure scans the residual records
in order and writes the exact rounded-instance records to a reserved array.
It allocates twelve scratch words per edge, preserves the remaining old
memory, and costs at most `1800*count+20` steps.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[source,potentials,count,B^8,B^9,power,C+1,records,heap]`. -/
def roundedEdgesBody (self record : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 2) (.const 0)) (.ret (.reg 8))
    (.call 9 record [.reg 0, .reg 1, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8] ;;
     .call 10 self [.bin .add (.reg 0) (.const 5), .reg 1, .bin .sub (.reg 2) (.const 1),
       .reg 3, .reg 4, .reg 5, .reg 6, .bin .add (.reg 7) (.const 5), .reg 9] ;;
     .ret (.reg 10))

/-- The scan entry and the proved single-record transformation. -/
def roundedEdgesModule (b : ℕ) : List Stmt :=
  roundedEdgesBody b (b+1) :: roundedRecordModule (b+1)

/-- Input records and potentials precede the reserved output array, which
precedes fresh scratch. Every remaining scalar operation has local budgets. -/
def roundedEdgesContract (w : ℕ) {I : Circulation} (s : CostState I) (C : ℕ)
    (es : List (Fin (I.m+I.m))) : Contract where
  pre args mem := ∃ a pot records heap,
    args = [a, pot, es.length, (I.m+I.m)^8, (I.m+I.m)^9, s.power, C+1, records, heap] ∧
    ListAt mem a (es.flatMap (I.residual s.flow).solverEdgeWords) ∧
    SignedTableAt mem pot s.potential ∧ a+5*es.length ≤ records ∧
    pot+2*I.n ≤ records ∧ records+5*es.length ≤ heap ∧
    (∀ e ∈ es, ∀ x ∈ (I.residual s.flow).solverEdgeWords e, x < 2 ^ w) ∧
    (∀ e ∈ es, (roundedCostContract w s C e).pre (roundedCostArguments s C e heap) mem) ∧
    ZeroFrom mem heap ∧ heap+12*es.length < 2 ^ w ∧ 12 < 2 ^ w
  post args mem out mem' := out = heapArg args+12*es.length ∧
    ListAt mem' (args.getD 7 0) (es.flatMap (s.roundedInstance C).solverEdgeWords) ∧
    ZeroFrom mem' out ∧
    ∀ x < heapArg args, x < args.getD 7 0 ∨ args.getD 7 0+5*es.length ≤ x → mem' x = mem x
  cost _ _ := 1800*es.length+20

/-- Rounding the entire edge array uses no random instructions. -/
theorem roundedEdgesModule_noRand (b : ℕ) :
    ∀ body ∈ roundedEdgesModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [roundedEdgesBody, Stmt.NoRand, and_self]
  · exact roundedRecordModule_noRand _ body hb

/-- The scan writes exactly the cost model's edge records in their original
order, with explicit linear time, exact scratch use, and the output frame. -/
theorem roundedEdges_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (roundedEdgesModule b)) {I : Circulation} (s : CostState I)
    (C : ℕ) (es : List (Fin (I.m+I.m))) :
    MeetsContract w p b (roundedEdgesContract w s C es) := by
  have hrecord := hasAt_tail hp
  induction es with
  | nil =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨a, pot, records, heap, rfl, _, _, _, _, _, _, _, hzero, hspace, hw⟩ := hpre
    have hh : heap < 2 ^ w := by simpa only [List.length_nil, Nat.mul_zero, Nat.add_zero] using hspace
    have hone : 1 < 2 ^ w := by omega
    apply runs_start_le
    unfold roundedEdgesBody
    wram_step
    · refine runs_ret_le (v := heap) (by eval_expr) ?_ ?_
      · change heap = heap+12*0 ∧ ListAt mem records [] ∧ ZeroFrom mem heap ∧
          ∀ x < heap, x < records ∨ records+5*0 ≤ x → mem x = mem x
        exact ⟨by omega, listAt_nil _ _, hzero, fun _ _ _ => rfl⟩
      · simp only [roundedEdgesContract, List.length_nil, Expr.size_bin, Expr.size_reg, Expr.size_const]; omega
    · simp at hcond
  | cons e es ih =>
    have hkE := roundedRecord_meetsContract (w := w) hrecord s C e
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨a, pot, records, heap, rfl, hat, htable, hsourceend, hpotend, hrecordsend,
      hinput, hscalar, hzero, hspace, hw⟩ := hpre
    obtain ⟨hhead, htail⟩ := listAt_append.mp hat
    change ListAt mem a ((I.residual s.flow).solverEdgeWords e) at hhead
    change ListAt mem (a+5) (es.flatMap (I.residual s.flow).solverEdgeWords) at htail
    have hB8 : (I.m+I.m)^8 < 2 ^ w := hwords _ (by simp)
    have hB9 : (I.m+I.m)^9 < 2 ^ w := hwords _ (by simp)
    have hpower : s.power < 2 ^ w := hwords _ (by simp)
    have hd : C+1 < 2 ^ w := hwords _ (by simp)
    have hlen : (e :: es).length < 2 ^ w := hwords _ (by simp)
    have ha : a < 2 ^ w := by simp only [List.length_cons] at hsourceend hrecordsend hspace; omega
    have ha5 : a+5 < 2 ^ w := by simp only [List.length_cons] at hsourceend hrecordsend hspace; omega
    have hpot : pot < 2 ^ w := by simp only [List.length_cons] at hrecordsend hspace; omega
    have hrecords : records < 2 ^ w := by simp only [List.length_cons] at hrecordsend hspace; omega
    have hrecords5 : records+5 < 2 ^ w := by simp only [List.length_cons] at hrecordsend hspace; omega
    have hheap : heap < 2 ^ w := by omega
    have hheap12 : heap+12 < 2 ^ w := by simp only [List.length_cons] at hspace; omega
    have hone : 1 < 2 ^ w := by omega
    have hfive : 5 < 2 ^ w := by omega
    apply runs_start_le
    unfold roundedEdgesBody
    wram_step
    · simp at hcond
    · refine runs_seq_call_le hkE
        (vs := [a, pot, (I.m+I.m)^8, (I.m+I.m)^9, s.power, C+1, records, heap])
        (by eval_expr) ?_ ?_ ?_
      · wram_words
      · refine ⟨a, pot, records, heap, rfl, hhead, htable, ?_, hpotend, ?_,
          hinput e List.mem_cons_self, hscalar e List.mem_cons_self⟩
        · simp only [List.length_cons] at hsourceend; omega
        · simp only [List.length_cons] at hrecordsend; omega
      · intro next memE posE hpostE
        obtain ⟨hnext, hrecordE, hzeroE, hframeE⟩ := hpostE
        change next = heap+12 at hnext
        change ListAt memE records ((s.roundedInstance C).solverEdgeWords e) at hrecordE
        change (∀ x < heap, x < records ∨ records+5 ≤ x → memE x = mem x) at hframeE
        have hsourceTail : a+5+5*es.length ≤ records := by
          simp only [List.length_cons] at hsourceend; omega
        have htailE : ListAt memE (a+5) (es.flatMap (I.residual s.flow).solverEdgeWords) := by
          apply htail.of_agree_below (h₀ := records)
          · rw [Circulation.solverEdgeRecords_length]
            exact hsourceTail
          · intro x hx
            exact hframeE x (by omega) (Or.inl hx)
        have htableE : SignedTableAt memE pot s.potential := by
          apply htable.of_agree_below hpotend
          intro x hx
          exact hframeE x (by omega) (Or.inl hx)
        have hnextword : next < 2 ^ w := by omega
        have hlenTail : es.length < 2 ^ w := by simp only [List.length_cons] at hlen; omega
        have hspaceTail : next+12*es.length < 2 ^ w := by
          simp only [List.length_cons] at hspace; omega
        refine runs_seq_call_le ih
          (vs := [a+5, pot, es.length, (I.m+I.m)^8, (I.m+I.m)^9, s.power, C+1, records+5, next])
          ?_ ?_ ?_ ?_
        · have heq : (e :: es).length-1 = es.length := rfl
          rw [← heq]; eval_expr
        · wram_words
        · refine ⟨a+5, pot, records+5, next, rfl, htailE, htableE, by omega, by omega,
            ?_, fun e' he' => hinput e' (List.mem_cons_of_mem e he'), ?_, hzeroE, hspaceTail, hw⟩
          · simp only [List.length_cons] at hrecordsend; omega
          · intro e' he'
            have hnonempty : 0 < es.length := List.length_pos_of_mem he'
            apply roundedCost_pre_transfer (hscalar e' (List.mem_cons_of_mem e he')) hzeroE
            omega
        · intro out memR posR hpostR
          obtain ⟨hout, htailR, hzeroR, hframeR⟩ := hpostR
          change out = next+12*es.length at hout
          change ListAt memR (records+5) (es.flatMap (s.roundedInstance C).solverEdgeWords) at htailR
          change (∀ x < next, x < records+5 ∨ records+5+5*es.length ≤ x → memR x = memE x) at hframeR
          have houtword : out < 2 ^ w := by omega
          refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
          · change out = heap+12*(e :: es).length ∧
              ListAt memR records ((e :: es).flatMap (s.roundedInstance C).solverEdgeWords) ∧
              ZeroFrom memR out ∧
              ∀ x < heap, x < records ∨ records+5*(e :: es).length ≤ x → memR x = mem x
            refine ⟨by simp only [List.length_cons]; omega, ?_, hzeroR, ?_⟩
            · rw [List.flatMap_cons]
              apply listAt_append.mpr
              refine ⟨?_, htailR⟩
              apply hrecordE.of_agree_below (h₀ := records+5)
              · exact le_rfl
              · intro x hx
                exact hframeR x (by omega) (Or.inl hx)
            · intro x hx hxout
              apply (hframeR x (by omega) ?_).trans (hframeE x hx ?_)
              · rcases hxout with hxout | hxout
                · exact Or.inl (by omega)
                · right; simp only [List.length_cons] at hxout; omega
              · rcases hxout with hxout | hxout
                · exact Or.inl hxout
                · right; simp only [List.length_cons] at hxout; omega
          · simp only [roundedEdgesContract, roundedRecordContract, List.length_cons,
              argsSize_cons, argsSize_nil, Expr.size_bin, Expr.size_reg, Expr.size_const]; omega

end MinCostFlow.Scaling.Machine
