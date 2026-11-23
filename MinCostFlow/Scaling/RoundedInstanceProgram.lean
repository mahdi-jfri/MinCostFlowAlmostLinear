module

public import MinCostFlow.Scaling.RoundedEdgesProgram
public import MinCostFlow.Scaling.WordPairProgram
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Constructing the complete rounded residual instance

The cost-scaling loop passes a residual graph and its potential table to
cost rounding. This procedure writes the unchanged header, reserves the
edge-record array, and runs the rounded-edge scan with fresh scratch after
that array. Its graph output is exactly `CostState.roundedInstance` in the
shared circulation layout. It costs at most `3600*m+300` steps and uses
`2+34*m` fresh words, including scratch.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[residual,potentials,B^8,B^9,power,C+1,heap]`. -/
def roundedInstanceBody (header scan : ℕ) : Stmt :=
  .assign 7 (.load (.reg 0)) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 9 header [.reg 7, .reg 8, .reg 6] ;;
  .assign 10 (.bin .add (.reg 9) (.bin .mul (.const 5) (.reg 8))) ;;
  .call 11 scan [.bin .add (.reg 0) (.const 2), .reg 1, .reg 8,
    .reg 2, .reg 3, .reg 4, .reg 5, .reg 9, .reg 10] ;;
  .ret (.reg 11)

/-- Complete instance construction, header writing, and edge rounding. -/
def roundedInstanceModule (b : ℕ) : List Stmt :=
  roundedInstanceBody (b+1) (b+2) :: wordPairBody :: roundedEdgesModule (b+2)

/-- Both input arrays precede the fresh output. Scalar preconditions supply
only the arithmetic budgets for the finite residual-edge set. -/
def roundedInstanceContract (w : ℕ) {I : Circulation} (s : CostState I) (C : ℕ) : Contract :=
  let R := I.residual s.flow
  let H := heapContract w
    (fun args mem => ∃ a pot heap,
      args = [a, pot, (I.m+I.m)^8, (I.m+I.m)^9, s.power, C+1, heap] ∧
      ListAt mem a R.solverWords ∧ SignedTableAt mem pot s.potential ∧
      a+R.solverWords.length ≤ heap ∧ pot+2*I.n ≤ heap ∧
      (∀ x ∈ R.solverWords, x < 2 ^ w) ∧
      (∀ e, (roundedCostContract w s C e).pre (roundedCostArguments s C e heap) mem) ∧
      12 < 2 ^ w)
    (fun args _ mem' => ListAt mem' (heapArg args) (s.roundedInstance C).solverWords)
    (fun _ _ => 1800*(I.m+I.m)+300) (fun _ _ => 2+17*(I.m+I.m))
  { H with post := fun args mem out mem' => H.post args mem out mem' ∧
      out = heapArg args+2+17*(I.m+I.m) }

/-- The rounded graph constructor and all helpers use no random instructions. -/
theorem roundedInstanceModule_noRand (b : ℕ) :
    ∀ body ∈ roundedInstanceModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [roundedInstanceBody, Stmt.NoRand, and_self]
  · rcases List.mem_cons.mp hb with rfl | hb
    · exact wordPairBody_noRand
    · exact roundedEdgesModule_noRand _ body hb

/-- The complete graph constructor computes exactly the cost-scaling
model's rounded residual instance, with explicit linear cost and space. -/
theorem roundedInstance_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (roundedInstanceModule b)) {I : Circulation} (s : CostState I) (C : ℕ) :
    MeetsContract w p b (roundedInstanceContract w s C) := by
  have htail := hasAt_tail hp
  have hheader : p.HasAt (b+1) wordPairModule := by
    intro i hi
    have hi0 : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [wordPairModule, List.getElem_cons_zero, Nat.add_zero] using htail.head
  have hscan : p.HasAt (b+2) (roundedEdgesModule (b+2)) := by
    simpa only [Nat.add_assoc] using hasAt_tail htail
  let R := I.residual s.flow
  let M := I.m+I.m
  have hkH := wordPair_meetsContract (w := w) hheader
  have hkS := roundedEdges_meetsContract (w := w) hscan s C (List.finRange M)
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a, pot, heap, rfl, hat, htable, hend, hpotend, hinput, hscalar, hw⟩, hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap+(2+17*M) < 2 ^ w at hspace
  have hsize : R.solverWords.length = 2+5*M := R.solverWords_length
  change a+R.solverWords.length ≤ heap at hend
  rw [hsize] at hend
  have hN : mem a = I.n := by
    simpa only [Circulation.solverWords, List.getElem_cons_zero, Nat.add_zero] using
      hat 0 (by change 0 < R.solverWords.length; rw [hsize]; omega)
  have hM : mem (a+1) = M := by
    simpa only [Circulation.solverWords, List.getElem_cons_succ, List.getElem_cons_zero] using
      hat 1 (by change 1 < R.solverWords.length; rw [hsize]; omega)
  have hedge : ListAt mem (a+2) ((List.finRange M).flatMap R.solverEdgeWords) := by
    have h := (listAt_cons.mp (listAt_cons.mp hat).2).2
    simpa only [Nat.add_assoc] using h
  have hrecordWords : ∀ e ∈ List.finRange M, ∀ x ∈ R.solverEdgeWords e, x < 2 ^ w := by
    intro e _ x hx
    exact hinput x (Circulation.solverEdgeWord_mem R e hx)
  have hn : I.n < 2 ^ w := hinput _ List.mem_cons_self
  have hm : M < 2 ^ w := hinput _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hB8 : (I.m+I.m)^8 < 2 ^ w := hwords _ (by simp)
  have hB9 : (I.m+I.m)^9 < 2 ^ w := hwords _ (by simp)
  have hpower : s.power < 2 ^ w := hwords _ (by simp)
  have hd : C+1 < 2 ^ w := hwords _ (by simp)
  have ha : a < 2 ^ w := by omega
  have ha1 : a+1 < 2 ^ w := by omega
  have ha2 : a+2 < 2 ^ w := by omega
  have hpot : pot < 2 ^ w := by omega
  have hh : heap < 2 ^ w := by omega
  have hh2 : heap+2 < 2 ^ w := by omega
  have hfiveM : 5*M < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have htwo : 2 < 2 ^ w := by omega
  have hfive : 5 < 2 ^ w := by omega
  apply runs_start_le
  unfold roundedInstanceBody
  refine runs_seq_assign_le (v := I.n) (by eval_expr) ?_
  refine runs_seq_assign_le (v := M) (by eval_expr) ?_
  refine runs_seq_call_le hkH (vs := [I.n, M, heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨I.n, M, heap, rfl⟩, hzero, hh2⟩
  · intro records memH posH hpostH
    obtain ⟨⟨_, _, hframeH, hzeroH, hheaderH⟩, hrecords⟩ := hpostH
    change records = heap+2 at hrecords
    change (∀ x < heap, memH x = mem x) at hframeH
    change ZeroFrom memH records at hzeroH
    change ListAt memH heap [I.n, M] at hheaderH
    have hedgeH : ListAt memH (a+2) ((List.finRange M).flatMap R.solverEdgeWords) := by
      apply hedge.of_agree_below (h₀ := heap)
      · rw [Circulation.solverEdgeRecords_length, List.length_finRange]
        omega
      · exact hframeH
    have htableH : SignedTableAt memH pot s.potential := htable.of_agree_below hpotend hframeH
    have hrecordsWord : records < 2 ^ w := by omega
    have hscratchWord : records+5*M < 2 ^ w := by omega
    have hzeroScratch : ZeroFrom memH (records+5*M) := by
      intro x hx
      exact hzeroH x (by omega)
    refine runs_seq_assign_le (v := records+5*M) (by eval_expr) ?_
    refine runs_seq_call_le hkS
      (vs := [a+2, pot, M, (I.m+I.m)^8, (I.m+I.m)^9, s.power, C+1, records, records+5*M])
      (by eval_expr) ?_ ?_ ?_
    · wram_words
    · refine ⟨a+2, pot, records, records+5*M, by simp only [List.length_finRange], hedgeH, htableH, ?_, by omega,
        ?_, hrecordWords, ?_, hzeroScratch, ?_, hw⟩
      · rw [List.length_finRange]; omega
      · rw [List.length_finRange]
      · intro e he
        apply roundedCost_pre_transfer (hscalar e) hzeroScratch
        have hMpos : 0 < M := by have h := e.isLt; omega
        omega
      · rw [List.length_finRange]; omega
    · intro out memS posS hpostS
      obtain ⟨hout, hrecordsS, hzeroS, hframeS⟩ := hpostS
      change out = records+5*M+12*(List.finRange M).length at hout
      rw [List.length_finRange] at hout
      change ListAt memS records ((List.finRange M).flatMap (s.roundedInstance C).solverEdgeWords) at hrecordsS
      change (∀ x < records+5*M, x < records ∨ records+5*(List.finRange M).length ≤ x → memS x = memH x) at hframeS
      have houtWord : out < 2 ^ w := by omega
      refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
      · change (heap ≤ out ∧ out ≤ heap+(2+17*M) ∧ (∀ x < heap, memS x = mem x) ∧
          ZeroFrom memS out ∧ ListAt memS heap (s.roundedInstance C).solverWords) ∧
          out = heap+2+17*M
        refine ⟨⟨by omega, by omega, ?_, hzeroS, ?_⟩, by omega⟩
        · intro x hx
          exact (hframeS x (by omega) (Or.inl (by omega))).trans (hframeH x hx)
        · have hheaderS : ListAt memS heap [I.n, M] := by
            apply hheaderH.of_agree_below (h₀ := records)
            · change heap+2 ≤ records; omega
            · intro x hx
              exact hframeS x (by omega) (Or.inl hx)
          change ListAt memS heap ([I.n, M] ++ ((List.finRange M).flatMap (s.roundedInstance C).solverEdgeWords))
          apply listAt_append.mpr
          exact ⟨hheaderS, by simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, hrecords] using hrecordsS⟩
      · simp only [roundedInstanceContract, heapContract, wordPairContract, roundedEdgesContract,
          List.length_finRange, argsSize_cons, argsSize_nil, Expr.size_bin, Expr.size_load,
          Expr.size_reg, Expr.size_const]
        change _ ≤ 1800*M+300
        omega

end MinCostFlow.Scaling.Machine
