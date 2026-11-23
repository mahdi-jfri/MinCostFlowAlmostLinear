module

public import MinCostFlow.Scaling.PositiveInstanceEdgesProgram
public import MinCostFlow.Scaling.WordPairProgram
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Entry
import WordRAM.LinkDefs
import Mathlib.Tactic.NormNum

/-!
# Constructing the positive-capacity solver input

The zero-capacity adapter adds one isolated vertex and retains every edge
slot. This procedure writes the new header and replaces inactive records
by unit-capacity zero-cost loops. The output is exactly `positiveInstance`
in the solver layout. It allocates `2+5*m` words and costs at most
`300*m+200` steps. Multiplier two on the source circulation encoding fits
all its words and allocation.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[circulation,heap]`. -/
def positiveInstanceBody (header scan : ℕ) : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 4 header [.bin .add (.reg 2) (.const 1), .reg 3, .reg 1] ;;
  .call 5 scan [.bin .add (.reg 0) (.const 2), .reg 3, .reg 2, .reg 4] ;;
  .ret (.reg 5)

/-- Header construction followed by the positive-capacity edge scan. -/
def positiveInstanceModule (b : ℕ) : List Stmt :=
  positiveInstanceBody (b+1) (b+2) :: wordPairBody :: positiveInstanceEdgesModule (b+2)

/-- The input circulation precedes the fresh output, and the additional
vertex index fits along with the original words. -/
def positiveInstanceContract (w : ℕ) (J : Circulation) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a heap, args = [a, heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length ≤ heap ∧ (∀ x ∈ J.solverWords, x < 2 ^ w) ∧
      J.n+1 < 2 ^ w ∧ 8 < 2 ^ w)
    (fun args _ mem' => ListAt mem' (heapArg args) J.positiveInstance.solverWords)
    (fun _ _ => 300*J.m+200) (fun _ _ => 2+5*J.m)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧
      out = heapArg args+2+5*J.m }

/-- Building the solver adapter's graph is deterministic. -/
theorem positiveInstanceModule_noRand (b : ℕ) :
    ∀ body ∈ positiveInstanceModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [positiveInstanceBody, Stmt.NoRand, and_self]
  · rcases List.mem_cons.mp hb with rfl | hb
    · exact wordPairBody_noRand
    · exact positiveInstanceEdgesModule_noRand _ body hb

/-- The constructor computes the model's exact positive-capacity solver
input with linear cost, exact allocation, and the fresh-heap frame. -/
theorem positiveInstance_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (positiveInstanceModule b)) (J : Circulation) :
    MeetsContract w p b (positiveInstanceContract w J) := by
  have htail := hasAt_tail hp
  have hheader : p.HasAt (b+1) wordPairModule := by
    intro i hi
    have hi0 : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [wordPairModule, List.getElem_cons_zero, Nat.add_zero] using htail.head
  have hscan : p.HasAt (b+2) (positiveInstanceEdgesModule (b+2)) := by
    simpa only [Nat.add_assoc] using hasAt_tail htail
  have hkH := wordPair_meetsContract (w := w) hheader
  have hkS := positiveInstanceEdges_meetsContract (w := w) hscan J (List.finRange J.m)
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a, heap, rfl, hat, hend, hinput, hn1, hw⟩, hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap+(2+5*J.m) < 2 ^ w at hspace
  have hsize := J.solverWords_length
  have hN : mem a = J.n := by
    simpa only [Circulation.solverWords, List.getElem_cons_zero, Nat.add_zero] using
      hat 0 (by rw [hsize]; omega)
  have hM : mem (a+1) = J.m := by
    simpa only [Circulation.solverWords, List.getElem_cons_succ, List.getElem_cons_zero] using
      hat 1 (by rw [hsize]; omega)
  have hedge : ListAt mem (a+2) ((List.finRange J.m).flatMap J.solverEdgeWords) := by
    have h := (listAt_cons.mp (listAt_cons.mp hat).2).2
    simpa only [Nat.add_assoc] using h
  have hrecordWords : ∀ e ∈ List.finRange J.m, ∀ x ∈ J.solverEdgeWords e, x < 2 ^ w := by
    intro e _ x hx
    exact hinput x (Circulation.solverEdgeWord_mem J e hx)
  have hn : J.n < 2 ^ w := by omega
  have hm : J.m < 2 ^ w := hinput _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have ha : a < 2 ^ w := by rw [hsize] at hend; omega
  have ha1 : a+1 < 2 ^ w := by rw [hsize] at hend; omega
  have ha2 : a+2 < 2 ^ w := by rw [hsize] at hend; omega
  have hh : heap < 2 ^ w := by omega
  have hh2 : heap+2 < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have htwo : 2 < 2 ^ w := by omega
  apply runs_start_le
  unfold positiveInstanceBody
  refine runs_seq_assign_le (v := J.n) (by eval_expr) ?_
  refine runs_seq_assign_le (v := J.m) (by eval_expr) ?_
  refine runs_seq_call_le hkH (vs := [J.n+1, J.m, heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨J.n+1, J.m, heap, rfl⟩, hzero, hh2⟩
  · intro records memH posH hpostH
    obtain ⟨⟨_, _, hframeH, hzeroH, hheaderH⟩, hrecords⟩ := hpostH
    change records = heap+2 at hrecords
    change (∀ x < heap, memH x = mem x) at hframeH
    change ZeroFrom memH records at hzeroH
    change ListAt memH heap [J.n+1, J.m] at hheaderH
    have hedgeH : ListAt memH (a+2) ((List.finRange J.m).flatMap J.solverEdgeWords) := by
      apply hedge.of_agree_below (h₀ := heap)
      · rw [Circulation.solverEdgeRecords_length, List.length_finRange]
        rw [hsize] at hend
        omega
      · exact hframeH
    have hrecordsWord : records < 2 ^ w := by omega
    refine runs_seq_call_le hkS (vs := [a+2, J.m, J.n, records]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · refine ⟨⟨a+2, records, by simp only [List.length_finRange], hedgeH, ?_, hrecordWords, hw⟩,
        hzeroH, ?_⟩
      · rw [List.length_finRange]
        have hend' : a+(2+5*J.m) ≤ heap := by rw [← hsize]; exact hend
        omega
      · change records+5*(List.finRange J.m).length < 2 ^ w
        rw [List.length_finRange]
        omega
    · intro out memS posS hpostS
      obtain ⟨⟨_, _, hframeS, hzeroS, hrecordsS⟩, hout⟩ := hpostS
      change out = records+5*(List.finRange J.m).length at hout
      rw [List.length_finRange] at hout
      change (∀ x < records, memS x = memH x) at hframeS
      change ZeroFrom memS out at hzeroS
      change ListAt memS records ((List.finRange J.m).flatMap J.positiveInstance.solverEdgeWords) at hrecordsS
      have houtWord : out < 2 ^ w := by omega
      refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
      · change (heap ≤ out ∧ out ≤ heap+(2+5*J.m) ∧ (∀ x < heap, memS x = mem x) ∧
          ZeroFrom memS out ∧ ListAt memS heap J.positiveInstance.solverWords) ∧ out = heap+2+5*J.m
        refine ⟨⟨by omega, by omega, ?_, hzeroS, ?_⟩, by omega⟩
        · intro x hx
          exact (hframeS x (by omega)).trans (hframeH x hx)
        · have hheaderS : ListAt memS heap [J.n+1, J.m] := by
            apply hheaderH.of_agree_below (h₀ := records)
            · change heap+2 ≤ records; omega
            · exact hframeS
          change ListAt memS heap ([J.n+1, J.m] ++ ((List.finRange J.m).flatMap J.positiveInstance.solverEdgeWords))
          apply listAt_append.mpr
          exact ⟨hheaderS, by simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, hrecords] using hrecordsS⟩
      · simp only [positiveInstanceContract, heapContract, wordPairContract, positiveInstanceEdgesContract,
          List.length_finRange, argsSize_cons, argsSize_nil, Expr.size_bin, Expr.size_load,
          Expr.size_reg, Expr.size_const]; omega

/-- Multiplier two on the source circulation encoding simultaneously fits
all input words, the additional vertex, and the complete fresh output. -/
theorem positiveInstance_pre_wordSize (J : Circulation) :
    (∀ x ∈ [0, J.solverWords.length], x < 2 ^ wordSize 2 J.solverWords) ∧
      (positiveInstanceContract (wordSize 2 J.solverWords) J).pre
        [0, J.solverWords.length] (initMem J.solverWords) := by
  let B := J.solverWords.length+J.solverWords.foldr max 0+2
  have hlen := J.solverWords_length
  have hbase : 4+5*J.m ≤ B := by dsimp only [B]; omega
  have hbase4 : 4 ≤ B := by omega
  have hproduct : 4*(4+5*J.m) ≤ B^2 := by
    simpa only [pow_two] using Nat.mul_le_mul hbase4 hbase
  have hself : B ≤ B^2 := by
    have h := Nat.mul_le_mul hbase4 (le_refl B)
    rw [← pow_two] at h
    omega
  have hnTop : J.n ≤ J.solverWords.foldr max 0 := Link.elem_le_foldr_max List.mem_cons_self
  have hnB : J.n+1 ≤ B := by dsimp only [B]; omega
  have hp := pow_lt_two_pow_wordSize (by decide : 1 ≤ 2) J.solverWords
  change B^2 < 2 ^ wordSize 2 J.solverWords at hp
  have halloc : J.solverWords.length+(2+5*J.m) < 2 ^ wordSize 2 J.solverWords := by omega
  refine ⟨?_, ⟨0, J.solverWords.length, rfl, listAt_initMem _, by omega,
    fun x hx => lt_two_pow_wordSize_of_mem (by decide) hx,
    hnB.trans_lt (hself.trans_lt hp), by omega⟩, zeroFrom_initMem _, halloc⟩
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> omega

end MinCostFlow.Scaling.Machine
