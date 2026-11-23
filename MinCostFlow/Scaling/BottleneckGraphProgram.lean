module

public import MinCostFlow.Scaling.BottleneckEdgesProgram
public import MinCostFlow.Scaling.WordPairProgram
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Entry
import WordRAM.LinkDefs
import Mathlib.Tactic.NormNum

/-!
# Constructing a complete bottleneck test graph

Copy the dimensions and scan all edge slots, preserving endpoints and
costs while testing each capacity against the threshold. This constructs
exactly the bottleneck graph used by the model's binary search.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,threshold,heap]`. -/
def bottleneckGraphBody (header scan : ℕ) : Stmt :=
  .assign 3 (.load (.reg 0)) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 5 header [.reg 3,.reg 4,.reg 2] ;;
  .call 6 scan [.bin .add (.reg 0) (.const 2),.reg 4,.reg 1,.reg 5] ;;
  .ret (.reg 6)

/-- Header construction followed by the bottleneck edge scan. -/
def bottleneckGraphModule (b : ℕ) : List Stmt :=
  bottleneckGraphBody (b+1) (b+2) :: wordPairBody :: bottleneckEdgesModule (b+2)

/-- The input circulation precedes fresh output, and every copied word fits. -/
def bottleneckGraphContract (w : ℕ) (J : Circulation) (B : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a heap, args = [a,B,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length ≤ heap ∧ (∀ x ∈ J.solverWords, x < 2 ^ w) ∧
      8 < 2 ^ w)
    (fun args _ mem' => ListAt mem' (heapArg args) (J.bottleneckGraph B).solverWords)
    (fun _ _ => 200*J.m+200) (fun _ _ => 2+5*J.m)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧
      out = heapArg args+2+5*J.m }

/-- Building the bottleneck test graph is deterministic. -/
theorem bottleneckGraphModule_noRand (b : ℕ) :
    ∀ body ∈ bottleneckGraphModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [bottleneckGraphBody, Stmt.NoRand, and_self]
  · rcases List.mem_cons.mp hb with rfl | hb
    · exact wordPairBody_noRand
    · exact bottleneckEdgesModule_noRand _ body hb

/-- The constructor computes the model's exact bottleneck test
input with linear cost, exact allocation, and the fresh-heap frame. -/
theorem bottleneckGraph_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (bottleneckGraphModule b)) (J : Circulation) (B : ℕ) :
    MeetsContract w p b (bottleneckGraphContract w J B) := by
  have htail := hasAt_tail hp
  have hheader : p.HasAt (b+1) wordPairModule := by
    intro i hi
    have hi0 : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [wordPairModule, List.getElem_cons_zero, Nat.add_zero] using htail.head
  have hscan : p.HasAt (b+2) (bottleneckEdgesModule (b+2)) := by
    simpa only [Nat.add_assoc] using hasAt_tail htail
  have hkH := wordPair_meetsContract (w := w) hheader
  have hkS := bottleneckEdges_meetsContract (w := w) hscan J B (List.finRange J.m)
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a, heap, rfl, hat, hend, hinput, hw⟩, hzero, hspace⟩ := hpre
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
  have hn : J.n < 2 ^ w := hinput _ List.mem_cons_self
  have hB : B < 2^w := hwords _ (by simp)
  have hm : J.m < 2 ^ w := hinput _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have ha : a < 2 ^ w := by rw [hsize] at hend; omega
  have ha1 : a+1 < 2 ^ w := by rw [hsize] at hend; omega
  have ha2 : a+2 < 2 ^ w := by rw [hsize] at hend; omega
  have hh : heap < 2 ^ w := by omega
  have hh2 : heap+2 < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have htwo : 2 < 2 ^ w := by omega
  apply runs_start_le
  unfold bottleneckGraphBody
  refine runs_seq_assign_le (v := J.n) (by eval_expr) ?_
  refine runs_seq_assign_le (v := J.m) (by eval_expr) ?_
  refine runs_seq_call_le hkH (vs := [J.n,J.m,heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨J.n,J.m,heap, rfl⟩, hzero, hh2⟩
  · intro records memH posH hpostH
    obtain ⟨⟨_, _, hframeH, hzeroH, hheaderH⟩, hrecords⟩ := hpostH
    change records = heap+2 at hrecords
    change (∀ x < heap, memH x = mem x) at hframeH
    change ZeroFrom memH records at hzeroH
    change ListAt memH heap [J.n,J.m] at hheaderH
    have hedgeH : ListAt memH (a+2) ((List.finRange J.m).flatMap J.solverEdgeWords) := by
      apply hedge.of_agree_below (h₀ := heap)
      · rw [Circulation.solverEdgeRecords_length, List.length_finRange]
        rw [hsize] at hend
        omega
      · exact hframeH
    have hrecordsWord : records < 2 ^ w := by omega
    refine runs_seq_call_le hkS (vs := [a+2,J.m,B,records]) (by eval_expr) ?_ ?_ ?_
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
      change ListAt memS records ((List.finRange J.m).flatMap (J.bottleneckGraph B).solverEdgeWords) at hrecordsS
      have houtWord : out < 2 ^ w := by omega
      refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
      · change (heap ≤ out ∧ out ≤ heap+(2+5*J.m) ∧ (∀ x < heap, memS x = mem x) ∧
          ZeroFrom memS out ∧ ListAt memS heap (J.bottleneckGraph B).solverWords) ∧ out = heap+2+5*J.m
        refine ⟨⟨by omega, by omega, ?_, hzeroS, ?_⟩, by omega⟩
        · intro x hx
          exact (hframeS x (by omega)).trans (hframeH x hx)
        · have hheaderS : ListAt memS heap [J.n,J.m] := by
            apply hheaderH.of_agree_below (h₀ := records)
            · change heap+2 ≤ records; omega
            · exact hframeS
          change ListAt memS heap ([J.n,J.m] ++ ((List.finRange J.m).flatMap (J.bottleneckGraph B).solverEdgeWords))
          apply listAt_append.mpr
          exact ⟨hheaderS, by simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, hrecords] using hrecordsS⟩
      · simp only [bottleneckGraphContract, heapContract, wordPairContract, bottleneckEdgesContract,
          List.length_finRange, argsSize_cons, argsSize_nil, Expr.size_bin, Expr.size_load,
          Expr.size_reg, Expr.size_const]; omega

end MinCostFlow.Scaling.Machine
