module

public import MinCostFlow.Scaling.ShortestRoutingOldEdgesProgram
public import MinCostFlow.Scaling.ShortestRoutingSourceEdgesProgram
public import MinCostFlow.Scaling.WordPairProgram
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Entry
import WordRAM.LinkDefs
import Mathlib.Tactic.NormNum

/-!
# Constructing the complete shortest-routing graph

Write the new dimensions, copy the original slots with their routing
capacities, and append the zero-cost source arcs. The result is exactly
the shortest-routing model's circulation encoding, with linear time and
fresh allocation.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[circulation,heap]`. -/
def shortestRoutingGraphBody (header scan source : ℕ) : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 4 header [.bin .add (.reg 2) (.const 1), .bin .add (.reg 3) (.reg 2), .reg 1] ;;
  .call 5 scan [.bin .add (.reg 0) (.const 2), .reg 3, .reg 2, .reg 4] ;;
  .call 6 source [.reg 2, .const 0, .reg 2, .reg 5] ;;
  .ret (.reg 6)

/-- Header construction followed by the shortest-routing edge scan. -/
def shortestRoutingGraphModule (b : ℕ) : List Stmt :=
  shortestRoutingGraphBody (b+1) (b+2) (b+4) :: wordPairBody ::
    (shortestRoutingOldEdgesModule (b+2) ++ shortestRoutingSourceEdgesModule (b+4))

/-- The input circulation precedes the fresh output, and the additional
vertex index and total edge count fits along with the original words. -/
def shortestRoutingGraphContract (w : ℕ) (J : Circulation) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a heap, args = [a, heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length ≤ heap ∧ (∀ x ∈ J.solverWords, x < 2 ^ w) ∧
      J.n+1 < 2 ^ w ∧ J.m+J.n < 2 ^ w ∧ 8 < 2 ^ w)
    (fun args _ mem' => ListAt mem' (heapArg args) J.shortestRoutingGraph.solverWords)
    (fun _ _ => 300*(J.m+J.n)+400) (fun _ _ => 2+5*(J.m+J.n))
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧
      out = heapArg args+2+5*(J.m+J.n) }

/-- Building the shortest-routing graph is deterministic. -/
theorem shortestRoutingGraphModule_noRand (b : ℕ) :
    ∀ body ∈ shortestRoutingGraphModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [shortestRoutingGraphBody, Stmt.NoRand, and_self]
  · rcases List.mem_cons.mp hb with rfl | hb
    · exact wordPairBody_noRand
    · rcases List.mem_append.mp hb with hb | hb
      · exact shortestRoutingOldEdgesModule_noRand _ body hb
      · exact shortestRoutingSourceEdgesModule_noRand _ body hb

/-- The constructor computes the model's exact shortest-routing solver
input with linear cost, exact allocation, and the fresh-heap frame. -/
theorem shortestRoutingGraph_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (shortestRoutingGraphModule b)) (J : Circulation) :
    MeetsContract w p b (shortestRoutingGraphContract w J) := by
  have htail := hasAt_tail hp
  have hheader : p.HasAt (b+1) wordPairModule := by
    intro i hi
    have hi0 : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [wordPairModule, List.getElem_cons_zero, Nat.add_zero] using htail.head
  have hscan : p.HasAt (b+2) (shortestRoutingOldEdgesModule (b+2)) := by
    simpa only [Nat.add_assoc] using hasAt_append_left (hasAt_tail htail)
  have hsource : p.HasAt (b+4) (shortestRoutingSourceEdgesModule (b+4)) := by
    have hh := hasAt_append_right (hasAt_tail htail)
    simpa only [shortestRoutingOldEdgesModule,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.add_assoc] using hh
  have hkV := shortestRoutingSourceEdges_meetsContract (w := w) hsource J (List.finRange J.n)
  have hkH := wordPair_meetsContract (w := w) hheader
  have hkS := shortestRoutingOldEdges_meetsContract (w := w) hscan J (List.finRange J.m)
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a, heap, rfl, hat, hend, hinput, hn1, hmn, hw⟩, hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap+(2+5*(J.m+J.n)) < 2 ^ w at hspace
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
  unfold shortestRoutingGraphBody
  refine runs_seq_assign_le (v := J.n) (by eval_expr) ?_
  refine runs_seq_assign_le (v := J.m) (by eval_expr) ?_
  refine runs_seq_call_le hkH (vs := [J.n+1, J.m+J.n, heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨J.n+1, J.m+J.n, heap, rfl⟩, hzero, hh2⟩
  · intro records memH posH hpostH
    obtain ⟨⟨_, _, hframeH, hzeroH, hheaderH⟩, hrecords⟩ := hpostH
    change records = heap+2 at hrecords
    change (∀ x < heap, memH x = mem x) at hframeH
    change ZeroFrom memH records at hzeroH
    change ListAt memH heap [J.n+1, J.m+J.n] at hheaderH
    have hedgeH : ListAt memH (a+2) ((List.finRange J.m).flatMap J.solverEdgeWords) := by
      apply hedge.of_agree_below (h₀ := heap)
      · rw [Circulation.solverEdgeRecords_length, List.length_finRange]
        rw [hsize] at hend
        omega
      · exact hframeH
    have hrecordsWord : records < 2 ^ w := by omega
    refine runs_seq_call_le hkS (vs := [a+2, J.m, J.n, records]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · refine ⟨⟨a+2, records, by simp only [List.length_finRange], hedgeH, ?_, hrecordWords, hw, hn1⟩,
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
      change ListAt memS records ((List.finRange J.m).flatMap (fun e => J.shortestRoutingGraph.solverEdgeWords (Fin.castAdd J.n e))) at hrecordsS
      have houtWord : out < 2 ^ w := by omega
      refine runs_seq_call_le hkV (vs := [J.n,0,J.n,out]) (by eval_expr) (by wram_words) ?_ ?_
      · refine ⟨⟨0,out,by simp only [List.length_finRange],?_,?_,hn1,hw⟩,hzeroS,?_⟩
        · intro i
          simp only [List.getElem_finRange,Fin.val_cast,Nat.zero_add]
        · simp only [List.length_finRange,Nat.zero_add]
          exact le_rfl
        · change out+5*(List.finRange J.n).length < 2^w
          rw [List.length_finRange]
          omega
      · intro ret memV posV hpostV
        obtain ⟨⟨_,_,hframeV,hzeroV,hsourceV⟩,hret⟩ := hpostV
        change ret = out+5*(List.finRange J.n).length at hret
        rw [List.length_finRange] at hret
        change (∀ x < out, memV x = memS x) at hframeV
        change ZeroFrom memV ret at hzeroV
        change ListAt memV out ((List.finRange J.n).flatMap
          (fun v => J.shortestRoutingGraph.solverEdgeWords (Fin.natAdd J.m v))) at hsourceV
        have hretWord : ret < 2^w := by omega
        refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
        · change (heap ≤ ret ∧ ret ≤ heap+(2+5*(J.m+J.n)) ∧ (∀ x < heap, memV x = mem x) ∧
            ZeroFrom memV ret ∧ ListAt memV heap J.shortestRoutingGraph.solverWords) ∧
            ret = heap+2+5*(J.m+J.n)
          refine ⟨⟨by omega,by omega,?_,hzeroV,?_⟩,by omega⟩
          · intro x hx
            exact (hframeV x (by omega)).trans ((hframeS x (by omega)).trans (hframeH x hx))
          · have hheaderV : ListAt memV heap [J.n+1,J.m+J.n] := by
              apply (hheaderH.of_agree_below (h₀ := records) (by change heap+2 ≤ records; omega) hframeS).of_agree_below (h₀ := out)
              · change heap+2 ≤ out
                omega
              · exact hframeV
            have hrecordsV := hrecordsS.of_agree_below (h₀ := out) (by
              have hlen : ((List.finRange J.m).flatMap
                  (fun e => J.shortestRoutingGraph.solverEdgeWords (Fin.castAdd J.n e))).length = 5*J.m := by
                simp only [List.length_flatMap,Circulation.solverEdgeWords,List.length_cons,List.length_nil]
                simp
                omega
              rw [hlen]
              omega) hframeV
            rw [shortestRouting_solverWords_flatMap]
            apply listAt_append.mpr
            refine ⟨hheaderV,?_⟩
            change ListAt memV (heap+2) (_ ++ _)
            apply listAt_append.mpr
            refine ⟨by simpa only [hrecords] using hrecordsV,?_⟩
            have hblockLen : ((List.finRange J.m).flatMap
                (fun e => J.shortestRoutingGraph.solverEdgeWords (Fin.castAdd J.n e))).length = 5*J.m := by
              simp only [List.length_flatMap,Circulation.solverEdgeWords,List.length_cons,List.length_nil]
              simp
              omega
            rw [hblockLen]
            simpa only [hrecords,hout] using hsourceV
        · simp only [shortestRoutingGraphContract,heapContract,wordPairContract,
            shortestRoutingOldEdgesContract,shortestRoutingSourceEdgesContract,
            List.length_finRange,argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,
            Expr.size_reg,Expr.size_const]
          omega

end MinCostFlow.Scaling.Machine
