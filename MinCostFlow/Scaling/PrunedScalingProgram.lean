module

public import MinCostFlow.Scaling.PrunedScalingContract
import MinCostFlow.Scaling.CostCapacityProgram
import MinCostFlow.Scaling.CostCapacityOutputBounds
import MinCostFlow.Scaling.CirculationLayout
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# Executing the exact pruned scaling adapter

Stable compaction saves original edge indices. The full cost-capacity
program solves the compacted graph, whose optimal flow is nonnegative.
Conversion writes its signed pairs, and scatter into fresh zero memory
restores exactly the model's original edge coordinates.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Pruning, full scaling, signed conversion, and zero-initialized scatter
compute the exact counted pruning adapter with linear additional cost. -/
theorem prunedScaling_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ} {T : ℕ → ℕ → ℕ}
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hdet : solver.IsDeterministic) (hmono : SolverTimeMonotone T)
    (hp : p.HasAt b (prunedScalingModule solver entry b)) (J : Circulation) (C U : ℕ) :
    MeetsContract w p b (prunedScalingContract w solver entry T hproc J C U) := by
  let scale := b+4
  let convert := scale+(costCapacityModule solver entry scale).length
  let restore := convert+2
  let K := J.withoutZeroEdges
  let f := (costCapacityModel (canonicalSolver solver entry T hproc) K C U).value
  let entries := J.positiveFlowEntries f
  have hkm : K.m≤J.m := J.positiveEdges_length_le
  have helen : entries.length=K.m := List.length_ofFn
  have hkeys : entries.map (fun e => e.1.val)=J.positiveEdges.map Fin.val := by
    rw [show (fun e : Fin J.m × ℤ => e.1.val)=Fin.val ∘ Prod.fst from rfl,←List.map_map,
      Circulation.positiveFlowEntries_keys]
  have hvalues : (entries.map Prod.snd).flatMap encodeInt=(List.ofFn f).flatMap encodeInt := by
    simp only [entries,Circulation.positiveFlowEntries,List.map_ofFn,Function.comp_def]
  have ht : p.HasAt (b+1) (positivePruneModule (b+1) ++
      (costCapacityModule solver entry scale ++
        (unsignedFlowModule convert ++ restoreScatterModule restore))) := hasAt_tail hp
  have hP : p.HasAt (b+1) (positivePruneModule (b+1)) := hasAt_append_left ht
  have htS : p.HasAt scale (costCapacityModule solver entry scale ++
      (unsignedFlowModule convert ++ restoreScatterModule restore)) := by
    have h := hasAt_append_right ht
    change p.HasAt scale _ at h
    exact h
  have hS : p.HasAt scale (costCapacityModule solver entry scale) := hasAt_append_left htS
  have htF : p.HasAt convert (unsignedFlowModule convert ++ restoreScatterModule restore) :=
    hasAt_append_right htS
  have hF : p.HasAt convert (unsignedFlowModule convert) := hasAt_append_left htF
  have hR : p.HasAt restore (restoreScatterModule restore) := hasAt_append_right htF
  have hkP := positivePrune_meetsContract (w := w) hP J
  have hkS := costCapacity_meetsContract (w := w) hproc hdet hmono hS K C U
  have hkF := unsignedFlowTable_meetsContract (w := w) hF f
  have hkR := restoreScatter_meetsContract (w := w) hR entries
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,heap,rfl,hgraph,hgraphEnd,hinput,h8,hC,hu,hU,hz,hs⟩ := hpre
  have hCK : K.CostsBounded C := fun e => hC (J.positiveIndex e)
  have huK : ∀ e,K.capacity e≤U := fun e => hu (J.positiveIndex e)
  have hf := costCapacityModel_output_bounds solver entry T hproc K C U hCK huK hU
  have hUword : U<2^w := hwords U (by simp)
  have hCword : C<2^w := hwords C (by simp)
  have hsNum := hs
  change heap+(2+6*J.m+costScalingSpace K C (max U (2*K.m+1))+2*K.m+2*J.m)<2^w at hsNum
  have hsize := J.solverWords_length
  have hh : heap<2^w := by omega
  have ha : a<2^w := by rw [hsize] at hgraphEnd; omega
  have ha1 : a+1<2^w := by rw [hsize] at hgraphEnd; omega
  have hm : J.m<2^w := by omega
  have hkword : K.m<2^w := hkm.trans_lt hm
  have h5m : 5*J.m<2^w := by omega
  have hh2 : heap+2<2^w := by omega
  have hindex : heap+2+5*J.m<2^w := by omega
  have hM := (solver_header_at J hgraph).2
  apply runs_start_le
  unfold prunedScalingBody
  refine runs_seq_assign_le (v := J.m) (by eval_expr) ?_
  refine runs_seq_call_le hkP (vs := [a,heap]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨a,heap,rfl,hgraph,hgraphEnd,hinput,h8⟩,hz,by change heap+(2+6*J.m)<2^w; omega⟩
  · intro pruneEnd memP posP hpostP
    obtain ⟨⟨_,_,hframeP,hzP,hgraphP,hindicesP⟩,hpruneEnd⟩ := hpostP
    change pruneEnd=heap+2+6*J.m at hpruneEnd
    change ListAt memP heap K.solverWords at hgraphP
    change ListAt memP (heap+2+5*J.m) (J.positiveEdges.map Fin.val) at hindicesP
    change (∀ x<heap,memP x=mem x) at hframeP
    change ZeroFrom memP pruneEnd at hzP
    have hpword : pruneEnd<2^w := by omega
    have hK := (solver_header_at K hgraphP).2
    refine runs_seq_assign_le (v := K.m) (by eval_expr) ?_
    refine runs_seq_call_le hkS (vs := [heap,C,U,pruneEnd]) (by eval_expr) (by wram_words) ?_ ?_
    · refine ⟨heap,pruneEnd,rfl,hgraphP,?_,hCK,huK,hzP,?_⟩
      · rw [K.solverWords_length]; omega
      · omega
    · intro solveEnd memS posS hpostS
      obtain ⟨hloS,hhiS,hflowS,hzS,hframeS⟩ := hpostS
      change pruneEnd≤solveEnd at hloS
      change solveEnd≤pruneEnd+costScalingSpace K C (max U (2*K.m+1)) at hhiS
      change ListAt memS (solveEnd-K.m) (List.ofFn (fun e => (f e).toNat)) at hflowS
      change (∀ x<pruneEnd,memS x=memP x) at hframeS
      have hsword : solveEnd<2^w := by omega
      have hfword : solveEnd-K.m<2^w := by omega
      have hsk : K.m≤solveEnd := by omega
      refine runs_seq_call_le hkF (vs := [solveEnd-K.m,K.m,solveEnd]) (by eval_expr)
        (by wram_words) ?_ ?_
      · refine ⟨⟨solveEnd-K.m,solveEnd,rfl,hflowS,by omega,?_,by omega⟩,hzS,?_⟩
        · intro e; exact ⟨(hf e).1,((hf e).2).trans_lt hUword⟩
        · change solveEnd+2*K.m<2^w; omega
      · intro signedEnd memF posF hpostF
        obtain ⟨⟨_,_,hframeF,hzF,htableF⟩,hsignedEnd⟩ := hpostF
        change signedEnd=solveEnd+2*K.m at hsignedEnd
        change (∀ x<solveEnd,memF x=memS x) at hframeF
        change SignedTableAt memF solveEnd f at htableF
        change ZeroFrom memF signedEnd at hzF
        have hfw : signedEnd<2^w := by omega
        have hkeysF : ListAt memF (heap+2+5*J.m) (entries.map (fun e => e.1.val)) := by
          rw [hkeys]
          apply (hindicesP.of_agree_below (h₀ := pruneEnd) ?_ hframeS).of_agree_below (h₀ := solveEnd) ?_ hframeF
          all_goals rw [List.length_map]; have hklen := J.positiveEdges_length_le; omega
        refine runs_seq_call_le hkR
          (vs := [heap+2+5*J.m,solveEnd,K.m,J.m,signedEnd]) (by eval_expr) (by wram_words) ?_ ?_
        · refine ⟨⟨heap+2+5*J.m,solveEnd,signedEnd,by rw [helen],hkeysF,?_,?_,?_,?_,by omega⟩,hzF,?_⟩
          · rw [hvalues]; exact htableF.listAt
          · rw [helen]; omega
          · rw [helen]; omega
          · intro e he
            obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
            exact ((hf i).2).trans_lt hUword
          · change signedEnd+2*J.m<2^w; omega
        · intro out memR posR hpostR
          obtain ⟨⟨_,_,hframeR,hzR,htableR⟩,hout⟩ := hpostR
          change out=signedEnd+2*J.m at hout
          change (∀ x<signedEnd,memR x=memF x) at hframeR
          change SignedTableAt memR signedEnd (Scatter.write (fun _ => 0) entries) at htableR
          have how : out<2^w := by omega
          refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
          · change heap≤out ∧ out≤heap+prunedScalingSpace J C U ∧
              SignedTableAt memR (out-2*J.m) (J.scatterPositive f) ∧
              ZeroFrom memR out ∧ ∀ x<heap,memR x=mem x
            refine ⟨by omega,?_,?_,hzR,?_⟩
            · unfold prunedScalingSpace; change out≤heap+(2+6*J.m+costScalingSpace K C (max U (2*K.m+1))+2*K.m+2*J.m); omega
            · have he : out-2*J.m=signedEnd := by omega
              rw [he]; exact htableR
            · intro x hx
              exact (hframeR x (by omega)).trans ((hframeF x (by omega)).trans
                ((hframeS x (by omega)).trans (hframeP x hx)))
          · simp only [prunedScalingContract,positivePruneContract,unsignedFlowTableContract,
              restoreScatterContract,heapContract,helen,argsSize_cons,argsSize_nil,
              Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
            have hc : (costCapacityContract w solver entry T hproc K C U).cost [heap,C,U,pruneEnd]
                memP=
                (costCapacityContract w solver entry T hproc J.withoutZeroEdges C U).cost [] (fun _ => 0) := rfl
            rw [hc]
            omega

end MinCostFlow.Scaling.Machine
