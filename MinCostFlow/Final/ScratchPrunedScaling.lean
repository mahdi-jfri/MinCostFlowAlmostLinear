module

public import MinCostFlow.Final.ScratchCostCapacity
public import MinCostFlow.Scaling.PrunedScalingContract
import MinCostFlow.Scaling.CostCapacityOutputBounds
import MinCostFlow.Scaling.CostCapacityCorrectness
import MinCostFlow.Scaling.CirculationLayout
import MinCostFlow.Scaling.CostCapacityOutputBounds
import MinCostFlow.Scaling.CostCapacityProgram
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# Pruned scaling with polynomial scratch

The compacted graph is solved using the widened scaling program. The
restore pass scatters the integral result back into original edge order.
-/

@[expose] public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine

/-- The actual composed model returns nonnegative integral coordinates
bounded by the supplied capacity budget. -/
theorem scratchCostCapacityModel_output_bounds (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (J : Circulation) (C U : ℕ) (hC : J.CostsBounded C)
    (hu : ∀ e,J.capacity e≤U) (hU : 1≤U) :
    ∀ e,0≤(costCapacityModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) J C U).value e ∧
      ((costCapacityModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) J C U).value e).natAbs≤U := by
  have hopt := costCapacityModel_optimal ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K))
    (fun K _ _ => compressedCanonicalSolverAt_optimal _ solver entry T S (hproc K) K) J C U hU hC hu
  intro e
  have hlo : 0≤(costCapacityModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) J C U).value e :=
    Int.cast_nonneg_iff.mp (hopt.1.2 e).1
  have hhi : (costCapacityModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) J C U).value e≤(U : ℤ) := by
    apply (Int.cast_le (R := ℝ)).mp
    simpa only [Int.cast_natCast] using ((hopt.1.2 e).2.trans (by exact_mod_cast hu e))
  have habs := congrArg Int.natAbs (Int.toNat_of_nonneg hlo)
  simp only [Int.natAbs_natCast] at habs
  refine ⟨hlo,?_⟩
  rw [←habs]
  simpa only [Int.toNat_natCast] using Int.toNat_le_toNat hhi

/-- Pruning, full cost-capacity scaling, conversion, and scatter. -/
def scratchPrunedScalingModule (solver : Program) (entry b c d : ℕ) : List Stmt :=
  let scale := b+4
  let convert := scale+(scratchCostCapacityModule solver entry scale c d).length
  let restore := convert+2
  prunedScalingBody (b+1) scale convert restore ::
    (positivePruneModule (b+1) ++ (scratchCostCapacityModule solver entry scale c d ++
      (unsignedFlowModule convert ++ restoreScatterModule restore)))

/-- Space for compaction, the exact nested solver, conversion, and scatter. -/
def scratchPrunedScalingSpace (c d : ℕ) (J : Circulation) (C U : ℕ) : ℕ :=
  2+6*J.m+scratchCostScalingSpace c d J.withoutZeroEdges C (max U (2*J.withoutZeroEdges.m+1))+
    2*J.withoutZeroEdges.m+2*J.m

/-- Exact pruning-adapter output in a signed table occupying the final
`2*m` returned cells. The solver receives only the compacted graph. -/
noncomputable def scratchPrunedScalingContract (w : ℕ) (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (J : Circulation) (C U : ℕ) : Contract :=
  let inner := fun K => costCapacityModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) K C U
  { pre := fun args mem => ∃ a heap,args=[a,C,U,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length≤heap ∧ (∀ x∈J.solverWords,x<2^w) ∧ 8<2^w ∧
      J.CostsBounded C ∧ (∀ e,J.capacity e≤U) ∧ 1≤U ∧
      ZeroFrom mem heap ∧ heap+scratchPrunedScalingSpace c d J C U<2^w
    post := fun args mem ret mem' => heapArg args≤ret ∧ ret≤heapArg args+scratchPrunedScalingSpace c d J C U ∧
      SignedTableAt mem' (ret-2*J.m) (Circulation.invokePruned inner J).value ∧
      ZeroFrom mem' ret ∧ ∀ x<heapArg args,mem' x=mem x
    cost := fun _ _ => (scratchCostCapacityContract w solver entry T S c d hproc J.withoutZeroEdges C U).cost [] (fun _ => 0)+
      1000*J.m+1000 }

/-- The pruned entry contains no random instruction when its solver does not. -/
theorem scratchPrunedScalingModule_noRand (solver : Program) (entry b c d : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body∈scratchPrunedScalingModule solver entry b c d,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [prunedScalingBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hb | hb
    · exact positivePruneModule_noRand _ body hb
    · rcases List.mem_append.mp hb with hb | hb
      · exact scratchCostCapacityModule_noRand solver entry _ c d hdet body hb
      · rcases List.mem_append.mp hb with hb | hb
        · exact unsignedFlowModule_noRand _ body hb
        · exact restoreScatterModule_noRand _ body hb

/-- Pruning, full scaling, signed conversion, and zero-initialized scatter
compute the exact counted pruning adapter with linear additional cost. -/
theorem scratchPrunedScaling_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ} {T S : ℕ → ℕ → ℕ} {c d : ℕ}
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hScratch : ∀ n m, S n m ≤ c * (n + m + 2)^d)
    (hdet : solver.IsDeterministic) (hmono : SolverTimeMonotone T)
    (hp : p.HasAt b (scratchPrunedScalingModule solver entry b c d)) (J : Circulation) (C U : ℕ) :
    MeetsContract w p b (scratchPrunedScalingContract w solver entry T S c d hproc J C U) := by
  let scale := b+4
  let convert := scale+(scratchCostCapacityModule solver entry scale c d).length
  let restore := convert+2
  let K := J.withoutZeroEdges
  let f := (costCapacityModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) K C U).value
  let entries := J.positiveFlowEntries f
  have hkm : K.m≤J.m := J.positiveEdges_length_le
  have helen : entries.length=K.m := List.length_ofFn
  have hkeys : entries.map (fun e => e.1.val)=J.positiveEdges.map Fin.val := by
    rw [show (fun e : Fin J.m × ℤ => e.1.val)=Fin.val ∘ Prod.fst from rfl,←List.map_map,
      Circulation.positiveFlowEntries_keys]
  have hvalues : (entries.map Prod.snd).flatMap encodeInt=(List.ofFn f).flatMap encodeInt := by
    simp only [entries,Circulation.positiveFlowEntries,List.map_ofFn,Function.comp_def]
  have ht : p.HasAt (b+1) (positivePruneModule (b+1) ++
      (scratchCostCapacityModule solver entry scale c d ++
        (unsignedFlowModule convert ++ restoreScatterModule restore))) := hasAt_tail hp
  have hP : p.HasAt (b+1) (positivePruneModule (b+1)) := hasAt_append_left ht
  have htS : p.HasAt scale (scratchCostCapacityModule solver entry scale c d ++
      (unsignedFlowModule convert ++ restoreScatterModule restore)) := by
    have h := hasAt_append_right ht
    change p.HasAt scale _ at h
    exact h
  have hS : p.HasAt scale (scratchCostCapacityModule solver entry scale c d) := hasAt_append_left htS
  have htF : p.HasAt convert (unsignedFlowModule convert ++ restoreScatterModule restore) :=
    hasAt_append_right htS
  have hF : p.HasAt convert (unsignedFlowModule convert) := hasAt_append_left htF
  have hR : p.HasAt restore (restoreScatterModule restore) := hasAt_append_right htF
  have hkP := positivePrune_meetsContract (w := w) hP J
  have hkS := scratchCostCapacity_meetsContract (w := w) hproc hScratch hdet hmono hS K C U
  have hkF := unsignedFlowTable_meetsContract (w := w) hF f
  have hkR := restoreScatter_meetsContract (w := w) hR entries
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,heap,rfl,hgraph,hgraphEnd,hinput,h8,hC,hu,hU,hz,hs⟩ := hpre
  have hCK : K.CostsBounded C := fun e => hC (J.positiveIndex e)
  have huK : ∀ e,K.capacity e≤U := fun e => hu (J.positiveIndex e)
  have hf := scratchCostCapacityModel_output_bounds solver entry T S c d hproc K C U hCK huK hU
  have hUword : U<2^w := hwords U (by simp)
  have hCword : C<2^w := hwords C (by simp)
  have hsNum := hs
  change heap+(2+6*J.m+scratchCostScalingSpace c d K C (max U (2*K.m+1))+2*K.m+2*J.m)<2^w at hsNum
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
      change solveEnd≤pruneEnd+scratchCostScalingSpace c d K C (max U (2*K.m+1)) at hhiS
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
          · change heap≤out ∧ out≤heap+scratchPrunedScalingSpace c d J C U ∧
              SignedTableAt memR (out-2*J.m) (J.scatterPositive f) ∧
              ZeroFrom memR out ∧ ∀ x<heap,memR x=mem x
            refine ⟨by omega,?_,?_,hzR,?_⟩
            · unfold scratchPrunedScalingSpace; change out≤heap+(2+6*J.m+scratchCostScalingSpace c d K C (max U (2*K.m+1))+2*K.m+2*J.m); omega
            · have he : out-2*J.m=signedEnd := by omega
              rw [he]; exact htableR
            · intro x hx
              exact (hframeR x (by omega)).trans ((hframeF x (by omega)).trans
                ((hframeS x (by omega)).trans (hframeP x hx)))
          · simp only [scratchPrunedScalingContract,positivePruneContract,unsignedFlowTableContract,
              restoreScatterContract,heapContract,helen,argsSize_cons,argsSize_nil,
              Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
            have hc : (scratchCostCapacityContract w solver entry T S c d hproc K C U).cost [heap,C,U,pruneEnd]
                memP=
                (scratchCostCapacityContract w solver entry T S c d hproc J.withoutZeroEdges C U).cost [] (fun _ => 0) := rfl
            rw [hc]
            omega

/-- Deleting zero-capacity slots cannot enlarge the complete nested
cost-scaling workspace, including its augmented capacity budget. -/
theorem scratchWithoutZeroEdges_costScalingSpace_le (c d : ℕ) (J : Circulation) (C U : ℕ) :
    scratchCostScalingSpace c d J.withoutZeroEdges C (max U (2*J.withoutZeroEdges.m+1))≤
      scratchCostScalingSpace c d J C (max U (2*J.m+1)) := by
  let K := J.withoutZeroEdges
  have hm : K.m≤J.m := J.positiveEdges_length_le
  have hn : K.n=J.n := rfl
  have hV : max U (2*K.m+1)≤max U (2*J.m+1) := max_le_max le_rfl (by omega)
  have hp := Nat.pow_le_pow_left (show K.m+K.m≤J.m+J.m by omega) 10
  have hD : costStepNumberBase K C (max U (2*K.m+1))≤
      costStepNumberBase J C (max U (2*J.m+1)) := by
    unfold costStepNumberBase
    rw [hn]
    omega
  have hN := Nat.pow_le_pow_left hD (524*scratchWidthFactor c d)
  have hc := Nat.mul_le_mul_left (costRounds J.n C+2) hN
  have hlenK := K.solverWords_length
  have hlenJ := J.solverWords_length
  change scratchCostScalingSpace c d K C (max U (2*K.m+1))≤_
  unfold scratchCostScalingSpace
  rw [hn,hlenK,hlenJ]
  omega

/-- Original dimensions cover the pruned solve and every linear adapter
allocation together. -/
theorem scratchPrunedScalingSpace_le (c d : ℕ) (J : Circulation) (C U : ℕ) :
    scratchPrunedScalingSpace c d J C U≤2+10*J.m+scratchCostScalingSpace c d J C (max U (2*J.m+1)) := by
  have hm := J.positiveEdges_length_le
  have hs := scratchWithoutZeroEdges_costScalingSpace_le c d J C U
  change J.withoutZeroEdges.m≤J.m at hm
  unfold scratchPrunedScalingSpace
  omega

end MinCostFlow.Final
