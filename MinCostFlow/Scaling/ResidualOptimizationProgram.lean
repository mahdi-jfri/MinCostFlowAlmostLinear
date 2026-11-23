module

public import MinCostFlow.Scaling.ResidualOptimizationContract
import MinCostFlow.Scaling.ResidualOptimizationFacts
import MinCostFlow.Scaling.PrunedScalingProgram
import MinCostFlow.Scaling.PrunedScalingOutputBounds
import MinCostFlow.Scaling.FeasibilityPhaseFacts
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# Executing the residual optimization phase

The stored shifted graph and its bounded flow give the exact residual
circulation. The full pruned scaling procedure returns the same correction
as the counted general-flow model. Its proved bounds justify copying the
magnitudes and augmenting the shifted flow with unsigned arithmetic.
The last scan adds the lower capacities back and produces the model's
original edge-indexed signed flow.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The complete residual optimization phase returns exactly the counted
reduction's successful flow, with the actual nested scaling budget and
linear additional work, without randomness. -/
theorem residualOptimization_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ} {T : ℕ → ℕ → ℕ}
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hdet : solver.IsDeterministic) (hmono : SolverTimeMonotone T)
    (hp : p.HasAt b (residualOptimizationModule solver entry b))
    (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) (C U : ℕ) :
    MeetsContract w p b (residualOptimizationContract w solver entry T hproc I hv f C U) := by
  let solve := b+1+(residualModule (b+1)).length
  let copy := solve+(prunedScalingModule solver entry solve).length
  let augment := copy+1
  let restore := augment+(residualAugmentModule augment).length
  let J := FlowReduction.shiftedGraph I hv
  let R := J.residual f
  let B := FlowReduction.scalingCapacityBudget I U
  let delta := (Circulation.invokePruned
    (fun K => costCapacityModel (canonicalSolver solver entry T hproc) K C B) R).value
  let updated := fun e => f e+delta (Fin.castAdd I.m e)-delta (Fin.natAdd I.m e)
  let entries := List.ofFn (fun e => (I.edge e,(updated e).toNat))
  have hJm : J.m=I.m := rfl
  have hRm : R.m=I.m+I.m := rfl
  have hlen : entries.length=I.m := List.length_ofFn
  have hparts : p.HasAt (b+1) (residualModule (b+1) ++ (prunedScalingModule solver entry solve ++
      (magnitudeCopyModule copy ++ (residualAugmentModule augment ++ lowerRestoreModule restore)))) := hasAt_tail hp
  have hres := hasAt_append_left hparts
  have htS : p.HasAt solve (prunedScalingModule solver entry solve ++
      (magnitudeCopyModule copy ++ (residualAugmentModule augment ++ lowerRestoreModule restore))) := hasAt_append_right hparts
  have hsolve := hasAt_append_left htS
  have htC : p.HasAt copy (magnitudeCopyModule copy ++
      (residualAugmentModule augment ++ lowerRestoreModule restore)) := hasAt_append_right htS
  have hcopy := hasAt_append_left htC
  have htA : p.HasAt augment (residualAugmentModule augment ++ lowerRestoreModule restore) := hasAt_append_right htC
  have haugment := hasAt_append_left htA
  have hrestore : p.HasAt restore (lowerRestoreModule restore) := hasAt_append_right htA
  have hkR := residual_meetsContract (w := w) hres J f
  have hkS := prunedScaling_meetsContract (w := w) hproc hdet hmono hsolve R C B
  have hkC := magnitudeCopy_meetsContract (w := w) hcopy (List.ofFn delta)
  have hkA := residualAugment_meetsContract (w := w) haugment f delta
  have hkL := lowerRestore_meetsContract (w := w) hrestore entries
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,graph,flow,heap,rfl,hinputAt,hgraph,hflow,hinputEnd,hgraphEnd,hflowEnd,hf,hC,hl,hu,hinput,hJinput,hRinput,h8,hBword,h4U,hz,hs⟩ := hpre
  obtain ⟨hRcap,hd,ha⟩ := residualOptimization_bounds solver entry T hproc I hv f C U hf hC hl hu
  change (∀ e,R.capacity e≤2*U) at hRcap
  change (∀ e,0≤delta e ∧ (delta e).toNat≤2*U) at hd
  change (∀ e,0≤updated e ∧ updated e≤(2*U : ℕ)) at ha
  have h2B : 2*U≤B := by
    have hh := Nat.mul_le_mul_right U (show 2≤2*(I.m+1) by omega)
    unfold B FlowReduction.scalingCapacityBudget; omega
  have hRC : R.CostsBounded C := J.residual_costsBounded f C hC
  have hRB : ∀ e,R.capacity e≤B := fun e => (hRcap e).trans h2B
  have hBpos : 1≤B := by unfold B FlowReduction.scalingCapacityBudget; omega
  have hfNat : ∀ e,(f e).toNat≤2*U := by
    intro e
    exact (Int.toNat_le_toNat (hf e).2).trans
      (by simpa only [Int.toNat_natCast] using FlowReduction.shiftedGraph_capacity_le I hv U hl hu e)
  have hd0 : ∀ e,0≤delta e := fun e => (hd e).1
  have hdAbs : ∀ e,(delta e).natAbs<2^w := by
    intro e
    have he := congrArg Int.natAbs (Int.toNat_of_nonneg (hd0 e))
    simp only [Int.natAbs_natCast] at he
    rw [←he]
    have hh := (hd e).2
    omega
  have haNat : ∀ e,(updated e).toNat≤2*U := by
    intro e
    simpa only [Int.toNat_natCast] using Int.toNat_le_toNat (ha e).2
  have hsNum := hs
  change heap+(2+15*I.m+prunedScalingSpace R C B)<2^w at hsNum
  have hh : heap<2^w := by omega
  have haWord : a<2^w := by have hl := instance_encode_length I hv; rw [hl] at hinputEnd; omega
  have ha1 : a+1<2^w := by have hl := instance_encode_length I hv; rw [hl] at hinputEnd; omega
  have ha2 : a+2<2^w := by have hl := instance_encode_length I hv; rw [hl] at hinputEnd; omega
  have hgWord : graph<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  have hfWord : flow<2^w := by omega
  have hCword : C<2^w := hwords C (by simp)
  have hUword : U<2^w := hwords U (by simp)
  have hm : I.m<2^w := by omega
  have hm1 : I.m+1<2^w := by omega
  have h2m1 : 2*(I.m+1)<2^w := by omega
  have hprod : 2*(I.m+1)*U<2^w := by
    have hh : 2*(I.m+1)*U+1<2^w := hBword
    omega
  have h2m : I.m+I.m<2^w := by omega
  have h4m : 2*(I.m+I.m)<2^w := by omega
  have hmHead := (instance_header_at I mem a hinputAt).2
  have hedge := instance_edges_at I mem a hinputAt
  apply runs_start_le
  unfold residualOptimizationBody
  refine runs_seq_assign_le (v := I.m) (by eval_expr) ?_
  refine runs_seq_call_le hkR (vs := [graph,flow,heap]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨graph,flow,heap,rfl,hgraph,hflow,hgraphEnd,hflowEnd,hf,hJinput,h8⟩,hz,
      by change heap+(2+10*I.m)<2^w; omega⟩
  · intro residualEnd memR posR hpostR
    obtain ⟨⟨_,_,hframeR,hzR,hresidual⟩,hresidualEnd⟩ := hpostR
    change residualEnd=heap+2+10*I.m at hresidualEnd
    change ListAt memR heap R.solverWords at hresidual
    change (∀ x<heap,memR x=mem x) at hframeR
    change ZeroFrom memR residualEnd at hzR
    have hrword : residualEnd<2^w := by omega
    refine runs_seq_assign_le (v := B) ?_ ?_
    · change Expr.eval w _ _=some (2*(I.m+1)*U+1)
      eval_expr
    · refine runs_seq_call_le hkS (vs := [heap,C,B,residualEnd]) (by eval_expr) (by wram_words) ?_ ?_
      · refine ⟨heap,residualEnd,rfl,hresidual,?_,hRinput,h8,hRC,hRB,hBpos,hzR,?_⟩
        · rw [R.solverWords_length,hRm]; omega
        · omega
      · intro signedEnd memS posS hpostS
        obtain ⟨hloS,hhiS,hdeltaS,hzS,hframeS⟩ := hpostS
        change residualEnd≤signedEnd at hloS
        change signedEnd≤residualEnd+prunedScalingSpace R C B at hhiS
        change SignedTableAt memS (signedEnd-2*R.m) delta at hdeltaS
        change (∀ x<residualEnd,memS x=memR x) at hframeS
        have hsword : signedEnd<2^w := by omega
        have hflowptr : signedEnd-2*R.m<2^w := by omega
        have hflowbound : 2*R.m≤signedEnd := by rw [hRm]; omega
        refine runs_seq_assign_le (v := R.m) (by rw [hRm]; eval_expr) ?_
        refine runs_seq_call_le hkC (vs := [signedEnd-2*R.m,R.m,signedEnd])
          (by eval_expr) (by wram_words) ?_ ?_
        · refine ⟨⟨signedEnd-2*R.m,signedEnd,by rw [List.length_ofFn],hdeltaS.listAt,?_,?_,by omega⟩,hzS,?_⟩
          · rw [List.length_ofFn]; omega
          · intro z hz
            obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hz
            exact hdAbs e
          · change signedEnd+(List.ofFn delta).length<2^w
            rw [List.length_ofFn,hRm]; omega
        · intro unsignedEnd memC posC hpostC
          obtain ⟨⟨_,_,hframeC,hzC,hdeltaC⟩,hunsignedEnd⟩ := hpostC
          change unsignedEnd=signedEnd+(List.ofFn delta).length at hunsignedEnd
          rw [List.length_ofFn,hRm] at hunsignedEnd
          change ListAt memC signedEnd ((List.ofFn delta).map Int.natAbs) at hdeltaC
          rw [nonnegative_magnitudes_eq_unsigned delta hd0] at hdeltaC
          change (∀ x<signedEnd,memC x=memS x) at hframeC
          change ZeroFrom memC unsignedEnd at hzC
          have huword : unsignedEnd<2^w := by omega
          have hflowC := ((hflow.of_agree_below (h₀ := heap) ?_ hframeR).of_agree_below
            (h₀ := residualEnd) ?_ hframeS).of_agree_below (h₀ := signedEnd) ?_ hframeC
          all_goals try (rw [List.length_ofFn]; omega)
          refine runs_seq_call_le hkA (vs := [flow,signedEnd,I.m,unsignedEnd]) (by eval_expr) (by wram_words) ?_ ?_
          · refine ⟨⟨flow,signedEnd,unsignedEnd,rfl,hflowC,hdeltaC,by omega,by omega,
              fun e => (hf e).1,hd0,fun e => (ha e).1,?_,by omega⟩,hzC,?_⟩
            · intro e
              have hs := hfNat e
              have hdF := (hd (Fin.castAdd I.m e)).2
              have hdR := (hd (Fin.natAdd I.m e)).2
              exact ⟨by omega,by omega⟩
            · change unsignedEnd+I.m<2^w; omega
          · intro augmentEnd memA posA hpostA
            obtain ⟨⟨_,_,hframeA,hzA,hupdatedA⟩,haugmentEnd⟩ := hpostA
            change augmentEnd=unsignedEnd+I.m at haugmentEnd
            change ListAt memA unsignedEnd (List.ofFn (fun e => (updated e).toNat)) at hupdatedA
            change (∀ x<unsignedEnd,memA x=memC x) at hframeA
            change ZeroFrom memA augmentEnd at hzA
            have haword : augmentEnd<2^w := by omega
            have hedgeA : ListAt memA (a+2) ((entries.map Prod.fst).flatMap Edge.encode) := by
              rw [lowerRestore_entries_edges I (fun e => (updated e).toNat)]
              apply ((((hedge.of_agree_below (h₀ := heap) ?_ hframeR).of_agree_below
                (h₀ := residualEnd) ?_ hframeS).of_agree_below (h₀ := signedEnd) ?_ hframeC).of_agree_below
                  (h₀ := unsignedEnd) ?_ hframeA)
              all_goals rw [edges_encode_length]; have hlenI := instance_encode_length I hv; rw [hlenI] at hinputEnd; change a+2+8*I.m≤_; omega
            refine runs_seq_call_le hkL (vs := [a+2,unsignedEnd,I.m,augmentEnd]) (by eval_expr) (by wram_words) ?_ ?_
            · refine ⟨⟨a+2,unsignedEnd,augmentEnd,by rw [hlen],hedgeA,?_,?_,?_,?_,h8⟩,hzA,?_⟩
              · simpa only [entries,List.map_ofFn,Function.comp_def] using hupdatedA
              · rw [hlen]; have hlenI := instance_encode_length I hv; rw [hlenI] at hinputEnd; omega
              · rw [hlen]; omega
              · intro x hx
                obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hx
                have hlow := hl e
                have hup := haNat e
                change (I.edge e).lower.natAbs+(updated e).toNat<2^w
                omega
              · change augmentEnd+2*entries.length<2^w
                rw [hlen]; omega
            · intro out memL posL hpostL
              obtain ⟨⟨_,_,hframeL,hzL,hresult⟩,hout⟩ := hpostL
              change out=augmentEnd+2*entries.length at hout
              rw [hlen] at hout
              change (∀ x<augmentEnd,memL x=memA x) at hframeL
              change ZeroFrom memL out at hzL
              change ListAt memL augmentEnd ((entries.map (fun x => x.1.lower+(x.2 : ℤ))).flatMap encodeInt) at hresult
              have hresult' : SignedTableAt memL augmentEnd (fun e =>
                  (I.edge e).lower+f e+delta (Fin.castAdd I.m e)-delta (Fin.natAdd I.m e)) := by
                apply signedTableAt_of_listAt
                rwa [lowerRestore_entries_value I f delta (fun e => (ha e).1)] at hresult
              have how : out<2^w := by omega
              refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
              · change heap≤out ∧ out≤heap+residualOptimizationSpace I hv f C U ∧
                  SignedTableAt memL (out-2*I.m) (fun e =>
                    (I.edge e).lower+f e+delta (Fin.castAdd I.m e)-delta (Fin.natAdd I.m e)) ∧
                  ZeroFrom memL out ∧ ∀ x<heap,memL x=mem x
                refine ⟨by omega,?_,?_,hzL,?_⟩
                · change out≤heap+(2+15*I.m+prunedScalingSpace R C B); omega
                · have he : out-2*I.m=augmentEnd := by omega
                  rwa [he]
                · intro x hx
                  exact (hframeL x (by omega)).trans ((hframeA x (by omega)).trans
                    ((hframeC x (by omega)).trans ((hframeS x (by omega)).trans (hframeR x hx))))
              · simp only [residualOptimizationContract,residualContract,magnitudeCopyContract,
                  residualAugmentContract,lowerRestoreContract,heapContract,List.length_ofFn,hlen,
                  argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
                have hc : (prunedScalingContract w solver entry T hproc R C B).cost [heap,C,B,residualEnd] memR=
                    (prunedScalingContract w solver entry T hproc R C B).cost [] (fun _ => 0) := rfl
                change _≤(prunedScalingContract w solver entry T hproc R C B).cost [] (fun _ => 0)+2000*I.m+1000
                rw [hc,hRm,hJm]
                omega

end MinCostFlow.Scaling.Machine
