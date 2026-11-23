module

public import MinCostFlow.Scaling.CycleCandidateContract
import MinCostFlow.Scaling.CycleCandidateFacts
import MinCostFlow.Scaling.CirculationLayout
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# Computing the scattered candidate and its magnitude

The fresh flow array starts at zero. The index scatter writes the exact
candidate, and the objective scan preserves it while computing its signed
cost. A negative cost contributes its magnitude; a nonnegative cost
contributes zero. The final header points to the preserved flow array.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

private theorem neg_toNat_eq (z : ℤ) : (-z).toNat=if z<0 then z.natAbs else 0 := by
  cases z <;> simp

/-- Construct the exact unsigned cycle candidate and its objective-based
magnitude, at linear cost in the edge array and returned cycle list. -/
theorem cycleCandidate_meetsContract {w b lo : ℕ} {p : Program}
    (hp : p.HasAt b (cycleCandidateModule b)) (J : Circulation) (es : List (Fin J.m)) (u C : ℕ) :
    MeetsContract w p b (cycleCandidateContract w lo J es u C) := by
  let f := Scatter.write (fun _ : Fin J.m => (0 : ℕ)) (es.map (fun e => (e,u)))
  let cost := J.integerObjective (fun e => (f e : ℤ))
  have ht := hasAt_tail hp
  have hl := hasAt_append_left ht
  have hScatter := hasAt_append_left hl
  have hObjective : p.HasAt (b+2) (integerObjectiveModule (b+2)) := by
    simpa only [indexScatterModule,List.length_cons,List.length_nil,Nat.add_assoc] using hasAt_append_right hl
  have hPair : p.HasAt (b+2+(integerObjectiveModule (b+2)).length) wordPairModule := by
    simpa only [indexScatterModule,List.length_append,List.length_cons,List.length_nil,←Nat.add_assoc,Nat.reduceAdd] using hasAt_append_right ht
  have hkO := integerObjective_meetsContract (w := w) hObjective J f
  have hkP := wordPair_meetsContract (w := w) hPair
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,ptr,heap,rfl,hgraph,hgraphEnd,hlist,hinput,hcosts,hbudget,hz,hspace,hw⟩ := hpre
  have hkS := indexScatter_meetsContract (w := w) (lo := lo) (bound := heap) hScatter (fun _ : Fin J.m => 0) es u
  have ha1 : a+1<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  have hh : heap<2^w := by omega
  have hhM : heap+J.m<2^w := by omega
  have hm : J.m<2^w := by omega
  have hptrWord : ptr<2^w := hlist.pointer_le.trans_lt hh
  have hu : u<2^w := hwords _ (by simp)
  have hzero : ListAt mem heap (List.ofFn (fun _ : Fin J.m => (0 : ℕ))) := by
    intro i hi
    change mem (heap+i)=(List.ofFn (fun _ : Fin J.m => (0 : ℕ)))[i]
    rw [hz _ (by omega),List.getElem_ofFn]
  have hM := (solver_header_at J hgraph).2
  have hf : ∀ e,f e<2^w := fun e =>
    (scatter_constant_le (fun _ => 0) es u (fun _ => Nat.zero_le u) e).trans_lt hu
  have hmass : objectiveScanMass J f (List.finRange J.m)<2^w :=
    (scatter_constant_objective_mass J es u C hcosts).trans_lt hbudget
  have hcostWord : cost.natAbs<2^w := by
    have h := (objectiveScan_natAbs_le J f (List.finRange J.m)).trans_lt hmass
    simpa only [objectiveScan_finRange] using h
  apply runs_start_le
  unfold cycleCandidateBody
  refine runs_seq_assign_le (v := J.m) (by eval_expr) ?_
  refine runs_seq_assign_le (v := heap+J.m) (by eval_expr) ?_
  refine runs_seq_call_le hkS (vs := [ptr,u,heap]) (by eval_expr) (by wram_words)
    ⟨ptr,heap,rfl,hlist,hzero,le_rfl,hhM,by omega⟩ ?_
  intro scatterRet memS posS hpostS
  obtain ⟨_,htableS,hframeS⟩ := hpostS
  change ListAt memS heap (List.ofFn f) at htableS
  change (∀ x,x<heap ∨ heap+J.m≤x → memS x=mem x) at hframeS
  have hgraphS : ListAt memS a J.solverWords :=
    hgraph.of_agree_below (h₀ := heap) hgraphEnd (fun x hx => hframeS x (Or.inl hx))
  have hzS : ZeroFrom memS (heap+J.m) := by
    intro x hx
    exact (hframeS x (Or.inr hx)).trans (hz x (by omega))
  refine runs_seq_call_le hkO (vs := [a,heap,heap+J.m]) (by eval_expr) (by wram_words)
    ⟨⟨a,heap,heap+J.m,rfl,hgraphS,htableS,by omega,le_rfl,hinput,hf,hmass,hw⟩,
      hzS,by change heap+J.m+(4*J.m+2)<2^w; omega⟩ ?_
  intro objectiveEnd memO posO hpostO
  obtain ⟨⟨_,_,hframeO,hzO,_⟩,hobjectiveEnd,hsigned⟩ := hpostO
  change objectiveEnd=heap+J.m+4*J.m+2 at hobjectiveEnd
  change (∀ x<heap+J.m,memO x=memS x) at hframeO
  change ZeroFrom memO objectiveEnd at hzO
  change ListAt memO (objectiveEnd-2) (encodeInt cost) at hsigned
  have htableO := htableS.of_agree_below (h₀ := heap+J.m)
    (by simp only [List.length_ofFn]; omega) hframeO
  have hsign : memO (objectiveEnd-2)=(if cost<0 then 1 else 0) := by
    have h : memO (objectiveEnd-2+0)=(if cost<0 then 1 else 0) := hsigned 0 (by change 0<2; decide)
    simpa only [Nat.add_zero] using h
  have hmag : memO (objectiveEnd-1)=cost.natAbs := by
    have h : memO (objectiveEnd-2+1)=cost.natAbs := hsigned 1 (by change 1<2; decide)
    have heq : objectiveEnd-2+1=objectiveEnd-1 := by omega
    simpa only [heq] using h
  have ho : objectiveEnd<2^w := by omega
  have ho1 : objectiveEnd-1<2^w := by omega
  have ho2 : objectiveEnd-2<2^w := by omega
  have hsignRaw : memO (heap+J.m+4*J.m+2-2)=(if cost<0 then 1 else 0) := by rw [←hobjectiveEnd]; exact hsign
  have hmagRaw : memO (heap+J.m+4*J.m+2-1)=cost.natAbs := by rw [←hobjectiveEnd]; exact hmag
  have hsignWord : (if cost<0 then 1 else 0 : ℕ)<2^w := by split <;> omega
  refine runs_seq_assign_le (v := if cost<0 then 1 else 0) (by eval_expr) ?_
  wram_step
  · have hnegative : cost<0 := hcond
    unfold cycleCandidateWrite
    refine runs_seq_call_le hkP (vs := [heap,cost.natAbs,objectiveEnd]) (by eval_expr) (by wram_words)
      ⟨⟨heap,cost.natAbs,objectiveEnd,rfl⟩,hzO,by change objectiveEnd+2<2^w; omega⟩ ?_
    intro ret memP posP hpostP
    obtain ⟨⟨_,_,hframeP,hzP,hheaderP⟩,hret⟩ := hpostP
    change ret=objectiveEnd+2 at hret
    change (∀ x<objectiveEnd,memP x=memO x) at hframeP
    refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
    · change ret=heap+5*J.m+4 ∧ ListAt memP heap (List.ofFn f) ∧
        ListAt memP (ret-2) [heap,(-cost).toNat] ∧ ZeroFrom memP ret ∧ ∀ x<heap,memP x=mem x
      refine ⟨by omega,htableO.of_agree_below (h₀ := objectiveEnd)
        (by simp only [List.length_ofFn]; omega) hframeP,?_,hzP,?_⟩
      · have hptr : ret-2=objectiveEnd := by omega
        rw [hptr,neg_toNat_eq,ite_eq_left hnegative]
        exact hheaderP
      · intro x hx
        exact (hframeP x (by omega)).trans ((hframeO x (by omega)).trans (hframeS x (Or.inl hx)))
    · simp only [cycleCandidateContract,indexScatterContract,integerObjectiveContract,wordPairContract,
        heapContract,argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
      omega
  · have hnonnegative : ¬cost<0 := hcond
    unfold cycleCandidateWrite
    refine runs_seq_call_le hkP (vs := [heap,0,objectiveEnd]) (by eval_expr) (by wram_words)
      ⟨⟨heap,0,objectiveEnd,rfl⟩,hzO,by change objectiveEnd+2<2^w; omega⟩ ?_
    intro ret memP posP hpostP
    obtain ⟨⟨_,_,hframeP,hzP,hheaderP⟩,hret⟩ := hpostP
    change ret=objectiveEnd+2 at hret
    change (∀ x<objectiveEnd,memP x=memO x) at hframeP
    refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
    · change ret=heap+5*J.m+4 ∧ ListAt memP heap (List.ofFn f) ∧
        ListAt memP (ret-2) [heap,(-cost).toNat] ∧ ZeroFrom memP ret ∧ ∀ x<heap,memP x=mem x
      refine ⟨by omega,htableO.of_agree_below (h₀ := objectiveEnd)
        (by simp only [List.length_ofFn]; omega) hframeP,?_,hzP,?_⟩
      · have hptr : ret-2=objectiveEnd := by omega
        rw [hptr,neg_toNat_eq,ite_eq_right hnonnegative]
        exact hheaderP
      · intro x hx
        exact (hframeP x (by omega)).trans ((hframeO x (by omega)).trans (hframeS x (Or.inl hx)))
    · simp only [cycleCandidateContract,indexScatterContract,integerObjectiveContract,wordPairContract,
        heapContract,argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
      omega

/-- A returned cycle of at most `m` edges gives a linear graph-size
candidate-construction cost. -/
theorem cycleCandidate_cost_le (w lo : ℕ) (J : Circulation) (es : List (Fin J.m)) (u C : ℕ)
    (hsize : es.length≤J.m) (args : List ℕ) (mem : ℕ → ℕ) :
    (cycleCandidateContract w lo J es u C).cost args mem≤600*(J.m+1) := by
  change 500*J.m+60*es.length+500≤600*(J.m+1)
  omega

end MinCostFlow.Scaling.Machine
