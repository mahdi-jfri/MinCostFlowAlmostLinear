module

public import MinCostFlow.Scaling.CapacityScaledEdgesProgram
public import MinCostFlow.Scaling.CapacityPowerProgram
public import MinCostFlow.Scaling.WordPairProgram
import MinCostFlow.Scaling.CirculationLayout
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# Constructing the complete scaled capacity-rounded circulation

Read the dimensions, compute `m^20` and the rounding unit once, write the
unchanged graph header, and scan the edge records with those shared values.
The result is precisely `scaledRoundedInstance`, whose capacities are the
corrected clipped quantities of Definition C.11.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,B,heap]`. -/
def capacityScaledGraphBody (power unit header scan : ℕ) : Stmt :=
  .assign 3 (.load (.reg 0)) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 5 power [.reg 4] ;;
  .call 6 unit [.reg 5,.reg 1] ;;
  .call 7 header [.reg 3,.reg 4,.reg 2] ;;
  .call 8 scan [.bin .add (.reg 0) (.const 2),.reg 4,.reg 4,.reg 1,.reg 5,.reg 6,.reg 7] ;;
  .ret (.reg 8)

/-- Entry, shared power/unit, header writer, and complete edge scan. -/
def capacityScaledGraphModule (b : ℕ) : List Stmt :=
  capacityScaledGraphBody (b+1) (b+2) (b+3) (b+4) ::
    capacityPowerBody :: capacityUnitBody :: wordPairBody :: capacityScaledEdgesModule (b+4)

/-- Positive edge and rounding counts are the branch in which the rounded
solver constructs a graph. The single clipping product covers all arithmetic. -/
def capacityScaledGraphContract (w : ℕ) (J : Circulation) (B : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a heap,args = [a,B,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length ≤ heap ∧ (∀ x ∈ J.solverWords,x < 2^w) ∧
      0 < J.m ∧ 0 < B ∧ B*J.m^20 < 2^w ∧ 8 < 2^w)
    (fun args _ mem' => ListAt mem' (heapArg args) (J.scaledRoundedInstance B).solverWords)
    (fun _ _ => 200*J.m+300) (fun _ _ => 2+5*J.m)
  { C with post := fun args mem ret mem' => C.post args mem ret mem' ∧ ret = heapArg args+2+5*J.m }

/-- Every constructor procedure uses no random instruction. -/
theorem capacityScaledGraphModule_noRand (b : ℕ) :
    ∀ body ∈ capacityScaledGraphModule b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [capacityScaledGraphBody,Stmt.NoRand,and_self]
  · rcases List.mem_cons.mp hb with rfl | hb
    · exact capacityPowerBody_noRand
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact capacityUnitBody_noRand
      · rcases List.mem_cons.mp hb with rfl | hb
        · exact wordPairBody_noRand
        · exact capacityScaledEdgesModule_noRand _ body hb

/-- The complete constructor writes exactly the model's scaled rounded
circulation, with shared constant-time preprocessing and linear scan cost. -/
theorem capacityScaledGraph_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (capacityScaledGraphModule b)) (J : Circulation) (B : ℕ) :
    MeetsContract w p b (capacityScaledGraphContract w J B) := by
  have hpower : p.HasAt (b+1) capacityPowerModule := by
    intro i hi
    have hi0 : i = 0 := by change i<1 at hi; omega
    subst i
    simpa only [capacityPowerModule,capacityScaledGraphModule,List.getElem_cons_succ,
      List.getElem_cons_zero,Nat.add_zero] using hp 1 (by simp [capacityScaledGraphModule])
  have hunit : p.HasAt (b+2) capacityUnitModule := by
    intro i hi
    have hi0 : i = 0 := by change i<1 at hi; omega
    subst i
    simpa only [capacityUnitModule,capacityScaledGraphModule,List.getElem_cons_succ,
      List.getElem_cons_zero,Nat.add_zero] using hp 2 (by simp [capacityScaledGraphModule])
  have hheader : p.HasAt (b+3) wordPairModule := by
    intro i hi
    have hi0 : i = 0 := by change i<1 at hi; omega
    subst i
    simpa only [wordPairModule,capacityScaledGraphModule,List.getElem_cons_succ,
      List.getElem_cons_zero,Nat.add_zero] using hp 3 (by simp [capacityScaledGraphModule])
  have hscan : p.HasAt (b+4) (capacityScaledEdgesModule (b+4)) := by
    have h := hasAt_tail (hasAt_tail (hasAt_tail (hasAt_tail hp)))
    simpa only [Nat.add_assoc,Nat.reduceAdd] using h
  have hkP := capacityPower_meetsContract (w := w) hpower J.m
  have hkU := capacityUnit_meetsContract (w := w) hunit J.m B
  have hkH := wordPair_meetsContract (w := w) hheader
  have hkS := capacityScaledEdges_meetsContract (w := w) hscan J B (List.finRange J.m)
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a,heap,rfl,hat,hend,hinput,hmpos,hBpos,hproduct,hw⟩,hz,hs⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+(2+5*J.m) < 2^w at hs
  have hn : J.n < 2^w := hinput _ List.mem_cons_self
  have hm : J.m < 2^w := hinput _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hB : B < 2^w := hwords _ (by simp)
  have hpow : J.m^20 < 2^w := by
    have hp : J.m^20 ≤ B*J.m^20 := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right (J.m^20) (Nat.succ_le_of_lt hBpos)
    exact hp.trans_lt hproduct
  have hunitWord : capacityUnit J.m B < 2^w := (capacityUnit_le J.m B hmpos hBpos).trans_lt hB
  have hh : heap < 2^w := by omega
  have hh2 : heap+2 < 2^w := by omega
  have ha1 : a+1 < 2^w := by rw [J.solverWords_length] at hend; omega
  have ha2 : a+2 < 2^w := by rw [J.solverWords_length] at hend; omega
  have hheaderMem := solver_header_at J hat
  obtain ⟨hN,hM⟩ := hheaderMem
  have hedge : ListAt mem (a+2) ((List.finRange J.m).flatMap J.solverEdgeWords) := by
    have h := (listAt_cons.mp (listAt_cons.mp hat).2).2
    simpa only [Nat.add_assoc] using h
  have hrecordWords : ∀ e ∈ List.finRange J.m,∀ x ∈ J.solverEdgeWords e,x < 2^w := by
    intro e _ x hx
    exact hinput x (J.solverEdgeWord_mem e hx)
  apply runs_start_le
  unfold capacityScaledGraphBody
  refine runs_seq_assign_le (v := J.n) (by eval_expr) ?_
  refine runs_seq_assign_le (v := J.m) (by eval_expr) ?_
  refine runs_seq_call_le hkP (vs := [J.m]) (by eval_expr) (by wram_words) ⟨rfl,hpow⟩ ?_
  intro power memP posP hpostP
  obtain ⟨hmemP,hpowerEq⟩ := hpostP
  subst memP
  subst power
  refine runs_seq_call_le hkU (vs := [J.m^20,B]) (by eval_expr) (by wram_words)
    ⟨rfl,hmpos,hBpos,hB⟩ ?_
  intro unit memU posU hpostU
  obtain ⟨hmemU,hunitEq⟩ := hpostU
  subst memU
  subst unit
  refine runs_seq_call_le hkH (vs := [J.n,J.m,heap]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨_,_,heap,rfl⟩,hz,hh2⟩
  · intro records memH posH hpostH
    obtain ⟨⟨_,_,hframeH,hzH,hatH⟩,hrecords⟩ := hpostH
    change records = heap+2 at hrecords
    change (∀ x < heap,memH x = mem x) at hframeH
    change ZeroFrom memH records at hzH
    change ListAt memH heap [J.n,J.m] at hatH
    have hedgeH := hedge.of_agree_below (h₀ := heap) (by
      rw [J.solverEdgeRecords_length,List.length_finRange]
      rw [J.solverWords_length] at hend
      omega) hframeH
    have hrecordsWord : records < 2^w := by omega
    refine runs_seq_call_le hkS
      (vs := [a+2,J.m,J.m,B,J.m^20,capacityUnit J.m B,records]) (by eval_expr) (by wram_words) ?_ ?_
    · refine ⟨⟨a+2,records,by simp only [List.length_finRange],hedgeH,?_,hrecordWords,hproduct,hw⟩,hzH,?_⟩
      · rw [List.length_finRange]
        rw [J.solverWords_length] at hend
        omega
      · change records+5*(List.finRange J.m).length < 2^w
        rw [List.length_finRange]
        omega
    · intro ret memS posS hpostS
      obtain ⟨⟨_,_,hframeS,hzS,hatS⟩,hret⟩ := hpostS
      change ret = records+5*(List.finRange J.m).length at hret
      rw [List.length_finRange] at hret
      change (∀ x < records,memS x = memH x) at hframeS
      change ZeroFrom memS ret at hzS
      change ListAt memS records ((List.finRange J.m).flatMap (J.scaledRoundedInstance B).solverEdgeWords) at hatS
      have hr : ret < 2^w := by omega
      refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
      · change (heap ≤ ret ∧ ret ≤ heap+(2+5*J.m) ∧ (∀ x < heap,memS x = mem x) ∧
          ZeroFrom memS ret ∧ ListAt memS heap (J.scaledRoundedInstance B).solverWords) ∧ ret = heap+2+5*J.m
        refine ⟨⟨by omega,by omega,?_,hzS,?_⟩,by omega⟩
        · intro x hx
          exact (hframeS x (by omega)).trans (hframeH x hx)
        · have hheadS := hatH.of_agree_below (h₀ := records) (by change heap+2 ≤ records; omega) hframeS
          change ListAt memS heap ([J.n,J.m] ++ ((List.finRange J.m).flatMap (J.scaledRoundedInstance B).solverEdgeWords))
          apply listAt_append.mpr
          exact ⟨hheadS,by simpa only [List.length_cons,List.length_nil,Nat.reduceAdd,hrecords] using hatS⟩
      · simp only [capacityScaledGraphContract,capacityPowerContract,capacityUnitContract,
          wordPairContract,capacityScaledEdgesContract,heapContract,List.length_finRange,
          argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
        omega

end MinCostFlow.Scaling.Machine
