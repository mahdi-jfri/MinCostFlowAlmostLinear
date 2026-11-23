module

public import MinCostFlow.IPM.Machine.PrecisionSelection
public import MinCostFlow.Num.IPM.Alpha
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Selecting parameters and storing the barrier exponent

The parameter record is computed first. Its precision and limb count
are loaded and passed to the numerical exponent routine. The output
block stores `alphaPrime` exactly in the selected format, so later
coefficient routines read a machine-produced exponent.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[m,U,heap]`. The alpha header and block follow the record. -/
def precisionAlphaBody (select alpha : ℕ) : Stmt :=
  .call 3 select [.reg 0,.reg 1,.reg 2] ;;
  .assign 4 (.load (.bin .add (.reg 2) (.const 4))) ;;
  .assign 5 (.load (.bin .add (.reg 2) (.const 5))) ;;
  .call 6 alpha [.reg 0,.reg 1,.reg 5,.reg 4,.reg 3] ;;
  .ret (.reg 6)

/-- Parameter selection followed by the verified dyadic-exponent module. -/
def precisionAlphaModule (b : ℕ) : List Stmt :=
  [precisionAlphaBody (b+1) (b+6)] ++
    (precisionSelectionModule (b+1) ++ Num.IPM.alphaModule (b+6) 4)

/-- Six parameter words, one exponent header and one exact alpha block.
The selected format and every arithmetic margin follow from the input. -/
def precisionAlphaContract (w : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ m U heap,args=[m,U,heap] ∧ 2 ≤ m*U ∧ ipmParameterWordBits m U ≤ w)
    (fun args _ mem' =>
      ListAt mem' (heapArg args) (precisionWords (args.getD 0 0) (args.getD 1 0)) ∧
      mem' (heapArg args+6)=Num.IPM.alphaExponent (args.getD 0 0) (args.getD 1 0) ∧
      ScalarAt mem' (heapArg args+7) 4
        (ipmLimbs (args.getD 0 0) (args.getD 1 0))
        (ipmPrecision (args.getD 0 0) (args.getD 1 0))
        (Num.IPM.alphaPrime (args.getD 0 0) (args.getD 1 0)))
    (fun args _ => 20028*((args.getD 0 0).size+(args.getD 1 0).size)+20700)
    (fun args _ => 7+ipmLimbs (args.getD 0 0) (args.getD 1 0))
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧
    v=heapArg args+7+ipmLimbs (args.getD 0 0) (args.getD 1 0)}

/-- Both the selection and exponent-storage procedures are deterministic. -/
theorem precisionAlphaModule_noRand (b : ℕ) :
    ∀ body ∈ precisionAlphaModule b,body.NoRand := by
  intro body hb
  simp only [precisionAlphaModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb | hb
  · simp [precisionAlphaBody,Stmt.NoRand]
  · exact precisionSelectionModule_noRand _ _ hb
  · exact Num.IPM.alphaModule_noRand _ _ _ hb

/-- All parameters and the exact stored exponent are produced by a
terminating deterministic machine program with the stated cost. -/
theorem precisionAlpha_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (precisionAlphaModule b)) :
    MeetsContract w p b (precisionAlphaContract w) := by
  have htail := Num.hasAt_append_right hp
  have hselect : p.HasAt (b+1) (precisionSelectionModule (b+1)) := Num.hasAt_append_left htail
  have halpha : p.HasAt (b+6) (Num.IPM.alphaModule (b+6) 4) := by
    simpa [precisionSelectionModule,precisionRangeModule,precisionRecordModule,Num.IPM.bitLengthModule]
      using Num.hasAt_append_right htail
  have hselectSpec := precisionSelection_meetsContract (w:=w) hselect
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨m,U,heap,rfl,hsize,hw⟩,hzero,hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap+(7+ipmLimbs m U) < 2^w at hspace
  have hfits := ipm_parameter_words_fit m U hw
  have hmargin := ipm_precision_margins m U
  have halphaSpec := Num.IPM.alpha_meetsContract (by decide : 0 < 4)
    (by have hh := hfits.1; omega : 2*4+2 ≤ w) halpha
  have hm : m < 2^w := hwords _ (by simp)
  have hU : U < 2^w := hwords _ (by simp)
  have hheap : heap < 2^w := hwords _ (by simp)
  have hL : ipmLimbs m U < 2^w := hfits.2.1
  have hP : ipmPrecision m U < 2^w := hfits.2.2.1
  have hwidth : ipmPrecision m U+2 ≤ 4*ipmLimbs m U := by
    have hh := hmargin.2.2.2.1
    omega
  apply runs_start_le
  unfold precisionAlphaBody
  refine runs_seq_call_le hselectSpec (vs:=[m,U,heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨m,U,heap,rfl,hsize,hw⟩,hzero,by change heap+6 < 2^w; omega⟩
  · intro endRecord mem1 pos1 hp1
    obtain ⟨⟨hlo1,hhi1,hframe1,hzero1,hrecord⟩,hend⟩ := hp1
    change endRecord=heap+6 at hend
    change ListAt mem1 heap (precisionWords m U) at hrecord
    change ∀ x < heap,mem1 x=mem x at hframe1
    have hPr : mem1 (heap+4)=ipmPrecision m U := by
      simpa [precisionWords] using hrecord.getElem (i:=4) (by simp [precisionWords])
    have hLr : mem1 (heap+5)=ipmLimbs m U := by
      simpa [precisionWords] using hrecord.getElem (i:=5) (by simp [precisionWords])
    have hendw : endRecord < 2^w := by omega
    have hspaceAlpha : endRecord+(ipmLimbs m U+1) < 2^w := by omega
    wram_step
    wram_step
    refine runs_seq_call_le halphaSpec
      (vs:=[m,U,ipmLimbs m U,ipmPrecision m U,endRecord]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · refine ⟨⟨m,U,ipmLimbs m U,ipmPrecision m U,endRecord,rfl,hsize,
        hmargin.2.2.2.2.2,hwidth,hfits.2.2.2.2.2.2.1⟩,hzero1,?_⟩
      change endRecord+(ipmLimbs m U+1) < 2^w
      omega
    · intro v mem2 pos2 hp2
      obtain ⟨hv,hlo2,hhi2,hframe2,hzero2,hheader,hvalid,hvalue⟩ := hp2
      change v=endRecord+(ipmLimbs m U+1) at hv
      change mem2 endRecord=Num.IPM.alphaExponent m U at hheader
      change Num.Valid mem2 (endRecord+1) 4 (ipmLimbs m U) at hvalid
      change Num.fixVal mem2 (endRecord+1) 4 (ipmLimbs m U) (ipmPrecision m U)=
        Num.IPM.alphaPrime m U at hvalue
      change ∀ x < endRecord,mem2 x=mem1 x at hframe2
      change endRecord ≤ v at hlo2
      have hvw : v < 2^w := hhi2.trans_lt hspaceAlpha
      have hrecord2 : ListAt mem2 heap (precisionWords m U) :=
        hrecord.of_agree_below (by simp [precisionWords]; omega) hframe2
      refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
      · change (heap ≤ v ∧ v ≤ heap+(7+ipmLimbs m U) ∧
          (∀ x < heap,mem2 x=mem x) ∧ ZeroFrom mem2 v ∧
          ListAt mem2 heap (precisionWords m U) ∧ mem2 (heap+6)=Num.IPM.alphaExponent m U ∧
          ScalarAt mem2 (heap+7) 4 (ipmLimbs m U) (ipmPrecision m U) (Num.IPM.alphaPrime m U)) ∧
          v=heap+7+ipmLimbs m U
        refine ⟨⟨by omega,by omega,?_,hzero2,hrecord2,?_,?_,?_⟩,by omega⟩
        · intro x hx
          exact (hframe2 x (by omega)).trans (hframe1 x hx)
        · simpa only [hend] using hheader
        · simpa only [hend,show heap+6+1=heap+7 by omega] using hvalid
        · simpa only [hend,show heap+6+1=heap+7 by omega] using hvalue
      · simp [precisionAlphaContract,heapContract,precisionSelectionContract,Num.IPM.alphaContract,
          argsSize,startState,Expr.size_bin,Expr.size_reg,Expr.size_const]
        omega

/-- Exact alpha storage and the selected parameter record coexist in
an actual run on every tape, with all local width and space premises. -/
theorem precisionAlpha_example :
    let p : Program := ⟨precisionAlphaModule 0⟩
    p.IsDeterministic ∧ ∀ ω : ℕ → Bool,
      ∃ o st c,Runs 64 p ω (precisionAlphaBody 1 6)
        (startState [1,2,0] (fun _ => 0) 0) o st c ∧
        (precisionAlphaContract 64).post [1,2,0] (fun _ => 0) o.value st.mem ∧ c ≤ 80784 := by
  dsimp only
  have hplace : (⟨precisionAlphaModule 0⟩ : Program).HasAt 0 (precisionAlphaModule 0) := by
    intro i hi
    simp only [Nat.zero_add,List.getElem?_eq_getElem hi]
  have hmet := precisionAlpha_meetsContract (w:=64) hplace
  constructor
  · exact precisionAlphaModule_noRand 0
  · intro ω
    have hpre : (precisionAlphaContract 64).pre [1,2,0] (fun _ => 0) := by
      refine ⟨⟨1,2,0,rfl,by decide,by decide⟩,?_,by decide⟩
      intro x _
      rfl
    obtain ⟨body,hbody,o,st,c,hr,hpost,hcost⟩ := hmet [1,2,0] (fun _ => 0) 0 ω
      (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> decide) hpre
    have he : body=precisionAlphaBody 1 6 := by
      simpa [precisionAlphaModule] using hbody.symm
    subst body
    refine ⟨o,st,c,hr,hpost,?_⟩
    simpa [precisionAlphaContract,heapContract,show Nat.size 1=1 by decide,
      show Nat.size 2=2 by decide] using hcost

/-- Arguments `[m,U,k,heap]`. The alpha header and block follow the record. -/
def qualityPrecisionAlphaBody (select alpha : ℕ) : Stmt :=
  .call 4 select [.reg 0,.reg 1,.reg 2,.reg 3] ;;
  .assign 5 (.load (.bin .add (.reg 3) (.const 4))) ;;
  .assign 6 (.load (.bin .add (.reg 3) (.const 5))) ;;
  .call 7 alpha [.reg 0,.reg 1,.reg 6,.reg 5,.reg 4] ;;
  .ret (.reg 7)

/-- Parameter selection followed by the verified dyadic-exponent module. -/
def qualityPrecisionAlphaModule (b : ℕ) : List Stmt :=
  [qualityPrecisionAlphaBody (b+1) (b+6)] ++
    (qualityPrecisionSelectionModule (b+1) ++ Num.IPM.alphaModule (b+6) 4)

/-- Six parameter words, one exponent header and one exact alpha block.
The selected format and every arithmetic margin follow from the input. -/
def qualityPrecisionAlphaContract (w : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ m U k heap,args=[m,U,k,heap] ∧ 2 ≤ m*U ∧ ipmQualityParameterWordBits m U k ≤ w)
    (fun args _ mem' =>
      ListAt mem' (heapArg args) (qualityPrecisionWords (args.getD 0 0) (args.getD 1 0) (args.getD 2 0)) ∧
      mem' (heapArg args+6)=Num.IPM.alphaExponent (args.getD 0 0) (args.getD 1 0) ∧
      ScalarAt mem' (heapArg args+7) 4
        (ipmQualityLimbs (args.getD 0 0) (args.getD 1 0) (args.getD 2 0))
        (ipmQualityPrecision (args.getD 0 0) (args.getD 1 0) (args.getD 2 0))
        (Num.IPM.alphaPrime (args.getD 0 0) (args.getD 1 0)))
    (fun args _ => 20028*((args.getD 0 0).size+(args.getD 1 0).size)+20710)
    (fun args _ => 7+ipmQualityLimbs (args.getD 0 0) (args.getD 1 0) (args.getD 2 0))
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧
    v=heapArg args+7+ipmQualityLimbs (args.getD 0 0) (args.getD 1 0) (args.getD 2 0)}

/-- Both the selection and exponent-storage procedures are deterministic. -/
theorem qualityPrecisionAlphaModule_noRand (b : ℕ) :
    ∀ body ∈ qualityPrecisionAlphaModule b,body.NoRand := by
  intro body hb
  simp only [qualityPrecisionAlphaModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb | hb
  · simp [qualityPrecisionAlphaBody,Stmt.NoRand]
  · exact qualityPrecisionSelectionModule_noRand _ _ hb
  · exact Num.IPM.alphaModule_noRand _ _ _ hb

/-- All parameters and the exact stored exponent are produced by a
terminating deterministic machine program with the stated cost. -/
theorem qualityPrecisionAlpha_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (qualityPrecisionAlphaModule b)) :
    MeetsContract w p b (qualityPrecisionAlphaContract w) := by
  have htail := Num.hasAt_append_right hp
  have hselect : p.HasAt (b+1) (qualityPrecisionSelectionModule (b+1)) := Num.hasAt_append_left htail
  have halpha : p.HasAt (b+6) (Num.IPM.alphaModule (b+6) 4) := by
    simpa [qualityPrecisionSelectionModule,precisionRangeModule,precisionRecordModule,Num.IPM.bitLengthModule]
      using Num.hasAt_append_right htail
  have hselectSpec := qualityPrecisionSelection_meetsContract (w:=w) hselect
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨m,U,k,heap,rfl,hsize,hw⟩,hzero,hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap+(7+ipmQualityLimbs m U k) < 2^w at hspace
  have hfits := ipm_quality_parameter_words_fit m U k hw
  have hmargin := ipm_quality_precision_margins m U k
  have halphaSpec := Num.IPM.alpha_meetsContract (by decide : 0 < 4)
    (by have hh := hfits.1; omega : 2*4+2 ≤ w) halpha
  have hm : m < 2^w := hwords _ (by simp)
  have hU : U < 2^w := hwords _ (by simp)
  have hk : k < 2^w := hwords _ (by simp)
  have hheap : heap < 2^w := hwords _ (by simp)
  have hL : ipmQualityLimbs m U k < 2^w := hfits.2.1
  have hP : ipmQualityPrecision m U k < 2^w := hfits.2.2.1
  have hwidth : ipmQualityPrecision m U k+2 ≤ 4*ipmQualityLimbs m U k := by
    have hh := hmargin.2.2.2.1
    omega
  apply runs_start_le
  unfold qualityPrecisionAlphaBody
  refine runs_seq_call_le hselectSpec (vs:=[m,U,k,heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨m,U,k,heap,rfl,hsize,hw⟩,hzero,by change heap+6 < 2^w; omega⟩
  · intro endRecord mem1 pos1 hp1
    obtain ⟨⟨hlo1,hhi1,hframe1,hzero1,hrecord⟩,hend⟩ := hp1
    change endRecord=heap+6 at hend
    change ListAt mem1 heap (qualityPrecisionWords m U k) at hrecord
    change ∀ x < heap,mem1 x=mem x at hframe1
    have hPr : mem1 (heap+4)=ipmQualityPrecision m U k := by
      simpa [qualityPrecisionWords] using hrecord.getElem (i:=4) (by simp [qualityPrecisionWords])
    have hLr : mem1 (heap+5)=ipmQualityLimbs m U k := by
      simpa [qualityPrecisionWords] using hrecord.getElem (i:=5) (by simp [qualityPrecisionWords])
    have hendw : endRecord < 2^w := by omega
    have hspaceAlpha : endRecord+(ipmQualityLimbs m U k+1) < 2^w := by omega
    wram_step
    wram_step
    refine runs_seq_call_le halphaSpec
      (vs:=[m,U,ipmQualityLimbs m U k,ipmQualityPrecision m U k,endRecord]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · refine ⟨⟨m,U,ipmQualityLimbs m U k,ipmQualityPrecision m U k,endRecord,rfl,hsize,
        hmargin.2.2.2.2.2,hwidth,hfits.2.2.2.2.2.2.1⟩,hzero1,?_⟩
      change endRecord+(ipmQualityLimbs m U k+1) < 2^w
      omega
    · intro v mem2 pos2 hp2
      obtain ⟨hv,hlo2,hhi2,hframe2,hzero2,hheader,hvalid,hvalue⟩ := hp2
      change v=endRecord+(ipmQualityLimbs m U k+1) at hv
      change mem2 endRecord=Num.IPM.alphaExponent m U at hheader
      change Num.Valid mem2 (endRecord+1) 4 (ipmQualityLimbs m U k) at hvalid
      change Num.fixVal mem2 (endRecord+1) 4 (ipmQualityLimbs m U k) (ipmQualityPrecision m U k)=
        Num.IPM.alphaPrime m U at hvalue
      change ∀ x < endRecord,mem2 x=mem1 x at hframe2
      change endRecord ≤ v at hlo2
      have hvw : v < 2^w := hhi2.trans_lt hspaceAlpha
      have hrecord2 : ListAt mem2 heap (qualityPrecisionWords m U k) :=
        hrecord.of_agree_below (by simp [qualityPrecisionWords]; omega) hframe2
      refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
      · change (heap ≤ v ∧ v ≤ heap+(7+ipmQualityLimbs m U k) ∧
          (∀ x < heap,mem2 x=mem x) ∧ ZeroFrom mem2 v ∧
          ListAt mem2 heap (qualityPrecisionWords m U k) ∧ mem2 (heap+6)=Num.IPM.alphaExponent m U ∧
          ScalarAt mem2 (heap+7) 4 (ipmQualityLimbs m U k) (ipmQualityPrecision m U k) (Num.IPM.alphaPrime m U)) ∧
          v=heap+7+ipmQualityLimbs m U k
        refine ⟨⟨by omega,by omega,?_,hzero2,hrecord2,?_,?_,?_⟩,by omega⟩
        · intro x hx
          exact (hframe2 x (by omega)).trans (hframe1 x hx)
        · simpa only [hend] using hheader
        · simpa only [hend,show heap+6+1=heap+7 by omega] using hvalid
        · simpa only [hend,show heap+6+1=heap+7 by omega] using hvalue
      · simp [qualityPrecisionAlphaContract,heapContract,qualityPrecisionSelectionContract,Num.IPM.alphaContract,
          argsSize,startState,Expr.size_bin,Expr.size_reg,Expr.size_const]
        omega

end MinCostFlow.IPM.Machine
