module

public import MinCostFlow.IPM.Machine.PrecisionRangeProgram
import WordRAM.Tactic
import WordRAM.Memory
import Mathlib.Tactic.IntervalCases

/-!
# Writing the chosen fixed-point parameters

After binary-length scans and range selection, this arithmetic kernel
writes the six parameters used by the IPM. The layout is slack range,
coefficient range, common DS range, error bits, precision, limb count.
All values come from the input bit lengths and the previously computed
slack exponent. Its cost is constant and all scratch allocation is counted.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The parameter-record layout `[Es,K,R,q,P,L]`. -/
def precisionWords (m U : ℕ) : List ℕ :=
  [slackRangeExponent m U,gradientCoefficientExponent m U,ipmRangeExponent m U,
    ipmErrorBits m U,ipmPrecision m U,ipmLimbs m U]

/-- Arguments `[size m,size U,Es,heap]`. -/
def precisionRecordBody : Stmt :=
  .assign 4 (.bin .add (.bin .add (.reg 0) (.reg 1)) (.const 5)) ;;
  .assign 5 (.bin .add (.bin .add (.bin .mul (.const 4) (.reg 2))
    (.bin .mul (.const 2) (.reg 4))) (.const 100)) ;;
  .assign 6 (.bin .add (.reg 5) (.const 10)) ;;
  .assign 7 (.bin .mul (.const 4) (.bin .add (.bin .add (.bin .add
    (.bin .add (.reg 6) (.bin .mul (.const 5) (.reg 5))) (.reg 0))
    (.bin .mul (.const 1000) (.bin .add (.reg 0) (.reg 1)))) (.const 100))) ;;
  .assign 8 (.bin .add (.bin .add (.bin .add (.reg 7) (.reg 4))
    (.bin .mul (.const 5) (.reg 5))) (.const 40)) ;;
  .store (.reg 3) (.reg 2) ;;
  .store (.bin .add (.reg 3) (.const 1)) (.reg 4) ;;
  .store (.bin .add (.reg 3) (.const 2)) (.reg 5) ;;
  .store (.bin .add (.reg 3) (.const 3)) (.reg 6) ;;
  .store (.bin .add (.reg 3) (.const 4)) (.reg 7) ;;
  .store (.bin .add (.reg 3) (.const 5)) (.reg 8) ;;
  .ret (.bin .add (.reg 3) (.const 6))

/-- One arithmetic-and-record entry. -/
def precisionRecordModule : List Stmt := [precisionRecordBody]

/-- Write exactly six cells and return their end, with full heap framing. -/
def precisionRecordContract (w : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ m U heap,args=[m.size,U.size,slackRangeExponent m U,heap] ∧
      ipmParameterWordBits m U ≤ w)
    (fun args _ mem' => ∀ m U heap,args=[m.size,U.size,slackRangeExponent m U,heap] →
      ListAt mem' heap (precisionWords m U))
    (fun _ _ => 300) (fun _ _ => 6)
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧ v=heapArg args+6}

/-- Parameter arithmetic and storage contain no random instruction. -/
theorem precisionRecord_noRand : precisionRecordBody.NoRand := by
  simp [precisionRecordBody,Stmt.NoRand]

private theorem parameter_assign_flat {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {r : ℕ} {e : Expr} {s : Stmt} {mem regs regs' : ℕ → ℕ} {pos v k T : ℕ}
    {Q : Outcome → State → Prop}
    (he : e.eval w ⟨mem,regs,pos⟩ = some v)
    (hreg : regs'=Function.update regs r v)
    (hrest : ∃ o st' c,Runs w p ω s ⟨mem,regs',pos⟩ o st' c ∧
      Q o st' ∧ k+e.size+2+c ≤ T) :
    ∃ o st' c,Runs w p ω (.seq (.assign r e) s) ⟨mem,regs,pos⟩ o st' c ∧
      Q o st' ∧ k+c ≤ T := by
  subst hreg
  exact runs_seq_assign_le he hrest

set_option maxRecDepth 4096 in
/-- All parameter arithmetic is exact in the chosen word range. The
record costs at most three hundred operations and uses six fresh words. -/
theorem precisionRecord_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b precisionRecordModule) :
    MeetsContract w p b (precisionRecordContract w) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨m,U,heap,rfl,hw⟩,hzero,hspace⟩ := hpre
  change heap+6 < 2^w at hspace
  change ZeroFrom mem heap at hzero
  have hb := Nat.lt_size_self (ipmParameterBound m U)
  have hfits := ipm_parameter_words_fit m U hw
  have hbound : ipmParameterBound m U < 2^w := by
    apply (Nat.size_le).mp
    unfold ipmParameterWordBits at hw
    omega
  have hE : slackRangeExponent m U < 2^w := by
    have hh := hfits.2.2.2.1
    unfold ipmRangeExponent at hh
    omega
  have hK : gradientCoefficientExponent m U < 2^w := by
    have hh := hfits.2.1
    unfold ipmLimbs at hh
    omega
  have hmB : m.size+U.size < 2^w := by unfold gradientCoefficientExponent at hK; omega
  have hscale : 1000*(m.size+U.size) < 2^w := by
    have hh := hfits.2.2.2.2.2.2.1
    simpa only [Num.IPM.alphaScale] using (Nat.lt_of_le_of_lt (Nat.le_add_right _ 1) hh)
  have hR := hfits.2.2.2.1
  have hP := hfits.2.2.1
  have hL := hfits.2.1
  have hq : ipmErrorBits m U < 2^w := by
    have hh := (ipm_precision_margins m U).2.1
    omega
  have hconst : 1000 < 2^w := by
    have hh := hfits.1
    have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) hh
    omega
  have hRcalc : 4*slackRangeExponent m U+2*gradientCoefficientExponent m U+100 < 2^w := hR
  have hPcalc : 4*(ipmErrorBits m U+5*ipmRangeExponent m U+m.size+
      1000*(m.size+U.size)+100) < 2^w := hP
  have hLcalc : ipmPrecision m U+gradientCoefficientExponent m U+5*ipmRangeExponent m U+40 < 2^w := hL
  have hKd : gradientCoefficientExponent m U=m.size+U.size+5 := rfl
  have hRd : ipmRangeExponent m U=4*slackRangeExponent m U+2*gradientCoefficientExponent m U+100 := rfl
  have hqd : ipmErrorBits m U=ipmRangeExponent m U+10 := rfl
  have hPd : ipmPrecision m U=4*(ipmErrorBits m U+5*ipmRangeExponent m U+m.size+1000*(m.size+U.size)+100) := rfl
  have hLd : ipmLimbs m U=ipmPrecision m U+gradientCoefficientExponent m U+5*ipmRangeExponent m U+40 := rfl
  let regs0 := (startState [m.size,U.size,slackRangeExponent m U,heap] mem pos).regs
  let regs1 := Function.update regs0 4 (gradientCoefficientExponent m U)
  let regs2 := Function.update regs1 5 (ipmRangeExponent m U)
  let regs3 := Function.update regs2 6 (ipmErrorBits m U)
  let regs4 := Function.update regs3 7 (ipmPrecision m U)
  let regs5 := Function.update regs4 8 (ipmLimbs m U)
  apply runs_start_le
  unfold precisionRecordBody
  refine parameter_assign_flat (regs':=regs1) (v:=gradientCoefficientExponent m U) ?_ rfl ?_
  · dsimp only [regs0,gradientCoefficientExponent]
    clear * - hK hconst hKd hRd hqd hPd hLd
    with_reducible eval_expr
  refine parameter_assign_flat (regs':=regs2) (v:=ipmRangeExponent m U) ?_ rfl ?_
  · dsimp only [regs1,regs0,ipmRangeExponent]
    clear * - hRcalc hconst hKd hRd hqd hPd hLd
    with_reducible eval_expr
  refine parameter_assign_flat (regs':=regs3) (v:=ipmErrorBits m U) ?_ rfl ?_
  · dsimp only [regs2,regs1,regs0,ipmErrorBits]
    clear * - hq hconst hKd hRd hqd hPd hLd
    with_reducible eval_expr
  refine parameter_assign_flat (regs':=regs4) (v:=ipmPrecision m U) ?_ rfl ?_
  · dsimp only [regs3,regs2,regs1,regs0,ipmPrecision,Num.IPM.alphaScale]
    clear * - hPcalc hconst hKd hRd hqd hPd hLd
    with_reducible eval_expr
  refine parameter_assign_flat (regs':=regs5) (v:=ipmLimbs m U) ?_ rfl ?_
  · dsimp only [regs4,regs3,regs2,regs1,regs0,ipmLimbs]
    clear * - hLcalc hconst hKd hRd hqd hPd hLd
    with_reducible eval_expr
  dsimp only [regs5,regs4,regs3,regs2,regs1,regs0]
  wram_step
  wram_step
  wram_step
  wram_step
  wram_step
  wram_step
  refine runs_ret_le (v := heap+6) (by eval_expr) ?_ ?_
  · let outMem := Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update mem heap (slackRangeExponent m U))
        (heap+1) (gradientCoefficientExponent m U)) (heap+2) (ipmRangeExponent m U))
        (heap+3) (ipmErrorBits m U)) (heap+4) (ipmPrecision m U)) (heap+5) (ipmLimbs m U)
    change (heap ≤ heap+6 ∧ heap+6 ≤ heap+6 ∧ (∀ x < heap,outMem x=mem x) ∧
      ZeroFrom outMem (heap+6) ∧ (∀ m' U' heap',
        [m.size,U.size,slackRangeExponent m U,heap]=[m'.size,U'.size,slackRangeExponent m' U',heap'] →
        ListAt outMem heap' (precisionWords m' U'))) ∧ heap+6=heap+6
    refine ⟨⟨by omega,le_rfl,?_,?_,?_⟩,rfl⟩
    · intro x hx
      dsimp only [outMem]
      simp only [Function.update_of_ne (by omega : x ≠ heap+5),Function.update_of_ne (by omega : x ≠ heap+4),
        Function.update_of_ne (by omega : x ≠ heap+3),Function.update_of_ne (by omega : x ≠ heap+2),
        Function.update_of_ne (by omega : x ≠ heap+1),Function.update_of_ne (by omega : x ≠ heap)]
    · intro x hx
      change heap+6 ≤ x at hx
      dsimp only [outMem]
      simp only [Function.update_of_ne (by omega : x ≠ heap+5),Function.update_of_ne (by omega : x ≠ heap+4),
        Function.update_of_ne (by omega : x ≠ heap+3),Function.update_of_ne (by omega : x ≠ heap+2),
        Function.update_of_ne (by omega : x ≠ heap+1),Function.update_of_ne (by omega : x ≠ heap)]
      exact hzero x (by omega)
    · intro m' U' heap' he
      simp only [List.cons.injEq,and_true] at he
      obtain ⟨hm,hu,he,rfl⟩ := he
      have hparams : precisionWords m' U'=precisionWords m U := by
        simp only [precisionWords,slackRangeExponent,gradientCoefficientExponent,ipmRangeExponent,
          ipmErrorBits,ipmPrecision,ipmLimbs,Num.IPM.alphaScale,← hm,← hu]
      rw [hparams]
      intro i hi
      change i < 6 at hi
      interval_cases i <;> simp [outMem,precisionWords]
  · simp only [precisionRecordContract,heapContract,Expr.size_bin,Expr.size_reg,Expr.size_const]
    omega


/-- The parameter-record layout `[Es,K,R,q,P,L]`. -/
def qualityPrecisionWords (m U k : ℕ) : List ℕ :=
  [qualitySlackExponent m U k,gradientCoefficientExponent m U,ipmQualityRangeExponent m U k,
    ipmQualityErrorBits m U k,ipmQualityPrecision m U k,ipmQualityLimbs m U k]

/-- The selector returns the original record when the quality fits the base range. -/
theorem qualityPrecisionWords_eq {m U k : ℕ} (hk : k ≤ slackRangeExponent m U) :
    qualityPrecisionWords m U k = precisionWords m U := by
  obtain ⟨hR,hq,hP,hL,_⟩ := ipmQualityParameters_eq hk
  simp only [qualityPrecisionWords, precisionWords, qualitySlackExponent_eq hk, hR,hq,hP,hL]

/-- Write exactly six cells and return their end, with full heap framing. -/
def qualityPrecisionRecordContract (w : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ m U k heap,args=[m.size,U.size,qualitySlackExponent m U k,heap] ∧
      ipmQualityParameterWordBits m U k ≤ w)
    (fun args _ mem' => ∀ m U k heap,args=[m.size,U.size,qualitySlackExponent m U k,heap] →
      ListAt mem' heap (qualityPrecisionWords m U k))
    (fun _ _ => 300) (fun _ _ => 6)
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧ v=heapArg args+6}

set_option maxRecDepth 4096 in
/-- All parameter arithmetic is exact in the chosen word range. The
record costs at most three hundred operations and uses six fresh words. -/
theorem qualityPrecisionRecord_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b precisionRecordModule) :
    MeetsContract w p b (qualityPrecisionRecordContract w) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨m,U,k,heap,rfl,hw⟩,hzero,hspace⟩ := hpre
  change heap+6 < 2^w at hspace
  change ZeroFrom mem heap at hzero
  have hb := Nat.lt_size_self (ipmQualityParameterBound m U k)
  have hfits := ipm_quality_parameter_words_fit m U k hw
  have hbound : ipmQualityParameterBound m U k < 2^w := by
    apply (Nat.size_le).mp
    unfold ipmQualityParameterWordBits at hw
    omega
  have hE : qualitySlackExponent m U k < 2^w := by
    have hh := hfits.2.2.2.1
    unfold ipmQualityRangeExponent at hh
    omega
  have hK : gradientCoefficientExponent m U < 2^w := by
    have hh := hfits.2.1
    unfold ipmQualityLimbs at hh
    omega
  have hmB : m.size+U.size < 2^w := by unfold gradientCoefficientExponent at hK; omega
  have hscale : 1000*(m.size+U.size) < 2^w := by
    have hh := hfits.2.2.2.2.2.2.1
    simpa only [Num.IPM.alphaScale] using (Nat.lt_of_le_of_lt (Nat.le_add_right _ 1) hh)
  have hR := hfits.2.2.2.1
  have hP := hfits.2.2.1
  have hL := hfits.2.1
  have hq : ipmQualityErrorBits m U k < 2^w := by
    have hh := (ipm_quality_precision_margins m U k).2.1
    omega
  have hconst : 1000 < 2^w := by
    have hh := hfits.1
    have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) hh
    omega
  have hRcalc : 4*qualitySlackExponent m U k+2*gradientCoefficientExponent m U+100 < 2^w := hR
  have hPcalc : 4*(ipmQualityErrorBits m U k+5*ipmQualityRangeExponent m U k+m.size+
      1000*(m.size+U.size)+100) < 2^w := hP
  have hLcalc : ipmQualityPrecision m U k+gradientCoefficientExponent m U+5*ipmQualityRangeExponent m U k+40 < 2^w := hL
  have hKd : gradientCoefficientExponent m U=m.size+U.size+5 := rfl
  have hRd : ipmQualityRangeExponent m U k=4*qualitySlackExponent m U k+2*gradientCoefficientExponent m U+100 := rfl
  have hqd : ipmQualityErrorBits m U k=ipmQualityRangeExponent m U k+10 := rfl
  have hPd : ipmQualityPrecision m U k=4*(ipmQualityErrorBits m U k+5*ipmQualityRangeExponent m U k+m.size+1000*(m.size+U.size)+100) := rfl
  have hLd : ipmQualityLimbs m U k=ipmQualityPrecision m U k+gradientCoefficientExponent m U+5*ipmQualityRangeExponent m U k+40 := rfl
  let regs0 := (startState [m.size,U.size,qualitySlackExponent m U k,heap] mem pos).regs
  let regs1 := Function.update regs0 4 (gradientCoefficientExponent m U)
  let regs2 := Function.update regs1 5 (ipmQualityRangeExponent m U k)
  let regs3 := Function.update regs2 6 (ipmQualityErrorBits m U k)
  let regs4 := Function.update regs3 7 (ipmQualityPrecision m U k)
  let regs5 := Function.update regs4 8 (ipmQualityLimbs m U k)
  apply runs_start_le
  unfold precisionRecordBody
  refine parameter_assign_flat (regs':=regs1) (v:=gradientCoefficientExponent m U) ?_ rfl ?_
  · dsimp only [regs0,gradientCoefficientExponent]
    clear * - hK hconst hKd hRd hqd hPd hLd
    with_reducible eval_expr
  refine parameter_assign_flat (regs':=regs2) (v:=ipmQualityRangeExponent m U k) ?_ rfl ?_
  · dsimp only [regs1,regs0,ipmQualityRangeExponent]
    clear * - hRcalc hconst hKd hRd hqd hPd hLd
    with_reducible eval_expr
  refine parameter_assign_flat (regs':=regs3) (v:=ipmQualityErrorBits m U k) ?_ rfl ?_
  · dsimp only [regs2,regs1,regs0,ipmQualityErrorBits]
    clear * - hq hconst hKd hRd hqd hPd hLd
    with_reducible eval_expr
  refine parameter_assign_flat (regs':=regs4) (v:=ipmQualityPrecision m U k) ?_ rfl ?_
  · dsimp only [regs3,regs2,regs1,regs0,ipmQualityPrecision,Num.IPM.alphaScale]
    clear * - hPcalc hconst hKd hRd hqd hPd hLd
    with_reducible eval_expr
  refine parameter_assign_flat (regs':=regs5) (v:=ipmQualityLimbs m U k) ?_ rfl ?_
  · dsimp only [regs4,regs3,regs2,regs1,regs0,ipmQualityLimbs]
    clear * - hLcalc hconst hKd hRd hqd hPd hLd
    with_reducible eval_expr
  dsimp only [regs5,regs4,regs3,regs2,regs1,regs0]
  wram_step
  wram_step
  wram_step
  wram_step
  wram_step
  wram_step
  refine runs_ret_le (v := heap+6) (by eval_expr) ?_ ?_
  · let outMem := Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update mem heap (qualitySlackExponent m U k))
        (heap+1) (gradientCoefficientExponent m U)) (heap+2) (ipmQualityRangeExponent m U k))
        (heap+3) (ipmQualityErrorBits m U k)) (heap+4) (ipmQualityPrecision m U k)) (heap+5) (ipmQualityLimbs m U k)
    change (heap ≤ heap+6 ∧ heap+6 ≤ heap+6 ∧ (∀ x < heap,outMem x=mem x) ∧
      ZeroFrom outMem (heap+6) ∧ (∀ m' U' k' heap',
        [m.size,U.size,qualitySlackExponent m U k,heap]=[m'.size,U'.size,qualitySlackExponent m' U' k',heap'] →
        ListAt outMem heap' (qualityPrecisionWords m' U' k'))) ∧ heap+6=heap+6
    refine ⟨⟨by omega,le_rfl,?_,?_,?_⟩,rfl⟩
    · intro x hx
      dsimp only [outMem]
      simp only [Function.update_of_ne (by omega : x ≠ heap+5),Function.update_of_ne (by omega : x ≠ heap+4),
        Function.update_of_ne (by omega : x ≠ heap+3),Function.update_of_ne (by omega : x ≠ heap+2),
        Function.update_of_ne (by omega : x ≠ heap+1),Function.update_of_ne (by omega : x ≠ heap)]
    · intro x hx
      change heap+6 ≤ x at hx
      dsimp only [outMem]
      simp only [Function.update_of_ne (by omega : x ≠ heap+5),Function.update_of_ne (by omega : x ≠ heap+4),
        Function.update_of_ne (by omega : x ≠ heap+3),Function.update_of_ne (by omega : x ≠ heap+2),
        Function.update_of_ne (by omega : x ≠ heap+1),Function.update_of_ne (by omega : x ≠ heap)]
      exact hzero x (by omega)
    · intro m' U' k' heap' he
      simp only [List.cons.injEq,and_true] at he
      obtain ⟨hm,hu,he,rfl⟩ := he
      have hparams : qualityPrecisionWords m' U' k'=qualityPrecisionWords m U k := by
        simp only [qualityPrecisionWords,gradientCoefficientExponent,ipmQualityRangeExponent,
          ipmQualityErrorBits,ipmQualityPrecision,ipmQualityLimbs,Num.IPM.alphaScale,← hm,← hu,← he]
      rw [hparams]
      intro i hi
      change i < 6 at hi
      interval_cases i <;> simp [outMem,qualityPrecisionWords]
  · simp only [qualityPrecisionRecordContract,heapContract,Expr.size_bin,Expr.size_reg,Expr.size_const]
    omega

end MinCostFlow.IPM.Machine
