module

public import MinCostFlow.IPM.Machine.PrecisionRecord
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic

/-!
# Selecting the fixed-point parameters from the input

Binary-length scans, the potential-derived slack exponent, and the
constant-cost arithmetic record writer are composed into one procedure.
The output is the six-word parameter record. Every scan is charged,
including the scans internal to the range-exponent entry.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[m,U,heap]`, output `[Es,K,R,q,P,L]` at the incoming heap. -/
def precisionSelectionBody (bits range record : ℕ) : Stmt :=
  .call 3 bits [.reg 0] ;;
  .call 4 bits [.reg 1] ;;
  .call 5 range [.reg 0,.reg 1] ;;
  .call 6 record [.reg 3,.reg 4,.reg 5,.reg 2] ;;
  .ret (.reg 6)

/-- Entry, shared bit-length scan, range selection, and parameter writer. -/
def precisionSelectionModule (b : ℕ) : List Stmt :=
  [precisionSelectionBody (b+1) (b+2) (b+4)] ++
    (Num.IPM.bitLengthModule (b+1) ++
      (precisionRangeModule (b+2) ++ precisionRecordModule))

/-- Exact six-word parameters, six allocated cells, and linear bit-scan cost. -/
def precisionSelectionContract (w : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ m U heap,args=[m,U,heap] ∧ 2 ≤ m*U ∧ ipmParameterWordBits m U ≤ w)
    (fun args _ mem' => ListAt mem' (heapArg args)
      (precisionWords (args.getD 0 0) (args.getD 1 0)))
    (fun args _ => 28*((args.getD 0 0).size+(args.getD 1 0).size)+600)
    (fun _ _ => 6)
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧ v=heapArg args+6}

/-- Parameter selection is deterministic. -/
theorem precisionSelectionModule_noRand (b : ℕ) :
    ∀ body ∈ precisionSelectionModule b,body.NoRand := by
  intro body hb
  simp only [precisionSelectionModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb | hb | hb
  · simp [precisionSelectionBody,Stmt.NoRand]
  · exact Num.IPM.bitLengthModule_noRand _ _ hb
  · exact precisionRangeModule_noRand _ _ hb
  · have he : body=precisionRecordBody := by simpa [precisionRecordModule] using hb
    subst body
    exact precisionRecord_noRand

/-- The actual machine selects the format parameters from `m,U`, with
all scans and arithmetic counted and all old memory preserved. -/
theorem precisionSelection_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (precisionSelectionModule b)) :
    MeetsContract w p b (precisionSelectionContract w) := by
  have htail := Num.hasAt_append_right hp
  have hbits : p.HasAt (b+1) (Num.IPM.bitLengthModule (b+1)) := Num.hasAt_append_left htail
  have hrest := Num.hasAt_append_right htail
  have hrange : p.HasAt (b+2) (precisionRangeModule (b+2)) := by
    simpa [Num.IPM.bitLengthModule] using Num.hasAt_append_left hrest
  have hrecord : p.HasAt (b+4) precisionRecordModule := by
    simpa [Num.IPM.bitLengthModule,precisionRangeModule] using Num.hasAt_append_right hrest
  have hrecordSpec := precisionRecord_meetsContract (w:=w) hrecord
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨m,U,heap,rfl,hsize,hw⟩,hzero,hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap+6 < 2^w at hspace
  have hw14 := (ipm_parameter_words_fit m U hw).1
  have htwo : 2 < 2^w := by
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) hw14
    omega
  have hbitSpec := Num.IPM.bitLength_meetsContract htwo hbits
  have hrangeSpec := precisionRange_meetsContract htwo hrange
  have hmw : m < 2^w := hwords _ (by simp)
  have hUw : U < 2^w := hwords _ (by simp)
  have hheap : heap < 2^w := hwords _ (by simp)
  have hmb : m.size < 2^w := (Num.IPM.size_le_value m).trans_lt hmw
  have hUb : U.size < 2^w := (Num.IPM.size_le_value U).trans_lt hUw
  have hE : slackRangeExponent m U < 2^w := by
    have hh := (ipm_parameter_words_fit m U hw).2.2.2.1
    unfold ipmRangeExponent at hh
    omega
  apply runs_start_le
  unfold precisionSelectionBody
  refine runs_seq_call_le hbitSpec (vs:=[m]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨m,rfl⟩
  · intro vm mem1 pos1 hp1
    obtain ⟨rfl,hvm⟩ := hp1
    change vm=m.size at hvm
    subst vm
    refine runs_seq_call_le hbitSpec (vs:=[U]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · exact ⟨U,rfl⟩
    · intro vU mem2 pos2 hp2
      obtain ⟨rfl,hvU⟩ := hp2
      change vU=U.size at hvU
      subst vU
      refine runs_seq_call_le hrangeSpec (vs:=[m,U]) (by eval_expr) ?_ ?_ ?_
      · wram_words
      · exact precisionRange_pre_of_parameter_width m U hw hsize mem2
      · intro E mem3 pos3 hp3
        obtain ⟨rfl,hEval⟩ := hp3
        change E=slackRangeExponent m U at hEval
        subst E
        refine runs_seq_call_le hrecordSpec
          (vs:=[m.size,U.size,slackRangeExponent m U,heap]) (by eval_expr) ?_ ?_ ?_
        · wram_words
        · exact ⟨⟨m,U,heap,rfl,hw⟩,hzero,hspace⟩
        · intro v mem4 pos4 hp4
          obtain ⟨⟨hlo,hhi,hframe,hfresh,hout⟩,hv⟩ := hp4
          change v=heap+6 at hv
          have hvw : v < 2^w := by omega
          refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
          · exact ⟨⟨hlo,hhi,hframe,hfresh,hout m U heap rfl⟩,hv⟩
          · simp [precisionSelectionContract,heapContract,Num.IPM.bitLengthContract,
              precisionRangeContract,precisionRecordContract,argsSize,startState,
              Expr.size_reg]
            omega

/-- The complete parameter selector has a concrete terminating run on
every random tape, witnessing all its word and heap conditions together. -/
theorem precisionSelection_example :
    let p : Program := ⟨precisionSelectionModule 0⟩
    p.IsDeterministic ∧ ∀ ω : ℕ → Bool,
      ∃ o st c,Runs 64 p ω (precisionSelectionBody 1 2 4)
        (startState [1,2,0] (fun _ => 0) 0) o st c ∧
        o.value=6 ∧ ListAt st.mem 0 (precisionWords 1 2) ∧ c ≤ 684 := by
  dsimp only
  have hplace : (⟨precisionSelectionModule 0⟩ : Program).HasAt 0 (precisionSelectionModule 0) := by
    intro i hi
    simp only [Nat.zero_add,List.getElem?_eq_getElem hi]
  have hmet := precisionSelection_meetsContract (w:=64) hplace
  constructor
  · exact precisionSelectionModule_noRand 0
  · intro ω
    have hpre : (precisionSelectionContract 64).pre [1,2,0] (fun _ => 0) := by
      refine ⟨⟨1,2,0,rfl,by decide,by decide⟩,?_,by decide⟩
      intro x _
      rfl
    obtain ⟨body,hbody,o,st,c,hr,hpost,hcost⟩ := hmet [1,2,0] (fun _ => 0) 0 ω
      (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> decide) hpre
    have he : body=precisionSelectionBody 1 2 4 := by
      simpa [precisionSelectionModule] using hbody.symm
    subst body
    refine ⟨o,st,c,hr,hpost.2,hpost.1.2.2.2.2,?_⟩
    simpa [precisionSelectionContract,heapContract,show Nat.size 1=1 by decide,
      show Nat.size 2=2 by decide] using hcost

/-- Arguments `[m,U,k,heap]`, output `[Es,K,R,q,P,L]` at the incoming heap. -/
def qualityPrecisionSelectionBody (bits range record : ℕ) : Stmt :=
  .call 4 bits [.reg 0] ;;
  .call 5 bits [.reg 1] ;;
  .call 6 range [.reg 0,.reg 1] ;;
  .cond (.bin .lt (.reg 6) (.reg 2))
    (.call 7 record [.reg 4,.reg 5,.reg 2,.reg 3] ;; .ret (.reg 7))
    (.call 7 record [.reg 4,.reg 5,.reg 6,.reg 3] ;; .ret (.reg 7))

/-- Entry, shared bit-length scan, range selection, and parameter writer. -/
def qualityPrecisionSelectionModule (b : ℕ) : List Stmt :=
  [qualityPrecisionSelectionBody (b+1) (b+2) (b+4)] ++
    (Num.IPM.bitLengthModule (b+1) ++
      (precisionRangeModule (b+2) ++ precisionRecordModule))

/-- Exact six-word parameters, six allocated cells, and linear bit-scan cost. -/
def qualityPrecisionSelectionContract (w : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ m U k heap,args=[m,U,k,heap] ∧ 2 ≤ m*U ∧ ipmQualityParameterWordBits m U k ≤ w)
    (fun args _ mem' => ListAt mem' (heapArg args)
      (qualityPrecisionWords (args.getD 0 0) (args.getD 1 0) (args.getD 2 0)))
    (fun args _ => 28*((args.getD 0 0).size+(args.getD 1 0).size)+610)
    (fun _ _ => 6)
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧ v=heapArg args+6}

/-- Parameter selection is deterministic. -/
theorem qualityPrecisionSelectionModule_noRand (b : ℕ) :
    ∀ body ∈ qualityPrecisionSelectionModule b,body.NoRand := by
  intro body hb
  simp only [qualityPrecisionSelectionModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb | hb | hb
  · simp [qualityPrecisionSelectionBody,Stmt.NoRand]
  · exact Num.IPM.bitLengthModule_noRand _ _ hb
  · exact precisionRangeModule_noRand _ _ hb
  · have he : body=precisionRecordBody := by simpa [precisionRecordModule] using hb
    subst body
    exact precisionRecord_noRand

/-- The actual machine selects the format parameters from `m,U`, with
all scans and arithmetic counted and all old memory preserved. -/
theorem qualityPrecisionSelection_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (qualityPrecisionSelectionModule b)) :
    MeetsContract w p b (qualityPrecisionSelectionContract w) := by
  have htail := Num.hasAt_append_right hp
  have hbits : p.HasAt (b+1) (Num.IPM.bitLengthModule (b+1)) := Num.hasAt_append_left htail
  have hrest := Num.hasAt_append_right htail
  have hrange : p.HasAt (b+2) (precisionRangeModule (b+2)) := by
    simpa [Num.IPM.bitLengthModule] using Num.hasAt_append_left hrest
  have hrecord : p.HasAt (b+4) precisionRecordModule := by
    simpa [Num.IPM.bitLengthModule,precisionRangeModule] using Num.hasAt_append_right hrest
  have hrecordSpec := qualityPrecisionRecord_meetsContract (w:=w) hrecord
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨m,U,k,heap,rfl,hsize,hw⟩,hzero,hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap+6 < 2^w at hspace
  have hQuality := hw
  have hw := (ipmParameterWordBits_le_quality m U k).trans hw
  have hk : k < 2^w := hwords _ (by simp)
  have hw14 := (ipm_parameter_words_fit m U hw).1
  have htwo : 2 < 2^w := by
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) hw14
    omega
  have hbitSpec := Num.IPM.bitLength_meetsContract htwo hbits
  have hrangeSpec := precisionRange_meetsContract htwo hrange
  have hmw : m < 2^w := hwords _ (by simp)
  have hUw : U < 2^w := hwords _ (by simp)
  have hheap : heap < 2^w := hwords _ (by simp)
  have hmb : m.size < 2^w := (Num.IPM.size_le_value m).trans_lt hmw
  have hUb : U.size < 2^w := (Num.IPM.size_le_value U).trans_lt hUw
  have hE : slackRangeExponent m U < 2^w := by
    have hh := (ipm_parameter_words_fit m U hw).2.2.2.1
    unfold ipmRangeExponent at hh
    omega
  apply runs_start_le
  unfold qualityPrecisionSelectionBody
  refine runs_seq_call_le hbitSpec (vs:=[m]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨m,rfl⟩
  · intro vm mem1 pos1 hp1
    obtain ⟨rfl,hvm⟩ := hp1
    change vm=m.size at hvm
    subst vm
    refine runs_seq_call_le hbitSpec (vs:=[U]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · exact ⟨U,rfl⟩
    · intro vU mem2 pos2 hp2
      obtain ⟨rfl,hvU⟩ := hp2
      change vU=U.size at hvU
      subst vU
      refine runs_seq_call_le hrangeSpec (vs:=[m,U]) (by eval_expr) ?_ ?_ ?_
      · wram_words
      · exact precisionRange_pre_of_parameter_width m U hw hsize mem2
      · intro E mem3 pos3 hp3
        obtain ⟨rfl,hEval⟩ := hp3
        change E=slackRangeExponent m U at hEval
        subst E
        refine runs_cond_le
          (v := if slackRangeExponent m U < k then 1 else 0) (by eval_expr) ?_ ?_
        · intro ht
          have hlt : slackRangeExponent m U < k := by
            by_contra hn
            exact ht (ite_eq_right hn)
          have he : qualitySlackExponent m U k = k := max_eq_right hlt.le
          refine runs_seq_call_le hrecordSpec
            (vs:=[m.size,U.size,qualitySlackExponent m U k,heap]) (by rw [he]; eval_expr) ?_ ?_ ?_
          · rw [he]
            wram_words
          · exact ⟨⟨m,U,k,heap,rfl,hQuality⟩,hzero,hspace⟩
          · intro v mem4 pos4 hp4
            obtain ⟨⟨hlo,hhi,hframe,hfresh,hout⟩,hv⟩ := hp4
            change v=heap+6 at hv
            have hvw : v < 2^w := by omega
            refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
            · exact ⟨⟨hlo,hhi,hframe,hfresh,hout m U k heap rfl⟩,hv⟩
            · simp [qualityPrecisionSelectionContract,heapContract,Num.IPM.bitLengthContract,
                precisionRangeContract,qualityPrecisionRecordContract,argsSize,startState,
                Expr.size]
              omega
        · intro ht
          have hle : k ≤ slackRangeExponent m U := by
            by_contra hn
            have hl : slackRangeExponent m U < k := by omega
            simp [hl] at ht
          have he := qualitySlackExponent_eq hle
          refine runs_seq_call_le hrecordSpec
            (vs:=[m.size,U.size,qualitySlackExponent m U k,heap]) (by rw [he]; eval_expr) ?_ ?_ ?_
          · rw [he]
            wram_words
          · exact ⟨⟨m,U,k,heap,rfl,hQuality⟩,hzero,hspace⟩
          · intro v mem4 pos4 hp4
            obtain ⟨⟨hlo,hhi,hframe,hfresh,hout⟩,hv⟩ := hp4
            change v=heap+6 at hv
            have hvw : v < 2^w := by omega
            refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
            · exact ⟨⟨hlo,hhi,hframe,hfresh,hout m U k heap rfl⟩,hv⟩
            · simp [qualityPrecisionSelectionContract,heapContract,Num.IPM.bitLengthContract,
                precisionRangeContract,qualityPrecisionRecordContract,argsSize,startState,
                Expr.size]
              omega

end MinCostFlow.IPM.Machine
