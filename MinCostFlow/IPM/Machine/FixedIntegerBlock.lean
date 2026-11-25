module

public import MinCostFlow.IPM.Machine.Layout
public import MinCostFlow.Num.LoadInt
public import MinCostFlow.Num.ShiftLeft
import MinCostFlow.Num.ModulePlacement
import MinCostFlow.Num.WordBounds
import WordRAM.Tactic

/-!
# Loading target-test integers at a chosen precision

Costs are signed integers at precision zero. Capacities and target guesses
must be loaded on the flow's fixed-point grid. This wrapper loads the
shared sign-and-magnitude encoding and shifts its exact numerator by P.
It counts both numerical calls and preserves their complete heap frame.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[sign,magnitude,L,P,heap]`. -/
def fixedIntegerBlockBody (load shift : ℕ) : Stmt :=
  .call 5 load [.reg 0,.reg 1,.reg 2,.reg 4] ;;
  .call 6 shift [.bin .add (.reg 4) (.reg 2),.reg 2,.reg 3,.reg 5] ;;
  .ret (.reg 6)

/-- Integer loader followed by exact fixed-point scaling. -/
def fixedIntegerBlockModule (b h : ℕ) : List Stmt :=
  [fixedIntegerBlockBody (b+1) (b+6)] ++
    (Num.loadIntModule (b+1) h ++ Num.shiftLeftModule (b+6) h)

/-- The exact result begins at `heap+2L`, with `3L` total allocation. -/
def fixedIntegerBlockContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ n : ℤ,∃ L P heap,args=encodeSignedPair n++[L,P,heap] ∧
      Num.Fits h L n ∧ Num.Fits h L (n*(2:ℤ)^P))
    (fun args _ mem' => ScalarAt mem' (heapArg args+2*args.getD 2 0) h
      (args.getD 2 0) (args.getD 3 0)
      (Num.decodeIntWords (args.getD 0 0) (args.getD 1 0):ℝ))
    (fun args _ => 100*args.getD 2 0+200) (fun args _ => 3*args.getD 2 0)
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧ v=heapArg args+3*args.getD 2 0}

/-- Loading a signed integer and scaling it use no random instruction. -/
theorem fixedIntegerBlockModule_noRand (b h : ℕ) :
    ∀ body ∈ fixedIntegerBlockModule b h,body.NoRand := by
  intro body hb
  simp only [fixedIntegerBlockModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb | hb
  · simp [fixedIntegerBlockBody,Stmt.NoRand]
  · exact Num.loadIntModule_noRand _ _ _ hb
  · exact Num.shiftLeftModule_noRand _ _ _ hb

/-- Exact loading of any fitting signed integer costs at most `100L+200`
and yields a valid block at the caller's precision, including P=0. -/
theorem fixedIntegerBlock_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0 < h) (hw : 2*h+2 ≤ w) (hp : p.HasAt b (fixedIntegerBlockModule b h)) :
    MeetsContract w p b (fixedIntegerBlockContract w h) := by
  have htail := Num.hasAt_append_right hp
  have hload : p.HasAt (b+1) (Num.loadIntModule (b+1) h) := Num.hasAt_append_left htail
  have hshift : p.HasAt (b+6) (Num.shiftLeftModule (b+6) h) := Num.hasAt_append_right htail
  have hw1 : 1 < 2^w := lt_trans (Nat.one_lt_pow (Nat.ne_of_gt hh) (by decide)) (Num.base_lt_word hw)
  have hloadSpec := Num.loadInt_meetsContract hw1 (Num.base_lt_word hw) hload
  have hshiftSpec := Num.shiftLeft_meetsContract hh hw hshift
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨n,L,P,heap,rfl,hn,hscaled⟩,hzero,hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap+3*L < 2^w at hspace
  have hsw : (if n < 0 then 1 else 0) < 2^w := hwords _ (by simp [encodeSignedPair])
  have hmw : n.natAbs < 2^w := hwords _ (by simp [encodeSignedPair])
  have hLw : L < 2^w := hwords _ (by simp [encodeSignedPair])
  have hPw : P < 2^w := hwords _ (by simp [encodeSignedPair])
  have hhw : heap < 2^w := hwords _ (by simp [encodeSignedPair])
  apply runs_start_le
  unfold fixedIntegerBlockBody
  refine runs_seq_call_le hloadSpec (vs:=encodeSignedPair n++[L,heap]) (by simp only [encodeSignedPair,List.cons_append,List.nil_append]; eval_expr) ?_ ?_ ?_
  · intro x hx
    simp [encodeSignedPair] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  · exact ⟨⟨n,L,heap,rfl⟩,hzero,by change heap+2*L < 2^w; omega⟩
  · intro v1 mem1 pos1 hp1
    have hval := Num.loadInt_value_of_fits hp1 hn
    obtain ⟨hv1,hlo1,hhi1,hframe1,hzero1,hvalid,_⟩ := hp1
    change v1=heap+2*L at hv1
    change Num.Valid mem1 (heap+L) h L at hvalid
    change ∀ x < heap,mem1 x=mem x at hframe1
    have hv1w : v1 < 2^w := by omega
    refine runs_seq_call_le hshiftSpec (vs:=[heap+L,L,P,v1]) (by simp only [encodeSignedPair,List.cons_append,List.nil_append]; eval_expr) ?_ ?_ ?_
    · wram_words
    · exact ⟨⟨_,_,_,_,rfl,by omega,hvalid⟩,hzero1,by change v1+L < 2^w; omega⟩
    · intro v2 mem2 pos2 hp2
      obtain ⟨hv2,hlo2,hhi2,hframe2,hzero2,hvalid2,hvalue2⟩ := hp2
      change v2=v1+L at hv2
      change Num.Valid mem2 v1 h L at hvalid2
      change Num.intVal mem2 v1 h L=Num.wrap h L (Num.intVal mem1 (heap+L) h L*(2:ℤ)^P) at hvalue2
      rw [hval,Num.wrap_of_fits hscaled] at hvalue2
      have hv2w : v2 < 2^w := by omega
      refine runs_ret_le (v:=v2) (by simp only [encodeSignedPair,List.cons_append,List.nil_append]; eval_expr) ?_ ?_
      · change (heap ≤ v2 ∧ v2 ≤ heap+3*L ∧ (∀ x < heap,mem2 x=mem x) ∧
          ZeroFrom mem2 v2 ∧ ScalarAt mem2 (heap+2*L) h L P (Num.decodeIntWords (if n < 0 then 1 else 0) n.natAbs:ℝ)) ∧
          v2=heap+3*L
        rw [Num.decodeIntWords_encodeInt]
        refine ⟨⟨by omega,by omega,?_,hzero2,?_,?_⟩,by omega⟩
        · intro x hx
          exact (hframe2 x (by change x < v1; omega)).trans (hframe1 x hx)
        · simpa only [hv1] using hvalid2
        · rw [← hv1,Num.fixVal,hvalue2]
          simp only [Int.cast_mul,Int.cast_pow,Int.cast_ofNat]
          exact mul_div_cancel_right₀ _ (by positivity)
      · simp only [fixedIntegerBlockContract,heapContract,encodeSignedPair,List.cons_append,List.nil_append,
          List.getD_cons_zero,List.getD_cons_succ,Num.loadIntContract,Num.shiftLeftContract,
          Expr.size_reg,Expr.size_bin,argsSize_cons,argsSize_nil]
        omega

/-- A negative target is loaded exactly on a nonzero-precision grid in
an actual terminating machine run for every random tape. -/
theorem fixedIntegerBlock_negative_example :
    let p : Program := ⟨fixedIntegerBlockModule 0 4⟩
    p.IsDeterministic ∧ ∀ ω : ℕ → Bool,
      ∃ o st c,Runs 16 p ω (fixedIntegerBlockBody 1 6)
        (startState (encodeSignedPair (-3)++[8,8,0]) (fun _ => 0) 0) o st c ∧
        o.value=24 ∧ ScalarAt st.mem 16 4 8 8 (-3) ∧ c ≤ 1000 := by
  dsimp only
  have hplace : (⟨fixedIntegerBlockModule 0 4⟩ : Program).HasAt 0 (fixedIntegerBlockModule 0 4) := by
    intro i hi
    simp only [Nat.zero_add,List.getElem?_eq_getElem hi]
  have hmet := fixedIntegerBlock_meetsContract (by decide : 0 < 4)
    (by decide : 2*4+2 ≤ 16) hplace
  constructor
  · exact fixedIntegerBlockModule_noRand 0 4
  · intro ω
    have hpre : (fixedIntegerBlockContract 16 4).pre (encodeSignedPair (-3)++[8,8,0]) (fun _ => 0) := by
      refine ⟨⟨-3,8,8,0,rfl,?_,?_⟩,?_,by decide⟩
      · norm_num [Num.Fits,Num.capacity,Num.base]
      · norm_num [Num.Fits,Num.capacity,Num.base]
      · intro x _
        rfl
    obtain ⟨body,hbody,o,st,c,hr,hpost,hcost⟩ := hmet (encodeSignedPair (-3)++[8,8,0]) (fun _ => 0) 0 ω
      (by intro x hx; simp [encodeSignedPair] at hx; rcases hx with rfl | rfl | rfl | rfl <;> decide) hpre
    have he : body=fixedIntegerBlockBody 1 6 := by
      simpa [fixedIntegerBlockModule] using hbody.symm
    subst body
    refine ⟨o,st,c,hr,hpost.2,?_,hcost⟩
    simpa [encodeSignedPair,Num.decodeIntWords,heapArg] using hpost.1.2.2.2.2

end MinCostFlow.IPM.Machine
