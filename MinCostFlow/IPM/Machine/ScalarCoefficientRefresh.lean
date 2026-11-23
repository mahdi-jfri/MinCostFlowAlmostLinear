module

public import MinCostFlow.IPM.Machine.ScalarGradientFrame
public import MinCostFlow.Num.IPM.Length
public import MinCostFlow.Num.IPM.ArrayData
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Computing both coefficients of one reported edge

Compute the length and then the gradient from the stored edge and held
residual. A final word records the length address. The gradient occupies
the block immediately before that word. This lets the caller copy both
results to its coefficient tables after both numerical calls finish.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[m,cost,residual,lower,flow,upper,alpha,one,L,P,E,heap]`. -/
def scalarCoefficientRefreshBody (length gradient : ℕ) : Stmt :=
  .call 12 length [.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,.reg 8,.reg 9,.reg 10,.reg 11] ;;
  .call 13 gradient [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,
    .reg 8,.reg 9,.reg 10,.reg 12] ;;
  .store (.reg 13) (.bin .sub (.reg 12) (.reg 8)) ;;
  .ret (.bin .add (.reg 13) (.const 1))

/-- The two scalar numerical modules follow the refresh entry. -/
def scalarCoefficientRefreshModule (b h : ℕ) : List Stmt :=
  let g := b+1+(Num.IPM.lengthModule (b+1) h).length
  [scalarCoefficientRefreshBody (b+1) g] ++
    (Num.IPM.lengthModule (b+1) h ++ Num.IPM.gradientModule g h)

/-- Both scalar coefficients refer to the same original input memory.
The returned heap minus one stores the length pointer. -/
def scalarCoefficientRefreshContract (w h q K : ℕ) : Contract where
  pre args mem := (∃ m c r lo f up a one L P E heap,
    args=[m,c,r,lo,f,up,a,one,L,P,E,heap] ∧ L≤heap ∧
    (Num.IPM.lengthContract w h q).pre [lo,f,up,a,one,L,P,E,heap] mem ∧
    (Num.IPM.gradientContract w h q K).pre args mem) ∧
    heapArg args+Num.IPM.lengthSpace (args.getD 8 0) (args.getD 9 0) (args.getD 10 0)+
      Num.IPM.gradientSpace (args.getD 8 0) (args.getD 9 0) (args.getD 10 0)+1<2^w
  post args mem v mem' :=
    heapArg args≤v ∧ v≤heapArg args+
      Num.IPM.lengthSpace (args.getD 8 0) (args.getD 9 0) (args.getD 10 0)+
      Num.IPM.gradientSpace (args.getD 8 0) (args.getD 9 0) (args.getD 10 0)+1 ∧
    (∀ x<heapArg args,mem' x=mem x) ∧ ZeroFrom mem' v ∧
    Num.Valid mem' (mem' (v-1)) h (args.getD 8 0) ∧
    ScalarApprox (1+1/(2:ℝ)^q)
      (Num.fixVal mem' (mem' (v-1)) h (args.getD 8 0) (args.getD 9 0))
      (Num.IPM.arrayLength mem (args.getD 3 0) (args.getD 4 0) (args.getD 5 0)
        (args.getD 6 0) h (args.getD 8 0) (args.getD 9 0) 0) ∧
    Num.Valid mem' (v-1-args.getD 8 0) h (args.getD 8 0) ∧
    |Num.fixVal mem' (v-1-args.getD 8 0) h (args.getD 8 0) (args.getD 9 0)-
      Num.IPM.arrayGradient mem (args.getD 0 0) (args.getD 1 0) (args.getD 2 0)
        (args.getD 3 0) (args.getD 4 0) (args.getD 5 0) (args.getD 6 0) h
        (args.getD 8 0) (args.getD 9 0) 0|≤
      (1/(2:ℝ)^q)*Num.IPM.arrayLength mem (args.getD 3 0) (args.getD 4 0)
        (args.getD 5 0) (args.getD 6 0) h (args.getD 8 0) (args.getD 9 0) 0 ∧
    heapArg args-args.getD 8 0≤mem' (v-1) ∧
    mem' (v-1)+args.getD 8 0≤v-1 ∧ heapArg args≤v-1
  cost args _ := Num.IPM.lengthCost (args.getD 8 0) (args.getD 9 0) (args.getD 10 0)+
    Num.IPM.gradientCost (args.getD 8 0) (args.getD 9 0) (args.getD 10 0)+200

/-- The scalar refresh has no random statements. -/
theorem scalarCoefficientRefreshModule_noRand (b h : ℕ) :
    ∀ body∈scalarCoefficientRefreshModule b h,body.NoRand := by
  intro body hb
  simp only [scalarCoefficientRefreshModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb | hb
  · simp [scalarCoefficientRefreshBody,Stmt.NoRand]
  · exact Num.IPM.lengthModule_noRand _ _ _ hb
  · exact Num.IPM.gradientModule_noRand _ _ _ hb

/-- Both actual scalar numerical calls preserve the source prefix and
produce coefficients at their stated tolerances with explicit total cost. -/
theorem scalarCoefficientRefresh_meetsContract {w h b q K : ℕ} {p : Program}
    (hh : 0<h) (hw : 3*h+2≤w)
    (hp : p.HasAt b (scalarCoefficientRefreshModule b h)) :
    MeetsContract w p b (scalarCoefficientRefreshContract w h q K) := by
  have ht := Num.hasAt_append_right hp
  have hl : p.HasAt (b+1) (Num.IPM.lengthModule (b+1) h) := Num.hasAt_append_left ht
  have hg := Num.hasAt_append_right ht
  have hlSpec := Num.IPM.length_meetsContract (q:=q) hh hw hl
  have hgSpec := Num.IPM.gradient_meetsContract (q:=q) (K:=K) hh hw hg
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨m,c,r,lo,f,up,a,one,L,P,E,heap,rfl,hL,hpreL,hpreG⟩,hspace⟩ := hpre
  change heap+Num.IPM.lengthSpace L P E+Num.IPM.gradientSpace L P E+1<2^w at hspace
  have hsource := hpreG.1
  obtain ⟨m',c',r',lo',f',up',a',one',L',P',E',heap',heq,
    _,_,_,_,_,_,_,hc,hr,hlo,hf,hup,ha,ho,_⟩ := hsource
  simp only [List.cons.injEq,and_true] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  apply runs_start_le
  unfold scalarCoefficientRefreshBody
  refine runs_seq_call_le hlSpec (vs:=[lo,f,up,a,one,L,P,E,heap])
    (by eval_expr) (by intro x hx; apply hwords x; simp_all only [List.mem_cons,List.not_mem_nil,or_false]; tauto)
    hpreL ?_
  intro v0 mem0 pos0 hp0
  obtain ⟨⟨hlo0,hhi0,hframe0,hfresh0,_⟩,hvalid0,hlengthRaw⟩ := hp0
  change heap≤v0 at hlo0
  change v0≤heap+Num.IPM.lengthSpace L P E at hhi0
  change ∀ x<heap,mem0 x=mem x at hframe0
  have hv0w : v0<2^w := by omega
  have hgradPre := gradient_pre_frozen hpreG hframe0 hlo0 hfresh0
    (by omega : v0+Num.IPM.gradientSpace L P E<2^w)
  refine runs_seq_call_le hgSpec (vs:=[m,c,r,lo,f,up,a,one,L,P,E,v0]) (by eval_expr) ?_ hgradPre ?_
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | rfl
    all_goals first | exact hx ▸ hwords _ (by simp) | exact hv0w
  · intro v1 mem1 pos1 hp1
    obtain ⟨⟨hlo1,hhi1,hframe1,hfresh1,_⟩,hvalid1,hgradientRaw⟩ := hp1
    change v0≤v1 at hlo1
    change v1≤v0+Num.IPM.gradientSpace L P E at hhi1
    change ∀ x<v0,mem1 x=mem0 x at hframe1
    change Num.Valid mem0 (v0-L) h L at hvalid0
    change Num.Valid mem1 (v1-L) h L at hvalid1
    have hlength : ScalarApprox (1+1/(2:ℝ)^q) (Num.fixVal mem0 (v0-L) h L P)
      (Num.IPM.arrayLength mem lo f up a h L P 0) := by
      simpa only [Num.IPM.arrayLength,Nat.zero_mul,Nat.add_zero,List.getD_cons_zero,List.getD_cons_succ,startState] using hlengthRaw
    have hgradient : |Num.fixVal mem1 (v1-L) h L P-Num.IPM.arrayGradient mem0 m c r lo f up a h L P 0|≤
      (1/(2:ℝ)^q)*Num.IPM.arrayLength mem0 lo f up a h L P 0 := by
      simpa only [Num.IPM.arrayLength,Num.IPM.arrayGradient,Nat.zero_mul,Nat.add_zero,List.getD_cons_zero,List.getD_cons_succ] using hgradientRaw
    have hlenEnd : v0-L+L≤v0 := by omega
    have hgradEnd : v1-L+L≤v1 := by omega
    have hvalid0' := Num.IPM.valid_frozen hframe1 hlenEnd hvalid0
    have hlength' := hlength
    rw [← Num.IPM.fixVal_frozen (h:=h) (P:=P) hframe1 hlenEnd] at hlength'
    have hgFrozen := Num.IPM.arrayGradient_frozen (m:=m) (c:=c) (lo:=lo) (f:=f) (up:=up) (h:=h) (P:=P) (i:=0) hframe0
      (by simpa using hc) hr (by simpa using hlo) (by simpa using hf) (by simpa using hup) ha
    have hlFrozen := Num.IPM.arrayLength_frozen (lo:=lo) (f:=f) (up:=up) (h:=h) (P:=P) (i:=0) hframe0
      (by simpa using hlo) (by simpa using hf) (by simpa using hup) ha
    rw [hgFrozen,hlFrozen] at hgradient
    have hv1w : v1<2^w := by omega
    have hptr : v0-L<2^w := by omega
    wram_step
    refine runs_ret_le (v:=v1+1) (by eval_expr) ?_ ?_
    · let outMem := Function.update mem1 v1 (v0-L)
      have hframeOut : ∀ x<v1,outMem x=mem1 x := by
        intro x hx
        exact Function.update_of_ne (by omega : x≠v1) _ _
      have hrecord : outMem (v1+1-1)=v0-L := by simp [outMem]
      change heap≤v1+1 ∧ v1+1≤heap+Num.IPM.lengthSpace L P E+Num.IPM.gradientSpace L P E+1 ∧
        (∀ x<heap,outMem x=mem x) ∧ ZeroFrom outMem (v1+1) ∧
        Num.Valid outMem (outMem (v1+1-1)) h L ∧
        ScalarApprox (1+1/(2:ℝ)^q) (Num.fixVal outMem (outMem (v1+1-1)) h L P)
          (Num.IPM.arrayLength mem lo f up a h L P 0) ∧
        Num.Valid outMem (v1+1-1-L) h L ∧
        |Num.fixVal outMem (v1+1-1-L) h L P-Num.IPM.arrayGradient mem m c r lo f up a h L P 0|≤
          (1/(2:ℝ)^q)*Num.IPM.arrayLength mem lo f up a h L P 0 ∧
        heap-L≤outMem (v1+1-1) ∧ outMem (v1+1-1)+L≤v1+1-1 ∧ heap≤v1+1-1
      refine ⟨by omega,by omega,?_,?_,?_,?_,?_,?_,?_⟩
      · intro x hx
        exact (hframeOut x (by omega)).trans ((hframe1 x (by omega)).trans (hframe0 x hx))
      · intro x hx
        dsimp only [outMem]
        rw [Function.update_of_ne (by omega : x≠v1)]
        exact hfresh1 x (by omega)
      · rw [hrecord]
        exact Num.IPM.valid_frozen hframeOut (by omega : v0-L+L≤v1) hvalid0'
      · rw [hrecord,Num.IPM.fixVal_frozen (h:=h) (P:=P) hframeOut (by omega : v0-L+L≤v1)]
        exact hlength'
      · simp only [Nat.add_sub_cancel]
        exact Num.IPM.valid_frozen hframeOut hgradEnd hvalid1
      · simp only [Nat.add_sub_cancel]
        rw [Num.IPM.fixVal_frozen (h:=h) (P:=P) hframeOut hgradEnd]
        exact hgradient
      · rw [hrecord]
        omega
    · simp only [scalarCoefficientRefreshContract,Num.IPM.lengthContract,Num.IPM.gradientContract,
        heapContract,List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,
        Expr.size_bin,Expr.size_const,argsSize_cons,argsSize_nil]
      omega

end MinCostFlow.IPM.Machine
