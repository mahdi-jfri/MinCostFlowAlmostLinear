module

public import MinCostFlow.IPM.Machine.LengthRefresh
public import MinCostFlow.IPM.Machine.GradientRefresh
public import MinCostFlow.IPM.Machine.GradientInputFrame
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Computing both coefficient arrays for an IPM epoch

Compute the length vector, reserve its complete workspace, then compute
the gradient vector with the held epoch residual. Every source block and
the first output vector survive the second call. The two outputs have
known addresses, and the returned heap is their reserved endpoint.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[m,cost,residual,lower,flow,upper,alpha,one,L,P,E,lengthAllocation,gradientAllocation,heap]`. -/
def coefficientRefreshBody (length gradient : ℕ) : Stmt :=
  .call 14 length [.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,.reg 0,.reg 8,.reg 9,.reg 10,.reg 11,.reg 13] ;;
  .call 15 gradient [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,.reg 8,.reg 9,.reg 10,.reg 12,.reg 14] ;;
  .ret (.reg 15)

/-- Both closed numerical refresh modules follow the entry. -/
def coefficientRefreshModule (b h : ℕ) : List Stmt :=
  let g := b+1+(lengthRefreshModule (b+1) h).length
  [coefficientRefreshBody (b+1) g] ++
    (lengthRefreshModule (b+1) h ++ gradientRefreshModule g h)

/-- The length output starts at the incoming heap; the gradient output
starts after the reserved length workspace. Both errors use the original
stored coordinates and held residual. -/
def coefficientRefreshContract (w h q K : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ m cp rp lo fp up ap one L P E la ga heap,
      args=[m,cp,rp,lo,fp,up,ap,one,L,P,E,la,ga,heap] ∧
      la=Num.IPM.lengthArraySpace m L P E ∧ ga=Num.IPM.gradientArraySpace m L P E ∧
      (Num.IPM.lengthArrayContract w h q).pre [lo,fp,up,ap,one,m,L,P,E,heap] mem ∧
      (Num.IPM.gradientArrayContract w h q K).pre [m,cp,rp,lo,fp,up,ap,one,L,P,E,heap] mem)
    (fun args mem mem' =>
      let m := args.getD 0 0
      let cp := args.getD 1 0
      let rp := args.getD 2 0
      let lo := args.getD 3 0
      let fp := args.getD 4 0
      let up := args.getD 5 0
      let ap := args.getD 6 0
      let L := args.getD 8 0
      let P := args.getD 9 0
      let heap := heapArg args
      (∀ i < m,Num.Valid mem' (heap+i*L) h L ∧
        ScalarApprox (1+1/(2:ℝ)^q) (Num.fixVal mem' (heap+i*L) h L P)
          (Num.IPM.arrayLength mem lo fp up ap h L P i)) ∧
      (∀ i < m,Num.Valid mem' (heap+args.getD 11 0+i*L) h L ∧
        |Num.fixVal mem' (heap+args.getD 11 0+i*L) h L P-
          Num.IPM.arrayGradient mem m cp rp lo fp up ap h L P i| ≤
          (1/(2:ℝ)^q)*Num.IPM.arrayLength mem lo fp up ap h L P i))
    (fun args _ => Num.IPM.lengthArrayCost (args.getD 0 0) (args.getD 8 0)
      (args.getD 9 0) (args.getD 10 0)+Num.IPM.gradientArrayCost (args.getD 0 0)
      (args.getD 8 0) (args.getD 9 0) (args.getD 10 0)+400)
    (fun args _ => args.getD 11 0+args.getD 12 0)
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧
    v=heapArg args+(args.getD 11 0+args.getD 12 0)}

/-- Coefficient refresh is deterministic, including every numerical call. -/
theorem coefficientRefreshModule_noRand (b h : ℕ) :
    ∀ body ∈ coefficientRefreshModule b h,body.NoRand := by
  intro body hb
  simp only [coefficientRefreshModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb | hb
  · simp [coefficientRefreshBody,Stmt.NoRand]
  · exact lengthRefreshModule_noRand _ _ _ hb
  · exact gradientRefreshModule_noRand _ _ _ hb

/-- Actual length and gradient procedures compute both epoch coefficient
arrays with their stated errors, exact allocation, framing and total cost. -/
theorem coefficientRefresh_meetsContract {w h b q K : ℕ} {p : Program}
    (hh : 0 < h) (hw : 3*h+2 ≤ w) (hp : p.HasAt b (coefficientRefreshModule b h)) :
    MeetsContract w p b (coefficientRefreshContract w h q K) := by
  have ht := Num.hasAt_append_right hp
  have hl : p.HasAt (b+1) (lengthRefreshModule (b+1) h) := Num.hasAt_append_left ht
  have hg : p.HasAt (b+1+(lengthRefreshModule (b+1) h).length)
      (gradientRefreshModule (b+1+(lengthRefreshModule (b+1) h).length) h) :=
    Num.hasAt_append_right ht
  have hlSpec := lengthRefresh_meetsContract (q:=q) hh hw hl
  have hgSpec := gradientRefresh_meetsContract (q:=q) (K:=K) hh hw hg
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨m,cp,rp,lo,fp,up,ap,one,L,P,E,la,ga,heap,rfl,rfl,rfl,hpreL,hpreG⟩,hz,hspace⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+(Num.IPM.lengthArraySpace m L P E+Num.IPM.gradientArraySpace m L P E) < 2^w at hspace
  have hsource := hpreG.1
  obtain ⟨m',cp',rp',lo',fp',up',ap',one',L',P',E',heap',heq,
    _,_,_,_,_,_,hc,hr,hlo,hf,hup,ha,ho,_⟩ := hsource
  simp only [List.cons.injEq,and_true] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  have hargWords : ∀ x ∈ [lo,fp,up,ap,one,m,L,P,E,Num.IPM.lengthArraySpace m L P E,heap],x < 2^w := by
    intro x hx
    apply hwords x
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    tauto
  apply runs_start_le
  unfold coefficientRefreshBody
  refine runs_seq_call_le hlSpec
    (vs:=[lo,fp,up,ap,one,m,L,P,E,Num.IPM.lengthArraySpace m L P E,heap])
    (by eval_expr) hargWords ?_ ?_
  · exact ⟨⟨lo,fp,up,ap,one,m,L,P,E,_,heap,rfl,rfl,hpreL⟩,hz,
      by change heap+Num.IPM.lengthArraySpace m L P E < 2^w; omega⟩
  · intro v0 mem0 pos0 hp0
    obtain ⟨⟨_,_,hframe0,hfresh0,hlength⟩,hv0⟩ := hp0
    change v0=heap+Num.IPM.lengthArraySpace m L P E at hv0
    change ∀ x < heap,mem0 x=mem x at hframe0
    have hvw : v0 < 2^w := by omega
    have hgradPre := gradientArray_pre_frozen hpreG hframe0 (by omega : heap ≤ v0)
      hfresh0 (by omega : v0+Num.IPM.gradientArraySpace m L P E < 2^w)
    refine runs_seq_call_le hgSpec
      (vs:=[m,cp,rp,lo,fp,up,ap,one,L,P,E,Num.IPM.gradientArraySpace m L P E,v0])
      (by eval_expr) ?_ ?_ ?_
    · intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | rfl
      all_goals first | exact hx ▸ hwords _ (by simp) | exact hvw
    · exact ⟨⟨m,cp,rp,lo,fp,up,ap,one,L,P,E,_,v0,rfl,rfl,hgradPre⟩,hfresh0,
        by change v0+Num.IPM.gradientArraySpace m L P E < 2^w; omega⟩
    · intro v1 mem1 pos1 hp1
      obtain ⟨⟨_,_,hframe1,hfresh1,hgradient⟩,hv1⟩ := hp1
      change v1=v0+Num.IPM.gradientArraySpace m L P E at hv1
      change ∀ x < v0,mem1 x=mem0 x at hframe1
      change ∀ i < m,Num.Valid mem0 (heap+i*L) h L ∧
        ScalarApprox (1+1/(2:ℝ)^q) (Num.fixVal mem0 (heap+i*L) h L P)
          (Num.IPM.arrayLength mem lo fp up ap h L P i) at hlength
      change ∀ i < m,Num.Valid mem1 (v0+i*L) h L ∧
        |Num.fixVal mem1 (v0+i*L) h L P-Num.IPM.arrayGradient mem0 m cp rp lo fp up ap h L P i| ≤
          (1/(2:ℝ)^q)*Num.IPM.arrayLength mem0 lo fp up ap h L P i at hgradient
      refine runs_ret_le (v:=v1) (by eval_expr) ?_ ?_
      · change (heap ≤ v1 ∧
          v1 ≤ heap+(Num.IPM.lengthArraySpace m L P E+Num.IPM.gradientArraySpace m L P E) ∧
          (∀ x < heap,mem1 x=mem x) ∧ ZeroFrom mem1 v1 ∧
          (∀ i < m,Num.Valid mem1 (heap+i*L) h L ∧
            ScalarApprox (1+1/(2:ℝ)^q) (Num.fixVal mem1 (heap+i*L) h L P)
              (Num.IPM.arrayLength mem lo fp up ap h L P i)) ∧
          (∀ i < m,Num.Valid mem1 (heap+Num.IPM.lengthArraySpace m L P E+i*L) h L ∧
            |Num.fixVal mem1 (heap+Num.IPM.lengthArraySpace m L P E+i*L) h L P-
              Num.IPM.arrayGradient mem m cp rp lo fp up ap h L P i| ≤
              (1/(2:ℝ)^q)*Num.IPM.arrayLength mem lo fp up ap h L P i)) ∧
          v1=heap+(Num.IPM.lengthArraySpace m L P E+Num.IPM.gradientArraySpace m L P E)
        refine ⟨⟨by omega,by omega,?_,hfresh1,?_,?_⟩,by omega⟩
        · intro x hx
          exact (hframe1 x (by omega)).trans (hframe0 x hx)
        · intro i hi
          have hb : heap+i*L+L ≤ v0 := by
            have hh0 := Nat.mul_le_mul_right L (show i+1 ≤ m by omega)
            simp only [Nat.add_mul,one_mul] at hh0
            have hmL : m*L ≤ (m+1)*L := Nat.mul_le_mul_right L (by omega)
            unfold Num.IPM.lengthArraySpace at hv0
            omega
          refine ⟨Num.IPM.valid_frozen hframe1 hb (hlength i hi).1,?_⟩
          rw [Num.IPM.fixVal_frozen hframe1 hb]
          exact (hlength i hi).2
        · intro i hi
          have hb : i*L+L ≤ m*L := by
            have hh0 := Nat.mul_le_mul_right L (show i+1 ≤ m by omega)
            simpa only [Nat.add_mul,one_mul] using hh0
          have he := hgradient i hi
          rw [Num.IPM.arrayGradient_frozen hframe0 (by omega : cp+i*L+L ≤ heap) hr
              (by omega : lo+i*L+L ≤ heap) (by omega : fp+i*L+L ≤ heap)
              (by omega : up+i*L+L ≤ heap) ha,
            Num.IPM.arrayLength_frozen hframe0 (by omega : lo+i*L+L ≤ heap)
              (by omega : fp+i*L+L ≤ heap) (by omega : up+i*L+L ≤ heap) ha] at he
          simpa only [hv0] using he
      · simp only [coefficientRefreshContract,lengthRefreshContract,gradientRefreshContract,
          heapContract,List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,argsSize_cons,argsSize_nil]
        omega

end MinCostFlow.IPM.Machine
