module

public import MinCostFlow.Num.IPM.DotFacts
public import MinCostFlow.Num.IPM.IntegerTimes
public import MinCostFlow.Num.AddCarry
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Exact dot-product scan

A scan multiplies one integer cost by its flow numerator, adds the product
to the accumulator, and advances both arrays by one limb block. Each
product and each partial sum must fit the shared signed width. Under these
explicit fit conditions every operation is exact at the original precision.
-/

@[expose] public section
namespace MinCostFlow.Num.IPM
open WordRAM

/-- Arguments `[costs,flows,n,L,accumulator,heap]`. -/
def dotLoopBody (self mul add copy : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 2) (.const 0))
    (.call 6 copy [.reg 4,.reg 3,.reg 5] ;; .ret (.reg 6))
    (.call 6 mul [.reg 0,.reg 1,.reg 3,.reg 5] ;;
     .call 7 add [.reg 4,.bin .sub (.reg 6) (.reg 3),.reg 3,.const 0,.reg 6] ;;
     .call 8 self [.bin .add (.reg 0) (.reg 3),.bin .add (.reg 1) (.reg 3),
       .bin .sub (.reg 2) (.const 1),.reg 3,.reg 6,.reg 7] ;;
     .ret (.reg 8))

/-- The recursive scan shares arithmetic helpers between all edges. -/
def dotLoopModule (b h : ℕ) : List Stmt :=
  [dotLoopBody b (b+1) (b+8) (b+9)] ++
    (integerTimesModule (b+1) h ++ (addCarryModule (b+8) h ++ copyModule (b+9)))

/-- Exact products and exact partial sums are the only numeric fit conditions.
Inputs and accumulator stay below the initial heap; the result is at `v-L`.
Space is `(8n+1)L` and cost is `n(152L²+245L+400)+17L+100`. -/
def dotLoopContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ c f n L acc heap,args=[c,f,n,L,acc,heap] ∧
      c+n*L≤heap ∧ f+n*L≤heap ∧ acc+L≤heap ∧ Valid mem acc h L ∧
      (∀i<n,Valid mem (c+i*L) h L ∧ Valid mem (f+i*L) h L ∧
        Fits h L (intVal mem (c+i*L) h L*intVal mem (f+i*L) h L)) ∧
      (∀j≤n,Fits h L (intVal mem acc h L+dotNumerator mem c f h L j)))
    (fun args mem mem' =>
      Valid mem' (heapArg args+8*args.getD 2 0*args.getD 3 0) h (args.getD 3 0) ∧
      intVal mem' (heapArg args+8*args.getD 2 0*args.getD 3 0) h (args.getD 3 0)=
        intVal mem (args.getD 4 0) h (args.getD 3 0)+
          dotNumerator mem (args.getD 0 0) (args.getD 1 0) h (args.getD 3 0) (args.getD 2 0))
    (fun args _ => args.getD 2 0*(152*(args.getD 3 0)^2+245*args.getD 3 0+400)+17*args.getD 3 0+100)
    (fun args _ => (8*args.getD 2 0+1)*args.getD 3 0)
  {C with post := fun args mem v mem' => v=heapArg args+(8*args.getD 2 0+1)*args.getD 3 0 ∧ C.post args mem v mem'}

/-- Neither the scan nor its arithmetic helpers uses random bits. -/
theorem dotLoopModule_noRand (b h : ℕ) : ∀ s∈dotLoopModule b h,s.NoRand := by
  intro s hs
  simp only [dotLoopModule,List.mem_append,List.mem_singleton] at hs
  rcases hs with rfl | hm | ha | hc
  · simp [dotLoopBody,Stmt.NoRand]
  · exact integerTimesModule_noRand _ _ _ hm
  · simp only [addCarryModule,List.mem_singleton] at ha
    subst s
    exact addCarryBody_noRand _ _
  · simp only [copyModule,List.mem_singleton] at hc
    subst s
    exact copyBody_noRand

set_option maxHeartbeats 800000 in
/-- The left-to-right scan computes the exact accumulated dot numerator.
Its cost is quadratic in the limb width and linear in the array length. -/
theorem dotLoop_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0<h) (hw : 2*h+2≤w) (hp : p.HasAt b (dotLoopModule b h)) :
    MeetsContract w p b (dotLoopContract w h) := by
  have ht := hasAt_append_right hp
  change p.HasAt (b+1) _ at ht
  have hm := hasAt_append_left ht
  have ht₂ := hasAt_append_right ht
  change p.HasAt (b+8) _ at ht₂
  have ha := hasAt_append_left ht₂
  have hc := hasAt_append_right ht₂
  change p.HasAt (b+9) _ at hc
  have hmc := integerTimes_meetsContract hh hw hm
  have hac := addCarry_meetsContract hh hw ha
  have hw1 : 1<2^w := lt_of_lt_of_le (by decide : 1<2^1)
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hcc := copy_meetsContract (h:=h) hw1 hc
  apply meetsContract_of_rec (fun args _ => args.getD 2 0) hp.head
  intro t ih args mem pos ω hwords hpre ht
  rcases hpre with ⟨⟨c,f,n,L,acc,heap,rfl,hc,hf,hacc,hva,hblocks,hfits⟩,hz,hbound⟩
  change n=t at ht
  subst t
  change ZeroFrom mem heap at hz
  change heap+(8*n+1)*L<2^w at hbound
  have hcw : c<2^w := hwords c (by simp)
  have hfw : f<2^w := hwords f (by simp)
  have hnw : n<2^w := hwords n (by simp)
  have hLw : L<2^w := hwords L (by simp)
  have haccw : acc<2^w := hwords acc (by simp)
  have hheapw : heap<2^w := hwords heap (by simp)
  apply runs_start_le
  unfold dotLoopBody
  wram_step
  · have hn0 : n=0 := by simpa [startState] using hcond
    subst n
    refine runs_seq_call_le hcc (vs:=[acc,L,heap]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨⟨_,_,_,rfl,hacc,hva⟩,hz,by change heap+L<2^w; omega⟩
    · intro v mem₁ pos₁ hp₁
      rcases hp₁ with ⟨he,hl,hu,fr,hz₁,hlimbs,hv,hval⟩
      change v=heap+L at he
      change (∀ z<heap,mem₁ z=mem z) at fr
      change Valid mem₁ heap h L at hv
      change intVal mem₁ heap h L=intVal mem acc h L at hval
      have hvw : v<2^w := by omega
      refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
      · change v=heap+(8*0+1)*L ∧ heap≤v ∧ v≤heap+(8*0+1)*L ∧ (∀z<heap,mem₁ z=mem z) ∧
          ZeroFrom mem₁ v ∧ Valid mem₁ (heap+8*0*L) h L ∧
          intVal mem₁ (heap+8*0*L) h L=intVal mem acc h L+dotNumerator mem c f h L 0
        simpa only [Nat.mul_zero,Nat.zero_mul,zero_add,add_zero,one_mul,dotNumerator_zero] using
          (show v=heap+L ∧ heap≤v ∧ v≤heap+L ∧ (∀z<heap,mem₁ z=mem z) ∧ ZeroFrom mem₁ v ∧
            Valid mem₁ heap h L ∧ intVal mem₁ heap h L=intVal mem acc h L from
              ⟨he,by omega,by omega,fr,hz₁,hv,hval⟩)
      · simp only [dotLoopContract,copyContract,heapContract,List.getD_cons_zero,List.getD_cons_succ,
          Expr.size_reg,Expr.size_const,Expr.size_bin,argsSize_cons,argsSize_nil]
        omega
  · have hn0 : n≠0 := by simpa [startState] using hcond
    obtain ⟨N,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    simp only [Nat.succ_eq_add_one] at *
    have hnl : L≤(N+1)*L := by rw [Nat.add_mul,one_mul]; omega
    obtain ⟨hvc,hvf,hprod⟩ := hblocks 0 (by omega)
    simp only [zero_mul,add_zero] at hvc hvf hprod
    have hsumFit : Fits h L (intVal mem acc h L+intVal mem c h L*intVal mem f h L+0) := by
      have he := hfits 1 (by omega)
      simpa only [dotNumerator_succ,dotNumerator_zero,add_zero] using he
    refine runs_seq_call_le hmc (vs:=[c,f,L,heap]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨⟨_,_,_,_,rfl,by omega,by omega,hvc,hvf,hprod⟩,hz,
        by change heap+7*L<2^w; nlinarith only [hbound,Nat.zero_le N]⟩
    · intro v₁ mem₁ pos₁ hp₁
      rcases hp₁ with ⟨he₁,hl₁,hh₁,fr₁,hz₁,hv₁,hval₁⟩
      change v₁=heap+7*L at he₁
      change (∀z<heap,mem₁ z=mem z) at fr₁
      change Valid mem₁ (heap+6*L) h L at hv₁
      change intVal mem₁ (heap+6*L) h L=intVal mem c h L*intVal mem f h L at hval₁
      have hptr₁ : v₁-L=heap+6*L := by omega
      have haval₁ := value_frozen (h:=h) fr₁ hacc
      have hsumFit₁ : Fits h L (intVal mem₁ acc h L+intVal mem₁ (v₁-L) h L+0) := by
        rw [hptr₁,hval₁,haval₁]; exact hsumFit
      have hv₁w : v₁<2^w := by nlinarith only [hbound,he₁,Nat.zero_le N]
      have hp₁w : v₁-L<2^w := by omega
      refine runs_seq_call_le hac (vs:=[acc,v₁-L,L,0,v₁]) (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨⟨_,_,_,_,_,rfl,by omega,by omega,by decide,valid_frozen fr₁ hacc hva,hptr₁.symm ▸ hv₁⟩,
          hz₁,by change v₁+L<2^w; nlinarith only [hbound,he₁,Nat.zero_le N]⟩
      · intro v₂ mem₂ pos₂ hp₂
        rcases hp₂ with ⟨he₂,hl₂,hh₂,fr₂,hz₂,hlist₂⟩
        change v₂=v₁+L at he₂
        change (∀z<v₁,mem₂ z=mem₁ z) at fr₂
        change ListAt mem₂ v₁ (digits h L (unsignedVal mem₁ acc h L+unsignedVal mem₁ (v₁-L) h L+0)) at hlist₂
        have hv₂ := (addCarry_value hlist₂).1
        have hval₂ := addCarry_value_of_fits hlist₂ hsumFit₁
        simp only [Nat.cast_zero,add_zero] at hval₂
        rw [hptr₁,hval₁,haval₁] at hval₂
        have hfr : ∀z<heap,mem₂ z=mem z := fun z hz => (fr₂ z (by omega)).trans (fr₁ z hz)
        have hcs : c+L+N*L≤heap := by nlinarith only [hc]
        have hfs : f+L+N*L≤heap := by nlinarith only [hf]
        have hblockTail : ∀i<N,Valid mem₂ (c+L+i*L) h L ∧ Valid mem₂ (f+L+i*L) h L ∧
            Fits h L (intVal mem₂ (c+L+i*L) h L*intVal mem₂ (f+L+i*L) h L) := by
          intro i hi
          have hcaddr : c+L+i*L=c+(i+1)*L := by ring
          have hfaddr : f+L+i*L=f+(i+1)*L := by ring
          rw [hcaddr,hfaddr]
          obtain ⟨hcV,hfV,hfit⟩ := hblocks (i+1) (by omega)
          have hib : (i+1)*L+L≤(N+1)*L := by
            have he := Nat.mul_le_mul_right L (show i+2≤N+1 by omega)
            nlinarith only [he]
          refine ⟨valid_frozen hfr (by omega) hcV,valid_frozen hfr (by omega) hfV,?_⟩
          rw [value_frozen (h:=h) hfr (show c+(i+1)*L+L≤heap by omega),
              value_frozen (h:=h) hfr (show f+(i+1)*L+L≤heap by omega)]
          exact hfit
        have hfitsTail : ∀j≤N,Fits h L (intVal mem₂ v₁ h L+dotNumerator mem₂ (c+L) (f+L) h L j) := by
          intro j hj
          have hjL : j*L≤N*L := Nat.mul_le_mul_right L hj
          rw [hval₂,dotNumerator_frozen hfr (show c+L+j*L≤heap by omega) (show f+L+j*L≤heap by omega)]
          have he := hfits (j+1) (by omega)
          rw [dotNumerator_succ] at he
          simpa only [add_assoc] using he
        have hrec : MeetsContract w p b ((dotLoopContract w h).below (fun args _ => args.getD 2 0) (N+1)) := ih
        have hv₂w : v₂<2^w := by nlinarith only [hbound,he₁,he₂,Nat.zero_le N]
        have hcw' : c+L<2^w := by omega
        have hfw' : f+L<2^w := by omega
        have hNw : N<2^w := by omega
        have hNdec : N<N+1 := by omega
        refine runs_seq_call_le hrec (vs:=[c+L,f+L,N,L,v₁,v₂]) (by
          eval_expr
          conv_rhs => rw [← Nat.add_sub_cancel N 1]
          exact Expr.eval_sub (a:=.reg 2) (b:=.const 1) (x:=N+1) (y:=1)
            (by eval_expr) (by eval_expr) hnw) (by wram_words) ?_ ?_
        · refine ⟨⟨⟨_,_,_,_,_,_,rfl,by omega,by omega,by omega,hv₂,hblockTail,hfitsTail⟩,hz₂,?_⟩,?_⟩
          · change v₂+(8*N+1)*L<2^w
            nlinarith only [hbound,he₁,he₂]
          · change N<N+1; omega
        · intro v mem₃ pos₃ hp₃
          rcases hp₃ with ⟨he₃,hl₃,hh₃,fr₃,hz₃,hv₃,hval₃⟩
          change v=v₂+(8*N+1)*L at he₃
          change (∀z<v₂,mem₃ z=mem₂ z) at fr₃
          change Valid mem₃ (v₂+8*N*L) h L at hv₃
          change intVal mem₃ (v₂+8*N*L) h L=intVal mem₂ v₁ h L+dotNumerator mem₂ (c+L) (f+L) h L N at hval₃
          rw [hval₂,dotNumerator_frozen hfr hcs hfs] at hval₃
          have hpout : v₂+8*N*L=heap+8*(N+1)*L := by nlinarith only [he₁,he₂]
          rw [hpout] at hv₃ hval₃
          have hvw : v<2^w := by nlinarith only [hbound,he₁,he₂,he₃]
          refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
          · change v=heap+(8*(N+1)+1)*L ∧ heap≤v ∧ v≤heap+(8*(N+1)+1)*L ∧
              (∀z<heap,mem₃ z=mem z) ∧ ZeroFrom mem₃ v ∧ Valid mem₃ (heap+8*(N+1)*L) h L ∧
              intVal mem₃ (heap+8*(N+1)*L) h L=intVal mem acc h L+dotNumerator mem c f h L (N+1)
            refine ⟨by nlinarith only [he₁,he₂,he₃],by omega,by nlinarith only [he₁,he₂,he₃],?_,hz₃,hv₃,?_⟩
            · intro z hz
              rw [fr₃ z (by omega),hfr z hz]
            · rw [dotNumerator_succ,← add_assoc]
              exact hval₃
          · simp only [dotLoopContract,Contract.below,integerTimesContract,addCarryContract,heapContract,
              List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_const,Expr.size_bin,
              argsSize_cons,argsSize_nil]
            ring_nf
            omega

end MinCostFlow.Num.IPM
