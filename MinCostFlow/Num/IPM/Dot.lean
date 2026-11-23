module

public import MinCostFlow.Num.IPM.DotLoop
public import MinCostFlow.Num.LoadSmall
import MinCostFlow.Num.ModulePlacement
import MinCostFlow.Num.WordBounds
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Exact cost-flow dot products on arrays

Initialize a zero accumulator and scan consecutive cost and flow blocks.
Integer costs preserve the flow's fixed-point scale. When products and
partial sums fit, the returned block is the exact dot product, so residual
formation requires only an exact subtraction at that same precision.
-/

@[expose] public section
namespace MinCostFlow.Num.IPM
open WordRAM

/-- Arguments `[costs,flows,n,L,heap]`. -/
def dotBody (load loop : ℕ) : Stmt :=
  .call 5 load [.const 0,.reg 3,.reg 4] ;;
  .call 6 loop [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5] ;;
  .ret (.reg 6)

/-- Zero initialization and the exact dot-product scan. -/
def dotModule (b h : ℕ) : List Stmt :=
  [dotBody (b+1) (b+2)] ++ (loadSmallModule (b+1) h ++ dotLoopModule (b+2) h)

/-- Costs are unscaled signed integers and flows share any fixed precision.
Each product and each prefix sum must fit the signed `L`-limb format. -/
def dotContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ c f n L heap,args=[c,f,n,L,heap] ∧ c+n*L≤heap ∧ f+n*L≤heap ∧
      (∀i<n,Valid mem (c+i*L) h L ∧ Valid mem (f+i*L) h L ∧
        Fits h L (intVal mem (c+i*L) h L*intVal mem (f+i*L) h L)) ∧
      (∀j≤n,Fits h L (dotNumerator mem c f h L j)))
    (fun args mem mem' =>
      Valid mem' (heapArg args+(8*args.getD 2 0+1)*args.getD 3 0) h (args.getD 3 0) ∧
      intVal mem' (heapArg args+(8*args.getD 2 0+1)*args.getD 3 0) h (args.getD 3 0)=
        dotNumerator mem (args.getD 0 0) (args.getD 1 0) h (args.getD 3 0) (args.getD 2 0))
    (fun args _ => args.getD 2 0*(152*(args.getD 3 0)^2+245*args.getD 3 0+400)+40*args.getD 3 0+200)
    (fun args _ => (8*args.getD 2 0+2)*args.getD 3 0)
  {C with post := fun args mem v mem' => v=heapArg args+(8*args.getD 2 0+2)*args.getD 3 0 ∧ C.post args mem v mem'}

/-- Dot products use no random bits. -/
theorem dotModule_noRand (b h : ℕ) : ∀ s∈dotModule b h,s.NoRand := by
  intro s hs
  simp only [dotModule,List.mem_append,List.mem_singleton] at hs
  rcases hs with rfl | hl | hd
  · simp [dotBody,Stmt.NoRand]
  · simp only [loadSmallModule,List.mem_singleton] at hl
    subst s
    exact loadSmallBody_noRand _ _
  · exact dotLoopModule_noRand _ _ _ hd

/-- The complete dot-product procedure computes the exact numerator with
space `(8n+2)L` and time `n(152L²+245L+400)+40L+200`. -/
theorem dot_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0<h) (hw : 2*h+2≤w) (hp : p.HasAt b (dotModule b h)) :
    MeetsContract w p b (dotContract w h) := by
  have ht := hasAt_append_right hp
  change p.HasAt (b+1) _ at ht
  have hl := hasAt_append_left ht
  have hd := hasAt_append_right ht
  change p.HasAt (b+2) _ at hd
  have hw1 : 1<2^w := lt_trans (Nat.one_lt_pow (Nat.ne_of_gt hh) (by decide)) (base_lt_word hw)
  have hlc := loadSmall_meetsContract hw1 (base_lt_word hw) hl
  have hdc := dotLoop_meetsContract hh hw hd
  have hw0 : 0<2^w := pow_pos (by decide) w
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨c,f,n,L,heap,rfl,hc,hf,hblocks,hfits⟩,hz,hbound⟩
  change ZeroFrom mem heap at hz
  change heap+(8*n+2)*L<2^w at hbound
  have hcw : c<2^w := hwords c (by simp)
  have hfw : f<2^w := hwords f (by simp)
  have hnw : n<2^w := hwords n (by simp)
  have hLw : L<2^w := hwords L (by simp)
  have hheapw : heap<2^w := hwords heap (by simp)
  have hspace : L≤(8*n+2)*L := by nlinarith only [Nat.zero_le n]
  apply runs_start_le
  unfold dotBody
  refine runs_seq_call_le hlc (vs:=[0,L,heap]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨_,_,_,rfl⟩,hz,by change heap+L<2^w; omega⟩
  · intro v₁ mem₁ pos₁ hp₁
    rcases hp₁ with ⟨he₁,hl₁,hh₁,fr₁,hz₁,hlist₁⟩
    change v₁=heap+L at he₁
    change (∀z<heap,mem₁ z=mem z) at fr₁
    change ListAt mem₁ heap (digits h L 0) at hlist₁
    have hv₁ := (loadSmall_value hlist₁).1
    have hval₁ : intVal mem₁ heap h L=0 := by
      simpa only [Nat.zero_mod,signedVal_zero] using (loadSmall_value hlist₁).2.2
    have hblocks₁ : ∀i<n,Valid mem₁ (c+i*L) h L ∧ Valid mem₁ (f+i*L) h L ∧
        Fits h L (intVal mem₁ (c+i*L) h L*intVal mem₁ (f+i*L) h L) := by
      intro i hi
      have hib : i*L+L≤n*L := by
        have ht := Nat.mul_le_mul_right L (show i+1≤n by omega)
        simpa only [Nat.add_mul,one_mul] using ht
      obtain ⟨hcV,hfV,hfit⟩ := hblocks i hi
      refine ⟨valid_frozen fr₁ (by omega) hcV,valid_frozen fr₁ (by omega) hfV,?_⟩
      rw [value_frozen (h:=h) fr₁ (show c+i*L+L≤heap by omega),
          value_frozen (h:=h) fr₁ (show f+i*L+L≤heap by omega)]
      exact hfit
    have hfits₁ : ∀j≤n,Fits h L (intVal mem₁ heap h L+dotNumerator mem₁ c f h L j) := by
      intro j hj
      have hjL := Nat.mul_le_mul_right L hj
      rw [hval₁,zero_add,dotNumerator_frozen fr₁ (show c+j*L≤heap by omega) (show f+j*L≤heap by omega)]
      exact hfits j hj
    have hv₁w : v₁<2^w := by omega
    refine runs_seq_call_le hdc (vs:=[c,f,n,L,heap,v₁]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨⟨_,_,_,_,_,_,rfl,by omega,by omega,by omega,hv₁,hblocks₁,hfits₁⟩,hz₁,
        by change v₁+(8*n+1)*L<2^w; nlinarith only [hbound,he₁]⟩
    · intro v mem₂ pos₂ hp₂
      rcases hp₂ with ⟨he₂,hl₂,hh₂,fr₂,hz₂,hv₂,hval₂⟩
      change v=v₁+(8*n+1)*L at he₂
      change (∀z<v₁,mem₂ z=mem₁ z) at fr₂
      change Valid mem₂ (v₁+8*n*L) h L at hv₂
      change intVal mem₂ (v₁+8*n*L) h L=intVal mem₁ heap h L+dotNumerator mem₁ c f h L n at hval₂
      rw [hval₁,zero_add,dotNumerator_frozen fr₁ hc hf] at hval₂
      have hout : v₁+8*n*L=heap+(8*n+1)*L := by nlinarith only [he₁]
      rw [hout] at hv₂ hval₂
      have hvw : v<2^w := by nlinarith only [hbound,he₁,he₂]
      refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
      · change v=heap+(8*n+2)*L ∧ heap≤v ∧ v≤heap+(8*n+2)*L ∧ (∀z<heap,mem₂ z=mem z) ∧
          ZeroFrom mem₂ v ∧ Valid mem₂ (heap+(8*n+1)*L) h L ∧
          intVal mem₂ (heap+(8*n+1)*L) h L=dotNumerator mem c f h L n
        refine ⟨by nlinarith only [he₁,he₂],by omega,by nlinarith only [he₁,he₂],?_,hz₂,hv₂,hval₂⟩
        intro z hz
        rw [fr₂ z (by omega),fr₁ z hz]
      · simp only [dotContract,loadSmallContract,dotLoopContract,heapContract,
          List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_const,Expr.size_bin,argsSize_cons,argsSize_nil]
        omega

/-- The dot-product output is exact at every precision shared by the flow
blocks. No divisibility or alignment condition on `P` is needed. -/
theorem dot_output {w h c f n L heap v P : ℕ} {mem mem' : ℕ→ℕ}
    (hout : (dotContract w h).post [c,f,n,L,heap] mem v mem') :
    fixVal mem' (v-L) h L P=
      ∑i∈Finset.range n,(intVal mem (c+i*L) h L:ℝ)*fixVal mem (f+i*L) h L P := by
  have hv := hout.1
  have he := hout.2.2.2.2.2.2
  change v=heap+(8*n+2)*L at hv
  change intVal mem' (heap+(8*n+1)*L) h L=dotNumerator mem c f h L n at he
  have hv' : v=heap+(8*n+1)*L+L := by nlinarith only [hv]
  have hp : v-L=heap+(8*n+1)*L := by omega
  rw [hp,fixVal,he]
  exact dotNumerator_scaled _ _ _ _ _ _ _

end MinCostFlow.Num.IPM
