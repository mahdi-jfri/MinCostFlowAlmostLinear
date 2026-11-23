module

public import MinCostFlow.Num.IPM.Dot
public import MinCostFlow.Num.IPM.Slacks
public import MinCostFlow.IPM.Definitions
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Exact residual formation

The residual in Definition 4.2 of Chen et al. (page 24) is `cᵀf-F`.
The dot product and target have the same fixed-point precision, so exact
subtraction forms the residual with no error, whenever the difference fits.
-/

@[expose] public section
namespace MinCostFlow.Num.IPM
open WordRAM

/-- Arguments `[costs,flows,n,target,L,heap]`. -/
def residualBody (dot sub : ℕ) : Stmt :=
  .call 6 dot [.reg 0,.reg 1,.reg 2,.reg 4,.reg 5] ;;
  .call 7 sub [.bin .sub (.reg 6) (.reg 4),.reg 3,.reg 4,.reg 6] ;;
  .ret (.reg 7)

/-- Exact dot product followed by exact target subtraction. -/
def residualModule (b h : ℕ) : List Stmt :=
  [residualBody (b+1) (b+13)] ++ (dotModule (b+1) h ++ subtractModule (b+13) h)

/-- All dot-product products and prefix sums, and the final difference, fit.
The result is at `v-L`, using `(8n+4)L` fresh cells. -/
def residualContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ c f n target L heap,args=[c,f,n,target,L,heap] ∧
      c+n*L≤heap ∧ f+n*L≤heap ∧ target+L≤heap ∧ Valid mem target h L ∧
      (∀i<n,Valid mem (c+i*L) h L ∧ Valid mem (f+i*L) h L ∧
        Fits h L (intVal mem (c+i*L) h L*intVal mem (f+i*L) h L)) ∧
      (∀j≤n,Fits h L (dotNumerator mem c f h L j)) ∧
      Fits h L (dotNumerator mem c f h L n-intVal mem target h L))
    (fun args mem mem' =>
      Valid mem' (heapArg args+(8*args.getD 2 0+3)*args.getD 4 0) h (args.getD 4 0) ∧
      intVal mem' (heapArg args+(8*args.getD 2 0+3)*args.getD 4 0) h (args.getD 4 0)=
        dotNumerator mem (args.getD 0 0) (args.getD 1 0) h (args.getD 4 0) (args.getD 2 0)-
          intVal mem (args.getD 3 0) h (args.getD 4 0))
    (fun args _ => args.getD 2 0*(152*(args.getD 4 0)^2+245*args.getD 4 0+400)+114*args.getD 4 0+300)
    (fun args _ => (8*args.getD 2 0+4)*args.getD 4 0)
  {C with post := fun args mem v mem' => v=heapArg args+(8*args.getD 2 0+4)*args.getD 4 0 ∧ C.post args mem v mem'}

/-- Residual formation is deterministic. -/
theorem residualModule_noRand (b h : ℕ) : ∀ s∈residualModule b h,s.NoRand := by
  intro s hs
  simp only [residualModule,List.mem_append,List.mem_singleton] at hs
  rcases hs with rfl | hd | hs
  · simp [residualBody,Stmt.NoRand]
  · exact dotModule_noRand _ _ _ hd
  · exact subtractModule_noRand _ _ _ hs

/-- Exact residual formation preserves both source arrays and the target. -/
theorem residual_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0<h) (hw : 2*h+2≤w) (hp : p.HasAt b (residualModule b h)) :
    MeetsContract w p b (residualContract w h) := by
  have ht := hasAt_append_right hp
  change p.HasAt (b+1) _ at ht
  have hd := hasAt_append_left ht
  have hs := hasAt_append_right ht
  change p.HasAt (b+13) _ at hs
  have hdc := dot_meetsContract hh hw hd
  have hsc := subtract_meetsContract hh hw hs
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨c,f,n,target,L,heap,rfl,hc,hf,ht,hvt,hblocks,hfits,hfit⟩,hz,hbound⟩
  change ZeroFrom mem heap at hz
  change heap+(8*n+4)*L<2^w at hbound
  have hcw : c<2^w := hwords c (by simp)
  have hfw : f<2^w := hwords f (by simp)
  have hnw : n<2^w := hwords n (by simp)
  have htw : target<2^w := hwords target (by simp)
  have hLw : L<2^w := hwords L (by simp)
  have hheapw : heap<2^w := hwords heap (by simp)
  apply runs_start_le
  unfold residualBody
  refine runs_seq_call_le hdc (vs:=[c,f,n,L,heap]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨_,_,_,_,_,rfl,hc,hf,hblocks,hfits⟩,hz,
      by change heap+(8*n+2)*L<2^w; nlinarith only [hbound]⟩
  · intro v₁ mem₁ pos₁ hp₁
    rcases hp₁ with ⟨he₁,hl₁,hh₁,fr₁,hz₁,hv₁,hval₁⟩
    change v₁=heap+(8*n+2)*L at he₁
    change (∀z<heap,mem₁ z=mem z) at fr₁
    change Valid mem₁ (heap+(8*n+1)*L) h L at hv₁
    change intVal mem₁ (heap+(8*n+1)*L) h L=dotNumerator mem c f h L n at hval₁
    have hev₁ : v₁=heap+(8*n+1)*L+L := by nlinarith only [he₁]
    have hptr₁ : v₁-L=heap+(8*n+1)*L := by omega
    have htval := value_frozen (h:=h) fr₁ ht
    have hv₁w : v₁<2^w := by nlinarith only [hbound,he₁]
    have hptr₁w : v₁-L<2^w := by omega
    refine runs_seq_call_le hsc (vs:=[v₁-L,target,L,v₁]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨⟨_,_,_,_,rfl,by omega,by omega,hptr₁.symm ▸ hv₁,valid_frozen fr₁ ht hvt⟩,hz₁,
        by change v₁+2*L<2^w; nlinarith only [hbound,he₁]⟩
    · intro v mem₂ pos₂ hp₂
      rcases hp₂ with ⟨he₂,hl₂,hh₂,fr₂,hz₂,hv₂,hval₂⟩
      change v=v₁+2*L at he₂
      change (∀z<v₁,mem₂ z=mem₁ z) at fr₂
      change Valid mem₂ (v₁+L) h L at hv₂
      change intVal mem₂ (v₁+L) h L=wrap h L (intVal mem₁ (v₁-L) h L-intVal mem₁ target h L) at hval₂
      rw [hptr₁,hval₁,htval,wrap_of_fits hfit] at hval₂
      have hout : v₁+L=heap+(8*n+3)*L := by nlinarith only [he₁]
      rw [hout] at hv₂ hval₂
      have hvw : v<2^w := by nlinarith only [hbound,he₁,he₂]
      refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
      · change v=heap+(8*n+4)*L ∧ heap≤v ∧ v≤heap+(8*n+4)*L ∧ (∀z<heap,mem₂ z=mem z) ∧
          ZeroFrom mem₂ v ∧ Valid mem₂ (heap+(8*n+3)*L) h L ∧
          intVal mem₂ (heap+(8*n+3)*L) h L=dotNumerator mem c f h L n-intVal mem target h L
        refine ⟨by nlinarith only [he₁,he₂],by omega,by nlinarith only [he₁,he₂],?_,hz₂,hv₂,hval₂⟩
        intro z hz
        rw [fr₂ z (by omega),fr₁ z hz]
      · simp only [residualContract,dotContract,subtractContract,heapContract,
          List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_const,Expr.size_bin,argsSize_cons,argsSize_nil]
        omega

/-- Residual outputs decode exactly as dot product minus the target at any
shared precision. -/
theorem residual_output {w h c f n target L heap v P : ℕ} {mem mem' : ℕ→ℕ}
    (hout : (residualContract w h).post [c,f,n,target,L,heap] mem v mem') :
    fixVal mem' (v-L) h L P=
      (∑i∈Finset.range n,(intVal mem (c+i*L) h L:ℝ)*fixVal mem (f+i*L) h L P)-
        fixVal mem target h L P := by
  have hv := hout.1
  have he := hout.2.2.2.2.2.2
  change v=heap+(8*n+4)*L at hv
  change intVal mem' (heap+(8*n+3)*L) h L=dotNumerator mem c f h L n-intVal mem target h L at he
  have hv' : v=heap+(8*n+3)*L+L := by nlinarith only [hv]
  have hp : v-L=heap+(8*n+3)*L := by omega
  rw [hp,fixVal,he,scaled_sub,dotNumerator_scaled]
  rfl

/-- Decoding the arrays of an instance identifies the exact machine dot
product with `I.cost f`. -/
theorem dot_output_instance (I : Instance) (f : Fin I.m→ℝ)
    {w h cp fp L heap v P : ℕ} {mem mem' : ℕ→ℕ}
    (hout : (dotContract w h).post [cp,fp,I.m,L,heap] mem v mem')
    (hc : ∀e : Fin I.m,intVal mem (cp+e.val*L) h L=(I.edge e).cost)
    (hf : ∀e : Fin I.m,fixVal mem (fp+e.val*L) h L P=f e) :
    fixVal mem' (v-L) h L P=I.cost f := by
  rw [dot_output hout,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro e he
  rw [hc e,hf e]

/-- Residual formation gives the exact residual expected by the per-edge
gradient contract, when the arrays decode the instance and flow. -/
theorem residual_output_instance (I : Instance) (f : Fin I.m→ℝ)
    {w h cp fp tp L heap v P : ℕ} {mem mem' : ℕ→ℕ} {F : ℝ}
    (hout : (residualContract w h).post [cp,fp,I.m,tp,L,heap] mem v mem')
    (hc : ∀e : Fin I.m,intVal mem (cp+e.val*L) h L=(I.edge e).cost)
    (hf : ∀e : Fin I.m,fixVal mem (fp+e.val*L) h L P=f e)
    (hF : fixVal mem tp h L P=F) :
    fixVal mem' (v-L) h L P=MinCostFlow.IPM.residual I F f := by
  rw [residual_output hout,hF,← Fin.sum_univ_eq_sum_range]
  unfold MinCostFlow.IPM.residual Instance.cost
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  rw [hc e,hf e]

end MinCostFlow.Num.IPM
