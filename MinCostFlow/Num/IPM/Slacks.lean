module

public import MinCostFlow.Num.Subtract
public import MinCostFlow.Num.IPM.FixedPointFacts
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Exact slack computation for one edge

The two slacks in Definition 4.2 of Chen et al. (page 24) are differences
of numbers at the same precision. Subtraction therefore introduces no
rounding. Two signed guard bits above the slack range prevent overflow.
The sources stay below the heap and the two result blocks are fresh.
-/

@[expose] public section
namespace MinCostFlow.Num.IPM
open WordRAM

/-- Arguments `[lower,flow,upper,L,P,heap]`. -/
def slacksBody (sub : ℕ) : Stmt :=
  .call 6 sub [.reg 2,.reg 1,.reg 3,.reg 5] ;;
  .call 7 sub [.reg 1,.reg 0,.reg 3,.reg 6] ;;
  .ret (.reg 7)

/-- Both slack calculations share the signed subtraction module. -/
def slacksModule (b h : ℕ) : List Stmt :=
  [slacksBody (b+1)] ++ subtractModule (b+1) h

/-- Exact slacks at `heap+L` and `heap+3L`, with `4L` fresh cells.
The precision is unchanged. The explicit cost is `148L+120`. -/
def slacksContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ lo f up L P E heap,args=[lo,f,up,L,P,heap] ∧
      P+E+2≤h*L ∧ lo+L≤heap ∧ f+L≤heap ∧ up+L≤heap ∧
      Valid mem lo h L ∧ Valid mem f h L ∧ Valid mem up h L ∧
      |fixVal mem up h L P-fixVal mem f h L P|≤(2:ℝ)^E ∧
      |fixVal mem f h L P-fixVal mem lo h L P|≤(2:ℝ)^E)
    (fun args mem mem' =>
      Valid mem' (heapArg args+args.getD 3 0) h (args.getD 3 0) ∧
      Valid mem' (heapArg args+3*args.getD 3 0) h (args.getD 3 0) ∧
      fixVal mem' (heapArg args+args.getD 3 0) h (args.getD 3 0) (args.getD 4 0)=
        fixVal mem (args.getD 2 0) h (args.getD 3 0) (args.getD 4 0)-
          fixVal mem (args.getD 1 0) h (args.getD 3 0) (args.getD 4 0) ∧
      fixVal mem' (heapArg args+3*args.getD 3 0) h (args.getD 3 0) (args.getD 4 0)=
        fixVal mem (args.getD 1 0) h (args.getD 3 0) (args.getD 4 0)-
          fixVal mem (args.getD 0 0) h (args.getD 3 0) (args.getD 4 0))
    (fun args _ => 148*args.getD 3 0+120) (fun args _ => 4*args.getD 3 0)
  {C with post := fun args mem v mem' => v=heapArg args+4*args.getD 3 0 ∧ C.post args mem v mem'}

/-- Slack computation uses no random instructions. -/
theorem slacksModule_noRand (b h : ℕ) : ∀ s∈slacksModule b h,s.NoRand := by
  intro s hs
  simp only [slacksModule,List.mem_append,List.mem_singleton] at hs
  rcases hs with rfl | hs
  · simp [slacksBody,Stmt.NoRand]
  · exact subtractModule_noRand _ _ _ hs

/-- The machine computes both real slack differences exactly. -/
theorem slacks_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0<h) (hw : 2*h+2≤w) (hp : p.HasAt b (slacksModule b h)) :
    MeetsContract w p b (slacksContract w h) := by
  have hs := hasAt_append_right hp
  change p.HasAt (b+1) (subtractModule (b+1) h) at hs
  have hc := subtract_meetsContract hh hw hs
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨lo,f,up,L,P,E,heap,rfl,hwidth,hlo,hf,hup,hvlo,hvf,hvup,hu,hd⟩,hz,hbound⟩
  change ZeroFrom mem heap at hz
  change heap+4*L<2^w at hbound
  have hfitU : Fits h L (intVal mem up h L-intVal mem f h L) :=
    fits_of_scaled_bound hwidth (by simpa only [scaled_sub,fixVal] using hu)
  have hfitD : Fits h L (intVal mem f h L-intVal mem lo h L) :=
    fits_of_scaled_bound hwidth (by simpa only [scaled_sub,fixVal] using hd)
  have hlow : lo<2^w := hwords lo (by simp)
  have hfw : f<2^w := hwords f (by simp)
  have hupw : up<2^w := hwords up (by simp)
  have hLw : L<2^w := hwords L (by simp)
  have hheapw : heap<2^w := hwords heap (by simp)
  apply runs_start_le
  unfold slacksBody
  refine runs_seq_call_le hc (vs:=[up,f,L,heap]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨_,_,_,_,rfl,hup,hf,hvup,hvf⟩,hz,by change heap+2*L<2^w; omega⟩
  · intro v₁ mem₁ pos₁ hp₁
    rcases hp₁ with ⟨he₁,hl₁,hh₁,fr₁,hz₁,hv₁,heq₁⟩
    change v₁=heap+2*L at he₁
    change (∀ z<heap,mem₁ z=mem z) at fr₁
    change Valid mem₁ (heap+L) h L at hv₁
    change intVal mem₁ (heap+L) h L=wrap h L (intVal mem up h L-intVal mem f h L) at heq₁
    rw [wrap_of_fits hfitU] at heq₁
    have hflow₁ := valid_frozen fr₁ hf hvf
    have hlower₁ := valid_frozen fr₁ hlo hvlo
    have hflowval₁ := value_frozen (h:=h) fr₁ hf
    have hlowerval₁ := value_frozen (h:=h) fr₁ hlo
    have hv₁w : v₁<2^w := by omega
    refine runs_seq_call_le hc (vs:=[f,lo,L,v₁]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨⟨_,_,_,_,rfl,by omega,by omega,hflow₁,hlower₁⟩,hz₁,
        by change v₁+2*L<2^w; omega⟩
    · intro v₂ mem₂ pos₂ hp₂
      rcases hp₂ with ⟨he₂,hl₂,hh₂,fr₂,hz₂,hv₂,heq₂⟩
      change v₂=v₁+2*L at he₂
      change (∀ z<v₁,mem₂ z=mem₁ z) at fr₂
      change Valid mem₂ (v₁+L) h L at hv₂
      change intVal mem₂ (v₁+L) h L=wrap h L (intVal mem₁ f h L-intVal mem₁ lo h L) at heq₂
      rw [hflowval₁,hlowerval₁,wrap_of_fits hfitD] at heq₂
      have hv₂w : v₂<2^w := by omega
      refine runs_ret_le (v:=v₂) (by eval_expr) ?_ ?_
      · refine ⟨by change v₂=heap+4*L; omega,?_⟩
        change heap≤v₂ ∧ v₂≤heap+4*L ∧ (∀ z<heap,mem₂ z=mem z) ∧
          ZeroFrom mem₂ v₂ ∧ Valid mem₂ (heap+L) h L ∧
          Valid mem₂ (heap+3*L) h L ∧
          fixVal mem₂ (heap+L) h L P=fixVal mem up h L P-fixVal mem f h L P ∧
          fixVal mem₂ (heap+3*L) h L P=fixVal mem f h L P-fixVal mem lo h L P
        refine ⟨by omega,by omega,?_,hz₂,valid_frozen fr₂ (by omega) hv₁,?_,?_,?_⟩
        · intro z hz
          rw [fr₂ z (by omega),fr₁ z hz]
        · convert hv₂ using 1 <;> omega
        · rw [fixVal_frozen fr₂ (by omega)]
          simp only [fixVal,heq₁,scaled_sub]
        · have he : heap+3*L=v₁+L := by omega
          rw [he]
          simp only [fixVal,heq₂,scaled_sub]
      · simp only [slacksContract,subtractContract,heapContract,List.getD_cons_zero,
          List.getD_cons_succ,Expr.size_reg,argsSize_cons,argsSize_nil]
        omega

end MinCostFlow.Num.IPM
