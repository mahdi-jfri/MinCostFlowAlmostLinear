module

public import MinCostFlow.Num.IPM.GradientFromSlacks
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Computing one full IPM gradient entry

We compute the exact slacks from the flow and capacities, then call the
verified gradient calculation. The output tolerance refers to the original
edge data in Definition 4.2 of Chen et al. (page 24). Decoding equations
connect it directly to the instance's `gradient` and `lengths` functions.
-/

@[expose] public section
namespace MinCostFlow.Num.IPM
open WordRAM

/-- Arguments `[m,cost,residual,lower,flow,upper,alpha,one,L,P,E,heap]`. -/
def gradientBody (slacks gradient : ℕ) : Stmt :=
  .call 12 slacks [.reg 3,.reg 4,.reg 5,.reg 8,.reg 9,.reg 11] ;;
  .call 13 gradient [.reg 0,.reg 1,.reg 2,.bin .add (.reg 11) (.reg 8),
    .bin .add (.reg 11) (.bin .mul (.const 3) (.reg 8)),
    .reg 6,.reg 7,.reg 8,.reg 9,.reg 10,.reg 12] ;;
  .ret (.reg 13)

/-- Exact slacks followed by the complete scalar gradient calculation. -/
def gradientModule (b h : ℕ) : List Stmt :=
  [gradientBody (b+1) (b+7)] ++ (slacksModule (b+1) h ++ gradientFromSlacksModule (b+7) h)

/-- Space for the slacks and scalar gradient calculation. -/
def gradientSpace (L P E : ℕ) := 4*L+gradientFromSlacksSpace L P E

/-- Explicit polynomial cost. -/
def gradientCost (L P E : ℕ) := 148*L+gradientFromSlacksCost L P E+300

/-- The full edge-gradient contract. `K` bounds `20m` and `|20mc|`.
All fixed-point inputs have precision `P`; the cost is an unscaled integer. -/
def gradientContract (w h q K : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ m c r lo f up a one L P E heap,args=[m,c,r,lo,f,up,a,one,L,P,E,heap] ∧ h∣P ∧
      q+4*E+42≤P ∧ P+K+4*E+30≤h*L ∧ 2*P+9<2^w ∧
      20*m<2^w ∧ 20*m≤2^K ∧ |20*(m:ℤ)*intVal mem c h L|≤(2:ℤ)^K ∧
      c+L≤heap ∧ r+L≤heap ∧ lo+L≤heap ∧ f+L≤heap ∧ up+L≤heap ∧ a+L≤heap ∧ one+L≤heap ∧
      Valid mem c h L ∧ Valid mem r h L ∧ Valid mem lo h L ∧ Valid mem f h L ∧
      Valid mem up h L ∧ Valid mem a h L ∧ Valid mem one h L ∧ intVal mem one h L=(2:ℤ)^P ∧
      1/(2:ℝ)^E≤fixVal mem r h L P ∧ fixVal mem r h L P≤(2:ℝ)^E ∧
      1/(2:ℝ)^E≤fixVal mem up h L P-fixVal mem f h L P ∧
      fixVal mem up h L P-fixVal mem f h L P≤(2:ℝ)^E ∧
      1/(2:ℝ)^E≤fixVal mem f h L P-fixVal mem lo h L P ∧
      fixVal mem f h L P-fixVal mem lo h L P≤(2:ℝ)^E ∧
      0≤fixVal mem a h L P ∧ fixVal mem a h L P≤1)
    (fun _ _ _ => True)
    (fun args _ => gradientCost (args.getD 8 0) (args.getD 9 0) (args.getD 10 0))
    (fun args _ => gradientSpace (args.getD 8 0) (args.getD 9 0) (args.getD 10 0))
  {C with post := fun args mem v mem' =>
      let u := Real.rpow (fixVal mem (args.getD 5 0) h (args.getD 8 0) (args.getD 9 0)-
          fixVal mem (args.getD 4 0) h (args.getD 8 0) (args.getD 9 0))
        (-1-fixVal mem (args.getD 6 0) h (args.getD 8 0) (args.getD 9 0))
      let d := Real.rpow (fixVal mem (args.getD 4 0) h (args.getD 8 0) (args.getD 9 0)-
          fixVal mem (args.getD 3 0) h (args.getD 8 0) (args.getD 9 0))
        (-1-fixVal mem (args.getD 6 0) h (args.getD 8 0) (args.getD 9 0))
      let t := 20*(args.getD 0 0:ℝ)*(fixVal mem (args.getD 2 0) h (args.getD 8 0) (args.getD 9 0))⁻¹*
        (intVal mem (args.getD 1 0) h (args.getD 8 0):ℝ)
      C.post args mem v mem' ∧ Valid mem' (v-args.getD 8 0) h (args.getD 8 0) ∧
      |fixVal mem' (v-args.getD 8 0) h (args.getD 8 0) (args.getD 9 0)-
        (t+fixVal mem (args.getD 6 0) h (args.getD 8 0) (args.getD 9 0)*(u-d))|≤(1/(2:ℝ)^q)*(u+d)}

/-- The full gradient module contains no random statements. -/
theorem gradientModule_noRand (b h : ℕ) : ∀ s∈gradientModule b h,s.NoRand := by
  intro s hs
  simp only [gradientModule,List.mem_append,List.mem_singleton] at hs
  rcases hs with rfl | hs | hg
  · simp [gradientBody,Stmt.NoRand]
  · exact slacksModule_noRand _ _ _ hs
  · exact gradientFromSlacksModule_noRand _ _ _ hg

set_option maxRecDepth 16384 in
/-- The complete procedure satisfies the length-scaled gradient error bound
from the original stored capacities, flow, residual, cost, and alpha. -/
theorem gradient_meetsContract {w h b q K : ℕ} {p : Program}
    (hh : 0<h) (hw : 3*h+2≤w) (hp : p.HasAt b (gradientModule b h)) :
    MeetsContract w p b (gradientContract w h q K) := by
  have ht := hasAt_append_right hp
  change p.HasAt (b+1) _ at ht
  have hs := hasAt_append_left ht
  have hg := hasAt_append_right ht
  change p.HasAt (b+7) _ at hg
  have hsc := slacks_meetsContract hh (show 2*h+2≤w by omega) hs
  have hgc := gradientFromSlacks_meetsContract (q:=q) (K:=K) hh hw hg
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨m,c,r,lo,f,up,a,one,L,P,E,heap,rfl,hP,hprec,hwidth,hPw,hmw,hmB,hcB,hc,hr,hlo,hf,hup,ha,ho,hvc,hvr,hvlo,hvf,hvup,hva,hvo,hone,hrl,hrh,hul,huh,hdl,hdh,ha0,ha1⟩,hz,hbound⟩
  change ZeroFrom mem heap at hz
  change heap+gradientSpace L P E<2^w at hbound
  have hmw' : m<2^w := hwords m (by simp)
  have hcw : c<2^w := hwords c (by simp)
  have hrw : r<2^w := hwords r (by simp)
  have hlow : lo<2^w := hwords lo (by simp)
  have hfw : f<2^w := hwords f (by simp)
  have hupw : up<2^w := hwords up (by simp)
  have haw : a<2^w := hwords a (by simp)
  have how : one<2^w := hwords one (by simp)
  have hLw : L<2^w := hwords L (by simp)
  have hPword : P<2^w := hwords P (by simp)
  have hEw : E<2^w := hwords E (by simp)
  have hheapw : heap<2^w := hwords heap (by simp)
  have hU0 : 0≤fixVal mem up h L P-fixVal mem f h L P := le_trans (by positivity) hul
  have hD0 : 0≤fixVal mem f h L P-fixVal mem lo h L P := le_trans (by positivity) hdl
  apply runs_start_le
  unfold gradientBody
  refine runs_seq_call_le hsc (vs:=[lo,f,up,L,P,heap]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨_,_,_,_,_,E,_,rfl,by omega,hlo,hf,hup,hvlo,hvf,hvup,
      by simpa only [startState,abs_of_nonneg hU0] using huh,
      by simpa only [startState,abs_of_nonneg hD0] using hdh⟩,hz,
      by change heap+4*L<2^w; unfold gradientSpace at hbound; omega⟩
  · intro v₁ mem₁ pos₁ hp₁
    rcases hp₁ with ⟨he₁,hl₁,hh₁,fr₁,hz₁,hvu₁,hvd₁,hu₁,hd₁⟩
    change v₁=heap+4*L at he₁
    change (∀ z<heap,mem₁ z=mem z) at fr₁
    change Valid mem₁ (heap+L) h L at hvu₁
    change Valid mem₁ (heap+3*L) h L at hvd₁
    change fixVal mem₁ (heap+L) h L P=fixVal mem up h L P-fixVal mem f h L P at hu₁
    change fixVal mem₁ (heap+3*L) h L P=fixVal mem f h L P-fixVal mem lo h L P at hd₁
    have hcval := value_frozen (h:=h) fr₁ hc
    have hrfix := fixVal_frozen (h:=h) (P:=P) fr₁ hr
    have hafix := fixVal_frozen (h:=h) (P:=P) fr₁ ha
    have honeval := value_frozen (h:=h) fr₁ ho
    have hv₁w : v₁<2^w := by unfold gradientSpace at hbound; omega
    have hUword : heap+L<2^w := by omega
    have h3Lword : 3*L<2^w := by omega
    have hDword : heap+3*L<2^w := by omega
    refine runs_seq_call_le hgc (vs:=[m,c,r,heap+L,heap+3*L,a,one,L,P,E,v₁]) (by eval_expr) (by wram_words) ?_ ?_
    · refine ⟨⟨_,_,_,_,_,_,_,_,_,_,_,rfl,hP,hprec,hwidth,hPw,hmw,hmB,?_,
        by omega,by omega,by omega,by omega,by omega,by omega,
        valid_frozen fr₁ hc hvc,valid_frozen fr₁ hr hvr,hvu₁,hvd₁,
        valid_frozen fr₁ ha hva,valid_frozen fr₁ ho hvo,honeval.trans hone,?_,?_,?_,?_,?_,?_,?_,?_⟩,
        hz₁,by change v₁+gradientFromSlacksSpace L P E<2^w; unfold gradientSpace at hbound; omega⟩
      · rw [hcval]; exact hcB
      · rw [hrfix]; exact hrl
      · rw [hrfix]; exact hrh
      · rw [hu₁]; exact hul
      · rw [hu₁]; exact huh
      · rw [hd₁]; exact hdl
      · rw [hd₁]; exact hdh
      · rw [hafix]; exact ha0
      · rw [hafix]; exact ha1
    · intro v mem₂ pos₂ hp₂
      rcases hp₂ with ⟨⟨hl₂,hh₂,fr₂,hz₂,_⟩,hv₂,herr₂⟩
      change v₁≤v at hl₂
      change v≤v₁+gradientFromSlacksSpace L P E at hh₂
      change (∀ z<v₁,mem₂ z=mem₁ z) at fr₂
      change Valid mem₂ (v-L) h L at hv₂
      change |fixVal mem₂ (v-L) h L P-((20*(m:ℝ)*(fixVal mem₁ r h L P)⁻¹*(intVal mem₁ c h L:ℝ))+
        fixVal mem₁ a h L P*(Real.rpow (fixVal mem₁ (heap+L) h L P) (-1-fixVal mem₁ a h L P)-
          Real.rpow (fixVal mem₁ (heap+3*L) h L P) (-1-fixVal mem₁ a h L P)))|≤
        (1/(2:ℝ)^q)*(Real.rpow (fixVal mem₁ (heap+L) h L P) (-1-fixVal mem₁ a h L P)+
          Real.rpow (fixVal mem₁ (heap+3*L) h L P) (-1-fixVal mem₁ a h L P)) at herr₂
      rw [hu₁,hd₁,hafix,hcval,hrfix] at herr₂
      have hvw : v<2^w := by unfold gradientSpace at hbound; omega
      refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
      · change (heap≤v ∧ v≤heap+gradientSpace L P E ∧ (∀ z<heap,mem₂ z=mem z) ∧ ZeroFrom mem₂ v ∧ True) ∧
          Valid mem₂ (v-L) h L ∧ _
        refine ⟨⟨by omega,?_,?_,hz₂,trivial⟩,hv₂,herr₂⟩
        · unfold gradientSpace; omega
        · intro z hz
          rw [fr₂ z (by omega),fr₁ z hz]
      · simp only [gradientContract,slacksContract,gradientFromSlacksContract,heapContract,
          List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_const,Expr.size_bin,
          argsSize_cons,argsSize_nil,gradientCost]
        omega

/-- Decoding equations connect the scalar contract directly to the IPM
length and gradient functions. The residual equation is exact. -/
theorem gradient_output (I : Instance) (f : Fin I.m→ℝ) (e : Fin I.m)
    {w h q K cp rp lo fp up ap one L P E heap v : ℕ} {mem mem' : ℕ→ℕ} {a F : ℝ}
    (hout : (gradientContract w h q K).post [I.m,cp,rp,lo,fp,up,ap,one,L,P,E,heap] mem v mem')
    (hc : intVal mem cp h L=(I.edge e).cost)
    (hr : fixVal mem rp h L P=I.cost f-F)
    (hlo : fixVal mem lo h L P=(I.edge e).lower)
    (hf : fixVal mem fp h L P=f e)
    (hup : fixVal mem up h L P=(I.edge e).upper)
    (ha : fixVal mem ap h L P=a) :
    |fixVal mem' (v-L) h L P-MinCostFlow.IPM.gradient I a F f e|≤
      (1/(2:ℝ)^q)*MinCostFlow.IPM.lengths I a f e := by
  have he := hout.2.2
  change |fixVal mem' (v-L) h L P-((20*(I.m:ℝ)*(fixVal mem rp h L P)⁻¹*(intVal mem cp h L:ℝ))+
    fixVal mem ap h L P*(Real.rpow (fixVal mem up h L P-fixVal mem fp h L P) (-1-fixVal mem ap h L P)-
      Real.rpow (fixVal mem fp h L P-fixVal mem lo h L P) (-1-fixVal mem ap h L P)))|≤
    (1/(2:ℝ)^q)*(Real.rpow (fixVal mem up h L P-fixVal mem fp h L P) (-1-fixVal mem ap h L P)+
      Real.rpow (fixVal mem fp h L P-fixVal mem lo h L P) (-1-fixVal mem ap h L P)) at he
  rw [hc,hr,hlo,hf,hup,ha] at he
  have heq : MinCostFlow.IPM.gradient I a F f e=
      (20*(I.m:ℝ)*(I.cost f-F)⁻¹*((I.edge e).cost:ℝ))+
      a*(Real.rpow (((I.edge e).upper:ℝ)-f e) (-1-a)-
        Real.rpow (f e-((I.edge e).lower:ℝ)) (-1-a)) := by
    unfold MinCostFlow.IPM.gradient MinCostFlow.IPM.residual
    ring
  rw [heq]
  exact he

end MinCostFlow.Num.IPM
