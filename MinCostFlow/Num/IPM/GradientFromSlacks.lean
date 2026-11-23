module

public import MinCostFlow.Num.IPM.CostTerm
public import MinCostFlow.Num.IPM.BarrierFromSlacks
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Computing a gradient entry from stored slacks

Definition 4.2 of Chen et al. (page 24) adds the cost term to the barrier
term. We compute these separately and add their stored results exactly.
The lower bound on either slack power covers both rounding units, so the
final absolute error is bounded by `2^-q` times the exact edge length.
-/

@[expose] public section
namespace MinCostFlow.Num.IPM
open WordRAM

/-- Arguments `[m,cost,residual,upperSlack,lowerSlack,alpha,one,L,P,E,heap]`. -/
def gradientFromSlacksBody (cost barrier add : ℕ) : Stmt :=
  .call 11 cost [.reg 0,.reg 1,.reg 2,.reg 7,.reg 8,.reg 10] ;;
  .call 12 barrier [.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,.reg 8,.reg 9,.reg 11] ;;
  .call 13 add [.bin .sub (.reg 11) (.reg 7),.bin .sub (.reg 12) (.reg 7),.reg 7,.const 0,.reg 12] ;;
  .ret (.reg 13)

/-- Closed modules for the cost term, barrier term, and exact sum. -/
def gradientFromSlacksModule (b h : ℕ) : List Stmt :=
  [gradientFromSlacksBody (b+1) (b+44) (b+376)] ++
    (costTermModule (b+1) h ++ (barrierFromSlacksModule (b+44) h ++ addCarryModule (b+376) h))

/-- Fresh storage for the two terms and their exact sum. -/
def gradientFromSlacksSpace (L P E : ℕ) := costTermSpace L+barrierFromSlacksSpace L P E+L

/-- Explicit polynomial cost. -/
def gradientFromSlacksCost (L P E : ℕ) := costTermCost L+barrierFromSlacksCost L P E+38*L+300

/-- The source slacks and residual lie in `[2^-E,2^E]`, alpha in `[0,1]`,
and `K` bounds `20m` and `|20mc|`. Precision and width cover the smallest
length and the largest possible signed gradient entry. -/
def gradientFromSlacksContract (w h q K : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ m c r u d a one L P E heap,args=[m,c,r,u,d,a,one,L,P,E,heap] ∧ h∣P ∧
      q+4*E+42≤P ∧ P+K+4*E+30≤h*L ∧ 2*P+9<2^w ∧
      20*m<2^w ∧ 20*m≤2^K ∧ |20*(m:ℤ)*intVal mem c h L|≤(2:ℤ)^K ∧
      c+L≤heap ∧ r+L≤heap ∧ u+L≤heap ∧ d+L≤heap ∧ a+L≤heap ∧ one+L≤heap ∧
      Valid mem c h L ∧ Valid mem r h L ∧ Valid mem u h L ∧ Valid mem d h L ∧
      Valid mem a h L ∧ Valid mem one h L ∧ intVal mem one h L=(2:ℤ)^P ∧
      1/(2:ℝ)^E≤fixVal mem r h L P ∧ fixVal mem r h L P≤(2:ℝ)^E ∧
      1/(2:ℝ)^E≤fixVal mem u h L P ∧ fixVal mem u h L P≤(2:ℝ)^E ∧
      1/(2:ℝ)^E≤fixVal mem d h L P ∧ fixVal mem d h L P≤(2:ℝ)^E ∧
      0≤fixVal mem a h L P ∧ fixVal mem a h L P≤1)
    (fun _ _ _ => True)
    (fun args _ => gradientFromSlacksCost (args.getD 7 0) (args.getD 8 0) (args.getD 9 0))
    (fun args _ => gradientFromSlacksSpace (args.getD 7 0) (args.getD 8 0) (args.getD 9 0))
  {C with post := fun args mem v mem' =>
      let u := Real.rpow (fixVal mem (args.getD 3 0) h (args.getD 7 0) (args.getD 8 0))
        (-1-fixVal mem (args.getD 5 0) h (args.getD 7 0) (args.getD 8 0))
      let d := Real.rpow (fixVal mem (args.getD 4 0) h (args.getD 7 0) (args.getD 8 0))
        (-1-fixVal mem (args.getD 5 0) h (args.getD 7 0) (args.getD 8 0))
      let t := 20*(args.getD 0 0:ℝ)*(fixVal mem (args.getD 2 0) h (args.getD 7 0) (args.getD 8 0))⁻¹*
        (intVal mem (args.getD 1 0) h (args.getD 7 0):ℝ)
      C.post args mem v mem' ∧ Valid mem' (v-args.getD 7 0) h (args.getD 7 0) ∧
      |fixVal mem' (v-args.getD 7 0) h (args.getD 7 0) (args.getD 8 0)-
        (t+fixVal mem (args.getD 5 0) h (args.getD 7 0) (args.getD 8 0)*(u-d))|≤(1/(2:ℝ)^q)*(u+d)}

/-- Gradient computation is deterministic. -/
theorem gradientFromSlacksModule_noRand (b h : ℕ) : ∀ s∈gradientFromSlacksModule b h,s.NoRand := by
  intro s hs
  simp only [gradientFromSlacksModule,List.mem_append,List.mem_singleton] at hs
  rcases hs with rfl | hc | hb | ha
  · simp [gradientFromSlacksBody,Stmt.NoRand]
  · exact costTermModule_noRand _ _ _ hc
  · exact barrierFromSlacksModule_noRand _ _ _ hb
  · simp only [addCarryModule,List.mem_singleton] at ha
    subst s
    exact addCarryBody_noRand _ _

set_option maxRecDepth 16384 in
/-- The two rounded terms fit their exact sum, and their errors total at
most the requested length-scaled tolerance. -/
theorem gradientFromSlacks_meetsContract {w h b q K : ℕ} {p : Program}
    (hh : 0<h) (hw : 3*h+2≤w) (hp : p.HasAt b (gradientFromSlacksModule b h)) :
    MeetsContract w p b (gradientFromSlacksContract w h q K) := by
  have ht := hasAt_append_right hp
  change p.HasAt (b+1) _ at ht
  have hcost := hasAt_append_left ht
  have ht₂ := hasAt_append_right ht
  change p.HasAt (b+44) _ at ht₂
  have hb := hasAt_append_left ht₂
  have ha := hasAt_append_right ht₂
  change p.HasAt (b+376) _ at ha
  have hbc := barrierFromSlacks_meetsContract (q:=q) hh hw hb
  have hac := addCarry_meetsContract hh (show 2*h+2≤w by omega) ha
  have hw0 : 0<2^w := pow_pos (by decide) w
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨m,c,r,u,d,a,one,L,P,E,heap,rfl,hP,hprec,hwidth,hPw,hmw,hmB,hcB,hc,hr,hu,hd,ha,ho,hvc,hvr,hvu,hvd,hva,hvo,hone,hrl,hrh,hul,huh,hdl,hdh,ha0,ha1⟩,hz,hbound⟩
  have hcc := costTerm_meetsContract (E:=E) (K:=K) hh hw hcost
  change ZeroFrom mem heap at hz
  change heap+gradientFromSlacksSpace L P E<2^w at hbound
  have hcspace : L≤costTermSpace L := by unfold costTermSpace; omega
  have hbspace : L≤barrierFromSlacksSpace L P E := by unfold barrierFromSlacksSpace; omega
  have hmw' : m<2^w := hwords m (by simp)
  have hcw : c<2^w := hwords c (by simp)
  have hrw : r<2^w := hwords r (by simp)
  have huw : u<2^w := hwords u (by simp)
  have hdw : d<2^w := hwords d (by simp)
  have haw : a<2^w := hwords a (by simp)
  have how : one<2^w := hwords one (by simp)
  have hLw : L<2^w := hwords L (by simp)
  have hPword : P<2^w := hwords P (by simp)
  have hEw : E<2^w := hwords E (by simp)
  have hheapw : heap<2^w := hwords heap (by simp)
  have hcReal : |20*(m:ℝ)*(intVal mem c h L:ℝ)|≤(2:ℝ)^K := by exact_mod_cast hcB
  have hpowU := slack_power_dyadic_bounds hul huh ha0 ha1
  have hpowD := slack_power_dyadic_bounds hdl hdh ha0 ha1
  have hlength : 1/(2:ℝ)^(2*E)≤
      Real.rpow (fixVal mem u h L P) (-1-fixVal mem a h L P)+
      Real.rpow (fixVal mem d h L P) (-1-fixVal mem a h L P) := by
    have hd0 : 0≤Real.rpow (fixVal mem d h L P) (-1-fixVal mem a h L P) :=
      le_trans (by positivity) hpowD.1
    linarith only [hpowU.1,hd0]
  have hunit := unit_gradient_budget hlength (show q+2*E+3≤P by omega)
  apply runs_start_le
  unfold gradientFromSlacksBody
  refine runs_seq_call_le hcc (vs:=[m,c,r,L,P,heap]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨_,_,_,_,_,_,rfl,hP,by omega,hmw,hmB,hcB,hc,hr,hvc,hvr,hrl,hrh⟩,hz,
      by change heap+costTermSpace L<2^w; unfold gradientFromSlacksSpace at hbound; omega⟩
  · intro v₁ mem₁ pos₁ hp₁
    have htBound := costTerm_output_range hp₁ hcReal hrl
    rcases hp₁ with ⟨⟨hl₁,hh₁,fr₁,hz₁,_⟩,hv₁,herr₁⟩
    change heap≤v₁ at hl₁
    change v₁≤heap+costTermSpace L at hh₁
    change (∀ z<heap,mem₁ z=mem z) at fr₁
    change Valid mem₁ (v₁-L) h L at hv₁
    change |fixVal mem₁ (v₁-L) h L P-
      (20*(m:ℝ)*(fixVal mem r h L P)⁻¹*(intVal mem c h L:ℝ))|≤1/(2:ℝ)^P at herr₁
    have hufix := fixVal_frozen (h:=h) (P:=P) fr₁ hu
    have hdfix := fixVal_frozen (h:=h) (P:=P) fr₁ hd
    have hafix := fixVal_frozen (h:=h) (P:=P) fr₁ ha
    have honeval := value_frozen (h:=h) fr₁ ho
    have hv₁w : v₁<2^w := by unfold gradientFromSlacksSpace at hbound; omega
    refine runs_seq_call_le hbc (vs:=[u,d,a,one,L,P,E,v₁]) (by eval_expr) (by wram_words) ?_ ?_
    · refine ⟨⟨_,_,_,_,_,_,_,_,rfl,hP,hprec,by omega,hPw,by omega,by omega,by omega,by omega,
        valid_frozen fr₁ hu hvu,valid_frozen fr₁ hd hvd,valid_frozen fr₁ ha hva,
        valid_frozen fr₁ ho hvo,honeval.trans hone,?_,?_,?_,?_,?_,?_⟩,hz₁,
        by change v₁+barrierFromSlacksSpace L P E<2^w; unfold gradientFromSlacksSpace at hbound; omega⟩
      · rw [hufix]; exact hul
      · rw [hufix]; exact huh
      · rw [hdfix]; exact hdl
      · rw [hdfix]; exact hdh
      · rw [hafix]; exact ha0
      · rw [hafix]; exact ha1
    · intro v₂ mem₂ pos₂ hp₂
      rcases hp₂ with ⟨⟨hl₂,hh₂,fr₂,hz₂,_⟩,hv₂,herr₂,hbBound⟩
      change v₁≤v₂ at hl₂
      change v₂≤v₁+barrierFromSlacksSpace L P E at hh₂
      change (∀ z<v₁,mem₂ z=mem₁ z) at fr₂
      change Valid mem₂ (v₂-L) h L at hv₂
      change |fixVal mem₂ (v₂-L) h L P-(fixVal mem₁ a h L P*
        (Real.rpow (fixVal mem₁ u h L P) (-1-fixVal mem₁ a h L P)-
         Real.rpow (fixVal mem₁ d h L P) (-1-fixVal mem₁ a h L P)))|≤
        1/(2:ℝ)^P+(1/(2:ℝ)^q)/4*(Real.rpow (fixVal mem₁ u h L P) (-1-fixVal mem₁ a h L P)+
          Real.rpow (fixVal mem₁ d h L P) (-1-fixVal mem₁ a h L P)) at herr₂
      rw [hufix,hdfix,hafix] at herr₂
      change |fixVal mem₂ (v₂-L) h L P|≤(2:ℝ)^(2*E+3) at hbBound
      change |fixVal mem₁ (v₁-L) h L P|≤(2:ℝ)^(K+E+1) at htBound
      have hfirstfix := fixVal_frozen (h:=h) (P:=P) fr₂ (show v₁-L+L≤v₁ by omega)
      have hfirstvalid := valid_frozen fr₂ (show v₁-L+L≤v₁ by omega) hv₁
      have hsumB : |fixVal mem₂ (v₁-L) h L P+fixVal mem₂ (v₂-L) h L P|≤(2:ℝ)^(K+3*E+5) := by
        have ht := abs_add_le (fixVal mem₂ (v₁-L) h L P) (fixVal mem₂ (v₂-L) h L P)
        rw [hfirstfix] at ht
        have h₁ : (2:ℝ)^(K+E+1)≤(2:ℝ)^(K+3*E+4) := pow_le_pow_right₀ (by norm_num) (by omega)
        have h₂ : (2:ℝ)^(2*E+3)≤(2:ℝ)^(K+3*E+4) := pow_le_pow_right₀ (by norm_num) (by omega)
        have he : K+3*E+5=(K+3*E+4)+1 := by omega
        rw [hfirstfix,he,pow_succ]
        linarith only [ht,htBound,hbBound,h₁,h₂]
      have hsumFit : Fits h L (intVal mem₂ (v₁-L) h L+intVal mem₂ (v₂-L) h L+0) := by
        apply fits_of_scaled_bound (P:=P) (E:=K+3*E+5) (by omega)
        simpa only [add_zero,Int.cast_add,add_div,fixVal] using hsumB
      have hv₂w : v₂<2^w := by unfold gradientFromSlacksSpace at hbound; omega
      have hp₁w : v₁-L<2^w := by omega
      have hp₂w : v₂-L<2^w := by omega
      refine runs_seq_call_le hac (vs:=[v₁-L,v₂-L,L,0,v₂]) (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨⟨_,_,_,_,_,rfl,by omega,by omega,by decide,hfirstvalid,hv₂⟩,hz₂,
          by change v₂+L<2^w; unfold gradientFromSlacksSpace at hbound; omega⟩
      · intro v mem₃ pos₃ hp₃
        rcases hp₃ with ⟨he₃,hl₃,hh₃,fr₃,hz₃,hlist₃⟩
        change v=v₂+L at he₃
        change (∀ z<v₂,mem₃ z=mem₂ z) at fr₃
        change ListAt mem₃ v₂ (digits h L (unsignedVal mem₂ (v₁-L) h L+unsignedVal mem₂ (v₂-L) h L+0)) at hlist₃
        have hvalid₃ := (addCarry_value hlist₃).1
        have hval₃ := addCarry_value_of_fits hlist₃ hsumFit
        simp only [Nat.cast_zero,add_zero] at hval₃
        have hptr : v-L=v₂ := by omega
        have hsum : fixVal mem₃ (v-L) h L P=fixVal mem₁ (v₁-L) h L P+fixVal mem₂ (v₂-L) h L P := by
          rw [hptr]
          simp only [fixVal,hval₃,Int.cast_add,add_div]
          change fixVal mem₂ (v₁-L) h L P+fixVal mem₂ (v₂-L) h L P=_
          rw [hfirstfix]; rfl
        have ht := abs_add_le
          (fixVal mem₁ (v₁-L) h L P-(20*(m:ℝ)*(fixVal mem r h L P)⁻¹*(intVal mem c h L:ℝ)))
          (fixVal mem₂ (v₂-L) h L P-(fixVal mem a h L P*
            (Real.rpow (fixVal mem u h L P) (-1-fixVal mem a h L P)-Real.rpow (fixVal mem d h L P) (-1-fixVal mem a h L P))))
        have hεl : 0≤(1/(2:ℝ)^q)*(Real.rpow (fixVal mem u h L P) (-1-fixVal mem a h L P)+
            Real.rpow (fixVal mem d h L P) (-1-fixVal mem a h L P)) := by
          exact mul_nonneg (by positivity) (le_trans (by positivity) hlength)
        have hfinal : |fixVal mem₃ (v-L) h L P-
            ((20*(m:ℝ)*(fixVal mem r h L P)⁻¹*(intVal mem c h L:ℝ))+fixVal mem a h L P*
              (Real.rpow (fixVal mem u h L P) (-1-fixVal mem a h L P)-Real.rpow (fixVal mem d h L P) (-1-fixVal mem a h L P)))|≤
            (1/(2:ℝ)^q)*(Real.rpow (fixVal mem u h L P) (-1-fixVal mem a h L P)+Real.rpow (fixVal mem d h L P) (-1-fixVal mem a h L P)) := by
          rw [hsum]
          have he : fixVal mem₁ (v₁-L) h L P+fixVal mem₂ (v₂-L) h L P-
              ((20*(m:ℝ)*(fixVal mem r h L P)⁻¹*(intVal mem c h L:ℝ))+fixVal mem a h L P*
                (Real.rpow (fixVal mem u h L P) (-1-fixVal mem a h L P)-Real.rpow (fixVal mem d h L P) (-1-fixVal mem a h L P)))=
              (fixVal mem₁ (v₁-L) h L P-(20*(m:ℝ)*(fixVal mem r h L P)⁻¹*(intVal mem c h L:ℝ)))+
              (fixVal mem₂ (v₂-L) h L P-(fixVal mem a h L P*
                (Real.rpow (fixVal mem u h L P) (-1-fixVal mem a h L P)-Real.rpow (fixVal mem d h L P) (-1-fixVal mem a h L P)))) := by ring
          rw [he]
          linarith only [ht,herr₁,herr₂,hunit,hεl]
        have hvw : v<2^w := by unfold gradientFromSlacksSpace at hbound; omega
        refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
        · change (heap≤v ∧ v≤heap+gradientFromSlacksSpace L P E ∧ (∀ z<heap,mem₃ z=mem z) ∧ ZeroFrom mem₃ v ∧ True) ∧
            Valid mem₃ (v-L) h L ∧ _
          refine ⟨⟨by omega,?_,?_,hz₃,trivial⟩,hptr.symm ▸ hvalid₃,hfinal⟩
          · unfold gradientFromSlacksSpace; omega
          · intro z hz
            rw [fr₃ z (by omega),fr₂ z (by omega),fr₁ z hz]
        · simp only [gradientFromSlacksContract,costTermContract,barrierFromSlacksContract,addCarryContract,heapContract,
            List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_const,Expr.size_bin,
            argsSize_cons,argsSize_nil,gradientFromSlacksCost]
          omega

end MinCostFlow.Num.IPM
