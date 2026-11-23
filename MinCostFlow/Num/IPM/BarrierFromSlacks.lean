module

public import MinCostFlow.Num.IPM.SlackPower
public import MinCostFlow.Num.IPM.GradientFacts
public import MinCostFlow.Num.IPM.WeightedDifference
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# The barrier part of one gradient entry

Evaluate both powers in Definition 4.2 of Chen et al. (page 24), subtract
exactly, and multiply by alpha once. The error is the sum of the two power
errors and one output rounding. All bounds concern the original slacks.
-/

@[expose] public section
namespace MinCostFlow.Num.IPM
open WordRAM

/-- Arguments `[upperSlack,lowerSlack,alpha,one,L,P,E,heap]`. -/
def barrierFromSlacksBody (pow add : ℕ) : Stmt :=
  .call 8 pow [.reg 0,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7] ;;
  .call 9 pow [.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 8] ;;
  .call 10 add [.bin .sub (.reg 8) (.reg 4),.bin .sub (.reg 9) (.reg 4),.reg 2,.reg 4,.reg 5,.reg 9] ;;
  .ret (.reg 10)

/-- Both evaluations share one closed power module. -/
def barrierFromSlacksModule (b h : ℕ) : List Stmt :=
  [barrierFromSlacksBody (b+1) (b+315)] ++
    (slackPowerModule (b+1) h ++ weightedDifferenceModule (b+315) h)

/-- Two power workspaces and weighted-difference storage. -/
def barrierFromSlacksSpace (L P E : ℕ) := 2*slackPowerSpace L P E+(13*L+1)

/-- Explicit polynomial cost for the barrier part of a gradient. -/
def barrierFromSlacksCost (L P E : ℕ) := 2*slackPowerCost L P E+152*L^2+413*L+600

/-- An absolute barrier approximation and range bound at address `v-L`.
The source slacks lie in `[2^-E,2^E]`, and `0≤alpha≤1`. -/
def barrierFromSlacksContract (w h q : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ u d a one L P E heap,args=[u,d,a,one,L,P,E,heap] ∧ h∣P ∧
      q+4*E+42≤P ∧ P+4*E+20≤h*L ∧ 2*P+9<2^w ∧
      u+L≤heap ∧ d+L≤heap ∧ a+L≤heap ∧ one+L≤heap ∧
      Valid mem u h L ∧ Valid mem d h L ∧ Valid mem a h L ∧ Valid mem one h L ∧
      intVal mem one h L=(2:ℤ)^P ∧
      1/(2:ℝ)^E≤fixVal mem u h L P ∧ fixVal mem u h L P≤(2:ℝ)^E ∧
      1/(2:ℝ)^E≤fixVal mem d h L P ∧ fixVal mem d h L P≤(2:ℝ)^E ∧
      0≤fixVal mem a h L P ∧ fixVal mem a h L P≤1)
    (fun _ _ _ => True)
    (fun args _ => barrierFromSlacksCost (args.getD 4 0) (args.getD 5 0) (args.getD 6 0))
    (fun args _ => barrierFromSlacksSpace (args.getD 4 0) (args.getD 5 0) (args.getD 6 0))
  {C with post := fun args mem v mem' =>
      let u := Real.rpow (fixVal mem (args.getD 0 0) h (args.getD 4 0) (args.getD 5 0))
        (-1-fixVal mem (args.getD 2 0) h (args.getD 4 0) (args.getD 5 0))
      let d := Real.rpow (fixVal mem (args.getD 1 0) h (args.getD 4 0) (args.getD 5 0))
        (-1-fixVal mem (args.getD 2 0) h (args.getD 4 0) (args.getD 5 0))
      C.post args mem v mem' ∧ Valid mem' (v-args.getD 4 0) h (args.getD 4 0) ∧
      |fixVal mem' (v-args.getD 4 0) h (args.getD 4 0) (args.getD 5 0)-
        (fixVal mem (args.getD 2 0) h (args.getD 4 0) (args.getD 5 0)*(u-d))|≤
          1/(2:ℝ)^(args.getD 5 0)+(1/(2:ℝ)^q)/4*(u+d) ∧
      |fixVal mem' (v-args.getD 4 0) h (args.getD 4 0) (args.getD 5 0)|≤(2:ℝ)^(2*args.getD 6 0+3)}

/-- Barrier evaluation is deterministic. -/
theorem barrierFromSlacksModule_noRand (b h : ℕ) : ∀ s∈barrierFromSlacksModule b h,s.NoRand := by
  intro s hs
  simp only [barrierFromSlacksModule,List.mem_append,List.mem_singleton] at hs
  rcases hs with rfl | hp | ha
  · simp [barrierFromSlacksBody,Stmt.NoRand]
  · exact slackPowerModule_noRand _ _ _ hp
  · exact weightedDifferenceModule_noRand _ _ _ ha

set_option maxRecDepth 8192 in
/-- Two relative power errors at precision `q+2` and one product rounding
give the stated absolute barrier error and output range. -/
theorem barrierFromSlacks_meetsContract {w h b q : ℕ} {p : Program}
    (hh : 0<h) (hw : 3*h+2≤w) (hp : p.HasAt b (barrierFromSlacksModule b h)) :
    MeetsContract w p b (barrierFromSlacksContract w h q) := by
  have ht := hasAt_append_right hp
  change p.HasAt (b+1) _ at ht
  have hpow := hasAt_append_left ht
  have hwm := hasAt_append_right ht
  change p.HasAt (b+315) _ at hwm
  have hpc := slackPower_meetsContract (q:=q+2) hh hw hpow
  have hw0 : 0<2^w := pow_pos (by decide) w
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨u,d,a,one,L,P,E,heap,rfl,hP,hprec,hwidth,hPw,hu,hd,ha,ho,hvu,hvd,hva,hvo,hone,hul,huh,hdl,hdh,ha0,ha1⟩,hz,hbound⟩
  have hac := weightedDifference_meetsContract (D:=2*E+2) hh (show 2*h+2≤w by omega) hwm
  change ZeroFrom mem heap at hz
  change heap+barrierFromSlacksSpace L P E<2^w at hbound
  have hspace : L≤slackPowerSpace L P E := by unfold slackPowerSpace; omega
  have huword : u<2^w := hwords u (by simp)
  have hdword : d<2^w := hwords d (by simp)
  have haword : a<2^w := hwords a (by simp)
  have howord : one<2^w := hwords one (by simp)
  have hLword : L<2^w := hwords L (by simp)
  have hPword : P<2^w := hwords P (by simp)
  have hEword : E<2^w := hwords E (by simp)
  have hheapword : heap<2^w := hwords heap (by simp)
  have hε0 : (0:ℝ)<1/(2:ℝ)^q := by positivity
  have hε1 : 1/(2:ℝ)^q≤1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hhalf : 1/(2:ℝ)^(q+2)=(1/(2:ℝ)^q)/4 := by rw [pow_add]; norm_num; ring
  have hδ0 : (0:ℝ)≤1/(2:ℝ)^(q+2) := by positivity
  have hδ1 : 1/(2:ℝ)^(q+2)≤1 := by rw [hhalf]; linarith only [hε1]
  have hup : 0<fixVal mem u h L P := lt_of_lt_of_le (by positivity) hul
  have hdp : 0<fixVal mem d h L P := lt_of_lt_of_le (by positivity) hdl
  have hpowU : 0<Real.rpow (fixVal mem u h L P) (-1-fixVal mem a h L P) := Real.rpow_pos_of_pos hup _
  have hpowD : 0<Real.rpow (fixVal mem d h L P) (-1-fixVal mem a h L P) := Real.rpow_pos_of_pos hdp _
  have hpowUB := (slack_power_dyadic_bounds hul huh ha0 ha1).2
  have hpowDB := (slack_power_dyadic_bounds hdl hdh ha0 ha1).2
  apply runs_start_le
  unfold barrierFromSlacksBody
  refine runs_seq_call_le hpc (vs:=[u,a,one,L,P,E,heap]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨_,_,_,_,_,_,_,rfl,hP,by omega,hwidth,hPw,hu,ha,ho,hvu,hva,hvo,hone,hul,huh,ha0,ha1⟩,
      hz,by change heap+slackPowerSpace L P E<2^w; unfold barrierFromSlacksSpace at hbound; omega⟩
  · intro v₁ mem₁ pos₁ hp₁
    rcases hp₁ with ⟨⟨hl₁,hh₁,fr₁,hz₁,_⟩,hv₁,herr₁⟩
    change heap≤v₁ at hl₁
    change v₁≤heap+slackPowerSpace L P E at hh₁
    change (∀ z<heap,mem₁ z=mem z) at fr₁
    change Valid mem₁ (v₁-L) h L at hv₁
    change |fixVal mem₁ (v₁-L) h L P-Real.rpow (fixVal mem u h L P) (-1-fixVal mem a h L P)|≤
      (1/(2:ℝ)^(q+2))*Real.rpow (fixVal mem u h L P) (-1-fixVal mem a h L P) at herr₁
    have hd₁ := fixVal_frozen (h:=h) (P:=P) fr₁ hd
    have ha₁ := fixVal_frozen (h:=h) (P:=P) fr₁ ha
    have ho₁ := value_frozen (h:=h) fr₁ ho
    have hv₁word : v₁<2^w := by unfold barrierFromSlacksSpace at hbound; omega
    refine runs_seq_call_le hpc (vs:=[d,a,one,L,P,E,v₁]) (by eval_expr) (by wram_words) ?_ ?_
    · refine ⟨⟨_,_,_,_,_,_,_,rfl,hP,by omega,hwidth,hPw,by omega,by omega,by omega,
        valid_frozen fr₁ hd hvd,valid_frozen fr₁ ha hva,valid_frozen fr₁ ho hvo,ho₁.trans hone,?_,?_,?_,?_⟩,
        hz₁,by change v₁+slackPowerSpace L P E<2^w; unfold barrierFromSlacksSpace at hbound; omega⟩
      · rw [hd₁]; exact hdl
      · rw [hd₁]; exact hdh
      · rw [ha₁]; exact ha0
      · rw [ha₁]; exact ha1
    · intro v₂ mem₂ pos₂ hp₂
      rcases hp₂ with ⟨⟨hl₂,hh₂,fr₂,hz₂,_⟩,hv₂,herr₂⟩
      change v₁≤v₂ at hl₂
      change v₂≤v₁+slackPowerSpace L P E at hh₂
      change (∀ z<v₁,mem₂ z=mem₁ z) at fr₂
      change Valid mem₂ (v₂-L) h L at hv₂
      change |fixVal mem₂ (v₂-L) h L P-Real.rpow (fixVal mem₁ d h L P) (-1-fixVal mem₁ a h L P)|≤
        (1/(2:ℝ)^(q+2))*Real.rpow (fixVal mem₁ d h L P) (-1-fixVal mem₁ a h L P) at herr₂
      rw [hd₁,ha₁] at herr₂
      have hfirstvalid := valid_frozen fr₂ (show v₁-L+L≤v₁ by omega) hv₁
      have hfirstfix := fixVal_frozen (h:=h) (P:=P) fr₂ (show v₁-L+L≤v₁ by omega)
      have hdiffB := approximate_power_difference_bound hpowU.le hpowD.le hpowUB hpowDB hδ1 herr₁ herr₂
      rw [← hfirstfix] at hdiffB
      have hdiffB' : |fixVal mem₂ (v₁-L) h L P-fixVal mem₂ (v₂-L) h L P|≤(2:ℝ)^(2*E+2) := by
        convert hdiffB using 1
        rw [pow_add]; norm_num; ring
      have hafix₂ : fixVal mem₂ a h L P=fixVal mem a h L P :=
        (fixVal_frozen fr₂ (by omega)).trans ha₁
      have havalid₂ := valid_frozen fr₂ (show a+L≤v₁ by omega) (valid_frozen fr₁ ha hva)
      have hv₂word : v₂<2^w := by unfold barrierFromSlacksSpace at hbound; omega
      have hp₁word : v₁-L<2^w := by omega
      have hp₂word : v₂-L<2^w := by omega
      refine runs_seq_call_le hac (vs:=[v₁-L,v₂-L,a,L,P,v₂]) (by eval_expr) (by wram_words) ?_ ?_
      · refine ⟨⟨_,_,_,_,_,_,rfl,hP,by omega,by omega,by omega,by omega,hfirstvalid,hv₂,havalid₂,?_,?_,hdiffB'⟩,
          hz₂,by change v₂+(13*L+1)<2^w; unfold barrierFromSlacksSpace at hbound; omega⟩
        · rw [hafix₂]; exact ha0
        · rw [hafix₂]; exact ha1
      · intro v mem₃ pos₃ hp₃
        rcases hp₃ with ⟨⟨hl₃,hh₃,fr₃,hz₃,_⟩,hvalid₃,herr₃,houtB⟩
        change v₂≤v at hl₃
        change v≤v₂+(13*L+1) at hh₃
        change (∀ z<v₂,mem₃ z=mem₂ z) at fr₃
        change Valid mem₃ (v-L) h L at hvalid₃
        change |fixVal mem₃ (v-L) h L P-fixVal mem₂ a h L P*
          (fixVal mem₂ (v₁-L) h L P-fixVal mem₂ (v₂-L) h L P)|≤1/(2:ℝ)^P at herr₃
        change |fixVal mem₃ (v-L) h L P|≤(2:ℝ)^((2*E+2)+1) at houtB
        rw [hafix₂,hfirstfix] at herr₃
        have herr := barrier_error ha0 ha1 hδ0 hpowU.le hpowD.le herr₁ herr₂ herr₃
        rw [hhalf] at herr
        have he : fixVal mem a h L P*Real.rpow (fixVal mem u h L P) (-1-fixVal mem a h L P)-
            fixVal mem a h L P*Real.rpow (fixVal mem d h L P) (-1-fixVal mem a h L P)=
            fixVal mem a h L P*(Real.rpow (fixVal mem u h L P) (-1-fixVal mem a h L P)-
              Real.rpow (fixVal mem d h L P) (-1-fixVal mem a h L P)) := by ring
        rw [he] at herr
        have hvword : v<2^w := by unfold barrierFromSlacksSpace at hbound; omega
        refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
        · change (heap≤v ∧ v≤heap+barrierFromSlacksSpace L P E ∧ (∀ z<heap,mem₃ z=mem z) ∧
            ZeroFrom mem₃ v ∧ True) ∧ Valid mem₃ (v-L) h L ∧
            |fixVal mem₃ (v-L) h L P-(fixVal mem a h L P*
              (Real.rpow (fixVal mem u h L P) (-1-fixVal mem a h L P)-
               Real.rpow (fixVal mem d h L P) (-1-fixVal mem a h L P)))|≤
              1/(2:ℝ)^P+(1/(2:ℝ)^q)/4*(Real.rpow (fixVal mem u h L P) (-1-fixVal mem a h L P)+
                Real.rpow (fixVal mem d h L P) (-1-fixVal mem a h L P)) ∧
            |fixVal mem₃ (v-L) h L P|≤(2:ℝ)^(2*E+3)
          refine ⟨⟨by omega,?_,?_,hz₃,trivial⟩,hvalid₃,herr,?_⟩
          · unfold barrierFromSlacksSpace; omega
          · intro z hz
            rw [fr₃ z (by omega),fr₂ z (by omega),fr₁ z hz]
          · simpa only [Nat.add_assoc] using houtB
        · simp only [barrierFromSlacksContract,slackPowerContract,weightedDifferenceContract,heapContract,
            List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_const,Expr.size_bin,
            argsSize_cons,argsSize_nil,barrierFromSlacksCost]
          omega

end MinCostFlow.Num.IPM
