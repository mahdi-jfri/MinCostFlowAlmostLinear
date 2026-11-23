module

public import MinCostFlow.Num.NegativePower
public import MinCostFlow.Num.AddCarry
public import MinCostFlow.Num.IPM.FixedPointFacts
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Negative powers of IPM slacks

Definition 4.2 of Chen et al. (page 24) raises each slack to `-1-a`.
We first add the fixed-point blocks for one and `a` exactly. The verified
negative-power procedure then evaluates the slack at this stored exponent.
Only that evaluation introduces an error.
-/

@[expose] public section
namespace MinCostFlow.Num.IPM
open WordRAM

/-- Arguments `[slack,alpha,one,L,P,E,heap]`. -/
def slackPowerBody (add pow : ℕ) : Stmt :=
  .call 7 add [.reg 1,.reg 2,.reg 3,.const 0,.reg 6] ;;
  .call 8 pow [.reg 0,.bin .sub (.reg 7) (.reg 3),.reg 2,.reg 3,.reg 4,.reg 5,.reg 7] ;;
  .ret (.reg 8)

/-- A one-limb-adder entry followed by the negative-power module. -/
def slackPowerModule (b h : ℕ) : List Stmt :=
  [slackPowerBody (b+1) (b+2)] ++
    (addCarryModule (b+1) h ++ negativePowerModule (b+2) h)

/-- Fresh storage includes the exact exponent block and power workspace. -/
def slackPowerSpace (L P E : ℕ) := L+negativePowerSpace L P E

/-- Explicit cost of exact exponent formation and negative-power evaluation. -/
def slackPowerCost (L P E : ℕ) := negativePowerCost L P E+38*L+100

/-- Relative error for the power in Definition 4.2 (page 24).
The returned block starts at `v-L`. The alpha input may be any fixed-point
number in `[0,1]`, so in particular it may be the dyadic alpha procedure's output. -/
def slackPowerContract (w h q : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ s a one L P E heap,args=[s,a,one,L,P,E,heap] ∧ h∣P ∧
      q+4*E+40≤P ∧ P+4*E+20≤h*L ∧ 2*P+9<2^w ∧
      s+L≤heap ∧ a+L≤heap ∧ one+L≤heap ∧
      Valid mem s h L ∧ Valid mem a h L ∧ Valid mem one h L ∧
      intVal mem one h L=(2:ℤ)^P ∧
      1/(2:ℝ)^E≤fixVal mem s h L P ∧ fixVal mem s h L P≤(2:ℝ)^E ∧
      0≤fixVal mem a h L P ∧ fixVal mem a h L P≤1)
    (fun _ _ _ => True)
    (fun args _ => slackPowerCost (args.getD 3 0) (args.getD 4 0) (args.getD 5 0))
    (fun args _ => slackPowerSpace (args.getD 3 0) (args.getD 4 0) (args.getD 5 0))
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧
      Valid mem' (v-args.getD 3 0) h (args.getD 3 0) ∧
      |fixVal mem' (v-args.getD 3 0) h (args.getD 3 0) (args.getD 4 0) -
        (Real.rpow (fixVal mem (args.getD 0 0) h (args.getD 3 0) (args.getD 4 0))
          (-1 - fixVal mem (args.getD 1 0) h (args.getD 3 0) (args.getD 4 0)))| ≤
        (1/(2:ℝ)^q)*(Real.rpow (fixVal mem (args.getD 0 0) h (args.getD 3 0) (args.getD 4 0))
          (-1 - fixVal mem (args.getD 1 0) h (args.getD 3 0) (args.getD 4 0))) }


/-- The slack-power module is deterministic. -/
theorem slackPowerModule_noRand (b h : ℕ) : ∀ s∈slackPowerModule b h,s.NoRand := by
  intro s hs
  simp only [slackPowerModule,List.mem_append,List.mem_singleton] at hs
  rcases hs with rfl | ha | hp
  · simp [slackPowerBody,Stmt.NoRand]
  · simp only [addCarryModule,List.mem_singleton] at ha
    subst s
    exact addCarryBody_noRand _ _
  · exact negativePowerModule_noRand _ _ _ hp

set_option maxRecDepth 4096 in
/-- Forming `1+a` is exact, and the power procedure's error is therefore
relative to the original slack and original alpha input. -/
theorem slackPower_meetsContract {w h b q : ℕ} {p : Program}
    (hh : 0<h) (hw : 3*h+2≤w) (hp : p.HasAt b (slackPowerModule b h)) :
    MeetsContract w p b (slackPowerContract w h q) := by
  have ht := hasAt_append_right hp
  change p.HasAt (b+1) _ at ht
  have ha := hasAt_append_left ht
  have hpow := hasAt_append_right ht
  change p.HasAt (b+2) _ at hpow
  have hac := addCarry_meetsContract hh (show 2*h+2≤w by omega) ha
  have hpc := negativePower_meetsContract (q:=q) hh hw hpow
  have hw0 : 0<2^w := pow_pos (by decide) w
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨s,a,one,L,P,E,heap,rfl,hP,hprec,hwidth,hPw,hs,ha,ho,hvs,hva,hvo,hone,hsl,hsh,ha0,ha1⟩,hz,hbound⟩
  change ZeroFrom mem heap at hz
  change heap+slackPowerSpace L P E<2^w at hbound
  have hpowSpace : L≤negativePowerSpace L P E := by
    unfold negativePowerSpace logarithmSpace; omega
  have hsword : s<2^w := hwords s (by simp)
  have haword : a<2^w := hwords a (by simp)
  have howord : one<2^w := hwords one (by simp)
  have hLword : L<2^w := hwords L (by simp)
  have hPword : P<2^w := hwords P (by simp)
  have hEword : E<2^w := hwords E (by simp)
  have hheapword : heap<2^w := hwords heap (by simp)
  have honefix : fixVal mem one h L P=1 := by
    simp only [fixVal,hone,Int.cast_pow,Int.cast_ofNat]
    exact div_self (by positivity)
  have hfit : Fits h L (intVal mem a h L+intVal mem one h L+0) := by
    apply fits_of_scaled_bound (P:=P) (E:=1) (by omega)
    simp only [add_zero,Int.cast_add,add_div,pow_one]
    change |fixVal mem a h L P+fixVal mem one h L P|≤2
    rw [honefix]
    rw [abs_of_nonneg (by linarith only [ha0])]
    linarith only [ha1]
  apply runs_start_le
  unfold slackPowerBody
  refine runs_seq_call_le hac (vs:=[a,one,L,0,heap]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨_,_,_,_,_,rfl,ha,ho,by decide,hva,hvo⟩,hz,
      by change heap+L<2^w; unfold slackPowerSpace at hbound; omega⟩
  · intro v₁ mem₁ pos₁ hp₁
    rcases hp₁ with ⟨he₁,hl₁,hh₁,fr₁,hz₁,hlist₁⟩
    change v₁=heap+L at he₁
    change (∀ z<heap,mem₁ z=mem z) at fr₁
    change ListAt mem₁ heap (digits h L (unsignedVal mem a h L+unsignedVal mem one h L+0)) at hlist₁
    have hvalid₁ := (addCarry_value hlist₁).1
    have hval₁ := addCarry_value_of_fits hlist₁ hfit
    simp only [Nat.cast_zero,add_zero] at hval₁
    have hfix₁ : fixVal mem₁ heap h L P=1+fixVal mem a h L P := by
      simp only [fixVal,hval₁,add_zero,Int.cast_add,add_div]
      change fixVal mem a h L P+fixVal mem one h L P=1+fixVal mem a h L P
      rw [honefix,add_comm]
    have hsfix := fixVal_frozen (h:=h) (P:=P) fr₁ hs
    have honeval := value_frozen (h:=h) fr₁ ho
    have hv₁word : v₁<2^w := by unfold slackPowerSpace at hbound; omega
    have hptrword : v₁-L<2^w := by omega
    refine runs_seq_call_le hpc (vs:=[s,v₁-L,one,L,P,E,v₁]) (by eval_expr) (by wram_words) ?_ ?_
    · refine ⟨⟨_,_,_,_,_,_,_,rfl,hP,hprec,hwidth,hPw,by omega,by omega,by omega,
        valid_frozen fr₁ hs hvs,?_,valid_frozen fr₁ ho hvo,honeval.trans hone,?_,?_,?_,?_⟩,
        hz₁,?_⟩
      · convert hvalid₁ using 1 <;> omega
      · rw [hsfix]; exact hsl
      · rw [hsfix]; exact hsh
      · have he : v₁-L=heap := by omega
        rw [he,hfix₁]; linarith only [ha0]
      · have he : v₁-L=heap := by omega
        rw [he,hfix₁]; linarith only [ha1]
      · change v₁+negativePowerSpace L P E<2^w
        unfold slackPowerSpace at hbound
        omega
    · intro v mem₂ pos₂ hp₂
      rcases hp₂ with ⟨⟨hl₂,hh₂,fr₂,hz₂,_⟩,hvalid₂,herr₂⟩
      change v₁≤v at hl₂
      change v≤v₁+negativePowerSpace L P E at hh₂
      change (∀ z<v₁,mem₂ z=mem₁ z) at fr₂
      change Valid mem₂ (v-L) h L at hvalid₂
      change |fixVal mem₂ (v-L) h L P-Real.rpow (fixVal mem₁ s h L P)
        (-fixVal mem₁ (v₁-L) h L P)|≤
        (1/(2:ℝ)^q)*Real.rpow (fixVal mem₁ s h L P) (-fixVal mem₁ (v₁-L) h L P) at herr₂
      have he : v₁-L=heap := by omega
      rw [he,hfix₁,hsfix] at herr₂
      have hexp : -(1+fixVal mem a h L P)=-1-fixVal mem a h L P := by ring
      rw [hexp] at herr₂
      have hvword : v<2^w := by unfold slackPowerSpace at hbound; omega
      refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
      · change (heap≤v ∧ v≤heap+slackPowerSpace L P E ∧ (∀ z<heap,mem₂ z=mem z) ∧
          ZeroFrom mem₂ v ∧ True) ∧ Valid mem₂ (v-L) h L ∧
          |fixVal mem₂ (v-L) h L P-Real.rpow (fixVal mem s h L P) (-1 - fixVal mem a h L P)|≤
            (1/(2:ℝ)^q)*Real.rpow (fixVal mem s h L P) (-1 - fixVal mem a h L P)
        refine ⟨⟨by omega,?_,?_,hz₂,trivial⟩,hvalid₂,herr₂⟩
        · unfold slackPowerSpace; omega
        · intro z hz
          rw [fr₂ z (by omega),fr₁ z hz]
      · simp only [slackPowerContract,negativePowerContract,addCarryContract,heapContract,
          List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_const,Expr.size_bin,
          argsSize_cons,argsSize_nil,slackPowerCost]
        omega

end MinCostFlow.Num.IPM
