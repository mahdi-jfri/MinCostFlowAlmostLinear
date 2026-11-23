module

public import MinCostFlow.IPM.Machine.SolverResources
import MinCostFlow.IPM.Machine.TargetSearchCost
import Mathlib.Tactic

/-!
# Nearly linear numerical work and the two data-structure charges

The augmentation gives at most three times as many edges. Its
polynomial penalty increases the bit length by only a constant
factor. The complete operation count separates the local numerical
work, all min-ratio operations over the search, and the forest pass.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM
set_option maxHeartbeats 150000

private theorem solverPenalty_two (m : ℕ) (hm : 0 < m) : 2≤solverPenalty m := by
  have hU : 2≤solverCapacityBound m := le_max_left _ _
  have hpow : 1≤(solverCapacityBound m)^2 := Nat.one_le_pow _ _ (by omega)
  apply le_trans _ (Nat.le_mul_of_pos_right _ (by omega : 0 < (solverCapacityBound m)^2))
  omega

private theorem solverLogBound (m M : ℕ) (hm : 0 < m) (hM : m≤M) (hMax : M≤3*m) :
    5*Real.log ((M*solverPenalty m:ℕ):ℝ)≤430*Real.log ((m:ℝ)+2) := by
  have hmR : 0 < (m:ℝ) := Nat.cast_pos.mpr hm
  have hm1 : (1:ℝ)≤m := by exact_mod_cast hm
  have hprod : M*solverPenalty m≤48*m^82 := by
    calc
      _ ≤ (3*m)*(16*m^81) := Nat.mul_le_mul hMax (solverPenalty_le m hm)
      _ = _ := by ring
  have hreal : ((M*solverPenalty m:ℕ):ℝ)≤48*(m:ℝ)^82 := by exact_mod_cast hprod
  have hpos : (0:ℝ)<((M*solverPenalty m:ℕ):ℝ) := by
    exact_mod_cast Nat.mul_pos (hm.trans_le hM) (by have := solverPenalty_two m hm; omega)
  have hl := Real.log_le_log hpos hreal
  rw [Real.log_mul (by norm_num : (48:ℝ)≠0) (pow_pos hmR _).ne',Real.log_pow] at hl
  have hmL := Real.log_le_log hmR (show (m:ℝ)≤m+2 by linarith)
  have h48 : (48:ℝ)≤((m:ℝ)+2)^4 := by
    apply le_trans (show (48:ℝ)≤3^4 by norm_num)
    exact pow_le_pow_left₀ (by norm_num) (by linarith) 4
  have hlog48 := Real.log_le_log (by norm_num : (0:ℝ)<48) h48
  rw [Real.log_pow] at hlog48
  norm_num only [Nat.cast_ofNat] at hl hlog48
  linarith only [hl,hmL,hlog48]

/-- Bound the binary length driving the solver cost at an augmented size. -/
theorem solverInputBits_log_bound (m M : ℕ) (hm : 0 < m) (hM : m≤M) (hMax : M≤3*m) :
    2≤M*solverPenalty m ∧
      ((M.size+(solverPenalty m).size:ℕ):ℝ)≤430*Real.log ((m:ℝ)+2) := by
  have hSize := (solverPenalty_two m hm).trans
    (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right (solverPenalty m) (hm.trans_le hM))
  exact ⟨hSize,(Num.IPM.alpha_bit_length_bounds hSize).2.trans (solverLogBound m M hm hM hMax)⟩

private theorem solverOtherCost (n m M L B R f : ℕ) (hm : 0 < m) (hM : M≤3*m) :
    300*m+400*n+M*(200*L+600)+20028*B+23000+
    (30*(n+1)+M*(600*L+1900)+36*L+1800)+(14*(B+R)+550)+
    (roundMachineCost f L (n+1) M+17*(M*L)+m*(100*L+240)+100)+1200 ≤
      500*n+100000*m*(L+B+R+1)+f*(n+2+30*m) := by
  have hML := Nat.mul_le_mul_right L hM
  have hMF := Nat.mul_le_mul_right f hM
  have hmL : L≤m*L := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right L hm
  have hmB : B≤m*B := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right B hm
  have hmR : R≤m*R := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right R hm
  unfold roundMachineCost
  ring_nf at hML hMF ⊢
  rw [Nat.mul_comm m L] at hmL
  omega

private theorem bisectionChargeMono (M m rate k : ℕ) (x y : ℝ)
    (hx : 0≤x) (hxy : x≤y) (hM : M≤3*m) :
    (2+2*x)*(3276800000000001*x^3*((2:ℝ)^k)^2*
      ((M:ℝ)*(100000000*(30000000*x^2)^3)+((30*M+1:ℕ):ℝ)*rate)+3000000000*x^2+419) ≤
    (2+2*y)*(3276800000000001*y^3*((2:ℝ)^k)^2*
      ((3*(m:ℝ))*(100000000*(30000000*y^2)^3)+(90*(m:ℝ)+1)*rate)+3000000000*y^2+419) := by
  have hM' : (M:ℝ)≤3*(m:ℝ) := by exact_mod_cast hM
  have hrate : ((30*M+1:ℕ):ℝ)≤90*(m:ℝ)+1 := by simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]; linarith
  have hy : 0≤y := hx.trans hxy
  gcongr

/-- An explicit upper envelope for the total advertised solver time.
Here `b = 430 log(m+2)` and the approximation quality is `2^-k`.
The local numerical work is linear in (n+m) times powers of (b)
and the inverse quality squared. The remaining terms count the
charged min-ratio calls and the single forest pass. -/
theorem solverTime_log_bound (r : SolverResources) (n m : ℕ) (hm : 0 < m) :
    let b := 430*Real.log ((m:ℝ)+2)
    let R := (((Finset.Icc m (3*m)).sup r.cycleRate : ℕ) : ℝ)
    (solverTime r n m:ℝ) ≤
      500*n+100000*m*(30000000*b^2+3*b+3)+(r.forestRate (n+1):ℝ)*(n+2+30*m)+
      (2+2*b)*(3276800000000001*b^3*((2:ℝ)^r.qualityExponent)^2*
        ((3*(m:ℝ))*(100000000*(30000000*b^2)^3)+(90*(m:ℝ)+1)*R)+3000000000*b^2+419)+30 := by
  dsimp only
  let y := 430*Real.log ((m:ℝ)+2)
  let R := (Finset.Icc m (3*m)).sup r.cycleRate
  have hi : m∈Finset.Icc m (3*m) := Finset.mem_Icc.mpr ⟨le_rfl,by omega⟩
  obtain ⟨M,hMem,hMax⟩ := Finset.exists_mem_eq_sup (Finset.Icc m (3*m)) ⟨m,hi⟩ (solverTimeAt r n m)
  obtain ⟨hM,hUpper⟩ := Finset.mem_Icc.mp hMem
  let V := solverPenalty m
  let bits := M.size+V.size
  let L := ipmLimbs M V
  let rounds := targetSearchRounds (M*V^2)
  let F := ipmMinRatioFormat M V (w:=ipmParameterWordBits M V) le_rfl
  let x := 5*Real.log ((M*V:ℕ):ℝ)
  let ft := targetSearchCost F M V r.qualityExponent F.rangeExponent r.cycleRate
  let f := r.forestRate (n+1)
  have hMpos : 0 < M := hm.trans_le hM
  have hV : 2≤V := solverPenalty_two m hm
  have hSize : 2≤M*V := hV.trans (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right V hMpos)
  have hBits : (bits:ℝ)≤x := (Num.IPM.alpha_bit_length_bounds hSize).2
  have hx : 0≤x := (Nat.cast_nonneg bits).trans hBits
  have hxy : x≤y := solverLogBound m M hm hM hUpper
  have hy : 0≤y := hx.trans hxy
  have hBy : (bits:ℝ)≤y := hBits.trans hxy
  have hr : (rounds:ℝ)≤2+2*y := by
    have h' : (rounds:ℝ)≤2+2*(bits:ℝ) := by
      have h := targetSearch_rounds_bit_bound M V
      change rounds+1≤2+2*bits at h
      exact_mod_cast (show rounds≤2+2*bits by omega)
    linarith only [h',hBy]
  have hLy : (L:ℝ)≤30000000*y^2 := by
    have hl : (L:ℝ)≤30000000*(bits:ℝ)^2 := by
      exact_mod_cast (target_format_bit_bound M V hMpos).1
    exact hl.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hBy 2) (by positivity))
  have hf := targetSearch_cost_log_bound M V r.qualityExponent le_rfl hMpos hSize r.cycleRate ft le_rfl
  have hSearch := hf.trans (bisectionChargeMono M m (r.cycleRate M) r.qualityExponent x y hx hxy hUpper)
  have hRate : (r.cycleRate M:ℝ)≤(R:ℝ) := by exact_mod_cast Finset.le_sup (f:=r.cycleRate) hMem
  have hSearch' : (ft:ℝ) ≤
      (2+2*y)*(3276800000000001*y^3*((2:ℝ)^r.qualityExponent)^2*
        ((3*(m:ℝ))*(100000000*(30000000*y^2)^3)+(90*(m:ℝ)+1)*R)+3000000000*y^2+419) := by
    apply hSearch.trans
    gcongr
  have hOther : solverTimeAt r n m M≤
      500*n+100000*m*(L+bits+rounds+1)+f*(n+2+30*m)+ft := by
    let rest := 300*m+400*n+M*(200*L+600)+20028*bits+23000+
      (30*(n+1)+M*(600*L+1900)+36*L+1800)+(14*(bits+rounds)+550)+
      (roundMachineCost f L (n+1) M+17*(M*L)+m*(100*L+240)+100)+1200
    have hEq : solverTimeAt r n m M=rest+ft := by
      change 300*m+400*n+M*(200*L+600)+20028*bits+23000+
        (30*(n+1)+M*(600*L+1900)+36*L+1800)+(14*(bits+rounds)+550)+ft+
        (roundMachineCost f L (n+1) M+17*(M*L)+m*(100*L+240)+100)+1200=rest+ft
      dsimp only [rest]
      ac_rfl
    rw [hEq]
    exact Nat.add_le_add_right (solverOtherCost n m M L bits rounds f hm hUpper) ft
  have hOther' : (solverTimeAt r n m M:ℝ)≤
      500*n+100000*m*((L:ℝ)+bits+rounds+1)+(f:ℝ)*(n+2+30*m)+ft := by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using (Nat.cast_le (α:=ℝ)).mpr hOther
  have hmR : (0:ℝ)≤m := Nat.cast_nonneg m
  have hn : (0:ℝ)≤n := Nat.cast_nonneg n
  have hpoly : ((L:ℝ)+bits+rounds+1)≤30000000*y^2+3*y+3 := by linarith only [hLy,hBy,hr]
  have hLocal := mul_le_mul_of_nonneg_left hpoly (show (0:ℝ)≤100000*m by positivity)
  have hTime : solverTime r n m≤solverTimeAt r n m M+30 := by
    unfold solverTime
    rw [hMax]
    exact max_le (Nat.le_add_left _ _) (Nat.le_add_right _ _)
  have hTime' : (solverTime r n m:ℝ)≤(solverTimeAt r n m M:ℝ)+30 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using (Nat.cast_le (α:=ℝ)).mpr hTime
  refine hTime'.trans (add_le_add (hOther'.trans ?_) (show (30:ℝ)≤30 from le_rfl))
  exact add_le_add (add_le_add (add_le_add (show (500:ℝ)*n≤500*n from le_rfl) hLocal) le_rfl) hSearch'


/-- The time bound at a maximizing augmented edge count includes its
runtime quality charge and the iteration factor `4^(k M)`. -/
theorem solverRuntimeTime_log_bound (r : SolverRuntimeResources) (n m : ℕ) (hm : 0 < m) :
    ∃ M ∈ Finset.Icc m (3*m),
      let b := 430*Real.log ((m:ℝ)+2)
      let R := (((Finset.Icc m (3*m)).sup r.template.cycleRate : ℕ) : ℝ)
      (solverRuntimeTime r n m:ℝ) ≤
        500*n+100000*m*(30000000*b^2+3*b+3)+(r.template.forestRate (n+1):ℝ)*(n+2+30*m)+
        (2+2*b)*(3276800000000001*b^3*(4:ℝ)^r.qualityExponent M*
          ((3*(m:ℝ))*(100000000*(30000000*b^2)^3)+(90*(m:ℝ)+1)*R)+3000000000*b^2+419)+30+
        r.qualityCost M := by
  have hMem : m ∈ Finset.Icc m (3*m) := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  obtain ⟨M,hM,hMax⟩ := Finset.exists_mem_eq_sup (Finset.Icc m (3*m)) ⟨m,hMem⟩
    (fun M => solverTimeAt (r.forSize M) n m M + r.qualityCost M)
  refine ⟨M,hM,?_⟩
  have hT : solverRuntimeTime r n m ≤ solverTime (r.forSize M) n m + r.qualityCost M := by
    unfold solverRuntimeTime
    rw [hMax]
    apply max_le
    · exact (le_max_left _ _).trans (Nat.le_add_right _ _)
    · exact Nat.add_le_add_right
        ((Finset.le_sup (f := solverTimeAt (r.forSize M) n m) hM).trans (le_max_right _ _)) _
  have hBound := solverTime_log_bound (r.forSize M) n m hm
  dsimp only [SolverRuntimeResources.forSize] at hBound
  have hPow : ((2:ℝ)^r.qualityExponent M)^2 = (4:ℝ)^r.qualityExponent M := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  rw [hPow] at hBound
  have hCast := (Nat.cast_le (α := ℝ)).mpr hT
  rw [Nat.cast_add] at hCast
  exact hCast.trans (add_le_add hBound le_rfl)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 700000 in
/-- Cost at the augmented sizes attaining the widened solver's envelope.
The numerical dimensions are bounded by the original quadratic bit bound
plus a linear term in the runtime quality exponent. -/
theorem solverQualityRuntimeTime_width_bound (r : SolverRuntimeResources)
    (n m : ℕ) (hm : 0 < m) :
    ∃ M ∈ Finset.Icc m (3*m),
      let V := solverPenalty m
      let B := M.size+V.size
      let k := r.qualityExponent M
      let W := 30000000*B^2+116*k
      solverQualityRuntimeTime r n m ≤
        500*n+100000*m*(W+3*B+3)+r.template.forestRate (n+1)*(n+2+30*m)+
        (2+2*B)*(targetTestLimit M V k*(M*(100000000*W^3)+(30*M+1)*r.template.cycleRate M)+
          100*W+419)+50+2*r.qualityCost M := by
  let bound := fun M => solverQualityTimeAt (r.forSize M) n m M + 2*r.qualityCost M
  have hi : m ∈ Finset.Icc m (3*m) := Finset.mem_Icc.mpr ⟨le_rfl,by omega⟩
  obtain ⟨M,hM,hMax⟩ := Finset.exists_mem_eq_sup (Finset.Icc m (3*m)) ⟨m,hi⟩ bound
  obtain ⟨hLower,hUpper⟩ := Finset.mem_Icc.mp hM
  refine ⟨M,hM,?_⟩
  let V := solverPenalty m
  let B := M.size+V.size
  let k := r.qualityExponent M
  let W := 30000000*B^2+116*k
  let L := ipmQualityLimbs M V k
  let E := ipmQualityRangeExponent M V k
  let F := ipmQualityMinRatioFormat M V k (w:=ipmQualityParameterWordBits M V k) le_rfl
  let rounds := targetSearchRounds (M*V^2)
  let search := targetSearchCost F M V k E r.template.cycleRate
  let f := r.template.forestRate (n+1)
  have hpos : 0 < M := hm.trans_le hLower
  have hL : L≤W := (ipmQualityLimbs_le M V k).trans
    (Nat.add_le_add_right (target_format_bit_bound M V hpos).1 _)
  have hP : F.fmt.precision≤W := by
    refine le_trans ?_ hL
    change ipmQualityPrecision M V k ≤ L
    unfold L ipmQualityLimbs
    omega
  have hE : E≤W := by
    refine le_trans ?_ hL
    unfold E L ipmQualityLimbs
    omega
  have hW : 1≤W := by
    have hb : 0<B := (Nat.size_pos.mpr hpos).trans_le (Nat.le_add_right _ _)
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (by
      unfold W
      exact (Nat.mul_pos (by decide) (pow_pos hb 2)).trans_le (Nat.le_add_right _ _)))
  have hSearch := targetSearch_cost_width_bound F M V k E W hpos r.template.cycleRate hW hL hP hE
  have hRounds : rounds+1≤2+2*B := targetSearch_rounds_bit_bound M V
  have hLocal := solverOtherCost n m M L B rounds f hm hUpper
  have hWork : 100000*m*(L+B+rounds+1)≤100000*m*(W+3*B+3) :=
    Nat.mul_le_mul_left _ (by omega)
  have hTime : solverQualityRuntimeTime r n m ≤ bound M+30 := by
    unfold solverQualityRuntimeTime
    change max 30 ((Finset.Icc m (3*m)).sup bound) ≤ _
    rw [hMax]
    exact max_le (Nat.le_add_left _ _) (Nat.le_add_right _ _)
  refine hTime.trans ?_
  let rest := 300*m+400*n+M*(200*L+600)+20028*B+23000+
    (30*(n+1)+M*(600*L+1900)+36*L+1800)+(14*(B+rounds)+550)+
    (roundMachineCost f L (n+1) M+17*(M*L)+m*(100*L+240)+100)+1200
  let localBound := 500*n+100000*m*(W+3*B+3)+f*(n+2+30*m)
  let searchBound := (2+2*B)*(targetTestLimit M V k*
    (M*(100000000*W^3)+(30*M+1)*r.template.cycleRate M)+100*W+419)
  have hRest : rest ≤ localBound := hLocal.trans
    (Nat.add_le_add_right (Nat.add_le_add_left hWork _) _)
  have hEq : bound M + 30 = rest + search + 50 + 2*r.qualityCost M := by
    change 300*m+400*n+M*(200*L+600)+20028*B+23020+
      (30*(n+1)+M*(600*L+1900)+36*L+1800)+(14*(B+rounds)+550)+search+
      (roundMachineCost f L (n+1) M+17*(M*L)+m*(100*L+240)+100)+1200+2*r.qualityCost M+30 =
      rest + search + 50 + 2*r.qualityCost M
    dsimp only [rest]
    rw [show (23020 : ℕ) = 23000 + 20 by decide, show (50 : ℕ) = 20 + 30 by decide]
    ac_rfl
  rw [hEq]
  change rest+search+50+2*r.qualityCost M ≤ localBound+searchBound+50+2*r.qualityCost M
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add hRest hSearch) _) _

end MinCostFlow.IPM.Machine
