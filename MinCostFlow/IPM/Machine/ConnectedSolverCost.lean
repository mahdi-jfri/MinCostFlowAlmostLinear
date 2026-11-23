module

public import MinCostFlow.IPM.Machine.ConnectedSolverResources
public import MinCostFlow.IPM.Machine.SolverCost
import MinCostFlow.IPM.Machine.TargetSearchCost
import Mathlib.Tactic

/-!
# Time of the connected solver at widened precision

The connected edge bound changes the linear coefficients and the
bit-length estimate. The search charge keeps the same width bound.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM Scaling Rounding

private theorem connected_solverPenalty_two (m : ℕ) (hm : 0 < m) : 2≤solverPenalty m := by
  have hU : 2≤solverCapacityBound m := le_max_left _ _
  have hpow : 1≤(solverCapacityBound m)^2 := Nat.one_le_pow _ _ (by omega)
  apply le_trans _ (Nat.le_mul_of_pos_right _ (by omega : 0 < (solverCapacityBound m)^2))
  omega

private theorem connectedSolverLogBound (m M : ℕ) (hm : 0 < m) (hM : m≤M) (hMax : M≤7*m) :
    5*Real.log ((M*solverPenalty m:ℕ):ℝ)≤435*Real.log ((m:ℝ)+2) := by
  have hmR : 0 < (m:ℝ) := Nat.cast_pos.mpr hm
  have hm1 : (1:ℝ)≤m := by exact_mod_cast hm
  have hprod : M*solverPenalty m≤112*m^82 := by
    calc
      _ ≤ (7*m)*(16*m^81) := Nat.mul_le_mul hMax (solverPenalty_le m hm)
      _ = _ := by ring
  have hreal : ((M*solverPenalty m:ℕ):ℝ)≤112*(m:ℝ)^82 := by exact_mod_cast hprod
  have hpos : (0:ℝ)<((M*solverPenalty m:ℕ):ℝ) := by
    exact_mod_cast Nat.mul_pos (hm.trans_le hM) (by have := connected_solverPenalty_two m hm; omega)
  have hl := Real.log_le_log hpos hreal
  rw [Real.log_mul (by norm_num : (112:ℝ)≠0) (pow_pos hmR _).ne',Real.log_pow] at hl
  have hmL := Real.log_le_log hmR (show (m:ℝ)≤m+2 by linarith)
  have h112 : (112:ℝ)≤((m:ℝ)+2)^5 := by
    apply le_trans (show (112:ℝ)≤3^5 by norm_num)
    exact pow_le_pow_left₀ (by norm_num) (by linarith) 5
  have hlog112 := Real.log_le_log (by norm_num : (0:ℝ)<112) h112
  rw [Real.log_pow] at hlog112
  norm_num only [Nat.cast_ofNat] at hl hlog112
  linarith only [hl,hmL,hlog112]

/-- Bound the binary length driving the solver cost at an augmented size. -/
theorem connectedSolverInputBits_log_bound (m M : ℕ) (hm : 0 < m) (hM : m≤M) (hMax : M≤7*m) :
    2≤M*solverPenalty m ∧
      ((M.size+(solverPenalty m).size:ℕ):ℝ)≤435*Real.log ((m:ℝ)+2) := by
  have hSize := (connected_solverPenalty_two m hm).trans
    (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right (solverPenalty m) (hm.trans_le hM))
  exact ⟨hSize,(Num.IPM.alpha_bit_length_bounds hSize).2.trans (connectedSolverLogBound m M hm hM hMax)⟩

private theorem connectedSolverOtherCost (n m M L B R f : ℕ) (hm : 0 < m) (hM : M≤7*m) :
    300*m+900*n+M*(200*L+600)+20028*B+23400+
    (30*(n+1)+M*(600*L+1900)+36*L+1800)+(14*(B+R)+550)+
    (roundMachineCost f L (n+1) M+17*(M*L)+m*(100*L+240)+100)+1200 ≤
      1000*n+100000*m*(L+B+R+1)+f*(n+2+70*m) := by
  have hML := Nat.mul_le_mul_right L hM
  have hMF := Nat.mul_le_mul_right f hM
  have hmL : L≤m*L := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right L hm
  have hmB : B≤m*B := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right B hm
  have hmR : R≤m*R := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right R hm
  unfold roundMachineCost
  ring_nf at hML hMF ⊢
  rw [Nat.mul_comm m L] at hmL
  omega

set_option maxHeartbeats 700000 in
/-- Cost at the augmented sizes attaining the widened solver's envelope with
`L`-dependent forest rate. -/
theorem forestConnectedSolverRuntimeTime_width_bound (r : SolverForestRuntimeResources)
    (n m : ℕ) (hm : 0 < m) :
    ∃ M ∈ Finset.Icc m (7*m),
      let V := solverPenalty m
      let B := M.size+V.size
      let k := r.qualityExponent M
      let W := 30000000*B^2+116*k
      let L := ipmQualityLimbs M V k
      forestConnectedSolverRuntimeTime r n m ≤
        1000*n+100000*m*(W+3*B+3)+r.template.forestRate (n+1) L*(n+2+70*m)+
        (2+2*B)*(targetTestLimit M V k*(M*(100000000*W^3)+(30*M+1)*r.template.cycleRate M)+
          100*W+419)+50+2*r.qualityCost M := by
  let bound := fun M => forestConnectedSolverTimeAt (r.forSize M) n m M + 2*r.qualityCost M
  have hi : m ∈ Finset.Icc m (7*m) := Finset.mem_Icc.mpr ⟨le_rfl,by omega⟩
  obtain ⟨M,hM,hMax⟩ := Finset.exists_mem_eq_sup (Finset.Icc m (7*m)) ⟨m,hi⟩ bound
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
  let f := r.template.forestRate (n+1) L
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
  have hLocal := connectedSolverOtherCost n m M L B rounds f hm hUpper
  have hWork : 100000*m*(L+B+rounds+1)≤100000*m*(W+3*B+3) :=
    Nat.mul_le_mul_left _ (by omega)
  have hTime : forestConnectedSolverRuntimeTime r n m ≤ bound M+30 := by
    unfold forestConnectedSolverRuntimeTime
    change max 30 ((Finset.Icc m (7*m)).sup bound) ≤ _
    rw [hMax]
    exact max_le (Nat.le_add_left _ _) (Nat.le_add_right _ _)
  refine hTime.trans ?_
  let rest := 300*m+900*n+M*(200*L+600)+20028*B+23400+
    (30*(n+1)+M*(600*L+1900)+36*L+1800)+(14*(B+rounds)+550)+
    (roundMachineCost f L (n+1) M+17*(M*L)+m*(100*L+240)+100)+1200
  let localBound := 1000*n+100000*m*(W+3*B+3)+f*(n+2+70*m)
  let searchBound := (2+2*B)*(targetTestLimit M V k*
    (M*(100000000*W^3)+(30*M+1)*r.template.cycleRate M)+100*W+419)
  have hRest : rest ≤ localBound := hLocal.trans
    (Nat.add_le_add_right (Nat.add_le_add_left hWork _) _)
  have hEq : bound M + 30 = rest + search + 50 + 2*r.qualityCost M := by
    change 300*m+900*n+M*(200*L+600)+20028*B+23420+
      (30*(n+1)+M*(600*L+1900)+36*L+1800)+(14*(B+rounds)+550)+search+
      (roundMachineCost f L (n+1) M+17*(M*L)+m*(100*L+240)+100)+1200+2*r.qualityCost M+30 =
      rest + search + 50 + 2*r.qualityCost M
    dsimp only [rest]
    rw [show (23420 : ℕ) = 23400 + 20 by decide, show (50 : ℕ) = 20 + 30 by decide]
    ac_rfl
  rw [hEq]
  change rest+search+50+2*r.qualityCost M ≤ localBound+searchBound+50+2*r.qualityCost M
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add hRest hSearch) _) _

/-- Cost at the augmented sizes attaining the widened solver's envelope.
The numerical dimensions are bounded by the original quadratic bit bound
plus a linear term in the runtime quality exponent. -/
theorem connectedSolverRuntimeTime_width_bound (r : SolverRuntimeResources)
    (n m : ℕ) (hm : 0 < m) :
    ∃ M ∈ Finset.Icc m (7*m),
      let V := solverPenalty m
      let B := M.size+V.size
      let k := r.qualityExponent M
      let W := 30000000*B^2+116*k
      connectedSolverRuntimeTime r n m ≤
        1000*n+100000*m*(W+3*B+3)+r.template.forestRate (n+1)*(n+2+70*m)+
        (2+2*B)*(targetTestLimit M V k*(M*(100000000*W^3)+(30*M+1)*r.template.cycleRate M)+
          100*W+419)+50+2*r.qualityCost M :=
  forestConnectedSolverRuntimeTime_width_bound r.toForest n m hm

end MinCostFlow.IPM.Machine
