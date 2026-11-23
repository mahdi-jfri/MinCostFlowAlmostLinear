module

public import MinCostFlow.IPM.Machine.ConnectedSolverResources

public import MinCostFlow.IPM.Machine.SolverWordSize
import MinCostFlow.IPM.Machine.TargetSearchCost
import MinCostFlow.IPM.Machine.CoefficientWorkspace
import Mathlib.Tactic

/-!
# Polynomial address space for the bounded solver

The solver's arrays and their scratch use a fixed polynomial in the
input dimensions and inverse quality. This gives a constant word
multiplier when the two data structures advertise polynomial allocation.
The proof also bounds the numeric guard used in the public precondition.
-/

public section
namespace MinCostFlow.IPM.Machine

private theorem solverWordBase_power {B : ℕ} (hB : 2≤B) {i j : ℕ} (h : i≤j) :
    B^i≤B^j := Nat.pow_le_pow_right (by omega) h

private theorem solverWordBase_constant {B c p : ℕ} (hB : 2≤B) (hc : c≤2^p) :
    c≤B^p := hc.trans (Nat.pow_le_pow_left hB p)

private theorem solverBitLength_power {B x p : ℕ} (hx : x≤B^p) (hp : p≠0) :
    x.size≤p*B := by
  apply Nat.size_le.mpr
  rw [Nat.mul_comm p B,pow_mul]
  exact hx.trans_lt (Nat.pow_lt_pow_left Nat.lt_two_pow_self hp)

private theorem solverBitLength_guard (x : ℕ) : 2^x.size≤2*(x+1) := by
  by_cases h : x.size=0
  · rw [h,pow_zero]; omega
  · have hx : 2^(x.size-1)≤x := by
      by_contra hx
      have hh := Nat.size_le.mpr (Nat.lt_of_not_ge hx)
      omega
    have hp : x.size=x.size-1+1 := by omega
    calc
      _ = 2^(x.size-1)*2 := by rw [←pow_succ,←hp]
      _ ≤ _ := by omega

private theorem connected_workspace_polynomials {A M N m L P E limit rounds B A₀ A₁ : ℕ}
    (hA : 8192≤A) (hm : m≤A) (hM : M≤A) (hN : N≤A)
    (hL : L≤A) (hP : P≤A) (hE : E≤A) (hLimit : limit≤A)
    (hRounds : rounds+1≤A) (hB : B≤A) (h₀ : A₀≤A) (h₁ : A₁≤A) :
    let len := lengthWorkspace L P E
    let grad := gradientWorkspace L P E
    let iteration := 2*B+M*(B+16*L+len+grad+12)+2*L+16
    let stage := (8*M+4)*L+M*L+((M+1)*L+M*len+((M+1)*L+M*grad)+B)+M+4+
        (M+1)*iteration+2
    (2+5*m+17*N+7+L+4*(M*L))+
      (2+N+3*M+(9*M+1)*L+5*L)+5+
      (rounds+1)*(3*L+limit*stage+2)+
      (M*L+roundMachineSpace A₀ A₁ L M+recoverScanSpace L m)≤A^10 := by
  dsimp only
  let len := lengthWorkspace A A A
  let grad := gradientWorkspace A A A
  have hlen : lengthWorkspace L P E≤len := by
    unfold len lengthWorkspace
    gcongr
  have hgrad : gradientWorkspace L P E≤grad := by
    unfold grad gradientWorkspace
    gcongr
  have hReduce :
      (2+5*m+17*N+7+L+4*(M*L))+
        (2+N+3*M+(9*M+1)*L+5*L)+5+
        (rounds+1)*(3*L+limit*((8*M+4)*L+M*L+
          ((M+1)*L+M*lengthWorkspace L P E+((M+1)*L+M*gradientWorkspace L P E)+B)+M+4+
          (M+1)*(2*B+M*(B+16*L+lengthWorkspace L P E+gradientWorkspace L P E+12)+2*L+16)+2)+2)+
        (M*L+roundMachineSpace A₀ A₁ L M+recoverScanSpace L m) ≤
      (2+5*A+17*A+7+A+4*(A*A))+
        (2+A+3*A+(9*A+1)*A+5*A)+5+
        A*(3*A+A*((8*A+4)*A+A*A+((A+1)*A+A*len+((A+1)*A+A*grad)+A)+A+4+
          (A+1)*(2*A+A*(A+16*A+len+grad+12)+2*A+16)+2)+2)+
        (A*A+roundMachineSpace A A A A+recoverScanSpace A A) := by
    unfold roundMachineSpace recoverScanSpace
    gcongr
  apply hReduce.trans
  unfold len grad gradientWorkspace lengthWorkspace roundMachineSpace recoverScanSpace
  have hAbsorb (i : ℕ) (hi : i≤8) : 8192*A^i≤A^9 := by
    calc
      _ ≤ A*A^i := Nat.mul_le_mul_right _ hA
      _ = A^(i+1) := by rw [pow_succ,Nat.mul_comm]
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  suffices hSum :
    (2+5*A+17*A+7+A+4*(A*A))+
        (2+A+3*A+(9*A+1)*A+5*A)+5+
        A*(3*A+A*((8*A+4)*A+A*A+
          ((A+1)*A+A*lengthWorkspace A A A+((A+1)*A+A*gradientWorkspace A A A)+A)+A+4+
          (A+1)*(2*A+A*(A+16*A+lengthWorkspace A A A+gradientWorkspace A A A+12)+2*A+16)+2)+2)+
        (A*A+roundMachineSpace A A A A+recoverScanSpace A A)≤8*A^9 by
    have hAdvance : 8*A^9≤A^9*A := by
      rw [Nat.mul_comm 8]
      exact Nat.mul_le_mul_left _ (show 8≤A by omega)
    exact hSum.trans (hAdvance.trans_eq (pow_succ A 9).symm)
  unfold gradientWorkspace lengthWorkspace roundMachineSpace recoverScanSpace
  have h0 := hAbsorb 0 (by decide)
  have h1 := hAbsorb 1 (by decide)
  have h2 := hAbsorb 2 (by decide)
  have h3 := hAbsorb 3 (by decide)
  have h4 := hAbsorb 4 (by decide)
  have h5 := hAbsorb 5 (by decide)
  have h6 := hAbsorb 6 (by decide)
  have h7 := hAbsorb 7 (by decide)
  ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 ⊢
  omega

private theorem connectedSolverSpaceAt_polynomial (r : SolverForestResources) (n m M d q : ℕ)
    (hm : 0 < m) (hM : m≤M) (hUpper : M≤7*m)
    (hQuality : 2^r.qualityExponent ≤ (n+m+2)^q)
    (hCycle : r.cycleSpace (n+1) M≤(n+m+2)^d)
    (hForest₀ : r.forestInitSpace (n+1) M≤(n+m+2)^d)
    (hForest₁ : r.forestOpSpace (ipmQualityLimbs M (solverPenalty m) r.qualityExponent) (n+1) M≤(n+m+2)^d) :
    max (forestConnectedSolverWorkspaceAt r n m M) (2^solverQualityForestNumericWidthAt r m M)≤
      (n+m+2)^(10*(d+2*q+240)) := by
  let base := n+m+2
  let k := r.qualityExponent
  let s := d+2*q+240
  let A := base^s
  let V := solverPenalty m
  let bits := M.size+V.size
  let L := ipmLimbs M V
  let P := ipmPrecision M V
  let E := ipmRangeExponent M V
  let wideL := ipmQualityLimbs M V k
  let wideP := ipmQualityPrecision M V k
  let wideE := ipmQualityRangeExponent M V k
  let span := 2*(M*V^2)
  let limit := targetTestLimit M V k
  let rounds := targetSearchRounds (M*V^2)
  have hBase : 3≤base := by unfold base; omega
  have hB2 : 2≤base := by omega
  have power {i j : ℕ} (h : i≤j) : base^i≤base^j := solverWordBase_power hB2 h
  have constant {c p : ℕ} (h : c≤2^p) : c≤base^p := solverWordBase_constant hB2 h
  have lift (i : ℕ) (hi : i≤s) : base^i≤A := power hi
  have hA : 8192≤A := (constant (show 8192≤2^13 by decide)).trans (lift 13 (by dsimp [s]; omega))
  have hmB : m≤base := by unfold base; omega
  have hnB : n+1≤base := by unfold base; omega
  have hmb : M≤base^2 := by
    have h7 : (7*(m:ℤ) ≤ ((m:ℤ)+2)^2) := by nlinarith [sq_nonneg ((m:ℤ)-2)]
    exact hUpper.trans ((by exact_mod_cast h7 : 7*m ≤ (m+2)^2).trans
      (Nat.pow_le_pow_left (by unfold base; omega) _))
  have hVb : V≤base^85 := by
    calc
      _ ≤ 16*m^81 := solverPenalty_le m hm
      _ ≤ base^4*base^81 := Nat.mul_le_mul (constant (by decide : 16≤2^4)) (Nat.pow_le_pow_left hmB _)
      _ = _ := (pow_add base 4 81).symm
  have hbits₁ : bits≤87*base := by
    have h₁ := solverBitLength_power hmb (by decide)
    have h₂ := solverBitLength_power hVb (by decide)
    dsimp only [bits]
    omega
  have hBitsB : bits≤base^8 := by
    calc
      _ ≤ 87*base := hbits₁
      _ ≤ base^7*base := Nat.mul_le_mul_right _ (constant (by decide : 87≤2^7))
      _ = _ := (pow_succ _ _).symm
  have hV2 : 2≤V := by
    have hv := Nat.one_le_pow 2 (solverCapacityBound m) (show 1≤solverCapacityBound m from (le_max_left _ _).trans' (by decide))
    have hh := Nat.le_mul_of_pos_right (4*m) (by omega : 0<(solverCapacityBound m)^2)
    change 4*m≤V at hh
    omega
  have hMpos : 0<M := hm.trans_le hM
  have hSize : 2≤M*V := hV2.trans (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right V hMpos)
  have hFormat := target_format_bit_bound M V hMpos
  have hmarg : 30000000*bits^2≤base^41 := by
    calc
      _ ≤ base^25*(base^8)^2 := Nat.mul_le_mul (constant (by decide : 30000000≤2^25))
        (Nat.pow_le_pow_left hBitsB 2)
      _ = _ := by rw [←pow_mul,←pow_add]
  have hL : L≤base^41 := hFormat.1.trans hmarg
  have hP : P≤base^41 := hFormat.2.1.trans hmarg
  have hE : E≤base^41 := hFormat.2.2.trans hmarg
  have hLimit : limit≤base^(76+2*q) := by
    have hl := targetTest_limit_bit_bound M V k hSize
    have ht : limit≤3276800000000001*bits^3*((2:ℕ)^k)^2 := by exact_mod_cast hl
    refine ht.trans ?_
    calc
      _ ≤ (base^52)*(base^8)^3*((base^q)^2) := Nat.mul_le_mul
        (Nat.mul_le_mul (constant (by decide : 3276800000000001≤2^52)) (Nat.pow_le_pow_left hBitsB 3))
        (Nat.pow_le_pow_left hQuality 2)
      _ = _ := by rw [←pow_mul,←pow_mul,←pow_add,←pow_add]; congr 1; omega
  have hRound : rounds+1≤base^11 := by
    refine (targetSearch_rounds_bit_bound M V).trans ?_
    have hpow : 1≤base^8 := Nat.one_le_pow _ _ (by omega)
    have hs : 2+2*bits≤8*base^8 := by omega
    exact hs.trans (by
      rw [show (11:ℕ)=8+3 by decide,pow_add]
      simpa only [Nat.mul_comm 8] using Nat.mul_le_mul_left (base^8) (constant (by decide : 8≤2^3)))
  have hSpan : span≤base^173 := by
    calc
      _ ≤ base*(base^2*(base^85)^2) := Nat.mul_le_mul hB2
        (Nat.mul_le_mul hmb (Nat.pow_le_pow_left hVb 2))
      _ = _ := by
        rw [←pow_mul,←pow_add]
        simpa only [pow_one] using (pow_add base 1 172).symm
  have hNumeric : 2^solverQualityForestNumericWidthAt r m M≤A := by
    change 2^(max (ipmQualityParameterWordBits M V k)
      (max span.size (max limit.size (max bits.size k.size))))≤A
    have hAlpha : Num.IPM.alphaScale M V≤base^18 := by
      unfold Num.IPM.alphaScale
      exact (Nat.mul_le_mul (constant (by decide : 1000≤2^10)) hBitsB).trans_eq (pow_add base 10 8).symm
    have hS : ipmParameterBound M V+1≤base^93 := by
      have ha : 1≤base^85 := Nat.one_le_pow _ _ (by omega)
      have h₁ := hL.trans (power (show 41≤85 by decide))
      have h₂ := hP.trans (power (show 41≤85 by decide))
      have h₃ := hE.trans (power (show 41≤85 by decide))
      have h₄ := hAlpha.trans (power (show 18≤85 by decide))
      have h₅ := hmb.trans (power (show 2≤85 by decide))
      change 2*P+20*M+Num.IPM.alphaScale M V+V+L+E+100+1≤base^93
      have hBound : 2*P+20*M+Num.IPM.alphaScale M V+V+L+E+100+1≤128*base^85 := by omega
      exact hBound.trans (by
        have hh := Nat.mul_le_mul_right (base^85) (constant (by decide : 128≤2^8))
        exact hh.trans_eq (pow_add base 8 85).symm)
    have hMain : 2^ipmParameterWordBits M V≤base^108 := by
      unfold ipmParameterWordBits
      rw [pow_add]
      calc
        _ ≤ 2^14*(2*(ipmParameterBound M V+1)) :=
          Nat.mul_le_mul_left _ (solverBitLength_guard _)
        _ ≤ base^15*base^93 := by
          rw [←Nat.mul_assoc]
          exact Nat.mul_le_mul (constant (by decide : 2^14*2≤2^15)) hS
        _ = _ := (pow_add base 15 93).symm
    have hWide : 2^ipmQualityParameterWordBits M V k ≤ base^(108+q+9) := by
      calc
        _ ≤ 2^(ipmParameterWordBits M V+k+9) :=
          Nat.pow_le_pow_right (by decide) (ipmQualityParameterWordBits_le M V k)
        _ ≤ base^108*base^q*base^9 := by
          rw [pow_add,pow_add]
          exact Nat.mul_le_mul (Nat.mul_le_mul hMain hQuality) (Nat.pow_le_pow_left hB2 9)
        _ = _ := by rw [pow_add,pow_add]
    have doubled {x t : ℕ} (hx : x≤base^t) : 2^x.size≤base^(t+2) := by
      have ha : 1≤base^t := Nat.one_le_pow _ _ (by omega)
      refine (solverBitLength_guard _).trans ((show 2*(x+1)≤4*base^t by omega).trans ?_)
      rw [pow_add, Nat.mul_comm]
      exact Nat.mul_le_mul_left _ (constant (by decide : 4≤2^2))
    have casesWidth (x y : ℕ) (hx : 2^x≤A) (hy : 2^y≤A) : 2^(max x y)≤A := by
      rcases le_total x y with h | h
      · simpa only [max_eq_right h] using hy
      · simpa only [max_eq_left h] using hx
    apply casesWidth _ _ (hWide.trans (lift (108+q+9) (by dsimp [s]; omega)))
    apply casesWidth _ _ ((doubled hSpan).trans (lift 175 (by dsimp [s]; omega)))
    apply casesWidth _ _ ((doubled hLimit).trans (lift (76+2*q+2) (by dsimp [s]; omega)))
    apply casesWidth _ _ ((doubled hBitsB).trans (lift 10 (by dsimp [s]; omega)))
    have hkPow : 2^k.size≤base^(q+1) := by
      calc
        _ ≤ 2*(k+1) := solverBitLength_guard _
        _ ≤ 2*2^k := Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt Nat.lt_two_pow_self)
        _ ≤ base^q*base := by rw [Nat.mul_comm 2]; exact Nat.mul_le_mul hQuality hB2
        _ = _ := (pow_succ _ _).symm
    exact hkPow.trans (lift (q+1) (by dsimp [s]; omega))
  have hWideL : wideL ≤ A := by
    have hk : k ≤ base^q := Nat.lt_two_pow_self.le.trans hQuality
    have hLk := (ipmQualityLimbs_le M V k).trans
      (Nat.add_le_add hL (Nat.mul_le_mul_left 116 hk))
    let j := max 41 q
    have hj : base^41 ≤ base^j := power (le_max_left _ _)
    have hj' : base^q ≤ base^j := power (le_max_right _ _)
    refine hLk.trans ((show base^41+116*base^q ≤ 117*base^j by omega).trans ?_)
    calc
      _ ≤ base^7*base^j := Nat.mul_le_mul_right _ (constant (by decide : 117≤2^7))
      _ ≤ A := by
        rw [←pow_add]
        apply lift
        dsimp [s,j]
        omega
  have hWideP : wideP ≤ A := by
    have hh : wideP ≤ wideL := by unfold wideP wideL ipmQualityLimbs; omega
    exact hh.trans hWideL
  have hWideE : wideE ≤ A := by
    have hh : wideE ≤ wideL := by unfold wideE wideL ipmQualityLimbs; omega
    exact hh.trans hWideL
  have hActual : forestConnectedSolverWorkspaceAt r n m M≤A^10 := by
    have hlo := connected_workspace_polynomials hA
      (hmB.trans (by simpa only [pow_one] using lift 1 (by dsimp [s]; omega))) (hmb.trans (lift 2 (by dsimp [s]; omega)))
      (hnB.trans (by simpa only [pow_one] using lift 1 (by dsimp [s]; omega))) hWideL
      hWideP hWideE
      (hLimit.trans (lift (76+2*q) (by dsimp [s]; omega))) (hRound.trans (lift 11 (by dsimp [s]; omega)))
      (hCycle.trans (lift d (by dsimp [s]; omega))) (hForest₀.trans (lift d (by dsimp [s]; omega)))
      (hForest₁.trans (lift d (by dsimp [s]; omega)))
    simp only [forestConnectedSolverWorkspaceAt,targetSearchSpace,targetOffsetSpace,targetStageSpace,
      budgetedIterationSpace,ipmQualityMinRatioFormat,Num.IPM.lengthArraySpace,Num.IPM.gradientArraySpace,
      ←lengthWorkspace_eq,←gradientWorkspace_eq]
    have hFix : 2+5*m+17*n+7+wideL+4*(M*wideL)≤2+5*m+17*(n+1)+7+wideL+4*(M*wideL) := by omega
    exact (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add_right hFix _) _) _) _).trans hlo
  change _≤base^(10*s)
  rw [Nat.mul_comm 10 s,pow_mul]
  exact max_le hActual (hNumeric.trans (by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 0<A by omega) (show 1≤10 by decide)))

/-- Bound `ipmQualityLimbs` polynomially in `(n + m + 2)` from `2 ^ k ≤ (n + m + 2) ^ q`. -/
theorem ipmQualityLimbs_connected_poly (n m M k q : ℕ) (hm : 0 < m) (hM : m ≤ M)
    (hUpper : M ≤ 7 * m) (hQuality : 2 ^ k ≤ (n + m + 2) ^ q) :
    ipmQualityLimbs M (solverPenalty m) k ≤ (n + m + 2) ^ (max 41 q + 7) := by
  let base := n + m + 2
  let V := solverPenalty m
  let bits := M.size + V.size
  let L := ipmLimbs M V
  have hBase : 3 ≤ base := by unfold base; omega
  have hB2 : 2 ≤ base := by omega
  have constant {c p : ℕ} (h : c ≤ 2 ^ p) : c ≤ base ^ p := solverWordBase_constant hB2 h
  have hmB : m ≤ base := by unfold base; omega
  have hmb : M ≤ base ^ 2 := by
    have h7 : (7 * (m : ℤ) ≤ ((m : ℤ) + 2) ^ 2) := by nlinarith [sq_nonneg ((m : ℤ) - 2)]
    exact hUpper.trans ((by exact_mod_cast h7 : 7 * m ≤ (m + 2) ^ 2).trans
      (Nat.pow_le_pow_left (by unfold base; omega) _))
  have hVb : V ≤ base ^ 85 := by
    calc _ ≤ 16 * m ^ 81 := solverPenalty_le m hm
      _ ≤ base ^ 4 * base ^ 81 := Nat.mul_le_mul (constant (by decide : 16 ≤ 2 ^ 4)) (Nat.pow_le_pow_left hmB _)
      _ = _ := (pow_add base 4 81).symm
  have hbits₁ : bits ≤ 87 * base := by
    have h₁ := solverBitLength_power hmb (by decide)
    have h₂ := solverBitLength_power hVb (by decide)
    dsimp only [bits]; omega
  have hBitsB : bits ≤ base ^ 8 := by
    calc _ ≤ 87 * base := hbits₁
      _ ≤ base ^ 7 * base := Nat.mul_le_mul_right _ (constant (by decide : 87 ≤ 2 ^ 7))
      _ = _ := (pow_succ _ _).symm
  have hV2 : 2 ≤ V := by
    have hv := Nat.one_le_pow 2 (solverCapacityBound m) (show 1 ≤ solverCapacityBound m from (le_max_left _ _).trans' (by decide))
    have hh := Nat.le_mul_of_pos_right (4 * m) (by omega : 0 < (solverCapacityBound m) ^ 2)
    change 4 * m ≤ V at hh; omega
  have hMpos : 0 < M := hm.trans_le hM
  have hL : L ≤ base ^ 41 := by
    refine (target_format_bit_bound M V hMpos).1.trans ?_
    calc 30000000 * bits ^ 2 ≤ base ^ 25 * (base ^ 8) ^ 2 :=
          Nat.mul_le_mul (constant (by decide : 30000000 ≤ 2 ^ 25)) (Nat.pow_le_pow_left hBitsB 2)
      _ = _ := by rw [← pow_mul, ← pow_add]
  have hk : k ≤ base ^ q := Nat.lt_two_pow_self.le.trans hQuality
  have hLk := (ipmQualityLimbs_le M V k).trans (Nat.add_le_add hL (Nat.mul_le_mul_left 116 hk))
  let j := max 41 q
  have hj : base ^ 41 ≤ base ^ j := solverWordBase_power hB2 (le_max_left _ _)
  have hj' : base ^ q ≤ base ^ j := solverWordBase_power hB2 (le_max_right _ _)
  refine hLk.trans ((show base ^ 41 + 116 * base ^ q ≤ 117 * base ^ j by omega).trans ?_)
  calc 117 * base ^ j ≤ base ^ 7 * base ^ j := Nat.mul_le_mul_right _ (constant (by decide : 117 ≤ 2 ^ 7))
    _ = base ^ (j + 7) := (pow_add base 7 j).symm.trans (by rw [add_comm])

/-- A polynomial bound on `L`-aware forest op space and reciprocal quality
gives polynomial scratch for `forestConnectedSolverRuntimeWorkspace`. -/
theorem forestConnectedSolverRuntimeWorkspace_polynomial (r : SolverForestRuntimeResources) (n m d q : ℕ)
    (hQuality : ∀ M ∈ Finset.Icc m (7*m), 2^r.qualityExponent M ≤ (n+m+2)^q)
    (hCycle : ∀ M ∈ Finset.Icc m (7*m), r.template.cycleSpace (n+1) M≤(n+m+2)^d)
    (hForest₀ : ∀ M ∈ Finset.Icc m (7*m), r.template.forestInitSpace (n+1) M≤(n+m+2)^d)
    (hForest₁ : ∀ M ∈ Finset.Icc m (7*m), r.template.forestOpSpace (ipmQualityLimbs M (solverPenalty m) (r.qualityExponent M)) (n+1) M≤(n+m+2)^d) :
    forestConnectedSolverRuntimeWorkspace r n m ≤ (n+m+2)^(10*(d+2*q+240)) := by
  unfold forestConnectedSolverRuntimeWorkspace
  split
  · exact Nat.zero_le _
  · rename_i hm
    apply Finset.sup_le
    intro M hM
    obtain ⟨hLower,hUpper⟩ := Finset.mem_Icc.mp hM
    exact connectedSolverSpaceAt_polynomial (r.forSize M) n m M d q (Nat.pos_of_ne_zero hm)
      hLower hUpper (hQuality M hM) (hCycle M hM) (hForest₀ M hM) (hForest₁ M hM)

/-- A polynomial bound on the reciprocal quality suffices for scratch,
even when the exponent varies with the augmented edge count. -/
theorem connectedSolverRuntimeWorkspace_polynomial (r : SolverRuntimeResources) (n m d q : ℕ)
    (hQuality : ∀ M ∈ Finset.Icc m (7*m), 2^r.qualityExponent M ≤ (n+m+2)^q)
    (hCycle : ∀ M ∈ Finset.Icc m (7*m), r.template.cycleSpace (n+1) M≤(n+m+2)^d)
    (hForest₀ : ∀ M ∈ Finset.Icc m (7*m), r.template.forestInitSpace (n+1) M≤(n+m+2)^d)
    (hForest₁ : ∀ M ∈ Finset.Icc m (7*m), r.template.forestOpSpace (n+1) M≤(n+m+2)^d) :
    connectedSolverRuntimeWorkspace r n m ≤ (n+m+2)^(10*(d+2*q+240)) :=
  forestConnectedSolverRuntimeWorkspace_polynomial r.toForest n m d q hQuality hCycle hForest₀ hForest₁


end MinCostFlow.IPM.Machine
