module

public import MinCostFlow.Final.AssemblyDryRunSCLastMult
import Mathlib.Tactic

/-!
# Polynomial space bound for `dryLastSpace` (`AssemblyDryRunSCLastSpace`)

Proves `dryLastSpace_le_poly`: `dryLastSpace J = packedRuntimeAllocBound ...` is bounded by a
`PolyNat` function of `(solverConnectedAugmented J).m`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program WideWord

set_option maxHeartbeats 800000 in
/-- Polynomial bound on `packedRuntimeAllocBound` abstract in `guest` (so `lastGuest` is never
unfolded by tactics). -/
private theorem packedRuntimeAllocBound_le_poly (guest : Program) (C : ℝ) (c₀ : ℕ) :
    ∃ K : ℕ, ∀ L M vCap eCap : ℕ,
      packedRuntimeAllocBound guest C c₀ L M vCap eCap ≤
        K * (L + M + vCap + eCap + 2) ^ 7 := by
  generalize hD : ⌈max 1 C⌉₊ = D
  generalize hsc : simScale guest = sG
  generalize ha7 : (1024 * D).size = a7
  let Bmul : ℕ := 20 + a7
  let Smul : ℕ := max 1 c₀ * 25 * Bmul
  let C_gw : ℕ := 10000 + (D * 100 + 2000) * Smul ^ 2 + sG * Smul * (D * 100 * Smul ^ 2 + 50)
  let K : ℕ := 1000 * C_gw + 500000 * Bmul ^ 2 + 1000 * D + c₀ + 100000
  refine ⟨K, fun L M vCap eCap => ?_⟩
  set Z := L + M + vCap + eCap + 2
  have hZ1 : 1 ≤ Z := by omega
  have hZp : ∀ a b : ℕ, a ≤ b → Z ^ a ≤ Z ^ b := fun a b h => Nat.pow_le_pow_right hZ1 h
  have hZ12 : Z ≤ Z ^ 2 := by simpa only [pow_one] using hZp 1 2 (by decide)
  have hZ13 : Z ≤ Z ^ 3 := by simpa only [pow_one] using hZp 1 3 (by decide)
  have hZ15 : Z ≤ Z ^ 5 := by simpa only [pow_one] using hZp 1 5 (by decide)
  have hZ16 : Z ≤ Z ^ 6 := by simpa only [pow_one] using hZp 1 6 (by decide)
  have hZ17 : Z ≤ Z ^ 7 := by simpa only [pow_one] using hZp 1 7 (by decide)
  have hZ27 : Z ^ 2 ≤ Z ^ 7 := hZp 2 7 (by decide)
  have hZ37 : Z ^ 3 ≤ Z ^ 7 := hZp 3 7 (by decide)
  have hZ47 : Z ^ 4 ≤ Z ^ 7 := hZp 4 7 (by decide)
  have hZ56 : Z ^ 5 ≤ Z ^ 6 := hZp 5 6 (by decide)
  have hZ67 : Z ^ 6 ≤ Z ^ 7 := hZp 6 7 (by decide)
  have hBmul1 : 1 ≤ Bmul := by dsimp only [Bmul]; omega
  have hBmul2 : Bmul ≤ Bmul ^ 2 := Nat.le_self_pow (by decide) Bmul
  have hSmul1 : 1 ≤ Smul := by
    dsimp only [Smul]; have h1 : 1 ≤ max 1 c₀ := le_max_left _ _; nlinarith only [h1, hBmul1]
  have hSm2 : Smul ≤ Smul ^ 2 := Nat.le_self_pow (by decide) Smul
  have hS2 : 2 ≤ Smul := by
    dsimp only [Smul]; have h1 : 1 ≤ max 1 c₀ := le_max_left _ _; nlinarith only [h1, hBmul1]
  have hBmul_Smul : Bmul ≤ Smul := by
    dsimp only [Smul]; have h1 : 1 ≤ max 1 c₀ := le_max_left _ _; nlinarith only [h1, hBmul1]
  unfold packedRuntimeAllocBound
  dsimp only
  rw [hD]
  set H := countGraph (2 * M) M
  set Gc := countGraph (M + 1) M
  have hHn : H.n = 2 * M := countGraph_n (2 * M) M
  have hHm : H.m = M := countGraph_m (2 * M) M
  have hGn : Gc.n = M + 1 := countGraph_n (M + 1) M
  have hGm : Gc.m = M := countGraph_m (M + 1) M
  set N := representativeGuestWidthBound D L M
  have hN_le : N ≤ Bmul * Z := by
    unfold N representativeGuestWidthBound
    rw [ha7]
    have hs1 : (2 * M).size ≤ 2 * M := Nat.size_le.mpr Nat.lt_two_pow_self
    have hs2 : (M + 1).size ≤ M + 1 := Nat.size_le.mpr Nat.lt_two_pow_self
    have hBm : 20 + a7 ≤ Bmul := by dsimp only [Bmul]; omega
    have hsum : max (2 * M).size (4 * L) + max (4 * L) (a7 + 3 * (M + 1).size) + 1 ≤
        8 * L + 5 * M + a7 + 4 := by omega
    have h1 : 8 * L + 5 * M + 4 ≤ 20 * Z := by omega
    have h2 : a7 ≤ a7 * Z := Nat.le_mul_of_pos_right a7 hZ1
    nlinarith only [hsum, h1, h2, hBm, hZ1]
  have hSim_le : ∀ n', n' ≤ 2 * Z → lsstLSimMin c₀ n' M N 1 ≤ Smul * Z := by
    intro n' _
    unfold lsstLSimMin w'Max kWidthOf
    have hl1 := Nat.log_le_self 2 (6 + 16 * M)
    have hl2 := Nat.log_le_self 2 (4 * M + 2)
    have h1 : N + (Nat.log 2 (4 * M + 2) + 1) + 2 ≤ 5 * Bmul * Z := by
      have : Nat.log 2 (4 * M + 2) + 1 + 2 ≤ 4 * Z := by omega
      nlinarith only [hN_le, this, hBmul1, hZ1]
    have h2 : c₀ * (Nat.log 2 (6 + 16 * M) +
        (N + (Nat.log 2 (4 * M + 2) + 1) + 2) * 1 + 3) ≤ Smul * Z := by
      have : Nat.log 2 (6 + 16 * M) + 3 ≤ 16 * Z := by omega
      have h3 : Nat.log 2 (6 + 16 * M) + (N + (Nat.log 2 (4 * M + 2) + 1) + 2) * 1 + 3 ≤
          25 * Bmul * Z := by nlinarith only [h1, this, hBmul1, hZ1]
      have hc : c₀ ≤ max 1 c₀ := le_max_right _ _
      calc c₀ * _ ≤ max 1 c₀ * (25 * Bmul * Z) := Nat.mul_le_mul hc h3
        _ = Smul * Z := by dsimp only [Smul]; ring
    have h1' : N + (Nat.log 2 (4 * M + 2) + 1) + 2 ≤ Smul * Z := by
      have hle : 5 * Bmul ≤ Smul := by
        dsimp only [Smul]; have h1c : 1 ≤ max 1 c₀ := le_max_left _ _; nlinarith only [h1c, hBmul1]
      exact h1.trans (Nat.mul_le_mul_right Z hle)
    exact max_le h1' h2
  apply max_le
  · -- Branch 1: `loopOnlySpace`
    unfold loopOnlySpace dynGraphSize
    have h1 : 8 + (4 + 7 * vCap + 9 * eCap) + eCap * L ≤ 50 * Z ^ 2 := by
      have hv : vCap ≤ Z := by omega
      have he : eCap ≤ Z := by omega
      have hL : L ≤ Z := by omega
      nlinarith only [hv, he, hL, hZ1, hZ12]
    have hK50 : 50 ≤ K := by dsimp only [K]; omega
    exact h1.trans (Nat.mul_le_mul hK50 hZ27)
  apply max_le
  · -- Branch 2: `representativePackedInitSpace`
    set sim := lsstLSimMin c₀ H.n H.m N 1
    have hSimH : sim ≤ Smul * Z := by
      dsimp only [sim]; rw [hHm]; exact hSim_le H.n (by omega)
    have hWP : weightPrecision C H ≤ Bmul * Z := by
      unfold weightPrecision integerScale
      rw [hD, hHn, hHm]
      have hl : Nat.log 2 (2 * M + 2) + 1 ≤ 2 * Z :=
        (Nat.add_le_add_right (Nat.log_le_self 2 _) 1).trans (by omega)
      have harg : 2 * (4 * D * M * (Nat.log 2 (2 * M + 2) + 1) ^ 2) < 2 ^ (a7 + 3 * Z + 1) := by
        have h1 : 2 * (4 * D * M * (Nat.log 2 (2 * M + 2) + 1) ^ 2) ≤ 32 * D * Z ^ 3 := by
          have hl2 : (Nat.log 2 (2 * M + 2) + 1) ^ 2 ≤ 4 * Z ^ 2 := by
            have := Nat.pow_le_pow_left hl 2; linarith
          have hMZ : M ≤ Z := by omega
          calc 2 * (4 * D * M * (Nat.log 2 (2 * M + 2) + 1) ^ 2)
              = 8 * D * M * (Nat.log 2 (2 * M + 2) + 1) ^ 2 := by ring
            _ ≤ 8 * D * Z * (4 * Z ^ 2) :=
                Nat.mul_le_mul (Nat.mul_le_mul_left (8 * D) hMZ) hl2
            _ = 32 * D * Z ^ 3 := by ring
        have hDlt : 32 * D < 2 ^ (a7 + 1) := by
          have h1024 : 1024 * D < 2 ^ a7 := ha7 ▸ Nat.lt_size_self (1024 * D)
          have h2p : 2 ^ a7 ≤ 2 ^ (a7 + 1) := Nat.pow_le_pow_right (by decide) (by omega)
          omega
        have hZlt : Z ^ 3 ≤ 2 ^ (3 * Z) := by
          rw [mul_comm, pow_mul]; exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le 3
        have hpowEq : 2 ^ (a7 + 3 * Z + 1) = 2 ^ (a7 + 1) * 2 ^ (3 * Z) := by
          rw [← pow_add]; congr 1; omega
        rw [hpowEq]
        exact lt_of_le_of_lt h1 (lt_of_le_of_lt (Nat.mul_le_mul_left (32 * D) hZlt)
          (Nat.mul_lt_mul_of_pos_right hDlt (Nat.two_pow_pos _)))
      have hsz : (2 * (4 * D * M * (Nat.log 2 (2 * M + 2) + 1) ^ 2)).size ≤ a7 + 3 * Z + 1 :=
        Nat.size_le.mpr harg
      have hBm : 20 + a7 ≤ Bmul := by dsimp only [Bmul]; omega
      have ha7Z : a7 ≤ a7 * Z := Nat.le_mul_of_pos_right a7 hZ1
      nlinarith only [hsz, hBm, ha7Z, hZ1]
    have hGW : queryHeap H N + guestWorkspace guest D H.n H.m sim ≤ 4 * C_gw * Z ^ 5 := by
      have hQH : queryHeap H N ≤ 12 * (Bmul * Z ^ 2) := by
        unfold queryHeap queryHeader queryBridges queryOriginals queryWeights queryLengths
        rw [hHn, hHm]
        have hMZ : M ≤ Z := by omega
        have hMN : M * N ≤ Bmul * Z ^ 2 := by nlinarith only [hMZ, hN_le]
        have hZ_B : Z ≤ Bmul * Z ^ 2 := by nlinarith only [hBmul1, hZ12]
        have h1_B : 1 ≤ Bmul * Z ^ 2 := by nlinarith only [hBmul1, hZ1, hZ12]
        linarith only [hMN, hZ_B, h1_B, hMZ]
      unfold guestWorkspace weightsSpace Num.integerDivideSpace Num.unsignedDivideSpace
        simDecodeSpace guestCitedCostBound
      dsimp only
      rw [hsc, hHn, hHm]
      have hs1 : (2 * M + 2).size ≤ 2 * Z := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
      have hs2 : (sim + 4).size ≤ (Smul + 4) * Z := by
        have := Nat.size_le.mpr (Nat.lt_two_pow_self (n := sim + 4))
        nlinarith only [this, hSimH, hZ1]
      have hSim2 : sim ^ 2 ≤ Smul ^ 2 * Z ^ 2 := by
        rw [← Nat.mul_pow]; exact Nat.pow_le_pow_left hSimH 2
      have hSZ : Smul * Z ≤ Smul ^ 2 * Z ^ 2 := Nat.mul_le_mul hSm2 hZ12
      have hdiv : 5 * (2 * sim) * (2 * sim + 1) ≤ 30 * Smul ^ 2 * Z ^ 2 := by
        nlinarith only [hSimH, hSim2, hSZ]
      have hcost : D * (4 * M + 1) * (2 * M + 2).size * ((2 * M + 2).size + (sim + 4).size) ≤
          D * 100 * Smul * Z ^ 3 := by
        have ha : 4 * M + 1 ≤ 4 * Z := by omega
        have hb : (2 * M + 2).size + (sim + 4).size ≤ 7 * Smul * Z := by
          nlinarith only [hs1, hs2, hSmul1, hZ1]
        calc _ ≤ D * (4 * Z) * (2 * Z) * (7 * Smul * Z) := by gcongr
          _ = D * 56 * Smul * Z ^ 3 := by ring
          _ ≤ D * 100 * Smul * Z ^ 3 := by gcongr; omega
      have hsim_cost : sG * sim * 2 ^ 1 *
          (D * (4 * M + 1) * (2 * M + 2).size * ((2 * M + 2).size + (sim + 4).size) +
            (2 + 3 * (4 * M)) + 1) ≤
          sG * Smul * (D * 100 * Smul ^ 2 + 50) * Z ^ 4 := by
        have h1 : D * (4 * M + 1) * (2 * M + 2).size * ((2 * M + 2).size + (sim + 4).size) +
            (2 + 3 * (4 * M)) + 1 ≤ (D * 100 * Smul + 15) * Z ^ 3 := by
          have : 2 + 3 * (4 * M) + 1 ≤ 15 * Z := by omega
          nlinarith only [hcost, this, hZ13]
        have h2 : sG * sim * 2 ^ 1 ≤ 2 * sG * Smul * Z := by
          have := Nat.mul_le_mul_left sG hSimH; nlinarith only [this]
        have h3 : 2 * (D * 100 * Smul + 15) ≤ D * 100 * Smul ^ 2 + 50 := by
          have hDS : 2 * Smul ≤ Smul ^ 2 := by nlinarith only [hS2]
          have := Nat.mul_le_mul_left (D * 100) hDS
          nlinarith only [this]
        calc _ ≤ (2 * sG * Smul * Z) * ((D * 100 * Smul + 15) * Z ^ 3) := Nat.mul_le_mul h2 h1
          _ = sG * Smul * (2 * (D * 100 * Smul + 15)) * Z ^ 4 := by ring
          _ ≤ sG * Smul * (D * 100 * Smul ^ 2 + 50) * Z ^ 4 := by gcongr
      have hMZ : M ≤ Z := by omega
      have hZ23 : Z ^ 2 ≤ Z ^ 3 := hZp 2 3 (by decide)
      have hdiv_m : M * (18 * sim + 2 * (3 * (2 * sim) + 2 + 5 * (2 * sim) * (2 * sim + 1) + 3 * (2 * sim))) ≤
          120 * Smul ^ 2 * Z ^ 3 := by
        have hin : 18 * sim + 2 * (3 * (2 * sim) + 2 + 5 * (2 * sim) * (2 * sim + 1) + 3 * (2 * sim)) ≤
            120 * Smul ^ 2 * Z ^ 2 := by
          nlinarith only [hdiv, hSimH, hSZ, hSmul1, hSm2, hZ1, hZ12]
        calc _ ≤ Z * (120 * Smul ^ 2 * Z ^ 2) := Nat.mul_le_mul hMZ hin
          _ = 120 * Smul ^ 2 * Z ^ 3 := by ring
      have hrest : queryHeap H N + ((4 + 9 * (2 * M) + 4 * M + M * sim) +
          (13 * sim + M * (18 * sim + 2 * (3 * (2 * sim) + 2 + 5 * (2 * sim) * (2 * sim + 1) + 3 * (2 * sim)))) +
          2 * M + (2 + 3 * (4 * M)) * sim +
          (5 + (1 + 2 * M) * sim + sim + (2 + 3 * (4 * M)) * (sim * 2 ^ 1 + sim))) ≤
          1000 * Smul ^ 2 * Z ^ 3 := by
        have h10B : 12 * (Bmul * Z ^ 2) ≤ 12 * Smul ^ 2 * Z ^ 3 := by
          have : Bmul ≤ Smul ^ 2 := hBmul_Smul.trans hSm2
          nlinarith only [this, hZ23]
        nlinarith only [hQH, h10B, hSimH, hSmul1, hSm2, hZ1, hZ12, hZ13, hZ23, hMZ, hdiv_m]
      have hCgw : 1000 * Smul ^ 2 + sG * Smul * (D * 100 * Smul ^ 2 + 50) ≤ C_gw := by
        have : 1000 * Smul ^ 2 ≤ (D * 100 + 2000) * Smul ^ 2 :=
          Nat.mul_le_mul_right _ (by omega)
        dsimp only [C_gw]; omega
      have hsum : 1000 * Smul ^ 2 * Z ^ 3 + sG * Smul * (D * 100 * Smul ^ 2 + 50) * Z ^ 4 ≤
          C_gw * Z ^ 5 := by
        calc _ ≤ 1000 * Smul ^ 2 * Z ^ 5 + sG * Smul * (D * 100 * Smul ^ 2 + 50) * Z ^ 5 :=
              Nat.add_le_add (Nat.mul_le_mul_left _ (hZp 3 5 (by decide)))
                (Nat.mul_le_mul_left _ (hZp 4 5 (by decide)))
          _ = (1000 * Smul ^ 2 + sG * Smul * (D * 100 * Smul ^ 2 + 50)) * Z ^ 5 := by ring
          _ ≤ C_gw * Z ^ 5 := Nat.mul_le_mul_right _ hCgw
      have h4C : C_gw * Z ^ 5 ≤ 4 * C_gw * Z ^ 5 := by
        rw [Nat.mul_assoc]; omega
      omega
    have h2Pow : 2 ^ paddedGuestWidth guest D H.n H.m sim (queryHeap H N) ≤ 32 + 8 * C_gw * Z ^ 5 := by
      unfold paddedGuestWidth
      rcases le_total 5 (Nat.log 2 (queryHeap H N + guestWorkspace guest D H.n H.m sim) + 1) with h | h
      · rw [max_eq_right h, pow_succ]
        have hpl : 2 ^ Nat.log 2 (queryHeap H N + guestWorkspace guest D H.n H.m sim) ≤
            queryHeap H N + guestWorkspace guest D H.n H.m sim + 1 := by
          cases hq : queryHeap H N + guestWorkspace guest D H.n H.m sim with
          | zero => simp
          | succ n => exact (Nat.pow_log_le_self 2 (Nat.succ_ne_zero n)).trans (Nat.le_succ _)
        have h2x : (4 * C_gw * Z ^ 5 + 1) * 2 ≤ 32 + 8 * C_gw * Z ^ 5 := by
          have : 4 * C_gw * Z ^ 5 * 2 = 8 * C_gw * Z ^ 5 := by
            clear_value C_gw; ring
          omega
        have hstep : 2 ^ Nat.log 2 (queryHeap H N + guestWorkspace guest D H.n H.m sim) * 2 ≤
            (4 * C_gw * Z ^ 5 + 1) * 2 :=
          Nat.mul_le_mul_right 2 (hpl.trans (Nat.add_le_add_right hGW 1))
        exact hstep.trans h2x
      · rw [max_eq_left h]; norm_num
    have hclog : Nat.clog 2 H.n ≤ 2 * Z := by
      rw [hHn]
      exact ((Nat.clog_le_iff_le_pow (by decide)).mpr Nat.lt_two_pow_self.le).trans (by omega)
    have hK_round : L + (weightPrecision C H + Nat.clog 2 H.n + 7) / 4 ≤ 4 * Bmul * Z := by
      have hL : L ≤ Bmul * Z := (by omega : L ≤ Z).trans (Nat.le_mul_of_pos_left Z hBmul1)
      have hZ_B : Z ≤ Bmul * Z := Nat.le_mul_of_pos_left Z hBmul1
      have h4 : 4 * (Bmul * Z) = 4 * Bmul * Z := (Nat.mul_assoc 4 Bmul Z).symm
      omega
    have hRound : stagedPackedRoundSpace H guest D N sim (Nat.clog 2 H.n) L (weightPrecision C H)
        H.n vCap eCap ≤ (20 * C_gw + 50000 * Bmul ^ 2 + 5000) * Z ^ 5 := by
      unfold stagedPackedRoundSpace queryOriginals queryWeights queryLengths stagedTraversalReserve
        edgeStretchSpace stretchFromLengthSpace narrowWeightSpace widenWeightSpace weightUpdateSpace
        Num.fixedDivideSpace Num.integerDivideSpace Num.unsignedDivideSpace dynGraphSize
      dsimp only
      set Kr := L + (weightPrecision C H + Nat.clog 2 H.n + 7) / 4
      have hKrSq : Kr ^ 2 ≤ 16 * Bmul ^ 2 * Z ^ 2 := by
        have := Nat.pow_le_pow_left hK_round 2; linarith
      have hMZ : M ≤ Z := by omega
      have hvZ : vCap ≤ Z := by omega
      have heZ : eCap ≤ Z := by omega
      have hLZ : L ≤ Z := by omega
      have hN2 : H.m * N ≤ Bmul * Z ^ 2 := by rw [hHm]; nlinarith only [hMZ, hN_le]
      have hES : edgeStretchSpace Kr ≤ 1500 * Bmul ^ 2 * Z ^ 2 := by
        unfold edgeStretchSpace stretchFromLengthSpace Num.fixedDivideSpace
          Num.integerDivideSpace Num.unsignedDivideSpace
        have hKr1 : Kr ≤ 4 * Bmul ^ 2 * Z ^ 2 := by
          have : Bmul * Z ≤ Bmul ^ 2 * Z ^ 2 := Nat.mul_le_mul hBmul2 hZ12
          nlinarith only [hK_round, this]
        nlinarith only [hKrSq, hKr1, hBmul1, hBmul2, hZ1, hZ12]
      have hNW : narrowWeightSpace Kr ≤ 1500 * Bmul ^ 2 * Z ^ 2 := by
        unfold narrowWeightSpace widenWeightSpace weightUpdateSpace
          Num.integerDivideSpace Num.unsignedDivideSpace
        dsimp only
        have hKr1 : Kr ≤ 4 * Bmul ^ 2 * Z ^ 2 := by
          have : Bmul * Z ≤ Bmul ^ 2 * Z ^ 2 := Nat.mul_le_mul hBmul2 hZ12
          nlinarith only [hK_round, this]
        nlinarith only [hKrSq, hKr1, hBmul1, hBmul2, hZ1, hZ12]
      have hH_ES : M * (5 * Kr + (2 * Kr + (10 * Kr + (3 * (3 * Kr) + 2 + 5 * (3 * Kr) * (3 * Kr + 1) + 3 * (3 * Kr))) + Kr)) ≤
          1500 * (Bmul ^ 2 * Z ^ 3) := by
        have : 5 * Kr + (2 * Kr + (10 * Kr + (3 * (3 * Kr) + 2 + 5 * (3 * Kr) * (3 * Kr + 1) + 3 * (3 * Kr))) + Kr) =
            edgeStretchSpace Kr := rfl
        rw [this]
        calc M * edgeStretchSpace Kr ≤ Z * (1500 * Bmul ^ 2 * Z ^ 2) := Nat.mul_le_mul hMZ hES
          _ = 1500 * (Bmul ^ 2 * Z ^ 3) := by ring
      have hH_NW : M * ((let W := 2 * Kr + 1; 3 * W + ((11 * W + 1) + (3 * W + 2 + 5 * W * (W + 1) + 3 * W) + W)) + Kr) ≤
          1500 * (Bmul ^ 2 * Z ^ 3) := by
        have : (let W := 2 * Kr + 1; 3 * W + ((11 * W + 1) + (3 * W + 2 + 5 * W * (W + 1) + 3 * W) + W)) + Kr =
            narrowWeightSpace Kr := rfl
        rw [this]
        calc M * narrowWeightSpace Kr ≤ Z * (1500 * Bmul ^ 2 * Z ^ 2) := Nat.mul_le_mul hMZ hNW
          _ = 1500 * (Bmul ^ 2 * Z ^ 3) := by ring
      rw [hHn, hHm]
      rw [hHn, hHm] at h2Pow
      have h2Pow' : 2 ^ paddedGuestWidth guest D (2 * M) M sim (queryHeap H N) ≤
          32 + 8 * (C_gw * Z ^ 5) := by simpa only [Nat.mul_assoc] using h2Pow
      dsimp only at hH_NW
      have hML : M * L ≤ Z ^ 2 := by nlinarith only [hMZ, hLZ]
      have heL : eCap * L ≤ Z ^ 2 := by nlinarith only [heZ, hLZ]
      have hZ25 : Z ^ 2 ≤ Z ^ 5 := hZp 2 5 (by decide)
      have hZ35 : Z ^ 3 ≤ Z ^ 5 := hZp 3 5 (by decide)
      have hM_Kr : M * Kr ≤ 4 * (Bmul ^ 2 * Z ^ 2) := by
        have h1 : M * Kr ≤ Z * (4 * Bmul * Z) := Nat.mul_le_mul hMZ hK_round
        have h2 : Bmul ≤ Bmul ^ 2 := hBmul2
        nlinarith only [h1, h2, hZ12]
      have h2M_Kr : 2 * M * Kr ≤ 8 * (Bmul ^ 2 * Z ^ 2) := by linarith only [hM_Kr]
      have h2M1_Kr : (2 * M - 1) * Kr ≤ 8 * (Bmul ^ 2 * Z ^ 2) :=
        (Nat.mul_le_mul_right Kr (Nat.sub_le (2 * M) 1)).trans h2M_Kr
      have hTrav : (Nat.clog 2 (2 * M) + 4) * (2 * M) + 1 ≤ 20 * Z ^ 2 := by
        rw [hHn] at hclog
        nlinarith only [hclog, hMZ, hZ1, hZ12]
      have hMZ_B : M * N ≤ Bmul ^ 2 * Z ^ 2 := by
        rw [hHm] at hN2; nlinarith only [hN2, hBmul2, hZ12]
      have hB5 : Bmul * Z ≤ Bmul ^ 2 * Z ^ 5 := by
        have := Nat.mul_le_mul hBmul2 hZ15; exact this
      have hB25 : Bmul ^ 2 * Z ^ 2 ≤ Bmul ^ 2 * Z ^ 5 := Nat.mul_le_mul_left _ hZ25
      have hB35 : Bmul ^ 2 * Z ^ 3 ≤ Bmul ^ 2 * Z ^ 5 := Nat.mul_le_mul_left _ hZ35
      have h15 : 1 ≤ Z ^ 5 := Nat.one_le_pow 5 Z hZ1
      have hKr5 : Kr ≤ 4 * (Bmul ^ 2 * Z ^ 5) := by linarith only [hK_round, hB5]
      have hExp : (20 * C_gw + 50000 * Bmul ^ 2 + 5000) * Z ^ 5 =
          20 * (C_gw * Z ^ 5) + 50000 * (Bmul ^ 2 * Z ^ 5) + 5000 * Z ^ 5 := by
        simp only [Nat.add_mul, Nat.mul_assoc]
      rw [hExp]
      have h1 : 2 * M + M * N + M * N + 1 + 2 ^ paddedGuestWidth guest D (2 * M) M sim (queryHeap H N) +
          M + 2 * M + ((Nat.clog 2 (2 * M) + 4) * (2 * M) + 1) + 2 * M + 6 * (2 * M) + 2 * M +
          M * Kr + M * Kr + 2 * Kr + 2 * M * Kr + (2 * M - 1) * Kr +
          M * (5 * Kr + (2 * Kr + (10 * Kr + (3 * (3 * Kr) + 2 + 5 * (3 * Kr) * (3 * Kr + 1) + 3 * (3 * Kr))) + Kr)) +
          M * (3 * (2 * Kr + 1) + (11 * (2 * Kr + 1) + 1 +
            (3 * (2 * Kr + 1) + 2 + 5 * (2 * Kr + 1) * (2 * Kr + 1 + 1) + 3 * (2 * Kr + 1)) +
            (2 * Kr + 1)) + Kr) +
          M * L + M * L + 2 * L + 3 * (2 * M) + 4 + (4 + 7 * vCap + 9 * eCap) +
          vCap + 2 + eCap + eCap * L + eCap * L + 1 ≤
          20 * (C_gw * Z ^ 5) + 50000 * (Bmul ^ 2 * Z ^ 5) + 5000 * Z ^ 5 := by
        have hES5 : M * (5 * Kr + (2 * Kr + (10 * Kr + (3 * (3 * Kr) + 2 + 5 * (3 * Kr) * (3 * Kr + 1) + 3 * (3 * Kr))) + Kr)) ≤
            1500 * (Bmul ^ 2 * Z ^ 5) := hH_ES.trans (Nat.mul_le_mul_left 1500 hB35)
        have hNW5 : M * (3 * (2 * Kr + 1) + (11 * (2 * Kr + 1) + 1 +
            (3 * (2 * Kr + 1) + 2 + 5 * (2 * Kr + 1) * (2 * Kr + 1 + 1) + 3 * (2 * Kr + 1)) +
            (2 * Kr + 1)) + Kr) ≤
            1500 * (Bmul ^ 2 * Z ^ 5) := hH_NW.trans (Nat.mul_le_mul_left 1500 hB35)
        have hMN5 : M * N ≤ Bmul ^ 2 * Z ^ 5 := hMZ_B.trans hB25
        have hMKr5 : M * Kr ≤ 4 * (Bmul ^ 2 * Z ^ 5) := hM_Kr.trans (Nat.mul_le_mul_left 4 hB25)
        have h2MKr5 : 2 * M * Kr ≤ 8 * (Bmul ^ 2 * Z ^ 5) := h2M_Kr.trans (Nat.mul_le_mul_left 8 hB25)
        have h2M1Kr5 : (2 * M - 1) * Kr ≤ 8 * (Bmul ^ 2 * Z ^ 5) := h2M1_Kr.trans (Nat.mul_le_mul_left 8 hB25)
        have hTrav5 : (Nat.clog 2 (2 * M) + 4) * (2 * M) + 1 ≤ 20 * Z ^ 5 :=
          hTrav.trans (Nat.mul_le_mul_left 20 hZ25)
        have hML5 : M * L ≤ Z ^ 5 := hML.trans hZ25
        have heL5 : eCap * L ≤ Z ^ 5 := heL.trans hZ25
        have hM5 : M ≤ Z ^ 5 := hMZ.trans hZ15
        have hv5 : vCap ≤ Z ^ 5 := hvZ.trans hZ15
        have he5 : eCap ≤ Z ^ 5 := heZ.trans hZ15
        have hL5 : L ≤ Z ^ 5 := hLZ.trans hZ15
        clear_value C_gw Bmul Smul K H Gc N sim Kr Z
        omega
      exact h1
    unfold representativePackedInitSpace stagedPackedCollectionSpace queryWeights queryLengths
    rw [hGm, hHm]
    have hMN : M * N ≤ Bmul * Z ^ 2 := by
      have hMZ : M ≤ Z := by omega
      nlinarith only [hMZ, hN_le]
    have hML : M * L ≤ Z ^ 2 := by
      have hMZ : M ≤ Z := by omega
      have hLZ : L ≤ Z := by omega
      nlinarith only [hMZ, hLZ]
    have hM_Round : M * stagedPackedRoundSpace H guest D N sim (Nat.clog 2 H.n) L
        (weightPrecision C H) H.n vCap eCap ≤
        (20 * C_gw + 50000 * Bmul ^ 2 + 5000) * Z ^ 6 := by
      have hMZ : M ≤ Z := by omega
      calc _ ≤ Z * ((20 * C_gw + 50000 * Bmul ^ 2 + 5000) * Z ^ 5) := Nat.mul_le_mul hMZ hRound
        _ = (20 * C_gw + 50000 * Bmul ^ 2 + 5000) * Z ^ 6 := by
            rw [Nat.mul_left_comm, ← pow_succ']
    have hK_ge : 20 * C_gw + 50000 * Bmul ^ 2 + 5000 + 2 * Bmul + 100 ≤ K := by
      have h2B : 2 * Bmul ≤ 2 * Bmul ^ 2 := Nat.mul_le_mul_left 2 hBmul2
      change _ ≤ 1000 * C_gw + 500000 * Bmul ^ 2 + 1000 * D + c₀ + 100000
      clear_value C_gw Bmul Smul K H Gc N sim Z
      omega
    have hMZ : M ≤ Z := by omega
    have hvZ : vCap ≤ Z := by omega
    have hLZ : L ≤ Z := by omega
    have h16 : 1 ≤ Z ^ 6 := Nat.one_le_pow 6 Z hZ1
    have hZ26 : Z ^ 2 ≤ Z ^ 6 := hZp 2 6 (by decide)
    have hStep : 11 * M + vCap + 1 + (2 * M + M * N) +
        (1 + M + 2 * L + M * L + 1 +
          M * stagedPackedRoundSpace H guest D N sim (Nat.clog 2 H.n) L
            (weightPrecision C H) H.n vCap eCap) + (2 * M + M * N) ≤
        (20 * C_gw + 50000 * Bmul ^ 2 + 5000 + 2 * Bmul + 100) * Z ^ 6 := by
      have hBM6 : Bmul * Z ^ 2 ≤ Bmul * Z ^ 6 := Nat.mul_le_mul_left _ hZ26
      have hMN6 : M * N ≤ Bmul * Z ^ 6 := hMN.trans hBM6
      have hML6 : M * L ≤ Z ^ 6 := hML.trans hZ26
      have hM6 : M ≤ Z ^ 6 := hMZ.trans hZ16
      have hv6 : vCap ≤ Z ^ 6 := hvZ.trans hZ16
      have hL6 : L ≤ Z ^ 6 := hLZ.trans hZ16
      have hExp2 : (20 * C_gw + 50000 * Bmul ^ 2 + 5000 + 2 * Bmul + 100) * Z ^ 6 =
          (20 * C_gw + 50000 * Bmul ^ 2 + 5000) * Z ^ 6 + 2 * (Bmul * Z ^ 6) + 100 * Z ^ 6 := by
        simp only [Nat.add_mul, Nat.mul_assoc]
      rw [hExp2]
      clear_value C_gw Bmul Smul K H Gc N sim Z
      omega
    exact hStep.trans (Nat.mul_le_mul hK_ge hZ67)
  · -- Branch 3: `packedRuntimeWordBound`
    unfold packedRuntimeWordBound packedFormatScalarBound integerScale
    dsimp only
    rw [hGn, hGm, ha7]
    have hSimG : lsstLSimMin c₀ (M + 1) M N 1 ≤ Smul * Z := hSim_le (M + 1) (by omega)
    have hvc : vCap * vCap * eCap ≤ Z ^ 3 := by
      have hv : vCap ≤ Z := by omega
      have he : eCap ≤ Z := by omega
      calc vCap * vCap * eCap ≤ Z * Z * Z := by gcongr
        _ = Z ^ 3 := by ring
    have his : 2 * (4 * D * M * (Nat.log 2 (M + 1 + 2) + 1) ^ 2) ≤ 32 * (D * Z ^ 3) := by
      have hl : Nat.log 2 (M + 1 + 2) + 1 ≤ 2 * Z :=
        (Nat.add_le_add_right (Nat.log_le_self 2 _) 1).trans (by omega)
      have hl2 : (Nat.log 2 (M + 1 + 2) + 1) ^ 2 ≤ 4 * Z ^ 2 := by
        have := Nat.pow_le_pow_left hl 2; linarith
      have hMZ : M ≤ Z := by omega
      calc 2 * (4 * D * M * (Nat.log 2 (M + 1 + 2) + 1) ^ 2)
          = 8 * D * M * (Nat.log 2 (M + 1 + 2) + 1) ^ 2 := by ring
        _ ≤ 8 * D * Z * (4 * Z ^ 2) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left (8 * D) hMZ) hl2
        _ = 32 * (D * Z ^ 3) := by ring
    have hs1 : (2 * M).size ≤ 2 * M := Nat.size_le.mpr Nat.lt_two_pow_self
    have hs2 : (M + 1).size ≤ M + 1 := Nat.size_le.mpr Nat.lt_two_pow_self
    have hKge : 16384 + 40 * D + 10 * Smul + 10 * Bmul + c₀ + 1000 ≤ K := by
      have hSmC : 10 * Smul ≤ C_gw := by
        have h2000 : 2000 * Smul ^ 2 ≤ C_gw := by
          have := Nat.mul_le_mul_right (Smul ^ 2) (by omega : 2000 ≤ D * 100 + 2000)
          change _ ≤ 10000 + (D * 100 + 2000) * Smul ^ 2 + sG * Smul * (D * 100 * Smul ^ 2 + 50)
          omega
        nlinarith only [h2000, hSmul1, hSm2]
      have h10B : 10 * Bmul ≤ 10 * Bmul ^ 2 := Nat.mul_le_mul_left 10 hBmul2
      change _ ≤ 1000 * C_gw + 500000 * Bmul ^ 2 + 1000 * D + c₀ + 100000
      clear_value C_gw Bmul Smul K H Gc N Z
      omega
    have hZ13' : Z ≤ Z ^ 3 := hZ13
    apply max_le
    · apply max_le
      · have h17 : 1 ≤ Z ^ 7 := Nat.one_le_pow 7 Z hZ1
        have : 2 ^ 14 ≤ K := by
          change 2 ^ 14 ≤ 1000 * C_gw + 500000 * Bmul ^ 2 + 1000 * D + c₀ + 100000
          omega
        nlinarith only [this, h17]
      · exact hvc.trans ((Nat.le_mul_of_pos_left _ (by
          change 0 < 1000 * C_gw + 500000 * Bmul ^ 2 + 1000 * D + c₀ + 100000; omega)).trans
          (Nat.mul_le_mul_left K hZ37))
    · have hmax : max (4 * L) (a7 + 3 * (M + 1).size) ≤ 4 * L + a7 + 3 * (M + 1) := by omega
      have hBmZ : a7 ≤ Bmul * Z := by
        have : a7 ≤ Bmul := by dsimp only [Bmul]; omega
        exact this.trans (Nat.le_mul_of_pos_right _ hZ1)
      have hRest : 16 + D + c₀ + (M + 1) + 4 + 16 * M + 8 +
          (2 * (4 * D * M * (Nat.log 2 (M + 1 + 2) + 1) ^ 2) + 2) +
          (4 * L + max (4 * L) (a7 + 3 * (M + 1).size) + (2 * M).size + 2) +
          N + N + (4 * L + N) + lsstLSimMin c₀ (M + 1) M N 1 ≤
          (16384 + 40 * D + 10 * Smul + 10 * Bmul + c₀ + 1000) * Z ^ 3 := by
        have hSmZ : Smul * Z ≤ Smul * Z ^ 3 := Nat.mul_le_mul_left _ hZ13'
        have hBmZ3 : Bmul * Z ≤ Bmul * Z ^ 3 := Nat.mul_le_mul_left _ hZ13'
        have h13 : 1 ≤ Z ^ 3 := Nat.one_le_pow 3 Z hZ1
        have hD3 : D ≤ D * Z ^ 3 := Nat.le_mul_of_pos_right D h13
        have hc3 : c₀ ≤ c₀ * Z ^ 3 := Nat.le_mul_of_pos_right c₀ h13
        have hMZ : M ≤ Z ^ 3 := (by omega : M ≤ Z).trans hZ13'
        have hLZ : L ≤ Z ^ 3 := (by omega : L ≤ Z).trans hZ13'
        have hN3 : N ≤ Bmul * Z ^ 3 := hN_le.trans hBmZ3
        have ha73 : a7 ≤ Bmul * Z ^ 3 := hBmZ.trans hBmZ3
        have hSim3 : lsstLSimMin c₀ (M + 1) M N 1 ≤ Smul * Z ^ 3 := hSimG.trans hSmZ
        have hExp3 : (16384 + 40 * D + 10 * Smul + 10 * Bmul + c₀ + 1000) * Z ^ 3 =
            16384 * Z ^ 3 + 40 * (D * Z ^ 3) + 10 * (Smul * Z ^ 3) + 10 * (Bmul * Z ^ 3) +
              c₀ * Z ^ 3 + 1000 * Z ^ 3 := by
          simp only [Nat.add_mul, Nat.mul_assoc]
        rw [hExp3]
        clear_value C_gw Bmul Smul K H Gc N Z
        omega
      exact hRest.trans (Nat.mul_le_mul hKge hZ37)

/-- `dryLastSpace J` is bounded by a `PolyNat` function of `I.m`. -/
theorem dryLastSpace_le_poly :
    ∃ f : ℕ → ℕ, PolyNat f ∧
      ∀ (J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        dryLastSpace J ≤ f (solverConnectedAugmented J).m := by
  obtain ⟨K, hK⟩ := packedRuntimeAllocBound_le_poly lastGuest lastCanonConst lastWordConst
  let fArg : ℕ → ℕ := fun M => dryLimbsOfM M + M + 2 * (12 * dryM0OfM M + 4) + 2
  have hfArgPoly : PolyNat fArg :=
    PolyNat.add_const
      (PolyNat.add
        (PolyNat.add (SubpolyNat.toPolyNat dryLimbsOfM_subpoly) PolyNat.id)
        (PolyNat.const_mul (PolyNat.add_const (PolyNat.const_mul dryM0OfM_poly 12) 4) 2)) 2
  refine ⟨fun M => K * (fArg M) ^ 7, PolyNat.const_mul (PolyNat.pow hfArgPoly 7) K,
    fun J hJn hJm hCap => ?_⟩
  set I := solverConnectedAugmented J
  set k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  have hL : ipmQualityLimbs I.m (solverPenalty J.m) k ≤ dryLimbsOfM I.m :=
    dryLimbs_le_ofM J hJn hJm hCap
  have hCapEq : dryCapLimit dryWitnessUsed J = 12 * dryM0OfM I.m + 4 := rfl
  have h1 := hK (ipmQualityLimbs I.m (solverPenalty J.m) k) I.m
    (dryCapLimit dryWitnessUsed J) (dryCapLimit dryWitnessUsed J)
  have h2 : ipmQualityLimbs I.m (solverPenalty J.m) k + I.m +
      dryCapLimit dryWitnessUsed J + dryCapLimit dryWitnessUsed J + 2 ≤ fArg I.m := by
    dsimp only [fArg]; rw [hCapEq]; omega
  exact h1.trans (Nat.mul_le_mul_left K (Nat.pow_le_pow_left h2 7))

end MinCostFlow.Final.DryRun

end
