module

public import MinCostFlow.Spanner.ProgSparsifyCapProps

@[expose] public section

/-!
# Polynomial Base and Heap-Space Bounds for Word-RAM `Sparsify`

Bundles the polynomial bounds on all intermediate caps (`dJCap`, `mwCap`, `phiDenCap`, PathDS
`gExp`/`gDel`/`phiOutDen`, `tau2Cap`, `eta1Cap`, `eta2Bound`, `dLMax`, and the Task 1/2/3/Output
heap deltas) derived from `DecomposeImpl.InvPhiBound` and `PathDSParams.hpoly`.
-/

namespace MinCostFlow.Spanner

open WordRAM Cited

/-- Input size `H'.n + H'.m + J.n + J.m + embVertSum` matching `citedInputSize`. -/
def sparsifyInputSize (inp : Task1Input) : ℕ :=
  inp.H'.n + inp.H'.m + inp.J.n + inp.J.m + (inp.toT2 0).embVertSum

/-- Polynomial upper bounds on all base caps and heap allocations of `Sparsify` in
`x = sparsifyInputSize inp + 2`. -/
structure SparsifyPolyPack (impl : SpannerToolImpl) where
  C_sp : ℕ
  c_sp : ℕ
  C_pd : ℕ
  k_pd : ℕ
  C_mw : ℕ
  k_mw : ℕ
  C_pds : ℕ
  k_pds : ℕ
  C_tau2 : ℕ
  k_tau2 : ℕ
  C_η1 : ℕ
  C_argJ : ℕ
  C_argW : ℕ
  C_ceArg : ℕ
  k_ceArg : ℕ
  C_dsJArg : ℕ
  k_dsJArg : ℕ
  C_dsWArg : ℕ
  k_dsWArg : ℕ
  hC_sp : 1 ≤ C_sp
  hc_sp : 1 ≤ c_sp
  hk_pd : 1 ≤ k_pd
  hk_mw : 1 ≤ k_mw
  hk_pds : 1 ≤ k_pds
  hk_ceArg : 1 ≤ k_ceArg
  hk_dsJArg : 1 ≤ k_dsJArg
  hk_dsWArg : 1 ≤ k_dsWArg
  hbounds : ∀ (inp : Task1Input),
    let x := sparsifyInputSize inp + 2
    let m0 := (stripLoops inp.J).m
    let pds := impl.pathDS.params
    let dW := WitnessCoreInput.dWInt impl.constructExpander
    Task1Input.phiDenCap impl inp.J ≤ C_pd * x ^ k_pd ∧
    Task1Input.mwCap impl inp.J ≤ C_mw * x ^ k_mw ∧
    Task1Input.dJCap impl inp.J + m0 + 2 ≤ C_argJ * x ^ k_mw ∧
    dW + Task1Input.mwCap impl inp.J + 2 ≤ C_argW * x ^ k_mw ∧
    pds.gExp (Task1Input.dJCap impl inp.J) m0 ≤ C_pds * x ^ k_pds ∧
    pds.gExp dW (Task1Input.mwCap impl inp.J) ≤ C_pds * x ^ k_pds ∧
    pds.gDel (Task1Input.dJCap impl inp.J) m0 ≤ C_pds * x ^ k_pds ∧
    pds.gDel dW (Task1Input.mwCap impl inp.J) ≤ C_pds * x ^ k_pds ∧
    Task2Input.gammaExpCap impl inp.J ≤ C_pds * x ^ k_pds ∧
    Task1Input.tau2Cap impl inp.J ≤ C_tau2 * x ^ k_tau2 ∧
    Task2Input.eta1Cap impl inp.J ≤ C_η1 * x ^ k_mw ∧
    inp.J.n + 4 * m0 * Task1Input.phiDenCap impl inp.J + 2 ≤ C_ceArg * x ^ k_ceArg ∧
    Task1Input.phiDenCap impl inp.J + inp.J.n + m0 + m0 +
      pds.gExp (Task1Input.dJCap impl inp.J) m0 + 2 ≤ C_dsJArg * x ^ k_dsJArg ∧
    impl.constructExpander.phiDen + 4 * Task1Input.mwCap impl inp.J +
      pds.gExp dW (Task1Input.mwCap impl inp.J) + 2 ≤ C_dsWArg * x ^ k_dsWArg ∧
    inp.maxHeapEnd impl ≤ inp.h + C_sp * x ^ c_sp ∧
    sparsifyMaxHeapEnd impl inp ≤ inp.h + C_sp * x ^ c_sp

/-- Builds `SparsifyPolyPack impl` from `DecomposeImpl.InvPhiBound` and `PathDSParams.hpoly`. -/
theorem SparsifyPolyPack.exists_of_invPhi (impl : SpannerToolImpl)
    (invB : impl.decompose.InvPhiBound) :
    Nonempty (SparsifyPolyPack impl) := by
  set dec := impl.decompose
  set ce := impl.constructExpander
  set pds := impl.pathDS.params
  obtain ⟨Cp0, kp, hp_poly⟩ := pds.hpoly
  set Cp := Cp0 + 1
  set A_φ : ℕ := Nat.ceil (invB.invPhiC * Real.exp (6 * invB.invPhiExp)) + 1
  set k_φ : ℕ := Nat.ceil (3 * invB.invPhiExp)
  have hinvPhi_nat : ∀ m : ℕ, 1 / dec.φ_lb m ≤ (A_φ : ℝ) * ((m : ℝ) + 2) ^ k_φ := fun m => by
    have h1 := invB.hinvPhi_le m
    have h2 := decomposeSubpoly_poly_le invB.hinvPhiExp m
    have h3 : invB.invPhiC * decomposeSubpoly invB.invPhiExp m ≤
        (invB.invPhiC * Real.exp (6 * invB.invPhiExp)) * ((m : ℝ) + 2) ^ k_φ := by
      have := mul_le_mul_of_nonneg_left h2 invB.hinvPhiC.le
      linarith
    have hA : invB.invPhiC * Real.exp (6 * invB.invPhiExp) ≤ (A_φ : ℝ) := by
      have := Nat.le_ceil (invB.invPhiC * Real.exp (6 * invB.invPhiExp))
      dsimp only [A_φ]; push_cast; linarith
    have h4 : (invB.invPhiC * Real.exp (6 * invB.invPhiExp)) * ((m : ℝ) + 2) ^ k_φ ≤
        (A_φ : ℝ) * ((m : ℝ) + 2) ^ k_φ :=
      mul_le_mul_of_nonneg_right hA (by positivity)
    exact le_trans h1 (le_trans h3 h4)
  set kmw := k_φ + 1
  set CdJ := A_φ + 1
  set Cmw := 2 * ce.c_deg_int * A_φ + 2
  set dW := WitnessCoreInput.dWInt ce
  set Cpd := dec.C_phi + 1
  set kpd := dec.c_phi + 1
  set C_argJ := CdJ + 2
  set C_argW := dW + Cmw + 2
  set C_pds := Cp * (max C_argJ C_argW) ^ kp
  set k_pds := kmw * kp + 1
  set C_tau2 := C_pds ^ 3
  set k_tau2 := 3 * k_pds
  set C_η1 := 1 + (Nat.ceil (2 * (2 * (ce.c_deg_int : ℝ))) + 1) * (2 * ce.c_deg_int * A_φ + 3)
  set C_dL := Nat.ceil dec.c_ℓ + 1
  set C_wM := 1 + 2 * ce.c_deg_int * Cpd
  set k_wM := kpd + 1
  set C_ceArg := 2 + 4 * Cpd
  set k_ceArg := kpd + 1
  set C_t1 := 60 + dec.C_space * 2 ^ dec.c_space + C_dL + pds.C_space * C_argJ ^ pds.c_space +
    pds.C_space * C_argW ^ pds.c_space + ce.C_space * C_ceArg ^ ce.c_space + 6 * C_wM
  set k_t1 := max (max dec.c_space (kmw * pds.c_space)) (max (1 + k_ceArg * ce.c_space) k_wM) + 1
  set C_dsJArg := Cpd + C_pds + 4
  set k_dsJArg := max kpd k_pds
  set C_dsJ := pds.C_space * C_dsJArg ^ pds.c_space
  set k_dsJ := k_dsJArg * pds.c_space
  set C_t2 := 60 + 2 * Cmw + 6 * Cmw * C_pds + (2 * C_η1 + Cmw) * C_dsJ
  set k_t2 := max (kmw + k_pds) (kmw + 1 + k_dsJ) + 1
  set C_dsWArg := ce.phiDen + 4 * Cmw + C_pds + 2
  set k_dsWArg := max kmw k_pds
  set C_dsW := pds.C_space * C_dsWArg ^ pds.c_space
  set k_dsW := k_dsWArg * pds.c_space
  set C_t3 := 60 + 3 * Cmw + (5 + C_pds) * C_dsW + 5 * C_pds
  set k_t3 := max (max kmw (2 + k_pds + k_dsW)) (1 + k_pds) + 1
  set C_out := 20 + 9 * Cmw * C_pds + 8 * C_pds ^ 2 + 14 * C_pds
  set k_out := max (kmw + k_pds) (1 + 2 * k_pds) + 1
  set C_sp := C_t1 + C_t2 + C_t3 + C_out + 1
  set c_sp := max (max k_t1 k_t2) (max k_t3 k_out)
  refine ⟨{
    C_sp := C_sp, c_sp := c_sp, C_pd := Cpd, k_pd := kpd, C_mw := Cmw, k_mw := kmw,
    C_pds := C_pds, k_pds := k_pds, C_tau2 := C_tau2, k_tau2 := k_tau2, C_η1 := C_η1,
    C_argJ := C_argJ, C_argW := C_argW, C_ceArg := C_ceArg, k_ceArg := k_ceArg,
    C_dsJArg := C_dsJArg, k_dsJArg := k_dsJArg, C_dsWArg := C_dsWArg, k_dsWArg := k_dsWArg,
    hC_sp := by omega, hc_sp := by omega, hk_pd := by omega, hk_mw := by omega,
    hk_pds := by omega, hk_ceArg := by omega, hk_dsJArg := by omega, hk_dsWArg := by omega,
    hbounds := fun inp => ?_ }⟩
  intro x m0 pds' dW'
  have hx1 : 1 ≤ x := by dsimp only [x]; omega
  have hm0_le_m : m0 ≤ inp.J.m := stripLoops_m_le inp.J
  have hHn_x : inp.H'.n ≤ x := by dsimp only [x, sparsifyInputSize]; omega
  have hJn_x : inp.J.n ≤ x := by dsimp only [x, sparsifyInputSize]; omega
  have hJm_x : inp.J.m ≤ x := by dsimp only [x, sparsifyInputSize]; omega
  have hm0_x : m0 ≤ x := le_trans hm0_le_m hJm_x
  have hevs_x : (inp.toT2 0).embVertSum ≤ x := by dsimp only [x, sparsifyInputSize]; omega
  have h1_pow : ∀ r, 1 ≤ x ^ r := fun r => Nat.one_le_pow r x hx1
  have hdJ_ge1 : 1 ≤ Task1Input.dJCap impl inp.J :=
    Nat.one_le_ceil_iff.mpr (div_pos one_pos (dec.hφ_lb_pos m0))
  have hdW_ge1 : 1 ≤ dW := by
    dsimp only [dW]; rw [WitnessCoreInput.dWInt_eq]
    exact Nat.one_le_ceil_iff.mpr (div_pos one_pos ce.hφ_Const_pos)
  have hinv_x : 1 / dec.φ_lb m0 ≤ (A_φ : ℝ) * (x : ℝ) ^ k_φ :=
    le_trans (hinvPhi_nat m0) (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by exact_mod_cast (by dsimp only [x, sparsifyInputSize]; omega : m0 + 2 ≤ x)) k_φ)
      (Nat.cast_nonneg _))
  have hdJ_le : Task1Input.dJCap impl inp.J ≤ CdJ * x ^ kmw := by
    unfold Task1Input.dJCap
    have h2 : Nat.ceil (1 / dec.φ_lb m0) ≤ A_φ * x ^ k_φ := Nat.ceil_le.mpr (by exact_mod_cast hinv_x)
    have h3 : x ^ k_φ ≤ x ^ kmw := Nat.pow_le_pow_right hx1 (by omega)
    have h4 := h1_pow kmw
    have h5 : A_φ * x ^ k_φ ≤ A_φ * x ^ kmw := Nat.mul_le_mul_left A_φ h3
    dsimp only [CdJ]; nlinarith only [h2, h4, h5]
  have hmw_le : Task1Input.mwCap impl inp.J ≤ Cmw * x ^ kmw := by
    unfold Task1Input.mwCap
    have h1 : 2 * (ce.c_deg_int : ℝ) * (m0 : ℝ) / dec.φ_lb m0 ≤
        ((2 * ce.c_deg_int * A_φ : ℕ) : ℝ) * (x : ℝ) ^ kmw := by
      have hb : (m0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hm0_x
      have hc : 2 * (ce.c_deg_int : ℝ) * (m0 : ℝ) / dec.φ_lb m0 =
          (2 * (ce.c_deg_int : ℝ)) * ((m0 : ℝ) * (1 / dec.φ_lb m0)) := by ring
      rw [hc]
      have hd := mul_le_mul hb hinv_x (div_nonneg zero_le_one (dec.hφ_lb_pos m0).le) (Nat.cast_nonneg _)
      have he := mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ 2 * (ce.c_deg_int : ℝ))
      have hf : (2 * (ce.c_deg_int : ℝ)) * ((x : ℝ) * ((A_φ : ℝ) * (x : ℝ) ^ k_φ)) =
          ((2 * ce.c_deg_int * A_φ : ℕ) : ℝ) * (x : ℝ) ^ kmw := by
        dsimp only [kmw]; push_cast; rw [pow_succ]; ring
      linarith only [he, hf]
    have h2 : Nat.ceil (2 * (ce.c_deg_int : ℝ) * (m0 : ℝ) / dec.φ_lb m0) ≤
        2 * ce.c_deg_int * A_φ * x ^ kmw := Nat.ceil_le.mpr (by exact_mod_cast h1)
    have h3 := h1_pow kmw
    dsimp only [Cmw]; nlinarith only [h2, h3]
  have hpd_le : Task1Input.phiDenCap impl inp.J ≤ Cpd * x ^ kpd := by
    unfold Task1Input.phiDenCap
    have h1 := dec.hmaxPhiDen_le m0
    have h2 : (m0 + 2) ^ dec.c_phi ≤ x ^ kpd :=
      le_trans (Nat.pow_le_pow_left (by dsimp only [x, sparsifyInputSize]; omega) dec.c_phi)
        (Nat.pow_le_pow_right hx1 (by omega))
    exact le_trans h1 (Nat.mul_le_mul (by omega) h2)
  have hargJ_le : Task1Input.dJCap impl inp.J + m0 + 2 ≤ C_argJ * x ^ kmw := by
    have h1 : m0 + 2 ≤ 2 * x ^ kmw := by
      have : x ≤ x ^ kmw := Nat.le_self_pow (by omega) x; omega
    dsimp only [C_argJ]; nlinarith only [hdJ_le, h1]
  have hargW_le : dW + Task1Input.mwCap impl inp.J + 2 ≤ C_argW * x ^ kmw := by
    have h1 := h1_pow kmw
    dsimp only [C_argW]; nlinarith only [hmw_le, h1]
  have hpds_J : pds.gQuery (Task1Input.dJCap impl inp.J) m0 ≤ C_pds * x ^ k_pds ∧
      pds.gDel (Task1Input.dJCap impl inp.J) m0 ≤ C_pds * x ^ k_pds := by
    have ⟨hQ, hD⟩ := hp_poly (Task1Input.dJCap impl inp.J) m0 hdJ_ge1
    have hpow : (Task1Input.dJCap impl inp.J + m0 + 2) ^ kp ≤ (max C_argJ C_argW) ^ kp * x ^ k_pds :=
      spPoly_le hx1 (spPoly_pow (le_trans hargJ_le (Nat.mul_le_mul_right _ (le_max_left _ _)))) le_rfl (by omega)
    refine ⟨le_trans hQ ?_, le_trans hD ?_⟩ <;>
      calc _ ≤ Cp * ((max C_argJ C_argW) ^ kp * x ^ k_pds) := Nat.mul_le_mul (by omega) hpow
        _ = C_pds * x ^ k_pds := by dsimp only [C_pds]; ring
  have hpds_W : pds.gQuery dW (Task1Input.mwCap impl inp.J) ≤ C_pds * x ^ k_pds ∧
      pds.gDel dW (Task1Input.mwCap impl inp.J) ≤ C_pds * x ^ k_pds := by
    have ⟨hQ, hD⟩ := hp_poly dW (Task1Input.mwCap impl inp.J) hdW_ge1
    have hpow : (dW + Task1Input.mwCap impl inp.J + 2) ^ kp ≤ (max C_argJ C_argW) ^ kp * x ^ k_pds :=
      spPoly_le hx1 (spPoly_pow (le_trans hargW_le (Nat.mul_le_mul_right _ (le_max_right _ _)))) le_rfl (by omega)
    refine ⟨le_trans hQ ?_, le_trans hD ?_⟩ <;>
      calc _ ≤ Cp * ((max C_argJ C_argW) ^ kp * x ^ k_pds) := Nat.mul_le_mul (by omega) hpow
        _ = C_pds * x ^ k_pds := by dsimp only [C_pds]; ring
  have hgEJ_le : pds.gExp (Task1Input.dJCap impl inp.J) m0 ≤ C_pds * x ^ k_pds :=
    le_trans (pds.hgQuery_ge _ _ hdJ_ge1) hpds_J.1
  have hgEW_le : pds.gExp dW (Task1Input.mwCap impl inp.J) ≤ C_pds * x ^ k_pds :=
    le_trans (pds.hgQuery_ge _ _ hdW_ge1) hpds_W.1
  have hphiJ_le : pds.phiOutDen (Task1Input.dJCap impl inp.J) m0 ≤ C_pds * x ^ k_pds :=
    le_trans (pds.hgExp_ge _ _ hdJ_ge1) hgEJ_le
  have hphiW_le : pds.phiOutDen dW (Task1Input.mwCap impl inp.J) ≤ C_pds * x ^ k_pds :=
    le_trans (pds.hgExp_ge _ _ hdW_ge1) hgEW_le
  have hγE_le : Task2Input.gammaExpCap impl inp.J ≤ C_pds * x ^ k_pds := max_le hgEJ_le hgEW_le
  have hγE1_le : Task1Input.gammaExpCap impl inp.J ≤ C_pds * x ^ k_pds := max_le hgEJ_le hgEW_le
  have hγD_le : Task1Input.gammaDelCap impl inp.J ≤ C_pds * x ^ k_pds := max_le hpds_J.2 hpds_W.2
  have hphiDs_le : Task1Input.phiDsDenCap impl inp.J ≤ C_pds * x ^ k_pds := max_le hphiJ_le hphiW_le
  have htau2_le : Task1Input.tau2Cap impl inp.J ≤ C_tau2 * x ^ k_tau2 := by
    unfold Task1Input.tau2Cap
    have h1 := spPoly_mul hγE1_le hγD_le
    have h2 := spPoly_mul h1 hphiDs_le
    exact spPoly_le hx1 h2 (le_of_eq (by dsimp only [C_tau2]; ring)) (by omega)
  have hη1_le : Task2Input.eta1Cap impl inp.J ≤ C_η1 * x ^ kmw := by
    unfold Task2Input.eta1Cap; dsimp only
    have hdiv : 2 * (ce.c_deg_int : ℝ) * (inp.J.m : ℝ) / (2 * dec.φ_lb m0) ≤
        ((2 * ce.c_deg_int * A_φ : ℕ) : ℝ) * (x : ℝ) ^ kmw := by
      have hpos := dec.hφ_lb_pos m0
      have h1 : 2 * (ce.c_deg_int : ℝ) * (inp.J.m : ℝ) / (2 * dec.φ_lb m0) ≤
          2 * (ce.c_deg_int : ℝ) * (inp.J.m : ℝ) / dec.φ_lb m0 :=
        div_le_div_of_nonneg_left (by positivity) hpos (by linarith only [hpos])
      have h2 : (inp.J.m : ℝ) * (1 / dec.φ_lb m0) ≤ (x : ℝ) * ((A_φ : ℝ) * (x : ℝ) ^ k_φ) :=
        mul_le_mul (by exact_mod_cast hJm_x) hinv_x (div_nonneg zero_le_one hpos.le) (Nat.cast_nonneg _)
      have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * (ce.c_deg_int : ℝ))
      have h4 : 2 * (ce.c_deg_int : ℝ) * (inp.J.m : ℝ) / dec.φ_lb m0 =
          2 * (ce.c_deg_int : ℝ) * ((inp.J.m : ℝ) * (1 / dec.φ_lb m0)) := by ring
      have h5 : 2 * (ce.c_deg_int : ℝ) * ((x : ℝ) * ((A_φ : ℝ) * (x : ℝ) ^ k_φ)) =
          ((2 * ce.c_deg_int * A_φ : ℕ) : ℝ) * (x : ℝ) ^ kmw := by
        dsimp only [kmw]; push_cast; rw [pow_succ]; ring
      linarith only [h1, h3, h4, h5]
    have hceil : Nat.ceil (2 * (ce.c_deg_int : ℝ) * (inp.J.m : ℝ) / (2 * dec.φ_lb m0)) ≤
        2 * ce.c_deg_int * A_φ * x ^ kmw := Nat.ceil_le.mpr (by exact_mod_cast hdiv)
    have hlog : Nat.log 2 (Nat.ceil (2 * (ce.c_deg_int : ℝ) * (inp.J.m : ℝ) / (2 * dec.φ_lb m0)) + 1) + 1 ≤
        (2 * ce.c_deg_int * A_φ + 3) * x ^ kmw := by
      have hlg := spNat_log2_le_self (Nat.ceil (2 * (ce.c_deg_int : ℝ) * (inp.J.m : ℝ) / (2 * dec.φ_lb m0)) + 1)
      have h1 := h1_pow kmw; nlinarith only [hceil, hlg, h1]
    have hprod := Nat.mul_le_mul (Nat.le_succ (Nat.ceil (2 * (2 * (ce.c_deg_int : ℝ))))) hlog
    have h1 := h1_pow kmw
    dsimp only [C_η1]; nlinarith only [hprod, h1]
  have hη2_le : eta2Bound inp.J ≤ 3 * x := by
    unfold eta2Bound; have := spNat_log2_le_self (inp.J.m + 1); dsimp only [x, sparsifyInputSize]; omega
  have hdL_le : Task1Input.dLMax impl inp.J ≤ C_dL * x := by
    unfold Task1Input.dLMax
    have hlog : Nat.log 2 (m0 + 2) + 1 ≤ x := by
      have h1 : Nat.log 2 (m0 + 2) < m0 + 2 :=
        (Nat.log_lt_iff_lt_pow (by norm_num) (by omega)).mpr Nat.lt_two_pow_self
      dsimp only [x, sparsifyInputSize]; omega
    have hc : dec.c_ℓ ≤ (C_dL : ℝ) := by
      have := Nat.le_ceil dec.c_ℓ; dsimp only [C_dL]; push_cast; linarith only [this]
    have hmul : dec.c_ℓ * ((Nat.log 2 (m0 + 2) : ℝ) + 1) ≤ ((C_dL * x : ℕ) : ℝ) := by
      have h1 := mul_le_mul hc (by exact_mod_cast hlog : (Nat.log 2 (m0 + 2) : ℝ) + 1 ≤ (x : ℝ))
        (by positivity) (Nat.cast_nonneg _)
      simpa [Nat.cast_mul] using h1
    exact Nat.floor_le_of_le hmul
  have hceArg_le : inp.J.n + 4 * m0 * Task1Input.phiDenCap impl inp.J + 2 ≤ C_ceArg * x ^ k_ceArg := by
    have h1 : 4 * m0 * Task1Input.phiDenCap impl inp.J ≤ (4 * Cpd) * x ^ k_ceArg := by
      have ha : m0 * Task1Input.phiDenCap impl inp.J ≤ Cpd * x ^ (1 + kpd) := by
        simpa [pow_one] using spPoly_mul (show m0 ≤ 1 * x ^ 1 by simp only [pow_one]; omega) hpd_le
      have hb : 1 + kpd = k_ceArg := by omega
      rw [hb] at ha; nlinarith only [ha]
    have h2 : inp.J.n + 2 ≤ 2 * x ^ k_ceArg := by
      have : x ≤ x ^ k_ceArg := Nat.le_self_pow (by omega) x; omega
    dsimp only [C_ceArg]; rw [Nat.add_mul]; omega
  have hwM_le : m0 + 2 * ce.c_deg_int * m0 * Task1Input.phiDenCap impl inp.J ≤ C_wM * x ^ k_wM := by
    have h1 : m0 * Task1Input.phiDenCap impl inp.J ≤ Cpd * x ^ k_wM := by
      have ha := spPoly_mul (show m0 ≤ 1 * x ^ 1 by simp only [pow_one]; omega) hpd_le
      simpa [show 1 + kpd = k_wM by omega, one_mul] using ha
    have h2 : m0 ≤ x ^ k_wM := le_trans hm0_x (Nat.le_self_pow (by omega) x)
    have h3 : 2 * ce.c_deg_int * m0 * Task1Input.phiDenCap impl inp.J =
        (2 * ce.c_deg_int) * (m0 * Task1Input.phiDenCap impl inp.J) := by ring
    have h4 := Nat.mul_le_mul_left (2 * ce.c_deg_int) h1
    rw [h3]; dsimp only [C_wM]; nlinarith only [h2, h4]
  have ht1_heap : inp.maxHeapEnd impl ≤ inp.h + C_t1 * x ^ k_t1 := by
    unfold Task1Input.maxHeapEnd Task1Input.coreHMax Task1Input.prepHMax
      Task1Input.decAddr Task1Input.nlAddr Task1Input.j0Addr; dsimp only
    have hdec_sp : dec.space inp.J.n m0 ≤ (dec.C_space * 2 ^ dec.c_space) * x ^ k_t1 := by
      have h1 := dec.hspace_le inp.J.n m0
      have h2 : (inp.J.n + m0 + 2) ^ dec.c_space ≤ (2 * x) ^ dec.c_space :=
        Nat.pow_le_pow_left (by dsimp only [x, sparsifyInputSize]; omega) _
      rw [mul_pow] at h2
      have h3 : x ^ dec.c_space ≤ x ^ k_t1 := Nat.pow_le_pow_right hx1 (by omega)
      calc dec.space inp.J.n m0 ≤ dec.C_space * (2 ^ dec.c_space * x ^ dec.c_space) :=
            le_trans h1 (Nat.mul_le_mul_left _ h2)
        _ = (dec.C_space * 2 ^ dec.c_space) * x ^ dec.c_space := by ring
        _ ≤ (dec.C_space * 2 ^ dec.c_space) * x ^ k_t1 := Nat.mul_le_mul_left _ h3
    have hp1 : pds.C_space * (Task1Input.dJCap impl inp.J + m0 + 2) ^ pds.c_space ≤
        (pds.C_space * C_argJ ^ pds.c_space) * x ^ k_t1 := by
      have h1 := spPoly_pow (r := pds.c_space) hargJ_le
      have h2 : x ^ (kmw * pds.c_space) ≤ x ^ k_t1 := Nat.pow_le_pow_right hx1 (by omega)
      calc _ ≤ pds.C_space * (C_argJ ^ pds.c_space * x ^ (kmw * pds.c_space)) :=
            Nat.mul_le_mul_left _ h1
        _ = (pds.C_space * C_argJ ^ pds.c_space) * x ^ (kmw * pds.c_space) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ h2
    have hp2 : pds.C_space * (dW + Task1Input.mwCap impl inp.J + 2) ^ pds.c_space ≤
        (pds.C_space * C_argW ^ pds.c_space) * x ^ k_t1 := by
      have h1 := spPoly_pow (r := pds.c_space) hargW_le
      have h2 : x ^ (kmw * pds.c_space) ≤ x ^ k_t1 := Nat.pow_le_pow_right hx1 (by omega)
      calc _ ≤ pds.C_space * (C_argW ^ pds.c_space * x ^ (kmw * pds.c_space)) :=
            Nat.mul_le_mul_left _ h1
        _ = (pds.C_space * C_argW ^ pds.c_space) * x ^ (kmw * pds.c_space) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ h2
    have hce_sp : m0 * ce.C_space * (inp.J.n + 4 * m0 * Task1Input.phiDenCap impl inp.J + 2) ^ ce.c_space ≤
        (ce.C_space * C_ceArg ^ ce.c_space) * x ^ k_t1 := by
      have h1 := spPoly_pow (r := ce.c_space) hceArg_le
      have h2 := spPoly_mul (show m0 ≤ 1 * x ^ 1 by simp only [pow_one]; omega)
        (show ce.C_space * (inp.J.n + 4 * m0 * Task1Input.phiDenCap impl inp.J + 2) ^ ce.c_space ≤
          (ce.C_space * C_ceArg ^ ce.c_space) * x ^ (k_ceArg * ce.c_space) by
          calc _ ≤ ce.C_space * (C_ceArg ^ ce.c_space * x ^ (k_ceArg * ce.c_space)) :=
                Nat.mul_le_mul_left _ h1
            _ = _ := by ring)
      rw [Nat.mul_assoc]
      exact spPoly_le hx1 (by simpa [one_mul] using h2) le_rfl (by omega)
    have hx_t1 : x ≤ x ^ k_t1 := Nat.le_self_pow (by omega) x
    have hwM_t1 : 6 * (m0 + 2 * ce.c_deg_int * m0 * Task1Input.phiDenCap impl inp.J) ≤
        6 * C_wM * x ^ k_t1 := by
      rw [Nat.mul_assoc 6 C_wM]; exact Nat.mul_le_mul_left 6 (spPoly_le hx1 hwM_le le_rfl (by omega : k_wM ≤ k_t1))
    have hdL_t1 : Task1Input.dLMax impl inp.J ≤ C_dL * x ^ k_t1 :=
      spPoly_le hx1 (show Task1Input.dLMax impl inp.J ≤ C_dL * x ^ 1 by simp only [pow_one]; exact hdL_le)
        le_rfl (by omega : 1 ≤ k_t1)
    have hlin : 6 + 3 + inp.J.n + 2 * inp.H'.n + 2 + 2 * inp.J.m + m0 + 9 + 16 * m0 +
        2 * inp.J.n + 20 + 6 * m0 + 4 * m0 + 2 + 3 * inp.J.m ≤ 60 * x ^ k_t1 := by
      have : 6 + 3 + inp.J.n + 2 * inp.H'.n + 2 + 2 * inp.J.m + m0 + 9 + 16 * m0 +
          2 * inp.J.n + 20 + 6 * m0 + 4 * m0 + 2 + 3 * inp.J.m ≤ 60 * x := by omega
      exact le_trans this (Nat.mul_le_mul_left 60 hx_t1)
    have hsum : C_t1 * x ^ k_t1 = 60 * x ^ k_t1 + (dec.C_space * 2 ^ dec.c_space) * x ^ k_t1 +
        C_dL * x ^ k_t1 + (pds.C_space * C_argJ ^ pds.c_space) * x ^ k_t1 +
        (pds.C_space * C_argW ^ pds.c_space) * x ^ k_t1 +
        (ce.C_space * C_ceArg ^ ce.c_space) * x ^ k_t1 + 6 * C_wM * x ^ k_t1 := by
      dsimp only [C_t1]; ring
    change inp.h + 6 + 3 + inp.J.n + 2 * inp.H'.n + 2 + 2 * inp.J.m + m0 +
      dec.space inp.J.n m0 + 9 + Task1Input.dLMax impl inp.J + 16 * m0 + 2 * inp.J.n + 20 +
      pds.C_space * (Task1Input.dJCap impl inp.J + m0 + 2) ^ pds.c_space +
      pds.C_space * (dW + Task1Input.mwCap impl inp.J + 2) ^ pds.c_space +
      6 * m0 + 4 * m0 +
      m0 * ce.C_space * (inp.J.n + 4 * m0 * Task1Input.phiDenCap impl inp.J + 2) ^ ce.c_space +
      (2 + 6 * (m0 + 2 * ce.c_deg_int * m0 * Task1Input.phiDenCap impl inp.J) + 3 * inp.J.m) ≤ _
    linarith only [hdec_sp, hp1, hp2, hce_sp, hwM_t1, hdL_t1, hlin, hsum]
  have hdsJArg_le : Task1Input.phiDenCap impl inp.J + inp.J.n + m0 + m0 +
      pds.gExp (Task1Input.dJCap impl inp.J) m0 + 2 ≤ C_dsJArg * x ^ k_dsJArg := by
    have ha := spPoly_le hx1 hpd_le le_rfl (le_max_left kpd k_pds)
    have hb := spPoly_le hx1 hgEJ_le le_rfl (le_max_right kpd k_pds)
    have hc : inp.J.n + m0 + m0 + 2 ≤ 4 * x ^ k_dsJArg := by
      have : x ≤ x ^ k_dsJArg := Nat.le_self_pow (by omega) x; omega
    dsimp only [C_dsJArg]; nlinarith only [ha, hb, hc]
  have hdsJ_le : pds.C_space * (Task1Input.phiDenCap impl inp.J + inp.J.n + m0 + m0 +
      pds.gExp (Task1Input.dJCap impl inp.J) m0 + 2) ^ pds.c_space ≤ C_dsJ * x ^ k_dsJ := by
    have h1 := spPoly_pow (r := pds.c_space) hdsJArg_le
    calc _ ≤ pds.C_space * (C_dsJArg ^ pds.c_space * x ^ k_dsJ) := Nat.mul_le_mul_left _ h1
      _ = C_dsJ * x ^ k_dsJ := by dsimp only [C_dsJ]; ring
  have hCp1 : 1 ≤ C_pds := Nat.mul_pos (by omega) (Nat.pow_pos (by omega : 0 < max C_argJ C_argW))
  have ht2_heap : Task2Input.maxHeapEnd impl (inp.toT2 0) ≤ C_t2 * x ^ k_t2 := by
    unfold Task2Input.maxHeapEnd Task2Input.staticEndCap Task2Input.nodesAddr
      Task2Input.queueAddr Task2Input.eWVertStampAddr Task2Input.procStampAddr
      Task2Input.vcongNumAddr Task2Input.vHeadAddr Task2Input.vhatStampAddr
      Task2Input.compEdgeDelRoundAddr Task2Input.vhatOffsetAddr
      Task2Input.compEdgeBaseAddr Task2Input.dsHandlesAddr Task2Input.embWJAddr
    simp only [Task1Input.toT2]
    have hx_t2 : x ≤ x ^ k_t2 := Nat.le_self_pow (by omega) x
    have hlin : 32 + inp.J.m + inp.J.m + inp.J.m + inp.J.m + 2 * inp.J.m +
        inp.H'.n + inp.H'.n + inp.H'.n + inp.H'.n + inp.H'.n +
        3 * (inp.toT2 0).embVertSum ≤ 60 * x ^ k_t2 := by
      have : 32 + inp.J.m + inp.J.m + inp.J.m + inp.J.m + 2 * inp.J.m +
          inp.H'.n + inp.H'.n + inp.H'.n + inp.H'.n + inp.H'.n +
          3 * (inp.toT2 0).embVertSum ≤ 60 * x := by omega
      exact le_trans this (Nat.mul_le_mul_left 60 hx_t2)
    have hmw_t2 : Task1Input.mwCap impl inp.J * (2 * Task2Input.gammaExpCap impl inp.J + 5) ≤
        (6 * Cmw * C_pds + Cmw) * x ^ k_t2 := by
      have h2 := spPoly_le hx1 (spPoly_mul hmw_le hγE_le) le_rfl (by omega : kmw + k_pds ≤ k_t2)
      have h3 := spPoly_le hx1 hmw_le le_rfl (by omega : kmw ≤ k_t2)
      have h4 : Cmw * x ^ k_t2 ≤ Cmw * C_pds * x ^ k_t2 :=
        Nat.mul_le_mul_right _ (by simpa using Nat.mul_le_mul_left Cmw hCp1)
      nlinarith only [h2, h3, h4]
    have hmw1 := spPoly_le hx1 hmw_le le_rfl (by omega : kmw ≤ k_t2)
    have hds_sum : Task2Input.eta1Cap impl inp.J * inp.J.m *
          (pds.C_space * (Task1Input.phiDenCap impl inp.J + inp.J.n + m0 + m0 +
            pds.gExp (Task1Input.dJCap impl inp.J) m0 + 2) ^ pds.c_space) +
        Task2Input.eta1Cap impl inp.J * inp.J.m *
          (pds.C_space * (Task1Input.phiDenCap impl inp.J + inp.J.n + m0 + m0 +
            pds.gExp (Task1Input.dJCap impl inp.J) m0 + 2) ^ pds.c_space) +
        Task1Input.mwCap impl inp.J *
          (pds.C_space * (Task1Input.phiDenCap impl inp.J + inp.J.n + m0 + m0 +
            pds.gExp (Task1Input.dJCap impl inp.J) m0 + 2) ^ pds.c_space) ≤
        ((2 * C_η1 + Cmw) * C_dsJ) * x ^ k_t2 := by
      have ha : Task2Input.eta1Cap impl inp.J * inp.J.m ≤ C_η1 * x ^ (kmw + 1) := by
        simpa [mul_one] using spPoly_mul hη1_le (show inp.J.m ≤ 1 * x ^ 1 by simp only [pow_one]; omega)
      have hb := spPoly_le hx1 (spPoly_mul ha hdsJ_le) le_rfl (by omega : kmw + 1 + k_dsJ ≤ k_t2)
      have hc := spPoly_le hx1 (spPoly_mul hmw_le hdsJ_le) le_rfl (by omega : kmw + k_dsJ ≤ k_t2)
      have hEq : ((2 * C_η1 + Cmw) * C_dsJ) * x ^ k_t2 =
          2 * ((C_η1 * C_dsJ) * x ^ k_t2) + (Cmw * C_dsJ) * x ^ k_t2 := by ring
      linarith only [hb, hc, hEq]
    have hsum : C_t2 * x ^ k_t2 = 60 * x ^ k_t2 + 2 * Cmw * x ^ k_t2 +
        6 * Cmw * C_pds * x ^ k_t2 + ((2 * C_η1 + Cmw) * C_dsJ) * x ^ k_t2 := by
      dsimp only [C_t2]; ring
    change 0 + 32 + Task1Input.mwCap impl inp.J + inp.J.m + inp.J.m + inp.J.m + inp.J.m +
      2 * inp.J.m + inp.H'.n + inp.H'.n + inp.H'.n + inp.H'.n + inp.H'.n +
      3 * (inp.toT2 0).embVertSum +
      Task1Input.mwCap impl inp.J * (2 * Task2Input.gammaExpCap impl inp.J + 5) +
      Task2Input.eta1Cap impl inp.J * inp.J.m *
        (pds.C_space * (Task1Input.phiDenCap impl inp.J + inp.J.n + m0 + m0 +
          pds.gExp (Task1Input.dJCap impl inp.J) m0 + 2) ^ pds.c_space) +
      Task2Input.eta1Cap impl inp.J * inp.J.m *
        (pds.C_space * (Task1Input.phiDenCap impl inp.J + inp.J.n + m0 + m0 +
          pds.gExp (Task1Input.dJCap impl inp.J) m0 + 2) ^ pds.c_space) +
      Task1Input.mwCap impl inp.J *
        (pds.C_space * (Task1Input.phiDenCap impl inp.J + inp.J.n + m0 + m0 +
          pds.gExp (Task1Input.dJCap impl inp.J) m0 + 2) ^ pds.c_space) ≤ _
    linarith only [hlin, hmw_t2, hmw1, hds_sum, hsum]
  have hdsWArg_le : ce.phiDen + 4 * Task1Input.mwCap impl inp.J +
      pds.gExp dW (Task1Input.mwCap impl inp.J) + 2 ≤ C_dsWArg * x ^ k_dsWArg := by
    have ha := spPoly_le hx1 hmw_le le_rfl (le_max_left kmw k_pds)
    have hb := spPoly_le hx1 hgEW_le le_rfl (le_max_right kmw k_pds)
    have hc := h1_pow k_dsWArg
    dsimp only [C_dsWArg]; nlinarith only [ha, hb, hc]
  have hdsW_le : Task3Input.dsOneW impl inp.J ≤ C_dsW * x ^ k_dsW := by
    unfold Task3Input.dsOneW; dsimp only
    have h1 := spPoly_pow (r := pds.c_space) hdsWArg_le
    calc _ ≤ pds.C_space * (C_dsWArg ^ pds.c_space * x ^ k_dsW) := Nat.mul_le_mul_left _ h1
      _ = C_dsW * x ^ k_dsW := by dsimp only [C_dsW]; ring
  have ht3_heap : Task3Input.maxHeapEnd impl (inp.toT3 0) ≤ C_t3 * x ^ k_t3 := by
    unfold Task3Input.maxHeapEnd Task3Input.staticEndCap t3HdrSize
    simp only [Task1Input.toT3]
    have hx_t3 : x ≤ x ^ k_t3 := Nat.le_self_pow (by omega) x
    have hlin : 32 + 5 * inp.J.m + 5 * inp.J.m + 3 * inp.J.m ≤ 60 * x ^ k_t3 := by
      have : 32 + 5 * inp.J.m + 5 * inp.J.m + 3 * inp.J.m ≤ 60 * x := by omega
      exact le_trans this (Nat.mul_le_mul_left 60 hx_t3)
    have hmw_t3 : 3 * Task1Input.mwCap impl inp.J ≤ 3 * Cmw * x ^ k_t3 := by
      rw [Nat.mul_assoc 3 Cmw]; exact Nat.mul_le_mul_left 3 (spPoly_le hx1 hmw_le le_rfl (by omega : kmw ≤ k_t3))
    have hcoef : eta2Bound inp.J * inp.J.m + inp.J.m +
        inp.J.m * pds.gExp dW (Task1Input.mwCap impl inp.J) ≤ (5 + C_pds) * x ^ (2 + k_pds) := by
      have ha : eta2Bound inp.J * inp.J.m ≤ 3 * x ^ 2 := by
        simpa using spPoly_mul (show eta2Bound inp.J ≤ 3 * x ^ 1 by simp only [pow_one]; omega) (show inp.J.m ≤ 1 * x ^ 1 by simp only [pow_one]; omega)
      have ha' := spPoly_le hx1 ha le_rfl (by omega : 2 ≤ 2 + k_pds)
      have hb : inp.J.m ≤ x ^ (2 + k_pds) := le_trans hJm_x (Nat.le_self_pow (by omega) x)
      have hc : inp.J.m * pds.gExp dW (Task1Input.mwCap impl inp.J) ≤ C_pds * x ^ (2 + k_pds) := by
        have := spPoly_mul (show inp.J.m ≤ 1 * x ^ 1 by simp only [pow_one]; omega) hgEW_le
        exact spPoly_le hx1 (by simpa [one_mul] using this) le_rfl (by omega)
      nlinarith only [ha', hb, hc]
    have hds_t3 := spPoly_le hx1 (spPoly_mul hcoef hdsW_le) le_rfl (by omega : 2 + k_pds + k_dsW ≤ k_t3)
    have hwalk_t3 : inp.J.m * (2 * pds.gExp dW (Task1Input.mwCap impl inp.J) + 3) ≤
        5 * C_pds * x ^ k_t3 := by
      have h1 : inp.J.m * pds.gExp dW (Task1Input.mwCap impl inp.J) ≤ C_pds * x ^ k_t3 := by
        have := spPoly_mul (show inp.J.m ≤ 1 * x ^ 1 by simp only [pow_one]; omega) hgEW_le
        exact spPoly_le hx1 (by simpa [one_mul] using this) le_rfl (by omega)
      have h2 : inp.J.m ≤ C_pds * x ^ k_t3 := le_trans (le_trans hJm_x hx_t3) (Nat.le_mul_of_pos_left _ hCp1)
      nlinarith only [h1, h2]
    have hsum : C_t3 * x ^ k_t3 = 60 * x ^ k_t3 + 3 * Cmw * x ^ k_t3 +
        ((5 + C_pds) * C_dsW) * x ^ k_t3 + 5 * C_pds * x ^ k_t3 := by
      dsimp only [C_t3]; ring
    change 0 + 32 + 5 * inp.J.m + 3 * Task1Input.mwCap impl inp.J + 5 * inp.J.m +
      (eta2Bound inp.J * inp.J.m + inp.J.m +
        inp.J.m * pds.gExp dW (Task1Input.mwCap impl inp.J)) * Task3Input.dsOneW impl inp.J +
      inp.J.m * (2 * pds.gExp dW (Task1Input.mwCap impl inp.J) + 3) ≤ _
    linarith only [hlin, hmw_t3, hds_t3, hwalk_t3, hsum]
  have hout_heap : sparsifyOutSpace (Task1Input.mwCap impl inp.J) inp.J.m
      (Task2Input.gammaExpCap impl inp.J) ≤ C_out * x ^ k_out := by
    unfold sparsifyOutSpace; dsimp only
    have hx_out : x ≤ x ^ k_out := Nat.le_self_pow (by omega) x
    have hmwγ := spPoly_le hx1 (spPoly_mul hmw_le hγE_le) le_rfl (by omega : kmw + k_pds ≤ k_out)
    have hmw_o : Task1Input.mwCap impl inp.J ≤ (Cmw * C_pds) * x ^ k_out :=
      le_trans (spPoly_le hx1 hmw_le le_rfl (by omega)) (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hCp1))
    have hγsq : Task2Input.gammaExpCap impl inp.J * Task2Input.gammaExpCap impl inp.J ≤
        C_pds ^ 2 * x ^ (2 * k_pds) := by
      simpa [sq, two_mul] using spPoly_mul hγE_le hγE_le
    have hγsq_out : Task2Input.gammaExpCap impl inp.J * Task2Input.gammaExpCap impl inp.J ≤
        C_pds ^ 2 * x ^ k_out := spPoly_le hx1 hγsq le_rfl (by omega)
    have hγ_out : Task2Input.gammaExpCap impl inp.J ≤ C_pds * x ^ k_out :=
      spPoly_le hx1 hγE_le le_rfl (by omega)
    have hmγsq : inp.J.m * (Task2Input.gammaExpCap impl inp.J * Task2Input.gammaExpCap impl inp.J) ≤
        C_pds ^ 2 * x ^ k_out := by
      have := spPoly_mul (show inp.J.m ≤ 1 * x ^ 1 by simp only [pow_one]; omega) hγsq
      exact spPoly_le hx1 (by simpa [one_mul] using this) le_rfl (by omega)
    have hmγ : inp.J.m * Task2Input.gammaExpCap impl inp.J ≤ C_pds * x ^ k_out := by
      have := spPoly_mul (show inp.J.m ≤ 1 * x ^ 1 by simp only [pow_one]; omega) hγE_le
      exact spPoly_le hx1 (by simpa [one_mul] using this) le_rfl (by omega)
    have hsum : C_out * x ^ k_out = 20 * x ^ k_out + 9 * (Cmw * C_pds) * x ^ k_out +
        8 * C_pds ^ 2 * x ^ k_out + 14 * C_pds * x ^ k_out := by
      dsimp only [C_out]; ring
    have hlin : 6 + 7 * inp.J.m ≤ 20 * x ^ k_out := by omega
    have hrew : 3 + 3 * (Task1Input.mwCap impl inp.J * Task2Input.gammaExpCap impl inp.J) + 4 * inp.J.m +
        Task1Input.mwCap impl inp.J +
        Task1Input.mwCap impl inp.J * (2 * Task2Input.gammaExpCap impl inp.J + 3) +
        (2 * Task2Input.gammaExpCap impl inp.J + 3) +
        2 * (Task2Input.gammaExpCap impl inp.J * (2 * Task2Input.gammaExpCap impl inp.J + 3)) +
        inp.J.m +
        inp.J.m * (2 + 2 * (Task2Input.gammaExpCap impl inp.J * (2 * Task2Input.gammaExpCap impl inp.J + 3))) =
        (6 + 7 * inp.J.m) + 4 * Task1Input.mwCap impl inp.J +
        5 * (Task1Input.mwCap impl inp.J * Task2Input.gammaExpCap impl inp.J) +
        8 * Task2Input.gammaExpCap impl inp.J +
        4 * (Task2Input.gammaExpCap impl inp.J * Task2Input.gammaExpCap impl inp.J) +
        4 * (inp.J.m * (Task2Input.gammaExpCap impl inp.J * Task2Input.gammaExpCap impl inp.J)) +
        6 * (inp.J.m * Task2Input.gammaExpCap impl inp.J) := by ring
    rw [hrew]; nlinarith only [hmwγ, hmw_o, hγsq_out, hγ_out, hmγsq, hmγ, hsum, hlin]
  have hsp_heap : sparsifyMaxHeapEnd impl inp ≤ inp.h + C_sp * x ^ c_sp := by
    unfold sparsifyMaxHeapEnd
    have h1 : C_t1 * x ^ k_t1 ≤ C_t1 * x ^ c_sp :=
      Nat.mul_le_mul_left C_t1 (Nat.pow_le_pow_right hx1 (le_trans (le_max_left k_t1 k_t2) (le_max_left (max k_t1 k_t2) (max k_t3 k_out))))
    have h2 : C_t2 * x ^ k_t2 ≤ C_t2 * x ^ c_sp :=
      Nat.mul_le_mul_left C_t2 (Nat.pow_le_pow_right hx1 (le_trans (le_max_right k_t1 k_t2) (le_max_left (max k_t1 k_t2) (max k_t3 k_out))))
    have h3 : C_t3 * x ^ k_t3 ≤ C_t3 * x ^ c_sp :=
      Nat.mul_le_mul_left C_t3 (Nat.pow_le_pow_right hx1 (le_trans (le_max_left k_t3 k_out) (le_max_right (max k_t1 k_t2) (max k_t3 k_out))))
    have h4 : C_out * x ^ k_out ≤ C_out * x ^ c_sp :=
      Nat.mul_le_mul_left C_out (Nat.pow_le_pow_right hx1 (le_trans (le_max_right k_t3 k_out) (le_max_right (max k_t1 k_t2) (max k_t3 k_out))))
    have hsum : C_sp * x ^ c_sp = C_t1 * x ^ c_sp + C_t2 * x ^ c_sp +
        C_t3 * x ^ c_sp + C_out * x ^ c_sp + x ^ c_sp := by
      dsimp only [C_sp]; ring
    linarith only [ht1_heap, ht2_heap, ht3_heap, hout_heap, h1, h2, h3, h4, hsum, h1_pow c_sp]
  have ht1_sp : inp.maxHeapEnd impl ≤ inp.h + C_sp * x ^ c_sp := by
    have h0 : inp.maxHeapEnd impl ≤ sparsifyMaxHeapEnd impl inp := by
      unfold sparsifyMaxHeapEnd; omega
    exact le_trans h0 hsp_heap
  exact ⟨hpd_le, hmw_le, hargJ_le, hargW_le, hgEJ_le, hgEW_le, hpds_J.2, hpds_W.2,
    hγE_le, htau2_le, hη1_le, hceArg_le, hdsJArg_le, hdsWArg_le, ht1_sp, hsp_heap⟩

end MinCostFlow.Spanner
