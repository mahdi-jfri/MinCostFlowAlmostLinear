module

public import MinCostFlow.Spanner.ProgSparsify
public import MinCostFlow.Spanner.Theorem81

@[expose] public section

/-!
# Runtime Bound of Word-RAM `Sparsify` Against `sparsifyCost` / Theorem 8.1

Bounds `sparsifyTotalCost impl inp mem` (the contract cost of `sparsifyBody` / `sparsifyModule`)
against the Theorem 8.1 runtime formula (`RuntimeBase.lean`, `Runtime.lean`, `Theorem81.lean`),
using `gQuery` for `Delete` and `GetPath` and `gExp` for path lengths, up to an explicit
implementation-dependent constant `sparsifyProgConst impl`.

The main results are:
- `sparsifyTotalCost_le_cap_with_time`: bounds `sparsifyTotalCost` by
  `costs.decompose.callCost (stripLoops J).m + sparsifyProgConst impl * γ_t * (J.n + J.m * γ_ℓ^2 * length) * (1 + log (J.n + J.m + 2))`.
- `sparsifyTotalCost_le_cap_of_dec_le_with_time`: absorbs `Decompose` when
  `impl.decompose.decFactor M ≤ C_dec * γ_ℓ ^ 2`.
-/

namespace MinCostFlow.Spanner

open WordRAM Cited

/-! ### Explicit constant factor for the Word-RAM `Sparsify` program -/

/-- Explicit constant factor bounding all non-`Decompose` work of `sparsifyTotalCost impl inp mem`
relative to `γ_t * (J.n + J.m * γ_ℓ ^ 2 * length J embJH) * (1 + log (J.n + J.m + 2))`. -/
noncomputable def sparsifyProgConst (impl : SpannerToolImpl) : ℝ :=
  let c_deg : ℝ := 2 * (impl.constructExpander.c_deg_int : ℝ)
  let pds := impl.pathDS.params
  let C_η1 : ℝ := 1 + (2 * c_deg + 1) * (c_deg + 1) / Real.log 2
  let C_η2 : ℝ := 1 + 2 / Real.log 2
  let C_t1 : ℝ := 4000 + impl.decompose.K_dec + 5 * impl.constructExpander.K_ce +
    150 * (c_deg + 1) + (pds.K_bounds : ℝ) * (c_deg + 5) / Real.log 2
  let C_t2 : ℝ := C_η1 * (pds.K_init + pds.K_del + 100 * (c_deg + 1) + 820) +
    (c_deg + 1) * (pds.K_query + 1005) + 1300
  let C_t3 : ℝ := C_η2 * ((c_deg + 1) * (pds.K_init + 85) + 705) +
    pds.K_query + pds.K_del + 1510
  let C_out : ℝ := (c_deg + 1) * 500 + 2500
  C_t1 + C_t2 + C_t3 + C_out

lemma sparsifyProgConst_pos (impl : SpannerToolImpl) : 0 < sparsifyProgConst impl := by
  unfold sparsifyProgConst; dsimp only
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : 0 ≤ (2 * (impl.constructExpander.c_deg_int : ℝ)) := by positivity
  have h2 := impl.decompose.hK_dec
  have h3 := impl.constructExpander.hK_ce
  have h4 := impl.pathDS.params.hK_init
  have h5 := impl.pathDS.params.hK_del
  have h6 := impl.pathDS.params.hK_query
  have h7 : 0 ≤ (impl.pathDS.params.K_bounds : ℝ) := Nat.cast_nonneg _
  positivity

/-! ### Helper bounds comparing Word-RAM caps to `Runtime.lean` caps -/

private lemma nat_ceil_le_add_one (x : ℝ) (hx : 0 ≤ x) : (Nat.ceil x : ℝ) ≤ x + 1 := by
  have := Nat.ceil_lt_add_one hx; linarith

private lemma log2_prod_le {x A : ℝ} {n : ℕ} (hA : 1 ≤ A) (hx : 2 ≤ x)
    (hn : (n : ℝ) ≤ A * x) :
    (Nat.log 2 n : ℝ) + 1 ≤ (A / Real.log 2) * (1 + Real.log x) := by
  have hAx : 1 ≤ A * x := by nlinarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2_le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have h1 : (Nat.log 2 n : ℝ) + 1 ≤ (1 / Real.log 2) * (1 + Real.log (A * x)) := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp only [Nat.log_zero_right, Nat.cast_zero, zero_add]
      have hlog_nn : 0 ≤ Real.log (A * x) := Real.log_nonneg hAx
      rw [one_div_mul_eq_div, le_div_iff₀ hl2]; linarith
    · have hpow : (2 : ℝ) ^ (Nat.log 2 n) ≤ (n : ℝ) := by
        exact_mod_cast Nat.pow_log_le_self 2 (by omega)
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast hpos
      have hlog : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log (A * x) := by
        calc (Nat.log 2 n : ℝ) * Real.log 2
            = Real.log ((2 : ℝ) ^ (Nat.log 2 n)) := (Real.log_pow 2 (Nat.log 2 n)).symm
          _ ≤ Real.log (n : ℝ) := Real.log_le_log (by positivity) hpow
          _ ≤ Real.log (A * x) := Real.log_le_log hn_pos hn
      have ha : (Nat.log 2 n : ℝ) ≤ Real.log (A * x) / Real.log 2 := (le_div_iff₀ hl2).mpr hlog
      have hb : (1 : ℝ) ≤ 1 / Real.log 2 := (one_le_div hl2).mpr hl2_le
      calc (Nat.log 2 n : ℝ) + 1 ≤ Real.log (A * x) / Real.log 2 + 1 / Real.log 2 := by linarith
        _ = (1 / Real.log 2) * (1 + Real.log (A * x)) := by ring
  have hlogA : Real.log A ≤ A - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hmul : Real.log (A * x) = Real.log A + Real.log x :=
    Real.log_mul (by linarith) (by linarith)
  have hsum : 1 + Real.log (A * x) ≤ A * (1 + Real.log x) := by
    rw [hmul]; nlinarith
  calc (Nat.log 2 n : ℝ) + 1
      ≤ (1 / Real.log 2) * (1 + Real.log (A * x)) := h1
    _ ≤ (1 / Real.log 2) * (A * (1 + Real.log x)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (A / Real.log 2) * (1 + Real.log x) := by ring

private lemma embVertSum_le {H' J : Graph} {embJH : ℕ → Walk}
    (hEmb : IsEmbedding J H' embJH) (hLen : 1 ≤ J.m → 1 ≤ length J embJH) :
    ∑ e ∈ Finset.range J.m, (embJH e).verts.length ≤ 2 * J.m * length J embJH := by
  rcases Nat.eq_zero_or_pos J.m with hm0 | hmpos
  · simp [hm0]
  · have hl1 : 1 ≤ length J embJH := hLen hmpos
    calc ∑ e ∈ Finset.range J.m, (embJH e).verts.length
        ≤ ∑ _e ∈ Finset.range J.m, (2 * length J embJH) := by
          refine Finset.sum_le_sum fun e he => ?_
          have h1 := walk_verts_length_le_edges_succ (hEmb.2 e (Finset.mem_range.mp he))
          have h2 := edges_length_le_length embJH (Finset.mem_range.mp he)
          omega
      _ = J.m * (2 * length J embJH) := by simp
      _ = 2 * J.m * length J embJH := by ring

private lemma cap_quantities_le (impl : SpannerToolImpl) (J : Graph) {M : ℕ}
    (hJm : J.m ≤ M) :
    let tools := spannerTools_of_impl impl
    let ce := impl.constructExpander
    let pds := impl.pathDS.params
    let c_deg : ℝ := 2 * (ce.c_deg_int : ℝ)
    let φ_min := impl.decompose.φ_lb M
    let m0 := (stripLoops J).m
    let dJ := Task1Input.dJCap impl J
    let mw := Task1Input.mwCap impl J
    let dW := WitnessCoreInput.dWInt ce
    let γ_E := capGammaExpPath c_deg ce.φ_Const tools.pathDS φ_min M
    let γ_Q := capGammaQuery c_deg ce.φ_Const tools.pathDS φ_min M
    2 ≤ γ_E ∧
    (dJ : ℝ) ≤ γ_E ∧
    (dW : ℝ) ≤ γ_E ∧
    (pds.gExp dJ m0 : ℝ) ≤ γ_E ∧
    (pds.gExp dW mw : ℝ) ≤ γ_E ∧
    (pds.gQuery dJ m0 : ℝ) ≤ γ_Q ∧
    (pds.gQuery dW mw : ℝ) ≤ γ_Q ∧
    (Task2Input.gammaExpCap impl J : ℝ) ≤ γ_E ∧
    1 / impl.decompose.φ_lb m0 ≤ γ_E ∧
    mw ≤ capM_W c_deg φ_min M := by
  intro tools ce pds c_deg φ_min m0 dJ mw dW γ_E γ_Q
  have hφm_pos : 0 < φ_min := impl.decompose.hφ_lb_pos M
  have hφC_pos : 0 < ce.φ_Const := ce.hφ_Const_pos
  have hm0_le : m0 ≤ M := le_trans (stripLoops_m_le J) hJm
  have hφ_mono : φ_min ≤ impl.decompose.φ_lb m0 := impl.decompose.hφ_lb_anti hm0_le
  have hφ0_pos : 0 < impl.decompose.φ_lb m0 := impl.decompose.hφ_lb_pos m0
  have hdJ_ge1 : 1 ≤ dJ := Nat.one_le_ceil_iff.mpr (div_pos one_pos hφ0_pos)
  have hdW_ge1 : 1 ≤ dW := by
    dsimp only [dW]; rw [WitnessCoreInput.dWInt_eq]; exact Nat.one_le_ceil_iff.mpr (div_pos one_pos hφC_pos)
  have hdJ_le_M : dJ ≤ Nat.ceil (1 / φ_min) :=
    Nat.ceil_mono (one_div_le_one_div_of_le hφm_pos hφ_mono)
  have hmw_le_cap : mw ≤ capM_W c_deg φ_min M := by
    unfold mw Task1Input.mwCap capM_W
    have hc : 0 ≤ c_deg := by positivity
    have hm_r : (m0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hm0_le
    have hdiv : c_deg * (m0 : ℝ) / impl.decompose.φ_lb m0 ≤ c_deg * (M : ℝ) / φ_min :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hm_r hc) hφm_pos hφ_mono
    exact Nat.add_le_add_right (Nat.ceil_mono hdiv) 1
  have hφm_r : 0 < roundPhi φ_min := roundPhi_pos hφm_pos
  have hφC_r : 0 < roundPhi ce.φ_Const := roundPhi_pos hφC_pos
  have hdJ_le_r : dJ ≤ Nat.ceil (1 / roundPhi φ_min) :=
    le_trans hdJ_le_M (Nat.ceil_mono (one_div_le_one_div_of_le hφm_r (roundPhi_le hφm_pos)))
  have hdW_le_r : dW ≤ Nat.ceil (1 / roundPhi ce.φ_Const) := by
    dsimp only [dW]; rw [WitnessCoreInput.dWInt_eq]
    exact Nat.ceil_mono (one_div_le_one_div_of_le hφC_r (roundPhi_le hφC_pos))
  have hgEJ : (pds.gExp dJ m0 : ℝ) ≤ γ_E := by
    have h1 : pds.gExp dJ m0 ≤ pds.gExp (Nat.ceil (1 / roundPhi φ_min)) M :=
      pds.hgExp_mono hdJ_ge1 hdJ_le_r hm0_le
    have h2 : (pds.gExp (Nat.ceil (1 / roundPhi φ_min)) M : ℝ) = tools.pathDS.γ_ExpPath φ_min M := by
      simp [tools, spannerTools_of_impl, pathDSTool_of_impl, PathDSParams.γ_ExpPath, pds]
    have hmax : tools.pathDS.γ_ExpPath φ_min M ≤ γ_E := le_max_left _ _
    rw [← h2] at hmax
    exact le_trans (Nat.cast_le.mpr h1) hmax
  have hgEW : (pds.gExp dW mw : ℝ) ≤ γ_E := by
    have h1 : pds.gExp dW mw ≤ pds.gExp (Nat.ceil (1 / roundPhi ce.φ_Const)) (capM_W c_deg φ_min M) :=
      pds.hgExp_mono hdW_ge1 hdW_le_r hmw_le_cap
    have h2 : (pds.gExp (Nat.ceil (1 / roundPhi ce.φ_Const)) (capM_W c_deg φ_min M) : ℝ) =
        tools.pathDS.γ_ExpPath ce.φ_Const (capM_W c_deg φ_min M) := by
      simp [tools, spannerTools_of_impl, pathDSTool_of_impl, PathDSParams.γ_ExpPath, pds]
    have hmax : tools.pathDS.γ_ExpPath ce.φ_Const (capM_W c_deg φ_min M) ≤ γ_E := le_max_right _ _
    rw [← h2] at hmax
    exact le_trans (Nat.cast_le.mpr h1) hmax
  have hgQJ : (pds.gQuery dJ m0 : ℝ) ≤ γ_Q := by
    have h1 : pds.gQuery dJ m0 ≤ pds.gQuery (Nat.ceil (1 / roundPhi φ_min)) M :=
      pds.hgQuery_mono hdJ_ge1 hdJ_le_r hm0_le
    have h2 : (pds.gQuery (Nat.ceil (1 / roundPhi φ_min)) M : ℝ) = tools.pathDS.γ_query φ_min M := by
      simp [tools, spannerTools_of_impl, pathDSTool_of_impl, PathDSParams.γ_query, pds]
    have hmax : tools.pathDS.γ_query φ_min M ≤ γ_Q := le_max_left _ _
    rw [← h2] at hmax
    exact le_trans (Nat.cast_le.mpr h1) hmax
  have hgQW : (pds.gQuery dW mw : ℝ) ≤ γ_Q := by
    have h1 : pds.gQuery dW mw ≤ pds.gQuery (Nat.ceil (1 / roundPhi ce.φ_Const)) (capM_W c_deg φ_min M) :=
      pds.hgQuery_mono hdW_ge1 hdW_le_r hmw_le_cap
    have h2 : (pds.gQuery (Nat.ceil (1 / roundPhi ce.φ_Const)) (capM_W c_deg φ_min M) : ℝ) =
        tools.pathDS.γ_query ce.φ_Const (capM_W c_deg φ_min M) := by
      simp [tools, spannerTools_of_impl, pathDSTool_of_impl, PathDSParams.γ_query, pds]
    have hmax : tools.pathDS.γ_query ce.φ_Const (capM_W c_deg φ_min M) ≤ γ_Q := le_max_right _ _
    rw [← h2] at hmax
    exact le_trans (Nat.cast_le.mpr h1) hmax
  have hdJ_le_gE : (dJ : ℝ) ≤ γ_E := by
    have h1 : dJ ≤ pds.gExp dJ m0 :=
      le_trans (le_trans (le_max_right 2 dJ) (pds.hphiOutDen_ge dJ m0 hdJ_ge1)) (pds.hgExp_ge dJ m0 hdJ_ge1)
    exact le_trans (by exact_mod_cast h1) hgEJ
  have hdW_le_gE : (dW : ℝ) ≤ γ_E := by
    have h1 : dW ≤ pds.gExp dW mw :=
      le_trans (le_trans (le_max_right 2 dW) (pds.hphiOutDen_ge dW mw hdW_ge1)) (pds.hgExp_ge dW mw hdW_ge1)
    exact le_trans (by exact_mod_cast h1) hgEW
  have hγE_ge2 : 2 ≤ γ_E := two_le_capGammaExpPath hφC_pos hφm_pos M
  have hγCap_le : (Task2Input.gammaExpCap impl J : ℝ) ≤ γ_E := by
    unfold Task2Input.gammaExpCap; push_cast; exact max_le hgEJ hgEW
  have hinv_le : 1 / impl.decompose.φ_lb m0 ≤ γ_E := le_trans (Nat.le_ceil _) hdJ_le_gE
  exact ⟨hγE_ge2, hdJ_le_gE, hdW_le_gE, hgEJ, hgEW, hgQJ, hgQW, hγCap_le, hinv_le, hmw_le_cap⟩

/-! ### Main Word-RAM cost bound against `sparsifyCost` / Theorem 8.1 -/

/-- Bounds `sparsifyTotalCost impl inp mem` against the Theorem 8.1 / `sparsifyCost` runtime
bound at edge cap `M` (`1 ≤ J.m ≤ M`, `1 ≤ length J embJH`), using `gQuery` for `Delete` and
`GetPath` and `gExp` for path length. -/
theorem sparsifyTotalCost_le_cap_with_time (impl : SpannerToolImpl) (inp : Task1Input)
    (mem : ℕ → ℕ) (M : ℕ) (γ_t : ℝ)
    (hEmb : IsEmbedding inp.J inp.H' inp.embJH)
    (hgJ : GraphAt mem inp.jAddr inp.J)
    (hEA : EmbAt mem inp.embJHAddr inp.J.m inp.embJH)
    (hJm : inp.J.m ≤ M) (hJm_pos : 1 ≤ inp.J.m) (hLen : 1 ≤ length inp.J inp.embJH)
    (hγt : 1 ≤ γ_t)
    (hγq : let tools := spannerTools_of_impl impl
      let ce := impl.constructExpander
      let φ_min := impl.decompose.φ_lb M
      capGammaQuery (2 * (ce.c_deg_int : ℝ)) ce.φ_Const tools.pathDS φ_min M ≤
        γ_t * capGammaExpPath (2 * (ce.c_deg_int : ℝ)) ce.φ_Const tools.pathDS φ_min M) :
    let tools := spannerTools_of_impl impl
    let costs := spannerToolCosts_of_impl impl
    let ce := impl.constructExpander
    let φ_min := impl.decompose.φ_lb M
    let γ_ℓ := capGammaL (2 * (ce.c_deg_int : ℝ)) ce.φ_Const tools.pathDS φ_min M
    (sparsifyTotalCost impl inp mem : ℝ) ≤
      (costs.decompose.callCost (stripLoops inp.J).m : ℝ) +
      sparsifyProgConst impl * γ_t *
        ((inp.J.n : ℝ) + (inp.J.m : ℝ) * γ_ℓ ^ 2 * (length inp.J inp.embJH : ℝ)) *
        (1 + Real.log ((inp.J.n : ℝ) + (inp.J.m : ℝ) + 2)) := by
  intro tools costs ce φ_min γ_ℓ
  set pds := impl.pathDS.params
  set c_deg : ℝ := 2 * (ce.c_deg_int : ℝ)
  set m := inp.J.m
  set m0 := (stripLoops inp.J).m
  set l := length inp.J inp.embJH
  set dJ := Task1Input.dJCap impl inp.J
  set mw := Task1Input.mwCap impl inp.J
  set dW := WitnessCoreInput.dWInt ce
  set γ_E := capGammaExpPath c_deg ce.φ_Const tools.pathDS φ_min M
  set γ_Q := capGammaQuery c_deg ce.φ_Const tools.pathDS φ_min M
  set L_log := 1 + Real.log ((inp.J.n : ℝ) + (m : ℝ) + 2)
  set B := ((inp.J.n : ℝ) + (m : ℝ) * γ_ℓ ^ 2 * (l : ℝ)) * L_log
  have hcaps := cap_quantities_le impl inp.J hJm
  have hγE2 : 2 ≤ γ_E := hcaps.1
  have hdJ_E : (dJ : ℝ) ≤ γ_E := hcaps.2.1
  have hdW_E : (dW : ℝ) ≤ γ_E := hcaps.2.2.1
  have hgEJ : (pds.gExp dJ m0 : ℝ) ≤ γ_E := hcaps.2.2.2.1
  have hgEW : (pds.gExp dW mw : ℝ) ≤ γ_E := hcaps.2.2.2.2.1
  have hgQJ : (pds.gQuery dJ m0 : ℝ) ≤ γ_Q := hcaps.2.2.2.2.2.1
  have hgQW : (pds.gQuery dW mw : ℝ) ≤ γ_Q := hcaps.2.2.2.2.2.2.1
  have hγCap_E : (Task2Input.gammaExpCap impl inp.J : ℝ) ≤ γ_E := hcaps.2.2.2.2.2.2.2.1
  have hinv_E : 1 / impl.decompose.φ_lb m0 ≤ γ_E := hcaps.2.2.2.2.2.2.2.2.1
  have hm_ge1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hJm_pos
  have hl_ge1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hLen
  have hm0_le : (m0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast stripLoops_m_le inp.J
  have hcdeg_ge2 : 2 ≤ c_deg := by
    have := ce.hc_deg_int; dsimp only [c_deg]; exact_mod_cast (by omega : 2 ≤ 2 * ce.c_deg_int)
  have hL1 : 1 ≤ L_log := one_le_one_add_log inp.J.n m
  have hγℓ_eq : γ_ℓ = γ_E ^ 2 := rfl
  have hγE4 : γ_E ^ 4 = γ_ℓ ^ 2 := by rw [hγℓ_eq]; ring
  have hγE_nn : 0 ≤ γ_E := by linarith
  have hγE_ge1 : 1 ≤ γ_E := by linarith
  have hγE_sq : γ_E ≤ γ_E ^ 2 := by rw [sq]; exact le_mul_of_one_le_right hγE_nn hγE_ge1
  have hγE_1_2 : 1 ≤ γ_E ^ 2 := le_trans hγE_ge1 hγE_sq
  have hγE_2_4 : γ_E ^ 2 ≤ γ_E ^ 4 := by
    have : γ_E ^ 4 = γ_E ^ 2 * γ_E ^ 2 := by ring
    rw [this]; exact le_mul_of_one_le_right (sq_nonneg _) hγE_1_2
  have hγE_1_4 : 1 ≤ γ_E ^ 4 := le_trans hγE_1_2 hγE_2_4
  have hγE_E_4 : γ_E ≤ γ_E ^ 4 := le_trans hγE_sq hγE_2_4
  have hB_ge_m : (m : ℝ) * γ_E ^ 4 * (l : ℝ) * L_log ≤ B := by
    dsimp only [B]; rw [hγE4]
    have h1 : (m : ℝ) * γ_ℓ ^ 2 * (l : ℝ) ≤ (inp.J.n : ℝ) + (m : ℝ) * γ_ℓ ^ 2 * (l : ℝ) :=
      le_add_of_nonneg_left (Nat.cast_nonneg _)
    exact mul_le_mul_of_nonneg_right h1 (by linarith)
  have hB_ge : ∀ a b : ℝ, 0 ≤ a → a ≤ γ_E ^ 4 → 0 ≤ b → b ≤ (l : ℝ) →
      (m : ℝ) * a * b * L_log ≤ B := fun a b _ ha _ hb => by
    have h1 : (m : ℝ) * a ≤ (m : ℝ) * γ_E ^ 4 := mul_le_mul_of_nonneg_left ha (by positivity)
    have h2 : (m : ℝ) * a * b ≤ (m : ℝ) * γ_E ^ 4 * (l : ℝ) :=
      mul_le_mul h1 hb (by positivity) (by positivity)
    exact le_trans (mul_le_mul_of_nonneg_right h2 (by linarith)) hB_ge_m
  have hB_ge_1 : 1 ≤ B := by
    have h1 := hB_ge 1 1 (by norm_num) hγE_1_4 (by norm_num) hl_ge1
    have h2 : (1 : ℝ) ≤ (m : ℝ) * L_log :=
      le_trans hm_ge1 (le_mul_of_one_le_right (Nat.cast_nonneg _) hL1)
    linarith
  have hB_ge_m0 : (m : ℝ) ≤ B := by
    have h1 := hB_ge 1 1 (by norm_num) hγE_1_4 (by norm_num) hl_ge1
    have h2 : (m : ℝ) ≤ (m : ℝ) * L_log := le_mul_of_one_le_right (Nat.cast_nonneg _) hL1
    linarith
  have hB_ge_ml : (m : ℝ) * (l : ℝ) ≤ B := by
    have h1 := hB_ge 1 l (by norm_num) hγE_1_4 (by positivity) le_rfl
    have h2 : (m : ℝ) * (l : ℝ) ≤ (m : ℝ) * (l : ℝ) * L_log :=
      le_mul_of_one_le_right (by positivity) hL1
    linarith
  have hB_ge_mE : (m : ℝ) * γ_E ≤ B := by
    have h1 := hB_ge γ_E 1 hγE_nn hγE_E_4 (by norm_num) hl_ge1
    have h2 : (m : ℝ) * γ_E ≤ (m : ℝ) * γ_E * L_log :=
      le_mul_of_one_le_right (mul_nonneg (Nat.cast_nonneg _) hγE_nn) hL1
    linarith
  have hB_ge_mE2 : (m : ℝ) * γ_E ^ 2 ≤ B := by
    have h1 := hB_ge (γ_E ^ 2) 1 (sq_nonneg _) hγE_2_4 (by norm_num) hl_ge1
    have h2 : (m : ℝ) * γ_E ^ 2 ≤ (m : ℝ) * γ_E ^ 2 * L_log :=
      le_mul_of_one_le_right (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) hL1
    linarith
  have hB_ge_mE2L : (m : ℝ) * γ_E ^ 2 * L_log ≤ B := by
    have h1 := hB_ge (γ_E ^ 2) 1 (sq_nonneg _) hγE_2_4 (by norm_num) hl_ge1; linarith
  have hB_ge_mE2l : (m : ℝ) * γ_E ^ 2 * (l : ℝ) ≤ B := by
    have h1 := hB_ge (γ_E ^ 2) l (sq_nonneg _) hγE_2_4 (by positivity) le_rfl
    have h2 : (m : ℝ) * γ_E ^ 2 * (l : ℝ) ≤ (m : ℝ) * γ_E ^ 2 * (l : ℝ) * L_log :=
      le_mul_of_one_le_right (by positivity) hL1
    linarith
  have hB_ge_mElL : (m : ℝ) * γ_E * (l : ℝ) * L_log ≤ B :=
    hB_ge γ_E l hγE_nn hγE_E_4 (by positivity) le_rfl
  have hB_ge_EL : γ_E * L_log ≤ B := by
    have h0 : γ_E ≤ (m : ℝ) * γ_E ^ 2 :=
      le_trans hγE_sq (le_mul_of_one_le_left (sq_nonneg _) hm_ge1)
    exact le_trans (mul_le_mul_of_nonneg_right h0 (by linarith)) hB_ge_mE2L
  have hγQ_le : γ_Q ≤ γ_t * γ_E := hγq
  have hgQJ_t : (pds.gQuery dJ m0 : ℝ) ≤ γ_t * γ_E := le_trans hgQJ hγQ_le
  have hgQW_t : (pds.gQuery dW mw : ℝ) ≤ γ_t * γ_E := le_trans hgQW hγQ_le
  -- Bound `mw ≤ (c_deg + 1) * m * γ_E`.
  have hinv_nn : 0 ≤ 1 / impl.decompose.φ_lb m0 := div_nonneg zero_le_one (impl.decompose.hφ_lb_pos m0).le
  have hmw_le : (mw : ℝ) ≤ (c_deg + 1) * (m : ℝ) * γ_E := by
    have h1 : (mw : ℝ) ≤ c_deg * (m0 : ℝ) / impl.decompose.φ_lb m0 + 2 := by
      unfold mw Task1Input.mwCap; push_cast
      have := nat_ceil_le_add_one (c_deg * (m0 : ℝ) / impl.decompose.φ_lb m0)
        (div_nonneg (by positivity) (impl.decompose.hφ_lb_pos m0).le)
      linarith
    have h2 : c_deg * (m0 : ℝ) / impl.decompose.φ_lb m0 ≤ c_deg * (m : ℝ) * γ_E := by
      have ha : c_deg * ((m0 : ℝ) * (1 / impl.decompose.φ_lb m0)) ≤ c_deg * ((m : ℝ) * γ_E) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hm0_le hinv_E hinv_nn (Nat.cast_nonneg _)) (by linarith only [hcdeg_ge2])
      have hb : c_deg * (m0 : ℝ) / impl.decompose.φ_lb m0 = c_deg * ((m0 : ℝ) * (1 / impl.decompose.φ_lb m0)) := by ring
      linarith only [ha, hb]
    nlinarith only [h1, h2, hm_ge1, hγE2]
  -- Bound `embVertSum ≤ 2 * m * l`.
  have hevs_eq : embVertSumMem mem inp.jAddr inp.embJHAddr = (inp.toT2 0).embVertSum := by
    rw [embVertSumMem_eq hgJ hEA]; rfl
  have hevs_le : ((inp.toT2 0).embVertSum : ℝ) ≤ 2 * (m : ℝ) * (l : ℝ) := by
    exact_mod_cast embVertSum_le hEmb (fun _ => hLen)
  -- Bound `eta1Cap` and `eta2Bound`.
  have hJn_nn : (0 : ℝ) ≤ (inp.J.n : ℝ) := Nat.cast_nonneg _
  have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  have hx_ge2 : (2 : ℝ) ≤ (inp.J.n : ℝ) + (m : ℝ) + 2 := by linarith
  have hη1_le : (Task2Input.eta1Cap impl inp.J : ℝ) ≤
      (1 + (2 * c_deg + 1) * (c_deg + 1) / Real.log 2) * γ_E * L_log := by
    unfold Task2Input.eta1Cap; push_cast
    change 1 + (Nat.ceil (2 * c_deg) : ℝ) *
      ((Nat.log 2 (Nat.ceil (c_deg * (m : ℝ) / (2 * impl.decompose.φ_lb m0)) + 1) : ℝ) + 1) ≤ _
    have hceil1 : (Nat.ceil (2 * c_deg) : ℝ) ≤ 2 * c_deg + 1 := nat_ceil_le_add_one _ (by positivity)
    have harg : ((Nat.ceil (c_deg * (m : ℝ) / (2 * impl.decompose.φ_lb m0)) + 1 : ℕ) : ℝ) ≤
        ((c_deg + 1) * γ_E) * ((inp.J.n : ℝ) + (m : ℝ) + 2) := by
      push_cast
      have hpos := impl.decompose.hφ_lb_pos m0
      have h0 : (Nat.ceil (c_deg * (m : ℝ) / (2 * impl.decompose.φ_lb m0)) : ℝ) ≤
          c_deg * (m : ℝ) / (2 * impl.decompose.φ_lb m0) + 1 :=
        nat_ceil_le_add_one _ (div_nonneg (by positivity) (by linarith))
      have h1 : c_deg * (m : ℝ) / (2 * impl.decompose.φ_lb m0) ≤ c_deg * (m : ℝ) * γ_E := by
        have hhalf : c_deg * (m : ℝ) / (2 * impl.decompose.φ_lb m0) ≤ c_deg * (m : ℝ) / impl.decompose.φ_lb m0 := by
          have hc0 : 0 ≤ c_deg * (m : ℝ) := by positivity
          exact div_le_div_of_nonneg_left hc0 hpos (by linarith)
        have h2 : c_deg * (m : ℝ) / impl.decompose.φ_lb m0 ≤ c_deg * (m : ℝ) * γ_E := by
          have ha : c_deg * ((m : ℝ) * (1 / impl.decompose.φ_lb m0)) ≤ c_deg * ((m : ℝ) * γ_E) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinv_E hm_nn) (by linarith only [hcdeg_ge2])
          have hb : c_deg * (m : ℝ) / impl.decompose.φ_lb m0 = c_deg * ((m : ℝ) * (1 / impl.decompose.φ_lb m0)) := by ring
          linarith only [ha, hb]
        linarith
      have h3 : c_deg * (m : ℝ) * γ_E + 2 ≤ ((c_deg + 1) * γ_E) * ((inp.J.n : ℝ) + (m : ℝ) + 2) := by
        have ha : (c_deg + 1) * γ_E * ((m : ℝ) + 2) ≤ (c_deg + 1) * γ_E * ((inp.J.n : ℝ) + (m : ℝ) + 2) :=
          mul_le_mul_of_nonneg_left (by linarith only [hJn_nn]) (by nlinarith only [hcdeg_ge2, hγE2])
        have hb : 0 ≤ (m : ℝ) * γ_E := mul_nonneg hm_nn hγE_nn
        nlinarith only [ha, hb, hcdeg_ge2, hγE2]
      linarith only [h0, h1, h3]
    have hA1 : 1 ≤ (c_deg + 1) * γ_E := by nlinarith only [hcdeg_ge2, hγE2]
    have hlog := log2_prod_le (A := (c_deg + 1) * γ_E) hA1 hx_ge2 harg
    have hlog_nn : 0 ≤ (Nat.log 2 (Nat.ceil (c_deg * (m : ℝ) / (2 * impl.decompose.φ_lb m0)) + 1) : ℝ) + 1 := by
      positivity
    have hmul : (Nat.ceil (2 * c_deg) : ℝ) *
        ((Nat.log 2 (Nat.ceil (c_deg * (m : ℝ) / (2 * impl.decompose.φ_lb m0)) + 1) : ℝ) + 1) ≤
        (2 * c_deg + 1) * (((c_deg + 1) * γ_E / Real.log 2) * L_log) :=
      mul_le_mul hceil1 hlog hlog_nn (by positivity)
    have h1le : (1 : ℝ) ≤ 1 * γ_E * L_log := by nlinarith only [hγE2, hL1]
    have hr : (2 * c_deg + 1) * (((c_deg + 1) * γ_E / Real.log 2) * L_log) =
        ((2 * c_deg + 1) * (c_deg + 1) / Real.log 2) * γ_E * L_log := by ring
    linarith only [hmul, h1le, hr]
  have hη2_le : (eta2Bound inp.J : ℝ) ≤ (1 + 2 / Real.log 2) * L_log := by
    unfold eta2Bound; push_cast
    change 1 + 2 * ((Nat.log 2 (m + 1) : ℝ) + 1) ≤ (1 + 2 / Real.log 2) * L_log
    have hlog : (Nat.log 2 (m + 1) : ℝ) + 1 ≤ (1 / Real.log 2) * L_log :=
      log2_prod_le (A := 1) le_rfl hx_ge2 (n := m + 1) (by push_cast; linarith only [hJn_nn])
    have h2 : 2 * (1 / Real.log 2 * L_log) = 2 / Real.log 2 * L_log := by ring
    linarith only [hlog, h2, hL1]
  -- 1. Task 1 cost bound.
  have hdec_le : (Nat.ceil (impl.decompose.K_dec * ((m0 : ℝ) * impl.decompose.decFactor m0 + 1)) : ℝ) ≤
      (costs.decompose.callCost m0 : ℝ) + (impl.decompose.K_dec + 1) := by
    rcases Nat.eq_zero_or_pos m0 with hm00 | hm0p
    · rw [hm00]; simp only [Nat.cast_zero, zero_mul, zero_add, mul_one]
      have := nat_ceil_le_add_one impl.decompose.K_dec impl.decompose.hK_dec
      have : (0 : ℝ) ≤ costs.decompose.callCost 0 := Nat.cast_nonneg _
      linarith
    · have h1 : Nat.ceil (impl.decompose.K_dec * ((m0 : ℝ) * impl.decompose.decFactor m0 + 1)) ≤
          costs.decompose.callCost m0 := decompose_cost_le impl.decompose hm0p
      have h2 : (Nat.ceil (impl.decompose.K_dec * ((m0 : ℝ) * impl.decompose.decFactor m0 + 1)) : ℝ) ≤
          (costs.decompose.callCost m0 : ℝ) := by exact_mod_cast h1
      linarith [impl.decompose.hK_dec]
  have hlog_b1 : (Nat.log 2 (dJ + m0 + 2) : ℝ) + 1 ≤ (2 * γ_E / Real.log 2) * L_log := by
    refine log2_prod_le (A := 2 * γ_E) (by linarith) hx_ge2 ?_
    push_cast; nlinarith only [hdJ_E, hm0_le, hJn_nn, hm_nn, hγE2]
  have hlog_b2 : (Nat.log 2 (dW + mw + 2) : ℝ) + 1 ≤ ((c_deg + 3) * γ_E / Real.log 2) * L_log := by
    refine log2_prod_le (A := (c_deg + 3) * γ_E) (by nlinarith only [hcdeg_ge2, hγE2]) hx_ge2 ?_
    push_cast
    have h1 : (c_deg + 1) * (m : ℝ) * γ_E + 2 * (c_deg + 3) * γ_E ≤
        (c_deg + 3) * γ_E * ((inp.J.n : ℝ) + (m : ℝ) + 2) := by
      have ha : (c_deg + 3) * γ_E * ((m : ℝ) + 2) ≤ (c_deg + 3) * γ_E * ((inp.J.n : ℝ) + (m : ℝ) + 2) :=
        mul_le_mul_of_nonneg_left (by linarith only [hJn_nn]) (by nlinarith only [hcdeg_ge2, hγE2])
      have hb : (c_deg + 1) * (m : ℝ) * γ_E ≤ (c_deg + 3) * γ_E * (m : ℝ) := by
        have : 0 ≤ (m : ℝ) * γ_E := mul_nonneg hm_nn hγE_nn
        linarith only [this]
      linarith only [ha, hb]
    nlinarith only [hdW_E, hmw_le, h1, hcdeg_ge2, hγE2]
  have hce_ceil : (Nat.ceil (ce.K_ce * (4 * (m0 : ℝ) + 2 * (m0 : ℝ) / impl.decompose.φ_lb m0)) : ℝ) ≤
      ce.K_ce * (4 * (m : ℝ) + 2 * (m : ℝ) * γ_E) + 1 := by
    have h0 := nat_ceil_le_add_one (ce.K_ce * (4 * (m0 : ℝ) + 2 * (m0 : ℝ) / impl.decompose.φ_lb m0))
      (mul_nonneg ce.hK_ce (add_nonneg (by positivity) (div_nonneg (by positivity) (impl.decompose.hφ_lb_pos m0).le)))
    have h1 : 2 * (m0 : ℝ) / impl.decompose.φ_lb m0 ≤ 2 * (m : ℝ) * γ_E := by
      have ha : (m0 : ℝ) * (1 / impl.decompose.φ_lb m0) ≤ (m : ℝ) * γ_E :=
        mul_le_mul hm0_le hinv_E hinv_nn hm_nn
      have hb : 2 * (m0 : ℝ) / impl.decompose.φ_lb m0 = 2 * ((m0 : ℝ) * (1 / impl.decompose.φ_lb m0)) := by ring
      linarith only [ha, hb]
    have h2 : 4 * (m0 : ℝ) + 2 * (m0 : ℝ) / impl.decompose.φ_lb m0 ≤ 4 * (m : ℝ) + 2 * (m : ℝ) * γ_E := by
      linarith only [hm0_le, h1]
    have h3 := mul_le_mul_of_nonneg_left h2 ce.hK_ce
    linarith only [h0, h3]
  have ht1 : (task1StepCost impl inp.J (embVertSumMem mem inp.jAddr inp.embJHAddr) : ℝ) ≤
      (costs.decompose.callCost m0 : ℝ) +
      (3900 + impl.decompose.K_dec + 5 * ce.K_ce + 150 * (c_deg + 1) +
        (pds.K_bounds : ℝ) * (c_deg + 5) / Real.log 2) * B := by
    rw [hevs_eq]
    unfold task1StepCost; dsimp only; push_cast
    change 215 * (m : ℝ) + 120 * ((inp.toT2 0).embVertSum : ℝ) + 180 + (115 * (m : ℝ) + 55) +
      (Nat.ceil (impl.decompose.K_dec * ((m0 : ℝ) * impl.decompose.decFactor m0 + 1)) : ℝ) +
      (1200 * (m0 : ℝ) + 500) +
      (350 + (pds.K_bounds : ℝ) * ((Nat.log 2 (dJ + m0 + 2) : ℝ) + 1) +
        (pds.K_bounds : ℝ) * ((Nat.log 2 (dW + mw + 2) : ℝ) + 1)) +
      (265 * (m0 : ℝ) + 10 + ((m0 : ℝ) +
        (Nat.ceil (ce.K_ce * (4 * (m0 : ℝ) + 2 * (m0 : ℝ) / impl.decompose.φ_lb m0)) : ℝ))) +
      (307 * (m0 : ℝ) + 119 * (mw : ℝ) + 120) + 200 ≤ _
    have hKb_nn : (0 : ℝ) ≤ (pds.K_bounds : ℝ) := Nat.cast_nonneg _
    have hKb : (pds.K_bounds : ℝ) * ((Nat.log 2 (dJ + m0 + 2) : ℝ) + 1) +
        (pds.K_bounds : ℝ) * ((Nat.log 2 (dW + mw + 2) : ℝ) + 1) ≤
        ((pds.K_bounds : ℝ) * (c_deg + 5) / Real.log 2) * B := by
      have h1 := mul_le_mul_of_nonneg_left (add_le_add hlog_b1 hlog_b2) hKb_nn
      have h2 : (pds.K_bounds : ℝ) * ((2 * γ_E / Real.log 2) * L_log +
          ((c_deg + 3) * γ_E / Real.log 2) * L_log) =
          ((pds.K_bounds : ℝ) * (c_deg + 5) / Real.log 2) * (γ_E * L_log) := by ring
      rw [mul_add, h2] at h1
      have hhl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      exact le_trans h1 (mul_le_mul_of_nonneg_left hB_ge_EL (by positivity))
    have hce_B : ce.K_ce * (4 * (m : ℝ) + 2 * (m : ℝ) * γ_E) ≤ 5 * ce.K_ce * B := by
      have h1 : 4 * (m : ℝ) + 2 * (m : ℝ) * γ_E ≤ 5 * B := by
        have : (m : ℝ) ≤ (m : ℝ) * γ_E / 2 := by nlinarith only [hm_nn, hγE2]
        linarith only [this, hB_ge_mE]
      have := mul_le_mul_of_nonneg_left h1 ce.hK_ce; linarith only [this]
    have hmw_B : 119 * (mw : ℝ) ≤ 150 * (c_deg + 1) * B := by
      have : (mw : ℝ) ≤ (c_deg + 1) * B := by
        calc (mw : ℝ) ≤ (c_deg + 1) * ((m : ℝ) * γ_E) := by linarith only [hmw_le]
          _ ≤ (c_deg + 1) * B := mul_le_mul_of_nonneg_left hB_ge_mE (by positivity)
      linarith only [this]
    have hdec_K : impl.decompose.K_dec + 1 ≤ impl.decompose.K_dec * B + B := by
      nlinarith only [impl.decompose.hK_dec, hB_ge_1]
    linarith only [hdec_le, hKb, hce_ceil, hce_B, hmw_B, hdec_K, hevs_le, hm0_le, hB_ge_1, hB_ge_m0, hB_ge_ml]
  -- 2. Task 2 cost bound.
  set C_η1 : ℝ := 1 + (2 * c_deg + 1) * (c_deg + 1) / Real.log 2
  have hCη1_nn : 0 ≤ C_η1 := by have : 0 < Real.log 2 := Real.log_pos (by norm_num); positivity
  have hB_ge_mE2L_t : (m : ℝ) * γ_E ^ 2 * L_log ≤ γ_t * B :=
    le_trans hB_ge_mE2L (le_mul_of_one_le_left (by linarith) hγt)
  have ht2 : (task2Cost impl inp.J l (inp.toT2 0).embVertSum : ℝ) ≤
      (C_η1 * (pds.K_init + pds.K_del + 100 * (c_deg + 1) + 820) +
        (c_deg + 1) * (pds.K_query + 1005) + 1300) * γ_t * B := by
    unfold task2Cost; dsimp only; push_cast
    change (Task2Input.eta1Cap impl inp.J : ℝ) *
      ((m : ℝ) * (Nat.ceil (pds.K_init * (pds.gExp dJ m0 : ℝ)) : ℝ) +
        (m : ℝ) * (Nat.ceil (pds.K_del * (pds.gQuery dJ m0 : ℝ)) : ℝ) +
        400 * (m : ℝ) + 100 * (mw : ℝ) + 80 * ((inp.toT2 0).embVertSum : ℝ) + 250) +
      (mw : ℝ) * ((Nat.ceil (pds.K_query * (pds.gQuery dJ m0 : ℝ)) : ℝ) +
        200 * (pds.gExp dJ m0 : ℝ) * ((l : ℝ) + 1) + 600) +
      250 * (m : ℝ) + 200 * ((inp.toT2 0).embVertSum : ℝ) + 600 ≤ _
    have hc_init : (Nat.ceil (pds.K_init * (pds.gExp dJ m0 : ℝ)) : ℝ) ≤ pds.K_init * γ_E + 1 := by
      have h0 := nat_ceil_le_add_one (pds.K_init * (pds.gExp dJ m0 : ℝ)) (mul_nonneg pds.hK_init (Nat.cast_nonneg _))
      have h1 := mul_le_mul_of_nonneg_left hgEJ pds.hK_init; linarith only [h0, h1]
    have hc_del : (Nat.ceil (pds.K_del * (pds.gQuery dJ m0 : ℝ)) : ℝ) ≤ pds.K_del * (γ_t * γ_E) + 1 := by
      have h0 := nat_ceil_le_add_one (pds.K_del * (pds.gQuery dJ m0 : ℝ)) (mul_nonneg pds.hK_del (Nat.cast_nonneg _))
      have h1 := mul_le_mul_of_nonneg_left hgQJ_t pds.hK_del; linarith only [h0, h1]
    have hc_qry : (Nat.ceil (pds.K_query * (pds.gQuery dJ m0 : ℝ)) : ℝ) ≤ pds.K_query * (γ_t * γ_E) + 1 := by
      have h0 := nat_ceil_le_add_one (pds.K_query * (pds.gQuery dJ m0 : ℝ)) (mul_nonneg pds.hK_query (Nat.cast_nonneg _))
      have h1 := mul_le_mul_of_nonneg_left hgQJ_t pds.hK_query; linarith only [h0, h1]
    have hmEl_nn : 0 ≤ (m : ℝ) * γ_E * (l : ℝ) := by positivity
    have hmE_le_mEl : (m : ℝ) * γ_E ≤ (m : ℝ) * γ_E * (l : ℝ) :=
      le_mul_of_one_le_right (mul_nonneg hm_nn hγE_nn) hl_ge1
    have h3 : (m : ℝ) * γ_E ≤ γ_t * (m : ℝ) * γ_E * (l : ℝ) := by
      have := le_mul_of_one_le_left hmEl_nn hγt; linarith only [hmE_le_mEl, this]
    have h4 : (m : ℝ) * (l : ℝ) ≤ γ_t * (m : ℝ) * γ_E * (l : ℝ) := by
      have ha : (m : ℝ) * (l : ℝ) ≤ (m : ℝ) * γ_E * (l : ℝ) := by
        have := le_mul_of_one_le_right hm_nn hγE_ge1
        exact mul_le_mul_of_nonneg_right this (Nat.cast_nonneg _)
      have hb := le_mul_of_one_le_left hmEl_nn hγt; linarith only [ha, hb]
    have h5 : (m : ℝ) ≤ γ_t * (m : ℝ) * γ_E * (l : ℝ) :=
      le_trans (le_mul_of_one_le_right hm_nn hγE_ge1) h3
    have h6 : (1 : ℝ) ≤ γ_t * (m : ℝ) * γ_E * (l : ℝ) := le_trans hm_ge1 h5
    have hinner1 : (m : ℝ) * (Nat.ceil (pds.K_init * (pds.gExp dJ m0 : ℝ)) : ℝ) +
        (m : ℝ) * (Nat.ceil (pds.K_del * (pds.gQuery dJ m0 : ℝ)) : ℝ) +
        400 * (m : ℝ) + 100 * (mw : ℝ) + 80 * ((inp.toT2 0).embVertSum : ℝ) + 250 ≤
        (pds.K_init + pds.K_del + 100 * (c_deg + 1) + 820) * (γ_t * (m : ℝ) * γ_E * (l : ℝ)) := by
      have h1 : (m : ℝ) * (pds.K_init * γ_E + 1) ≤ (pds.K_init + 1) * (γ_t * (m : ℝ) * γ_E * (l : ℝ)) := by
        have ha := mul_le_mul_of_nonneg_left h3 pds.hK_init; linarith only [ha, h5]
      have h2 : (m : ℝ) * (pds.K_del * (γ_t * γ_E) + 1) ≤ (pds.K_del + 1) * (γ_t * (m : ℝ) * γ_E * (l : ℝ)) := by
        have hgtE : (m : ℝ) * (γ_t * γ_E) ≤ γ_t * (m : ℝ) * γ_E * (l : ℝ) := by
          have := le_mul_of_one_le_right (show 0 ≤ γ_t * (m : ℝ) * γ_E by positivity) hl_ge1; linarith only [this]
        have ha := mul_le_mul_of_nonneg_left hgtE pds.hK_del; linarith only [ha, h5]
      have h7 : 100 * (mw : ℝ) ≤ 100 * (c_deg + 1) * (γ_t * (m : ℝ) * γ_E * (l : ℝ)) := by
        have := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ 100 * (c_deg + 1)); linarith only [hmw_le, this]
      have hi1 := mul_le_mul_of_nonneg_left hc_init hm_nn
      have hi2 := mul_le_mul_of_nonneg_left hc_del hm_nn
      linarith only [h1, h2, h4, h5, h6, h7, hi1, hi2, hevs_le]
    have hterm1 : (Task2Input.eta1Cap impl inp.J : ℝ) *
        ((m : ℝ) * (Nat.ceil (pds.K_init * (pds.gExp dJ m0 : ℝ)) : ℝ) +
          (m : ℝ) * (Nat.ceil (pds.K_del * (pds.gQuery dJ m0 : ℝ)) : ℝ) +
          400 * (m : ℝ) + 100 * (mw : ℝ) + 80 * ((inp.toT2 0).embVertSum : ℝ) + 250) ≤
        (C_η1 * (pds.K_init + pds.K_del + 100 * (c_deg + 1) + 820)) * γ_t * B := by
      have hmul := mul_le_mul hη1_le hinner1 (by positivity) (by positivity)
      have hB' : γ_E * L_log * (γ_t * (m : ℝ) * γ_E * (l : ℝ)) ≤ γ_t * B := by
        have h0 : (m : ℝ) * γ_E ^ 2 * (l : ℝ) * L_log ≤ B :=
          hB_ge (γ_E ^ 2) l (sq_nonneg _) hγE_2_4 (by positivity) le_rfl
        have h1 := mul_le_mul_of_nonneg_left h0 (by linarith only [hγt] : 0 ≤ γ_t)
        have h2 : γ_E * L_log * (γ_t * (m : ℝ) * γ_E * (l : ℝ)) = γ_t * ((m : ℝ) * γ_E ^ 2 * (l : ℝ) * L_log) := by ring
        linarith only [h1, h2]
      have hcoeff : 0 ≤ C_η1 * (pds.K_init + pds.K_del + 100 * (c_deg + 1) + 820) := by
        have := pds.hK_init; have := pds.hK_del; positivity
      calc _ ≤ (C_η1 * (pds.K_init + pds.K_del + 100 * (c_deg + 1) + 820)) *
            (γ_E * L_log * (γ_t * (m : ℝ) * γ_E * (l : ℝ))) := by linarith only [hmul]
        _ ≤ (C_η1 * (pds.K_init + pds.K_del + 100 * (c_deg + 1) + 820)) * (γ_t * B) :=
            mul_le_mul_of_nonneg_left hB' hcoeff
        _ = _ := by ring
    have hinner2 : (Nat.ceil (pds.K_query * (pds.gQuery dJ m0 : ℝ)) : ℝ) +
        200 * (pds.gExp dJ m0 : ℝ) * ((l : ℝ) + 1) + 600 ≤
        (pds.K_query + 1005) * (γ_t * γ_E * (l : ℝ)) := by
      have hgtE : γ_t * γ_E ≤ γ_t * γ_E * (l : ℝ) :=
        le_mul_of_one_le_right (by positivity) hl_ge1
      have hEl : γ_E * (l : ℝ) ≤ γ_t * γ_E * (l : ℝ) := by
        have := le_mul_of_one_le_left (show 0 ≤ γ_E * (l : ℝ) by positivity) hγt; linarith only [this]
      have h1 : (1 : ℝ) ≤ γ_t * γ_E * (l : ℝ) := le_trans hγE_ge1 (le_trans (le_mul_of_one_le_right hγE_nn hl_ge1) hEl)
      have hg2 : 200 * (pds.gExp dJ m0 : ℝ) * ((l : ℝ) + 1) ≤ 400 * (γ_E * (l : ℝ)) := by
        have ha : (pds.gExp dJ m0 : ℝ) * ((l : ℝ) + 1) ≤ γ_E * (2 * (l : ℝ)) :=
          mul_le_mul hgEJ (by linarith only [hl_ge1]) (by positivity) hγE_nn
        linarith only [ha]
      have hkq := mul_le_mul_of_nonneg_left hgtE pds.hK_query
      linarith only [hc_qry, hg2, hkq, hEl, h1]
    have hterm2 : (mw : ℝ) * ((Nat.ceil (pds.K_query * (pds.gQuery dJ m0 : ℝ)) : ℝ) +
        200 * (pds.gExp dJ m0 : ℝ) * ((l : ℝ) + 1) + 600) ≤
        ((c_deg + 1) * (pds.K_query + 1005)) * γ_t * B := by
      have hmul := mul_le_mul hmw_le hinner2 (by positivity) (by positivity)
      have hB' : (m : ℝ) * γ_E * (γ_t * γ_E * (l : ℝ)) ≤ γ_t * B := by
        have := mul_le_mul_of_nonneg_left hB_ge_mE2l (by linarith only [hγt] : 0 ≤ γ_t); linarith only [this]
      have hcoeff : 0 ≤ (c_deg + 1) * (pds.K_query + 1005) := by have := pds.hK_query; positivity
      calc _ ≤ ((c_deg + 1) * (pds.K_query + 1005)) * ((m : ℝ) * γ_E * (γ_t * γ_E * (l : ℝ))) := by linarith only [hmul]
        _ ≤ ((c_deg + 1) * (pds.K_query + 1005)) * (γ_t * B) := mul_le_mul_of_nonneg_left hB' hcoeff
        _ = _ := by ring
    have hterm3 : 250 * (m : ℝ) + 200 * ((inp.toT2 0).embVertSum : ℝ) + 600 ≤ 1300 * γ_t * B := by
      have hBt : B ≤ γ_t * B := le_mul_of_one_le_left (by linarith only [hB_ge_1]) hγt
      linarith only [hB_ge_1, hB_ge_m0, hB_ge_ml, hevs_le, hBt]
    linarith only [hterm1, hterm2, hterm3]
  -- 3. Task 3 cost bound.
  set C_η2 : ℝ := 1 + 2 / Real.log 2
  have hCη2_nn : 0 ≤ C_η2 := by have : 0 < Real.log 2 := Real.log_pos (by norm_num); positivity
  have ht3 : (task3Cost impl inp.J : ℝ) ≤
      (C_η2 * ((c_deg + 1) * (pds.K_init + 85) + 705) + pds.K_query + pds.K_del + 1510) * γ_t * B := by
    unfold task3Cost; dsimp only; push_cast
    change (eta2Bound inp.J : ℝ) *
      ((mw : ℝ) * (Nat.ceil (pds.K_init * (pds.gExp dW mw : ℝ)) : ℝ) +
        80 * (mw : ℝ) + 300 * (m : ℝ) + 400) +
      (m : ℝ) * ((Nat.ceil (pds.K_query * (pds.gQuery dW mw : ℝ)) : ℝ) +
        (pds.gExp dW mw : ℝ) * ((Nat.ceil (pds.K_del * (pds.gQuery dW mw : ℝ)) : ℝ) + 300) + 600) +
      600 ≤ _
    have hc_init : (Nat.ceil (pds.K_init * (pds.gExp dW mw : ℝ)) : ℝ) ≤ pds.K_init * γ_E + 1 := by
      have h0 := nat_ceil_le_add_one (pds.K_init * (pds.gExp dW mw : ℝ)) (mul_nonneg pds.hK_init (Nat.cast_nonneg _))
      have h1 := mul_le_mul_of_nonneg_left hgEW pds.hK_init; linarith only [h0, h1]
    have hc_del : (Nat.ceil (pds.K_del * (pds.gQuery dW mw : ℝ)) : ℝ) ≤ pds.K_del * (γ_t * γ_E) + 1 := by
      have h0 := nat_ceil_le_add_one (pds.K_del * (pds.gQuery dW mw : ℝ)) (mul_nonneg pds.hK_del (Nat.cast_nonneg _))
      have h1 := mul_le_mul_of_nonneg_left hgQW_t pds.hK_del; linarith only [h0, h1]
    have hc_qry : (Nat.ceil (pds.K_query * (pds.gQuery dW mw : ℝ)) : ℝ) ≤ pds.K_query * (γ_t * γ_E) + 1 := by
      have h0 := nat_ceil_le_add_one (pds.K_query * (pds.gQuery dW mw : ℝ)) (mul_nonneg pds.hK_query (Nat.cast_nonneg _))
      have h1 := mul_le_mul_of_nonneg_left hgQW_t pds.hK_query; linarith only [h0, h1]
    have hinner1 : (mw : ℝ) * (Nat.ceil (pds.K_init * (pds.gExp dW mw : ℝ)) : ℝ) +
        80 * (mw : ℝ) + 300 * (m : ℝ) + 400 ≤
        ((c_deg + 1) * (pds.K_init + 85) + 705) * ((m : ℝ) * γ_E ^ 2) := by
      have h1 := mul_le_mul hmw_le hc_init (by positivity) (by positivity)
      have hmE_le : (m : ℝ) * γ_E ≤ (m : ℝ) * γ_E ^ 2 := mul_le_mul_of_nonneg_left hγE_sq hm_nn
      have hm_le : (m : ℝ) ≤ (m : ℝ) * γ_E ^ 2 := le_mul_of_one_le_right hm_nn hγE_1_2
      have h1_le : (1 : ℝ) ≤ (m : ℝ) * γ_E ^ 2 := le_trans hm_ge1 hm_le
      have h2 : (c_deg + 1) * (m : ℝ) * γ_E * (pds.K_init * γ_E + 1) ≤
          (c_deg + 1) * (pds.K_init + 1) * ((m : ℝ) * γ_E ^ 2) := by
        have hstep := mul_le_mul_of_nonneg_left hmE_le (show 0 ≤ c_deg + 1 by positivity)
        linarith only [hstep]
      have hmw2 : 80 * (mw : ℝ) ≤ 80 * (c_deg + 1) * ((m : ℝ) * γ_E ^ 2) := by
        have hstep := mul_le_mul_of_nonneg_left hmE_le (show 0 ≤ 80 * (c_deg + 1) by positivity)
        linarith only [hstep, hmw_le]
      have hpad : (0 : ℝ) ≤ (4 * (c_deg + 1) + 5) * ((m : ℝ) * γ_E ^ 2) := by positivity
      linarith only [h1, h2, hmw2, hm_le, h1_le, hpad]
    have hterm1 : (eta2Bound inp.J : ℝ) *
        ((mw : ℝ) * (Nat.ceil (pds.K_init * (pds.gExp dW mw : ℝ)) : ℝ) +
          80 * (mw : ℝ) + 300 * (m : ℝ) + 400) ≤
        (C_η2 * ((c_deg + 1) * (pds.K_init + 85) + 705)) * γ_t * B := by
      have hmul := mul_le_mul hη2_le hinner1 (by positivity) (by positivity)
      have hcoeff : 0 ≤ C_η2 * ((c_deg + 1) * (pds.K_init + 85) + 705) := by
        have := pds.hK_init; positivity
      calc _ ≤ (C_η2 * ((c_deg + 1) * (pds.K_init + 85) + 705)) * ((m : ℝ) * γ_E ^ 2 * L_log) := by linarith only [hmul]
        _ ≤ (C_η2 * ((c_deg + 1) * (pds.K_init + 85) + 705)) * (γ_t * B) :=
            mul_le_mul_of_nonneg_left hB_ge_mE2L_t hcoeff
        _ = _ := by ring
    have hterm2 : (m : ℝ) * ((Nat.ceil (pds.K_query * (pds.gQuery dW mw : ℝ)) : ℝ) +
        (pds.gExp dW mw : ℝ) * ((Nat.ceil (pds.K_del * (pds.gQuery dW mw : ℝ)) : ℝ) + 300) + 600) + 600 ≤
        (pds.K_query + pds.K_del + 1510) * γ_t * B := by
      have hdel_mul : (pds.gExp dW mw : ℝ) * ((Nat.ceil (pds.K_del * (pds.gQuery dW mw : ℝ)) : ℝ) + 300) ≤
          γ_E * (pds.K_del * (γ_t * γ_E) + 301) :=
        mul_le_mul hgEW (by linarith only [hc_del]) (by positivity) hγE_nn
      have hsub : (m : ℝ) * ((Nat.ceil (pds.K_query * (pds.gQuery dW mw : ℝ)) : ℝ) +
          (pds.gExp dW mw : ℝ) * ((Nat.ceil (pds.K_del * (pds.gQuery dW mw : ℝ)) : ℝ) + 300) + 600) ≤
          (pds.K_query + pds.K_del + 910) * (γ_t * ((m : ℝ) * γ_E ^ 2)) := by
        have h1 : (Nat.ceil (pds.K_query * (pds.gQuery dW mw : ℝ)) : ℝ) +
            (pds.gExp dW mw : ℝ) * ((Nat.ceil (pds.K_del * (pds.gQuery dW mw : ℝ)) : ℝ) + 300) + 600 ≤
            (pds.K_query + pds.K_del + 910) * (γ_t * γ_E ^ 2) := by
          have ha : γ_t * γ_E ≤ γ_t * γ_E ^ 2 := mul_le_mul_of_nonneg_left hγE_sq (by linarith only [hγt])
          have hb : γ_E ≤ γ_t * γ_E ^ 2 := le_trans hγE_sq (le_mul_of_one_le_left (sq_nonneg _) hγt)
          have hc : (1 : ℝ) ≤ γ_t * γ_E ^ 2 := le_trans hγE_ge1 hb
          have hkq := mul_le_mul_of_nonneg_left ha pds.hK_query
          have hdel' : γ_E * (pds.K_del * (γ_t * γ_E) + 301) = pds.K_del * (γ_t * γ_E ^ 2) + 301 * γ_E := by ring
          linarith only [hc_qry, hdel_mul, hdel', hkq, hb, hc]
        have := mul_le_mul_of_nonneg_left h1 hm_nn; linarith only [this]
      have hB' : γ_t * ((m : ℝ) * γ_E ^ 2) ≤ γ_t * B :=
        mul_le_mul_of_nonneg_left hB_ge_mE2 (by linarith only [hγt])
      have hcoeff : 0 ≤ pds.K_query + pds.K_del + 910 := by
        have := pds.hK_query; have := pds.hK_del; positivity
      have h600 : (600 : ℝ) ≤ 600 * γ_t * B := by
        have h1 : (1 : ℝ) ≤ γ_t * B := le_trans hB_ge_1 (le_mul_of_one_le_left (by linarith only [hB_ge_1]) hγt)
        linarith only [h1]
      have hB'' := mul_le_mul_of_nonneg_left hB' hcoeff
      linarith only [hsub, hB'', h600]
    linarith only [hterm1, hterm2]
  -- 4. Output stage + 140 glue steps.
  have hout : (sparsifyOutCost mw m (Task2Input.gammaExpCap impl inp.J) : ℝ) + 140 ≤
      ((c_deg + 1) * 500 + 2500) * γ_t * B := by
    unfold sparsifyOutCost; dsimp only; push_cast
    set γC : ℝ := (Task2Input.gammaExpCap impl inp.J : ℝ)
    have hγC_nn : 0 ≤ γC := Nat.cast_nonneg _
    have h1 : (mw : ℝ) * (20 * γC + 120) + 115 * ((mw : ℝ) * γC) +
        (mw : ℝ) * (50 * (2 * γC + 3) + 200) ≤ (c_deg + 1) * 500 * ((m : ℝ) * γ_E ^ 2) := by
      have hmw_lin : (mw : ℝ) * (20 * γC + 120) + 115 * ((mw : ℝ) * γC) +
          (mw : ℝ) * (50 * (2 * γC + 3) + 200) = (mw : ℝ) * (235 * γC + 470) := by ring
      rw [hmw_lin]
      have hmul := mul_le_mul hmw_le (show 235 * γC + 470 ≤ 500 * γ_E by linarith only [hγCap_E, hγE2]) (by positivity) (by positivity)
      linarith only [hmul]
    have h2 : 90 * (m : ℝ) + (m : ℝ) * (γC * (120 * (2 * γC + 3) + 620) + 300) + 600 + 140 ≤
        2500 * ((m : ℝ) * γ_E ^ 2) := by
      have hq : γC * (120 * (2 * γC + 3) + 620) ≤ γ_E * (240 * γ_E + 980) := by
        exact mul_le_mul hγCap_E (by linarith only [hγCap_E]) (by positivity) hγE_nn
      have hq' : γ_E * (240 * γ_E + 980) ≤ 730 * γ_E ^ 2 := by nlinarith only [hγE2]
      have hm_le : (m : ℝ) ≤ (m : ℝ) * γ_E ^ 2 := le_mul_of_one_le_right hm_nn hγE_1_2
      have h1_le : (1 : ℝ) ≤ (m : ℝ) * γ_E ^ 2 := le_trans hm_ge1 hm_le
      have hmq := mul_le_mul_of_nonneg_left (le_trans hq hq') hm_nn
      linarith only [hmq, hm_le, h1_le]
    have hB' : (m : ℝ) * γ_E ^ 2 ≤ γ_t * B :=
      le_trans hB_ge_mE2 (le_mul_of_one_le_left (by linarith only [hB_ge_1]) hγt)
    have hB'' := mul_le_mul_of_nonneg_left hB' (by positivity : 0 ≤ (c_deg + 1) * 500 + 2500)
    linarith only [h1, h2, hB'']
  -- Combine all four pieces.
  have ht1' : (task1StepCost impl inp.J (embVertSumMem mem inp.jAddr inp.embJHAddr) : ℝ) ≤
      (costs.decompose.callCost m0 : ℝ) +
      (3900 + impl.decompose.K_dec + 5 * ce.K_ce + 150 * (c_deg + 1) +
        (pds.K_bounds : ℝ) * (c_deg + 5) / Real.log 2) * γ_t * B := by
    have hcoeff : 0 ≤ 3900 + impl.decompose.K_dec + 5 * ce.K_ce + 150 * (c_deg + 1) +
        (pds.K_bounds : ℝ) * (c_deg + 5) / Real.log 2 := by
      have := impl.decompose.hK_dec; have := ce.hK_ce
      have : 0 < Real.log 2 := Real.log_pos (by norm_num); positivity
    have hBt : B ≤ γ_t * B := le_mul_of_one_le_left (by linarith only [hB_ge_1]) hγt
    have := mul_le_mul_of_nonneg_left hBt hcoeff
    linarith only [ht1, this]
  have h1_le_B : (1 : ℝ) ≤ γ_t * B :=
    le_trans hB_ge_1 (le_mul_of_one_le_left (by linarith only [hB_ge_1]) hγt)
  have hrhs : sparsifyProgConst impl * γ_t *
      ((inp.J.n : ℝ) + (inp.J.m : ℝ) * γ_ℓ ^ 2 * (length inp.J inp.embJH : ℝ)) *
      (1 + Real.log ((inp.J.n : ℝ) + (inp.J.m : ℝ) + 2)) =
      ((4000 + impl.decompose.K_dec + 5 * ce.K_ce + 150 * (c_deg + 1) +
          (pds.K_bounds : ℝ) * (c_deg + 5) / Real.log 2) +
        (C_η1 * (pds.K_init + pds.K_del + 100 * (c_deg + 1) + 820) +
          (c_deg + 1) * (pds.K_query + 1005) + 1300) +
        (C_η2 * ((c_deg + 1) * (pds.K_init + 85) + 705) + pds.K_query + pds.K_del + 1510) +
        ((c_deg + 1) * 500 + 2500)) * γ_t * B := by
    change sparsifyProgConst impl * γ_t * ((inp.J.n : ℝ) + (m : ℝ) * γ_ℓ ^ 2 * (l : ℝ)) * L_log = _
    have hB_eq : ((inp.J.n : ℝ) + (m : ℝ) * γ_ℓ ^ 2 * (l : ℝ)) * L_log = B := rfl
    rw [mul_assoc, hB_eq]
    unfold sparsifyProgConst; rfl
  have hlhs : (sparsifyTotalCost impl inp mem : ℝ) =
      (task1StepCost impl inp.J (embVertSumMem mem inp.jAddr inp.embJHAddr) : ℝ) +
      (task2Cost impl inp.J l (inp.toT2 0).embVertSum : ℝ) +
      (task3Cost impl inp.J : ℝ) +
      (sparsifyOutCost mw m (Task2Input.gammaExpCap impl inp.J) : ℝ) + 140 := by
    unfold sparsifyTotalCost sparsifyCoreCost; push_cast; ring
  rw [hlhs, hrhs]
  linarith only [ht1', ht2, ht3, hout, h1_le_B]

/-- Absorbed cap-form runtime bound matching `theorem_8_1_at_cap_of_dec_le_with_time` when
`impl.decompose.decFactor M ≤ C_dec * γ_ℓ ^ 2`. -/
theorem sparsifyTotalCost_le_cap_of_dec_le_with_time (impl : SpannerToolImpl) (inp : Task1Input)
    (mem : ℕ → ℕ) (M : ℕ) {C_dec : ℝ} (γ_t : ℝ)
    (hC_nn : 0 ≤ C_dec)
    (hEmb : IsEmbedding inp.J inp.H' inp.embJH)
    (hgJ : GraphAt mem inp.jAddr inp.J)
    (hEA : EmbAt mem inp.embJHAddr inp.J.m inp.embJH)
    (hJm : inp.J.m ≤ M) (hJm_pos : 1 ≤ inp.J.m) (hLen : 1 ≤ length inp.J inp.embJH)
    (hγt : 1 ≤ γ_t)
    (hγq : let tools := spannerTools_of_impl impl
      let ce := impl.constructExpander
      let φ_min := impl.decompose.φ_lb M
      capGammaQuery (2 * (ce.c_deg_int : ℝ)) ce.φ_Const tools.pathDS φ_min M ≤
        γ_t * capGammaExpPath (2 * (ce.c_deg_int : ℝ)) ce.φ_Const tools.pathDS φ_min M)
    (hdec_le : let tools := spannerTools_of_impl impl
      let ce := impl.constructExpander
      let φ_min := impl.decompose.φ_lb M
      impl.decompose.decFactor M ≤
        C_dec * (capGammaL (2 * (ce.c_deg_int : ℝ)) ce.φ_Const tools.pathDS φ_min M) ^ 2) :
    let tools := spannerTools_of_impl impl
    let ce := impl.constructExpander
    let φ_min := impl.decompose.φ_lb M
    let γ_ℓ := capGammaL (2 * (ce.c_deg_int : ℝ)) ce.φ_Const tools.pathDS φ_min M
    (sparsifyTotalCost impl inp mem : ℝ) ≤
      (C_dec * (2 * impl.decompose.K_dec + 1) + sparsifyProgConst impl) * γ_t *
        ((inp.J.n : ℝ) + (inp.J.m : ℝ) * γ_ℓ ^ 2 * (length inp.J inp.embJH : ℝ)) *
        (1 + Real.log ((inp.J.n : ℝ) + (inp.J.m : ℝ) + 2)) := by
  intro tools ce φ_min γ_ℓ
  have hmain := sparsifyTotalCost_le_cap_with_time impl inp mem M γ_t hEmb hgJ hEA hJm hJm_pos hLen hγt hγq
  set costs := spannerToolCosts_of_impl impl
  set L_log := 1 + Real.log ((inp.J.n : ℝ) + (inp.J.m : ℝ) + 2)
  have hL1 : 1 ≤ L_log := one_le_one_add_log inp.J.n inp.J.m
  have hKdec : 0 ≤ costs.decompose.K_dec + 1 := by linarith [costs.decompose.hK_dec]
  have hdec_call : (costs.decompose.callCost (stripLoops inp.J).m : ℝ) ≤
      (C_dec * (2 * impl.decompose.K_dec + 1)) * γ_t *
        ((inp.J.n : ℝ) + (inp.J.m : ℝ) * γ_ℓ ^ 2 * (length inp.J inp.embJH : ℝ)) * L_log := by
    have hcall := costs.decompose.callCost_le_of_le (le_trans (stripLoops_m_le inp.J) hJm)
    have hstrip_m : ((stripLoops inp.J).m : ℝ) ≤ (inp.J.m : ℝ) :=
      Nat.cast_le.mpr (stripLoops_m_le inp.J)
    have h0 : (costs.decompose.K_dec + 1) * ((stripLoops inp.J).m : ℝ) * costs.decompose.decFactor M ≤
        (costs.decompose.K_dec + 1) * (inp.J.m : ℝ) * (C_dec * γ_ℓ ^ 2) := by
      have ha := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstrip_m hKdec)
        (by linarith [costs.decompose.hdec_ge M])
      have hb := mul_le_mul_of_nonneg_left (show costs.decompose.decFactor M ≤ C_dec * γ_ℓ ^ 2 from hdec_le)
        (mul_nonneg hKdec (Nat.cast_nonneg inp.J.m))
      exact le_trans ha hb
    have hlen1 : (1 : ℝ) ≤ (length inp.J inp.embJH : ℝ) := by exact_mod_cast hLen
    have hsum : (inp.J.m : ℝ) * γ_ℓ ^ 2 ≤
        γ_t * ((inp.J.n : ℝ) + (inp.J.m : ℝ) * γ_ℓ ^ 2 * (length inp.J inp.embJH : ℝ)) * L_log := by
      have h1 : (inp.J.m : ℝ) * γ_ℓ ^ 2 ≤ (inp.J.m : ℝ) * γ_ℓ ^ 2 * (length inp.J inp.embJH : ℝ) :=
        le_mul_of_one_le_right (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) hlen1
      have h2 : (inp.J.m : ℝ) * γ_ℓ ^ 2 ≤
          (inp.J.n : ℝ) + (inp.J.m : ℝ) * γ_ℓ ^ 2 * (length inp.J inp.embJH : ℝ) := by
        have : (0 : ℝ) ≤ inp.J.n := Nat.cast_nonneg _; linarith
      have h3 := le_trans h2 (le_mul_of_one_le_right (by positivity) hL1)
      have h4 : ((inp.J.n : ℝ) + (inp.J.m : ℝ) * γ_ℓ ^ 2 * (length inp.J inp.embJH : ℝ)) * L_log ≤
          γ_t * (((inp.J.n : ℝ) + (inp.J.m : ℝ) * γ_ℓ ^ 2 * (length inp.J inp.embJH : ℝ)) * L_log) :=
        le_mul_of_one_le_left (by positivity) hγt
      linarith
    have hKeq : costs.decompose.K_dec + 1 = 2 * impl.decompose.K_dec + 1 := rfl
    have hmul := mul_le_mul_of_nonneg_left hsum (mul_nonneg hC_nn hKdec)
    calc (costs.decompose.callCost (stripLoops inp.J).m : ℝ)
        ≤ (costs.decompose.K_dec + 1) * (inp.J.m : ℝ) * (C_dec * γ_ℓ ^ 2) := le_trans hcall h0
      _ = (C_dec * (costs.decompose.K_dec + 1)) * ((inp.J.m : ℝ) * γ_ℓ ^ 2) := by ring
      _ ≤ (C_dec * (costs.decompose.K_dec + 1)) *
            (γ_t * ((inp.J.n : ℝ) + (inp.J.m : ℝ) * γ_ℓ ^ 2 * (length inp.J inp.embJH : ℝ)) * L_log) := hmul
      _ = _ := by rw [hKeq]; ring
  linarith

end MinCostFlow.Spanner
