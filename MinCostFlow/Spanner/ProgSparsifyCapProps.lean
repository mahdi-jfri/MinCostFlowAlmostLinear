module

public import MinCostFlow.Spanner.ProgSparsifyCost

@[expose] public section

/-!
# Uniform Cap Properties and Polynomial Helpers for Word-RAM `Sparsify`

Proves:
- `decomposeSubpoly_poly_le`: `decomposeSubpoly c m ≤ Real.exp (6 * c) * (m + 2) ^ ⌈3 * c⌉₊`.
- Polynomial arithmetic and log-width helpers (`spPoly_le`, `spPoly_mul`, `spPoly_pow`,
  `spNat_lt_pow_of_poly`, `spNat_lt_two_pow_of_poly`, `spLog2_poly_le`,
  `spLength_le_embVertSum`, `spVcongNat_le_m`, `spMaxDeg_le_two_m`).
- `sparsifyPost_cap_props`: lifts `SparsifyPost` to the uniform `M`-cap Theorem 8.1 output
  guarantees (`γ_c`, `γ_ℓ`, `K_s`) matching `CitedSparsifyProp`.
-/

namespace MinCostFlow.Spanner

open WordRAM Cited

/-! ### Polynomial bound on `decomposeSubpoly` -/

/-- Subpolynomial `decomposeSubpoly c m = exp (c · (log (m+2))^{2/3} · log (log (m+2) + 2))`
is bounded above by `exp (6 · c) · (m + 2)^{⌈3 · c⌉₊}` for every `c ≥ 0` and `m : ℕ`. -/
theorem decomposeSubpoly_poly_le {c : ℝ} (hc : 0 ≤ c) (m : ℕ) :
    decomposeSubpoly c m ≤ Real.exp (6 * c) * ((m : ℝ) + 2) ^ Nat.ceil (3 * c) := by
  unfold decomposeSubpoly
  set x : ℝ := (m : ℝ) + 2
  have hx2 : (2 : ℝ) ≤ x := by dsimp only [x]; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hx_pos : 0 < x := by linarith
  set t : ℝ := Real.log x
  have ht_pos : 0 < t := Real.log_pos (by linarith)
  have ht2_pos : 0 < t + 2 := by linarith
  have hlog_t2 : Real.log (t + 2) ≤ 3 * (t + 2) ^ (1 / 3 : ℝ) := by
    have hrpow : Real.log ((t + 2) ^ (1 / 3 : ℝ)) = (1 / 3 : ℝ) * Real.log (t + 2) :=
      Real.log_rpow ht2_pos (1 / 3 : ℝ)
    have hle := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos ht2_pos (1 / 3 : ℝ))
    linarith
  have ht_rpow : t ^ (2 / 3 : ℝ) ≤ (t + 2) ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow ht_pos.le (by linarith) (by norm_num)
  have hprod : t ^ (2 / 3 : ℝ) * Real.log (t + 2) ≤ 3 * t + 6 := by
    have h1 : t ^ (2 / 3 : ℝ) * Real.log (t + 2) ≤
        (t + 2) ^ (2 / 3 : ℝ) * (3 * (t + 2) ^ (1 / 3 : ℝ)) :=
      mul_le_mul ht_rpow hlog_t2 (Real.log_nonneg (by linarith)) (by positivity)
    have h2 : (t + 2) ^ (2 / 3 : ℝ) * (t + 2) ^ (1 / 3 : ℝ) = t + 2 := by
      rw [← Real.rpow_add ht2_pos]
      norm_num
    linarith
  have hexp_le : c * (t ^ (2 / 3 : ℝ) * Real.log (t + 2)) ≤
      6 * c + (Nat.ceil (3 * c) : ℝ) * t := by
    have h1 : c * (t ^ (2 / 3 : ℝ) * Real.log (t + 2)) ≤ c * (3 * t + 6) :=
      mul_le_mul_of_nonneg_left hprod hc
    have hceil : 3 * c ≤ (Nat.ceil (3 * c) : ℝ) := Nat.le_ceil (3 * c)
    have h2 : (3 * c) * t ≤ (Nat.ceil (3 * c) : ℝ) * t :=
      mul_le_mul_of_nonneg_right hceil ht_pos.le
    linarith
  calc Real.exp (c * t ^ (2 / 3 : ℝ) * Real.log (t + 2))
      = Real.exp (c * (t ^ (2 / 3 : ℝ) * Real.log (t + 2))) := by ring_nf
    _ ≤ Real.exp (6 * c + (Nat.ceil (3 * c) : ℝ) * t) := Real.exp_le_exp.mpr hexp_le
    _ = Real.exp (6 * c) * Real.exp ((Nat.ceil (3 * c) : ℝ) * Real.log x) := Real.exp_add _ _
    _ = Real.exp (6 * c) * x ^ Nat.ceil (3 * c) := by
        rw [mul_comm (Nat.ceil (3 * c) : ℝ), ← Real.rpow_def_of_pos hx_pos, Real.rpow_natCast]

/-! ### Polynomial arithmetic and graph-statistic helpers -/

lemma spPoly_le {a C k C' k' x : ℕ} (hx : 1 ≤ x)
    (ha : a ≤ C * x ^ k) (hC : C ≤ C') (hk : k ≤ k') :
    a ≤ C' * x ^ k' :=
  le_trans ha (Nat.mul_le_mul hC (Nat.pow_le_pow_right hx hk))

lemma spPoly_mul {a b C₁ C₂ k₁ k₂ x : ℕ}
    (ha : a ≤ C₁ * x ^ k₁) (hb : b ≤ C₂ * x ^ k₂) :
    a * b ≤ (C₁ * C₂) * x ^ (k₁ + k₂) := by
  calc a * b ≤ (C₁ * x ^ k₁) * (C₂ * x ^ k₂) := Nat.mul_le_mul ha hb
    _ = (C₁ * C₂) * (x ^ k₁ * x ^ k₂) := by ring
    _ = (C₁ * C₂) * x ^ (k₁ + k₂) := by rw [← pow_add]

lemma spPoly_pow {a C k r x : ℕ} (ha : a ≤ C * x ^ k) :
    a ^ r ≤ C ^ r * x ^ (k * r) := by
  calc a ^ r ≤ (C * x ^ k) ^ r := Nat.pow_le_pow_left ha r
    _ = C ^ r * (x ^ k) ^ r := mul_pow _ _ _
    _ = C ^ r * x ^ (k * r) := by rw [← pow_mul]

lemma spNat_log2_le_self (n : ℕ) : Nat.log 2 n ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact le_trans Nat.lt_two_pow_self.le (Nat.pow_log_le_self 2 hn.ne')

lemma spNat_lt_pow_of_poly {C k H cw : ℕ} (hH : 2 ≤ H)
    (hcw : Nat.log 2 C + 1 + k ≤ cw) :
    C * H ^ k < H ^ cw := by
  have hC : C < 2 ^ (Nat.log 2 C + 1) := Nat.lt_pow_succ_log_self (by norm_num) C
  have h1 : C < H ^ (Nat.log 2 C + 1) := lt_of_lt_of_le hC (Nat.pow_le_pow_left hH _)
  have h2 : C * H ^ k < H ^ (Nat.log 2 C + 1) * H ^ k :=
    Nat.mul_lt_mul_of_pos_right h1 (Nat.pow_pos (by omega))
  rw [← pow_add] at h2
  exact lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by omega) hcw)

lemma spNat_lt_two_pow_of_poly {Y C k H cw w : ℕ} (hH : 2 ≤ H)
    (hY : Y ≤ C * H ^ k) (hcw : Nat.log 2 C + 1 + k ≤ cw)
    (hw : cw * (Nat.log 2 H + 1) ≤ w) :
    Y < 2 ^ w := by
  have h1 : Y < H ^ cw := lt_of_le_of_lt hY (spNat_lt_pow_of_poly hH hcw)
  have hH_lt : H < 2 ^ (Nat.log 2 H + 1) := Nat.lt_pow_succ_log_self (by norm_num) H
  have h2 : H ^ cw < (2 ^ (Nat.log 2 H + 1)) ^ cw :=
    Nat.pow_lt_pow_left hH_lt (by omega)
  rw [← pow_mul, Nat.mul_comm] at h2
  exact lt_of_lt_of_le (lt_trans h1 h2) (Nat.pow_le_pow_right (by norm_num) hw)

lemma spLog2_poly_le {Y C k H : ℕ} (hY : Y ≤ C * H ^ k) :
    Nat.log 2 Y + 1 ≤ (Nat.log 2 C + 1 + k) * (Nat.log 2 H + 1) := by
  set L := Nat.log 2 H + 1
  have hL : 1 ≤ L := by omega
  have hH_lt : H < 2 ^ L := Nat.lt_pow_succ_log_self (by norm_num) H
  have hC_lt : C < 2 ^ (Nat.log 2 C + 1) := Nat.lt_pow_succ_log_self (by norm_num) C
  have hY_lt : Y < 2 ^ (Nat.log 2 C + 1 + k * L) := by
    calc Y ≤ C * H ^ k := hY
      _ ≤ C * (2 ^ L) ^ k := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hH_lt.le k)
      _ < 2 ^ (Nat.log 2 C + 1) * (2 ^ L) ^ k :=
          Nat.mul_lt_mul_of_pos_right hC_lt (Nat.pow_pos (Nat.pow_pos (by norm_num)))
      _ = 2 ^ (Nat.log 2 C + 1 + k * L) := by rw [← pow_mul, ← pow_add, Nat.mul_comm L k]
  have hlog : Nat.log 2 Y < Nat.log 2 C + 1 + k * L := by
    rcases Nat.eq_zero_or_pos Y with rfl | hYp
    · simp
    · exact (Nat.log_lt_iff_lt_pow (by norm_num) hYp.ne').mpr hY_lt
  have h1 : Nat.log 2 C + 1 ≤ (Nat.log 2 C + 1) * L := Nat.le_mul_of_pos_right _ hL
  have h2 : Nat.log 2 C + 1 + k * L ≤ (Nat.log 2 C + 1 + k) * L := by
    rw [Nat.add_mul]; omega
  omega

lemma spLength_le_embVertSum {H' J : Graph} {embJH : ℕ → Walk}
    (hEmb : IsEmbedding J H' embJH) :
    length J embJH ≤ ∑ e ∈ Finset.range J.m, (embJH e).verts.length := by
  unfold length
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun e he => ?_⟩
  have he' : e < J.m := Finset.mem_range.mp he
  have h1 : (embJH e).edges.length ≤ (embJH e).verts.length := by
    rcases hEmb.2 e he' with ⟨_, _, ⟨hPv, hPe, _⟩ | ⟨_, hlen, _⟩⟩
    · simp [hPv, hPe]
    · omega
  exact le_trans h1 (Finset.single_le_sum (f := fun j => (embJH j).verts.length)
    (fun _ _ => Nat.zero_le _) he)

lemma spVcongNat_le_m (J H' : Graph) (embJH : ℕ → Walk) :
    vcongNat J H' embJH ≤ J.m := by
  unfold vcongNat
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun x _ => ?_⟩
  exact le_trans (Finset.card_filter_le _ _) (by simp)

lemma spMaxDeg_le_two_m {J : Graph} (hJ : J.IsValid) :
    maxDeg J ≤ 2 * J.m := by
  unfold maxDeg
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun v hv => ?_⟩
  have hvol : ∑ u ∈ Finset.range J.n, J.deg u = 2 * J.m := by
    have := vol_verts_eq_two_mul_m hJ
    simpa [Graph.vol, Graph.volIn, Graph.deg, Graph.verts] using this
  rw [← hvol]
  exact Finset.single_le_sum (f := fun u => J.deg u) (fun _ _ => Nat.zero_le _) hv

/-! ### Uniform `M`-cap Theorem 8.1 properties from `SparsifyPost` -/

/-- Lifts `SparsifyPost` to the uniform `M`-cap Theorem 8.1 bounds (`γ_c`, `γ_ℓ`, `K_s`). -/
theorem sparsifyPost_cap_props {impl : SpannerToolImpl} {inp : Task1Input}
    {mem mem' : ℕ → ℕ} {retHeap M : ℕ}
    (hpost : SparsifyPost impl inp mem mem' retHeap) (hJm : inp.J.m ≤ M) :
    let tools := spannerTools_of_impl impl
    let c_deg : ℝ := 2 * (impl.constructExpander.c_deg_int : ℝ)
    let φ_Const := impl.constructExpander.φ_Const
    let φ_min := impl.decompose.φ_lb M
    let γ_ℓ := capGammaL c_deg φ_Const tools.pathDS φ_min M
    let γ_c := capGammaC c_deg φ_Const tools.pathDS φ_min M
    let K_s := 1 + impl.decompose.c_ℓ * c_deg / Real.log 2
    ∃ (cJtilde : Graph) (kept : List ℕ) (embJJtilde : ℕ → Walk),
      kept.Nodup ∧
      (∀ k ∈ kept, k < inp.J.m) ∧
      cJtilde.n = inp.J.n ∧
      cJtilde.edges = kept.map (fun k => inp.J.edges.getD k (0, 0)) ∧
      cJtilde.IsValid ∧
      IsEmbedding inp.J cJtilde embJJtilde ∧
      vcong inp.J inp.H' (fun _ => 1) (compose cJtilde (restrictEmb inp.embJH kept) embJJtilde) ≤
        γ_c * (length inp.J inp.embJH : ℝ) *
          (vcong inp.J inp.H' (fun _ => 1) inp.embJH + (maxDeg inp.J : ℝ)) ∧
      (length inp.J embJJtilde : ℝ) ≤ γ_ℓ ∧
      (cJtilde.m : ℝ) ≤ K_s * (inp.J.n : ℝ) * γ_ℓ * (1 + Real.log ((inp.J.n : ℝ) + (inp.J.m : ℝ) + 2)) ∧
      inp.h + 3 ≤ retHeap ∧ retHeap ≤ sparsifyMaxHeapEnd impl inp ∧
      ZeroFrom mem' retHeap ∧ (∀ x < inp.h, mem' x = mem x) ∧
      inp.h ≤ mem' inp.h ∧ inp.h ≤ mem' (inp.h + 1) ∧ inp.h ≤ mem' (inp.h + 2) ∧
      mem' inp.h + cJtilde.encode.length ≤ retHeap ∧
      mem' (inp.h + 1) + 1 + kept.length ≤ retHeap ∧
      mem' (inp.h + 2) + inp.J.m ≤ retHeap ∧
      GraphAt mem' (mem' inp.h) cJtilde ∧
      ListAt mem' (mem' (inp.h + 1)) (kept.length :: kept) ∧
      EmbAt mem' (mem' (inp.h + 2)) inp.J.m embJJtilde ∧
      EmbBounded mem' (mem' (inp.h + 2)) inp.J.m embJJtilde retHeap := by
  intro tools c_deg φ_Const φ_min γ_ℓ γ_c K_s
  obtain ⟨wd, embWJ, embJW, η₁, η₂, _, _, _, _, hφ_lb, hcdeg, hφC, hJ0, hMW_cap, _, hℓ_le, hWm_n,
    hφds, hγE, hγD, hτ1, hτ2, hOK, hnd, hkept_lt, hJn, _, hJval, _, _, hEmbJJ, _, hvc, hlenJJ,
    _, hJtm_le, h3r, hr_max, hZr, hagr, hpJ0, hpK0, hpE0, hpJ_r, hpK_r, hpE_r, hGsub, hkept,
    hEmbC, hBndC⟩ := hpost
  have hOK0 := hOK (tools.toLocal 0 1)
  have hpds_mono := pathDSMonotone_of_impl impl.pathDS
  have hm0_le : (stripLoops inp.J).m ≤ M := le_trans (stripLoops_m_le inp.J) hJm
  have hφm_pos : 0 < φ_min := impl.decompose.hφ_lb_pos M
  have hφC_pos : 0 < φ_Const := impl.constructExpander.hφ_Const_pos
  have hφ_dec_ge : φ_min ≤ wd.φ_dec := le_trans (impl.decompose.hφ_lb_anti hm0_le) hφ_lb
  have hMW_le : wd.M_W ≤ capM_W c_deg φ_min M := by
    have h1 : Task1Input.mwCap impl inp.J ≤ capM_W c_deg φ_min M := by
      unfold Task1Input.mwCap capM_W
      have hc : 0 ≤ c_deg := by positivity
      have hm_r : ((stripLoops inp.J).m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hm0_le
      have hdiv : c_deg * ((stripLoops inp.J).m : ℝ) / impl.decompose.φ_lb (stripLoops inp.J).m ≤
          c_deg * (M : ℝ) / φ_min :=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hm_r hc) hφm_pos
          (impl.decompose.hφ_lb_anti hm0_le)
      exact Nat.add_le_add_right (Nat.ceil_mono hdiv) 1
    exact le_trans hMW_cap h1
  have hφds_ge : capPhiDS c_deg φ_Const tools.pathDS φ_min M ≤ wd.φ_ds := by
    rw [hφds]
    exact min_le_min (hpds_mono.hφ_out_mono hφm_pos hφ_dec_ge hOK0.φ_dec_le hm0_le)
      (hpds_mono.hφ_out_mono hφC_pos (hφC ▸ le_rfl) (hφC ▸ hOK0.φ_Const_le) hMW_le)
  have hγE_le : wd.γ_ExpPath ≤ capGammaExpPath c_deg φ_Const tools.pathDS φ_min M := by
    rw [hγE]
    exact max_le_max (hpds_mono.hγ_ExpPath_mono hφm_pos hφ_dec_ge hOK0.φ_dec_le hm0_le)
      (hpds_mono.hγ_ExpPath_mono hφC_pos (hφC ▸ le_rfl) (hφC ▸ hOK0.φ_Const_le) hMW_le)
  have hγD_le : wd.γ_del ≤ capGammaDel c_deg φ_Const tools.pathDS φ_min M := by
    rw [hγD]
    exact max_le_max (hpds_mono.hγ_del_mono hφm_pos hφ_dec_ge hOK0.φ_dec_le hm0_le)
      (hpds_mono.hγ_del_mono hφC_pos (hφC ▸ le_rfl) (hφC ▸ hOK0.φ_Const_le) hMW_le)
  have hη1_le : eta1Bound wd inp.J ≤ capEta1 c_deg φ_min M := by
    unfold eta1Bound capEta1; rw [hcdeg]
    have hc_nn : 0 ≤ c_deg := by dsimp only [c_deg]; positivity
    have hdiv : c_deg * (inp.J.m : ℝ) / (2 * wd.φ_dec) ≤ c_deg * (M : ℝ) / (2 * φ_min) :=
      div_le_div₀ (mul_nonneg hc_nn (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hJm) hc_nn)
        (by linarith only [hφm_pos]) (by linarith only [hφ_dec_ge])
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _
      (Nat.add_le_add_right (Nat.log_mono_right (Nat.add_le_add_right (Nat.ceil_mono hdiv) 1)) 1)) 1
  have hη2_le : eta2Bound inp.J ≤ capEta2 M := by
    unfold eta2Bound capEta2
    exact Nat.add_le_add_left (Nat.mul_le_mul_left 2
      (Nat.add_le_add_right (Nat.log_mono_right (Nat.add_le_add_right hJm 1)) 1)) 1
  have hγE_nn : 0 ≤ wd.γ_ExpPath := le_trans (div_nonneg zero_le_one hOK0.φ_ds_pos.le) hOK0.γ_ExpPath_ge
  have hsq_γ : wd.γ_ExpPath ^ 2 ≤ γ_ℓ := by
    unfold γ_ℓ capGammaL; nlinarith only [hγE_le, hγE_nn]
  have hlen_cap : (length inp.J (compose wd.W (fun eW => (embWJ eW).mapEdges (flatEdges embWJ wd.W.m).dedup.idxOf) embJW) : ℝ) ≤ γ_ℓ :=
    le_trans hlenJJ hsq_γ
  have hvc_cap : vcong inp.J inp.H' (fun _ => 1)
      (compose (subgraphOf inp.J (flatEdges embWJ wd.W.m).dedup)
        (restrictEmb inp.embJH (flatEdges embWJ wd.W.m).dedup)
        (compose wd.W (fun eW => (embWJ eW).mapEdges (flatEdges embWJ wd.W.m).dedup.idxOf) embJW)) ≤
      γ_c * (length inp.J inp.embJH : ℝ) *
        (vcong inp.J inp.H' (fun _ => 1) inp.embJH + (maxDeg inp.J : ℝ)) := by
    have hφ_cap_pos : 0 < capPhiDS c_deg φ_Const tools.pathDS φ_min M := capPhiDS_pos hφC_pos hφm_pos M
    have hprod_eq : (((eta1Bound wd inp.J : ℝ) + 1 / 2) * ((eta2Bound inp.J : ℝ) + 1 / 2)) *
        wd.τ₁ * wd.τ₂ =
        (2 * ((eta1Bound wd inp.J : ℝ) + 1 / 2) * ((eta2Bound inp.J : ℝ) + 1 / 2) *
          wd.γ_ExpPath ^ 2 * wd.γ_del ^ 2 / wd.φ_ds ^ 2) *
        (length inp.J inp.embJH : ℝ) *
        (vcong inp.J inp.H' (fun _ => 1) inp.embJH + (maxDeg inp.J : ℝ)) := by
      rw [hτ1, hτ2]; ring
    have hγc_mono : 2 * ((eta1Bound wd inp.J : ℝ) + 1 / 2) * ((eta2Bound inp.J : ℝ) + 1 / 2) *
        wd.γ_ExpPath ^ 2 * wd.γ_del ^ 2 / wd.φ_ds ^ 2 ≤ γ_c := by
      unfold γ_c capGammaC
      have hη1_r : (eta1Bound wd inp.J : ℝ) + 1 / 2 ≤ (capEta1 c_deg φ_min M : ℝ) + 1 / 2 := by
        linarith [show (eta1Bound wd inp.J : ℝ) ≤ (capEta1 c_deg φ_min M : ℝ) by exact_mod_cast hη1_le]
      have hη2_r : (eta2Bound inp.J : ℝ) + 1 / 2 ≤ (capEta2 M : ℝ) + 1 / 2 := by
        linarith [show (eta2Bound inp.J : ℝ) ≤ (capEta2 M : ℝ) by exact_mod_cast hη2_le]
      have hγD_nn : 0 ≤ wd.γ_del := le_trans zero_le_one hOK0.γ_del_ge
      have hnum : 2 * ((eta1Bound wd inp.J : ℝ) + 1 / 2) * ((eta2Bound inp.J : ℝ) + 1 / 2) *
          wd.γ_ExpPath ^ 2 * wd.γ_del ^ 2 ≤
          2 * ((capEta1 c_deg φ_min M : ℝ) + 1 / 2) * ((capEta2 M : ℝ) + 1 / 2) *
          (capGammaExpPath c_deg φ_Const tools.pathDS φ_min M) ^ 2 *
          (capGammaDel c_deg φ_Const tools.pathDS φ_min M) ^ 2 := by
        have h1 : 2 * ((eta1Bound wd inp.J : ℝ) + 1 / 2) * ((eta2Bound inp.J : ℝ) + 1 / 2) ≤
            2 * ((capEta1 c_deg φ_min M : ℝ) + 1 / 2) * ((capEta2 M : ℝ) + 1 / 2) := by
          have ha : 0 ≤ (eta1Bound wd inp.J : ℝ) + 1 / 2 := by positivity
          have hb : 0 ≤ (eta2Bound inp.J : ℝ) + 1 / 2 := by positivity
          nlinarith only [hη1_r, hη2_r, ha, hb]
        have h2 : wd.γ_ExpPath ^ 2 ≤ (capGammaExpPath c_deg φ_Const tools.pathDS φ_min M) ^ 2 := by
          nlinarith only [hγE_le, hγE_nn]
        have h3 : wd.γ_del ^ 2 ≤ (capGammaDel c_deg φ_Const tools.pathDS φ_min M) ^ 2 := by
          nlinarith only [hγD_le, hγD_nn]
        have h4 := mul_le_mul h2 h3 (sq_nonneg _) (sq_nonneg _)
        have h5 := mul_le_mul h1 h4 (by positivity) (by positivity)
        linarith only [h5]
      exact div_le_div₀ (by positivity) hnum (sq_pos_of_pos hφ_cap_pos)
        (by nlinarith only [hφds_ge, hφ_cap_pos, hOK0.φ_ds_pos])
    have hfac_nn : 0 ≤ (length inp.J inp.embJH : ℝ) *
        (vcong inp.J inp.H' (fun _ => 1) inp.embJH + (maxDeg inp.J : ℝ)) := by
      have : 0 ≤ vcong inp.J inp.H' (fun _ => 1) inp.embJH := vcong_nonneg inp.J inp.H' (fun _ => 1) inp.embJH
      positivity
    rw [hprod_eq] at hvc
    exact le_trans hvc (by
      have := mul_le_mul_of_nonneg_right hγc_mono hfac_nn; linarith only [this])
  have hsp_cap : ((subgraphOf inp.J (flatEdges embWJ wd.W.m).dedup).m : ℝ) ≤
      K_s * (inp.J.n : ℝ) * γ_ℓ * (1 + Real.log ((inp.J.n : ℝ) + (inp.J.m : ℝ) + 2)) := by
    set L_log := 1 + Real.log ((inp.J.n : ℝ) + (inp.J.m : ℝ) + 2)
    have hL1 : 1 ≤ L_log := one_le_one_add_log inp.J.n inp.J.m
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hl2_le : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    have hlog_le : (Nat.log 2 ((stripLoops inp.J).m + 2) : ℝ) + 1 ≤ (1 / Real.log 2) * L_log := by
      have hpow : (2 : ℝ) ^ (Nat.log 2 ((stripLoops inp.J).m + 2)) ≤ ((stripLoops inp.J).m + 2 : ℝ) := by
        exact_mod_cast Nat.pow_log_le_self 2 (by omega)
      have hx : ((stripLoops inp.J).m + 2 : ℝ) ≤ (inp.J.n : ℝ) + (inp.J.m : ℝ) + 2 := by
        have hsm : (stripLoops inp.J).m ≤ inp.J.m := stripLoops_m_le inp.J
        have hn0 : (0 : ℝ) ≤ inp.J.n := Nat.cast_nonneg _
        have hsm_r : ((stripLoops inp.J).m : ℝ) ≤ (inp.J.m : ℝ) := by exact_mod_cast hsm
        linarith
      have hlg : (Nat.log 2 ((stripLoops inp.J).m + 2) : ℝ) * Real.log 2 ≤
          Real.log ((inp.J.n : ℝ) + (inp.J.m : ℝ) + 2) := by
        calc (Nat.log 2 ((stripLoops inp.J).m + 2) : ℝ) * Real.log 2
            = Real.log ((2 : ℝ) ^ (Nat.log 2 ((stripLoops inp.J).m + 2))) := (Real.log_pow 2 _).symm
          _ ≤ Real.log ((stripLoops inp.J).m + 2 : ℝ) := Real.log_le_log (by positivity) hpow
          _ ≤ Real.log ((inp.J.n : ℝ) + (inp.J.m : ℝ) + 2) := Real.log_le_log (by positivity) hx
      have ha : (Nat.log 2 ((stripLoops inp.J).m + 2) : ℝ) ≤
          Real.log ((inp.J.n : ℝ) + (inp.J.m : ℝ) + 2) / Real.log 2 := (le_div_iff₀ hl2).mpr hlg
      have hb : (1 : ℝ) ≤ 1 / Real.log 2 := (one_le_div hl2).mpr hl2_le
      have hrew : Real.log ((inp.J.n : ℝ) + (inp.J.m : ℝ) + 2) / Real.log 2 + 1 / Real.log 2 =
          (1 / Real.log 2) * L_log := by dsimp only [L_log]; ring
      linarith only [ha, hb, hrew]
    have hcℓ_nn : 0 ≤ impl.decompose.c_ℓ := le_trans (by norm_num) impl.decompose.hc_ℓ
    have hℓ_L : (wd.decomp.ℓ : ℝ) ≤ (impl.decompose.c_ℓ / Real.log 2) * L_log := by
      have h1 := mul_le_mul_of_nonneg_left hlog_le hcℓ_nn
      have h2 : impl.decompose.c_ℓ * ((1 / Real.log 2) * L_log) =
          (impl.decompose.c_ℓ / Real.log 2) * L_log := by ring
      linarith only [hℓ_le, h1, h2]
    have hφ_inv : 1 / wd.φ_dec ≤ wd.γ_ExpPath :=
      le_trans (one_div_le_one_div_of_le hOK0.φ_ds_pos hOK0.φ_ds_le_dec) hOK0.γ_ExpPath_ge
    have hγ_ge2 : 2 ≤ wd.γ_ExpPath := by
      have h1 : (2 : ℝ) ≤ 1 / wd.φ_ds := by
        rw [le_div_iff₀ hOK0.φ_ds_pos]; linarith only [hOK0.φ_ds_half]
      exact le_trans h1 hOK0.γ_ExpPath_ge
    have h1 : ((subgraphOf inp.J (flatEdges embWJ wd.W.m).dedup).m : ℝ) ≤
        ((inp.J.n : ℝ) + (wd.decomp.ℓ : ℝ) * c_deg * (inp.J.n : ℝ) / wd.φ_dec) * wd.γ_ExpPath := by
      rw [hcdeg] at hWm_n
      exact le_trans hJtm_le (mul_le_mul_of_nonneg_right hWm_n hγE_nn)
    have hn_nn : (0 : ℝ) ≤ inp.J.n := Nat.cast_nonneg _
    have hc_nn : 0 ≤ c_deg := by positivity
    have ht1 : (inp.J.n : ℝ) * wd.γ_ExpPath ≤ 1 * (inp.J.n : ℝ) * wd.γ_ExpPath ^ 2 * L_log := by
      have ha : wd.γ_ExpPath ≤ wd.γ_ExpPath ^ 2 := by nlinarith only [hγ_ge2]
      have hb : (inp.J.n : ℝ) * wd.γ_ExpPath ≤ (inp.J.n : ℝ) * wd.γ_ExpPath ^ 2 :=
        mul_le_mul_of_nonneg_left ha hn_nn
      have hc := le_mul_of_one_le_right (show 0 ≤ (inp.J.n : ℝ) * wd.γ_ExpPath ^ 2 by positivity) hL1
      linarith only [hb, hc]
    have ht2 : ((wd.decomp.ℓ : ℝ) * c_deg * (inp.J.n : ℝ) / wd.φ_dec) * wd.γ_ExpPath ≤
        (impl.decompose.c_ℓ * c_deg / Real.log 2) * (inp.J.n : ℝ) * wd.γ_ExpPath ^ 2 * L_log := by
      have hrew1 : ((wd.decomp.ℓ : ℝ) * c_deg * (inp.J.n : ℝ) / wd.φ_dec) * wd.γ_ExpPath =
          (c_deg * (inp.J.n : ℝ) * wd.γ_ExpPath) * ((wd.decomp.ℓ : ℝ) * (1 / wd.φ_dec)) := by ring
      have ha : (wd.decomp.ℓ : ℝ) * (1 / wd.φ_dec) ≤
          ((impl.decompose.c_ℓ / Real.log 2) * L_log) * wd.γ_ExpPath :=
        mul_le_mul hℓ_L hφ_inv (div_nonneg zero_le_one hOK0.φ_dec_pos.le) (by positivity)
      have hb := mul_le_mul_of_nonneg_left ha (show 0 ≤ c_deg * (inp.J.n : ℝ) * wd.γ_ExpPath by positivity)
      have hrew2 : (c_deg * (inp.J.n : ℝ) * wd.γ_ExpPath) * (((impl.decompose.c_ℓ / Real.log 2) * L_log) * wd.γ_ExpPath) =
          (impl.decompose.c_ℓ * c_deg / Real.log 2) * (inp.J.n : ℝ) * wd.γ_ExpPath ^ 2 * L_log := by ring
      linarith only [hrew1, hb, hrew2]
    have hsum : ((subgraphOf inp.J (flatEdges embWJ wd.W.m).dedup).m : ℝ) ≤
        K_s * (inp.J.n : ℝ) * wd.γ_ExpPath ^ 2 * L_log := by
      have hrew : K_s * (inp.J.n : ℝ) * wd.γ_ExpPath ^ 2 * L_log =
          1 * (inp.J.n : ℝ) * wd.γ_ExpPath ^ 2 * L_log +
          (impl.decompose.c_ℓ * c_deg / Real.log 2) * (inp.J.n : ℝ) * wd.γ_ExpPath ^ 2 * L_log := by
        dsimp only [K_s]; ring
      linarith only [h1, ht1, ht2, hrew]
    have hKs_nn : 0 ≤ K_s := by dsimp only [K_s]; positivity
    have hstep : K_s * (inp.J.n : ℝ) * wd.γ_ExpPath ^ 2 * L_log ≤ K_s * (inp.J.n : ℝ) * γ_ℓ * L_log :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq_γ (mul_nonneg hKs_nn hn_nn))
        (by linarith only [hL1])
    exact le_trans hsum hstep
  refine ⟨subgraphOf inp.J (flatEdges embWJ wd.W.m).dedup, (flatEdges embWJ wd.W.m).dedup,
    compose wd.W (fun eW => (embWJ eW).mapEdges (flatEdges embWJ wd.W.m).dedup.idxOf) embJW,
    hnd, hkept_lt, hJn, rfl, hJval, hEmbJJ, hvc_cap, hlen_cap, hsp_cap,
    h3r, hr_max, hZr, hagr, hpJ0, hpK0, hpE0, hpJ_r, hpK_r, hpE_r, hGsub, hkept, hEmbC, hBndC⟩

end MinCostFlow.Spanner
