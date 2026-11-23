module

public import MinCostFlow.HierPaths.RegimesQuery
public import MinCostFlow.HierPaths.RegimesDec
public import MinCostFlow.Expander.Section8Static

/-!
# The chain from the hierarchy, without `hPaths`

The chain of Section 8 of the paper takes the cited path data structure `Cited.DecrementalExpanderPaths`
(`hPaths`). Our path data structure is built from the hierarchy of embedded matchings, with the
parameters `hierParams a …`. This file states what we prove about it
(`HierPathDSExists`): for every `a ≥ 1` there is a `PathDSImpl` with these parameters whose
procedures are deterministic. From it we prove Theorem 8.1 in the two forms of
`Expander/Section8Static.lean`, with `HierPathDSExists` in place of `hPaths`:
`theorem_8_1_concrete_of_hier` and `theorem_8_1_concrete_with_time_of_hier`.

The constant `a` is chosen from `hDec`. The overhead of the decomposition is
`exp(C₀ log(m)^{2/3} log log m)` for a constant `C₀` of `hDec`, and it fits under `capGammaL^2`
once `a ≥ C₀` (`decFactor_le_capGammaL_sq_of_gExp_eq`). We take `a = max 1 a₀`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Expander

/-- An implementation of the path data structure with the parameters `hierParams a …` whose
procedures are all deterministic exists for every `a ≥ 1`. The RAM constants, the word constant
and the space functions are part of what exists. -/
def HierPathDSExists : Prop :=
  ∀ a : ℕ, 1 ≤ a →
    ∃ (K_init K_del K_query : ℝ) (hK_init : 0 ≤ K_init) (hK_del : 0 ≤ K_del)
      (hK_query : 0 ≤ K_query) (K_bounds cw : ℕ) (hcw_pos : 1 ≤ cw)
      (boundsSpace : ℕ → ℕ → ℕ) (initSpace delSpace querySpace : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ)
      (C_space c_space : ℕ) (hC_space : 1 ≤ C_space)
      (hb : ∀ d M, boundsSpace d M ≤ C_space * (d + M + 2) ^ c_space)
      (hi : ∀ phiNum phiDen n m M, 1 ≤ phiNum → phiNum ≤ phiDen →
        initSpace phiNum phiDen n m M ≤
          C_space * (phiDen + n + m + M + gammaHP a ((phiDen + phiNum - 1) / phiNum) M + 2) ^
            c_space)
      (hd : ∀ phiNum phiDen n m M, 1 ≤ phiNum → phiNum ≤ phiDen →
        delSpace phiNum phiDen n m M ≤
          C_space * (phiDen + n + m + M + gammaHP a ((phiDen + phiNum - 1) / phiNum) M + 2) ^
            c_space)
      (hq : ∀ phiNum phiDen n m M, 1 ≤ phiNum → phiNum ≤ phiDen →
        querySpace phiNum phiDen n m M ≤
          C_space * (phiDen + n + m + M + gammaHP a ((phiDen + phiNum - 1) / phiNum) M + 2) ^
            c_space)
      (impl : Spanner.PathDSImpl),
      impl.params = hierParams a K_init K_del K_query hK_init hK_del hK_query K_bounds cw hcw_pos
        boundsSpace initSpace delSpace querySpace C_space c_space hC_space hb hi hd hq ∧
      ∀ b, ∀ s ∈ impl.procs b, s.NoRand

/-- What the chain uses of `HierPathDSExists`: for every `a ≥ 1` a `PathDSImpl` with
`phiOutDen = gExp = gQuery = Γ`, `gDel = 1` and deterministic procedures. -/
theorem exists_pathDS_of_hier (hHier : HierPathDSExists) (a : ℕ) (ha : 1 ≤ a) :
    ∃ impl : Spanner.PathDSImpl,
      impl.params.phiOutDen = gammaHP a ∧ impl.params.gExp = gammaHP a ∧
      impl.params.gQuery = gammaHP a ∧ impl.params.gDel = (fun _ _ => 1) ∧
      ∀ b, ∀ s ∈ impl.procs b, s.NoRand := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, impl, hparams, hnr⟩ :=
    hHier a ha
  exact ⟨impl, by rw [hparams]; rfl, by rw [hparams]; rfl, by rw [hparams]; rfl,
    by rw [hparams]; rfl, hnr⟩

/-- The implementation the chain uses (`ExpanderDecompositionUsed` version): `a = max 1 a₀`, with
`a₀` from `decFactor_le_capGammaL_sq_of_gExp_eq`. -/
theorem exists_pathDS_for_chain_used (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (hHier : HierPathDSExists) :
    ∃ (pathDS : Spanner.PathDSImpl) (C_q : ℝ),
      ConsumerSubpolyAtRegimes pathDS.params.phiOutDen ∧
      ConsumerSubpolyAtRegimes pathDS.params.gExp ∧
      ConsumerSubpolyAtRegimes pathDS.params.gDel ∧
      0 < C_q ∧
      (∀ mMax : ℕ,
        Spanner.capGammaQuery 36 constructExpanderImpl.φ_Const
          (Spanner.pathDSTool_of_impl pathDS) ((decomposeImplUsed hDec).φ_lb mMax) mMax ≤
          Real.exp (C_q * Real.log (↑mMax + 2) ^ (8 / 9 : ℝ) *
            Real.log (Real.log (↑mMax + 2) + 2) ^ (4 / 3 : ℝ))) ∧
      (∀ mMax : ℕ, (decomposeImplUsed hDec).decFactor mMax ≤
        1 * Spanner.capGammaL 36 constructExpanderImpl.φ_Const
          (Spanner.pathDSTool_of_impl pathDS) ((decomposeImplUsed hDec).φ_lb mMax) mMax ^ 2) ∧
      (∀ φ M, 0 < φ →
        (Spanner.pathDSTool_of_impl pathDS).γ_query φ M =
          (Spanner.pathDSTool_of_impl pathDS).γ_ExpPath φ M) ∧
      (∀ b, ∀ s ∈ pathDS.procs b, s.NoRand) := by
  obtain ⟨a₀, hdec⟩ := decFactor_le_capGammaL_sq_of_gExp_eq hDec
  obtain ⟨pathDS, hphi, hexp, hquery, hdel, hnr⟩ :=
    exists_pathDS_of_hier hHier (max 1 a₀) (le_max_left 1 a₀)
  obtain ⟨C_q, hCq, hbd⟩ := capGammaQuery_bound_of_gQuery_eq hDec pathDS (max 1 a₀) hquery
  refine ⟨pathDS, C_q, ?_, ?_, ?_, hCq, hbd, hdec (max 1 a₀) (le_max_right 1 a₀) pathDS hexp,
    fun φ M _ => ?_, hnr⟩
  · rw [hphi]; exact gammaHP_at_regimes _
  · rw [hexp]; exact gammaHP_at_regimes _
  · rw [hdel]; exact one_at_regimes
  · simp only [Spanner.pathDSTool_of_impl, Spanner.PathDSParams.γ_query,
      Spanner.PathDSParams.γ_ExpPath, hquery, hexp]

/-- The implementation the chain uses (`Cited.ExpanderDecomposition` wrapper). -/
theorem exists_pathDS_for_chain (hDec : Cited.ExpanderDecomposition)
    (hHier : HierPathDSExists) :
    ∃ (pathDS : Spanner.PathDSImpl) (C_q : ℝ),
      ConsumerSubpolyAtRegimes pathDS.params.phiOutDen ∧
      ConsumerSubpolyAtRegimes pathDS.params.gExp ∧
      ConsumerSubpolyAtRegimes pathDS.params.gDel ∧
      0 < C_q ∧
      (∀ mMax : ℕ,
        Spanner.capGammaQuery 36 constructExpanderImpl.φ_Const
          (Spanner.pathDSTool_of_impl pathDS) ((decomposeImpl hDec).φ_lb mMax) mMax ≤
          Real.exp (C_q * Real.log (↑mMax + 2) ^ (8 / 9 : ℝ) *
            Real.log (Real.log (↑mMax + 2) + 2) ^ (4 / 3 : ℝ))) ∧
      (∀ mMax : ℕ, (decomposeImpl hDec).decFactor mMax ≤
        1 * Spanner.capGammaL 36 constructExpanderImpl.φ_Const
          (Spanner.pathDSTool_of_impl pathDS) ((decomposeImpl hDec).φ_lb mMax) mMax ^ 2) ∧
      (∀ φ M, 0 < φ →
        (Spanner.pathDSTool_of_impl pathDS).γ_query φ M =
          (Spanner.pathDSTool_of_impl pathDS).γ_ExpPath φ M) ∧
      (∀ b, ∀ s ∈ pathDS.procs b, s.NoRand) :=
  exists_pathDS_for_chain_used (.of_cited hDec) hHier

/-- **Theorem 8.1 (page 39) from the hierarchy (`ExpanderDecompositionUsed` version)**. -/
theorem theorem_8_1_concrete_of_hier_used
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed) (hHier : HierPathDSExists) :
    ∃ (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
      (params : ℕ → DynSpanner.SparsifyParams) (C_γ K_s K_t : ℝ),
      0 < C_γ ∧
      K_s = 1 + 36 / Real.log 2 ∧
      0 ≤ K_s ∧ 0 ≤ K_t ∧
      (∀ mMax : ℕ,
        (params mMax).K_s = K_s ∧
        (params mMax).p_s = 1 ∧
        (params mMax).K_t = K_t ∧
        (params mMax).p_t = 1 ∧
        (params mMax).γ_ℓ ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        (params mMax).γ_c ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        DynSpanner.SparsifySpec mMax (params mMax) sparsify) := by
  obtain ⟨pathDS, _, hphi, hexp, hdel, _, _, hdec, hγq, _⟩ := exists_pathDS_for_chain_used hDec hHier
  obtain ⟨C_γ, K_s, K_t, h1, h2, h3, h4, h5⟩ :=
    spannerToolImpl_theorem_8_1_of_dec_le hDec pathDS zero_le_one hphi hexp hdel hdec hγq
  exact ⟨_, _, C_γ, K_s, K_t, h1, h2, h3, h4, h5⟩

/-- **Theorem 8.1 (page 39) from the hierarchy, with each `GetPath` charged `γ_ExpPath`**. -/
theorem theorem_8_1_concrete_of_hier
    (hDec : Cited.ExpanderDecomposition) (hHier : HierPathDSExists) :
    ∃ (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
      (params : ℕ → DynSpanner.SparsifyParams) (C_γ K_s K_t : ℝ),
      0 < C_γ ∧
      K_s = 1 + 36 / Real.log 2 ∧
      0 ≤ K_s ∧ 0 ≤ K_t ∧
      (∀ mMax : ℕ,
        (params mMax).K_s = K_s ∧
        (params mMax).p_s = 1 ∧
        (params mMax).K_t = K_t ∧
        (params mMax).p_t = 1 ∧
        (params mMax).γ_ℓ ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        (params mMax).γ_c ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        DynSpanner.SparsifySpec mMax (params mMax) sparsify) :=
  theorem_8_1_concrete_of_hier_used (.of_cited hDec) hHier

/-- **Theorem 8.1 (page 39) with query time from the hierarchy (`ExpanderDecompositionUsed` version)**. -/
theorem theorem_8_1_concrete_with_time_of_hier_used
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed) (hHier : HierPathDSExists) :
    ∃ (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
      (params : ℕ → DynSpanner.SparsifyParams) (C_γ K_s K_t C_q : ℝ),
      0 < C_γ ∧
      K_s = 1 + 36 / Real.log 2 ∧
      0 ≤ K_s ∧ 0 ≤ K_t ∧ 0 < C_q ∧
      (∀ mMax : ℕ,
        (params mMax).K_s = K_s ∧
        (params mMax).p_s = 1 ∧
        (params mMax).K_t = K_t ∧
        (params mMax).p_t = 1 ∧
        (params mMax).γ_ℓ ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        (params mMax).γ_c ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        (params mMax).γ_t ≤ Real.exp (C_q * Real.log ((mMax : ℝ) + 2) ^ (8 / 9 : ℝ) *
          Real.log (Real.log ((mMax : ℝ) + 2) + 2) ^ (4 / 3 : ℝ)) ∧
        DynSpanner.SparsifySpecWithTime mMax (params mMax) sparsify) := by
  obtain ⟨pathDS, C_q, hphi, hexp, hdel, hCq, hbd, hdec, _, _⟩ :=
    exists_pathDS_for_chain_used hDec hHier
  obtain ⟨C_γ, K_s, K_t, h1, h2, h3, h4, h5⟩ :=
    spannerToolImpl_theorem_8_1_with_time_of_dec_le hDec pathDS zero_le_one hphi hexp hdel hbd
      hdec
  exact ⟨_, _, C_γ, K_s, K_t, C_q, h1, h2, h3, h4, hCq, h5⟩

/-- **Theorem 8.1 (page 39) from the hierarchy, with the query time of Theorem 8.6**. -/
theorem theorem_8_1_concrete_with_time_of_hier
    (hDec : Cited.ExpanderDecomposition) (hHier : HierPathDSExists) :
    ∃ (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
      (params : ℕ → DynSpanner.SparsifyParams) (C_γ K_s K_t C_q : ℝ),
      0 < C_γ ∧
      K_s = 1 + 36 / Real.log 2 ∧
      0 ≤ K_s ∧ 0 ≤ K_t ∧ 0 < C_q ∧
      (∀ mMax : ℕ,
        (params mMax).K_s = K_s ∧
        (params mMax).p_s = 1 ∧
        (params mMax).K_t = K_t ∧
        (params mMax).p_t = 1 ∧
        (params mMax).γ_ℓ ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        (params mMax).γ_c ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        (params mMax).γ_t ≤ Real.exp (C_q * Real.log ((mMax : ℝ) + 2) ^ (8 / 9 : ℝ) *
          Real.log (Real.log ((mMax : ℝ) + 2) + 2) ^ (4 / 3 : ℝ)) ∧
        DynSpanner.SparsifySpecWithTime mMax (params mMax) sparsify) :=
  theorem_8_1_concrete_with_time_of_hier_used (.of_cited hDec) hHier

end MinCostFlow.HierPaths
