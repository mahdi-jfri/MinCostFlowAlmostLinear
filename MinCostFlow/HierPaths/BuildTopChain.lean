module

public import MinCostFlow.HierPaths.BuildTopStatic
public import MinCostFlow.HierPaths.ImplParts
import MinCostFlow.HierPaths.InitProgCompleteCost
import MinCostFlow.HierPaths.QueryProgSpec
import MinCostFlow.HierPaths.DelProgSpec

/-!
# Consumer corollaries for `buildTopStatic_spec` (`buildTopMinA ≤ a`)

`buildTopStatic_spec` proves `StaticProcSpec a (buildTopStaticProc PL) …` for every
`a ≥ buildTopMinA` (`= 264`). This file verifies that restricting `a` to `a ≥ aMin` (in
particular `a ≥ buildTopMinA`) is completely harmless for the chain of Section 8 of the paper:

* `HierPathDSExistsFrom aMin`: the threshold variant of `HierPathDSExists` (`Chain.lean`)
  requiring a deterministic `PathDSImpl` with parameters `hierParams a …` for every `a ≥ aMin`.
* `hierPathDSExistsFrom_of_static`: combines any static builder for `a ≥ aMin` with the already
  verified `hierInitBlockBuilder_spec`, `hierDeleteProc_spec`, `hierQueryProc_spec`, and
  `gammaBoundsProcs`.
* `hierPathDSExistsFrom_of_level`: instantiates `hierPathDSExistsFrom_of_static` with
  `buildTopStatic_spec`, giving `HierPathDSExistsFrom buildTopMinA` directly from a level
  procedure meeting `ProvidesBuildLevel` and `BuildLevelSpacePoly`.
* `exists_pathDS_for_chain_from`, `theorem_8_1_concrete_of_hierFrom`, and
  `theorem_8_1_concrete_with_time_of_hierFrom`: choosing `a = max aMin a₀` gives the exact
  conclusions of `exists_pathDS_for_chain`, `theorem_8_1_concrete_of_hier`, and
  `theorem_8_1_concrete_with_time_of_hier` (`Chain.lean`).
* `theorem_8_1_concrete_of_level` and `theorem_8_1_concrete_with_time_of_level`: direct end-to-end
  corollaries from a level procedure meeting `ProvidesBuildLevel` and `BuildLevelSpacePoly`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Expander MinCostFlow.Spanner

/-- Threshold variant of `HierPathDSExists` (`Chain.lean`): a deterministic `PathDSImpl` with
parameters `hierParams a …` exists for every `a ≥ aMin`. -/
def HierPathDSExistsFrom (aMin : ℕ) : Prop :=
  ∀ a : ℕ, aMin ≤ a →
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

/-- Assembly of `HierPathDSExistsFrom aMin` from the three procedures (`Init`, `Delete`,
`GetPath`) for all `a ≥ aMin`. -/
theorem hierPathDSExistsFrom_of_procs {aMin : ℕ}
    (h : ∀ a : ℕ, aMin ≤ a → ∃ (PI PD PQ : HierProc) (KI KD KQ : ℝ)
      (sI sD sQ : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (CI cI CD cD CQ cQ cwI cwD cwQ : ℕ),
      InitProcSpec a PI KI sI CI cI cwI ∧ DelProcSpec a PD KD sD CD cD cwD ∧
        QueryProcSpec a PQ KQ sQ CQ cQ cwQ) :
    HierPathDSExistsFrom aMin := by
  intro a ha
  obtain ⟨PI, PD, PQ, KI, KD, KQ, sI, sD, sQ, CI, cI, CD, cD, CQ, cQ, cwI, cwD, cwQ,
    ⟨hnrI, hKI, hfI, hspecI⟩, ⟨hnrD, hKD, hfD, hspecD⟩, ⟨hnrQ, hKQ, hfQ, hspecQ⟩⟩ := h a ha
  let hc := assembleConsts a KI KD KQ hKI hKD hKQ sI sD sQ CI cI CD cD CQ cQ cwI cwD cwQ hfI hfD hfQ
  have hcwI : cwI ≤ hc.cw := by simp only [hc, assembleConsts]; omega
  have hcwD : cwD ≤ hc.cw := by simp only [hc, assembleConsts]; omega
  have hcwQ : cwQ ≤ hc.cw := by simp only [hc, assembleConsts]; omega
  have hcw3 : 3 ≤ hc.cw := by simp only [hc, assembleConsts]; omega
  let impl : PathDSImpl :=
    { params := hc.params
      R := hierRep a
      procs := hierProcs PI PD PQ
      hprocs_len := fun b => by simp [hierProcs]
      spec := fun w p b hp => by
        obtain ⟨hI, hD, hQ⟩ := hierProcs_at hp
        refine implements_of_clauses (hierRep_local a)
          (hspecI hc rfl rfl hcwI w p b _ hI) (fun i => ?_)
        match i with
        | 0 => exact hspecD hc rfl rfl hcwD w p (b + 1) _ hD
        | 1 => exact hspecQ hc rfl rfl hcwQ w p (b + 2) _ hQ
        | i + 2 =>
          intro _ _ _ _ _ _ _ _ _ _ hpre
          exact hpre.elim
      boundsProcs := fun _ => gammaBoundsProcs a
      hbounds_nonempty := fun _ => gammaBoundsProcs_nonempty a
      hbounds_noRand := fun _ => gammaBoundsProcs_noRand a
      boundsSpec := fun w p bB hp =>
        hierParams_boundsSpec a hcw3 (le_refl 1000) (fun _ _ => le_refl 3) w p bB hp }
  refine ⟨hc.K_init, hc.K_del, hc.K_query, hc.hK_init, hc.hK_del, hc.hK_query, hc.K_bounds,
    hc.cw, hc.hcw_pos, hc.boundsSpace, hc.initSpace, hc.delSpace, hc.querySpace, hc.C_space,
    hc.c_space, hc.hC_space, hc.hb, hc.hi, hc.hd, hc.hq, impl, rfl, fun b s hs => ?_⟩
  simp only [impl, hierProcs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with (((rfl | rfl | rfl) | hs) | hs) | hs
  · exact (hnrI _).1
  · exact (hnrD _).1
  · exact (hnrQ _).1
  · exact (hnrI _).2 s hs
  · exact (hnrD _).2 s hs
  · exact (hnrQ _).2 s hs

/-- A deterministic static builder meeting `StaticProcSpec` for all `a ≥ aMin` (with `1 ≤ aMin`)
combines with the verified block builder, `Delete`, and `GetPath` procedures to give
`HierPathDSExistsFrom aMin`. -/
theorem hierPathDSExistsFrom_of_static {aMin : ℕ} (haMin : 1 ≤ aMin)
    (h : ∀ a : ℕ, aMin ≤ a → ∃ (PS : HierProc) (Ks : ℕ)
      (sS : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (CS cS cwS : ℕ),
      StaticProcSpec a PS Ks sS CS cS cwS) :
    HierPathDSExistsFrom aMin := by
  refine hierPathDSExistsFrom_of_procs fun a ha => ?_
  have ha1 : 1 ≤ a := haMin.trans ha
  obtain ⟨PS, Ks, sS, CS, cS, cwS, hS⟩ := h a ha
  have hR : RestProcSpec a (restProc (hierInitBuilder a ha1 (initMiddleWriters a)))
      (40000 + 80) (hierBuilderSpace a) 300000 2 :=
    restProc_spec a _ 40000 (hierBuilderSpace a) 300000 2 (hierInitBlockBuilder_spec a ha1)
  have hI := initProc_spec a ha1 PS (restProc (hierInitBuilder a ha1 (initMiddleWriters a)))
    Ks (40000 + 80) 2000 sS (hierBuilderSpace a) (blockSpace a) CS cS 300000 2 2000 2 cwS
    hS hR (blockSpace_form a)
    (fun S G phiNum phiDen M hg => length_initBlock_le S ha1 G phiNum phiDen hg)
    (fun S G phiNum phiDen M hg => length_initBlock_le S ha1 G phiNum phiDen hg)
  exact ⟨initProc PS (restProc (hierInitBuilder a ha1 (initMiddleWriters a))),
    hierDeleteProc, hierQueryProc, _, 106496, 10000, _, hierDeleteSpace, hierQuerySpace a,
    _, _, 11 * 16 ^ 12, 12, 9, 1, cwS, 1, 1, hI, hierDeleteProc_spec a, hierQueryProc_spec a⟩

/-- End-to-end hierarchy assembly from a single level procedure meeting `ProvidesBuildLevel`
and `BuildLevelSpacePoly`, via `buildTopStatic_spec`. -/
theorem hierPathDSExistsFrom_of_level {K Cs cs : ℕ} {space : Cited.Graph → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}
    {PL : HierProc}
    (hPL_nr : PL.NoRand)
    (hPL_spec : ∀ w p j k, PL.At p j k → ProvidesBuildLevel w K space p j)
    (hSpPoly : BuildLevelSpacePoly space Cs cs) :
    HierPathDSExistsFrom buildTopMinA :=
  hierPathDSExistsFrom_of_static one_le_buildTopMinA fun a ha =>
    ⟨buildTopStaticProc PL, 2 ^ 20 * (K + 1), buildTopStaticSpace K Cs cs a,
      (50000 + 2 ^ 15 * (K + 1)) + 5 * Cs * 2000 ^ cs, max 4 (2 * cs + 2), 1,
      buildTopStatic_spec hPL_nr hPL_spec hSpPoly a ha⟩

/-- Extracting a `PathDSImpl` from `HierPathDSExistsFrom aMin` at any `a ≥ aMin`. -/
theorem exists_pathDS_of_hierFrom {aMin : ℕ} (hHier : HierPathDSExistsFrom aMin)
    (a : ℕ) (ha : aMin ≤ a) :
    ∃ impl : Spanner.PathDSImpl,
      impl.params.phiOutDen = gammaHP a ∧ impl.params.gExp = gammaHP a ∧
      impl.params.gQuery = gammaHP a ∧ impl.params.gDel = (fun _ _ => 1) ∧
      ∀ b, ∀ s ∈ impl.procs b, s.NoRand := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, impl, hparams, hnr⟩ :=
    hHier a ha
  exact ⟨impl, by rw [hparams]; rfl, by rw [hparams]; rfl, by rw [hparams]; rfl,
    by rw [hparams]; rfl, hnr⟩

/-- Exact conclusion of `exists_pathDS_for_chain_used` from `HierPathDSExistsFrom aMin` and
`ExpanderDecompositionUsed`, choosing `a = max aMin a₀`. -/
theorem exists_pathDS_for_chain_from_used {aMin : ℕ}
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed) (hHier : HierPathDSExistsFrom aMin) :
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
    exists_pathDS_of_hierFrom hHier (max aMin a₀) (le_max_left aMin a₀)
  obtain ⟨C_q, hCq, hbd⟩ := capGammaQuery_bound_of_gQuery_eq hDec pathDS (max aMin a₀) hquery
  refine ⟨pathDS, C_q, ?_, ?_, ?_, hCq, hbd, hdec (max aMin a₀) (le_max_right aMin a₀) pathDS hexp,
    fun φ M _ => ?_, hnr⟩
  · rw [hphi]; exact gammaHP_at_regimes _
  · rw [hexp]; exact gammaHP_at_regimes _
  · rw [hdel]; exact one_at_regimes
  · simp only [Spanner.pathDSTool_of_impl, Spanner.PathDSParams.γ_query,
      Spanner.PathDSParams.γ_ExpPath, hquery, hexp]

/-- Exact conclusion of `exists_pathDS_for_chain` (`Chain.lean`) from `HierPathDSExistsFrom aMin`. -/
theorem exists_pathDS_for_chain_from {aMin : ℕ}
    (hDec : Cited.ExpanderDecomposition) (hHier : HierPathDSExistsFrom aMin) :
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
  exists_pathDS_for_chain_from_used (.of_cited hDec) hHier

/-- **Theorem 8.1 (page 39) from `HierPathDSExistsFrom aMin` and `ExpanderDecompositionUsed`**. -/
theorem theorem_8_1_concrete_of_hierFrom_used {aMin : ℕ}
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed) (hHier : HierPathDSExistsFrom aMin) :
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
  obtain ⟨pathDS, _, hphi, hexp, hdel, _, _, hdec, hγq, _⟩ :=
    exists_pathDS_for_chain_from_used hDec hHier
  obtain ⟨C_γ, K_s, K_t, h1, h2, h3, h4, h5⟩ :=
    spannerToolImpl_theorem_8_1_of_dec_le hDec pathDS zero_le_one hphi hexp hdel hdec hγq
  exact ⟨_, _, C_γ, K_s, K_t, h1, h2, h3, h4, h5⟩

/-- **Theorem 8.1 (page 39) from `HierPathDSExistsFrom aMin`**, with the exact conclusion of
`theorem_8_1_concrete_of_hier` (`Chain.lean`). -/
theorem theorem_8_1_concrete_of_hierFrom {aMin : ℕ}
    (hDec : Cited.ExpanderDecomposition) (hHier : HierPathDSExistsFrom aMin) :
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
  theorem_8_1_concrete_of_hierFrom_used (.of_cited hDec) hHier

/-- **Theorem 8.1 (page 39) with query time from `HierPathDSExistsFrom aMin` and
`ExpanderDecompositionUsed`**. -/
theorem theorem_8_1_concrete_with_time_of_hierFrom_used {aMin : ℕ}
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed) (hHier : HierPathDSExistsFrom aMin) :
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
    exists_pathDS_for_chain_from_used hDec hHier
  obtain ⟨C_γ, K_s, K_t, h1, h2, h3, h4, h5⟩ :=
    spannerToolImpl_theorem_8_1_with_time_of_dec_le hDec pathDS zero_le_one hphi hexp hdel hbd
      hdec
  exact ⟨_, _, C_γ, K_s, K_t, C_q, h1, h2, h3, h4, hCq, h5⟩

/-- **Theorem 8.1 (page 39) with query time from `HierPathDSExistsFrom aMin`**, with the exact
conclusion of `theorem_8_1_concrete_with_time_of_hier` (`Chain.lean`). -/
theorem theorem_8_1_concrete_with_time_of_hierFrom {aMin : ℕ}
    (hDec : Cited.ExpanderDecomposition) (hHier : HierPathDSExistsFrom aMin) :
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
  theorem_8_1_concrete_with_time_of_hierFrom_used (.of_cited hDec) hHier

/-- **Theorem 8.1 (page 39) directly from a level builder** meeting `ProvidesBuildLevel` and
`BuildLevelSpacePoly`. -/
theorem theorem_8_1_concrete_of_level {K Cs cs : ℕ} {space : Cited.Graph → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}
    {PL : HierProc}
    (hDec : Cited.ExpanderDecomposition)
    (hPL_nr : PL.NoRand)
    (hPL_spec : ∀ w p j k, PL.At p j k → ProvidesBuildLevel w K space p j)
    (hSpPoly : BuildLevelSpacePoly space Cs cs) :
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
  theorem_8_1_concrete_of_hierFrom hDec (hierPathDSExistsFrom_of_level hPL_nr hPL_spec hSpPoly)

/-- **Theorem 8.1 (page 39) with query time directly from a level builder** meeting
`ProvidesBuildLevel` and `BuildLevelSpacePoly`. -/
theorem theorem_8_1_concrete_with_time_of_level {K Cs cs : ℕ} {space : Cited.Graph → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}
    {PL : HierProc}
    (hDec : Cited.ExpanderDecomposition)
    (hPL_nr : PL.NoRand)
    (hPL_spec : ∀ w p j k, PL.At p j k → ProvidesBuildLevel w K space p j)
    (hSpPoly : BuildLevelSpacePoly space Cs cs) :
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
  theorem_8_1_concrete_with_time_of_hierFrom hDec
    (hierPathDSExistsFrom_of_level hPL_nr hPL_spec hSpPoly)

end MinCostFlow.HierPaths
