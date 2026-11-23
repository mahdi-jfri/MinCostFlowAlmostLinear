module

public import MinCostFlow.Spanner.ProgSparsifyGuest
public import MinCostFlow.DynSpanner.Program.CanonicalSparsify
public import MinCostFlow.HierPaths.BuildFinal
public import MinCostFlow.Expander.SpannerToolImplProg

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The sparsifier program of Section 8 as a `SparsifyImpl`

The chain of Section 5 calls `Sparsify(H', J, Π_{J → H'})` of Theorem 8.1 (page 39) through a
Word-RAM program `impl : SparsifyImpl` (`SparsifyContract.lean`). The chain asks that the
parameters `canonicalSparsifyParams impl` have `p_s = p_t = 1`, constant `K_s` and `K_t`, unit
time factor `γ_t = 1`, and `γ_ℓ, γ_c ≤ exp(C log^{7/8}(m + 2))`.

Here we build this program from the tools of Section 8 and prove these facts.

* The tools are `spannerToolImpl_of_pathDS` with the proved expander decomposition
  `expanderDecompositionUsed_holds` (Theorem 8.5, page 41) and the path data structure of
  `exists_pathDS_for_chain_unconditional` (Theorem 8.6, page 41).
* The program is `sparsifyImplOfTools` on these tools (Algorithm 4, page 42). It needs a
  subpolynomial bound on `1 / φ_lb`, which we get from `decomposeImpl_phi_lb_subpoly`
  (`decomposeImplUsed_invPhiBound`), and the fact that the three tools make no random choices.
* The time factor `γ_t` is a maximum of three terms (`sparsifyGuestGammaT`). The path data
  structure answers queries as fast as it builds paths (`γ_query = γ_ExpPath`), so the second
  term is `1`. The decomposition is not slower than `γ_ℓ²` (`decFactor ≤ γ_ℓ²`), so the third
  term is at most `1`. Hence `γ_t = 1` (`sparsifyImplUsed_γ_t`).
* The bounds on `γ_ℓ` and `γ_c` are the ones that `spannerToolImpl_theorem_8_1_of_dec_le`
  proves for the same tools, since the program uses the same factors `capGammaL` and `capGammaC`.

The main result is `sparsifyImplUsed_hp_spec`, in the form of the hypothesis `hp_spec` of
`concreteChainWitnessWithLastOf`, and `sparsifyImplUsed_sparsifySpec`, its hypothesis
`hsparsify`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM MinCostFlow.Spanner MinCostFlow.Expander

public section

/-! ## The inverse conductance bound of the decomposition -/

/-- The bound of Theorem 8.5 (page 41) on the conductance of the decomposition program
`decomposeImplUsed hDec`: `1 / φ_lb m ≤ C₁ · exp(C₀ log^{2/3}(m + 2) · log(log(m + 2) + 2))`.
The constants are those of `decomposeImpl_phi_lb_subpoly`. -/
noncomputable def decomposeImplUsed_invPhiBound (hDec : ExpanderDecomp.ExpanderDecompositionUsed) :
    (decomposeImplUsed hDec).InvPhiBound :=
  let h := decomposeImpl_phi_lb_subpoly hDec
  { invPhiC := Classical.choose (Classical.choose_spec h)
    invPhiExp := Classical.choose h
    hinvPhiC := lt_of_lt_of_le zero_lt_one (Classical.choose_spec (Classical.choose_spec h)).2.1
    hinvPhiExp := (Classical.choose_spec (Classical.choose_spec h)).1.le
    hinvPhi_le := (Classical.choose_spec (Classical.choose_spec h)).2.2 }

/-! ## The tools -/

/-- The path data structure of Theorem 8.6 (page 41) given by
`exists_pathDS_for_chain_unconditional`. -/
noncomputable def sparsifyPathDSUsed : Spanner.PathDSImpl :=
  Classical.choose HierPaths.exists_pathDS_for_chain_unconditional

/-- The properties of `sparsifyPathDSUsed` from `exists_pathDS_for_chain_unconditional`. -/
theorem sparsifyPathDSUsed_spec :
    ∃ C_q : ℝ,
      ConsumerSubpolyAtRegimes sparsifyPathDSUsed.params.phiOutDen ∧
      ConsumerSubpolyAtRegimes sparsifyPathDSUsed.params.gExp ∧
      ConsumerSubpolyAtRegimes sparsifyPathDSUsed.params.gDel ∧
      0 < C_q ∧
      (∀ mMax : ℕ,
        capGammaQuery 36 constructExpanderImpl.φ_Const
          (pathDSTool_of_impl sparsifyPathDSUsed)
          ((decomposeImplUsed ExpanderDecomp.expanderDecompositionUsed_holds).φ_lb mMax) mMax ≤
          Real.exp (C_q * Real.log (↑mMax + 2) ^ (8 / 9 : ℝ) *
            Real.log (Real.log (↑mMax + 2) + 2) ^ (4 / 3 : ℝ))) ∧
      (∀ mMax : ℕ, (decomposeImplUsed ExpanderDecomp.expanderDecompositionUsed_holds).decFactor mMax ≤
        1 * capGammaL 36 constructExpanderImpl.φ_Const
          (pathDSTool_of_impl sparsifyPathDSUsed)
          ((decomposeImplUsed ExpanderDecomp.expanderDecompositionUsed_holds).φ_lb mMax) mMax ^ 2) ∧
      (∀ φ M, 0 < φ →
        (pathDSTool_of_impl sparsifyPathDSUsed).γ_query φ M =
          (pathDSTool_of_impl sparsifyPathDSUsed).γ_ExpPath φ M) ∧
      (∀ b, ∀ s ∈ sparsifyPathDSUsed.procs b, s.NoRand) ∧
      sparsifyPathDSUsed.params.cw = 3 :=
  Classical.choose_spec HierPaths.exists_pathDS_for_chain_unconditional

/-- Determinism (`Stmt.NoRand`) of every procedure of `sparsifyPathDSUsed`. -/
theorem sparsifyPathDSUsed_noRand (b : ℕ) :
    ∀ s ∈ sparsifyPathDSUsed.procs b, s.NoRand := by
  obtain ⟨_, _, _, _, _, _, _, _, hnr, _⟩ := sparsifyPathDSUsed_spec
  exact hnr b

/-- Word-width multiplier of `sparsifyPathDSUsed` (`cw = 3`). -/
theorem sparsifyPathDSUsed_cw : sparsifyPathDSUsed.params.cw = 3 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hcw⟩ := sparsifyPathDSUsed_spec
  exact hcw

/-- Subpolynomial regime bound on `sparsifyPathDSUsed.params.phiOutDen`. -/
theorem sparsifyPathDSUsed_phiOutDen_regimes :
    ConsumerSubpolyAtRegimes sparsifyPathDSUsed.params.phiOutDen := by
  obtain ⟨_, h, _, _, _, _, _, _, _, _⟩ := sparsifyPathDSUsed_spec
  exact h

/-- Subpolynomial regime bound on `sparsifyPathDSUsed.params.gExp`. -/
theorem sparsifyPathDSUsed_gExp_regimes :
    ConsumerSubpolyAtRegimes sparsifyPathDSUsed.params.gExp := by
  obtain ⟨_, _, h, _, _, _, _, _, _, _⟩ := sparsifyPathDSUsed_spec
  exact h

/-- Subpolynomial regime bound on `sparsifyPathDSUsed.params.gDel`. -/
theorem sparsifyPathDSUsed_gDel_regimes :
    ConsumerSubpolyAtRegimes sparsifyPathDSUsed.params.gDel := by
  obtain ⟨_, _, _, h, _, _, _, _, _, _⟩ := sparsifyPathDSUsed_spec
  exact h

/-- Decomposition factor bound `decFactor mMax ≤ 1 * capGammaL²` for `sparsifyPathDSUsed`. -/
theorem sparsifyPathDSUsed_decFactor_le (mMax : ℕ) :
    (decomposeImplUsed ExpanderDecomp.expanderDecompositionUsed_holds).decFactor mMax ≤
      1 * capGammaL 36 constructExpanderImpl.φ_Const
        (pathDSTool_of_impl sparsifyPathDSUsed)
        ((decomposeImplUsed ExpanderDecomp.expanderDecompositionUsed_holds).φ_lb mMax) mMax ^ 2 := by
  obtain ⟨_, _, _, _, _, _, h, _, _, _⟩ := sparsifyPathDSUsed_spec
  exact h mMax

/-- Query factor equals path factor (`γ_query = γ_ExpPath`) for `sparsifyPathDSUsed`. -/
theorem sparsifyPathDSUsed_γ_query_eq (φ : ℝ) (M : ℕ) (hφ : 0 < φ) :
    (pathDSTool_of_impl sparsifyPathDSUsed).γ_query φ M =
      (pathDSTool_of_impl sparsifyPathDSUsed).γ_ExpPath φ M := by
  obtain ⟨_, _, _, _, _, _, _, h, _, _⟩ := sparsifyPathDSUsed_spec
  exact h φ M hφ

/-- The three tools of Algorithm 4 (page 42): `ConstructExpander` (Theorem 8.4), `Decompose`
(Theorem 8.5) and the path data structure (Theorem 8.6). -/
noncomputable def spannerToolImplUsed : SpannerToolImpl :=
  spannerToolImpl_of_pathDS ExpanderDecomp.expanderDecompositionUsed_holds sparsifyPathDSUsed

/-! ## The program -/

/-- The Word-RAM program of `Sparsify` (Algorithm 4, page 42) on the tools
`spannerToolImplUsed`, as a `SparsifyImpl`. -/
noncomputable def sparsifyImplUsed : SparsifyImpl :=
  sparsifyImplOfTools spannerToolImplUsed
    (decomposeImplUsed_invPhiBound ExpanderDecomp.expanderDecompositionUsed_holds)
    (spannerToolImpl_decompose_noRand _ _ _)
    (spannerToolImpl_constructExpander_noRand _ _ _)
    (sparsifyPathDSUsed_noRand _)

theorem sparsifyImplUsed_p_s : sparsifyImplUsed.p_s = 1 := by
  unfold sparsifyImplUsed
  exact sparsifyImplOfTools_p_s _ _ _ _ _

theorem sparsifyImplUsed_p_t : sparsifyImplUsed.p_t = 1 := by
  unfold sparsifyImplUsed
  exact sparsifyImplOfTools_p_t _ _ _ _ _

/-- The sparsity constant is `K_s = 1 + 36 / log 2`, since `c_ℓ = 1` and the expanders of
Theorem 8.4 have degree constant `36`. -/
theorem sparsifyImplUsed_K_s : sparsifyImplUsed.K_s = 1 + 36 / Real.log 2 := by
  change 1 + (decomposeImplUsed ExpanderDecomp.expanderDecompositionUsed_holds).c_ℓ *
    (2 * (constructExpanderImpl.c_deg_int : ℝ)) / Real.log 2 = 1 + 36 / Real.log 2
  rw [decomposeImplUsed_c_ell, constructExpanderImpl_c_deg_int]
  norm_num

/-! ## Unit time factor -/

private theorem two_mul_c_deg_int : (2 * (constructExpanderImpl.c_deg_int : ℝ)) = 36 := by
  rw [constructExpanderImpl_c_deg_int]
  norm_num

/-- The time factor of `sparsifyImplUsed` is `1` at every edge cap. The query factor equals the
path factor (`γ_query = γ_ExpPath`), and the decomposition factor is at most `γ_ℓ²`
(`decFactor ≤ 1 · capGammaL²`), both from `exists_pathDS_for_chain_unconditional`. -/
theorem sparsifyImplUsed_γ_t (m : ℕ) : sparsifyImplUsed.γ_t m = 1 := by
  have hdec_le := sparsifyPathDSUsed_decFactor_le
  have hγq := sparsifyPathDSUsed_γ_query_eq
  set hD := ExpanderDecomp.expanderDecompositionUsed_holds
  set φ_m := (decomposeImplUsed hD).φ_lb m
  set φ_C := constructExpanderImpl.φ_Const
  set pds := pathDSTool_of_impl sparsifyPathDSUsed
  have hφm : 0 < φ_m := (decomposeImplUsed hD).hφ_lb_pos m
  have hφC : 0 < φ_C := constructExpanderImpl.hφ_Const_pos
  have hq : capGammaQuery 36 φ_C pds φ_m m = capGammaExpPath 36 φ_C pds φ_m m := by
    unfold capGammaQuery capGammaExpPath
    rw [hγq _ _ hφm, hγq _ _ hφC]
  have hE : 0 < capGammaExpPath 36 φ_C pds φ_m m :=
    lt_of_lt_of_le two_pos (two_le_capGammaExpPath hφC hφm m)
  have hL : 0 < capGammaL 36 φ_C pds φ_m m :=
    lt_of_lt_of_le (by norm_num) (four_le_capGammaL hφC hφm m)
  have hdec : (decomposeImplUsed hD).decFactor m / capGammaL 36 φ_C pds φ_m m ^ 2 ≤ 1 := by
    rw [div_le_one (pow_pos hL 2)]
    simpa using hdec_le m
  change max (max 1 (capGammaQuery (2 * (constructExpanderImpl.c_deg_int : ℝ)) φ_C pds φ_m m /
      capGammaExpPath (2 * (constructExpanderImpl.c_deg_int : ℝ)) φ_C pds φ_m m))
    ((decomposeImplUsed hD).decFactor m /
      capGammaL (2 * (constructExpanderImpl.c_deg_int : ℝ)) φ_C pds φ_m m ^ 2) = 1
  rw [two_mul_c_deg_int, hq, div_self hE.ne', max_self]
  exact max_eq_left hdec

/-- The length factor of `sparsifyImplUsed` at edge cap `m` equals `capGammaL` with expander degree
constant `36`, `constructExpanderImpl.φ_Const`, `sparsifyPathDSUsed`, and
`(decomposeImplUsed expanderDecompositionUsed_holds).φ_lb m`. -/
theorem sparsifyImplUsed_γ_ℓ (m : ℕ) :
    sparsifyImplUsed.γ_ℓ m =
      capGammaL 36 constructExpanderImpl.φ_Const
        (pathDSTool_of_impl sparsifyPathDSUsed)
        ((decomposeImplUsed ExpanderDecomp.expanderDecompositionUsed_holds).φ_lb m) m := by
  change capGammaL (2 * (constructExpanderImpl.c_deg_int : ℝ))
    constructExpanderImpl.φ_Const (pathDSTool_of_impl sparsifyPathDSUsed)
    ((decomposeImplUsed ExpanderDecomp.expanderDecompositionUsed_holds).φ_lb m) m = _
  rw [two_mul_c_deg_int]

/-! ## The bounds on `γ_ℓ` and `γ_c` -/

/-- The length factor and the congestion factor of `sparsifyImplUsed` are at most
`exp(C log^{7/8}(m + 2))` (Theorem 8.1, page 39). These are the bounds of
`spannerToolImpl_theorem_8_1_of_dec_le` for the same tools: the program uses the same factors
`capGammaL` and `capGammaC`. -/
theorem sparsifyImplUsed_gamma_bound :
    ∃ C_sp : ℝ, 0 < C_sp ∧ ∀ m : ℕ,
      sparsifyImplUsed.γ_ℓ m ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
      sparsifyImplUsed.γ_c m + 1 ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
  obtain ⟨C_γ, _, _, hCγ, _, _, _, h⟩ :=
    spannerToolImpl_theorem_8_1_of_dec_le ExpanderDecomp.expanderDecompositionUsed_holds
      sparsifyPathDSUsed zero_le_one
      sparsifyPathDSUsed_phiOutDen_regimes sparsifyPathDSUsed_gExp_regimes
      sparsifyPathDSUsed_gDel_regimes sparsifyPathDSUsed_decFactor_le sparsifyPathDSUsed_γ_query_eq
  exact ⟨C_γ, hCγ, fun m => ⟨(h m).2.2.2.2.1, (h m).2.2.2.2.2.1⟩⟩

/-! ## The hypotheses of the chain witness -/

/-- The hypothesis `hp_spec` of `concreteChainWitnessWithLastOf` for the parameters
`canonicalSparsifyParams sparsifyImplUsed`, with `K_s := sparsifyImplUsed.K_s` and
`K_t := 2 sparsifyImplUsed.K_t + 1`: `p_s = p_t = 1`, both constants fixed, and
`γ_ℓ, γ_c ≤ exp(C_sp log^{7/8}(m + 2))` (Theorem 8.1, page 39). -/
theorem sparsifyImplUsed_hp_spec :
    ∃ C_sp : ℝ, 0 < C_sp ∧ ∀ m : ℕ,
      (canonicalSparsifyParams sparsifyImplUsed m).K_s = sparsifyImplUsed.K_s ∧
      (canonicalSparsifyParams sparsifyImplUsed m).p_s = 1 ∧
      (canonicalSparsifyParams sparsifyImplUsed m).K_t = 2 * sparsifyImplUsed.K_t + 1 ∧
      (canonicalSparsifyParams sparsifyImplUsed m).p_t = 1 ∧
      (canonicalSparsifyParams sparsifyImplUsed m).γ_ℓ ≤
        Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
      (canonicalSparsifyParams sparsifyImplUsed m).γ_c ≤
        Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
  obtain ⟨C_sp, hC, h⟩ := sparsifyImplUsed_gamma_bound
  exact ⟨C_sp, hC, fun m => ⟨rfl, sparsifyImplUsed_p_s, rfl, sparsifyImplUsed_p_t, (h m).1, (h m).2⟩⟩

/-- The hypothesis `hsparsify` of `concreteChainWitnessWithLastOf`: the canonical sparsifier of
`sparsifyImplUsed` meets `SparsifySpec` (Theorem 8.1, page 39) at every edge cap, since its time
factor is `1` (`sparsifyImplUsed_γ_t`). -/
theorem sparsifyImplUsed_sparsifySpec (mMax : ℕ) :
    DynSpanner.SparsifySpec mMax (canonicalSparsifyParams sparsifyImplUsed mMax)
      (canonicalSparsify sparsifyImplUsed) :=
  canonicalSparsify_spec sparsifyImplUsed mMax (sparsifyImplUsed_γ_t mMax)

end

end MinCostFlow.DynSpanner.Program
