module

public import MinCostFlow.IPM.InitialConstruction
public import MinCostFlow.IPM.InitialSize
public import MinCostFlow.IPM.InitialRecovery
import MinCostFlow.IPM.InitialRouting
import MinCostFlow.IPM.InitialDomain
import MinCostFlow.IPM.InitialNumbers
import MinCostFlow.IPM.InitialPotential
import MinCostFlow.IPM.InitialOptimalAuxiliary
import MinCostFlow.IPM.Optimum
import MinCostFlow.IPM.Parameters
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Initial point and recovery

Lemma 4.12 (page 31) of Chen et al., arXiv:2203.00671v2, is proved in Appendix B.1 (page 92).
The construction deletes fixed edges and adds midpoint deficit edges at
one new vertex. Its integral penalty is `4mU²`. The checks below either
certify infeasibility, solve a graph with no edges, or establish all input
conditions for that construction. The potential is bounded using the
actual augmented edge count, correcting the literal constant with the
original count. Recovery works for arbitrary real augmented optima.
-/

noncomputable section
public section
namespace MinCostFlow.IPM

/-- The integral auxiliary-edge penalty in Lemma 4.12 (page 31). -/
@[expose] def initialPenalty (I : Instance) (U : ℕ) : ℤ := 4*(I.m : ℤ)*(U : ℤ)^2

private theorem initialPenalty_bounds (I : Instance) (U : ℕ) (hm : 0 < I.m) (hU : 1 ≤ U) :
    (initialPenalty I U : ℝ) = 4*I.m*(U : ℝ)^2 ∧
      0 ≤ (initialPenalty I U : ℝ) ∧ 2*I.m*(U : ℝ) < (initialPenalty I U : ℝ) := by
  have heq : (initialPenalty I U : ℝ) = 4*I.m*(U : ℝ)^2 := penalty_cast I U
  have hm' : (0 : ℝ) < I.m := Nat.cast_pos.mpr hm
  have hU' : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hU0 : (0 : ℝ) < U := lt_of_lt_of_le (by norm_num) hU'
  have hpow : (U : ℝ) ≤ (U : ℝ)^2 := by nlinarith only [hU']
  have hmul := mul_le_mul_of_nonneg_left hpow (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hm'.le)
  have hpos : 0 < (I.m : ℝ)*U := mul_pos hm' hU0
  refine ⟨heq, ?_, ?_⟩ <;> rw [heq] <;> nlinarith only [hmul, hpos]

private theorem cost_eq_zero_of_no_edges (I : Instance) (hm : I.m = 0) (f : Fin I.m → ℝ) :
    I.cost f = 0 := by
  unfold Instance.cost
  apply Finset.sum_eq_zero
  intro e _
  have h : e.val < 0 := lt_of_lt_of_le e.2 (Nat.le_of_eq hm)
  exact False.elim (Nat.not_lt_zero _ h)

/-- A graph with no edges is solved by its unique empty flow, or has no
feasible flow. This handles the zero-edge case before taking logarithms. -/
theorem no_edges_minCost_or_infeasible (I : Instance) (hm : I.m = 0) :
    I.IsMinCostFlow (fun _ => 0) ∨ ¬ ∃ f, I.IsFeasible f := by
  classical
  by_cases hz : I.IsFeasible (fun _ => 0)
  · left
    refine ⟨hz, ?_⟩
    intro f _
    rw [cost_eq_zero_of_no_edges I hm, cost_eq_zero_of_no_edges I hm]
  · right
    rintro ⟨f, hf⟩
    have heq : f = fun _ => 0 := by
      funext e
      have h : e.val < 0 := lt_of_lt_of_le e.2 (Nat.le_of_eq hm)
      exact False.elim (Nat.not_lt_zero _ h)
    exact hz (heq ▸ hf)

/-- The preprocessing cases for Lemma 4.12 (page 31). No extra feasibility
hypothesis is assumed: failure of a capacity, balance, or isolated-demand
check is proved to certify infeasibility. -/
theorem initialization_precheck (I : Instance) (hI : I.IsValid) :
    I.IsMinCostFlow (fun _ => 0) ∨ (¬ ∃ f, I.IsFeasible f) ∨
      (0 < I.m ∧ (∀ e : Fin I.m, (I.edge e).lower ≤ (I.edge e).upper) ∧
        (∑ v : Fin I.n, (I.d v : ℝ)) = 0 ∧ IsolatedDemandsZero I) := by
  classical
  by_cases hm : I.m = 0
  · rcases no_edges_minCost_or_infeasible I hm with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · by_cases hc : ∀ e : Fin I.m, (I.edge e).lower ≤ (I.edge e).upper
    · by_cases hb : (∑ v : Fin I.n, (I.d v : ℝ)) = 0
      · by_cases hi : IsolatedDemandsZero I
        · exact Or.inr (Or.inr ⟨Nat.pos_of_ne_zero hm, hc, hb, hi⟩)
        · exact Or.inr (Or.inl (infeasible_of_isolated_demand I hi))
      · exact Or.inr (Or.inl (infeasible_of_unbalanced I hI hb))
    · right
      left
      rintro ⟨f, hf⟩
      apply hc
      intro e
      exact_mod_cast (hf.2 e).1.trans (hf.2 e).2

/-- Increasing the supplied integer bound to at least two preserves every
numeric input bound and avoids the degenerate logarithm `log(mU)=0`. -/
theorem numbersBounded_normalize (I : Instance) (U : ℕ) (hnums : NumbersBounded I (U : ℝ)) :
    NumbersBounded I ((max U 2 : ℕ) : ℝ) := by
  have hbound : (U : ℝ) ≤ (max U 2 : ℕ) := by exact_mod_cast le_max_left U 2
  exact ⟨fun v => (hnums.1 v).trans hbound,
    fun e => ⟨(hnums.2 e).1.trans hbound, (hnums.2 e).2.1.trans hbound, (hnums.2 e).2.2.trans hbound⟩⟩

/-- An augmented optimum either certifies that the initial flow is already
optimal, or gives a positive residual and the source's initial potential
bound with the augmented edge count. -/
theorem initial_point_or_optimal (I : Instance) (U a : ℝ) (K : ℤ)
    (hm : 0 < I.m) (hU : 1 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hi : IsolatedDemandsZero I)
    (hK : 0 ≤ (K : ℝ)) (hK' : (K : ℝ) ≤ 4*I.m*U^2)
    (ha : 0 ≤ a) (ha' : a ≤ 1)
    (hfeas : (initialInstance I K).IsFeasible (initialFlow I K))
    (gstar : Fin (initialInstance I K).m → ℝ)
    (hgstar : (initialInstance I K).IsMinCostFlow gstar) :
    (initialInstance I K).IsMinCostFlow (initialFlow I K) ∨
      (0 < residual (initialInstance I K) ((initialInstance I K).cost gstar) (initialFlow I K) ∧
      potential (initialInstance I K) a ((initialInstance I K).cost gstar) (initialFlow I K) ≤
        200*(initialInstance I K).m*Real.log (I.m*U)) := by
  have hopt := hgstar.2 (initialFlow I K) hfeas
  by_cases heq : (initialInstance I K).cost (initialFlow I K) = (initialInstance I K).cost gstar
  · left
    refine ⟨hfeas, ?_⟩
    intro g hg
    rw [heq]
    exact hgstar.2 g hg
  · have hr : 0 < residual (initialInstance I K) ((initialInstance I K).cost gstar) (initialFlow I K) :=
      sub_pos.mpr (lt_of_le_of_ne hopt (Ne.symm heq))
    exact Or.inr ⟨hr, initial_potential_le I U a _ K hm hU hsize hnums hi hK hK' ha ha'
      gstar hgstar rfl hr⟩

/-- A positive initial optimality gap implies a nonempty augmented edge
set, so the next IPM phase has a positive edge count. -/
theorem initial_residual_m_pos (I : Instance) (K : ℤ)
    (gstar : Fin (initialInstance I K).m → ℝ)
    (hr : 0 < residual (initialInstance I K) ((initialInstance I K).cost gstar) (initialFlow I K)) :
    0 < (initialInstance I K).m := by
  by_contra hn
  have hm : (initialInstance I K).m = 0 := Nat.eq_zero_of_not_pos hn
  have hf := cost_eq_zero_of_no_edges (initialInstance I K) hm (initialFlow I K)
  have hg := cost_eq_zero_of_no_edges (initialInstance I K) hm gstar
  dsimp only [residual] at hr
  rw [hf, hg, sub_self] at hr
  exact (lt_irrefl 0) hr

/-- The exponent for the augmented numeric bound lies in the range used
by `initial_point_or_optimal`, whenever an IPM phase is needed. -/
theorem initial_exponent_bounds (I : Instance) (U : ℕ) (K : ℤ)
    (hm : 0 < I.m) (hU : 1 ≤ U) (hM : 0 < (initialInstance I K).m) :
    0 < alpha (initialInstance I K) (4*I.m*(U : ℝ)^2) ∧
      alpha (initialInstance I K) (4*I.m*(U : ℝ)^2) ≤ 1 := by
  have hmR : (1 : ℝ) ≤ I.m := Nat.one_le_cast.mpr hm
  have hMR : (1 : ℝ) ≤ (initialInstance I K).m := Nat.one_le_cast.mpr hM
  have hUR : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hUsq : (1 : ℝ) ≤ (U : ℝ)^2 := by nlinarith only [hUR]
  have hproduct := mul_le_mul hmR hUsq (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg I.m)
  have hbig : (2 : ℝ) ≤ 4*I.m*(U : ℝ)^2 := by nlinarith only [hproduct]
  have hsize : (2 : ℝ) ≤ (initialInstance I K).m*(4*I.m*(U : ℝ)^2) := by
    have ht := mul_le_mul_of_nonneg_right hMR (le_trans (by norm_num) hbig)
    nlinarith only [ht, hbig]
  exact ⟨alpha_pos _ _ hsize, (alpha_le _ _ hsize).trans (by norm_num)⟩

/-- Lemma 4.12 (page 31) of Chen et al., arXiv:2203.00671v2, after the proved
prechecks. The construction is `initialInstance` with `initialPenalty`,
and its flow is `initialFlow`. Costs and capacities obey `4mU²`, demands
obey `2mU`, and the edge count is at most `3m`. `initial_point_or_optimal`
gives the potential bound or an already optimal initial flow. The bound
uses the augmented count (equivalently at most `600m log(mU)`), repairing
the source's literal input-count constant. Recovery is for real optima. -/
theorem lemma_4_12 (I : Instance) (U : ℕ) (hI : I.IsValid) (hm : 0 < I.m) (hU : 2 ≤ U)
    (hnums : NumbersBounded I (U : ℝ))
    (hordered : ∀ e : Fin I.m, (I.edge e).lower ≤ (I.edge e).upper)
    (hbal : (∑ v : Fin I.n, (I.d v : ℝ)) = 0) (hi : IsolatedDemandsZero I) :
    (initialInstance I (initialPenalty I U)).n = I.n+1 ∧
    (initialInstance I (initialPenalty I U)).m ≤ 3*I.m ∧
    (initialInstance I (initialPenalty I U)).IsValid ∧
    (initialInstance I (initialPenalty I U)).IsFeasible (initialFlow I (initialPenalty I U)) ∧
    StrictlyInside (initialInstance I (initialPenalty I U)) (initialFlow I (initialPenalty I U)) ∧
    (∀ v : Fin (initialInstance I (initialPenalty I U)).n,
      |((initialInstance I (initialPenalty I U)).d v : ℝ)| ≤ 2*I.m*(U : ℝ)) ∧
    (∀ e : Fin (initialInstance I (initialPenalty I U)).m,
      |(((initialInstance I (initialPenalty I U)).edge e).lower : ℝ)| ≤ 4*I.m*(U : ℝ)^2 ∧
      |(((initialInstance I (initialPenalty I U)).edge e).upper : ℝ)| ≤ 4*I.m*(U : ℝ)^2 ∧
      |(((initialInstance I (initialPenalty I U)).edge e).cost : ℝ)| ≤ 4*I.m*(U : ℝ)^2) ∧
    (∃ gstar, (initialInstance I (initialPenalty I U)).IsMinCostFlow gstar) ∧
    (∀ a : ℝ, 0 ≤ a → a ≤ 1 → ∀ gstar,
      (initialInstance I (initialPenalty I U)).IsMinCostFlow gstar →
      (initialInstance I (initialPenalty I U)).IsMinCostFlow (initialFlow I (initialPenalty I U)) ∨
      (0 < residual (initialInstance I (initialPenalty I U))
        ((initialInstance I (initialPenalty I U)).cost gstar) (initialFlow I (initialPenalty I U)) ∧
      potential (initialInstance I (initialPenalty I U)) a
        ((initialInstance I (initialPenalty I U)).cost gstar) (initialFlow I (initialPenalty I U)) ≤
        200*(initialInstance I (initialPenalty I U)).m*Real.log (I.m*(U : ℝ)))) ∧
    (∀ gstar, (initialInstance I (initialPenalty I U)).IsMinCostFlow gstar →
      I.IsMinCostFlow (recoverInitialFlow I (initialPenalty I U) gstar) ∨ ¬ ∃ f, I.IsFeasible f) := by
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hU)
  have hU0 : (0 : ℝ) ≤ U := le_trans (by norm_num) hU1
  obtain ⟨heq, hK, hKlarge⟩ := initialPenalty_bounds I U hm (le_trans (by norm_num) hU)
  have hnumK : |(initialPenalty I U : ℝ)| ≤ 4*I.m*(U : ℝ)^2 := by rw [abs_of_nonneg hK, heq]
  have hn := initialInstance_numbers I (U : ℝ) (initialPenalty I U) hm hU1 hnums hnumK
  have hf := initialFlow_feasible I (initialPenalty I U) hI hordered hbal
  refine ⟨rfl, initialInstance_m_le I _ hi, initialInstance_valid I _ hI, hf,
    initialFlow_inside I _, hn.1, hn.2, exists_minCostFlow _ ⟨_, hf⟩, ?_, ?_⟩
  · intro a ha ha' gstar hgstar
    have hmR : (1 : ℝ) ≤ I.m := Nat.one_le_cast.mpr hm
    have hU2 : (2 : ℝ) ≤ U := by exact_mod_cast hU
    have hsize : (2 : ℝ) ≤ I.m*U := by
      have h := mul_le_mul hmR hU2 (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg I.m)
      simpa only [one_mul] using h
    exact initial_point_or_optimal I (U : ℝ) a (initialPenalty I U) hm hU1 hsize hnums hi
      hK heq.le ha ha' hf gstar hgstar
  · intro gstar hgstar
    exact initial_optimum_recovery I (U : ℝ) (initialPenalty I U) hI hordered hU0 hnums hK hKlarge gstar hgstar

end MinCostFlow.IPM
