module

public import MinCostFlow.IPM.InitialArcCost
import MinCostFlow.IPM.InitialSupport
import MinCostFlow.IPM.InitialDomain
import MinCostFlow.IPM.InitialSize
import MinCostFlow.IPM.RecoveryCycle
import MinCostFlow.IPM.RecoveryPerturbation
import Mathlib.Tactic.Linarith

/-!
# Auxiliary flow vanishes at a real optimum

Appendix B.1 (page 92) of Chen et al., arXiv:2203.00671v2, rules out auxiliary
flow by charging its penalty. To cover arbitrary real optima, compare
with a feasible original flow embedded with zero auxiliaries. A positive
auxiliary coordinate gives a supported backward auxiliary arc. Its simple
return route has at most `2m` arcs, each costing at most `U`. Thus the
closed route costs at most `-K+2mU < 0`, contradicting optimality via a
small feasible real step. This replaces the source's incomplete argument
that only considers auxiliary flow of at least one unit.
-/

public section
namespace MinCostFlow.IPM

private theorem supported_walk_cost_le (I : Instance) (U : ℝ) (K : ℤ)
    (hU : 0 ≤ U) (hnums : NumbersBounded I U) (hK : 0 ≤ (K : ℝ))
    (d : Fin (initialInstance I K).m → ℝ)
    (hdaux : ∀ j, d (initialAuxiliaryEdge I K j) ≤ 0)
    (P : List (Fin (initialInstance I K).m × Bool)) (hP : ∀ a ∈ P, ArcSupported d a) :
    (initialInstance I K).cost (instanceWalkFlow P) ≤ P.length*U := by
  unfold Instance.cost
  rw [sum_instanceWalkFlow]
  induction P with
  | nil => simp
  | cons a P ih =>
    have hhead := initial_supported_arc_cost_le I U K hU hnums hK d hdaux a
      (hP a (List.mem_cons_self))
    have htail := ih (fun b hb => hP b (List.mem_cons_of_mem _ hb))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith only [hhead, htail]

/-- If the original instance is feasible, every real optimum of the
augmented instance has zero flow on every auxiliary edge. The penalty
condition `K > 2mU` holds for the source's choice `K = 4mU²`, `U ≥ 1`. -/
theorem optimal_auxiliary_zero (I : Instance) (U : ℝ) (K : ℤ)
    (hI : I.IsValid) (hU : 0 ≤ U) (hnums : NumbersBounded I U)
    (hK : 0 ≤ (K : ℝ)) (hKlarge : 2*I.m*U < (K : ℝ))
    (f : Fin I.m → ℝ) (hf : I.IsFeasible f)
    (g : Fin (initialInstance I K).m → ℝ) (hg : (initialInstance I K).IsMinCostFlow g) :
    ∀ j, initialAuxiliaryFlow I K g j = 0 := by
  let faug := embedInitialFlow I K (projectFreeFlow I f)
  have hfaug : (initialInstance I K).IsFeasible faug :=
    embedInitialFlow_feasible I K hI _ (feasible_projectFreeFlow I f hf)
  let d : Fin (initialInstance I K).m → ℝ := fun e => faug e-g e
  have hd : IsCirculation (initialInstance I K) d := by
    intro v
    simp only [d, mul_sub, Finset.sum_sub_distrib, hfaug.1 v, hg.1.1 v, sub_self]
  have hdaux_eq : ∀ j, d (initialAuxiliaryEdge I K j) = -initialAuxiliaryFlow I K g j := by
    intro j
    have hz := embedInitialFlow_auxiliary_zero I K (projectFreeFlow I f) j
    rw [initialAuxiliaryFlow_eq] at hz
    change faug (initialAuxiliaryEdge I K j) = 0 at hz
    change faug (initialAuxiliaryEdge I K j)-g (initialAuxiliaryEdge I K j) = _
    rw [hz, zero_sub]
    rfl
  have hdaux : ∀ j, d (initialAuxiliaryEdge I K j) ≤ 0 := by
    intro j
    rw [hdaux_eq]
    exact neg_nonpos.mpr (initialAuxiliaryFlow_nonneg I K g hg.1 j)
  have hJ := initialInstance_valid I K hI
  have hi := isolatedDemandsZero_of_feasible I f hf
  intro j
  by_contra hz
  have hpos : 0 < initialAuxiliaryFlow I K g j :=
    lt_of_le_of_ne (initialAuxiliaryFlow_nonneg I K g hg.1 j) (Ne.symm hz)
  let a : Fin (initialInstance I K).m × Bool := (initialAuxiliaryEdge I K j, false)
  have ha : ArcSupported d a := by
    simp only [ArcSupported, a, arcSign, Bool.false_eq_true, ↓reduceIte, neg_one_mul]
    rw [hdaux_eq, neg_neg]
    exact hpos
  obtain ⟨P, hlength, hP, hcir⟩ := supported_cycle_through_arc (initialInstance I K) hJ d hd a ha
    (initialSupportVertices I) (initial_residualSupport_vertices I K hi hJ d)
  have hbound := initialSupportVertices_card_le I
  have hlength' : P.length+1 ≤ (initialSupportVertices I).card := hlength
  have hplen : P.length ≤ 2*I.m := Nat.le_of_succ_le_succ (hlength'.trans hbound)
  have htail := supported_walk_cost_le I U K hU hnums hK d hdaux P
    (fun b hb => hP b (List.mem_cons_of_mem _ hb))
  have hwalk : (initialInstance I K).cost (instanceWalkFlow (a::P)) =
      -(K : ℝ)+(initialInstance I K).cost (instanceWalkFlow P) := by
    unfold Instance.cost
    rw [sum_instanceWalkFlow]
    simp only [List.map_cons, List.sum_cons]
    rw [← sum_instanceWalkFlow P (fun e => (((initialInstance I K).edge e).cost : ℝ))]
    rw [show (((initialInstance I K).edge a.1).cost : ℝ)*arcSign a = -(K : ℝ) by
      exact initial_backward_auxiliary_cost I K j]
  have hnonneg := no_negative_supported_walk (initialInstance I K) g faug hg hfaug (a::P) hP hcir
  have hlenU := mul_le_mul_of_nonneg_right (show (P.length : ℝ) ≤ 2*I.m by exact_mod_cast hplen) hU
  rw [hwalk] at hnonneg
  linarith only [hnonneg, htail, hlenU, hKlarge]

/-- Positive auxiliary flow at a real augmented optimum is a certificate
that the original instance has no feasible flow. -/
theorem infeasible_of_positive_auxiliary (I : Instance) (U : ℝ) (K : ℤ)
    (hI : I.IsValid) (hU : 0 ≤ U) (hnums : NumbersBounded I U)
    (hK : 0 ≤ (K : ℝ)) (hKlarge : 2*I.m*U < (K : ℝ))
    (g : Fin (initialInstance I K).m → ℝ) (hg : (initialInstance I K).IsMinCostFlow g)
    (j : Fin (deficitVertices I).card) (hj : initialAuxiliaryFlow I K g j ≠ 0) :
    ¬ ∃ f, I.IsFeasible f := by
  rintro ⟨f, hf⟩
  exact hj (optimal_auxiliary_zero I U K hI hU hnums hK hKlarge f hf g hg j)

/-- Recovery from any real augmented optimum: if every auxiliary flow
is zero the reconstructed flow is optimal, and otherwise the original
instance has no feasible flow. This is the recovery assertion of
Lemma 4.12 (page 31), with the real-flow gap in Appendix B.1 (page 92) filled by the
supported-cycle argument. -/
theorem initial_optimum_recovery (I : Instance) (U : ℝ) (K : ℤ)
    (hI : I.IsValid) (hordered : ∀ e : Fin I.m, (I.edge e).lower ≤ (I.edge e).upper)
    (hU : 0 ≤ U) (hnums : NumbersBounded I U)
    (hK : 0 ≤ (K : ℝ)) (hKlarge : 2*I.m*U < (K : ℝ))
    (g : Fin (initialInstance I K).m → ℝ) (hg : (initialInstance I K).IsMinCostFlow g) :
    I.IsMinCostFlow (recoverInitialFlow I K g) ∨ ¬ ∃ f, I.IsFeasible f := by
  classical
  by_cases hzero : ∀ j, initialAuxiliaryFlow I K g j = 0
  · exact Or.inl (recoverInitialFlow_minCost I K hI hordered g hg hzero)
  · right
    rintro ⟨f, hf⟩
    exact hzero (optimal_auxiliary_zero I U K hI hU hnums hK hKlarge f hf g hg)

end MinCostFlow.IPM
