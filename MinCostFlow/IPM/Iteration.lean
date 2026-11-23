module

public import MinCostFlow.IPM.Update
public import Mathlib.Algebra.Order.Floor.Semiring
import MinCostFlow.IPM.Parameters
import MinCostFlow.IPM.WeightedBounds
import MinCostFlow.IPM.OptimalDirection
import MinCostFlow.IPM.IterationBound
import Mathlib.Tactic.Linarith

/-!
# The potential-reduction iteration

Theorem 4.3 (page 25) of Chen et al., arXiv:2203.00671v2, repeatedly takes a
permitted update until the cost residual is at most `(mU)^(-10)`.
Lemma 4.7 (page 28) ensures a permitted update exists before stopping. Lemma 4.4 (page 25)
preserves its domain and decreases the potential. Summing this decrease
gives the explicit iteration limit below.
-/

noncomputable section
public section
namespace MinCostFlow.IPM

/-- The explicit iteration limit from the proof of Theorem 4.3 (page 25). The
inverse square corrects the source's two occurrences of `κ²` in the count. -/
@[expose] def iterationLimit (I : Instance) (U κ : ℝ) : ℕ :=
  Nat.ceil (200000*I.m*Real.log (I.m*U)/κ^2)

/-- Before the cost stopping threshold, the residual hypothesis of
Lemma 4.7 (page 28) holds. -/
theorem log_residual_before_stop (I : Instance) (U F : ℝ) (f : Fin I.m → ℝ)
    (hsize : 2 ≤ (I.m : ℝ)*U)
    (hstop : Real.rpow (I.m*U) (-10) < residual I F f) :
    -10*Real.log (I.m*U) ≤ Real.log (residual I F f) := by
  have hs : 0 < (I.m : ℝ)*U := lt_of_lt_of_le (by norm_num) hsize
  have ht : 0 < (I.m*U)^(-10 : ℝ) := Real.rpow_pos_of_pos hs _
  have hl := Real.log_le_log ht hstop.le
  rw [Real.log_rpow hs] at hl
  simpa only [mul_comm] using hl

private theorem nonempty_update (I : Instance) (U F κ : ℝ) (f fstar : Fin I.m → ℝ)
    (hm : 0 < I.m) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hf : StrictlyInside I f) (hroute : I.Routes f) (hs : I.IsMinCostFlow fstar)
    (hr : 0 < residual I F f) (hF : I.cost fstar = F)
    (hκ : 0 < κ) (hκa : κ ≤ alpha I U/4)
    (hpot : potential I (alpha I U) F f ≤ 200*I.m*Real.log (I.m*U))
    (hstop : Real.rpow (I.m*U) (-10) < residual I F f) : Nonempty (Update I U F κ f) := by
  have hex := exact_approximations I (alpha I U) F (κ/8) f hf
    (div_nonneg hκ.le (by norm_num : (0 : ℝ) ≤ 8))
  obtain ⟨s, _, _, _⟩ := exists_update_with_approximations I U F κ f fstar
    (gradient I (alpha I U) F f) (lengths I (alpha I U) f) hm hsize hf hroute hs hr hF
    hκ hκa hex.1 hex.2 hpot (log_residual_before_stop I U F f hsize hstop)
  exact ⟨s⟩

/-- One mathematical iteration: stop at the threshold, otherwise choose
any permitted update. The existence of an update on every reachable
nonterminal flow is proved below. -/
@[expose] def reductionNext (I : Instance) (U F κ : ℝ) (f : Fin I.m → ℝ) : Fin I.m → ℝ := by
  classical
  exact if Real.rpow (I.m*U) (-10) < residual I F f then
    if h : Nonempty (Update I U F κ f) then (Classical.choice h).next else f
  else f

/-- The mathematical flow sequence in Theorem 4.3 (page 25). -/
@[expose] def reductionFlow (I : Instance) (U F κ : ℝ) (f₀ : Fin I.m → ℝ) : ℕ → Fin I.m → ℝ
  | 0 => f₀
  | t+1 => reductionNext I U F κ (reductionFlow I U F κ f₀ t)

private theorem reductionNext_update (I : Instance) (U F κ : ℝ) (f : Fin I.m → ℝ)
    (hstop : Real.rpow (I.m*U) (-10) < residual I F f)
    (hs : Nonempty (Update I U F κ f)) :
    ∃ s : Update I U F κ f, reductionNext I U F κ f = s.next := by
  refine ⟨Classical.choice hs, ?_⟩
  simp only [reductionNext, hstop, hs, ↓reduceIte, ↓reduceDIte]

/-- The sequence keeps the routing, strict capacities, positive residual,
and initial potential bound. These are proved invariants, not fields of
an assumed state contract. -/
theorem reductionFlow_invariants (I : Instance) (U F κ : ℝ) (f₀ fstar : Fin I.m → ℝ)
    (hm : 0 < I.m) (hU : 0 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hf : StrictlyInside I f₀) (hroute : I.Routes f₀)
    (hr : 0 < residual I F f₀) (hs : I.IsMinCostFlow fstar) (hF : I.cost fstar = F)
    (hκ : 0 < κ) (hκa : κ ≤ alpha I U/4)
    (hinit : potential I (alpha I U) F f₀ ≤ 200*I.m*Real.log (I.m*U)) (t : ℕ) :
    I.Routes (reductionFlow I U F κ f₀ t) ∧
      StrictlyInside I (reductionFlow I U F κ f₀ t) ∧
      0 < residual I F (reductionFlow I U F κ f₀ t) ∧
      potential I (alpha I U) F (reductionFlow I U F κ f₀ t) ≤ 200*I.m*Real.log (I.m*U) := by
  have hκ' : κ ≤ 1 := by linarith only [hκa, alpha_le I U hsize]
  induction t with
  | zero => exact ⟨hroute, hf, hr, hinit⟩
  | succ t ih =>
    simp only [reductionFlow]
    by_cases hstop : Real.rpow (I.m*U) (-10) < residual I F (reductionFlow I U F κ f₀ t)
    · have hex := nonempty_update I U F κ (reductionFlow I U F κ f₀ t) fstar hm hsize
        ih.2.1 ih.1 hs ih.2.2.1 hF hκ hκa ih.2.2.2 hstop
      obtain ⟨s, heq⟩ := reductionNext_update I U F κ _ hstop hex
      rw [heq]
      have hspec := s.spec hm hU hsize hnums ih.2.1 ih.1 ih.2.2.1 hκ hκ'
      refine ⟨hspec.1, hspec.2.1, hspec.2.2.1, ?_⟩
      have hn := sq_nonneg κ
      linarith only [hspec.2.2.2, ih.2.2.2, hn]
    · simpa only [reductionNext, hstop, ↓reduceIte] using ih

/-- Every nonterminal iteration of the constructed sequence is a permitted
update, so the source's tolerances remain available to later implementations. -/
theorem reductionFlow_update (I : Instance) (U F κ : ℝ) (f₀ fstar : Fin I.m → ℝ)
    (hm : 0 < I.m) (hU : 0 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hf : StrictlyInside I f₀) (hroute : I.Routes f₀)
    (hr : 0 < residual I F f₀) (hs : I.IsMinCostFlow fstar) (hF : I.cost fstar = F)
    (hκ : 0 < κ) (hκa : κ ≤ alpha I U/4)
    (hinit : potential I (alpha I U) F f₀ ≤ 200*I.m*Real.log (I.m*U)) (t : ℕ)
    (hstop : Real.rpow (I.m*U) (-10) < residual I F (reductionFlow I U F κ f₀ t)) :
    ∃ s : Update I U F κ (reductionFlow I U F κ f₀ t),
      reductionFlow I U F κ f₀ (t+1) = s.next := by
  have hi := reductionFlow_invariants I U F κ f₀ fstar hm hU hsize hnums hf hroute hr hs hF hκ hκa hinit t
  have hex := nonempty_update I U F κ _ fstar hm hsize hi.2.1 hi.1 hs hi.2.2.1 hF hκ hκa hi.2.2.2 hstop
  exact reductionNext_update I U F κ _ hstop hex

/-- A run follows the choices of Theorem 4.3 (page 25) before its stopping
threshold. No condition is imposed after the first successful prefix. -/
@[expose] def AdmissibleRun (I : Instance) (U F κ : ℝ)
    (f : ℕ → Fin I.m → ℝ) (a : ℝ := alpha I U) : Prop :=
  ∀ t, Real.rpow (I.m*U) (-10) < residual I F (f t) →
    ∃ s : Update I U F κ (f t) a, f (t+1) = s.next

/-- Theorem 4.3 (page 25) of Chen et al., arXiv:2203.00671v2, for every
admissible run. Lemma 4.4 preserves the domain and drops the potential at
every step before stopping. The counting bound then forces a successful
prefix within `ceil(200000 m log(mU)/κ²)` steps. As in the one-step analysis,
we retain the restriction `κ ≤ α/4`. The target need not be optimal for
this implication. Existence for an optimal target is proved below. -/
theorem theorem_4_3_prefix (I : Instance) (U F κ : ℝ) (f : ℕ → Fin I.m → ℝ)
    (hm : 0 < I.m) (hU : 0 < U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hf : StrictlyInside I (f 0))
    (hroute : I.Routes (f 0)) (hr : 0 < residual I F (f 0))
    (hκ : 0 < κ) (hκa : κ ≤ alpha I U/4)
    (hinit : potential I (alpha I U) F (f 0) ≤ 200*I.m*Real.log (I.m*U))
    (hrun : AdmissibleRun I U F κ f) :
    ∃ t ≤ iterationLimit I U κ,
      I.IsFeasible (f t) ∧ I.cost (f t) ≤ F+Real.rpow (I.m*U) (-10) := by
  have hκ' : κ ≤ 1 := by linarith only [hκa, alpha_le I U hsize]
  by_contra h
  have hinv : ∀ t, t ≤ iterationLimit I U κ →
      I.Routes (f t) ∧ StrictlyInside I (f t) ∧
      0 < residual I F (f t) ∧
      potential I (alpha I U) F (f t) ≤ 200*I.m*Real.log (I.m*U) := by
    intro t
    induction t with
    | zero => intro _; exact ⟨hroute, hf, hr, hinit⟩
    | succ t ih =>
      intro ht
      have hi := ih (Nat.le_of_succ_le ht)
      have hbefore : Real.rpow (I.m*U) (-10) < residual I F (f t) := by
        apply lt_of_not_ge
        intro hh
        apply h
        refine ⟨t, Nat.le_of_succ_le ht, feasible_of_inside I _ hi.1 hi.2.1, ?_⟩
        dsimp only [residual] at hh
        linarith only [hh]
      obtain ⟨s, heq⟩ := hrun t hbefore
      rw [heq]
      have hs := s.spec hm hU.le hsize hnums hi.2.1 hi.1 hi.2.2.1 hκ hκ'
      refine ⟨hs.1, hs.2.1, hs.2.2.1, ?_⟩
      linarith only [hs.2.2.2, hi.2.2.2, sq_nonneg κ]
  have hbefore : ∀ t ≤ iterationLimit I U κ,
      Real.rpow (I.m*U) (-10) < residual I F (f t) := by
    intro t ht
    apply lt_of_not_ge
    intro hh
    have hi := hinv t ht
    apply h
    refine ⟨t, ht, feasible_of_inside I _ hi.1 hi.2.1, ?_⟩
    dsimp only [residual] at hh
    linarith only [hh]
  have hstep : ∀ t < iterationLimit I U κ,
      potential I (alpha I U) F (f (t+1)) ≤
        potential I (alpha I U) F (f t)-κ^2/500 := by
    intro t ht
    obtain ⟨s, heq⟩ := hrun t (hbefore t ht.le)
    have hi := hinv t ht.le
    rw [heq]
    exact (s.spec hm hU.le hsize hnums hi.2.1 hi.1 hi.2.2.1 hκ hκ').2.2.2
  have hn : 200000*I.m*Real.log (I.m*U) ≤ (iterationLimit I U κ : ℝ)*κ^2 :=
    (div_le_iff₀ (sq_pos_of_pos hκ)).mp (Nat.le_ceil _)
  have hi := hinv (iterationLimit I U κ) le_rfl
  have hsmall := residual_after_steps I (alpha I U) F U κ f
    (iterationLimit I U κ) hm hU hi.2.1 hi.2.2.1 hinit hstep hn
  exact (not_lt_of_ge hsmall) (hbefore _ le_rfl)

/-- The stopping rule in Theorem 4.3 (page 25): after the residual reaches
the threshold, the terminated run is extended by keeping its flow fixed. -/
@[expose] def StopsAtThreshold (I : Instance) (U F : ℝ)
    (f : ℕ → Fin I.m → ℝ) : Prop :=
  ∀ t, residual I F (f t) ≤ Real.rpow (I.m*U) (-10) → f (t+1) = f t

private theorem stopped_flow_eq (I : Instance) (U F : ℝ) (f : ℕ → Fin I.m → ℝ)
    (hstop : StopsAtThreshold I U F f) (t n : ℕ) (htn : t ≤ n)
    (ht : residual I F (f t) ≤ Real.rpow (I.m*U) (-10)) : f n = f t := by
  induction n, htn using Nat.le_induction with
  | base => rfl
  | succ n _ ih =>
    rw [hstop n (by rw [ih]; exact ht), ih]

/-- Theorem 4.3 (page 25) of Chen et al., arXiv:2203.00671v2, for every
admissible stopped run. After `ceil(200000 m log(mU)/κ²)` steps its flow
is feasible and has cost at most `F+(mU)^(-10)`. Each nonterminal step
may use any approximations and circulation allowed by `Update`.
The stopping rule extends a terminated run by its final flow. We retain
the restriction `κ ≤ α/4` needed by the source's one-step analysis. -/
theorem theorem_4_3 (I : Instance) (U F κ : ℝ) (f : ℕ → Fin I.m → ℝ)
    (hm : 0 < I.m) (hU : 0 < U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hf : StrictlyInside I (f 0))
    (hroute : I.Routes (f 0)) (hr : 0 < residual I F (f 0))
    (hκ : 0 < κ) (hκa : κ ≤ alpha I U/4)
    (hinit : potential I (alpha I U) F (f 0) ≤ 200*I.m*Real.log (I.m*U))
    (hrun : AdmissibleRun I U F κ f) (hstop : StopsAtThreshold I U F f) :
    I.IsFeasible (f (iterationLimit I U κ)) ∧
      I.cost (f (iterationLimit I U κ)) ≤ F+Real.rpow (I.m*U) (-10) := by
  obtain ⟨t, ht, hfeas, hcost⟩ := theorem_4_3_prefix I U F κ f hm hU hsize hnums
    hf hroute hr hκ hκa hinit hrun
  have hres : residual I F (f t) ≤ Real.rpow (I.m*U) (-10) := by
    dsimp only [residual]
    linarith only [hcost]
  rw [stopped_flow_eq I U F f hstop t _ ht hres]
  exact ⟨hfeas, hcost⟩

/-- The constructed admissible sequence also follows the IPM stopping
rule. This property requires no extra assumptions on its choices. -/
theorem reductionFlow_stopsAtThreshold (I : Instance) (U F κ : ℝ) (f₀ : Fin I.m → ℝ) :
    StopsAtThreshold I U F (reductionFlow I U F κ f₀) := by
  intro t ht
  have hnot : ¬ Real.rpow (I.m*U) (-10) < residual I F (reductionFlow I U F κ f₀ t) :=
    not_lt_of_ge ht
  simp only [reductionFlow, reductionNext, hnot, ↓reduceIte]

/-- The choices required by `AdmissibleRun` can hold together: the constructed
run supplies them for any strictly interior initial flow with the stated
potential bound and an optimal target. -/
theorem reductionFlow_admissible (I : Instance) (U F κ : ℝ) (f₀ fstar : Fin I.m → ℝ)
    (hm : 0 < I.m) (hU : 0 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hf : StrictlyInside I f₀) (hroute : I.Routes f₀)
    (hr : 0 < residual I F f₀) (hs : I.IsMinCostFlow fstar) (hF : I.cost fstar = F)
    (hκ : 0 < κ) (hκa : κ ≤ alpha I U/4)
    (hinit : potential I (alpha I U) F f₀ ≤ 200*I.m*Real.log (I.m*U)) :
    AdmissibleRun I U F κ (reductionFlow I U F κ f₀) :=
  reductionFlow_update I U F κ f₀ fstar hm hU hsize hnums hf hroute hr hs hF hκ hκa hinit

/-- Theorem 4.3 (page 25) of Chen et al., arXiv:2203.00671v2, with explicit count
`ceil(200000 m log(mU)/κ²)`. The source's first-item tolerance needs a
restriction relating `κ` and `α`; we use `0 < κ ≤ α/4`, which also ensures
a good direction exists. Every nonterminal update and its error tolerances
are given by `reductionFlow_update`. The hidden-direction ratio for all
permitted approximations is Lemma 4.7 (page 28). -/
theorem theorem_4_3_constructed (I : Instance) (U F κ : ℝ) (f₀ fstar : Fin I.m → ℝ)
    (hm : 0 < I.m) (hU : 0 < U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hf : StrictlyInside I f₀) (hroute : I.Routes f₀)
    (hr : 0 < residual I F f₀) (hs : I.IsMinCostFlow fstar) (hF : I.cost fstar = F)
    (hκ : 0 < κ) (hκa : κ ≤ alpha I U/4)
    (hinit : potential I (alpha I U) F f₀ ≤ 200*I.m*Real.log (I.m*U)) :
    ∃ t ≤ iterationLimit I U κ,
      I.IsFeasible (reductionFlow I U F κ f₀ t) ∧
      I.cost (reductionFlow I U F κ f₀ t) ≤ F+Real.rpow (I.m*U) (-10) := by
  have hκ' : κ ≤ 1 := by linarith only [hκa, alpha_le I U hsize]
  have hinv := reductionFlow_invariants I U F κ f₀ fstar hm hU.le hsize hnums hf hroute hr hs hF hκ hκa hinit
  have hterminal : ∃ t ≤ iterationLimit I U κ,
      residual I F (reductionFlow I U F κ f₀ t) ≤ Real.rpow (I.m*U) (-10) := by
    by_contra h
    have hbefore : ∀ t ≤ iterationLimit I U κ,
        Real.rpow (I.m*U) (-10) < residual I F (reductionFlow I U F κ f₀ t) := by
      intro t ht
      apply lt_of_not_ge
      intro hh
      exact h ⟨t, ht, hh⟩
    have hstep : ∀ t < iterationLimit I U κ,
        potential I (alpha I U) F (reductionFlow I U F κ f₀ (t+1)) ≤
          potential I (alpha I U) F (reductionFlow I U F κ f₀ t)-κ^2/500 := by
      intro t ht
      obtain ⟨s, heq⟩ := reductionFlow_update I U F κ f₀ fstar hm hU.le hsize hnums
        hf hroute hr hs hF hκ hκa hinit t (hbefore t ht.le)
      have hi := hinv t
      rw [heq]
      exact (s.spec hm hU.le hsize hnums hi.2.1 hi.1 hi.2.2.1 hκ hκ').2.2.2
    have hn : 200000*I.m*Real.log (I.m*U) ≤ (iterationLimit I U κ : ℝ)*κ^2 := by
      exact (div_le_iff₀ (sq_pos_of_pos hκ)).mp (Nat.le_ceil _)
    have hi := hinv (iterationLimit I U κ)
    have hsmall := residual_after_steps I (alpha I U) F U κ (reductionFlow I U F κ f₀)
      (iterationLimit I U κ) hm hU hi.2.1 hi.2.2.1 hinit hstep hn
    exact (not_lt_of_ge hsmall) (hbefore _ le_rfl)
  obtain ⟨t, ht, hsmall⟩ := hterminal
  have hi := hinv t
  refine ⟨t, ht, feasible_of_inside I _ hi.1 hi.2.1, ?_⟩
  dsimp only [residual] at hsmall
  linarith only [hsmall]

end MinCostFlow.IPM
