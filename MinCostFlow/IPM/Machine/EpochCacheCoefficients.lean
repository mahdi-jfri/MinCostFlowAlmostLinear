module

public import MinCostFlow.IPM.Machine.EpochConditions
public import MinCostFlow.IPM.GradientStability
import Mathlib.Tactic.Ring
import MinCostFlow.IPM.Machine.ReportedTableLayout
import MinCostFlow.Num.IPM.FixedPointFacts

/-!
# Numerical cache values in the IPM formulas

The cache stores dyadic coordinates, lengths and gradients in dense
arrays. Their scalar contracts compare against the same lengths and
held-residual gradient used by Lemma 9.1 (Chen et al., arXiv:2203.00671v2,
page 70). Decode those contracts against the instance's capacity and
cost tables to obtain the vector tolerances.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine

/-- Read a dense fixed-point coordinate array on the IPM edge type. -/
noncomputable def epochVector {w : ℕ} (F : MinRatioFormat w) (I : Instance)
    (mem : ℕ → ℕ) (ptr : ℕ) (e : Fin I.m) : ℝ :=
  Num.fixVal mem (ptr+e.val*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision

/-- The instance data, exponent and residual decoded from the held
numerical sources. -/
def epochSourcesAt {w : ℕ} (F : MinRatioFormat w) (I : Instance)
    (L : EpochLayout) (a r : ℝ) (mem : ℕ → ℕ) : Prop :=
  Num.fixVal mem L.alpha F.fmt.limbBits F.limbs F.fmt.precision=a ∧
  Num.fixVal mem L.residual F.fmt.limbBits F.limbs F.fmt.precision=r ∧
  ∀ e : Fin I.m, epochVector F I mem L.lower e=(I.edge e).lower ∧
    epochVector F I mem L.upper e=(I.edge e).upper ∧
    Num.intVal mem (L.cost+e.val*F.limbs) F.fmt.limbBits F.limbs=(I.edge e).cost

/-- Preserving the prefix before the mutable flow table preserves the
decoded instance data and both held scalars. -/
theorem epochSourcesAt.frozen {w : ℕ} {F : MinRatioFormat w} {I : Instance} {L : EpochLayout}
    {a r : ℝ} {mem final : ℕ → ℕ} (h : epochSourcesAt F I L a r mem)
    (hframe : ∀ z<L.flow,final z=mem z)
    (harrays : ∀ ptr∈[L.base,L.cost,L.lower,L.upper],ptr+I.m*F.limbs≤L.flow)
    (hscalars : L.residual+F.limbs≤L.flow ∧ L.alpha+F.limbs≤L.flow) :
    epochSourcesAt F I L a r final := by
  refine ⟨(Num.IPM.fixVal_frozen hframe hscalars.2).trans h.1,
    (Num.IPM.fixVal_frozen hframe hscalars.1).trans h.2.1,?_⟩
  intro e
  have he (ptr : ℕ) (hp : ptr∈[L.base,L.cost,L.lower,L.upper]) : ptr+e.val*F.limbs+F.limbs≤L.flow :=
    (reported_entry_end ptr F.limbs e.val I.m e.isLt).trans (harrays ptr hp)
  exact ⟨(Num.IPM.fixVal_frozen hframe (he L.lower (by simp))).trans (h.2.2 e).1,
    (Num.IPM.fixVal_frozen hframe (he L.upper (by simp))).trans (h.2.2 e).2.1,
    (Num.IPM.value_frozen hframe (he L.cost (by simp))).trans (h.2.2 e).2.2⟩

/-- On one actual cache block, the length and gradient errors compare
against the IPM formulas, and the stored coordinate has strict slacks. -/
theorem reportedCachePost_coefficients {w : ℕ} (F : MinRatioFormat w) (I : Instance)
    (A : MinRatioDataStructureWithFailure) (L : EpochLayout) (a r : ℝ) (mem : ℕ → ℕ)
    (hsource : epochSourcesAt F I L a r mem)
    (q : ℕ) (e : Fin I.m) (s : A.State)
    (hc : reportedCachePost F A s I.m q L.base L.lower L.upper L.flow L.cost
      L.residual L.alpha L.lengths L.gradient e.val mem) :
    ScalarApprox (1+1/(2:ℝ)^q) (epochVector F I mem L.lengths e)
      (lengths I a (epochVector F I mem L.flow) e) ∧
    |epochVector F I mem L.gradient e-gradientWithResidual I a r (epochVector F I mem L.flow) e|≤
      (1/(2:ℝ)^q)*lengths I a (epochVector F I mem L.flow) e ∧
    (I.edge e).lower<epochVector F I mem L.flow e ∧ epochVector F I mem L.flow e<(I.edge e).upper := by
  obtain ⟨ha,hr,he⟩ := hsource
  obtain ⟨hlo,hup,hcost⟩ := he e
  have hl : Num.IPM.arrayLength mem L.lower L.flow L.upper L.alpha
      F.fmt.limbBits F.limbs F.fmt.precision e.val=lengths I a (epochVector F I mem L.flow) e := by
    unfold Num.IPM.arrayLength lengths
    rw [ha]
    change Real.rpow (epochVector F I mem L.upper e-epochVector F I mem L.flow e) (-1-a)+
      Real.rpow (epochVector F I mem L.flow e-epochVector F I mem L.lower e) (-1-a)=_
    rw [hlo,hup]
  have hg : Num.IPM.arrayGradient mem I.m L.cost L.residual L.lower L.flow L.upper L.alpha
      F.fmt.limbBits F.limbs F.fmt.precision e.val=gradientWithResidual I a r (epochVector F I mem L.flow) e := by
    unfold Num.IPM.arrayGradient gradientWithResidual
    rw [ha,hr,hcost]
    change 20*(I.m:ℝ)*r⁻¹*(I.edge e).cost+
      a*(Real.rpow (epochVector F I mem L.upper e-epochVector F I mem L.flow e) (-1-a)-
        Real.rpow (epochVector F I mem L.flow e-epochVector F I mem L.lower e) (-1-a))=_
    rw [hlo,hup]
    ring
  refine ⟨?_,?_,?_⟩
  · rw [← hl]
    exact hc.2.2.2.1
  · rw [← hg,← hl]
    exact hc.2.2.2.2.2.1
  · rw [← hlo,← hup]
    exact hc.2.2.2.2.2.2

end MinCostFlow.IPM.Machine
