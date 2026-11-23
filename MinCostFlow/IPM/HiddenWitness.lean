module

public import MinCostFlow.IPM.NamedInstance
public import MinCostFlow.Basic.Hidden
import MinCostFlow.IPM.OptimalDirection
import MinCostFlow.IPM.Parameters
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The IPM's hidden circulation and widths

Chen et al., arXiv:2203.00671v2, Lemma 9.2 (pages 70--71), chooses
`c = f* - f` and `w = 50 + |ℓ c|`. This file proves the circulation,
width, ratio and width-stability parts of that argument on the shared
named graph. In the width-stability calculation the source writes an
equality for a difference of absolute values. The triangle inequality
gives the inequality needed by the proof.
-/

@[expose] public section
namespace MinCostFlow.IPM

/-- The widths in Chen et al., arXiv:2203.00671v2, Lemma 9.2
(pages 70--71). The constant fifty is the source's constant. -/
def hiddenWidth {m : ℕ} (fstar f ℓ : Fin m → ℝ) (e : Fin m) : ℝ :=
  50+|ℓ e*(fstar e-f e)|

/-- The hidden width is at least fifty. -/
theorem hiddenWidth_ge {m : ℕ} (fstar f ℓ : Fin m → ℝ) (e : Fin m) :
    (50 : ℝ) ≤ hiddenWidth fstar f ℓ e := by
  exact le_add_of_nonneg_right (abs_nonneg _)

/-- The hidden widths change by at most the weighted flow displacement
when the stored edge length has not changed. This is the triangle
inequality step in Chen et al., Lemma 9.2 (pages 70--71). -/
theorem hiddenWidth_change {m : ℕ} (fstar f f' ℓ : Fin m → ℝ) (e : Fin m) :
    |hiddenWidth fstar f ℓ e-hiddenWidth fstar f' ℓ e| ≤ |ℓ e*(f e-f' e)| := by
  have h := abs_abs_sub_abs_le_abs_sub (ℓ e*(fstar e-f e)) (ℓ e*(fstar e-f' e))
  have hid : hiddenWidth fstar f ℓ e-hiddenWidth fstar f' ℓ e =
      |ℓ e*(fstar e-f e)|-|ℓ e*(fstar e-f' e)| := by unfold hiddenWidth; ring
  rw [hid]
  have harg : ℓ e*(fstar e-f e)-ℓ e*(fstar e-f' e) = -(ℓ e*(f e-f' e)) := by ring
  simpa only [harg, abs_neg] using h

/-- Detect's bound of one on an unchanged edge suffices for item 4 of
Definition 4.4 (page 14), since the old width is at least fifty. -/
theorem hiddenWidth_stable {m : ℕ} (fstar f f' ℓ : Fin m → ℝ) (e : Fin m)
    (hclose : |ℓ e*(f e-f' e)| ≤ 1) :
    hiddenWidth fstar f ℓ e ≤ 2*hiddenWidth fstar f' ℓ e := by
  have h := (abs_le.mp ((hiddenWidth_change fstar f f' ℓ e).trans hclose)).2
  have hw := hiddenWidth_ge fstar f' ℓ e
  linarith only [h, hw]

/-- The direction between two demand-routing flows is a circulation. -/
theorem difference_circulation (I : Instance) (fstar f : Fin I.m → ℝ)
    (hs : I.Routes fstar) (hf : I.Routes f) :
    IsCirculation I (fun e => fstar e-f e) := by
  intro v
  simp only [mul_sub, Finset.sum_sub_distrib, hs v, hf v, sub_self]

/-- The hidden circulation and widths are a valid pair on the named graph,
with precisely the same incidence equations as the finite IPM instance. -/
theorem hiddenWidth_valid (I : Instance) (fstar f ℓ : Fin I.m → ℝ)
    (hs : I.Routes fstar) (hf : I.Routes f) :
    IsValidPair (namedInstance I) (namedVector ℓ)
      (namedVector (fun e => fstar e-f e)) (namedVector (hiddenWidth fstar f ℓ)) := by
  refine ⟨namedInstance_circulation I _ (difference_circulation I fstar f hs hf), ?_⟩
  intro e he
  have he' : e < I.m := Finset.mem_range.mp he
  simp only [namedVector, he', ↓reduceDIte, hiddenWidth]
  linarith only [abs_nonneg (ℓ ⟨e, he'⟩*(fstar ⟨e, he'⟩-f ⟨e, he'⟩))]

/-- The width norm is exactly the denominator used in Lemma 9.2. -/
theorem hiddenWidth_norm (I : Instance) (fstar f ℓ : Fin I.m → ℝ) :
    (namedInstance I).norm1 (namedVector (hiddenWidth fstar f ℓ)) =
      50*I.m+weightedLength ℓ (fun e => fstar e-f e) := by
  have hh := sum_namedVector I (hiddenWidth fstar f ℓ)
  calc
    _ = ∑ e ∈ (namedInstance I).E, namedVector (hiddenWidth fstar f ℓ) e := by
      apply Finset.sum_congr rfl
      intro e he
      have he' : e < I.m := Finset.mem_range.mp he
      rw [show e = (⟨e, he'⟩ : Fin I.m).val from rfl, namedVector_fin]
      exact abs_of_nonneg (le_trans (by norm_num) (hiddenWidth_ge _ _ _ _))
    _ = ∑ e, hiddenWidth fstar f ℓ e := hh
    _ = _ := by simp only [hiddenWidth, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, weightedLength]; ring

/-- The negative-ratio part of Chen et al., Lemma 9.2 (pages 70--71).
A residual estimate within `1+ε`, for `ε ≤ 1`, loses at most a factor
two when the rescaled approximate gradient is converted back to the
stored gradient. The resulting hidden stability parameter is `α/8`. -/
theorem hiddenWidth_ratio (I : Instance) (U F ε r : ℝ)
    (fstar f g ℓ : Fin I.m → ℝ)
    (hm : 0 < I.m) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hf : StrictlyInside I f) (hs : I.IsFeasible fstar)
    (hr : 0 < residual I F f) (hF : I.cost fstar ≤ F)
    (_he : 0 ≤ ε) (he' : ε ≤ 1)
    (hres : ScalarApprox (1+ε) r (residual I F f))
    (hg : GradientTolerance (lengths I (alpha I U) f)
      (fun e => (r/residual I F f)*g e) (gradient I (alpha I U) F f) (alpha I U/2))
    (hl : VectorApprox 2 ℓ (lengths I (alpha I U) f))
    (hpot : potential I (alpha I U) F f ≤ 200*I.m*Real.log (I.m*U))
    (hreslog : -10*Real.log (I.m*U) ≤ Real.log (residual I F f)) :
    (namedInstance I).inner (namedVector g) (namedVector (fun e => fstar e-f e)) /
      (namedInstance I).norm1 (namedVector (hiddenWidth fstar f ℓ)) ≤ -(alpha I U/8) := by
  have hq := direction_of_cost_le I U F (alpha I U/2) f fstar
    (fun e => (r/residual I F f)*g e) ℓ hm hsize hf hs hr hF le_rfl hg hl hpot hreslog
  have hlen : 0 ≤ weightedLength ℓ (fun e => fstar e-f e) :=
    Finset.sum_nonneg fun e _ => abs_nonneg _
  have hmR : (0 : ℝ) < I.m := Nat.cast_pos.mpr hm
  have ha := alpha_pos I U hsize
  have hd100 : 0 < 100*(I.m : ℝ)+weightedLength ℓ (fun e => fstar e-f e) := by
    linarith only [hmR, hlen]
  have hd50 : 0 < 50*(I.m : ℝ)+weightedLength ℓ (fun e => fstar e-f e) := by
    linarith only [hmR, hlen]
  have hq' := (div_le_iff₀ hd100).mp hq
  have hneg : dot (fun e => (r/residual I F f)*g e) (fun e => fstar e-f e) ≤ 0 :=
    hq'.trans (mul_nonpos_of_nonpos_of_nonneg (by linarith only [ha]) hd100.le)
  have hratio : (1/2 : ℝ) ≤ residual I F f/r := by
    apply (le_div_iff₀ hres.1).mpr
    have hh := hres.2.2.2
    have hp := mul_le_mul_of_nonneg_right he' hr.le
    linarith only [hh, hp]
  have hid : dot g (fun e => fstar e-f e) =
      (residual I F f/r)*dot (fun e => (r/residual I F f)*g e) (fun e => fstar e-f e) := by
    unfold dot
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    field_simp [hr.ne', hres.1.ne']
  have hscaled := mul_le_mul_of_nonpos_right hratio hneg
  rw [namedInstance_inner, hiddenWidth_norm]
  apply (div_le_iff₀ hd50).mpr
  rw [hid]
  nlinarith only [hscaled, hq', mul_nonneg ha.le hmR.le]

end MinCostFlow.IPM
