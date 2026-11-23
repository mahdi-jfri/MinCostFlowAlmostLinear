module

public import MinCostFlow.Scaling.ResidualReduction
import Mathlib.Tactic.Linarith

/-!
# Residual arcs after augmentation

The proof of Lemma C.7 in Appendix C of Chen et al., arXiv:2203.00671v2,
examines arcs after a residual circulation is added. With two explicit slots
per edge, both slots can carry flow. A remaining forward arc comes either
from unused forward capacity or from positive reverse augmentation. The
symmetric statement handles a remaining reverse arc. These alternatives
make the source's residual-arc argument valid even when both slots are used.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- Forward activity after augmentation has one of two complementary-slackness
witnesses. This includes cancellation between the two residual slots. -/
theorem augment_forward_alternatives (I : Circulation) (f : Fin I.m → ℤ)
    (hf : I.Feasible (fun e => (f e : ℝ)))
    (g : Fin (I.m + I.m) → ℝ) (hg : (I.residual f).Feasible g)
    (e : Fin I.m) (ha : I.augment f g e < I.capacity e) :
    (g (Fin.castAdd I.m e) < (I.residual f).capacity (Fin.castAdd I.m e) ∧
      0 < (I.residual f).capacity (Fin.castAdd I.m e)) ∨
    (0 < g (Fin.natAdd I.m e) ∧ 0 < (I.residual f).capacity (Fin.natAdd I.m e)) := by
  have hforward := hg.2 (Fin.castAdd I.m e)
  have hreverse := hg.2 (Fin.natAdd I.m e)
  have hc := (I.residual_capacity_cast f hf.2 e).1
  by_cases h : g (Fin.castAdd I.m e) < (I.residual f).capacity (Fin.castAdd I.m e)
  · left
    refine ⟨h, ?_⟩
    have hh : (0 : ℝ) < (I.residual f).capacity (Fin.castAdd I.m e) :=
      lt_of_le_of_lt hforward.1 h
    exact_mod_cast hh
  · right
    have hr : 0 < g (Fin.natAdd I.m e) := by
      dsimp only [augment, project] at ha
      linarith only [ha, hc, hforward.2, h]
    refine ⟨hr, ?_⟩
    have hh : (0 : ℝ) < (I.residual f).capacity (Fin.natAdd I.m e) :=
      lt_of_lt_of_le hr hreverse.2
    exact_mod_cast hh

/-- Reverse activity after augmentation likewise has an unsaturated reverse
slot or a positive forward augmentation as a witness. -/
theorem augment_reverse_alternatives (I : Circulation) (f : Fin I.m → ℤ)
    (hf : I.Feasible (fun e => (f e : ℝ)))
    (g : Fin (I.m + I.m) → ℝ) (hg : (I.residual f).Feasible g)
    (e : Fin I.m) (ha : 0 < I.augment f g e) :
    (g (Fin.natAdd I.m e) < (I.residual f).capacity (Fin.natAdd I.m e) ∧
      0 < (I.residual f).capacity (Fin.natAdd I.m e)) ∨
    (0 < g (Fin.castAdd I.m e) ∧ 0 < (I.residual f).capacity (Fin.castAdd I.m e)) := by
  have hforward := hg.2 (Fin.castAdd I.m e)
  have hreverse := hg.2 (Fin.natAdd I.m e)
  have hc := (I.residual_capacity_cast f hf.2 e).2
  by_cases h : g (Fin.natAdd I.m e) < (I.residual f).capacity (Fin.natAdd I.m e)
  · left
    refine ⟨h, ?_⟩
    have hh : (0 : ℝ) < (I.residual f).capacity (Fin.natAdd I.m e) :=
      lt_of_le_of_lt hreverse.1 h
    exact_mod_cast hh
  · right
    have hr : 0 < g (Fin.castAdd I.m e) := by
      dsimp only [augment, project] at ha
      linarith only [ha, hc, hreverse.2, h]
    refine ⟨hr, ?_⟩
    have hh : (0 : ℝ) < (I.residual f).capacity (Fin.castAdd I.m e) :=
      lt_of_lt_of_le hr hforward.2
    exact_mod_cast hh

end MinCostFlow.Scaling.Circulation
