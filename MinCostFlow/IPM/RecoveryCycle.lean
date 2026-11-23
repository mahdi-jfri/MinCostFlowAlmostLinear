module

public import MinCostFlow.IPM.RecoveryWalk
public import MinCostFlow.IPM.RecoveryPath
import Mathlib.Tactic.Ring

/-!
# A supported circulation through a chosen arc

The real-flow recovery argument for Appendix B.1 (page 92) of Chen et al.,
arXiv:2203.00671v2, follows a chosen auxiliary arc and a simple residual
return route. The shared walk flow of this closed route is a circulation,
has the residual's coordinate signs, and has bounded length.
-/

public section
namespace MinCostFlow.IPM

private theorem chain_arcs (I : Instance) (hI : I.IsValid) (d : Fin I.m → ℝ)
    (l : List (Fin I.n)) (a b : Fin I.n)
    (hc : List.IsChain (residualSupport I hI d) (a::l)) (hlast : (a::l).getLast? = some b) :
    ∃ P : List (Fin I.m × Bool), P.length = l.length ∧
      (∀ x ∈ P, ArcSupported d x) ∧
      ∀ v : Fin I.n, (∑ e, (I.edge e).b v*instanceWalkFlow P e) =
        (if v = a then (1 : ℝ) else 0)-(if v = b then (1 : ℝ) else 0) := by
  induction l generalizing a with
  | nil =>
    have hab : a = b := Option.some.inj hlast
    subst b
    refine ⟨[], rfl, ?_, ?_⟩
    · intro x hx
      exact False.elim (List.not_mem_nil hx)
    · intro v
      simp only [instanceWalkFlow, List.map_nil, walkFlow, List.sum_nil,
        mul_zero, Finset.sum_const_zero, sub_self]
  | cons c l ih =>
    have hcons := List.isChain_cons_cons.mp hc
    have hlast' : (c::l).getLast? = some b := by simpa only [List.getLast?_cons_cons] using hlast
    obtain ⟨P, hlen, hP, hroute⟩ := ih c hcons.2 hlast'
    obtain ⟨x, hx, hsrc, hdst⟩ := residualSupport_arc I hI d a c hcons.1
    refine ⟨x::P, by simp only [List.length_cons, hlen], ?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact hP y hy
    · intro v
      rw [sum_instanceWalkFlow]
      simp only [List.map_cons, List.sum_cons]
      rw [← sum_instanceWalkFlow P (fun e => (I.edge e).b v), arc_incidence I hI x v, hsrc, hdst, hroute]
      ring

/-- A supported arc can be completed to a closed supported route whose
shared walk flow is a circulation. Its length is bounded by the number
of vertices in a specified set containing every support endpoint. -/
theorem supported_cycle_through_arc (I : Instance) (hI : I.IsValid)
    (d : Fin I.m → ℝ) (hd : IsCirculation I d) (a : Fin I.m × Bool)
    (ha : ArcSupported d a) (S : Finset (Fin I.n))
    (hS : ∀ x y, residualSupport I hI d x y → x ∈ S ∧ y ∈ S) :
    ∃ P : List (Fin I.m × Bool), (a::P).length ≤ S.card ∧
      (∀ x ∈ a::P, ArcSupported d x) ∧ IsCirculation I (instanceWalkFlow (a::P)) := by
  have harc : residualSupport I hI d (arcSource I hI a) (arcTarget I hI a) := by
    refine ⟨a.1, ?_⟩
    cases hb : a.2
    · right
      refine ⟨?_, by simp only [arcSource, hb, Bool.false_eq_true, ↓reduceIte],
        by simp only [arcTarget, hb, Bool.false_eq_true, ↓reduceIte]⟩
      simpa only [ArcSupported, arcSign, hb, Bool.false_eq_true, ↓reduceIte, neg_one_mul, neg_pos] using ha
    · left
      refine ⟨?_, by simp only [arcSource, hb, ↓reduceIte],
        by simp only [arcTarget, hb, ↓reduceIte]⟩
      simpa only [ArcSupported, arcSign, hb, ↓reduceIte, one_mul] using ha
  obtain ⟨l, hc, hlast, _, hlength⟩ := residualSupport_return_length I hI d hd
    (arcSource I hI a) (arcTarget I hI a) harc S (hS _ _ harc).2 hS
  obtain ⟨P, hlen, hP, hroute⟩ := chain_arcs I hI d l (arcTarget I hI a) (arcSource I hI a) hc hlast
  refine ⟨P, by simpa only [List.length_cons, hlen] using hlength, ?_, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · exact hP x hx
  · intro v
    rw [sum_instanceWalkFlow]
    simp only [List.map_cons, List.sum_cons]
    rw [← sum_instanceWalkFlow P (fun e => (I.edge e).b v), arc_incidence I hI a v, hroute]
    ring

end MinCostFlow.IPM
