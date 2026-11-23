module

public import MinCostFlow.IPM.RecoverySupport
public import MinCostFlow.Basic.Graph
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Residual walk flows in instance coordinates

The real-flow repair of Appendix B.1 (page 92) of Chen et al., arXiv:2203.00671v2,
uses a supported residual cycle. We use the shared `walkFlow`, mapping
finite edge labels to their natural-number labels and restricting the
result back to the instance. Its weighted sums are the sums of the
oriented edge contributions. A supported list has the same coordinate
signs as the residual circulation.
-/

noncomputable section
@[expose] public section
namespace MinCostFlow.IPM

/-- The sign of an oriented edge, in the convention of `walkFlow`. -/
def arcSign {m : ℕ} (a : Fin m × Bool) : ℝ := if a.2 then 1 else -1

/-- The initial vertex of an oriented instance edge. -/
def arcSource (I : Instance) (hI : I.IsValid) (a : Fin I.m × Bool) : Fin I.n :=
  if a.2 then tailVertex I hI a.1 else headVertex I hI a.1

/-- The final vertex of an oriented instance edge. -/
def arcTarget (I : Instance) (hI : I.IsValid) (a : Fin I.m × Bool) : Fin I.n :=
  if a.2 then headVertex I hI a.1 else tailVertex I hI a.1

/-- An arc points in the strict sign of the residual flow. -/
def ArcSupported {m : ℕ} (d : Fin m → ℝ) (a : Fin m × Bool) : Prop :=
  0 < arcSign a*d a.1

/-- The shared walk flow, transported from finite labels to natural
labels and then restricted to the finite edge set of the instance. -/
def instanceWalkFlow {m : ℕ} (P : List (Fin m × Bool)) (e : Fin m) : ℝ :=
  walkFlow (P.map fun a => (a.1.val, a.2)) e.val

/-- One oriented edge adds its signed unit flow to the shared walk flow. -/
theorem instanceWalkFlow_cons {m : ℕ} (a : Fin m × Bool) (P : List (Fin m × Bool)) (e : Fin m) :
    instanceWalkFlow (a::P) e = (if e = a.1 then arcSign a else 0)+instanceWalkFlow P e := by
  have he : (a.1.val = e.val) ↔ e = a.1 := by rw [Fin.ext_iff]; exact eq_comm
  simp only [instanceWalkFlow, List.map_cons, walkFlow, List.sum_cons, he, arcSign]

/-- A weighted sum of the shared walk flow equals the sum along its arcs. -/
theorem sum_instanceWalkFlow {m : ℕ} (P : List (Fin m × Bool)) (w : Fin m → ℝ) :
    (∑ e, w e*instanceWalkFlow P e) = (P.map fun a => w a.1*arcSign a).sum := by
  induction P with
  | nil => simp only [instanceWalkFlow, List.map_nil, walkFlow, List.sum_nil, mul_zero, Finset.sum_const_zero]
  | cons a P ih =>
    simp only [instanceWalkFlow_cons, mul_add, Finset.sum_add_distrib, ih, List.map_cons, List.sum_cons]
    congr 1
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- A residual support step can be represented by an oriented edge. -/
theorem residualSupport_arc (I : Instance) (hI : I.IsValid) (d : Fin I.m → ℝ)
    (u v : Fin I.n) (h : residualSupport I hI d u v) :
    ∃ a : Fin I.m × Bool, ArcSupported d a ∧ arcSource I hI a = u ∧ arcTarget I hI a = v := by
  obtain ⟨e, he⟩ := h
  rcases he with ⟨hp, ht, hh⟩ | ⟨hp, hh, ht⟩
  · exact ⟨(e, true), by simpa only [ArcSupported, arcSign, ↓reduceIte, one_mul] using hp, ht, hh⟩
  · exact ⟨(e, false), by simpa only [ArcSupported, arcSign, Bool.false_eq_true, ↓reduceIte, neg_one_mul] using neg_pos.mpr hp, hh, ht⟩

/-- The incidence of an oriented edge is one at its source and minus one
at its target, including the cancellation on a self-loop. -/
theorem arc_incidence (I : Instance) (hI : I.IsValid) (a : Fin I.m × Bool) (v : Fin I.n) :
    (I.edge a.1).b v*arcSign a =
      (if v = arcSource I hI a then (1 : ℝ) else 0) -
      (if v = arcTarget I hI a then (1 : ℝ) else 0) := by
  have ht : ((v : ℕ) = (I.edge a.1).tail) ↔ v = tailVertex I hI a.1 := by
    change ((v : ℕ) = (tailVertex I hI a.1).val) ↔ _
    exact Fin.ext_iff.symm
  have hh : ((v : ℕ) = (I.edge a.1).head) ↔ v = headVertex I hI a.1 := by
    change ((v : ℕ) = (headVertex I hI a.1).val) ↔ _
    exact Fin.ext_iff.symm
  cases hb : a.2 <;> simp only [arcSign, arcSource, arcTarget, hb, Bool.false_eq_true, ↓reduceIte, Edge.b, ht, hh] <;> ring

/-- Every walk-flow coordinate agrees in sign with the residual flow
when every arc is supported. -/
theorem instanceWalkFlow_signs {m : ℕ} (P : List (Fin m × Bool)) (d : Fin m → ℝ)
    (hP : ∀ a ∈ P, ArcSupported d a) (e : Fin m) :
    (0 ≤ d e → 0 ≤ instanceWalkFlow P e) ∧
      (d e ≤ 0 → instanceWalkFlow P e ≤ 0) ∧
      (d e = 0 → instanceWalkFlow P e = 0) := by
  induction P with
  | nil => simp only [instanceWalkFlow, List.map_nil, walkFlow, List.sum_nil, le_refl, implies_true, and_self]
  | cons a P ih =>
    have ha := hP a (List.mem_cons_self)
    have hi := ih (fun b hb => hP b (List.mem_cons_of_mem _ hb))
    rw [instanceWalkFlow_cons]
    by_cases he : e = a.1
    · subst e
      cases hb : a.2
      · have hd : d a.1 < 0 := by
          simpa only [ArcSupported, arcSign, hb, Bool.false_eq_true, ↓reduceIte, neg_one_mul, neg_pos] using ha
        simp only [arcSign, hb, Bool.false_eq_true, ↓reduceIte]
        refine ⟨?_, ?_, ?_⟩
        · intro h
          exact False.elim (not_lt_of_ge h hd)
        · intro h
          linarith only [hi.2.1 h]
        · intro h
          exact False.elim (hd.ne h)
      · have hd : 0 < d a.1 := by simpa only [ArcSupported, arcSign, hb, Bool.false_eq_true, ↓reduceIte, one_mul] using ha
        simp only [arcSign, hb, ↓reduceIte]
        refine ⟨?_, ?_, ?_⟩
        · intro h
          linarith only [hi.1 h]
        · intro h
          exact False.elim (not_lt_of_ge h hd)
        · intro h
          exact False.elim (hd.ne' h)
    · simpa only [he, ↓reduceIte, zero_add] using hi

end MinCostFlow.IPM
