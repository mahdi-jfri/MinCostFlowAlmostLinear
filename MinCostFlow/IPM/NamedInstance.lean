module

public import MinCostFlow.IPM.Definitions
public import MinCostFlow.Basic.Graph
import Mathlib.Algebra.BigOperators.Fin

/-!
# Passing the IPM's fixed graph to the dynamic interface

The IPM of Chen et al., arXiv:2203.00671v2, Algorithm 7 (Section 9,
page 69), keeps its graph fixed and changes gradient and length entries.
Definition 4.5 of arXiv:2309.16629v1 (page 14) uses named dynamic graphs.
This file names vertex `v` and edge `e` by their original indices. It
proves that sums, ratios, and circulations agree under zero extension.
-/

@[expose] public section
noncomputable section
namespace MinCostFlow.IPM

/-- Edge-vector zero extension from the IPM's finite indices to edge names. -/
def namedVector {m : ℕ} (f : Fin m → ℝ) (e : ℕ) : ℝ :=
  if he : e < m then f ⟨e, he⟩ else 0

/-- The fixed IPM graph as a shared `MGraph`, with the original indices
as names. Default endpoints outside the graph do not affect any sum. -/
def namedInstance (I : Instance) : MGraph where
  V := Finset.range I.n
  E := Finset.range I.m
  tail e := if he : e < I.m then (I.edge ⟨e, he⟩).tail else 0
  head e := if he : e < I.m then (I.edge ⟨e, he⟩).head else 0

/-- Zero extension agrees at every original edge. -/
theorem namedVector_fin {m : ℕ} (f : Fin m → ℝ) (e : Fin m) :
    namedVector f e = f e := by simp only [namedVector, e.2, ↓reduceDIte]

/-- The named graph has exactly the original edge count. -/
theorem namedInstance_m (I : Instance) : (namedInstance I).m = I.m :=
  Finset.card_range I.m

/-- The named graph is valid when the original instance is valid. -/
theorem namedInstance_valid (I : Instance) (hI : I.IsValid) : (namedInstance I).IsValid := by
  intro e he
  have he' : e < I.m := Finset.mem_range.mp he
  have hh := hI.1 (I.edge ⟨e, he'⟩) (List.getElem_mem he')
  simpa only [namedInstance, he', ↓reduceDIte, Finset.mem_range] using hh

/-- Finite sums are preserved by zero extension. -/
theorem sum_namedVector (I : Instance) (f : Fin I.m → ℝ) :
    (∑ e ∈ (namedInstance I).E, namedVector f e) = ∑ e, f e := by
  have h := Fin.sum_univ_eq_sum_range (namedVector f) I.m
  simpa only [namedInstance, namedVector_fin] using h.symm

/-- Dot products are unchanged by the naming map. -/
theorem namedInstance_inner (I : Instance) (g f : Fin I.m → ℝ) :
    (namedInstance I).inner (namedVector g) (namedVector f) = dot g f := by
  have h := sum_namedVector I (fun e => g e*f e)
  unfold dot
  rw [← h]
  apply Finset.sum_congr rfl
  intro e he
  have he' : e < I.m := Finset.mem_range.mp he
  simp only [namedVector, he', ↓reduceDIte]

/-- Positive length vectors have the same weighted norm after naming. -/
theorem namedInstance_lnorm (I : Instance) (ℓ f : Fin I.m → ℝ)
    (hℓ : ∀ e, 0 < ℓ e) :
    (namedInstance I).lnorm (namedVector ℓ) (namedVector f) = weightedLength ℓ f := by
  have h := sum_namedVector I (fun e => |ℓ e*f e|)
  unfold weightedLength
  rw [← h]
  apply Finset.sum_congr rfl
  intro e he
  have he' : e < I.m := Finset.mem_range.mp he
  simp only [namedVector, he', ↓reduceDIte, abs_mul, abs_of_pos (hℓ ⟨e, he'⟩)]

/-- Incidence agrees at each named original edge. -/
theorem namedInstance_b (I : Instance) (e : Fin I.m) (v : ℕ) :
    (namedInstance I).b e v = (I.edge e).b v := by
  simp only [MGraph.b, namedInstance, e.2, ↓reduceDIte, Edge.b]

/-- Circulations on the original graph are exactly circulations of the
zero-extended vector on the named graph. -/
theorem namedInstance_circulation (I : Instance) (d : Fin I.m → ℝ)
    (hd : IsCirculation I d) : (namedInstance I).IsCirculation (namedVector d) := by
  intro v hv
  have hv' : v < I.n := Finset.mem_range.mp hv
  change (∑ e ∈ (namedInstance I).E, (namedInstance I).b e v*namedVector d e) = 0
  have hs := sum_namedVector I (fun e => (I.edge e).b v*d e)
  rw [← hd ⟨v, hv'⟩, ← hs]
  apply Finset.sum_congr rfl
  intro e he
  have he' : e < I.m := Finset.mem_range.mp he
  rw [show e = (⟨e, he'⟩ : Fin I.m).val from rfl, namedInstance_b]
  simp only [namedVector, he', ↓reduceDIte]

/-- Restricting an arbitrary named circulation to the original finite
edge indices preserves its routing equations. -/
theorem namedInstance_restrict_circulation (I : Instance) (d : ℕ → ℝ)
    (hd : (namedInstance I).IsCirculation d) : IsCirculation I (fun e => d e) := by
  intro v
  have hh := hd v (Finset.mem_range.mpr v.2)
  change (∑ e ∈ (namedInstance I).E, (namedInstance I).b e v*d e) = 0 at hh
  rw [← hh, ← sum_namedVector I (fun e => (I.edge e).b v*d e)]
  apply Finset.sum_congr rfl
  intro e he
  have heI : e < I.m := Finset.mem_range.mp he
  rw [show e = (⟨e, heI⟩ : Fin I.m).val from rfl, namedInstance_b]
  simp only [namedVector, heI, ↓reduceDIte]

/-- Dot products against an arbitrary named direction depend only on
its original edge coordinates. -/
theorem namedInstance_inner_restrict (I : Instance) (g : Fin I.m → ℝ) (d : ℕ → ℝ) :
    (namedInstance I).inner (namedVector g) d = dot g (fun e => d e) := by
  rw [dot, ← sum_namedVector I (fun e => g e*d e)]
  apply Finset.sum_congr rfl
  intro e he
  have heI : e < I.m := Finset.mem_range.mp he
  simp only [namedVector, heI, ↓reduceDIte]

/-- The weighted norm of an arbitrary named direction is its finite
coordinate norm when the stored lengths are positive. -/
theorem namedInstance_lnorm_restrict (I : Instance) (ℓ : Fin I.m → ℝ) (d : ℕ → ℝ)
    (hℓ : ∀ e, 0 < ℓ e) :
    (namedInstance I).lnorm (namedVector ℓ) d = weightedLength ℓ (fun e => d e) := by
  rw [weightedLength, ← sum_namedVector I (fun e => |ℓ e*d e|)]
  apply Finset.sum_congr rfl
  intro e he
  have heI : e < I.m := Finset.mem_range.mp he
  simp only [namedVector, heI, ↓reduceDIte, abs_mul, abs_of_pos (hℓ ⟨e, heI⟩)]

end MinCostFlow.IPM
