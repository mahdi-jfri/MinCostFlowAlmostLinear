module

public import MinCostFlow.Scaling.VertexCompression
import Mathlib.Data.Fintype.Card

/-!
# Compression never increases the vertex count

Starting from an empty label table, every allocated positive label belongs
to a vertex. An encounter preserves this property and assigns the next
label only to an unlabelled vertex. Choosing one vertex per allocated
label gives an injection into the original vertex set. This bounds the
compressed solver's vertex parameter by the original one.
-/

public section
namespace MinCostFlow.Scaling

private theorem encounter_covers_labels {n : ℕ} (s : VertexLabels n) (v : Fin n)
    (hcover : ∀ i<s.count,∃ u,s.table u=i+1) :
    ∀ i<(s.encounter v).count,∃ u,(s.encounter v).table u=i+1 := by
  by_cases hv : s.table v=0
  · simp only [VertexLabels.encounter,hv,↓reduceIte]
    intro i hi
    by_cases heq : i=s.count
    · subst i
      exact ⟨v,Function.update_self _ _ _⟩
    · obtain ⟨u,hu⟩ := hcover i (by omega)
      have hne : u≠v := by
        intro he
        subst u
        rw [hv] at hu
        omega
      exact ⟨u,(Function.update_of_ne hne _ _).trans hu⟩
  · simpa only [VertexLabels.encounter,hv,↓reduceIte] using hcover

private theorem scan_covers_labels {n : ℕ} (s : VertexLabels n) (vs : List (Fin n))
    (hcover : ∀ i<s.count,∃ u,s.table u=i+1) :
    ∀ i<(s.scan vs).count,∃ u,(s.scan vs).table u=i+1 := by
  induction vs generalizing s with
  | nil => exact hcover
  | cons v vs ih => exact ih (s.encounter v) (encounter_covers_labels s v hcover)

private theorem scan_empty_count_le_vertices {n : ℕ} (vs : List (Fin n)) :
    ((VertexLabels.empty n).scan vs).count≤n := by
  classical
  let s := (VertexLabels.empty n).scan vs
  have hcover : ∀ i<s.count,∃ u,s.table u=i+1 :=
    scan_covers_labels (VertexLabels.empty n) vs (by intro i hi; change i<0 at hi; omega)
  let f : Fin s.count → Fin n := fun i => Classical.choose (hcover i.val i.isLt)
  have hlabel (i : Fin s.count) : s.table (f i)=i.val+1 := Classical.choose_spec (hcover i.val i.isLt)
  have hinj : Function.Injective f := by
    intro i j hij
    have h := congrArg s.table hij
    rw [hlabel i,hlabel j] at h
    apply Fin.ext
    omega
  have h := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_fin] using h

/-- The endpoint-label compression used by capacity scaling has no more
vertices than its original circulation. -/
theorem Circulation.compress_vertices_le (J : Circulation) : J.compress.n≤J.n :=
  scan_empty_count_le_vertices J.endpoints

end MinCostFlow.Scaling
