module

public import MinCostFlow.Scaling.RoutingAugmentProgram
import WordRAM.Layout

/-!
# Connecting residual flow arrays to the augmentation scan

The residual encoding puts forward slots before reverse slots. Form the
scan's coordinate triples from a starting flow and these two halves.
Their three projections are exactly the stored source arrays. When the
integer update is nonnegative, the unsigned output is its exact magnitude.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Physical scan coordinates for the model's integer residual update. -/
def routingAugmentTriples {m : ℕ} (start : Fin m → ℤ) (delta : Fin (m+m) → ℤ) :
    List (ℕ × ℕ × ℕ) :=
  List.ofFn (fun e => ((start e).toNat,(delta (Fin.castAdd m e)).toNat,
    (delta (Fin.natAdd m e)).toNat))

/-- The starting array and the forward/reverse halves of a residual array
realize the scan's three input layouts. -/
theorem routingAugment_sources {m : ℕ} (start : Fin m → ℤ) (delta : Fin (m+m) → ℤ)
    {mem : ℕ → ℕ} {a d : ℕ}
    (hs : ListAt mem a (List.ofFn (fun e => (start e).toNat)))
    (hd : ListAt mem d (List.ofFn (fun e => (delta e).toNat))) :
    ListAt mem a ((routingAugmentTriples start delta).map Prod.fst) ∧
    ListAt mem d ((routingAugmentTriples start delta).map (fun x => x.2.1)) ∧
    ListAt mem (d+m) ((routingAugmentTriples start delta).map (fun x => x.2.2)) := by
  simp only [routingAugmentTriples,List.map_ofFn]
  refine ⟨hs,?_,?_⟩
  · intro i hi
    have hi' : i < m := by simpa only [List.length_ofFn] using hi
    have h := hd i (by simp only [List.length_ofFn]; omega)
    rw [List.getElem_ofFn] at h
    change mem (d+i) = (delta (Fin.castAdd m ⟨i,hi'⟩)).toNat at h
    simpa only [List.getElem_ofFn,Function.comp_apply] using h
  · intro i hi
    have hi' : i < m := by simpa only [List.length_ofFn] using hi
    have h := hd (m+i) (by simp only [List.length_ofFn]; omega)
    rw [List.getElem_ofFn] at h
    change mem (d+(m+i)) = (delta (Fin.natAdd m ⟨i,hi'⟩)).toNat at h
    simpa only [List.getElem_ofFn,Nat.add_assoc,Function.comp_apply] using h

/-- The unsigned scan output equals the integer model update coordinatewise
when the starting flow and correction are nonnegative and the update fits
above zero. These are numeric conditions, without an optimality assumption. -/
theorem routingAugment_words {m : ℕ} (start : Fin m → ℤ) (delta : Fin (m+m) → ℤ)
    (hs : ∀ e, 0 ≤ start e) (hd : ∀ e, 0 ≤ delta e)
    (hr : ∀ e, 0 ≤ start e+delta (Fin.castAdd m e)-delta (Fin.natAdd m e)) :
    (routingAugmentTriples start delta).map (fun x => x.1+x.2.1-x.2.2) =
      List.ofFn (fun e => (start e+delta (Fin.castAdd m e)-delta (Fin.natAdd m e)).toNat) := by
  rw [routingAugmentTriples,List.map_ofFn]
  apply congrArg List.ofFn
  funext e
  have hs' := Int.toNat_of_nonneg (hs e)
  have hf' := Int.toNat_of_nonneg (hd (Fin.castAdd m e))
  have hr' := Int.toNat_of_nonneg (hd (Fin.natAdd m e))
  have hnonneg : (delta (Fin.natAdd m e)).toNat ≤
      (start e).toNat+(delta (Fin.castAdd m e)).toNat := by
    have h := hr e
    rw [← hs',← hf',← hr'] at h
    omega
  have h := routingAugment_coordinate (start e).toNat
    (delta (Fin.castAdd m e)).toNat (delta (Fin.natAdd m e)).toNat hnonneg
  rw [hs',hf',hr'] at h
  have heq := congrArg Int.toNat h
  simpa only [Int.toNat_natCast,Function.comp_apply] using heq

end MinCostFlow.Scaling.Machine
