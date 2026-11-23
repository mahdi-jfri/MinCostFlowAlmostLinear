module

public import MinCostFlow.DynSpanner.Program.DynSpannerUpdateLoopDefs

/-!
# The cost of a step with `0 < j`, written with sums over sets

The cost bound of the nonempty branch (`dsStepPosNonEmptyCost`) is written with sums over the
list `E_aff.toList` that the program walks through. For the amortized analysis we write it with
sums over the set `E_aff` (`dsStepPosNonEmptyCost_toList`): the call of the sparsifier, the
lengths of the walks it returns, of the composed walks, of the old walks and of the new walks, the
old levels `oldBucketsSum` that the branch clears, the size of `J̃`, and linear terms.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

public section

/-- The cost of the nonempty branch, with sums over the set `E`. -/
theorem dsStepPosNonEmptyCost_toList (impl : SparsifyImpl) (mMax L vCap eCap j : ℕ)
    (G' J : MGraph) (piLt embJH : MinCostFlow.Embedding) (S E : Finset ℕ) (oS : ℕ) :
    let out := canonicalSparsify impl G' J embJH
    let outEmb : MinCostFlow.Embedding := fun e => shortcutWalk out.Jtilde (J.tail e) (out.emb e)
    let embMid := MinCostFlow.Embedding.comp embJH outEmb
    dsStepPosNonEmptyCost impl mMax L vCap eCap j G' J piLt embJH S E.toList oS =
      sparsifyDynCost impl mMax G' J embJH + 400 * ∑ e ∈ E, (out.emb e).length +
        70 * ∑ e ∈ E, (embMid e).length + 120 * ∑ e ∈ E, (outEmb e).length +
        800 * ∑ e ∈ E, (piLt e).length + 800 * ∑ e ∈ E, (embMid e).length +
        400 * ∑ e ∈ E, (reembedWalk G' G' piLt embMid S e).length +
        100 * ∑ e ∈ E, (piLt e).length +
        1440 * oS + 150 * (L + 1 - j) + 3150 * out.Jtilde.m + 2185 * E.card + 3525 := by
  intro out outEmb embMid
  have hsp : (dsSparsifyStageContract impl mMax 0 vCap eCap vCap eCap vCap eCap L vCap eCap 0
      G' J embJH E.toList).cost [] 0 =
      sparsifyDynCost impl mMax G' J embJH + 400 * ∑ e ∈ E, (out.emb e).length +
        300 * E.card + 1000 := by
    simp only [dsSparsifyStageContract, Finset.sum_map_toList, Finset.length_toList]
    rfl
  have hcomp : compAllCost embJH outEmb E.toList =
      70 * ∑ e ∈ E, (embMid e).length + 120 * ∑ e ∈ E, (outEmb e).length + 80 * E.card + 20 := by
    simp only [compAllCost, Finset.sum_map_toList, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, smul_eq_mul]
    simp only [embMid, comp_eq_flatMap]
    ring
  have hre : reembedAllCost piLt embMid E.toList =
      800 * ∑ e ∈ E, (piLt e).length + 800 * ∑ e ∈ E, (embMid e).length + 1100 * E.card + 20 := by
    simp only [reembedAllCost, Finset.sum_map_toList, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, smul_eq_mul, Nat.mul_add]
    ring
  simp only [dsStepPosNonEmptyCost]
  rw [hsp, hcomp, hre]
  simp only [Finset.sum_map_toList, Finset.length_toList]
  ring

end

end MinCostFlow.DynSpanner.Program
