module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitBktTable
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitComp
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitSlotRun
public import MinCostFlow.SparseCore.Program.AssemblyBranchStepCost
import Mathlib.Tactic

/-!
# The cost of the first steps of the build against the machine cost (`AssemblyFirstInitCost`)

The build (`AsmFirstInitBuildAt`) must cost at most `mul` times the machine cost `machCost` of the
model state `tr₀` of the init, with `mul` a function of `capExp` and `limbMul` only. This file
checks this for the three procedures of the build that do not come from other pieces: the bucket
table, the map from vertices to components, and the slot lists.

**The bucket table is the costly one.** It calls the bucket word once per edge, and one call costs
`bucketWordCost L_w L`, quadratic in `K = L_w + L + 1`. With `lg = bundleLogFactor M N`, the
hypotheses of the build give `L ≤ limbMul · lg` (`SparseCoreCapHyp`) and a bound on `L_w` (P4's
export), so `K ≤ 2 · Kc · lg` with `Kc = limbMul + capExp + sparseCoreReadout2LimbConst + 1`
(`limbs_succ_le`). So the table costs about `m · Kc² · lg²`. One factor `lg` is not enough to pay
for this. But `machCost` has the term `lsfInitSize G₀ · lg · lg`, and `lsfInitSize G₀ ≥ m`
(`m_le_lsfInitSize`): every edge lies in the component of its tail, which has an edge. So
`bucketTableCost` is at most `bktTableMul capExp limbMul · machCost` (`bucketTableCost_le`).

The map to the components and the slot lists cost `O(m log m)`, which `(3 m + 2) · lg` pays for
(`compMapCost_le`, `slotListCost_le`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.LSF MinCostFlow.SparseCore MinCostFlow.Chain MinCostFlow.Bundle
open MinCostFlow.DynSpanner

/-- **Every edge lies in a component with an edge**, so the size of the LSF init is at least the
number of edges. -/
theorem m_le_lsfInitSize {G : MGraph} (hG : G.IsValid) : G.m ≤ lsfInitSize G := by
  classical
  unfold lsfInitSize
  set S := (components G).filter fun C => 1 ≤ (compGraph G C).m
  -- each edge is an edge of the graph of the component of its tail
  have hsub : G.E ⊆ S.biUnion fun C => compEdgeSet G C := by
    intro e he
    have htV : G.tail e ∈ G.V := (hG e he).1
    have heC : e ∈ compEdgeSet G (compOf G (G.tail e)) := by
      unfold compEdgeSet
      exact Finset.mem_filter.mpr ⟨he, self_mem_compOf htV⟩
    refine Finset.mem_biUnion.mpr ⟨compOf G (G.tail e), ?_, heC⟩
    refine Finset.mem_filter.mpr ⟨compOf_mem_components htV, ?_⟩
    unfold MGraph.m compGraph
    exact Finset.card_pos.mpr ⟨e, heC⟩
  calc G.m = G.E.card := rfl
    _ ≤ (S.biUnion fun C => compEdgeSet G C).card := Finset.card_le_card hsub
    _ ≤ S.sum fun C => (compEdgeSet G C).card := Finset.card_biUnion_le
    _ ≤ S.sum fun C => (compGraph G C).m + (compGraph G C).n + 1 :=
        Finset.sum_le_sum fun C _ => Nat.le_succ_of_le (Nat.le_add_right _ _)

/-- The machine cost of the init dominates `lsfInitSize G · lg · lg`. -/
theorem initMachCost_ge_lsf {depth : ℕ} (lsfInit : LSFInit)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) (params : ℕ → SparsifyParams)
    (spanConst k M N : ℕ) (G : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) (j : ℕ) :
    lsfInitSize G * bundleLogFactor M N * bundleLogFactor M N ≤
      (initBundleTreeWithParams lsfInit depth sparsify params spanConst k M N G ℓ₀ ord
        j).machCost := by
  have h1 : 1 ≤ bundleLogFactor M N := by
    unfold bundleLogFactor
    have : 1 ≤ Nat.log 2 (M + N + 2) + 1 := Nat.succ_pos _
    exact Nat.one_le_pow 2 _ this
  have hsq : bundleLogFactor M N ≤ bundleLogFactor M N ^ 2 := by
    calc bundleLogFactor M N = bundleLogFactor M N * 1 := (Nat.mul_one _).symm
      _ ≤ bundleLogFactor M N * bundleLogFactor M N := Nat.mul_le_mul_left _ h1
      _ = bundleLogFactor M N ^ 2 := (sq _).symm
  have hmul : lsfInitSize G * bundleLogFactor M N ≤ lsfInitSize G * bundleLogFactor M N ^ 2 :=
    Nat.mul_le_mul_left _ hsq
  exact Nat.mul_le_mul_right _ (by dsimp only [initBundleTreeWithParams]; omega)

/-- The factor of the bucket table. -/
def bktTableMul (capExp limbMul : ℕ) : ℕ :=
  9200 * (limbMul + capExp + sparseCoreReadout2LimbConst + 1) ^ 2 + 150

/-- One call of the bucket word costs at most `2282 K²`, for `K = L_w + L + 1`. -/
theorem bucketWordCost_le (Lw L : ℕ) : bucketWordCost Lw L + 60 ≤ 2282 * (Lw + L + 1) ^ 2 := by
  unfold bucketWordCost
  set K := Lw + L + 1
  have hK : 1 ≤ K := by omega
  have h1 : K ≤ K ^ 2 := by nlinarith
  nlinarith

/-- **The bucket table is paid for by the machine cost.** With `lg = bundleLogFactor M N`, if
`L ≤ limbMul · lg`, `L_w` is within the bound of P4's export, `G` is valid and
`lsfInitSize G · lg · lg ≤ machCost`, then the table costs at most
`bktTableMul capExp limbMul · machCost`. -/
theorem bucketTableCost_le {Lw L M N capExp limbMul machCost : ℕ} {G : MGraph}
    (hL : L ≤ limbMul * bundleLogFactor M N)
    (hLw : Lw ≤ L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1))
    (hG : G.IsValid) (hmc : lsfInitSize G * bundleLogFactor M N * bundleLogFactor M N ≤ machCost)
    (hmc1 : 1 ≤ machCost) :
    bucketTableCost Lw L G.m ≤ bktTableMul capExp limbMul * machCost := by
  set lg := bundleLogFactor M N
  set Kc := limbMul + capExp + sparseCoreReadout2LimbConst + 1
  have hLw1 : Lw + 1 ≤ Kc * lg := limbs_succ_le hL hLw
  have hLK : L ≤ Kc * lg := hL.trans (Nat.mul_le_mul_right _ (by omega))
  have hK : Lw + L + 1 ≤ 2 * Kc * lg := by
    have : 2 * Kc * lg = Kc * lg + Kc * lg := by ring
    omega
  have hK2 : (Lw + L + 1) ^ 2 ≤ 4 * Kc ^ 2 * (lg * lg) := by
    calc (Lw + L + 1) ^ 2 ≤ (2 * Kc * lg) ^ 2 := Nat.pow_le_pow_left hK 2
      _ = 4 * Kc ^ 2 * (lg * lg) := by ring
  have hm : G.m * (lg * lg) ≤ machCost := by
    calc G.m * (lg * lg) ≤ lsfInitSize G * (lg * lg) :=
          Nat.mul_le_mul_right _ (m_le_lsfInitSize hG)
      _ = lsfInitSize G * lg * lg := by ring
      _ ≤ machCost := hmc
  have hcall := bucketWordCost_le Lw L
  calc bucketTableCost Lw L G.m = G.m * (bucketWordCost Lw L + 60) + 150 := rfl
    _ ≤ G.m * (2282 * (4 * Kc ^ 2 * (lg * lg))) + 150 * machCost := by
        have := Nat.mul_le_mul_left G.m (hcall.trans (Nat.mul_le_mul_left 2282 hK2))
        omega
    _ = 9128 * Kc ^ 2 * (G.m * (lg * lg)) + 150 * machCost := by ring
    _ ≤ 9128 * Kc ^ 2 * machCost + 150 * machCost := by
        have := Nat.mul_le_mul_left (9128 * Kc ^ 2) hm
        omega
    _ ≤ bktTableMul capExp limbMul * machCost := by
        have e : bktTableMul capExp limbMul * machCost =
            9200 * Kc ^ 2 * machCost + 150 * machCost := by
          unfold bktTableMul; ring
        have : 9128 * Kc ^ 2 * machCost ≤ 9200 * Kc ^ 2 * machCost :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))
        omega

/-- **The map to the components is paid for** by `(3 m + 2) · lg`, for `n ≤ m + 1`. -/
theorem compMapCost_le {n m machCost lg : ℕ} (hnm : n ≤ m + 1) (hlg : 1 ≤ lg)
    (hmc : (3 * m + 2) * lg ≤ machCost) : compMapCost n m ≤ 600 * machCost := by
  have h1 : 3 * m + 2 ≤ (3 * m + 2) * lg := Nat.le_mul_of_pos_right _ hlg
  unfold compMapCost
  omega

/-- `log₂ (m + 1) + 1` is at most `lg = (log₂ (M + N + 2) + 1)²` when `m ≤ M`. -/
theorem log_succ_le_bundleLogFactor {m M N : ℕ} (hm : m ≤ M) :
    Nat.log 2 (m + 1) + 1 ≤ bundleLogFactor M N := by
  unfold bundleLogFactor
  have h : Nat.log 2 (m + 1) ≤ Nat.log 2 (M + N + 2) := Nat.log_mono_right (by omega)
  nlinarith

/-- **The slot lists are paid for** by `(3 m + 2) · lg`, when the number of components and the
number of forest edges are at most `m + 1` and `m ≤ M`. -/
theorem slotListCost_le {m nComp nF M N machCost : ℕ} (hc : nComp ≤ m + 1) (hF : nF ≤ m + 1)
    (hm : m ≤ M) (hmc : (3 * m + 2) * bundleLogFactor M N ≤ machCost) :
    slotListCost m nComp nF ≤ 500 * machCost := by
  set lg := bundleLogFactor M N
  have hl := log_succ_le_bundleLogFactor (N := N) hm
  have hlg : 1 ≤ lg := by omega
  have h1 : m * (Nat.log 2 (m + 1) + 1) ≤ m * lg := Nat.mul_le_mul_left _ hl
  have h2 : 3 * m + 2 ≤ (3 * m + 2) * lg := Nat.le_mul_of_pos_right _ hlg
  have h3 : (3 * m + 2) * lg = 3 * (m * lg) + 2 * lg := by ring
  unfold slotListCost slotFrontCost slotTailCost
  omega

end MinCostFlow.SparseCore.Program
