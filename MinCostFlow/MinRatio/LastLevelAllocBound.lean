module

public import MinCostFlow.LastLevelProgram.PackedRuntimeSpace
import Mathlib.Tactic
import Mathlib.Data.Nat.Size

/-!
# A bound on the last-level allocation by the graph size (`LastLevelAllocBound`)

The last-level program of Definition 5.8 (pages 19–20) reserves its space before it reads the
lengths: `packedRuntimeAllocation G …`. This number depends on the graph `G`. The solver needs one
number that covers the last graph of every chain of a given size. This file gives it.

The allocation depends on `G` only through a few counts: the vertex and edge counts of `G`, and
those of its representative graph `representativeGraph G (fun _ => 1)`. The representative graph
keeps at most one edge of `G` per pair of ends, so it has at most `G.m` edges, and every vertex of
it is an end of one of its edges, so it has at most twice as many vertices as edges. Every space
formula of the program only grows with these counts, with the capacities and with the guest
width. We prove these monotone lemmas, and then evaluate the formulas at a graph that has the
largest counts (`countGraph`). The result is `packedRuntimeAllocation_le_bound`: for every graph
with at most `M + 1` vertices and at most `M` edges and every pair of capacities up to
`(vCap, eCap)`, the allocation is at most `packedRuntimeAllocBound … M vCap eCap`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM SparseCore LastLevelProgram DynSpanner.Program

/-- A graph with vertex set `range n` and edge set `range m`. The space formulas of the
last-level program see a graph only through its two counts, so this graph stands for every graph
with these counts. -/
@[expose] def countGraph (n m : ℕ) : MGraph :=
  ⟨Finset.range n, Finset.range m, fun _ => 0, fun _ => 0⟩

@[simp] theorem countGraph_n (n m : ℕ) : (countGraph n m).n = n := Finset.card_range n

@[simp] theorem countGraph_m (n m : ℕ) : (countGraph n m).m = m := Finset.card_range m

/-! ## Monotone lemmas -/

/-- The integer update scale grows with the vertex and edge counts. -/
theorem integerScale_le_of_counts {D : ℕ} {G G' : MGraph} (hn : G.n ≤ G'.n) (hm : G.m ≤ G'.m) :
    integerScale D G ≤ integerScale D G' := by
  unfold integerScale
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hm)
    (Nat.pow_le_pow_left (Nat.succ_le_succ (Nat.log_mono_right (Nat.add_le_add_right hn 2))) _)

/-- The weight precision grows with the vertex and edge counts, since it is the bit count of
twice the integer scale. -/
theorem weightPrecision_le_of_counts (C : ℝ) {G G' : MGraph} (hn : G.n ≤ G'.n)
    (hm : G.m ≤ G'.m) : weightPrecision C G ≤ weightPrecision C G' := by
  unfold weightPrecision
  exact Nat.size_le_size (Nat.mul_le_mul_left 2 (integerScale_le_of_counts hn hm))

private theorem unsignedDivideSpace_mono {a b : ℕ} (h : a ≤ b) :
    Num.unsignedDivideSpace a ≤ Num.unsignedDivideSpace b := by
  unfold Num.unsignedDivideSpace
  have := Nat.mul_le_mul (Nat.mul_le_mul_left 5 h) (show a + 1 ≤ b + 1 by omega)
  omega

private theorem integerDivideSpace_mono {a b : ℕ} (h : a ≤ b) :
    Num.integerDivideSpace a ≤ Num.integerDivideSpace b := by
  unfold Num.integerDivideSpace
  have := unsignedDivideSpace_mono h
  omega

/-- The space of one rounded stretch grows with the limb count. -/
theorem edgeStretchSpace_mono {a b : ℕ} (h : a ≤ b) : edgeStretchSpace a ≤ edgeStretchSpace b := by
  unfold edgeStretchSpace stretchFromLengthSpace Num.fixedDivideSpace
  have := integerDivideSpace_mono (Nat.mul_le_mul_left 3 h)
  omega

/-- The space of one narrowed weight update grows with the limb count. -/
theorem narrowWeightSpace_mono {a b : ℕ} (h : a ≤ b) :
    narrowWeightSpace a ≤ narrowWeightSpace b := by
  unfold narrowWeightSpace widenWeightSpace weightUpdateSpace
  have := integerDivideSpace_mono (show 2 * a + 1 ≤ 2 * b + 1 by omega)
  dsimp only
  omega

private theorem dynGraphSize_le {v e v' e' : ℕ} (hv : v ≤ v') (he : e ≤ e') :
    dynGraphSize v e ≤ dynGraphSize v' e' := by
  unfold dynGraphSize; omega

private theorem queryHeap_le {H H' : MGraph} {N N' : ℕ} (hn : H.n ≤ H'.n) (hm : H.m ≤ H'.m)
    (hN : N ≤ N') : queryHeap H N ≤ queryHeap H' N' := by
  have := Nat.mul_le_mul hm hN
  simp only [queryHeap, queryHeader, queryBridges, queryOriginals, queryWeights, queryLengths]
  omega

private theorem queryOriginals_le {H H' : MGraph} {N N' : ℕ} (hm : H.m ≤ H'.m) (hN : N ≤ N') :
    queryOriginals H N ≤ queryOriginals H' N' := by
  have := Nat.mul_le_mul hm hN
  simp only [queryOriginals, queryWeights, queryLengths]
  omega

private theorem queryWeights_le {H H' : MGraph} {N N' : ℕ} (hm : H.m ≤ H'.m) (hN : N ≤ N') :
    queryWeights H N ≤ queryWeights H' N' := by
  have := Nat.mul_le_mul hm hN
  simp only [queryWeights, queryLengths]
  omega

/-- The space of one widened round grows with the counts of the representative graph, the guest
width, the simulation width, the level count, the weight precision, the branch count and the
capacities. -/
theorem stagedPackedRoundSpace_mono_all {H H' : MGraph} (guest : Program)
    {D N N' sim sim' levels levels' L P P' count count' vCap vCap' eCap eCap' : ℕ}
    (hn : H.n ≤ H'.n) (hm : H.m ≤ H'.m) (hN : N ≤ N') (hsim : sim ≤ sim')
    (hlev : levels ≤ levels') (hP : P ≤ P') (hc : count ≤ count') (hv : vCap ≤ vCap')
    (he : eCap ≤ eCap') :
    stagedPackedRoundSpace H guest D N sim levels L P count vCap eCap ≤
      stagedPackedRoundSpace H' guest D N' sim' levels' L P' count' vCap' eCap' := by
  have hK : L + (P + levels + 7) / 4 ≤ L + (P' + levels' + 7) / 4 :=
    Nat.add_le_add_left (Nat.div_le_div_right (by omega)) L
  have hwidth := paddedGuestWidth_mono guest (le_refl D) hn hm hsim (queryHeap_le hn hm hN)
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hwidth
  have hq := queryOriginals_le hm hN
  have h1 := Nat.mul_le_mul hm hK
  have h2 := Nat.mul_le_mul hn hK
  have h3 := Nat.mul_le_mul (Nat.sub_le_sub_right hn 1) hK
  have h4 := Nat.mul_le_mul hm (edgeStretchSpace_mono hK)
  have h5 := Nat.mul_le_mul hm (narrowWeightSpace_mono hK)
  have h6 := Nat.mul_le_mul hm (le_refl L)
  have h7 : stagedTraversalReserve H.n levels ≤ stagedTraversalReserve H'.n levels' := by
    unfold stagedTraversalReserve
    have := Nat.mul_le_mul (Nat.add_le_add_right hlev 4) hn
    omega
  have h8 := Nat.mul_le_mul he (le_refl L)
  have h9 := dynGraphSize_le hv he
  unfold stagedPackedRoundSpace
  dsimp only
  omega

/-- The collection reservation grows with the same quantities. -/
theorem stagedPackedCollectionSpace_mono_all {H H' : MGraph} (guest : Program)
    {D N N' sim sim' levels levels' L P P' count count' vCap vCap' eCap eCap' : ℕ}
    (hn : H.n ≤ H'.n) (hm : H.m ≤ H'.m) (hN : N ≤ N') (hsim : sim ≤ sim')
    (hlev : levels ≤ levels') (hP : P ≤ P') (hc : count ≤ count') (hv : vCap ≤ vCap')
    (he : eCap ≤ eCap') :
    stagedPackedCollectionSpace H guest D N sim levels L P count vCap eCap ≤
      stagedPackedCollectionSpace H' guest D N' sim' levels' L P' count' vCap' eCap' := by
  have hr := stagedPackedRoundSpace_mono_all guest (D := D) (L := L) hn hm hN hsim hlev hP hn hv he
  have h1 := Nat.mul_le_mul hc hr
  have h2 := Nat.mul_le_mul hm (le_refl L)
  unfold stagedPackedCollectionSpace
  omega

/-- The representative initializer's reservation grows with the edge count of the input graph and
with the quantities of `stagedPackedCollectionSpace_mono_all`. -/
theorem representativePackedInitSpace_mono_all {G G' H H' : MGraph} (guest : Program)
    {D N N' sim sim' levels levels' L P P' count count' vCap vCap' eCap eCap' : ℕ}
    (hGm : G.m ≤ G'.m) (hn : H.n ≤ H'.n) (hm : H.m ≤ H'.m) (hN : N ≤ N') (hsim : sim ≤ sim')
    (hlev : levels ≤ levels') (hP : P ≤ P') (hc : count ≤ count') (hv : vCap ≤ vCap')
    (he : eCap ≤ eCap') :
    representativePackedInitSpace G H guest D N sim levels L P count vCap eCap ≤
      representativePackedInitSpace G' H' guest D N' sim' levels' L P' count' vCap' eCap' := by
  have hcol := stagedPackedCollectionSpace_mono_all guest (D := D) (L := L) hn hm hN hsim hlev hP
    hc hv he
  have hq := queryWeights_le hm hN
  unfold representativePackedInitSpace
  omega

/-- The bound on the guest width grows with the edge count. -/
theorem representativeGuestWidthBound_mono {D L m m' : ℕ} (hm : m ≤ m') :
    representativeGuestWidthBound D L m ≤ representativeGuestWidthBound D L m' := by
  unfold representativeGuestWidthBound
  have h1 := Nat.size_le_size (Nat.mul_le_mul_left 2 hm)
  have h2 := Nat.size_le_size (Nat.add_le_add_right hm 1)
  have h3 : max (2 * m).size (4 * L) ≤ max (2 * m').size (4 * L) := max_le_max h1 le_rfl
  have h4 : max (4 * L) ((1024 * D).size + 3 * (m + 1).size) ≤
      max (4 * L) ((1024 * D).size + 3 * (m' + 1).size) := max_le_max le_rfl (by omega)
  omega

/-- The bound on the scalar intermediates grows with the counts of the graph and with its other
arguments. -/
theorem packedFormatScalarBound_mono {H H' : MGraph}
    {d c L caller grid grid' Q Q' N N' sim sim' : ℕ}
    (hn : H.n ≤ H'.n) (hm : H.m ≤ H'.m) (hgrid : grid ≤ grid') (hQ : Q ≤ Q') (hN : N ≤ N')
    (hsim : sim ≤ sim') :
    packedFormatScalarBound H d c L caller grid Q N sim ≤
      packedFormatScalarBound H' d c L caller grid' Q' N' sim' := by
  have hscale := integerScale_le_of_counts (D := d) hn hm
  have hsize := Nat.size_le_size (Nat.mul_le_mul_left 2 hm)
  have hmax : max caller grid ≤ max caller grid' := max_le_max le_rfl hgrid
  unfold packedFormatScalarBound
  omega

/-- The word bound of the dispatcher grows with the counts of the graph and the capacities. -/
theorem packedRuntimeWordBound_mono {G G' : MGraph} {d c L vCap vCap' eCap eCap' : ℕ}
    (hn : G.n ≤ G'.n) (hm : G.m ≤ G'.m) (hv : vCap ≤ vCap') (he : eCap ≤ eCap') :
    packedRuntimeWordBound G d c L vCap eCap ≤ packedRuntimeWordBound G' d c L vCap' eCap' := by
  have hB := representativeGuestWidthBound_mono (D := d) (L := L) hm
  have hgrid : (1024 * d).size + 3 * (G.m + 1).size ≤ (1024 * d).size + 3 * (G'.m + 1).size := by
    have := Nat.size_le_size (Nat.add_le_add_right hm 1)
    omega
  have hsim := packedSimWidth_mono (c := c) (n := G.n) (n' := G'.n) hm hB
  have hcap : vCap * vCap * eCap ≤ vCap' * vCap' * eCap' :=
    Nat.mul_le_mul (Nat.mul_le_mul hv hv) he
  unfold packedRuntimeWordBound
  exact max_le_max (max_le_max le_rfl hcap)
    (packedFormatScalarBound_mono hn hm hgrid hB hB hsim)

/-! ## The bound -/

/-- The allocation bound of the last-level program for every graph with at most `M + 1` vertices
and at most `M` edges, at capacities up to `(vCap, eCap)`: the three branches of
`packedRuntimeAllocation`, with the counts of the graph replaced by `M + 1` and `M`, and the
counts of its representative graph by `2 M` and `M`. -/
@[expose] noncomputable def packedRuntimeAllocBound (guest : Program) (C : ℝ)
    (c₀ L M vCap eCap : ℕ) : ℕ :=
  let D := ⌈max 1 C⌉₊
  let H := countGraph (2 * M) M
  let N := representativeGuestWidthBound D L M
  max (loopOnlySpace vCap eCap L)
    (max (representativePackedInitSpace (countGraph (M + 1) M) H guest D N
        (WideWord.lsstLSimMin c₀ H.n H.m N 1) (Nat.clog 2 H.n) L (weightPrecision C H) H.m
        vCap eCap)
      (packedRuntimeWordBound (countGraph (M + 1) M) D c₀ L vCap eCap))

/-- The representative graph has at most as many edges as the graph. -/
theorem representativeGraph_m_le (G : MGraph) (ℓ : ℕ → ℝ) :
    (representativeGraph G ℓ).m ≤ G.m :=
  Finset.card_le_card fun _ hf => (Finset.mem_filter.mp (representative_mem hf).1).1

/-- **The allocation bound.** For every graph with at most `M + 1` vertices and at most `M`
edges, and every pair of capacities up to `(vCap, eCap)`, the allocation of the last-level
program is at most `packedRuntimeAllocBound guest C c₀ L M vCap eCap`. -/
theorem packedRuntimeAllocation_le_bound (G : MGraph) (guest : Program) (C : ℝ)
    {c₀ L M vc ec vCap eCap : ℕ} (hn : G.n ≤ M + 1) (hm : G.m ≤ M) (hvc : vc ≤ vCap)
    (hec : ec ≤ eCap) (i : ℕ) (args : List ℕ) :
    packedRuntimeAllocation G guest C c₀ L vc ec i args ≤
      packedRuntimeAllocBound guest C c₀ L M vCap eCap := by
  unfold packedRuntimeAllocation packedRuntimeAllocBound
  dsimp only
  split_ifs
  · refine le_max_of_le_right (max_le_max ?_ ?_)
    · let H₁ := representativeGraph G (fun _ => 1)
      have hHm : H₁.m ≤ M := (representativeGraph_m_le G _).trans hm
      have hHn : H₁.n ≤ 2 * M :=
        (representativeGraph_n_le_twice_m G _).trans (Nat.mul_le_mul_left 2 hHm)
      have hHn' : H₁.n ≤ (countGraph (2 * M) M).n := by rw [countGraph_n]; exact hHn
      have hHm' : H₁.m ≤ (countGraph (2 * M) M).m := by rw [countGraph_m]; exact hHm
      have hN := representativeGuestWidthBound_mono (D := ⌈max 1 C⌉₊) (L := L) hm
      unfold representativePackedSpaceBound
      dsimp only
      exact representativePackedInitSpace_mono_all guest
        (by rw [countGraph_m]; exact hm) hHn' hHm' hN
        (packedSimWidth_mono hHm' hN) (Nat.clog_mono_right 2 hHn')
        (weightPrecision_le_of_counts C hHn' hHm') hHm' hvc hec
    · exact packedRuntimeWordBound_mono (by rw [countGraph_n]; exact hn)
        (by rw [countGraph_m]; exact hm) hvc hec
  · exact le_max_of_le_left (by unfold loopOnlySpace dynGraphSize; have := Nat.mul_le_mul hec (le_refl L); omega)

end MinCostFlow.MinRatio
