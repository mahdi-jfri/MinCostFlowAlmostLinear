module

public import MinCostFlow.SparseCore.Program.RestartIface
public import MinCostFlow.DynSpanner.Program.DynSpannerAmortInput
import MinCostFlow.DynSpanner.Program.DynSpannerInitCost

/-!
# A polynomial bound on the space of a spanner initialization (`AssemblyBranchSpaceSpan`)

The restart of a branch builds one bucket spanner per slot. Its heap space is
`spanActivateSpace P G = dsFixedSize P.L P.vCap P.eCap + dsInitCoreSpaceBound …` (P6). To bound the
space of the restart by a polynomial in the sizes, as `AsmBranchAt.restart_runs` asks, each term
must be polynomial. Two terms need an argument:
* `2 ^ (w' + 1)`, where `w' = wordSize impl.cw input` is the word size of the cited sparsifier on
  the canonical input. Since `w' = cw · (⌊log₂ X⌋ + 1)` with `X` the length plus the largest word
  plus `2`, we get `2 ^ (w' + 1) ≤ 2 · (2X) ^ cw` (`two_pow_wordSize_succ_le`), and `X` is linear in
  the graph (`canonSparsifyInput_size_le`). The degree is the constant `impl.cw` of the cited
  sparsifier.
* `⌈γ_ℓ mMax⌉`, the walk length bound of the cited sparsifier. It is a function of `mMax` that
  `SparsifyImpl` does not bound, so the bound below keeps it as a factor.

The fixed part is linear in the depth and the caps (`dsFixedSize_le`). The core part is
`dsInitCoreSpaceBound_le`: its space is at most
`2 · (36 (n + 2m + 1)) ^ cw + 30 (m + 1) (⌈γ_ℓ mMax⌉ + 1) + 3 n + dynGraphSize vCap eCap + eCap + 10`
for a graph with `n` vertices and `m` edges. Together: `spanActivateSpace_le`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

/-- `2 ^ (⌊log₂ X⌋ + 1) ≤ 2 X` for `X ≥ 1`. -/
theorem two_pow_log_succ_le {X : ℕ} (hX : 1 ≤ X) : 2 ^ (Nat.log 2 X + 1) ≤ 2 * X := by
  rw [pow_succ, mul_comm]
  exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (by omega))

/-- **The word size of an input is logarithmic**: `2 ^ (wordSize c input + 1)` is at most
`2 · (2X) ^ c`, where `X` is the length of the input plus its largest word plus `2`. -/
theorem two_pow_wordSize_succ_le (c : ℕ) (input : List ℕ) :
    2 ^ (WordRAM.wordSize c input + 1) ≤
      2 * (2 * (input.length + input.foldr max 0 + 2)) ^ c := by
  unfold WordRAM.wordSize
  set X := input.length + input.foldr max 0 + 2
  have h := two_pow_log_succ_le (X := X) (by omega)
  rw [pow_succ, mul_comm (2 ^ _) 2, mul_comm c, pow_mul]
  exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left h c)

/-- **The space of the core of a spanner initialization is polynomial** in the size of the graph
and the caps, with degree `impl.cw`, times the walk length bound `⌈γ_ℓ mMax⌉`. -/
theorem dsInitCoreSpaceBound_le (impl : SparsifyImpl) (mMax vCap eCap : ℕ) (G : MGraph) :
    dsInitCoreSpaceBound impl mMax vCap eCap G ≤
      2 * (36 * (G.n + 2 * G.m + 1)) ^ impl.cw +
        30 * (G.m + 1) * (Nat.ceil (impl.γ_ℓ mMax) + 1) + 3 * G.n +
        dynGraphSize vCap eCap + eCap + 10 := by
  unfold dsInitCoreSpaceBound
  simp only []
  set Gact := activeSubgraph G
  set input := canonSparsifyInput Gact Gact idEmb
  have hn : Gact.n ≤ G.n := activeSubgraph_n_le G
  have hm : Gact.m = G.m := rfl
  have hlen : idEmb.length Gact ≤ 1 := idEmb_length_le_one Gact
  have hsize := canonSparsifyInput_size_le Gact Gact idEmb
  have hX : input.length + input.foldr max 0 + 2 ≤ 18 * (G.n + 2 * G.m + 1) := by
    refine hsize.trans (Nat.mul_le_mul_left 18 ?_)
    have : Gact.m * (idEmb.length Gact + 1) ≤ G.m * 2 := by
      rw [hm]; exact Nat.mul_le_mul_left _ (by omega)
    omega
  have hpow : 2 ^ (WordRAM.wordSize impl.cw input + 1) ≤
      2 * (36 * (G.n + 2 * G.m + 1)) ^ impl.cw := by
    refine (two_pow_wordSize_succ_le impl.cw input).trans (Nat.mul_le_mul_left 2 ?_)
    exact Nat.pow_le_pow_left (by omega) _
  set g := Nat.ceil (impl.γ_ℓ mMax)
  have h3 : G.m * (1 + 2 * g) + 9 * G.m * (g + 1) + 17 * G.m ≤ 30 * (G.m + 1) * (g + 1) := by
    nlinarith
  omega

/-- **The fixed part of a spanner is linear in the depth and the caps.** -/
theorem dsFixedSize_le (L vCap eCap : ℕ) :
    dsFixedSize L vCap eCap ≤ 100 * ((L + 1) * (vCap + eCap + 1)) := by
  simp only [dsFixedSize, dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase,
    dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase, dsEdgeDomGenBase,
    dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase, dsHNextBase, dsMinHBase, dsAuxPtr,
    dsHPtr, dsGPtr, dsHdrSize, dynGraphSize]
  have hA : eCap ≤ (L + 1) * eCap := Nat.le_mul_of_pos_left _ (by omega)
  have hB : vCap ≤ (L + 1) * vCap := Nat.le_mul_of_pos_left _ (by omega)
  have hC : (L + 1) * (vCap + eCap + 1) = (L + 1) * vCap + (L + 1) * eCap + (L + 1) := by ring
  rw [hC]
  omega

/-- **The space of a spanner initialization is polynomial**: linear in the depth `P.L` and the
caps for the fixed part, and of degree `impl.cw` in the graph for the core
(`dsInitCoreSpaceBound_le`), times the walk length bound `⌈γ_ℓ mMax⌉`. -/
theorem spanActivateSpace_le (P : DSParams) (G : MGraph) :
    spanActivateSpace P G ≤
      100 * ((P.L + 1) * (P.vCap + P.eCap + 1)) +
        (2 * (36 * (G.n + 2 * G.m + 1)) ^ P.impl.cw +
          30 * (G.m + 1) * (Nat.ceil (P.impl.γ_ℓ P.mMax) + 1) + 3 * G.n +
          dynGraphSize P.vCap P.eCap + P.eCap + 10) :=
  Nat.add_le_add (dsFixedSize_le _ _ _) (dsInitCoreSpaceBound_le _ _ _ _ _)

end MinCostFlow.SparseCore.Program
