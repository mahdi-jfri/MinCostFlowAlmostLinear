module

public import MinCostFlow.DynSpanner.Tools
public import MinCostFlow.Spanner.MGraphSpec
public import MinCostFlow.Spanner.PathDSContract
public import MinCostFlow.Spanner.Theorem81
public import MinCostFlow.DynSpanner.Program.GraphTranslateRev
public import WordRAM.Entry

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Static `Sparsify` Word-RAM Contract Parameter (`SparsifyContract`)

Specifies the guest Word-RAM contract interface `sparsifyGuestContract` and parameter record
`SparsifyImpl` for Algorithm 4 (`Sparsify(H', J, Π_{J → H'})` of Theorem 8.1, arXiv:2309.16629v1
p. 39), bridged to both:
1. `MinCostFlow.Spanner.theorem_8_1_at_cap` on `Cited.Graph` / `WalkAt` / `EmbAt` (`CitedSparsifyProp`);
2. `MinCostFlow.DynSpanner.SparsifySpec` on `MGraph` / `Embedding` (`mGraph_props_of_citedSparsifyProp`).
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.Cited

@[expose] public section

/-! ## Mathematical guest predicate (`CitedSparsifyProp`) -/

/-- Exact mathematical postcondition guaranteed by Theorem 8.1 (`Sparsify(H', J, embJH)`) on
`Cited.Graph`, `kept : List ℕ`, and `embJJtilde : ℕ → Walk` at edge-count cap `mMax`. -/
def CitedSparsifyProp (_mMax : ℕ) (γ_c γ_ℓ K_s : ℝ) (p_s : ℕ)
    (H' J : Cited.Graph) (embJH : ℕ → Walk)
    (cJtilde : Cited.Graph) (kept : List ℕ) (embJJtilde : ℕ → Walk) : Prop :=
  kept.Nodup ∧
  (∀ k ∈ kept, k < J.m) ∧
  cJtilde.n = J.n ∧
  cJtilde.edges = kept.map (fun k => J.edges.getD k (0, 0)) ∧
  cJtilde.IsValid ∧
  Spanner.IsEmbedding J cJtilde embJJtilde ∧
  Spanner.vcong J H' (fun _ => 1)
    (Spanner.compose cJtilde (Spanner.restrictEmb embJH kept) embJJtilde) ≤
      γ_c * (Spanner.length J embJH : ℝ) *
        (Spanner.vcong J H' (fun _ => 1) embJH + (Spanner.maxDeg J : ℝ)) ∧
  (Spanner.length J embJJtilde : ℝ) ≤ γ_ℓ ∧
  (cJtilde.m : ℝ) ≤ K_s * (J.n : ℝ) * γ_ℓ * (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ p_s

/-- Restriction of a `J → H'` embedding to the kept edge indices is an embedding `cJtilde → H'`
whenever `cJtilde` is the subgraph formed by `kept`. -/
theorem restrictEmb_isEmbedding_of_edges {H' J cJtilde : Cited.Graph} {embJH : ℕ → Walk}
    {kept : List ℕ}
    (hemb : Spanner.IsEmbedding J H' embJH)
    (hkept : ∀ k ∈ kept, k < J.m)
    (hJn : cJtilde.n = J.n)
    (hJed : cJtilde.edges = kept.map (fun k => J.edges.getD k (0, 0))) :
    Spanner.IsEmbedding cJtilde H' (Spanner.restrictEmb embJH kept) := by
  refine ⟨hJn.symm ▸ hemb.1, fun i hi => ?_⟩
  have hi_k : i < kept.length := by
    simpa [Cited.Graph.m, hJed] using hi
  have hk_lt : kept[i]'hi_k < J.m := hkept _ (List.getElem_mem hi_k)
  have hwalk := hemb.2 (kept[i]'hi_k) hk_lt
  have hEdge : cJtilde.edges[i]'hi = J.edges[kept[i]'hi_k]'hk_lt := by
    simp only [hJed, List.getElem_map, List.getD_eq_getElem _ (0, 0) hk_lt]
  have hWalkEq : Spanner.restrictEmb embJH kept i = embJH (kept[i]'hi_k) := by
    dsimp only [Spanner.restrictEmb]
    rw [List.getD_eq_getElem kept 0 hi_k]
  rw [hEdge, hWalkEq]
  exact hwalk

/-- Bridge from `MinCostFlow.Spanner.theorem_8_1_at_cap_with_time` to `CitedSparsifyProp`. -/
theorem citedSparsifyProp_of_theorem_8_1 (tools : SpannerTools) (costs : SpannerToolCosts)
    (hdec : DecomposeMonotone tools.decompose) (hpds : PathDSMonotone tools.pathDS)
    (mMax : ℕ) {H' J : Cited.Graph} {embJH : ℕ → Walk}
    (hJ : J.IsValid) (hemb : Spanner.IsEmbedding J H' embJH)
    (hJm : J.m ≤ mMax) (hLen : 1 ≤ J.m → 1 ≤ Spanner.length J embJH) :
    let out := Spanner.sparsify tools H' J embJH
    let φ_min := hdec.φ_lb mMax
    let c_deg := tools.constructExpander.c_deg
    let φ_Const := tools.constructExpander.φ_Const
    let γ_ℓ := capGammaL c_deg φ_Const tools.pathDS φ_min mMax
    let γ_c := capGammaC c_deg φ_Const tools.pathDS φ_min mMax
    let K_s := 1 + tools.decompose.c_ℓ * c_deg / Real.log 2
    CitedSparsifyProp mMax γ_c γ_ℓ K_s 1 H' J embJH out.Jtilde out.keptEdges out.embJJtilde := by
  have ht := theorem_8_1_at_cap_with_time tools costs hdec hpds mMax H' J embJH hJ hemb hJm hLen
  rcases ht with ⟨hnodup, hkept, hn, _, hvalid, _, hembJJ, _, _, _, _, _, _, hvcong, hlen, _, hsp, _⟩
  refine ⟨hnodup, hkept, hn, ?_, hvalid, hembJJ, hvcong, hlen, ?_⟩
  · simp only [Spanner.sparsify, sparsifyLocal]
  · rw [pow_one]; exact hsp

/-! ## Memory readers for guest contract cost and space -/

/-- Maximum edge length of cited embedding walks read from `mem` at `[pEmb .. pEmb + mJ)`. -/
def readCitedEmbLen (mem : ℕ → ℕ) (pEmb mJ : ℕ) : ℕ :=
  ((List.range mJ).map fun j => mem (mem (pEmb + j)) - 1).foldr max 0

/-- Total number of vertices stored across all cited embedding walks at `[pEmb .. pEmb + mJ)`. -/
def readTotalEmbVerts (mem : ℕ → ℕ) (pEmb mJ : ℕ) : ℕ :=
  ((List.range mJ).map fun j => mem (mem (pEmb + j))).sum

/-- Input size metric computed solely from `(mem 0, mem 1, mem 2)`:
`H'.n + H'.m + J.n + J.m + ∑_{j < J.m} (emb j).verts.length`. -/
def citedInputSize (mem : ℕ → ℕ) : ℕ :=
  let H := readGraph mem (mem 0)
  let J := readGraph mem (mem 1)
  H.n + H.m + J.n + J.m + readTotalEmbVerts mem (mem 2) J.m

/-- Maximum memory value stored in `[0 .. heap)`. -/
def citedMaxWord (mem : ℕ → ℕ) (heap : ℕ) : ℕ :=
  ((List.range heap).map mem).foldr max 0

private lemma list_foldr_max_eq_of_eq (f g : ℕ → ℕ) (n : ℕ) (h : ∀ j < n, f j = g j) :
    ((List.range n).map f).foldr max 0 = ((List.range n).map g).foldr max 0 := by
  have hmap : (List.range n).map f = (List.range n).map g := by
    refine List.map_congr_left fun j hj => ?_
    exact h j (List.mem_range.mp hj)
  rw [hmap]

private lemma list_sum_map_range (f : ℕ → ℕ) :
    ∀ n : ℕ, ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton,
      Finset.sum_range_succ, list_sum_map_range f n]

private lemma foldr_max_range_eq_finset_fold (f : ℕ → ℕ) :
    ∀ n : ℕ, ((List.range n).map f).foldr max 0 = Finset.fold max 0 f (Finset.range n)
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.map_singleton, List.foldr_append, List.foldr_cons,
      List.foldr_nil, Nat.max_zero, Finset.range_add_one,
      Finset.fold_insert Finset.notMem_range_self]
    have foldr_max : ∀ (l : List ℕ) (a : ℕ), l.foldr max a = max (l.foldr max 0) a := by
      intro l
      induction l with
      | nil => intro a; simp
      | cons x xs ihxs =>
        intro a; simp only [List.foldr_cons]; rw [ihxs a, ihxs 0]; omega
    rw [foldr_max, foldr_max_range_eq_finset_fold f n, Nat.max_comm]

theorem readCitedEmbLen_eq_length {mem : ℕ → ℕ} {pEmb : ℕ} {H' J : Cited.Graph} {embJH : ℕ → Walk}
    (hEmb : EmbAt mem pEmb J.m embJH) (hIsEmb : Spanner.IsEmbedding J H' embJH) :
    readCitedEmbLen mem pEmb J.m = Spanner.length J embJH := by
  unfold readCitedEmbLen Spanner.length
  have hj_eq : ∀ j < J.m, mem (mem (pEmb + j)) - 1 = (embJH j).edges.length := by
    intro j hj
    have hWalkAt : WalkAt mem (mem (pEmb + j)) (embJH j) := hEmb j hj
    have hm0 : mem (mem (pEmb + j)) = (embJH j).verts.length := by
      simpa [WalkAt, Walk.encode] using hWalkAt 0 (by simp [Walk.encode])
    have hw := hIsEmb.2 j hj
    rcases hw with ⟨_, _, ⟨hPv, hPe, _⟩ | ⟨_, hlen, _⟩⟩
    · simp [hm0, hPv, hPe]
    · simp [hm0, hlen]
  rw [list_foldr_max_eq_of_eq _ (fun j => (embJH j).edges.length) J.m hj_eq]
  exact foldr_max_range_eq_finset_fold (fun j => (embJH j).edges.length) J.m

theorem readTotalEmbVerts_eq {mem : ℕ → ℕ} {pEmb mJ : ℕ} {embJH : ℕ → Walk}
    (hEmb : EmbAt mem pEmb mJ embJH) :
    readTotalEmbVerts mem pEmb mJ = ∑ j ∈ Finset.range mJ, (embJH j).verts.length := by
  unfold readTotalEmbVerts
  rw [list_sum_map_range]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hWalkAt := hEmb j (Finset.mem_range.mp hj)
  simpa [WalkAt, Walk.encode] using hWalkAt 0 (by simp [Walk.encode])

theorem citedInputSize_eq {mem : ℕ → ℕ} {H' J : Cited.Graph} {embJH : ℕ → Walk}
    (hH : GraphAt mem (mem 0) H') (hJ : GraphAt mem (mem 1) J)
    (hEmb : EmbAt mem (mem 2) J.m embJH) :
    citedInputSize mem =
      H'.n + H'.m + J.n + J.m + ∑ j ∈ Finset.range J.m, (embJH j).verts.length := by
  unfold citedInputSize
  dsimp only
  rw [graphAt_iff_readGraph.mp hH, graphAt_iff_readGraph.mp hJ, readTotalEmbVerts_eq hEmb]

/-! ## Guest Word-RAM contract (`sparsifyGuestContract`) and `SparsifyImpl` -/

/-- Heap-based Word-RAM contract for a guest `Sparsify` procedure at guest word size `w`,
carrying explicit time-overhead factor `γ_t ≥ 1` matching `DynSpanner.SparsifySpecWithTime`
(Theorem 8.1).
Arguments `[0, heap]` expect relative offsets `[pH, pJ, pEmb]` at addresses `0, 1, 2` with
`GraphAt H'`, `GraphAt J`, and `EmbAt embJH` packed inside `[0 .. heap)`.
Output writes `SparsifyOutRelocAt mem' 0 heap retHeap J.m cJtilde kept embJJtilde` and returns
`retHeap` with `ZeroFrom mem' retHeap`. -/
noncomputable def sparsifyGuestContractWithTime (mMax : ℕ) (γ_c γ_ℓ K_s : ℝ) (p_s : ℕ)
    (K_t γ_t : ℝ) (p_t : ℕ) (cw : ℕ) (space : ℕ → ℕ) (w : ℕ) : Contract :=
  have C := WordRAM.heapContract w
    (fun args mem =>
      ∃ (heap : ℕ) (H' J : Cited.Graph) (embJH : ℕ → Walk),
        args = [0, heap] ∧
        16 ≤ 2 ^ w ∧
        3 ≤ heap ∧
        mem 0 + H'.encode.length ≤ heap ∧
        mem 1 + J.encode.length ≤ heap ∧
        mem 2 + J.m ≤ heap ∧
        GraphAt mem (mem 0) H' ∧
        GraphAt mem (mem 1) J ∧
        EmbAt mem (mem 2) J.m embJH ∧
        EmbBounded mem (mem 2) J.m embJH heap ∧
        H'.IsValid ∧ J.IsValid ∧ Spanner.IsEmbedding J H' embJH ∧
        J.m ≤ mMax ∧
        (1 ≤ J.m → 1 ≤ Spanner.length J embJH) ∧
        cw * (Nat.log 2 (heap + citedMaxWord mem heap + 2) + 1) ≤ w)
    (fun _ _ _ => True)
    (fun _args mem =>
      let J := readGraph mem (mem 1)
      let l := readCitedEmbLen mem (mem 2) J.m
      ⌈K_t * γ_t * (1 + (J.n : ℝ) + (J.m : ℝ) * γ_ℓ ^ 2 * (l : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ p_t⌉₊)
    (fun _args mem => space (citedInputSize mem))
  { pre := C.pre
    post := fun args mem v mem' =>
      C.post args mem v mem' ∧
      ∃ (heap : ℕ) (H' J : Cited.Graph) (embJH : ℕ → Walk)
        (cJtilde : Cited.Graph) (kept : List ℕ) (embJJtilde : ℕ → Walk),
        args = [0, heap] ∧
        GraphAt mem (mem 0) H' ∧
        GraphAt mem (mem 1) J ∧
        EmbAt mem (mem 2) J.m embJH ∧
        CitedSparsifyProp mMax γ_c γ_ℓ K_s p_s H' J embJH cJtilde kept embJJtilde ∧
        SparsifyOutRelocAt mem' 0 heap v J.m cJtilde kept embJJtilde
    cost := C.cost }

/-- Guest Word-RAM contract specialized to unit time overhead (`γ_t = 1`). -/
noncomputable def sparsifyGuestContract (mMax : ℕ) (γ_c γ_ℓ K_s : ℝ) (p_s : ℕ) (K_t : ℝ) (p_t : ℕ)
    (cw : ℕ) (space : ℕ → ℕ) (w : ℕ) : Contract :=
  sparsifyGuestContractWithTime mMax γ_c γ_ℓ K_s p_s K_t 1 p_t cw space w

/-- Deterministic guest Word-RAM implementation of static `Sparsify` (`procs` independent of `mMax`).
The single fixed program `{ procs := procs }` meets `sparsifyGuestContractWithTime` with parameters
`(γ_c mMax, γ_ℓ mMax, γ_t mMax)` for every edge cap `mMax : ℕ` and sufficiently large word size `w`. -/
structure SparsifyImpl where
  γ_c : ℕ → ℝ
  γ_ℓ : ℕ → ℝ
  K_s : ℝ
  p_s : ℕ
  K_t : ℝ
  γ_t : ℕ → ℝ := fun _ => 1
  p_t : ℕ
  cw : ℕ
  space : ℕ → ℕ
  C_space : ℕ
  c_space : ℕ
  hγ_c : ∀ mMax, 1 ≤ γ_c mMax
  hγ_ℓ : ∀ mMax, 1 ≤ γ_ℓ mMax
  hK_s : 0 ≤ K_s
  hK_t : 0 ≤ K_t
  hγ_t : ∀ mMax, 1 ≤ γ_t mMax := by intro _; norm_num
  hcw : 2 ≤ cw
  hC_space : 1 ≤ C_space
  hspace_le : ∀ s, space s ≤ C_space * (s + 2) ^ c_space
  hcw_space : ∀ heap mVal s, 3 ≤ heap → s ≤ 3 * (heap + mVal) →
    heap + space s < (heap + mVal + 2) ^ cw
  procs : List Stmt
  hprocs_nonempty : 0 < procs.length
  hprocs_noRand : ∀ s ∈ procs, s.NoRand
  spec : ∀ mMax w : ℕ,
    MeetsContract w { procs := procs } 0
      (sparsifyGuestContractWithTime mMax (γ_c mMax) (γ_ℓ mMax) K_s p_s K_t (γ_t mMax) p_t cw space w)

/-- Standalone guest `Program` extracted from a `SparsifyImpl`. -/
def SparsifyImpl.program (impl : SparsifyImpl) : Program :=
  { procs := impl.procs }

theorem SparsifyImpl.program_isDeterministic (impl : SparsifyImpl) :
    impl.program.IsDeterministic :=
  impl.hprocs_noRand

theorem SparsifyImpl.spec_of_one (impl : SparsifyImpl) {mMax : ℕ} (h1 : impl.γ_t mMax = 1) (w : ℕ) :
    MeetsContract w { procs := impl.procs } 0
      (sparsifyGuestContract mMax (impl.γ_c mMax) (impl.γ_ℓ mMax) impl.K_s impl.p_s
        impl.K_t impl.p_t impl.cw impl.space w) := by
  simpa [sparsifyGuestContract, h1] using impl.spec mMax w

/-- Fixed-edge-cap specialization of `SparsifyImpl` retained for single-cap callers. -/
structure FixedCapSparsifyImpl where
  mMax : ℕ
  γ_c : ℝ
  γ_ℓ : ℝ
  K_s : ℝ
  p_s : ℕ
  K_t : ℝ
  γ_t : ℝ := 1
  p_t : ℕ
  cw : ℕ
  space : ℕ → ℕ
  C_space : ℕ
  c_space : ℕ
  hγ_c : 1 ≤ γ_c
  hγ_ℓ : 1 ≤ γ_ℓ
  hK_s : 0 ≤ K_s
  hK_t : 0 ≤ K_t
  hγ_t : 1 ≤ γ_t := by norm_num
  hcw : 2 ≤ cw
  hC_space : 1 ≤ C_space
  hspace_le : ∀ s, space s ≤ C_space * (s + 2) ^ c_space
  hcw_space : ∀ heap mVal s, 3 ≤ heap → s ≤ 3 * (heap + mVal) →
    heap + space s < (heap + mVal + 2) ^ cw
  procs : List Stmt
  hprocs_nonempty : 0 < procs.length
  hprocs_noRand : ∀ s ∈ procs, s.NoRand
  spec : ∀ w : ℕ,
    MeetsContract w { procs := procs } 0
      (sparsifyGuestContractWithTime mMax γ_c γ_ℓ K_s p_s K_t γ_t p_t cw space w)

/-- Specialize a uniform `SparsifyImpl` to a fixed edge cap `mMax`. -/
def SparsifyImpl.atCap (impl : SparsifyImpl) (mMax : ℕ) : FixedCapSparsifyImpl where
  mMax := mMax
  γ_c := impl.γ_c mMax
  γ_ℓ := impl.γ_ℓ mMax
  K_s := impl.K_s
  p_s := impl.p_s
  K_t := impl.K_t
  γ_t := impl.γ_t mMax
  p_t := impl.p_t
  cw := impl.cw
  space := impl.space
  C_space := impl.C_space
  c_space := impl.c_space
  hγ_c := impl.hγ_c mMax
  hγ_ℓ := impl.hγ_ℓ mMax
  hK_s := impl.hK_s
  hK_t := impl.hK_t
  hγ_t := impl.hγ_t mMax
  hcw := impl.hcw
  hC_space := impl.hC_space
  hspace_le := impl.hspace_le
  hcw_space := impl.hcw_space
  procs := impl.procs
  hprocs_nonempty := impl.hprocs_nonempty
  hprocs_noRand := impl.hprocs_noRand
  spec := impl.spec mMax

/-- Helper showing any polynomial `space s ≤ C_space * (s + 2) ^ c_space` satisfies
`hcw_space` once `cw` is chosen large enough. -/
theorem hcw_space_of_poly {C_space c_space cw : ℕ} {space : ℕ → ℕ}
    (hsp : ∀ s, space s ≤ C_space * (s + 2) ^ c_space)
    (hcw1 : c_space + 1 ≤ cw)
    (hcw2 : C_space * 3 ^ c_space + 1 ≤ 2 ^ (cw - (c_space + 1))) :
    ∀ heap mVal s, 3 ≤ heap → s ≤ 3 * (heap + mVal) →
      heap + space s < (heap + mVal + 2) ^ cw := by
  intro heap mVal s hh hs
  set b := heap + mVal + 2
  have hb2 : 2 ≤ b := by omega
  have hs_le : s + 2 ≤ 3 * b := by omega
  have h1 : space s ≤ C_space * (3 * b) ^ c_space :=
    le_trans (hsp s) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs_le _))
  have h2 : (3 * b) ^ c_space = 3 ^ c_space * b ^ c_space := Nat.mul_pow 3 b c_space
  have hbc_le : b ^ c_space ≤ b ^ (c_space + 1) :=
    Nat.pow_le_pow_right (by omega) (Nat.le_succ _)
  have hheap_lt : heap < b ^ (c_space + 1) := by
    have h1pow : b ≤ b ^ (c_space + 1) := by
      simpa using Nat.pow_le_pow_right (by omega) (by omega : 1 ≤ c_space + 1)
    omega
  have hsp_le : C_space * (3 * b) ^ c_space ≤ C_space * 3 ^ c_space * b ^ (c_space + 1) := by
    rw [h2, ← mul_assoc]
    exact Nat.mul_le_mul_left _ hbc_le
  have h3 : heap + space s < (C_space * 3 ^ c_space + 1) * b ^ (c_space + 1) := by
    nlinarith
  have h4 : (C_space * 3 ^ c_space + 1) * b ^ (c_space + 1) ≤
      b ^ (cw - (c_space + 1)) * b ^ (c_space + 1) := by
    refine Nat.mul_le_mul_right _ (le_trans hcw2 (Nat.pow_le_pow_left hb2 _))
  have h5 : b ^ (cw - (c_space + 1)) * b ^ (c_space + 1) = b ^ cw := by
    rw [← pow_add, Nat.sub_add_cancel hcw1]
  omega

section MGraphBridge

/-! ## Bridging `CitedSparsifyProp` back to `DynSpanner.SparsifySpec` -/

private lemma isWalk_mem_verts_lt {H : Cited.Graph} (hH : H.IsValid) {u v : ℕ} {P : Walk}
    (hP : Walk.IsWalk H u v P) : ∀ x ∈ P.verts, x < H.n := by
  rcases hP with ⟨_, _, ⟨hPv, _⟩ | ⟨hne, hlen, _, _, hedges, hmatch⟩⟩
  · intro x hx; simp [hPv] at hx
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have hi_e : i < P.edges.length ∨ ∃ j, j + 1 = i ∧ j < P.edges.length := by
      cases i with
      | zero =>
        left; exact Nat.pos_of_ne_zero (by intro h0; exact hne (List.length_eq_zero_iff.mp h0))
      | succ j =>
        right; refine ⟨j, rfl, ?_⟩; omega
    rcases hi_e with hi_lt | ⟨j, rfl, hj_lt⟩
    · have hm := hmatch i hi_lt
      have he_lt : P.edges.getD i 0 < H.m := hedges _ (List.getD_eq_getElem P.edges 0 hi_lt ▸ List.getElem_mem hi_lt)
      have he_mem : H.edges.getD (P.edges.getD i 0) (0, 0) ∈ H.edges := by
        rw [List.getD_eq_getElem _ (0, 0) he_lt]
        exact List.getElem_mem he_lt
      have hvalid := hH _ he_mem
      have hvp : P.verts.getD i 0 = P.verts[i]'hi := List.getD_eq_getElem _ 0 hi
      rw [hvp] at hm
      rcases hm with ⟨h1, _⟩ | ⟨h2, _⟩
      · exact h1 ▸ hvalid.1
      · exact h2 ▸ hvalid.2
    · have hm := hmatch j hj_lt
      have he_lt : P.edges.getD j 0 < H.m := hedges _ (List.getD_eq_getElem P.edges 0 hj_lt ▸ List.getElem_mem hj_lt)
      have he_mem : H.edges.getD (P.edges.getD j 0) (0, 0) ∈ H.edges := by
        rw [List.getD_eq_getElem _ (0, 0) he_lt]
        exact List.getElem_mem he_lt
      have hvalid := hH _ he_mem
      have hvp : P.verts.getD (j + 1) 0 = P.verts[j + 1]'hi := List.getD_eq_getElem _ 0 hi
      rw [hvp] at hm
      rcases hm with ⟨_, h2⟩ | ⟨_, h1⟩
      · exact h2 ▸ hvalid.2
      · exact h1 ▸ hvalid.1

/-- `CitedSparsifyProp` plus guest `w` bounds yields all Word-RAM encoding bounds needed by
`gtReverseDynContract`. -/
theorem revDyn_bounds_of_citedSparsifyProp {w mMax : ℕ} {γ_c γ_ℓ K_s : ℝ} {p_s : ℕ}
    {mem : ℕ → ℕ} {guestBase spOutG retHeap : ℕ}
    {H' J : Cited.Graph} {embJH : ℕ → Walk}
    {cJtilde : Cited.Graph} {kept : List ℕ} {embJJtilde : ℕ → Walk}
    (hProp : CitedSparsifyProp mMax γ_c γ_ℓ K_s p_s H' J embJH cJtilde kept embJJtilde)
    (hSpOut : SparsifyOutRelocAt mem guestBase spOutG retHeap J.m cJtilde kept embJJtilde)
    (_hJ : J.IsValid) (hJn_w : J.n < 2 ^ w) (hJm_w : J.m < 2 ^ w) (hret_w : retHeap < 2 ^ w) :
    cJtilde.encode.all (· < 2 ^ w) ∧
    (∀ i < cJtilde.m, (cJtilde.edges[i]!).1 < 2 ^ w ∧ (cJtilde.edges[i]!).2 < 2 ^ w) ∧
    cJtilde.m = kept.length ∧
    ∀ j < J.m,
      (embJJtilde j).verts.length < 2 ^ w ∧
      (embJJtilde j).edges.length < 2 ^ w ∧
      (∀ c ∈ (embJJtilde j).edges, c < cJtilde.m ∧ c < kept.length) ∧
      (∀ u ∈ (embJJtilde j).verts, u < 2 ^ w) := by
  rcases hProp with ⟨hnodup, hkept, hcJn, hcJed, hcJvalid, hembJJ, _⟩
  have hcJm : cJtilde.m = kept.length := by
    simp [Cited.Graph.m, hcJed]
  have hcJ_w : ∀ i < cJtilde.m, (cJtilde.edges[i]!).1 < 2 ^ w ∧ (cJtilde.edges[i]!).2 < 2 ^ w := by
    intro i hi
    rw [getElem!_pos cJtilde.edges i hi]
    have hv := hcJvalid _ (List.getElem_mem hi)
    omega
  have hcJall : cJtilde.encode.all (· < 2 ^ w) = true := by
    rw [List.all_eq_true]
    intro x hx
    rw [decide_eq_true_eq]
    simp only [Cited.Graph.encode, List.mem_cons, List.mem_flatMap] at hx
    rcases hx with rfl | rfl | ⟨e, he, hxe⟩
    · simpa [hcJn] using hJn_w
    · have hkept_le : kept.length ≤ J.m := by
        calc kept.length = kept.toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
          _ ≤ (Finset.range J.m).card := Finset.card_le_card fun k hk =>
            Finset.mem_range.mpr (hkept k (List.mem_toFinset.mp hk))
          _ = J.m := Finset.card_range J.m
      rw [hcJm]; omega
    · have hve := hcJvalid e he
      rw [hcJn] at hve
      simp only [List.not_mem_nil, or_false] at hxe
      rcases hxe with rfl | rfl <;> omega
  refine ⟨hcJall, hcJ_w, hcJm, fun j hj => ?_⟩
  have hw := hembJJ.2 j hj
  have hEnc := (hSpOut.2.2.2.2.2.2 j hj).1
  have hLenEnc : (embJJtilde j).encode.length =
      (embJJtilde j).verts.length + (embJJtilde j).edges.length + 2 := by
    simp [Walk.encode]; omega
  refine ⟨by omega, by omega, fun c hc => ?_, fun u hu => ?_⟩
  · have hc_lt : c < cJtilde.m := by
      rcases hw with ⟨_, _, ⟨_, hPe, _⟩ | ⟨_, _, _, _, hedges, _⟩⟩
      · simp [hPe] at hc
      · exact hedges c hc
    exact ⟨hc_lt, hcJm ▸ hc_lt⟩
  · have hu_lt : u < cJtilde.n := isWalk_mem_verts_lt hcJvalid hw u hu
    rw [hcJn] at hu_lt
    omega

private lemma mgraph_vcong_nonneg (J H' : MGraph) (emb : MinCostFlow.Embedding) :
    0 ≤ emb.vcong J H' (fun _ => 1) := by
  unfold MinCostFlow.Embedding.vcong MinCostFlow.Embedding.vcongAt
  split_ifs with hne
  · obtain ⟨v, hv⟩ := hne
    exact le_trans (Finset.sum_nonneg fun _ _ => zero_le_one)
      (Finset.le_sup' (fun x => ∑ e ∈ J.E with x ∈ H'.walkVertices (J.tail e) (emb e), (1 : ℝ)) hv)
  · exact le_rfl

private lemma mgraph_vcong_eq_zero_of_empty {J H' : MGraph} (emb : MinCostFlow.Embedding)
    (hE : J.E = ∅) :
    emb.vcong J H' (fun _ => 1) = 0 := by
  unfold MinCostFlow.Embedding.vcong MinCostFlow.Embedding.vcongAt
  split_ifs with hne
  · apply le_antisymm
    · refine Finset.sup'_le _ _ fun v _ => ?_
      simp [hE]
    · obtain ⟨v, hv⟩ := hne
      exact le_trans (Finset.sum_nonneg fun _ _ => zero_le_one)
        (Finset.le_sup' (fun x => ∑ e ∈ J.E with x ∈ H'.walkVertices (J.tail e) (emb e), (1 : ℝ)) hv)
  · rfl

/-- Lifts `CitedSparsifyProp` on `(toCitedH, toCitedJ, embToCited)` back to the `MGraph`
subgraph, embedding, congestion, length, and sparsity guarantees matching `DynSpanner.SparsifySpec`. -/
theorem mGraph_props_of_citedSparsifyProp {mMax : ℕ} {γ_c γ_ℓ K_s : ℝ} {p_s : ℕ}
    (hγ_c_nn : 0 ≤ γ_c)
    {H' J : MGraph} {embJH : MinCostFlow.Embedding}
    {cJtilde : Cited.Graph} {kept : List ℕ} {embJJtilde : ℕ → Walk}
    (hH' : H'.IsValid) (hJ : J.IsValid) (_hJm : J.m ≤ mMax)
    (hLen : J.E.Nonempty → 1 ≤ embJH.length J)
    (hembJH : embJH.IsEmbedding J H')
    (hProp : CitedSparsifyProp mMax γ_c γ_ℓ K_s p_s
      (toCitedH H' J embJH) (toCitedJ J) (embToCited H' J embJH) cJtilde kept embJJtilde) :
    let Jtilde := outJtilde J kept
    let outEmb := citedEmbToMGraph J cJtilde kept embJJtilde
    J.IsSubgraph Jtilde ∧
    outEmb.IsEmbedding J Jtilde ∧
    ((embJH.comp outEmb).vcong J H' (fun _ => 1) ≤
      (γ_c + 1) * (embJH.length J : ℝ) * (embJH.vcong J H' (fun _ => 1) + (J.maxDeg : ℝ))) ∧
    (((embJH.comp outEmb).length J : ℝ) ≤ γ_ℓ * (embJH.length J : ℝ)) ∧
    ((Jtilde.m : ℝ) ≤ K_s * (J.n : ℝ) * γ_ℓ * (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ p_s) := by
  rcases hProp with ⟨hnodup, hkept_cit, hcJn_cit, hcJed_cit, hcJvalid, hembJJ, hvcong, hlenJJ, hsp⟩
  have hkept : ∀ k ∈ kept, k < J.m := fun k hk => (toCitedJ_m J) ▸ hkept_cit k hk
  have hcJn : cJtilde.n = J.n := hcJn_cit.trans (by dsimp [toCitedJ]; exact vertsOf_length J.V)
  have hcJm : cJtilde.m = kept.length := by simp [Cited.Graph.m, hcJed_cit]
  have hsub := outJtilde_isSubgraph J kept hkept
  have hemb_mg := citedEmbToMGraph_isEmbedding hJ hkept hcJn hcJed_cit hembJJ
  refine ⟨hsub, hemb_mg, ?_, ?_, ?_⟩
  · by_cases hEne : J.E.Nonempty
    · have hlen1 : (1 : ℝ) ≤ (embJH.length J : ℝ) := by exact_mod_cast hLen hEne
      have hemb_cit := embToCited_isEmbedding hJ hembJH
      have hres := restrictEmb_isEmbedding_of_edges hemb_cit hkept_cit hcJn_cit hcJed_cit
      have hcomp := vcong_comp_mgraph_le hH' hJ hembJH hcJvalid hkept hcJn hcJed_cit hembJJ hres
      have hlen_eq : (Spanner.length (toCitedJ J) (embToCited H' J embJH) : ℝ) =
          (embJH.length J : ℝ) := by
        exact_mod_cast length_embToCited_eq H' J embJH
      have hvc_le := vcong_embToCited_le hH' hJ hembJH
      have hdeg_le : (Spanner.maxDeg (toCitedJ J) : ℝ) ≤ (J.maxDeg : ℝ) := by
        exact_mod_cast maxDeg_toCitedJ_le hJ
      have hlen_nn : 0 ≤ (embJH.length J : ℝ) := Nat.cast_nonneg _
      have hv_nn : 0 ≤ embJH.vcong J H' (fun _ => 1) := mgraph_vcong_nonneg J H' embJH
      have hdeg_nn : 0 ≤ (J.maxDeg : ℝ) := Nat.cast_nonneg _
      have hterm1 : (J.maxDeg : ℝ) ≤
          1 * (embJH.length J : ℝ) * (embJH.vcong J H' (fun _ => 1) + (J.maxDeg : ℝ)) := by
        nlinarith
      have hterm2 : γ_c * (Spanner.length (toCitedJ J) (embToCited H' J embJH) : ℝ) *
          (Spanner.vcong (toCitedJ J) (toCitedH H' J embJH) (fun _ => 1) (embToCited H' J embJH) +
            (Spanner.maxDeg (toCitedJ J) : ℝ)) ≤
          γ_c * (embJH.length J : ℝ) * (embJH.vcong J H' (fun _ => 1) + (J.maxDeg : ℝ)) := by
        rw [hlen_eq]
        refine mul_le_mul_of_nonneg_left (add_le_add hvc_le hdeg_le) ?_
        exact mul_nonneg hγ_c_nn hlen_nn
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty] at hEne
      rw [mgraph_vcong_eq_zero_of_empty _ hEne]
      exact mul_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _))
        (add_nonneg (mgraph_vcong_nonneg J H' embJH) (Nat.cast_nonneg _))
  · have hlen_mg : ((embJH.comp (citedEmbToMGraph J cJtilde kept embJJtilde)).length J : ℝ) ≤
        (Spanner.length (toCitedJ J) embJJtilde : ℝ) * (embJH.length J : ℝ) := by
      exact_mod_cast length_comp_mgraph_le hkept hemb_mg
    exact le_trans hlen_mg (mul_le_mul_of_nonneg_right hlenJJ (Nat.cast_nonneg _))
  · have hm_eq : ((outJtilde J kept).m : ℝ) = (cJtilde.m : ℝ) := by
      rw [outJtilde_m_eq J kept hnodup hkept, hcJm]
    have hcJn' : ((toCitedJ J).n : ℝ) = (J.n : ℝ) := by
      dsimp [toCitedJ]; rw [vertsOf_length]; rfl
    have hcJm' : ((toCitedJ J).m : ℝ) = (J.m : ℝ) := by exact_mod_cast toCitedJ_m J
    rw [hm_eq]
    simpa [hcJn', hcJm'] using hsp

end MGraphBridge

end

end MinCostFlow.DynSpanner.Program
