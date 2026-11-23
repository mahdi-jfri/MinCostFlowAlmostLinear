module

public import WordRAM.Layout
public import MinCostFlow.Spanner.Layouts
public import MinCostFlow.ExpanderDecomp.FakeEdges
public import MinCostFlow.Expander.GraphHelpers
public import MinCostFlow.Expander.PruningState

import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Relabeling Isomorphism and Memory Layouts for Expander-Decomposition Programs

Shared mathematical and memory-layout infrastructure for Word-RAM procedures over induced
subgraphs `G[X]` given as a duplicate-free list `verts : List ℕ` of original vertex IDs:

1. **Flat memory layouts** (`readList`, `readEdges`, `EdgesAt`) matching `WordRAM.ListAt` and
   `Spanner.GraphAt`.
2. **Vertex relabeling isomorphism** (`relabelEdges`, `relabelGraph`) mapping `X = verts.toFinset`
   to `Finset.range verts.length` using only `verts.Nodup` (no sorting required), preserving
   `inside`, `degIn`, `volIn`, `cutIn`, and `IsConductanceExpanderOn`.
3. **Subdivision indexing and `RemoveFake` integer parameters** (`subdiv_length`,
   `subdiv_getElem_even`, `subdiv_getElem_odd`, `range_union_midpoints`, `rfCcap`, `rfHParam`),
   connecting integer arithmetic on `rhoNum / rhoDen` to `PruneCfg.Valid`,
   `pruneExpander_wordram_spec`, and `removeFake_of_pruned`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Flat Memory Readers and Layouts -/

/-- Read `k` consecutive words starting at `addr`. -/
def readList (mem : ℕ → ℕ) (addr k : ℕ) : List ℕ :=
  (List.range k).map fun i => mem (addr + i)

/-- Read `m` consecutive edge pairs `(u, v)` stored as `2 * m` words starting at `addr`. -/
def readEdges (mem : ℕ → ℕ) (addr m : ℕ) : List (ℕ × ℕ) :=
  (List.range m).map fun j => (mem (addr + 2 * j), mem (addr + 2 * j + 1))

/-- Edge list `es` stored as `2 * es.length` consecutive words starting at `addr`. -/
def EdgesAt (mem : ℕ → ℕ) (addr : ℕ) (es : List (ℕ × ℕ)) : Prop :=
  ∀ j (hj : j < es.length),
    mem (addr + 2 * j) = (es[j]'hj).1 ∧ mem (addr + 2 * j + 1) = (es[j]'hj).2

/-- Relabel each edge endpoint `u` to its local index `verts.idxOf u`. -/
def relabelEdges (verts : List ℕ) (es : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  es.map fun e => (verts.idxOf e.1, verts.idxOf e.2)

/-- Graph on `0, …, verts.length - 1` obtained by relabeling `es` via `verts.idxOf`. -/
def relabelGraph (verts : List ℕ) (es : List (ℕ × ℕ)) : Graph :=
  ⟨verts.length, relabelEdges verts es⟩

/-- Integer pruning capacity `C_cap = ⌈12 · rhoDen / rhoNum⌉ + 2` for `ρ = rhoNum / rhoDen`. -/
def rfCcap (rhoNum rhoDen : ℕ) : ℕ :=
  (12 * rhoDen + rhoNum - 1) / rhoNum + 2

/-- Integer pruning height `H = 4 · C_cap · (⌊log₂(2 · mJ + 1)⌋ + 1) + 2` for `mJ = mH + 2 · mF`. -/
def rfHParam (mH mF rhoNum rhoDen : ℕ) : ℕ :=
  4 * rfCcap rhoNum rhoDen * (Nat.log 2 (2 * (mH + 2 * mF) + 1) + 1) + 2

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 2. Basic Layout Lemmas -/

lemma readList_length (mem : ℕ → ℕ) (addr k : ℕ) : (readList mem addr k).length = k := by
  simp [readList]

lemma readList_getElem (mem : ℕ → ℕ) (addr k i : ℕ) (hi : i < k) :
    (readList mem addr k)[i]'(by simp [readList, hi]) = mem (addr + i) := by
  simp [readList]

lemma listAt_readList (mem : ℕ → ℕ) (addr k : ℕ) :
    ListAt mem addr (readList mem addr k) := by
  intro i hi
  simp only [readList_length] at hi
  simp [readList]

lemma readList_eq_of_listAt {mem : ℕ → ℕ} {addr : ℕ} {xs : List ℕ} (h : ListAt mem addr xs) :
    readList mem addr xs.length = xs := by
  apply List.ext_getElem (by simp [readList])
  intro i hi _
  simp only [readList_length] at hi
  rw [readList_getElem mem addr xs.length i hi]
  exact h i hi

lemma readEdges_length (mem : ℕ → ℕ) (addr m : ℕ) : (readEdges mem addr m).length = m := by
  simp [readEdges]

lemma readEdges_getElem (mem : ℕ → ℕ) (addr m j : ℕ) (hj : j < m) :
    (readEdges mem addr m)[j]'(by simp [readEdges, hj]) =
      (mem (addr + 2 * j), mem (addr + 2 * j + 1)) := by
  simp [readEdges]

lemma edgesAt_readEdges (mem : ℕ → ℕ) (addr m : ℕ) :
    EdgesAt mem addr (readEdges mem addr m) := by
  intro j hj
  simp only [readEdges_length] at hj
  simp [readEdges]

lemma readEdges_eq_of_edgesAt {mem : ℕ → ℕ} {addr : ℕ} {es : List (ℕ × ℕ)}
    (h : EdgesAt mem addr es) :
    readEdges mem addr es.length = es := by
  apply List.ext_getElem (by simp [readEdges])
  intro j hj _
  simp only [readEdges_length] at hj
  rw [readEdges_getElem mem addr es.length j hj]
  have hpair := h j hj
  exact Prod.ext hpair.1 hpair.2

lemma graphAt_to_edgesAt {mem : ℕ → ℕ} {a : ℕ} {G : Graph} (h : GraphAt mem a G) :
    EdgesAt mem (a + 2) G.edges := by
  intro j hj
  have h1 := graphAt_edge_fst h hj
  have h2 := graphAt_edge_snd h hj
  refine ⟨h1, ?_⟩
  rw [show a + 2 + 2 * j + 1 = a + 3 + 2 * j by omega]
  exact h2

lemma EdgesAt.congr {mem mem' : ℕ → ℕ} {addr : ℕ} {es : List (ℕ × ℕ)}
    (h : EdgesAt mem addr es)
    (heq : ∀ k, addr ≤ k → k < addr + 2 * es.length → mem' k = mem k) :
    EdgesAt mem' addr es := by
  intro j hj
  rw [heq (addr + 2 * j) (by omega) (by omega),
    heq (addr + 2 * j + 1) (by omega) (by omega)]
  exact h j hj

lemma ListAt.congr {mem mem' : ℕ → ℕ} {addr : ℕ} {xs : List ℕ}
    (h : ListAt mem addr xs)
    (heq : ∀ k, addr ≤ k → k < addr + xs.length → mem' k = mem k) :
    ListAt mem' addr xs := by
  intro i hi
  rw [heq (addr + i) (by omega) (by omega)]
  exact h i hi

/-! ## 3. Bijection and Graph Isomorphism under `verts.Nodup` -/

lemma nodup_getD_idxOf {verts : List ℕ} {u : ℕ} (hu : u ∈ verts) :
    verts.getD (verts.idxOf u) 0 = u := by
  have hlt : verts.idxOf u < verts.length := List.idxOf_lt_length_of_mem hu
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
  exact List.getElem_idxOf hlt

lemma nodup_idxOf_getD {verts : List ℕ} (hnd : verts.Nodup) {i : ℕ} (hi : i < verts.length) :
    verts.idxOf (verts.getD i 0) = i := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  have hlt : verts.idxOf (verts[i]'hi) < verts.length :=
    List.idxOf_lt_length_of_mem (List.getElem_mem hi)
  exact (List.Nodup.getElem_inj_iff hnd).mp (List.getElem_idxOf hlt)

lemma nodup_getD_inj {verts : List ℕ} (hnd : verts.Nodup) {i j : ℕ}
    (hi : i < verts.length) (hj : j < verts.length)
    (heq : verts.getD i 0 = verts.getD j 0) : i = j := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
    Option.getD_some] at heq
  exact (List.Nodup.getElem_inj_iff hnd).mp heq

lemma image_range_getD (verts : List ℕ) :
    (Finset.range verts.length).image (fun i => verts.getD i 0) = verts.toFinset := by
  ext u
  simp only [Finset.mem_image, Finset.mem_range, List.mem_toFinset]
  constructor
  · rintro ⟨i, hi, rfl⟩
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact List.getElem_mem hi
  · intro hu
    exact ⟨verts.idxOf u, List.idxOf_lt_length_of_mem hu, nodup_getD_idxOf hu⟩

lemma image_sdiff_getD {verts : List ℕ} (hnd : verts.Nodup) {A B : Finset ℕ}
    (hA : A ⊆ Finset.range verts.length) (hB : B ⊆ Finset.range verts.length) :
    (A \ B).image (fun i => verts.getD i 0) =
      A.image (fun i => verts.getD i 0) \ B.image (fun i => verts.getD i 0) := by
  ext u
  simp only [Finset.mem_image, Finset.mem_sdiff]
  constructor
  · rintro ⟨i, ⟨hiA, hiB⟩, rfl⟩
    refine ⟨⟨i, hiA, rfl⟩, ?_⟩
    rintro ⟨j, hjB, hji⟩
    have hij := nodup_getD_inj hnd (Finset.mem_range.mp (hB hjB))
      (Finset.mem_range.mp (hA hiA)) hji
    exact hiB (hij ▸ hjB)
  · rintro ⟨⟨i, hiA, rfl⟩, hnotB⟩
    refine ⟨i, ⟨hiA, fun hiB => hnotB ⟨i, hiB, rfl⟩⟩, rfl⟩

lemma image_getD_subset_toFinset {verts : List ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.range verts.length) :
    S.image (fun i => verts.getD i 0) ⊆ verts.toFinset := by
  rw [← image_range_getD]
  exact Finset.image_subset_image hS

lemma idxOf_mem_iff_mem_image {verts : List ℕ} (hnd : verts.Nodup) {S : Finset ℕ}
    (hS : S ⊆ Finset.range verts.length) {u : ℕ} (hu : u ∈ verts) :
    verts.idxOf u ∈ S ↔ u ∈ S.image (fun i => verts.getD i 0) := by
  constructor
  · intro h
    exact Finset.mem_image.mpr ⟨verts.idxOf u, h, nodup_getD_idxOf hu⟩
  · intro h
    rcases Finset.mem_image.mp h with ⟨i, hi, hfi⟩
    have hi_lt : i < verts.length := Finset.mem_range.mp (hS hi)
    have hidx_lt : verts.idxOf u < verts.length := List.idxOf_lt_length_of_mem hu
    have heq : i = verts.idxOf u :=
      nodup_getD_inj hnd hi_lt hidx_lt (hfi.trans (nodup_getD_idxOf hu).symm)
    rwa [← heq]

lemma relabelGraph_m (verts : List ℕ) (es : List (ℕ × ℕ)) :
    (relabelGraph verts es).m = es.length := by
  simp [relabelGraph, relabelEdges, Graph.m]

lemma relabelGraph_isValid {verts : List ℕ} {es : List (ℕ × ℕ)}
    (hes : ∀ e ∈ es, e.1 ∈ verts.toFinset ∧ e.2 ∈ verts.toFinset) :
    (relabelGraph verts es).IsValid := by
  intro e he
  simp only [relabelGraph, relabelEdges, List.mem_map] at he
  rcases he with ⟨e₀, he₀, rfl⟩
  have h12 := hes e₀ he₀
  exact ⟨List.idxOf_lt_length_of_mem (List.mem_toFinset.mp h12.1),
    List.idxOf_lt_length_of_mem (List.mem_toFinset.mp h12.2)⟩

lemma relabelGraph_inside {n : ℕ} {verts : List ℕ} {es : List (ℕ × ℕ)}
    (hnd : verts.Nodup) (hes : ∀ e ∈ es, e.1 ∈ verts.toFinset ∧ e.2 ∈ verts.toFinset)
    {S : Finset ℕ} (hS : S ⊆ Finset.range verts.length) :
    (relabelGraph verts es).inside S =
      relabelEdges verts ((Graph.mk n es).inside (S.image fun i => verts.getD i 0)) := by
  simp only [relabelGraph, relabelEdges, Graph.inside, List.filter_map, Function.comp_def]
  congr 1
  apply List.filter_congr
  intro e he
  have h1 := List.mem_toFinset.mp (hes e he).1
  have h2 := List.mem_toFinset.mp (hes e he).2
  simp only [idxOf_mem_iff_mem_image hnd hS h1, idxOf_mem_iff_mem_image hnd hS h2]

lemma relabelGraph_degIn {n : ℕ} {verts : List ℕ} {es : List (ℕ × ℕ)}
    (hnd : verts.Nodup) (hes : ∀ e ∈ es, e.1 ∈ verts.toFinset ∧ e.2 ∈ verts.toFinset)
    {S : Finset ℕ} (hS : S ⊆ Finset.range verts.length) {i : ℕ} (hi : i < verts.length) :
    (relabelGraph verts es).degIn S i =
      (Graph.mk n es).degIn (S.image fun j => verts.getD j 0) (verts.getD i 0) := by
  unfold Graph.degIn
  rw [relabelGraph_inside (n := n) hnd hes hS]
  simp only [relabelEdges, List.filter_map, List.length_map, Function.comp_def]
  have hf1 :
      (((Graph.mk n es).inside (S.image fun j => verts.getD j 0)).filter
        fun e => decide (verts.idxOf e.1 = i)).length =
      (((Graph.mk n es).inside (S.image fun j => verts.getD j 0)).filter
        fun e => decide (e.1 = verts.getD i 0)).length := by
    congr 1
    apply List.filter_congr
    intro e he
    have he' := (mem_inside_iff.mp he).1
    have h1 := List.mem_toFinset.mp (hes e he').1
    have hiff : verts.idxOf e.1 = i ↔ e.1 = verts.getD i 0 := by
      constructor
      · intro h; rw [← h]; exact (nodup_getD_idxOf h1).symm
      · intro h; rw [h]; exact nodup_idxOf_getD hnd hi
    simp [hiff]
  have hf2 :
      (((Graph.mk n es).inside (S.image fun j => verts.getD j 0)).filter
        fun e => decide (verts.idxOf e.2 = i)).length =
      (((Graph.mk n es).inside (S.image fun j => verts.getD j 0)).filter
        fun e => decide (e.2 = verts.getD i 0)).length := by
    congr 1
    apply List.filter_congr
    intro e he
    have he' := (mem_inside_iff.mp he).1
    have h2 := List.mem_toFinset.mp (hes e he').2
    have hiff : verts.idxOf e.2 = i ↔ e.2 = verts.getD i 0 := by
      constructor
      · intro h; rw [← h]; exact (nodup_getD_idxOf h2).symm
      · intro h; rw [h]; exact nodup_idxOf_getD hnd hi
    simp [hiff]
  exact congrArg₂ (· + ·) hf1 hf2

lemma relabelGraph_volIn {n : ℕ} {verts : List ℕ} {es : List (ℕ × ℕ)}
    (hnd : verts.Nodup) (hes : ∀ e ∈ es, e.1 ∈ verts.toFinset ∧ e.2 ∈ verts.toFinset)
    {A S : Finset ℕ} (hA : A ⊆ Finset.range verts.length) (hSA : S ⊆ A) :
    (relabelGraph verts es).volIn A S =
      (Graph.mk n es).volIn (A.image fun i => verts.getD i 0) (S.image fun i => verts.getD i 0) := by
  have hS : S ⊆ Finset.range verts.length := hSA.trans hA
  have hinj : Set.InjOn (fun i => verts.getD i 0) (S : Set ℕ) := fun i hi j hj hij =>
    nodup_getD_inj hnd (Finset.mem_range.mp (hS hi)) (Finset.mem_range.mp (hS hj)) hij
  unfold Graph.volIn
  rw [Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun i hi => ?_
  exact relabelGraph_degIn hnd hes hA (Finset.mem_range.mp (hS hi))

lemma relabelGraph_cutIn {n : ℕ} {verts : List ℕ} {es : List (ℕ × ℕ)}
    (hnd : verts.Nodup) (hes : ∀ e ∈ es, e.1 ∈ verts.toFinset ∧ e.2 ∈ verts.toFinset)
    {A S : Finset ℕ} (hA : A ⊆ Finset.range verts.length) (hSA : S ⊆ A) :
    (relabelGraph verts es).cutIn A S =
      (Graph.mk n es).cutIn (A.image fun i => verts.getD i 0) (S.image fun i => verts.getD i 0) := by
  have hS : S ⊆ Finset.range verts.length := hSA.trans hA
  unfold Graph.cutIn
  rw [relabelGraph_inside (n := n) hnd hes hA]
  simp only [relabelEdges, List.filter_map, List.length_map, Function.comp_def]
  congr 1
  apply List.filter_congr
  intro e he
  have he' := (mem_inside_iff.mp he).1
  have h1 := List.mem_toFinset.mp (hes e he').1
  have h2 := List.mem_toFinset.mp (hes e he').2
  simp only [idxOf_mem_iff_mem_image hnd hS h1, idxOf_mem_iff_mem_image hnd hS h2]

/-- Conductance on `A` in `relabelGraph verts es` is equivalent to conductance on `A.image f` in
`Graph.mk n es`. -/
theorem relabelGraph_isConductanceExpanderOn_iff {n : ℕ} {verts : List ℕ} {es : List (ℕ × ℕ)}
    (hnd : verts.Nodup) (hes : ∀ e ∈ es, e.1 ∈ verts.toFinset ∧ e.2 ∈ verts.toFinset)
    {A : Finset ℕ} (hA : A ⊆ Finset.range verts.length) {φ : ℝ} :
    (relabelGraph verts es).IsConductanceExpanderOn A φ ↔
      (Graph.mk n es).IsConductanceExpanderOn (A.image fun i => verts.getD i 0) φ := by
  let f : ℕ → ℕ := fun i => verts.getD i 0
  have hinjA : Set.InjOn f (A : Set ℕ) := fun i hi j hj hij =>
    nodup_getD_inj hnd (Finset.mem_range.mp (hA hi)) (Finset.mem_range.mp (hA hj)) hij
  constructor
  · intro hexp S hS hSne hSneA
    let S_loc : Finset ℕ := A.filter fun i => f i ∈ S
    have hSloc_sub : S_loc ⊆ A := Finset.filter_subset _ _
    have hS_eq : S_loc.image f = S := by
      ext u
      simp only [S_loc, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨i, ⟨_, hfi⟩, rfl⟩; exact hfi
      · intro hu
        rcases Finset.mem_image.mp (hS hu) with ⟨i, hiA, rfl⟩
        exact ⟨i, ⟨hiA, hu⟩, rfl⟩
    have hSloc_ne : S_loc.Nonempty := by
      rcases hSne with ⟨u, hu⟩
      rw [← hS_eq] at hu
      rcases Finset.mem_image.mp hu with ⟨i, hi, _⟩
      exact ⟨i, hi⟩
    have hSloc_neA : S_loc ≠ A := by
      intro heq
      apply hSneA
      rw [← hS_eq, heq]
    have h := hexp S_loc hSloc_sub hSloc_ne hSloc_neA
    rw [relabelGraph_volIn (n := n) hnd hes hA hSloc_sub,
      relabelGraph_volIn (n := n) hnd hes hA Finset.sdiff_subset,
      relabelGraph_cutIn (n := n) hnd hes hA hSloc_sub,
      image_sdiff_getD hnd hA (hSloc_sub.trans hA), hS_eq] at h
    exact h
  · intro hexp S_loc hSA hSne hSneA
    have hS_sub : S_loc.image f ⊆ A.image f := Finset.image_subset_image hSA
    have hS_ne : (S_loc.image f).Nonempty := hSne.image f
    have hS_neA : S_loc.image f ≠ A.image f := by
      intro heq
      apply hSneA
      ext i
      constructor
      · exact fun hi => hSA hi
      · intro hiA
        have hmem : f i ∈ S_loc.image f := heq ▸ Finset.mem_image_of_mem f hiA
        rcases Finset.mem_image.mp hmem with ⟨j, hj, hji⟩
        have hEq : j = i := hinjA (hSA hj) hiA hji
        rwa [← hEq]
    have h := hexp (S_loc.image f) hS_sub hS_ne hS_neA
    rw [relabelGraph_volIn (n := n) hnd hes hA hSA,
      relabelGraph_volIn (n := n) hnd hes hA Finset.sdiff_subset,
      relabelGraph_cutIn (n := n) hnd hes hA hSA,
      image_sdiff_getD hnd hA (hSA.trans hA)]
    exact h

/-- `Graph.mk n (G.inside X)` agrees with `G` on every subset `S ⊆ X`. -/
lemma inside_mk_inside_eq {G : Graph} {X S : Finset ℕ} (hSX : S ⊆ X) :
    (Graph.mk G.n (G.inside X)).inside S = G.inside S := by
  simp only [Graph.inside, List.filter_filter]
  apply List.filter_congr
  intro e _
  by_cases h1 : e.1 ∈ S <;> by_cases h2 : e.2 ∈ S
  · simp [h1, h2, hSX h1, hSX h2]
  · simp [h1, h2]
  · simp [h1, h2]
  · simp [h1, h2]

lemma degIn_mk_inside_eq {G : Graph} {X S : Finset ℕ} (hSX : S ⊆ X) (v : ℕ) :
    (Graph.mk G.n (G.inside X)).degIn S v = G.degIn S v := by
  simp only [Graph.degIn, inside_mk_inside_eq hSX]

lemma volIn_mk_inside_eq {G : Graph} {X A S : Finset ℕ} (hAX : A ⊆ X) :
    (Graph.mk G.n (G.inside X)).volIn A S = G.volIn A S := by
  unfold Graph.volIn
  exact Finset.sum_congr rfl fun v _ => degIn_mk_inside_eq hAX v

lemma cutIn_mk_inside_eq {G : Graph} {X A S : Finset ℕ} (hAX : A ⊆ X) :
    (Graph.mk G.n (G.inside X)).cutIn A S = G.cutIn A S := by
  simp only [Graph.cutIn, inside_mk_inside_eq hAX]

/-! ## 4. Subdivision Indexing and `RemoveFake` Parameter Arithmetic -/

lemma subdiv_length (m : ℕ) (F : List (ℕ × ℕ)) :
    (subdiv m F).length = 2 * F.length := by
  induction F generalizing m with
  | nil => simp [subdiv]
  | cons e F ih =>
    simp only [subdiv, List.length_cons, ih]
    omega

lemma subdiv_getElem_even (m : ℕ) (F : List (ℕ × ℕ)) (j : ℕ) (hj : j < F.length) :
    (subdiv m F)[2 * j]'(by rw [subdiv_length]; omega) = ((F[j]'hj).1, m + j) := by
  induction F generalizing m j with
  | nil => simp at hj
  | cons e F ih =>
    cases j with
    | zero => simp [subdiv]
    | succ j =>
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at hj
      have h := ih (m + 1) j hj
      simp only [subdiv, show 2 * (j + 1) = 2 * j + 2 by omega, List.getElem_cons_succ]
      simpa [show m + 1 + j = m + (j + 1) by omega] using h

lemma subdiv_getElem_odd (m : ℕ) (F : List (ℕ × ℕ)) (j : ℕ) (hj : j < F.length) :
    (subdiv m F)[2 * j + 1]'(by rw [subdiv_length]; omega) = (m + j, (F[j]'hj).2) := by
  induction F generalizing m j with
  | nil => simp at hj
  | cons e F ih =>
    cases j with
    | zero => simp [subdiv]
    | succ j =>
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at hj
      have h := ih (m + 1) j hj
      simp only [subdiv, show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by omega, List.getElem_cons_succ]
      simpa [show m + 1 + j = m + (j + 1) by omega] using h

lemma range_union_midpoints (k : ℕ) (F : List (ℕ × ℕ)) :
    Finset.range k ∪ midpoints k F = Finset.range (k + F.length) := by
  ext u
  simp only [midpoints, Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
  omega

private lemma ceil_div_nat_eq (a b : ℕ) (hb : 1 ≤ b) :
    Nat.ceil ((a : ℝ) / (b : ℝ)) = (a + b - 1) / b := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  by_cases ha0 : a = 0
  · subst ha0
    have hdiv0 : (b - 1) / b = 0 := Nat.div_eq_of_lt (by omega)
    simp [hdiv0]
  · have hpos : 0 < (a + b - 1) / b := Nat.div_pos (by omega) (by omega)
    rw [Nat.ceil_eq_iff (by omega : (a + b - 1) / b ≠ 0)]
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ hbR]
      have hnat : ((a + b - 1) / b - 1) * b < a := by
        have hsub : ((a + b - 1) / b - 1) * b + b = (a + b - 1) / b * b := by
          calc ((a + b - 1) / b - 1) * b + b
              = ((a + b - 1) / b - 1 + 1) * b := by ring
            _ = (a + b - 1) / b * b := by rw [Nat.sub_add_cancel hpos]
        have hle : (a + b - 1) / b * b ≤ a + b - 1 := Nat.div_mul_le_self _ _
        omega
      exact_mod_cast hnat
    · rw [div_le_iff₀ hbR]
      have h1 : a ≤ ((a + b - 1) / b) * b := by
        have hmod : (a + b - 1) / b * b + (a + b - 1) % b = a + b - 1 := by
          rw [mul_comm]; exact Nat.div_add_mod (a + b - 1) b
        have hltb : (a + b - 1) % b ≤ b - 1 := Nat.le_pred_of_lt (Nat.mod_lt _ (by omega))
        omega
      exact_mod_cast h1

lemma rfCcap_ge_fourteen {rhoNum rhoDen : ℕ} (h1 : 1 ≤ rhoNum) (h2 : rhoNum ≤ rhoDen) :
    14 ≤ rfCcap rhoNum rhoDen := by
  unfold rfCcap
  have h12 : 12 ≤ (12 * rhoDen + rhoNum - 1) / rhoNum := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    omega
  omega

lemma rfCcap_eq_max_ceil {rhoNum rhoDen : ℕ} (h1 : 1 ≤ rhoNum) (h2 : rhoNum ≤ rhoDen) :
    rfCcap rhoNum rhoDen =
      max 7 (Nat.ceil (4 / (((rhoNum : ℝ) / (rhoDen : ℝ)) / 3)) + 2) := by
  have hge14 := rfCcap_ge_fourteen h1 h2
  have hnum_pos : (0 : ℝ) < rhoNum := by exact_mod_cast h1
  have hden_pos : (0 : ℝ) < rhoDen := by exact_mod_cast (le_trans h1 h2)
  have hdiv : (4 : ℝ) / (((rhoNum : ℝ) / (rhoDen : ℝ)) / 3) = ((12 * rhoDen : ℕ) : ℝ) / (rhoNum : ℝ) := by
    push_cast
    field_simp
    ring
  rw [hdiv, ceil_div_nat_eq (12 * rhoDen) rhoNum h1]
  have hle : 7 ≤ (12 * rhoDen + rhoNum - 1) / rhoNum + 2 := by
    unfold rfCcap at hge14; omega
  rw [max_eq_right hle]
  rfl

lemma rfCcap_phi_bound {rhoNum rhoDen : ℕ} (h1 : 1 ≤ rhoNum) (h2 : rhoNum ≤ rhoDen) :
    4 ≤ (((rhoNum : ℝ) / (rhoDen : ℝ)) / 3) * ((rfCcap rhoNum rhoDen : ℝ) - 1) := by
  have hnum_pos : (0 : ℝ) < rhoNum := by exact_mod_cast h1
  have hden_pos : (0 : ℝ) < rhoDen := by exact_mod_cast (le_trans h1 h2)
  have hφ_pos : (0 : ℝ) < ((rhoNum : ℝ) / (rhoDen : ℝ)) / 3 := by positivity
  rw [rfCcap_eq_max_ceil h1 h2]
  have hceil : 4 / (((rhoNum : ℝ) / (rhoDen : ℝ)) / 3) ≤
      (Nat.ceil (4 / (((rhoNum : ℝ) / (rhoDen : ℝ)) / 3)) : ℝ) := Nat.le_ceil _
  have hmax : (Nat.ceil (4 / (((rhoNum : ℝ) / (rhoDen : ℝ)) / 3)) + 2 : ℕ) ≤
      max 7 (Nat.ceil (4 / (((rhoNum : ℝ) / (rhoDen : ℝ)) / 3)) + 2) := le_max_right _ _
  have hmaxR : (Nat.ceil (4 / (((rhoNum : ℝ) / (rhoDen : ℝ)) / 3)) : ℝ) + 2 ≤
      (max 7 (Nat.ceil (4 / (((rhoNum : ℝ) / (rhoDen : ℝ)) / 3)) + 2) : ℕ) := by
    exact_mod_cast hmax
  have hsub : 4 / (((rhoNum : ℝ) / (rhoDen : ℝ)) / 3) ≤
      ((max 7 (Nat.ceil (4 / (((rhoNum : ℝ) / (rhoDen : ℝ)) / 3)) + 2) : ℕ) : ℝ) - 1 := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hsub hφ_pos.le
  rw [mul_div_cancel₀ _ hφ_pos.ne'] at hmul
  exact hmul

lemma rfCcap_le_fifteen_div_rho {rhoNum rhoDen : ℕ} (h1 : 1 ≤ rhoNum) (h2 : rhoNum ≤ rhoDen) :
    (rfCcap rhoNum rhoDen : ℝ) ≤ 15 / ((rhoNum : ℝ) / (rhoDen : ℝ)) := by
  have hρ0 : (0 : ℝ) < (rhoNum : ℝ) / (rhoDen : ℝ) := by
    have : (0 : ℝ) < rhoNum := by exact_mod_cast h1
    have : (0 : ℝ) < rhoDen := by exact_mod_cast (le_trans h1 h2)
    positivity
  have hρ1 : (rhoNum : ℝ) / (rhoDen : ℝ) ≤ 1 := by
    have hden_pos : (0 : ℝ) < rhoDen := by exact_mod_cast (le_trans h1 h2)
    rw [div_le_one hden_pos]
    exact_mod_cast h2
  rw [rfCcap_eq_max_ceil h1 h2]
  exact cap_le hρ0 hρ1

lemma rf_pruneCfg_valid {k : ℕ} {H_loc F_loc : List (ℕ × ℕ)} {rhoNum rhoDen : ℕ}
    (h1 : 1 ≤ rhoNum) (h2 : rhoNum ≤ rhoDen)
    (hH : ∀ e ∈ H_loc, e.1 < k ∧ e.2 < k)
    (hF : ∀ e ∈ F_loc, e.1 ∈ Finset.range k ∧ e.2 ∈ Finset.range k)
    (hdeg : ∀ v ∈ Finset.range k, 1 ≤ (Graph.mk k (H_loc ++ F_loc)).degIn (Finset.range k) v) :
    let J := subdivGraph k H_loc F_loc
    let cfg : PruneCfg :=
      { G := J
        X := Finset.range J.n
        B := midpoints k F_loc
        C_cap := rfCcap rhoNum rhoDen
        H := rfHParam H_loc.length F_loc.length rhoNum rhoDen
        θ_out_nat := 1 }
    cfg.Valid ∧
      (∀ x ∈ cfg.X, x ∉ cfg.B → ∀ d < cfg.θ_out_nat, 3 * d ≤ cfg.degX x) := by
  intro J cfg
  have hJval : J.IsValid := subdivGraph_isValid (Finset.Subset.refl _) hH hF
  have hXeq : cfg.X = Finset.range k ∪ midpoints k F_loc := (range_union_midpoints k F_loc).symm
  have hBX : cfg.B ⊆ cfg.X := hXeq ▸ Finset.subset_union_right
  have hC14 := rfCcap_ge_fourteen h1 h2
  have hedg_len : cfg.edges.length = H_loc.length + 2 * F_loc.length := by
    change (J.inside J.verts).length = _
    rw [inside_verts_of_isValid hJval]
    simp [J, subdivGraph, subdiv_length]
  refine ⟨⟨hJval, hBX, by dsimp only [cfg]; omega, ?_, ?_⟩, ?_⟩
  · change 4 * rfCcap rhoNum rhoDen * (Nat.log 2 (2 * cfg.edges.length + 1) + 1) + 2 ≤
      rfHParam H_loc.length F_loc.length rhoNum rhoDen
    rw [hedg_len]
    exact le_rfl
  · intro v hv hvB
    have hv_lt : v < k := by
      rw [hXeq, Finset.mem_union] at hv
      rcases hv with hv' | hv'
      · exact Finset.mem_range.mp hv'
      · exact absurd hv' hvB
    have h1v := hdeg v (Finset.mem_range.mpr hv_lt)
    have h2v := degIn_le_subdiv (Finset.Subset.refl _) hH hF (Finset.mem_range.mpr hv_lt)
    change 1 ≤ J.degIn cfg.X v
    rw [hXeq]
    exact h1v.trans h2v
  · intro x _ _ d hd
    dsimp only [cfg] at hd
    have hd0 : d = 0 := by omega
    subst hd0
    simp

end MinCostFlow.ExpanderDecomp
