module

public import MinCostFlow.SparseCore.Program.RestartIface

/-!
# Exported bundle graphs and the spanner initialization (`RestartExport`)

The bundle piece writes each new bundle graph as a descriptor (`ExportAt`). This file shows that
the spanner initialization of `bucketSpannerDS` reads from it exactly `normGraph` of that graph
(`graphOfLists_eq_normGraph`), and that the precondition of operation `0` holds when the graph
meets `SpanGraphOK` and the heap lies above the lists (`bucketActivatePre_of_exportAt`). It also
gives the cost and the space of operation `0` in the form `spanActivateCost`,
`spanActivateSpace`, and shows that `normGraph` depends only on the vertices, the edges and their
ends (`normGraph_of_bunAgree`).
-/

namespace MinCostFlow.SparseCore.Program.Restart

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

public section

/-! ## `normGraph` -/

theorem normGraph_V (G : MGraph) : (normGraph G).V = G.V := rfl

theorem normGraph_E (G : MGraph) : (normGraph G).E = G.E := rfl

theorem normGraph_n (G : MGraph) : (normGraph G).n = G.n := rfl

theorem normGraph_m (G : MGraph) : (normGraph G).m = G.m := rfl

/-- Graphs with the same vertices, edges and ends of edges have the same `normGraph`. -/
theorem normGraph_congr {G G' : MGraph} (h : GraphEq G G') : normGraph G = normGraph G' := by
  obtain ⟨hV, hE, hte⟩ := h
  unfold normGraph
  congr 1
  · funext e
    by_cases he : e ∈ G.E
    · have he' : e ∈ G'.E := hE ▸ he
      simp only [he, he', ↓reduceIte, (hte e he).1]
    · have he' : e ∉ G'.E := hE ▸ he
      simp only [he, he', ↓reduceIte]
  · funext e
    by_cases he : e ∈ G.E
    · have he' : e ∈ G'.E := hE ▸ he
      simp only [he, he', ↓reduceIte, (hte e he).2]
    · have he' : e ∉ G'.E := hE ▸ he
      simp only [he, he', ↓reduceIte]

/-- Bundle states that agree on what a program sees have graphs that agree on their edges. -/
theorem graphEq_of_bunAgree {B B' : BundleState} (h : BunAgree B B') : GraphEq B.graph B'.graph :=
  ⟨h.1, h.2.1, fun e he => ⟨h.2.2.2 (e, true) he, h.2.2.2 (e, false) he⟩⟩

/-- Bundle states that agree on what a program sees give the same `normGraph`. -/
theorem normGraph_of_bunAgree {B B' : BundleState} (h : BunAgree B B') :
    normGraph B.graph = normGraph B'.graph :=
  normGraph_congr (graphEq_of_bunAgree h)

/-- `normGraph` keeps validity. -/
theorem normGraph_isValid {G : MGraph} (hG : G.IsValid) : (normGraph G).IsValid := by
  intro e he
  have he' : e ∈ G.E := he
  simp only [normGraph, he', ↓reduceIte]
  exact hG e he'

/-! ## Reading the exported lists -/

theorem readList_length (mem : ℕ → ℕ) (a n : ℕ) : (readList mem a n).length = n := by
  simp [readList]

theorem readTriples_length (mem : ℕ → ℕ) (a n : ℕ) : (readTriples mem a n).length = n := by
  simp [readTriples]

private theorem find?_of_unique {eT : List (ℕ × ℕ × ℕ)} (hnd : (eT.map Prod.fst).Nodup)
    {t : ℕ × ℕ × ℕ} (ht : t ∈ eT) : eT.find? (fun t' => t'.1 = t.1) = some t := by
  induction eT with
  | nil => simp at ht
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp ht with rfl | ht'
    · simp
    · have hne : a.1 ≠ t.1 := fun h => hnd.1 ⟨t, ht', h.symm⟩
      rw [List.find?_cons_of_neg (by simpa using hne)]
      exact ih hnd.2 ht'

private theorem find?_none_of_not_mem {eT : List (ℕ × ℕ × ℕ)} {e : ℕ}
    (h : ∀ t ∈ eT, t.1 ≠ e) : eT.find? (fun t' => t'.1 = e) = none := by
  rw [List.find?_eq_none]
  intro t ht
  simpa using h t ht

/-- A vertex list and an edge list that list the vertices, and each edge once with its ends, read
as `normGraph G`. -/
theorem graphOfLists_eq_normGraph {G : MGraph} {vL : List ℕ} {eT : List (ℕ × ℕ × ℕ)}
    (hV : ∀ v, v ∈ vL ↔ v ∈ G.V) (hnd : (eT.map Prod.fst).Nodup)
    (hT : ∀ t ∈ eT, t.1 ∈ G.E ∧ t.2.1 = G.tail t.1 ∧ t.2.2 = G.head t.1)
    (hcov : ∀ e ∈ G.E, ∃ t ∈ eT, t.1 = e) : graphOfLists vL eT = normGraph G := by
  have hE : (eT.map Prod.fst).toFinset = G.E := by
    ext e
    simp only [List.mem_toFinset, List.mem_map]
    exact ⟨fun ⟨t, ht, he⟩ => he ▸ (hT t ht).1, fun he => hcov e he⟩
  unfold graphOfLists normGraph
  congr 1
  · ext v; simp [hV]
  · funext e
    by_cases he : e ∈ G.E
    · obtain ⟨t, ht, rfl⟩ := hcov _ he
      rw [find?_of_unique hnd ht]
      simp only [he, ↓reduceIte, Option.map_some, Option.getD_some]
      exact (hT t ht).2.1
    · rw [find?_none_of_not_mem (fun t ht h => he (by rw [← h]; exact (hT t ht).1))]
      simp [he]
  · funext e
    by_cases he : e ∈ G.E
    · obtain ⟨t, ht, rfl⟩ := hcov _ he
      rw [find?_of_unique hnd ht]
      simp only [he, ↓reduceIte, Option.map_some, Option.getD_some]
      exact (hT t ht).2.2
    · rw [find?_none_of_not_mem (fun t ht h => he (by rw [← h]; exact (hT t ht).1))]
      simp [he]

/-- The graph that the spanner initialization reads from a descriptor is `normGraph` of the
exported graph. -/
theorem initArgsGraph_of_exportAt {mem : ℕ → ℕ} {d hEnd : ℕ} {G : MGraph}
    (hx : ExportAt mem d hEnd G) (tbl slot L splitB vCap eCap hp : ℕ) :
    initArgsGraph (bucketActInitArgs [tbl, slot, L, splitB, vCap, eCap, mem d, mem (d + 1),
      mem (d + 2), mem (d + 3), hp]) mem = normGraph G := by
  obtain ⟨-, -, -, hV, hnd, hT, hcov, -⟩ := hx
  exact graphOfLists_eq_normGraph hV hnd hT hcov

/-- The arguments of operation `0` on descriptor `d`. -/
@[expose] def activateArgs (P : DSParams) (mem : ℕ → ℕ) (tbl slot d hp : ℕ) : List ℕ :=
  [tbl, slot, P.L, P.splitBound, P.vCap, P.eCap, mem d, mem (d + 1), mem (d + 2), mem (d + 3), hp]

/-- **The precondition of operation `0` from a descriptor.** If descriptor `d` exports `G`, the
graph `normGraph G` meets `SpanGraphOK`, the lists lie below the heap pointer `hp`, memory from
`hp` on is zero and the space of the initialization fits in a word, then operation `0` of
`bucketSpannerDS` may be called on slot `slot < cap` with this descriptor. -/
theorem bucketActivatePre_of_exportAt {P : DSParams} {cap : ℕ} {mem : ℕ → ℕ} {d hEnd : ℕ}
    {G : MGraph} (hx : ExportAt mem d hEnd G) (hok : SpanGraphOK P (normGraph G))
    {tbl slot hp : ℕ} (hslot : slot < cap) (hEnd_hp : hEnd ≤ hp) (hp1 : 1 ≤ hp)
    (hz : ZeroFrom mem hp) (hspace : hp + spanActivateSpace P (normGraph G) < 2 ^ P.w) :
    BucketActivatePre P cap (activateArgs P mem tbl slot d hp) mem := by
  have hG := initArgsGraph_of_exportAt hx tbl slot P.L P.splitBound P.vCap P.eCap hp
  obtain ⟨hn, hm, _, hV, hnd, hT, hcov, _, _, _, hVend, hEend⟩ := hx
  obtain ⟨hL1, hps, hw16, hnW, hmW, hws, hval, hmM, hvC, heC⟩ := hok
  refine ⟨tbl, slot, mem d, mem (d + 1), mem (d + 2), mem (d + 3), hp, rfl, hslot, ?_, ?_⟩
  · rw [hn]; exact hnW
  · unfold activateArgs at hG ⊢
    unfold DSInitPre
    rw [hG]
    refine ⟨phaseBase (mem d + P.splitBound) P.L, mem d, mem (d + 1), mem (d + 2), mem (d + 3),
      hp, rfl, by rw [hn]; rfl, hL1, hps, ?_⟩
    refine ⟨mem (d + 1), mem (d + 3), hp, ?_, hw16, hp1,
      le_trans (by omega) (two_le_phaseBase _ _), ?_, hz, hmW, hws, hval, hmM, hvC, heC, ?_, (fun i hi => by simp [readList]),
      ?_, ?_, ?_, hnd, ?_, ?_, ?_, ?_⟩
    · simp only [readList_length, readTriples_length]; rfl
    · unfold spanActivateSpace at hspace; omega
    · rw [readList_length, hn]; rfl
    · intro v; rw [hV]; rfl
    · intro i hi; rw [readList_length] at hi; omega
    · rw [readTriples_length, hm]; rfl
    · intro i hi
      rw [readTriples_length] at hi
      simp [readTriples]
    · intro t ht
      have h := hT t ht
      refine ⟨h.1, ?_, ?_⟩
      · show t.2.1 = (if t.1 ∈ G.E then G.tail t.1 else 0)
        simp only [h.1, ↓reduceIte]; exact h.2.1
      · show t.2.2 = (if t.1 ∈ G.E then G.head t.1 else 0)
        simp only [h.1, ↓reduceIte]; exact h.2.2
    · intro e he; exact hcov e he
    · intro i hi; rw [readTriples_length] at hi; omega

/-- The cost bound of operation `0` on a descriptor of `G` is `spanActivateCost P (normGraph G)`. -/
theorem bucketActivateCost_of_exportAt {P : DSParams} {cap : ℕ} {mem : ℕ → ℕ} {d hEnd : ℕ}
    {G : MGraph} (hx : ExportAt mem d hEnd G) (S : BucketSpannerState cap) (tbl slot hp : ℕ) :
    (bucketSpannerDS P cap).cost 0 S (activateArgs P mem tbl slot d hp) mem =
      spanActivateCost P (normGraph G) := by
  have hG := initArgsGraph_of_exportAt hx tbl slot P.L P.splitBound P.vCap P.eCap hp
  have hn := hx.1
  unfold activateArgs at hG ⊢
  simp only [bucketSpannerDS, dynSpannerDS, dsInitContract, List.getD_cons_succ,
    List.getD_cons_zero]
  rw [hG, spanActivateCost, normGraph_n, ← hn]

/-- The space bound of operation `0` on a descriptor of `G` is `spanActivateSpace P (normGraph G)`. -/
theorem bucketActivateSpace_of_exportAt {P : DSParams} {cap : ℕ} {mem : ℕ → ℕ} {d hEnd : ℕ}
    {G : MGraph} (hx : ExportAt mem d hEnd G) (S : BucketSpannerState cap) (tbl slot hp : ℕ) :
    (bucketSpannerDS P cap).space 0 S (activateArgs P mem tbl slot d hp) mem =
      spanActivateSpace P (normGraph G) := by
  have hG := initArgsGraph_of_exportAt hx tbl slot P.L P.splitBound P.vCap P.eCap hp
  unfold activateArgs at hG ⊢
  simp only [bucketSpannerDS, dynSpannerDS]
  rw [hG]; rfl

end

end MinCostFlow.SparseCore.Program.Restart
