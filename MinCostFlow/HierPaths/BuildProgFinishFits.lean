module

public import MinCostFlow.HierPaths.BuildProgFinishBatch
import MinCostFlow.HierPaths.QueryProgRoute

/-!
# Fitting the application scratch after routing

A matched reply already provides the endpoint and walk tables. The child
graphs fit below that reply. The shared arena starts with the positions and
has room for the raw walks. The router's length certificate bounds each
walk's scratch use.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- The child graph updates occupy separate regions below the router reply. -/
structure FinishChildRegions (w : ℕ) (D : ApplyBatchData) (ends rep : ℕ) : Prop where
  parent : ∀ i < D.matchings.length, ends + 2 * D.host.m ≤ D.addr i
  spend : ∀ i < D.matchings.length, D.cap i ≤ rep
  apart : ∀ i < D.matchings.length, ∀ j < D.matchings.length, i ≠ j →
    D.cap i ≤ D.addr j ∨ D.cap j ≤ D.addr i
  offsets : ∀ i < D.matchings.length, D.offset i < 2 ^ w

private theorem rowWordEnd {Ms : List (List (ℕ × ℕ))} {i mt : ℕ} {mem : ℕ → ℕ}
    (hi : i < Ms.length) (hAt : ListAt mem mt (csrList Ms.length (matchingRowWords Ms))) :
    matchingRowBase Ms mt i + 2 * (Ms.getD i []).length ≤
      mt + (csrList Ms.length (matchingRowWords Ms)).length := by
  have hEnd := csr_end_le Ms.length (matchingRowWords Ms) hi
  have hFirst := (matchingRow_view hi hAt).1
  have hOff := csrList_offset hAt hi.le
  rw [← hOff, hFirst, length_matchingRowWords] at hEnd
  unfold matchingRowBase
  omega

/-- The matched reply, room for the work areas, and the graph reservations
supply the precondition of the application wrapper. -/
theorem buildFinishBatch_pre_of_matched {w Δ L b z cap rep heap cuts graphs offsets ends : ℕ}
    {D : ApplyBatchData} {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)} {mem : ℕ → ℕ}
    (hReply : ListAt mem rep (routeResultWords (.matched D.matchings D.emb)))
    (hHeap : rep + (routeResultWords (.matched D.matchings D.emb)).length ≤ heap)
    (hZ : ZeroFrom mem heap) (hG : D.host.IsValid)
    (hMatch : RouteMatchedSpec D.host X pairs Δ L b z D.matchings D.emb)
    (hX : X ⊆ Finset.range D.host.n) (hPairs : ValidTerminalPairs X pairs)
    (hLength : routePathLen Δ b L ≤ cap)
    (hTables : ApplyBatchTables D mem cuts graphs offsets) (hCutsEnd : cuts + D.indices.length ≤ rep)
    (hRegions : FinishChildRegions w D ends rep)
    (hEdges : ListAt mem ends (D.host.edges.flatMap fun e => [e.1, e.2]))
    (hChildren : ∀ i < D.matchings.length, GraphAt mem (D.addr i) (D.graph i))
    (hLocal : ∀ i < D.matchings.length, ∀ e ∈ D.matchings.getD i [],
      D.offset i ≤ e.1 ∧ D.offset i ≤ e.2 ∧ e.1 < 2 ^ w ∧ e.2 < 2 ^ w)
    (hWord : D.cursor (heap + 4 + D.matchings.flatten.length + cap + 1 + D.host.n)
      D.matchings.length < 2 ^ w) :
    (buildFinishBatchContract w D).pre
      [rep, cuts, graphs, offsets, ends, D.host.n, cap, heap, D.matchings.length] mem := by
  let mt := (matchedTableBases mem rep).1
  let tb := (matchedTableBases mem rep).2
  let dir := heap + 4
  let vs := dir + D.matchings.flatten.length
  let P := vs + cap + 1
  let out := P + D.host.n
  change D.cursor out D.matchings.length < 2 ^ w at hWord
  have hOut : out < 2 ^ w := (D.cursor_mono out (Nat.zero_le _)).trans_lt hWord
  obtain ⟨hMt, hTb⟩ := routeMatched_view hReply
  obtain ⟨hME, hTE⟩ := matchedTables_end_le hReply hHeap
  change mt + (csrList D.matchings.length (matchingRowWords D.matchings)).length ≤ heap at hME
  change tb + (csrList D.matchings.flatten.length D.emb).length ≤ heap at hTE
  have hMtLo : rep ≤ mt := by unfold mt matchedTableBases; omega
  have hTbLo : rep ≤ tb := by unfold tb matchedTableBases; omega
  have hh : rep ≤ heap := by omega
  have hDir : heap + 4 = dir := rfl
  have hVs : dir + D.matchings.flatten.length = vs := rfl
  have hP : vs + cap + 1 = P := rfl
  have hOP : P + D.host.n = out := rfl
  have h1 : 1 < 2 ^ w := by omega
  have hCanon : ∀ i < D.matchings.length, ∀ j < (D.row i).count,
      (D.row i).u j < D.host.n ∧
      IsEdgeWalk D.host.edges ((D.row i).u j) ((D.row i).v j) ((D.row i).raw j) :=
    fun i hi j hj => matchingWalkRow_correct hMatch hX hPairs hi hj
  have hFit : ApplyBatchFit w D mt tb heap ends vs P dir out := by
    refine ⟨hRegions.offsets, ?_, hRegions.apart, hDir.le, hVs.le, by omega, hOP.le, hWord, h1⟩
    intro i hi
    let R := D.row i
    let rowDir := D.directory dir i
    let top := D.cursor out i
    have hTop : out ≤ top := D.cursor_mono out (Nat.zero_le i)
    have hLo : dir ≤ rowDir := Nat.le_add_right _ _
    have he := matchingRow_end_le hi
    change R.first + R.count ≤ R.total at he
    have hFlat : R.total = D.matchings.flatten.length := rfl
    have hRows : rowDir + R.count ≤ vs := by
      have hRow : rowDir = dir + R.first := rfl
      omega
    have hAt : ListAt mem mt (csrList D.matchings.length (matchingRowWords D.matchings)) := hMt
    have hSource := (rowWordEnd hi hAt).trans hME
    have hCap := hRegions.spend i hi
    refine ⟨hi, hRegions.parent i hi, hCap.trans hMtLo, hCap.trans hTbLo, hME, hTE,
      by omega, by omega, ?_⟩
    refine ⟨he, hTE.trans (by omega), hSource.trans (by omega), ?_, hRows, ?_, by omega, ?_, h1⟩
    · exact (hRegions.parent i hi).trans (by
        have hc : D.addr i ≤ D.cap i := by unfold ApplyBatchData.cap; omega
        omega)
    · intro j hj
      have hi' := (getD_flatten_flatIndex D.matchings (0, 0) hi hj).1
      have hRaw := hMatch.2.2.2.2.1 _ hi'
      change (R.raw j).length ≤ routePathLen Δ b L at hRaw
      change vs + (R.raw j).length + 1 ≤ P
      omega
    · exact (D.cursor_mono out (show i + 1 ≤ D.matchings.length by omega)).trans_lt hWord
  refine ⟨rep,cuts,graphs,offsets,ends,cap,heap,rfl,hReply,hHeap,hOut,?_⟩
  refine ⟨mt,tb,cuts,graphs,offsets,heap,ends,vs,P,dir,out,rfl,hTables,hCutsEnd.trans hMtLo,hFit,hG,hMt,hTb,hEdges,
    fun i hi => ⟨hChildren i hi,hLocal i hi,hCanon i hi⟩,?_ ,?_⟩
  · intro a ha
    exact hZ a (by omega)
  · intro a _
    exact hZ _ (by omega)

end MinCostFlow.HierPaths
