module

public import MinCostFlow.DynSpanner.Program.GraphTranslateCollect
public import MinCostFlow.Spanner.Layouts
public import MinCostFlow.Spanner.MGraphTranslate

import Mathlib.Data.List.TakeDrop

/-!
# Canonical Translation Input Layout & Graph Emitters (`GraphTranslateEmit`)

Defines:
1. Canonical serialized input layout `canonWalkOffsets` / `canonSparsifyInput` packing
   `toCitedH H' J emb`, `toCitedJ J`, and `embToCited H' J emb` into a self-contained buffer
   `[3, pJ, pEmb] ++ cH.encode ++ cJ.encode ++ walkOffsets ++ walkData`, with `GraphAt`, `EmbAt`,
   and `EmbBounded` lemmas.
2. Deterministic Word-RAM emitter procedures `gtEmitProcs` (`gtEmitCitedJ`, `gtEmitCitedH`,
   `gtEmitEmbToCited`) and verification of `gtEmitCitedJ_meetsContract` and
   `gtEmitCitedH_meetsContract` (`gtEmitEmbToCited_meetsContract` is in `GraphTranslateEmitWalk`).
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner (Walk WalkAt EmbAt EmbBounded GraphAt toCitedJ toCitedH walkToCited
  embToCited hVerts hEdges vertsOf mem_vertsOf vertsOf_length vertsOf_nodup
  mgraph_mem_walkVertices_src_dst walk_encode_length graph_encode_length
  toCitedJ_m toCitedH_m usedHVerts usedHEdges usedHVerts_subset_V)

@[expose] public section

def gtIdxEmitCitedJ : ℕ := 0
def gtIdxEmitCitedH : ℕ := 1
def gtIdxEmitEmbToCited : ℕ := 2

lemma vertsOf_pairwise_lt (X : Finset ℕ) : (vertsOf X).Pairwise (· < ·) :=
  ((Finset.pairwise_sort X (· ≤ ·)).and (vertsOf_nodup X)).imp fun h =>
    lt_of_le_of_ne h.1 h.2

/-! ## Pure canonical serialization & walk translation lemmas -/

/-- Relative offset table for a list of `Cited.Walk` encodings starting at `base`. -/
def canonWalkOffsets (base : ℕ) : List Walk → List ℕ
  | [] => []
  | w :: ws => base :: canonWalkOffsets (base + (Walk.encode w).length) ws

/-- Canonical flat buffer encoding `toCitedH H' J emb`, `toCitedJ J`, and `embToCited H' J emb`:
`[3, pJ, pEmb] ++ cH.encode ++ cJ.encode ++ canonWalkOffsets pWalks cWalks ++ cWalks.flatMap Walk.encode`. -/
def canonSparsifyInput (H' J : MGraph) (emb : MinCostFlow.Embedding) : List ℕ :=
  let cH := toCitedH H' J emb
  let cJ := toCitedJ J
  let cWalks := (List.range cJ.m).map (embToCited H' J emb)
  let pH := 3
  let pJ := pH + cH.encode.length
  let pEmb := pJ + cJ.encode.length
  let pWalks := pEmb + cJ.m
  [pH, pJ, pEmb] ++ cH.encode ++ cJ.encode ++ canonWalkOffsets pWalks cWalks ++
    cWalks.flatMap Walk.encode

@[simp] lemma canonWalkOffsets_length (base : ℕ) (ws : List Walk) :
    (canonWalkOffsets base ws).length = ws.length := by
  induction ws generalizing base with
  | nil => rfl
  | cons w ws ih => simp [canonWalkOffsets, ih]

lemma canonWalkOffsets_append (base : ℕ) (xs ys : List Walk) :
    canonWalkOffsets base (xs ++ ys) =
      canonWalkOffsets base xs ++
        canonWalkOffsets (base + (xs.flatMap Walk.encode).length) ys := by
  induction xs generalizing base with
  | nil => simp [canonWalkOffsets]
  | cons x xs ih =>
    simp only [List.cons_append, canonWalkOffsets, List.flatMap_cons, List.length_append, ih,
      Nat.add_assoc]

lemma canonWalkOffsets_getElem (base : ℕ) :
    ∀ (ws : List Walk) (j : ℕ) (hj : j < ws.length),
      (canonWalkOffsets base ws)[j]'(by simp [hj]) =
        base + ((ws.take j).flatMap Walk.encode).length
  | [], _, hj => by simp at hj
  | w :: ws, 0, _ => by simp [canonWalkOffsets]
  | w :: ws, j + 1, hj => by
    have hj' : j < ws.length := by simpa using hj
    have ih := canonWalkOffsets_getElem (base + (Walk.encode w).length) ws j hj'
    simp only [canonWalkOffsets, List.getElem_cons_succ, ih, List.take_succ_cons,
      List.flatMap_cons, List.length_append]
    omega

lemma listAt_flatMap_getElem {mem : ℕ → ℕ} {base : ℕ} {f : Walk → List ℕ} :
    ∀ (ws : List Walk), ListAt mem base (ws.flatMap f) →
      ∀ j (hj : j < ws.length),
        ListAt mem (base + ((ws.take j).flatMap f).length) (f (ws[j]'hj))
  | [], _, _, hj => by simp at hj
  | w :: ws, h, 0, _ => by
    simp only [List.flatMap_cons] at h
    simpa using (listAt_append.mp h).1
  | w :: ws, h, j + 1, hj => by
    simp only [List.flatMap_cons] at h
    have ih := listAt_flatMap_getElem ws (listAt_append.mp h).2 j (by simpa using hj)
    simpa [List.take_succ_cons, List.flatMap_cons, List.length_append, Nat.add_assoc] using ih

lemma embAt_of_walkOffsets_flat {mem : ℕ → ℕ} {ptrs data : ℕ}
    {ws : List Walk} {emb : ℕ → Walk}
    (hPtrs : ListAt mem ptrs (canonWalkOffsets data ws))
    (hFlat : ListAt mem data (ws.flatMap Walk.encode))
    (hLe : ptrs + ws.length ≤ data + (ws.flatMap Walk.encode).length)
    (heq : ∀ j (hj : j < ws.length), emb j = ws[j]'hj) :
    EmbAt mem ptrs ws.length emb ∧
      EmbBounded mem ptrs ws.length emb (data + (ws.flatMap Walk.encode).length) := by
  have hElem : ∀ j (hj : j < ws.length),
      mem (ptrs + j) = data + ((ws.take j).flatMap Walk.encode).length := by
    intro j hj
    have h1 := hPtrs j (by simpa using hj)
    rw [canonWalkOffsets_getElem (hj := by simpa using hj)] at h1
    exact h1
  refine ⟨fun j hj => ?_, hLe, fun j hj => ?_⟩
  · rw [hElem j hj, heq j hj]
    exact listAt_flatMap_getElem ws hFlat j hj
  · rw [hElem j hj, heq j hj]
    have htake : (ws.take (j + 1)).flatMap Walk.encode =
        (ws.take j).flatMap Walk.encode ++ Walk.encode (ws[j]'hj) := by
      rw [List.take_succ_eq_append_getElem hj, List.flatMap_append]
      simp
    have hsplit : ws = ws.take (j + 1) ++ ws.drop (j + 1) := (List.take_append_drop _ _).symm
    have hlen_le : ((ws.take (j + 1)).flatMap Walk.encode).length ≤
        (ws.flatMap Walk.encode).length := by
      conv_rhs => rw [hsplit, List.flatMap_append, List.length_append]
      exact Nat.le_add_right _ _
    rw [← Nat.add_le_add_iff_left (n := data)] at hlen_le
    rw [htake, List.length_append, ← Nat.add_assoc] at hlen_le
    simpa [Nat.add_assoc] using hlen_le

theorem canonSparsifyInput_length (H' J : MGraph) (emb : MinCostFlow.Embedding) :
    (canonSparsifyInput H' J emb).length =
      3 + (2 + 2 * (toCitedH H' J emb).m) + (2 + 2 * J.m) + J.m +
        (((List.range J.m).map (embToCited H' J emb)).flatMap Walk.encode).length := by
  dsimp only [canonSparsifyInput]
  simp only [List.length_append, List.length_cons, List.length_nil, canonWalkOffsets_length,
    List.length_map, List.length_range, graph_encode_length, toCitedJ_m]

theorem canonSparsifyInput_decomp {mem : ℕ → ℕ} {base : ℕ}
    {H' J : MGraph} {emb : MinCostFlow.Embedding}
    (hAt : ListAt mem base (canonSparsifyInput H' J emb)) :
    let cH := toCitedH H' J emb
    let cJ := toCitedJ J
    let cWalks := (List.range cJ.m).map (embToCited H' J emb)
    let pH := 3
    let pJ := pH + cH.encode.length
    let pEmb := pJ + cJ.encode.length
    let pWalks := pEmb + cJ.m
    mem base = pH ∧ mem (base + 1) = pJ ∧ mem (base + 2) = pEmb ∧
      GraphAt mem (base + pH) cH ∧ GraphAt mem (base + pJ) cJ ∧
      ListAt mem (base + pEmb) (canonWalkOffsets pWalks cWalks) ∧
      ListAt mem (base + pWalks) (cWalks.flatMap Walk.encode) := by
  dsimp only [canonSparsifyInput] at hAt
  rcases listAt_append.mp hAt with ⟨h1234, hFlat⟩
  rcases listAt_append.mp h1234 with ⟨h123, hOff⟩
  rcases listAt_append.mp h123 with ⟨h12, hcJ⟩
  rcases listAt_append.mp h12 with ⟨hHdr, hcH⟩
  have hm0 : mem base = 3 := by simpa using hHdr 0 (by simp)
  have hm1 : mem (base + 1) = 3 + (toCitedH H' J emb).encode.length := by
    simpa using hHdr 1 (by simp)
  have hm2 : mem (base + 2) =
      3 + (toCitedH H' J emb).encode.length + (toCitedJ J).encode.length := by
    simpa using hHdr 2 (by simp)
  simp only [List.length_cons, List.length_nil, List.length_append, canonWalkOffsets_length,
    List.length_map, List.length_range] at hcH hcJ hOff hFlat
  refine ⟨hm0, hm1, hm2, ?_, ?_, ?_, ?_⟩
  · simpa [GraphAt, Nat.add_assoc] using hcH
  · simpa [GraphAt, Nat.add_assoc] using hcJ
  · simpa [Nat.add_assoc] using hOff
  · simpa [Nat.add_assoc] using hFlat

theorem canonSparsifyInput_EmbAt {mem : ℕ → ℕ} {H' J : MGraph} {emb : MinCostFlow.Embedding}
    (hAt : ListAt mem 0 (canonSparsifyInput H' J emb)) :
    let cH := toCitedH H' J emb
    let cJ := toCitedJ J
    let pEmb := 3 + cH.encode.length + cJ.encode.length
    EmbAt mem pEmb cJ.m (embToCited H' J emb) ∧
      EmbBounded mem pEmb cJ.m (embToCited H' J emb) (canonSparsifyInput H' J emb).length := by
  dsimp only
  have hd := canonSparsifyInput_decomp hAt
  rcases hd with ⟨_, _, _, _, _, hOff, hFlat⟩
  simp only [Nat.zero_add] at hOff hFlat
  have hres := embAt_of_walkOffsets_flat (emb := embToCited H' J emb) hOff hFlat (by
    simp only [List.length_map, List.length_range]; exact Nat.le_add_right _ _)
    fun j hj => by
      have hj' : j < (toCitedJ J).m := by
        simpa [List.length_map, List.length_range] using hj
      simp only [List.getElem_map, List.getElem_range]
  have hlen : (canonSparsifyInput H' J emb).length =
      3 + (toCitedH H' J emb).encode.length + (toCitedJ J).encode.length + (toCitedJ J).m +
        (((List.range (toCitedJ J).m).map (embToCited H' J emb)).flatMap Walk.encode).length := by
    dsimp only [canonSparsifyInput]
    simp only [List.length_append, List.length_cons, List.length_nil, canonWalkOffsets_length,
      List.length_map, List.length_range]
  simpa only [List.length_map, List.length_range, ← hlen] using hres

lemma emb_usedH_props {H' J : MGraph} {emb : MinCostFlow.Embedding}
    (hH' : H'.IsValid) (hJ : J.IsValid) (hemb : emb.IsEmbedding J H') :
    (∀ e ∈ usedHEdges J emb, e ∈ H'.E) ∧
    (∀ v ∈ usedHVerts H' J emb, v ∈ H'.V) := by
  refine ⟨fun e he => ?_, fun v hv => usedHVerts_subset_V hH' hJ hemb hv⟩
  simp only [usedHEdges, Finset.mem_biUnion, List.mem_toFinset,
    MinCostFlow.walkEdges, List.mem_map] at he
  rcases he with ⟨eJ, heJ, y, hy, rfl⟩
  exact (mgraph_mem_walkVertices_src_dst (hemb.2 eJ heJ) y hy).1

/-- Explicit flat encode equality for `Cited.Graph.encode` via `List.range G.m`. -/
lemma citedGraph_encode_eq_range (G : Cited.Graph) :
    G.encode = G.n :: G.m :: (List.range G.m).flatMap
      (fun j => [(G.edges.getD j (0, 0)).1, (G.edges.getD j (0, 0)).2]) := by
  simp only [Cited.Graph.encode, Cited.Graph.m]
  congr 2
  have haux : ∀ (es : List (ℕ × ℕ)),
      es.flatMap (fun e => [e.1, e.2]) =
        (List.range es.length).flatMap
          (fun j => [(es.getD j (0, 0)).1, (es.getD j (0, 0)).2]) := by
    intro es
    induction es with
    | nil => simp
    | cons e es ih =>
      simp only [List.flatMap_cons, List.length_cons, List.range_succ_eq_map,
        List.flatMap_map, ih]
      simp
  exact haux G.edges

lemma toCitedJ_encode_steps (J : MGraph) (jVs jEs jTails jHeads : List ℕ)
    (hjV : jVs = vertsOf J.V) (hjE : jEs = vertsOf J.E)
    (hLenT : jTails.length = jEs.length) (hLenH : jHeads.length = jEs.length)
    (htail : ∀ j (hj : j < jEs.length), jTails[j]'(hLenT ▸ hj) = J.tail (jEs[j]'hj))
    (hhead : ∀ j (hj : j < jEs.length), jHeads[j]'(hLenH ▸ hj) = J.head (jEs[j]'hj)) :
    (toCitedJ J).encode = jVs.length :: jEs.length :: (List.range jEs.length).flatMap
      (fun j => [jVs.idxOf (jTails.getD j 0), jVs.idxOf (jHeads.getD j 0)]) := by
  rw [citedGraph_encode_eq_range]
  have hm : (toCitedJ J).m = jEs.length := by
    simp [toCitedJ, Cited.Graph.m, hjE]
  have hn : (toCitedJ J).n = jVs.length := by
    simp [toCitedJ, hjV]
  rw [hn, hm]
  congr 2
  rw [List.flatMap_congr]
  intro j hj
  rw [List.mem_range] at hj
  have hjT : j < jTails.length := hLenT ▸ hj
  have hjH : j < jHeads.length := hLenH ▸ hj
  have hedge : (toCitedJ J).edges.getD j (0, 0) =
      (jVs.idxOf (jTails.getD j 0), jVs.idxOf (jHeads.getD j 0)) := by
    simp only [toCitedJ, ← hjV, ← hjE, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some]
    rw [List.getElem?_eq_getElem hjT, List.getElem?_eq_getElem hjH,
      Option.getD_some, Option.getD_some, htail j hj, hhead j hj]
  rw [hedge]

lemma toCitedH_encode_steps (H' J : MGraph) (emb : MinCostFlow.Embedding)
    (jVs exVs hEs : List ℕ)
    (hjV : jVs = vertsOf J.V)
    (hexV : exVs = vertsOf (usedHVerts H' J emb \ J.V))
    (hhE : hEs = vertsOf (usedHEdges J emb)) :
    (toCitedH H' J emb).encode =
      (jVs.length + exVs.length) :: hEs.length :: (List.range hEs.length).flatMap
        (fun i => [(jVs ++ exVs).idxOf (H'.tail (hEs.getD i 0)),
          (jVs ++ exVs).idxOf (H'.head (hEs.getD i 0))]) := by
  rw [citedGraph_encode_eq_range]
  have hhVs : hVerts H' J emb = jVs ++ exVs := by
    simp [hVerts, hjV, hexV]
  have hn : (toCitedH H' J emb).n = jVs.length + exVs.length := by
    simp [toCitedH, hhVs]
  have hm : (toCitedH H' J emb).m = hEs.length := by
    simp only [toCitedH, Cited.Graph.m, hEdges, List.length_map, hhE]
  rw [hn, hm]
  congr 2
  rw [List.flatMap_congr]
  intro i hi
  rw [List.mem_range] at hi
  have hedge : (toCitedH H' J emb).edges.getD i (0, 0) =
      ((jVs ++ exVs).idxOf (H'.tail (hEs.getD i 0)),
       (jVs ++ exVs).idxOf (H'.head (hEs.getD i 0))) := by
    simp only [List.getD_eq_getElem?_getD, toCitedH, hEdges, ← hhE, hhVs,
      List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]
  rw [hedge]

lemma walkToCited_empty_encode (H' : MGraph) (vs es : List ℕ) (u : ℕ) :
    Walk.encode (walkToCited H' vs es u []) = [0, 0] := by
  simp [walkToCited, Walk.empty, Walk.encode]

lemma walkToCited_nonempty_encode (H' : MGraph) (vs es : List ℕ) (u : ℕ)
    (P : List (ℕ × Bool)) (hne : P ≠ []) :
    Walk.encode (walkToCited H' vs es u P) =
      (P.length + 1) :: vs.idxOf u ::
        ((List.range P.length).map fun t => vs.idxOf (H'.dst (P[t]!))) ++
        P.length :: ((List.range P.length).map fun t => es.idxOf (P[t]!).1) := by
  have hne' : P.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
  simp only [walkToCited, hne', Bool.false_eq_true, ↓reduceIte, Walk.encode,
    List.length_map, MGraph.walkVertices, List.length_cons, List.map_cons,
    List.cons_append]
  refine congr_arg ((P.length + 1) :: vs.idxOf u :: ·) ?_
  refine congr_arg₂ (· ++ ·) ?_ (congr_arg (P.length :: ·) ?_)
  · refine List.ext_getElem (by simp) fun t ht1 ht2 => ?_
    simp only [List.length_map] at ht1
    simp only [List.getElem_map, List.getElem_range, List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem ht1, Option.getD_some]
  · refine List.ext_getElem (by simp) fun t ht1 ht2 => ?_
    simp only [List.length_map] at ht1
    simp only [List.getElem_map, List.getElem_range, List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem ht1, Option.getD_some]

/-! ## Emitter procedures (`gtEmitProcs`) -/

/-- Emit `toCitedJ J` in `Cited.Graph.encode` format at `outPtr`, returning `2 + 2 * mJ`
(`[mJ, jVsPtr, nJ, jTailsPtr, jHeadsPtr, outPtr]`). -/
def gtEmitCitedJStmt (bSort : ℕ) : Stmt :=
  .store (.reg 5) (.reg 2) ;;
  .store (.bin .add (.reg 5) (.const 1)) (.reg 0) ;;
  forRange 6 (.const 0) (.reg 0)
    (.assign 7 (.load (.bin .add (.reg 3) (.reg 6))) ;;
     .call 8 (bSort + sortIdxBinSearch) [.reg 1, .reg 2, .reg 7] ;;
     .store (.bin .add (.reg 5) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 6)))) (.reg 8) ;;
     .assign 7 (.load (.bin .add (.reg 4) (.reg 6))) ;;
     .call 8 (bSort + sortIdxBinSearch) [.reg 1, .reg 2, .reg 7] ;;
     .store (.bin .add (.reg 5) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 6)))) (.reg 8)) ;;
  .ret (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 0)))

/-- Emit `toCitedH H' J emb` in `Cited.Graph.encode` format at `outPtr`, returning `2 + 2 * mH`
(`[hPtr, nJ, exVsPtr, nEx, hEsPtr, mH, jVsPtr, outPtr]`). -/
def gtEmitCitedHStmt (bOps bGT : ℕ) : Stmt :=
  .store (.reg 7) (.bin .add (.reg 1) (.reg 3)) ;;
  .store (.bin .add (.reg 7) (.const 1)) (.reg 5) ;;
  forRange 8 (.const 0) (.reg 5)
    (.assign 9 (.load (.bin .add (.reg 4) (.reg 8))) ;;
     .call 10 (bOps + dgIdxGetTail) [.reg 0, .reg 9] ;;
     .call 11 (bGT + gtIdxLookupHVert) [.reg 6, .reg 1, .reg 2, .reg 3, .reg 10] ;;
     .store (.bin .add (.reg 7) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 8)))) (.reg 11) ;;
     .call 10 (bOps + dgIdxGetHead) [.reg 0, .reg 9] ;;
     .call 11 (bGT + gtIdxLookupHVert) [.reg 6, .reg 1, .reg 2, .reg 3, .reg 10] ;;
     .store (.bin .add (.reg 7) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 8)))) (.reg 11)) ;;
  .ret (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 5)))

/-- Emit `canonWalkOffsets` at `ptrsOut` and `Walk.encode` data at `dataOut` for
`embToCited H' J emb`, returning total walk data words written
(`[hPtr, mJ, jEsPtr, jTailsPtr, mEmbPtr, jVsPtr, nJ, exVsPtr, nEx, hEsPtr, mH, ptrsOut, dataOut, offBase]`). -/
def gtEmitEmbToCitedStmt (bSort bOps bGT : ℕ) : Stmt :=
  .assign 14 (.const 0) ;;
  forRange 15 (.const 0) (.reg 1)
    (.store (.bin .add (.reg 11) (.reg 15)) (.bin .add (.reg 13) (.reg 14)) ;;
     .assign 16 (.load (.bin .add (.reg 2) (.reg 15))) ;;
     .assign 17 (.load (.bin .add (.reg 4) (.reg 16))) ;;
     .assign 18 (.load (.reg 17)) ;;
     .cond (.bin .eq (.reg 18) (.const 0))
       (.store (.bin .add (.reg 12) (.reg 14)) (.const 0) ;;
        .store (.bin .add (.reg 12) (.bin .add (.reg 14) (.const 1))) (.const 0) ;;
        .assign 14 (.bin .add (.reg 14) (.const 2)))
       (.assign 19 (.bin .add (.reg 12) (.reg 14)) ;;
        .store (.reg 19) (.bin .add (.reg 18) (.const 1)) ;;
        .store (.bin .add (.reg 19) (.bin .add (.const 2) (.reg 18))) (.reg 18) ;;
        .assign 20 (.load (.bin .add (.reg 3) (.reg 15))) ;;
        .call 21 (bGT + gtIdxLookupHVert) [.reg 5, .reg 6, .reg 7, .reg 8, .reg 20] ;;
        .store (.bin .add (.reg 19) (.const 1)) (.reg 21) ;;
        forRange 20 (.const 0) (.reg 18)
          (.assign 21 (.load (.bin .add (.reg 17) (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 20))))) ;;
           .assign 22 (.load (.bin .add (.reg 17) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 20))))) ;;
           .cond (.bin .eq (.reg 22) (.const 1))
             (.call 23 (bOps + dgIdxGetHead) [.reg 0, .reg 21])
             (.call 23 (bOps + dgIdxGetTail) [.reg 0, .reg 21]) ;;
           .call 24 (bGT + gtIdxLookupHVert) [.reg 5, .reg 6, .reg 7, .reg 8, .reg 23] ;;
           .store (.bin .add (.reg 19) (.bin .add (.const 2) (.reg 20))) (.reg 24) ;;
           .call 24 (bSort + sortIdxBinSearch) [.reg 9, .reg 10, .reg 21] ;;
           .store (.bin .add (.reg 19) (.bin .add (.bin .add (.const 3) (.reg 18)) (.reg 20))) (.reg 24)) ;;
        .assign 14 (.bin .add (.reg 14) (.bin .add (.bin .mul (.const 2) (.reg 18)) (.const 3))))) ;;
  .ret (.reg 14)

def gtEmitProcs (bSort bOps bGT : ℕ) : List Stmt :=
  [gtEmitCitedJStmt bSort, gtEmitCitedHStmt bOps bGT, gtEmitEmbToCitedStmt bSort bOps bGT]

lemma gtEmitProcs_length (bSort bOps bGT : ℕ) : (gtEmitProcs bSort bOps bGT).length = 3 := rfl

lemma gtEmitProcs_noRand (bSort bOps bGT : ℕ) : ∀ s ∈ gtEmitProcs bSort bOps bGT, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-! ## Emitter contracts -/

def gtEmitCitedJContract (w : ℕ) (J : MGraph) (jVs jEs jTails jHeads : List ℕ) : Contract where
  pre args mem := ∃ jVsPtr jTailsPtr jHeadsPtr outPtr,
    args = [jEs.length, jVsPtr, jVs.length, jTailsPtr, jHeadsPtr, outPtr] ∧
    16 ≤ 2 ^ w ∧
    jVsPtr + jVs.length < 2 ^ w ∧ jTailsPtr + jEs.length < 2 ^ w ∧
    jHeadsPtr + jEs.length < 2 ^ w ∧ outPtr + (2 + 2 * jEs.length) < 2 ^ w ∧
    (∀ i < jVs.length, jVsPtr + i < outPtr ∨ outPtr + (2 + 2 * jEs.length) ≤ jVsPtr + i) ∧
    (∀ i < jEs.length, jTailsPtr + i < outPtr ∨ outPtr + (2 + 2 * jEs.length) ≤ jTailsPtr + i) ∧
    (∀ i < jEs.length, jHeadsPtr + i < outPtr ∨ outPtr + (2 + 2 * jEs.length) ≤ jHeadsPtr + i) ∧
    J.IsValid ∧ jVs = vertsOf J.V ∧ jEs = vertsOf J.E ∧
    jTails.length = jEs.length ∧ jHeads.length = jEs.length ∧
    (∀ j (hj : j < jEs.length),
      jTails.getD j 0 = J.tail (jEs[j]'hj) ∧
      jHeads.getD j 0 = J.head (jEs[j]'hj)) ∧
    ListAt mem jVsPtr jVs ∧ ListAt mem jTailsPtr jTails ∧ ListAt mem jHeadsPtr jHeads ∧
    (∀ v ∈ jVs, v < 2 ^ w)
  post args mem ret mem' := ∃ jVsPtr jTailsPtr jHeadsPtr outPtr,
    args = [jEs.length, jVsPtr, jVs.length, jTailsPtr, jHeadsPtr, outPtr] ∧
    ret = 2 + 2 * jEs.length ∧ GraphAt mem' outPtr (toCitedJ J) ∧
    ∀ addr, addr < outPtr ∨ outPtr + (2 + 2 * jEs.length) ≤ addr → mem' addr = mem addr
  cost _ _ := 100 * jEs.length * (Nat.log 2 (jVs.length + 1) + 1) + 85 * jEs.length + 45

def gtEmitCitedHContract (w vCap eCap : ℕ) (H' J : MGraph) (emb : MinCostFlow.Embedding)
    (jVs exVs hEs : List ℕ) : Contract where
  pre args mem := ∃ hPtr exVsPtr hEsPtr jVsPtr outPtr,
    args = [hPtr, jVs.length, exVsPtr, exVs.length, hEsPtr, hEs.length, jVsPtr, outPtr] ∧
    16 ≤ 2 ^ w ∧
    hPtr + dynGraphSize vCap eCap < 2 ^ w ∧
    jVsPtr + jVs.length < 2 ^ w ∧ exVsPtr + exVs.length < 2 ^ w ∧
    hEsPtr + hEs.length < 2 ^ w ∧ outPtr + (2 + 2 * hEs.length) < 2 ^ w ∧
    jVs.length + exVs.length < 2 ^ w ∧
    (∀ i < dynGraphSize vCap eCap, hPtr + i < outPtr ∨ outPtr + (2 + 2 * hEs.length) ≤ hPtr + i) ∧
    (∀ i < jVs.length, jVsPtr + i < outPtr ∨ outPtr + (2 + 2 * hEs.length) ≤ jVsPtr + i) ∧
    (∀ i < exVs.length, exVsPtr + i < outPtr ∨ outPtr + (2 + 2 * hEs.length) ≤ exVsPtr + i) ∧
    (∀ i < hEs.length, hEsPtr + i < outPtr ∨ outPtr + (2 + 2 * hEs.length) ≤ hEsPtr + i) ∧
    DynGraphAt mem hPtr vCap eCap H' ∧
    jVs = vertsOf J.V ∧ exVs = vertsOf (usedHVerts H' J emb \ J.V) ∧
    hEs = vertsOf (usedHEdges J emb) ∧
    ListAt mem jVsPtr jVs ∧ ListAt mem exVsPtr exVs ∧ ListAt mem hEsPtr hEs ∧
    (∀ e ∈ usedHEdges J emb, e ∈ H'.E) ∧
    (∀ x ∈ jVs, x < 2 ^ w) ∧ (∀ x ∈ exVs, x < 2 ^ w) ∧ (∀ e ∈ hEs, e < 2 ^ w) ∧
    (∀ e ∈ usedHEdges J emb, H'.tail e ∈ usedHVerts H' J emb ∧ H'.head e ∈ usedHVerts H' J emb)
  post args mem ret mem' := ∃ hPtr exVsPtr hEsPtr jVsPtr outPtr,
    args = [hPtr, jVs.length, exVsPtr, exVs.length, hEsPtr, hEs.length, jVsPtr, outPtr] ∧
    ret = 2 + 2 * hEs.length ∧ GraphAt mem' outPtr (toCitedH H' J emb) ∧
    ∀ addr, addr < outPtr ∨ outPtr + (2 + 2 * hEs.length) ≤ addr → mem' addr = mem addr
  cost _ _ := 200 * hEs.length * (Nat.log 2 (jVs.length + exVs.length + 1) + 1) + 330 * hEs.length + 45

def gtEmitEmbToCitedContract (w vCap eCap : ℕ) (H' J : MGraph) (emb : MinCostFlow.Embedding)
    (jVs exVs jEs jTails hEs : List ℕ) : Contract where
  pre args mem := ∃ hPtr jEsPtr jTailsPtr mEmbPtr jVsPtr exVsPtr hEsPtr ptrsOut dataOut offBase,
    let cWalks := (List.range jEs.length).map (embToCited H' J emb)
    let dataLen := (cWalks.flatMap Walk.encode).length
    args = [hPtr, jEs.length, jEsPtr, jTailsPtr, mEmbPtr, jVsPtr, jVs.length,
      exVsPtr, exVs.length, hEsPtr, hEs.length, ptrsOut, dataOut, offBase] ∧
    16 ≤ 2 ^ w ∧
    hPtr + dynGraphSize vCap eCap < 2 ^ w ∧
    jEsPtr + jEs.length < 2 ^ w ∧ jTailsPtr + jEs.length < 2 ^ w ∧
    mEmbPtr + eCap < 2 ^ w ∧ jVsPtr + jVs.length < 2 ^ w ∧
    exVsPtr + exVs.length < 2 ^ w ∧ hEsPtr + hEs.length < 2 ^ w ∧
    ptrsOut + jEs.length < 2 ^ w ∧ dataOut + dataLen < 2 ^ w ∧
    offBase + dataLen < 2 ^ w ∧ jVs.length + exVs.length < 2 ^ w ∧
    (ptrsOut + jEs.length ≤ dataOut ∨ dataOut + dataLen ≤ ptrsOut) ∧
    let dis := fun addr =>
      (addr < ptrsOut ∨ ptrsOut + jEs.length ≤ addr) ∧
      (addr < dataOut ∨ dataOut + dataLen ≤ addr)
    (∀ i < dynGraphSize vCap eCap, dis (hPtr + i)) ∧
    (∀ i < jEs.length, dis (jEsPtr + i)) ∧
    (∀ i < jEs.length, dis (jTailsPtr + i)) ∧
    (∀ e ∈ J.E, dis (mEmbPtr + e)) ∧
    (∀ e ∈ J.E, ∀ k < (mWalkEncode (emb e)).length, dis (mem (mEmbPtr + e) + k)) ∧
    (∀ i < jVs.length, dis (jVsPtr + i)) ∧
    (∀ i < exVs.length, dis (exVsPtr + i)) ∧
    (∀ i < hEs.length, dis (hEsPtr + i)) ∧
    DynGraphAt mem hPtr vCap eCap H' ∧ J.IsValid ∧ emb.IsEmbedding J H' ∧
    jVs = vertsOf J.V ∧ exVs = vertsOf (usedHVerts H' J emb \ J.V) ∧
    jEs = vertsOf J.E ∧ hEs = vertsOf (usedHEdges J emb) ∧
    jTails.length = jEs.length ∧
    (∀ j (hj : j < jEs.length), jTails.getD j 0 = J.tail (jEs[j]'hj)) ∧
    MEmbAt mem mEmbPtr J.E eCap emb ∧
    ListAt mem jEsPtr jEs ∧ ListAt mem jTailsPtr jTails ∧
    ListAt mem jVsPtr jVs ∧ ListAt mem exVsPtr exVs ∧ ListAt mem hEsPtr hEs ∧
    (∀ x ∈ jVs, x < 2 ^ w) ∧ (∀ x ∈ exVs, x < 2 ^ w) ∧ (∀ e ∈ hEs, e < 2 ^ w) ∧
    (∀ e ∈ J.E, (emb e).length < 2 ^ w ∧ mem (mEmbPtr + e) + (mWalkEncode (emb e)).length < 2 ^ w)
  post args mem ret mem' := ∃ hPtr jEsPtr jTailsPtr mEmbPtr jVsPtr exVsPtr hEsPtr ptrsOut dataOut offBase,
    let cWalks := (List.range jEs.length).map (embToCited H' J emb)
    let dataLen := (cWalks.flatMap Walk.encode).length
    args = [hPtr, jEs.length, jEsPtr, jTailsPtr, mEmbPtr, jVsPtr, jVs.length,
      exVsPtr, exVs.length, hEsPtr, hEs.length, ptrsOut, dataOut, offBase] ∧
    ret = dataLen ∧
    ListAt mem' ptrsOut (canonWalkOffsets offBase cWalks) ∧
    ListAt mem' dataOut (cWalks.flatMap Walk.encode) ∧
    ∀ addr, (addr < ptrsOut ∨ ptrsOut + jEs.length ≤ addr) →
      (addr < dataOut ∨ dataOut + dataLen ≤ addr) → mem' addr = mem addr
  cost _ _ :=
    230 * ((collectRawEsFun jEs emb).length + jEs.length) *
      (Nat.log 2 (jVs.length + exVs.length + hEs.length + 2) + 1) +
    360 * ((collectRawEsFun jEs emb).length + jEs.length) + 80

end

/-! ## Verification of `gtEmitCitedJ` and `gtEmitCitedH` -/

public section

theorem gtEmitCitedJ_meetsContract {w : ℕ} {p : Program} {b bSort bOps bGT : ℕ}
    {J : MGraph} {jVs jEs jTails jHeads : List ℕ}
    (hp : p.HasAt b (gtEmitProcs bSort bOps bGT)) (hpSort : p.HasAt bSort (sortProcs bSort)) :
    MeetsContract w p (b + gtIdxEmitCitedJ) (gtEmitCitedJContract w J jVs jEs jTails jHeads) := by
  refine meetsContract_of_runs (hp.get (i := gtIdxEmitCitedJ) (by simp [gtEmitProcs, gtIdxEmitCitedJ]))
    fun args mem pos _ hargs hpre => ?_
  rcases hpre with ⟨jVsPtr, jTailsPtr, jHeadsPtr, outPtr, rfl, hw16, hjVB, hjTB, hjHB, houtB,
    hdisjV, hdisjT, hdisjH, hJ, hjV, hjE, hLenT, hLenH, hTH, hVAt, hTAt, hHAt, hVw⟩
  have hlt_mJ : jEs.length < 2 ^ w := hargs jEs.length (by simp)
  have hlt_nJ : jVs.length < 2 ^ w := hargs jVs.length (by simp)
  have h0_lt : (0 : ℕ) < 2 ^ w := by omega
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have h2_lt : (2 : ℕ) < 2 ^ w := by omega
  have h3_lt : (3 : ℕ) < 2 ^ w := by omega
  have hjVPair : jVs.Pairwise (· < ·) := hjV ▸ vertsOf_pairwise_lt J.V
  let pairOf : ℕ → List ℕ := fun j => [jVs.idxOf (jTails.getD j 0), jVs.idxOf (jHeads.getD j 0)]
  let prefP : ℕ → List ℕ := fun j => (List.range j).flatMap pairOf
  have hprefP_len : ∀ j, (prefP j).length = 2 * j := by
    intro j
    induction j with
    | zero => simp [prefP]
    | succ j ih =>
      simp only [prefP, pairOf, List.range_succ, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.length_append, List.length_cons,
        List.length_nil] at ih ⊢
      omega
  refine runs_start_le ?_
  dsimp only [gtEmitProcs, gtIdxEmitCitedJ, List.getElem_cons_zero, gtEmitCitedJStmt]
  refine runs_seq_store_le (x := outPtr) (v := jVs.length)
    (by simp [Expr.eval, startState])
    (by eval_expr) ?_
  refine runs_seq_store_le (x := outPtr + 1) (v := jEs.length)
    (by simp [Expr.eval, BinOp.eval, startState, h1_lt, show outPtr + 1 < 2 ^ w by omega])
    (by eval_expr) ?_
  let body : Stmt :=
    .assign 7 (.load (.bin .add (.reg 3) (.reg 6))) ;;
    .call 8 (bSort + sortIdxBinSearch) [.reg 1, .reg 2, .reg 7] ;;
    .store (.bin .add (.reg 5) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 6)))) (.reg 8) ;;
    .assign 7 (.load (.bin .add (.reg 4) (.reg 6))) ;;
    .call 8 (bSort + sortIdxBinSearch) [.reg 1, .reg 2, .reg 7] ;;
    .store (.bin .add (.reg 5) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 6)))) (.reg 8)
  let InvPre : State → Prop := fun st =>
    st.regs 0 = jEs.length ∧ st.regs 1 = jVsPtr ∧ st.regs 2 = jVs.length ∧
    st.regs 3 = jTailsPtr ∧ st.regs 4 = jHeadsPtr ∧ st.regs 5 = outPtr ∧
    st.mem outPtr = jVs.length ∧ st.mem (outPtr + 1) = jEs.length ∧
    ListAt st.mem (outPtr + 2) (prefP 0) ∧
    ∀ addr, addr < outPtr ∨ outPtr + 2 ≤ addr → st.mem addr = mem addr
  let Inv : ℕ → State → Prop := fun j st =>
    st.regs 0 = jEs.length ∧ st.regs 1 = jVsPtr ∧ st.regs 2 = jVs.length ∧
    st.regs 3 = jTailsPtr ∧ st.regs 4 = jHeadsPtr ∧ st.regs 5 = outPtr ∧ st.regs 6 = j ∧
    st.mem outPtr = jVs.length ∧ st.mem (outPtr + 1) = jEs.length ∧
    ListAt st.mem (outPtr + 2) (prefP j) ∧
    ∀ addr, addr < outPtr ∨ outPtr + (2 + 2 * j) ≤ addr → st.mem addr = mem addr
  let stepC := 100 * (Nat.log 2 (jVs.length + 1) + 1) + 75
  have hloop : Triple w p InvPre (forRange 6 (.const 0) (.reg 0) body)
      (normalPost (Inv jEs.length))
      (fun _ => jEs.length * (stepC + Expr.size (.reg 0) + 8) +
        (Expr.size (.const 0) + Expr.size (.reg 0) + 5)) := by
    refine Triple.forRange_const stepC 0 jEs.length (Nat.zero_le _) h1_lt (fun _ => hlt_mJ)
      (fun st hInv => ⟨by simp [Expr.eval, h0_lt], by
        rcases hInv with ⟨r0, r1, r2, r3, r4, r5, hm0, hm1, hat, hfr⟩
        exact ⟨by simpa [Function.update_of_ne] using r0, by simpa [Function.update_of_ne] using r1,
          by simpa [Function.update_of_ne] using r2, by simpa [Function.update_of_ne] using r3,
          by simpa [Function.update_of_ne] using r4, by simpa [Function.update_of_ne] using r5,
          by simp, hm0, hm1, hat, by simpa using hfr⟩⟩)
      (fun j st _ _ hInv => hInv.2.2.2.2.2.2.1)
      (fun j st _ _ hInv => by simp [Expr.eval, hInv.1]) ?_
    intro j _ hj_lt st ω' ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hm0, hm1, hat, hfr⟩
    have hj_ltw : j < 2 ^ w := by omega
    have hjT : j < jTails.length := hLenT ▸ hj_lt
    have hjH : j < jHeads.length := hLenH ▸ hj_lt
    have heJ : jEs[j] ∈ J.E := by
      have hm : jEs[j] ∈ vertsOf J.E := hjE ▸ List.getElem_mem hj_lt
      rwa [mem_vertsOf] at hm
    have hgetT : jTails[j] = jTails.getD j 0 := (List.getD_eq_getElem _ _ hjT).symm
    have hgetH : jHeads[j] = jHeads.getD j 0 := (List.getD_eq_getElem _ _ hjH).symm
    have htail_memV : jTails[j] ∈ jVs := by
      rw [hgetT, (hTH j hj_lt).1, hjV, mem_vertsOf]; exact (hJ _ heJ).1
    have hhead_memV : jHeads[j] ∈ jVs := by
      rw [hgetH, (hTH j hj_lt).2, hjV, mem_vertsOf]; exact (hJ _ heJ).2
    have htail_ltw : jTails[j] < 2 ^ w := hVw _ htail_memV
    have hhead_ltw : jHeads[j] < 2 ^ w := hVw _ hhead_memV
    have hVAt_cur : ListAt st.mem jVsPtr jVs := by
      intro t ht
      rw [hfr _ (by rcases hdisjV t ht with h | h <;> [left; right] <;> omega)]
      exact hVAt t ht
    have hT_mem : st.mem (jTailsPtr + j) = jTails[j] := by
      rw [hfr _ (by rcases hdisjT j hj_lt with h | h <;> [left; right] <;> omega)]
      exact hTAt j hjT
    have hH_mem : st.mem (jHeadsPtr + j) = jHeads[j] := by
      rw [hfr _ (by rcases hdisjH j hj_lt with h | h <;> [left; right] <;> omega)]
      exact hHAt j hjH
    have hwordsT : ∀ v ∈ [jVsPtr, jVs.length, jTails[j]], v < 2 ^ w := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv; · omega
      rcases List.mem_cons.mp hv with rfl | hv; · exact hlt_nJ
      rcases List.mem_cons.mp hv with rfl | hv; · exact htail_ltw
      cases hv
    have hwordsH : ∀ v ∈ [jVsPtr, jVs.length, jHeads[j]], v < 2 ^ w := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv; · omega
      rcases List.mem_cons.mp hv with rfl | hv; · exact hlt_nJ
      rcases List.mem_cons.mp hv with rfl | hv; · exact hhead_ltw
      cases hv
    have h2j_lt : 2 * j < 2 ^ w := by omega
    have h22j_lt : 2 + 2 * j < 2 ^ w := by omega
    have h32j_lt : 3 + 2 * j < 2 ^ w := by omega
    have ha1_lt : outPtr + (2 + 2 * j) < 2 ^ w := by omega
    have ha2_lt : outPtr + (3 + 2 * j) < 2 ^ w := by omega
    refine runs_start_le ?_
    dsimp only [body]
    refine runs_seq_assign_le
      (Expr.eval_load_of_eq (v := jTails[j])
        (by simp [Expr.eval, BinOp.eval, hr3, hr6, show jTailsPtr + j < 2 ^ w by omega]) hT_mem) ?_
    have hpre1 : (binSearchContract w jVs jTails[j]).pre [jVsPtr, jVs.length, jTails[j]] st.mem :=
      ⟨jVsPtr, rfl, hw16, hjVB, hjVPair, htail_memV, hVAt_cur, hVw⟩
    refine runs_seq_call_le (binSearch_meetsContract hpSort)
      (by simp [evalArgs, Expr.eval, Function.update_of_ne, hr1, hr2])
      hwordsT hpre1 ?_
    rintro idxT mem1 _ ⟨_, _, heq1, hidxT, hidxT_lt⟩
    subst heq1
    have hidxT_ltw : idxT < 2 ^ w := by omega
    refine runs_seq_store_le (x := outPtr + (2 + 2 * j)) (v := idxT)
      (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, hr5, hr6, h2_lt, h2j_lt, h22j_lt,
        ha1_lt])
      (by eval_expr) ?_
    have hH_mem1 : (Function.update st.mem (outPtr + (2 + 2 * j)) idxT) (jHeadsPtr + j) = jHeads[j] := by
      have hne : jHeadsPtr + j ≠ outPtr + (2 + 2 * j) := by
        rcases hdisjH j hj_lt with h | h <;> omega
      rw [Function.update_of_ne hne, hH_mem]
    refine runs_seq_assign_le
      (Expr.eval_load_of_eq (v := jHeads[j])
        (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, hr4, hr6,
          show jHeadsPtr + j < 2 ^ w by omega]) hH_mem1) ?_
    have hVAt1 : ListAt (Function.update st.mem (outPtr + (2 + 2 * j)) idxT) jVsPtr jVs := by
      intro t ht
      have hne : jVsPtr + t ≠ outPtr + (2 + 2 * j) := by
        rcases hdisjV t ht with h | h <;> omega
      rw [Function.update_of_ne hne, hVAt_cur t ht]
    have hpre2 : (binSearchContract w jVs jHeads[j]).pre [jVsPtr, jVs.length, jHeads[j]]
        (Function.update st.mem (outPtr + (2 + 2 * j)) idxT) :=
      ⟨jVsPtr, rfl, hw16, hjVB, hjVPair, hhead_memV, hVAt1, hVw⟩
    refine runs_seq_call_le (binSearch_meetsContract hpSort)
      (by simp [evalArgs, Expr.eval, Function.update_of_ne, hr1, hr2])
      hwordsH hpre2 ?_
    rintro idxH mem2 _ ⟨_, _, heq2, hidxH, hidxH_lt⟩
    subst heq2
    have hidxH_ltw : idxH < 2 ^ w := by omega
    refine runs_store_le (x := outPtr + (3 + 2 * j)) (v := idxH)
      (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, hr5, hr6, h2_lt, h3_lt,
        h2j_lt, h32j_lt, ha2_lt])
      (by eval_expr) ?_
      (by dsimp only [binSearchContract, argsSize, Expr.size, stepC]; omega)
    have hpref_succ : prefP (j + 1) = prefP j ++ [idxT, idxH] := by
      dsimp only [prefP, pairOf]
      rw [List.range_succ, List.flatMap_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
        ← hgetT, ← hgetH, hidxT, hidxH]
    refine ⟨⟨by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3], by simp [hr4],
      by simp [hr5], by simp, ?_, ?_, ?_, ?_⟩, hr6⟩
    · dsimp only
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hm0]
    · dsimp only
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hm1]
    · rw [hpref_succ]
      have hat1 : ListAt (Function.update st.mem (outPtr + (2 + 2 * j)) idxT) (outPtr + 2)
          (prefP j) :=
        ListAt.update_ge hat (by rw [hprefP_len]; omega)
      have hat2 : ListAt (Function.update (Function.update st.mem (outPtr + (2 + 2 * j)) idxT)
          (outPtr + (3 + 2 * j)) idxH) (outPtr + 2) (prefP j) :=
        ListAt.update_ge hat1 (by rw [hprefP_len]; omega)
      refine listAt_append.mpr ⟨hat2, fun u hu => ?_⟩
      simp only [List.length_cons, List.length_nil] at hu
      rcases (by omega : u = 0 ∨ u = 1) with rfl | rfl
      · rw [hprefP_len]
        dsimp only
        rw [Nat.add_zero, Function.update_of_ne (by omega),
          show outPtr + 2 + 2 * j = outPtr + (2 + 2 * j) by omega, Function.update_self]
        rfl
      · rw [hprefP_len]
        dsimp only
        rw [show outPtr + 2 + 2 * j + 1 = outPtr + (3 + 2 * j) by omega, Function.update_self]
        rfl
    · intro addr had
      dsimp only
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hfr addr (by omega)
  refine runs_seq_triple_le hloop
    ⟨by simp [startState], by simp [startState], by simp [startState], by simp [startState],
     by simp [startState], by simp [startState],
     by simp [Function.update_of_ne], by simp, by simp [prefP, listAt_nil],
     fun addr had => by
       dsimp only
       rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
       rfl⟩ ?_
  intro st' ⟨hr0', _, _, _, _, _, _, hm0', hm1', hat', hfr'⟩
  refine runs_ret_le (v := 2 + 2 * jEs.length)
    (by simp [Expr.eval, BinOp.eval, hr0', h2_lt, show 2 * jEs.length < 2 ^ w by omega,
      show 2 + 2 * jEs.length < 2 ^ w by omega])
    ⟨jVsPtr, jTailsPtr, jHeadsPtr, outPtr, rfl, rfl, ?_, ?_⟩ ?_
  · have hEnc := toCitedJ_encode_steps J jVs jEs jTails jHeads hjV hjE hLenT hLenH
      (fun j hj => (List.getD_eq_getElem jTails 0 (hLenT ▸ hj)).symm.trans (hTH j hj).1)
      (fun j hj => (List.getD_eq_getElem jHeads 0 (hLenH ▸ hj)).symm.trans (hTH j hj).2)
    change ListAt st'.mem outPtr (toCitedJ J).encode
    rw [hEnc, listAt_cons, listAt_cons]
    exact ⟨hm0', hm1', hat'⟩
  · intro addr had; exact hfr' addr had
  · have hmul : jEs.length * (stepC + 1 + 8) =
        100 * jEs.length * (Nat.log 2 (jVs.length + 1) + 1) + 84 * jEs.length := by
      dsimp only [stepC]; ring
    dsimp only [gtEmitCitedJContract, Expr.size]
    rw [hmul]; omega

theorem gtEmitCitedH_meetsContract {w vCap eCap : ℕ} {p : Program} {b bSort bOps bGT : ℕ}
    {H' J : MGraph} {emb : MinCostFlow.Embedding} {jVs exVs hEs : List ℕ}
    (hp : p.HasAt b (gtEmitProcs bSort bOps bGT))
    (hpOps : p.HasAt bOps dgOpsProcs)
    (hpGT : p.HasAt bGT (gtProcs bSort bOps))
    (hpSort : p.HasAt bSort (sortProcs bSort)) :
    MeetsContract w p (b + gtIdxEmitCitedH)
      (gtEmitCitedHContract w vCap eCap H' J emb jVs exVs hEs) := by
  refine meetsContract_of_runs (hp.get (i := gtIdxEmitCitedH) (by simp [gtEmitProcs, gtIdxEmitCitedH]))
    fun args mem pos _ hargs hpre => ?_
  rcases hpre with ⟨hPtr, exVsPtr, hEsPtr, jVsPtr, outPtr, rfl, hw16, hhB, hjB, hexB, hhEB,
    houtB, hnHB, hdisjH, hdisjJ, hdisjEx, hdisjHE, hDynH, hjV, hexV, hhE, hjAt, hexAt, hhEAt,
    hhEinH, hjw, hexw, hhew, hEndUsed⟩
  have hlt_hP : hPtr < 2 ^ w := hargs hPtr (by simp)
  have hlt_nJ : jVs.length < 2 ^ w := hargs jVs.length (by simp)
  have hlt_exP : exVsPtr < 2 ^ w := hargs exVsPtr (by simp)
  have hlt_nEx : exVs.length < 2 ^ w := hargs exVs.length (by simp)
  have hlt_hEP : hEsPtr < 2 ^ w := hargs hEsPtr (by simp)
  have hlt_mH : hEs.length < 2 ^ w := hargs hEs.length (by simp)
  have hlt_jP : jVsPtr < 2 ^ w := hargs jVsPtr (by simp)
  have hlt_out : outPtr < 2 ^ w := hargs outPtr (by simp)
  have h0_lt : (0 : ℕ) < 2 ^ w := by omega
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have h2_lt : (2 : ℕ) < 2 ^ w := by omega
  have h3_lt : (3 : ℕ) < 2 ^ w := by omega
  have hjPair : jVs.Pairwise (· < ·) := hjV ▸ vertsOf_pairwise_lt J.V
  have hexPair : exVs.Pairwise (· < ·) := hexV ▸ vertsOf_pairwise_lt (usedHVerts H' J emb \ J.V)
  have hdisj_vex : ∀ x ∈ jVs, x ∉ exVs := fun x hx1 hx2 => by
    rw [hjV, mem_vertsOf] at hx1
    rw [hexV, mem_vertsOf] at hx2
    exact (Finset.mem_sdiff.mp hx2).2 hx1
  let pairH : ℕ → List ℕ := fun i =>
    [(jVs ++ exVs).idxOf (H'.tail (hEs.getD i 0)), (jVs ++ exVs).idxOf (H'.head (hEs.getD i 0))]
  let prefH : ℕ → List ℕ := fun i => (List.range i).flatMap pairH
  have hprefH_len : ∀ i, (prefH i).length = 2 * i := by
    intro i
    induction i with
    | zero => simp [prefH]
    | succ i ih =>
      simp only [prefH, pairH, List.range_succ, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.length_append, List.length_cons,
        List.length_nil] at ih ⊢
      omega
  refine runs_start_le ?_
  dsimp only [gtEmitProcs, gtIdxEmitCitedH, List.getElem_cons_succ, List.getElem_cons_zero,
    gtEmitCitedHStmt]
  refine runs_seq_store_le (x := outPtr) (v := jVs.length + exVs.length)
    (by simp [Expr.eval, startState])
    (by simp [Expr.eval, BinOp.eval, startState, hnHB]) ?_
  refine runs_seq_store_le (x := outPtr + 1) (v := hEs.length)
    (by simp [Expr.eval, BinOp.eval, startState, h1_lt, show outPtr + 1 < 2 ^ w by omega])
    (by eval_expr) ?_
  let body : Stmt :=
    .assign 9 (.load (.bin .add (.reg 4) (.reg 8))) ;;
    .call 10 (bOps + dgIdxGetTail) [.reg 0, .reg 9] ;;
    .call 11 (bGT + gtIdxLookupHVert) [.reg 6, .reg 1, .reg 2, .reg 3, .reg 10] ;;
    .store (.bin .add (.reg 7) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 8)))) (.reg 11) ;;
    .call 10 (bOps + dgIdxGetHead) [.reg 0, .reg 9] ;;
    .call 11 (bGT + gtIdxLookupHVert) [.reg 6, .reg 1, .reg 2, .reg 3, .reg 10] ;;
    .store (.bin .add (.reg 7) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 8)))) (.reg 11)
  let InvPre : State → Prop := fun st =>
    st.regs 0 = hPtr ∧ st.regs 1 = jVs.length ∧ st.regs 2 = exVsPtr ∧
    st.regs 3 = exVs.length ∧ st.regs 4 = hEsPtr ∧ st.regs 5 = hEs.length ∧
    st.regs 6 = jVsPtr ∧ st.regs 7 = outPtr ∧
    st.mem outPtr = jVs.length + exVs.length ∧ st.mem (outPtr + 1) = hEs.length ∧
    ListAt st.mem (outPtr + 2) (prefH 0) ∧
    ∀ addr, addr < outPtr ∨ outPtr + 2 ≤ addr → st.mem addr = mem addr
  let Inv : ℕ → State → Prop := fun i st =>
    st.regs 0 = hPtr ∧ st.regs 1 = jVs.length ∧ st.regs 2 = exVsPtr ∧
    st.regs 3 = exVs.length ∧ st.regs 4 = hEsPtr ∧ st.regs 5 = hEs.length ∧
    st.regs 6 = jVsPtr ∧ st.regs 7 = outPtr ∧ st.regs 8 = i ∧
    st.mem outPtr = jVs.length + exVs.length ∧ st.mem (outPtr + 1) = hEs.length ∧
    ListAt st.mem (outPtr + 2) (prefH i) ∧
    ∀ addr, addr < outPtr ∨ outPtr + (2 + 2 * i) ≤ addr → st.mem addr = mem addr
  let stepC := 200 * (Nat.log 2 (jVs.length + exVs.length + 1) + 1) + 320
  have hloop : Triple w p InvPre (forRange 8 (.const 0) (.reg 5) body)
      (normalPost (Inv hEs.length))
      (fun _ => hEs.length * (stepC + Expr.size (.reg 5) + 8) +
        (Expr.size (.const 0) + Expr.size (.reg 5) + 5)) := by
    refine Triple.forRange_const stepC 0 hEs.length (Nat.zero_le _) h1_lt (fun _ => hlt_mH)
      (fun st hInv => ⟨by simp [Expr.eval, h0_lt], by
        rcases hInv with ⟨r0, r1, r2, r3, r4, r5, r6, r7, hm0, hm1, hat, hfr⟩
        exact ⟨by simpa [Function.update_of_ne] using r0, by simpa [Function.update_of_ne] using r1,
          by simpa [Function.update_of_ne] using r2, by simpa [Function.update_of_ne] using r3,
          by simpa [Function.update_of_ne] using r4, by simpa [Function.update_of_ne] using r5,
          by simpa [Function.update_of_ne] using r6, by simpa [Function.update_of_ne] using r7,
          by simp, hm0, hm1, hat, by simpa using hfr⟩⟩)
      (fun i st _ _ hInv => hInv.2.2.2.2.2.2.2.2.1)
      (fun i st _ _ hInv => by simp [Expr.eval, hInv.2.2.2.2.2.1]) ?_
    intro i _ hi_lt st ω' ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hm0, hm1, hat, hfr⟩
    have hi_ltw : i < 2 ^ w := by omega
    have he_mem : hEs[i] ∈ usedHEdges J emb := by
      have hm : hEs[i] ∈ vertsOf (usedHEdges J emb) := hhE ▸ List.getElem_mem hi_lt
      rwa [mem_vertsOf] at hm
    have he_H : hEs[i] ∈ H'.E := hhEinH _ he_mem
    have he_ltw : hEs[i] < 2 ^ w := hhew _ (List.getElem_mem hi_lt)
    have hEnds := hEndUsed _ he_mem
    have ht_mem : H'.tail hEs[i] ∈ jVs ++ exVs := by
      have : H'.tail hEs[i] ∈ usedHVerts H' J emb := hEnds.1
      by_cases hJ : H'.tail hEs[i] ∈ J.V
      · exact List.mem_append_left _ (hjV ▸ mem_vertsOf.mpr hJ)
      · exact List.mem_append_right _ (hexV ▸ mem_vertsOf.mpr (Finset.mem_sdiff.mpr ⟨this, hJ⟩))
    have hh_mem : H'.head hEs[i] ∈ jVs ++ exVs := by
      have : H'.head hEs[i] ∈ usedHVerts H' J emb := hEnds.2
      by_cases hJ : H'.head hEs[i] ∈ J.V
      · exact List.mem_append_left _ (hjV ▸ mem_vertsOf.mpr hJ)
      · exact List.mem_append_right _ (hexV ▸ mem_vertsOf.mpr (Finset.mem_sdiff.mpr ⟨this, hJ⟩))
    have ht_ltw : H'.tail hEs[i] < 2 ^ w := by
      rcases List.mem_append.mp ht_mem with h | h
      · exact hjw _ h
      · exact hexw _ h
    have hh_ltw : H'.head hEs[i] < 2 ^ w := by
      rcases List.mem_append.mp hh_mem with h | h
      · exact hjw _ h
      · exact hexw _ h
    have hDyn_cur : DynGraphAt st.mem hPtr vCap eCap H' := by
      refine hDynH.of_agree ?_
      intro k hk1 hk2
      rw [hfr _ (by rcases hdisjH (k - hPtr) (by omega) with h | h <;> [left; right] <;> omega)]
    have hjAt_cur : ListAt st.mem jVsPtr jVs := fun t ht => by
      rw [hfr _ (by rcases hdisjJ t ht with h | h <;> [left; right] <;> omega)]
      exact hjAt t ht
    have hexAt_cur : ListAt st.mem exVsPtr exVs := fun t ht => by
      rw [hfr _ (by rcases hdisjEx t ht with h | h <;> [left; right] <;> omega)]
      exact hexAt t ht
    have he_val : st.mem (hEsPtr + i) = hEs[i] := by
      rw [hfr _ (by rcases hdisjHE i hi_lt with h | h <;> [left; right] <;> omega)]
      exact hhEAt i hi_lt
    have h2i_lt : 2 * i < 2 ^ w := by omega
    have h22i_lt : 2 + 2 * i < 2 ^ w := by omega
    have h32i_lt : 3 + 2 * i < 2 ^ w := by omega
    have ha1_lt : outPtr + (2 + 2 * i) < 2 ^ w := by omega
    have ha2_lt : outPtr + (3 + 2 * i) < 2 ^ w := by omega
    refine runs_start_le ?_
    dsimp only [body]
    refine runs_seq_assign_le
      (Expr.eval_load_of_eq (v := hEs[i])
        (by simp [Expr.eval, BinOp.eval, hr4, hr8, show hEsPtr + i < 2 ^ w by omega]) he_val) ?_
    have hwe : ∀ v ∈ [hPtr, hEs[i]], v < 2 ^ w := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv; · exact hlt_hP
      rcases List.mem_cons.mp hv with rfl | hv; · exact he_ltw
      cases hv
    have hpreT : (dgGetTailContract w vCap eCap H').pre [hPtr, hEs[i]] st.mem :=
      ⟨hPtr, hEs[i], rfl, hw16, hhB, he_H, hDyn_cur⟩
    refine runs_seq_call_le (dgGetTail_meetsContract hpOps)
      (by simp [evalArgs, Expr.eval, Function.update_of_ne, hr0])
      hwe hpreT ?_
    rintro tailV mem1 _ ⟨_, _, heq1, hmem1, htailV⟩
    subst hmem1
    simp only [List.cons.injEq, and_true] at heq1
    have htailV' : tailV = H'.tail hEs[i] := by rw [← heq1.2] at htailV; exact htailV
    have hwtV : ∀ v ∈ [jVsPtr, jVs.length, exVsPtr, exVs.length, tailV], v < 2 ^ w := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv; · exact hlt_jP
      rcases List.mem_cons.mp hv with rfl | hv; · exact hlt_nJ
      rcases List.mem_cons.mp hv with rfl | hv; · exact hlt_exP
      rcases List.mem_cons.mp hv with rfl | hv; · exact hlt_nEx
      rcases List.mem_cons.mp hv with rfl | hv; · exact htailV' ▸ ht_ltw
      cases hv
    have hpreLT : (gtLookupHVertContract w jVs exVs tailV).pre
        [jVsPtr, jVs.length, exVsPtr, exVs.length, tailV] st.mem :=
      ⟨jVsPtr, exVsPtr, rfl, hw16, hjB, hexB, htailV' ▸ ht_ltw, hnHB,
       hjPair, hexPair, hdisj_vex, htailV' ▸ ht_mem, hjAt_cur, hexAt_cur, hjw, hexw⟩
    refine runs_seq_call_le (gtLookupHVert_meetsContract hpGT hpSort)
      (by simp [evalArgs, Expr.eval, Function.update_of_ne, hr6, hr1, hr2, hr3])
      hwtV hpreLT ?_
    rintro idxT mem2 _ ⟨_, _, heq2, hmem2, hidxT, hidxT_lt⟩
    subst hmem2
    have hidxT_ltw : idxT < 2 ^ w := by omega
    refine runs_seq_store_le (x := outPtr + (2 + 2 * i)) (v := idxT)
      (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, hr7, hr8, h2_lt, h2i_lt,
        h22i_lt, ha1_lt])
      (by eval_expr) ?_
    let memU := Function.update st.mem (outPtr + (2 + 2 * i)) idxT
    have hDyn1 : DynGraphAt memU hPtr vCap eCap H' := by
      refine hDyn_cur.of_agree ?_
      intro k hk1 hk2
      have hne : k ≠ outPtr + (2 + 2 * i) := by
        rcases hdisjH (k - hPtr) (by omega) with h | h <;> omega
      exact Function.update_of_ne hne _ _
    have hpreH : (dgGetHeadContract w vCap eCap H').pre [hPtr, hEs[i]] memU :=
      ⟨hPtr, hEs[i], rfl, hw16, hhB, he_H, hDyn1⟩
    refine runs_seq_call_le (dgGetHead_meetsContract hpOps)
      (by simp [evalArgs, Expr.eval, Function.update_of_ne, hr0])
      hwe hpreH ?_
    rintro headV mem3 _ ⟨_, _, heq3, hmem3, hheadV⟩
    subst hmem3
    simp only [List.cons.injEq, and_true] at heq3
    have hheadV' : headV = H'.head hEs[i] := by rw [← heq3.2] at hheadV; exact hheadV
    have hwhV : ∀ v ∈ [jVsPtr, jVs.length, exVsPtr, exVs.length, headV], v < 2 ^ w := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv; · exact hlt_jP
      rcases List.mem_cons.mp hv with rfl | hv; · exact hlt_nJ
      rcases List.mem_cons.mp hv with rfl | hv; · exact hlt_exP
      rcases List.mem_cons.mp hv with rfl | hv; · exact hlt_nEx
      rcases List.mem_cons.mp hv with rfl | hv; · exact hheadV' ▸ hh_ltw
      cases hv
    have hjAt1 : ListAt memU jVsPtr jVs := fun t ht => by
      have hne : jVsPtr + t ≠ outPtr + (2 + 2 * i) := by
        rcases hdisjJ t ht with h | h <;> omega
      dsimp only [memU]; rw [Function.update_of_ne hne]; exact hjAt_cur t ht
    have hexAt1 : ListAt memU exVsPtr exVs := fun t ht => by
      have hne : exVsPtr + t ≠ outPtr + (2 + 2 * i) := by
        rcases hdisjEx t ht with h | h <;> omega
      dsimp only [memU]; rw [Function.update_of_ne hne]; exact hexAt_cur t ht
    have hpreLH : (gtLookupHVertContract w jVs exVs headV).pre
        [jVsPtr, jVs.length, exVsPtr, exVs.length, headV] memU :=
      ⟨jVsPtr, exVsPtr, rfl, hw16, hjB, hexB, hheadV' ▸ hh_ltw, hnHB,
       hjPair, hexPair, hdisj_vex, hheadV' ▸ hh_mem, hjAt1, hexAt1, hjw, hexw⟩
    refine runs_seq_call_le (gtLookupHVert_meetsContract hpGT hpSort)
      (by simp [evalArgs, Expr.eval, Function.update_of_ne, hr6, hr1, hr2, hr3])
      hwhV hpreLH ?_
    rintro idxH mem4 _ ⟨_, _, heq4, hmem4, hidxH, hidxH_lt⟩
    subst hmem4
    have hidxH_ltw : idxH < 2 ^ w := by omega
    refine runs_store_le (x := outPtr + (3 + 2 * i)) (v := idxH)
      (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, hr7, hr8, h2_lt, h3_lt,
        h2i_lt, h32i_lt, ha2_lt])
      (by eval_expr) ?_
      (by dsimp only [dgGetTailContract, dgGetHeadContract, gtLookupHVertContract,
        argsSize, Expr.size, stepC]; omega)
    have hpref_succ : prefH (i + 1) = prefH i ++ [idxT, idxH] := by
      dsimp only [prefH, pairH]
      rw [List.range_succ, List.flatMap_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.getD_eq_getElem _ _ hi_lt, hidxT, hidxH, htailV', hheadV']
    refine ⟨⟨by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3], by simp [hr4],
      by simp [hr5], by simp [hr6], by simp [hr7], by simp, ?_, ?_, ?_, ?_⟩, hr8⟩
    · dsimp only [memU]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hm0]
    · dsimp only [memU]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hm1]
    · rw [hpref_succ]
      have hat1 : ListAt memU (outPtr + 2) (prefH i) :=
        ListAt.update_ge hat (by rw [hprefH_len]; omega)
      have hat2 : ListAt (Function.update memU (outPtr + (3 + 2 * i)) idxH)
          (outPtr + 2) (prefH i) :=
        ListAt.update_ge hat1 (by rw [hprefH_len]; omega)
      refine listAt_append.mpr ⟨hat2, fun u hu => ?_⟩
      simp only [List.length_cons, List.length_nil] at hu
      rcases (by omega : u = 0 ∨ u = 1) with rfl | rfl
      · rw [hprefH_len]; dsimp only [memU]
        rw [Nat.add_zero, Function.update_of_ne (by omega),
          show outPtr + 2 + 2 * i = outPtr + (2 + 2 * i) by omega, Function.update_self]
        rfl
      · rw [hprefH_len]; dsimp only [memU]
        rw [show outPtr + 2 + 2 * i + 1 = outPtr + (3 + 2 * i) by omega, Function.update_self]
        rfl
    · intro addr had
      dsimp only [memU]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hfr addr (by omega)
  refine runs_seq_triple_le hloop
    ⟨by simp [startState], by simp [startState], by simp [startState], by simp [startState],
     by simp [startState], by simp [startState], by simp [startState], by simp [startState],
     by simp [Function.update_of_ne], by simp, by simp [prefH, listAt_nil],
     fun addr had => by
       dsimp only
       rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
       rfl⟩ ?_
  intro st' ⟨_, _, _, _, _, hr5', _, _, _, hm0', hm1', hat', hfr'⟩
  refine runs_ret_le (v := 2 + 2 * hEs.length)
    (by simp [Expr.eval, BinOp.eval, hr5', h2_lt, show 2 * hEs.length < 2 ^ w by omega,
      show 2 + 2 * hEs.length < 2 ^ w by omega])
    ⟨hPtr, exVsPtr, hEsPtr, jVsPtr, outPtr, rfl, rfl, ?_, ?_⟩ ?_
  · have hEnc := toCitedH_encode_steps H' J emb jVs exVs hEs hjV hexV hhE
    change ListAt st'.mem outPtr (toCitedH H' J emb).encode
    rw [hEnc, listAt_cons, listAt_cons]
    exact ⟨hm0', hm1', hat'⟩
  · intro addr had; exact hfr' addr had
  · have hmul : hEs.length * (stepC + 1 + 8) =
        200 * hEs.length * (Nat.log 2 (jVs.length + exVs.length + 1) + 1) + 329 * hEs.length := by
      dsimp only [stepC]; ring
    dsimp only [gtEmitCitedHContract, Expr.size]
    rw [hmul]; omega

end

end MinCostFlow.DynSpanner.Program
