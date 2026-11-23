module

public import MinCostFlow.SparseCore.Program.AssemblyFirstSplitModel
public import MinCostFlow.SparseCore.Program.AssemblyFirstCharge
public import MinCostFlow.SparseCore.Program.OrdEditsBlocks
public import MinCostFlow.SparseCore.Program.OutStepSpec
public import MinCostFlow.SparseCore.Program.AssemblyStatement
import all MinCostFlow.SparseCore.Program.AssemblyFirstSplitLists

/-!
# The tour mark-block interface and block-by-block edits for `Σ |Y|` (`AssemblyFirstTourMarks`)

During the first phase of a branch step, P2's tour applies the input order edits `ed` block by
block alongside the updates of the input batch `U` (`OrdEditsForBatch`, `OrdEditsBlocks.lean`),
interleaved with the forest cuts and links of `canonStepCore`, calling P7's helper `outSmallSide`
after each core split.

This file formalizes the bridge between P2's tour, `OrdEditsForBatch`, and the model split-list
bound `outCutLens_sum_le_enc` (`AssemblyFirstSplitModel.lean`):

* **Block decomposition of `OrdEditsForBatch`**: `editBlockAt U ed i` and `editRotBlock U ed`
  split `ed` into one block per update of `U` followed by the trailing `rotateTo` block
  (`editBlocks_concat`, `applyOrdEdits_blocks`), with each block matching its update
  (`editBlockAt_delete`, `editBlockAt_split`, `editBlockAt_insert`).
* **Model mark-block lemma** (`outMarksOf_markedList_eq_markBlock`): whenever the tour holds
  `OutMarksOf s (coreRotation ρ hG hF).order M` with `M ⊆ (coreGraph G L).E`, the marked list
  `s.markedList r` at every vertex `r` is duplicate-free and has underlying set
  `markBlock M (coreGraph G L) r`. Consequently, `outSmallSide` at a core split `(v, v')` returns
  a duplicate-free list `Y` matching the smaller of `markBlock M C' v` and `markBlock M C' v'`
  (`outSmallSide_matches_markBlock`).
* **Named interface** `TourSplitMarksMatch`: states that across all splits of a core batch `UC`,
  the lists `Ys` produced by `outSmallSide` match the smaller `markBlock` set at each split. It
  composes across concatenated batches (`tourSplitMarksMatch_append`), fixes the list lengths to
  `cutLens M C UC` (`tourSplitMarksMatch_lengths`), and yields the exact `Σ |Y|` bound of
  `AsmBrCoreStepAt` (`tourSplitMarksMatch_sum_le_capExp`).
* **Block-by-block tour driver interface** `AsmFirstTourBlockStepAt`: states what P2's tour
  step does (using `OrdEditsForBatch`, P4's `CompSplitListAt`, and `outSmallSide`). The procedures
  of `AssemblyFirstTourStepProg.lean` implement it.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

/-! ## Block decomposition of `OrdEditsForBatch` -/

@[expose] public section

/-- The `i`-th update block of `ed` for batch `U`: starts at `batchEditBlocksLen (U.take i)` and
has length `updateEditBlockLen (U.getD i (.delete 0))`. -/
def editBlockAt (U : List Update) (ed : List OrdEdit) (i : ℕ) : List OrdEdit :=
  (ed.drop (batchEditBlocksLen (U.take i))).take (updateEditBlockLen (U.getD i (.delete 0)))

/-- The trailing `rotateTo` block of `ed` after all update blocks of `U`. -/
def editRotBlock (U : List Update) (ed : List OrdEdit) : List OrdEdit :=
  ed.drop (batchEditBlocksLen U)

/-- **Named interface for `Σ |Y|`**: across a core batch `UC` on core graph `C` with initial marked
edges `M`, the split lists `Ys` produced by `outSmallSide` match the smaller of the two
`markBlock` sets at each core split (deletions remove their edge from `M`; insertions add no
mark). -/
def TourSplitMarksMatch : Finset ℕ → MGraph → List Update → List (List End) → Prop
  | _, _, [], Ys => Ys = []
  | M, C, .insert e a b :: UC, Ys =>
      TourSplitMarksMatch M (C.applyUpdate (.insert e a b)) UC Ys
  | M, C, .delete e :: UC, Ys =>
      TourSplitMarksMatch (M.erase e) (C.applyUpdate (.delete e)) UC Ys
  | M, C, .split v v' St Sh :: UC, Y :: Ys =>
      let C' := C.applyUpdate (.split v v' St Sh)
      Y.Nodup ∧
      ((Y.toFinset = markBlock M C' v ∧
          (markBlock M C' v).card ≤ (markBlock M C' v').card) ∨
       (Y.toFinset = markBlock M C' v' ∧
          (markBlock M C' v').card ≤ (markBlock M C' v).card)) ∧
      TourSplitMarksMatch M C' UC Ys
  | _, _, .split _ _ _ _ :: _, [] => False

/-- **Interface for P2's block-by-block tour step**: given `OrdEditsForBatch tr.cs.G U ed`,
the tour applies each update block `editBlockAt U ed i` together with the forest cuts and
`outSmallSide` calls of `canonStepCore`, then applies `editRotBlock U ed`, leaving the new core
lists `outCoreOrder info.state ord'`, marks `E₀` between `outKeep` and `tr.S_cur.E`, and split
records `OutSplitListsAt` whose lists `Ys` meet `TourSplitMarksMatch`. -/
structure AsmFirstTourBlockStepAt {OS : OutTourSpec} {w : ℕ} {p : Program} {nm sm fm lm : ℕ}
    (TT : (vCap eCap : ℕ) → OutTourAt OS w vCap eCap p nm sm fm lm)
    (impl : SparsifyImpl) (depth : ℕ) (fTourStep : ℕ) where
  mul : ℕ
  space : ℕ → ℕ
  space_mono : Monotone space
  runs : ∀ (vCap eCap tourH batch words edits editWords splitListPtr h : ℕ)
      (tr : BundleTreeState depth) (ord : ℕ → List End) (sTour : OutTourAbs)
      (tx : (TT vCap eCap).rep.τ) (U : List Update) (ed : List OrdEdit)
      (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      let ord' := applyOrdEdits ord ed
      let sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut := fun _ => canonicalSparsify impl
      let info := stepBundleTree sp tr U ord ord'
      OutStepReady sp tr U ord ord' →
      OrdEditsForBatch tr.cs.G U ed →
      OrdEditsValidFor vCap eCap ord ed →
      OutMarksOf sTour (outCoreOrder tr ord) tr.S_cur.E →
      (TT vCap eCap).rep.rep tourH sTour tx mem →
      (∀ a, (TT vCap eCap).rep.foot tourH tx a → a < h) →
      ZeroFrom mem h →
      h + space (vCap + eCap + words + editWords) < 2 ^ w →
      ∃ body, p.procs[fTourStep]? = some body ∧
        ∃ o st' c sTour' tx' splitPtr Ys M,
          Runs w p ω body
            (startState [tourH, batch, words, edits, editWords, splitListPtr, h] mem pos)
            o st' c ∧
          (TT vCap eCap).rep.rep tourH sTour' tx' st'.mem ∧
          outKeep sp tr U ord ord' ⊆ M ∧ M ⊆ tr.S_cur.E ∧
          OutMarksOf sTour' (outCoreOrder info.state ord') M ∧
          TourSplitMarksMatch M (coreGraph tr.cs.G tr.cs.lsf) info.U_core Ys ∧
          OutSplitListsAt st'.mem o.value (fun a => (TT vCap eCap).rep.foot tourH tx' a)
            (outKeep sp tr U ord ord') tr.S_cur.E splitPtr
            (tr.S_cur.applyBatch ((outDelList sp tr U ord ord').map Update.delete))
            (restrictSplits (outKeep sp tr U ord ord') info.U_core) Ys ∧
          st'.mem h = splitPtr ∧
          h + 1 ≤ o.value ∧ o.value ≤ h + space (vCap + eCap + words + editWords) ∧
          ZeroFrom st'.mem o.value ∧
          (∀ a < h, ¬ (TT vCap eCap).rep.foot tourH tx a → st'.mem a = mem a) ∧
          (∀ a, (TT vCap eCap).rep.foot tourH tx' a →
            (TT vCap eCap).rep.foot tourH tx a ∨ (h + 1 ≤ a ∧ a < o.value)) ∧
          c + (TT vCap eCap).rep.phi tourH tx' st'.mem ≤
            mul * ((Ys.map List.length).sum + words + editWords + 1) * ordStoreLog eCap +
              (TT vCap eCap).rep.phi tourH tx mem

end

public section

/-! ## Block decomposition lemmas for `OrdEditsForBatch` -/

private lemma flatMap_editBlockAt_eq_take :
    ∀ (U : List Update) (ed : List OrdEdit),
      (List.range U.length).flatMap (editBlockAt U ed) = ed.take (batchEditBlocksLen U)
  | [], _ => by simp [batchEditBlocksLen]
  | u :: U, ed => by
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    have h0 : editBlockAt (u :: U) ed 0 = ed.take (updateEditBlockLen u) := by
      simp [editBlockAt, batchEditBlocksLen]
    have htail : (fun i => editBlockAt (u :: U) ed (i + 1)) =
        editBlockAt U (ed.drop (updateEditBlockLen u)) := by
      funext i
      simp only [editBlockAt, List.take_succ_cons, batchEditBlocksLen_cons, List.drop_drop,
        List.getD_cons_succ, Nat.add_comm (updateEditBlockLen u)]
    rw [h0, htail, flatMap_editBlockAt_eq_take U (ed.drop (updateEditBlockLen u)),
      batchEditBlocksLen_cons, ← List.take_add]

/-- The update blocks `editBlockAt U ed 0, …, editBlockAt U ed (U.length - 1)` followed by the
trailing rotation block `editRotBlock U ed` concatenate to `ed`. -/
theorem editBlocks_concat (U : List Update) (ed : List OrdEdit) :
    (List.range U.length).flatMap (editBlockAt U ed) ++ editRotBlock U ed = ed := by
  rw [flatMap_editBlockAt_eq_take, editRotBlock, List.take_append_drop]

/-- Applying `ed` to `ord` is identical to applying its update blocks in order, followed by the
trailing `rotateTo` block `editRotBlock U ed`. -/
theorem applyOrdEdits_blocks (U : List Update) (ord : ℕ → List End) (ed : List OrdEdit) :
    applyOrdEdits ord ed =
      applyOrdEdits
        ((List.range U.length).foldl (fun o i => applyOrdEdits o (editBlockAt U ed i)) ord)
        (editRotBlock U ed) := by
  have happ : ∀ (o : ℕ → List End) (a b : List OrdEdit),
      applyOrdEdits o (a ++ b) = applyOrdEdits (applyOrdEdits o a) b :=
    fun o a b => List.foldl_append
  have hfold : ∀ (ls : List ℕ) (f : ℕ → List OrdEdit) (o : ℕ → List End),
      applyOrdEdits o (ls.flatMap f) = ls.foldl (fun acc i => applyOrdEdits acc (f i)) o := by
    intro ls f
    induction ls with
    | nil => intro o; rfl
    | cons a as ih =>
      intro o
      simp only [List.flatMap_cons, List.foldl_cons, happ, ih]
  conv_lhs => rw [← editBlocks_concat U ed]
  rw [happ, hfold]

/-- Under `OrdEditsForBatch G U ed`, when `U[i] = .delete e`, block `i` is `[.dropEdge e]`. -/
theorem editBlockAt_delete {G : MGraph} {U : List Update} {ed : List OrdEdit}
    (h : OrdEditsForBatch G U ed) {i e : ℕ} (hi : i < U.length) (hu : U[i]'hi = .delete e) :
    editBlockAt U ed i = [.dropEdge e] := by
  have hdrop := (ordEditsForBatch_split_at U i G ed h).2
  have hdropU : U.drop i = .delete e :: U.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons hi, hu]
  rw [hdropU] at hdrop
  obtain ⟨ed', hed', -⟩ := ordEditsForBatch_delete_iff.mp hdrop
  have hgetD : U.getD i (.delete 0) = .delete e := by
    rw [List.getD_eq_getElem _ _ hi, hu]
  unfold editBlockAt
  rw [hed', hgetD]
  rfl

/-- Under `OrdEditsForBatch G U ed`, when `U[i] = .split v v' St Sh`, block `i` is
`[.moveEnds v v' sel c]` agreeing with `splitEnds St Sh` on `G.applyBatch (U.take i)`. -/
theorem editBlockAt_split {G : MGraph} {U : List Update} {ed : List OrdEdit}
    (h : OrdEditsForBatch G U ed) {i v v' : ℕ} {St Sh : Finset ℕ} (hi : i < U.length)
    (hu : U[i]'hi = .split v v' St Sh) :
    ∃ sel c, editBlockAt U ed i = [.moveEnds v v' sel c] ∧
      ∀ x : End, x.1 ∈ (G.applyBatch (U.take i)).E → (G.applyBatch (U.take i)).src x = v →
        movedBy sel c x = splitEnds St Sh x := by
  have hdrop := (ordEditsForBatch_split_at U i G ed h).2
  have hdropU : U.drop i = .split v v' St Sh :: U.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons hi, hu]
  rw [hdropU] at hdrop
  obtain ⟨sel, c, ed', hed', hmov, -⟩ := ordEditsForBatch_split_iff.mp hdrop
  have hgetD : U.getD i (.delete 0) = .split v v' St Sh := by
    rw [List.getD_eq_getElem _ _ hi, hu]
  refine ⟨sel, c, ?_, hmov⟩
  unfold editBlockAt
  rw [hed', hgetD]
  rfl

/-- Under `OrdEditsForBatch G U ed`, when `U[i] = .insert e a b`, block `i` is
`[.insertBefore a (e, true) y₁, .insertBefore b (e, false) y₂]`. -/
theorem editBlockAt_insert {G : MGraph} {U : List Update} {ed : List OrdEdit}
    (h : OrdEditsForBatch G U ed) {i e a b : ℕ} (hi : i < U.length)
    (hu : U[i]'hi = .insert e a b) :
    ∃ y₁ y₂, editBlockAt U ed i =
      [.insertBefore a (e, true) y₁, .insertBefore b (e, false) y₂] := by
  have hdrop := (ordEditsForBatch_split_at U i G ed h).2
  have hdropU : U.drop i = .insert e a b :: U.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons hi, hu]
  rw [hdropU] at hdrop
  obtain ⟨y₁, y₂, ed', hed', -⟩ := ordEditsForBatch_insert_iff.mp hdrop
  have hgetD : U.getD i (.delete 0) = .insert e a b := by
    rw [List.getD_eq_getElem _ _ hi, hu]
  refine ⟨y₁, y₂, ?_⟩
  unfold editBlockAt
  rw [hed', hgetD]
  rfl

/-- Under `OrdEditsForBatch G U ed`, every edit in `editRotBlock U ed` is a `rotateTo` edit. -/
theorem editRotBlock_isRotate {G : MGraph} {U : List Update} {ed : List OrdEdit}
    (h : OrdEditsForBatch G U ed) : ∀ d ∈ editRotBlock U ed, d.IsRotate :=
  (ordEditsForBatch_take_drop h).2.2

/-! ## Model proof that `OutMarksOf` gives `markBlock` -/

/-- **Model mark-block lemma.** When the tour holds the core rotation lists of `(G, L)` and marks
the edges `M ⊆ (coreGraph G L).E` (`OutMarksOf`), the marked list `s.markedList r` at every vertex
`r` is duplicate-free and has underlying set `markBlock M (coreGraph G L) r`. -/
theorem outMarksOf_markedList_eq_markBlock {G : MGraph} {L : LSF} (ρ : Rotation G)
    (hG : G.IsValid) (hF : L.F.IsRootedSpanningForestOf G) {s : OutTourAbs} {M : Finset ℕ}
    (hMarks : OutMarksOf s (coreRotation (L := L) ρ hG hF).order M)
    (hM : M ⊆ (coreGraph G L).E) (r : ℕ) :
    (s.markedList r).Nodup ∧ (s.markedList r).toFinset = markBlock M (coreGraph G L) r := by
  classical
  set cr := coreRotation (L := L) ρ hG hF
  refine ⟨?_, ?_⟩
  · unfold OutTourAbs.markedList
    rw [hMarks.1]
    exact (cr.nodup r).filter _
  · ext x
    simp only [List.mem_toFinset, OutTourAbs.markedList, List.mem_filter, decide_eq_true_eq,
      mem_markBlock, hMarks.1, hMarks.2, cr.mem_order]
    constructor
    · rintro ⟨⟨_, hsrc⟩, ⟨_, hxM⟩⟩
      exact ⟨hxM, hsrc⟩
    · rintro ⟨hxM, hsrc⟩
      have hxE : x.1 ∈ (coreGraph G L).E := hM hxM
      exact ⟨⟨hxE, hsrc⟩, ⟨⟨r, hxE, hsrc⟩, hxM⟩⟩

/-- **Single-split proof from `OutMarksOf`.** At a core split `(v, v')`, if the post-split tour
holds the post-split core rotation and `OutMarksOf s' _ M` with `M ⊆ C'.E`, then `outSmallSide`'s
chosen list `Y` is duplicate-free and equals the smaller of `markBlock M C' v` and
`markBlock M C' v'`. -/
theorem outSmallSide_matches_markBlock {G' : MGraph} {L' : LSF} (ρ' : Rotation G')
    (hG' : G'.IsValid) (hF' : L'.F.IsRootedSpanningForestOf G') {s' : OutTourAbs} {M : Finset ℕ}
    (hMarks : OutMarksOf s' (coreRotation (L := L') ρ' hG' hF').order M)
    (hM : M ⊆ (coreGraph G' L').E) (v v' : ℕ) :
    let side := if (s'.markedList v).length ≤ (s'.markedList v').length then 0 else 1
    let Y := s'.markedList (if side = 0 then v else v')
    Y.Nodup ∧
      ((Y.toFinset = markBlock M (coreGraph G' L') v ∧
          (markBlock M (coreGraph G' L') v).card ≤ (markBlock M (coreGraph G' L') v').card) ∨
       (Y.toFinset = markBlock M (coreGraph G' L') v' ∧
          (markBlock M (coreGraph G' L') v').card ≤ (markBlock M (coreGraph G' L') v).card)) := by
  intro side Y
  obtain ⟨hndV, hsetV⟩ := outMarksOf_markedList_eq_markBlock ρ' hG' hF' hMarks hM v
  obtain ⟨hndV', hsetV'⟩ := outMarksOf_markedList_eq_markBlock ρ' hG' hF' hMarks hM v'
  have hlenV : (s'.markedList v).length = (markBlock M (coreGraph G' L') v).card := by
    rw [← hsetV, List.toFinset_card_of_nodup hndV]
  have hlenV' : (s'.markedList v').length = (markBlock M (coreGraph G' L') v').card := by
    rw [← hsetV', List.toFinset_card_of_nodup hndV']
  by_cases hle : (s'.markedList v).length ≤ (s'.markedList v').length
  · have hside : side = 0 := ite_eq_left hle
    have hY : Y = s'.markedList v := by dsimp only [Y]; simp [hside]
    rw [hY]
    exact ⟨hndV, Or.inl ⟨hsetV, hlenV ▸ hlenV' ▸ hle⟩⟩
  · have hside : side = 1 := ite_eq_right hle
    have hY : Y = s'.markedList v' := by dsimp only [Y]; simp [hside]
    rw [hY]
    exact ⟨hndV', Or.inr ⟨hsetV', by omega⟩⟩

/-! ## Composition and `Σ |Y|` bound from `TourSplitMarksMatch` -/

/-- `TourSplitMarksMatch` composes across concatenated core batches `UC₁ ++ UC₂` (matching
`canonCoreBatch` concatenated update by update). -/
theorem tourSplitMarksMatch_append :
    ∀ (UC₁ UC₂ : List Update) (M : Finset ℕ) (C : MGraph) (Ys₁ Ys₂ : List (List End)),
      TourSplitMarksMatch M C UC₁ Ys₁ →
      TourSplitMarksMatch (markAfter M UC₁) (C.applyBatch UC₁) UC₂ Ys₂ →
      TourSplitMarksMatch M C (UC₁ ++ UC₂) (Ys₁ ++ Ys₂)
  | [], _, _, _, _, _, rfl, h₂ => by
      simpa [markAfter, MGraph.applyBatch] using h₂
  | .insert e a b :: UC₁, UC₂, M, C, Ys₁, Ys₂, h₁, h₂ => by
      have h₂' : TourSplitMarksMatch (markAfter M UC₁)
          ((C.applyUpdate (.insert e a b)).applyBatch UC₁) UC₂ Ys₂ := by
        simpa [markAfter, MGraph.applyBatch] using h₂
      exact tourSplitMarksMatch_append UC₁ UC₂ M (C.applyUpdate (.insert e a b)) Ys₁ Ys₂ h₁ h₂'
  | .delete e :: UC₁, UC₂, M, C, Ys₁, Ys₂, h₁, h₂ => by
      have h₂' : TourSplitMarksMatch (markAfter (M.erase e) UC₁)
          ((C.applyUpdate (.delete e)).applyBatch UC₁) UC₂ Ys₂ := by
        simpa [markAfter, MGraph.applyBatch] using h₂
      exact tourSplitMarksMatch_append UC₁ UC₂ (M.erase e) (C.applyUpdate (.delete e)) Ys₁ Ys₂ h₁ h₂'
  | .split _ _ _ _ :: _, _, _, _, [], _, h₁, _ => False.elim h₁
  | .split v v' St Sh :: UC₁, UC₂, M, C, Y :: Ys₁, Ys₂, ⟨hnd, hset, hrest⟩, h₂ => by
      have h₂' : TourSplitMarksMatch (markAfter M UC₁)
          ((C.applyUpdate (.split v v' St Sh)).applyBatch UC₁) UC₂ Ys₂ := by
        simpa [markAfter, MGraph.applyBatch] using h₂
      exact ⟨hnd, hset, tourSplitMarksMatch_append UC₁ UC₂ M (C.applyUpdate (.split v v' St Sh))
        Ys₁ Ys₂ hrest h₂'⟩

/-- Under `TourSplitMarksMatch`, the lengths of the split lists `Ys` equal `cutLens M C UC`. -/
theorem tourSplitMarksMatch_lengths :
    ∀ (UC : List Update) (M : Finset ℕ) (C : MGraph) (Ys : List (List End)),
      TourSplitMarksMatch M C UC Ys → Ys.map List.length = cutLens M C UC
  | [], _, _, _, rfl => by simp [cutLens]
  | .insert e a b :: UC, M, C, Ys, h => by
      simpa [cutLens] using
        tourSplitMarksMatch_lengths UC M (C.applyUpdate (.insert e a b)) Ys h
  | .delete e :: UC, M, C, Ys, h => by
      simpa [cutLens] using
        tourSplitMarksMatch_lengths UC (M.erase e) (C.applyUpdate (.delete e)) Ys h
  | .split _ _ _ _ :: _, _, _, [], h => False.elim h
  | .split v v' St Sh :: UC, M, C, Y :: Ys, ⟨hnd, hset, hrest⟩ => by
      simp only [List.map_cons, cutLens, List.cons.injEq]
      refine ⟨?_, tourSplitMarksMatch_lengths UC M (C.applyUpdate (.split v v' St Sh)) Ys hrest⟩
      rw [← List.toFinset_card_of_nodup hnd]
      rcases hset with ⟨heq, hle⟩ | ⟨heq, hle⟩
      · rw [heq, min_eq_left hle]
      · rw [heq, min_eq_right hle]

/-- **The `Σ |Y|` bound of `AsmBrCoreStepAt` from `TourSplitMarksMatch`.** Under `OutStepReady`,
`outKeep ⊆ M ⊆ tr.S_cur.E`, `tr.S_cur.E.card ≤ eCap`, and the cap bound
`vCap + eCap + 2 ≤ (M₀ + N₀ + 2) ^ capExp`, the split list lengths sum to at most
`(1 + 4 * capExp) * tr.S_cur.batchEnc info.U_S * (Nat.log 2 (M₀ + N₀ + 2) + 1)`. -/
theorem tourSplitMarksMatch_sum_le_capExp {L capExp vCap eCap M₀ N₀ : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End)
    (hready : OutStepReady sparsify tr U ord ord')
    {M : Finset ℕ} (hkM : outKeep sparsify tr U ord ord' ⊆ M) (hM : M ⊆ tr.S_cur.E)
    (hEcard : tr.S_cur.E.card ≤ eCap) (hcap : vCap + eCap + 2 ≤ (M₀ + N₀ + 2) ^ capExp)
    {Ys : List (List End)}
    (hMatch : TourSplitMarksMatch M (coreGraph tr.cs.G tr.cs.lsf)
      (stepBundleTree sparsify tr U ord ord').U_core Ys) :
    (Ys.map List.length).sum ≤
      (1 + 4 * capExp) * tr.S_cur.batchEnc (stepBundleTree sparsify tr U ord ord').U_S *
        (Nat.log 2 (M₀ + N₀ + 2) + 1) := by
  rw [tourSplitMarksMatch_lengths _ _ _ _ hMatch]
  have h1 := outCutLens_sum_le_enc sparsify tr U ord ord' hready hkM hM
  have hlog1 : Nat.log 2 (2 * tr.S_cur.E.card + 1) ≤ Nat.log 2 (2 * eCap + 1) :=
    Nat.log_mono_right (by omega)
  have hlog2 := log_two_mul_eCap_add_one_le hcap
  have hlog : Nat.log 2 (2 * tr.S_cur.E.card + 1) ≤ capExp * (Nat.log 2 (M₀ + N₀ + 2) + 1) :=
    le_trans hlog1 hlog2
  have hfac : 1 + 4 * Nat.log 2 (2 * tr.S_cur.E.card + 1) ≤
      (1 + 4 * capExp) * (Nat.log 2 (M₀ + N₀ + 2) + 1) := by
    have h4 : 4 * Nat.log 2 (2 * tr.S_cur.E.card + 1) ≤
        4 * capExp * (Nat.log 2 (M₀ + N₀ + 2) + 1) := by
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 4 hlog
    rw [Nat.add_mul, Nat.one_mul]
    omega
  calc (cutLens M (coreGraph tr.cs.G tr.cs.lsf) (stepBundleTree sparsify tr U ord ord').U_core).sum
      ≤ tr.S_cur.batchEnc (stepBundleTree sparsify tr U ord ord').U_S *
          (1 + 4 * Nat.log 2 (2 * tr.S_cur.E.card + 1)) := h1
    _ ≤ tr.S_cur.batchEnc (stepBundleTree sparsify tr U ord ord').U_S *
          ((1 + 4 * capExp) * (Nat.log 2 (M₀ + N₀ + 2) + 1)) :=
        Nat.mul_le_mul_left _ hfac
    _ = (1 + 4 * capExp) * tr.S_cur.batchEnc (stepBundleTree sparsify tr U ord ord').U_S *
          (Nat.log 2 (M₀ + N₀ + 2) + 1) := by ring

end

end MinCostFlow.SparseCore.Program
