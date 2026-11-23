module

public import MinCostFlow.HierPaths.BuildProgChoiceSaved
public import MinCostFlow.HierPaths.BuildProgInjectBatch
import MinCostFlow.HierPaths.BuildChildHost

/-!
# The finished game's injection input

The saved table supplies the certificate set of each child. The game
invariant gives inclusion in the child and the size comparison needed
for a full routing call.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

/-- The saved set, when present, is the second side of the injection. -/
theorem injPairs_getD {s k c : ℕ} {off : ℕ → ℕ} {sts : ℕ → ChildState}
    {S : Finset ℕ} (hc : c < k) (hS : (sts c).saved = some S) :
    (injPairs s k off sts).getD c (∅,∅) =
      (shiftSet (off c) (Finset.range s \ S),shiftSet (off c) S) := by
  have hi : c < (injPairs s k off sts).length := by simpa [injPairs] using hc
  rw [List.getD_eq_getElem _ _ hi]
  simp [injPairs,savedSet,hS]

/-- An ended game has a complete injection table below the free arena. -/
theorem ChoiceLoopTrace.injectInput {w tailBudget : ℕ} {D : ChoiceLoopData} {β : ℝ} {bh : ℕ}
    {initial mem : ℕ → ℕ} {heap : ℕ} {sts : ℕ → ChildState}
    (hTrace : ChoiceLoopTrace w D initial D.limit heap sts mem)
    (h : ChoiceGameHyp D β bh) (hL : GameFixedLayout w D.geometry)
    (hInit : ChoiceGameMemory D D.addrs.heap (fun _ => ChildState.init) initial)
    (hRoom : ∀ t heap sts mem, t < D.limit →
      ChoiceLoopTrace w D initial t heap sts mem → (D.round sts).jobs.count ≠ 0 →
      ChoiceRoundBudget w tailBudget D heap sts) :
    let pairs := injPairs D.base.childSize D.count D.offset sts
    InjectInput w mem D.saved heap D.first D.base.childSize pairs ∧
      ∀ c < pairs.length, (buildBatchRow pairs c).length = D.base.childSize := by
  let pairs := injPairs D.base.childSize D.count D.offset sts
  have hPairCount : pairs.length = D.count := by simp [pairs,injPairs]
  obtain ⟨hInv,_⟩ := hTrace.certified.invariant h.router h.host h.positive h.expansion
    h.denominator h.children h.even (coreLevel_le h.coreSize)
  have hDone := CertifiedGame.all_saved h.children.1 h.sizeLog hInv
  have hSaved := hTrace.savedMemory le_rfl h hL hInit hRoom
  change InjectInput w mem D.saved heap D.first D.base.childSize pairs ∧ _
  refine ⟨?_,?_⟩
  · intro c hc
    rw [hPairCount] at hc
    obtain ⟨S,hS⟩ := hDone c hc
    have hSub := ((hInv c hc).2.2.2.1 S hS).1
    obtain ⟨_,hEnd,hAt⟩ := hSaved c hc S hS
    have hLen : (coreResultWords (.expander S)).length = 4+S.card := by
      simp [coreResultWords,layoutList,csrList,csrOffsets,csrData,List.range_succ,finsetWords]
      omega
    rw [hLen] at hEnd
    exact ⟨S,hSub,by omega,hAt,injPairs_getD hc hS,hL.offsetWords c hc⟩
  · intro c hc
    rw [hPairCount] at hc
    obtain ⟨S,hS⟩ := hDone c hc
    have hSub := ((hInv c hc).2.2.2.1 S hS).1
    have he : pairs.getD c (∅,∅) =
        (shiftSet (D.offset c) (Finset.range D.base.childSize \ S),shiftSet (D.offset c) S) :=
      injPairs_getD hc hS
    change (buildBatchRow pairs c).length = D.base.childSize
    simpa only [buildBatchRow,he,List.length_append,injectSides] using
      (injectSides_length (off := D.offset c) hSub)

/-- The complement of each saved set fits in that set. Across children
all endpoints lie in disjoint groups, as required by the router. -/
theorem ChoiceLoopTrace.injectRouterPre {w : ℕ} {D : ChoiceLoopData} {β : ℝ} {bh : ℕ}
    {initial mem : ℕ → ℕ} {heap : ℕ} {sts : ℕ → ChildState}
    (hTrace : ChoiceLoopTrace w D initial D.limit heap sts mem) (h : ChoiceGameHyp D β bh) :
    RouterPre D.base.host D.base.verts (injPairs D.base.childSize D.count D.offset sts)
      D.base.Δ D.base.L := by
  let s := D.base.childSize
  let pair := fun c =>
    (shiftSet (D.offset c) (Finset.range s \ savedSet s (sts c)),shiftSet (D.offset c) (savedSet s (sts c)))
  obtain ⟨hInv,_⟩ := hTrace.certified.invariant h.router h.host h.positive h.expansion
    h.denominator h.children h.even (coreLevel_le h.coreSize)
  have hDone := CertifiedGame.all_saved h.children.1 h.sizeLog hInv
  obtain ⟨hV,hL,hΔ,hD,hLpos,hSize⟩ := h.host
  refine ⟨hV,hL,hΔ,hD,hLpos,hSize,?_⟩
  change ValidTerminalPairs D.base.verts ((List.range D.count).map pair)
  refine validTerminalPairs_of_children List.nodup_range
    (fun c hc => (h.children.2.1 c (List.mem_range.mp hc)).1)
    (fun a ha b hb hab => h.children.2.2 a (List.mem_range.mp ha) b (List.mem_range.mp hb) hab) ?_
  intro c hc
  obtain ⟨S,hS⟩ := hDone c (List.mem_range.mp hc)
  obtain ⟨hSub,hHalf,_⟩ := (hInv c (List.mem_range.mp hc)).2.2.2.1 S hS
  have he : savedSet s (sts c) = S := by simp [savedSet,hS]
  change (pair c).1 ⊆ _ ∧ (pair c).2 ⊆ _ ∧ Disjoint (pair c).1 (pair c).2 ∧ _
  simp only [pair,he]
  refine ⟨shiftSet_subset Finset.sdiff_subset,shiftSet_subset hSub,?_,?_⟩
  · rw [shiftSet_sdiff]
    exact Finset.sdiff_disjoint
  · rw [card_shiftSet,card_shiftSet,Finset.card_sdiff_of_subset hSub,Finset.card_range]
    have hh : s ≤ 2*S.card := hHalf
    omega

/-- Full routing (`lemma_1`) supplies a full injection for every ended certified game. -/
theorem ChoiceLoopTrace.injectMatched {w : ℕ} {D : ChoiceLoopData} {β : ℝ} {bh : ℕ}
    {initial mem : ℕ → ℕ} {heap : ℕ} {sts : ℕ → ChildState}
    (hTrace : ChoiceLoopTrace w D initial D.limit heap sts mem) (h : ChoiceGameHyp D β bh)
    (hk : 1 ≤ D.count) :
    let pairs := injPairs D.base.childSize D.count D.offset sts
    let res := lemma1Route D.base.route D.base.host D.base.verts pairs D.base.Δ D.base.L
    ∃ Ms emb, res.1 = .matched Ms emb ∧
      RouteMatchedSpec D.base.host D.base.verts pairs D.base.Δ D.base.L res.2 0 Ms emb ∧
      (∀ i (hi : i < pairs.length), (Ms.getD i []).length = (pairs[i]'hi).1.card) ∧ res.2 ≤ bh := by
  let pairs := injPairs D.base.childSize D.count D.offset sts
  let res := lemma1Route D.base.route D.base.host D.base.verts pairs D.base.Δ D.base.L
  have hpos : 1 ≤ pairs.length := by simpa [pairs,injPairs] using hk
  obtain ⟨_,hex⟩ := exists_lemma_1 h.router
  obtain ⟨⟨ms,em,he,hs,hN⟩,_,hBh,_,_⟩ := hex D.base.host D.base.verts pairs D.base.Δ D.base.L
    (hTrace.injectRouterPre h) hpos β h.positive h.expansion
  have hReal : (res.2 : ℝ) ≤ (bh : ℝ) := hBh.trans h.denominator
  exact ⟨ms,em,he,hs,hN,by exact_mod_cast hReal⟩

end MinCostFlow.HierPaths
