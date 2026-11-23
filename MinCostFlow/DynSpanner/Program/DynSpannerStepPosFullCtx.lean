module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosFullAffPost
public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosFullHead
public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosFullBound
import MinCostFlow.DynSpanner.Program.DynSpannerStepMidMinH
import MinCostFlow.DynSpanner.Program.DynSpannerStepBridge

/-!
# The context of the last part of the step for `0 < j`

`dsStepPosStmt` (the last part of the step) takes its precondition as a context `StepPosCtx`:
the facts on the memories `mem2` after `dsStepHead` and `memAff` after `dsAffStage`.
`stepPosFullCtx` builds this context from the precondition of the whole step, the post of
`dsStepHead` (through its frames, `stepPosHead_keep`) and the facts after `dsAffStage`
(`StepPosAffFacts`). The heap of the step is laid out as in `DynSpannerStepPosFullDefs.lean`:
the records of `restrictUpdate u H` at `heapStep + 5`, the heap of `dsUpdateSLevels` at
`heapStep + 5 + len`, and the heap of `dsAffStage` at `heapStep + 5 + len + 4 · j`.

Most fields are hypotheses. The others follow from the frames: the words of the state that a call
does not write keep their values, and the words above the heap of the step stay zero.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.DynSpanner

/-- Memory is zero from `Z` on if it agrees with a memory that is zero from `hs` on, through a
second memory, above `H`, with `hs ≤ H ≤ Z`. -/
lemma zeroFrom_of_frames {memAff mem2 mem0 : ℕ → ℕ} {Z H hs : ℕ}
    (hz : ∀ addr, Z ≤ addr → memAff addr = mem2 addr)
    (hk : ∀ addr, H ≤ addr → mem2 addr = mem0 addr) (h0 : ZeroFrom mem0 hs)
    (hZH : H ≤ Z) (hsH : hs ≤ H) : ZeroFrom memAff Z := fun addr ha => by
  rw [hz addr ha, hk addr (by omega)]
  exact h0 addr (by omega)

@[expose] public section

/-- The context `StepPosCtx` after `dsStepHead` and `dsAffStage` in a step at `0 < j`. Here
`mid` is the memory between the two calls of `dsStepHead`, `r₁` the end of the heap of
`dsUpdateSLevels`, `prefWords` the number of words of the records of `restrictUpdate u H`,
`sLists'` the lists of the new sets `S_i`, and `cand`, `eAff` the lists of candidates and of
affected edges. -/
noncomputable def stepPosFullCtx (m : StepPosModel) (mMax w vCap eCap b len : ℕ)
    (x : DynSpannerMeta m.L) (mem0 mid mem2 memAff : ℕ → ℕ) (heapStep r₁ prefWords : ℕ)
    (sLists' : Fin (m.L + 1) → List ℕ) (cand eAff : List ℕ)
    (hw16 : 16 ≤ 2 ^ w) (hVG₀ : m.G₀.IsValid) (hq : 1 ≤ m.q) (hGm₀ : m.G₀.m ≤ mMax)
    (hE₀_cap : ∀ e ∈ m.G₀.E, e < eCap) (hBV : m.G₀.BatchIsValid m.us)
    (hds : ∀ u' ∈ m.us, isDelOrSplit u') (hu_some : m.us[m.k]? = some m.u)
    (hPref : ∀ s ≤ m.k, SnapInv m.G₀ m.L m.q mMax (canonicalSparsifyParams m.impl mMax).absorbTime
      (canonicalSparsify m.impl) m.us s)
    (hj_pos : 0 < m.j)
    (hRev : RevHistoryInv m.G₀ m.q (canonicalSparsify m.impl) m.us m.k x)
    (hState : DynSpannerStateAt m.L vCap eCap b mem0 x m.st)
    (hfix : b + dsFixedSize m.L vCap eCap ≤ heapStep)
    (hfoot : ∀ a, heapFoot x a → a < heapStep)
    (hZero : ZeroFrom mem0 heapStep)
    (hEnd : dsStepPosFullEnd m mMax vCap eCap len x heapStep < 2 ^ w)
    (hGen : mem0 (b + dsGenOff) + m.j + 4 + m.G'.m < 2 ^ w)
    (ht : m.k + 1 < 2 ^ w)
    -- the post of `dsStepHead`
    (hr₁lo : heapStep + 5 + len ≤ r₁) (hr₁hi : r₁ ≤ heapStep + 5 + len + 4 * m.j)
    (hgen₁ : mem0 (b + dsGenOff) ≤ mid (b + dsGenOff))
    (hgen₂ : mid (b + dsGenOff) ≤ mem0 (b + dsGenOff) + m.j)
    (hfrS : ∀ addr, dsUpdateSLevelsFrameCond m.L vCap eCap b (heapStep + 5 + len) r₁ addr →
      mid addr = mem0 addr)
    (hfrP : ∀ addr, (addr < heapStep + 5 ∨ heapStep + 5 + len ≤ addr) →
      (addr < dsGPtr b ∨ (dsAuxPtr b vCap eCap ≤ addr ∧ addr < dsMinHBase b vCap eCap) ∨
        dsDomGenBase b m.L vCap eCap ≤ addr) → mem2 addr = mid addr)
    (hpw : prefWords ≤ len)
    (hPrefBody : BatchBodyAt mem2 (heapStep + 5) m.st.H (restrictUpdate m.u m.st.H) prefWords)
    (hG' : DynGraphAt mem2 (dsGPtr b) vCap eCap m.G')
    (hHmid : DynGraphAt mem2 (dsHPtr b vCap eCap) vCap eCap
      (m.st.H.applyBatch (restrictUpdate m.u m.st.H)))
    (hBk : BucketsAt mem2 m.L vCap eCap b (stepPosBmid m.u x))
    (hminP : ∀ e' < eCap, mem2 (dsMinHBase b vCap eCap + e') =
      minHAfter m.u (mid (dsMinHBase b vCap eCap + e')) e')
    (hSL2 : ∀ i : Fin (m.L + 1),
      let S' : Finset ℕ := if i.1 < m.j then m.st.S_level i ∪ touchedVertices m.st.G m.u else ∅
      mem2 (dsSGenBase b m.L vCap eCap + i.1) ≤ mem2 (b + dsGenOff) ∧
      (m.j ≤ i.1 → mem2 (dsSGenBase b m.L vCap eCap + i.1) = 0) ∧
      (∀ v ∈ S', v < vCap) ∧
      (∀ v < vCap,
        mem2 (dsVSGenBase b m.L vCap eCap + i.1 * vCap + v) ≤ mem2 (b + dsGenOff) ∧
        ((0 < mem2 (dsSGenBase b m.L vCap eCap + i.1) ∧
          mem2 (dsVSGenBase b m.L vCap eCap + i.1 * vCap + v) =
            mem2 (dsSGenBase b m.L vCap eCap + i.1)) ↔ v ∈ S')) ∧
      (sLists' i).Nodup ∧ (∀ v, v ∈ sLists' i ↔ v ∈ S') ∧
      (if 0 < mem2 (dsSGenBase b m.L vCap eCap + i.1)
       then LinkedListIn (fun p => heapFoot x p ∨ (heapStep + 5 + len ≤ p ∧ p < r₁)) mem2
              (mem2 (dsSHeadBase b m.L vCap eCap + i.1)) (sLists' i)
       else sLists' i = []))
    -- the post of `dsAffStage`
    (hA : StepPosAffFacts m.L vCap eCap b (heapStep + 5 + len + 4 * m.j) m.G' m.piLt_mid
      m.S_prev m.E_aff (sLists' ⟨m.j - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _)
        (Nat.lt_succ_of_le (chooseLevel_le m.L m.q (m.k + 1)))⟩)
      mem2 memAff (heapFoot x) cand eAff) : StepPosCtx :=
  have hjL : m.j ≤ m.L := chooseLevel_le m.L m.q (m.k + 1)
  have hjL1 : m.j - 1 < m.L + 1 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_of_le hjL)
  have hkeep := stepPosHead_keep hfix hr₁hi hfrS hfrP
  have hlay := stepPosLayout b m.L vCap eCap
  have hfa := dsFixedSize_pos m.L vCap eCap
  have hsp_card : (sLists' ⟨m.j - 1, hjL1⟩).length = m.S_prev.card := by
    have h := hSL2 ⟨m.j - 1, hjL1⟩
    simp only [show m.j - 1 < m.j by omega, ↓reduceIte] at h
    exact list_length_eq_card h.2.2.2.2.1 h.2.2.2.2.2.1
  have hcand : cand.length ≤ m.G'.m := by
    have hsub : cand.toFinset ⊆ m.G'.E := fun e he => hA.2.1 e (List.mem_toFinset.mp he)
    rw [← List.toFinset_card_of_nodup hA.1]
    exact Finset.card_le_card hsub
  have heAff_le : eAff.length ≤ m.G'.m := by
    have hsub : eAff.toFinset ⊆ m.G'.E := fun e he =>
      (Finset.mem_filter.mp ((hA.2.2.2.1 e).mp (List.mem_toFinset.mp he))).1
    rw [← List.toFinset_card_of_nodup hA.2.2.1]
    exact Finset.card_le_card hsub
  have hendle := stepPosFull_end_le m mMax vCap eCap len x heapStep (sPrevList :=
    sLists' ⟨m.j - 1, hjL1⟩) (cand := cand) hA.2.2.1 hA.2.2.2.1 hcand hsp_card hpw
  have hk_inv := hPref m.k le_rfl
  have hdu : isDelOrSplit m.u := hds m.u (List.mem_of_getElem? hu_some)
  have hbridge := unionGraphLt_bridge m.G' m.H_mid m.j m.piLt_mid m.piLt_mid m.S_prev m.E_aff
  { G₀ := m.G₀, w := w, L := m.L, q := m.q, mMax := mMax, vCap := vCap, eCap := eCap, b := b,
    k := m.k, impl := m.impl, us := m.us, u := m.u, mem0 := mem0, mem2 := mem2,
    memAff := memAff, x := x, headHeap := heapStep + 5 + len, r₁ := r₁, heapStep := heapStep,
    heapAff := heapStep + 5 + len + 4 * m.j,
    sPrevList := sLists' ⟨m.j - 1, hjL1⟩, cand := cand, eAff := eAff,
    prefWords := prefWords, oldBucketsSum := stepPosOldSum m.u x m.j
    hw16 := hw16, hVG₀ := hVG₀, hq := hq, hGm₀ := hGm₀, hE₀_cap := hE₀_cap, hBV := hBV,
    hds := hds, hu_some := hu_some, hPref := hPref, hj_pos := hj_pos, hState := hState
    hGV'_cap := hG'.2.1
    hfix_step := hfix
    hhead_in := ⟨by omega, hr₁lo, hr₁hi⟩
    hfoot_lt := hfoot
    hEnd_ltw := lt_of_le_of_lt (le_trans (Nat.le_add_right _ 2) hendle) hEnd
    hGen_ltw := by
      have h1 := hA.2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [h1, hkeep.2.2.2.2.1]
      omega
    hZeroAff := by
      have hz := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      rw [projHeapNeed_eq, ← Nat.add_assoc] at hz
      exact zeroFrom_of_frames hz hkeep.2.2.2.1 hZero (by omega) (by omega)
    hOldSum := rfl
    hG'_graph := hG'
    hHmid_graph := hHmid
    hBk_mem2 := hBk
    hmin_after := by
      rcases hState with ⟨_, _, _, _, _, _, _, _, _, _, hGE_cap, _, _, _, _, _, _, _, _, _,
        hminH0, hBuck0, _, _, _, _⟩
      obtain ⟨_, _, hU_k⟩ := batchIsValid_take m.us m.G₀ m.k hBV hds
      obtain ⟨hu_val, _⟩ := hU_k m.u hu_some
      have hmid_min : ∀ e' < eCap, mid (dsMinHBase b vCap eCap + e') =
          mem0 (dsMinHBase b vCap eCap + e') := by
        intro e' he'
        rcases hkeep.2.2.2.2.2 (dsMinHBase b vCap eCap + e') (by omega) with h | h
        · exact h
        · omega
      exact minH_after_update hdu
        (m := fun e => mem0 (dsMinHBase b vCap eCap + e))
        (m' := fun e => mem2 (dsMinHBase b vCap eCap + e))
        (H_level := m.st.H_level) (H_mid := m.H_mid) (B := stepPosBmid0 x)
        (fun e he => (hminH0 e he).1) (fun e he => (hminH0 e he).2)
        (fun i e => by simpa [stepPosBmid0, i.2] using (hBuck0 i).2.2 e)
        (fun i => by simpa [stepPosBmid0, i.2] using (hBuck0 i).1.1)
        (fun e he => by rw [hminP e he, hmid_min e he])
        (fun i => mid_E_delSet hdu (m.st.H_level i))
        (fun e heq => hGE_cap e (by rw [heq] at hu_val; exact hk_inv.G_eq ▸ hu_val))
    hgen_02 := by rw [hkeep.2.2.2.2.1]; exact hgen₁
    hS2_lt := fun i _ => ⟨(hSL2 i).1, fun v hv => ((hSL2 i).2.2.2.1 v hv).1⟩
    hS2_ge := fun i _ v hv => ((hSL2 i).2.2.2.1 v hv).1
    hHdr_02 := fun addr _ h2 h3 => hkeep.1 addr h2 h3
    hDom_02 := fun addr h1 h2 => hkeep.2.1 addr h1 h2
    hVSt_02 := fun v hv => by
      rw [hkeep.2.2.1 _ (by omega) (by omega), hkeep.2.2.2.2.1]
      exact le_trans (hState.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 v hv).2 hgen₁
    hKept_02 := fun e he => hkeep.2.2.1 _ (by omega) (by omega)
    hFoot_02 := fun a ha => by
      have h1 : b + dsFixedSize m.L vCap eCap ≤ a := by
        obtain ⟨iv, hiv, h1, _⟩ := ha
        exact le_trans (hState.2.2.1 iv hiv) h1
      exact hkeep.2.2.1 a (by omega) (hfoot a ha)
    hFrame_02 := fun a ha hnf => by
      simp only [metaFoot, hState.1, hState.2.1, not_or, not_and, not_lt] at hnf
      by_cases hab : a < b
      · exact hkeep.1 a (by omega) (by simp only [dsGenOff]; omega)
      · exact hkeep.2.2.1 a (by have := hnf.1 (by omega); omega) ha
    hAff_eNd := hA.2.2.1
    hAff_iff := hA.2.2.2.1
    hAff_at := hA.2.2.2.2.2.2.2.1
    hAff_sPrev := hA.2.2.2.2.2.2.1
    hAff_aux := by
      have h := hA.2.2.2.2.2.2.2.2.1
      dsimp only
      rw [hbridge.1]
      exact h
    hAff_wp := fun k hk => by
      obtain ⟨h1, h2, h3⟩ := hA.2.2.2.2.2.2.2.2.2.1 k hk
      have hlen : 0 < (mWalkEncode (m.piLt_mid eAff[k])).length := by
        rw [mWalkEncode_length]; omega
      have key : ∀ (p n : ℕ), 0 < n → (∀ addr, p ≤ addr → addr < p + n → heapFoot x addr) →
          p + n ≤ heapStep := fun p n hn h => by
        have := hfoot _ (h (p + n - 1) (by omega) (by omega)); omega
      exact ⟨h1, key _ _ hlen h2, h3⟩
    hAff_emb := by
      have h := hA.2.2.2.2.2.2.2.2.2.2.1
      dsimp only
      rw [hbridge.2.1]
      exact h
    hAff_sBit := hA.2.2.2.2.2.2.2.2.2.2.2.1
    hAff_gen := by rw [hA.2.2.2.2.2.2.2.2.2.2.2.2.1, hkeep.2.2.2.2.1]
    hAff_eStamp := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hAff_frame := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    sLists' := sLists'
    hRev := hRev
    hPrefBody := hPrefBody
    hSL2 := hSL2
    hsPrev_eq := rfl
    hKept_le := fun e he => (hState.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 e he).2
    ht_ltw := ht }

end

end MinCostFlow.DynSpanner.Program
