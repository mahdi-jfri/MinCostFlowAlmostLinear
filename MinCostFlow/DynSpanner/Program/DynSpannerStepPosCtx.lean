module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosDefs
import WordRAM.Tactic

/-!
# From the context of a `0 < j` step to the contexts of its parts

`StepPosCtx` (`DynSpannerStepPosDefs.lean`) holds the facts after `dsAffStage`. This file builds
from it the context of each part that `dsStepPosStmt` runs: `toNE` for the nonempty branch
(when `0 < eAff.length`), `toEmpty` for the empty branch (when `eAff = []`), and `toEp` for the
epilogue, once a branch has ended in `StepPosMidPost`. Most fields are copied. The lemmas before
the definitions prove the few fields that differ.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.DynSpanner

@[expose] public section

namespace StepPosCtx

lemma hEnd_ne (ctx : StepPosCtx) (hpos : 0 < ctx.eAff.length) :
    dsStepPosNonEmptyEnd ctx.impl ctx.mMax ctx.vCap ctx.eCap ctx.G' ctx.J ctx.piLt_mid
      ctx.embJH ctx.eAff ctx.wpPtr ctx.cand.length ctx.oldBucketsSum < 2 ^ ctx.w := by
  have h : ctx.midEnd + ctx.prefWords + 4 * ctx.res.UH.length < 2 ^ ctx.w := ctx.hEnd_ltw
  simp only [StepPosCtx.midEnd, hpos, ↓reduceIte] at h
  omega

lemma hEnd_em (ctx : StepPosCtx) (h0 : ctx.eAff = []) :
    ctx.retAffE + ctx.eCap + 1 + 2 * ctx.oldBucketsSum < 2 ^ ctx.w := by
  have h : ctx.midEnd + ctx.prefWords + 4 * ctx.res.UH.length < 2 ^ ctx.w := ctx.hEnd_ltw
  have hn : ¬ 0 < ctx.eAff.length := by simp [h0]
  simp only [StepPosCtx.midEnd, hn, ↓reduceIte] at h
  omega

lemma hEnd_ep (ctx : StepPosCtx) {nextHeap : ℕ} (hNext : nextHeap ≤ ctx.midEnd) :
    nextHeap + ctx.prefWords + 4 * ctx.res.UH.length < 2 ^ ctx.w := by
  have h : ctx.midEnd + ctx.prefWords + 4 * ctx.res.UH.length < 2 ^ ctx.w := ctx.hEnd_ltw
  omega

lemma hGen_em (ctx : StepPosCtx) : ctx.memAff (ctx.b + dsGenOff) + 2 < 2 ^ ctx.w := by
  have := ctx.hGen_ltw
  omega

lemma hZero_em (ctx : StepPosCtx) (h0 : ctx.eAff = []) : ZeroFrom ctx.memAff ctx.retAffE := by
  intro a ha
  have h := ctx.hZeroAff
  dsimp only at h
  apply h a
  simp only [h0, List.length_nil, List.map_nil, List.sum_nil, Nat.mul_zero, Nat.add_zero]
  exact ha

lemma hAff_empty (ctx : StepPosCtx) (h0 : ctx.eAff = []) :
    affectedEdges ctx.G' ctx.H_lt ctx.piLt_mid ctx.S_prev = ∅ :=
  Finset.eq_empty_of_forall_notMem fun e he => by
    have h1 := (ctx.hAff_iff e).mpr he
    rw [h0] at h1
    exact List.not_mem_nil h1

/-- The words `minH` after `dsStepHead`: they are `minHAfter u` of the old words. This is the form
the empty branch uses; it follows from `hmin_after` and the old state. -/
lemma hmin2 (ctx : StepPosCtx) :
    ∀ e < ctx.eCap, ctx.mem2 (dsMinHBase ctx.b ctx.vCap ctx.eCap + e) =
      minHAfter ctx.u (ctx.mem0 (dsMinHBase ctx.b ctx.vCap ctx.eCap + e)) e := by
  intro e he
  have hdu := (batchIsValid_take ctx.us ctx.G₀ ctx.k ctx.hBV ctx.hds).2.2 ctx.u ctx.hu_some
  have h0 := ctx.hState.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e he
  have h2 := ctx.hmin_after.1 e he
  have hmem_mid : ∀ k' : Fin (ctx.L + 1), (ctx.H_mid k').E = (ctx.st.H_level k').E ∩ ctx.G'.E := by
    intro k'
    have hsub := (ctx.hPref ctx.k (le_refl _)).H_level_sub k'
    have hV := (ctx.hPref ctx.k (le_refl _)).H_level_V k'
    exact (isSubgraph_restrictUpdate ((ctx.hPref ctx.k (le_refl _)).G_eq ▸ hsub)
      ((ctx.hPref ctx.k (le_refl _)).G_eq ▸ hV)
      ((ctx.hPref ctx.k (le_refl _)).G_eq ▸ hdu.1) hdu.2).2.2.2.1
  cases hu_eq : ctx.u with
  | insert _ _ _ => rw [hu_eq] at hdu; exact hdu.2.elim
  | delete d =>
    simp only [minHAfter]
    by_cases hed : e = d
    · subst hed
      have hnot : e ∉ delSet (Update.delete e) ctx.st.H.E := by simp [delSet]
      simp only [↓reduceIte]
      exact h2.1.mpr (hu_eq ▸ hnot)
    · simp only [hed, ↓reduceIte]
      by_cases heH : e ∈ ctx.st.H.E
      · have heD : e ∈ delSet ctx.u ctx.st.H.E := by rw [hu_eq]; simp [delSet, hed, heH]
        obtain ⟨i, hi_eq, hi_mem, hi_min⟩ := h0.2 heH
        obtain ⟨i', hi'_eq, hi'_mem, hi'_min⟩ := h2.2 heD
        have heG' : e ∈ ctx.G'.E := by
          have heG : e ∈ ctx.st.G.E := (ctx.hPref ctx.k (le_refl _)).G_eq ▸
            (ctx.hPref ctx.k (le_refl _)).H_sub.2.1 heH
          change e ∈ (ctx.st.G.applyUpdate ctx.u).E
          rw [applyUpdate_E_delSet hdu.2, hu_eq]; simp [delSet, hed, heG]
        have hmem_iff : ∀ k' : Fin (ctx.L + 1), e ∈ (ctx.H_mid k').E ↔ e ∈ (ctx.st.H_level k').E :=
          fun k' => by rw [hmem_mid k', Finset.mem_inter]; exact ⟨And.left, fun h => ⟨h, heG'⟩⟩
        have hle1 : ¬ i'.1 < i.1 := fun hlt => hi_min i' hlt ((hmem_iff i').mp hi'_mem)
        have hle2 : ¬ i.1 < i'.1 := fun hlt => hi'_min i hlt ((hmem_iff i).mpr hi_mem)
        omega
      · have hnot : e ∉ delSet ctx.u ctx.st.H.E := by rw [hu_eq]; simp [delSet, heH]
        rw [h0.1.mpr heH, h2.1.mpr hnot]
  | split v v' St Sh =>
    simp only [minHAfter]
    by_cases heH : e ∈ ctx.st.H.E
    · have heD : e ∈ delSet ctx.u ctx.st.H.E := by rw [hu_eq]; simp [delSet, heH]
      obtain ⟨i, hi_eq, hi_mem, hi_min⟩ := h0.2 heH
      obtain ⟨i', hi'_eq, hi'_mem, hi'_min⟩ := h2.2 heD
      have heG' : e ∈ ctx.G'.E := by
        have heG : e ∈ ctx.st.G.E := (ctx.hPref ctx.k (le_refl _)).G_eq ▸
          (ctx.hPref ctx.k (le_refl _)).H_sub.2.1 heH
        change e ∈ (ctx.st.G.applyUpdate ctx.u).E
        rw [applyUpdate_E_delSet hdu.2, hu_eq]; simp [delSet, heG]
      have hmem_iff : ∀ k' : Fin (ctx.L + 1), e ∈ (ctx.H_mid k').E ↔ e ∈ (ctx.st.H_level k').E :=
        fun k' => by rw [hmem_mid k', Finset.mem_inter]; exact ⟨And.left, fun h => ⟨h, heG'⟩⟩
      have hle1 : ¬ i'.1 < i.1 := fun hlt => hi_min i' hlt ((hmem_iff i').mp hi'_mem)
      have hle2 : ¬ i.1 < i'.1 := fun hlt => hi'_min i hlt ((hmem_iff i).mpr hi_mem)
      omega
    · have hnot : e ∉ delSet ctx.u ctx.st.H.E := by rw [hu_eq]; simp [delSet, heH]
      rw [h0.1.mpr heH, h2.1.mpr hnot]

/-- The context of the nonempty branch. -/
noncomputable def toNE (ctx : StepPosCtx) (hpos : 0 < ctx.eAff.length) : StepPosNECtx where
  G₀ := ctx.G₀
  w := ctx.w
  L := ctx.L
  q := ctx.q
  mMax := ctx.mMax
  vCap := ctx.vCap
  eCap := ctx.eCap
  b := ctx.b
  k := ctx.k
  impl := ctx.impl
  us := ctx.us
  u := ctx.u
  mem0 := ctx.mem0
  mem2 := ctx.mem2
  memAff := ctx.memAff
  x := ctx.x
  headHeap := ctx.headHeap
  r₁ := ctx.r₁
  heapStep := ctx.heapStep
  heapAff := ctx.heapAff
  sPrevList := ctx.sPrevList
  cand := ctx.cand
  eAff := ctx.eAff
  prefWords := ctx.prefWords
  oldBucketsSum := ctx.oldBucketsSum
  hw16 := ctx.hw16
  hVG₀ := ctx.hVG₀
  hq := ctx.hq
  hGm₀ := ctx.hGm₀
  hE₀_cap := ctx.hE₀_cap
  hBV := ctx.hBV
  hds := ctx.hds
  hu_some := ctx.hu_some
  hPref := ctx.hPref
  hj_pos := ctx.hj_pos
  hState := ctx.hState
  hGV'_cap := ctx.hGV'_cap
  hfix_step := ctx.hfix_step
  hhead_in := ctx.hhead_in
  hfoot_lt := ctx.hfoot_lt
  heAff_pos := hpos
  hEnd_ltw := ctx.hEnd_ne hpos
  hGen_ltw := ctx.hGen_ltw
  hZeroAff := ctx.hZeroAff
  hOldSum := ctx.hOldSum
  hG'_graph := ctx.hG'_graph
  hHmid_graph := ctx.hHmid_graph
  hBk_mem2 := ctx.hBk_mem2
  hmin_after := ctx.hmin_after
  hgen_02 := ctx.hgen_02
  hS2_lt := ctx.hS2_lt
  hS2_ge := ctx.hS2_ge
  hHdr_02 := ctx.hHdr_02
  hDom_02 := ctx.hDom_02
  hVSt_02 := ctx.hVSt_02
  hKept_02 := ctx.hKept_02
  hFoot_02 := ctx.hFoot_02
  hFrame_02 := ctx.hFrame_02
  hAff_eNd := ctx.hAff_eNd
  hAff_iff := ctx.hAff_iff
  hAff_at := ctx.hAff_at
  hAff_sPrev := ctx.hAff_sPrev
  hAff_aux := ctx.hAff_aux
  hAff_wp := ctx.hAff_wp
  hAff_emb := ctx.hAff_emb
  hAff_sBit := ctx.hAff_sBit
  hAff_gen := ctx.hAff_gen
  hAff_eStamp := ctx.hAff_eStamp
  hAff_frame := ctx.hAff_frame

/-- The context of the empty branch, with its zero table at `retAffE = eAffPtr + cand.length`. -/
noncomputable def toEmpty (ctx : StepPosCtx) (h0 : ctx.eAff = []) : StepPosEmptyCtx where
  G₀ := ctx.G₀
  w := ctx.w
  L := ctx.L
  q := ctx.q
  mMax := ctx.mMax
  vCap := ctx.vCap
  eCap := ctx.eCap
  b := ctx.b
  k := ctx.k
  impl := ctx.impl
  us := ctx.us
  u := ctx.u
  mem0 := ctx.mem0
  mem2 := ctx.mem2
  memAff := ctx.memAff
  x := ctx.x
  headHeap := ctx.headHeap
  r₁ := ctx.r₁
  heapStep := ctx.heapStep
  heapAff := ctx.heapAff
  retAff := ctx.retAffE
  sPrevList := ctx.sPrevList
  cand := ctx.cand
  prefWords := ctx.prefWords
  oldBucketsSum := ctx.oldBucketsSum
  hw16 := ctx.hw16
  hVG₀ := ctx.hVG₀
  hq := ctx.hq
  hGm₀ := ctx.hGm₀
  hBV := ctx.hBV
  hds := ctx.hds
  hu_some := ctx.hu_some
  hPref := ctx.hPref
  hj_pos := ctx.hj_pos
  hState := ctx.hState
  hGV'_cap := ctx.hGV'_cap
  hfix_step := ctx.hfix_step
  hhead_in := ctx.hhead_in
  hret_ge := Nat.le_add_right _ _
  hEnd_ltw := ctx.hEnd_em h0
  hGen_ltw := ctx.hGen_em
  hZeroAff := ctx.hZero_em h0
  hOldSum := ctx.hOldSum
  hG'_graph := ctx.hG'_graph
  hHmid_graph := ctx.hHmid_graph
  hBk_mem2 := ctx.hBk_mem2
  hmin2 := ctx.hmin2
  hgen_02 := ctx.hgen_02
  hS2_ge := ctx.hS2_ge
  hHdr_02 := ctx.hHdr_02
  hDom_02 := ctx.hDom_02
  hVSt_02 := ctx.hVSt_02
  hKept_02 := ctx.hKept_02
  hFoot_02 := ctx.hFoot_02
  hfoot_lt := ctx.hfoot_lt
  hFrame_02 := ctx.hFrame_02
  hAff_empty := ctx.hAff_empty h0
  hAff_sPrev := ctx.hAff_sPrev
  hAff_aux := ctx.hAff_aux
  hAff_sBit := ctx.hAff_sBit
  hAff_gen := ctx.hAff_gen
  hAff_eStamp := ctx.hAff_eStamp
  hAff_frame := ctx.hAff_frame

/-- The context of the epilogue, after a branch has ended in `StepPosMidPost` with next free
word `nextHeap`. -/
noncomputable def toEp (ctx : StepPosCtx) (memMid : ℕ → ℕ) (nextHeap : ℕ)
    (hMid : StepPosMidPost ctx.G₀ ctx.L ctx.q ctx.vCap ctx.eCap ctx.b ctx.k ctx.impl ctx.us ctx.u
      ctx.mem0 ctx.mem2 ctx.x ctx.headHeap ctx.r₁ ctx.heapStep ctx.heapAff ctx.sPrevList
      ctx.prefWords memMid nextHeap)
    (hNext : nextHeap ≤ ctx.midEnd) : StepPosEpCtx where
  G₀ := ctx.G₀
  w := ctx.w
  L := ctx.L
  q := ctx.q
  mMax := ctx.mMax
  vCap := ctx.vCap
  eCap := ctx.eCap
  b := ctx.b
  k := ctx.k
  impl := ctx.impl
  us := ctx.us
  u := ctx.u
  mem0 := ctx.mem0
  mem2 := ctx.mem2
  memMid := memMid
  x := ctx.x
  sLists' := ctx.sLists'
  headHeap := ctx.headHeap
  r₁ := ctx.r₁
  heapStep := ctx.heapStep
  heapAff := ctx.heapAff
  sPrevList := ctx.sPrevList
  prefWords := ctx.prefWords
  nextHeap := nextHeap
  hw16 := ctx.hw16
  hVG₀ := ctx.hVG₀
  hq := ctx.hq
  hGm₀ := ctx.hGm₀
  hBV := ctx.hBV
  hds := ctx.hds
  hu_some := ctx.hu_some
  hPref := ctx.hPref
  hj_pos := ctx.hj_pos
  hState := ctx.hState
  hRev := ctx.hRev
  hGV'_cap := ctx.hGV'_cap
  hfix_step := ctx.hfix_step
  hhead_in := ctx.hhead_in
  hgen_02 := ctx.hgen_02
  hPrefBody := ctx.hPrefBody
  hSL2 := ctx.hSL2
  hsPrev_eq := ctx.hsPrev_eq
  hFoot_02 := ctx.hFoot_02
  hfoot_lt := ctx.hfoot_lt
  hKept_le := ctx.hKept_le
  hMidPost := hMid
  ht_ltw := ctx.ht_ltw
  hEnd_ltw := ctx.hEnd_ep hNext

end StepPosCtx

end

end MinCostFlow.DynSpanner.Program
