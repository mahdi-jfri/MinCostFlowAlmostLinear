module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosFullDefs

/-!
# The precondition of the first call of the step for `0 < j`

The whole step (`dsStepPosFullStmt`) starts with `dsStepHeadStmt`. This file derives the
precondition of that call from the state before the step (`DynSpannerStateAt`), the invariants
of the run up to `k`, and the record of `u`. The call has two parts with their own
preconditions: `stepPos_prefix_pre` for `dsStepPrefix` (apply `u` to `G`, `H` and the buckets) and
`stepPos_updS_pre` for `dsUpdateSLevels` (the sets `S_i`). `stepPos_head_pre` puts them
together.

The heap of the step starts at `heapStep`. The records of `restrictUpdate u H` go to
`heapStep + 5`, and the heap of `dsUpdateSLevels` starts at `heapStep + 5 + len`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.DynSpanner

public section

/-- The touched vertices of a deletion or a split are below `vCap`: the ends of a deleted edge
are vertices of `G`, and a split names a vertex of `G` and a new vertex below `vCap`. -/
lemma touchedVertices_lt_cap {G : MGraph} {u : Update} {vCap : ℕ} (hG : G.IsValid)
    (hu : G.UpdateIsValid u) (hcap : UpdateWithinCaps vCap 0 u)
    (hV : ∀ v ∈ G.V, v < vCap) : ∀ v ∈ touchedVertices G u, v < vCap := by
  intro v hv
  cases u with
  | insert _ _ _ => simp [touchedVertices] at hv
  | delete e =>
    have hends := hG e hu
    simp only [touchedVertices, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hV _ hends.1
    · exact hV _ hends.2
  | split v₁ v₂ St Sh =>
    simp only [touchedVertices, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hV _ hu.1
    · exact hcap

/-- `UpdateWithinCaps` does not look at `eCap` for a deletion or a split. -/
lemma updateWithinCaps_zero {vCap eCap : ℕ} {u : Update} (hds : isDelOrSplit u)
    (h : UpdateWithinCaps vCap eCap u) : UpdateWithinCaps vCap 0 u := by
  cases u with
  | insert _ _ _ => exact hds.elim
  | delete _ => trivial
  | split _ _ _ _ => exact h

/-- The precondition of `dsStepPrefixStmt` at the start of the step: the records of
`restrictUpdate u H` go to `heapStep + 5`. -/
theorem stepPos_prefix_pre {G₀ : MGraph} {impl : SparsifyImpl} {mMax w L q vCap eCap b k : ℕ}
    {us : List Update} {u : Update} {len updPtr heapStep : ℕ} {mem0 : ℕ → ℕ}
    {x : DynSpannerMeta L}
    (hBV : G₀.BatchIsValid us) (hds : ∀ u' ∈ us, isDelOrSplit u') (hu_some : us[k]? = some u)
    (hPref : ∀ s ≤ k, SnapInv G₀ L q mMax (canonicalSparsifyParams impl mMax).absorbTime
      (canonicalSparsify impl) us s)
    (hw16 : 16 ≤ 2 ^ w)
    (hState : DynSpannerStateAt L vCap eCap b mem0 x
      (runState (L := L) G₀ q (canonicalSparsify impl) us k))
    (hfix : b + dsFixedSize L vCap eCap ≤ heapStep)
    (hsp : heapStep + 5 + len < 2 ^ w)
    (hupd_le : updPtr + len ≤ heapStep)
    (hupd_foot : ∀ i < len, ¬ metaFoot b x (updPtr + i))
    (hupd_w : ∀ i < len, mem0 (updPtr + i) < 2 ^ w)
    (hupd_at : UpdateAt mem0 updPtr (runState (L := L) G₀ q (canonicalSparsify impl) us k).G u
      len)
    (hupd_cap : UpdateWithinCaps vCap eCap u) :
    let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
    (dsStepPrefixContract w L vCap eCap b st.G st.H u len (stepPosBmid0 x) (heapStep + 5)).pre
      [dsGPtr b, dsHPtr b vCap eCap, b, dsMinHBase b vCap eCap, updPtr,
        dgEPresBase (dsHPtr b vCap eCap) vCap, heapStep + 5] mem0 := by
  intro st
  have hk_inv := hPref k le_rfl
  obtain ⟨_, _, hU_k⟩ := batchIsValid_take us G₀ k hBV hds
  obtain ⟨hu_val, hdu⟩ := hU_k u hu_some
  rcases hState with ⟨hxV, hxE, _, _, _, _, hHV, hHEsub, hHends, _, hGE_cap,
    _, _, hmL, hmV, hmE, _, hG, hH, _, hminH, hBuck, _, _, _, _⟩
  have hSub : st.G.IsSubgraph st.H := ⟨hHV.subset, hHEsub, hHends⟩
  refine ⟨updPtr, rfl, ⟨updPtr, rfl, hw16, by omega, by omega, fun i hi => ?_, hupd_w, hupd_at,
    hk_inv.G_eq ▸ hu_val, hupd_cap, hdu, hGE_cap, hG, hH, hSub, hHV, hmL, hmV, hmE,
    fun i hi => by
      have hi' : i < L + 1 := by omega
      simp only [stepPosBmid0, hi', ↓reduceDIte]
      exact ⟨(hBuck ⟨i, hi'⟩).1, (hBuck ⟨i, hi'⟩).2.1⟩,
    fun i hi i' hi' hne e he => ?_,
    fun e he hz i hi heB => ?_,
    fun e he i hm => ?_⟩, by omega, by unfold IvlDisj; omega, by omega⟩
  · have hnf := hupd_foot i hi
    simp only [metaFoot, hxV, hxE, not_or, not_and, not_lt] at hnf
    by_cases hlt : updPtr + i < dsGPtr b
    · exact Or.inl hlt
    · exact Or.inr (hnf.1 (le_trans (dsGPtr_ge b) (Nat.le_of_not_lt hlt)))
  · have hi1 : i < L + 1 := by omega
    have hi2 : i' < L + 1 := by omega
    simp only [stepPosBmid0, hi1, hi2, ↓reduceDIte] at he ⊢
    intro he2
    have h1 := ((hBuck ⟨i, hi1⟩).2.2 e).mp he
    have h2 := ((hBuck ⟨i', hi2⟩).2.2 e).mp he2
    dsimp only at h1 h2
    omega
  · have hi1 : i < L + 1 := by omega
    simp only [stepPosBmid0, hi1, ↓reduceDIte] at heB
    have h1 := ((hBuck ⟨i, hi1⟩).2.2 e).mp heB
    dsimp only at h1
    omega
  · have heH : e ∈ st.H.E := by
      by_contra hnot
      have := (hminH e he).1.mpr hnot
      omega
    obtain ⟨i0, hi0_eq, _, _⟩ := (hminH e he).2 heH
    have hi_eq : i = i0.1 := by omega
    subst hi_eq
    refine ⟨by omega, ?_⟩
    simp only [stepPosBmid0, i0.2, ↓reduceDIte]
    exact ((hBuck i0).2.2 e).mpr ⟨heH, hm⟩

/-- The precondition of `dsUpdateSLevelsStmt` at the start of the step, with its heap at
`heapPtr`. -/
theorem stepPos_updS_pre {G₀ : MGraph} {impl : SparsifyImpl} {mMax w L q vCap eCap b k : ℕ}
    {us : List Update} {u : Update} {len updPtr heapPtr : ℕ} {mem0 : ℕ → ℕ}
    {x : DynSpannerMeta L}
    (hBV : G₀.BatchIsValid us) (hds : ∀ u' ∈ us, isDelOrSplit u') (hu_some : us[k]? = some u)
    (hPref : ∀ s ≤ k, SnapInv G₀ L q mMax (canonicalSparsifyParams impl mMax).absorbTime
      (canonicalSparsify impl) us s)
    (hw16 : 16 ≤ 2 ^ w) (hj_pos : 0 < chooseLevel L q (k + 1))
    (hState : DynSpannerStateAt L vCap eCap b mem0 x
      (runState (L := L) G₀ q (canonicalSparsify impl) us k))
    (hfix : b + dsFixedSize L vCap eCap ≤ heapPtr)
    (hfoot : ∀ a, heapFoot x a → a < heapPtr)
    (hsp : heapPtr + 4 * chooseLevel L q (k + 1) < 2 ^ w)
    (hgen : mem0 (b + dsGenOff) + chooseLevel L q (k + 1) < 2 ^ w)
    (hupd_w : updPtr + len < 2 ^ w)
    (hupd_at : UpdateAt mem0 updPtr (runState (L := L) G₀ q (canonicalSparsify impl) us k).G u
      len)
    (hupd_cap : UpdateWithinCaps vCap eCap u) :
    let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
    (dsUpdateSLevelsContract w L vCap eCap b (chooseLevel L q (k + 1)) st.G u len st.S_level
      x.sLists (heapFoot x)).pre [b, chooseLevel L q (k + 1), updPtr, heapPtr] mem0 := by
  intro st
  have hk_inv := hPref k le_rfl
  obtain ⟨_, _, hU_k⟩ := batchIsValid_take us G₀ k hBV hds
  obtain ⟨hu_val, hdu⟩ := hU_k u hu_some
  have hu_val' : st.G.UpdateIsValid u := hk_inv.G_eq ▸ hu_val
  rcases hState with ⟨_, _, hxiv, hb1, hGval, _, _, _, _, hGV_cap, hGE_cap,
    _, _, hmL, hmV, hmE, hgen1, hG, _, _, _, _, _, hS, _, _⟩
  have hj_le : chooseLevel L q (k + 1) ≤ L := chooseLevel_le L q (k + 1)
  refine ⟨updPtr, heapPtr, rfl, hw16, hb1, hj_pos, hj_le, hfix, hsp, hmL, hmV, hmE, hgen1, hgen,
    hG, hGval, hGV_cap, hGE_cap, hupd_at, hu_val', hdu, hupd_w,
    touchedVertices_lt_cap hGval hu_val' (updateWithinCaps_zero hdu hupd_cap) hGV_cap,
    fun a ha => ⟨let ⟨iv, hiv, h1, _⟩ := ha; le_trans (hxiv iv hiv) h1, hfoot a ha⟩, hS⟩

end

end MinCostFlow.DynSpanner.Program
