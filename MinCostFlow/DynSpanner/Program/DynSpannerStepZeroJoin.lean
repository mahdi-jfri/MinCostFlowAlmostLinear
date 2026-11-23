module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepZeroDefs
public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosJoinB

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Pure stage joins for the `j = 0` restart branch (`DynSpannerStepZeroJoin`)

Bridges the abstract model (`step`, `SnapInv`, `RevHistoryInv`, `diffBatch_perm_props`) and
the Word-RAM stage contracts for `dsStepZeroStmt`:

* `stepZero_prefix_pre`: builds `dsStepPrefixContract.pre` from `DynSpannerStateAt`.
* `stepZero_clearBuckets_ctx`: builds `CBCtx` on levels `0..L` after `dsStepPrefix`,
  `dsCopyWords`, `dsStampList`, and `clearAuxGraph`, and proves `bucketsCat` has length
  `H_mid_union.m` and clears every `minH[e]` (`e < eCap`) to `0`.
* `stepZero_initCore_pre`: builds `dsInitCoreContract.pre` after `dsClearBuckets`,
  `dsClearAbove`, and `t := t + 1`.
* `stepZero_rebuild_post`: assembles `StepOutPost` (including `DynSpannerStateAt`,
  `RevHistoryInv`, `BatchBodyAt`, `uhActual.Perm res.UH`, `dL.toFinset = res.D`, `ZeroFrom`,
  and the frame below `heapStep`) after `dsInitCore` and the emit phase.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.DynSpanner

@[expose] public section

private lemma idx_lt_mul_z {i n e m : ℕ} (hi : i < n) (he : e < m) : i * m + e < n * m :=
  calc i * m + e < i * m + m := Nat.add_lt_add_left he _
    _ = (i + 1) * m := by ring
    _ ≤ n * m := Nat.mul_le_mul_right _ hi

/-- Build `dsStepPrefixContract.pre` from `DynSpannerStateAt` and the `j = 0` step preconditions. -/
theorem stepZero_prefix_pre {G₀ : MGraph} {impl : SparsifyImpl} {mMax w L q vCap eCap b k : ℕ}
    {us : List Update} {u : Update} {len updPtr heapStep : ℕ} {mem0 : ℕ → ℕ}
    {x : DynSpannerMeta L}
    (_hVG₀ : G₀.IsValid) (_hq : 1 ≤ q) (hBV : G₀.BatchIsValid us)
    (hds : ∀ u' ∈ us, isDelOrSplit u') (hu_some : us[k]? = some u)
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
    (hupd_at : UpdateAt mem0 updPtr (runState (L := L) G₀ q (canonicalSparsify impl) us k).G u len)
    (hupd_cap : UpdateWithinCaps vCap eCap u) :
    let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
    let B0 := fun i => if hi : i < L + 1 then x.hBuckets ⟨i, hi⟩ else []
    (dsStepPrefixContract w L vCap eCap b st.G st.H u len B0 (heapStep + 5)).pre
      [dsGPtr b, dsHPtr b vCap eCap, b, dsMinHBase b vCap eCap, updPtr,
        dgEPresBase (dsHPtr b vCap eCap) vCap, heapStep + 5] mem0 := by
  intro st B0
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
      simp only [B0, hi', ↓reduceDIte]
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
    simp only [B0, hi1, hi2, ↓reduceDIte] at he ⊢
    intro he2
    have h1 := ((hBuck ⟨i, hi1⟩).2.2 e).mp he
    have h2 := ((hBuck ⟨i', hi2⟩).2.2 e).mp he2
    dsimp only at h1 h2
    omega
  · have hi1 : i < L + 1 := by omega
    simp only [B0, hi1, ↓reduceDIte] at heB
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
    simp only [B0, i0.2, ↓reduceDIte]
    exact ((hBuck i0).2.2 e).mpr ⟨heH, hm⟩

private lemma stepZero_cb_addrs {w b L vCap eCap : ℕ}
    (hfix_w : b + dsFixedSize L vCap eCap < 2 ^ w) :
    dsMinHBase b vCap eCap + eCap = dsHNextBase b vCap eCap ∧
    dsHNextBase b vCap eCap + eCap = dsHPrevBase b vCap eCap ∧
    dsHPrevBase b vCap eCap + eCap = dsHHeadBase b vCap eCap ∧
    dsHHeadBase b vCap eCap + (L + 1) = dsHDegDummyBase b L vCap eCap ∧
    dsHDegDummyBase b L vCap eCap + (L + 1) = dsDomGenBase b L vCap eCap ∧
    dsDomGenBase b L vCap eCap ≤ b + dsFixedSize L vCap eCap ∧
    dsHNextBase b vCap eCap + eCap < 2 ^ w ∧
    dsMinHBase b vCap eCap + eCap < 2 ^ w ∧
    dsHHeadBase b vCap eCap + (L + 1) < 2 ^ w ∧
    dsHDegDummyBase b L vCap eCap + (L + 1) < 2 ^ w := by
  obtain ⟨_, _, _, _, hmn, hnp, hph, hhd, hdd, hde, hep, hpr, hrr, hrs, hsv, hvs, hsh, hsb, hve,
    hek, hkm, hmf⟩ := stepZero_fixed_order b L vCap eCap
  exact ⟨hmn, hnp, hph, hhd, hdd, by omega, by omega, by omega, by omega, by omega⟩

/-- After `dsStepPrefix`, `dsCopyWords` (old edges), `dsStampList`, and `clearAuxGraph`, build
`CBCtx` on levels `0..L`, prove `(bucketsCat Bmid 0 (L + 1)).length = H_mid_union.m`, and show
that `CBMem` from `dsClearBuckets` sets every `minH[e]` (`e < eCap`) to `0`. -/
theorem stepZero_clearBuckets_ctx {G₀ : MGraph} {impl : SparsifyImpl} {mMax w L q vCap eCap b k : ℕ}
    {us : List Update} {u : Update} {mem0 memPref memCur : ℕ → ℕ} {x : DynSpannerMeta L}
    (hBV : G₀.BatchIsValid us) (hds : ∀ u' ∈ us, isDelOrSplit u') (hu_some : us[k]? = some u)
    (hPref : ∀ s ≤ k, SnapInv G₀ L q mMax (canonicalSparsifyParams impl mMax).absorbTime
      (canonicalSparsify impl) us s)
    (hw16 : 16 ≤ 2 ^ w)
    (hState : DynSpannerStateAt L vCap eCap b mem0 x
      (runState (L := L) G₀ q (canonicalSparsify impl) us k))
    (hfix_w : b + dsFixedSize L vCap eCap < 2 ^ w)
    (hBpref : BucketsAt memPref L vCap eCap b
      (fun i => delErase u (if hi : i < L + 1 then x.hBuckets ⟨i, hi⟩ else [])))
    (hminPref : ∀ e < eCap, memPref (dsMinHBase b vCap eCap + e) =
      minHAfter u (mem0 (dsMinHBase b vCap eCap + e)) e)
    (hag : ∀ addr, dsMinHBase b vCap eCap ≤ addr → addr < dsDomGenBase b L vCap eCap →
      memCur addr = memPref addr) :
    let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
    let H_mid_union := st.H.applyBatch (restrictUpdate u st.H)
    let Bmid := fun i => delErase u (if hi : i < L + 1 then x.hBuckets ⟨i, hi⟩ else [])
    ∃ c : CBCtx,
      c.w = w ∧ c.eCap = eCap ∧ c.B = Bmid ∧ c.lo = 0 ∧ c.hi = L + 1 ∧
      c.prevBase = dsHPrevBase b vCap eCap ∧ c.nextBase = dsHNextBase b vCap eCap ∧
      c.headBase = dsHHeadBase b vCap eCap ∧ c.degBase = dsHDegDummyBase b L vCap eCap ∧
      c.minH = dsMinHBase b vCap eCap ∧ c.mem0 = memCur ∧
      (bucketsCat Bmid 0 (L + 1)).length = H_mid_union.m ∧
      (∀ e, e ∈ bucketsCat Bmid 0 (L + 1) ↔ e ∈ H_mid_union.E) ∧
      (∀ memAfter, CBMem c (bucketsCat Bmid 0 (L + 1)) (L + 1) memAfter →
        (∀ e < eCap, memAfter (dsMinHBase b vCap eCap + e) = 0) ∧
        (∀ i : Fin (L + 1),
          IsDoublyLinkedList memAfter (dsHPrevBase b vCap eCap) (dsHNextBase b vCap eCap)
            (dsHHeadBase b vCap eCap + i.1) eCap [] ∧
          memAfter (dsHDegDummyBase b L vCap eCap + i.1) = 0)) := by
  intro st H_mid_union Bmid
  have hk_inv := hPref k le_rfl
  obtain ⟨_, _, hU_k⟩ := batchIsValid_take us G₀ k hBV hds
  obtain ⟨hu_val, hdu⟩ := hU_k u hu_some
  rcases hState with ⟨_, _, _, _, _, _, _, hHEsub, _, _, hGE_cap,
    _, _, _, _, _, _, _, _, _, hminH0, hBuck0, _, _, _, _⟩
  obtain ⟨hmn, hnp, hph, hhd, hdd, _, hnB, hmB, hhB, hdB⟩ := stepZero_cb_addrs hfix_w
  have hBk_cur : BucketsAt memCur L vCap eCap b Bmid := hBpref.of_agree_range hag
  have hmin_cur : ∀ e < eCap, memCur (dsMinHBase b vCap eCap + e) =
      minHAfter u (mem0 (dsMinHBase b vCap eCap + e)) e := fun e he =>
    (hag _ (Nat.le_add_right _ _) (by omega)).trans (hminPref e he)
  let H_mid : Fin (L + 1) → MGraph :=
    fun i => (st.H_level i).applyBatch (restrictUpdate u (st.H_level i))
  have hmin_after := minH_after_update hdu
    (m := fun e => mem0 (dsMinHBase b vCap eCap + e))
    (m' := fun e => memPref (dsMinHBase b vCap eCap + e))
    (H_level := st.H_level) (H_mid := H_mid)
    (B := fun i => if hi : i < L + 1 then x.hBuckets ⟨i, hi⟩ else [])
    (fun e he => (hminH0 e he).1) (fun e he => (hminH0 e he).2)
    (fun i e => by simpa [i.2] using (hBuck0 i).2.2 e)
    (fun i => by simpa [i.2] using (hBuck0 i).1.1)
    hminPref (fun i => mid_E_delSet hdu (st.H_level i))
    (fun e heq => hGE_cap e (by rw [heq] at hu_val; exact hk_inv.G_eq ▸ hu_val))
  have hHmid_E : H_mid_union.E = delSet u st.H.E := mid_E_delSet hdu st.H
  have hHmid_sub : H_mid_union.E ⊆ st.G.E := by
    rw [hHmid_E]
    cases u with
    | insert _ _ _ => exact hdu.elim
    | delete _ => exact Finset.Subset.trans (Finset.erase_subset _ _) hHEsub
    | split _ _ _ _ => exact hHEsub
  have hBmid_iff : ∀ i : Fin (L + 1), ∀ e,
      e ∈ Bmid i.1 ↔ e ∈ H_mid_union.E ∧ memCur (dsMinHBase b vCap eCap + e) = i.1 + 1 := by
    intro i e
    by_cases heC : e < eCap
    · rw [hmin_cur e heC, ← hminPref e heC, hHmid_E]
      exact hmin_after.2 i e heC
    · constructor
      · intro hmem; exact (heC ((hBk_cur i.1 (by omega)).1.2.1 e hmem)).elim
      · rintro ⟨heH, _⟩; exact (heC (hGE_cap e (hHmid_sub heH))).elim
  have hcat_nd : (bucketsCat Bmid 0 (L + 1)).Nodup := by
    refine bucketsCat_nodup (fun i _ hi => (hBk_cur i (by omega)).1.1)
      (fun i₁ i₂ _ h1 _ h2 hne e he1 he2 => ?_)
    have a1 := (hBmid_iff ⟨i₁, by omega⟩ e).mp he1
    have a2 := (hBmid_iff ⟨i₂, by omega⟩ e).mp he2
    dsimp only at a1 a2
    omega
  have hcat_iff : ∀ e, e ∈ bucketsCat Bmid 0 (L + 1) ↔ e ∈ H_mid_union.E := by
    intro e
    rw [mem_bucketsCat]
    constructor
    · rintro ⟨i, _, hi, hei⟩
      exact ((hBmid_iff ⟨i, by omega⟩ e).mp hei).1
    · intro heH
      have heC : e < eCap := hGE_cap e (hHmid_sub heH)
      obtain ⟨i, hi_eq, _, _⟩ := (hmin_after.1 e heC).2 (hHmid_E ▸ heH)
      refine ⟨i.1, Nat.zero_le _, by have := i.2; omega, (hBmid_iff i e).mpr ⟨heH, ?_⟩⟩
      rw [hmin_cur e heC, ← hminPref e heC]
      exact hi_eq
  have hcat_len : (bucketsCat Bmid 0 (L + 1)).length = H_mid_union.m := by
    have hfin : (bucketsCat Bmid 0 (L + 1)).toFinset = H_mid_union.E := by
      ext e; simp [hcat_iff]
    rw [← List.toFinset_card_of_nodup hcat_nd, hfin]; rfl
  let c : CBCtx :=
    { w := w, eCap := eCap, B := Bmid, lo := 0, hi := L + 1,
      prevBase := dsHPrevBase b vCap eCap, nextBase := dsHNextBase b vCap eCap,
      headBase := dsHHeadBase b vCap eCap, degBase := dsHDegDummyBase b L vCap eCap,
      minH := dsMinHBase b vCap eCap, mem0 := memCur,
      hle := Nat.zero_le _, hw16 := hw16,
      hnB := hnB, hmB := hmB, hhB := hhB, hdB := hdB,
      dMN := Or.inl (le_of_eq hmn),
      dMH := Or.inl (by omega),
      dMD := Or.inl (by omega),
      dNH := Or.inl (by omega),
      dND := Or.inl (by omega),
      dHD := Or.inl (by simp only [Nat.add_zero, Nat.sub_zero]; exact le_of_eq hhd),
      hB := fun i _ hi => hBk_cur i (by omega) }
  refine ⟨c, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hcat_len, hcat_iff,
    fun memAfter hCB => ?_⟩
  rcases hCB with ⟨hzm, hzh, hfr⟩
  refine ⟨fun e he => ?_, fun i => ?_⟩
  · by_cases heH : e ∈ H_mid_union.E
    · exact hzm e ((hcat_iff e).mpr heH)
    · have hne1 : ∀ x ∈ bucketsCat Bmid 0 (L + 1), dsMinHBase b vCap eCap + e ≠ dsMinHBase b vCap eCap + x := by
        intro x hx hEq
        exact heH ((hcat_iff e).mp ((Nat.add_left_cancel hEq) ▸ hx))
      have hne2 : ∀ i', 0 ≤ i' → i' < L + 1 →
          dsMinHBase b vCap eCap + e ≠ dsHHeadBase b vCap eCap + i' ∧
          dsMinHBase b vCap eCap + e ≠ dsHDegDummyBase b L vCap eCap + i' := fun i' _ _ =>
        ⟨by omega, by omega⟩
      rw [hfr _ hne1 hne2]; dsimp only [c]; rw [hmin_cur e he, ← hminPref e he]
      exact (hmin_after.1 e he).1.mpr (hHmid_E ▸ heH)
  · obtain ⟨hh0, hd0⟩ := hzh i.1 (Nat.zero_le _) i.2
    exact ⟨IsDoublyLinkedList.nil hh0, hd0⟩

/-- Assemble `StepOutPost` and the heap/generation bounds for `dsStepZeroStmt` from the
postconditions of `dsInitCoreStmt` and the emit phase. -/
theorem stepZero_rebuild_post {G₀ : MGraph} {impl : SparsifyImpl} {mMax L q vCap eCap b k : ℕ}
    {us : List Update} {u : Update} {len heapStep heapInit retInit : ℕ}
    {prefWords delCnt insCnt uhPtr uhLen uhWords dPtr retFinal gOld : ℕ}
    {oldHEdges dL buck0 : List ℕ} {rev0 : ℕ → List ℕ}
    {mem0 memCore memFinal : ℕ → ℕ} {x : DynSpannerMeta L}
    (hVG₀ : G₀.IsValid) (hL1 : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hBV : G₀.BatchIsValid us) (hds : ∀ u' ∈ us, isDelOrSplit u') (hu_some : us[k]? = some u)
    (hPref : ∀ s ≤ k, SnapInv G₀ L q mMax (canonicalSparsifyParams impl mMax).absorbTime
      (canonicalSparsify impl) us s)
    (hj0 : chooseLevel L q (k + 1) = 0)
    (hState : DynSpannerStateAt L vCap eCap b mem0 x
      (runState (L := L) G₀ q (canonicalSparsify impl) us k))
    (hupd_cap : UpdateWithinCaps vCap eCap u)
    (hfix : b + dsFixedSize L vCap eCap ≤ heapStep)
    (hheap_ar : heapStep + 5 ≤ heapInit ∧ heapInit ≤ retInit ∧
      retInit = dPtr ∧ uhPtr = dPtr + dL.length ∧
      uhWords = prefWords + 2 * delCnt + 4 * insCnt ∧
      retFinal = uhPtr + uhWords ∧
      uhLen = (if prefWords = 0 then 0 else 1) + delCnt + insCnt ∧
      retInit ≤ heapInit + dsInitCoreSpaceBound impl mMax vCap eCap
        ((runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u) ∧
      heapInit = heapStep + 5 + len + oldHEdges.length ∧
      prefWords ≤ len)
    (hgen_eq : memFinal (b + dsGenOff) = gOld + 1 +
      ((runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u).m ∧
      gOld = mem0 (b + dsGenOff) + 1)
    (hHdrF :
      memFinal heapStep = uhPtr ∧ memFinal (heapStep + 1) = uhLen ∧
      memFinal (heapStep + 2) = uhWords ∧ memFinal (heapStep + 3) = dPtr ∧
      memFinal (heapStep + 4) = dL.length)
    (hFixedAg : ∀ addr, b ≤ addr → addr < b + dsFixedSize L vCap eCap →
      memFinal addr = memCore addr)
    (hWalkAg : ∀ addr, heapInit ≤ addr → addr < retInit → memFinal addr = memCore addr)
    (hFrameLt : ∀ a < heapStep, ¬ metaFoot b x a → memFinal a = mem0 a)
    (hzFinal : ZeroFrom memFinal retFinal)
    (hHdrCore :
      memCore (b + dsQOff) = q ∧ memCore (b + dsTOff) = k + 1 ∧
      memCore (b + dsLOff) = L ∧ memCore (b + dsVCapOff) = vCap ∧ memCore (b + dsECapOff) = eCap ∧
      memCore (b + dsGenOff) = gOld + 1 +
        ((runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u).m ∧
      memCore (dsDomGenBase b L vCap eCap) = gOld + 1)
    (hGraphsCore :
      let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
      let G' := st.G.applyUpdate u
      let H₀ := (initCore G' (canonicalSparsify impl)).1
      DynGraphAt memCore (dsGPtr b) vCap eCap G' ∧
      DynGraphAt memCore (dsHPtr b vCap eCap) vCap eCap H₀ ∧
      DynGraphAt memCore (dsAuxPtr b vCap eCap) vCap eCap emptyMGraph)
    (hCoreArrays :
      let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
      let G' := st.G.applyUpdate u
      let core := initCore G' (canonicalSparsify impl)
      let H₀ := core.1
      let Pi₀ := core.2.1
      (∀ e < eCap, (memCore (dsMinHBase b vCap eCap + e) = 0 ↔ e ∉ H₀.E) ∧
        (e ∈ H₀.E → memCore (dsMinHBase b vCap eCap + e) = 1)) ∧
      IsDoublyLinkedList memCore (dsHPrevBase b vCap eCap) (dsHNextBase b vCap eCap)
        (dsHHeadBase b vCap eCap) eCap buck0 ∧
      memCore (dsHDegDummyBase b L vCap eCap) = buck0.length ∧
      (∀ e, e ∈ buck0 ↔ e ∈ H₀.E) ∧
      (∀ i : Fin (L + 1), 0 < i.1 →
        IsDoublyLinkedList memCore (dsHPrevBase b vCap eCap) (dsHNextBase b vCap eCap)
          (dsHHeadBase b vCap eCap + i.1) eCap [] ∧
        memCore (dsHDegDummyBase b L vCap eCap + i.1) = 0 ∧
        memCore (dsDomGenBase b L vCap eCap + i.1) = 0 ∧
        (∀ e < eCap, memCore (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e) ≤ memCore (b + dsGenOff)) ∧
        (∀ v < vCap, memCore (dsRevGenBase b L vCap eCap + i.1 * vCap + v) ≤ memCore (b + dsGenOff))) ∧
      (∀ e < eCap, memCore (dsEdgeDomGenBase b L vCap eCap + e) ≤ memCore (b + dsGenOff)) ∧
      (∀ e < eCap, (0 < memCore (dsDomGenBase b L vCap eCap) ∧
        memCore (dsEdgeDomGenBase b L vCap eCap + e) = memCore (dsDomGenBase b L vCap eCap)) ↔
          e ∈ G'.E) ∧
      (∀ e ∈ G'.E, let ptr := memCore (dsPiPtrBase b L vCap eCap + e)
        MWalkAt memCore ptr (Pi₀ e) ∧ heapInit ≤ ptr ∧ ptr + (mWalkEncode (Pi₀ e)).length ≤ retInit) ∧
      (∀ v < vCap, memCore (dsRevGenBase b L vCap eCap + v) ≤ memCore (b + dsGenOff) ∧
        (rev0 v).Nodup ∧ (∀ e, e ∈ rev0 v ↔ e ∈ G'.E ∧ v ∈ H₀.walkVertices (G'.tail e) (Pi₀ e)) ∧
        (if 0 < memCore (dsDomGenBase b L vCap eCap) ∧
            memCore (dsRevGenBase b L vCap eCap + v) = memCore (dsDomGenBase b L vCap eCap)
         then LinkedListIn (fun a => heapInit ≤ a ∧ a < retInit) memCore
                (memCore (dsRevHeadBase b L vCap eCap + v)) (rev0 v)
         else rev0 v = [])) ∧
      (∀ i : Fin (L + 1), memCore (dsSGenBase b L vCap eCap + i.1) = 0 ∧
        ∀ v < vCap, memCore (dsVSGenBase b L vCap eCap + i.1 * vCap + v) ≤ memCore (b + dsGenOff)) ∧
      (∀ v < vCap, memCore (dsSBitBase b L vCap eCap + v) = 0 ∧
        memCore (dsVStampBase b L vCap eCap + v) ≤ memCore (b + dsGenOff)) ∧
      (∀ e < eCap, memCore (dsEStampBase b L vCap eCap + e) ≤ memCore (b + dsGenOff) ∧
        memCore (dsKeptStampBase b L vCap eCap + e) ≤ memCore (b + dsGenOff)))
    (hOldE :
      let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
      let H_mid := st.H.applyBatch (restrictUpdate u st.H)
      oldHEdges.Nodup ∧ (∀ e, e ∈ oldHEdges ↔ e ∈ H_mid.E) ∧ oldHEdges.length = H_mid.m)
    (hDList :
      let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
      let H₀ := (initCore (st.G.applyUpdate u) (canonicalSparsify impl)).1
      dL.Nodup ∧ (∀ e, e ∈ dL ↔ e ∈ H₀.E) ∧ dL.length = H₀.m ∧ ListAt memFinal dPtr dL)
    (hUHBat :
      let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
      let G' := st.G.applyUpdate u
      let H_mid := st.H.applyBatch (restrictUpdate u st.H)
      let H₀ := (initCore G' (canonicalSparsify impl)).1
      BatchBodyAt memFinal uhPtr st.H (restrictUpdate u st.H) prefWords ∧
      delCnt = (delList H₀.E oldHEdges).length ∧
      ListAt memFinal (uhPtr + prefWords) (delWords H₀.E oldHEdges) ∧
      insCnt = (insList H_mid.E dL).length ∧
      ListAt memFinal (uhPtr + prefWords + 2 * delCnt) (insWords G' H_mid.E dL)) :
    let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
    let G' := st.G.applyUpdate u
    let H₀ := (initCore G' (canonicalSparsify impl)).1
    StepOutPost G₀ L q vCap eCap b k impl us u mem0 x heapStep memFinal retFinal ∧
    heapStep + 5 ≤ retFinal ∧
    retFinal ≤ heapStep + dsStepZeroSpace impl mMax vCap eCap G' st.H H₀ len ∧
    memFinal (b + dsGenOff) ≤ mem0 (b + dsGenOff) + 2 + G'.m ∧
    memFinal (heapStep + 2) ≤ len + 4 * (step st u (canonicalSparsify impl)).UH.length := by
  intro st G' H₀
  set res := step st u (canonicalSparsify impl)
  set H_mid := st.H.applyBatch (restrictUpdate u st.H)
  set Pi₀ := (initCore G' (canonicalSparsify impl)).2.1
  have hk_inv := hPref k le_rfl
  obtain ⟨_, _, hU_k⟩ := batchIsValid_take us G₀ k hBV hds
  obtain ⟨hu_val, hdu⟩ := hU_k u hu_some
  have hnext_inv := step_inv hVG₀ hL1 hq hGm₀ (canonicalSparsify_spec_absorb impl mMax) hBV hds
    hu_some hPref
  rcases hnext_inv with ⟨hk1_inv, _⟩
  have hst1_eq : runState (L := L) G₀ q (canonicalSparsify impl) us (k + 1) = res.state := by
    simp only [runState, res, st, hu_some]
  have hcl_eq : chooseLevel L st.q (st.t + 1) = 0 := by rw [hk_inv.q_eq, hk_inv.t_eq, hj0]
  rcases hState with ⟨hxV, hxE, hxiv, hb1, hGval, _, hHV0, hHEsub0, hHends0, hGV_cap, hGE_cap,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  have hSub0 : st.G.IsSubgraph st.H := ⟨hHV0.subset, hHEsub0, hHends0⟩
  have hG'val : G'.IsValid := isValid_applyUpdate_of_delOrSplit hGval (hk_inv.G_eq ▸ hu_val) hdu
  have hG'E_sub : G'.E ⊆ st.G.E := E_applyUpdate_subset hdu
  have hGE'_cap : ∀ e ∈ G'.E, e < eCap := fun e he => hGE_cap e (hG'E_sub he)
  have hGV'_cap : ∀ v ∈ G'.V, v < vCap := by
    intro v hv
    cases u with
    | insert _ _ _ => exact hdu.elim
    | delete _ => exact hGV_cap v hv
    | split _ v' _ _ =>
      simp only [G', MGraph.applyUpdate, Finset.mem_insert] at hv
      rcases hv with rfl | hv
      · exact hupd_cap
      · exact hGV_cap v hv
  have hG'm_le : G'.m ≤ mMax := by
    have h1 : G'.E ⊆ G₀.E := Finset.Subset.trans hG'E_sub (by
      rw [hk_inv.G_eq]
      obtain ⟨hBV_k, hds_k, _⟩ := batchIsValid_take us G₀ k hBV hds
      exact (batch_delOrSplit_invariants (us.take k) G₀ hVG₀ hBV_k hds_k).2.1)
    exact le_trans (Finset.card_le_card h1) hGm₀
  have hCoreSpec := initCore_spec (canonicalSparsify_spec_absorb impl mMax) hG'val hG'm_le
  rcases hCoreSpec with ⟨_, hH₀_sub, hH₀_V, hPi₀_emb, _, _, _, _⟩
  -- Express `res` fields cleanly when `j = 0`.
  have hres_q : res.state.q = q := by
    dsimp only [res, step]; rw [dite_eq_left_of_eq_true (eq_true hcl_eq)]; exact hk_inv.q_eq
  have hres_t : res.state.t = k + 1 := by
    dsimp only [res, step]; rw [dite_eq_left_of_eq_true (eq_true hcl_eq)]
    exact congrArg (· + 1) hk_inv.t_eq
  have hres_G : res.state.G = G' := by
    dsimp only [res, step, G']; rw [dite_eq_left_of_eq_true (eq_true hcl_eq)]
    rfl
  have hres_Hlevel : ∀ i : Fin (L + 1), res.state.H_level i =
      if i.1 = 0 then H₀ else emptyGraphOn G' := fun i => by
    dsimp only [res, step, H₀, G']; rw [dite_eq_left_of_eq_true (eq_true hcl_eq)]; rfl
  have hres_Pi : ∀ i : Fin (L + 1), res.state.Pi_level i =
      if i.1 = 0 then Pi₀ else fun _ => [] := fun i => by
    dsimp only [res, step, Pi₀, G']; rw [dite_eq_left_of_eq_true (eq_true hcl_eq)]; rfl
  have hres_inDom : ∀ i : Fin (L + 1), res.state.inDom i =
      if i.1 = 0 then G'.E else ∅ := fun i => by
    dsimp only [res, step, G']; rw [dite_eq_left_of_eq_true (eq_true hcl_eq)]; rfl
  have hres_S : ∀ i : Fin (L + 1), res.state.S_level i = ∅ := fun i => by
    dsimp only [res, step]; rw [dite_eq_left_of_eq_true (eq_true hcl_eq)]; rfl
  have hres_D : res.D = res.state.H.E := by
    dsimp only [res, step]; rw [dite_eq_left_of_eq_true (eq_true hcl_eq)]
  have hH'_E : res.state.H.E = H₀.E := by
    have h1 := hk1_inv.H_E
    rw [hst1_eq] at h1
    rw [h1]
    ext e
    simp only [unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, _, hei⟩
      rw [hres_Hlevel i] at hei
      by_cases hi0 : i.1 = 0
      · simpa [hi0] using hei
      · simp [hi0, emptyGraphOn] at hei
    · intro he
      refine ⟨⟨0, Nat.zero_lt_succ L⟩, Nat.zero_lt_succ L, ?_⟩
      rw [hres_Hlevel ⟨0, Nat.zero_lt_succ L⟩]
      exact he
  have hH'_sub : G'.IsSubgraph res.state.H := by
    have h := hk1_inv.H_sub
    have hG1 : G₀.applyBatch (us.take (k + 1)) = G' := by
      rw [← hk1_inv.G_eq, hst1_eq, hres_G]
    rw [hst1_eq, hG1] at h
    exact h
  have hH'_V : res.state.H.V = G'.V := by
    have h := hk1_inv.H_V
    have hG1 : G₀.applyBatch (us.take (k + 1)) = G' := by
      rw [← hk1_inv.G_eq, hst1_eq, hres_G]
    rw [hst1_eq, hG1] at h
    exact h
  have hH'_val : res.state.H.IsValid := by
    have h := hk1_inv.H_valid
    rwa [hst1_eq] at h
  -- Unsorted `U_H` batch assembly and permutation bridge.
  rcases hOldE with ⟨hold_nd, hold_mem, hold_len⟩
  rcases hDList with ⟨hdL_nd, hdL_mem, hdL_len, hdL_at⟩
  rcases hUHBat with ⟨hPrefBat, hdelCnt, hDelWords, hinsCnt, hInsWords⟩
  set lDel := delList H₀.E oldHEdges
  set lIns := insList H_mid.E dL
  set uhActual := restrictUpdate u st.H ++ lDel.map Update.delete ++ insRecs G' H_mid.E dL
  have hdiff := diffBatch_perm_props (lDel := lDel) (lIns := lIns) hGval hSub0 hHV0
    (hk_inv.G_eq ▸ hu_val) hdu hH₀_sub.2.1 (hold_nd.filter _)
    (fun e => by simp only [lDel, mem_delList, hold_mem, Finset.mem_sdiff]; rfl)
    (hdL_nd.filter _)
    (fun e => by simp only [lIns, mem_insList, hdL_mem, Finset.mem_sdiff]; rfl)
  have huh_perm : uhActual.Perm res.UH := by
    have hres_UH : res.UH = restrictUpdate u st.H ++
        ((H_mid.E \ H₀.E).sort (· ≤ ·)).map Update.delete ++
        ((H₀.E \ H_mid.E).sort (· ≤ ·)).map (fun e => Update.insert e (G'.tail e) (G'.head e)) := by
      dsimp only [res, step, H_mid, H₀, G']
      rw [dite_eq_left_of_eq_true (eq_true hcl_eq)]
      rfl
    rw [hres_UH]
    exact hdiff.1
  have hPrefBat' : BatchBodyAt memFinal uhPtr st.H (restrictUpdate u st.H) prefWords := hPrefBat
  have huh_len_eq : uhActual.length = uhLen := by
    have hplen : (restrictUpdate u st.H).length = if prefWords = 0 then 0 else 1 :=
      restrictUpdate_length_eq_ite hdu hPrefBat'
    simp only [uhActual, insRecs, List.length_append, List.length_map, hplen, hheap_ar.2.2.2.2.2.2.1,
      hdelCnt, hinsCnt, lDel, lIns]
  have huh_bat : BatchBodyAt memFinal uhPtr st.H uhActual uhWords := by
    have hbDel := delRecs_batchBodyAt (mem := memFinal) H_mid H₀.E oldHEdges (uhPtr + prefWords)
      hDelWords
    have hbIns := insRecs_batchBodyAt (mem := memFinal) G'
      (H_mid.applyBatch (lDel.map Update.delete)) H_mid.E dL (uhPtr + prefWords + 2 * delCnt)
      hInsWords
    have h1 := batchBodyAt_append hPrefBat' (by simpa [H_mid, hdelCnt, lDel] using hbDel)
    have h2 := batchBodyAt_append h1 (by
      simpa [H_mid, applyBatch_append, Nat.add_assoc, hdelCnt, hinsCnt, lDel, lIns] using hbIns)
    rw [hheap_ar.2.2.2.2.1, Nat.add_assoc]
    simpa [uhActual, List.append_assoc, hdelCnt, hinsCnt, lDel, lIns, Nat.add_assoc] using h2
  -- Space bound.
  have hold_le : oldHEdges.length ≤ st.H.m := by
    rw [hold_len]
    have hE := mid_E_delSet hdu st.H
    have hsub : H_mid.E ⊆ st.H.E := by
      rw [hE]
      cases u with
      | insert _ _ _ => exact hdu.elim
      | delete _ => exact Finset.erase_subset _ _
      | split _ _ _ _ => exact Finset.Subset.rfl
    exact Finset.card_le_card hsub
  have hdel_le : delCnt ≤ oldHEdges.length := hdelCnt ▸ delList_length_le H₀.E oldHEdges
  have hins_le : insCnt ≤ dL.length := hinsCnt ▸ insList_length_le H_mid.E dL
  have hret_le : retFinal ≤ heapStep + dsStepZeroSpace impl mMax vCap eCap G' st.H H₀ len := by
    rcases hheap_ar with ⟨_, _, hr_d, hu_d, huw, hrf, _, hri_le, hhi, hpw⟩
    change retInit ≤ heapInit + dsInitCoreSpaceBound impl mMax vCap eCap G' at hri_le
    have hdL_len' : dL.length = H₀.m := hdL_len
    dsimp only [dsStepZeroSpace]
    omega
  -- Build metadata `x'`.
  let x' : DynSpannerMeta L :=
    { vCap := vCap, eCap := eCap, intervals := x.intervals ++ [(heapStep, retFinal)],
      hBuckets := fun i => if i.1 = 0 then buck0 else [],
      memInDom := fun i => if i.1 = 0 then G'.E else ∅,
      revLists := fun i v => if i.1 = 0 then rev0 v else [],
      sLists := fun _ => [] }
  have hmem_in : ∀ addr, b ≤ addr → addr < b + dsFixedSize L vCap eCap →
      memFinal addr = memCore addr := hFixedAg
  obtain ⟨hF_hdr, hF_G, hF_H, hF_A, hF_min, hF_prev, hF_next, hF_head, hF_deg, hF_dom,
    hF_edom, hF_pi, hF_rg, hF_rh, hF_sg, hF_vsg, hF_sbit, hF_vst, hF_est, hF_kst⟩ :=
    stepZero_fixed_lt b L vCap eCap
  have hgenF_eq : memFinal (b + dsGenOff) = memCore (b + dsGenOff) :=
    hmem_in _ (hF_hdr dsGenOff (by decide)).1 (hF_hdr dsGenOff (by decide)).2
  -- Helper: `H₀` and `res.state.H` have identical `V, E` and endpoints on `E`.
  have hH₀_ends_H' : ∀ e ∈ H₀.E, H₀.tail e = res.state.H.tail e ∧ H₀.head e = res.state.H.head e :=
    fun e he => by
      have he' : e ∈ res.state.H.E := hH'_E.symm ▸ he
      exact ⟨(hH₀_sub.2.2 e he).1.trans (hH'_sub.2.2 e he').1.symm,
        (hH₀_sub.2.2 e he).2.trans (hH'_sub.2.2 e he').2.symm⟩
  have hH'_sub_H₀ : res.state.H.IsSubgraph H₀ :=
    ⟨(hH₀_V.trans hH'_V.symm).subset, hH'_E.symm.subset, fun e he => hH₀_ends_H' e he⟩
  have hfoot_new : ∀ a, heapInit ≤ a → a < retInit → heapFoot x' a := fun a ha1 ha2 =>
    ⟨(heapStep, retFinal), List.mem_append_right _ List.mem_cons_self, by omega, by omega⟩
  have hStateFinal : DynSpannerStateAt L vCap eCap b memFinal x' res.state := by
    rcases hGraphsCore with ⟨hGC, hHC, hAuxC⟩
    rcases hCoreArrays with ⟨hminC, hdll0C, hdeg0C, hbuck0C, hPosC, hedLe0C, hed0C, hpi0C,
      hrev0C, hSC, hvSC, heSC⟩
    refine ⟨rfl, rfl, fun iv hiv => ?_, hb1, hres_G ▸ hG'val, hH'_val, hres_G ▸ hH'_V,
      hres_G ▸ hH'_sub.2.1, hres_G ▸ hH'_sub.2.2, hres_G ▸ hGV'_cap, hres_G ▸ hGE'_cap,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rcases List.mem_append.mp hiv with hiv | hiv
      · exact hxiv iv hiv
      · simp only [List.mem_singleton] at hiv; subst hiv; exact hfix
    · rw [hmem_in _ (hF_hdr dsQOff (by decide)).1 (hF_hdr dsQOff (by decide)).2, hHdrCore.1, hres_q]
    · rw [hmem_in _ (hF_hdr dsTOff (by decide)).1 (hF_hdr dsTOff (by decide)).2, hHdrCore.2.1, hres_t]
    · rw [hmem_in _ (hF_hdr dsLOff (by decide)).1 (hF_hdr dsLOff (by decide)).2, hHdrCore.2.2.1]
    · rw [hmem_in _ (hF_hdr dsVCapOff (by decide)).1 (hF_hdr dsVCapOff (by decide)).2, hHdrCore.2.2.2.1]
    · rw [hmem_in _ (hF_hdr dsECapOff (by decide)).1 (hF_hdr dsECapOff (by decide)).2, hHdrCore.2.2.2.2.1]
    · rw [hgenF_eq, hHdrCore.2.2.2.2.2.1]; exact Nat.le_add_right_of_le (Nat.succ_le_succ (Nat.zero_le _))
    · rw [hres_G]
      exact dynGraphAt_of_agree hGC fun a h1 h2 =>
        hmem_in a (le_trans hF_G.1 h1) (lt_of_lt_of_le h2 hF_G.2)
    · exact dynGraphAt_congr (hH₀_V.trans hH'_V.symm) hH'_E.symm hH₀_ends_H'
        (dynGraphAt_of_agree hHC fun a h1 h2 =>
          hmem_in a (le_trans hF_H.1 h1) (lt_of_lt_of_le h2 hF_H.2))
    · exact dynGraphAt_of_agree hAuxC fun a h1 h2 =>
        hmem_in a (le_trans hF_A.1 h1) (lt_of_lt_of_le h2 hF_A.2)
    · -- `minH`
      intro e he
      rw [hmem_in _ (hF_min e he).1 (hF_min e he).2, hH'_E]
      refine ⟨(hminC e he).1, fun heH => ⟨⟨0, Nat.zero_lt_succ L⟩, (hminC e he).2 heH, ?_,
        fun k' hk' => by simp at hk'⟩⟩
      have h0l : res.state.H_level ⟨0, Nat.zero_lt_succ L⟩ = H₀ := by
        simpa using hres_Hlevel ⟨0, Nat.zero_lt_succ L⟩
      change e ∈ (res.state.H_level ⟨0, Nat.zero_lt_succ L⟩).E
      rw [h0l]; exact heH
    · -- `hBuckets`
      intro i
      by_cases hi0 : i.1 = 0
      · simp only [x', hi0, Nat.add_zero, ↓reduceIte]
        have h0lt : 0 < L + 1 := Nat.zero_lt_succ L
        refine ⟨hdll0C.of_agree
          (hmem_in _ (by simpa using (hF_head 0 h0lt).1) (by simpa using (hF_head 0 h0lt).2))
          (fun e he => hmem_in _ (hF_prev e (hdll0C.2.1 e he)).1 (hF_prev e (hdll0C.2.1 e he)).2)
          (fun e he => hmem_in _ (hF_next e (hdll0C.2.1 e he)).1 (hF_next e (hdll0C.2.1 e he)).2),
          (hmem_in _ (by simpa using (hF_deg 0 h0lt).1) (by simpa using (hF_deg 0 h0lt).2)).trans hdeg0C,
          fun e => ?_⟩
        rw [hbuck0C e, hH'_E]
        constructor
        · intro heH
          have heC : e < eCap := hGE'_cap e (hH₀_sub.2.1 heH)
          exact ⟨heH, (hmem_in _ (hF_min e heC).1 (hF_min e heC).2).trans ((hminC e heC).2 heH)⟩
        · exact fun h => h.1
      · have hi_pos : 0 < i.1 := Nat.pos_of_ne_zero hi0
        obtain ⟨hdllI, hdegI, _, _, _⟩ := hPosC i hi_pos
        simp only [x', hi0, ↓reduceIte]
        refine ⟨IsDoublyLinkedList.nil
            ((hmem_in _ (hF_head i.1 i.2).1 (hF_head i.1 i.2).2).trans hdllI.2.2.1),
          (hmem_in _ (hF_deg i.1 i.2).1 (hF_deg i.1 i.2).2).trans hdegI, fun e => ?_⟩
        refine ⟨by simp, fun ⟨heH, hm_eq⟩ => ?_⟩
        have heC : e < eCap := hGE'_cap e (hH₀_sub.2.1 (hH'_E ▸ heH))
        have h1 : memFinal (dsMinHBase b vCap eCap + e) = 1 :=
          (hmem_in _ (hF_min e heC).1 (hF_min e heC).2).trans ((hminC e heC).2 (hH'_E ▸ heH))
        omega
    · -- `inDom`, `Pi_level`, `revLists`
      intro i
      by_cases hi0 : i.1 = 0
      · have h0lt : 0 < L + 1 := Nat.zero_lt_succ L
        simp only [x', hi0, Nat.zero_mul, Nat.add_zero, ↓reduceIte]
        have hdom_ag : memFinal (dsDomGenBase b L vCap eCap) = memCore (dsDomGenBase b L vCap eCap) :=
          hmem_in _ (by simpa using (hF_dom 0 h0lt).1) (by simpa using (hF_dom 0 h0lt).2)
        refine ⟨by rw [hdom_ag, hgenF_eq, hHdrCore.2.2.2.2.2.2, hHdrCore.2.2.2.2.2.1]; exact Nat.le_add_right _ _,
          fun e he => ?_, hGE'_cap, ?_, fun e he => ?_, fun v hv => ?_⟩
        · have he_ag : memFinal (dsEdgeDomGenBase b L vCap eCap + e) =
              memCore (dsEdgeDomGenBase b L vCap eCap + e) :=
            hmem_in _ (by simpa using (hF_edom 0 h0lt e he).1) (by simpa using (hF_edom 0 h0lt e he).2)
          rw [he_ag, hgenF_eq, hdom_ag]
          exact ⟨hedLe0C e he, hed0C e he⟩
        · rw [hres_inDom i, hres_G]; simp [hi0]
        · rw [hres_inDom i] at he; simp only [hi0, ↓reduceIte] at he
          have heC : e < eCap := hGE'_cap e he
          have hpi_ag : memFinal (dsPiPtrBase b L vCap eCap + e) =
              memCore (dsPiPtrBase b L vCap eCap + e) :=
            hmem_in _ (by simpa using (hF_pi 0 h0lt e heC).1) (by simpa using (hF_pi 0 h0lt e heC).2)
          rw [hpi_ag, hres_Pi i]; simp only [hi0, ↓reduceIte]
          obtain ⟨hmw, hlo, hhi⟩ := hpi0C e he
          refine ⟨hmw.of_agree fun a h1 h2 => hWalkAg a (le_trans hlo h1) (by
            rw [mWalkEncode_length] at hhi
            exact lt_of_lt_of_le (by rw [Nat.add_assoc] at h2; exact h2) hhi),
            fun a h1 h2 => hfoot_new a (le_trans hlo h1) (lt_of_lt_of_le h2 hhi)⟩
        · have hrg_ag : memFinal (dsRevGenBase b L vCap eCap + v) =
              memCore (dsRevGenBase b L vCap eCap + v) :=
            hmem_in _ (by simpa using (hF_rg 0 h0lt v hv).1) (by simpa using (hF_rg 0 h0lt v hv).2)
          have hrh_ag : memFinal (dsRevHeadBase b L vCap eCap + v) =
              memCore (dsRevHeadBase b L vCap eCap + v) :=
            hmem_in _ (by simpa using (hF_rh 0 h0lt v hv).1) (by simpa using (hF_rh 0 h0lt v hv).2)
          obtain ⟨hrg, hnd, hmem, hll⟩ := hrev0C v hv
          rw [hdom_ag, hrg_ag, hrh_ag, hgenF_eq]
          refine ⟨hrg, hnd, fun e he => ⟨hGE'_cap e ((hmem e).mp he).1, ((hmem e).mp he).1⟩, ?_⟩
          split_ifs at hll ⊢
          · exact (hll.of_agree fun a ha => hWalkAg a ha.1 ha.2).mono fun a ha =>
              hfoot_new a ha.1 ha.2
          · exact hll
      · have hi_pos : 0 < i.1 := Nat.pos_of_ne_zero hi0
        obtain ⟨_, _, hdz, hedI, hrgI⟩ := hPosC i hi_pos
        exact levelDom_of_gen_zero i
          ((hmem_in _ (hF_dom i.1 i.2).1 (hF_dom i.1 i.2).2).trans hdz)
          (fun e he => by
            rw [hmem_in _ (hF_edom i.1 i.2 e he).1 (hF_edom i.1 i.2 e he).2, hgenF_eq]
            exact hedI e he)
          (fun v hv => by
            rw [hmem_in _ (hF_rg i.1 i.2 v hv).1 (hF_rg i.1 i.2 v hv).2, hgenF_eq]
            exact hrgI v hv)
          (by simp [x', hi0]) (fun _ => by simp [x', hi0]) (by rw [hres_inDom i]; simp [hi0])
    · -- `S_level`
      intro i
      obtain ⟨hsz, hvsI⟩ := hSC i
      exact levelS_of_gen_zero i
        ((hmem_in _ (hF_sg i.1 i.2).1 (hF_sg i.1 i.2).2).trans hsz)
        (fun v hv => by
          rw [hmem_in _ (hF_vsg i.1 i.2 v hv).1 (hF_vsg i.1 i.2 v hv).2, hgenF_eq]
          exact hvsI v hv)
        rfl (hres_S i)
    · -- `sBit`, `vStamp`
      intro v hv
      rw [hmem_in _ (hF_sbit v hv).1 (hF_sbit v hv).2,
        hmem_in _ (hF_vst v hv).1 (hF_vst v hv).2, hgenF_eq]
      exact hvSC v hv
    · -- `eStamp`, `keptStamp`
      intro e he
      rw [hmem_in _ (hF_est e he).1 (hF_est e he).2,
        hmem_in _ (hF_kst e he).1 (hF_kst e he).2, hgenF_eq]
      exact heSC e he
  -- `RevHistoryInv` at `k + 1`.
  have hRevFinal : RevHistoryInv G₀ q (canonicalSparsify impl) us (k + 1) x' := by
    intro i
    have hdvd0 : phasePeriod q L 0 ∣ (k + 1) := hj0 ▸ chooseLevel_dvd L q (k + 1)
    have hdvd_i : phasePeriod q L i.1 ∣ (k + 1) :=
      dvd_trans (Nat.pow_dvd_pow q (by omega)) hdvd0
    have hlr : lastRebuild q L i.1 (k + 1) = k + 1 := lastRebuild_eq_self_of_dvd hdvd_i
    dsimp only
    rw [hlr, hst1_eq]
    by_cases hi0 : i.1 = 0
    · refine ⟨by simp only [x', hi0, hres_inDom i], fun v hv e => ?_⟩
      simp only [x', hi0, ↓reduceIte, hres_inDom i, hres_G, hres_Pi i]
      rw [(hCoreArrays.2.2.2.2.2.2.2.2.1 v hv).2.2.1 e]
      constructor <;> rintro ⟨heG, hvw⟩ <;> refine ⟨heG, ?_⟩
      · rwa [walkVertices_of_isSubgraph hH'_sub_H₀ (hPi₀_emb.2 e heG)]
      · rwa [← walkVertices_of_isSubgraph hH'_sub_H₀ (hPi₀_emb.2 e heG)]
    · refine ⟨by simp only [x', hi0, hres_inDom i], fun v _ e => ?_⟩
      simp [x', hi0, hres_inDom i]
  refine ⟨⟨uhPtr, uhWords, dPtr, uhActual, dL, x', hHdrF.1, hHdrF.2.1.trans huh_len_eq.symm,
    hHdrF.2.2.1, hHdrF.2.2.2.1, hHdrF.2.2.2.2, by omega, by omega, hheap_ar.2.2.2.2.2.1.symm,
    huh_bat, huh_perm, hdL_nd, ?_, hdL_at, hzFinal, rfl, rfl, rfl, hStateFinal, hRevFinal,
    hFrameLt⟩, by omega, hret_le, ?_, ?_⟩
  · ext e; simp only [List.mem_toFinset, hdL_mem]; change e ∈ H₀.E ↔ e ∈ res.D; rw [hres_D, hH'_E]
  · have hg1 : memFinal (b + dsGenOff) = gOld + 1 + G'.m := hgen_eq.1
    have hg2 : gOld = mem0 (b + dsGenOff) + 1 := hgen_eq.2
    omega
  · have hpl : uhActual.length = res.UH.length := huh_perm.length_eq
    have hwl : uhWords = prefWords + 2 * delCnt + 4 * insCnt := hheap_ar.2.2.2.2.1
    have hul : uhLen = (if prefWords = 0 then 0 else 1) + delCnt + insCnt := hheap_ar.2.2.2.2.2.2.1
    have hpf : prefWords ≤ len := hheap_ar.2.2.2.2.2.2.2.2.2
    rw [hHdrF.2.2.1]; omega

end

end MinCostFlow.DynSpanner.Program
