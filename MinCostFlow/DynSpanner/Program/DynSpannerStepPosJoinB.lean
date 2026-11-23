module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosJoinA
public import MinCostFlow.DynSpanner.Program.DynSpannerStepFinish
public import MinCostFlow.DynSpanner.Program.DynSpannerCollectD
public import MinCostFlow.DynSpanner.Program.DynSpannerStepEmpty
public import MinCostFlow.DynSpanner.Program.DynSpannerStepMidMinH
public import MinCostFlow.DynSpanner.Program.DynSpannerStepUH
public import MinCostFlow.DynSpanner.Program.DynSpannerStepAuxProcs

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Stage Joins for a `0 < j` Step (Part B: `UTCtx`, `RBCtx`, `DynSpannerStateAt`, and `RevHistoryInv`)

Pure mathematical join lemmas for the second half of a `0 < j` step:

* `bucketsCat_nodup_and_mem`: proves `bucketsCat B_mid j (L + 1 - j)` has no duplicates, has
  length equal to the sum of `dsHDegDummyBase[j..L]`, and enumerates
  `H_mid_union.E \ unionEdgesLt H_mid j`.
* `buildFinishCtx`: builds `c : UTCtx` and `r : RBCtx` on the memory before `dsStepFinishStmt`
  (uniformly for both `E_aff.Nonempty` and `E_aff = ∅`), proves `c.recs` is a valid
  delete/insert permutation of `uhDel ++ uhIns` whose application to `H_mid_union` equals
  `res.state.H`, and satisfies `(dsStepTailContract c H_mid_union (dsHPtr ...) hdr r).pre`.
* `rebuildStatePos`: reconstructs `DynSpannerStateAt` and `RevHistoryInv` at timestamp `k + 1`
  from the postconditions of `dsStepFinishStmt`, `dsClearSBitStmt`, `clearAuxGraphStmt`, and the
  timestamp increment `t := t + 1`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

@[expose] public section

/-! ## Bucket concatenation lemmas -/

lemma bucketsCat_length_eq_sum_range (B : ℕ → List ℕ) (lo k : ℕ) :
    (bucketsCat B lo k).length =
      ((List.range k).map fun d => (B (lo + d)).length).sum := by
  induction k with
  | zero => simp [bucketsCat]
  | succ k ih =>
    rw [bucketsCat_succ, List.length_append, ih, List.range_succ, List.map_append,
      List.sum_append, List.map_singleton, List.sum_singleton]

lemma mem_bucketsCat {B : ℕ → List ℕ} {lo k e : ℕ} :
    e ∈ bucketsCat B lo k ↔ ∃ i, lo ≤ i ∧ i < lo + k ∧ e ∈ B i := by
  simp only [bucketsCat, List.mem_flatMap, List.mem_range'_1]
  constructor
  · rintro ⟨i, ⟨h1, h2⟩, hi⟩; exact ⟨i, h1, h2, hi⟩
  · rintro ⟨i, h1, h2, hi⟩; exact ⟨i, ⟨h1, h2⟩, hi⟩

lemma bucketsCat_nodup {B : ℕ → List ℕ} {lo k : ℕ}
    (hnd : ∀ i, lo ≤ i → i < lo + k → (B i).Nodup)
    (hdisj : ∀ i₁ i₂, lo ≤ i₁ → i₁ < lo + k → lo ≤ i₂ → i₂ < lo + k → i₁ ≠ i₂ →
      ∀ e, e ∈ B i₁ → e ∉ B i₂) :
    (bucketsCat B lo k).Nodup := by
  induction k with
  | zero => simp [bucketsCat]
  | succ k ih =>
    rw [bucketsCat_succ, List.nodup_append]
    refine ⟨ih (fun i h1 h2 => hnd i h1 (by omega))
        (fun i₁ i₂ h1 h2 h3 h4 hne => hdisj i₁ i₂ h1 (by omega) h3 (by omega) hne),
      hnd (lo + k) (by omega) (by omega), fun e he₁ e₂ he₂ heq => ?_⟩
    subst heq
    obtain ⟨i, h1, h2, hi⟩ := mem_bucketsCat.mp he₁
    exact hdisj i (lo + k) h1 (by omega) (by omega) (by omega) (by omega) e hi he₂

lemma utCtx_recs_isDelOrIns (c : UTCtx) : ∀ u ∈ c.recs, isDelOrIns u := by
  intro u hu
  simp only [UTCtx.recs, insRecs, List.mem_append, List.mem_map] at hu
  rcases hu with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> trivial

lemma batchWithinCaps_of_delIns {vCap eCap : ℕ} {G : MGraph} {us : List Update}
    (hGe : ∀ e ∈ G.E, e < eCap)
    (h : ∀ u ∈ us, (∃ e, u = .delete e) ∨ (∃ e ∈ G.E, u = .insert e (G.tail e) (G.head e))) :
    BatchWithinCaps vCap eCap us := by
  intro u hu
  rcases h u hu with ⟨e, rfl⟩ | ⟨e, he, rfl⟩
  · trivial
  · exact hGe e he

/-! ## Building `UTCtx` and `RBCtx` before `dsStepFinishStmt` -/

/-- Build `UTCtx` and `RBCtx` on the memory `mem` immediately before `dsStepFinishStmt`, proving
all preconditions of `dsStepTailContract` and the exact permutation / `applyBatch` bridge to the
abstract model `step`. -/
theorem buildFinishCtx {G₀ : MGraph} {w L q mMax vCap eCap b k : ℕ} {impl : SparsifyImpl}
    {us : List Update} {u : Update} {mem0 mem2 mem : ℕ → ℕ} {x : DynSpannerMeta L}
    {jtEList : List ℕ} {jtPresPtr jtEListPtr hdr : ℕ}
    (hVG₀ : G₀.IsValid) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hBV : G₀.BatchIsValid us) (hds : ∀ u' ∈ us, isDelOrSplit u')
    (hu_some : us[k]? = some u)
    (hPref : ∀ s ≤ k, SnapInv G₀ L q mMax (canonicalSparsifyParams impl mMax).absorbTime
      (canonicalSparsify impl) us s)
    (hj_pos : 0 < chooseLevel L q (k + 1))
    (hw16 : 16 ≤ 2 ^ w)
    (hState : DynSpannerStateAt L vCap eCap b mem0 x
      (runState (L := L) G₀ q (canonicalSparsify impl) us k))
    (hGV'_cap : ∀ v ∈ ((runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u).V,
      v < vCap)
    (hfix_w : b + dsFixedSize L vCap eCap < 2 ^ w)
    (hfix_hdr : b + dsFixedSize L vCap eCap ≤ hdr)
    (hB2 : BucketsAt mem2 L vCap eCap b
      (fun i => delErase u (if hi : i < L + 1 then x.hBuckets ⟨i, hi⟩ else [])))
    (hmin2 : ∀ e < eCap, mem2 (dsMinHBase b vCap eCap + e) =
      minHAfter u (mem0 (dsMinHBase b vCap eCap + e)) e)
    (hag_hdr : ∀ addr, b ≤ addr → addr < dsGPtr b → addr ≠ b + dsGenOff → mem addr = mem0 addr)
    (hag_buck : ∀ addr, dsMinHBase b vCap eCap ≤ addr → addr < dsDomGenBase b L vCap eCap →
      mem addr = mem2 addr)
    (hDG' : DynGraphAt mem (dsGPtr b) vCap eCap
      ((runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u))
    (hDHmid : DynGraphAt mem (dsHPtr b vCap eCap) vCap eCap
      ((runState (L := L) G₀ q (canonicalSparsify impl) us k).H.applyBatch
        (restrictUpdate u (runState (L := L) G₀ q (canonicalSparsify impl) us k).H)))
    (hjt_nd : jtEList.Nodup)
    (hjt_iff :
      let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
      let j := chooseLevel L q (k + 1)
      let G' := st.G.applyUpdate u
      let H_mid : Fin (L + 1) → MGraph :=
        fun i => (st.H_level i).applyBatch (restrictUpdate u (st.H_level i))
      let inDom_mid : Fin (L + 1) → Finset ℕ := fun i => st.inDom i ∩ G'.E
      let S_prev := st.S_level ⟨j - 1, by have := chooseLevel_le L q (k + 1); omega⟩ ∪
        touchedVertices st.G u
      let H_lt := unionGraphLt G' H_mid j
      let piLt_mid := piLtFrom st.Pi_level inDom_mid j
      let E_aff := affectedEdges G' H_lt piLt_mid S_prev
      let J := buildProjGraph G' H_lt piLt_mid S_prev E_aff
      let H_aux := buildAuxHost G' H_lt E_aff
      let embJH := projWalk G' H_lt piLt_mid S_prev
      let out := if E_aff.Nonempty then canonicalSparsify impl H_aux J embJH else ⟨J, idEmb, 0⟩
      ∀ e, e ∈ jtEList ↔ e ∈ out.Jtilde.E)
    (hjt_at : ListAt mem jtEListPtr jtEList)
    (hjt_pres : ∀ e < eCap, mem (jtPresPtr + e) = if e ∈ jtEList.toFinset then 1 else 0)
    (hjt_fix : b + dsFixedSize L vCap eCap ≤ jtEListPtr)
    (hjt_hdr : jtEListPtr + jtEList.length ≤ hdr)
    (hpres_hdr : jtPresPtr + eCap ≤ hdr)
    (hsz_w :
      let Bmid := fun i => delErase u (if hi : i < L + 1 then x.hBuckets ⟨i, hi⟩ else [])
      let j := chooseLevel L q (k + 1)
      hdr + 1 + (2 * (bucketsCat Bmid j (L + 1 - j)).length + 4 * jtEList.length) < 2 ^ w) :
    let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
    let res := step st u (canonicalSparsify impl)
    let j := chooseLevel L q (k + 1)
    let H_mid_union := st.H.applyBatch (restrictUpdate u st.H)
    let Bmid := fun i => delErase u (if hi : i < L + 1 then x.hBuckets ⟨i, hi⟩ else [])
    ∃ (c : UTCtx) (r : RBCtx),
      c.da.w = w ∧ c.da.eCap = eCap ∧ c.vCap = vCap ∧ c.da.mem0 = mem ∧
      c.da.nextBase = dsHNextBase b vCap eCap ∧ c.da.headBase = dsHHeadBase b vCap eCap ∧
      c.da.lenBase = dsHDegDummyBase b L vCap eCap ∧ c.da.lo = j ∧ c.da.hi = L + 1 ∧
      c.da.pres = jtPresPtr ∧ c.da.out = hdr + 1 ∧ c.da.B = Bmid ∧
      c.esPtr = jtEListPtr ∧ c.es = jtEList ∧
      c.presY = dgEPresBase (dsHPtr b vCap eCap) vCap ∧ c.gPtr = dsGPtr b ∧
      r.w = w ∧ r.L = L ∧ r.vCap = vCap ∧ r.eCap = eCap ∧ r.b = b ∧ r.j = j ∧
      r.es = jtEList ∧ r.esPtr = jtEListPtr ∧ r.B = Bmid ∧ r.mem0 = mem ∧
      (dsStepTailContract c H_mid_union (dsHPtr b vCap eCap) hdr r).pre
        ([dsHNextBase b vCap eCap, dsHHeadBase b vCap eCap, dsHDegDummyBase b L vCap eCap,
          j, L + 1, jtPresPtr, hdr + 1, jtEListPtr, jtEList.length,
          dgEPresBase (dsHPtr b vCap eCap) vCap, dsGPtr b, dsHPtr b vCap eCap, hdr] ++
         [dsHNextBase b vCap eCap, dsHHeadBase b vCap eCap, dsHDegDummyBase b L vCap eCap,
          j, L + 1, dsMinHBase b vCap eCap, b, jtEListPtr, jtEList.length] ++
         [dsDomGenBase b L vCap eCap, dsSGenBase b L vCap eCap, j + 1, j, L + 1]) mem ∧
      H_mid_union.applyBatch c.recs = res.state.H ∧
      (restrictUpdate u st.H ++ c.recs).Perm res.UH ∧
      (∀ u' ∈ c.recs, isDelOrIns u') ∧
      (bucketsCat Bmid j (L + 1 - j)).length =
        ((List.range (L + 1 - j)).map fun d => mem (dsHDegDummyBase b L vCap eCap + (j + d))).sum ∧
      (∀ e < eCap,
        (minHRebuild j jtEList.toFinset r.m0 e = 0 ↔ e ∉ res.state.H.E) ∧
        (e ∈ res.state.H.E → ∃ i : Fin (L + 1),
          minHRebuild j jtEList.toFinset r.m0 e = i.1 + 1 ∧
          e ∈ (res.state.H_level i).E ∧
          ∀ k' : Fin (L + 1), k'.1 < i.1 → e ∉ (res.state.H_level k').E)) ∧
      (∀ i : Fin (L + 1), ∀ e, e ∈ r.newB i.1 ↔
        e ∈ res.state.H.E ∧ minHRebuild j jtEList.toFinset r.m0 e = i.1 + 1) := by
  intro st res j H_mid_union Bmid
  have hj_le : j ≤ L := chooseLevel_le L q (k + 1)
  have hL1 : 1 ≤ L := by omega
  have hj_ne : j ≠ 0 := by omega
  have hk_inv := hPref k le_rfl
  obtain ⟨_, _, hU_k⟩ := batchIsValid_take us G₀ k hBV hds
  obtain ⟨hu_val, hdu⟩ := hU_k u hu_some
  have hnext_inv := step_inv hVG₀ hL1 hq hGm₀ (canonicalSparsify_spec_absorb impl mMax) hBV hds
    hu_some hPref
  rcases hnext_inv with ⟨hk1_inv, hRec⟩
  have hst1_eq : runState (L := L) G₀ q (canonicalSparsify impl) us (k + 1) = res.state := by
    simp only [runState, res, st, hu_some]
  have hstep_out : runStepOut (L := L) G₀ q (canonicalSparsify impl) us k = res := by
    simp only [runStepOut, res, st, hu_some]
  rcases hState with ⟨hxV, hxE, _, hb1, hGval, hHval, hHV, hHEsub, hHends, hGV_cap, hGE_cap,
    _, _, hmL0, hmV0, hmE0, _, _, _, _, hminH0, hBuck0, _, _, _, _⟩
  let G' := st.G.applyUpdate u
  let H_mid : Fin (L + 1) → MGraph :=
    fun i => (st.H_level i).applyBatch (restrictUpdate u (st.H_level i))
  let inDom_mid : Fin (L + 1) → Finset ℕ := fun i => st.inDom i ∩ G'.E
  let S_prev := st.S_level ⟨j - 1, by omega⟩ ∪ touchedVertices st.G u
  let H_lt := unionGraphLt G' H_mid j
  let piLt_mid := piLtFrom st.Pi_level inDom_mid j
  let E_aff := affectedEdges G' H_lt piLt_mid S_prev
  let J := buildProjGraph G' H_lt piLt_mid S_prev E_aff
  let H_aux := buildAuxHost G' H_lt E_aff
  let embJH := projWalk G' H_lt piLt_mid S_prev
  let out := if E_aff.Nonempty then canonicalSparsify impl H_aux J embJH else ⟨J, idEmb, 0⟩
  let H_j : MGraph := { V := G'.V, E := out.Jtilde.E, tail := G'.tail, head := G'.head }
  have hG'val : G'.IsValid := isValid_applyUpdate_of_delOrSplit hGval (hk_inv.G_eq ▸ hu_val) hdu
  have hG'E_sub : G'.E ⊆ st.G.E := E_applyUpdate_subset hdu
  have hGE'_cap : ∀ e ∈ G'.E, e < eCap := fun e he => hGE_cap e (hG'E_sub he)
  -- Express `res` components cleanly using `hj_ne`.
  have hcl_eq : chooseLevel L st.q (st.t + 1) = j := by rw [hk_inv.q_eq, hk_inv.t_eq]
  have hjt_eq_Hj : jtEList.toFinset = H_j.E := by
    ext e; simp only [List.mem_toFinset, H_j]; exact hjt_iff e
  have hres_Hlevel : res.state.H_level = rebuildLevels H_mid H_j G' j := by
    funext i
    dsimp only [res, step, rebuildLevels, H_mid, H_j, G', out, embJH, H_aux, J, E_aff, piLt_mid,
      H_lt, S_prev, inDom_mid]
    simp only [hcl_eq, hj_ne, ↓reduceDIte]
  have hres_HE : res.state.H.E = unionEdgesLt H_mid j ∪ H_j.E := by
    have h1 := hk1_inv.H_E
    rw [hst1_eq, hres_Hlevel, unionEdgesLt_rebuild H_mid H_j G' hj_le] at h1
    exact h1
  have hjt_sub_G' : out.Jtilde.E ⊆ G'.E := by
    intro e he
    have : e ∈ res.state.H.E := by rw [hres_HE]; exact Finset.mem_union_right _ he
    have hG1 : res.state.G = G' := by
      dsimp only [res, step, G']; simp only [hcl_eq, hj_ne, ↓reduceDIte]
    have hsub := hk1_inv.H_sub
    rw [hst1_eq] at hsub
    have hGeq : G₀.applyBatch (us.take (k + 1)) = G' := by
      rw [← hG1, ← hst1_eq, hk1_inv.G_eq]
    rw [hGeq] at hsub
    exact hsub.2.1 this
  have hjt_cap : ∀ e ∈ jtEList, e < eCap := fun e he =>
    hGE'_cap e (hjt_sub_G' ((hjt_iff e).mp he))
  have hjt_G' : ∀ e ∈ jtEList, e ∈ G'.E := fun e he =>
    hjt_sub_G' ((hjt_iff e).mp he)
  -- Layout arithmetic.
  have hfa := dsFixedSize_add b L vCap eCap
  have hmin_eq := dsMinHBase_eq b vCap eCap
  have hdom_eq := dsDomGenBase_eq b L vCap eCap
  have hdom_le_fix : dsDomGenBase b L vCap eCap ≤ b + dsFixedSize L vCap eCap := by
    rw [← hfa]
    have := dsRevGenBase_eq b L vCap eCap
    have := dsRevHeadBase_eq b L vCap eCap
    have := dsVStampBase_eq b L vCap eCap
    simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase]
    omega
  have hh_lt_min : dsHPtr b vCap eCap + dynGraphSize vCap eCap ≤ dsMinHBase b vCap eCap := by
    simp only [dsMinHBase, dsAuxPtr]; omega
  have hg_lt_h : dsGPtr b + dynGraphSize vCap eCap = dsHPtr b vCap eCap := rfl
  have hprev_def : dsHPrevBase b vCap eCap = dsHNextBase b vCap eCap + eCap := rfl
  have hnext_def : dsHNextBase b vCap eCap = dsMinHBase b vCap eCap + eCap := rfl
  have hhead_def : dsHHeadBase b vCap eCap = dsHPrevBase b vCap eCap + eCap := rfl
  have hdeg_def : dsHDegDummyBase b L vCap eCap = dsHHeadBase b vCap eCap + (L + 1) := rfl
  have hdom_def : dsDomGenBase b L vCap eCap = dsHDegDummyBase b L vCap eCap + (L + 1) := rfl
  -- Transfer `minH` and buckets from `mem0 -> mem2 -> mem`.
  have hmin_after := minH_after_update hdu
    (m := fun e => mem0 (dsMinHBase b vCap eCap + e))
    (m' := fun e => mem2 (dsMinHBase b vCap eCap + e))
    (H_level := st.H_level) (H_mid := H_mid)
    (B := fun i => if hi : i < L + 1 then x.hBuckets ⟨i, hi⟩ else [])
    (fun e he => (hminH0 e he).1) (fun e he => (hminH0 e he).2)
    (fun i e => by simpa [i.2] using (hBuck0 i).2.2 e)
    (fun i => by simpa [i.2] using (hBuck0 i).1.1)
    hmin2 (fun i => mid_E_delSet hdu (st.H_level i))
    (fun e heq => hGE_cap e (by rw [heq] at hu_val; exact hk_inv.G_eq ▸ hu_val))
  have hHmid_E : H_mid_union.E = delSet u st.H.E := mid_E_delSet hdu st.H
  have hBk_mem : BucketsAt mem L vCap eCap b Bmid :=
    hB2.of_agree_range hag_buck
  have hmin_mem : ∀ e < eCap, mem (dsMinHBase b vCap eCap + e) =
      mem2 (dsMinHBase b vCap eCap + e) := fun e he =>
    hag_buck (dsMinHBase b vCap eCap + e) (by omega) (by omega)
  have hmin_spec : ∀ e < eCap,
      (mem (dsMinHBase b vCap eCap + e) = 0 ↔ e ∉ H_mid_union.E) ∧
      (e ∈ H_mid_union.E → ∃ i : Fin (L + 1),
        mem (dsMinHBase b vCap eCap + e) = i.1 + 1 ∧ e ∈ (H_mid i).E ∧
        ∀ k' : Fin (L + 1), k'.1 < i.1 → e ∉ (H_mid k').E) := by
    intro e he
    rw [hmin_mem e he, hHmid_E]
    exact hmin_after.1 e he
  have hHmid_sub_stG : H_mid_union.E ⊆ st.G.E := by
    rw [hHmid_E]
    cases u with
    | insert _ _ _ => exact hdu.elim
    | delete _ => exact Finset.Subset.trans (Finset.erase_subset _ _) hHEsub
    | split _ _ _ _ => exact hHEsub
  have hBmid_iff : ∀ i : Fin (L + 1), ∀ e,
      e ∈ Bmid i.1 ↔ e ∈ H_mid_union.E ∧ mem (dsMinHBase b vCap eCap + e) = i.1 + 1 := by
    intro i e
    by_cases heC : e < eCap
    · rw [hmin_mem e heC, hHmid_E]
      exact hmin_after.2 i e heC
    · constructor
      · intro hmem
        have hlt := (hBk_mem i.1 (by omega)).1.2.1 e hmem
        exact (heC hlt).elim
      · rintro ⟨heH, _⟩
        exact (heC (hGE_cap e (hHmid_sub_stG heH))).elim
  have hBmid_iff_rb : ∀ i e, i ≤ L →
      (e ∈ Bmid i ↔ e < eCap ∧ mem (dsMinHBase b vCap eCap + e) = i + 1) := by
    intro i e hi
    rw [hBmid_iff ⟨i, by omega⟩ e]
    constructor
    · rintro ⟨heH, hm⟩
      exact ⟨hGE_cap e (hHmid_sub_stG heH), hm⟩
    · rintro ⟨heC, hm⟩
      refine ⟨?_, hm⟩
      by_contra hnot
      have := (hmin_spec e heC).1.mpr hnot
      omega
  have hbig : ∀ e < eCap, mem (dsMinHBase b vCap eCap + e) ≤ L + 1 := by
    intro e he
    by_cases hE : e ∈ H_mid_union.E
    · obtain ⟨i, hi, _, _⟩ := (hmin_spec e he).2 hE
      omega
    · have := (hmin_spec e he).1.mpr hE
      omega
  -- Construct `r : RBCtx`.
  let r : RBCtx :=
    { w := w, L := L, vCap := vCap, eCap := eCap, b := b, j := j
      es := jtEList, esPtr := jtEListPtr, B := Bmid, mem0 := mem
      hw16 := hw16, hbound := hfix_w, hjL := hj_le
      hLw := (hag_hdr _ (by simp [dsLOff]) (by simp [dsGPtr, dsHdrSize, dsLOff])
        (by simp [dsLOff, dsGenOff])).trans hmL0
      hvw := (hag_hdr _ (by simp [dsVCapOff]) (by simp [dsGPtr, dsHdrSize, dsVCapOff])
        (by simp [dsVCapOff, dsGenOff])).trans hmV0
      hew := (hag_hdr _ (by simp [dsECapOff]) (by simp [dsGPtr, dsHdrSize, dsECapOff])
        (by simp [dsECapOff, dsGenOff])).trans hmE0
      hesB := by omega
      dEB := Or.inr (by omega)
      hes := hjt_at, hnd := hjt_nd, hesC := hjt_cap, hBk := hBk_mem
      hBiff := hBmid_iff_rb, hbig := hbig }
  -- Construct `da : DACtx` and `c : UTCtx`.
  have hpresY : ∀ e < eCap, mem (dgEPresBase (dsHPtr b vCap eCap) vCap + e) =
      if e ∈ H_mid_union.E then 1 else 0 := by
    intro e he
    exact hDHmid.2.2.2.2.2.2.2.2.2.2.2.1 e he
  let da : DACtx :=
    { w := w, eCap := eCap, X := jtEList.toFinset, B := Bmid, lo := j, hi := L + 1
      prevBase := dsHPrevBase b vCap eCap, nextBase := dsHNextBase b vCap eCap
      headBase := dsHHeadBase b vCap eCap, lenBase := dsHDegDummyBase b L vCap eCap
      pres := jtPresPtr, out := hdr + 1, mem0 := mem
      hle := by omega, hw16 := hw16, hnB := by omega, hpB := by omega
      hhB := by omega, hlB := by omega
      hoB := by dsimp only [Bmid, j] at hsz_w ⊢; omega
      dOR := Or.inr (by omega), dON := Or.inr (by omega), dOP := Or.inr (by omega)
      dOH := Or.inr (by omega), dOL := Or.inr (by omega)
      hB := fun i h1 h2 => hBk_mem i (by omega)
      hpres := hjt_pres }
  let c : UTCtx :=
    { da := da, vCap := vCap, G := G', Y := H_mid_union.E, es := jtEList
      esPtr := jtEListPtr, presY := dgEPresBase (dsHPtr b vCap eCap) vCap
      gPtr := dsGPtr b
      hesB := by dsimp only [da]; omega
      hpB := by dsimp only [da]; simp only [dgEPresBase]; unfold dynGraphSize at hh_lt_min; omega
      hgB := by dsimp only [da]; omega
      hoB := by dsimp only [da, Bmid, j] at hsz_w ⊢; omega
      dOE := Or.inr (by dsimp only [da]; omega)
      dOP := Or.inr (by dsimp only [da]; simp only [dgEPresBase]; unfold dynGraphSize at hh_lt_min; omega)
      dOG := Or.inr (by dsimp only [da]; omega)
      hes := hjt_at, hesG := hjt_G', hG := hDG', hpres := hpresY, hGcap := hG'val }
  -- Connect `c.recs` to `step`'s `uhDel ++ uhIns` via `diffBatch_perm_props`.
  have hHmid_union_eq : H_mid_union.E = unionEdgesLt H_mid (L + 1) := by
    rw [hHmid_E, hk_inv.H_E]
    have h1 := unionEdgesLt_mid hdu st.H_level
      (fun i => hk_inv.G_eq ▸ (hk_inv.H_level_sub i).2.1) (L + 1)
    change delSet u (unionEdgesLt st.H_level (L + 1)) = unionEdgesLt H_mid (L + 1)
    rw [h1, applyUpdate_E_delSet hdu st.G]
    ext e
    simp only [Finset.mem_inter]
    cases u with
    | insert _ _ _ => exact hdu.elim
    | delete d =>
      simp only [delSet, Finset.mem_erase]
      exact ⟨fun ⟨hne, heu⟩ => ⟨heu, hne, hHEsub (hk_inv.H_E ▸ heu)⟩,
        fun ⟨heu, hne, _⟩ => ⟨hne, heu⟩⟩
    | split _ _ _ _ =>
      simp only [delSet]
      exact ⟨fun heu => ⟨heu, hHEsub (hk_inv.H_E ▸ heu)⟩, fun ⟨heu, _⟩ => heu⟩
  have hsub_lt_mid : unionEdgesLt H_mid j ⊆ H_mid_union.E := by
    rw [hHmid_union_eq]; exact unionEdgesLt_mono H_mid (by omega)
  have hlt_iff_minH : ∀ e < eCap,
      e ∈ unionEdgesLt H_mid j ↔
        0 < mem (dsMinHBase b vCap eCap + e) ∧ mem (dsMinHBase b vCap eCap + e) ≤ j := by
    intro e heC
    constructor
    · intro heu
      have heH : e ∈ H_mid_union.E := hsub_lt_mid heu
      obtain ⟨i, hi_eq, _, hi_min⟩ := (hmin_spec e heC).2 heH
      simp only [unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at heu
      rcases heu with ⟨k', hk'j, hek'⟩
      have : ¬ k'.1 < i.1 := fun hlt => hi_min k' hlt hek'
      omega
    · rintro ⟨hm_pos, hm_le⟩
      have heH : e ∈ H_mid_union.E := by
        by_contra hnot; have := (hmin_spec e heC).1.mpr hnot; omega
      obtain ⟨i, hi_eq, hei, _⟩ := (hmin_spec e heC).2 heH
      simp only [unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨i, by omega, hei⟩
  have hcat_nd : (bucketsCat Bmid j (L + 1 - j)).Nodup := by
    refine bucketsCat_nodup (fun i _ h2 => (hBk_mem i (by omega)).1.1) ?_
    intro i₁ i₂ h1 h2 h3 h4 hne e he₁ he₂
    have hm1 := ((hBmid_iff ⟨i₁, by omega⟩ e).mp he₁).2
    have hm2 := ((hBmid_iff ⟨i₂, by omega⟩ e).mp he₂).2
    simp only at hm1 hm2
    omega
  have hdel_nd : (delList jtEList.toFinset (bucketsCat Bmid j (L + 1 - j))).Nodup :=
    hcat_nd.sublist List.filter_sublist
  have hins_nd : (insList H_mid_union.E jtEList).Nodup := hjt_nd.sublist List.filter_sublist
  have hdel_mem : ∀ e, e ∈ delList jtEList.toFinset (bucketsCat Bmid j (L + 1 - j)) ↔
      e ∈ H_mid_union.E \ res.state.H.E := by
    intro e
    simp only [delList, List.mem_filter, decide_eq_true_eq, mem_bucketsCat, hres_HE,
      Finset.mem_sdiff, Finset.mem_union, not_or, ← hjt_eq_Hj]
    constructor
    · rintro ⟨⟨i, hi1, hi2, hBi⟩, hnotX⟩
      obtain ⟨heH, hmi⟩ := (hBmid_iff ⟨i, by omega⟩ e).mp hBi
      have heC : e < eCap := hGE_cap e (hHmid_sub_stG heH)
      have hnotLt : e ∉ unionEdgesLt H_mid j := by
        rw [hlt_iff_minH e heC, hmi]; simp only; omega
      exact ⟨heH, hnotLt, hnotX⟩
    · rintro ⟨heH, hnotLt, hnotX⟩
      have heC : e < eCap := hGE_cap e (hHmid_sub_stG heH)
      obtain ⟨i, hmi, _, _⟩ := (hmin_spec e heC).2 heH
      have hij : j ≤ i.1 := by
        by_contra hlt
        apply hnotLt
        rw [hlt_iff_minH e heC, hmi]
        omega
      refine ⟨⟨i.1, hij, by omega, (hBmid_iff i e).mpr ⟨heH, hmi⟩⟩, hnotX⟩
  have hins_mem : ∀ e, e ∈ insList H_mid_union.E jtEList ↔ e ∈ res.state.H.E \ H_mid_union.E := by
    intro e
    simp only [insList, List.mem_filter, decide_eq_true_eq]
    rw [← List.mem_toFinset, hjt_eq_Hj, hres_HE, Finset.mem_sdiff, Finset.mem_union]
    exact ⟨fun ⟨h1, h2⟩ => ⟨Or.inr h1, h2⟩, fun ⟨h1, h2⟩ =>
      ⟨h1.elim (fun h => absurd (hsub_lt_mid h) h2) id, h2⟩⟩
  have hHnew_sub : res.state.H.E ⊆ G'.E := by
    have hG1 : res.state.G = G' := by
      dsimp only [res, step, G']; simp only [hcl_eq, hj_ne, ↓reduceDIte]
    have hsub := hk1_inv.H_sub
    rw [hst1_eq] at hsub
    have hGeq : G₀.applyBatch (us.take (k + 1)) = G' := by
      rw [← hG1, ← hst1_eq, hk1_inv.G_eq]
    rw [hGeq] at hsub
    exact hsub.2.1
  have hdiff := diffBatch_perm_props (G := st.G) (H := st.H) (u := u) (H_new_E := res.state.H.E)
    (lDel := delList jtEList.toFinset (bucketsCat Bmid j (L + 1 - j)))
    (lIns := insList H_mid_union.E jtEList)
    hGval (hk_inv.G_eq ▸ hk_inv.H_sub) hHV (hk_inv.G_eq ▸ hu_val) hdu hHnew_sub
    hdel_nd hdel_mem hins_nd hins_mem
  rcases hdiff with ⟨hPerm_all, hBV_all, hApply_eq, _⟩
  have hres_UH_eq : res.UH = restrictUpdate u st.H ++
      ((H_mid_union.E \ res.state.H.E).sort (· ≤ ·)).map Update.delete ++
      ((res.state.H.E \ H_mid_union.E).sort (· ≤ ·)).map
        (fun e => Update.insert e (G'.tail e) (G'.head e)) := by
    have hHnew_eq : res.state.H.E = unionEdgesLt res.state.H_level (L + 1) := by
      rw [← hst1_eq]; exact hk1_inv.H_E
    rw [hHnew_eq]
    dsimp only [res, step, H_mid_union, G']
    simp only [hcl_eq, hj_ne, ↓reduceDIte]
  have hrecs_split : restrictUpdate u st.H ++ c.recs =
      (restrictUpdate u st.H ++
        (delList jtEList.toFinset (bucketsCat Bmid j (L + 1 - j))).map Update.delete) ++
        (insList H_mid_union.E jtEList).map (fun e => Update.insert e (G'.tail e) (G'.head e)) := by
    simp [c, da, UTCtx.recs, insRecs, List.append_assoc]
  have hBV_recs : H_mid_union.BatchIsValid c.recs := by
    have h1 : st.H.BatchIsValid (restrictUpdate u st.H ++ c.recs) := by
      simpa only [hrecs_split] using hBV_all
    rw [batchIsValid_append] at h1
    exact h1.2
  have hApply_recs : H_mid_union.applyBatch c.recs = res.state.H := by
    have h1 : st.H.applyBatch (restrictUpdate u st.H ++ c.recs) = st.H.applyBatch res.UH := by
      rw [hrecs_split, hres_UH_eq]
      exact hApply_eq
    rw [applyBatch_append] at h1
    have h2 : st.H.applyBatch res.UH = res.state.H := by
      simpa [hstep_out, hst1_eq] using hRec.uh_apply
    exact h1.trans h2
  have hPerm_recs : (restrictUpdate u st.H ++ c.recs).Perm res.UH := by
    rw [hrecs_split, hres_UH_eq]; exact hPerm_all
  have hCaps_recs : BatchWithinCaps vCap eCap c.recs := by
    refine batchWithinCaps_of_delIns hGE'_cap fun u' hu' => ?_
    simp only [c, da, UTCtx.recs, insRecs, List.mem_append, List.mem_map] at hu'
    rcases hu' with ⟨e, _, rfl⟩ | ⟨e, he, rfl⟩
    · exact Or.inl ⟨e, rfl⟩
    · exact Or.inr ⟨e, hjt_G' e (List.mem_filter.mp he).1, rfl⟩
  -- Assemble `dsStepTailContract.pre`.
  have hpre_tail : (dsStepTailContract c H_mid_union (dsHPtr b vCap eCap) hdr r).pre
      ([dsHNextBase b vCap eCap, dsHHeadBase b vCap eCap, dsHDegDummyBase b L vCap eCap,
        j, L + 1, jtPresPtr, hdr + 1, jtEListPtr, jtEList.length,
        dgEPresBase (dsHPtr b vCap eCap) vCap, dsGPtr b, dsHPtr b vCap eCap, hdr] ++
       [dsHNextBase b vCap eCap, dsHHeadBase b vCap eCap, dsHDegDummyBase b L vCap eCap,
        j, L + 1, dsMinHBase b vCap eCap, b, jtEListPtr, jtEList.length] ++
       [dsDomGenBase b L vCap eCap, dsSGenBase b L vCap eCap, j + 1, j, L + 1]) mem := by
    refine ⟨⟨⟨rfl, rfl, rfl, by dsimp only [c, da]; omega, Or.inr (by dsimp only [c, da]; omega),
      hDHmid, hBV_recs, hCaps_recs⟩,
      rfl, rfl, rfl, fun addr ha => ?_⟩, rfl, fun addr ha => ?_⟩
    · dsimp only [c, da, r, RBCtx.Reads, UTCtx.size] at ha ⊢
      rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine ⟨?_, Or.inr (by omega)⟩
        rintro (⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;> omega
      · refine ⟨?_, Or.inl (by omega)⟩
        rintro (⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;> omega
    · dsimp only [c, da, r, RBCtx.GenWord, UTCtx.size] at ha ⊢
      have hs_le : dsSGenBase b L vCap eCap + (L + 1) ≤ b + dsFixedSize L vCap eCap := by
        rw [← hfa]
        simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase,
          dsSHeadBase, dsVSGenBase]
        omega
      have hdom_le_s : dsDomGenBase b L vCap eCap + (L + 1) ≤ dsSGenBase b L vCap eCap := by
        simp only [dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase, dsEdgeDomGenBase]; omega
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> rcases ha with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  -- `bucketsCat` length equals sum of `dsHDegDummyBase`.
  have hcat_sum : (bucketsCat Bmid j (L + 1 - j)).length =
      ((List.range (L + 1 - j)).map fun d => mem (dsHDegDummyBase b L vCap eCap + (j + d))).sum := by
    rw [bucketsCat_length_eq_sum_range]
    congr 1
    refine List.map_congr_left fun d hd => ?_
    have hd_lt : d < L + 1 - j := List.mem_range.mp hd
    exact (hBk_mem (j + d) (by omega)).2.symm
  -- `minHRebuild` and `r.newB` clauses via `minH_clause_new` and `newB_mem_iff`.
  let mFull : ℕ → ℕ := fun e => if e < eCap then r.m0 e else 0
  have hm_eq : ∀ e < r.eCap, mFull e = r.m0 e := fun e he => by
    dsimp only [r] at he; simp [mFull, he]
  have hm0_full : ∀ e, mFull e = 0 ↔ e ∉ H_mid_union.E := by
    intro e
    by_cases heC : e < eCap
    · simpa [mFull, heC, r, RBCtx.m0] using (hmin_spec e heC).1
    · have hnot : e ∉ H_mid_union.E := fun heH => heC (hGE_cap e (hHmid_sub_stG heH))
      simp [mFull, heC, hnot]
  have hmin_full : ∀ e ∈ H_mid_union.E, ∃ i : Fin (L + 1), mFull e = i.1 + 1 ∧ e ∈ (H_mid i).E ∧
      ∀ k' : Fin (L + 1), k'.1 < i.1 → e ∉ (H_mid k').E := by
    intro e heH
    have heC : e < eCap := hGE_cap e (hHmid_sub_stG heH)
    simpa [mFull, heC, r, RBCtx.m0] using (hmin_spec e heC).2 heH
  have hHmid_cap : ∀ e ∈ H_mid_union.E, e < r.eCap := fun e heH => hGE_cap e (hHmid_sub_stG heH)
  have hmin_new := minH_clause_new r (H_mid := H_mid) (Hj := H_j) (G' := G') (E := H_mid_union.E)
    (m := mFull) (mem' := fun a => if a < dsMinHBase b vCap eCap then 0 else
      minHRebuild j jtEList.toFinset r.m0 (a - dsMinHBase b vCap eCap))
    hm_eq hm0_full hmin_full hsub_lt_mid hjt_eq_Hj.symm
    (fun e _ => by simp [r])
  have hnewB_new := newB_mem_iff r (H_mid := H_mid) (E := H_mid_union.E) (m := mFull)
    (mem' := fun a => if a < dsMinHBase b vCap eCap then 0 else
      minHRebuild j jtEList.toFinset r.m0 (a - dsMinHBase b vCap eCap))
    hm_eq hm0_full hmin_full hsub_lt_mid hHmid_cap (fun e _ => by simp [r])
  refine ⟨c, r, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hpre_tail, hApply_recs, hPerm_recs,
    utCtx_recs_isDelOrIns c, hcat_sum, ?_, ?_⟩
  · intro e he
    have h := hmin_new e he
    simp only [r, Nat.not_lt.mpr (Nat.le_add_right _ _), ↓reduceIte, Nat.add_sub_cancel_left] at h
    simpa [hres_HE, hres_Hlevel] using h
  · intro i e
    have h := hnewB_new i.1 (by dsimp only [r]; omega) e
    simp only [r, Nat.not_lt.mpr (Nat.le_add_right _ _), ↓reduceIte, Nat.add_sub_cancel_left] at h
    simpa [hres_HE, hjt_eq_Hj] using h

/-! ## Rebuilding `DynSpannerStateAt` and `RevHistoryInv` at `k + 1` -/

/-- Reconstruct `DynSpannerStateAt` and `RevHistoryInv` for `(step st u (canonicalSparsify impl)).state`
from the postconditions of `dsStepFinishStmt`, `dsClearSBitStmt`, `clearAuxGraphStmt`, and
incrementing `t := t + 1`. -/
theorem rebuildStatePos {G₀ : MGraph} {L q mMax vCap eCap b k : ℕ} {impl : SparsifyImpl}
    {us : List Update} {u : Update} {mem0 mem2 memFin memFinal : ℕ → ℕ} {x : DynSpannerMeta L}
    {r : RBCtx} {sLists' : Fin (L + 1) → List ℕ} {revJ : ℕ → List ℕ}
    {headHeap r₁ heapStep retFinal : ℕ}
    (hVG₀ : G₀.IsValid) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hBV : G₀.BatchIsValid us) (hds : ∀ u' ∈ us, isDelOrSplit u')
    (hu_some : us[k]? = some u)
    (hPref : ∀ s ≤ k, SnapInv G₀ L q mMax (canonicalSparsifyParams impl mMax).absorbTime
      (canonicalSparsify impl) us s)
    (hRev : RevHistoryInv G₀ q (canonicalSparsify impl) us k x)
    (hj_pos : 0 < chooseLevel L q (k + 1))
    (hState : DynSpannerStateAt L vCap eCap b mem0 x
      (runState (L := L) G₀ q (canonicalSparsify impl) us k))
    (hGV'_cap : ∀ v ∈ ((runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u).V,
      v < vCap)
    (hr_eq : r.L = L ∧ r.vCap = vCap ∧ r.eCap = eCap ∧ r.b = b ∧ r.j = chooseLevel L q (k + 1))
    (hfix_step : b + dsFixedSize L vCap eCap ≤ heapStep)
    (hhead_in : heapStep ≤ headHeap ∧ r₁ ≤ retFinal)
    -- Final memory properties (after `dsStepFinish`, `dsCollectD`, `dsClearSBit`, `clearAux`, `t++`, `packUH`)
    (hHdr : memFinal (b + dsQOff) = (runState (L := L) G₀ q (canonicalSparsify impl) us k).q ∧
      memFinal (b + dsTOff) = (runState (L := L) G₀ q (canonicalSparsify impl) us k).t + 1 ∧
      memFinal (b + dsLOff) = L ∧ memFinal (b + dsVCapOff) = vCap ∧
      memFinal (b + dsECapOff) = eCap ∧
      1 ≤ memFinal (b + dsGenOff) ∧ memFin (b + dsGenOff) ≤ memFinal (b + dsGenOff) ∧
      mem2 (b + dsGenOff) ≤ memFin (b + dsGenOff) ∧
      mem0 (b + dsGenOff) ≤ mem2 (b + dsGenOff))
    (hGraphs :
      let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
      let res := step st u (canonicalSparsify impl)
      DynGraphAt memFinal (dsGPtr b) vCap eCap res.state.G ∧
      DynGraphAt memFinal (dsHPtr b vCap eCap) vCap eCap res.state.H ∧
      DynGraphAt memFinal (dsAuxPtr b vCap eCap) vCap eCap emptyMGraph)
    (hBuckets :
      let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
      let res := step st u (canonicalSparsify impl)
      BucketsAt memFinal L vCap eCap b r.newB ∧
      (∀ e < eCap,
        (memFinal (dsMinHBase b vCap eCap + e) = 0 ↔ e ∉ res.state.H.E) ∧
        (e ∈ res.state.H.E → ∃ i : Fin (L + 1),
          memFinal (dsMinHBase b vCap eCap + e) = i.1 + 1 ∧
          e ∈ (res.state.H_level i).E ∧
          ∀ k' : Fin (L + 1), k'.1 < i.1 → e ∉ (res.state.H_level k').E)) ∧
      (∀ i : Fin (L + 1), ∀ e, e ∈ r.newB i.1 ↔
        e ∈ res.state.H.E ∧ memFinal (dsMinHBase b vCap eCap + e) = i.1 + 1))
    -- Levels `< j` preserved on `domGen..sGen` and `heapFoot x`
    (hag_dom_lt : ∀ i : Fin (L + 1), i.1 < chooseLevel L q (k + 1) →
      memFinal (dsDomGenBase b L vCap eCap + i.1) = mem0 (dsDomGenBase b L vCap eCap + i.1) ∧
      (∀ e < eCap,
        memFinal (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e) =
          mem0 (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e) ∧
        memFinal (dsPiPtrBase b L vCap eCap + i.1 * eCap + e) =
          mem0 (dsPiPtrBase b L vCap eCap + i.1 * eCap + e)) ∧
      (∀ v < vCap,
        memFinal (dsRevGenBase b L vCap eCap + i.1 * vCap + v) =
          mem0 (dsRevGenBase b L vCap eCap + i.1 * vCap + v) ∧
        memFinal (dsRevHeadBase b L vCap eCap + i.1 * vCap + v) =
          mem0 (dsRevHeadBase b L vCap eCap + i.1 * vCap + v)))
    (hag_foot0 : ∀ a, heapFoot x a → memFinal a = mem0 a)
    -- Level `j` established by `dsSetLevelWalks`
    (hLvlJ :
      let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
      let res := step st u (canonicalSparsify impl)
      let j := chooseLevel L q (k + 1)
      let jF : Fin (L + 1) := ⟨j, by have := chooseLevel_le L q (k + 1); omega⟩
      0 < memFinal (dsDomGenBase b L vCap eCap + j) ∧
      memFinal (dsDomGenBase b L vCap eCap + j) ≤ memFinal (b + dsGenOff) ∧
      (∀ e < eCap,
        memFinal (dsEdgeDomGenBase b L vCap eCap + j * eCap + e) ≤ memFinal (b + dsGenOff) ∧
        ((0 < memFinal (dsDomGenBase b L vCap eCap + j) ∧
          memFinal (dsEdgeDomGenBase b L vCap eCap + j * eCap + e) =
            memFinal (dsDomGenBase b L vCap eCap + j)) ↔ e ∈ res.state.inDom jF)) ∧
      (∀ e ∈ res.state.inDom jF,
        let ptr := memFinal (dsPiPtrBase b L vCap eCap + j * eCap + e)
        MWalkAt memFinal ptr (res.state.Pi_level jF e) ∧
        heapStep ≤ ptr ∧ ptr + (mWalkEncode (res.state.Pi_level jF e)).length ≤ retFinal) ∧
      (∀ v < vCap,
        memFinal (dsRevGenBase b L vCap eCap + j * vCap + v) ≤ memFinal (b + dsGenOff) ∧
        (revJ v).Nodup ∧
        (∀ e, e ∈ revJ v ↔ e ∈ res.state.inDom jF ∧
          v ∈ res.state.H.walkVertices (res.state.G.tail e) (res.state.Pi_level jF e)) ∧
        (if 0 < memFinal (dsDomGenBase b L vCap eCap + j) ∧
            memFinal (dsRevGenBase b L vCap eCap + j * vCap + v) =
              memFinal (dsDomGenBase b L vCap eCap + j)
         then LinkedListIn (fun a => heapStep ≤ a ∧ a < retFinal) memFinal
                (memFinal (dsRevHeadBase b L vCap eCap + j * vCap + v)) (revJ v)
         else revJ v = [])))
    -- Levels `> j` cleared
    (hDomGt : ∀ i : Fin (L + 1), chooseLevel L q (k + 1) < i.1 →
      memFinal (dsDomGenBase b L vCap eCap + i.1) = 0 ∧
      (∀ e < eCap, memFinal (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e) =
        mem0 (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e)) ∧
      (∀ v < vCap, memFinal (dsRevGenBase b L vCap eCap + i.1 * vCap + v) =
        mem0 (dsRevGenBase b L vCap eCap + i.1 * vCap + v)))
    -- `S_level` for `< j` preserved from `mem2`, and `≥ j` cleared
    (hSL2 : ∀ i : Fin (L + 1),
      let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
      let j := chooseLevel L q (k + 1)
      let S' : Finset ℕ := if i.1 < j then st.S_level i ∪ touchedVertices st.G u else ∅
      mem2 (dsSGenBase b L vCap eCap + i.1) ≤ mem2 (b + dsGenOff) ∧
      (j ≤ i.1 → mem2 (dsSGenBase b L vCap eCap + i.1) = 0) ∧
      (∀ v ∈ S', v < vCap) ∧
      (∀ v < vCap,
        mem2 (dsVSGenBase b L vCap eCap + i.1 * vCap + v) ≤ mem2 (b + dsGenOff) ∧
        ((0 < mem2 (dsSGenBase b L vCap eCap + i.1) ∧
          mem2 (dsVSGenBase b L vCap eCap + i.1 * vCap + v) =
            mem2 (dsSGenBase b L vCap eCap + i.1)) ↔ v ∈ S')) ∧
      (sLists' i).Nodup ∧ (∀ v, v ∈ sLists' i ↔ v ∈ S') ∧
      (if 0 < mem2 (dsSGenBase b L vCap eCap + i.1)
       then LinkedListIn (fun p => heapFoot x p ∨ (headHeap ≤ p ∧ p < r₁)) mem2
              (mem2 (dsSHeadBase b L vCap eCap + i.1)) (sLists' i)
       else sLists' i = []))
    (hag_S : ∀ i : Fin (L + 1),
      memFinal (dsSGenBase b L vCap eCap + i.1) = mem2 (dsSGenBase b L vCap eCap + i.1) ∧
      memFinal (dsSHeadBase b L vCap eCap + i.1) = mem2 (dsSHeadBase b L vCap eCap + i.1) ∧
      (∀ v < vCap, memFinal (dsVSGenBase b L vCap eCap + i.1 * vCap + v) =
        mem2 (dsVSGenBase b L vCap eCap + i.1 * vCap + v)))
    (hag_sfoot : ∀ p, (heapFoot x p ∨ (headHeap ≤ p ∧ p < r₁)) → memFinal p = mem2 p)
    -- Clean temporary arrays
    (hClean : (∀ v < vCap, memFinal (dsSBitBase b L vCap eCap + v) = 0 ∧
        memFinal (dsVStampBase b L vCap eCap + v) ≤ memFinal (b + dsGenOff)) ∧
      (∀ e < eCap, memFinal (dsEStampBase b L vCap eCap + e) ≤ memFinal (b + dsGenOff) ∧
        memFinal (dsKeptStampBase b L vCap eCap + e) ≤ memFinal (b + dsGenOff))) :
    let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
    let res := step st u (canonicalSparsify impl)
    ∃ x' : DynSpannerMeta L,
      x'.vCap = vCap ∧ x'.eCap = eCap ∧
      x'.intervals = x.intervals ++ [(heapStep, retFinal)] ∧
      DynSpannerStateAt L vCap eCap b memFinal x' res.state ∧
      RevHistoryInv G₀ q (canonicalSparsify impl) us (k + 1) x' := by
  intro st res
  set j := chooseLevel L q (k + 1)
  have hj_le : j ≤ L := chooseLevel_le L q (k + 1)
  have hL1 : 1 ≤ L := by omega
  have hj_ne : j ≠ 0 := by omega
  have hk_inv := hPref k le_rfl
  obtain ⟨_, _, hU_k⟩ := batchIsValid_take us G₀ k hBV hds
  obtain ⟨hu_val, hdu⟩ := hU_k u hu_some
  have hnext_inv := step_inv hVG₀ hL1 hq hGm₀ (canonicalSparsify_spec_absorb impl mMax) hBV hds
    hu_some hPref
  rcases hnext_inv with ⟨hk1_inv, _⟩
  have hst1_eq : runState (L := L) G₀ q (canonicalSparsify impl) us (k + 1) = res.state := by
    simp only [runState, res, st, hu_some]
  rcases hState with ⟨hxV, hxE, hxiv, hb1, hGval, _, _, _, _, _, hGE_cap,
    _, _, _, _, _, _, _, _, _, _, _, hDom0, _, _, _⟩
  have hcl_eq : chooseLevel L st.q (st.t + 1) = j := by rw [hk_inv.q_eq, hk_inv.t_eq]
  have hG'eq : res.state.G = st.G.applyUpdate u := by
    dsimp only [res, step]; simp only [hcl_eq, hj_ne, ↓reduceDIte]
  have hG'val : res.state.G.IsValid :=
    hG'eq ▸ isValid_applyUpdate_of_delOrSplit hGval (hk_inv.G_eq ▸ hu_val) hdu
  have hG'E_sub : res.state.G.E ⊆ st.G.E := hG'eq ▸ E_applyUpdate_subset hdu
  have hGE'_cap : ∀ e ∈ res.state.G.E, e < eCap := fun e he => hGE_cap e (hG'E_sub he)
  have hH'sub : res.state.G.IsSubgraph res.state.H := by
    have h1 := hk1_inv.H_sub
    rw [hst1_eq, ← hk1_inv.G_eq, hst1_eq] at h1
    exact h1
  have hH'V : res.state.H.V = res.state.G.V := by
    have h1 := hk1_inv.H_V
    rw [hst1_eq, ← hk1_inv.G_eq, hst1_eq] at h1
    exact h1
  have hH'val : res.state.H.IsValid := by
    rw [← hst1_eq]; exact hk1_inv.H_valid
  let jF : Fin (L + 1) := ⟨j, by omega⟩
  let x' : DynSpannerMeta L :=
    { vCap := vCap, eCap := eCap
      intervals := x.intervals ++ [(heapStep, retFinal)]
      hBuckets := fun i => r.newB i.1
      memInDom := fun i => if i.1 < j then x.memInDom i else if i.1 = j then res.state.inDom jF else ∅
      revLists := fun i v => if i.1 < j then x.revLists i v else if i.1 = j then revJ v else []
      sLists := fun i => if i.1 < j then sLists' i else [] }
  have hfoot_old : ∀ a, heapFoot x a → heapFoot x' a := fun a ⟨iv, hiv, h1, h2⟩ =>
    ⟨iv, List.mem_append_left _ hiv, h1, h2⟩
  have hfoot_new : ∀ a, heapStep ≤ a → a < retFinal → heapFoot x' a := fun a h1 h2 =>
    ⟨(heapStep, retFinal), List.mem_append_right _ List.mem_cons_self, h1, h2⟩
  have hgen_mono0 : mem0 (b + dsGenOff) ≤ memFinal (b + dsGenOff) :=
    le_trans hHdr.2.2.2.2.2.2.2.2 (le_trans hHdr.2.2.2.2.2.2.2.1 hHdr.2.2.2.2.2.2.1)
  have hgen_mono2 : mem2 (b + dsGenOff) ≤ memFinal (b + dsGenOff) :=
    le_trans hHdr.2.2.2.2.2.2.2.1 hHdr.2.2.2.2.2.2.1
  have hres_q : res.state.q = st.q := by
    dsimp only [res, step]; simp only [hcl_eq, hj_ne, ↓reduceDIte]
  have hres_t : res.state.t = st.t + 1 := by
    dsimp only [res, step]; simp only [hcl_eq, hj_ne, ↓reduceDIte]
  have hres_inDom : ∀ i : Fin (L + 1), res.state.inDom i =
      if i.1 < j then st.inDom i ∩ res.state.G.E
      else if i.1 = j then res.state.inDom jF else ∅ := by
    intro i
    by_cases h1 : i.1 < j
    · dsimp only [res, step]; simp only [hcl_eq, hj_ne, ↓reduceDIte, h1, ↓reduceIte]
    · by_cases h2 : i.1 = j
      · have hi_eq : i = jF := Fin.ext h2
        subst hi_eq; simp [jF]
      · dsimp only [res, step]; simp only [hcl_eq, hj_ne, ↓reduceDIte, h1, h2, ↓reduceIte]
  have hres_Pi_lt : ∀ i : Fin (L + 1), i.1 < j → res.state.Pi_level i = st.Pi_level i := by
    intro i hi
    dsimp only [res, step]; simp only [hcl_eq, hj_ne, ↓reduceDIte, hi, ↓reduceIte]
  have hres_S : ∀ i : Fin (L + 1), res.state.S_level i =
      if i.1 < j then st.S_level i ∪ touchedVertices st.G u else ∅ := by
    intro i
    dsimp only [res, step]; simp only [hcl_eq, hj_ne, ↓reduceDIte]
  refine ⟨x', rfl, rfl, rfl, ?_, ?_⟩
  · -- Prove `DynSpannerStateAt L vCap eCap b memFinal x' res.state`
    refine ⟨rfl, rfl, fun iv hiv => ?_, hb1, hG'val, hH'val, hH'V, hH'sub.2.1, hH'sub.2.2,
      hG'eq ▸ hGV'_cap, hGE'_cap, hHdr.1.trans hres_q.symm, hHdr.2.1.trans hres_t.symm,
      hHdr.2.2.1, hHdr.2.2.2.1, hHdr.2.2.2.2.1, hHdr.2.2.2.2.2.1,
      hGraphs.1, hGraphs.2.1, hGraphs.2.2, hBuckets.2.1, fun i => ?_, fun i => ?_, fun i => ?_,
      hClean.1, hClean.2⟩
    · rcases List.mem_append.mp hiv with hiv | hiv
      · exact hxiv iv hiv
      · simp only [List.mem_singleton] at hiv; subst hiv; exact hfix_step
    · -- `hBuckets`
      obtain ⟨hdll, hdeg⟩ := hBuckets.1 i.1 (by omega)
      exact ⟨hdll, hdeg, hBuckets.2.2 i⟩
    · -- `inDom`, `Pi_level`, `revLists`
      by_cases hlt : i.1 < j
      · -- Level `i < j`: preserved from `mem0`
        obtain ⟨hd0, hed0, hmem0, hin0, hpi0, hrev0⟩ := hDom0 i
        obtain ⟨hd_eq, he_eq, hr_eq'⟩ := hag_dom_lt i hlt
        simp only [x', hlt, ↓reduceIte]
        refine ⟨by rw [hd_eq]; exact le_trans hd0 hgen_mono0,
          fun e he => ⟨by rw [(he_eq e he).1]; exact le_trans (hed0 e he).1 hgen_mono0,
            by rw [hd_eq, (he_eq e he).1]; exact (hed0 e he).2⟩,
          hmem0, by rw [hres_inDom i, ite_eq_left_iff.mpr (fun h => absurd hlt h), hin0,
            Finset.inter_assoc, Finset.inter_eq_right.mpr hG'E_sub],
          fun e he => ?_, fun v hv => ?_⟩
        · have he_old : e ∈ st.inDom i := by
            rw [hres_inDom i] at he; simp only [hlt, ↓reduceIte] at he; exact (Finset.mem_inter.mp he).1
          have heC : e < eCap := hGE'_cap e (by
            rw [hres_inDom i] at he; simp only [hlt, ↓reduceIte] at he; exact (Finset.mem_inter.mp he).2)
          obtain ⟨hmw, hrf⟩ := hpi0 e he_old
          rw [(he_eq e heC).2, hres_Pi_lt i hlt]
          exact ⟨hmw.of_agree fun a h1 h2 => hag_foot0 a (hrf a h1 (by rw [mWalkEncode_length]; omega)),
            fun a h1 h2 => hfoot_old a (hrf a h1 h2)⟩
        · obtain ⟨hrg0, hnd0, hre0, hll0⟩ := hrev0 v hv
          rw [hd_eq, (hr_eq' v hv).1, (hr_eq' v hv).2]
          refine ⟨le_trans hrg0 hgen_mono0, hnd0, hre0, ?_⟩
          split_ifs at hll0 ⊢
          · exact (hll0.of_agree hag_foot0).mono hfoot_old
          · exact hll0
      · by_cases heq : i.1 = j
        · -- Level `i = j`: from `hLvlJ`
          have hi_eq : i = jF := Fin.ext heq
          subst hi_eq
          obtain ⟨hd_pos, hd_le, hed, hpi, hrevJ⟩ := hLvlJ
          have hdom_sub_G' : res.state.inDom jF ⊆ res.state.G.E := by
            rw [← hst1_eq, hk1_inv.G_eq]; exact hk1_inv.inDom_sub jF
          simp only [x', jF, lt_irrefl, ↓reduceIte]
          refine ⟨hd_le, hed, fun e he => hGE'_cap e (hdom_sub_G' he),
            (Finset.inter_eq_left.mpr hdom_sub_G').symm, fun e he => ?_, fun v hv => ?_⟩
          · obtain ⟨hmw, hlo, hhi⟩ := hpi e he
            exact ⟨hmw, fun a h1 h2 => hfoot_new a (le_trans hlo h1) (lt_of_lt_of_le h2 hhi)⟩
          · obtain ⟨hrg, hnd, hmem, hll⟩ := hrevJ v hv
            refine ⟨hrg, hnd, fun e he => ⟨hGE'_cap e (hdom_sub_G' ((hmem e).mp he).1),
              ((hmem e).mp he).1⟩, ?_⟩
            split_ifs at hll ⊢
            · exact hll.mono fun a ha => hfoot_new a ha.1 ha.2
            · exact hll
        · -- Level `i > j`: cleared by `dsClearAbove`
          have hgt : j < i.1 := by omega
          obtain ⟨hd_z, he_eq, hr_eq'⟩ := hDomGt i hgt
          obtain ⟨_, hed0, _, _, _, hrev0⟩ := hDom0 i
          have hdom_i : res.state.inDom i = ∅ := by rw [hres_inDom i]; simp [hlt, heq]
          exact levelDom_of_gen_zero i hd_z
            (fun e he => by rw [he_eq e he]; exact le_trans (hed0 e he).1 hgen_mono0)
            (fun v hv => by rw [hr_eq' v hv]; exact le_trans (hrev0 v hv).1 hgen_mono0)
            (by simp [x', hlt, heq]) (fun v => by simp [x', hlt, heq]) hdom_i
    · -- `S_level` and `sLists`
      obtain ⟨hsg_eq, hsh_eq, hvs_eq⟩ := hag_S i
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hSL2 i
      by_cases hlt : i.1 < j
      · simp only [hlt, ↓reduceIte] at h3 h4 h6 ⊢
        simp only [x', hlt, ↓reduceIte, hres_S i]
        rw [hsg_eq, hsh_eq]
        refine ⟨le_trans h1 hgen_mono2, h3, fun v hv => ?_, h5, h6, ?_⟩
        · rw [hvs_eq v hv]; exact ⟨le_trans (h4 v hv).1 hgen_mono2, (h4 v hv).2⟩
        · split_ifs at h7 ⊢
          · exact (h7.of_agree hag_sfoot).mono fun a ha => by
              rcases ha with ha | ⟨ha1, ha2⟩
              · exact hfoot_old a ha
              · exact hfoot_new a (le_trans hhead_in.1 ha1) (lt_of_lt_of_le ha2 hhead_in.2)
          · exact h7
      · have hge : j ≤ i.1 := by omega
        have hsz : memFinal (dsSGenBase b L vCap eCap + i.1) = 0 := by rw [hsg_eq]; exact h2 hge
        exact levelS_of_gen_zero i hsz
          (fun v hv => by rw [hvs_eq v hv]; exact le_trans (h4 v hv).1 hgen_mono2)
          (by simp [x', hlt]) (by simp [hres_S i, hlt])
  · -- Prove `RevHistoryInv G₀ q (canonicalSparsify impl) us (k + 1) x'`
    intro i
    dsimp only
    by_cases hlt : i.1 < j
    · -- Level `i < j`: `lastRebuild q L i (k + 1) = lastRebuild q L i k`
      have hndvd : ¬ phasePeriod q L i.1 ∣ (k + 1) := not_dvd_of_lt_chooseLevel hlt
      have hlr : lastRebuild q L i.1 (k + 1) = lastRebuild q L i.1 k :=
        lastRebuild_eq_of_not_dvd hndvd
      rw [hlr]
      simpa [x', hlt, hxV] using hRev i
    · by_cases heq : i.1 = j
      · -- Level `i = j`: `lastRebuild q L j (k + 1) = k + 1`
        have hdvd : phasePeriod q L i.1 ∣ (k + 1) := by rw [heq]; exact chooseLevel_dvd L q (k + 1)
        have hlr : lastRebuild q L i.1 (k + 1) = k + 1 := lastRebuild_eq_self_of_dvd hdvd
        have hi_eq : i = jF := Fin.ext heq
        subst hi_eq
        rw [hlr, hst1_eq]
        refine ⟨by simp [x', jF], fun v hv e => ?_⟩
        simpa [x', jF] using (hLvlJ.2.2.2.2 v hv).2.2.1 e
      · -- Level `i > j`: `lastRebuild q L i (k + 1) = k + 1` and `inDom i = ∅`
        have hgt : j < i.1 := by omega
        have hdvd_j : phasePeriod q L j ∣ (k + 1) := chooseLevel_dvd L q (k + 1)
        have hdvd_i : phasePeriod q L i.1 ∣ (k + 1) :=
          dvd_trans (Nat.pow_dvd_pow q (by omega)) hdvd_j
        have hlr : lastRebuild q L i.1 (k + 1) = k + 1 := lastRebuild_eq_self_of_dvd hdvd_i
        have hdom_i : res.state.inDom i = ∅ := by rw [hres_inDom i]; simp [hlt, heq]
        rw [hlr, hst1_eq, hdom_i]
        simp [x', hlt, heq]

end

end MinCostFlow.DynSpanner.Program
