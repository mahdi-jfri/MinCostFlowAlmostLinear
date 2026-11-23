module

public import MinCostFlow.DynSpanner.Program.DynSpannerUpdateLoopDefs
import Mathlib.Tactic.Ring

/-!
# Verification of step dispatch, step-output saving, and `U_H` packing (`DynSpannerUpdateLoopAux`)

Proves the pure summation and metadata-free bound lemmas, state transfer lemmas, and Word-RAM
contracts for `dsStepStmt`, `dsSaveStepOutStmt`, and `dsPackBatchUHStmt`:

* `stepPosOldSum_le_modelOldSum`, `candRevSum_eq_modelCandRevSum`, `stepPosCandSet_eq_modelCandSet`,
  `dsStepPosFullEnd_le_add_space`, `dsStepPosFullAffEnd_le_add_space`,
  `dsStepPosFullCost_le_model`: eliminate metadata `x` from `dsStepPosFullEnd`,
  `dsStepPosFullAffEnd`, and `dsStepPosFullCost`.
* `dynSpannerStateAt_of_collectD` and `dynSpannerStateAt_of_agree_lt`: state transfer lemmas.
* `dsStep_meetsContract`: unified single-step dispatcher combining `chooseLevel_meetsContract`,
  `dsStepZero_meetsContract`, and `dsStepPosFull_meetsContract` (with `stepPosFullUHWordsBound`).
* `stepPosFullUHWordsBound`: every run of `dsStepPosFullStmt` from its pre writes at most
  `len + 4 * |U_H|` as the word count of `U_H`.
* `dsSaveStepOut_meetsContract`: copies a step's `D` and `U_H` output outside `metaFoot`.
* `dsPackBatchUH_meetsContract`: packs the per-step `U_H` bodies into a single `BatchAt`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.DynSpanner

public section

/-! ## Pure `rangeCost` and `finRange` summation helpers -/

lemma rangeCost_eq_sum_range (f : ℕ → ℕ) :
    ∀ k lo hi, hi - lo = k → rangeCost f lo hi = ∑ r ∈ Finset.range k, f (lo + r) := by
  intro k
  induction k with
  | zero =>
    intro lo hi hk
    rw [rangeCost_of_le (by omega), Finset.range_zero, Finset.sum_empty]
  | succ k ih =>
    intro lo hi hk
    rw [rangeCost_step (by omega), ih (lo + 1) hi (by omega), Finset.sum_range_succ']
    simp only [Nat.add_zero, Nat.add_assoc, Nat.add_comm 1]
    omega

lemma finRange_take_succ {m i : ℕ} (hi : i < m) :
    (List.finRange m).take (i + 1) = (List.finRange m).take i ++ [⟨i, hi⟩] := by
  rw [List.take_add_one]
  have hlt : i < (List.finRange m).length := by simpa using hi
  rw [List.getElem?_eq_getElem hlt]
  simp

lemma sum_finRange_take_succ {m i : ℕ} (hi : i < m) (f : Fin m → ℕ) :
    (((List.finRange m).take (i + 1)).map f).sum =
      (((List.finRange m).take i).map f).sum + f ⟨i, hi⟩ := by
  rw [finRange_take_succ hi, List.map_append, List.sum_append]
  simp

lemma sum_finRange_eq_finset_sum : ∀ {m : ℕ} (f : Fin m → ℕ),
    ((List.finRange m).map f).sum = ∑ i : Fin m, f i := by
  intro m
  induction m with
  | zero => intro f; simp
  | succ m ih =>
    intro f
    rw [List.finRange_succ, List.map_cons, List.sum_cons, List.map_map,
      Fin.sum_univ_succ, ← ih (fun i => f i.succ)]
    rfl

lemma sum_finRange_take_le {m i : ℕ} (f : Fin m → ℕ) :
    (((List.finRange m).take i).map f).sum ≤ ∑ r : Fin m, f r := by
  rw [← sum_finRange_eq_finset_sum]
  have hsp : (List.finRange m).take i ++ (List.finRange m).drop i = List.finRange m :=
    List.take_append_drop i _
  conv_rhs => rw [← hsp, List.map_append, List.sum_append]
  exact Nat.le_add_right _ _

lemma flatMap_finRange_take_succ {α : Type*} {m i : ℕ} (hi : i < m) (f : Fin m → List α) :
    ((List.finRange m).take (i + 1)).flatMap f =
      ((List.finRange m).take i).flatMap f ++ f ⟨i, hi⟩ := by
  rw [finRange_take_succ hi, List.flatMap_append]
  simp

/-! ## Metadata-free bounds for `dsStepPosFullEnd`, `dsStepPosFullAffEnd`, and `dsStepPosFullCost` -/

private lemma delErase_length_le (u : Update) (l : List ℕ) : (delErase u l).length ≤ l.length := by
  cases u with
  | delete e => exact List.length_erase_le
  | insert _ _ _ => exact le_rfl
  | split _ _ _ _ => exact le_rfl

/-- `stepPosOldSum m.u x m.j` is at most the metadata-free `modelOldSum m`. -/
lemma stepPosOldSum_le_modelOldSum {m : StepPosModel} {vCap eCap b : ℕ} {mem : ℕ → ℕ}
    {x : DynSpannerMeta m.L}
    (hState : DynSpannerStateAt m.L vCap eCap b mem x m.st) :
    stepPosOldSum m.u x m.j ≤ modelOldSum m := by
  have hjL : m.j ≤ m.L + 1 := Nat.le_succ_of_le (chooseLevel_le m.L m.q (m.k + 1))
  have hcat := bucketsCat_length_eq_sum_range (stepPosBmid m.u x) m.j (m.L + 1 - m.j)
  have hsum_range : ∀ k (f : ℕ → ℕ), ((List.range k).map f).sum = ∑ r ∈ Finset.range k, f r := by
    intro k f
    induction k with
    | zero => simp
    | succ k ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp
  rw [stepPosOldSum, hcat, hsum_range]
  have hle_sum : (∑ d ∈ Finset.range (m.L + 1 - m.j), (stepPosBmid m.u x (m.j + d)).length) ≤
      ∑ i : Fin (m.L + 1), if m.j ≤ i.1 then (m.st.H_level i).m else 0 := by
    have hIco : (∑ d ∈ Finset.range (m.L + 1 - m.j), (stepPosBmid m.u x (m.j + d)).length) =
        ∑ i ∈ Finset.Ico m.j (m.L + 1), (stepPosBmid m.u x i).length := by
      rw [Finset.sum_Ico_eq_sum_range]
    rw [hIco]
    have hfin : (∑ i : Fin (m.L + 1), if m.j ≤ i.1 then (m.st.H_level i).m else 0) =
        ∑ i ∈ Finset.Ico m.j (m.L + 1),
          if hi : i < m.L + 1 then (m.st.H_level ⟨i, hi⟩).m else 0 := by
      have hcast : (∑ i : Fin (m.L + 1), if m.j ≤ i.1 then (m.st.H_level i).m else 0) =
          ∑ i : Fin (m.L + 1), (fun n => if m.j ≤ n then
            (if hi : n < m.L + 1 then (m.st.H_level ⟨n, hi⟩).m else 0) else 0) i.1 :=
        Finset.sum_congr rfl fun i _ => by simp [i.isLt]
      rw [hcast, Fin.sum_univ_eq_sum_range (fun n => if m.j ≤ n then
        (if hi : n < m.L + 1 then (m.st.H_level ⟨n, hi⟩).m else 0) else 0)]
      rw [← Finset.sum_filter]
      refine Finset.sum_congr (by ext i; simp; omega) fun i _ => rfl
    rw [hfin]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi_lt : i < m.L + 1 := (Finset.mem_Ico.mp hi).2
    simp only [hi_lt, ↓reduceDIte, stepPosBmid]
    refine le_trans (delErase_length_le m.u _) ?_
    have hbuck := hState.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ⟨i, hi_lt⟩
    have hminH := hState.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hnd : (x.hBuckets ⟨i, hi_lt⟩).Nodup := hbuck.1.1
    rw [← List.toFinset_card_of_nodup hnd]
    refine Finset.card_le_card fun e he => ?_
    have ⟨heH, hmin_eq⟩ := (hbuck.2.2 e).mp (List.mem_toFinset.mp he)
    have heC : e < eCap := hState.2.2.2.2.2.2.2.2.2.2.1 e (hState.2.2.2.2.2.2.2.1 heH)
    obtain ⟨i', hi'eq, hi'mem, _⟩ := (hminH e heC).2 heH
    have hii' : i' = ⟨i, hi_lt⟩ := Fin.ext (by omega)
    exact hii' ▸ hi'mem
  exact hle_sum

/-- The vertices of `S_{j-1}` are below `vCap`. -/
lemma sPrev_lt_vCap {m : StepPosModel} {vCap eCap b : ℕ} {mem : ℕ → ℕ}
    {x : DynSpannerMeta m.L}
    (hState : DynSpannerStateAt m.L vCap eCap b mem x m.st)
    (hu_val : m.st.G.UpdateIsValid m.u)
    (hupd_cap : UpdateWithinCaps vCap eCap m.u) {v : ℕ} (hv : v ∈ m.S_prev) : v < vCap := by
  have hjL : m.j ≤ m.L := chooseLevel_le m.L m.q (m.k + 1)
  rcases Finset.mem_union.mp hv with hvS | hvT
  · exact (hState.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ⟨m.j - 1, by omega⟩).2.1 v hvS
  · cases hm_u : m.u with
    | insert _ _ _ => simp [touchedVertices, hm_u] at hvT
    | delete e =>
      rw [hm_u] at hvT hu_val
      simp only [touchedVertices, Finset.mem_insert, Finset.mem_singleton] at hvT
      rcases hvT with rfl | rfl
      · exact hState.2.2.2.2.2.2.2.2.2.1 _ (hState.2.2.2.2.1 e hu_val).1
      · exact hState.2.2.2.2.2.2.2.2.2.1 _ (hState.2.2.2.2.1 e hu_val).2
    | split v₀ v' _ _ =>
      rw [hm_u] at hvT hu_val hupd_cap
      simp only [touchedVertices, Finset.mem_insert, Finset.mem_singleton] at hvT
      rcases hvT with rfl | rfl
      · exact hState.2.2.2.2.2.2.2.2.2.1 _ hu_val.1
      · exact hupd_cap

/-- Under `RevHistoryInv`, the reverse list of `v ∈ S_{j-1}` at level `i` holds the edges of
`modelRevSet m i v`. -/
lemma mem_revLists_iff_modelRevSet {m : StepPosModel} {vCap eCap b : ℕ} {mem : ℕ → ℕ}
    {x : DynSpannerMeta m.L}
    (hState : DynSpannerStateAt m.L vCap eCap b mem x m.st)
    (hRev : RevHistoryInv m.G₀ m.q (canonicalSparsify m.impl) m.us m.k x)
    (hu_val : m.st.G.UpdateIsValid m.u)
    (hupd_cap : UpdateWithinCaps vCap eCap m.u) (i : Fin (m.L + 1)) {v : ℕ} (hv : v ∈ m.S_prev)
    (e : ℕ) : e ∈ x.revLists i v ↔ e ∈ modelRevSet m i v := by
  have hvC := sPrev_lt_vCap hState hu_val hupd_cap hv
  have hmem := (hRev i).2 v (hState.1.symm ▸ hvC)
  simp only [modelRevSet, Finset.mem_filter]
  exact hmem e

/-- `candRevSum m.L m.j x.revLists m.S_prev.toList` equals the metadata-free `modelCandRevSum m`. -/
lemma candRevSum_eq_modelCandRevSum {m : StepPosModel} {vCap eCap b : ℕ} {mem : ℕ → ℕ}
    {x : DynSpannerMeta m.L}
    (hState : DynSpannerStateAt m.L vCap eCap b mem x m.st)
    (hRev : RevHistoryInv m.G₀ m.q (canonicalSparsify m.impl) m.us m.k x)
    (hu_val : m.st.G.UpdateIsValid m.u)
    (hupd_cap : UpdateWithinCaps vCap eCap m.u) :
    candRevSum m.L m.j x.revLists m.S_prev.toList = modelCandRevSum m := by
  have hjL : m.j ≤ m.L := chooseLevel_le m.L m.q (m.k + 1)
  simp only [candRevSum, modelCandRevSum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi_lt : i < m.j := Finset.mem_range.mp hi
  have hiL : i < m.L + 1 := by omega
  have hsum_toList : ∀ (S : Finset ℕ) (f : ℕ → ℕ), (S.toList.map f).sum = ∑ v ∈ S, f v := by
    intro S f
    rw [Finset.sum_eq_multiset_sum, ← Finset.coe_toList S, Multiset.map_coe, Multiset.sum_coe]
  rw [hsum_toList]
  refine Finset.sum_congr rfl fun v hv => ?_
  simp only [hiL, ↓reduceDIte]
  have hvC := sPrev_lt_vCap hState hu_val hupd_cap hv
  have hnd := ((hState.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ⟨i, hiL⟩).2.2.2.2.2 v hvC).2.1
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext e
  simp only [List.mem_toFinset]
  exact mem_revLists_iff_modelRevSet hState hRev hu_val hupd_cap ⟨i, hiL⟩ hv e

/-- Under `RevHistoryInv`, the candidates that the program enumerates are `modelCandSet m`. -/
lemma stepPosCandSet_eq_modelCandSet {m : StepPosModel} {vCap eCap b : ℕ} {mem : ℕ → ℕ}
    {x : DynSpannerMeta m.L}
    (hState : DynSpannerStateAt m.L vCap eCap b mem x m.st)
    (hRev : RevHistoryInv m.G₀ m.q (canonicalSparsify m.impl) m.us m.k x)
    (hu_val : m.st.G.UpdateIsValid m.u)
    (hupd_cap : UpdateWithinCaps vCap eCap m.u) :
    stepPosCandSet m x = modelCandSet m := by
  ext e
  simp only [stepPosCandSet, revCandSet, modelCandSet, Finset.mem_filter]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨i, v, hv, hij, he⟩
    exact ⟨i, v, hv, hij, (mem_revLists_iff_modelRevSet hState hRev hu_val hupd_cap i hv e).mp he⟩
  · rintro ⟨i, v, hv, hij, he⟩
    exact ⟨i, v, hv, hij, (mem_revLists_iff_modelRevSet hState hRev hu_val hupd_cap i hv e).mpr he⟩

lemma dsStepPosFullEnd_le_add_space {m : StepPosModel} {mMax vCap eCap b len heapStep : ℕ}
    {mem : ℕ → ℕ} {x : DynSpannerMeta m.L}
    (hState : DynSpannerStateAt m.L vCap eCap b mem x m.st) :
    dsStepPosFullEnd m mMax vCap eCap len x heapStep ≤
      heapStep + dsStepPosSpaceAt m mMax vCap eCap len := by
  have hold := stepPosOldSum_le_modelOldSum hState
  have hle_end : dsStepPosFullEnd m mMax vCap eCap len x heapStep ≤
      heapStep + dsStepPosEndDelta m mMax vCap eCap len := by
    simp only [dsStepPosFullEnd, dsStepPosEndDelta]
    split_ifs
    · simp only [dsStepPosNonEmptyEnd, spOutBound]; omega
    · omega
  exact le_trans hle_end (Nat.add_le_add_left (le_max_left _ _) _)

lemma dsStepPosFullAffEnd_le_add_space (m : StepPosModel) (mMax vCap eCap len heapStep : ℕ) :
    dsStepPosFullAffEnd m vCap eCap len heapStep ≤
      heapStep + dsStepPosSpaceAt m mMax vCap eCap len := by
  have h1 : dsStepPosFullAffEnd m vCap eCap len heapStep =
      heapStep + dsStepPosAffDelta m vCap eCap len := by
    simp only [dsStepPosFullAffEnd, dsStepPosAffDelta]; omega
  rw [h1]
  exact Nat.add_le_add_left (le_max_right _ _) _

lemma dsStepPosFullCost_le_model {m : StepPosModel} {mMax vCap eCap b len : ℕ}
    {mem : ℕ → ℕ} {x : DynSpannerMeta m.L}
    (hState : DynSpannerStateAt m.L vCap eCap b mem x m.st)
    (hRev : RevHistoryInv m.G₀ m.q (canonicalSparsify m.impl) m.us m.k x)
    (hu_val : m.st.G.UpdateIsValid m.u)
    (hupd_cap : UpdateWithinCaps vCap eCap m.u) :
    dsStepPosFullCost m mMax vCap eCap len x ≤ dsStepPosCostModel m mMax vCap eCap len := by
  have hold := stepPosOldSum_le_modelOldSum hState
  have hrev := candRevSum_eq_modelCandRevSum hState hRev hu_val hupd_cap
  have hcand := stepPosCandSet_eq_modelCandSet hState hRev hu_val hupd_cap
  simp only [dsStepPosFullCost, dsStepPosCostModel, dsStepPosFullAffCost, dsStepPosAffCostModel,
    dsStepPosCost, dsStepPosNonEmptyCost, dsStepPosEmptyCost, dsStepPosEpilogueCost]
  rw [hrev, hcand]
  split_ifs <;> omega

/-! ## State transfer lemmas (`dynSpannerStateAt_of_collectD`, `dynSpannerStateAt_of_agree_lt`) -/

private lemma idx_lt_mul_ul {i n e m : ℕ} (hi : i < n) (he : e < m) : i * m + e < n * m :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_left he _)
    (by simpa [Nat.succ_mul] using Nat.mul_le_mul_right m hi)

lemma collectD_lt_eStamp_bounds (b L vCap eCap : ℕ) :
    b + dsGenOff < dsGPtr b ∧
    (∀ off < dsHdrSize, b + off < dsEStampBase b L vCap eCap) ∧
    dsGPtr b + dynGraphSize vCap eCap ≤ dsEStampBase b L vCap eCap ∧
    dsHPtr b vCap eCap + dynGraphSize vCap eCap ≤ dsEStampBase b L vCap eCap ∧
    dsAuxPtr b vCap eCap + dynGraphSize vCap eCap ≤ dsEStampBase b L vCap eCap ∧
    dsMinHBase b vCap eCap + eCap ≤ dsEStampBase b L vCap eCap ∧
    dsHNextBase b vCap eCap + eCap ≤ dsEStampBase b L vCap eCap ∧
    dsHPrevBase b vCap eCap + eCap ≤ dsEStampBase b L vCap eCap ∧
    dsHHeadBase b vCap eCap + (L + 1) ≤ dsEStampBase b L vCap eCap ∧
    dsHDegDummyBase b L vCap eCap + (L + 1) ≤ dsEStampBase b L vCap eCap ∧
    dsDomGenBase b L vCap eCap + (L + 1) ≤ dsEStampBase b L vCap eCap ∧
    dsEdgeDomGenBase b L vCap eCap + (L + 1) * eCap ≤ dsEStampBase b L vCap eCap ∧
    dsPiPtrBase b L vCap eCap + (L + 1) * eCap ≤ dsEStampBase b L vCap eCap ∧
    dsRevGenBase b L vCap eCap + (L + 1) * vCap ≤ dsEStampBase b L vCap eCap ∧
    dsRevHeadBase b L vCap eCap + (L + 1) * vCap ≤ dsEStampBase b L vCap eCap ∧
    dsSGenBase b L vCap eCap + (L + 1) ≤ dsEStampBase b L vCap eCap ∧
    dsVSGenBase b L vCap eCap + (L + 1) * vCap ≤ dsEStampBase b L vCap eCap ∧
    dsSHeadBase b L vCap eCap + (L + 1) ≤ dsEStampBase b L vCap eCap ∧
    dsSBitBase b L vCap eCap + vCap ≤ dsEStampBase b L vCap eCap ∧
    dsVStampBase b L vCap eCap + vCap = dsEStampBase b L vCap eCap ∧
    dsEStampBase b L vCap eCap + eCap = dsKeptStampBase b L vCap eCap ∧
    dsKeptStampBase b L vCap eCap + eCap ≤ b + dsFixedSize L vCap eCap := by
  obtain ⟨hgo, hgh, hha, ham, hmn, hnp, hph, hhd, hdd, hde, hep, hpr, hrr, hrs, hsv, hvs, hsh, hsb,
    hve, hek, hkm, hmf⟩ := stepZero_fixed_order b L vCap eCap
  have h1 : dsVStampBase b L vCap eCap ≤ dsEStampBase b L vCap eCap := hve ▸ Nat.le_add_right _ _
  have h2 : dsSBitBase b L vCap eCap ≤ dsEStampBase b L vCap eCap := (hsb ▸ Nat.le_add_right _ _).trans h1
  have h3 : dsSHeadBase b L vCap eCap ≤ dsEStampBase b L vCap eCap := (hsh ▸ Nat.le_add_right _ _).trans h2
  have h4 : dsVSGenBase b L vCap eCap ≤ dsEStampBase b L vCap eCap := (hvs ▸ Nat.le_add_right _ _).trans h3
  have h5 : dsSGenBase b L vCap eCap ≤ dsEStampBase b L vCap eCap := (hsv ▸ Nat.le_add_right _ _).trans h4
  have h6 : dsRevHeadBase b L vCap eCap ≤ dsEStampBase b L vCap eCap := (hrs ▸ Nat.le_add_right _ _).trans h5
  have h7 : dsRevGenBase b L vCap eCap ≤ dsEStampBase b L vCap eCap := (hrr ▸ Nat.le_add_right _ _).trans h6
  have h8 : dsPiPtrBase b L vCap eCap ≤ dsEStampBase b L vCap eCap := (hpr ▸ Nat.le_add_right _ _).trans h7
  have h9 : dsEdgeDomGenBase b L vCap eCap ≤ dsEStampBase b L vCap eCap := (hep ▸ Nat.le_add_right _ _).trans h8
  have h10 : dsDomGenBase b L vCap eCap ≤ dsEStampBase b L vCap eCap := (hde ▸ Nat.le_add_right _ _).trans h9
  have h11 : dsHDegDummyBase b L vCap eCap ≤ dsEStampBase b L vCap eCap := (hdd ▸ Nat.le_add_right _ _).trans h10
  have h12 : dsHHeadBase b vCap eCap ≤ dsEStampBase b L vCap eCap := (hhd ▸ Nat.le_add_right _ _).trans h11
  have h13 : dsHPrevBase b vCap eCap ≤ dsEStampBase b L vCap eCap := (hph ▸ Nat.le_add_right _ _).trans h12
  have h14 : dsHNextBase b vCap eCap ≤ dsEStampBase b L vCap eCap := (hnp ▸ Nat.le_add_right _ _).trans h13
  have h15 : dsMinHBase b vCap eCap ≤ dsEStampBase b L vCap eCap := (hmn ▸ Nat.le_add_right _ _).trans h14
  have h16 : dsAuxPtr b vCap eCap ≤ dsEStampBase b L vCap eCap := (ham ▸ Nat.le_add_right _ _).trans h15
  have h17 : dsHPtr b vCap eCap ≤ dsEStampBase b L vCap eCap := (hha ▸ Nat.le_add_right _ _).trans h16
  have h18 : dsGPtr b ≤ dsEStampBase b L vCap eCap := (hgh ▸ Nat.le_add_right _ _).trans h17
  refine ⟨hgo, fun off ho => lt_of_lt_of_le (Nat.add_lt_add_left ho b) h18,
    hgh.symm ▸ h17, hha.symm ▸ h16, ham.symm ▸ h15, hmn.symm ▸ h14, hnp.symm ▸ h13,
    hph.symm ▸ h12, hhd.symm ▸ h11, hdd.symm ▸ h10, hde.symm ▸ h9, hep.symm ▸ h8,
    hpr.symm ▸ h7, hrr.symm ▸ h6, hrs.symm ▸ h5, hsv.symm ▸ h4, hvs.symm ▸ h3,
    hsh.symm ▸ h2, hsb.symm ▸ h1, hve, hek, hkm.symm ▸ (hmf ▸ Nat.le_add_right _ _)⟩

/-- Updating `mem[b + dsGenOff]` to `g + 1` (or leaving `mem[b + dsGenOff]` unchanged), stamping
`eStamp[e] ≤ mem'[b + dsGenOff]`, and writing outside `[b, b + dsFixedSize) ∪ heapFoot x`
preserves `DynSpannerStateAt L vCap eCap b mem' x st`. The words below `b` are not read. -/
theorem dynSpannerStateAt_of_collectD_foot {L vCap eCap b : ℕ} {mem mem' : ℕ → ℕ}
    {x : DynSpannerMeta L} {st : DynSpannerState L}
    (hState : DynSpannerStateAt L vCap eCap b mem x st)
    (hgen : mem (b + dsGenOff) ≤ mem' (b + dsGenOff))
    (heS : ∀ e < eCap, mem' (dsEStampBase b L vCap eCap + e) ≤ mem' (b + dsGenOff))
    (hOther : ∀ a, a ≠ b + dsGenOff →
      (a < dsEStampBase b L vCap eCap ∨ dsEStampBase b L vCap eCap + eCap ≤ a) →
      ((b ≤ a ∧ a < b + dsFixedSize L vCap eCap) ∨ heapFoot x a) → mem' a = mem a) :
    DynSpannerStateAt L vCap eCap b mem' x st := by
  obtain ⟨hgo, hhdr, hG_e, hH_e, hA_e, hM_e, hN_e, hP_e, hHd_e, hDg_e, hDm_e, hEd_e, hPi_e,
    hRg_e, hRh_e, hSg_e, hVs_e, hSh_e, hSb_e, hVs_eq, hek, hks_top⟩ :=
    collectD_lt_eStamp_bounds b L vCap eCap
  have heSt_le_fix : dsEStampBase b L vCap eCap ≤ b + dsFixedSize L vCap eCap :=
    (Nat.le_add_right _ _).trans (hek.symm ▸ ((Nat.le_add_right _ _).trans hks_top))
  have hb_est : b ≤ dsEStampBase b L vCap eCap :=
    le_trans (Nat.le_add_right _ _)
      (le_of_lt (lt_of_lt_of_le hgo (le_trans (Nat.le_add_right _ _) hG_e)))
  have hlt_est : ∀ a, b ≤ a → a ≠ b + dsGenOff → a < dsEStampBase b L vCap eCap → mem' a = mem a :=
    fun a hb hne hlt => hOther a hne (Or.inl hlt) (Or.inl ⟨hb, lt_of_lt_of_le hlt heSt_le_fix⟩)
  have hgt_est : ∀ a, dsEStampBase b L vCap eCap + eCap ≤ a →
      (a < b + dsFixedSize L vCap eCap ∨ heapFoot x a) → mem' a = mem a :=
    fun a hge hdom =>
      hOther a (ne_of_gt (lt_of_lt_of_le (lt_of_lt_of_le hgo (le_trans (Nat.le_add_right _ _) hG_e))
        (le_trans (Nat.le_add_right _ _) hge))) (Or.inr hge)
        (hdom.imp_left fun h => ⟨le_trans hb_est (le_trans (Nat.le_add_right _ _) hge), h⟩)
  have hgt_G : ∀ a, dsGPtr b ≤ a → a < dsEStampBase b L vCap eCap → mem' a = mem a :=
    fun a h1 h2 => hlt_est a (le_trans (Nat.le_add_right _ _) h1) (ne_of_gt (lt_of_lt_of_le hgo h1)) h2
  have hG_le_H : dsGPtr b ≤ dsHPtr b vCap eCap := Nat.le_add_right _ _
  have hG_le_A : dsGPtr b ≤ dsAuxPtr b vCap eCap := hG_le_H.trans (Nat.le_add_right _ _)
  have hG_le_M : dsGPtr b ≤ dsMinHBase b vCap eCap := hG_le_A.trans (Nat.le_add_right _ _)
  have hG_le_N : dsGPtr b ≤ dsHNextBase b vCap eCap := hG_le_M.trans (Nat.le_add_right _ _)
  have hG_le_P : dsGPtr b ≤ dsHPrevBase b vCap eCap := hG_le_N.trans (Nat.le_add_right _ _)
  have hG_le_Hd : dsGPtr b ≤ dsHHeadBase b vCap eCap := hG_le_P.trans (Nat.le_add_right _ _)
  have hG_le_Dg : dsGPtr b ≤ dsHDegDummyBase b L vCap eCap := hG_le_Hd.trans (Nat.le_add_right _ _)
  have hG_le_Dm : dsGPtr b ≤ dsDomGenBase b L vCap eCap := hG_le_Dg.trans (Nat.le_add_right _ _)
  have hG_le_Ed : dsGPtr b ≤ dsEdgeDomGenBase b L vCap eCap := hG_le_Dm.trans (Nat.le_add_right _ _)
  have hG_le_Pi : dsGPtr b ≤ dsPiPtrBase b L vCap eCap := hG_le_Ed.trans (Nat.le_add_right _ _)
  have hG_le_Rg : dsGPtr b ≤ dsRevGenBase b L vCap eCap := hG_le_Pi.trans (Nat.le_add_right _ _)
  have hG_le_Rh : dsGPtr b ≤ dsRevHeadBase b L vCap eCap := hG_le_Rg.trans (Nat.le_add_right _ _)
  have hG_le_Sg : dsGPtr b ≤ dsSGenBase b L vCap eCap := hG_le_Rh.trans (Nat.le_add_right _ _)
  have hG_le_Vs : dsGPtr b ≤ dsVSGenBase b L vCap eCap := hG_le_Sg.trans (Nat.le_add_right _ _)
  have hG_le_Sh : dsGPtr b ≤ dsSHeadBase b L vCap eCap := hG_le_Vs.trans (Nat.le_add_right _ _)
  have hG_le_Sb : dsGPtr b ≤ dsSBitBase b L vCap eCap := hG_le_Sh.trans (Nat.le_add_right _ _)
  have hG_le_Vt : dsGPtr b ≤ dsVStampBase b L vCap eCap := hG_le_Sb.trans (Nat.le_add_right _ _)
  have hhf_ag : ∀ a, heapFoot x a → mem' a = mem a := fun a ha => by
    rcases ha with ⟨iv, hiv, h1, h2⟩
    have hfix_iv := hState.2.2.1 iv hiv
    have heSt_top : dsEStampBase b L vCap eCap + eCap ≤ b + dsFixedSize L vCap eCap :=
      hek.symm ▸ ((Nat.le_add_right _ _).trans hks_top)
    exact hgt_est a (heSt_top.trans (hfix_iv.trans h1)) (Or.inr ⟨iv, hiv, h1, h2⟩)
  rcases hState with ⟨hvC, heC, hivs, hb1, hGv, hHv, hHV, hHE, hHend, hGVc, hGEc,
    hQ, hT, hL, hV, hE, hgen1, hG, hH, hAux, hminH, hBuck, hDom, hS, hSBit, hES⟩
  have hle_gen : ∀ u, u ≤ mem (b + dsGenOff) → u ≤ mem' (b + dsGenOff) := fun u hu => le_trans hu hgen
  refine ⟨hvC, heC, hivs, hb1, hGv, hHv, hHV, hHE, hHend, hGVc, hGEc,
    (hlt_est _ (Nat.le_add_right _ _) (by simp [dsQOff, dsGenOff]) (hhdr dsQOff (by decide))).trans hQ,
    (hlt_est _ (Nat.le_add_right _ _) (by simp [dsTOff, dsGenOff]) (hhdr dsTOff (by decide))).trans hT,
    (hlt_est _ (Nat.le_add_right _ _) (by simp [dsLOff, dsGenOff]) (hhdr dsLOff (by decide))).trans hL,
    (hlt_est _ (Nat.le_add_right _ _) (by simp [dsVCapOff, dsGenOff]) (hhdr dsVCapOff (by decide))).trans hV,
    (hlt_est _ (Nat.le_add_right _ _) (by simp [dsECapOff, dsGenOff]) (hhdr dsECapOff (by decide))).trans hE,
    le_trans hgen1 hgen,
    dynGraphAt_of_agree hG (fun a h1 h2 => hgt_G a h1 (lt_of_lt_of_le h2 hG_e)),
    dynGraphAt_of_agree hH (fun a h1 h2 => hgt_G a (hG_le_H.trans h1) (lt_of_lt_of_le h2 hH_e)),
    dynGraphAt_of_agree hAux (fun a h1 h2 => hgt_G a (hG_le_A.trans h1) (lt_of_lt_of_le h2 hA_e)),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    rw [hgt_G _ (hG_le_M.trans (Nat.le_add_right _ _)) (lt_of_lt_of_le (Nat.add_lt_add_left he _) hM_e)]
    exact hminH e he
  · intro i
    obtain ⟨hdll, hdeg, hmem⟩ := hBuck i
    refine ⟨hdll.of_agree
        (hgt_G _ (hG_le_Hd.trans (Nat.le_add_right _ _)) (lt_of_lt_of_le (Nat.add_lt_add_left i.2 _) hHd_e))
        (fun e he => hgt_G _ (hG_le_P.trans (Nat.le_add_right _ _))
          (lt_of_lt_of_le (Nat.add_lt_add_left (hdll.2.1 e he) _) hP_e))
        (fun e he => hgt_G _ (hG_le_N.trans (Nat.le_add_right _ _))
          (lt_of_lt_of_le (Nat.add_lt_add_left (hdll.2.1 e he) _) hN_e)),
      (hgt_G _ (hG_le_Dg.trans (Nat.le_add_right _ _)) (lt_of_lt_of_le (Nat.add_lt_add_left i.2 _) hDg_e)).trans hdeg,
      fun e => ?_⟩
    rw [hmem e]
    by_cases he : e < eCap
    · rw [hgt_G _ (hG_le_M.trans (Nat.le_add_right _ _)) (lt_of_lt_of_le (Nat.add_lt_add_left he _) hM_e)]
    · constructor <;> rintro ⟨h1, _⟩ <;> exact (he (hGEc e (hHE h1))).elim
  · intro i
    obtain ⟨hdg, hed, hinC, hinE, hpi, hrev⟩ := hDom i
    have hdg_ag : mem' (dsDomGenBase b L vCap eCap + i.1) = mem (dsDomGenBase b L vCap eCap + i.1) :=
      hgt_G _ (hG_le_Dm.trans (Nat.le_add_right _ _)) (lt_of_lt_of_le (Nat.add_lt_add_left i.2 _) hDm_e)
    refine ⟨hle_gen _ (hdg_ag ▸ hdg), fun e he => ?_, hinC, hinE, fun e he => ?_, fun v hv => ?_⟩
    · have hmul := idx_lt_mul_ul i.2 he
      have hed_ag : mem' (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e) =
          mem (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e) :=
        hgt_G _ (hG_le_Ed.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))
          (lt_of_lt_of_le (by rw [Nat.add_assoc]; exact Nat.add_lt_add_left hmul _) hEd_e)
      rw [hed_ag, hdg_ag]; exact ⟨hle_gen _ (hed e he).1, (hed e he).2⟩
    · have heC' : e < eCap := hGEc e (by rw [hinE] at he; exact (Finset.mem_inter.mp he).2)
      have hmul := idx_lt_mul_ul i.2 heC'
      have hpi_ag : mem' (dsPiPtrBase b L vCap eCap + i.1 * eCap + e) =
          mem (dsPiPtrBase b L vCap eCap + i.1 * eCap + e) :=
        hgt_G _ (hG_le_Pi.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))
          (lt_of_lt_of_le (by rw [Nat.add_assoc]; exact Nat.add_lt_add_left hmul _) hPi_e)
      obtain ⟨hmw, hrng⟩ := hpi e he
      rw [hpi_ag]
      refine ⟨hmw.of_agree fun a h1 h2 => hhf_ag a (hrng a h1 (by
        rw [mWalkEncode_length]; rw [Nat.add_assoc] at h2; exact h2)), hrng⟩
    · have hmul := idx_lt_mul_ul i.2 hv
      have hrg_ag : mem' (dsRevGenBase b L vCap eCap + i.1 * vCap + v) =
          mem (dsRevGenBase b L vCap eCap + i.1 * vCap + v) :=
        hgt_G _ (hG_le_Rg.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))
          (lt_of_lt_of_le (by rw [Nat.add_assoc]; exact Nat.add_lt_add_left hmul _) hRg_e)
      have hrh_ag : mem' (dsRevHeadBase b L vCap eCap + i.1 * vCap + v) =
          mem (dsRevHeadBase b L vCap eCap + i.1 * vCap + v) :=
        hgt_G _ (hG_le_Rh.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))
          (lt_of_lt_of_le (by rw [Nat.add_assoc]; exact Nat.add_lt_add_left hmul _) hRh_e)
      obtain ⟨hrg, hnd, hrm, hll⟩ := hrev v hv
      rw [hdg_ag, hrg_ag, hrh_ag]
      refine ⟨hle_gen _ hrg, hnd, hrm, ?_⟩
      split_ifs at hll ⊢
      · exact hll.of_agree hhf_ag
      · exact hll
  · intro i
    obtain ⟨hsg, hsC, hvs, hnd, hsm, hll⟩ := hS i
    have hsg_ag : mem' (dsSGenBase b L vCap eCap + i.1) = mem (dsSGenBase b L vCap eCap + i.1) :=
      hgt_G _ (hG_le_Sg.trans (Nat.le_add_right _ _)) (lt_of_lt_of_le (Nat.add_lt_add_left i.2 _) hSg_e)
    have hsh_ag : mem' (dsSHeadBase b L vCap eCap + i.1) = mem (dsSHeadBase b L vCap eCap + i.1) :=
      hgt_G _ (hG_le_Sh.trans (Nat.le_add_right _ _)) (lt_of_lt_of_le (Nat.add_lt_add_left i.2 _) hSh_e)
    refine ⟨hle_gen _ (hsg_ag ▸ hsg), hsC, fun v hv => ?_, hnd, hsm, ?_⟩
    · have hmul := idx_lt_mul_ul i.2 hv
      have hvs_ag : mem' (dsVSGenBase b L vCap eCap + i.1 * vCap + v) =
          mem (dsVSGenBase b L vCap eCap + i.1 * vCap + v) :=
        hgt_G _ (hG_le_Vs.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))
          (lt_of_lt_of_le (by rw [Nat.add_assoc]; exact Nat.add_lt_add_left hmul _) hVs_e)
      rw [hvs_ag, hsg_ag]; exact ⟨hle_gen _ (hvs v hv).1, (hvs v hv).2⟩
    · rw [hsg_ag, hsh_ag]
      split_ifs at hll ⊢
      · exact hll.of_agree hhf_ag
      · exact hll
  · intro v hv
    have hsb_ag : mem' (dsSBitBase b L vCap eCap + v) = mem (dsSBitBase b L vCap eCap + v) :=
      hgt_G _ (hG_le_Sb.trans (Nat.le_add_right _ _)) (lt_of_lt_of_le (Nat.add_lt_add_left hv _) hSb_e)
    have hvs_ag : mem' (dsVStampBase b L vCap eCap + v) = mem (dsVStampBase b L vCap eCap + v) :=
      hgt_G _ (hG_le_Vt.trans (Nat.le_add_right _ _)) (hVs_eq ▸ Nat.add_lt_add_left hv _)
    rw [hsb_ag, hvs_ag]
    exact ⟨(hSBit v hv).1, hle_gen _ (hSBit v hv).2⟩
  · intro e he
    have hks_ag : mem' (dsKeptStampBase b L vCap eCap + e) = mem (dsKeptStampBase b L vCap eCap + e) :=
      hgt_est _ (hek ▸ Nat.le_add_right _ _) (Or.inl (lt_of_lt_of_le (Nat.add_lt_add_left he _) hks_top))
    rw [hks_ag]
    exact ⟨heS e he, hle_gen _ (hES e he).2⟩

/-- `dynSpannerStateAt_of_collectD_foot` with agreement asked on every address below
`b + dsFixedSize` outside the generation word and the edge stamps. -/
theorem dynSpannerStateAt_of_collectD {L vCap eCap b : ℕ} {mem mem' : ℕ → ℕ}
    {x : DynSpannerMeta L} {st : DynSpannerState L}
    (hState : DynSpannerStateAt L vCap eCap b mem x st)
    (hgen : mem (b + dsGenOff) ≤ mem' (b + dsGenOff))
    (heS : ∀ e < eCap, mem' (dsEStampBase b L vCap eCap + e) ≤ mem' (b + dsGenOff))
    (hOther : ∀ a, a ≠ b + dsGenOff →
      (a < dsEStampBase b L vCap eCap ∨ dsEStampBase b L vCap eCap + eCap ≤ a) →
      (a < b + dsFixedSize L vCap eCap ∨ heapFoot x a) → mem' a = mem a) :
    DynSpannerStateAt L vCap eCap b mem' x st :=
  dynSpannerStateAt_of_collectD_foot hState hgen heS
    (fun a h1 h2 h3 => hOther a h1 h2 (h3.imp_left And.right))

/-- Agreeing on all addresses `< bound` above the fixed block and `heapFoot x` preserves
`DynSpannerStateAt`. -/
lemma dynSpannerStateAt_of_agree_lt {L vCap eCap b bound : ℕ} {mem mem' : ℕ → ℕ}
    {x : DynSpannerMeta L} {st : DynSpannerState L}
    (hState : DynSpannerStateAt L vCap eCap b mem x st)
    (hfix : b + dsFixedSize L vCap eCap ≤ bound)
    (hfoot : ∀ a, heapFoot x a → a < bound)
    (hag : ∀ a < bound, mem' a = mem a) :
    DynSpannerStateAt L vCap eCap b mem' x st := by
  have hlt := stepZero_fixed_lt b L vCap eCap
  have hgen_eq : mem' (b + dsGenOff) = mem (b + dsGenOff) :=
    hag _ (lt_of_lt_of_le (hlt.1 dsGenOff (by decide)).2 hfix)
  refine dynSpannerStateAt_of_collectD hState (le_of_eq hgen_eq.symm) (fun e he => ?_)
    (fun a _ _ hdom => ?_)
  · rw [hag _ (lt_of_lt_of_le (hlt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e he).2 hfix), hgen_eq]
    exact (hState.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 e he).1
  · rcases hdom with hltF | hhf
    · exact hag a (lt_of_lt_of_le hltF hfix)
    · exact hag a (hfoot a hhf)

/-! ## 1. Verification of `dsStepStmt` -/

/-- The `U_H` word-length bound holds for every run of `dsStepPosFullStmt` from its
precondition. The precondition makes the arguments words (they lie below
`dsStepPosFullAffEnd`, which is below `2 ^ w`), so `dsStepPosFull_meetsContract` gives a run whose
post has the bound, and that run is the given one by `Runs.det`. -/
theorem stepPosFullUHWordsBound {w vCap eCap b mMax : ℕ} {impl : SparsifyImpl} {p : Program}
    {bs : StepPosFullBases} (hp : HasStepPosFullProcs impl p bs) :
    StepPosFullUHWordsBound w vCap eCap b mMax impl p bs.bFull := by
  intro m len x updPtr heapStep mem pos ω body o st' c himpl hget hpre hrun
  subst himpl
  have hpre' := hpre
  obtain ⟨updPtr', heapStep', hargs, -, -, -, -, -, -, -, -, -, -, -, -, -, hfix, -, -, -, hAffEnd,
    hgen, -, hfixU, hupd, -⟩ := hpre'
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨-, -, rfl, rfl, -⟩ := hargs
  have hW : ∀ a ∈ [b, m.j, updPtr, heapStep, len], a < 2 ^ w := by
    have hA : heapStep + len + m.j < 2 ^ w := by
      simp only [dsStepPosFullAffEnd] at hAffEnd; omega
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> omega
  obtain ⟨body', hget', o', st'', c', hrun', ⟨_, _, hargs', _, _, _, hUH⟩, _⟩ :=
    dsStepPosFull_meetsContract m mMax w vCap eCap b len x hp _ mem pos ω hW hpre
  rw [hget] at hget'
  cases hget'
  obtain ⟨-, rfl, -⟩ := hrun.det hrun'
  simp only [List.cons.injEq, and_true] at hargs'
  obtain ⟨-, -, -, rfl, -⟩ := hargs'
  exact hUH

private lemma dsStepPosFull_meetsContract_ext (m : StepPosModel) (mMax w vCap eCap b len : ℕ)
    (x : DynSpannerMeta m.L) {p : Program} {bs : StepPosFullBases}
    (hp : HasStepPosFullProcs m.impl p bs) :
    MeetsContract w p (bs.bFull + stepPosFullIdx)
      { (dsStepPosFullContract m mMax w vCap eCap b len x) with
        post := fun args mem ret mem' =>
          (dsStepPosFullContract m mMax w vCap eCap b len x).post args mem ret mem' ∧
          ∀ updPtr heapStep, args = [b, m.j, updPtr, heapStep, len] →
            mem' (heapStep + 2) ≤ len + 4 * m.res.UH.length } := by
  intro args mem pos ω hW hpre
  obtain ⟨body, hget, o, st', c, hrun, hpost, hcost⟩ :=
    dsStepPosFull_meetsContract m mMax w vCap eCap b len x hp args mem pos ω hW hpre
  have ⟨updPtr, heapStep, hargs, _⟩ := hpre
  subst hargs
  refine ⟨body, hget, o, st', c, hrun, ⟨hpost, fun u' h' heq => ?_⟩, hcost⟩
  simp only [List.cons.injEq, and_true] at heq
  rcases heq with ⟨_, _, rfl, rfl, _⟩
  exact stepPosFullUHWordsBound hp m len x updPtr heapStep mem pos ω body o st' c rfl hget hpre
    hrun

/-- `dsStepStmt` meets `dsStepContract`: computes `j := chooseLevel L q (t + 1)` and dispatches to
`dsStepZeroStmt` (`j = 0`) or `dsStepPosFullStmt` (`0 < j`). -/
theorem dsStep_meetsContract {G₀ : MGraph} {impl : SparsifyImpl}
    {mMax w L q vCap eCap b k : ℕ} {us : List Update} {u : Update} {len : ℕ}
    {x : DynSpannerMeta L} {p : Program} {bs : UpdateLoopBases}
    (hps : HasUpdateLoopProcs impl p bs) :
    MeetsContract w p (bs.bUL + updateLoopIdxStep)
      (dsStepContract G₀ impl mMax w L q vCap eCap b k us u len x) := by
  refine meetsContract_of_runs
    (hps.hpUL.get (i := updateLoopIdxStep) (by simp [updateLoopProcs, updateLoopIdxStep])) ?_
  rintro args mem0 pos ω _ ⟨updPtr, heapStep, rfl, hw16, hL1, hq1, hVG₀, hGm₀, hE₀_cap, hBV, hds,
    hu_some, hPref, hState, hRev, hfix, hfoot_lt, hz0, hsp, hgen_w, hk_w, hq_w, hWOK, hfixU,
    hupd_le, hupd_foot, hupd_w, hupd_at, hupd_cap⟩
  set st := runState (L := L) G₀ q (canonicalSparsify impl) us k
  have hfix_w : b + dsFixedSize L vCap eCap < 2 ^ w := by omega
  have hltF := stepZero_fixed_lt b L vCap eCap
  have hL_w : L < 2 ^ w := by
    have h1 := (hltF.2.2.2.2.2.2.2.1 L (Nat.lt_succ_self L)).2
    omega
  have hmemQ : mem0 (b + dsQOff) = q :=
    hState.2.2.2.2.2.2.2.2.2.2.2.1.trans (hPref k le_rfl).q_eq
  have hmemT : mem0 (b + dsTOff) = k :=
    hState.2.2.2.2.2.2.2.2.2.2.2.2.1.trans (hPref k le_rfl).t_eq
  have hmemL : mem0 (b + dsLOff) = L := hState.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbL_lt : b + dsLOff < 2 ^ w := lt_trans (hltF.1 dsLOff (by decide)).2 hfix_w
  have hbQ_lt : b + dsQOff < 2 ^ w := lt_trans (hltF.1 dsQOff (by decide)).2 hfix_w
  have hbT_lt : b + dsTOff < 2 ^ w := lt_trans (hltF.1 dsTOff (by decide)).2 hfix_w
  simp only [updateLoopProcs, updateLoopIdxStep, List.getElem_cons_zero]
  dsimp only [dsStepStmt]
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := L)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_const (by dsimp only [dsLOff]; omega)) hbL_lt) hmemL) ?_
  refine runs_seq_assign_le (v := q)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_const (by dsimp only [dsQOff]; omega)) hbQ_lt) hmemQ) ?_
  refine runs_seq_assign_le (v := k)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_const (by dsimp only [dsTOff]; omega)) hbT_lt) hmemT) ?_
  refine runs_seq_call_le (vs := [L, q, k + 1])
    (chooseLevel_meetsContract (w := w) (L := L) (q := q) (t := k + 1) hps.hpSZ.hpPhase)
    (by simp [evalArgs, Expr.eval, BinOp.eval, show (1 : ℕ) < 2 ^ w by omega, hk_w])
    (fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl <;> omega)
    ⟨rfl, hw16, hq1, hL_w, hq_w, hk_w⟩ ?_
  rintro j mem1 _ ⟨_, hm1, hj_eq⟩
  dsimp only at hm1
  subst mem1; subst j
  refine runs_cond_le (v := chooseLevel L q (k + 1)) (Expr.eval_reg_of_eq (by simp))
    (fun hjne => ?_) (fun hj0 => ?_)
  · have hjpos : 0 < chooseLevel L q (k + 1) := Nat.pos_of_ne_zero hjne
    have hjL : chooseLevel L q (k + 1) ≤ L := chooseLevel_le L q (k + 1)
    let m : StepPosModel := ⟨G₀, impl, L, q, k, us, u⟩
    have hu_val : m.st.G.UpdateIsValid m.u := by
      obtain ⟨_, _, hUk⟩ := batchIsValid_take us G₀ k hBV hds
      have hG := (hPref k le_rfl).G_eq
      exact hG.symm ▸ (hUk u hu_some).1
    have hsp' : heapStep + dsStepPosSpaceAt m mMax vCap eCap len < 2 ^ w := by
      simpa [dsStepSpaceAt, hu_some, hjne, m] using hsp
    have hEnd_lt : dsStepPosFullEnd m mMax vCap eCap len x heapStep < 2 ^ w :=
      lt_of_le_of_lt (dsStepPosFullEnd_le_add_space hState) hsp'
    have hAff_lt : dsStepPosFullAffEnd m vCap eCap len heapStep < 2 ^ w :=
      lt_of_le_of_lt (dsStepPosFullAffEnd_le_add_space m mMax vCap eCap len heapStep) hsp'
    have hgen' : mem0 (b + dsGenOff) + m.j + 4 + m.G'.m < 2 ^ w := by
      have h1 : mem0 (b + dsGenOff) + (m.j + 4 + m.G'.m) < 2 ^ w := by
        simpa [dsStepGenAt, hu_some, hjne, m, StepPosModel.j, StepPosModel.G', StepPosModel.st] using hgen_w
      omega
    refine runs_seq_call_le (vs := [b, m.j, updPtr, heapStep, len])
      (dsStepPosFull_meetsContract_ext m mMax w vCap eCap b len x hps.hpPos)
      (by simp [evalArgs, Expr.eval, startState, m, StepPosModel.j])
      (fun z hz => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl
        · omega
        · exact lt_of_le_of_lt hjL hL_w
        · omega
        · omega
        · omega)
      ⟨updPtr, heapStep, rfl, hw16, hL1, hq1, hVG₀, hGm₀, hE₀_cap, hBV, hds, hu_some, hjpos,
        hPref, hRev, hState, hfix, hfoot_lt, hz0, hEnd_lt, hAff_lt, hgen', hk_w, hfixU, hupd_le,
        hupd_foot, hupd_w, hupd_at, hupd_cap⟩ ?_
    rintro ret memFinal _ ⟨⟨_, _, hEq, hPost, hret_end, hgenF⟩, huhW⟩
    simp only [List.cons.injEq, and_true] at hEq
    rcases hEq with ⟨_, _, rfl, rfl, _⟩
    have hge7 : heapStep + 7 ≤ ret := by
      rcases hPost with ⟨_, _, _, _, rfl, hSO, _⟩
      rcases hSO with ⟨_, _, _, _, _, _, _, _, _, _, _, h1, h2, h3, _⟩; omega
    have hret_sp : ret ≤ heapStep + dsStepSpaceAt G₀ impl mMax L q vCap eCap us k len := by
      simp only [dsStepSpaceAt, hu_some, hjne, ↓reduceIte]
      exact le_trans hret_end (dsStepPosFullEnd_le_add_space hState)
    have hgen_sp : memFinal (b + dsGenOff) ≤ mem0 (b + dsGenOff) + dsStepGenAt G₀ impl L q us k := by
      dsimp only [startState] at hgenF
      simp only [dsStepGenAt, hu_some, hjne, ↓reduceIte]
      dsimp only [m, StepPosModel.j, StepPosModel.G', StepPosModel.st] at hgenF
      clear * - hgenF; omega
    refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by simp))
      ⟨updPtr, heapStep, rfl, hPost, hge7, hret_sp, hgen_sp, huhW updPtr heapStep rfl⟩ ?_
    have hcm := dsStepPosFullCost_le_model (m := m) (mMax := mMax) (vCap := vCap) (eCap := eCap)
      (len := len) hState hRev hu_val hupd_cap
    dsimp only [m] at hcm
    dsimp only [Expr.size, argsSize, dsStepContract, dsStepPosFullContract, chooseLevelContract]
    simp only [dsStepCostAt, hu_some, hjne, ↓reduceIte, m]
    clear * - hcm; omega
  · have hsp2 : heapStep + (dsStepZeroSpace impl mMax vCap eCap (st.G.applyUpdate u) st.H
        (initCore (st.G.applyUpdate u) (canonicalSparsify impl)).1 len + 2) < 2 ^ w := by
      simpa [dsStepSpaceAt, hj0, hu_some, st] using hsp
    have hsp' : heapStep + dsStepZeroSpace impl mMax vCap eCap (st.G.applyUpdate u) st.H
        (initCore (st.G.applyUpdate u) (canonicalSparsify impl)).1 len < 2 ^ w := by omega
    have hgen' : mem0 (b + dsGenOff) + 2 + (st.G.applyUpdate u).m < 2 ^ w := by
      have h1 : mem0 (b + dsGenOff) + (2 + (st.G.applyUpdate u).m) < 2 ^ w := by
        simpa [dsStepGenAt, hj0, hu_some, st] using hgen_w
      omega
    have hwok' : (st.G.applyUpdate u).E.Nonempty →
        wordSize impl.cw (canonSparsifyInput (activeSubgraph (st.G.applyUpdate u))
          (activeSubgraph (st.G.applyUpdate u)) idEmb) ≤ w := by
      simp only [dsStepWordOKAt, hu_some, hj0] at hWOK
      exact hWOK trivial
    refine runs_seq_call_le (vs := [b, updPtr, heapStep])
      (dsStepZero_meetsContract hps.hpSZ)
      (by simp [evalArgs, Expr.eval, startState])
      (fun z hz => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl <;> omega)
      ⟨updPtr, heapStep, rfl, hw16, hL1, hq1, hVG₀, hGm₀, hBV, hds, hu_some, hj0, hPref,
        hState, hfix, hfoot_lt, hz0, hsp', hgen', hk_w, hwok', hupd_le, hupd_foot, hupd_w,
        hupd_at, hupd_cap⟩ ?_
    rintro ret0 memPre _ ⟨_, _, hEq, hPost, hge5, hleSp, hgenF, huhW⟩
    simp only [List.cons.injEq, and_true] at hEq
    rcases hEq with ⟨_, rfl, rfl⟩
    have ⟨_, _, _, _, _, x', _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hS', _⟩ := hPost
    have hmemV : memPre (b + dsVCapOff) = vCap := hS'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hmemE : memPre (b + dsECapOff) = eCap := hS'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hG' : DynGraphAt memPre (dsGPtr b) vCap eCap (step st u (canonicalSparsify impl)).state.G :=
      hS'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hgm : memPre (dsGPtr b + dgMOff) = (step st u (canonicalSparsify impl)).state.G.m :=
      hG'.2.2.2.2.2.2.1
    obtain ⟨eL, heL_len, heL_nd, heL_mem, heL_at, _⟩ := hG'.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hG_top : dsGPtr b + dynGraphSize vCap eCap ≤ b + dsFixedSize L vCap eCap := by
      have hcb := collectD_lt_eStamp_bounds b L vCap eCap
      have h1 := hcb.2.2.1
      have h2 := hcb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have h3 := hcb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      clear hcb; omega
    have hdg_eq : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
    have heL_base_eq : ((dsGPtr b + 4) + 7 * vCap) + eCap = dgEListBase (dsGPtr b) vCap eCap := by
      simp [dgEListBase]
    have heL_cap : eL.length ≤ eCap := by
      rw [← List.toFinset_card_of_nodup heL_nd]
      have hsub : eL.toFinset ⊆ Finset.range eCap := fun e he =>
        Finset.mem_range.mpr (hG'.2.2.1 e ((heL_mem e).mp (List.mem_toFinset.mp he)))
      exact le_trans (Finset.card_le_card hsub) (by simp)
    have hret2_lt : ret0 + 2 < 2 ^ w := by
      dsimp only [st] at hsp2; clear * - hleSp hsp2; omega
    have hret1_lt : ret0 + 1 < 2 ^ w := by omega
    have hbV_lt : b + dsVCapOff < 2 ^ w := lt_trans (hltF.1 dsVCapOff (by decide)).2 hfix_w
    have hbE_lt : b + dsECapOff < 2 ^ w := lt_trans (hltF.1 dsECapOff (by decide)).2 hfix_w
    have hbH_lt : b + dsHdrSize < 2 ^ w := by dsimp only [dsGPtr] at hG_top; omega
    have hg4_lt : dsGPtr b + 4 < 2 ^ w := by omega
    have h7v_lt : 7 * vCap < 2 ^ w := by omega
    have hg47_lt : (dsGPtr b + 4) + 7 * vCap < 2 ^ w := by omega
    have hgEL_lt : ((dsGPtr b + 4) + 7 * vCap) + eCap < 2 ^ w := by omega
    have hgm_lt : dsGPtr b + dgMOff < 2 ^ w := by simp only [dgMOff]; omega
    refine runs_seq_assign_le (v := vCap)
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
        (Expr.eval_const (by dsimp only [dsVCapOff]; omega)) hbV_lt) hmemV) ?_
    refine runs_seq_assign_le (v := eCap)
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
        (Expr.eval_const (by dsimp only [dsECapOff]; omega)) hbE_lt) hmemE) ?_
    refine runs_seq_assign_le (v := dsGPtr b)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
        (Expr.eval_const (by dsimp only [dsHdrSize]; omega)) hbH_lt) ?_
    refine runs_seq_assign_le (v := dgEListBase (dsGPtr b) vCap eCap)
      (heL_base_eq ▸ Expr.eval_add
        (Expr.eval_add
          (Expr.eval_add (Expr.eval_reg_of_eq (v := dsGPtr b) (by simp))
            (Expr.eval_const (by omega)) hg4_lt)
          (Expr.eval_mul (Expr.eval_const (by omega))
            (Expr.eval_reg_of_eq (v := vCap) (by simp)) h7v_lt)
          hg47_lt)
        (Expr.eval_reg_of_eq (v := eCap) (by simp)) hgEL_lt) ?_
    refine runs_seq_assign_le (v := eL.length)
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := dsGPtr b) (by simp))
        (Expr.eval_const (by dsimp only [dgMOff]; omega)) hgm_lt) (hgm.trans heL_len.symm)) ?_
    refine runs_seq_store_le (x := ret0) (v := dgEListBase (dsGPtr b) vCap eCap)
      (Expr.eval_reg_of_eq (v := ret0) (by simp))
      (Expr.eval_reg_of_eq (v := dgEListBase (dsGPtr b) vCap eCap) (by simp)) ?_
    refine runs_seq_store_le (x := ret0 + 1) (v := eL.length)
      (Expr.eval_add (Expr.eval_reg_of_eq (v := ret0) (by simp))
        (Expr.eval_const (by omega)) hret1_lt)
      (Expr.eval_reg_of_eq (v := eL.length) (by simp)) ?_
    let memFinal := Function.update
      (Function.update memPre ret0 (dgEListBase (dsGPtr b) vCap eCap)) (ret0 + 1) eL.length
    have hcl : chooseLevel L st.q (st.t + 1) = 0 := by
      rw [(hPref k le_rfl).q_eq, (hPref k le_rfl).t_eq]; exact hj0
    have hresG : (step st u (canonicalSparsify impl)).state.G = st.G.applyUpdate u := by
      simp [step, hcl, initAt, initCore]
    have heL_fin : eL.toFinset = stepReembSet st u := by
      rw [stepReembSet_eq_zero st u hcl]
      ext e
      rw [List.mem_toFinset, heL_mem, hresG]
    have hR_le : dgEListBase (dsGPtr b) vCap eCap + eL.length ≤ b + dsFixedSize L vCap eCap := by
      rw [← heL_base_eq]; omega
    have hReembPost : StepReembOutPost G₀ L q vCap eCap b k impl us u mem0 x heapStep
        memFinal (ret0 + 2) :=
      ⟨memPre, ret0, dgEListBase (dsGPtr b) vCap eCap, eL, rfl, hPost, rfl, heL_nd, heL_fin,
        Or.inl hR_le, heL_at⟩
    have hgenF' : memFinal (b + dsGenOff) ≤ mem0 (b + dsGenOff) + dsStepGenAt G₀ impl L q us k := by
      have hne0 : b + dsGenOff ≠ ret0 := by
        have := (hltF.1 dsGenOff (by decide)).2; omega
      have hne1 : b + dsGenOff ≠ ret0 + 1 := by
        have := (hltF.1 dsGenOff (by decide)).2; omega
      simp only [memFinal, Function.update_of_ne hne1, Function.update_of_ne hne0]
      dsimp only [startState, st] at hgenF
      have : memPre (b + dsGenOff) ≤ mem0 (b + dsGenOff) + (2 + (st.G.applyUpdate u).m) := by
        dsimp only [st]; clear * - hgenF; omega
      simpa [dsStepGenAt, hj0, hu_some, st] using this
    have huhW' : memFinal (heapStep + 2) ≤ len + 4 * (step st u (canonicalSparsify impl)).UH.length := by
      have hne0 : heapStep + 2 ≠ ret0 := by omega
      have hne1 : heapStep + 2 ≠ ret0 + 1 := by omega
      simp only [memFinal, Function.update_of_ne hne1, Function.update_of_ne hne0]
      exact huhW
    refine runs_ret_le (v := ret0 + 2)
      (Expr.eval_add (Expr.eval_reg_of_eq (v := ret0) (by simp))
        (Expr.eval_const (by omega)) hret2_lt)
      ⟨updPtr, heapStep, rfl, hReembPost, by dsimp only [Outcome.value]; omega,
        by dsimp only [Outcome.value]; simp only [dsStepSpaceAt, hj0, hu_some, ↓reduceIte]; omega,
        hgenF', huhW'⟩ ?_
    dsimp only [Expr.size, argsSize, dsStepContract, dsStepZeroContract, chooseLevelContract]
    simp only [dsStepCostAt, hu_some, hj0, ↓reduceIte]
    clear * - ; omega

end

end MinCostFlow.DynSpanner.Program
