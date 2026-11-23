module

public import MinCostFlow.LSF.Program.FForestMath
public import MinCostFlow.LSF.Program.FAncFill

/-!
# The blocks of `F` match the model

`fGraphProc` and `fAncFillProc` write their outputs from index arrays. This file shows that,
when the index arrays come from the roots pass for a root set `R` (`RootPassIdx`), the outputs are
the blocks of `LSFRep` for `F = forestGivenRoots T₀ r₀ R π`:

* `fGraph_bridge`: the dynamic graph is `F` (`DynGraphAt`);
* `fAnc_bridge`: the root and component block is `FAncAt` for the rooted forest `(F, R)`. The
  component of a vertex is named by its root (`compId v = vL (rt (idxOf v))`, `compRoot c = c`),
  and every root names a component.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

variable {T₀ : MGraph} {vList : List ℕ} {tM r : ℕ} {fid tl hd par pe dep : ℕ → ℕ}
  {R : Finset ℕ} {π inR piv mp own rt : ℕ → ℕ}

/-- The dynamic graph built by `fGraphProc` is `F`. -/
theorem fGraph_bridge (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep)
    (h : RootPassIdx T₀ vList tM r fid par pe R π inR piv mp own rt)
    {mem : ℕ → ℕ} {dgPtr vCap eCap : ℕ} {V : Finset ℕ} {fe tE hE own' : ℕ → ℕ}
    (hV : V = T₀.V) (hfe : ∀ i < tM, fe i = fid i ∧ fid i < eCap)
    (hends : ∀ i < tM, tE i = vList.getD (tl i) 0 ∧ hE i = vList.getD (hd i) 0)
    (hown : ∀ i < tM, own' i = own i)
    (hdg : DynGraphAt mem dgPtr vCap eCap (fGraph V eCap fe tE hE own' tM)) :
    DynGraphAt mem dgPtr vCap eCap (forestGivenRoots T₀ (vList.getD r 0) R π) := by
  classical
  obtain ⟨hEq, hEnds⟩ := fGraph_spec (V := V) (eCap := eCap) (fe := fe) (tE := tE) (hE := hE)
    (own := own') tM
    (fun i hi => by rw [(hfe i hi).1]; exact (hfe i hi).2)
    (fun i hi j hj he => hI.hA.fid_inj i hi j hj (by rw [← (hfe i hi).1, ← (hfe j hj).1]; exact he))
  have hEf : (fGraph V eCap fe tE hE own' tM).E = (forestGivenRoots T₀ (vList.getD r 0) R π).E := by
    rw [hEq, forest_E_eq hI h]
    ext f
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨i, ⟨hi, ho⟩, rfl⟩
      exact ⟨i, ⟨hi, by rw [← hown i hi]; exact ho⟩, (hfe i hi).1.symm⟩
    · rintro ⟨i, ⟨hi, ho⟩, rfl⟩
      exact ⟨i, ⟨hi, by rw [hown i hi]; exact ho⟩, (hfe i hi).1⟩
  refine DynGraphAt.congr_ends ?_ hEf ?_ hdg
  · rw [fGraph_V, hV]; rfl
  · intro e he
    rw [hEq] at he
    obtain ⟨i, hi', rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hi, ho⟩ := Finset.mem_filter.mp hi'
    rw [Finset.mem_range] at hi
    rw [(hEnds i hi ho).1, (hEnds i hi ho).2, (hfe i hi).1]
    exact ⟨by rw [(hends i hi).1]; exact (hI.hA.tail_eq i hi).symm,
      by rw [(hends i hi).2]; exact (hI.hA.head_eq i hi).symm⟩

/-- The block written by `fAncFillProc` is `FAncAt` for `(F, R)`. -/
theorem fAnc_bridge (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep)
    (h : RootPassIdx T₀ vList tM r fid par pe R π inR piv mp own rt) {RF : RootedForest}
    (hRF : RF.F = forestGivenRoots T₀ (vList.getD r 0) R π) (hRR : RF.R = R)
    {mem' : ℕ → ℕ} {fAncPtr vCap : ℕ} {vL inR' rt' : ℕ → ℕ}
    (hvL : ∀ x < vList.length, vL x = vList.getD x 0 ∧ vL x < vCap)
    (hinR' : ∀ x < vList.length, inR' x = inR x) (hrt' : ∀ x < vList.length, rt' x = rt x)
    (hnv : vList.length ≤ vCap)
    (h0 : mem' (fAncPtr + fOffRCount) = (rootList vL inR' vList.length).length)
    (h1 : mem' (fAncPtr + fOffIsRootPtr) = fIsRootBase fAncPtr)
    (h2 : mem' (fAncPtr + fOffRListPtr) = fRListBase fAncPtr vCap)
    (h3 : mem' (fAncPtr + fOffCompIdPtr) = fCompIdBase fAncPtr vCap)
    (h4 : mem' (fAncPtr + fOffCompRootPtr) = fCompRootBase fAncPtr vCap)
    (h5 : mem' (fAncPtr + fOffCompSizePtr) = fCompSizeBase fAncPtr vCap)
    (hIs : ∀ v < vCap, mem' (fIsRootBase fAncPtr + v) = isRootVal vL inR' vList.length v)
    (hRL : ListAt mem' (fRListBase fAncPtr vCap) (rootList vL inR' vList.length))
    (hCI : ∀ x < vList.length, mem' (fCompIdBase fAncPtr vCap + vL x) = vL (rt' x))
    (hCR : ∀ x < vList.length, inR' x = 1 → mem' (fCompRootBase fAncPtr vCap + vL x) = vL x)
    (hCS : ∀ v < vCap, mem' (fCompSizeBase fAncPtr vCap + v) = sizeVal vL rt' vList.length v) :
    FAncAt mem' fAncPtr vCap RF (rootList vL inR' vList.length)
      (fun v => vL (rt' (vList.idxOf v))) (fun c => c) (sizeVal vL rt' vList.length) RF.R := by
  classical
  set n := vList.length with hn
  have hB := rt_bridge hI h.hS h.hmp h.hown h.hrt_r h.hrule
  have hRV : R ⊆ T₀.V := h.hS.hR.1
  have hidx : ∀ v ∈ T₀.V, vList.idxOf v < n ∧ vList.getD (vList.idxOf v) 0 = v := fun v hv =>
    ⟨List.idxOf_lt_length_of_mem ((hI.hV v).mp hv), getD_idxOf ((hI.hV v).mp hv)⟩
  -- the root list
  have hmemR : ∀ v, v ∈ rootList vL inR' n ↔ v ∈ R := by
    intro v
    simp only [rootList, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨x, ⟨hx, hx1⟩, rfl⟩
      rw [(hvL x hx).1]
      exact (h.hS.hinR x hx).mp (by rw [← hinR' x hx]; exact hx1)
    · intro hv
      obtain ⟨hxl, hgx⟩ := hidx v (hRV hv)
      refine ⟨_, ⟨hxl, ?_⟩, by rw [(hvL _ hxl).1, hgx]⟩
      rw [hinR' _ hxl]
      exact (h.hS.hinR _ hxl).mpr (by rw [hgx]; exact hv)
  have hnd : (rootList vL inR' n).Nodup := by
    refine (List.nodup_range.filter _).map_on fun x hx y hy he => ?_
    simp only [List.mem_filter, List.mem_range] at hx hy
    rw [(hvL x hx.1).1, (hvL y hy.1).1] at he
    exact hI.getD_inj hx.1 hy.1 he
  have hcard : (rootList vL inR' n).length = R.card := by
    rw [← List.toFinset_card_of_nodup hnd]
    congr 1
    ext v
    rw [List.mem_toFinset, hmemR]
  have hlen : (rootList vL inR' n).length ≤ n := rootList_length_le _ _ _
  -- the facts about one root
  have hroot : ∀ c ∈ R, vList.idxOf c < n ∧ vList.getD (vList.idxOf c) 0 = c ∧
      vL (vList.idxOf c) = c ∧ inR' (vList.idxOf c) = 1 ∧ rt (vList.idxOf c) = vList.idxOf c := by
    intro c hc
    obtain ⟨hxl, hgx⟩ := hidx c (hRV hc)
    have h1 : inR (vList.idxOf c) = 1 := (h.hS.hinR _ hxl).mpr (by rw [hgx]; exact hc)
    refine ⟨hxl, hgx, by rw [(hvL _ hxl).1, hgx], by rw [hinR' _ hxl]; exact h1, ?_⟩
    by_cases hxr : vList.idxOf c = r
    · rw [hxr]; exact h.hrt_r
    · rw [h.hrule _ hxl hxr, if_pos h1]
  have hsz : ∀ c ∈ R, sizeVal vL rt' n c =
      ((Finset.range n).filter (fun x => rt x = vList.idxOf c)).card := by
    intro c hc
    obtain ⟨hxl, hgx, -, -, -⟩ := hroot c hc
    unfold sizeVal
    congr 1
    refine Finset.filter_congr fun x hx => ?_
    rw [Finset.mem_range] at hx
    have hrl := (hB x hx).1
    rw [hrt' x hx, (hvL _ hrl).1]
    constructor
    · intro he; exact hI.getD_inj hrl hxl (he.trans hgx.symm)
    · intro he; rw [he, hgx]
  refine ⟨by rw [h0, hcard, hRR], h1, h2, h3, h4, h5, fun v hv => ?_, by rw [hcard, hRR],
    hnd, fun v => by rw [hmemR, hRR], hlen.trans hnv, hRL, fun v hv => ?_, subset_rfl,
    fun c hc => ?_, fun v hv => ?_⟩
  · rw [hRF] at hv
    obtain ⟨hxl, hgx⟩ := hidx v hv
    rw [← hgx, ← (hvL _ hxl).1]
    exact (hvL _ hxl).2
  · rw [hIs v hv, hRR]
    unfold isRootVal
    refine if_congr ?_ rfl rfl
    rw [← hmemR]
    simp only [rootList, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨x, hx, hx1, rfl⟩; exact ⟨x, ⟨hx, hx1⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hx1⟩, rfl⟩; exact ⟨x, hx, hx1, rfl⟩
  · rw [hRR] at hc
    obtain ⟨hxl, hgx, hvx, hix, hrx⟩ := hroot c hc
    have hcv : c < vCap := by rw [← hvx]; exact (hvL _ hxl).2
    refine ⟨hcv, by rw [← hvx, hCR _ hxl hix], by rw [hRR]; exact hc, ?_, hCS c hcv, ?_, ?_⟩
    · show vL (rt' (vList.idxOf c)) = c
      rw [hrt' _ hxl, hrx, hvx]
    · rw [hsz c hc]
      exact Finset.card_pos.mpr ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hxl, hrx⟩⟩
    · rw [hsz c hc, hRF]
      have := compCard_eq hI h hxl (by rw [hgx]; exact hc)
      rw [hgx] at this
      exact this.symm
  · rw [hRF] at hv
    obtain ⟨hxl, hgx⟩ := hidx v hv
    have hvx : vL (vList.idxOf v) = v := by rw [(hvL _ hxl).1, hgx]
    obtain ⟨hrl, hrR, hconn⟩ := hB _ hxl
    have hc : mem' (fCompIdBase fAncPtr vCap + v) = vList.getD (rt (vList.idxOf v)) 0 := by
      have := hCI _ hxl
      rw [hvx, hrt' _ hxl, (hvL _ hrl).1] at this
      exact this
    refine ⟨?_, ?_, ?_⟩
    · show mem' (fCompIdBase fAncPtr vCap + v) = vL (rt' (vList.idxOf v))
      rw [hc, hrt' _ hxl, (hvL _ hrl).1]
    · rw [hc, hRR]; exact hrR
    · show RF.F.Connected v (mem' (fCompIdBase fAncPtr vCap + v))
      rw [hc, hRF]
      rw [hgx] at hconn
      exact hconn

end MinCostFlow.LSF.Program

end
