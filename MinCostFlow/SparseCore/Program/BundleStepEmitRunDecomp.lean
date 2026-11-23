module

public import MinCostFlow.SparseCore.Program.BundleStepEmitCandRuns
public import MinCostFlow.SparseCore.Program.BundleStepScanBridge

/-!
# Pure two-branch run-decomposition lemmas (`BundleStepEmitRunDecomp`)

Defines `scanVRuns` (all runs of `rawByRootVRuns` with root `≠ w_rem`) and proves the pure
run-decomposition lemmas connecting `ScanValidForSlot`, `scanVRuns`, `rawByRootVRuns`,
`promoteLargestRun`, and `byRootVRuns`:
* `rawByRootVRuns_info`, `rawByRootVRuns_pairwise`, `scanVRuns_pairwise`,
* `scanVRuns_pack_eq_sort`: sorted scanned packed keys for candidate `b` equal `vRunsPacked` of
  `scanVRuns`,
* `byRootVRuns_branch1_eq`: when `winLen < keptLen`, `byRootVRuns = (w_rem, keptXs) :: scanVRuns`,
* `byRootVRuns_branch2_eq`: when `keptLen ≤ winLen`, `degB ≤ 2 * m_b`,
  `byRootVRuns = raw[bestIdx] :: (raw.take bestIdx ++ raw.drop (bestIdx + 1))`, and
  `vRunsEndsLen (raw.take bestIdx) + vRunsEndsLen (raw.drop (bestIdx + 1)) ≤ m_b`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner
open MinCostFlow.DynSpanner.Program

@[expose] public section

/-- Non-remainder runs of candidate `b` (all runs of `rawByRootVRuns` with root `≠ w_rem`). -/
noncomputable def scanVRuns (B : BundleState) (src' : End → ℕ) (b w_rem : ℕ) :
    List (ℕ × List End) :=
  (rawByRootVRuns B B.edges src' b).filter fun vr => vr.1 != w_rem

end

public section

lemma vRunsEndsLen_append (a b : List (ℕ × List End)) :
    vRunsEndsLen (a ++ b) = vRunsEndsLen a + vRunsEndsLen b := by
  simp [vRunsEndsLen]

lemma rawByRootVRuns_info {B : BundleState} {src' : End → ℕ} {b : ℕ} :
    ∀ vr ∈ rawByRootVRuns B B.edges src' b,
      0 < vr.2.length ∧ vr.2.Nodup ∧ (∀ x ∈ vr.2, x ∈ B.ends b ∧ src' x = vr.1) := by
  have hsurv : survivingEnds B B.edges b = B.ends b := by
    ext x; simp only [survivingEnds, Finset.mem_filter, BundleState.mem_ends]
    exact ⟨fun h => h.1, fun h => ⟨h, h.1⟩⟩
  intro vr hvr
  simp only [rawByRootVRuns, List.mem_map, Finset.mem_sort, finalRootsOf, hsurv, Finset.mem_image] at hvr
  rcases hvr with ⟨v, ⟨x₀, hx₀, rfl⟩, rfl⟩
  have hmem_xs : ∀ x, x ∈ ((((B.ends b).filter fun x => src' x = src' x₀).image endKey).sort (· ≤ ·)).map endOfKey ↔
      x ∈ B.ends b ∧ src' x = src' x₀ := fun x => by
    simp only [List.mem_map, Finset.mem_sort, Finset.mem_image, Finset.mem_filter]
    exact ⟨fun ⟨k, ⟨y, hy, heq⟩, hxy⟩ => by subst heq; rw [bundle_endOfKey_endKey] at hxy; rwa [← hxy],
      fun hx => ⟨endKey x, ⟨x, hx, rfl⟩, bundle_endOfKey_endKey x⟩⟩
  refine ⟨List.length_pos_iff_exists_mem.mpr ⟨x₀, (hmem_xs x₀).mpr ⟨hx₀, rfl⟩⟩,
    (Finset.sort_nodup _ _).map_on fun k₁ _ k₂ _ heq => by
      have := congrArg endKey heq; rwa [bundle_endKey_endOfKey, bundle_endKey_endOfKey] at this,
    fun x hx => (hmem_xs x).mp hx⟩

lemma rawByRootVRuns_pairwise {B : BundleState} {src' : End → ℕ} {b : ℕ} :
    ((rawByRootVRuns B B.edges src' b).map Prod.fst).Pairwise (· < ·) := by
  simp only [rawByRootVRuns, List.map_map, Function.comp_def, List.map_id']
  exact ((Finset.pairwise_sort _ _).and (Finset.sort_nodup _ _)).imp fun ⟨h1, h2⟩ => lt_of_le_of_ne h1 h2

lemma scanVRuns_pairwise {B : BundleState} {src' : End → ℕ} {b w_rem : ℕ} :
    ((scanVRuns B src' b w_rem).map Prod.fst).Pairwise (· < ·) :=
  rawByRootVRuns_pairwise.sublist (List.filter_sublist.map Prod.fst)

lemma scanVRuns_pack_eq_sort {eCap : ℕ} {B : BundleState} {src' : End → ℕ}
    {candSet_j : Finset ℕ} {scan_j : List (ℕ × ℕ × ℕ)} {b w_rem : ℕ}
    (hE_lt : ∀ e ∈ B.edges, e < eCap)
    (hval : ScanValidForSlot B src' candSet_j scan_j)
    (hrem_ne : ∀ t ∈ scan_j, t.1 = b → t.2.1 ≠ w_rem)
    (hrem_eq : ∀ x ∈ B.ends b, endKey x ∉ scan_j.map (fun t => t.2.2) → src' x = w_rem) :
    let L_b := scan_j.filter fun t => t.1 == b
    vRunsPacked eCap (scanVRuns B src' b w_rem) =
      (L_b.map fun t => packEndKey eCap t.2.1 t.2.2).toFinset.sort (· ≤ ·) ∧
    vRunsEndsLen (scanVRuns B src' b w_rem) = L_b.length := by
  intro L_b
  set sr := scanVRuns B src' b w_rem
  have hsurv : survivingEnds B B.edges b = B.ends b := by
    ext x; simp only [survivingEnds, Finset.mem_filter, BundleState.mem_ends]
    exact ⟨fun h => h.1, fun h => ⟨h, h.1⟩⟩
  have hk_lt : ∀ x ∈ B.ends b, endKey x < 2 * eCap := fun x hx => by
    have he := hE_lt x.1 ((BundleState.mem_ends B b x).mp hx).1
    rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
  have hraw_pw : (vRunsPacked eCap (rawByRootVRuns B B.edges src' b)).Pairwise (· < ·) := by
    have hsort := rawByRootVRuns_pack_eq_sort (eCap := eCap) (B := B) (E := B.edges) (src' := src') (b := b) hE_lt
    change vRunsPacked eCap (rawByRootVRuns B B.edges src' b) = _ at hsort
    rw [hsort]
    exact ((Finset.pairwise_sort _ _).and (Finset.sort_nodup _ _)).imp fun ⟨h1, h2⟩ => lt_of_le_of_ne h1 h2
  have hsub_pk : (vRunsPacked eCap sr).Sublist (vRunsPacked eCap (rawByRootVRuns B B.edges src' b)) := by
    have hgo : ∀ {l₁ l₂ : List (ℕ × List End)}, l₁.Sublist l₂ →
        (vRunsPacked eCap l₁).Sublist (vRunsPacked eCap l₂) := by
      intro l₁ l₂ h
      induction h with
      | slnil => exact List.Sublist.slnil
      | cons a _ ih => exact ih.trans (List.sublist_append_right _ _)
      | cons_cons a _ ih => exact (List.Sublist.refl _).append ih
    exact hgo List.filter_sublist
  have hsr_pw : (vRunsPacked eCap sr).Pairwise (· < ·) := hraw_pw.sublist hsub_pk
  have hsr_nd : (vRunsPacked eCap sr).Nodup := hsr_pw.imp ne_of_lt
  have hsr_le : (vRunsPacked eCap sr).Pairwise (· ≤ ·) := hsr_pw.imp le_of_lt
  have hLb_pk_nd : (L_b.map fun t => packEndKey eCap t.2.1 t.2.2).Nodup := by
    have hLb_k_nd : (L_b.map fun t => t.2.2).Nodup := hval.1.sublist (List.filter_sublist.map _)
    have hLb_lt : ∀ t ∈ L_b, t.2.2 < 2 * eCap := fun t ht => by
      obtain ⟨ht_in, htb⟩ := List.mem_filter.mp ht
      have htb' : t.1 = b := by simpa using htb
      have := hk_lt _ (htb' ▸ (hval.2.1 t ht_in).2.1); rwa [bundle_endKey_endOfKey] at this
    have hgo : ∀ l : List (ℕ × ℕ × ℕ), (l.map fun t => t.2.2).Nodup →
        (∀ t ∈ l, t.2.2 < 2 * eCap) → (l.map fun t => packEndKey eCap t.2.1 t.2.2).Nodup := by
      intro l; induction l with
      | nil => intro _ _; exact List.nodup_nil
      | cons a tl ih =>
        intro hnd hlt
        obtain ⟨ha_not, htl_nd⟩ := List.nodup_cons.mp hnd
        rw [List.map_cons, List.nodup_cons]
        refine ⟨fun hm => ?_, ih htl_nd fun t ht => hlt t (List.mem_cons_of_mem _ ht)⟩
        obtain ⟨t, ht, heq⟩ := List.mem_map.mp hm
        have hkeq := (packEndKey_inj (hlt t (List.mem_cons_of_mem _ ht)) (hlt a List.mem_cons_self) heq).2
        exact ha_not (List.mem_map.mpr ⟨t, ht, hkeq⟩)
    exact hgo L_b hLb_k_nd hLb_lt
  have hperm : (vRunsPacked eCap sr).Perm ((L_b.map fun t => packEndKey eCap t.2.1 t.2.2).toFinset.sort (· ≤ ·)) := by
    rw [List.perm_ext_iff_of_nodup hsr_nd (Finset.sort_nodup _ _)]
    intro pk
    simp only [Finset.mem_sort, List.mem_toFinset, List.mem_map, vRunsPacked, List.mem_flatMap]
    constructor
    · rintro ⟨vr, hvr_sr, x, hx_vr, rfl⟩
      obtain ⟨hvr_raw, hne_w⟩ := List.mem_filter.mp hvr_sr
      have hne_w' : vr.1 ≠ w_rem := by simpa using hne_w
      obtain ⟨hxB, hxsrc⟩ := (rawByRootVRuns_info vr hvr_raw).2.2 x hx_vr
      have hkin : endKey x ∈ scan_j.map (fun t => t.2.2) := by
        by_contra hnot; exact hne_w' (hxsrc.symm.trans (hrem_eq x hxB hnot))
      obtain ⟨t, ht_in, htk⟩ := List.mem_map.mp hkin
      have htB := (hval.2.1 t ht_in).2.1
      have htsrc := (hval.2.1 t ht_in).2.2
      rw [htk, bundle_endOfKey_endKey] at htB htsrc
      have htb : t.1 = b :=
        ((BundleState.mem_ends B t.1 x).mp htB).2.symm.trans ((BundleState.mem_ends B b x).mp hxB).2
      refine ⟨t, List.mem_filter.mpr ⟨ht_in, by simp [htb]⟩, ?_⟩
      rw [htk, ← htsrc, hxsrc]
    · rintro ⟨t, ht_f, rfl⟩
      obtain ⟨ht_in, htb⟩ := List.mem_filter.mp ht_f
      have htb' : t.1 = b := by simpa using htb
      have htB : endOfKey t.2.2 ∈ B.ends b := htb' ▸ (hval.2.1 t ht_in).2.1
      have htsrc : src' (endOfKey t.2.2) = t.2.1 := (hval.2.1 t ht_in).2.2
      have hne_w : t.2.1 ≠ w_rem := hrem_ne t ht_in htb'
      refine ⟨(t.2.1, ((((survivingEnds B B.edges b).filter fun x => src' x = t.2.1).image endKey).sort (· ≤ ·)).map endOfKey),
        ?_, endOfKey t.2.2, ?_, by rw [bundle_endKey_endOfKey]⟩
      · refine List.mem_filter.mpr ⟨?_, by simp [hne_w]⟩
        simp only [rawByRootVRuns, List.mem_map, Finset.mem_sort, finalRootsOf, hsurv, Finset.mem_image]
        exact ⟨t.2.1, ⟨endOfKey t.2.2, htB, htsrc⟩, rfl⟩
      · simp only [List.mem_map, Finset.mem_sort, Finset.mem_image, Finset.mem_filter, hsurv]
        exact ⟨t.2.2, ⟨endOfKey t.2.2, ⟨htB, htsrc⟩, bundle_endKey_endOfKey _⟩, rfl⟩
  have heq := hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => le_antisymm h1 h2) hsr_le (Finset.pairwise_sort _ _)
  have hlen : vRunsEndsLen sr = L_b.length := by
    rw [← vRunsPacked_length eCap, heq, Finset.length_sort, List.toFinset_card_of_nodup hLb_pk_nd, List.length_map]
  exact ⟨heq, hlen⟩

lemma byRootVRuns_branch1_eq {eCap : ℕ} {B : BundleState} {src' : End → ℕ}
    {candSet_j : Finset ℕ} {scan_j : List (ℕ × ℕ × ℕ)} {b w_rem : ℕ}
    (hE_lt : ∀ e ∈ B.edges, e < eCap)
    (hval : ScanValidForSlot B src' candSet_j scan_j)
    (hrem_ne : ∀ t ∈ scan_j, t.1 = b → t.2.1 ≠ w_rem)
    (hrem_eq : ∀ x ∈ B.ends b, endKey x ∉ scan_j.map (fun t => t.2.2) → src' x = w_rem)
    (hwin_lt : ∀ vr ∈ scanVRuns B src' b w_rem,
      vr.2.length < (B.ends b).card - (scan_j.filter fun t => t.1 == b).length)
    (hkept_pos : 0 < (B.ends b).card - (scan_j.filter fun t => t.1 == b).length) :
    ∃ keptXs : List End,
      0 < keptXs.length ∧
      (∀ x ∈ keptXs, x ∈ B.ends b ∧ src' x = w_rem) ∧
      byRootVRuns B B.edges src' b = (w_rem, keptXs) :: scanVRuns B src' b w_rem := by
  set raw := rawByRootVRuns B B.edges src' b
  set sr := scanVRuns B src' b w_rem
  set L_b := scan_j.filter fun t => t.1 == b
  have hsr_len : vRunsEndsLen sr = L_b.length :=
    (scanVRuns_pack_eq_sort hE_lt hval hrem_ne hrem_eq).2
  have hraw_len : vRunsEndsLen raw = (B.ends b).card := by
    have hsort := rawByRootVRuns_pack_eq_sort (eCap := eCap) (B := B) (E := B.edges) (src' := src') (b := b) hE_lt
    change vRunsPacked eCap raw = _ at hsort
    rw [← vRunsPacked_length eCap, hsort, Finset.length_sort]
    have hsurv : survivingEnds B B.edges b = B.ends b := by
      ext x; simp only [survivingEnds, Finset.mem_filter, BundleState.mem_ends]
      exact ⟨fun h => h.1, fun h => ⟨h, h.1⟩⟩
    rw [hsurv, Finset.card_image_of_injOn]
    intro x hx y hy heq
    have hkx : endKey x < 2 * eCap := by
      have := hE_lt x.1 ((BundleState.mem_ends B b x).mp hx).1
      rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
    have hky : endKey y < 2 * eCap := by
      have := hE_lt y.1 ((BundleState.mem_ends B b y).mp hy).1
      rcases y with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
    exact endKey_injective (packEndKey_inj hkx hky heq).2
  have hraw_nodup_v : (raw.map Prod.fst).Nodup := rawByRootVRuns_pairwise.imp ne_of_lt
  have hex_rem : ∃ i, ∃ (hi : i < raw.length), (raw[i]'hi).1 = w_rem := by
    by_contra hno
    push Not at hno
    have hsr_eq : sr = raw := List.filter_eq_self.mpr fun vr hvr => by
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hvr
      exact bne_iff_ne.mpr (hno i hi)
    rw [hsr_eq, hraw_len] at hsr_len
    omega
  obtain ⟨i_rem, hi_rem, hrem_fst⟩ := hex_rem
  have hoth_ne : ∀ j (hj : j < raw.length), j ≠ i_rem → (raw[j]'hj).1 ≠ w_rem := fun j hj hne heq =>
    hne ((List.Nodup.getElem_inj_iff (i := j) (j := i_rem) (hi := by simp [hj]) (hj := by simp [hi_rem]) hraw_nodup_v).mp
      (by simp [heq, hrem_fst]))
  have herase_eq : raw.eraseIdx i_rem = sr := by
    have hgo : ∀ (l : List (ℕ × List End)) (idx : ℕ) (hidx : idx < l.length),
        (l[idx]'hidx).1 = w_rem → (∀ j (hj : j < l.length), j ≠ idx → (l[j]'hj).1 ≠ w_rem) →
        l.eraseIdx idx = l.filter fun vr => vr.1 != w_rem := by
      intro l; induction l with
      | nil => intro _ h; cases h
      | cons a tl ihl =>
        intro idx hidx h1 h2
        cases idx with
        | zero =>
          simp only [List.eraseIdx_zero, List.tail_cons, List.filter_cons,
            show (a.1 != w_rem) = false by simpa using h1]
          exact (List.filter_eq_self.mpr fun vr hvr => by
            obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hvr
            have := h2 (j + 1) (by simp; omega) (by omega)
            simpa using this).symm
        | succ idx' =>
          have ha_ne : a.1 ≠ w_rem := h2 0 (by simp) (by omega)
          simp only [List.eraseIdx_cons_succ, List.filter_cons, show (a.1 != w_rem) = true by simp [ha_ne]]
          congr 1
          exact ihl idx' (by simp at hidx; omega) (by simpa using h1) fun j hj hne =>
            h2 (j + 1) (by simp; omega) (by omega)
    exact hgo raw i_rem hi_rem hrem_fst hoth_ne
  have hrem_len : (raw[i_rem]'hi_rem).2.length = (B.ends b).card - L_b.length := by
    have hsplit_sum : vRunsEndsLen raw = (raw[i_rem]'hi_rem).2.length + vRunsEndsLen (raw.eraseIdx i_rem) := by
      have h1 := List.take_append_drop i_rem raw
      rw [List.drop_eq_getElem_cons hi_rem] at h1
      have h2 := congrArg vRunsEndsLen h1
      rw [List.eraseIdx_eq_take_drop_succ, vRunsEndsLen_append]
      rw [vRunsEndsLen_append] at h2
      simp only [vRunsEndsLen, List.map_cons, List.sum_cons] at h2 ⊢
      omega
    rw [herase_eq, hsr_len, hraw_len] at hsplit_sum
    omega
  have hbest_eq : maxRunIdx raw = i_rem := by
    have hraw_ne : raw ≠ [] := fun hnil => by rw [hnil] at hi_rem; cases hi_rem
    have hlt_b := maxRunIdx_lt hraw_ne
    have hspec := maxRunIdx_spec hraw_ne
    by_contra hne
    have hmem_sr : raw[maxRunIdx raw]'hlt_b ∈ sr := by
      rw [← herase_eq, List.eraseIdx_eq_take_drop_succ, List.mem_append]
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · left; rw [List.mem_iff_getElem]
        exact ⟨maxRunIdx raw, by simp [List.length_take]; omega, by simp⟩
      · right; rw [List.mem_iff_getElem]
        exact ⟨maxRunIdx raw - (i_rem + 1), by simp [List.length_drop]; omega,
          by simp [show i_rem + 1 + (maxRunIdx raw - (i_rem + 1)) = maxRunIdx raw by omega]⟩
    have h1 := hwin_lt _ hmem_sr
    have h2 := hspec.1 i_rem hi_rem
    omega
  refine ⟨(raw[i_rem]'hi_rem).2, by omega,
    fun x hx => by
      have h := (rawByRootVRuns_info _ (List.getElem_mem hi_rem)).2.2 x hx
      exact ⟨h.1, h.2.trans hrem_fst⟩, ?_⟩
  change promoteLargestRun raw = _
  have hne : raw ≠ [] := fun hnil => by rw [hnil] at hi_rem; cases hi_rem
  obtain ⟨hd, tl, hraw_cons⟩ := List.exists_cons_of_ne_nil hne
  have hprom : promoteLargestRun raw = raw.getD (maxRunIdx raw) (0, []) :: raw.eraseIdx (maxRunIdx raw) := by
    conv_lhs => rw [hraw_cons, promoteLargestRun]
    rw [← hraw_cons]
  rw [hprom, hbest_eq, herase_eq, List.getD_eq_getElem _ _ hi_rem]
  have hpair : raw[i_rem]'hi_rem = (w_rem, (raw[i_rem]'hi_rem).2) := Prod.ext hrem_fst rfl
  rw [← hpair]

lemma byRootVRuns_branch2_eq {eCap : ℕ} {B : BundleState} {src' : End → ℕ}
    {candSet_j : Finset ℕ} {scan_j : List (ℕ × ℕ × ℕ)} {b w_rem : ℕ}
    (hE_lt : ∀ e ∈ B.edges, e < eCap)
    (hval : ScanValidForSlot B src' candSet_j scan_j)
    (hrem_ne : ∀ t ∈ scan_j, t.1 = b → t.2.1 ≠ w_rem)
    (hrem_eq : ∀ x ∈ B.ends b, endKey x ∉ scan_j.map (fun t => t.2.2) → src' x = w_rem)
    (hdeg_pos : 0 < (B.ends b).card)
    (hkept_le : (B.ends b).card - (scan_j.filter fun t => t.1 == b).length ≤
      ((scanVRuns B src' b w_rem).getD (maxRunIdx (scanVRuns B src' b w_rem)) (0, [])).2.length) :
    let raw := rawByRootVRuns B B.edges src' b
    let bestIdx := maxRunIdx raw
    let L_b := scan_j.filter fun t => t.1 == b
    ∃ hlt : bestIdx < raw.length,
      byRootVRuns B B.edges src' b =
        (raw[bestIdx]'hlt) :: (raw.take bestIdx ++ raw.drop (bestIdx + 1)) ∧
      vRunsEndsLen (raw.take bestIdx) + (raw[bestIdx]'hlt).2.length +
        vRunsEndsLen (raw.drop (bestIdx + 1)) = (B.ends b).card ∧
      (B.ends b).card ≤ 2 * L_b.length ∧
      vRunsEndsLen (raw.take bestIdx) + vRunsEndsLen (raw.drop (bestIdx + 1)) ≤ L_b.length := by
  intro raw bestIdx L_b
  set sr := scanVRuns B src' b w_rem
  have hsr_len : vRunsEndsLen sr = L_b.length :=
    (scanVRuns_pack_eq_sort hE_lt hval hrem_ne hrem_eq).2
  have hraw_len : vRunsEndsLen raw = (B.ends b).card := by
    have hsort := rawByRootVRuns_pack_eq_sort (eCap := eCap) (B := B) (E := B.edges) (src' := src') (b := b) hE_lt
    change vRunsPacked eCap raw = _ at hsort
    rw [← vRunsPacked_length eCap, hsort, Finset.length_sort]
    have hsurv : survivingEnds B B.edges b = B.ends b := by
      ext x; simp only [survivingEnds, Finset.mem_filter, BundleState.mem_ends]
      exact ⟨fun h => h.1, fun h => ⟨h, h.1⟩⟩
    rw [hsurv, Finset.card_image_of_injOn]
    intro x hx y hy heq
    have hkx : endKey x < 2 * eCap := by
      have := hE_lt x.1 ((BundleState.mem_ends B b x).mp hx).1
      rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
    have hky : endKey y < 2 * eCap := by
      have := hE_lt y.1 ((BundleState.mem_ends B b y).mp hy).1
      rcases y with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
    exact endKey_injective (packEndKey_inj hkx hky heq).2
  have hraw_ne : raw ≠ [] := fun hnil => by rw [hnil] at hraw_len; simp [vRunsEndsLen] at hraw_len; omega
  have hlt : bestIdx < raw.length := maxRunIdx_lt hraw_ne
  have hby_eq : byRootVRuns B B.edges src' b =
      (raw[bestIdx]'hlt) :: (raw.take bestIdx ++ raw.drop (bestIdx + 1)) := by
    change promoteLargestRun raw = _
    obtain ⟨hd, tl, hraw_cons⟩ := List.exists_cons_of_ne_nil hraw_ne
    have hprom : promoteLargestRun raw = raw.getD (maxRunIdx raw) (0, []) :: raw.eraseIdx (maxRunIdx raw) := by
      conv_lhs => rw [hraw_cons, promoteLargestRun]
      rw [← hraw_cons]
    rw [hprom, List.getD_eq_getElem _ _ hlt, List.eraseIdx_eq_take_drop_succ]
  have hsplit_len : vRunsEndsLen (raw.take bestIdx) + (raw[bestIdx]'hlt).2.length +
      vRunsEndsLen (raw.drop (bestIdx + 1)) = (B.ends b).card := by
    have h1 := List.take_append_drop bestIdx raw
    rw [List.drop_eq_getElem_cons hlt] at h1
    have h2 := congrArg vRunsEndsLen h1
    rw [hraw_len, vRunsEndsLen_append] at h2
    simp only [vRunsEndsLen, List.map_cons, List.sum_cons] at h2 ⊢
    omega
  have hwin_le_Lb : (sr.getD (maxRunIdx sr) (0, [])).2.length ≤ L_b.length := by
    by_cases hsr : sr = []
    · simp [hsr]
    · have hlt_s : maxRunIdx sr < sr.length := maxRunIdx_lt hsr
      rw [List.getD_eq_getElem _ _ hlt_s, ← hsr_len]
      have h1 := List.take_append_drop (maxRunIdx sr) sr
      rw [List.drop_eq_getElem_cons hlt_s] at h1
      have h2 := congrArg vRunsEndsLen h1
      rw [vRunsEndsLen_append] at h2
      simp only [vRunsEndsLen, List.map_cons, List.sum_cons] at h2 ⊢
      omega
  have hwin_le_best : (sr.getD (maxRunIdx sr) (0, [])).2.length ≤ (raw[bestIdx]'hlt).2.length := by
    by_cases hsr : sr = []
    · simp [hsr]
    · have hlt_s : maxRunIdx sr < sr.length := maxRunIdx_lt hsr
      rw [List.getD_eq_getElem _ _ hlt_s]
      have hmem_raw : sr[maxRunIdx sr]'hlt_s ∈ raw :=
        (List.mem_filter.mp (List.getElem_mem hlt_s)).1
      obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hmem_raw
      have hspec := (maxRunIdx_spec hraw_ne).1 j hj
      rw [hjeq] at hspec
      exact hspec
  exact ⟨hlt, hby_eq, hsplit_len,
    by dsimp only [L_b] at hkept_le hwin_le_Lb ⊢; omega,
    by dsimp only [L_b] at hkept_le hwin_le_Lb ⊢; omega⟩

end

end MinCostFlow.SparseCore.Program
