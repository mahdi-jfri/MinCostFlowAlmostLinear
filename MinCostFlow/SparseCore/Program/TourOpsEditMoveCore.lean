module

public import MinCostFlow.SparseCore.Program.TourMoveMath
public import MinCostFlow.SparseCore.Program.TourOpsEditCommon
import Mathlib.Tactic

/-!
# Core invariant and root-detection lemmas for `moveEnds` (Op 0)

Provides:
- `tourMove_empty_core`: `TourCoreAt` preservation on the fast path `s.ord v = []`.
- `tourMove_rootTag_detect`: when `v ∉ s.rf.R` and `s.ord v ≠ []`, proves that the `rootTag`
  summary of `tKeep?` is `r + 1` if `F'.Connected v r` and `0` otherwise (in which case `tMove?`
  is non-empty with `rootTag` summary `r + 1`).
- `tourMove_slotSwap_bij`: bijection preservation when swapping `v ↔ v'` slots (`complement = true`).
- `tourMove_core`: uniform `TourCoreAt` reconstruction after `moveEnds` for both `c = false` and
  `c = true` and all three root cases.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-! ## Fast path (`s.ord v = []`) -/

/-- When `s.ord v = []`, `moveEnds v v' sel c` simply adds `v'` as a new isolated root with empty
order and leaves all splay trees and ends unchanged. -/
theorem tourMove_empty_core {τ_ord : Type} {vCap eCap b v v' : ℕ}
    {sel : Finset End} {c : Bool} {s : TourAbs} {x : TourConcrete τ_ord} {mem : ℕ → ℕ}
    (h : TourCoreAt vCap eCap b s x mem)
    (he : TourEditValid vCap eCap s (.moveEnds v v' sel c))
    (hnil : s.ord v = []) :
    let s' := tourApplyEdit s (.moveEnds v v' sel c)
    let mem' := Function.update mem (isRootBase b vCap + v') 1
    let x' : TourConcrete τ_ord := { x with compTree := Function.update x.compTree v' none }
    s'.ord = s.ord ∧ s'.rf.R = insert v' s.rf.R ∧ TourCoreAt vCap eCap b s' x' mem' := by
  classical
  intro s' mem' x'
  rcases he with ⟨hvLt, hv'Lt, hne, hvF, hv'NotF, hord_v', hsel⟩
  have hvalid' : TourValid vCap eCap s' :=
    tourValid_applyEdit_moveEnds h.valid ⟨hvLt, hv'Lt, hne, hvF, hv'NotF, hord_v', hsel⟩
  obtain ⟨hvR, hvIso⟩ := empty_ord_mem_roots h.valid hvF hnil
  have hrv : s.rf.root v = v := hvIso _ (h.valid.root_spec hvF).2
  have hord_eq : s'.ord = s.ord := by
    funext w
    by_cases hwv : w = v
    · subst hwv; simp [s', tourApplyEdit, applyOrdEdit, hnil]
    · by_cases hwv' : w = v'
      · subst hwv'; simp [s', tourApplyEdit, applyOrdEdit, hne.symm, hord_v', hnil]
      · simp [s', tourApplyEdit, applyOrdEdit, hwv, hwv']
  have hR_eq : s'.rf.R = insert v' s.rf.R := by
    simp only [s', tourApplyEdit, hrv, connected_refl, ↓reduceIte]
  have hft_v' : fullTour s'.ord s'.rf.F hvalid'.compat.forest v' = [] :=
    (fullTour_eq_nil_iff hvalid'.compat v').mpr (by rw [hord_eq, hord_v'])
  have hft_v : fullTour s'.ord s'.rf.F hvalid'.compat.forest v = [] :=
    (fullTour_eq_nil_iff hvalid'.compat v).mpr (by rw [hord_eq, hnil])
  have hft_other : ∀ r' ∈ s.rf.R,
      fullTour s'.ord s'.rf.F hvalid'.compat.forest r' =
      fullTour s.ord s.rf.F h.valid.compat.forest r' := by
    intro r' hr'
    by_cases hr'v : r' = v
    · subst hr'v; rw [hft_v, (fullTour_eq_nil_iff h.valid.compat r').mpr hnil]
    · exact fullTour_moveEnds_other h.valid ⟨hvLt, hv'Lt, hne, hvF, hv'NotF, hord_v', hsel⟩
        hr' (by rw [hrv]; exact hr'v)
  have hrt_eq : ∀ z, tourRootTagVal s' z = tourRootTagVal s z := by
    intro z
    by_cases hex : ∃ r' ∈ s.rf.R, (s.ord r').head? = some z
    · obtain ⟨r', hr'R, hr'h⟩ := hex
      rw [tourRootTagVal_eq_succ h.valid hr'R hr'h,
          tourRootTagVal_eq_succ hvalid' (hR_eq ▸ Finset.mem_insert_of_mem hr'R) (by rw [hord_eq]; exact hr'h)]
    · push Not at hex
      rw [tourRootTagVal_eq_zero hex, tourRootTagVal_eq_zero]
      intro r' hr' hh
      rw [hR_eq, Finset.mem_insert] at hr'
      rcases hr' with rfl | hr'R
      · rw [hord_eq, hord_v'] at hh; simp at hh
      · exact hex r' hr'R (by rwa [← hord_eq])
  have hmem_ne : ∀ a, a ≠ isRootBase b vCap + v' → mem' a = mem a := fun a ha =>
    Function.update_of_ne ha _ _
  have hhdr' : TourHeaderAt vCap eCap b x.numNodes mem' := by
    rcases h.header with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    have hf : ∀ k < 16, mem' (b + k) = mem (b + k) := fun k hk =>
      hmem_ne _ (by simp [isRootBase]; omega)
    exact ⟨by rw [hf _ (by decide)]; exact h0, by rw [hf _ (by decide)]; exact h1,
      by rw [hf _ (by decide)]; exact h2, by rw [hf _ (by decide)]; exact h3,
      by rw [hf _ (by decide)]; exact h4, by rw [hf _ (by decide)]; exact h5,
      by rw [hf _ (by decide)]; exact h6, by rw [hf _ (by decide)]; exact h7,
      by rw [hf _ (by decide)]; exact h8, by rw [hf _ (by decide)]; exact h9,
      by rw [hf _ (by decide)]; exact h10, by rw [hf _ (by decide)]; exact h11,
      by rw [hf _ (by decide)]; exact h12, by rw [hf _ (by decide)]; exact h13,
      by rw [hf _ (by decide)]; exact h14⟩
  refine ⟨hord_eq, hR_eq, ?_⟩
  refine
    { valid := hvalid'
      header := hhdr'
      numNodes_le := h.numNodes_le
      nodeOf_mem := fun k hk => by
        rw [hmem_ne _ (by simp [nodeOfEndBase, isRootBase]; omega)]; exact h.nodeOf_mem k hk
      nodeOf_keyOf := h.nodeOf_keyOf
      keyOf_mem := fun u h1 h2 => by
        rw [hmem_ne _ (by simp [keyOfNodeBase, isRootBase]; omega)]; exact h.keyOf_mem u h1 h2
      firstEnd_mem := fun w hw => by
        rw [hmem_ne _ (by simp [firstEndBase, isRootBase]; omega), hord_eq]; exact h.firstEnd_mem w hw
      isRoot_mem := fun w hw => by
        by_cases hww' : w = v'
        · subst hww'; simp [mem', hR_eq]
        · rw [hmem_ne _ (by omega), h.isRoot_mem w hw, hR_eq]
          simp [hww']
      slot_bij := h.slot_bij
      slotOf_mem := fun w hw => by
        rw [hmem_ne _ (by simp [slotOfVertBase, isRootBase]; omega)]; exact h.slotOf_mem w hw
      vertOf_mem := fun sl hsl => by
        rw [hmem_ne _ (by simp [vertOfSlotBase, isRootBase]; omega)]; exact h.vertOf_mem sl hsl
      active_end := fun w hw e he => by
        rw [hord_eq] at he
        rw [hmem_ne _ (by simp [endOwnerBase, isRootBase]; omega)]
        exact h.active_end w hw e he
      inactive_owner := fun k hk hno => by
        rw [hmem_ne _ (by simp [endOwnerBase, isRootBase]; omega)]
        exact h.inactive_owner k hk fun w hw => hno w (by rwa [hord_eq])
      markArr_zero := fun k hk => by
        rw [hmem_ne _ (by simp [markArrBase, isRootBase]; omega)]; exact h.markArr_zero k hk
      nodesAt := NodesAt.congr tourLayout h.nodesAt fun a ha =>
        hmem_ne a (by have := (inRecords_lt_ordHandle_of_le h.numNodes_le ha).1; simp [nodesBase, isRootBase] at this ⊢; omega)
      forestInv := h.forestInv
      nodes_exact := h.nodes_exact
      comp_none := fun r' hr' hft0 => by
        rw [hR_eq, Finset.mem_insert] at hr'
        rcases hr' with rfl | hr'R
        · simp [x']
        · have hne' : r' ≠ v' := fun heq => hv'NotF (heq ▸ h.valid.roots_sub hr'R)
          rw [hft_other r' hr'R] at hft0
          simp [x', Function.update_of_ne hne', h.comp_none r' hr'R hft0]
      comp_some := fun r' hr' hftNe => by
        rw [hR_eq, Finset.mem_insert] at hr'
        rcases hr' with rfl | hr'R
        · exact absurd hft_v' hftNe
        · have hne' : r' ≠ v' := fun heq => hv'NotF (heq ▸ h.valid.roots_sub hr'R)
          rw [hft_other r' hr'R] at hftNe ⊢
          obtain ⟨t, hct, htMem, htMap⟩ := h.comp_some r' hr'R hftNe
          exact ⟨t, by simp [x', Function.update_of_ne hne', hct], htMem, htMap⟩
      tree_class := fun t ht => by
        rcases h.tree_class t ht with ⟨r', hr'R, hct⟩ | ⟨u, htu, hno⟩
        · have hne' : r' ≠ v' := fun heq => hv'NotF (heq ▸ h.valid.roots_sub hr'R)
          exact Or.inl ⟨r', hR_eq ▸ Finset.mem_insert_of_mem hr'R, by simp [x', Function.update_of_ne hne', hct]⟩
        · exact Or.inr ⟨u, htu, fun w hw => hno w (by rwa [← hord_eq])⟩
      inactive_single := fun u h1 h2 hno =>
        h.inactive_single u h1 h2 fun w hw => hno w (by rwa [hord_eq])
      val_active := fun u h1 h2 hact => by
        obtain ⟨w, hw⟩ := hact
        rw [hord_eq] at hw
        have hFE : s'.rf.F.E = s.rf.F.E := rfl
        have hmk : s'.marked = s.marked := rfl
        simpa only [x', hFE, hmk, hrt_eq] using h.val_active u h1 h2 ⟨w, hw⟩
      val_inactive_rt := fun u h1 h2 hno =>
        h.val_inactive_rt u h1 h2 fun w hw => hno w (by rwa [hord_eq])
      val_unused_rt := h.val_unused_rt }

/-! ## Root-tag summary detection (`v ∉ s.rf.R`) -/

private theorem foldr_max_eq_zero_of_all_zero {ls : List ℕ} (h : ∀ z ∈ ls, z = 0) :
    ls.foldr max 0 = 0 := by
  induction ls with
  | nil => rfl
  | cons a as ih =>
    simp only [List.foldr_cons, h a (by simp), ih (fun z hz => h z (by simp [hz])), max_self]

private theorem foldr_max_eq_of_mem_le {ls : List ℕ} {m : ℕ}
    (hmem : m ∈ ls) (hle : ∀ z ∈ ls, z ≤ m) : ls.foldr max 0 = m := by
  have h1 : ls.foldr max 0 ≤ m := by
    clear hmem
    induction ls with
    | nil => simp
    | cons a as ih =>
      simp only [List.foldr_cons]
      exact max_le (hle a (by simp)) (ih (fun z hz => hle z (by simp [hz])))
  have h2 : m ≤ ls.foldr max 0 := by
    clear hle h1
    induction ls with
    | nil => simp at hmem
    | cons a as ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp hmem with rfl | htl
      · exact le_max_left _ _
      · exact le_trans (ih htl) (le_max_right _ _)
  omega

private theorem mem_rootTag_of_nodesAt {mem : ℕ → ℕ} {nb cap : ℕ}
    {sT : SplayState TourVal TourSum Unit} {t : AuxTree} {ts : List AuxTree}
    (hnodes : tourLayout.NodesAt mem nb cap sT) (hinv : TourForestInv cap sT ts) (ht : t ∈ ts) :
    mem (nb + 17 * t.rootId + 15) =
      (t.toList.map fun u => (sT.nodes u).val.rootTag).foldr max 0 := by
  have hne := hinv.nonEmpty t ht
  have hrcap : t.rootId ≤ cap := (hinv.mem_inCap ht (AuxTree.rootId_mem hne)).2
  have hnd := hnodes t.rootId hrcap
  have hsum_mem : mem (nb + 17 * t.rootId + 15) = (sT.nodes t.rootId).sum.rootTag := by
    have h1 := hnd.2.2.2.2.2.2.2.1.2.2.2
    have hoff : tourLayout.offSum = 12 := rfl
    simpa [NodeLayout.nodeAddr, tourLayout_stride, hoff, Nat.add_assoc] using h1
  rw [hsum_mem, hinv.sum_rootTag ht]

/-- When `v ∉ s.rf.R` and `s.ord v ≠ []`, splitting `t` into `(tKeep?, tMove?)` (with node values
still equal to `x.st`) places the unique nonzero `rootTag = r + 1` in `tKeep?` iff
`F'.Connected v r`, and otherwise in `tMove?`. -/
theorem tourMove_rootTag_detect {τ_ord : Type} {vCap eCap b v v' : ℕ}
    {sel : Finset End} {c : Bool} {s : TourAbs} {x : TourConcrete τ_ord} {mem mem' : ℕ → ℕ}
    {sT : SplayState TourVal TourSum Unit} {t : AuxTree} {tKeep? tMove? : Option AuxTree}
    {rest : List AuxTree}
    (h : TourCoreAt vCap eCap b s x mem)
    (he : TourEditValid vCap eCap s (.moveEnds v v' sel c))
    (hvNotR : v ∉ s.rf.R)
    (ht_mem : t ∈ x.trees)
    (ht_map : t.toList.map (fun id => endOfKey (x.keyOf id)) =
      fullTour s.ord s.rf.F h.valid.compat.forest (s.rf.root v))
    (hnodes : tourLayout.NodesAt mem' (nodesBase b vCap eCap) x.numNodes sT)
    (hinv : TourForestInv x.numNodes sT (optTrees tKeep? ++ optTrees tMove? ++ rest))
    (hval : ∀ u ≤ x.numNodes, (sT.nodes u).val = (x.st.nodes u).val)
    (hperm : (optList tKeep? ++ optList tMove?).Perm t.toList)
    (hKeep_map : (optList tKeep?).map (fun id => endOfKey (x.keyOf id)) =
      fullTour (tourApplyEdit s (.moveEnds v v' sel c)).ord
        (tourApplyEdit s (.moveEnds v v' sel c)).rf.F
        (tourValid_applyEdit_moveEnds h.valid he).compat.forest v)
    (hMove_map : (optList tMove?).map (fun id => endOfKey (x.keyOf id)) =
      fullTour (tourApplyEdit s (.moveEnds v v' sel c)).ord
        (tourApplyEdit s (.moveEnds v v' sel c)).rf.F
        (tourValid_applyEdit_moveEnds h.valid he).compat.forest v') :
    let s' := tourApplyEdit s (.moveEnds v v' sel c)
    let r := s.rf.root v
    let rtKeep := if optRoot tKeep? = 0 then 0 else mem' (nodesBase b vCap eCap + 17 * optRoot tKeep? + 15)
    (s'.rf.F.Connected v r → rtKeep = r + 1 ∧ ∃ tK, tKeep? = some tK) ∧
    (¬s'.rf.F.Connected v r → rtKeep = 0 ∧ ∃ tM, tMove? = some tM ∧
      mem' (nodesBase b vCap eCap + 17 * tM.rootId + 15) = r + 1) := by
  classical
  intro s' r rtKeep
  rcases he with ⟨hvLt, hv'Lt, hne, hvF, hv'NotF, hord_v', hsel⟩
  have hvalid' := tourValid_applyEdit_moveEnds (c := c) h.valid ⟨hvLt, hv'Lt, hne, hvF, hv'NotF, hord_v', hsel⟩
  have hr_spec := h.valid.root_spec hvF
  have hr_ne_v : r ≠ v := fun heq => hvNotR (heq ▸ hr_spec.1)
  have hr_ne_v' : r ≠ v' := fun heq => hv'NotF (heq ▸ h.valid.roots_sub hr_spec.1)
  have hord_r_eq : s'.ord r = s.ord r := by
    simp [s', tourApplyEdit, applyOrdEdit, hr_ne_v, hr_ne_v']
  have hord_r_ne : s.ord r ≠ [] := by
    obtain ⟨e, heF, hsrc⟩ := exists_edge_of_connected_ne (connected_symm hr_spec.2) hr_ne_v
    exact List.ne_nil_of_mem (hsrc ▸ h.valid.compat.mem_ord_of_forest heF)
  obtain ⟨aR, haR⟩ : ∃ aR, (s.ord r).head? = some aR :=
    Option.isSome_iff_exists.mp (by cases ho : s.ord r <;> simp_all)
  have haR_mem : aR ∈ s'.ord r := by rw [hord_r_eq]; exact List.mem_of_head? haR
  have hval_u : ∀ u ∈ t.toList, (sT.nodes u).val.rootTag = tourRootTagVal s (endOfKey (x.keyOf u)) := by
    intro u hu
    have hu_in : 1 ≤ u ∧ u ≤ x.numNodes := (h.nodes_exact u).mp (List.mem_flatMap.mpr ⟨t, ht_mem, hu⟩)
    rw [hval u hu_in.2]
    have hu_ft : endOfKey (x.keyOf u) ∈ fullTour s.ord s.rf.F h.valid.compat.forest r := by
      rw [← ht_map]; exact List.mem_map_of_mem hu
    obtain ⟨w, hw, _⟩ := ((fullTour_spec h.valid.compat r).2 _).mp hu_ft
    rw [h.val_active u hu_in.1 hu_in.2 ⟨w, hw⟩]
  have hrt_zero_ne : ∀ u ∈ t.toList, endOfKey (x.keyOf u) ≠ aR → (sT.nodes u).val.rootTag = 0 := by
    intro u hu hne_aR
    rw [hval_u u hu]
    apply tourRootTagVal_eq_zero
    intro r' hr'R hr'h
    have hu_ft : endOfKey (x.keyOf u) ∈ fullTour s.ord s.rf.F h.valid.compat.forest r := by
      rw [← ht_map]; exact List.mem_map_of_mem hu
    obtain ⟨w, hw, hcw⟩ := ((fullTour_spec h.valid.compat r).2 _).mp hu_ft
    have hwr' : w = r' := h.valid.compat.unique w r' _ hw (List.mem_of_head? hr'h)
    rw [hwr'] at hcw
    have hrr' : r' = r :=
      (h.valid.root_eq_of_mem (h.valid.roots_sub hr'R) hr'R (connected_refl _ _)).symm.trans
        (h.valid.root_eq_of_mem (h.valid.roots_sub hr'R) hr_spec.1 (connected_symm hcw))
    rw [hrr', haR] at hr'h
    exact hne_aR (Option.some.inj hr'h).symm
  have hrt_eq_aR : ∀ u ∈ t.toList, endOfKey (x.keyOf u) = aR → (sT.nodes u).val.rootTag = r + 1 := by
    intro u hu heq
    rw [hval_u u hu, heq, tourRootTagVal_eq_succ h.valid hr_spec.1 haR]
  have hnc_vv' : ¬s'.rf.F.Connected v v' :=
    not_connected_v_v'_applySplit h.valid.compat.forest hne hv'NotF _ _
  have hconn_or : s'.rf.F.Connected v r ∨ s'.rf.F.Connected v' r :=
    connected_applySplit_v_or_v' h.valid.compat.forest _ _ hr_spec.2
  constructor
  · intro hvr
    have haR_ftK : aR ∈ fullTour s'.ord s'.rf.F hvalid'.compat.forest v :=
      ((fullTour_spec hvalid'.compat v).2 aR).mpr ⟨r, haR_mem, hvr⟩
    rw [← hKeep_map] at haR_ftK
    obtain ⟨ua, hua_K, hua_eq⟩ := List.mem_map.mp haR_ftK
    cases hKc : tKeep? with
    | none => simp [hKc, optList] at hua_K
    | some tK =>
      rw [hKc] at hinv hperm hua_K
      have hK_mem : tK ∈ optTrees (some tK) ++ optTrees tMove? ++ rest := by simp [optTrees]
      have hK_nz : tK.rootId ≠ 0 := Nat.ne_of_gt (hinv.mem_inCap hK_mem (AuxTree.rootId_mem (hinv.nonEmpty tK hK_mem))).1
      have hrtK_eq : rtKeep = (tK.toList.map fun u => (sT.nodes u).val.rootTag).foldr max 0 := by
        simp only [rtKeep, hKc, optRoot, Option.elim, hK_nz, ↓reduceIte]
        exact mem_rootTag_of_nodesAt hnodes hinv hK_mem
      have hsub_t : ∀ u ∈ tK.toList, u ∈ t.toList := fun u hu =>
        hperm.mem_iff.mp (List.mem_append_left _ (by simpa [optList] using hu))
      have hua_tK : ua ∈ tK.toList := by simpa [optList] using hua_K
      refine ⟨?_, tK, rfl⟩
      rw [hrtK_eq]
      refine foldr_max_eq_of_mem_le
        (List.mem_map.mpr ⟨ua, hua_tK, hrt_eq_aR ua (hsub_t ua hua_tK) hua_eq⟩) ?_
      intro z hz
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hz
      by_cases hu_aR : endOfKey (x.keyOf u) = aR
      · rw [hrt_eq_aR u (hsub_t u hu) hu_aR]
      · rw [hrt_zero_ne u (hsub_t u hu) hu_aR]; omega
  · intro hnvr
    have hv'r : s'.rf.F.Connected v' r := hconn_or.resolve_left hnvr
    have haR_notK : aR ∉ fullTour s'.ord s'.rf.F hvalid'.compat.forest v := by
      intro hmem
      obtain ⟨w, hw, hvw⟩ := ((fullTour_spec hvalid'.compat v).2 aR).mp hmem
      have hwr : w = r := hvalid'.compat.unique w r aR hw haR_mem
      exact hnvr (hwr ▸ hvw)
    have hrtK0 : rtKeep = 0 := by
      cases hKc : tKeep? with
      | none => simp [rtKeep, hKc, optRoot]
      | some tK =>
        rw [hKc] at hinv hperm hKeep_map
        have hK_mem : tK ∈ optTrees (some tK) ++ optTrees tMove? ++ rest := by simp [optTrees]
        have hK_nz : tK.rootId ≠ 0 := Nat.ne_of_gt (hinv.mem_inCap hK_mem (AuxTree.rootId_mem (hinv.nonEmpty tK hK_mem))).1
        simp only [rtKeep, hKc, optRoot, Option.elim, hK_nz, ↓reduceIte]
        rw [mem_rootTag_of_nodesAt hnodes hinv hK_mem]
        apply foldr_max_eq_zero_of_all_zero
        intro z hz
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hz
        have hu_t : u ∈ t.toList := hperm.mem_iff.mp (List.mem_append_left _ (by simpa [optList] using hu))
        have hu_ne_aR : endOfKey (x.keyOf u) ≠ aR := fun heq => haR_notK (by
          rw [← hKeep_map]; exact List.mem_map.mpr ⟨u, by simpa [optList] using hu, heq⟩)
        exact hrt_zero_ne u hu_t hu_ne_aR
    have haR_ftM : aR ∈ fullTour s'.ord s'.rf.F hvalid'.compat.forest v' :=
      ((fullTour_spec hvalid'.compat v').2 aR).mpr ⟨r, haR_mem, hv'r⟩
    rw [← hMove_map] at haR_ftM
    obtain ⟨ua, hua_M, hua_eq⟩ := List.mem_map.mp haR_ftM
    cases hMc : tMove? with
    | none => simp [hMc, optList] at hua_M
    | some tM =>
      rw [hMc] at hinv hperm hua_M
      have hM_mem : tM ∈ optTrees tKeep? ++ optTrees (some tM) ++ rest := by simp [optTrees]
      have hsub_t : ∀ u ∈ tM.toList, u ∈ t.toList := fun u hu =>
        hperm.mem_iff.mp (List.mem_append_right _ (by simpa [optList] using hu))
      have hua_tM : ua ∈ tM.toList := by simpa [optList] using hua_M
      refine ⟨hrtK0, tM, rfl, ?_⟩
      rw [mem_rootTag_of_nodesAt hnodes hinv hM_mem]
      refine foldr_max_eq_of_mem_le
        (List.mem_map.mpr ⟨ua, hua_tM, hrt_eq_aR ua (hsub_t ua hua_tM) hua_eq⟩) ?_
      intro z hz
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hz
      by_cases hu_aR : endOfKey (x.keyOf u) = aR
      · rw [hrt_eq_aR u (hsub_t u hu) hu_aR]
      · rw [hrt_zero_ne u (hsub_t u hu) hu_aR]; omega

/-! ## Slot-swap bijection helper (`c = true`) -/

/-- Swapping `slotOf` at `v ↔ v'` and `vertOf` at `sv ↔ sv'` preserves the slot bijection. -/
theorem tourMove_slotSwap_bij {vCap v v' : ℕ} {slotOf vertOf : ℕ → ℕ}
    (hbij : ∀ w < vCap, slotOf w < vCap ∧ vertOf (slotOf w) = w ∧ slotOf (vertOf w) = w)
    (hvLt : v < vCap) (hv'Lt : v' < vCap) (hne : v ≠ v') :
    let sv := slotOf v
    let sv' := slotOf v'
    let slotOf' := Function.update (Function.update slotOf v sv') v' sv
    let vertOf' := Function.update (Function.update vertOf sv v') sv' v
    ∀ w < vCap, slotOf' w < vCap ∧ vertOf' (slotOf' w) = w ∧ slotOf' (vertOf' w) = w := by
  intro sv sv' slotOf' vertOf' w hw
  have hsv_lt : sv < vCap := (hbij v hvLt).1
  have hsv'_lt : sv' < vCap := (hbij v' hv'Lt).1
  have hsv_ne : sv ≠ sv' := fun heq => hne (by
    dsimp only [sv, sv'] at heq
    rw [← (hbij v hvLt).2.1, heq, (hbij v' hv'Lt).2.1])
  refine ⟨?_, ?_, ?_⟩
  · by_cases hw' : w = v'
    · subst hw'; simp [slotOf', hsv_lt]
    · by_cases hwv : w = v
      · subst hwv; simp [slotOf', hw', hsv'_lt]
      · simp [slotOf', hw', hwv, (hbij w hw).1]
  · by_cases hw' : w = v'
    · subst hw'; simp [slotOf', vertOf', hsv_ne]
    · by_cases hwv : w = v
      · subst hwv; simp [slotOf', vertOf', hw']
      · have hsw_ne : slotOf w ≠ sv := fun heq => hwv (by rw [← (hbij w hw).2.1, heq, (hbij v hvLt).2.1])
        have hsw_ne' : slotOf w ≠ sv' := fun heq => hw' (by rw [← (hbij w hw).2.1, heq, (hbij v' hv'Lt).2.1])
        simp [slotOf', vertOf', hw', hwv, hsw_ne, hsw_ne', (hbij w hw).2.1]
  · by_cases hw' : w = sv'
    · subst hw'; simp [slotOf', vertOf', hne]
    · by_cases hwv : w = sv
      · subst hwv; simp [slotOf', vertOf', hw']
      · have hvw_ne : vertOf w ≠ v := fun heq => hwv (by rw [← (hbij w hw).2.2, heq])
        have hvw_ne' : vertOf w ≠ v' := fun heq => hw' (by rw [← (hbij w hw).2.2, heq])
        simp [slotOf', vertOf', hw', hwv, hvw_ne, hvw_ne', (hbij w hw).2.2]

/-! ## General `TourCoreAt` reconstruction after `moveEnds` -/

open Classical in
/-- Uniform `TourCoreAt` reconstruction after `moveEnds v v' sel c` (non-empty `s.ord v`),
handling both `c = false` / `c = true` and all three root cases simultaneously. -/
theorem tourMove_core {τ_ord : Type} {vCap eCap b v v' : ℕ}
    {sel : Finset End} {c : Bool} {s : TourAbs} {x : TourConcrete τ_ord} {mem memF : ℕ → ℕ}
    {sF : SplayState TourVal TourSum Unit} {t : AuxTree} {tKeep'? tMove'? : Option AuxTree}
    {rest : List AuxTree} {slotOf' vertOf' : ℕ → ℕ}
    (h : TourCoreAt vCap eCap b s x mem)
    (he : TourEditValid vCap eCap s (.moveEnds v v' sel c))
    (hord_v_ne : s.ord v ≠ [])
    (hct_r : x.compTree (s.rf.root v) = some t)
    (hperm_r : x.trees.Perm (t :: rest))
    (ht_map : t.toList.map (fun id => endOfKey (x.keyOf id)) =
      fullTour s.ord s.rf.F h.valid.compat.forest (s.rf.root v))
    (hhdrF : TourHeaderAt vCap eCap b x.numNodes memF)
    (hnodeOfF : ∀ k < 2 * eCap, memF (nodeOfEndBase b vCap + k) = x.nodeOf k)
    (hkeyOfF : ∀ u, 1 ≤ u → u ≤ x.numNodes → memF (keyOfNodeBase b vCap eCap + u) = x.keyOf u)
    (hfirstEndF : ∀ w < vCap, memF (firstEndBase b + w) =
      match ((tourApplyEdit s (.moveEnds v v' sel c)).ord w).head? with
      | none => 0
      | some e => x.nodeOf (endKey e))
    (hisRootF : ∀ w < vCap, memF (isRootBase b vCap + w) =
      if w ∈ (tourApplyEdit s (.moveEnds v v' sel c)).rf.R then 1 else 0)
    (hbij' : ∀ w < vCap, slotOf' w < vCap ∧ vertOf' (slotOf' w) = w ∧ slotOf' (vertOf' w) = w)
    (hslotOfF : ∀ w < vCap, decodeSlot (memF (slotOfVertBase b vCap eCap + w)) w = slotOf' w)
    (hvertOfF : ∀ sl < vCap, decodeSlot (memF (vertOfSlotBase b vCap eCap + sl)) sl = vertOf' sl)
    (hendOwnerAct : ∀ w < vCap, ∀ e ∈ (tourApplyEdit s (.moveEnds v v' sel c)).ord w,
      memF (endOwnerBase b vCap eCap + endKey e) = slotOf' w + 1)
    (hendOwnerInact : ∀ k < 2 * eCap,
      (∀ w, endOfKey k ∉ (tourApplyEdit s (.moveEnds v v' sel c)).ord w) →
      memF (endOwnerBase b vCap eCap + k) = 0)
    (hmarkArrF : ∀ k < 2 * eCap, memF (markArrBase b vCap eCap + k) = 0)
    (hnF : tourLayout.NodesAt memF (nodesBase b vCap eCap) x.numNodes sF)
    (hinvF : TourForestInv x.numNodes sF (optTrees tKeep'? ++ optTrees tMove'? ++ rest))
    (hperm_nodes : (optList tKeep'? ++ optList tMove'?).Perm t.toList)
    (hKeep_map : (optList tKeep'?).map (fun id => endOfKey (x.keyOf id)) =
      fullTour (tourApplyEdit s (.moveEnds v v' sel c)).ord
        (tourApplyEdit s (.moveEnds v v' sel c)).rf.F
        (tourValid_applyEdit_moveEnds h.valid he).compat.forest
        (if (tourApplyEdit s (.moveEnds v v' sel c)).rf.F.Connected v (s.rf.root v) then s.rf.root v else v))
    (hMove_map : (optList tMove'?).map (fun id => endOfKey (x.keyOf id)) =
      fullTour (tourApplyEdit s (.moveEnds v v' sel c)).ord
        (tourApplyEdit s (.moveEnds v v' sel c)).rf.F
        (tourValid_applyEdit_moveEnds h.valid he).compat.forest
        (if (tourApplyEdit s (.moveEnds v v' sel c)).rf.F.Connected v (s.rf.root v) then v' else s.rf.root v))
    (hvalF_act : ∀ u, 1 ≤ u → u ≤ x.numNodes →
      (∃ w, endOfKey (x.keyOf u) ∈ (tourApplyEdit s (.moveEnds v v' sel c)).ord w) →
      (sF.nodes u).val =
        { isOpen := decide ((endOfKey (x.keyOf u)).1 ∉ (tourApplyEdit s (.moveEnds v v' sel c)).rf.F.E)
          isMarked := decide (endOfKey (x.keyOf u) ∈ (tourApplyEdit s (.moveEnds v v' sel c)).marked)
          rootTag := tourRootTagVal (tourApplyEdit s (.moveEnds v v' sel c)) (endOfKey (x.keyOf u)) })
    (hvalF_oth : ∀ u ≤ x.numNodes, u ∉ t.toList → (sF.nodes u).val = (x.st.nodes u).val) :
    let s' := tourApplyEdit s (.moveEnds v v' sel c)
    let r := s.rf.root v
    let rKeep := if s'.rf.F.Connected v r then r else v
    let rMove := if s'.rf.F.Connected v r then v' else r
    let x' : TourConcrete τ_ord :=
      { ordX := x.ordX
        numNodes := x.numNodes
        st := sF
        trees := optTrees tKeep'? ++ optTrees tMove'? ++ rest
        nodeOf := x.nodeOf
        keyOf := x.keyOf
        compTree := Function.update (Function.update x.compTree rKeep tKeep'?) rMove tMove'?
        slotOf := slotOf'
        vertOf := vertOf' }
    TourCoreAt vCap eCap b s' x' memF := by
  classical
  intro s' r rKeep rMove x'
  rcases he with ⟨hvLt, hv'Lt, hne, hvF, hv'NotF, hord_v', hsel⟩
  have hvalid' := tourValid_applyEdit_moveEnds (c := c) h.valid ⟨hvLt, hv'Lt, hne, hvF, hv'NotF, hord_v', hsel⟩
  have hr_spec := h.valid.root_spec hvF
  have hr_ne_v' : r ≠ v' := fun heq => hv'NotF (heq ▸ h.valid.roots_sub hr_spec.1)
  have hact_iff : ∀ z, (∃ w, z ∈ s'.ord w) ↔ (∃ w, z ∈ s.ord w) := by
    intro z; constructor
    · rintro ⟨w, hw⟩
      by_cases hwv : w = v
      · subst hwv; simp only [s', tourApplyEdit, applyOrdEdit, ↓reduceIte, List.mem_filter] at hw
        exact ⟨w, hw.1⟩
      · by_cases hwv' : w = v'
        · subst hwv'
          simp only [s', tourApplyEdit, applyOrdEdit, hne.symm, ↓reduceIte,
            hord_v', List.nil_append, List.mem_filter] at hw
          exact ⟨v, hw.1⟩
        · simp only [s', tourApplyEdit, applyOrdEdit, hwv, hwv', ↓reduceIte] at hw
          exact ⟨w, hw⟩
    · rintro ⟨w, hw⟩
      by_cases hwv : w = v
      · subst hwv
        by_cases hp : movedBy sel c z = true
        · exact ⟨v', by simp [s', tourApplyEdit, applyOrdEdit, hne.symm, hord_v', hw, hp]⟩
        · have hpf : movedBy sel c z = false := by cases hm : movedBy sel c z <;> simp_all
          exact ⟨w, by simp [s', tourApplyEdit, applyOrdEdit, hw, hpf]⟩
      · have hwv' : w ≠ v' := fun heq => by rw [heq, hord_v'] at hw; simp at hw
        exact ⟨w, by simp [s', tourApplyEdit, applyOrdEdit, hwv, hwv', hw]⟩
  have hrKM_ne : rKeep ≠ rMove := by
    dsimp only [rKeep, rMove]
    split_ifs with hvr
    · exact hr_ne_v'
    · intro heq; rw [heq] at hvr; exact hvr (connected_refl _ _)
  have hR_cases : ∀ r' ∈ s'.rf.R, r' = rKeep ∨ r' = rMove ∨ (r' ∈ s.rf.R ∧ r' ≠ r) := by
    intro r' hr'
    simp only [s', tourApplyEdit, Finset.mem_insert] at hr'
    rcases hr' with rfl | hr'R
    · by_cases hvr : s'.rf.F.Connected v r
      · exact Or.inr (Or.inl (by change (if s'.rf.F.Connected v r then v' else v) = rMove; simp [rMove, hvr]))
      · exact Or.inl (by change (if s'.rf.F.Connected v r then v' else v) = rKeep; simp [rKeep, hvr])
    · by_cases hr'r : r' = r
      · rw [hr'r]
        by_cases hvr : s'.rf.F.Connected v r
        · exact Or.inl (by simp only [rKeep, hvr, ↓reduceIte])
        · exact Or.inr (Or.inl (by simp only [rMove, hvr, ↓reduceIte]))
      · exact Or.inr (Or.inr ⟨hr'R, hr'r⟩)
  have hcomp_inj : ∀ r' ∈ s.rf.R, r' ≠ r → x.compTree r' ≠ some t := by
    intro r' hr' hne' heq
    have hne_ft : fullTour s.ord s.rf.F h.valid.compat.forest r' ≠ [] := fun h0 => by
      rw [h.comp_none r' hr' h0] at heq; cases heq
    obtain ⟨t', ht'eq, _, ht'map⟩ := h.comp_some r' hr' hne_ft
    rw [heq] at ht'eq; cases Option.some.inj ht'eq
    obtain ⟨a, ha⟩ : ∃ a, (s.ord v).head? = some a :=
      Option.isSome_iff_exists.mp (by cases ho : s.ord v <;> simp_all)
    have ha_ft : a ∈ fullTour s.ord s.rf.F h.valid.compat.forest r :=
      ((fullTour_spec h.valid.compat r).2 a).mpr ⟨v, List.mem_of_head? ha, connected_symm hr_spec.2⟩
    rw [← ht_map, ht'map] at ha_ft
    obtain ⟨w, hw, hcr'⟩ := ((fullTour_spec h.valid.compat r').2 a).mp ha_ft
    have hwv : w = v := h.valid.compat.unique w v a hw (List.mem_of_head? ha)
    rw [hwv] at hcr'
    exact hne' ((h.valid.unique_root v hvF).unique ⟨hr', connected_symm hcr'⟩ hr_spec)
  have hnodes_perm : (optTrees tKeep'? ++ optTrees tMove'? ++ rest).flatMap AuxTree.toList |>.Perm
      (x.trees.flatMap AuxTree.toList) := by
    have h1 : (optTrees tKeep'? ++ optTrees tMove'? ++ rest).flatMap AuxTree.toList =
        (optList tKeep'? ++ optList tMove'?) ++ rest.flatMap AuxTree.toList := by
      simp only [List.flatMap_append, List.append_assoc]
      have hK : (optTrees tKeep'?).flatMap AuxTree.toList = optList tKeep'? := by
        cases tKeep'? <;> simp [optTrees, optList]
      have hM : (optTrees tMove'?).flatMap AuxTree.toList = optList tMove'? := by
        cases tMove'? <;> simp [optTrees, optList]
      rw [hK, hM]
    rw [h1]
    exact (hperm_nodes.append_right _).trans (by
      have hp := hperm_r.symm.flatMap_right AuxTree.toList
      simpa [List.flatMap_cons] using hp)
  have hmem_t_of_inact : ∀ u, (∀ w, endOfKey (x.keyOf u) ∉ s.ord w) → u ∉ t.toList := by
    intro u hno hu
    have hft : endOfKey (x.keyOf u) ∈ fullTour s.ord s.rf.F h.valid.compat.forest r := by
      rw [← ht_map]; exact List.mem_map_of_mem hu
    obtain ⟨w, hw, _⟩ := ((fullTour_spec h.valid.compat r).2 _).mp hft
    exact hno w hw
  have hrest_no_t : ∀ t' ∈ rest, t' ≠ t := by
    have hnd := h.forestInv.nodupAll
    have hnd' := (hperm_r.flatMap_right AuxTree.toList).nodup_iff.mp hnd
    have hne_t : t.toList ≠ [] := by
      have h1 := h.forestInv.nonEmpty t (hperm_r.mem_iff.mpr (by simp))
      cases htc : t with
      | leaf => exact absurd htc h1
      | node _ _ _ => simp [AuxTree.toList]
    obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil t.toList hne_t
    have hsp := List.nodup_append.mp (by simpa [List.flatMap_cons] using hnd')
    intro t' ht' heq; subst heq
    exact hsp.2.2 u hu u (List.mem_flatMap.mpr ⟨t', ht', hu⟩) rfl
  refine
    { valid := hvalid'
      header := hhdrF
      numNodes_le := h.numNodes_le
      nodeOf_mem := fun k hk => ⟨hnodeOfF k hk, (h.nodeOf_mem k hk).2⟩
      nodeOf_keyOf := h.nodeOf_keyOf
      keyOf_mem := fun u h1 h2 => ⟨hkeyOfF u h1 h2, (h.keyOf_mem u h1 h2).2⟩
      firstEnd_mem := hfirstEndF
      isRoot_mem := hisRootF
      slot_bij := hbij'
      slotOf_mem := hslotOfF
      vertOf_mem := hvertOfF
      active_end := fun w hw e he' => by
        obtain ⟨w0, hw0⟩ := (hact_iff e).mp ⟨w, he'⟩
        have hw0_lt : w0 < vCap := by
          by_contra hge
          have h0 := h.valid.ordWithin.2.1 w0 (Nat.le_of_not_lt hge)
          rw [h0] at hw0; simp at hw0
        exact ⟨(h.active_end w0 hw0_lt e hw0).1, hendOwnerAct w hw e he'⟩
      inactive_owner := hendOwnerInact
      markArr_zero := hmarkArrF
      nodesAt := hnF
      forestInv := hinvF
      nodes_exact := fun u => (hnodes_perm.mem_iff).trans (h.nodes_exact u)
      comp_none := fun r' hr' hft0 => by
        rcases hR_cases r' hr' with rfl | rfl | ⟨hr'R, hr'r⟩
        · rw [← hKeep_map] at hft0
          have hnil : optList tKeep'? = [] := List.map_eq_nil_iff.mp hft0
          have hK0 : tKeep'? = none := by
            cases hKc : tKeep'? with
            | none => rfl
            | some tK =>
              rw [hKc] at hinvF hnil
              have hne := hinvF.nonEmpty tK (by simp [optTrees])
              cases tK <;> simp [optList, AuxTree.toList] at hne hnil
          simp [x', Function.update_of_ne hrKM_ne, hK0]
        · rw [← hMove_map] at hft0
          have hnil : optList tMove'? = [] := List.map_eq_nil_iff.mp hft0
          have hM0 : tMove'? = none := by
            cases hMc : tMove'? with
            | none => rfl
            | some tM =>
              rw [hMc] at hinvF hnil
              have hne := hinvF.nonEmpty tM (by simp [optTrees])
              cases tM <;> simp [optList, AuxTree.toList] at hne hnil
          simp [x', hM0]
        · have hne1 : r' ≠ rKeep := by
            dsimp only [rKeep]; split_ifs with hvr
            · exact hr'r
            · intro heq; subst heq; exact hr'r (h.valid.root_eq_of_mem hvF hr'R (connected_refl _ _)).symm
          have hne2 : r' ≠ rMove := by
            dsimp only [rMove]; split_ifs with hvr
            · exact fun heq => hv'NotF (heq ▸ h.valid.roots_sub hr'R)
            · exact hr'r
          rw [fullTour_moveEnds_other h.valid ⟨hvLt, hv'Lt, hne, hvF, hv'NotF, hord_v', hsel⟩ hr'R hr'r] at hft0
          simp [x', Function.update_of_ne hne2, Function.update_of_ne hne1, h.comp_none r' hr'R hft0]
      comp_some := fun r' hr' hftNe => by
        rcases hR_cases r' hr' with rfl | rfl | ⟨hr'R, hr'r⟩
        · cases hKc : tKeep'? with
          | none => rw [hKc, optList] at hKeep_map; exact absurd hKeep_map.symm hftNe
          | some tK =>
            refine ⟨tK, by simp [x', Function.update_of_ne hrKM_ne, hKc],
              by simp [x', hKc, optTrees], by simpa [hKc, optList] using hKeep_map⟩
        · cases hMc : tMove'? with
          | none => rw [hMc, optList] at hMove_map; exact absurd hMove_map.symm hftNe
          | some tM =>
            refine ⟨tM, by simp [x', hMc],
              by simp [x', hMc, optTrees], by simpa [hMc, optList] using hMove_map⟩
        · have hne1 : r' ≠ rKeep := by
            dsimp only [rKeep]; split_ifs with hvr
            · exact hr'r
            · intro heq; subst heq; exact hr'r (h.valid.root_eq_of_mem hvF hr'R (connected_refl _ _)).symm
          have hne2 : r' ≠ rMove := by
            dsimp only [rMove]; split_ifs with hvr
            · exact fun heq => hv'NotF (heq ▸ h.valid.roots_sub hr'R)
            · exact hr'r
          have hft_eq := fullTour_moveEnds_other (c := c) h.valid ⟨hvLt, hv'Lt, hne, hvF, hv'NotF, hord_v', hsel⟩ hr'R hr'r
          rw [hft_eq] at hftNe ⊢
          obtain ⟨t', hct', ht'Mem, ht'Map⟩ := h.comp_some r' hr'R hftNe
          have ht'_ne : t' ≠ t := fun heq => hcomp_inj r' hr'R hr'r (heq ▸ hct')
          have ht'_rest : t' ∈ rest := (List.mem_cons.mp (hperm_r.mem_iff.mp ht'Mem)).resolve_left ht'_ne
          exact ⟨t', by simp [x', Function.update_of_ne hne2, Function.update_of_ne hne1, hct'],
            by simp [x', ht'_rest], ht'Map⟩
      tree_class := fun t' ht' => by
        simp only [x', List.mem_append] at ht'
        rcases ht' with (htK | htM) | htR
        · cases hKc : tKeep'? with
          | none => simp [hKc, optTrees] at htK
          | some tK =>
            simp only [hKc, optTrees, Option.toList_some, List.mem_singleton] at htK; subst htK
            have hrK_in : rKeep ∈ s'.rf.R := by
              have hR : s'.rf.R = insert (if s'.rf.F.Connected v r then v' else v) s.rf.R := rfl
              dsimp only [rKeep]; rw [hR]; split_ifs with hvr
              · exact Finset.mem_insert_of_mem hr_spec.1
              · exact Finset.mem_insert_self _ _
            exact Or.inl ⟨rKeep, hrK_in, by simp [x', Function.update_of_ne hrKM_ne, hKc]⟩
        · cases hMc : tMove'? with
          | none => simp [hMc, optTrees] at htM
          | some tM =>
            simp only [hMc, optTrees, Option.toList_some, List.mem_singleton] at htM; subst htM
            have hrM_in : rMove ∈ s'.rf.R := by
              have hR : s'.rf.R = insert (if s'.rf.F.Connected v r then v' else v) s.rf.R := rfl
              dsimp only [rMove]; rw [hR]; split_ifs with hvr
              · exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem hr_spec.1
            exact Or.inl ⟨rMove, hrM_in, by simp [x', hMc]⟩
        · have ht'_old : t' ∈ x.trees := hperm_r.mem_iff.mpr (by simp [htR])
          rcases h.tree_class t' ht'_old with ⟨r', hr'R, hct'⟩ | ⟨u, htu, hno⟩
          · have hr'r : r' ≠ r := fun heq => hrest_no_t t' htR (Option.some.inj (by rw [← hct', heq, hct_r]))
            have hne1 : r' ≠ rKeep := by
              dsimp only [rKeep]; split_ifs with hvr
              · exact hr'r
              · intro heq; subst heq; exact hr'r (h.valid.root_eq_of_mem hvF hr'R (connected_refl _ _)).symm
            have hne2 : r' ≠ rMove := by
              dsimp only [rMove]; split_ifs with hvr
              · exact fun heq => hv'NotF (heq ▸ h.valid.roots_sub hr'R)
              · exact hr'r
            exact Or.inl ⟨r', Finset.mem_insert_of_mem hr'R,
              by simp [x', Function.update_of_ne hne2, Function.update_of_ne hne1, hct']⟩
          · exact Or.inr ⟨u, htu, fun w hw => by
              obtain ⟨w0, hw0⟩ := (hact_iff _).mp ⟨w, hw⟩; exact hno w0 hw0⟩
      inactive_single := fun u h1 h2 hno => by
        have hno0 : ∀ w, endOfKey (x.keyOf u) ∉ s.ord w := fun w hw => by
          obtain ⟨w1, hw1⟩ := (hact_iff _).mpr ⟨w, hw⟩; exact hno w1 hw1
        have hmem := h.inactive_single u h1 h2 hno0
        have hne_t : AuxTree.node u .leaf .leaf ≠ t := fun heq =>
          hmem_t_of_inact u hno0 (by rw [← heq]; simp [AuxTree.toList])
        have hrest : AuxTree.node u .leaf .leaf ∈ rest :=
          (List.mem_cons.mp (hperm_r.mem_iff.mp hmem)).resolve_left hne_t
        simp [x', hrest]
      val_active := hvalF_act
      val_inactive_rt := fun u h1 h2 hno => by
        have hno0 : ∀ w, endOfKey (x.keyOf u) ∉ s.ord w := fun w hw => by
          obtain ⟨w1, hw1⟩ := (hact_iff _).mpr ⟨w, hw⟩; exact hno w1 hw1
        rw [hvalF_oth u h2 (hmem_t_of_inact u hno0)]
        exact h.val_inactive_rt u h1 h2 hno0
      val_unused_rt := fun u hu hcase => by
        have hun : u ∉ t.toList := fun ht => by
          have := (h.nodes_exact u).mp (List.mem_flatMap.mpr ⟨t, hperm_r.mem_iff.mpr (by simp), ht⟩)
          dsimp only [x'] at hcase
          rcases hcase with rfl | hgt <;> omega
        rw [hvalF_oth u hu hun]; exact h.val_unused_rt u hu hcase }

end MinCostFlow.SparseCore.Program
