module

public import MinCostFlow.SparseCore.Program.TourOpsEditMovePost
import Mathlib.Tactic

/-!
# Post-split root-update helpers and Case 1 (`v ∈ s.rf.R`) for `moveEnds` (Op 0)

Verifies `tourMoveRootsStmt`: handles all three root cases (`v ∈ R`, `v ∉ R ∧ F'.Connected v r`,
and `v ∉ R ∧ ¬F'.Connected v r`), updating `isRoot`, `rootTag`, and rotating the surviving root
`r` back to the front of its tour in `O(tourLog eCap)` amortized time.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

theorem optRoot_mem_head_end {τ_ord : Type} {vCap eCap b w0 : ℕ}
    {s : TourAbs} {x : TourConcrete τ_ord} {mem : ℕ → ℕ}
    {s' : TourAbs} (hvalid' : TourValid vCap eCap s')
    (h : TourCoreAt vCap eCap b s x mem)
    {t : AuxTree} (ht_mem : t ∈ x.trees) {t0 : AuxTree}
    (ht0_ne : t0 ≠ .leaf)
    (hhd : (optList (some t0)).head?.getD 0 = optRoot (some t0))
    (hmap : (optList (some t0)).map (fun id => endOfKey (x.keyOf id)) =
      fullTour s'.ord s'.rf.F hvalid'.compat.forest w0)
    (hsub : ∀ u ∈ t0.toList, u ∈ t.toList) :
    (s'.ord w0).head? = some (endOfKey (x.keyOf t0.rootId)) ∧
    ∀ u ∈ t0.toList, u ≠ t0.rootId → endOfKey (x.keyOf u) ≠ endOfKey (x.keyOf t0.rootId) := by
  have htl_ne : t0.toList ≠ [] := by cases t0 <;> simp [AuxTree.toList] at ht0_ne ⊢
  obtain ⟨h0, hs, hcs⟩ := List.exists_cons_of_ne_nil htl_ne
  have hh0_eq : h0 = t0.rootId := by simpa [optList, optRoot, hcs] using hhd
  subst hh0_eq
  have hft_ne : fullTour s'.ord s'.rf.F hvalid'.compat.forest w0 ≠ [] := by
    rw [← hmap]; simp [optList, hcs]
  have hord_ne : s'.ord w0 ≠ [] := mt (fullTour_eq_nil_iff hvalid'.compat w0).mpr hft_ne
  obtain ⟨a, ha⟩ : ∃ a, (s'.ord w0).head? = some a :=
    Option.isSome_iff_exists.mp (by cases ho : s'.ord w0 <;> simp_all)
  have hft_hd := fullTour_head? hvalid'.compat w0 ha
  rw [← hmap] at hft_hd
  have ha_eq : endOfKey (x.keyOf t0.rootId) = a := by simpa [optList, hcs] using hft_hd
  refine ⟨by rw [ha, ha_eq], fun u hu hne heq => ?_⟩
  have hu1 := (h.nodes_exact u).mp (List.mem_flatMap.mpr ⟨t, ht_mem, hsub u hu⟩)
  have hr1 := (h.nodes_exact t0.rootId).mp (List.mem_flatMap.mpr ⟨t, ht_mem, hsub t0.rootId (by rw [hcs]; simp)⟩)
  have hkeq : x.keyOf u = x.keyOf t0.rootId := by rw [← endKey_endOfKey' (x.keyOf u), heq, endKey_endOfKey']
  exact hne (by rw [← (h.keyOf_mem u hu1.1 hu1.2).2.2, hkeq, (h.keyOf_mem t0.rootId hr1.1 hr1.2).2.2])

theorem rotateNatList_map_fullTour {τ_ord : Type} {vCap eCap b v0 r : ℕ}
    {s : TourAbs} {x : TourConcrete τ_ord} {mem : ℕ → ℕ}
    {s' : TourAbs} (hvalid' : TourValid vCap eCap s')
    (h : TourCoreAt vCap eCap b s x mem)
    {t : AuxTree} (ht_mem : t ∈ x.trees) {t0 : AuxTree} {feR : ℕ} {aR : End}
    (hmap : t0.toList.map (fun id => endOfKey (x.keyOf id)) =
      fullTour s'.ord s'.rf.F hvalid'.compat.forest v0)
    (hsub : ∀ u ∈ t0.toList, u ∈ t.toList)
    (hconn : s'.rf.F.Connected v0 r)
    (haR : (s'.ord r).head? = some aR)
    (hfeR_in : feR ∈ t0.toList) (hfeR_key : endOfKey (x.keyOf feR) = aR) :
    (rotateNatList feR t0.toList).map (fun id => endOfKey (x.keyOf id)) =
      fullTour s'.ord s'.rf.F hvalid'.compat.forest r := by
  have hinj : ∀ a ∈ t0.toList, ∀ b ∈ t0.toList,
      endOfKey (x.keyOf a) = endOfKey (x.keyOf b) → a = b := by
    intro a ha b hb hab
    have ha' := (h.nodes_exact a).mp (List.mem_flatMap.mpr ⟨t, ht_mem, hsub a ha⟩)
    have hb' := (h.nodes_exact b).mp (List.mem_flatMap.mpr ⟨t, ht_mem, hsub b hb⟩)
    have hka : x.keyOf a = x.keyOf b := by rw [← endKey_endOfKey' (x.keyOf a), hab, endKey_endOfKey']
    rw [← (h.keyOf_mem a ha'.1 ha'.2).2.2, hka, (h.keyOf_mem b hb'.1 hb'.2).2.2]
  have hidx : (t0.toList.map fun id => endOfKey (x.keyOf id)).idxOf aR = t0.toList.idxOf feR := by
    rw [← hfeR_key]
    clear * - hinj hfeR_in
    generalize t0.toList = ls at hinj hfeR_in ⊢
    induction ls with
    | nil => simp at hfeR_in
    | cons z zs ih =>
      by_cases hzf : z = feR
      · subst hzf; simp
      · have hne : endOfKey (x.keyOf z) ≠ endOfKey (x.keyOf feR) :=
          fun heq => hzf (hinj z (by simp) feR hfeR_in heq)
        have hfzs : feR ∈ zs := (List.mem_cons.mp hfeR_in).resolve_left (Ne.symm hzf)
        simp [List.idxOf_cons_ne _ hzf, List.idxOf_cons_ne _ hne,
          ih (fun a ha b hb => hinj a (by simp [ha]) b (by simp [hb])) hfzs]
  have ham : aR ∈ t0.toList.map (fun id => endOfKey (x.keyOf id)) :=
    List.mem_map.mpr ⟨feR, hfeR_in, hfeR_key⟩
  have hrot_m : (rotateNatList feR t0.toList).map (fun id => endOfKey (x.keyOf id)) =
      rotateToList aR (t0.toList.map fun id => endOfKey (x.keyOf id)) := by
    simp [rotateNatList, rotateToList, hfeR_in, ham, hidx, List.map_append, List.map_drop, List.map_take]
  rw [hrot_m, hmap]
  exact tour_rotateToList_eq_of_isRotated (fullTour_spec hvalid'.compat r).1
    (fullTour_isRotated_of_connected hvalid'.compat hconn) (fullTour_head? hvalid'.compat r haR)

open Classical in
/-- Execute `tourMoveRootsStmt`: handles all three root cases (`v ∈ R`, `v ∉ R ∧ F'.Connected v r`,
and `v ∉ R ∧ ¬F'.Connected v r`), updating `isRoot`, `rootTag`, and rotating the surviving root
`r` back to the front of its tour in `O(tourLog eCap)` amortized time. -/
theorem tourMoveRoots_case1 {τ_ord : Type}
    {w vCap eCap b v v' hOut : ℕ} {sel : Finset End} {c : Bool} {p : Program}
    (C : TourSplayQueryProcs w p) (ω : ℕ → Bool)
    {s : TourAbs} {x : TourConcrete τ_ord} {mem : ℕ → ℕ} {st0 : State}
    {sT : SplayState TourVal TourSum Unit} {t : AuxTree} {tKeep? tMove? : Option AuxTree}
    {rest : List AuxTree}
    (h : TourCoreAt vCap eCap b s x mem)
    (he : TourEditValid vCap eCap s (.moveEnds v v' sel c))
    (ht_mem : t ∈ x.trees)
    (ht_map : t.toList.map (fun id => endOfKey (x.keyOf id)) =
      fullTour s.ord s.rf.F h.valid.compat.forest (s.rf.root v))
    (hhdr0 : TourHeaderAt vCap eCap b x.numNodes st0.mem)
    (hfe0 : ∀ u < vCap, st0.mem (firstEndBase b + u) =
      match ((tourApplyEdit s (.moveEnds v v' sel c)).ord u).head? with
      | none => 0 | some e => x.nodeOf (endKey e))
    (hir0 : ∀ u < vCap, st0.mem (isRootBase b vCap + u) = if u ∈ s.rf.R then 1 else 0)
    (hn0 : tourLayout.NodesAt st0.mem (nodesBase b vCap eCap) x.numNodes sT)
    (hinv0 : TourForestInv x.numNodes sT (optTrees tKeep? ++ optTrees tMove? ++ rest))
    (hvals0 : TourValsOk w x.numNodes sT)
    (hhdK : (optList tKeep?).head?.getD 0 = optRoot tKeep?)
    (hhdM : (optList tMove?).head?.getD 0 = optRoot tMove?)
    (hperm : (optList tKeep? ++ optList tMove?).Perm t.toList)
    (hKeep_map : (optList tKeep?).map (fun id => endOfKey (x.keyOf id)) =
      fullTour (tourApplyEdit s (.moveEnds v v' sel c)).ord
        (tourApplyEdit s (.moveEnds v v' sel c)).rf.F
        (tourValid_applyEdit_moveEnds h.valid he).compat.forest v)
    (hMove_map : (optList tMove?).map (fun id => endOfKey (x.keyOf id)) =
      fullTour (tourApplyEdit s (.moveEnds v v' sel c)).ord
        (tourApplyEdit s (.moveEnds v v' sel c)).rf.F
        (tourValid_applyEdit_moveEnds h.valid he).compat.forest v')
    (hval_in : v ∈ s.rf.R → ∀ u ≤ x.numNodes,
      (u ∈ t.toList → (sT.nodes u).val = { (x.st.nodes u).val with rootTag := 0 }) ∧
      (u ∉ t.toList → (sT.nodes u).val = (x.st.nodes u).val))
    (hval_out : v ∉ s.rf.R → ∀ u ≤ x.numNodes, (sT.nodes u).val = (x.st.nodes u).val)
    (hr0 : st0.regs 0 = b) (hr4 : st0.regs 4 = v) (hr5 : st0.regs 5 = v')
    (hr9 : st0.regs 9 = nodesBase b vCap eCap) (hr10 : st0.regs 10 = 2 * eCap + 2)
    (hr11 : st0.regs 11 = if v ∈ s.rf.R then 1 else 0)
    (hr15 : st0.regs 15 = hOut)
    (hr16 : st0.regs 16 = optRoot tKeep?) (hr17 : st0.regs 17 = optRoot tMove?)
    (hord_le : ordHandleOf b vCap eCap ≤ hOut)
    (hroom : hOut + 2 < 2 ^ w) (hw : vCap + 2 * eCap + 4 < 2 ^ w) (hwide : 18 ≤ 2 ^ w)
    (hzero : ZeroFrom st0.mem hOut) (hvR : v ∈ s.rf.R) :
    let s' := tourApplyEdit s (.moveEnds v v' sel c)
    let r := s.rf.root v
    let rKeep := if s'.rf.F.Connected v r then r else v
    let rMove := if s'.rf.F.Connected v r then v' else r
    ∃ tKeep'? tMove'? sF stF cost,
      Runs w p ω (tourMoveRootsStmt C.setValNode C.rotateFront) st0 .normal stF cost ∧
      stF.regs 15 = hOut ∧
      tourLayout.NodesAt stF.mem (nodesBase b vCap eCap) x.numNodes sF ∧
      ZeroFrom stF.mem hOut ∧
      (∀ a < hOut, ¬tourLayout.InRecords (nodesBase b vCap eCap) x.numNodes a →
        a ≠ isRootBase b vCap + v → a ≠ isRootBase b vCap + v' → stF.mem a = st0.mem a) ∧
      (∀ u < vCap, stF.mem (isRootBase b vCap + u) = if u ∈ s'.rf.R then 1 else 0) ∧
      TourForestInv x.numNodes sF (optTrees tKeep'? ++ optTrees tMove'? ++ rest) ∧
      (optList tKeep'? ++ optList tMove'?).Perm t.toList ∧
      (optList tKeep'?).map (fun id => endOfKey (x.keyOf id)) =
        fullTour s'.ord s'.rf.F (tourValid_applyEdit_moveEnds h.valid he).compat.forest rKeep ∧
      (optList tMove'?).map (fun id => endOfKey (x.keyOf id)) =
        fullTour s'.ord s'.rf.F (tourValid_applyEdit_moveEnds h.valid he).compat.forest rMove ∧
      (∀ u, 1 ≤ u → u ≤ x.numNodes → (∃ w', endOfKey (x.keyOf u) ∈ s'.ord w') →
        (sF.nodes u).val =
          { isOpen := decide ((endOfKey (x.keyOf u)).1 ∉ s'.rf.F.E)
            isMarked := decide (endOfKey (x.keyOf u) ∈ s'.marked)
            rootTag := tourRootTagVal s' (endOfKey (x.keyOf u)) }) ∧
      (∀ u ≤ x.numNodes, u ∉ t.toList → (sF.nodes u).val = (x.st.nodes u).val) ∧
      cost + TOUR_PHI_MULT * forestPhi (optTrees tKeep'? ++ optTrees tMove'? ++ rest) ≤
        TOUR_PHI_MULT * forestPhi (optTrees tKeep? ++ optTrees tMove? ++ rest) +
          (TOUR_SEQ_AMORT + 2 * TOUR_FIND_AMORT) * (Nat.log 2 (x.numNodes + 2) + 1) + 200 := by
  intro s' r rKeep rMove
  rcases he with ⟨hvLt, hv'Lt, hne, hvF, hv'NotF, hord_v', hsel⟩
  have hvalid' := tourValid_applyEdit_moveEnds (c := c) h.valid ⟨hvLt, hv'Lt, hne, hvF, hv'NotF, hord_v', hsel⟩
  have hr_spec := h.valid.root_spec hvF
  have hrLt : r < vCap := h.valid.verts_lt r (h.valid.roots_sub hr_spec.1)
  have hb_lt : b + 16 < 2 ^ w := by simp [ordHandleOf, tourFixedSize] at hord_le; omega
  have hrec_le : tourLayout.nodeAddr (nodesBase b vCap eCap) (x.numNodes + 1) ≤ hOut := by
    have := h.numNodes_le; simp [NodeLayout.nodeAddr, tourLayout_stride, nodesBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega
  have hFE : s'.rf.F.E = s.rf.F.E := rfl
  have hmk : s'.marked = s.marked := rfl
  -- Load `isRootBase` into `r18`
  set r1 := Function.update st0.regs 18 (isRootBase b vCap)
  have ha18 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 18) (rBase := 0) (off := HDR_IS_ROOT)
    (b := b) (val := isRootBase b vCap) (st := st0) hr0
    (by simp [HDR_IS_ROOT]; omega) (by simp [HDR_IS_ROOT]; omega) hhdr0.2.2.2.2.2.1
  -- Active-end and outside-`t` rootTag helpers
  have hact_to_old : ∀ z, (∃ w', z ∈ s'.ord w') → ∃ w', z ∈ s.ord w' := by
    rintro z ⟨w', hw'⟩
    by_cases h1 : w' = v
    · subst h1; simp only [s', tourApplyEdit, applyOrdEdit, ↓reduceIte, List.mem_filter] at hw'; exact ⟨w', hw'.1⟩
    · by_cases h2 : w' = v'
      · subst h2; simp only [s', tourApplyEdit, applyOrdEdit, hne.symm, ↓reduceIte, hord_v', List.nil_append, List.mem_filter] at hw'
        exact ⟨v, hw'.1⟩
      · simp only [s', tourApplyEdit, applyOrdEdit, h1, h2, ↓reduceIte] at hw'; exact ⟨w', hw'⟩
  have hrt_outside : ∀ u, 1 ≤ u → u ≤ x.numNodes → u ∉ t.toList →
      (∃ w', endOfKey (x.keyOf u) ∈ s'.ord w') →
      tourRootTagVal s' (endOfKey (x.keyOf u)) = tourRootTagVal s (endOfKey (x.keyOf u)) := by
    intro u h1 h2 hu_nt ⟨w', hw'⟩
    have hmem_t_of : ∀ z ∈ s.ord v, z = endOfKey (x.keyOf u) → False := fun z hzv hze => hu_nt (by
      have hft : endOfKey (x.keyOf u) ∈ fullTour s.ord s.rf.F h.valid.compat.forest r :=
        ((fullTour_spec h.valid.compat r).2 _).mpr ⟨v, hze ▸ hzv, connected_symm hr_spec.2⟩
      rw [← ht_map] at hft; obtain ⟨u', hu', hke⟩ := List.mem_map.mp hft
      have hu'in := (h.nodes_exact u').mp (List.mem_flatMap.mpr ⟨t, ht_mem, hu'⟩)
      have hkeq : x.keyOf u' = x.keyOf u := by rw [← endKey_endOfKey' (x.keyOf u'), hke, endKey_endOfKey']
      have hequ : u' = u := by rw [← (h.keyOf_mem u' hu'in.1 hu'in.2).2.2, hkeq, (h.keyOf_mem u h1 h2).2.2]
      exact hequ ▸ hu')
    have hne_v : w' ≠ v := fun heq => by
      subst heq; simp only [s', tourApplyEdit, applyOrdEdit, ↓reduceIte, List.mem_filter] at hw'
      exact hmem_t_of _ hw'.1 rfl
    have hne_v' : w' ≠ v' := fun heq => by
      subst heq; simp only [s', tourApplyEdit, applyOrdEdit, hne.symm, ↓reduceIte, hord_v', List.nil_append, List.mem_filter] at hw'
      exact hmem_t_of _ hw'.1 rfl
    have hw'0 : endOfKey (x.keyOf u) ∈ s.ord w' := by simpa [s', tourApplyEdit, applyOrdEdit, hne_v, hne_v'] using hw'
    have hord_w' : s'.ord w' = s.ord w' := by simp [s', tourApplyEdit, applyOrdEdit, hne_v, hne_v']
    have hR_w' : w' ∈ s'.rf.R ↔ w' ∈ s.rf.R := by
      simp only [s', tourApplyEdit, Finset.mem_insert]
      exact ⟨fun h0 => h0.elim (fun hnew => by split_ifs at hnew <;> simp_all) id, Or.inr⟩
    by_cases hwR : w' ∈ s.rf.R ∧ (s.ord w').head? = some (endOfKey (x.keyOf u))
    · rw [tourRootTagVal_eq_succ h.valid hwR.1 hwR.2,
          tourRootTagVal_eq_succ hvalid' (hR_w'.mpr hwR.1) (by rw [hord_w']; exact hwR.2)]
    · have hz1 : tourRootTagVal s' (endOfKey (x.keyOf u)) = 0 :=
        tourRootTagVal_eq_zero (fun r' hr' hh => hwR ⟨hR_w'.mp (by rwa [hvalid'.compat.unique r' w' _ (List.mem_of_head? hh) hw'] at hr'),
          by rw [← hord_w']; rwa [hvalid'.compat.unique r' w' _ (List.mem_of_head? hh) hw'] at hh⟩)
      have hz2 : tourRootTagVal s (endOfKey (x.keyOf u)) = 0 :=
        tourRootTagVal_eq_zero (fun r' hr' hh => hwR ⟨by rwa [h.valid.compat.unique r' w' _ (List.mem_of_head? hh) hw'0] at hr',
          by rwa [h.valid.compat.unique r' w' _ (List.mem_of_head? hh) hw'0] at hh⟩)
      rw [hz1, hz2]
  have hsubK : ∀ u ∈ optList tKeep?, u ∈ t.toList := fun u hu => hperm.mem_iff.mp (List.mem_append_left _ hu)
  have hsubM : ∀ u ∈ optList tMove?, u ∈ t.toList := fun u hu => hperm.mem_iff.mp (List.mem_append_right _ hu)
  have hdisj_KM : ∀ u ∈ optList tKeep?, u ∉ optList tMove? := by
    have hnd : (optList tKeep? ++ optList tMove?).Nodup := hperm.nodup_iff.mpr (h.forestInv.treesInv t ht_mem).nodup
    exact fun u hu hm => (List.nodup_append.mp hnd).2.2 u hu u hm rfl
  -- Case 1: `v ∈ s.rf.R`.
  have hrv : r = v := h.valid.root_eq_of_mem hvF hvR (connected_refl _ _)
  have hvr : s'.rf.F.Connected v r := hrv ▸ connected_refl _ _
  have hrK_eq : rKeep = v := by simp [rKeep, hrv]
  have hrM_eq : rMove = v' := by simp [rMove, hvr]
  have hR_eq : s'.rf.R = insert v' s.rf.R := by
    change insert (if s'.rf.F.Connected v r then v' else v) s.rf.R = _; simp [hvr]
  have hcond1 : (Expr.reg 11).eval w { st0 with regs := r1 } = some 1 := by
    simp [Expr.eval, r1, hr11, hvR]
  set mem1 := Function.update st0.mem (isRootBase b vCap + v') 1
  have hst_ir : Runs w p ω (.store (.bin .add (.reg 18) (.reg 5)) (.const 1))
      { st0 with regs := r1 } .normal { st0 with mem := mem1, regs := r1 } 5 :=
    runs_store_iff.mpr ⟨isRootBase b vCap + v', 1,
      by simp [Expr.eval, r1, hr5, BinOp.eval,
        (by simp [isRootBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega : isRootBase b vCap + v' < 2 ^ w)],
      by simp [Expr.eval, (by omega : 1 < 2 ^ w)], rfl, rfl, rfl⟩
  have hn1 : tourLayout.NodesAt mem1 (nodesBase b vCap eCap) x.numNodes sT :=
    NodesAt.congr tourLayout hn0 fun a ha => by
      dsimp only [mem1]; exact Function.update_of_ne (by have := (inRecords_lt_ordHandle_of_le h.numNodes_le ha).1; simp [isRootBase, nodesBase] at this ⊢; omega) _ _
  have hz1 : ZeroFrom mem1 hOut := fun a ha => by
    dsimp only [mem1]; rw [Function.update_of_ne (by simp [isRootBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)]
    exact hzero a ha
  have hinv_K : TourForestInv x.numNodes sT (optTrees tKeep? ++ (optTrees tMove? ++ rest)) := by
    simpa [List.append_assoc] using hinv0
  obtain ⟨tKeep'?, s1, st1, c1, hrun1, hr1_lt, hn1', hfr1, hinv1, hvals1, hlist1, hval1N, hval1S, hc1⟩ :=
    setRootTagIfNz_runs (fuel := 2 * eCap + 2) (rNode := 16) (rVert := 4) (vert := v) (st := { st0 with mem := mem1, regs := r1 })
      C ω (by omega) (by omega) (by simp [r1, hr16]) (by simp [r1, hr4]) (by simp [r1, hr9])
      (by simp [r1, hr10]) (by simp [r1, hr15]) hn1 hinv_K hvals0 (by omega) (by have := h.numNodes_le; omega) (by omega)
      ⟨hrec_le, hroom, hz1, by omega⟩
  have hperm1 : (optTrees tKeep'? ++ (optTrees tMove? ++ rest)).Perm
      (optTrees tMove? ++ (optTrees tKeep'? ++ rest)) := by
    simpa [List.append_assoc] using (List.perm_append_comm (l₁ := optTrees tKeep'?) (l₂ := optTrees tMove?)).append_right rest
  obtain ⟨tMove'?, s2, st2, c2, hrun2, hr2_lt, hn2', hfr2, hinv2, hvals2, hlist2, hval2N, hval2S, hc2⟩ :=
    setRootTagIfNz_runs (fuel := 2 * eCap + 2) (rNode := 17) (rVert := 5) (vert := v') (st := st1)
      C ω (by omega) (by omega) (by rw [hr1_lt 17 (by omega)]; simp [r1, hr17])
      (by rw [hr1_lt 5 (by omega)]; simp [r1, hr5]) (by rw [hr1_lt 9 (by omega)]; simp [r1, hr9])
      (by rw [hr1_lt 10 (by omega)]; simp [r1, hr10]) (by rw [hr1_lt 15 (by omega)]; simp [r1, hr15])
      hn1' (hinv1.perm hperm1).1 hvals1 (by omega) (by have := h.numNodes_le; omega) (by omega)
      ⟨hrec_le, hroom, hfr1.1, by omega⟩
  have hperm2 : (optTrees tMove'? ++ (optTrees tKeep'? ++ rest)).Perm
      (optTrees tKeep'? ++ optTrees tMove'? ++ rest) := by
    simpa [List.append_assoc] using (List.perm_append_comm (l₁ := optTrees tMove'?) (l₂ := optTrees tKeep'?)).append_right rest
  have hfr12 := hfr1.trans hfr2
  have hval_final : ∀ u, 1 ≤ u → u ≤ x.numNodes → (∃ w', endOfKey (x.keyOf u) ∈ s'.ord w') →
      (s2.nodes u).val =
        { isOpen := decide ((endOfKey (x.keyOf u)).1 ∉ s'.rf.F.E)
          isMarked := decide (endOfKey (x.keyOf u) ∈ s'.marked)
          rootTag := tourRootTagVal s' (endOfKey (x.keyOf u)) } := by
    intro u hu1 hu2 hact
    have hcap : u ≤ x.numNodes := hu2
    have hval_old := h.val_active u hu1 hu2 (hact_to_old _ hact)
    by_cases hut : u ∈ t.toList
    · have hzero_u := (hval_in hvR u hcap).1 hut
      have hkm : u ∈ optList tKeep? ∨ u ∈ optList tMove? := List.mem_append.mp (hperm.mem_iff.mpr hut)
      rcases hkm with huK | huM
      · have hu_nM : u ∉ optList tMove? := hdisj_KM u huK
        have hv2_eq : (s2.nodes u).val = (s1.nodes u).val := by
          cases hMc : tMove? with
          | none => exact hval2N hMc u hcap
          | some tM =>
            have hval2 := hval2S tM hMc; simp only [hMc] at hu_nM
            have hne_r : u ≠ tM.rootId := fun heq => hu_nM (by
              have hne_tM := hinv0.nonEmpty tM (by simp [hMc, optTrees])
              simpa [optList] using heq ▸ AuxTree.rootId_mem hne_tM)
            exact hval2.2 u hcap hne_r
        cases hKc : tKeep? with
        | none => simp [hKc, optList] at huK
        | some tK =>
          have hval1 := hval1S tK hKc; rw [hKc] at huK hhdK hKeep_map
          have hne_tK : tK ≠ .leaf := hinv0.nonEmpty tK (by simp [hKc, optTrees])
          obtain ⟨hhd_v, hne_hd_v⟩ := optRoot_mem_head_end hvalid' h ht_mem hne_tK hhdK hKeep_map
            (fun z hz => hsubK z (by simpa [hKc, optList] using hz))
          rw [hv2_eq]
          by_cases hur : u = tK.rootId
          · subst hur
            rw [hval1.1, hzero_u, hval_old]
            rw [tourRootTagVal_eq_succ hvalid' (hR_eq ▸ Finset.mem_insert_of_mem hvR) hhd_v]; simp only [hFE, hmk]
          · rw [hval1.2 u hcap hur, hzero_u, hval_old]
            have hrt0 : tourRootTagVal s' (endOfKey (x.keyOf u)) = 0 := by
              apply tourRootTagVal_eq_zero; intro r' hr' hh
              have hfu : endOfKey (x.keyOf u) ∈ fullTour s'.ord s'.rf.F hvalid'.compat.forest v := by
                rw [← hKeep_map]; exact List.mem_map_of_mem huK
              obtain ⟨w1, hw1, hvw1⟩ := ((fullTour_spec hvalid'.compat v).2 _).mp hfu
              have hw1r' : w1 = r' := hvalid'.compat.unique w1 r' _ hw1 (List.mem_of_head? hh)
              rw [hw1r'] at hvw1
              have hr'v : r' = v := (hvalid'.unique_root v (Finset.mem_insert_of_mem hvF)).unique
                ⟨hr', hvw1⟩ ⟨hR_eq ▸ Finset.mem_insert_of_mem hvR, connected_refl _ _⟩
              rw [hr'v, hhd_v] at hh
              exact hne_hd_v u (by simpa [optList] using huK) hur (Option.some.inj hh).symm
            simp only [hFE, hmk, hrt0]
      · have hu_nK : u ∉ optList tKeep? := fun hk => hdisj_KM u hk huM
        have hv1_eq : (s1.nodes u).val = (sT.nodes u).val := by
          cases hKc : tKeep? with
          | none => exact hval1N hKc u hcap
          | some tK =>
            have hval1 := hval1S tK hKc; simp only [hKc] at hu_nK
            have hne_r : u ≠ tK.rootId := fun heq => hu_nK (by
              have hne_tK := hinv0.nonEmpty tK (by simp [hKc, optTrees])
              simpa [optList] using heq ▸ AuxTree.rootId_mem hne_tK)
            exact hval1.2 u hcap hne_r
        cases hMc : tMove? with
        | none => simp [hMc, optList] at huM
        | some tM =>
          have hval2 := hval2S tM hMc; rw [hMc] at huM hhdM hMove_map
          have hne_tM : tM ≠ .leaf := hinv0.nonEmpty tM (by simp [hMc, optTrees])
          obtain ⟨hhd_v', hne_hd_v'⟩ := optRoot_mem_head_end hvalid' h ht_mem hne_tM hhdM hMove_map
            (fun z hz => hsubM z (by simpa [hMc, optList] using hz))
          by_cases hur : u = tM.rootId
          · subst hur
            rw [hval2.1, hv1_eq, hzero_u, hval_old]
            rw [tourRootTagVal_eq_succ hvalid' (hR_eq ▸ Finset.mem_insert_self v' _) hhd_v']; simp only [hFE, hmk]
          · rw [hval2.2 u hcap hur, hv1_eq, hzero_u, hval_old]
            have hrt0 : tourRootTagVal s' (endOfKey (x.keyOf u)) = 0 := by
              apply tourRootTagVal_eq_zero; intro r' hr' hh
              have hfu : endOfKey (x.keyOf u) ∈ fullTour s'.ord s'.rf.F hvalid'.compat.forest v' := by
                rw [← hMove_map]; exact List.mem_map_of_mem huM
              obtain ⟨w1, hw1, hvw1⟩ := ((fullTour_spec hvalid'.compat v').2 _).mp hfu
              have hw1r' : w1 = r' := hvalid'.compat.unique w1 r' _ hw1 (List.mem_of_head? hh)
              rw [hw1r'] at hvw1
              have hr'v' : r' = v' := (hvalid'.unique_root v' (Finset.mem_insert_self v' _)).unique
                ⟨hr', hvw1⟩ ⟨hR_eq ▸ Finset.mem_insert_self v' _, connected_refl _ _⟩
              rw [hr'v', hhd_v'] at hh
              exact hne_hd_v' u (by simpa [optList] using huM) hur (Option.some.inj hh).symm
            simp only [hFE, hmk, hrt0]
    · have hv_nt : (s2.nodes u).val = (x.st.nodes u).val := by
        have hv2' : (s2.nodes u).val = (s1.nodes u).val := by
          cases hMc : tMove? with
          | none => exact hval2N hMc u hcap
          | some tM =>
            have hval2 := hval2S tM hMc
            have hne_r : u ≠ tM.rootId := fun heq => hut (hsubM u (by
              have hne_tM := hinv0.nonEmpty tM (by simp [hMc, optTrees])
              simpa [hMc, optList] using heq ▸ AuxTree.rootId_mem hne_tM))
            exact hval2.2 u hcap hne_r
        have hv1' : (s1.nodes u).val = (sT.nodes u).val := by
          cases hKc : tKeep? with
          | none => exact hval1N hKc u hcap
          | some tK =>
            have hval1 := hval1S tK hKc
            have hne_r : u ≠ tK.rootId := fun heq => hut (hsubK u (by
              have hne_tK := hinv0.nonEmpty tK (by simp [hKc, optTrees])
              simpa [hKc, optList] using heq ▸ AuxTree.rootId_mem hne_tK))
            exact hval1.2 u hcap hne_r
        rw [hv2', hv1', (hval_in hvR u hcap).2 hut]
      rw [hv_nt, hval_old, hrt_outside u hu1 hu2 hut hact, hFE, hmk]
  have hval_oth : ∀ u ≤ x.numNodes, u ∉ t.toList → (s2.nodes u).val = (x.st.nodes u).val := by
    intro u hcap hut
    have hv2' : (s2.nodes u).val = (s1.nodes u).val := by
      cases hMc : tMove? with
      | none => exact hval2N hMc u hcap
      | some tM =>
        have hval2 := hval2S tM hMc
        have hne_r : u ≠ tM.rootId := fun heq => hut (hsubM u (by
          have hne_tM := hinv0.nonEmpty tM (by simp [hMc, optTrees])
          simpa [hMc, optList] using heq ▸ AuxTree.rootId_mem hne_tM))
        exact hval2.2 u hcap hne_r
    have hv1' : (s1.nodes u).val = (sT.nodes u).val := by
      cases hKc : tKeep? with
      | none => exact hval1N hKc u hcap
      | some tK =>
        have hval1 := hval1S tK hKc
        have hne_r : u ≠ tK.rootId := fun heq => hut (hsubK u (by
          have hne_tK := hinv0.nonEmpty tK (by simp [hKc, optTrees])
          simpa [hKc, optList] using heq ▸ AuxTree.rootId_mem hne_tK))
        exact hval1.2 u hcap hne_r
    rw [hv2', hv1', (hval_in hvR u hcap).2 hut]
  refine ⟨tKeep'?, tMove'?, s2, st2, _,
    tour_runs_seq_normal ha18 (tour_runs_cond_true hcond1 (by omega)
      (tour_runs_seq_normal hst_ir (tour_runs_seq_normal hrun1 hrun2))),
    by rw [hr2_lt 15 (by omega), hr1_lt 15 (by omega)]; simp [r1, hr15],
    hn2', hfr12.1,
    fun a ha hnr h1 h2 => by
      rw [hfr12.2 a ha hnr]; dsimp only [mem1]; exact Function.update_of_ne h2 _ _,
    fun u hu => by
      rw [hfr12.2 _ (by simp [isRootBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)
        (not_inRecords_of_lt_nodesBase (by simp [isRootBase, nodesBase]; omega))]
      dsimp only [mem1]; by_cases huv' : u = v'
      · subst huv'; simp [hR_eq]
      · rw [Function.update_of_ne (by omega), hir0 u hu, hR_eq]; simp [huv'],
    (hinv2.perm hperm2).1, by rwa [hlist1, hlist2],
    by rw [hrK_eq, hlist1]; exact hKeep_map, by rw [hrM_eq, hlist2]; exact hMove_map,
    hval_final, hval_oth, ?_⟩
  have hpeq0 : forestPhi (optTrees tKeep? ++ (optTrees tMove? ++ rest)) =
      forestPhi (optTrees tKeep? ++ optTrees tMove? ++ rest) := by simp [List.append_assoc]
  have hpeq1 := forestPhi_perm hperm1
  have hpeq2 := forestPhi_perm hperm2
  rw [← hpeq2]; rw [← hpeq1] at hc2; rw [hpeq0] at hc1
  have hlog1 : 1 ≤ Nat.log 2 (x.numNodes + 2) + 1 := by omega
  clear * - hc1 hc2 hlog1; simp only [Expr.size, TOUR_FIND_AMORT, TOUR_SEQ_AMORT] at *; omega

end MinCostFlow.SparseCore.Program
