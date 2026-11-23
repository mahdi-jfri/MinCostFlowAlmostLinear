module

public import MinCostFlow.SparseCore.Program.TourOpsEditMoveRootsCase1
import Mathlib.Tactic

/-!
# Post-split root-update verification (`tourMoveRoots_exec`) for `moveEnds` (Op 0)

Verifies `tourMoveRootsStmt`: delegates Case 1 (`v ∈ R`) to `tourMoveRoots_case1` and handles
Case 2 (`v ∉ R`, both `F'.Connected v r` and `¬F'.Connected v r`), updating `isRoot`, `rootTag`,
and rotating the surviving root `r` back to the front of its tour in `O(tourLog eCap)` amortized time.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

open Classical in
/-- Execute `tourMoveRootsStmt`: handles all three root cases (`v ∈ R`, `v ∉ R ∧ F'.Connected v r`,
and `v ∉ R ∧ ¬F'.Connected v r`), updating `isRoot`, `rootTag`, and rotating the surviving root
`r` back to the front of its tour in `O(tourLog eCap)` amortized time. -/
theorem tourMoveRoots_exec {τ_ord : Type}
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
    (hzero : ZeroFrom st0.mem hOut) :
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
  by_cases hvR : v ∈ s.rf.R
  · exact tourMoveRoots_case1 C ω h ⟨hvLt, hv'Lt, hne, hvF, hv'NotF, hord_v', hsel⟩ ht_mem ht_map
      hhdr0 hfe0 hir0 hn0 hinv0 hvals0 hhdK hhdM
      hperm hKeep_map hMove_map hval_in hval_out hr0 hr4 hr5 hr9 hr10 hr11 hr15 hr16 hr17
      hord_le hroom hw hwide hzero hvR
  · -- Case 2: `v ∉ s.rf.R`.
    have hcond1 : (Expr.reg 11).eval w { st0 with regs := r1 } = some 0 := by
      simp [Expr.eval, r1, hr11, hvR]
    have hr_ne_v : r ≠ v := fun heq => hvR (heq ▸ hr_spec.1)
    have hr_ne_v' : r ≠ v' := fun heq => hv'NotF (heq ▸ h.valid.roots_sub hr_spec.1)
    have hord_r_eq : s'.ord r = s.ord r := by simp [s', tourApplyEdit, applyOrdEdit, hr_ne_v, hr_ne_v']
    have hord_r_ne : s.ord r ≠ [] := by
      obtain ⟨e, heF, hsrc⟩ := exists_edge_of_connected_ne (connected_symm hr_spec.2) hr_ne_v
      exact List.ne_nil_of_mem (hsrc ▸ h.valid.compat.mem_ord_of_forest heF)
    obtain ⟨aR, haR⟩ : ∃ aR, (s.ord r).head? = some aR :=
      Option.isSome_iff_exists.mp (by cases ho : s.ord r <;> simp_all)
    have haR' : (s'.ord r).head? = some aR := by rw [hord_r_eq]; exact haR
    have hfeR_mem : st0.mem (firstEndBase b + r) = x.nodeOf (endKey aR) := by
      rw [hfe0 r hrLt, haR']
    set feR := x.nodeOf (endKey aR)
    have hfeR_key : endOfKey (x.keyOf feR) = aR := by
      have haLt : endKey aR < 2 * eCap := key_lt_two_mul_of_endOfKey (by simpa [endOfKey_endKey] using h.valid.ordWithin.2.2 r aR (List.mem_of_head? haR))
      rw [h.nodeOf_keyOf _ haLt (h.active_end r hrLt aR (List.mem_of_head? haR)).1, endOfKey_endKey]
    have hfeR_in_of : ∀ (opt : Option AuxTree) (w0 : ℕ),
        (optList opt).map (fun id => endOfKey (x.keyOf id)) = fullTour s'.ord s'.rf.F hvalid'.compat.forest w0 →
        (∀ u ∈ optList opt, u ∈ t.toList) → s'.rf.F.Connected w0 r → feR ∈ optList opt := by
      intro opt w0 hmap hsub hcw
      have hft : aR ∈ fullTour s'.ord s'.rf.F hvalid'.compat.forest w0 :=
        ((fullTour_spec hvalid'.compat w0).2 aR).mpr ⟨r, List.mem_of_head? haR', hcw⟩
      rw [← hmap] at hft; obtain ⟨u, hu, hue⟩ := List.mem_map.mp hft
      have hu1 := (h.nodes_exact u).mp (List.mem_flatMap.mpr ⟨t, ht_mem, hsub u hu⟩)
      have hkeq : x.keyOf u = endKey aR := by rw [← hue, endKey_endOfKey']
      have hequ : u = feR := by dsimp only [feR]; rw [← hkeq, (h.keyOf_mem u hu1.1 hu1.2).2.2]
      exact hequ ▸ hu
    -- Execute `rtKeep := if feKeep == 0 then 0 else mem[nb + 17 * feKeep + 15]` into `r19`
    set rtKeep := if optRoot tKeep? = 0 then 0 else st0.mem (nodesBase b vCap eCap + 17 * optRoot tKeep? + 15)
    set r2 := Function.update r1 19 rtKeep
    have hrun_rtK : ∃ cRt, cRt ≤ 15 ∧
        Runs w p ω (.cond (.bin .eq (.reg 16) (.const 0)) (.assign 19 (.const 0))
          (.assign 19 (.load (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 17) (.reg 16))) (.const 15)))))
          { st0 with regs := r1 } .normal { st0 with regs := r2 } cRt := by
      by_cases hK0 : optRoot tKeep? = 0
      · have hc : (Expr.bin .eq (.reg 16) (.const 0)).eval w { st0 with regs := r1 } = some 1 := by
          simp [Expr.eval, r1, hr16, hK0, BinOp.eval, (by omega : 0 < 2 ^ w), (by omega : 1 < 2 ^ w)]
        have ha : Runs w p ω (.assign 19 (.const 0)) { st0 with regs := r1 } .normal { st0 with regs := r2 } 2 :=
          runs_assign_iff.mpr ⟨0, by simp [Expr.eval, (by omega : 0 < 2 ^ w)], rfl,
            by congr 1; funext k; by_cases hk : k = 19 <;> simp [r2, rtKeep, hK0, hk], rfl⟩
        exact ⟨_, by simp [Expr.size], tour_runs_cond_true hc (by omega) ha⟩
      · have hc : (Expr.bin .eq (.reg 16) (.const 0)).eval w { st0 with regs := r1 } = some 0 := by
          simp [Expr.eval, r1, hr16, hK0, BinOp.eval, (by omega : 0 < 2 ^ w)]
        have hK_cap : optRoot tKeep? ≤ x.numNodes := by
          cases hKc : tKeep? with
          | none => simp [hKc, optRoot] at hK0
          | some tK =>
            simp only [optRoot]
            exact (hinv0.mem_inCap (t := tK) (by simp [hKc, optTrees])
              (AuxTree.rootId_mem (hinv0.nonEmpty tK (by simp [hKc, optTrees])))).2
        have hAt : nodesBase b vCap eCap + 17 * optRoot tKeep? + 17 ≤ hOut := by
          have := hrec_le; simp [NodeLayout.nodeAddr, tourLayout_stride] at this; omega
        have ha : Runs w p ω (.assign 19 (.load (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 17) (.reg 16))) (.const 15))))
            { st0 with regs := r1 } .normal { st0 with regs := r2 } 9 :=
          runs_assign_iff.mpr ⟨rtKeep, by
            simp [Expr.eval, r1, hr9, hr16, BinOp.eval, (by omega : 17 < 2 ^ w), (by omega : 15 < 2 ^ w),
              (by omega : 17 * optRoot tKeep? < 2 ^ w), (by omega : nodesBase b vCap eCap + 17 * optRoot tKeep? < 2 ^ w),
              (by omega : nodesBase b vCap eCap + 17 * optRoot tKeep? + 15 < 2 ^ w), rtKeep, hK0], rfl, rfl, rfl⟩
        exact ⟨_, by simp [Expr.size], tour_runs_cond_false hc ha⟩
    obtain ⟨cRt, hcRt, hrunRt⟩ := hrun_rtK
    obtain ⟨hdet_T, hdet_F⟩ := tourMove_rootTag_detect h ⟨hvLt, hv'Lt, hne, hvF, hv'NotF, hord_v', hsel⟩
      hvR ht_mem ht_map hn0 hinv0 (hval_out hvR) hperm hKeep_map hMove_map
    have hconn_or : s'.rf.F.Connected v r ∨ s'.rf.F.Connected v' r :=
      connected_applySplit_v_or_v' h.valid.compat.forest _ _ hr_spec.2
    -- Split on `F'.Connected v r` vs `¬F'.Connected v r`!
    by_cases hvr : s'.rf.F.Connected v r
    · -- Case 2a: `F'.Connected v r` -> `rtKeep = r + 1 ≠ 0`, `rKeep = r`, `rMove = v'`, `newRoot = v'`
      obtain ⟨hrtK_eq, tK, hKc⟩ := hdet_T hvr
      have hrK_eq : rKeep = r := by simp [rKeep, hvr]
      have hrM_eq : rMove = v' := by simp [rMove, hvr]
      have hR_eq : s'.rf.R = insert v' s.rf.R := by
        change insert (if s'.rf.F.Connected v r then v' else v) s.rf.R = _; simp [hvr]
      have hcond2 : (Expr.reg 19).eval w { st0 with regs := r2 } = some (r + 1) := by
        simp [Expr.eval, r2]; exact hrtK_eq
      set r3 := Function.update r2 19 r
      set r4 := Function.update r3 20 (firstEndBase b)
      set r5 := Function.update r4 20 feR
      have ha19 : Runs w p ω (.assign 19 (.bin .sub (.reg 19) (.const 1)))
          { st0 with regs := r2 } .normal { st0 with regs := r3 } 4 :=
        runs_assign_iff.mpr ⟨r, by
          have hr19 : r2 19 = r + 1 := by simp [r2]; exact hrtK_eq
          simp [Expr.eval, hr19, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : r < 2 ^ w)], rfl, rfl, rfl⟩
      have ha20a := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 20) (rBase := 0) (off := HDR_FIRST_END)
        (b := b) (val := firstEndBase b) (st := { st0 with regs := r3 }) (by simp [r3, r2, r1, hr0])
        (by simp [HDR_FIRST_END]; omega) (by simp [HDR_FIRST_END]; omega) hhdr0.2.2.2.2.1
      have ha20b := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 20) (rBase := 20) (rIdx := 19)
        (base := firstEndBase b) (idx := r) (val := feR) (st := { st0 with regs := r4 })
        (by simp [r4]) (by simp [r4, r3])
        (by simp [firstEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega) hfeR_mem
      have hfeR_tK : feR ∈ tK.toList := by
        have := hfeR_in_of (some tK) v (hKc ▸ hKeep_map) (fun z hz => hsubK z (hKc ▸ hz)) hvr
        simpa [optList] using this
      have hinv_K : TourForestInv x.numNodes sT (tK :: (optTrees tMove? ++ rest)) := by
        simpa [hKc, optTrees, List.append_assoc] using hinv0
      obtain ⟨tK', s1, o1, st1, c1, hrun1, _, hn1, hfr1, hinv1, hvals1, _, hrot1, hval1, _, hc1⟩ :=
        tourRotateFrontBody_runs (fuel := 2 * eCap + 2) (pos := st0.pos) C.toTourSplayOpsProcs ω
          hn0 hinv_K hvals0 hfeR_tK (by have := h.numNodes_le; omega) (by omega) ⟨hrec_le, hroom, hzero, by omega⟩
      have hcall_rot := runs_call_regs4 21 9 20 10 15 (st := { st0 with regs := r5 }) C.rotateFront_body
        (by simp [r5, r4, r3, r2, r1, hr9]) (by simp [r5])
        (by simp [r5, r4, r3, r2, r1, hr10]) (by simp [r5, r4, r3, r2, r1, hr15]) hrun1
      set r6 := Function.update r5 21 o1.value
      set mem1 := Function.update st1.mem (isRootBase b vCap + v') 1
      have hst_ir : Runs w p ω (.store (.bin .add (.reg 18) (.reg 5)) (.const 1))
          { st1 with regs := r6 } .normal { st1 with mem := mem1, regs := r6 } 5 :=
        runs_store_iff.mpr ⟨isRootBase b vCap + v', 1,
          by simp [Expr.eval, r6, r5, r4, r3, r2, r1, hr5, BinOp.eval,
            (by simp [isRootBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega : isRootBase b vCap + v' < 2 ^ w)],
          by simp [Expr.eval, (by omega : 1 < 2 ^ w)], rfl, rfl, rfl⟩
      have hn1' : tourLayout.NodesAt mem1 (nodesBase b vCap eCap) x.numNodes s1 :=
        NodesAt.congr tourLayout hn1 fun a ha => by
          dsimp only [mem1]; exact Function.update_of_ne (by have := (inRecords_lt_ordHandle_of_le h.numNodes_le ha).1; simp [isRootBase, nodesBase] at this ⊢; omega) _ _
      have hz1 : ZeroFrom mem1 hOut := fun a ha => by
        dsimp only [mem1]; rw [Function.update_of_ne (by simp [isRootBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)]
        exact hfr1.1 a ha
      have hperm1 : (tK' :: (optTrees tMove? ++ rest)).Perm (optTrees tMove? ++ (optTrees (some tK') ++ rest)) := by
        simpa [optTrees, List.append_assoc] using (List.perm_append_comm (l₁ := [tK']) (l₂ := optTrees tMove?)).append_right rest
      obtain ⟨tMove'?, s2, st2, c2, hrun2, hr2_lt, hn2', hfr2, hinv2, hvals2, hlist2, hval2N, hval2S, hc2⟩ :=
        setRootTagIfNz_runs (fuel := 2 * eCap + 2) (rNode := 17) (rVert := 5) (vert := v') (st := { st1 with mem := mem1, regs := r6 })
          C ω (by omega) (by omega) (by simp [r6, r5, r4, r3, r2, r1, hr17])
          (by simp [r6, r5, r4, r3, r2, r1, hr5]) (by simp [r6, r5, r4, r3, r2, r1, hr9])
          (by simp [r6, r5, r4, r3, r2, r1, hr10]) (by simp [r6, r5, r4, r3, r2, r1, hr15])
          hn1' (hinv1.perm hperm1).1 hvals1 (by omega) (by have := h.numNodes_le; omega) (by omega)
          ⟨hrec_le, hroom, hz1, by omega⟩
      have hperm2 : (optTrees tMove'? ++ (optTrees (some tK') ++ rest)).Perm
          (optTrees (some tK') ++ optTrees tMove'? ++ rest) := by
        simpa [List.append_assoc] using (List.perm_append_comm (l₁ := optTrees tMove'?) (l₂ := optTrees (some tK'))).append_right rest
      have hK'_map : (optList (some tK')).map (fun id => endOfKey (x.keyOf id)) =
          fullTour s'.ord s'.rf.F hvalid'.compat.forest r := by
        simp only [optList, Option.elim, hrot1]
        exact rotateNatList_map_fullTour hvalid' h ht_mem (by simpa [hKc, optList] using hKeep_map)
          (fun z hz => hsubK z (by simpa [hKc, optList] using hz)) hvr haR' hfeR_tK hfeR_key
      have hval_final : ∀ u, 1 ≤ u → u ≤ x.numNodes → (∃ w', endOfKey (x.keyOf u) ∈ s'.ord w') →
          (s2.nodes u).val =
            { isOpen := decide ((endOfKey (x.keyOf u)).1 ∉ s'.rf.F.E)
              isMarked := decide (endOfKey (x.keyOf u) ∈ s'.marked)
              rootTag := tourRootTagVal s' (endOfKey (x.keyOf u)) } := by
        intro u hu1 hu2 hact
        have hcap : u ≤ x.numNodes := hu2
        have hval_old := h.val_active u hu1 hu2 (hact_to_old _ hact)
        by_cases hut : u ∈ t.toList
        · rcases List.mem_append.mp (hperm.mem_iff.mpr hut) with huK | huM
          · have hu_nM : u ∉ optList tMove? := hdisj_KM u huK
            have hv2_eq : (s2.nodes u).val = (x.st.nodes u).val := by
              have h1 : (s2.nodes u).val = (s1.nodes u).val := by
                cases hMc : tMove? with
                | none => exact hval2N hMc u hcap
                | some tM =>
                  have hval2 := hval2S tM hMc; simp only [hMc] at hu_nM
                  have hne_r : u ≠ tM.rootId := fun heq => hu_nM (by
                    simpa [optList] using heq ▸ AuxTree.rootId_mem (hinv0.nonEmpty tM (by simp [hMc, optTrees])))
                  exact hval2.2 u hcap hne_r
              rw [h1, hval1 u hcap, hval_out hvR u hcap]
            rw [hv2_eq, hval_old, hFE, hmk]
            have hfu : endOfKey (x.keyOf u) ∈ fullTour s'.ord s'.rf.F hvalid'.compat.forest v := by
              rw [← hKeep_map]; exact List.mem_map_of_mem huK
            by_cases huaR : endOfKey (x.keyOf u) = aR
            · rw [huaR, tourRootTagVal_eq_succ h.valid hr_spec.1 haR,
                  tourRootTagVal_eq_succ hvalid' (hR_eq ▸ Finset.mem_insert_of_mem hr_spec.1) haR']
            · have hrt_s0 : tourRootTagVal s (endOfKey (x.keyOf u)) = 0 := by
                apply tourRootTagVal_eq_zero; intro r' hr' hh
                have hft_s : endOfKey (x.keyOf u) ∈ fullTour s.ord s.rf.F h.valid.compat.forest r := by
                  rw [← ht_map]; exact List.mem_map_of_mem hut
                obtain ⟨w1, hw1, hcr1⟩ := ((fullTour_spec h.valid.compat r).2 _).mp hft_s
                have hw1r' := h.valid.compat.unique w1 r' _ hw1 (List.mem_of_head? hh)
                rw [hw1r'] at hcr1
                have hr'r : r' = r := (h.valid.root_eq_of_mem (h.valid.roots_sub hr') hr' (connected_refl _ _)).symm.trans
                  (h.valid.root_eq_of_mem (h.valid.roots_sub hr') hr_spec.1 (connected_symm hcr1))
                rw [hr'r, haR] at hh; exact huaR (Option.some.inj hh).symm
              have hrt_s'0 : tourRootTagVal s' (endOfKey (x.keyOf u)) = 0 := by
                apply tourRootTagVal_eq_zero; intro r' hr' hh
                obtain ⟨w1, hw1, hvw1⟩ := ((fullTour_spec hvalid'.compat v).2 _).mp hfu
                have hw1r' := hvalid'.compat.unique w1 r' _ hw1 (List.mem_of_head? hh)
                rw [hw1r'] at hvw1
                have hr'r : r' = r := (hvalid'.unique_root v (Finset.mem_insert_of_mem hvF)).unique
                  ⟨hr', hvw1⟩ ⟨hR_eq ▸ Finset.mem_insert_of_mem hr_spec.1, hvr⟩
                rw [hr'r, haR'] at hh; exact huaR (Option.some.inj hh).symm
              rw [hrt_s0, hrt_s'0]
          · cases hMc : tMove? with
            | none => simp [hMc, optList] at huM
            | some tM =>
              have hval2 := hval2S tM hMc; rw [hMc] at huM hhdM hMove_map
              have hne_tM := hinv0.nonEmpty tM (by simp [hMc, optTrees])
              obtain ⟨hhd_v', hne_hd_v'⟩ := optRoot_mem_head_end hvalid' h ht_mem hne_tM hhdM hMove_map
                (fun z hz => hsubM z (by simpa [hMc, optList] using hz))
              by_cases hur : u = tM.rootId
              · subst hur
                rw [hval2.1, hval1 _ hcap, hval_out hvR _ hcap, hval_old]
                rw [tourRootTagVal_eq_succ hvalid' (hR_eq ▸ Finset.mem_insert_self v' _) hhd_v']; simp only [hFE, hmk]
              · rw [hval2.2 u hcap hur, hval1 u hcap, hval_out hvR u hcap, hval_old, hFE, hmk]
                have hfu : endOfKey (x.keyOf u) ∈ fullTour s'.ord s'.rf.F hvalid'.compat.forest v' := by
                  rw [← hMove_map]; exact List.mem_map_of_mem huM
                have hrt_s'0 : tourRootTagVal s' (endOfKey (x.keyOf u)) = 0 := by
                  apply tourRootTagVal_eq_zero; intro r' hr' hh
                  obtain ⟨w1, hw1, hvw1⟩ := ((fullTour_spec hvalid'.compat v').2 _).mp hfu
                  have hw1r' := hvalid'.compat.unique w1 r' _ hw1 (List.mem_of_head? hh)
                  rw [hw1r'] at hvw1
                  have hr'v' : r' = v' := (hvalid'.unique_root v' (Finset.mem_insert_self v' _)).unique
                    ⟨hr', hvw1⟩ ⟨hR_eq ▸ Finset.mem_insert_self v' _, connected_refl _ _⟩
                  rw [hr'v', hhd_v'] at hh
                  exact hne_hd_v' u (by simpa [optList] using huM) hur (Option.some.inj hh).symm
                have hrt_s0 : tourRootTagVal s (endOfKey (x.keyOf u)) = 0 := by
                  apply tourRootTagVal_eq_zero; intro r' hr' hh
                  have hft_s : endOfKey (x.keyOf u) ∈ fullTour s.ord s.rf.F h.valid.compat.forest r := by
                    rw [← ht_map]; exact List.mem_map_of_mem hut
                  obtain ⟨w1, hw1, hcr1⟩ := ((fullTour_spec h.valid.compat r).2 _).mp hft_s
                  have hw1r' := h.valid.compat.unique w1 r' _ hw1 (List.mem_of_head? hh)
                  rw [hw1r'] at hcr1
                  have hr'r : r' = r := (h.valid.root_eq_of_mem (h.valid.roots_sub hr') hr' (connected_refl _ _)).symm.trans
                    (h.valid.root_eq_of_mem (h.valid.roots_sub hr') hr_spec.1 (connected_symm hcr1))
                  rw [hr'r, haR] at hh
                  have huaR : endOfKey (x.keyOf u) = aR := (Option.some.inj hh).symm
                  obtain ⟨w2, hw2, hv'w2⟩ := ((fullTour_spec hvalid'.compat v').2 _).mp hfu
                  have hw2r := hvalid'.compat.unique w2 r _ hw2 (huaR ▸ List.mem_of_head? haR')
                  exact not_connected_v_v'_applySplit h.valid.compat.forest hne hv'NotF _ _
                    (connected_trans hvr (connected_symm (hw2r ▸ hv'w2)))
                rw [hrt_s0, hrt_s'0]
        · have hv_nt : (s2.nodes u).val = (x.st.nodes u).val := by
            have h1 : (s2.nodes u).val = (s1.nodes u).val := by
              cases hMc : tMove? with
              | none => exact hval2N hMc u hcap
              | some tM =>
                have hval2 := hval2S tM hMc
                have hne_r : u ≠ tM.rootId := fun heq => hut (hsubM u (by
                  simpa [hMc, optList] using heq ▸ AuxTree.rootId_mem (hinv0.nonEmpty tM (by simp [hMc, optTrees]))))
                exact hval2.2 u hcap hne_r
            rw [h1, hval1 u hcap, hval_out hvR u hcap]
          rw [hv_nt, hval_old, hrt_outside u hu1 hu2 hut hact, hFE, hmk]
      have hval_oth : ∀ u ≤ x.numNodes, u ∉ t.toList → (s2.nodes u).val = (x.st.nodes u).val := by
        intro u hcap hut
        have h1 : (s2.nodes u).val = (s1.nodes u).val := by
          cases hMc : tMove? with
          | none => exact hval2N hMc u hcap
          | some tM =>
            have hval2 := hval2S tM hMc
            have hne_r : u ≠ tM.rootId := fun heq => hut (hsubM u (by
              simpa [hMc, optList] using heq ▸ AuxTree.rootId_mem (hinv0.nonEmpty tM (by simp [hMc, optTrees]))))
            exact hval2.2 u hcap hne_r
        rw [h1, hval1 u hcap, hval_out hvR u hcap]
      refine ⟨some tK', tMove'?, s2, st2, _,
        tour_runs_seq_normal ha18 (tour_runs_cond_false hcond1 (tour_runs_seq_normal hrunRt
          (tour_runs_cond_true hcond2 (by omega) (tour_runs_seq_normal ha19 (tour_runs_seq_normal ha20a
            (tour_runs_seq_normal ha20b (tour_runs_seq_normal hcall_rot (tour_runs_seq_normal hst_ir hrun2)))))))),
        by rw [hr2_lt 15 (by omega)]; simp [r6, r5, r4, r3, r2, r1, hr15],
        hn2', hfr2.1,
        fun a ha hnr h1 h2 => by
          rw [hfr2.2 a ha hnr]; dsimp only [mem1]; rw [Function.update_of_ne h2]; exact hfr1.2 a ha hnr,
        fun u hu => by
          rw [hfr2.2 _ (by simp [isRootBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)
            (not_inRecords_of_lt_nodesBase (by simp [isRootBase, nodesBase]; omega))]
          dsimp only [mem1]; by_cases huv' : u = v'
          · subst huv'; simp [hR_eq]
          · rw [Function.update_of_ne (by omega),
              hfr1.2 _ (by simp [isRootBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)
                (not_inRecords_of_lt_nodesBase (by simp [isRootBase, nodesBase]; omega)),
              hir0 u hu, hR_eq]; simp [huv'],
        (hinv2.perm hperm2).1,
        ((show (optList (some tK')).Perm (optList tKeep?) by
            simp only [optList, Option.elim, hKc, hrot1]; exact rotateNatList_perm hfeR_tK).append
          (List.Perm.of_eq hlist2)).trans hperm,
        by rw [hrK_eq]; exact hK'_map, by rw [hrM_eq, hlist2]; exact hMove_map,
        hval_final, hval_oth, ?_⟩
      have hpeq0 : forestPhi (tK :: (optTrees tMove? ++ rest)) =
          forestPhi (optTrees tKeep? ++ optTrees tMove? ++ rest) := by simp [hKc, optTrees]
      have hpeq1 := forestPhi_perm hperm1
      have hpeq2 := forestPhi_perm hperm2
      rw [← hpeq2]; rw [← hpeq1] at hc2; rw [hpeq0] at hc1
      have hlog1 : 1 ≤ Nat.log 2 (x.numNodes + 2) + 1 := by omega
      clear * - hcRt hc1 hc2 hlog1; simp only [Expr.size, TOUR_FIND_AMORT, TOUR_SEQ_AMORT] at *; omega
    · -- Case 2b: `¬F'.Connected v r` -> `rtKeep = 0`, `tMove? = some tM` with `rootTag = r + 1`, `rKeep = v`, `rMove = r`, `newRoot = v`
      have hv'r : s'.rf.F.Connected v' r := hconn_or.resolve_left hvr
      obtain ⟨hrtK0, tM, hMc, hrtM_eq⟩ := hdet_F hvr
      have hrK_eq : rKeep = v := by simp [rKeep, hvr]
      have hrM_eq : rMove = r := by simp [rMove, hvr]
      have hR_eq : s'.rf.R = insert v s.rf.R := by
        change insert (if s'.rf.F.Connected v r then v' else v) s.rf.R = _; simp [hvr]
      have hcond2 : (Expr.reg 19).eval w { st0 with regs := r2 } = some 0 := by
        simp [Expr.eval, r2]; exact hrtK0
      have hM_cap : tM.rootId ≤ x.numNodes :=
        (hinv0.mem_inCap (t := tM) (by simp [hMc, optTrees])
          (AuxTree.rootId_mem (hinv0.nonEmpty tM (by simp [hMc, optTrees])))).2
      have hAtM : nodesBase b vCap eCap + 17 * tM.rootId + 17 ≤ hOut := by
        have := hrec_le; simp [NodeLayout.nodeAddr, tourLayout_stride] at this; omega
      set r3 := Function.update r2 19 r
      set r4 := Function.update r3 20 (firstEndBase b)
      set r5 := Function.update r4 20 feR
      have ha19 : Runs w p ω (.assign 19 (.bin .sub (.load (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 17) (.reg 17))) (.const 15))) (.const 1)))
          { st0 with regs := r2 } .normal { st0 with regs := r3 } 11 :=
        runs_assign_iff.mpr ⟨r, by
          simp [Expr.eval, r2, r1, hr9, hr17, hMc, optRoot, BinOp.eval, (by omega : 17 < 2 ^ w),
            (by omega : 15 < 2 ^ w), (by omega : 1 < 2 ^ w), (by omega : 17 * tM.rootId < 2 ^ w),
            (by omega : nodesBase b vCap eCap + 17 * tM.rootId < 2 ^ w),
            (by omega : nodesBase b vCap eCap + 17 * tM.rootId + 15 < 2 ^ w), hrtM_eq]; exact ⟨by omega, rfl⟩, rfl, rfl, rfl⟩
      have ha20a := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 20) (rBase := 0) (off := HDR_FIRST_END)
        (b := b) (val := firstEndBase b) (st := { st0 with regs := r3 }) (by simp [r3, r2, r1, hr0])
        (by simp [HDR_FIRST_END]; omega) (by simp [HDR_FIRST_END]; omega) hhdr0.2.2.2.2.1
      have ha20b := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 20) (rBase := 20) (rIdx := 19)
        (base := firstEndBase b) (idx := r) (val := feR) (st := { st0 with regs := r4 })
        (by simp [r4]) (by simp [r4, r3])
        (by simp [firstEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega) hfeR_mem
      have hfeR_tM : feR ∈ tM.toList := by
        have := hfeR_in_of (some tM) v' (hMc ▸ hMove_map) (fun z hz => hsubM z (hMc ▸ hz)) hv'r
        simpa [optList] using this
      have hperm0M : (optTrees tKeep? ++ optTrees tMove? ++ rest).Perm (tM :: (optTrees tKeep? ++ rest)) := by
        cases tKeep? <;> simp [hMc, optTrees]
        exact List.Perm.swap _ _ _
      obtain ⟨tM', s1, o1, st1, c1, hrun1, _, hn1, hfr1, hinv1, hvals1, _, hrot1, hval1, _, hc1⟩ :=
        tourRotateFrontBody_runs (fuel := 2 * eCap + 2) (pos := st0.pos) C.toTourSplayOpsProcs ω
          hn0 (hinv0.perm hperm0M).1 hvals0 hfeR_tM (by have := h.numNodes_le; omega) (by omega) ⟨hrec_le, hroom, hzero, by omega⟩
      have hcall_rot := runs_call_regs4 21 9 20 10 15 (st := { st0 with regs := r5 }) C.rotateFront_body
        (by simp [r5, r4, r3, r2, r1, hr9]) (by simp [r5])
        (by simp [r5, r4, r3, r2, r1, hr10]) (by simp [r5, r4, r3, r2, r1, hr15]) hrun1
      set r6 := Function.update r5 21 o1.value
      set mem1 := Function.update st1.mem (isRootBase b vCap + v) 1
      have hst_ir : Runs w p ω (.store (.bin .add (.reg 18) (.reg 4)) (.const 1))
          { st1 with regs := r6 } .normal { st1 with mem := mem1, regs := r6 } 5 :=
        runs_store_iff.mpr ⟨isRootBase b vCap + v, 1,
          by simp [Expr.eval, r6, r5, r4, r3, r2, r1, hr4, BinOp.eval,
            (by simp [isRootBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega : isRootBase b vCap + v < 2 ^ w)],
          by simp [Expr.eval, (by omega : 1 < 2 ^ w)], rfl, rfl, rfl⟩
      have hn1' : tourLayout.NodesAt mem1 (nodesBase b vCap eCap) x.numNodes s1 :=
        NodesAt.congr tourLayout hn1 fun a ha => by
          dsimp only [mem1]; exact Function.update_of_ne (by have := (inRecords_lt_ordHandle_of_le h.numNodes_le ha).1; simp [isRootBase, nodesBase] at this ⊢; omega) _ _
      have hz1 : ZeroFrom mem1 hOut := fun a ha => by
        dsimp only [mem1]; rw [Function.update_of_ne (by simp [isRootBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)]
        exact hfr1.1 a ha
      have hperm1 : (tM' :: (optTrees tKeep? ++ rest)).Perm (optTrees tKeep? ++ (optTrees (some tM') ++ rest)) := by
        simpa [optTrees, List.append_assoc] using (List.perm_append_comm (l₁ := [tM']) (l₂ := optTrees tKeep?)).append_right rest
      obtain ⟨tKeep'?, s2, st2, c2, hrun2, hr2_lt, hn2', hfr2, hinv2, hvals2, hlist2, hval2N, hval2S, hc2⟩ :=
        setRootTagIfNz_runs (fuel := 2 * eCap + 2) (rNode := 16) (rVert := 4) (vert := v) (st := { st1 with mem := mem1, regs := r6 })
          C ω (by omega) (by omega) (by simp [r6, r5, r4, r3, r2, r1, hr16])
          (by simp [r6, r5, r4, r3, r2, r1, hr4]) (by simp [r6, r5, r4, r3, r2, r1, hr9])
          (by simp [r6, r5, r4, r3, r2, r1, hr10]) (by simp [r6, r5, r4, r3, r2, r1, hr15])
          hn1' (hinv1.perm hperm1).1 hvals1 (by omega) (by have := h.numNodes_le; omega) (by omega)
          ⟨hrec_le, hroom, hz1, by omega⟩
      have hM'_map : (optList (some tM')).map (fun id => endOfKey (x.keyOf id)) =
          fullTour s'.ord s'.rf.F hvalid'.compat.forest r := by
        simp only [optList, Option.elim, hrot1]
        exact rotateNatList_map_fullTour hvalid' h ht_mem (by simpa [hMc, optList] using hMove_map)
          (fun z hz => hsubM z (by simpa [hMc, optList] using hz)) hv'r haR' hfeR_tM hfeR_key
      have hval_final : ∀ u, 1 ≤ u → u ≤ x.numNodes → (∃ w', endOfKey (x.keyOf u) ∈ s'.ord w') →
          (s2.nodes u).val =
            { isOpen := decide ((endOfKey (x.keyOf u)).1 ∉ s'.rf.F.E)
              isMarked := decide (endOfKey (x.keyOf u) ∈ s'.marked)
              rootTag := tourRootTagVal s' (endOfKey (x.keyOf u)) } := by
        intro u hu1 hu2 hact
        have hcap : u ≤ x.numNodes := hu2
        have hval_old := h.val_active u hu1 hu2 (hact_to_old _ hact)
        by_cases hut : u ∈ t.toList
        · rcases List.mem_append.mp (hperm.mem_iff.mpr hut) with huK | huM
          · cases hKc : tKeep? with
            | none => simp [hKc, optList] at huK
            | some tK =>
              have hval2 := hval2S tK hKc; rw [hKc] at huK hhdK hKeep_map
              have hne_tK := hinv0.nonEmpty tK (by simp [hKc, optTrees])
              obtain ⟨hhd_v, hne_hd_v⟩ := optRoot_mem_head_end hvalid' h ht_mem hne_tK hhdK hKeep_map
                (fun z hz => hsubK z (by simpa [hKc, optList] using hz))
              by_cases hur : u = tK.rootId
              · subst hur
                rw [hval2.1, hval1 _ hcap, hval_out hvR _ hcap, hval_old]
                rw [tourRootTagVal_eq_succ hvalid' (hR_eq ▸ Finset.mem_insert_self v _) hhd_v]; simp only [hFE, hmk]
              · rw [hval2.2 u hcap hur, hval1 u hcap, hval_out hvR u hcap, hval_old, hFE, hmk]
                have hfu : endOfKey (x.keyOf u) ∈ fullTour s'.ord s'.rf.F hvalid'.compat.forest v := by
                  rw [← hKeep_map]; exact List.mem_map_of_mem huK
                have hrt_s'0 : tourRootTagVal s' (endOfKey (x.keyOf u)) = 0 := by
                  apply tourRootTagVal_eq_zero; intro r' hr' hh
                  obtain ⟨w1, hw1, hvw1⟩ := ((fullTour_spec hvalid'.compat v).2 _).mp hfu
                  have hw1r' := hvalid'.compat.unique w1 r' _ hw1 (List.mem_of_head? hh)
                  rw [hw1r'] at hvw1
                  have hr'v : r' = v := (hvalid'.unique_root v (Finset.mem_insert_of_mem hvF)).unique
                    ⟨hr', hvw1⟩ ⟨hR_eq ▸ Finset.mem_insert_self v _, connected_refl _ _⟩
                  rw [hr'v, hhd_v] at hh
                  exact hne_hd_v u (by simpa [optList] using huK) hur (Option.some.inj hh).symm
                have hrt_s0 : tourRootTagVal s (endOfKey (x.keyOf u)) = 0 := by
                  apply tourRootTagVal_eq_zero; intro r' hr' hh
                  have hft_s : endOfKey (x.keyOf u) ∈ fullTour s.ord s.rf.F h.valid.compat.forest r := by
                    rw [← ht_map]; exact List.mem_map_of_mem hut
                  obtain ⟨w1, hw1, hcr1⟩ := ((fullTour_spec h.valid.compat r).2 _).mp hft_s
                  have hw1r' := h.valid.compat.unique w1 r' _ hw1 (List.mem_of_head? hh)
                  rw [hw1r'] at hcr1
                  have hr'r : r' = r := (h.valid.root_eq_of_mem (h.valid.roots_sub hr') hr' (connected_refl _ _)).symm.trans
                    (h.valid.root_eq_of_mem (h.valid.roots_sub hr') hr_spec.1 (connected_symm hcr1))
                  rw [hr'r, haR] at hh
                  have huaR : endOfKey (x.keyOf u) = aR := (Option.some.inj hh).symm
                  obtain ⟨w2, hw2, hvw2⟩ := ((fullTour_spec hvalid'.compat v).2 _).mp hfu
                  have hw2r := hvalid'.compat.unique w2 r _ hw2 (huaR ▸ List.mem_of_head? haR')
                  exact hvr (hw2r ▸ hvw2)
                rw [hrt_s0, hrt_s'0]
          · have hu_nK : u ∉ optList tKeep? := fun hk => hdisj_KM u hk huM
            have hv2_eq : (s2.nodes u).val = (x.st.nodes u).val := by
              have h1 : (s2.nodes u).val = (s1.nodes u).val := by
                cases hKc : tKeep? with
                | none => exact hval2N hKc u hcap
                | some tK =>
                  have hval2 := hval2S tK hKc; simp only [hKc] at hu_nK
                  have hne_r : u ≠ tK.rootId := fun heq => hu_nK (by
                    simpa [optList] using heq ▸ AuxTree.rootId_mem (hinv0.nonEmpty tK (by simp [hKc, optTrees])))
                  exact hval2.2 u hcap hne_r
              rw [h1, hval1 u hcap, hval_out hvR u hcap]
            rw [hv2_eq, hval_old, hFE, hmk]
            have hfu : endOfKey (x.keyOf u) ∈ fullTour s'.ord s'.rf.F hvalid'.compat.forest v' := by
              rw [← hMove_map]; exact List.mem_map_of_mem huM
            by_cases huaR : endOfKey (x.keyOf u) = aR
            · rw [huaR, tourRootTagVal_eq_succ h.valid hr_spec.1 haR,
                  tourRootTagVal_eq_succ hvalid' (hR_eq ▸ Finset.mem_insert_of_mem hr_spec.1) haR']
            · have hrt_s0 : tourRootTagVal s (endOfKey (x.keyOf u)) = 0 := by
                apply tourRootTagVal_eq_zero; intro r' hr' hh
                have hft_s : endOfKey (x.keyOf u) ∈ fullTour s.ord s.rf.F h.valid.compat.forest r := by
                  rw [← ht_map]; exact List.mem_map_of_mem hut
                obtain ⟨w1, hw1, hcr1⟩ := ((fullTour_spec h.valid.compat r).2 _).mp hft_s
                have hw1r' := h.valid.compat.unique w1 r' _ hw1 (List.mem_of_head? hh)
                rw [hw1r'] at hcr1
                have hr'r : r' = r := (h.valid.root_eq_of_mem (h.valid.roots_sub hr') hr' (connected_refl _ _)).symm.trans
                  (h.valid.root_eq_of_mem (h.valid.roots_sub hr') hr_spec.1 (connected_symm hcr1))
                rw [hr'r, haR] at hh; exact huaR (Option.some.inj hh).symm
              have hrt_s'0 : tourRootTagVal s' (endOfKey (x.keyOf u)) = 0 := by
                apply tourRootTagVal_eq_zero; intro r' hr' hh
                obtain ⟨w1, hw1, hv'w1⟩ := ((fullTour_spec hvalid'.compat v').2 _).mp hfu
                have hw1r' := hvalid'.compat.unique w1 r' _ hw1 (List.mem_of_head? hh)
                rw [hw1r'] at hv'w1
                have hr'r : r' = r := (hvalid'.unique_root v' (Finset.mem_insert_self v' _)).unique
                  ⟨hr', hv'w1⟩ ⟨hR_eq ▸ Finset.mem_insert_of_mem hr_spec.1, hv'r⟩
                rw [hr'r, haR'] at hh; exact huaR (Option.some.inj hh).symm
              rw [hrt_s0, hrt_s'0]
        · have hv_nt : (s2.nodes u).val = (x.st.nodes u).val := by
            have h1 : (s2.nodes u).val = (s1.nodes u).val := by
              cases hKc : tKeep? with
              | none => exact hval2N hKc u hcap
              | some tK =>
                have hval2 := hval2S tK hKc
                have hne_r : u ≠ tK.rootId := fun heq => hut (hsubK u (by
                  simpa [hKc, optList] using heq ▸ AuxTree.rootId_mem (hinv0.nonEmpty tK (by simp [hKc, optTrees]))))
                exact hval2.2 u hcap hne_r
            rw [h1, hval1 u hcap, hval_out hvR u hcap]
          rw [hv_nt, hval_old, hrt_outside u hu1 hu2 hut hact, hFE, hmk]
      have hval_oth : ∀ u ≤ x.numNodes, u ∉ t.toList → (s2.nodes u).val = (x.st.nodes u).val := by
        intro u hcap hut
        have h1 : (s2.nodes u).val = (s1.nodes u).val := by
          cases hKc : tKeep? with
          | none => exact hval2N hKc u hcap
          | some tK =>
            have hval2 := hval2S tK hKc
            have hne_r : u ≠ tK.rootId := fun heq => hut (hsubK u (by
              simpa [hKc, optList] using heq ▸ AuxTree.rootId_mem (hinv0.nonEmpty tK (by simp [hKc, optTrees]))))
            exact hval2.2 u hcap hne_r
        rw [h1, hval1 u hcap, hval_out hvR u hcap]
      refine ⟨tKeep'?, some tM', s2, st2, _,
        tour_runs_seq_normal ha18 (tour_runs_cond_false hcond1 (tour_runs_seq_normal hrunRt
          (tour_runs_cond_false hcond2 (tour_runs_seq_normal ha19 (tour_runs_seq_normal ha20a
            (tour_runs_seq_normal ha20b (tour_runs_seq_normal hcall_rot (tour_runs_seq_normal hst_ir hrun2)))))))),
        by rw [hr2_lt 15 (by omega)]; simp [r6, r5, r4, r3, r2, r1, hr15],
        hn2', hfr2.1,
        fun a ha hnr h1 h2 => by
          rw [hfr2.2 a ha hnr]; dsimp only [mem1]; rw [Function.update_of_ne h1]; exact hfr1.2 a ha hnr,
        fun u hu => by
          rw [hfr2.2 _ (by simp [isRootBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)
            (not_inRecords_of_lt_nodesBase (by simp [isRootBase, nodesBase]; omega))]
          dsimp only [mem1]; by_cases huv : u = v
          · subst huv; simp [hR_eq]
          · rw [Function.update_of_ne (by omega),
              hfr1.2 _ (by simp [isRootBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)
                (not_inRecords_of_lt_nodesBase (by simp [isRootBase, nodesBase]; omega)),
              hir0 u hu, hR_eq]; simp [huv],
        by simpa [List.append_assoc] using hinv2,
        ((List.Perm.of_eq hlist2).append (show (optList (some tM')).Perm (optList tMove?) by
            simp only [optList, Option.elim, hMc, hrot1]; exact rotateNatList_perm hfeR_tM)).trans hperm,
        by rw [hrK_eq, hlist2]; exact hKeep_map, by rw [hrM_eq]; exact hM'_map,
        hval_final, hval_oth, ?_⟩
      have hpeq0 := forestPhi_perm hperm0M
      have hpeq1 := forestPhi_perm hperm1
      have hpeq2 : forestPhi (optTrees tKeep'? ++ (optTrees (some tM') ++ rest)) =
          forestPhi (optTrees tKeep'? ++ optTrees (some tM') ++ rest) := by simp [List.append_assoc]
      rw [← hpeq2]; rw [← hpeq1] at hc2; rw [← hpeq0] at hc1
      have hlog1 : 1 ≤ Nat.log 2 (x.numNodes + 2) + 1 := by omega
      clear * - hcRt hc1 hc2 hlog1; simp only [Expr.size, TOUR_FIND_AMORT, TOUR_SEQ_AMORT] at *; omega

end MinCostFlow.SparseCore.Program
