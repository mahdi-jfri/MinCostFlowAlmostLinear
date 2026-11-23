module

public import MinCostFlow.SparseCore.Program.TourOpsEditDropCore
import Mathlib.Tactic

/-!
# Case 1 (`u = feOld`) splay-delete and `rootTag` update for `tourDropOneBody` (Op 0)

Verifies `tourDropOne_case1_cond`: executing the `if irV` branch (clearing `u`'s `rootTag`,
deleting `u`, and transferring `rootTag`/`rotateFront` to `newFe` when `v ∈ R`, or just
deleting `u` when `v ∉ R`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

private theorem runs_call_regs7 {w : ℕ} {p : Program} {ω : ℕ → Bool} (r : ℕ) {f : ℕ}
    (r0 r1 r2 r3 r4 r5 r6 : ℕ) {st st₁ : State} {v0 v1 v2 v3 v4 v5 v6 : ℕ} {body : Stmt}
    {o₁ : Outcome} {c₁ : ℕ} (hget : p.procs[f]? = some body)
    (h0 : st.regs r0 = v0) (h1 : st.regs r1 = v1) (h2 : st.regs r2 = v2) (h3 : st.regs r3 = v3)
    (h4 : st.regs r4 = v4) (h5 : st.regs r5 = v5) (h6 : st.regs r6 = v6)
    (hrun : Runs w p ω body (startState [v0, v1, v2, v3, v4, v5, v6] st.mem st.pos) o₁ st₁ c₁) :
    Runs w p ω (.call r f [.reg r0, .reg r1, .reg r2, .reg r3, .reg r4, .reg r5, .reg r6]) st .normal
      { st₁ with regs := Function.update st.regs r o₁.value } (8 + c₁) := by
  have h := tour_runs_call_of (r := r) (args := [.reg r0, .reg r1, .reg r2, .reg r3, .reg r4, .reg r5, .reg r6]) hget
    (by simp [evalArgs, Expr.eval, h0, h1, h2, h3, h4, h5, h6]) hrun
  convert h using 1; simp [argsSize, Expr.size]; omega

/-- Execute the `if irV` splay-delete and `rootTag` update in Case 1 (`u = feOld`) of
`tourDropOneBody`. -/
theorem tourDropOne_case1_cond {τ_ord : Type}
    {w vCap eCap b v keyX u hN newFe : ℕ} {p : Program}
    (C : TourSplayQueryProcs w p) (ω : ℕ → Bool)
    {s : TourAbs} {x : TourConcrete τ_ord} {mem memN1 : ℕ → ℕ}
    {stN : State} {rI2 : ℕ → ℕ} {t : AuxTree} {rest : List AuxTree}
    (h : TourCoreAt vCap eCap b s x mem)
    (_hkeyLt : keyX < 2 * eCap) (hvLt : v < vCap)
    (hxv : endOfKey keyX ∈ s.ord v) (hxOpen : (endOfKey keyX).1 ∉ s.rf.F.E)
    (hhead_x : (s.ord v).head? = some (endOfKey keyX))
    (hu_eq : u = x.nodeOf keyX) (hu1' : 1 ≤ u) (hu_le' : u ≤ x.numNodes) (hu_key' : x.keyOf u = keyX)
    (hinv_p : TourForestInv x.numNodes x.st (t :: rest))
    (hperm_r : x.trees.Perm (t :: rest))
    (ht_map : t.toList.map (fun id => endOfKey (x.keyOf id)) = fullTour s.ord s.rf.F h.valid.compat.forest (s.rf.root v))
    (hu_t' : u ∈ t.toList)
    (hnN1 : tourLayout.NodesAt memN1 (nodesBase b vCap eCap) x.numNodes x.st)
    (hheapN1 : HeapOk tourLayout w (nodesBase b vCap eCap) x.numNodes hN 2 memN1)
    (hnewFe_eq : newFe = match ((tourDropOneAbs s (endOfKey keyX)).ord v).head? with | none => 0 | some e => x.nodeOf (endKey e))
    (ht_erase_rot : ((t.toList.erase u).map fun id => endOfKey (x.keyOf id)).IsRotated
      (fullTour (tourDropOneAbs s (endOfKey keyX)).ord s.rf.F
        (tourValid_dropOneAbs h.valid hxOpen).compat.forest (s.rf.root v)))
    (hrI2_2 : rI2 2 = hN) (hrI2_5 : rI2 5 = v) (hrI2_6 : rI2 6 = u)
    (hrI2_9 : rI2 9 = nodesBase b vCap eCap) (hrI2_10 : rI2 10 = 2 * eCap + 2)
    (hrI2_14 : rI2 14 = newFe) (hrI2_15 : rI2 15 = if v ∈ s.rf.R then 1 else 0)
    (_hord_le : ordHandleOf b vCap eCap ≤ hN) (hroom : hN + 4 < 2 ^ w)
    (hw : vCap + 2 * eCap + 4 < 2 ^ w) (hwide : 18 ≤ 2 ^ w) :
    let s' := tourDropOneAbs s (endOfKey keyX)
    let hvalid' := tourValid_dropOneAbs h.valid hxOpen
    ∃ (tF? : Option AuxTree) (sF : SplayState TourVal TourSum Unit) (stF : State) (cTail : ℕ),
      Runs w p ω
        (.cond (.reg 15)
          (.assign 16 (.const 1) ;; .assign 17 (.const 0) ;;
           .call 18 C.setValNode [.reg 9, .reg 6, .reg 16, .reg 17, .reg 17, .reg 10, .reg 2] ;;
           .call 18 C.deleteNode [.reg 9, .reg 6, .reg 10, .reg 2] ;;
           .cond (.reg 14)
             (.assign 15 (.bin .add (.reg 9) (.bin .mul (.const 17) (.reg 14))) ;;
              .assign 16 (.load (.bin .add (.reg 15) (.const 9))) ;;
              .assign 17 (.load (.bin .add (.reg 15) (.const 10))) ;;
              .assign 18 (.bin .add (.reg 5) (.const 1)) ;;
              .call 19 C.setValNode [.reg 9, .reg 14, .reg 16, .reg 17, .reg 18, .reg 10, .reg 2] ;;
              .call 19 C.rotateFront [.reg 9, .reg 14, .reg 10, .reg 2])
             .nop)
          (.call 18 C.deleteNode [.reg 9, .reg 6, .reg 10, .reg 2]))
        { stN with mem := memN1, regs := rI2 } .normal stF cTail ∧
      stF.regs 2 = hN ∧
      tourLayout.NodesAt stF.mem (nodesBase b vCap eCap) x.numNodes sF ∧
      TreeFrame tourLayout (nodesBase b vCap eCap) x.numNodes hN memN1 stF.mem ∧
      TourForestInv x.numNodes sF (AuxTree.node u .leaf .leaf :: optTrees tF? ++ rest) ∧
      (optList tF?).Perm (t.toList.erase u) ∧
      (optList tF?).map (fun id => endOfKey (x.keyOf id)) = fullTour s'.ord s'.rf.F hvalid'.compat.forest (s.rf.root v) ∧
      (∀ id, 1 ≤ id → id ≤ x.numNodes → id ≠ u →
        (∃ w', endOfKey (x.keyOf id) ∈ s'.ord w') →
        (sF.nodes id).val =
          { isOpen := decide ((endOfKey (x.keyOf id)).1 ∉ s.rf.F.E)
            isMarked := decide (endOfKey (x.keyOf id) ∈ s'.marked)
            rootTag := tourRootTagVal s' (endOfKey (x.keyOf id)) }) ∧
      (sF.nodes u).val.rootTag = 0 ∧
      (∀ id ≤ x.numNodes, (∀ w', endOfKey (x.keyOf id) ∉ s.ord w') ∨ id = 0 ∨ x.numNodes < id →
        (sF.nodes id).val = (x.st.nodes id).val) ∧
      cTail + TOUR_PHI_MULT * forestPhi (AuxTree.node u .leaf .leaf :: optTrees tF? ++ rest) ≤
        TOUR_PHI_MULT * forestPhi (t :: rest) +
          (2 * TOUR_FIND_AMORT + 2 * TOUR_SEQ_AMORT) * (Nat.log 2 (x.numNodes + 2) + 1) + 200 := by
  intro s' hvalid'
  set r := s.rf.root v
  have hrR : r ∈ s.rf.R := (h.valid.root_spec (h.valid.compat.vert v (List.ne_nil_of_mem hxv))).1
  set irV := if v ∈ s.rf.R then 1 else 0
  have hord'_upd : s'.ord = Function.update s.ord v ((s.ord v).filter fun z => z != endOfKey keyX) :=
    tourDropOneAbs_ord_eq_update h.valid hxv
  set condStmt : Stmt :=
    .cond (.reg 15)
      (.assign 16 (.const 1) ;; .assign 17 (.const 0) ;;
       .call 18 C.setValNode [.reg 9, .reg 6, .reg 16, .reg 17, .reg 17, .reg 10, .reg 2] ;;
       .call 18 C.deleteNode [.reg 9, .reg 6, .reg 10, .reg 2] ;;
       .cond (.reg 14)
         (.assign 15 (.bin .add (.reg 9) (.bin .mul (.const 17) (.reg 14))) ;;
          .assign 16 (.load (.bin .add (.reg 15) (.const 9))) ;;
          .assign 17 (.load (.bin .add (.reg 15) (.const 10))) ;;
          .assign 18 (.bin .add (.reg 5) (.const 1)) ;;
          .call 19 C.setValNode [.reg 9, .reg 14, .reg 16, .reg 17, .reg 18, .reg 10, .reg 2] ;;
          .call 19 C.rotateFront [.reg 9, .reg 14, .reg 10, .reg 2])
         .nop)
      (.call 18 C.deleteNode [.reg 9, .reg 6, .reg 10, .reg 2])
  have hClose1 : ∀ (tF? : Option AuxTree) (sF : SplayState TourVal TourSum Unit) (stF : State) (cTail : ℕ),
      Runs w p ω condStmt { stN with mem := memN1, regs := rI2 } .normal stF cTail →
      stF.regs 2 = hN →
      tourLayout.NodesAt stF.mem (nodesBase b vCap eCap) x.numNodes sF →
      TreeFrame tourLayout (nodesBase b vCap eCap) x.numNodes hN memN1 stF.mem →
      TourForestInv x.numNodes sF (AuxTree.node u .leaf .leaf :: optTrees tF? ++ rest) →
      (optList tF?).Perm (t.toList.erase u) →
      (optList tF?).map (fun id => endOfKey (x.keyOf id)) = fullTour s'.ord s'.rf.F hvalid'.compat.forest r →
      (∀ id, 1 ≤ id → id ≤ x.numNodes → id ≠ u →
        (∃ w', endOfKey (x.keyOf id) ∈ s'.ord w') →
        (sF.nodes id).val =
          { isOpen := decide ((endOfKey (x.keyOf id)).1 ∉ s.rf.F.E)
            isMarked := decide (endOfKey (x.keyOf id) ∈ s'.marked)
            rootTag := tourRootTagVal s' (endOfKey (x.keyOf id)) }) →
      (sF.nodes u).val.rootTag = 0 →
      (∀ id ≤ x.numNodes, (∀ w', endOfKey (x.keyOf id) ∉ s.ord w') ∨ id = 0 ∨ x.numNodes < id →
        (sF.nodes id).val = (x.st.nodes id).val) →
      cTail + TOUR_PHI_MULT * forestPhi (AuxTree.node u .leaf .leaf :: optTrees tF? ++ rest) ≤
        TOUR_PHI_MULT * forestPhi (t :: rest) +
          (2 * TOUR_FIND_AMORT + 2 * TOUR_SEQ_AMORT) * (Nat.log 2 (x.numNodes + 2) + 1) + 200 →
      ∃ (tF? : Option AuxTree) (sF : SplayState TourVal TourSum Unit) (stF : State) (cTail : ℕ),
        Runs w p ω condStmt { stN with mem := memN1, regs := rI2 } .normal stF cTail ∧
        stF.regs 2 = hN ∧
        tourLayout.NodesAt stF.mem (nodesBase b vCap eCap) x.numNodes sF ∧
        TreeFrame tourLayout (nodesBase b vCap eCap) x.numNodes hN memN1 stF.mem ∧
        TourForestInv x.numNodes sF (AuxTree.node u .leaf .leaf :: optTrees tF? ++ rest) ∧
        (optList tF?).Perm (t.toList.erase u) ∧
        (optList tF?).map (fun id => endOfKey (x.keyOf id)) = fullTour s'.ord s'.rf.F hvalid'.compat.forest r ∧
        (∀ id, 1 ≤ id → id ≤ x.numNodes → id ≠ u →
          (∃ w', endOfKey (x.keyOf id) ∈ s'.ord w') →
          (sF.nodes id).val =
            { isOpen := decide ((endOfKey (x.keyOf id)).1 ∉ s.rf.F.E)
              isMarked := decide (endOfKey (x.keyOf id) ∈ s'.marked)
              rootTag := tourRootTagVal s' (endOfKey (x.keyOf id)) }) ∧
        (sF.nodes u).val.rootTag = 0 ∧
        (∀ id ≤ x.numNodes, (∀ w', endOfKey (x.keyOf id) ∉ s.ord w') ∨ id = 0 ∨ x.numNodes < id →
          (sF.nodes id).val = (x.st.nodes id).val) ∧
        cTail + TOUR_PHI_MULT * forestPhi (AuxTree.node u .leaf .leaf :: optTrees tF? ++ rest) ≤
          TOUR_PHI_MULT * forestPhi (t :: rest) +
            (2 * TOUR_FIND_AMORT + 2 * TOUR_SEQ_AMORT) * (Nat.log 2 (x.numNodes + 2) + 1) + 200 :=
    fun tF? sF stF cTail a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 =>
      ⟨tF?, sF, stF, cTail, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩
  by_cases hvR : v ∈ s.rf.R
  · -- `v ∈ s.rf.R`: clear `u`'s `rootTag`, delete `u`, and if `newFe ≠ 0` set `v + 1` on `newFe` + `rotateFront newFe`!
    have hr_eq_v : r = v := (h.valid.unique_root v (h.valid.compat.vert v (List.ne_nil_of_mem hxv))).unique
      (h.valid.root_spec (h.valid.compat.vert v (List.ne_nil_of_mem hxv))) ⟨hvR, connected_refl _ v⟩
    have hir1 : irV = 1 := by simp [irV, hvR]
    have hcond_ir : (Expr.reg 15).eval w { stN with mem := memN1, regs := rI2 } = some 1 := by simp [Expr.eval, hrI2_15, irV, hvR]
    set rA1 := Function.update rI2 16 1
    set rA2 := Function.update rA1 17 0
    have hA1 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 16) (val := 1) (st := { stN with mem := memN1, regs := rI2 }) (by omega)
    have hA2 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 17) (val := 0) (st := { stN with mem := memN1, regs := rA1 }) (by omega)
    obtain ⟨t₁, s₁, o₁, st₁, c₁, hrun₁, hn₁, hfr₁, hinv₁, hvals₁, _, _, hlist₁, hvalU₁, hvalne₁, _, hcost₁⟩ :=
      tourSetValNodeBody_runs (fuel := 2 * eCap + 2) (pos := stN.pos) C ω hnN1 hinv_p (h.valsOk hw) hu_t' (by omega) (by have := h.numNodes_le; omega)
        (isOpen := 1) (isMarked := 0) (rootTag := 0) (by omega) hheapN1
    have hA3 := runs_call_regs7 18 9 6 16 17 17 10 2 (st := { stN with mem := memN1, regs := rA2 }) C.setValNode_body
      (by simp [rA2, rA1, hrI2_9]) (by simp [rA2, rA1, hrI2_6])
      (by simp [rA2, rA1]) (by simp [rA2]) (by simp [rA2])
      (by simp [rA2, rA1, hrI2_10]) (by simp [rA2, rA1, hrI2_2]) hrun₁
    set rA3 := Function.update rA2 18 o₁.value
    have hu_t1 : u ∈ t₁.toList := by rw [hlist₁]; exact hu_t'
    obtain ⟨t₂?, s₂, o₂, st₂, c₂, hrun₂, _, hn₂, hfr₂, hinv₂, hvals₂, hlist₂, hval₂, _, hcost₂⟩ :=
      tourDeleteNodeBody_runs (fuel := 2 * eCap + 2) (pos := st₁.pos) C.toTourSplayOpsProcs ω hn₁ hinv₁ hvals₁ hu_t1
        (by have := h.numNodes_le; omega) (by omega) ⟨hheapN1.rec_le, hheapN1.room, hfr₁.1, hheapN1.wide⟩
    have hA4 := runs_call_regs4 18 9 6 10 2 (st := { st₁ with regs := rA3 }) C.deleteNode_body
      (by simp [rA3, rA2, rA1, hrI2_9]) (by simp [rA3, rA2, rA1, hrI2_6])
      (by simp [rA3, rA2, rA1, hrI2_10]) (by simp [rA3, rA2, rA1, hrI2_2]) hrun₂
    set rA4 := Function.update rA3 18 o₂.value
    have hlist₂' : optList t₂? = t.toList.erase u := by rw [hlist₂, hlist₁]
    cases hhd' : (s'.ord v).head? with
    | none =>
      have hnf0 : newFe = 0 := by rw [hnewFe_eq, show ((tourDropOneAbs s (endOfKey keyX)).ord v).head? = none from hhd']
      have hcond_nf : (Expr.reg 14).eval w { st₂ with regs := rA4 } = some 0 := by
        simp [Expr.eval, rA4, rA3, rA2, rA1, hrI2_14, hnf0]
      have hs'_ord_v0 : s'.ord v = [] := List.head?_eq_none_iff.mp hhd'
      have hft_nil : fullTour s'.ord s'.rf.F hvalid'.compat.forest r = [] := by
        rw [hr_eq_v]; exact (fullTour_eq_nil_iff hvalid'.compat v).mpr hs'_ord_v0
      have ht₂_map : (optList t₂?).map (fun id => endOfKey (x.keyOf id)) = fullTour s'.ord s'.rf.F hvalid'.compat.forest r := by
        rw [hlist₂']; have h1 := List.Perm.nil_eq (hft_nil ▸ ht_erase_rot.perm.symm); rw [← h1, hft_nil]
      refine hClose1 t₂? s₂ { st₂ with regs := rA4 } _
        (tour_runs_cond_true hcond_ir (by omega) (tour_runs_seq_normal hA1 (tour_runs_seq_normal hA2
          (tour_runs_seq_normal hA3 (tour_runs_seq_normal hA4 (tour_runs_cond_false hcond_nf (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩)))))))
        (by simp [rA4, rA3, rA2, rA1, hrI2_2]) hn₂ (hfr₁.trans hfr₂) hinv₂
        (by rw [hlist₂']) ht₂_map ?_ (by rw [hval₂ u hu_le', hvalU₁]) ?_
        (by
          have hmul : TOUR_FIND_AMORT * (Nat.log 2 (x.numNodes + 2) + 1) + TOUR_SEQ_AMORT * (Nat.log 2 (x.numNodes + 2) + 1) ≤
              (2 * TOUR_FIND_AMORT + 2 * TOUR_SEQ_AMORT) * (Nat.log 2 (x.numNodes + 2) + 1) := by
            have : (TOUR_FIND_AMORT + TOUR_SEQ_AMORT) * (Nat.log 2 (x.numNodes + 2) + 1) ≤
                (2 * TOUR_FIND_AMORT + 2 * TOUR_SEQ_AMORT) * (Nat.log 2 (x.numNodes + 2) + 1) :=
              Nat.mul_le_mul_right _ (by unfold TOUR_FIND_AMORT TOUR_SEQ_AMORT; omega)
            nlinarith
          clear * - hcost₁ hcost₂ hmul; simp only [Expr.size, TOUR_PHI_MULT] at *; omega)
      · intro id h1 h2 hiu hact
        have hcap : id ≤ x.numNodes := h2
        rw [hval₂ id hcap, hvalne₁ id hcap hiu]
        obtain ⟨w', hw'⟩ := hact
        have hw'0 : endOfKey (x.keyOf id) ∈ s.ord w' := (List.mem_filter.mp hw').1
        have hne_x : endOfKey (x.keyOf id) ≠ endOfKey keyX := bne_iff_ne.mp (List.mem_filter.mp hw').2
        rw [h.val_active id h1 h2 ⟨w', hw'0⟩]
        have hmk_eq : decide (endOfKey (x.keyOf id) ∈ s'.marked) = decide (endOfKey (x.keyOf id) ∈ s.marked) := by
          simp [s', tourDropOneAbs, hne_x]
        have hrt_eq : tourRootTagVal s' (endOfKey (x.keyOf id)) = tourRootTagVal s (endOfKey (x.keyOf id)) := by
          by_cases hex' : ∃ r' ∈ s.rf.R, (s.ord r').head? = some (endOfKey (x.keyOf id))
          · obtain ⟨r', hr'R, hr'h⟩ := hex'
            have hrv : r' ≠ v := fun heq => by subst heq; rw [hhead_x] at hr'h; exact hne_x (Option.some.inj hr'h).symm
            rw [tourRootTagVal_eq_succ h.valid hr'R hr'h,
              tourRootTagVal_eq_succ hvalid' hr'R (by rw [hord'_upd, Function.update_of_ne hrv]; exact hr'h)]
          · push Not at hex'
            rw [tourRootTagVal_eq_zero hex', tourRootTagVal_eq_zero]
            intro r' hr' hh
            by_cases hrv : r' = v
            · subst hrv; rw [hhd'] at hh; cases hh
            · exact hex' r' hr' (by simpa [hord'_upd, Function.update_of_ne hrv] using hh)
        rw [hmk_eq, hrt_eq]
      · intro id hid hc
        have hiu : id ≠ u := by
          rcases hc with hno | rfl | hgt
          · intro heq; subst heq; exact hno v (by rwa [hu_key'])
          · omega
          · omega
        rw [hval₂ id hid, hvalne₁ id hid hiu]
    | some aNew =>
      have haNew_mem' : aNew ∈ s'.ord v := List.mem_of_head? hhd'
      have haNew_mem : aNew ∈ s.ord v := (List.mem_filter.mp haNew_mem').1
      have haNew_ne : aNew ≠ endOfKey keyX := bne_iff_ne.mp (List.mem_filter.mp haNew_mem').2
      have haNew_lt : endKey aNew < 2 * eCap := by
        have := h.valid.ordWithin.2.2 v aNew haNew_mem; simp only [endKey]; cases aNew.2 <;> simp <;> omega
      have hnf_eq : newFe = x.nodeOf (endKey aNew) := by
        rw [hnewFe_eq, show ((tourDropOneAbs s (endOfKey keyX)).ord v).head? = some aNew from hhd']
      have hnf_nz : newFe ≠ 0 := hnf_eq ▸ (h.active_end v hvLt aNew haNew_mem).1
      have hnf_cap : newFe ≤ x.numNodes := hnf_eq ▸ (h.nodeOf_mem _ haNew_lt).2
      have hnf_key : x.keyOf newFe = endKey aNew := by rw [hnf_eq]; exact h.nodeOf_keyOf _ haNew_lt (hnf_eq ▸ hnf_nz)
      have hnf_ne_u : newFe ≠ u := fun heq => haNew_ne (by rw [← endOfKey_endKey aNew, ← hnf_key, heq, hu_key'])
      have hcond_nf : (Expr.reg 14).eval w { st₂ with regs := rA4 } = some newFe := by
        simp [Expr.eval, rA4, rA3, rA2, rA1, hrI2_14]
      -- `t₂?` must be `some t₂` containing `newFe`!
      have hnf_in_erase : newFe ∈ t.toList.erase u := by
        have hnf_t : newFe ∈ t.toList := by
          have ha_ft : aNew ∈ fullTour s.ord s.rf.F h.valid.compat.forest r :=
            ((fullTour_spec h.valid.compat r).2 aNew).mpr ⟨v, haNew_mem, connected_symm (h.valid.root_spec (h.valid.compat.vert v (List.ne_nil_of_mem hxv))).2⟩
          rw [← ht_map] at ha_ft; obtain ⟨id, hid, hida⟩ := List.mem_map.mp ha_ft
          have hid_in := (h.nodes_exact id).mp (List.mem_flatMap.mpr ⟨t, hperm_r.mem_iff.mpr (by simp), hid⟩)
          have hkeq : x.keyOf id = endKey aNew := by rw [← hida, endKey_endOfKey']
          have : id = newFe := by rw [hnf_eq, ← hkeq, (h.keyOf_mem id hid_in.1 hid_in.2).2.2]
          exact this ▸ hid
        exact ((hinv_p.treesInv t (by simp)).nodup.mem_erase_iff).mpr ⟨hnf_ne_u, hnf_t⟩
      cases ht₂c : t₂? with
      | none =>
        rw [ht₂c] at hlist₂'; simp only [optList, Option.elim] at hlist₂'
        rw [← hlist₂'] at hnf_in_erase; simp at hnf_in_erase
      | some t₂ =>
        rw [ht₂c] at hinv₂ hlist₂' hcost₂
        have hnf_t2 : newFe ∈ t₂.toList := by
          simp only [optList, Option.elim] at hlist₂'; rwa [hlist₂']
        have hperm2 : (AuxTree.node u .leaf .leaf :: optTrees (some t₂) ++ rest).Perm
            (t₂ :: AuxTree.node u .leaf .leaf :: rest) := by
          simp only [optTrees, Option.toList, List.cons_append, List.nil_append]; exact List.Perm.swap _ _ rest
        have hinv₂_sw : TourForestInv x.numNodes s₂ (t₂ :: AuxTree.node u .leaf .leaf :: rest) := (hinv₂.perm hperm2).1
        set opN := if (s₂.nodes newFe).val.isOpen then 1 else 0
        set mkN := if (s₂.nodes newFe).val.isMarked then 1 else 0
        have hm2_opN : st₂.mem (nodesBase b vCap eCap + 17 * newFe + 9) = opN := by
          have hnd := hn₂ newFe hnf_cap; simpa [NodeLayout.nodeAddr, tourLayout_stride, OFF_VAL, opN, Nat.add_assoc] using hnd.2.2.2.2.2.2.1.2.2.2.1
        have hm2_mkN : st₂.mem (nodesBase b vCap eCap + 17 * newFe + 10) = mkN := by
          have hnd := hn₂ newFe hnf_cap; simpa [NodeLayout.nodeAddr, tourLayout_stride, OFF_VAL, mkN, Nat.add_assoc] using hnd.2.2.2.2.2.2.1.2.2.2.2.1
        have hheap2 : HeapOk tourLayout w (nodesBase b vCap eCap) x.numNodes hN 2 st₂.mem :=
          ⟨hheapN1.rec_le, hheapN1.room, (hfr₁.trans hfr₂).1, hheapN1.wide⟩
        obtain ⟨t₃, s₃, o₃, st₃, c₃, hrun₃, hn₃, hfr₃, hinv₃, hvals₃, _, _, hlist₃, hvalN₃, hvalne₃, _, hcost₃⟩ :=
          tourSetValNodeBody_runs (fuel := 2 * eCap + 2) (pos := st₂.pos) C ω hn₂ hinv₂_sw hvals₂ hnf_t2 (by omega) (by have := h.numNodes_le; omega)
            (isOpen := opN) (isMarked := mkN) (rootTag := v + 1) (by omega) hheap2
        have hnf_t3 : newFe ∈ t₃.toList := by rw [hlist₃]; exact hnf_t2
        obtain ⟨t₄, s₄, o₄, st₄, c₄, hrun₄, _, hn₄, hfr₄, hinv₄, _, _, hrot₄, hval₄, _, hcost₄⟩ :=
          tourRotateFrontBody_runs (fuel := 2 * eCap + 2) (pos := st₃.pos) C.toTourSplayOpsProcs ω hn₃ hinv₃ hvals₃ hnf_t3
            (by have := h.numNodes_le; omega) (by omega) ⟨hheap2.rec_le, hheap2.room, hfr₃.1, hheap2.wide⟩
        -- Execute the 6-statement `if newFe ≠ 0` block
        have hAnf : nodesBase b vCap eCap + 17 * newFe + 17 < 2 ^ w := by
          have := hheap2.addr_lt hnf_cap; simp [NodeLayout.nodeAddr, tourLayout_stride] at this; omega
        set rB1 := Function.update rA4 15 (nodesBase b vCap eCap + 17 * newFe)
        set rB2 := Function.update rB1 16 opN
        set rB3 := Function.update rB2 17 mkN
        set rB4 := Function.update rB3 18 (v + 1)
        have hB1 : Runs w p ω (.assign 15 (.bin .add (.reg 9) (.bin .mul (.const 17) (.reg 14))))
            { st₂ with regs := rA4 } .normal { st₂ with regs := rB1 } 6 :=
          runs_assign_iff.mpr ⟨nodesBase b vCap eCap + 17 * newFe, by
            simp [Expr.eval, rA4, rA3, rA2, rA1, hrI2_9, hrI2_14, BinOp.eval,
              (by omega : 17 < 2 ^ w), (by omega : 17 * newFe < 2 ^ w),
              (by omega : nodesBase b vCap eCap + 17 * newFe < 2 ^ w)], rfl, rfl, rfl⟩
        have hB2 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 16) (rBase := 15) (off := 9)
          (b := nodesBase b vCap eCap + 17 * newFe) (val := opN) (st := { st₂ with regs := rB1 })
          (by simp [rB1]) (by omega) (by omega) hm2_opN
        have hB3 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 17) (rBase := 15) (off := 10)
          (b := nodesBase b vCap eCap + 17 * newFe) (val := mkN) (st := { st₂ with regs := rB2 })
          (by simp [rB2, rB1]) (by omega) (by omega) hm2_mkN
        have hB4 : Runs w p ω (.assign 18 (.bin .add (.reg 5) (.const 1)))
            { st₂ with regs := rB3 } .normal { st₂ with regs := rB4 } 4 :=
          runs_assign_iff.mpr ⟨v + 1, by
            simp [Expr.eval, rB3, rB2, rB1, rA4, rA3, rA2, rA1, hrI2_5,
              BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : v + 1 < 2 ^ w)], rfl, rfl, rfl⟩
        have hB5 := runs_call_regs7 19 9 14 16 17 18 10 2 (st := { st₂ with regs := rB4 }) C.setValNode_body
          (by simp [rB4, rB3, rB2, rB1, rA4, rA3, rA2, rA1, hrI2_9])
          (by simp [rB4, rB3, rB2, rB1, rA4, rA3, rA2, rA1, hrI2_14])
          (by simp [rB4, rB3, rB2]) (by simp [rB4, rB3]) (by simp [rB4])
          (by simp [rB4, rB3, rB2, rB1, rA4, rA3, rA2, rA1, hrI2_10])
          (by simp [rB4, rB3, rB2, rB1, rA4, rA3, rA2, rA1, hrI2_2]) hrun₃
        set rB5 := Function.update rB4 19 o₃.value
        have hB6 := runs_call_regs4 19 9 14 10 2 (st := { st₃ with regs := rB5 }) C.rotateFront_body
          (by simp [rB5, rB4, rB3, rB2, rB1, rA4, rA3, rA2, rA1, hrI2_9])
          (by simp [rB5, rB4, rB3, rB2, rB1, rA4, rA3, rA2, rA1, hrI2_14])
          (by simp [rB5, rB4, rB3, rB2, rB1, rA4, rA3, rA2, rA1, hrI2_10])
          (by simp [rB5, rB4, rB3, rB2, rB1, rA4, rA3, rA2, rA1, hrI2_2]) hrun₄
        have hrun_nf := tour_runs_cond_true (s₂ := .nop) hcond_nf hnf_nz
          (tour_runs_seq_normal hB1 (tour_runs_seq_normal hB2 (tour_runs_seq_normal hB3
            (tour_runs_seq_normal hB4 (tour_runs_seq_normal hB5 hB6)))))
        have hperm4 : (t₄ :: AuxTree.node u .leaf .leaf :: rest).Perm
            (AuxTree.node u .leaf .leaf :: optTrees (some t₄) ++ rest) := by
          simp only [optTrees, Option.toList, List.cons_append, List.nil_append]; exact List.Perm.swap _ _ rest
        have ht₄_map : (optList (some t₄)).map (fun id => endOfKey (x.keyOf id)) =
            fullTour s'.ord s'.rf.F hvalid'.compat.forest r := by
          simp only [optList, Option.elim, hrot₄]
          have ht3_eq : t₃.toList = t.toList.erase u := by rw [hlist₃]; simpa [optList] using hlist₂'
          rw [ht3_eq]
          have hinj : ∀ a ∈ t.toList.erase u, ∀ b ∈ t.toList.erase u,
              endOfKey (x.keyOf a) = endOfKey (x.keyOf b) → a = b := by
            intro a ha b hb hab
            have ha' := (h.nodes_exact a).mp (List.mem_flatMap.mpr ⟨t, hperm_r.mem_iff.mpr (by simp), List.mem_of_mem_erase ha⟩)
            have hb' := (h.nodes_exact b).mp (List.mem_flatMap.mpr ⟨t, hperm_r.mem_iff.mpr (by simp), List.mem_of_mem_erase hb⟩)
            have hka : x.keyOf a = x.keyOf b := by rw [← endKey_endOfKey' (x.keyOf a), hab, endKey_endOfKey']
            rw [← (h.keyOf_mem a ha'.1 ha'.2).2.2, hka, (h.keyOf_mem b hb'.1 hb'.2).2.2]
          have hrot_m : (rotateNatList newFe (t.toList.erase u)).map (fun id => endOfKey (x.keyOf id)) =
              rotateToList aNew ((t.toList.erase u).map fun id => endOfKey (x.keyOf id)) := by
            have hidx : ((t.toList.erase u).map fun id => endOfKey (x.keyOf id)).idxOf aNew = (t.toList.erase u).idxOf newFe := by
              rw [← show endOfKey (x.keyOf newFe) = aNew by rw [hnf_key, endOfKey_endKey]]
              clear * - hinj hnf_in_erase
              generalize t.toList.erase u = ls at hinj hnf_in_erase ⊢
              induction ls with
              | nil => simp at hnf_in_erase
              | cons z zs ih =>
                by_cases hzn : z = newFe
                · subst hzn; simp
                · have hne : endOfKey (x.keyOf z) ≠ endOfKey (x.keyOf newFe) := fun heq => hzn (hinj z (by simp) newFe hnf_in_erase heq)
                  have hnzs : newFe ∈ zs := (List.mem_cons.mp hnf_in_erase).resolve_left (Ne.symm hzn)
                  simp [List.idxOf_cons_ne _ hzn, List.idxOf_cons_ne _ hne,
                    ih (fun a ha b hb => hinj a (by simp [ha]) b (by simp [hb])) hnzs]
            have ham : aNew ∈ (t.toList.erase u).map (fun id => endOfKey (x.keyOf id)) :=
              List.mem_map.mpr ⟨newFe, hnf_in_erase, by rw [hnf_key, endOfKey_endKey]⟩
            simp [rotateNatList, rotateToList, hnf_in_erase, ham, hidx, List.map_append, List.map_drop, List.map_take]
          rw [hrot_m]
          have hhd_r : (s'.ord r).head? = some aNew := hr_eq_v ▸ hhd'
          exact tour_rotateToList_eq_of_isRotated (fullTour_spec hvalid'.compat r).1 ht_erase_rot (fullTour_head? hvalid'.compat r hhd_r)
        refine hClose1 (some t₄) s₄ { st₄ with regs := Function.update rB5 19 o₄.value } _
          (tour_runs_cond_true hcond_ir (by omega) (tour_runs_seq_normal hA1 (tour_runs_seq_normal hA2
            (tour_runs_seq_normal hA3 (tour_runs_seq_normal hA4 hrun_nf)))))
          (by simp [rB5, rB4, rB3, rB2, rB1, rA4, rA3, rA2, rA1, hrI2_2])
          hn₄ (hfr₁.trans (hfr₂.trans (hfr₃.trans hfr₄))) (hinv₄.perm hperm4).1
          (by simp only [optList, Option.elim, hrot₄]; exact (rotateNatList_perm hnf_t3).trans (List.Perm.of_eq (by rw [hlist₃]; simpa [optList] using hlist₂')))
          ht₄_map ?_
          (by rw [hval₄ u hu_le', hvalne₃ u hu_le' hnf_ne_u.symm,
                hval₂ u hu_le', hvalU₁]) ?_ ?_
        · intro id h1 h2 hiu hact
          have hcap : id ≤ x.numNodes := h2
          obtain ⟨w', hw'⟩ := hact
          have hw'0 : endOfKey (x.keyOf id) ∈ s.ord w' := (List.mem_filter.mp hw').1
          have hne_x : endOfKey (x.keyOf id) ≠ endOfKey keyX := bne_iff_ne.mp (List.mem_filter.mp hw').2
          have hmk_eq : decide (endOfKey (x.keyOf id) ∈ s'.marked) = decide (endOfKey (x.keyOf id) ∈ s.marked) := by
            simp [s', tourDropOneAbs, hne_x]
          rw [hval₄ id hcap]
          by_cases hidn : id = newFe
          · subst hidn
            have hrt_n : tourRootTagVal s' (endOfKey (x.keyOf id)) = v + 1 := by
              rw [hnf_key, endOfKey_endKey]; exact tourRootTagVal_eq_succ hvalid' hvR hhd'
            have hval_old := h.val_active id h1 h2 ⟨w', hw'0⟩
            have hop : decide (0 < opN) = decide ((endOfKey (x.keyOf id)).1 ∉ s.rf.F.E) := by
              simp only [opN, hval₂ id hcap, hvalne₁ id hcap hiu, hval_old]
              by_cases ho : (endOfKey (x.keyOf id)).1 ∈ s.rf.F.E <;> simp [ho]
            have hmk : decide (0 < mkN) = decide (endOfKey (x.keyOf id) ∈ s'.marked) := by
              rw [hmk_eq]; simp only [mkN, hval₂ id hcap, hvalne₁ id hcap hiu, hval_old]
              by_cases hm : endOfKey (x.keyOf id) ∈ s.marked <;> simp [hm]
            rw [hvalN₃, hrt_n, ← hop, ← hmk]
          · rw [hvalne₃ id hcap hidn, hval₂ id hcap, hvalne₁ id hcap hiu, h.val_active id h1 h2 ⟨w', hw'0⟩, hmk_eq]
            have hne_new : endOfKey (x.keyOf id) ≠ aNew := fun heq => hidn (by
              rw [hnf_eq, ← heq, endKey_endOfKey', (h.keyOf_mem id h1 h2).2.2])
            have hrt_eq : tourRootTagVal s' (endOfKey (x.keyOf id)) = tourRootTagVal s (endOfKey (x.keyOf id)) := by
              by_cases hex' : ∃ r' ∈ s.rf.R, (s.ord r').head? = some (endOfKey (x.keyOf id))
              · obtain ⟨r', hr'R, hr'h⟩ := hex'
                have hrv : r' ≠ v := fun heq => by subst heq; rw [hhead_x] at hr'h; exact hne_x (Option.some.inj hr'h).symm
                rw [tourRootTagVal_eq_succ h.valid hr'R hr'h,
                  tourRootTagVal_eq_succ hvalid' hr'R (by rw [hord'_upd, Function.update_of_ne hrv]; exact hr'h)]
              · push Not at hex'
                rw [tourRootTagVal_eq_zero hex', tourRootTagVal_eq_zero]
                intro r' hr' hh
                by_cases hrv : r' = v
                · subst hrv; rw [hhd'] at hh; exact hne_new (Option.some.inj hh).symm
                · exact hex' r' hr' (by simpa [hord'_upd, Function.update_of_ne hrv] using hh)
            rw [hrt_eq]
        · intro id hid hc
          have hiu : id ≠ u := by
            rcases hc with hno | rfl | hgt
            · intro heq; subst heq; exact hno v (by rwa [hu_key'])
            · omega
            · omega
          have hidn : id ≠ newFe := by
            rcases hc with hno | rfl | hgt
            · intro heq; subst heq; exact hno v (by rw [hnf_key, endOfKey_endKey]; exact haNew_mem)
            · omega
            · have := hnf_eq ▸ (h.nodeOf_mem _ haNew_lt).2; omega
          rw [hval₄ id hid, hvalne₃ id hid hidn, hval₂ id hid, hvalne₁ id hid hiu]
        · rw [← forestPhi_perm hperm4]; rw [forestPhi_perm hperm2] at hcost₂
          have hsum : TOUR_FIND_AMORT * (Nat.log 2 (x.numNodes + 2) + 1) +
              TOUR_SEQ_AMORT * (Nat.log 2 (x.numNodes + 2) + 1) +
              TOUR_FIND_AMORT * (Nat.log 2 (x.numNodes + 2) + 1) +
              TOUR_SEQ_AMORT * (Nat.log 2 (x.numNodes + 2) + 1) =
              (2 * TOUR_FIND_AMORT + 2 * TOUR_SEQ_AMORT) * (Nat.log 2 (x.numNodes + 2) + 1) := by ring
          clear * - hcost₁ hcost₂ hcost₃ hcost₄ hsum; simp only [Expr.size, TOUR_PHI_MULT] at *; omega
  · -- `v ∉ s.rf.R`: only `firstEnd[v] := newFe` and `deleteNode u`!
    have hir0 : irV = 0 := by simp [irV, hvR]
    have hcond_ir : (Expr.reg 15).eval w { stN with mem := memN1, regs := rI2 } = some 0 := by simp [Expr.eval, hrI2_15, irV, hvR]
    have hrv_ne : r ≠ v := fun heq => hvR (heq ▸ hrR)
    obtain ⟨t₂?, s₂, o₂, st₂, c₂, hrun₂, _, hn₂, hfr₂, hinv₂, _, hlist₂, hval₂, _, hcost₂⟩ :=
      tourDeleteNodeBody_runs (fuel := 2 * eCap + 2) (pos := stN.pos) C.toTourSplayOpsProcs ω hnN1 hinv_p (h.valsOk hw) hu_t'
        (by have := h.numNodes_le; omega) (by omega) hheapN1
    have hcall_del := runs_call_regs4 18 9 6 10 2 (st := { stN with mem := memN1, regs := rI2 }) C.deleteNode_body
      (by simp [hrI2_9]) (by simp [hrI2_6])
      (by simp [hrI2_10]) (by simp [hrI2_2]) hrun₂
    -- `t.toList` starts at `firstEnd[r] ≠ u`, so `t.toList.erase u` still starts at `firstEnd[r]`!
    have ht₂_map : (optList t₂?).map (fun id => endOfKey (x.keyOf id)) = fullTour s'.ord s'.rf.F hvalid'.compat.forest r := by
      rw [hlist₂]
      have hord_r_ne : s.ord r ≠ [] := fun h0 => by
        have := (fullTour_eq_nil_iff h.valid.compat r).mpr h0
        rw [← ht_map] at this; have hne := hinv_p.nonEmpty t (by simp)
        have hnil := List.map_eq_nil_iff.mp this; cases t <;> simp [AuxTree.toList] at hne hnil
      obtain ⟨aR, haR⟩ : ∃ aR, (s.ord r).head? = some aR := by
        cases ho : s.ord r with | nil => exact absurd ho hord_r_ne | cons aR _ => exact ⟨aR, rfl⟩
      have hhd_t : (t.toList.map fun id => endOfKey (x.keyOf id)).head? = some aR := by
        rw [ht_map]; exact fullTour_head? h.valid.compat r haR
      have haR_ne_x : aR ≠ endOfKey keyX := fun heq =>
        hrv_ne (h.valid.compat.unique r v aR (List.mem_of_head? haR) (heq ▸ hxv))
      cases htc : t.toList with
      | nil => rw [htc] at hu_t'; simp at hu_t'
      | cons t0 ts =>
        have ht0_eq : endOfKey (x.keyOf t0) = aR := by rw [htc] at hhd_t; simpa using hhd_t
        have ht0_ne_u : t0 ≠ u := fun heq => haR_ne_x (by rw [← ht0_eq, heq, hu_key'])
        have hhd_er : ((t.toList.erase u).map fun id => endOfKey (x.keyOf id)).head? = some aR := by
          rw [htc, List.erase_cons]; simp [beq_false_of_ne ht0_ne_u, ht0_eq]
        have hhd_s' : (s'.ord r).head? = some aR := by rw [hord'_upd, Function.update_of_ne hrv_ne]; exact haR
        rw [← htc]
        have h1 := tour_rotateToList_eq_of_isRotated (ht_erase_rot.perm.nodup_iff.mpr (fullTour_spec hvalid'.compat r).1)
          (List.IsRotated.refl _) hhd_er
        have h2 := tour_rotateToList_eq_of_isRotated (fullTour_spec hvalid'.compat r).1 ht_erase_rot
          (fullTour_head? hvalid'.compat r hhd_s')
        exact h1.symm.trans h2
    refine hClose1 t₂? s₂ { st₂ with regs := Function.update rI2 18 o₂.value } _
      (tour_runs_cond_false hcond_ir hcall_del)
      (by simp [hrI2_2]) hn₂ hfr₂ hinv₂ (by rw [hlist₂]) ht₂_map ?_
      (by rw [hval₂ u hu_le', h.val_active u hu1' hu_le' ⟨v, by rwa [hu_key']⟩, hu_key']
          apply tourRootTagVal_eq_zero; intro r' hr' hh
          exact hvR ((h.valid.compat.unique r' v (endOfKey keyX) (List.mem_of_head? hh) hxv) ▸ hr'))
      (fun id hid _ => hval₂ id hid)
      (by
        have hmul : TOUR_SEQ_AMORT * (Nat.log 2 (x.numNodes + 2) + 1) ≤
            (2 * TOUR_FIND_AMORT + 2 * TOUR_SEQ_AMORT) * (Nat.log 2 (x.numNodes + 2) + 1) :=
          Nat.mul_le_mul_right _ (by unfold TOUR_FIND_AMORT TOUR_SEQ_AMORT; omega)
        clear * - hcost₂ hmul; simp only [Expr.size, TOUR_PHI_MULT] at *; omega)
    intro id h1 h2 hiu hact
    have hcap : id ≤ x.numNodes := h2
    obtain ⟨w', hw'⟩ := hact
    have hw'0 : endOfKey (x.keyOf id) ∈ s.ord w' := (List.mem_filter.mp hw').1
    have hne_x : endOfKey (x.keyOf id) ≠ endOfKey keyX := bne_iff_ne.mp (List.mem_filter.mp hw').2
    rw [hval₂ id hcap, h.val_active id h1 h2 ⟨w', hw'0⟩]
    have hmk_eq : decide (endOfKey (x.keyOf id) ∈ s'.marked) = decide (endOfKey (x.keyOf id) ∈ s.marked) := by
      simp [s', tourDropOneAbs, hne_x]
    have hrt_eq : tourRootTagVal s' (endOfKey (x.keyOf id)) = tourRootTagVal s (endOfKey (x.keyOf id)) := by
      by_cases hex' : ∃ r' ∈ s.rf.R, (s.ord r').head? = some (endOfKey (x.keyOf id))
      · obtain ⟨r', hr'R, hr'h⟩ := hex'
        have hr'v : r' ≠ v := fun heq => hvR (heq ▸ hr'R)
        rw [tourRootTagVal_eq_succ h.valid hr'R hr'h,
          tourRootTagVal_eq_succ hvalid' hr'R (by rw [hord'_upd, Function.update_of_ne hr'v]; exact hr'h)]
      · push Not at hex'
        rw [tourRootTagVal_eq_zero hex', tourRootTagVal_eq_zero]
        intro r' hr' hh
        have hr'v : r' ≠ v := fun heq => hvR (heq ▸ hr')
        exact hex' r' hr' (by simpa [hord'_upd, Function.update_of_ne hr'v] using hh)
    rw [hmk_eq, hrt_eq]

end MinCostFlow.SparseCore.Program
