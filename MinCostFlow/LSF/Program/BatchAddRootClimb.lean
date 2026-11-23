module

public import MinCostFlow.LSF.Program.BatchAddRootClimbBase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Header-Load, Setup, and `T_H`-Climb Verification for `addOrigRootProc` (`BatchAddRootClimb`)

Verifies the header-load, slow-path setup, and `T_H`-climbing stages of `addOrigRootProc`
(`addOrigRootHdr_triple`, `addOrigRootSetup_triple`, `addOrigRootClimb_runs`).
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## Header-load, slow-path setup, and `T_H` climb verifications -/

lemma addOrigRootHdr_triple {w b u : ℕ} {p : Program} {S : LSFState} {x : LSFConcrete}
    {mem : ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w) (hend_ltw : x.endAddr b < 2 ^ w)
    (hrep : (LSFRep x.h).rep b S x mem) :
    Triple w p
      (fun st => st.mem = mem ∧ st.regs 0 = b ∧ st.regs 1 = u)
      addOrigRootHdrStmt
      (normalPost fun st' =>
        st'.mem = mem ∧ st'.regs 0 = b ∧ st'.regs 1 = u ∧
        st'.regs 2 = x.vCap ∧ st'.regs 3 = x.eCap ∧ st'.regs 4 = x.n0 ∧ st'.regs 5 = x.tM ∧
        st'.regs 6 = lsfTBlockPtr b x.vCap x.eCap ∧
        st'.regs 7 = lsfDgFPtr b x.vCap x.eCap x.tM ∧
        st'.regs 8 = lsfFAncPtr b x.vCap x.eCap x.n0 x.tM ∧
        st'.regs 9 = lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w ∧
        st'.regs 10 = fIsRootBase (lsfFAncPtr b x.vCap x.eCap x.n0 x.tM))
      (fun _ => 70) := by
  set vCap := x.vCap; set eCap := x.eCap; set n0 := x.n0; set tM := x.tM; set L_w := x.L_w
  have hlay := addRoot_layout hend_ltw
  rcases hrep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hhdr, _, _, _, hFAnc, _⟩
  rcases hhdr with ⟨h0_vC, h1_eC, h2_n0, _, _, h5_tP, h6_dgF, h7_fA, _, _, _, _, _, _, _, _,
    _, _, h18_aux, _, _, _, h22_tM, _⟩
  rcases hFAnc with ⟨_, hIsR_ptr, _⟩
  have hhdr_ltw : b + lsfHdrSize < 2 ^ w := by omega
  have hf_hdr_ltw : lsfFAncPtr b x.vCap x.eCap x.n0 x.tM + 6 < 2 ^ w := by
    dsimp [fAncSize, fAncHdrSize] at hlay; omega
  intro st ω ⟨hmem, hr0, hr1⟩
  subst hmem
  dsimp only [addOrigRootHdrStmt]
  refine runs_start_le ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := vCap) (by
    dsimp [lsfOffVCap, lsfHdrSize] at hhdr_ltw ⊢; rw [show b = b + 0 from rfl]; eval_expr) h0_vC) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := eCap) (by dsimp [lsfOffECap, lsfHdrSize] at hhdr_ltw ⊢; eval_expr) h1_eC) ?_; dsimp only
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := n0) (by dsimp [lsfOffN0, lsfHdrSize] at hhdr_ltw ⊢; eval_expr) h2_n0) ?_; dsimp only
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := tM) (by dsimp [lsfOffTM, lsfHdrSize] at hhdr_ltw ⊢; eval_expr) h22_tM) ?_; dsimp only
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := lsfTBlockPtr b vCap eCap) (by dsimp [lsfOffTPtr, lsfHdrSize] at hhdr_ltw ⊢; eval_expr) h5_tP) ?_; dsimp only
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := lsfDgFPtr b vCap eCap tM) (by dsimp [lsfOffDgFPtr, lsfHdrSize] at hhdr_ltw ⊢; eval_expr) h6_dgF) ?_; dsimp only
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := lsfFAncPtr b vCap eCap n0 tM) (by dsimp [lsfOffFAncPtr, lsfHdrSize] at hhdr_ltw ⊢; eval_expr) h7_fA) ?_; dsimp only
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := lsfAuxPtr b vCap eCap n0 tM L_w) (by dsimp [lsfOffAuxPtr, lsfHdrSize] at hhdr_ltw ⊢; eval_expr) h18_aux) ?_; dsimp only
  refine runs_assign_le (Expr.eval_load_of_eq (v := fIsRootBase (lsfFAncPtr b vCap eCap n0 tM))
    (by dsimp [fOffIsRootPtr]; eval_expr) hIsR_ptr) ?_ (by dsimp [Expr.size]; omega)
  refine ⟨rfl, by simp [hr0], by simp [hr1], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

lemma addOrigRootSetup_triple {w b u : ℕ} {p : Program} {S : LSFState} {x : LSFConcrete}
    {mem : ℕ → ℕ} {regs_in : ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w) (hend_ltw : x.endAddr b < 2 ^ w)
    (hrep : (LSFRep x.h).rep b S x mem)
    {uIdx : ℕ} (huIdx_lt : uIdx < x.n0) (hu_eq : x.vList[uIdx]! = u) :
    Triple w p
      (fun st => st.mem = mem ∧ st.regs = regs_in ∧
        st.regs 1 = u ∧ st.regs 2 = x.vCap ∧ st.regs 3 = x.eCap ∧ st.regs 4 = x.n0 ∧
        st.regs 7 = lsfDgFPtr b x.vCap x.eCap x.tM ∧
        st.regs 8 = lsfFAncPtr b x.vCap x.eCap x.n0 x.tM ∧
        st.regs 9 = lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w)
      addOrigRootSetupStmt
      (normalPost fun st' =>
        st'.mem = mem ∧
        st'.regs 11 = auxVIdxBase (lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w) ∧
        st'.regs 12 = auxVListBase (lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w) x.vCap ∧
        st'.regs 13 = auxThParentBase (lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w) x.vCap x.n0 ∧
        st'.regs 14 = auxThStackBase (lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w) x.vCap x.n0 ∧
        st'.regs 15 = auxOrigVertBase (lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w) x.vCap x.n0 ∧
        st'.regs 16 = fRListBase (lsfFAncPtr b x.vCap x.eCap x.n0 x.tM) x.vCap ∧
        st'.regs 17 = fCompIdBase (lsfFAncPtr b x.vCap x.eCap x.n0 x.tM) x.vCap ∧
        st'.regs 18 = fCompRootBase (lsfFAncPtr b x.vCap x.eCap x.n0 x.tM) x.vCap ∧
        st'.regs 19 = fCompSizeBase (lsfFAncPtr b x.vCap x.eCap x.n0 x.tM) x.vCap ∧
        st'.regs 20 = fECap x.eCap x.n0 ∧
        st'.regs 21 = dgIntToExtBase (lsfDgFPtr b x.vCap x.eCap x.tM) x.vCap ∧
        st'.regs 36 = dgETailSlotBase (lsfDgFPtr b x.vCap x.eCap x.tM) x.vCap (fECap x.eCap x.n0) ∧
        st'.regs 37 = dgEHeadSlotBase (lsfDgFPtr b x.vCap x.eCap x.tM) x.vCap (fECap x.eCap x.n0) ∧
        st'.regs 22 = uIdx ∧
        st'.regs 23 = 0 ∧
        ∀ r, r ≤ 10 → st'.regs r = regs_in r)
      (fun _ => 120) := by
  set vCap := x.vCap; set eCap := x.eCap; set n0 := x.n0; set tM := x.tM; set L_w := x.L_w
  set eCapF := fECap eCap n0
  set dgFPtr := lsfDgFPtr b vCap eCap tM
  set fAncPtr := lsfFAncPtr b vCap eCap n0 tM
  set auxPtr := lsfAuxPtr b vCap eCap n0 tM L_w
  have hlay := addRoot_layout hend_ltw
  rcases hrep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hvT_lt, _, _, _, _, _,
    hFAnc, _, _, hAux⟩
  rcases hFAnc with ⟨_, _, h2_rL, h3_cid, h4_cr, h5_cs, _⟩
  rcases hAux with ⟨h0_vi, h1_vl, _, _, _, _, _, _, h8_thp, h9_ov, _, _, _, _, _, h15_stk, _,
    hvLen, _, hvMem, _, _, hvIdx, _⟩
  have hu_get : x.vList[uIdx]'(by omega) = u := by rwa [getElem!_pos x.vList uIdx (by omega)] at hu_eq
  have hu_lt : u < vCap := hvT_lt u ((hvMem u).mp (hu_get ▸ List.getElem_mem _))
  have hvIdx_u : mem (auxVIdxBase auxPtr + u) = uIdx + 1 := by
    have := hvIdx uIdx (by omega); rwa [hu_get] at this
  have haux_hdr_ltw : auxPtr + 18 < 2 ^ w := by
    dsimp [auxPtr, vCap, eCap, n0, tM, L_w, auxSize, auxHdrSize] at hlay ⊢; omega
  have haux_hdr_ltw' : lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w + 18 < 2 ^ w := haux_hdr_ltw
  have hf_hdr_ltw : fAncPtr + 6 < 2 ^ w := by
    dsimp [fAncPtr, vCap, eCap, n0, tM, fAncSize, fAncHdrSize] at hlay ⊢; omega
  have hf_hdr_ltw' : lsfFAncPtr b x.vCap x.eCap x.n0 x.tM + 6 < 2 ^ w := hf_hdr_ltw
  have hdgF_ltw : dgFPtr + dynGraphSize vCap eCapF < 2 ^ w := by
    dsimp only [dgFPtr, eCapF, vCap, eCap, n0, tM]; omega
  have hdgF_sz : dynGraphSize vCap eCapF = 4 + 7 * vCap + 9 * eCapF := rfl
  have h3e_n0_ltw : 3 * eCap + n0 < 2 ^ w := by dsimp [eCapF, fECap] at hdgF_ltw hdgF_sz; omega
  have hvi_u_ltw : auxVIdxBase auxPtr + u < 2 ^ w := by
    dsimp [auxPtr, vCap, eCap, n0, tM, L_w, auxVIdxBase, auxSize] at hlay ⊢; omega
  intro st ω ⟨hmem, hregs, hr1, hr2, hr3, hr4, hr7, hr8, hr9⟩
  subst hmem
  dsimp only [addOrigRootSetupStmt]
  refine runs_start_le ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := auxVIdxBase auxPtr) (by
    dsimp [auxOffVIdxPtr]; rw [show lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w = auxPtr + 0 from rfl]; eval_expr) h0_vi) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := auxVListBase auxPtr vCap) (by dsimp [auxOffVListPtr]; eval_expr) h1_vl) ?_; dsimp only
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := auxThParentBase auxPtr vCap n0) (by dsimp [auxOffThParentPtr]; eval_expr) h8_thp) ?_; dsimp only
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := auxThStackBase auxPtr vCap n0) (by dsimp [auxOffThStackPtr]; eval_expr) h15_stk) ?_; dsimp only
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := auxOrigVertBase auxPtr vCap n0) (by dsimp [auxOffOrigVertPtr]; eval_expr) h9_ov) ?_; dsimp only
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := fRListBase fAncPtr vCap) (by dsimp [fOffRListPtr]; eval_expr) h2_rL) ?_; dsimp only
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := fCompIdBase fAncPtr vCap) (by dsimp [fOffCompIdPtr]; eval_expr) h3_cid) ?_; dsimp only
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := fCompRootBase fAncPtr vCap) (by dsimp [fOffCompRootPtr]; eval_expr) h4_cr) ?_; dsimp only
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := fCompSizeBase fAncPtr vCap) (by dsimp [fOffCompSizePtr]; eval_expr) h5_cs) ?_; dsimp only
  refine runs_seq_assign_le (v := eCapF) (by dsimp [eCapF, fECap]; eval_expr) ?_; dsimp only
  refine runs_seq_assign_le (v := dgIntToExtBase dgFPtr vCap) (by dsimp [dgIntToExtBase]; eval_expr) ?_; dsimp only
  refine runs_seq_assign_le (v := dgETailSlotBase dgFPtr vCap eCapF) (by dsimp [dgETailSlotBase]; eval_expr) ?_; dsimp only
  refine runs_seq_assign_le (v := dgEHeadSlotBase dgFPtr vCap eCapF) (by
    have h : dgEHeadSlotBase dgFPtr vCap eCapF = dgETailSlotBase dgFPtr vCap eCapF + eCapF := by
      dsimp [dgEHeadSlotBase, dgETailSlotBase]; omega
    have hlt : dgETailSlotBase dgFPtr vCap eCapF + eCapF < 2 ^ w := by
      dsimp [dgETailSlotBase]; omega
    rw [h]; eval_expr) ?_; dsimp only
  refine runs_seq_assign_le (v := uIdx) ?_ ?_
  · rw [show some uIdx = some (BinOp.sub.eval (uIdx + 1) 1) from rfl]
    exact Expr.eval_bin (Expr.eval_load_of_eq (by eval_expr) hvIdx_u)
      (Expr.eval_const (by omega)) (by dsimp [BinOp.eval]; omega)
  dsimp only
  refine runs_assign_le (v := 0) (by eval_expr) ?_ (by dsimp [Expr.size]; omega)
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro r hr
  dsimp only
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega), hregs]

private lemma thStackInv_of_chain {S₀ : LSFState} {vList : List ℕ} {thParent : ℕ → ℕ} {n0 r0Idx : ℕ}
    (hT₀ : IsRootedTree S₀.T₀ S₀.r₀) (hvLen : vList.length = n0) (hvNd : vList.Nodup)
    (hvMem : ∀ v, v ∈ vList ↔ v ∈ S₀.T₀.V)
    (hr0_lt : r0Idx < n0) (hr0_v : vList[r0Idx]? = some S₀.r₀)
    (hth_lt : ∀ i < n0, thParent i < n0)
    (hThProp : ∀ i (hi : i < vList.length), i ≠ r0Idx →
      (S₀.TH.forestPath vList[i] S₀.r₀).length = (S₀.TH.forestPath vList[thParent i]! S₀.r₀).length + 1 ∧
      ∃ e ∈ S₀.TH.E, (S₀.TH.tail e = vList[i] ∧ S₀.TH.head e = vList[thParent i]!) ∨
        (S₀.TH.tail e = vList[thParent i]! ∧ S₀.TH.head e = vList[i])) :
    ∀ (L : List ℕ) (S_cur : LSFState),
      LSFStructInv S_cur → S_cur.T₀ = S₀.T₀ → S_cur.r₀ = S₀.r₀ →
      L.Nodup →
      (∀ idx ∈ L, idx < n0 ∧ vList[idx]! ∉ S_cur.R_orig) →
      (∀ j (hj : j + 1 < L.length), thParent (L[j + 1]) = L[j]) →
      (∀ a rest, L = a :: rest → vList[thParent a]! ∈ S_cur.R_orig) →
      ThStackInv S_cur vList thParent n0 L := by
  intro L
  induction L with
  | nil => intro _ _ _ _ _ _ _ _; trivial
  | cons a rest ih =>
    intro S_cur hInv hT_eq hr_eq hnd hall hstep htop
    have ha_lt := (hall a List.mem_cons_self).1
    have ha_not := (hall a List.mem_cons_self).2
    have ha_par_R := htop a rest rfl
    have ha_ne_r0 : a ≠ r0Idx := by
      intro hEq
      have hget : vList[r0Idx]! = S₀.r₀ := by
        rw [getElem!_pos vList r0Idx (by omega)]
        have h1 : vList[r0Idx]? = some (vList[r0Idx]'(by omega)) := List.getElem?_eq_getElem (by omega)
        rw [hr0_v] at h1; exact Option.some.inj h1.symm
      rw [hEq, hget, ← hr_eq] at ha_not
      exact ha_not hInv.r₀_mem_R_orig
    have hp_lt := hth_lt a ha_lt
    have hprop := hThProp a (by omega) ha_ne_r0
    have hpar_spec := auxAt_thParent_isParent hT₀ hvLen hvMem ha_lt hp_lt hprop.1 hprop.2
    have hanc_iff : ∀ w, IsAncestor S_cur.TH S_cur.r₀ w (vList[a]!) ↔
        w = vList[a]! ∨ IsAncestor S_cur.TH S_cur.r₀ w (vList[thParent a]!) := by
      intro w
      have hTH_eq : S_cur.TH = hldAuxTree S₀.T₀ S₀.r₀ := by simp [LSFState.TH, hT_eq, hr_eq]
      rw [hTH_eq, hr_eq, getElem!_pos vList a (by omega), getElem!_pos vList (thParent a) (by omega)]
      exact hpar_spec.2 w
    have ha_T : vList[a]! ∈ S_cur.T₀.V := by
      rw [hT_eq, getElem!_pos vList a (by omega)]
      exact (hvMem _).mp (List.getElem_mem _)
    let S_next : LSFState := { S_cur with R₀_base := insert (vList[a]!) S_cur.R₀_base }
    have hRorig_next : S_next.R_orig = insert (vList[a]!) S_cur.R_orig := by
      ext w
      rw [Finset.mem_insert]
      change w ∈ upClosure S_cur.TH S_cur.r₀ (insert (vList[a]!) S_cur.R₀_base) ↔
        w = vList[a]! ∨ w ∈ S_cur.R_orig
      rw [mem_upClosure_iff]
      have hTHc := hldAuxTree_isRootedTree hInv.hT₀
      constructor
      · rintro ⟨u, hu, hwu⟩
        rw [Finset.mem_insert] at hu
        rcases hu with rfl | hu
        · rcases (hanc_iff w).mp hwu with rfl | hwp
          · exact Or.inl rfl
          · exact Or.inr (upClosure_isUpwardClosed hTHc hInv.hR₀_sub ha_par_R hwp)
        · exact Or.inr (mem_upClosure_iff.mpr ⟨u, hu, hwu⟩)
      · rintro (h | hw)
        · rw [h]; exact ⟨vList[a]!, Finset.mem_insert_self _ _, isAncestor_refl _ _ _⟩
        · obtain ⟨u, hu, hwu⟩ := mem_upClosure_iff.mp hw
          exact ⟨u, Finset.mem_insert_of_mem hu, hwu⟩
    refine ⟨ha_lt, ha_not, ha_par_R, hanc_iff, ?_⟩
    refine ih S_next (hInv.addOrigRoot_inv ha_T).1 hT_eq hr_eq (List.nodup_cons.mp hnd).2 ?_ ?_ ?_
    · intro idx hidx
      have hidx_lt := (hall idx (List.mem_cons_of_mem _ hidx)).1
      have hidx_not := (hall idx (List.mem_cons_of_mem _ hidx)).2
      refine ⟨hidx_lt, ?_⟩
      rw [hRorig_next, Finset.mem_insert]
      rintro (hEq | hmem)
      · rw [getElem!_pos vList idx (by omega), getElem!_pos vList a (by omega)] at hEq
        have hidx_eq_a : idx = a := (hvNd.getElem_inj_iff).mp hEq
        exact (List.nodup_cons.mp hnd).1 (hidx_eq_a ▸ hidx)
      · exact hidx_not hmem
    · intro j hj
      exact hstep (j + 1) (Nat.succ_lt_succ hj)
    · intro b rest' hEq
      subst hEq
      have hpb : thParent b = a := hstep 0 (by simp)
      rw [hpb, hRorig_next]
      exact Finset.mem_insert_self _ _

/-- Verification of `addOrigRootClimbStmt` by induction on `d = (S.TH.forestPath vList[curIdx]! S.r₀).length`. -/
lemma addOrigRootClimb_runs {w b : ℕ} {p : Program} {ω : ℕ → Bool}
    {S : LSFState} {x : LSFConcrete} {mem0 : ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w) (hend_ltw : x.endAddr b < 2 ^ w)
    (hrep : (LSFRep x.h).rep b S x mem0) :
    ∀ d (curIdx : ℕ) (stk0 : List ℕ) (st : State),
      curIdx < x.n0 →
      (S.TH.forestPath (x.vList[curIdx]!) S.r₀).length = d →
      stk0.length + d ≤ hldDepthBound x.n0 →
      (∀ a, ¬ (auxThStackBase (lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w) x.vCap x.n0 ≤ a ∧
        a < auxThStackBase (lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w) x.vCap x.n0 +
          (hldDepthBound x.n0 + 2)) → st.mem a = mem0 a) →
      StackMemAt st.mem (auxThStackBase (lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w) x.vCap x.n0) stk0 →
      stk0.Nodup →
      (∀ idx ∈ stk0, idx < x.n0 ∧ x.vList[idx]! ∉ S.R_orig ∧
        d < (S.TH.forestPath (x.vList[idx]!) S.r₀).length) →
      (∀ j (hj : j + 1 < stk0.length), x.thParent (stk0[j + 1]) = stk0[j]) →
      (∀ prev rest, stk0 = prev :: rest → x.thParent prev = curIdx) →
      st.regs 10 = fIsRootBase (lsfFAncPtr b x.vCap x.eCap x.n0 x.tM) →
      st.regs 12 = auxVListBase (lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w) x.vCap →
      st.regs 13 = auxThParentBase (lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w) x.vCap x.n0 →
      st.regs 14 = auxThStackBase (lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w) x.vCap x.n0 →
      st.regs 22 = curIdx →
      st.regs 23 = stk0.length →
      ∃ (st' : State) (c : ℕ) (stk : List ℕ),
        Runs w p ω addOrigRootClimbStmt st .normal st' c ∧
        (∀ a, ¬ (auxThStackBase (lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w) x.vCap x.n0 ≤ a ∧
          a < auxThStackBase (lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w) x.vCap x.n0 +
            (hldDepthBound x.n0 + 2)) → st'.mem a = mem0 a) ∧
        StackMemAt st'.mem (auxThStackBase (lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w) x.vCap x.n0) stk ∧
        (∀ idx ∈ stk0, idx ∈ stk) ∧
        stk0.length ≤ stk.length ∧ stk.length ≤ hldDepthBound x.n0 ∧
        ThStackInv S x.vList x.thParent x.n0 stk ∧
        (∀ w, (∃ idx ∈ stk, w = x.vList[idx]!) → IsAncestor S.TH S.r₀ w (x.vList[curIdx]!) ∨
          ∃ idx ∈ stk0, w = x.vList[idx]!) ∧
        (∀ w, IsAncestor S.TH S.r₀ w (x.vList[curIdx]!) →
          w ∈ S.R_orig ∨ ∃ idx ∈ stk, w = x.vList[idx]!) ∧
        st'.regs 23 = stk.length ∧
        (∀ r, r ≠ 22 → r ≠ 23 → st'.regs r = st.regs r) ∧
        c ≤ 30 * (stk.length - stk0.length) + 10 := by
  set vCap := x.vCap; set eCap := x.eCap; set n0 := x.n0; set tM := x.tM; set L_w := x.L_w
  set fAncPtr := lsfFAncPtr b vCap eCap n0 tM
  set auxPtr := lsfAuxPtr b vCap eCap n0 tM L_w
  set isRootBase := fIsRootBase fAncPtr
  set vListBase := auxVListBase auxPtr vCap
  set thParentBase := auxThParentBase auxPtr vCap n0
  set thStackBase := auxThStackBase auxPtr vCap n0
  have hlay := addRoot_layout hend_ltw
  have hstk_end_ltw : thStackBase + (hldDepthBound n0 + 2) < 2 ^ w := by
    dsimp only [thStackBase, auxPtr, vCap, eCap, n0, tM, L_w]; omega
  rcases hrep with ⟨_, _, _, _, _, _, hInv, _, _, _, _, _, _, _, hvT_lt, _, _, _, _, _,
    hFAnc, _, _, hAux⟩
  rcases hFAnc with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hIsRoot, _⟩
  rcases hAux with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hvLen, hvNd, hvMem, _, hvLA, _, _, hr0_lt, hr0_v, _, _, _, _, hth_mem, _, _, _, _, hThProp, _⟩
  have hvl_lt_stk : vListBase + n0 ≤ thStackBase := by
    dsimp [vListBase, thStackBase, auxThStackBase, auxVisBBase, auxVisABase, auxQBufBBase,
      auxQBufABase, auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase,
      auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase]; omega
  have hthp_lt_stk : thParentBase + n0 ≤ thStackBase := by
    dsimp [thParentBase, thStackBase, auxThStackBase, auxVisBBase, auxVisABase, auxQBufBBase,
      auxQBufABase, auxIsOrigVertBase, auxOrigVertBase, auxThParentBase]; omega
  have hisr_lt_stk : isRootBase + vCap ≤ thStackBase := by
    have h1 : isRootBase + vCap ≤ fAncPtr + fAncSize vCap := by
      dsimp [isRootBase, fIsRootBase, fAncSize]; omega
    have h2 : fAncPtr + fAncSize vCap ≤ auxPtr := by
      dsimp only [fAncPtr, auxPtr, vCap, eCap, n0, tM, L_w]; omega
    have h3 : auxPtr ≤ thStackBase := by
      dsimp [thStackBase, auxThStackBase, auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase,
        auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase,
        auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase]; omega
    omega
  have hTH := hldAuxTree_isRootedTree hInv.hT₀
  intro d
  induction d with
  | zero =>
    intro curIdx stk0 st hcur_lt hd hsp_bd hfr hstk hnd hall hstep htop hr10 hr12 hr13 hr14 hr22 hr23
    have hcur_get : x.vList[curIdx]! = x.vList[curIdx]'(by omega) := getElem!_pos x.vList curIdx (by omega)
    have hcur_T : x.vList[curIdx]! ∈ S.T₀.V := hcur_get ▸ (hvMem _).mp (List.getElem_mem _)
    have hcur_vCap : x.vList[curIdx]! < vCap := hvT_lt _ hcur_T
    have hcur_eq_r0 : x.vList[curIdx]! = S.r₀ := by
      have hP := forestPath_isPath hTH.isForest (hTH.connected hcur_T hTH.2)
      have hnil : (hldAuxTree S.T₀ S.r₀).forestPath (x.vList[curIdx]!) S.r₀ = [] := List.eq_nil_of_length_eq_zero hd
      have hw := hP.1; rw [hnil] at hw
      have hnil_eq : ∀ {G : MGraph} {a b : ℕ}, G.IsWalk a b [] → a = b := by
        intro G a b h; cases h; rfl
      exact hnil_eq hw
    have hcur_Rorig : x.vList[curIdx]! ∈ S.R_orig := hcur_eq_r0 ▸ hInv.r₀_mem_R_orig
    have hcur_in_R : x.vList[curIdx]! ∈ S.RF.R := Finset.mem_union_left _ hcur_Rorig
    have hv_mem : st.mem (vListBase + curIdx) = x.vList[curIdx]! := by
      rw [hfr _ (fun hc => Nat.not_le.mpr (lt_of_lt_of_le (Nat.add_lt_add_left hcur_lt _) hvl_lt_stk) hc.1),
        hcur_get]
      exact hvLA curIdx (by omega)
    have hisr_mem : st.mem (isRootBase + x.vList[curIdx]!) = 1 := by
      rw [hfr _ (fun hc => Nat.not_le.mpr (lt_of_lt_of_le (Nat.add_lt_add_left hcur_vCap _) hisr_lt_stk) hc.1),
        hIsRoot _ hcur_vCap, ite_eq_left hcur_in_R]
    have hcond_eval : (Expr.bin .eq (.load (.bin .add (.reg 10)
        (.load (.bin .add (.reg 12) (.reg 22))))) (.const 0)).eval w st = some 0 := by
      have h1 : (Expr.load (.bin .add (.reg 12) (.reg 22))).eval w st = some (x.vList[curIdx]!) :=
        Expr.eval_load_of_eq (by eval_expr) hv_mem
      have h2 : (Expr.load (.bin .add (.reg 10) (.load (.bin .add (.reg 12) (.reg 22))))).eval w st = some 1 :=
        Expr.eval_load_of_eq (Expr.eval_bin (hr10 ▸ Expr.eval_reg (w := w) 10 st) h1
          (by dsimp [BinOp.eval]; omega)) hisr_mem
      exact Expr.eval_bin h2 (Expr.eval_const (k := 0) (by omega)) (by dsimp [BinOp.eval]; omega)
    have hinv0 : ThStackInv S x.vList x.thParent n0 stk0 :=
      thStackInv_of_chain hInv.hT₀ hvLen hvNd hvMem hr0_lt hr0_v (fun i hi => (hth_mem i hi).2)
        hThProp stk0 S hInv rfl rfl hnd (fun i hi => ⟨(hall i hi).1, (hall i hi).2.1⟩) hstep
        (fun a rest hEq => by rw [htop a rest hEq]; exact hcur_Rorig)
    refine ⟨st, _, stk0, runs_loop_iff.mpr (Or.inl ⟨hcond_eval, rfl, rfl, rfl⟩), hfr, hstk, fun _ h => h, le_rfl, by omega, hinv0,
      fun _ h => Or.inr h,
      fun w hw => Or.inl (upClosure_isUpwardClosed hTH hInv.hR₀_sub hcur_Rorig hw),
      hr23, fun _ _ _ => rfl, by dsimp [Expr.size]; omega⟩
  | succ d ih =>
    intro curIdx stk0 st hcur_lt hd hsp_bd hfr hstk hnd hall hstep htop hr10 hr12 hr13 hr14 hr22 hr23
    have hcur_get : x.vList[curIdx]! = x.vList[curIdx]'(by omega) := getElem!_pos x.vList curIdx (by omega)
    have hcur_T : x.vList[curIdx]! ∈ S.T₀.V := hcur_get ▸ (hvMem _).mp (List.getElem_mem _)
    have hcur_vCap : x.vList[curIdx]! < vCap := hvT_lt _ hcur_T
    have hv_mem : st.mem (vListBase + curIdx) = x.vList[curIdx]! := by
      rw [hfr _ (fun hc => Nat.not_le.mpr (lt_of_lt_of_le (Nat.add_lt_add_left hcur_lt _) hvl_lt_stk) hc.1),
        hcur_get]
      exact hvLA curIdx (by omega)
    have hcur_in_R_iff : x.vList[curIdx]! ∈ S.RF.R ↔ x.vList[curIdx]! ∈ S.R_orig := by
      simp only [LSFState.RF, LSFState.R, Finset.mem_union]
      exact ⟨fun h => h.resolve_right (Finset.disjoint_left.mp hInv.hdisj_iso hcur_T), Or.inl⟩
    by_cases hcur_Rorig : x.vList[curIdx]! ∈ S.R_orig
    · have hisr_mem : st.mem (isRootBase + x.vList[curIdx]!) = 1 := by
        rw [hfr _ (fun hc => Nat.not_le.mpr (lt_of_lt_of_le (Nat.add_lt_add_left hcur_vCap _) hisr_lt_stk) hc.1),
          hIsRoot _ hcur_vCap, ite_eq_left (hcur_in_R_iff.mpr hcur_Rorig)]
      have hcond_eval : (Expr.bin .eq (.load (.bin .add (.reg 10)
          (.load (.bin .add (.reg 12) (.reg 22))))) (.const 0)).eval w st = some 0 := by
        have h1 : (Expr.load (.bin .add (.reg 12) (.reg 22))).eval w st = some (x.vList[curIdx]!) :=
          Expr.eval_load_of_eq (by eval_expr) hv_mem
        have h2 : (Expr.load (.bin .add (.reg 10) (.load (.bin .add (.reg 12) (.reg 22))))).eval w st = some 1 :=
          Expr.eval_load_of_eq (Expr.eval_bin (hr10 ▸ Expr.eval_reg (w := w) 10 st) h1
            (by dsimp [BinOp.eval]; omega)) hisr_mem
        exact Expr.eval_bin h2 (Expr.eval_const (k := 0) (by omega)) (by dsimp [BinOp.eval]; omega)
      have hinv0 : ThStackInv S x.vList x.thParent n0 stk0 :=
        thStackInv_of_chain hInv.hT₀ hvLen hvNd hvMem hr0_lt hr0_v (fun i hi => (hth_mem i hi).2)
          hThProp stk0 S hInv rfl rfl hnd (fun i hi => ⟨(hall i hi).1, (hall i hi).2.1⟩) hstep
          (fun a rest hEq => by rw [htop a rest hEq]; exact hcur_Rorig)
      refine ⟨st, _, stk0, runs_loop_iff.mpr (Or.inl ⟨hcond_eval, rfl, rfl, rfl⟩), hfr, hstk, fun _ h => h, le_rfl, by omega, hinv0,
        fun _ h => Or.inr h,
        fun w hw => Or.inl (upClosure_isUpwardClosed hTH hInv.hR₀_sub hcur_Rorig hw),
        hr23, fun _ _ _ => rfl, by dsimp [Expr.size]; omega⟩
    · have hisr_mem : st.mem (isRootBase + x.vList[curIdx]!) = 0 := by
        rw [hfr _ (fun hc => Nat.not_le.mpr (lt_of_lt_of_le (Nat.add_lt_add_left hcur_vCap _) hisr_lt_stk) hc.1),
          hIsRoot _ hcur_vCap, ite_eq_right (fun h => hcur_Rorig (hcur_in_R_iff.mp h))]
      have hcond_eval : (Expr.bin .eq (.load (.bin .add (.reg 10)
          (.load (.bin .add (.reg 12) (.reg 22))))) (.const 0)).eval w st = some 1 := by
        have h1 : (Expr.load (.bin .add (.reg 12) (.reg 22))).eval w st = some (x.vList[curIdx]!) :=
          Expr.eval_load_of_eq (by eval_expr) hv_mem
        have h2 : (Expr.load (.bin .add (.reg 10) (.load (.bin .add (.reg 12) (.reg 22))))).eval w st = some 0 :=
          Expr.eval_load_of_eq (Expr.eval_bin (hr10 ▸ Expr.eval_reg (w := w) 10 st) h1
            (by dsimp [BinOp.eval]; omega)) hisr_mem
        exact Expr.eval_bin h2 (Expr.eval_const (k := 0) (by omega)) (by dsimp [BinOp.eval]; omega)
      have hcur_ne_r0 : curIdx ≠ mem0 (auxPtr + auxOffR0Idx) := by
        intro hEq; subst hEq
        have hget : x.vList[mem0 (auxPtr + auxOffR0Idx)]! = S.r₀ := by
          rw [getElem!_pos x.vList _ (by omega)]
          have h1 : x.vList[mem0 (auxPtr + auxOffR0Idx)]? =
              some (x.vList[mem0 (auxPtr + auxOffR0Idx)]'(by omega)) := List.getElem?_eq_getElem (by omega)
          rw [hr0_v] at h1; exact Option.some.inj h1.symm
        exact hcur_Rorig (hget ▸ hInv.r₀_mem_R_orig)
      set parIdx := x.thParent curIdx
      have hpar_lt : parIdx < n0 := (hth_mem curIdx hcur_lt).2
      have hprop := hThProp curIdx (by omega) hcur_ne_r0
      have hpar_dep : (S.TH.forestPath (x.vList[parIdx]!) S.r₀).length = d := by
        have h1 : (S.TH.forestPath x.vList[curIdx]! S.r₀).length =
            (S.TH.forestPath x.vList[parIdx]! S.r₀).length + 1 := by
          rw [hcur_get]; exact hprop.1
        omega
      have hpar_spec := auxAt_thParent_isParent hInv.hT₀ hvLen hvMem hcur_lt hpar_lt hprop.1 hprop.2
      have hpar_anc : IsAncestor S.TH S.r₀ (x.vList[parIdx]!) (x.vList[curIdx]!) := by
        rw [hcur_get, getElem!_pos x.vList parIdx (by omega)]; exact hpar_spec.1
      have hanc_iff : ∀ w, IsAncestor S.TH S.r₀ w (x.vList[curIdx]!) ↔
          w = x.vList[curIdx]! ∨ IsAncestor S.TH S.r₀ w (x.vList[parIdx]!) := by
        intro w; rw [hcur_get, getElem!_pos x.vList parIdx (by omega)]; exact hpar_spec.2 w
      have hpar_mem : st.mem (thParentBase + curIdx) = parIdx := by
        rw [hfr _ (fun hc => Nat.not_le.mpr (lt_of_lt_of_le (Nat.add_lt_add_left hcur_lt _) hthp_lt_stk) hc.1)]
        exact (hth_mem curIdx hcur_lt).1
      let mem1 := Function.update st.mem (thStackBase + stk0.length) curIdx
      let regs1 := Function.update (Function.update st.regs 23 (stk0.length + 1)) 22 parIdx
      let st1 : State := { mem := mem1, regs := regs1, pos := st.pos }
      have hthp_mem1 : mem1 (thParentBase + curIdx) = parIdx := by
        dsimp only [mem1]; rw [Function.update_of_ne (by omega)]; exact hpar_mem
      have hbody_run : ∃ cb,
          Runs w p ω
            (.store (.bin .add (.reg 14) (.reg 23)) (.reg 22) ;;
             .assign 23 (.bin .add (.reg 23) (.const 1)) ;;
             .assign 22 (.load (.bin .add (.reg 13) (.reg 22)))) st .normal st1 cb ∧
          cb ≤ 18 := by
        have hstk_ltw : thStackBase + stk0.length < 2 ^ w := by omega
        have hthp_ltw : thParentBase + curIdx < 2 ^ w := by omega
        have hrun_full : ∃ o st_b cb,
            Runs w p ω
              (.store (.bin .add (.reg 14) (.reg 23)) (.reg 22) ;;
               .assign 23 (.bin .add (.reg 23) (.const 1)) ;;
               .assign 22 (.load (.bin .add (.reg 13) (.reg 22)))) st o st_b cb ∧
            (o = .normal ∧ st_b = st1) ∧ 0 + cb ≤ 18 := by
          refine runs_seq_store_le (x := thStackBase + stk0.length) (v := curIdx)
            (by eval_expr) (by eval_expr) ?_
          refine runs_seq_assign_le (v := stk0.length + 1) (by eval_expr) ?_; dsimp only
          refine runs_assign_le (Expr.eval_load_of_eq (v := parIdx) (by eval_expr) hthp_mem1)
            ⟨rfl, rfl⟩ (by dsimp [Expr.size]; omega)
        obtain ⟨o, st_b, cb, hrb, ⟨rfl, rfl⟩, hcb⟩ := hrun_full
        exact ⟨cb, hrb, by omega⟩
      obtain ⟨cb, hbody, hcb⟩ := hbody_run
      have hfr1 : ∀ a, ¬ (thStackBase ≤ a ∧ a < thStackBase + (hldDepthBound n0 + 2)) →
          st1.mem a = mem0 a := fun a ha => by
        dsimp only [st1, mem1]
        rw [Function.update_of_ne (fun h => ha ⟨by rw [h]; omega, by rw [h]; omega⟩)]
        exact hfr a ha
      have hstk1 : StackMemAt st1.mem thStackBase (curIdx :: stk0) :=
        stackMemAt_push hstk (fun j hj => by dsimp [st1, mem1]; rw [Function.update_of_ne (by omega)])
          (by dsimp [st1, mem1]; exact Function.update_self _ _ _)
      have hcur_not_in : curIdx ∉ stk0 := fun hmem => by
        have := (hall curIdx hmem).2.2; omega
      have hnd1 : (curIdx :: stk0).Nodup := List.nodup_cons.mpr ⟨hcur_not_in, hnd⟩
      have hall1 : ∀ idx ∈ curIdx :: stk0, idx < n0 ∧ x.vList[idx]! ∉ S.R_orig ∧
          d < (S.TH.forestPath (x.vList[idx]!) S.r₀).length := by
        intro idx hidx
        rcases List.mem_cons.mp hidx with rfl | hmem
        · exact ⟨hcur_lt, hcur_Rorig, by omega⟩
        · obtain ⟨h1, h2, h3⟩ := hall idx hmem
          exact ⟨h1, h2, by omega⟩
      have hstep1 : ∀ j (hj : j + 1 < (curIdx :: stk0).length),
          x.thParent ((curIdx :: stk0)[j + 1]) = (curIdx :: stk0)[j] := by
        intro j hj
        cases j with
        | zero =>
          cases stk0 with
          | nil => simp at hj
          | cons prev rest =>
            simp only [List.getElem_cons_succ, List.getElem_cons_zero]
            exact htop prev rest rfl
        | succ j' =>
          exact hstep j' (Nat.lt_of_succ_lt_succ hj)
      obtain ⟨st', c2, stk, hrun2, hfr', hstk', hsub_stk, hlen_le, hlen_bd, hinv', hanc_sub, hanc_cov,
        hr23', hreg', hc2⟩ :=
        ih parIdx (curIdx :: stk0) st1 hpar_lt hpar_dep (by simp; omega) hfr1 hstk1 hnd1 hall1
          hstep1 (fun _ _ hEq => by cases hEq; rfl)
          (by dsimp [st1, regs1]; simp [hr10]) (by dsimp [st1, regs1]; simp [hr12])
          (by dsimp [st1, regs1]; simp [hr13]) (by dsimp [st1, regs1]; simp [hr14])
          (by dsimp [st1, regs1]; rfl) (by dsimp [st1, regs1]; simp)
      refine ⟨st', _, stk, runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st1, cb, c2, hcond_eval, by decide, hbody, hrun2, rfl⟩)),
        hfr', hstk', fun idx hidx => hsub_stk idx (List.mem_cons_of_mem _ hidx),
        by simp at hlen_le; omega, hlen_bd, hinv', ?_, ?_, hr23', ?_, ?_⟩
      · intro w hw
        rcases hanc_sub w hw with hwp | ⟨idx, hidx, rfl⟩
        · exact Or.inl (isAncestor_trans hTH hcur_T hwp hpar_anc)
        · rcases List.mem_cons.mp hidx with rfl | hmem
          · exact Or.inl (isAncestor_refl S.TH S.r₀ _)
          · exact Or.inr ⟨idx, hmem, rfl⟩
      · intro w hw
        rcases (hanc_iff w).mp hw with rfl | hwp
        · exact Or.inr ⟨curIdx, hsub_stk curIdx List.mem_cons_self, rfl⟩
        · exact hanc_cov w hwp
      · intro r h22 h23
        rw [hreg' r h22 h23]
        dsimp only [st1, regs1]
        rw [Function.update_of_ne h22, Function.update_of_ne h23]
      · simp only [List.length_cons] at hlen_le hc2
        dsimp only [Expr.size]
        omega

end

end MinCostFlow.LSF.Program
