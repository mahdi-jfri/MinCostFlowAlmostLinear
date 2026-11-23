module

public import MinCostFlow.Spanner.ProgBuildWitnessCeHelpers

/-!
# Word-RAM Verification of Phase 2 of `buildWitnessCore` (`ProgBuildWitnessCe`)

Verifies `buildCeBody` and `buildCeLoopStmt`: constructs component expanders via
`ConstructExpander` (`ce.spec`), populates the 6-word component extension table `compExt`,
and transitions from `Phase01Post` to `CeLoopPost`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited WitnessCoreInput

private def CeAfterCallPre (inp : WitnessCoreInput) (ce : ConstructExpanderImpl)
    (pds : PathDSParams) (mem₀ : ℕ → ℕ) (ci aCompExt curH wStart : ℕ)
    (WSubs : List Graph) (W : Graph) (vRet : ℕ) (st : State) : Prop :=
  let rc := inp.prep.rawComps[ci]!
  let kCard := rc.2.length
  ci < inp.prep.rawComps.length ∧
  kCard ≤ inp.prep.J.n ∧
  st.regs 0 = inp.prep.jAddr ∧
  st.regs 4 = inp.h ∧
  st.regs 5 = inp.prep.J.n ∧
  st.regs 6 = inp.prep.J.m ∧
  st.regs 10 = inp.prep.phiNum_dec ∧
  st.regs 11 = inp.prep.phiDen_dec ∧
  st.regs 12 = inp.prep.j0Edges.length ∧
  st.regs 13 = inp.prep.aJ0Out ∧
  st.regs 14 = inp.prep.rawComps.length ∧
  st.regs 15 = inp.prep.aComps ∧
  st.regs 16 = inp.prep.J0_strip.m ∧
  st.regs 18 = aCompExt ∧
  st.regs 22 = ci ∧
  st.regs 23 = wStart ∧
  st.regs 26 = kCard ∧
  st.regs 28 = 2 ^ rc.1 ∧
  st.regs 29 = inp.prep.phiNum_dec * 2 ^ rc.1 ∧
  st.regs 30 = curH + kCard ∧
  st.regs 31 = vRet ∧
  st.mem (inp.h + 12) = aCompExt ∧
  inp.h + 20 ≤ aCompExt ∧
  aCompExt ≤ inp.h + 20 + pds.boundsSpace inp.dJInt inp.prep.J0_strip.m +
    pds.boundsSpace (dWInt ce) (inp.mwInt ce) ∧
  aCompExt + 6 * inp.prep.rawComps.length ≤ curH ∧
  curH + kCard + (2 + 2 * W.m) ≤ vRet ∧
  vRet ≤ aCompExt + 6 * inp.prep.rawComps.length +
    ((inp.prep.rawComps.take (ci + 1)).map fun rc => rc.2.length).sum +
    (ci + 1) * (ce.C_space * (inp.prep.J.n + 4 * inp.prep.J0_strip.m * inp.prep.phiDen_dec + 2) ^ ce.c_space) ∧
  (∀ x < inp.h, st.mem x = mem₀ x) ∧
  WitnessHdr0 st.mem inp ce pds ∧
  ZeroFrom st.mem vRet ∧
  GraphAt st.mem (curH + kCard) W ∧
  W.n = kCard ∧
  W.IsValid ∧
  W.IsConductanceExpanderOn W.verts ce.φ_Const ∧
  (∀ k (hk : k < kCard),
    let wList := inp.compWeights rc
    let hk_w : k < wList.length := by simp [wList, compWeights]; exact hk
    ((wList[k]'hk_w : ℕ) : ℝ) ≤ (W.deg k : ℝ) ∧
    (W.deg k : ℝ) ≤ (ce.c_deg_int : ℝ) * ((wList[k]'hk_w : ℕ) : ℝ)) ∧
  inp.ValidWSubsPrefix ce ci WSubs ∧
  wStart = inp.prep.j0Edges.length + (WSubs.map Graph.m).sum ∧
  CompExtPrefixAt st.mem aCompExt inp.prep.phiNum_dec curH
    (inp.buildCompsFrom inp.prep.j0Edges.length (inp.prep.rawComps.take ci) WSubs) ∧
  (∀ j < ci, aCompExt + 6 * inp.prep.rawComps.length ≤ st.mem (aCompExt + 6 * j + 1))

private theorem ce_afterCall_triple {w : ℕ} {p : Program}
    {inp : WitnessCoreInput} {ce : ConstructExpanderImpl} {pds : PathDSParams}
    {mem₀ : ℕ → ℕ} {ci aCompExt curH wStart : ℕ} {WSubs : List Graph} {W : Graph} {vRet : ℕ}
    (hvalid : inp.Valid ce pds mem₀ w) :
    Triple w p (CeAfterCallPre inp ce pds mem₀ ci aCompExt curH wStart WSubs W vRet)
      (.assign 32 (.load (.bin .add (.reg 30) (.const 1))) ;;
       .assign 33 (.bin .add (.reg 18) (.bin .mul (.const 6) (.reg 22))) ;;
       .store (.reg 33) (.reg 23) ;;
       .store (.bin .add (.reg 33) (.const 1)) (.reg 30) ;;
       .store (.bin .add (.reg 33) (.const 2)) (.reg 28) ;;
       .store (.bin .add (.reg 33) (.const 3)) (.reg 29) ;;
       .store (.bin .add (.reg 33) (.const 4)) (.reg 26) ;;
       .store (.bin .add (.reg 33) (.const 5)) (.reg 32) ;;
       .assign 23 (.bin .add (.reg 23) (.reg 32)) ;;
       .assign 17 (.reg 31))
      (normalPost fun st =>
        CeLoopInv inp ce pds mem₀ (ci + 1)
          { st with regs := Function.update st.regs 22 (ci + 1) } ∧ st.regs 22 = ci)
      (fun _ => 55) := by
  intro st ω hpre
  cases st with | mk m regs pos =>
  rcases ce_word_bounds hvalid with ⟨h1w, hheap_w, hm_w⟩
  rcases hpre with ⟨hci, hk_le_n, hr0, hr4, hr5, hr6, hr10, hr11, hr12, hr13, hr14, hr15, hr16,
    hr18, hr22, hr23, hr26, hr28, hr29, hr30, hr31, hhdr12, ha_lo, ha_hi, hcur_lo, hv_lo, hv_hi,
    hbelow, hhdr0, hzf, hW_at, hWn, hWval, hWexp, hWdeg, hws_pref, hwStart_eq, hcomp_pref, hj_lo⟩
  dsimp only at hr0 hr4 hr5 hr6 hr10 hr11 hr12 hr13 hr14 hr15 hr16 hr18 hr22 hr23 hr26 hr28 hr29
  dsimp only at hr30 hr31 hhdr12 hbelow hhdr0 hzf hW_at hcomp_pref hj_lo
  set rc := inp.prep.rawComps[ci]!
  set kCard := rc.2.length
  have hrc_eq : rc = inp.prep.rawComps[ci] := by simp [rc, hci]
  have hv := hvalid.2.2.1
  have hcprops := comp_props_at hv.toValid_zeroTail hci
  change 1 ≤ rc.1 ∧ rc.1 ≤ inp.prep.d_ℓ ∧ rc.2.Pairwise (· < ·) ∧ 2 ≤ rc.2.length ∧
    rc.2.Nodup ∧ (∀ u ∈ rc.2, u < inp.prep.J.n) ∧ (inp.prep.cJSub rc).n = rc.2.length ∧
    (inp.prep.cJSub rc).IsValid at hcprops
  have hce_sum := (ceWeights_sum_le hvalid).1
  have htake_sum : ((inp.prep.rawComps.take (ci + 1)).map fun x => x.2.length).sum ≤
      2 * inp.prep.J0_strip.m := by
    calc ((inp.prep.rawComps.take (ci + 1)).map fun x => x.2.length).sum
        ≤ (inp.prep.rawComps.map fun x => x.2.length).sum := by
          conv_rhs => rw [← List.take_append_drop (ci + 1) inp.prep.rawComps, List.map_append, List.sum_append]
          exact Nat.le_add_right _ _
      _ ≤ 2 * inp.prep.J0_strip.m := hce_sum
  have hv_lt_w : vRet < 2 ^ w := by
    have hmul : (ci + 1) * (ce.C_space * (inp.prep.J.n + 4 * inp.prep.J0_strip.m * inp.prep.phiDen_dec + 2) ^ ce.c_space) ≤
        inp.prep.rawComps.length * ce.C_space *
          (inp.prep.J.n + 4 * inp.prep.J0_strip.m * inp.prep.phiDen_dec + 2) ^ ce.c_space := by
      rw [Nat.mul_assoc inp.prep.rawComps.length]; exact Nat.mul_le_mul_right _ hci
    have h_le : vRet ≤ inp.maxHeapEnd ce pds := by
      dsimp only [maxHeapEnd]
      calc vRet ≤ aCompExt + 6 * inp.prep.rawComps.length +
              ((inp.prep.rawComps.take (ci + 1)).map fun rc => rc.2.length).sum +
              (ci + 1) * (ce.C_space * (inp.prep.J.n + 4 * inp.prep.J0_strip.m * inp.prep.phiDen_dec + 2) ^ ce.c_space) := hv_hi
        _ ≤ (inp.h + 20 + pds.boundsSpace inp.dJInt inp.prep.J0_strip.m +
                pds.boundsSpace (dWInt ce) (inp.mwInt ce)) +
              6 * inp.prep.rawComps.length + 2 * inp.prep.J0_strip.m +
              inp.prep.rawComps.length * ce.C_space *
                (inp.prep.J.n + 4 * inp.prep.J0_strip.m * inp.prep.phiDen_dec + 2) ^ ce.c_space :=
            Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ha_hi le_rfl) htake_sum) hmul
        _ ≤ _ := by omega
    exact lt_of_le_of_lt h_le hheap_w
  have hwSub_1_lt : curH + kCard + 1 < 2 ^ w :=
    lt_of_le_of_lt (by omega) hv_lt_w
  have hWm : m (curH + kCard + 1) = W.m := graphAt_m hW_at
  have hws_next : inp.ValidWSubsPrefix ce (ci + 1) (WSubs ++ [W]) := by
    refine ⟨by simp [hws_pref.1], fun j hj hjr => ?_⟩
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hj_lt | rfl
    · have hj_l : j < WSubs.length := by rw [hws_pref.1]; exact hj_lt
      have hget : (WSubs ++ [W]).getD j ⟨0, []⟩ = WSubs.getD j ⟨0, []⟩ := by
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hj_l,
          List.getElem_append_left hj_l]
      simpa only [hget] using hws_pref.2 j hj_lt hjr
    · have hget : (WSubs ++ [W]).getD j ⟨0, []⟩ = W := by
        rw [List.getD_eq_getElem _ _ (by simp [hws_pref.1]),
          List.getElem_append_right (Nat.le_of_eq hws_pref.1)]
        simp [hws_pref.1]
      rw [hget]
      refine ⟨by simpa only [← hrc_eq] using hWn, hWval, hWexp, fun k hk => ?_⟩
      simpa only [← hrc_eq] using hWdeg k (by simpa only [← hrc_eq] using hk)
  have hwm_bound := ce_prefix_w_m_bound hvalid hci hws_next
  have hwStart_next_le : wStart + W.m ≤
      inp.prep.J0_strip.m + 2 * ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec := by
    have hmap : ((WSubs ++ [W]).map Graph.m).sum = (WSubs.map Graph.m).sum + W.m := by simp
    linarith only [hwm_bound.2, hwStart_eq, hmap]
  have hwStart_next_lt : wStart + W.m < 2 ^ w := by
    have hpnd := hv.2.2.2.2.2.2.2.2.2.1; have hpn := hv.2.2.2.2.2.2.2.2.1
    have hm1 : inp.prep.J0_strip.m ≤ 4 * (inp.prep.J0_strip.m + 1) * inp.prep.phiDen_dec := by
      have hpd1 : 1 ≤ inp.prep.phiDen_dec := le_trans hpn hpnd
      nlinarith only [hpd1]
    have h2 : 2 * ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec ≤
        2 * ce.c_deg_int * (inp.prep.J0_strip.m + 1) * inp.prep.phiDen_dec := by
      have := Nat.mul_le_mul_right inp.prep.phiDen_dec
        (Nat.mul_le_mul_left (2 * ce.c_deg_int) (Nat.le_succ inp.prep.J0_strip.m))
      nlinarith only [this]
    have hsum : inp.prep.J0_strip.m + 2 * ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec < 2 ^ w := by
      linarith only [hm1, h2, hm_w]
    linarith only [hwStart_next_le, hsum]
  have ha6ci_lt : aCompExt + 6 * ci + 5 < 2 ^ w := by
    have hlt_cur : aCompExt + 6 * ci + 5 < curH := by omega
    linarith only [hlt_cur, hv_lo, hv_lt_w]
  refine runs_start_le ?_
  refine runs_seq_assign_flat (e := .load (.bin .add (.reg 30) (.const 1)))
    (by simp [Expr.eval, BinOp.eval, hr30, h1w, hwSub_1_lt, hWm]; rfl) ?_
  refine runs_seq_assign_flat (e := .bin .add (.reg 18) (.bin .mul (.const 6) (.reg 22)))
    (by simp [Expr.eval, BinOp.eval, Function.update, hr18, hr22, show 6 < 2 ^ w by omega,
      show 6 * ci < 2 ^ w by omega, show aCompExt + 6 * ci < 2 ^ w by omega]; rfl) ?_
  refine runs_seq_store_flat (ea := .reg 33) (ev := .reg 23)
    (by simp [Expr.eval]; rfl) (by simp [Expr.eval, Function.update, hr23]; rfl) ?_
  refine runs_seq_store_flat (ea := .bin .add (.reg 33) (.const 1)) (ev := .reg 30)
    (by simp [Expr.eval, BinOp.eval, h1w, show aCompExt + 6 * ci + 1 < 2 ^ w by omega]; rfl)
    (by simp [Expr.eval, Function.update, hr30]; rfl) ?_
  refine runs_seq_store_flat (ea := .bin .add (.reg 33) (.const 2)) (ev := .reg 28)
    (by simp [Expr.eval, BinOp.eval, show 2 < 2 ^ w by omega,
      show aCompExt + 6 * ci + 2 < 2 ^ w by omega]; rfl)
    (by simp [Expr.eval, Function.update, hr28]; rfl) ?_
  refine runs_seq_store_flat (ea := .bin .add (.reg 33) (.const 3)) (ev := .reg 29)
    (by simp [Expr.eval, BinOp.eval, show 3 < 2 ^ w by omega,
      show aCompExt + 6 * ci + 3 < 2 ^ w by omega]; rfl)
    (by simp [Expr.eval, Function.update, hr29]; rfl) ?_
  refine runs_seq_store_flat (ea := .bin .add (.reg 33) (.const 4)) (ev := .reg 26)
    (by simp [Expr.eval, BinOp.eval, show 4 < 2 ^ w by omega,
      show aCompExt + 6 * ci + 4 < 2 ^ w by omega]; rfl)
    (by simp [Expr.eval, Function.update, hr26]; rfl) ?_
  refine runs_seq_store_flat (ea := .bin .add (.reg 33) (.const 5)) (ev := .reg 32)
    (by simp [Expr.eval, BinOp.eval, show 5 < 2 ^ w by omega,
      show aCompExt + 6 * ci + 5 < 2 ^ w by omega]; rfl)
    (by simp [Expr.eval, Function.update]; rfl) ?_
  refine runs_seq_assign_flat (e := .bin .add (.reg 23) (.reg 32))
    (by simp [Expr.eval, BinOp.eval, Function.update, hr23, hwStart_next_lt]; rfl) ?_
  set m' := Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update m (aCompExt + 6 * ci) wStart)
      (aCompExt + 6 * ci + 1) (curH + kCard))
      (aCompExt + 6 * ci + 2) (2 ^ rc.1))
      (aCompExt + 6 * ci + 3) (inp.prep.phiNum_dec * 2 ^ rc.1))
      (aCompExt + 6 * ci + 4) kCard)
      (aCompExt + 6 * ci + 5) W.m
  refine ⟨.normal,
    { mem := m'
      regs := Function.update (Function.update (Function.update (Function.update regs 32 W.m)
        33 (aCompExt + 6 * ci)) 23 (wStart + W.m)) 17 vRet
      pos := pos },
    _, runs_assign_iff.mpr ⟨vRet, by simp [Expr.eval, Function.update, hr31], rfl, rfl, rfl⟩,
    ?_, by simp [Expr.size]⟩
  have hm_outside : ∀ x, x < aCompExt + 6 * ci ∨ aCompExt + 6 * ci + 5 < x → m' x = m x := by
    intro x hx
    dsimp only [m']
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hm_below_ext : ∀ x < aCompExt, m' x = m x := fun x hx => hm_outside x (Or.inl (by omega))
  have hm_above_curH : ∀ x, curH ≤ x → m' x = m x := fun x hx => hm_outside x (Or.inr (by omega))
  have hcomps_eq : inp.buildCompsFrom inp.prep.j0Edges.length (inp.prep.rawComps.take (ci + 1)) (WSubs ++ [W]) =
      inp.buildCompsFrom inp.prep.j0Edges.length (inp.prep.rawComps.take ci) WSubs ++
        inp.buildCompsFrom wStart [inp.prep.rawComps[ci]] [W] := by
    rw [List.take_succ_eq_append_getElem hci]
    have hlen_t : (inp.prep.rawComps.take ci).length = ci := List.length_take_of_le (by omega)
    rw [buildCompsFrom_append inp inp.prep.j0Edges.length _ [inp.prep.rawComps[ci]] WSubs [W]
      (by rw [hws_pref.1, hlen_t]), hwStart_eq]
  have hcomp_ext_next : CompExtPrefixAt m' aCompExt inp.prep.phiNum_dec vRet
      (inp.buildCompsFrom inp.prep.j0Edges.length (inp.prep.rawComps.take (ci + 1)) (WSubs ++ [W])) := by
    rw [hcomps_eq]
    have hcl_pref : (inp.buildCompsFrom inp.prep.j0Edges.length (inp.prep.rawComps.take ci) WSubs).length = ci := by
      rw [buildCompsFrom_length inp inp.prep.j0Edges.length (inp.prep.rawComps.take ci) WSubs
        (by rw [hws_pref.1, List.length_take_of_le (Nat.le_of_lt hci)]),
        List.length_take_of_le (Nat.le_of_lt hci)]
    have hcl_one : (inp.buildCompsFrom wStart [inp.prep.rawComps[ci]] [W]).length = 1 := rfl
    intro j hj
    rw [List.length_append, hcl_pref, hcl_one] at hj ⊢
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hj_lt | hj_eq
    · have hpj := hcomp_pref j (by rw [hcl_pref]; exact hj_lt)
      dsimp only at hpj
      have hget : (inp.buildCompsFrom inp.prep.j0Edges.length (inp.prep.rawComps.take ci) WSubs ++
          inp.buildCompsFrom wStart [inp.prep.rawComps[ci]] [W])[j]'(by
            rw [List.length_append, hcl_pref, hcl_one]; omega) =
          (inp.buildCompsFrom inp.prep.j0Edges.length (inp.prep.rawComps.take ci) WSubs)[j]'(by
            rw [hcl_pref]; exact hj_lt) :=
        List.getElem_append_left (by rw [hcl_pref]; exact hj_lt)
      simp only [hget]
      have hslot : ∀ t ≤ 5, m' (aCompExt + 6 * j + t) = m (aCompExt + 6 * j + t) :=
        fun t ht => hm_outside _ (Or.inl (by omega))
      have hwSub_j := hj_lo j hj_lt
      refine ⟨(hslot 0 (by omega)).trans hpj.1, (hslot 2 (by omega)).trans hpj.2.1,
        (hslot 3 (by omega)).trans hpj.2.2.1, (hslot 4 (by omega)).trans hpj.2.2.2.1,
        (hslot 5 (by omega)).trans hpj.2.2.2.2.1, ?_, ?_, ?_⟩
      · rw [hslot 1 (by omega)]
        intro k hk
        rw [hm_outside _ (Or.inr (by omega))]
        exact hpj.2.2.2.2.2.1 k hk
      · rw [hslot 1 (by omega)]; omega
      · rw [hslot 1 (by omega)]; exact le_trans hpj.2.2.2.2.2.2.2 (by omega)
    · subst j
      have hget : (inp.buildCompsFrom inp.prep.j0Edges.length (inp.prep.rawComps.take ci) WSubs ++
          inp.buildCompsFrom wStart [inp.prep.rawComps[ci]] [W])[ci]'(by
            rw [List.length_append, hcl_pref, hcl_one]; omega) =
          (inp.buildCompsFrom wStart [inp.prep.rawComps[ci]] [W])[0]'(by simp [buildCompsFrom]) := by
        have hright : (inp.buildCompsFrom inp.prep.j0Edges.length (inp.prep.rawComps.take ci) WSubs ++
              inp.buildCompsFrom wStart [inp.prep.rawComps[ci]] [W])[ci]'(by
                rw [List.length_append, hcl_pref, hcl_one]; omega) =
            (inp.buildCompsFrom wStart [inp.prep.rawComps[ci]] [W])[ci -
              (inp.buildCompsFrom inp.prep.j0Edges.length (inp.prep.rawComps.take ci) WSubs).length]'(by
                rw [hcl_pref]; simp [buildCompsFrom]) :=
          List.getElem_append_right (by rw [hcl_pref])
        simp only [hcl_pref, Nat.sub_self] at hright
        exact hright
      rw [hget]
      simp only [buildCompsFrom, List.getElem_cons_zero]
      have hcard : inp.prep.rawComps[ci].2.toFinset.card = kCard := by
        rw [← hrc_eq, List.toFinset_card_of_nodup hcprops.2.2.2.2.1]
      have h0 : m' (aCompExt + 6 * ci) = wStart := by
        dsimp only [m']
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_self]
      have h1 : m' (aCompExt + 6 * ci + 1) = curH + kCard := by
        dsimp only [m']
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
      have h2 : m' (aCompExt + 6 * ci + 2) = 2 ^ rc.1 := by
        dsimp only [m']
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_self]
      have h3 : m' (aCompExt + 6 * ci + 3) = inp.prep.phiNum_dec * 2 ^ rc.1 := by
        dsimp only [m']
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
      have h4 : m' (aCompExt + 6 * ci + 4) = kCard := by
        dsimp only [m']
        rw [Function.update_of_ne (by omega), Function.update_self]
      have h5 : m' (aCompExt + 6 * ci + 5) = W.m := by dsimp only [m']; rw [Function.update_self]
      refine ⟨h0, by rw [hrc_eq] at h2; exact h2, by rw [hrc_eq] at h3; exact h3,
        by rw [h4, hcard], h5, ?_, by rw [h1]; omega, by rw [h1]; exact hv_lo⟩
      rw [h1]; intro k hk; rw [hm_above_curH _ (by omega)]; exact hW_at k hk
  have hj_next : ∀ j < ci + 1, aCompExt + 6 * inp.prep.rawComps.length ≤ m' (aCompExt + 6 * j + 1) := by
    intro j hj
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hj_lt | rfl
    · rw [hm_outside _ (Or.inl (by omega))]; exact hj_lo j hj_lt
    · dsimp only [m']
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
      omega
  have hr18_end : Function.update (Function.update (Function.update (Function.update
      (Function.update regs 32 W.m) 33 (aCompExt + 6 * ci)) 23 (wStart + W.m)) 17 vRet) 22 (ci + 1) 18 =
      aCompExt := by simp [Function.update, hr18]
  have hr17_end : Function.update (Function.update (Function.update (Function.update
      (Function.update regs 32 W.m) 33 (aCompExt + 6 * ci)) 23 (wStart + W.m)) 17 vRet) 22 (ci + 1) 17 =
      vRet := by simp [Function.update]
  refine ⟨⟨hci, by simp [Function.update],
    ⟨by simp [Function.update, hr0], by simp [Function.update, hr4],
     by simp [Function.update, hr5], by simp [Function.update, hr6],
     by simp [Function.update, hr10], by simp [Function.update, hr11],
     by simp [Function.update, hr12], by simp [Function.update, hr13],
     by simp [Function.update, hr14], by simp [Function.update, hr15],
     by simp [Function.update, hr16],
     by dsimp only; rw [hm_below_ext _ (by omega)]; simp [Function.update, hr18, hhdr12],
     by simp [Function.update, hr18, ha_lo],
     by simp [Function.update, hr18, ha_hi],
     fun x hx => by dsimp only; rw [hm_below_ext _ (by omega)]; exact hbelow x hx,
     witnessHdr0_of_agree_below hhdr0 (by omega) hm_below_ext⟩,
    by dsimp only; rw [hr18_end, hr17_end]; omega,
    by dsimp only; rw [hr18_end, hr17_end]; exact hv_hi,
    fun x hx => by
      dsimp only at hx ⊢
      rw [hr17_end] at hx
      rw [hm_above_curH _ (by omega)]; exact hzf x hx,
    WSubs ++ [W], hws_next,
    by simp [Function.update, hwStart_eq, List.map_append, List.sum_append, Nat.add_assoc],
    by simp [Function.update]; exact hwStart_next_le,
    by dsimp only; rw [hr18_end, hr17_end]; exact hcomp_ext_next,
    by dsimp only; rw [hr18_end]; exact hj_next⟩,
    by simp [Function.update, hr22]⟩

private theorem buildCeBody_triple {w : ℕ} {p : Program}
    {inp : WitnessCoreInput} {ce : ConstructExpanderImpl} {pds : PathDSParams}
    {ceBase : ℕ} {mem₀ : ℕ → ℕ} {ci : ℕ}
    (hce : p.HasAt ceBase (ce.procs ceBase))
    (hvalid : inp.Valid ce pds mem₀ w) (hci : ci < inp.prep.rawComps.length) :
    Triple w p (CeLoopInv inp ce pds mem₀ ci) (buildCeBody ceBase)
      (normalPost fun st =>
        CeLoopInv inp ce pds mem₀ (ci + 1)
          { st with regs := Function.update st.regs 22 (ci + 1) } ∧ st.regs 22 = ci)
      (fun _ => ceStepCost inp ce ci) := by
  intro st ω hinv
  cases st with | mk m regs pos =>
  rcases ce_word_bounds hvalid with ⟨h1w, hheap_w, hm_w⟩
  rcases hinv with ⟨_, h22, hbase, hcur_lo, hcur_hi, hzf, WSubs, hws_pref, hwStart_eq,
    hwStart_le, hcomp_pref, hj_lo⟩
  rcases hbase with ⟨hr0, hr4, hr5, hr6, hr10, hr11, hr12, hr13, hr14, hr15, hr16,
    hhdr12, ha_lo, ha_hi, hbelow, hhdr0⟩
  dsimp only at h22 hcur_lo hcur_hi hzf hwStart_eq hwStart_le hcomp_pref hj_lo
  dsimp only at hr0 hr4 hr5 hr6 hr10 hr11 hr12 hr13 hr14 hr15 hr16 hhdr12 ha_lo ha_hi hbelow hhdr0
  set aCompExt := regs 18
  set curH := regs 17
  set wStart := regs 23
  set rc := inp.prep.rawComps[ci]
  set kCard := rc.2.length
  set lvl := rc.1
  have hv := hvalid.2.2.1
  have hc_lt_h := (inp.input_reads_lt_h hvalid).2.2.2.2.2.2.2 ci hci
  have haC_lt : inp.prep.aComps + 7 * inp.prep.rawComps.length ≤ inp.h :=
    (inp.input_reads_lt_h hvalid).2.2.2.2.2.1
  have hcprops := comp_props_at hv.toValid_zeroTail hci
  have hc_eq : inp.prep.rawComps[ci]! = rc := by simp [rc, hci]
  rw [hc_eq] at hcprops
  have hdone := hvalid.2.2.2.2.2.2.2.2.2.1 ci hci
  dsimp only at hdone
  rw [hc_eq] at hdone
  have hcb := comp_weight_bounds hv hci
  have hk_le_n : kCard ≤ inp.prep.J.n :=
    nodup_lt_length_le hcprops.2.2.2.2.1 hcprops.2.2.2.2.2.1
  have hce_sum := (ceWeights_sum_le hvalid).1
  have htake_kCard : ((inp.prep.rawComps.take ci).map fun x => x.2.length).sum + kCard =
      ((inp.prep.rawComps.take (ci + 1)).map fun x => x.2.length).sum := by
    rw [List.take_succ_eq_append_getElem hci, List.map_append, List.sum_append]
    simp [kCard, rc]
  have htake_all : ((inp.prep.rawComps.take (ci + 1)).map fun x => x.2.length).sum ≤
      2 * inp.prep.J0_strip.m := by
    calc ((inp.prep.rawComps.take (ci + 1)).map fun x => x.2.length).sum
        ≤ (inp.prep.rawComps.map fun x => x.2.length).sum := by
          conv_rhs => rw [← List.take_append_drop (ci + 1) inp.prep.rawComps, List.map_append, List.sum_append]
          exact Nat.le_add_right _ _
      _ ≤ 2 * inp.prep.J0_strip.m := hce_sum
  have hcur_k_space_le : curH + kCard + ce.space kCard (inp.compWeights rc).sum ≤
      aCompExt + 6 * inp.prep.rawComps.length +
        ((inp.prep.rawComps.take (ci + 1)).map fun x => x.2.length).sum +
        (ci + 1) * (ce.C_space * (inp.prep.J.n + 4 * inp.prep.J0_strip.m * inp.prep.phiDen_dec + 2) ^ ce.c_space) := by
    have hs1 := ce.hspace_le kCard (inp.compWeights rc).sum
    have hcw_le : (inp.compWeights rc).sum ≤ 4 * inp.prep.J0_strip.m * inp.prep.phiDen_dec := hcb.2.2.2.2
    have hbase_le : kCard + (inp.compWeights rc).sum + 2 ≤
        inp.prep.J.n + 4 * inp.prep.J0_strip.m * inp.prep.phiDen_dec + 2 :=
      by linarith only [hk_le_n, hcw_le]
    have hs2 : ce.space kCard (inp.compWeights rc).sum ≤
        ce.C_space * (inp.prep.J.n + 4 * inp.prep.J0_strip.m * inp.prep.phiDen_dec + 2) ^ ce.c_space :=
      le_trans hs1 (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase_le _))
    have hsucc : (ci + 1) * (ce.C_space * (inp.prep.J.n + 4 * inp.prep.J0_strip.m * inp.prep.phiDen_dec + 2) ^ ce.c_space) =
        ci * (ce.C_space * (inp.prep.J.n + 4 * inp.prep.J0_strip.m * inp.prep.phiDen_dec + 2) ^ ce.c_space) +
          ce.C_space * (inp.prep.J.n + 4 * inp.prep.J0_strip.m * inp.prep.phiDen_dec + 2) ^ ce.c_space := by
      rw [Nat.succ_mul]
    linarith only [hcur_hi, hs2, htake_kCard, hsucc]
  have hcur_k_space_lt_w : curH + kCard + ce.space kCard (inp.compWeights rc).sum < 2 ^ w := by
    have hmul : (ci + 1) * (ce.C_space * (inp.prep.J.n + 4 * inp.prep.J0_strip.m * inp.prep.phiDen_dec + 2) ^ ce.c_space) ≤
        inp.prep.rawComps.length * ce.C_space *
          (inp.prep.J.n + 4 * inp.prep.J0_strip.m * inp.prep.phiDen_dec + 2) ^ ce.c_space := by
      rw [Nat.mul_assoc inp.prep.rawComps.length]; exact Nat.mul_le_mul_right _ hci
    have h_le : curH + kCard + ce.space kCard (inp.compWeights rc).sum ≤ inp.maxHeapEnd ce pds := by
      dsimp only [maxHeapEnd]
      calc curH + kCard + ce.space kCard (inp.compWeights rc).sum
          ≤ aCompExt + 6 * inp.prep.rawComps.length +
              ((inp.prep.rawComps.take (ci + 1)).map fun rc => rc.2.length).sum +
              (ci + 1) * (ce.C_space * (inp.prep.J.n + 4 * inp.prep.J0_strip.m * inp.prep.phiDen_dec + 2) ^ ce.c_space) :=
            hcur_k_space_le
        _ ≤ (inp.h + 20 + pds.boundsSpace inp.dJInt inp.prep.J0_strip.m +
                pds.boundsSpace (dWInt ce) (inp.mwInt ce)) +
              6 * inp.prep.rawComps.length + 2 * inp.prep.J0_strip.m +
              inp.prep.rawComps.length * ce.C_space *
                (inp.prep.J.n + 4 * inp.prep.J0_strip.m * inp.prep.phiDen_dec + 2) ^ ce.c_space :=
            Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ha_hi le_rfl) htake_all) hmul
        _ ≤ _ := by omega
    exact lt_of_le_of_lt h_le hheap_w
  have h_lt_w : inp.h < 2 ^ w := by
    have : inp.h ≤ inp.maxHeapEnd ce pds := by simp [maxHeapEnd]; omega
    exact lt_of_le_of_lt this hheap_w
  have hmlvl : m (inp.prep.aComps + 7 * ci) = lvl := by
    rw [hbelow (inp.prep.aComps + 7 * ci) (by omega)]; exact hdone.1
  have hmcard : m (inp.prep.aComps + 7 * ci + 1) = kCard := by
    rw [hbelow (inp.prep.aComps + 7 * ci + 1) (by omega)]; exact hdone.2.1
  have hmdeg : m (inp.prep.aComps + 7 * ci + 5) = inp.prep.cDegPtr ci := by
    rw [hbelow (inp.prep.aComps + 7 * ci + 5) (by omega)]; exact hdone.2.2.2.2.2.1
  have hm0_pd_up : 2 * inp.prep.J0_strip.m * inp.prep.phiDen_dec ≤
      4 * (inp.prep.J0_strip.m + 1) * inp.prep.phiDen_dec := by
    have : 2 * inp.prep.J0_strip.m ≤ 4 * (inp.prep.J0_strip.m + 1) := by omega
    exact Nat.mul_le_mul_right inp.prep.phiDen_dec this
  have hpow_lt : 2 ^ lvl < 2 ^ w := by
    have h_le : 2 ^ lvl ≤ 4 * (inp.prep.J0_strip.m + 1) * inp.prep.phiDen_dec :=
      le_trans hcb.2.1 hm0_pd_up
    exact lt_of_le_of_lt (le_trans h_le (by omega)) hm_w
  have hdenom_lt : inp.prep.phiNum_dec * 2 ^ lvl < 2 ^ w := by
    have h_le : inp.prep.phiNum_dec * 2 ^ lvl ≤ 4 * (inp.prep.J0_strip.m + 1) * inp.prep.phiDen_dec :=
      le_trans hcb.1 hm0_pd_up
    exact lt_of_le_of_lt (le_trans h_le (by omega)) hm_w
  have hcw_ce : ce.cw * (Nat.log 2 (kCard + (inp.compWeights rc).sum + 2) + 1) ≤ w := by
    have hcw_base := hvalid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hlog : Nat.log 2 (kCard + (inp.compWeights rc).sum + 2) ≤
        Nat.log 2 (inp.prep.J.n + 4 * inp.prep.J0_strip.m * inp.prep.phiDen_dec + 2) :=
      Nat.log_mono_right (Nat.add_le_add_right (Nat.add_le_add hk_le_n hcb.2.2.2.2) 2)
    exact le_trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hlog 1)) hcw_base
  dsimp only [buildCeBody]
  refine runs_start_le ?_
  refine runs_seq_assign_flat (e := .bin .add (.reg 15) (.bin .mul (.const 7) (.reg 22)))
    (by simp [Expr.eval, BinOp.eval, hr15, h22, show 7 < 2 ^ w by omega,
      show 7 * ci < 2 ^ w by omega, show inp.prep.aComps + 7 * ci < 2 ^ w by omega]; rfl) ?_
  refine runs_seq_assign_flat (e := .load (.reg 24))
    (by simp [Expr.eval, Function.update, hmlvl]; rfl) ?_
  refine runs_seq_assign_flat (e := .load (.bin .add (.reg 24) (.const 1)))
    (by simp [Expr.eval, BinOp.eval, Function.update, h1w,
      show inp.prep.aComps + 7 * ci + 1 < 2 ^ w by omega, hmcard]; rfl) ?_
  refine runs_seq_assign_flat (e := .load (.bin .add (.reg 24) (.const 5)))
    (by simp [Expr.eval, BinOp.eval, Function.update, show 5 < 2 ^ w by omega,
      show inp.prep.aComps + 7 * ci + 5 < 2 ^ w by omega, hmdeg]; rfl) ?_
  refine runs_seq_assign_flat (e := .bin .shiftLeft (.const 1) (.reg 25))
    (by simp [Expr.eval, BinOp.eval, Function.update, h1w, Nat.one_shiftLeft lvl, hpow_lt]; rfl) ?_
  refine runs_seq_assign_flat (e := .bin .mul (.reg 10) (.reg 28))
    (by simp [Expr.eval, BinOp.eval, Function.update, hr10, hdenom_lt]; rfl) ?_
  refine runs_seq_assign_flat (e := .const 0)
    (by simp [Expr.eval, show 0 < 2 ^ w by omega]; rfl) ?_
  set regsF := Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update regs 24 (inp.prep.aComps + 7 * ci))
      25 lvl) 26 kCard) 27 (inp.prep.cDegPtr ci)) 28 (2 ^ lvl))
      29 (inp.prep.phiNum_dec * 2 ^ lvl)) 30 0
  refine runs_seq_triple_le (buildWeightFill_triple hvalid hci (kCard := kCard) rfl (by omega)
    (lt_of_le_of_lt (Nat.le_add_right _ _) hcur_k_space_lt_w) hc_lt_h.2.2 hbelow
    (by simp [regsF, hr11]) (by simp [regsF, curH]) (by simp [regsF]) (by simp [regsF])
    (by simp [regsF, lvl, rc]))
    ⟨Nat.zero_le _, by simp [regsF], fun _ _ => rfl, fun _ _ => rfl, by simp [ListAt], hzf⟩ ?_
  intro st₁ hpost₁
  rcases hpost₁ with ⟨_, hr30_1, hregs_1, hbelow_1, hlistW_1, hzf_1⟩
  cases st₁ with | mk m₁ regs₁ pos₁ =>
  dsimp only at hr30_1 hregs_1 hbelow_1 hlistW_1 hzf_1
  rw [hc_eq] at hlistW_1
  have hlistW_full : ListAt m₁ curH (inp.compWeights rc) := by
    have htake : List.take kCard (inp.compWeights rc) = inp.compWeights rc := by
      dsimp only [kCard, rc]; rw [← hcb.2.2.1, List.take_length]
    rwa [htake] at hlistW_1
  have hmap_ce : ((List.range kCard).map fun v => m₁ (curH + v)) = inp.compWeights rc := by
    have hlen_w : (inp.compWeights rc).length = kCard := hcb.2.2.1
    apply List.ext_getElem
    · simp [hlen_w]
    · intro i hi1 hi2
      rw [List.getElem_map, List.getElem_range]
      exact hlistW_full i hi2
  have hsum_ce : ((List.range kCard).map fun v => m₁ (curH + v)).sum = (inp.compWeights rc).sum :=
    congrArg List.sum hmap_ce
  have hr17_1 : regs₁ 17 = curH := by
    rw [hregs_1 17 (by omega)]; simp [regsF, Function.update]; rfl
  have hr26_1 : regs₁ 26 = kCard := by rw [hregs_1 26 (by omega)]; simp [regsF, Function.update]
  refine runs_seq_assign_flat (e := .bin .add (.reg 17) (.reg 26))
    (by simp [Expr.eval, BinOp.eval, hr17_1, hr26_1, show curH + kCard < 2 ^ w by omega]; rfl) ?_
  have hf_ce := ce.meets (w := w) (p := p) (b := ceBase) hce
  refine WordRAM.runs_seq_call_le (vs := [kCard, curH, curH + kCard]) hf_ce
    (by simp [evalArgs, Expr.eval, hr26_1, hr17_1, Function.update])
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with rfl | rfl | rfl <;> omega)
    (by
      refine ⟨⟨kCard, curH, curH + kCard, inp.compWeights rc, rfl, hcprops.2.2.2.1, le_rfl,
        hlistW_full, hcb.2.2.1, fun v hv => (hcb.2.2.2.1 v (by rw [← hcb.2.2.1]; exact hv)).1, ?_⟩, ?_, ?_⟩
      · simpa [hcb.2.2.1] using hcw_ce
      · simpa [heapArg] using hzf_1
      · simp only [heapArg, List.getLastD_cons, List.getLastD_nil, List.getD_cons_zero, List.getD_cons_succ]
        rw [hsum_ce]; exact hcur_k_space_lt_w) ?_
  intro vRet m₂ pos₂ hpost_ce
  rcases hpost_ce with ⟨⟨hlo_ce, hhi_ce, hagree_ce, hzf_ce, n', wAddr', h', wList', W,
    heq_ce, hwlist_len, hwlist_at, hW_at, hWn, hWval, hWexp, hWdeg⟩, hv_le_sum⟩
  simp only [List.cons.injEq, and_true] at heq_ce
  rcases heq_ce with ⟨rfl, rfl, rfl⟩
  simp only [heapArg, List.getLastD_cons, List.getLastD_nil, List.getD_cons_zero, List.getD_cons_succ] at hlo_ce hhi_ce hagree_ce hW_at hwlist_len hwlist_at
  rw [hsum_ce] at hhi_ce
  have hm2_below_curH : ∀ x < curH, m₂ x = m x := fun x hx =>
    (hagree_ce x (by omega)).trans (hbelow_1 x hx)
  have hv_lo : curH + kCard + (2 + 2 * W.m) ≤ vRet := by
    rcases hv_le_sum with ⟨W', hW', hle⟩
    simp only [heapArg, List.getLastD_cons, List.getLastD_nil] at hW' hle
    rw [graphAt_unique hW' hW_at] at hle
    exact hle
  have hwlist_eq : wList' = inp.compWeights rc :=
    List.ext_getElem (by rw [hwlist_at]; exact hcb.2.2.1.symm) fun i hi1 hi2 =>
      (hwlist_len i hi1).symm.trans (hlistW_full i hi2)
  have hcost_ce : (constructExpanderContract ce w).cost [kCard, curH, curH + kCard] m₁ =
      Nat.ceil (ce.K_ce * ((rc.2.length : ℝ) + ((inp.compWeights rc).sum : ℝ))) := by
    simp only [constructExpanderContract, constructExpanderHeapContract, heapContract,
      List.getD_cons_zero, List.getD_cons_succ]
    rw [hsum_ce]
  have hreg_eq : ∀ r ≤ 29, Function.update (Function.update regs₁ 30 (curH + kCard)) 31 vRet r = regsF r := by
    intro r hr
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hregs_1 r hr
  refine runs_triple_le
    (ce_afterCall_triple hvalid (aCompExt := aCompExt) (curH := curH) (wStart := wStart)
      (WSubs := WSubs) (W := W) (vRet := vRet))
    ?_ (fun _ _ h => h)
    (by simp only [ceStepCost, hc_eq, Expr.size, argsSize]; rw [hcost_ce]; omega)
  unfold CeAfterCallPre
  dsimp only
  refine ⟨hci, by simpa [hc_eq] using hk_le_n,
    by rw [hreg_eq 0 (by omega)]; simp [regsF, Function.update, hr0],
    by rw [hreg_eq 4 (by omega)]; simp [regsF, Function.update, hr4],
    by rw [hreg_eq 5 (by omega)]; simp [regsF, Function.update, hr5],
    by rw [hreg_eq 6 (by omega)]; simp [regsF, Function.update, hr6],
    by rw [hreg_eq 10 (by omega)]; simp [regsF, Function.update, hr10],
    by rw [hreg_eq 11 (by omega)]; simp [regsF, Function.update, hr11],
    by rw [hreg_eq 12 (by omega)]; simp [regsF, Function.update, hr12],
    by rw [hreg_eq 13 (by omega)]; simp [regsF, Function.update, hr13],
    by rw [hreg_eq 14 (by omega)]; simp [regsF, Function.update, hr14],
    by rw [hreg_eq 15 (by omega)]; simp [regsF, Function.update, hr15],
    by rw [hreg_eq 16 (by omega)]; simp [regsF, Function.update, hr16],
    by rw [hreg_eq 18 (by omega)]; simp [regsF, Function.update]; rfl,
    by rw [hreg_eq 22 (by omega)]; simp [regsF, Function.update, h22],
    by rw [hreg_eq 23 (by omega)]; simp [regsF, Function.update]; rfl,
    by rw [hreg_eq 26 (by omega)]; simp [regsF, Function.update, hc_eq]; rfl,
    by rw [hreg_eq 28 (by omega)]; simp [regsF, Function.update, hc_eq]; rfl,
    by rw [hreg_eq 29 (by omega)]; simp only [regsF]; rw [Function.update_of_ne (by decide), Function.update_self, hc_eq],
    by rw [Function.update_of_ne (by omega), Function.update_self, hc_eq],
    by rw [Function.update_self],
    by rw [hm2_below_curH _ (by omega)]; exact hhdr12, ha_lo, ha_hi, hcur_lo,
    by simp only [hc_eq]; exact hv_lo,
    le_trans hhi_ce hcur_k_space_le,
    fun x hx => (hm2_below_curH x (by omega)).trans (hbelow x hx),
    witnessHdr0_of_agree_below hhdr0 (by omega) hm2_below_curH, hzf_ce,
    by simp only [hc_eq]; exact hW_at,
    by simp only [hc_eq]; exact hWn, hWval, hWexp,
    fun k hk => by
      simp only [hc_eq]
      have hd := hWdeg k (by rw [hwlist_eq, hcb.2.2.1]; simpa [hc_eq] using hk)
      simp only [hwlist_eq] at hd
      exact hd,
    hws_pref, hwStart_eq, compExtPrefix_of_agree_below hcomp_pref hm2_below_curH,
    fun j hj => by rw [hm2_below_curH _ (by omega)]; exact hj_lo j hj⟩

/-- Full verification of Phase 2 (`buildCeLoopStmt ceBase`) from `Phase01Post` to `CeLoopPost`. -/
theorem buildCeLoop_triple {w : ℕ} {p : Program}
    {inp : WitnessCoreInput} {ce : ConstructExpanderImpl} {pds : PathDSParams}
    {ceBase : ℕ} {mem₀ : ℕ → ℕ}
    (hce : p.HasAt ceBase (ce.procs ceBase))
    (hvalid : inp.Valid ce pds mem₀ w) :
    Triple w p (Phase01Post inp ce pds mem₀)
      (buildCeLoopStmt ceBase)
      (normalPost (CeLoopPost inp ce pds mem₀))
      (fun _ => ceLoopCost inp ce) := by
  have hv := hvalid.2.2.1
  rcases ce_word_bounds hvalid with ⟨h1w, hheap_w, hm_w⟩
  have haC_lt := (inp.input_reads_lt_h hvalid).2.2.2.2.2.1
  have hrcl_lt_w : inp.prep.rawComps.length < 2 ^ w := by
    have : inp.h ≤ inp.maxHeapEnd ce pds := by simp [maxHeapEnd]; omega
    omega
  dsimp only [buildCeLoopStmt]
  let MidInv : State → Prop := fun st =>
    CeBaseInv inp ce pds mem₀ st ∧
    st.regs 18 + 6 * inp.prep.rawComps.length ≤ st.regs 17 ∧
    st.regs 17 ≤ st.regs 18 + 6 * inp.prep.rawComps.length ∧
    ZeroFrom st.mem (st.regs 17) ∧
    st.regs 23 = inp.prep.j0Edges.length
  refine Triple.seq_normal (R := MidInv)
    (T₂ := fun _ => rangeCost (ceStepCost inp ce) 0 inp.prep.rawComps.length +
      9 * inp.prep.rawComps.length + 7)
    (Triple.assign (val := fun _ => inp.prep.j0Edges.length)
      (fun st hP => by simp [Expr.eval, hP.2.2.2.2.2.2.2.2.2.2.2.2.1])
      (fun st hP => by
        rcases hP with ⟨hr0, _, _, _, hr4, hr5, hr6, _, _, _, hr10, hr11, hr12, hr13, hr14, hr15,
          hr16, hhdr12, ha_lo, ha_hi, hcur, hbelow, hzf, hhdr0⟩
        exact ⟨⟨by simp [Function.update, hr0], by simp [Function.update, hr4],
           by simp [Function.update, hr5], by simp [Function.update, hr6],
           by simp [Function.update, hr10], by simp [Function.update, hr11],
           by simp [Function.update, hr12], by simp [Function.update, hr13],
           by simp [Function.update, hr14], by simp [Function.update, hr15],
           by simp [Function.update, hr16], by simp [Function.update, hhdr12],
           by simp [Function.update]; exact ha_lo,
           by simp [Function.update]; exact ha_hi,
           hbelow, hhdr0⟩,
          by simp [Function.update]; omega, by simp [Function.update]; omega,
          by simp [Function.update]; exact hzf, by simp [Function.update]⟩))
    ?_ (fun _ _ _ _ => by simp only [ceLoopCost, Expr.size]; omega)
  refine ((Triple.forRange_le (P := MidInv) (ceStepCost inp ce) 0 inp.prep.rawComps.length
    (Nat.zero_le _) h1w (fun _ => hrcl_lt_w)
    (fun st hMid => by
      refine ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], ?_⟩
      rcases hMid with ⟨hbase, hcur_lo, hcur_hi, hzf, hr23⟩
      exact ⟨Nat.zero_le _, by simp [Function.update],
        ⟨by simp [Function.update, hbase.1], by simp [Function.update, hbase.2.1],
         by simp [Function.update, hbase.2.2.1], by simp [Function.update, hbase.2.2.2.1],
         by simp [Function.update, hbase.2.2.2.2.1], by simp [Function.update, hbase.2.2.2.2.2.1],
         by simp [Function.update, hbase.2.2.2.2.2.2.1], by simp [Function.update, hbase.2.2.2.2.2.2.2.1],
         by simp [Function.update, hbase.2.2.2.2.2.2.2.2.1],
         by simp [Function.update, hbase.2.2.2.2.2.2.2.2.2.1],
         by simp [Function.update, hbase.2.2.2.2.2.2.2.2.2.2.1],
         by simp [Function.update, hbase.2.2.2.2.2.2.2.2.2.2.2.1],
         by simp [Function.update]; exact hbase.2.2.2.2.2.2.2.2.2.2.2.2.1,
         by simp [Function.update]; exact hbase.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
         hbase.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hbase.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩,
        by simp [Function.update]; exact hcur_lo,
        by simp [Function.update]; omega,
        by simp [Function.update]; exact hzf,
        [], ⟨rfl, fun _ h => (Nat.not_lt_zero _ h).elim⟩,
        by simp [Function.update, hr23],
        by have := PrepInput.StaticValid.size_bounds hv; simp [Function.update, hr23]; omega,
        fun _ h => (Nat.not_lt_zero _ h).elim, fun _ h => (Nat.not_lt_zero _ h).elim⟩)
    (fun _ _ _ _ h => h.2.1)
    (fun _ _ _ _ h => by simp [Expr.eval, h.2.2.1.2.2.2.2.2.2.2.2.1])
    (fun ci _ hci => buildCeBody_triple hce hvalid hci)).mono_cost
      (fun _ _ => by simp only [Expr.size]; omega)).strengthen_post ?_
  intro o st hpost
  cases o with
  | returned _ => exact False.elim hpost
  | normal =>
  rcases hpost with ⟨_, _, hbase, hcur_lo, hcur_hi, hzf, WSubs, hws_pref, hwStart_eq, hwStart_le,
    hcomp_pref, _⟩
  have hws : inp.ValidWSubs ce WSubs := ⟨hws_pref.1, fun j hj => hws_pref.2 j hj hj⟩
  have hWm_eq : (inp.mkWitnessData ce pds WSubs).W.m =
      inp.prep.j0Edges.length + (WSubs.map Graph.m).sum :=
    mkWitnessData_W_m_eq_sum inp ce pds hws.1
  have hce_sum := (ceWeights_sum_le hvalid).1
  have hmax_le : st.regs 17 + (2 + 6 * (inp.mkWitnessData ce pds WSubs).W.m + 3 * inp.prep.J.m) ≤
      inp.maxHeapEnd ce pds := by
    have ha_hi := hbase.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    rw [List.take_length] at hcur_hi
    dsimp only [maxHeapEnd]
    linarith only [hcur_hi, ha_hi, hce_sum, hwStart_le, hwStart_eq, hWm_eq]
  refine ⟨hbase, hcur_lo, hzf, WSubs, hws, hwStart_eq.trans hWm_eq.symm, ?_, hmax_le⟩
  rw [List.take_length] at hcomp_pref
  exact hcomp_pref

end MinCostFlow.Spanner
