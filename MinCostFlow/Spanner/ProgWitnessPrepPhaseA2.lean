module

public import MinCostFlow.Spanner.ProgWitnessPrepHelpers

/-!
# Phase A2 Verification for `witnessPrep` (`prepHdrStore`, `prepParse`)

Proves Hoare triples for header initialization (`prepHdrStoreStmt`) and component-table metadata
parsing (`prepParseStmt`).
-/

public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-- Verification of `prepHdrStoreStmt`: writes the 8-word preparation header at `h..h+7` and
initializes component parse cursor registers. -/
theorem prepHdrStore_triple {w : ℕ} {p : Program} (inp : PrepInput) (mem₀ : ℕ → ℕ)
    (hv : inp.Valid mem₀ w) :
    Triple w p
      (fun st =>
        AgreeOutside st.mem mem₀ inp.aLvlHead inp.aComps ∧
        (∀ x < inp.h, st.mem x = mem₀ x) ∧
        PrepBaseRegs inp st ∧
        st.regs 12 = inp.j0Edges.length ∧
        ListAt st.mem inp.aJ0Out inp.j0Edges ∧
        ∀ lvl ≤ inp.d_ℓ,
          ChainAt st.mem inp.aEdgeNext (st.mem (inp.aLvlHead + lvl))
            (DecomposeOutput.edgesAt inp.J0_strip inp.decomp lvl))
      prepHdrStoreStmt
      (normalPost fun st =>
        AgreeOutside st.mem mem₀ inp.h inp.aComps ∧
        PrepStaticState inp mem₀ st.mem ∧
        ZeroFrom st.mem inp.aComps ∧
        PrepFullRegs inp st ∧
        st.regs 16 = inp.cJSubPtr 0 ∧
        st.regs 17 = 0 ∧
        st.regs 18 = inp.decAddr + 4 + inp.J0_strip.m)
      (fun _ => 100) := by
  intro st ω ⟨hag, hlt, hb, h12, hl, hch⟩
  have hsz := inp.size_bounds hv
  rcases hv with ⟨hJ, hgJ, hJ0, hgJ0, hnl, hlNl, hdec, hllen, hpn, hpnd, hpw, hprops, hdp,
    hjle, hj0le, hnlle, hdecle, hzero, hw1, hwb⟩
  have hdecF := decomposeOutAt_fields hdec
  have hj0len_lt : inp.j0Edges.length < 2 ^ w := by omega
  have haC_lt : inp.aComps < 2 ^ w := by
    simp only [PrepInput.aComps, PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega
  have haVC_lt : inp.aVComp < 2 ^ w := by
    simp only [PrepInput.aVComp, PrepInput.aComps, PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega
  have haVL_lt : inp.aVLoc < 2 ^ w := by
    simp only [PrepInput.aVLoc, PrepInput.aVComp, PrepInput.aComps, PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega
  have hBS_lt : inp.hBlocksStart < 2 ^ w := by
    rw [inp.hBlocksStart_eq]
    simp only [PrepInput.aVLoc, PrepInput.aVComp, PrepInput.aComps, PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega
  have haJ0_lt : inp.aJ0Out < 2 ^ w := by simp [PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega
  have hnumC_lt : inp.rawComps.length < 2 ^ w := by omega
  have haLH_lt : inp.aLvlHead < 2 ^ w := by simp [PrepInput.aLvlHead]; omega
  have haEN_lt : inp.aEdgeNext < 2 ^ w := by simp [PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega
  have h7c_lt : 7 * inp.rawComps.length < 2 ^ w := by omega
  have hdec34_lt : inp.decAddr + 4 < 2 ^ w := by
    have := decompose_encode_length inp.d_ℓ inp.phiNum_dec inp.phiDen_dec inp.level inp.rawComps
    omega
  have hraw0_lt : inp.decAddr + 4 + inp.J0_strip.m < 2 ^ w := by
    have := decompose_encode_length inp.d_ℓ inp.phiNum_dec inp.phiDen_dec inp.level inp.rawComps
    omega
  dsimp only [prepHdrStoreStmt]
  refine runs_seq_assign0 (v := inp.aComps) ?_ ?_
  · exact ev_add (ev_reg hb.2.2.2.2.2.2.2.2.2.2.2 haJ0_lt) (ev_reg h12 hj0len_lt) (by simp only [PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega)
  refine runs_seq_assign_le (v := inp.aVComp) ?_ ?_
  · exact ev_add (ev_reg (by simp) haC_lt)
      (ev_mul (ev_const (c := 7) (by omega)) (ev_reg (by simp [hb.2.2.2.2.2.2.2.2.1]) hnumC_lt) h7c_lt)
      (by simp only [PrepInput.aComps, PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega)
  refine runs_seq_assign_le (v := inp.aVLoc) ?_ ?_
  · exact ev_add (ev_reg (by simp) haVC_lt) (ev_reg (by simp [hb.2.2.2.2.2.1]) (by omega)) (by simp only [PrepInput.aVComp, PrepInput.aComps, PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega)
  refine runs_seq_assign_le (v := inp.hBlocksStart) ?_ ?_
  · rw [inp.hBlocksStart_eq]
    exact ev_add (ev_reg (by simp) haVL_lt) (ev_reg (by simp [hb.2.2.2.2.2.1]) (by omega)) (by simp only [PrepInput.aVLoc, PrepInput.aVComp, PrepInput.aComps, PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega)
  refine runs_seq_store_le (x := inp.h) (v := inp.j0Edges.length) ?_ ?_ ?_
  · exact ev_reg (by simp [hb.2.2.2.2.1]) (by omega)
  · exact ev_reg (by simp [h12]) hj0len_lt
  refine runs_seq_store_le (x := inp.h + 1) (v := inp.aJ0Out) ?_ ?_ ?_
  · exact ev_add (ev_reg (by simp [hb.2.2.2.2.1]) (by omega)) (ev_const hw1) (by omega)
  · exact ev_reg (by simp [hb.2.2.2.2.2.2.2.2.2.2.2]) haJ0_lt
  refine runs_seq_store_le (x := inp.h + 2) (v := inp.rawComps.length) ?_ ?_ ?_
  · exact ev_add (ev_reg (by simp [hb.2.2.2.2.1]) (by omega)) (ev_const (by omega)) (by omega)
  · exact ev_reg (by simp [hb.2.2.2.2.2.2.2.2.1]) hnumC_lt
  refine runs_seq_store_le (x := inp.h + 3) (v := inp.aComps) ?_ ?_ ?_
  · exact ev_add (ev_reg (by simp [hb.2.2.2.2.1]) (by omega)) (ev_const (by omega)) (by omega)
  · exact ev_reg (by simp) haC_lt
  refine runs_seq_store_le (x := inp.h + 4) (v := inp.aLvlHead) ?_ ?_ ?_
  · exact ev_add (ev_reg (by simp [hb.2.2.2.2.1]) (by omega)) (ev_const (by omega)) (by omega)
  · exact ev_reg (by simp [hb.2.2.2.2.2.2.2.2.2.1]) haLH_lt
  refine runs_seq_store_le (x := inp.h + 5) (v := inp.aEdgeNext) ?_ ?_ ?_
  · exact ev_add (ev_reg (by simp [hb.2.2.2.2.1]) (by omega)) (ev_const (by omega)) (by omega)
  · exact ev_reg (by simp [hb.2.2.2.2.2.2.2.2.2.2.1]) haEN_lt
  refine runs_seq_store_le (x := inp.h + 6) (v := inp.aVComp) ?_ ?_ ?_
  · exact ev_add (ev_reg (by simp [hb.2.2.2.2.1]) (by omega)) (ev_const (by omega)) (by omega)
  · exact ev_reg (by simp) haVC_lt
  refine runs_seq_store_le (x := inp.h + 7) (v := inp.aVLoc) ?_ ?_ ?_
  · exact ev_add (ev_reg (by simp [hb.2.2.2.2.1]) (by omega)) (ev_const (by omega)) (by omega)
  · exact ev_reg (by simp) haVL_lt
  refine runs_seq_assign_le (v := inp.decAddr + 4 + inp.J0_strip.m) ?_ ?_
  · exact ev_add (ev_add (ev_reg (by simp [hb.2.2.2.1]) (by omega)) (ev_const (by omega)) hdec34_lt)
      (ev_reg (by simp [hb.2.2.2.2.2.2.1]) (by omega)) hraw0_lt
  refine ⟨.normal, _, _, runs_assign_iff.mpr ⟨0, ev_const (by omega), rfl, rfl, rfl⟩,
    ?_, by norm_num [Expr.size]⟩
  dsimp only [normalPost]
  set m0 := Function.update st.mem inp.h inp.j0Edges.length
  set m1 := Function.update m0 (inp.h + 1) inp.aJ0Out
  set m2 := Function.update m1 (inp.h + 2) inp.rawComps.length
  set m3 := Function.update m2 (inp.h + 3) inp.aComps
  set m4 := Function.update m3 (inp.h + 4) inp.aLvlHead
  set m5 := Function.update m4 (inp.h + 5) inp.aEdgeNext
  set m6 := Function.update m5 (inp.h + 6) inp.aVComp
  set m7 := Function.update m6 (inp.h + 7) inp.aVLoc
  have hAgree : AgreeOutside m7 mem₀ inp.h inp.aComps := by
    have ha0 : AgreeOutside m7 st.mem inp.h (inp.h + 8) := by
      intro x hx
      rcases hx with hxlo | hxhi
      · simp [m7, m6, m5, m4, m3, m2, m1, m0,
          Function.update_of_ne (by omega : x ≠ inp.h + 7),
          Function.update_of_ne (by omega : x ≠ inp.h + 6),
          Function.update_of_ne (by omega : x ≠ inp.h + 5),
          Function.update_of_ne (by omega : x ≠ inp.h + 4),
          Function.update_of_ne (by omega : x ≠ inp.h + 3),
          Function.update_of_ne (by omega : x ≠ inp.h + 2),
          Function.update_of_ne (by omega : x ≠ inp.h + 1),
          Function.update_of_ne (by omega : x ≠ inp.h)]
      · simp [m7, m6, m5, m4, m3, m2, m1, m0,
          Function.update_of_ne (by omega : x ≠ inp.h + 7),
          Function.update_of_ne (by omega : x ≠ inp.h + 6),
          Function.update_of_ne (by omega : x ≠ inp.h + 5),
          Function.update_of_ne (by omega : x ≠ inp.h + 4),
          Function.update_of_ne (by omega : x ≠ inp.h + 3),
          Function.update_of_ne (by omega : x ≠ inp.h + 2),
          Function.update_of_ne (by omega : x ≠ inp.h + 1),
          Function.update_of_ne (by omega : x ≠ inp.h)]
    have hag' : AgreeOutside st.mem mem₀ inp.h inp.aComps :=
      agreeOutside_mono hag (by simp [PrepInput.aLvlHead]) le_rfl
    exact agreeOutside_trans ha0 hag' le_rfl (by simp [PrepInput.aComps, PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega)
  refine ⟨hAgree, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hlt_m7 : ∀ x < inp.h, m7 x = mem₀ x := fun x hx =>
      hAgree x (Or.inl hx)
    have haJ0_agree : ∀ x, inp.aLvlHead ≤ x → x < inp.aComps → m7 x = st.mem x := by
      intro x hx1 hx2
      have hx8 : inp.h + 8 ≤ x := by simp only [PrepInput.aLvlHead] at hx1; omega
      simp [m7, m6, m5, m4, m3, m2, m1, m0,
        Function.update_of_ne (by omega : x ≠ inp.h + 7),
        Function.update_of_ne (by omega : x ≠ inp.h + 6),
        Function.update_of_ne (by omega : x ≠ inp.h + 5),
        Function.update_of_ne (by omega : x ≠ inp.h + 4),
        Function.update_of_ne (by omega : x ≠ inp.h + 3),
        Function.update_of_ne (by omega : x ≠ inp.h + 2),
        Function.update_of_ne (by omega : x ≠ inp.h + 1),
        Function.update_of_ne (by omega : x ≠ inp.h)]
    refine ⟨hlt_m7, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [m7, m6, m5, m4, m3, m2, m1, m0]
    · simp [m7, m6, m5, m4, m3, m2, m1]
    · simp [m7, m6, m5, m4, m3, m2]
    · simp [m7, m6, m5, m4, m3]
    · simp [m7, m6, m5, m4]
    · simp [m7, m6, m5]
    · simp [m7, m6]
    · simp [m7]
    · refine listAt_of_congr hl fun i hi => haJ0_agree (inp.aJ0Out + i)
        (by simp [PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega)
        (by simp [PrepInput.aComps]; omega)
    · intro lvl hlvl
      have hhd_eq : m7 (inp.aLvlHead + lvl) = st.mem (inp.aLvlHead + lvl) :=
        haJ0_agree _ (by omega)
          (by simp [PrepInput.aComps, PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega)
      rw [hhd_eq]
      refine chainAt_of_agree (hch lvl hlvl) fun q hq => ?_
      simp only [DecomposeOutput.edgesAt, List.mem_filter, List.mem_range] at hq
      have hqm := hq.1
      exact haJ0_agree (inp.aEdgeNext + q)
        (by simp [PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega)
        (by simp [PrepInput.aComps, PrepInput.aJ0Out]; omega)
  · exact fun x hx => (hAgree x (Or.inr hx)).trans (hzero x (by
      simp only [PrepInput.aComps, PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead] at hx
      omega))
  · refine ⟨prepBaseRegs_congr hb (fun r hr => by
        dsimp only
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]),
      ?_, ?_, ?_, ?_⟩ <;> simp [h12]
  · simp [PrepInput.cJSubPtr_zero]
  · simp
  · simp

/-- Loop invariant for `prepParseStmt` after parsing `ci` component records. -/
@[expose] def prepParseInv (inp : PrepInput) (mem₀ : ℕ → ℕ) (ci : ℕ) (st : State) : Prop :=
  AgreeOutside st.mem mem₀ inp.h (inp.aComps + 7 * ci) ∧
  PrepStaticState inp mem₀ st.mem ∧
  ZeroFrom st.mem (inp.aComps + 7 * ci) ∧
  PrepFullRegs inp st ∧
  st.regs 16 = inp.cJSubPtr 0 ∧
  st.regs 17 = ci ∧
  st.regs 18 = inp.cVertsPtr ci - 2 ∧
  ∀ k < ci,
    st.mem (inp.aComps + 7 * k) = inp.rawComps[k]!.1 ∧
    st.mem (inp.aComps + 7 * k + 1) = inp.rawComps[k]!.2.length ∧
    st.mem (inp.aComps + 7 * k + 2) = inp.cVertsPtr k ∧
    st.mem (inp.aComps + 7 * k + 3) = 0 ∧
    st.mem (inp.aComps + 7 * k + 4) = 0 ∧
    st.mem (inp.aComps + 7 * k + 5) = 0 ∧
    st.mem (inp.aComps + 7 * k + 6) = 0

/-- Verification of `prepParseStmt`: scans component records in `decAddr` and populates metadata
in the component table at `aComps`. -/
theorem prepParse_triple {w : ℕ} {p : Program} (inp : PrepInput) (mem₀ : ℕ → ℕ)
    (hv : inp.Valid mem₀ w) :
    Triple w p
      (fun st =>
        AgreeOutside st.mem mem₀ inp.h inp.aComps ∧
        PrepStaticState inp mem₀ st.mem ∧
        ZeroFrom st.mem inp.aComps ∧
        PrepFullRegs inp st ∧
        st.regs 16 = inp.cJSubPtr 0 ∧
        st.regs 17 = 0 ∧
        st.regs 18 = inp.decAddr + 4 + inp.J0_strip.m)
      prepParseStmt
      (normalPost (prepParseInv inp mem₀ inp.rawComps.length))
      (fun _ => 60 * inp.J0_strip.m + 10) := by
  have hsz := inp.size_bounds hv
  have hw1 : 1 < 2 ^ w := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hwb : inp.h + 9 + inp.d_ℓ + 16 * inp.J0_strip.m + 2 * inp.J.n < 2 ^ w :=
    hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hnc_lt : 0 < inp.rawComps.length → inp.rawComps.length < 2 ^ w := fun _ => by omega
  have hmain : Triple w p (prepParseInv inp mem₀ 0) prepParseStmt
      (normalPost (prepParseInv inp mem₀ inp.rawComps.length))
      (fun _ => inp.rawComps.length * (45 + (Expr.reg 8).size + 8) + ((Expr.reg 8).size + 3)) := by
    refine Triple.forUp_const (r := 17) (hi := .reg 8) (body := prepParseBody)
      (Inv := prepParseInv inp mem₀) 45 0 inp.rawComps.length
      (Nat.zero_le _) hw1 hnc_lt
      (fun i st _ _ hInv => hInv.2.2.2.2.2.1)
      (fun i st _ _ hInv => ev_reg hInv.2.2.2.1.1.2.2.2.2.2.2.2.2.1 (by omega))
      ?_
    intro i _ hi st ω ⟨hag, hst, hz, hf, h16, h17, h18, hrecs⟩
    have hrec_raw := rawComps_recordAt hv hst.1 hi
    set c := inp.rawComps[i]
    have hc_mem : c ∈ inp.rawComps := List.getElem_mem hi
    have hc_props := hv.2.2.2.2.2.2.2.2.2.2.2.1 c hc_mem
    have h_sum_le : ((inp.rawComps.take i).map fun p => 2 + p.2.length).sum + (2 + c.2.length) ≤
        (inp.rawComps.map fun p => 2 + p.2.length).sum := by
      have htake := congrArg (List.map fun p : ℕ × List ℕ => 2 + p.2.length) (List.take_append_drop i inp.rawComps)
      have hsum := congrArg List.sum htake
      rw [List.drop_eq_getElem_cons hi, List.map_append, List.map_cons,
        List.sum_append, List.sum_cons] at hsum
      change ((inp.rawComps.take i).map fun p => 2 + p.2.length).sum + (2 + inp.rawComps[i].2.length) ≤ _
      rw [← hsum]
      omega
    have hc_end_h : inp.cVertsPtr i + c.2.length ≤ inp.h := by
      have hdl := decompose_encode_length inp.d_ℓ inp.phiNum_dec inp.phiDen_dec inp.level inp.rawComps
      have hllen := hv.2.2.2.2.2.2.2.1
      have hdecle := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      simp only [PrepInput.cVertsPtr]
      omega
    have hptr : inp.cVertsPtr i - 2 + 2 = inp.cVertsPtr i := by
      simp only [PrepInput.cVertsPtr]; omega
    have hr18_lt : inp.cVertsPtr i - 2 < 2 ^ w := by omega
    have hr18_1_lt : inp.cVertsPtr i - 1 < 2 ^ w := by omega
    have hvp_lt : inp.cVertsPtr i < 2 ^ w := by omega
    have hc1_lt : c.1 < 2 ^ w := by omega
    have hc2_lt : c.2.length < 2 ^ w := by
      have hle_sum : 2 + c.2.length ≤ (inp.rawComps.map fun p => 2 + p.2.length).sum :=
        List.le_sum_of_mem (List.mem_map_of_mem hc_mem)
      omega
    have ha7_lt : inp.aComps + 7 * i < 2 ^ w := by
      simp only [PrepInput.aComps, PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead]
      omega
    have ha71_lt : inp.aComps + 7 * i + 1 < 2 ^ w := by
      simp only [PrepInput.aComps, PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega
    have ha72_lt : inp.aComps + 7 * i + 2 < 2 ^ w := by
      simp only [PrepInput.aComps, PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega
    have h7i_lt : 7 * i < 2 ^ w := by omega
    have hnext_eq : inp.cVertsPtr (i + 1) - 2 = inp.cVertsPtr i + c.2.length := by
      have htk : inp.rawComps.take (i + 1) = inp.rawComps.take i ++ [c] :=
        List.take_succ_eq_append_getElem hi
      simp only [PrepInput.cVertsPtr, htk, List.map_append, List.map_singleton, List.sum_append,
        List.sum_singleton]
      omega
    have hnext_lt : inp.cVertsPtr i + c.2.length < 2 ^ w := by omega
    have hr18_add2 : (inp.cVertsPtr i - 2) + 2 < 2 ^ w := by omega
    dsimp only [prepParseBody]
    refine runs_seq_assign0 (v := c.1) (ev_load (ev_reg h18 hr18_lt) hrec_raw.1 hc1_lt) ?_
    refine runs_seq_assign_le (v := c.2.length) ?_ ?_
    · exact ev_load (ev_add (ev_reg (by simp [h18]) hr18_lt) (ev_const hw1) (by omega))
        (by rw [show (inp.cVertsPtr i - 2) + 1 = inp.cVertsPtr i - 1 by omega]; exact hrec_raw.2.1) hc2_lt
    refine runs_seq_assign_le (v := inp.cVertsPtr i) ?_ ?_
    · rw [← hptr]
      exact ev_add (ev_reg (by simp [h18]) hr18_lt) (ev_const (c := 2) (by omega)) hr18_add2
    refine runs_seq_assign_le (v := inp.aComps + 7 * i) ?_ ?_
    · exact ev_add (ev_reg (by simp [hf.2.2.1]) (by simp [PrepInput.aComps, PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega))
        (ev_mul (ev_const (c := 7) (by omega)) (ev_reg (by simp [h17]) (by omega)) h7i_lt) ha7_lt
    refine runs_seq_store_le (x := inp.aComps + 7 * i) (v := c.1) ?_ ?_ ?_
    · exact ev_reg (by simp) ha7_lt
    · exact ev_reg (by simp) hc1_lt
    refine runs_seq_store_le (x := inp.aComps + 7 * i + 1) (v := c.2.length) ?_ ?_ ?_
    · exact ev_add (ev_reg (by simp) ha7_lt) (ev_const hw1) ha71_lt
    · exact ev_reg (by simp) hc2_lt
    refine runs_seq_store_le (x := inp.aComps + 7 * i + 2) (v := inp.cVertsPtr i) ?_ ?_ ?_
    · exact ev_add (ev_reg (by simp) ha7_lt) (ev_const (c := 2) (by omega)) ha72_lt
    · exact ev_reg (by simp) hvp_lt
    refine ⟨.normal, _, _, runs_assign_iff.mpr ⟨inp.cVertsPtr i + c.2.length,
        ev_add (ev_reg (by simp) hvp_lt) (ev_reg (by simp) hc2_lt) hnext_lt, rfl, rfl, rfl⟩,
      ?_, by norm_num [Expr.size]⟩
    dsimp only [normalPost, prepParseInv]
    set m0 := Function.update st.mem (inp.aComps + 7 * i) c.1
    set m1 := Function.update m0 (inp.aComps + 7 * i + 1) c.2.length
    set m2 := Function.update m1 (inp.aComps + 7 * i + 2) (inp.cVertsPtr i)
    have hag_step : AgreeOutside m2 st.mem (inp.aComps + 7 * i) (inp.aComps + 7 * (i + 1)) := by
      intro x hx
      rcases hx with hx1 | hx2 <;>
        simp [m2, m1, m0, Function.update_of_ne (by omega : x ≠ inp.aComps + 7 * i + 2),
          Function.update_of_ne (by omega : x ≠ inp.aComps + 7 * i + 1),
          Function.update_of_ne (by omega : x ≠ inp.aComps + 7 * i)]
    have hag_ext : AgreeOutside st.mem mem₀ inp.h (inp.aComps + 7 * (i + 1)) :=
      agreeOutside_mono hag le_rfl (by omega)
    have hag' : AgreeOutside m2 mem₀ inp.h (inp.aComps + 7 * (i + 1)) :=
      agreeOutside_trans hag_step hag_ext (by simp [PrepInput.aComps, PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega) le_rfl
    have hz' : ZeroFrom m2 (inp.aComps + 7 * (i + 1)) := fun x hx =>
      (hag_step x (Or.inr hx)).trans (hz x (by omega))
    refine ⟨⟨hag', prepStaticState_of_agree hst (fun x hx => hag_step x (Or.inl (by omega))),
      hz', ?_, ?_, ?_, ?_, ?_⟩, by simp [h17]⟩
    · exact prepFullRegs_congr hf fun r hr => by
        dsimp only
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    · simpa using h16
    · simp
    · simp [hnext_eq]
    · intro k hk
      by_cases hki : k = i
      · rw [hki]
        have hne01 : inp.aComps + 7 * i ≠ inp.aComps + 7 * i + 1 := by omega
        have hne02 : inp.aComps + 7 * i ≠ inp.aComps + 7 * i + 2 := by omega
        have hne12 : inp.aComps + 7 * i + 1 ≠ inp.aComps + 7 * i + 2 := by omega
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · dsimp only [m2, m1, m0]; rw [Function.update_of_ne hne02, Function.update_of_ne hne01, Function.update_self]
          simp only [c]; rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
        · dsimp only [m2, m1]; rw [Function.update_of_ne hne12, Function.update_self]
          simp only [c]; rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
        · dsimp only [m2]; rw [Function.update_self]
        · dsimp only [m2, m1, m0]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hz _ (by omega)
        · dsimp only [m2, m1, m0]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hz _ (by omega)
        · dsimp only [m2, m1, m0]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hz _ (by omega)
        · dsimp only [m2, m1, m0]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hz _ (by omega)
      · have hkp := hrecs k (by omega)
        have hlt_k : ∀ off < 7, inp.aComps + 7 * k + off < inp.aComps + 7 * i := fun _ _ => by omega
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [show inp.aComps + 7 * k = inp.aComps + 7 * k + 0 by omega,
            hag_step _ (Or.inl (hlt_k 0 (by omega)))]; exact hkp.1
        · rw [hag_step _ (Or.inl (hlt_k 1 (by omega)))]; exact hkp.2.1
        · rw [hag_step _ (Or.inl (hlt_k 2 (by omega)))]; exact hkp.2.2.1
        · rw [hag_step _ (Or.inl (hlt_k 3 (by omega)))]; exact hkp.2.2.2.1
        · rw [hag_step _ (Or.inl (hlt_k 4 (by omega)))]; exact hkp.2.2.2.2.1
        · rw [hag_step _ (Or.inl (hlt_k 5 (by omega)))]; exact hkp.2.2.2.2.2.1
        · rw [hag_step _ (Or.inl (hlt_k 6 (by omega)))]; exact hkp.2.2.2.2.2.2
  refine hmain.conseq ?_ (fun _ _ h => h) ?_
  · intro st ⟨hag, hst, hz, hf, h16, h17, h18⟩
    refine ⟨by simpa using hag, hst, by simpa using hz, hf, h16, h17, ?_, fun _ h0 => (Nat.not_lt_zero _ h0).elim⟩
    simp only [PrepInput.cVertsPtr, List.take_zero, List.map_nil, List.sum_nil, add_zero]
    omega
  · intro _ _; simp only [Expr.size]; omega

end MinCostFlow.Spanner
