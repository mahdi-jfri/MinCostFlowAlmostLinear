module

public import MinCostFlow.DynSpanner.Program.DynSpannerInitAtHelpers

/-!
# Verification of `dsInitAtStmt` (`DynSpannerInitAt`)

Proves `dsInitAt_state_agree` and `dsInitAt_meetsContract` for `initProcs` at `initIdxAt`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

public section

private lemma dsInitAt_state_agree {impl : SparsifyImpl} {mMax L q t vCap eCap b heapPtr ret : ℕ}
    {G : MGraph} {mem5 memFinal : ℕ → ℕ} {buck0 : List ℕ} {rev0 : ℕ → List ℕ}
    (hb1 : 1 ≤ b) (hfix : b + dsFixedSize L vCap eCap ≤ heapPtr)
    (hG_val : G.IsValid) (hGm_max : G.m ≤ mMax) (hG_v : ∀ v ∈ G.V, v < vCap) (hG_e : ∀ e ∈ G.E, e < eCap)
    (hmQ : memFinal (b + dsQOff) = q) (hmT : memFinal (b + dsTOff) = t)
    (hmL : memFinal (b + dsLOff) = L) (hmV : memFinal (b + dsVCapOff) = vCap)
    (hmE : memFinal (b + dsECapOff) = eCap) (hG_F : DynGraphAt memFinal (dsGPtr b) vCap eCap G)
    (hz5 : ZeroFrom mem5 (dsMinHBase b vCap eCap))
    (hcorePost :
      let core := initCore G (canonicalSparsify impl)
      let H₀ := core.1
      let Pi₀ := core.2.1
      memFinal (b + dsGenOff) = 1 + G.m ∧
      memFinal (dsDomGenBase b L vCap eCap) = 1 ∧
      (∀ v < vCap, memFinal (dsVStampBase b L vCap eCap + v) ≤ memFinal (b + dsGenOff)) ∧
      (∀ e < eCap, memFinal (dsEdgeDomGenBase b L vCap eCap + e) ≤ memFinal (b + dsGenOff)) ∧
      DynGraphAt memFinal (dsHPtr b vCap eCap) vCap eCap H₀ ∧
      DynGraphAt memFinal (dsAuxPtr b vCap eCap) vCap eCap emptyMGraph ∧
      (∀ e < eCap, (memFinal (dsMinHBase b vCap eCap + e) = 0 ↔ e ∉ H₀.E) ∧
        (e ∈ H₀.E → memFinal (dsMinHBase b vCap eCap + e) = 1)) ∧
      IsDoublyLinkedList memFinal (dsHPrevBase b vCap eCap) (dsHNextBase b vCap eCap)
        (dsHHeadBase b vCap eCap) eCap buck0 ∧
      memFinal (dsHDegDummyBase b L vCap eCap) = buck0.length ∧ (∀ e, e ∈ buck0 ↔ e ∈ H₀.E) ∧
      (∀ e < eCap, (0 < memFinal (dsDomGenBase b L vCap eCap) ∧
        memFinal (dsEdgeDomGenBase b L vCap eCap + e) = memFinal (dsDomGenBase b L vCap eCap)) ↔ e ∈ G.E) ∧
      (∀ e ∈ G.E, let ptr := memFinal (dsPiPtrBase b L vCap eCap + e)
        MWalkAt memFinal ptr (Pi₀ e) ∧ heapPtr ≤ ptr ∧ ptr + (mWalkEncode (Pi₀ e)).length ≤ ret) ∧
      (∀ v < vCap, memFinal (dsRevGenBase b L vCap eCap + v) ≤ memFinal (b + dsGenOff) ∧
        (rev0 v).Nodup ∧ (∀ e, e ∈ rev0 v ↔ e ∈ G.E ∧ v ∈ H₀.walkVertices (G.tail e) (Pi₀ e)) ∧
        (if 0 < memFinal (dsDomGenBase b L vCap eCap) ∧
            memFinal (dsRevGenBase b L vCap eCap + v) = memFinal (dsDomGenBase b L vCap eCap)
         then LinkedListIn (fun a => heapPtr ≤ a ∧ a < ret) memFinal
                (memFinal (dsRevHeadBase b L vCap eCap + v)) (rev0 v)
         else rev0 v = [])) ∧
      ∀ addr, dsInitCoreFrameCond L vCap eCap b heapPtr ret addr → memFinal addr = mem5 addr) :
    let stInit := (initAt G L q t (canonicalSparsify impl)).state
    ∃ x : DynSpannerMeta L,
      x.vCap = vCap ∧ x.eCap = eCap ∧ x.intervals = [(heapPtr, ret)] ∧
      (∀ i : Fin (L + 1), x.sLists i = []) ∧ x.memInDom ⟨0, Nat.zero_lt_succ L⟩ = G.E ∧
      (∀ i : Fin (L + 1), 0 < i.1 → x.memInDom i = ∅ ∧ ∀ v < vCap, x.revLists i v = []) ∧
      (∀ v < vCap, ∀ e : ℕ, e ∈ x.revLists ⟨0, Nat.zero_lt_succ L⟩ v ↔
        e ∈ G.E ∧ v ∈ stInit.H.walkVertices (G.tail e) (stInit.Pi_level ⟨0, Nat.zero_lt_succ L⟩ e)) ∧
      DynSpannerStateAt L vCap eCap b memFinal x stInit := by
  dsimp only
  rcases hcorePost with ⟨hgenF, hdomF, hvstF, hedLeF, hH_F, hAux_F, hminF, hdllF, hdegF,
    hbuckF, hedF, hpiF, hrevF, hfrC⟩
  obtain ⟨hpos0, hpos_ge, hSb, hSe⟩ := dsInitAt_memFinal_zero hfix hz5 hfrC
  have hProps := initAt_state_props (L := L) (q := q) (t := t)
    (canonicalSparsify_spec_absorb impl mMax) hG_val hGm_max le_rfl
  rcases hProps with ⟨hst_q, hst_t, _, hH_val, hHV, _, hSub, _, _, _, _, _, _⟩
  let x : DynSpannerMeta L :=
    { vCap := vCap, eCap := eCap, intervals := [(heapPtr, ret)],
      hBuckets := fun i => if i.1 = 0 then buck0 else [],
      memInDom := fun i => if i.1 = 0 then G.E else ∅,
      revLists := fun i v => if i.1 = 0 then rev0 v else [],
      sLists := fun _ => [] }
  refine ⟨x, rfl, rfl, rfl, fun _ => rfl, rfl, fun i hi => by simp [x, Nat.ne_of_gt hi], ?_, ?_⟩
  · intro v hv e; simpa [x, initAt] using (hrevF v hv).2.2.1 e
  · refine ⟨rfl, rfl, fun iv hiv => by simp only [x, List.mem_cons, List.not_mem_nil, or_false] at hiv; subst hiv; exact hfix,
      hb1, hG_val, hH_val, by simpa [initAt] using hHV, hSub.2.1, hSub.2.2, hG_v, hG_e,
      hmQ.trans hst_q.symm, hmT.trans hst_t.symm, hmL, hmV, hmE, by omega, by simpa [initAt] using hG_F,
      hH_F, hAux_F, ?_, ?_, ?_, ?_, fun v hv => ⟨hSb v hv, hvstF v hv⟩,
      fun e he => ⟨by rw [(hSe e he).1]; exact Nat.zero_le _, by rw [(hSe e he).2]; exact Nat.zero_le _⟩⟩
    · intro e he
      refine ⟨(hminF e he).1, fun heH => ?_⟩
      refine ⟨⟨0, Nat.zero_lt_succ L⟩, (hminF e he).2 heH, ?_, fun k hk => by simp at hk⟩
      simpa [initAt] using heH
    · intro i
      by_cases hi0 : i.1 = 0
      · simp only [x, hi0, Nat.add_zero, ↓reduceIte]
        exact ⟨hdllF, hdegF, fun e => ⟨fun hb => ⟨(hbuckF e).mp hb,
          (hminF e (hG_e e (hSub.2.1 ((hbuckF e).mp hb)))).2 ((hbuckF e).mp hb)⟩,
          fun ⟨heH, _⟩ => (hbuckF e).mpr heH⟩⟩
      · have hi_pos : 0 < i.1 := Nat.pos_of_ne_zero hi0
        obtain ⟨h1, h2, _⟩ := hpos0 i hi_pos
        simp only [x, hi0, ↓reduceIte]
        refine ⟨IsDoublyLinkedList.nil h1, h2, fun e => ⟨by simp, fun ⟨heH, hm_eq⟩ => ?_⟩⟩
        have := (hminF e (hG_e e (hSub.2.1 heH))).2 heH
        omega
    · intro i
      by_cases hi0 : i.1 = 0
      · have hDom : (initAt G L q t (canonicalSparsify impl)).state.inDom i = G.E := by
          simp only [initAt, hi0, ↓reduceIte]
        have hPi : (initAt G L q t (canonicalSparsify impl)).state.Pi_level i =
            (initCore G (canonicalSparsify impl)).2.1 := by
          simp only [initAt, hi0, ↓reduceIte]
        simp only [x, hi0, Nat.zero_mul, Nat.add_zero, ↓reduceIte]
        refine ⟨by omega, fun e he => ⟨hedLeF e he, hedF e he⟩, hG_e, ?_, fun e he => ?_, fun v hv => ?_⟩
        · rw [hDom]; exact (Finset.inter_self G.E).symm
        · rw [hDom] at he
          rw [hPi]
          obtain ⟨hmw, hlo, hhi⟩ := hpiF e he
          exact ⟨hmw, rangeInHeapFoot_of_interval List.mem_cons_self hlo hhi⟩
        · rcases hrevF v hv with ⟨hrg, hnd, hmem, hll⟩
          refine ⟨hrg, hnd, fun e he_m => ⟨hG_e e (hmem e |>.mp he_m).1, (hmem e |>.mp he_m).1⟩, ?_⟩
          split_ifs at hll ⊢
          · exact hll.mono fun a ha => ⟨(heapPtr, ret), List.mem_cons_self, ha.1, ha.2⟩
          · exact hll
      · have hi_pos : 0 < i.1 := Nat.pos_of_ne_zero hi0
        obtain ⟨_, _, hdm, hed_z, hrg_z⟩ := hpos0 i hi_pos
        have hDom : (initAt G L q t (canonicalSparsify impl)).state.inDom i = ∅ := by
          simp only [initAt, hi0, ↓reduceIte]
        simp only [x, hi0, ↓reduceIte]
        refine ⟨by omega, fun e he => ⟨by rw [hed_z e he]; omega, by simp [hdm]⟩, (fun _ h => by cases h),
          (by rw [hDom]; simp), (fun _ h => by rw [hDom] at h; cases h),
          fun v hv => ⟨by rw [hrg_z v hv]; omega, List.nodup_nil, by simp, by simp [hdm]⟩⟩
    · intro i
      obtain ⟨hsg, hvsg, _hsh⟩ := hpos_ge i
      have hSL : (initAt G L q t (canonicalSparsify impl)).state.S_level i = ∅ := by
        simp only [initAt]
      simp only [x]
      refine ⟨by omega, (fun _ h => by rw [hSL] at h; cases h),
        fun v hv => ⟨by rw [hvsg v hv]; omega, by rw [hSL]; simp [hsg]⟩,
        List.nodup_nil, (fun v => by rw [hSL]; simp), by simp [hsg]⟩

theorem dsInitAt_meetsContract {impl : SparsifyImpl} {mMax w L q t vCap eCap b : ℕ}
    {G : MGraph} {vL : List ℕ} {eEdges : List (ℕ × ℕ × ℕ)}
    {p : Program} {bOps bEdge bBatch bPhase bLW bSpDyn bInit : ℕ}
    {bSort bSplit bFwd bRevPrim bGT bRevCore bRevDyn bEmit bGuest bRev : ℕ}
    (hpInit : p.HasAt bInit (initProcs bOps bEdge bBatch bPhase bLW bSpDyn bInit))
    (hpOps : p.HasAt bOps dgOpsProcs) (hpBatch : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hpPhase : p.HasAt bPhase (phaseProcs bOps bEdge))
    (hpLW : p.HasAt bLW (levelWalkProcs bOps bRev)) (hpRev : p.HasAt bRev (revProcs bOps bRev))
    (hpSpDyn : p.HasAt bSpDyn (sparsifyDynProcs impl.program.regBound impl.cw bFwd bRevDyn bGuest))
    (hpGuest : p.HasAt bGuest (sparsifyGuestProcs impl bGuest))
    (hpFwd : p.HasAt bFwd (gtForwardProcs bOps bGT bEmit bFwd))
    (hpEmit : p.HasAt bEmit (gtEmitProcs bSort bOps bGT))
    (hpRevDyn : p.HasAt bRevDyn (gtRevDynProcs bOps bGT bRevCore))
    (hpRevCore : p.HasAt bRevCore (gtRevCoreProcs bBatch bRevPrim))
    (hpRevPrim : p.HasAt bRevPrim gtRevPrimProcs)
    (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpGT : p.HasAt bGT (gtProcs bSort bOps)) (hpSort : p.HasAt bSort (sortProcs bSort)) :
    MeetsContract w p (bInit + initIdxAt)
      (dsInitAtContract impl mMax w L q t vCap eCap b G vL eEdges) := by
  refine meetsContract_of_runs
    (hpInit.get (i := initIdxAt) (by simp [initProcs, initIdxAt]))
    fun args mem0 pos ω hargs hpre => ?_
  rcases hpre with ⟨V_ptr, E_ptr, heapPtr, rfl, hw16, hb1, hq1, ht_w, hfix, hspace, hzb,
    h1m_w, hw'_le, hG_val, hGm_max, hG_v, hG_e, hVl_len, hVl_at, hVl_mem, hVp_lt, hEl_len,
    hEl_nd, hEl_at, hEl_inG, hG_inEl, hEp_lt⟩
  have hheap_w : heapPtr < 2 ^ w := by omega
  have hL_w : L < 2 ^ w := hargs L (by simp)
  have hq_w : q < 2 ^ w := hargs q (by simp)
  have hv_w : vCap < 2 ^ w := hargs vCap (by simp)
  have he_w : eCap < 2 ^ w := hargs eCap (by simp)
  have hVl_w : vL.length < 2 ^ w := hargs vL.length (by simp)
  have hVp_w : V_ptr < 2 ^ w := hargs V_ptr (by simp)
  have hEl_w : eEdges.length < 2 ^ w := hargs eEdges.length (by simp)
  have hEp_w : E_ptr < 2 ^ w := hargs E_ptr (by simp)
  have hb_w : b < 2 ^ w := hargs b (by simp)
  have ⟨_, _, hmh_eq, hmh_w, _, _, _, _, _, _, _, haux_le⟩ := dsAddrs_bound hfix hheap_w
  have hb6 : b + dsHdrSize < 2 ^ w := by omega
  have haux_w : dsAuxPtr b vCap eCap < 2 ^ w := by omega
  simp only [initProcs, initIdxAt, List.getElem_cons_succ, List.getElem_cons_zero]
  dsimp only [dsInitAtStmt]
  refine runs_start_le ?_
  refine dsInitAt_stores_cont hw16 hzb hb6 hq_w ht_w hL_w hv_w he_w rfl
    (by simp [startState]) (by simp [startState]) (by simp [startState])
    (by simp [startState]) (by simp [startState]) (by simp [startState]) ?_
  rintro st1 ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr_ge6, hmQ, hmT, hmL, hmV, hmE, hmG, hz1, hfr1⟩
  have hr6 : st1.regs 6 = vL.length := (hr_ge6 6 (by decide)).trans (by simp [startState])
  have hr7 : st1.regs 7 = V_ptr := (hr_ge6 7 (by decide)).trans (by simp [startState])
  have hr8 : st1.regs 8 = eEdges.length := (hr_ge6 8 (by decide)).trans (by simp [startState])
  have hr9 : st1.regs 9 = E_ptr := (hr_ge6 9 (by decide)).trans (by simp [startState])
  have hr10 : st1.regs 10 = heapPtr := (hr_ge6 10 (by decide)).trans (by simp [startState])
  refine dsInitAt_assigns_cont hw16 haux_w hr0 hr4 hr5 ?_
  rintro st2 ⟨hm2, hr_le10, hr11, hr12, hr13, hr14⟩
  rw [← hm2] at hmQ hmT hmL hmV hmE hmG hz1 hfr1
  have hr0' : st2.regs 0 = b := (hr_le10 0 (by decide)).trans hr0
  have hr4' : st2.regs 4 = vCap := (hr_le10 4 (by decide)).trans hr4
  have hr5' : st2.regs 5 = eCap := (hr_le10 5 (by decide)).trans hr5
  have hr6' : st2.regs 6 = vL.length := (hr_le10 6 (by decide)).trans hr6
  have hr7' : st2.regs 7 = V_ptr := (hr_le10 7 (by decide)).trans hr7
  have hr8' : st2.regs 8 = eEdges.length := (hr_le10 8 (by decide)).trans hr8
  have hr9' : st2.regs 9 = E_ptr := (hr_le10 9 (by decide)).trans hr9
  have hr10' : st2.regs 10 = heapPtr := (hr_le10 10 (by decide)).trans hr10
  have hgp_b : b + dsHdrSize = dsGPtr b := rfl
  have hpre_initG : (dgInitFromListsContract w vCap eCap G vL eEdges).pre
      [dsGPtr b, vCap, eCap, vL.length, V_ptr, eEdges.length, E_ptr] st2.mem :=
    ⟨dsGPtr b, vL.length, V_ptr, eEdges.length, E_ptr, rfl, hw16, by omega, hz1, hG_val, hG_v,
      hG_e, rfl, fun i hi => by rw [hfr1 _ (by have := hVp_lt i hi; omega)]; exact hVl_at i hi,
      hVl_mem, fun i hi => by have := hVp_lt i hi; omega, rfl, hEl_nd,
      fun i hi => by
        rw [hfr1 _ (by have := hEp_lt (3 * i) (by omega); omega),
          hfr1 _ (by have := hEp_lt (3 * i + 1) (by omega); omega),
          hfr1 _ (by have := hEp_lt (3 * i + 2) (by omega); omega)]
        exact hEl_at i hi,
      hEl_inG, hG_inEl, fun i hi => by have := hEp_lt i hi; omega⟩
  refine runs_seq_call_le (dgInitFromLists_meetsContract hpBatch hpEdge hpOps)
    (by simp [evalArgs, Expr.eval, hr12, hr4', hr5', hr6', hr7', hr8', hr9'])
    (fun z hz => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
                    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    hpre_initG ?_
  intro _ mem3 pos3 ⟨_, _, _, _, _, hEqG, _, hG3, hfr3, hz3⟩
  simp only [List.cons.injEq, and_true] at hEqG
  rcases hEqG with ⟨rfl, _, _, rfl, rfl, rfl, rfl⟩
  have hpre_initH : (dgInitEmptyContract w).pre [dsHPtr b vCap eCap, vCap, eCap] mem3 :=
    ⟨dsHPtr b vCap eCap, vCap, eCap, rfl, hw16, by omega, hz3⟩
  refine runs_seq_call_le (dgInitEmpty_meetsContract hpOps)
    (by simp [evalArgs, Expr.eval, hr13, hr4', hr5'])
    (fun z hz => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
                    rcases hz with rfl | rfl | rfl <;> omega)
    hpre_initH ?_
  intro _ mem4 pos4 ⟨_, _, _, hEqH, _, hH4_empty, hfr4, hz4⟩
  simp only [List.cons.injEq, and_true] at hEqH; rcases hEqH with ⟨rfl, rfl, rfl⟩
  have hdg4_le : 4 ≤ dynGraphSize vCap eCap := by simp [dynGraphSize]; omega
  have hz4_aux : ZeroFrom mem4 (dsAuxPtr b vCap eCap) := fun a ha => hz4 a (by
    have : dsHPtr b vCap eCap + dynGraphSize vCap eCap = dsAuxPtr b vCap eCap := rfl; omega)
  have hpre_initA : (dgInitEmptyContract w).pre [dsAuxPtr b vCap eCap, vCap, eCap] mem4 :=
    ⟨dsAuxPtr b vCap eCap, vCap, eCap, rfl, hw16, by omega, hz4_aux⟩
  refine runs_seq_call_le (dgInitEmpty_meetsContract hpOps)
    (by simp [evalArgs, Expr.eval, hr14, hr4', hr5'])
    (fun z hz => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
                    rcases hz with rfl | rfl | rfl <;> omega)
    hpre_initA ?_
  intro _ mem5 pos5 ⟨_, _, _, hEqA, _, hAux5_empty, hfr5, hz5⟩
  simp only [List.cons.injEq, and_true] at hEqA; rcases hEqA with ⟨rfl, rfl, rfl⟩
  have hgp_eq : dsGPtr b = b + dsHdrSize := rfl
  have hgh_eq : dsGPtr b + dynGraphSize vCap eCap = dsHPtr b vCap eCap := rfl
  have hha_eq : dsHPtr b vCap eCap + dynGraphSize vCap eCap = dsAuxPtr b vCap eCap := rfl
  have hgoff_eq : dsGenOff = 5 := rfl
  have hhdr_eq : dsHdrSize = 6 := rfl
  have hz5_min : ZeroFrom mem5 (dsMinHBase b vCap eCap) := fun a ha => hz5 a (by
    have : dsAuxPtr b vCap eCap + dynGraphSize vCap eCap = dsMinHBase b vCap eCap := rfl; omega)
  have hagree5_hdr : ∀ addr < dsGPtr b, mem5 addr = st2.mem addr := fun addr hlt =>
    (hfr5 addr (Or.inl (by omega))).trans ((hfr4 addr (Or.inl (by omega))).trans
      (hfr3 addr (Or.inl hlt)))
  have hG5 : DynGraphAt mem5 (dsGPtr b) vCap eCap G :=
    hG3.of_agree fun addr _ h2 => (hfr5 addr (Or.inl (by omega))).trans
      (hfr4 addr (Or.inl (by omega)))
  have hH5 : DynGraphAt mem5 (dsHPtr b vCap eCap) vCap eCap emptyMGraph :=
    hH4_empty.of_agree fun addr _ hhi => hfr5 addr (Or.inl (by omega))
  have hL5 : mem5 (b + dsLOff) = L := (hagree5_hdr _ (by simp [dsLOff, dsGPtr, dsHdrSize])).trans hmL
  have hvC5 : mem5 (b + dsVCapOff) = vCap := (hagree5_hdr _ (by simp [dsVCapOff, dsGPtr, dsHdrSize])).trans hmV
  have heC5 : mem5 (b + dsECapOff) = eCap := (hagree5_hdr _ (by simp [dsECapOff, dsGPtr, dsHdrSize])).trans hmE
  have hgen5 : mem5 (b + dsGenOff) = 0 := (hagree5_hdr _ (by simp [dsGenOff, dsGPtr, dsHdrSize])).trans hmG
  obtain ⟨hz5_hp, hmin5, hdll5, hdeg5, hdom5, hed5, hrevg5, hvst5⟩ :=
    dsInitAt_mem4_zero hfix hz5_min hgen5
  have hpre_core : (dsInitCoreContract impl mMax w L vCap eCap b G).pre [b, heapPtr] mem5 :=
    ⟨heapPtr, rfl, hw16, hb1, hfix, hspace, hz5_hp, hw'_le, hL5, hvC5, heC5,
      by rw [hgen5]; exact h1m_w, hmin5, hdll5, hdeg5, hdom5, hed5, hrevg5, hvst5,
      hG5, hH5, hAux5_empty, hG_val, hGm_max, hG_v, hG_e⟩
  refine runs_seq_call_le (dsInitCore_meetsContract hpInit hpOps hpPhase hpLW hpRev hpSpDyn
      hpGuest hpFwd hpEmit hpRevDyn hpRevCore hpRevPrim hpBatch hpEdge hpGT hpSort)
    (by simp [evalArgs, Expr.eval, hr0', hr10'])
    (fun z hz => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
                    rcases hz with rfl | rfl <;> omega)
    hpre_core ?_
  intro retFinal memFinal _ ⟨_, hEqCore, hrt_ge, hrt_le, hzF, hgenF, hdomF, hvstF, hedLeF, hH_F,
    hAux_F, hminF, ⟨buck0, hdllF, hdegF, hbuckF⟩, hedF, hpiF, ⟨rev0, hrevF⟩, hfrC⟩
  simp only [List.cons.injEq, and_true] at hEqCore; rcases hEqCore with ⟨_, rfl⟩
  dsimp only at hgenF hdomF hvstF hedLeF hminF hedF hrevF hfrC
  have hagree_hdr_F : ∀ addr < dsGPtr b, addr ≠ b + dsGenOff → memFinal addr = st2.mem addr :=
    fun addr hlt hne => (hfrC addr (dsInitCoreFrameCond_lt_H hfix (by omega) hne)).trans
      (hagree5_hdr addr hlt)
  have hmQ_F : memFinal (b + dsQOff) = q :=
    (hagree_hdr_F _ (by simp [dsQOff, dsGPtr, dsHdrSize]) (by simp [dsQOff, dsGenOff])).trans hmQ
  have hmT_F : memFinal (b + dsTOff) = t :=
    (hagree_hdr_F _ (by simp [dsTOff, dsGPtr, dsHdrSize]) (by simp [dsTOff, dsGenOff])).trans hmT
  have hmL_F : memFinal (b + dsLOff) = L :=
    (hagree_hdr_F _ (by simp [dsLOff, dsGPtr, dsHdrSize]) (by simp [dsLOff, dsGenOff])).trans hmL
  have hmV_F : memFinal (b + dsVCapOff) = vCap :=
    (hagree_hdr_F _ (by simp [dsVCapOff, dsGPtr, dsHdrSize]) (by simp [dsVCapOff, dsGenOff])).trans hmV
  have hmE_F : memFinal (b + dsECapOff) = eCap :=
    (hagree_hdr_F _ (by simp [dsECapOff, dsGPtr, dsHdrSize]) (by simp [dsECapOff, dsGenOff])).trans hmE
  have hG_F : DynGraphAt memFinal (dsGPtr b) vCap eCap G :=
    hG5.of_agree fun addr hlo hhi => hfrC addr (dsInitCoreFrameCond_lt_H hfix (by omega) (by omega))
  refine runs_ret_le (by simp [Expr.eval])
    ⟨V_ptr, E_ptr, heapPtr, rfl, hrt_ge, hrt_le, hzF, ?_, ?_, by show memFinal _ = _; rw [hgenF, hgen5, Nat.zero_add]⟩ ?_
  · rw [hgen5, Nat.zero_add] at hgenF hdomF
    exact dsInitAt_state_agree hb1 hfix hG_val hGm_max hG_v hG_e hmQ_F hmT_F hmL_F hmV_F hmE_F hG_F
      hz5_min ⟨hgenF, hdomF, hvstF, hedLeF, hH_F, hAux_F, hminF, hdllF, hdegF, hbuckF, hedF, hpiF,
        hrevF, hfrC⟩
  · intro addr hlt
    exact (hagree_hdr_F addr (by omega) (by omega)).trans (hfr1 addr hlt)
  · dsimp only [dsInitAtContract, dgInitFromListsContract, dgInitEmptyContract, dsInitCoreContract,
      List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, argsSize, Expr.size]
    omega

end

end MinCostFlow.DynSpanner.Program
