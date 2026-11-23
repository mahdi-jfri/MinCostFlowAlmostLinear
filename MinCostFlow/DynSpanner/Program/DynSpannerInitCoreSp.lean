module

public import MinCostFlow.DynSpanner.Program.DynSpannerInitCorePrep
public import MinCostFlow.DynSpanner.Program.DynSpannerLevelWalks
public import MinCostFlow.DynSpanner.Program.SparsifyHost

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sparsification half of `dsInitCoreStmt` nonempty branch (`DynSpannerInitCoreSp`)

Proves fixed-layout ordering helpers and `dsInitCore_spPhase_cont`, running
`buildActiveOnAux`, `dsWriteIdEmb`, `sparsifyDyn`, and parameter unpacking up to `Jtilde` insertion.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

public section

lemma collectRawEsFun_idEmb_len (E : Finset ℕ) :
    (collectRawEsFun (MinCostFlow.Spanner.vertsOf E) idEmb).length = E.card := by
  have h1 : ∀ e, ((idEmb e).map Prod.fst).length = 1 := fun e => by simp [idEmb]
  rw [collectRawEsFun, List.length_flatMap]
  have hmap : (MinCostFlow.Spanner.vertsOf E).map (fun e => ((idEmb e).map Prod.fst).length) =
      (MinCostFlow.Spanner.vertsOf E).map (fun _ => 1) :=
    List.map_congr_left fun e _ => h1 e
  rw [hmap, List.map_const', List.sum_replicate, smul_eq_mul, mul_one,
    MinCostFlow.Spanner.vertsOf_length]

lemma sum_eL_eq_finset {eL : List ℕ} {E : Finset ℕ}
    (hNd : eL.Nodup) (hMem : ∀ e, e ∈ eL ↔ e ∈ E) (f : ℕ → ℕ) :
    (eL.map f).sum = ∑ e ∈ E, f e := by
  have h1 := List.sum_toFinset f hNd
  have hts : eL.toFinset = E := by ext e; simp [hMem e]
  simpa [hts] using h1.symm

lemma dsInitCore_fixed_order (b L vCap eCap : ℕ) :
    b + dsGenOff < dsGPtr b ∧
    b + dsLOff < dsGPtr b ∧
    b + dsVCapOff < dsGPtr b ∧
    b + dsECapOff < dsGPtr b ∧
    dsGPtr b + dynGraphSize vCap eCap = dsHPtr b vCap eCap ∧
    dsHPtr b vCap eCap + dynGraphSize vCap eCap = dsAuxPtr b vCap eCap ∧
    dsAuxPtr b vCap eCap + dynGraphSize vCap eCap = dsMinHBase b vCap eCap ∧
    dsMinHBase b vCap eCap + eCap = dsHNextBase b vCap eCap ∧
    dsHNextBase b vCap eCap + eCap = dsHPrevBase b vCap eCap ∧
    dsHPrevBase b vCap eCap + eCap = dsHHeadBase b vCap eCap ∧
    dsHHeadBase b vCap eCap + (L + 1) = dsHDegDummyBase b L vCap eCap ∧
    dsHDegDummyBase b L vCap eCap + (L + 1) = dsDomGenBase b L vCap eCap ∧
    dsDomGenBase b L vCap eCap + (L + 1) = dsEdgeDomGenBase b L vCap eCap ∧
    dsEdgeDomGenBase b L vCap eCap + (L + 1) * eCap = dsPiPtrBase b L vCap eCap ∧
    dsPiPtrBase b L vCap eCap + (L + 1) * eCap = dsRevGenBase b L vCap eCap ∧
    dsRevGenBase b L vCap eCap + (L + 1) * vCap = dsRevHeadBase b L vCap eCap ∧
    dsRevHeadBase b L vCap eCap + (L + 1) * vCap = dsSGenBase b L vCap eCap ∧
    dsSGenBase b L vCap eCap + (L + 1) + (L + 1) * vCap + (L + 1) + vCap =
      dsVStampBase b L vCap eCap ∧
    dsVStampBase b L vCap eCap + vCap + 2 * eCap = dsMEmbTempBase b L vCap eCap ∧
    dsMEmbTempBase b L vCap eCap + eCap = b + dsFixedSize L vCap eCap := by
  have hf := dsFixedSize_add b L vCap eCap
  have hm := dsMEmbTempBase_eq b L vCap eCap
  have h5 := dsVStampBase_eq b L vCap eCap
  have h4 := dsRevHeadBase_eq b L vCap eCap
  have h3 := dsRevGenBase_eq b L vCap eCap
  have h2 := dsDomGenBase_eq b L vCap eCap
  have h1 := dsMinHBase_eq b vCap eCap
  refine ⟨by simp [dsGenOff, dsGPtr, dsHdrSize], by simp [dsLOff, dsGPtr, dsHdrSize],
    by simp [dsVCapOff, dsGPtr, dsHdrSize], by simp [dsECapOff, dsGPtr, dsHdrSize],
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    ?_, ?_, hf⟩
  · simp only [dsVStampBase, dsSBitBase, dsSHeadBase, dsVSGenBase]
  · simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase]; omega

private lemma spPhase_space_parts (impl : SparsifyImpl) (mMax vCap eCap heapPtr : ℕ) (G : MGraph) :
    let Gact := activeSubgraph G
    let w' := wordSize impl.cw (canonSparsifyInput Gact Gact idEmb)
    3 * G.m ≤ dsInitCoreSpaceBound impl mMax vCap eCap G ∧
    3 * G.m + (8 + 3 * Gact.n + 11 * G.m) ≤ dsInitCoreSpaceBound impl mMax vCap eCap G ∧
    (∀ ret, ret ≤ (heapPtr + 3 * G.m + (8 + 3 * Gact.n + 11 * G.m)) +
        2 ^ (w' + 1) + 2 + 3 * G.m + dynGraphSize vCap eCap + eCap +
        G.m * (1 + 2 * Nat.ceil (impl.γ_ℓ mMax)) →
      ret + 9 * G.m * (Nat.ceil (impl.γ_ℓ mMax) + 1) ≤
        heapPtr + dsInitCoreSpaceBound impl mMax vCap eCap G) := by
  dsimp only [dsInitCoreSpaceBound]
  refine ⟨?_, ?_, fun ret hret => ?_⟩
  · exact le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ _)
      (le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ _)
        (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)))))))
  · exact le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ _)
      (le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ _)
        (Nat.le_add_right _ _))))))
  · refine le_trans (Nat.add_le_add_right hret _) ?_
    simp only [Nat.add_assoc, le_refl]

private lemma spPhase_cont_step {w : ℕ} {p : Program} {ω : ℕ → Bool} {s : Stmt}
    {st : State} {k k' T : ℕ} {P : State → Prop} {Q : Outcome → State → Prop}
    (hrest : ∀ st₁, P st₁ → ∃ o st' c, Runs w p ω s st₁ o st' c ∧ Q o st' ∧ k' + c ≤ T)
    (hP : P st) (hk : k ≤ k') :
    ∃ o st' c, Runs w p ω s st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases hrest st hP with ⟨o, st', c, hr, hq, hc⟩
  exact ⟨o, st', c, hr, hq, Nat.le_trans (Nat.add_le_add_right hk c) hc⟩

lemma dsInitCore_spPhase_cont {impl : SparsifyImpl} {mMax w L vCap eCap b heapPtr : ℕ}
    {G : MGraph} {mem0 mem1 : ℕ → ℕ}
    {p : Program} {bOps bEdge bPhase bLW bSpDyn : ℕ}
    {bSort bSplit bBatch bFwd bRevPrim bGT bRevCore bRevDyn bEmit bGuest bRev : ℕ}
    (hpOps : p.HasAt bOps dgOpsProcs)
    (hpPhase : p.HasAt bPhase (phaseProcs bOps bEdge))
    (hpLW : p.HasAt bLW (levelWalkProcs bOps bRev))
    (hpSpDyn : p.HasAt bSpDyn (sparsifyDynProcs impl.program.regBound impl.cw bFwd bRevDyn bGuest))
    (hpGuest : p.HasAt bGuest (sparsifyGuestProcs impl bGuest))
    (hpFwd : p.HasAt bFwd (gtForwardProcs bOps bGT bEmit bFwd))
    (hpEmit : p.HasAt bEmit (gtEmitProcs bSort bOps bGT))
    (hpRevDyn : p.HasAt bRevDyn (gtRevDynProcs bOps bGT bRevCore))
    (hpRevCore : p.HasAt bRevCore (gtRevCoreProcs bBatch bRevPrim))
    (hpRevPrim : p.HasAt bRevPrim gtRevPrimProcs)
    (hpBatch : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpGT : p.HasAt bGT (gtProcs bSort bOps))
    (hpSort : p.HasAt bSort (sortProcs bSort))
    (hw16 : 16 ≤ 2 ^ w)
    (hfix : b + dsFixedSize L vCap eCap ≤ heapPtr)
    (hspace : heapPtr + dsInitCoreSpaceBound impl mMax vCap eCap G < 2 ^ w)
    (hz0 : ZeroFrom mem0 heapPtr)
    (hGm_ne : G.m ≠ 0)
    (hw'_le : wordSize impl.cw (canonSparsifyInput (activeSubgraph G) (activeSubgraph G) idEmb) ≤ w)
    (hGm_max : G.m ≤ mMax)
    (hG_v : ∀ v ∈ G.V, v < vCap) (hG_e : ∀ e ∈ G.E, e < eCap) (hG_val : G.IsValid)
    (hG1 : DynGraphAt mem1 (dsGPtr b) vCap eCap G)
    (hAux1 : DynGraphAt mem1 (dsAuxPtr b vCap eCap) vCap eCap emptyMGraph)
    (hfr1 : ∀ addr, addr < dsHPtr b vCap eCap ∨
        dsHPtr b vCap eCap + dynGraphSize vCap eCap ≤ addr →
      mem1 addr = mem0 addr)
    {s : Stmt} {st : State} {ω : ℕ → Bool} {k T : ℕ} {Q : Outcome → State → Prop}
    (hst : st.mem = mem1 ∧
      st.regs 0 = b ∧ st.regs 1 = heapPtr ∧ st.regs 2 = vCap ∧ st.regs 3 = eCap ∧
      st.regs 4 = L ∧ st.regs 5 = dynGraphSize vCap eCap ∧ st.regs 6 = dsGPtr b ∧
      st.regs 7 = dsHPtr b vCap eCap ∧ st.regs 8 = dsAuxPtr b vCap eCap ∧
      st.regs 9 = dsMEmbTempBase b L vCap eCap ∧ st.regs 10 = G.n ∧ st.regs 11 = G.m)
    (hrest : ∀ st₁ : State,
      (∃ jtPtr mEmbOutPtr heapSp,
        let Gact := activeSubgraph G
        let out := canonicalSparsify impl Gact Gact idEmb
        st₁.regs 0 = b ∧ st₁.regs 1 = heapPtr + 3 * G.m ∧ st₁.regs 2 = vCap ∧ st₁.regs 3 = eCap ∧
        st₁.regs 4 = L ∧ st₁.regs 6 = dsGPtr b ∧ st₁.regs 7 = dsHPtr b vCap eCap ∧
        st₁.regs 8 = dsAuxPtr b vCap eCap ∧ st₁.regs 11 = G.m ∧ st₁.regs 15 = heapSp ∧
        st₁.regs 16 = jtPtr ∧ st₁.regs 17 = mEmbOutPtr ∧ st₁.regs 18 = out.Jtilde.m ∧
        st₁.regs 19 = dgEListBase jtPtr vCap eCap ∧
        heapPtr + 3 * G.m ≤ jtPtr ∧
        jtPtr + dynGraphSize vCap eCap ≤ mEmbOutPtr ∧
        mEmbOutPtr + eCap ≤ heapSp ∧
        heapSp + 9 * G.m * (Nat.ceil (impl.γ_ℓ mMax) + 1) ≤
          heapPtr + dsInitCoreSpaceBound impl mMax vCap eCap G ∧
        ZeroFrom st₁.mem heapSp ∧
        DynGraphAt st₁.mem (dsAuxPtr b vCap eCap) vCap eCap Gact ∧
        DynGraphAt st₁.mem jtPtr vCap eCap out.Jtilde ∧
        MEmbBounded st₁.mem mEmbOutPtr G.E eCap out.emb mEmbOutPtr heapSp ∧
        (∀ e ∈ G.E, mEmbOutPtr + eCap ≤ st₁.mem (mEmbOutPtr + e)) ∧
        ∀ addr, addr < heapPtr →
          (addr < dsAuxPtr b vCap eCap ∨ dsAuxPtr b vCap eCap + dynGraphSize vCap eCap ≤ addr) →
          (addr < dsMEmbTempBase b L vCap eCap ∨ dsMEmbTempBase b L vCap eCap + eCap ≤ addr) →
          st₁.mem addr = mem1 addr) →
      ∃ o st' c, Runs w p ω s st₁ o st' c ∧ Q o st' ∧
        (k + sparsifyDynCost impl mMax (activeSubgraph G) (activeSubgraph G) idEmb +
          960 * G.m + 180) + c ≤ T) :
    let _Gact := activeSubgraph G
    ∃ o st' c, Runs w p ω
      (.call 12 (bPhase + phaseIdxBuildActive) [.reg 6, .reg 8] ;;
       .call 1 (bLW + lwIdxWriteIdEmb) [.reg 8, .reg 9, .reg 1] ;;
       .assign 12 (.reg 1) ;;
       .assign 13 (.load (.bin .add (.reg 8) (.const dgNOff))) ;;
       .assign 14 (.bin .add (.reg 12)
         (.bin .add (.const 8)
           (.bin .add (.bin .mul (.const 3) (.reg 13)) (.bin .mul (.const 11) (.reg 11))))) ;;
       .call 15 (bSpDyn + gtIdxSparsifyDyn)
         [.reg 8, .reg 8, .reg 9, .reg 2, .reg 3, .reg 12, .reg 14] ;;
       .assign 16 (.load (.reg 12)) ;;
       .assign 17 (.load (.bin .add (.reg 12) (.const 1))) ;;
       .assign 18 (.load (.bin .add (.reg 16) (.const dgMOff))) ;;
       .assign 19 (.bin .add (.bin .add (.reg 16) (.const 4))
         (.bin .add (.bin .mul (.const 7) (.reg 2)) (.reg 3))) ;; s) st o st' c ∧
      Q o st' ∧ k + c ≤ T := by
  intro Gact
  set out := canonicalSparsify impl Gact Gact idEmb
  rcases hst with ⟨hm, hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11⟩
  subst hm
  have hheap_w : heapPtr < 2 ^ w := by omega
  have had := dsAddrs_bound (w := w) (L := L) (vCap := vCap) (eCap := eCap) hfix hheap_w
  rcases had with ⟨hdg_def, hdg_lt, _, hmin_lt, _, _, _, _, _, _, hh_aux, ha_min⟩
  obtain ⟨_, _, _, _, h_g_h, h_h_a, h_a_min, ho_mhn, ho_n_p, ho_p_h, ho_h_d, ho_d_dm, ho_dm_ed,
    ho_ed_pi, ho_pi_rg, ho_rg_rh, ho_rh_sg, ho_sg_vs, ho_vs_me, ho_me_fix⟩ :=
    dsInitCore_fixed_order b L vCap eCap
  have hg_ltw : dsGPtr b + dynGraphSize vCap eCap < 2 ^ w := by omega
  have ha_ltw : dsAuxPtr b vCap eCap + dynGraphSize vCap eCap < 2 ^ w := by omega
  have hm_ltw : dsMEmbTempBase b L vCap eCap + eCap < 2 ^ w := by omega
  have hga_disj : dsGPtr b + dynGraphSize vCap eCap ≤ dsAuxPtr b vCap eCap ∨
      dsAuxPtr b vCap eCap + dynGraphSize vCap eCap ≤ dsGPtr b := Or.inl (by omega)
  have hGact_E : Gact.E = G.E := rfl
  have hGact_m : Gact.m = G.m := rfl
  have hGact_val : Gact.IsValid := activeSubgraph_isValid hG_val
  have hE_ne : G.E.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hGm_ne)
  have hGact_n_pos : 1 ≤ Gact.n := by
    rcases hE_ne with ⟨e, he⟩
    exact Finset.card_pos.mpr ⟨_, (hGact_val e he).1⟩
  have hGact_v : ∀ v ∈ Gact.V, v < vCap := fun v hv =>
    hG_v v ((activeSubgraph_isSubgraph G).1 hv)
  have hpre_ba : (buildActiveOnAuxContract w vCap eCap G).pre [dsGPtr b, dsAuxPtr b vCap eCap] st.mem :=
    ⟨dsGPtr b, dsAuxPtr b vCap eCap, rfl, hw16, hg_ltw, ha_ltw, hga_disj, hG1, hAux1⟩
  refine runs_seq_call_le (buildActiveOnAux_meetsContract hpPhase hpEdge hpOps)
    (by simp [evalArgs, Expr.eval, hr6, hr8])
    (fun z hz => by simp at hz; rcases hz with rfl | rfl <;> omega)
    hpre_ba ?_
  intro retBA memBA posBA ⟨_, _, hEqBA, _, hAuxBA, hfrBA⟩
  simp only [List.cons.injEq, and_true] at hEqBA
  rcases hEqBA with ⟨rfl, rfl⟩
  have hAuxBA' : DynGraphAt memBA (dsAuxPtr b vCap eCap) vCap eCap Gact := hAuxBA
  have hzBA : ZeroFrom memBA heapPtr := fun addr ha =>
    (hfrBA addr (Or.inr (by omega))).trans ((hfr1 addr (Or.inr (by omega))).trans (hz0 addr ha))
  have hmE_disj_hp : dsMEmbTempBase b L vCap eCap + eCap ≤ heapPtr ∨
      heapPtr + 3 * G.m ≤ dsMEmbTempBase b L vCap eCap := by left; omega
  obtain ⟨hsp_3m, hsp_gb, hsp_ret⟩ := spPhase_space_parts impl mMax vCap eCap heapPtr G
  have hpre_wie : (dsWriteIdEmbContract w vCap eCap Gact).pre
      [dsAuxPtr b vCap eCap, dsMEmbTempBase b L vCap eCap, heapPtr] memBA := by
    refine ⟨dsAuxPtr b vCap eCap, dsMEmbTempBase b L vCap eCap, heapPtr,
      rfl, hw16, ha_ltw, hm_ltw, by rw [hGact_m]; omega,
      fun _ _ => ⟨by left; omega, by left; omega⟩, ?_, hAuxBA', hG_e⟩
    rw [hGact_m]; exact hmE_disj_hp
  refine runs_seq_call_le (dsWriteIdEmb_meetsContract hpLW)
    (by simp [evalArgs, Expr.eval, hr8, hr9, hr1])
    (fun z hz => by simp at hz; rcases hz with rfl | rfl | rfl <;> omega)
    hpre_wie ?_
  intro retIE memIE posIE ⟨_, _, _, hEqIE, hretIE_eq, hmEmbIE, hmEmbBnd_IE, hfrIE⟩
  simp only [List.cons.injEq, and_true] at hEqIE
  rcases hEqIE with ⟨rfl, rfl, rfl⟩
  rw [hGact_m] at hretIE_eq hmEmbBnd_IE
  subst hretIE_eq
  let scrPtr := heapPtr + 3 * G.m
  let gb := scrPtr + (8 + 3 * Gact.n + 11 * G.m)
  have hAuxIE : DynGraphAt memIE (dsAuxPtr b vCap eCap) vCap eCap Gact :=
    hAuxBA'.of_agree fun addr _ _ => hfrIE addr (Or.inl (by omega)) (Or.inl (by omega))
  have hAuxIE_n : memIE (dsAuxPtr b vCap eCap + dgNOff) = Gact.n := hAuxIE.2.2.2.2.2.1
  have hzIE : ZeroFrom memIE scrPtr := fun addr ha =>
    (hfrIE addr (Or.inr (by omega)) (Or.inr ha)).trans (hzBA addr (by omega))
  have h1_w : (1 : ℕ) < 2 ^ w := by omega
  have h2_w : (2 : ℕ) < 2 ^ w := by omega
  have h3_w : (3 : ℕ) < 2 ^ w := by omega
  have h4_w : (4 : ℕ) < 2 ^ w := by omega
  have h7_w : (7 : ℕ) < 2 ^ w := by omega
  have h8_w : (8 : ℕ) < 2 ^ w := by omega
  have h11_w : (11 : ℕ) < 2 ^ w := by omega
  have haN_lt : dsAuxPtr b vCap eCap + 2 < 2 ^ w := by
    simp only [dynGraphSize] at ha_ltw; omega
  have hGact_n_w : Gact.n < 2 ^ w := by
    have hact_n : Gact.n ≤ G.n := activeSubgraph_n_le G
    have hGn_le : G.n ≤ vCap :=
      (Finset.card_le_card (show G.V ⊆ Finset.range vCap from
        fun v hv => Finset.mem_range.mpr (hG_v v hv))).trans_eq (Finset.card_range vCap)
    have hvc_dg : vCap < dynGraphSize vCap eCap := by dsimp [dynGraphSize]; omega
    exact lt_of_le_of_lt (le_trans hact_n (le_trans hGn_le hvc_dg.le)) hdg_lt
  have hscr_w : scrPtr < 2 ^ w := by dsimp [scrPtr]; omega
  have hgb_w : gb < 2 ^ w := by
    have : Gact.n = (activeSubgraph G).n := rfl
    dsimp [gb, scrPtr]; omega
  have hraw_len : (collectRawEsFun (MinCostFlow.Spanner.vertsOf Gact.E) idEmb).length = G.m := by
    rw [collectRawEsFun_idEmb_len, hGact_E]; rfl
  have hsLen_le : max (gtFwdDynScratchLen Gact.n Gact.m Gact.m)
      (gtRevDynScratchLen Gact.n Gact.m) ≤ 8 + 3 * Gact.n + 11 * G.m := by
    simp only [gtFwdDynScratchLen, gtRevDynScratchLen, hGact_m]; omega
  refine runs_seq_assign_le (v := scrPtr) (by simp [Expr.eval, scrPtr]) ?_
  refine runs_seq_assign_le (v := Gact.n)
    (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, dgNOff, hr8, h2_w, haN_lt]) hAuxIE_n) ?_
  refine runs_seq_assign_le (v := gb)
    (by simp [gb, scrPtr, Expr.eval, BinOp.eval, hr11, h3_w, h8_w, h11_w,
      show 3 * Gact.n < 2 ^ w by omega, show 11 * G.m < 2 ^ w by omega,
      show 3 * Gact.n + 11 * G.m < 2 ^ w by omega,
      show 8 + (3 * Gact.n + 11 * G.m) < 2 ^ w by omega,
      show heapPtr + (3 * G.m + (8 + (3 * Gact.n + 11 * G.m))) < 2 ^ w by
        dsimp [gb, scrPtr] at hgb_w; omega, Nat.add_assoc]) ?_
  have hpre_sp : (sparsifyDynContract impl mMax w vCap eCap vCap eCap vCap eCap Gact Gact idEmb).pre
      [dsAuxPtr b vCap eCap, dsAuxPtr b vCap eCap, dsMEmbTempBase b L vCap eCap,
       vCap, eCap, scrPtr, gb] memIE := by
    refine ⟨dsAuxPtr b vCap eCap, dsAuxPtr b vCap eCap, dsMEmbTempBase b L vCap eCap,
      scrPtr, gb, rfl, hw16, hGact_n_pos, ?_, ?_, by dsimp [gb, scrPtr]; omega, hw'_le, ?_,
      by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_,
      fun addr ha => hzIE addr (by dsimp [gb] at ha ⊢; omega),
      hAuxIE, hAuxIE, idEmb_isEmbedding Gact, hmEmbIE, hGm_max,
      fun h => by rw [idEmb_length_eq_one h],
      hGact_v, fun e he => hG_e e (hGact_E ▸ he), fun e he => ?_⟩
    · dsimp only [dynGraphSize] at hdg_lt; omega
    · dsimp only [dynGraphSize] at hdg_lt; omega
    · have : gb + 2 ^ (wordSize impl.cw (canonSparsifyInput Gact Gact idEmb) + 1) + 2 +
          3 * G.m + dynGraphSize vCap eCap + eCap + G.m * (1 + 2 * Nat.ceil (impl.γ_ℓ mMax)) +
          9 * G.m * (Nat.ceil (impl.γ_ℓ mMax) + 1) ≤
          heapPtr + dsInitCoreSpaceBound impl mMax vCap eCap G :=
        hsp_ret _ le_rfl
      rw [hGact_m]; omega
    · dsimp only [gb, scrPtr]; rw [hraw_len]; exact Nat.add_le_add_left hsLen_le scrPtr
    · intro j hj; left; omega
    · intro j hj; left; omega
    · intro e he; have := hG_e e (hGact_E ▸ he); left; omega
    · intro e he _ _
      have hbd := hmEmbBnd_IE e (hGact_E ▸ he)
      have hml : (mWalkEncode (idEmb e)).length = 3 := by simp [mWalkEncode_length, idEmb]
      left; omega
    · have hbd := hmEmbBnd_IE e (hGact_E ▸ he)
      have hml : (mWalkEncode (idEmb e)).length = 3 := by simp [mWalkEncode_length, idEmb]
      dsimp only [gb, scrPtr]; omega
  refine runs_seq_call_le (sparsifyDyn_meetsContract impl mMax hpSpDyn hpGuest hpFwd hpEmit
      hpRevDyn hpRevCore hpRevPrim hpBatch hpEdge hpOps hpGT hpSort)
    (by simp [evalArgs, Expr.eval, hr2, hr3, hr8, hr9])
    (fun z hz => by
      simp at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp [dynGraphSize] at hdg_lt <;> omega)
    hpre_sp ?_
  intro retSP memSP posSP ⟨_, _, _, _, _, hEqSP, hgb_jt, hjt_mep, hmep_ret, hret_lt,
    hret_ub, hDynJt, hmEmbB_SP, hmEmbLo_SP, hzSP, hfrSP⟩
  simp only [List.cons.injEq, and_true] at hEqSP
  rcases hEqSP with ⟨_, _, _, _, _, rfl, rfl⟩
  let jtPtr := memSP scrPtr
  let mEmbOutPtr := memSP (scrPtr + 1)
  have hscr1_ltw : scrPtr + 1 < 2 ^ w := by dsimp [scrPtr]; omega
  have hjt_w : jtPtr < 2 ^ w := by omega
  have hjt_M : memSP (jtPtr + dgMOff) = out.Jtilde.m := hDynJt.2.2.2.2.2.2.1
  have hjtM_ltw : jtPtr + 3 < 2 ^ w := by dsimp only [dynGraphSize] at hjt_mep; omega
  have hAuxSP : DynGraphAt memSP (dsAuxPtr b vCap eCap) vCap eCap Gact :=
    hAuxIE.of_agree fun addr _ _ => hfrSP addr (Or.inl (by omega)) (by omega)
  have hfr_all_SP : ∀ addr, addr < heapPtr →
      (addr < dsAuxPtr b vCap eCap ∨ dsAuxPtr b vCap eCap + dynGraphSize vCap eCap ≤ addr) →
      (addr < dsMEmbTempBase b L vCap eCap ∨ dsMEmbTempBase b L vCap eCap + eCap ≤ addr) →
      memSP addr = st.mem addr := fun addr ha hna hnm => by
    rw [hfrSP addr (Or.inl (lt_of_lt_of_le ha (Nat.le_add_right _ _))) (by omega)]
    change memIE addr = st.mem addr
    rw [hfrIE addr hnm (Or.inl ha)]
    change memBA addr = st.mem addr
    exact hfrBA addr hna
  have heL_expr : jtPtr + 4 + (7 * vCap + eCap) = dgEListBase jtPtr vCap eCap := by
    simp only [dgEListBase]; omega
  have hjt4_ltw : jtPtr + 4 < 2 ^ w := by dsimp only [dynGraphSize] at hjt_mep; omega
  have h7v_ltw : 7 * vCap < 2 ^ w := by dsimp only [dynGraphSize] at hdg_lt; omega
  have h7ve_ltw : 7 * vCap + eCap < 2 ^ w := by dsimp only [dynGraphSize] at hdg_lt; omega
  have hjtEL_ltw : dgEListBase jtPtr vCap eCap < 2 ^ w := by
    rw [← heL_expr]; dsimp only [dynGraphSize] at hjt_mep; omega
  refine runs_seq_assign_le (v := jtPtr)
    (Expr.eval_load_of_eq (by simp [Expr.eval, scrPtr]) rfl) ?_
  refine runs_seq_assign_le (v := mEmbOutPtr)
    (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, h1_w, hscr1_ltw]) rfl) ?_
  refine runs_seq_assign_le (v := out.Jtilde.m)
    (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, dgMOff, h3_w, hjtM_ltw]) hjt_M) ?_
  refine runs_seq_assign_le (v := dgEListBase jtPtr vCap eCap)
    (by simp [Expr.eval, BinOp.eval, hr2, hr3, h4_w, h7_w, hjt4_ltw, h7v_ltw, h7ve_ltw,
      heL_expr, hjtEL_ltw]) ?_
  refine spPhase_cont_step hrest ?_ (by
      dsimp only [Expr.size, argsSize, sparsifyDynCost, sparsifyDynContract,
        buildActiveOnAuxContract, dsWriteIdEmbContract]
      rw [show Gact = activeSubgraph G from rfl, show (activeSubgraph G).m = G.m from rfl]
      omega)
  refine ⟨jtPtr, mEmbOutPtr, retSP, by simp [hr0], by simp, by simp [hr2], by simp [hr3],
    by simp [hr4], by simp [hr6], by simp [hr7], by simp [hr8], by simp [hr11],
    by simp, by simp, by simp, by simp [out, Gact], by simp, by omega, hjt_mep.le, hmep_ret, ?_, hzSP,
    hAuxSP, hDynJt, hmEmbB_SP, hmEmbLo_SP, hfr_all_SP⟩
  have hret_ub' : retSP ≤ (heapPtr + 3 * G.m + (8 + 3 * Gact.n + 11 * G.m)) +
      2 ^ (wordSize impl.cw (canonSparsifyInput Gact Gact idEmb) + 1) + 2 + 3 * G.m +
      dynGraphSize vCap eCap + eCap + G.m * (1 + 2 * Nat.ceil (impl.γ_ℓ mMax)) := by
    rw [← hGact_m]; exact hret_ub
  exact hsp_ret retSP hret_ub'

end

end MinCostFlow.DynSpanner.Program
