module

public import MinCostFlow.DynSpanner.Program.DynSpannerInitCorePrep
public import MinCostFlow.DynSpanner.Program.DynSpannerInitCoreBranch

import Mathlib.Tactic.Linarith

/-!
# Full contract proof for `dsInitCoreStmt` (`DynSpannerInitCore`)

Proves the empty branch (`G.m = 0`), combines it with `dsInitCorePrep_triple` and
`dsInitCore_nonempty_triple`, and establishes `dsInitCore_meetsContract`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

public section

private lemma dsCore_empty_addrs (b L vCap eCap : ℕ) :
    b + dsGenOff < dsGPtr b ∧
    b + dsLOff < dsGPtr b ∧
    b + dsVCapOff < dsGPtr b ∧
    b + dsECapOff < dsGPtr b ∧
    dsGPtr b + dynGraphSize vCap eCap = dsHPtr b vCap eCap ∧
    dsHPtr b vCap eCap + dynGraphSize vCap eCap = dsAuxPtr b vCap eCap ∧
    dsAuxPtr b vCap eCap + dynGraphSize vCap eCap = dsMinHBase b vCap eCap ∧
    dsMinHBase b vCap eCap + 3 * eCap = dsHHeadBase b vCap eCap ∧
    dsHHeadBase b vCap eCap < dsHDegDummyBase b L vCap eCap ∧
    dsHDegDummyBase b L vCap eCap < dsDomGenBase b L vCap eCap ∧
    dsDomGenBase b L vCap eCap ≤ dsEdgeDomGenBase b L vCap eCap ∧
    dsDomGenBase b L vCap eCap ≤ dsRevGenBase b L vCap eCap ∧
    dsDomGenBase b L vCap eCap ≤ dsVStampBase b L vCap eCap ∧
    dsVStampBase b L vCap eCap + vCap ≤ dsMEmbTempBase b L vCap eCap ∧
    dsEdgeDomGenBase b L vCap eCap + eCap ≤ dsMEmbTempBase b L vCap eCap ∧
    dsRevGenBase b L vCap eCap + vCap ≤ dsMEmbTempBase b L vCap eCap ∧
    dsMEmbTempBase b L vCap eCap + eCap = b + dsFixedSize L vCap eCap := by
  obtain ⟨hg, hl, hv, he, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    dsInitCore_fixed_order b L vCap eCap
  have he_mul : eCap ≤ (L + 1) * eCap := Nat.le_mul_of_pos_left eCap (Nat.succ_pos L)
  have hv_mul : vCap ≤ (L + 1) * vCap := Nat.le_mul_of_pos_left vCap (Nat.succ_pos L)
  have hf := dsFixedSize_add b L vCap eCap
  have hvs := dsVStampBase_eq b L vCap eCap
  have hme := dsMEmbTempBase_eq b L vCap eCap
  have hrg := dsRevGenBase_eq b L vCap eCap
  have hdg := dsDomGenBase_eq b L vCap eCap
  have h1 := dsMinHBase_eq b vCap eCap
  have hpi : dsEdgeDomGenBase b L vCap eCap + (L + 1) * eCap = dsPiPtrBase b L vCap eCap := rfl
  have hrh : dsRevGenBase b L vCap eCap + (L + 1) * vCap = dsRevHeadBase b L vCap eCap := rfl
  have hed : dsDomGenBase b L vCap eCap + (L + 1) = dsEdgeDomGenBase b L vCap eCap := rfl
  have hpr : dsPiPtrBase b L vCap eCap + (L + 1) * eCap = dsRevGenBase b L vCap eCap := rfl
  refine ⟨hg, hl, hv, he, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hf⟩ <;>
    simp only [dsHHeadBase, dsHPrevBase, dsHNextBase, dsHDegDummyBase, dsDomGenBase] at * <;> omega

private lemma dsInitCore_empty_triple {impl : SparsifyImpl} {mMax w L vCap eCap b heapPtr : ℕ}
    {G : MGraph} {mem0 mem1 : ℕ → ℕ} {p : Program} {bLW bRev bOps : ℕ}
    (hpLW : p.HasAt bLW (levelWalkProcs bOps bRev)) (hpRev : p.HasAt bRev (revProcs bOps bRev))
    (hpOps : p.HasAt bOps dgOpsProcs)
    (hw16 : 16 ≤ 2 ^ w) (hb1 : 1 ≤ b)
    (hfix : b + dsFixedSize L vCap eCap ≤ heapPtr)
    (hheap_w : heapPtr < 2 ^ w) (hz0 : ZeroFrom mem0 heapPtr) (hGm0 : G.m = 0)
    (hL0 : mem0 (b + dsLOff) = L) (hvC0 : mem0 (b + dsVCapOff) = vCap)
    (heC0 : mem0 (b + dsECapOff) = eCap) (hgen_w : mem0 (b + dsGenOff) + 1 + G.m < 2 ^ w)
    (hmin0 : ∀ e < eCap, mem0 (dsMinHBase b vCap eCap + e) = 0)
    (hdll0 : IsDoublyLinkedList mem0 (dsHPrevBase b vCap eCap) (dsHNextBase b vCap eCap)
      (dsHHeadBase b vCap eCap) eCap [])
    (hdeg0 : mem0 (dsHDegDummyBase b L vCap eCap) = 0)
    (hedg0 : ∀ e < eCap, mem0 (dsEdgeDomGenBase b L vCap eCap + e) ≤ mem0 (b + dsGenOff))
    (hrevg0 : ∀ v < vCap, mem0 (dsRevGenBase b L vCap eCap + v) ≤ mem0 (b + dsGenOff))
    (hvst0 : ∀ v < vCap, mem0 (dsVStampBase b L vCap eCap + v) ≤ mem0 (b + dsGenOff))
    (hG_v : ∀ v ∈ G.V, v < vCap) (hG_e : ∀ e ∈ G.E, e < eCap) (hG_val : G.IsValid)
    (hG1 : DynGraphAt mem1 (dsGPtr b) vCap eCap G)
    (hH1 : DynGraphAt mem1 (dsHPtr b vCap eCap) vCap eCap
      { V := G.V, E := ∅, tail := fun _ => 0, head := fun _ => 0 })
    (hAux1 : DynGraphAt mem1 (dsAuxPtr b vCap eCap) vCap eCap emptyMGraph)
    (hfr1 : ∀ addr, addr < dsHPtr b vCap eCap ∨
        dsHPtr b vCap eCap + dynGraphSize vCap eCap ≤ addr →
      mem1 addr = mem0 addr) :
    Triple w p
      (fun st => st.mem = mem1 ∧
        st.regs 0 = b ∧ st.regs 1 = heapPtr ∧ st.regs 2 = vCap ∧ st.regs 3 = eCap ∧
        st.regs 4 = L ∧ st.regs 6 = dsGPtr b ∧ st.regs 9 = dsMEmbTempBase b L vCap eCap)
      (.assign 12 (.bin .add (.bin .add (.reg 6) (.const 4))
         (.bin .add (.bin .mul (.const 7) (.reg 2)) (.reg 3))) ;;
       .call 1 (bLW + lwIdxSetLevelWalks) [.reg 0, .const 0, .reg 12, .const 0, .reg 9, .reg 1] ;;
       .ret (.reg 1))
      (fun o st' => ∃ ret, o = .returned ret ∧
        (dsInitCoreContract impl mMax w L vCap eCap b G).post [b, heapPtr] mem0 ret st'.mem)
      (fun _ => 270) := by
  intro st ω ⟨hm, hr0, hr1, hr2, hr3, hr4, hr6, hr9⟩
  subst hm
  have hGE_empty : G.E = ∅ := Finset.card_eq_zero.mp hGm0
  have hCoreEq : initCore G (canonicalSparsify impl) = (emptyGraphOn G, idEmb, G.n) := by
    simp [initCore, hGE_empty]
  have hH0_val : (emptyGraphOn G).IsValid := fun _ h => by simp [emptyGraphOn] at h
  have hH1_emp : DynGraphAt st.mem (dsHPtr b vCap eCap) vCap eCap (emptyGraphOn G) :=
    hH1.congr_ends (by rfl) (by simp [emptyGraphOn]) (fun _ h => False.elim (Finset.notMem_empty _ h))
  obtain ⟨ho_g, ho_l, ho_v, ho_e, hgh, hha, ham, hm_h, hh_d, hd_dm, hd_ed, hd_rg, hd_vs,
    hvs_me, hed_me, hrg_me, hme_fix⟩ := dsCore_empty_addrs b L vCap eCap
  have h4_w : (4 : ℕ) < 2 ^ w := by omega
  have h7_w : (7 : ℕ) < 2 ^ w := by omega
  have hg4_lt : dsGPtr b + 4 < 2 ^ w := by simp only [dynGraphSize] at hgh; omega
  have h7v_lt : 7 * vCap < 2 ^ w := by simp only [dynGraphSize] at hgh; omega
  have h7ve_lt : 7 * vCap + eCap < 2 ^ w := by simp only [dynGraphSize] at hgh; omega
  have heLG_eq : dsGPtr b + 4 + (7 * vCap + eCap) = dgEListBase (dsGPtr b) vCap eCap := by
    simp only [dgEListBase]; omega
  have heLG_ltw : dgEListBase (dsGPtr b) vCap eCap < 2 ^ w := by
    simp only [dgEListBase, dynGraphSize] at hgh ⊢; omega
  have hdg_elist_ge : dsGPtr b ≤ dgEListBase (dsGPtr b) vCap eCap := by
    simp only [dgEListBase]; omega
  have heL_at_nil : ListAt st.mem (dgEListBase (dsGPtr b) vCap eCap) [] := fun _ hi => by simp at hi
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := dgEListBase (dsGPtr b) vCap eCap)
    (by simp [Expr.eval, BinOp.eval, hr6, hr2, hr3, h4_w, h7_w, hg4_lt, h7v_lt, h7ve_lt,
      heLG_eq, heLG_ltw]) ?_
  have hpre_lw : (dsSetLevelWalksContract w L vCap eCap b 0 G
      (emptyGraphOn G) [] idEmb (fun _ => False)).pre
      [b, 0, dgEListBase (dsGPtr b) vCap eCap, 0, dsMEmbTempBase b L vCap eCap, heapPtr] st.mem := by
    refine ⟨dgEListBase (dsGPtr b) vCap eCap, dsMEmbTempBase b L vCap eCap, heapPtr,
      rfl, hw16, hb1, Nat.zero_le _, hfix, (by simp; omega), heLG_ltw, (by omega),
      (by rw [hfr1 _ (Or.inl (by omega)), hL0]), (by rw [hfr1 _ (Or.inl (by omega)), hvC0]),
      (by rw [hfr1 _ (Or.inl (by omega)), heC0]),
      (by simp only [List.length_nil]; rw [hfr1 _ (Or.inl (by omega))]; omega),
      (fun v hv => by rw [hfr1 _ (Or.inr (by omega)), hfr1 _ (Or.inl (by omega))]; exact hvst0 v hv),
      (fun e he => by
        simp only [Nat.zero_mul, Nat.add_zero]
        rw [hfr1 _ (Or.inr (by omega)), hfr1 _ (Or.inl (by omega))]
        exact hedg0 e he),
      (fun v hv => by
        simp only [Nat.zero_mul, Nat.add_zero]
        rw [hfr1 _ (Or.inr (by omega)), hfr1 _ (Or.inl (by omega))]
        exact hrevg0 v hv),
      (fun _ h => False.elim h), (fun _ hk => by simp at hk),
      (fun _ he => absurd he List.not_mem_nil),
      List.nodup_nil, heL_at_nil, hG1, hG_val, hG_v, hG_e, hH1_emp, hH0_val, Finset.Subset.rfl, hG_v,
      (fun _ h => absurd h (by simp [emptyGraphOn])), (fun _ he => absurd he List.not_mem_nil)⟩
  refine runs_seq_call_le (dsSetLevelWalks_meetsContract hpLW hpRev hpOps)
    (by simp [evalArgs, Expr.eval, hr0, hr1, hr9])
    (fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    hpre_lw ?_
  intro retFinal memFinal _ ⟨_, _, _, hEqLW, hret_ge, hret_le, hgenF, hdomF, hvstF,
    hedgLeF, hedgF, _, ⟨rev0, hrev0⟩, hfrLW⟩
  simp only [List.cons.injEq, true_and, and_true, List.length_nil] at hEqLW
  rcases hEqLW with ⟨rfl, rfl, rfl⟩
  dsimp only at hgenF hdomF hvstF hedgLeF hedgF hfrLW
  simp only [List.map_nil, List.sum_nil, MulZeroClass.mul_zero, Nat.add_zero,
    List.length_nil] at hret_le hgenF hdomF
  have hret_eq : retFinal = heapPtr := by omega
  subst retFinal
  have hlw_dom : ∀ addr, dsMinHBase b vCap eCap ≤ addr → addr < dsDomGenBase b L vCap eCap →
      memFinal addr = mem0 addr := fun addr hlo hhi =>
    (hfrLW addr (lw_frame_of_lt_dom hfix hhi (by omega))).trans (hfr1 addr (Or.inr (by omega)))
  have hlw_ge_h : ∀ addr, dsHPtr b vCap eCap ≤ addr → addr < dsDomGenBase b L vCap eCap →
      memFinal addr = st.mem addr := fun addr hlo hhi =>
    hfrLW addr (lw_frame_of_lt_dom hfix hhi (by omega))
  have hlw_ge_heap : ∀ addr, heapPtr ≤ addr → dsLevelWalksFrameCond L vCap eCap b 0 heapPtr heapPtr addr := by
    intro addr ha
    have hvs := dsVStampBase_eq b L vCap eCap
    have hrh := dsRevHeadBase_eq b L vCap eCap
    have hpi : dsPiPtrBase b L vCap eCap + (L + 1) * eCap = dsRevGenBase b L vCap eCap := rfl
    have hed : dsEdgeDomGenBase b L vCap eCap + (L + 1) * eCap = dsPiPtrBase b L vCap eCap := rfl
    have hrev := dsRevGenBase_eq b L vCap eCap
    have hm := dsMEmbTempBase_eq b L vCap eCap
    refine ⟨by omega, by omega, fun e he => ?_, fun e he => ?_, fun v hv => ?_,
      fun v hv => ?_, fun v hv => ?_, Or.inr ha⟩ <;>
      { try simp only [Nat.zero_mul, Nat.add_zero]
        omega }
  have hzero_final : ZeroFrom memFinal heapPtr := fun addr ha => by
    rw [hfrLW addr (hlw_ge_heap addr ha), hfr1 addr (Or.inr (by omega))]
    exact hz0 addr ha
  refine runs_ret_le (by simp [Expr.eval]) ⟨heapPtr, rfl, heapPtr, rfl, le_refl _,
    Nat.le_add_right _ _, hzero_final, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_
  · dsimp only; rw [hgenF, hfr1 _ (Or.inl (by omega)), hGm0]
  · dsimp only; rw [hdomF, hfr1 _ (Or.inl (by omega))]
  · dsimp only; exact hvstF
  · intro e he; dsimp only; simpa [Nat.zero_mul, Nat.add_zero] using hedgLeF e he
  · dsimp only; rw [hCoreEq]; exact hH1_emp.of_agree fun addr h1 h2 => hlw_ge_h addr h1 (by omega)
  · dsimp only; exact hAux1.of_agree fun addr h1 h2 => hlw_ge_h addr (by omega) (by omega)
  · intro e he; dsimp only; rw [hCoreEq]
    have hm_lw : memFinal (dsMinHBase b vCap eCap + e) = mem0 (dsMinHBase b vCap eCap + e) :=
      hlw_dom _ (by omega) (by omega)
    rw [hm_lw, hmin0 e he]; simp [emptyGraphOn]
  · dsimp only; rw [hCoreEq]
    refine ⟨[], hdll0.of_agree (hlw_dom _ (by omega) (by omega))
      (fun _ h => by cases h) (fun _ h => by cases h), ?_, by simp [emptyGraphOn]⟩
    rw [hlw_dom _ (by omega) (by omega), hdeg0]; simp
  · intro e he; dsimp only
    simpa [Nat.zero_mul, Nat.add_zero, hGE_empty] using hedgF e he
  · intro e he; rw [hGE_empty] at he; exact False.elim (Finset.notMem_empty e he)
  · refine ⟨rev0, fun v hv => ?_⟩
    dsimp only; rw [hCoreEq]
    rcases hrev0 v hv with ⟨hrg, hnd, hmem_rev, hll⟩
    simp only [Nat.zero_mul, Nat.add_zero] at hrg hmem_rev hll ⊢
    refine ⟨hrg, hnd, fun e => ?_, ?_⟩
    · simpa [hGE_empty] using hmem_rev e
    · split_ifs at hll ⊢ with hc
      · exact hll.mono fun _ ha => by rcases ha with h | h; exact False.elim h; exact h
      · exact hll
  · intro addr hfc; dsimp only
    rw [hfrLW addr (dsInitCoreFrameCond_to_lw (le_refl heapPtr) hfc)]
    exact hfr1 addr (by rcases hfc.2.1 with h | h <;> [left; right] <;> omega)
  · simp only [dsSetLevelWalksContract, List.map_nil, List.sum_nil, List.length_nil,
      argsSize, Expr.size]; omega

private def seqRight : Stmt → Stmt → Stmt
  | .seq a b, r => .seq a (seqRight b r)
  | s, r => .seq s r

private def rightDepth : Stmt → ℕ
  | .seq _ b => rightDepth b + 1
  | _ => 0

private lemma runs_seqRight_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {s r : Stmt} {st : State}
    {k T : ℕ} {Q : Outcome → State → Prop}
    (h : ∃ o st' c, Runs w p ω (seqRight s r) st o st' c ∧ Q o st' ∧ (k + rightDepth s) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq s r) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  induction s generalizing st k T with
  | seq a b _ ihb =>
    refine runs_seq_assoc_le ?_
    rcases h with ⟨o, st', c, hrun, hq, hc⟩
    rcases runs_seq_iff.mp hrun with ⟨v, c₁, hr₁, rfl, rfl⟩ | ⟨st₁, c₁, c₂, hr₁, hr₂, rfl⟩
    · exact ⟨.returned v, st', c₁ + 1, runs_seq_iff.mpr (Or.inl ⟨v, c₁, hr₁, rfl, rfl⟩),
        hq, by simp only [rightDepth] at hc; omega⟩
    · obtain ⟨o', st'', c₂', hr₂', hq', hc'⟩ :=
        ihb (st := st₁) (k := 0) (T := rightDepth b + c₂) ⟨o, st', c₂, hr₂, hq, by rw [Nat.zero_add]⟩
      exact ⟨o', st'', c₁ + c₂' + 1, runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂', hr₁, hr₂', rfl⟩),
        hq', by simp only [rightDepth] at hc; omega⟩
  | _ =>
    rcases h with ⟨o, st', c, hrun, hq, hc⟩
    exact ⟨o, st', c, hrun, hq, hc⟩

theorem dsInitCore_meetsContract {impl : SparsifyImpl} {mMax w L vCap eCap b : ℕ} {G : MGraph}
    {p : Program} {bOps bEdge bBatch bPhase bLW bSpDyn bInit : ℕ}
    {bSort bSplit bFwd bRevPrim bGT bRevCore bRevDyn bEmit bGuest bRev : ℕ}
    (hpInit : p.HasAt bInit (initProcs bOps bEdge bBatch bPhase bLW bSpDyn bInit))
    (hpOps : p.HasAt bOps dgOpsProcs) (hpPhase : p.HasAt bPhase (phaseProcs bOps bEdge))
    (hpLW : p.HasAt bLW (levelWalkProcs bOps bRev)) (hpRev : p.HasAt bRev (revProcs bOps bRev))
    (hpSpDyn : p.HasAt bSpDyn (sparsifyDynProcs impl.program.regBound impl.cw bFwd bRevDyn bGuest))
    (hpGuest : p.HasAt bGuest (sparsifyGuestProcs impl bGuest))
    (hpFwd : p.HasAt bFwd (gtForwardProcs bOps bGT bEmit bFwd))
    (hpEmit : p.HasAt bEmit (gtEmitProcs bSort bOps bGT))
    (hpRevDyn : p.HasAt bRevDyn (gtRevDynProcs bOps bGT bRevCore))
    (hpRevCore : p.HasAt bRevCore (gtRevCoreProcs bBatch bRevPrim))
    (hpRevPrim : p.HasAt bRevPrim gtRevPrimProcs)
    (hpBatch : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpGT : p.HasAt bGT (gtProcs bSort bOps)) (hpSort : p.HasAt bSort (sortProcs bSort)) :
    MeetsContract w p (bInit + initIdxCore) (dsInitCoreContract impl mMax w L vCap eCap b G) := by
  refine meetsContract_of_runs
    (hpInit.get (i := initIdxCore) (by simp [initProcs, initIdxCore]))
    fun args mem0 pos ω _ hpre => ?_
  rcases hpre with ⟨heapPtr, rfl, hw16, hb1, hfix, hspace, hz0, hw'_le, hL0, hvC0, heC0, hgen_w,
    hmin0, hdll0, hdeg0, hdom0, hedg0, hrevg0, hvst0, hG0, hH0, hAux0, hG_val, hGm_max, hG_v, hG_e⟩
  have hheap_w : heapPtr < 2 ^ w := by omega
  simp only [initProcs, initIdxCore, List.getElem_cons_zero]
  dsimp only [dsInitCoreStmt]
  refine runs_start_le ?_
  refine runs_seq_triple_le (fun st ω hst =>
      dsInitCorePrep_triple hpOps hw16 hfix hheap_w hL0 hvC0 heC0 hG0 hH0 hst)
    ⟨by simp [startState], by simp [startState], by simp [startState]⟩ ?_
  rintro st1 ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, _,
    hH1, hfr1⟩
  have hG1 : DynGraphAt st1.mem (dsGPtr b) vCap eCap G :=
    hG0.of_agree fun addr _ h2 => hfr1 addr (Or.inl (by
      have : dsGPtr b + dynGraphSize vCap eCap = dsHPtr b vCap eCap := rfl
      omega))
  have hAux1 : DynGraphAt st1.mem (dsAuxPtr b vCap eCap) vCap eCap emptyMGraph :=
    hAux0.of_agree fun addr h1 _ => hfr1 addr (Or.inr (by
      have : dsHPtr b vCap eCap + dynGraphSize vCap eCap = dsAuxPtr b vCap eCap := rfl
      omega))
  refine runs_seq_cond_le (v := G.m) (by simp [Expr.eval, hr11]) ?_ ?_
  · intro hGm_ne
    have hE_ne : G.E.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hGm_ne)
    refine runs_seqRight_le ?_
    dsimp only [seqRight, rightDepth]
    refine runs_triple_le (dsInitCore_nonempty_triple hpOps hpPhase hpLW hpRev hpSpDyn hpGuest
        hpFwd hpEmit hpRevDyn hpRevCore hpRevPrim hpBatch hpEdge hpGT hpSort hw16 hb1 hfix hspace
        hz0 hGm_ne (hw'_le hE_ne) hL0 hvC0 heC0 hgen_w hmin0 hdll0 hdeg0 hdom0 hedg0 hrevg0 hvst0
        hGm_max hG_v hG_e hG_val hG1 hH1 hAux1 hfr1)
      ⟨rfl, hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11⟩
      (fun _ _ ⟨ret, hr, hp⟩ => by rw [hr]; exact hp) ?_
    dsimp only [dsInitCoreContract, dsInitCoreCost, dsInitCorePrepStmt, Expr.size, argsSize]
    simp only [hGm_ne, ↓reduceIte]
    have h1 : (activeSubgraph G).m = G.m := rfl
    omega
  · intro hGm0
    refine runs_seqRight_le ?_
    dsimp only [seqRight, rightDepth]
    refine runs_triple_le (dsInitCore_empty_triple (impl := impl) (mMax := mMax) hpLW hpRev hpOps hw16 hb1 hfix
        hheap_w hz0 hGm0 hL0 hvC0 heC0 hgen_w hmin0 hdll0 hdeg0 hedg0 hrevg0 hvst0 hG_v hG_e
        hG_val hG1 hH1 hAux1 hfr1)
      ⟨rfl, hr0, hr1, hr2, hr3, hr4, hr6, hr9⟩
      (fun _ _ ⟨ret, hr, hp⟩ => by rw [hr]; exact hp) ?_
    dsimp only [dsInitCoreContract, dsInitCoreCost, Expr.size]
    simp only [hGm0, ↓reduceIte]
    omega

end

end MinCostFlow.DynSpanner.Program