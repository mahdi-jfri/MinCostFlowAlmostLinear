module

public import MinCostFlow.DynSpanner.Program.DynSpannerInitCorePost

import Mathlib.Tactic.Ring

/-!
# Verification of the nonempty branch of `dsInitCoreStmt` (`DynSpannerInitCoreBranch`)

Composes `dsInitCore_spPhase_cont`, `dsInsertJtildeH_triple`, and `dsInitCore_postIns_triple` to
verify the nonempty branch of `dsInitCoreStmt`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

public section

private lemma isWalk_of_ends_sub {J G : MGraph} (hE : J.E ⊆ G.E)
    (hEnds : ∀ e ∈ J.E, J.tail e = G.tail e ∧ J.head e = G.head e)
    {u v : ℕ} {P : List (ℕ × Bool)} (hW : J.IsWalk u v P) : G.IsWalk u v P := by
  induction hW with
  | nil u => exact .nil u
  | cons hxE hsrc hrest ih =>
    rename_i u' v' x xs
    have he := hEnds x.1 hxE
    have hsrcG : G.src x = u' := by
      have hs : J.src x = G.src x := by
        cases x.2 <;> simp [MGraph.src, he.1, he.2]
      exact hs.symm.trans hsrc
    have hdst_eq : J.dst x = G.dst x := by
      cases x.2 <;> simp [MGraph.dst, he.1, he.2]
    exact .cons (hE hxE) hsrcG (hdst_eq ▸ ih)

lemma dsInitCore_nonempty_triple {impl : SparsifyImpl} {mMax w L vCap eCap b heapPtr : ℕ}
    {G : MGraph} {mem0 mem1 : ℕ → ℕ}
    {p : Program} {bOps bEdge bPhase bLW bSpDyn : ℕ}
    {bSort bSplit bBatch bFwd bRevPrim bGT bRevCore bRevDyn bEmit bGuest bRev : ℕ}
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
    (hpGT : p.HasAt bGT (gtProcs bSort bOps)) (hpSort : p.HasAt bSort (sortProcs bSort))
    (hw16 : 16 ≤ 2 ^ w) (hb1 : 1 ≤ b)
    (hfix : b + dsFixedSize L vCap eCap ≤ heapPtr)
    (hspace : heapPtr + dsInitCoreSpaceBound impl mMax vCap eCap G < 2 ^ w)
    (hz0 : ZeroFrom mem0 heapPtr) (hGm_ne : G.m ≠ 0)
    (hw'_le : wordSize impl.cw (canonSparsifyInput (activeSubgraph G) (activeSubgraph G) idEmb) ≤ w)
    (hL0 : mem0 (b + dsLOff) = L) (hvC0 : mem0 (b + dsVCapOff) = vCap)
    (heC0 : mem0 (b + dsECapOff) = eCap)
    (hgen_w : mem0 (b + dsGenOff) + 1 + G.m < 2 ^ w)
    (hmin0 : ∀ e < eCap, mem0 (dsMinHBase b vCap eCap + e) = 0)
    (hdll0 : IsDoublyLinkedList mem0 (dsHPrevBase b vCap eCap) (dsHNextBase b vCap eCap)
      (dsHHeadBase b vCap eCap) eCap [])
    (hdeg0 : mem0 (dsHDegDummyBase b L vCap eCap) = 0)
    (hdom0 : mem0 (dsDomGenBase b L vCap eCap) ≤ mem0 (b + dsGenOff))
    (hedg0 : ∀ e < eCap, mem0 (dsEdgeDomGenBase b L vCap eCap + e) ≤ mem0 (b + dsGenOff))
    (hrevg0 : ∀ v < vCap, mem0 (dsRevGenBase b L vCap eCap + v) ≤ mem0 (b + dsGenOff))
    (hvst0 : ∀ v < vCap, mem0 (dsVStampBase b L vCap eCap + v) ≤ mem0 (b + dsGenOff))
    (hGm_max : G.m ≤ mMax)
    (hG_v : ∀ v ∈ G.V, v < vCap) (hG_e : ∀ e ∈ G.E, e < eCap) (hG_val : G.IsValid)
    (hG1 : DynGraphAt mem1 (dsGPtr b) vCap eCap G)
    (hH1 : DynGraphAt mem1 (dsHPtr b vCap eCap) vCap eCap
      { V := G.V, E := ∅, tail := fun _ => 0, head := fun _ => 0 })
    (hAux1 : DynGraphAt mem1 (dsAuxPtr b vCap eCap) vCap eCap emptyMGraph)
    (hfr1 : ∀ addr, addr < dsHPtr b vCap eCap ∨
        dsHPtr b vCap eCap + dynGraphSize vCap eCap ≤ addr →
      mem1 addr = mem0 addr) :
    let Gact := activeSubgraph G
    let out := canonicalSparsify impl Gact Gact idEmb
    Triple w p
      (fun st => st.mem = mem1 ∧
        st.regs 0 = b ∧ st.regs 1 = heapPtr ∧ st.regs 2 = vCap ∧ st.regs 3 = eCap ∧
        st.regs 4 = L ∧ st.regs 5 = dynGraphSize vCap eCap ∧ st.regs 6 = dsGPtr b ∧
        st.regs 7 = dsHPtr b vCap eCap ∧ st.regs 8 = dsAuxPtr b vCap eCap ∧
        st.regs 9 = dsMEmbTempBase b L vCap eCap ∧ st.regs 10 = G.n ∧ st.regs 11 = G.m)
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
         (.bin .add (.bin .mul (.const 7) (.reg 2)) (.reg 3))) ;;
       forRange 20 (.const 0) (.reg 18)
         (.assign 21 (.load (.bin .add (.reg 19) (.reg 20))) ;;
          .call 22 (bOps + dgIdxGetTail) [.reg 6, .reg 21] ;;
          .call 23 (bOps + dgIdxGetHead) [.reg 6, .reg 21] ;;
          .call 24 (bEdge + dgIdxInsertEdge) [.reg 7, .reg 21, .reg 22, .reg 23] ;;
          .call 24 (bPhase + phaseIdxHBucketCons) [.reg 0, .const 0, .reg 21]) ;;
       .call 13 (bPhase + phaseIdxClearAux) [.reg 8] ;;
       .assign 12 (.bin .add (.bin .add (.reg 6) (.const 4))
         (.bin .add (.bin .mul (.const 7) (.reg 2)) (.reg 3))) ;;
       .call 15 (bLW + lwIdxShortcutEmb) [.reg 0, .reg 6, .reg 12, .reg 11, .reg 17, .reg 15] ;;
       .call 1 (bLW + lwIdxSetLevelWalks) [.reg 0, .const 0, .reg 12, .reg 11, .reg 17, .reg 15] ;;
       .ret (.reg 1))
      (fun o st' => ∃ ret, o = .returned ret ∧
        (dsInitCoreContract impl mMax w L vCap eCap b G).post [b, heapPtr] mem0 ret st'.mem)
      (fun _ => sparsifyDynCost impl mMax Gact Gact idEmb +
        800 * (∑ e ∈ G.E, (out.emb e).length) + 30 * G.n + 2380 * G.m +
        820 * out.Jtilde.E.card + 950) := by
  intro Gact out st ω hst
  refine runs_start_le ?_
  refine dsInitCore_spPhase_cont hpOps hpPhase hpLW hpSpDyn hpGuest hpFwd hpEmit hpRevDyn hpRevCore
    hpRevPrim hpBatch hpEdge hpGT hpSort hw16 hfix hspace hz0 hGm_ne hw'_le hGm_max hG_v hG_e
    hG_val hG1 hAux1 hfr1 hst ?_
  rintro stSP ⟨jtPtr, mEmbOutPtr, heapSp, hr0, _, hr2, hr3, hr4, hr6, hr7, hr8, hr11, hr15,
    hr16, hr17, hr18, hr19, hjt_fix, hjt_mep, hmep_sp, hsp_bnd, hzSP, hAuxSP, hJtSP,
    hmEmbB_SP, hmEmbLo_SP, hfrSP⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := dsCore_base_chain b L vCap eCap
  have hheap_w : heapPtr < 2 ^ w := by omega
  have hb_fix_w : b + dsFixedSize L vCap eCap < 2 ^ w := by omega
  have hsp_w : heapSp < 2 ^ w := by omega
  obtain ⟨ho_g, ho_l, ho_v, ho_e, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    dsInitCore_fixed_order b L vCap eCap
  have hspec_all := initCore_spec (canonicalSparsify_spec_absorb impl mMax) hG_val hGm_max
  have hE_ne : G.E.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hGm_ne)
  have hCoreEq : (initCore G (canonicalSparsify impl)).1 =
      { V := G.V, E := out.Jtilde.E, tail := G.tail, head := G.head } ∧
      (initCore G (canonicalSparsify impl)).2.1 = fun e => shortcutWalk G (G.tail e) (out.emb e) := by
    simp [initCore, hE_ne]; exact ⟨rfl, rfl⟩
  have hH0_val : ({ V := G.V, E := out.Jtilde.E, tail := G.tail, head := G.head } : MGraph).IsValid :=
    hCoreEq.1 ▸ hspec_all.1
  have hSub0 := hspec_all.2.1
  rw [hCoreEq.1] at hSub0
  have hJt_sub : out.Jtilde.E ⊆ G.E := hSub0.2.1
  have hJm_w : out.Jtilde.m < 2 ^ w := by
    have hGm_le : G.m ≤ eCap := by
      simpa [MGraph.m] using Finset.card_le_card (fun e he => Finset.mem_range.mpr (hG_e e he))
    have hdg_lt := (dsAddrs_bound hfix hheap_w).2.1
    simp only [dynGraphSize] at hdg_lt
    have : out.Jtilde.m ≤ G.m := Finset.card_le_card hJt_sub
    omega
  have hagree_fix : ∀ addr, (addr < dsHPtr b vCap eCap ∨ dsMinHBase b vCap eCap ≤ addr) →
      addr < dsMEmbTempBase b L vCap eCap → stSP.mem addr = mem0 addr := fun addr hnh hnm => by
    rw [hfrSP addr (by omega) (by rcases hnh with h | h <;> [left; right] <;> omega) (Or.inl hnm)]
    exact hfr1 addr (by rcases hnh with h | h <;> [left; right] <;> omega)
  have hG_SP : DynGraphAt stSP.mem (dsGPtr b) vCap eCap G :=
    hG1.of_agree fun addr _ _ => hfrSP addr (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  have hH_SP : DynGraphAt stSP.mem (dsHPtr b vCap eCap) vCap eCap
      { V := G.V, E := ∅, tail := fun _ => 0, head := fun _ => 0 } :=
    hH1.of_agree fun addr _ _ => hfrSP addr (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  have hspec_sp := canonicalSparsify_spec_with_time impl mMax Gact Gact idEmb
    (activeSubgraph_isValid hG_val) (activeSubgraph_isValid hG_val) hGm_max
    (fun h => by rw [idEmb_length_eq_one h]) (idEmb_isEmbedding _)
  have hEmb_G : ∀ e ∈ G.E, G.IsWalk (G.tail e) (G.head e) (out.emb e) := fun e he => by
    have hE_jt : out.Jtilde.E ⊆ G.E := hJt_sub
    have hEnds_jt : ∀ e' ∈ out.Jtilde.E, out.Jtilde.tail e' = G.tail e' ∧
        out.Jtilde.head e' = G.head e' := fun e' he' => hspec_sp.1.2.2 e' he'
    exact isWalk_of_ends_sub hE_jt hEnds_jt (hspec_sp.2.1.2 e he)
  have hm_out_le_ceil : ∀ e ∈ G.E, (out.emb e).length ≤ Nat.ceil (impl.γ_ℓ mMax) := fun e he => by
    have hlen_sp := hspec_sp.2.2.2.1
    dsimp only [canonicalSparsifyParams] at hlen_sp
    rw [idEmb_comp, idEmb_length_eq_one (show Gact.E.Nonempty from hE_ne), Nat.cast_one,
      mul_one] at hlen_sp
    have he_le : (out.emb e).length ≤ out.emb.length Gact :=
      Finset.le_sup (f := fun x => (out.emb x).length) he
    exact Nat.cast_le.mp (le_trans (le_trans (Nat.cast_le.mpr he_le) hlen_sp) (Nat.le_ceil _))
  have hsum_out : ∑ e ∈ G.E, ((out.emb e).length + 1) ≤ G.m * (Nat.ceil (impl.γ_ℓ mMax) + 1) := by
    calc ∑ e ∈ G.E, ((out.emb e).length + 1)
        ≤ ∑ _ ∈ G.E, (Nat.ceil (impl.γ_ℓ mMax) + 1) :=
          Finset.sum_le_sum fun e he => Nat.add_le_add_right (hm_out_le_ceil e he) 1
      _ = G.m * (Nat.ceil (impl.γ_ℓ mMax) + 1) := by simp [MGraph.m]
  have hsum_out_w : heapSp + 9 * (∑ e ∈ G.E, ((out.emb e).length + 1)) ≤
      heapPtr + dsInitCoreSpaceBound impl mMax vCap eCap G := by
    have h1 := Nat.mul_le_mul_left 9 hsum_out
    have h2 : 9 * (G.m * (Nat.ceil (impl.γ_ℓ mMax) + 1)) =
        9 * G.m * (Nat.ceil (impl.γ_ℓ mMax) + 1) := by ring
    omega
  refine runs_seq_triple_le (dsInsertJtildeH_triple hpOps hpEdge hpPhase hw16 hb_fix_w hG_v hG_e
      hG_val hJt_sub hJm_w jtPtr mEmbOutPtr stSP.mem (by omega) (by omega) hsp_w
      (by rw [hagree_fix _ (Or.inl (by omega)) (by omega), hL0])
      (by rw [hagree_fix _ (Or.inl (by omega)) (by omega), hvC0])
      (by rw [hagree_fix _ (Or.inl (by omega)) (by omega), heC0])
      hG_SP hH_SP hJtSP
      (fun e he => by rw [hagree_fix _ (Or.inr (Nat.le_add_right _ _)) (by omega)]; exact hmin0 e he)
      (hdll0.of_agree (hagree_fix _ (Or.inr (by omega)) (by omega))
        (fun _ h => by cases h) (fun _ h => by cases h))
      (by rw [hagree_fix _ (Or.inr (by omega)) (by omega), hdeg0]))
    ⟨rfl, hr0, hr2, hr3, hr4, hr6, hr7, hr8, hr11, hr15, hr16, hr17, hr18, hr19⟩ ?_
  intro stIns ⟨hr0I, hr2I, hr3I, hr6I, hr7I, hr8I, hr11I, hr15I, hr17I, hH_Ins, hminI,
    ⟨buck0, hdllI, hdegI, hbuckI⟩, hfrI⟩
  refine runs_triple_le (dsInitCore_postIns_triple hpOps hpPhase hpLW hpRev hpEdge hw16 hb1 hfix
    (by omega) (by omega) (by omega) hsum_out_w (by omega) hz0 hzSP hL0 hvC0 heC0 hgen_w hrevg0
    hedg0 hvst0 hG_v hG_e hG_val hH0_val Finset.Subset.rfl hG_v hJt_sub hG_SP hAuxSP
    hEmb_G (hCoreEq.1 ▸ hCoreEq.2 ▸ hspec_all.2.2.2.1) hmEmbB_SP hmEmbLo_SP hfrSP hfr1)
    ⟨buck0, hr0I, hr2I, hr3I, hr6I, hr7I, hr8I, hr11I, hr15I, hr17I, hH_Ins, hminI,
      hdllI, hdegI, hbuckI, hfrI⟩ ?_ ?_
  · rintro o st' ⟨ret, rfl, h1, h2, h3, h4, h5, h6, h6_ed, h7, h8, h9, h10, h11, h12, h13, h14⟩
    exact ⟨ret, rfl, heapPtr, rfl, h1, h2, h3, h4, h5, h6, h6_ed, hCoreEq.1 ▸ h7, h8,
      by simpa [hCoreEq.1] using h9, by simpa [hCoreEq.1] using h10, h11,
      by simpa [hCoreEq.2] using h12, by simpa [hCoreEq.1, hCoreEq.2] using h13, h14⟩
  · have hGact_n : Gact.n ≤ G.n := activeSubgraph_n_le G
    have hJt_card : out.Jtilde.m = out.Jtilde.E.card := rfl
    have hGact_m : (activeSubgraph G).m = G.m := rfl
    dsimp only [Gact] at *
    rw [hGact_m] at *
    dsimp only [dsInsertJtildeH_triple, argsSize, Expr.size]
    omega

end

end MinCostFlow.DynSpanner.Program