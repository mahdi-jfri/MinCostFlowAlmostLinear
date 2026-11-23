module

public import MinCostFlow.DynSpanner.Program.DynSpannerInitCoreSp
public import MinCostFlow.DynSpanner.Program.DynSpannerInitInsertH
public import MinCostFlow.DynSpanner.Program.DynSpannerShortcut

import Mathlib.Tactic.Linarith

/-!
# Post-insert continuation for `dsInitCoreStmt` (`DynSpannerInitCorePost`)

Verifies the sequence `clearAuxGraph ;; dsSetLevelWalks ;; ret r1` starting from the state after
inserting `Jt` into `H` (`dsInsertJtildeH_triple`), together with framing helpers.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

public section

lemma dsCore_base_chain (b L vCap eCap : ℕ) :
    dsGPtr b + dynGraphSize vCap eCap = dsHPtr b vCap eCap ∧
    dsHPtr b vCap eCap + dynGraphSize vCap eCap = dsAuxPtr b vCap eCap ∧
    dsAuxPtr b vCap eCap + dynGraphSize vCap eCap = dsMinHBase b vCap eCap ∧
    dsMinHBase b vCap eCap + eCap = dsHNextBase b vCap eCap ∧
    dsHNextBase b vCap eCap + eCap = dsHPrevBase b vCap eCap ∧
    dsHPrevBase b vCap eCap + eCap = dsHHeadBase b vCap eCap ∧
    dsHHeadBase b vCap eCap + (L + 1) = dsHDegDummyBase b L vCap eCap ∧
    dsHDegDummyBase b L vCap eCap + (L + 1) = dsDomGenBase b L vCap eCap ∧
    dsDomGenBase b L vCap eCap ≤ dsMEmbTempBase b L vCap eCap ∧
    dsMEmbTempBase b L vCap eCap + eCap = b + dsFixedSize L vCap eCap := by
  have hm := dsMEmbTempBase_eq b L vCap eCap
  have hf := dsFixedSize_add b L vCap eCap
  have hdm := dsDomGenBase_eq b L vCap eCap
  have hr3 := dsRevGenBase_eq b L vCap eCap
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, hf⟩
  simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase,
    dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase, dsEdgeDomGenBase]
  omega

private lemma dsCore_postIns_bounds (b L vCap eCap : ℕ) :
    b + dsGenOff < dsGPtr b ∧
    b + dsLOff < dsGPtr b ∧
    b + dsVCapOff < dsGPtr b ∧
    b + dsECapOff < dsGPtr b ∧
    dsDomGenBase b L vCap eCap ≤ dsEdgeDomGenBase b L vCap eCap ∧
    dsEdgeDomGenBase b L vCap eCap + eCap ≤ dsMEmbTempBase b L vCap eCap ∧
    dsDomGenBase b L vCap eCap ≤ dsRevGenBase b L vCap eCap ∧
    dsRevGenBase b L vCap eCap + vCap ≤ dsMEmbTempBase b L vCap eCap ∧
    dsDomGenBase b L vCap eCap ≤ dsVStampBase b L vCap eCap ∧
    dsVStampBase b L vCap eCap + vCap ≤ dsMEmbTempBase b L vCap eCap := by
  have he_mul : eCap ≤ (L + 1) * eCap := Nat.le_mul_of_pos_left eCap (Nat.succ_pos L)
  have hv_mul : vCap ≤ (L + 1) * vCap := Nat.le_mul_of_pos_left vCap (Nat.succ_pos L)
  have hvs := dsVStampBase_eq b L vCap eCap
  have hme := dsMEmbTempBase_eq b L vCap eCap
  have hrg := dsRevGenBase_eq b L vCap eCap
  have hdg := dsDomGenBase_eq b L vCap eCap
  have hpi : dsEdgeDomGenBase b L vCap eCap + (L + 1) * eCap = dsPiPtrBase b L vCap eCap := rfl
  have hrh : dsRevGenBase b L vCap eCap + (L + 1) * vCap = dsRevHeadBase b L vCap eCap := rfl
  have hed : dsDomGenBase b L vCap eCap + (L + 1) = dsEdgeDomGenBase b L vCap eCap := rfl
  have hpr : dsPiPtrBase b L vCap eCap + (L + 1) * eCap = dsRevGenBase b L vCap eCap := rfl
  refine ⟨by simp [dsGenOff, dsGPtr, dsHdrSize], by simp [dsLOff, dsGPtr, dsHdrSize],
    by simp [dsVCapOff, dsGPtr, dsHdrSize], by simp [dsECapOff, dsGPtr, dsHdrSize], ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    omega

private lemma dsCore_vstamp_order (b L vCap eCap : ℕ) :
    dsGPtr b + dynGraphSize vCap eCap ≤ dsVStampBase b L vCap eCap ∧
    dsDomGenBase b L vCap eCap ≤ dsEdgeDomGenBase b L vCap eCap ∧
    dsEdgeDomGenBase b L vCap eCap + eCap ≤ dsVStampBase b L vCap eCap ∧
    dsRevGenBase b L vCap eCap + vCap ≤ dsVStampBase b L vCap eCap ∧
    dsVStampBase b L vCap eCap + vCap ≤ dsMEmbTempBase b L vCap eCap := by
  have he_mul : eCap ≤ (L + 1) * eCap := Nat.le_mul_of_pos_left eCap (Nat.succ_pos L)
  have hv_mul : vCap ≤ (L + 1) * vCap := Nat.le_mul_of_pos_left vCap (Nat.succ_pos L)
  have hvs := dsVStampBase_eq b L vCap eCap
  have hme := dsMEmbTempBase_eq b L vCap eCap
  have hrg := dsRevGenBase_eq b L vCap eCap
  have hdg := dsDomGenBase_eq b L vCap eCap
  have hpi : dsEdgeDomGenBase b L vCap eCap + (L + 1) * eCap = dsPiPtrBase b L vCap eCap := rfl
  have hrh : dsRevGenBase b L vCap eCap + (L + 1) * vCap = dsRevHeadBase b L vCap eCap := rfl
  have hed : dsDomGenBase b L vCap eCap + (L + 1) = dsEdgeDomGenBase b L vCap eCap := rfl
  have hpr : dsPiPtrBase b L vCap eCap + (L + 1) * eCap = dsRevGenBase b L vCap eCap := rfl
  have hgh : dsGPtr b + dynGraphSize vCap eCap = dsHPtr b vCap eCap := rfl
  have hha : dsHPtr b vCap eCap + dynGraphSize vCap eCap = dsAuxPtr b vCap eCap := rfl
  have ham : dsAuxPtr b vCap eCap + dynGraphSize vCap eCap = dsMinHBase b vCap eCap := rfl
  have hm1 := dsMinHBase_eq b vCap eCap
  refine ⟨by omega, by omega, by omega, by omega, by omega⟩

private lemma ins_frame_of_lt_minH {b L vCap eCap addr : ℕ}
    (hlt : addr < dsMinHBase b vCap eCap) :
    (∀ e < eCap, addr ≠ dsMinHBase b vCap eCap + e) ∧
    addr ≠ dsHHeadBase b vCap eCap ∧ addr ≠ dsHDegDummyBase b L vCap eCap ∧
    (∀ e < eCap, addr ≠ dsHPrevBase b vCap eCap + e) ∧
    (∀ e < eCap, addr ≠ dsHNextBase b vCap eCap + e) := by
  obtain ⟨_, _, _, h1, h2, h3, h4, _, _, _⟩ := dsCore_base_chain b L vCap eCap
  exact ⟨fun _ _ => by omega, by omega, by omega, fun _ _ => by omega, fun _ _ => by omega⟩

private lemma ins_frame_of_ge_dom {b L vCap eCap addr : ℕ}
    (hge : dsDomGenBase b L vCap eCap ≤ addr) :
    (addr < dsHPtr b vCap eCap ∨ dsHPtr b vCap eCap + dynGraphSize vCap eCap ≤ addr) ∧
    (∀ e < eCap, addr ≠ dsMinHBase b vCap eCap + e) ∧
    addr ≠ dsHHeadBase b vCap eCap ∧ addr ≠ dsHDegDummyBase b L vCap eCap ∧
    (∀ e < eCap, addr ≠ dsHPrevBase b vCap eCap + e) ∧
    (∀ e < eCap, addr ≠ dsHNextBase b vCap eCap + e) := by
  obtain ⟨_, hha, hami, h1, h2, h3, h4, h5, _, _⟩ := dsCore_base_chain b L vCap eCap
  exact ⟨Or.inr (by omega), fun _ _ => by omega, by omega, by omega,
    fun _ _ => by omega, fun _ _ => by omega⟩

lemma lw_frame_of_lt_dom {b L vCap eCap heapSp ret addr : ℕ}
    (hfix_sp : b + dsFixedSize L vCap eCap ≤ heapSp)
    (hlt : addr < dsDomGenBase b L vCap eCap) (hne : addr ≠ b + dsGenOff) :
    dsLevelWalksFrameCond L vCap eCap b 0 heapSp ret addr := by
  obtain ⟨_, _, _, _, _, _, _, _, hdom_me, hme_fix⟩ := dsCore_base_chain b L vCap eCap
  obtain ⟨_, _, _, _, h_ed, _, h_rg, _, h_vs, _⟩ := dsCore_postIns_bounds b L vCap eCap
  have hge_pi : dsDomGenBase b L vCap eCap ≤ dsPiPtrBase b L vCap eCap := by
    have : dsEdgeDomGenBase b L vCap eCap ≤ dsPiPtrBase b L vCap eCap := by simp [dsPiPtrBase]
    omega
  have hge_rh : dsDomGenBase b L vCap eCap ≤ dsRevHeadBase b L vCap eCap := by
    have : dsRevGenBase b L vCap eCap ≤ dsRevHeadBase b L vCap eCap := by simp [dsRevHeadBase]
    omega
  refine ⟨hne, by omega, fun _ _ => by omega, fun _ _ => by omega,
    fun _ _ => by omega, fun _ _ => by omega, fun _ _ => by omega, Or.inl (by omega)⟩

private lemma lw_frame_of_ge_fix {b L vCap eCap heapSp ret addr : ℕ}
    (hge : b + dsFixedSize L vCap eCap ≤ addr) (hout : addr < heapSp ∨ ret ≤ addr) :
    dsLevelWalksFrameCond L vCap eCap b 0 heapSp ret addr := by
  have hf := dsFixedSize_add b L vCap eCap
  have hm := dsMEmbTempBase_eq b L vCap eCap
  have hrev := dsRevGenBase_eq b L vCap eCap
  have hpi : dsPiPtrBase b L vCap eCap + (L + 1) * eCap = dsRevGenBase b L vCap eCap := rfl
  have hed : dsEdgeDomGenBase b L vCap eCap + (L + 1) * eCap = dsPiPtrBase b L vCap eCap := rfl
  have hdom : dsDomGenBase b L vCap eCap + (L + 1) = dsEdgeDomGenBase b L vCap eCap := rfl
  have hg : b + dsGenOff < b + dsFixedSize L vCap eCap := by
    have := dsCore_postIns_bounds b L vCap eCap
    have := dsCore_base_chain b L vCap eCap
    omega
  refine ⟨by omega, by omega, fun e he => ?_, fun e he => ?_, fun v hv => ?_, fun v hv => ?_,
    fun v hv => ?_, hout⟩ <;>
    { try simp only [Nat.zero_mul, Nat.add_zero]
      have hvs := dsVStampBase_eq b L vCap eCap
      have hrh := dsRevHeadBase_eq b L vCap eCap
      omega }

private lemma sc_frame_of_lt_vstamp {b L vCap eCap mEmbPtr heapPtr ret addr : ℕ}
    (hfix_mep : b + dsFixedSize L vCap eCap ≤ mEmbPtr) (hmep_hp : mEmbPtr ≤ heapPtr)
    (hlt : addr < dsVStampBase b L vCap eCap) :
    dsShortcutFrameCond L vCap eCap b eCap mEmbPtr heapPtr ret addr := by
  have hvsm : dsVStampBase b L vCap eCap + vCap + 2 * eCap = dsMEmbTempBase b L vCap eCap := by
    simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase]; omega
  have hf := dsFixedSize_add b L vCap eCap
  refine ⟨fun v _ => by omega, fun e _ => by omega, Or.inl (by omega)⟩

lemma ins_agree_range {memIns memSP : ℕ → ℕ} {b L vCap eCap : ℕ}
    (hfrI : ∀ addr,
      (addr < dsHPtr b vCap eCap ∨ dsHPtr b vCap eCap + dynGraphSize vCap eCap ≤ addr) →
      (∀ e < eCap, addr ≠ dsMinHBase b vCap eCap + e) →
      addr ≠ dsHHeadBase b vCap eCap → addr ≠ dsHDegDummyBase b L vCap eCap →
      (∀ e < eCap, addr ≠ dsHPrevBase b vCap eCap + e) →
      (∀ e < eCap, addr ≠ dsHNextBase b vCap eCap + e) →
      memIns addr = memSP addr) :
    (∀ addr, addr < dsHPtr b vCap eCap → memIns addr = memSP addr) ∧
    (∀ addr, dsAuxPtr b vCap eCap ≤ addr → addr < dsMinHBase b vCap eCap → memIns addr = memSP addr) ∧
    (∀ addr, dsDomGenBase b L vCap eCap ≤ addr → memIns addr = memSP addr) := by
  obtain ⟨_, hha, ham, _, _, _, _, _, _, _⟩ := dsCore_base_chain b L vCap eCap
  refine ⟨fun addr hlt => ?_, fun addr hlo hhi => ?_, fun addr hge => ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := ins_frame_of_lt_minH (b := b) (L := L) (vCap := vCap)
      (eCap := eCap) (addr := addr) (by omega)
    exact hfrI addr (Or.inl hlt) h1 h2 h3 h4 h5
  · obtain ⟨h1, h2, h3, h4, h5⟩ := ins_frame_of_lt_minH hhi
    exact hfrI addr (Or.inr (by omega)) h1 h2 h3 h4 h5
  · obtain ⟨h0, h1, h2, h3, h4, h5⟩ := ins_frame_of_ge_dom hge
    exact hfrI addr h0 h1 h2 h3 h4 h5

private lemma postIns_frame_agree {memFinal memSC memCA memIns memSP mem1 mem0 : ℕ → ℕ}
    {L vCap eCap b heapPtr mEmbOutPtr heapSp heapSC retFinal addr : ℕ}
    (hmep_hp : heapPtr ≤ mEmbOutPtr) (hsp_mep : mEmbOutPtr + eCap ≤ heapSp)
    (hhp_sp : heapPtr ≤ heapSp) (hsp_sc : heapSp ≤ heapSC) (hsc_ret : heapSC ≤ retFinal)
    (hzSP : ZeroFrom memSP heapSp) (hz0 : ZeroFrom mem0 heapPtr)
    (hfrLW : ∀ addr, dsLevelWalksFrameCond L vCap eCap b 0 heapSC retFinal addr →
      memFinal addr = memSC addr)
    (hfrSC : ∀ addr, dsShortcutFrameCond L vCap eCap b eCap mEmbOutPtr heapSp heapSC addr →
      memSC addr = memCA addr)
    (hfrCA : ∀ addr, addr < dsAuxPtr b vCap eCap ∨ dsAuxPtr b vCap eCap + dynGraphSize vCap eCap ≤ addr →
      memCA addr = memIns addr)
    (hfrI : ∀ addr,
      (addr < dsHPtr b vCap eCap ∨ dsHPtr b vCap eCap + dynGraphSize vCap eCap ≤ addr) →
      (∀ e < eCap, addr ≠ dsMinHBase b vCap eCap + e) →
      addr ≠ dsHHeadBase b vCap eCap → addr ≠ dsHDegDummyBase b L vCap eCap →
      (∀ e < eCap, addr ≠ dsHPrevBase b vCap eCap + e) →
      (∀ e < eCap, addr ≠ dsHNextBase b vCap eCap + e) →
      memIns addr = memSP addr)
    (hfrSP : ∀ addr, addr < heapPtr →
      (addr < dsAuxPtr b vCap eCap ∨ dsAuxPtr b vCap eCap + dynGraphSize vCap eCap ≤ addr) →
      (addr < dsMEmbTempBase b L vCap eCap ∨ dsMEmbTempBase b L vCap eCap + eCap ≤ addr) →
      memSP addr = mem1 addr)
    (hfr1 : ∀ addr, addr < dsHPtr b vCap eCap ∨
        dsHPtr b vCap eCap + dynGraphSize vCap eCap ≤ addr →
      mem1 addr = mem0 addr)
    (hfc : dsInitCoreFrameCond L vCap eCap b heapPtr retFinal addr) :
    memFinal addr = mem0 addr := by
  have hfc_lw := dsInitCoreFrameCond_to_lw (h1 := heapSC) (by omega) hfc
  have hfc_sc : dsShortcutFrameCond L vCap eCap b eCap mEmbOutPtr heapSp heapSC addr := by
    refine ⟨hfc.2.2.2.2.2.2.2.2.2.2.2.2.1, fun e he => ?_, ?_⟩
    · rcases hfc.2.2.2.2.2.2.2.2.2.2.2.2.2.2 with hlt | hge <;> omega
    · rcases hfc.2.2.2.2.2.2.2.2.2.2.2.2.2.2 with hlt | hge
      · exact Or.inl (lt_of_lt_of_le hlt hhp_sp)
      · exact Or.inr (le_trans hsc_ret hge)
  obtain ⟨_, hha, _⟩ := dsCore_base_chain b L vCap eCap
  have hca_cond : addr < dsAuxPtr b vCap eCap ∨ dsAuxPtr b vCap eCap + dynGraphSize vCap eCap ≤ addr := by
    rcases hfc.2.1 with h | h <;> [left; right] <;> omega
  have hh_cond : addr < dsHPtr b vCap eCap ∨ dsHPtr b vCap eCap + dynGraphSize vCap eCap ≤ addr := by
    rcases hfc.2.1 with h | h <;> [left; right] <;> omega
  rw [hfrLW addr hfc_lw, hfrSC addr hfc_sc, hfrCA addr hca_cond,
    hfrI addr hh_cond hfc.2.2.1 hfc.2.2.2.1 hfc.2.2.2.2.1 hfc.2.2.2.2.2.1 hfc.2.2.2.2.2.2.1]
  rcases hfc.2.2.2.2.2.2.2.2.2.2.2.2.2.2 with hlt | hge
  · have hmemb : addr < dsMEmbTempBase b L vCap eCap ∨ dsMEmbTempBase b L vCap eCap + eCap ≤ addr := by
      by_cases hm : addr < dsMEmbTempBase b L vCap eCap
      · exact Or.inl hm
      · right
        by_contra hlt_e
        exact absurd (Nat.add_sub_of_le (le_of_not_gt hm)).symm
          (hfc.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (addr - dsMEmbTempBase b L vCap eCap) (by omega))
    rw [hfrSP addr hlt hca_cond hmemb]
    exact hfr1 addr hh_cond
  · rw [hzSP addr (by omega), hz0 addr (by omega)]

private lemma dsInitCore_lwRet_cont {w L vCap eCap b heapPtr mEmbOutPtr heapSp retSC heapMax : ℕ}
    {G H₀ : MGraph} {emb : MinCostFlow.Embedding} {eL_G : List ℕ}
    {mem0 mem1 memSP memIns memCA memSC : ℕ → ℕ}
    {buck0 : List ℕ}
    {p : Program} {bLW bRev bOps : ℕ}
    (hpLW : p.HasAt bLW (levelWalkProcs bOps bRev))
    (hpRev : p.HasAt bRev (revProcs bOps bRev))
    (hpOps : p.HasAt bOps dgOpsProcs)
    (hw16 : 16 ≤ 2 ^ w) (hb1 : 1 ≤ b)
    (hfix : b + dsFixedSize L vCap eCap ≤ heapPtr) (hheap_sp : heapPtr ≤ heapSp)
    (hmep_lo : heapPtr ≤ mEmbOutPtr) (hmep_hi : mEmbOutPtr + eCap ≤ heapSp)
    (hsc_ge : heapSp ≤ retSC)
    (hsc_bnd : retSC ≤ heapSp + 7 * ∑ e ∈ G.E, ((emb e).length + 1))
    (hsp_max : heapSp + 9 * (∑ e ∈ G.E, ((emb e).length + 1)) ≤ heapMax)
    (hmax_w : heapMax < 2 ^ w)
    (hz0 : ZeroFrom mem0 heapPtr) (hzSP : ZeroFrom memSP heapSp)
    (hL0 : mem0 (b + dsLOff) = L) (hvC0 : mem0 (b + dsVCapOff) = vCap)
    (heC0 : mem0 (b + dsECapOff) = eCap)
    (hgen_w : mem0 (b + dsGenOff) + 1 + G.m < 2 ^ w)
    (hrevg0 : ∀ v < vCap, mem0 (dsRevGenBase b L vCap eCap + v) ≤ mem0 (b + dsGenOff))
    (hedg0 : ∀ e < eCap, mem0 (dsEdgeDomGenBase b L vCap eCap + e) ≤ mem0 (b + dsGenOff))
    (hG_v : ∀ v ∈ G.V, v < vCap) (hG_e : ∀ e ∈ G.E, e < eCap) (hG_val : G.IsValid)
    (hH_val : H₀.IsValid) (hGV_sub : G.V ⊆ H₀.V) (hHV_v : ∀ v ∈ H₀.V, v < vCap) (hHE_sub : H₀.E ⊆ G.E)
    (heL_len : eL_G.length = G.m) (heL_nd : eL_G.Nodup) (heL_mem : ∀ e, e ∈ eL_G ↔ e ∈ G.E)
    (heL_at_CA : ListAt memCA (dgEListBase (dsGPtr b) vCap eCap) eL_G)
    (hG_CA : DynGraphAt memCA (dsGPtr b) vCap eCap G)
    (hH_CA : DynGraphAt memCA (dsHPtr b vCap eCap) vCap eCap H₀)
    (hAux_CA : DynGraphAt memCA (dsAuxPtr b vCap eCap) vCap eCap emptyMGraph)
    (hminI : ∀ e < eCap, (memIns (dsMinHBase b vCap eCap + e) = 0 ↔ e ∉ H₀.E) ∧
      (e ∈ H₀.E → memIns (dsMinHBase b vCap eCap + e) = 1))
    (hdllI : IsDoublyLinkedList memIns (dsHPrevBase b vCap eCap) (dsHNextBase b vCap eCap)
      (dsHHeadBase b vCap eCap) eCap buck0)
    (hdegI : memIns (dsHDegDummyBase b L vCap eCap) = buck0.length)
    (hbuckI : ∀ e, e ∈ buck0 ↔ e ∈ H₀.E)
    (hEmb_core : MinCostFlow.Embedding.IsEmbedding (fun e => shortcutWalk G (G.tail e) (emb e)) G H₀)
    (hvstSC : ∀ v < vCap, memSC (dsVStampBase b L vCap eCap + v) ≤ memCA (b + dsGenOff))
    (hWalksSC : ∀ e ∈ eL_G,
      let pi := shortcutWalk G (G.tail e) (emb e)
      heapSp ≤ memSC (mEmbOutPtr + e) ∧
      memSC (mEmbOutPtr + e) + 1 + 2 * pi.length ≤ retSC ∧
      MWalkAt memSC (memSC (mEmbOutPtr + e)) pi)
    (hfrSC : ∀ addr, dsShortcutFrameCond L vCap eCap b eCap mEmbOutPtr heapSp retSC addr →
      memSC addr = memCA addr)
    (hfrCA : ∀ addr, addr < dsAuxPtr b vCap eCap ∨ dsAuxPtr b vCap eCap + dynGraphSize vCap eCap ≤ addr →
      memCA addr = memIns addr)
    (hfrI : ∀ addr,
      (addr < dsHPtr b vCap eCap ∨ dsHPtr b vCap eCap + dynGraphSize vCap eCap ≤ addr) →
      (∀ e < eCap, addr ≠ dsMinHBase b vCap eCap + e) →
      addr ≠ dsHHeadBase b vCap eCap → addr ≠ dsHDegDummyBase b L vCap eCap →
      (∀ e < eCap, addr ≠ dsHPrevBase b vCap eCap + e) →
      (∀ e < eCap, addr ≠ dsHNextBase b vCap eCap + e) →
      memIns addr = memSP addr)
    (hfrSP : ∀ addr, addr < heapPtr →
      (addr < dsAuxPtr b vCap eCap ∨ dsAuxPtr b vCap eCap + dynGraphSize vCap eCap ≤ addr) →
      (addr < dsMEmbTempBase b L vCap eCap ∨ dsMEmbTempBase b L vCap eCap + eCap ≤ addr) →
      memSP addr = mem1 addr)
    (hfr1 : ∀ addr, addr < dsHPtr b vCap eCap ∨
        dsHPtr b vCap eCap + dynGraphSize vCap eCap ≤ addr →
      mem1 addr = mem0 addr)
    (hAgree_CA_0 : ∀ addr, (addr < dsHPtr b vCap eCap ∨ dsDomGenBase b L vCap eCap ≤ addr) →
      addr < dsMEmbTempBase b L vCap eCap → memCA addr = mem0 addr)
    (hAgree_CA_ge_fix : ∀ addr, b + dsFixedSize L vCap eCap ≤ addr → memCA addr = memSP addr)
    (stSC : State) (ω : ℕ → Bool) {k T : ℕ}
    (hmSC : stSC.mem = memSC)
    (hr0 : stSC.regs 0 = b) (hr11 : stSC.regs 11 = G.m)
    (hr12 : stSC.regs 12 = dgEListBase (dsGPtr b) vCap eCap)
    (hr15 : stSC.regs 15 = retSC) (hr17 : stSC.regs 17 = mEmbOutPtr)
    (hkT : k + (400 * (∑ e ∈ G.E, (emb e).length) + 620 * G.m + 240) ≤ T) :
    let Pi₀ : MinCostFlow.Embedding := fun e => shortcutWalk G (G.tail e) (emb e)
    ∃ o st' c,
      Runs w p ω
        (.call 1 (bLW + lwIdxSetLevelWalks) [.reg 0, .const 0, .reg 12, .reg 11, .reg 17, .reg 15] ;;
         .ret (.reg 1)) stSC o st' c ∧
      (∃ ret, o = .returned ret ∧
        heapPtr ≤ ret ∧ ret ≤ heapMax ∧ ZeroFrom st'.mem ret ∧
        st'.mem (b + dsGenOff) = mem0 (b + dsGenOff) + 1 + G.m ∧
        st'.mem (dsDomGenBase b L vCap eCap) = mem0 (b + dsGenOff) + 1 ∧
        (∀ v < vCap, st'.mem (dsVStampBase b L vCap eCap + v) ≤ st'.mem (b + dsGenOff)) ∧
        (∀ e < eCap, st'.mem (dsEdgeDomGenBase b L vCap eCap + e) ≤ st'.mem (b + dsGenOff)) ∧
        DynGraphAt st'.mem (dsHPtr b vCap eCap) vCap eCap H₀ ∧
        DynGraphAt st'.mem (dsAuxPtr b vCap eCap) vCap eCap emptyMGraph ∧
        (∀ e < eCap,
          (st'.mem (dsMinHBase b vCap eCap + e) = 0 ↔ e ∉ H₀.E) ∧
          (e ∈ H₀.E → st'.mem (dsMinHBase b vCap eCap + e) = 1)) ∧
        (∃ buck0 : List ℕ,
          IsDoublyLinkedList st'.mem (dsHPrevBase b vCap eCap) (dsHNextBase b vCap eCap)
            (dsHHeadBase b vCap eCap) eCap buck0 ∧
          st'.mem (dsHDegDummyBase b L vCap eCap) = buck0.length ∧
          (∀ e, e ∈ buck0 ↔ e ∈ H₀.E)) ∧
        (∀ e < eCap,
          (0 < st'.mem (dsDomGenBase b L vCap eCap) ∧
           st'.mem (dsEdgeDomGenBase b L vCap eCap + e) = st'.mem (dsDomGenBase b L vCap eCap)) ↔
            e ∈ G.E) ∧
        (∀ e ∈ G.E,
          let ptr := st'.mem (dsPiPtrBase b L vCap eCap + e)
          MWalkAt st'.mem ptr (Pi₀ e) ∧ heapPtr ≤ ptr ∧ ptr + (mWalkEncode (Pi₀ e)).length ≤ ret) ∧
        (∃ rev0 : ℕ → List ℕ, ∀ v < vCap,
          st'.mem (dsRevGenBase b L vCap eCap + v) ≤ st'.mem (b + dsGenOff) ∧
          (rev0 v).Nodup ∧
          (∀ e, e ∈ rev0 v ↔ e ∈ G.E ∧ v ∈ H₀.walkVertices (G.tail e) (Pi₀ e)) ∧
          (if 0 < st'.mem (dsDomGenBase b L vCap eCap) ∧
              st'.mem (dsRevGenBase b L vCap eCap + v) = st'.mem (dsDomGenBase b L vCap eCap)
           then LinkedListIn (fun a => heapPtr ≤ a ∧ a < ret) st'.mem
                  (st'.mem (dsRevHeadBase b L vCap eCap + v)) (rev0 v)
           else rev0 v = [])) ∧
        ∀ addr, dsInitCoreFrameCond L vCap eCap b heapPtr ret addr → st'.mem addr = mem0 addr) ∧
      k + c ≤ T := by
  intro Pi₀
  subst hmSC
  obtain ⟨hgh, hha, ham, hm_n, hn_p, hp_h, hh_d, hd_dm, hdm_me, hme_fix⟩ :=
    dsCore_base_chain b L vCap eCap
  obtain ⟨ho_g, ho_l, ho_v, ho_e, h_ed, hed_me, h_rg, hrg_me, h_vs, hvs_me⟩ :=
    dsCore_postIns_bounds b L vCap eCap
  obtain ⟨hg_vs, hdm_ed, hed_vs, hrg_vs, _⟩ := dsCore_vstamp_order b L vCap eCap
  have hsp_w : heapSp < 2 ^ w := by omega
  have hdsG_lt : dsGPtr b + dynGraphSize vCap eCap < 2 ^ w := by omega
  have hdg_elist_lt : dgEListBase (dsGPtr b) vCap eCap + eCap ≤ dsHPtr b vCap eCap := by
    simp only [dgEListBase, dsHPtr, dynGraphSize]; omega
  have hGm_le_eCap : G.m ≤ eCap := by
    simpa [MGraph.m] using Finset.card_le_card (fun e he => Finset.mem_range.mpr (hG_e e he))
  have hsum_pi_le : ∑ e ∈ G.E, ((Pi₀ e).length + 1) ≤ ∑ e ∈ G.E, ((emb e).length + 1) :=
    Finset.sum_le_sum fun e _ => Nat.add_le_add_right (shortcutWalk_length_le G (emb e) (G.tail e)) 1
  have hsum_len : (eL_G.map fun e => (Pi₀ e).length + 1).sum = ∑ e ∈ G.E, ((Pi₀ e).length + 1) :=
    sum_eL_eq_finset heL_nd heL_mem _
  have hsum_len0 : (eL_G.map fun e => (Pi₀ e).length).sum = ∑ e ∈ G.E, (Pi₀ e).length :=
    sum_eL_eq_finset heL_nd heL_mem _
  have hsum_pi0_le : ∑ e ∈ G.E, (Pi₀ e).length ≤ ∑ e ∈ G.E, (emb e).length :=
    Finset.sum_le_sum fun e _ => shortcutWalk_length_le G (emb e) (G.tail e)
  have hAgree_SC_0 : ∀ addr, (addr < dsHPtr b vCap eCap ∨ dsDomGenBase b L vCap eCap ≤ addr) →
      addr < dsVStampBase b L vCap eCap → stSC.mem addr = mem0 addr := fun addr h1a h2a =>
    (hfrSC addr (sc_frame_of_lt_vstamp (by omega) (by omega) h2a)).trans
      (hAgree_CA_0 addr h1a (by omega))
  have hAgree_SC_dom : ∀ addr, dsHPtr b vCap eCap ≤ addr → addr < dsDomGenBase b L vCap eCap →
      stSC.mem addr = memCA addr := fun addr hlo hhi =>
    hfrSC addr (sc_frame_of_lt_vstamp (by omega) (by omega) (by omega))
  have hAgree_SC_ge_sc : ∀ addr, retSC ≤ addr → stSC.mem addr = memSP addr := fun addr ha =>
    (hfrSC addr ⟨fun v _ => by omega, fun e _ => by omega, Or.inr ha⟩).trans
      (hAgree_CA_ge_fix addr (by omega))
  have hG_SC : DynGraphAt stSC.mem (dsGPtr b) vCap eCap G :=
    hG_CA.of_agree fun addr h1 h2 =>
      hfrSC addr (sc_frame_of_lt_vstamp (by omega) (by omega) (by omega))
  have hH_SC : DynGraphAt stSC.mem (dsHPtr b vCap eCap) vCap eCap H₀ :=
    hH_CA.of_agree fun addr h1 h2 => hAgree_SC_dom addr h1 (by omega)
  have hAux_SC : DynGraphAt stSC.mem (dsAuxPtr b vCap eCap) vCap eCap emptyMGraph :=
    hAux_CA.of_agree fun addr h1 h2 => hAgree_SC_dom addr (by omega) (by omega)
  have heL_at_SC : ListAt stSC.mem (dgEListBase (dsGPtr b) vCap eCap) eL_G := fun i hi =>
    (hfrSC _ (sc_frame_of_lt_vstamp (by omega) (by omega) (by rw [heL_len] at hi; omega))).trans
      (heL_at_CA i hi)
  have hmax_lw : retSC + 2 * (eL_G.map fun e => (Pi₀ e).length + 1).sum < 2 ^ w := by
    rw [hsum_len]
    have h2 : 2 * ∑ e ∈ G.E, ((Pi₀ e).length + 1) ≤ 2 * ∑ e ∈ G.E, ((emb e).length + 1) :=
      Nat.mul_le_mul_left 2 hsum_pi_le
    exact lt_of_le_of_lt (Nat.add_le_add hsc_bnd h2) (by omega)
  have hsc_fix : b + dsFixedSize L vCap eCap ≤ retSC :=
    le_trans (le_trans hfix hheap_sp) hsc_ge
  have heL_lt_w : dgEListBase (dsGPtr b) vCap eCap + eL_G.length < 2 ^ w := by
    rw [heL_len]
    exact lt_of_le_of_lt (Nat.add_le_add_left hGm_le_eCap _) (by omega)
  have hmep_lt_w : mEmbOutPtr + eCap < 2 ^ w := lt_of_le_of_lt hmep_hi hsp_w
  have hpre_lw : (dsSetLevelWalksContract w L vCap eCap b 0 G H₀ eL_G Pi₀ (fun _ => False)).pre
      [b, 0, dgEListBase (dsGPtr b) vCap eCap, G.m, mEmbOutPtr, retSC] stSC.mem := by
    refine ⟨dgEListBase (dsGPtr b) vCap eCap, mEmbOutPtr, retSC, by simp [heL_len], hw16, hb1,
      Nat.zero_le _, hsc_fix, hmax_lw, heL_lt_w, hmep_lt_w,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ h => False.elim h, ?_, ?_, heL_nd, heL_at_SC,
      hG_SC, hG_val, hG_v, hG_e, hH_SC, hH_val, hGV_sub, hHV_v, fun e he => hG_e e (hHE_sub he), ?_⟩
    · rw [hAgree_SC_0 _ (Or.inl (by omega)) (by omega), hL0]
    · rw [hAgree_SC_0 _ (Or.inl (by omega)) (by omega), hvC0]
    · rw [hAgree_SC_0 _ (Or.inl (by omega)) (by omega), heC0]
    · rw [hAgree_SC_0 _ (Or.inl (by omega)) (by omega), heL_len]; exact hgen_w
    · intro v hv
      have hgen_sc : stSC.mem (b + dsGenOff) = memCA (b + dsGenOff) :=
        hfrSC _ (sc_frame_of_lt_vstamp (by omega) (by omega) (by omega))
      rw [hgen_sc]
      exact hvstSC v hv
    · intro e he
      simp only [Nat.zero_mul, Nat.add_zero]
      rw [hAgree_SC_0 _ (Or.inr (by omega)) (by omega), hAgree_SC_0 _ (Or.inl (by omega)) (by omega)]
      exact hedg0 e he
    · intro v hv
      simp only [Nat.zero_mul, Nat.add_zero]
      rw [hAgree_SC_0 _ (Or.inr (by omega)) (by omega), hAgree_SC_0 _ (Or.inl (by omega)) (by omega)]
      exact hrevg0 v hv
    · intro k hk
      have hdg_elist_ge : dsGPtr b ≤ dgEListBase (dsGPtr b) vCap eCap := by
        simp only [dgEListBase]; omega
      have _ := hGm_le_eCap
      exact lw_frame_of_lt_dom hsc_fix (by rw [heL_len] at hk; omega) (by omega)
    · intro e he
      have he_c := hG_e e ((heL_mem e).mp he)
      exact lw_frame_of_ge_fix (by omega) (Or.inl (by omega))
    · intro e he
      have heG : e ∈ G.E := (heL_mem e).mp he
      obtain ⟨hpi_ge, hpi_le, hmw_sc⟩ := hWalksSC e he
      have hmwe : (mWalkEncode (Pi₀ e)).length = 1 + 2 * (Pi₀ e).length := mWalkEncode_length _
      refine ⟨heG, hEmb_core.2 e heG, hmw_sc,
        le_trans (le_trans hfix hheap_sp) hpi_ge,
        by rw [hmwe, ← Nat.add_assoc]; exact hpi_le⟩
  refine runs_seq_call_le (dsSetLevelWalks_meetsContract hpLW hpRev hpOps)
    (by simp [evalArgs, Expr.eval, hr0, hr11, hr12, hr15, hr17])
    (fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    hpre_lw ?_
  intro retFinal memFinal _ ⟨_, _, _, hEqLW, hret_ge, hret_le, hgenF, hdomF, hvstF,
    hedgLeF, hedgF, hpiF, ⟨rev0, hrev0⟩, hfrLW⟩
  simp only [List.cons.injEq, true_and, and_true] at hEqLW
  rcases hEqLW with ⟨_, _, rfl, _, rfl, rfl⟩
  have hret_bnd : retFinal ≤ heapMax := by rw [hsum_len] at hret_le; omega
  have hlw_dom : ∀ addr, dsHPtr b vCap eCap ≤ addr → addr < dsDomGenBase b L vCap eCap →
      memFinal addr = stSC.mem addr := fun addr hlo hhi =>
    hfrLW addr (lw_frame_of_lt_dom hsc_fix hhi (by omega))
  have hmin_dom : ∀ addr, dsMinHBase b vCap eCap ≤ addr → addr < dsDomGenBase b L vCap eCap →
      memFinal addr = memIns addr := fun addr hlo hhi =>
    (hlw_dom addr (by omega) hhi).trans
      ((hAgree_SC_dom addr (by omega) hhi).trans (hfrCA addr (Or.inr (by omega))))
  have hH_final : DynGraphAt memFinal (dsHPtr b vCap eCap) vCap eCap H₀ :=
    hH_SC.of_agree fun addr h1 h2 => hlw_dom addr h1 (by omega)
  have hAux_final : DynGraphAt memFinal (dsAuxPtr b vCap eCap) vCap eCap emptyMGraph :=
    hAux_SC.of_agree fun addr h1 h2 => hlw_dom addr (by omega) (by omega)
  have hzero_final : ZeroFrom memFinal retFinal := fun addr ha => by
    rw [hfrLW addr (lw_frame_of_ge_fix (by omega) (Or.inr ha)), hAgree_SC_ge_sc addr (by omega)]
    exact hzSP addr (by omega)
  refine runs_ret_le (by simp [Expr.eval]) ⟨retFinal, rfl, by omega, hret_bnd, hzero_final,
    ?_, ?_, hvstF, ?_, hH_final, hAux_final, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_
  · dsimp only; rw [hgenF, heL_len, hAgree_SC_0 _ (Or.inl (by omega)) (by omega)]
  · dsimp only; simp only [Nat.add_zero] at hdomF
    rw [hdomF, hAgree_SC_0 _ (Or.inl (by omega)) (by omega)]
  · intro e he; dsimp only
    simpa [Nat.zero_mul, Nat.add_zero] using hedgLeF e he
  · intro e he; dsimp only
    rw [hmin_dom _ (by omega) (by omega)]
    exact hminI e he
  · refine ⟨buck0, hdllI.of_agree (hmin_dom _ (by omega) (by omega))
      (fun e he => hmin_dom _ (by omega) (by have := hdllI.2.1 e he; omega))
      (fun e he => hmin_dom _ (by omega) (by have := hdllI.2.1 e he; omega)), ?_, hbuckI⟩
    dsimp only; rw [← hdegI]; exact hmin_dom _ (by omega) (by omega)
  · intro e he; dsimp only; simpa [Nat.zero_mul, Nat.add_zero, heL_mem e] using hedgF e he
  · intro e he; dsimp only
    have heL_m : e ∈ eL_G := (heL_mem e).mpr he
    obtain ⟨hpi_eq, hmw⟩ := hpiF e heL_m
    obtain ⟨hpi_ge, hpi_le, _⟩ := hWalksSC e heL_m
    have hmw_len : (mWalkEncode (Pi₀ e)).length = 1 + 2 * (Pi₀ e).length := mWalkEncode_length _
    have hlen_pi : (Pi₀ e).length = (shortcutWalk G (G.tail e) (emb e)).length := rfl
    simp only [Nat.zero_mul, Nat.add_zero] at hpi_eq hmw ⊢
    rw [hpi_eq] at hmw ⊢
    rw [hmw_len, hlen_pi]
    exact ⟨hmw, by omega, by omega⟩
  · refine ⟨rev0, fun v hv => ?_⟩
    rcases hrev0 v hv with ⟨hrg, hnd, hmem_rev, hll⟩
    dsimp only at hrg hmem_rev hll ⊢
    simp only [Nat.zero_mul, Nat.add_zero] at hrg hmem_rev hll ⊢
    refine ⟨hrg, hnd, fun e => ?_, ?_⟩
    · rw [hmem_rev e, heL_mem e]
    · split_ifs at hll ⊢ with hc
      · exact hll.mono fun _ ha => by rcases ha with h | h; exact False.elim h; omega
      · exact hll
  · intro addr hfc; dsimp only
    exact postIns_frame_agree hmep_lo hmep_hi hheap_sp hsc_ge hret_ge hzSP hz0
      hfrLW hfrSC hfrCA hfrI hfrSP hfr1 hfc
  · simp only [dsSetLevelWalksContract, argsSize, Expr.size]
    rw [hsum_len0, heL_len]
    have _ := hsum_pi0_le
    have _ := hkT
    omega

lemma dsInitCore_postIns_triple {w L vCap eCap b heapPtr mEmbOutPtr heapSp heapMax : ℕ}
    {G H₀ A : MGraph} {emb : MinCostFlow.Embedding} {mem0 mem1 memSP : ℕ → ℕ}
    {p : Program} {bOps bEdge bPhase bLW bRev : ℕ}
    (hpOps : p.HasAt bOps dgOpsProcs) (hpPhase : p.HasAt bPhase (phaseProcs bOps bEdge))
    (hpLW : p.HasAt bLW (levelWalkProcs bOps bRev)) (hpRev : p.HasAt bRev (revProcs bOps bRev))
    (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hw16 : 16 ≤ 2 ^ w) (hb1 : 1 ≤ b)
    (hfix : b + dsFixedSize L vCap eCap ≤ heapPtr) (hheap_sp : heapPtr ≤ heapSp)
    (hmep_lo : heapPtr ≤ mEmbOutPtr) (hmep_hi : mEmbOutPtr + eCap ≤ heapSp)
    (hsp_max : heapSp + 9 * (∑ e ∈ G.E, ((emb e).length + 1)) ≤ heapMax)
    (hmax_w : heapMax < 2 ^ w)
    (hz0 : ZeroFrom mem0 heapPtr) (hzSP : ZeroFrom memSP heapSp)
    (hL0 : mem0 (b + dsLOff) = L) (hvC0 : mem0 (b + dsVCapOff) = vCap)
    (heC0 : mem0 (b + dsECapOff) = eCap)
    (hgen_w : mem0 (b + dsGenOff) + 1 + G.m < 2 ^ w)
    (hrevg0 : ∀ v < vCap, mem0 (dsRevGenBase b L vCap eCap + v) ≤ mem0 (b + dsGenOff))
    (hedg0 : ∀ e < eCap, mem0 (dsEdgeDomGenBase b L vCap eCap + e) ≤ mem0 (b + dsGenOff))
    (hvst0 : ∀ v < vCap, mem0 (dsVStampBase b L vCap eCap + v) ≤ mem0 (b + dsGenOff))
    (hG_v : ∀ v ∈ G.V, v < vCap) (hG_e : ∀ e ∈ G.E, e < eCap) (hG_val : G.IsValid)
    (hH_val : H₀.IsValid) (hGV_sub : G.V ⊆ H₀.V) (hHV_v : ∀ v ∈ H₀.V, v < vCap) (hHE_sub : H₀.E ⊆ G.E)
    (hG_SP : DynGraphAt memSP (dsGPtr b) vCap eCap G)
    (hAux_SP : DynGraphAt memSP (dsAuxPtr b vCap eCap) vCap eCap A)
    (hEmb_G : ∀ e ∈ G.E, G.IsWalk (G.tail e) (G.head e) (emb e))
    (hEmb_core : MinCostFlow.Embedding.IsEmbedding (fun e => shortcutWalk G (G.tail e) (emb e)) G H₀)
    (hmEmbB_SP : MEmbBounded memSP mEmbOutPtr G.E eCap emb mEmbOutPtr heapSp)
    (hmEmbLo_SP : ∀ e ∈ G.E, mEmbOutPtr + eCap ≤ memSP (mEmbOutPtr + e))
    (hfrSP : ∀ addr, addr < heapPtr →
      (addr < dsAuxPtr b vCap eCap ∨ dsAuxPtr b vCap eCap + dynGraphSize vCap eCap ≤ addr) →
      (addr < dsMEmbTempBase b L vCap eCap ∨ dsMEmbTempBase b L vCap eCap + eCap ≤ addr) →
      memSP addr = mem1 addr)
    (hfr1 : ∀ addr, addr < dsHPtr b vCap eCap ∨
        dsHPtr b vCap eCap + dynGraphSize vCap eCap ≤ addr →
      mem1 addr = mem0 addr) :
    let Pi₀ : MinCostFlow.Embedding := fun e => shortcutWalk G (G.tail e) (emb e)
    Triple w p
      (fun st => ∃ buck0 : List ℕ,
        st.regs 0 = b ∧ st.regs 2 = vCap ∧ st.regs 3 = eCap ∧
        st.regs 6 = dsGPtr b ∧ st.regs 7 = dsHPtr b vCap eCap ∧
        st.regs 8 = dsAuxPtr b vCap eCap ∧ st.regs 11 = G.m ∧
        st.regs 15 = heapSp ∧ st.regs 17 = mEmbOutPtr ∧
        DynGraphAt st.mem (dsHPtr b vCap eCap) vCap eCap H₀ ∧
        (∀ e < eCap, (st.mem (dsMinHBase b vCap eCap + e) = 0 ↔ e ∉ H₀.E) ∧
          (e ∈ H₀.E → st.mem (dsMinHBase b vCap eCap + e) = 1)) ∧
        IsDoublyLinkedList st.mem (dsHPrevBase b vCap eCap) (dsHNextBase b vCap eCap)
          (dsHHeadBase b vCap eCap) eCap buck0 ∧
        st.mem (dsHDegDummyBase b L vCap eCap) = buck0.length ∧
        (∀ e, e ∈ buck0 ↔ e ∈ H₀.E) ∧
        ∀ addr,
          (addr < dsHPtr b vCap eCap ∨ dsHPtr b vCap eCap + dynGraphSize vCap eCap ≤ addr) →
          (∀ e < eCap, addr ≠ dsMinHBase b vCap eCap + e) →
          addr ≠ dsHHeadBase b vCap eCap → addr ≠ dsHDegDummyBase b L vCap eCap →
          (∀ e < eCap, addr ≠ dsHPrevBase b vCap eCap + e) →
          (∀ e < eCap, addr ≠ dsHNextBase b vCap eCap + e) →
          st.mem addr = memSP addr)
      (.call 13 (bPhase + phaseIdxClearAux) [.reg 8] ;;
       .assign 12 (.bin .add (.bin .add (.reg 6) (.const 4))
         (.bin .add (.bin .mul (.const 7) (.reg 2)) (.reg 3))) ;;
       .call 15 (bLW + lwIdxShortcutEmb) [.reg 0, .reg 6, .reg 12, .reg 11, .reg 17, .reg 15] ;;
       .call 1 (bLW + lwIdxSetLevelWalks) [.reg 0, .const 0, .reg 12, .reg 11, .reg 17, .reg 15] ;;
       .ret (.reg 1))
      (fun o st' => ∃ ret, o = .returned ret ∧
        heapPtr ≤ ret ∧ ret ≤ heapMax ∧ ZeroFrom st'.mem ret ∧
        st'.mem (b + dsGenOff) = mem0 (b + dsGenOff) + 1 + G.m ∧
        st'.mem (dsDomGenBase b L vCap eCap) = mem0 (b + dsGenOff) + 1 ∧
        (∀ v < vCap, st'.mem (dsVStampBase b L vCap eCap + v) ≤ st'.mem (b + dsGenOff)) ∧
        (∀ e < eCap, st'.mem (dsEdgeDomGenBase b L vCap eCap + e) ≤ st'.mem (b + dsGenOff)) ∧
        DynGraphAt st'.mem (dsHPtr b vCap eCap) vCap eCap H₀ ∧
        DynGraphAt st'.mem (dsAuxPtr b vCap eCap) vCap eCap emptyMGraph ∧
        (∀ e < eCap,
          (st'.mem (dsMinHBase b vCap eCap + e) = 0 ↔ e ∉ H₀.E) ∧
          (e ∈ H₀.E → st'.mem (dsMinHBase b vCap eCap + e) = 1)) ∧
        (∃ buck0 : List ℕ,
          IsDoublyLinkedList st'.mem (dsHPrevBase b vCap eCap) (dsHNextBase b vCap eCap)
            (dsHHeadBase b vCap eCap) eCap buck0 ∧
          st'.mem (dsHDegDummyBase b L vCap eCap) = buck0.length ∧
          (∀ e, e ∈ buck0 ↔ e ∈ H₀.E)) ∧
        (∀ e < eCap,
          (0 < st'.mem (dsDomGenBase b L vCap eCap) ∧
           st'.mem (dsEdgeDomGenBase b L vCap eCap + e) = st'.mem (dsDomGenBase b L vCap eCap)) ↔
            e ∈ G.E) ∧
        (∀ e ∈ G.E,
          let ptr := st'.mem (dsPiPtrBase b L vCap eCap + e)
          MWalkAt st'.mem ptr (Pi₀ e) ∧ heapPtr ≤ ptr ∧ ptr + (mWalkEncode (Pi₀ e)).length ≤ ret) ∧
        (∃ rev0 : ℕ → List ℕ, ∀ v < vCap,
          st'.mem (dsRevGenBase b L vCap eCap + v) ≤ st'.mem (b + dsGenOff) ∧
          (rev0 v).Nodup ∧
          (∀ e, e ∈ rev0 v ↔ e ∈ G.E ∧ v ∈ H₀.walkVertices (G.tail e) (Pi₀ e)) ∧
          (if 0 < st'.mem (dsDomGenBase b L vCap eCap) ∧
              st'.mem (dsRevGenBase b L vCap eCap + v) = st'.mem (dsDomGenBase b L vCap eCap)
           then LinkedListIn (fun a => heapPtr ≤ a ∧ a < ret) st'.mem
                  (st'.mem (dsRevHeadBase b L vCap eCap + v)) (rev0 v)
           else rev0 v = [])) ∧
        ∀ addr, dsInitCoreFrameCond L vCap eCap b heapPtr ret addr → st'.mem addr = mem0 addr)
      (fun _ => 500 * A.m + 30 * A.n + 800 * (∑ e ∈ G.E, (emb e).length) + 920 * G.m + 560) := by
  intro Pi₀ st ω ⟨buck0, hr0, hr2, hr3, hr6, hr7, hr8, hr11, hr15, hr17,
    hH_Ins, hminI, hdllI, hdegI, hbuckI, hfrI⟩
  obtain ⟨hgh, hha, ham, hm_n, hn_p, hp_h, hh_d, hd_dm, hdm_me, hme_fix⟩ :=
    dsCore_base_chain b L vCap eCap
  obtain ⟨ho_g, ho_l, ho_v, ho_e, h_ed, hed_me, h_rg, hrg_me, h_vs, hvs_me⟩ :=
    dsCore_postIns_bounds b L vCap eCap
  obtain ⟨hg_vs, hdm_ed, hed_vs, hrg_vs, _⟩ := dsCore_vstamp_order b L vCap eCap
  have ⟨hfrI_lt_h, hfrI_aux, hfrI_ge_dom⟩ := ins_agree_range hfrI
  have hsp_w : heapSp < 2 ^ w := by omega
  have hdsG_lt : dsGPtr b + dynGraphSize vCap eCap < 2 ^ w := by omega
  have hAux_Ins : DynGraphAt st.mem (dsAuxPtr b vCap eCap) vCap eCap A :=
    hAux_SP.of_agree fun addr h1 h2 => hfrI_aux addr h1 (by omega)
  have ha_ltw : dsAuxPtr b vCap eCap + dynGraphSize vCap eCap < 2 ^ w := by omega
  refine runs_start_le ?_
  refine runs_seq_call_le (clearAuxGraph_meetsContract hpPhase hpEdge hpOps)
    (by simp [evalArgs, Expr.eval, hr8])
    (fun z hz => by simp at hz; subst hz; omega)
    ⟨dsAuxPtr b vCap eCap, rfl, hw16, ha_ltw, hAux_Ins⟩ ?_
  intro retCA memCA _ ⟨_, hEqCA, _, hAuxCA, hfrCA⟩
  simp only [List.cons.injEq, and_true] at hEqCA; subst hEqCA
  have h4_w : (4 : ℕ) < 2 ^ w := by omega
  have h7_w : (7 : ℕ) < 2 ^ w := by omega
  have hg4_lt : dsGPtr b + 4 < 2 ^ w := by simp only [dynGraphSize] at hdsG_lt; omega
  have h7v_lt : 7 * vCap < 2 ^ w := by simp only [dynGraphSize] at hdsG_lt; omega
  have h7ve_lt : 7 * vCap + eCap < 2 ^ w := by simp only [dynGraphSize] at hdsG_lt; omega
  have heLG_eq : dsGPtr b + 4 + (7 * vCap + eCap) = dgEListBase (dsGPtr b) vCap eCap := by
    simp only [dgEListBase]; omega
  have heLG_ltw : dgEListBase (dsGPtr b) vCap eCap < 2 ^ w := by
    simp only [dgEListBase, dynGraphSize] at hdsG_lt ⊢; omega
  refine runs_seq_assign_le (v := dgEListBase (dsGPtr b) vCap eCap)
    (by simp [Expr.eval, BinOp.eval, hr6, hr2, hr3, h4_w, h7_w, hg4_lt, h7v_lt, h7ve_lt,
      heLG_eq, heLG_ltw]) ?_
  have hG_CA : DynGraphAt memCA (dsGPtr b) vCap eCap G :=
    hG_SP.of_agree fun addr h1 h2 =>
      (hfrCA addr (Or.inl (by omega))).trans (hfrI_lt_h addr (by omega))
  have hH_CA : DynGraphAt memCA (dsHPtr b vCap eCap) vCap eCap H₀ :=
    hH_Ins.of_agree fun addr _ h2 => hfrCA addr (Or.inl h2)
  obtain ⟨eL_G, heL_len, heL_nd, heL_mem, heL_at, _⟩ := hG_CA.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsum_len_emb : (eL_G.map fun e => (emb e).length + 1).sum = ∑ e ∈ G.E, ((emb e).length + 1) :=
    sum_eL_eq_finset heL_nd heL_mem _
  have hsum_len_emb0 : (eL_G.map fun e => (emb e).length).sum = ∑ e ∈ G.E, (emb e).length :=
    sum_eL_eq_finset heL_nd heL_mem _
  have hsum_pi_le : ∑ e ∈ G.E, ((Pi₀ e).length + 1) ≤ ∑ e ∈ G.E, ((emb e).length + 1) :=
    Finset.sum_le_sum fun e _ => Nat.add_le_add_right (shortcutWalk_length_le G (emb e) (G.tail e)) 1
  have hsum_len : (eL_G.map fun e => (Pi₀ e).length + 1).sum = ∑ e ∈ G.E, ((Pi₀ e).length + 1) :=
    sum_eL_eq_finset heL_nd heL_mem _
  have hsum_len0 : (eL_G.map fun e => (Pi₀ e).length).sum = ∑ e ∈ G.E, (Pi₀ e).length :=
    sum_eL_eq_finset heL_nd heL_mem _
  have hsum_pi0_le : ∑ e ∈ G.E, (Pi₀ e).length ≤ ∑ e ∈ G.E, (emb e).length :=
    Finset.sum_le_sum fun e _ => shortcutWalk_length_le G (emb e) (G.tail e)
  have hsum_emb_split : ∑ e ∈ G.E, ((emb e).length + 1) = ∑ e ∈ G.E, (emb e).length + G.m := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]; rfl
  have hAgree_CA_0 : ∀ addr, (addr < dsHPtr b vCap eCap ∨ dsDomGenBase b L vCap eCap ≤ addr) →
      addr < dsMEmbTempBase b L vCap eCap → memCA addr = mem0 addr := fun addr h1a h2a => by
    have hca : memCA addr = st.mem addr :=
      hfrCA addr (by rcases h1a with h | h <;> [left; right] <;> omega)
    have hi : st.mem addr = memSP addr := by
      rcases h1a with h | h
      · exact hfrI_lt_h addr h
      · exact hfrI_ge_dom addr h
    have hsp : memSP addr = mem1 addr :=
      hfrSP addr (by omega) (by rcases h1a with h | h <;> [left; right] <;> omega) (Or.inl h2a)
    exact hca.trans (hi.trans (hsp.trans (hfr1 addr (by rcases h1a with h | h <;> [left; right] <;> omega))))
  have hAgree_CA_ge_fix : ∀ addr, b + dsFixedSize L vCap eCap ≤ addr → memCA addr = memSP addr :=
    fun addr ha => (hfrCA addr (Or.inr (by omega))).trans (hfrI_ge_dom addr (by omega))
  have hGm_le_eCap : G.m ≤ eCap := by
    simpa [MGraph.m] using Finset.card_le_card (fun e he => Finset.mem_range.mpr (hG_e e he))
  have hdg_elist_ge : dsGPtr b ≤ dgEListBase (dsGPtr b) vCap eCap := by
    simp only [dgEListBase]; omega
  have hdg_elist_lt : dgEListBase (dsGPtr b) vCap eCap + eCap ≤ dsHPtr b vCap eCap := by
    simp only [dgEListBase, dsHPtr, dynGraphSize]; omega
  have hsc_space_bnd : dsShortcutHeapSpace eL_G emb ≤ 7 * ∑ e ∈ G.E, ((emb e).length + 1) := by
    dsimp only [dsShortcutHeapSpace]
    rw [hsum_len_emb0, heL_len, hsum_emb_split]
  have hpre_sc : (dsShortcutEmbContract w L vCap eCap b vCap eCap eCap G eL_G emb).pre
      [b, dsGPtr b, dgEListBase (dsGPtr b) vCap eCap, G.m, mEmbOutPtr, heapSp] memCA := by
    refine ⟨dsGPtr b, dgEListBase (dsGPtr b) vCap eCap, mEmbOutPtr, heapSp,
      by simp [heL_len], hw16, hb1, by omega, by omega, by omega,
      by rw [heL_len]; omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      heL_nd, heL_at, hG_CA, hG_val, hG_v, fun e he => ?_⟩
    · rw [hAgree_CA_0 _ (Or.inl (by omega)) (by omega), hL0]
    · rw [hAgree_CA_0 _ (Or.inl (by omega)) (by omega), hvC0]
    · rw [hAgree_CA_0 _ (Or.inl (by omega)) (by omega), heC0]
    · rw [hAgree_CA_0 _ (Or.inl (by omega)) (by omega)]; omega
    · intro e he; refine ⟨fun v hv => by omega, Or.inl (by omega)⟩
    · intro v hv
      rw [hAgree_CA_0 _ (Or.inr (by omega)) (by omega), hAgree_CA_0 _ (Or.inl (by omega)) (by omega)]
      exact hvst0 v hv
    · intro i hi
      exact sc_frame_of_lt_vstamp (by omega) (by omega) (by omega)
    · intro k hk
      exact sc_frame_of_lt_vstamp (by omega) (by omega) (by rw [heL_len] at hk; omega)
    · have heG : e ∈ G.E := (heL_mem e).mp he
      obtain ⟨he_c, hmem_lo, hmem_hi, hw_sp⟩ := hmEmbB_SP.2.2 e heG
      have hmlo_ge := hmEmbLo_SP e heG
      have hmep_ag : memCA (mEmbOutPtr + e) = memSP (mEmbOutPtr + e) :=
        hAgree_CA_ge_fix _ (by omega)
      have hlen_mwe : (mWalkEncode (emb e)).length = 1 + 2 * (emb e).length := mWalkEncode_length _
      have hmw_ca : MWalkAt memCA (memCA (mEmbOutPtr + e)) (emb e) := by
        rw [hmep_ag]
        exact hw_sp.of_agree fun _ h1 _ => hAgree_CA_ge_fix _ (by omega)
      refine ⟨heG, he_c, hEmb_G e heG, hmw_ca, by rw [hmep_ag]; omega, fun addr ha1 ha2 => ?_⟩
      rw [hmep_ag] at ha1 ha2
      exact ⟨fun v hv => by omega, fun e' he' => by omega, Or.inl (by omega)⟩
  refine runs_seq_call_le (dsShortcutEmb_meetsContract hpLW hpOps)
    (by simp [evalArgs, Expr.eval, hr0, hr6, hr11, hr17, hr15])
    (fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    hpre_sc ?_
  intro retSC memSC _ ⟨_, _, _, _, hEqSC, hsc_ge, hsc_le, hvstSC, hWalksSC, hfrSC⟩
  simp only [List.cons.injEq, true_and, and_true] at hEqSC
  rcases hEqSC with ⟨rfl, rfl, _, rfl, rfl⟩
  dsimp only at hsc_ge hsc_le hvstSC hWalksSC hfrSC
  have hsc_bnd : retSC ≤ heapSp + 7 * ∑ e ∈ G.E, ((emb e).length + 1) := by omega
  refine dsInitCore_lwRet_cont hpLW hpRev hpOps hw16 hb1 hfix hheap_sp hmep_lo hmep_hi hsc_ge hsc_bnd
    hsp_max hmax_w hz0 hzSP hL0 hvC0 heC0 hgen_w hrevg0 hedg0 hG_v hG_e hG_val hH_val hGV_sub
    hHV_v hHE_sub heL_len heL_nd heL_mem heL_at hG_CA hH_CA hAuxCA hminI hdllI hdegI hbuckI
    hEmb_core hvstSC hWalksSC hfrSC hfrCA hfrI hfrSP hfr1 hAgree_CA_0 hAgree_CA_ge_fix
    _ ω rfl (by simp [Function.update_of_ne, hr0]) (by simp [Function.update_of_ne, hr11])
    (by simp [Function.update_of_ne]) (by simp) (by simp [Function.update_of_ne, hr17]) ?_
  simp only [clearAuxGraphContract, dsShortcutEmbContract, argsSize, Expr.size]
  rw [hsum_len_emb0, heL_len]
  omega

end

end MinCostFlow.DynSpanner.Program
