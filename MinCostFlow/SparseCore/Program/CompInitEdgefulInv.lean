module

public import MinCostFlow.SparseCore.Program.CompInitBase
import WordRAM.Tactic

/-!
# Memory-Invariant Step for Edgeful Component Initialization (`CompInitEdgefulInv`)

Proves `initMemInv_step_edgeful`, isolating the memory-invariant preservation after running
`compBfsCompProc`, the three component-metadata stores, `dgInitFromLists`, and `W.initOff`
on an unvisited edgeful component `C`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

private lemma initHdr_of_agree {b vCap eCap k L_w h L_in P_fp m0Total : ℕ}
    {m1 m2 : ℕ → ℕ}
    (hag : ∀ off < compHdrSize, m2 (b + off) = m1 (b + off))
    (H : m1 (b + compOffVCap) = vCap ∧ m1 (b + compOffECap) = eCap ∧ m1 (b + compOffK) = k ∧
      m1 (b + compOffLW) = L_w ∧ m1 (b + compOffHLimb) = h ∧ m1 (b + compOffLIn) = L_in ∧
      m1 (b + compOffPFp) = P_fp ∧ m1 (b + compOffVCompPtr) = compVCompBase b ∧
      m1 (b + compOffEdgefulPtr) = compEdgefulBase b vCap ∧
      m1 (b + compOffEdgefulIdxPtr) = compEdgefulIdxBase b vCap ∧
      m1 (b + compOffN0Ptr) = compN0Base b vCap ∧
      m1 (b + compOffM0Ptr) = compM0Base b vCap ∧
      m1 (b + compOffEdgeC1Ptr) = compEdgeC1Base b vCap ∧
      m1 (b + compOffEdgeC2Ptr) = compEdgeC2Base b vCap eCap ∧
      m1 (b + compOffIsCrossPtr) = compIsCrossBase b vCap eCap ∧
      m1 (b + compOffIsInsPtr) = compIsInsBase b vCap eCap ∧
      m1 (b + compOffGhostPtr) = compGhostBase b vCap eCap ∧
      m1 (b + compOffTouchMarkPtr) = compTouchMarkBase b vCap eCap ∧
      m1 (b + compOffOneLimbPtr) = compOneLimbBase b vCap eCap ∧
      m1 (b + compOffHandlesPtr) = compHandlesBase b vCap eCap L_w ∧
      m1 (b + compOffM0Total) = m0Total) :
    m2 (b + compOffVCap) = vCap ∧ m2 (b + compOffECap) = eCap ∧ m2 (b + compOffK) = k ∧
      m2 (b + compOffLW) = L_w ∧ m2 (b + compOffHLimb) = h ∧ m2 (b + compOffLIn) = L_in ∧
      m2 (b + compOffPFp) = P_fp ∧ m2 (b + compOffVCompPtr) = compVCompBase b ∧
      m2 (b + compOffEdgefulPtr) = compEdgefulBase b vCap ∧
      m2 (b + compOffEdgefulIdxPtr) = compEdgefulIdxBase b vCap ∧
      m2 (b + compOffN0Ptr) = compN0Base b vCap ∧
      m2 (b + compOffM0Ptr) = compM0Base b vCap ∧
      m2 (b + compOffEdgeC1Ptr) = compEdgeC1Base b vCap ∧
      m2 (b + compOffEdgeC2Ptr) = compEdgeC2Base b vCap eCap ∧
      m2 (b + compOffIsCrossPtr) = compIsCrossBase b vCap eCap ∧
      m2 (b + compOffIsInsPtr) = compIsInsBase b vCap eCap ∧
      m2 (b + compOffGhostPtr) = compGhostBase b vCap eCap ∧
      m2 (b + compOffTouchMarkPtr) = compTouchMarkBase b vCap eCap ∧
      m2 (b + compOffOneLimbPtr) = compOneLimbBase b vCap eCap ∧
      m2 (b + compOffHandlesPtr) = compHandlesBase b vCap eCap L_w ∧
      m2 (b + compOffM0Total) = m0Total := by
  rcases H with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  exact ⟨(hag compOffVCap (by decide)).trans h0, (hag compOffECap (by decide)).trans h1,
    (hag compOffK (by decide)).trans h2, (hag compOffLW (by decide)).trans h3,
    (hag compOffHLimb (by decide)).trans h4, (hag compOffLIn (by decide)).trans h5,
    (hag compOffPFp (by decide)).trans h6, (hag compOffVCompPtr (by decide)).trans h7,
    (hag compOffEdgefulPtr (by decide)).trans h8, (hag compOffEdgefulIdxPtr (by decide)).trans h9,
    (hag compOffN0Ptr (by decide)).trans h10, (hag compOffM0Ptr (by decide)).trans h11,
    (hag compOffEdgeC1Ptr (by decide)).trans h12, (hag compOffEdgeC2Ptr (by decide)).trans h13,
    (hag compOffIsCrossPtr (by decide)).trans h14, (hag compOffIsInsPtr (by decide)).trans h15,
    (hag compOffGhostPtr (by decide)).trans h16, (hag compOffTouchMarkPtr (by decide)).trans h17,
    (hag compOffOneLimbPtr (by decide)).trans h18, (hag compOffHandlesPtr (by decide)).trans h19,
    (hag compOffM0Total (by decide)).trans h20⟩

/-- Preserves `InitMemInv` across one edgeful component initialization step. -/
lemma initMemInv_step_edgeful {W : LSFWindowImpl} {w k : ℕ} {G₀ : MGraph} {p : Program}
    {mem0 m0 mBfs mWin : ℕ → ℕ}
    (ctx : InitCtx W w k G₀ p mem0)
    {C : Finset ℕ} {curHeap endHeap : ℕ} {comps : List (Finset ℕ)} {efIdx : List ℕ}
    {winH : ℕ → ℕ → ℕ} {winX : ℕ → ℕ → LSFConcrete}
    {hWinC : ℕ → ℕ} {xWinC : ℕ → LSFConcrete}
    (hC_mem : C ∈ components G₀) (hC_not : C ∉ comps)
    (hmC_pos : 1 ≤ (compGraph G₀ C).m)
    (hc_lt : comps.length < ctx.vCap)
    (hInv : InitMemInv ctx m0 curHeap comps efIdx winH winX)
    (hBfs_m0 : mBfs (compM0Base ctx.b ctx.vCap + comps.length) = (compGraph G₀ C).m)
    (hBfs_vis : ∀ u < ctx.vCap0, mBfs (compTablesEnd ctx.b ctx.vCap ctx.eCap ctx.L_w G₀.m k + u) =
      if u ∈ comps.toFinset.biUnion id ∪ C then 1 else 0)
    (hBfs_vc : ∀ u ∈ C, mBfs (compVCompBase ctx.b + u) = comps.length)
    (hBfs_vc_fr : ∀ u < ctx.vCap0, u ∉ C → mBfs (compVCompBase ctx.b + u) = m0 (compVCompBase ctx.b + u))
    (hBfs_eC : ∀ e ∈ compEdgeSet G₀ C,
      mBfs (compEdgeC1Base ctx.b ctx.vCap + e) = comps.length ∧
      mBfs (compEdgeC2Base ctx.b ctx.vCap ctx.eCap + e) = comps.length)
    (hBfs_eC_fr : ∀ e < ctx.eCap0, e ∉ compEdgeSet G₀ C →
      mBfs (compEdgeC1Base ctx.b ctx.vCap + e) = m0 (compEdgeC1Base ctx.b ctx.vCap + e) ∧
      mBfs (compEdgeC2Base ctx.b ctx.vCap ctx.eCap + e) = m0 (compEdgeC2Base ctx.b ctx.vCap ctx.eCap + e))
    (hBfs_fr : ∀ a,
      (a < compTablesEnd ctx.b ctx.vCap ctx.eCap ctx.L_w G₀.m k ∨
        compTablesEnd ctx.b ctx.vCap ctx.eCap ctx.L_w G₀.m k + ctx.vCap0 ≤ a) →
      (a < compVCompBase ctx.b ∨ compVCompBase ctx.b + ctx.vCap0 ≤ a) →
      (a < compEdgeC1Base ctx.b ctx.vCap ∨ compEdgeC1Base ctx.b ctx.vCap + ctx.eCap0 ≤ a) →
      (a < compEdgeC2Base ctx.b ctx.vCap ctx.eCap ∨ compEdgeC2Base ctx.b ctx.vCap ctx.eCap + ctx.eCap0 ≤ a) →
      (a < compTablesEnd ctx.b ctx.vCap ctx.eCap ctx.L_w G₀.m k + ctx.vCap ∨
        compTablesEnd ctx.b ctx.vCap ctx.eCap ctx.L_w G₀.m k + ctx.vCap + (compGraph G₀ C).n ≤ a) →
      (a < compTablesEnd ctx.b ctx.vCap ctx.eCap ctx.L_w G₀.m k + ctx.vCap + G₀.n ∨
        compTablesEnd ctx.b ctx.vCap ctx.eCap ctx.L_w G₀.m k + ctx.vCap + G₀.n + 3 * (compGraph G₀ C).m ≤ a) →
      a ≠ compM0Base ctx.b ctx.vCap + comps.length → mBfs a = m0 a)
    (hend_ge : curHeap + dynGraphSize ctx.vCap ctx.eCap ≤ endHeap)
    (hend_le : endHeap ≤ curHeap + dynGraphSize ctx.vCap ctx.eCap +
      W.winSpace k ctx.L_w ctx.vCap ctx.eCap (compGraph G₀ C).n (compGraph G₀ C).m)
    (hWin_zf : ZeroFrom mWin endHeap)
    (_hho_le : compHandlesBase ctx.b ctx.vCap ctx.eCap ctx.L_w + efIdx.length * k + k ≤ ctx.heap0)
    (hWin_m10 : ∀ a < curHeap,
      (a < compHandlesBase ctx.b ctx.vCap ctx.eCap ctx.L_w + efIdx.length * k ∨
        compHandlesBase ctx.b ctx.vCap ctx.eCap ctx.L_w + efIdx.length * k + k ≤ a) →
      mWin a =
        Function.update
          (Function.update
            (Function.update mBfs (compEdgefulBase ctx.b ctx.vCap + comps.length) 1)
            (compEdgefulIdxBase ctx.b ctx.vCap + comps.length) efIdx.length)
          (compN0Base ctx.b ctx.vCap + comps.length) (compGraph G₀ C).n a)
    (hWin_j : ∀ j < k,
      mWin (compHandlesBase ctx.b ctx.vCap ctx.eCap ctx.L_w + efIdx.length * k + j) = hWinC j ∧
      (LSFRep W.h).rep (hWinC j) (W.lsfInit (compGraph G₀ C) ctx.ell k j) (xWinC j) mWin ∧
      (xWinC j).vCap = ctx.vCap ∧ (xWinC j).eCap = ctx.eCap ∧ (xWinC j).L_w = ctx.L_w ∧
      ∀ a, (LSFRep W.h).foot (hWinC j) (xWinC j) a →
        curHeap + dynGraphSize ctx.vCap ctx.eCap ≤ a ∧ a < endHeap)
    (hWin_disj : ∀ j₁ < k, ∀ j₂ < k, j₁ ≠ j₂ →
      ∀ a, (LSFRep W.h).foot (hWinC j₁) (xWinC j₁) a →
        ¬ (LSFRep W.h).foot (hWinC j₂) (xWinC j₂) a) :
    InitMemInv ctx mWin endHeap (comps ++ [C]) (efIdx ++ [comps.length])
      (fun r j => if r = efIdx.length then hWinC j else winH r j)
      (fun r j => if r = efIdx.length then xWinC j else winX r j) := by
  classical
  set visBase := compTablesEnd ctx.b ctx.vCap ctx.eCap ctx.L_w G₀.m k
  set handlesBase := compHandlesBase ctx.b ctx.vCap ctx.eCap ctx.L_w
  set handlesOut := handlesBase + efIdx.length * k
  set winHeap := curHeap + dynGraphSize ctx.vCap ctx.eCap
  set m10 := Function.update
    (Function.update
      (Function.update mBfs (compEdgefulBase ctx.b ctx.vCap + comps.length) 1)
      (compEdgefulIdxBase ctx.b ctx.vCap + comps.length) efIdx.length)
    (compN0Base ctx.b ctx.vCap + comps.length) (compGraph G₀ C).n
  have hch_ge : ctx.heap0 ≤ curHeap := hInv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hnC_le : (compGraph G₀ C).n ≤ G₀.n := compGraph_n_le hC_mem
  have hmC_le : (compGraph G₀ C).m ≤ G₀.m := compGraph_m_le
  have hDisjC : ∀ X ∈ comps, Disjoint X C := fun X hX =>
    comp_disjoint_of_ne G₀ (hInv.2.2.2.2.2.1 X hX) hC_mem (fun h => hC_not (h ▸ hX))
  have hef_disj_C : C ∉ comps.toFinset.filter (fun X => 1 ≤ (compGraph G₀ X).m) := fun h =>
    hC_not (List.mem_toFinset.mp (Finset.mem_filter.mp h).1)
  have hef_succ_le : efIdx.length + 1 ≤ G₀.m := by
    have h1 := init_numEdgeful_le hInv.2.2.2.2.1 hInv.2.2.2.2.2.2.1
      hInv.2.2.2.2.2.2.2.1 hInv.2.2.2.2.2.2.2.2.1
    have hsub_ins : insert C (comps.toFinset.filter fun X => 1 ≤ (compGraph G₀ X).m) ⊆ components G₀ := by
      intro X hX
      rcases Finset.mem_insert.mp hX with rfl | hX'
      · exact hC_mem
      · exact hInv.2.2.2.2.2.1 X (List.mem_toFinset.mp (Finset.mem_filter.mp hX').1)
    have h2 := init_sum_m_le hsub_ins
    rw [Finset.sum_insert hef_disj_C] at h2
    omega
  have hho_vis : handlesOut + k ≤ visBase := by
    have hmul : (efIdx.length + 1) * k ≤ G₀.m * k := Nat.mul_le_mul_right k hef_succ_le
    dsimp [handlesOut, handlesBase, visBase, compTablesEnd]
    have : efIdx.length * k + k = (efIdx.length + 1) * k := by ring
    omega
  -- Contiguous region ordering
  have hB_vc : ctx.b + compHdrSize = compVCompBase ctx.b := rfl
  have hVC_ef : compVCompBase ctx.b + ctx.vCap = compEdgefulBase ctx.b ctx.vCap := rfl
  have hEF_efi : compEdgefulBase ctx.b ctx.vCap + ctx.vCap = compEdgefulIdxBase ctx.b ctx.vCap := rfl
  have hEFI_n0 : compEdgefulIdxBase ctx.b ctx.vCap + ctx.vCap = compN0Base ctx.b ctx.vCap := rfl
  have hN0_m0 : compN0Base ctx.b ctx.vCap + ctx.vCap = compM0Base ctx.b ctx.vCap := rfl
  have hM0_ec1 : compM0Base ctx.b ctx.vCap + ctx.vCap = compEdgeC1Base ctx.b ctx.vCap := rfl
  have hEC1_ec2 : compEdgeC1Base ctx.b ctx.vCap + ctx.eCap = compEdgeC2Base ctx.b ctx.vCap ctx.eCap := rfl
  have hEC2_ic : compEdgeC2Base ctx.b ctx.vCap ctx.eCap + ctx.eCap = compIsCrossBase ctx.b ctx.vCap ctx.eCap := rfl
  have hIC_one : compIsCrossBase ctx.b ctx.vCap ctx.eCap ≤ compOneLimbBase ctx.b ctx.vCap ctx.eCap := by
    dsimp [compOneLimbBase, compTouchMarkBase, compGhostBase, compIsInsBase]; omega
  have hOne_h : compOneLimbBase ctx.b ctx.vCap ctx.eCap + ctx.L_w = handlesBase :=
    compOneLimb_end_eq ctx.b ctx.vCap ctx.eCap ctx.L_w
  have hH_vis : handlesBase + G₀.m * k = visBase := rfl
  have hVis_h0 : visBase + ctx.vCap + G₀.n + 3 * G₀.m = ctx.heap0 := rfl
  have hvCap_le : ctx.vCap0 ≤ ctx.vCap := ctx.hvCap_le
  have heCap_le : ctx.eCap0 ≤ ctx.eCap := ctx.heCap_le
  have hLw_pos : 1 ≤ ctx.L_w := ctx.hLw
  have hlt_ho : ∀ a < handlesBase, a < handlesOut := fun a ha => by dsimp [handlesOut]; omega
  have hm10_bfs : ∀ a, a ≠ compEdgefulBase ctx.b ctx.vCap + comps.length →
      a ≠ compEdgefulIdxBase ctx.b ctx.vCap + comps.length →
      a ≠ compN0Base ctx.b ctx.vCap + comps.length → m10 a = mBfs a := fun a h1 h2 h3 => by
    dsimp only [m10]
    rw [Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
  have hm10_ge : ∀ a, ctx.heap0 ≤ a → m10 a = m0 a := fun a ha =>
    (hm10_bfs a (by omega) (by omega) (by omega)).trans
    (hBfs_fr a (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (by omega))
  have hstWin_st : ∀ a < curHeap, (a < handlesOut ∨ handlesOut + k ≤ a) →
      a < compVCompBase ctx.b ∨
      (compIsCrossBase ctx.b ctx.vCap ctx.eCap ≤ a ∧ a < visBase) ∨
      ctx.heap0 ≤ a → mWin a = m0 a := fun a ha hho hreg => by
    rw [hWin_m10 a ha hho]
    rcases hreg with h1 | ⟨h1, h2⟩ | h1
    · exact (hm10_bfs a (by omega) (by omega) (by omega)).trans
        (hBfs_fr a (Or.inl (by omega)) (Or.inl h1) (Or.inl (by omega))
          (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (by omega))
    · exact (hm10_bfs a (by omega) (by omega) (by omega)).trans
        (hBfs_fr a (Or.inl h2) (Or.inr (by omega)) (Or.inr (by omega))
          (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (by omega))
    · exact hm10_ge a h1
  have hC_nd : (comps ++ [C]).Nodup := List.nodup_append.mpr
    ⟨hInv.2.2.2.2.1, List.nodup_singleton _, fun x hx y hy => by
      simp only [List.mem_singleton] at hy; subst hy; exact fun h => hC_not (h ▸ hx)⟩
  have hC_sub' : ∀ X ∈ comps ++ [C], X ∈ components G₀ := fun X hX => by
    rcases List.mem_append.mp hX with h1 | h2
    · exact hInv.2.2.2.2.2.1 X h1
    · simp only [List.mem_singleton] at h2; exact h2 ▸ hC_mem
  have hef_nd : (efIdx ++ [comps.length]).Nodup := List.nodup_append.mpr
    ⟨hInv.2.2.2.2.2.2.1, List.nodup_singleton _, fun x hx y hy => by
      simp only [List.mem_singleton] at hy; subst hy
      have := hInv.2.2.2.2.2.2.2.1 x hx; omega⟩
  refine ⟨fun a ha => (hstWin_st a (by omega) (Or.inl (hlt_ho a (by omega)))
      (Or.inl (by omega))).trans (hInv.1 a ha),
    ?_, ?_, ?_, hC_nd, hC_sub', hef_nd,
    fun idx hidx => by
      simp only [List.mem_append, List.mem_singleton, List.length_append, List.length_singleton] at hidx ⊢
      rcases hidx with h1 | rfl
      · have := hInv.2.2.2.2.2.2.2.1 idx h1; omega
      · omega,
    ?_, ?_, ?_, ?_, ?_, by omega, ?_, hWin_zf⟩
  · -- Header preserved
    exact initHdr_of_agree (fun off hoff =>
      hstWin_st _ (by omega) (Or.inl (hlt_ho _ (by omega))) (Or.inl (by omega))) hInv.2.1
  · -- Zero region `[compIsCrossBase, compOneLimbBase)`
    intro a ha1 ha2
    exact (hstWin_st a (by omega) (Or.inl (hlt_ho a (by omega)))
      (Or.inr (Or.inl ⟨ha1, by omega⟩))).trans (hInv.2.2.1 a ha1 ha2)
  · -- `oneLimb = [1, 0, ..., 0]`
    refine ⟨(hstWin_st _ (by omega) (Or.inl (hlt_ho _ (by omega)))
      (Or.inr (Or.inl ⟨hIC_one, by omega⟩))).trans hInv.2.2.2.1.1,
      fun t ht1 ht2 => (hstWin_st _ (by omega) (Or.inl (hlt_ho _ (by omega)))
        (Or.inr (Or.inl ⟨by omega, by omega⟩))).trans (hInv.2.2.2.1.2 t ht1 ht2)⟩
  · -- Edgeful membership characterization
    intro idx hi
    simp only [List.length_append, List.length_singleton, List.mem_append, List.mem_singleton] at hi ⊢
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · rw [List.getElem_append_left hi']
      have hprev := hInv.2.2.2.2.2.2.2.2.1 idx hi'
      exact ⟨fun h => Or.inl (hprev.mp h), fun h => by rcases h with h | h; exact hprev.mpr h; omega⟩
    · rw [List.getElem_append_right le_rfl]
      simp only [Nat.sub_self, List.getElem_singleton]
      exact ⟨fun _ => Or.inr trivial, fun _ => hmC_pos⟩
  · -- Visited array
    intro u hu
    have hu_eq : mWin (visBase + u) = mBfs (visBase + u) :=
      (hWin_m10 _ (by omega) (Or.inr (by omega))).trans
      (hm10_bfs _ (by omega) (by omega) (by omega))
    rw [hu_eq]
    by_cases hu0 : u < ctx.vCap0
    · rw [hBfs_vis u hu0]; simp
    · have hfr := hBfs_fr (visBase + u) (Or.inr (by omega)) (Or.inr (by omega))
        (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (by omega)
      rw [hfr, hInv.2.2.2.2.2.2.2.2.2.1 u hu]
      have huNotC : u ∉ C := fun h => hu0 (ctx.hdg.2.1 u (by
        rcases Finset.mem_image.mp hC_mem with ⟨w', _, hEq⟩
        rw [← hEq] at h; exact (mem_compOf_iff.mp h).1))
      simp [huNotC]
  · -- Per-component metadata (`vComp`, `edgeful`, `n0`, `m0`, `edgeC1`, `edgeC2`)
    intro idx hi
    simp only [List.length_append, List.length_singleton] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · rw [List.getElem_append_left hi']
      have hprev := hInv.2.2.2.2.2.2.2.2.2.2.1 idx hi'
      have hCi_disj : Disjoint comps[idx] C := hDisjC _ (List.getElem_mem hi')
      refine ⟨fun u hu => ?_, ?_, ?_, ?_, fun e he => ?_⟩
      · have hu0 : u < ctx.vCap0 := ctx.hdg.2.1 u (by
          rcases Finset.mem_image.mp (hInv.2.2.2.2.2.1 _ (List.getElem_mem hi')) with ⟨w', _, hEq⟩
          rw [← hEq] at hu; exact (mem_compOf_iff.mp hu).1)
        have huNotC : u ∉ C := Finset.disjoint_left.mp hCi_disj hu
        exact ((hWin_m10 _ (by omega) (Or.inl (hlt_ho _ (by omega)))).trans
          ((hm10_bfs _ (by omega) (by omega) (by omega)).trans
          (hBfs_vc_fr u hu0 huNotC))).trans (hprev.1 u hu)
      · exact ((hWin_m10 _ (by omega) (Or.inl (hlt_ho _ (by omega)))).trans
          ((hm10_bfs _ (by omega) (by omega) (by omega)).trans
          (hBfs_fr _ (Or.inl (by omega)) (Or.inr (by omega)) (Or.inl (by omega))
            (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (by omega)))).trans hprev.2.1
      · exact ((hWin_m10 _ (by omega) (Or.inl (hlt_ho _ (by omega)))).trans
          ((hm10_bfs _ (by omega) (by omega) (by omega)).trans
          (hBfs_fr _ (Or.inl (by omega)) (Or.inr (by omega)) (Or.inl (by omega))
            (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (by omega)))).trans hprev.2.2.1
      · exact ((hWin_m10 _ (by omega) (Or.inl (hlt_ho _ (by omega)))).trans
          ((hm10_bfs _ (by omega) (by omega) (by omega)).trans
          (hBfs_fr _ (Or.inl (by omega)) (Or.inr (by omega)) (Or.inl (by omega))
            (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (by omega)))).trans hprev.2.2.2.1
      · have he0 : e < ctx.eCap0 := ctx.hdg.2.2.1 e (Finset.filter_subset _ _ he)
        have heNotC : e ∉ compEdgeSet G₀ C := Finset.disjoint_left.mp
          (compEdgeSet_pairwiseDisjoint G₀ (hInv.2.2.2.2.2.1 _ (List.getElem_mem hi')) hC_mem
            (fun h => hC_not (h ▸ List.getElem_mem hi'))) he
        have he_fr := hBfs_eC_fr e he0 heNotC
        exact ⟨((hWin_m10 _ (by omega) (Or.inl (hlt_ho _ (by omega)))).trans
            ((hm10_bfs _ (by omega) (by omega) (by omega)).trans he_fr.1)).trans (hprev.2.2.2.2 e he).1,
          ((hWin_m10 _ (by omega) (Or.inl (hlt_ho _ (by omega)))).trans
            ((hm10_bfs _ (by omega) (by omega) (by omega)).trans he_fr.2)).trans (hprev.2.2.2.2 e he).2⟩
    · rw [List.getElem_append_right le_rfl]
      simp only [Nat.sub_self, List.getElem_singleton]
      refine ⟨fun u hu => ?_, ?_, ?_, ?_, fun e he => ?_⟩
      · have hu0 : u < ctx.vCap0 := ctx.hdg.2.1 u (by
          rcases Finset.mem_image.mp hC_mem with ⟨w', _, hEq⟩
          rw [← hEq] at hu; exact (mem_compOf_iff.mp hu).1)
        exact (hWin_m10 _ (by omega) (Or.inl (hlt_ho _ (by omega)))).trans
          ((hm10_bfs _ (by omega) (by omega) (by omega)).trans (hBfs_vc u hu))
      · rw [ite_eq_left hmC_pos, hWin_m10 _ (by omega) (Or.inl (hlt_ho _ (by omega)))]
        dsimp only [m10]
        have hne1 : compEdgefulBase ctx.b ctx.vCap + comps.length ≠
            compN0Base ctx.b ctx.vCap + comps.length := by omega
        have hne2 : compEdgefulBase ctx.b ctx.vCap + comps.length ≠
            compEdgefulIdxBase ctx.b ctx.vCap + comps.length := by omega
        rw [Function.update_of_ne hne1, Function.update_of_ne hne2, Function.update_self]
      · rw [hWin_m10 _ (by omega) (Or.inl (hlt_ho _ (by omega)))]
        exact Function.update_self _ _ _
      · exact (hWin_m10 _ (by omega) (Or.inl (hlt_ho _ (by omega)))).trans
          ((hm10_bfs _ (by omega) (by omega) (by omega)).trans hBfs_m0)
      · have he0 : e < ctx.eCap0 := ctx.hdg.2.2.1 e (Finset.filter_subset _ _ he)
        exact ⟨(hWin_m10 _ (by omega) (Or.inl (hlt_ho _ (by omega)))).trans
            ((hm10_bfs _ (by omega) (by omega) (by omega)).trans (hBfs_eC e he).1),
          (hWin_m10 _ (by omega) (Or.inl (hlt_ho _ (by omega)))).trans
            ((hm10_bfs _ (by omega) (by omega) (by omega)).trans (hBfs_eC e he).2)⟩
  · -- Per-edgeful component windows
    intro r hr
    simp only [List.length_append, List.length_singleton] at hr
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr' | rfl
    · rw [List.getElem_append_left hr']
      obtain ⟨hi, hefi, hwj⟩ := hInv.2.2.2.2.2.2.2.2.2.2.2.1 r hr'
      refine ⟨by simp; omega, ?_, fun j hj => ?_⟩
      · exact ((hWin_m10 _ (by omega) (Or.inl (hlt_ho _ (by omega)))).trans
          ((hm10_bfs _ (by omega) (by omega) (by omega)).trans
          (hBfs_fr _ (Or.inl (by omega)) (Or.inr (by omega)) (Or.inl (by omega))
            (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (by omega)))).trans hefi
      · obtain ⟨hm_h, hrep_j, hvj, hej, hLwj, hge_j, hle_j, hft_j⟩ := hwj j hj
        have hrne : r ≠ efIdx.length := Nat.ne_of_lt hr'
        simp only [hrne, ↓reduceIte, List.getElem_append_left hi]
        have hslot_lt : handlesBase + (r * k + j) < handlesOut := by
          have : r * k + j < efIdx.length * k := by
            calc r * k + j < r * k + k := Nat.add_lt_add_left hj _
              _ = (r + 1) * k := by ring
              _ ≤ efIdx.length * k := Nat.mul_le_mul_right k hr'
          dsimp [handlesOut]; omega
        refine ⟨(hstWin_st _ (by omega) (Or.inl hslot_lt)
            (Or.inr (Or.inl ⟨by omega, by omega⟩))).trans hm_h,
          (lsfRep_local W.h _ _ _ _ _ fun a ha =>
            (hstWin_st a (hft_j a ha).2 (Or.inr (by have := (hft_j a ha).1; omega))
              (Or.inr (Or.inr (hft_j a ha).1))).symm).1 hrep_j,
          hvj, hej, hLwj, hge_j, by omega,
          fun a ha => ⟨(hft_j a ha).1, by have := (hft_j a ha).2; omega⟩⟩
    · rw [List.getElem_append_right le_rfl]
      simp only [Nat.sub_self, List.getElem_singleton]
      refine ⟨by simp, ?_, fun j hj => ?_⟩
      · rw [hWin_m10 _ (by omega) (Or.inl (hlt_ho _ (by omega)))]
        dsimp only [m10]
        have hne1 : compEdgefulIdxBase ctx.b ctx.vCap + comps.length ≠
            compN0Base ctx.b ctx.vCap + comps.length := by omega
        rw [Function.update_of_ne hne1, Function.update_self]
      · simp only [↓reduceIte, List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_singleton]
        obtain ⟨hm_h, hrep_j, hvj, hej, hLwj, hft_j⟩ := hWin_j j hj
        have hpos : hWinC j + lsfHdrSize ≤ (xWinC j).endAddr (hWinC j) :=
          lsfHdr_lt_end _ _ _ _ _ _
        have hhdr_pos : 0 < lsfHdrSize := by decide
        have hhdr_ge : winHeap ≤ hWinC j :=
          (hft_j (hWinC j) ⟨le_rfl, by omega⟩).1
        have hend_j_le : (xWinC j).endAddr (hWinC j) ≤ endHeap := by
          have hlt := (hft_j ((xWinC j).endAddr (hWinC j) - 1) ⟨by omega, by omega⟩).2
          omega
        have hge_ch : ctx.heap0 ≤ hWinC j := by
          have : curHeap ≤ hWinC j := by dsimp [winHeap] at hhdr_ge; omega
          clear * - this hch_ge; omega
        refine ⟨by rw [← Nat.add_assoc]; exact hm_h, hrep_j, hvj, hej, hLwj,
          hge_ch, hend_j_le,
          fun a ha => ⟨by have h1 := (hft_j a ha).1; clear * - h1 hch_ge; omega, (hft_j a ha).2⟩⟩
  · -- Pairwise disjointness of all windows
    intro r1 hr1 r2 hr2 j1 hj1 j2 hj2 hne a ha1 ha2
    simp only [List.length_append, List.length_singleton] at hr1 hr2
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr1 with hr1' | rfl <;>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr2 with hr2' | rfl
    · simp only [Nat.ne_of_lt hr1', Nat.ne_of_lt hr2', ↓reduceIte] at ha1 ha2
      exact hInv.2.2.2.2.2.2.2.2.2.2.2.2.1 r1 hr1' r2 hr2' j1 hj1 j2 hj2 hne a ha1 ha2
    · simp only [Nat.ne_of_lt hr1', ↓reduceIte] at ha1 ha2
      obtain ⟨_, _, hw1⟩ := hInv.2.2.2.2.2.2.2.2.2.2.2.1 r1 hr1'
      have h1 := ((hw1 j1 hj1).2.2.2.2.2.2.2 a ha1).2
      have h2 := ((hWin_j j2 hj2).2.2.2.2.2 a ha2).1
      omega
    · simp only [Nat.ne_of_lt hr2', ↓reduceIte] at ha1 ha2
      obtain ⟨_, _, hw2⟩ := hInv.2.2.2.2.2.2.2.2.2.2.2.1 r2 hr2'
      have h2 := ((hw2 j2 hj2).2.2.2.2.2.2.2 a ha2).2
      have h1 := ((hWin_j j1 hj1).2.2.2.2.2 a ha1).1
      omega
    · simp only [↓reduceIte] at ha1 ha2
      exact hWin_disj j1 hj1 j2 hj2 (hne.resolve_left (fun h => h rfl)) a ha1 ha2
  · -- Heap bound sum over edgeful components
    have hfilt_eq : ((comps ++ [C]).toFinset.filter fun X => 1 ≤ (compGraph G₀ X).m) =
        insert C (comps.toFinset.filter fun X => 1 ≤ (compGraph G₀ X).m) := by
      ext X; simp only [List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
        Finset.mem_filter, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty, or_false]
      constructor
      · rintro ⟨h1 | rfl, hm⟩; exact Or.inr ⟨h1, hm⟩; exact Or.inl rfl
      · rintro (rfl | ⟨h1, hm⟩); exact ⟨Or.inr rfl, hmC_pos⟩; exact ⟨Or.inl h1, hm⟩
    rw [hfilt_eq, Finset.sum_insert hef_disj_C]
    have hch_le := hInv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    clear * - hend_le hch_le
    omega

end

end MinCostFlow.SparseCore.Program
