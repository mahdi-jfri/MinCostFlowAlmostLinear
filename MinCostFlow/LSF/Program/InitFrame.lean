module

public import MinCostFlow.LSF.Program.InitKeep
public import MinCostFlow.LSF.Program.DecompFrame
public import MinCostFlow.LSF.Program.OrderPhaseFrame

/-!
# The frame of the whole init driver

The data-structure contract asks two things of the memory after `Initialize`: the cells below
the handle `b` are as before, and the memory is zero from the returned heap pointer on. The
driver returns `useEnd`, the end of its work area. `init_frame` proves both from the posts that
`main_wp` hands to its final condition.

Each phase writes only inside its own blocks, and every block lies in `[b, useEnd)`. So a cell
below `b` passes unchanged through all phases. A cell at or above `useEnd` passes unchanged
through all phases after the `[AN19]` call, and the tree phase leaves the memory zero from its
returned heap `H ≤ useEnd` on (`tree_ret`).
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.WideWord
  InitDriver

@[expose] public section

set_option maxHeartbeats 1000000 in
/-- The places of the driver: every block starts at or above `b` and ends at or below
`useEnd`. -/
lemma InitVals.frame_places (V : InitVals) (hH : V.lsstHeap ≤ V.H)
    (hLB : V.LB = wstrLB V.n0 (hldDepthBound V.n0) V.L_w) :
    (V.b ≤ V.auxPtr ∧ V.b ≤ V.fPtr ∧ V.b ≤ V.fAncPtr ∧ V.b ≤ V.wBase ∧ V.b ≤ V.wPtr ∧
      V.b ≤ V.dBase ∧ V.b ≤ V.numSt ∧ V.b ≤ V.tPtr ∧ V.b ≤ V.qNat ∧ V.b ≤ V.gPtr) ∧
    (V.b + 24 ≤ V.useEnd ∧ V.auxPtr + 20 ≤ V.useEnd ∧
      V.fPtr + dynGraphSize V.vCap (fECap V.eCap V.n0) ≤ V.useEnd ∧
      V.fAncPtr + fAncSize V.vCap ≤ V.useEnd ∧
      V.wBase + wWorkSize V.n0 (auxLogCap V.n0) ≤ V.useEnd ∧
      V.wPtr + wBlockSize V.n0 ≤ V.useEnd ∧
      wsPt V.idPtr V.n0 V.tM V.m0 (wstrLB V.n0 (hldDepthBound V.n0) V.L_w) 18 + V.m0 ≤
        V.useEnd ∧
      V.thBase + 8 * V.n0 ≤ V.useEnd ∧ V.H ≤ V.useEnd) := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ := V.aux_order
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19,
    s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32⟩ := V.scratch_order
  obtain ⟨u1, u2, u3, u4⟩ := V.useEnd_ge
  have hls : lsfHdrSize = 24 := rfl
  have hU : V.useEnd = V.wBase + wWorkSize V.n0 (auxLogCap V.n0) := rfl
  have hax : 20 ≤ auxSize V.vCap V.n0 := by simp only [auxSize, auxHdrSize]; omega
  rw [← hLB]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals omega

set_option maxHeartbeats 1600000 in
/-- The memory at the end of the driver agrees with the input below `b` and is zero from
`useEnd` on. -/
theorem init_frame {w h C : ℕ} {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ} {G₀ : MGraph}
    {v ℓ₀ : ℕ → ℝ} {P_fp : ℕ} {g0Ptr vCap0 eCap0 lenArr wtArr kk cnt H : ℕ}
    {bRoot bStore bOrder bT bTH bWT bLB bW bCopy bFlag bRoots bG bA bWF : ℕ}
    {mem mem₁ mem₂ mem₃ mem₄ mem₅ mem₆ mem₇ mem₈ : ℕ → ℕ} {v₄ v₅ v₆ v₇ v₈ : ℕ}
    {vList eList : List ℕ} {T₀ : MGraph} {vs₇ vs₈ : List ℕ}
    (V : InitVals) (hh : 1 ≤ h) (hLin : 1 ≤ V.L_in) (hn : G₀.n = V.n0)
    (hLBV : V.LB = wstrLB V.n0 (hldDepthBound V.n0) V.L_w)
    (h₁ : (prepStageContract w G₀).post (prepArgsV V g0Ptr vCap0 eCap0 kk) mem cnt mem₁)
    (h₂ : (widthsContract w).post [V.m0, V.L_in, V.endA + 3] mem₁ 0 mem₂)
    (h₃ : (treePhaseContract Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp vList eList).post
        (treeArgsV V lenArr wtArr) mem₂ H mem₃)
    (IO : OrderPhaseIn w h G₀ T₀ vList eList
      (OrderLayout.ofVals (V.withH H) (mem₃ V.outHdr)) mem₃)
    (h₄ : (orderPhaseContract w h G₀ T₀ vList eList bRoot bStore bOrder bT
      bTH).post (OrderLayout.ofVals (V.withH H) (mem₃ V.outHdr)).args mem₃ v₄ mem₄)
    (ID : DecompPhaseIn w h C T₀ vList
        (DecompLayout.ofVals (V.withH H) (mem₃ V.outHdr) (4 * kk * (hldDepthBound V.n0 + 1))
          (hldDepthBound V.n0) kk lenArr cnt) mem₄)
    (h₅ : (decompPhaseContract w h C bWT bLB bW bCopy bFlag bRoots decompPhaseCost).post
        (DecompLayout.ofVals (V.withH H) (mem₃ V.outHdr) (4 * kk * (hldDepthBound V.n0 + 1))
          (hldDepthBound V.n0) kk lenArr cnt).args mem₄ v₅ mem₅)
    (h₆ : (fPhaseContract w h bG bA bWF).post
        (FLayout.ofVals (V.withH H) (mem₃ V.outHdr) (4 * kk * (hldDepthBound V.n0 + 1))
          (hldDepthBound V.n0) kk lenArr cnt).args mem₅ v₆ mem₆)
    (h₇ : (storeArgsContract w 20).post (V.auxPtr :: vs₇) mem₆ v₇ mem₇)
    (h₈ : (storeArgsContract w 24).post (V.b :: vs₈) mem₇ v₈ mem₈) :
    (∀ a < V.b, mem₈ a = mem a) ∧ ZeroFrom mem₈ (V.withH H).useEnd := by
  obtain ⟨hH1, -, hz3⟩ := tree_ret V hh hLin h₃
  obtain ⟨_, _, _, _, _, _, _, o₁, o₃, o₄, o₅⟩ := orderPhase_post h₄
  have OF := (orderPhase_frame IO o₁ o₃ o₄ o₅).1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, p₁, p₃, p₄, p₅, p₆, p₇, p₈⟩ := decompPhase_post h₅
  obtain ⟨DF1, DF2, -⟩ := decompPhase_frame ID p₁ p₃ p₄ p₅ p₆ p₇ p₈
  have FF := fPhase_frame h₆
  obtain ⟨_, _, heq₇, -, -, hfr₇⟩ := h₇
  simp only [List.cons.injEq] at heq₇
  obtain ⟨rfl, rfl⟩ := heq₇
  obtain ⟨_, _, heq₈, -, -, hfr₈⟩ := h₈
  simp only [List.cons.injEq] at heq₈
  obtain ⟨rfl, rfl⟩ := heq₈
  have TF := tree_frame_low V h₃
  have BF := segB_frame h₁ h₂ hn
  -- the order of the places
  have hWH : (V.withH H).lsstHeap ≤ (V.withH H).H := hH1
  obtain ⟨⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ :=
    (V.withH H).frame_places hWH hLBV
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · rw [hfr₈ a (Or.inl ha), hfr₇ a (Or.inl (lt_of_lt_of_le ha f1)),
      FF a (Or.inl (lt_of_lt_of_le ha f2)) (Or.inl (lt_of_lt_of_le ha f3))
        (Or.inl (lt_of_lt_of_le ha f4)) (Or.inl (lt_of_lt_of_le ha f5)),
      DF1 a (lt_of_lt_of_le ha f6) (Or.inl (lt_of_lt_of_le ha f7)),
      OF a (Or.inl (lt_of_lt_of_le ha f8)), TF a (lt_of_lt_of_le ha f9)]
    exact BF a (Or.inl (lt_of_lt_of_le ha f10))
  · rw [hfr₈ a (Or.inr (le_trans g1 ha)), hfr₇ a (Or.inr (le_trans g2 ha)),
      FF a (Or.inr (le_trans g3 ha)) (Or.inr (le_trans g4 ha)) (Or.inr (le_trans g5 ha))
        (Or.inr (le_trans g6 ha)),
      DF2 a (le_trans g7 ha),
      OF a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (le_trans g8 ha))))))))]
    exact hz3 a (le_trans g9 ha)

end

end MinCostFlow.LSF.Program
