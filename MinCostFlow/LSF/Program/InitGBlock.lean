module

public import MinCostFlow.LSF.Program.InitTBlock

/-!
# The `G` block of the initial state, and the size of `T₀`

The prep stage copies `G₀` into the `G` block at `gPtr`, and the order phase reads it there
(`OrderPhaseIn.hdg`). `init_gBlockAt` follows the block to the end of the driver: the order
phase writes only from `tPtr` on, the decomposition phase only from `numSt` on or above
`dBase`, and the forest phase and the two header stores keep `[gPtr, fPtr)`
(`init_tail_frame`). `init_tCard` counts the edges of `T₀`: it is a spanning tree on the
`n₀` vertices of `vList`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.Num
  InitDriver

@[expose] public section

/-- At the end of the driver, the `G` block represents `G₀`. -/
theorem init_gBlockAt {w h C : ℕ} {G₀ T₀ : MGraph} {vList eList : List ℕ} {V : InitVals}
    {H nOrig kk lenArr cnt : ℕ} {bRoot bStore bOrder bT bTH bWT bLB bW bCopy bFlag bRoots : ℕ}
    {bG bA bWF : ℕ} {mem₃ mem₄ mem₅ mem₆ mem₇ mem₈ : ℕ → ℕ} {v₄ v₅ v₆ v₇ v₈ : ℕ}
    {vs₇ vs₈ : List ℕ}
    (IO : OrderPhaseIn w h G₀ T₀ vList eList (OrderLayout.ofVals (V.withH H) nOrig) mem₃)
    (h₄ : (orderPhaseContract w h G₀ T₀ vList eList bRoot bStore bOrder bT bTH).post
      (OrderLayout.ofVals (V.withH H) nOrig).args mem₃ v₄ mem₄)
    (ID : DecompPhaseIn w h C T₀ vList
        (DecompLayout.ofVals (V.withH H) nOrig (4 * kk * (hldDepthBound V.n0 + 1))
          (hldDepthBound V.n0) kk lenArr cnt) mem₄)
    (h₅ : (decompPhaseContract w h C bWT bLB bW bCopy bFlag bRoots decompPhaseCost).post
        (DecompLayout.ofVals (V.withH H) nOrig (4 * kk * (hldDepthBound V.n0 + 1))
          (hldDepthBound V.n0) kk lenArr cnt).args mem₄ v₅ mem₅)
    (h₆ : (fPhaseContract w h bG bA bWF).post
      (FLayout.ofVals (V.withH H) nOrig (4 * kk * (hldDepthBound V.n0 + 1))
          (hldDepthBound V.n0) kk lenArr cnt).args mem₅ v₆ mem₆)
    (h₇ : (storeArgsContract w 20).post (V.auxPtr :: vs₇) mem₆ v₇ mem₇)
    (h₈ : (storeArgsContract w 24).post (V.b :: vs₈) mem₇ v₈ mem₈) (hH : V.lsstHeap ≤ H) :
    DynGraphAt mem₈ V.gPtr V.vCap V.eCap G₀ := by
  obtain ⟨u₁, m₁, u₃, m₃, u₄, m₄, u₅, o₁, o₃, o₄, o₅⟩ := orderPhase_post h₄
  have hFr := (orderPhase_frame IO o₁ o₃ o₄ o₅).1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩ := decompPhase_post h₅
  have F1 : ∀ a < (V.withH H).dBase, (a < V.numSt ∨ V.denSt + V.eCap * V.L_w ≤ a) →
      mem₅ a = mem₄ a := (decompPhase_frame ID q₁ q₂ q₃ q₄ q₅ q₆ q₇).1
  have L12 : V.vIdx + V.vCap ≤ (V.withH H).dBase := ID.L12
  have hfr := init_tail_frame (V := V.withH H) h₆ h₇ h₈ hH
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ := V.aux_order
  have hax : V.auxPtr ≤ V.numSt := by
    have h20' : auxHdrSize = 20 := rfl
    have : 20 ≤ auxSize V.vCap V.n0 := by simp only [auxSize]; omega
    omega
  have hG₃ : DynGraphAt mem₃ V.gPtr V.vCap V.eCap G₀ := IO.hdg
  have hG₄ : DynGraphAt mem₄ V.gPtr V.vCap V.eCap G₀ :=
    hG₃.of_agree fun a _ ha2 => hFr a (Or.inl (show a < V.tPtr by omega))
  have hG₅ : DynGraphAt mem₅ V.gPtr V.vCap V.eCap G₀ :=
    hG₄.of_agree fun a _ ha2 => F1 a (by omega) (Or.inl (by omega))
  exact hG₅.of_agree fun a ha1 ha2 => hfr a (Or.inl ⟨by
    show V.gPtr ≤ a; omega, by show a < V.fPtr; omega⟩)

/-- The tree `T₀` of the order phase has `n₀ - 1` edges. -/
lemma init_tCard {w h : ℕ} {G₀ T₀ : MGraph} {vList eList : List ℕ} {V : InitVals}
    {H nOrig : ℕ} {mem₃ : ℕ → ℕ}
    (IO : OrderPhaseIn w h G₀ T₀ vList eList (OrderLayout.ofVals (V.withH H) nOrig) mem₃) :
    T₀.E.card = V.tM := by
  have h1 : T₀.E.card + 1 = T₀.V.card := spanningTree_edge_card IO.hT.1 ⟨_, IO.hT.2⟩
  have h2 : T₀.V = vList.toFinset := by
    ext u; rw [List.mem_toFinset]; exact IO.hV u
  have h3 : vList.toFinset.card = vList.length := List.toFinset_card_of_nodup IO.hnd
  have h4 : vList.length = V.n0 := IO.hvlen
  rw [h2, h3, h4] at h1
  show T₀.E.card = V.n0 - 1
  omega

end

end MinCostFlow.LSF.Program
