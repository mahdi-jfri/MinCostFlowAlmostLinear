module

public import MinCostFlow.LSF.Program.InitKeep

/-!
# The `T` block of the initial state

The tree stage of the order phase writes the `T` block. Its post states `TBlockAt` with the
order read from the block right after the stage, and with the edge IDs read from the scratch
array at that time. The model's order is `orderPi`, read after the whole order phase, with the
IDs read at the start of the phase. The two agree: the scratch array of IDs is kept by the
rooting and order calls, and the last call of the phase, the `T_H` stage, keeps the `T` block.
`TBlockAt` reads the order only on the edges of its list (`TBlockAt.congr_pi`), and for such an
edge the rank lies inside the block. So `order_tBlockAt` gives `TBlockAt` after the order phase
with the model's order. The decomposition phase writes only above `dBase` and at the stretch
arrays, and the forest phase and the headers keep `[gPtr, fPtr)` (`init_tail_frame`). So
`init_tBlockAt` gives `TBlockAt` at the end of the driver.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.Num
  InitDriver

@[expose] public section

/-- `TBlockAt` depends on the order only through its values on the edge list. -/
lemma TBlockAt.congr_pi {mem : ℕ → ℕ} {tPtr vCap eCap tM : ℕ} {G T_cur T₀ : MGraph}
    {π π' : ℕ → ℕ} {tOrigList : List ℕ}
    (h : TBlockAt mem tPtr vCap eCap tM G T_cur T₀ π tOrigList)
    (hπ : ∀ f ∈ tOrigList, π f = π' f) :
    TBlockAt mem tPtr vCap eCap tM G T_cur T₀ π' tOrigList := by
  have hm : tOrigList.map π = tOrigList.map π' := List.map_congr_left hπ
  unfold TBlockAt at h ⊢
  rw [← hm]
  exact h

/-- After the order phase, the `T` block represents `T₀` with the order `orderPi` and the edge
IDs of the scratch array at the start of the phase. -/
theorem order_tBlockAt {w h : ℕ} {G₀ T₀ : MGraph} {vList eList : List ℕ} {X : OrderLayout}
    {bRoot bStore bOrder bT bTH : ℕ} {mem mem₅ : ℕ → ℕ} {ret : ℕ}
    (I : OrderPhaseIn w h G₀ T₀ vList eList X mem)
    (hpost : (orderPhaseContract w h G₀ T₀ vList eList bRoot bStore bOrder bT bTH).post X.args
      mem ret mem₅) :
    TBlockAt mem₅ X.tPtr X.vCap X.eCap X.tM G₀ T₀ T₀ (orderPi X mem mem₅)
      (tStageList mem X.tOrigSrc X.tM) := by
  obtain ⟨v₁, mem₁, v₃, mem₃, v₄, mem₄, v₅, h₁, h₃, h₄, h₅⟩ := orderPhase_post hpost
  obtain ⟨hFr, -, -, h53, hTB, -⟩ := orderPhase_frame I h₁ h₃ h₄ h₅
  have hn := I.hn2
  have l1 := I.l1; have l2 := I.l2; have l3 := I.l3; have l4 := I.l4; have l5 := I.l5
  have l6 := I.l6; have l7 := I.l7; have l8 := I.l8; have l9 := I.l9; have l10 := I.l10
  have l11 := I.l11; have l12 := I.l12; have l13 := I.l13; have l14 := I.l14; have l15 := I.l15
  have l16 := I.l16; have l17 := I.l17; have l18 := I.l18; have hmin := I.hmin
  -- the scratch array of IDs is the same at the start of the phase and before the tree stage
  have hsrc : ∀ i < X.tM, mem₃ (X.tOrigSrc + i) = mem (X.tOrigSrc + i) := fun i hi => by
    rw [← h53 _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)),
      hFr _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))]
  have hL : tStageList mem₃ X.tOrigSrc X.tM = tStageList mem X.tOrigSrc X.tM := by
    unfold tStageList
    exact List.map_congr_left fun i hi => hsrc i (List.mem_range.mp hi)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, heq₄, -, hTBA, -, -⟩ := h₄
  simp only [List.cons.injEq, and_true] at heq₄
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, -, -⟩ := heq₄
  rw [hL] at hTBA
  refine (hTBA.of_agree hTB).congr_pi fun f hf => ?_
  have hlt : (tStageList mem X.tOrigSrc X.tM).idxOf f < X.tM := by
    have := List.idxOf_lt_length_of_mem hf
    simpa [tStageList] using this
  unfold orderPi tStagePi
  exact (hTB _ (by simp only [tPiBase, tOrigIdBase, tDgTPtr]; omega)
    (by simp only [tPiBase, tOrigIdBase, tDgTPtr, tBlockSize]; omega)).symm

/-- At the end of the driver, the `T` block represents `T₀` with the model's order. -/
theorem init_tBlockAt {w h C : ℕ} {G₀ T₀ : MGraph} {vList eList : List ℕ} {V : InitVals}
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
    TBlockAt mem₈ V.tPtr V.vCap V.eCap V.tM G₀ T₀ T₀
      (orderPi (OrderLayout.ofVals (V.withH H) nOrig) mem₃ mem₄) (tStageList mem₃ V.tOrig V.tM) := by
  have hT₄ := order_tBlockAt IO h₄
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
  have hT₅ : TBlockAt mem₅ V.tPtr V.vCap V.eCap V.tM G₀ T₀ T₀
      (orderPi (OrderLayout.ofVals (V.withH H) nOrig) mem₃ mem₄)
      (tStageList mem₃ V.tOrig V.tM) :=
    hT₄.of_agree fun a (ha1 : V.tPtr ≤ a)
      (ha2 : a < V.tPtr + tBlockSize V.vCap V.eCap V.tM) => F1 a (by omega) (Or.inl (by omega))
  exact hT₅.of_agree fun a ha1 ha2 => hfr a (Or.inl ⟨by
    show V.gPtr ≤ a; omega, by show a < V.fPtr; omega⟩)

end

end MinCostFlow.LSF.Program
