module

public import MinCostFlow.LSF.Program.InitWstrOut
public import MinCostFlow.LSF.Program.InitMain
public import MinCostFlow.LSF.Program.InitOrderOut

/-!
# The stretches of the initial state, in the terms of the driver

`init_wstrAt` takes the posts that `main_wp` hands to its final condition, up to the
decomposition phase, and gives `WstrAt` at the static places `numSt`, `denSt` of the state. The
length blocks of the input lie below `b`, which the prep, widths and tree phases keep
(`init_len_facts`); `order_decomp_wstrAt` does the rest. The order is `orderPi` of the order
phase, an edge order by `order_pi_of_posts`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.Num
  InitDriver

@[expose] public section

/-- The length blocks of the input, after the tree phase. -/
lemma init_len_facts {w h : ℕ} {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ} {G₀ : MGraph}
    {v ℓ₀ : ℕ → ℝ} {P_fp : ℕ} {g0Ptr vCap0 eCap0 lenArr wtArr kk cnt H : ℕ}
    {mem mem₁ mem₂ mem₃ : ℕ → ℕ} {vList eList : List ℕ} (V : InitVals)
    (S : SegBIn w h Q_AN c_AN K_AN G₀ v ℓ₀ P_fp V lenArr wtArr kk mem) (hn : G₀.n = V.n0)
    (h₁ : (prepStageContract w G₀).post (prepArgsV V g0Ptr vCap0 eCap0 kk) mem cnt mem₁)
    (h₂ : (widthsContract w).post [V.m0, V.L_in, V.endA + 3] mem₁ 0 mem₂)
    (h₃ : (treePhaseContract Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp vList eList).post
        (treeArgsV V lenArr wtArr) mem₂ H mem₃) :
    ∀ e ∈ G₀.E, Valid mem₃ (lenArr + e * V.L_in) h V.L_in ∧
      fixVal mem₃ (lenArr + e * V.L_in) h V.L_in P_fp = ℓ₀ e ∧ 0 < ℓ₀ e ∧
      lenArr + e * V.L_in + V.L_in ≤ V.tPtr := by
  have hfrB := segB_frame h₁ h₂ hn
  have hfr₃ := tree_frame_low V h₃
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ := V.aux_order
  have hq := V.scratch_order.1
  have hls : lsfHdrSize = 24 := rfl
  intro e he
  have hb := S.hlenB e he
  obtain ⟨hv, hf, hp⟩ := S.hlv e he
  have hag : ∀ i < V.L_in, mem₃ (lenArr + e * V.L_in + i) = mem (lenArr + e * V.L_in + i) :=
    fun i hi => by rw [hfr₃ _ (by omega), hfrB _ (Or.inl (by omega))]
  refine ⟨fun i hi => by rw [hag i hi]; exact hv i hi, ?_, hp, by omega⟩
  rw [← hf]
  simp only [fixVal, intVal]
  rw [unsignedVal_congr hag]

set_option maxHeartbeats 1600000 in
/-- After the decomposition phase of the driver, the arrays at `numSt` and `denSt` represent the
stretches of the initial state of the model, with the threshold `threshProd C n₀ kk`. -/
theorem init_wstrAt {w h C : ℕ} {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ} {G₀ : MGraph}
    {v ℓ₀ : ℕ → ℝ} {P_fp : ℕ} {g0Ptr vCap0 eCap0 lenArr wtArr kk cnt H : ℕ}
    {bRoot bStore bOrder bT bTH bWT bLB bW bCopy bFlag bRoots : ℕ}
    {mem mem₁ mem₂ mem₃ mem₄ mem₅ : ℕ → ℕ} {v₄ v₅ : ℕ} {vList eList : List ℕ} {T_raw : MGraph}
    (V : InitVals)
    (S : SegBIn w h Q_AN c_AN K_AN G₀ v ℓ₀ P_fp V lenArr wtArr kk mem)
    (hn : G₀.n = V.n0) (hm : G₀.E.card = V.m0)
    (hLinw : V.L_in ≤ V.L_w)
    (hθ : threshProd C V.n0 kk < 2 ^ (h * (V.L_w - V.L_in)))
    (h₁ : (prepStageContract w G₀).post (prepArgsV V g0Ptr vCap0 eCap0 kk) mem cnt mem₁)
    (h₂ : (widthsContract w).post [V.m0, V.L_in, V.endA + 3] mem₁ 0 mem₂)
    (heLen : eList.length = V.m0) (heNd : eList.Nodup) (heE : ∀ e, e ∈ eList ↔ e ∈ G₀.E)
    (h₃ : (treePhaseContract Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp vList eList).post
        (treeArgsV V lenArr wtArr) mem₂ H mem₃)
    (IO : OrderPhaseIn w h G₀ (projectTree G₀ v T_raw) vList eList
      (OrderLayout.ofVals (V.withH H) (mem₃ V.outHdr)) mem₃)
    (h₄ : (orderPhaseContract w h G₀ (projectTree G₀ v T_raw) vList eList bRoot bStore bOrder bT
      bTH).post (OrderLayout.ofVals (V.withH H) (mem₃ V.outHdr)).args mem₃ v₄ mem₄)
    (ID : DecompPhaseIn w h C (projectTree G₀ v T_raw) vList
        (DecompLayout.ofVals (V.withH H) (mem₃ V.outHdr) (4 * kk * (hldDepthBound V.n0 + 1))
          (hldDepthBound V.n0) kk lenArr cnt) mem₄)
    (h₅ : (decompPhaseContract w h C bWT bLB bW bCopy bFlag bRoots decompPhaseCost).post
        (DecompLayout.ofVals (V.withH H) (mem₃ V.outHdr) (4 * kk * (hldDepthBound V.n0 + 1))
          (hldDepthBound V.n0) kk lenArr cnt).args mem₄ v₅ mem₅) :
    WstrAt mem₅ V.numSt V.denSt V.eCap h V.L_w G₀
      (initWstr (projectTree G₀ v T_raw) G₀ (vList.getD 0 0)
        (orderPi (OrderLayout.ofVals (V.withH H) (mem₃ V.outHdr)) mem₃ mem₄) (safeLen G₀ ℓ₀)
        (threshProd C V.n0 kk)) := by
  have hπ := (order_pi_of_posts V S hn hm h₁ h₂ heLen heNd heE h₃ IO h₄).1
  have hlen := init_len_facts V S hn h₁ h₂ h₃
  have hhL : 2 ≤ h * V.L_w :=
    le_trans S.h2L (Nat.mul_le_mul_left _ hLinw)
  exact (order_decomp_wstrAt (P := P_fp) IO h₄ ID h₅ hπ heE hlen hhL hθ rfl).1

end

end MinCostFlow.LSF.Program
