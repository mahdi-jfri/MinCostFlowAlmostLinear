module

public import MinCostFlow.LSF.Program.InitSegF

/-!
# Glue between the segments of the init driver

`prepStage` writes the threshold `θ = 4 k (D + 1)` at `endA + 2`, and the fourth segment reads it
after the widths, the tree phase and the order phase. `theta_kept` shows that none of these
writes there: the widths write `endA + 3 … endA + 5`, the tree phase writes from `endA + 6` on,
and the order phase keeps the memory between the end of the aux block and the heap `H`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.WideWord

@[expose] public section

/-- The word `endA + 2` lies between the end of the aux block and the heap. -/
lemma InitVals.theta_place (V : InitVals) (hH : V.lsstHeap ≤ V.H) :
    V.thDst + V.n0 ≤ V.endA + 2 ∧ V.endA + 2 < V.rtOut ∧ V.endA + 2 < V.qNat := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ := V.aux_order
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, -⟩ :=
    V.scratch_order
  refine ⟨by omega, by omega, by omega⟩

/-- The threshold that `prepStage` writes is still at `endA + 2` after the order phase. -/
theorem theta_kept {w h : ℕ} {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ} {G₀ T₀ : MGraph}
    {v ℓ₀ : ℕ → ℝ} {P_fp : ℕ} {g0Ptr vCap0 eCap0 lenArr wtArr kk cnt H nOrig ret : ℕ}
    {bRoot bStore bOrder bT bTH : ℕ}
    {mem mem₁ mem₂ mem₃ mem₄ : ℕ → ℕ} {vList eList vList' eList' : List ℕ} (V : InitVals)
    (hH : V.lsstHeap ≤ V.H)
    (h₁ : (prepStageContract w G₀).post (prepArgsV V g0Ptr vCap0 eCap0 kk) mem cnt mem₁)
    (h₂ : (widthsContract w).post [V.m0, V.L_in, V.endA + 3] mem₁ 0 mem₂)
    (h₃ : (treePhaseContract Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp vList eList).post
        (treeArgsV V lenArr wtArr) mem₂ H mem₃)
    (I : OrderPhaseIn w h G₀ T₀ vList' eList' (OrderLayout.ofVals V nOrig) mem₃)
    (h₄ : (orderPhaseContract w h G₀ T₀ vList' eList' bRoot bStore bOrder bT bTH).post
        (OrderLayout.ofVals V nOrig).args mem₃ ret mem₄) :
    mem₄ (V.endA + 2) = 4 * kk * (hldDepthBound G₀.n + 1) := by
  obtain ⟨t1, t2, t3⟩ := V.theta_place hH
  -- the prep stage
  obtain ⟨g0', vc', ec', k', ax', gp', po', vc0', ec0', vL, rL, heq, -, -, hθ, -⟩ := h₁
  simp only [prepArgsV, List.cons.injEq, and_true] at heq
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, -, -, -, -⟩ := heq
  -- the widths
  obtain ⟨m', L', o', heq₂, -, -, -, -, hfr₂⟩ := h₂
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl⟩ := heq₂
  -- the tree phase
  obtain ⟨mem₁', hcp, hls⟩ := h₃
  rw [treePhaseCopyArgs_treeArgsV] at hcp
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, heqc, -, -, -, -, -, -, -,
    -, -, -, hfrc⟩ := hcp
  simp only [treeCopyArgsV, List.cons.injEq, and_true] at heqc
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl⟩ := heqc
  rw [treePhaseLsstArgs_treeArgsV] at hls
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, heql, -, -, -, -, -,
    hfrl⟩ := hls
  simp only [List.cons.injEq, and_true] at heql
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl⟩ := heql
  -- the order phase
  obtain ⟨_, _, _, _, _, _, _, o₁, o₃, o₄, o₅⟩ := orderPhase_post h₄
  have hfr₄ := (orderPhase_frame I o₁ o₃ o₄ o₅).1
  have hlsH : V.endA + 2 < V.lsstHeap := by
    obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, -⟩ :=
      V.scratch_order
    omega
  rw [hfr₄ _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨t1, t2⟩))))]
  rw [hfrl _ hlsH (Or.inl (by
      obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, -⟩ := V.scratch_order
      omega))
    (Or.inl (by
      obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, -⟩ := V.scratch_order
      omega))]
  rw [hfrc _ t3, hfr₂ _ (Or.inl (by omega))]
  exact hθ

/-- The tree phase keeps the memory below `qNat`. -/
lemma tree_frame_low {w h : ℕ} {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ} {G₀ : MGraph}
    {v ℓ₀ : ℕ → ℝ} {P_fp lenArr wtArr H : ℕ} {mem₂ mem₃ : ℕ → ℕ} {vList eList : List ℕ}
    (V : InitVals)
    (h₃ : (treePhaseContract Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp vList eList).post
        (treeArgsV V lenArr wtArr) mem₂ H mem₃) :
    ∀ a < V.qNat, mem₃ a = mem₂ a := by
  obtain ⟨mem₁', hcp, hls⟩ := h₃
  rw [treePhaseCopyArgs_treeArgsV] at hcp
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, heqc, -, -, -, -, -, -, -,
    -, -, -, hfrc⟩ := hcp
  simp only [treeCopyArgsV, List.cons.injEq, and_true] at heqc
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl⟩ := heqc
  rw [treePhaseLsstArgs_treeArgsV] at hls
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, heql, -, -, -, -, -,
    hfrl⟩ := hls
  simp only [List.cons.injEq, and_true] at heql
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl⟩ := heql
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, -⟩ :=
    V.scratch_order
  intro a ha
  rw [hfrl a (by omega) (Or.inl (by omega)) (Or.inl (by omega))]
  exact hfrc a ha

/-- A block of `wstrLB` limbs that starts below `b` ends below `dBase`. -/
lemma InitVals.lb_le_dBase (V : InitVals) (hH : V.lsstHeap ≤ V.H) (he : 1 ≤ V.eCap) :
    V.b + wstrLB V.n0 (hldDepthBound V.n0) V.L_w ≤ V.dBase := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ := V.aux_order
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19,
    s20, s21, s22, s23, s24, s25, s26, -⟩ := V.scratch_order
  have h1 := Nat.log_lt_self 2 (show V.n0 + 1 ≠ 0 by omega)
  have h2 := Nat.log_lt_self 2 (show hldDepthBound V.n0 + 2 ≠ 0 by omega)
  have h3 : V.L_w ≤ V.eCap * V.L_w := Nat.le_mul_of_pos_left _ he
  simp only [auxSize, auxHdrSize, lsfHdrSize] at e7 e15
  unfold wstrLB
  omega

set_option maxHeartbeats 2000000 in
/-- The facts of `DecompExtra`, from the posts of the second segment. -/
theorem decompExtra_of_segB {w h C : ℕ} {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ} {G₀ : MGraph}
    {v ℓ₀ : ℕ → ℝ} {P_fp : ℕ} {g0Ptr vCap0 eCap0 lenArr wtArr kk cnt nOrig : ℕ}
    {mem mem₁ mem₂ mem₃ : ℕ → ℕ} {vList eList : List ℕ} (V : InitVals)
    (S : SegBIn w h Q_AN c_AN K_AN G₀ v ℓ₀ P_fp V lenArr wtArr kk mem)
    (hn : G₀.n = V.n0) (hn1 : 1 ≤ V.n0) (hnv : V.n0 ≤ V.vCap) (he : 1 ≤ V.eCap) (hH : V.lsstHeap ≤ V.H)
    (hlb : lenArr ≤ V.b) (hLinw : V.L_in ≤ V.L_w) (hC : C < 2 ^ (h * V.L_w))
    (hDw : 2 * (hldDepthBound V.n0 + 1) < 2 ^ w) (hm0w : 2 * V.m0 < 2 ^ w)
    (hLB : wstrLB V.n0 (hldDepthBound V.n0) V.L_w < 2 ^ w) (hkw : kk < 2 ^ w)
    (hL19 : wsPt V.idPtr V.n0 V.tM V.m0 (wstrLB V.n0 (hldDepthBound V.n0) V.L_w) 18 + V.m0 <
      2 ^ w)
    (h₁ : (prepStageContract w G₀).post (prepArgsV V g0Ptr vCap0 eCap0 kk) mem cnt mem₁)
    (h₂ : (widthsContract w).post [V.m0, V.L_in, V.endA + 3] mem₁ 0 mem₂)
    (hvL : ListAt mem₂ V.vListPtr vList) (hvLen : vList.length = V.n0)
    (heNd : eList.Nodup)
    (h₃ : (treePhaseContract Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp vList eList).post
        (treeArgsV V lenArr wtArr) mem₂ V.H mem₃)
    (hz : ZeroFrom mem₃ V.H) :
    ∃ repList, DecompExtra w h C G₀ vList eList repList (OrderLayout.ofVals V nOrig)
      (DecompLayout.ofVals V nOrig (4 * kk * (hldDepthBound V.n0 + 1)) (hldDepthBound V.n0) kk
        lenArr cnt) mem₃ := by
  have hfrB := segB_frame h₁ h₂ hn
  have hfr₃ := tree_frame_low V h₃
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ := V.aux_order
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19,
    s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, -⟩ := V.scratch_order
  have hLBd := V.lb_le_dBase hH he
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := V.segB_le
  have hls : lsfHdrSize = 24 := rfl
  have hax : auxHdrSize = 20 := rfl
  have hrp : V.repPtr + V.vCap ≤ V.auxPtr + auxSize V.vCap V.n0 := e6
  obtain ⟨g0', vc', ec', k', ax', gp', po', vc0', ec0', vL', repList, heq, -, -, -, hdg₁, hvLen',
    -, hvV, hvL', -, -, -, -, -, hc1, hcn, hrl, -, hr0, hrA, hrep, -⟩ := h₁
  simp only [prepArgsV, List.cons.injEq, and_true] at heq
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, -, -, -, -⟩ := heq
  obtain ⟨m', L', o', heq₂, -, -, -, -, hfr₂⟩ := h₂
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl⟩ := heq₂
  -- the vertex list of `prepStage` is `vList`
  have hvEq : vL' = vList := by
    refine listAt_unique (fun i hi => ?_) hvL (by rw [hvLen', hvLen, hn])
    rw [hfr₂ _ (Or.inl (by rw [hvLen', hn] at hi; omega))]
    exact hvL' i hi
  subst vL'
  rw [hn] at hcn hrA
  have hrepP : auxQBufBBase V.auxPtr V.vCap V.n0 = V.repPtr := rfl
  rw [hrepP] at hrA
  refine ⟨repList, ?_⟩
  exact {
    hLin1 := S.hLin
    hLinw := hLinw
    hC := hC
    hD := rfl
    hDw := hDw
    hθ := Nat.mul_pos (Nat.mul_pos (by norm_num) S.hk) (Nat.succ_pos _)
    hθw := S.hkw
    hm0w := hm0w
    hLB := hLB
    hk := hkw
    hlenG := fun e he' => by
      have hb := S.hlenB e he'
      have hv := (S.hlv e he').1
      have hbq : V.b < V.qNat := by omega
      have hbg : V.b < V.gPtr := by omega
      refine ⟨fun i hi => ?_, ?_, ?_, ?_⟩
      · have hi' : i < V.L_in := hi
        show mem₃ (lenArr + e * V.L_in + i) < _
        rw [hfr₃ _ (by omega), hfrB _ (Or.inl (by omega))]
        exact hv i hi
      · exact hdg₁.2.2.1 e he'
      · show lenArr + e * V.L_in + V.L_in ≤ V.tPtr
        omega
      · show lenArr + e * V.L_in + wstrLB V.n0 (hldDepthBound V.n0) V.L_w ≤ V.dBase
        omega
    heNd := heNd
    hrepAt := fun j hj => by
      show mem₃ (V.repPtr + j) = _
      have hjn : j < V.n0 := by omega
      rw [hfr₃ _ (by omega), hfr₂ _ (Or.inl (by omega))]
      exact hrA j hj
    hrepLen := hrl
    hrepV := fun u hu => (hvV u).mpr (hrep.2.1 (List.mem_toFinset.mpr hu))
    hrep0 := hr0
    hcnt := hc1
    hrepLay := ⟨by show V.thDst + V.n0 ≤ V.repPtr; omega,
      by show V.repPtr + cnt ≤ V.rtOut; omega⟩
    hzD := fun a ha _ => hz a (by show V.H ≤ a; simp only [DecompLayout.ofVals,
      DecompLayout.ofOrder] at ha; omega)
    L1 := by show lenArr + wstrLB V.n0 (hldDepthBound V.n0) V.L_w ≤ V.dBase; omega
    L10 := by show V.thBase + 8 * V.n0 ≤ V.dBase; omega
    L12s := by show V.tPtr ≤ V.numSt; omega
    L13 := by show V.numSt + V.eCap * V.L_w ≤ V.denSt; omega
    L14 := by show V.denSt + V.eCap * V.L_w ≤ V.dBase; omega
    L15 := by show V.dBase + 12 * V.n0 ≤ V.hiCopy; omega
    L16 := by show V.hiCopy + V.m0 ≤ V.inR; omega
    L17 := by show V.inR + 3 * V.n0 + V.tM ≤ V.numS; omega
    L18 := by show V.numS + 2 * (V.eCap * V.L_w) ≤ V.idPtr; omega
    L19 := hL19 }

/-- After the order phase, the edge IDs in the `T` block are the IDs that the tree phase wrote. -/
theorem order_tOrigId {w h : ℕ} {G₀ T₀ : MGraph} {vList eList : List ℕ} {X : OrderLayout}
    {mem mem₁ mem₃ mem₄ mem₅ : ℕ → ℕ} {v₁ v₃ v₄ v₅ : ℕ}
    (I : OrderPhaseIn w h G₀ T₀ vList eList X mem)
    (h₁ : (rootStageContract w).post
        [X.n, X.tM, X.tTail, X.tHead, 0, X.rtOut, X.sPtr, X.auxPar, X.logCap] mem v₁ mem₁)
    (h₃ : (orderStageContract w h G₀ vList eList).post
        [X.n, 0, X.m0, dgEListBase X.gPtr X.vCap X.eCap, dgETailSlotBase X.gPtr X.vCap X.eCap,
          dgEHeadSlotBase X.gPtr X.vCap X.eCap, dgIntToExtBase X.gPtr X.vCap, X.vIdx, X.eu, X.ev,
          X.qPtr, X.Kq, X.dPtr, X.K, X.tmpPtr, X.logCap, X.auxPar + 3 * X.n,
          X.auxPar + X.n + X.n, X.auxPar, X.qOrd, X.auxPar + X.n, X.arrPtr, X.scratchPtr,
          tPiBase X.tPtr X.vCap X.tM, X.minPtr]
        (Function.update mem₁ (X.auxPar + X.n) 0) v₃ mem₃)
    (h₄ : (tStageContract w G₀ T₀ vList).post [X.tPtr, X.vCap, X.eCap, X.tM, X.vListPtr,
        X.tOrigSrc, X.tTail, X.tHead, X.n, X.nOrig, tOrigIdBase X.tPtr X.vCap X.tM,
        tDgTPtr X.tPtr] mem₃ v₄ mem₄)
    (h₅ : (thStageContract w T₀ vList).post
        [X.n, X.qOrd, X.auxPar, X.auxPar + X.n + X.n, X.thBase, 0, X.thDst] mem₄ v₅ mem₅) :
    ∀ i < X.tM, mem₅ (tOrigIdBase X.tPtr X.vCap X.tM + i) = mem (X.tOrigSrc + i) := by
  obtain ⟨hFr, -, -, h53, hTB, -⟩ := orderPhase_frame I h₁ h₃ h₄ h₅
  have hn := I.hn2
  have l1 := I.l1; have l2 := I.l2; have l3 := I.l3; have l4 := I.l4; have l5 := I.l5
  have l6 := I.l6; have l7 := I.l7; have l8 := I.l8; have l9 := I.l9; have l10 := I.l10
  have l11 := I.l11; have l12 := I.l12; have l13 := I.l13; have l14 := I.l14; have l15 := I.l15
  have l16 := I.l16; have l17 := I.l17; have l18 := I.l18; have hmin := I.hmin
  obtain ⟨ht1, ht2⟩ := I.tPi_le
  have htt : X.tPtr ≤ tOrigIdBase X.tPtr X.vCap X.tM := by
    simp only [tOrigIdBase, tDgTPtr]; omega
  have htb : tPiBase X.tPtr X.vCap X.tM + X.tM ≤ X.tPtr + tBlockSize X.vCap X.eCap X.tM := by
    simp only [tPiBase, tOrigIdBase, tDgTPtr, tBlockSize]; omega
  have ht0 : tOrigIdBase X.tPtr X.vCap X.tM + X.tM = tPiBase X.tPtr X.vCap X.tM := rfl
  obtain ⟨_, _, _, _, _, _, _, _, _, _, heq₄, -, hTBA, -, -⟩ := h₄
  simp only [List.cons.injEq, and_true] at heq₄
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, -, -⟩ := heq₄
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hIdAt, -⟩ := hTBA
  intro i hi
  have h1 := hIdAt i (by simp [tStageList]; omega)
  simp only [tStageList, List.getElem_map, List.getElem_range] at h1
  rw [hTB _ (by omega) (by omega), h1, ← h53 _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)),
    hFr _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))]

/-- The places that `FExtra` compares. -/
lemma InitVals.fExtra_layout (V : InitVals) (hH : V.lsstHeap ≤ V.H) :
    tOrigIdBase V.tPtr V.vCap V.tM + V.tM ≤ V.fPtr ∧
    V.fPtr + dynGraphSize V.vCap (fECap V.eCap V.n0) = V.fAncPtr ∧
    V.fAncPtr + fAncSize V.vCap = V.wPtr ∧ V.wPtr + wBlockSize V.n0 = V.auxPtr ∧
    V.auxPtr ≤ V.vListPtr ∧ V.vListPtr + V.n0 ≤ V.auxPar ∧
    V.auxPar + 3 * V.n0 + V.n0 * auxLogCap V.n0 ≤ V.thDst ∧ V.thDst + V.n0 ≤ V.numSt ∧
    V.numSt + V.eCap * V.L_w = V.denSt ∧ V.denSt + V.eCap * V.L_w = V.endA ∧
    V.endA + 6 ≤ V.tTail ∧ V.tTail + V.n0 = V.tHead ∧ V.tHead + V.n0 ≤ V.H ∧
    V.H + 3 * V.n0 ≤ V.thBase ∧ V.thBase + 8 * V.n0 ≤ V.dBase ∧
    V.tPtr + tBlockSize V.vCap V.eCap V.tM = V.fPtr := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ := V.aux_order
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19,
    s20, s21, s22, s23, s24, s25, s26, -⟩ := V.scratch_order
  have hmin := V.minPtr_eq
  have htb : tBlockSize V.vCap V.eCap V.tM = tHdrSize + dynGraphSize V.vCap (2 * V.tM + 1) +
      4 * V.tM + V.eCap + (4 + 2 * V.tM) := rfl
  have ht : tOrigIdBase V.tPtr V.vCap V.tM = V.tPtr + tHdrSize + dynGraphSize V.vCap (2 * V.tM + 1) :=
    rfl
  have hax : auxHdrSize = 20 := rfl
  have hvI : V.vIdx = V.auxPtr + auxHdrSize := rfl
  refine ⟨by omega, e11, e12, e10, by omega, e3.le, by omega, by omega, e8, e9, by omega, s15,
    by omega, by omega, s26.le, e13⟩

/-- `FExtra` on the memory after the order phase. The IDs of the tree edges must be below the
edge capacity `fECap eCap n₀` of the `F` graph (`hTE`). -/
theorem fExtra_of_order {w h : ℕ} {G₀ T₀ : MGraph} {vList eList : List ℕ}
    {bRoot bStore bOrder bT bTH nOrig θ D kk lenArr cnt ret : ℕ} {mem₃ mem₄ : ℕ → ℕ}
    (V : InitVals)
    (I : OrderPhaseIn w h G₀ T₀ vList eList (OrderLayout.ofVals V nOrig) mem₃)
    (h₄ : (orderPhaseContract w h G₀ T₀ vList eList bRoot bStore bOrder bT bTH).post
        (OrderLayout.ofVals V nOrig).args mem₃ ret mem₄)
    (hH : V.lsstHeap ≤ V.H) (hzF : ∀ a, V.fPtr ≤ a → a < V.wPtr → mem₃ a = 0)
    (hz : ZeroFrom mem₃ V.H) (hnv : V.n0 ≤ V.vCap) (hTE : ∀ f ∈ T₀.E, f < fECap V.eCap V.n0)
    (hLB : V.LB = wstrLB V.n0 D V.L_w) (hU : V.useEnd < 2 ^ w) :
    FExtra w (DecompLayout.ofVals V nOrig θ D kk lenArr cnt) V.fPtr V.vListPtr V.tTail V.tHead
      V.fAncPtr V.wBase V.wPtr mem₄ := by
  obtain ⟨v₁, mem₁, v₃, mem₃', v₄, mem₄', v₅, o₁, o₃, o₄, o₅⟩ := orderPhase_post h₄
  have hFr := (orderPhase_frame I o₁ o₃ o₄ o₅).1
  have hid : ∀ i < V.tM, mem₄ (tOrigIdBase V.tPtr V.vCap V.tM + i) = mem₃ (V.tOrig + i) :=
    order_tOrigId I o₁ o₃ o₄ o₅
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16⟩ :=
    V.fExtra_layout hH
  have hn := I.hn2
  have hvlen : vList.length = V.n0 := I.hvlen
  have htM : V.tM ≤ V.n0 := Nat.sub_le _ _
  have hw0 : V.wBase ≥ V.thBase + 8 * V.n0 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, s26, s27,
      s28, s29, s30, s31, s32⟩ := V.scratch_order
    omega
  -- the region of the aux block below `auxPar` and the `F` blocks are kept
  have k2 : ∀ a, V.fPtr ≤ a → a < V.auxPar → mem₄ a = mem₃ a := fun a h1 h2 =>
    hFr a (Or.inr (Or.inl ⟨by show V.tPtr + tBlockSize V.vCap V.eCap V.tM ≤ a; omega, h2⟩))
  have hvAt : ListAt mem₃ V.vListPtr vList := I.hvLA
  refine
    { hnv := hnv
      hnL := by
        show V.n0 < 2 ^ auxLogCap V.n0
        unfold auxLogCap
        have := Nat.lt_pow_succ_log_self (b := 2) (by decide) (V.n0 + 1)
        omega
      hzG := fun i hi => by
        have hi' : i < dynGraphSize V.vCap (fECap V.eCap V.n0) := hi
        rw [k2 _ (by omega) (by omega)]
        exact hzF _ (by omega) (by have : fAncSize V.vCap = 6 + 5 * V.vCap := rfl; omega)
      hzA := fun i hi => by
        have hi' : i < fAncSize V.vCap := hi
        rw [k2 _ (by omega) (by omega)]
        exact hzF _ (by omega) (by omega)
      hzW := fun y hy => by
        show mem₄ (V.wBase + V.n0 * (3 * auxLogCap V.n0) + 2 * V.n0 + y) = 0
        rw [hFr _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (show V.thBase + 8 * V.n0 ≤ _ by omega))))))))]
        exact hz _ (by omega)
      hvL := fun x hx => by
        have hx' : x < V.n0 := hx
        rw [k2 _ (by omega) (by omega), hvAt x (by omega)]
        exact I.hvCap _ (List.getElem_mem _)
      hvInj := fun x hx y hy hxy => by
        have hx' : x < V.n0 := hx
        have hy' : y < V.n0 := hy
        rw [k2 _ (by omega) (by omega), k2 _ (by omega) (by omega), hvAt x (by omega),
          hvAt y (by omega)] at hxy
        exact (I.hnd.getElem_inj_iff).mp hxy
      hT := fun i hi => by
        have hi' : i < V.tM := hi
        have r4 : ∀ a, V.tTail ≤ a → a < V.tHead + V.n0 → mem₄ a = mem₃ a := fun a h1 h2 =>
          hFr a (Or.inr (Or.inr (Or.inr (Or.inl ⟨by show V.thDst + V.n0 ≤ a; omega,
            by show a < V.H; omega⟩))))
        refine ⟨?_, ?_, ?_⟩
        · show mem₄ (V.tTail + i) < V.n0
          rw [r4 _ (by omega) (by omega), ← hvlen]
          exact I.hA.tl_lt i hi
        · show mem₄ (V.tHead + i) < V.n0
          rw [r4 _ (by omega) (by omega), ← hvlen]
          exact I.hA.hd_lt i hi
        · show mem₄ (tOrigIdBase V.tPtr V.vCap V.tM + i) < fECap V.eCap V.n0
          rw [hid i hi]
          exact hTE _ (I.hA.fid_mem i hi)
      m1 := m1
      m2 := m2.le
      m3 := m3.le
      m4 := by show V.wPtr + wBlockSize V.n0 ≤ V.numSt; omega
      m5 := Or.inl (by show V.vListPtr + V.n0 ≤ V.numSt; omega)
      m6 := Or.inr (by show V.denSt + V.eCap * V.L_w ≤ V.tTail; omega)
      m7 := Or.inr (by show V.denSt + V.eCap * V.L_w ≤ V.tHead; omega)
      m8 := Or.inl (by
        show V.auxPar + 2 * V.n0 ≤ V.numSt
        omega)
      m9 := by show V.vListPtr + V.n0 ≤ V.dBase; omega
      m10 := by show V.tTail + V.tM ≤ V.dBase; omega
      m11 := by show V.tHead + V.tM ≤ V.dBase; omega
      m12 := by
        show wsPt V.idPtr V.n0 V.tM V.m0 (wstrLB V.n0 D V.L_w) 18 + V.m0 ≤ V.wBase
        rw [← hLB]; exact le_rfl
      m13 := hU
      m14 := by show V.wPtr + wBlockSize V.n0 ≤ V.vListPtr; omega
      m15 := by show V.wPtr + wBlockSize V.n0 ≤ V.tTail; omega
      m16 := by show V.wPtr + wBlockSize V.n0 ≤ V.tHead; omega
      m17 := by show V.wPtr + wBlockSize V.n0 ≤ V.auxPar; omega }

/-- The heap that the tree phase returns lies between `lsstHeap` and `lsstHeap` plus the space of
the `[AN19]` call for `2 m₀` copies, and memory is zero from there on. -/
lemma tree_ret {w h : ℕ} {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ} {G₀ : MGraph}
    {v ℓ₀ : ℕ → ℝ} {P_fp lenArr wtArr H : ℕ} {mem₂ mem₃ : ℕ → ℕ} {vList eList : List ℕ}
    (V : InitVals) (hh : 1 ≤ h) (hLin : 1 ≤ V.L_in)
    (h₃ : (treePhaseContract Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp vList eList).post
        (treeArgsV V lenArr wtArr) mem₂ H mem₃) :
    V.lsstHeap ≤ H ∧
      H ≤ V.lsstHeap + lsstSpace Q_AN K_AN V.n0 (2 * V.m0)
        (lsstLSimMin c_AN 0 (2 * V.m0) V.L_in h) h ∧ ZeroFrom mem₃ H := by
  obtain ⟨mem₁', hcp, hls⟩ := h₃
  rw [treePhaseCopyArgs_treeArgsV] at hcp
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, heqc, -, hMle, -⟩ := hcp
  simp only [treeCopyArgsV, List.cons.injEq, and_true] at heqc
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl⟩ := heqc
  rw [treePhaseLsstArgs_treeArgsV] at hls
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, heql, hlo, hhi, hz, -⟩ := hls
  simp only [List.cons.injEq, and_true] at heql
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl⟩ := heql
  have hLs1 : 1 ≤ lsstLSimMin c_AN 0 (2 * V.m0) V.L_in h :=
    le_trans (by unfold kWidthOf; omega) (le_max_left _ _)
  have hM : treePhaseM G₀ v vList eList ≤ 2 * V.m0 := hMle
  have hsp := lsstSpace_mono_m (Q_AN := Q_AN) (K_AN := K_AN) (n := V.n0) hLs1 hh hM
  exact ⟨hlo, hhi.trans (Nat.add_le_add_left hsp _), hz⟩

end

end MinCostFlow.LSF.Program
