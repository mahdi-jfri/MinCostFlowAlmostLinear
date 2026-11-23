module

public import MinCostFlow.LSF.Program.InitSegB
public import MinCostFlow.LSF.Program.OrderPhasePre
public import MinCostFlow.LSF.Lemma54InitBase

/-!
# From the tree phase to the order phase, in the init driver

`orderIn_of_segB` shows that the memory after the second segment satisfies `OrderPhaseIn` at the
places `OrderLayout.ofVals V nOrig`, where `nOrig` is the number that the tree phase writes at
`outHdr`, and the tree `T₀` is `projectTree G₀ v T_raw` for the low-stretch tree `T_raw` of the
copy graph.

The memory went through four calls: `prepStage`, `widths`, the copies and the `[AN19]` stage.
Each fact is read at the call that wrote it and carried to the end through the frames of the later
calls. The places are in order by `OrderLayout.ofVals_layout`, which only uses the definitions of
the places and `lsstHeap ≤ H`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.WideWord
  MinCostFlow.Num

@[expose] public section

/-- The layout part of `OrderPhaseIn` at the places of the driver. -/
lemma OrderLayout.ofVals_layout (V : InitVals) (nOrig : ℕ) (hH : V.lsstHeap ≤ V.H) :
    let X := OrderLayout.ofVals V nOrig
    X.gPtr + dynGraphSize X.vCap X.eCap ≤ X.tPtr ∧
    X.tPtr + tBlockSize X.vCap X.eCap X.tM ≤ X.vIdx ∧ X.vIdx + X.vCap ≤ X.vListPtr ∧
    X.vListPtr + X.n ≤ X.auxPar ∧ X.minPtr + X.n * X.logCap ≤ X.thDst ∧
    X.thDst + X.n ≤ X.qPtr ∧ X.qPtr + X.m0 * X.Kq ≤ X.tOrigSrc ∧ X.tOrigSrc + X.tM ≤ X.tTail ∧
    X.tTail + X.tM ≤ X.tHead ∧ X.tHead + X.tM ≤ X.rtOut ∧ X.rtOut + 3 * X.n ≤ X.sPtr ∧
    X.sPtr + 4 * X.n + 2 * X.tM ≤ X.eu ∧ X.eu + X.m0 ≤ X.ev ∧ X.ev + X.m0 ≤ X.dPtr ∧
    X.dPtr + X.n * X.K ≤ X.tmpPtr ∧ X.tmpPtr + X.K ≤ X.arrPtr ∧ X.arrPtr + X.n ≤ X.scratchPtr ∧
    X.scratchPtr + X.n ≤ X.thBase := by
  intro X
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ := V.aux_order
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19,
    s20, s21, s22, s23, s24, s25, -⟩ := V.scratch_order
  have htM : V.tM ≤ V.n0 := by simp only [InitVals.tM]; omega
  simp only [X, OrderLayout.ofVals]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- The graph block of the tree lies between the graph block of `G₀` and the aux block. -/
lemma InitVals.tDg_le (V : InitVals) :
    V.gPtr + dynGraphSize V.vCap V.eCap ≤ tDgTPtr V.tPtr ∧
    tDgTPtr V.tPtr + dynGraphSize V.vCap (2 * V.tM + 1) ≤ V.auxPtr := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ := V.aux_order
  have htb : tBlockSize V.vCap V.eCap V.tM = tHdrSize + dynGraphSize V.vCap (2 * V.tM + 1) +
      4 * V.tM + V.eCap + (4 + 2 * V.tM) := rfl
  have ht : tDgTPtr V.tPtr = V.tPtr + tHdrSize := rfl
  constructor <;> omega

/-- The `idxOfEdge` table of the `T` block lies between the graph block of `G₀` and the aux block. -/
lemma InitVals.tIdx_le (V : InitVals) :
    V.gPtr + dynGraphSize V.vCap V.eCap ≤ tIdxOfEdgeBase V.tPtr V.vCap V.tM ∧
    tIdxOfEdgeBase V.tPtr V.vCap V.tM + V.eCap ≤ V.auxPtr := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ := V.aux_order
  have htb : tBlockSize V.vCap V.eCap V.tM = tHdrSize + dynGraphSize V.vCap (2 * V.tM + 1) +
      4 * V.tM + V.eCap + (4 + 2 * V.tM) := rfl
  have hidx : tIdxOfEdgeBase V.tPtr V.vCap V.tM =
      V.tPtr + tHdrSize + dynGraphSize V.vCap (2 * V.tM + 1) + 4 * V.tM := by
    simp only [tIdxOfEdgeBase, tFrozenHeadBase, tFrozenTailBase, tPiBase, tOrigIdBase, tDgTPtr]
    omega
  constructor <;> omega

/-- Places below `qNat` that `prepStage` and `widths` do not write keep their value through the
second segment. -/
lemma segB_frame {w : ℕ} {G₀ : MGraph} {V : InitVals} {g0Ptr vCap0 eCap0 kk cnt : ℕ}
    {mem mem₁ mem₂ : ℕ → ℕ}
    (h₁ : (prepStageContract w G₀).post (prepArgsV V g0Ptr vCap0 eCap0 kk) mem cnt mem₁)
    (h₂ : (widthsContract w).post [V.m0, V.L_in, V.endA + 3] mem₁ 0 mem₂) (hn : G₀.n = V.n0) :
    ∀ a, (a < V.gPtr ∨ (V.gPtr + dynGraphSize V.vCap V.eCap ≤ a ∧ a < V.auxPtr) ∨
      V.endA + 6 ≤ a) → mem₂ a = mem a := by
  obtain ⟨g0', vc', ec', k', ax', gp', po', vc0', ec0', vList', repList, heq, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, hfr₁⟩ := h₁
  simp only [prepArgsV, List.cons.injEq, and_true] at heq
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, -, -, -, -⟩ := heq
  obtain ⟨m', L', o', heq₂, -, -, -, -, hfr₂⟩ := h₂
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl⟩ := heq₂
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := V.segB_le
  intro a ha
  rw [hn] at hfr₁
  rcases ha with ha | ⟨ha1, ha2⟩ | ha
  · rw [hfr₂ a (Or.inl (by omega))]
    exact hfr₁ a (Or.inl ha) (Or.inl (by omega)) (Or.inl (by omega))
  · rw [hfr₂ a (Or.inl (by omega))]
    exact hfr₁ a (Or.inr ha1) (Or.inl ha2) (Or.inl (by omega))
  · rw [hfr₂ a (Or.inr (by omega))]
    exact hfr₁ a (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))

set_option maxHeartbeats 4000000 in
theorem orderIn_of_segB {w h : ℕ} {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ} {G₀ : MGraph}
    {v ℓ₀ : ℕ → ℝ} {P_fp : ℕ} {g0Ptr vCap0 eCap0 lenArr wtArr kk cnt H : ℕ}
    {mem mem₁ mem₂ mem₃ : ℕ → ℕ} {vList eList : List ℕ} (V : InitVals)
    (S : SegBIn w h Q_AN c_AN K_AN G₀ v ℓ₀ P_fp V lenArr wtArr kk mem)
    (hdg0 : DynGraphAt mem g0Ptr vCap0 eCap0 G₀) (hzb : ZeroFrom mem V.b)
    (hKw : V.K_w = kWidthOf V.m0 V.L_in) (hKK : V.K = widthK V.m0 V.L_in)
    (hm : G₀.E.card = V.m0) (hn : G₀.n = V.n0) (hn2 : 2 ≤ V.n0)
    (hH : V.H = H) (hl19 : V.thBase + 8 * V.n0 < 2 ^ w)
    (hl20 : thBound V.n0 + 2 * V.n0 + 8 < 2 ^ w)
    (h₁ : (prepStageContract w G₀).post (prepArgsV V g0Ptr vCap0 eCap0 kk) mem cnt mem₁)
    (h₂ : (widthsContract w).post [V.m0, V.L_in, V.endA + 3] mem₁ 0 mem₂)
    (hvLen : vList.length = V.n0) (hvL₂ : ListAt mem₂ V.vListPtr vList)
    (heLen : eList.length = V.m0) (heE : ∀ e, e ∈ eList ↔ e ∈ G₀.E)
    (heL : ListAt mem₂ (dgEListBase V.gPtr V.vCap V.eCap) eList)
    (h₃ : (treePhaseContract Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp vList eList).post
        (treeArgsV V lenArr wtArr) mem₂ H mem₃) :
    ∃ T_raw, IsLSST (open Classical in if G₀.E.Nonempty then weightedCopyGraph G₀ v else G₀)
        (open Classical in if G₀.E.Nonempty then weightedCopyLen G₀ ℓ₀ else fun _ => 1)
        (fun _ => 1) ((4 * max K_AN 1 + 5) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) T_raw ∧
      OrderPhaseIn w h G₀ (projectTree G₀ v T_raw) vList eList
        (OrderLayout.ofVals V (mem₃ V.outHdr)) mem₃ ∧
      ∀ f ∈ (projectTree G₀ v T_raw).E, f < fECap V.eCap V.n0 := by
  have hfrB := segB_frame h₁ h₂ hn
  obtain ⟨g0', vc', ec', k', ax', gp', po', vc0', ec0', vList', repList, heq, -, -, -,
    hdg₁, hvLen', hvNd, hvV, hvL, hvI, -, -, -, -, -, -, -, -, -, -, -, -⟩ := h₁
  simp only [prepArgsV, List.cons.injEq, and_true] at heq
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, -, -, -, -⟩ := heq
  obtain ⟨m', L', o', heq₂, -, -, -, -, hfr₂⟩ := h₂
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl⟩ := heq₂
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := V.segB_le
  have hdgs : dynGraphSize V.vCap V.eCap = 4 + 7 * V.vCap + 9 * V.eCap := rfl
  -- the vertex list of `prepStage` is `vList`
  have hvEq : vList' = vList := by
    refine listAt_unique (fun i hi => ?_) hvL₂ (by rw [hvLen', hvLen, hn])
    rw [hfr₂ _ (Or.inl (by rw [hvLen', hn] at hi; omega))]
    exact hvL i hi
  subst vList'
  -- the posts of the two parts of the tree phase
  obtain ⟨mem₁', hcp, hls⟩ := h₃
  rw [treePhaseCopyArgs_treeArgsV] at hcp
  obtain ⟨g0'', eListPtr', lenArr', wtArr', L_in', m0', K_w', qNatPtr', lsstHeap', vIdxBase',
    n0', eCap', multPtr', copyTailPtr', copyHeadPtr', copyLenPtr', copyWtPtr', copyOrigIdxPtr',
    copySubIdxPtr', usedBridgePtr', heqc, -, -, hq, -, -, -, -, -, -, -, hfrc⟩ := hcp
  simp only [treeCopyArgsV, List.cons.injEq, and_true] at heqc
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl⟩ := heqc
  rw [treePhaseLsstArgs_treeArgsV] at hls
  obtain ⟨n0'', M', ct', ch', cl', cw', L'', Ls', oo', ob', oh', lh', co', ub', ubl', ec'', to',
    tt', th', heql, hHlo, -, hzH, ⟨T_raw, hLSST, hTV, hTA, hTEb⟩, ⟨nOrig, hnOle, hnOeq, hnO⟩,
    hfrl⟩ := hls
  simp only [List.cons.injEq, and_true] at heql
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl⟩ := heql
  subst hH
  have hST : (projectTree G₀ v T_raw).IsSpanningTreeOn G₀.V ∧
      ∀ f ∈ (projectTree G₀ v T_raw).E, f ∈ G₀.E →
        (projectTree G₀ v T_raw).tail f = G₀.tail f ∧
          (projectTree G₀ v T_raw).head f = G₀.head f := by
    classical
    by_cases hEne : G₀.E.Nonempty
    · rw [if_pos hEne, if_pos hEne] at hLSST
      obtain ⟨hSp, hTG, -⟩ := projectTree_isLSST hdg0.1 (fun e he => (S.hlv e he).2.2)
        (fun e he => (S.hwv e he).2.2) hLSST
      exact ⟨hSp, hTG⟩
    · rw [if_neg hEne, if_neg hEne] at hLSST
      have hpt : projectTree G₀ v T_raw = T_raw := by
        unfold projectTree; rw [if_neg hEne]
      rw [hpt]
      exact ⟨hLSST.1, hLSST.2.1⟩
  obtain ⟨hSp, hTG⟩ := hST
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19,
    s20, s21, s22, s23, s24, s25, -⟩ := V.scratch_order
  -- the memory at the end, below `qNat` and in the `q` numbers
  have hlowc : ∀ a < V.qNat, mem₃ a = mem₂ a := fun a ha => by
    rw [hfrl a (by omega) (Or.inl (by omega)) (Or.inl (by omega)), hfrc a ha]
  have hmE : V.m0 ≤ V.eCap := by
    rw [← hm]
    have := Finset.card_le_card (show G₀.E ⊆ Finset.range V.eCap from fun e he =>
      Finset.mem_range.mpr (hdg₁.2.2.1 e he))
    simpa using this
  have hKq : V.Kq = kWidthOf V.m0 V.L_in + 6 := by unfold InitVals.Kq; rw [hKw]
  have hqv : ∀ t < V.m0, Valid mem₃ (V.qNat + t * V.Kq) h V.Kq := fun t ht =>
    numValid_congr (fun i hi => by
      have h1 : (t + 1) * V.Kq ≤ V.m0 * V.Kq := Nat.mul_le_mul_right _ ht
      rw [Nat.succ_mul] at h1
      exact (hfrl _ (by omega) (Or.inl (by omega)) (Or.inl (by omega))).symm) (hq t ht).2.1
  have hw16 : 16 ≤ 2 ^ w := by
    have : 5 ≤ w := by have := S.hhw; have := S.hh; omega
    exact le_trans (by decide : 16 ≤ 2 ^ 5) (Nat.pow_le_pow_right (by norm_num) this)
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18⟩ :=
    OrderLayout.ofVals_layout V (mem₃ V.outHdr) hHlo
  refine ⟨T_raw, hLSST, ?_, fun f hf => by
    have := hTEb f hf
    unfold fECap
    omega⟩
  exact {
    hw16 := hw16
    hh := by have := S.hh; exact this
    hhw := by have := S.hhw; show 2 * h + 2 ≤ w; omega
    hn2 := hn2
    hvlen := hvLen
    hnd := hvNd
    hV := fun u => by rw [hSp.2.1]; exact hvV u |>.symm
    hGV := fun u => (hvV u).symm
    htM := rfl
    hT := isRootedTree_of_spanningTreeOn hSp ((hvV _).mp (getD_mem_of_lt (by omega)))
    hST := fun u hu x hx => hSp.2.2 u (hSp.2.1 ▸ hu) x (hSp.2.1 ▸ hx)
    hA := by show T0IndexArrays _ vList (V.n0 - 1) _ _ _; rw [← hn]; exact hTA
    hnO := by show mem₃ V.outHdr ≤ V.n0 - 1; rw [hnOeq, ← hn]; exact hnOle
    hO := fun i hi => by rw [hnOeq]; exact hnO i (by rw [hn]; exact hi)
    hTG := hTG
    hdg := (hdg₁.of_agree fun a _ ha => hfr₂ a (Or.inl (by omega))).of_agree fun a _ ha => by
      rw [hlowc a (by omega)]
    heL := fun i hi => by
      have hi' : i < V.m0 := heLen ▸ hi
      have hlt : dgEListBase V.gPtr V.vCap V.eCap + i < V.qNat := by
        simp only [dgEListBase]; omega
      show mem₃ (dgEListBase V.gPtr V.vCap V.eCap + i) = _
      rw [hlowc _ hlt]; exact heL i hi
    heLen := heLen
    heE := fun e he => (heE e).mp he
    hvI := fun i hi => by
      have := hdg₁.2.1 _ ((hvV _).mp (List.getElem_mem hi))
      show mem₃ (V.vIdx + _) = _
      rw [hlowc _ (by omega), hfr₂ _ (Or.inl (by omega))]; exact hvI i hi
    hvLA := fun i hi => by
      show mem₃ (V.vListPtr + i) = _
      rw [hlowc _ (by omega)]; exact hvL₂ i hi
    hvCap := fun u hu => hdg₁.2.1 u ((hvV u).mp hu)
    hK := by show 1 ≤ V.K; rw [hKK]; unfold widthK; omega
    hKq := by show V.Kq ≤ V.K; rw [hKK, hKq]; unfold widthK; omega
    hme := hmE
    hq := hqv
    hqs := by
      have hs := widthK_sum_lt (h := h) (m0 := V.m0) (L_in := V.L_in) S.hh
        (f := fun t => unsignedVal mem₃ (V.qNat + t * V.Kq) h V.Kq) (fun t ht => by
          have := unsignedVal_lt (hqv t ht)
          unfold capacity base at this
          rw [← pow_mul] at this
          exact this.trans_eq (by rw [hKq]))
      show _ < capacity h V.K
      unfold capacity base
      rw [← pow_mul, hKK]
      exact hs
    hzS1 := fun i _ => hzH _ (by show V.H ≤ V.sPtr + i; omega)
    hzS2 := fun i _ => hzH _ (by show V.H ≤ V.sPtr + V.n0 + 2 * V.tM + i; omega)
    hzT := fun i hi => by
      have hi' : i < dynGraphSize V.vCap (2 * V.tM + 1) := hi
      obtain ⟨t1, t2⟩ := V.tDg_le
      show mem₃ (tDgTPtr V.tPtr + i) = 0
      rw [hlowc _ (by omega), hfrB _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]
      exact hzb _ (by omega)
    hzIdx := fun e he => by
      have he' : e < V.eCap := he
      obtain ⟨t1, t2⟩ := V.tIdx_le
      show mem₃ (tIdxOfEdgeBase V.tPtr V.vCap V.tM + e) = 0
      rw [hlowc _ (by omega), hfrB _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]
      exact hzb _ (by omega)
    hzTH := fun a ha _ => hzH a (by have ha' : V.thBase ≤ a := ha; show V.H ≤ a; omega)
    hlog := rfl
    hmin := V.minPtr_eq
    l1 := o1
    l2 := o2
    l3 := o3
    l4 := o4
    l5 := o5
    l6 := o6
    l7 := o7
    l8 := o8
    l9 := o9
    l10 := o10
    l11 := o11
    l12 := o12
    l13 := o13
    l14 := o14
    l15 := o15
    l16 := o16
    l17 := o17
    l18 := o18
    l19 := hl19
    l20 := hl20 }

end

end MinCostFlow.LSF.Program
