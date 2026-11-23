module

public import MinCostFlow.LSF.Program.InitMainBase

/-!
# The main path of the init driver

`main_wp` runs the six segments of `mainSteps` one after the other and hands every post to a
final condition. The heap `H` that the tree phase returns is not known in advance, so the places
above it are those of `V.withH H`. The word bounds on these places are asked for every `H` up to
`lsstHeap` plus the space of the `[AN19]` call (`hU`), since `useEnd` is the largest of them.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.WideWord
  InitDriver

@[expose] public section

set_option maxHeartbeats 8000000 in
/-- The main path of the driver runs, and its final memory comes from the posts of the phases.
The procedure contracts that depend on data found during the run (`htree`, `hord`) are asked
for all values of that data; the texts of those procedures do not depend on it. -/
theorem main_wp {w h C : ℕ} {p : Program} {I : InitIdx} {P : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → Prop}
    (hP : UpClosed P) {regs mem : ℕ → ℕ} {B : ℕ}
    {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ} {G₀ : MGraph} {v ℓ₀ : ℕ → ℝ} {P_fp : ℕ}
    {g0Ptr vCap0 eCap0 lenArr wtArr kk Bt : ℕ}
    {bRoot bStore bOrder bT bTH bWT bLB bW bCopy bFlag bRoots bG bA bWF : ℕ} (V : InitVals)
    -- the procedures
    (hlog : MeetsContract w p I.log2 log2Contract)
    (hprep : MeetsContract w p I.prep (prepStageContract w G₀))
    (hwid : MeetsContract w p I.widths (widthsContract w))
    (htree : ∀ vList eList, MeetsContract w p I.tree
      (treePhaseContract Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp vList eList))
    (hord : ∀ T₀ vList eList, MeetsContract w p I.order
      (orderPhaseContract w h G₀ T₀ vList eList bRoot bStore bOrder bT bTH))
    (hlb : MeetsContract w p I.lb (wstrLBContract w))
    (hdec : MeetsContract w p I.decomp
      (decompPhaseContract w h C bWT bLB bW bCopy bFlag bRoots decompPhaseCost))
    (hf : MeetsContract w p I.forest (fPhaseContract w h bG bA bWF))
    (hs20 : MeetsContract w p I.store20 (storeArgsContract w 20))
    (hs24 : MeetsContract w p I.store24 (storeArgsContract w 24))
    -- the arguments
    (r0 : regs rG0 = g0Ptr) (r1 : regs rLen = lenArr) (r2 : regs rWt = wtArr)
    (r3 : regs rLin = V.L_in) (r4 : regs rPfp = P_fp) (r5 : regs rKn = kk)
    (r6 : regs rLw = V.L_w) (r7 : regs rVc = V.vCap) (r8 : regs rEc = V.eCap)
    (r9 : regs rB = V.b)
    -- the input
    (S : SegBIn w h Q_AN c_AN K_AN G₀ v ℓ₀ P_fp V lenArr wtArr kk mem)
    (hdg0 : DynGraphAt mem g0Ptr vCap0 eCap0 G₀) (hg0 : g0Ptr + dynGraphSize vCap0 eCap0 ≤ V.b)
    (hvc : vCap0 ≤ V.vCap) (hec0 : eCap0 ≤ V.eCap) (hzb : ZeroFrom mem V.b)
    (hKw : V.K_w = kWidthOf V.m0 V.L_in) (hKK : V.K = widthK V.m0 V.L_in)
    (hLBV : V.LB = wstrLB V.n0 (hldDepthBound V.n0) V.L_w)
    (hm : G₀.E.card = V.m0) (hn : G₀.n = V.n0) (hn2 : 2 ≤ V.n0)
    (hn0 : V.n0 ≤ V.vCap) (hm0 : V.m0 ≤ V.eCap) (he : 1 ≤ V.eCap) (hlb0 : lenArr ≤ V.b) (hLinw : V.L_in ≤ V.L_w)
    (hC : C < 2 ^ (h * V.L_w))
    -- word bounds
    (hw : V.endA + 6 < 2 ^ w)
    (hU : ∀ H, H ≤ V.lsstHeap + lsstSpace Q_AN K_AN V.n0 (2 * V.m0)
      (lsstLSimMin c_AN 0 (2 * V.m0) V.L_in h) h → (V.withH H).useEnd < 2 ^ w)
    (hl20 : thBound V.n0 + 2 * V.n0 + 8 < 2 ^ w)
    (hDw : 2 * (hldDepthBound V.n0 + 1) < 2 ^ w) (hm0w : 2 * V.m0 < 2 ^ w)
    (hLBw : wstrLB V.n0 (hldDepthBound V.n0) V.L_w < 2 ^ w) (hkw : kk < 2 ^ w)
    (hLw : V.L_w < 2 ^ w) (hPw : P_fp < 2 ^ w)
    -- the cost
    (hBt : ∀ vList eList, eList.length = V.m0 → eList.Nodup → (∀ e, e ∈ eList ↔ e ∈ G₀.E) →
      treeCostOf Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp V lenArr wtArr vList eList ≤ Bt)
    (hB : segACost V.n0 + segBCost V.n0 V.m0 Bt + segCCost V + segDCost V V.n0 + segECost V +
      segFCost ≤ B)
    -- the final condition, from the posts of all phases
    (hfin : ∀ regs' cnt mem₁ mem₂ vList eList H mem₃ T_raw v₄ mem₄ v₅ mem₅ v₆ mem₆ v₇ mem₇ v₈
        mem₈,
      (prepStageContract w G₀).post (prepArgsV V g0Ptr vCap0 eCap0 kk) mem cnt mem₁ →
      (widthsContract w).post [V.m0, V.L_in, V.endA + 3] mem₁ 0 mem₂ →
      vList.length = V.n0 → ListAt mem₂ V.vListPtr vList →
      eList.length = V.m0 → eList.Nodup → (∀ e, e ∈ eList ↔ e ∈ G₀.E) →
      ListAt mem₂ (dgEListBase V.gPtr V.vCap V.eCap) eList →
      (treePhaseContract Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp vList eList).post
        (treeArgsV V lenArr wtArr) mem₂ H mem₃ →
      IsLSST (open Classical in if G₀.E.Nonempty then weightedCopyGraph G₀ v else G₀)
        (open Classical in if G₀.E.Nonempty then weightedCopyLen G₀ ℓ₀ else fun _ => 1)
        (fun _ => 1) ((4 * max K_AN 1 + 5) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) T_raw →
      OrderPhaseIn w h G₀ (projectTree G₀ v T_raw) vList eList
        (OrderLayout.ofVals (V.withH H) (mem₃ V.outHdr)) mem₃ →
      (orderPhaseContract w h G₀ (projectTree G₀ v T_raw) vList eList bRoot bStore bOrder bT
        bTH).post (OrderLayout.ofVals (V.withH H) (mem₃ V.outHdr)).args mem₃ v₄ mem₄ →
      DecompPhaseIn w h C (projectTree G₀ v T_raw) vList
        (DecompLayout.ofVals (V.withH H) (mem₃ V.outHdr) (4 * kk * (hldDepthBound V.n0 + 1))
          (hldDepthBound V.n0) kk lenArr cnt) mem₄ →
      (decompPhaseContract w h C bWT bLB bW bCopy bFlag bRoots decompPhaseCost).post
        (DecompLayout.ofVals (V.withH H) (mem₃ V.outHdr) (4 * kk * (hldDepthBound V.n0 + 1))
          (hldDepthBound V.n0) kk lenArr cnt).args mem₄ v₅ mem₅ →
      FPhaseIn w h (FLayout.ofVals (V.withH H) (mem₃ V.outHdr)
          (4 * kk * (hldDepthBound V.n0 + 1)) (hldDepthBound V.n0) kk lenArr cnt) mem₅ →
      (fPhaseContract w h bG bA bWF).post
        (FLayout.ofVals (V.withH H) (mem₃ V.outHdr) (4 * kk * (hldDepthBound V.n0 + 1))
          (hldDepthBound V.n0) kk lenArr cnt).args mem₅ v₆ mem₆ →
      (storeArgsContract w 20).post (V.auxPtr :: auxHdrVals V) mem₆ v₇ mem₇ →
      (storeArgsContract w 24).post
        (V.b :: lsfHdrVals V h P_fp kk (mem₆ V.fAncPtr) (mem₆ V.vListPtr)) mem₇ v₈ mem₈ →
      regs' rRet = (V.withH H).useEnd →
      P regs' mem₈ (B - (segACost V.n0 + segBCost V.n0 V.m0 Bt + segCCost V + segDCost V V.n0 +
        segECost V + segFCost))) :
    SeqWPR w p 10 P 0 (mainSteps I h) regs mem B := by
  have hn1 : 1 ≤ V.n0 := by omega
  have hw16 : 16 ≤ 2 ^ w := by
    have : 5 ≤ w := by have := S.hhw; have := S.hh; omega
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold mainSteps
  refine segA_wp hP V hlog r0 r6 r7 r8 r9 hdg0 hn hm hg0 hm0 hn0 hn1 hw (by omega) ?_
  intro regs₁ e1 a1
  refine segB_wp hP V hprep hwid htree ((e1 0 (by omega)).trans r0) ((e1 1 (by omega)).trans r1)
    ((e1 2 (by omega)).trans r2) ((e1 3 (by omega)).trans r3) ((e1 5 (by omega)).trans r5)
    ((e1 7 (by omega)).trans r7) ((e1 8 (by omega)).trans r8) a1 S hdg0 hg0 hvc hec0 hzb hKw
    hKK hm hn hn1 hBt (by omega) ?_
  intro regs₂ cnt mem₁ mem₂ vList eList H mem₃ h₁ h₂ hvLen hvL heLen heNd heE heL h₃ e2 a2 b2
    h49
  obtain ⟨hH1, hH2, hz3⟩ := tree_ret V S.hh S.hLin h₃
  have hU' := hU H hH2
  have hcn : cnt ≤ V.n0 := hn ▸ prep_cnt_le h₁
  obtain ⟨u1, u2, u3, u4⟩ := (V.withH H).useEnd_ge
  have hl19 : (V.withH H).thBase + 8 * (V.withH H).n0 < 2 ^ w := by omega
  obtain ⟨T_raw, hLSST, IO, hTE⟩ := orderIn_of_segB (V.withH H) (S.withH H) hdg0 hzb hKw hKK hm hn hn2 rfl
    hl19 hl20 h₁ h₂ hvLen hvL heLen heE heL h₃
  have q : ∀ j < 10, regs₂ j = regs j := fun j hj => (e2 j hj).trans (e1 j hj)
  refine segC_wp hP (V.withH H) (hord _ _ _) IO ((q 7 (by omega)).trans r7)
    ((q 8 (by omega)).trans r8) a2 b2 h49 rfl hH1
    (budget_segC V hB) ?_
  intro regs₃ v₄ mem₄ h₄ e3 c3 r64
  obtain ⟨_, _, _, _, _, _, _, o₁, o₃, o₄, o₅⟩ := orderPhase_post h₄
  have hL19 : wsPt (V.withH H).idPtr V.n0 V.tM V.m0 (wstrLB V.n0 (hldDepthBound V.n0) V.L_w) 18
      + V.m0 < 2 ^ w := by
    have u2' : wsPt (V.withH H).idPtr V.n0 V.tM V.m0 V.LB 18 + V.m0 = (V.withH H).wBase := u2
    rw [hLBV] at u2'
    omega
  obtain ⟨repList, E⟩ := decompExtra_of_segB (V.withH H) (S.withH H) hn hn1 hn0 he hH1 hlb0 hLinw hC hDw
    hm0w hLBw hkw hL19 h₁ h₂ hvL hvLen heNd h₃ hz3
  have ID := decompIn_of_order IO E o₁ o₃ o₄ o₅
  have hθ := theta_kept (V.withH H) hH1 h₁ h₂ h₃ IO h₄
  rw [hn] at hθ
  have q3 : ∀ j < 10, regs₃ j = regs j := fun j hj => (e3 j (by omega)).trans (q j hj)
  have a3 : ∀ j < 19, regs₃ (10 + j) = (segAVals (V.withH H)).getD j 0 :=
    fun j hj => (e3 _ (by omega)).trans (a2 j hj)
  have b3 : ∀ j < 20, regs₃ (29 + j) = (segBVals (V.withH H) cnt).getD j 0 :=
    fun j hj => (e3 _ (by omega)).trans (b2 j hj)
  refine segD_wp hP (V.withH H) hlb hdec ID hLBV ((q3 1 (by omega)).trans r1)
    ((q3 3 (by omega)).trans r3) ((q3 5 (by omega)).trans r5) ((q3 6 (by omega)).trans r6)
    ((q3 7 (by omega)).trans r7) ((q3 8 (by omega)).trans r8) a3 b3 c3 hθ hH1
    (budget_segD V hcn hB) ?_
  intro regs₄ v₅ mem₅ h₅ e4 d4 r72
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, p₁, p₃, p₄, p₅, p₆, p₇, p₈⟩ := decompPhase_post h₅
  have hzF : ∀ a, (V.withH H).fPtr ≤ a → a < (V.withH H).wPtr → mem₃ a = 0 := by
    intro a ha1 ha2
    have ha1' : V.fPtr ≤ a := ha1
    have ha2' : a < V.wPtr := ha2
    obtain ⟨e1', e2', e3', e4', e5', e6', e7', e8', e9', e10', e11', e12', e13', e14', e15'⟩ :=
      V.aux_order
    have hq : (V.withH H).qNat = V.endA + 6 := V.scratch_order.1.symm
    rw [tree_frame_low (V.withH H) h₃ a (by omega),
      segB_frame h₁ h₂ hn a (Or.inr (Or.inl ⟨by omega, by omega⟩))]
    exact hzb a (by omega)
  have FE := fExtra_of_order (θ := 4 * kk * (hldDepthBound V.n0 + 1)) (D := hldDepthBound V.n0)
    (kk := kk) (lenArr := lenArr) (cnt := cnt) (V.withH H) IO h₄ hH1 hzF hz3 hn0
    hTE hLBV hU'
  have FI := fIn_of_decomp ID FE p₁ p₃ p₄ p₅ p₆ p₇ p₈
  have q4 : ∀ j < 65, regs₄ j = regs₃ j := e4
  refine segE_wp hP (V.withH H) hf FI ((q4 7 (by omega)).trans ((q3 7 (by omega)).trans r7))
    ((q4 8 (by omega)).trans ((q3 8 (by omega)).trans r8))
    (fun j hj => (q4 _ (by omega)).trans (a3 j hj))
    (fun j hj => (q4 _ (by omega)).trans (b3 j hj))
    (fun j hj => (q4 _ (by omega)).trans (c3 j hj)) d4
    (budget_segE V hcn hB) ?_
  intro regs₅ v₆ mem₆ h₆ e5 w73 r74
  have q5 : ∀ j < 10, regs₅ j = regs j :=
    fun j hj => (e5 j (by omega)).trans ((q4 j (by omega)).trans (q3 j hj))
  have hfv := fPhase_words FI h₆
  refine segF_wp hP (V.withH H) hs20 hs24 ((q5 4 (by omega)).trans r4)
    ((q5 5 (by omega)).trans r5) ((q5 6 (by omega)).trans r6) ((q5 3 (by omega)).trans r3)
    ((q5 7 (by omega)).trans r7) ((q5 8 (by omega)).trans r8) ((q5 9 (by omega)).trans r9)
    (fun j hj => (e5 _ (by omega)).trans ((q4 _ (by omega)).trans (a3 j hj)))
    (fun j hj => (e5 _ (by omega)).trans ((q4 _ (by omega)).trans (c3 j hj))) w73 hw16 hn1
    (show V.endA < 2 ^ w by omega) hU' hLw
    (show V.L_in < 2 ^ w by omega)
    (show V.m0 < 2 ^ w by omega) S.hl4 hPw hkw hfv.1 hfv.2
    (budget_segF V hcn hB) ?_
  intro v₇ mem₇ v₈ mem₈ regs₆ q₇ q₈ e6 r77
  refine hP _ _ _ _ ?_ (hfin regs₆ cnt mem₁ mem₂ vList eList H mem₃ T_raw v₄ mem₄ v₅ mem₅ v₆ mem₆
    v₇ mem₇ v₈ mem₈ h₁ h₂ hvLen hvL heLen heNd heE heL h₃ hLSST IO h₄ ID h₅ FI h₆ q₇ q₈ r77)
  exact budget_fin V hcn

end

end MinCostFlow.LSF.Program
