module

public import MinCostFlow.LSF.Program.InitGBlock
public import MinCostFlow.LSF.Program.InitAuxAt
public import MinCostFlow.LSF.Program.InitHeader
public import MinCostFlow.LSF.Program.InitWstrMain
public import MinCostFlow.LSF.Program.InitValid
public import MinCostFlow.LSF.Program.InitWstr
public import MinCostFlow.LSF.Lemma54With

/-!
# The representation of the initial state

`init_lsfRep` puts the blocks of the state together. It takes the posts that `main_wp` hands
to its final condition and gives the parameters of `initLSFWith` (the representatives and the
decomposition that the program found, the root and the order it wrote), the fact that they
satisfy `ValidLSFParams`, and a concrete state `x` with `LSFRep` of `initLSFWith` at the end
of the driver. Each block comes from one earlier lemma: `init_gBlockAt` (the copy of `G₀`),
`init_tBlockAt` (the tree), `init_forestBlocks` (the forest, its roots and components, and the
refined decomposition), `init_wstrAt` with `init_wstrAt_final` (the stretches), `init_auxAt`
(the aux block) and `init_lsfHeader` (the header). The model's invariant comes from
`initLSFWith_inv`.

The program computes the threshold as `threshProd C n₀ kk`, and the model uses
`defaultThreshNat K_AN n₀ kk`. The hypothesis `hCθ` says that the two agree (`threshProd_eq`
gives it for `C = defaultC_ceil K_AN`).
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.Num
  InitDriver

@[expose] public section

open Classical in
set_option maxHeartbeats 1600000 in
/-- At the end of the driver, the memory represents `initLSFWith` for parameters that satisfy
`ValidLSFParams`. -/
theorem init_lsfRep {w h C : ℕ} {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ} {G₀ : MGraph}
    {v ℓ₀ : ℕ → ℝ} {P_fp : ℕ} {g0Ptr vCap0 eCap0 lenArr wtArr kk cnt H : ℕ}
    {bRoot bStore bOrder bT bTH bWT bLB bW bCopy bFlag bRoots bG bA bWF : ℕ}
    {mem mem₁ mem₂ mem₃ mem₄ mem₅ mem₆ mem₇ mem₈ : ℕ → ℕ} {v₄ v₅ v₆ v₇ v₈ : ℕ}
    {vList eList : List ℕ} {T_raw : MGraph}
    (V : InitVals)
    (S : SegBIn w h Q_AN c_AN K_AN G₀ v ℓ₀ P_fp V lenArr wtArr kk mem)
    (hn : G₀.n = V.n0) (hm : G₀.E.card = V.m0) (hn0 : V.n0 ≤ V.vCap)
    (hm0 : V.m0 ≤ V.eCap) (hG₀ : G₀.IsValid)
    (hVlt : ∀ u ∈ G₀.V, u < V.vCap) (hElt : ∀ e ∈ G₀.E, e < V.eCap)
    (hLinw : V.L_in ≤ V.L_w)
    (hCθ : threshProd C V.n0 kk = defaultThreshNat K_AN G₀.n kk)
    (hθ : threshProd C V.n0 kk < 2 ^ (h * (V.L_w - V.L_in)))
    (h₁ : (prepStageContract w G₀).post (prepArgsV V g0Ptr vCap0 eCap0 kk) mem cnt mem₁)
    (h₂ : (widthsContract w).post [V.m0, V.L_in, V.endA + 3] mem₁ 0 mem₂)
    (hvLen : vList.length = V.n0) (hvL : ListAt mem₂ V.vListPtr vList)
    (heLen : eList.length = V.m0) (heNd : eList.Nodup) (heE : ∀ e, e ∈ eList ↔ e ∈ G₀.E)
    (h₃ : (treePhaseContract Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp vList eList).post
        (treeArgsV V lenArr wtArr) mem₂ H mem₃)
    (hT : IsLSST (open Classical in if G₀.E.Nonempty then weightedCopyGraph G₀ v else G₀)
        (open Classical in if G₀.E.Nonempty then weightedCopyLen G₀ ℓ₀ else fun _ => 1)
        (fun _ => 1) ((4 * max K_AN 1 + 5) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) T_raw)
    (IO : OrderPhaseIn w h G₀ (projectTree G₀ v T_raw) vList eList
      (OrderLayout.ofVals (V.withH H) (mem₃ V.outHdr)) mem₃)
    (h₄ : (orderPhaseContract w h G₀ (projectTree G₀ v T_raw) vList eList bRoot bStore bOrder bT
      bTH).post (OrderLayout.ofVals (V.withH H) (mem₃ V.outHdr)).args mem₃ v₄ mem₄)
    (ID : DecompPhaseIn w h C (projectTree G₀ v T_raw) vList
        (DecompLayout.ofVals (V.withH H) (mem₃ V.outHdr) (4 * kk * (hldDepthBound V.n0 + 1))
          (hldDepthBound V.n0) kk lenArr cnt) mem₄)
    (h₅ : (decompPhaseContract w h C bWT bLB bW bCopy bFlag bRoots decompPhaseCost).post
        (DecompLayout.ofVals (V.withH H) (mem₃ V.outHdr) (4 * kk * (hldDepthBound V.n0 + 1))
          (hldDepthBound V.n0) kk lenArr cnt).args mem₄ v₅ mem₅)
    (IF : FPhaseIn w h (FLayout.ofVals (V.withH H) (mem₃ V.outHdr)
          (4 * kk * (hldDepthBound V.n0 + 1)) (hldDepthBound V.n0) kk lenArr cnt) mem₅)
    (h₆ : (fPhaseContract w h bG bA bWF).post
        (FLayout.ofVals (V.withH H) (mem₃ V.outHdr) (4 * kk * (hldDepthBound V.n0 + 1))
          (hldDepthBound V.n0) kk lenArr cnt).args mem₅ v₆ mem₆)
    (h₇ : (storeArgsContract w 20).post (V.auxPtr :: auxHdrVals V) mem₆ v₇ mem₇)
    (h₈ : (storeArgsContract w 24).post
        (V.b :: lsfHdrVals V h P_fp kk (mem₆ V.fAncPtr) (mem₆ V.vListPtr)) mem₇ v₈ mem₈) :
    ∃ (C_reps : Finset ℕ) (W_T : Finset (Finset ℕ)),
      ValidLSFParams (4 * max K_AN 1 + 5) (5 / 4) (defaultThreshNat K_AN G₀.n kk : ℝ)
        (defaultK_sigma K_AN : ℝ) G₀ ℓ₀ v (kk : ℝ) T_raw (vList.getD 0 0) C_reps
        (orderPi (OrderLayout.ofVals (V.withH H) (mem₃ V.outHdr)) mem₃ mem₄) W_T ∧
      ∃ x : LSFConcrete, x.vCap = V.vCap ∧ x.eCap = V.eCap ∧ x.n0 = V.n0 ∧ x.tM = V.tM ∧
        x.L_w = V.L_w ∧
        (LSFRep h).rep V.b (initLSFWith G₀ ℓ₀ v (kk : ℝ) T_raw (vList.getD 0 0) C_reps
          (orderPi (OrderLayout.ofVals (V.withH H) (mem₃ V.outHdr)) mem₃ mem₄) W_T
          (defaultThreshNat K_AN G₀.n kk : ℝ)) x mem₈ := by
  have hH : V.lsstHeap ≤ H := (tree_ret V S.hh S.hLin h₃).1
  have hk1 : (1 : ℝ) ≤ (kk : ℝ) := by exact_mod_cast S.hk
  -- the blocks
  have hG := init_gBlockAt IO h₄ ID h₅ h₆ h₇ h₈ hH
  have hTB := init_tBlockAt IO h₄ ID h₅ h₆ h₇ h₈ hH
  have hTc := init_tCard IO
  have hWs := init_wstrAt_final (V := V.withH H)
    (init_wstrAt V S hn hm hLinw hθ h₁ h₂ heLen heNd heE h₃ IO h₄ ID h₅) h₆ h₇ h₈ hH
  have hπ := order_pi_of_posts V S hn hm h₁ h₂ heLen heNd heE h₃ IO h₄
  obtain ⟨repList, hC, W, hW, hF, hFA, hWB⟩ := init_forestBlocks V S hn hm hn0 hG₀ hLinw hθ
    h₁ h₂ hvLen hvL heLen heNd heE h₃ IO h₄ ID h₅ IF h₆ h₇ h₈
  rw [hCθ] at hF hFA hWB hWs
  have hp := validParams_of_parts (K_AN := K_AN) hT hC hπ hW S.hk
  refine ⟨repList.toFinset, W, hp, ?_⟩
  -- the model state and its invariant
  have hn2 : 2 ≤ V.n0 := IO.hn2
  have htM : V.tM = V.n0 - 1 := rfl
  have hV₀ : G₀.V.Nonempty := by
    have : 0 < vList.length := by omega
    obtain ⟨u, hu⟩ := List.exists_mem_of_length_pos this
    exact ⟨u, (IO.hGV u).mpr hu⟩
  have hInv := LSFInvWith.toStructInv (initLSFWith_inv hG₀ hV₀ (fun e he => (S.hlv e he).2.2)
    (fun e he => (S.hwv e he).2.2) hk1 hp)
  have hAux := init_auxAt (S := initLSFWith G₀ ℓ₀ v (kk : ℝ) T_raw (vList.getD 0 0)
      repList.toFinset (orderPi (OrderLayout.ofVals (V.withH H) (mem₃ V.outHdr)) mem₃ mem₄) W
      (defaultThreshNat K_AN G₀.n kk : ℝ)) V hn hH h₁ h₂ hvLen hvL h₃ IO h₄ ID h₅ h₆ h₇ h₈
    rfl rfl rfl (fun u hu => ⟨hu, rfl⟩)
  have hFA' := hFA (initLSFWith G₀ ℓ₀ v (kk : ℝ) T_raw (vList.getD 0 0)
      repList.toFinset (orderPi (OrderLayout.ofVals (V.withH H) (mem₃ V.outHdr)) mem₃ mem₄) W
      (defaultThreshNat K_AN G₀.n kk : ℝ)).RF rfl (Finset.union_empty _)
  -- the two numbers of the header
  have hkeep := init_store_keep h₇ h₈
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ := V.aux_order
  have hfs : 1 ≤ fAncSize V.vCap := by simp only [fAncSize, fAncHdrSize]; omega
  have hR := hFA'.1
  rw [show V.fAncPtr + fOffRCount = V.fAncPtr from rfl,
    hkeep _ (Or.inl ⟨by omega, by omega⟩)] at hR
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hLA, -⟩ := hAux
  have hr : mem₈ V.vListPtr = vList.getD 0 0 := by
    have := hLA 0 (by omega)
    rw [List.getD_eq_getElem _ _ (by omega)]
    simpa [InitVals.vListPtr] using this
  have h20 : V.auxPtr + 20 ≤ V.vListPtr := by
    show V.auxPtr + 20 ≤ V.auxPtr + auxHdrSize + V.vCap
    have : auxHdrSize = 20 := rfl
    omega
  rw [hkeep _ (Or.inr h20)] at hr
  refine ⟨⟨V.vCap, V.eCap, V.n0, V.m0, V.tM, h, P_fp, V.L_in, V.L_w, kk,
    tStageList mem₃ V.tOrig V.tM, vList,
    fun x => mem₈ (auxT0ParentBase V.auxPtr V.vCap V.n0 + x),
    fun x => mem₈ (auxT0ParentTreeIdxBase V.auxPtr V.vCap V.n0 + x),
    fun x => mem₈ (auxT0DepthBase V.auxPtr V.vCap V.n0 + x),
    fun x => mem₈ (auxThParentBase V.auxPtr V.vCap V.n0 + x),
    fun i j => mem₈ (auxUpVBase V.auxPtr V.vCap V.n0 + (i * auxLogCap V.n0 + j)),
    fun i j => mem₈ (auxUpMinIdxBase V.auxPtr V.vCap V.n0 + (i * auxLogCap V.n0 + j)),
    rootList (fun x => vList.getD x 0) (fun y => mem₅ ((V.withH H).inR + y)) vList.length,
    fun u => vList.getD (mem₅ ((V.withH H).inR + V.n0 + V.n0 + V.tM + vList.idxOf u)) 0,
    fun c => c,
    sizeVal (fun x => vList.getD x 0)
      (fun y => mem₅ ((V.withH H).inR + V.n0 + V.n0 + V.tM + y)) vList.length,
    (initLSFWith G₀ ℓ₀ v (kk : ℝ) T_raw (vList.getD 0 0)
      repList.toFinset (orderPi (OrderLayout.ofVals (V.withH H) (mem₃ V.outHdr)) mem₃ mem₄) W
      (defaultThreshNat K_AN G₀.n kk : ℝ)).RF.R⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, S.hh, S.hLin, le_trans S.hLin hLinw, S.hk, rfl, hInv, hn, hm,
    hTc, hn0, hm0, (Nat.sub_le _ _ : V.n0 - 1 ≤ V.n0), (by omega : 1 ≤ V.n0), fun u hu => hVlt u ((IO.hGV u).mpr ((IO.hV u).mp hu)),
    hElt, ?_, hG, hTB, hF, hFA', hWB, ?_, ?_⟩
  · exact init_lsfHeader h₈ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hR.symm rfl hr.symm
  · rw [initLSFWith_wstr]
    exact hWs
  · exact init_auxAt V hn hH h₁ h₂ hvLen hvL h₃ IO h₄ ID h₅ h₆ h₇ h₈ rfl rfl rfl
      (fun u hu => ⟨hu, rfl⟩)


/-- `LSFRep` of `initLSFWith`, with the lengths and weights read from the input arrays, gives
`lsfInitPost`: the header holds the numbers and the places of the two stretch arrays, and the
stretch block is `WstrAt`. -/
theorem lsfInitPost_of_rep {K_AN : ℝ} {h : ℕ} {args : List ℕ} {mem mem' : ℕ → ℕ} {G₀ : MGraph}
    {g0Ptr vCap0 eCap0 lenArr wtArr L_in P_fp k_nat L_w vCap eCap b : ℕ} {T_raw : MGraph}
    {r₀ : ℕ} {C_reps : Finset ℕ} {π : ℕ → ℕ} {W_T : Finset (Finset ℕ)} {x : LSFConcrete}
    (hargs : args = [g0Ptr, lenArr, wtArr, L_in, P_fp, k_nat, L_w, vCap, eCap, b])
    (hdg : DynGraphAt mem g0Ptr vCap0 eCap0 G₀)
    (hp : ValidLSFParams (4 * max K_AN 1 + 5) (5 / 4)
      (defaultThreshNat K_AN G₀.n k_nat : ℝ) (defaultK_sigma K_AN : ℝ)
      G₀ (memArrayReal mem lenArr G₀ h L_in P_fp) (memArrayReal mem wtArr G₀ h L_in P_fp)
      (k_nat : ℝ) T_raw r₀ C_reps π W_T)
    (hrep : (LSFRep h).rep b (initLSFWith G₀ (memArrayReal mem lenArr G₀ h L_in P_fp)
      (memArrayReal mem wtArr G₀ h L_in P_fp) (k_nat : ℝ) T_raw r₀ C_reps π W_T
      (defaultThreshNat K_AN G₀.n k_nat : ℝ)) x mem')
    (hvc : x.vCap = vCap) (hec : x.eCap = eCap) (hLw : x.L_w = L_w) :
    lsfInitPost K_AN h args mem (initLSFWith G₀ (memArrayReal mem lenArr G₀ h L_in P_fp)
      (memArrayReal mem wtArr G₀ h L_in P_fp) (k_nat : ℝ) T_raw r₀ C_reps π W_T
      (defaultThreshNat K_AN G₀.n k_nat : ℝ)) mem' := by
  obtain ⟨hxH, -, -, -, -, -, -, hn0, hm0, htM, -, -, -, -, -, -, hhdr, -, -, -, -, -, hW, -⟩ :=
    hrep
  obtain ⟨d1, d2, d3, d4, -, -, -, -, -, d10, d11, d12, -⟩ := hhdr
  subst hvc hec hLw hxH
  have hn : G₀.n = x.n0 := hn0
  have hm : G₀.E.card = x.m0 := hm0
  have ht : (projectTree G₀ (memArrayReal mem wtArr G₀ x.h L_in P_fp) T_raw).E.card = x.tM := htM
  refine ⟨G₀, g0Ptr, vCap0, eCap0, lenArr, wtArr, L_in, P_fp, k_nat, x.L_w, x.vCap, x.eCap, b,
    T_raw, C_reps, W_T, hargs, hdg, hp, rfl, d1, d2, by rw [d3, hn], by rw [d4, hm], d12, ?_, ?_,
    ?_⟩
  · show _ = lsfWstrNumPtr b x.vCap x.eCap G₀.n
      (projectTree G₀ (memArrayReal mem wtArr G₀ x.h L_in P_fp) T_raw).E.card
    rw [d10, hn, ht]
  · show _ = lsfWstrDenPtr b x.vCap x.eCap G₀.n
      (projectTree G₀ (memArrayReal mem wtArr G₀ x.h L_in P_fp) T_raw).E.card x.L_w
    rw [d11, hn, ht]
  · rw [d10, d11]
    exact hW

end

end MinCostFlow.LSF.Program
