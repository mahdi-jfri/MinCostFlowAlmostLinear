module

public import MinCostFlow.LSF.Program.InitForestIn
public import MinCostFlow.LSF.Program.FPhaseBlocks
public import MinCostFlow.LSF.Program.InitKeep

/-!
# The forest blocks of the initial state, in the terms of the driver

`init_forestBlocks` takes the posts that `main_wp` hands to its final condition and gives the
three forest blocks of the state at the end of the driver: `DynGraphAt` of `F_T(R, π)` at
`fPtr`, `FAncAt` at `fAncPtr` and `WBlockAt` at `wPtr`, for the root set `R` of `initLSFWith`.
`init_forestIn` gives the decomposition, the representatives and the roots pass, and
`fPhase_blocks` the blocks after the forest phase. The tree arrays that the forest phase reads
are those of the start of the decomposition phase, which the decomposition phase keeps. The ends
`tTail`, `tHead` name the same vertices as the ends `tl`, `hd` of `DecompPhaseIn.htree`: both
give the ends of the tree edge `fid i`. The two header stores write
below `gPtr` and at the aux header, so they keep the blocks.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.Num
  InitDriver

@[expose] public section

open Classical in
set_option maxHeartbeats 1600000 in
/-- At the end of the driver, the forest blocks of the state represent the forest of the first
root set of `initLSFWith` (threshold `threshProd C n₀ kk`), its root and component block, and
the refined decomposition, for a decomposition `W` with the properties of Lemma B.7. -/
theorem init_forestBlocks {w h C : ℕ} {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ} {G₀ : MGraph}
    {v ℓ₀ : ℕ → ℝ} {P_fp : ℕ} {g0Ptr vCap0 eCap0 lenArr wtArr kk cnt H : ℕ}
    {bRoot bStore bOrder bT bTH bWT bLB bW bCopy bFlag bRoots bG bA bWF : ℕ}
    {mem mem₁ mem₂ mem₃ mem₄ mem₅ mem₆ mem₇ mem₈ : ℕ → ℕ} {v₄ v₅ v₆ v₇ v₈ : ℕ}
    {vList eList vs₇ vs₈ : List ℕ} {T_raw : MGraph}
    (V : InitVals)
    (S : SegBIn w h Q_AN c_AN K_AN G₀ v ℓ₀ P_fp V lenArr wtArr kk mem)
    (hn : G₀.n = V.n0) (hm : G₀.E.card = V.m0) (hn0 : V.n0 ≤ V.vCap)
    (hG₀ : G₀.IsValid)
    (hLinw : V.L_in ≤ V.L_w)
    (hθ : threshProd C V.n0 kk < 2 ^ (h * (V.L_w - V.L_in)))
    (h₁ : (prepStageContract w G₀).post (prepArgsV V g0Ptr vCap0 eCap0 kk) mem cnt mem₁)
    (h₂ : (widthsContract w).post [V.m0, V.L_in, V.endA + 3] mem₁ 0 mem₂)
    (hvLen : vList.length = V.n0) (hvL : ListAt mem₂ V.vListPtr vList)
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
          (hldDepthBound V.n0) kk lenArr cnt).args mem₄ v₅ mem₅)
    (IF : FPhaseIn w h (FLayout.ofVals (V.withH H) (mem₃ V.outHdr)
          (4 * kk * (hldDepthBound V.n0 + 1)) (hldDepthBound V.n0) kk lenArr cnt) mem₅)
    (h₆ : (fPhaseContract w h bG bA bWF).post
        (FLayout.ofVals (V.withH H) (mem₃ V.outHdr) (4 * kk * (hldDepthBound V.n0 + 1))
          (hldDepthBound V.n0) kk lenArr cnt).args mem₅ v₆ mem₆)
    (h₇ : (storeArgsContract w 20).post (V.auxPtr :: vs₇) mem₆ v₇ mem₇)
    (h₈ : (storeArgsContract w 24).post (V.b :: vs₈) mem₇ v₈ mem₈) :
    ∃ repList : List ℕ, IsCompReps G₀ (vList.getD 0 0) repList.toFinset ∧
    ∃ W : Finset (Finset ℕ), IsTreeDecompSpec G₀ (projectTree G₀ v T_raw) kk W ∧
      let π := orderPi (OrderLayout.ofVals (V.withH H) (mem₃ V.outHdr)) mem₃ mem₄
      let T₀ := projectTree G₀ v T_raw
      let R := upClosure (hldAuxTree T₀ (vList.getD 0 0)) (vList.getD 0 0)
        (repList.toFinset ∪ boundary W ∪
          (G₀.E.filter fun e => (threshProd C V.n0 kk : ℝ) ≤
            levelStretchBound T₀ (vList.getD 0 0) π G₀ (safeLen G₀ ℓ₀) e).biUnion
              fun e => {G₀.tail e, G₀.head e})
      DynGraphAt mem₈ V.fPtr V.vCap (fECap V.eCap V.n0)
        (forestGivenRoots T₀ (vList.getD 0 0) R π) ∧
      (∀ RF : RootedForest, RF.F = forestGivenRoots T₀ (vList.getD 0 0) R π → RF.R = R →
        FAncAt mem₈ V.fAncPtr V.vCap RF
          (rootList (fun x => vList.getD x 0) (fun y => mem₅ ((V.withH H).inR + y))
            vList.length)
          (fun u => vList.getD
            (mem₅ ((V.withH H).inR + V.n0 + V.n0 + V.tM + vList.idxOf u)) 0) (fun c => c)
          (sizeVal (fun x => vList.getD x 0)
            (fun y => mem₅ ((V.withH H).inR + V.n0 + V.n0 + V.tM + y)) vList.length) RF.R) ∧
      WBlockAt mem₈ V.wPtr V.n0 (refineDecomp W (forestGivenRoots T₀ (vList.getD 0 0) R π))
        (forestGivenRoots T₀ (vList.getD 0 0) R π) := by
  obtain ⟨repList, hC, W, hspec, hlab, hrp⟩ := init_forestIn V S hn hm hn0 hG₀ hLinw hθ h₁
    h₂ hvLen hvL heLen heNd heE h₃ IO h₄ ID h₅
  refine ⟨repList, hC, W, hspec, ?_⟩
  -- the frames
  obtain ⟨_, _, _, _, _, _, _, o₁, o₃, o₄, o₅⟩ := orderPhase_post h₄
  have hFr := (orderPhase_frame IO o₁ o₃ o₄ o₅).1
  have hfid₄ := order_tOrigId IO o₁ o₃ o₄ o₅
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩ := decompPhase_post h₅
  have F1 : ∀ a < (V.withH H).dBase, (a < V.numSt ∨ V.denSt + V.eCap * V.L_w ≤ a) →
      mem₅ a = mem₄ a := (decompPhase_frame ID q₁ q₂ q₃ q₄ q₅ q₆ q₇).1
  have hH := (tree_ret V S.hh S.hLin h₃).1
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ := V.aux_order
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19,
    s20, s21, s22, s23, s24, s25, s26, -⟩ := V.scratch_order
  have k9 : V.tTail + V.tM ≤ V.tHead := IO.l9
  have k10 : V.tHead + V.tM ≤ H := IO.l10
  have k11 : H + 3 * V.n0 ≤ (V.withH H).sPtr := IO.l11
  have k12 : (V.withH H).sPtr + 4 * V.n0 + 2 * V.tM ≤ (V.withH H).eu := IO.l12
  have k13 : (V.withH H).eu + V.m0 ≤ (V.withH H).dBase := ID.L7
  have L2 : tOrigIdBase V.tPtr V.vCap V.tM + V.tM ≤ (V.withH H).dBase := ID.L2
  have hmin : V.auxPar ≤ V.minPtr := by
    simp only [InitVals.minPtr, InitVals.auxPar, auxUpMinIdxBase, auxUpVBase, auxT0DepthBase,
      auxT0ParentTreeIdxBase]
    omega
  have hvl := ID.hvlen
  have hTt : tOrigIdBase V.tPtr V.vCap V.tM + V.tM ≤ V.tPtr + tBlockSize V.vCap V.eCap V.tM := by
    simp only [tOrigIdBase, tDgTPtr, tBlockSize]; omega
  -- the tree arrays of the start of the decomposition phase
  obtain ⟨Q, tl, hd, dep, -, -, hRA, -, hTA⟩ := ID.htree
  have hI : TreeIdx (projectTree G₀ v T_raw) vList V.tM 0
      (fun i => mem₄ (tOrigIdBase V.tPtr V.vCap V.tM + i)) tl hd
      (fun x => mem₄ (V.auxPar + x)) (fun x => mem₄ (V.auxPar + V.n0 + x)) dep :=
    ⟨ID.hT, hTA, ID.hnd, ID.hV, by rw [hvl]; exact hRA, by rw [hvl]; exact ID.hn⟩
  -- the ends of the tree edges, as indices into `vList`
  have hends : ∀ i < V.tM, mem₅ (V.tTail + i) = mem₃ (V.tTail + i) ∧
      mem₅ (V.tHead + i) = mem₃ (V.tHead + i) := fun i hi => by
    have hiT : i < V.n0 := by simp only [InitVals.tM] at hi; omega
    refine ⟨?_, ?_⟩
    · rw [F1 _ (by omega) (Or.inr (by omega)), hFr _ (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨show V.thDst + V.n0 ≤ _ by omega, show _ < H by omega⟩))))]
    · rw [F1 _ (by omega) (Or.inr (by omega)), hFr _ (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨show V.thDst + V.n0 ≤ _ by omega, show _ < H by omega⟩))))]
  have hvx : ListAt mem₅ V.vListPtr vList := fun k hk => by
    have : k < V.n0 := by omega
    rw [F1 _ (by omega) (Or.inl (by omega)), hFr _ (Or.inr (Or.inl
      ⟨show V.tPtr + tBlockSize V.vCap V.eCap V.tM ≤ _ by omega,
        show _ < V.auxPar by omega⟩))]
    exact IO.hvLA k hk
  intro π T₀ R
  -- the blocks lie in `[fPtr, auxPtr)`, which the two stores keep
  have hst : ∀ a, V.fPtr ≤ a → a < V.auxPtr → mem₈ a = mem₆ a := by
    obtain ⟨_, _, heq₇, -, -, hfr₇⟩ := h₇
    simp only [List.cons.injEq] at heq₇
    obtain ⟨rfl, rfl⟩ := heq₇
    obtain ⟨_, _, heq₈, -, -, hfr₈⟩ := h₈
    simp only [List.cons.injEq] at heq₈
    obtain ⟨rfl, rfl⟩ := heq₈
    have hls : lsfHdrSize = 24 := rfl
    intro a ha1 ha2
    rw [hfr₈ a (Or.inr (by omega)), hfr₇ a (Or.inl ha2)]
  have hfW : V.fPtr + dynGraphSize V.vCap (fECap V.eCap V.n0) ≤ V.auxPtr := by
    have : 0 ≤ fAncSize V.vCap := Nat.zero_le _
    have : 0 ≤ wBlockSize V.n0 := Nat.zero_le _
    omega
  have hB := fun (RF : RootedForest) (hRF : RF.F = forestGivenRoots T₀ (vList.getD 0 0) R π)
      (hRR : RF.R = R) => fPhase_blocks (W_T := W) (RF := RF) IF h₆ hI hrp hlab hRF hRR hvl hvx
    (fun i (hi : i < V.tM) => show mem₅ (tOrigIdBase V.tPtr V.vCap V.tM + i) = _ from
      F1 _ (by omega) (Or.inl (by omega)))
    (fun i (hi : i < V.tM) => by
      show vList.getD (mem₅ (V.tTail + i)) 0 = _
      rw [(hends i hi).1]
      exact ((IO.hA.tail_eq i hi).symm.trans (congrArg _ (hfid₄ i hi).symm)).trans
        (hI.hA.tail_eq i hi))
    (fun i (hi : i < V.tM) => by
      show vList.getD (mem₅ (V.tHead + i)) 0 = _
      rw [(hends i hi).2]
      exact ((IO.hA.head_eq i hi).symm.trans (congrArg _ (hfid₄ i hi).symm)).trans
        (hI.hA.head_eq i hi))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun x (hx : x < V.n0) => show mem₅ (V.auxPar + x) = _ from
      F1 _ (by omega) (Or.inl (by omega)))
    (fun x (hx : x < V.n0) => show mem₅ (V.auxPar + V.n0 + x) = _ from
      F1 _ (by omega) (Or.inl (by omega)))
  obtain ⟨hF, -, hW⟩ := hB ⟨forestGivenRoots T₀ (vList.getD 0 0) R π, R⟩ rfl rfl
  refine ⟨hF.of_agree fun a (h1 : V.fPtr ≤ a)
      (h2 : a < V.fPtr + dynGraphSize V.vCap (fECap V.eCap V.n0)) => hst a h1 (by omega),
    fun RF hRF hRR => (hB RF hRF hRR).2.1.of_agree fun a (h1 : V.fAncPtr ≤ a)
      (h2 : a < V.fAncPtr + fAncSize V.vCap) => hst a (by omega) (by omega),
    hW.of_agree fun a (h1 : V.wPtr ≤ a) (h2 : a < V.wPtr + wBlockSize V.n0) =>
      hst a (by omega) (by omega)⟩

end

end MinCostFlow.LSF.Program
