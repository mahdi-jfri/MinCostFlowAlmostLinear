module

public import MinCostFlow.LSF.Program.InitWstrMain
public import MinCostFlow.LSF.Program.InitRootsOut
public import MinCostFlow.LSF.Program.InitMainBase

/-!
# What the forest phase reads, in the terms of the driver

`init_forestIn` takes the posts that `main_wp` hands to its final condition, up to the
decomposition phase, and gives the inputs of the forest bridges: the representatives of the prep
stage (`IsCompReps`), a decomposition `W` with its labels, and the roots pass of the root set
`R₀_init` of `initLSFWith`. The representatives stay at `repPtr` from the prep stage to the
decomposition phase (`init_repList_at`); the rest is `decompPhase_forestIn`, with the high flags
of `order_decomp_wstrAt` and the edge facts of `order_ends`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.Num
  InitDriver

@[expose] public section

/-- The list at `repPtr` that the prep stage writes is still there at the start of the
decomposition phase: the widths call, the tree phase and the order phase do not write it. -/
lemma init_repList_at {w h : ℕ} {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ} {G₀ T₀ : MGraph}
    {v ℓ₀ : ℕ → ℝ} {P_fp lenArr wtArr H nOrig : ℕ} {bRoot bStore bOrder bT bTH v₄ : ℕ}
    {mem₁ mem₂ mem₃ mem₄ : ℕ → ℕ} {vList eList repList : List ℕ} (V : InitVals)
    (h₂ : (widthsContract w).post [V.m0, V.L_in, V.endA + 3] mem₁ 0 mem₂)
    (h₃ : (treePhaseContract Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp vList eList).post
        (treeArgsV V lenArr wtArr) mem₂ H mem₃)
    (IO : OrderPhaseIn w h G₀ T₀ vList eList (OrderLayout.ofVals (V.withH H) nOrig) mem₃)
    (h₄ : (orderPhaseContract w h G₀ T₀ vList eList bRoot bStore bOrder bT bTH).post
      (OrderLayout.ofVals (V.withH H) nOrig).args mem₃ v₄ mem₄)
    (hH : V.lsstHeap ≤ H) (hrl : repList.length ≤ V.vCap)
    (hL : ListAt mem₁ V.repPtr repList) : ListAt mem₄ V.repPtr repList := by
  obtain ⟨_, _, _, _, _, _, _, o₁, o₃, o₄, o₅⟩ := orderPhase_post h₄
  have hFr := (orderPhase_frame IO o₁ o₃ o₄ o₅).1
  have hfr₃ := tree_frame_low V h₃
  obtain ⟨m', L', o', heq₂, -, -, -, -, hfr₂⟩ := h₂
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl⟩ := heq₂
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ := V.aux_order
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, -⟩ :=
    V.scratch_order
  refine fun k hk => Eq.trans ?_ (hL k hk)
  have hk' : V.repPtr + k < V.endA := by omega
  rw [hFr _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨show V.thDst + V.n0 ≤ _ by omega,
      show _ < H by omega⟩)))), hfr₃ _ (by omega), hfr₂ _ (Or.inl (by omega))]

open Classical in
set_option maxHeartbeats 1600000 in
/-- After the decomposition phase of the driver: the representatives of the prep stage, a
decomposition `W` of `T₀` with its labels, and the roots pass of the first root set of
`initLSFWith` with the threshold `threshProd C n₀ kk`. -/
theorem init_forestIn {w h C : ℕ} {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ} {G₀ : MGraph}
    {v ℓ₀ : ℕ → ℝ} {P_fp : ℕ} {g0Ptr vCap0 eCap0 lenArr wtArr kk cnt H : ℕ}
    {bRoot bStore bOrder bT bTH bWT bLB bW bCopy bFlag bRoots : ℕ}
    {mem mem₁ mem₂ mem₃ mem₄ mem₅ : ℕ → ℕ} {v₄ v₅ : ℕ} {vList eList : List ℕ} {T_raw : MGraph}
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
          (hldDepthBound V.n0) kk lenArr cnt).args mem₄ v₅ mem₅) :
    ∃ repList : List ℕ, IsCompReps G₀ (vList.getD 0 0) repList.toFinset ∧
    ∃ W : Finset (Finset ℕ), IsTreeDecompSpec G₀ (projectTree G₀ v T_raw) kk W ∧
      WLabels (projectTree G₀ v T_raw) vList 0 W
        (fun x => (mem₅ ((V.withH H).dBase + 6 * V.n0 + x),
          mem₅ ((V.withH H).dBase + 7 * V.n0 + x))) ∧
      RootPassIdx (projectTree G₀ v T_raw) vList V.tM 0
        (fun i => mem₄ (tOrigIdBase V.tPtr V.vCap V.tM + i))
        (fun x => mem₄ (V.auxPar + x)) (fun x => mem₄ (V.auxPar + V.n0 + x))
        (upClosure (hldAuxTree (projectTree G₀ v T_raw) (vList.getD 0 0)) (vList.getD 0 0)
          (repList.toFinset ∪ boundary W ∪
            (G₀.E.filter fun e => (threshProd C V.n0 kk : ℝ) ≤
              levelStretchBound (projectTree G₀ v T_raw) (vList.getD 0 0)
                (orderPi (OrderLayout.ofVals (V.withH H) (mem₃ V.outHdr)) mem₃ mem₄) G₀
                (safeLen G₀ ℓ₀) e).biUnion fun e => {G₀.tail e, G₀.head e}))
        (orderPi (OrderLayout.ofVals (V.withH H) (mem₃ V.outHdr)) mem₃ mem₄)
        (fun y => mem₅ ((V.withH H).inR + y)) (fun i => mem₄ (tPiBase V.tPtr V.vCap V.tM + i))
        (fun y => mem₅ ((V.withH H).inR + V.n0 + y))
        (fun i => mem₅ ((V.withH H).inR + V.n0 + V.n0 + i))
        (fun y => mem₅ ((V.withH H).inR + V.n0 + V.n0 + V.tM + y)) := by
  have hπ := (order_pi_of_posts V S hn hm h₁ h₂ heLen heNd heE h₃ IO h₄).1
  have hlen := init_len_facts V S hn h₁ h₂ h₃
  have hhL : 2 ≤ h * V.L_w := le_trans S.h2L (Nat.mul_le_mul_left _ hLinw)
  have hhigh := (order_decomp_wstrAt (P := P_fp) IO h₄ ID h₅ hπ heE hlen hhL hθ rfl).2
  obtain ⟨heL₄, hends⟩ := order_ends IO h₄
  have hpiv := order_pi_idx IO h₄
  obtain ⟨repList, hrl, -, -, hrL, hC⟩ := prep_reps h₁ h₂ hn hvLen hvL
  have hcn : cnt ≤ V.n0 := hn ▸ prep_cnt_le h₁
  have hH := (tree_ret V S.hh S.hLin h₃).1
  have hrL₄ := init_repList_at V h₂ h₃ IO h₄ hH (by omega) hrL
  have hreq : (List.range cnt).map (fun j => mem₄ (V.repPtr + j)) = repList := by
    refine List.ext_getElem (by simp [hrl]) fun j h1 h2 => ?_
    rw [List.getElem_map, List.getElem_range]
    exact hrL₄ j h2
  have hvl := ID.hvlen
  have heuv := ID.heuv
  have hTV : (projectTree G₀ v T_raw).V = G₀.V :=
    Finset.ext fun u => (IO.hV u).trans (IO.hGV u).symm
  have hn2 := IO.hn2
  obtain ⟨W, hspec, hlab, hrp⟩ := decompPhase_forestIn (G₀ := G₀) (eList := eList)
    (P := fun e => (threshProd C V.n0 kk : ℝ) ≤
      levelStretchBound (projectTree G₀ v T_raw) (vList.getD 0 0)
        (orderPi (OrderLayout.ofVals (V.withH H) (mem₃ V.outHdr)) mem₃ mem₄) G₀
        (safeLen G₀ ℓ₀) e) ID h₅ hG₀ hTV (show 0 < kk from S.hk)
    (by
      show 4 * kk * (hldDepthBound V.n0 + 1) = 4 * kk * (hldDepthBound G₀.n + 1); rw [hn]) hn2 heNd heE heLen heL₄
    (fun t ht => ⟨by rw [hvLen]; exact (heuv t (show t < V.m0 by omega)).1,
      (hends t (show t < V.m0 by omega)).1⟩)
    (fun t ht => ⟨by rw [hvLen]; exact (heuv t (show t < V.m0 by omega)).2,
      (hends t (show t < V.m0 by omega)).2⟩)
    (fun j hj => by
      show mem₄ (V.repPtr + j) ∈ vList
      rw [hrL₄ j (by rw [hrl]; exact hj)]
      exact (IO.hGV _).mp (hC.2.1 (List.mem_toFinset.mpr (List.getElem_mem _))))
    IO.hvCap
    (fun i hi => by
      obtain ⟨_, _, _, _, _, _, _, o₁, o₃, o₄, o₅⟩ := orderPhase_post h₄
      have hFr := (orderPhase_frame IO o₁ o₃ o₄ o₅).1
      obtain ⟨e1, e2, e3, -⟩ := V.aux_order
      have : vList[i] < V.vCap := IO.hvCap _ (List.getElem_mem hi)
      show mem₄ (V.vIdx + vList[i]) = i + 1
      rw [hFr _ (Or.inr (Or.inl ⟨show V.tPtr + tBlockSize V.vCap V.eCap V.tM ≤ _ by omega,
        show _ < V.auxPar by omega⟩))]
      exact IO.hvI i hi)
    (fun t ht => by
      show mem₅ ((V.withH H).hiCopy + t) = 1 ↔ _
      rw [hhigh t ht, heL₄ t ht]
      split_ifs with hc
      · exact iff_of_true rfl hc
      · exact iff_of_false (by decide) hc)
    hπ hpiv
  refine ⟨repList, hC, W, hspec, hlab, ?_⟩
  rw [← hreq]
  exact hrp

end

end MinCostFlow.LSF.Program
