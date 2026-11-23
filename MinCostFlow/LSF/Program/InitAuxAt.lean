module

public import MinCostFlow.LSF.Program.InitForest
public import MinCostFlow.LSF.Program.InitAux
public import MinCostFlow.LSF.Program.OrderPhaseMin

/-!
# The aux block of the initial state, in the terms of the driver

`init_auxAt` gives `AuxAt` of the aux block at the end of the driver, from the posts that
`main_wp` hands to its final condition. It feeds `auxAt_init` (through `auxAt_init_n`, which
states the length of the vertex list as `n₀`), with the inputs taken from these places.

* The header and the root index `0` come from the two header stores (`init_auxHeader`).
* The tree arrays (parents, parent edges, depths), the ancestor table, the minimum table and the
  parents of `T_H` are written by the order phase. They lie in the aux block below `numSt`,
  which the decomposition phase, the forest phase and the stores keep. The tree arrays and the
  ancestor table are stated by `DecompPhaseIn.htree`, the minimum table by
  `orderPhase_minTable`, the parents of `T_H` by `DecompPhaseIn.hthPar` and the post of the
  `T_H` stage at the root.
* The vertex list and its index come from `OrderPhaseIn`.
* The index outside the vertices, the flags of the original vertices, their names and the two
  visit arrays come from the post of the prep stage. They lie in the aux block below `auxPar` or
  above `thDst + n₀`, which no later call writes.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.Num
  InitDriver

@[expose] public section

/-- `auxAt_init` with the length of the vertex list given as a number `n`, and with the tree
`T₀` of the state given by an equation. -/
theorem auxAt_init_n {mem : ℕ → ℕ} {auxPtr vCap tM r n : ℕ} {S : LSFState} {T₀ : MGraph}
    {tOrigList vList : List ℕ} {fid tl hd : ℕ → ℕ} (hn : vList.length = n) (hST : S.T₀ = T₀)
    (hH : AuxHeader mem auxPtr vCap n)
    (hr0 : mem (auxPtr + auxOffR0Idx) = r) (hS0 : S.r₀ = vList.getD r 0)
    (hTI : TreeIdx T₀ vList tM r fid tl hd
      (fun x => mem (auxT0ParentBase auxPtr vCap n + x))
      (fun x => mem (auxT0ParentTreeIdxBase auxPtr vCap n + x))
      (fun x => mem (auxT0DepthBase auxPtr vCap n + x)))
    (hlenT : tOrigList.length = tM) (hfid : ∀ t < tM, fid t = tOrigList.getD t 0)
    (hper : 0 < tM → mem (auxT0ParentTreeIdxBase auxPtr vCap n + r) < tM)
    (hvLA : ListAt mem (auxVListBase auxPtr vCap) vList)
    (hvIdx : ∀ i (hi : i < vList.length), mem (auxVIdxBase auxPtr + vList[i]) = i + 1)
    (hvIdx0 : ∀ v < vCap, v ∉ T₀.V → mem (auxVIdxBase auxPtr + v) = 0)
    (hup : ∀ i < n, ∀ j < auxLogCap n,
      mem (auxUpVBase auxPtr vCap n + (i * auxLogCap n + j)) =
        liftF (fun x => mem (auxT0ParentBase auxPtr vCap n + x)) i j)
    (hmin : ∀ i < n, ∀ j < auxLogCap n,
      mem (auxUpMinIdxBase auxPtr vCap n + (i * auxLogCap n + j)) =
        liftMin (fun i j => liftF (fun x => mem (auxT0ParentBase auxPtr vCap n + x)) i j)
          (fun x => mem (auxT0ParentTreeIdxBase auxPtr vCap n + x))
          (fun t => S.π (fid t)) r i j)
    (hth : ∀ x < n, x ≠ r →
      mem (auxThParentBase auxPtr vCap n + x) < n ∧
      vList.getD (mem (auxThParentBase auxPtr vCap n + x)) 0 =
        thParent T₀ (vList.getD r 0) (vList.getD x 0))
    (hthr : mem (auxThParentBase auxPtr vCap n + r) = r)
    (hIso : ∀ v < vCap, mem (auxIsOrigVertBase auxPtr vCap n + v) =
      if v ∈ T₀.V then 1 else 0)
    (hOrig : ∀ w ∈ S.G.V, w < vCap →
      mem (auxOrigVertBase auxPtr vCap n + w) = S.origVert w)
    (hVis : ∀ v < vCap, mem (auxVisABase auxPtr vCap n + v) = 0 ∧
      mem (auxVisBBase auxPtr vCap n + v) = 0) :
    AuxAt mem auxPtr vCap n tM S tOrigList vList
      (fun x => mem (auxT0ParentBase auxPtr vCap n + x))
      (fun x => mem (auxT0ParentTreeIdxBase auxPtr vCap n + x))
      (fun x => mem (auxT0DepthBase auxPtr vCap n + x))
      (fun x => mem (auxThParentBase auxPtr vCap n + x))
      (fun i j => mem (auxUpVBase auxPtr vCap n + (i * auxLogCap n + j)))
      (fun i j => mem (auxUpMinIdxBase auxPtr vCap n + (i * auxLogCap n + j))) := by
  subst hn
  exact auxAt_init hH hr0 hS0 (by rw [hST]; exact hTI) hlenT hfid hper hvLA hvIdx
    (by rw [hST]; exact hvIdx0) hup hmin (by rw [hST]; exact hth) hthr
    (by rw [hST]; exact hIso) hOrig hVis

/-- The arrays of the aux block after `thDst + n₀` lie below `numSt`. -/
lemma InitVals.aux_tail_places (V : InitVals) {v : ℕ} (hv : v < V.vCap) :
    V.thDst + V.n0 ≤ auxOrigVertBase V.auxPtr V.vCap V.n0 + v ∧
    auxOrigVertBase V.auxPtr V.vCap V.n0 + v < V.numSt ∧
    V.thDst + V.n0 ≤ auxIsOrigVertBase V.auxPtr V.vCap V.n0 + v ∧
    auxIsOrigVertBase V.auxPtr V.vCap V.n0 + v < V.numSt ∧
    V.thDst + V.n0 ≤ auxVisABase V.auxPtr V.vCap V.n0 + v ∧
    auxVisABase V.auxPtr V.vCap V.n0 + v < V.numSt ∧
    V.thDst + V.n0 ≤ auxVisBBase V.auxPtr V.vCap V.n0 + v ∧
    auxVisBBase V.auxPtr V.vCap V.n0 + v < V.numSt := by
  have e7 := V.aux_order.2.2.2.2.2.2.1
  simp only [auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase, auxIsOrigVertBase,
    auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase, auxT0DepthBase,
    auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase, auxHdrSize, auxSize,
    InitVals.thDst] at e7 ⊢
  omega

/-- The aux block and the numerators of the stretches lie below the scratch area of the forest
phase. -/
lemma InitVals.numSt_le_wBase (V : InitVals) (hH : V.lsstHeap ≤ V.H) : V.numSt ≤ V.wBase := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ := V.aux_order
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19,
    s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32⟩ := V.scratch_order
  omega

open Classical in
set_option maxHeartbeats 1600000 in
/-- At the end of the driver, the aux block represents the tree `T₀` of the state, with the
vertex list of the prep stage, the root index `0`, the edge list of the tree stage and the
order of the order phase. -/
theorem init_auxAt {w h C : ℕ} {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ} {G₀ T₀ : MGraph}
    {v ℓ₀ : ℕ → ℝ} {P_fp g0Ptr vCap0 eCap0 lenArr wtArr kk cnt₀ cnt H nOrig : ℕ}
    {bRoot bStore bOrder bT bTH bWT bLB bW bCopy bFlag bRoots bG bA bWF : ℕ}
    {mem mem₁ mem₂ mem₃ mem₄ mem₅ mem₆ mem₇ mem₈ : ℕ → ℕ} {v₄ v₅ v₆ v₇ v₈ : ℕ}
    {vList eList vs₈ : List ℕ} {S : LSFState} (V : InitVals)
    (hn : G₀.n = V.n0) (hH : V.lsstHeap ≤ H)
    (h₁ : (prepStageContract w G₀).post (prepArgsV V g0Ptr vCap0 eCap0 kk) mem cnt₀ mem₁)
    (h₂ : (widthsContract w).post [V.m0, V.L_in, V.endA + 3] mem₁ 0 mem₂)
    (hvLen : vList.length = V.n0) (hvL : ListAt mem₂ V.vListPtr vList)
    (h₃ : (treePhaseContract Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp vList eList).post
        (treeArgsV V lenArr wtArr) mem₂ H mem₃)
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
    (h₇ : (storeArgsContract w 20).post (V.auxPtr :: auxHdrVals V) mem₆ v₇ mem₇)
    (h₈ : (storeArgsContract w 24).post (V.b :: vs₈) mem₇ v₈ mem₈)
    (hST : S.T₀ = T₀) (hSr : S.r₀ = vList.getD 0 0)
    (hSπ : S.π = orderPi (OrderLayout.ofVals (V.withH H) nOrig) mem₃ mem₄)
    (hSG : ∀ x ∈ S.G.V, x ∈ G₀.V ∧ S.origVert x = x) :
    AuxAt mem₈ V.auxPtr V.vCap V.n0 V.tM S (tStageList mem₃ V.tOrig V.tM) vList
      (fun x => mem₈ (auxT0ParentBase V.auxPtr V.vCap V.n0 + x))
      (fun x => mem₈ (auxT0ParentTreeIdxBase V.auxPtr V.vCap V.n0 + x))
      (fun x => mem₈ (auxT0DepthBase V.auxPtr V.vCap V.n0 + x))
      (fun x => mem₈ (auxThParentBase V.auxPtr V.vCap V.n0 + x))
      (fun i j => mem₈ (auxUpVBase V.auxPtr V.vCap V.n0 + (i * auxLogCap V.n0 + j)))
      (fun i j => mem₈ (auxUpMinIdxBase V.auxPtr V.vCap V.n0 + (i * auxLogCap V.n0 + j))) := by
  obtain ⟨hAH, hr0⟩ := init_auxHeader h₇ h₈
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ := V.aux_order
  have hmP := V.minPtr_eq
  have hq : V.endA + 6 = V.qNat := V.scratch_order.1
  have hhdr : auxHdrSize = 20 := rfl
  have hvI : V.vIdx = V.auxPtr + 20 := rfl
  have hn2 : 2 ≤ V.n0 := IO.hn2
  have htM : V.tM = V.n0 - 1 := IO.htM
  -- the frames, from the prep stage to the end of the driver
  obtain ⟨_, _, _, _, _, _, _, o₁, o₃, o₄, o₅⟩ := orderPhase_post h₄
  obtain ⟨hFr, -, -, -, -, hpe0⟩ := orderPhase_frame IO o₁ o₃ o₄ o₅
  have l6 : V.thDst + V.n0 ≤ V.qNat := IO.l6
  have hrt : V.qNat ≤ (V.withH H).rtOut := by
    have l7 := IO.l7; have l8 := IO.l8; have l9 := IO.l9; have l10 := IO.l10
    exact le_trans (Nat.le_add_right _ _) (l7.trans (le_trans (Nat.le_add_right _ _)
      (l8.trans (le_trans (Nat.le_add_right _ _) (l9.trans (le_trans (Nat.le_add_right _ _)
        l10))))))
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩ := decompPhase_post h₅
  have F1 : ∀ a < (V.withH H).dBase, (a < V.numSt ∨ V.denSt + V.eCap * V.L_w ≤ a) →
      mem₅ a = mem₄ a := (decompPhase_frame ID q₁ q₂ q₃ q₄ q₅ q₆ q₇).1
  have L14 : V.denSt + V.eCap * V.L_w ≤ (V.withH H).dBase := ID.L14
  have hfr := init_tail_frame (V := V.withH H) h₆ h₇ h₈ hH
  have hwb' : V.numSt ≤ (V.withH H).wBase := (V.withH H).numSt_le_wBase hH
  have K84 : ∀ a, V.vIdx ≤ a → a < V.numSt → mem₈ a = mem₄ a := fun a h1 h2 => by
    rw [hfr a (Or.inr ⟨show V.auxPtr + 20 ≤ a by omega, show a < (V.withH H).wBase by omega⟩)]
    exact F1 a (by omega) (Or.inl h2)
  have K43 : ∀ a, V.vIdx ≤ a → (a < V.auxPar ∨ (V.thDst + V.n0 ≤ a ∧ a < V.numSt)) →
      mem₄ a = mem₃ a := fun a h1 h2 => by
    refine hFr a ?_
    rcases h2 with h2 | ⟨h2, h3⟩
    · exact Or.inr (Or.inl ⟨show V.tPtr + tBlockSize V.vCap V.eCap V.tM ≤ a by omega,
        show a < V.auxPar from h2⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨show V.thDst + V.n0 ≤ a from h2,
        show a < (V.withH H).rtOut by omega⟩)))
  have K32 : ∀ a < V.qNat, mem₃ a = mem₂ a := tree_frame_low V h₃
  obtain ⟨m', L', o', heq₂, -, -, -, -, hfr₂⟩ := h₂
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl⟩ := heq₂
  have K81 : ∀ a, V.vIdx ≤ a → (a < V.auxPar ∨ (V.thDst + V.n0 ≤ a ∧ a < V.numSt)) →
      mem₈ a = mem₁ a := fun a h1 h2 => by
    have h3 : a < V.numSt := by rcases h2 with h2 | h2 <;> omega
    rw [K84 a h1 h3, K43 a h1 h2, K32 a (by omega), hfr₂ a (Or.inl (by omega))]
  -- the post of the prep stage
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, heq₁, -, -, -, -, -, -, -, -, -,
    hvI0, hIso₁, hOrig₁, hVis₁, -, -, -, -, -, -, -, -⟩ := h₁
  simp only [prepArgsV, List.cons.injEq, and_true] at heq₁
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, -, -, -, -⟩ := heq₁
  rw [hn] at hIso₁ hOrig₁ hVis₁
  -- the tree arrays of the start of the decomposition phase
  obtain ⟨Q, tl, hd, dep, -, -, hRA, hLT, hTA⟩ := ID.htree
  have hpar84 : ∀ x < V.n0, mem₄ (V.auxPar + x) = mem₈ (V.auxPar + x) := fun x hx =>
    (K84 _ (by omega) (by omega)).symm
  have hpe84 : ∀ x < V.n0, mem₄ (V.auxPar + V.n0 + x) = mem₈ (V.auxPar + V.n0 + x) :=
    fun x hx => (K84 _ (by omega) (by omega)).symm
  have hdep8 : ∀ x < V.n0, dep x = mem₈ (V.auxPar + V.n0 + V.n0 + x) := fun x hx => by
    rw [K84 _ (by omega) (by omega)]; exact (hLT.hd x hx).symm
  have hparlt : ∀ x < V.n0, mem₄ (V.auxPar + x) < V.n0 := hRA.par_lt
  have hpe4lt : ∀ i < V.n0, mem₄ (V.auxPar + V.n0 + i) < V.tM := fun i hi => by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [Nat.add_zero]
      have : mem₄ (V.auxPar + V.n0) = 0 := hpe0
      omega
    · exact (hRA.step i hi (by omega)).1
  have hR8 : RootedArrays V.n0 V.tM 0 tl hd
      (fun x => mem₈ (auxT0ParentBase V.auxPtr V.vCap V.n0 + x))
      (fun x => mem₈ (auxT0ParentTreeIdxBase V.auxPtr V.vCap V.n0 + x))
      (fun x => mem₈ (auxT0DepthBase V.auxPtr V.vCap V.n0 + x)) :=
    hRA.congr (by show 0 < V.n0; omega) hpar84 hpe84 hdep8
  have hTI : TreeIdx T₀ vList V.tM 0 (fun i => mem₄ (tOrigIdBase V.tPtr V.vCap V.tM + i)) tl hd
      (fun x => mem₈ (auxT0ParentBase V.auxPtr V.vCap V.n0 + x))
      (fun x => mem₈ (auxT0ParentTreeIdxBase V.auxPtr V.vCap V.n0 + x))
      (fun x => mem₈ (auxT0DepthBase V.auxPtr V.vCap V.n0 + x)) :=
    ⟨ID.hT, hTA, ID.hnd, ID.hV, by rw [hvLen]; exact hR8, by rw [hvLen]; omega⟩
  have hfid₄ := order_tOrigId IO o₁ o₃ o₄ o₅
  -- the minimum table
  have hM4 := orderPhase_minTable IO o₁ o₃ o₄ o₅ hpe4lt
  have hC := liftMin_congr_all (r := 0) (n := V.n0) (L := auxLogCap V.n0) (tM := V.tM)
    (U := fun i j => liftF (fun x => mem₄ (V.auxPar + x)) i j)
    (pe := fun x => mem₄ (V.auxPar + V.n0 + x))
    (piv := fun t => mem₄ (tPiBase V.tPtr V.vCap V.tM + t))
    (U' := fun i j => liftF (fun x => mem₈ (auxT0ParentBase V.auxPtr V.vCap V.n0 + x)) i j)
    (pe' := fun x => mem₈ (auxT0ParentTreeIdxBase V.auxPtr V.vCap V.n0 + x))
    (piv' := fun t => S.π (mem₄ (tOrigIdBase V.tPtr V.vCap V.tM + t)))
    (fun i hi j _ => liftF_congr hparlt hpar84 j i hi)
    (fun i hi j _ => liftF_lt hparlt j i hi) hpe84 hpe4lt
    (fun t ht => by rw [hSπ]; exact (order_pi_idx IO h₄ t ht).symm)
  have hL : 1 ≤ auxLogCap V.n0 := by unfold auxLogCap; omega
  have hij : ∀ i < V.n0, ∀ j < auxLogCap V.n0, i * auxLogCap V.n0 + j < V.n0 * auxLogCap V.n0 :=
    fun i hi j hj => by
      have : (i + 1) * auxLogCap V.n0 ≤ V.n0 * auxLogCap V.n0 := Nat.mul_le_mul_right _ hi
      rw [Nat.add_mul, Nat.one_mul] at this; omega
  have a3 : auxUpVBase V.auxPtr V.vCap V.n0 = V.auxPar + 3 * V.n0 := by
    simp only [auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, InitVals.auxPar]; omega
  refine auxAt_init_n hvLen hST hAH hr0 (by rw [hSr]) hTI (by simp [tStageList])
    (fun t ht => ?_) (fun htM0 => ?_) (fun k hk => ?_) (fun i hi => ?_) (fun x hx hxT => ?_)
    (fun i hi j hj => ?_) (fun i hi j hj => ?_) (fun x hx hx0 => ?_) ?_ (fun x hx => ?_)
    (fun x hx hxc => ?_) (fun x hx => ?_)
  · -- the edge IDs
    simp only [tStageList, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht,
      Option.map_some, Option.getD_some]
    exact hfid₄ t ht
  · -- the parent edge of the root
    have := hpe4lt 0 (by omega)
    show mem₈ (V.auxPar + V.n0 + 0) < V.tM
    rw [← hpe84 0 (by omega)]; exact this
  · -- the vertex list
    have hk' : k < V.n0 := by rw [← hvLen]; exact hk
    show mem₈ (V.vListPtr + k) = _
    rw [K84 _ (by omega) (by omega), K43 _ (by omega) (Or.inl (by omega))]
    exact IO.hvLA k hk
  · -- the index of the vertex list
    have : vList[i] < V.vCap := IO.hvCap _ (List.getElem_mem hi)
    show mem₈ (V.vIdx + _) = _
    rw [K84 _ (by omega) (by omega), K43 _ (by omega) (Or.inl (by omega))]
    exact IO.hvI i hi
  · -- the index outside the vertices
    have hxG : x ∉ G₀.V := fun h' => hxT ((IO.hV x).mpr ((IO.hGV x).mp h'))
    show mem₈ (V.vIdx + x) = 0
    rw [K81 _ (by omega) (Or.inl (by omega))]
    exact hvI0 x hx hxG
  · -- the ancestor table
    have := hij i hi j hj
    rw [K84 _ (by rw [a3]; omega) (by rw [a3]; omega), a3]
    exact (hLT.hup i hi j hj).trans (liftF_congr hparlt hpar84 j i hi)
  · -- the minimum table
    have := hij i hi j hj
    show mem₈ (V.minPtr + _) = _
    rw [K84 _ (by omega) (by omega)]
    exact (hM4 i hi j hj).trans (hC j hj.le i hi).1
  · -- the parents of `T_H`
    show mem₈ (V.thDst + x) < V.n0 ∧ vList.getD (mem₈ (V.thDst + x)) 0 = _
    rw [K84 _ (by omega) (by omega)]
    exact ID.hthPar x hx hx0
  · -- the parent of the root in `T_H`
    obtain ⟨_, _, _, _, _, _, _, heq₅, -, -, hth0, -, -⟩ := o₅
    simp only [List.cons.injEq, and_true] at heq₅
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₅
    show mem₈ (V.thDst + 0) = 0
    rw [K84 _ (by omega) (by omega)]
    exact hth0
  · -- the flags of the original vertices
    obtain ⟨-, -, h1, h2, -⟩ := V.aux_tail_places hx
    rw [K81 _ (by omega) (Or.inr ⟨h1, h2⟩), hIso₁ x hx]
    exact if_congr ((IO.hGV x).trans (IO.hV x).symm) rfl rfl
  · -- the names of the original vertices
    obtain ⟨hxG, hxo⟩ := hSG x hx
    obtain ⟨h1, h2, -⟩ := V.aux_tail_places hxc
    rw [K81 _ (by omega) (Or.inr ⟨h1, h2⟩), hOrig₁ x hxG hxc, hxo]
  · -- the two visit arrays
    obtain ⟨-, -, -, -, h1, h2, h3, h4⟩ := V.aux_tail_places hx
    rw [K81 _ (by omega) (Or.inr ⟨h1, h2⟩), K81 _ (by omega) (Or.inr ⟨h3, h4⟩)]
    exact hVis₁ x hx
