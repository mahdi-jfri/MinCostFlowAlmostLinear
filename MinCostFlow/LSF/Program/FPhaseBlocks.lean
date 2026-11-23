module

public import MinCostFlow.LSF.Program.FPhase
public import MinCostFlow.LSF.Program.FBridge
public import MinCostFlow.LSF.Program.WBridge

/-!
# The three blocks after the forest phase

The forest phase runs `fGraphProc`, `fAncFillProc` and `wBlockProc`. Each post states its block in
terms of the arrays it reads, at the memory just before the call. `fPhase_blocks` turns the three
posts into the blocks of the model: `DynGraphAt` of the forest `F_T(R, π)`, `FAncAt` of `(F, R)`
and `WBlockAt` of `refineDecomp W_T F`. It applies `fGraph_bridge`, `fAnc_bridge` and
`wBlock_bridge`. The arrays these read lie outside the blocks that the earlier calls write, so
they still hold the values of the start memory, and the congruence lemmas below move each post
to the functions of the start memory.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

lemma rootList_congr {vL vL' inR inR' : ℕ → ℕ} {j : ℕ} (h1 : ∀ x < j, vL x = vL' x)
    (h2 : ∀ x < j, inR x = inR' x) : rootList vL inR j = rootList vL' inR' j := by
  unfold rootList
  rw [List.filter_congr (fun x hx => by rw [h2 x (List.mem_range.mp hx)])]
  exact List.map_congr_left fun x hx => h1 x (List.mem_range.mp (List.mem_filter.mp hx).1)

lemma isRootVal_congr {vL vL' inR inR' : ℕ → ℕ} {j : ℕ} (h1 : ∀ x < j, vL x = vL' x)
    (h2 : ∀ x < j, inR x = inR' x) (v : ℕ) :
    isRootVal vL inR j v = isRootVal vL' inR' j v := by
  have hiff : (∃ x < j, inR x = 1 ∧ vL x = v) ↔ (∃ x < j, inR' x = 1 ∧ vL' x = v) :=
    ⟨fun ⟨x, hx, a, b⟩ => ⟨x, hx, (h2 x hx) ▸ a, (h1 x hx) ▸ b⟩,
      fun ⟨x, hx, a, b⟩ => ⟨x, hx, (h2 x hx).symm ▸ a, (h1 x hx).symm ▸ b⟩⟩
  unfold isRootVal
  by_cases ha : ∃ x < j, inR x = 1 ∧ vL x = v
  · rw [if_pos ha, if_pos (hiff.mp ha)]
  · rw [if_neg ha, if_neg (fun h => ha (hiff.mpr h))]

lemma sizeVal_congr {vL vL' rt rt' : ℕ → ℕ} {j : ℕ} (h1 : ∀ x < j, vL (rt x) = vL' (rt' x))
    (v : ℕ) : sizeVal vL rt j v = sizeVal vL' rt' j v := by
  unfold sizeVal
  rw [Finset.filter_congr (fun x hx => by rw [h1 x (Finset.mem_range.mp hx)])]

lemma WLabels.congr {T₀ : MGraph} {vList : List ℕ} {r : ℕ} {W_T : Finset (Finset ℕ)}
    {lab lab' : ℕ → ℕ × ℕ} (h : WLabels T₀ vList r W_T lab)
    (e : ∀ x < vList.length, lab' x = lab x) : WLabels T₀ vList r W_T lab' :=
  ⟨h.hconv, h.hdisj, h.hcov, fun x hx hxr x' hx' hxr' => by
    rw [e x hx, e x' hx']; exact h.hlab x hx hxr x' hx' hxr'⟩

lemma WKeyOK.congr_rt {K s lY lB rt rt' : ℕ → ℕ} {cnt : ℕ} (h : WKeyOK K s lY lB rt cnt)
    (e : ∀ j < cnt, rt' (s j) = rt (s j)) : WKeyOK K s lY lB rt' cnt :=
  ⟨h.1, fun j hj j' hj' => by rw [e j hj, e j' hj']; exact h.2 j hj j' hj'⟩

/-- The vertices of the groups are kept indices or their parents, so they lie below `n`. -/
lemma flatV_wGroups_lt {K s pa : ℕ → ℕ} {cnt n : ℕ}
    (hsort : ∀ i j, i ≤ j → j < cnt → K (s i) ≤ K (s j)) (hs : ∀ j < cnt, s j < n)
    (hpa : ∀ x < n, pa x < n) : ∀ y ∈ flatV (wGroups K s pa cnt), y < n := by
  have GI := groupsInv_of_le (pa := pa) hsort cnt le_rfl
  intro y hy
  unfold flatV at hy
  obtain ⟨l, hl, hyl⟩ := List.mem_flatten.mp hy
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hl
  obtain ⟨x, hx, hxy⟩ := ((GI.hvert q hq).2 y).mp hyl
  have hxS : x ∈ (List.range cnt).map s := by
    rw [← GI.hflat]; exact List.mem_flatten.mpr ⟨q.1, List.mem_map_of_mem hq, hx⟩
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hxS
  have := hs j (List.mem_range.mp hj)
  rcases hxy with rfl | rfl
  · exact this
  · exact hpa _ this

set_option maxHeartbeats 800000 in
/-- After the forest phase, its three blocks represent the forest `F_T(R, π)`, the rooted forest
`(F, R)` and the refined decomposition, when the arrays of the start memory are the tree arrays
of `hI` and the roots pass `hR`, and the labels name the pieces of `W_T`. -/
theorem fPhase_blocks {w h : ℕ} {X : FLayout} {bG bA bW : ℕ} {mem mem₃ : ℕ → ℕ} {ret : ℕ}
    {T₀ : MGraph} {vList : List ℕ} {fid tl hd par pe dep : ℕ → ℕ} {R : Finset ℕ}
    {π inR piv mp own rt : ℕ → ℕ} {W_T : Finset (Finset ℕ)} {RF : RootedForest}
    (I : FPhaseIn w h X mem)
    (hpost : (fPhaseContract w h bG bA bW).post X.args mem ret mem₃)
    (hI : TreeIdx T₀ vList X.tM 0 fid tl hd par pe dep)
    (hR : RootPassIdx T₀ vList X.tM 0 fid par pe R π inR piv mp own rt)
    (hW : WLabels T₀ vList 0 W_T
      (fun x => (mem (X.dBase + 6 * X.n + x), mem (X.dBase + 7 * X.n + x))))
    (hRF : RF.F = forestGivenRoots T₀ (vList.getD 0 0) R π) (hRR : RF.R = R)
    (hvlen : vList.length = X.n) (hvL : ListAt mem X.vListPtr vList)
    (hfid : ∀ i < X.tM, mem (X.fid + i) = fid i)
    (htl : ∀ i < X.tM, vList.getD (mem (X.tTail + i)) 0 = vList.getD (tl i) 0)
    (hhd : ∀ i < X.tM, vList.getD (mem (X.tHead + i)) 0 = vList.getD (hd i) 0)
    (hinR : ∀ x < X.n, mem (X.inR + x) = inR x)
    (hown : ∀ i < X.tM, mem (X.own + i) = own i)
    (hrt : ∀ x < X.n, mem (X.rt + x) = rt x)
    (hpar : ∀ x < X.n, mem (X.auxPar + x) = par x)
    (hpe : ∀ x < X.n, mem (X.auxPar + X.n + x) = pe x) :
    DynGraphAt mem₃ X.dgF X.vCap X.eCap (forestGivenRoots T₀ (vList.getD 0 0) R π) ∧
    FAncAt mem₃ X.fAnc X.vCap RF (rootList (fun x => vList.getD x 0) inR vList.length)
      (fun v => vList.getD (rt (vList.idxOf v)) 0) (fun c => c)
      (sizeVal (fun x => vList.getD x 0) rt vList.length) RF.R ∧
    WBlockAt mem₃ X.wPtr X.n (refineDecomp W_T (forestGivenRoots T₀ (vList.getD 0 0) R π))
      (forestGivenRoots T₀ (vList.getD 0 0) R π) := by
  obtain ⟨v₁, m₁, v₂, m₂, v₃, p₁, p₂, p₃⟩ := fPhase_post hpost
  have l1 := I.l1; have l2 := I.l2; have l3 := I.l3; have l4 := I.l4; have l5 := I.l5
  have l6 := I.l6; have l7 := I.l7; have l8 := I.l8; have l9 := I.l9; have l10 := I.l10
  have l11 := I.l11; have l12 := I.l12
  -- the posts
  obtain ⟨_, _, _, _, _, _, _, _, _, _, heq₁, -, hdg, hfr₁⟩ := p₁
  simp only [List.cons.injEq, and_true] at heq₁
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₁
  obtain ⟨_, _, _, _, _, _, heq₂, -, hfr₂, a0, a1, a2, a3, a4, a5, aIs, aRL, aCI, aCR, aCS⟩ := p₂
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₂
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, cnt, K, s, heq₃, -, hcn, hfr₃, hSnd, hSmem,
    hKok, b0, b1, b2, b3, b4, b5, b6, bVO, bEO, bVS, bES⟩ := p₃
  simp only [List.cons.injEq, and_true] at heq₃
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₃
  -- what the later calls read is still the start memory
  have hm1 : ∀ a, X.wPtr + wBlockSize X.n ≤ a → m₁ a = mem a := fun a ha =>
    hfr₁ a (Or.inr (by omega))
  have hm2 : ∀ a, (a < X.dgF ∨ X.wPtr + wBlockSize X.n ≤ a) → m₂ a = mem a := fun a ha => by
    rw [hfr₂ a (by omega)]
    exact hfr₁ a (by omega)
  have hvx : ∀ x < X.n, mem (X.vListPtr + x) = vList.getD x 0 := fun x hx => by
    rw [hvL x (by omega), List.getD_eq_getElem _ _ (by omega)]
  have hrtn : ∀ x < X.n, rt x < X.n := fun x hx => by rw [← hrt x hx]; exact I.hrt x hx
  -- 1. the graph block
  have hF₁ : DynGraphAt m₁ X.dgF X.vCap X.eCap (forestGivenRoots T₀ (vList.getD 0 0) R π) := by
    refine fGraph_bridge hI hR ?_ (fun i hi => ⟨hfid i hi, by rw [← hfid i hi]; exact
      (I.hT i hi).2.2⟩) (fun i hi => ⟨?_, ?_⟩) hown hdg
    · have hs : memSlice mem X.vListPtr X.n = vList := by
        refine List.ext_getElem (by rw [memSlice_length, hvlen]) fun i h1 h2 => ?_
        rw [memSlice_getElem]; exact hvL i h2
      rw [hs]
      ext u
      rw [List.mem_toFinset, hI.hV]
    · show mem (X.vListPtr + mem (X.tTail + i)) = _
      rw [hvx _ (I.hT i hi).1]; exact htl i hi
    · show mem (X.vListPtr + mem (X.tHead + i)) = _
      rw [hvx _ (I.hT i hi).2.1]; exact hhd i hi
  -- 2. the root and component block
  have evL : ∀ x < X.n, vList.getD x 0 = m₁ (X.vListPtr + x) := fun x hx => by
    rw [hm1 _ (by omega), hvx x hx]
  have einR : ∀ x < X.n, inR x = m₁ (X.inR + x) := fun x hx => by
    rw [hm1 _ (by omega), hinR x hx]
  have ert : ∀ x < X.n, rt x = m₁ (X.rt + x) := fun x hx => by
    rw [hm1 _ (by omega), hrt x hx]
  have hA₂ := fAnc_bridge (vL := fun x => vList.getD x 0) (inR' := inR) (rt' := rt)
    (mem' := m₂) hI hR hRF hRR
    (fun x hx => ⟨rfl, by rw [hvlen] at hx; rw [← hvx x hx]; exact I.hvL x hx⟩)
    (fun _ _ => rfl) (fun _ _ => rfl) (by rw [hvlen]; exact I.hnv)
    (by rw [hvlen, rootList_congr evL einR]; exact a0) a1 a2 a3 a4 a5
    (fun v hv => by rw [hvlen, isRootVal_congr evL einR]; exact aIs v hv)
    (by rw [hvlen, rootList_congr evL einR]; exact aRL)
    (fun x hx => by
      rw [hvlen] at hx
      rw [evL _ (hrtn x hx), ert x hx, evL x hx]; exact aCI x hx)
    (fun x hx hx1 => by
      rw [hvlen] at hx
      rw [evL x hx]; exact aCR x hx (by show m₁ (X.inR + x) = 1; rw [← einR x hx]; exact hx1))
    (fun v hv => by
      rw [hvlen, sizeVal_congr (vL' := fun x => m₁ (X.vListPtr + x))
        (rt' := fun x => m₁ (X.rt + x)) (fun x hx => by
          show _ = m₁ (X.vListPtr + m₁ (X.rt + x))
          rw [← ert x hx, evL _ (hrtn x hx)])]
      exact aCS v hv)
  -- 3. the decomposition block
  have epe : ∀ y < X.n, y ≠ 0 → m₂ (X.auxPar + X.n + y) = pe y ∧ pe y < X.tM :=
    fun y hy hy0 => ⟨by rw [hm2 _ (Or.inr (by omega)), hpe y hy],
      (hI.hR.step y (by omega) hy0).1⟩
  have eown : ∀ i < X.tM, m₂ (X.own + i) = own i := fun i hi => by
    rw [hm2 _ (Or.inr (by omega)), hown i hi]
  have hSmem' : ∀ y, y ∈ (List.range cnt).map s ↔ y < vList.length ∧ y ≠ 0 ∧ own (pe y) = 0 :=
    fun y => by
      rw [hSmem, hvlen]
      constructor
      · rintro ⟨a, b, c⟩
        obtain ⟨e1, e2⟩ := epe y a b
        rw [e1, eown _ e2] at c
        exact ⟨a, b, c⟩
      · rintro ⟨a, b, c⟩
        obtain ⟨e1, e2⟩ := epe y a b
        refine ⟨a, b, ?_⟩
        rw [e1, eown _ e2]; exact c
  have hs : ∀ j < cnt, s j < X.n ∧ s j ≠ 0 := fun j hj => by
    have := (hSmem' (s j)).mp (List.mem_map_of_mem (List.mem_range.mpr hj))
    exact ⟨hvlen ▸ this.1, this.2.1⟩
  have hKok' : WKeyOK K s (fun y => m₂ (X.dBase + 6 * X.n + y))
      (fun y => m₂ (X.dBase + 7 * X.n + y)) rt cnt :=
    hKok.congr_rt fun j hj => by
      show rt (s j) = m₂ (X.rt + s j)
      rw [hm2 _ (Or.inr (by omega)), hrt _ (hs j hj).1]
  have hGeq : wGroups K s (fun y => m₂ (X.auxPar + y)) cnt = wGroups K s par cnt :=
    wGroups_congr_pa cnt fun j hj => by
      show m₂ (X.auxPar + s j) = par (s j)
      rw [hm2 _ (Or.inr (by omega)), hpar _ (hs j hj).1]
  rw [hGeq] at b0 b5 bVO bEO bVS
  have hW' : WLabels T₀ vList 0 W_T
      (fun y => (m₂ (X.dBase + 6 * X.n + y), m₂ (X.dBase + 7 * X.n + y))) :=
    hW.congr fun x hx => by
      rw [hvlen] at hx
      show (m₂ _, m₂ _) = (mem _, mem _)
      rw [hm2 _ (Or.inr (by omega)), hm2 _ (Or.inr (by omega))]
  have hfl := flatV_wGroups_lt hKok.1 (fun j hj => (hs j hj).1)
    (fun x hx => hvlen ▸ hI.hR.par_lt x (by omega))
  have hmap : (flatV (wGroups K s par cnt)).map (fun y => m₂ (X.vListPtr + y)) =
      (flatV (wGroups K s par cnt)).map (fun y => vList.getD y 0) :=
    List.map_congr_left fun y hy => by
      have := hfl y hy
      rw [hm2 _ (Or.inr (by omega)), hvx y this]
  rw [hmap] at bVS
  have hWB := wBlock_bridge hI hR hW' (fun y => rfl) hSnd hSmem' hKok' hcn b0 b1 b2 b3 b4 b5 b6
    bVO bEO bVS (fun j hj => by
      obtain ⟨e1, e2⟩ := epe _ (hs j hj).1 (hs j hj).2
      rw [bES j hj, e1, hm2 _ (Or.inl (by omega)), hfid _ e2])
  refine ⟨hF₁.of_agree fun a h1 h2 => ?_, hA₂.of_agree fun a h1 h2 => ?_, hWB⟩
  · rw [hfr₃ a (Or.inl (by omega)) (Or.inl (by omega)), hfr₂ a (Or.inl (by omega))]
  · exact hfr₃ a (Or.inl (by omega)) (Or.inl (by omega))

end

end MinCostFlow.LSF.Program
