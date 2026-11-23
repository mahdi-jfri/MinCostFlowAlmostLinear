module

public import MinCostFlow.LSF.Program.BatchMath
import Mathlib.Tactic.Linarith

/-!
# Binary-Lifting Minimum-Edge Query (`BatchMinUp`)

Implements `minEdgeUpProc`: given `AuxAt` and `TBlockAt` for `(T₀, r₀, π)` and two distinct vertex
indices `uIdx, wIdx < n₀` where one of `vList[uIdx], vList[wIdx]` is an ancestor of the other in
`(T₀, r₀)`, returns `minEdgeOn S.π (walkEdges (S.T₀.forestPath vList[uIdx] vList[wIdx]))` in
`O(auxLogCap n₀)` time without modifying memory (`minEdgeUp_meetsContract`).
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## Pure tree-climbing helpers from `AuxAt` -/

/-- If `y` lies on the tree path from `x` to `z`, then `walkEdges (T.forestPath x z)` is the union
of `walkEdges (T.forestPath x y)` and `walkEdges (T.forestPath y z)`. -/
lemma walkEdges_forestPath_split {T : MGraph} (hT : T.IsForest) {x y z : ℕ}
    (hxz : T.Connected x z) (hy : y ∈ T.walkVertices x (T.forestPath x z)) :
    walkEdges (T.forestPath x z) =
      walkEdges (T.forestPath x y) ∪ walkEdges (T.forestPath y z) := by
  rw [(forestPath_mem_walkVertices_split hT hxz hy).1, walkEdges_append]

/-- From `AuxAt`, iterating `t0Parent` walks strictly upward along `T₀.forestPath (vList[i]) r₀`,
so `t0Depth i` equals `(T₀.forestPath (vList[i]) r₀).length`, the vertices of that path are
exactly `{vList[t0Parent^[k] i] | k ≤ t0Depth i}`, and each `t0Parent^[k] i` has depth
`t0Depth i - k`. -/
lemma auxAt_t0Parent_path {T₀ : MGraph} {r₀ n0 r0Idx : ℕ} {vList : List ℕ}
    {t0Parent t0Depth : ℕ → ℕ}
    (hT₀ : IsRootedTree T₀ r₀) (hvLen : vList.length = n0) (hvNd : vList.Nodup)
    (hvMem : ∀ v, v ∈ vList ↔ v ∈ T₀.V)
    (hr0_lt : r0Idx < n0) (hr0_v : vList[r0Idx]? = some r₀)
    (hpar_lt : ∀ i < n0, t0Parent i < n0)
    (hdep0 : t0Depth r0Idx = 0)
    (hstep : ∀ i (hi : i < vList.length), i ≠ r0Idx →
      t0Depth i = t0Depth (t0Parent i) + 1 ∧
      ∃ f ∈ T₀.E, (T₀.tail f = vList[i] ∧ T₀.head f = vList[t0Parent i]!) ∨
        (T₀.tail f = vList[t0Parent i]! ∧ T₀.head f = vList[i])) :
    ∀ d, ∀ i (hi : i < n0), t0Depth i = d →
      (T₀.forestPath (vList[i]'(by omega)) r₀).length = d ∧
      (∀ k ≤ d,
        ∃ (ha : t0Parent^[k] i < n0), t0Depth (t0Parent^[k] i) = d - k ∧
        vList[t0Parent^[k] i]'(by omega) ∈ T₀.walkVertices (vList[i]'(by omega))
          (T₀.forestPath (vList[i]'(by omega)) r₀)) ∧
      (∀ w ∈ T₀.walkVertices (vList[i]'(by omega)) (T₀.forestPath (vList[i]'(by omega)) r₀),
        ∃ k ≤ d, ∃ (ha : t0Parent^[k] i < n0), w = vList[t0Parent^[k] i]'(by omega)) := by
  intro d
  induction d with
  | zero =>
    intro i hi hd
    have hir : i = r0Idx := by
      by_contra hne
      have := (hstep i (by omega) hne).1
      omega
    subst hir
    have hv_eq : vList[i]'(by omega) = r₀ := by
      have h1 : vList[i]? = some (vList[i]'(by omega)) := List.getElem?_eq_getElem (by omega)
      rw [hr0_v] at h1; exact Option.some.inj h1.symm
    have hfp : T₀.forestPath (vList[i]'(by omega)) r₀ = [] := by
      rw [hv_eq, forestPath_self hT₀.isForest]
    refine ⟨by rw [hfp]; rfl, fun k hk => ?_, fun w hw => ?_⟩
    · have hk0 : k = 0 := by omega
      subst hk0
      exact ⟨hi, by simp [hd], by rw [hfp]; simp [MGraph.walkVertices]⟩
    · rw [hfp] at hw; simp only [MGraph.walkVertices, List.map_nil, List.mem_singleton] at hw
      exact ⟨0, le_rfl, hi, hw⟩
  | succ d ih =>
    intro i hi hd
    have hir : i ≠ r0Idx := fun h => by rw [h, hdep0] at hd; omega
    obtain ⟨hdep_eq, f, hfE, hfh⟩ := hstep i (by omega) hir
    have hp_lt : t0Parent i < n0 := hpar_lt i hi
    have hvp_eq : vList[t0Parent i]! = vList[t0Parent i]'(by omega) :=
      getElem!_pos vList (t0Parent i) (by omega)
    rw [hvp_eq] at hfh
    obtain ⟨hlen_p, hanc_p, hverts_p⟩ := ih (t0Parent i) hp_lt (by omega)
    have hvi_V : vList[i]'(by omega) ∈ T₀.V := (hvMem _).mp (List.getElem_mem _)
    have hvp_V : vList[t0Parent i]'(by omega) ∈ T₀.V := (hvMem _).mp (List.getElem_mem _)
    have hP_p := forestPath_isPath hT₀.isForest (hT₀.connected hvp_V hT₀.2)
    have hnot_on : vList[i]'(by omega) ∉
        T₀.walkVertices (vList[t0Parent i]'(by omega))
          (T₀.forestPath (vList[t0Parent i]'(by omega)) r₀) := by
      intro hmem
      obtain ⟨k, hk, ha, hwk⟩ := hverts_p _ hmem
      have hidx_eq : i = t0Parent^[k] (t0Parent i) := (hvNd.getElem_inj_iff).mp hwk
      obtain ⟨_, hdep_k, _⟩ := hanc_p k hk
      rw [← hidx_eq, hd] at hdep_k
      omega
    have hex_step : ∃ dir : Bool, T₀.src (f, dir) = vList[i]'(by omega) ∧
        T₀.dst (f, dir) = vList[t0Parent i]'(by omega) := by
      rcases hfh with ⟨ht, hh⟩ | ⟨ht, hh⟩
      · exact ⟨true, by simp [MGraph.src, ht], by simp [MGraph.dst, hh]⟩
      · exact ⟨false, by simp [MGraph.src, hh], by simp [MGraph.dst, ht]⟩
    obtain ⟨dir, hsrc, hdst⟩ := hex_step
    let Q := (f, dir) :: T₀.forestPath (vList[t0Parent i]'(by omega)) r₀
    have hQ_walk : T₀.IsWalk (vList[i]'(by omega)) r₀ Q :=
      .cons hfE hsrc (hdst.symm ▸ hP_p.1)
    have hQ_wv : T₀.walkVertices (vList[i]'(by omega)) Q =
        vList[i]'(by omega) :: T₀.walkVertices (vList[t0Parent i]'(by omega))
          (T₀.forestPath (vList[t0Parent i]'(by omega)) r₀) := by
      simp [Q, MGraph.walkVertices, hdst]
    have hQ_path : T₀.IsPath (vList[i]'(by omega)) r₀ Q :=
      ⟨hQ_walk, by rw [hQ_wv]; exact List.nodup_cons.mpr ⟨hnot_on, hP_p.2⟩⟩
    have hfp_eq : T₀.forestPath (vList[i]'(by omega)) r₀ = Q :=
      forestPath_eq_of_isPath hT₀.isForest hQ_path
    refine ⟨by rw [hfp_eq]; simp [Q, hlen_p], fun k hk => ?_, fun w hw => ?_⟩
    · cases k with
      | zero =>
        exact ⟨hi, by simp [hd], by rw [hfp_eq, hQ_wv]; exact List.mem_cons_self⟩
      | succ k' =>
        have hk' : k' ≤ d := by omega
        obtain ⟨ha1, ha2, ha3⟩ := hanc_p k' hk'
        have hit : t0Parent^[k' + 1] i = t0Parent^[k'] (t0Parent i) := Function.iterate_succ_apply _ _ _
        refine ⟨by rw [hit]; exact ha1, by rw [hit, ha2]; omega, ?_⟩
        rw [hfp_eq, hQ_wv]
        refine List.mem_cons_of_mem _ ?_
        simpa only [hit] using ha3
    · rw [hfp_eq, hQ_wv, List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact ⟨0, Nat.zero_le _, hi, rfl⟩
      · obtain ⟨k', hk', ha, hwk⟩ := hverts_p w hw
        have hit : t0Parent^[k' + 1] i = t0Parent^[k'] (t0Parent i) := Function.iterate_succ_apply _ _ _
        exact ⟨k' + 1, by omega, by rw [hit]; exact ha, by simpa only [hit] using hwk⟩

/-- `upV i j = t0Parent^[2^j] i` for all `i < n0` and `j < logCap`. -/
lemma upV_eq_iterate {n0 logCap : ℕ} {t0Parent : ℕ → ℕ} {upV : ℕ → ℕ → ℕ}
    (hup0 : ∀ i < n0, 0 < logCap → upV i 0 = t0Parent i)
    (hupS : ∀ i < n0, ∀ j, j + 1 < logCap → upV i (j + 1) = upV (upV i j) j)
    (hupLt : ∀ i < n0, ∀ j < logCap, upV i j < n0) :
    ∀ j < logCap, ∀ i < n0, upV i j = t0Parent^[2 ^ j] i := by
  intro j
  induction j with
  | zero =>
    intro hj i hi
    simpa using hup0 i hi hj
  | succ j ih =>
    intro hj i hi
    rw [hupS i hi j hj, ih (by omega) _ (hupLt i hi j (by omega)), ih (by omega) i hi,
      ← Function.iterate_add_apply, show 2 ^ j + 2 ^ j = 2 ^ (j + 1) by rw [pow_succ]; omega]

/-- If `vList[topIdx]` is an ancestor of `vList[botIdx]` in `(T₀, r₀)`, then
`t0Depth topIdx ≤ t0Depth botIdx` and `t0Parent^[t0Depth botIdx - t0Depth topIdx] botIdx = topIdx`. -/
lemma ancestor_depth_iterate {T₀ : MGraph} {r₀ n0 r0Idx : ℕ} {vList : List ℕ}
    {t0Parent t0Depth : ℕ → ℕ}
    (hT₀ : IsRootedTree T₀ r₀) (hvLen : vList.length = n0) (hvNd : vList.Nodup)
    (hvMem : ∀ v, v ∈ vList ↔ v ∈ T₀.V)
    (hr0_lt : r0Idx < n0) (hr0_v : vList[r0Idx]? = some r₀)
    (hpar_lt : ∀ i < n0, t0Parent i < n0)
    (hdep0 : t0Depth r0Idx = 0)
    (hstep : ∀ i (hi : i < vList.length), i ≠ r0Idx →
      t0Depth i = t0Depth (t0Parent i) + 1 ∧
      ∃ f ∈ T₀.E, (T₀.tail f = vList[i] ∧ T₀.head f = vList[t0Parent i]!) ∨
        (T₀.tail f = vList[t0Parent i]! ∧ T₀.head f = vList[i]))
    {botIdx topIdx : ℕ} (hbot : botIdx < n0) (htop : topIdx < n0)
    (hanc : IsAncestor T₀ r₀ (vList[topIdx]'(by omega)) (vList[botIdx]'(by omega))) :
    t0Depth topIdx ≤ t0Depth botIdx ∧
      t0Parent^[t0Depth botIdx - t0Depth topIdx] botIdx = topIdx := by
  have hpath := auxAt_t0Parent_path hT₀ hvLen hvNd hvMem hr0_lt hr0_v hpar_lt hdep0 hstep
    (t0Depth botIdx) botIdx hbot rfl
  obtain ⟨k, hk, ha, hwk⟩ := hpath.2.2 _ hanc
  have hidx_eq : topIdx = t0Parent^[k] botIdx := (hvNd.getElem_inj_iff).mp hwk
  obtain ⟨_, hdep_k, _⟩ := hpath.2.1 k hk
  rw [← hidx_eq] at hdep_k
  refine ⟨by omega, ?_⟩
  rw [show t0Depth botIdx - t0Depth topIdx = k by omega, ← hidx_eq]

/-- `t0Depth i < n0` for all `i < n0` under `AuxAt`. -/
lemma auxAt_t0Depth_lt {T₀ : MGraph} {r₀ n0 r0Idx : ℕ} {vList : List ℕ}
    {t0Parent t0Depth : ℕ → ℕ}
    (hT₀ : IsRootedTree T₀ r₀) (hvLen : vList.length = n0) (hvNd : vList.Nodup)
    (hvMem : ∀ v, v ∈ vList ↔ v ∈ T₀.V)
    (hr0_lt : r0Idx < n0) (hr0_v : vList[r0Idx]? = some r₀)
    (hpar_lt : ∀ i < n0, t0Parent i < n0)
    (hdep0 : t0Depth r0Idx = 0)
    (hstep : ∀ i (hi : i < vList.length), i ≠ r0Idx →
      t0Depth i = t0Depth (t0Parent i) + 1 ∧
      ∃ f ∈ T₀.E, (T₀.tail f = vList[i] ∧ T₀.head f = vList[t0Parent i]!) ∨
        (T₀.tail f = vList[t0Parent i]! ∧ T₀.head f = vList[i]))
    {i : ℕ} (hi : i < n0) :
    t0Depth i < n0 := by
  have hpath := auxAt_t0Parent_path hT₀ hvLen hvNd hvMem hr0_lt hr0_v hpar_lt hdep0 hstep
    (t0Depth i) i hi rfl
  have hviV : vList[i]'(by omega) ∈ T₀.V := (hvMem _).mp (List.getElem_mem _)
  have hP := forestPath_isPath hT₀.isForest (hT₀.connected hviV hT₀.2)
  have hlen_wv : (T₀.walkVertices (vList[i]'(by omega))
      (T₀.forestPath (vList[i]'(by omega)) r₀)).length = t0Depth i + 1 := by
    simp [MGraph.walkVertices, hpath.1]
  have hsub : (T₀.walkVertices (vList[i]'(by omega))
      (T₀.forestPath (vList[i]'(by omega)) r₀)).toFinset ⊆ T₀.V := by
    intro x hx
    obtain ⟨k, hk, ha, rfl⟩ := hpath.2.2 x (List.mem_toFinset.mp hx)
    exact (hvMem _).mp (List.getElem_mem (by omega))
  have hcard1 : (T₀.walkVertices (vList[i]'(by omega))
      (T₀.forestPath (vList[i]'(by omega)) r₀)).toFinset.card = t0Depth i + 1 := by
    rw [List.toFinset_card_of_nodup hP.2, hlen_wv]
  have hcard2 : T₀.V.card = n0 := by
    have hto : vList.toFinset = T₀.V := by ext v; simp [hvMem]
    rw [← hto, List.toFinset_card_of_nodup hvNd, hvLen]
  have := Finset.card_le_card hsub
  omega

/-- Unique minimum-`π` characterization of `minEdgeOn`: if `e ∈ E` and `∀ f ∈ E, π e ≤ π f` under
an injective `IsEdgeOrder T π` with `E ⊆ T.E`, then `e = minEdgeOn π E`. -/
lemma eq_minEdgeOn_of_le {T : MGraph} {π : ℕ → ℕ} {E : Finset ℕ} {e : ℕ}
    (hord : IsEdgeOrder T π) (hET : E ⊆ T.E) (he : e ∈ E) (hle : ∀ f ∈ E, π e ≤ π f) :
    e = minEdgeOn π E := by
  have hne : E.Nonempty := ⟨e, he⟩
  have hm_mem : minEdgeOn π E ∈ E := minEdgeOn_mem hne
  have hm_le : π (minEdgeOn π E) ≤ π e := minEdgeOn_le he
  have he_le : π e ≤ π (minEdgeOn π E) := hle _ hm_mem
  exact hord e (hET he) (minEdgeOn π E) (hET hm_mem) (Nat.le_antisymm he_le hm_le)

/-! ## Word-RAM procedure `minEdgeUpProc` -/

/-- Loop body of `minEdgeUpProc` at bit `r19 = j` (registers: `r8 = logCap`, `r9 = upVBase`,
`r10 = upMinBase`, `r11 = piBase`, `r15 = cur`, `r16 = rem`, `r17 = hasBest`, `r18 = bestIdx`). -/
def minEdgeUpStepStmt : Stmt :=
  .cond (.bin .mod (.reg 16) (.const 2))
    (.assign 20 (.load (.bin .add (.reg 10) (.bin .add (.bin .mul (.reg 15) (.reg 8)) (.reg 19)))) ;;
     .cond (.reg 17)
       (.cond (.bin .lt (.load (.bin .add (.reg 11) (.reg 20))) (.load (.bin .add (.reg 11) (.reg 18))))
         (.assign 18 (.reg 20))
         .nop)
       (.assign 18 (.reg 20) ;; .assign 17 (.const 1)) ;;
     .assign 15 (.load (.bin .add (.reg 9) (.bin .add (.bin .mul (.reg 15) (.reg 8)) (.reg 19)))))
    .nop ;;
  .assign 16 (.bin .div (.reg 16) (.const 2))

/-- Binary-lifting minimum-`π` edge query on a vertical path in `T₀`:
`args = [auxPtr, tPtr, vCap, n0, tM, uIdx, wIdx]`. Returns `tOrigId[bestIdx]`. -/
def minEdgeUpProc : Stmt :=
  .assign 7 (.load (.bin .add (.reg 0) (.const auxOffT0DepthPtr))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const auxOffLogCap))) ;;
  .assign 9 (.load (.bin .add (.reg 0) (.const auxOffUpVPtr))) ;;
  .assign 10 (.load (.bin .add (.reg 0) (.const auxOffUpMinIdxPtr))) ;;
  .assign 11 (.load (.bin .add (.reg 1) (.const tOffPiPtr))) ;;
  .assign 12 (.load (.bin .add (.reg 1) (.const tOffOrigIdPtr))) ;;
  .assign 13 (.load (.bin .add (.reg 7) (.reg 5))) ;;
  .assign 14 (.load (.bin .add (.reg 7) (.reg 6))) ;;
  .cond (.bin .lt (.reg 14) (.reg 13))
    (.assign 15 (.reg 5) ;; .assign 16 (.bin .sub (.reg 13) (.reg 14)))
    (.assign 15 (.reg 6) ;; .assign 16 (.bin .sub (.reg 14) (.reg 13))) ;;
  .assign 17 (.const 0) ;;
  .assign 18 (.const 0) ;;
  forRange 19 (.const 0) (.reg 8) minEdgeUpStepStmt ;;
  .ret (.load (.bin .add (.reg 12) (.reg 18)))

lemma minEdgeUpProc_noRand : minEdgeUpProc.NoRand := by
  simp [minEdgeUpProc, minEdgeUpStepStmt, forRange, forUp, Stmt.NoRand]

/-- Contract for `minEdgeUpProc`: `[auxPtr, tPtr, vCap, n0, tM, uIdx, wIdx]`. -/
def minEdgeUpContract (w : ℕ) (S : LSFState) (vList tOrigList : List ℕ) : Contract where
  pre args mem := ∃ auxPtr tPtr vCap eCap n0 tM uIdx wIdx
      t0Parent t0ParentTreeIdx t0Depth thParent upV upMinIdx,
    args = [auxPtr, tPtr, vCap, n0, tM, uIdx, wIdx] ∧
    16 ≤ 2 ^ w ∧
    auxPtr + auxSize vCap n0 < 2 ^ w ∧
    tPtr + tBlockSize vCap eCap tM < 2 ^ w ∧
    LSFStructInv S ∧
    1 ≤ tM ∧
    AuxAt mem auxPtr vCap n0 tM S tOrigList vList
      t0Parent t0ParentTreeIdx t0Depth thParent upV upMinIdx ∧
    TBlockAt mem tPtr vCap eCap tM S.G S.T_cur S.T₀ S.π tOrigList ∧
    uIdx < n0 ∧ wIdx < n0 ∧ uIdx ≠ wIdx ∧
    (IsAncestor S.T₀ S.r₀ (vList[wIdx]!) (vList[uIdx]!) ∨
      IsAncestor S.T₀ S.r₀ (vList[uIdx]!) (vList[wIdx]!))
  post args mem ret mem' := ∃ auxPtr tPtr vCap n0 tM uIdx wIdx,
    args = [auxPtr, tPtr, vCap, n0, tM, uIdx, wIdx] ∧
    mem' = mem ∧
    ret = minEdgeOn S.π (walkEdges (S.T₀.forestPath (vList[uIdx]!) (vList[wIdx]!)))
  cost args _ := 120 * auxLogCap (args.getD 3 0) + 120

/-! ## Verification -/

private lemma minEdgeUpStep_triple {w n0 tM logCap upVBase upMinBase piBase origIdBase
    botIdx topIdx diff : ℕ} {p : Program} {mem : ℕ → ℕ} {T₀ : MGraph} {r₀ : ℕ} {π : ℕ → ℕ}
    {vList tOrigList : List ℕ} {t0Parent t0Depth : ℕ → ℕ} {upV upMinIdx : ℕ → ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w) (hT₀ : IsRootedTree T₀ r₀)
    (hvLen : vList.length = n0) (hvNd : vList.Nodup) (hvMem : ∀ v, v ∈ vList ↔ v ∈ T₀.V)
    (_htLen : tOrigList.length = tM)
    (hupV_ltw : upVBase + n0 * logCap < 2 ^ w)
    (hupMin_ltw : upMinBase + n0 * logCap < 2 ^ w)
    (hpi_ltw : piBase + tM < 2 ^ w)
    (hdiff_ltw : diff < 2 ^ w)
    (hbot_lt : botIdx < n0) (_htop_lt : topIdx < n0)
    (hdiff_eq : diff = t0Depth botIdx - t0Depth topIdx)
    (hdep_le : t0Depth topIdx ≤ t0Depth botIdx)
    (hall_path : ∀ i (hi : i < n0),
      (∀ k ≤ t0Depth i,
        ∃ (ha : t0Parent^[k] i < n0), t0Depth (t0Parent^[k] i) = t0Depth i - k ∧
        vList[t0Parent^[k] i]'(by omega) ∈ T₀.walkVertices (vList[i]'(by omega))
          (T₀.forestPath (vList[i]'(by omega)) r₀)) ∧
      (∀ w ∈ T₀.walkVertices (vList[i]'(by omega)) (T₀.forestPath (vList[i]'(by omega)) r₀),
        ∃ k ≤ t0Depth i, ∃ (ha : t0Parent^[k] i < n0), w = vList[t0Parent^[k] i]'(by omega)))
    (hupV_mem : ∀ i < n0, ∀ j < logCap, mem (upVBase + (i * logCap + j)) = upV i j ∧ upV i j < n0)
    (hupMin_mem : ∀ i < n0, ∀ j < logCap,
      mem (upMinBase + (i * logCap + j)) = upMinIdx i j ∧ upMinIdx i j < tM)
    (hpi_mem : ∀ i < tM, mem (piBase + i) = π (tOrigList[i]!))
    (hupV_it : ∀ i < n0, ∀ j < logCap, upV i j = t0Parent^[2 ^ j] i)
    (hupMin_spec : ∀ i < n0, ∀ j < logCap,
      let u := vList[i]!
      let v := vList[upV i j]!
      u ≠ v → upMinIdx i j < tM ∧ tOrigList[upMinIdx i j]! ∈ walkEdges (T₀.forestPath u v) ∧
        ∀ e ∈ walkEdges (T₀.forestPath u v), π (tOrigList[upMinIdx i j]!) ≤ π e)
    (j : ℕ) (hj : j < logCap) :
    let Inv : ℕ → State → Prop := fun k st =>
      st.mem = mem ∧ st.regs 8 = logCap ∧ st.regs 9 = upVBase ∧ st.regs 10 = upMinBase ∧
      st.regs 11 = piBase ∧ st.regs 12 = origIdBase ∧
      st.regs 15 = t0Parent^[diff % 2 ^ k] botIdx ∧
      st.regs 16 = diff / 2 ^ k ∧
      st.regs 19 = k ∧
      (diff % 2 ^ k = 0 → st.regs 17 = 0) ∧
      (0 < diff % 2 ^ k →
        st.regs 17 = 1 ∧ st.regs 18 < tM ∧
        tOrigList[st.regs 18]! ∈ walkEdges (T₀.forestPath (vList[botIdx]!) (vList[st.regs 15]!)) ∧
        ∀ e ∈ walkEdges (T₀.forestPath (vList[botIdx]!) (vList[st.regs 15]!)),
          π (tOrigList[st.regs 18]!) ≤ π e)
    Triple w p (Inv j) minEdgeUpStepStmt
      (normalPost fun st =>
        Inv (j + 1) { st with regs := Function.update st.regs 19 (j + 1) } ∧ st.regs 19 = j)
      (fun _ => 110) := by
  have hpath := (hall_path botIdx hbot_lt).1
  intro Inv st ω ⟨hmem, hr8, hr9, hr10, hr11, hr12, hr15, hr16, hr19, hzero, hpos⟩
  rcases st with ⟨stm, str, stp⟩
  dsimp only at hmem hr8 hr9 hr10 hr11 hr12 hr15 hr16 hr19 hzero hpos
  subst stm
  set climbed := diff % 2 ^ j with hcl_def
  set rem := diff / 2 ^ j with hrem_def
  have hcl_le : climbed ≤ diff := Nat.mod_le _ _
  have hcl_dep : climbed ≤ t0Depth botIdx := by omega
  obtain ⟨hcur_lt, hcur_dep, hcur_on⟩ := hpath climbed hcl_dep
  have hrem_ltw : rem < 2 ^ w := lt_of_le_of_lt (Nat.div_le_self _ _) hdiff_ltw
  have hmod_eq : diff % 2 ^ (j + 1) = climbed + 2 ^ j * (rem % 2) := by
    have h1 : diff = 2 ^ j * rem + climbed := (Nat.div_add_mod diff (2 ^ j)).symm
    have h2 : rem = 2 * (rem / 2) + rem % 2 := (Nat.div_add_mod rem 2).symm
    have h3 : diff = (2 ^ j * 2) * (rem / 2) + (climbed + 2 ^ j * (rem % 2)) := by
      calc diff = 2 ^ j * (2 * (rem / 2) + rem % 2) + climbed := by rw [← h2]; exact h1
        _ = (2 ^ j * 2) * (rem / 2) + (climbed + 2 ^ j * (rem % 2)) := by ring
    have hlt : climbed + 2 ^ j * (rem % 2) < 2 ^ j * 2 := by
      have hc : climbed < 2 ^ j := Nat.mod_lt _ (Nat.two_pow_pos j)
      have hr : rem % 2 ≤ 1 := Nat.lt_succ_iff.mp (Nat.mod_lt _ (by decide))
      have hmul : 2 ^ j * (rem % 2) ≤ 2 ^ j * 1 := Nat.mul_le_mul_left _ hr
      omega
    rw [pow_succ, h3, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
  have hdiv_eq : diff / 2 ^ (j + 1) = rem / 2 := by
    rw [pow_succ, Nat.div_div_eq_div_mul]
  have hlt2 : 2 < 2 ^ w := by omega
  have hidx_lt : t0Parent^[climbed] botIdx * logCap + j < n0 * logCap := by
    calc t0Parent^[climbed] botIdx * logCap + j
        < t0Parent^[climbed] botIdx * logCap + logCap := Nat.add_lt_add_left hj _
      _ = (t0Parent^[climbed] botIdx + 1) * logCap := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ n0 * logCap := Nat.mul_le_mul_right _ hcur_lt
  have hmod_eval : (Expr.bin .mod (.reg 16) (.const 2)).eval w
      { mem := mem, regs := str, pos := stp } = some (rem % 2) := by
    have : rem % 2 < 2 ^ w := lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by omega)
    eval_expr
  suffices h : ∃ o st' c,
      Runs w p ω minEdgeUpStepStmt { mem := mem, regs := str, pos := stp } o st' c ∧
      normalPost (fun st =>
        Inv (j + 1) { st with regs := Function.update st.regs 19 (j + 1) } ∧ st.regs 19 = j) o st' ∧
      0 + c ≤ 110 by
    rcases h with ⟨o, st', c, hr, hq, hc⟩
    exact ⟨o, st', c, hr, hq, by simpa using hc⟩
  dsimp only [minEdgeUpStepStmt]
  refine runs_seq_cond_le hmod_eval ?_ ?_
  · -- Bit `j` is 1 (`rem % 2 ≠ 0`, so `rem % 2 = 1`)
    intro hbit
    have hbit1 : rem % 2 = 1 := by omega
    have hcl_next : diff % 2 ^ (j + 1) = climbed + 2 ^ j := by rw [hmod_eq, hbit1, mul_one]
    have hcl_next_le : climbed + 2 ^ j ≤ diff := by rw [← hcl_next]; exact Nat.mod_le _ _
    have hcl_next_dep : climbed + 2 ^ j ≤ t0Depth botIdx := by omega
    set cur := t0Parent^[climbed] botIdx
    set cand := upMinIdx cur j
    set nxt := upV cur j
    have hcand_eq : mem (upMinBase + (cur * logCap + j)) = cand := (hupMin_mem cur hcur_lt j hj).1
    have hcand_lt : cand < tM := (hupMin_mem cur hcur_lt j hj).2
    have hnxt_eq : mem (upVBase + (cur * logCap + j)) = nxt := (hupV_mem cur hcur_lt j hj).1
    have hnxt_lt : nxt < n0 := (hupV_mem cur hcur_lt j hj).2
    have hnxt_it : nxt = t0Parent^[climbed + 2 ^ j] botIdx := by
      dsimp only [nxt, cur]
      rw [hupV_it _ hcur_lt j hj, ← Function.iterate_add_apply, Nat.add_comm]
    have hnxt_dep : t0Depth nxt = t0Depth botIdx - (climbed + 2 ^ j) := by
      rw [hnxt_it]; exact (hpath (climbed + 2 ^ j) hcl_next_dep).choose_spec.1
    have hcur_ne_nxt : vList[cur]! ≠ vList[nxt]! := by
      rw [getElem!_pos vList cur (by omega), getElem!_pos vList nxt (by omega)]
      intro heq
      have hcn : cur = nxt := (hvNd.getElem_inj_iff).mp heq
      have h1 : t0Depth cur = t0Depth nxt := congrArg t0Depth hcn
      have h2j : 1 ≤ 2 ^ j := Nat.one_le_two_pow
      omega
    obtain ⟨_, hcand_mem, hcand_min⟩ := hupMin_spec cur hcur_lt j hj hcur_ne_nxt
    -- Path splitting: `T₀[bot, nxt] = T₀[bot, cur] ∪ T₀[cur, nxt]`
    have hpath_split : walkEdges (T₀.forestPath (vList[botIdx]!) (vList[nxt]!)) =
        walkEdges (T₀.forestPath (vList[botIdx]!) (vList[cur]!)) ∪
        walkEdges (T₀.forestPath (vList[cur]!) (vList[nxt]!)) := by
      rw [getElem!_pos vList botIdx (by omega), getElem!_pos vList cur (by omega),
        getElem!_pos vList nxt (by omega)]
      have hbotV : vList[botIdx]'(by omega) ∈ T₀.V := (hvMem _).mp (List.getElem_mem _)
      have hcurV : vList[cur]'(by omega) ∈ T₀.V := (hvMem _).mp (List.getElem_mem _)
      have hnxtV : vList[nxt]'(by omega) ∈ T₀.V := (hvMem _).mp (List.getElem_mem _)
      have hnxt_on_bot_r : vList[nxt]'(by omega) ∈
          T₀.walkVertices (vList[botIdx]'(by omega))
            (T₀.forestPath (vList[botIdx]'(by omega)) r₀) := by
        simpa only [hnxt_it] using (hpath (climbed + 2 ^ j) hcl_next_dep).choose_spec.2
      have hP_split := forestPath_mem_walkVertices_split hT₀.isForest (hT₀.connected hbotV hT₀.2)
        hnxt_on_bot_r
      have hcur_in_bn : vList[cur]'(by omega) ∈
          T₀.walkVertices (vList[botIdx]'(by omega))
            (T₀.forestPath (vList[botIdx]'(by omega)) (vList[nxt]'(by omega))) := by
        have hmem_cat := hcur_on
        rw [hP_split.1, walkVertices_append, List.mem_append] at hmem_cat
        rcases hmem_cat with h1 | h2
        · exact h1
        · have hcur_on_nr : vList[cur]'(by omega) ∈
              T₀.walkVertices (vList[nxt]'(by omega))
                (T₀.forestPath (vList[nxt]'(by omega)) r₀) := by
            rw [MGraph.walkVertices]; exact List.mem_cons_of_mem _ h2
          obtain ⟨k, hk, ha, hwk⟩ := (hall_path nxt hnxt_lt).2 _ hcur_on_nr
          have hidx_eq : cur = t0Parent^[k] nxt := (hvNd.getElem_inj_iff).mp hwk
          obtain ⟨_, hdep_k, _⟩ := (hall_path nxt hnxt_lt).1 k hk
          rw [← hidx_eq] at hdep_k
          have h2j : 1 ≤ 2 ^ j := Nat.one_le_two_pow
          omega
      exact walkEdges_forestPath_split hT₀.isForest (hT₀.connected hbotV hnxtV) hcur_in_bn
    -- Step 1: assign r20 := upMinIdx[cur, j]
    refine runs_seq_assoc_le (runs_seq_assign_le (Expr.eval_load_of_eq (v := cand) (by eval_expr) hcand_eq) ?_); dsimp only
    -- Step 2: branch on hasBest (r17)
    refine runs_seq_assoc_le (runs_seq_cond_le (v := str 17) (by eval_expr) ?_ ?_)
    · -- hasBest ≠ 0 (so `0 < climbed`!)
      intro h17_ne
      have hcl_pos : 0 < climbed := by
        by_contra h0
        have : climbed = 0 := by omega
        exact h17_ne (hzero this)
      obtain ⟨h17_1, h18_lt, h18_mem, h18_min⟩ := hpos hcl_pos
      have hpi_cand : mem (piBase + cand) = π (tOrigList[cand]!) := hpi_mem cand hcand_lt
      have hpi_best : mem (piBase + str 18) = π (tOrigList[str 18]!) := hpi_mem (str 18) h18_lt
      let st20 : State := { mem := mem, regs := Function.update str 20 cand, pos := stp }
      have hlt_eval : (Expr.bin .lt (.load (.bin .add (.reg 11) (.reg 20)))
          (.load (.bin .add (.reg 11) (.reg 18)))).eval w st20 =
          some (if π (tOrigList[cand]!) < π (tOrigList[str 18]!) then 1 else 0) := by
        have h1 : (Expr.load (.bin .add (.reg 11) (.reg 20))).eval w st20 =
            some (π (tOrigList[cand]!)) :=
          Expr.eval_load_of_eq (by dsimp only [st20]; eval_expr) hpi_cand
        have h2 : (Expr.load (.bin .add (.reg 11) (.reg 18))).eval w st20 =
            some (π (tOrigList[str 18]!)) :=
          Expr.eval_load_of_eq (by dsimp only [st20]; eval_expr) hpi_best
        exact Expr.eval_bin h1 h2 (by dsimp [BinOp.eval]; split_ifs <;> omega)
      refine runs_seq_cond_le hlt_eval ?_ ?_
      · intro hlt_ne
        have hlt_pi : π (tOrigList[cand]!) < π (tOrigList[str 18]!) := by
          by_contra hc; simp only [hc, ↓reduceIte] at hlt_ne; exact hlt_ne rfl
        refine runs_seq_assign_le (v := cand) (by eval_expr) ?_; dsimp only
        refine runs_seq_assign_le (Expr.eval_load_of_eq (v := nxt) (by eval_expr) hnxt_eq) ?_; dsimp only
        refine runs_assign_le (v := rem / 2) (by eval_expr) ?_ (by dsimp [Expr.size]; omega)
        refine ⟨⟨rfl, by simp [hr8], by simp [hr9], by simp [hr10], by simp [hr11], by simp [hr12],
          by simp [hcl_next, hnxt_it], by simp [hdiv_eq], by simp, fun h => by omega, fun _ => ?_⟩,
          by simp [hr19]⟩
        refine ⟨by simp [h17_1], by simp [hcand_lt], ?_, ?_⟩
        · simp only [Function.update_of_ne (by decide : (18 : ℕ) ≠ 19),
            Function.update_of_ne (by decide : (18 : ℕ) ≠ 16),
            Function.update_of_ne (by decide : (18 : ℕ) ≠ 15), Function.update_self,
            Function.update_of_ne (by decide : (15 : ℕ) ≠ 19),
            Function.update_of_ne (by decide : (15 : ℕ) ≠ 16)]
          rw [hpath_split]; exact Finset.mem_union_right _ hcand_mem
        · intro e he
          simp only [Function.update_of_ne (by decide : (18 : ℕ) ≠ 19),
            Function.update_of_ne (by decide : (18 : ℕ) ≠ 16),
            Function.update_of_ne (by decide : (18 : ℕ) ≠ 15), Function.update_self,
            Function.update_of_ne (by decide : (15 : ℕ) ≠ 19),
            Function.update_of_ne (by decide : (15 : ℕ) ≠ 16)] at he ⊢
          rw [hpath_split, Finset.mem_union] at he
          rcases he with h1 | h2
          · exact le_trans (le_of_lt hlt_pi) (h18_min e (by rwa [hr15]))
          · exact hcand_min e h2
      · intro hlt_eq0
        have hge_pi : π (tOrigList[str 18]!) ≤ π (tOrigList[cand]!) := by
          by_contra hc; push Not at hc; simp only [hc, ↓reduceIte] at hlt_eq0; exact Nat.one_ne_zero hlt_eq0
        refine runs_seq_nop_le ?_
        refine runs_seq_assign_le (Expr.eval_load_of_eq (v := nxt) (by eval_expr) hnxt_eq) ?_; dsimp only
        refine runs_assign_le (v := rem / 2) (by eval_expr) ?_ (by dsimp [Expr.size]; omega)
        refine ⟨⟨rfl, by simp [hr8], by simp [hr9], by simp [hr10], by simp [hr11], by simp [hr12],
          by simp [hcl_next, hnxt_it], by simp [hdiv_eq], by simp, fun h => by omega, fun _ => ?_⟩,
          by simp [hr19]⟩
        refine ⟨by simp [h17_1], by simp [h18_lt], ?_, ?_⟩
        · simp only [Function.update_of_ne (by decide : (18 : ℕ) ≠ 19),
            Function.update_of_ne (by decide : (18 : ℕ) ≠ 16),
            Function.update_of_ne (by decide : (18 : ℕ) ≠ 15),
            Function.update_of_ne (by decide : (18 : ℕ) ≠ 20),
            Function.update_of_ne (by decide : (15 : ℕ) ≠ 19),
            Function.update_of_ne (by decide : (15 : ℕ) ≠ 16), Function.update_self]
          rw [hpath_split]; exact Finset.mem_union_left _ (by rwa [hr15] at h18_mem)
        · intro e he
          simp only [Function.update_of_ne (by decide : (18 : ℕ) ≠ 19),
            Function.update_of_ne (by decide : (18 : ℕ) ≠ 16),
            Function.update_of_ne (by decide : (18 : ℕ) ≠ 15),
            Function.update_of_ne (by decide : (18 : ℕ) ≠ 20),
            Function.update_of_ne (by decide : (15 : ℕ) ≠ 19),
            Function.update_of_ne (by decide : (15 : ℕ) ≠ 16), Function.update_self] at he ⊢
          rw [hpath_split, Finset.mem_union] at he
          rcases he with h1 | h2
          · exact h18_min e (by rwa [hr15])
          · exact le_trans hge_pi (hcand_min e h2)
    · -- hasBest = 0 (so `climbed = 0`, `cur = botIdx`!)
      intro h17_eq0
      have hcl_0 : climbed = 0 := by
        by_contra hc
        have := (hpos (Nat.pos_of_ne_zero hc)).1
        omega
      have hcur_bot : cur = botIdx := by simp [cur, hcl_0]
      refine runs_seq_assoc_le (runs_seq_assign_le (v := cand) (by eval_expr) ?_); dsimp only
      refine runs_seq_assign_le (v := 1) (by eval_expr) ?_; dsimp only
      refine runs_seq_assign_le (Expr.eval_load_of_eq (v := nxt) (by eval_expr) hnxt_eq) ?_; dsimp only
      refine runs_assign_le (v := rem / 2) (by eval_expr) ?_ (by dsimp [Expr.size]; omega)
      refine ⟨⟨rfl, by simp [hr8], by simp [hr9], by simp [hr10], by simp [hr11], by simp [hr12],
        by simp [hcl_next, hnxt_it], by simp [hdiv_eq], by simp, fun h => by omega, fun _ => ?_⟩,
        by simp [hr19]⟩
      refine ⟨by simp, by simp [hcand_lt], ?_, ?_⟩
      · simp only [Function.update_of_ne (by decide : (18 : ℕ) ≠ 19),
          Function.update_of_ne (by decide : (18 : ℕ) ≠ 16),
          Function.update_of_ne (by decide : (18 : ℕ) ≠ 15),
          Function.update_of_ne (by decide : (18 : ℕ) ≠ 17), Function.update_self,
          Function.update_of_ne (by decide : (15 : ℕ) ≠ 19),
          Function.update_of_ne (by decide : (15 : ℕ) ≠ 16)]
        rwa [← hcur_bot]
      · intro e he
        simp only [Function.update_of_ne (by decide : (18 : ℕ) ≠ 19),
          Function.update_of_ne (by decide : (18 : ℕ) ≠ 16),
          Function.update_of_ne (by decide : (18 : ℕ) ≠ 15),
          Function.update_of_ne (by decide : (18 : ℕ) ≠ 17), Function.update_self,
          Function.update_of_ne (by decide : (15 : ℕ) ≠ 19),
          Function.update_of_ne (by decide : (15 : ℕ) ≠ 16)] at he ⊢
        rw [← hcur_bot] at he
        exact hcand_min e he
  · -- Bit `j` is 0 (`rem % 2 = 0`)
    intro hbit0
    have hcl_next : diff % 2 ^ (j + 1) = climbed := by rw [hmod_eq, hbit0, mul_zero, add_zero]
    refine runs_seq_nop_le ?_
    refine runs_assign_le (v := rem / 2) (by eval_expr) ?_ (by dsimp [Expr.size]; omega)
    refine ⟨⟨rfl, by simp [hr8], by simp [hr9], by simp [hr10], by simp [hr11], by simp [hr12],
      by simp [hcl_next, hr15], by simp [hdiv_eq], by simp,
      fun h => by rw [hcl_next] at h; simp [hzero h],
      fun h => by
        rw [hcl_next] at h
        obtain ⟨h1, h2, h3, h4⟩ := hpos h
        refine ⟨by simp [h1], by simp [h2], ?_, ?_⟩
        · simpa [hr15] using h3
        · simpa [hr15] using h4⟩,
      by simp [hr19]⟩

/-- `minEdgeUpProc` satisfies `minEdgeUpContract`. -/
theorem minEdgeUp_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    {S : LSFState} {vList tOrigList : List ℕ}
    (hp : p.procs[b]? = some minEdgeUpProc) :
    MeetsContract w p b (minEdgeUpContract w S vList tOrigList) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨auxPtr, tPtr, vCap, eCap, n0, tM, uIdx, wIdx,
    t0Parent, t0ParentTreeIdx, t0Depth, thParent, upV, upMinIdx,
    rfl, hw16, haux_ltw, ht_ltw, hInv, htM1, hAux, hT, hu_lt, hw_lt, hne_uw, hanc_or⟩ := hpre
  set logCap := auxLogCap n0
  set depthBase := auxT0DepthBase auxPtr vCap n0
  set upVBase := auxUpVBase auxPtr vCap n0
  set upMinBase := auxUpMinIdxBase auxPtr vCap n0
  set piBase := tPiBase tPtr vCap tM
  set origIdBase := tOrigIdBase tPtr vCap tM
  obtain ⟨-, -, -, -, h4_dep, h5_log, h6_upV, h7_upMin, -, -, -, -, -, -, -, -, -,
    hvLen, hvNd, hvMem, htLen, -, -, -, hr0_lt, hr0_v, hpar_mem, hpti_mem, hdep_mem, hup_mem,
    -, -, hdep0, ht0Edge, hUpProp, -⟩ := hAux
  obtain ⟨-, -, h2_orig, h3_pi, -, -, -, -, htLenT, -, htMemT, hOrigLA, hPiLA, -⟩ := hT
  have hpar_lt : ∀ i < n0, t0Parent i < n0 := fun i hi => (hpar_mem i hi).2
  have hstep : ∀ i (hi : i < vList.length), i ≠ mem (auxPtr + auxOffR0Idx) →
      t0Depth i = t0Depth (t0Parent i) + 1 ∧
      ∃ f ∈ S.T₀.E, (S.T₀.tail f = vList[i] ∧ S.T₀.head f = vList[t0Parent i]!) ∨
        (S.T₀.tail f = vList[t0Parent i]! ∧ S.T₀.head f = vList[i]) := fun i hi hne => by
    obtain ⟨hd, hpti, hfE, hfh⟩ := ht0Edge i hi hne
    exact ⟨hd, tOrigList[t0ParentTreeIdx i]!, hfE, hfh⟩
  have hall_path : ∀ i (hi : i < n0),
      (∀ k ≤ t0Depth i,
        ∃ (ha : t0Parent^[k] i < n0), t0Depth (t0Parent^[k] i) = t0Depth i - k ∧
        vList[t0Parent^[k] i]'(by omega) ∈ S.T₀.walkVertices (vList[i]'(by omega))
          (S.T₀.forestPath (vList[i]'(by omega)) S.r₀)) ∧
      (∀ w ∈ S.T₀.walkVertices (vList[i]'(by omega)) (S.T₀.forestPath (vList[i]'(by omega)) S.r₀),
        ∃ k ≤ t0Depth i, ∃ (ha : t0Parent^[k] i < n0), w = vList[t0Parent^[k] i]'(by omega)) :=
    fun i hi => by
      have h := auxAt_t0Parent_path hInv.hT₀ hvLen hvNd hvMem hr0_lt hr0_v hpar_lt hdep0 hstep
        (t0Depth i) i hi rfl
      exact ⟨h.2.1, h.2.2⟩
  have hlog_pos : 1 ≤ logCap := by dsimp [logCap, auxLogCap]; omega
  have hupV_it : ∀ i < n0, ∀ j < logCap, upV i j = t0Parent^[2 ^ j] i :=
    fun i hi j hj => upV_eq_iterate
      (fun x hx _ => (hUpProp x hx 0 hlog_pos).1 rfl |>.1)
      (fun x hx k hk => (hUpProp x hx k (by omega)).2.1 hk)
      (fun x hx k hk => (hup_mem x hx k hk).2.1) j hj i hi
  have hdu_lt : t0Depth uIdx < n0 :=
    auxAt_t0Depth_lt hInv.hT₀ hvLen hvNd hvMem hr0_lt hr0_v hpar_lt hdep0 hstep hu_lt
  have hdw_lt : t0Depth wIdx < n0 :=
    auxAt_t0Depth_lt hInv.hT₀ hvLen hvNd hvMem hr0_lt hr0_v hpar_lt hdep0 hstep hw_lt
  -- Determine `(botIdx, topIdx)` based on which depth is strictly greater
  have hbot_top : ∃ botIdx topIdx,
      ((t0Depth wIdx < t0Depth uIdx ∧ botIdx = uIdx ∧ topIdx = wIdx) ∨
       (¬ t0Depth wIdx < t0Depth uIdx ∧ botIdx = wIdx ∧ topIdx = uIdx)) ∧
      botIdx < n0 ∧ topIdx < n0 ∧
      t0Depth topIdx < t0Depth botIdx ∧
      t0Parent^[t0Depth botIdx - t0Depth topIdx] botIdx = topIdx := by
    rw [getElem!_pos vList wIdx (by omega), getElem!_pos vList uIdx (by omega)] at hanc_or
    rcases hanc_or with hwu | huw
    · obtain ⟨hle, hit⟩ := ancestor_depth_iterate hInv.hT₀ hvLen hvNd hvMem hr0_lt hr0_v hpar_lt
        hdep0 hstep hu_lt hw_lt hwu
      have hlt : t0Depth wIdx < t0Depth uIdx := by
        by_contra hge
        have heq : t0Depth uIdx - t0Depth wIdx = 0 := by omega
        rw [heq] at hit; exact hne_uw hit
      exact ⟨uIdx, wIdx, Or.inl ⟨hlt, rfl, rfl⟩, hu_lt, hw_lt, hlt, hit⟩
    · obtain ⟨hle, hit⟩ := ancestor_depth_iterate hInv.hT₀ hvLen hvNd hvMem hr0_lt hr0_v hpar_lt
        hdep0 hstep hw_lt hu_lt huw
      have hlt : t0Depth uIdx < t0Depth wIdx := by
        by_contra hge
        have heq : t0Depth wIdx - t0Depth uIdx = 0 := by omega
        rw [heq] at hit; exact hne_uw hit.symm
      exact ⟨wIdx, uIdx, Or.inr ⟨by omega, rfl, rfl⟩, hw_lt, hu_lt, hlt, hit⟩
  obtain ⟨botIdx, topIdx, hcase, hbot_lt, htop_lt, hdep_lt, hbot_hit⟩ := hbot_top
  set diff := t0Depth botIdx - t0Depth topIdx
  have hdiff_pos : 1 ≤ diff := by omega
  have hdiff_lt_n0 : diff < n0 := by
    rcases hcase with ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ <;> omega
  have hdiff_lt_pow : diff < 2 ^ logCap := by
    have h1 : n0 + 1 < 2 ^ (Nat.log 2 (n0 + 1) + 1) := Nat.lt_pow_succ_log_self (by decide) (n0 + 1)
    dsimp only [logCap, auxLogCap]; omega
  -- Word-size bounds from `haux_ltw` and `ht_ltw`
  have hdep_ltw : depthBase + n0 < 2 ^ w := by
    dsimp only [depthBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase,
      auxVListBase, auxVIdxBase, auxSize] at haux_ltw ⊢; omega
  have hupV_ltw : upVBase + n0 * logCap < 2 ^ w := by
    dsimp only [upVBase, logCap, auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase,
      auxVListBase, auxVIdxBase, auxSize] at haux_ltw ⊢; omega
  have hupMin_ltw : upMinBase + n0 * logCap < 2 ^ w := by
    dsimp only [upMinBase, logCap, auxUpMinIdxBase, auxUpVBase, auxT0DepthBase,
      auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase, auxSize] at haux_ltw ⊢
    omega
  have hpi_ltw : piBase + tM < 2 ^ w := by
    dsimp only [piBase, tPiBase, tOrigIdBase, tDgTPtr, tBlockSize] at ht_ltw ⊢; omega
  have horig_ltw : origIdBase + tM < 2 ^ w := by
    dsimp only [origIdBase, tOrigIdBase, tDgTPtr, tBlockSize] at ht_ltw ⊢; omega
  have hlog_ltw : logCap < 2 ^ w := by
    have : 1 * logCap ≤ n0 * logCap := Nat.mul_le_mul_right _ (by omega)
    omega
  have hpi_mem : ∀ i < tM, mem (piBase + i) = S.π (tOrigList[i]!) := fun i hi => by
    have h1 := hPiLA i (by simp [htLen, hi])
    rw [List.getElem_map] at h1
    rw [getElem!_pos tOrigList i (by omega)]
    exact h1
  have horig_mem : ∀ i < tM, mem (origIdBase + i) = tOrigList[i]! := fun i hi => by
    rw [getElem!_pos tOrigList i (by omega)]
    exact hOrigLA i (by omega)
  let Inv : ℕ → State → Prop := fun k st =>
    st.mem = mem ∧ st.regs 8 = logCap ∧ st.regs 9 = upVBase ∧ st.regs 10 = upMinBase ∧
    st.regs 11 = piBase ∧ st.regs 12 = origIdBase ∧
    st.regs 15 = t0Parent^[diff % 2 ^ k] botIdx ∧
    st.regs 16 = diff / 2 ^ k ∧
    st.regs 19 = k ∧
    (diff % 2 ^ k = 0 → st.regs 17 = 0) ∧
    (0 < diff % 2 ^ k →
      st.regs 17 = 1 ∧ st.regs 18 < tM ∧
      tOrigList[st.regs 18]! ∈ walkEdges (S.T₀.forestPath (vList[botIdx]!) (vList[st.regs 15]!)) ∧
      ∀ e ∈ walkEdges (S.T₀.forestPath (vList[botIdx]!) (vList[st.regs 15]!)),
        S.π (tOrigList[st.regs 18]!) ≤ S.π e)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 19) (lo := .const 0) (hi := .reg 8)
    (body := minEdgeUpStepStmt)
    (P := fun st => st.mem = mem ∧ st.regs 8 = logCap ∧ st.regs 9 = upVBase ∧
      st.regs 10 = upMinBase ∧ st.regs 11 = piBase ∧ st.regs 12 = origIdBase ∧
      st.regs 15 = botIdx ∧ st.regs 16 = diff ∧ st.regs 17 = 0 ∧ st.regs 18 = 0)
    (Inv := Inv) 110 0 logCap (Nat.zero_le _) (by omega) (fun _ => hlog_ltw)
    (fun st ⟨hm, h8, h9, h10, h11, h12, h15, h16, h17, _⟩ => by
      refine ⟨by eval_expr, hm, by simp [h8], by simp [h9], by simp [h10], by simp [h11],
        by simp [h12], by simp [h15, Nat.mod_one], by simp [h16], by simp, fun _ => by simp [h17],
        fun h => by simp [Nat.mod_one] at h⟩)
    (fun _ st _ _ hi => hi.2.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hi => by have h8 := hi.2.1; eval_expr)
    (fun j _ hj =>
      minEdgeUpStep_triple hw16 hInv.hT₀ hvLen hvNd hvMem htLen hupV_ltw hupMin_ltw hpi_ltw
        (by omega) hbot_lt htop_lt rfl (le_of_lt hdep_lt) hall_path
        (fun i hi k hk => ⟨(hup_mem i hi k hk).1, (hup_mem i hi k hk).2.1⟩)
        (fun i hi k hk => ⟨(hup_mem i hi k hk).2.2.1, (hup_mem i hi k hk).2.2.2 htM1⟩)
        hpi_mem hupV_it
        (fun i hi k hk hne => by
          obtain ⟨h1, h2, h3⟩ := (hUpProp i hi k hk).2.2 hne
          exact ⟨by omega, h2, h3⟩) j hj)
  -- Run prefix + loop + return
  refine runs_start_le ?_
  dsimp only [minEdgeUpProc, startState]
  have haux_hdr_lt : auxPtr + 7 < 2 ^ w := by
    dsimp [auxSize] at haux_ltw; omega
  have ht_hdr_lt : tPtr + 3 < 2 ^ w := by
    dsimp [tBlockSize] at ht_ltw; omega
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := depthBase) (by dsimp only [auxOffT0DepthPtr]; eval_expr) h4_dep) ?_; dsimp only
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := logCap) (by dsimp only [auxOffLogCap]; eval_expr) h5_log) ?_; dsimp only
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := upVBase) (by dsimp only [auxOffUpVPtr]; eval_expr) h6_upV) ?_; dsimp only
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := upMinBase) (by dsimp only [auxOffUpMinIdxPtr]; eval_expr) h7_upMin) ?_; dsimp only
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := piBase) (by dsimp only [tOffPiPtr]; eval_expr) h3_pi) ?_; dsimp only
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := origIdBase) (by dsimp only [tOffOrigIdPtr]; eval_expr) h2_orig) ?_; dsimp only
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := t0Depth uIdx) (by eval_expr) (hdep_mem uIdx hu_lt)) ?_; dsimp only
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := t0Depth wIdx) (by eval_expr) (hdep_mem wIdx hw_lt)) ?_; dsimp only
  refine runs_seq_cond_le (v := if t0Depth wIdx < t0Depth uIdx then 1 else 0) (by eval_expr) ?_ ?_
  · intro hlt1
    have hlt_wu : t0Depth wIdx < t0Depth uIdx := by by_contra hc; simp [hc] at hlt1
    have hbt : botIdx = uIdx ∧ topIdx = wIdx := by
      rcases hcase with ⟨_, h1, h2⟩ | ⟨hnot, _, _⟩
      · exact ⟨h1, h2⟩
      · exact absurd hlt_wu hnot
    refine runs_seq_assoc_le (runs_seq_assign_le (v := botIdx) (by rw [hbt.1]; eval_expr) ?_); dsimp only
    refine runs_seq_assign_le (v := diff) (by dsimp only [diff]; rw [hbt.1, hbt.2]; eval_expr) ?_; dsimp only
    refine runs_seq_assign_le (v := 0) (by eval_expr) ?_; dsimp only
    refine runs_seq_assign_le (v := 0) (by eval_expr) ?_; dsimp only
    refine runs_seq_triple_le hloop ⟨rfl, by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp⟩ ?_
    rintro st₁ ⟨hm1, -, -, -, -, h12, h15, -, -, -, hpos1⟩
    have hmod_all : diff % 2 ^ logCap = diff := Nat.mod_eq_of_lt hdiff_lt_pow
    rw [hmod_all, hbot_hit] at h15
    obtain ⟨_, h18_lt, h18_mem, h18_min⟩ := hpos1 (by omega)
    rw [h15] at h18_mem h18_min
    have hret_eq : tOrigList[st₁.regs 18]! =
        minEdgeOn S.π (walkEdges (S.T₀.forestPath (vList[uIdx]!) (vList[wIdx]!))) := by
      rw [← hbt.1, ← hbt.2]
      exact eq_minEdgeOn_of_le hInv.hord (walkEdges_forestPath_sub_edges hInv.hT₀.isForest)
        h18_mem h18_min
    refine runs_ret_le (Expr.eval_load_of_eq (v := tOrigList[st₁.regs 18]!)
      (by eval_expr) (by rw [hm1]; exact horig_mem _ h18_lt))
      ⟨auxPtr, tPtr, vCap, n0, tM, uIdx, wIdx, rfl, hm1, hret_eq⟩ ?_
    simp only [minEdgeUpContract, List.getD_cons_zero, List.getD_cons_succ, Expr.size,
      Nat.sub_zero]; omega
  · intro hlt0
    have hnot_wu : ¬ t0Depth wIdx < t0Depth uIdx := fun hc => by simp [hc] at hlt0
    have hbt : botIdx = wIdx ∧ topIdx = uIdx := by
      rcases hcase with ⟨h1, _, _⟩ | ⟨_, h1, h2⟩
      · exact absurd h1 hnot_wu
      · exact ⟨h1, h2⟩
    refine runs_seq_assoc_le (runs_seq_assign_le (v := botIdx) (by rw [hbt.1]; eval_expr) ?_); dsimp only
    refine runs_seq_assign_le (v := diff) (by dsimp only [diff]; rw [hbt.1, hbt.2]; eval_expr) ?_; dsimp only
    refine runs_seq_assign_le (v := 0) (by eval_expr) ?_; dsimp only
    refine runs_seq_assign_le (v := 0) (by eval_expr) ?_; dsimp only
    refine runs_seq_triple_le hloop ⟨rfl, by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp⟩ ?_
    rintro st₁ ⟨hm1, -, -, -, -, h12, h15, -, -, -, hpos1⟩
    have hmod_all : diff % 2 ^ logCap = diff := Nat.mod_eq_of_lt hdiff_lt_pow
    rw [hmod_all, hbot_hit] at h15
    obtain ⟨_, h18_lt, h18_mem, h18_min⟩ := hpos1 (by omega)
    rw [h15] at h18_mem h18_min
    have hcomm : walkEdges (S.T₀.forestPath (vList[uIdx]!) (vList[wIdx]!)) =
        walkEdges (S.T₀.forestPath (vList[wIdx]!) (vList[uIdx]!)) := by
      rw [getElem!_pos vList uIdx (by omega), getElem!_pos vList wIdx (by omega)]
      have hconn : S.T₀.Connected (vList[uIdx]'(by omega)) (vList[wIdx]'(by omega)) :=
        hInv.hT₀.connected ((hvMem _).mp (List.getElem_mem _)) ((hvMem _).mp (List.getElem_mem _))
      rw [← walkEdges_walkRev, ← forestPath_rev hInv.hT₀.isForest hconn]
    have hret_eq : tOrigList[st₁.regs 18]! =
        minEdgeOn S.π (walkEdges (S.T₀.forestPath (vList[uIdx]!) (vList[wIdx]!))) := by
      rw [hcomm, ← hbt.1, ← hbt.2]
      exact eq_minEdgeOn_of_le hInv.hord (walkEdges_forestPath_sub_edges hInv.hT₀.isForest)
        h18_mem h18_min
    refine runs_ret_le (Expr.eval_load_of_eq (v := tOrigList[st₁.regs 18]!)
      (by eval_expr) (by rw [hm1]; exact horig_mem _ h18_lt))
      ⟨auxPtr, tPtr, vCap, n0, tM, uIdx, wIdx, rfl, hm1, hret_eq⟩ ?_
    simp only [minEdgeUpContract, List.getD_cons_zero, List.getD_cons_succ, Expr.size,
      Nat.sub_zero]; omega

end

end MinCostFlow.LSF.Program
