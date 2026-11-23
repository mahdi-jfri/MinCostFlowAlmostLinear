module

public import MinCostFlow.DynSpanner.Program.DynSpannerAmortSum
public import MinCostFlow.DynSpanner.Program.DynSpannerAmortPosFacts
public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosNonEmptyDefs

/-!
# The new walks of one step of the spanner are paid by the step

One update of the dynamic spanner of Theorem 8.2 (page 39) gives new walks to the edges of
`stepReembSet` and keeps the walks of the other edges (`piTotal_eq_of_not_mem_stepReembSet`).
The program of the spanner writes each new walk into its memory, so the cost bound of its step
pays for the total length of the new walks. This file proves it, for step `k` of a run:
```
Σ_{e ∈ runStepReembSet k} |piTotal (runState (k + 1)) e| ≤ dsStepAmortCost k.
```
(`runStepReemb_walks_le_amortCost`). There are two cases.
* A restart (`j = 0`): every edge of the new graph `G'` gets the walk `shortcutWalk` of its walk
  in the sparsifier on `G'`. The cost of the restart has `800` times the total length of the
  walks of the sparsifier (`dsInitCoreCost`), and a short cut is not longer than the walk.
* A rebuild of level `j > 0`: the edges of `E_aff` get the walks `reembedWalk` of level `j`, and
  the cost of the step has `400` times their total length (`dsStepPosNonEmptyCost`). The program
  calls the sparsifier with host `G'` and the model with host `H_aux`; both give the same output
  (`canonicalSparsify_congr_ends`), so the walks are the same.
-/

public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

/-- The total embedding of a state, as the lookup over all levels. -/
theorem piTotal_eq_piLtFrom {L : ℕ} (st : DynSpannerState L) (e : ℕ) :
    piTotal st e = piLtFrom st.Pi_level st.inDom (L + 1) e := rfl

/-- If only level `0` holds `e` in its domain, the total embedding of `e` is its walk of
level `0`. -/
theorem piLtFrom_eq_level_zero {L : ℕ} (Pi_level : Fin (L + 1) → MinCostFlow.Embedding)
    (inDom : Fin (L + 1) → Finset ℕ) {e : ℕ} (h0 : e ∈ inDom ⟨0, Nat.zero_lt_succ L⟩)
    (hnone : ∀ k : Fin (L + 1), 0 < k.1 → e ∉ inDom k) :
    piLtFrom Pi_level inDom (L + 1) e = Pi_level ⟨0, Nat.zero_lt_succ L⟩ e := by
  have h1 := piLtFrom_eq_self_of_mem Pi_level inDom (j := ⟨0, Nat.zero_lt_succ L⟩) h0 h0
  rw [← h1]
  exact piLtFrom_eq_of_lt Pi_level inDom Nat.one_pos (Nat.succ_le_succ (Nat.zero_le L)) h0
    fun k hk _ => hnone k hk

/-- **The new walks of a restart.** If step `k` is a restart (`chooseLevel L q (k + 1) = 0`),
the total length of the new walks of its edges is at most its cost bound. -/
theorem runStepReemb_walks_le_stepCost_zero (impl : SparsifyImpl) {G₀ : MGraph}
    {mMax L q vCap eCap : ℕ} (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k : ℕ} (hk : k < us.length) (hj : chooseLevel L q (k + 1) = 0) :
    ∑ e ∈ runStepReembSet (L := L) G₀ q (canonicalSparsify impl) us k,
        (piTotal (runState (L := L) G₀ q (canonicalSparsify impl) us (k + 1)) e).length ≤
      dsStepCostAt G₀ impl mMax L q vCap eCap us k 0 := by
  set sp := canonicalSparsify impl
  set u := us[k]'hk
  have hu : us[k]? = some u := List.getElem?_eq_getElem hk
  have hSpec : SparsifySpec mMax (canonicalSparsifyParams impl mMax).absorbTime sp :=
    canonicalSparsify_spec_absorb impl mMax
  have hInv := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds k hk.le).1
  set st := runState (L := L) G₀ q sp us k
  have hj' : chooseLevel L st.q (st.t + 1) = 0 := by rw [hInv.q_eq, hInv.t_eq]; exact hj
  set G' := st.G.applyUpdate u
  have hR : runStepReembSet (L := L) G₀ q sp us k = G'.E := by
    simp only [runStepReembSet, hu]
    exact stepReembSet_eq_zero st u hj'
  have hst1 : runState (L := L) G₀ q sp us (k + 1) = (step st u sp).state := by
    simp only [runState, hu]; rfl
  have hPi : (step st u sp).state.Pi_level =
      fun i => if i.1 = 0 then (initCore G' sp).2.1 else fun _ => [] := by
    dsimp only [step]; rw [dite_eq_left_of_eq_true (eq_true hj')]; rfl
  have hDom : (step st u sp).state.inDom = fun i => if i.1 = 0 then G'.E else ∅ := by
    dsimp only [step]; rw [dite_eq_left_of_eq_true (eq_true hj')]; rfl
  have hCost : dsStepCostAt G₀ impl mMax L q vCap eCap us k 0 =
      dsStepZeroCost impl mMax L G' st.H (initCore G' sp).1 0 := by
    simp only [dsStepCostAt, hu, hj, ↓reduceIte]; rfl
  rw [hR, hCost, hst1]
  -- The walk of each edge is the short cut of its walk in the sparsifier.
  have hwalk : ∀ e ∈ G'.E, (piTotal (step st u sp).state e).length ≤
      ((canonicalSparsify impl (activeSubgraph G') (activeSubgraph G') idEmb).emb e).length := by
    intro e he
    rw [piTotal_eq_piLtFrom, hPi, hDom]
    rw [piLtFrom_eq_level_zero _ _ (by simpa using he) (fun k hk => by
      simp [Nat.pos_iff_ne_zero.mp hk])]
    have hne : G'.E.Nonempty := ⟨e, he⟩
    simp only [initCore, dite_eq_left hne]
    exact shortcutWalk_length_le G' _ (G'.tail e)
  have hsum := Finset.sum_le_sum hwalk
  have hcore : 800 * ∑ e ∈ G'.E,
      ((canonicalSparsify impl (activeSubgraph G') (activeSubgraph G') idEmb).emb e).length ≤
      dsInitCoreCost impl mMax G' := by
    simp only [dsInitCoreCost]
    omega
  simp only [dsStepZeroCost]
  omega

/-- The cost of a nonempty rebuild has `400` times the total length of the new walks. -/
theorem reembedWalks_le_dsStepPosNonEmptyCost (impl : SparsifyImpl) (mMax L vCap eCap j : ℕ)
    (G' J : MGraph) (piLt_mid embJH : MinCostFlow.Embedding) (S_prev : Finset ℕ) (eAff : List ℕ)
    (oldSum : ℕ) :
    400 * (eAff.map fun e => (reembedWalk G' G' piLt_mid
        (MinCostFlow.Embedding.comp embJH fun e =>
          shortcutWalk (canonicalSparsify impl G' J embJH).Jtilde (J.tail e)
            ((canonicalSparsify impl G' J embJH).emb e)) S_prev e).length).sum ≤
      dsStepPosNonEmptyCost impl mMax L vCap eCap j G' J piLt_mid embJH S_prev eAff oldSum := by
  simp only [dsStepPosNonEmptyCost]
  omega

/-- The cost of a step with `0 < j` and a nonempty `E_aff` is at least that of its rebuild. -/
theorem dsStepPosNonEmptyCost_le_dsStepPosCost (impl : SparsifyImpl) (mMax L vCap eCap j : ℕ)
    (G' J : MGraph) (piLt_mid embJH : MinCostFlow.Embedding) (S_prev : Finset ℕ) (eAff : List ℕ)
    (oldSum sPrevLen prefWords uhLen : ℕ) (h : 0 < eAff.length) :
    dsStepPosNonEmptyCost impl mMax L vCap eCap j G' J piLt_mid embJH S_prev eAff oldSum ≤
      dsStepPosCost impl mMax L vCap eCap j G' J piLt_mid embJH S_prev eAff oldSum sPrevLen
        prefWords uhLen := by
  simp only [dsStepPosCost, h, ↓reduceIte]
  omega

/-- The cost bound of a step with `0 < j` is at least the cost of its main part. -/
theorem dsStepPosCost_le_dsStepPosCostModel (m : StepPosModel) (mMax vCap eCap len : ℕ) :
    dsStepPosCost m.impl mMax m.L vCap eCap m.j m.G' m.J m.piLt_mid m.embJH m.S_prev
        m.E_aff.toList (modelOldSum m) m.S_prev.card len m.res.UH.length ≤
      dsStepPosCostModel m mMax vCap eCap len := by
  unfold dsStepPosCostModel
  omega

/-- **The new walks of a rebuild.** If step `k` rebuilds a level `j > 0`, the total length of the
new walks of its edges `E_aff` is at most its cost bound. -/
theorem runStepReemb_walks_le_stepCost_pos (impl : SparsifyImpl) {G₀ : MGraph}
    {mMax L q vCap eCap : ℕ} (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k : ℕ} (hk : k < us.length) (hj : 0 < chooseLevel L q (k + 1)) :
    ∑ e ∈ runStepReembSet (L := L) G₀ q (canonicalSparsify impl) us k,
        (piTotal (runState (L := L) G₀ q (canonicalSparsify impl) us (k + 1)) e).length ≤
      dsStepCostAt G₀ impl mMax L q vCap eCap us k 0 := by
  set sp := canonicalSparsify impl
  set u := us[k]'hk
  have hu : us[k]? = some u := List.getElem?_eq_getElem hk
  have hSpec : SparsifySpec mMax (canonicalSparsifyParams impl mMax).absorbTime sp :=
    canonicalSparsify_spec_absorb impl mMax
  obtain ⟨hInvk, -⟩ := runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds k hk.le
  obtain ⟨hInvk1, hRecs⟩ := runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds (k + 1) hk
  have hRec := hRecs k (Nat.lt_succ_self k) u hu
  let m : StepPosModel := ⟨G₀, impl, L, q, k, us, u⟩
  have hjL : m.j ≤ L := chooseLevel_le L q (k + 1)
  have hjL1 : m.j < L + 1 := Nat.lt_succ_of_le hjL
  have hch_j : chooseLevel L (runState (L := L) G₀ q sp us k).q
      ((runState (L := L) G₀ q sp us k).t + 1) = chooseLevel L q (k + 1) := by
    rw [hInvk.q_eq, hInvk.t_eq]
  have hch_ne : ¬ chooseLevel L (runState (L := L) G₀ q sp us k).q
      ((runState (L := L) G₀ q sp us k).t + 1) = 0 := by
    rw [hch_j]; exact Nat.pos_iff_ne_zero.mp hj
  have hst1 : runState (L := L) G₀ q sp us (k + 1) = m.res.state := by
    simp only [runState, hu]; rfl
  have hR : runStepReembSet (L := L) G₀ q sp us k = m.E_aff := by
    simp only [runStepReembSet, hu]
    dsimp only [stepReembSet]
    simp only [hch_ne, ↓reduceIte]
    simp only [hch_j]
    rfl
  have hDom : ∀ l : Fin (L + 1), m.res.state.inDom l =
      if l.1 < m.j then m.inDom_mid l else if l.1 = m.j then m.E_aff else ∅ := fun l => by
    show (step (runState (L := L) G₀ q sp us k) u sp).state.inDom l = _
    dsimp only [step]
    simp only [hch_ne, ↓reduceDIte]
    simp only [hch_j]
    rfl
  have hPi : m.res.state.Pi_level ⟨m.j, hjL1⟩ =
      reembedWalk m.G' m.H_lt m.piLt_mid
        (MinCostFlow.Embedding.comp m.embJH fun e =>
          shortcutWalk (if m.E_aff.Nonempty then sp (buildAuxHost m.G' m.H_lt m.E_aff) m.J m.embJH
            else ⟨m.J, idEmb, 0⟩).Jtilde (m.J.tail e)
            ((if m.E_aff.Nonempty then sp (buildAuxHost m.G' m.H_lt m.E_aff) m.J m.embJH
              else ⟨m.J, idEmb, 0⟩).emb e))
        m.S_prev := by
    show (step (runState (L := L) G₀ q sp us k) u sp).state.Pi_level _ = _
    dsimp only [step]
    simp only [hch_ne, ↓reduceDIte]
    have hmj : m.j = chooseLevel L q (k + 1) := rfl
    simp only [hch_j, hmj, lt_irrefl, ↓reduceIte]
    rfl
  have hG : m.res.state.G = m.G' := by
    show (step (runState (L := L) G₀ q sp us k) u sp).state.G = _
    dsimp only [step]
    simp only [hch_ne, ↓reduceDIte]
    rfl
  have hEsub : m.E_aff ⊆ m.G'.E := Finset.filter_subset _ _
  -- The new walk of an affected edge is its walk of level `j`.
  have hwalk : ∀ e ∈ m.E_aff,
      piTotal m.res.state e = m.res.state.Pi_level ⟨m.j, hjL1⟩ e := by
    intro e he
    have he0 : e ∈ m.res.state.inDom ⟨0, Nat.zero_lt_succ L⟩ := by
      have h1 := hInvk1.inDom0
      rw [← hInvk1.G_eq, hst1] at h1
      rw [h1, hG]
      exact hEsub he
    have hej : e ∈ m.res.state.inDom ⟨m.j, hjL1⟩ := by
      rw [hDom]; simp [he]
    rw [piTotal_eq_piLtFrom]
    rw [piLtFrom_eq_of_lt m.res.state.Pi_level m.res.state.inDom (Nat.succ_pos m.j)
      (Nat.succ_le_succ hjL) he0 fun l hl _ => by
        rw [hDom l]
        simp [Nat.not_lt.mpr (Nat.le_of_succ_le hl), Nat.ne_of_gt (Nat.lt_of_succ_le hl)]]
    exact piLtFrom_eq_self_of_mem m.res.state.Pi_level m.res.state.inDom he0 hej
  -- The cost of the step.
  have hcost : dsStepCostAt G₀ impl mMax L q vCap eCap us k 0 =
      dsStepPosCostModel m mMax vCap eCap 0 := by
    simp only [dsStepCostAt, hu, Nat.pos_iff_ne_zero.mp hj, ↓reduceIte]
    rfl
  rw [hR, hst1, hcost]
  by_cases hne : m.E_aff.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
    exact Nat.zero_le _
  -- The two hosts give the same sparsifier output.
  obtain ⟨-, -, -, -, -, -, hVG', hAuxV, hJV, hEmbAux, hSub, -⟩ := hRec.rebuild_sizes hj
  have hEmbG' : m.embJH.IsEmbedding m.J m.G' :=
    ⟨hEmbAux.1, fun e he => IsWalk.of_isSubgraph hSub (hEmbAux.2 e he)⟩
  have hLen1 : m.J.E.Nonempty → 1 ≤ m.embJH.length m.J := by
    rintro ⟨e, he⟩
    have hle : (m.embJH e).length ≤ m.embJH.length m.J :=
      Finset.le_sup (f := fun x => (m.embJH x).length) he
    have hpos : 1 ≤ (m.embJH e).length := by
      simp only [StepPosModel.embJH, projWalk, List.length_append, List.length_cons,
        List.length_nil]
      omega
    omega
  have hcongr : sp (buildAuxHost m.G' m.H_lt m.E_aff) m.J m.embJH =
      canonicalSparsify impl m.G' m.J m.embJH :=
    canonicalSparsify_congr_ends impl rfl rfl hAuxV hVG' hJV hLen1 hEmbAux hEmbG'
  have hsum : ∑ e ∈ m.E_aff, (piTotal m.res.state e).length =
      (m.E_aff.toList.map fun e => (reembedWalk m.G' m.G' m.piLt_mid
        (MinCostFlow.Embedding.comp m.embJH fun e =>
          shortcutWalk (canonicalSparsify impl m.G' m.J m.embJH).Jtilde (m.J.tail e)
            ((canonicalSparsify impl m.G' m.J m.embJH).emb e)) m.S_prev e).length).sum := by
    rw [Finset.sum_map_toList]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [hwalk e he, hPi, ite_eq_left hne, hcongr]
    rw [reembedWalk_congr_host (G' := m.G') (H_lt := m.H_lt) rfl rfl]
  rw [hsum]
  have hlen : 0 < m.E_aff.toList.length := by
    rw [Finset.length_toList]; exact Finset.card_pos.mpr hne
  have h1 := reembedWalks_le_dsStepPosNonEmptyCost impl mMax L vCap eCap m.j m.G' m.J m.piLt_mid
    m.embJH m.S_prev m.E_aff.toList (modelOldSum m)
  have h2 := dsStepPosNonEmptyCost_le_dsStepPosCost impl mMax L vCap eCap m.j m.G' m.J m.piLt_mid
    m.embJH m.S_prev m.E_aff.toList (modelOldSum m) m.S_prev.card 0 m.res.UH.length hlen
  have h3 : dsStepPosCost impl mMax L vCap eCap m.j m.G' m.J m.piLt_mid m.embJH m.S_prev
        m.E_aff.toList (modelOldSum m) m.S_prev.card 0 m.res.UH.length ≤
      dsStepPosCostModel m mMax vCap eCap 0 :=
    dsStepPosCost_le_dsStepPosCostModel m mMax vCap eCap 0
  omega

/-- **The new walks of one step are paid by the step.** For step `k` of a run of valid deletions
and splits, the total length of the new walks of the edges of `runStepReembSet` is at most the
amortized cost `dsStepAmortCost` of the step. -/
theorem runStepReemb_walks_le_amortCost (impl : SparsifyImpl) {G₀ : MGraph}
    {mMax L q vCap eCap : ℕ} (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k : ℕ} (hk : k < us.length) :
    ∑ e ∈ runStepReembSet (L := L) G₀ q (canonicalSparsify impl) us k,
        (piTotal (runState (L := L) G₀ q (canonicalSparsify impl) us (k + 1)) e).length ≤
      dsStepAmortCost G₀ impl mMax L q vCap eCap us k := by
  have h : ∑ e ∈ runStepReembSet (L := L) G₀ q (canonicalSparsify impl) us k,
        (piTotal (runState (L := L) G₀ q (canonicalSparsify impl) us (k + 1)) e).length ≤
      dsStepCostAt G₀ impl mMax L q vCap eCap us k 0 := by
    rcases Nat.eq_zero_or_pos (chooseLevel L q (k + 1)) with hj | hj
    · exact runStepReemb_walks_le_stepCost_zero impl hVG₀ hL hq hGm₀ hBV hds hk hj
    · exact runStepReemb_walks_le_stepCost_pos impl hVG₀ hL hq hGm₀ hBV hds hk hj
  rw [dsStepAmortCost_eq]
  omega

end MinCostFlow.SparseCore.Program
