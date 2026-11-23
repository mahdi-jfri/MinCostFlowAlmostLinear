module

public import MinCostFlow.SparseCore.Program.AssemblyFirstWalkBank

import MinCostFlow.DynSpanner.Program.DynSpannerAmortAppend
import MinCostFlow.DynSpanner.Program.DynSpannerDSBank
import Mathlib.Tactic

/-!
# Simultaneous walk-length, output-count, and bank bound for dynamic spanners (`AssemblyFsCostSpanBank`)

Tightens `AssemblyFirstWalkStep` / `AssemblyFirstWalkBank` to keep the factor `400` on re-embedded
walk lengths and simultaneously account for the disjoint `90 * |D|`, `90 * |R|`, `240 * |UH|`,
and `240 * |U|` summands already present in `dsStepAmortCost`:

* `runStepReemb_400_walks_le_stepCost`: `400 * ∑_{e ∈ runStepReembSet k} |piTotal (runState (k+1)) e| ≤ dsStepCostAt ... k 0`.
* `updateReemb_400_walks_le_stepCost_sum`: batch induction over a slice `U` of a valid run.
* `dsHist_walks_counts_bank_le`: for any `DSHist` `s` and valid deletion/split batch `U`,
  `400 * reembWalks + 90 * |D| + 90 * |R| + 240 * |UH| + 240 * |U| + s'.bank P ≤ s.bank P + dsBatchCharge`.
-/

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

public section

/-- **Single-step 400x new-walk bound (restart, `j = 0`)**. -/
theorem runStepReemb_400_walks_le_stepCost_zero (impl : SparsifyImpl) {G₀ : MGraph}
    {mMax L q vCap eCap : ℕ} (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k : ℕ} (hk : k < us.length) (hj : chooseLevel L q (k + 1) = 0) :
    400 * ∑ e ∈ runStepReembSet (L := L) G₀ q (canonicalSparsify impl) us k,
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
  have hwalk : ∀ e ∈ G'.E, (piTotal (step st u sp).state e).length ≤
      ((canonicalSparsify impl (activeSubgraph G') (activeSubgraph G') idEmb).emb e).length := by
    intro e he
    rw [piTotal_eq_piLtFrom, hPi, hDom]
    rw [piLtFrom_eq_level_zero _ _ (by simpa using he) (fun l hl => by
      simp [Nat.pos_iff_ne_zero.mp hl])]
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

/-- **Single-step 400x new-walk bound (rebuild, `j > 0`)**. -/
theorem runStepReemb_400_walks_le_stepCost_pos (impl : SparsifyImpl) {G₀ : MGraph}
    {mMax L q vCap eCap : ℕ} (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k : ℕ} (hk : k < us.length) (hj : 0 < chooseLevel L q (k + 1)) :
    400 * ∑ e ∈ runStepReembSet (L := L) G₀ q (canonicalSparsify impl) us k,
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
  have hcost : dsStepCostAt G₀ impl mMax L q vCap eCap us k 0 =
      dsStepPosCostModel m mMax vCap eCap 0 := by
    simp only [dsStepCostAt, hu, Nat.pos_iff_ne_zero.mp hj, ↓reduceIte]
    rfl
  rw [hR, hst1, hcost]
  by_cases hne : m.E_aff.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty, Nat.mul_zero]
    exact Nat.zero_le _
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
  exact le_trans h1 (le_trans h2 h3)

/-- **Single-step 400x new-walk bound** (both `j = 0` and `j > 0`). -/
theorem runStepReemb_400_walks_le_stepCost (impl : SparsifyImpl) {G₀ : MGraph}
    {mMax L q vCap eCap : ℕ} (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k : ℕ} (hk : k < us.length) :
    400 * ∑ e ∈ runStepReembSet (L := L) G₀ q (canonicalSparsify impl) us k,
        (piTotal (runState (L := L) G₀ q (canonicalSparsify impl) us (k + 1)) e).length ≤
      dsStepCostAt G₀ impl mMax L q vCap eCap us k 0 := by
  rcases Nat.eq_zero_or_pos (chooseLevel L q (k + 1)) with hj | hj
  · exact runStepReemb_400_walks_le_stepCost_zero impl hVG₀ hL hq hGm₀ hBV hds hk hj
  · exact runStepReemb_400_walks_le_stepCost_pos impl hVG₀ hL hq hGm₀ hBV hds hk hj

/-- Prefix induction for `400 * reembWalks ≤ ∑ dsStepCostAt ... 0`. -/
private theorem reemb_400_walks_prefix_le (impl : SparsifyImpl) {G₀ : MGraph}
    {mMax L q vCap eCap : ℕ} (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u) (k₀ : ℕ) :
    ∀ n, k₀ + n ≤ us.length →
      400 * ∑ e ∈ ((Finset.range n).biUnion fun i =>
          runStepReembSet (L := L) G₀ q (canonicalSparsify impl) us (k₀ + i)) ∩
          (runState (L := L) G₀ q (canonicalSparsify impl) us (k₀ + n)).G.E,
        (piTotal (runState (L := L) G₀ q (canonicalSparsify impl) us (k₀ + n)) e).length ≤
      ∑ i ∈ Finset.range n, dsStepCostAt G₀ impl mMax L q vCap eCap us (k₀ + i) 0
  | 0, _ => by simp
  | n + 1, hn => by
    classical
    set sp := canonicalSparsify impl
    have hk : k₀ + n < us.length := by omega
    set u := us[k₀ + n]'hk
    have hu : us[k₀ + n]? = some u := List.getElem?_eq_getElem hk
    have ih := reemb_400_walks_prefix_le (vCap := vCap) (eCap := eCap) impl hVG₀ hL hq hGm₀ hBV hds
      k₀ n (by omega)
    have hstep := runStepReemb_400_walks_le_stepCost (vCap := vCap) (eCap := eCap) impl hVG₀ hL hq
      hGm₀ hBV hds hk
    set st := runState (L := L) G₀ q sp us (k₀ + n)
    set st' := runState (L := L) G₀ q sp us (k₀ + (n + 1))
    have hst' : st' = (step st u sp).state := by
      show runState (L := L) G₀ q sp us (k₀ + n + 1) = _
      simp only [runState, hu]; rfl
    have hR : runStepReembSet (L := L) G₀ q sp us (k₀ + n) = stepReembSet st u := by
      simp only [runStepReembSet, hu]; rfl
    have hsame := piTotal_eq_of_not_mem_stepReembSet hVG₀ hL hq hGm₀
      (canonicalSparsify_spec_absorb impl mMax) hBV hds hk
    simp only at hsame
    have hSpec := canonicalSparsify_spec_absorb impl mMax
    have hE : st'.G.E ⊆ st.G.E := by
      have hI := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds (k₀ + n) hk.le).1.G_eq
      have hI' := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds (k₀ + n + 1) hk).1.G_eq
      rw [show st' = runState (L := L) G₀ q sp us (k₀ + n + 1) from rfl, hI', hI,
        take_succ_of_getElem? hu, applyBatch_append]
      exact applyUpdate_E_subset_of_delOrSplit (hds u (List.getElem_mem hk))
    set A := (Finset.range n).biUnion fun i => runStepReembSet (L := L) G₀ q sp us (k₀ + i)
    set R := runStepReembSet (L := L) G₀ q sp us (k₀ + n)
    have hA : (Finset.range (n + 1)).biUnion
        (fun i => runStepReembSet (L := L) G₀ q sp us (k₀ + i)) = A ∪ R := by
      rw [Finset.range_add_one, Finset.biUnion_insert, Finset.union_comm]
    rw [hA, Finset.sum_range_succ]
    have hsplit := Finset.sum_filter_add_sum_filter_not ((A ∪ R) ∩ st'.G.E) (· ∈ R)
      (fun e => (piTotal st' e).length)
    have h1 : ∑ e ∈ ((A ∪ R) ∩ st'.G.E).filter (· ∈ R), (piTotal st' e).length ≤
        ∑ e ∈ R, (piTotal st' e).length :=
      Finset.sum_le_sum_of_subset (fun e he => (Finset.mem_filter.mp he).2)
    have h2 : ∑ e ∈ ((A ∪ R) ∩ st'.G.E).filter (· ∉ R), (piTotal st' e).length ≤
        ∑ e ∈ A ∩ st.G.E, (piTotal st e).length := by
      calc ∑ e ∈ ((A ∪ R) ∩ st'.G.E).filter (· ∉ R), (piTotal st' e).length
          = ∑ e ∈ ((A ∪ R) ∩ st'.G.E).filter (· ∉ R), (piTotal st e).length := by
            refine Finset.sum_congr rfl fun e he => ?_
            obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
            have heG : e ∈ st'.G.E := (Finset.mem_inter.mp he1).2
            rw [hst'] at heG ⊢
            rw [hR] at he2
            rw [hsame e heG he2]
        _ ≤ ∑ e ∈ A ∩ st.G.E, (piTotal st e).length := by
            refine Finset.sum_le_sum_of_subset fun e he => ?_
            obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
            obtain ⟨heAR, heG⟩ := Finset.mem_inter.mp he1
            refine Finset.mem_inter.mpr ⟨?_, hE heG⟩
            rcases Finset.mem_union.mp heAR with h | h
            · exact h
            · exact absurd h he2
    have hstep' : 400 * ∑ e ∈ R, (piTotal st' e).length ≤
        dsStepCostAt G₀ impl mMax L q vCap eCap us (k₀ + n) 0 := hstep
    omega

/-- **Simultaneous walk-length, output-count, and bank bound for a `DSHist` batch update.**
A single unit of `s.bank P + dsBatchCharge` simultaneously pays `400 * reembWalks`, `90 * |D|`,
`90 * |R|`, `240 * |UH|`, `240 * |U|`, and the new bank `s'.bank P`. -/
theorem dsHist_walks_counts_bank_le (P : DSParams) (s : DSHist) (U : List Update)
    (hVG₀ : s.G₀.IsValid) (hL : 1 ≤ P.L) (hGm₀ : s.G₀.m ≤ P.mMax)
    (hBV : s.G₀.BatchIsValid (s.flat ++ U)) (hds : ∀ u ∈ s.flat ++ U, isDelOrSplit u)
    (hsplit : batchSplitCount (s.flat ++ U) ≤ P.splitBound)
    (hp : 1 ≤ max P.impl.p_s P.impl.p_t) :
    let out := update (s.state P) U (canonicalSparsify P.impl)
    let R := updateReembSet (s.state P) U (canonicalSparsify P.impl)
    400 * (∑ e ∈ R, (piTotal ((⟨s.G₀, s.Us ++ [U]⟩ : DSHist).state P) e).length) +
      90 * out.D.card + 90 * R.card + 240 * out.UH.length + 240 * U.length +
      (⟨s.G₀, s.Us ++ [U]⟩ : DSHist).bank P ≤
      s.bank P + dsBatchCharge P.impl P.mMax P.L (s.G₀.n + P.splitBound) s.G₀
        (s.G₀.applyBatch s.flat) U := by
  intro out R
  have hq : 1 ≤ s.q P := le_trans (by decide) (two_le_phaseBase _ _)
  have hst : s.state P = runState (L := P.L) s.G₀ (s.q P) (canonicalSparsify P.impl) (s.flat ++ U)
      s.flat.length := by
    rw [runState_append s.G₀ (s.q P) (canonicalSparsify P.impl) s.flat U s.flat.length le_rfl]; rfl
  have hst' : (⟨s.G₀, s.Us ++ [U]⟩ : DSHist).state P =
      runState (L := P.L) s.G₀ (s.q P) (canonicalSparsify P.impl) (s.flat ++ U)
        (s.flat.length + U.length) := by
    simp only [DSHist.state, dsHist_flat_append, List.length_append]; rfl
  have hmatch : ∀ (i : ℕ) (hi : i < U.length),
      (s.flat ++ U)[s.flat.length + i]? = some (U[i]'hi) := by
    intro i hi
    simp only [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact List.getElem?_eq_getElem hi
  have hwalks : 400 * (∑ e ∈ R, (piTotal ((⟨s.G₀, s.Us ++ [U]⟩ : DSHist).state P) e).length) ≤
      ∑ i ∈ Finset.range U.length,
        dsStepCostAt s.G₀ P.impl P.mMax P.L (s.q P) P.vCap P.eCap (s.flat ++ U) (s.flat.length + i) 0 := by
    dsimp only [R]
    rw [hst, hst', updateReembSet_run_eq s.G₀ (s.flat ++ U) U s.flat.length hmatch]
    exact reemb_400_walks_prefix_le (vCap := P.vCap) (eCap := P.eCap) P.impl hVG₀ hL hq hGm₀
      hBV hds s.flat.length U.length (by simp)
  have hspec := update_batch_spec hVG₀ hL hq hGm₀ (canonicalSparsify_spec_absorb P.impl P.mMax)
    hBV hds (k₀ := s.flat.length) (U := U) (by simp) hmatch
  have hUH_eq : out.UH.length =
      ∑ i ∈ Finset.range U.length,
        (runStepOut (L := P.L) s.G₀ (s.q P) (canonicalSparsify P.impl) (s.flat ++ U)
          (s.flat.length + i)).UH.length := by
    dsimp only [out]; rw [hst]; exact hspec.2.2.2.2.1
  have hD_le : out.D.card ≤
      ∑ i ∈ Finset.range U.length,
        (runStepOut (L := P.L) s.G₀ (s.q P) (canonicalSparsify P.impl) (s.flat ++ U)
          (s.flat.length + i)).D.card := by
    dsimp only [out]; rw [hst]; exact hspec.2.2.2.2.2.2.2.2.1
  have hR_le : R.card ≤
      ∑ i ∈ Finset.range U.length,
        (runStepReembSet (L := P.L) s.G₀ (s.q P) (canonicalSparsify P.impl) (s.flat ++ U)
          (s.flat.length + i)).card := by
    dsimp only [R]
    rw [hst, updateReembSet_run_eq s.G₀ (s.flat ++ U) U s.flat.length hmatch]
    exact le_trans (Finset.card_le_card Finset.inter_subset_left) Finset.card_biUnion_le
  have hsplit_sum :
      ∑ r ∈ Finset.range U.length,
          dsStepAmortCost s.G₀ P.impl P.mMax P.L (s.q P) P.vCap P.eCap (s.flat ++ U)
            (s.flat.length + r) =
      ∑ r ∈ Finset.range U.length,
          (dsStepCostAt s.G₀ P.impl P.mMax P.L (s.q P) P.vCap P.eCap (s.flat ++ U)
            (s.flat.length + r) 0 + 35 * P.L + 520) +
        90 * ∑ r ∈ Finset.range U.length,
          (runStepOut (L := P.L) s.G₀ (s.q P) (canonicalSparsify P.impl) (s.flat ++ U)
            (s.flat.length + r)).D.card +
        90 * ∑ r ∈ Finset.range U.length,
          (runStepReembSet (L := P.L) s.G₀ (s.q P) (canonicalSparsify P.impl) (s.flat ++ U)
            (s.flat.length + r)).card +
        240 * ∑ r ∈ Finset.range U.length,
          (runStepOut (L := P.L) s.G₀ (s.q P) (canonicalSparsify P.impl) (s.flat ++ U)
            (s.flat.length + r)).UH.length +
        240 * U.length := by
    simp only [dsStepAmortCost_eq, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const,
      Finset.card_range, smul_eq_mul]
    ring
  have hstep_le : ∑ r ∈ Finset.range U.length,
        dsStepCostAt s.G₀ P.impl P.mMax P.L (s.q P) P.vCap P.eCap (s.flat ++ U)
          (s.flat.length + r) 0 ≤
      ∑ r ∈ Finset.range U.length,
        (dsStepCostAt s.G₀ P.impl P.mMax P.L (s.q P) P.vCap P.eCap (s.flat ++ U)
          (s.flat.length + r) 0 + 35 * P.L + 520) :=
    Finset.sum_le_sum fun _ _ => by omega
  have hcomb :
      400 * (∑ e ∈ R, (piTotal ((⟨s.G₀, s.Us ++ [U]⟩ : DSHist).state P) e).length) +
        90 * out.D.card + 90 * R.card + 240 * out.UH.length + 240 * U.length ≤
      ∑ r ∈ Finset.range U.length,
        dsStepAmortCost s.G₀ P.impl P.mMax P.L (s.q P) P.vCap P.eCap (s.flat ++ U)
          (s.flat.length + r) := by
    rw [hsplit_sum]; omega
  -- Combine with bank telescoping (same as `dsHist_reemb_walks_add_bank_le`)
  have hflat : (s.Us ++ [U]).flatten = s.flat ++ U := dsHist_flat_append s U
  have hsp := dsSpent_append P.impl P.mMax P.L (s.q P) P.vCap P.eCap s.G₀ s.flat U
  have hle := dsSpent_le_bankTotal (vCap := P.vCap) (eCap := P.eCap) (nMax := s.G₀.n + P.splitBound)
    P.impl (Us := s.Us ++ [U])
    hVG₀ hL hGm₀ (by rw [hflat]; exact hBV) (by rw [hflat]; exact hds)
    (by rw [hflat]; exact Nat.add_le_add_left hsplit _) hp
  have htot := dsBankTotal_append P.impl P.mMax P.L (s.q P) (s.G₀.n + P.splitBound) s.G₀ s.Us U
  simp only [DSHist.bank, dsBank]
  have hq' : (⟨s.G₀, s.Us ++ [U]⟩ : DSHist).q P = s.q P := rfl
  rw [hq', hflat]
  rw [hflat] at hle
  have hq'' : s.q P = phaseBase (s.G₀.n + P.splitBound) P.L := rfl
  rw [hq''] at hsp htot hcomb ⊢
  rw [show s.Us.flatten = s.flat from rfl] at htot ⊢
  omega

end

end MinCostFlow.SparseCore.Program
