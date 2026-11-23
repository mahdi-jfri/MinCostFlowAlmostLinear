module

public import MinCostFlow.DynSpanner.ProjGraphVerts

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Step transition for Algorithm 6

This file proves `step_inv` and `runInv_all`, advancing `SnapInv` and `StepCostRecord` across
every single update step `k → k + 1` (both `j = 0` restarts and `0 < j` rebuilds).
-/

namespace MinCostFlow.DynSpanner

section Transition

@[expose] public section

private lemma log_mono_nm {a b c d : ℕ} (h1 : a ≤ c) (h2 : b ≤ d) (p : ℕ) :
    (1 + Real.log ((a : ℝ) + (b : ℝ) + 2)) ^ p ≤
      (1 + Real.log ((c : ℝ) + (d : ℝ) + 2)) ^ p := by
  have ha : (1 : ℝ) ≤ (a : ℝ) + (b : ℝ) + 2 := by
    linarith [Nat.cast_nonneg (α := ℝ) a, Nat.cast_nonneg (α := ℝ) b]
  have hlog : Real.log ((a : ℝ) + (b : ℝ) + 2) ≤ Real.log ((c : ℝ) + (d : ℝ) + 2) :=
    Real.log_le_log (by linarith) (by gcongr)
  exact pow_le_pow_left₀ (by linarith [Real.log_nonneg ha]) (by linarith) p

private lemma batchInsertCount_map_delete (xs : List ℕ) :
    batchInsertCount (xs.map Update.delete) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [batchInsertCount] at ih ⊢

private lemma batchInsertCount_map_insert (xs : List ℕ) (t h : ℕ → ℕ) :
    batchInsertCount (xs.map fun e => Update.insert e (t e) (h e)) = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [batchInsertCount] at ih ⊢

private lemma batchDeleteCount_map_delete (xs : List ℕ) :
    batchDeleteCount (xs.map Update.delete) = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [batchDeleteCount] at ih ⊢; exact ih

private lemma batchDeleteCount_map_insert (xs : List ℕ) (t h : ℕ → ℕ) :
    batchDeleteCount (xs.map fun e => Update.insert e (t e) (h e)) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [batchDeleteCount] at ih ⊢

private lemma batchSplitCount_map_delete (xs : List ℕ) :
    batchSplitCount (xs.map Update.delete) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [batchSplitCount, isSplit] at ih ⊢

private lemma batchSplitCount_map_insert (xs : List ℕ) (t h : ℕ → ℕ) :
    batchSplitCount (xs.map fun e => Update.insert e (t e) (h e)) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [batchSplitCount, isSplit] at ih ⊢

private lemma dynState_eq {L : ℕ} (s : DynSpannerState L) {q' t' : ℕ} {G' : MGraph}
    (hq : s.q = q') (ht : s.t = t') (hG : s.G = G') :
    s = ⟨q', t', G', s.H_level, s.Pi_level, s.inDom, s.S_level, s.H⟩ := by
  cases s; cases hq; cases ht; cases hG; rfl

private theorem step_inv_restart {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k : ℕ} {u : Update} (hu_some : us[k]? = some u)
    (hk_inv : SnapInv G₀ L q mMax P sparsify us k)
    (hj0 : chooseLevel L q (k + 1) = 0) :
    SnapInv G₀ L q mMax P sparsify us (k + 1) ∧ StepCostRecord G₀ L q P sparsify us k u := by
  have hγl : 0 ≤ P.γ_ℓ := by linarith [P.hγ_ℓ]
  let st := runState (L := L) G₀ q sparsify us k
  let res := runStepOut (L := L) G₀ q sparsify us k
  have hres_eq : res = step st u sparsify := by
    dsimp only [res, runStepOut]
    rw [hu_some]
  have hst'_eq : runState (L := L) G₀ q sparsify us (k + 1) = res.state := by
    dsimp only [runState, res, runStepOut]
    rw [hu_some]
  obtain ⟨hBV_take_k, hds_take_k, hU_valid⟩ := batchIsValid_take us G₀ k hBV hds
  obtain ⟨hu_valid, hdu⟩ := hU_valid u hu_some
  have htake_succ : us.take (k + 1) = us.take k ++ [u] := take_succ_of_getElem? hu_some
  have hInv_k := batch_delOrSplit_invariants (us.take k) G₀ hVG₀ hBV_take_k hds_take_k
  rcases hInv_k with ⟨hVGk, hEGk_sub, _, hDeg_k, _, _, _⟩
  let Gk := G₀.applyBatch (us.take k)
  let G' := G₀.applyBatch (us.take (k + 1))
  have hG'_eq : G' = Gk.applyUpdate u := by
    simp [G', Gk, htake_succ, MGraph.applyBatch]
  have hVG' : G'.IsValid := hG'_eq ▸ isValid_applyUpdate_of_delOrSplit hVGk hu_valid hdu
  have hG'E_sub : G'.E ⊆ Gk.E := hG'_eq ▸ E_applyUpdate_subset hdu
  have hG'deg : G'.maxDeg ≤ G₀.maxDeg :=
    le_trans (hG'_eq ▸ maxDeg_applyUpdate_le hVGk hu_valid hdu) hDeg_k
  have hG'm_le : G'.m ≤ mMax :=
    le_trans (Finset.card_le_card (Finset.Subset.trans hG'E_sub hEGk_sub)) hGm₀
  have hG'm_le0 : G'.m ≤ G₀.m := Finset.card_le_card (Finset.Subset.trans hG'E_sub hEGk_sub)
  let res₀ := initAt G' L q (k + 1) sparsify
  have hP0 := initAt_state_props (L := L) (q := q) (t := k + 1) hSpec hVG' hG'm_le hG'deg
  rcases hP0 with ⟨hq0, ht0, hG0, _hHV0, _hH_V0, hH_E0, hH_sub0, hHls0, hHlV0, hin0, hinsub0,
    hinact0, hHlsp0, hemb0, hlen0, hvc0, hCost0⟩
  have hDB := diffBatch_spec hVGk hk_inv.H_sub hk_inv.H_V hu_valid hdu (hG'_eq ▸ hH_sub0.2.1)
  dsimp only at hDB
  rcases hDB with ⟨hBV_uh, hVH'_valid, hSub_H', hV_H', hE_H', _hDel_len, hIns_len, hPref_enc⟩
  let uhPref := restrictUpdate u st.H
  let H_mid_union := st.H.applyBatch uhPref
  let uhDel := ((H_mid_union.E \ res₀.state.H.E).sort (· ≤ ·)).map Update.delete
  let uhIns := ((res₀.state.H.E \ H_mid_union.E).sort (· ≤ ·)).map
    fun e => Update.insert e (G'.tail e) (G'.head e)
  have hstep_un : res =
      { state := { res₀.state with H := st.H.applyBatch (uhPref ++ uhDel ++ uhIns) }
        UH := uhPref ++ uhDel ++ uhIns
        D := (st.H.applyBatch (uhPref ++ uhDel ++ uhIns)).E
        cost := res₀.cost + (L + 1) * st.G.updateEnc u + H_mid_union.E.card +
          res₀.state.H.E.card + (uhPref ++ uhDel ++ uhIns).length +
          (st.H.applyBatch (uhPref ++ uhDel ++ uhIns)).E.card } := by
    rw [hres_eq]
    dsimp only [step]
    have hch0 : chooseLevel L st.q (st.t + 1) = 0 := by
      rw [hk_inv.q_eq, hk_inv.t_eq]; exact hj0
    simp only [hch0, ↓reduceDIte]
    have hstG' : st.G.applyUpdate u = G' := by rw [hk_inv.G_eq, ← hG'_eq]
    rw [hstG', hk_inv.q_eq, hk_inv.t_eq]
  have hUH_eq : res.UH = uhPref ++ uhDel ++ uhIns := by rw [hstep_un]
  have hSt'_rec : res.state = { res₀.state with H := st.H.applyBatch res.UH } := by
    rw [hUH_eq, hstep_un]
  have hD_eq : res.D = res.state.H.E := by rw [hSt'_rec, hstep_un]
  have hdbG' : (G₀.applyBatch (us.take k)).applyUpdate u = G' := hG'_eq.symm
  have hSt'_H_V : res.state.H.V = G'.V := by
    rw [hSt'_rec, hUH_eq]
    simpa only [st, H_mid_union, res₀, uhPref, uhDel, uhIns, hdbG', ← hG'_eq] using hV_H'
  have hSt'_H_E : res.state.H.E = res₀.state.H.E := by
    rw [hSt'_rec, hUH_eq]
    simpa only [st, H_mid_union, res₀, uhPref, uhDel, uhIns, hdbG', ← hG'_eq] using hE_H'
  have hSt'_H_sub : G'.IsSubgraph res.state.H := by
    rw [hSt'_rec, hUH_eq]
    simpa only [st, H_mid_union, res₀, uhPref, uhDel, uhIns, hdbG', ← hG'_eq] using hSub_H'
  have hSt'_H_valid : res.state.H.IsValid := by
    rw [hSt'_rec, hUH_eq]
    simpa only [st, H_mid_union, res₀, uhPref, uhDel, uhIns, hdbG', ← hG'_eq] using hVH'_valid
  have hSt'_H_E_union : res.state.H.E = unionEdgesLt res.state.H_level (L + 1) := by
    rw [hSt'_H_E, hH_E0, hSt'_rec]
  have hLR : ∀ i : ℕ, i ≤ L → lastRebuild q L i (k + 1) = k + 1 := fun i hi =>
    lastRebuild_eq_self_of_dvd ((chooseLevel_le_iff_dvd hq hi).mp (hj0 ▸ Nat.zero_le i))
  have hSnap : SnapInv G₀ L q mMax P sparsify us (k + 1) := by
    refine ⟨by rw [hst'_eq, hSt'_rec]; exact hq0, by rw [hst'_eq, hSt'_rec]; exact ht0,
      by rw [hst'_eq, hSt'_rec]; exact hG0,
      hst'_eq ▸ hSt'_H_valid, hst'_eq ▸ hSt'_H_V, hst'_eq ▸ hSt'_H_E_union, hst'_eq ▸ hSt'_H_sub,
      fun i => by rw [hst'_eq, hSt'_rec]; exact hHls0 i,
      fun i => by rw [hst'_eq, hSt'_rec]; exact hHlV0 i,
      ?_, ?_, ?_, ?_, by rw [hst'_eq, hSt'_rec]; exact hin0,
      fun i => by rw [hst'_eq, hSt'_rec]; exact hinsub0 i,
      ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      rw [hLR i.1 (Nat.le_of_lt_succ i.2), hst'_eq, hSt'_rec]
      exact (Finset.inter_eq_left.mpr (hHls0 i).2.1).symm
    · intro i; rw [hLR i.1 (Nat.le_of_lt_succ i.2), hst'_eq]
    · intro i
      rw [hLR i.1 (Nat.le_of_lt_succ i.2), hst'_eq, hSt'_rec]
      exact (Finset.inter_eq_left.mpr (hinsub0 i)).symm
    · intro i
      rw [hLR i.1 (Nat.le_of_lt_succ i.2), hst'_eq, hSt'_rec]
      have hdrop : (us.take (k + 1)).drop (k + 1) = [] := List.drop_eq_nil_of_le (by simp)
      rw [hdrop]
      simp [allTouched, res₀, initAt]
    · intro i hi
      rw [hLR i.1 (Nat.le_of_lt_succ i.2), hj0] at hi
      rw [hst'_eq, hSt'_rec]
      exact hinact0 i hi
    · intro i
      rw [hst'_eq, hSt'_rec]
      change ((res₀.state.H_level i).m : ℝ) ≤
        P.K_s * (G'.n : ℝ) * P.γ_ℓ * (1 + Real.log ((G'.n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s
      have hlog := log_mono_nm (activeSubgraph_n_le G') hG'm_le0 P.p_s
      have harg1 : (1 : ℝ) ≤ ((activeSubgraph G').n : ℝ) + (G'.m : ℝ) + 2 := by
        linarith [Nat.cast_nonneg (α := ℝ) (activeSubgraph G').n, Nat.cast_nonneg (α := ℝ) G'.m]
      have hl1 : 0 ≤ (1 + Real.log (((activeSubgraph G').n : ℝ) + (G'.m : ℝ) + 2)) ^ P.p_s :=
        pow_nonneg (by linarith [Real.log_nonneg harg1]) _
      have ha_le : ((activeSubgraph G').n : ℝ) ≤ (G'.n : ℝ) :=
        Nat.cast_le.mpr (activeSubgraph_n_le G')
      have hkn : 0 ≤ P.K_s * (G'.n : ℝ) * P.γ_ℓ :=
        mul_nonneg (mul_nonneg P.hK_s (Nat.cast_nonneg _)) hγl
      have hm1 : P.K_s * ((activeSubgraph G').n : ℝ) * P.γ_ℓ *
          (1 + Real.log (((activeSubgraph G').n : ℝ) + (G'.m : ℝ) + 2)) ^ P.p_s ≤
          P.K_s * (G'.n : ℝ) * P.γ_ℓ *
          (1 + Real.log (((activeSubgraph G').n : ℝ) + (G'.m : ℝ) + 2)) ^ P.p_s :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha_le P.hK_s) hγl) hl1
      exact le_trans (hHlsp0 i) (le_trans hm1 (mul_le_mul_of_nonneg_left hlog hkn))
    · intro i _
      have hpi : piLe (runState (L := L) G₀ q sparsify us (k + 1)) i.1 = piLe res₀.state i.1 := by
        rw [hst'_eq, hSt'_rec]; rfl
      have hug : unionGraphLt G' (runState (L := L) G₀ q sparsify us (k + 1)).H_level (i.1 + 1) =
          unionGraphLt G' res₀.state.H_level (i.1 + 1) := by rw [hst'_eq, hSt'_rec]
      rw [hpi, hug]; exact hemb0 i
    · intro i _
      have hpi : piLe (runState (L := L) G₀ q sparsify us (k + 1)) i.1 = piLe res₀.state i.1 := by
        rw [hst'_eq, hSt'_rec]; rfl
      rw [hpi]; exact hlen0 i
    · intro i _
      have hpi : piLe (runState (L := L) G₀ q sparsify us (k + 1)) i.1 = piLe res₀.state i.1 := by
        rw [hst'_eq, hSt'_rec]; rfl
      have hug : unionGraphLt G' (runState (L := L) G₀ q sparsify us (k + 1)).H_level (i.1 + 1) =
          unionGraphLt G' res₀.state.H_level (i.1 + 1) := by rw [hst'_eq, hSt'_rec]
      rw [hpi, hug]; exact hvc0 i
  have hUH_valid' : st.H.BatchIsValid res.UH := by
    rw [hUH_eq]
    simpa only [st, H_mid_union, res₀, uhPref, uhDel, uhIns, hdbG', ← hG'_eq] using hBV_uh
  have hUH_apply' : st.H.applyBatch res.UH = (runState (L := L) G₀ q sparsify us (k + 1)).H := by
    rw [hst'_eq, hSt'_rec]
  have hIns_eq : batchInsertCount res.UH = uhIns.length := by
    rw [hUH_eq, batchInsertCount_append, batchInsertCount_append]
    have h1 : batchInsertCount uhPref = 0 := (restrictUpdate_counts st.H u).1
    have h2 : batchInsertCount uhDel = 0 := batchInsertCount_map_delete _
    have h3 : batchInsertCount uhIns = uhIns.length := by
      dsimp only [uhIns]; rw [batchInsertCount_map_insert, List.length_map]
    omega
  have hDel_eq : batchDeleteCount res.UH = batchDeleteCount uhPref + uhDel.length := by
    rw [hUH_eq, batchDeleteCount_append, batchDeleteCount_append]
    have h2 : batchDeleteCount uhDel = uhDel.length := by
      dsimp only [uhDel]; rw [batchDeleteCount_map_delete, List.length_map]
    have h3 : batchDeleteCount uhIns = 0 := batchDeleteCount_map_insert _ _ _
    omega
  have hSp_le : batchSplitCount res.UH ≤ if isSplit u then 1 else 0 := by
    rw [hUH_eq, batchSplitCount_append, batchSplitCount_append]
    have h1 : batchSplitCount uhPref ≤ if isSplit u then 1 else 0 := (restrictUpdate_counts st.H u).2.2
    have h2 : batchSplitCount uhDel = 0 := batchSplitCount_map_delete _
    have h3 : batchSplitCount uhIns = 0 := batchSplitCount_map_insert _ _ _
    omega
  have hUH_len : res.UH.length ≤ st.G.updateEnc u + batchDeleteCount res.UH + batchInsertCount res.UH := by
    have hl : res.UH.length = uhPref.length + uhDel.length + uhIns.length := by
      rw [hUH_eq, List.length_append, List.length_append]
    have hp : uhPref.length ≤ st.G.updateEnc u := by simpa [uhPref] using hk_inv.G_eq ▸ hPref_enc
    omega
  refine ⟨hSnap, hUH_valid', hUH_apply', hst'_eq ▸ hD_eq ▸ le_rfl, hUH_len, hSp_le, fun _ => ?_,
    fun hlt => absurd hj0 (Nat.ne_of_gt hlt), fun hlt => absurd hj0 (Nat.ne_of_gt hlt)⟩
  have hIns_le : (batchInsertCount res.UH : ℝ) ≤ (res.state.H.E.card : ℝ) := by
    rw [hIns_eq, hSt'_H_E]
    have hle : uhIns.length ≤ res₀.state.H.E.card := by
      have hlen' : uhIns.length = (res₀.state.H.E \ H_mid_union.E).card := by
        simp [uhIns, H_mid_union, uhPref]
      rw [hlen']
      exact Finset.card_le_card Finset.sdiff_subset
    exact_mod_cast hle
  have hH_card_le : (res.state.H.E.card : ℝ) ≤
      P.K_s * ((activeSubgraph res.state.G).n : ℝ) * P.γ_ℓ *
      (1 + Real.log (((activeSubgraph res.state.G).n : ℝ) + (res.state.G.m : ℝ) + 2)) ^ P.p_s := by
    rw [hSt'_H_E]
    have hGe : res.state.G = G' := by rw [hSt'_rec]; exact hG0
    rw [hGe]
    have hHm : res₀.state.H.E.card = (res₀.state.H_level ⟨0, Nat.zero_lt_succ L⟩).m := by
      simp [res₀, initAt, MGraph.m]
    rw [hHm]
    exact hHlsp0 ⟨0, Nat.zero_lt_succ L⟩
  have hMid_le : H_mid_union.E.card ≤ st.H.m := by
    have hsub := isSubgraph_restrictUpdate hk_inv.H_sub hk_inv.H_V
      (hk_inv.G_eq ▸ hu_valid) hdu
    have hEeq : H_mid_union.E = st.H.E ∩ G'.E := by
      simpa [H_mid_union, uhPref, hG'_eq, hk_inv.G_eq] using hsub.2.2.2.1
    rw [hEeq]
    exact Finset.card_le_card Finset.inter_subset_left
  have hCost_le : (res.cost : ℝ) ≤ P.K_t * (((activeSubgraph res.state.G).n : ℝ) + (res.state.G.m : ℝ) * P.γ_ℓ ^ 2) *
      (1 + Real.log (((activeSubgraph res.state.G).n : ℝ) + (res.state.G.m : ℝ) + 2)) ^ P.p_t +
      (res.state.G.n : ℝ) + (res.state.G.m : ℝ) + 2 * (res.state.H.E.card : ℝ) +
      (res.state.G.m : ℝ) * lenBound P.γ_ℓ 0 + (L : ℝ) + 1 +
      ((L : ℝ) + 1) * (st.G.updateEnc u : ℝ) + 2 * (st.H.m : ℝ) +
      (res.UH.length : ℝ) + (res.D.card : ℝ) := by
    have hGe : res.state.G = G' := by rw [hSt'_rec]; exact hG0
    rw [hGe]
    have hc_eq : res.cost = res₀.cost + (L + 1) * st.G.updateEnc u + H_mid_union.E.card +
        res₀.state.H.E.card + res.UH.length + res.D.card := by
      rw [hUH_eq, hD_eq, hstep_un]
    rw [hc_eq]
    push_cast
    have hHm0 : (res₀.state.H.m : ℝ) = (res.state.H.E.card : ℝ) := by
      rw [MGraph.m, ← hSt'_H_E]
    have hHm1 : (res₀.state.H.E.card : ℝ) = (res.state.H.E.card : ℝ) := by rw [← hSt'_H_E]
    have hMid_r : (H_mid_union.E.card : ℝ) ≤ (st.H.m : ℝ) := Nat.cast_le.mpr hMid_le
    have hst_nn : (0 : ℝ) ≤ (st.H.m : ℝ) := Nat.cast_nonneg _
    linarith [hCost0, hHm0, hHm1, hMid_r, hst_nn]
  exact ⟨hIns_le, hH_card_le, by rw [hD_eq], hCost_le⟩

private theorem step_inv_rebuild {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (_hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k : ℕ} {u : Update} (hu_some : us[k]? = some u)
    (hPref : ∀ s ≤ k, SnapInv G₀ L q mMax P sparsify us s)
    (hj_pos : 0 < chooseLevel L q (k + 1)) :
    SnapInv G₀ L q mMax P sparsify us (k + 1) ∧ StepCostRecord G₀ L q P sparsify us k u := by
  have hγc : 0 ≤ P.γ_c := by linarith [P.hγ_c]
  have hγl : 0 ≤ P.γ_ℓ := by linarith [P.hγ_ℓ]
  have hk_inv := hPref k le_rfl
  let st := runState (L := L) G₀ q sparsify us k
  let res := runStepOut (L := L) G₀ q sparsify us k
  have hres_eq : res = step st u sparsify := by
    dsimp only [res, runStepOut]
    rw [hu_some]
  have hst'_eq : runState (L := L) G₀ q sparsify us (k + 1) = res.state := by
    dsimp only [runState, res, runStepOut]
    rw [hu_some]
  obtain ⟨hBV_take_k, hds_take_k, hU_valid⟩ := batchIsValid_take us G₀ k hBV hds
  obtain ⟨hu_valid, hdu⟩ := hU_valid u hu_some
  have htake_succ : us.take (k + 1) = us.take k ++ [u] := take_succ_of_getElem? hu_some
  have hInv_k := batch_delOrSplit_invariants (us.take k) G₀ hVG₀ hBV_take_k hds_take_k
  rcases hInv_k with ⟨hVGk, hEGk_sub, _, _, _, _, _⟩
  let Gk := G₀.applyBatch (us.take k)
  let G' := G₀.applyBatch (us.take (k + 1))
  have hG'_eq : G' = Gk.applyUpdate u := by
    simp [G', Gk, htake_succ, MGraph.applyBatch]
  have hVG' : G'.IsValid := hG'_eq ▸ isValid_applyUpdate_of_delOrSplit hVGk hu_valid hdu
  have hG'E_sub : G'.E ⊆ Gk.E := hG'_eq ▸ E_applyUpdate_subset hdu
  have hG'V_sup : Gk.V ⊆ G'.V := hG'_eq ▸ V_subset_applyUpdate hdu
  have hG'm_le0 : G'.m ≤ G₀.m := Finset.card_le_card (Finset.Subset.trans hG'E_sub hEGk_sub)
  let j := chooseLevel L q (k + 1)
  have hj_le : j ≤ L := chooseLevel_le L q (k + 1)
  have hj_ne : ¬ j = 0 := Nat.ne_of_gt hj_pos
  let r := lastRebuild q L (j - 1) (k + 1)
  have hr_not_dvd : ¬ phasePeriod q L (j - 1) ∣ (k + 1) :=
    not_dvd_of_lt_chooseLevel (Nat.sub_lt hj_pos Nat.one_pos)
  have hr_eq_k : r = lastRebuild q L (j - 1) k := lastRebuild_eq_of_not_dvd hr_not_dvd
  have hr_le_k : r ≤ k := hr_eq_k ▸ lastRebuild_le q L (j - 1) k
  have hInv_r := hPref r hr_le_k
  have hr_ch : chooseLevel L q r ≤ j - 1 :=
    lastRebuild_chooseLevel_le hq (le_trans (Nat.sub_le j 1) hj_le)
  let st_r := runState (L := L) G₀ q sparsify us r
  let G_r := G₀.applyBatch (us.take r)
  let delta := (us.take (k + 1)).drop r
  have htake_k1 : us.take (k + 1) = us.take r ++ delta := by
    have hkl : k + 1 ≤ us.length := by
      by_contra hgt
      have hnone : us[k]? = none := List.getElem?_eq_none (by omega)
      rw [hnone] at hu_some
      cases hu_some
    have hlen_r : r ≤ (us.take (k + 1)).length := by
      rw [List.length_take]
      omega
    have ht_eq : (us.take (k + 1)).take r = us.take r := by
      rw [List.take_take, min_eq_left (Nat.le_succ_of_le hr_le_k)]
    rw [← ht_eq]
    exact (List.take_append_drop r (us.take (k + 1))).symm
  have hBV_k1 : G₀.BatchIsValid (us.take (k + 1)) := (batchIsValid_take us G₀ (k + 1) hBV hds).1
  have hds_k1 : ∀ x ∈ us.take (k + 1), isDelOrSplit x := (batchIsValid_take us G₀ (k + 1) hBV hds).2.1
  rw [htake_k1, batchIsValid_append] at hBV_k1
  obtain ⟨hBV_r, hBV_d⟩ := hBV_k1
  have hds_d : ∀ x ∈ delta, isDelOrSplit x := fun x hx =>
    hds_k1 x (by rw [htake_k1]; exact List.mem_append_right _ hx)
  have hds_r : ∀ x ∈ us.take r, isDelOrSplit x := fun x hx =>
    hds_k1 x (by rw [htake_k1]; exact List.mem_append_left _ hx)
  have hVG_r : G_r.IsValid := (batch_delOrSplit_invariants (us.take r) G₀ hVG₀ hBV_r hds_r).1
  have hG_r_m : G_r.m ≤ mMax :=
    le_trans (Finset.card_le_card (batch_delOrSplit_invariants (us.take r) G₀ hVG₀ hBV_r hds_r).2.1) hGm₀
  have hG'_delta : G' = G_r.applyBatch delta := by simp [G', G_r, htake_k1, applyBatch_append]
  have hrk_eq_lt : ∀ {m : ℕ}, m < j →
      lastRebuild q L m (k + 1) = lastRebuild q L m k ∧
      lastRebuild q L m r = lastRebuild q L m k := fun {m} hm => by
    have hnd : ¬ phasePeriod q L m ∣ (k + 1) := not_dvd_of_lt_chooseLevel hm
    have h1 := lastRebuild_eq_of_not_dvd hnd
    have hm_le : lastRebuild q L m k ≤ r := by
      rw [hr_eq_k]
      exact lastRebuild_mono_level hq (Nat.le_pred_of_lt hm) (le_trans (Nat.sub_le j 1) hj_le)
    exact ⟨h1, lastRebuild_idempotent_le hq hm_le hr_le_k⟩
  let H_mid : Fin (L + 1) → MGraph := fun i => (st.H_level i).applyBatch (restrictUpdate u (st.H_level i))
  have hH_mid_props : ∀ i : Fin (L + 1),
      G'.IsSubgraph (H_mid i) ∧ (H_mid i).V = G'.V ∧
      (H_mid i).E = (st.H_level i).E ∩ G'.E := fun i => by
    have hr := isSubgraph_restrictUpdate (hk_inv.H_level_sub i) (hk_inv.H_level_V i) hu_valid hdu
    exact ⟨by simpa [H_mid, hG'_eq, hk_inv.G_eq] using hr.2.1,
      by simpa [H_mid, hG'_eq, hk_inv.G_eq] using hr.2.2.1,
      by simpa [H_mid, hG'_eq, hk_inv.G_eq] using hr.2.2.2.1⟩
  let H_lt := unionGraphLt G' H_mid j
  let H_lt_r := unionGraphLt G_r st_r.H_level j
  have hSub_lt_r : G_r.IsSubgraph H_lt_r := by
    refine ⟨Finset.Subset.rfl, ?_, fun _ _ => ⟨rfl, rfl⟩⟩
    intro e he
    simp only [H_lt_r, unionGraphLt, unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_univ, true_and] at he
    rcases he with ⟨i, _, hei⟩
    exact (hInv_r.H_level_sub i).2.1 hei
  have hHLt_E : H_lt.E = H_lt_r.E ∩ G'.E := by
    ext e
    simp only [H_lt, H_lt_r, unionGraphLt, unionEdgesLt, Finset.mem_inter, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hij, hei⟩
      rw [(hH_mid_props i).2.2, hk_inv.H_level_E i, ← (hrk_eq_lt hij).2] at hei
      have hei' := Finset.mem_inter.mp hei
      have hei1 := Finset.mem_inter.mp hei'.1
      have hei_r : e ∈ (st_r.H_level i).E := by
        rw [hInv_r.H_level_E i]
        exact Finset.mem_inter.mpr ⟨hei1.1,
          (batch_delOrSplit_invariants delta G_r hVG_r hBV_d hds_d).2.1 (hG'_delta ▸ hei'.2)⟩
      exact ⟨⟨i, hij, hei_r⟩, hei'.2⟩
    · rintro ⟨⟨i, hij, hei_r⟩, heG'⟩
      refine ⟨i, hij, ?_⟩
      rw [(hH_mid_props i).2.2, hk_inv.H_level_E i, ← (hrk_eq_lt hij).2]
      rw [hInv_r.H_level_E i, Finset.mem_inter] at hei_r
      exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hei_r.1, hG'E_sub heG'⟩, heG'⟩
  have hSub_lt : G'.IsSubgraph H_lt := by
    refine ⟨Finset.Subset.rfl, ?_, fun _ _ => ⟨rfl, rfl⟩⟩
    rw [hHLt_E]; exact Finset.inter_subset_right
  let inDom_mid : Fin (L + 1) → Finset ℕ := fun i => st.inDom i ∩ G'.E
  let piLt_mid : Embedding := piLtFrom st.Pi_level inDom_mid j
  let S_prev : Finset ℕ := st.S_level ⟨j - 1, by omega⟩ ∪ touchedVertices st.G u
  have hS_prev_eq : S_prev = allTouched G_r delta := by
    dsimp only [S_prev]
    rw [hk_inv.S_level_eq ⟨j - 1, by omega⟩, ← hr_eq_k]
    have hdrop_app : (us.take (k + 1)).drop r = (us.take k).drop r ++ [u] := by
      have hk_lt : k < us.length := by
        by_contra hle
        simp [List.getElem?_eq_none (Nat.le_of_not_lt hle)] at hu_some
      rw [htake_succ, List.drop_append_of_le_length]
      rw [List.length_take]; omega
    have hGapp : G_r.applyBatch ((us.take k).drop r) = Gk := by
      have htk : us.take k = us.take r ++ (us.take k).drop r := by
        have h1 : (us.take k).take r = us.take r := by rw [List.take_take, min_eq_left hr_le_k]
        rw [← h1]; exact (List.take_append_drop r (us.take k)).symm
      have hGk_eq : Gk = G_r.applyBatch ((us.take k).drop r) := by
        dsimp only [Gk, G_r]; conv_lhs => rw [htk]
        exact applyBatch_append G₀ (us.take r) ((us.take k).drop r)
      exact hGk_eq.symm
    dsimp only [delta]
    rw [hdrop_app, allTouched_append, hGapp]
    dsimp only [Gk, G_r]
    rw [hk_inv.G_eq]
    simp [allTouched]
  have hpi_eq : ∀ e ∈ G'.E, piLt_mid e = piLe st_r (j - 1) e := fun e heG' => by
    change piLtFrom st.Pi_level inDom_mid j e = piLtFrom st_r.Pi_level st_r.inDom ((j - 1) + 1) e
    have hsub1 : (j - 1) + 1 = j := Nat.sub_add_cancel hj_pos
    rw [hsub1]
    have h0_mid : e ∈ inDom_mid ⟨0, Nat.zero_lt_succ L⟩ := by
      dsimp only [inDom_mid]
      rw [Finset.mem_inter, hk_inv.inDom0]
      exact ⟨hG'E_sub heG', heG'⟩
    have h0_r : e ∈ st_r.inDom ⟨0, Nat.zero_lt_succ L⟩ := by
      rw [hInv_r.inDom0]
      exact (batch_delOrSplit_invariants delta G_r hVG_r hBV_d hds_d).2.1 (hG'_delta ▸ heG')
    have hcongr_in : ∀ m : Fin (L + 1), m.1 < j → (e ∈ inDom_mid m ↔ e ∈ st_r.inDom m) := by
      intro m hm
      have h1 := hk_inv.inDom_eq m
      have h2 := hInv_r.inDom_eq m
      rw [← (hrk_eq_lt hm).2] at h1
      have heGk : e ∈ Gk.E := hG'E_sub heG'
      have heGr : e ∈ G_r.E :=
        (batch_delOrSplit_invariants delta G_r hVG_r hBV_d hds_d).2.1 (hG'_delta ▸ heG')
      constructor
      · intro h
        rw [Finset.mem_inter] at h
        have h' : e ∈ st.inDom m := h.1
        rw [h1, Finset.mem_inter] at h'
        rw [h2]
        exact Finset.mem_inter.mpr ⟨h'.1, heGr⟩
      · intro h
        rw [h2, Finset.mem_inter] at h
        refine Finset.mem_inter.mpr ⟨?_, heG'⟩
        rw [h1]
        exact Finset.mem_inter.mpr ⟨h.1, heGk⟩
    obtain ⟨m₁, hm₁j, hm₁d, hm₁none, heq₁⟩ := piLtFrom_eq st.Pi_level inDom_mid hj_pos h0_mid
    obtain ⟨m₂, hm₂j, hm₂d, hm₂none, heq₂⟩ := piLtFrom_eq st_r.Pi_level st_r.inDom hj_pos h0_r
    have hm_eq : m₁ = m₂ := by
      by_contra hne
      rcases Nat.lt_or_lt_of_ne (fun h => hne (Fin.ext h)) with hlt | hlt
      · exact hm₁none m₂ hlt hm₂j ((hcongr_in m₂ hm₂j).mpr hm₂d)
      · exact hm₂none m₁ hlt hm₁j ((hcongr_in m₁ hm₁j).mp hm₁d)
    rw [heq₁, heq₂, hm_eq, hk_inv.Pi_level_eq m₂, ← (hrk_eq_lt hm₂j).2, hInv_r.Pi_level_eq m₂]
  have hj1_succ : (j - 1) + 1 = j := Nat.sub_add_cancel hj_pos
  have hEmbr := hInv_r.emb_at ⟨j - 1, by omega⟩ hr_ch
  have hLenr := hInv_r.len_at ⟨j - 1, by omega⟩ hr_ch
  have hVcr := hInv_r.vcong_at ⟨j - 1, by omega⟩ hr_ch
  dsimp only at hEmbr hLenr hVcr
  rw [hj1_succ] at hEmbr hVcr
  have hJV_sub : (buildProjGraph G' H_lt piLt_mid S_prev (affectedEdges G' H_lt piLt_mid S_prev)).V ⊆ G'.V :=
    hG'_delta ▸ projGraph_V_subset hVG_r hBV_d hds_d hSub_lt_r hEmbr
      (by simp [H_lt, unionGraphLt, hG'_delta]) (hG'_delta ▸ hHLt_E)
      (by simp [H_lt, unionGraphLt, hG'_delta]) (by simp [H_lt, unionGraphLt, hG'_delta])
      (hG'_delta ▸ hSub_lt) hS_prev_eq.symm.subset (fun e he => hpi_eq e (hG'_delta ▸ he))
  have hPW := projWalk_spec hSpec hVG_r hBV_d hds_d hG_r_m hSub_lt_r hEmbr hLenr hVcr
    (vcongBound_nonneg hγc hγl G₀.maxDeg (j - 1))
    (vcongBound_step P.hγ_c P.hγ_ℓ G₀.maxDeg (j - 1))
    (by simp [H_lt, unionGraphLt, hG'_delta]) (hG'_delta ▸ hHLt_E)
    (by simp [H_lt, unionGraphLt, hG'_delta]) (by simp [H_lt, unionGraphLt, hG'_delta])
    (hG'_delta ▸ hSub_lt) hS_prev_eq.symm.subset (fun e he => hpi_eq e (hG'_delta ▸ he))
  dsimp only at hPW
  rw [← hG'_delta] at hPW
  rcases hPW with ⟨hAff_card, hJm, hJn, hOut_aff, hSub_Hj, hHj_valid, hHnew_sub, _hHnew_V,
    hHnew_valid, hPinew_emb, hPinew_len, hPinew_vcong, hNonempty_bnd, hJH_edges, hEmpty_bnd, _hOut_emb,
    hAux_valid, hJ_valid, _, hEmbJH, hLenMid⟩
  let E_aff := affectedEdges G' H_lt piLt_mid S_prev
  let J := buildProjGraph G' H_lt piLt_mid S_prev E_aff
  let H_aux := buildAuxHost G' H_lt E_aff
  let embJH : Embedding := projWalk G' H_lt piLt_mid S_prev
  let out := if E_aff.Nonempty then sparsify H_aux J embJH else ⟨J, idEmb, 0⟩
  let outEmb : Embedding := fun e => shortcutWalk out.Jtilde (J.tail e) (out.emb e)
  let embMid : Embedding := Embedding.comp embJH outEmb
  let H_j : MGraph := { V := G'.V, E := out.Jtilde.E, tail := G'.tail, head := G'.head }
  let Pi_j : Embedding := reembedWalk G' H_lt piLt_mid embMid S_prev
  let H_level' : Fin (L + 1) → MGraph := fun i =>
    if i.1 < j then H_mid i
    else if i.1 = j then H_j
    else emptyGraphOn G'
  let Pi_level' : Fin (L + 1) → Embedding := fun i =>
    if i.1 < j then st.Pi_level i
    else if i.1 = j then Pi_j
    else fun _ => []
  let inDom' : Fin (L + 1) → Finset ℕ := fun i =>
    if i.1 < j then inDom_mid i
    else if i.1 = j then E_aff
    else ∅
  let S_level' : Fin (L + 1) → Finset ℕ := fun i =>
    if i.1 < j then (st.S_level i ∪ touchedVertices st.G u) else ∅
  let H_new_E := unionEdgesLt H_level' (L + 1)
  have hNewSub_G' : H_new_E ⊆ G'.E := by
    intro e he
    simp only [H_new_E, unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
      true_and] at he
    rcases he with ⟨i, _, hei⟩
    by_cases hij : i.1 < j
    · simp only [H_level', hij, ↓reduceIte] at hei
      exact (hH_mid_props i).1.2.1 hei
    · by_cases heq : i.1 = j
      · simp only [H_level', hij, ↓reduceIte] at hei
        simp only [heq, ↓reduceIte] at hei
        exact hSub_Hj.2.1 hei
      · simp [H_level', hij, heq, emptyGraphOn] at hei
  have hDB := diffBatch_spec hVGk (hk_inv.G_eq ▸ hk_inv.H_sub) hk_inv.H_V
    (hk_inv.G_eq ▸ hu_valid) hdu (hG'_eq ▸ hNewSub_G')
  dsimp only at hDB
  rcases hDB with ⟨hBV_uh, hVH'_valid, hSub_H', hV_H', hE_H', _hDel_len, hIns_len, hPref_enc⟩
  let uhPref := restrictUpdate u st.H
  let H_mid_union := st.H.applyBatch uhPref
  let uhDel := ((H_mid_union.E \ H_new_E).sort (· ≤ ·)).map Update.delete
  let uhIns := ((H_new_E \ H_mid_union.E).sort (· ≤ ·)).map
    fun e => Update.insert e (G'.tail e) (G'.head e)
  let uh := uhPref ++ uhDel ++ uhIns
  have hstep_un : res =
      { state :=
          { q := q, t := k + 1, G := G', H_level := H_level', Pi_level := Pi_level',
            inDom := inDom', S_level := S_level', H := st.H.applyBatch uh }
        UH := uh
        D := out.Jtilde.E.biUnion (fun e => walkEdges (embJH e))
        cost := (L + 1) * st.G.updateEnc u + S_prev.card + E_aff.card +
          (∑ e ∈ E_aff, ((piLt_mid e).length + (Pi_j e).length)) + out.cost +
          out.Jtilde.E.card + (∑ e ∈ out.Jtilde.E, (embJH e).length) + uh.length +
          (out.Jtilde.E.biUnion (fun e => walkEdges (embJH e))).card } := by
    have hst_eq := dynState_eq st hk_inv.q_eq hk_inv.t_eq hk_inv.G_eq
    have hgk_apply : (G₀.applyBatch (List.take k us)).applyUpdate u = G' := hG'_eq.symm
    rw [hres_eq]
    conv_lhs => rw [hst_eq]
    dsimp only [step]
    simp only [show ¬ chooseLevel L q (k + 1) = 0 from hj_ne, ↓reduceDIte, hgk_apply]
    rw [show G₀.applyBatch (List.take k us) = st.G from hk_inv.G_eq.symm]
  have hUH_eq : res.UH = uh := by rw [hstep_un]
  have hSt'_rec : res.state =
      { q := q, t := k + 1, G := G', H_level := H_level', Pi_level := Pi_level',
        inDom := inDom', S_level := S_level', H := st.H.applyBatch res.UH } := by
    rw [hUH_eq, hstep_un]
  have hD_eq : res.D = out.Jtilde.E.biUnion (fun e => walkEdges (embJH e)) := by rw [hstep_un]
  have hdbG' : (G₀.applyBatch (us.take k)).applyUpdate u = G' := hG'_eq.symm
  have hSt'_H_valid : res.state.H.IsValid := by
    rw [hSt'_rec, hUH_eq]
    simpa only [st, H_mid_union, uh, uhPref, uhDel, uhIns, hdbG'] using hVH'_valid
  have hSt'_H_V : res.state.H.V = G'.V := by
    rw [hSt'_rec, hUH_eq]
    simpa only [st, H_mid_union, uh, uhPref, uhDel, uhIns, hdbG'] using hV_H'
  have hSt'_H_E : res.state.H.E = H_new_E := by
    rw [hSt'_rec, hUH_eq]
    simpa only [st, H_mid_union, uh, uhPref, uhDel, uhIns, hdbG'] using hE_H'
  have hSt'_H_sub : G'.IsSubgraph res.state.H := by
    rw [hSt'_rec, hUH_eq]
    simpa only [st, H_mid_union, uh, uhPref, uhDel, uhIns, hdbG'] using hSub_H'
  have hSt'_H_level_sub : ∀ i : Fin (L + 1), G'.IsSubgraph (res.state.H_level i) := fun i => by
    rw [hSt'_rec]; dsimp only [H_level']
    split_ifs with h1 h2
    · exact (hH_mid_props i).1
    · exact hSub_Hj
    · exact ⟨Finset.Subset.rfl, Finset.empty_subset _, fun _ he => by simp [emptyGraphOn] at he⟩
  have hSt'_H_level_V : ∀ i : Fin (L + 1), (res.state.H_level i).V = G'.V := fun i => by
    rw [hSt'_rec]; dsimp only [H_level']
    split_ifs <;> first | exact (hH_mid_props i).2.1 | rfl
  have hLR_ge : ∀ {m : ℕ}, j ≤ m → m ≤ L → lastRebuild q L m (k + 1) = k + 1 := fun h1 h2 =>
    lastRebuild_eq_self_of_dvd ((chooseLevel_le_iff_dvd hq h2).mp h1)
  have hinDom0' : res.state.inDom ⟨0, Nat.zero_lt_succ L⟩ = G'.E := by
    rw [hSt'_rec]
    dsimp only [inDom', inDom_mid, st]
    change (if 0 < j then (runState G₀ q sparsify us k).inDom ⟨0, Nat.zero_lt_succ L⟩ ∩ G'.E
      else if 0 = j then E_aff else ∅) = G'.E
    simp only [show 0 < j from hj_pos, ↓reduceIte, hk_inv.inDom0]
    exact Finset.inter_eq_right.mpr hG'E_sub
  have hinDom_sub' : ∀ i : Fin (L + 1), res.state.inDom i ⊆ G'.E := fun i => by
    rw [hSt'_rec]; dsimp only [inDom']
    split_ifs
    · exact Finset.inter_subset_right
    · exact Finset.filter_subset _ _
    · exact Finset.empty_subset _
  have hUnion_eq_new_lt : unionEdgesLt res.state.H_level (j + 1) = H_lt.E ∪ H_j.E := by
    ext e
    simp only [unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, H_lt, unionGraphLt]
    constructor
    · rintro ⟨i, hij1, hei⟩
      rw [hSt'_rec] at hei; dsimp only [H_level'] at hei
      by_cases hij : i.1 < j
      · left; simp only [hij, ↓reduceIte] at hei
        exact ⟨i, hij, hei⟩
      · have heq : i.1 = j := by omega
        right; simpa [hij, heq] using hei
    · rintro (⟨i, hij, hei⟩ | he2)
      · refine ⟨i, Nat.lt_succ_of_lt hij, ?_⟩
        rw [hSt'_rec]; simp [H_level', hij, hei]
      · refine ⟨⟨j, Nat.lt_succ_of_le hj_le⟩, Nat.lt_succ_self j, ?_⟩
        rw [hSt'_rec]; simp [H_level', he2]
  have hinactive' : ∀ i : Fin (L + 1), chooseLevel L q (lastRebuild q L i.1 (k + 1)) < i.1 →
      res.state.inDom i = ∅ ∧ (res.state.H_level i).E = ∅ := fun i hi => by
    by_cases hij : i.1 < j
    · rw [(hrk_eq_lt hij).1] at hi
      obtain ⟨hiD, hiE⟩ := hk_inv.inactive i hi
      rw [hSt'_rec]
      dsimp only [inDom', H_level', inDom_mid]
      simp only [st, hij, ↓reduceIte, hiD, (hH_mid_props i).2.2, hiE, Finset.empty_inter, and_self]
    · by_cases heq : i.1 = j
      · exfalso
        rw [hLR_ge (Nat.le_of_eq heq.symm) (Nat.le_of_lt_succ i.2)] at hi
        exact Nat.lt_irrefl i.1 (heq ▸ hi)
      · rw [hSt'_rec]; simp [inDom', H_level', hij, heq, emptyGraphOn]
  have hH_level_spars' : ∀ i : Fin (L + 1), ((res.state.H_level i).m : ℝ) ≤
      P.K_s * (G'.n : ℝ) * P.γ_ℓ * (1 + Real.log ((G'.n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s := fun i => by
    by_cases hij : i.1 < j
    · have hm_le : (res.state.H_level i).m ≤ (st.H_level i).m := by
        rw [hSt'_rec]; simp only [H_level', hij, ↓reduceIte]
        rw [MGraph.m, (hH_mid_props i).2.2]
        exact Finset.card_le_card Finset.inter_subset_left
      have hn_le : Gk.n ≤ G'.n := Finset.card_le_card hG'V_sup
      have hlog := log_mono_nm hn_le (le_refl G₀.m) P.p_s
      have hprev := hk_inv.H_level_spars i
      have harg1 : (1 : ℝ) ≤ (Gk.n : ℝ) + (G₀.m : ℝ) + 2 := by
        linarith [Nat.cast_nonneg (α := ℝ) Gk.n, Nat.cast_nonneg (α := ℝ) G₀.m]
      have hl1 : 0 ≤ (1 + Real.log ((Gk.n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s :=
        pow_nonneg (by linarith [Real.log_nonneg harg1]) _
      have hkn : 0 ≤ P.K_s * (G'.n : ℝ) * P.γ_ℓ :=
        mul_nonneg (mul_nonneg P.hK_s (Nat.cast_nonneg _)) hγl
      have h1 : P.K_s * (Gk.n : ℝ) * P.γ_ℓ * (1 + Real.log ((Gk.n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s ≤
          P.K_s * (G'.n : ℝ) * P.γ_ℓ * (1 + Real.log ((G'.n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s :=
        le_trans
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hn_le) P.hK_s) hγl) hl1)
          (mul_le_mul_of_nonneg_left hlog hkn)
      exact le_trans (Nat.cast_le.mpr hm_le) (le_trans hprev h1)
    · by_cases heq : i.1 = j
      · have hm_eq : (res.state.H_level i).m = out.Jtilde.m := by
          rw [hSt'_rec]; simp [H_level', heq, H_j, MGraph.m]
        rw [hm_eq]
        by_cases hEne : E_aff.Nonempty
        · obtain ⟨_, hSpars_out, _⟩ := hNonempty_bnd hEne
          have hJn_le : J.n ≤ G'.n := Finset.card_le_card hJV_sub
          have hJm_le : J.m ≤ G₀.m := le_trans (Finset.card_le_card (Finset.filter_subset _ _)) hG'm_le0
          have hlog := log_mono_nm hJn_le hJm_le P.p_s
          have harg1 : (1 : ℝ) ≤ (J.n : ℝ) + (J.m : ℝ) + 2 := by
            linarith [Nat.cast_nonneg (α := ℝ) J.n, Nat.cast_nonneg (α := ℝ) J.m]
          have hl1 : 0 ≤ (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ P.p_s :=
            pow_nonneg (by linarith [Real.log_nonneg harg1]) _
          have hkn : 0 ≤ P.K_s * (G'.n : ℝ) * P.γ_ℓ :=
            mul_nonneg (mul_nonneg P.hK_s (Nat.cast_nonneg _)) hγl
          have h1 : P.K_s * (J.n : ℝ) * P.γ_ℓ * (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ P.p_s ≤
              P.K_s * (G'.n : ℝ) * P.γ_ℓ * (1 + Real.log ((G'.n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s :=
            le_trans
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hJn_le) P.hK_s) hγl) hl1)
              (mul_le_mul_of_nonneg_left hlog hkn)
          exact le_trans hSpars_out h1
        · rw [Finset.not_nonempty_iff_eq_empty] at hEne
          dsimp only [out]
          rw [MGraph.m, (hEmpty_bnd hEne).2, Finset.card_empty, Nat.cast_zero]
          have harg1 : (1 : ℝ) ≤ (G'.n : ℝ) + (G₀.m : ℝ) + 2 := by
            linarith [Nat.cast_nonneg (α := ℝ) G'.n, Nat.cast_nonneg (α := ℝ) G₀.m]
          have hΛ_nn : 0 ≤ (1 + Real.log ((G'.n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s :=
            pow_nonneg (by linarith [Real.log_nonneg harg1]) _
          exact mul_nonneg (mul_nonneg (mul_nonneg P.hK_s (Nat.cast_nonneg _)) hγl) hΛ_nn
      · have hm0 : (res.state.H_level i).m = 0 := by
          rw [hSt'_rec]; simp [H_level', hij, heq, emptyGraphOn, MGraph.m]
        rw [hm0, Nat.cast_zero]
        have harg1 : (1 : ℝ) ≤ (G'.n : ℝ) + (G₀.m : ℝ) + 2 := by
          linarith [Nat.cast_nonneg (α := ℝ) G'.n, Nat.cast_nonneg (α := ℝ) G₀.m]
        have hΛ_nn : 0 ≤ (1 + Real.log ((G'.n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s :=
          pow_nonneg (by linarith [Real.log_nonneg harg1]) _
        exact mul_nonneg (mul_nonneg (mul_nonneg P.hK_s (Nat.cast_nonneg _)) hγl) hΛ_nn
  let pi_new : Embedding := fun e => if e ∈ E_aff then Pi_j e else piLt_mid e
  have hPiLe_j_eq : ∀ e ∈ G'.E, piLe res.state j e = pi_new e := fun e heG' => by
    have he0 : e ∈ res.state.inDom ⟨0, Nat.zero_lt_succ L⟩ := hinDom0' ▸ heG'
    change piLtFrom res.state.Pi_level res.state.inDom (j + 1) e = _
    by_cases heAff : e ∈ E_aff
    · have hj_dom : e ∈ res.state.inDom ⟨j, Nat.lt_succ_of_le hj_le⟩ := by
        rw [hSt'_rec]; simp [inDom', heAff]
      obtain ⟨m, hmj, hmd, hm_none, heqm⟩ := piLtFrom_eq res.state.Pi_level res.state.inDom
        (Nat.succ_pos j) he0
      have hm_eq : m.1 = j := by
        apply le_antisymm (Nat.lt_succ_iff.mp hmj)
        by_contra hlt
        exact hm_none ⟨j, Nat.lt_succ_of_le hj_le⟩ (Nat.lt_of_not_le hlt) (Nat.lt_succ_self j) hj_dom
      rw [heqm, show m = ⟨j, Nat.lt_succ_of_le hj_le⟩ from Fin.ext hm_eq, hSt'_rec]
      simp [Pi_level', heAff, pi_new]
    · have hj_not : e ∉ res.state.inDom ⟨j, Nat.lt_succ_of_le hj_le⟩ := by
        rw [hSt'_rec]; simp [inDom', heAff]
      have hprev := piLtFrom_eq_prev_of_not_mem res.state.Pi_level res.state.inDom
        (j := ⟨j, Nat.lt_succ_of_le hj_le⟩) hj_pos he0 hj_not
      have hmid_congr : piLtFrom res.state.Pi_level res.state.inDom j e = piLt_mid e := by
        rw [hSt'_rec]
        obtain ⟨m, hmj, hmd, hm_none, heqm⟩ := piLtFrom_eq Pi_level' inDom' hj_pos
          (by simpa [hSt'_rec] using he0)
        have h0_st : e ∈ inDom_mid ⟨0, Nat.zero_lt_succ L⟩ := by
          dsimp only [inDom_mid]
          rw [Finset.mem_inter, hk_inv.inDom0]
          exact ⟨hG'E_sub heG', heG'⟩
        obtain ⟨m', hm'j, hm'd, hm'_none, heqm'⟩ := piLtFrom_eq st.Pi_level inDom_mid hj_pos h0_st
        have hmm' : m = m' := by
          by_contra hne
          rcases Nat.lt_or_lt_of_ne (fun h => hne (Fin.ext h)) with hlt | hlt
          · exact hm_none m' hlt hm'j (by simp only [inDom', show ↑m' < j from hm'j, ↓reduceIte]; exact hm'd)
          · exact hm'_none m hlt hmj (by simpa only [inDom', show ↑m < j from hmj, ↓reduceIte] using hmd)
        dsimp only [piLt_mid]
        rw [heqm, heqm', hmm']
        simp only [Pi_level', show ↑m' < j from hm'j, ↓reduceIte]
      rw [hprev, hmid_congr]
      simp [pi_new, heAff]
  have hPiLe_ge_eq : ∀ i : Fin (L + 1), chooseLevel L q (k + 1) ≤ i.1 →
      ∀ e ∈ G'.E, piLe res.state i.1 e = pi_new e := fun i hi e heG' => by
    have he0 : e ∈ res.state.inDom ⟨0, Nat.zero_lt_succ L⟩ := hinDom0' ▸ heG'
    have h1 := piLtFrom_eq_of_lt res.state.Pi_level res.state.inDom (Nat.succ_pos j)
      (Nat.succ_le_succ hi) he0 fun k hk1 _ => by
        rw [hSt'_rec]; simp [inDom', Nat.not_lt.mpr (Nat.le_of_succ_le hk1),
          Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hk1)]
    exact h1.trans (hPiLe_j_eq e heG')
  have hUE_ge : ∀ i : Fin (L + 1), chooseLevel L q (k + 1) ≤ i.1 →
      unionEdgesLt res.state.H_level (i.1 + 1) = H_lt.E ∪ H_j.E := fun i hi => by
    rw [← hUnion_eq_new_lt]
    exact unionEdgesLt_congr (Nat.succ_le_succ hi) fun m hm1 _ => by
      rw [hSt'_rec]; simp [H_level', Nat.not_lt.mpr (Nat.le_of_succ_le hm1),
        Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hm1), emptyGraphOn]
  have hEmb_all : ∀ i : Fin (L + 1), chooseLevel L q (k + 1) ≤ i.1 →
      Embedding.IsEmbedding (piLe res.state i.1) G' (unionGraphLt G' res.state.H_level (i.1 + 1)) :=
    fun i hi => by
      have hGcongr := isEmbedding_graph_congr (G := G')
        (H₁ := { V := G'.V, E := H_lt.E ∪ H_j.E, tail := G'.tail, head := G'.head })
        (H₂ := unionGraphLt G' res.state.H_level (i.1 + 1))
        rfl (hUE_ge i hi).symm (fun _ _ => rfl) (fun _ _ => rfl) hPinew_emb
      exact (isEmbedding_congr_eq (hPiLe_ge_eq i hi)).mpr hGcongr
  have hLen_all : ∀ i : Fin (L + 1), chooseLevel L q (k + 1) ≤ i.1 →
      (Embedding.length (piLe res.state i.1) G' : ℝ) ≤ lenBound P.γ_ℓ i.1 := fun i hi => by
    rw [length_congr_eq (hPiLe_ge_eq i hi)]
    exact le_trans (by simpa [hj1_succ] using hPinew_len) (lenBound_mono P.hγ_ℓ hi)
  have hVcong_all : ∀ i : Fin (L + 1), chooseLevel L q (k + 1) ≤ i.1 →
      Embedding.vcong (piLe res.state i.1) G' (unionGraphLt G' res.state.H_level (i.1 + 1)) (fun _ => 1) ≤
        vcongBound P.γ_c P.γ_ℓ G₀.maxDeg i.1 := fun i hi => by
    rw [vcong_congr_eq (hPiLe_ge_eq i hi)]
    have hEqVc := vcong_graph_congr (H₂ := unionGraphLt G' res.state.H_level (i.1 + 1))
      hVG' hHnew_valid rfl (hUE_ge i hi).symm (fun _ _ => rfl) (fun _ _ => rfl) hPinew_emb
    rw [← hEqVc]
    exact le_trans hPinew_vcong
      (vcongBound_mono P.hγ_c P.hγ_ℓ G₀.maxDeg (by rw [hj1_succ]; exact hi))
  have hSnap : SnapInv G₀ L q mMax P sparsify us (k + 1) := by
    refine ⟨by rw [hst'_eq, hSt'_rec], by rw [hst'_eq, hSt'_rec], by rw [hst'_eq, hSt'_rec],
      hst'_eq ▸ hSt'_H_valid, hst'_eq ▸ hSt'_H_V, by rw [hst'_eq, hSt'_H_E, hSt'_rec],
      hst'_eq ▸ hSt'_H_sub, fun i => hst'_eq ▸ hSt'_H_level_sub i, fun i => hst'_eq ▸ hSt'_H_level_V i,
      ?_, ?_, ?_, ?_, hst'_eq ▸ hinDom0', fun i => hst'_eq ▸ hinDom_sub' i,
      fun i hi => hst'_eq ▸ hinactive' i hi, fun i => hst'_eq ▸ hH_level_spars' i,
      fun i hi => by rw [hst'_eq]; exact hEmb_all i hi,
      fun i hi => by rw [hst'_eq]; exact hLen_all i hi,
      fun i hi => by rw [hst'_eq]; exact hVcong_all i hi⟩
    · intro i
      by_cases hij : i.1 < j
      · rw [hst'_eq, hSt'_rec, (hrk_eq_lt hij).1]
        dsimp only [H_level']
        simp only [hij, ↓reduceIte, (hH_mid_props i).2.2]
        dsimp only [st]
        rw [hk_inv.H_level_E i]
        ext e
        simp only [Finset.mem_inter]
        exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hG'E_sub h.2⟩, h.2⟩⟩
      · rw [hLR_ge (Nat.le_of_not_lt hij) (Nat.le_of_lt_succ i.2), hst'_eq]
        exact (Finset.inter_eq_left.mpr (hSt'_H_level_sub i).2.1).symm
    · intro i
      by_cases hij : i.1 < j
      · rw [hst'_eq, hSt'_rec, (hrk_eq_lt hij).1]
        dsimp only [Pi_level', st]
        simp only [hij, ↓reduceIte, hk_inv.Pi_level_eq i]
      · rw [hLR_ge (Nat.le_of_not_lt hij) (Nat.le_of_lt_succ i.2), hst'_eq]
    · intro i
      by_cases hij : i.1 < j
      · rw [hst'_eq, hSt'_rec, (hrk_eq_lt hij).1]
        dsimp only [inDom', inDom_mid, st]
        simp only [hij, ↓reduceIte, hk_inv.inDom_eq i]
        ext e
        simp only [Finset.mem_inter]
        exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hG'E_sub h.2⟩, h.2⟩⟩
      · rw [hLR_ge (Nat.le_of_not_lt hij) (Nat.le_of_lt_succ i.2), hst'_eq]
        exact (Finset.inter_eq_left.mpr (hinDom_sub' i)).symm
    · intro i
      by_cases hij : i.1 < j
      · have hdrop_app : (us.take (k + 1)).drop (lastRebuild q L i.1 k) =
            (us.take k).drop (lastRebuild q L i.1 k) ++ [u] := by
          have hk_lt : k < us.length := by
            by_contra hle
            have hnone : us[k]? = none := List.getElem?_eq_none (Nat.le_of_not_lt hle)
            rw [hnone] at hu_some; contradiction
          rw [htake_succ, List.drop_append_of_le_length]
          rw [List.length_take]; exact le_trans (lastRebuild_le q L i.1 k) (Nat.le_min.mpr ⟨le_rfl, Nat.le_of_lt hk_lt⟩)
        have hGapp : (G₀.applyBatch (us.take (lastRebuild q L i.1 k))).applyBatch
            ((us.take k).drop (lastRebuild q L i.1 k)) = Gk := by
          have htk : us.take k = us.take (lastRebuild q L i.1 k) ++
              (us.take k).drop (lastRebuild q L i.1 k) := by
            have h1 : (us.take k).take (lastRebuild q L i.1 k) = us.take (lastRebuild q L i.1 k) := by
              rw [List.take_take, min_eq_left (lastRebuild_le q L i.1 k)]
            rw [← h1]; exact (List.take_append_drop _ _).symm
          have hGk_eq : Gk = (G₀.applyBatch (us.take (lastRebuild q L i.1 k))).applyBatch
              ((us.take k).drop (lastRebuild q L i.1 k)) := by
            dsimp only [Gk]; conv_lhs => rw [htk]
            exact applyBatch_append _ _ _
          exact hGk_eq.symm
        rw [hst'_eq, hSt'_rec, (hrk_eq_lt hij).1, hdrop_app, allTouched_append, hGapp]
        dsimp only [S_level', st, Gk]
        simp only [hij, ↓reduceIte, hk_inv.S_level_eq i, hk_inv.G_eq, allTouched,
          Finset.union_empty]
      · rw [hLR_ge (Nat.le_of_not_lt hij) (Nat.le_of_lt_succ i.2), hst'_eq]
        have hdrop : (us.take (k + 1)).drop (k + 1) = [] := List.drop_eq_nil_of_le (by simp)
        rw [hdrop, hSt'_rec]
        simp [S_level', hij, allTouched]
  have hUH_valid' : st.H.BatchIsValid res.UH := by
    rw [hUH_eq]
    simpa only [st, H_mid_union, uh, uhPref, uhDel, uhIns, hdbG'] using hBV_uh
  have hUH_apply' : st.H.applyBatch res.UH = (runState (L := L) G₀ q sparsify us (k + 1)).H := by
    rw [hst'_eq, hSt'_rec]
  have hD_sub : res.D ⊆ (runState (L := L) G₀ q sparsify us (k + 1)).H.E := by
    rw [hst'_eq, hSt'_H_E, hD_eq]
    intro eD heD
    rw [Finset.mem_biUnion] at heD
    rcases heD with ⟨eJ, heJ, heWalk⟩
    rw [mem_walkEdges_iff] at heWalk
    rcases heWalk with ⟨x, hx, rfl⟩
    rcases hJH_edges eJ heJ x hx with hxLt | hxEq
    · have heUnion : x.1 ∈ unionEdgesLt res.state.H_level (j + 1) :=
        hUnion_eq_new_lt ▸ Finset.mem_union_left _ hxLt
      rw [hSt'_rec] at heUnion
      exact unionEdgesLt_mono H_level' (Nat.succ_le_succ hj_le) heUnion
    · have heUnion : x.1 ∈ unionEdgesLt res.state.H_level (j + 1) :=
        hUnion_eq_new_lt ▸ Finset.mem_union_right _ (hxEq ▸ heJ)
      rw [hSt'_rec] at heUnion
      exact unionEdgesLt_mono H_level' (Nat.succ_le_succ hj_le) heUnion
  have hIns_eq : batchInsertCount res.UH = uhIns.length := by
    rw [hUH_eq, batchInsertCount_append, batchInsertCount_append]
    have h1 : batchInsertCount uhPref = 0 := (restrictUpdate_counts st.H u).1
    have h2 : batchInsertCount uhDel = 0 := batchInsertCount_map_delete _
    have h3 : batchInsertCount uhIns = uhIns.length := by
      dsimp only [uhIns]; rw [batchInsertCount_map_insert, List.length_map]
    omega
  have hDel_eq : batchDeleteCount res.UH = batchDeleteCount uhPref + uhDel.length := by
    rw [hUH_eq, batchDeleteCount_append, batchDeleteCount_append]
    have h2 : batchDeleteCount uhDel = uhDel.length := by
      dsimp only [uhDel]; rw [batchDeleteCount_map_delete, List.length_map]
    have h3 : batchDeleteCount uhIns = 0 := batchDeleteCount_map_insert _ _ _
    omega
  have hSp_le : batchSplitCount res.UH ≤ if isSplit u then 1 else 0 := by
    rw [hUH_eq, batchSplitCount_append, batchSplitCount_append]
    have h1 : batchSplitCount uhPref ≤ if isSplit u then 1 else 0 := (restrictUpdate_counts st.H u).2.2
    have h2 : batchSplitCount uhDel = 0 := batchSplitCount_map_delete _
    have h3 : batchSplitCount uhIns = 0 := batchSplitCount_map_insert _ _ _
    omega
  have hUH_len : res.UH.length ≤ st.G.updateEnc u + batchDeleteCount res.UH + batchInsertCount res.UH := by
    have hl : res.UH.length = uhPref.length + uhDel.length + uhIns.length := by
      rw [hUH_eq, List.length_append, List.length_append]
    have hp : uhPref.length ≤ st.G.updateEnc u := by simpa [uhPref] using hk_inv.G_eq ▸ hPref_enc
    omega
  refine ⟨hSnap, hUH_valid', hUH_apply', hD_sub, hUH_len, hSp_le,
    fun h => absurd h (Nat.ne_of_gt hj_pos), fun _ => ?_, fun _ => ?_⟩
  on_goal 2 =>
    have hGu : st.G.applyUpdate u = G' := by rw [hG'_eq, hk_inv.G_eq]
    have hS2 : S_prev.card ≤ 2 * (k + 1 - r) := by
      have hkl : k + 1 ≤ us.length := (List.getElem?_eq_some_iff.mp hu_some).1
      have hdl : delta.length = k + 1 - r := by
        simp only [delta, List.length_drop, List.length_take]; omega
      rw [hS_prev_eq, ← hdl]; exact card_allTouched_le delta G_r
    have hpiL : ∀ e ∈ G'.E, ((piLt_mid e).length : ℝ) ≤ lenBound P.γ_ℓ (j - 1) := fun e heG' => by
      have heGr : e ∈ G_r.E :=
        (batch_delOrSplit_invariants delta G_r hVG_r hBV_d hds_d).2.1 (hG'_delta ▸ heG')
      rw [hpi_eq e heG']
      exact le_trans (Nat.cast_le.mpr (Finset.le_sup (f := fun e => (piLe st_r (j - 1) e).length)
        heGr)) hLenr
    have hAuxSub : G'.IsSubgraph (buildAuxHost G' H_lt (affectedEdges G' H_lt piLt_mid S_prev)) := by
      refine ⟨Finset.Subset.rfl, ?_, fun _ _ => ⟨rfl, rfl⟩⟩
      intro e he
      simp only [buildAuxHost, Finset.mem_union] at he
      rcases he with he | he
      · simp only [H_lt, unionGraphLt, unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter,
          Finset.mem_univ, true_and] at he
        obtain ⟨i, -, hei⟩ := he
        exact (hH_mid_props i).1.2.1 hei
      · exact (Finset.mem_filter.mp he).1
    dsimp only; rw [hGu]
    refine ⟨hS2, hAff_card, hpiL, hJn, Finset.card_le_card hJV_sub, hG'm_le0, hVG', hAux_valid,
      hJ_valid, hEmbJH, hAuxSub, fun hEne => ?_⟩
    have hEne' : (affectedEdges G' H_lt piLt_mid S_prev).Nonempty := hEne
    have hout_eq : out = sparsify H_aux J embJH := ite_eq_left hEne'
    obtain ⟨hL1, hJt1, _⟩ := hNonempty_bnd hEne
    simp only [ite_eq_left hEne'] at hJt1 hLenMid
    refine ⟨hL1, hJt1, hLenMid, fun e heAff => ?_⟩
    have hsup := Finset.le_sup (f := fun e => (pi_new e).length) (Finset.mem_filter.mp heAff).1
    have hlen_pi : (Embedding.length pi_new G' : ℝ) ≤ lenBound P.γ_ℓ j := by
      simpa only [pi_new, Pi_j, embMid, embJH, out, J, H_aux, E_aff, hj1_succ] using hPinew_len
    have heq : pi_new e = Pi_j e := ite_eq_left heAff
    rw [heq] at hsup
    simp only [Pi_j, embMid, outEmb, hout_eq] at hsup
    exact le_trans (Nat.cast_le.mpr hsup) hlen_pi
  have hres_G : res.state.G = G' := by rw [hSt'_rec]
  dsimp only
  rw [hres_G]
  set sLen := k + 1 - r
  set eaBound : ℝ := 2 * (sLen : ℝ) * vcongBound P.γ_c P.γ_ℓ G₀.maxDeg (j - 1)
  set Λ_s : ℝ := (1 + Real.log ((G'.n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s
  set Λ_t : ℝ := (1 + Real.log ((G'.n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_t
  set jtBound : ℝ := P.K_s * (2 * eaBound) * P.γ_ℓ * Λ_s
  have hdelta_len : delta.length = sLen := by
    simp only [delta, sLen, List.length_drop, List.length_take]
    have hkl : k + 1 ≤ us.length := by
      by_contra hgt
      have hnone : us[k]? = none := List.getElem?_eq_none (by omega)
      rw [hnone] at hu_some; contradiction
    omega
  have hS_card : S_prev.card ≤ 2 * sLen := by
    rw [hS_prev_eq, ← hdelta_len]; exact card_allTouched_le delta G_r
  have hS_card_r : (S_prev.card : ℝ) ≤ 2 * (sLen : ℝ) := by exact_mod_cast hS_card
  have hEaff_le : (E_aff.card : ℝ) ≤ eaBound :=
    le_trans hAff_card (mul_le_mul_of_nonneg_right hS_card_r
      (vcongBound_nonneg hγc hγl G₀.maxDeg (j - 1)))
  have hEa_nn : 0 ≤ eaBound :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (vcongBound_nonneg hγc hγl G₀.maxDeg (j - 1))
  have hargG' : (1 : ℝ) ≤ (G'.n : ℝ) + (G₀.m : ℝ) + 2 := by
    linarith [Nat.cast_nonneg (α := ℝ) G'.n, Nat.cast_nonneg (α := ℝ) G₀.m]
  have hΛs_ge1 : 1 ≤ Λ_s := one_le_pow₀ (by linarith [Real.log_nonneg hargG'])
  have hΛt_ge1 : 1 ≤ Λ_t := one_le_pow₀ (by linarith [Real.log_nonneg hargG'])
  have hJt_le : (out.Jtilde.E.card : ℝ) ≤ jtBound := by
    by_cases hEne : E_aff.Nonempty
    · obtain ⟨_, hSpars_out, _⟩ := hNonempty_bnd hEne
      have hJm_le : J.m ≤ G₀.m := le_trans (Finset.card_le_card (Finset.filter_subset _ _)) hG'm_le0
      have hJn_leG' : J.n ≤ G'.n := Finset.card_le_card hJV_sub
      have hJn_ea : (J.n : ℝ) ≤ 2 * eaBound := by
        have hJn_r : (J.n : ℝ) ≤ 2 * (E_aff.card : ℝ) := by exact_mod_cast hJn
        linarith
      have hlog := log_mono_nm hJn_leG' hJm_le P.p_s
      have harg1 : (1 : ℝ) ≤ (J.n : ℝ) + (J.m : ℝ) + 2 := by
        linarith [Nat.cast_nonneg (α := ℝ) J.n, Nat.cast_nonneg (α := ℝ) J.m]
      have hΛ_Jnn : 0 ≤ (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ P.p_s :=
        pow_nonneg (by linarith [Real.log_nonneg harg1]) _
      have hkn : 0 ≤ P.K_s * (2 * eaBound) * P.γ_ℓ :=
        mul_nonneg (mul_nonneg P.hK_s (by linarith)) hγl
      calc (out.Jtilde.E.card : ℝ) = (out.Jtilde.m : ℝ) := rfl
        _ ≤ P.K_s * (J.n : ℝ) * P.γ_ℓ * (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ P.p_s := hSpars_out
        _ ≤ P.K_s * (2 * eaBound) * P.γ_ℓ * (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ P.p_s :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJn_ea P.hK_s) hγl) hΛ_Jnn
        _ ≤ jtBound := mul_le_mul_of_nonneg_left hlog hkn
    · rw [Finset.not_nonempty_iff_eq_empty] at hEne
      rw [(hEmpty_bnd hEne).2, Finset.card_empty, CharP.cast_eq_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg P.hK_s (by linarith)) hγl) (by linarith [hΛs_ge1])
  have hIns_le_jt : (batchInsertCount res.UH : ℝ) ≤ jtBound := by
    have hNew_sub_uni : H_new_E ⊆ H_mid_union.E ∪ out.Jtilde.E := by
      intro e he
      simp only [H_new_E, unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
        true_and] at he
      rcases he with ⟨i, _, hei⟩
      rw [Finset.mem_union]
      by_cases hij : i.1 < j
      · left
        simp only [H_level', hij, ↓reduceIte] at hei
        rw [(hH_mid_props i).2.2] at hei
        have hsub := isSubgraph_restrictUpdate hk_inv.H_sub hk_inv.H_V
          (hk_inv.G_eq ▸ hu_valid) hdu
        have hE_mid : H_mid_union.E = st.H.E ∩ G'.E := by
          simpa [H_mid_union, uhPref, hG'_eq, hk_inv.G_eq] using hsub.2.2.2.1
        rw [hE_mid, hk_inv.H_E]
        refine Finset.mem_inter.mpr ⟨?_, (Finset.mem_inter.mp hei).2⟩
        simp only [unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨i, Nat.lt_succ_of_le (Nat.le_of_lt_succ i.2), (Finset.mem_inter.mp hei).1⟩
      · by_cases heq : i.1 = j
        · right; simpa [H_level', hij, heq, H_j] using hei
        · simp [H_level', hij, heq, emptyGraphOn] at hei
    have hsdiff_sub : H_new_E \ H_mid_union.E ⊆ out.Jtilde.E := fun e he =>
      (Finset.mem_union.mp (hNew_sub_uni (Finset.mem_sdiff.mp he).1)).resolve_left
        (Finset.mem_sdiff.mp he).2
    have hins_le : batchInsertCount res.UH ≤ out.Jtilde.E.card := by
      rw [hIns_eq]
      have hlen' : uhIns.length = (H_new_E \ H_mid_union.E).card := by
        simp [uhIns, H_mid_union, uhPref]
      rw [hlen']; exact Finset.card_le_card hsdiff_sub
    exact le_trans (Nat.cast_le.mpr hins_le) hJt_le
  have hEmbJH_le : ∀ e ∈ out.Jtilde.E, ((embJH e).length : ℝ) ≤ lenBound P.γ_ℓ (j - 1) + 1 :=
    fun e he => by
      obtain ⟨hL1, _⟩ := hNonempty_bnd ⟨e, hOut_aff he⟩
      exact le_trans (Nat.cast_le.mpr (Finset.le_sup (f := fun e => (embJH e).length) (hOut_aff he))) hL1
  have hReemb_le : ((∑ e ∈ out.Jtilde.E, (embJH e).length : ℕ) : ℝ) ≤
      jtBound * (lenBound P.γ_ℓ (j - 1) + 1) := by
    have hsum : (∑ e ∈ out.Jtilde.E, ((embJH e).length : ℝ)) ≤
        ∑ _ ∈ out.Jtilde.E, (lenBound P.γ_ℓ (j - 1) + 1) := Finset.sum_le_sum hEmbJH_le
    have hsum' : ((∑ e ∈ out.Jtilde.E, (embJH e).length : ℕ) : ℝ) ≤
        (out.Jtilde.E.card : ℝ) * (lenBound P.γ_ℓ (j - 1) + 1) := by
      calc ((∑ e ∈ out.Jtilde.E, (embJH e).length : ℕ) : ℝ)
          = ∑ e ∈ out.Jtilde.E, ((embJH e).length : ℝ) := by rw [Nat.cast_sum]
        _ ≤ ∑ _ ∈ out.Jtilde.E, (lenBound P.γ_ℓ (j - 1) + 1) := hsum
        _ = (out.Jtilde.E.card : ℝ) * (lenBound P.γ_ℓ (j - 1) + 1) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    exact le_trans hsum'
      (mul_le_mul_of_nonneg_right hJt_le (by linarith [lenBound_nonneg hγl (j - 1)]))
  have hD_card_le : (res.D.card : ℝ) ≤ jtBound * (lenBound P.γ_ℓ (j - 1) + 1) := by
    have hDc : res.D.card ≤ ∑ e ∈ out.Jtilde.E, (embJH e).length := by
      rw [hD_eq]
      exact le_trans Finset.card_biUnion_le
        (Finset.sum_le_sum fun e _ => walkEdges_card_le_length (embJH e))
    exact le_trans (Nat.cast_le.mpr hDc) hReemb_le
  have hAffWork_le : ((∑ e ∈ E_aff, ((piLt_mid e).length + (Pi_j e).length) : ℕ) : ℝ) ≤
      eaBound * (lenBound P.γ_ℓ (j - 1) + lenBound P.γ_ℓ j) := by
    have hterm : ∀ e ∈ E_aff,
        ((piLt_mid e).length : ℝ) + ((Pi_j e).length : ℝ) ≤
        lenBound P.γ_ℓ (j - 1) + lenBound P.γ_ℓ j := fun e heAff => by
      have heG' := (Finset.mem_filter.mp heAff).1
      have heGr : e ∈ G_r.E :=
        (batch_delOrSplit_invariants delta G_r hVG_r hBV_d hds_d).2.1 (hG'_delta ▸ heG')
      have h1 : ((piLt_mid e).length : ℝ) ≤ lenBound P.γ_ℓ (j - 1) := by
        rw [hpi_eq e heG']
        exact le_trans (Nat.cast_le.mpr (Finset.le_sup (f := fun e => (piLe st_r (j - 1) e).length) heGr)) hLenr
      have h2 : ((Pi_j e).length : ℝ) ≤ lenBound P.γ_ℓ j := by
        have heq : Pi_j e = pi_new e := by simp [pi_new, heAff]
        rw [heq]
        have hsup := Finset.le_sup (f := fun e => (pi_new e).length) heG'
        change (pi_new e).length ≤ Embedding.length pi_new G' at hsup
        have hlen_pi : (Embedding.length pi_new G' : ℝ) ≤ lenBound P.γ_ℓ j := by
          simpa only [pi_new, Pi_j, embMid, embJH, out, J, H_aux, E_aff, hj1_succ] using hPinew_len
        exact le_trans (Nat.cast_le.mpr hsup) hlen_pi
      exact add_le_add h1 h2
    have hsum : (∑ e ∈ E_aff, (((piLt_mid e).length : ℝ) + ((Pi_j e).length : ℝ))) ≤
        ∑ _ ∈ E_aff, (lenBound P.γ_ℓ (j - 1) + lenBound P.γ_ℓ j) := Finset.sum_le_sum hterm
    have hsum' : ((∑ e ∈ E_aff, ((piLt_mid e).length + (Pi_j e).length) : ℕ) : ℝ) ≤
        (E_aff.card : ℝ) * (lenBound P.γ_ℓ (j - 1) + lenBound P.γ_ℓ j) := by
      calc ((∑ e ∈ E_aff, ((piLt_mid e).length + (Pi_j e).length) : ℕ) : ℝ)
          = ∑ e ∈ E_aff, (((piLt_mid e).length : ℝ) + ((Pi_j e).length : ℝ)) := by
            rw [Nat.cast_sum]; refine Finset.sum_congr rfl fun e _ => ?_; push_cast; rfl
        _ ≤ ∑ _ ∈ E_aff, (lenBound P.γ_ℓ (j - 1) + lenBound P.γ_ℓ j) := hsum
        _ = (E_aff.card : ℝ) * (lenBound P.γ_ℓ (j - 1) + lenBound P.γ_ℓ j) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    exact le_trans hsum'
      (mul_le_mul_of_nonneg_right hEaff_le (add_nonneg (lenBound_nonneg hγl (j - 1)) (lenBound_nonneg hγl j)))
  have hOutCost_le : (out.cost : ℝ) ≤
      P.K_t * (2 * eaBound + eaBound * P.γ_ℓ ^ 2 * (lenBound P.γ_ℓ (j - 1) + 1)) * Λ_t := by
    by_cases hEne : E_aff.Nonempty
    · obtain ⟨_, _, hCost_out⟩ := hNonempty_bnd hEne
      have hJm_le : J.m ≤ G₀.m := le_trans (Finset.card_le_card (Finset.filter_subset _ _)) hG'm_le0
      have hJn_leG' : J.n ≤ G'.n := Finset.card_le_card hJV_sub
      have hJn_ea : (J.n : ℝ) ≤ 2 * eaBound := by
        have hJn_r : (J.n : ℝ) ≤ 2 * (E_aff.card : ℝ) := by exact_mod_cast hJn
        linarith
      have hJm_ea : (J.m : ℝ) ≤ eaBound := by rw [hJm]; exact hEaff_le
      have hlog := log_mono_nm hJn_leG' hJm_le P.p_t
      have harg1 : (1 : ℝ) ≤ (J.n : ℝ) + (J.m : ℝ) + 2 := by
        linarith [Nat.cast_nonneg (α := ℝ) J.n, Nat.cast_nonneg (α := ℝ) J.m]
      have hΛ_Jnn : 0 ≤ (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ P.p_t :=
        pow_nonneg (by linarith [Real.log_nonneg harg1]) _
      have hlnn : 0 ≤ lenBound P.γ_ℓ (j - 1) + 1 := by linarith [lenBound_nonneg hγl (j - 1)]
      have hinner : (J.n : ℝ) + (J.m : ℝ) * P.γ_ℓ ^ 2 * (lenBound P.γ_ℓ (j - 1) + 1) ≤
          2 * eaBound + eaBound * P.γ_ℓ ^ 2 * (lenBound P.γ_ℓ (j - 1) + 1) := by
        have := mul_le_mul_of_nonneg_right hJm_ea (mul_nonneg (sq_nonneg P.γ_ℓ) hlnn)
        linarith
      have h1 : P.K_t * ((J.n : ℝ) + (J.m : ℝ) * P.γ_ℓ ^ 2 * (lenBound P.γ_ℓ (j - 1) + 1)) *
          (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ P.p_t ≤
          P.K_t * (2 * eaBound + eaBound * P.γ_ℓ ^ 2 * (lenBound P.γ_ℓ (j - 1) + 1)) *
          (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ P.p_t :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinner P.hK_t) hΛ_Jnn
      have h2 : P.K_t * (2 * eaBound + eaBound * P.γ_ℓ ^ 2 * (lenBound P.γ_ℓ (j - 1) + 1)) *
          (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ P.p_t ≤
          P.K_t * (2 * eaBound + eaBound * P.γ_ℓ ^ 2 * (lenBound P.γ_ℓ (j - 1) + 1)) * Λ_t :=
        mul_le_mul_of_nonneg_left hlog (mul_nonneg P.hK_t (by positivity))
      exact le_trans hCost_out (le_trans h1 h2)
    · rw [Finset.not_nonempty_iff_eq_empty] at hEne
      rw [(hEmpty_bnd hEne).1, Nat.cast_zero]
      have hlnn : 0 ≤ lenBound P.γ_ℓ (j - 1) + 1 := by linarith [lenBound_nonneg hγl (j - 1)]
      exact mul_nonneg (mul_nonneg P.hK_t (by positivity)) (by linarith [hΛt_ge1])
  have hCost_eq : res.cost = (L + 1) * st.G.updateEnc u + S_prev.card + E_aff.card +
      (∑ e ∈ E_aff, ((piLt_mid e).length + (Pi_j e).length)) + out.cost + out.Jtilde.E.card +
      (∑ e ∈ out.Jtilde.E, (embJH e).length) + res.UH.length + res.D.card := by
    rw [hUH_eq, hD_eq, hstep_un]
  have hCost_le : (res.cost : ℝ) ≤ ((L : ℝ) + 1) * (st.G.updateEnc u : ℝ) + 2 * (sLen : ℝ) + eaBound +
      eaBound * (lenBound P.γ_ℓ (j - 1) + lenBound P.γ_ℓ j) +
      P.K_t * (2 * eaBound + eaBound * P.γ_ℓ ^ 2 * (lenBound P.γ_ℓ (j - 1) + 1)) * Λ_t +
      jtBound + jtBound * (lenBound P.γ_ℓ (j - 1) + 1) +
      (res.UH.length : ℝ) + (res.D.card : ℝ) := by
    rw [hCost_eq]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_sum] at hAffWork_le hReemb_le ⊢
    linarith [hS_card_r, hEaff_le, hAffWork_le, hOutCost_le, hJt_le, hReemb_le]
  exact ⟨hIns_le_jt, hD_card_le, hCost_le⟩

/-- Advance `SnapInv` and emit `StepCostRecord` from `k` to `k + 1` given `us[k]? = some u`. -/
theorem step_inv {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k : ℕ} {u : Update} (hu_some : us[k]? = some u)
    (hPref : ∀ s ≤ k, SnapInv G₀ L q mMax P sparsify us s) :
    SnapInv G₀ L q mMax P sparsify us (k + 1) ∧ StepCostRecord G₀ L q P sparsify us k u := by
  by_cases hj0 : chooseLevel L q (k + 1) = 0
  · exact step_inv_restart hVG₀ hq hGm₀ hSpec hBV hds hu_some (hPref k le_rfl) hj0
  · exact step_inv_rebuild hVG₀ hL hq hGm₀ hSpec hBV hds hu_some hPref (Nat.pos_of_ne_zero hj0)

private theorem runInv_prefix {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u) :
    ∀ k ≤ us.length,
      (∀ s ≤ k, SnapInv G₀ L q mMax P sparsify us s) ∧
      (∀ s < k, ∀ u, us[s]? = some u → StepCostRecord G₀ L q P sparsify us s u)
  | 0, _ =>
    ⟨fun s hs => by obtain rfl : s = 0 := Nat.le_zero.mp hs; exact init_inv hVG₀ hGm₀ hSpec us,
      fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1, hk => by
    obtain ⟨hPref_snap, hPref_rec⟩ :=
      runInv_prefix hVG₀ hL hq hGm₀ hSpec hBV hds k (Nat.le_of_lt hk)
    have hu_some : us[k]? = some (us[k]'hk) := List.getElem?_eq_getElem hk
    obtain ⟨hNext_snap, hNext_rec⟩ :=
      step_inv hVG₀ hL hq hGm₀ hSpec hBV hds hu_some hPref_snap
    refine ⟨fun s hs => ?_, fun s hs u hu => ?_⟩
    · rcases Nat.lt_or_eq_of_le hs with hlt | rfl
      · exact hPref_snap s (Nat.lt_succ_iff.mp hlt)
      · exact hNext_snap
    · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hs) with hlt | rfl
      · exact hPref_rec s hlt u hu
      · rw [hu_some] at hu
        cases hu
        exact hNext_rec

/-- Main invariant: for all `k ≤ us.length`, both `SnapInv` at `k` and `StepCostRecord` at all
steps `< k` hold. -/
theorem runInv_all {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u) :
    ∀ k ≤ us.length,
      SnapInv G₀ L q mMax P sparsify us k ∧
      (∀ s < k, ∀ u, us[s]? = some u → StepCostRecord G₀ L q P sparsify us s u) :=
  fun k hk =>
    let h := runInv_prefix hVG₀ hL hq hGm₀ hSpec hBV hds k hk
    ⟨h.1 k le_rfl, h.2⟩

end

end Transition

end MinCostFlow.DynSpanner
