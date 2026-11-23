module

public import MinCostFlow.Expander.DecomposeLevelCommon
public import MinCostFlow.Expander.DecomposeLevelSetup
public import MinCostFlow.Expander.DecomposeLevelPart

import Mathlib.Tactic.Linarith

/-!
# Single-Level Word-RAM Procedure for Expander Decomposition

Implements `levelProc` and proves `level_runs` (Theorem 8.5 / Algorithm 5, single recursive
level `lvl ∈ {ℓ, ..., 1}`):
1. Loads `curN, curM` and computes `csrAddr, qAddr, lblAddr`.
2. Builds the twin graph (`buildTwinStmt`) and runs `[B1]` on it (`twinDecompStmt`).
3. Clears `keptVert[0..curN)` (`zeroKeptStmt`), groups vertices (`b_gv`), normalizes
   `grpSameTwin` to `{0, 1}` (`normSameTwinStmt`), and groups edges (`b_ge`).
4. Loops `q = 0..k-1` calling `b_part`, emitting non-empty kept expanders `R_q` (`2 ≤ |R_q|`)
   into the arena (`statePtr`), and marks kept vertices in `keptVert`.
5. Partitions edges into `(nextGAddr, nextIdxAddr)` and updates `lvlArr` (`splitEdgesStmt`).
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner


/-! ## 5. Complete `level_runs` Theorem -/

lemma level_runs {w : ℕ} {p : Program} {b_run b_csr b_bfs b_gv b_ge b_part b_prune thr : ℕ}
    {P_cited : Program} {c_cited : ℕ} {φ_cited : ℝ}
    (mem₀ : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) (curG : Cited.Graph) (curIdx : List ℕ)
    (curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
      keptVertAddr statePtr lvl D D_phi mCap zeroCursor arena₀ total₀ c_cited_ub : ℕ)
    (hV : curG.IsValid) (hL : curG.IsLoopless) (h1n : 1 ≤ curG.n)
    (h1lvl : 1 ≤ lvl) (hD_eq : D = 2 ^ lvl)
    (hm_le_D : curG.m ≤ D * curG.n) (_hm_le_mCap : curG.m ≤ mCap) (h200 : 200 ≤ D_phi)
    (hga : GraphAt mem₀ curGAddr curG)
    (hidx_len : curIdx.length = curG.m) (hidx_pw : curIdx.Pairwise (· < ·))
    (hidx_lt : ∀ a ∈ curIdx, a < mCap) (hidx_list : ListAt mem₀ curIdxAddr curIdx)
    (hstate_0 : mem₀ statePtr = arena₀) (hstate_1 : mem₀ (statePtr + 1) = zeroCursor)
    (hstate_2 : mem₀ (statePtr + 2) = total₀) (hzf : ZeroFrom mem₀ zeroCursor)
    (h_csr : MeetsContract w p b_csr (buildCsrContract w))
    (h_bfs : MeetsContract w p b_bfs (bfsLabelsContract w))
    (h_run : p.HasAt b_run (runner (stripRandProg P_cited) c_cited b_run))
    (h_gv : MeetsContract w p b_gv (groupVertsContract w))
    (h_ge : MeetsContract w p b_ge (groupEdgesContract w))
    (h_part : p.procs[b_part]? = some (partPruneProc b_csr b_prune))
    (h_prune : p.procs[b_prune]? = some pruneWrapProc)
    (hcited : thr ≤ curG.m + D * curG.n →
      ∃ out cost_c,
        RunsTo (wordSize c_cited ((twinGraph D curG).encode ++ [1, 200, rOf (curG.m + D * curG.n)]))
          P_cited ((twinGraph D curG).encode ++ [1, 200, rOf (curG.m + D * curG.n)]) (fun _ => false)
          out cost_c ∧
        IsExpanderDecomposition (twinGraph D curG) (1 / 200) φ_cited out ∧
        1 / (D_phi : ℝ) ≤ φ_cited ∧ cost_c ≤ c_cited_ub)
    (hthr_Dphi : thr + 1 ≤ D_phi) (hthr_w : thr < 2 ^ w)
    (hs_lvl : statePtr + 3 ≤ lvlArrAddr)
    (hdj : SplitDisjoint curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr bufAddr keptVertAddr
      curG.n curG.m mCap)
    (hcg_tw : curGAddr + 2 + 2 * curG.m ≤ twAddr)
    (_hci_tw : curIdxAddr + curG.m ≤ twAddr)
    (_hng_tw : nextGAddr + 2 + 2 * curG.m ≤ twAddr)
    (_hni_tw : nextIdxAddr + curG.m ≤ twAddr)
    (hlbl_buf : twAddr + 6 + 6 * curG.n + 6 * (curG.m + D * curG.n) + 2 * curG.n ≤ bufAddr)
    (hbuf_work : bufAddr + groupBufSize curG.n curG.m ≤ workAddr)
    (hwork_kept : workAddr + partWorkSize curG.n curG.m
      (4 * (4 * D_phi + 2) * (Nat.log 2 (2 * curG.m + 1) + 1) + 2) ≤ keptVertAddr)
    (hkept_arena : keptVertAddr + curG.n ≤ arena₀)
    (harena_zc : arena₀ + 4 * curG.m ≤ zeroCursor)
    (harena_w : arena₀ + 4 * curG.m + 2 + curG.n < 2 ^ w)
    (hlog_w : Nat.log 2 (curG.m + D * curG.n) + 1 < 2 ^ w)
    (hrOf_w : (rOf (curG.m + D * curG.n) + 1) ^ 3 < 2 ^ w)
    (h201_w : 201 ≤ 2 ^ w)
    (hzero_w : zeroCursor < 2 ^ w)
    (hrun_w : thr ≤ curG.m + D * curG.n →
      zeroCursor + 2 * curG.n +
        2 ^ (wordSize c_cited ((twinGraph D curG).encode ++ [1, 200, rOf (curG.m + D * curG.n)]) + 1) + 2 ≤ 2 ^ w)
    (hword_part : 8 * (4 * D_phi + 2) * curG.m + 4 * (4 * D_phi + 2) + 2 * curG.n + 2 * curG.m +
      (4 * (4 * D_phi + 2) * (Nat.log 2 (2 * curG.m + 1) + 1) + 2) + 16 < 2 ^ w)
    (hword_D : 2 * curG.m * D_phi + D + 4 < 2 ^ w)
    (hword_Dphi : D + 3 * D_phi < 2 ^ w)
    (hlvl_w : lvl < 2 ^ w) (hmCap_w : mCap < 2 ^ w) (htot_w : total₀ + curG.n < 2 ^ w)
    (hargs_w : ∀ a ∈ [curGAddr, curIdxAddr, nextGAddr, nextIdxAddr, lvlArrAddr, twAddr, bufAddr,
      workAddr, keptVertAddr, statePtr, lvl, D, D_phi, mCap], a < 2 ^ w) :
    let args := [curGAddr, curIdxAddr, nextGAddr, nextIdxAddr, lvlArrAddr, twAddr, bufAddr,
      workAddr, keptVertAddr, statePtr, lvl, D, D_phi, mCap]
    ∃ st' c arena₁ zeroCursor', ∃ rawComps_lvl : List (ℕ × List ℕ), ∃ validRs : List (Finset ℕ),
      ∃ remG Gi : Cited.Graph, ∃ remIdx keptIdx : List ℕ, ∃ keptFlag : ℕ → Bool,
      Runs w p ω (levelProc b_run b_csr b_bfs b_gv b_ge b_part thr)
        (startState args mem₀ pos) (.returned 0) st' c ∧
      arena₀ ≤ arena₁ ∧ arena₁ ≤ arena₀ + 4 * curG.m ∧
      st'.mem statePtr = arena₁ ∧
      st'.mem (statePtr + 1) = zeroCursor' ∧
      st'.mem (statePtr + 2) = total₀ + rawComps_lvl.length ∧
      ZeroFrom st'.mem zeroCursor' ∧
      zeroCursor ≤ zeroCursor' ∧
      zeroCursor' ≤ (if thr ≤ curG.m + D * curG.n then
        zeroCursor + 1 + 2 ^ (wordSize c_cited ((twinGraph D curG).encode ++ [1, 200, rOf (curG.m + D * curG.n)]))
        else zeroCursor) ∧
      ListAt st'.mem arena₀ (rawComps_lvl.flatMap compRecord) ∧
      arena₁ = arena₀ + (rawComps_lvl.flatMap compRecord).length ∧
      rawComps_lvl.map (fun comp => comp.2.toFinset) = validRs ∧
      (∀ comp ∈ rawComps_lvl, comp.1 = lvl ∧ List.Pairwise (· < ·) comp.2 ∧ 2 ≤ comp.2.length) ∧
      Gi.n = curG.n ∧ remG.n = curG.n ∧
      Gi.IsValid ∧ Gi.IsLoopless ∧ remG.IsValid ∧ remG.IsLoopless ∧
      (Gi.edges ++ remG.edges).Perm curG.edges ∧
      Gi.m ≤ 2 ^ lvl * curG.n ∧ remG.m ≤ 2 ^ (lvl - 1) * curG.n ∧
      validRs.Pairwise Disjoint ∧
      (∀ R ∈ validRs, R ⊆ curG.verts ∧ 2 ≤ R.card ∧
        Gi.IsConductanceExpanderOn R (1 / (3 * (D_phi : ℝ))) ∧
        (∀ x ∈ R, (1 : ℝ) / (3 * (D_phi : ℝ)) * (2 : ℝ) ^ lvl ≤ (Gi.degIn R x : ℝ)) ∧
        (∀ e ∈ Gi.edges, e.1 ∈ R ↔ e.2 ∈ R)) ∧
      (∀ e ∈ Gi.edges, ∃ R ∈ validRs, e.1 ∈ R ∧ e.2 ∈ R) ∧
      GraphAt st'.mem nextGAddr remG ∧
      ListAt st'.mem nextIdxAddr remIdx ∧
      remIdx.length = remG.m ∧ remIdx.Nodup ∧ remIdx.Pairwise (· < ·) ∧ (∀ a ∈ remIdx, a < mCap) ∧
      keptIdx.length = Gi.m ∧ keptIdx.Nodup ∧ keptIdx.Pairwise (· < ·) ∧ (∀ a ∈ keptIdx, a < mCap) ∧
      remG.edges = ((List.range curG.m).filter fun t => !keptFlag t).map (fun t => curG.edges.getD t (0, 0)) ∧
      remIdx = ((List.range curG.m).filter fun t => !keptFlag t).map (fun t => curIdx.getD t 0) ∧
      Gi.edges = ((List.range curG.m).filter fun t => keptFlag t).map (fun t => curG.edges.getD t (0, 0)) ∧
      keptIdx = ((List.range curG.m).filter fun t => keptFlag t).map (fun t => curIdx.getD t 0) ∧
      (∀ a < mCap, st'.mem (lvlArrAddr + a) = if a ∈ keptIdx then lvl else mem₀ (lvlArrAddr + a)) ∧
      (∀ a < zeroCursor, ¬ (statePtr ≤ a ∧ a < statePtr + 3) →
        ¬ (lvlArrAddr ≤ a ∧ a < lvlArrAddr + mCap) →
        ¬ (nextGAddr ≤ a ∧ a < nextGAddr + 2 + 2 * curG.m) →
        ¬ (nextIdxAddr ≤ a ∧ a < nextIdxAddr + curG.m) →
        ¬ (twAddr ≤ a ∧ a < keptVertAddr + curG.n) →
        ¬ (arena₀ ≤ a ∧ a < arena₁) →
        st'.mem a = mem₀ a) ∧
      c ≤ levelCost curG.n curG.m D D_phi c_cited_ub (runnerScale P_cited)
        (wordSize c_cited ((twinGraph D curG).encode ++ [1, 200, rOf (curG.m + D * curG.n)])) := by
  dsimp only
  have h1D : 1 ≤ D := by rw [hD_eq]; exact Nat.one_le_two_pow
  have hidx_nd : curIdx.Nodup := hidx_pw.imp fun hab => Nat.ne_of_lt hab
  obtain ⟨hlvl_cg, hlvl_ci, hlvl_ng, hlvl_ni, hcg_buf, hci_buf, hng_buf, hni_buf,
    hcg_ng, hcg_ni, hci_ng, hci_ni, hng_ni, _⟩ := id hdj
  have hbuf_sz : groupBufSize curG.n curG.m = 12 * curG.n + 2 * curG.m + 2 := rfl
  rw [hbuf_sz] at hbuf_work
  have hs_cg : statePtr + 3 ≤ curGAddr := by omega
  have hs_tw : statePtr + 3 ≤ twAddr := by omega
  have hkept_w_addr : keptVertAddr + curG.n < 2 ^ w := by omega
  have hpw2 : 2 ≤ partWorkSize curG.n curG.m
      (4 * (4 * D_phi + 2) * (Nat.log 2 (2 * curG.m + 1) + 1) + 2) := by
    simp [partWorkSize, pruneWorkSpace]; omega
  have hbuf_w : bufAddr + groupBufSize curG.n curG.m + 2 < 2 ^ w := by omega
  have hbuf_kept : bufAddr + groupBufSize curG.n curG.m ≤ keptVertAddr := by
    rw [hbuf_sz]; omega
  have hzero_lo : keptVertAddr + curG.n ≤ zeroCursor := by omega
  -- Stage 1: `levelSetupPrefix`
  obtain ⟨st₁, c₁, k, label, φ_B1, hr₁, hlvl₁, hr₁_20, hk1, hkn, hlbl_len, hphi_ge, hexpDec,
    hzf₁, hzc_le, hzc_ub, hfr₁, hkept0, hgrp, hsame, hpid, huniq_pw, hpo0, hcnt_sum, hpo_step,
    heo0, hecnt_sum, heo_step, hc₁⟩ :=
    levelSetupPrefix_runs mem₀ pos ω curG curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr
      twAddr bufAddr workAddr keptVertAddr statePtr lvl D D_phi mCap zeroCursor c_cited_ub
      hV h1n h1D hga hstate_1 hzf h_csr h_bfs h_run h_gv h_ge hcited hthr_Dphi hthr_w hs_cg
      hcg_tw hkept_w_addr hlog_w hrOf_w h201_w hlbl_buf hbuf_w hbuf_kept hzero_lo hzero_w
      hrun_w hargs_w
  set m_tw := curG.m + D * curG.n
  set csrAddr := twAddr + 5 + 2 * m_tw
  set qAddr := csrAddr + 4 * curG.n + 1 + 4 * m_tw
  set lblAddr := qAddr + 2 * curG.n
  set zeroCursor' := st₁.mem (statePtr + 1)
  have hlt_tw_eq : ∀ a < twAddr, a ≠ statePtr + 1 → st₁.mem a = mem₀ a := fun a ha hne => by
    apply hfr₁ a (by omega) (by omega) (by omega) (by omega) (by omega) hne
  have hga₁ : GraphAt st₁.mem curGAddr curG := by
    have heq : ∀ a, curGAddr ≤ a → a < curGAddr + 2 + 2 * curG.m → st₁.mem a = mem₀ a :=
      fun a ha1 ha2 => hlt_tw_eq a (by omega) (by omega)
    exact graphAt_of_cells
      (by rw [heq _ (le_refl _) (by omega)]; exact graphAt_n hga)
      (by rw [heq _ (by omega) (by omega)]; exact graphAt_m hga)
      (fun t ht => ⟨
        by rw [heq _ (by omega) (by omega)]; exact graphAt_edge_fst hga ht,
        by rw [heq _ (by omega) (by omega)]; exact graphAt_edge_snd hga ht⟩)
  have hst₁_ptr0 : st₁.mem statePtr = arena₀ := by
    rw [hlt_tw_eq statePtr (by omega) (by omega)]; exact hstate_0
  have hst₁_ptr2 : st₁.mem (statePtr + 2) = total₀ := by
    rw [hlt_tw_eq (statePtr + 2) (by omega) (by omega)]; exact hstate_2
  -- Stage 2: `level_partLoop_runs`
  obtain ⟨st₂, c₂, arena₁, Rs, rawComps_lvl, hr₂, hlvl₂, ha0_le, ha_ub, hst₂_ptr0, hst₂_ptr1,
    hst₂_ptr2, hlist_ar, hptr_eq, hrc_map, hrc_mem, hRs_len, hRs_disj, hRs_spec, hkept_inv,
    hfr₂, hc₂⟩ :=
    level_partLoop_runs st₁.mem ω curG curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr
      twAddr bufAddr workAddr keptVertAddr statePtr lvl D D_phi mCap csrAddr qAddr lblAddr
      zeroCursor' arena₀ total₀ k label φ_B1 st₁ hV hL h1D h200 hphi_ge hexpDec hga₁ h_csr
      h_part h_prune hlvl₁ rfl hr₁_20 hk1 hkn hst₁_ptr0 rfl hst₁_ptr2 hkept0 hgrp hsame hpid
      hpo0 hcnt_sum hpo_step heo0 hecnt_sum heo_step hs_cg (by omega) hbuf_w hbuf_work
      hwork_kept hkept_arena (by omega) harena_w hword_part hword_D hword_Dphi hlvl_w htot_w
      (by omega)
  -- Frame properties of `st₂.mem` before `splitEdgesStmt`
  have hga₂ : GraphAt st₂.mem curGAddr curG := by
    have heq : ∀ a, curGAddr ≤ a → a < curGAddr + 2 + 2 * curG.m → st₂.mem a = st₁.mem a :=
      fun a ha1 ha2 => hfr₂ a (by omega) (by omega) (by omega) (by omega) (by omega)
    exact graphAt_of_cells
      (by rw [heq _ (le_refl _) (by omega)]; exact graphAt_n hga₁)
      (by rw [heq _ (by omega) (by omega)]; exact graphAt_m hga₁)
      (fun t ht => ⟨
        by rw [heq _ (by omega) (by omega)]; exact graphAt_edge_fst hga₁ ht,
        by rw [heq _ (by omega) (by omega)]; exact graphAt_edge_snd hga₁ ht⟩)
  have hidx₂ : ListAt st₂.mem curIdxAddr curIdx := fun t ht => by
    rw [hfr₂ _ (by omega) (by omega) (by omega) (by omega) (by omega), hlt_tw_eq _ (by omega) (by omega)]
    exact hidx_list t ht
  set partId : ℕ → ℕ := fun u => st₁.mem (bufAddr + 3 * curG.n + u)
  set kept : ℕ → ℕ := fun u => st₂.mem (keptVertAddr + u)
  have hpart₂_read : ∀ u < curG.n, st₂.mem (bufAddr + 3 * curG.n + u) = partId u := fun u hu => by
    apply hfr₂ _ (by omega) (by omega) (by omega) (by omega) (by omega)
  have hpart_w : ∀ u < curG.n, partId u < 2 ^ w := fun u hu => by
    have hlt := (hpid u hu).1
    have hbuf_3n : bufAddr + 3 * curG.n + u < 2 ^ w := by
      have := hbuf_w; simp [groupBufSize] at this; omega
    dsimp [partId]; change st₁.mem (grpPartId bufAddr curG.n + u) < 2 ^ w
    omega
  -- Stage 3: `splitEdgesStmt`
  have hsp := splitEdges_triple p st₂.mem curG curIdx partId kept
    curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr keptVertAddr
    statePtr lvl D D_phi mCap csrAddr qAddr lblAddr
    hV hga₂ hidx_len hidx_nd hidx_lt hidx₂ hpart₂_read hpart_w (fun _ _ => rfl)
    (fun u hu => (hkept_inv u hu).1) hdj hlvl_w hmCap_w (by omega)
    (by omega) (by omega) hkept_w_addr (by omega) (by omega) (by omega) (by omega)
  obtain ⟨o₃, st₃, c₃, hr₃, hpost₃, hc₃⟩ := hsp st₂ ω ⟨hlvl₂, rfl⟩
  cases o₃ with
  | returned _ => exact False.elim hpost₃
  | normal =>
    rcases hpost₃ with ⟨_, _, hrem_le, hrem_valid, hga_rem, hlist_rem, hremI_len,
      hremI_nd, hremI_lt, hlvl_arr, hfr₃⟩
    dsimp only at hc₃
    -- Stage 4: `.ret (.const 0)`
    have hret : Runs w p ω (.ret (.const 0)) st₃ (.returned 0) st₃ 2 :=
      runs_ret_iff.mpr ⟨0, by simp [Expr.eval], rfl, rfl, rfl⟩
    have hrun_lvl : Runs w p ω (levelProc b_run b_csr b_bfs b_gv b_ge b_part thr)
        (startState [curGAddr, curIdxAddr, nextGAddr, nextIdxAddr, lvlArrAddr, twAddr, bufAddr,
          workAddr, keptVertAddr, statePtr, lvl, D, D_phi, mCap] mem₀ pos)
        (.returned 0) st₃ (c₁ + (c₂ + (c₃ + 2 + 1) + 1) + 1) :=
      runs_seq hr₁ (runs_seq hr₂ (runs_seq hr₃ hret))
    -- Apply `decomposeLevel_of_parts_spec`
    set uniqLabels := tab k fun q => st₁.mem (grpUniqLbl bufAddr curG.n + q)
    let R_of : ℕ → Finset ℕ := fun L => Rs.getD (uniqLabels.idxOf L) ∅
    have huniq_nd : uniqLabels.Nodup := huniq_pw.imp fun hab => Nat.ne_of_lt hab
    have huniq_len : uniqLabels.length = k := by simp [uniqLabels, tab]
    have hRs_map : uniqLabels.map R_of = Rs := by
      refine List.ext_getElem (by simp [huniq_len, hRs_len]) fun q h1 h2 => ?_
      simp only [List.getElem_map]
      dsimp only [R_of]
      have hq : q < k := by simpa [hRs_len] using h2
      have hUq : uniqLabels[q]'(by omega) = st₁.mem (grpUniqLbl bufAddr curG.n + q) := by
        simp [uniqLabels, tab]
      rw [idxOf_getElem_of_pairwise_lt huniq_pw (by omega), List.getD_eq_getElem _ _ h2]
    have hvalidRs_eq : rawComps_lvl.map (fun comp => comp.2.toFinset) =
        List.filter (fun R => decide (2 ≤ R.card)) (uniqLabels.map R_of) := by
      rw [hrc_map, hRs_map]
    set validRs := List.filter (fun R => decide (2 ≤ R.card)) (uniqLabels.map R_of)
    have hphi_out_pos : (0 : ℝ) < 1 / (3 * (D_phi : ℝ)) := by positivity
    have hcross_le := crossing_edges_le_of_expDecomp (twinGraph_isValid (D := D) hV) hexpDec
    have hm_le_2lvl : curG.m ≤ 2 ^ lvl * curG.n := by rw [← hD_eq]; exact hm_le_D
    have hdl_spec := decomposeLevel_of_parts_spec (curG := curG) (i := lvl) hV hL h1lvl
      hm_le_2lvl hphi_out_pos (by rw [← hD_eq]; exact hexpDec) (by rw [← hD_eq]; exact hcross_le)
      uniqLabels huniq_nd
      (fun v hv => by
        have hlt : st₁.mem (grpPartId bufAddr curG.n + v) < k := (hpid v hv).1
        have hlv := ((hpid v hv).2 _ hlt).mp rfl
        rw [hlv]
        have : st₁.mem (grpUniqLbl bufAddr curG.n + st₁.mem (grpPartId bufAddr curG.n + v)) =
            uniqLabels[st₁.mem (grpPartId bufAddr curG.n + v)]'(by simp [uniqLabels, tab]; exact hlt) := by
          simp [uniqLabels, tab]
        rw [this]; exact List.getElem_mem _)
      R_of
      (fun L hL => by
        rw [List.mem_iff_getElem] at hL
        obtain ⟨q, hqk, rfl⟩ := hL
        have hq : q < k := by omega
        have hUq : uniqLabels[q]'(by omega) = st₁.mem (grpUniqLbl bufAddr curG.n + q) := by
          simp [uniqLabels, tab]
        have hR_eq : R_of (uniqLabels[q]'hqk) = Rs.getD q ∅ := by
          dsimp [R_of]; rw [idxOf_getElem_of_pairwise_lt huniq_pw (by omega)]
        rw [hR_eq, hUq]
        simpa [hD_eq] using hRs_spec q hq)
    dsimp only at hdl_spec
    rcases hdl_spec with ⟨hGi_val, hGi_loop, _, _, hperm, hGi_m, hrem_m_lvl, hvalid_disj,
      hvalid_spec, hGi_cover⟩
    set pred := fun e : ℕ × ℕ => validRs.any fun R => decide (e.1 ∈ R ∧ e.2 ∈ R)
    set Gi : Cited.Graph := { n := curG.n, edges := List.filter pred curG.edges }
    set remG : Cited.Graph := { n := curG.n, edges := remEdgesPrefix curG partId kept curG.m }
    set remIdx := remIdxPrefix curG curIdx partId kept curG.m
    set keptFlag : ℕ → Bool := fun t => edgeKeptBool curG partId kept t
    set keptIdx := ((List.range curG.m).filter fun t => keptFlag t).map (fun t => curIdx.getD t 0)
    have hRs_filt_eq : validRs = (List.range k).filterMap (fun q =>
        if 2 ≤ (Rs.getD q ∅).card then some (Rs.getD q ∅) else none) := by
      dsimp only [validRs]
      rw [← filter_ge2_map_eq_filterMap]
      congr 1
      rw [hRs_map]
      refine List.ext_getElem (by simp [hRs_len]) fun q h1 h2 => ?_
      rw [List.getElem_map, List.getElem_range]
      exact (List.getD_eq_getElem Rs ∅ h1).symm
    have hk_eq_flag : ∀ t < curG.m, edgeKeptBool curG partId kept t =
        validRs.any (fun R => decide ((curG.edges.getD t (0, 0)).1 ∈ R ∧
          (curG.edges.getD t (0, 0)).2 ∈ R)) := by
      intro t ht
      refine edgeKeptBool_iff_any_valid partId kept (fun q => Rs.getD q ∅) validRs hRs_filt_eq
        (fun q hq => by
          have hsub := (hRs_spec q hq).1
          intro u hu
          have hpx := hsub hu
          simp only [partX, Finset.mem_filter, Finset.mem_range] at hpx
          rw [Finset.mem_filter, Finset.mem_range]
          exact ⟨hpx.1, ((hpid u hpx.1).2 q hq).mpr hpx.2.2⟩)
        (fun q hq => by
          have hs := (hRs_spec q hq).2.1
          exact hs.imp id fun h => h.1)
        (fun u hu => by
          dsimp [kept]
          simpa [ne_eq] using (hkept_inv u hu).2)
        hV ht
    have hremE_eq : remG.edges = List.filter (fun e => !pred e) curG.edges := by
      dsimp only [remG]
      rw [remEdgesPrefix_eq_filter_map curG partId kept curG.m (le_refl _)]
      have hmap_all : curG.edges = (List.range curG.m).map (fun t => curG.edges.getD t (0, 0)) := by
        refine List.ext_getElem (by simp [Cited.Graph.m]) fun t h1 h2 => ?_
        simp only [List.getElem_map, List.getElem_range]
        rw [List.getD_eq_getElem _ _ h1]
      conv_rhs => rw [hmap_all, List.filter_map]
      have hf : ((List.range curG.m).filter fun t => !edgeKeptBool curG partId kept t) =
          ((List.range curG.m).filter fun t => !pred (curG.edges.getD t (0, 0))) := by
        apply List.filter_congr; intro t ht; rw [List.mem_range] at ht; simp [pred, hk_eq_flag t ht]
      rw [hf]; rfl
    have hremG_eq_split : remG = ⟨curG.n, List.filter (fun e => !pred e) curG.edges⟩ := by
      dsimp [remG]
      exact congrArg (Cited.Graph.mk curG.n) (by dsimp [remG] at hremE_eq; exact hremE_eq)
    have hGiE_eq : Gi.edges = ((List.range curG.m).filter fun t => keptFlag t).map (fun t => curG.edges.getD t (0, 0)) := by
      dsimp only [Gi]
      have hmap_all : curG.edges = (List.range curG.m).map (fun t => curG.edges.getD t (0, 0)) := by
        refine List.ext_getElem (by simp [Cited.Graph.m]) fun t h1 h2 => ?_
        simp only [List.getElem_map, List.getElem_range]
        rw [List.getD_eq_getElem _ _ h1]
      conv_lhs => rw [hmap_all, List.filter_map]
      have hf : ((List.range curG.m).filter fun t => pred (curG.edges.getD t (0, 0))) =
          ((List.range curG.m).filter fun t => keptFlag t) := by
        apply List.filter_congr; intro t ht; rw [List.mem_range] at ht; simp [keptFlag, pred, hk_eq_flag t ht]
      simp only [Function.comp_def]
      rw [hf]
    have hremIdx_pw : remIdx.Pairwise (· < ·) := by
      dsimp only [remIdx]
      rw [remIdxPrefix_eq_filter_map curG curIdx partId kept curG.m (le_refl _), ← hidx_len]
      exact pairwise_lt_map_filter curIdx hidx_pw _
    have hkeptIdx_pw : keptIdx.Pairwise (· < ·) := by
      dsimp only [keptIdx]
      rw [← hidx_len]
      exact pairwise_lt_map_filter curIdx hidx_pw _
    have hkeptIdx_nd : keptIdx.Nodup := hkeptIdx_pw.imp fun hab => Nat.ne_of_lt hab
    have hkeptIdx_lt : ∀ a ∈ keptIdx, a < mCap := by
      intro a ha
      rw [List.mem_map] at ha
      rcases ha with ⟨t, ht, rfl⟩
      rw [List.mem_filter, List.mem_range] at ht
      exact hidx_lt _ (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
    have hkeptIdx_len : keptIdx.length = Gi.m := by
      rw [Cited.Graph.m, hGiE_eq]; simp [keptIdx]
    refine ⟨st₃, _, arena₁, zeroCursor', rawComps_lvl, validRs, remG, Gi, remIdx, keptIdx,
      keptFlag, hrun_lvl, ha0_le, ha_ub, ?_, ?_, ?_, ?_, hzc_le, ?_, ?_, hptr_eq,
      hvalidRs_eq, hrc_mem, rfl, rfl, hGi_val, hGi_loop, ?_, ?_, ?_, hGi_m, ?_,
      hvalid_disj, hvalid_spec, hGi_cover, hga_rem, hlist_rem, hremI_len, hremI_nd,
      hremIdx_pw, hremI_lt, hkeptIdx_len, hkeptIdx_nd, hkeptIdx_pw, hkeptIdx_lt, ?_, ?_, hGiE_eq,
      rfl, ?_, ?_, ?_⟩
    · rw [hfr₃ statePtr (Or.inl (by omega)) (by omega) (by omega)]; exact hst₂_ptr0
    · rw [hfr₃ (statePtr + 1) (Or.inl (by omega)) (by omega) (by omega)]; exact hst₂_ptr1
    · rw [hfr₃ (statePtr + 2) (Or.inl (by omega)) (by omega) (by omega)]; exact hst₂_ptr2
    · intro a ha
      rw [hfr₃ a (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)),
        hfr₂ a (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hzf₁ a ha
    · simpa [m_tw] using hzc_ub
    · intro t ht
      rw [hfr₃ _ (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))]
      exact hlist_ar t ht
    · rwa [hremG_eq_split]
    · rwa [hremG_eq_split]
    · rw [hremG_eq_split]; exact hperm
    · rw [hremG_eq_split]; exact hrem_m_lvl
    · dsimp only [remG]; exact remEdgesPrefix_eq_filter_map curG partId kept curG.m (le_refl _)
    · dsimp only [remIdx]; exact remIdxPrefix_eq_filter_map curG curIdx partId kept curG.m (le_refl _)
    · intro a ha
      rw [hlvl_arr a ha]
      dsimp only [splitLvlVal, keptIdx, keptFlag]
      have hpre_eq : st₂.mem (lvlArrAddr + a) = mem₀ (lvlArrAddr + a) := by
        rw [hfr₂ _ (by omega) (by omega) (by omega) (by omega) (by omega),
          hlt_tw_eq _ (by omega) (by omega)]
      rw [hpre_eq]
      by_cases hmem : ∃ t < curG.m, curIdx.getD t 0 = a ∧ edgeKeptBool curG partId kept t = true
      · have hmem2 : a ∈ List.map (fun t => curIdx.getD t 0)
            (List.filter (fun t => edgeKeptBool curG partId kept t) (List.range curG.m)) := by
          rcases hmem with ⟨t, ht, ha_eq, hk⟩
          exact List.mem_map.mpr ⟨t, List.mem_filter.mpr ⟨List.mem_range.mpr ht, hk⟩, ha_eq⟩
        simp only [hmem, hmem2, ↓reduceIte]
      · have hmem2 : a ∉ List.map (fun t => curIdx.getD t 0)
            (List.filter (fun t => edgeKeptBool curG partId kept t) (List.range curG.m)) := by
          intro hm
          rcases List.mem_map.mp hm with ⟨t, ht, ha_eq⟩
          rw [List.mem_filter, List.mem_range] at ht
          exact hmem ⟨t, ht.1, ha_eq, ht.2⟩
        simp only [hmem, hmem2, ↓reduceIte]
    · intro a ha_zc hns hnl hng hni hntw hnar
      rw [hfr₃ a (by omega) (by omega) (by omega),
        hfr₂ a (by by_contra h; exact hntw ⟨by omega, by omega⟩) (by by_contra h; exact hntw ⟨by omega, by omega⟩) hnar
          (by by_contra h; subst h; exact hns ⟨le_rfl, by omega⟩)
          (by by_contra h; subst h; exact hns ⟨by omega, by omega⟩)]
      exact hfr₁ a ha_zc
        (by by_contra h; exact hntw ⟨by omega, by omega⟩)
        (by by_contra h; exact hntw ⟨by omega, by omega⟩)
        (by by_contra h; exact hntw ⟨by omega, by omega⟩)
        (by by_contra h; exact hntw ⟨by omega, by omega⟩)
        (by by_contra h; subst h; exact hns ⟨by omega, by omega⟩)
    · dsimp only [levelCost, m_tw] at hc₁ hc₂ hc₃ ⊢
      have hn_sq : curG.n * (1000 + 400 * (4 * (4 * (4 * D_phi + 2) * (Nat.log 2 (2 * curG.m + 1) + 1) + 2) + 14) ^ 2) ≤
          curG.n * (1100 + 400 * (4 * (4 * (4 * D_phi + 2) * (Nat.log 2 (2 * curG.m + 1) + 1) + 2) + 14) ^ 2) :=
        Nat.mul_le_mul_left _ (by omega)
      omega

end MinCostFlow.Expander
