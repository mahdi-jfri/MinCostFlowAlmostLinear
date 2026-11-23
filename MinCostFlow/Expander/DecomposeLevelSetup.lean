/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MinCostFlow.Expander.DecomposeLevelCommon

import Mathlib.Tactic.Linarith

/-!
# Stage 1 Setup Execution (`levelSetupPrefix_runs`) for Single-Level Expander Decomposition

Proves `levelSetupPrefix_runs`, covering twin-graph construction, `[B1]` decomposition,
zeroing `keptVert`, vertex grouping, `normSameTwinStmt`, and edge grouping.
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-! ## 3. Stage 1: `levelSetupPrefix_runs` -/

lemma levelSetupPrefix_runs {w : ℕ} {p : Program} {b_run b_csr b_bfs b_gv b_ge thr : ℕ}
    {P_cited : Program} {c_cited : ℕ} {φ_cited : ℝ}
    (mem₀ : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) (curG : Cited.Graph)
    (curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
      keptVertAddr statePtr lvl D D_phi mCap zeroCursor c_cited_ub : ℕ)
    (hV : curG.IsValid) (h1n : 1 ≤ curG.n) (h1D : 1 ≤ D)
    (hga : GraphAt mem₀ curGAddr curG)
    (hzeroCursor : mem₀ (statePtr + 1) = zeroCursor) (hzf : ZeroFrom mem₀ zeroCursor)
    (h_csr : MeetsContract w p b_csr (buildCsrContract w))
    (h_bfs : MeetsContract w p b_bfs (bfsLabelsContract w))
    (h_run : p.HasAt b_run (runner (stripRandProg P_cited) c_cited b_run))
    (h_gv : MeetsContract w p b_gv (groupVertsContract w))
    (h_ge : MeetsContract w p b_ge (groupEdgesContract w))
    (hcited : thr ≤ curG.m + D * curG.n →
      ∃ out cost_c,
        RunsTo (wordSize c_cited ((twinGraph D curG).encode ++ [1, 200, rOf (curG.m + D * curG.n)]))
          P_cited ((twinGraph D curG).encode ++ [1, 200, rOf (curG.m + D * curG.n)]) (fun _ => false)
          out cost_c ∧
        IsExpanderDecomposition (twinGraph D curG) (1 / 200) φ_cited out ∧
        1 / (D_phi : ℝ) ≤ φ_cited ∧ cost_c ≤ c_cited_ub)
    (hthr_Dphi : thr + 1 ≤ D_phi) (hthr_w : thr < 2 ^ w)
    (hs_cg : statePtr + 3 ≤ curGAddr) (hcg_tw : curGAddr + 2 + 2 * curG.m ≤ twAddr)
    (hkept_w_addr : keptVertAddr + curG.n < 2 ^ w)
    (hlog_w : Nat.log 2 (curG.m + D * curG.n) + 1 < 2 ^ w)
    (hrOf_w : (rOf (curG.m + D * curG.n) + 1) ^ 3 < 2 ^ w)
    (h201_w : 201 ≤ 2 ^ w)
    (hlbl_buf : twAddr + 6 + 6 * curG.n + 6 * (curG.m + D * curG.n) + 2 * curG.n ≤ bufAddr)
    (hbuf_w : bufAddr + groupBufSize curG.n curG.m + 2 < 2 ^ w)
    (hbuf_kept : bufAddr + groupBufSize curG.n curG.m ≤ keptVertAddr)
    (hzero_lo : keptVertAddr + curG.n ≤ zeroCursor)
    (hzero_w : zeroCursor < 2 ^ w)
    (hrun_w : thr ≤ curG.m + D * curG.n →
      zeroCursor + 2 * curG.n +
        2 ^ (wordSize c_cited ((twinGraph D curG).encode ++ [1, 200, rOf (curG.m + D * curG.n)]) + 1) + 2 ≤ 2 ^ w)
    (hargs_w : ∀ a ∈ [curGAddr, curIdxAddr, nextGAddr, nextIdxAddr, lvlArrAddr, twAddr, bufAddr,
      workAddr, keptVertAddr, statePtr, lvl, D, D_phi, mCap], a < 2 ^ w) :
    let m_tw := curG.m + D * curG.n
    let csrAddr := twAddr + 5 + 2 * m_tw
    let qAddr := csrAddr + 4 * curG.n + 1 + 4 * m_tw
    let lblAddr := qAddr + 2 * curG.n
    let args := [curGAddr, curIdxAddr, nextGAddr, nextIdxAddr, lvlArrAddr, twAddr, bufAddr,
      workAddr, keptVertAddr, statePtr, lvl, D, D_phi, mCap]
    ∃ st' c k label, ∃ φ_B1 : ℝ,
      Runs w p ω (levelSetupPrefix b_run b_csr b_bfs b_gv b_ge thr)
        (startState args mem₀ pos) .normal st' c ∧
      LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
        keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr st' ∧
      st'.regs 20 = k ∧ 1 ≤ k ∧ k ≤ curG.n ∧
      label.length = 2 * curG.n ∧
      1 / (D_phi : ℝ) ≤ φ_B1 ∧
      IsExpanderDecomposition (twinGraph D curG) (1 / 200) φ_B1 label ∧
      ZeroFrom st'.mem (st'.mem (statePtr + 1)) ∧
      zeroCursor ≤ st'.mem (statePtr + 1) ∧
      st'.mem (statePtr + 1) ≤ (if thr ≤ m_tw then
        zeroCursor + 1 + 2 ^ (wordSize c_cited ((twinGraph D curG).encode ++ [1, 200, rOf m_tw]))
        else zeroCursor) ∧
      (∀ a < zeroCursor, ¬ (twAddr ≤ a ∧ a < twAddr + 5 + 2 * m_tw) →
        ¬ (csrAddr ≤ a ∧ a < lblAddr + 2 * curG.n) →
        ¬ (bufAddr ≤ a ∧ a < bufAddr + groupBufSize curG.n curG.m) →
        ¬ (keptVertAddr ≤ a ∧ a < keptVertAddr + curG.n) →
        a ≠ statePtr + 1 → st'.mem a = mem₀ a) ∧
      (∀ u < curG.n, st'.mem (keptVertAddr + u) = 0) ∧
      (∀ q < k, ∃ cnt off ecnt eoff,
        st'.mem (grpPartCnt bufAddr curG.n + q) = cnt ∧
        st'.mem (grpPartOff bufAddr curG.n + q) = off ∧
        st'.mem (grpEdgeCnt bufAddr curG.n + q) = ecnt ∧
        st'.mem (grpEdgeOff bufAddr curG.n + q) = eoff ∧
        off + cnt ≤ curG.n ∧ eoff + ecnt ≤ curG.m ∧
        (have L := st'.mem (grpUniqLbl bufAddr curG.n + q);
         have Y := {z ∈ Finset.range (2 * curG.n) | label.getD z 0 = L};
         (tab cnt fun t => st'.mem (grpPartVerts bufAddr curG.n + off + t)).toFinset = partX curG.n Y ∧
         (twinGraph D curG).IsConductanceExpanderOn Y φ_B1) ∧
        (∀ u : ℕ, (u ∈ tab cnt fun t => st'.mem (grpPartVerts bufAddr curG.n + off + t)) ↔
          u < curG.n ∧ st'.mem (grpPartId bufAddr curG.n + u) = q) ∧
        List.Pairwise (· < ·) (tab cnt fun t => st'.mem (grpPartVerts bufAddr curG.n + off + t)) ∧
        (∀ u < curG.n, st'.mem (grpPartId bufAddr curG.n + u) = q →
          st'.mem (grpLocalId bufAddr curG.n + u) < cnt ∧
          st'.mem (grpPartVerts bufAddr curG.n + off + st'.mem (grpLocalId bufAddr curG.n + u)) = u) ∧
        (have partFn := fun u => st'.mem (grpPartId bufAddr curG.n + u);
         have localFn := fun u => st'.mem (grpLocalId bufAddr curG.n + u);
         have es := List.map (fun j => (localFn (st'.mem (curGAddr + 2 + 2 * j)),
           localFn (st'.mem (curGAddr + 3 + 2 * j))))
           (List.filter (fun j => decide (partFn (st'.mem (curGAddr + 2 + 2 * j)) = q ∧
             partFn (st'.mem (curGAddr + 3 + 2 * j)) = q)) (List.range curG.m));
         ecnt = es.length ∧ ∀ t (ht : t < es.length),
           st'.mem (grpPartEdges bufAddr curG.n + 2 * (eoff + t)) = es[t].1 ∧
           st'.mem (grpPartEdges bufAddr curG.n + 2 * (eoff + t) + 1) = es[t].2)) ∧
      (∀ u < curG.n, st'.mem (grpSameTwin bufAddr curG.n + u) < 2 ^ w ∧
        (st'.mem (grpSameTwin bufAddr curG.n + u) ≠ 0 ↔
          2 * u + 1 ∈ {z ∈ Finset.range (2 * curG.n) | label.getD z 0 = label.getD (2 * u) 0})) ∧
      (∀ u < curG.n, st'.mem (grpPartId bufAddr curG.n + u) < k ∧
        ∀ q < k, st'.mem (grpPartId bufAddr curG.n + u) = q ↔
          label.getD (2 * u) 0 = st'.mem (grpUniqLbl bufAddr curG.n + q)) ∧
      List.Pairwise (· < ·) (tab k fun q => st'.mem (grpUniqLbl bufAddr curG.n + q)) ∧
      st'.mem (grpPartOff bufAddr curG.n) = 0 ∧
      st'.mem (grpPartOff bufAddr curG.n + k) = curG.n ∧
      (∀ q < k, st'.mem (grpPartOff bufAddr curG.n + (q + 1)) =
        st'.mem (grpPartOff bufAddr curG.n + q) + st'.mem (grpPartCnt bufAddr curG.n + q)) ∧
      st'.mem (grpEdgeOff bufAddr curG.n) = 0 ∧
      st'.mem (grpEdgeOff bufAddr curG.n + k) ≤ curG.m ∧
      (∀ q < k, st'.mem (grpEdgeOff bufAddr curG.n + (q + 1)) =
        st'.mem (grpEdgeOff bufAddr curG.n + q) + st'.mem (grpEdgeCnt bufAddr curG.n + q)) ∧
      c ≤ 120 * (m_tw + 1) + 45 * (Nat.log 2 (m_tw + 1) + 2) +
        400 * (2 * curG.n + m_tw + 2) +
        runnerScale P_cited * (2 * c_cited_ub + (5 + 2 * m_tw) +
          wordSize c_cited ((twinGraph D curG).encode ++ [1, 200, rOf m_tw]) + 1) +
        1000 * (curG.n * (2 * Nat.log 2 (curG.n + 2) + 1) + 1) +
        39 * curG.n + 200 * (curG.n + curG.m + 1) + 120 := by
  dsimp only
  set m_tw := curG.m + D * curG.n
  set csrAddr := twAddr + 5 + 2 * m_tw
  set qAddr := csrAddr + 4 * curG.n + 1 + 4 * m_tw
  set lblAddr := qAddr + 2 * curG.n
  set args := [curGAddr, curIdxAddr, nextGAddr, nextIdxAddr, lvlArrAddr, twAddr, bufAddr,
    workAddr, keptVertAddr, statePtr, lvl, D, D_phi, mCap]
  have hm_tw_eq : (twinGraph D curG).m = m_tw := twinGraph_m D curG
  have hargs_lt : ∀ i < 14, args.getD i 0 < 2 ^ w := fun i hi => by
    have : args.getD i 0 ∈ args := by
      rw [List.getD_eq_getElem _ _ (by simp [args]; omega)]
      exact List.getElem_mem _
    exact hargs_w _ this
  have hcurG_w : curGAddr < 2 ^ w := hargs_lt 0 (by omega)
  have hs_tw : statePtr + 3 ≤ twAddr := by omega
  have htw_w : twAddr < 2 ^ w := hargs_lt 5 (by omega)
  have hbuf_a_w : bufAddr < 2 ^ w := hargs_lt 6 (by omega)
  have hD_w : D < 2 ^ w := hargs_lt 11 (by omega)
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hw5 : 5 < 2 ^ w := by omega
  have hw16 : 16 ≤ 2 ^ w := by omega
  have hcurN_w : curG.n < 2 ^ w := by have := hbuf_w; simp [groupBufSize] at this; omega
  have hcurM_w : curG.m < 2 ^ w := by have := hbuf_w; simp [groupBufSize] at this; omega
  have hm_tw_w : m_tw < 2 ^ w := by omega
  have htw_end_w : twAddr + 5 + 2 * m_tw < 2 ^ w := by omega
  have h2n_w : 2 * curG.n < 2 ^ w := by omega
  have h4n_w : 4 * curG.n < 2 ^ w := by omega
  have h4mtw_w : 4 * m_tw < 2 ^ w := by omega
  -- 1. Register initialization
  let s0 := startState args mem₀ pos
  let s1 : State := { s0 with regs := Function.update s0.regs 14 curG.n }
  let s2 : State := { s1 with regs := Function.update s1.regs 15 curG.m }
  let s3 : State := { s2 with regs := Function.update s2.regs 19 m_tw }
  let s4 : State := { s3 with regs := Function.update s3.regs 16 csrAddr }
  let s5 : State := { s4 with regs := Function.update s4.regs 17 qAddr }
  let s6 : State := { s5 with regs := Function.update s5.regs 18 lblAddr }
  have hga_n : mem₀ curGAddr = curG.n := graphAt_n hga
  have hga_m : mem₀ (curGAddr + 1) = curG.m := graphAt_m hga
  have ha14 : Runs w p ω (.assign 14 (.load (.reg 0))) s0 .normal s1 3 :=
    runs_assign_iff.mpr ⟨curG.n, by simp [Expr.eval, s0, args, startState, hga_n], rfl, rfl, rfl⟩
  have ha15 : Runs w p ω (.assign 15 (.load (.bin .add (.reg 0) (.const 1)))) s1 .normal s2 5 :=
    runs_assign_iff.mpr ⟨curG.m, by
      simp [Expr.eval, BinOp.eval, s1, s0, args, startState, hw1, show curGAddr + 1 < 2 ^ w by omega, hga_m],
      rfl, rfl, rfl⟩
  have ha19 : Runs w p ω (.assign 19 (.bin .add (.reg 15) (.bin .mul (.reg 11) (.reg 14)))) s2 .normal s3 6 :=
    runs_assign_iff.mpr ⟨m_tw, by
      simp [Expr.eval, BinOp.eval, s2, s1, s0, args, startState, show D * curG.n < 2 ^ w by omega, hm_tw_w, m_tw],
      rfl, rfl, rfl⟩
  have ha16 : Runs w p ω (.assign 16 (.bin .add (.reg 5) (.bin .add (.const 5) (.bin .mul (.const 2) (.reg 19)))))
      s3 .normal s4 8 :=
    runs_assign_iff.mpr ⟨csrAddr, by
      simp [Expr.eval, BinOp.eval, s3, s2, s1, s0, args, startState, hw2, hw5, show 2 * m_tw < 2 ^ w by omega,
        show 5 + 2 * m_tw < 2 ^ w by omega, show twAddr + (5 + 2 * m_tw) < 2 ^ w by omega, csrAddr, Nat.add_assoc],
      rfl, rfl, rfl⟩
  have ha17 : Runs w p ω (.assign 17 (.bin .add (.reg 16)
      (.bin .add (.bin .mul (.const 4) (.reg 14))
        (.bin .add (.const 1) (.bin .mul (.const 4) (.reg 19)))))) s4 .normal s5 12 :=
    runs_assign_iff.mpr ⟨qAddr, by
      simp [Expr.eval, BinOp.eval, s4, s3, s2, s1, s0, args, startState, hw4, hw1, h4n_w, h4mtw_w,
        show 1 + 4 * m_tw < 2 ^ w by omega, show 4 * curG.n + (1 + 4 * m_tw) < 2 ^ w by omega,
        show csrAddr + (4 * curG.n + (1 + 4 * m_tw)) = qAddr by omega,
        show qAddr < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have ha18 : Runs w p ω (.assign 18 (.bin .add (.reg 17) (.bin .mul (.const 2) (.reg 14)))) s5 .normal s6 6 :=
    runs_assign_iff.mpr ⟨lblAddr, by
      simp [Expr.eval, BinOp.eval, s5, s4, s3, s2, s1, s0, args, startState, hw2, h2n_w, lblAddr,
        show lblAddr < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have hlvl_s6 : LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
      keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr s6 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [s6, s5, s4, s3, s2, s1, s0, args, startState]
  -- 2. `buildTwinStmt`
  have hbt := buildTwin_triple p mem₀ curG curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr
    twAddr bufAddr workAddr keptVertAddr statePtr lvl D D_phi mCap csrAddr qAddr lblAddr
    hV h1D hga hcg_tw hm_tw_w hlog_w hrOf_w h2n_w htw_end_w h201_w hw16
  obtain ⟨o_bt, s_bt, c_bt, hr_bt, hbt_post, hc_bt⟩ := hbt s6 ω ⟨hlvl_s6, rfl⟩
  cases o_bt with
  | returned _ => exact False.elim hbt_post
  | normal =>
    rcases hbt_post with ⟨hlvl_bt, h19_bt, h20_bt, _, hlist_bt, hga_bt, hfr_bt⟩
    dsimp only at hc_bt
    -- 3. `twinDecompStmt`
    have hmem_zc : s_bt.mem (statePtr + 1) = zeroCursor := by
      rw [hfr_bt (statePtr + 1) (Or.inl (by omega))]; exact hzeroCursor
    have hzf_bt : ZeroFrom s_bt.mem zeroCursor := fun a ha => by
      rw [hfr_bt a (Or.inr (by omega))]; exact hzf a ha
    have hcited' : thr ≤ (twinGraph D curG).m →
        ∃ out cost_c,
          RunsTo (wordSize c_cited ((twinGraph D curG).encode ++ [1, 200, rOf (twinGraph D curG).m]))
            P_cited ((twinGraph D curG).encode ++ [1, 200, rOf (twinGraph D curG).m]) (fun _ => false)
            out cost_c ∧
          IsExpanderDecomposition (twinGraph D curG) (1 / 200) φ_cited out ∧
          1 / (D_phi : ℝ) ≤ φ_cited ∧ cost_c ≤ c_cited_ub := by
      intro h; rw [hm_tw_eq] at h ⊢; exact hcited h
    have hrun_w' : thr ≤ (twinGraph D curG).m →
        zeroCursor + 2 * curG.n +
          2 ^ (wordSize c_cited ((twinGraph D curG).encode ++ [1, 200, rOf (twinGraph D curG).m]) + 1) + 2 ≤ 2 ^ w := by
      intro h; rw [hm_tw_eq] at h ⊢; exact hrun_w h
    have hrOf_tw : rOf (twinGraph D curG).m < 2 ^ w := by
      have h1 : rOf m_tw < (rOf m_tw + 1) ^ 3 := by
        calc rOf m_tw < rOf m_tw + 1 := Nat.lt_succ_self _
          _ ≤ (rOf m_tw + 1) ^ 3 := Nat.le_self_pow (by omega) _
      rw [hm_tw_eq]; omega
    have htd := twinDecomp_triple (b_run := b_run) (b_csr := b_csr) (b_bfs := b_bfs) (thr := thr)
      (P_cited := P_cited) (c_cited := c_cited) (φ_cited := φ_cited)
      s_bt.mem curG curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
      keptVertAddr statePtr lvl D D_phi mCap csrAddr qAddr lblAddr zeroCursor c_cited_ub
      hV hga_bt hlist_bt hmem_zc hzf_bt h_csr h_bfs h_run hcited' hthr_Dphi hthr_w hs_tw
      (by omega) (by omega) (by omega)
      (by omega) hzero_w hrun_w'
      (twinGraph_encode_lt_pow curG D hV h2n_w (by rw [hm_tw_eq]; exact hm_tw_w) hrOf_tw h201_w)
      hw16
    obtain ⟨o_td, s_td, c_td, hr_td, htd_post, hc_td⟩ := htd s_bt ω ⟨hlvl_bt, h19_bt, h20_bt, rfl⟩
    rcases htd_post with ⟨rfl, hlvl_td, label, φ_B1, hlbl_len, hlbl_at, hlbl_w, hphi_ge,
      hexpDec, hzf_td, hzc_le, hzc_ub, hfr_td⟩
    dsimp only at hc_td
    -- 4. `zeroKeptStmt`
    have hzk := zeroKept_triple p s_td.mem curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr
      twAddr bufAddr workAddr keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr
      hkept_w_addr hw1
    obtain ⟨o_zk, s_zk, c_zk, hr_zk, hpost_zk, hc_zk⟩ := hzk s_td ω ⟨hlvl_td, rfl⟩
    cases o_zk with
    | returned _ => exact False.elim hpost_zk
    | normal =>
      rcases hpost_zk with ⟨hlvl_zk, hkept_zero, hfr_zk⟩
      dsimp only at hc_zk
      have hlbl_zk : ListAt s_zk.mem lblAddr label := fun i hi => by
        rw [hfr_zk _ (Or.inl (by omega))]; exact hlbl_at i hi
      have hlbl_w_zk : ∀ i < 2 * curG.n, s_zk.mem (lblAddr + i) < 2 ^ w := fun i hi => by
        rw [hfr_zk _ (Or.inl (by omega))]; exact hlbl_w i hi
      have hga_zk : GraphAt s_zk.mem curGAddr curG := by
        have heq : ∀ a, curGAddr ≤ a → a < curGAddr + 2 + 2 * curG.m → s_zk.mem a = mem₀ a := fun a ha1 ha2 => by
          rw [hfr_zk a (Or.inl (by omega)), hfr_td a (by omega) (by omega) (Or.inl (by omega)),
            hfr_bt a (Or.inl (by omega))]
        exact graphAt_of_cells
          (by rw [heq _ (le_refl _) (by omega)]; exact hga_n)
          (by rw [heq _ (by omega) (by omega)]; exact hga_m)
          (fun t ht => ⟨
            by rw [heq _ (by omega) (by omega)]; exact graphAt_edge_fst hga ht,
            by rw [heq _ (by omega) (by omega)]; exact graphAt_edge_snd hga ht⟩)
      -- 5. `.call 19 b_gv [.reg 14, .reg 18, .reg 6]`
      have heval_gv : evalArgs w s_zk [.reg 14, .reg 18, .reg 6] = some [curG.n, lblAddr, bufAddr] := by
        simp [evalArgs, Expr.eval, hlvl_zk.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hlvl_zk.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, hlvl_zk.2.2.2.2.2.2.1]
      have hpre_gv : (groupVertsContract w).pre [curG.n, lblAddr, bufAddr] s_zk.mem :=
        ⟨curG.n, lblAddr, bufAddr, label, rfl, h1n, hlbl_zk, hlbl_len, hlbl_w_zk, by omega, by
          have := hbuf_w; simp [groupBufSize] at this ⊢; omega, hw16⟩
      have hgv_end := h_gv [curG.n, lblAddr, bufAddr] s_zk.mem s_zk.pos ω
        (fun a ha => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl <;> omega)
        hpre_gv
      rcases hgv_end with ⟨body_gv, hproc_gv, o_gv, s1_gv, c_gv, hr1_gv, hpost_gv, hc_gv⟩
      let s_gv : State := { mem := s1_gv.mem, regs := Function.update s_zk.regs 19 o_gv.value, pos := s1_gv.pos }
      have hcall_gv : Runs w p ω (.call 19 b_gv [.reg 14, .reg 18, .reg 6]) s_zk .normal s_gv (3 + c_gv + 1) :=
        runs_call_iff.mpr ⟨[curG.n, lblAddr, bufAddr], body_gv, o_gv, s1_gv, c_gv,
          heval_gv, hproc_gv, hr1_gv, rfl, rfl, by simp [argsSize, Expr.size]⟩
      set k := o_gv.value
      dsimp only [groupVertsContract] at hpost_gv hc_gv
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hpost_gv hc_gv
      rcases hpost_gv with ⟨hk1, hkn, huniq_pw, hpart_spec, huniq_wit, hpo0, hpok, hpo_step,
        hverts_spec, hlid_spec, hfr_gv⟩
      -- 6. `normSameTwinStmt`
      have hlvl_gv : LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
          keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr s_gv :=
        lvlRegs_of_eq (fun r hr => by dsimp [s_gv]; rw [Function.update_of_ne (by omega)]) hlvl_zk
      obtain ⟨s_nst, c_nst, hr_nst, hc_nst, hregs_nst, hdone_nst, hfr_nst⟩ :=
        normSameTwin_runs (p := p) (ω := ω) curG.n bufAddr s_gv
          hlvl_gv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hlvl_gv.2.2.2.2.2.2.1
          hcurN_w (by have := hbuf_w; simp [groupBufSize] at this; omega) hw1
      have hlvl_nst : LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
          keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr s_nst :=
        lvlRegs_of_eq (fun r hr => hregs_nst r (by omega)) hlvl_gv
      have hs_nst_19 : s_nst.regs 19 = k := by
        rw [hregs_nst 19 (by omega)]; dsimp [s_gv]; rw [Function.update_self]
      have hga_nst : GraphAt s_nst.mem curGAddr curG := by
        have heq : ∀ a, curGAddr ≤ a → a < curGAddr + 2 + 2 * curG.m → s_nst.mem a = s_zk.mem a := fun a ha1 ha2 => by
          rw [hfr_nst a (Or.inl (by omega)), hfr_gv a (Or.inl (by omega))]
        exact graphAt_of_cells
          (by rw [heq _ (le_refl _) (by omega)]; exact graphAt_n hga_zk)
          (by rw [heq _ (by omega) (by omega)]; exact graphAt_m hga_zk)
          (fun t ht => ⟨
            by rw [heq _ (by omega) (by omega)]; exact graphAt_edge_fst hga_zk ht,
            by rw [heq _ (by omega) (by omega)]; exact graphAt_edge_snd hga_zk ht⟩)
      -- 7. `.call 20 b_ge [.reg 0, .reg 19, .reg 6]`
      have heval_ge : evalArgs w s_nst [.reg 0, .reg 19, .reg 6] = some [curGAddr, k, bufAddr] := by
        simp [evalArgs, Expr.eval, hlvl_nst.1, hs_nst_19, hlvl_nst.2.2.2.2.2.2.1]
      have hpre_ge : (groupEdgesContract w).pre [curGAddr, k, bufAddr] s_nst.mem := by
        refine ⟨curGAddr, k, bufAddr, curG, rfl, hk1, hkn, hV, hga_nst, by omega, hbuf_w, hw16, ?_, ?_⟩
        · intro u hu; rw [hfr_nst _ (Or.inr (by simp [grpPartId]; omega))]
          exact (hpart_spec u hu).2.2.2
        · intro u hu; rw [hfr_nst _ (Or.inr (by simp [grpLocalId]; omega))]
          have hlid_lt := (hlid_spec u hu).1
          have hq_lt : s1_gv.mem (grpPartId bufAddr curG.n + u) < k := (hpart_spec u hu).2.2.2
          have hpo_le := (hverts_spec _ hq_lt).2.1
          dsimp [s_gv]; omega
      have hge_end := h_ge [curGAddr, k, bufAddr] s_nst.mem s_nst.pos ω
        (fun a ha => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl <;> omega)
        hpre_ge
      rcases hge_end with ⟨body_ge, hproc_ge, o_ge, s1_ge, c_ge, hr1_ge, hpost_ge, hc_ge⟩
      let s_ge : State := { mem := s1_ge.mem, regs := Function.update s_nst.regs 20 o_ge.value, pos := s1_ge.pos }
      have hcall_ge : Runs w p ω (.call 20 b_ge [.reg 0, .reg 19, .reg 6]) s_nst .normal s_ge (3 + c_ge + 1) :=
        runs_call_iff.mpr ⟨[curGAddr, k, bufAddr], body_ge, o_ge, s1_ge, c_ge,
          heval_ge, hproc_ge, hr1_ge, rfl, rfl, by simp [argsSize, Expr.size]⟩
      dsimp only [groupEdgesContract] at hpost_ge hc_ge
      simp only [List.getD_cons_zero, List.getD_cons_succ, graphAt_n hga_nst, graphAt_m hga_nst] at hpost_ge hc_ge
      rcases hpost_ge with ⟨heo0, heok, heo_step, hes_spec, hfr_ge⟩
      -- 8. `.assign 20 (.reg 19)`
      let s_k : State := { s_ge with regs := Function.update s_ge.regs 20 k }
      have hs_ge_19 : s_ge.regs 19 = k := by
        dsimp [s_ge]; rw [Function.update_of_ne (by omega)]; exact hs_nst_19
      have ha_k : Runs w p ω (.assign 20 (.reg 19)) s_ge .normal s_k 2 :=
        runs_assign_iff.mpr ⟨k, by simp [Expr.eval, hs_ge_19], rfl, rfl, rfl⟩
      have hlvl_ge : LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
          keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr s_ge :=
        lvlRegs_of_eq (fun r hr => by dsimp [s_ge]; rw [Function.update_of_ne (by omega)]) hlvl_nst
      have hlvl_k : LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
          keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr s_k :=
        lvlRegs_of_eq (fun r hr => by dsimp [s_k]; rw [Function.update_of_ne (by omega)]) hlvl_ge
      have hrun_full :=
        runs_seq ha14 (runs_seq ha15 (runs_seq ha19 (runs_seq ha16 (runs_seq ha17 (runs_seq ha18
          (runs_seq hr_bt (runs_seq hr_td (runs_seq hr_zk
            (runs_seq hcall_gv (runs_seq hr_nst (runs_seq hcall_ge ha_k)))))))))))
      rw [← levelSetupPrefix_eq] at hrun_full
      have hsk_lo : ∀ a, a < grpEdgeCnt bufAddr curG.n → s_k.mem a = s_nst.mem a := fun a ha =>
        hfr_ge a (Or.inl ha)
      have hsk_mid : ∀ a, bufAddr + curG.n ≤ a → a < grpEdgeCnt bufAddr curG.n → s_k.mem a = s_gv.mem a :=
        fun a ha1 ha2 => by rw [hsk_lo a ha2, hfr_nst a (Or.inr ha1)]
      have hsk_hi : ∀ a, bufAddr + groupBufSize curG.n curG.m ≤ a → s_k.mem a = s_zk.mem a :=
        fun a ha => by
          rw [hfr_ge a (Or.inr ha), hfr_nst a (Or.inr (by simp [groupBufSize] at ha ⊢; omega)),
            hfr_gv a (Or.inr (by simp [groupBufSize] at ha ⊢; omega))]
      have hsk_ptr1 : s_k.mem (statePtr + 1) = s_td.mem (statePtr + 1) := by
        rw [hsk_lo (statePtr + 1) (by simp [grpEdgeCnt]; omega),
          hfr_nst (statePtr + 1) (Or.inl (by omega)), hfr_gv (statePtr + 1) (Or.inl (by omega)),
          hfr_zk (statePtr + 1) (Or.inl (by omega))]
      have hsk_above_kept : ∀ a, keptVertAddr + curG.n ≤ a → s_k.mem a = s_td.mem a := fun a ha => by
        rw [hsk_hi a (by omega), hfr_zk a (Or.inr ha)]
      have huniq_eq : ∀ q < k, s_k.mem (grpUniqLbl bufAddr curG.n + q) =
          s_gv.mem (grpUniqLbl bufAddr curG.n + q) := fun q hq => by
        apply hsk_mid _ (by simp [grpUniqLbl]; omega) (by simp [grpUniqLbl, grpEdgeCnt]; omega)
      have hpartId_eq : ∀ u < curG.n, s_k.mem (grpPartId bufAddr curG.n + u) =
          s_gv.mem (grpPartId bufAddr curG.n + u) := fun u hu => by
        apply hsk_mid _ (by simp [grpPartId]; omega) (by simp [grpPartId, grpEdgeCnt]; omega)
      have hpartCnt_eq : ∀ q < k, s_k.mem (grpPartCnt bufAddr curG.n + q) =
          s_gv.mem (grpPartCnt bufAddr curG.n + q) := fun q hq => by
        apply hsk_mid _ (by simp [grpPartCnt]; omega) (by simp [grpPartCnt, grpEdgeCnt]; omega)
      have hpartOff_eq : ∀ q ≤ k, s_k.mem (grpPartOff bufAddr curG.n + q) =
          s_gv.mem (grpPartOff bufAddr curG.n + q) := fun q hq => by
        apply hsk_mid _ (by simp [grpPartOff]; omega) (by simp [grpPartOff, grpEdgeCnt]; omega)
      have hlid_eq : ∀ u < curG.n, s_k.mem (grpLocalId bufAddr curG.n + u) =
          s_gv.mem (grpLocalId bufAddr curG.n + u) := fun u hu => by
        apply hsk_mid _ (by simp [grpLocalId]; omega) (by simp [grpLocalId, grpEdgeCnt]; omega)
      have huniq_spec : ∀ u < curG.n, s_k.mem (grpPartId bufAddr curG.n + u) < k ∧
          ∀ q < k, s_k.mem (grpPartId bufAddr curG.n + u) = q ↔
            label.getD (2 * u) 0 = s_k.mem (grpUniqLbl bufAddr curG.n + q) := by
        intro u hu
        rw [hpartId_eq u hu]
        have hps := hpart_spec u hu
        have hl2u : s_zk.mem (lblAddr + 2 * u) = label.getD (2 * u) 0 := by
          rw [hlbl_zk (2 * u) (by omega), List.getD_eq_getElem _ _ (by omega)]
        rw [hl2u] at hps
        refine ⟨hps.2.2.2, fun q hq => ?_⟩
        rw [hps.2.2.1, huniq_eq q hq]
        set uniq := tab k fun p => s_gv.mem (grpUniqLbl bufAddr curG.n + p)
        have hmem_u : label.getD (2 * u) 0 ∈ uniq := hps.2.1
        have hUq : s_gv.mem (grpUniqLbl bufAddr curG.n + q) = uniq[q]'(by simp [uniq, tab, hq]) := by
          simp [uniq, tab]
        rw [hUq]
        constructor
        · intro hidx
          have hopt : some (label.getD (2 * u) 0) = some (uniq[q]'(by simp [uniq, tab, hq])) := by
            rw [← List.getElem?_eq_getElem (by simp [uniq, tab, hq]), ← hidx, List.getElem?_idxOf hmem_u]
          exact Option.some.inj hopt
        · intro heq
          rw [heq]
          exact idxOf_getElem_of_pairwise_lt huniq_pw (by simp [uniq, tab, hq])
      refine ⟨s_k, _, k, label, φ_B1, hrun_full, hlvl_k, by simp [s_k], hk1, hkn, hlbl_len, hphi_ge,
        hexpDec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, huniq_spec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro a ha
        rw [hsk_ptr1] at ha
        rw [hsk_above_kept a (le_trans hzero_lo (le_trans hzc_le ha))]
        exact hzf_td a ha
      · rw [hsk_ptr1]; exact hzc_le
      · rw [hsk_ptr1]
        simpa [hm_tw_eq] using hzc_ub
      · intro a ha_zc hnot_tw hnot_csr hnot_buf hnot_kept hnot_st
        have ha_grp : a < bufAddr ∨ bufAddr + groupBufSize curG.n curG.m ≤ a := by
          by_contra hcon; push Not at hcon; exact hnot_buf ⟨hcon.1, hcon.2⟩
        have hke_a : s_k.mem a = s_zk.mem a := by
          rcases ha_grp with hlt | hge
          · rw [hsk_lo a (by simp [grpEdgeCnt]; omega),
              hfr_nst a (Or.inl hlt), hfr_gv a (Or.inl hlt)]
          · exact hsk_hi a hge
        rw [hke_a]
        have hzk_a : s_zk.mem a = s_td.mem a := by
          apply hfr_zk a
          by_contra hcon; push Not at hcon
          exact hnot_kept ⟨hcon.1, hcon.2⟩
        rw [hzk_a]
        have htd_a : s_td.mem a = s_bt.mem a :=
          hfr_td a ha_zc hnot_st (by
            by_cases hlt : a < csrAddr
            · exact Or.inl hlt
            · exact Or.inr (by by_contra hcon; push Not at hcon; exact hnot_csr ⟨by omega, hcon⟩))
        rw [htd_a]
        exact hfr_bt a (by
          by_contra hcon; push Not at hcon
          exact hnot_tw ⟨hcon.1, by simp only [csrAddr, ← hm_tw_eq]; exact hcon.2⟩)
      · intro u hu; rw [hsk_hi _ (by omega)]; exact hkept_zero u hu
      · intro q hq
        set cnt := s_gv.mem (grpPartCnt bufAddr curG.n + q)
        set off := s_gv.mem (grpPartOff bufAddr curG.n + q)
        set ecnt := s_ge.mem (grpEdgeCnt bufAddr curG.n + q)
        set eoff := s_ge.mem (grpEdgeOff bufAddr curG.n + q)
        have hvc := hverts_spec q hq
        have h_oc : off + cnt ≤ curG.n := hvc.2.1
        have hec_spec := hes_spec q hq
        have hest := heo_step q hq
        have hv_eq : (tab cnt fun t => s_k.mem (grpPartVerts bufAddr curG.n + off + t)) =
            (tab cnt fun t => s_gv.mem (grpPartVerts bufAddr curG.n + off + t)) :=
          tab_eq_of_eq fun t ht =>
            hsk_mid _ (by simp [grpPartVerts]; omega)
              (by simp [grpPartVerts, grpEdgeCnt]; omega)
        refine ⟨cnt, off, ecnt, eoff, hpartCnt_eq q hq, hpartOff_eq q (le_of_lt hq), rfl, rfl,
          hvc.2.1, hest.2, ?_, ?_, ?_, ?_, ?_⟩
        · constructor
          · ext u
            rw [List.mem_toFinset, hv_eq]
            have hu_iff : u ∈ tab cnt (fun t => s1_gv.mem (grpPartVerts bufAddr curG.n + off + t)) ↔
                u < curG.n ∧ s1_gv.mem (grpPartId bufAddr curG.n + u) = q := hvc.2.2 u
            change (u ∈ tab cnt fun t => s1_gv.mem (grpPartVerts bufAddr curG.n + off + t)) ↔ _
            rw [hu_iff]
            simp only [partX, Finset.mem_filter, Finset.mem_range]
            constructor
            · rintro ⟨hu, hpid⟩
              have hpid' : s_k.mem (grpPartId bufAddr curG.n + u) = q := (hpartId_eq u hu).trans hpid
              exact ⟨hu, ⟨by omega, ((huniq_spec u hu).2 q hq).mp hpid'⟩⟩
            · rintro ⟨hu, ⟨_, hq_eq⟩⟩
              have hpid' : s_k.mem (grpPartId bufAddr curG.n + u) = q := ((huniq_spec u hu).2 q hq).mpr hq_eq
              exact ⟨hu, (hpartId_eq u hu).symm.trans hpid'⟩
          · set uniq := tab k fun p => s_gv.mem (grpUniqLbl bufAddr curG.n + p)
            have hL_in : s_k.mem (grpUniqLbl bufAddr curG.n + q) ∈ uniq := by
              rw [huniq_eq q hq]
              have hq_len : q < uniq.length := by simp [uniq, tab, hq]
              have : s_gv.mem (grpUniqLbl bufAddr curG.n + q) = uniq[q] := by simp [uniq, tab]
              rw [this]; exact List.getElem_mem hq_len
            obtain ⟨u₀, hu₀, hu₀_eq⟩ := huniq_wit _ hL_in
            have hl2u₀ : label.getD (2 * u₀) 0 = s_k.mem (grpUniqLbl bufAddr curG.n + q) := by
              have h1 := hlbl_zk (2 * u₀) (by omega)
              rw [List.getD_eq_getElem _ _ (by omega)]
              exact h1.symm.trans hu₀_eq
            have hY_mem : {z ∈ Finset.range (2 * curG.n) | label.getD z 0 = s_k.mem (grpUniqLbl bufAddr curG.n + q)} ∈
                partsOf (twinGraph D curG) label := by
              rw [partsOf, Finset.mem_image]
              refine ⟨2 * u₀, ?_, ?_⟩
              · change 2 * u₀ ∈ Finset.range (2 * curG.n)
                rw [Finset.mem_range]; omega
              · ext z
                simp only [Finset.mem_filter, Finset.mem_range, Cited.Graph.verts]
                change z < 2 * curG.n ∧ label.getD z 0 = label.getD (2 * u₀) 0 ↔
                  z < 2 * curG.n ∧ label.getD z 0 = s_k.mem (grpUniqLbl bufAddr curG.n + q)
                constructor <;> rintro ⟨hz, hzl⟩ <;> exact ⟨hz, by first | exact hzl.trans hl2u₀ | exact hzl.trans hl2u₀.symm⟩
            exact hexpDec.2.1 _ hY_mem
        · intro u
          rw [hv_eq, hvc.2.2 u]
          constructor <;> rintro ⟨hu, h⟩ <;> refine ⟨hu, ?_⟩
          · rwa [hpartId_eq u hu]
          · rwa [hpartId_eq u hu] at h
        · rw [hv_eq]; exact hvc.1
        · intro u hu hpid
          rw [hpartId_eq u hu] at hpid
          have hl := hlid_spec u hu
          dsimp only [s_gv] at hpid
          rw [hpid] at hl
          have h_lid : s_gv.mem (grpLocalId bufAddr curG.n + u) < cnt := hl.1
          refine ⟨by rw [hlid_eq u hu]; exact h_lid, ?_⟩
          rw [hlid_eq u hu]
          have hmid : s_k.mem (grpPartVerts bufAddr curG.n + off + s_gv.mem (grpLocalId bufAddr curG.n + u)) =
              s_gv.mem (grpPartVerts bufAddr curG.n + off + s_gv.mem (grpLocalId bufAddr curG.n + u)) :=
            hsk_mid _ (by simp [grpPartVerts]; omega)
              (by simp [grpPartVerts, grpEdgeCnt]; omega)
          rw [hmid]
          exact hl.2
        · have hlo_all : ∀ u < curG.n, s_k.mem (grpPartId bufAddr curG.n + u) = s_nst.mem (grpPartId bufAddr curG.n + u) ∧
              s_k.mem (grpLocalId bufAddr curG.n + u) = s_nst.mem (grpLocalId bufAddr curG.n + u) := fun u hu =>
            ⟨hsk_lo _ (by simp [grpPartId, grpEdgeCnt]; omega),
             hsk_lo _ (by simp [grpLocalId, grpEdgeCnt]; omega)⟩
          have hedge_eq : ∀ j < curG.m,
              s_k.mem (curGAddr + 2 + 2 * j) = s_nst.mem (curGAddr + 2 + 2 * j) ∧
              s_k.mem (curGAddr + 3 + 2 * j) = s_nst.mem (curGAddr + 3 + 2 * j) := fun j hj =>
            ⟨hsk_lo _ (by simp [grpEdgeCnt]; omega), hsk_lo _ (by simp [grpEdgeCnt]; omega)⟩
          have hfilter_eq :
              (List.filter (fun j => decide (s_k.mem (grpPartId bufAddr curG.n + s_k.mem (curGAddr + 2 + 2 * j)) = q ∧
                s_k.mem (grpPartId bufAddr curG.n + s_k.mem (curGAddr + 3 + 2 * j)) = q)) (List.range curG.m)) =
              (List.filter (fun j => decide (s_nst.mem (grpPartId bufAddr curG.n + s_nst.mem (curGAddr + 2 + 2 * j)) = q ∧
                s_nst.mem (grpPartId bufAddr curG.n + s_nst.mem (curGAddr + 3 + 2 * j)) = q)) (List.range curG.m)) := by
            apply List.filter_congr
            intro j hj
            rw [List.mem_range] at hj
            have hvj := hV _ (List.getElem_mem hj)
            have he1 : s_nst.mem (curGAddr + 2 + 2 * j) = curG.edges[j].1 := graphAt_edge_fst hga_nst hj
            have he2 : s_nst.mem (curGAddr + 3 + 2 * j) = curG.edges[j].2 := graphAt_edge_snd hga_nst hj
            rw [(hedge_eq j hj).1, (hedge_eq j hj).2, he1, he2,
              (hlo_all _ hvj.1).1, (hlo_all _ hvj.2).1]
          have hmap_eq :
              List.map (fun j => (s_k.mem (grpLocalId bufAddr curG.n + s_k.mem (curGAddr + 2 + 2 * j)),
                s_k.mem (grpLocalId bufAddr curG.n + s_k.mem (curGAddr + 3 + 2 * j))))
                (List.filter (fun j => decide (s_k.mem (grpPartId bufAddr curG.n + s_k.mem (curGAddr + 2 + 2 * j)) = q ∧
                  s_k.mem (grpPartId bufAddr curG.n + s_k.mem (curGAddr + 3 + 2 * j)) = q)) (List.range curG.m)) =
              List.map (fun j => (s_nst.mem (grpLocalId bufAddr curG.n + s_nst.mem (curGAddr + 2 + 2 * j)),
                s_nst.mem (grpLocalId bufAddr curG.n + s_nst.mem (curGAddr + 3 + 2 * j))))
                (List.filter (fun j => decide (s_nst.mem (grpPartId bufAddr curG.n + s_nst.mem (curGAddr + 2 + 2 * j)) = q ∧
                  s_nst.mem (grpPartId bufAddr curG.n + s_nst.mem (curGAddr + 3 + 2 * j)) = q)) (List.range curG.m)) := by
            rw [hfilter_eq]
            apply List.map_congr_left
            intro j hj
            rw [List.mem_filter, List.mem_range] at hj
            have hjm : j < curG.edges.length := hj.1
            have hvj := hV _ (List.getElem_mem hjm)
            have he1 : s_nst.mem (curGAddr + 2 + 2 * j) = (curG.edges[j]'hjm).1 := graphAt_edge_fst hga_nst hjm
            have he2 : s_nst.mem (curGAddr + 3 + 2 * j) = (curG.edges[j]'hjm).2 := graphAt_edge_snd hga_nst hjm
            rw [(hedge_eq j hj.1).1, (hedge_eq j hj.1).2, he1, he2,
              (hlo_all _ hvj.1).2, (hlo_all _ hvj.2).2]
          rw [hmap_eq]
          exact hec_spec
      · intro u hu
        have hst_eq : s_k.mem (grpSameTwin bufAddr curG.n + u) = s_nst.mem (grpSameTwin bufAddr curG.n + u) :=
          hsk_lo _ (by simp [grpSameTwin, grpEdgeCnt]; omega)
        rw [hst_eq]
        have hdone_u := hdone_nst u hu
        simp only [grpSameTwin] at hdone_u ⊢
        have hgv_st := (hpart_spec u hu).1
        have hs_zk_2u : s_zk.mem (lblAddr + 2 * u) = label.getD (2 * u) 0 := by
          rw [hlbl_zk (2 * u) (by omega), List.getD_eq_getElem _ _ (by omega)]
        have hs_zk_2u1 : s_zk.mem (lblAddr + 2 * u + 1) = label.getD (2 * u + 1) 0 := by
          rw [Nat.add_assoc lblAddr (2 * u) 1, hlbl_zk (2 * u + 1) (by omega),
            List.getD_eq_getElem _ _ (by omega)]
        rw [hdone_u]
        refine ⟨by split_ifs <;> omega, ?_⟩
        simp only [Finset.mem_filter, Finset.mem_range, show 2 * u + 1 < 2 * curG.n by omega, true_and]
        rw [← hs_zk_2u, ← hs_zk_2u1]
        split_ifs with h0
        · simp only [ne_eq, not_true_eq_false, false_iff]
          intro h
          exact (hgv_st.mpr h.symm) h0
        · simp only [ne_eq, one_ne_zero, not_false_eq_true, true_iff]
          exact (hgv_st.mp h0).symm
      · rw [tab_eq_of_eq (fun q hq => huniq_eq q hq)]; exact huniq_pw
      · have h0 := hpartOff_eq 0 (Nat.zero_le _); simp only [Nat.add_zero] at h0; rw [h0]; exact hpo0
      · rw [hpartOff_eq k (le_refl _)]; exact hpok
      · intro q hq
        rw [hpartOff_eq (q + 1) (by omega), hpartOff_eq q (le_of_lt hq), hpartCnt_eq q hq]
        exact hpo_step q hq
      · exact heo0
      · exact heok
      · intro q hq; exact (heo_step q hq).1
      · rw [hm_tw_eq] at hc_td
        have hlog_eq : Nat.log 2 (curG.m + D * curG.n + 1) = Nat.log 2 (m_tw + 1) := rfl
        rw [hlog_eq] at hc_bt
        omega


end MinCostFlow.Expander
