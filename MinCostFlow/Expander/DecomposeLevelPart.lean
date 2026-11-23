/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MinCostFlow.Expander.DecomposeLevelCommon

import Mathlib.Tactic.Linarith

/-!
# Stage 2 Component Loop (`level_partLoop_runs`) for Single-Level Expander Decomposition

Proves `level_partLoop_runs`, covering the `q = 0..k-1` pruning/emission loop (`partLoopBody`)
of `levelProc`.
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-! ## 4. Stage 2: `level_partLoop_runs` -/

lemma level_partLoop_runs {w : ℕ} {p : Program} {b_csr b_part b_prune : ℕ}
    (mem₁ : ℕ → ℕ) (ω : ℕ → Bool) (curG : Cited.Graph)
    (curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
      keptVertAddr statePtr lvl D D_phi mCap csrAddr qAddr lblAddr zeroCursor' arena₀ total₀ k : ℕ)
    (label : List ℕ) (φ_B1 : ℝ) (st₁ : State)
    (hV : curG.IsValid) (hL : curG.IsLoopless) (h1D : 1 ≤ D) (h200 : 200 ≤ D_phi)
    (h1phi : 1 / (D_phi : ℝ) ≤ φ_B1)
    (hexpDec : IsExpanderDecomposition (twinGraph D curG) (1 / 200) φ_B1 label)
    (hga : GraphAt mem₁ curGAddr curG)
    (h_csr : MeetsContract w p b_csr (buildCsrContract w))
    (h_part : p.procs[b_part]? = some (partPruneProc b_csr b_prune))
    (h_prune : p.procs[b_prune]? = some pruneWrapProc)
    (hst₁_lvl : LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
      keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr st₁)
    (hst₁_mem : st₁.mem = mem₁) (hst₁_20 : st₁.regs 20 = k)
    (hk1 : 1 ≤ k) (hkn : k ≤ curG.n)
    (hstate_0 : mem₁ statePtr = arena₀) (hstate_1 : mem₁ (statePtr + 1) = zeroCursor')
    (hstate_2 : mem₁ (statePtr + 2) = total₀)
    (hkept0 : ∀ u < curG.n, mem₁ (keptVertAddr + u) = 0)
    (hgrp : ∀ q < k, ∃ cnt off ecnt eoff,
      mem₁ (grpPartCnt bufAddr curG.n + q) = cnt ∧
      mem₁ (grpPartOff bufAddr curG.n + q) = off ∧
      mem₁ (grpEdgeCnt bufAddr curG.n + q) = ecnt ∧
      mem₁ (grpEdgeOff bufAddr curG.n + q) = eoff ∧
      off + cnt ≤ curG.n ∧ eoff + ecnt ≤ curG.m ∧
      (have L := mem₁ (grpUniqLbl bufAddr curG.n + q);
       have Y := {z ∈ Finset.range (2 * curG.n) | label.getD z 0 = L};
       (tab cnt fun t => mem₁ (grpPartVerts bufAddr curG.n + off + t)).toFinset = partX curG.n Y ∧
       (twinGraph D curG).IsConductanceExpanderOn Y φ_B1) ∧
      (∀ u : ℕ, (u ∈ tab cnt fun t => mem₁ (grpPartVerts bufAddr curG.n + off + t)) ↔
        u < curG.n ∧ mem₁ (grpPartId bufAddr curG.n + u) = q) ∧
      List.Pairwise (· < ·) (tab cnt fun t => mem₁ (grpPartVerts bufAddr curG.n + off + t)) ∧
      (∀ u < curG.n, mem₁ (grpPartId bufAddr curG.n + u) = q →
        mem₁ (grpLocalId bufAddr curG.n + u) < cnt ∧
        mem₁ (grpPartVerts bufAddr curG.n + off + mem₁ (grpLocalId bufAddr curG.n + u)) = u) ∧
      (have partFn := fun u => mem₁ (grpPartId bufAddr curG.n + u);
       have localFn := fun u => mem₁ (grpLocalId bufAddr curG.n + u);
       have es := List.map (fun j => (localFn (mem₁ (curGAddr + 2 + 2 * j)),
         localFn (mem₁ (curGAddr + 3 + 2 * j))))
         (List.filter (fun j => decide (partFn (mem₁ (curGAddr + 2 + 2 * j)) = q ∧
           partFn (mem₁ (curGAddr + 3 + 2 * j)) = q)) (List.range curG.m));
       ecnt = es.length ∧ ∀ t (ht : t < es.length),
         mem₁ (grpPartEdges bufAddr curG.n + 2 * (eoff + t)) = es[t].1 ∧
         mem₁ (grpPartEdges bufAddr curG.n + 2 * (eoff + t) + 1) = es[t].2))
    (hsame : ∀ u < curG.n, mem₁ (grpSameTwin bufAddr curG.n + u) < 2 ^ w ∧
      (mem₁ (grpSameTwin bufAddr curG.n + u) ≠ 0 ↔
        2 * u + 1 ∈ {z ∈ Finset.range (2 * curG.n) | label.getD z 0 = label.getD (2 * u) 0}))
    (hpid : ∀ u < curG.n, mem₁ (grpPartId bufAddr curG.n + u) < k ∧
      ∀ q < k, mem₁ (grpPartId bufAddr curG.n + u) = q ↔
        label.getD (2 * u) 0 = mem₁ (grpUniqLbl bufAddr curG.n + q))
    (hpo0 : mem₁ (grpPartOff bufAddr curG.n) = 0)
    (hcnt_sum : mem₁ (grpPartOff bufAddr curG.n + k) = curG.n)
    (hpo_step : ∀ q < k, mem₁ (grpPartOff bufAddr curG.n + (q + 1)) =
      mem₁ (grpPartOff bufAddr curG.n + q) + mem₁ (grpPartCnt bufAddr curG.n + q))
    (heo0 : mem₁ (grpEdgeOff bufAddr curG.n) = 0)
    (hecnt_sum : mem₁ (grpEdgeOff bufAddr curG.n + k) ≤ curG.m)
    (heo_step : ∀ q < k, mem₁ (grpEdgeOff bufAddr curG.n + (q + 1)) =
      mem₁ (grpEdgeOff bufAddr curG.n + q) + mem₁ (grpEdgeCnt bufAddr curG.n + q))
    (hs_cg : statePtr + 3 ≤ curGAddr)
    (hcg_buf : curGAddr + 2 + 2 * curG.m ≤ bufAddr)
    (hbuf_w : bufAddr + groupBufSize curG.n curG.m + 2 < 2 ^ w)
    (hbuf_work : bufAddr + groupBufSize curG.n curG.m ≤ workAddr)
    (hwork_kept : workAddr + partWorkSize curG.n curG.m
      (4 * (4 * D_phi + 2) * (Nat.log 2 (2 * curG.m + 1) + 1) + 2) ≤ keptVertAddr)
    (hkept_arena : keptVertAddr + curG.n ≤ arena₀)
    (_harena_zc : arena₀ + 4 * curG.m ≤ zeroCursor')
    (harena_w : arena₀ + 4 * curG.m + 2 + curG.n < 2 ^ w)
    (hword_part : 8 * (4 * D_phi + 2) * curG.m + 4 * (4 * D_phi + 2) + 2 * curG.n + 2 * curG.m +
      (4 * (4 * D_phi + 2) * (Nat.log 2 (2 * curG.m + 1) + 1) + 2) + 16 < 2 ^ w)
    (hword_D : 2 * curG.m * D_phi + D + 4 < 2 ^ w)
    (hword_Dphi : D + 3 * D_phi < 2 ^ w)
    (hlvl_w : lvl < 2 ^ w) (htot_w : total₀ + curG.n < 2 ^ w) (hw16 : 16 ≤ 2 ^ w) :
    let H_max := 4 * (4 * D_phi + 2) * (Nat.log 2 (2 * curG.m + 1) + 1) + 2
    ∃ st' c arena₁, ∃ Rs : List (Finset ℕ), ∃ rawComps_lvl : List (ℕ × List ℕ),
      Runs w p ω (forRange 19 (.const 0) (.reg 20) (partLoopBody b_part)) st₁ .normal st' c ∧
      LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
        keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr st' ∧
      arena₀ ≤ arena₁ ∧ arena₁ ≤ arena₀ + 4 * curG.m ∧
      st'.mem statePtr = arena₁ ∧
      st'.mem (statePtr + 1) = zeroCursor' ∧
      st'.mem (statePtr + 2) = total₀ + rawComps_lvl.length ∧
      ListAt st'.mem arena₀ (rawComps_lvl.flatMap compRecord) ∧
      arena₁ = arena₀ + (rawComps_lvl.flatMap compRecord).length ∧
      rawComps_lvl.map (fun c => c.2.toFinset) = Rs.filter (fun R => decide (2 ≤ R.card)) ∧
      (∀ comp ∈ rawComps_lvl, comp.1 = lvl ∧ List.Pairwise (· < ·) comp.2 ∧ 2 ≤ comp.2.length) ∧
      Rs.length = k ∧
      Rs.Pairwise Disjoint ∧
      (∀ (q : ℕ) (hq : q < k),
        have L := mem₁ (grpUniqLbl bufAddr curG.n + q);
        have Y := {z ∈ Finset.range (2 * curG.n) | label.getD z 0 = L};
        have X := partX curG.n Y;
        have R := Rs.getD q ∅;
        R ⊆ X ∧
        (R = ∅ ∨ 2 ≤ R.card ∧ curG.IsConductanceExpanderOn R (1 / (3 * (D_phi : ℝ))) ∧
          ∀ v ∈ R, (1 : ℝ) / (3 * (D_phi : ℝ)) * (D : ℝ) ≤ (curG.degIn R v : ℝ)) ∧
        (curG.inside X).length - (curG.inside R).length ≤ 15 * (twinGraph D curG).cut Y) ∧
      (∀ u < curG.n, st'.mem (keptVertAddr + u) < 2 ^ w ∧
        (st'.mem (keptVertAddr + u) ≠ 0 ↔ ∃ (q : ℕ) (_ : q < k), u ∈ Rs.getD q ∅)) ∧
      (∀ a, ¬ (workAddr ≤ a ∧ a < workAddr + partWorkSize curG.n curG.m H_max) →
        ¬ (keptVertAddr ≤ a ∧ a < keptVertAddr + curG.n) →
        ¬ (arena₀ ≤ a ∧ a < arena₁) →
        a ≠ statePtr → a ≠ statePtr + 2 →
        st'.mem a = mem₁ a) ∧
      c ≤ 620 * curG.n +
        (590 + 720 * (4 * H_max + 14) ^ 2) * curG.m +
        curG.n * (1000 + 400 * (4 * H_max + 14) ^ 2) + 20 := by
  dsimp only
  set H_max := 4 * (4 * D_phi + 2) * (Nat.log 2 (2 * curG.m + 1) + 1) + 2
  have hw1 : 1 < 2 ^ w := by omega
  have hgrp_data : ∀ q < k, ∃ cnt off ecnt eoff,
      mem₁ (grpPartCnt bufAddr curG.n + q) = cnt ∧
      mem₁ (grpPartOff bufAddr curG.n + q) = off ∧
      mem₁ (grpEdgeCnt bufAddr curG.n + q) = ecnt ∧
      mem₁ (grpEdgeOff bufAddr curG.n + q) = eoff := fun q hq => by
    obtain ⟨cnt, off, ecnt, eoff, h⟩ := hgrp q hq
    exact ⟨cnt, off, ecnt, eoff, h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  let cntOf : ℕ → ℕ := fun q => mem₁ (grpPartCnt bufAddr curG.n + q)
  let offOf : ℕ → ℕ := fun q => mem₁ (grpPartOff bufAddr curG.n + q)
  let ecntOf : ℕ → ℕ := fun q => mem₁ (grpEdgeCnt bufAddr curG.n + q)
  let eoffOf : ℕ → ℕ := fun q => mem₁ (grpEdgeOff bufAddr curG.n + q)
  let Inv : ℕ → State → Prop := fun q st =>
    LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
      keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr st ∧
    st.regs 19 = q ∧ st.regs 20 = k ∧
    ∃ (arenaPtr : ℕ) (Rs : List (Finset ℕ)) (rawComps_lvl : List (ℕ × List ℕ)),
      arena₀ ≤ arenaPtr ∧ arenaPtr ≤ arena₀ + 4 * curG.m ∧
      st.mem statePtr = arenaPtr ∧
      st.mem (statePtr + 1) = zeroCursor' ∧
      st.mem (statePtr + 2) = total₀ + rawComps_lvl.length ∧
      rawComps_lvl.length ≤ q ∧
      ListAt st.mem arena₀ (rawComps_lvl.flatMap compRecord) ∧
      arenaPtr = arena₀ + (rawComps_lvl.flatMap compRecord).length ∧
      rawComps_lvl.map (fun c => c.2.toFinset) = Rs.filter (fun R => decide (2 ≤ R.card)) ∧
      (∀ comp ∈ rawComps_lvl, comp.1 = lvl ∧ List.Pairwise (· < ·) comp.2 ∧ 2 ≤ comp.2.length) ∧
      Rs.length = q ∧
      Rs.Pairwise Disjoint ∧
      (∀ (p' : ℕ) (hp' : p' < q),
        have L := mem₁ (grpUniqLbl bufAddr curG.n + p');
        have Y := {z ∈ Finset.range (2 * curG.n) | label.getD z 0 = L};
        have X := partX curG.n Y;
        have R := Rs.getD p' ∅;
        R ⊆ X ∧
        (R = ∅ ∨ 2 ≤ R.card ∧ curG.IsConductanceExpanderOn R (1 / (3 * (D_phi : ℝ))) ∧
          ∀ v ∈ R, (1 : ℝ) / (3 * (D_phi : ℝ)) * (D : ℝ) ≤ (curG.degIn R v : ℝ)) ∧
        (curG.inside X).length - (curG.inside R).length ≤ 15 * (twinGraph D curG).cut Y) ∧
      (∀ u < curG.n, st.mem (keptVertAddr + u) < 2 ^ w ∧
        (st.mem (keptVertAddr + u) ≠ 0 ↔ ∃ (p' : ℕ) (hp' : p' < q), u ∈ Rs.getD p' ∅)) ∧
      (∀ a, ¬ (workAddr ≤ a ∧ a < workAddr + partWorkSize curG.n curG.m H_max) →
        ¬ (keptVertAddr ≤ a ∧ a < keptVertAddr + curG.n) →
        ¬ (arena₀ ≤ a ∧ a < arenaPtr) →
        a ≠ statePtr → a ≠ statePtr + 2 →
        st.mem a = mem₁ a)
  have hstep : ∀ q st, 0 ≤ q → q < k → Inv q st →
      ∃ st₁ c₁, Runs w p ω (partLoopBody b_part) st .normal st₁ c₁ ∧
        c₁ ≤ partPruneCost (cntOf q) (ecntOf q) D_phi + 40 ∧ st₁.regs 19 = q ∧
        Inv (q + 1) { st₁ with regs := Function.update st₁.regs 19 (q + 1) } := by
    intro q st _ hqk hinv
    rcases hinv with ⟨hlvl, hr19, hr20, arenaPtr, Rs, rawComps_lvl, ha0_le, ha_ub, hst_ptr0,
      hst_ptr1, hst_ptr2, hrc_len, hlist_ar, hptr_eq, hrc_map, hrc_mem, hRs_len, hRs_disj,
      hRs_spec, hkept_inv, hfr_st⟩
    have hq_grp := hgrp q hqk
    rcases hq_grp with ⟨cnt, off, ecnt, eoff, hq_cnt, hq_off, hq_ecnt, hq_eoff, hoff_cnt,
      heoff_ecnt, hX_exp, hverts_iff, hverts_pw, hlid_spec, hes_spec⟩
    have hcnt_eq : cnt = cntOf q := hq_cnt.symm
    have hecnt_eq : ecnt = ecntOf q := hq_ecnt.symm
    -- All read-only memory (`< workAddr`, outside `statePtr, statePtr+2`) equals `mem₁`
    have hst_lt_work : ∀ a < workAddr, a ≠ statePtr → a ≠ statePtr + 2 → st.mem a = mem₁ a :=
      fun a ha1 ha2 ha3 => hfr_st a (by omega) (by omega) (by omega) ha2 ha3
    have hga_st : GraphAt st.mem curGAddr curG := by
      have heq : ∀ a, curGAddr ≤ a → a < curGAddr + 2 + 2 * curG.m → st.mem a = mem₁ a :=
        fun a ha1 ha2 => hst_lt_work a (by omega) (by omega) (by omega)
      exact graphAt_of_cells
        (by rw [heq _ (le_refl _) (by omega)]; exact graphAt_n hga)
        (by rw [heq _ (by omega) (by omega)]; exact graphAt_m hga)
        (fun t ht => ⟨
          by rw [heq _ (by omega) (by omega)]; exact graphAt_edge_fst hga ht,
          by rw [heq _ (by omega) (by omega)]; exact graphAt_edge_snd hga ht⟩)
    have hbuf_eq : ∀ a, bufAddr ≤ a → a < bufAddr + groupBufSize curG.n curG.m → st.mem a = mem₁ a :=
      fun a ha1 ha2 => hst_lt_work a (by omega) (by omega) (by omega)
    have hpr_runs := partPrune_runs (b_csr := b_csr) (b_prune := b_prune) h_csr h_prune st.mem st.pos ω
      curGAddr bufAddr q lvl D D_phi workAddr keptVertAddr arenaPtr curG hV hL h1D h200
      label φ_B1 h1phi hexpDec hga_st (by omega) k cnt off ecnt eoff hk1 hqk hkn
      (by rw [hbuf_eq _ (by simp [grpPartCnt]; omega) (by simp [grpPartCnt, groupBufSize]; omega)]; exact hq_cnt)
      (by rw [hbuf_eq _ (by simp [grpPartOff]; omega) (by simp [grpPartOff, groupBufSize]; omega)]; exact hq_off)
      (by rw [hbuf_eq _ (by simp [grpEdgeCnt]; omega) (by simp [grpEdgeCnt, groupBufSize]; omega)]; exact hq_ecnt)
      (by rw [hbuf_eq _ (by simp [grpEdgeOff]; omega) (by simp [grpEdgeOff, groupBufSize]; omega)]; exact hq_eoff)
      hoff_cnt heoff_ecnt
      (by
        dsimp only
        rw [hbuf_eq _ (by dsimp [grpUniqLbl]; omega) (by dsimp [grpUniqLbl, groupBufSize]; omega)]
        rw [tab_eq_of_eq (f := fun t => st.mem (grpPartVerts bufAddr curG.n + off + t))
          (g := fun t => mem₁ (grpPartVerts bufAddr curG.n + off + t))
          (fun t ht => hbuf_eq _ (by dsimp [grpPartVerts]; omega)
            (by dsimp [grpPartVerts, groupBufSize]; omega))]
        exact hX_exp)
      (fun u hu => by
        rw [hbuf_eq _ (by dsimp [grpSameTwin]; omega) (by dsimp [grpSameTwin, groupBufSize]; omega)]
        exact hsame u hu)
      (fun u hu => by
        rw [hbuf_eq _ (by dsimp [grpPartId]; omega) (by dsimp [grpPartId, groupBufSize]; omega),
          hbuf_eq _ (by dsimp [grpUniqLbl]; omega) (by dsimp [grpUniqLbl, groupBufSize]; omega)]
        exact ⟨(hpid u hu).1, (hpid u hu).2 q hqk⟩)
      (fun u => by
        rw [tab_eq_of_eq (f := fun t => st.mem (grpPartVerts bufAddr curG.n + off + t))
          (g := fun t => mem₁ (grpPartVerts bufAddr curG.n + off + t))
          (fun t ht => hbuf_eq _ (by dsimp [grpPartVerts]; omega)
            (by dsimp [grpPartVerts, groupBufSize]; omega))]
        refine (hverts_iff u).trans ?_
        constructor <;> rintro ⟨hu, hq'⟩ <;> refine ⟨hu, ?_⟩
        · rw [hbuf_eq _ (by dsimp [grpPartId]; omega) (by dsimp [grpPartId, groupBufSize]; omega)]; exact hq'
        · rwa [hbuf_eq _ (by dsimp [grpPartId]; omega) (by dsimp [grpPartId, groupBufSize]; omega)] at hq')
      (by
        rw [tab_eq_of_eq (f := fun t => st.mem (grpPartVerts bufAddr curG.n + off + t))
          (g := fun t => mem₁ (grpPartVerts bufAddr curG.n + off + t))
          (fun t ht => hbuf_eq _ (by dsimp [grpPartVerts]; omega)
            (by dsimp [grpPartVerts, groupBufSize]; omega))]
        exact hverts_pw)
      (fun u hu hpid_u => by
        rw [hbuf_eq _ (by simp [grpPartId]; omega) (by simp [grpPartId, groupBufSize]; omega)] at hpid_u
        rw [hbuf_eq _ (by simp [grpLocalId]; omega) (by simp [grpLocalId, groupBufSize]; omega)]
        have hl := hlid_spec u hu hpid_u
        refine ⟨hl.1, ?_⟩
        rw [hbuf_eq _ (by simp [grpPartVerts]; omega) (by simp [grpPartVerts, groupBufSize]; omega)]
        exact hl.2)
      (by
        dsimp only
        have heq_id : ∀ u < curG.n, st.mem (grpPartId bufAddr curG.n + u) = mem₁ (grpPartId bufAddr curG.n + u) ∧
            st.mem (grpLocalId bufAddr curG.n + u) = mem₁ (grpLocalId bufAddr curG.n + u) := fun u hu =>
          ⟨hbuf_eq _ (by simp [grpPartId]; omega) (by simp [grpPartId, groupBufSize]; omega),
           hbuf_eq _ (by simp [grpLocalId]; omega) (by simp [grpLocalId, groupBufSize]; omega)⟩
        have heq_ed : ∀ j < curG.m, st.mem (curGAddr + 2 + 2 * j) = mem₁ (curGAddr + 2 + 2 * j) ∧
            st.mem (curGAddr + 3 + 2 * j) = mem₁ (curGAddr + 3 + 2 * j) := fun j hj =>
          ⟨hst_lt_work _ (by omega) (by omega) (by omega), hst_lt_work _ (by omega) (by omega) (by omega)⟩
        have hfilt : List.filter (fun j => decide (st.mem (grpPartId bufAddr curG.n + st.mem (curGAddr + 2 + 2 * j)) = q ∧
            st.mem (grpPartId bufAddr curG.n + st.mem (curGAddr + 3 + 2 * j)) = q)) (List.range curG.m) =
            List.filter (fun j => decide (mem₁ (grpPartId bufAddr curG.n + mem₁ (curGAddr + 2 + 2 * j)) = q ∧
            mem₁ (grpPartId bufAddr curG.n + mem₁ (curGAddr + 3 + 2 * j)) = q)) (List.range curG.m) := by
          apply List.filter_congr; intro j hj; rw [List.mem_range] at hj
          have hvj := hV _ (List.getElem_mem hj)
          have h1 : mem₁ (curGAddr + 2 + 2 * j) = curG.edges[j].1 := graphAt_edge_fst hga hj
          have h2 : mem₁ (curGAddr + 3 + 2 * j) = curG.edges[j].2 := graphAt_edge_snd hga hj
          rw [(heq_ed j hj).1, (heq_ed j hj).2, h1, h2, (heq_id _ hvj.1).1, (heq_id _ hvj.2).1]
        have hmap : List.map (fun j => (st.mem (grpLocalId bufAddr curG.n + st.mem (curGAddr + 2 + 2 * j)),
            st.mem (grpLocalId bufAddr curG.n + st.mem (curGAddr + 3 + 2 * j))))
            (List.filter (fun j => decide (st.mem (grpPartId bufAddr curG.n + st.mem (curGAddr + 2 + 2 * j)) = q ∧
              st.mem (grpPartId bufAddr curG.n + st.mem (curGAddr + 3 + 2 * j)) = q)) (List.range curG.m)) =
            List.map (fun j => (mem₁ (grpLocalId bufAddr curG.n + mem₁ (curGAddr + 2 + 2 * j)),
              mem₁ (grpLocalId bufAddr curG.n + mem₁ (curGAddr + 3 + 2 * j))))
            (List.filter (fun j => decide (mem₁ (grpPartId bufAddr curG.n + mem₁ (curGAddr + 2 + 2 * j)) = q ∧
              mem₁ (grpPartId bufAddr curG.n + mem₁ (curGAddr + 3 + 2 * j)) = q)) (List.range curG.m)) := by
          rw [hfilt]; apply List.map_congr_left; intro j hj
          rw [List.mem_filter, List.mem_range] at hj
          have hj_len : j < curG.edges.length := hj.1
          have hvj := hV _ (List.getElem_mem hj_len)
          have h1 : mem₁ (curGAddr + 2 + 2 * j) = (curG.edges[j]'hj_len).1 := graphAt_edge_fst hga hj_len
          have h2 : mem₁ (curGAddr + 3 + 2 * j) = (curG.edges[j]'hj_len).2 := graphAt_edge_snd hga hj_len
          have hl1 := (heq_id _ hvj.1).2
          have hl2 := (heq_id _ hvj.2).2
          rw [(heq_ed j hj_len).1, (heq_ed j hj_len).2, h1, h2, hl1, hl2]
        rw [hmap]
        refine ⟨hes_spec.1, fun t ht => ?_⟩
        have ht' : t < ecnt := hes_spec.1 ▸ ht
        rw [hbuf_eq _ (by dsimp [grpPartEdges]; omega) (by dsimp [grpPartEdges, groupBufSize]; omega),
          hbuf_eq _ (by dsimp [grpPartEdges]; omega) (by dsimp [grpPartEdges, groupBufSize]; omega)]
        exact hes_spec.2 t ht)
      hbuf_w hbuf_work hwork_kept (by omega) (by omega) hword_part hword_D hword_Dphi hlvl_w hw16
    rcases hpr_runs with ⟨st_p, c_p, arenaPtr', R, R_list, hr_p, hc_p, ha_le, ha_ub',
      hRl_pw, hRl_set, hbranch, hfr_p, hR_subX, hR_spec, hinside_loss⟩
    rw [hcnt_eq, hecnt_eq] at hc_p
    -- 1. `.assign 21 (.load (.reg 9))`
    let s1 : State := { st with regs := Function.update st.regs 21 arenaPtr }
    have hs1_run : Runs w p ω (.assign 21 (.load (.reg 9))) st .normal s1 3 :=
      runs_assign_iff.mpr ⟨arenaPtr, by simp [Expr.eval, hlvl.2.2.2.2.2.2.2.2.2.1, hst_ptr0], rfl, rfl, rfl⟩
    -- 2. `.call 22 b_part [...]`
    let pargs := [curGAddr, bufAddr, q, lvl, D, D_phi, workAddr, keptVertAddr, arenaPtr]
    have heval_pargs : evalArgs w s1
        [.reg 0, .reg 6, .reg 19, .reg 10, .reg 11, .reg 12, .reg 7, .reg 8, .reg 21] = some pargs := by
      simp [evalArgs, Expr.eval, s1, pargs, hlvl.1, hlvl.2.2.2.2.2.2.1, hr19, hlvl.2.2.2.2.2.2.2.2.2.2.1,
        hlvl.2.2.2.2.2.2.2.2.2.2.2.1, hlvl.2.2.2.2.2.2.2.2.2.2.2.2.1, hlvl.2.2.2.2.2.2.2.1,
        hlvl.2.2.2.2.2.2.2.2.1]
    have hstart_eq : startState pargs s1.mem s1.pos = startState pargs st.mem st.pos := rfl
    let s2 : State := { mem := st_p.mem, regs := Function.update s1.regs 22 arenaPtr', pos := st_p.pos }
    have hs2_run : Runs w p ω (.call 22 b_part
        [.reg 0, .reg 6, .reg 19, .reg 10, .reg 11, .reg 12, .reg 7, .reg 8, .reg 21])
        s1 .normal s2 (9 + c_p + 1) :=
      runs_call_iff.mpr ⟨pargs, partPruneProc b_csr b_prune, .returned arenaPtr', st_p, c_p,
        heval_pargs, h_part, by simpa [startState] using hr_p, rfl, rfl, by simp [argsSize, Expr.size]⟩
    -- 3. Conditional arena pointer & component counter update
    have hRs_next_disj : (Rs ++ [R]).Pairwise Disjoint := by
      rw [List.pairwise_append]
      refine ⟨hRs_disj, List.pairwise_singleton _ _, fun T hT R' hR' => ?_⟩
      simp only [List.mem_singleton] at hR'; subst hR'
      rw [List.mem_iff_getElem] at hT
      obtain ⟨p', hp', rfl⟩ := hT
      have hTp := (hRs_spec p' (by omega)).1
      rw [List.getD_eq_getElem _ _ hp'] at hTp
      refine Finset.disjoint_left.mpr fun z hzT hzR => ?_
      have hzXp := hTp hzT
      simp only [partX, Finset.mem_filter, Finset.mem_range] at hzXp
      have hzXq := hR_subX hzR
      simp only [partX, Finset.mem_filter, Finset.mem_range] at hzXq
      have hbuf_uq : st.mem (grpUniqLbl bufAddr curG.n + q) = mem₁ (grpUniqLbl bufAddr curG.n + q) :=
        hbuf_eq _ (by dsimp [grpUniqLbl]; omega) (by dsimp [grpUniqLbl, groupBufSize]; omega)
      have hLq : label.getD (2 * z) 0 = mem₁ (grpUniqLbl bufAddr curG.n + q) :=
        hzXq.2.2.trans hbuf_uq
      have hLp : label.getD (2 * z) 0 = mem₁ (grpUniqLbl bufAddr curG.n + p') := hzXp.2.2
      have hz_lt : z < curG.n := hzXp.1
      have hp_eq := (hpid z hz_lt).2 p' (by omega) |>.mpr hLp
      have hq_eq := (hpid z hz_lt).2 q hqk |>.mpr hLq
      omega
    have hRs_next_spec : ∀ (p' : ℕ) (hp' : p' < q + 1),
        have L := mem₁ (grpUniqLbl bufAddr curG.n + p');
        have Y := {z ∈ Finset.range (2 * curG.n) | label.getD z 0 = L};
        have X := partX curG.n Y;
        have R' := (Rs ++ [R]).getD p' ∅;
        R' ⊆ X ∧
        (R' = ∅ ∨ 2 ≤ R'.card ∧ curG.IsConductanceExpanderOn R' (1 / (3 * (D_phi : ℝ))) ∧
          ∀ v ∈ R', (1 : ℝ) / (3 * (D_phi : ℝ)) * (D : ℝ) ≤ (curG.degIn R' v : ℝ)) ∧
        (curG.inside X).length - (curG.inside R').length ≤ 15 * (twinGraph D curG).cut Y := by
      intro p' hp'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hp' with hlt | hp_eq
      · have hs := hRs_spec p' hlt
        rw [List.getD_eq_getElem _ _ (by simp [hRs_len]; omega),
          List.getElem_append_left (by omega : p' < Rs.length),
          ← List.getD_eq_getElem _ _ (by omega : p' < Rs.length)]
        exact hs
      · subst p'
        dsimp only
        have hbuf_uq : st.mem (grpUniqLbl bufAddr curG.n + q) = mem₁ (grpUniqLbl bufAddr curG.n + q) :=
          hbuf_eq _ (by dsimp [grpUniqLbl]; omega) (by dsimp [grpUniqLbl, groupBufSize]; omega)
        rw [List.getD_eq_getElem _ _ (by simp [hRs_len]),
          List.getElem_append_right (by omega : Rs.length ≤ q)]
        simp only [hRs_len, Nat.sub_self, List.getElem_singleton]
        rw [hbuf_uq] at hR_subX hinside_loss
        exact ⟨hR_subX, hR_spec, hinside_loss⟩
    have hs2_21 : s2.regs 21 = arenaPtr := by simp [s2, s1]
    have hs2_22 : s2.regs 22 = arenaPtr' := by simp [s2]
    have hs2_9 : s2.regs 9 = statePtr := by simp [s2, s1, hlvl.2.2.2.2.2.2.2.2.2.1]
    have hs2_kept : ∀ u < curG.n, s2.mem (keptVertAddr + u) = st_p.mem (keptVertAddr + u) := fun _ _ => rfl
    have hs2_fr : ∀ a, ¬ (workAddr ≤ a ∧ a < workAddr + partWorkSize curG.n curG.m H_max) →
        ¬ (keptVertAddr ≤ a ∧ a < keptVertAddr + curG.n) →
        ¬ (arenaPtr ≤ a ∧ a < arenaPtr') → s2.mem a = st.mem a := hfr_p
    have hs2_ptr0 : s2.mem statePtr = arenaPtr := by
      rw [hs2_fr _ (by omega) (by omega) (by omega), hst_ptr0]
    have hs2_ptr1 : s2.mem (statePtr + 1) = zeroCursor' := by
      rw [hs2_fr _ (by omega) (by omega) (by omega), hst_ptr1]
    have hs2_ptr2 : s2.mem (statePtr + 2) = total₀ + rawComps_lvl.length := by
      rw [hs2_fr _ (by omega) (by omega) (by omega), hst_ptr2]
    by_cases hR0 : R = ∅
    · subst hR0
      simp only [↓reduceIte] at hbranch
      rcases hbranch with ⟨harena_eq, hkept_eq⟩
      rw [harena_eq] at hs2_22 hs2_fr
      have hcond : Runs w p ω
          (.cond (.bin .lt (.reg 21) (.reg 22))
            (.seq (.store (.reg 9) (.reg 22))
              (.store (.bin .add (.reg 9) (.const 2))
                (.bin .add (.load (.bin .add (.reg 9) (.const 2))) (.const 1)))) .nop)
          s2 .normal s2 5 :=
        runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, BinOp.eval, hs2_21, hs2_22], by simp [runs_nop_iff], rfl⟩
      have hbody_run := runs_seq hs1_run (runs_seq hs2_run hcond)
      rw [← partLoopBody_eq] at hbody_run
      refine ⟨s2, _, hbody_run, by omega, by simp [s2, s1, hr19], ?_⟩
      refine ⟨lvlRegs_of_eq (fun r hr => by
          dsimp [s2, s1]
          rw [Function.update_of_ne (by omega : r ≠ 19), Function.update_of_ne (by omega : r ≠ 22),
            Function.update_of_ne (by omega : r ≠ 21)]) hlvl,
        by simp [s2, s1], by simp [s2, s1, hr20],
        arenaPtr, Rs ++ [∅], rawComps_lvl, ha0_le, ha_ub, hs2_ptr0, hs2_ptr1, hs2_ptr2,
        by omega, ?_, hptr_eq, ?_, hrc_mem, by simp [hRs_len], hRs_next_disj, hRs_next_spec, ?_, ?_⟩
      · intro t ht; rw [hs2_fr _ (by omega) (by omega) (by omega)]; exact hlist_ar t ht
      · rw [hrc_map, List.filter_append]; simp
      · intro u hu
        rw [hs2_kept u hu, hkept_eq u hu]
        refine ⟨(hkept_inv u hu).1, ?_⟩
        rw [(hkept_inv u hu).2]
        constructor
        · rintro ⟨p', hp', hu'⟩
          refine ⟨p', by omega, ?_⟩
          rw [List.getD_eq_getElem _ _ (by simp [hRs_len]; omega), List.getElem_append_left (by omega)]
          rwa [List.getD_eq_getElem _ _ (by omega)] at hu'
        · rintro ⟨p', hp', hu'⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hp' with hlt | hp_eq
          · refine ⟨p', hlt, ?_⟩
            have hget_lt : (Rs ++ [∅]).getD p' ∅ = Rs.getD p' ∅ := by
              rw [List.getD_eq_getElem _ _ (by simp [hRs_len]; omega),
                List.getElem_append_left (by omega : p' < Rs.length),
                ← List.getD_eq_getElem _ _ (by omega : p' < Rs.length)]
            rwa [hget_lt] at hu'
          · subst p'
            rw [List.getD_eq_getElem _ _ (by simp [hRs_len]), List.getElem_append_right (by omega : Rs.length ≤ q)] at hu'
            simp only [List.getElem_singleton] at hu'
            exact absurd hu' (Finset.notMem_empty _)
      · intro a h1 h2 h3 h4 h5
        rw [hs2_fr a h1 h2 (by omega)]
        exact hfr_st a h1 h2 h3 h4 h5
    · simp only [hR0, ↓reduceIte] at hbranch
      rcases hbranch with ⟨hRl_2, ha_eq', hRl_at, hkept_new⟩
      have hRl_card : R_list.length = R.card := by
        rw [← hRl_set, List.toFinset_card_of_nodup (hRl_pw.imp fun hab => Nat.ne_of_lt hab)]
      have hR_card2 : 2 ≤ R.card := by omega
      have hR_spec_ne : 2 ≤ R.card ∧ curG.IsConductanceExpanderOn R (1 / (3 * (D_phi : ℝ))) ∧
          ∀ v ∈ R, (1 : ℝ) / (3 * (D_phi : ℝ)) * (D : ℝ) ≤ (curG.degIn R v : ℝ) :=
        hR_spec.resolve_left hR0
      let rawComps' := rawComps_lvl ++ [(lvl, R_list)]
      have hrc_map' : rawComps'.map (fun c => c.2.toFinset) = (Rs ++ [R]).filter (fun R' => decide (2 ≤ R'.card)) := by
        simp [rawComps', hrc_map, List.filter_append, hRl_set, hR_card2]
      have ha_ub_new : arenaPtr' ≤ arena₀ + 4 * curG.m := by
        have hlen_flat : (rawComps'.flatMap compRecord).length =
            (rawComps_lvl.flatMap compRecord).length + (2 + R_list.length) := by
          simp [rawComps', List.flatMap_append, compRecord, List.flatMap_cons, List.flatMap_nil]
          omega
        have harena_eq_len : arenaPtr' = arena₀ + (rawComps'.flatMap compRecord).length := by
          omega
        have hlen_rec_aux : ∀ (l : List (ℕ × List ℕ)), (∀ c ∈ l, List.Pairwise (· < ·) c.2) →
            (l.flatMap compRecord).length = ((l.map fun c => c.2.toFinset).map fun R' => 2 + R'.card).sum := by
          intro l hl
          induction l with
          | nil => simp
          | cons c cs ih =>
            simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons]
            rw [ih fun x hx => hl x (List.mem_cons_of_mem c hx)]
            have hnodup : c.2.Nodup := (hl c List.mem_cons_self).imp fun hab => Nat.ne_of_lt hab
            simp [compRecord, List.toFinset_card_of_nodup hnodup]
            omega
        have hsum_rec : (rawComps'.flatMap compRecord).length =
            ((rawComps'.map (fun c => c.2.toFinset)).map fun R' => 2 + R'.card).sum := by
          refine hlen_rec_aux rawComps' fun c hc => ?_
          rcases List.mem_append.mp hc with hc1 | hc2
          · exact (hrc_mem c hc1).2.1
          · simp only [List.mem_singleton] at hc2; subst hc2; exact hRl_pw
        have hfilt_disj : ((Rs ++ [R]).filter fun R' => decide (2 ≤ R'.card)).Pairwise Disjoint :=
          hRs_next_disj.filter _
        have hle_sum : ((rawComps'.map (fun c => c.2.toFinset)).map fun R' => 2 + R'.card).sum ≤
            4 * ((rawComps'.map (fun c => c.2.toFinset)).map fun R' => (curG.inside R').length).sum := by
          rw [← List.sum_map_mul_left]
          apply List.Forall₂.sum_le_sum
          rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
          refine List.forall₂_same.mpr fun R' hR' => ?_
          rw [hrc_map'] at hR'
          rw [List.mem_filter, List.mem_iff_getElem] at hR'
          rcases hR' with ⟨⟨p', hp', rfl⟩, hcard⟩
          have hp_spec := hRs_next_spec p' (by simp [hRs_len] at hp'; omega)
          rw [List.getD_eq_getElem _ _ hp'] at hp_spec
          have hne' : (Rs ++ [R])[p'] ≠ ∅ := by
            intro h0; rw [h0] at hcard; simp at hcard
          exact arena_record_le_four_inside h1D (by omega) (decide_eq_true_eq.mp hcard)
            (hp_spec.2.1.resolve_left hne').2.2
        have hle_m := sum_filter_inside_disjoint_le _ hfilt_disj curG.edges
        rw [← hrc_map'] at hle_m
        calc arenaPtr' = arena₀ + (rawComps'.flatMap compRecord).length := harena_eq_len
          _ = arena₀ + ((rawComps'.map (fun c => c.2.toFinset)).map fun R' => 2 + R'.card).sum := by rw [hsum_rec]
          _ ≤ arena₀ + 4 * ((rawComps'.map (fun c => c.2.toFinset)).map fun R' => (curG.inside R').length).sum :=
              Nat.add_le_add_left hle_sum _
          _ ≤ arena₀ + 4 * curG.edges.length := Nat.add_le_add_left (Nat.mul_le_mul_left 4 hle_m) _
          _ = arena₀ + 4 * curG.m := rfl
      have ha_lt_a' : arenaPtr < arenaPtr' := by omega
      have harena'_w : arenaPtr' < 2 ^ w := by omega
      let s3 : State := { s2 with mem := Function.update s2.mem statePtr arenaPtr' }
      let s4 : State := { s3 with mem := Function.update s3.mem (statePtr + 2) (total₀ + rawComps_lvl.length + 1) }
      have hs3_run : Runs w p ω (.store (.reg 9) (.reg 22)) s2 .normal s3 3 :=
        runs_store_iff.mpr ⟨statePtr, arenaPtr', by simp [Expr.eval, hs2_9], by simp [Expr.eval, hs2_22], rfl, rfl, rfl⟩
      have htot_next_w : total₀ + rawComps_lvl.length + 1 < 2 ^ w := by omega
      have hs4_run : Runs w p ω
          (.store (.bin .add (.reg 9) (.const 2))
            (.bin .add (.load (.bin .add (.reg 9) (.const 2))) (.const 1))) s3 .normal s4 10 := by
        have hw2 : (2 : ℕ) < 2 ^ w := by omega
        have ha_s3 : (Expr.bin .add (.reg 9) (.const 2)).eval w s3 = some (statePtr + 2) := by
          simp [Expr.eval, BinOp.eval, s3, hs2_9, hw2, show statePtr + 2 < 2 ^ w by omega]
        have hne_sp : statePtr + 2 ≠ statePtr := by omega
        have hload_ptr2 : (Expr.load (.bin .add (.reg 9) (.const 2))).eval w s3 =
            some (total₀ + rawComps_lvl.length) := by
          simp [Expr.eval, BinOp.eval, s3, hs2_9, hw2, show statePtr + 2 < 2 ^ w by omega, hs2_ptr2]
        refine runs_store_iff.mpr ⟨statePtr + 2, total₀ + rawComps_lvl.length + 1, ha_s3, ?_, rfl, rfl, rfl⟩
        rw [Expr.eval, hload_ptr2]
        simp [Expr.eval, BinOp.eval, hw1, htot_next_w]
      have hcond : Runs w p ω
          (.cond (.bin .lt (.reg 21) (.reg 22))
            (.seq (.store (.reg 9) (.reg 22))
              (.store (.bin .add (.reg 9) (.const 2))
                (.bin .add (.load (.bin .add (.reg 9) (.const 2))) (.const 1)))) .nop)
          s2 .normal s4 18 :=
        runs_cond_iff.mpr ⟨1, 14, by simp [Expr.eval, BinOp.eval, hw1, hs2_21, hs2_22, ha_lt_a'],
          runs_seq hs3_run hs4_run, rfl⟩
      have hbody_run := runs_seq hs1_run (runs_seq hs2_run hcond)
      rw [← partLoopBody_eq] at hbody_run
      refine ⟨s4, _, hbody_run, by omega, by simp [s4, s3, s2, s1, hr19], ?_⟩
      refine ⟨lvlRegs_of_eq (fun r hr => by
          dsimp [s4, s3, s2, s1]
          rw [Function.update_of_ne (by omega : r ≠ 19), Function.update_of_ne (by omega : r ≠ 22),
            Function.update_of_ne (by omega : r ≠ 21)]) hlvl,
        by simp [s4, s3, s2, s1], by simp [s4, s3, s2, s1, hr20],
        arenaPtr', Rs ++ [R], rawComps', ha0_le.trans ha_le, ha_ub_new,
        by dsimp [s4, s3]; rw [Function.update_of_ne (by omega), Function.update_self],
        by dsimp [s4, s3]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hs2_ptr1,
        by dsimp [s4]; rw [Function.update_self]; simp [rawComps']; omega,
        by simp [rawComps']; omega, ?_, ?_, hrc_map', ?_, by simp [hRs_len], hRs_next_disj,
        hRs_next_spec, ?_, ?_⟩
      · intro t ht
        have hlt_or : t < (rawComps_lvl.flatMap compRecord).length ∨
            (rawComps_lvl.flatMap compRecord).length ≤ t := lt_or_ge _ _
        dsimp only [s4, s3]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        rcases hlt_or with hlt | hge
        · have hget_lt : (rawComps'.flatMap compRecord)[t]'ht = (rawComps_lvl.flatMap compRecord)[t]'hlt := by
            dsimp [rawComps']; simp only [List.flatMap_append]; exact List.getElem_append_left hlt
          rw [hget_lt, hs2_fr _ (by omega) (by omega) (by omega)]
          exact hlist_ar t hlt
        · have hsub_lt : t - (rawComps_lvl.flatMap compRecord).length < ([lvl, R_list.length] ++ R_list).length := by
            simp only [rawComps', List.flatMap_append, List.length_append, List.flatMap_cons,
              List.flatMap_nil, List.append_nil, compRecord, List.length_cons, List.length_nil] at ht ⊢
            omega
          have hget_ge : (rawComps'.flatMap compRecord)[t]'ht = ([lvl, R_list.length] ++ R_list)[t - (rawComps_lvl.flatMap compRecord).length]'hsub_lt := by
            dsimp [rawComps']; simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, compRecord]
            exact List.getElem_append_right hge
          have hlat := hRl_at (t - (rawComps_lvl.flatMap compRecord).length) hsub_lt
          rw [hget_ge, show arena₀ + t = arenaPtr + (t - (rawComps_lvl.flatMap compRecord).length) by omega]
          exact hlat
      · dsimp only [rawComps']
        rw [List.flatMap_append, List.length_append, ha_eq', hptr_eq]
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, compRecord, List.length_cons]
        omega
      · intro comp hc
        rcases List.mem_append.mp hc with h1 | h2
        · exact hrc_mem comp h1
        · simp only [List.mem_singleton] at h2; subst h2; exact ⟨rfl, hRl_pw, hRl_2⟩
      · intro u hu
        dsimp only [s4, s3]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        rw [hs2_kept u hu]
        by_cases huR : u ∈ R
        · rw [(hkept_new u hu).1 huR]
          refine ⟨by omega, ?_⟩
          simp only [ne_eq, one_ne_zero, not_false_eq_true, true_iff]
          refine ⟨q, Nat.lt_succ_self q, ?_⟩
          rw [List.getD_eq_getElem _ _ (by simp [hRs_len]), List.getElem_append_right (by omega : Rs.length ≤ q)]
          simp [hRs_len, huR]
        · rw [(hkept_new u hu).2 huR]
          refine ⟨(hkept_inv u hu).1, ?_⟩
          rw [(hkept_inv u hu).2]
          constructor
          · rintro ⟨p', hp', hu'⟩
            refine ⟨p', by omega, ?_⟩
            rw [List.getD_eq_getElem _ _ (by simp [hRs_len]; omega), List.getElem_append_left (by omega)]
            rwa [List.getD_eq_getElem _ _ (by omega)] at hu'
          · rintro ⟨p', hp', hu'⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hp' with hlt | hp_eq
            · refine ⟨p', hlt, ?_⟩
              have hget_lt : (Rs ++ [R]).getD p' ∅ = Rs.getD p' ∅ := by
                rw [List.getD_eq_getElem _ _ (by simp [hRs_len]; omega),
                  List.getElem_append_left (by omega : p' < Rs.length),
                  ← List.getD_eq_getElem _ _ (by omega : p' < Rs.length)]
              rwa [hget_lt] at hu'
            · subst p'
              rw [List.getD_eq_getElem _ _ (by simp [hRs_len]), List.getElem_append_right (by omega : Rs.length ≤ q)] at hu'
              simp only [List.getElem_singleton] at hu'
              exact absurd hu' huR
      · intro a h1 h2 h3 h4 h5
        dsimp only [s4, s3]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        rw [hs2_fr a h1 h2 (by omega)]
        exact hfr_st a h1 h2 (by omega) h4 h5
  have hrun_loop := forRange_varCost (w := w) (p := p) (ω := ω)
    19 (.const 0) (.reg 20) (partLoopBody b_part) Inv
    (fun q => partPruneCost (cntOf q) (ecntOf q) D_phi + 40) 0 k
    (Nat.zero_le k) hw1 (by omega)
    (fun _ _ _ _ h => h.2.1)
    (fun _ _ _ _ h => by simp [Expr.eval]; exact h.2.2.1)
    hstep st₁ (by simp [Expr.eval])
    (by
      refine ⟨lvlRegs_of_eq (fun r hr => by simp [Function.update_of_ne (by omega : r ≠ 19)]) hst₁_lvl,
        by simp, by simp [hst₁_20], arena₀, [], [], le_rfl, by omega,
        by simp [hst₁_mem, hstate_0], by simp [hst₁_mem, hstate_1], by simp [hst₁_mem, hstate_2],
        by simp, fun _ h => by simp at h, rfl, by simp, fun _ h => by simp at h, rfl, List.Pairwise.nil,
        fun _ h => by omega, fun u hu => by simp [hst₁_mem, hkept0 u hu], fun _ _ _ _ _ _ => congrFun hst₁_mem _⟩)
  rcases hrun_loop with ⟨st', c_loop, hr_loop, ⟨hlvl', _, _, arena₁, Rs, rawComps_lvl, ha0_le,
    ha_ub, hst'_ptr0, hst'_ptr1, hst'_ptr2, _, hlist_ar, hptr_eq, hrc_map, hrc_mem, hRs_len,
    hRs_disj, hRs_spec, hkept_inv, hfr_end⟩, hc_loop⟩
  refine ⟨st', c_loop, arena₁, Rs, rawComps_lvl, hr_loop, hlvl', ha0_le, ha_ub, hst'_ptr0,
    hst'_ptr1, hst'_ptr2, hlist_ar, hptr_eq, hrc_map, hrc_mem, hRs_len, hRs_disj, hRs_spec,
    hkept_inv, hfr_end, ?_⟩
  -- Bound summed loop cost
  have hsum_cnt : ∑ q ∈ Finset.Ico 0 k, cntOf q = curG.n := by
    dsimp only [cntOf]
    rw [sum_Ico_eq_of_off k (off := fun q => mem₁ (grpPartOff bufAddr curG.n + q)) hpo0 hpo_step, hcnt_sum]
  have hsum_ecnt : ∑ q ∈ Finset.Ico 0 k, ecntOf q ≤ curG.m := by
    dsimp only [ecntOf]
    rw [sum_Ico_eq_of_off k (off := fun q => mem₁ (grpEdgeOff bufAddr curG.n + q)) heo0 heo_step]; exact hecnt_sum
  have hterm_le : ∀ q ∈ Finset.Ico 0 k,
      partPruneCost (cntOf q) (ecntOf q) D_phi + 40 + (Expr.reg 20).size + 8 ≤
        620 * cntOf q + (590 + 720 * (4 * H_max + 14) ^ 2) * ecntOf q +
          (1000 + 400 * (4 * H_max + 14) ^ 2) := by
    intro q hq
    rw [Finset.mem_Ico] at hq
    have hec_le : ecntOf q ≤ curG.m := by
      obtain ⟨_, _, ecnt, _, _, _, hq_ec, _, _, heoff_le, _⟩ := hgrp q hq.2
      change ecntOf q = ecnt at hq_ec
      omega
    have hpb := partPruneCost_le_bound (cnt := cntOf q) (D_phi := D_phi) hec_le
    dsimp only [Expr.size] at hpb ⊢
    dsimp only [H_max]
    omega
  have hsum_bound :
      ∑ q ∈ Finset.Ico 0 k, (partPruneCost (cntOf q) (ecntOf q) D_phi + 40 + (Expr.reg 20).size + 8) ≤
        ∑ q ∈ Finset.Ico 0 k, (620 * cntOf q + (590 + 720 * (4 * H_max + 14) ^ 2) * ecntOf q +
          (1000 + 400 * (4 * H_max + 14) ^ 2)) := Finset.sum_le_sum hterm_le
  conv_rhs at hsum_bound =>
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_const, Nat.card_Ico, Nat.sub_zero, smul_eq_mul]
  rw [hsum_cnt] at hsum_bound
  have hmul_ecnt : (590 + 720 * (4 * H_max + 14) ^ 2) * ∑ q ∈ Finset.Ico 0 k, ecntOf q ≤
      (590 + 720 * (4 * H_max + 14) ^ 2) * curG.m := Nat.mul_le_mul_left _ hsum_ecnt
  have hmul_k : k * (1000 + 400 * (4 * H_max + 14) ^ 2) ≤
      curG.n * (1000 + 400 * (4 * H_max + 14) ^ 2) := Nat.mul_le_mul_right _ hkn
  simp only [Expr.size] at hc_loop hsum_bound
  dsimp only [H_max] at hc_loop hsum_bound hmul_ecnt hmul_k ⊢
  omega


end MinCostFlow.Expander
