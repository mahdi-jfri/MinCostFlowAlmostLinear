module

public import MinCostFlow.Expander.DecomposePartBase

import Mathlib.Tactic.Linarith

/-!
# Partition Pruning: Setup, Compressed Graph Copy, and Degree Scan

Proves `partPtrSetup_triple`, `partBuildGX_triple`, and `partDegX_triple`
for `partPruneProc`.
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

lemma partPtrSetup_triple {w curGAddr bufAddr q lvl D D_phi workAddr keptVertAddr arenaPtr : ℕ}
    (p : Program) (mem : ℕ → ℕ)
    (curG : Cited.Graph) (k cnt off ecnt eoff : ℕ)
    (hk : 1 ≤ k) (hqk : q < k) (hkn : k ≤ curG.n)
    (hcnt_eq : mem (grpPartCnt bufAddr curG.n + q) = cnt)
    (hoff_eq : mem (grpPartOff bufAddr curG.n + q) = off)
    (hecnt_eq : mem (grpEdgeCnt bufAddr curG.n + q) = ecnt)
    (heoff_eq : mem (grpEdgeOff bufAddr curG.n + q) = eoff)
    (hoff_le : off + cnt ≤ curG.n)
    (heoff_le : eoff + ecnt ≤ curG.m)
    (hbuf : bufAddr + groupBufSize curG.n curG.m + 2 < 2 ^ w)
    (hw_hi : partPruneWorkAddr workAddr cnt ecnt < 2 ^ w)
    (hw16 : 16 ≤ 2 ^ w) :
    Triple w p
      (fun st =>
        st.regs 0 = curGAddr ∧ st.regs 1 = bufAddr ∧ st.regs 2 = q ∧
        st.regs 3 = lvl ∧ st.regs 4 = D ∧ st.regs 5 = D_phi ∧
        st.regs 6 = workAddr ∧ st.regs 7 = keptVertAddr ∧ st.regs 8 = arenaPtr ∧
        st.regs 9 = curG.n ∧ st.regs 10 = curG.m ∧ st.regs 11 = cnt ∧
        st.mem = mem)
      partPtrSetupStmt
      (normalPost fun st =>
        st.regs 0 = curGAddr ∧ st.regs 1 = bufAddr ∧ st.regs 2 = q ∧
        st.regs 3 = lvl ∧ st.regs 4 = D ∧ st.regs 5 = D_phi ∧
        st.regs 6 = workAddr ∧ st.regs 7 = keptVertAddr ∧ st.regs 8 = arenaPtr ∧
        st.regs 9 = curG.n ∧ st.regs 10 = curG.m ∧ st.regs 11 = cnt ∧
        st.regs 12 = grpPartVerts bufAddr curG.n + off ∧
        st.regs 13 = ecnt ∧
        st.regs 14 = grpPartEdges bufAddr curG.n + 2 * eoff ∧
        st.regs 15 = partGXAddr workAddr cnt ecnt ∧
        st.regs 16 = partDegXAddr workAddr cnt ecnt ∧
        st.regs 17 = partInBAddr workAddr cnt ecnt ∧
        st.regs 18 = partOutRAddr workAddr cnt ecnt ∧
        st.regs 19 = partCsrAddr workAddr cnt ecnt ∧
        st.regs 20 = partPruneWorkAddr workAddr cnt ecnt ∧
        st.mem = mem)
      (fun _ => 100) := by
  intro st ω ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hm⟩
  have hpo : mem (bufAddr + 5 * curG.n + q) = off := by simpa [grpPartOff] using hoff_eq
  have hec : mem (bufAddr + 9 * curG.n + 1 + q) = ecnt := by simpa [grpEdgeCnt] using hecnt_eq
  have heo : mem (bufAddr + 10 * curG.n + 1 + q) = eoff := by simpa [grpEdgeOff] using heoff_eq
  dsimp only [groupBufSize] at hbuf
  dsimp only [partPruneWorkAddr] at hw_hi
  refine runs_start_le ?_
  dsimp only [partPtrSetupStmt, seqStmts]
  wram_step; simp only [hm, hpo]
  wram_step
  wram_step; simp only [h1, h9, h2, hec]
  wram_step; simp only [h1, h9, h2, heo]
  wram_run
  · dsimp only [grpPartVerts, grpPartEdges, partGXAddr, partDegXAddr, partInBAddr, partOutRAddr,
      partCsrAddr, partPruneWorkAddr]
    refine ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp; omega
    · simp [h6]
    · simp [h6]; omega
    · simp [h6]; omega
    · simp [h6]; omega
    · simp [h6]; omega
    · simp [h6]; omega
    · rfl
  · wram_cost

lemma partBuildGX_triple {w curGAddr bufAddr q lvl D D_phi workAddr keptVertAddr arenaPtr : ℕ}
    (p : Program) (mem : ℕ → ℕ)
    (curG : Cited.Graph) (cnt off ecnt eoff : ℕ) (G_X : Cited.Graph)
    (hGX_n : G_X.n = cnt) (hGX_m : G_X.m = ecnt)
    (hedges : ∀ j (hj : j < G_X.edges.length),
      mem (grpPartEdges bufAddr curG.n + 2 * (eoff + j)) = (G_X.edges[j]'hj).1 ∧
      mem (grpPartEdges bufAddr curG.n + 2 * (eoff + j) + 1) = (G_X.edges[j]'hj).2)
    (hGXV : G_X.IsValid)
    (heoff_le : eoff + ecnt ≤ curG.m)
    (hlow_work : bufAddr + groupBufSize curG.n curG.m ≤ workAddr)
    (_hcnt_w : cnt < 2 ^ w)
    (hdegX_w : partDegXAddr workAddr cnt ecnt + 2 < 2 ^ w)
    (hw16 : 16 ≤ 2 ^ w) :
    Triple w p
      (fun st =>
        st.regs 0 = curGAddr ∧ st.regs 1 = bufAddr ∧ st.regs 2 = q ∧
        st.regs 3 = lvl ∧ st.regs 4 = D ∧ st.regs 5 = D_phi ∧
        st.regs 6 = workAddr ∧ st.regs 7 = keptVertAddr ∧ st.regs 8 = arenaPtr ∧
        st.regs 9 = curG.n ∧ st.regs 10 = curG.m ∧ st.regs 11 = cnt ∧
        st.regs 12 = grpPartVerts bufAddr curG.n + off ∧
        st.regs 13 = ecnt ∧
        st.regs 14 = grpPartEdges bufAddr curG.n + 2 * eoff ∧
        st.regs 15 = partGXAddr workAddr cnt ecnt ∧
        st.regs 16 = partDegXAddr workAddr cnt ecnt ∧
        st.regs 17 = partInBAddr workAddr cnt ecnt ∧
        st.regs 18 = partOutRAddr workAddr cnt ecnt ∧
        st.regs 19 = partCsrAddr workAddr cnt ecnt ∧
        st.regs 20 = partPruneWorkAddr workAddr cnt ecnt ∧
        st.mem = mem)
      partBuildGXStmt
      (normalPost fun st =>
        st.regs 0 = curGAddr ∧ st.regs 1 = bufAddr ∧ st.regs 2 = q ∧
        st.regs 3 = lvl ∧ st.regs 4 = D ∧ st.regs 5 = D_phi ∧
        st.regs 6 = workAddr ∧ st.regs 7 = keptVertAddr ∧ st.regs 8 = arenaPtr ∧
        st.regs 9 = curG.n ∧ st.regs 10 = curG.m ∧ st.regs 11 = cnt ∧
        st.regs 12 = grpPartVerts bufAddr curG.n + off ∧
        st.regs 13 = ecnt ∧
        st.regs 14 = grpPartEdges bufAddr curG.n + 2 * eoff ∧
        st.regs 15 = partGXAddr workAddr cnt ecnt ∧
        st.regs 16 = partDegXAddr workAddr cnt ecnt ∧
        st.regs 17 = partInBAddr workAddr cnt ecnt ∧
        st.regs 18 = partOutRAddr workAddr cnt ecnt ∧
        st.regs 19 = partCsrAddr workAddr cnt ecnt ∧
        st.regs 20 = partPruneWorkAddr workAddr cnt ecnt ∧
        GraphAt st.mem (partGXAddr workAddr cnt ecnt) G_X ∧
        MemFrame mem st.mem (partGXAddr workAddr cnt ecnt) (partDegXAddr workAddr cnt ecnt))
      (fun _ => 49 * ecnt + 25) := by
  dsimp only [partGXAddr, partDegXAddr] at hdegX_w ⊢
  dsimp only [groupBufSize] at hlow_work
  have hw2 : 1 < 2 ^ w := by omega
  have h15_bound : ecnt < 2 ^ w := by omega
  let PreL : State → Prop := fun st =>
    st.regs 0 = curGAddr ∧ st.regs 1 = bufAddr ∧ st.regs 2 = q ∧
    st.regs 3 = lvl ∧ st.regs 4 = D ∧ st.regs 5 = D_phi ∧
    st.regs 6 = workAddr ∧ st.regs 7 = keptVertAddr ∧ st.regs 8 = arenaPtr ∧
    st.regs 9 = curG.n ∧ st.regs 10 = curG.m ∧ st.regs 11 = cnt ∧
    st.regs 12 = grpPartVerts bufAddr curG.n + off ∧
    st.regs 13 = ecnt ∧
    st.regs 14 = grpPartEdges bufAddr curG.n + 2 * eoff ∧
    st.regs 15 = workAddr ∧
    st.regs 16 = workAddr + 2 + 2 * ecnt ∧
    st.regs 17 = partInBAddr workAddr cnt ecnt ∧
    st.regs 18 = partOutRAddr workAddr cnt ecnt ∧
    st.regs 19 = partCsrAddr workAddr cnt ecnt ∧
    st.regs 20 = partPruneWorkAddr workAddr cnt ecnt ∧
    st.mem workAddr = cnt ∧
    st.mem (workAddr + 1) = ecnt ∧
    MemFrame mem st.mem workAddr (workAddr + 2 + 2 * ecnt)
  let Pre1 : State → Prop := fun st =>
    st.regs 0 = curGAddr ∧ st.regs 1 = bufAddr ∧ st.regs 2 = q ∧
    st.regs 3 = lvl ∧ st.regs 4 = D ∧ st.regs 5 = D_phi ∧
    st.regs 6 = workAddr ∧ st.regs 7 = keptVertAddr ∧ st.regs 8 = arenaPtr ∧
    st.regs 9 = curG.n ∧ st.regs 10 = curG.m ∧ st.regs 11 = cnt ∧
    st.regs 12 = grpPartVerts bufAddr curG.n + off ∧
    st.regs 13 = ecnt ∧
    st.regs 14 = grpPartEdges bufAddr curG.n + 2 * eoff ∧
    st.regs 15 = workAddr ∧
    st.regs 16 = workAddr + 2 + 2 * ecnt ∧
    st.regs 17 = partInBAddr workAddr cnt ecnt ∧
    st.regs 18 = partOutRAddr workAddr cnt ecnt ∧
    st.regs 19 = partCsrAddr workAddr cnt ecnt ∧
    st.regs 20 = partPruneWorkAddr workAddr cnt ecnt ∧
    st.mem workAddr = cnt ∧
    MemFrame mem st.mem workAddr (workAddr + 2 + 2 * ecnt)
  have hhdr1 : Triple w p
      (fun st =>
        st.regs 0 = curGAddr ∧ st.regs 1 = bufAddr ∧ st.regs 2 = q ∧
        st.regs 3 = lvl ∧ st.regs 4 = D ∧ st.regs 5 = D_phi ∧
        st.regs 6 = workAddr ∧ st.regs 7 = keptVertAddr ∧ st.regs 8 = arenaPtr ∧
        st.regs 9 = curG.n ∧ st.regs 10 = curG.m ∧ st.regs 11 = cnt ∧
        st.regs 12 = grpPartVerts bufAddr curG.n + off ∧
        st.regs 13 = ecnt ∧
        st.regs 14 = grpPartEdges bufAddr curG.n + 2 * eoff ∧
        st.regs 15 = workAddr ∧
        st.regs 16 = workAddr + 2 + 2 * ecnt ∧
        st.regs 17 = partInBAddr workAddr cnt ecnt ∧
        st.regs 18 = partOutRAddr workAddr cnt ecnt ∧
        st.regs 19 = partCsrAddr workAddr cnt ecnt ∧
        st.regs 20 = partPruneWorkAddr workAddr cnt ecnt ∧
        st.mem = mem)
      (.store (.reg 15) (.reg 11))
      (normalPost Pre1)
      (fun _ => 5) := by
    intro st ω ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, hm⟩
    refine runs_start_le ?_
    wram_run
    · refine ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
        h16, h17, h18, h19, h20, ?_, ?_⟩
      · simp
      · simpa [hm, h15] using memFrame_update (le_refl workAddr)
          (by omega : workAddr < workAddr + 2 + 2 * ecnt)
    · wram_cost
  have hhdr2 : Triple w p Pre1
      (.store (.bin .add (.reg 15) (.const 1)) (.reg 13))
      (normalPost PreL)
      (fun _ => 6) := by
    intro st ω ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, hmw0, hfr⟩
    refine runs_start_le ?_
    wram_run
    · refine ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
        h16, h17, h18, h19, h20, ?_, ?_, ?_⟩
      · simp [hmw0]
      · simp
      · simpa [h15] using memFrame_trans hfr
          (memFrame_update (by omega : workAddr ≤ workAddr + 1)
            (by omega : workAddr + 1 < workAddr + 2 + 2 * ecnt))
    · wram_cost
  let Inv : ℕ → State → Prop := fun j st =>
    st.regs 0 = curGAddr ∧ st.regs 1 = bufAddr ∧ st.regs 2 = q ∧
    st.regs 3 = lvl ∧ st.regs 4 = D ∧ st.regs 5 = D_phi ∧
    st.regs 6 = workAddr ∧ st.regs 7 = keptVertAddr ∧ st.regs 8 = arenaPtr ∧
    st.regs 9 = curG.n ∧ st.regs 10 = curG.m ∧ st.regs 11 = cnt ∧
    st.regs 12 = grpPartVerts bufAddr curG.n + off ∧
    st.regs 13 = ecnt ∧
    st.regs 14 = grpPartEdges bufAddr curG.n + 2 * eoff ∧
    st.regs 15 = workAddr ∧
    st.regs 16 = workAddr + 2 + 2 * ecnt ∧
    st.regs 17 = partInBAddr workAddr cnt ecnt ∧
    st.regs 18 = partOutRAddr workAddr cnt ecnt ∧
    st.regs 19 = partCsrAddr workAddr cnt ecnt ∧
    st.regs 20 = partPruneWorkAddr workAddr cnt ecnt ∧
    st.regs 24 = j ∧
    st.mem workAddr = cnt ∧
    st.mem (workAddr + 1) = ecnt ∧
    (∀ t (ht : t < j), ∃ (htG : t < G_X.edges.length),
      st.mem (workAddr + 2 + 2 * t) = (G_X.edges[t]'htG).1 ∧
      st.mem (workAddr + 3 + 2 * t) = (G_X.edges[t]'htG).2) ∧
    MemFrame mem st.mem workAddr (workAddr + 2 + 2 * ecnt)
  let body := seqStmts
    [ .assign 25 (.load (.bin .add (.reg 14) (.bin .mul (.const 2) (.reg 24))))
    , .assign 26 (.load (.bin .add (.reg 14) (.bin .add (.bin .mul (.const 2) (.reg 24)) (.const 1))))
    , .store (.bin .add (.reg 15) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 24)))) (.reg 25)
    , .store (.bin .add (.reg 15) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 24)))) (.reg 26) ]
  have hloop := Triple.forRange_const (p := p) (r := 24) (lo := .const 0) (hi := .reg 13)
    (body := body) (P := PreL) (Inv := Inv) 40 0 ecnt (Nat.zero_le ecnt) hw2
    (fun _ => by omega)
    (fun st ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
        h19, h20, hmw0, hmw1, hfr⟩ =>
      ⟨by eval_expr, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
        h17, h18, h19, h20, by simp, hmw0, hmw1, fun _ ht => by omega, hfr⟩)
    (fun _ st _ _ hI => hI.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hI => by have := hI.2.2.2.2.2.2.2.2.2.2.2.2.2.1; eval_expr)
    (fun j _ hjlt st ω hI => by
      rcases hI with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
        h17, h18, h19, h20, h24, hmw0, hmw1, hed_j, hfr⟩
      have hjG : j < G_X.edges.length := by change j < G_X.m; rw [hGX_m]; exact hjlt
      have hev := hGXV _ (List.getElem_mem hjG)
      have he1_lt : (G_X.edges[j]'hjG).1 < cnt := by rw [← hGX_n]; exact hev.1
      have he2_lt : (G_X.edges[j]'hjG).2 < cnt := by rw [← hGX_n]; exact hev.2
      have hedges_j := hedges j hjG
      dsimp only [grpPartEdges] at h14
      have hsrc1 : st.mem (bufAddr + 12 * curG.n + 2 + 2 * eoff + 2 * j) = (G_X.edges[j]'hjG).1 := by
        rw [hfr _ (Or.inl (by omega)), show bufAddr + 12 * curG.n + 2 + 2 * eoff + 2 * j =
          grpPartEdges bufAddr curG.n + 2 * (eoff + j) by dsimp only [grpPartEdges]; omega]
        exact hedges_j.1
      have hsrc2 : st.mem (bufAddr + 12 * curG.n + 2 + 2 * eoff + (2 * j + 1)) = (G_X.edges[j]'hjG).2 := by
        rw [hfr _ (Or.inl (by omega)), show bufAddr + 12 * curG.n + 2 + 2 * eoff + (2 * j + 1) =
          grpPartEdges bufAddr curG.n + 2 * (eoff + j) + 1 by dsimp only [grpPartEdges]; omega]
        exact hedges_j.2
      have ha1_lo : workAddr ≤ workAddr + (2 + 2 * j) := by omega
      have ha1_hi : workAddr + (2 + 2 * j) < workAddr + 2 + 2 * ecnt := by omega
      have ha2_lo : workAddr ≤ workAddr + (3 + 2 * j) := by omega
      have ha2_hi : workAddr + (3 + 2 * j) < workAddr + 2 + 2 * ecnt := by omega
      refine runs_start_le ?_
      dsimp only [body, seqStmts]
      wram_step; simp only [hsrc1]
      wram_step; simp only [h14, h24, hsrc2]
      wram_run
      · dsimp only [Inv]
        simp only [h15, h24]
        refine ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
          by dsimp only [grpPartEdges]; exact h14, h15, h16, h17, h18,
          h19, h20, by simp, ?_, ?_, fun t ht => ?_, ?_⟩, by simp [h24]⟩
        · simp only [Function.update_of_ne (by omega : workAddr ≠ workAddr + (3 + 2 * j)),
            Function.update_of_ne (by omega : workAddr ≠ workAddr + (2 + 2 * j)), hmw0]
        · simp only [Function.update_of_ne (by omega : workAddr + 1 ≠ workAddr + (3 + 2 * j)),
            Function.update_of_ne (by omega : workAddr + 1 ≠ workAddr + (2 + 2 * j)), hmw1]
        · rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht' | htj
          · have hp := hed_j t ht'
            rcases hp with ⟨htG, hp1, hp2⟩
            refine ⟨htG, ?_, ?_⟩
            · have ha : workAddr + 2 + 2 * t ≠ workAddr + (3 + 2 * j) := by omega
              have hb : workAddr + 2 + 2 * t ≠ workAddr + (2 + 2 * j) := by omega
              simpa [Function.update_of_ne ha, Function.update_of_ne hb] using hp1
            · have ha : workAddr + 3 + 2 * t ≠ workAddr + (3 + 2 * j) := by omega
              have hb : workAddr + 3 + 2 * t ≠ workAddr + (2 + 2 * j) := by omega
              simpa [Function.update_of_ne ha, Function.update_of_ne hb] using hp2
          · subst htj
            refine ⟨hjG, ?_, ?_⟩
            · have ha : workAddr + 2 + 2 * t ≠ workAddr + (3 + 2 * t) := by omega
              have hb : workAddr + 2 + 2 * t = workAddr + (2 + 2 * t) := by omega
              dsimp only
              rw [Function.update_of_ne ha, hb, Function.update_self]
            · have hb : workAddr + 3 + 2 * t = workAddr + (3 + 2 * t) := by omega
              dsimp only
              rw [hb, Function.update_self]
        · exact memFrame_trans hfr (memFrame_trans (memFrame_update ha1_lo ha1_hi) (memFrame_update ha2_lo ha2_hi))
      · wram_cost)
  have htail := Triple.seq_normal hhdr2 hloop (T := fun _ => 49 * ecnt + 15) fun _ _ _ _ => by
    simp only [Expr.size_reg, Expr.size_const, Nat.sub_zero]; omega
  refine (Triple.seq_normal hhdr1 htail (T := fun _ => 49 * ecnt + 25) fun _ _ _ _ => by omega).conseq
    (fun _ h => h) ?_ (fun _ _ => le_rfl)
  intro o st' h
  cases o with
  | returned _ => exact False.elim h
  | normal =>
    rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
      h19, h20, _, hmw0, hmw1, hed_all, hfr⟩
    refine ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
      ?_, hfr⟩
    refine graphAt_of_cells (by rw [hmw0, hGX_n]) (by rw [hmw1, hGX_m]) fun j hj => ?_
    have hj_ec : j < ecnt := hGX_m ▸ hj
    obtain ⟨_, h1j, h2j⟩ := hed_all j hj_ec
    exact ⟨h1j, h2j⟩

lemma partDegX_triple {w curGAddr bufAddr q lvl D D_phi workAddr keptVertAddr arenaPtr : ℕ}
    (p : Program) (mem : ℕ → ℕ)
    (curG : Cited.Graph) (cnt off ecnt eoff : ℕ) (G_X : Cited.Graph)
    (hX : G_X.n = cnt) (hGX_m : G_X.m = ecnt) (hGXV : G_X.IsValid)
    (hgaX : GraphAt mem (partGXAddr workAddr cnt ecnt) G_X)
    (hinB_w : partInBAddr workAddr cnt ecnt + 2 < 2 ^ w)
    (hm_w : 2 * ecnt + 4 < 2 ^ w) (hw16 : 16 ≤ 2 ^ w) :
    Triple w p
      (fun st =>
        st.regs 0 = curGAddr ∧ st.regs 1 = bufAddr ∧ st.regs 2 = q ∧
        st.regs 3 = lvl ∧ st.regs 4 = D ∧ st.regs 5 = D_phi ∧
        st.regs 6 = workAddr ∧ st.regs 7 = keptVertAddr ∧ st.regs 8 = arenaPtr ∧
        st.regs 9 = curG.n ∧ st.regs 10 = curG.m ∧ st.regs 11 = cnt ∧
        st.regs 12 = grpPartVerts bufAddr curG.n + off ∧
        st.regs 13 = ecnt ∧
        st.regs 14 = grpPartEdges bufAddr curG.n + 2 * eoff ∧
        st.regs 15 = partGXAddr workAddr cnt ecnt ∧
        st.regs 16 = partDegXAddr workAddr cnt ecnt ∧
        st.regs 17 = partInBAddr workAddr cnt ecnt ∧
        st.regs 18 = partOutRAddr workAddr cnt ecnt ∧
        st.regs 19 = partCsrAddr workAddr cnt ecnt ∧
        st.regs 20 = partPruneWorkAddr workAddr cnt ecnt ∧
        st.mem = mem)
      partDegXStmt
      (normalPost fun st =>
        st.regs 0 = curGAddr ∧ st.regs 1 = bufAddr ∧ st.regs 2 = q ∧
        st.regs 3 = lvl ∧ st.regs 4 = D ∧ st.regs 5 = D_phi ∧
        st.regs 6 = workAddr ∧ st.regs 7 = keptVertAddr ∧ st.regs 8 = arenaPtr ∧
        st.regs 9 = curG.n ∧ st.regs 10 = curG.m ∧ st.regs 11 = cnt ∧
        st.regs 12 = grpPartVerts bufAddr curG.n + off ∧
        st.regs 13 = ecnt ∧
        st.regs 14 = grpPartEdges bufAddr curG.n + 2 * eoff ∧
        st.regs 15 = partGXAddr workAddr cnt ecnt ∧
        st.regs 16 = partDegXAddr workAddr cnt ecnt ∧
        st.regs 17 = partInBAddr workAddr cnt ecnt ∧
        st.regs 18 = partOutRAddr workAddr cnt ecnt ∧
        st.regs 19 = partCsrAddr workAddr cnt ecnt ∧
        st.regs 20 = partPruneWorkAddr workAddr cnt ecnt ∧
        (∀ x < cnt, st.mem (partDegXAddr workAddr cnt ecnt + x) = G_X.degIn G_X.verts x) ∧
        MemFrame mem st.mem (partDegXAddr workAddr cnt ecnt) (partInBAddr workAddr cnt ecnt))
      (fun _ => 15 * cnt + 60 * ecnt + 25) := by
  dsimp only [partGXAddr, partDegXAddr, partInBAddr] at hinB_w hgaX ⊢
  have hw2 : 1 < 2 ^ w := by omega
  have hcnt_w : cnt < 2 ^ w := by omega
  have hecnt_w : ecnt < 2 ^ w := by omega
  let InvZ : ℕ → State → Prop := fun q0 st =>
    st.regs 0 = curGAddr ∧ st.regs 1 = bufAddr ∧ st.regs 2 = q ∧
    st.regs 3 = lvl ∧ st.regs 4 = D ∧ st.regs 5 = D_phi ∧
    st.regs 6 = workAddr ∧ st.regs 7 = keptVertAddr ∧ st.regs 8 = arenaPtr ∧
    st.regs 9 = curG.n ∧ st.regs 10 = curG.m ∧ st.regs 11 = cnt ∧
    st.regs 12 = grpPartVerts bufAddr curG.n + off ∧
    st.regs 13 = ecnt ∧
    st.regs 14 = grpPartEdges bufAddr curG.n + 2 * eoff ∧
    st.regs 15 = workAddr ∧
    st.regs 16 = workAddr + 2 + 2 * ecnt ∧
    st.regs 17 = workAddr + 2 + 2 * ecnt + cnt ∧
    st.regs 18 = partOutRAddr workAddr cnt ecnt ∧
    st.regs 19 = partCsrAddr workAddr cnt ecnt ∧
    st.regs 20 = partPruneWorkAddr workAddr cnt ecnt ∧
    st.regs 24 = q0 ∧
    (∀ x < q0, st.mem (workAddr + 2 + 2 * ecnt + x) = 0) ∧
    MemFrame mem st.mem (workAddr + 2 + 2 * ecnt) (workAddr + 2 + 2 * ecnt + cnt)
  have hzero := Triple.forRange_const (p := p) (r := 24) (lo := .const 0) (hi := .reg 11)
    (body := .store (.bin .add (.reg 16) (.reg 24)) (.const 0))
    (P := fun st =>
      st.regs 0 = curGAddr ∧ st.regs 1 = bufAddr ∧ st.regs 2 = q ∧
      st.regs 3 = lvl ∧ st.regs 4 = D ∧ st.regs 5 = D_phi ∧
      st.regs 6 = workAddr ∧ st.regs 7 = keptVertAddr ∧ st.regs 8 = arenaPtr ∧
      st.regs 9 = curG.n ∧ st.regs 10 = curG.m ∧ st.regs 11 = cnt ∧
      st.regs 12 = grpPartVerts bufAddr curG.n + off ∧
      st.regs 13 = ecnt ∧
      st.regs 14 = grpPartEdges bufAddr curG.n + 2 * eoff ∧
      st.regs 15 = workAddr ∧
      st.regs 16 = workAddr + 2 + 2 * ecnt ∧
      st.regs 17 = workAddr + 2 + 2 * ecnt + cnt ∧
      st.regs 18 = partOutRAddr workAddr cnt ecnt ∧
      st.regs 19 = partCsrAddr workAddr cnt ecnt ∧
      st.regs 20 = partPruneWorkAddr workAddr cnt ecnt ∧
      st.mem = mem)
    (Inv := InvZ) 6 0 cnt (Nat.zero_le cnt) hw2 (fun _ => by omega)
    (fun st ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
        h19, h20, hm⟩ =>
      ⟨by eval_expr, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
        h17, h18, h19, h20, by simp, fun _ hx => by omega,
        by simpa [hm] using memFrame_refl st.mem _ _⟩)
    (fun _ st _ _ hI => hI.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hI => by have := hI.2.2.2.2.2.2.2.2.2.2.2.1; eval_expr)
    (fun x _ hxlt st ω hI => by
      rcases hI with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
        h18, h19, h20, h24, hz, hfr⟩
      refine runs_start_le ?_
      wram_run
      · refine ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
          h19, h20, by simp, fun y hy => ?_, ?_⟩, by simp [h24]⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hy with hy' | rfl
          · simp [Function.update_of_ne (by omega : workAddr + 2 + 2 * ecnt + y ≠
              workAddr + 2 + 2 * ecnt + x), hz y hy']
          · simp
        · simpa [h16, h24] using memFrame_trans hfr
            (memFrame_update (by omega : workAddr + 2 + 2 * ecnt ≤ workAddr + 2 + 2 * ecnt + x)
              (by omega : workAddr + 2 + 2 * ecnt + x < workAddr + 2 + 2 * ecnt + cnt))
      · wram_cost)
  let InvD : ℕ → State → Prop := fun j st =>
    st.regs 0 = curGAddr ∧ st.regs 1 = bufAddr ∧ st.regs 2 = q ∧
    st.regs 3 = lvl ∧ st.regs 4 = D ∧ st.regs 5 = D_phi ∧
    st.regs 6 = workAddr ∧ st.regs 7 = keptVertAddr ∧ st.regs 8 = arenaPtr ∧
    st.regs 9 = curG.n ∧ st.regs 10 = curG.m ∧ st.regs 11 = cnt ∧
    st.regs 12 = grpPartVerts bufAddr curG.n + off ∧
    st.regs 13 = ecnt ∧
    st.regs 14 = grpPartEdges bufAddr curG.n + 2 * eoff ∧
    st.regs 15 = workAddr ∧
    st.regs 16 = workAddr + 2 + 2 * ecnt ∧
    st.regs 17 = workAddr + 2 + 2 * ecnt + cnt ∧
    st.regs 18 = partOutRAddr workAddr cnt ecnt ∧
    st.regs 19 = partCsrAddr workAddr cnt ecnt ∧
    st.regs 20 = partPruneWorkAddr workAddr cnt ecnt ∧
    st.regs 24 = j ∧
    (∀ x < cnt, st.mem (workAddr + 2 + 2 * ecnt + x) = degXPrefix G_X j x) ∧
    MemFrame mem st.mem (workAddr + 2 + 2 * ecnt) (workAddr + 2 + 2 * ecnt + cnt)
  let body := seqStmts
    [ .assign 25 (.load (.bin .add (.reg 15) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 24)))))
    , .assign 26 (.load (.bin .add (.reg 15) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 24)))))
    , .assign 27 (.load (.bin .add (.reg 16) (.reg 25)))
    , .store (.bin .add (.reg 16) (.reg 25)) (.bin .add (.reg 27) (.const 1))
    , .assign 27 (.load (.bin .add (.reg 16) (.reg 26)))
    , .store (.bin .add (.reg 16) (.reg 26)) (.bin .add (.reg 27) (.const 1)) ]
  have hscan := Triple.forRange_const (p := p) (r := 24) (lo := .const 0) (hi := .reg 13)
    (body := body) (P := InvZ cnt) (Inv := InvD) 50 0 ecnt (Nat.zero_le ecnt) hw2
    (fun _ => by omega)
    (fun st ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
        h18, h19, h20, _, hz, hfr⟩ =>
      ⟨by eval_expr, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
        h18, h19, h20, by simp, fun x hx => by simp [degXPrefix_zero, hz x hx], hfr⟩)
    (fun _ st _ _ hI => hI.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hI => by have := hI.2.2.2.2.2.2.2.2.2.2.2.2.2.1; eval_expr)
    (fun j _ hjlt st ω hI => by
      rcases hI with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
        h18, h19, h20, h24, hdeg, hfr⟩
      have hjG : j < G_X.edges.length := by change j < G_X.m; rw [hGX_m]; exact hjlt
      have hev := hGXV _ (List.getElem_mem hjG)
      set u := (G_X.edges[j]'hjG).1
      set v := (G_X.edges[j]'hjG).2
      have hu_cnt : u < cnt := by rw [← hX]; exact hev.1
      have hv_cnt : v < cnt := by rw [← hX]; exact hev.2
      have hu_eq : st.mem (workAddr + (2 + 2 * j)) = u := by
        rw [hfr _ (Or.inl (by omega)), ← Nat.add_assoc]; exact graphAt_edge_fst hgaX hjG
      have hv_eq : st.mem (workAddr + (3 + 2 * j)) = v := by
        rw [hfr _ (Or.inl (by omega)), ← Nat.add_assoc]; exact graphAt_edge_snd hgaX hjG
      have hdu_eq : st.mem (workAddr + 2 + 2 * ecnt + u) = degXPrefix G_X j u := hdeg u hu_cnt
      have hdu_le : degXPrefix G_X j u ≤ 2 * ecnt := by rw [← hGX_m]; exact degXPrefix_le_two_mul_m j u
      have hdv_le : degXPrefix G_X j v ≤ 2 * ecnt := by rw [← hGX_m]; exact degXPrefix_le_two_mul_m j v
      have hf10 : workAddr + 2 + 2 * ecnt ≤ workAddr + 2 + 2 * ecnt + u := by omega
      have hf11 : workAddr + 2 + 2 * ecnt + u < workAddr + 2 + 2 * ecnt + cnt := by omega
      have hf20 : workAddr + 2 + 2 * ecnt ≤ workAddr + 2 + 2 * ecnt + v := by omega
      have hf21 : workAddr + 2 + 2 * ecnt + v < workAddr + 2 + 2 * ecnt + cnt := by omega
      refine runs_start_le ?_
      dsimp only [body, seqStmts]
      wram_step; simp only [hu_eq]
      wram_step; simp only [h15, h24, hv_eq]
      wram_step; simp only [h16, hdu_eq]
      wram_step
      wram_step
      · dsimp only
        rw [h16]
        have hdv1 : Function.update st.mem (workAddr + 2 + 2 * ecnt + u) (degXPrefix G_X j u + 1)
            (workAddr + 2 + 2 * ecnt + v) = degXPrefix G_X j v + (if u = v then 1 else 0) := by
          by_cases huv : u = v
          · simp [huv]
          · have hne : workAddr + 2 + 2 * ecnt + v ≠ workAddr + 2 + 2 * ecnt + u := by omega
            simp [Function.update_of_ne hne, hdeg v hv_cnt, huv]
        have hdv_max : (degXPrefix G_X j v + if u = v then 1 else 0) + 1 < 2 ^ w := by
          split_ifs <;> omega
        rw [hdv1]
        wram_run
        · dsimp only [InvD]
          rw [h16]
          refine ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
            h18, h19, h20, by simp, fun x hx => ?_, ?_⟩, by simp [h24]⟩
          · rw [degXPrefix_succ_of_edge hjG x]
            change _ = degXPrefix G_X j x + (if u = x then 1 else 0) + (if v = x then 1 else 0)
            by_cases hxv : x = v <;> by_cases hxu : x = u
            · have huv : u = v := hxu.symm.trans hxv
              simp [hxv, huv, Function.update_self, Nat.add_assoc]
            · have huv : u ≠ v := fun h => hxu (hxv.trans h.symm)
              simp [hxv, huv, Function.update_self, Nat.add_assoc]
            · have hvx : v ≠ u := fun h => hxv (hxu.trans h.symm)
              have hne : workAddr + 2 + 2 * ecnt + u ≠ workAddr + 2 + 2 * ecnt + v := by
                intro h; apply hxv; omega
              simp [hxu, hvx, Function.update_of_ne hne, Function.update_self]
            · have hne1 : workAddr + 2 + 2 * ecnt + x ≠ workAddr + 2 + 2 * ecnt + v := by
                intro h; apply hxv; omega
              have hne2 : workAddr + 2 + 2 * ecnt + x ≠ workAddr + 2 + 2 * ecnt + u := by
                intro h; apply hxu; omega
              simp [Ne.symm hxu, Ne.symm hxv, Function.update_of_ne hne1, Function.update_of_ne hne2, hdeg x hx]
          · exact memFrame_trans hfr
              (memFrame_trans (memFrame_update hf10 hf11) (memFrame_update hf20 hf21))
        · wram_cost)
  refine (Triple.seq_normal hzero hscan (T := fun _ => 15 * cnt + 60 * ecnt + 25)
    fun _ _ _ _ => by simp only [Expr.size_reg, Expr.size_const, Nat.sub_zero]; omega).conseq
    (fun _ h => h) ?_ (fun _ _ => le_rfl)
  intro o st' h
  cases o with
  | returned _ => exact False.elim h
  | normal =>
    rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
      h19, h20, _, hdeg, hfr⟩
    refine ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
      h19, h20, fun x hx => ?_, hfr⟩
    rw [hdeg x hx, ← hGX_m]
    have hXverts : G_X.verts = Finset.range G_X.n := rfl
    exact degXPrefix_full (cfg := { G := G_X, X := G_X.verts, B := ∅, C_cap := 5, H := 1, θ_out_nat := 1 })
      hXverts hGXV x

end MinCostFlow.Expander
