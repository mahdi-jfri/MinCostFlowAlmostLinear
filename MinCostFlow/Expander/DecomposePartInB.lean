module

public import MinCostFlow.Expander.DecomposePartBase

/-!
# Partition Pruning: `B_loc` Setup & Bad-Twin Early Exit

Proves `partInB_triple` for `partInBStmt`, which marks low-degree internal vertices in
`B_loc` and aborts early returning `arenaPtr` if any low-degree internal vertex still has
`sameTwin > 0`.
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

lemma partInB_triple {w curGAddr bufAddr q lvl D D_phi workAddr keptVertAddr arenaPtr : ℕ}
    (p : Program) (mem : ℕ → ℕ)
    (curG : Cited.Graph) (cnt off ecnt eoff : ℕ) (G_X : Cited.Graph)
    (hGX_n : G_X.n = cnt) (hGX_m : G_X.m = ecnt) (_hGXV : G_X.IsValid)
    (hdegX : ∀ x < cnt, mem (partDegXAddr workAddr cnt ecnt + x) = G_X.degIn G_X.verts x)
    (hoff_le : off + cnt ≤ curG.n)
    (hverts_lt : ∀ x < cnt, mem (grpPartVerts bufAddr curG.n + off + x) < curG.n)
    (htwin_lt : ∀ u < curG.n, mem (grpSameTwin bufAddr curG.n + u) < 2 ^ w)
    (hbuf : bufAddr + groupBufSize curG.n curG.m + 2 < 2 ^ w)
    (hlow_work : bufAddr + groupBufSize curG.n curG.m ≤ workAddr)
    (houtR_w : partOutRAddr workAddr cnt ecnt + 2 < 2 ^ w)
    (hmul_w : 2 * ecnt * D_phi + D + 4 < 2 ^ w) (hw16 : 16 ≤ 2 ^ w) :
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
      partInBStmt
      (fun o st =>
        match o with
        | .returned v =>
          v = arenaPtr ∧
          MemFrame mem st.mem (partInBAddr workAddr cnt ecnt) (partOutRAddr workAddr cnt ecnt) ∧
          ∃ x < cnt,
            G_X.degIn G_X.verts x * D_phi < D ∧
            mem (grpSameTwin bufAddr curG.n + mem (grpPartVerts bufAddr curG.n + off + x)) ≠ 0
        | .normal =>
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
          (∀ x < cnt,
            (st.mem (partInBAddr workAddr cnt ecnt + x) ≠ 0 ↔ G_X.degIn G_X.verts x * D_phi < D) ∧
            (G_X.degIn G_X.verts x * D_phi < D →
              mem (grpSameTwin bufAddr curG.n + mem (grpPartVerts bufAddr curG.n + off + x)) = 0)) ∧
          MemFrame mem st.mem (partInBAddr workAddr cnt ecnt) (partOutRAddr workAddr cnt ecnt))
      (fun _ => 55 * cnt + 30) := by
  dsimp only [partDegXAddr, partInBAddr, partOutRAddr] at hdegX houtR_w ⊢
  dsimp only [groupBufSize] at hbuf hlow_work
  have hw2 : 1 < 2 ^ w := by omega
  have hcnt_w : cnt < 2 ^ w := by omega
  have hdeg_le : ∀ x < cnt, G_X.degIn G_X.verts x ≤ 2 * ecnt := fun x _ => by
    have h1 : ((G_X.inside G_X.verts).filter fun e => decide (e.1 = x)).length ≤ G_X.m :=
      le_trans (List.length_filter_le _ _) (List.length_filter_le _ _)
    have h2 : ((G_X.inside G_X.verts).filter fun e => decide (e.2 = x)).length ≤ G_X.m :=
      le_trans (List.length_filter_le _ _) (List.length_filter_le _ _)
    unfold Cited.Graph.degIn
    omega
  let PreB : State → Prop := fun st =>
    st.regs 0 = curGAddr ∧ st.regs 1 = bufAddr ∧ st.regs 2 = q ∧
    st.regs 3 = lvl ∧ st.regs 4 = D ∧ st.regs 5 = D_phi ∧
    st.regs 6 = workAddr ∧ st.regs 7 = keptVertAddr ∧ st.regs 8 = arenaPtr ∧
    st.regs 9 = curG.n ∧ st.regs 10 = curG.m ∧ st.regs 11 = cnt ∧
    st.regs 12 = grpPartVerts bufAddr curG.n + off ∧
    st.regs 13 = ecnt ∧
    st.regs 14 = grpPartEdges bufAddr curG.n + 2 * eoff ∧
    st.regs 15 = partGXAddr workAddr cnt ecnt ∧
    st.regs 16 = workAddr + 2 + 2 * ecnt ∧
    st.regs 17 = workAddr + 2 + 2 * ecnt + cnt ∧
    st.regs 18 = workAddr + 2 + 2 * ecnt + 2 * cnt ∧
    st.regs 19 = partCsrAddr workAddr cnt ecnt ∧
    st.regs 20 = partPruneWorkAddr workAddr cnt ecnt ∧
    st.regs 21 = 0 ∧
    st.mem = mem
  have hinit : Triple w p
      (fun st =>
        st.regs 0 = curGAddr ∧ st.regs 1 = bufAddr ∧ st.regs 2 = q ∧
        st.regs 3 = lvl ∧ st.regs 4 = D ∧ st.regs 5 = D_phi ∧
        st.regs 6 = workAddr ∧ st.regs 7 = keptVertAddr ∧ st.regs 8 = arenaPtr ∧
        st.regs 9 = curG.n ∧ st.regs 10 = curG.m ∧ st.regs 11 = cnt ∧
        st.regs 12 = grpPartVerts bufAddr curG.n + off ∧
        st.regs 13 = ecnt ∧
        st.regs 14 = grpPartEdges bufAddr curG.n + 2 * eoff ∧
        st.regs 15 = partGXAddr workAddr cnt ecnt ∧
        st.regs 16 = workAddr + 2 + 2 * ecnt ∧
        st.regs 17 = workAddr + 2 + 2 * ecnt + cnt ∧
        st.regs 18 = workAddr + 2 + 2 * ecnt + 2 * cnt ∧
        st.regs 19 = partCsrAddr workAddr cnt ecnt ∧
        st.regs 20 = partPruneWorkAddr workAddr cnt ecnt ∧
        st.mem = mem)
      (.assign 21 (.const 0)) (normalPost PreB) (fun _ => 2) := by
    intro st ω ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
      h16, h17, h18, h19, h20, hm⟩
    refine runs_start_le ?_
    wram_run
    · exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
        h16, h17, h18, h19, h20, by simp, hm⟩
    · wram_cost
  let InvB : ℕ → State → Prop := fun j st =>
    st.regs 0 = curGAddr ∧ st.regs 1 = bufAddr ∧ st.regs 2 = q ∧
    st.regs 3 = lvl ∧ st.regs 4 = D ∧ st.regs 5 = D_phi ∧
    st.regs 6 = workAddr ∧ st.regs 7 = keptVertAddr ∧ st.regs 8 = arenaPtr ∧
    st.regs 9 = curG.n ∧ st.regs 10 = curG.m ∧ st.regs 11 = cnt ∧
    st.regs 12 = grpPartVerts bufAddr curG.n + off ∧
    st.regs 13 = ecnt ∧
    st.regs 14 = grpPartEdges bufAddr curG.n + 2 * eoff ∧
    st.regs 15 = partGXAddr workAddr cnt ecnt ∧
    st.regs 16 = workAddr + 2 + 2 * ecnt ∧
    st.regs 17 = workAddr + 2 + 2 * ecnt + cnt ∧
    st.regs 18 = workAddr + 2 + 2 * ecnt + 2 * cnt ∧
    st.regs 19 = partCsrAddr workAddr cnt ecnt ∧
    st.regs 20 = partPruneWorkAddr workAddr cnt ecnt ∧
    st.regs 24 = j ∧
    (st.regs 21 = 0 ∨ st.regs 21 = 1) ∧
    (st.regs 21 ≠ 0 ↔ ∃ x < j,
      G_X.degIn G_X.verts x * D_phi < D ∧
      mem (grpSameTwin bufAddr curG.n + mem (grpPartVerts bufAddr curG.n + off + x)) ≠ 0) ∧
    (∀ x < j, st.mem (workAddr + 2 + 2 * ecnt + cnt + x) ≠ 0 ↔
      G_X.degIn G_X.verts x * D_phi < D) ∧
    MemFrame mem st.mem (workAddr + 2 + 2 * ecnt + cnt) (workAddr + 2 + 2 * ecnt + 2 * cnt)
  let body := seqStmts
    [ .assign 25 (.load (.bin .add (.reg 16) (.reg 24)))
    , .cond (.bin .lt (.bin .mul (.reg 25) (.reg 5)) (.reg 4))
        (seqStmts
          [ .assign 26 (.load (.bin .add (.reg 12) (.reg 24)))
          , .assign 27 (.load (.bin .add (.reg 1) (.reg 26)))
          , .cond (.bin .lt (.const 0) (.reg 27))
              (.assign 21 (.const 1))
              .nop
          , .store (.bin .add (.reg 17) (.reg 24)) (.const 1) ])
        (.store (.bin .add (.reg 17) (.reg 24)) (.const 0)) ]
  have hloop := Triple.forRange_const (p := p) (r := 24) (lo := .const 0) (hi := .reg 11)
    (body := body) (P := PreB) (Inv := InvB) 42 0 cnt (Nat.zero_le cnt) hw2
    (fun _ => by omega)
    (fun st ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
        h19, h20, h21, hm⟩ =>
      ⟨by eval_expr, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
        h17, h18, h19, h20, by simp, Or.inl h21,
        ⟨fun h => absurd h21 h, fun ⟨_, hx, _⟩ => by omega⟩,
        fun _ hx => by omega, by simpa [hm] using memFrame_refl st.mem _ _⟩)
    (fun _ st _ _ hI => hI.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hI => by have := hI.2.2.2.2.2.2.2.2.2.2.2.1; eval_expr)
    (fun x _ hxlt st ω hI => by
      rcases hI with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
        h18, h19, h20, h24, h21b, hbad_iff, hB, hfr⟩
      have hdx : st.mem (workAddr + 2 + 2 * ecnt + x) = G_X.degIn G_X.verts x := by
        rw [hfr _ (Or.inl (by omega))]; exact hdegX x hxlt
      have hdx_le : G_X.degIn G_X.verts x ≤ 2 * ecnt := hdeg_le x hxlt
      have hmul_lt : G_X.degIn G_X.verts x * D_phi < 2 ^ w := by
        have h1 : G_X.degIn G_X.verts x * D_phi ≤ 2 * ecnt * D_phi :=
          Nat.mul_le_mul_right D_phi hdx_le
        omega
      have hf0 : workAddr + 2 + 2 * ecnt + cnt ≤ workAddr + 2 + 2 * ecnt + cnt + x := by omega
      have hf1 : workAddr + 2 + 2 * ecnt + cnt + x < workAddr + 2 + 2 * ecnt + 2 * cnt := by omega
      have hmul_st : G_X.degIn G_X.verts x * st.regs 5 < 2 ^ w := by rw [h5]; exact hmul_lt
      dsimp only [grpPartVerts] at h12
      refine runs_start_le ?_
      dsimp only [body, seqStmts]
      wram_step; simp only [hdx]
      wram_step
      · -- true branch: `degX * D_phi < D`
        have hlt_deg : G_X.degIn G_X.verts x * D_phi < D := by simpa [h4, h5] using hcond
        have hu_mem : st.mem (bufAddr + 7 * curG.n + 1 + off + x) =
            mem (grpPartVerts bufAddr curG.n + off + x) := by
          dsimp only [grpPartVerts]; exact hfr _ (Or.inl (by omega))
        have hu_lt : mem (grpPartVerts bufAddr curG.n + off + x) < curG.n := hverts_lt x hxlt
        have htwin_eq : st.mem (bufAddr + mem (grpPartVerts bufAddr curG.n + off + x)) =
            mem (grpSameTwin bufAddr curG.n + mem (grpPartVerts bufAddr curG.n + off + x)) := by
          dsimp only [grpSameTwin]
          exact hfr _ (Or.inl (by omega))
        have htw_w : mem (grpSameTwin bufAddr curG.n + mem (grpPartVerts bufAddr curG.n + off + x)) <
            2 ^ w := htwin_lt _ hu_lt
        wram_step; simp only [h12, h24, hu_mem]
        wram_step; simp only [h1, htwin_eq]
        wram_step
        · -- `0 < sameTwin`
          have htw_pos : 0 < mem (grpSameTwin bufAddr curG.n + mem (grpPartVerts bufAddr curG.n + off + x)) :=
            by simpa using hcond
          wram_run
          · refine ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
              by dsimp only [grpPartVerts]; exact h12, h13, h14, h15, h16, h17,
              h18, h19, h20, by simp, Or.inr (by simp), ?_, fun y hy => ?_, ?_⟩, by simp [h24]⟩
            · simp only [Function.update_of_ne (by decide : (21 : ℕ) ≠ 24), Function.update_self]
              exact ⟨fun _ => ⟨x, Nat.lt_succ_self x, hlt_deg, by omega⟩, fun _ => by simp⟩
            · rcases Nat.lt_succ_iff_lt_or_eq.mp hy with hy' | rfl
              · simp [h17, h24, Function.update_of_ne (by omega : workAddr + 2 + 2 * ecnt + cnt + y ≠
                  workAddr + 2 + 2 * ecnt + cnt + x), hB y hy']
              · simp [h17, h24, hlt_deg]
            · simpa [h17, h24] using memFrame_trans hfr (memFrame_update hf0 hf1)
          · wram_cost
        · -- `sameTwin = 0`
          have htw_zero : mem (grpSameTwin bufAddr curG.n + mem (grpPartVerts bufAddr curG.n + off + x)) = 0 := by
            have hn : ¬ 0 < mem (grpSameTwin bufAddr curG.n + mem (grpPartVerts bufAddr curG.n + off + x)) := hcond
            omega
          wram_run
          · refine ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
              by dsimp only [grpPartVerts]; exact h12, h13, h14, h15, h16, h17,
              h18, h19, h20, by simp, h21b, ?_, fun y hy => ?_, ?_⟩, by simp [h24]⟩
            · simp only [Function.update_of_ne (by decide : (21 : ℕ) ≠ 24),
                Function.update_of_ne (by decide : (21 : ℕ) ≠ 27),
                Function.update_of_ne (by decide : (21 : ℕ) ≠ 26),
                Function.update_of_ne (by decide : (21 : ℕ) ≠ 25)]
              rw [hbad_iff]
              constructor
              · intro ⟨z, hz, hz_spec⟩; exact ⟨z, Nat.lt_succ_of_lt hz, hz_spec⟩
              · intro ⟨z, hz, hzd, hzt⟩
                rcases Nat.lt_succ_iff_lt_or_eq.mp hz with hz' | rfl
                · exact ⟨z, hz', hzd, hzt⟩
                · exact absurd htw_zero hzt
            · rcases Nat.lt_succ_iff_lt_or_eq.mp hy with hy' | rfl
              · simp [h17, h24, Function.update_of_ne (by omega : workAddr + 2 + 2 * ecnt + cnt + y ≠
                  workAddr + 2 + 2 * ecnt + cnt + x), hB y hy']
              · simp [h17, h24, hlt_deg]
            · simpa [h17, h24] using memFrame_trans hfr (memFrame_update hf0 hf1)
          · wram_cost
      · -- false branch: `¬ degX * D_phi < D`
        have hnot_deg : ¬ G_X.degIn G_X.verts x * D_phi < D := by simpa [h4, h5] using hcond
        wram_run
        · refine ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
            by dsimp only [grpPartVerts]; exact h12, h13, h14, h15, h16, h17,
            h18, h19, h20, by simp, h21b, ?_, fun y hy => ?_, ?_⟩, by simp [h24]⟩
          · simp only [Function.update_of_ne (by decide : (21 : ℕ) ≠ 24),
              Function.update_of_ne (by decide : (21 : ℕ) ≠ 25)]
            rw [hbad_iff]
            constructor
            · intro ⟨z, hz, hz_spec⟩; exact ⟨z, Nat.lt_succ_of_lt hz, hz_spec⟩
            · intro ⟨z, hz, hzd, hzt⟩
              rcases Nat.lt_succ_iff_lt_or_eq.mp hz with hz' | rfl
              · exact ⟨z, hz', hzd, hzt⟩
              · exact absurd hzd hnot_deg
          · rcases Nat.lt_succ_iff_lt_or_eq.mp hy with hy' | rfl
            · simp [h17, h24, Function.update_of_ne (by omega : workAddr + 2 + 2 * ecnt + cnt + y ≠
                workAddr + 2 + 2 * ecnt + cnt + x), hB y hy']
            · simp [h17, h24, hnot_deg]
          · simpa [h17, h24] using memFrame_trans hfr (memFrame_update hf0 hf1)
        · wram_cost)
  intro st ω hpre
  rcases hinit st ω hpre with ⟨o1, st1, c1, hr1, ho1, hc1⟩
  cases o1 with
  | returned _ => exact False.elim ho1
  | normal =>
    rcases hloop st1 ω ho1 with ⟨o2, st2, c2, hr2, ho2, hc2⟩
    cases o2 with
    | returned _ => exact False.elim ho2
    | normal =>
      rcases ho2 with ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16,
        s17, s18, s19, s20, s24, s21b, hbad_iff, hB, hfr⟩
      by_cases h21 : 0 < st2.regs 21
      · have hcond_ev : (Expr.bin .lt (.const 0) (.reg 21)).eval w st2 = some 1 := by
          simp [Expr.eval, BinOp.eval, h21, hw2]
        have hret : Runs w p ω (.ret (.reg 8)) st2 (.returned arenaPtr) st2 2 :=
          runs_ret_iff.mpr ⟨arenaPtr, by simp [Expr.eval, s8], rfl, rfl, by simp [Expr.size]⟩
        have hcond_r : Runs w p ω (.cond (.bin .lt (.const 0) (.reg 21)) (.ret (.reg 8)) .nop)
            st2 (.returned arenaPtr) st2 6 :=
          runs_cond_iff.mpr ⟨1, 2, hcond_ev, hret, by simp [Expr.size]⟩
        have hseq : Runs w p ω partInBStmt st (.returned arenaPtr) st2 (c1 + (c2 + 6 + 1) + 1) :=
          runs_seq_iff.mpr (Or.inr ⟨st1, c1, _, hr1, runs_seq_iff.mpr (Or.inr ⟨st2, c2, 6, hr2, hcond_r, rfl⟩), rfl⟩)
        refine ⟨.returned arenaPtr, st2, _, hseq, ⟨rfl, hfr, hbad_iff.mp (by omega)⟩, ?_⟩
        dsimp only at hc1 hc2 ⊢; simp only [Expr.size_reg, Expr.size_const, Nat.sub_zero] at hc2
        omega
      · have h21_0 : st2.regs 21 = 0 := by omega
        have hcond_ev : (Expr.bin .lt (.const 0) (.reg 21)).eval w st2 = some 0 := by
          simp [Expr.eval, BinOp.eval, h21_0]
        have hnop : Runs w p ω .nop st2 .normal st2 1 := runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩
        have hcond_r : Runs w p ω (.cond (.bin .lt (.const 0) (.reg 21)) (.ret (.reg 8)) .nop)
            st2 .normal st2 5 :=
          runs_cond_iff.mpr ⟨0, 1, hcond_ev, hnop, by simp [Expr.size]⟩
        have hseq : Runs w p ω partInBStmt st .normal st2 (c1 + (c2 + 5 + 1) + 1) :=
          runs_seq_iff.mpr (Or.inr ⟨st1, c1, _, hr1, runs_seq_iff.mpr (Or.inr ⟨st2, c2, 5, hr2, hcond_r, rfl⟩), rfl⟩)
        have hnobad : ∀ x < cnt, G_X.degIn G_X.verts x * D_phi < D →
            mem (grpSameTwin bufAddr curG.n + mem (grpPartVerts bufAddr curG.n + off + x)) = 0 := by
          intro x hx hxd
          by_contra hnz
          have h21ne := hbad_iff.mpr ⟨x, hx, hxd, hnz⟩
          exact h21ne h21_0
        refine ⟨.normal, st2, _, hseq, ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12,
          s13, s14, s15, s16, s17, s18, s19, s20, fun x hx => ⟨hB x hx, hnobad x hx⟩, hfr⟩, ?_⟩
        dsimp only at hc1 hc2 ⊢; simp only [Expr.size_reg, Expr.size_const, Nat.sub_zero] at hc2
        omega

end MinCostFlow.Expander
