/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MinCostFlow.Expander.DecomposeProgRegs

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Setup Word RAM Subroutines (`computeEllStmt`, `computeLayoutStmt`, `initMemoryStmt`)

Verifies `computeEllStmt`, `computeLayoutStmt`, and `initMemoryStmt` for multi-level `DecomposeImpl`.
-/

namespace MinCostFlow.Expander

open MinCostFlow.Cited MinCostFlow.Spanner WordRAM

public section

/-! ## 4. Setup Stmts (`computeEllStmt`, `computeLayoutStmt`, `initMemoryStmt`) -/

@[expose] def computeEllStmt : Stmt :=
  seqStmts
    [ .assign rTmp1 (.bin .div (.reg rM) (.reg rN))
    , .assign rTmp2 (.const 0)
    , .loop (.bin .lt (.const 1) (.reg rTmp1))
        (seqStmts
          [ .assign rTmp1 (.bin .div (.reg rTmp1) (.const 2))
          , .assign rTmp2 (.bin .add (.reg rTmp2) (.const 1)) ])
    , .assign rEll (.bin .add (.reg rTmp2) (.const 1)) ]

lemma computeEllStmt_noRand : computeEllStmt.NoRand := by
  simp [computeEllStmt, seqStmts, Stmt.NoRand]

lemma computeEll_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (n m : ℕ) (hn : 1 ≤ n) (hnm : n < m) (hm_w : m < 2 ^ w) (hw4 : 4 ≤ 2 ^ w)
    (st₀ : State) (hst_n : st₀.regs rN = n) (hst_m : st₀.regs rM = m) :
    ∃ st' c,
      Runs w p ω computeEllStmt st₀ .normal st' c ∧
      st'.regs rEll = Nat.log 2 (m / n) + 1 ∧
      st'.mem = st₀.mem ∧
      st'.pos = st₀.pos ∧
      (∀ r, r ≠ rEll → r ≠ rTmp1 → r ≠ rTmp2 → st'.regs r = st₀.regs r) ∧
      c ≤ 13 * (Nat.log 2 (m / n) + 1) + 20 := by
  have hw0 : w ≠ 0 := by intro h0; subst h0; simp at hw4
  have hdiv_pos : 1 ≤ m / n := Nat.div_pos (le_of_lt hnm) hn
  have hdiv_le : m / n ≤ m := Nat.div_le_self m n
  have hdiv_w : m / n < 2 ^ w := by omega
  have hlog_w : Nat.log 2 (m / n) + 1 < 2 ^ w := by
    have := natLog2_add_one_le_self' hdiv_pos; omega
  let st1 : State := { st₀ with regs := Function.update st₀.regs rTmp1 (m / n) }
  have h1 : Runs w p ω (.assign rTmp1 (.bin .div (.reg rM) (.reg rN))) st₀ .normal st1 4 := by
    apply runs_assign_iff.mpr
    refine ⟨m / n, by simp [Expr.eval, BinOp.eval, hst_m, hst_n, hdiv_w], rfl, rfl, by simp [Expr.size]⟩
  let st2 : State := { st1 with regs := Function.update st1.regs rTmp2 0 }
  have h2 : Runs w p ω (.assign rTmp2 (.const 0)) st1 .normal st2 2 := by
    apply runs_assign_iff.mpr
    refine ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
  obtain ⟨st3, c3, h3, h3_log, h3_mem, h3_pos, h3_regs, hc3⟩ :=
    log2_loop_runs (w := w) (p := p) (ω := ω) rTmp1 rTmp2 (by decide) (m / n) hdiv_w hw4 st2
      (by simp [st2, st1, Function.update_of_ne, Function.update_self])
      (by simp [st2, Function.update_self]) (by omega)
  let st4 : State := { st3 with regs := Function.update st3.regs rEll (Nat.log 2 (m / n) + 1) }
  have h4 : Runs w p ω (.assign rEll (.bin .add (.reg rTmp2) (.const 1))) st3 .normal st4 4 := by
    apply runs_assign_iff.mpr
    refine ⟨Nat.log 2 (m / n) + 1, by
      simp [Expr.eval, BinOp.eval, h3_log, hw0, hlog_w], rfl, rfl, by simp [Expr.size]⟩
  have hfull := runs_seq h1 (runs_seq h2 (runs_seq h3 h4))
  have hce_eq :
      computeEllStmt =
        .seq (.assign rTmp1 (.bin .div (.reg rM) (.reg rN)))
          (.seq (.assign rTmp2 (.const 0))
            (.seq (.loop (.bin .lt (.const 1) (.reg rTmp1))
                (seqStmts
                  [ .assign rTmp1 (.bin .div (.reg rTmp1) (.const 2))
                  , .assign rTmp2 (.bin .add (.reg rTmp2) (.const 1)) ]))
              (.assign rEll (.bin .add (.reg rTmp2) (.const 1))))) := rfl
  rw [← hce_eq] at hfull
  refine ⟨st4, _, hfull, by simp [st4], h3_mem, h3_pos, ?_, ?_⟩
  · intro r hrE hr1 hr2
    dsimp [st4]
    rw [Function.update_of_ne hrE, h3_regs r hr1 hr2]
    dsimp [st2, st1]
    rw [Function.update_of_ne hr2, Function.update_of_ne hr1]
  · omega

@[expose] def computeLayoutStmt : Stmt :=
  seqStmts
    [ .assign rTmp1 (.bin .add (.bin .mul (.const 2) (.reg rM)) (.const 1))
    , .assign rTmp2 (.const 0)
    , .loop (.bin .lt (.const 1) (.reg rTmp1))
        (seqStmts
          [ .assign rTmp1 (.bin .div (.reg rTmp1) (.const 2))
          , .assign rTmp2 (.bin .add (.reg rTmp2) (.const 1)) ])
    , .assign rTmp3 (.bin .add (.reg rTmp2) (.const 1)) -- log2m1
    , .assign rTmp1
        (.bin .add
          (.bin .mul (.const 4)
            (.bin .mul (.bin .add (.bin .mul (.const 4) (.reg rDphi)) (.const 2)) (.reg rTmp3)))
          (.const 2)) -- H_cap
    , .assign rStatePtr (.bin .add (.reg rOutH) (.bin .add (.const 4) (.bin .mul (.const 5) (.reg rM))))
    , .assign rBounds (.bin .add (.reg rStatePtr) (.const 3))
    , .assign rLvlArr (.bin .add (.reg rBounds) (.bin .add (.bin .mul (.const 2) (.reg rM)) (.const 6)))
    , .assign rCurG (.bin .add (.reg rLvlArr) (.reg rM))
    , .assign rCurIdx (.bin .add (.reg rCurG) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg rM))))
    , .assign rNextG (.bin .add (.reg rCurIdx) (.reg rM))
    , .assign rNextIdx (.bin .add (.reg rNextG) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg rM))))
    , .assign rTw (.bin .add (.reg rNextIdx) (.reg rM))
    , .assign rBuf (.bin .add (.reg rTw)
        (.bin .add (.const 6) (.bin .add (.bin .mul (.const 8) (.reg rN)) (.bin .mul (.const 18) (.reg rM)))))
    , .assign rWork (.bin .add (.reg rBuf)
        (.bin .add (.bin .mul (.const 12) (.reg rN)) (.bin .add (.bin .mul (.const 2) (.reg rM)) (.const 2))))
    , .assign rKept (.bin .add (.reg rWork)
        (.bin .add (.bin .mul (.const 17) (.reg rN))
          (.bin .add (.bin .mul (.const 7) (.reg rM))
            (.bin .add (.bin .mul (.const 2) (.reg rTmp1)) (.const 5)))))
    , .assign rArena (.bin .add (.reg rKept) (.reg rN))
    , .assign rZC (.bin .add (.reg rArena) (.bin .mul (.const 4) (.reg rM)))
    , .assign rLvl (.reg rEll)
    , .assign rD (.bin .shiftLeft (.const 1) (.reg rEll)) ]

lemma computeLayoutStmt_noRand : computeLayoutStmt.NoRand := by
  simp [computeLayoutStmt, seqStmts, Stmt.NoRand]

lemma computeLayout_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (gAddr h n m ℓ D_phi : ℕ) (h1n : 1 ≤ n) (hnm : n < m)
    (hℓ_pow : 2 ^ ℓ ≤ 2 * m) (hzc_w : (mkDecompLayout h n m D_phi).zeroCursor₀ < 2 ^ w)
    (hw20 : 20 ≤ 2 ^ w) (st₀ : State)
    (hr0 : st₀.regs rGAddr = gAddr) (hr1 : st₀.regs rOutH = h) (hr2 : st₀.regs rN = n)
    (hr3 : st₀.regs rM = m) (hr4 : st₀.regs rEll = ℓ) (hr5 : st₀.regs rDphi = D_phi) :
    let L := mkDecompLayout h n m D_phi
    ∃ st' c,
      Runs w p ω computeLayoutStmt st₀ .normal st' c ∧
      DecompRegs gAddr h n m ℓ D_phi ℓ (2 ^ ℓ) L.g0Addr L.idx0Addr L.g1Addr L.idx1Addr L st' ∧
      st'.mem = st₀.mem ∧
      st'.pos = st₀.pos ∧
      c ≤ 13 * (Nat.log 2 (2 * m + 1) + 1) + 250 := by
  dsimp only
  set L := mkDecompLayout h n m D_phi
  have hw0 : w ≠ 0 := by intro h0; subst h0; simp at hw20
  let Llog := Nat.log 2 (2 * m + 1) + 1
  let DpL := D_phi * Llog
  have hlog2m : Llog ≤ 2 * m + 1 := natLog2_add_one_le_self' (by omega)
  have hLlog_pos : 1 ≤ Llog := by dsimp [Llog]; omega
  have hzc_eq : L.zeroCursor₀ = h + 34 + 38 * n + 45 * m + 32 * DpL + 16 * Llog := by
    simp only [L, mkDecompLayout, groupBufSize, partWorkSize, pruneWorkSpace, Llog, DpL]; ring
  have h2m1_w : 2 * m + 1 < 2 ^ w := by omega
  let H_cap := 4 * (4 * D_phi + 2) * Llog + 2
  have hH_cap_eq : H_cap = 16 * DpL + 8 * Llog + 2 := by dsimp [H_cap, DpL]; ring
  have hH_2w : 2 * H_cap < 2 ^ w := by rw [hH_cap_eq]; omega
  have ha_w : ∀ x ≤ L.zeroCursor₀, x < 2 ^ w := fun x hx => by omega
  have hL_sp : L.statePtr = h + 4 + 5 * m := rfl
  have hL_bnd : L.boundsAddr = L.statePtr + 3 := rfl
  have hL_lvl : L.lvlArrAddr = L.boundsAddr + 2 * m + 6 := rfl
  have hL_g0 : L.g0Addr = L.lvlArrAddr + m := rfl
  have hL_i0 : L.idx0Addr = L.g0Addr + 2 + 2 * m := rfl
  have hL_g1 : L.g1Addr = L.idx0Addr + m := rfl
  have hL_i1 : L.idx1Addr = L.g1Addr + 2 + 2 * m := rfl
  have hL_tw : L.twAddr = L.idx1Addr + m := rfl
  have hL_buf : L.bufAddr = L.twAddr + 6 + 8 * n + 18 * m := rfl
  have hL_work : L.workAddr = L.bufAddr + (12 * n + 2 * m + 2) := by
    change L.bufAddr + groupBufSize n m = _; simp [groupBufSize]
  have hL_kept : L.keptVertAddr = L.workAddr + (17 * n + 7 * m + 2 * H_cap + 5) := by
    change L.workAddr + partWorkSize n m H_cap = _; simp [partWorkSize, pruneWorkSpace]; omega
  have hL_ar : L.arena₀ = L.keptVertAddr + n := rfl
  have hL_zc : L.zeroCursor₀ = L.arena₀ + 4 * m := rfl
  have h4Dphi_mul_eq : (4 * D_phi + 2) * Llog = 4 * DpL + 2 * Llog := by dsimp [DpL]; ring
  have hDphi_le_DpL : D_phi ≤ DpL := Nat.le_mul_of_pos_right D_phi hLlog_pos
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  have h3_w : 3 < 2 ^ w := by omega
  have h4_w : 4 < 2 ^ w := by omega
  have h5_w : 5 < 2 ^ w := by omega
  have h6_w : 6 < 2 ^ w := by omega
  have h7_w : 7 < 2 ^ w := by omega
  have h8_w : 8 < 2 ^ w := by omega
  have h12_w : 12 < 2 ^ w := by omega
  have h17_w : 17 < 2 ^ w := by omega
  have h18_w : 18 < 2 ^ w := by omega
  have h4D_w : 4 * D_phi < 2 ^ w := by omega
  have h4D2_w : 4 * D_phi + 2 < 2 ^ w := by omega
  have h4D2L_w : (4 * D_phi + 2) * Llog < 2 ^ w := by rw [h4Dphi_mul_eq]; omega
  have h4_4D2L_w : 4 * ((4 * D_phi + 2) * Llog) < 2 ^ w := by
    rw [show 4 * ((4 * D_phi + 2) * Llog) = 16 * DpL + 8 * Llog by dsimp [DpL]; ring]; omega
  have hHcap_eval_w : 4 * ((4 * D_phi + 2) * Llog) + 2 < 2 ^ w := by
    rw [show 4 * ((4 * D_phi + 2) * Llog) + 2 = H_cap by dsimp [H_cap]; ring]; omega
  have h2m_w : 2 * m < 2 ^ w := by omega
  have h5m_w : 5 * m < 2 ^ w := by omega
  have h4_5m_w : 4 + 5 * m < 2 ^ w := by omega
  have hsp_eq : h + (4 + 5 * m) = L.statePtr := by omega
  have hsp_w : h + (4 + 5 * m) < 2 ^ w := by omega
  have hbnd_w : L.statePtr + 3 < 2 ^ w := by omega
  have h2m6_w : 2 * m + 6 < 2 ^ w := by omega
  have hlvl_eq : L.boundsAddr + (2 * m + 6) = L.lvlArrAddr := by omega
  have hlvl_w : L.boundsAddr + (2 * m + 6) < 2 ^ w := by omega
  have hg0_w : L.lvlArrAddr + m < 2 ^ w := by omega
  have h2_2m_w : 2 + 2 * m < 2 ^ w := by omega
  have hi0_eq : L.g0Addr + (2 + 2 * m) = L.idx0Addr := by omega
  have hi0_w : L.g0Addr + (2 + 2 * m) < 2 ^ w := by omega
  have hg1_w : L.idx0Addr + m < 2 ^ w := by omega
  have hi1_eq : L.g1Addr + (2 + 2 * m) = L.idx1Addr := by omega
  have hi1_w : L.g1Addr + (2 + 2 * m) < 2 ^ w := by omega
  have htw_w : L.idx1Addr + m < 2 ^ w := by omega
  have h8n_w : 8 * n < 2 ^ w := by omega
  have h18m_w : 18 * m < 2 ^ w := by omega
  have h8n18m_w : 8 * n + 18 * m < 2 ^ w := by omega
  have h6_8n18m_w : 6 + (8 * n + 18 * m) < 2 ^ w := by omega
  have hbuf_eq : L.twAddr + (6 + (8 * n + 18 * m)) = L.bufAddr := by omega
  have hbuf_w : L.twAddr + (6 + (8 * n + 18 * m)) < 2 ^ w := by omega
  have h12n_w : 12 * n < 2 ^ w := by omega
  have h2m2_w : 2 * m + 2 < 2 ^ w := by omega
  have h12n2m2_w : 12 * n + (2 * m + 2) < 2 ^ w := by omega
  have hwork_eq : L.bufAddr + (12 * n + (2 * m + 2)) = L.workAddr := by omega
  have hwork_w : L.bufAddr + (12 * n + (2 * m + 2)) < 2 ^ w := by omega
  have h17n_w : 17 * n < 2 ^ w := by omega
  have h7m_w : 7 * m < 2 ^ w := by omega
  have h2H5_w : 2 * H_cap + 5 < 2 ^ w := by omega
  have h7m2H5_w : 7 * m + (2 * H_cap + 5) < 2 ^ w := by omega
  have h17n7m2H5_w : 17 * n + (7 * m + (2 * H_cap + 5)) < 2 ^ w := by omega
  have hkept_eq : L.workAddr + (17 * n + (7 * m + (2 * H_cap + 5))) = L.keptVertAddr := by omega
  have hkept_w : L.workAddr + (17 * n + (7 * m + (2 * H_cap + 5))) < 2 ^ w := by omega
  have har_w : L.keptVertAddr + n < 2 ^ w := by omega
  have h4m_w : 4 * m < 2 ^ w := by omega
  have hzc_w' : L.arena₀ + 4 * m < 2 ^ w := by omega
  have h1shl_w : 1 <<< ℓ < 2 ^ w := by rw [Nat.one_shiftLeft]; omega
  have hlog1_w : Llog < 2 ^ w := by omega
  have hH_eq_eval : 4 * ((4 * D_phi + 2) * Llog) + 2 = H_cap := by dsimp [H_cap]; ring
  let st1 : State := { st₀ with regs := Function.update st₀.regs rTmp1 (2 * m + 1) }
  have st1_run : Runs w p ω (.assign rTmp1 (.bin .add (.bin .mul (.const 2) (.reg rM)) (.const 1)))
      st₀ .normal st1 6 := by
    apply runs_assign_iff.mpr
    refine ⟨2 * m + 1,
      ev_add (ev_mul (ev_const h2_w) (ev_reg hr3) h2m_w) (ev_const h1_w) h2m1_w,
      rfl, rfl, by simp [Expr.size]⟩
  let st2 : State := { st1 with regs := Function.update st1.regs rTmp2 0 }
  have st2_run : Runs w p ω (.assign rTmp2 (.const 0)) st1 .normal st2 2 := by
    apply runs_assign_iff.mpr
    refine ⟨0, ev_const h0_w, rfl, rfl, by simp [Expr.size]⟩
  obtain ⟨st3, c3, st3_run, h3_log, h3_mem, h3_pos, h3_regs, hc3⟩ :=
    log2_loop_runs (w := w) (p := p) (ω := ω) rTmp1 rTmp2 (by decide) (2 * m + 1) h2m1_w (by omega) st2
      (by simp [st2, st1, Function.update_of_ne, Function.update_self])
      (by simp [st2, Function.update_self]) (by omega)
  let st4 : State := { st3 with regs := Function.update st3.regs rTmp3 Llog }
  have st4_run : Runs w p ω (.assign rTmp3 (.bin .add (.reg rTmp2) (.const 1))) st3 .normal st4 4 := by
    apply runs_assign_iff.mpr
    refine ⟨Llog, ev_eq_of (ev_add (ev_reg h3_log) (ev_const h1_w) hlog1_w) rfl,
      rfl, rfl, by simp [Expr.size]⟩
  have h4_g : st4.regs rGAddr = gAddr := by
    dsimp [st4]; rw [Function.update_of_ne (by decide), h3_regs _ (by decide) (by decide)]
    simp [st2, st1, Function.update_of_ne, hr0]
  have h4_h : st4.regs rOutH = h := by
    dsimp [st4]; rw [Function.update_of_ne (by decide), h3_regs _ (by decide) (by decide)]
    simp [st2, st1, Function.update_of_ne, hr1]
  have h4_n : st4.regs rN = n := by
    dsimp [st4]; rw [Function.update_of_ne (by decide), h3_regs _ (by decide) (by decide)]
    simp [st2, st1, Function.update_of_ne, hr2]
  have h4_m : st4.regs rM = m := by
    dsimp [st4]; rw [Function.update_of_ne (by decide), h3_regs _ (by decide) (by decide)]
    simp [st2, st1, Function.update_of_ne, hr3]
  have h4_ell : st4.regs rEll = ℓ := by
    dsimp [st4]; rw [Function.update_of_ne (by decide), h3_regs _ (by decide) (by decide)]
    simp [st2, st1, Function.update_of_ne, hr4]
  have h4_dphi : st4.regs rDphi = D_phi := by
    dsimp [st4]; rw [Function.update_of_ne (by decide), h3_regs _ (by decide) (by decide)]
    simp [st2, st1, Function.update_of_ne, hr5]
  have h4_log : st4.regs rTmp3 = Llog := by simp [st4]
  let st5 : State := { st4 with regs := Function.update st4.regs rTmp1 H_cap }
  have st5_run : Runs w p ω
      (.assign rTmp1 (.bin .add (.bin .mul (.const 4)
        (.bin .mul (.bin .add (.bin .mul (.const 4) (.reg rDphi)) (.const 2)) (.reg rTmp3))) (.const 2)))
      st4 .normal st5 12 := by
    apply runs_assign_iff.mpr
    refine ⟨H_cap,
      ev_eq_of
        (ev_add
          (ev_mul (ev_const h4_w)
            (ev_mul
              (ev_add
                (ev_mul (ev_const h4_w) (ev_reg h4_dphi) h4D_w)
                (ev_const h2_w) h4D2_w)
              (ev_reg h4_log) h4D2L_w)
            h4_4D2L_w)
          (ev_const h2_w) hHcap_eval_w)
        hH_eq_eval,
      rfl, rfl, by simp [Expr.size]⟩
  let st6 : State := { st5 with regs := Function.update st5.regs rStatePtr L.statePtr }
  have h5_h : st5.regs rOutH = h := by dsimp [st5]; rw [Function.update_of_ne (by decide), h4_h]
  have h5_m : st5.regs rM = m := by dsimp [st5]; rw [Function.update_of_ne (by decide), h4_m]
  have h5_n : st5.regs rN = n := by dsimp [st5]; rw [Function.update_of_ne (by decide), h4_n]
  have h5_ell : st5.regs rEll = ℓ := by dsimp [st5]; rw [Function.update_of_ne (by decide), h4_ell]
  have st6_run : Runs w p ω (.assign rStatePtr (.bin .add (.reg rOutH) (.bin .add (.const 4) (.bin .mul (.const 5) (.reg rM)))))
      st5 .normal st6 8 := by
    apply runs_assign_iff.mpr
    refine ⟨L.statePtr,
      ev_eq_of
        (ev_add (ev_reg h5_h)
          (ev_add (ev_const h4_w) (ev_mul (ev_const h5_w) (ev_reg h5_m) h5m_w) h4_5m_w)
          hsp_w)
        hsp_eq,
      rfl, rfl, by simp [Expr.size]⟩
  let st7 : State := { st6 with regs := Function.update st6.regs rBounds L.boundsAddr }
  have h6_sp : st6.regs rStatePtr = L.statePtr := by simp [st6]
  have h6_m : st6.regs rM = m := by dsimp [st6]; rw [Function.update_of_ne (by decide), h5_m]
  have h6_n : st6.regs rN = n := by dsimp [st6]; rw [Function.update_of_ne (by decide), h5_n]
  have h6_ell : st6.regs rEll = ℓ := by dsimp [st6]; rw [Function.update_of_ne (by decide), h5_ell]
  have st7_run : Runs w p ω (.assign rBounds (.bin .add (.reg rStatePtr) (.const 3))) st6 .normal st7 4 := by
    apply runs_assign_iff.mpr
    refine ⟨L.boundsAddr,
      ev_eq_of (ev_add (ev_reg h6_sp) (ev_const h3_w) hbnd_w) rfl,
      rfl, rfl, by simp [Expr.size]⟩
  let st8 : State := { st7 with regs := Function.update st7.regs rLvlArr L.lvlArrAddr }
  have h7_bnd : st7.regs rBounds = L.boundsAddr := by simp [st7]
  have h7_m : st7.regs rM = m := by dsimp [st7]; rw [Function.update_of_ne (by decide), h6_m]
  have h7_n : st7.regs rN = n := by dsimp [st7]; rw [Function.update_of_ne (by decide), h6_n]
  have h7_ell : st7.regs rEll = ℓ := by dsimp [st7]; rw [Function.update_of_ne (by decide), h6_ell]
  have st8_run : Runs w p ω (.assign rLvlArr (.bin .add (.reg rBounds) (.bin .add (.bin .mul (.const 2) (.reg rM)) (.const 6))))
      st7 .normal st8 8 := by
    apply runs_assign_iff.mpr
    refine ⟨L.lvlArrAddr,
      ev_eq_of
        (ev_add (ev_reg h7_bnd)
          (ev_add (ev_mul (ev_const h2_w) (ev_reg h7_m) h2m_w) (ev_const h6_w) h2m6_w)
          hlvl_w)
        hlvl_eq,
      rfl, rfl, by simp [Expr.size]⟩
  let st9 : State := { st8 with regs := Function.update st8.regs rCurG L.g0Addr }
  have h8_lvl : st8.regs rLvlArr = L.lvlArrAddr := by simp [st8]
  have h8_m : st8.regs rM = m := by dsimp [st8]; rw [Function.update_of_ne (by decide), h7_m]
  have h8_n : st8.regs rN = n := by dsimp [st8]; rw [Function.update_of_ne (by decide), h7_n]
  have h8_ell : st8.regs rEll = ℓ := by dsimp [st8]; rw [Function.update_of_ne (by decide), h7_ell]
  have st9_run : Runs w p ω (.assign rCurG (.bin .add (.reg rLvlArr) (.reg rM))) st8 .normal st9 4 := by
    apply runs_assign_iff.mpr
    refine ⟨L.g0Addr,
      ev_eq_of (ev_add (ev_reg h8_lvl) (ev_reg h8_m) hg0_w) rfl,
      rfl, rfl, by simp [Expr.size]⟩
  let st10 : State := { st9 with regs := Function.update st9.regs rCurIdx L.idx0Addr }
  have h9_cg : st9.regs rCurG = L.g0Addr := by simp [st9]
  have h9_m : st9.regs rM = m := by dsimp [st9]; rw [Function.update_of_ne (by decide), h8_m]
  have h9_n : st9.regs rN = n := by dsimp [st9]; rw [Function.update_of_ne (by decide), h8_n]
  have h9_ell : st9.regs rEll = ℓ := by dsimp [st9]; rw [Function.update_of_ne (by decide), h8_ell]
  have st10_run : Runs w p ω (.assign rCurIdx (.bin .add (.reg rCurG) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg rM)))))
      st9 .normal st10 8 := by
    apply runs_assign_iff.mpr
    refine ⟨L.idx0Addr,
      ev_eq_of
        (ev_add (ev_reg h9_cg)
          (ev_add (ev_const h2_w) (ev_mul (ev_const h2_w) (ev_reg h9_m) h2m_w) h2_2m_w)
          hi0_w)
        hi0_eq,
      rfl, rfl, by simp [Expr.size]⟩
  let st11 : State := { st10 with regs := Function.update st10.regs rNextG L.g1Addr }
  have h10_ci : st10.regs rCurIdx = L.idx0Addr := by simp [st10]
  have h10_m : st10.regs rM = m := by dsimp [st10]; rw [Function.update_of_ne (by decide), h9_m]
  have h10_n : st10.regs rN = n := by dsimp [st10]; rw [Function.update_of_ne (by decide), h9_n]
  have h10_ell : st10.regs rEll = ℓ := by dsimp [st10]; rw [Function.update_of_ne (by decide), h9_ell]
  have st11_run : Runs w p ω (.assign rNextG (.bin .add (.reg rCurIdx) (.reg rM))) st10 .normal st11 4 := by
    apply runs_assign_iff.mpr
    refine ⟨L.g1Addr,
      ev_eq_of (ev_add (ev_reg h10_ci) (ev_reg h10_m) hg1_w) rfl,
      rfl, rfl, by simp [Expr.size]⟩
  let st12 : State := { st11 with regs := Function.update st11.regs rNextIdx L.idx1Addr }
  have h11_ng : st11.regs rNextG = L.g1Addr := by simp [st11]
  have h11_m : st11.regs rM = m := by dsimp [st11]; rw [Function.update_of_ne (by decide), h10_m]
  have h11_n : st11.regs rN = n := by dsimp [st11]; rw [Function.update_of_ne (by decide), h10_n]
  have h11_ell : st11.regs rEll = ℓ := by dsimp [st11]; rw [Function.update_of_ne (by decide), h10_ell]
  have st12_run : Runs w p ω (.assign rNextIdx (.bin .add (.reg rNextG) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg rM)))))
      st11 .normal st12 8 := by
    apply runs_assign_iff.mpr
    refine ⟨L.idx1Addr,
      ev_eq_of
        (ev_add (ev_reg h11_ng)
          (ev_add (ev_const h2_w) (ev_mul (ev_const h2_w) (ev_reg h11_m) h2m_w) h2_2m_w)
          hi1_w)
        hi1_eq,
      rfl, rfl, by simp [Expr.size]⟩
  let st13 : State := { st12 with regs := Function.update st12.regs rTw L.twAddr }
  have h12_ni : st12.regs rNextIdx = L.idx1Addr := by simp [st12]
  have h12_m : st12.regs rM = m := by dsimp [st12]; rw [Function.update_of_ne (by decide), h11_m]
  have h12_n : st12.regs rN = n := by dsimp [st12]; rw [Function.update_of_ne (by decide), h11_n]
  have h12_ell : st12.regs rEll = ℓ := by dsimp [st12]; rw [Function.update_of_ne (by decide), h11_ell]
  have st13_run : Runs w p ω (.assign rTw (.bin .add (.reg rNextIdx) (.reg rM))) st12 .normal st13 4 := by
    apply runs_assign_iff.mpr
    refine ⟨L.twAddr,
      ev_eq_of (ev_add (ev_reg h12_ni) (ev_reg h12_m) htw_w) rfl,
      rfl, rfl, by simp [Expr.size]⟩
  let st14 : State := { st13 with regs := Function.update st13.regs rBuf L.bufAddr }
  have h13_tw : st13.regs rTw = L.twAddr := by simp [st13]
  have h13_m : st13.regs rM = m := by dsimp [st13]; rw [Function.update_of_ne (by decide), h12_m]
  have h13_n : st13.regs rN = n := by dsimp [st13]; rw [Function.update_of_ne (by decide), h12_n]
  have h13_ell : st13.regs rEll = ℓ := by dsimp [st13]; rw [Function.update_of_ne (by decide), h12_ell]
  have st14_run : Runs w p ω (.assign rBuf (.bin .add (.reg rTw)
      (.bin .add (.const 6) (.bin .add (.bin .mul (.const 8) (.reg rN)) (.bin .mul (.const 18) (.reg rM))))))
      st13 .normal st14 12 := by
    apply runs_assign_iff.mpr
    refine ⟨L.bufAddr,
      ev_eq_of
        (ev_add (ev_reg h13_tw)
          (ev_add (ev_const h6_w)
            (ev_add (ev_mul (ev_const h8_w) (ev_reg h13_n) h8n_w)
              (ev_mul (ev_const h18_w) (ev_reg h13_m) h18m_w) h8n18m_w)
            h6_8n18m_w)
          hbuf_w)
        hbuf_eq,
      rfl, rfl, by simp [Expr.size]⟩
  let st15 : State := { st14 with regs := Function.update st14.regs rWork L.workAddr }
  have h14_buf : st14.regs rBuf = L.bufAddr := by simp [st14]
  have h14_m : st14.regs rM = m := by dsimp [st14]; rw [Function.update_of_ne (by decide), h13_m]
  have h14_n : st14.regs rN = n := by dsimp [st14]; rw [Function.update_of_ne (by decide), h13_n]
  have h14_ell : st14.regs rEll = ℓ := by dsimp [st14]; rw [Function.update_of_ne (by decide), h13_ell]
  have st15_run : Runs w p ω (.assign rWork (.bin .add (.reg rBuf)
      (.bin .add (.bin .mul (.const 12) (.reg rN)) (.bin .add (.bin .mul (.const 2) (.reg rM)) (.const 2)))))
      st14 .normal st15 12 := by
    apply runs_assign_iff.mpr
    refine ⟨L.workAddr,
      ev_eq_of
        (ev_add (ev_reg h14_buf)
          (ev_add (ev_mul (ev_const h12_w) (ev_reg h14_n) h12n_w)
            (ev_add (ev_mul (ev_const h2_w) (ev_reg h14_m) h2m_w)
              (ev_const h2_w) h2m2_w)
            h12n2m2_w)
          hwork_w)
        hwork_eq,
      rfl, rfl, by simp [Expr.size]⟩
  let st16 : State := { st15 with regs := Function.update st15.regs rKept L.keptVertAddr }
  have h15_work : st15.regs rWork = L.workAddr := by simp [st15]
  have h15_m : st15.regs rM = m := by dsimp [st15]; rw [Function.update_of_ne (by decide), h14_m]
  have h15_n : st15.regs rN = n := by dsimp [st15]; rw [Function.update_of_ne (by decide), h14_n]
  have h15_ell : st15.regs rEll = ℓ := by dsimp [st15]; rw [Function.update_of_ne (by decide), h14_ell]
  have h15_t1 : st15.regs rTmp1 = H_cap := by
    dsimp [st15, st14, st13, st12, st11, st10, st9, st8, st7, st6, st5]
    repeat rw [Function.update_of_ne (by decide)]
    exact Function.update_self _ _ _
  have st16_run : Runs w p ω (.assign rKept (.bin .add (.reg rWork)
      (.bin .add (.bin .mul (.const 17) (.reg rN))
        (.bin .add (.bin .mul (.const 7) (.reg rM))
          (.bin .add (.bin .mul (.const 2) (.reg rTmp1)) (.const 5))))))
      st15 .normal st16 16 := by
    apply runs_assign_iff.mpr
    refine ⟨L.keptVertAddr,
      ev_eq_of
        (ev_add (ev_reg h15_work)
          (ev_add (ev_mul (ev_const h17_w) (ev_reg h15_n) h17n_w)
            (ev_add (ev_mul (ev_const h7_w) (ev_reg h15_m) h7m_w)
              (ev_add (ev_mul (ev_const h2_w) (ev_reg h15_t1) hH_2w)
                (ev_const h5_w) h2H5_w)
              h7m2H5_w)
            h17n7m2H5_w)
          hkept_w)
        hkept_eq,
      rfl, rfl, by simp [Expr.size]⟩
  let st17 : State := { st16 with regs := Function.update st16.regs rArena L.arena₀ }
  have h16_kept : st16.regs rKept = L.keptVertAddr := by simp [st16]
  have h16_m : st16.regs rM = m := by dsimp [st16]; rw [Function.update_of_ne (by decide), h15_m]
  have h16_n : st16.regs rN = n := by dsimp [st16]; rw [Function.update_of_ne (by decide), h15_n]
  have h16_ell : st16.regs rEll = ℓ := by dsimp [st16]; rw [Function.update_of_ne (by decide), h15_ell]
  have st17_run : Runs w p ω (.assign rArena (.bin .add (.reg rKept) (.reg rN))) st16 .normal st17 4 := by
    apply runs_assign_iff.mpr
    refine ⟨L.arena₀,
      ev_eq_of (ev_add (ev_reg h16_kept) (ev_reg h16_n) har_w) rfl,
      rfl, rfl, by simp [Expr.size]⟩
  let st18 : State := { st17 with regs := Function.update st17.regs rZC L.zeroCursor₀ }
  have h17_ar : st17.regs rArena = L.arena₀ := by simp [st17]
  have h17_m : st17.regs rM = m := by dsimp [st17]; rw [Function.update_of_ne (by decide), h16_m]
  have h17_ell : st17.regs rEll = ℓ := by dsimp [st17]; rw [Function.update_of_ne (by decide), h16_ell]
  have st18_run : Runs w p ω (.assign rZC (.bin .add (.reg rArena) (.bin .mul (.const 4) (.reg rM))))
      st17 .normal st18 6 := by
    apply runs_assign_iff.mpr
    refine ⟨L.zeroCursor₀,
      ev_eq_of (ev_add (ev_reg h17_ar) (ev_mul (ev_const h4_w) (ev_reg h17_m) h4m_w) hzc_w') rfl,
      rfl, rfl, by simp [Expr.size]⟩
  let st19 : State := { st18 with regs := Function.update st18.regs rLvl ℓ }
  have h18_ell : st18.regs rEll = ℓ := by dsimp [st18]; rw [Function.update_of_ne (by decide), h17_ell]
  have st19_run : Runs w p ω (.assign rLvl (.reg rEll)) st18 .normal st19 2 := by
    apply runs_assign_iff.mpr
    refine ⟨ℓ, ev_reg h18_ell, rfl, rfl, by simp [Expr.size]⟩
  let st20 : State := { st19 with regs := Function.update st19.regs rD (2 ^ ℓ) }
  have h19_ell : st19.regs rEll = ℓ := by dsimp [st19]; rw [Function.update_of_ne (by decide), h18_ell]
  have st20_run : Runs w p ω (.assign rD (.bin .shiftLeft (.const 1) (.reg rEll))) st19 .normal st20 4 := by
    apply runs_assign_iff.mpr
    refine ⟨2 ^ ℓ,
      ev_eq_of (ev_shl (ev_const h1_w) (ev_reg h19_ell) h1shl_w) (Nat.one_shiftLeft ℓ),
      rfl, rfl, by simp [Expr.size]⟩
  have hfull := runs_seq st1_run (runs_seq st2_run (runs_seq st3_run (runs_seq st4_run
    (runs_seq st5_run (runs_seq st6_run (runs_seq st7_run (runs_seq st8_run
      (runs_seq st9_run (runs_seq st10_run (runs_seq st11_run (runs_seq st12_run
        (runs_seq st13_run (runs_seq st14_run (runs_seq st15_run (runs_seq st16_run
          (runs_seq st17_run (runs_seq st18_run (runs_seq st19_run st20_run))))))))))))))))))
  change Runs w p ω computeLayoutStmt st₀ .normal st20 _ at hfull
  refine ⟨st20, _, hfull, ?_, h3_mem, h3_pos, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [st20, st19, st18, st17, st16, st15, st14, st13, st12, st11, st10, st9, st8, st7, st6, st5,
        Function.update_self, Function.update_of_ne, h4_g, h4_h, h4_n, h4_m, h4_ell, h4_dphi]
  · linarith [hc3]

@[expose] def initMemoryStmt : Stmt :=
  seqStmts
    [ .store (.reg rStatePtr) (.reg rArena)
    , .store (.bin .add (.reg rStatePtr) (.const 1)) (.reg rZC)
    , .store (.bin .add (.reg rStatePtr) (.const 2)) (.const 0)
    , .assign rTmp1 (.bin .add (.const 2) (.bin .mul (.const 2) (.reg rM)))
    , copyMemLoop rGAddr rCurG rTmp1 rTmp2
    , iotaRangeLoop rCurIdx rM rTmp2 ]

lemma initMemoryStmt_noRand : initMemoryStmt.NoRand := by
  simp [initMemoryStmt, seqStmts, Stmt.NoRand, copyMemLoop_noRand, iotaRangeLoop_noRand]

lemma initMemory_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (gAddr h ℓ D_phi : ℕ) (G : Cited.Graph) (st₀ : State)
    (hG_len : gAddr + G.encode.length ≤ h) (hga : GraphAt st₀.mem gAddr G)
    (hzc_w : (mkDecompLayout h G.n G.m D_phi).zeroCursor₀ < 2 ^ w) (hw4 : 4 ≤ 2 ^ w)
    (hregs : DecompRegs gAddr h G.n G.m ℓ D_phi ℓ (2 ^ ℓ)
      (mkDecompLayout h G.n G.m D_phi).g0Addr (mkDecompLayout h G.n G.m D_phi).idx0Addr
      (mkDecompLayout h G.n G.m D_phi).g1Addr (mkDecompLayout h G.n G.m D_phi).idx1Addr
      (mkDecompLayout h G.n G.m D_phi) st₀) :
    let L := mkDecompLayout h G.n G.m D_phi
    ∃ st' c,
      Runs w p ω initMemoryStmt st₀ .normal st' c ∧
      DecompRegs gAddr h G.n G.m ℓ D_phi ℓ (2 ^ ℓ) L.g0Addr L.idx0Addr L.g1Addr L.idx1Addr L st' ∧
      st'.mem L.statePtr = L.arena₀ ∧
      st'.mem (L.statePtr + 1) = L.zeroCursor₀ ∧
      st'.mem (L.statePtr + 2) = 0 ∧
      GraphAt st'.mem L.g0Addr G ∧
      ListAt st'.mem L.idx0Addr (List.range G.m) ∧
      (∀ a, a < L.statePtr → st'.mem a = st₀.mem a) ∧
      (∀ a, L.boundsAddr ≤ a → a < L.g0Addr → st'.mem a = st₀.mem a) ∧
      (∀ a, L.idx0Addr + G.m ≤ a → st'.mem a = st₀.mem a) ∧
      st'.pos = st₀.pos ∧
      c ≤ 60 * G.m + 100 := by
  dsimp only
  set L := mkDecompLayout h G.n G.m D_phi
  have hw0 : w ≠ 0 := by intro h0; subst h0; simp at hw4
  have henc_len : G.encode.length = 2 + 2 * G.m := graph_encode_length G
  have hsep0 : h ≤ L.statePtr := by dsimp [L, mkDecompLayout]; omega
  have hsep1 : L.statePtr + 3 ≤ L.boundsAddr := by dsimp [L, mkDecompLayout]; omega
  have hsep2 : L.boundsAddr + 2 * G.m + 6 ≤ L.lvlArrAddr := by dsimp [L, mkDecompLayout]; omega
  have hsep3 : L.lvlArrAddr + G.m ≤ L.g0Addr := by dsimp [L, mkDecompLayout]; omega
  have hsep4 : L.g0Addr + (2 + 2 * G.m) ≤ L.idx0Addr := by dsimp [L, mkDecompLayout]; omega
  have hsep5 : L.idx0Addr + G.m ≤ L.zeroCursor₀ := by dsimp [L, mkDecompLayout]; omega
  have hsep_arena : L.statePtr < L.arena₀ := by dsimp [L, mkDecompLayout]; omega
  have hst_w : L.statePtr + 2 < 2 ^ w := by omega
  let st1 : State := { st₀ with mem := Function.update st₀.mem L.statePtr L.arena₀ }
  have h1 : Runs w p ω (.store (.reg rStatePtr) (.reg rArena)) st₀ .normal st1 3 := by
    apply runs_store_iff.mpr
    refine ⟨L.statePtr, L.arena₀, by simp [Expr.eval, hregs.2.2.2.2.2.2.1],
      by simp [Expr.eval, hregs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1],
      rfl, rfl, by simp [Expr.size]⟩
  let st2 : State := { st1 with mem := Function.update st1.mem (L.statePtr + 1) L.zeroCursor₀ }
  have h2 : Runs w p ω (.store (.bin .add (.reg rStatePtr) (.const 1)) (.reg rZC)) st1 .normal st2 5 := by
    apply runs_store_iff.mpr
    refine ⟨L.statePtr + 1, L.zeroCursor₀,
      by simp [Expr.eval, BinOp.eval, st1, hregs.2.2.2.2.2.2.1, hw0, show L.statePtr + 1 < 2 ^ w by omega],
      by simp [Expr.eval, st1, hregs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1],
      rfl, rfl, by simp [Expr.size]⟩
  let st3 : State := { st2 with mem := Function.update st2.mem (L.statePtr + 2) 0 }
  have h3 : Runs w p ω (.store (.bin .add (.reg rStatePtr) (.const 2)) (.const 0)) st2 .normal st3 5 := by
    apply runs_store_iff.mpr
    refine ⟨L.statePtr + 2, 0,
      by simp [Expr.eval, BinOp.eval, st2, st1, hregs.2.2.2.2.2.2.1, show 2 < 2 ^ w by omega, hst_w],
      by simp [Expr.eval], rfl, rfl, by simp [Expr.size]⟩
  let st4 : State := { st3 with regs := Function.update st3.regs rTmp1 (2 + 2 * G.m) }
  have h2m2_w : 2 + 2 * G.m < 2 ^ w := by omega
  have h4 : Runs w p ω (.assign rTmp1 (.bin .add (.const 2) (.bin .mul (.const 2) (.reg rM)))) st3 .normal st4 6 := by
    apply runs_assign_iff.mpr
    refine ⟨2 + 2 * G.m, by
      simp [Expr.eval, BinOp.eval, st3, st2, st1, hregs.2.2.2.1, show 2 < 2 ^ w by omega,
        show 2 * G.m < 2 ^ w by omega, h2m2_w],
      rfl, rfl, by simp [Expr.size]⟩
  obtain ⟨st5, c5, h5, h5_copy, h5_fr, h5_pos, h5_regs, hc5⟩ :=
    copyMemLoop_runs (w := w) (p := p) (ω := ω) rGAddr rCurG rTmp1 rTmp2 (by decide)
      gAddr L.g0Addr (2 + 2 * G.m) st4
      (by simp [st4, st3, st2, st1, Function.update_of_ne, hregs.1])
      (by simp [st4, st3, st2, st1, Function.update_of_ne, hregs.2.2.2.2.2.2.2.2.2.1])
      (by simp [st4, Function.update_self])
      (by omega) h2m2_w (by omega) (by omega) (Or.inl (by omega))
  obtain ⟨st6, c6, h6, h6_iota, h6_fr, h6_pos, h6_regs, hc6⟩ :=
    iotaRangeLoop_runs (w := w) (p := p) (ω := ω) rCurIdx rM rTmp2 (by decide)
      L.idx0Addr G.m st5
      (by rw [h5_regs _ (by decide)]; simp [st4, st3, st2, st1, Function.update_of_ne, hregs.2.2.2.2.2.2.2.2.2.2.1])
      (by rw [h5_regs _ (by decide)]; simp [st4, st3, st2, st1, Function.update_of_ne, hregs.2.2.2.1])
      (by omega) (by omega) (by omega)
  have hfull := runs_seq h1 (runs_seq h2 (runs_seq h3 (runs_seq h4 (runs_seq h5 h6))))
  have him_eq :
      initMemoryStmt =
        .seq (.store (.reg rStatePtr) (.reg rArena))
          (.seq (.store (.bin .add (.reg rStatePtr) (.const 1)) (.reg rZC))
            (.seq (.store (.bin .add (.reg rStatePtr) (.const 2)) (.const 0))
              (.seq (.assign rTmp1 (.bin .add (.const 2) (.bin .mul (.const 2) (.reg rM))))
                (.seq (copyMemLoop rGAddr rCurG rTmp1 rTmp2)
                  (iotaRangeLoop rCurIdx rM rTmp2))))) := rfl
  rw [← him_eq] at hfull
  refine ⟨st6, _, hfull, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine decompRegs_of_eq (fun r hr => ?_) hregs
    rw [h6_regs r (by simp [rTmp2]; omega), h5_regs r (by simp [rTmp2]; omega)]
    dsimp [st4, st3, st2, st1]
    rw [Function.update_of_ne (by simp [rTmp1]; omega)]
  · rw [h6_fr _ (by omega), h5_fr _ (by omega)]
    dsimp [st4, st3, st2, st1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
  · rw [h6_fr _ (by omega), h5_fr _ (by omega)]
    dsimp [st4, st3, st2]
    rw [Function.update_of_ne (by omega), Function.update_self]
  · rw [h6_fr _ (by omega), h5_fr _ (by omega)]
    dsimp [st4, st3]
    rw [Function.update_self]
  · intro i hi
    rw [← henc_len] at h5_copy
    rw [h6_fr _ (by omega), h5_copy i hi]
    have hgi : st4.mem (gAddr + i) = st₀.mem (gAddr + i) := by
      dsimp [st4, st3, st2, st1]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    rw [hgi]
    exact hga i hi
  · intro i hi
    simp only [List.length_range] at hi
    rw [List.getElem_range]
    exact h6_iota i hi
  · intro a ha
    rw [h6_fr _ (by omega), h5_fr _ (by omega)]
    dsimp [st4, st3, st2, st1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · intro a ha1 ha2
    rw [h6_fr _ (by omega), h5_fr _ (by omega)]
    dsimp [st4, st3, st2, st1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · intro a ha
    rw [h6_fr _ (by omega), h5_fr _ (by omega)]
    dsimp [st4, st3, st2, st1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · rw [h6_pos, h5_pos]
  · omega


end

end MinCostFlow.Expander
