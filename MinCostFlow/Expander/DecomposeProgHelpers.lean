/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MinCostFlow.Expander.DecomposeProgRegs
public import MinCostFlow.Expander.DecomposeProgSetup

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Helper Word RAM Subroutines for `DecomposeProg`

Reusable helper `Stmt`s and their `Runs` / `Triple` specifications:
* `copyMemLoop` — disjoint memory range copy (`forRange`),
* `zeroRangeLoop` — zero-fill `[dst, dst + len)` (used by the `m ≤ n` fast path),
* `iotaRangeLoop` — fill `dst[j] = j` (`0 ≤ j < m`, initial edge indices),
* `sparseFastPathStmt` — exact `O(m + 1)` fast path when `m ≤ n`,
* `computeEllStmt` — `ℓ = Nat.log 2 (m / n) + 1`,
* `computeLayoutStmt` — computes all `DecompLayout` addresses and initial `ℓ, 2^ℓ` registers,
* `initMemoryStmt` — initializes `statePtr[0..2]`, `g0`, `idx0`,
* `packOutputStmt` — writes header, copies `lvlArr`, and appends ascending arena slices into `[h, ...)`.
-/

namespace MinCostFlow.Expander

open MinCostFlow.Cited MinCostFlow.Spanner WordRAM

public section


/-! ## 5. Ascending Output Packing (`packOutputStmt`) -/

@[expose] def packSlicesLoop : Stmt :=
  forRange rTmp1 (.const 0) (.reg rEll)
    (seqStmts
      [ .assign rTmp3 (.load (.bin .add (.reg rBounds) (.bin .mul (.const 2) (.bin .add (.reg rTmp1) (.const 1)))))
      , .assign rTmp4 (.load (.bin .add (.reg rBounds) (.bin .add (.bin .mul (.const 2) (.bin .add (.reg rTmp1) (.const 1))) (.const 1))))
      , .assign rRet (.bin .sub (.reg rTmp4) (.reg rTmp3))
      , copyMemLoop rTmp3 rTmp2 rRet rTmp5
      , .assign rTmp2 (.bin .add (.reg rTmp2) (.reg rRet)) ])

lemma packSlicesLoop_noRand : packSlicesLoop.NoRand := by
  apply forRange_noRand
  simp [Stmt.NoRand, copyMemLoop_noRand]

@[expose] def packOutputStmt : Stmt :=
  seqStmts
    [ .store (.reg rOutH) (.reg rEll)
    , .store (.bin .add (.reg rOutH) (.const 1)) (.const 1)
    , .store (.bin .add (.reg rOutH) (.const 2)) (.bin .mul (.const 3) (.reg rDphi))
    , .assign rTmp1 (.bin .add (.reg rOutH) (.const 3))
    , copyMemLoop rLvlArr rTmp1 rM rTmp2
    , .store (.bin .add (.reg rOutH) (.bin .add (.const 3) (.reg rM)))
        (.load (.bin .add (.reg rStatePtr) (.const 2)))
    , .assign rTmp2 (.bin .add (.reg rOutH) (.bin .add (.const 4) (.reg rM)))
    , packSlicesLoop
    , .ret (.load (.bin .add (.reg rStatePtr) (.const 1))) ]

lemma packOutputStmt_noRand : packOutputStmt.NoRand := by
  simp [packOutputStmt, seqStmts, Stmt.NoRand, copyMemLoop_noRand, packSlicesLoop_noRand]

private lemma flatten_map_flatMap (recs : List DecompLevelRec) :
    (recs.map fun r => r.rawComps.flatMap compRecord).flatten =
      (recs.map (·.rawComps)).flatten.flatMap compRecord := by
  induction recs with
  | nil => rfl
  | cons r rs ih => simp [List.flatMap_append, ih]

private lemma sum_Ico_rec_flatLen (recs : List DecompLevelRec) :
    (∑ q ∈ Finset.Ico 0 recs.length,
      if h : q < recs.length then 20 * (recs[q].rawComps.flatMap compRecord).length else 0) =
      20 * (recs.map fun r => r.rawComps.flatMap compRecord).flatten.length := by
  induction recs using List.reverseRecOn with
  | nil => simp
  | append_singleton rs r ih =>
    rw [show Finset.Ico 0 (rs ++ [r]).length = Finset.Ico 0 (rs.length + 1) from by simp]
    rw [Finset.sum_Ico_succ_top (Nat.zero_le _)]
    have hleft : (∑ q ∈ Finset.Ico 0 rs.length,
        if h : q < (rs ++ [r]).length then 20 * ((rs ++ [r])[q].rawComps.flatMap compRecord).length else 0) =
        ∑ q ∈ Finset.Ico 0 rs.length,
          if h : q < rs.length then 20 * (rs[q].rawComps.flatMap compRecord).length else 0 := by
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [Finset.mem_Ico] at hq
      have hlt : q < rs.length := hq.2
      have hlt2 : q < (rs ++ [r]).length := by simp; omega
      simp only [hlt, hlt2, ↓reduceDIte, List.getElem_append_left]
    have htop : rs.length < (rs ++ [r]).length := by simp
    rw [hleft, ih]
    simp only [htop, ↓reduceDIte, List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_singleton]
    simp [List.map_append, List.flatten_append, Nat.mul_add]

lemma packOutput_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (gAddr h n m ℓ D_phi curGAddr curIdxAddr nextGAddr nextIdxAddr zeroCursorFinal : ℕ)
    (recs : List DecompLevelRec) (level : List ℕ) (st₀ : State)
    (h1n : 1 ≤ n) (hnm : n < m) (hℓ_le : ℓ ≤ m + 2)
    (hlen : recs.length = ℓ)
    (hlvl_len : level.length = m)
    (hlvl_at : ListAt st₀.mem (mkDecompLayout h n m D_phi).lvlArrAddr level)
    (htotal : st₀.mem ((mkDecompLayout h n m D_phi).statePtr + 2) =
      ((recs.map (·.rawComps)).flatten).length)
    (hzc : st₀.mem ((mkDecompLayout h n m D_phi).statePtr + 1) = zeroCursorFinal)
    (harena_le : (mkDecompLayout h n m D_phi).zeroCursor₀ ≤ zeroCursorFinal)
    (hbounds : ∀ (t : ℕ) (ht : t < recs.length),
      let a0 := st₀.mem ((mkDecompLayout h n m D_phi).boundsAddr + 2 * (t + 1))
      let a1 := st₀.mem ((mkDecompLayout h n m D_phi).boundsAddr + 2 * (t + 1) + 1)
      (mkDecompLayout h n m D_phi).arena₀ ≤ a0 ∧ a0 ≤ a1 ∧
      a1 ≤ (mkDecompLayout h n m D_phi).arena₀ + 4 * m ∧
      a1 - a0 = (recs[t].rawComps.flatMap compRecord).length ∧
      ListAt st₀.mem a0 (recs[t].rawComps.flatMap compRecord))
    (henc_len : (Decompose.encode ℓ 1 (3 * D_phi) level ((recs.map (·.rawComps)).flatten)).length ≤ 4 + 5 * m)
    (hw4 : 4 < 2 ^ w) (hphi_w : 3 * D_phi < 2 ^ w)
    (hzc_w : zeroCursorFinal < 2 ^ w)
    (hregs : DecompRegs gAddr h n m ℓ D_phi 0 (2 ^ 0) curGAddr curIdxAddr nextGAddr nextIdxAddr
      (mkDecompLayout h n m D_phi) st₀) :
    let L := mkDecompLayout h n m D_phi
    ∃ st' c,
      Runs w p ω packOutputStmt st₀ (.returned zeroCursorFinal) st' c ∧
      DecomposeOutAt st'.mem h ℓ 1 (3 * D_phi) level ((recs.map (·.rawComps)).flatten) ∧
      (∀ a, a < h ∨ L.statePtr ≤ a → st'.mem a = st₀.mem a) ∧
      c ≤ 150 * m + 65 * ℓ + 120 := by
  dsimp only
  set L := mkDecompLayout h n m D_phi
  have hw0 : w ≠ 0 := by intro h0; subst h0; simp at hw4
  let rawComps := (recs.map (·.rawComps)).flatten
  have hflat_len : (rawComps.flatMap compRecord).length ≤ 4 * m := by
    have he : (Decompose.encode ℓ 1 (3 * D_phi) level rawComps).length =
        4 + level.length + (rawComps.flatMap compRecord).length := by
      simp [Decompose.encode, List.length_append]; omega
    change (Decompose.encode ℓ 1 (3 * D_phi) level rawComps).length ≤ 4 + 5 * m at henc_len
    omega
  have hL_w : L.zeroCursor₀ < 2 ^ w := by omega
  have hℓ_w : ℓ < 2 ^ w := by dsimp [L, mkDecompLayout] at hL_w; omega
  have hsp_lt : h + 4 + 5 * m = L.statePtr := rfl
  have hh_w : h < 2 ^ w := by dsimp [L, mkDecompLayout] at hL_w; omega
  have hh3m_w : h + (3 + m) < 2 ^ w := by dsimp [L, mkDecompLayout] at hL_w; omega
  have hh4m_w : h + (4 + m) < 2 ^ w := by dsimp [L, mkDecompLayout] at hL_w; omega
  let st1 : State := { st₀ with mem := Function.update st₀.mem h ℓ }
  have h1 : Runs w p ω (.store (.reg rOutH) (.reg rEll)) st₀ .normal st1 3 := by
    apply runs_store_iff.mpr
    refine ⟨h, ℓ, by simp [Expr.eval, hregs.2.1], by simp [Expr.eval, hregs.2.2.2.2.1],
      rfl, rfl, by simp [Expr.size]⟩
  let st2 : State := { st1 with mem := Function.update st1.mem (h + 1) 1 }
  have h2 : Runs w p ω (.store (.bin .add (.reg rOutH) (.const 1)) (.const 1)) st1 .normal st2 5 := by
    apply runs_store_iff.mpr
    refine ⟨h + 1, 1, by simp [Expr.eval, BinOp.eval, st1, hregs.2.1, hw0, show h + 1 < 2 ^ w by omega],
      by simp [Expr.eval, hw0], rfl, rfl, by simp [Expr.size]⟩
  let st3 : State := { st2 with mem := Function.update st2.mem (h + 2) (3 * D_phi) }
  have h3 : Runs w p ω (.store (.bin .add (.reg rOutH) (.const 2)) (.bin .mul (.const 3) (.reg rDphi)))
      st2 .normal st3 7 := by
    apply runs_store_iff.mpr
    refine ⟨h + 2, 3 * D_phi,
      by simp [Expr.eval, BinOp.eval, st2, st1, hregs.2.1, show 2 < 2 ^ w by omega, show h + 2 < 2 ^ w by omega],
      by simp [Expr.eval, BinOp.eval, st2, st1, hregs.2.2.2.2.2.1, show 3 < 2 ^ w by omega, hphi_w],
      rfl, rfl, by simp [Expr.size]⟩
  let st4 : State := { st3 with regs := Function.update st3.regs rTmp1 (h + 3) }
  have h4 : Runs w p ω (.assign rTmp1 (.bin .add (.reg rOutH) (.const 3))) st3 .normal st4 4 := by
    apply runs_assign_iff.mpr
    refine ⟨h + 3, by simp [Expr.eval, BinOp.eval, st3, st2, st1, hregs.2.1, show 3 < 2 ^ w by omega,
      show h + 3 < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
  have hdisj_lvl : L.lvlArrAddr + m ≤ h + 3 ∨ h + 3 + m ≤ L.lvlArrAddr := Or.inr (by
    dsimp [L, mkDecompLayout]; omega)
  obtain ⟨st5, c5, h5, h5_copy, h5_fr, h5_pos, h5_regs, hc5⟩ :=
    copyMemLoop_runs (w := w) (p := p) (ω := ω) rLvlArr rTmp1 rM rTmp2 (by decide)
      L.lvlArrAddr (h + 3) m st4
      (by simp [st4, st3, st2, st1, Function.update_of_ne, hregs.2.2.2.2.2.2.2.2.1])
      (by simp [st4, Function.update_self])
      (by simp [st4, st3, st2, st1, Function.update_of_ne, hregs.2.2.2.1])
      (by omega) (by omega) (by dsimp [L, mkDecompLayout] at hL_w ⊢; omega) (by omega) hdisj_lvl
  have hst5_state : st5.mem (L.statePtr + 2) = rawComps.length := by
    rw [h5_fr _ (by omega)]
    dsimp [st4, st3, st2, st1]
    rw [Function.update_of_ne (by dsimp [L, mkDecompLayout]; omega),
      Function.update_of_ne (by dsimp [L, mkDecompLayout]; omega),
      Function.update_of_ne (by dsimp [L, mkDecompLayout]; omega)]
    exact htotal
  have h5_rH : st5.regs rOutH = h := by rw [h5_regs _ (by decide)]; simp [st4, st3, st2, st1, Function.update_of_ne, hregs.2.1]
  have h5_rM : st5.regs rM = m := by rw [h5_regs _ (by decide)]; simp [st4, st3, st2, st1, Function.update_of_ne, hregs.2.2.2.1]
  have h5_rSP : st5.regs rStatePtr = L.statePtr := by
    rw [h5_regs _ (by decide)]; simp [st4, st3, st2, st1, Function.update_of_ne, hregs.2.2.2.2.2.2.1]
  have hrc_len_le : rawComps.length ≤ (rawComps.flatMap compRecord).length := by
    clear h1 h2 h3 h4 h5 h5_copy h5_fr h5_pos h5_regs hc5 hst5_state hflat_len henc_len hbounds htotal
    induction rawComps with
    | nil => simp
    | cons c cs ih => simp [compRecord]; omega
  have htotal_w : rawComps.length < 2 ^ w := by
    dsimp [L, mkDecompLayout] at hL_w; omega
  let st6 : State := { st5 with mem := Function.update st5.mem (h + (3 + m)) rawComps.length }
  have h6 : Runs w p ω
      (.store (.bin .add (.reg rOutH) (.bin .add (.const 3) (.reg rM)))
        (.load (.bin .add (.reg rStatePtr) (.const 2))))
      st5 .normal st6 10 := by
    apply runs_store_iff.mpr
    refine ⟨h + (3 + m), rawComps.length,
      by simp [Expr.eval, BinOp.eval, h5_rH, h5_rM, show 3 < 2 ^ w by omega, show 3 + m < 2 ^ w by omega, hh3m_w],
      by simp [Expr.eval, BinOp.eval, h5_rSP, show 2 < 2 ^ w by omega,
        show L.statePtr + 2 < 2 ^ w by dsimp [L, mkDecompLayout] at hL_w; omega, hst5_state],
      rfl, rfl, by simp [Expr.size]⟩
  let st7 : State := { st6 with regs := Function.update st6.regs rTmp2 (h + (4 + m)) }
  have h7 : Runs w p ω (.assign rTmp2 (.bin .add (.reg rOutH) (.bin .add (.const 4) (.reg rM))))
      st6 .normal st7 6 := by
    apply runs_assign_iff.mpr
    refine ⟨h + (4 + m),
      ev_add (ev_reg (by dsimp [st6]; exact h5_rH))
        (ev_add (ev_const hw4) (ev_reg (by dsimp [st6]; exact h5_rM)) (by omega))
        hh4m_w,
      rfl, rfl, by simp [Expr.size]⟩
  have hrec_flat_eq : (recs.map fun r => r.rawComps.flatMap compRecord).flatten =
      rawComps.flatMap compRecord := flatten_map_flatMap recs
  -- Run `packSlicesLoop` for `t = 0 .. ℓ - 1`
  let prefixFlat : ℕ → List ℕ := fun t => ((recs.take t).map fun r => r.rawComps.flatMap compRecord).flatten
  have hprefix_len : ∀ t ≤ ℓ, (prefixFlat t).length ≤ (rawComps.flatMap compRecord).length := by
    intro t _ht
    have h1 : (prefixFlat t).length + ((recs.drop t).map fun r => r.rawComps.flatMap compRecord).flatten.length =
        (rawComps.flatMap compRecord).length := by
      dsimp [prefixFlat]
      have hd : recs.take t ++ recs.drop t = recs := List.take_append_drop t recs
      calc ((recs.take t).map fun r => r.rawComps.flatMap compRecord).flatten.length +
            ((recs.drop t).map fun r => r.rawComps.flatMap compRecord).flatten.length
          = (((recs.take t ++ recs.drop t).map fun r => r.rawComps.flatMap compRecord).flatten).length := by
            simp only [List.map_append, List.flatten_append, List.length_append]
        _ = (recs.map fun r => r.rawComps.flatMap compRecord).flatten.length := by rw [hd]
        _ = (rawComps.flatMap compRecord).length := congrArg List.length hrec_flat_eq
    omega
  let Inv : ℕ → State → Prop := fun t st =>
    st.regs rTmp1 = t ∧ st.regs rBounds = L.boundsAddr ∧ st.regs rEll = ℓ ∧
    st.regs rStatePtr = L.statePtr ∧ st.regs rTmp2 = h + 4 + m + (prefixFlat t).length ∧
    st.pos = st₀.pos ∧
    ListAt st.mem (h + 4 + m) (prefixFlat t) ∧
    (∀ a, a < h + 4 + m ∨ h + 4 + m + (prefixFlat t).length ≤ a → st.mem a = st7.mem a)
  let hstep_cost : ℕ → ℕ := fun t => if _h : t < recs.length then 20 * (recs[t].rawComps.flatMap compRecord).length + 45 else 0
  have hpack := forRange_varCost (w := w) (p := p) (ω := ω) rTmp1 (.const 0) (.reg rEll)
    (seqStmts
      [ .assign rTmp3 (.load (.bin .add (.reg rBounds) (.bin .mul (.const 2) (.bin .add (.reg rTmp1) (.const 1)))))
      , .assign rTmp4 (.load (.bin .add (.reg rBounds) (.bin .add (.bin .mul (.const 2) (.bin .add (.reg rTmp1) (.const 1))) (.const 1))))
      , .assign rRet (.bin .sub (.reg rTmp4) (.reg rTmp3))
      , copyMemLoop rTmp3 rTmp2 rRet rTmp5
      , .assign rTmp2 (.bin .add (.reg rTmp2) (.reg rRet)) ])
    Inv hstep_cost 0 ℓ (Nat.zero_le ℓ) (by omega) hℓ_w
    (fun t st _ _ hi => hi.1)
    (fun t st _ _ hi => by simp [Expr.eval, hi.2.2.1])
    (fun t st _ ht hi => by
      have ht_len : t < recs.length := by omega
      have hb := hbounds t ht_len
      dsimp only at hb
      set a0 := st₀.mem (L.boundsAddr + 2 * (t + 1))
      set a1 := st₀.mem (L.boundsAddr + 2 * (t + 1) + 1)
      have ha_bnd_ge : h + 4 + m + (prefixFlat t).length ≤ L.boundsAddr := by
        have hp := hprefix_len t (by omega)
        dsimp [L, mkDecompLayout] at *; omega
      have hst_bnd0 : st.mem (L.boundsAddr + 2 * (t + 1)) = a0 := by
        rw [hi.2.2.2.2.2.2.2 _ (Or.inr (by omega))]
        dsimp [st7, st6]
        rw [Function.update_of_ne (by dsimp [L, mkDecompLayout]; omega)]
        rw [h5_fr _ (by dsimp [L, mkDecompLayout]; omega)]
        dsimp [st4, st3, st2, st1]
        rw [Function.update_of_ne (by dsimp [L, mkDecompLayout]; omega),
          Function.update_of_ne (by dsimp [L, mkDecompLayout]; omega),
          Function.update_of_ne (by dsimp [L, mkDecompLayout]; omega)]
      have hst_bnd1 : st.mem (L.boundsAddr + 2 * (t + 1) + 1) = a1 := by
        rw [hi.2.2.2.2.2.2.2 _ (Or.inr (by omega))]
        dsimp [st7, st6]
        rw [Function.update_of_ne (by dsimp [L, mkDecompLayout]; omega)]
        rw [h5_fr _ (by dsimp [L, mkDecompLayout]; omega)]
        dsimp [st4, st3, st2, st1]
        rw [Function.update_of_ne (by dsimp [L, mkDecompLayout]; omega),
          Function.update_of_ne (by dsimp [L, mkDecompLayout]; omega),
          Function.update_of_ne (by dsimp [L, mkDecompLayout]; omega)]
      have ha0_w : a0 < 2 ^ w := by dsimp [L, mkDecompLayout] at hL_w hb; omega
      have ha1_w : a1 < 2 ^ w := by dsimp [L, mkDecompLayout] at hL_w hb; omega
      have h2t1_w : 2 * (t + 1) + 1 < 2 ^ w := by dsimp [L, mkDecompLayout] at hL_w; omega
      have hbnd0_w : L.boundsAddr + 2 * (t + 1) < 2 ^ w := by
        dsimp [L, mkDecompLayout] at hL_w ⊢; omega
      have hbnd1_w : L.boundsAddr + (2 * (t + 1) + 1) < 2 ^ w := by
        dsimp [L, mkDecompLayout] at hL_w ⊢; omega
      let stA : State := { st with regs := Function.update st.regs rTmp3 a0 }
      have hA : Runs w p ω
          (.assign rTmp3 (.load (.bin .add (.reg rBounds) (.bin .mul (.const 2) (.bin .add (.reg rTmp1) (.const 1))))))
          st .normal stA 9 := by
        apply runs_assign_iff.mpr
        refine ⟨a0,
          ev_load
            (ev_add (ev_reg hi.2.1)
              (ev_mul (ev_const (by omega))
                (ev_add (ev_reg hi.1) (ev_const (by omega)) (by omega)) (by omega))
              hbnd0_w)
            hst_bnd0,
          rfl, rfl, by simp [Expr.size]⟩
      let stB : State := { stA with regs := Function.update stA.regs rTmp4 a1 }
      have hAst_bnd : stA.regs rBounds = L.boundsAddr := by
        dsimp [stA]; rw [Function.update_of_ne (by decide), hi.2.1]
      have hAst_t1 : stA.regs rTmp1 = t := by
        dsimp [stA]; rw [Function.update_of_ne (by decide), hi.1]
      have hB : Runs w p ω
          (.assign rTmp4 (.load (.bin .add (.reg rBounds) (.bin .add (.bin .mul (.const 2) (.bin .add (.reg rTmp1) (.const 1))) (.const 1)))))
          stA .normal stB 11 := by
        apply runs_assign_iff.mpr
        refine ⟨a1,
          ev_load
            (ev_add (ev_reg hAst_bnd)
              (ev_add
                (ev_mul (ev_const (by omega))
                  (ev_add (ev_reg hAst_t1) (ev_const (by omega)) (by omega)) (by omega))
                (ev_const (by omega)) h2t1_w)
              hbnd1_w)
            (by rw [show L.boundsAddr + (2 * (t + 1) + 1) = L.boundsAddr + 2 * (t + 1) + 1 by omega]; exact hst_bnd1),
          rfl, rfl, by simp [Expr.size]⟩
      let slen := a1 - a0
      have hslen_w : slen < 2 ^ w := by omega
      let stC : State := { stB with regs := Function.update stB.regs rRet slen }
      have hBt3 : stB.regs rTmp3 = a0 := by dsimp [stB, stA]; rw [Function.update_of_ne (by decide), Function.update_self]
      have hBt4 : stB.regs rTmp4 = a1 := by simp [stB]
      have hC : Runs w p ω (.assign rRet (.bin .sub (.reg rTmp4) (.reg rTmp3))) stB .normal stC 4 := by
        apply runs_assign_iff.mpr
        refine ⟨slen, ev_sub (ev_reg hBt4) (ev_reg hBt3) hslen_w, rfl, rfl, by simp [Expr.size]⟩
      let wp := h + 4 + m + (prefixFlat t).length
      have htake : recs.take (t + 1) = recs.take t ++ [recs[t]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem ht_len]; rfl
      have hpf_succ : prefixFlat (t + 1) = prefixFlat t ++ recs[t].rawComps.flatMap compRecord := by
        dsimp [prefixFlat]; rw [htake]; simp only [List.map_append, List.map_cons, List.map_nil,
          List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
      have hwp_le_st : wp + slen ≤ L.statePtr := by
        have hsum_le : (prefixFlat (t + 1)).length ≤ (rawComps.flatMap compRecord).length :=
          hprefix_len (t + 1) (by omega)
        have hpf_len : (prefixFlat (t + 1)).length =
            (prefixFlat t).length + (recs[t].rawComps.flatMap compRecord).length := by
          rw [hpf_succ, List.length_append]
        dsimp [wp, slen]
        omega
      have hdisj_slice : a0 + slen ≤ wp ∨ wp + slen ≤ a0 := Or.inr (by
        dsimp [L, mkDecompLayout] at hwp_le_st hb; omega)
      obtain ⟨stD, cD, hD, hD_copy, hD_fr, hD_pos, hD_regs, hcD⟩ :=
        copyMemLoop_runs (w := w) (p := p) (ω := ω) rTmp3 rTmp2 rRet rTmp5 (by decide)
          a0 wp slen stC
          (by simp [stC, stB, stA, Function.update_of_ne, Function.update_self])
          (by simp [stC, stB, stA, Function.update_of_ne, hi.2.2.2.2.1]; rfl)
          (by simp [stC, Function.update_self])
          (by omega) hslen_w (by omega) (by dsimp [L, mkDecompLayout] at hL_w hwp_le_st; omega) hdisj_slice
      let stE : State := { stD with regs := Function.update stD.regs rTmp2 (wp + slen) }
      have hDt2 : stD.regs rTmp2 = wp := by
        rw [hD_regs rTmp2 (by decide)]; simp [stC, stB, stA, Function.update_of_ne, hi.2.2.2.2.1]; rfl
      have hDret : stD.regs rRet = slen := by rw [hD_regs rRet (by decide)]; simp [stC]
      have hE : Runs w p ω (.assign rTmp2 (.bin .add (.reg rTmp2) (.reg rRet))) stD .normal stE 4 := by
        apply runs_assign_iff.mpr
        refine ⟨wp + slen,
          ev_add (ev_reg hDt2) (ev_reg hDret)
            (by dsimp [wp] at *; dsimp [L, mkDecompLayout] at hL_w hwp_le_st; omega),
          rfl, rfl, by simp [Expr.size]⟩
      have hstep_full := runs_seq hA (runs_seq hB (runs_seq hC (runs_seq hD hE)))
      change Runs w p ω
        (seqStmts
          [ .assign rTmp3 (.load (.bin .add (.reg rBounds) (.bin .mul (.const 2) (.bin .add (.reg rTmp1) (.const 1)))))
          , .assign rTmp4 (.load (.bin .add (.reg rBounds) (.bin .add (.bin .mul (.const 2) (.bin .add (.reg rTmp1) (.const 1))) (.const 1))))
          , .assign rRet (.bin .sub (.reg rTmp4) (.reg rTmp3))
          , copyMemLoop rTmp3 rTmp2 rRet rTmp5
          , .assign rTmp2 (.bin .add (.reg rTmp2) (.reg rRet)) ])
        st .normal stE _ at hstep_full
      have hlist_succ : ListAt stE.mem (h + 4 + m) (prefixFlat (t + 1)) := by
        intro idx hidx
        rw [hpf_succ, List.length_append] at hidx
        by_cases hlt : idx < (prefixFlat t).length
        · have he : (prefixFlat (t + 1))[idx]'(by rw [hpf_succ, List.length_append]; exact hidx) =
              (prefixFlat t)[idx]'hlt := by
            simp only [hpf_succ]; exact List.getElem_append_left hlt
          rw [he, show stE.mem (h + 4 + m + idx) = st.mem (h + 4 + m + idx) from
            hD_fr _ (Or.inl (by omega))]
          exact hi.2.2.2.2.2.2.1 idx hlt
        · have hge : (prefixFlat t).length ≤ idx := Nat.le_of_not_lt hlt
          have hsub : idx - (prefixFlat t).length < (recs[t].rawComps.flatMap compRecord).length := by omega
          have he : (prefixFlat (t + 1))[idx]'(by rw [hpf_succ, List.length_append]; exact hidx) =
              (recs[t].rawComps.flatMap compRecord)[idx - (prefixFlat t).length]'hsub := by
            simp only [hpf_succ]; exact List.getElem_append_right hge
          have hcopy := hD_copy (idx - (prefixFlat t).length) (by omega)
          have hst_mem : stC.mem (a0 + (idx - (prefixFlat t).length)) =
              st₀.mem (a0 + (idx - (prefixFlat t).length)) := by
            have hp := hprefix_len t (by omega)
            dsimp [stC, stB, stA]
            rw [hi.2.2.2.2.2.2.2 _ (Or.inr (by dsimp [L, mkDecompLayout] at hb ⊢; omega))]
            dsimp [st7, st6]
            rw [Function.update_of_ne (by dsimp [L, mkDecompLayout] at hb; omega)]
            rw [h5_fr _ (by dsimp [L, mkDecompLayout] at hb; omega)]
            dsimp [st4, st3, st2, st1]
            rw [Function.update_of_ne (by dsimp [L, mkDecompLayout] at hb; omega),
              Function.update_of_ne (by dsimp [L, mkDecompLayout] at hb; omega),
              Function.update_of_ne (by dsimp [L, mkDecompLayout] at hb; omega)]
          rw [he, show h + 4 + m + idx = wp + (idx - (prefixFlat t).length) by omega]
          dsimp [stE]
          rw [hcopy, hst_mem]
          exact hb.2.2.2.2 (idx - (prefixFlat t).length) hsub
      refine ⟨stE, _, hstep_full, ?_, ?_, ?_⟩
      · have hsc : hstep_cost t = 20 * (recs[t].rawComps.flatMap compRecord).length + 45 := by
          simp [hstep_cost, ht_len]
        omega
      · dsimp [stE]; rw [Function.update_of_ne (by decide), hD_regs rTmp1 (by decide)]
        simp [stC, stB, stA, Function.update_of_ne, hi.1]
      · refine ⟨by dsimp only; exact Function.update_self _ _ _, ?_, ?_, ?_, ?_, ?_, hlist_succ, ?_⟩
        · dsimp only [stE]; rw [Function.update_of_ne (by decide : rBounds ≠ rTmp1),
            Function.update_of_ne (by decide : rBounds ≠ rTmp2), hD_regs rBounds (by decide)]
          simp [stC, stB, stA, Function.update_of_ne, hi.2.1]
        · dsimp only [stE]; rw [Function.update_of_ne (by decide : rEll ≠ rTmp1),
            Function.update_of_ne (by decide : rEll ≠ rTmp2), hD_regs rEll (by decide)]
          simp [stC, stB, stA, Function.update_of_ne, hi.2.2.1]
        · dsimp only [stE]; rw [Function.update_of_ne (by decide : rStatePtr ≠ rTmp1),
            Function.update_of_ne (by decide : rStatePtr ≠ rTmp2), hD_regs rStatePtr (by decide)]
          simp [stC, stB, stA, Function.update_of_ne, hi.2.2.2.1]
        · dsimp only [stE]; rw [Function.update_of_ne (by decide : rTmp2 ≠ rTmp1),
            Function.update_self, hpf_succ, List.length_append]
          dsimp [wp, slen]; omega
        · dsimp only [stE]; rw [hD_pos]; exact hi.2.2.2.2.2.1
        · intro a ha
          have ha_wp : a < wp ∨ wp + slen ≤ a := by
            rw [hpf_succ, List.length_append] at ha
            dsimp [wp, slen]; omega
          dsimp [stE]
          rw [hD_fr a ha_wp]
          have hlen_le : (prefixFlat t).length ≤ (prefixFlat (t + 1)).length := by
            rw [hpf_succ, List.length_append]; omega
          exact hi.2.2.2.2.2.2.2 a (by rcases ha with ha | ha <;> [exact Or.inl ha; exact Or.inr (by omega)])
      )
    st7 (by simp [Expr.eval])
    ⟨by simp,
      by dsimp only; rw [Function.update_of_ne (by decide)]; dsimp [st7, st6]; rw [Function.update_of_ne (by decide), h5_regs rBounds (by decide)]; simp [st4, st3, st2, st1, Function.update_of_ne, hregs.2.2.2.2.2.2.2.1],
      by dsimp only; rw [Function.update_of_ne (by decide)]; dsimp [st7, st6]; rw [Function.update_of_ne (by decide), h5_regs rEll (by decide)]; simp [st4, st3, st2, st1, Function.update_of_ne, hregs.2.2.2.2.1],
      by dsimp only; rw [Function.update_of_ne (by decide)]; dsimp [st7, st6]; rw [Function.update_of_ne (by decide), h5_rSP],
      by dsimp only; rw [Function.update_of_ne (by decide)]; simp [st7, Function.update_self, prefixFlat]; omega,
      by dsimp [st7, st6]; rw [h5_pos],
      fun idx hidx => by simp [prefixFlat] at hidx,
      fun _ _ => rfl⟩
  rcases hpack with ⟨st8, c8, h8, hinv8, hc8⟩
  have hst8_zc : st8.mem (L.statePtr + 1) = zeroCursorFinal := by
    rw [hinv8.2.2.2.2.2.2.2 _ (Or.inr (by
      have hp := hprefix_len ℓ (le_refl ℓ)
      dsimp [L, mkDecompLayout] at *; omega))]
    dsimp [st7, st6]
    rw [Function.update_of_ne (by dsimp [L, mkDecompLayout]; omega)]
    rw [h5_fr _ (by dsimp [L, mkDecompLayout]; omega)]
    dsimp [st4, st3, st2, st1]
    rw [Function.update_of_ne (by dsimp [L, mkDecompLayout]; omega),
      Function.update_of_ne (by dsimp [L, mkDecompLayout]; omega),
      Function.update_of_ne (by dsimp [L, mkDecompLayout]; omega)]
    exact hzc
  have h9 : Runs w p ω (.ret (.load (.bin .add (.reg rStatePtr) (.const 1))))
      st8 (.returned zeroCursorFinal) st8 5 := by
    apply runs_ret_iff.mpr
    refine ⟨zeroCursorFinal,
      ev_load (ev_add (ev_reg hinv8.2.2.2.1) (ev_const (by omega))
        (by dsimp [L, mkDecompLayout] at hsp_lt hL_w ⊢; omega)) hst8_zc,
      rfl, rfl, by simp [Expr.size]⟩
  have hfull := runs_seq h1 (runs_seq h2 (runs_seq h3 (runs_seq h4
    (runs_seq h5 (runs_seq h6 (runs_seq h7 (runs_seq h8 h9)))))))
  change Runs w p ω packOutputStmt st₀ (.returned zeroCursorFinal) st8 _ at hfull
  refine ⟨st8, _, hfull, ?_, ?_, ?_⟩
  · have hpf_all : prefixFlat ℓ = rawComps.flatMap compRecord := by
      dsimp [prefixFlat]
      rw [← hlen, List.take_length, hrec_flat_eq]
    intro i hi
    have hfront : ([ℓ, 1, 3 * D_phi] ++ level ++ [rawComps.length]).length = 4 + m := by
      simp [hlvl_len]; omega
    by_cases hlt : i < 4 + m
    · have ha : st8.mem (h + i) = st7.mem (h + i) := hinv8.2.2.2.2.2.2.2 (h + i) (Or.inl (by omega))
      rw [ha]
      simp only [Decompose.encode] at hi ⊢
      have hi' : i < (([ℓ, 1, 3 * D_phi] ++ level ++ [rawComps.length]) ++ rawComps.flatMap compRecord).length := by
        simpa [rawComps, List.append_assoc] using hi
      have helem : (([ℓ, 1, 3 * D_phi] ++ level ++ [rawComps.length]) ++ rawComps.flatMap compRecord)[i]'hi' =
          ([ℓ, 1, 3 * D_phi] ++ level ++ [rawComps.length])[i]'(by rw [hfront]; exact hlt) :=
        List.getElem_append_left (by rw [hfront]; exact hlt)
      change st7.mem (h + i) = (([ℓ, 1, 3 * D_phi] ++ level ++ [rawComps.length]) ++ rawComps.flatMap compRecord)[i]'hi'
      rw [helem]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ (3 ≤ i ∧ i < 3 + m) ∨ i = 3 + m by omega) with
        rfl | rfl | rfl | ⟨hi3, him⟩ | rfl
      · dsimp only [st7, st6]
        rw [Nat.add_zero, Function.update_of_ne (by omega : h ≠ h + (3 + m)), h5_fr _ (by omega)]
        dsimp only [st4, st3, st2, st1]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
        rfl
      · dsimp only [st7, st6]
        rw [Function.update_of_ne (by omega : h + 1 ≠ h + (3 + m)), h5_fr _ (by omega)]
        dsimp only [st4, st3, st2]
        rw [Function.update_of_ne (by omega), Function.update_self]
        rfl
      · dsimp only [st7, st6]
        rw [Function.update_of_ne (by omega : h + 2 ≠ h + (3 + m)), h5_fr _ (by omega)]
        dsimp only [st4, st3]
        rw [Function.update_self]
        rfl
      · have hmem : st5.mem (h + i) = level[i - 3]'(by rw [hlvl_len]; omega) := by
          rw [show h + i = (h + 3) + (i - 3) by omega, h5_copy (i - 3) (by omega)]
          have hlvl_st4 : st4.mem (L.lvlArrAddr + (i - 3)) = st₀.mem (L.lvlArrAddr + (i - 3)) := by
            dsimp [st4, st3, st2, st1]
            rw [Function.update_of_ne (by dsimp [L, mkDecompLayout]; omega),
              Function.update_of_ne (by dsimp [L, mkDecompLayout]; omega),
              Function.update_of_ne (by dsimp [L, mkDecompLayout]; omega)]
          rw [hlvl_st4]
          exact hlvl_at (i - 3) (by rw [hlvl_len]; omega)
        dsimp [st7, st6]
        rw [Function.update_of_ne (by omega : h + i ≠ h + (3 + m)), hmem]
        rcases i with _ | _ | _ | k
        · omega
        · omega
        · omega
        · change level[k]'(by rw [hlvl_len]; omega) =
              (level ++ [rawComps.length])[k]'(by simp [hlvl_len]; omega)
          exact (List.getElem_append_left (by rw [hlvl_len]; omega)).symm
      · dsimp [st7, st6]
        rw [Function.update_self]
        have hm3 : (ℓ :: 1 :: 3 * D_phi :: (level ++ [rawComps.length]))[3 + m]'(by simp [hlvl_len]; omega) =
            rawComps.length := by
          change ([ℓ, 1, 3 * D_phi] ++ level ++ [rawComps.length])[3 + m]'(by simp [hlvl_len]; omega) =
            rawComps.length
          rw [List.getElem_append_right (by simp [hlvl_len]; omega)]
          simp [hlvl_len]
        exact hm3.symm
    · have hge : 4 + m ≤ i := Nat.le_of_not_lt hlt
      simp only [Decompose.encode] at hi ⊢
      have hi' : i < (([ℓ, 1, 3 * D_phi] ++ level ++ [rawComps.length]) ++ rawComps.flatMap compRecord).length := by
        simpa [rawComps, List.append_assoc] using hi
      have helem : (([ℓ, 1, 3 * D_phi] ++ level ++ [rawComps.length]) ++ rawComps.flatMap compRecord)[i]'hi' =
          (rawComps.flatMap compRecord)[i - (4 + m)]'(by rw [List.length_append, hfront] at hi'; omega) := by
        rw [List.getElem_append_right (by rw [hfront]; exact hge)]; simp only [hfront]
      change st8.mem (h + i) = (([ℓ, 1, 3 * D_phi] ++ level ++ [rawComps.length]) ++ rawComps.flatMap compRecord)[i]'hi'
      rw [helem, show h + i = h + 4 + m + (i - (4 + m)) by omega]
      have hi_pf : i - (4 + m) < (prefixFlat ℓ).length := by
        rw [hpf_all]; rw [List.length_append, hfront] at hi'; omega
      simpa [hpf_all] using hinv8.2.2.2.2.2.2.1 (i - (4 + m)) hi_pf
  · intro a ha
    have ha_out : a < h + 4 + m ∨ h + 4 + m + (prefixFlat ℓ).length ≤ a := by
      have hp := hprefix_len ℓ (le_refl ℓ)
      rcases ha with ha | ha
      · exact Or.inl (by omega)
      · exact Or.inr (by dsimp [L, mkDecompLayout] at ha; omega)
    rw [hinv8.2.2.2.2.2.2.2 a ha_out]
    dsimp [st7, st6]
    rw [Function.update_of_ne (by rcases ha with ha | ha <;> [omega; (dsimp [L, mkDecompLayout] at ha; omega)])]
    rw [h5_fr a (by rcases ha with ha | ha <;> [omega; (dsimp [L, mkDecompLayout] at ha; omega)])]
    dsimp [st4, st3, st2, st1]
    rw [Function.update_of_ne (by rcases ha with ha | ha <;> [omega; (dsimp [L, mkDecompLayout] at ha; omega)]),
      Function.update_of_ne (by rcases ha with ha | ha <;> [omega; (dsimp [L, mkDecompLayout] at ha; omega)]),
      Function.update_of_ne (by rcases ha with ha | ha <;> [omega; (dsimp [L, mkDecompLayout] at ha; omega)])]
  · have hsum_cost : ∑ q ∈ Finset.Ico 0 ℓ, (hstep_cost q + (Expr.reg rEll).size + 8) ≤
        20 * (4 * m) + 55 * ℓ := by
      have hbd : ∑ q ∈ Finset.Ico 0 ℓ, hstep_cost q ≤ 20 * (4 * m) + 45 * ℓ := by
        have hstep_le : ∀ q ∈ Finset.Ico 0 ℓ,
            hstep_cost q ≤ (if h : q < recs.length then 20 * (recs[q].rawComps.flatMap compRecord).length else 0) + 45 := by
          intro q _; dsimp only [hstep_cost]; split_ifs <;> omega
        calc ∑ q ∈ Finset.Ico 0 ℓ, hstep_cost q
            ≤ ∑ q ∈ Finset.Ico 0 ℓ, ((if h : q < recs.length then 20 * (recs[q].rawComps.flatMap compRecord).length else 0) + 45) :=
              Finset.sum_le_sum hstep_le
          _ = (∑ q ∈ Finset.Ico 0 ℓ, if h : q < recs.length then 20 * (recs[q].rawComps.flatMap compRecord).length else 0) +
              45 * ℓ := by rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, Nat.sub_zero, smul_eq_mul]; omega
          _ = 20 * (prefixFlat ℓ).length + 45 * ℓ := by
              congr 1
              rw [← hlen, sum_Ico_rec_flatLen]
              dsimp [prefixFlat]
              rw [List.take_length]
          _ ≤ 20 * (4 * m) + 45 * ℓ := by
              have hp := hprefix_len ℓ (le_refl ℓ)
              omega
      calc ∑ q ∈ Finset.Ico 0 ℓ, (hstep_cost q + (Expr.reg rEll).size + 8)
          = (∑ q ∈ Finset.Ico 0 ℓ, hstep_cost q) + ∑ _q ∈ Finset.Ico 0 ℓ, ((Expr.reg rEll).size + 8) :=
            by simp only [add_assoc, Finset.sum_add_distrib]
        _ ≤ (20 * (4 * m) + 45 * ℓ) + 9 * ℓ := by
            gcongr; simp [Expr.size, Finset.sum_const, smul_eq_mul]; omega
        _ = 20 * (4 * m) + 54 * ℓ := by ring
        _ ≤ 20 * (4 * m) + 55 * ℓ := by omega
    simp only [Expr.size] at hc8 hsum_cost
    omega

end

end MinCostFlow.Expander
