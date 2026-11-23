module

public import MinCostFlow.Expander.PruningRelabelProg

import Mathlib.Tactic.Ring

/-!
# Pick-Level Triple and Freeze-Step Setup
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM
open MinCostFlow.Cited

/-! ### Section 7: `pickLevel` and `freezeStep` -/

def pickLevelStmt : Stmt :=
  seqStmts
    [ .assign prPicked (.const 1)
    , .assign prDelta (.load (.bin .add (.reg prDegX) (.reg prU)))
    , .assign prJ (.bin .sub (.reg prH) (.const 1))
    , .loop (.bin .lt (.const 0) (.reg prJ))
        (seqStmts
          [ .assign prTmp1 (.load (.bin .add (.reg prLvlVol) (.reg prJ)))
          , .assign prTmp2 (.bin .mul (.const 4) (.bin .mul (.reg prCcap) (.reg prTmp1)))
          , .cond (.bin .lt (.reg prDelta) (.reg prTmp2))
              .nop
              (.assign prPicked (.reg prJ))
          , .assign prDelta (.bin .add (.reg prDelta) (.reg prTmp1))
          , .assign prJ (.bin .sub (.reg prJ) (.const 1)) ]) ]

lemma pickLevelStmt_noRand : pickLevelStmt.NoRand := by
  dsimp [pickLevelStmt, seqStmts]
  repeat' constructor

lemma volGeLevel_H_freeze {cfg : PruneCfg} {inR : ℕ → Bool} {h : ℕ → ℕ} {u : ℕ}
    (hcfgX : cfg.X = Finset.range cfg.G.n) (huN : u < cfg.G.n) (huR : inR u = true)
    (hhLt : ∀ x, inR x = true → h x < cfg.H) :
    let hTmp := fun x => if x = u then cfg.H else h x
    volGeLevel cfg inR hTmp cfg.H = cfg.degX u := by
  intro hTmp
  have huX : u ∈ cfg.X := by rw [hcfgX]; exact Finset.mem_range.mpr huN
  unfold volGeLevel PruneCfg.degX
  have hsum := Finset.add_sum_erase cfg.X
    (fun x => if (inR x && decide (cfg.H ≤ hTmp x)) = true then cfg.G.degIn cfg.X x else 0) huX
  have herase :
      (∑ x ∈ cfg.X.erase u,
        if (inR x && decide (cfg.H ≤ hTmp x)) = true then cfg.G.degIn cfg.X x else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hne : x ≠ u := (Finset.mem_erase.mp hx).1
    by_cases hxr : inR x = true
    · have hlt : h x < cfg.H := hhLt x hxr
      simp [hxr, hTmp, hne, show ¬ (cfg.H ≤ h x) by omega]
    · simp [hxr]
  rw [← hsum, herase, add_zero]
  simp [huR, hTmp]

lemma volAtLevel_le_volGeLevel (cfg : PruneCfg) (inR : ℕ → Bool) (h : ℕ → ℕ) (ℓ : ℕ) :
    volAtLevel cfg inR h ℓ ≤ volGeLevel cfg inR h ℓ := by
  unfold volAtLevel volGeLevel PruneCfg.degX
  apply Finset.sum_le_sum
  intro x _
  by_cases hr : inR x = true <;> simp [hr]
  split_ifs with h1 h2
  · exact le_rfl
  · omega
  · exact Nat.zero_le _
  · exact le_rfl

lemma volGeLevel_antitone (cfg : PruneCfg) (inR : ℕ → Bool) (h : ℕ → ℕ)
    {a b : ℕ} (hab : a ≤ b) :
    volGeLevel cfg inR h b ≤ volGeLevel cfg inR h a := by
  unfold volGeLevel
  apply Finset.sum_le_sum
  intro x _
  by_cases hr : inR x = true <;> simp [hr]
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (le_trans hab h1) h2
  · exact Nat.zero_le _
  · exact le_rfl

theorem pickLevel_triple {w : ℕ} {p : Program}
    {cfg : PruneCfg} {workAddr u : ℕ} {inR : ℕ → Bool} {h : ℕ → ℕ} (st₀ : State)
    (hw : PruneWordBound w cfg.G.n cfg.G.m cfg.C_cap cfg.H workAddr)
    (hcfg : cfg.Valid) (hcfgX : cfg.X = Finset.range cfg.G.n)
    (hcfgE : cfg.edges.length = cfg.G.m)
    (huN : u < cfg.G.n) (huR : inR u = true) (hhLt : ∀ x, inR x = true → h x < cfg.H)
    (hr_u : st₀.regs prU = u) (hr_H : st₀.regs prH = cfg.H) (hr_cc : st₀.regs prCcap = cfg.C_cap)
    (hr_dX : st₀.regs prDegX = wDegX workAddr cfg.G.n cfg.G.m cfg.H)
    (hr_lv : st₀.regs prLvlVol = wLvlVol workAddr cfg.G.n cfg.G.m cfg.H)
    (hdX_u : st₀.mem (wDegX workAddr cfg.G.n cfg.G.m cfg.H + u) = cfg.degX u)
    (hlvl_eq : ∀ ℓ, 1 ≤ ℓ → ℓ < cfg.H →
      st₀.mem (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + ℓ) =
        volAtLevel cfg inR (fun x => if x = u then cfg.H else h x) ℓ) :
    let hTmp := fun x => if x = u then cfg.H else h x
    Triple w p (fun st => st = st₀) pickLevelStmt
      (normalPost fun st' =>
        (∀ r, r ≠ prJ → r ≠ prTmp1 → r ≠ prTmp2 → r ≠ prDelta → r ≠ prPicked →
          st'.regs r = st₀.regs r) ∧
        st'.regs prPicked = pickLevel cfg inR hTmp ∧
        st'.mem = st₀.mem ∧
        st'.pos = st₀.pos)
      (fun _ => 45 * cfg.H + 20) := by
  intro hTmp
  have hH3 : 3 ≤ cfg.H := PruneCfg.valid_three_le_H hcfg
  have hwb := pruneWordBound_pos hw
  have hlt2w : ∀ k, k < workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H → k < 2 ^ w := fun k hk => by
    unfold PruneWordBound at hw; omega
  have hvol1_le : volGeLevel cfg inR hTmp 1 ≤ 2 * cfg.G.m := by
    rw [← hcfgE]; exact volGeLevel_one_le cfg inR hTmp
  have hvolH_eq : volGeLevel cfg inR hTmp cfg.H = cfg.degX u :=
    volGeLevel_H_freeze hcfgX huN huR hhLt
  have hdegX_lt2w : cfg.degX u < 2 ^ w := by
    have : cfg.degX u ≤ 2 * cfg.G.m := by
      rw [← hvolH_eq]
      exact le_trans (volGeLevel_antitone cfg inR hTmp (by omega)) hvol1_le
    unfold PruneWordBound at hw; omega
  have hH_lt2w : cfg.H < 2 ^ w := hlt2w _ (by unfold pruneWorkSpace; omega)
  let loopCond := Expr.bin .lt (.const 0) (.reg prJ)
  let loopBody := seqStmts
    [ .assign prTmp1 (.load (.bin .add (.reg prLvlVol) (.reg prJ)))
    , .assign prTmp2 (.bin .mul (.const 4) (.bin .mul (.reg prCcap) (.reg prTmp1)))
    , .cond (.bin .lt (.reg prDelta) (.reg prTmp2)) .nop (.assign prPicked (.reg prJ))
    , .assign prDelta (.bin .add (.reg prDelta) (.reg prTmp1))
    , .assign prJ (.bin .sub (.reg prJ) (.const 1)) ]
  let Inv : ℕ → State → Prop := fun j st =>
    j ≤ cfg.H - 1 ∧ st.mem = st₀.mem ∧ st.pos = st₀.pos ∧
    (∀ r, r ≠ prJ → r ≠ prTmp1 → r ≠ prTmp2 → r ≠ prDelta → r ≠ prPicked →
      st.regs r = st₀.regs r) ∧
    st.regs prJ = j ∧
    st.regs prPicked = pickLevelAux cfg inR hTmp (cfg.H - 1 - j) ∧
    st.regs prDelta = volGeLevel cfg inR hTmp (j + 1)
  have hloop : Triple w p (Inv (cfg.H - 1)) (.loop loopCond loopBody)
      (normalPost fun st' =>
        (∀ r, r ≠ prJ → r ≠ prTmp1 → r ≠ prTmp2 → r ≠ prDelta → r ≠ prPicked →
          st'.regs r = st₀.regs r) ∧
        st'.regs prPicked = pickLevel cfg inR hTmp ∧
        st'.mem = st₀.mem ∧
        st'.pos = st₀.pos)
      (fun _ => 40 * (cfg.H - 1) + 10) := by
    refine Triple.loop_inv (Inv := Inv) (condVal := fun st => if 0 < st.regs prJ then 1 else 0)
      (fun j => j) (fun j => 40 * j + 10)
      (fun j st hinv =>
        Expr.eval_bin (op := .lt) (Expr.eval_const (k := 0) (by omega))
          (eval_reg_eq w st prJ rfl)
          (by dsimp only [BinOp.eval]; split_ifs <;> omega))
      (fun j st hinv h0 => by
        have hj0 : j = 0 := by
          by_contra hne
          have : 0 < st.regs prJ := by rw [hinv.2.2.2.2.1]; exact Nat.pos_of_ne_zero hne
          simp [this] at h0
        subst hj0
        refine ⟨⟨hinv.2.2.2.1, ?_, hinv.2.1, hinv.2.2.1⟩, by simp [Expr.size]⟩
        have hpick := hinv.2.2.2.2.2.1
        simpa only [Nat.sub_zero, pickLevel] using hpick)
      (fun j st hinv hne => by
        have hj_pos : 0 < j := by
          by_contra hle
          have hstj : st.regs prJ = 0 := by rw [hinv.2.2.2.2.1]; omega
          simp [hstj] at hne
        have hj_le : j ≤ cfg.H - 1 := hinv.1
        have hj1 : 1 ≤ j := hj_pos
        have hjH : j < cfg.H := by omega
        have hreg := hinv.2.2.2.1
        have hmem := hinv.2.1
        have hpos := hinv.2.2.1
        have hr_j : st.regs prJ = j := hinv.2.2.2.2.1
        have hr_pk : st.regs prPicked = pickLevelAux cfg inR hTmp (cfg.H - 1 - j) := hinv.2.2.2.2.2.1
        have hr_dl : st.regs prDelta = volGeLevel cfg inR hTmp (j + 1) := hinv.2.2.2.2.2.2
        have hvol_j : st.mem (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + j) = volAtLevel cfg inR hTmp j := by
          rw [hmem]; exact hlvl_eq j hj1 hjH
        have hvol_j_le : volAtLevel cfg inR hTmp j ≤ 2 * cfg.G.m :=
          le_trans (volAtLevel_le_volGeLevel cfg inR hTmp j)
            (le_trans (volGeLevel_antitone cfg inR hTmp hj1) hvol1_le)
        have hvol_j_lt2w : volAtLevel cfg inR hTmp j < 2 ^ w := by
          unfold PruneWordBound at hw; omega
        have hmul_inner_lt2w : cfg.C_cap * volAtLevel cfg inR hTmp j < 2 ^ w := by
          have : cfg.C_cap * volAtLevel cfg inR hTmp j ≤ 8 * cfg.C_cap * cfg.G.m := by
            calc cfg.C_cap * volAtLevel cfg inR hTmp j
                ≤ cfg.C_cap * (2 * cfg.G.m) := Nat.mul_le_mul_left _ hvol_j_le
              _ ≤ 8 * cfg.C_cap * cfg.G.m := by ring_nf; omega
          unfold PruneWordBound at hw; omega
        have hmul4_lt2w : 4 * (cfg.C_cap * volAtLevel cfg inR hTmp j) < 2 ^ w := by
          have : 4 * (cfg.C_cap * volAtLevel cfg inR hTmp j) ≤ 8 * cfg.C_cap * cfg.G.m := by
            calc 4 * (cfg.C_cap * volAtLevel cfg inR hTmp j)
                ≤ 4 * (cfg.C_cap * (2 * cfg.G.m)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hvol_j_le)
              _ = 8 * cfg.C_cap * cfg.G.m := by ring
          unfold PruneWordBound at hw; omega
        have hsum_dl_eq : volGeLevel cfg inR hTmp (j + 1) + volAtLevel cfg inR hTmp j =
            volGeLevel cfg inR hTmp j := by
          rw [Nat.add_comm]; exact (volGeLevel_succ_add cfg inR hTmp j).symm
        have hsum_dl_lt2w : volGeLevel cfg inR hTmp (j + 1) + volAtLevel cfg inR hTmp j < 2 ^ w := by
          rw [hsum_dl_eq]
          have : volGeLevel cfg inR hTmp j ≤ 2 * cfg.G.m :=
            le_trans (volGeLevel_antitone cfg inR hTmp hj1) hvol1_le
          unfold PruneWordBound at hw; omega
        let r1 := Function.update st.regs prTmp1 (volAtLevel cfg inR hTmp j)
        let s1 : State := { mem := st.mem, regs := r1, pos := st.pos }
        let rhsMul := 4 * (cfg.C_cap * volAtLevel cfg inR hTmp j)
        let r2 := Function.update r1 prTmp2 rhsMul
        let s2 : State := { mem := st.mem, regs := r2, pos := st.pos }
        let r3 := if volGeLevel cfg inR hTmp (j + 1) < rhsMul then r2 else Function.update r2 prPicked j
        let s3 : State := { mem := st.mem, regs := r3, pos := st.pos }
        let r4 := Function.update r3 prDelta (volGeLevel cfg inR hTmp (j + 1) + volAtLevel cfg inR hTmp j)
        let s4 : State := { mem := st.mem, regs := r4, pos := st.pos }
        let r5 := Function.update r4 prJ (j - 1)
        let s5 : State := { mem := st.mem, regs := r5, pos := st.pos }
        refine ⟨32, by
          intro st_init ω hsi
          subst st_init
          have hs1 : Runs w p ω (.assign prTmp1 (.load (.bin .add (.reg prLvlVol) (.reg prJ)))) st .normal s1 5 :=
            runs_assign_iff.mpr ⟨volAtLevel cfg inR hTmp j,
              eval_load_add_eq w st prLvlVol prJ (by rw [hreg prLvlVol (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hr_lv)
                hr_j (hlt2w _ (by unfold pruneWorkSpace; dsimp [wLvlVol]; omega)) hvol_j,
              rfl, rfl, by simp [Expr.size]⟩
          have hr1_cc : s1.regs prCcap = cfg.C_cap := by
            dsimp [s1, r1]; rw [Function.update_of_ne (by decide), hreg prCcap (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hr_cc
          have hr1_t1 : s1.regs prTmp1 = volAtLevel cfg inR hTmp j := by
            dsimp [s1, r1]; rw [Function.update_self]
          have hs2 : Runs w p ω (.assign prTmp2 (.bin .mul (.const 4) (.bin .mul (.reg prCcap) (.reg prTmp1)))) s1 .normal s2 6 :=
            runs_assign_iff.mpr ⟨rhsMul,
              Expr.eval_bin (op := .mul) (Expr.eval_const (by omega))
                (Expr.eval_bin (op := .mul) (eval_reg_eq w s1 prCcap hr1_cc) (eval_reg_eq w s1 prTmp1 hr1_t1)
                  (by dsimp only [BinOp.eval]; exact hmul_inner_lt2w))
                (by dsimp only [BinOp.eval]; exact hmul4_lt2w),
              rfl, rfl, by simp [Expr.size]⟩
          have hr2_dl : s2.regs prDelta = volGeLevel cfg inR hTmp (j + 1) := by
            dsimp [s2, r2, r1]
            rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
            exact hr_dl
          have hr2_t2 : s2.regs prTmp2 = rhsMul := by dsimp [s2, r2]; rw [Function.update_self]
          have hr2_j : s2.regs prJ = j := by
            dsimp [s2, r2, r1]
            rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
            exact hr_j
          have hs3 : ∃ c3, c3 ≤ 6 ∧ Runs w p ω
              (.cond (.bin .lt (.reg prDelta) (.reg prTmp2)) .nop (.assign prPicked (.reg prJ)))
              s2 .normal s3 c3 := by
            have hcond3 : Expr.eval w s2 (.bin .lt (.reg prDelta) (.reg prTmp2)) =
                some (if volGeLevel cfg inR hTmp (j + 1) < rhsMul then 1 else 0) :=
              Expr.eval_bin (op := .lt) (eval_reg_eq w s2 prDelta hr2_dl) (eval_reg_eq w s2 prTmp2 hr2_t2)
                (by dsimp only [BinOp.eval]; split_ifs <;> omega)
            by_cases hlt_dl : volGeLevel cfg inR hTmp (j + 1) < rhsMul
            · refine ⟨5, by omega, runs_cond_iff.mpr ⟨1, 1, ?_, ?_, by simp [Expr.size]⟩⟩
              · simpa [hlt_dl] using hcond3
              · simp only [Nat.one_ne_zero, ↓reduceIte, s3, r3, hlt_dl]
                exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩
            · refine ⟨6, le_rfl, runs_cond_iff.mpr ⟨0, 2, ?_, ?_, by simp [Expr.size]⟩⟩
              · simpa [hlt_dl] using hcond3
              · simp only [↓reduceIte, s3, r3, hlt_dl]
                exact runs_assign_iff.mpr ⟨j, eval_reg_eq w s2 prJ hr2_j, rfl, rfl, by simp [Expr.size]⟩
          rcases hs3 with ⟨c3, hc3, hs3⟩
          have hr3_dl : s3.regs prDelta = volGeLevel cfg inR hTmp (j + 1) := by
            dsimp [s3, r3]; split_ifs
            · exact hr2_dl
            · rw [Function.update_of_ne (by decide)]; exact hr2_dl
          have hr3_t1 : s3.regs prTmp1 = volAtLevel cfg inR hTmp j := by
            have hr2_t1 : s2.regs prTmp1 = volAtLevel cfg inR hTmp j := by
              dsimp [s2, r2]; rw [Function.update_of_ne (by decide)]; exact hr1_t1
            dsimp [s3, r3]; split_ifs
            · exact hr2_t1
            · rw [Function.update_of_ne (by decide)]; exact hr2_t1
          have hs4 : Runs w p ω (.assign prDelta (.bin .add (.reg prDelta) (.reg prTmp1))) s3 .normal s4 4 :=
            runs_assign_iff.mpr ⟨volGeLevel cfg inR hTmp (j + 1) + volAtLevel cfg inR hTmp j,
              Expr.eval_bin (op := .add) (eval_reg_eq w s3 prDelta hr3_dl) (eval_reg_eq w s3 prTmp1 hr3_t1)
                (by dsimp only [BinOp.eval]; exact hsum_dl_lt2w),
              rfl, rfl, by simp [Expr.size]⟩
          have hr4_j : s4.regs prJ = j := by
            have hr3_j : s3.regs prJ = j := by
              dsimp [s3, r3]; split_ifs
              · exact hr2_j
              · rw [Function.update_of_ne (by decide)]; exact hr2_j
            dsimp [s4, r4]; rw [Function.update_of_ne (by decide)]; exact hr3_j
          have hs5 : Runs w p ω (.assign prJ (.bin .sub (.reg prJ) (.const 1))) s4 .normal s5 4 :=
            runs_assign_iff.mpr ⟨j - 1,
              Expr.eval_bin (op := .sub) (eval_reg_eq w s4 prJ hr4_j) (Expr.eval_const (by omega))
                (by dsimp only [BinOp.eval]; omega),
              rfl, rfl, by simp [Expr.size]⟩
          refine ⟨.normal, s5, _, runs_seq hs1 (runs_seq hs2 (runs_seq hs3 (runs_seq hs4 hs5))), ?_,
            by dsimp only; omega⟩
          refine ⟨j - 1, ⟨by omega, hmem, hpos, ?_, ?_, ?_, ?_⟩, by omega,
            by simp only [Expr.size]; omega⟩
          · intro r hrj hr1 hr2 hrd hrp
            dsimp [s5, r5, r4, r3, r2, r1]
            rw [Function.update_of_ne hrj, Function.update_of_ne hrd]
            split_ifs
            · rw [Function.update_of_ne hr2, Function.update_of_ne hr1]
              exact hreg r hrj hr1 hr2 hrd hrp
            · rw [Function.update_of_ne hrp, Function.update_of_ne hr2, Function.update_of_ne hr1]
              exact hreg r hrj hr1 hr2 hrd hrp
          · dsimp [s5, r5]; rw [Function.update_self]
          · have hk1 : cfg.H - 1 - (j - 1) = (cfg.H - 1 - j) + 1 := by omega
            have hj_eq : cfg.H - 1 - (cfg.H - 1 - j) = j := by omega
            rw [hk1]
            change s5.regs prPicked =
              let lvl := cfg.H - 1 - (cfg.H - 1 - j)
              if 4 * cfg.C_cap * volAtLevel cfg inR hTmp lvl ≤ volGeLevel cfg inR hTmp (lvl + 1) then lvl
              else pickLevelAux cfg inR hTmp (cfg.H - 1 - j)
            rw [hj_eq]
            dsimp [s5, r5, r4, r3, r2, r1]
            rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
            by_cases hle : 4 * cfg.C_cap * volAtLevel cfg inR hTmp j ≤ volGeLevel cfg inR hTmp (j + 1)
            · have hnlt : ¬ volGeLevel cfg inR hTmp (j + 1) < rhsMul := by
                dsimp [rhsMul]; rw [← Nat.mul_assoc]; omega
              simp only [hnlt, ↓reduceIte, hle, Function.update_self]
            · have hlt_r : volGeLevel cfg inR hTmp (j + 1) < rhsMul := by
                dsimp [rhsMul]; rw [← Nat.mul_assoc]; omega
              simp only [hlt_r, ↓reduceIte, hle]
              rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
              exact hr_pk
          · dsimp [s5, r5, r4]; rw [Function.update_of_ne (by decide), Function.update_self, hsum_dl_eq]
            rw [show j - 1 + 1 = j by omega]⟩)
      (cfg.H - 1)
  intro st ω hst
  subst st
  let r1 := Function.update st₀.regs prPicked 1
  let r2 := Function.update r1 prDelta (cfg.degX u)
  let r3 := Function.update r2 prJ (cfg.H - 1)
  let s1 : State := { mem := st₀.mem, regs := r1, pos := st₀.pos }
  let s2 : State := { mem := st₀.mem, regs := r2, pos := st₀.pos }
  let s3 : State := { mem := st₀.mem, regs := r3, pos := st₀.pos }
  have hs1 : Runs w p ω (.assign prPicked (.const 1)) st₀ .normal s1 2 :=
    runs_assign_iff.mpr ⟨1, Expr.eval_const (k := 1) (by omega), rfl, rfl, by simp [Expr.size]⟩
  have hr1_dX : s1.regs prDegX = wDegX workAddr cfg.G.n cfg.G.m cfg.H := by
    dsimp [s1, r1]; rw [Function.update_of_ne (by decide)]; exact hr_dX
  have hr1_u : s1.regs prU = u := by
    dsimp [s1, r1]; rw [Function.update_of_ne (by decide)]; exact hr_u
  have hs2 : Runs w p ω (.assign prDelta (.load (.bin .add (.reg prDegX) (.reg prU)))) s1 .normal s2 5 :=
    runs_assign_iff.mpr ⟨cfg.degX u,
      eval_load_add_eq w s1 prDegX prU hr1_dX hr1_u
        (hlt2w _ (by unfold pruneWorkSpace; dsimp [wDegX]; omega)) hdX_u,
      rfl, rfl, by simp [Expr.size]⟩
  have hr2_H : s2.regs prH = cfg.H := by
    dsimp [s2, r2, r1]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    exact hr_H
  have hs3 : Runs w p ω (.assign prJ (.bin .sub (.reg prH) (.const 1))) s2 .normal s3 4 :=
    runs_assign_iff.mpr ⟨cfg.H - 1,
      Expr.eval_bin (op := .sub) (eval_reg_eq w s2 prH hr2_H) (Expr.eval_const (k := 1) (by omega))
        (by dsimp only [BinOp.eval]; omega),
      rfl, rfl, by simp [Expr.size]⟩
  have hInv_s3 : Inv (cfg.H - 1) s3 := by
    refine ⟨le_rfl, rfl, rfl, fun r hr1 hr2 hr3 hr4 hr5 => ?_, ?_, ?_, ?_⟩
    · dsimp [s3, r3, r2, r1]
      rw [Function.update_of_ne hr1, Function.update_of_ne hr4, Function.update_of_ne hr5]
    · dsimp [s3, r3]; rw [Function.update_self]
    · dsimp [s3, r3, r2, r1]
      rw [Nat.sub_self, Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]
      rfl
    · dsimp [s3, r3, r2]
      rw [Function.update_of_ne (by decide), Function.update_self, Nat.sub_add_cancel (by omega), hvolH_eq]
  rcases hloop s3 ω hInv_s3 with ⟨o, st', c_loop, hrun_loop, hq_loop, hc_loop⟩
  refine ⟨o, st', 2 + (5 + (4 + c_loop + 1) + 1) + 1,
    runs_seq hs1 (runs_seq hs2 (runs_seq hs3 hrun_loop)), hq_loop, ?_⟩
  dsimp only at hc_loop ⊢; omega


def walkPref (u : ℕ) (buckets : ℕ → List ℕ) (lvl : ℕ) : ℕ → List ℕ
  | 0 => [u]
  | k + 1 => walkPref u buckets lvl k ++ buckets (lvl + 1 + k)

def freezeRemList (cfg : PruneCfg) (u : ℕ) (s : PruneState) (buckets : ℕ → List ℕ) : List ℕ :=
  let hTmp := fun z => if z = u then cfg.H else s.h z
  let lvl := pickLevel cfg s.inR hTmp
  let buckets1 := if 1 ≤ s.h u then fun ℓ => if ℓ = s.h u then (buckets ℓ).erase u else buckets ℓ else buckets
  walkPref u buckets1 lvl (cfg.H - (lvl + 1))

def freezeStepStmt : Stmt :=
  seqStmts
    [ unlinkLvlStmt
    , .store (.bin .add (.reg prHArr) (.reg prU)) (.reg prH)
    , .store (.bin .add (.reg prCur) (.reg prU)) (.const 0)
    , pickLevelStmt
    , .store (.reg prRemArr) (.reg prU)
    , .assign prEnd (.const 1)
    , .assign prStart (.bin .add (.reg prPicked) (.const 1))
    , .loop (.bin .lt (.reg prStart) (.reg prH))
        (walkBucketStmt ;; .assign prStart (.bin .add (.reg prStart) (.const 1)))
    , .assign prSuf (.reg prEnd)
    , .assign prI (.const 0)
    , .loop (.bin .lt (.reg prI) (.reg prSuf))
        (seqStmts
          [ .assign prU (.load (.bin .add (.reg prRemArr) (.reg prI)))
          , removeOneFromRStmt
          , .assign prI (.bin .add (.reg prI) (.const 1)) ]) ]

lemma freezeStepStmt_noRand : freezeStepStmt.NoRand := by
  dsimp [freezeStepStmt, seqStmts]
  repeat'
    first
    | exact unlinkLvlStmt_noRand
    | exact pickLevelStmt_noRand
    | exact walkBucketStmt_noRand
    | exact removeOneFromRStmt_noRand
    | constructor


end MinCostFlow.Expander
