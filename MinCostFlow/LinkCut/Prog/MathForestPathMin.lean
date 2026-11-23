module

public import MinCostFlow.LinkCut.Prog.MathForestQueries

/-!
# Word-RAM Query Procedure `pathMin` for `MathForest`

Implements deterministic (`Stmt.NoRand`) `lctPathMinBody` and proves `lctPathMinBody_runs`
establishing full `LctMemRep`, `DSRep.Respects`, exact returned hit `[has, eid, x, y, avail, flow]`,
and the `O((L + 1) log (n + 2))` amortized cost bound (van den Brand et al., `arXiv:2309.16629v1`,
Lemma 4.1 p. 13, from [KangP15] Section 4).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section PathMinProcedure

def lctPathMinElseBody (lp : LctProcs) : Stmt :=
  .call 12 lp.reroot [.reg 7, .reg 8] ;;
  .call 12 lp.expose [.reg 7, .reg 9] ;;
  .assign 11 (.load (.bin .add (.bin .add (.reg 7) (.bin .mul (.const NODE_STRIDE) (.reg 9)))
    (.const OFF_MIN1_FIRST))) ;;
  .call 12 lp.splay.splay [.reg 7, .reg 11] ;;
  .assign 17 (.bin .add (.reg 7) (.bin .mul (.const NODE_STRIDE) (.reg 11))) ;;
  (.store (.reg 4) (.const 1) ;;
   .assign 12 (fieldLoadExpr 17 OFF_EID) ;;
   .store (.bin .add (.reg 4) (.const 1)) (.reg 12) ;;
   .assign 12 (fieldLoadExpr 17 OFF_DIR) ;;
   .assign 13 (fieldLoadExpr 17 OFF_EU) ;;
   .assign 14 (fieldLoadExpr 17 OFF_EV) ;;
   .cond (.reg 12)
     (.store (.bin .add (.reg 4) (.const 2)) (.reg 13) ;;
      .store (.bin .add (.reg 4) (.const 3)) (.reg 14))
     (.store (.bin .add (.reg 4) (.const 2)) (.reg 14) ;;
      .store (.bin .add (.reg 4) (.const 3)) (.reg 13))) ;;
  .assign 15 (fieldLoadExpr 17 OFF_AF_PTR) ;;
  .assign 13 (.bin .add (.reg 4) (.const 4)) ;;
  .call 16 lp.copyWords [.reg 15, .reg 13, .reg 5] ;;
  .assign 15 (fieldLoadExpr 17 OFF_FLOW_PTR) ;;
  .assign 14 (.bin .add (.reg 13) (.reg 5)) ;;
  .call 16 lp.copyWords [.reg 15, .reg 14, .reg 5]

/-- Deterministic Word-RAM `pathMin` body taking `args = [b, u, v, hp_caller]`:
allocates `4 + 2 * L` answer words at `hp_caller`, returns `has = 0` when `u = v`, and
otherwise rerroots `u`, exposes `v`, splays `ed = OFF_MIN1_FIRST (v + 1)` to push all tags
and reversals down to `ed`, writes `[1, eid, x, y]` and copies `OFF_AF_PTR` (tree-forward avail)
and `OFF_FLOW_PTR` (`L` limbs each) into `hp_caller + 4` and `hp_caller + 4 + L`. -/
def lctPathMinBody (lp : LctProcs) : Stmt :=
  .assign 4 (.reg 3) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const LCT_HDR_L))) ;;
  .assign 6 (.reg 0) ;;
  .assign 7 (.bin .add (.reg 0) (.const LCT_HDR_SIZE)) ;;
  .assign 8 (.bin .add (.reg 1) (.const 1)) ;;
  .assign 9 (.bin .add (.reg 2) (.const 1)) ;;
  .assign 10 (.bin .add (.reg 4) (.bin .add (.const 4) (.bin .mul (.const 2) (.reg 5)))) ;;
  .store (.bin .add (.reg 0) (.const LCT_HDR_HP)) (.reg 10) ;;
  .cond (.bin .eq (.reg 1) (.reg 2))
    (.store (.reg 4) (.const 0))
    (lctPathMinElseBody lp) ;;
  .assign 13 (.load (.bin .add (.reg 6) (.const LCT_HDR_HP))) ;;
  .ret (.bin .add (.reg 13) (.const 1))

theorem lctPathMinBody_noRand (lp : LctProcs) : (lctPathMinBody lp).NoRand := by
  simp [lctPathMinBody, lctPathMinElseBody, fieldLoadExpr, fieldAddrExpr, Stmt.NoRand]

private lemma pathMin_room_re_arith {hp L phi0 c_rexp_log cp_log m p2w : ℕ}
    (hk : c_rexp_log ≤ cp_log)
    (hbd : hp + phi0 + cp_log + m + 2 * L + 5 < p2w) :
    (hp + (4 + 2 * L)) + phi0 + c_rexp_log + m + 1 < p2w := by
  omega

private lemma pathMin_room2_arith {c_re c_exp s hp L phi0 phi2 c_rexp_log cp_log m6 m7 p2w : ℕ}
    (h1 : c_re + c_exp + (s - (hp + (4 + 2 * L))) + phi2 ≤ phi0 + c_rexp_log)
    (hle : hp + (4 + 2 * L) ≤ s) (hk : c_rexp_log ≤ cp_log) (hm : m6 ≤ m7)
    (hbd : hp + phi0 + cp_log + m7 + 2 * L + 5 < p2w) :
    s + m6 < p2w := by
  omega

private lemma pathMin_phi_arith {c_re c_exp c_sp s2 s3 hp_eff phi0 phi2 phi3 cr_e k3 cs : ℕ}
    (h12 : c_re + c_exp + (s2 - hp_eff) + phi2 ≤ phi0 + cr_e)
    (h23 : c_sp + (s3 - s2) + phi3 ≤ phi2 + k3 + cs)
    (_hle2 : hp_eff ≤ s2) (_hle3 : s2 ≤ s3) :
    (c_re + c_exp + c_sp) + (s3 - hp_eff) + phi3 ≤ phi0 + cr_e + k3 + cs := by
  omega

private lemma pathMin_cost_arith {c_tot c_re c_exp c_sp s hp L phi0 phi3 cr_log k3_log cs cp_log space p2w m7 : ℕ}
    (h1 : (c_re + c_exp + c_sp) + (s - (hp + (4 + 2 * L))) + phi3 ≤
      phi0 + cr_log + k3_log + cs)
    (hle : hp + (4 + 2 * L) ≤ s)
    (hct : c_tot ≤ c_re + c_exp + c_sp + 34 * L + 220)
    (hk : cr_log + k3_log + cs + 36 * L + 500 ≤ cp_log)
    (hsp : phi0 + cp_log + 2 * L + 5 ≤ space)
    (hbd : hp + phi0 + cp_log + m7 + 2 * L + 5 < p2w) :
    s + 1 < p2w ∧ s + 1 ≤ hp + space ∧
      c_tot + (s + 1 - hp) + phi3 ≤ phi0 + cp_log := by
  omega

private lemma pathMin_hk_mul_arith {L c_rexp k3 cs c_pm logN : ℕ}
    (hk : c_rexp + k3 + cs + 36 * L + 500 ≤ c_pm) (hlog : 1 ≤ logN) :
    c_rexp * logN + k3 * logN + cs + 36 * L + 500 ≤ c_pm * logN := by
  have h1 : cs + 36 * L + 500 ≤ (cs + 36 * L + 500) * logN := Nat.le_mul_of_pos_right _ hlog
  have h2 : (c_rexp + k3 + (cs + 36 * L + 500)) * logN =
      c_rexp * logN + k3 * logN + (cs + 36 * L + 500) * logN := by ring
  have h3 : (c_rexp + k3 + (cs + 36 * L + 500)) * logN ≤ c_pm * logN := by
    simpa only [Nat.add_assoc] using Nat.mul_le_mul_right logN hk
  omega

private lemma pathMin_ctot_arith {c_re c_exp c_sp c_cp1 c_cp2 L : ℕ}
    (h1 : c_cp1 ≤ 17 * L + 10) (h2 : c_cp2 ≤ 17 * L + 10) :
    (2 + c_re + 1) + ((2 + c_exp + 1) + (9 + ((2 + c_sp + 1) + (6 + (47 + (5 + (4 +
      ((3 + c_cp1 + 1) + (5 + (4 + (3 + c_cp2 + 1) + 1) + 1) + 1) + 1) + 1) +
      1) + 1) + 1) + 1) + 1) + 1 + 60 ≤
    c_re + c_exp + c_sp + 34 * L + 220 := by
  have hsum :
      (2 + c_re + 1) + ((2 + c_exp + 1) + (9 + ((2 + c_sp + 1) + (6 + (47 + (5 + (4 +
        ((3 + c_cp1 + 1) + (5 + (4 + (3 + c_cp2 + 1) + 1) + 1) + 1) + 1) + 1) +
        1) + 1) + 1) + 1) + 1) + 1 + 60 =
      c_re + c_exp + c_sp + c_cp1 + c_cp2 + 168 := by ring
  omega

private lemma pathMin_eq_cost_arith {c_tot s hp L phi0 cp space logN : ℕ}
    (hle : s = hp + (4 + 2 * L)) (hct : c_tot ≤ 80)
    (hcp : 2 * L + 500 ≤ cp) (hlog : 1 ≤ logN)
    (hsp : phi0 + cp * logN + 2 * L + 5 ≤ space) :
    s + 1 ≤ hp + space ∧ c_tot + (s + 1 - hp) + phi0 ≤ phi0 + cp * logN := by
  have hm : 2 * L + 500 ≤ cp * logN := le_trans hcp (Nat.le_mul_of_pos_right _ hlog)
  omega

private lemma pathMin_eq_room_lt {s hp L phi0 cp_log m p2w : ℕ}
    (hle : s = hp + (4 + 2 * L))
    (hbd : hp + phi0 + cp_log + m + 2 * L + 5 < p2w) :
    s + 1 < p2w := by
  omega

private lemma pathMin_xy_eq {dir eu ev rmin_eu rmin_ev : ℕ} {rmin_fwd : Bool}
    (h1 : rmin_eu = eu) (h2 : rmin_ev = ev) (h3 : rmin_fwd = decide (dir ≠ 0)) :
    (if dir = 0 then ev else eu) = (if rmin_fwd then rmin_eu else rmin_ev) ∧
    (if dir = 0 then eu else ev) = (if rmin_fwd then rmin_ev else rmin_eu) := by
  subst h1 h2 h3
  by_cases hd : dir = 0 <;> simp [hd]

private lemma pathMin_lt4_addL (a k L : ℕ) (h : k < 4) : a + k < a + 4 + L := by omega
private lemma pathMin_lt4_add4 (a k : ℕ) (h : k < 4) : a + k < a + 4 := by omega
private lemma pathMin_lt0_addL (a L : ℕ) : a < a + 4 + L := by omega
private lemma pathMin_lt0_add4 (a : ℕ) : a < a + 4 := by omega
private lemma pathMin_lt4L_addL (a i L : ℕ) (h : i < L) : a + 4 + i < a + 4 + L := by omega

private lemma pathMin_src_disj_4 {hp ptr i L : ℕ} (hi : i < L)
    (h : hp + (4 + 2 * L) ≤ ptr ∨ ptr + L ≤ hp) :
    ptr + i < hp ∨ hp + 4 ≤ ptr + i := by
  rcases h with h1 | h2 <;> [exact Or.inr (by omega); exact Or.inl (by omega)]

private lemma pathMin_src_disj_4L {hp ptr i L : ℕ} (hi : i < L)
    (h : hp + (4 + 2 * L) ≤ ptr ∨ ptr + L ≤ hp) :
    ptr + i < hp + 4 ∨ hp + 4 + L ≤ ptr + i := by
  rcases h with h1 | h2 <;> [exact Or.inr (by omega); exact Or.inl (by omega)]

private lemma update4_eq_outside {mem : ℕ → ℕ} {hp0 v0 v1 v2 v3 a : ℕ}
    (ha : a < hp0 ∨ hp0 + 4 ≤ a) :
    Function.update (Function.update (Function.update (Function.update mem hp0 v0)
      (hp0 + 1) v1) (hp0 + 2) v2) (hp0 + 3) v3 a = mem a := by
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

private lemma runs_fieldLoad_17 {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem : ℕ → ℕ} {regs : ℕ → ℕ} {pos rd off nb ed : ℕ}
    (hr17 : regs 17 = nb + NODE_STRIDE * ed)
    (hoff_w : off < 2 ^ w)
    (haddr_w : nb + NODE_STRIDE * ed + off < 2 ^ w) :
    Runs w p ω (.assign rd (fieldLoadExpr 17 off))
      { mem := mem, regs := regs, pos := pos } .normal
      { mem := mem, regs := Function.update regs rd (nodeField mem nb ed off), pos := pos } 5 := by
  refine runs_assign_iff.mpr ⟨nodeField mem nb ed off, ?_, rfl, rfl,
    by simp [fieldLoadExpr, fieldAddrExpr, Expr.size]⟩
  have hadd := Expr.eval_add
    (Expr.eval_reg_of_eq (st := { mem := mem, regs := regs, pos := pos }) (r := 17) hr17)
    (Expr.eval_const hoff_w) haddr_w
  dsimp only [fieldLoadExpr, fieldAddrExpr]
  rw [Expr.eval_load hadd]; rfl

private lemma pathMin_write4_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem : ℕ → ℕ} {regs : ℕ → ℕ} {pos nb ed hp_caller : ℕ}
    (hr4 : regs 4 = hp_caller) (hr17 : regs 17 = nb + NODE_STRIDE * ed)
    (h1_w : 1 < 2 ^ w) (h2_w : 2 < 2 ^ w) (h3_w : 3 < 2 ^ w)
    (h36_w : 36 < 2 ^ w)
    (hhp3_w : hp_caller + 3 < 2 ^ w)
    (hed_lt : ∀ off < NODE_STRIDE, nb + NODE_STRIDE * ed + off < hp_caller ∧
      nb + NODE_STRIDE * ed + off < 2 ^ w) :
    let eid := nodeField mem nb ed OFF_EID
    let dir := nodeField mem nb ed OFF_DIR
    let eu := nodeField mem nb ed OFF_EU
    let ev := nodeField mem nb ed OFF_EV
    let xv := if dir = 0 then ev else eu
    let yv := if dir = 0 then eu else ev
    let mem' := Function.update (Function.update (Function.update (Function.update mem hp_caller 1)
      (hp_caller + 1) eid) (hp_caller + 2) xv) (hp_caller + 3) yv
    ∃ regs' : ℕ → ℕ,
      Runs w p ω
        (.store (.reg 4) (.const 1) ;;
         .assign 12 (fieldLoadExpr 17 OFF_EID) ;;
         .store (.bin .add (.reg 4) (.const 1)) (.reg 12) ;;
         .assign 12 (fieldLoadExpr 17 OFF_DIR) ;;
         .assign 13 (fieldLoadExpr 17 OFF_EU) ;;
         .assign 14 (fieldLoadExpr 17 OFF_EV) ;;
         .cond (.reg 12)
           (.store (.bin .add (.reg 4) (.const 2)) (.reg 13) ;;
            .store (.bin .add (.reg 4) (.const 3)) (.reg 14))
           (.store (.bin .add (.reg 4) (.const 2)) (.reg 14) ;;
            .store (.bin .add (.reg 4) (.const 3)) (.reg 13)))
        { mem := mem, regs := regs, pos := pos } .normal
        { mem := mem', regs := regs', pos := pos } 47 ∧
      regs' 4 = hp_caller ∧ regs' 5 = regs 5 ∧ regs' 6 = regs 6 ∧
      regs' 7 = regs 7 ∧ regs' 17 = nb + NODE_STRIDE * ed := by
  dsimp only
  have ha_eid := (hed_lt OFF_EID (by decide)).1
  have ha_dir := (hed_lt OFF_DIR (by decide)).1
  have ha_eu := (hed_lt OFF_EU (by decide)).1
  have ha_ev := (hed_lt OFF_EV (by decide)).1
  let eid := nodeField mem nb ed OFF_EID
  let dir := nodeField mem nb ed OFF_DIR
  let eu := nodeField mem nb ed OFF_EU
  let ev := nodeField mem nb ed OFF_EV
  let xv := if dir = 0 then ev else eu
  let yv := if dir = 0 then eu else ev
  let m0 := Function.update mem hp_caller 1
  have hm0_eid : nodeField m0 nb ed OFF_EID = eid := Function.update_of_ne ha_eid.ne 1 mem
  let r1 := Function.update regs 12 eid
  let m1 := Function.update m0 (hp_caller + 1) eid
  let r2 := Function.update r1 12 dir
  let r3 := Function.update r2 13 eu
  let r4 := Function.update r3 14 ev
  have hm1_dir : nodeField m1 nb ed OFF_DIR = dir := by
    dsimp only [nodeField, m1, m0, dir]
    rw [Function.update_of_ne (by omega), Function.update_of_ne ha_dir.ne]
  have hm1_eu : nodeField m1 nb ed OFF_EU = eu := by
    dsimp only [nodeField, m1, m0, eu]
    rw [Function.update_of_ne (by omega), Function.update_of_ne ha_eu.ne]
  have hm1_ev : nodeField m1 nb ed OFF_EV = ev := by
    dsimp only [nodeField, m1, m0, ev]
    rw [Function.update_of_ne (by omega), Function.update_of_ne ha_ev.ne]
  have hr_ok1 : r1 4 = hp_caller ∧ r1 12 = eid ∧ r1 17 = nb + NODE_STRIDE * ed := by
    refine ⟨?_, ?_, ?_⟩ <;> simp [r1, hr4, hr17, Function.update_of_ne]
  have hr_ok4 : r4 4 = hp_caller ∧ r4 12 = dir ∧ r4 13 = eu ∧ r4 14 = ev := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [r4, r3, r2, r1, hr4, Function.update_of_ne]
  have hs0 : Runs w p ω (.store (.reg 4) (.const 1)) { mem := mem, regs := regs, pos := pos }
      .normal { mem := m0, regs := regs, pos := pos } 3 :=
    runs_store_iff.mpr ⟨hp_caller, 1, Expr.eval_reg_of_eq hr4, Expr.eval_const h1_w, rfl, rfl, by decide⟩
  have hs1 : Runs w p ω (.assign 12 (fieldLoadExpr 17 OFF_EID)) { mem := m0, regs := regs, pos := pos }
      .normal { mem := m0, regs := r1, pos := pos } 5 := by
    simpa [hm0_eid, r1] using runs_fieldLoad_17 (mem := m0) (rd := 12) hr17
      (lt_trans (by decide : OFF_EID < 36) h36_w) (hed_lt OFF_EID (by decide)).2
  have hs2 : Runs w p ω (.store (.bin .add (.reg 4) (.const 1)) (.reg 12))
      { mem := m0, regs := r1, pos := pos } .normal { mem := m1, regs := r1, pos := pos } 5 :=
    runs_store_iff.mpr ⟨hp_caller + 1, eid,
      Expr.eval_add (Expr.eval_reg_of_eq (st := { mem := m0, regs := r1, pos := pos }) hr_ok1.1)
        (Expr.eval_const h1_w) (by omega),
      Expr.eval_reg_of_eq (st := { mem := m0, regs := r1, pos := pos }) hr_ok1.2.1, rfl, rfl, by decide⟩
  have hs3 : Runs w p ω (.assign 12 (fieldLoadExpr 17 OFF_DIR)) { mem := m1, regs := r1, pos := pos }
      .normal { mem := m1, regs := r2, pos := pos } 5 := by
    simpa [hm1_dir, r2] using runs_fieldLoad_17 (mem := m1) (rd := 12) (by simp [r1, hr17])
      (lt_trans (by decide : OFF_DIR < 36) h36_w) (hed_lt OFF_DIR (by decide)).2
  have hs4 : Runs w p ω (.assign 13 (fieldLoadExpr 17 OFF_EU)) { mem := m1, regs := r2, pos := pos }
      .normal { mem := m1, regs := r3, pos := pos } 5 := by
    simpa [hm1_eu, r3] using runs_fieldLoad_17 (mem := m1) (rd := 13) (by simp [r2, r1, hr17])
      (lt_trans (by decide : OFF_EU < 36) h36_w) (hed_lt OFF_EU (by decide)).2
  have hs5 : Runs w p ω (.assign 14 (fieldLoadExpr 17 OFF_EV)) { mem := m1, regs := r3, pos := pos }
      .normal { mem := m1, regs := r4, pos := pos } 5 := by
    simpa [hm1_ev, r4] using runs_fieldLoad_17 (mem := m1) (rd := 14) (by simp [r3, r2, r1, hr17])
      (lt_trans (by decide : OFF_EV < 36) h36_w) (hed_lt OFF_EV (by decide)).2
  let mem' := Function.update (Function.update m1 (hp_caller + 2) xv) (hp_caller + 3) yv
  have hs6 : Runs w p ω
      (.cond (.reg 12)
        (.store (.bin .add (.reg 4) (.const 2)) (.reg 13) ;;
         .store (.bin .add (.reg 4) (.const 3)) (.reg 14))
        (.store (.bin .add (.reg 4) (.const 2)) (.reg 14) ;;
         .store (.bin .add (.reg 4) (.const 3)) (.reg 13)))
      { mem := m1, regs := r4, pos := pos } .normal
      { mem := mem', regs := r4, pos := pos } 13 := by
    rw [runs_cond_iff]
    refine ⟨dir, 11, Expr.eval_reg_of_eq (st := { mem := m1, regs := r4, pos := pos }) hr_ok4.2.1,
      ?_, rfl⟩
    by_cases hdz : dir = 0
    · simp only [hdz, ↓reduceIte]
      have ha1 : Runs w p ω (.store (.bin .add (.reg 4) (.const 2)) (.reg 14))
          { mem := m1, regs := r4, pos := pos } .normal
          { mem := Function.update m1 (hp_caller + 2) ev, regs := r4, pos := pos } 5 :=
        runs_store_iff.mpr ⟨hp_caller + 2, ev,
          Expr.eval_add (Expr.eval_reg_of_eq (st := { mem := m1, regs := r4, pos := pos }) hr_ok4.1)
            (Expr.eval_const h2_w) (by omega),
          Expr.eval_reg_of_eq (st := { mem := m1, regs := r4, pos := pos }) hr_ok4.2.2.2,
          rfl, rfl, by decide⟩
      have ha2 : Runs w p ω (.store (.bin .add (.reg 4) (.const 3)) (.reg 13))
          { mem := Function.update m1 (hp_caller + 2) ev, regs := r4, pos := pos } .normal
          { mem := mem', regs := r4, pos := pos } 5 := by
        simpa [mem', xv, yv, hdz] using runs_store_iff.mpr ⟨hp_caller + 3, eu,
          Expr.eval_add (Expr.eval_reg_of_eq (st := { mem := Function.update m1 (hp_caller + 2) ev, regs := r4, pos := pos }) hr_ok4.1)
            (Expr.eval_const h3_w) hhp3_w,
          Expr.eval_reg_of_eq (st := { mem := Function.update m1 (hp_caller + 2) ev, regs := r4, pos := pos }) hr_ok4.2.2.1,
          rfl, rfl, by decide⟩
      exact runs_seq_normal ha1 ha2
    · simp only [hdz, ↓reduceIte]
      have ha1 : Runs w p ω (.store (.bin .add (.reg 4) (.const 2)) (.reg 13))
          { mem := m1, regs := r4, pos := pos } .normal
          { mem := Function.update m1 (hp_caller + 2) eu, regs := r4, pos := pos } 5 :=
        runs_store_iff.mpr ⟨hp_caller + 2, eu,
          Expr.eval_add (Expr.eval_reg_of_eq (st := { mem := m1, regs := r4, pos := pos }) hr_ok4.1)
            (Expr.eval_const h2_w) (by omega),
          Expr.eval_reg_of_eq (st := { mem := m1, regs := r4, pos := pos }) hr_ok4.2.2.1,
          rfl, rfl, by decide⟩
      have ha2 : Runs w p ω (.store (.bin .add (.reg 4) (.const 3)) (.reg 14))
          { mem := Function.update m1 (hp_caller + 2) eu, regs := r4, pos := pos } .normal
          { mem := mem', regs := r4, pos := pos } 5 := by
        simpa [mem', xv, yv, hdz] using runs_store_iff.mpr ⟨hp_caller + 3, ev,
          Expr.eval_add (Expr.eval_reg_of_eq (st := { mem := Function.update m1 (hp_caller + 2) eu, regs := r4, pos := pos }) hr_ok4.1)
            (Expr.eval_const h3_w) hhp3_w,
          Expr.eval_reg_of_eq (st := { mem := Function.update m1 (hp_caller + 2) eu, regs := r4, pos := pos }) hr_ok4.2.2.2,
          rfl, rfl, by decide⟩
      exact runs_seq_normal ha1 ha2
  refine ⟨r4, runs_seq_normal hs0 (runs_seq_normal hs1 (runs_seq_normal hs2
    (runs_seq_normal hs3 (runs_seq_normal hs4 (runs_seq_normal hs5 hs6))))),
    hr_ok4.1, ?_, ?_, ?_, ?_⟩ <;> simp [r4, r3, r2, r1, Function.update_of_ne, hr17]

private theorem lctPathMin_ne_runs {w h L P b u v hp_caller space pos : ℕ}
    {F : MathForest} {x₀ : LctConc} (p : Program) (lp : LctProcs) (mem₀ : ℕ → ℕ)
    (hp_base : LctBaseOk w h L P p lp)
    (hp_sp : ∃ spB, lp.splay = SplayProcs.atBase spB)
    (hexpose_eq : p.procs[lp.expose]? = some (exposeBody lp.splay))
    (hreroot_eq : p.procs[lp.reroot]? = some (lctRerootBody lp))
    (hrep₀ : LctMemRep w h L P b F x₀ mem₀)
    (hu : u < F.n) (hv : v < F.n) (hne : u ≠ v) (hsc : F.SameComp u v)
    (hfoot : ∀ a, lctFoot b x₀ a → a < hp_caller)
    (hz₀ : ZeroFrom mem₀ hp_caller)
    (hhp_bd : hp_caller + lctPhi L mem₀ b F.n + C_PATHMIN_OP L * (Nat.log 2 (F.n + 2) + 1) +
      7000 * (L + 1) * (F.n + 2) + 2 * L + 5 < 2 ^ w)
    (hsp_ge : lctPhi L mem₀ b F.n + C_PATHMIN_OP L * (Nat.log 2 (F.n + 2) + 1) + 2 * L + 5 ≤ space)
    (r_in : ℕ → ℕ)
    (hr_in : r_in 4 = hp_caller ∧ r_in 5 = L ∧ r_in 6 = b ∧ r_in 7 = lctNodesBase b ∧
      r_in 8 = u + 1 ∧ r_in 9 = v + 1)
    (ω : ℕ → Bool) :
    let nb := lctNodesBase b
    let hp_eff := hp_caller + (4 + 2 * L)
    let mem₁ := Function.update mem₀ (nb - 1) hp_eff
    ∃ hp_final st' c x' hit,
      Runs w p ω (lctPathMinElseBody lp)
        { mem := mem₁, regs := r_in, pos := pos } .normal st' c ∧
      st'.regs 6 = b ∧
      st'.mem (b + LCT_HDR_HP) + 1 = hp_final ∧
      hp_final < 2 ^ w ∧
      LctMemRep w h L P b F x' st'.mem ∧
      (lctDSRep w h L P).Respects (lctFoot b x₀) hp_caller space mem₀ hp_final b x' st'.mem ∧
      F.pathMin u v = some hit ∧
      st'.mem hp_caller = 1 ∧
      st'.mem (hp_caller + 1) = hit.eid ∧
      st'.mem (hp_caller + 2) = hit.x ∧
      st'.mem (hp_caller + 3) = hit.y ∧
      Valid st'.mem (hp_caller + 4) h L ∧
      Valid st'.mem (hp_caller + 4 + L) h L ∧
      fixRat st'.mem (hp_caller + 4) h L P = hit.avail ∧
      fixRat st'.mem (hp_caller + 4 + L) h L P = hit.flow ∧
      c + 60 + (hp_final - hp_caller) + lctPhi L st'.mem b F.n ≤
        lctPhi L mem₀ b F.n + C_PATHMIN_OP L * (Nat.log 2 (F.n + 2) + 1) ∧
      RerootRoots mem₀ st'.mem b F u := by
  dsimp only
  set nb := lctNodesBase b
  set cap := lctCap F.n
  set hp_eff := hp_caller + (4 + 2 * L)
  set mem₁ := Function.update mem₀ (nb - 1) hp_eff
  have hlog_pos : 1 ≤ Nat.log 2 (F.n + 2) + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hrexp_le_pm : C_REROOT_OP L + C_EXPOSE_OP L ≤ C_PATHMIN_OP L := by
    unfold C_REROOT_OP C_EXPOSE_OP C_PATHMIN_OP; omega
  have hrexp_mul_le : (C_REROOT_OP L + C_EXPOSE_OP L) * (Nat.log 2 (F.n + 2) + 1) ≤
      C_PATHMIN_OP L * (Nat.log 2 (F.n + 2) + 1) :=
    Nat.mul_le_mul_right _ hrexp_le_pm
  have hroom_re : (hp_caller + (4 + 2 * L)) + lctPhi L mem₀ b F.n +
      (C_REROOT_OP L + C_EXPOSE_OP L) * (Nat.log 2 (F.n + 2) + 1) +
      7000 * (L + 1) * (F.n + 2) + 1 < 2 ^ w :=
    pathMin_room_re_arith hrexp_mul_le hhp_bd
  have hhpeff_w : hp_eff < 2 ^ w := room_lt_pow6_tail (by omega : 4 + 2 * L ≤ 2 * L + 5) hhp_bd
  have hhp_ge : hp_caller ≤ hp_eff := Nat.le_add_right _ _
  have hhp_w : hp_caller < 2 ^ w := lt_of_le_of_lt hhp_ge hhpeff_w
  rcases arenaHi_bounds hrep₀ hfoot hhp_w with
    ⟨harena_hp, _hnb_w, _hb_w, h36_w, hstr_w, _hbh_lt, hbh_hp, _hfn1_w, hnode_lt⟩
  have hL_w : L < 2 ^ w := by omega
  rcases rerootExpose_runs (pos := pos) p lp mem₀ hp_base hp_sp hexpose_eq hrep₀ hu hv hfoot
      hz₀ hhp_ge hroom_re ω with
    ⟨st₁, st₂, c_re, c_exp, l₂, rest₂, x₂, hrun_re, hrun_exp, hi₂, hsafe₂, _hz₂, hle₂, hpp₂,
      _hrev₂, _hht₂, _hev₂, hhead_same, hlast_v, hcost_re_exp, hrep₂, hx2_trees, hz0_safe, hpf0,
      hag0, harena_eff, _hfin_lt2, _, hmove_re⟩
  let rB := Function.update r_in 12 0
  have hcall_re : Runs w p ω (.call 12 lp.reroot [.reg 7, .reg 8])
      { mem := mem₁, regs := r_in, pos := pos } .normal
      { mem := st₁.mem, regs := rB, pos := st₁.pos } (2 + c_re + 1) :=
    runs_call_iff.mpr ⟨[nb, u + 1], lctRerootBody lp, .returned 0, st₁, c_re,
      by simp [evalArgs, Expr.eval, hr_in], hreroot_eq, hrun_re, rfl, by cases st₁; rfl, rfl⟩
  let rC := Function.update rB 12 (v + 1)
  have hcall_exp : Runs w p ω (.call 12 lp.expose [.reg 7, .reg 9])
      { mem := st₁.mem, regs := rB, pos := st₁.pos } .normal
      { mem := st₂.mem, regs := rC, pos := st₂.pos } (2 + c_exp + 1) := by
    have hargs : rB 7 = nb ∧ rB 9 = v + 1 := by simp [rB, Function.update_of_ne, hr_in]
    exact runs_call_iff.mpr ⟨[nb, v + 1], exposeBody lp.splay, .returned (v + 1), st₂, c_exp,
      by simp [evalArgs, Expr.eval, hargs], hexpose_eq, hrun_exp, rfl, by cases st₂; rfl, rfl⟩
  let t₂ := AuxTree.node (v + 1) l₂ .leaf
  have ht2_mem : t₂ ∈ x₂.trees := by rw [hx2_trees]; simp [t₂]
  rcases hrep₂.pathMin_eq ht2_mem hu hv hne hpp₂ (hhead_same hsc) hlast_v with
    ⟨hit, rmin, smin, hpm_eq, _hmin_has, hmin_first, hrmin_mem, hrmin_steps, ⟨ed', hmatch, hfwd⟩, hhit_eq⟩
  let ed := nodeField st₂.mem nb (v + 1) OFF_MIN1_FIRST
  have hed_eq : ed = rmin.nodeId := hmin_first
  have hed_mem : ed ∈ t₂.toList := hed_eq ▸ hrmin_mem
  have hed_bd : 1 ≤ ed ∧ ed ≤ cap :=
    (SplayForestOk.trees_ok hi₂.sf t₂ (by simp [t₂])).2.2.nodup_perm_mem hed_mem
  let rD := Function.update rC 11 ed
  let st_st2 : State := { mem := st₂.mem, regs := rC, pos := st₂.pos }
  have hrC_ok : rC 4 = hp_caller ∧ rC 5 = L ∧ rC 6 = b ∧ rC 7 = nb ∧ rC 9 = v + 1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [rC, rB, Function.update_of_ne, hr_in]
  have hload_ed : Runs w p ω (.assign 11 (.load (.bin .add (.bin .add (.reg 7)
      (.bin .mul (.const NODE_STRIDE) (.reg 9))) (.const OFF_MIN1_FIRST)))) st_st2 .normal
      { st_st2 with regs := rD } 9 := by
    refine runs_assign_iff.mpr ⟨ed, ?_, rfl, rfl, by decide⟩
    have hv_bd := hnode_lt (v + 1) OFF_MIN1_FIRST (by omega)
      (by unfold lctCap; omega) (by decide)
    have hmul_lt : NODE_STRIDE * (v + 1) < 2 ^ w :=
      lt_of_le_of_lt (Nat.le_add_left _ _) (lt_of_le_of_lt (Nat.le_add_right _ _) hv_bd.2)
    have e1 := Expr.eval_bin (op := .mul) (Expr.eval_const hstr_w)
      (Expr.eval_reg_of_eq (st := st_st2) (r := 9) hrC_ok.2.2.2.2)
      (by simpa [BinOp.eval] using hmul_lt)
    have e2 := Expr.eval_add (Expr.eval_reg_of_eq (st := st_st2) (r := 7) hrC_ok.2.2.2.1) e1
      (lt_of_le_of_lt (Nat.le_add_right _ _) hv_bd.2)
    have e3 := Expr.eval_add e2 (Expr.eval_const (lt_trans (by decide : OFF_MIN1_FIRST < 36) h36_w))
      hv_bd.2
    rw [Expr.eval_load e3]; rfl
  have hroom₂ : st₂.mem (nb - 1) + 6000 * (L + 1) * (F.n + 2) < 2 ^ w :=
    pathMin_room2_arith hcost_re_exp hle₂ hrexp_mul_le
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide : 6000 ≤ 7000))) hhp_bd
  have hhp_sp : st₂.mem (nb - 1) + K_PUSH_PATH L * (t₂.depthOf ed + 1) +
      8 * L * t₂.depthOf ed < 2 ^ w :=
    splay_lct_tree_headroom_lt hi₂.sf rfl (by dsimp only [t₂]; simp) hed_mem hroom₂
  have harena_eff_nb : nb + NODE_STRIDE * (cap + 1) ≤ hp_eff := by
    unfold lctArenaHi at harena_eff; exact harena_eff
  rcases splayForest_lct_runs p lp.splay mem₁ st₂.mem nb cap hp_eff st₂.pos
      hp_base.splay_hasAt hp_sp hp_base.splay_ok hz0_safe harena_eff_nb hsafe₂ hi₂.sf
      (List.Perm.refl (t₂ :: rest₂)) hed_mem hhp_sp ω with
    ⟨st₃, c_sp, t₃, hrun_sp, hsf₃, hsafe₃, hr3_root, ht3_perm, hev₃, hsteps₃, hrev₃, hht₃,
      hpp₃, hout₃, hstat₃, hfr₃, hphi₃_all⟩
  let rE := Function.update rD 12 ed
  have hstD_args : rD 7 = nb ∧ rD 11 = ed := by simp [rD, hrC_ok, Function.update_of_ne]
  have hcall_sp : Runs w p ω (.call 12 lp.splay.splay [.reg 7, .reg 11])
      { st_st2 with regs := rD } .normal { mem := st₃.mem, regs := rE, pos := st₃.pos }
      (2 + c_sp + 1) :=
    runs_call_iff.mpr ⟨[nb, ed], splayBody lp.splay, .returned ed, st₃, c_sp,
      by simp [evalArgs, Expr.eval, hstD_args], hp_base.splay_ok.splay_eq, hrun_sp, rfl,
      by cases st₃; rfl, rfl⟩
  have ht2_free : t₂.rootId ∉ x₀.freeEdges := fun hfm => by
    have h1 := (hi₂.freeNodeOk t₂.rootId hfm).1
    dsimp only [t₂, AuxTree.rootId] at h1
    omega
  rcases LctExposeInvs.of_splay hi₂ (List.Perm.refl (t₂ :: rest₂)) ht2_free hsf₃ hev₃
      hsteps₃ ht3_perm (by simpa [hr3_root] using hpp₃) hout₃ hstat₃ hfr₃ with
    ⟨hi₃, hpar₃, _, hvs₃_fn, hheavy₃⟩
  have hphi3_le : c_sp + (st₃.mem (nb - 1) - st₂.mem (nb - 1)) + lctPhi L st₃.mem b F.n ≤
      lctPhi L st₂.mem b F.n + 3 * K_SPLAY_STEP L * (Nat.log 2 (F.n + 2) + 1) + C_SPLAY_CONST L := by
    have hlog_t2 : t₂.rank (lctVSize st₂.mem nb cap) ≤ Nat.log 2 (F.n + 2) + 1 :=
      treeRank_le_log_of_invs hi₂.sf hi₂.subdivOk.1 hi₂.auxPathOk (by dsimp only [t₂]; simp)
    have hmul_rk : 3 * K_SPLAY_STEP L * t₂.rank (lctVSize st₂.mem nb cap) ≤
        3 * K_SPLAY_STEP L * (Nat.log 2 (F.n + 2) + 1) :=
      Nat.mul_le_mul_left _ hlog_t2
    have hvs₃_eq : lctVSize st₃.mem nb cap = lctVSize st₂.mem nb cap := funext hvs₃_fn
    have hsp := (hphi₃_all (lctVSize st₂.mem nb cap)).2.2
    nth_rw 1 [← hvs₃_eq] at hsp
    unfold lctPhi; rw [hheavy₃] at *
    dsimp only [nb, cap] at hsp hmul_rk ⊢
    omega
  have hphi_tot := pathMin_phi_arith hcost_re_exp hphi3_le hle₂ hfr₃.2.2.1
  have hle₃ : hp_eff ≤ st₃.mem (nb - 1) := le_trans hle₂ hfr₃.2.2.1
  have ht3_ne : t₃ ≠ .leaf := (hsf₃.trees_ok t₃ (by simp)).1
  have ht3_match := (hsf₃.trees_ok t₃ (by simp)).2.2
  have ht3_nd : t₃.toList.Nodup :=
    list_nodup_of_flatMap_nodup
      ((SplayForestOk.perm hsf₃).nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h)))
      (by simp)
  have hrmin_steps₃ : rmin ∈ evalMemSteps st₃.mem nb h L t₃ false 0 := by
    rw [hsteps₃]; exact hrmin_steps
  have hown_ed : nodeOwnRawStep st₃.mem nb h L ed = some rmin := by
    simpa [hr3_root] using evalMemSteps_root_unique ht3_match ht3_nd ht3_ne
      (by rw [hr3_root]; exact hrev₃) (by rw [hr3_root]; exact hht₃)
      hrmin_steps₃ (by rw [hr3_root, hed_eq])
  have hns_ed : NodeNonStructOk h L (nb + NODE_STRIDE * (cap + 1)) (st₃.mem (nb - 1)) nb st₃.mem ed := by
    simpa [hr3_root] using TreeMemMatch.nodeNonStructOk ht3_match (AuxTree.rootId_mem_toList ht3_ne)
  have hhe_nz : nodeField st₃.mem nb ed OFF_HASE ≠ 0 := by
    intro h0
    simp [nodeOwnRawStep, h0] at hown_ed
  have hhe_one : nodeField st₃.mem nb ed OFF_HASE = 1 := eq_one_of_le_one_ne_zero hns_ed.1 hhe_nz
  obtain ⟨kfl, kaf, _kab, _kcf, _kcb⟩ := hns_ed.2.2.1 hhe_one
  have hown_vals :
      rmin.eid = nodeField st₃.mem nb ed OFF_EID ∧
      rmin.eu = nodeField st₃.mem nb ed OFF_EU ∧
      rmin.ev = nodeField st₃.mem nb ed OFF_EV ∧
      rmin.fwd = decide (nodeField st₃.mem nb ed OFF_DIR ≠ 0) ∧
      rmin.flow = intVal st₃.mem (nodeField st₃.mem nb ed OFF_FLOW_PTR) h L ∧
      rmin.dirAvail = intVal st₃.mem (nodeField st₃.mem nb ed OFF_AF_PTR) h L := by
    unfold nodeOwnRawStep at hown_ed
    simp only [hhe_nz, ↓reduceIte, Option.some.injEq] at hown_ed
    subst hown_ed
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
    simp only [RawStep.dirAvail]
    cases decide (nodeField st₃.mem nb ed OFF_DIR ≠ 0) <;> simp
  have hed_lt : ∀ off < NODE_STRIDE, nb + NODE_STRIDE * ed + off < hp_caller ∧
      nb + NODE_STRIDE * ed + off < 2 ^ w := fun off hoff =>
    hnode_lt ed off hed_bd.1 hed_bd.2 hoff
  have hbase_lt_w : nb + NODE_STRIDE * ed < 2 ^ w := (hed_lt 0 (by decide)).2
  let baseEd := nb + NODE_STRIDE * ed
  let rF := Function.update rE 17 baseEd
  have hstE_regs : rE 4 = hp_caller ∧ rE 5 = L ∧ rE 6 = b ∧ rE 7 = nb ∧ rE 11 = ed := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [rE, rD, hrC_ok, Function.update_of_ne]
  have h_ed17 : Runs w p ω (.assign 17 (.bin .add (.reg 7) (.bin .mul (.const NODE_STRIDE) (.reg 11))))
      { mem := st₃.mem, regs := rE, pos := st₃.pos } .normal
      { mem := st₃.mem, regs := rF, pos := st₃.pos } 6 := by
    refine runs_assign_iff.mpr ⟨baseEd, ?_, rfl, rfl, by decide⟩
    have em := Expr.eval_bin (op := .mul) (Expr.eval_const hstr_w)
      (Expr.eval_reg_of_eq (st := { mem := st₃.mem, regs := rE, pos := st₃.pos }) (r := 11)
        hstE_regs.2.2.2.2)
      (by simpa [BinOp.eval] using lt_of_le_of_lt (Nat.le_add_left _ _) hbase_lt_w)
    exact Expr.eval_add
      (Expr.eval_reg_of_eq (st := { mem := st₃.mem, regs := rE, pos := st₃.pos }) (r := 7)
        hstE_regs.2.2.2.1) em hbase_lt_w
  have hrF_4 : rF 4 = hp_caller := by simp [rF, hstE_regs, Function.update_of_ne]
  have hrF_17 : rF 17 = baseEd := Function.update_self _ _ _
  rcases pathMin_write4_runs hrF_4 hrF_17 (lt_trans (by decide) h36_w)
      (lt_trans (by decide) h36_w) (lt_trans (by decide) h36_w) h36_w
      (by omega : hp_caller + 3 < 2 ^ w) hed_lt with
    ⟨rG, hwrite4, hrG_4, hrG_5, hrG_6, hrG_7, hrG_17⟩
  have hrG_5' : rG 5 = L := by rw [hrG_5]; simp [rF, hstE_regs, Function.update_of_ne]
  have hrG_6' : rG 6 = b := by rw [hrG_6]; simp [rF, hstE_regs, Function.update_of_ne]
  let eid := nodeField st₃.mem nb ed OFF_EID
  let dir := nodeField st₃.mem nb ed OFF_DIR
  let eu := nodeField st₃.mem nb ed OFF_EU
  let ev := nodeField st₃.mem nb ed OFF_EV
  let xv := if dir = 0 then ev else eu
  let yv := if dir = 0 then eu else ev
  let m4 := Function.update (Function.update (Function.update (Function.update st₃.mem hp_caller 1)
    (hp_caller + 1) eid) (hp_caller + 2) xv) (hp_caller + 3) yv
  have hm4_outside : ∀ a, a < hp_caller ∨ hp_caller + 4 ≤ a → m4 a = st₃.mem a := fun a ha =>
    update4_eq_outside ha
  let afPtr := nodeField st₃.mem nb ed OFF_AF_PTR
  let flPtr := nodeField st₃.mem nb ed OFF_FLOW_PTR
  have hm4_af : nodeField m4 nb ed OFF_AF_PTR = afPtr :=
    hm4_outside _ (Or.inl (hed_lt OFF_AF_PTR (by decide)).1)
  have hm4_fl : nodeField m4 nb ed OFF_FLOW_PTR = flPtr :=
    hm4_outside _ (Or.inl (hed_lt OFF_FLOW_PTR (by decide)).1)
  have hk_all : C_REROOT_OP L + C_EXPOSE_OP L + 3 * K_SPLAY_STEP L +
      C_SPLAY_CONST L + 36 * L + 500 ≤ C_PATHMIN_OP L := by
    unfold C_REROOT_OP C_EXPOSE_OP C_PATHMIN_OP K_SPLAY_STEP K_DOUBLE K_ROTATE K_PULL
      K_PUSH_PATH K_PUSH_DOWN C_SPLAY_CONST
    omega
  have hk_mul : (C_REROOT_OP L + C_EXPOSE_OP L) * (Nat.log 2 (F.n + 2) + 1) +
      3 * K_SPLAY_STEP L * (Nat.log 2 (F.n + 2) + 1) +
      C_SPLAY_CONST L + 36 * L + 500 ≤ C_PATHMIN_OP L * (Nat.log 2 (F.n + 2) + 1) :=
    pathMin_hk_mul_arith hk_all hlog_pos
  have hfin_bounds := pathMin_cost_arith hphi_tot hle₃ (by exact Nat.le_refl _) hk_mul hsp_ge hhp_bd
  have hfin_lt₃ : st₃.mem (nb - 1) + 1 < 2 ^ w := hfin_bounds.1
  have hfin_sp₃ : st₃.mem (nb - 1) + 1 ≤ hp_caller + space := hfin_bounds.2.1
  have hst3_hp_w : st₃.mem (nb - 1) < 2 ^ w := lt_trans (Nat.lt_succ_self _) hfin_lt₃
  have haf_disj := SafeMem.ptr_disjoint_ans hfoot hpf0 (by rw [hrep₀.2.2.2.2.1]; exact hsafe₃)
    hed_bd.1 (by rw [hrep₀.2.2.2.2.1]; exact hed_bd.2) (by decide : OFF_AF_PTR ∈ ptrOffs)
  have hfl_disj := SafeMem.ptr_disjoint_ans hfoot hpf0 (by rw [hrep₀.2.2.2.2.1]; exact hsafe₃)
    hed_bd.1 (by rw [hrep₀.2.2.2.2.1]; exact hed_bd.2) (by decide : OFF_FLOW_PTR ∈ ptrOffs)
  dsimp only at haf_disj hfl_disj
  have haf_no_ov_full : hp_eff ≤ afPtr ∨ afPtr + L ≤ hp_caller := by
    rcases haf_disj with h0 | hhi | hlo
    · exact absurd h0 kaf.1
    · exact Or.inl hhi
    · exact Or.inr hlo
  have hfl_no_ov_full : hp_eff ≤ flPtr ∨ flPtr + L ≤ hp_caller := by
    rcases hfl_disj with h0 | hhi | hlo
    · exact absurd h0 kfl.1
    · exact Or.inl hhi
    · exact Or.inr hlo
  have haf_lt_w : afPtr + L < 2 ^ w := lt_of_le_of_lt kaf.2.2.1 hst3_hp_w
  have hfl_lt_w : flPtr + L < 2 ^ w := lt_of_le_of_lt kfl.2.2.1 hst3_hp_w
  let r15a := Function.update rG 15 afPtr
  have hload_af : Runs w p ω (.assign 15 (fieldLoadExpr 17 OFF_AF_PTR))
      { mem := m4, regs := rG, pos := st₃.pos } .normal
      { mem := m4, regs := r15a, pos := st₃.pos } 5 := by
    simpa [hm4_af, r15a] using runs_fieldLoad_17 (mem := m4) (rd := 15) hrG_17
      (lt_trans (by decide : OFF_AF_PTR < 36) h36_w) (hed_lt OFF_AF_PTR (by decide)).2
  let r13a := Function.update r15a 13 (hp_caller + 4)
  have hset13 : Runs w p ω (.assign 13 (.bin .add (.reg 4) (.const 4)))
      { mem := m4, regs := r15a, pos := st₃.pos } .normal
      { mem := m4, regs := r13a, pos := st₃.pos } 4 := by
    refine runs_assign_iff.mpr ⟨hp_caller + 4, ?_, rfl, rfl, by decide⟩
    have hr4_eq : r15a 4 = hp_caller := by simp [r15a, Function.update_of_ne, hrG_4]
    exact Expr.eval_add (Expr.eval_reg_of_eq (st := { mem := m4, regs := r15a, pos := st₃.pos }) hr4_eq)
      (Expr.eval_const (lt_trans (by decide : 4 < 36) h36_w)) (by omega)
  have hr13a_ok : r13a 15 = afPtr ∧ r13a 13 = hp_caller + 4 ∧ r13a 5 = L ∧ r13a 6 = b ∧
      r13a 17 = baseEd := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      (try dsimp only [baseEd]) <;>
      simp [r13a, r15a, Function.update_of_ne, hrG_5', hrG_6', hrG_17]
  have haf_disj1 : hp_caller + 4 + L ≤ afPtr ∨ afPtr + L ≤ hp_caller + 4 := by
    rcases haf_no_ov_full with hhi | hlo
    · exact Or.inl (by dsimp only [hp_eff] at hhi; omega)
    · exact Or.inr (by omega)
  have haf_args_w : ∀ a ∈ [afPtr, hp_caller + 4, L], a < 2 ^ w := by
    intro a ha; simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> omega
  have hpre_cp1 : (copyWordsContract w).pre [afPtr, hp_caller + 4, L] m4 :=
    ⟨afPtr, hp_caller + 4, L, rfl, lt_trans (by decide) h36_w, Nat.le_of_lt haf_lt_w,
      by omega, haf_disj1⟩
  rcases hp_base.copyWords_ok [afPtr, hp_caller + 4, L] m4 st₃.pos ω haf_args_w hpre_cp1 with
    ⟨body1, hcp_eq1, o1, st_cp1, c_cp1, hrun_cp1, hpost1, hc_cp1⟩
  rcases hpost1 with ⟨_, _, _, hcp1_arg, _, hcp1_vals, hcp1_out⟩
  cases hcp1_arg
  let r_after1 := Function.update r13a 16 o1.value
  have hcall_cp1 : Runs w p ω (.call 16 lp.copyWords [.reg 15, .reg 13, .reg 5])
      { mem := m4, regs := r13a, pos := st₃.pos } .normal
      { mem := st_cp1.mem, regs := r_after1, pos := st_cp1.pos } (3 + c_cp1 + 1) :=
    runs_call_iff.mpr ⟨[afPtr, hp_caller + 4, L], body1, o1, st_cp1, c_cp1,
      by simp [evalArgs, Expr.eval, hr13a_ok], hcp_eq1, hrun_cp1, rfl, by cases st_cp1; rfl, rfl⟩
  have hcp1_fl : nodeField st_cp1.mem nb ed OFF_FLOW_PTR = flPtr := by
    rw [← hm4_fl]
    exact hcp1_out _ (Or.inl (lt_trans (hed_lt OFF_FLOW_PTR (by decide)).1 (by omega : hp_caller < hp_caller + 4)))
  have hr_after1_17 : r_after1 17 = baseEd := by simp [r_after1, Function.update_of_ne, hr13a_ok]
  let r15b := Function.update r_after1 15 flPtr
  have hload_fl : Runs w p ω (.assign 15 (fieldLoadExpr 17 OFF_FLOW_PTR))
      { mem := st_cp1.mem, regs := r_after1, pos := st_cp1.pos } .normal
      { mem := st_cp1.mem, regs := r15b, pos := st_cp1.pos } 5 := by
    simpa [hcp1_fl, r15b] using runs_fieldLoad_17 (mem := st_cp1.mem) (rd := 15) hr_after1_17
      (lt_trans (by decide : OFF_FLOW_PTR < 36) h36_w) (hed_lt OFF_FLOW_PTR (by decide)).2
  let r14b := Function.update r15b 14 (hp_caller + 4 + L)
  have hr15b_ok : r15b 13 = hp_caller + 4 ∧ r15b 5 = L := by
    refine ⟨?_, ?_⟩ <;> simp [r15b, r_after1, Function.update_of_ne, hr13a_ok]
  have hset14 : Runs w p ω (.assign 14 (.bin .add (.reg 13) (.reg 5)))
      { mem := st_cp1.mem, regs := r15b, pos := st_cp1.pos } .normal
      { mem := st_cp1.mem, regs := r14b, pos := st_cp1.pos } 4 :=
    runs_assign_iff.mpr ⟨hp_caller + 4 + L,
      Expr.eval_add (Expr.eval_reg_of_eq (st := { mem := st_cp1.mem, regs := r15b, pos := st_cp1.pos }) hr15b_ok.1)
        (Expr.eval_reg_of_eq (st := { mem := st_cp1.mem, regs := r15b, pos := st_cp1.pos }) hr15b_ok.2)
        (by omega), rfl, rfl, by decide⟩
  have hr14b_ok : r14b 15 = flPtr ∧ r14b 14 = hp_caller + 4 + L ∧ r14b 5 = L ∧ r14b 6 = b := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [r14b, r15b, r_after1, Function.update_of_ne, hr13a_ok]
  have hfl_disj2 : hp_caller + 4 + L + L ≤ flPtr ∨ flPtr + L ≤ hp_caller + 4 + L := by
    rcases hfl_no_ov_full with hhi | hlo
    · exact Or.inl (by dsimp only [hp_eff] at hhi; omega)
    · exact Or.inr (by omega)
  have hfl_args_w : ∀ a ∈ [flPtr, hp_caller + 4 + L, L], a < 2 ^ w := by
    intro a ha; simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> omega
  have hpre_cp2 : (copyWordsContract w).pre [flPtr, hp_caller + 4 + L, L] st_cp1.mem :=
    ⟨flPtr, hp_caller + 4 + L, L, rfl, lt_trans (by decide) h36_w, Nat.le_of_lt hfl_lt_w,
      by omega, hfl_disj2⟩
  rcases hp_base.copyWords_ok [flPtr, hp_caller + 4 + L, L] st_cp1.mem st_cp1.pos ω hfl_args_w hpre_cp2 with
    ⟨body2, hcp_eq2, o2, st_cp2, c_cp2, hrun_cp2, hpost2, hc_cp2⟩
  rcases hpost2 with ⟨_, _, _, hcp2_arg, _, hcp2_vals, hcp2_out⟩
  cases hcp2_arg
  let r_after2 := Function.update r14b 16 o2.value
  have hcall_cp2 : Runs w p ω (.call 16 lp.copyWords [.reg 15, .reg 14, .reg 5])
      { mem := st_cp1.mem, regs := r14b, pos := st_cp1.pos } .normal
      { mem := st_cp2.mem, regs := r_after2, pos := st_cp2.pos } (3 + c_cp2 + 1) :=
    runs_call_iff.mpr ⟨[flPtr, hp_caller + 4 + L, L], body2, o2, st_cp2, c_cp2,
      by simp [evalArgs, Expr.eval, hr14b_ok], hcp_eq2, hrun_cp2, rfl, by cases st_cp2; rfl, rfl⟩
  have hag_fin : ∀ a, a < hp_caller ∨ hp_eff ≤ a → st_cp2.mem a = st₃.mem a := fun a ha => by
    have hha1 : a < hp_caller + 4 + L ∨ hp_caller + 4 + L + L ≤ a := by
      rcases ha with hl | hr
      · exact Or.inl (by omega)
      · exact Or.inr (by dsimp only [hp_eff] at hr; omega)
    have hha2 : a < hp_caller + 4 ∨ hp_caller + 4 + L ≤ a := by
      rcases ha with hl | hr
      · exact Or.inl (by omega)
      · exact Or.inr (by dsimp only [hp_eff] at hr; omega)
    have hha3 : a < hp_caller ∨ hp_caller + 4 ≤ a := by
      rcases ha with hl | hr
      · exact Or.inl hl
      · exact Or.inr (by dsimp only [hp_eff] at hr; omega)
    rw [hcp2_out a hha1, hcp1_out a hha2, hm4_outside a hha3]
  have hnb1_lt_hp : nb - 1 < hp_caller := by
    have hpos : 1 ≤ nb := by dsimp only [nb, lctNodesBase, LCT_HDR_SIZE]; omega
    have hle : nb ≤ hp_caller :=
      le_trans (Nat.le_add_right _ _) (by simpa [nb, lctArenaHi] using harena_hp)
    omega
  have hmem_fin_hp : st_cp2.mem (b + LCT_HDR_HP) = st₃.mem (nb - 1) := by
    rw [hbh_hp]; exact hag_fin (nb - 1) (Or.inl hnb1_lt_hp)
  have hrun_ne :=
    runs_seq_normal hcall_re (runs_seq_normal hcall_exp (runs_seq_normal hload_ed
      (runs_seq_normal hcall_sp (runs_seq_normal h_ed17 (runs_seq_normal hwrite4
        (runs_seq_normal hload_af (runs_seq_normal hset13 (runs_seq_normal hcall_cp1
          (runs_seq_normal hload_fl (runs_seq_normal hset14 hcall_cp2))))))))))
  rcases exitOp_rep hrep₀ hfoot hhp_ge rfl hrep₀.valid hrep₀.edgeFits hz0_safe hpf0 hag0 hsafe₃
      hi₃.sf hi₃.hdrN hi₃.hdrCap hi₃.hdrL hi₃.hdrP hrep₀.edgeMap_snd_perm hrep₀.slots_perm
      hi₃.freeChain hi₃.freeNodeOk hi₃.vertexOk hi₃.edgeOk hi₃.auxPathOk hi₃.subdivOk
      hfin_lt₃ hfin_sp₃ hag_fin with
    ⟨hrep_fin, hresp_fin, hphi_fin⟩
  have hcost_fin := pathMin_cost_arith hphi_tot hle₃
    (pathMin_ctot_arith hc_cp1 hc_cp2) hk_mul hsp_ge hhp_bd
  have hstep_hit : hit.eid = rmin.eid ∧ hit.x = (if rmin.fwd then rmin.eu else rmin.ev) ∧
      hit.y = (if rmin.fwd then rmin.ev else rmin.eu) ∧
      hit.avail = (rmin.dirAvail : ℚ) / (2 : ℚ) ^ P ∧
      hit.flow = (rmin.flow : ℚ) / (2 : ℚ) ^ P := by
    rw [← hhit_eq]
    dsimp only [PathStep.toHit, PathStep.src, PathStep.dst, PathStep.dirAvail, RawStep.dirAvail]
    rcases hmatch with ⟨_, heid, heu, hev, _, hfl_q, haf_q, hab_q⟩
    rw [hfwd, heid, heu, hev, hfl_q]
    cases rmin.fwd <;> simp [haf_q, hab_q]
  have hm0_val : st_cp2.mem hp_caller = 1 := by
    rw [hcp2_out _ (Or.inl (pathMin_lt0_addL hp_caller L)),
      hcp1_out _ (Or.inl (pathMin_lt0_add4 hp_caller))]
    simp [m4, Function.update_of_ne]
  have hm1_val : st_cp2.mem (hp_caller + 1) = hit.eid := by
    rw [hcp2_out _ (Or.inl (pathMin_lt4_addL hp_caller 1 L (by decide))),
      hcp1_out _ (Or.inl (pathMin_lt4_add4 hp_caller 1 (by decide)))]
    simp [m4, eid, ← hown_vals.1, hstep_hit.1, Function.update_of_ne]
  have hxy_eq := pathMin_xy_eq hown_vals.2.1 hown_vals.2.2.1 hown_vals.2.2.2.1
  have hm2_val : st_cp2.mem (hp_caller + 2) = hit.x := by
    rw [hcp2_out _ (Or.inl (pathMin_lt4_addL hp_caller 2 L (by decide))),
      hcp1_out _ (Or.inl (pathMin_lt4_add4 hp_caller 2 (by decide)))]
    simp only [m4, Function.update_of_ne (Nat.ne_of_lt (Nat.add_lt_add_left (by decide : 2 < 3) hp_caller)),
      Function.update_self]
    exact hxy_eq.1.trans hstep_hit.2.1.symm
  have hm3_val : st_cp2.mem (hp_caller + 3) = hit.y := by
    rw [hcp2_out _ (Or.inl (pathMin_lt4_addL hp_caller 3 L (by decide))),
      hcp1_out _ (Or.inl (pathMin_lt4_add4 hp_caller 3 (by decide)))]
    simp only [m4, Function.update_self]
    exact hxy_eq.2.trans hstep_hit.2.2.1.symm
  have haf_src_agree : ∀ i < L, m4 (afPtr + i) = st₃.mem (afPtr + i) := fun i hi =>
    hm4_outside _ (pathMin_src_disj_4 hi haf_no_ov_full)
  have hval_af : Valid st_cp2.mem (hp_caller + 4) h L := fun i hi => by
    rw [hcp2_out _ (Or.inl (pathMin_lt4L_addL hp_caller i L hi)), hcp1_vals i hi, haf_src_agree i hi]
    exact kaf.2.2.2 i hi
  have hiv_af : fixRat st_cp2.mem (hp_caller + 4) h L P = hit.avail := by
    have hcongr : intVal st_cp2.mem (hp_caller + 4) h L = intVal st₃.mem afPtr h L :=
      intVal_congr fun i hi => by
        rw [hcp2_out _ (Or.inl (pathMin_lt4L_addL hp_caller i L hi)), hcp1_vals i hi, haf_src_agree i hi]
    unfold fixRat
    rw [hcongr, ← hown_vals.2.2.2.2.2]
    exact hstep_hit.2.2.2.1.symm
  have hfl_src_agree : ∀ i < L, st_cp1.mem (flPtr + i) = st₃.mem (flPtr + i) := fun i hi => by
    rw [hcp1_out _ (pathMin_src_disj_4L hi hfl_no_ov_full),
      hm4_outside _ (pathMin_src_disj_4 hi hfl_no_ov_full)]
  have hval_fl : Valid st_cp2.mem (hp_caller + 4 + L) h L := fun i hi => by
    rw [hcp2_vals i hi, hfl_src_agree i hi]
    exact kfl.2.2.2 i hi
  have hiv_fl : fixRat st_cp2.mem (hp_caller + 4 + L) h L P = hit.flow := by
    have hcongr : intVal st_cp2.mem (hp_caller + 4 + L) h L = intVal st₃.mem flPtr h L :=
      intVal_congr fun i hi => by rw [hcp2_vals i hi, hfl_src_agree i hi]
    unfold fixRat
    rw [hcongr, ← hown_vals.2.2.2.2.1]
    exact hstep_hit.2.2.2.2.symm
  let st_cp2_st : State := { mem := st_cp2.mem, regs := r_after2, pos := st_cp2.pos }
  have hr_after2_6 : st_cp2_st.regs 6 = b := by simp [st_cp2_st, r_after2, Function.update_of_ne, hr14b_ok]
  let hp_final := st₃.mem (nb - 1) + 1
  have hhp_fin_eq : st_cp2_st.mem (b + LCT_HDR_HP) + 1 = hp_final := by
    simp [st_cp2_st, hmem_fin_hp, hp_final]
  refine ⟨hp_final, st_cp2_st, _, _, hit, by simpa [lctPathMinElseBody] using hrun_ne,
    hr_after2_6, hhp_fin_eq, hfin_lt₃,
    hrep_fin, hresp_fin, hpm_eq, hm0_val, hm1_val, hm2_val, hm3_val, hval_af, hval_fl, hiv_af, hiv_fl,
    ?_, ?_⟩
  · change _ + 60 + (hp_final - hp_caller) + lctPhi L st_cp2.mem b F.n ≤ _
    rw [hphi_fin]
    exact hcost_fin.2.2
  · have harena_le : nb + NODE_STRIDE * (cap + 1) ≤ hp_caller := by
      simpa [nb, cap, lctArenaHi] using harena_hp
    refine hrep₀.rerootRoots_of_rootMove hu (rootMove_of_agree hmove_re fun z => ?_)
    rw [lctAuxParent_agree (mem₁ := st₃.mem)
      (fun i _ hi => (hag_fin i (Or.inl (lt_of_lt_of_le hi harena_le))).symm) z]
    exact hpar₃ z

theorem lctPathMinBody_runs {w h L P b u v hp_caller space pos : ℕ}
    {F : MathForest} {x₀ : LctConc} (p : Program) (lp : LctProcs) (mem₀ : ℕ → ℕ)
    (hp_base : LctBaseOk w h L P p lp)
    (hp_sp : ∃ spB, lp.splay = SplayProcs.atBase spB)
    (hexpose_eq : p.procs[lp.expose]? = some (exposeBody lp.splay))
    (hreroot_eq : p.procs[lp.reroot]? = some (lctRerootBody lp))
    (hrep₀ : LctMemRep w h L P b F x₀ mem₀)
    (hu : u < F.n) (hv : v < F.n) (hsc : F.SameComp u v)
    (hfoot : ∀ a, lctFoot b x₀ a → a < hp_caller)
    (hz₀ : ZeroFrom mem₀ hp_caller)
    (hhp_bd : hp_caller + lctPhi L mem₀ b F.n + C_PATHMIN_OP L * (Nat.log 2 (F.n + 2) + 1) +
      7000 * (L + 1) * (F.n + 2) + 2 * L + 5 < 2 ^ w)
    (hsp_ge : lctPhi L mem₀ b F.n + C_PATHMIN_OP L * (Nat.log 2 (F.n + 2) + 1) + 2 * L + 5 ≤ space)
    (ω : ℕ → Bool) :
    ∃ hp_final st' c x',
      Runs w p ω (lctPathMinBody lp) (startState [b, u, v, hp_caller] mem₀ pos)
        (.returned hp_final) st' c ∧
      LctMemRep w h L P b F x' st'.mem ∧
      (lctDSRep w h L P).Respects (lctFoot b x₀) hp_caller space mem₀ hp_final b x' st'.mem ∧
      (match F.pathMin u v with
        | none => st'.mem hp_caller = 0
        | some hit =>
            st'.mem hp_caller = 1 ∧
            st'.mem (hp_caller + 1) = hit.eid ∧
            st'.mem (hp_caller + 2) = hit.x ∧
            st'.mem (hp_caller + 3) = hit.y ∧
            Valid st'.mem (hp_caller + 4) h L ∧
            Valid st'.mem (hp_caller + 4 + L) h L ∧
            fixRat st'.mem (hp_caller + 4) h L P = hit.avail ∧
            fixRat st'.mem (hp_caller + 4 + L) h L P = hit.flow) ∧
      c + (hp_final - hp_caller) + lctPhi L st'.mem b F.n ≤
        lctPhi L mem₀ b F.n + C_PATHMIN_OP L * (Nat.log 2 (F.n + 2) + 1) ∧
      (u ≠ v → RerootRoots mem₀ st'.mem b F u) := by
  let nb := lctNodesBase b
  let hp_eff := hp_caller + (4 + 2 * L)
  let mem₁ := Function.update mem₀ (nb - 1) hp_eff
  have hlog_pos : 1 ≤ Nat.log 2 (F.n + 2) + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hhp_ge : hp_caller ≤ hp_eff := Nat.le_add_right _ _
  have hhpeff_w : hp_eff < 2 ^ w := room_lt_pow6_tail (by omega : 4 + 2 * L ≤ 2 * L + 5) hhp_bd
  have hhp_w : hp_caller < 2 ^ w := lt_of_le_of_lt hhp_ge hhpeff_w
  rcases arenaHi_bounds hrep₀ hfoot hhp_w with
    ⟨harena_hp, hnb_w, hb_w, h36_w, _hstr_w, hbh_lt, hbh_hp, hfn1_w, _⟩
  have hu1_w : u + 1 < 2 ^ w := by omega
  have hv1_w : v + 1 < 2 ^ w := by omega
  have hL_w : L < 2 ^ w := by omega
  have h2L_w : 2 * L < 2 ^ w := by omega
  have h42L_w : 4 + 2 * L < 2 ^ w := by omega
  let st_init := startState [b, u, v, hp_caller] mem₀ pos
  let s1 : State := { st_init with regs := Function.update st_init.regs 4 hp_caller }
  let s2 : State := { s1 with regs := Function.update s1.regs 5 L }
  let s3 : State := { s2 with regs := Function.update s2.regs 6 b }
  let s4 : State := { s3 with regs := Function.update s3.regs 7 nb }
  let s5 : State := { s4 with regs := Function.update s4.regs 8 (u + 1) }
  let s6 : State := { s5 with regs := Function.update s5.regs 9 (v + 1) }
  let s7 : State := { s6 with regs := Function.update s6.regs 10 hp_eff }
  let st_pre : State := { mem := mem₁, regs := s7.regs, pos := pos }
  have hs1 : Runs w p ω (.assign 4 (.reg 3)) st_init .normal s1 2 :=
    runs_assign_iff.mpr ⟨hp_caller, Expr.eval_reg_of_eq rfl, rfl, rfl, by decide⟩
  have hs2 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 0) (.const LCT_HDR_L)))) s1 .normal s2 5 := by
    refine runs_assign_iff.mpr ⟨L, ?_, rfl, rfl, by decide⟩
    have hadd := Expr.eval_add (Expr.eval_reg_of_eq (st := s1) (r := 0) (by simp [s1, st_init, startState]))
      (Expr.eval_const (lt_trans (by decide : LCT_HDR_L < 36) h36_w)) hbh_lt
    rw [Expr.eval_load hadd]; simp [s1, st_init, startState, hrep₀.2.2.2.2.2.2.2.2.2.2.2.1]
  have hs3 : Runs w p ω (.assign 6 (.reg 0)) s2 .normal s3 2 :=
    runs_assign_iff.mpr ⟨b, Expr.eval_reg_of_eq (st := s2) (r := 0) (by simp [s2, s1, st_init, startState]),
      rfl, rfl, by decide⟩
  have hs4 : Runs w p ω (.assign 7 (.bin .add (.reg 0) (.const LCT_HDR_SIZE))) s3 .normal s4 4 :=
    runs_assign_iff.mpr ⟨nb, Expr.eval_add
      (Expr.eval_reg_of_eq (st := s3) (r := 0) (by simp [s3, s2, s1, st_init, startState]))
      (Expr.eval_const (lt_trans (by decide : LCT_HDR_SIZE < 36) h36_w)) hnb_w, rfl, rfl, by decide⟩
  have hs5 : Runs w p ω (.assign 8 (.bin .add (.reg 1) (.const 1))) s4 .normal s5 4 :=
    runs_assign_iff.mpr ⟨u + 1, Expr.eval_add
      (Expr.eval_reg_of_eq (st := s4) (r := 1) (by simp [s4, s3, s2, s1, st_init, startState]))
      (Expr.eval_const (lt_trans (by decide : 1 < 36) h36_w)) hu1_w, rfl, rfl, by decide⟩
  have hs6 : Runs w p ω (.assign 9 (.bin .add (.reg 2) (.const 1))) s5 .normal s6 4 :=
    runs_assign_iff.mpr ⟨v + 1, Expr.eval_add
      (Expr.eval_reg_of_eq (st := s5) (r := 2) (by simp [s5, s4, s3, s2, s1, st_init, startState]))
      (Expr.eval_const (lt_trans (by decide : 1 < 36) h36_w)) hv1_w, rfl, rfl, by decide⟩
  have hs7 : Runs w p ω (.assign 10 (.bin .add (.reg 4) (.bin .add (.const 4) (.bin .mul (.const 2) (.reg 5)))))
      s6 .normal s7 8 := by
    refine runs_assign_iff.mpr ⟨hp_eff, ?_, rfl, rfl, by decide⟩
    have hr4 : s6.regs 4 = hp_caller := by simp [s6, s5, s4, s3, s2, s1, Function.update_of_ne]
    have hr5 : s6.regs 5 = L := by simp [s6, s5, s4, s3, s2, Function.update_of_ne]
    have em := Expr.eval_bin (op := .mul) (Expr.eval_const (lt_trans (by decide : 2 < 36) h36_w))
      (Expr.eval_reg_of_eq (st := s6) (r := 5) hr5) (by simpa [BinOp.eval] using h2L_w)
    have ea := Expr.eval_add (Expr.eval_const (lt_trans (by decide : 4 < 36) h36_w)) em h42L_w
    exact Expr.eval_add (Expr.eval_reg_of_eq (st := s6) (r := 4) hr4) ea hhpeff_w
  have hs8 : Runs w p ω (.store (.bin .add (.reg 0) (.const LCT_HDR_HP)) (.reg 10)) s7 .normal st_pre 5 := by
    have hadd : Expr.eval w s7 (.bin .add (.reg 0) (.const LCT_HDR_HP)) = some (nb - 1) := by
      rw [← hbh_hp]
      exact Expr.eval_add (Expr.eval_reg_of_eq (st := s7) (r := 0)
          (by simp [s7, s6, s5, s4, s3, s2, s1, st_init, startState]))
        (Expr.eval_const (lt_trans (by decide : LCT_HDR_HP < 36) h36_w)) (by omega)
    exact runs_store_iff.mpr ⟨nb - 1, hp_eff, hadd,
      Expr.eval_reg_of_eq (st := s7) (by simp [s7]), rfl, rfl, by decide⟩
  have hpre_ok : st_pre.regs 1 = u ∧ st_pre.regs 2 = v ∧
      st_pre.regs 4 = hp_caller ∧ st_pre.regs 5 = L ∧ st_pre.regs 6 = b ∧
      st_pre.regs 7 = nb ∧ st_pre.regs 8 = u + 1 ∧ st_pre.regs 9 = v + 1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [st_pre, s7, s6, s5, s4, s3, s2, s1, st_init, startState, Function.update_of_ne]
  have hcond_eq : Expr.eval w st_pre (.bin .eq (.reg 1) (.reg 2)) = some (if u = v then 1 else 0) := by
    have h1 := Expr.eval_reg_of_eq (w := w) (st := st_pre) hpre_ok.1
    have h2 := Expr.eval_reg_of_eq (w := w) (st := st_pre) hpre_ok.2.1
    have hw1 : (if u = v then 1 else 0) < 2 ^ w := by split_ifs <;> omega
    simpa [BinOp.eval] using Expr.eval_bin (op := .eq) h1 h2 (by simpa [BinOp.eval] using hw1)
  have hnb1_lt_hp : nb - 1 < hp_caller := by
    have hpos : 1 ≤ nb := by dsimp only [nb, lctNodesBase, LCT_HDR_SIZE]; omega
    have hle : nb ≤ hp_caller :=
      le_trans (Nat.le_add_right _ _) (by simpa [nb, lctArenaHi] using harena_hp)
    omega
  by_cases huv : u = v
  · subst huv
    have hnone : F.pathMin u u = none := (MathForest.pathMin_eq_none_iff hrep₀.valid hsc).2 rfl
    rcases enterOp_ready hrep₀ hfoot hz₀ hhp_ge hhpeff_w with
      ⟨hsf₁, hsafe₁, hphi₁, _hz₁, hN₁, hC₁, hL₁, hP₁, hfc₁, hvok₁, heok₁, hpok₁, hsok₁,
        hz0_safe, hpf0, hf_eq, hag0⟩
    have hfree_nd₁ : ∀ ed ∈ x₀.freeEdges, F.n + 1 ≤ ed ∧ ed ≤ lctCap F.n ∧
        AuxTree.node ed .leaf .leaf ∈ x₀.trees ∧
        nodeField mem₁ nb ed OFF_PPAR = 0 ∧ nodeField mem₁ nb ed OFF_ISV = 0 ∧
        nodeField mem₁ nb ed OFF_HASE = 0 := fun ed hed => by
      rcases hrep₀.free_ok ed hed with ⟨h1, h2, h3, h4, h5, h6⟩
      refine ⟨h1, h2, h3, ?_, ?_, ?_⟩ <;> rw [hf_eq ed h2 _ (by decide)] <;> assumption
    let mem_fin := Function.update mem₁ hp_caller 0
    have hag_fin : ∀ a, a < hp_caller ∨ hp_eff ≤ a → mem_fin a = mem₁ a := fun a ha =>
      Function.update_of_ne (by dsimp only [hp_eff] at ha; omega) 0 mem₁
    have hmem_fin_hp : mem_fin (b + LCT_HDR_HP) = hp_eff := by
      rw [hbh_hp, hag_fin _ (Or.inl hnb1_lt_hp)]
      exact Function.update_self _ _ _
    have hmem₁_hp : mem₁ (nb - 1) = hp_eff := Function.update_self _ _ _
    have hcp_lb : 2 * L + 500 ≤ C_PATHMIN_OP L := by
      unfold C_PATHMIN_OP; omega
    have hfin_lt : hp_eff + 1 < 2 ^ w := pathMin_eq_room_lt rfl hhp_bd
    have hcost_arith := pathMin_eq_cost_arith (c_tot := 2 + (5 + (2 + (4 + (4 + (4 + (8 + (5 +
      ((3 + 3 + 1) + (5 + 4 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)
      (hle := (rfl : hp_eff = hp_caller + (4 + 2 * L))) (by omega) hcp_lb hlog_pos hsp_ge
    let st_branch : State := { mem := mem_fin, regs := st_pre.regs, pos := pos }
    have hcond_run : Runs w p ω
        (.cond (.bin .eq (.reg 1) (.reg 2)) (.store (.reg 4) (.const 0)) (lctPathMinElseBody lp))
        st_pre .normal st_branch 7 := by
      rw [runs_cond_iff]
      refine ⟨1, 3, by simpa using hcond_eq, ?_, by decide⟩
      simp only [Nat.one_ne_zero, ↓reduceIte]
      exact runs_store_iff.mpr ⟨hp_caller, 0,
        Expr.eval_reg_of_eq (st := st_pre) hpre_ok.2.2.1,
        Expr.eval_const (lt_trans (by decide) h36_w), rfl, rfl, by decide⟩
    let r_end := Function.update st_pre.regs 13 hp_eff
    let st_load : State := { mem := mem_fin, regs := r_end, pos := pos }
    have hload_hp : Runs w p ω (.assign 13 (.load (.bin .add (.reg 6) (.const LCT_HDR_HP))))
        st_branch .normal st_load 5 := by
      refine runs_assign_iff.mpr ⟨hp_eff, ?_, rfl, rfl, by decide⟩
      have hadd := Expr.eval_add
        (Expr.eval_reg_of_eq (st := st_branch) (r := 6) hpre_ok.2.2.2.2.1)
        (Expr.eval_const (lt_trans (by decide : LCT_HDR_HP < 36) h36_w))
        (by rw [hbh_hp]; exact lt_trans hnb1_lt_hp hhp_w)
      rw [Expr.eval_load hadd]; exact congrArg some hmem_fin_hp
    let hp_final := hp_eff + 1
    have hret_hp : Runs w p ω (.ret (.bin .add (.reg 13) (.const 1)))
        st_load (.returned hp_final) st_load 4 :=
      runs_ret_iff.mpr ⟨hp_final,
        Expr.eval_add (Expr.eval_reg_of_eq (st := st_load) (r := 13) (by simp [st_load, r_end]))
          (Expr.eval_const (lt_trans (by decide : 1 < 36) h36_w)) hfin_lt,
        rfl, rfl, by decide⟩
    have hrun_full :=
      runs_seq_normal hs1 (runs_seq_normal hs2 (runs_seq_normal hs3 (runs_seq_normal hs4
        (runs_seq_normal hs5 (runs_seq_normal hs6 (runs_seq_normal hs7 (runs_seq_normal hs8
        (runs_seq_normal hcond_run (runs_seq_normal hload_hp hret_hp)))))))))
    have hag0' : ∀ a, a < b ∨ lctArenaHi b (lctCap F.n) ≤ a ∧ a < hp_caller → mem₁ a = mem₀ a :=
      fun a ha => hag0 a (ha.elim (fun hl => Or.inl (by unfold LCT_HDR_HP at *; omega)) (fun hr => Or.inr hr.1))
    rcases exitOp_rep hrep₀ hfoot hhp_ge rfl hrep₀.valid hrep₀.edgeFits hz0_safe hpf0 hag0' hsafe₁
        hsf₁ hN₁ hC₁ hL₁ hP₁ hrep₀.edgeMap_snd_perm hrep₀.slots_perm
        hfc₁ hfree_nd₁ hvok₁ heok₁ hpok₁ hsok₁
        (by simpa [hmem₁_hp] using hfin_lt)
        (by simpa [hmem₁_hp] using hcost_arith.1) hag_fin with
      ⟨hrep_fin, hresp_fin, hphi_fin⟩
    have hmem_zero : mem_fin hp_caller = 0 := Function.update_self _ _ _
    refine ⟨hp_final, st_load, _, _, by simpa [lctPathMinBody] using hrun_full,
      hrep_fin, by simpa [hmem₁_hp] using hresp_fin, by simpa [hnone] using hmem_zero, ?_,
      fun hne => absurd rfl hne⟩
    change _ + (hp_final - hp_caller) + lctPhi L mem_fin b F.n ≤ _
    rw [hphi_fin, hphi₁]
    exact hcost_arith.2
  · rcases lctPathMin_ne_runs (pos := pos) p lp mem₀ hp_base hp_sp hexpose_eq hreroot_eq
        hrep₀ hu hv huv hsc hfoot hz₀ hhp_bd hsp_ge st_pre.regs
        ⟨hpre_ok.2.2.1, hpre_ok.2.2.2.1, hpre_ok.2.2.2.2.1, hpre_ok.2.2.2.2.2.1,
         hpre_ok.2.2.2.2.2.2.1, hpre_ok.2.2.2.2.2.2.2⟩ ω with
      ⟨hp_final, st_branch, c_ne, x', hit, hrun_ne, hr6_branch, hhp_branch, hfin_lt,
        hrep', hresp', hpm_eq, hm0, hm1, hm2, hm3, hv1, hv2, hf1, hf2, hcost_ne, hroots_ne⟩
    have hcond_run : Runs w p ω
        (.cond (.bin .eq (.reg 1) (.reg 2)) (.store (.reg 4) (.const 0)) (lctPathMinElseBody lp))
        st_pre .normal st_branch (3 + c_ne + 1) := by
      rw [runs_cond_iff]
      refine ⟨0, c_ne, by simpa [huv] using hcond_eq, ?_, rfl⟩
      simp; exact hrun_ne
    let s_hp := st_branch.mem (b + LCT_HDR_HP)
    let r_end := Function.update st_branch.regs 13 s_hp
    let st_load : State := { mem := st_branch.mem, regs := r_end, pos := st_branch.pos }
    have hload_hp : Runs w p ω (.assign 13 (.load (.bin .add (.reg 6) (.const LCT_HDR_HP))))
        st_branch .normal st_load 5 := by
      refine runs_assign_iff.mpr ⟨s_hp, ?_, rfl, rfl, by decide⟩
      have hadd := Expr.eval_add (Expr.eval_reg_of_eq (st := st_branch) (r := 6) hr6_branch)
        (Expr.eval_const (lt_trans (by decide : LCT_HDR_HP < 36) h36_w))
        (by rw [hbh_hp]; exact lt_trans hnb1_lt_hp hhp_w)
      rw [Expr.eval_load hadd]
    have hret_hp : Runs w p ω (.ret (.bin .add (.reg 13) (.const 1)))
        st_load (.returned hp_final) st_load 4 := by
      have hev : Expr.eval w st_load (.bin .add (.reg 13) (.const 1)) = some hp_final := by
        have hr13 : st_load.regs 13 = st_branch.mem (b + LCT_HDR_HP) := by
          simp [st_load, r_end, s_hp]
        rw [← hhp_branch]
        exact Expr.eval_add (Expr.eval_reg_of_eq (st := st_load) (r := 13) hr13)
          (Expr.eval_const (lt_trans (by decide : 1 < 36) h36_w))
          (by rw [hhp_branch]; exact hfin_lt)
      exact runs_ret_iff.mpr ⟨hp_final, hev, rfl, rfl, by decide⟩
    have hrun_full :=
      runs_seq_normal hs1 (runs_seq_normal hs2 (runs_seq_normal hs3 (runs_seq_normal hs4
        (runs_seq_normal hs5 (runs_seq_normal hs6 (runs_seq_normal hs7 (runs_seq_normal hs8
        (runs_seq_normal hcond_run (runs_seq_normal hload_hp hret_hp)))))))))
    refine ⟨hp_final, st_load, _, _, by simpa [lctPathMinBody] using hrun_full, hrep', hresp', ?_, ?_,
      fun _ => hroots_ne⟩
    · simp only [hpm_eq]
      exact ⟨hm0, hm1, hm2, hm3, hv1, hv2, hf1, hf2⟩
    · change _ + (hp_final - hp_caller) + lctPhi L st_branch.mem b F.n ≤ _
      have hdiff : 2 + (5 + (2 + (4 + (4 + (4 + (8 + (5 + ((3 + c_ne + 1) + (5 + 4 + 1) + 1) +
          1) + 1) + 1) + 1) + 1) + 1) + 1) + 1 ≤ c_ne + 60 := by omega
      exact le_trans (Nat.add_le_add_right (Nat.add_le_add_right hdiff _) _) hcost_ne

end PathMinProcedure

end MinCostFlow.LinkCut.Prog
