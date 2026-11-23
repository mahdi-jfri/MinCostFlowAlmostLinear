module

public import MinCostFlow.HierPaths.InitProgNumbers

/-!
# The two length bounds stored by initialization

The header stores `λ` and `ξ` in one word each. Both procedures compute the hierarchy schedule
from the edge count. They then use multiplication and a shift to form the walk-length bound.
For `ξ`, a second shift and multiplication add the branching and depth factors.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

def initDenomExpr : Expr :=
  .bin .add (.bin .div (.bin .sub (.reg 2) (.const 1)) (.reg 1)) (.const 1)

def initScaleExpr : Expr := .bin .add (.const 2) (.reg 0)

def initSquareExpr (e : Expr) : Expr := .bin .mul e e

def initWalksExpr (a : ℕ) : Expr :=
  .bin .shiftLeft (initSquareExpr (initSquareExpr initScaleExpr))
    (.bin .mul (.bin .mul (.bin .mul (.const a) (.reg 9)) (.reg 21)) (.reg 9))

def initBranchExpr : Expr :=
  .bin .add (.bin .div (.bin .sub (.reg 5) (.const 1)) (.reg 9)) (.const 1)

/-- The last expression uses the walk-length word in register 12. -/
def initLoadBoundExpr : Expr :=
  .bin .mul (.reg 9) (.bin .shiftLeft (.reg 12) (.bin .mul (.const 2) initBranchExpr))

private theorem eval_initDenomExpr {w num den : ℕ} {s : State} (hn : 0 < num) (hd : 0 < den)
    (hnw : num < 2 ^ w) (hdw : den < 2 ^ w)
    (hr1 : s.regs 1 = num) (hr2 : s.regs 2 = den) :
    initDenomExpr.eval w s = some (dOf num den) := by
  rw [dOf_eq_div_pred num den hn hd]
  have hpred : den - 1 < 2 ^ w := (Nat.sub_le _ _).trans_lt hdw
  have hdiv : (den - 1) / num ≤ den - 1 := Nat.div_le_self _ _
  exact Expr.eval_add (Expr.eval_div
    (Expr.eval_sub (Expr.eval_reg_of_eq hr2) (Expr.eval_const (by omega)) hdw)
    (Expr.eval_reg_of_eq hr1) hpred) (Expr.eval_const (by omega)) (by omega)

private theorem eval_initWalksExpr {w a d m : ℕ} {s : State} (ha : 1 ≤ a)
    (hr0 : s.regs 0 = d) (hr9 : s.regs 9 = depthOf m) (hr21 : s.regs 21 = vxOf m)
    (hw : lamOf a d m < 2 ^ w) :
    (initWalksExpr a).eval w s = some (lamOf a d m) := by
  have hVpos : 0 < vOf a m := by rw [vOf_eq_pow_lengthExponent]; exact Nat.two_pow_pos _
  have hHpos : 0 < hOf d := by unfold hOf; exact Nat.pow_pos (by omega)
  have hH := (Nat.le_mul_of_pos_right (hOf d) hVpos).trans_lt hw
  have hV := (Nat.le_mul_of_pos_left (vOf a m) hHpos).trans_lt hw
  have hE : lengthExponent a m < 2 ^ w := by
    rw [vOf_eq_pow_lengthExponent] at hV
    exact Nat.lt_two_pow_self.trans hV
  have hh : 0 < depthOf m := (by decide : 0 < 2).trans_le (two_le_depthOf m)
  have hv : 0 < vxOf m := by
    have h := Nat.le_pow_clog (by decide : 1 < 2) (xOf m + 2)
    by_contra h0
    rw [show Nat.clog 2 (xOf m + 2) = 0 from Nat.eq_zero_of_not_pos h0, pow_zero] at h
    omega
  have h₃ := (Nat.le_mul_of_pos_right (a * depthOf m * vxOf m) hh).trans_lt hE
  have h₂ := (Nat.le_mul_of_pos_right (a * depthOf m) hv).trans_lt h₃
  have h₁ := (Nat.le_mul_of_pos_right a hh).trans_lt h₂
  have hbase : 1 ≤ 2 + d := by omega
  have hbasew : 2 + d < 2 ^ w :=
    (Nat.le_self_pow (by decide) (2 + d)).trans_lt hH
  have hsq : (2 + d) * (2 + d) < 2 ^ w := by
    rw [← pow_two]
    exact (Nat.pow_le_pow_right hbase (by decide)).trans_lt hH
  have ebase := Expr.eval_add (Expr.eval_const (by omega : 2 < 2 ^ w))
    (Expr.eval_reg_of_eq hr0) hbasew
  have esq := Expr.eval_mul ebase ebase hsq
  have eH : (initSquareExpr (initSquareExpr initScaleExpr)).eval w s = some (hOf d) := by
    have heq : (2 + d) * (2 + d) * ((2 + d) * (2 + d)) = hOf d := by unfold hOf; ring
    exact Expr.eval_eq_of_eq (Expr.eval_mul esq esq (heq ▸ hH)) heq
  have eshift : hOf d <<< lengthExponent a m = lamOf a d m := by
    rw [Nat.shiftLeft_eq, ← vOf_eq_pow_lengthExponent, lamOf]
  exact Expr.eval_eq_of_eq
    (Expr.eval_shiftLeft eH
      (Expr.eval_mul (Expr.eval_mul (Expr.eval_mul (Expr.eval_const h₁)
        (Expr.eval_reg_of_eq hr9) h₂) (Expr.eval_reg_of_eq hr21) h₃)
        (Expr.eval_reg_of_eq hr9) hE) (eshift ▸ hw)) eshift

private theorem eval_initLoadBoundExpr {w a d m : ℕ} {s : State}
    (hr5 : s.regs 5 = xOf m) (hr9 : s.regs 9 = depthOf m) (hr12 : s.regs 12 = lamOf a d m)
    (hx : xOf m < 2 ^ w) (hw : xiOf a d m < 2 ^ w) :
    initLoadBoundExpr.eval w s = some (xiOf a d m) := by
  have hh : 0 < depthOf m := (by decide : 0 < 2).trans_le (two_le_depthOf m)
  have hxpos := three_le_xOf m
  have h1 : 1 < 2 ^ w := by omega
  have h2 : 2 < 2 ^ w := by omega
  have hb : branchBits m = (xOf m - 1) / depthOf m + 1 := by
    unfold branchBits
    rw [show xOf m + depthOf m - 1 = (xOf m - 1) + depthOf m by omega, Nat.add_div_right _ hh]
  have hb_le : branchBits m ≤ xOf m := by
    have := Nat.div_le_self (xOf m - 1) (depthOf m)
    omega
  have he : 2 * branchBits m < 2 ^ w := by
    have hp : 2 ^ (2 * branchBits m) = branchOf m ^ 2 := by
      rw [branchOf, ← pow_mul, Nat.mul_comm]
    have hB := Nat.le_mul_of_pos_left (branchOf m ^ 2) hh
    have hXi := Nat.le_mul_of_pos_right (depthOf m * branchOf m ^ 2) (one_le_lamOf a d m)
    have hpow := (hB.trans hXi).trans_lt hw
    rw [← hp] at hpow
    exact Nat.lt_two_pow_self.trans hpow
  have eb : initBranchExpr.eval w s = some (branchBits m) := by
    apply Expr.eval_eq_of_eq _ hb.symm
    exact Expr.eval_add (Expr.eval_div
      (Expr.eval_sub (Expr.eval_reg_of_eq hr5) (Expr.eval_const h1) hx)
      (Expr.eval_reg_of_eq hr9) ((Nat.sub_le _ _).trans_lt hx))
      (Expr.eval_const h1) (by omega)
  have hs : lamOf a d m <<< (2 * branchBits m) = branchOf m ^ 2 * lamOf a d m := by
    rw [Nat.shiftLeft_eq, branchOf, ← pow_mul]
    rw [Nat.mul_comm 2, Nat.mul_comm (lamOf a d m)]
  have hxi : depthOf m * (branchOf m ^ 2 * lamOf a d m) = xiOf a d m := by
    rw [xiOf, Nat.mul_assoc]
  have hsw : lamOf a d m <<< (2 * branchBits m) < 2 ^ w := by
    rw [hs]
    exact (Nat.le_mul_of_pos_left _ hh).trans_lt (by rw [hxi]; exact hw)
  exact Expr.eval_eq_of_eq
    (Expr.eval_mul (Expr.eval_reg_of_eq hr9)
      (Expr.eval_eq_of_eq (Expr.eval_shiftLeft (Expr.eval_reg_of_eq hr12)
        (Expr.eval_mul (Expr.eval_const h2) eb he) hsw) hs)
      (by rw [hxi]; exact hw)) hxi

/-- Compute one of the two length bounds from the graph header and the conductance arguments. -/
def initBoundWord (a : ℕ) (loadBound : Bool) : Stmt :=
  .assign 10 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 0 initDenomExpr ;;
  initSchedule ;;
  .assign 12 (initWalksExpr a) ;;
  .ret (if loadBound then initLoadBoundExpr else .reg 12)

theorem initBoundWord_noRand (a : ℕ) (loadBound : Bool) : (initBoundWord a loadBound).NoRand := by
  simp [initBoundWord, initSchedule_noRand, Stmt.NoRand]

/-- Both bounds have the same schedule cost and a fixed number of remaining instructions. -/
def initBoundWordCost (G : Graph) : ℕ := initScheduleCost G.m + 100

/-- The cost of computing either bound is at most linear in the number of input edges. -/
theorem initBoundWordCost_le_affine (G : Graph) :
    initBoundWordCost G ≤ 45 * G.m + 381 := by
  have hx : xOf G.m ≤ G.m + 3 := by
    rw [xOf_eq_clog_add]
    exact Nat.add_le_add_right
      (Nat.clog_le_of_le_pow (Nat.lt_two_pow_self : G.m < 2 ^ G.m)) 3
  have hv : vxOf G.m ≤ xOf G.m + 2 := by
    exact Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n := xOf G.m + 2)).le
  have hh : depthOf G.m ≤ xOf G.m := ceilRoot_le_self _ _
  unfold initBoundWordCost initScheduleCost
  omega

theorem initBoundWordCost_le (G : Graph) (hm : 1 ≤ G.m) :
    initBoundWordCost G ≤ 450 * G.m :=
  (initBoundWordCost_le_affine G).trans (by omega)

/-- Each of the two procedures returns its bound and preserves memory. -/
noncomputable def initBoundW (a : ℕ) (ha : 1 ≤ a) (loadBound : Bool) : ValW a where
  body := initBoundWord a loadBound
  val _ G base :=
    let d := dOf (base.getD 1 0) (base.getD 2 0)
    if loadBound then xiOf a d G.m else lamOf a d G.m
  cost := initBoundWordCost
  noRand := initBoundWord_noRand a loadBound
  spec w p f hp S G := by
    refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
    obtain ⟨base, c, rfl, _, hI⟩ := hpre
    obtain ⟨gAddr, phiNum, phiDen, M, h, h₁, rfl, _, _, hG, hgh, hnum, hden, hgood, hblock,
      hxi, hlam⟩ := hI
    let d := dOf phiNum phiDen
    have hnumw : phiNum < 2 ^ w := hw _ (by simp)
    have hdenw : phiDen < 2 ^ w := hw _ (by simp)
    have hh : h < 2 ^ w := hw _ (by simp)
    have hgraph : G.encode.length = 2 + 2 * G.m := by
      simp [Graph.encode, Graph.m]; omega
    have hm : 1 ≤ G.m := by
      have hpos := Nat.two_pow_pos S.x
      have hterms := hgood.terms
      omega
    have hmword : G.m + 1 < 2 ^ w := by omega
    have hmread : mem (gAddr + 1) = G.m := by
      have hread := hG 1 (by omega)
      simpa [Graph.encode] using hread
    have hV : vOf a G.m < 2 ^ w :=
      (Nat.le_mul_of_pos_left _ (show 0 < hOf d by unfold hOf; exact Nat.pow_pos (by omega))).trans_lt hlam
    have hcube := (schedule_cube_le_vOf a G.m ha).trans_lt hV
    have hx2 := ((Nat.le_self_pow (by decide : 3 ≠ 0) _).trans
      (schedule_input_cube_le_vOf a G.m ha)).trans_lt hV
    let s := startState ([gAddr, phiNum, phiDen, M, h, h₁] ++ [c]) mem pos
    have hread : (Expr.load (.bin .add (.reg 0) (.const 1))).eval w s = some G.m :=
      Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := gAddr) rfl)
        (Expr.eval_const (by omega)) (by omega)) hmread
    refine runs_start_le ?_
    unfold initBoundWord
    refine runs_seq_assign_le hread ?_
    refine runs_seq_assign_le
      (eval_initDenomExpr (by omega) (by omega) hnumw hdenw rfl rfl) ?_
    refine runs_seq_triple_le (initSchedule_triple _ (by simp) hm hmword hcube hx2) rfl ?_
    intro t ⟨ht5, ht9, ht21, ht0, hmem⟩
    change t.regs 0 = d at ht0
    change t.mem = mem at hmem
    refine runs_seq_assign_le (eval_initWalksExpr ha ht0 ht9 ht21 hlam) ?_
    have hr : (if loadBound then initLoadBoundExpr else .reg 12).eval w
        { t with regs := Function.update t.regs 12 (lamOf a d G.m) } =
        some (if loadBound then xiOf a d G.m else lamOf a d G.m) := by
      cases loadBound
      · exact Expr.eval_reg_of_eq (by simp)
      · exact eval_initLoadBoundExpr (by simpa using ht5) (by simpa using ht9)
          (by simp) (by omega) hxi
    refine runs_ret_le hr ⟨_, c, rfl, rfl, hmem⟩ ?_
    cases loadBound <;>
      simp [ValContract, initBoundWordCost, initDenomExpr, initWalksExpr, initSquareExpr, initScaleExpr,
        initLoadBoundExpr, initBranchExpr, Expr.size] <;> omega

/-- The reverse-list bound word agrees with the model header. -/
theorem initBoundW_xi (S : StaticData) (a : ℕ) (ha : 1 ≤ a) (G : Graph)
    (gAddr phiNum phiDen M h h₁ : ℕ) :
    (initBoundW a ha true).val S G [gAddr, phiNum, phiDen, M, h, h₁] =
      (initConcrete S a (initAbs phiNum phiDen M G)).H.ξ := rfl

/-- The walk-length bound word agrees with the model header. -/
theorem initBoundW_lam (S : StaticData) (a : ℕ) (ha : 1 ≤ a) (G : Graph)
    (gAddr phiNum phiDen M h h₁ : ℕ) :
    (initBoundW a ha false).val S G [gAddr, phiNum, phiDen, M, h, h₁] =
      (initConcrete S a (initAbs phiNum phiDen M G)).H.lam := rfl

end MinCostFlow.HierPaths

end
