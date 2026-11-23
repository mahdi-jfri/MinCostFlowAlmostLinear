module

public import MinCostFlow.DynSpanner.Program.DynSpannerRevDefs

import Mathlib.Tactic.Linarith

/-!
# Verification of `dsRevConsStmt` (`DynSpannerRevCons`)

Proves `dsRevCons_meetsContract` for `dsRevConsStmt` (`revProcs bOps bRev` at index
`revIdxRevCons = 0`), performing an `O(1)` cons onto `(revGen[i, v], revHead[i, v])`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

public section

public theorem dsRevCons_meetsContract {w L vCap eCap b i v e : ℕ}
    {xs : List ℕ} {foot : ℕ → Prop} {p : Program} {bOps bRev : ℕ}
    (hp : p.HasAt bRev (revProcs bOps bRev)) :
    MeetsContract w p (bRev + revIdxRevCons) (dsRevConsContract w L vCap eCap b i v e xs foot) := by
  refine meetsContract_of_runs
    (hp.get (i := revIdxRevCons) (by simp [revProcs, revIdxRevCons]))
    fun args mem pos ω hargs hpre => ?_
  rcases hpre with ⟨heapPtr, rfl, hw16, hfix_le, hheap_lt, hiL, hvCap, he_lt,
    hL, hvC, heC, _, hfoot, hll⟩
  have hb_ltw : b < 2 ^ w := hargs b (by simp)
  have hi_ltw : i < 2 ^ w := hargs i (by simp)
  have hv_ltw : v < 2 ^ w := hargs v (by simp)
  have had := dsAddrs_bound (w := w) (L := L) (vCap := vCap) (eCap := eCap) hfix_le (by omega)
  rcases had with ⟨hdg_sz, hdg_lt, hmin_eq, hmin_lt, hdom_lt, _, _, hrevG_lt, hrevH_lt, hvs_fix, _, _⟩
  have hmul_lt := mul_add_lt_mul_succ hiL hvCap
  have hf := dsFixedSize_add b L vCap eCap
  have h1 := dsMinHBase_eq b vCap eCap
  have h2 := dsDomGenBase_eq b L vCap eCap
  have h3 := dsRevGenBase_eq b L vCap eCap
  have h4 := dsRevHeadBase_eq b L vCap eCap
  have h5 := dsVStampBase_eq b L vCap eCap
  have h0_lt : (0 : ℕ) < 2 ^ w := by omega
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have h2_lt : (2 : ℕ) < 2 ^ w := by omega
  have h3_lt : (3 : ℕ) < 2 ^ w := by omega
  have h4_lt : (4 : ℕ) < 2 ^ w := by omega
  have h6_lt : (6 : ℕ) < 2 ^ w := by omega
  have h7_lt : (7 : ℕ) < 2 ^ w := by omega
  have h9_lt : (9 : ℕ) < 2 ^ w := by omega
  have hiv_lt : dsRevGenBase b L vCap eCap + (i * vCap + v) < b + dsFixedSize L vCap eCap := by
    omega
  have hih_lt : dsRevHeadBase b L vCap eCap + (i * vCap + v) < b + dsFixedSize L vCap eCap := by
    omega
  have hdomi_lt : dsDomGenBase b L vCap eCap + i < b + dsFixedSize L vCap eCap := by omega
  set domAddr := dsDomGenBase b L vCap eCap + i
  set rgenAddr := dsRevGenBase b L vCap eCap + i * vCap + v
  set rheadAddr := dsRevHeadBase b L vCap eCap + i * vCap + v
  set domVal := mem domAddr
  set revVal := mem rgenAddr
  have hne_rg_rh : rgenAddr ≠ rheadAddr := dsRevGen_ne_dsRevHead hiL hvCap
  have hne_rg_hp : rgenAddr ≠ heapPtr := by omega
  have hne_rg_hp1 : rgenAddr ≠ heapPtr + 1 := by omega
  have hne_rh_hp : rheadAddr ≠ heapPtr := by omega
  have hne_rh_hp1 : rheadAddr ≠ heapPtr + 1 := by omega
  have hne_rg_dom : rgenAddr ≠ domAddr := by omega
  have hne_rh_dom : rheadAddr ≠ domAddr := by omega
  have hrg_eq : dsRevGenBase b L vCap eCap + (i * vCap + v) = rgenAddr := by omega
  have hrh_eq : dsRevHeadBase b L vCap eCap + (i * vCap + v) = rheadAddr := by omega
  refine runs_start_le ?_
  dsimp only [revProcs, revIdxRevCons, List.getElem_cons_zero, dsRevConsStmt]
  refine runs_seq_assign_le (v := vCap)
    (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, startState, dsVCapOff, h3_lt,
      show b + 3 < 2 ^ w by omega]) hvC) ?_
  refine runs_seq_assign_le (v := eCap)
    (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, startState, dsECapOff, h4_lt,
      show b + 4 < 2 ^ w by omega]) heC) ?_
  refine runs_seq_assign_le (v := L)
    (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, startState, dsLOff, h2_lt,
      show b + 2 < 2 ^ w by omega]) hL) ?_
  refine runs_seq_assign_le (v := dynGraphSize vCap eCap)
    (by simp [Expr.eval, BinOp.eval, h4_lt, h7_lt, h9_lt,
      show 7 * vCap < 2 ^ w by omega, show 9 * eCap < 2 ^ w by omega,
      show 7 * vCap + 9 * eCap < 2 ^ w by omega,
      show 4 + (7 * vCap + 9 * eCap) < 2 ^ w by omega]; omega) ?_
  refine runs_seq_assign_le (v := dsMinHBase b vCap eCap)
    (by rw [← hmin_eq, show dsHdrSize = 6 from rfl]
        simp [Expr.eval, BinOp.eval, startState, h6_lt, h3_lt,
          show b + 6 < 2 ^ w by omega,
          show 3 * dynGraphSize vCap eCap < 2 ^ w by omega,
          show b + 6 + 3 * dynGraphSize vCap eCap < 2 ^ w by
            rw [← show dsHdrSize = 6 from rfl, hmin_eq]; omega]) ?_
  refine runs_seq_assign_le (v := dsDomGenBase b L vCap eCap)
    (by rw [dsDomGenBase_eq]
        simp [Expr.eval, BinOp.eval, h3_lt, h2_lt, h1_lt,
          show 3 * eCap < 2 ^ w by omega, show L + 1 < 2 ^ w by omega,
          show 2 * (L + 1) < 2 ^ w by omega, show 3 * eCap + 2 * (L + 1) < 2 ^ w by omega,
          show dsMinHBase b vCap eCap + (3 * eCap + 2 * (L + 1)) < 2 ^ w by
            rw [← dsDomGenBase_eq]; omega]) ?_
  refine runs_seq_assign_le (v := dsRevGenBase b L vCap eCap)
    (by rw [dsRevGenBase_eq]
        simp [Expr.eval, BinOp.eval, h1_lt, h2_lt,
          show L + 1 < 2 ^ w by omega, show (L + 1) * eCap < 2 ^ w by omega,
          show 2 * ((L + 1) * eCap) < 2 ^ w by omega,
          show (L + 1) + 2 * ((L + 1) * eCap) < 2 ^ w by omega,
          show dsDomGenBase b L vCap eCap + ((L + 1) + 2 * ((L + 1) * eCap)) < 2 ^ w by
            rw [← dsRevGenBase_eq]; omega]) ?_
  refine runs_seq_assign_le (v := dsRevHeadBase b L vCap eCap)
    (by rw [dsRevHeadBase_eq]
        simp [Expr.eval, BinOp.eval, h1_lt,
          show L + 1 < 2 ^ w by omega, show (L + 1) * vCap < 2 ^ w by omega,
          show dsRevGenBase b L vCap eCap + (L + 1) * vCap < 2 ^ w by
            rw [← dsRevHeadBase_eq]; omega]) ?_
  refine runs_seq_assign_le (v := i * vCap + v)
    (by simp [Expr.eval, BinOp.eval, startState, show i * vCap < 2 ^ w by omega,
      show i * vCap + v < 2 ^ w by omega]) ?_
  refine runs_seq_assign_le (v := rgenAddr)
    (by rw [← hrg_eq]; simp [Expr.eval, BinOp.eval,
      show dsRevGenBase b L vCap eCap + (i * vCap + v) < 2 ^ w by omega]) ?_
  refine runs_seq_assign_le (v := rheadAddr)
    (by rw [← hrh_eq]; simp [Expr.eval, BinOp.eval,
      show dsRevHeadBase b L vCap eCap + (i * vCap + v) < 2 ^ w by omega]) ?_
  refine runs_seq_assign_le (v := domVal)
    (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, startState, domAddr,
      show dsDomGenBase b L vCap eCap + i < 2 ^ w by omega]) rfl) ?_
  refine runs_seq_assign_le (v := revVal)
    (Expr.eval_load_of_eq (by simp [Expr.eval]) rfl) ?_
  let tailStmt : Stmt :=
    .assign 9 (.load (.reg 14)) ;;
    .store (.reg 4) (.reg 3) ;;
    .store (.bin .add (.reg 4) (.const 1)) (.reg 9) ;;
    .store (.reg 14) (.reg 4) ;;
    .ret (.bin .add (.reg 4) (.const 2))
  have htail : ∀ (k₁ : ℕ) (st1 : State), k₁ ≤ 165 →
      st1.regs 3 = e → st1.regs 4 = heapPtr → st1.regs 14 = rheadAddr →
      st1.mem rgenAddr = domVal →
      LinkedListIn foot st1.mem (st1.mem rheadAddr) xs →
      (∀ addr, addr ≠ rgenAddr → addr ≠ rheadAddr → st1.mem addr = mem addr) →
      ∃ o st' c, Runs w p ω tailStmt st1 o st' c ∧
        (dsRevConsContract w L vCap eCap b i v e xs foot).post [b, i, v, e, heapPtr] mem o.value st'.mem ∧
        k₁ + c ≤ (dsRevConsContract w L vCap eCap b i v e xs foot).cost [b, i, v, e, heapPtr] mem := by
    intro k₁ st1 hk₁ hr3 hr4 hr14 hrg hll1 hfr1
    refine runs_seq_assign_le (v := st1.mem rheadAddr)
      (Expr.eval_load_of_eq (by simp [Expr.eval, hr14]) rfl) ?_
    refine runs_seq_store_le (x := heapPtr) (v := e)
      (by simp [Expr.eval, hr4]) (by simp [Expr.eval, hr3]) ?_
    refine runs_seq_store_le (x := heapPtr + 1) (v := st1.mem rheadAddr)
      (by simp [Expr.eval, BinOp.eval, hr4, h1_lt, show heapPtr + 1 < 2 ^ w by omega])
      (by simp [Expr.eval]) ?_
    refine runs_seq_store_le (x := rheadAddr) (v := heapPtr)
      (by simp [Expr.eval, hr14]) (by simp [Expr.eval, hr4]) ?_
    refine runs_ret_le (by simp [Expr.eval, BinOp.eval, hr4, h2_lt, show heapPtr + 2 < 2 ^ w by omega])
      ⟨heapPtr, rfl, rfl, ?_, ?_, ?_⟩ ?_
    · dsimp only
      rw [Function.update_of_ne hne_rg_rh, Function.update_of_ne hne_rg_hp1,
        Function.update_of_ne hne_rg_hp, hrg]
    · have hp_pos : 0 < heapPtr := by have := dsFixedSize_pos L vCap eCap; omega
      dsimp only
      rw [Function.update_self]
      refine ⟨hp_pos, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), ?_, ?_⟩
      · rw [Function.update_of_ne hne_rh_hp.symm, Function.update_of_ne (by omega), Function.update_self]
      · rw [Function.update_of_ne hne_rh_hp1.symm, Function.update_self]
        refine (hll1.of_agree fun a ha => ?_).mono fun _ h => Or.inl h
        have ha_b := hfoot a ha
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega)]
    · intro addr h1 h2 h3 h4
      dsimp only
      rw [Function.update_of_ne h2, Function.update_of_ne h4, Function.update_of_ne h3, hfr1 addr h1 h2]
    · dsimp only [dsRevConsContract, argsSize, Expr.size]; omega
  have hCond : Triple w p (fun st0 => st0.regs 3 = e ∧ st0.regs 4 = heapPtr ∧
      st0.regs 8 = domVal ∧ st0.regs 13 = rgenAddr ∧ st0.regs 14 = rheadAddr ∧
      st0.regs 15 = revVal ∧ st0.mem = mem)
      (.cond (.bin .eq (.reg 15) (.reg 8))
        (.nop)
        (.store (.reg 13) (.reg 8) ;;
         .store (.reg 14) (.const 0)))
      (normalPost fun st1 =>
        st1.regs 3 = e ∧ st1.regs 4 = heapPtr ∧ st1.regs 14 = rheadAddr ∧
        st1.mem rgenAddr = domVal ∧ LinkedListIn foot st1.mem (st1.mem rheadAddr) xs ∧
        ∀ addr, addr ≠ rgenAddr → addr ≠ rheadAddr → st1.mem addr = mem addr)
      (fun _ => 20) := by
    intro st0 ω ⟨r0_3, r0_4, r0_8, r0_13, r0_14, r0_15, m0⟩
    refine runs_start_le ?_
    by_cases h : revVal = domVal
    · refine runs_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, r0_15, r0_8, h, h1_lt])
        (fun _ => runs_nop_le ?_ (by dsimp only [Expr.size]; omega))
        (fun hz => False.elim (by omega))
      refine ⟨r0_3, r0_4, r0_14, ?_, ?_, fun _ _ _ => congrFun m0 _⟩
      · simpa [m0] using h
      · simpa [m0, revVal, domVal, rgenAddr, domAddr, rheadAddr, h] using hll
    · refine runs_cond_le (v := 0) (by simp [Expr.eval, BinOp.eval, r0_15, r0_8, h, h0_lt])
        (fun hne => False.elim (by omega)) (fun _ => ?_)
      have hnil : xs = [] := by
        simpa [revVal, domVal, rgenAddr, domAddr, h] using hll
      refine runs_seq_store_le (x := rgenAddr) (v := domVal)
        (by simp [Expr.eval, r0_13]) (by simp [Expr.eval, r0_8]) ?_
      refine runs_store_le (x := rheadAddr) (v := 0)
        (by simp [Expr.eval, r0_14]) (by eval_expr) ?_ (by dsimp only [Expr.size]; omega)
      refine ⟨r0_3, r0_4, r0_14, ?_, ?_, ?_⟩
      · dsimp only; rw [Function.update_of_ne hne_rg_rh, Function.update_self]
      · dsimp only; rw [Function.update_self, hnil]; rfl
      · intro addr ha1 ha2; dsimp only; rw [Function.update_of_ne ha2, Function.update_of_ne ha1, m0]
  refine runs_seq_triple_le hCond ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_
  intro st1 ⟨hr3, hr4, hr14, hrg, hll1, hfr1⟩
  exact htail _ st1 (by dsimp only [Expr.size]; omega) hr3 hr4 hr14 hrg hll1 hfr1


end

end MinCostFlow.DynSpanner.Program
