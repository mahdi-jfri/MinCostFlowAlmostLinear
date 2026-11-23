module

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import MinCostFlow.LSF.Program.InitArena
public import MinCostFlow.LSF.Program.SharedProcs

/-!
# LSF Tree Initialization Weight Scaling and Congruence-Quotient Primitives

Implements and verifies the four modular deterministic `WordRAM` procedures used in the
`m0 > 0` branch of `InitTree`:
- `limbsToWordProc`: decodes an `L`-limb unsigned integer `< 2 ^ w` into a machine word.
- `sumWeightsProc`: sums the input `L_in`-limb weights `v_int(e)` across `G₀.E` at width `K_w`.
- `multQNatStepProc`: computes `edgeMult G₀ v e` and `q_nat(e) = ⌊edgeMult * 2^(h*(L_in+4)) / ℓ_int(e)⌋`
  for one original edge, reusing `[hp, hp_next)` inside the `lsstSpace` arena.
- `emitEdgeCopiesProc`: emits the `edgeMult` parallel copies of one edge into `iaCopyTail`,
  `iaCopyHead`, `iaCopyLen`, `iaCopyWt`, `iaCopyOrigIdx`, and `iaCopySubIdx`.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open WordRAM

/-! ## Module Layout -/

def idxLimbsToWord : ℕ := 0
def idxSumWeights : ℕ := 1
def idxMultQNatStep : ℕ := 2
def idxEmitEdgeCopies : ℕ := 3

/-! ## Procedure 1: `limbsToWord` -/

def limbsToWordProc : Stmt :=
  .assign 3 (.const 0) ;;
  forRange 4 (.const 0) (.reg 1)
    (.assign 5 (.bin .sub (.reg 1) (.const 1)) ;;
     .assign 6 (.bin .sub (.reg 5) (.reg 4)) ;;
     .assign 7 (.load (.bin .add (.reg 0) (.reg 6))) ;;
     .assign 3 (.bin .add (.bin .mul (.reg 3) (.reg 2)) (.reg 7))) ;;
  .ret (.reg 3)

def limbsToWordContract (w h : ℕ) : Contract where
  pre args mem :=
    ∃ limbPtr len pow2h,
      args = [limbPtr, len, pow2h] ∧
        pow2h = 2 ^ h ∧ 1 ≤ h ∧ 1 ≤ len ∧ 16 ≤ 2 ^ w ∧
        limbPtr + len < 2 ^ w ∧ len < 2 ^ w ∧ pow2h < 2 ^ w ∧
        Num.Valid mem limbPtr h len ∧
        Num.unsignedVal mem limbPtr h len < 2 ^ w
  post args mem ret mem' :=
    ∃ limbPtr len pow2h,
      args = [limbPtr, len, pow2h] ∧
        mem' = mem ∧
        ret = Num.unsignedVal mem limbPtr h len
  cost args _ := 45 * args.getD 1 0 + 15

lemma limbsToWordProc_noRand : limbsToWordProc.NoRand := by
  simp [limbsToWordProc, forRange, forUp, Stmt.NoRand]

lemma unsignedVal_suffix_lt {mem : ℕ → ℕ} {limbPtr h len j : ℕ}
    (hj : j ≤ len) :
    Num.unsignedVal mem (limbPtr + (len - j)) h j ≤ Num.unsignedVal mem limbPtr h len := by
  have heq : len = (len - j) + j := (Nat.sub_add_cancel hj).symm
  conv_rhs => rw [heq, unsignedVal_split]
  have hcap : 1 ≤ Num.capacity h (len - j) := Num.capacity_pos h (len - j)
  calc Num.unsignedVal mem (limbPtr + (len - j)) h j
      ≤ Num.capacity h (len - j) * Num.unsignedVal mem (limbPtr + (len - j)) h j :=
        Nat.le_mul_of_pos_left _ hcap
    _ ≤ Num.unsignedVal mem limbPtr h (len - j) +
          Num.capacity h (len - j) * Num.unsignedVal mem (limbPtr + (len - j)) h j :=
        Nat.le_add_left _ _

lemma limbsToWord_meetsContract {w h f : ℕ} {p : Program}
    (hproc : p.procs[f]? = some limbsToWordProc) :
    MeetsContract w p f (limbsToWordContract w h) := by
  refine meetsContract_of_triple hproc ?_
  intro args mem pos hargs hpre
  rcases hpre with ⟨limbPtr, len, pow2h, rfl, rfl, hh, hlen1, hw16, hlim_w, hlen_w, hpow_w, hval, hu_w⟩
  have hw1 : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  let P0 : State → Prop := fun st =>
    st = startState [limbPtr, len, 2 ^ h] mem pos
  let P1 : State → Prop := fun st =>
    st.mem = mem ∧ st.regs 0 = limbPtr ∧ st.regs 1 = len ∧ st.regs 2 = 2 ^ h ∧ st.regs 3 = 0
  let Inv : ℕ → State → Prop := fun j st =>
    j ≤ len ∧ st.mem = mem ∧ st.regs 0 = limbPtr ∧ st.regs 1 = len ∧ st.regs 2 = 2 ^ h ∧
      st.regs 4 = j ∧ st.regs 3 = Num.unsignedVal mem (limbPtr + (len - j)) h j
  have h1 : Triple w p P0 (.assign 3 (.const 0)) (normalPost P1) fun _ => 2 :=
    Triple.assign (fun _ _ => Expr.eval_const h0_w) fun st hst => by
      subst hst
      refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> simp [startState, Function.update]
  have hloop : Triple w p P1
      (forRange 4 (.const 0) (.reg 1)
        (.assign 5 (.bin .sub (.reg 1) (.const 1)) ;;
         .assign 6 (.bin .sub (.reg 5) (.reg 4)) ;;
         .assign 7 (.load (.bin .add (.reg 0) (.reg 6))) ;;
         .assign 3 (.bin .add (.bin .mul (.reg 3) (.reg 2)) (.reg 7))))
      (normalPost (Inv len)) fun _ => (len - 0) * (22 + 1 + 8) + (1 + 1 + 5) := by
    refine Triple.forRange_const 22 0 len (Nat.zero_le _) hw1 (fun _ => hlen_w)
      (fun st hst => ⟨Expr.eval_const h0_w, Nat.zero_le _, hst.1,
        by dsimp; rw [Function.update_of_ne (by decide)]; exact hst.2.1,
        by dsimp; rw [Function.update_of_ne (by decide)]; exact hst.2.2.1,
        by dsimp; rw [Function.update_of_ne (by decide)]; exact hst.2.2.2.1,
        by dsimp; rw [Function.update_self],
        by dsimp; rw [Function.update_of_ne (by decide), hst.2.2.2.2]; simp [Num.unsignedVal]⟩)
      (fun i _ _ _ hi => hi.2.2.2.2.2.1)
      (fun i _ _ _ hi => Expr.eval_reg_of_eq hi.2.2.2.1)
      (fun j _ hj => ?_)
    have hsub1_w : len - 1 < 2 ^ w := by omega
    have hj1_le : j + 1 ≤ len := hj
    have hnext_w : len - 1 - j < 2 ^ w := by omega
    have haddr_w : limbPtr + (len - 1 - j) < 2 ^ w := by omega
    have hdj_lt : len - 1 - j < len := by omega
    have hlimb_lt_pow : mem (limbPtr + (len - 1 - j)) < 2 ^ h := hval _ hdj_lt
    have hstep_val :
        2 ^ h * Num.unsignedVal mem (limbPtr + (len - j)) h j + mem (limbPtr + (len - 1 - j)) =
          Num.unsignedVal mem (limbPtr + (len - (j + 1))) h (j + 1) := by
      have hpos_eq : limbPtr + (len - (j + 1)) + 1 = limbPtr + (len - j) := by omega
      have hidx_eq : len - 1 - j = len - (j + 1) := by omega
      rw [hidx_eq, Num.unsignedVal, hpos_eq]
      dsimp only [Num.base]
      ring
    have hsuf_le : Num.unsignedVal mem (limbPtr + (len - (j + 1))) h (j + 1) < 2 ^ w :=
      lt_of_le_of_lt (unsignedVal_suffix_lt hj1_le) hu_w
    have hadd_w_left :
        2 ^ h * Num.unsignedVal mem (limbPtr + (len - j)) h j + mem (limbPtr + (len - 1 - j)) <
          2 ^ w := by
      linarith [hstep_val, hsuf_le]
    have hmul_w : Num.unsignedVal mem (limbPtr + (len - j)) h j * 2 ^ h < 2 ^ w := by
      rw [mul_comm]
      omega
    have hadd_w :
        Num.unsignedVal mem (limbPtr + (len - j)) h j * 2 ^ h + mem (limbPtr + (len - 1 - j)) <
          2 ^ w := by
      rw [mul_comm]
      exact hadd_w_left
    refine Triple.seq_normal (T₁ := fun _ => 4) (T₂ := fun _ => 17)
      (R := fun st => Inv j st ∧ st.regs 5 = len - 1)
      (Triple.assign
        (fun st hst => Expr.eval_sub (Expr.eval_reg_of_eq hst.2.2.2.1) (Expr.eval_const hw1) hlen_w)
        fun st hst => by
          refine ⟨⟨hst.1, hst.2.1, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
          · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.2.2.1
          · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.2.2.2.1
          · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.2.2.2.2.1
          · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.2.2.2.2.2.1
          · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.2.2.2.2.2.2
          · dsimp; rw [Function.update_self])
      ?_ (fun _ _ _ _ => by omega)
    refine Triple.seq_normal (T₁ := fun _ => 4) (T₂ := fun _ => 12)
      (R := fun st => Inv j st ∧ st.regs 6 = len - 1 - j)
      (Triple.assign
        (fun st hst =>
          Expr.eval_sub (Expr.eval_reg_of_eq hst.2) (Expr.eval_reg_of_eq hst.1.2.2.2.2.2.1) hsub1_w)
        fun st hst => by
          refine ⟨⟨hst.1.1, hst.1.2.1, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
          · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.2.2.1
          · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.2.2.2.1
          · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.2.2.2.2.1
          · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.2.2.2.2.2.1
          · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.2.2.2.2.2.2
          · dsimp; rw [Function.update_self])
      ?_ (fun _ _ _ _ => by omega)
    refine Triple.seq_normal (T₁ := fun _ => 5) (T₂ := fun _ => 6)
      (R := fun st => Inv j st ∧ st.regs 7 = mem (limbPtr + (len - 1 - j)))
      (Triple.assign
        (fun st hst =>
          Expr.eval_load_of_eq
            (Expr.eval_add (Expr.eval_reg_of_eq hst.1.2.2.1) (Expr.eval_reg_of_eq hst.2) haddr_w)
            rfl)
        fun st hst => by
          refine ⟨⟨hst.1.1, hst.1.2.1, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
          · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.2.2.1
          · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.2.2.2.1
          · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.2.2.2.2.1
          · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.2.2.2.2.2.1
          · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.2.2.2.2.2.2
          · dsimp; rw [Function.update_self, hst.1.2.1])
      ?_ (fun _ _ _ _ => by omega)
    refine Triple.assign
      (fun st hst => by
        have hm := Expr.eval_mul (Expr.eval_reg_of_eq hst.1.2.2.2.2.2.2)
          (Expr.eval_reg_of_eq hst.1.2.2.2.2.1) hmul_w
        exact Expr.eval_add hm (Expr.eval_reg_of_eq hst.2) hadd_w)
      fun st hst => ?_
    refine ⟨⟨by omega, hst.1.2.1, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.2.2.1
    · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.2.2.2.1
    · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.2.2.2.2.1
    · dsimp; rw [Function.update_self]
    · dsimp; rw [Function.update_of_ne (by decide), Function.update_self]
      linarith [hstep_val]
    · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.2.2.2.2.2.1
  have hret : Triple w p (Inv len) (.ret (.reg 3))
      (retPost fun u st' => u = Num.unsignedVal mem limbPtr h len ∧ st'.mem = mem) fun _ => 2 :=
    Triple.ret (fun st hst => Expr.eval_reg_of_eq hst.2.2.2.2.2.2) fun st hst =>
      ⟨by rw [Nat.sub_self, Nat.add_zero], hst.2.1⟩
  refine Triple.conseq (Triple.seq_normal h1
      (Triple.seq_normal hloop hret (fun _ _ _ _ => le_rfl)) (fun _ _ _ _ => le_rfl))
    (fun st hst => hst)
    (fun o st' hpost => by
      cases o with
      | normal => exact False.elim hpost
      | returned _ => exact ⟨limbPtr, len, 2 ^ h, rfl, hpost.2, hpost.1⟩)
    (fun st _ => by
      simp only [limbsToWordContract, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some]
      omega)

/-! ## Procedure 2: `sumWeights` -/

def sumWeightsProc (b : ℕ) : Stmt :=
  .call 10 (lsfBaseUtils b + idxUtilMemFill) [.reg 4, .reg 6, .const 0] ;;
  forRange 7 (.const 0) (.reg 1)
    (.assign 8 (.load (.bin .add (.reg 0) (.reg 7))) ;;
     .call 10 (lsfBaseUtils b + idxUtilMemFill) [.reg 5, .reg 6, .const 0] ;;
     .assign 9 (.bin .add (.reg 2) (.bin .mul (.reg 8) (.reg 3))) ;;
     .call 10 (lsfBaseUtils b + idxUtilMemCopy) [.reg 5, .reg 9, .reg 3] ;;
     .call 10 (lsfBaseUtils b + idxUtilAddTo) [.reg 4, .reg 5, .reg 6]) ;;
  .ret (.const 0)

def sumWeightsContract (w h : ℕ) : Contract where
  pre args mem :=
    ∃ eListPtr m0 wtArr L_in svPtr edgeLimbsPtr K_w,
      args = [eListPtr, m0, wtArr, L_in, svPtr, edgeLimbsPtr, K_w] ∧
        1 ≤ h ∧ 2 * h + 2 ≤ w ∧ 16 ≤ 2 ^ w ∧
        1 ≤ m0 ∧ 1 ≤ L_in ∧ L_in ≤ K_w ∧
        eListPtr + m0 ≤ svPtr ∧
        (∀ j < m0, (wtArr + mem (eListPtr + j) * L_in) + L_in ≤ svPtr) ∧
        (∀ j < m0, Num.Valid mem (wtArr + mem (eListPtr + j) * L_in) h L_in) ∧
        svPtr + K_w ≤ edgeLimbsPtr ∧
        edgeLimbsPtr + K_w < 2 ^ w ∧
        (∑ j ∈ Finset.range m0, Num.unsignedVal mem (wtArr + mem (eListPtr + j) * L_in) h L_in) <
          Num.capacity h K_w / 2
  post args mem ret mem' :=
    ∃ eListPtr m0 wtArr L_in svPtr edgeLimbsPtr K_w,
      args = [eListPtr, m0, wtArr, L_in, svPtr, edgeLimbsPtr, K_w] ∧
        ret = 0 ∧
        Num.Valid mem' svPtr h K_w ∧
        Num.unsignedVal mem' svPtr h K_w =
          ∑ j ∈ Finset.range m0, Num.unsignedVal mem (wtArr + mem (eListPtr + j) * L_in) h L_in ∧
        (∀ a, a < svPtr ∨ edgeLimbsPtr + K_w ≤ a → mem' a = mem a)
  cost args _ :=
    let m0 := args.getD 1 0
    let L_in := args.getD 3 0
    let K_w := args.getD 6 0
    m0 * (100 * K_w + 25 * L_in + 120) + (20 * K_w + 50)

lemma sumWeightsProc_noRand (b : ℕ) : (sumWeightsProc b).NoRand := by
  simp [sumWeightsProc, forRange, forUp, Stmt.NoRand]

lemma sumWeights_meetsContract {w b K_AN h f : ℕ} {p : Program}
    (hp : p.HasAt (b + 2) (lsfSharedProcs b K_AN h))
    (hproc : p.procs[f]? = some (sumWeightsProc b)) :
    MeetsContract w p f (sumWeightsContract w h) := by
  refine meetsContract_of_triple hproc ?_
  intro args mem pos hargs hpre
  rcases hpre with ⟨eListPtr, m0, wtArr, L_in, svPtr, edgeLimbsPtr, K_w,
    rfl, hh1, hw2h, hw16, hm0, hLin, hLK, heL_sv, hwt_bd, hwt_val, hsv_ed, hed_w, hsum_cap⟩
  have hw1 : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hm0_w : m0 < 2 ^ w := hargs m0 (by simp)
  have hLin_w : L_in < 2 ^ w := hargs L_in (by simp)
  have hKw_w : K_w < 2 ^ w := hargs K_w (by simp)
  have heL_w : eListPtr < 2 ^ w := hargs eListPtr (by simp)
  have hwt_w : wtArr < 2 ^ w := hargs wtArr (by simp)
  have hsv_w : svPtr < 2 ^ w := hargs svPtr (by simp)
  have hed_w0 : edgeLimbsPtr < 2 ^ w := hargs edgeLimbsPtr (by simp)
  have hmc_fill := lsfMemFill_meetsContract hw1 hp
  have hmc_copy := lsfMemCopy_meetsContract hw1 hp
  have hmc_addTo := lsfAddTo_meetsContract (w := w) hp
  let partialSum : ℕ → ℕ := fun j =>
    ∑ t ∈ Finset.range j, Num.unsignedVal mem (wtArr + mem (eListPtr + t) * L_in) h L_in
  let Inv : ℕ → State → Prop := fun j st =>
    j ≤ m0 ∧
      st.regs 0 = eListPtr ∧ st.regs 1 = m0 ∧ st.regs 2 = wtArr ∧ st.regs 3 = L_in ∧
      st.regs 4 = svPtr ∧ st.regs 5 = edgeLimbsPtr ∧ st.regs 6 = K_w ∧ st.regs 7 = j ∧
      Num.Valid st.mem svPtr h K_w ∧
      Num.unsignedVal st.mem svPtr h K_w = partialSum j ∧
      (∀ a, a < svPtr ∨ edgeLimbsPtr + K_w ≤ a → st.mem a = mem a)
  have hinit : Triple w p (fun st => st = startState [eListPtr, m0, wtArr, L_in, svPtr, edgeLimbsPtr, K_w] mem pos)
      (.call 10 (lsfBaseUtils b + idxUtilMemFill) [.reg 4, .reg 6, .const 0])
      (normalPost (Inv 0)) fun _ => 16 * K_w + 20 := by
    refine Triple.conseq
      (Triple.call (vs := fun _ => [svPtr, K_w, 0]) hmc_fill
        (fun st hst => by
          subst hst
          exact evalArgs_cons (Expr.eval_reg_of_eq (by simp [startState]))
            (evalArgs_cons (Expr.eval_reg_of_eq (by simp [startState]))
              (evalArgs_cons (Expr.eval_const h0_w) (evalArgs_nil _ _))))
        (fun st hst v hv => by
          subst hst
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl <;> assumption)
        (fun st hst => by
          subst hst
          exact ⟨svPtr, K_w, 0, rfl, by omega⟩)
        (fun st _ mem1 _ hst ⟨dst, len, val, heq, _, hfill, hfr⟩ => by
          subst hst
          simp only [List.cons.injEq, and_true] at heq
          rcases heq with ⟨rfl, rfl, rfl⟩
          refine ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha => ?_⟩
          · dsimp; rw [Function.update_of_ne (by decide)]; rfl
          · dsimp; rw [Function.update_of_ne (by decide)]; rfl
          · dsimp; rw [Function.update_of_ne (by decide)]; rfl
          · dsimp; rw [Function.update_of_ne (by decide)]; rfl
          · dsimp; rw [Function.update_of_ne (by decide)]; rfl
          · dsimp; rw [Function.update_of_ne (by decide)]; rfl
          · dsimp; rw [Function.update_of_ne (by decide)]; rfl
          · dsimp; rw [Function.update_of_ne (by decide)]; rfl
          · intro i hi; dsimp; rw [hfill i hi]; exact Num.base_pos h
          · dsimp; simp [partialSum, Num.unsignedVal_zero fun i hi => hfill i hi]
          · exact hfr a (by omega)))
      (fun _ h => h) (fun _ _ h => h)
      (fun st hst => by
        subst hst
        simp only [argsSize, Expr.size, memFillContract, List.getD_eq_getElem?_getD,
          List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
        omega)
  have hloop : Triple w p (Inv 0)
      (forRange 7 (.const 0) (.reg 1)
        (.assign 8 (.load (.bin .add (.reg 0) (.reg 7))) ;;
         .call 10 (lsfBaseUtils b + idxUtilMemFill) [.reg 5, .reg 6, .const 0] ;;
         .assign 9 (.bin .add (.reg 2) (.bin .mul (.reg 8) (.reg 3))) ;;
         .call 10 (lsfBaseUtils b + idxUtilMemCopy) [.reg 5, .reg 9, .reg 3] ;;
         .call 10 (lsfBaseUtils b + idxUtilAddTo) [.reg 4, .reg 5, .reg 6]))
      (normalPost (Inv m0)) fun _ => (m0 - 0) * ((100 * K_w + 25 * L_in + 100) + 1 + 8) + (1 + 1 + 5) := by
    refine Triple.forRange_const (100 * K_w + 25 * L_in + 100) 0 m0 (Nat.zero_le _) hw1
      (fun _ => hm0_w)
      (fun st hst => ⟨Expr.eval_const h0_w, Nat.zero_le _,
        by dsimp; rw [Function.update_of_ne (by decide)]; exact hst.2.1,
        by dsimp; rw [Function.update_of_ne (by decide)]; exact hst.2.2.1,
        by dsimp; rw [Function.update_of_ne (by decide)]; exact hst.2.2.2.1,
        by dsimp; rw [Function.update_of_ne (by decide)]; exact hst.2.2.2.2.1,
        by dsimp; rw [Function.update_of_ne (by decide)]; exact hst.2.2.2.2.2.1,
        by dsimp; rw [Function.update_of_ne (by decide)]; exact hst.2.2.2.2.2.2.1,
        by dsimp; rw [Function.update_of_ne (by decide)]; exact hst.2.2.2.2.2.2.2.1,
        by dsimp; rw [Function.update_self],
        hst.2.2.2.2.2.2.2.2.2.1, hst.2.2.2.2.2.2.2.2.2.2.1, hst.2.2.2.2.2.2.2.2.2.2.2⟩)
      (fun i _ _ _ hi => hi.2.2.2.2.2.2.2.2.1)
      (fun i _ _ _ hi => Expr.eval_reg_of_eq hi.2.2.1)
      (fun j _ hj => ?_)
    have hsrc_bd := hwt_bd j hj
    have hsrc_val := hwt_val j hj
    have hsum_j1 : partialSum (j + 1) < Num.capacity h K_w / 2 := by
      have hsub : partialSum (j + 1) ≤ partialSum m0 := by
        dsimp only [partialSum]
        exact Finset.sum_le_sum_of_subset (Finset.range_mono hj)
      exact lt_of_le_of_lt hsub hsum_cap
    have he_val_mem : ∀ st, Inv j st → st.mem (eListPtr + j) = mem (eListPtr + j) := fun st hst =>
      hst.2.2.2.2.2.2.2.2.2.2.2 (eListPtr + j) (Or.inl (by omega))
    have haddr_e_w : eListPtr + j < 2 ^ w := by omega
    have hj_w : j < 2 ^ w := by omega
    have hmul_w : mem (eListPtr + j) * L_in < 2 ^ w := by omega
    have hsrc_w : wtArr + mem (eListPtr + j) * L_in + L_in < 2 ^ w := by omega
    -- Step 1: assign 8 := mem[eListPtr + j]
    refine Triple.seq_normal (T₁ := fun _ => 5) (T₂ := fun _ => 100 * K_w + 25 * L_in + 90)
      (R := fun st => Inv j st ∧ st.regs 8 = mem (eListPtr + j))
      (Triple.assign
        (fun st hst =>
          Expr.eval_load_of_eq
            (Expr.eval_add (Expr.eval_reg_of_eq hst.2.1) (Expr.eval_reg_of_eq hst.2.2.2.2.2.2.2.2.1)
              haddr_e_w)
            rfl)
        fun st hst => by
          refine ⟨⟨hst.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hst.2.2.2.2.2.2.2.2.2.1,
            hst.2.2.2.2.2.2.2.2.2.2.1, hst.2.2.2.2.2.2.2.2.2.2.2⟩, ?_⟩
          · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.2.1
          · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.2.2.1
          · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.2.2.2.1
          · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.2.2.2.2.1
          · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.2.2.2.2.2.1
          · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.2.2.2.2.2.2.1
          · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.2.2.2.2.2.2.2.1
          · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.2.2.2.2.2.2.2.2.1
          · dsimp; rw [Function.update_self]; exact he_val_mem st hst)
      ?_ (fun _ _ _ _ => by omega)
    -- Step 2: memFill edgeLimbsPtr K_w 0
    refine Triple.seq_normal (T₁ := fun _ => 16 * K_w + 18) (T₂ := fun _ => 75 * K_w + 25 * L_in + 70)
      (R := fun st =>
        (Inv j st ∧ st.regs 8 = mem (eListPtr + j)) ∧ ∀ i < K_w, st.mem (edgeLimbsPtr + i) = 0)
      (Triple.conseq
        (Triple.call (vs := fun _ => [edgeLimbsPtr, K_w, 0]) hmc_fill
          (fun st hst => evalArgs_cons (Expr.eval_reg_of_eq hst.1.2.2.2.2.2.2.1)
            (evalArgs_cons (Expr.eval_reg_of_eq hst.1.2.2.2.2.2.2.2.1)
              (evalArgs_cons (Expr.eval_const h0_w) (evalArgs_nil _ _))))
          (fun st hst v hv => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
            rcases hv with rfl | rfl | rfl
            · exact hed_w0
            · exact hKw_w
            · exact h0_w)
          (fun st hst => ⟨edgeLimbsPtr, K_w, 0, rfl, by omega⟩)
          (fun st _ mem1 _ hst ⟨dst, len, val, heq, _, hfill, hfr⟩ => by
            simp only [List.cons.injEq, and_true] at heq
            rcases heq with ⟨rfl, rfl, rfl⟩
            have hpres_sv : ∀ i < K_w, mem1 (svPtr + i) = st.mem (svPtr + i) := fun i hi =>
              hfr _ (Or.inl (by omega))
            refine ⟨⟨⟨hst.1.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
                fun i hi => by dsimp; rw [hpres_sv i hi]; exact hst.1.2.2.2.2.2.2.2.2.2.1 i hi,
                by dsimp; rw [Num.unsignedVal_congr hpres_sv]; exact hst.1.2.2.2.2.2.2.2.2.2.2.1,
                fun a ha => by
                  dsimp
                  rw [hfr a (by rcases ha with ha | ha <;> [exact Or.inl (by omega); exact Or.inr ha])]
                  exact hst.1.2.2.2.2.2.2.2.2.2.2.2 a ha⟩,
                by dsimp; rw [Function.update_of_ne (by decide)]; exact hst.2⟩, hfill⟩
            · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.2.1
            · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.2.2.1
            · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.2.2.2.1
            · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.2.2.2.2.1
            · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.2.2.2.2.2.1
            · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.2.2.2.2.2.2.1
            · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.2.2.2.2.2.2.2.1
            · dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.2.2.2.2.2.2.2.2.1))
        (fun _ h => h) (fun _ _ h => h)
        (fun st hst => by
          simp only [argsSize, Expr.size, memFillContract, List.getD_eq_getElem?_getD,
            List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
          omega))
      ?_ (fun _ _ _ _ => by omega)
    -- Step 3: reg 9 := wtArr + reg 8 * L_in
    refine Triple.seq_normal (T₁ := fun _ => 6) (T₂ := fun _ => 75 * K_w + 25 * L_in + 50)
      (R := fun st =>
        (Inv j st ∧ st.regs 9 = wtArr + mem (eListPtr + j) * L_in) ∧
          ∀ i < K_w, st.mem (edgeLimbsPtr + i) = 0)
      (Triple.assign
        (fun st hst =>
          Expr.eval_add (Expr.eval_reg_of_eq hst.1.1.2.2.2.1)
            (Expr.eval_mul (Expr.eval_reg_of_eq hst.1.2) (Expr.eval_reg_of_eq hst.1.1.2.2.2.2.1)
              hmul_w)
            (by omega))
        fun st hst =>
          ⟨⟨⟨hst.1.1.1,
            by dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.1.2.1,
            by dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.1.2.2.1,
            by dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.1.2.2.2.1,
            by dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.1.2.2.2.2.1,
            by dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.1.2.2.2.2.2.1,
            by dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.1.2.2.2.2.2.2.1,
            by dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.1.2.2.2.2.2.2.2.1,
            by dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.1.2.2.2.2.2.2.2.2.1,
            hst.1.1.2.2.2.2.2.2.2.2.2.1, hst.1.1.2.2.2.2.2.2.2.2.2.2.1,
            hst.1.1.2.2.2.2.2.2.2.2.2.2.2⟩,
            by dsimp; rw [Function.update_self]⟩,
            hst.2⟩)
      ?_ (fun _ _ _ _ => by omega)
    -- Step 4: memCopy edgeLimbsPtr reg9 L_in
    refine Triple.seq_normal (T₁ := fun _ => 20 * L_in + 18) (T₂ := fun _ => 55 * K_w + 25)
      (R := fun st =>
        Inv j st ∧ Num.Valid st.mem edgeLimbsPtr h K_w ∧
          Num.unsignedVal st.mem edgeLimbsPtr h K_w =
            Num.unsignedVal mem (wtArr + mem (eListPtr + j) * L_in) h L_in)
      (Triple.conseq
        (Triple.call (vs := fun _ => [edgeLimbsPtr, wtArr + mem (eListPtr + j) * L_in, L_in]) hmc_copy
          (fun st hst => evalArgs_cons (Expr.eval_reg_of_eq hst.1.1.2.2.2.2.2.2.1)
            (evalArgs_cons (Expr.eval_reg_of_eq hst.1.2)
              (evalArgs_cons (Expr.eval_reg_of_eq hst.1.1.2.2.2.2.1) (evalArgs_nil _ _))))
          (fun st hst v hv => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
            rcases hv with rfl | rfl | rfl
            · exact hed_w0
            · omega
            · exact hLin_w)
          (fun st hst => ⟨edgeLimbsPtr, wtArr + mem (eListPtr + j) * L_in, L_in,
            rfl, by omega, hsrc_w, Or.inr (by omega)⟩)
          (fun st _ mem2 _ hst ⟨dst, src, len, heq, _, hcp, hfr⟩ => by
            simp only [List.cons.injEq, and_true] at heq
            rcases heq with ⟨rfl, rfl, rfl⟩
            have hmem_src_all : ∀ i < L_in, st.mem (wtArr + mem (eListPtr + j) * L_in + i) =
                mem (wtArr + mem (eListPtr + j) * L_in + i) := fun i hi =>
              hst.1.1.2.2.2.2.2.2.2.2.2.2.2 _ (Or.inl (by omega))
            have hed_val : Num.Valid mem2 edgeLimbsPtr h K_w := by
              refine valid_pad_zero (L := L_in) ?_ ?_
              · intro i hi; rw [hcp i hi, hmem_src_all i hi]; exact hsrc_val i hi
              · intro i hi1 hi2; rw [hfr (edgeLimbsPtr + i) (Or.inr (by omega))]; exact hst.2 i hi2
            have hed_u : Num.unsignedVal mem2 edgeLimbsPtr h K_w =
                Num.unsignedVal mem (wtArr + mem (eListPtr + j) * L_in) h L_in := by
              rw [unsignedVal_pad_zero hLK (fun i hi1 hi2 => by
                rw [hfr (edgeLimbsPtr + i) (Or.inr (by omega))]; exact hst.2 i hi2)]
              exact Num.unsignedVal_congr fun i hi => by
                rw [hcp i hi, hst.1.1.2.2.2.2.2.2.2.2.2.2.2 _ (Or.inl (by omega))]
            have hpres_sv : ∀ i < K_w, mem2 (svPtr + i) = st.mem (svPtr + i) := fun i hi =>
              hfr _ (Or.inl (by omega))
            exact
              ⟨⟨hst.1.1.1,
                by dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.1.2.1,
                by dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.1.2.2.1,
                by dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.1.2.2.2.1,
                by dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.1.2.2.2.2.1,
                by dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.1.2.2.2.2.2.1,
                by dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.1.2.2.2.2.2.2.1,
                by dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.1.2.2.2.2.2.2.2.1,
                by dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.1.2.2.2.2.2.2.2.2.1,
                fun i hi => by dsimp; rw [hpres_sv i hi]; exact hst.1.1.2.2.2.2.2.2.2.2.2.1 i hi,
                by dsimp; rw [Num.unsignedVal_congr hpres_sv]; exact hst.1.1.2.2.2.2.2.2.2.2.2.2.1,
                fun a ha => by
                  dsimp
                  rw [hfr a (by rcases ha with ha | ha <;> [exact Or.inl (by omega); exact Or.inr (by omega)])]
                  exact hst.1.1.2.2.2.2.2.2.2.2.2.2.2 a ha⟩,
                hed_val, hed_u⟩))
        (fun _ h => h) (fun _ _ h => h)
        (fun st hst => by
          simp only [argsSize, Expr.size, memCopyContract, List.getD_eq_getElem?_getD,
            List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
          omega))
      ?_ (fun _ _ _ _ => by omega)
    -- Step 5: addTo svPtr edgeLimbsPtr K_w
    refine Triple.conseq
      (Triple.call (vs := fun _ => [svPtr, edgeLimbsPtr, K_w]) hmc_addTo
        (fun st hst => evalArgs_cons (Expr.eval_reg_of_eq hst.1.2.2.2.2.2.1)
          (evalArgs_cons (Expr.eval_reg_of_eq hst.1.2.2.2.2.2.2.1)
            (evalArgs_cons (Expr.eval_reg_of_eq hst.1.2.2.2.2.2.2.2.1) (evalArgs_nil _ _))))
        (fun st hst v hv => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl
          · exact hsv_w
          · exact hed_w0
          · exact hKw_w)
        (fun st hst => ⟨svPtr, edgeLimbsPtr, K_w, rfl,
          hh1, hw2h, by omega, hed_w, Or.inl hsv_ed,
          hst.1.2.2.2.2.2.2.2.2.2.1, hst.2.1⟩)
        (fun st _ mem3 _ hst ⟨dst, src, len, heq, _, hval3, hu3, _, hfr⟩ => by
          simp only [List.cons.injEq, and_true] at heq
          rcases heq with ⟨rfl, rfl, rfl⟩
          have hu_eq : Num.unsignedVal mem3 svPtr h K_w = partialSum (j + 1) := by
            rw [hu3, hst.1.2.2.2.2.2.2.2.2.2.2.1, hst.2.2]
            have hadd_sum : partialSum j + Num.unsignedVal mem (wtArr + mem (eListPtr + j) * L_in) h L_in =
                partialSum (j + 1) := by
              dsimp only [partialSum]; rw [Finset.sum_range_succ]
            rw [hadd_sum, Nat.mod_eq_of_lt (by omega)]
          refine ⟨⟨by omega,
            by dsimp; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hst.1.2.1,
            by dsimp; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hst.1.2.2.1,
            by dsimp; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hst.1.2.2.2.1,
            by dsimp; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hst.1.2.2.2.2.1,
            by dsimp; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hst.1.2.2.2.2.2.1,
            by dsimp; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hst.1.2.2.2.2.2.2.1,
            by dsimp; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hst.1.2.2.2.2.2.2.2.1,
            by dsimp; rw [Function.update_self],
            hval3, hu_eq,
            fun a ha => by
              dsimp
              rw [hfr a (by rcases ha with ha | ha <;> [exact Or.inl ha; exact Or.inr (by omega)])]
              exact hst.1.2.2.2.2.2.2.2.2.2.2.2 a ha⟩,
            by dsimp; rw [Function.update_of_ne (by decide)]; exact hst.1.2.2.2.2.2.2.2.2.1⟩))
      (fun _ h => h) (fun _ _ h => h)
      (fun st hst => by
        simp only [argsSize, Expr.size, addToContract, List.getD_eq_getElem?_getD,
          List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
        omega)
  have hret : Triple w p (Inv m0) (.ret (.const 0))
      (retPost fun u st' => u = 0 ∧ Num.Valid st'.mem svPtr h K_w ∧
        Num.unsignedVal st'.mem svPtr h K_w = partialSum m0 ∧
        (∀ a, a < svPtr ∨ edgeLimbsPtr + K_w ≤ a → st'.mem a = mem a)) fun _ => 2 :=
    Triple.ret (fun _ _ => Expr.eval_const h0_w) fun _ hst =>
      ⟨rfl, hst.2.2.2.2.2.2.2.2.2.1, hst.2.2.2.2.2.2.2.2.2.2.1, hst.2.2.2.2.2.2.2.2.2.2.2⟩
  refine Triple.conseq
    (Triple.seq_normal hinit (Triple.seq_normal hloop hret (fun _ _ _ _ => le_rfl))
      (fun _ _ _ _ => le_rfl))
    (fun st hst => hst)
    (fun o st' hpost => by
      cases o with
      | normal => exact False.elim hpost
      | returned _ => exact ⟨eListPtr, m0, wtArr, L_in, svPtr, edgeLimbsPtr, K_w, rfl, hpost.1, hpost.2.1, hpost.2.2.1, hpost.2.2.2⟩)
    (fun st hst => by
      subst hst
      simp only [sumWeightsContract, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some, Nat.sub_zero]
      nlinarith)

end MinCostFlow.LSF.Program
