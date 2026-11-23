module

public import MinCostFlow.LSF.Program.InitTreeQNatBase
public import MinCostFlow.LSF.Program.InitTreeWeights
public import MinCostFlow.LSF.Program.InitTreeCopy
public import MinCostFlow.LSF.Program.InitArena
public import WordRAM.Tactic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Computing Edge Multiplicities and `q_nat` Limbs in `InitTree` (`InitTreeQNat`)

Defines and verifies `initTreeQNatProc`: given `G₀`'s active edge list `eListPtr`, fixed-point
lengths `lenArr` and weights `wtArr`, limb width `K_w = kWidthOf m0 L_in`, and the scratch arena
starting at `qNatPtr`, computes `S_v`, `S_v - 1`, `m0`, all multiplicities
`multPtr[j] = ⌈m0 * v_int / S_v⌉ = edgeMult G₀ v e`, and quotient limbs
`qNatPtr[j] = ⌊edgeMult * 2^(h*(L_in+4)) / ℓ_int⌋`, using
`[lsstHeap, lsstHeap + m0 * multQNatStepSpace K_w)` as temporary workspace and zeroing it
afterwards so `ZeroFrom mem' lsstHeap` holds on return.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF

@[expose] public section

/-! ## Division Loop Helper and Main Contract Verification -/

private structure QNatLoopInv (G₀ : MGraph) (v : ℕ → ℝ) (eList : List ℕ)
    (eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap
     K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr
     S_v h : ℕ) (mem0 : ℕ → ℕ) (j : ℕ) (st : State) : Prop where
  j_le : j ≤ m0
  regs : QNatRegs eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap
    K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr st
  r17 : st.regs 17 = j
  r18 : st.regs 18 = lsstHeap + j * multQNatStepSpace K_w
  sv_val : Num.Valid st.mem svPtr h K_w
  sv_u : Num.unsignedVal st.mem svPtr h K_w = S_v
  sv1_val : Num.Valid st.mem svMinusOnePtr h K_w
  sv1_u : Num.unsignedVal st.mem svMinusOnePtr h K_w = S_v - 1
  m0_val : Num.Valid st.mem m0LimbsPtr h K_w
  m0_u : Num.unsignedVal st.mem m0LimbsPtr h K_w = m0
  entries : ∀ t < j,
    let e := eList.getD t 0
    let ℓ_int := (Num.intVal mem0 (lenArr + e * L_in) h L_in).toNat
    st.mem (multPtr + t) = edgeMult G₀ v e ∧
    Num.Valid st.mem (qNatPtr + t * K_q) h K_q ∧
    Num.unsignedVal st.mem (qNatPtr + t * K_q) h K_q =
      (edgeMult G₀ v e * 2 ^ (h * (L_in + 4))) / ℓ_int
  hz : ZeroFrom st.mem (lsstHeap + j * multQNatStepSpace K_w)
  hframe : ∀ a < qNatPtr, st.mem a = mem0 a

private lemma qNatLoopInv_upd_hi {G₀ : MGraph} {v : ℕ → ℝ} {eList : List ℕ}
    {eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap
     K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr
     S_v h : ℕ} {mem0 : ℕ → ℕ} {j r v' : ℕ} {st : State}
    (hr : 19 ≤ r)
    (hL : QNatLoopInv G₀ v eList eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap
      K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr S_v h mem0 j st) :
    QNatLoopInv G₀ v eList eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap
      K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr S_v h mem0 j
      { st with regs := Function.update st.regs r v' } :=
  ⟨hL.j_le, qNatRegs_upd_hi hL.regs (by omega),
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hL.r17,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hL.r18,
   hL.sv_val, hL.sv_u, hL.sv1_val, hL.sv1_u, hL.m0_val, hL.m0_u, hL.entries, hL.hz, hL.hframe⟩

private lemma initTreeQNat_loop {w h f_mq : ℕ} {p : Program}
    (hmq : MeetsContract w p f_mq (multQNatStepContract w h))
    {G₀ : MGraph} {v : ℕ → ℝ} {eList : List ℕ}
    {eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap S_v : ℕ}
    {mem0 : ℕ → ℕ}
    (hw1 : 1 < 2 ^ w) (hh1 : 1 ≤ h) (hw3h : 3 * h + 2 ≤ w) (hpow2h_w : 2 ^ h < 2 ^ w)
    (hLin1 : 1 ≤ L_in) (hLK : L_in ≤ K_w) (hm0 : 1 ≤ m0) (hm02_w : 2 * m0 < 2 ^ w)
    (hS_pos : 1 ≤ S_v) (hS_half : 2 * S_v < Num.capacity h K_w / 2)
    (hEL_len : eList.length = m0) (hEL_mem : ∀ e, e ∈ eList ↔ e ∈ G₀.E)
    (hEL_at : ListAt mem0 eListPtr eList)
    (heL_q : eListPtr + m0 ≤ qNatPtr)
    (hlen_q : ∀ e ∈ G₀.E, lenArr + e * L_in + L_in ≤ qNatPtr)
    (hwt_q : ∀ e ∈ G₀.E, wtArr + e * L_in + L_in ≤ qNatPtr)
    (harena_w : qNatPtr + m0 * (K_w + 6) + m0 + 5 * K_w + 2 * (K_w + 6) ≤ lsstHeap)
    (hhp_bd : lsstHeap + m0 * multQNatStepSpace K_w < 2 ^ w)
    (hlen_ok : ∀ e ∈ G₀.E, Num.Valid mem0 (lenArr + e * L_in) h L_in)
    (hwt_ok : ∀ e ∈ G₀.E, Num.Valid mem0 (wtArr + e * L_in) h L_in)
    (hz0 : ZeroFrom mem0 lsstHeap)
    (hstep_arith : ∀ (j : ℕ) (hj : j < m0),
      let e := eList[j]'(by omega)
      let v_int := Num.unsignedVal mem0 (wtArr + e * L_in) h L_in
      let ℓ_int := Num.unsignedVal mem0 (lenArr + e * L_in) h L_in
      ℓ_int = (Num.intVal mem0 (lenArr + e * L_in) h L_in).toNat ∧
      1 ≤ v_int ∧ 2 * v_int < Num.capacity h L_in ∧
      1 ≤ ℓ_int ∧ 2 * ℓ_int < Num.capacity h L_in ∧
      2 * (m0 * v_int + (S_v - 1)) < Num.capacity h K_w ∧
      (m0 * v_int + S_v - 1) / S_v = edgeMult G₀ v e ∧
      1 ≤ edgeMult G₀ v e ∧ edgeMult G₀ v e ≤ m0 ∧
      4 * m0 + 2 < Num.capacity h (K_w + 6 - (L_in + 4)) ∧
      4 * (2 * m0) * 2 ^ (h * (L_in + 4)) < Num.capacity h (K_w + 6) / 2) :
    let K_q := K_w + 6
    let multPtr := qNatPtr + m0 * K_q
    let svPtr := multPtr + m0
    let svMinusOnePtr := svPtr + K_w
    let m0LimbsPtr := svMinusOnePtr + K_w
    let oneLimbsPtr := m0LimbsPtr + K_w
    let edgeLimbsPtr := oneLimbsPtr + K_w
    let numerPtr := edgeLimbsPtr + K_w
    let lenQPtr := numerPtr + K_q
    Triple w p
      (fun st =>
        QNatRegs eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap
          K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr st ∧
        st.regs 18 = lsstHeap ∧
        Num.Valid st.mem svPtr h K_w ∧ Num.unsignedVal st.mem svPtr h K_w = S_v ∧
        Num.Valid st.mem svMinusOnePtr h K_w ∧ Num.unsignedVal st.mem svMinusOnePtr h K_w = S_v - 1 ∧
        Num.Valid st.mem m0LimbsPtr h K_w ∧ Num.unsignedVal st.mem m0LimbsPtr h K_w = m0 ∧
        ∀ a, (a < svPtr ∨ edgeLimbsPtr + K_w ≤ a) → st.mem a = mem0 a)
      (initTreeQNatLoopStmt f_mq h)
      (normalPost (QNatLoopInv G₀ v eList eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap
        K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr S_v h mem0 m0))
      fun _ => m0 * (800 * (K_w + 6) ^ 2 + 2500 * (K_w + 6) + 2069) + 7 := by
  intro K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr
  change qNatPtr + m0 * K_q + m0 + 5 * K_w + 2 * K_q ≤ lsstHeap at harena_w
  let Inv := QNatLoopInv G₀ v eList eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap
    K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr S_v h mem0
  have hL_w : L_in < 2 ^ w := by omega
  have hm0_w : m0 < 2 ^ w := by omega
  have hKw_w : K_w < 2 ^ w := by omega
  have hbase_w : 2 * h + 2 ≤ w := by omega
  have hinit : ∀ st,
      (QNatRegs eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap
        K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr st ∧
      st.regs 18 = lsstHeap ∧
      Num.Valid st.mem svPtr h K_w ∧ Num.unsignedVal st.mem svPtr h K_w = S_v ∧
      Num.Valid st.mem svMinusOnePtr h K_w ∧ Num.unsignedVal st.mem svMinusOnePtr h K_w = S_v - 1 ∧
      Num.Valid st.mem m0LimbsPtr h K_w ∧ Num.unsignedVal st.mem m0LimbsPtr h K_w = m0 ∧
      ∀ a, (a < svPtr ∨ edgeLimbsPtr + K_w ≤ a) → st.mem a = mem0 a) →
      (Expr.const 0).eval w st = some 0 ∧
        Inv 0 { st with regs := Function.update st.regs 17 0 } := by
    intro st hst
    have hfr0 := hst.2.2.2.2.2.2.2.2
    have hlt_sv : ∀ a < qNatPtr, a < svPtr := fun a ha => by omega
    have hz_lsst : ZeroFrom st.mem (lsstHeap + 0 * multQNatStepSpace K_w) := by
      rw [Nat.zero_mul, Nat.add_zero]
      intro a ha
      have hle : edgeLimbsPtr + K_w ≤ a := by omega
      rw [hfr0 a (Or.inr hle)]
      exact hz0 a ha
    refine ⟨Expr.eval_const (by omega), ⟨Nat.zero_le _, qNatRegs_upd_hi hst.1 (by omega),
      by dsimp; rw [Function.update_self],
      by dsimp; rw [Function.update_of_ne (by omega), Nat.zero_mul, Nat.add_zero]; exact hst.2.1,
      hst.2.2.1, hst.2.2.2.1, hst.2.2.2.2.1, hst.2.2.2.2.2.1,
      hst.2.2.2.2.2.2.1, hst.2.2.2.2.2.2.2.1,
      fun _ ht => False.elim (Nat.not_lt_zero _ ht),
      hz_lsst,
      fun a ha => hfr0 a (Or.inl (hlt_sv a ha))⟩⟩
  have hbody : ∀ j, 0 ≤ j → j < m0 →
      Triple w p (Inv j)
        (.assign 19 (.load (.bin .add (.reg 0) (.reg 17))) ;;
         .assign 20 (.bin .mul (.reg 19) (.reg 3)) ;;
         .assign 21 (.bin .add (.reg 2) (.reg 20)) ;;
         .assign 22 (.bin .add (.reg 1) (.reg 20)) ;;
         .assign 23 (.bin .add (.reg 6) (.bin .mul (.reg 17) (.reg 8))) ;;
         .assign 24 (.bin .add (.reg 9) (.reg 17)) ;;
         .call 18 f_mq
           [.reg 21, .reg 22, .reg 23, .reg 24, .reg 10, .reg 11, .reg 12, .reg 14,
            .reg 15, .reg 16, .reg 3, .reg 5, .reg 18, .const (2 ^ h)])
        (normalPost fun st₁ =>
          Inv (j + 1) { st₁ with regs := Function.update st₁.regs 17 (j + 1) } ∧ st₁.regs 17 = j)
        (fun _ => 800 * (K_w + 6) ^ 2 + 2500 * (K_w + 6) + 2060) := by
    intro j _ hj
    have hj_len : j < eList.length := by omega
    let e := eList[j]'hj_len
    have he_mem : e ∈ G₀.E := (hEL_mem e).mp (List.getElem_mem hj_len)
    have hlen_bd := hlen_q e he_mem
    have hwt_bd := hwt_q e he_mem
    have heL_j_w : eListPtr + j < 2 ^ w := by omega
    have he_le : e ≤ e * L_in := Nat.le_mul_of_pos_right _ hLin1
    have he_w : e < 2 ^ w := by omega
    have heL_mul_w : e * L_in < 2 ^ w := by omega
    have hwtE_w : wtArr + e * L_in < 2 ^ w := by omega
    have hlenE_w : lenArr + e * L_in < 2 ^ w := by omega
    have hjKq_le : (j + 1) * K_q ≤ m0 * K_q := Nat.mul_le_mul_right K_q (by omega)
    have hjKq_mul : (j + 1) * K_q = j * K_q + K_q := Nat.add_one_mul j K_q
    have hjKq_w : j * K_q < 2 ^ w := by omega
    have hqOut_w : qNatPtr + j * K_q < 2 ^ w := by omega
    have hmultOut_w : multPtr + j < 2 ^ w := by omega
    have hp_j_le : (j + 1) * multQNatStepSpace K_w ≤ m0 * multQNatStepSpace K_w :=
      Nat.mul_le_mul_right _ (by omega)
    have hm1_sp : (j + 1) * multQNatStepSpace K_w = j * multQNatStepSpace K_w + multQNatStepSpace K_w :=
      Nat.add_one_mul _ _
    have hp_j_w : lsstHeap + j * multQNatStepSpace K_w < 2 ^ w := by omega
    have hp_next_w : lsstHeap + j * multQNatStepSpace K_w + multQNatStepSpace K_w < 2 ^ w := by omega
    obtain ⟨hℓ_eq, hv1, hv2, hℓ1, hℓ2, hnum_lt, hceil_eq, hmb1, hmb2, hk_rem, hq_cap⟩ :=
      hstep_arith j hj
    have a19 : Triple w p (Inv j) (.assign 19 (.load (.bin .add (.reg 0) (.reg 17))))
        (normalPost fun st => Inv j st ∧ st.regs 19 = e) fun _ => 5 :=
      Triple.assign
        (fun _ hst => Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hst.regs.r0) (Expr.eval_reg_of_eq hst.r17) heL_j_w)
          (by rw [hst.hframe (eListPtr + j) (by omega), hEL_at j hj_len]))
        fun _ hst => ⟨qNatLoopInv_upd_hi (by omega) hst, by dsimp; rw [Function.update_self]⟩
    have a20 : Triple w p (fun st => Inv j st ∧ st.regs 19 = e)
        (.assign 20 (.bin .mul (.reg 19) (.reg 3)))
        (normalPost fun st => Inv j st ∧ st.regs 20 = e * L_in) fun _ => 4 :=
      Triple.assign
        (fun _ hst => Expr.eval_mul (Expr.eval_reg_of_eq hst.2) (Expr.eval_reg_of_eq hst.1.regs.r3) heL_mul_w)
        fun _ hst => ⟨qNatLoopInv_upd_hi (by omega) hst.1, by dsimp; rw [Function.update_self]⟩
    have a21 : Triple w p (fun st => Inv j st ∧ st.regs 20 = e * L_in)
        (.assign 21 (.bin .add (.reg 2) (.reg 20)))
        (normalPost fun st => Inv j st ∧ st.regs 20 = e * L_in ∧ st.regs 21 = wtArr + e * L_in) fun _ => 4 :=
      Triple.assign
        (fun _ hst => Expr.eval_add (Expr.eval_reg_of_eq hst.1.regs.r2) (Expr.eval_reg_of_eq hst.2) hwtE_w)
        fun _ hst => ⟨qNatLoopInv_upd_hi (by omega) hst.1,
          by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2, by dsimp; rw [Function.update_self]⟩
    have a22 : Triple w p (fun st => Inv j st ∧ st.regs 20 = e * L_in ∧ st.regs 21 = wtArr + e * L_in)
        (.assign 22 (.bin .add (.reg 1) (.reg 20)))
        (normalPost fun st => Inv j st ∧ st.regs 21 = wtArr + e * L_in ∧ st.regs 22 = lenArr + e * L_in)
        fun _ => 4 :=
      Triple.assign
        (fun _ hst => Expr.eval_add (Expr.eval_reg_of_eq hst.1.regs.r1) (Expr.eval_reg_of_eq hst.2.1) hlenE_w)
        fun _ hst => ⟨qNatLoopInv_upd_hi (by omega) hst.1,
          by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2, by dsimp; rw [Function.update_self]⟩
    have a23 : Triple w p (fun st => Inv j st ∧ st.regs 21 = wtArr + e * L_in ∧ st.regs 22 = lenArr + e * L_in)
        (.assign 23 (.bin .add (.reg 6) (.bin .mul (.reg 17) (.reg 8))))
        (normalPost fun st => Inv j st ∧ st.regs 21 = wtArr + e * L_in ∧ st.regs 22 = lenArr + e * L_in ∧
          st.regs 23 = qNatPtr + j * K_q) fun _ => 6 :=
      Triple.assign (P := fun st => Inv j st ∧ st.regs 21 = wtArr + e * L_in ∧ st.regs 22 = lenArr + e * L_in)
        (val := fun _ => qNatPtr + j * K_q)
        (fun _ hst => Expr.eval_add (Expr.eval_reg_of_eq hst.1.regs.r6)
          (Expr.eval_mul (Expr.eval_reg_of_eq hst.1.r17) (Expr.eval_reg_of_eq hst.1.regs.r8) hjKq_w) hqOut_w)
        fun _ hst => ⟨qNatLoopInv_upd_hi (by omega) hst.1,
          by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.1,
          by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2,
          by dsimp; rw [Function.update_self]⟩
    have a24 : Triple w p
        (fun st => Inv j st ∧ st.regs 21 = wtArr + e * L_in ∧ st.regs 22 = lenArr + e * L_in ∧
          st.regs 23 = qNatPtr + j * K_q)
        (.assign 24 (.bin .add (.reg 9) (.reg 17)))
        (normalPost fun st => Inv j st ∧ st.regs 21 = wtArr + e * L_in ∧ st.regs 22 = lenArr + e * L_in ∧
          st.regs 23 = qNatPtr + j * K_q ∧ st.regs 24 = multPtr + j) fun _ => 4 :=
      Triple.assign
        (fun _ hst => Expr.eval_add (Expr.eval_reg_of_eq hst.1.regs.r9) (Expr.eval_reg_of_eq hst.1.r17) hmultOut_w)
        fun _ hst => ⟨qNatLoopInv_upd_hi (by omega) hst.1,
          by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.1,
          by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.1,
          by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.2,
          by dsimp; rw [Function.update_self]⟩
    have cstep : Triple w p
        (fun st => Inv j st ∧ st.regs 21 = wtArr + e * L_in ∧ st.regs 22 = lenArr + e * L_in ∧
          st.regs 23 = qNatPtr + j * K_q ∧ st.regs 24 = multPtr + j)
        (.call 18 f_mq
          [.reg 21, .reg 22, .reg 23, .reg 24, .reg 10, .reg 11, .reg 12, .reg 14,
           .reg 15, .reg 16, .reg 3, .reg 5, .reg 18, .const (2 ^ h)])
        (normalPost fun st₁ =>
          Inv (j + 1) { st₁ with regs := Function.update st₁.regs 17 (j + 1) } ∧ st₁.regs 17 = j)
        fun _ => 800 * (K_w + 6) ^ 2 + 2500 * (K_w + 6) + 2020 := by
      refine Triple.conseq
        (Triple.call (vs := fun _ => [wtArr + e * L_in, lenArr + e * L_in, qNatPtr + j * K_q, multPtr + j,
            svPtr, svMinusOnePtr, m0LimbsPtr, edgeLimbsPtr, numerPtr, lenQPtr,
            L_in, K_w, lsstHeap + j * multQNatStepSpace K_w, 2 ^ h]) hmq
          (fun _ hst => evalArgs_cons (Expr.eval_reg_of_eq hst.2.1)
            (evalArgs_cons (Expr.eval_reg_of_eq hst.2.2.1)
              (evalArgs_cons (Expr.eval_reg_of_eq hst.2.2.2.1)
                (evalArgs_cons (Expr.eval_reg_of_eq hst.2.2.2.2)
                  (evalArgs_cons (Expr.eval_reg_of_eq hst.1.regs.r10)
                    (evalArgs_cons (Expr.eval_reg_of_eq hst.1.regs.r11)
                      (evalArgs_cons (Expr.eval_reg_of_eq hst.1.regs.r12)
                        (evalArgs_cons (Expr.eval_reg_of_eq hst.1.regs.r14)
                          (evalArgs_cons (Expr.eval_reg_of_eq hst.1.regs.r15)
                            (evalArgs_cons (Expr.eval_reg_of_eq hst.1.regs.r16)
                              (evalArgs_cons (Expr.eval_reg_of_eq hst.1.regs.r3)
                                (evalArgs_cons (Expr.eval_reg_of_eq hst.1.regs.r5)
                                  (evalArgs_cons (Expr.eval_reg_of_eq hst.1.r18)
                                    (evalArgs_cons (Expr.eval_const hpow2h_w) (evalArgs_nil _ _)))))))))))))))
          (fun _ _ v hv => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
            rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
              first | assumption | omega)
          (fun st hst => by
            have hL := hst.1
            have hwt_s := valid_unsignedVal_congr (hwt_ok e he_mem) fun i hi =>
              hL.hframe (wtArr + e * L_in + i) (by omega)
            have hlen_s := valid_unsignedVal_congr (hlen_ok e he_mem) fun i hi =>
              hL.hframe (lenArr + e * L_in + i) (by omega)
            refine ⟨wtArr + e * L_in, lenArr + e * L_in, qNatPtr + j * K_q, multPtr + j,
              svPtr, svMinusOnePtr, m0LimbsPtr, edgeLimbsPtr, numerPtr, lenQPtr,
              L_in, K_w, lsstHeap + j * multQNatStepSpace K_w, 2 ^ h, m0, S_v,
              Num.unsignedVal mem0 (wtArr + e * L_in) h L_in,
              Num.unsignedVal mem0 (lenArr + e * L_in) h L_in,
              rfl, rfl, hh1, hw3h, hLin1, hLK, hm0, hm02_w, hS_pos, hv1, hℓ1, hℓ2, hv2,
              by omega, hnum_lt, by rw [hceil_eq]; exact Nat.le_trans hmb2 (by omega), hk_rem, hq_cap,
              by omega, by omega, by omega, by omega, rfl.le, rfl.le, by omega, by omega,
              by omega, by omega, hp_next_w,
              hwt_s.1, hwt_s.2, hlen_s.1, hlen_s.2,
              hL.sv_val, hL.sv_u, hL.sv1_val, hL.sv1_u,
              hL.m0_val, hL.m0_u, hL.hz⟩)
          (fun st _ mem1 _ hst ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, m0_e, Sv_e, v_e, ℓ_e,
              heq, hret_hp, hv_eq, hℓ_eq_e, hsv_eq, hm0_eq, hmult_val, hq_val, hq_u, hz_hp, hfr⟩ => by
            simp only [List.cons.injEq, and_true] at heq
            rcases heq with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            have hL := hst.1
            have hwt_same := valid_unsignedVal_congr (hwt_ok e he_mem) fun i hi =>
              hL.hframe (wtArr + e * L_in + i) (by omega)
            have hlen_same := valid_unsignedVal_congr (hlen_ok e he_mem) fun i hi =>
              hL.hframe (lenArr + e * L_in + i) (by omega)
            have hm0_same : m0_e = m0 := by rw [← hm0_eq, hL.m0_u]
            have hsv_same : Sv_e = S_v := by rw [← hsv_eq, hL.sv_u]
            have hv_same : v_e = Num.unsignedVal mem0 (wtArr + e * L_in) h L_in := by
              rw [← hv_eq, hwt_same.2]
            have hℓ_same : ℓ_e = Num.unsignedVal mem0 (lenArr + e * L_in) h L_in := by
              rw [← hℓ_eq_e, hlen_same.2]
            subst hm0_same hsv_same hv_same hℓ_same
            have hsv_p := valid_unsignedVal_congr hL.sv_val fun i hi =>
              hfr (svPtr + i) (by omega) (Or.inr (by omega)) (by omega)
            have hsv1_p := valid_unsignedVal_congr hL.sv1_val fun i hi =>
              hfr (svMinusOnePtr + i) (by omega) (Or.inr (by omega)) (by omega)
            have hm0_p := valid_unsignedVal_congr hL.m0_val fun i hi =>
              hfr (m0LimbsPtr + i) (by omega) (Or.inr (by omega)) (by omega)
            dsimp only
            refine ⟨⟨by omega,
              ⟨by dsimp; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hL.regs.r0,
               by dsimp; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hL.regs.r1,
               by dsimp; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hL.regs.r2,
               by dsimp; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hL.regs.r3,
               by dsimp; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hL.regs.r4,
               by dsimp; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hL.regs.r5,
               by dsimp; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hL.regs.r6,
               by dsimp; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hL.regs.r7,
               by dsimp; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hL.regs.r8,
               by dsimp; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hL.regs.r9,
               by dsimp; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hL.regs.r10,
               by dsimp; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hL.regs.r11,
               by dsimp; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hL.regs.r12,
               by dsimp; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hL.regs.r13,
               by dsimp; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hL.regs.r14,
               by dsimp; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hL.regs.r15,
               by dsimp; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hL.regs.r16⟩,
              by dsimp; rw [Function.update_self],
              by dsimp; rw [Function.update_of_ne (by omega), Function.update_self, hret_hp, hm1_sp, Nat.add_assoc],
              hsv_p.1, hsv_p.2.trans hL.sv_u,
              hsv1_p.1, hsv1_p.2.trans hL.sv1_u,
              hm0_p.1, hm0_p.2.trans hL.m0_u,
              fun t ht => by
                dsimp only
                rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
                · have htp1 : (t + 1) * K_q ≤ j * K_q := Nat.mul_le_mul_right K_q ht
                  have ht_m : (t + 1) * K_q = t * K_q + K_q := Nat.add_one_mul t K_q
                  have hprev := hL.entries t ht
                  have hqt := valid_unsignedVal_congr hprev.2.1 fun i hi =>
                    hfr (qNatPtr + t * K_q + i) (by omega) (Or.inl (by omega)) (by omega)
                  refine ⟨?_, hqt.1, hqt.2.trans hprev.2.2⟩
                  rw [hfr (multPtr + t) (by omega) (Or.inr (by omega)) (by omega)]
                  exact hprev.1
                · rw [List.getD_eq_getElem _ _ hj_len]
                  refine ⟨?_, hq_val, ?_⟩
                  · rw [hmult_val, hceil_eq]
                  · rw [hq_u, hceil_eq, hℓ_eq],
              by dsimp only; rw [hm1_sp, ← Nat.add_assoc, ← hret_hp]; exact hz_hp,
              fun a ha => by
                dsimp only
                rw [hfr a (by omega) (Or.inl (by omega)) (by omega)]
                exact hL.hframe a ha⟩,
              by rw [Function.update_of_ne (by omega)]; exact hL.r17⟩))
        (fun _ hst => hst) (fun _ _ hst => hst) fun _ _ => by
          simp only [multQNatStepContract, argsSize, Expr.size, List.getD_eq_getElem?_getD,
            List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
          rw [Nat.mul_assoc, ← Nat.pow_two]
          omega
    exact (Triple.seq_normal_const a19 (Triple.seq_normal_const a20 (Triple.seq_normal_const a21
      (Triple.seq_normal_const a22 (Triple.seq_normal_const a23 (Triple.seq_normal_const a24 cstep)))))).mono_cost
      fun _ _ => by omega
  have hloop := Triple.forRange_const (p := p) (r := 17) (lo := .const 0) (hi := .reg 4)
    (body :=
      (.assign 19 (.load (.bin .add (.reg 0) (.reg 17))) ;;
       .assign 20 (.bin .mul (.reg 19) (.reg 3)) ;;
       .assign 21 (.bin .add (.reg 2) (.reg 20)) ;;
       .assign 22 (.bin .add (.reg 1) (.reg 20)) ;;
       .assign 23 (.bin .add (.reg 6) (.bin .mul (.reg 17) (.reg 8))) ;;
       .assign 24 (.bin .add (.reg 9) (.reg 17)) ;;
       .call 18 f_mq
         [.reg 21, .reg 22, .reg 23, .reg 24, .reg 10, .reg 11, .reg 12, .reg 14,
          .reg 15, .reg 16, .reg 3, .reg 5, .reg 18, .const (2 ^ h)]))
    (P := fun st =>
      QNatRegs eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap
        K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr st ∧
      st.regs 18 = lsstHeap ∧
      Num.Valid st.mem svPtr h K_w ∧ Num.unsignedVal st.mem svPtr h K_w = S_v ∧
      Num.Valid st.mem svMinusOnePtr h K_w ∧ Num.unsignedVal st.mem svMinusOnePtr h K_w = S_v - 1 ∧
      Num.Valid st.mem m0LimbsPtr h K_w ∧ Num.unsignedVal st.mem m0LimbsPtr h K_w = m0 ∧
      ∀ a, (a < svPtr ∨ edgeLimbsPtr + K_w ≤ a) → st.mem a = mem0 a)
    (Inv := Inv)
    (800 * (K_w + 6) ^ 2 + 2500 * (K_w + 6) + 2060)
    0 m0 (Nat.zero_le _) hw1 (fun _ => hm0_w)
    hinit
    (fun _ _ _ _ hi => hi.r17)
    (fun _ _ _ _ hi => Expr.eval_reg_of_eq hi.regs.r4)
    hbody
  change Triple w p _ (initTreeQNatLoopStmt f_mq h) (normalPost (Inv m0)) _ at hloop
  exact hloop.mono_cost fun _ _ => by
    dsimp only [Expr.size]
    set x := 800 * (K_w + 6) ^ 2 + 2500 * (K_w + 6)
    rw [Nat.sub_zero]

theorem initTreeQNat_meetsContract {w b K_AN h f_sw f_mq f : ℕ} {p : Program} {G₀ : MGraph}
    {v : ℕ → ℝ}
    (hp : p.HasAt (b + 2) (lsfSharedProcs b K_AN h))
    (hsw : MeetsContract w p f_sw (sumWeightsContract w h))
    (hmq : MeetsContract w p f_mq (multQNatStepContract w h))
    (hproc : p.procs[f]? = some (initTreeQNatProc b h f_sw f_mq)) :
    MeetsContract w p f (initTreeQNatContract w h G₀ v) := by
  refine meetsContract_of_triple hproc ?_
  intro args mem0 pos _ hpre
  rcases hpre with ⟨ℓ₀, eList, eListPtr, lenArr, wtArr, L_in, m0, K_w, qNatPtr, lsstHeap, P_fp,
    rfl, hh1, hw3h, hLin1, hdivP, hG_val, hm_card, hm0, hm02_w, hKw_eq, hEL_len, hEL_nd, hEL_mem,
    hEL_at, heL_q, hlen_q, hwt_q, harena_w, hhp_bd, hlen_ok, hwt_ok, hz0⟩
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 * h + 2 ≤ w := by omega
  have h16_w : 16 ≤ 2 ^ w := by
    have : 5 ≤ w := by omega
    exact le_trans (by decide : 16 ≤ 2 ^ 5) (Nat.pow_le_pow_right (by norm_num) this)
  have h6_w : 6 < 2 ^ w := by omega
  have hpow2h_w : 2 ^ h < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hlsst_w : lsstHeap < 2 ^ w := by omega
  have hLK : L_in ≤ K_w := by rw [hKw_eq]; dsimp only [WideWord.kWidthOf]; omega
  obtain ⟨_, _, hcap_lt⟩ := cap_kWidth_bounds hm0 hh1 (L_in := L_in)
  rw [← hKw_eq] at hcap_lt
  have hm0_half : m0 < Num.capacity h K_w := by
    have h1 : 1 ≤ Num.capacity h L_in := by rw [Num.capacity_eq_two_pow]; exact Nat.two_pow_pos _
    have h2 : Num.capacity h K_w / 2 ≤ Num.capacity h K_w := Nat.div_le_self _ _
    have h3 : m0 ≤ 4 * m0 * Num.capacity h L_in := by nlinarith
    omega
  have hwt_q_j : ∀ j < m0, wtArr + mem0 (eListPtr + j) * L_in + L_in ≤ qNatPtr := by
    intro j hj; have hj_len : j < eList.length := by omega
    rw [hEL_at j hj_len]; exact hwt_q _ ((hEL_mem _).mp (List.getElem_mem hj_len))
  have hwt_val_j : ∀ j < m0, Num.Valid mem0 (wtArr + mem0 (eListPtr + j) * L_in) h L_in := by
    intro j hj; have hj_len : j < eList.length := by omega
    rw [hEL_at j hj_len]; exact (hwt_ok _ ((hEL_mem _).mp (List.getElem_mem hj_len))).1
  have heL_w : eListPtr < 2 ^ w := by omega
  have hwt_w : wtArr < 2 ^ w := by have := hwt_q_j 0 hm0; omega
  have hlen_w : lenArr < 2 ^ w := by
    have he0 : eList[0]'(by omega) ∈ G₀.E := (hEL_mem _).mp (List.getElem_mem _)
    have := hlen_q _ he0; omega
  have hL_w : L_in < 2 ^ w := by omega
  have hm0_w : m0 < 2 ^ w := by omega
  have hKw_w : K_w < 2 ^ w := by omega
  set K_q := K_w + 6
  set multPtr := qNatPtr + m0 * K_q
  set svPtr := multPtr + m0
  set svMinusOnePtr := svPtr + K_w
  set m0LimbsPtr := svMinusOnePtr + K_w
  set oneLimbsPtr := m0LimbsPtr + K_w
  set edgeLimbsPtr := oneLimbsPtr + K_w
  set numerPtr := edgeLimbsPtr + K_w
  set lenQPtr := numerPtr + K_q
  set S_v_expr := ∑ j ∈ Finset.range m0, Num.unsignedVal mem0 (wtArr + mem0 (eListPtr + j) * L_in) h L_in
  have hS_eq : S_v_expr = ∑ j ∈ Finset.range m0, Num.unsignedVal mem0 (wtArr + (eList.getD j 0) * L_in) h L_in := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj; rw [List.getD_eq_getElem _ _ (by omega), hEL_at j (by omega)]
  obtain ⟨hS_pos, hS_half, hstep_arith⟩ := qNat_pre_arith hh1 hLin1 hm_card hm0 hKw_eq hEL_len
    hEL_nd hEL_mem hlen_ok hwt_ok
  rw [← hS_eq] at hS_pos hS_half hstep_arith
  have hass := initTreeQNat_assigns (w := w) (eListPtr := eListPtr) (lenArr := lenArr) (wtArr := wtArr)
    (L_in := L_in) (m0 := m0) (K_w := K_w) (qNatPtr := qNatPtr) (lsstHeap := lsstHeap) (pos := pos)
    (p := p) (mem0 := mem0) harena_w hlsst_w h6_w
  have hset := initTreeQNat_setup_calls hp hsw hw1 hh1 hw3h h16_w hLin1 hLK hm0 (lenArr := lenArr)
    heL_q hwt_q_j hwt_val_j hS_pos hS_half hm0_half harena_w hlsst_w heL_w hwt_w
  have hloop := initTreeQNat_loop hmq (lenArr := lenArr) (wtArr := wtArr) hw1 hh1 hw3h hpow2h_w hLin1 hLK
    hm0 hm02_w hS_pos hS_half hEL_len hEL_mem hEL_at heL_q hlen_q hwt_q harena_w hhp_bd
    (fun e he => (hlen_ok e he).1) (fun e he => (hwt_ok e he).1) hz0 hstep_arith
  have hmc_fill := lsfMemFill_meetsContract hw1 hp
  set hp_end := lsstHeap + m0 * multQNatStepSpace K_w
  have h0_w : 0 < 2 ^ w := by omega
  have hfill : Triple w p
      (QNatLoopInv G₀ v eList eListPtr lenArr wtArr L_in m0 K_w qNatPtr lsstHeap
        K_q multPtr svPtr svMinusOnePtr m0LimbsPtr oneLimbsPtr edgeLimbsPtr numerPtr lenQPtr S_v_expr h mem0 m0)
      (.call 19 (lsfBaseUtils b + idxUtilMemFill) [.reg 7, .bin .sub (.reg 18) (.reg 7), .const 0])
      (normalPost fun st =>
        (∀ t < m0,
          let e := eList.getD t 0
          let ℓ_int := (Num.intVal mem0 (lenArr + e * L_in) h L_in).toNat
          st.mem (multPtr + t) = edgeMult G₀ v e ∧
          Num.Valid st.mem (qNatPtr + t * K_q) h K_q ∧
          Num.unsignedVal st.mem (qNatPtr + t * K_q) h K_q =
            (edgeMult G₀ v e * 2 ^ (h * (L_in + 4))) / ℓ_int) ∧
        ZeroFrom st.mem lsstHeap ∧
        ∀ a < qNatPtr, st.mem a = mem0 a)
      fun _ => 16 * (m0 * multQNatStepSpace K_w) + 30 := by
    refine Triple.conseq
      (Triple.call (vs := fun _ => [lsstHeap, m0 * multQNatStepSpace K_w, 0]) hmc_fill
        (fun _ hst => evalArgs_cons (Expr.eval_reg_of_eq hst.regs.r7)
          (evalArgs_cons (by
            have hev := Expr.eval_sub (Expr.eval_reg_of_eq hst.r18) (Expr.eval_reg_of_eq hst.regs.r7) hhp_bd
            simpa [hp_end] using hev)
            (evalArgs_cons (Expr.eval_const h0_w) (evalArgs_nil _ _))))
        (fun _ _ v hv => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with rfl | rfl | rfl <;> omega)
        (fun _ _ => ⟨lsstHeap, m0 * multQNatStepSpace K_w, 0, rfl, hhp_bd⟩)
        (fun st _ mem1 _ hst ⟨_, _, _, heq, _, hzero_rng, hfr⟩ => by
          simp only [List.cons.injEq, and_true] at heq; rcases heq with ⟨rfl, rfl, rfl⟩
          dsimp only
          refine ⟨fun t ht => ?_, fun a ha => ?_, fun a ha => ?_⟩
          · have htp1 : (t + 1) * K_q ≤ m0 * K_q := Nat.mul_le_mul_right K_q ht
            have ht_m : (t + 1) * K_q = t * K_q + K_q := Nat.add_one_mul t K_q
            have hprev := hst.entries t ht
            have hqt := valid_unsignedVal_congr hprev.2.1 fun i hi =>
              hfr (qNatPtr + t * K_q + i) (Or.inl (by omega))
            refine ⟨?_, hqt.1, hqt.2.trans hprev.2.2⟩
            rw [hfr (multPtr + t) (Or.inl (by omega))]
            exact hprev.1
          · by_cases hal : a < lsstHeap + m0 * multQNatStepSpace K_w
            · have ha_sub : a - lsstHeap < m0 * multQNatStepSpace K_w := by omega
              have hadd : lsstHeap + (a - lsstHeap) = a := by omega
              rw [← hadd]
              exact hzero_rng (a - lsstHeap) ha_sub
            · rw [hfr a (Or.inr (by omega))]
              exact hst.hz a (by omega)
          · rw [hfr a (Or.inl (by omega))]
            exact hst.hframe a ha))
      (fun _ hst => hst) (fun _ _ hst => hst) fun _ _ => by
        simp only [memFillContract, argsSize, Expr.size, List.getD_eq_getElem?_getD,
          List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
        omega
  have hret : Triple w p
      (fun st =>
        (∀ t < m0,
          let e := eList.getD t 0
          let ℓ_int := (Num.intVal mem0 (lenArr + e * L_in) h L_in).toNat
          st.mem (multPtr + t) = edgeMult G₀ v e ∧
          Num.Valid st.mem (qNatPtr + t * K_q) h K_q ∧
          Num.unsignedVal st.mem (qNatPtr + t * K_q) h K_q =
            (edgeMult G₀ v e * 2 ^ (h * (L_in + 4))) / ℓ_int) ∧
        ZeroFrom st.mem lsstHeap ∧
        ∀ a < qNatPtr, st.mem a = mem0 a)
      (.ret (.const 0))
      (retPost fun ret st => ret = 0 ∧
        (∀ t < m0,
          let e := eList.getD t 0
          let ℓ_int := (Num.intVal mem0 (lenArr + e * L_in) h L_in).toNat
          st.mem (multPtr + t) = edgeMult G₀ v e ∧
          Num.Valid st.mem (qNatPtr + t * K_q) h K_q ∧
          Num.unsignedVal st.mem (qNatPtr + t * K_q) h K_q =
            (edgeMult G₀ v e * 2 ^ (h * (L_in + 4))) / ℓ_int) ∧
        ZeroFrom st.mem lsstHeap ∧
        ∀ a < qNatPtr, st.mem a = mem0 a) fun _ => 2 :=
    Triple.ret (fun _ _ => Expr.eval_const h0_w) fun _ hst => ⟨rfl, hst⟩
  have hfull := Triple.seq_normal_const hass
    (Triple.seq_normal_const hset
      (Triple.seq_normal_const hloop
        (Triple.seq_normal_const hfill hret)))
  refine Triple.conseq hfull (fun _ hst => hst)
    (fun o st hst => by
      cases o with
      | normal => exact False.elim hst
      | returned _ =>
        exact ⟨eList, eListPtr, lenArr, wtArr, L_in, m0, K_w, qNatPtr, lsstHeap,
          rfl, hst.1, hEL_len, hEL_nd, hEL_mem, hEL_at, hst.2.1, hst.2.2.1, hst.2.2.2⟩)
    (fun _ _ => by
      simp only [initTreeQNatContract, initTreeQNatCost, List.getD_eq_getElem?_getD,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      nlinarith)

end

end MinCostFlow.LSF.Program
