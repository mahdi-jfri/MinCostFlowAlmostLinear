module

public import MinCostFlow.Machine.WideWord.LSSTDecodeOut
import WordRAM.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Verification of `simDecodeProc`

This file defines `simDecodeSpace` and `simDecodeCost`, provides `runs_seq_call_stmt` for
calling compiled guest procedures, and proves `simDecode_runs`, showing that
`simDecodeProc` builds the trie for `G_aug.encode`, runs the simulated `[AN19]` program `Q`
on all-false randomness, reads out the resulting edge indices, and decodes them into
`(origEdges, bridgePairs)` matching `decodeAN19Output`.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM

/-! ### Space, cost, and general helper lemmas -/

def simDecodeSpace (Q : Program) (Vcnt m_aug L_sim h cost : ℕ) : ℕ :=
  let encLen := 2 + 3 * m_aug
  5 + (1 + Vcnt) * L_sim + L_sim + encLen * (L_sim * 2 ^ h + L_sim) +
    simScale Q * L_sim * 2 ^ h * (cost + encLen + 1)

def simDecodeCost (Q : Program) (w' Vcnt m_aug inactLen L_sim cost : ℕ) : ℕ :=
  let encLen := 2 + 3 * m_aug
  (95 * L_sim + 115) * encLen + simScale Q * L_sim * w' * (cost + encLen + 1) +
    (70 * L_sim + 80) * (Vcnt - 1) + decodeOutCost (Vcnt - 1) inactLen L_sim + 200

lemma runs_seq_call_stmt {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f cBody : ℕ}
    {args : List Expr} {s₂ : Stmt} {st st_b : State} {vs : List ℕ} {body : Stmt}
    {u k T : ℕ} {Q : Outcome → State → Prop}
    (hf : p.procs[f]? = some body)
    (he : evalArgs w st args = some vs)
    (hbody : Runs w p ω body (startState vs st.mem st.pos) (.returned u) st_b cBody)
    (hnext : ∃ o st'' c, Runs w p ω s₂
      { st_b with regs := Function.update st.regs r u } o st'' c ∧
      Q o st'' ∧ k + (argsSize args + cBody + 2) + c ≤ T) :
    ∃ o st'' c, Runs w p ω ((.call r f args) ;; s₂) st o st'' c ∧ Q o st'' ∧ k + c ≤ T := by
  obtain ⟨o, st'', c, hrun2, hq, hc⟩ := hnext
  have hcall : Runs w p ω (.call r f args) st .normal { st_b with regs := Function.update st.regs r u }
      (argsSize args + cBody + 1) :=
    runs_call_iff.mpr ⟨vs, body, .returned u, st_b, cBody, he, hf, hbody, rfl, rfl, rfl⟩
  refine ⟨o, st'', argsSize args + cBody + 1 + c + 1,
    runs_seq_iff.mpr (Or.inr ⟨_, argsSize args + cBody + 1, c, hcall, hrun2, rfl⟩), hq, by omega⟩

lemma gAug_encode_length (G : IndexedGraph) (V_list B : List ℕ) (mult w_orig : ℕ → ℕ) :
    (buildGAug G V_list B mult w_orig).encode.length =
      2 + 3 * (((nonloopEdges G).map mult).sum + B.length) := by
  dsimp only [Cited.WGraph.encode, Cited.WGraph.m, buildGAug]
  simp only [List.length_cons, List.length_flatMap, List.length_append, List.length_map,
    List.length_nil]
  have h1 : (List.map (fun _ => 3)
      ((nonloopEdges G).flatMap (fun e => List.replicate (mult e)
        (V_list.idxOf (G.tail e), V_list.idxOf (G.head e), w_orig e)) ++
        B.map (fun b => (0, V_list.idxOf b, 1)))).sum =
      3 * (((nonloopEdges G).map mult).sum + B.length) := by
    rw [List.map_append, List.sum_append]
    have hl : (List.map (fun _ => 3)
        ((nonloopEdges G).flatMap (fun e => List.replicate (mult e)
          (V_list.idxOf (G.tail e), V_list.idxOf (G.head e), w_orig e)))).sum =
        3 * ((nonloopEdges G).map mult).sum := by
      have hm : (List.map (fun _ => 3)
          ((nonloopEdges G).flatMap (fun e => List.replicate (mult e)
            (V_list.idxOf (G.tail e), V_list.idxOf (G.head e), w_orig e)))) =
          List.replicate ((nonloopEdges G).map mult).sum 3 := by
        rw [List.map_const', List.length_flatMap]
        congr 1
        simp [List.length_replicate]
      rw [hm, List.sum_replicate, smul_eq_mul, Nat.mul_comm]
    have hr : (List.map (fun _ => 3) (B.map fun b => (0, V_list.idxOf b, 1))).sum =
        3 * B.length := by
      rw [List.map_const', List.length_map, List.sum_replicate, smul_eq_mul, Nat.mul_comm]
    rw [hl, hr, Nat.mul_add]
  have hsum_eq : (List.map (fun _ : ℕ × ℕ × ℕ => 0 + 1 + 1 + 1)
      ((nonloopEdges G).flatMap (fun e => List.replicate (mult e)
        (V_list.idxOf (G.tail e), V_list.idxOf (G.head e), w_orig e)) ++
        B.map (fun b => (0, V_list.idxOf b, 1)))).sum =
      3 * (((nonloopEdges G).map mult).sum + B.length) := h1
  rw [hsum_eq]
  omega

/-! ### Register bundle -/

private structure SimDRegs (s : State) (Vcnt m_aug m₁ B_len bArr inactLen inactArr r₀ arrPtr
    L_sim h h2pow origsPtr outOrigPtr outBridgePtr outHdrPtr heap : ℕ) : Prop where
  r0 : s.regs 0 = Vcnt
  r1 : s.regs 1 = m_aug
  r2 : s.regs 2 = m₁
  r3 : s.regs 3 = B_len
  r4 : s.regs 4 = bArr
  r5 : s.regs 5 = inactLen
  r6 : s.regs 6 = inactArr
  r7 : s.regs 7 = r₀
  r8 : s.regs 8 = arrPtr
  r9 : s.regs 9 = L_sim
  r10 : s.regs 10 = h
  r11 : s.regs 11 = h2pow
  r12 : s.regs 12 = origsPtr
  r13 : s.regs 13 = outOrigPtr
  r14 : s.regs 14 = outBridgePtr
  r15 : s.regs 15 = outHdrPtr
  r16 : s.regs 16 = heap

private lemma simDRegs_upd {s st' : State} {Vcnt m_aug m₁ B_len bArr inactLen inactArr r₀ arrPtr
    L_sim h h2pow origsPtr outOrigPtr outBridgePtr outHdrPtr heap r v : ℕ}
    (hrg : SimDRegs s Vcnt m_aug m₁ B_len bArr inactLen inactArr r₀ arrPtr L_sim h h2pow origsPtr outOrigPtr outBridgePtr outHdrPtr heap)
    (hreg : st'.regs = Function.update s.regs r v) (hr : 17 ≤ r) :
    SimDRegs st' Vcnt m_aug m₁ B_len bArr inactLen inactArr r₀ arrPtr L_sim h h2pow origsPtr outOrigPtr outBridgePtr outHdrPtr heap :=
  ⟨by rw [hreg, Function.update_of_ne (by omega)]; exact hrg.r0,
   by rw [hreg, Function.update_of_ne (by omega)]; exact hrg.r1,
   by rw [hreg, Function.update_of_ne (by omega)]; exact hrg.r2,
   by rw [hreg, Function.update_of_ne (by omega)]; exact hrg.r3,
   by rw [hreg, Function.update_of_ne (by omega)]; exact hrg.r4,
   by rw [hreg, Function.update_of_ne (by omega)]; exact hrg.r5,
   by rw [hreg, Function.update_of_ne (by omega)]; exact hrg.r6,
   by rw [hreg, Function.update_of_ne (by omega)]; exact hrg.r7,
   by rw [hreg, Function.update_of_ne (by omega)]; exact hrg.r8,
   by rw [hreg, Function.update_of_ne (by omega)]; exact hrg.r9,
   by rw [hreg, Function.update_of_ne (by omega)]; exact hrg.r10,
   by rw [hreg, Function.update_of_ne (by omega)]; exact hrg.r11,
   by rw [hreg, Function.update_of_ne (by omega)]; exact hrg.r12,
   by rw [hreg, Function.update_of_ne (by omega)]; exact hrg.r13,
   by rw [hreg, Function.update_of_ne (by omega)]; exact hrg.r14,
   by rw [hreg, Function.update_of_ne (by omega)]; exact hrg.r15,
   by rw [hreg, Function.update_of_ne (by omega)]; exact hrg.r16⟩

private lemma simDRegs_of_eq {s st' : State} {Vcnt m_aug m₁ B_len bArr inactLen inactArr r₀ arrPtr
    L_sim h h2pow origsPtr outOrigPtr outBridgePtr outHdrPtr heap : ℕ}
    (hrg : SimDRegs s Vcnt m_aug m₁ B_len bArr inactLen inactArr r₀ arrPtr L_sim h h2pow origsPtr outOrigPtr outBridgePtr outHdrPtr heap)
    (hreg : st'.regs = s.regs) :
    SimDRegs st' Vcnt m_aug m₁ B_len bArr inactLen inactArr r₀ arrPtr L_sim h h2pow origsPtr outOrigPtr outBridgePtr outHdrPtr heap :=
  ⟨by rw [hreg]; exact hrg.r0, by rw [hreg]; exact hrg.r1, by rw [hreg]; exact hrg.r2,
   by rw [hreg]; exact hrg.r3, by rw [hreg]; exact hrg.r4, by rw [hreg]; exact hrg.r5,
   by rw [hreg]; exact hrg.r6, by rw [hreg]; exact hrg.r7, by rw [hreg]; exact hrg.r8,
   by rw [hreg]; exact hrg.r9, by rw [hreg]; exact hrg.r10, by rw [hreg]; exact hrg.r11,
   by rw [hreg]; exact hrg.r12, by rw [hreg]; exact hrg.r13, by rw [hreg]; exact hrg.r14,
   by rw [hreg]; exact hrg.r15, by rw [hreg]; exact hrg.r16⟩

/-! ### Setup prefix helper for `simDecodeProc` -/

private lemma simDecode_setup_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {pos₀ : ℕ}
    {Vcnt m_aug m₁ B_len bArr inactLen inactArr r₀ arrPtr L_sim h h2pow origsPtr
      outOrigPtr outBridgePtr outHdrPtr heap k T : ℕ}
    {s₂ : Stmt} {Q_post : Outcome → State → Prop}
    (hw3 : 3 ≤ w)
    (hhp₀_w : heap + (5 + (1 + Vcnt) * L_sim) < 2 ^ w)
    (henc_w : 2 + 3 * m_aug < 2 ^ w)
    (hV_w : Vcnt < 2 ^ w)
    (hz_heap : ZeroFrom mem heap)
    (h1 : 1 ≤ Vcnt) (h2 : 1 ≤ L_sim)
    (hnext : ∀ s10,
      SimDRegs s10 Vcnt m_aug m₁ B_len bArr inactLen inactArr r₀ arrPtr L_sim h h2pow
        origsPtr outOrigPtr outBridgePtr outHdrPtr heap →
      s10.regs 18 = 2 + 3 * m_aug →
      s10.regs 19 = heap + 5 →
      s10.regs 20 = Vcnt - 1 →
      s10.regs 21 = heap + 5 + L_sim →
      s10.regs 22 = heap + 5 + 2 * L_sim →
      s10.mem (heap + 1) = heap + 5 + (1 + Vcnt) * L_sim →
      s10.mem (heap + 2) = L_sim →
      s10.mem (heap + 3) = h →
      s10.mem (heap + 4) = h2pow →
      (∀ q < heap, s10.mem q = mem q) →
      ZeroFrom s10.mem (heap + 5 + (1 + Vcnt) * L_sim) →
      ∃ o st' c, Runs w p ω s₂ s10 o st' c ∧ Q_post o st' ∧ (k + 62) + c ≤ T) :
    ∃ o st' c,
      Runs w p ω
        (Stmt.assign 17 (.bin .add (.reg 16) (.bin .add (.const 5)
            (.bin .mul (.bin .add (.const 1) (.reg 0)) (.reg 9)))) ;;
          Stmt.assign 18 (.bin .add (.const 2) (.bin .mul (.const 3) (.reg 1))) ;;
          Stmt.assign 19 (.bin .add (.reg 16) (.const 5)) ;;
          Stmt.assign 20 (.bin .sub (.reg 0) (.const 1)) ;;
          Stmt.assign 21 (.bin .add (.reg 19) (.reg 9)) ;;
          Stmt.assign 22 (.bin .add (.reg 21) (.reg 9)) ;;
          Stmt.store (.bin .add (.reg 16) (.const 1)) (.reg 17) ;;
          Stmt.store (.bin .add (.reg 16) (.const 2)) (.reg 9) ;;
          Stmt.store (.bin .add (.reg 16) (.const 3)) (.reg 10) ;;
          Stmt.store (.bin .add (.reg 16) (.const 4)) (.reg 11) ;; s₂)
        (startState [Vcnt, m_aug, m₁, B_len, bArr, inactLen, inactArr, r₀,
          arrPtr, L_sim, h, h2pow, origsPtr, outOrigPtr, outBridgePtr, outHdrPtr, heap] mem pos₀)
        o st' c ∧ Q_post o st' ∧ k + c ≤ T := by
  have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow (by linarith only [hw3])
  have h2_w : 2 < 2 ^ w := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by linarith only [hw3] : 2 ≤ w))
  have h3_w : 3 < 2 ^ w := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by linarith only [hw3] : 2 ≤ w))
  have h4_w : 4 < 2 ^ w := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw3)
  have h5_w : 5 < 2 ^ w := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw3)
  have hV_mul : 1 + Vcnt ≤ (1 + Vcnt) * L_sim := Nat.le_mul_of_pos_right _ h2
  have hL_mul : L_sim ≤ (1 + Vcnt) * L_sim := Nat.le_mul_of_pos_left _ (by linarith only [h1])
  have h2L : 2 * L_sim ≤ (1 + Vcnt) * L_sim := Nat.mul_le_mul_right _ (by linarith only [h1])
  have hhp5 : heap + 5 ≤ heap + 5 + (1 + Vcnt) * L_sim := by linarith only [h2L, h2]
  have hV1_w : 1 + Vcnt < 2 ^ w := by linarith only [hhp₀_w, hV_mul]
  have hV1L_w : (1 + Vcnt) * L_sim < 2 ^ w := by linarith only [hhp₀_w]
  have hhp₀_off_w : 5 + (1 + Vcnt) * L_sim < 2 ^ w := by linarith only [hhp₀_w]
  have hm3_w : 3 * m_aug < 2 ^ w := by linarith only [henc_w]
  have hret_w : heap + 5 < 2 ^ w := by linarith only [hhp₀_w, hhp5]
  have hkey_w : heap + 5 + L_sim < 2 ^ w := by linarith only [hhp₀_w, h2L, h2]
  have houtLimbs_w : (heap + 5 + L_sim) + L_sim < 2 ^ w := by linarith only [hhp₀_w, h2L, h2]
  have hheap1_w : heap + 1 < 2 ^ w := by linarith only [hhp₀_w, hhp5]
  have hheap2_w : heap + 2 < 2 ^ w := by linarith only [hhp₀_w, hhp5]
  have hheap3_w : heap + 3 < 2 ^ w := by linarith only [hhp₀_w, hhp5]
  have hheap4_w : heap + 4 < 2 ^ w := by linarith only [hhp₀_w, hhp5]
  have hreg0 : SimDRegs
      (startState [Vcnt, m_aug, m₁, B_len, bArr, inactLen, inactArr, r₀, arrPtr, L_sim, h,
        h2pow, origsPtr, outOrigPtr, outBridgePtr, outHdrPtr, heap] mem pos₀)
      Vcnt m_aug m₁ B_len bArr inactLen inactArr r₀ arrPtr L_sim h h2pow
      origsPtr outOrigPtr outBridgePtr outHdrPtr heap := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [startState]
  refine runs_seq_assign_step
    (Expr.eval_add (Expr.eval_reg_of_eq hreg0.r16)
      (Expr.eval_add (Expr.eval_const h5_w)
        (Expr.eval_mul (Expr.eval_add (Expr.eval_const hw1) (Expr.eval_reg_of_eq hreg0.r0) hV1_w)
          (Expr.eval_reg_of_eq hreg0.r9) hV1L_w) hhp₀_off_w) hhp₀_w)
    rfl fun s1 hm1 _ hr1 => ?_
  have hrg1 := simDRegs_upd hreg0 hr1 (by decide)
  have hs1_17 : s1.regs 17 = heap + (5 + (1 + Vcnt) * L_sim) := by rw [hr1, Function.update_self]
  refine runs_seq_assign_step
    (Expr.eval_add (Expr.eval_const h2_w)
      (Expr.eval_mul (Expr.eval_const h3_w) (Expr.eval_reg_of_eq hrg1.r1) hm3_w) henc_w)
    rfl fun s2 hm2 _ hr2 => ?_
  have hrg2 := simDRegs_upd hrg1 hr2 (by decide)
  have hs2_17 : s2.regs 17 = heap + (5 + (1 + Vcnt) * L_sim) := by
    rw [hr2, Function.update_of_ne (by decide)]; exact hs1_17
  have hs2_18 : s2.regs 18 = 2 + 3 * m_aug := by rw [hr2, Function.update_self]
  refine runs_seq_assign_step
    (Expr.eval_add (Expr.eval_reg_of_eq hrg2.r16) (Expr.eval_const h5_w) hret_w)
    rfl fun s3 hm3 _ hr3 => ?_
  have hrg3 := simDRegs_upd hrg2 hr3 (by decide)
  have hs3_17 : s3.regs 17 = heap + (5 + (1 + Vcnt) * L_sim) := by
    rw [hr3, Function.update_of_ne (by decide)]; exact hs2_17
  have hs3_18 : s3.regs 18 = 2 + 3 * m_aug := by
    rw [hr3, Function.update_of_ne (by decide)]; exact hs2_18
  have hs3_19 : s3.regs 19 = heap + 5 := by rw [hr3, Function.update_self]
  refine runs_seq_assign_step
    (Expr.eval_sub (Expr.eval_reg_of_eq hrg3.r0) (Expr.eval_const hw1) hV_w)
    rfl fun s4 hm4 _ hr4 => ?_
  have hrg4 := simDRegs_upd hrg3 hr4 (by decide)
  have hs4_17 : s4.regs 17 = heap + (5 + (1 + Vcnt) * L_sim) := by
    rw [hr4, Function.update_of_ne (by decide)]; exact hs3_17
  have hs4_18 : s4.regs 18 = 2 + 3 * m_aug := by
    rw [hr4, Function.update_of_ne (by decide)]; exact hs3_18
  have hs4_19 : s4.regs 19 = heap + 5 := by
    rw [hr4, Function.update_of_ne (by decide)]; exact hs3_19
  have hs4_20 : s4.regs 20 = Vcnt - 1 := by rw [hr4, Function.update_self]
  refine runs_seq_assign_step
    (Expr.eval_add (Expr.eval_reg_of_eq hs4_19) (Expr.eval_reg_of_eq hrg4.r9) hkey_w)
    rfl fun s5 hm5 _ hr5 => ?_
  have hrg5 := simDRegs_upd hrg4 hr5 (by decide)
  have hs5_17 : s5.regs 17 = heap + (5 + (1 + Vcnt) * L_sim) := by
    rw [hr5, Function.update_of_ne (by decide)]; exact hs4_17
  have hs5_18 : s5.regs 18 = 2 + 3 * m_aug := by
    rw [hr5, Function.update_of_ne (by decide)]; exact hs4_18
  have hs5_19 : s5.regs 19 = heap + 5 := by
    rw [hr5, Function.update_of_ne (by decide)]; exact hs4_19
  have hs5_20 : s5.regs 20 = Vcnt - 1 := by
    rw [hr5, Function.update_of_ne (by decide)]; exact hs4_20
  have hs5_21 : s5.regs 21 = heap + 5 + L_sim := by rw [hr5, Function.update_self]
  refine runs_seq_assign_step
    (Expr.eval_add (Expr.eval_reg_of_eq hs5_21) (Expr.eval_reg_of_eq hrg5.r9) houtLimbs_w)
    rfl fun s6 hm6 _ hr6 => ?_
  have hrg6 := simDRegs_upd hrg5 hr6 (by decide)
  have hs6_17 : s6.regs 17 = heap + (5 + (1 + Vcnt) * L_sim) := by
    rw [hr6, Function.update_of_ne (by decide)]; exact hs5_17
  have hs6_18 : s6.regs 18 = 2 + 3 * m_aug := by
    rw [hr6, Function.update_of_ne (by decide)]; exact hs5_18
  have hs6_19 : s6.regs 19 = heap + 5 := by
    rw [hr6, Function.update_of_ne (by decide)]; exact hs5_19
  have hs6_20 : s6.regs 20 = Vcnt - 1 := by
    rw [hr6, Function.update_of_ne (by decide)]; exact hs5_20
  have hs6_21 : s6.regs 21 = heap + 5 + L_sim := by
    rw [hr6, Function.update_of_ne (by decide)]; exact hs5_21
  have hs6_22 : s6.regs 22 = heap + 5 + 2 * L_sim := by
    rw [hr6, Function.update_self]; linarith only
  refine runs_seq_store_step
    (Expr.eval_add (Expr.eval_reg_of_eq hrg6.r16) (Expr.eval_const hw1) hheap1_w)
    (Expr.eval_reg_of_eq hs6_17) rfl fun s7 hm7 hr7 _ => ?_
  have hrg7 := simDRegs_of_eq hrg6 hr7
  refine runs_seq_store_step
    (Expr.eval_add (Expr.eval_reg_of_eq hrg7.r16) (Expr.eval_const h2_w) hheap2_w)
    (Expr.eval_reg_of_eq hrg7.r9) rfl fun s8 hm8 hr8 _ => ?_
  have hrg8 := simDRegs_of_eq hrg7 hr8
  refine runs_seq_store_step
    (Expr.eval_add (Expr.eval_reg_of_eq hrg8.r16) (Expr.eval_const h3_w) hheap3_w)
    (Expr.eval_reg_of_eq hrg8.r10) rfl fun s9 hm9 hr9 _ => ?_
  have hrg9 := simDRegs_of_eq hrg8 hr9
  refine runs_seq_store_step
    (Expr.eval_add (Expr.eval_reg_of_eq hrg9.r16) (Expr.eval_const h4_w) hheap4_w)
    (Expr.eval_reg_of_eq hrg9.r11) rfl fun s10 hm10 hr10 _ => ?_
  have hrg10 := simDRegs_of_eq hrg9 hr10
  have hs10_18 : s10.regs 18 = 2 + 3 * m_aug := by rw [hr10, hr9, hr8, hr7]; exact hs6_18
  have hs10_19 : s10.regs 19 = heap + 5 := by rw [hr10, hr9, hr8, hr7]; exact hs6_19
  have hs10_20 : s10.regs 20 = Vcnt - 1 := by rw [hr10, hr9, hr8, hr7]; exact hs6_20
  have hs10_21 : s10.regs 21 = heap + 5 + L_sim := by rw [hr10, hr9, hr8, hr7]; exact hs6_21
  have hs10_22 : s10.regs 22 = heap + 5 + 2 * L_sim := by rw [hr10, hr9, hr8, hr7]; exact hs6_22
  have hs6_mem : s6.mem = mem := hm6.trans (hm5.trans (hm4.trans (hm3.trans (hm2.trans hm1))))
  have hs10_lt_heap : ∀ q < heap, s10.mem q = mem q := fun q hq => by
    rw [hm10, Function.update_of_ne (Nat.ne_of_lt (by linarith only [hq])),
      hm9, Function.update_of_ne (Nat.ne_of_lt (by linarith only [hq])),
      hm8, Function.update_of_ne (Nat.ne_of_lt (by linarith only [hq])),
      hm7, Function.update_of_ne (Nat.ne_of_lt (by linarith only [hq])), hs6_mem]
  have hs10_z : ZeroFrom s10.mem (heap + 5 + (1 + Vcnt) * L_sim) := fun q hq => by
    rw [hm10, Function.update_of_ne (Nat.ne_of_gt (by linarith only [hq, hhp5])),
      hm9, Function.update_of_ne (Nat.ne_of_gt (by linarith only [hq, hhp5])),
      hm8, Function.update_of_ne (Nat.ne_of_gt (by linarith only [hq, hhp5])),
      hm7, Function.update_of_ne (Nat.ne_of_gt (by linarith only [hq, hhp5])), hs6_mem]
    exact hz_heap q (by linarith only [hq, hhp5])
  have hs10_c1 : s10.mem (heap + 1) = heap + 5 + (1 + Vcnt) * L_sim := by
    rw [hm10, Function.update_of_ne (by linarith only),
      hm9, Function.update_of_ne (by linarith only),
      hm8, Function.update_of_ne (by linarith only),
      hm7, Function.update_self, Nat.add_assoc]
  have hs10_c2 : s10.mem (heap + 2) = L_sim := by
    rw [hm10, Function.update_of_ne (by linarith only),
      hm9, Function.update_of_ne (by linarith only), hm8, Function.update_self]
  have hs10_c3 : s10.mem (heap + 3) = h := by
    rw [hm10, Function.update_of_ne (by linarith only), hm9, Function.update_self]
  have hs10_c4 : s10.mem (heap + 4) = h2pow := by
    rw [hm10, Function.update_self]
  obtain ⟨o, st', c, hrun_s, hq_s, hc_s⟩ :=
    hnext s10 hrg10 hs10_18 hs10_19 hs10_20 hs10_21 hs10_22 hs10_c1 hs10_c2 hs10_c3 hs10_c4
      hs10_lt_heap hs10_z
  exact ⟨o, st', _, hrun_s, hq_s, by dsimp only [Expr.size]; linarith only [hc_s]⟩

/-! ### Full simulation + decoding correctness (`simDecode_runs`) -/

theorem simDecode_runs {w w' h arithBase packBase wrapBase simBase encodeBase : ℕ}
    {p Q : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {pos₀ : ℕ}
    (hSim : p.HasAt simBase (compile Q simBase))
    (hWrap : p.HasAt wrapBase (wrapperModule (simBase + 1) (simBase + 19)))
    (hEnc : p.HasAt encodeBase (encodeDecodeModule arithBase packBase wrapBase simBase encodeBase))
    (hPack : p.HasAt packBase (Num.packWordModule packBase h))
    (G : IndexedGraph) (V_list B : List ℕ) (mult w_orig : ℕ → ℕ)
    (bArr inactArr arrPtr L_sim origsPtr outOrigPtr outBridgePtr outHdrPtr heap : ℕ)
    (out : List ℕ) (cost : ℕ)
    (hh : 1 ≤ h) (hw2 : 2 * h + 2 ≤ w) (hL1 : 1 ≤ L_sim)
    (hw'1 : 1 ≤ w') (hw'_lh : w' ≤ L_sim * h)
    (hV_pos : 1 ≤ V_list.length) (hV_fit : V_list.length - 1 ≤ 2 ^ (L_sim * h))
    (hm_fit : 2 + 3 * (((nonloopEdges G).map mult).sum + B.length) ≤ 2 ^ (L_sim * h))
    (hx_lt : ∀ v ∈ (buildGAug G V_list B mult w_orig).encode, v < 2 ^ w')
    (hout_len : out.length = V_list.length - 1) (hout_lt : ∀ v ∈ out, v < 2 ^ w)
    (hrun : RunsTo w' Q (buildGAug G V_list B mult w_orig).encode (fun _ => false) out cost)
    (hheap_w : heap + simDecodeSpace Q V_list.length (((nonloopEdges G).map mult).sum + B.length) L_sim h cost < 2 ^ w)
    (hz_heap : ZeroFrom mem heap)
    (harr_lt : arrPtr + (2 + 3 * (((nonloopEdges G).map mult).sum + B.length)) * L_sim ≤ heap)
    (hb_lt : bArr + B.length ≤ heap)
    (hin_lt : inactArr + (inactiveVertsList G.n V_list).length ≤ heap)
    (horig_lt : origsPtr + ((nonloopEdges G).map mult).sum ≤ heap)
    (hoo_lt : outOrigPtr + (V_list.length - 1) ≤ heap)
    (hob_lt : outBridgePtr + 2 * ((V_list.length - 1) + (inactiveVertsList G.n V_list).length) ≤ heap)
    (hoh_lt : outHdrPtr + 2 ≤ heap)
    (hd_ob : DisjointRanges outOrigPtr (V_list.length - 1) outBridgePtr
      (2 * ((V_list.length - 1) + (inactiveVertsList G.n V_list).length)))
    (hd_oh : DisjointRanges outOrigPtr (V_list.length - 1) outHdrPtr 2)
    (hd_bh : DisjointRanges outBridgePtr
      (2 * ((V_list.length - 1) + (inactiveVertsList G.n V_list).length)) outHdrPtr 2)
    (hd_oo : DisjointRanges outOrigPtr (V_list.length - 1) origsPtr ((nonloopEdges G).map mult).sum)
    (hd_oB : DisjointRanges outOrigPtr (V_list.length - 1) bArr B.length)
    (hd_oi : DisjointRanges outOrigPtr (V_list.length - 1) inactArr (inactiveVertsList G.n V_list).length)
    (hd_bo : DisjointRanges outBridgePtr
      (2 * ((V_list.length - 1) + (inactiveVertsList G.n V_list).length)) origsPtr ((nonloopEdges G).map mult).sum)
    (hd_bB : DisjointRanges outBridgePtr
      (2 * ((V_list.length - 1) + (inactiveVertsList G.n V_list).length)) bArr B.length)
    (hd_bi : DisjointRanges outBridgePtr
      (2 * ((V_list.length - 1) + (inactiveVertsList G.n V_list).length)) inactArr (inactiveVertsList G.n V_list).length)
    (hd_ho : DisjointRanges outHdrPtr 2 origsPtr ((nonloopEdges G).map mult).sum)
    (hd_hB : DisjointRanges outHdrPtr 2 bArr B.length)
    (hd_hi : DisjointRanges outHdrPtr 2 inactArr (inactiveVertsList G.n V_list).length)
    (hr₀_w : V_list.headD 0 < 2 ^ w)
    (hOrig_lt : ∀ x ∈ origOfCopy G mult, x < 2 ^ w)
    (hB_lt : ∀ x ∈ B, x < 2 ^ w)
    (hIn_lt : ∀ x ∈ inactiveVertsList G.n V_list, x < 2 ^ w)
    (henc_limbs : ∀ i (hi : i < (buildGAug G V_list B mult w_orig).encode.length),
      LimbsAt mem (arrPtr + i * L_sim) L_sim h ((buildGAug G V_list B mult w_orig).encode[i]'hi))
    (horig_at : ListAt mem origsPtr (origOfCopy G mult))
    (hb_at : ListAt mem bArr B)
    (hin_at : ListAt mem inactArr (inactiveVertsList G.n V_list)) :
    let m₁ := ((nonloopEdges G).map mult).sum
    let m_aug := m₁ + B.length
    let inact := inactiveVertsList G.n V_list
    let r₀ := V_list.headD 0
    ∃ st' c,
      Runs w p ω (simDecodeProc wrapBase simBase encodeBase)
        (startState [V_list.length, m_aug, m₁, B.length, bArr, inact.length, inactArr, r₀,
          arrPtr, L_sim, h, 2 ^ h, origsPtr, outOrigPtr, outBridgePtr, outHdrPtr, heap] mem pos₀)
        (.returned 0) st' c ∧
      let dec := decodeAN19Output G V_list B mult out
      st'.mem outHdrPtr = dec.1.length ∧
      st'.mem (outHdrPtr + 1) = dec.2.length ∧
      ListAt st'.mem outOrigPtr dec.1 ∧
      ListAt st'.mem outBridgePtr (dec.2.flatMap fun p => [p.1, p.2]) ∧
      (∀ a < heap,
        (a < outOrigPtr ∨ outOrigPtr + (V_list.length - 1) ≤ a) →
        (a < outBridgePtr ∨ outBridgePtr + 2 * ((V_list.length - 1) + inact.length) ≤ a) →
        (a < outHdrPtr ∨ outHdrPtr + 2 ≤ a) → st'.mem a = mem a) ∧
      ZeroFrom st'.mem (heap + simDecodeSpace Q V_list.length
        (((nonloopEdges G).map mult).sum + B.length) L_sim h cost) ∧
      (heap + 5 ≤ st'.mem (heap + 1) ∧
        st'.mem (heap + 1) ≤ heap + simDecodeSpace Q V_list.length
          (((nonloopEdges G).map mult).sum + B.length) L_sim h cost ∧
        ZeroFrom st'.mem (st'.mem (heap + 1))) ∧
      c ≤ simDecodeCost Q w' V_list.length m_aug inact.length L_sim cost := by
  intro m₁ m_aug inact r₀
  let G_aug := buildGAug G V_list B mult w_orig
  let encLen := 2 + 3 * m_aug
  let hp₀ := heap + 5 + (1 + V_list.length) * L_sim
  let retDst := heap + 5
  let keyPtr := heap + 5 + L_sim
  let outLimbsPtr := heap + 5 + 2 * L_sim
  have hArith := arithModule_hasAt_of_compile hSim
  have hTrie := trieModule_hasAt_of_compile hSim
  have hbt_mc := buildInitTrie_of_module (w := w) hArith hTrie hWrap
  have hro_mc := readOutLimbs_of_module (w := w) hArith hTrie hWrap
  have hdo_mc := decodeOut_meetsContract (w := w) (h := h) hEnc hPack
  have hsim_proc := simEntry_procs_at hSim
  have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have h2_w : 2 < 2 ^ w := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ w))
  have h3_w : 3 < 2 ^ w := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ w))
  have h4_w : 4 < 2 ^ w := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 3 ≤ w))
  have h5_w : 5 < 2 ^ w := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 3 ≤ w))
  have hpow2h_pos : 1 ≤ 2 ^ h := Nat.one_le_pow h 2 (by norm_num)
  have hV_mul : 1 + V_list.length ≤ (1 + V_list.length) * L_sim := Nat.le_mul_of_pos_right _ hL1
  have hL_mul : L_sim ≤ (1 + V_list.length) * L_sim := Nat.le_mul_of_pos_left _ (by omega)
  have henc_mul : encLen ≤ encLen * (L_sim * 2 ^ h + L_sim) :=
    Nat.le_mul_of_pos_right _ (by nlinarith)
  have hsp_ge_hp₀ : hp₀ ≤ heap + simDecodeSpace Q V_list.length m_aug L_sim h cost := by
    dsimp only [hp₀, simDecodeSpace]; omega
  have hhp₀_w : hp₀ < 2 ^ w := lt_of_le_of_lt hsp_ge_hp₀ hheap_w
  have hsp_bt_w : hp₀ + L_sim + encLen * (L_sim * 2 ^ h + L_sim) +
      simScale Q * L_sim * 2 ^ h * (cost + encLen + 1) < 2 ^ w := by
    simpa only [hp₀, simDecodeSpace, encLen, m_aug, m₁, Nat.add_assoc] using hheap_w
  have hbt_bound_w : hp₀ + L_sim + encLen * (L_sim * 2 ^ h + L_sim) < 2 ^ w := by omega
  have hV1_w : 1 + V_list.length < 2 ^ w := by dsimp only [hp₀] at hhp₀_w; omega
  have hV1L_w : (1 + V_list.length) * L_sim < 2 ^ w := by dsimp only [hp₀] at hhp₀_w; omega
  have hhp₀_off_w : 5 + (1 + V_list.length) * L_sim < 2 ^ w := by dsimp only [hp₀] at hhp₀_w; omega
  have henc_w : encLen < 2 ^ w := by
    dsimp only [simDecodeSpace, encLen, m_aug, m₁] at hheap_w henc_mul
    omega
  have hm3_w : 3 * m_aug < 2 ^ w := by dsimp only [encLen] at henc_w; omega
  have hm_aug_w : m_aug < 2 ^ w := by omega
  have hm₁_w : m₁ < 2 ^ w := by dsimp only [m_aug] at hm_aug_w; omega
  have hheap_lt_w : heap < 2 ^ w := by dsimp only [hp₀] at hhp₀_w; omega
  have hheap1_w : heap + 1 < 2 ^ w := by dsimp only [hp₀] at hhp₀_w; omega
  have hheap2_w : heap + 2 < 2 ^ w := by dsimp only [hp₀] at hhp₀_w; omega
  have hheap3_w : heap + 3 < 2 ^ w := by dsimp only [hp₀] at hhp₀_w; omega
  have hheap4_w : heap + 4 < 2 ^ w := by dsimp only [hp₀] at hhp₀_w; omega
  have hret_w : retDst < 2 ^ w := by dsimp only [retDst, hp₀] at hhp₀_w; omega
  have houtLen_w : V_list.length - 1 < 2 ^ w := by omega
  have hkey_w : keyPtr < 2 ^ w := by
    have h2L : 2 * L_sim ≤ (1 + V_list.length) * L_sim := Nat.mul_le_mul_right _ (by omega)
    dsimp only [keyPtr, hp₀] at *; omega
  have houtLimbs_w : outLimbsPtr < 2 ^ w := by
    have h2L : 2 * L_sim ≤ (1 + V_list.length) * L_sim := Nat.mul_le_mul_right _ (by omega)
    dsimp only [outLimbsPtr, hp₀] at *; omega
  have hL_w : L_sim < 2 ^ w := by dsimp only [hp₀] at hhp₀_w; omega
  have h2h_w : 2 ^ h < 2 ^ w :=
    lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) (by omega : h < w)) (le_refl _)
  have hh_w : h < 2 ^ w := lt_trans (Nat.lt_two_pow_self (n := h)) h2h_w
  have hV_w : V_list.length < 2 ^ w := by omega
  have hB_w : B.length < 2 ^ w := by dsimp only [m_aug] at hm_aug_w; omega
  have hbArr_w : bArr < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right _ _) (lt_of_le_of_lt hb_lt hheap_lt_w)
  have hinLen_w : inact.length < 2 ^ w := lt_of_le_of_lt (Nat.le_add_left _ _) (lt_of_le_of_lt hin_lt hheap_lt_w)
  have hinArr_w : inactArr < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right _ _) (lt_of_le_of_lt hin_lt hheap_lt_w)
  have harr_w : arrPtr < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right _ _) (lt_of_le_of_lt harr_lt hheap_lt_w)
  have horig_w : origsPtr < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right _ _) (lt_of_le_of_lt horig_lt hheap_lt_w)
  have hoo_w : outOrigPtr < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right _ _) (lt_of_le_of_lt hoo_lt hheap_lt_w)
  have hob_w : outBridgePtr < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right _ _) (lt_of_le_of_lt hob_lt hheap_lt_w)
  have hoh_w : outHdrPtr < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right _ _) (lt_of_le_of_lt hoh_lt hheap_lt_w)
  have hreg0 : SimDRegs
      (startState [V_list.length, m_aug, m₁, B.length, bArr, inact.length, inactArr, r₀,
        arrPtr, L_sim, h, 2 ^ h, origsPtr, outOrigPtr, outBridgePtr, outHdrPtr, heap] mem pos₀)
      V_list.length m_aug m₁ B.length bArr inact.length inactArr r₀ arrPtr L_sim h (2 ^ h)
      origsPtr outOrigPtr outBridgePtr outHdrPtr heap := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [startState]
  suffices hrun_o : ∃ o st' c,
      Runs w p ω (simDecodeProc wrapBase simBase encodeBase)
        (startState [V_list.length, m_aug, m₁, B.length, bArr, inact.length, inactArr, r₀,
          arrPtr, L_sim, h, 2 ^ h, origsPtr, outOrigPtr, outBridgePtr, outHdrPtr, heap] mem pos₀)
        o st' c ∧
      (o = .returned 0 ∧
        st'.mem outHdrPtr = (decodeAN19Output G V_list B mult out).1.length ∧
        st'.mem (outHdrPtr + 1) = (decodeAN19Output G V_list B mult out).2.length ∧
        ListAt st'.mem outOrigPtr (decodeAN19Output G V_list B mult out).1 ∧
        ListAt st'.mem outBridgePtr ((decodeAN19Output G V_list B mult out).2.flatMap fun p => [p.1, p.2]) ∧
        (∀ a < heap,
          (a < outOrigPtr ∨ outOrigPtr + (V_list.length - 1) ≤ a) →
          (a < outBridgePtr ∨ outBridgePtr + 2 * ((V_list.length - 1) + inact.length) ≤ a) →
          (a < outHdrPtr ∨ outHdrPtr + 2 ≤ a) → st'.mem a = mem a) ∧
        ZeroFrom st'.mem (heap + simDecodeSpace Q V_list.length m_aug L_sim h cost) ∧
        (heap + 5 ≤ st'.mem (heap + 1) ∧
          st'.mem (heap + 1) ≤ heap + simDecodeSpace Q V_list.length m_aug L_sim h cost ∧
          ZeroFrom st'.mem (st'.mem (heap + 1)))) ∧
      0 + c ≤ simDecodeCost Q w' V_list.length m_aug inact.length L_sim cost by
    rcases hrun_o with ⟨o, st', c, hrun', ⟨rfl, hpost1, hpost2, hpost3, hpost4, hpost5, hpost6, hpost7⟩, hc⟩
    exact ⟨st', c, hrun', hpost1, hpost2, hpost3, hpost4, hpost5, hpost6, hpost7, by omega⟩
  dsimp only [simDecodeProc]
  refine simDecode_setup_runs (k := 0) (by omega : 3 ≤ w)
    (by dsimp only [hp₀] at hhp₀_w; omega) henc_w hV_w hz_heap hV_pos hL1
    fun s10 hrg10 hs10_18 hs10_19 hs10_20 hs10_21 hs10_22 hs10_c1_raw hs10_c2 hs10_c3 hs10_c4
      hs10_lt_heap hs10_z_raw => ?_
  have hs10_c1 : s10.mem (heap + 1) = hp₀ := by dsimp only [hp₀]; exact hs10_c1_raw
  have hs10_z : ZeroFrom s10.mem hp₀ := by dsimp only [hp₀]; exact hs10_z_raw
  have henc_len_eq : encLen = G_aug.encode.length := (gAug_encode_length G V_list B mult w_orig).symm
  have harr_lt' : arrPtr + encLen * L_sim ≤ heap := harr_lt
  have hpre_bt : (buildInitTrieContract w).pre
      [heap, heap + 1, arrPtr, encLen, L_sim, h, 2 ^ h] s10.mem :=
    ⟨heap, heap + 1, arrPtr, encLen, L_sim, h, hp₀, G_aug.encode, rfl,
      hL1, hh, hw2, henc_len_eq, hm_fit, by dsimp only [hp₀]; linarith only [hV_mul],
      hs10_c1, hs10_z, hbt_bound_w,
      by dsimp only [hp₀]; linarith only [hV_mul], by dsimp only [hp₀]; linarith only [hV_mul],
      by linarith only,
      by dsimp only [hp₀]; exact le_trans harr_lt' (by linarith only [hV_mul]),
      fun i hi => ⟨Nat.ne_of_lt (by linarith only [hi, harr_lt']),
        Nat.ne_of_lt (by linarith only [hi, harr_lt'])⟩,
      fun i hi => (henc_limbs i hi).congr fun q hq1 hq2 => by
        refine hs10_lt_heap q ?_
        have hmul_le : i * L_sim + L_sim ≤ G_aug.encode.length * L_sim := by
          have hm := Nat.mul_le_mul_right L_sim (Nat.succ_le_of_lt hi)
          rw [Nat.succ_mul] at hm; exact hm
        rw [← henc_len_eq] at hmul_le
        linarith only [hq2, hmul_le, harr_lt']⟩
  -- Step 11: call buildInitTrie
  refine runs_seq_call_step hbt_mc
    (vs := [heap, heap + 1, arrPtr, encLen, L_sim, h, 2 ^ h])
    (evalArgs_cons (Expr.eval_reg_of_eq hrg10.r16)
      (evalArgs_cons (Expr.eval_add (Expr.eval_reg_of_eq hrg10.r16) (Expr.eval_const hw1) hheap1_w)
        (evalArgs_cons (Expr.eval_reg_of_eq hrg10.r8)
          (evalArgs_cons (Expr.eval_reg_of_eq hs10_18)
            (evalArgs_cons (Expr.eval_reg_of_eq hrg10.r9)
              (evalArgs_cons (Expr.eval_reg_of_eq hrg10.r10)
                (evalArgs_cons (Expr.eval_reg_of_eq hrg10.r11) (evalArgs_nil _ _))))))))
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx | hx | hx | hx | hx | hx <;> rw [hx] <;> assumption)
    hpre_bt rfl (rfl : _ = (95 * L_sim + 115) * encLen + 30) fun _ mem_bt s11 hp_bt hm11 hr11 => ?_
  rcases hp_bt with ⟨rP, hP, aP, lenP, LP, hP', hp_b0, heq_bt, _, hc1_eq, hhp_mid_ge, hhp_mid_le,
    htrie_bt, hin_bt, hz_bt, hfr_bt⟩
  simp only [List.cons.injEq, and_true] at heq_bt
  rcases heq_bt with ⟨e0, e1, e2, e3, e4, e5, _⟩
  rw [← e1] at hc1_eq hhp_mid_ge hhp_mid_le hz_bt
  rw [← e3, ← e4, ← e5] at hhp_mid_le
  rw [← e0, ← e1, ← e2, ← e3, ← e4, ← e5] at htrie_bt
  rw [← e0, ← e1, ← e4, ← e5] at hin_bt
  rw [← e0, ← e1] at hfr_bt
  have h_b0 : hp₀ = hp_b0 := hs10_c1.symm.trans hc1_eq
  have hhp_mid_ge' : hp₀ ≤ mem_bt (heap + 1) := by rw [← hs10_c1]; exact hhp_mid_ge
  have hhp_mid_le' : mem_bt (heap + 1) ≤ hp₀ + L_sim + encLen * (L_sim * 2 ^ h + L_sim) := by
    rw [h_b0]; exact hhp_mid_le
  have htrie11 : TrieRep s11.mem L_sim h (s11.mem (heap + 1)) (s11.mem heap) (initMem G_aug.encode) := by
    rw [hm11]
    refine htrie_bt G_aug.encode henc_len_eq fun i hi => (henc_limbs i hi).congr fun q hq1 hq2 => ?_
    refine hs10_lt_heap q ?_
    have hmul_le : i * L_sim + L_sim ≤ G_aug.encode.length * L_sim := by
      have hm := Nat.mul_le_mul_right L_sim (Nat.succ_le_of_lt hi)
      rw [Nat.succ_mul] at hm; exact hm
    rw [← henc_len_eq] at hmul_le
    linarith only [hq2, hmul_le, harr_lt']
  have hhp5_hp₀ : heap + 5 ≤ hp₀ := by dsimp only [hp₀]; linarith only [hV_mul, hV_pos]
  have hs11_lt_heap : ∀ q < heap, s11.mem q = mem q := fun q hq => by
    have hqp : q < hp₀ := by linarith only [hq, hhp5_hp₀]
    rw [hm11, hfr_bt q (Nat.ne_of_lt (by linarith only [hq])) (Nat.ne_of_lt (by linarith only [hq]))
      (by rw [hs10_c1]; exact hqp), hs10_lt_heap q hq]
  have hs11_c2 : s11.mem (heap + 2) = L_sim := by
    have hqp : heap + 2 < hp₀ := by linarith only [hhp5_hp₀]
    rw [hm11, hfr_bt _ (by linarith only) (by linarith only) (by rw [hs10_c1]; exact hqp), hs10_c2]
  have hs11_c3 : s11.mem (heap + 3) = h := by
    have hqp : heap + 3 < hp₀ := by linarith only [hhp5_hp₀]
    rw [hm11, hfr_bt _ (by linarith only) (by linarith only) (by rw [hs10_c1]; exact hqp), hs10_c3]
  have hs11_c4 : s11.mem (heap + 4) = 2 ^ h := by
    have hqp : heap + 4 < hp₀ := by linarith only [hhp5_hp₀]
    rw [hm11, hfr_bt _ (by linarith only) (by linarith only) (by rw [hs10_c1]; exact hqp), hs10_c4]
  have hrg11 := simDRegs_upd hrg10 hr11 (by decide)
  have hs11_18 : s11.regs 18 = encLen := by rw [hr11, Function.update_of_ne (by decide)]; exact hs10_18
  have hs11_19 : s11.regs 19 = retDst := by rw [hr11, Function.update_of_ne (by decide)]; exact hs10_19
  have hs11_20 : s11.regs 20 = V_list.length - 1 := by rw [hr11, Function.update_of_ne (by decide)]; exact hs10_20
  have hs11_21 : s11.regs 21 = keyPtr := by rw [hr11, Function.update_of_ne (by decide)]; exact hs10_21
  have hs11_22 : s11.regs 22 = outLimbsPtr := by rw [hr11, Function.update_of_ne (by decide)]; exact hs10_22
  -- Step 12: call simBase (simEntry_runs)
  have hsim_bound : s11.mem (heap + 1) + simScale Q * L_sim * 2 ^ h * (cost + G_aug.encode.length + 1) < 2 ^ w := by
    rw [hm11, ← henc_len_eq]
    linarith only [hsp_bt_w, hhp_mid_le']
  have hret_hp : retDst + L_sim ≤ hp₀ := by dsimp only [retDst, hp₀]; linarith only [hL_mul]
  have hsim_hin : ∀ q, InTrie s11.mem L_sim h L_sim (s11.mem heap) q →
      (q < heap ∨ heap + 5 ≤ q) ∧ (q < retDst ∨ retDst + L_sim ≤ q) := fun q hq => by
    rw [hm11] at hq
    have hqr := hin_bt q hq
    exact ⟨Or.inr (by linarith only [hqr.1, h_b0, hhp5_hp₀, hL1]),
      Or.inr (by linarith only [hqr.1, h_b0, hret_hp])⟩
  have h1_hp_mid : heap + 5 ≤ s11.mem (heap + 1) := by
    rw [hm11]; linarith only [hhp5_hp₀, hhp_mid_ge']
  have hret_hp_mid : retDst + L_sim ≤ s11.mem (heap + 1) := by
    rw [hm11]; linarith only [hret_hp, hhp_mid_ge']
  obtain ⟨st_sim, c_sim, hp', gmem', hsim_run, hsim_hp, hhp_sim_ge, hhp_sim_le,
      htrie_sim, _hret_limbs, hgmem_out, hin_sim, hfr_sim, hcost_sim⟩ :=
    simEntry_runs (ω := ω) (pos₀ := s11.pos) hSim hL1 hh hw2 hw'1 hw'_lh
      h1_hp_mid hret_hp_mid
      (Or.inr (le_refl _))
      rfl hs11_c2 hs11_c3 hs11_c4 hx_lt htrie11 hsim_hin hsim_bound hrun
  have hsim_run' : Runs w p ω (simEntry Q (simBase + 1) (simBase + 21))
      (startState [heap, encLen, retDst] s11.mem s11.pos) (.returned 0) st_sim c_sim := by
    rwa [henc_len_eq]
  refine runs_seq_call_stmt hsim_proc
    (evalArgs_cons (Expr.eval_reg_of_eq hrg11.r16)
      (evalArgs_cons (Expr.eval_reg_of_eq hs11_18)
        (evalArgs_cons (Expr.eval_reg_of_eq hs11_19) (evalArgs_nil _ _))))
    hsim_run' ?_
  -- Step 13: reg 23 := mem heap (root)
  have hs12_hp' : hp' < 2 ^ w := by
    rw [← henc_len_eq] at hhp_sim_le
    rw [← hm11] at hhp_mid_le'
    linarith only [hsp_bt_w, hhp_mid_le', hhp_sim_le]
  have hs12_root_w : st_sim.mem heap < 2 ^ w :=
    subtrie_root_lt htrie_sim.2.1 hs12_hp' hw1
  have hs12_lt_heap : ∀ q < heap, st_sim.mem q = mem q := fun q hq => by
    have hq_mid : q < s11.mem (heap + 1) := by
      rw [hm11]; linarith only [hq, hhp5_hp₀, hhp_mid_ge']
    have hq_nt : ¬ InTrie s11.mem L_sim h L_sim (s11.mem heap) q := fun hqt => by
      rw [hm11] at hqt
      have hqt_b := (hin_bt q hqt).1
      linarith only [hq, hqt_b, h_b0, hhp5_hp₀]
    have hq_nr : q < retDst ∨ retDst + L_sim ≤ q := Or.inl (by dsimp only [retDst]; linarith only [hq])
    rw [hfr_sim q hq_mid (Nat.ne_of_lt (by linarith only [hq]))
      (Nat.ne_of_lt (by linarith only [hq])) hq_nt hq_nr, hs11_lt_heap q hq]
  have h12_20 : (Function.update s11.regs 24 0) 20 = V_list.length - 1 := by
    rw [Function.update_of_ne (by decide)]; exact hs11_20
  have h12_21 : (Function.update s11.regs 24 0) 21 = keyPtr := by
    rw [Function.update_of_ne (by decide)]; exact hs11_21
  have h12_22 : (Function.update s11.regs 24 0) 22 = outLimbsPtr := by
    rw [Function.update_of_ne (by decide)]; exact hs11_22
  have hrg12 := simDRegs_upd (st' := { st_sim with regs := Function.update s11.regs 24 0 })
    hrg11 (r := 24) (v := 0) rfl (by decide)
  refine runs_seq_assign_step
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq hrg12.r16) rfl)
    rfl fun s13 hm13 _ hr13 => ?_
  have hrg13 := simDRegs_upd hrg12 hr13 (by decide)
  have hs13_mem : s13.mem = st_sim.mem := hm13
  have hs13_20 : s13.regs 20 = V_list.length - 1 := by rw [hr13, Function.update_of_ne (by decide)]; exact h12_20
  have hs13_21 : s13.regs 21 = keyPtr := by rw [hr13, Function.update_of_ne (by decide)]; exact h12_21
  have hs13_22 : s13.regs 22 = outLimbsPtr := by rw [hr13, Function.update_of_ne (by decide)]; exact h12_22
  have hs13_23 : s13.regs 23 = st_sim.mem heap := by rw [hr13, Function.update_self]
  -- Step 14: call readOutLimbs
  have houtLimbs_eq_hp₀ : outLimbsPtr + (V_list.length - 1) * L_sim = hp₀ := by
    dsimp only [outLimbsPtr, hp₀]
    have hmul_eq : 2 * L_sim + (V_list.length - 1) * L_sim = (1 + V_list.length) * L_sim := by
      have hv1 : V_list.length - 1 + 1 = V_list.length := Nat.sub_add_cancel hV_pos
      have hv : 2 + (V_list.length - 1) = 1 + V_list.length := by linarith only [hv1]
      calc 2 * L_sim + (V_list.length - 1) * L_sim
          = (2 + (V_list.length - 1)) * L_sim := (Nat.add_mul _ _ _).symm
        _ = (1 + V_list.length) * L_sim := by rw [hv]
    linarith only [hmul_eq]
  have houtLimbs_end_w : outLimbsPtr + (V_list.length - 1) * L_sim < 2 ^ w := by
    rw [houtLimbs_eq_hp₀]; exact hhp₀_w
  have hpre_ro : (readOutLimbsContract w).pre
      [st_sim.mem heap, keyPtr, outLimbsPtr, V_list.length - 1, L_sim, 2 ^ h] s13.mem := by
    rw [hs13_mem]
    refine ⟨st_sim.mem heap, keyPtr, outLimbsPtr, V_list.length - 1, L_sim, h, hp', gmem', rfl,
      hL1, hh, hw2, hV_fit, hs12_hp',
      by dsimp only [keyPtr, outLimbsPtr] at houtLimbs_w ⊢; linarith only [houtLimbs_w],
      houtLimbs_end_w, Or.inl (by dsimp only [keyPtr, outLimbsPtr]; linarith only [hL1]), fun q hq => ?_, htrie_sim.2.1⟩
    have hqp : hp₀ ≤ q := by
      rcases hin_sim q hq with hq1 | hq2
      · rw [hm11] at hq1; have := (hin_bt q hq1).1; linarith only [this, h_b0]
      · rw [hm11] at hq2; linarith only [hq2.1, hhp_mid_ge']
    have hle : outLimbsPtr ≤ hp₀ := houtLimbs_eq_hp₀ ▸ Nat.le_add_right _ _
    exact ⟨Or.inr (by dsimp only [keyPtr, outLimbsPtr] at hle ⊢; linarith only [hle, hqp]),
      Or.inr (by rw [houtLimbs_eq_hp₀]; exact hqp)⟩
  refine runs_seq_call_step hro_mc
    (vs := [st_sim.mem heap, keyPtr, outLimbsPtr, V_list.length - 1, L_sim, 2 ^ h])
    (evalArgs_cons (Expr.eval_reg_of_eq hs13_23)
      (evalArgs_cons (Expr.eval_reg_of_eq hs13_21)
        (evalArgs_cons (Expr.eval_reg_of_eq hs13_22)
          (evalArgs_cons (Expr.eval_reg_of_eq hs13_20)
            (evalArgs_cons (Expr.eval_reg_of_eq hrg13.r9)
              (evalArgs_cons (Expr.eval_reg_of_eq hrg13.r11) (evalArgs_nil _ _)))))))
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx | hx | hx | hx | hx <;> rw [hx] <;> assumption)
    hpre_ro rfl (rfl : _ = (70 * L_sim + 80) * (V_list.length - 1) + 20)
    fun _ mem_ro s14 hp_ro hm14 hr14 => ?_
  rcases hp_ro with ⟨r_ro, k_ro, o_ro, l_ro, L_ro, B_ro, heq_ro, _, hro_limbs, hfr_ro⟩
  simp only [List.cons.injEq, and_true] at heq_ro
  rcases heq_ro with ⟨er, ek, eo, el, eL, eB⟩
  rw [← er, ← eo, ← el, ← eL] at hro_limbs
  rw [← ek, ← eo, ← el, ← eL] at hfr_ro
  have hs14_limbs : ∀ i (hi : i < out.length),
      LimbsAt s14.mem (outLimbsPtr + i * L_sim) L_sim h (out[i]'hi) ∧ out[i]'hi < 2 ^ w := by
    intro i hi
    have hiV : i < V_list.length - 1 := hout_len ▸ hi
    have hl := hro_limbs h hp' gmem' eB.symm (hs13_mem ▸ htrie_sim.2.1) i hiV
    rw [hgmem_out i hi] at hl
    exact ⟨hm14 ▸ hl, hout_lt _ (List.getElem_mem hi)⟩
  have hs14_lt_heap : ∀ q < heap, s14.mem q = mem q := fun q hq => by
    rw [hm14, hfr_ro q (Or.inl (by dsimp only [keyPtr]; linarith only [hq]))
      (Or.inl (by dsimp only [outLimbsPtr]; linarith only [hq])), hs13_mem, hs12_lt_heap q hq]
  have hs14_orig : ListAt s14.mem origsPtr (origOfCopy G mult) :=
    horig_at.congr fun q hq1 hq2 => by
      have hql : (origOfCopy G mult).length = m₁ := origOfCopy_length G mult ▸ copyEdgeList_length G mult
      rw [hql] at hq2
      exact hs14_lt_heap q (lt_of_lt_of_le hq2 horig_lt)
  have hs14_B : ListAt s14.mem bArr B :=
    hb_at.congr fun q hq1 hq2 => hs14_lt_heap q (lt_of_lt_of_le hq2 hb_lt)
  have hs14_in : ListAt s14.mem inactArr inact :=
    hin_at.congr fun q hq1 hq2 => hs14_lt_heap q (lt_of_lt_of_le hq2 hin_lt)
  have hs14_20 : s14.regs 20 = out.length := by
    rw [hr14, Function.update_of_ne (by decide), hs13_20, hout_len]
  have hs14_22 : s14.regs 22 = outLimbsPtr := by
    rw [hr14, Function.update_of_ne (by decide)]; exact hs13_22
  have hrg14 := simDRegs_upd hrg13 hr14 (by decide)
  -- Step 15: call decodeOut
  have hdo_outL : outOrigPtr + out.length < 2 ^ w := by rw [hout_len]; exact lt_of_le_of_lt hoo_lt hheap_lt_w
  have hdo_brL : outBridgePtr + 2 * (out.length + inact.length) < 2 ^ w := by
    rw [hout_len]; exact lt_of_le_of_lt hob_lt hheap_lt_w
  have hdo_hdL : outHdrPtr + 2 < 2 ^ w := lt_of_le_of_lt hoh_lt hheap_lt_w
  have hdo_oL : DisjointRanges outOrigPtr out.length outLimbsPtr (out.length * L_sim) :=
    Or.inl (by rw [hout_len]; exact le_trans hoo_lt (by dsimp only [outLimbsPtr]; linarith only))
  have hdo_bL : DisjointRanges outBridgePtr (2 * (out.length + inact.length)) outLimbsPtr (out.length * L_sim) :=
    Or.inl (by rw [hout_len]; exact le_trans hob_lt (by dsimp only [outLimbsPtr]; linarith only))
  have hdo_hL : DisjointRanges outHdrPtr 2 outLimbsPtr (out.length * L_sim) :=
    Or.inl (le_trans hoh_lt (by dsimp only [outLimbsPtr]; linarith only))
  have hpre_do : (decodeOutContract w h).pre
      [outLimbsPtr, out.length, m₁, B.length, bArr, inact.length, inactArr, r₀, L_sim, origsPtr,
        outOrigPtr, outBridgePtr, outHdrPtr] s14.mem := by
    refine ⟨out, B, inact, origOfCopy G mult, outLimbsPtr, m₁, bArr, inactArr, r₀, L_sim,
      origsPtr, outOrigPtr, outBridgePtr, outHdrPtr, rfl, hh, hw2, hL1, hm_aug_w,
      by rw [hout_len]; exact houtLimbs_end_w, lt_of_le_of_lt hb_lt hheap_lt_w,
      lt_of_le_of_lt hin_lt hheap_lt_w, lt_of_le_of_lt horig_lt hheap_lt_w,
      by rw [origOfCopy_length, copyEdgeList_length],
      hdo_outL, hdo_brL, hdo_hdL, hr₀_w, hOrig_lt, hB_lt, hIn_lt,
      by rw [hout_len]; exact hd_ob, by rw [hout_len]; exact hd_oh, by rw [hout_len]; exact hd_bh,
      hdo_oL, by rw [hout_len]; exact hd_oo, by rw [hout_len]; exact hd_oB, by rw [hout_len]; exact hd_oi,
      hdo_bL, by rw [hout_len]; exact hd_bo, by rw [hout_len]; exact hd_bB, by rw [hout_len]; exact hd_bi,
      hdo_hL, hd_ho, hd_hB, hd_hi, hs14_limbs, hs14_orig, hs14_B, hs14_in⟩
  refine runs_seq_call_step hdo_mc
    (vs := [outLimbsPtr, out.length, m₁, B.length, bArr, inact.length, inactArr, r₀, L_sim,
      origsPtr, outOrigPtr, outBridgePtr, outHdrPtr])
    (evalArgs_cons (Expr.eval_reg_of_eq hs14_22)
      (evalArgs_cons (Expr.eval_reg_of_eq hs14_20)
        (evalArgs_cons (Expr.eval_reg_of_eq hrg14.r2)
          (evalArgs_cons (Expr.eval_reg_of_eq hrg14.r3)
            (evalArgs_cons (Expr.eval_reg_of_eq hrg14.r4)
              (evalArgs_cons (Expr.eval_reg_of_eq hrg14.r5)
                (evalArgs_cons (Expr.eval_reg_of_eq hrg14.r6)
                  (evalArgs_cons (Expr.eval_reg_of_eq hrg14.r7)
                    (evalArgs_cons (Expr.eval_reg_of_eq hrg14.r9)
                      (evalArgs_cons (Expr.eval_reg_of_eq hrg14.r12)
                        (evalArgs_cons (Expr.eval_reg_of_eq hrg14.r13)
                          (evalArgs_cons (Expr.eval_reg_of_eq hrg14.r14)
                            (evalArgs_cons (Expr.eval_reg_of_eq hrg14.r15) (evalArgs_nil _ _))))))))))))))
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx <;>
        rw [hx] <;> try assumption
      rw [hout_len]; exact houtLen_w)
    hpre_do rfl (rfl : _ = decodeOutCost out.length inact.length L_sim) fun _ mem_do s15 hp_do hm15 _ => ?_
  rcases hp_do with ⟨out', B', inact', origs', outLimbs', m₁', bArr', inactArr', r₀', L_sim',
    origsPtr', outO', outB', outH', heq_do, _, hhdr0, hhdr1, hlo_do, hlb_do, hfr_do,
    horig_len', hlimbs', horig_at', hb_at', hinact_at'⟩
  simp only [List.cons.injEq, and_true] at heq_do
  rcases heq_do with ⟨e_oL, e_ol, e_m1, e_bl, e_bA, e_il, e_iA, e_r0, e_L, e_oP, e_oO, e_oB, e_oH⟩
  have hout'_eq : out' = out := List.ext_getElem e_ol.symm fun i hi1 hi2 => by
    have hlim := hlimbs' i hi1
    rw [← e_oL, ← e_L] at hlim
    exact LimbsAt.ext hlim (hs14_limbs i hi2).1
  have hB'_eq : B' = B := ListAt.ext (e_bA.symm ▸ hb_at') hs14_B e_bl.symm
  have hin'_eq : inact' = inact := ListAt.ext (e_iA.symm ▸ hinact_at') hs14_in e_il.symm
  have horig_len_eq : origs'.length = (origOfCopy G mult).length := by
    rw [horig_len', ← e_m1, origOfCopy_length, copyEdgeList_length]
  have horig'_eq : origs' = origOfCopy G mult :=
    ListAt.ext (e_oP.symm ▸ horig_at') hs14_orig horig_len_eq
  rw [hout'_eq, ← e_oH, horig'_eq, ← e_m1] at hhdr0
  rw [hout'_eq, ← e_oH, ← e_r0, hB'_eq, ← e_m1, hin'_eq] at hhdr1
  rw [hout'_eq, ← e_oO, horig'_eq, ← e_m1] at hlo_do
  rw [hout'_eq, ← e_oB, ← e_r0, hB'_eq, ← e_m1, hin'_eq] at hlb_do
  rw [hout'_eq, ← e_oO, ← e_oB, hin'_eq, ← e_oH] at hfr_do
  have hdec_eq : decodeAN19Output G V_list B mult out =
      ((out.filter fun j => decide (j < m₁)).map fun j => (origOfCopy G mult).getD j 0,
       (out.filter fun j => decide (m₁ ≤ j ∧ j < m₁ + B.length)).map
           (fun j => (r₀, B.getD (j - m₁) 0)) ++ inact.map fun u => (r₀, u)) := rfl
  refine runs_ret_le (Expr.eval_const (Nat.lt_trans Nat.zero_lt_one hw1)) ?_ ?_
  · refine ⟨rfl, ?_⟩
    rw [hdec_eq, hm15]
    have hhp'_le : hp' ≤ heap + simDecodeSpace Q V_list.length m_aug L_sim h cost := by
      have h1 := hhp_sim_le
      rw [← henc_len_eq] at h1
      have h2 := hhp_mid_le'
      rw [← hm11] at h2
      have h3 := le_trans h1 (Nat.add_le_add_right h2 _)
      simpa only [hp₀, simDecodeSpace, encLen, m_aug, m₁, Nat.add_assoc] using h3
    have hk_hp₀ : keyPtr + L_sim ≤ hp₀ := by
      have h2L : L_sim + L_sim ≤ (1 + V_list.length) * L_sim := by
        rw [← Nat.two_mul]
        exact Nat.mul_le_mul_right L_sim (Nat.add_le_add_left hV_pos 1)
      dsimp only [keyPtr, hp₀]
      rw [Nat.add_assoc (heap + 5) L_sim L_sim]
      exact Nat.add_le_add_left h2L (heap + 5)
    have hheap_le_hp₀ : heap ≤ hp₀ := by
      dsimp only [hp₀]
      rw [Nat.add_assoc]
      exact Nat.le_add_right _ _
    have hz_hp' : ZeroFrom mem_do hp' := by
      intro a ha_hp'
      have ha_hp₀ : hp₀ ≤ a := le_trans (le_trans (hm11 ▸ hhp_mid_ge') hhp_sim_ge) ha_hp'
      have ha_heap : heap ≤ a := le_trans hheap_le_hp₀ ha_hp₀
      have hao : a < outOrigPtr ∨ outOrigPtr + out.length ≤ a :=
        Or.inr (le_trans (by rw [hout_len]; exact hoo_lt) ha_heap)
      have hab : a < outBridgePtr ∨ outBridgePtr + 2 * (out.length + inact.length) ≤ a :=
        Or.inr (le_trans (by rw [hout_len]; exact hob_lt) ha_heap)
      have hah : a < outHdrPtr ∨ outHdrPtr + 2 ≤ a :=
        Or.inr (le_trans hoh_lt ha_heap)
      rw [hfr_do a hao hab hah, hm14,
        hfr_ro a (Or.inr (le_trans hk_hp₀ ha_hp₀)) (Or.inr (houtLimbs_eq_hp₀.symm ▸ ha_hp₀)), hs13_mem]
      exact htrie_sim.2.2 a ha_hp'
    have hdo_c1 : mem_do (heap + 1) = hp' := by
      have hao : heap + 1 < outOrigPtr ∨ outOrigPtr + out.length ≤ heap + 1 :=
        Or.inr (le_trans (by rw [hout_len]; exact hoo_lt) (Nat.le_succ heap))
      have hab : heap + 1 < outBridgePtr ∨ outBridgePtr + 2 * (out.length + inact.length) ≤ heap + 1 :=
        Or.inr (le_trans (by rw [hout_len]; exact hob_lt) (Nat.le_succ heap))
      have hah : heap + 1 < outHdrPtr ∨ outHdrPtr + 2 ≤ heap + 1 :=
        Or.inr (le_trans hoh_lt (Nat.le_succ heap))
      have hk_1 : heap + 1 < keyPtr := by dsimp only [keyPtr]; linarith only [hL1]
      have ho_1 : heap + 1 < outLimbsPtr := by dsimp only [outLimbsPtr]; linarith only [hL1]
      rw [hfr_do (heap + 1) hao hab hah, hm14, hfr_ro (heap + 1) (Or.inl hk_1) (Or.inl ho_1),
        hs13_mem, hsim_hp]
    have hz15 : ZeroFrom mem_do (heap + simDecodeSpace Q V_list.length m_aug L_sim h cost) :=
      fun a ha => hz_hp' a (le_trans hhp'_le ha)
    have hc1_lo : heap + 5 ≤ mem_do (heap + 1) := by
      rw [hdo_c1]; exact le_trans h1_hp_mid hhp_sim_ge
    have hc1_le : mem_do (heap + 1) ≤ heap + simDecodeSpace Q V_list.length m_aug L_sim h cost := by
      rw [hdo_c1]; exact hhp'_le
    have hc1_hz : ZeroFrom mem_do (mem_do (heap + 1)) := by
      rw [hdo_c1]; exact hz_hp'
    refine ⟨hhdr0, hhdr1, hlo_do, hlb_do, (fun a ha hao hab hah => ?_), hz15,
      hc1_lo, hc1_le, hc1_hz⟩
    rw [hfr_do a (by rw [hout_len]; exact hao) (by rw [hout_len]; exact hab) hah]
    exact hs14_lt_heap a ha
  · have hcost_sim' : c_sim ≤ simScale Q * L_sim * w' * (cost + encLen + 1) := by
      have hc1 : c_sim ≤ simScale Q * L_sim * w' * (cost + encLen + 1) - 10 := by
        rw [henc_len_eq]
        exact hcost_sim
      exact le_trans hc1 (Nat.sub_le _ _)
    dsimp only [encLen] at hcost_sim'
    dsimp only [simDecodeCost, decodeOutCost, argsSize, Expr.size]
    rw [← hout_len]
    dsimp only [encLen]
    linarith only [hcost_sim']

