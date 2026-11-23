module

public import MinCostFlow.Machine.WideWord.LSSTEncodeDecodeBase
import WordRAM.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Verified contracts for `encodeEdgeCopiesProc` and `encodeBridgesProc`

This module verifies `encodeEdgeCopiesContract` and `encodeBridgesContract`, which write
edge copies and unit-weight bridging edges into guest-size host limbs.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM

/-! ### Contracts and verification: `encodeEdgeCopies` and `encodeBridges` -/

def encodeEdgeCopiesCost (cnt L_sim : ℕ) : ℕ :=
  cnt * (70 * L_sim + 110) + 20

def encodeEdgeCopiesContract (w h : ℕ) : Contract where
  pre args mem :=
    ∃ uIdx vIdx wSrc K cnt L_sim pos origPtr origIdx origVal wVal,
      args = [uIdx, vIdx, wSrc, K, cnt, L_sim, 2 ^ h, pos, origPtr, origIdx, origVal] ∧
      1 ≤ h ∧ 2 * h + 2 ≤ w ∧ K ≤ L_sim ∧
      cnt < 2 ^ w ∧ wSrc + K < 2 ^ w ∧ pos + cnt * (3 * L_sim) < 2 ^ w ∧
      origPtr + origIdx + cnt < 2 ^ w ∧
      uIdx < 2 ^ (L_sim * h) ∧ vIdx < 2 ^ (L_sim * h) ∧
      (wSrc + K ≤ pos ∨ pos + cnt * (3 * L_sim) ≤ wSrc) ∧
      (origPtr + origIdx + cnt ≤ pos ∨ pos + cnt * (3 * L_sim) ≤ origPtr + origIdx) ∧
      (origPtr + origIdx + cnt ≤ wSrc ∨ wSrc + K ≤ origPtr + origIdx) ∧
      LimbsAt mem wSrc K h wVal
  post args mem ret mem' :=
    ∃ uIdx vIdx wSrc K cnt L_sim pos origPtr origIdx origVal wVal,
      args = [uIdx, vIdx, wSrc, K, cnt, L_sim, 2 ^ h, pos, origPtr, origIdx, origVal] ∧
      ret = pos + cnt * (3 * L_sim) ∧
      LimbsAt mem wSrc K h wVal ∧
      (∀ c < cnt, mem' (origPtr + origIdx + c) = origVal) ∧
      (∀ c < cnt,
        LimbsAt mem' (pos + c * (3 * L_sim)) L_sim h uIdx ∧
        LimbsAt mem' (pos + c * (3 * L_sim) + L_sim) L_sim h vIdx ∧
        LimbsAt mem' (pos + c * (3 * L_sim) + 2 * L_sim) L_sim h wVal) ∧
      (∀ a, (a < pos ∨ pos + cnt * (3 * L_sim) ≤ a) →
        (a < origPtr + origIdx ∨ origPtr + origIdx + cnt ≤ a) → mem' a = mem a)
  cost args _ := encodeEdgeCopiesCost (args.getD 4 0) (args.getD 5 0)

theorem encodeEdgeCopies_meetsContract {w b h a p w' s e : ℕ} {P : Program}
    (hp : P.HasAt b (encodeDecodeModule a p w' s e))
    (ha : P.HasAt a (arithModule a)) :
    MeetsContract w P (b + idxEncodeEdgeCopies) (encodeEdgeCopiesContract w h) := by
  have hproc : P.procs[b + idxEncodeEdgeCopies]? = some (encodeEdgeCopiesProc a) := by
    have := hp 0 (by rw [encodeDecodeModule_length]; omega)
    simpa [encodeDecodeModule, idxEncodeEdgeCopies] using this
  have hfh_mc := mwFromHost_of_arithModule (w := w) ha
  have hcp_mc := mwCopy_of_arithModule (w := w) ha
  have hzr_mc := mwZero_of_arithModule (w := w) ha
  refine meetsContract_of_runs hproc ?_
  intro args mem pos₀ ω hwords hpre
  rcases hpre with ⟨uIdx, vIdx, wSrc, K, cnt, L_sim, pos, origPtr, origIdx, origVal, wVal, hargs, hpr⟩
  have hwords' : ∀ a ∈ [uIdx, vIdx, wSrc, K, cnt, L_sim, 2 ^ h, pos, origPtr, origIdx, origVal], a < 2 ^ w :=
    hargs ▸ hwords
  rw [hargs]
  have hh := hpr.1
  have hw2 := hpr.2.1
  have hKL := hpr.2.2.1
  have hcnt_w := hpr.2.2.2.1
  have hwSrc_w := hpr.2.2.2.2.1
  have hpos_w := hpr.2.2.2.2.2.1
  have horig_w := hpr.2.2.2.2.2.2.1
  have hu_lt := hpr.2.2.2.2.2.2.2.1
  have hv_lt := hpr.2.2.2.2.2.2.2.2.1
  have hdw_pos := hpr.2.2.2.2.2.2.2.2.2.1
  have hdo_pos := hpr.2.2.2.2.2.2.2.2.2.2.1
  have hdo_w := hpr.2.2.2.2.2.2.2.2.2.2.2.1
  have hw_limbs := hpr.2.2.2.2.2.2.2.2.2.2.2.2
  have hL_w : L_sim < 2 ^ w := hwords' L_sim (by simp)
  have hK_w : K < 2 ^ w := hwords' K (by simp)
  have hu_w : uIdx < 2 ^ w := hwords' uIdx (by simp)
  have hv_w : vIdx < 2 ^ w := hwords' vIdx (by simp)
  have hB_w : 2 ^ h < 2 ^ w := hwords' (2 ^ h) (by simp)
  have hpos₀_w : pos < 2 ^ w := hwords' pos (by simp)
  have horigP_w : origPtr < 2 ^ w := hwords' origPtr (by simp)
  have horigI_w : origIdx < 2 ^ w := hwords' origIdx (by simp)
  have horigV_w : origVal < 2 ^ w := hwords' origVal (by simp)
  have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  let Regs : ℕ → State → Prop := fun c st =>
    (st.regs 0 = uIdx ∧ st.regs 1 = vIdx ∧ st.regs 2 = wSrc ∧ st.regs 3 = K) ∧
    (st.regs 4 = cnt ∧ st.regs 5 = L_sim ∧ st.regs 6 = 2 ^ h ∧ st.regs 8 = origPtr) ∧
    (st.regs 9 = origIdx ∧ st.regs 10 = origVal ∧
      st.regs 11 = pos + c * (3 * L_sim) ∧ st.regs 12 = L_sim - K ∧ st.regs 13 = c)
  let Inv : ℕ → State → Prop := fun c st =>
    Regs c st ∧
    (∀ t < c, st.mem (origPtr + origIdx + t) = origVal) ∧
    (∀ t < c,
      LimbsAt st.mem (pos + t * (3 * L_sim)) L_sim h uIdx ∧
      LimbsAt st.mem (pos + t * (3 * L_sim) + L_sim) L_sim h vIdx ∧
      LimbsAt st.mem (pos + t * (3 * L_sim) + 2 * L_sim) L_sim h wVal) ∧
    (∀ a, (a < pos ∨ pos + c * (3 * L_sim) ≤ a) →
      (a < origPtr + origIdx ∨ origPtr + origIdx + c ≤ a) → st.mem a = mem a)
  refine runs_start_le ?_
  refine runs_seq_assign_step (Expr.eval_reg_of_eq (v := pos) (by simp [startState])) rfl fun st1 hm1 _ hr1 => ?_
  refine runs_seq_assign_step (Expr.eval_sub
    (Expr.eval_reg_of_eq (v := L_sim) (by rw [hr1, Function.update_of_ne (by decide)]; simp [startState]))
    (Expr.eval_reg_of_eq (v := K) (by rw [hr1, Function.update_of_ne (by decide)]; simp [startState])) hL_w) rfl fun st2 hm2 _ hr2 => ?_
  have hloop := Triple.forRange_const (w := w) (p := P) (r := 13) (lo := .const 0) (hi := .reg 4)
    (body :=
      .store (.bin .add (.reg 8) (.bin .add (.reg 9) (.reg 13))) (.reg 10) ;;
      .call 14 (a + idxFromHost) [.reg 0, .reg 11, .reg 5, .reg 6] ;;
      .assign 11 (.bin .add (.reg 11) (.reg 5)) ;;
      .call 14 (a + idxFromHost) [.reg 1, .reg 11, .reg 5, .reg 6] ;;
      .assign 11 (.bin .add (.reg 11) (.reg 5)) ;;
      .call 14 (a + idxCopy) [.reg 2, .reg 11, .reg 3] ;;
      .call 14 (a + idxZero) [.bin .add (.reg 11) (.reg 3), .reg 12] ;;
      .assign 11 (.bin .add (.reg 11) (.reg 5)))
    (P := fun st => st = st2) (Inv := Inv) (70 * L_sim + 99) 0 cnt (Nat.zero_le _) hw1 (fun _ => hcnt_w)
    (fun st hst => by
      rw [hst]
      refine ⟨Expr.eval_const (Nat.lt_trans Nat.zero_lt_one hw1), ?_⟩
      dsimp only [Inv, Regs]
      rw [hm2, hm1]
      refine ⟨⟨⟨by rw [Function.update_of_ne (by decide), hr2, Function.update_of_ne (by decide), hr1, Function.update_of_ne (by decide)]; simp [startState],
          by rw [Function.update_of_ne (by decide), hr2, Function.update_of_ne (by decide), hr1, Function.update_of_ne (by decide)]; simp [startState],
          by rw [Function.update_of_ne (by decide), hr2, Function.update_of_ne (by decide), hr1, Function.update_of_ne (by decide)]; simp [startState],
          by rw [Function.update_of_ne (by decide), hr2, Function.update_of_ne (by decide), hr1, Function.update_of_ne (by decide)]; simp [startState]⟩,
        ⟨by rw [Function.update_of_ne (by decide), hr2, Function.update_of_ne (by decide), hr1, Function.update_of_ne (by decide)]; simp [startState],
          by rw [Function.update_of_ne (by decide), hr2, Function.update_of_ne (by decide), hr1, Function.update_of_ne (by decide)]; simp [startState],
          by rw [Function.update_of_ne (by decide), hr2, Function.update_of_ne (by decide), hr1, Function.update_of_ne (by decide)]; simp [startState],
          by rw [Function.update_of_ne (by decide), hr2, Function.update_of_ne (by decide), hr1, Function.update_of_ne (by decide)]; simp [startState]⟩,
        ⟨by rw [Function.update_of_ne (by decide), hr2, Function.update_of_ne (by decide), hr1, Function.update_of_ne (by decide)]; simp [startState],
          by rw [Function.update_of_ne (by decide), hr2, Function.update_of_ne (by decide), hr1, Function.update_of_ne (by decide)]; simp [startState],
          by rw [Function.update_of_ne (by decide), hr2, Function.update_of_ne (by decide), hr1, Function.update_self]; simp,
          by rw [Function.update_of_ne (by decide), hr2, Function.update_self],
          by rw [Function.update_self]⟩⟩,
        fun t ht => False.elim (Nat.not_lt_zero _ ht),
        fun t ht => False.elim (Nat.not_lt_zero _ ht), fun _ _ _ => rfl⟩)
    (fun _ st _ _ hi => hi.1.2.2.2.2.2.2)
    (fun _ st _ _ hi => Expr.eval_reg_of_eq hi.1.2.1.1)
    (fun c _ hc_lt => by
      intro st ω hInv
      have hrg := hInv.1
      have r0 := hrg.1.1
      have r1 := hrg.1.2.1
      have r2 := hrg.1.2.2.1
      have r3 := hrg.1.2.2.2
      have r4 := hrg.2.1.1
      have r5 := hrg.2.1.2.1
      have r6 := hrg.2.1.2.2.1
      have r8 := hrg.2.1.2.2.2
      have r9 := hrg.2.2.1
      have r10 := hrg.2.2.2.1
      have r11 := hrg.2.2.2.2.1
      have r12 := hrg.2.2.2.2.2.1
      have r13 := hrg.2.2.2.2.2.2
      have ho_prev := hInv.2.1
      have hl_prev := hInv.2.2.1
      have hfr_prev := hInv.2.2.2
      have hc_w : c < 2 ^ w := lt_trans hc_lt hcnt_w
      have hmul_c : (c + 1) * (3 * L_sim) ≤ cnt * (3 * L_sim) := Nat.mul_le_mul_right _ hc_lt
      rw [Nat.add_mul, Nat.one_mul] at hmul_c
      let baseC := pos + c * (3 * L_sim)
      have hb3_w : baseC + 3 * L_sim < 2 ^ w := by dsimp only [baseC]; linarith only [hpos_w, hmul_c]
      have hb2_w : baseC + 2 * L_sim < 2 ^ w := by linarith only [hb3_w, Nat.zero_le L_sim]
      have hb1_w : baseC + L_sim < 2 ^ w := by linarith only [hb2_w, Nat.zero_le L_sim]
      have hb0_w : baseC < 2 ^ w := by linarith only [hb1_w, Nat.zero_le L_sim]
      have horig_c_w : origPtr + (origIdx + c) < 2 ^ w := by linarith only [horig_w, hc_lt]
      have horig_c_add : origIdx + c < 2 ^ w := by linarith only [horig_c_w, Nat.zero_le origPtr]
      have hsub_add : baseC + L_sim + L_sim + K + (L_sim - K) = baseC + 3 * L_sim := by
        have hks := Nat.add_sub_cancel' hKL
        linarith only [hks]
      have hwSrc_cur : ∀ i < K, st.mem (wSrc + i) = mem (wSrc + i) := fun i hi => by
        refine hfr_prev (wSrc + i) ?_ ?_
        · rcases hdw_pos with h1 | h1
          · left; linarith only [h1, hi]
          · right; linarith only [h1, hmul_c, Nat.zero_le L_sim, Nat.zero_le i]
        · rcases hdo_w with h1 | h1
          · right; linarith only [h1, hc_lt, Nat.zero_le i]
          · left; linarith only [h1, hi]
      have hw_cur : LimbsAt st.mem wSrc K h wVal :=
        hw_limbs.congr fun k hk1 hk2 => by
          have hw := hwSrc_cur (k - wSrc) (Nat.sub_lt_left_of_lt_add hk1 hk2)
          rw [Nat.add_sub_of_le hk1] at hw
          exact hw
      refine runs_start_le ?_
      refine runs_seq_store_step
        (Expr.eval_add (Expr.eval_reg_of_eq r8)
          (Expr.eval_add (Expr.eval_reg_of_eq r9) (Expr.eval_reg_of_eq r13) horig_c_add) horig_c_w)
        (Expr.eval_reg_of_eq r10) rfl fun s1 hm_s1 hr_s1 _ => ?_
      have hne_s1_w : ∀ a, wSrc ≤ a → a < wSrc + K → s1.mem a = st.mem a := fun a ha1 ha2 => by
        rw [hm_s1, Function.update_of_ne]
        rcases hdo_w with h1 | h1
        · exact Nat.ne_of_gt (by linarith only [h1, hc_lt, ha1])
        · exact Nat.ne_of_lt (by linarith only [h1, ha2])
      have hw_s1 : LimbsAt s1.mem wSrc K h wVal := hw_cur.congr hne_s1_w
      have hs1_11 : s1.regs 11 = baseC := by rw [hr_s1]; exact r11
      refine runs_seq_call_step hfh_mc (vs := [uIdx, baseC, L_sim, 2 ^ h])
        (evalArgs_cons (Expr.eval_reg_of_eq (by rw [hr_s1]; exact r0))
          (evalArgs_cons (Expr.eval_reg_of_eq hs1_11)
            (evalArgs_cons (Expr.eval_reg_of_eq (by rw [hr_s1]; exact r5))
              (evalArgs_cons (Expr.eval_reg_of_eq (by rw [hr_s1]; exact r6)) (evalArgs_nil _ _)))))
        (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with hx | hx | hx | hx <;> rw [hx]
          · exact hu_w
          · exact hb0_w
          · exact hL_w
          · exact hB_w)
        ⟨uIdx, baseC, L_sim, h, rfl, hh, hw2, hb1_w⟩
        rfl (rfl : _ = 25 * L_sim + 15) fun _ mem_u s2 hpu hm_s2 hr_s2 => ?_
      obtain ⟨_, _, _, _, heq_u, _, hdu, hfu⟩ := hpu
      simp only [List.cons.injEq, and_true] at heq_u
      rcases heq_u with ⟨h1u, h2u, h3u, h4u⟩
      have heq_hu := Nat.pow_right_injective (by norm_num) h4u
      rw [← h1u, ← h2u, ← h3u, ← heq_hu] at hdu
      rw [← h2u, ← h3u] at hfu
      have hs2_11 : s2.regs 11 = baseC := by rw [hr_s2, Function.update_of_ne (by decide), hs1_11]
      have hs2_5 : s2.regs 5 = L_sim := by rw [hr_s2, Function.update_of_ne (by decide), hr_s1]; exact r5
      refine runs_seq_assign_step (Expr.eval_add (Expr.eval_reg_of_eq hs2_11) (Expr.eval_reg_of_eq hs2_5) hb1_w)
        rfl fun s3 hm_s3 _ hr_s3 => ?_
      have hs3_mem : s3.mem = mem_u := hm_s3.trans hm_s2
      refine runs_seq_call_step hfh_mc (vs := [vIdx, baseC + L_sim, L_sim, 2 ^ h])
        (evalArgs_cons (Expr.eval_reg_of_eq (by rw [hr_s3, hr_s2, Function.update_of_ne (by decide), hr_s1]; exact r1))
          (evalArgs_cons (Expr.eval_reg_of_eq (by rw [hr_s3, Function.update_self]))
            (evalArgs_cons (Expr.eval_reg_of_eq (by rw [hr_s3, Function.update_of_ne (by decide)]; exact hs2_5))
              (evalArgs_cons (Expr.eval_reg_of_eq (by rw [hr_s3, hr_s2, Function.update_of_ne (by decide), hr_s1]; exact r6))
                (evalArgs_nil _ _)))))
        (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with hx | hx | hx | hx <;> rw [hx]
          · exact hv_w
          · exact hb1_w
          · exact hL_w
          · exact hB_w)
        ⟨vIdx, baseC + L_sim, L_sim, h, rfl, hh, hw2, (by linarith only [hb2_w])⟩
        rfl (rfl : _ = 25 * L_sim + 15) fun _ mem_v s4 hpv hm_s4 hr_s4 => ?_
      rw [hs3_mem] at hpv
      obtain ⟨_, _, _, _, heq_v, _, hdv, hfv⟩ := hpv
      simp only [List.cons.injEq, and_true] at heq_v
      rcases heq_v with ⟨h1v, h2v, h3v, h4v⟩
      have heq_hv := Nat.pow_right_injective (by norm_num) h4v
      rw [← h1v, ← h2v, ← h3v, ← heq_hv] at hdv
      rw [← h2v, ← h3v] at hfv
      have hs4_11 : s4.regs 11 = baseC + L_sim := by
        rw [hr_s4, Function.update_of_ne (by decide), hr_s3, Function.update_self]
      have hs4_5 : s4.regs 5 = L_sim := by
        rw [hr_s4, Function.update_of_ne (by decide), hr_s3, Function.update_of_ne (by decide)]; exact hs2_5
      refine runs_seq_assign_step (Expr.eval_add (Expr.eval_reg_of_eq hs4_11) (Expr.eval_reg_of_eq hs4_5) (by linarith only [hb2_w]))
        rfl fun s5 hm_s5 _ hr_s5 => ?_
      have hs5_mem : s5.mem = mem_v := hm_s5.trans hm_s4
      have hwSrc_disj : baseC + L_sim + L_sim + K ≤ wSrc ∨ wSrc + K ≤ baseC + L_sim + L_sim ∨ wSrc = baseC + L_sim + L_sim := by
        rcases hdw_pos with h1 | h1
        · right; left; dsimp only [baseC]; linarith only [h1, Nat.zero_le (c * (3 * L_sim)), Nat.zero_le L_sim]
        · left; dsimp only [baseC]; linarith only [h1, hmul_c, hKL]
      have hdisj_w_v : ∀ a, wSrc ≤ a → a < wSrc + K → mem_v a = s1.mem a := fun a ha1 ha2 => by
        have hlt1 : a < baseC + L_sim ∨ baseC + L_sim + L_sim ≤ a := by
          rcases hdw_pos with h1 | h1
          · left; dsimp only [baseC]; linarith only [ha2, h1, Nat.zero_le (c * (3 * L_sim)), Nat.zero_le L_sim]
          · right; dsimp only [baseC]; linarith only [ha1, h1, hmul_c, Nat.zero_le L_sim]
        have hlt2 : a < baseC ∨ baseC + L_sim ≤ a := by
          rcases hdw_pos with h1 | h1
          · left; dsimp only [baseC]; linarith only [ha2, h1, Nat.zero_le (c * (3 * L_sim))]
          · right; dsimp only [baseC]; linarith only [ha1, h1, hmul_c, Nat.zero_le L_sim]
        rw [hfv a hlt1, hfu a hlt2]
      have hw_s5 : LimbsAt s5.mem wSrc K h wVal := by
        rw [hs5_mem]; exact hw_s1.congr hdisj_w_v
      have hs5_2 : s5.regs 2 = wSrc := by
        rw [hr_s5, Function.update_of_ne (by decide), hr_s4, Function.update_of_ne (by decide),
          hr_s3, Function.update_of_ne (by decide), hr_s2, Function.update_of_ne (by decide), hr_s1]; exact r2
      have hs5_3 : s5.regs 3 = K := by
        rw [hr_s5, Function.update_of_ne (by decide), hr_s4, Function.update_of_ne (by decide),
          hr_s3, Function.update_of_ne (by decide), hr_s2, Function.update_of_ne (by decide), hr_s1]; exact r3
      have hs5_11 : s5.regs 11 = baseC + L_sim + L_sim := by rw [hr_s5, Function.update_self]
      refine runs_seq_call_step hcp_mc (vs := [wSrc, baseC + L_sim + L_sim, K])
        (evalArgs_cons (Expr.eval_reg_of_eq hs5_2)
          (evalArgs_cons (Expr.eval_reg_of_eq hs5_11)
            (evalArgs_cons (Expr.eval_reg_of_eq hs5_3) (evalArgs_nil _ _))))
        (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with hx | hx | hx <;> rw [hx]
          · exact lt_of_le_of_lt (Nat.le_add_right _ _) hwSrc_w
          · linarith only [hb2_w]
          · exact hK_w)
        ⟨wSrc, baseC + L_sim + L_sim, K, rfl, hw1, hwSrc_w, by linarith only [hb3_w, hKL], hwSrc_disj⟩
        rfl (rfl : _ = 17 * K + 10) fun _ mem_w s6 hpw hm_s6 hr_s6 => ?_
      rw [hs5_mem] at hpw
      obtain ⟨_, _, _, heq_w, _, hcw, hfw⟩ := hpw
      simp only [List.cons.injEq, and_true] at heq_w
      rcases heq_w with ⟨h1w, h2w, h3w⟩
      rw [← h1w, ← h2w, ← h3w] at hcw
      rw [← h2w, ← h3w] at hfw
      have hs6_3 : s6.regs 3 = K := by rw [hr_s6, Function.update_of_ne (by decide)]; exact hs5_3
      have hs6_11 : s6.regs 11 = baseC + L_sim + L_sim := by rw [hr_s6, Function.update_of_ne (by decide)]; exact hs5_11
      have hs6_12 : s6.regs 12 = L_sim - K := by
        rw [hr_s6, Function.update_of_ne (by decide), hr_s5, Function.update_of_ne (by decide),
          hr_s4, Function.update_of_ne (by decide), hr_s3, Function.update_of_ne (by decide),
          hr_s2, Function.update_of_ne (by decide), hr_s1]; exact r12
      refine runs_seq_call_step hzr_mc (vs := [baseC + L_sim + L_sim + K, L_sim - K])
        (evalArgs_cons (Expr.eval_add (Expr.eval_reg_of_eq hs6_11) (Expr.eval_reg_of_eq hs6_3) (by linarith only [hb3_w, hKL]))
          (evalArgs_cons (Expr.eval_reg_of_eq hs6_12) (evalArgs_nil _ _)))
        (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with hx | hx <;> rw [hx]
          · linarith only [hb3_w, hKL]
          · linarith only [Nat.sub_le L_sim K, hL_w])
        ⟨baseC + L_sim + L_sim + K, L_sim - K, rfl, hw1, by linarith only [hb3_w, hsub_add]⟩
        rfl (rfl : _ = 14 * (L_sim - K) + 12) fun _ mem_z s7 hpz hm_s7 hr_s7 => ?_
      obtain ⟨_, _, heq_z, _, hzw, hfz⟩ := hpz
      simp only [List.cons.injEq, and_true] at heq_z
      rcases heq_z with ⟨h1z, h2z⟩
      rw [← h1z, ← h2z] at hzw hfz
      rw [hm_s6] at hfz
      have hzw_p : ∀ i < L_sim - K, mem_z (baseC + L_sim + L_sim + K + i) = 0 := fun i hi => by
        have hg := hzw i (by simpa [List.length_replicate] using hi)
        simp only [List.getElem_replicate] at hg
        exact hg
      have hfz_eq : ∀ q, q < baseC + L_sim + L_sim + K ∨ baseC + 3 * L_sim ≤ q → mem_z q = mem_w q := fun q hq => by
        apply hfz q
        rcases hq with hq | hq
        · left; exact hq
        · right; linarith only [hq, hsub_add]
      have hs7_5 : s7.regs 5 = L_sim := by
        rw [hr_s7, Function.update_of_ne (by decide), hr_s6, Function.update_of_ne (by decide), hr_s5,
          Function.update_of_ne (by decide)]; exact hs4_5
      have hs7_11 : s7.regs 11 = baseC + L_sim + L_sim := by
        rw [hr_s7, Function.update_of_ne (by decide)]; exact hs6_11
      have hkeep_r : ∀ r < 14, r ≠ 11 → s7.regs r = st.regs r := fun r hr14 hr11 => by
        rw [hr_s7, Function.update_of_ne (by omega),
          hr_s6, Function.update_of_ne (by omega), hr_s5, Function.update_of_ne hr11,
          hr_s4, Function.update_of_ne (by omega), hr_s3, Function.update_of_ne hr11,
          hr_s2, Function.update_of_ne (by omega), hr_s1]
      have hne_prev_block : ∀ q, q < baseC ∨ baseC + 3 * L_sim ≤ q →
          q ≠ origPtr + (origIdx + c) → mem_z q = st.mem q := fun q hq hno => by
        have hq' : q < baseC + L_sim + L_sim + K ∨ baseC + 3 * L_sim ≤ q := by
          rcases hq with hq | hq
          · left; linarith only [hq, Nat.zero_le L_sim, Nat.zero_le K]
          · right; exact hq
        have hqw : q < baseC + L_sim + L_sim ∨ baseC + L_sim + L_sim + K ≤ q := by
          rcases hq with hq | hq
          · left; linarith only [hq, Nat.zero_le L_sim]
          · right; linarith only [hq, hKL]
        have hqv : q < baseC + L_sim ∨ baseC + L_sim + L_sim ≤ q := by
          rcases hq with hq | hq
          · left; linarith only [hq, Nat.zero_le L_sim]
          · right; linarith only [hq, Nat.zero_le L_sim]
        have hqu : q < baseC ∨ baseC + L_sim ≤ q := by
          rcases hq with hq | hq
          · left; exact hq
          · right; linarith only [hq, Nat.zero_le L_sim]
        rw [hfz_eq q hq', hfw q hqw, hfv q hqv, hfu q hqu, hm_s1, Function.update_of_ne hno]
      refine runs_assign_le (Expr.eval_add (Expr.eval_reg_of_eq hs7_11) (Expr.eval_reg_of_eq hs7_5) (by linarith only [hb3_w])) ?_ ?_
      · refine ⟨⟨⟨⟨by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hkeep_r 0 (by decide) (by decide)]; exact r0,
            by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hkeep_r 1 (by decide) (by decide)]; exact r1,
            by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hkeep_r 2 (by decide) (by decide)]; exact r2,
            by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hkeep_r 3 (by decide) (by decide)]; exact r3⟩,
          ⟨by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hkeep_r 4 (by decide) (by decide)]; exact r4,
            by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hkeep_r 5 (by decide) (by decide)]; exact r5,
            by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hkeep_r 6 (by decide) (by decide)]; exact r6,
            by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hkeep_r 8 (by decide) (by decide)]; exact r8⟩,
          ⟨by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hkeep_r 9 (by decide) (by decide)]; exact r9,
            by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hkeep_r 10 (by decide) (by decide)]; exact r10,
            by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self]; dsimp only [baseC]; ring,
            by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hkeep_r 12 (by decide) (by decide)]; exact r12,
            by dsimp only; rw [Function.update_self]⟩⟩,
          ?_, ?_, ?_⟩,
          by dsimp only; rw [Function.update_of_ne (by decide), hkeep_r 13 (by decide) (by decide)]; exact r13⟩
        · intro t ht
          dsimp only; rw [hm_s7]
          by_cases htc : t = c
          · rw [htc]
            have ho_disj : origPtr + (origIdx + c) < baseC ∨ baseC + 3 * L_sim ≤ origPtr + (origIdx + c) := by
              rcases hdo_pos with h1 | h1
              · left; dsimp only [baseC]; linarith only [h1, hc_lt, Nat.zero_le (c * (3 * L_sim))]
              · right; dsimp only [baseC]; linarith only [h1, hmul_c, Nat.zero_le c]
            have hq' : origPtr + (origIdx + c) < baseC + L_sim + L_sim + K ∨ baseC + 3 * L_sim ≤ origPtr + (origIdx + c) := by
              rcases ho_disj with h1 | h1
              · left; linarith only [h1, Nat.zero_le L_sim, Nat.zero_le K]
              · right; exact h1
            have hqw : origPtr + (origIdx + c) < baseC + L_sim + L_sim ∨ baseC + L_sim + L_sim + K ≤ origPtr + (origIdx + c) := by
              rcases ho_disj with h1 | h1
              · left; linarith only [h1, Nat.zero_le L_sim]
              · right; linarith only [h1, hKL]
            have hqv : origPtr + (origIdx + c) < baseC + L_sim ∨ baseC + L_sim + L_sim ≤ origPtr + (origIdx + c) := by
              rcases ho_disj with h1 | h1
              · left; linarith only [h1, Nat.zero_le L_sim]
              · right; linarith only [h1, Nat.zero_le L_sim]
            have hqu : origPtr + (origIdx + c) < baseC ∨ baseC + L_sim ≤ origPtr + (origIdx + c) :=
              ho_disj.elim Or.inl (fun h1 => Or.inr (by linarith only [h1, Nat.zero_le L_sim]))
            rw [Nat.add_assoc origPtr origIdx c, hfz_eq _ hq', hfw _ hqw, hfv _ hqv, hfu _ hqu, hm_s1]
            exact Function.update_self (origPtr + (origIdx + c)) origVal st.mem
          · have htl : t < c := lt_of_le_of_ne (Nat.lt_succ_iff.mp ht) htc
            have hno : origPtr + origIdx + t ≠ origPtr + (origIdx + c) :=
              Nat.ne_of_lt (by linarith only [htl])
            have hoa : origPtr + origIdx + t < baseC ∨ baseC + 3 * L_sim ≤ origPtr + origIdx + t := by
              rcases hdo_pos with h1 | h1
              · left; dsimp only [baseC]; linarith only [h1, htl, hc_lt, Nat.zero_le (c * (3 * L_sim))]
              · right; dsimp only [baseC]; linarith only [h1, hmul_c, Nat.zero_le t]
            rw [hne_prev_block (origPtr + origIdx + t) hoa hno]
            exact ho_prev t htl
        · intro t ht
          dsimp only; rw [hm_s7]
          by_cases htc : t = c
          · rw [htc]
            have hlu : LimbsAt mem_u baseC L_sim h uIdx := limbsAt_of_fromHost hu_lt hdu
            have hlv : LimbsAt mem_v (baseC + L_sim) L_sim h vIdx := limbsAt_of_fromHost hv_lt hdv
            have hlu' : LimbsAt mem_z baseC L_sim h uIdx := hlu.congr fun q hq1 hq2 => by
              rw [hfz_eq q (Or.inl (by linarith only [hq2, Nat.zero_le L_sim, Nat.zero_le K])),
                hfw q (Or.inl (by linarith only [hq2, Nat.zero_le L_sim])),
                hfv q (Or.inl hq2)]
            have hlv' : LimbsAt mem_z (baseC + L_sim) L_sim h vIdx := hlv.congr fun q hq1 hq2 => by
              rw [hfz_eq q (Or.inl (by linarith only [hq2, Nat.zero_le K])), hfw q (Or.inl hq2)]
            have hlw' : LimbsAt mem_z (baseC + 2 * L_sim) L_sim h wVal := by
              refine limbsAt_of_copy_zeroExt hKL (by rw [hs5_mem] at hw_s5; exact hw_s5) ?_ ?_
              · intro i hi
                rw [show baseC + 2 * L_sim + i = baseC + L_sim + L_sim + i by ring]
                rw [hfz_eq _ (Or.inl (by linarith only [hi])), hcw i hi]
              · intro i hi1 hi2
                have hs := Nat.add_sub_cancel' hi1
                have hsub : baseC + 2 * L_sim + i = baseC + L_sim + L_sim + K + (i - K) := by linarith only [hs]
                rw [hsub]
                exact hzw_p (i - K) (by omega)
            exact ⟨hlu', hlv', hlw'⟩
          · have htl : t < c := lt_of_le_of_ne (Nat.lt_succ_iff.mp ht) htc
            have hpv := hl_prev t htl
            have hm_mul : (t + 1) * (3 * L_sim) ≤ c * (3 * L_sim) := Nat.mul_le_mul_right _ htl
            rw [Nat.add_mul, Nat.one_mul] at hm_mul
            have heq_t : ∀ m, pos + t * (3 * L_sim) ≤ m → m < pos + t * (3 * L_sim) + 3 * L_sim → mem_z m = st.mem m := by
              intro m hm1 hm2
              refine hne_prev_block m (Or.inl (by dsimp only [baseC]; linarith only [hm2, hm_mul])) ?_
              rcases hdo_pos with h1 | h1
              · exact Nat.ne_of_gt (by linarith only [h1, hc_lt, hm1, Nat.zero_le (t * (3 * L_sim))])
              · exact Nat.ne_of_lt (by linarith only [h1, hm2, hm_mul, hmul_c, Nat.zero_le c])
            refine ⟨hpv.1.congr fun m h1 h2 => heq_t m h1 (by linarith only [h2, Nat.zero_le L_sim]),
              hpv.2.1.congr fun m h1 h2 => heq_t m (by linarith only [h1, Nat.zero_le L_sim]) (by linarith only [h2, Nat.zero_le L_sim]),
              hpv.2.2.congr fun m h1 h2 => heq_t m (by linarith only [h1, Nat.zero_le L_sim]) (by linarith only [h2])⟩
        · intro a ha hao
          dsimp only; rw [hm_s7]
          have hm_c1 : (c + 1) * (3 * L_sim) = c * (3 * L_sim) + 3 * L_sim := by ring
          rw [hm_c1] at ha
          have ha_blk : a < baseC ∨ baseC + 3 * L_sim ≤ a := by
            rcases ha with h1 | h1
            · left; dsimp only [baseC]; linarith only [h1, Nat.zero_le (c * (3 * L_sim))]
            · right; dsimp only [baseC]; linarith only [h1]
          have hano : a ≠ origPtr + (origIdx + c) := by
            rcases hao with h1 | h1
            · exact Nat.ne_of_lt (by linarith only [h1, Nat.zero_le c])
            · exact Nat.ne_of_gt (by linarith only [h1])
          rw [hne_prev_block a ha_blk hano]
          exact hfr_prev a (ha.elim Or.inl (fun h1 => Or.inr (by linarith only [h1, Nat.zero_le (3 * L_sim)])))
            (hao.elim Or.inl (fun h1 => Or.inr (by linarith only [h1])))
      · have h14 : 14 * K + 14 * (L_sim - K) = 14 * L_sim := by
          have := Nat.add_sub_cancel' hKL
          linarith only [this]
        dsimp only [argsSize, Expr.size]
        linarith only [h14, hKL, Nat.zero_le L_sim, Nat.zero_le K])
  refine runs_seq_triple_le (hloop.conseq (fun _ h => h) (fun o st hq => by
    cases o with | returned _ => exact False.elim hq | normal => exact hq) (fun _ _ => le_rfl)) rfl ?_
  intro st_end hInv_end
  have hr11 := hInv_end.1.2.2.2.2.1
  have ho_end := hInv_end.2.1
  have hl_end := hInv_end.2.2.1
  have hfr_end := hInv_end.2.2.2
  refine runs_ret_le (Expr.eval_reg_of_eq hr11)
    ⟨uIdx, vIdx, wSrc, K, cnt, L_sim, pos, origPtr, origIdx, origVal, wVal, rfl, rfl,
      hw_limbs, ho_end, hl_end, hfr_end⟩ ?_
  dsimp only [encodeEdgeCopiesContract, encodeEdgeCopiesCost, argsSize, Expr.size]
  simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Nat.sub_zero]
  have hmul : cnt * (70 * L_sim + 108) ≤ cnt * (70 * L_sim + 110) :=
    Nat.mul_le_mul_left cnt (by omega)
  linarith only [hmul]

def encodeBridgesCost (B_len L_sim : ℕ) : ℕ :=
  B_len * (65 * L_sim + 100) + 20

def encodeBridgesContract (w h : ℕ) : Contract where
  pre args mem :=
    ∃ B_len bArr vIdxPtr L_sim pos, ∃ bIdxs : List ℕ,
      args = [B_len, bArr, vIdxPtr, L_sim, 2 ^ h, pos] ∧
      1 ≤ h ∧ 2 * h + 2 ≤ w ∧ 1 ≤ L_sim ∧
      bArr + B_len < 2 ^ w ∧ pos + B_len * (3 * L_sim) < 2 ^ w ∧
      bIdxs.length = B_len ∧
      (∀ k < B_len,
        mem (bArr + k) < 2 ^ w ∧
        mem (vIdxPtr + mem (bArr + k)) = bIdxs.getD k 0 ∧
        vIdxPtr + mem (bArr + k) < 2 ^ w ∧
        bIdxs.getD k 0 < 2 ^ (L_sim * h) ∧ bIdxs.getD k 0 < 2 ^ w) ∧
      (∀ k < B_len, bArr + k < pos ∨ pos + B_len * (3 * L_sim) ≤ bArr + k) ∧
      (∀ k < B_len, vIdxPtr + mem (bArr + k) < pos ∨ pos + B_len * (3 * L_sim) ≤ vIdxPtr + mem (bArr + k))
  post args mem ret mem' :=
    ∃ B_len bArr vIdxPtr L_sim pos, ∃ bIdxs : List ℕ,
      args = [B_len, bArr, vIdxPtr, L_sim, 2 ^ h, pos] ∧
      ret = pos + B_len * (3 * L_sim) ∧
      bIdxs.length = B_len ∧
      (∀ k < B_len, mem (vIdxPtr + mem (bArr + k)) = bIdxs.getD k 0) ∧
      (∀ k < B_len,
        LimbsAt mem' (pos + k * (3 * L_sim)) L_sim h 0 ∧
        LimbsAt mem' (pos + k * (3 * L_sim) + L_sim) L_sim h (bIdxs.getD k 0) ∧
        LimbsAt mem' (pos + k * (3 * L_sim) + 2 * L_sim) L_sim h 1) ∧
      (∀ a, a < pos ∨ pos + B_len * (3 * L_sim) ≤ a → mem' a = mem a)
  cost args _ := encodeBridgesCost (args.getD 0 0) (args.getD 3 0)

theorem encodeBridges_meetsContract {w b h a p w' s e : ℕ} {P : Program}
    (hp : P.HasAt b (encodeDecodeModule a p w' s e))
    (ha : P.HasAt a (arithModule a)) :
    MeetsContract w P (b + idxEncodeBridges) (encodeBridgesContract w h) := by
  have hproc : P.procs[b + idxEncodeBridges]? = some (encodeBridgesProc a) := by
    have := hp 1 (by rw [encodeDecodeModule_length]; omega)
    simpa [encodeDecodeModule, idxEncodeBridges] using this
  have hfh_mc := mwFromHost_of_arithModule (w := w) ha
  have hzr_mc := mwZero_of_arithModule (w := w) ha
  refine meetsContract_of_runs hproc ?_
  intro args mem pos₀ ω hwords hpre
  rcases hpre with ⟨B_len, bArr, vIdxPtr, L_sim, pos, bIdxs, hargs, hpr⟩
  have hwords' : ∀ a ∈ [B_len, bArr, vIdxPtr, L_sim, 2 ^ h, pos], a < 2 ^ w := hargs ▸ hwords
  rw [hargs]
  have hh := hpr.1
  have hw2 := hpr.2.1
  have hL1 := hpr.2.2.1
  have hb_w := hpr.2.2.2.1
  have hpos_w := hpr.2.2.2.2.1
  have hblen := hpr.2.2.2.2.2.1
  have hb_spec := hpr.2.2.2.2.2.2.1
  have hdb_pos := hpr.2.2.2.2.2.2.2.1
  have hdv_pos := hpr.2.2.2.2.2.2.2.2
  have hB_w : B_len < 2 ^ w := hwords' B_len (by simp)
  have hbArr_w : bArr < 2 ^ w := hwords' bArr (by simp)
  have hvIdx_w : vIdxPtr < 2 ^ w := hwords' vIdxPtr (by simp)
  have hL_w : L_sim < 2 ^ w := hwords' L_sim (by simp)
  have h2h_w : 2 ^ h < 2 ^ w := hwords' (2 ^ h) (by simp)
  have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have h1_lt : 1 < 2 ^ (L_sim * h) := Nat.one_lt_two_pow (by positivity)
  let Regs : ℕ → State → Prop := fun k st =>
    (st.regs 0 = B_len ∧ st.regs 1 = bArr ∧ st.regs 2 = vIdxPtr ∧ st.regs 3 = L_sim) ∧
    (st.regs 4 = 2 ^ h ∧ st.regs 6 = pos + k * (3 * L_sim) ∧ st.regs 7 = k)
  let Inv : ℕ → State → Prop := fun k st =>
    Regs k st ∧
    (∀ t (ht : t < k),
      LimbsAt st.mem (pos + t * (3 * L_sim)) L_sim h 0 ∧
      LimbsAt st.mem (pos + t * (3 * L_sim) + L_sim) L_sim h (bIdxs.getD t 0) ∧
      LimbsAt st.mem (pos + t * (3 * L_sim) + 2 * L_sim) L_sim h 1) ∧
    (∀ t, t < pos ∨ pos + k * (3 * L_sim) ≤ t → st.mem t = mem t)
  refine runs_start_le ?_
  refine runs_seq_assign_step (Expr.eval_reg_of_eq (v := pos) (by simp [startState])) rfl fun st1 hm1 _ hr1 => ?_
  have hloop := Triple.forRange_const (w := w) (p := P) (r := 7) (lo := .const 0) (hi := .reg 0)
    (body :=
      .call 8 (a + idxZero) [.reg 6, .reg 3] ;;
      .assign 6 (.bin .add (.reg 6) (.reg 3)) ;;
      .assign 8 (.load (.bin .add (.reg 1) (.reg 7))) ;;
      .assign 8 (.load (.bin .add (.reg 2) (.reg 8))) ;;
      .call 9 (a + idxFromHost) [.reg 8, .reg 6, .reg 3, .reg 4] ;;
      .assign 6 (.bin .add (.reg 6) (.reg 3)) ;;
      .call 8 (a + idxFromHost) [.const 1, .reg 6, .reg 3, .reg 4] ;;
      .assign 6 (.bin .add (.reg 6) (.reg 3)))
    (P := fun st => st = st1) (Inv := Inv) (64 * L_sim + 86) 0 B_len (Nat.zero_le _) hw1 (fun _ => hB_w)
    (fun st hst => by
      rw [hst]
      refine ⟨Expr.eval_const (Nat.lt_trans Nat.zero_lt_one hw1), ?_⟩
      dsimp only [Inv, Regs]
      rw [hm1]
      refine ⟨⟨⟨by rw [Function.update_of_ne (by decide), hr1, Function.update_of_ne (by decide)]; simp [startState],
          by rw [Function.update_of_ne (by decide), hr1, Function.update_of_ne (by decide)]; simp [startState],
          by rw [Function.update_of_ne (by decide), hr1, Function.update_of_ne (by decide)]; simp [startState],
          by rw [Function.update_of_ne (by decide), hr1, Function.update_of_ne (by decide)]; simp [startState]⟩,
        ⟨by rw [Function.update_of_ne (by decide), hr1, Function.update_of_ne (by decide)]; simp [startState],
          by rw [Function.update_of_ne (by decide), hr1, Function.update_self]; simp,
          by rw [Function.update_self]⟩⟩,
        fun t ht => False.elim (Nat.not_lt_zero _ ht), fun _ _ => rfl⟩)
    (fun _ st _ _ hi => hi.1.2.2.2)
    (fun _ st _ _ hi => Expr.eval_reg_of_eq hi.1.1.1)
    (fun k _ hk_lt => by
      intro st ω hInv
      have r0 := hInv.1.1.1
      have r1 := hInv.1.1.2.1
      have r2 := hInv.1.1.2.2.1
      have r3 := hInv.1.1.2.2.2
      have r4 := hInv.1.2.1
      have r6 := hInv.1.2.2.1
      have r7 := hInv.1.2.2.2
      have hl_prev := hInv.2.1
      have hfr_prev := hInv.2.2
      have hk_w : k < 2 ^ w := lt_trans hk_lt hB_w
      have hmul_k : (k + 1) * (3 * L_sim) ≤ B_len * (3 * L_sim) := Nat.mul_le_mul_right _ hk_lt
      rw [Nat.add_mul, Nat.one_mul] at hmul_k
      let baseK := pos + k * (3 * L_sim)
      have hb3_w : baseK + 3 * L_sim < 2 ^ w := by dsimp only [baseK]; linarith only [hpos_w, hmul_k]
      have hb2_w : baseK + 2 * L_sim < 2 ^ w := by linarith only [hb3_w, Nat.zero_le L_sim]
      have hb1_w : baseK + L_sim < 2 ^ w := by linarith only [hb2_w, Nat.zero_le L_sim]
      have hb0_w : baseK < 2 ^ w := by linarith only [hb1_w, Nat.zero_le L_sim]
      have hbSpec := hb_spec k hk_lt
      have hb_mem_eq : st.mem (bArr + k) = mem (bArr + k) :=
        hfr_prev _ (by
          rcases hdb_pos k hk_lt with h1 | h1
          · left; exact h1
          · right; linarith only [h1, hmul_k, Nat.zero_le L_sim])
      have hv_mem_eq : st.mem (vIdxPtr + mem (bArr + k)) = bIdxs.getD k 0 := by
        rw [hfr_prev _ (by
          rcases hdv_pos k hk_lt with h1 | h1
          · left; exact h1
          · right; linarith only [h1, hmul_k, Nat.zero_le L_sim])]
        exact hbSpec.2.1
      refine runs_start_le ?_
      refine runs_seq_call_step hzr_mc (vs := [baseK, L_sim])
        (evalArgs_cons (Expr.eval_reg_of_eq r6) (evalArgs_cons (Expr.eval_reg_of_eq r3) (evalArgs_nil _ _)))
        (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with hx | hx <;> rw [hx]
          · exact hb0_w
          · exact hL_w)
        ⟨baseK, L_sim, rfl, hw1, hb1_w⟩
        rfl (rfl : _ = 14 * L_sim + 12) fun _ mem_z s1 hpz hm_s1 hr_s1 => ?_
      obtain ⟨_, _, heq_z, _, hzw, hfz⟩ := hpz
      simp only [List.cons.injEq, and_true] at heq_z
      rcases heq_z with ⟨h1z, h2z⟩
      rw [← h1z, ← h2z] at hzw hfz
      have hs1_6 : s1.regs 6 = baseK := by rw [hr_s1, Function.update_of_ne (by decide)]; exact r6
      have hs1_3 : s1.regs 3 = L_sim := by rw [hr_s1, Function.update_of_ne (by decide)]; exact r3
      refine runs_seq_assign_step (Expr.eval_add (Expr.eval_reg_of_eq hs1_6) (Expr.eval_reg_of_eq hs1_3) hb1_w)
        rfl fun s2 hm_s2 _ hr_s2 => ?_
      have hs2_mem : s2.mem = mem_z := hm_s2.trans hm_s1
      have hs2_b_eq : s2.mem (bArr + k) = mem (bArr + k) := by
        rw [hs2_mem, hfz _ (by
          dsimp only [baseK]
          rcases hdb_pos k hk_lt with h1 | h1
          · left; linarith only [h1, Nat.zero_le (k * (3 * L_sim))]
          · right; linarith only [h1, hmul_k, Nat.zero_le L_sim]), hb_mem_eq]
      have hs2_1 : s2.regs 1 = bArr := by
        rw [hr_s2, Function.update_of_ne (by decide), hr_s1, Function.update_of_ne (by decide)]; exact r1
      have hs2_7 : s2.regs 7 = k := by
        rw [hr_s2, Function.update_of_ne (by decide), hr_s1, Function.update_of_ne (by decide)]; exact r7
      refine runs_seq_assign_step
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hs2_1) (Expr.eval_reg_of_eq hs2_7) (by linarith only [hk_lt, hb_w])) hs2_b_eq)
        rfl fun s3 hm_s3 _ hr_s3 => ?_
      have hs3_mem : s3.mem = mem_z := hm_s3.trans hs2_mem
      have hs3_v_eq : s3.mem (vIdxPtr + mem (bArr + k)) = bIdxs.getD k 0 := by
        rw [hs3_mem, hfz _ (by
          dsimp only [baseK]
          rcases hdv_pos k hk_lt with h1 | h1
          · left; linarith only [h1, Nat.zero_le (k * (3 * L_sim))]
          · right; linarith only [h1, hmul_k, Nat.zero_le L_sim]), hv_mem_eq]
      have hs3_2 : s3.regs 2 = vIdxPtr := by
        rw [hr_s3, Function.update_of_ne (by decide), hr_s2, Function.update_of_ne (by decide), hr_s1,
          Function.update_of_ne (by decide)]; exact r2
      have hs3_8 : s3.regs 8 = mem (bArr + k) := by rw [hr_s3, Function.update_self]
      refine runs_seq_assign_step
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hs3_2) (Expr.eval_reg_of_eq hs3_8) hbSpec.2.2.1) hs3_v_eq)
        rfl fun s4 hm_s4 _ hr_s4 => ?_
      have hs4_mem : s4.mem = mem_z := hm_s4.trans hs3_mem
      have hs4_8 : s4.regs 8 = bIdxs.getD k 0 := by rw [hr_s4, Function.update_self]
      have hs4_6 : s4.regs 6 = baseK + L_sim := by
        rw [hr_s4, Function.update_of_ne (by decide), hr_s3, Function.update_of_ne (by decide),
          hr_s2, Function.update_self]
      have hs4_3 : s4.regs 3 = L_sim := by
        rw [hr_s4, Function.update_of_ne (by decide), hr_s3, Function.update_of_ne (by decide),
          hr_s2, Function.update_of_ne (by decide)]; exact hs1_3
      have hs4_4 : s4.regs 4 = 2 ^ h := by
        rw [hr_s4, Function.update_of_ne (by decide), hr_s3, Function.update_of_ne (by decide),
          hr_s2, Function.update_of_ne (by decide), hr_s1, Function.update_of_ne (by decide)]; exact r4
      refine runs_seq_call_step hfh_mc (vs := [bIdxs.getD k 0, baseK + L_sim, L_sim, 2 ^ h])
        (evalArgs_cons (Expr.eval_reg_of_eq hs4_8)
          (evalArgs_cons (Expr.eval_reg_of_eq hs4_6)
            (evalArgs_cons (Expr.eval_reg_of_eq hs4_3)
              (evalArgs_cons (Expr.eval_reg_of_eq hs4_4) (evalArgs_nil _ _)))))
        (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with hx | hx | hx | hx <;> rw [hx]
          · exact hbSpec.2.2.2.2
          · exact hb1_w
          · exact hL_w
          · exact h2h_w)
        ⟨bIdxs.getD k 0, baseK + L_sim, L_sim, h, rfl, hh, hw2, (by linarith only [hb2_w])⟩
        rfl (rfl : _ = 25 * L_sim + 15) fun _ mem_v s5 hpv hm_s5 hr_s5 => ?_
      rw [hs4_mem] at hpv
      obtain ⟨_, _, _, _, heq_v, _, hdv, hfv⟩ := hpv
      simp only [List.cons.injEq, and_true] at heq_v
      rcases heq_v with ⟨h1v, h2v, h3v, h4v⟩
      have h_eqv := Nat.pow_right_injective (by norm_num) h4v
      rw [← h1v, ← h2v, ← h3v, ← h_eqv] at hdv
      rw [← h2v, ← h3v] at hfv
      have hs5_6 : s5.regs 6 = baseK + L_sim := by rw [hr_s5, Function.update_of_ne (by decide)]; exact hs4_6
      have hs5_3 : s5.regs 3 = L_sim := by rw [hr_s5, Function.update_of_ne (by decide)]; exact hs4_3
      refine runs_seq_assign_step (Expr.eval_add (Expr.eval_reg_of_eq hs5_6) (Expr.eval_reg_of_eq hs5_3) (by linarith only [hb2_w]))
        rfl fun s6 hm_s6 _ hr_s6 => ?_
      have hs6_mem : s6.mem = mem_v := hm_s6.trans hm_s5
      have hs6_6 : s6.regs 6 = baseK + L_sim + L_sim := by rw [hr_s6, Function.update_self]
      have hs6_3 : s6.regs 3 = L_sim := by rw [hr_s6, Function.update_of_ne (by decide)]; exact hs5_3
      have hs6_4 : s6.regs 4 = 2 ^ h := by rw [hr_s6, Function.update_of_ne (by decide), hr_s5, Function.update_of_ne (by decide)]; exact hs4_4
      refine runs_seq_call_step hfh_mc (vs := [1, baseK + L_sim + L_sim, L_sim, 2 ^ h])
        (evalArgs_cons (Expr.eval_const hw1)
          (evalArgs_cons (Expr.eval_reg_of_eq hs6_6)
            (evalArgs_cons (Expr.eval_reg_of_eq hs6_3)
              (evalArgs_cons (Expr.eval_reg_of_eq hs6_4) (evalArgs_nil _ _)))))
        (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with hx | hx | hx | hx <;> rw [hx]
          · exact hw1
          · linarith only [hb2_w]
          · exact hL_w
          · exact h2h_w)
        ⟨1, baseK + L_sim + L_sim, L_sim, h, rfl, hh, hw2, by dsimp only [baseK] at *; linarith only [hb3_w]⟩
        rfl (rfl : _ = 25 * L_sim + 15) fun _ mem_1 s7 hp1 hm_s7 hr_s7 => ?_
      rw [hs6_mem] at hp1
      obtain ⟨_, _, _, _, heq_1, _, hd1, hf1⟩ := hp1
      simp only [List.cons.injEq, and_true] at heq_1
      rcases heq_1 with ⟨h1_1, h2_1, h3_1, h4_1⟩
      have h_eq1 := Nat.pow_right_injective (by norm_num) h4_1
      rw [← h1_1, ← h2_1, ← h3_1, ← h_eq1] at hd1
      rw [← h2_1, ← h3_1] at hf1
      have hs7_6 : s7.regs 6 = baseK + L_sim + L_sim := by rw [hr_s7, Function.update_of_ne (by decide)]; exact hs6_6
      have hs7_3 : s7.regs 3 = L_sim := by rw [hr_s7, Function.update_of_ne (by decide)]; exact hs6_3
      have hkeep_regs : ∀ r, r ≠ 6 → r ≠ 8 → r ≠ 9 → s7.regs r = st.regs r := fun r h6 h8 h9 => by
        rw [hr_s7, Function.update_of_ne h8,
          hr_s6, Function.update_of_ne h6, hr_s5, Function.update_of_ne h9,
          hr_s4, Function.update_of_ne h8, hr_s3, Function.update_of_ne h8,
          hr_s2, Function.update_of_ne h6, hr_s1, Function.update_of_ne h8]
      have hne_block : ∀ q, q < baseK ∨ baseK + 3 * L_sim ≤ q → mem_1 q = st.mem q := fun q hq => by
        have hq1 : q < baseK + L_sim + L_sim ∨ baseK + L_sim + L_sim + L_sim ≤ q := by
          rcases hq with h1 | h1 <;> [left; right] <;> linarith only [h1, hL1]
        have hqv : q < baseK + L_sim ∨ baseK + L_sim + L_sim ≤ q := by
          rcases hq with h1 | h1 <;> [left; right] <;> linarith only [h1, hL1]
        have hqz : q < baseK ∨ baseK + L_sim ≤ q := by
          rcases hq with h1 | h1 <;> [left; right] <;> linarith only [h1, hL1]
        rw [hf1 q hq1, hfv q hqv, hfz q hqz]
      refine runs_assign_le (Expr.eval_add (Expr.eval_reg_of_eq hs7_6) (Expr.eval_reg_of_eq hs7_3) (by dsimp only [baseK] at hb3_w ⊢; linarith only [hb3_w])) ?_ ?_
      · refine ⟨⟨⟨⟨by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hkeep_regs 0 (by decide) (by decide) (by decide)]; exact r0,
            by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hkeep_regs 1 (by decide) (by decide) (by decide)]; exact r1,
            by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hkeep_regs 2 (by decide) (by decide) (by decide)]; exact r2,
            by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hkeep_regs 3 (by decide) (by decide) (by decide)]; exact r3⟩,
          ⟨by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hkeep_regs 4 (by decide) (by decide) (by decide)]; exact r4,
            by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self]; dsimp only [baseK]; ring,
            by dsimp only; rw [Function.update_self]⟩⟩,
          ?_, ?_⟩,
          by dsimp only; rw [Function.update_of_ne (by decide), hkeep_regs 7 (by decide) (by decide) (by decide)]; exact r7⟩
        · intro t ht
          dsimp only; rw [hm_s7]
          by_cases htk : t = k
          · rw [htk]
            have hlz : LimbsAt mem_z baseK L_sim h 0 := by
              refine limbsAt_of_fromHost (Nat.zero_lt_of_lt h1_lt) fun i hi => ?_
              rw [Nat.zero_div, Nat.zero_mod]
              have hg := hzw i (by simpa [List.length_replicate] using hi)
              simp only [List.getElem_replicate] at hg
              exact hg
            have hlv : LimbsAt mem_v (baseK + L_sim) L_sim h (bIdxs.getD k 0) :=
              limbsAt_of_fromHost hbSpec.2.2.2.1 hdv
            have hl1 : LimbsAt mem_1 (baseK + 2 * L_sim) L_sim h 1 := by
              rw [show baseK + 2 * L_sim = baseK + L_sim + L_sim by ring]
              exact limbsAt_of_fromHost h1_lt hd1
            exact ⟨hlz.congr fun q h1 h2 => by rw [hf1 q (Or.inl (by linarith only [h1, h2, hL1])), hfv q (Or.inl h2)],
              hlv.congr fun q h1 h2 => by rw [hf1 q (Or.inl h2)],
              hl1⟩
          · have htl : t < k := lt_of_le_of_ne (Nat.lt_succ_iff.mp ht) htk
            have hp := hl_prev t htl
            have hm_mul : (t + 1) * (3 * L_sim) ≤ k * (3 * L_sim) := Nat.mul_le_mul_right _ htl
            rw [Nat.add_mul, Nat.one_mul] at hm_mul
            have heq_t : ∀ q, pos + t * (3 * L_sim) ≤ q → q < pos + t * (3 * L_sim) + 3 * L_sim → mem_1 q = st.mem q := by
              intro q h1 h2
              exact hne_block q (Or.inl (by dsimp only [baseK]; linarith only [hm_mul, h2]))
            exact ⟨hp.1.congr fun q h1 h2 => heq_t q h1 (by linarith only [h2, Nat.zero_le L_sim]),
              hp.2.1.congr fun q h1 h2 => heq_t q (by linarith only [h1, Nat.zero_le L_sim]) (by linarith only [h2, Nat.zero_le L_sim]),
              hp.2.2.congr fun q h1 h2 => heq_t q (by linarith only [h1, Nat.zero_le L_sim]) (by linarith only [h2])⟩
        · intro q hq
          dsimp only; rw [hm_s7]
          have hm_k1 : (k + 1) * (3 * L_sim) = k * (3 * L_sim) + 3 * L_sim := by ring
          rw [hm_k1] at hq
          rw [hne_block q (hq.elim (fun h1 => Or.inl (by dsimp only [baseK]; linarith only [h1, Nat.zero_le (k * (3 * L_sim))]))
            (fun h1 => Or.inr (by dsimp only [baseK]; linarith only [h1])))]
          exact hfr_prev q (hq.elim Or.inl (fun h1 => Or.inr (by linarith only [h1, Nat.zero_le (3 * L_sim)])))
      · dsimp only [argsSize, Expr.size]; linarith only [Nat.zero_le L_sim])
  refine runs_seq_triple_le (hloop.conseq (fun _ h => h) (fun o st hq => by
    cases o with | returned _ => exact False.elim hq | normal => exact hq) (fun _ _ => le_rfl)) rfl ?_
  intro st_end hInv_end
  have hr6_end := hInv_end.1.2.2.1
  have hl_end := hInv_end.2.1
  have hfr_end := hInv_end.2.2
  refine runs_ret_le (Expr.eval_reg_of_eq hr6_end)
    ⟨B_len, bArr, vIdxPtr, L_sim, pos, bIdxs, rfl, rfl, hblen, fun k hk => (hb_spec k hk).2.1, hl_end, hfr_end⟩ ?_
  dsimp only [encodeBridgesContract, encodeBridgesCost, argsSize, Expr.size]
  simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Nat.sub_zero]
  have hmul : B_len * (64 * L_sim + 95) ≤ B_len * (65 * L_sim + 100) :=
    Nat.mul_le_mul_left B_len (by omega)
  linarith only [hmul, hL1]

end MinCostFlow.WideWord
