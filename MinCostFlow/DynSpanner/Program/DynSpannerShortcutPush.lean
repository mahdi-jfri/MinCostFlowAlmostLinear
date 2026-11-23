module

public import MinCostFlow.DynSpanner.Program.DynSpannerShortcutPop

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Stack-Node Push Helper for Pass 2 (`DynSpannerShortcutPush`)

Verifies `shortcut_pushNode_triple`, pushing `[target, P[i].1, dir, head]` onto the 4-word
linked stack and setting `vStamp[target] := stampVal`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

public section

/-- Push-node helper for Pass 2 (`¬ target ∈ G.walkVertices cur Q`). -/
lemma shortcut_pushNode_triple {w vCap vStampPtr stampVal gen0 wPtr nodeBase nodePtr target cur : ℕ}
    {G : MGraph} {P Q : List (ℕ × Bool)} {i : ℕ} (hi : i < P.length) {p : Program}
    (hw16 : 16 ≤ 2 ^ w)
    (hvst_disj : ∀ v < vCap, vStampPtr + v < nodeBase)
    (hnode_lo : nodeBase ≤ nodePtr)
    (hnode4_w : nodePtr + 4 < 2 ^ w)
    (hwPtr_w : wPtr + 1 + 2 * P.length < 2 ^ w)
    (hvsp_t_w : vStampPtr + target < 2 ^ w)
    (htarg_lt : target < vCap)
    (hdst : G.dst (P[i]'hi) = cur) :
    ∀ (st : State),
      st.regs 6 = vStampPtr → st.regs 7 = stampVal → st.regs 10 = wPtr →
      st.regs 12 = target → st.regs 17 = nodePtr → st.regs 21 = i →
      (P[i]'hi).1 < 2 ^ w →
      MWalkAt st.mem wPtr P →
      StackListIn G nodeBase nodePtr st.mem (st.regs 18) cur Q →
      VStampInv st.mem vStampPtr vCap stampVal gen0 (G.walkVertices cur Q) →
      Triple w p (fun s => s = st)
        (.assign 14 (.load (.bin .add (.reg 10)
            (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 21))))) ;;
         .assign 15 (.load (.bin .add (.reg 10)
            (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 21))))) ;;
         .store (.reg 17) (.reg 12) ;;
         .store (.bin .add (.reg 17) (.const 1)) (.reg 14) ;;
         .store (.bin .add (.reg 17) (.const 2)) (.reg 15) ;;
         .store (.bin .add (.reg 17) (.const 3)) (.reg 18) ;;
         .assign 18 (.reg 17) ;;
         .assign 17 (.bin .add (.reg 17) (.const 4)) ;;
         .store (.bin .add (.reg 6) (.reg 12)) (.reg 7))
        (normalPost fun st' =>
          st'.regs 13 = st.regs 13 ∧
          st'.regs 17 = nodePtr + 4 ∧
          st'.regs 18 = nodePtr ∧
          (∀ r, (r ≤ 11 ∨ r = 16 ∨ r = 19) → st'.regs r = st.regs r) ∧
          StackListIn G nodeBase (nodePtr + 4) st'.mem nodePtr target ((P[i]'hi) :: Q) ∧
          VStampInv st'.mem vStampPtr vCap stampVal gen0
            (G.walkVertices target ((P[i]'hi) :: Q)) ∧
          ∀ addr, (∀ v < vCap, addr ≠ vStampPtr + v) → (addr < nodeBase ∨ nodePtr + 4 ≤ addr) →
            st'.mem addr = st.mem addr)
        (fun _ => 55) := by
  intro st hr6 hr7 hr10 hr12 hr17 hr21 _ hMW hSt hV s₀ ω hs₀
  subst hs₀
  have h14_val : s₀.mem (wPtr + (1 + 2 * i)) = (P[i]'hi).1 := by
    rw [show wPtr + (1 + 2 * i) = wPtr + 1 + 2 * i by omega]
    exact MWalkAt_step_edge hMW hi
  have h15_val : s₀.mem (wPtr + (2 + 2 * i)) = if (P[i]'hi).2 then 1 else 0 := by
    rw [show wPtr + (2 + 2 * i) = wPtr + 1 + 2 * i + 1 by omega]
    exact MWalkAt_step_dir hMW hi
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := (P[i]'hi).1)
    (Expr.eval_load_of_eq (by
      simp [Expr.eval, BinOp.eval, hr10, hr21, show 1 < 2 ^ w by omega,
        show 2 < 2 ^ w by omega, show 2 * i < 2 ^ w by omega, show 1 + 2 * i < 2 ^ w by omega,
        show wPtr + (1 + 2 * i) < 2 ^ w by omega]) h14_val) ?_
  refine runs_seq_assign_le (v := if (P[i]'hi).2 then 1 else 0)
    (Expr.eval_load_of_eq (by
      simp [Expr.eval, BinOp.eval, hr10, hr21, show 2 < 2 ^ w by omega,
        show 2 * i < 2 ^ w by omega, show 2 + 2 * i < 2 ^ w by omega,
        show wPtr + (2 + 2 * i) < 2 ^ w by omega]) h15_val) ?_
  refine runs_seq_store_le (x := nodePtr) (v := target)
    (by simp [Expr.eval, hr17])
    (by simp [Expr.eval, hr12]) ?_
  refine runs_seq_store_le (x := nodePtr + 1) (v := (P[i]'hi).1)
    (by simp [Expr.eval, BinOp.eval, hr17, show 1 < 2 ^ w by omega,
      show nodePtr + 1 < 2 ^ w by omega])
    (by simp [Expr.eval]) ?_
  refine runs_seq_store_le (x := nodePtr + 2) (v := if (P[i]'hi).2 then 1 else 0)
    (by simp [Expr.eval, BinOp.eval, hr17, show 2 < 2 ^ w by omega,
      show nodePtr + 2 < 2 ^ w by omega])
    (by simp [Expr.eval]) ?_
  refine runs_seq_store_le (x := nodePtr + 3) (v := s₀.regs 18)
    (by simp [Expr.eval, BinOp.eval, hr17, show 3 < 2 ^ w by omega,
      show nodePtr + 3 < 2 ^ w by omega])
    (by simp [Expr.eval]) ?_
  refine runs_seq_assign_le (v := nodePtr)
    (by simp [Expr.eval, hr17]) ?_
  refine runs_seq_assign_le (v := nodePtr + 4)
    (by simp [Expr.eval, BinOp.eval, hr17, show 4 < 2 ^ w by omega, hnode4_w]) ?_
  refine runs_store_le (x := vStampPtr + target) (v := stampVal)
    (by simp [Expr.eval, BinOp.eval, hr6, hr12, hvsp_t_w])
    (by simp [Expr.eval, hr7]) ?_ ?_
  · have hm_eq : ∀ (m : ℕ → ℕ), m = Function.update (Function.update (Function.update
        (Function.update (Function.update s₀.mem nodePtr target) (nodePtr + 1) (P[i]'hi).1)
        (nodePtr + 2) (if (P[i]'hi).2 then 1 else 0)) (nodePtr + 3) (s₀.regs 18))
        (vStampPtr + target) stampVal →
        m nodePtr = target ∧ m (nodePtr + 1) = (P[i]'hi).1 ∧
        m (nodePtr + 2) = (if (P[i]'hi).2 then 1 else 0) ∧
        StackListIn G nodeBase (nodePtr + 4) m (m (nodePtr + 3)) (G.dst (P[i]'hi)) Q := by
      intro m hm; subst hm
      have hv_disj := hvst_disj target htarg_lt
      have hv_lt : vStampPtr + target < nodePtr := lt_of_lt_of_le hv_disj hnode_lo
      refine ⟨by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self],
        by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_self],
        by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_self], ?_⟩
      rw [Function.update_of_ne (by omega), Function.update_self, hdst]
      refine (hSt.of_agree fun a ha1 ha2 => ?_).mono_hi (by omega)
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
    obtain ⟨hm0, hm1, hm2, hmS⟩ := hm_eq _ rfl
    dsimp only
    refine ⟨by simp,
      by simp,
      by simp,
      fun r hrr => by
        dsimp only
        rcases hrr with h11 | rfl | rfl <;>
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)],
      ⟨hnode_lo, le_rfl, hm0, hm1, hm2, hmS⟩, ?_, ?_⟩
    · intro v hv
      have hV0 := hV v hv
      have hlt_np : vStampPtr + v < nodePtr := lt_of_lt_of_le (hvst_disj v hv) hnode_lo
      by_cases hvt : v = target
      · subst hvt
        refine ⟨fun _ => Function.update_self _ _ _,
          fun hnot => False.elim (hnot (by simp [MGraph.walkVertices]))⟩
      · have hv_ne : vStampPtr + v ≠ vStampPtr + target := by omega
        dsimp only
        rw [Function.update_of_ne hv_ne, Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega)]
        change (v ∈ target :: G.walkVertices (G.dst (P[i]'hi)) Q → _) ∧
          (v ∉ target :: G.walkVertices (G.dst (P[i]'hi)) Q → _)
        rw [hdst, List.mem_cons]
        exact ⟨fun h => hV0.1 (h.resolve_left hvt), fun h => hV0.2 fun hm => h (Or.inr hm)⟩
    · intro addr ha_vs ha_rng
      dsimp only
      rw [Function.update_of_ne (ha_vs target htarg_lt),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · dsimp only [Expr.size]; omega

end

end MinCostFlow.DynSpanner.Program
