module

public import MinCostFlow.DynSpanner.Program.DynSpannerShortcutPasses

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Cycle-Popping Loop for Pass 2 (`DynSpannerShortcutPop`)

Defines `PopLoopInv` and proves `shortcut_popLoop_triple`, verifying the inner stack-popping
`while` loop (`popPrefix G target cur₀ Q₀`) and `VStampInv` cleanup.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

public section

/-- Invariant for `shortcut_popLoop_triple` indexed by remaining `xs = popPrefix G target cur' Q'`. -/
def PopLoopInv (vCap vStampPtr stampVal gen0 nodeBase nodePtr target vEnd : ℕ)
    (G : MGraph) (cur₀ : ℕ) (Q₀ : List (ℕ × Bool)) (mem0 : ℕ → ℕ) (regs0 : ℕ → ℕ)
    (xs : List (ℕ × Bool)) (st : State) : Prop :=
  ∃ (cur' : ℕ) (Q' : List (ℕ × Bool)),
    xs = popPrefix G target cur' Q' ∧
    suffixFrom G target cur' Q' = suffixFrom G target cur₀ Q₀ ∧
    target ∈ G.walkVertices cur' Q' ∧
    cur' ∈ G.V ∧ G.IsWalk cur' vEnd Q' ∧ (G.walkVertices cur' Q').Nodup ∧
    StackListIn G nodeBase nodePtr st.mem (st.regs 18) cur' Q' ∧
    VStampInv st.mem vStampPtr vCap stampVal gen0 (G.walkVertices cur' Q') ∧
    st.regs 20 = (if xs = [] then 0 else 1) ∧
    (∀ r, (r ≤ 14 ∨ r = 16 ∨ r = 17 ∨ r = 19) → st.regs r = regs0 r) ∧
    (∀ addr, (∀ v < vCap, addr ≠ vStampPtr + v) → st.mem addr = mem0 addr)

lemma shortcut_popLoop_triple {w vCap vStampPtr stampVal gen0 nodeBase nodePtr target cur₀ vEnd : ℕ}
    {G : MGraph} {Q₀ : List (ℕ × Bool)} {p : Program}
    (hw16 : 16 ≤ 2 ^ w) (hnode : 1 ≤ nodeBase)
    (hvst_disj : ∀ v < vCap, vStampPtr + v < nodeBase)
    (hvst_w : vStampPtr + vCap < 2 ^ w) (hnode_w : nodePtr < 2 ^ w)
    (hG_val : G.IsValid) (hvG : ∀ v ∈ G.V, v < vCap)
    (hcur₀ : cur₀ ∈ G.V) (hWalk₀ : G.IsWalk cur₀ vEnd Q₀) (hNd₀ : (G.walkVertices cur₀ Q₀).Nodup)
    (hmem₀ : target ∈ G.walkVertices cur₀ Q₀) :
    ∀ (mem0 : ℕ → ℕ) (regs0 : ℕ → ℕ),
      regs0 6 = vStampPtr → regs0 12 = target →
      StackListIn G nodeBase nodePtr mem0 (regs0 18) cur₀ Q₀ →
      VStampInv mem0 vStampPtr vCap stampVal gen0 (G.walkVertices cur₀ Q₀) →
      Triple w p (fun st => st.mem = mem0 ∧ st.regs = regs0)
        (.cond (.reg 18)
          (.cond (.bin .eq (.load (.reg 18)) (.reg 12))
            (.assign 20 (.const 0)) (.assign 20 (.const 1)))
          (.assign 20 (.const 0)) ;;
         .loop (.reg 20)
           (.assign 15 (.load (.reg 18)) ;;
            .store (.bin .add (.reg 6) (.reg 15)) (.const 0) ;;
            .assign 18 (.load (.bin .add (.reg 18) (.const 3))) ;;
            .cond (.reg 18)
              (.cond (.bin .eq (.load (.reg 18)) (.reg 12))
                (.assign 20 (.const 0)) (.assign 20 (.const 1)))
              (.assign 20 (.const 0))))
        (normalPost fun st' =>
          StackListIn G nodeBase nodePtr st'.mem (st'.regs 18) target (suffixFrom G target cur₀ Q₀) ∧
          G.IsWalk target vEnd (suffixFrom G target cur₀ Q₀) ∧
          (G.walkVertices target (suffixFrom G target cur₀ Q₀)).Nodup ∧
          VStampInv st'.mem vStampPtr vCap stampVal gen0
            (G.walkVertices target (suffixFrom G target cur₀ Q₀)) ∧
          (∀ r, (r ≤ 14 ∨ r = 16 ∨ r = 17 ∨ r = 19) → st'.regs r = regs0 r) ∧
          ∀ addr, (∀ v < vCap, addr ≠ vStampPtr + v) → st'.mem addr = mem0 addr)
        (fun _ => 32 * (popPrefix G target cur₀ Q₀).length + 15) := by
  intro mem0 regs0 hr6 hr12 hSt₀ hV₀
  let Inv := PopLoopInv vCap vStampPtr stampVal gen0 nodeBase nodePtr target vEnd G cur₀ Q₀ mem0 regs0
  let flagStmt : Stmt :=
    .cond (.reg 18)
      (.cond (.bin .eq (.load (.reg 18)) (.reg 12))
        (.assign 20 (.const 0)) (.assign 20 (.const 1)))
      (.assign 20 (.const 0))
  let body : Stmt :=
    .assign 15 (.load (.reg 18)) ;;
    .store (.bin .add (.reg 6) (.reg 15)) (.const 0) ;;
    .assign 18 (.load (.bin .add (.reg 18) (.const 3))) ;;
    flagStmt
  have hloop : Triple w p (Inv (popPrefix G target cur₀ Q₀)) (.loop (.reg 20) body)
      (normalPost fun st' =>
        StackListIn G nodeBase nodePtr st'.mem (st'.regs 18) target (suffixFrom G target cur₀ Q₀) ∧
        G.IsWalk target vEnd (suffixFrom G target cur₀ Q₀) ∧
        (G.walkVertices target (suffixFrom G target cur₀ Q₀)).Nodup ∧
        VStampInv st'.mem vStampPtr vCap stampVal gen0
          (G.walkVertices target (suffixFrom G target cur₀ Q₀)) ∧
        (∀ r, (r ≤ 14 ∨ r = 16 ∨ r = 17 ∨ r = 19) → st'.regs r = regs0 r) ∧
        ∀ addr, (∀ v < vCap, addr ≠ vStampPtr + v) → st'.mem addr = mem0 addr)
      (fun _ => ((popPrefix G target cur₀ Q₀).map (fun _ => 30)).sum +
        (popPrefix G target cur₀ Q₀).length * ((Expr.reg 20).size + 1) + (Expr.reg 20).size + 1) := by
    refine Triple.loop_list (Inv := Inv) (fun _ => 30) ?_ ?_ (popPrefix G target cur₀ Q₀)
    · intro st ⟨cur', Q', hnil, hsuf, hmem, _, hW', hNd', hSt', hV', hr20, hr_eq, hm_fr⟩
      have hev : (Expr.reg 20).eval w st = some 0 := by simp [Expr.eval, hr20]
      have hct : cur' = target := by
        cases Q' with
        | nil =>
          simp only [MGraph.walkVertices, List.map_nil, List.mem_singleton] at hmem
          exact hmem.symm
        | cons x xs =>
          simp only [popPrefix] at hnil
          split_ifs at hnil with h
          · exact h
      subst hct
      have hsf_self : suffixFrom G cur' cur' Q' = Q' := by cases Q' <;> simp [suffixFrom]
      rw [← hsuf, hsf_self]
      refine ⟨hev, hSt', hW', hNd', hV', hr_eq, hm_fr⟩
    · intro x xs st0 ⟨cur', Q', hcons, hsuf, hmem, hcur', hW', hNd', hSt', hV', hr20, hr_eq, hm_fr⟩
      cases Q' with
      | nil => simp [popPrefix] at hcons
      | cons y Q_rest =>
        have hct : cur' ≠ target := by
          intro h; subst h; simp [popPrefix] at hcons
        have hcons' : x = y ∧ xs = popPrefix G target (G.dst y) Q_rest := by
          simpa [popPrefix, hct] using hcons
        rcases hcons' with ⟨rfl, hxs⟩
        rcases hW' with _ | ⟨he_y, _, hW_rest⟩
        rcases hSt' with ⟨hlo_hd, hhi_hd, hhd_c, _, _, hSt_rest⟩
        have hNd_cons : (cur' :: G.walkVertices (G.dst x) Q_rest).Nodup := by
          simpa [MGraph.walkVertices] using hNd'
        rw [List.nodup_cons] at hNd_cons
        have hcur_lt : cur' < vCap := hvG cur' hcur'
        have hdst_V : G.dst x ∈ G.V := isWalk_mem_dst_V hG_val he_y
        have hxs_ne : x :: xs ≠ [] := List.cons_ne_nil _ _
        have hr20_val : st0.regs 20 = 1 := by simp [hr20, hxs_ne]
        refine ⟨1, by simp [Expr.eval, hr20_val], one_ne_zero, fun st ω hst => ?_⟩
        dsimp only at hst; subst hst
        refine runs_start_le ?_
        have hr6_st : st.regs 6 = vStampPtr :=
          (hr_eq 6 (Or.inl (by omega))).trans hr6
        have hr12_st : st.regs 12 = target :=
          (hr_eq 12 (Or.inl (by omega))).trans hr12
        refine runs_seq_assign_le (v := cur') (Expr.eval_load_of_eq rfl hhd_c) ?_
        have hcur_w : cur' < 2 ^ w := by omega
        have hvsp_cur_lt : vStampPtr + cur' < 2 ^ w := by omega
        refine runs_seq_store_le (x := vStampPtr + cur') (v := 0)
          (Expr.eval_add (by simp [Expr.eval, hr6_st]) (by simp [Expr.eval]) hvsp_cur_lt)
          (Expr.eval_const (by omega)) ?_
        have hnext_lt : st.regs 18 + 3 < 2 ^ w := by omega
        have hnext_val : Function.update st.mem (vStampPtr + cur') 0 (st.regs 18 + 3) =
            st.mem (st.regs 18 + 3) := by
          have := hvst_disj cur' hcur_lt
          rw [Function.update_of_ne (by omega)]
        refine runs_seq_assign_le (v := st.mem (st.regs 18 + 3))
          (Expr.eval_load_of_eq (by
            simp [Expr.eval, BinOp.eval, show (3 : ℕ) < 2 ^ w by omega, hnext_lt]) hnext_val) ?_
        let st1 : State :=
          { st with
            mem := Function.update st.mem (vStampPtr + cur') 0
            regs := Function.update
              (Function.update st.regs 15 cur') 18 (st.mem (st.regs 18 + 3)) }
        have hSt1_agree : ∀ a, nodeBase ≤ a → a < nodePtr → st1.mem a = st.mem a := by
          intro a ha1 _
          have := hvst_disj cur' hcur_lt
          exact Function.update_of_ne (by omega) _ _
        have hSt1_stack : StackListIn G nodeBase nodePtr st1.mem (st1.regs 18)
            (G.dst x) Q_rest := by
          change StackListIn G nodeBase nodePtr st1.mem (st.mem (st.regs 18 + 3)) (G.dst x) Q_rest
          exact hSt_rest.of_agree hSt1_agree
        have hr12_1 : st1.regs 12 = target := by
          simp [st1, hr12_st]
        obtain ⟨o_f, st_f, c_f, hrun_f, hq_f, hc_f⟩ :=
          shortcut_setPopFlag_triple hw16 hnode st1 hSt1_stack hr12_1 st1 ω rfl
        cases o_f with
        | returned u => exact False.elim hq_f
        | normal =>
          dsimp only [normalPost] at hq_f
          subst hq_f
          refine ⟨.normal, _, c_f, hrun_f, ?_, by dsimp only [Expr.size] at hc_f ⊢; omega⟩
          have hsuf' : suffixFrom G target (G.dst x) Q_rest = suffixFrom G target cur₀ Q₀ := by
            have : suffixFrom G target cur' (x :: Q_rest) = suffixFrom G target (G.dst x) Q_rest := by
              simp [suffixFrom, hct]
            exact this.symm.trans hsuf
          have hmem' : target ∈ G.walkVertices (G.dst x) Q_rest := by
            simp only [MGraph.walkVertices, List.mem_cons] at hmem
            exact hmem.resolve_left (fun h => hct h.symm)
          refine ⟨G.dst x, Q_rest, hxs, hsuf', hmem', hdst_V, hW_rest, hNd_cons.2, hSt1_stack,
            ?_, ?_, ?_, ?_⟩
          · intro v hv
            have hv0 := hV' v hv
            change VStampInv st.mem _ _ _ _ _ at hV'
            by_cases hvc : v = cur'
            · subst hvc
              refine ⟨fun h => False.elim (hNd_cons.1 h), fun _ => ?_⟩
              dsimp only [st1]
              rw [Function.update_self]
              exact Nat.zero_le _
            · have hne : vStampPtr + v ≠ vStampPtr + cur' := by omega
              dsimp only [st1]
              rw [Function.update_of_ne hne]
              change (v ∈ G.walkVertices (G.dst x) Q_rest → _) ∧ _
              have hwk : G.walkVertices cur' (x :: Q_rest) = cur' :: G.walkVertices (G.dst x) Q_rest := rfl
              rw [hwk, List.mem_cons] at hv0
              exact ⟨fun h => hv0.1 (Or.inr h),
                fun h => hv0.2 (by rintro (rfl | hm); exact hvc rfl; exact h hm)⟩
          · simp [st1, hxs]
          · intro r hr
            dsimp only [st1]
            rw [Function.update_of_ne (by omega : r ≠ 20), Function.update_of_ne (by omega : r ≠ 18),
              Function.update_of_ne (by omega : r ≠ 15)]
            exact hr_eq r hr
          · intro addr haddr
            dsimp only [st1]
            rw [Function.update_of_ne (haddr cur' hcur_lt)]
            exact hm_fr addr haddr
  intro st ω ⟨hm, hr⟩
  subst hm; subst hr
  have hflag0 := shortcut_setPopFlag_triple (p := p) hw16 hnode st hSt₀ hr12 st ω rfl
  rcases hflag0 with ⟨o0, st0, c0, hrun0, hq0, hc0⟩
  cases o0 with
  | returned u => exact False.elim hq0
  | normal =>
    dsimp only [normalPost] at hq0
    subst hq0
    have hP0 : Inv (popPrefix G target cur₀ Q₀)
        { st with
          regs := Function.update st.regs 20 (if popPrefix G target cur₀ Q₀ = [] then 0 else 1) } :=
      ⟨cur₀, Q₀, rfl, rfl, hmem₀, hcur₀, hWalk₀, hNd₀, hSt₀, hV₀, by simp,
        fun r hr => by simp [Function.update_of_ne (by omega : r ≠ 20)], fun _ _ => rfl⟩
    obtain ⟨oL, stL, cL, hrunL, hqL, hcL⟩ := hloop _ ω hP0
    refine ⟨oL, stL, c0 + cL + 1, runs_seq_iff.mpr (Or.inr ⟨_, c0, cL, hrun0, hrunL, rfl⟩),
      hqL, ?_⟩
    have hmap : ((popPrefix G target cur₀ Q₀).map (fun _ : ℕ × Bool => (30 : ℕ))).sum =
        30 * (popPrefix G target cur₀ Q₀).length := by simp [Nat.mul_comm]
    dsimp only [Expr.size] at hc0 hcL ⊢
    rw [hmap] at hcL
    omega

end

end MinCostFlow.DynSpanner.Program
