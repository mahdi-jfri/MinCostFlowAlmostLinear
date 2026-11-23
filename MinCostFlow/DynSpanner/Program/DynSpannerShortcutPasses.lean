module

public import MinCostFlow.DynSpanner.Program.DynSpannerShortcutDefs
public import MinCostFlow.DynSpanner.Program.DynGraphOps

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Single-Edge Passes for `dsShortcutEmbStmt` (`DynSpannerShortcutPasses`)

Verifies the modular sub-passes used inside `dsShortcutEdgeStmt`:
* `shortcut_pass1_triple`: records walk vertices `V_0, …, V_k` via `dgIdxGetTail`/`dgIdxGetHead`.
* `shortcut_popLoop_triple`: executes Pass 2's cycle-popping `while` loop along `popPrefix`.
* `shortcut_pass2_triple`: executes Pass 2's backward scan (`forRange`) with telescoping
  potential cost via `rangeCost_shortcut_step`.
* `shortcut_pass3_triple`: materializes `MWalkAt mem' outWalkPtr Q_final`, clears `vStamp`,
  updates `mEmbPtr[e] := outWalkPtr`, and advances `permPtr`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

public section

lemma mWalkAt_of_entries {mem : ℕ → ℕ} {ptr : ℕ} {P : List (ℕ × Bool)}
    (hlen : mem ptr = P.length)
    (he : ∀ i (hi : i < P.length), mem (ptr + 1 + 2 * i) = (P[i]'hi).1)
    (hd : ∀ i (hi : i < P.length), mem (ptr + 1 + 2 * i + 1) = if (P[i]'hi).2 then 1 else 0) :
    MWalkAt mem ptr P := by
  intro k hk0
  have hk : k < 1 + 2 * P.length := by rwa [mWalkEncode_length] at hk0
  cases k with
  | zero => simp [mWalkEncode, hlen]
  | succ m =>
    have hm : m < 2 * P.length := by omega
    have hq : m / 2 < P.length := by omega
    rcases Nat.mod_two_eq_zero_or_one m with hm0 | hm1
    · have hptr_eq : ptr + (m + 1) = ptr + 1 + 2 * (m / 2) := by omega
      have hidx_eq : m = 2 * (m / 2) := by omega
      rw [hptr_eq, he _ hq]
      have hf := flatMap_pair_getElem_even (P := P) hq
      have hflat : (mWalkEncode P)[m + 1]'hk0 =
          (P.flatMap fun p => [p.1, if p.2 then 1 else 0])[2 * (m / 2)]'(by
            rw [flatMap_pair_length]; omega) := by
        change (P.flatMap fun p => [p.1, if p.2 then 1 else 0])[m]'(by
          rw [flatMap_pair_length]; omega) = _
        exact Option.some.inj (by
          rw [← List.getElem?_eq_getElem (by rw [flatMap_pair_length]; omega),
              ← List.getElem?_eq_getElem (by rw [flatMap_pair_length]; omega)]
          congr 2)
      exact (hflat.trans hf).symm
    · have hptr_eq : ptr + (m + 1) = ptr + 1 + 2 * (m / 2) + 1 := by omega
      have hidx_eq : m = 2 * (m / 2) + 1 := by omega
      rw [hptr_eq, hd _ hq]
      have hf := flatMap_pair_getElem_odd (P := P) hq
      have hflat : (mWalkEncode P)[m + 1]'hk0 =
          (P.flatMap fun p => [p.1, if p.2 then 1 else 0])[2 * (m / 2) + 1]'(by
            rw [flatMap_pair_length]; omega) := by
        change (P.flatMap fun p => [p.1, if p.2 then 1 else 0])[m]'(by
          rw [flatMap_pair_length]; omega) = _
        exact Option.some.inj (by
          rw [← List.getElem?_eq_getElem (by rw [flatMap_pair_length]; omega),
              ← List.getElem?_eq_getElem (by rw [flatMap_pair_length]; omega)]
          congr 2)
      exact (hflat.trans hf).symm

/-- Pass 1 loop invariant (`forRange 13 0 P.length`). -/
@[expose] def Pass1Inv (permPtr : ℕ) (G : MGraph) (u : ℕ)
    (P : List (ℕ × Bool)) (mem0 : ℕ → ℕ) (regs0 : ℕ → ℕ) (i : ℕ) (st : State) : Prop :=
  st.regs 13 = i ∧
  (∀ r, r < 12 → st.regs r = regs0 r) ∧
  (∀ j ≤ i, st.mem (permPtr + j) = vertAt G u P j) ∧
  (∀ addr, (addr < permPtr + 1 ∨ permPtr + P.length + 1 ≤ addr) → st.mem addr = mem0 addr)

lemma shortcut_pass1_triple {w vCapG eCapG gPtr permPtr wPtr : ℕ}
    {G : MGraph} {u vEnd : ℕ} {P : List (ℕ × Bool)}
    {p : Program} {bOps : ℕ} {mem0 : ℕ → ℕ} {regs0 : ℕ → ℕ}
    (hpOps : p.HasAt bOps dgOpsProcs)
    (hw16 : 16 ≤ 2 ^ w)
    (hg_lt : gPtr + dynGraphSize vCapG eCapG < 2 ^ w)
    (hwPtr_lt : wPtr + 1 + 2 * P.length < 2 ^ w)
    (hperm_lt : permPtr + P.length + 1 < 2 ^ w)
    (hreg1 : regs0 1 = gPtr) (hreg5 : regs0 5 = permPtr)
    (hreg10 : regs0 10 = wPtr) (hreg11 : regs0 11 = P.length)
    (hG_val : G.IsValid) (hu : u ∈ G.V) (hWalk : G.IsWalk u vEnd P)
    (hG : DynGraphAt mem0 gPtr vCapG eCapG G)
    (hMWalk : MWalkAt mem0 wPtr P)
    (hm0 : mem0 permPtr = u)
    (hG_disj : ∀ a, gPtr ≤ a → a < gPtr + dynGraphSize vCapG eCapG →
      a < permPtr + 1 ∨ permPtr + P.length + 1 ≤ a)
    (hW_disj : ∀ a, wPtr ≤ a → a < wPtr + 1 + 2 * P.length →
      a < permPtr + 1 ∨ permPtr + P.length + 1 ≤ a) :
    Triple w p
      (fun st => st.mem = mem0 ∧ (∀ r, r < 12 → st.regs r = regs0 r))
      (forRange 13 (.const 0) (.reg 11)
        (.assign 14 (.load (.bin .add (.reg 10)
          (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 13))))) ;;
         .assign 15 (.load (.bin .add (.reg 10)
          (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 13))))) ;;
         .cond (.reg 15)
           (.call 12 (bOps + dgIdxGetHead) [.reg 1, .reg 14])
           (.call 12 (bOps + dgIdxGetTail) [.reg 1, .reg 14]) ;;
         .store (.bin .add (.reg 5) (.bin .add (.reg 13) (.const 1))) (.reg 12)))
      (normalPost (Pass1Inv permPtr G u P mem0 regs0 P.length))
      (fun _ => 90 * P.length + 10) := by
  have hw1 : 1 < 2 ^ w := by omega
  let Inv := Pass1Inv permPtr G u P mem0 regs0
  let P0 : State → Prop := fun st => st.mem = mem0 ∧ (∀ r, r < 12 → st.regs r = regs0 r)
  have hloop : Triple w p P0
      (forRange 13 (.const 0) (.reg 11)
        (.assign 14 (.load (.bin .add (.reg 10)
          (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 13))))) ;;
         .assign 15 (.load (.bin .add (.reg 10)
          (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 13))))) ;;
         .cond (.reg 15)
           (.call 12 (bOps + dgIdxGetHead) [.reg 1, .reg 14])
           (.call 12 (bOps + dgIdxGetTail) [.reg 1, .reg 14]) ;;
         .store (.bin .add (.reg 5) (.bin .add (.reg 13) (.const 1))) (.reg 12)))
      (normalPost (Inv P.length))
      (fun _ => (P.length - 0) * (80 + (.reg 11 : Expr).size + 8) +
        ((.const 0 : Expr).size + (.reg 11 : Expr).size + 5)) :=
    Triple.forRange_const (P := P0) (r := 13) (lo := .const 0) (hi := .reg 11)
      (Inv := Inv) 80 0 P.length (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st ⟨hm, hr⟩ => by
      refine ⟨Expr.eval_const (by omega), rfl, ?_, ?_, fun _ _ => hm ▸ rfl⟩
      · intro r hr12; simp [Function.update_of_ne (by omega : r ≠ 13), hr r hr12]
      · intro j hj; have hj0 : j = 0 := by omega
        subst hj0; simp [hm, hm0, vertAt])
    (fun _ _ _ _ hI => hI.1)
    (fun i _ _ _ ⟨_, hr, _, _⟩ => by simp [Expr.eval, hr 11 (by omega), hreg11])
    (fun i _ hi => by
      intro st ω ⟨hr13, hr, harr, hfr⟩
      have he_mem : (P[i]'hi).1 ∈ G.E :=
        (isWalk_mem_V_tail_head hG_val hu hWalk _ (List.getElem_mem hi)).1
      have hagree_W : ∀ a, wPtr ≤ a → a < wPtr + 1 + 2 * P.length → st.mem a = mem0 a :=
        fun a ha1 ha2 => hfr a (hW_disj a ha1 ha2)
      have hG_cur : DynGraphAt st.mem gPtr vCapG eCapG G :=
        dynGraphAt_of_agree hG fun a ha1 ha2 => hfr a (hG_disj a ha1 ha2)
      have h14_val : st.mem (wPtr + (1 + 2 * i)) = (P[i]'hi).1 := by
        rw [hagree_W _ (by omega) (by omega), show wPtr + (1 + 2 * i) = wPtr + 1 + 2 * i by omega]
        exact MWalkAt_step_edge hMWalk hi
      have h15_val : st.mem (wPtr + (2 + 2 * i)) = if (P[i]'hi).2 then 1 else 0 := by
        rw [hagree_W _ (by omega) (by omega), show wPtr + (2 + 2 * i) = wPtr + 1 + 2 * i + 1 by omega]
        exact MWalkAt_step_dir hMWalk hi
      have hlt_g : gPtr < 2 ^ w := by dsimp [dynGraphSize] at hg_lt; omega
      have hlt_e : (P[i]'hi).1 < 2 ^ w := by
        have hlt : (P[i]'hi).1 < eCapG := hG.2.2.1 _ he_mem
        dsimp [dynGraphSize] at hg_lt; omega
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := (P[i]'hi).1)
        (Expr.eval_load_of_eq (by
          simp [Expr.eval, BinOp.eval, hr 10 (by omega), hreg10, hr13,
            show 1 < 2 ^ w by omega, show 2 < 2 ^ w by omega,
            show 2 * i < 2 ^ w by omega, show 1 + 2 * i < 2 ^ w by omega,
            show wPtr + (1 + 2 * i) < 2 ^ w by omega]) h14_val) ?_
      refine runs_seq_assign_le (v := if (P[i]'hi).2 then 1 else 0)
        (Expr.eval_load_of_eq (by
          simp [Expr.eval, BinOp.eval, hr 10 (by omega), hreg10, hr13,
            show 2 < 2 ^ w by omega, show 2 * i < 2 ^ w by omega,
            show 2 + 2 * i < 2 ^ w by omega, show wPtr + (2 + 2 * i) < 2 ^ w by omega]) h15_val) ?_
      have hcond_step : ∃ stC cC,
          Runs w p ω
            (.cond (.reg 15) (.call 12 (bOps + dgIdxGetHead) [.reg 1, .reg 14])
              (.call 12 (bOps + dgIdxGetTail) [.reg 1, .reg 14]))
            { st with
              regs := Function.update (Function.update st.regs 14 (P[i]'hi).1)
                15 (if (P[i]'hi).2 then 1 else 0) }
            .normal stC cC ∧
          stC.mem = st.mem ∧ stC.regs 12 = G.dst (P[i]'hi) ∧
          stC.regs 5 = permPtr ∧ stC.regs 13 = i ∧
          (∀ r, r < 12 → stC.regs r = regs0 r) ∧ cC ≤ 50 := by
        let stB : State :=
          { st with
            regs := Function.update (Function.update st.regs 14 (P[i]'hi).1)
              15 (if (P[i]'hi).2 then 1 else 0) }
        have hr1_B : stB.regs 1 = gPtr := by simp [stB, hr 1 (by omega), hreg1]
        have hr14_B : stB.regs 14 = (P[i]'hi).1 := by simp [stB]
        have hr15_B : stB.regs 15 = if (P[i]'hi).2 then 1 else 0 := by simp [stB]
        have heval_args : evalArgs w stB [.reg 1, .reg 14] = some [gPtr, (P[i]'hi).1] := by
          simp [evalArgs, Expr.eval, hr1_B, hr14_B]
        have hargs_lt : ∀ a ∈ [gPtr, (P[i]'hi).1], a < 2 ^ w := by
          intro a ha; rcases List.mem_cons.mp ha with rfl | ha
          · exact hlt_g
          · rcases List.mem_singleton.mp ha with rfl; exact hlt_e
        cases hdir : (P[i]'hi).2
        · obtain ⟨body, hp_get, o, st_sub, c_sub, hrun_sub, hpost_sub, hcost_sub⟩ :=
            dgGetTail_meetsContract hpOps (w := w) (vCap := vCapG) (eCap := eCapG) (G := G)
              [gPtr, (P[i]'hi).1] stB.mem stB.pos ω hargs_lt
              ⟨gPtr, (P[i]'hi).1, rfl, hw16, hg_lt, he_mem, hG_cur⟩
          rcases hpost_sub with ⟨_, _, heq_args, hm_sub, ho_val⟩
          simp only [List.cons.injEq, and_true] at heq_args
          have hdst : G.dst (P[i]'hi) = G.tail (P[i]'hi).1 := by simp [MGraph.dst, hdir]
          have hcall : Runs w p ω (.call 12 (bOps + dgIdxGetTail) [.reg 1, .reg 14])
              stB .normal { st_sub with regs := Function.update stB.regs 12 o.value }
              (argsSize [.reg 1, .reg 14] + c_sub + 1) :=
            runs_call_iff.mpr ⟨_, _, o, st_sub, c_sub, heval_args, hp_get, hrun_sub, rfl, rfl, rfl⟩
          refine ⟨{ st_sub with regs := Function.update stB.regs 12 o.value },
            1 + (argsSize [.reg 1, .reg 14] + c_sub + 1) + 1,
            runs_cond_iff.mpr ⟨0, argsSize [.reg 1, .reg 14] + c_sub + 1,
              by simp [Expr.eval],
              by simpa [stB, hdir] using hcall, by simp [Expr.size]⟩,
            hm_sub, by simp [ho_val, ← heq_args.2, hdst], by simp [stB, hr 5 (by omega), hreg5],
            by simp [stB, hr13],
            fun r hr12 => by
              dsimp [stB]
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega)]
              exact hr r hr12,
            by dsimp [argsSize, dgGetTailContract] at *; omega⟩
        · obtain ⟨body, hp_get, o, st_sub, c_sub, hrun_sub, hpost_sub, hcost_sub⟩ :=
            dgGetHead_meetsContract hpOps (w := w) (vCap := vCapG) (eCap := eCapG) (G := G)
              [gPtr, (P[i]'hi).1] stB.mem stB.pos ω hargs_lt
              ⟨gPtr, (P[i]'hi).1, rfl, hw16, hg_lt, he_mem, hG_cur⟩
          rcases hpost_sub with ⟨_, _, heq_args, hm_sub, ho_val⟩
          simp only [List.cons.injEq, and_true] at heq_args
          have hdst : G.dst (P[i]'hi) = G.head (P[i]'hi).1 := by simp [MGraph.dst, hdir]
          have hcall : Runs w p ω (.call 12 (bOps + dgIdxGetHead) [.reg 1, .reg 14])
              stB .normal { st_sub with regs := Function.update stB.regs 12 o.value }
              (argsSize [.reg 1, .reg 14] + c_sub + 1) :=
            runs_call_iff.mpr ⟨_, _, o, st_sub, c_sub, heval_args, hp_get, hrun_sub, rfl, rfl, rfl⟩
          refine ⟨{ st_sub with regs := Function.update stB.regs 12 o.value },
            1 + (argsSize [.reg 1, .reg 14] + c_sub + 1) + 1,
            runs_cond_iff.mpr ⟨1, argsSize [.reg 1, .reg 14] + c_sub + 1,
              by simp [Expr.eval],
              by simpa [stB, hdir] using hcall, by simp [Expr.size]⟩,
            hm_sub, by simp [ho_val, ← heq_args.2, hdst], by simp [stB, hr 5 (by omega), hreg5],
            by simp [stB, hr13],
            fun r hr12 => by
              dsimp [stB]
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega)]
              exact hr r hr12,
            by dsimp [argsSize, dgGetHeadContract] at *; omega⟩
      rcases hcond_step with ⟨stC, cC, hrunC, hmC, hr12C, hr5C, hr13C, hrC, hcC⟩
      have hst_tail := runs_store_le (w := w) (p := p) (ω := ω)
        (a := .bin .add (.reg 5) (.bin .add (.reg 13) (.const 1))) (e := .reg 12)
        (st := stC) (x := permPtr + (i + 1)) (v := G.dst (P[i]'hi))
        (k := 10 + 10 + cC + 1) (T := 80)
        (Q := normalPost fun st₁ =>
          Inv (i + 1) { st₁ with regs := Function.update st₁.regs 13 (i + 1) } ∧ st₁.regs 13 = i)
        (by simp [Expr.eval, BinOp.eval, hr5C, hr13C, show 1 < 2 ^ w by omega,
          show i + 1 < 2 ^ w by omega, show permPtr + (i + 1) < 2 ^ w by omega])
        (by simp [Expr.eval, hr12C])
        (by
          refine ⟨⟨rfl, fun r hr12 => ?_, fun j hj => ?_, fun addr haddr => ?_⟩, hr13C⟩
          · simp [Function.update_of_ne (by omega : r ≠ 13), hrC r hr12]
          · dsimp only
            by_cases hji : j = i + 1
            · subst hji
              rw [Function.update_self, vertAt_succ G u hi]
            · rw [Function.update_of_ne (by omega : permPtr + j ≠ permPtr + (i + 1)), hmC]
              exact harr j (by omega)
          · dsimp only
            rw [Function.update_of_ne (by omega : addr ≠ permPtr + (i + 1)), hmC]
            exact hfr addr haddr)
        (by dsimp only [Expr.size]; omega)
      rcases hst_tail with ⟨o_f, st_f, c_f, hrun_f, hq_f, hc_f⟩
      exact ⟨o_f, st_f, cC + c_f + 1,
        runs_seq_iff.mpr (Or.inr ⟨stC, cC, c_f, hrunC, hrun_f, rfl⟩), hq_f, by
          dsimp only [Expr.size] at *; omega⟩)
  refine hloop.conseq (fun st h => h) (fun o s' hq => hq) (fun _ _ => ?_)
  dsimp only [Expr.size]
  omega

/-- Sets `r20` to `0` if `popPrefix G target cur' Q' = []`, else `1`, reading only `r12, r18`. -/
lemma shortcut_setPopFlag_triple {w nodeBase nodePtr target : ℕ}
    {G : MGraph} {cur' : ℕ} {Q' : List (ℕ × Bool)} {p : Program}
    (hw16 : 16 ≤ 2 ^ w) (hnode : 1 ≤ nodeBase)
    (st : State) (hStack : StackListIn G nodeBase nodePtr st.mem (st.regs 18) cur' Q')
    (hr12 : st.regs 12 = target) :
      Triple w p (fun s => s = st)
        (.cond (.reg 18)
          (.cond (.bin .eq (.load (.reg 18)) (.reg 12))
            (.assign 20 (.const 0)) (.assign 20 (.const 1)))
          (.assign 20 (.const 0)))
        (normalPost fun s' => s' =
          { st with
            regs := Function.update st.regs 20
              (if popPrefix G target cur' Q' = [] then 0 else 1) })
        (fun _ => 12) := by
  intro s₀ ω hs₀; subst hs₀
  have hs := hStack
  cases Q' with
  | nil =>
    have hh0 : s₀.regs 18 = 0 := hs
    refine ⟨.normal, { s₀ with regs := Function.update s₀.regs 20 0 }, 4,
      runs_cond_iff.mpr ⟨0, 2, by simp [Expr.eval, hh0],
        by simpa using runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, by simp⟩,
        by simp [Expr.size]⟩,
      by simp [popPrefix], by dsimp only; omega⟩
  | cons x xs =>
    rcases hs with ⟨hlo, _, hmem_c, _⟩
    have hh_ne : s₀.regs 18 ≠ 0 := by omega
    by_cases hct : cur' = target
    · have hc_eq : (Expr.bin .eq (.load (.reg 18)) (.reg 12)).eval w s₀ = some 1 :=
        Expr.eval_eq_true (Expr.eval_load_of_eq rfl hmem_c) (Expr.eval_reg_of_eq hr12) hct
          (by omega)
      have hr2 : Runs w p ω
          (.cond (.bin .eq (.load (.reg 18)) (.reg 12))
            (.assign 20 (.const 0)) (.assign 20 (.const 1)))
          s₀ .normal { s₀ with regs := Function.update s₀.regs 20 0 } 7 :=
        runs_cond_iff.mpr ⟨1, 2, hc_eq,
          by simpa using runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, by simp⟩,
          by simp [Expr.size]⟩
      exact ⟨.normal, { s₀ with regs := Function.update s₀.regs 20 0 }, 9,
        runs_cond_iff.mpr ⟨s₀.regs 18, 7, rfl, by simpa [hh_ne] using hr2, by simp [Expr.size]⟩,
        by simp [popPrefix, hct], by dsimp only; omega⟩
    · have hc_eq : (Expr.bin .eq (.load (.reg 18)) (.reg 12)).eval w s₀ = some 0 :=
        Expr.eval_eq_false (Expr.eval_load_of_eq rfl hmem_c) (Expr.eval_reg_of_eq hr12) hct
          (by omega)
      have hr2 : Runs w p ω
          (.cond (.bin .eq (.load (.reg 18)) (.reg 12))
            (.assign 20 (.const 0)) (.assign 20 (.const 1)))
          s₀ .normal { s₀ with regs := Function.update s₀.regs 20 1 } 7 :=
        runs_cond_iff.mpr ⟨0, 2, hc_eq,
          by simpa using runs_assign_iff.mpr ⟨1, Expr.eval_const (by omega), rfl, rfl, by simp⟩,
          by simp [Expr.size]⟩
      exact ⟨.normal, { s₀ with regs := Function.update s₀.regs 20 1 }, 9,
        runs_cond_iff.mpr ⟨s₀.regs 18, 7, rfl, by simpa [hh_ne] using hr2, by simp [Expr.size]⟩,
        by simp [popPrefix, hct], by dsimp only; omega⟩

end

end MinCostFlow.DynSpanner.Program
