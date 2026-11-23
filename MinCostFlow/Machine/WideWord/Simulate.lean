module

public import MinCostFlow.Machine.WideWord.SimulateStmt

/-!
# Entry simulation and `simulate_runsTo`

This file proves the top-level deterministic simulation theorems for `compile`:
* `simEntry_runs`: `simEntry` (at procedure `base` of `compile Q base`) simulates any terminating
  run `RunsTo w' Q x (fun _ => false) out cost`.
* `simulate_runsTo`: main theorem shaped like `WordRAM.runner_spec`: calling `base` with
  `[.const ctrl, .const x.length, .const retDst]` returns `0` with `out.length` stored in `L`
  limbs at `retDst`, an updated trie representing a memory extending `out`, preserved host memory
  below `hp₀` outside `[ctrl, ctrl + 2) ∪ [retDst, retDst + L) ∪ InTrie`, bump allocation at most
  `simScale Q * L * 2 ^ h * (cost + x.length + 1)`, and host cost at most
  `simScale Q * L * w' * (cost + x.length + 1)`.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM

/-- Execute `simEntry` (at `base`) from `[ctrl, x.length, retDst]` given a guest `RunsTo` witness
on `ω₀ = fun _ => false`. -/
theorem simEntry_runs {w w' L h base : ℕ} {p Q : Program} {ω : ℕ → Bool}
    {mem : ℕ → ℕ} {x out : List ℕ} {cost ctrl hp₀ retDst pos₀ : ℕ}
    (hComp : p.HasAt base (compile Q base))
    (hL1 : 1 ≤ L) (hh : 1 ≤ h) (hw2 : 2 * h + 2 ≤ w) (hw'1 : 1 ≤ w') (hw'_lh : w' ≤ L * h)
    (hctrl_hp : ctrl + 5 ≤ hp₀) (hret_hp : retDst + L ≤ hp₀)
    (hret_ctrl : retDst + L ≤ ctrl ∨ ctrl + 5 ≤ retDst)
    (hm1 : mem (ctrl + 1) = hp₀) (hm2 : mem (ctrl + 2) = L)
    (hm3 : mem (ctrl + 3) = h) (hm4 : mem (ctrl + 4) = 2 ^ h)
    (hx_lt : ∀ v ∈ x, v < 2 ^ w')
    (htrie : TrieRep mem L h hp₀ (mem ctrl) (initMem x))
    (hin_disj : ∀ q, InTrie mem L h L (mem ctrl) q →
      (q < ctrl ∨ ctrl + 5 ≤ q) ∧ (q < retDst ∨ retDst + L ≤ q))
    (hbound : hp₀ + simScale Q * L * 2 ^ h * (cost + x.length + 1) < 2 ^ w)
    (hrun : RunsTo w' Q x (fun _ => false) out cost) :
    ∃ st' c hp' gmem',
      Runs w p ω (simEntry Q (base + 1) (base + 21))
        (startState [ctrl, x.length, retDst] mem pos₀) (.returned 0) st' c ∧
      st'.mem (ctrl + 1) = hp' ∧
      hp₀ ≤ hp' ∧
      hp' ≤ hp₀ + simScale Q * L * 2 ^ h * (cost + x.length + 1) ∧
      TrieRep st'.mem L h hp' (st'.mem ctrl) gmem' ∧
      LimbsAt st'.mem retDst L h out.length ∧
      (∀ i (hi : i < out.length), gmem' i = out[i]) ∧
      (∀ q, InTrie st'.mem L h L (st'.mem ctrl) q →
        InTrie mem L h L (mem ctrl) q ∨ (hp₀ ≤ q ∧ q < hp')) ∧
      (∀ q, q < hp₀ → q ≠ ctrl → q ≠ ctrl + 1 → ¬ InTrie mem L h L (mem ctrl) q →
        (q < retDst ∨ retDst + L ≤ q) → st'.mem q = mem q) ∧
      c ≤ simScale Q * L * w' * (cost + x.length + 1) - 10 := by
  rcases hrun with ⟨fuel, hrun_eq⟩
  dsimp only [WordRAM.run] at hrun_eq
  cases hex_top : exec w' Q (fun _ => false) fuel (.call 0 0 [.const x.length])
      { mem := initMem x, regs := fun _ => 0, pos := 0 } with
  | none => simp [hex_top] at hrun_eq
  | some res =>
    rcases res with ⟨o_top, st_top, c_top⟩
    simp only [hex_top, Option.some.injEq, Prod.mk.injEq] at hrun_eq
    rcases hrun_eq with ⟨hout_eq, hcost_eq⟩
    subst cost
    cases fuel with
    | zero => simp [exec] at hex_top
    | succ fuel' =>
      simp only [exec] at hex_top
      cases hargs0 : evalArgs w' { mem := initMem x, regs := fun _ => 0, pos := 0 } [.const x.length] with
      | none => simp [hargs0] at hex_top
      | some vs0 =>
        have hxlen_eq : vs0 = [x.length] ∧ x.length < 2 ^ w' := by
          simp only [evalArgs, Expr.eval] at hargs0
          split_ifs at hargs0 with hlt
          · exact ⟨(Option.some.inj hargs0).symm, hlt⟩
        rcases hxlen_eq with ⟨rfl, hxlen_w'⟩
        cases hproc0 : Q.procs[0]? with
        | none => simp [hargs0, hproc0] at hex_top
        | some body0 =>
          simp only [hargs0, hproc0] at hex_top
          change (match exec w' Q (fun _ => false) fuel' body0 (startState [x.length] (initMem x) 0) with
            | none => none
            | some (o, st', c) =>
              some (.normal, { st' with regs := Function.update (fun _ => 0) 0 o.value }, 1 + c + 1)) =
            some (o_top, st_top, c_top) at hex_top
          cases hbody0 : exec w' Q (fun _ => false) fuel' body0 (startState [x.length] (initMem x) 0) with
          | none => simp [hbody0] at hex_top
          | some res0 =>
            rcases res0 with ⟨o₀, gst₀, c₀⟩
            simp only [hbody0, Option.some.injEq, Prod.mk.injEq] at hex_top
            rcases hex_top with ⟨_, rfl, hc_eq⟩
            have hc0_pos : 1 ≤ c₀ := exec_cost_pos hbody0
            have hc0_le : c₀ + 2 = c_top := by omega
            set hp₁ := hp₀ + frameSlots Q * L
            have hhp1_heap : hp₁ + simScale Q * L * 2 ^ h * c₀ < 2 ^ w := by
              have hdist : simScale Q * L * 2 ^ h * (c_top + x.length + 1) =
                  simScale Q * L * 2 ^ h * c₀ + simScale Q * L * 2 ^ h * 1 +
                  simScale Q * L * 2 ^ h * (x.length + 2) := by rw [← hc0_le]; ring
              have h1 := scale_Lh_ge_one Q L h 1 hL1 (by omega)
              have hle : frameSlots Q * L ≤ simScale Q * L * 2 ^ h * 1 := by
                have h2h : 1 ≤ 2 ^ h := Nat.one_le_pow h 2 (by norm_num)
                have hsl := frameSlots_lt_simScale Q
                calc frameSlots Q * L ≤ simScale Q * L := Nat.mul_le_mul_right L (le_of_lt hsl)
                  _ = simScale Q * L * 1 * 1 := by ring
                  _ ≤ simScale Q * L * 2 ^ h * 1 :=
                    Nat.mul_le_mul_right 1 (Nat.mul_le_mul_left _ h2h)
              omega
            have hb := frame_word_bounds hL1 hh hw2 hc0_pos hctrl_hp hret_hp (le_refl hp₁) hhp1_heap
            have hArith := arithModule_hasAt_of_compile hComp
            set st₀ : State := startState [ctrl, x.length, retDst] mem pos₀
            have hr0_0 : st₀.regs 0 = ctrl := rfl
            have hr1_0 : st₀.regs 1 = x.length := rfl
            have hr2_0 : st₀.regs 2 = retDst := rfl
            set st₁ : State := { st₀ with regs := Function.update st₀.regs 3 (ctrl + 1) }
            set st₂ : State := { st₁ with regs := Function.update st₁.regs 4 L }
            set st₃ : State := { st₂ with regs := Function.update st₂.regs 5 (2 ^ h) }
            set st₄ : State := { st₃ with regs := Function.update st₃.regs 6 hp₀ }
            have ha3 : Runs w p ω (.assign 3 (.bin .add (.reg 0) (.const 1))) st₀ .normal st₁ 4 :=
              runs_assign_iff.mpr ⟨ctrl + 1,
                Expr.eval_add (by simp [Expr.eval, hr0_0])
                  (by simp [Expr.eval, hb.hw1]) (by omega), rfl, rfl, rfl⟩
            have hr0_1 : st₁.regs 0 = ctrl := by simp [st₁, hr0_0]
            have hr3_1 : st₁.regs 3 = ctrl + 1 := by simp [st₁]
            have ha4 : Runs w p ω (.assign 4 (.load (.bin .add (.reg 0) (.const 2)))) st₁ .normal st₂ 5 :=
              runs_assign_iff.mpr ⟨L, Expr.eval_load_of_eq
                (Expr.eval_add (by eval_expr) (by simp [Expr.eval]; have := hb.h16; omega) (by omega)) hm2,
                rfl, rfl, rfl⟩
            have hr0_2 : st₂.regs 0 = ctrl := by simp [st₂, hr0_1]
            have hr3_2 : st₂.regs 3 = ctrl + 1 := by simp [st₂, hr3_1]
            have hr4_2 : st₂.regs 4 = L := by simp [st₂]
            have ha5 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 0) (.const 4)))) st₂ .normal st₃ 5 :=
              runs_assign_iff.mpr ⟨2 ^ h, Expr.eval_load_of_eq
                (Expr.eval_add (by eval_expr) (by simp [Expr.eval]; have := hb.h16; omega) (by omega)) hm4,
                rfl, rfl, rfl⟩
            have hr0_3 : st₃.regs 0 = ctrl := by simp [st₃, hr0_2]
            have hr3_3 : st₃.regs 3 = ctrl + 1 := by simp [st₃, hr3_2]
            have hr4_3 : st₃.regs 4 = L := by simp [st₃, hr4_2]
            have hr5_3 : st₃.regs 5 = 2 ^ h := by simp [st₃]
            have ha6 : Runs w p ω (.assign 6 (.load (.reg 3))) st₃ .normal st₄ 3 :=
              runs_assign_iff.mpr ⟨hp₀, Expr.eval_load_of_eq (by eval_expr) hm1, rfl, rfl, rfl⟩
            have hhp1_w : hp₁ < 2 ^ w := by omega
            have hslotsL_w : frameSlots Q * L < 2 ^ w := by omega
            have hS : 1000 ≤ simScale Q := by dsimp only [simScale]; have := one_le_program_regBound Q; omega
            have hxlen_w : x.length < 2 ^ w := by
              have hle : x.length ≤ simScale Q * L * 2 ^ h * (c_top + x.length + 1) := by
                have h1 := scale_Lh_ge_one Q L h 1 hL1 (by omega)
                calc x.length ≤ c_top + x.length + 1 := by omega
                  _ = 1 * (c_top + x.length + 1) := by ring
                  _ ≤ (simScale Q * L * 2 ^ h) * (c_top + x.length + 1) :=
                    Nat.mul_le_mul_right _ (by simpa using h1)
                  _ = simScale Q * L * 2 ^ h * (c_top + x.length + 1) := by ring
              omega
            have hr0_4 : st₄.regs 0 = ctrl := by simp [st₄, hr0_3]
            have hr1_4 : st₄.regs 1 = x.length := by
              simp only [st₄, st₃, st₂, st₁]; rw [Function.update_of_ne (by omega),
                Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega), hr1_0]
            have hr2_4 : st₄.regs 2 = retDst := by
              simp only [st₄, st₃, st₂, st₁]; rw [Function.update_of_ne (by omega),
                Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega), hr2_0]
            have hr3_4 : st₄.regs 3 = ctrl + 1 := by simp [st₄, hr3_3]
            have hr4_4 : st₄.regs 4 = L := by simp [st₄, hr4_3]
            have hr5_4 : st₄.regs 5 = 2 ^ h := by simp [st₄, hr5_3]
            have hr6_4 : st₄.regs 6 = hp₀ := by simp [st₄]
            set st₅ : State := { st₄ with mem := Function.update st₄.mem (ctrl + 1) hp₁ }
            have hs5 : Runs w p ω
                (.store (.reg 3) (.bin .add (.reg 6) (.bin .mul (.const (frameSlots Q)) (.reg 4))))
                st₄ .normal st₅ 7 := by
              refine runs_store_iff.mpr ⟨ctrl + 1, hp₁, by eval_expr,
                Expr.eval_add (by eval_expr)
                  (Expr.eval_mul (by simp [Expr.eval, hb.hslots_w]) (by eval_expr) hslotsL_w) hhp1_w,
                rfl, rfl, rfl⟩
            have hargs_fh : evalArgs w st₅ [.reg 1, .reg 6, .reg 4, .reg 5] =
                some [x.length, hp₀, L, 2 ^ h] :=
              evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
                (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))
            have hhp0L_w : hp₀ + L < 2 ^ w := by
              have : L ≤ frameSlots Q * L :=
                Nat.le_mul_of_pos_left L (by have := frameSlots_ge Q; omega)
              omega
            have hpre_fh : (mwFromHostContract w).pre [x.length, hp₀, L, 2 ^ h] st₅.mem :=
              ⟨x.length, hp₀, L, h, rfl, hh, hw2, hhp0L_w⟩
            obtain ⟨st₆, c_fh, _, hcall_fh, hpost_fh, _, hother_fh, hc_fh⟩ :=
              runs_call_of_meetsContract (r := 8) (mwFromHost_of_arithModule hArith) hargs_fh
                (by
                  intro a ha
                  have := hb.hH2_w
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
                  rcases ha with rfl | rfl | rfl | rfl <;> omega)
                hpre_fh ω
            rcases hpost_fh with ⟨_, _, _, h', heq_fh, _, hfh_lim, hfr_fh⟩
            simp only [List.cons.injEq, and_true] at heq_fh
            rcases heq_fh with ⟨rfl, rfl, rfl, hp_eq⟩
            have hh_eq := Nat.pow_right_injective (by norm_num) hp_eq.symm
            cases hh_eq
            have hst6_below : ∀ q, q < hp₀ → st₆.mem q = st₅.mem q := fun q hq =>
              hfr_fh q (Or.inl hq)
            have hst6_above : ∀ q, hp₀ + L ≤ q → st₆.mem q = st₅.mem q := fun q hq =>
              hfr_fh q (Or.inr hq)
            have hctrl1_6 : st₆.mem (ctrl + 1) = hp₁ := by
              rw [hst6_below (ctrl + 1) (by omega)]; simp [st₅, st₄]
            have hm2_6 : st₆.mem (ctrl + 2) = L := by
              rw [hst6_below (ctrl + 2) (by omega)]
              simp only [st₅, st₄, st₃, st₂, st₁, st₀]
              rw [Function.update_of_ne (by omega : ctrl + 2 ≠ ctrl + 1)]; exact hm2
            have hm3_6 : st₆.mem (ctrl + 3) = h := by
              rw [hst6_below (ctrl + 3) (by omega)]
              simp only [st₅, st₄, st₃, st₂, st₁, st₀]
              rw [Function.update_of_ne (by omega : ctrl + 3 ≠ ctrl + 1)]; exact hm3
            have hm4_6 : st₆.mem (ctrl + 4) = 2 ^ h := by
              rw [hst6_below (ctrl + 4) (by omega)]
              simp only [st₅, st₄, st₃, st₂, st₁, st₀]
              rw [Function.update_of_ne (by omega : ctrl + 4 ≠ ctrl + 1)]; exact hm4
            have hctrl_6 : st₆.mem ctrl = mem ctrl := by
              rw [hst6_below ctrl (by omega)]
              simp only [st₅, st₄, st₃, st₂, st₁, st₀]
              rw [Function.update_of_ne (by omega : ctrl ≠ ctrl + 1)]; rfl
            have hin6_eq : ∀ q, InTrie mem L h L (mem ctrl) q → st₆.mem q = mem q := by
              intro q hq
              have hlt := (inTrie_bounds htrie.2.1 q hq).2
              have hne1 : q ≠ ctrl + 1 := by rcases (hin_disj q hq).1 with h1 | h1 <;> omega
              rw [hst6_below q hlt]
              simp only [st₅, st₄, st₃, st₂, st₁, st₀]
              rw [Function.update_of_ne hne1]; rfl
            have hz_6 : ZeroFrom st₆.mem hp₁ := by
              intro q hq
              have hq_ge : hp₀ + L ≤ q := by
                have : L ≤ frameSlots Q * L :=
                  Nat.le_mul_of_pos_left L (by have := frameSlots_ge Q; omega)
                omega
              rw [hst6_above q hq_ge]
              simp only [st₅, st₄, st₃, st₂, st₁, st₀]
              rw [Function.update_of_ne (by omega)]
              exact htrie.2.2 q (by omega)
            have hsub_6 : Subtrie st₆.mem L h hp₁ L (st₆.mem ctrl) (initMem x) := by
              rw [hctrl_6]
              exact subtrie_mono_hp (by omega : hp₀ ≤ hp₁) (subtrie_congr_mem hin6_eq htrie.2.1)
            have hin6_disj : ∀ q, InTrie st₆.mem L h L (st₆.mem ctrl) q →
                (q < ctrl ∨ ctrl + 5 ≤ q) ∧ (q < retDst ∨ retDst + L ≤ q) ∧
                (q < hp₀ ∨ hp₁ ≤ q) := by
              intro q hq
              rw [hctrl_6, inTrie_congr_mem L (mem ctrl) hin6_eq q] at hq
              exact ⟨(hin_disj q hq).1, (hin_disj q hq).2, Or.inl (inTrie_bounds htrie.2.1 q hq).2⟩
            have hxlen_lh : x.length < 2 ^ (L * h) :=
              lt_of_lt_of_le hxlen_w' (Nat.pow_le_pow_right (by norm_num) hw'_lh)
            have hmem_x_lt : ∀ a, initMem x a < 2 ^ w' := by
              intro a
              simp only [initMem]
              by_cases ha : a < x.length
              · rw [List.getD_eq_getElem _ _ ha]; exact hx_lt _ (List.getElem_mem ha)
              · rw [List.getD_eq_default _ _ (Nat.not_lt.mp ha)]; exact Nat.two_pow_pos _
            have hg0_reg_lt : ∀ r < Q.regBound, (startState [x.length] (initMem x) 0).regs r < 2 ^ w' := by
              intro r _
              simp only [startState]
              rcases r with _ | r
              · simpa using hxlen_w'
              · simp [List.getD]
            have hg0_reg_lim : ∀ r < Q.regBound,
                LimbsAt st₆.mem (hp₀ + r * L) L h ((startState [x.length] (initMem x) 0).regs r) := by
              intro r _
              simp only [startState]
              rcases r with _ | r
              · simpa using limbsAt_iff_pointwise.mpr ⟨hxlen_lh, hfh_lim⟩
              · simp only [List.getD, List.getElem?_cons_succ, List.getElem?_nil, Option.getD_none]
                refine limbsAt_zero_iff.mpr (WordRAM.listAt_replicate.mpr fun i hi => ?_)
                have hge : hp₀ + L ≤ hp₀ + (r + 1) * L + i := by
                  have := slot_mul_le_mul (by omega : 1 ≤ r + 1) (L := L); omega
                rw [hst6_above (hp₀ + (r + 1) * L + i) hge]
                simp only [st₅, st₄, st₃, st₂, st₁, st₀]
                rw [Function.update_of_ne (by omega)]
                exact htrie.2.2 (hp₀ + (r + 1) * L + i) (by omega)
            have hbody_mem : body0 ∈ Q.procs := List.mem_of_getElem? hproc0
            have hbody_stmt : ∀ hinvC : SimFrameInv w w' L h Q ctrl hp₀ retDst
                { mem := st₆.mem, regs := procEntryRegs ctrl retDst hp₀ L h, pos := st₆.pos }
                (startState [x.length] (initMem x) 0),
                CompileStmtPost w w' L h base p Q ω 0 body0 ctrl hp₀ retDst
                { mem := st₆.mem, regs := procEntryRegs ctrl retDst hp₀ L h, pos := st₆.pos }
                o₀ gst₀ c₀ :=
              fun hinvC => compileStmt_runs hComp hL1 hh hw2 hw'1 hw'_lh fuel' body0 0 ctrl hp₀
                retDst { mem := st₆.mem, regs := procEntryRegs ctrl retDst hp₀ L h, pos := st₆.pos }
                (startState [x.length] (initMem x) 0) o₀ gst₀ c₀ hbody0
                (stmt_regBound_le_program hbody_mem) (le_programTempBound hbody_mem) hinvC
                (by dsimp only; rw [hctrl1_6]; exact hhp1_heap)
            obtain ⟨st₇, c_proc, hr_proc, hc_proc, hhp7_lo, hhp7_hi, hlim_ret, ho0_lt, htrie₇,
                hin7_sub, hin7_disj, hmem7_lt, hfr₇⟩ :=
              compileProc_from_stmt (pos₀ := st₆.pos) (mem₀ := st₆.mem) hComp hL1 hh hw2 hw'1
                hm2_6 hm3_6 hm4_6 hctrl_hp hret_hp hret_ctrl (by rw [hctrl1_6])
                ⟨by rw [hctrl1_6]; have := htrie.1; omega,
                 by rw [hctrl1_6]; exact hsub_6,
                 by rw [hctrl1_6]; exact hz_6⟩
                hin6_disj hg0_reg_lt hg0_reg_lim hmem_x_lt hc0_pos
                (by rw [hctrl1_6]; exact hhp1_heap) hbody_stmt
            rw [hctrl1_6] at hhp7_lo hhp7_hi hfr₇
            have hr0_6 : st₆.regs 0 = ctrl := by rw [hother_fh 0 (by omega), hr0_4]
            have hr2_6 : st₆.regs 2 = retDst := by rw [hother_fh 2 (by omega), hr2_4]
            have hr6_6 : st₆.regs 6 = hp₀ := by rw [hother_fh 6 (by omega), hr6_4]
            have hargs_call : evalArgs w st₆ [.reg 0, .reg 2, .reg 6] = some [ctrl, retDst, hp₀] :=
              evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))
            have hproc_base : p.procs[base + 21 + 0]? =
                some (compileProc Q (base + 1) (base + 19) (base + 21) body0) :=
              compileProc_procs_at hComp hproc0
            set st₈ : State := { st₇ with regs := Function.update st₆.regs 8 0 }
            have hr_call : Runs w p ω (.call 8 (base + 21 + 0) [.reg 0, .reg 2, .reg 6])
                st₆ .normal st₈ (argsSize [.reg 0, .reg 2, .reg 6] + c_proc + 1) :=
              runs_call_iff.mpr ⟨[ctrl, retDst, hp₀],
                compileProc Q (base + 1) (base + 19) (base + 21) body0, .returned 0, st₇, c_proc,
                hargs_call, hproc_base, hr_proc, rfl, rfl, rfl⟩
            have hr_ret : Runs w p ω (.ret (.const 0)) st₈ (.returned 0) st₈ 2 :=
              runs_ret_iff.mpr ⟨0, by simp [Expr.eval], rfl, rfl, rfl⟩
            have hr_entry : Runs w p ω (simEntry Q (base + 1) (base + 21))
                st₀ (.returned 0) st₈
                (4 + (5 + (5 + (3 + (7 + (c_fh + ((3 + c_proc + 1) + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
              runs_seq_iff.mpr (Or.inr ⟨st₁, 4, _, ha3,
                runs_seq_iff.mpr (Or.inr ⟨st₂, 5, _, ha4,
                  runs_seq_iff.mpr (Or.inr ⟨st₃, 5, _, ha5,
                    runs_seq_iff.mpr (Or.inr ⟨st₄, 3, _, ha6,
                      runs_seq_iff.mpr (Or.inr ⟨st₅, 7, _, hs5,
                        runs_seq_iff.mpr (Or.inr ⟨st₆, c_fh, _, hcall_fh,
                          runs_seq_iff.mpr (Or.inr ⟨st₈, _, 2, hr_call, hr_ret, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
            have hout_len : out.length = o₀.value := by
              rw [← hout_eq]; simp
            have hout_get : ∀ i (hi : i < out.length), gst₀.mem i = out[i] := by
              intro i hi
              have hi0 : i < o₀.value := by omega
              have h_eq : out = List.map gst₀.mem (List.range o₀.value) := by
                rw [← hout_eq]; simp
              have hopt := congr_arg (fun l : List ℕ => l[i]?) h_eq
              simp only [List.getElem?_eq_getElem hi, List.getElem?_map,
                List.getElem?_range, hi0, Option.map_some, Option.some.injEq] at hopt
              exact hopt.symm
            have hin8_sub : ∀ q, InTrie st₈.mem L h L (st₈.mem ctrl) q →
                InTrie mem L h L (mem ctrl) q ∨ (hp₀ ≤ q ∧ q < st₈.mem (ctrl + 1)) := by
              intro q hq
              dsimp only [st₈] at hq ⊢
              rcases hin7_sub q hq with hq6 | ⟨hlo, hhi⟩
              · rw [hctrl_6, inTrie_congr_mem L (mem ctrl) hin6_eq q] at hq6
                exact Or.inl hq6
              · exact Or.inr ⟨by omega, hhi⟩
            refine ⟨st₈, _, st₈.mem (ctrl + 1), gst₀.mem, hr_entry, rfl, by dsimp only [st₈]; omega,
              ?_, htrie₇, by rw [hout_len]; exact hlim_ret, hout_get, hin8_sub, ?_, ?_⟩
            · dsimp only [st₈]
              have hdist : simScale Q * L * 2 ^ h * (c_top + x.length + 1) =
                  simScale Q * L * 2 ^ h * c₀ + simScale Q * L * 2 ^ h * 1 +
                  simScale Q * L * 2 ^ h * (x.length + 2) := by rw [← hc0_le]; ring
              have h1 := scale_Lh_ge_one Q L h 1 hL1 (by omega)
              have hle1 : frameSlots Q * L ≤ simScale Q * L * 2 ^ h * 1 := by
                have h2h : 1 ≤ 2 ^ h := Nat.one_le_pow h 2 (by norm_num)
                have hsl := frameSlots_lt_simScale Q
                calc frameSlots Q * L ≤ simScale Q * L := Nat.mul_le_mul_right L (le_of_lt hsl)
                  _ = simScale Q * L * 1 * 1 := by ring
                  _ ≤ simScale Q * L * 2 ^ h * 1 :=
                    Nat.mul_le_mul_right 1 (Nat.mul_le_mul_left _ h2h)
              omega
            · intro q hq hqc0 hqc1 hqi hqr
              have hqi6 : ¬ InTrie st₆.mem L h L (st₆.mem ctrl) q := by
                rw [hctrl_6, inTrie_congr_mem L (mem ctrl) hin6_eq q]; exact hqi
              dsimp only [st₈]
              rw [hfr₇ q (by omega) hqc0 hqc1 hqi6 hqr (Or.inl hq), hst6_below q hq]
              simp only [st₅, st₄, st₃, st₂, st₁, st₀]
              rw [Function.update_of_ne hqc1]; rfl
            · dsimp only [mwFromHostContract] at hc_fh
              simp only [argsSize, Expr.size] at hc_fh
              have h1w' : 1 ≤ L * w' := Nat.mul_pos hL1 hw'1
              have hoverhead : 25 * L + 140 + 80 * L * w' + 10 ≤ simScale Q * L * w' * 2 := by
                have h150 : 25 * L + 150 ≤ 175 * L * w' := mul_Lw'_bound hL1 hw'1 (by omega)
                have h255 : 175 * L * w' + 80 * L * w' = 255 * L * w' := by ring
                have h2S : 1000 * L * w' * 2 ≤ simScale Q * L * w' * 2 :=
                  Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hS))
                have h265 : 265 * (L * w') ≤ 2000 * (L * w') := Nat.mul_le_mul_right _ (by omega)
                have : 255 * L * w' + 10 ≤ 265 * (L * w') := by
                  have := Nat.le_mul_of_pos_right 10 h1w'
                  have : 265 * (L * w') = 255 * L * w' + 10 * (L * w') := by ring
                  omega
                have : 2000 * (L * w') = 1000 * L * w' * 2 := by ring
                omega
              have hdist : simScale Q * L * w' * (c_top + x.length + 1) =
                  simScale Q * L * w' * c₀ + simScale Q * L * w' * 2 +
                  simScale Q * L * w' * (x.length + 1) := by rw [← hc0_le]; ring
              omega

/-- Main simulation theorem (shaped like `WordRAM.runner_spec`): calling `base` on
`[.const ctrl, .const x.length, .const retDst]` in any host program `p` with `p.HasAt base (compile Q base)`
simulates a `w'`-bit deterministic guest run (`ω₀ = fun _ => false`) at narrow host width `w`,
leaving `|out|` in `L` limbs at `retDst`, an updated trie representing `gmem'` extending `out`,
preserved memory outside `[ctrl, ctrl+2) ∪ [retDst, retDst+L) ∪ InTrie`, bump allocation
`≤ simScale Q * L * 2 ^ h * (cost + x.length + 1)`, and host cost
`≤ simScale Q * L * w' * (cost + x.length + 1)`. -/
theorem simulate_runsTo {w w' L h base rRet : ℕ} {p Q : Program} {ω : ℕ → Bool}
    {st₀ : State} {x out : List ℕ} {cost ctrl hp₀ retDst : ℕ}
    (hComp : p.HasAt base (compile Q base))
    (hL1 : 1 ≤ L) (hh : 1 ≤ h) (hw2 : 2 * h + 2 ≤ w) (hw'1 : 1 ≤ w') (hw'_lh : w' ≤ L * h)
    (hctrl_hp : ctrl + 5 ≤ hp₀) (hret_hp : retDst + L ≤ hp₀)
    (hret_ctrl : retDst + L ≤ ctrl ∨ ctrl + 5 ≤ retDst)
    (hm1 : st₀.mem (ctrl + 1) = hp₀) (hm2 : st₀.mem (ctrl + 2) = L)
    (hm3 : st₀.mem (ctrl + 3) = h) (hm4 : st₀.mem (ctrl + 4) = 2 ^ h)
    (hx_lt : ∀ v ∈ x, v < 2 ^ w')
    (htrie : TrieRep st₀.mem L h hp₀ (st₀.mem ctrl) (initMem x))
    (hin_disj : ∀ q, InTrie st₀.mem L h L (st₀.mem ctrl) q →
      (q < ctrl ∨ ctrl + 5 ≤ q) ∧ (q < retDst ∨ retDst + L ≤ q))
    (hbound : hp₀ + simScale Q * L * 2 ^ h * (cost + x.length + 1) < 2 ^ w)
    (hrun : RunsTo w' Q x (fun _ => false) out cost) :
    ∃ st' c hp' gmem',
      Runs w p ω (.call rRet base [.const ctrl, .const x.length, .const retDst]) st₀ .normal st' c ∧
      st'.regs rRet = 0 ∧
      st'.mem (ctrl + 1) = hp' ∧
      hp₀ ≤ hp' ∧
      hp' ≤ hp₀ + simScale Q * L * 2 ^ h * (cost + x.length + 1) ∧
      TrieRep st'.mem L h hp' (st'.mem ctrl) gmem' ∧
      LimbsAt st'.mem retDst L h out.length ∧
      (∀ i (hi : i < out.length), gmem' i = out[i]) ∧
      (∀ q, InTrie st'.mem L h L (st'.mem ctrl) q →
        InTrie st₀.mem L h L (st₀.mem ctrl) q ∨ (hp₀ ≤ q ∧ q < hp')) ∧
      (∀ q, q < hp₀ → q ≠ ctrl → q ≠ ctrl + 1 → ¬ InTrie st₀.mem L h L (st₀.mem ctrl) q →
        (q < retDst ∨ retDst + L ≤ q) → st'.mem q = st₀.mem q) ∧
      c ≤ simScale Q * L * w' * (cost + x.length + 1) := by
  obtain ⟨st_e, c_e, hp', gmem', hr_e, hm1_e, hhp_lo, hhp_hi, htrie_e, hlim_ret,
      hout_get, hin_e, hfr_e, hc_e⟩ :=
    simEntry_runs (pos₀ := st₀.pos) hComp hL1 hh hw2 hw'1 hw'_lh hctrl_hp hret_hp hret_ctrl
      hm1 hm2 hm3 hm4 hx_lt htrie hin_disj hbound hrun
  have h1 := scale_Lh_ge_one Q L h 1 hL1 (by omega)
  have hxlen_w : x.length < 2 ^ w := by
    have : x.length ≤ simScale Q * L * 2 ^ h * (cost + x.length + 1) := by
      calc x.length ≤ cost + x.length + 1 := by omega
        _ = 1 * (cost + x.length + 1) := by ring
        _ ≤ (simScale Q * L * 2 ^ h) * (cost + x.length + 1) :=
          Nat.mul_le_mul_right _ (by simpa using h1)
        _ = simScale Q * L * 2 ^ h * (cost + x.length + 1) := by ring
    omega
  have hctrl_w : ctrl < 2 ^ w := by omega
  have hret_w : retDst < 2 ^ w := by omega
  have hargs : evalArgs w st₀ [.const ctrl, .const x.length, .const retDst] =
      some [ctrl, x.length, retDst] :=
    evalArgs_cons (by simp [Expr.eval, hctrl_w])
      (evalArgs_cons (by simp [Expr.eval, hxlen_w])
        (evalArgs_cons (by simp [Expr.eval, hret_w]) (evalArgs_nil _ _)))
  have hproc_entry := simEntry_procs_at hComp
  set st' : State := { st_e with regs := Function.update st₀.regs rRet 0 }
  have hr_call : Runs w p ω (.call rRet base [.const ctrl, .const x.length, .const retDst])
      st₀ .normal st' (argsSize [.const ctrl, .const x.length, .const retDst] + c_e + 1) :=
    runs_call_iff.mpr ⟨[ctrl, x.length, retDst], simEntry Q (base + 1) (base + 21), .returned 0,
      st_e, c_e, hargs, hproc_entry, hr_e, rfl, rfl, rfl⟩
  refine ⟨st', _, hp', gmem', hr_call, by simp [st'], hm1_e, hhp_lo, hhp_hi, htrie_e, hlim_ret,
    hout_get, hin_e, hfr_e, ?_⟩
  simp only [argsSize, Expr.size]
  have hS : 1000 ≤ simScale Q := by dsimp only [simScale]; have := one_le_program_regBound Q; omega
  have h1w' : 1 ≤ L * w' := Nat.mul_pos hL1 hw'1
  have h10 : 10 ≤ simScale Q * L * w' * (cost + x.length + 1) := by
    have hmul : 10 ≤ simScale Q * (L * w') * (cost + x.length + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul (by omega : 10 ≤ simScale Q) h1w')
        (by omega : 1 ≤ cost + x.length + 1)
    have : simScale Q * (L * w') * (cost + x.length + 1) =
        simScale Q * L * w' * (cost + x.length + 1) := by ring
    omega
  omega

end MinCostFlow.WideWord
