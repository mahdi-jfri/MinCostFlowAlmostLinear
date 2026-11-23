module

public import MinCostFlow.Machine.WideWord.SimulateInv

/-!
# Simulation of wide-word guest statements

This file proves `compileStmt_runs`: every terminating `exec w' Q (fun _ => false) fuel s gst`
is simulated by `compileStmt Q (base + 1) (base + 19) (base + 21) depth s` in at most
`simScale Q * L * w' * c_G` host steps and `simScale Q * L * 2 ^ h * c_G` bump words,
preserving `SimFrameInv` across `.normal` transitions and producing `LimbsAt` at `retDst` on
`.returned`.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM

theorem compileStmt_runs {w w' L h base : ℕ} {p Q : Program} {ω : ℕ → Bool}
    (hComp : p.HasAt base (compile Q base))
    (hL1 : 1 ≤ L) (hh : 1 ≤ h) (hw2 : 2 * h + 2 ≤ w) (hw'1 : 1 ≤ w') (hw'_lh : w' ≤ L * h) :
    ∀ (fuel : ℕ) (s : Stmt) (depth ctrl framePtr retDst : ℕ) (st gst : State)
      (o_G : Outcome) (gst' : State) (c_G : ℕ),
      exec w' Q (fun _ => false) fuel s gst = some (o_G, gst', c_G) →
      s.regBound ≤ Q.regBound →
      stmtTempDepth s ≤ programTempBound Q →
      SimFrameInv w w' L h Q ctrl framePtr retDst st gst →
      st.mem (ctrl + 1) + simScale Q * L * 2 ^ h * c_G < 2 ^ w →
      CompileStmtPost w w' L h base p Q ω depth s ctrl framePtr retDst st o_G gst' c_G := by
  have hMain : ∀ fuel, CompileStmtProp w w' L h base p Q ω fuel := by
    intro fuel
    induction fuel using Nat.strong_induction_on with
    | h fuel ih =>
      intro s depth ctrl framePtr retDst st gst o_G gst' c_G h_exec hs_rb hs_td hinv hheap
      have hArith := arithModule_hasAt_of_compile hComp
      have hTrie := trieModule_hasAt_of_compile hComp
      cases fuel with
      | zero => simp [exec] at h_exec
      | succ fuel =>
        have hcG_pos : 1 ≤ c_G := exec_cost_pos h_exec
        have hcf := hinv.ctrl_lt_frame
        have hrf := hinv.ret_lt_frame
        have hfh := hinv.frame_le_hp
        have hb := frame_word_bounds hL1 hh hw2 hcG_pos hcf hrf hfh hheap
        have hfw := hb.hframe_w
        have hS : 1000 ≤ simScale Q := by
          dsimp only [simScale]; have := one_le_program_regBound Q; omega
        have hS_pos : 0 < simScale Q := by omega
        have h1w' : 1 ≤ L * w' := Nat.mul_pos hL1 hw'1
        have hS_Lw' : 1 ≤ simScale Q * L * w' := Nat.mul_pos (Nat.mul_pos hS_pos hL1) hw'1
        have hQ_slots : Q.regBound < frameSlots Q := frameSlots_ge Q
        cases s with
        | nop =>
          simp only [exec, Option.some.injEq, Prod.mk.injEq] at h_exec
          rcases h_exec with ⟨rfl, rfl, rfl⟩
          refine ⟨.normal, st, 1, runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, ?_, le_refl _,
            Nat.le_add_right _ _, fun _ _ _ => rfl, fun _ hq => Or.inl hq,
            fun _ _ _ _ _ _ _ => rfl, rfl, hinv⟩
          simpa using hS_Lw'
        | assign r e =>
          simp only [exec] at h_exec
          cases he : e.eval w' gst with
          | none => simp [he] at h_exec
          | some v =>
            simp only [he, Option.some.injEq, Prod.mk.injEq] at h_exec
            rcases h_exec with ⟨rfl, rfl, rfl⟩
            have hr_rb : r < Q.regBound := by simp [Stmt.regBound] at hs_rb; omega
            have he_rb : e.regBound ≤ Q.regBound := by simp [Stmt.regBound] at hs_rb; omega
            have he_td : Q.regBound + 1 + exprTempDepth e ≤ frameSlots Q := by
              simp only [stmtTempDepth, frameSlots] at hs_td ⊢; omega
            have hv_lt : v < 2 ^ w' := expr_eval_lt_two_pow
              (fun r' hr' => hinv.reg_lt r' (lt_of_lt_of_le hr' he_rb)) hinv.mem_lt he
            obtain ⟨st₁, c₁, hr₁, hreg₁, hlim₁, hfr₁, hc₁⟩ :=
              compileExpr_runs (ω := ω) hArith hTrie hL1 hh hw2 hw'1 hw'_lh hb.hLh hb.hslots_w
                hb.hL_w hb.hH_w hb.hH2_w hb.hhp_w (by omega) hfw e Q.regBound
                (Q.regBound + 1) v st gst he he_rb (le_refl _) (by omega) he_td
                hinv.r2 hinv.r3 hinv.r5 hinv.r6 hinv.r7 rfl hinv.trie.2.1
                (fun q hq => (hinv.inTrie_disj q hq).2.2) hinv.reg_lt hinv.reg_limbs hinv.mem_lt
            have hr_slots : r < frameSlots Q := by omega
            have hr_end_fr : r * L + L ≤ frameSlots Q * L := slot_end_le_frame hr_slots
            have r2_1 : st₁.regs 2 = framePtr := by rw [hreg₁ 2 (by omega), hinv.r2]
            have r5_1 : st₁.regs 5 = L := by rw [hreg₁ 5 (by omega), hinv.r5]
            have hsrc_eval : (slotAddr 2 Q.regBound).eval w st₁ = some (framePtr + Q.regBound * L) :=
              eval_slotAddr r2_1 r5_1 hQ_slots hb.hslots_w hb.hL_w hfw
            have hdst_eval : (slotAddr 2 r).eval w st₁ = some (framePtr + r * L) :=
              eval_slotAddr r2_1 r5_1 hr_slots hb.hslots_w hb.hL_w hfw
            have hargs_cp : evalArgs w st₁ [slotAddr 2 Q.regBound, slotAddr 2 r, .reg 5] =
                some [framePtr + Q.regBound * L, framePtr + r * L, L] :=
              evalArgs_cons hsrc_eval (evalArgs_cons hdst_eval (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))
            have hsrc_end : framePtr + Q.regBound * L + L < 2 ^ w := by
              have := slot_end_le_frame hQ_slots (L := L); omega
            have hdst_end : framePtr + r * L + L < 2 ^ w := by omega
            have hdst_lt_src : framePtr + r * L + L ≤ framePtr + Q.regBound * L := by
              have := slot_end_le_frame hr_rb (L := L); omega
            have hpre_cp : (mwCopyContract w).pre [framePtr + Q.regBound * L, framePtr + r * L, L] st₁.mem :=
              ⟨framePtr + Q.regBound * L, framePtr + r * L, L, rfl, hb.hw1, hsrc_end, hdst_end,
                Or.inl hdst_lt_src⟩
            obtain ⟨st₂, c₂, _, hcall, hpost₂, _, hother₂, hc₂⟩ :=
              runs_call_of_meetsContract (r := 8) (mwCopy_of_arithModule hArith) hargs_cp
                (by
                  intro a ha
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
                  rcases ha with rfl | rfl | rfl <;> omega)
                hpre_cp ω
            rcases hpost₂ with ⟨_, _, _, heq₂, _, hcp₂, hfr₂⟩
            simp only [List.cons.injEq, and_true] at heq₂
            rcases heq₂ with ⟨rfl, rfl, rfl⟩
            have hmem_fr : ∀ q, (q < framePtr + Q.regBound * L ∨ framePtr + frameSlots Q * L ≤ q) →
                (q < framePtr + r * L ∨ framePtr + r * L + L ≤ q) → st₂.mem q = st.mem q := by
              intro q hqb hqr
              rw [hfr₂ q hqr]
              rcases hqb with hlt | hge
              · exact hfr₁ q (Or.inl hlt) (Or.inl (by
                  have := slot_mul_le_mul (by omega : Q.regBound ≤ Q.regBound + 1) (L := L); omega))
              · have h1 : framePtr + Q.regBound * L + L ≤ framePtr + frameSlots Q * L := by
                  have := slot_end_le_frame hQ_slots (L := L); omega
                have h2 : framePtr + (Q.regBound + 1 + exprTempDepth e) * L ≤ framePtr + frameSlots Q * L := by
                  have := slot_mul_le_mul he_td (L := L); omega
                exact hfr₁ q (Or.inr (by omega)) (Or.inr (by omega))
            have hval_lim : LimbsAt st₂.mem (framePtr + r * L) L h v :=
              limbsAt_iff_pointwise.mpr ⟨hlim₁.lt_pow, fun i hi => by
                rw [hcp₂ i hi]; exact hlim₁.getElem hi⟩
            have hregs₂ : ∀ r' < 16 + depth, r' ≠ 8 → st₂.regs r' = st.regs r' := fun r' _ hd =>
              (hother₂ r' hd).trans (hreg₁ r' hd)
            have hinv₂ := hinv.of_mem_scratch_and_reg (fun r' _ hd => hregs₂ r' (by omega) hd)
              hmem_fr hr_rb hv_lt hval_lim
            have hhp₂_eq : st₂.mem (ctrl + 1) = st.mem (ctrl + 1) :=
              hmem_fr (ctrl + 1) (Or.inl (by omega)) (Or.inl (by omega))
            have hctrl₂_eq : st₂.mem ctrl = st.mem ctrl :=
              hmem_fr ctrl (Or.inl (by omega)) (Or.inl (by omega))
            have hin_eq : ∀ q, InTrie st₂.mem L h L (st₂.mem ctrl) q ↔
                InTrie st.mem L h L (st.mem ctrl) q := by
              rw [hctrl₂_eq]
              exact inTrie_congr_mem L (st.mem ctrl) fun q hq => by
                rcases (hinv.inTrie_disj q hq).2.2 with hlt | hge
                · exact hmem_fr q (Or.inl (by omega)) (Or.inl (by omega))
                · exact hmem_fr q (Or.inr hge) (Or.inr (by omega))
            refine ⟨.normal, st₂, c₁ + c₂ + 1,
              runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, hr₁, hcall, rfl⟩), ?_,
              by rw [hhp₂_eq], by rw [hhp₂_eq]; exact Nat.le_add_right _ _,
              hregs₂, fun q hq => Or.inl ((hin_eq q).mp hq), ?_, rfl, hinv₂⟩
            · dsimp only [mwCopyContract] at hc₂
              simp only [slotAddr, Expr.size, argsSize] at hc₂
              have h50 : 17 * L + 25 ≤ 50 * L * w' := mul_Lw'_bound hL1 hw'1 (by omega)
              have h800 : 800 * L * w' * e.size ≤ simScale Q * L * w' * e.size :=
                Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega)))
              have h50S : 50 * L * w' ≤ simScale Q * L * w' :=
                Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
              have hdist : simScale Q * L * w' * (e.size + 1) =
                  simScale Q * L * w' * e.size + simScale Q * L * w' := by ring
              omega
            · intro q _ _ _ _ _ hqf
              rcases hqf with hlt | hge
              · exact hmem_fr q (Or.inl (by omega)) (Or.inl (by omega))
              · exact hmem_fr q (Or.inr hge) (Or.inr (by omega))
        | store a e =>
          simp only [exec] at h_exec
          cases ha : a.eval w' gst with
          | none => simp [ha] at h_exec
          | some addr =>
            cases he : e.eval w' gst with
            | none => simp [ha, he] at h_exec
            | some v =>
              simp only [ha, he, Option.some.injEq, Prod.mk.injEq] at h_exec
              rcases h_exec with ⟨rfl, rfl, rfl⟩
              have ha_rb : a.regBound ≤ Q.regBound := by simp [Stmt.regBound] at hs_rb; omega
              have he_rb : e.regBound ≤ Q.regBound := by simp [Stmt.regBound] at hs_rb; omega
              have ha_td : Q.regBound + 2 + exprTempDepth a ≤ frameSlots Q := by
                simp only [stmtTempDepth, frameSlots] at hs_td ⊢; omega
              have he_td : Q.regBound + 2 + exprTempDepth e ≤ frameSlots Q := by
                simp only [stmtTempDepth, frameSlots] at hs_td ⊢; omega
              have hva_lt : addr < 2 ^ w' := expr_eval_lt_two_pow
                (fun r hr => hinv.reg_lt r (lt_of_lt_of_le hr ha_rb)) hinv.mem_lt ha
              have hv_lt : v < 2 ^ w' := expr_eval_lt_two_pow
                (fun r hr => hinv.reg_lt r (lt_of_lt_of_le hr he_rb)) hinv.mem_lt he
              have hQ1_slots : Q.regBound + 1 < frameSlots Q := by
                simp only [stmtTempDepth, frameSlots] at hs_td ⊢; omega
              have hQ2_le : Q.regBound + 2 ≤ frameSlots Q := by omega
              obtain ⟨st₁, c₁, hr₁, hreg₁, hlim_a, hfr₁, hc₁⟩ :=
                compileExpr_runs (ω := ω) hArith hTrie hL1 hh hw2 hw'1 hw'_lh hb.hLh hb.hslots_w
                  hb.hL_w hb.hH_w hb.hH2_w hb.hhp_w (by omega) hfw a Q.regBound
                  (Q.regBound + 2) addr st gst ha ha_rb (le_refl _) (by omega) ha_td
                  hinv.r2 hinv.r3 hinv.r5 hinv.r6 hinv.r7 rfl hinv.trie.2.1
                  (fun q hq => (hinv.inTrie_disj q hq).2.2) hinv.reg_lt hinv.reg_limbs hinv.mem_lt
              have hfr_slots₁ : ∀ q, q < framePtr + Q.regBound * L ∨ framePtr + frameSlots Q * L ≤ q →
                  st₁.mem q = st.mem q := by
                intro q hq
                rcases hq with hlt | hge
                · exact hfr₁ q (Or.inl hlt) (Or.inl (by
                    have := slot_mul_le_mul (by omega : Q.regBound ≤ Q.regBound + 2) (L := L); omega))
                · have h1 : framePtr + Q.regBound * L + L ≤ framePtr + frameSlots Q * L := by
                    have := slot_end_le_frame hQ_slots (L := L); omega
                  have h2 : framePtr + (Q.regBound + 2 + exprTempDepth a) * L ≤ framePtr + frameSlots Q * L := by
                    have := slot_mul_le_mul ha_td (L := L); omega
                  exact hfr₁ q (Or.inr (by omega)) (Or.inr (by omega))
              have hinv₁ : SimFrameInv w w' L h Q ctrl framePtr retDst st₁ gst :=
                hinv.of_mem_scratch_only (fun r _ hd => hreg₁ r hd) hfr_slots₁
              have hhp₁_eq : st₁.mem (ctrl + 1) = st.mem (ctrl + 1) :=
                hfr_slots₁ (ctrl + 1) (Or.inl (by omega))
              obtain ⟨st₂, c₂, hr₂, hreg₂, hlim_e, hfr₂, hc₂⟩ :=
                compileExpr_runs (ω := ω) hArith hTrie hL1 hh hw2 hw'1 hw'_lh hb.hLh hb.hslots_w
                  hb.hL_w hb.hH_w hb.hH2_w hb.hhp_w (by omega) hfw e (Q.regBound + 1)
                  (Q.regBound + 2) v st₁ gst he he_rb (by omega) (by omega) he_td
                  hinv₁.r2 hinv₁.r3 hinv₁.r5 hinv₁.r6 hinv₁.r7 rfl (by rw [← hhp₁_eq]; exact hinv₁.trie.2.1)
                  (fun q hq => (hinv₁.inTrie_disj q hq).2.2) hinv₁.reg_lt hinv₁.reg_limbs hinv₁.mem_lt
              have hfr_slots₂ : ∀ q, (q < framePtr + Q.regBound * L ∨ framePtr + frameSlots Q * L ≤ q) →
                  (q < framePtr + (Q.regBound + 1) * L ∨ framePtr + (Q.regBound + 2) * L ≤ q) →
                  st₂.mem q = st.mem q := by
                intro q hq hq1
                have hq1' : q < framePtr + (Q.regBound + 1) * L ∨ framePtr + (Q.regBound + 1) * L + L ≤ q := by
                  rw [show framePtr + (Q.regBound + 1) * L + L = framePtr + (Q.regBound + 2) * L by ring]; exact hq1
                rw [hfr₂ q hq1' _, hfr_slots₁ q hq]
                rcases hq with hlt | hge
                · exact Or.inl (by
                    have := slot_mul_le_mul (by omega : Q.regBound ≤ Q.regBound + 2) (L := L); omega)
                · have := slot_mul_le_mul he_td (L := L); exact Or.inr (by omega)
              have hlim_a₂ : LimbsAt st₂.mem (framePtr + Q.regBound * L) L h addr :=
                hlim_a.congr fun q hq1 hq2 => by
                  rw [hfr₂ q (Or.inl (by
                    have := slot_end_le_frame (by omega : Q.regBound < Q.regBound + 1) (L := L); omega))
                    (Or.inl (by
                      have := slot_end_le_frame (by omega : Q.regBound < Q.regBound + 2) (L := L); omega))]
              have hst2_below : ∀ q, q < framePtr → st₂.mem q = st.mem q := fun q hq =>
                hfr_slots₂ q (Or.inl (by omega)) (Or.inl (by omega))
              have hst2_above : ∀ q, st.mem (ctrl + 1) ≤ q → st₂.mem q = st.mem q := fun q hq =>
                hfr_slots₂ q (Or.inr (by omega))
                  (Or.inr (by have := slot_mul_le_mul hQ2_le (L := L); omega))
              have hst2_inTrie : ∀ q, InTrie st.mem L h L (st.mem ctrl) q → st₂.mem q = st.mem q := by
                intro q hq
                have hd := (hinv.inTrie_disj q hq).2.2
                refine hfr_slots₂ q (by rcases hd with hlt | hge <;> [exact Or.inl (by omega); exact Or.inr hge]) ?_
                rcases hd with hlt | hge
                · exact Or.inl (by
                    have := slot_mul_le_mul (by omega : Q.regBound ≤ Q.regBound + 1) (L := L); omega)
                · exact Or.inr (by have := slot_mul_le_mul hQ2_le (L := L); omega)
              have hctrl₂ : st₂.mem ctrl = st.mem ctrl := hst2_below ctrl (by omega)
              have hhp₂ : st₂.mem (ctrl + 1) = st.mem (ctrl + 1) := hst2_below (ctrl + 1) (by omega)
              have hsub₂ : Subtrie st₂.mem L h (st₂.mem (ctrl + 1)) L (st₂.mem ctrl) gst.mem := by
                rw [hctrl₂, hhp₂]; exact subtrie_congr_mem hst2_inTrie hinv.trie.2.1
              have hz₂ : ZeroFrom st₂.mem (st₂.mem (ctrl + 1)) := by
                rw [hhp₂]; intro q hq; rw [hst2_above q hq]; exact hinv.trie.2.2 q hq
              have hin₂_disj : ∀ q, InTrie st₂.mem L h L (st₂.mem ctrl) q →
                  (q < ctrl ∨ ctrl + 5 ≤ q) ∧ (q < retDst ∨ retDst + L ≤ q) ∧
                  (q < framePtr ∨ framePtr + frameSlots Q * L ≤ q) := by
                intro q hq
                rw [hctrl₂, inTrie_congr_mem L (st.mem ctrl) hst2_inTrie q] at hq
                exact hinv.inTrie_disj q hq
              have r2_2 : st₂.regs 2 = framePtr := by rw [hreg₂ 2 (by omega), hreg₁ 2 (by omega), hinv.r2]
              have r3_2 : st₂.regs 3 = ctrl := by rw [hreg₂ 3 (by omega), hreg₁ 3 (by omega), hinv.r3]
              have r4_2 : st₂.regs 4 = ctrl + 1 := by rw [hreg₂ 4 (by omega), hreg₁ 4 (by omega), hinv.r4]
              have r5_2 : st₂.regs 5 = L := by rw [hreg₂ 5 (by omega), hreg₁ 5 (by omega), hinv.r5]
              have r7_2 : st₂.regs 7 = 2 ^ h := by rw [hreg₂ 7 (by omega), hreg₁ 7 (by omega), hinv.r7]
              have ha_eval : (slotAddr 2 Q.regBound).eval w st₂ = some (framePtr + Q.regBound * L) :=
                eval_slotAddr r2_2 r5_2 hQ_slots hb.hslots_w hb.hL_w hfw
              have he_eval : (slotAddr 2 (Q.regBound + 1)).eval w st₂ =
                  some (framePtr + (Q.regBound + 1) * L) :=
                eval_slotAddr r2_2 r5_2 hQ1_slots hb.hslots_w hb.hL_w hfw
              have hargs_tw : evalArgs w st₂
                  [.reg 3, .reg 4, slotAddr 2 Q.regBound, slotAddr 2 (Q.regBound + 1), .reg 5, .reg 7] =
                  some [ctrl, ctrl + 1, framePtr + Q.regBound * L, framePtr + (Q.regBound + 1) * L, L, 2 ^ h] :=
                evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons ha_eval
                  (evalArgs_cons he_eval (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
                    (evalArgs_nil _ _))))))
              have htw_heap : st.mem (ctrl + 1) + L * 2 ^ h + L < 2 ^ w := by
                have h2hL : L * 2 ^ h + L ≤ 2 * L * 2 ^ h := by
                  have : L ≤ L * 2 ^ h := Nat.le_mul_of_pos_right _ (Nat.one_le_pow h 2 (by norm_num))
                  have : L * 2 ^ h + L * 2 ^ h = 2 * L * 2 ^ h := by ring
                  omega
                have hSLh : 2 * L * 2 ^ h ≤ simScale Q * L * 2 ^ h * (a.size + e.size + 1) := by
                  have hge : 1 ≤ a.size + e.size + 1 := by omega
                  have h1 : 2 ≤ simScale Q := by omega
                  calc 2 * L * 2 ^ h ≤ simScale Q * L * 2 ^ h :=
                        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1)
                    _ ≤ simScale Q * L * 2 ^ h * (a.size + e.size + 1) := Nat.le_mul_of_pos_right _ hge
                omega
              have ha_end : framePtr + Q.regBound * L + L ≤ st₂.mem (ctrl + 1) := by
                rw [hhp₂]; have := slot_end_le_frame hQ_slots (L := L); omega
              have he_end : framePtr + (Q.regBound + 1) * L + L ≤ st₂.mem (ctrl + 1) := by
                rw [hhp₂]; have := slot_end_le_frame hQ1_slots (L := L); omega
              have hQ_end_fr := slot_end_le_frame hQ_slots (L := L)
              have hQ1_end_fr := slot_end_le_frame hQ1_slots (L := L)
              have hpre_tw : (trieWriteContract w).pre
                  [ctrl, ctrl + 1, framePtr + Q.regBound * L, framePtr + (Q.regBound + 1) * L, L, 2 ^ h] st₂.mem :=
                ⟨ctrl, ctrl + 1, framePtr + Q.regBound * L, framePtr + (Q.regBound + 1) * L, L, h,
                  st₂.mem ctrl, st₂.mem (ctrl + 1), gst.mem, addr, v,
                  rfl, hL1, hh, hw2, by rw [hhp₂]; exact hinv.trie.1, rfl, rfl,
                  subtrie_congr_mem (fun _ _ => rfl) hsub₂, hz₂,
                  by rw [hhp₂]; exact htw_heap,
                  by rw [hhp₂]; omega, by rw [hhp₂]; omega, by omega,
                  fun hin => by rcases (hin₂_disj ctrl hin).1 with hlt | hge <;> omega,
                  fun hin => by rcases (hin₂_disj (ctrl + 1) hin).1 with hlt | hge <;> omega,
                  ha_end, he_end,
                  fun i hi => ⟨by omega, by omega, fun hin => by
                    rcases (hin₂_disj _ hin).2.2 with hlt | hge <;> omega⟩,
                  fun i hi => ⟨by omega, by omega, fun hin => by
                    rcases (hin₂_disj _ hin).2.2 with hlt | hge <;> omega⟩,
                  hlim_a₂, hlim_e⟩
              have hctr_w := hb.hctrl_w
              have hhp_w := hb.hhp_w
              have hL_w := hb.hL_w
              have hH2_w := hb.hH2_w
              obtain ⟨st₃, c₃, _, hcall, hpost₃, _, hother₃, hc₃⟩ :=
                runs_call_of_meetsContract (r := 8) (trieWrite_of_trieModule hArith hTrie) hargs_tw
                  (by
                    intro q hq
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
                    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
                  hpre_tw ω
              rcases hpost₃ with ⟨_, _, _, _, _, _, heq₃, _, hhp_inc, hhp_bd, htr_fn, hz₃, hfr₃⟩
              simp only [List.cons.injEq, and_true] at heq₃
              rcases heq₃ with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
              obtain ⟨hsub₃, hin₃_sub⟩ := htr_fn h gst.mem addr v rfl hsub₂ hlim_a₂ hlim_e
              have hr_comb : Runs w p ω
                  (compileStmt Q (base + 1) (base + 19) (base + 21) depth (.store a e))
                  st .normal st₃ (c₁ + (c₂ + c₃ + 1) + 1) :=
                runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂ + c₃ + 1, hr₁,
                  runs_seq_iff.mpr (Or.inr ⟨st₂, c₂, c₃, hr₂, hcall, rfl⟩), rfl⟩)
              have hregs₃ : ∀ r < 16 + depth, r ≠ 8 → st₃.regs r = st.regs r := fun r _ hd =>
                (hother₃ r hd).trans ((hreg₂ r hd).trans (hreg₁ r hd))
              have hin₃_sub' : ∀ q, InTrie st₃.mem L h L (st₃.mem ctrl) q →
                  InTrie st.mem L h L (st.mem ctrl) q ∨
                  (st.mem (ctrl + 1) ≤ q ∧ q < st₃.mem (ctrl + 1)) := by
                intro q hq
                rcases hin₃_sub q hq with hq2 | ⟨hlo, hhi⟩
                · rw [hctrl₂, inTrie_congr_mem L (st.mem ctrl) hst2_inTrie q] at hq2
                  exact Or.inl hq2
                · rw [hhp₂] at hlo; exact Or.inr ⟨hlo, hhi⟩
              have hin₃_disj : ∀ q, InTrie st₃.mem L h L (st₃.mem ctrl) q →
                  (q < ctrl ∨ ctrl + 5 ≤ q) ∧ (q < retDst ∨ retDst + L ≤ q) ∧
                  (q < framePtr ∨ framePtr + frameSlots Q * L ≤ q) := by
                intro q hq
                rcases hin₃_sub' q hq with hq0 | ⟨hlo, _⟩
                · exact hinv.inTrie_disj q hq0
                · omega
              have hfr_below : ∀ q, q < st.mem (ctrl + 1) → q ≠ ctrl → q ≠ ctrl + 1 →
                  ¬ InTrie st.mem L h L (st.mem ctrl) q →
                  (q < retDst ∨ retDst + L ≤ q) →
                  (q < framePtr ∨ framePtr + frameSlots Q * L ≤ q) →
                  st₃.mem q = st.mem q := by
                intro q hq hqc0 hqc1 hqi _ hqf
                have hqi2 : ¬ InTrie st₂.mem L h L (st₂.mem ctrl) q := by
                  rw [hctrl₂, inTrie_congr_mem L (st.mem ctrl) hst2_inTrie q]; exact hqi
                rw [hfr₃ h q rfl hqc0 hqc1 hqi2 (by rw [hhp₂]; exact hq)]
                rcases hqf with hlt | hge
                · exact hst2_below q hlt
                · exact hfr_slots₂ q (Or.inr hge)
                    (Or.inr (by have := slot_mul_le_mul hQ2_le (L := L); omega))
              have hinv₃ : SimFrameInv w w' L h Q ctrl framePtr retDst st₃
                  { gst with mem := Function.update gst.mem addr v } :=
                ⟨by rw [hregs₃ 0 (by omega) (by omega), hinv.r0],
                 by rw [hregs₃ 1 (by omega) (by omega), hinv.r1],
                 by rw [hregs₃ 2 (by omega) (by omega), hinv.r2],
                 by rw [hregs₃ 3 (by omega) (by omega), hinv.r3],
                 by rw [hregs₃ 4 (by omega) (by omega), hinv.r4],
                 by rw [hregs₃ 5 (by omega) (by omega), hinv.r5],
                 by rw [hregs₃ 6 (by omega) (by omega), hinv.r6],
                 by rw [hregs₃ 7 (by omega) (by omega), hinv.r7],
                 by rw [hinv.ctrl_mem_eq_of_frame (by omega) (by omega) hfr_below, hinv.mem2],
                 by rw [hinv.ctrl_mem_eq_of_frame (by omega) (by omega) hfr_below, hinv.mem3],
                 by rw [hinv.ctrl_mem_eq_of_frame (by omega) (by omega) hfr_below, hinv.mem4],
                 hcf, hrf, hinv.ret_disj_ctrl,
                 by rw [hhp₂] at hhp_inc; omega,
                 ⟨by rw [hhp₂] at hhp_inc; have := hinv.trie.1; omega, hsub₃, hz₃⟩,
                 hin₃_disj, hinv.reg_lt,
                 fun r hr => by
                   refine (hinv.reg_limbs r hr).congr fun q hq1 hq2 => ?_
                   have hq_fr : q < framePtr + frameSlots Q * L := by
                     have := slot_end_le_frame (by omega : r < frameSlots Q) (L := L); omega
                   have hq_ltQ : q < framePtr + Q.regBound * L := by
                     have := slot_end_le_frame hr (L := L); omega
                   have hq_ltQ1 : q < framePtr + (Q.regBound + 1) * L := by
                     have := slot_mul_le_mul (by omega : Q.regBound ≤ Q.regBound + 1) (L := L); omega
                   have hqi2 : ¬ InTrie st₂.mem L h L (st₂.mem ctrl) q := by
                     rw [hctrl₂, inTrie_congr_mem L (st.mem ctrl) hst2_inTrie q]
                     intro hin; rcases (hinv.inTrie_disj q hin).2.2 with hlt | hge <;> omega
                   rw [hfr₃ h q rfl (by omega) (by omega) hqi2 (by rw [hhp₂]; omega)]
                   exact hfr_slots₂ q (Or.inl hq_ltQ) (Or.inl hq_ltQ1),
                 fun q => by
                   dsimp only; by_cases hq : q = addr
                   · subst hq; rw [Function.update_self]; exact hv_lt
                   · rw [Function.update_of_ne hq]; exact hinv.mem_lt q⟩
              refine ⟨.normal, st₃, _, hr_comb, ?_, by rw [hhp₂] at hhp_inc; exact hhp_inc, ?_,
                hregs₃, hin₃_sub', hfr_below, rfl, hinv₃⟩
              · dsimp only [trieWriteContract] at hc₃
                simp only [slotAddr, Expr.size, argsSize] at hc₃
                have h150 : 60 * L + 67 ≤ 150 * L * w' := mul_Lw'_bound hL1 hw'1 (by omega)
                have ha_s : 800 * L * w' * a.size ≤ simScale Q * L * w' * a.size :=
                  Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega)))
                have he_s : 800 * L * w' * e.size ≤ simScale Q * L * w' * e.size :=
                  Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega)))
                have h150S : 150 * L * w' ≤ simScale Q * L * w' :=
                  Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
                have hdist : simScale Q * L * w' * (a.size + e.size + 1) =
                    simScale Q * L * w' * a.size + simScale Q * L * w' * e.size +
                    simScale Q * L * w' := by ring
                omega
              · rw [hhp₂] at hhp_bd
                have h2hL : L * 2 ^ h + L ≤ 2 * L * 2 ^ h := by
                  have : L ≤ L * 2 ^ h := Nat.le_mul_of_pos_right _ (Nat.one_le_pow h 2 (by norm_num))
                  have : L * 2 ^ h + L * 2 ^ h = 2 * L * 2 ^ h := by ring
                  omega
                have hSLh : 2 * L * 2 ^ h ≤ simScale Q * L * 2 ^ h * (a.size + e.size + 1) := by
                  have hge : 1 ≤ a.size + e.size + 1 := by omega
                  have h1 : 2 ≤ simScale Q := by omega
                  calc 2 * L * 2 ^ h ≤ simScale Q * L * 2 ^ h :=
                        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1)
                    _ ≤ simScale Q * L * 2 ^ h * (a.size + e.size + 1) := Nat.le_mul_of_pos_right _ hge
                omega
        | rand r =>
          simp only [exec, readWord_const_false, Option.some.injEq, Prod.mk.injEq] at h_exec
          rcases h_exec with ⟨rfl, rfl, rfl⟩
          have hr_rb : r < Q.regBound := by simp [Stmt.regBound] at hs_rb; omega
          have hr_slots : r < frameSlots Q := by omega
          have hr_end_fr : r * L + L ≤ frameSlots Q * L := slot_end_le_frame hr_slots
          have hr_eval : (slotAddr 2 r).eval w st = some (framePtr + r * L) :=
            eval_slotAddr hinv.r2 hinv.r5 hr_slots hb.hslots_w hb.hL_w hfw
          have r5_0 : st.regs 5 = L := hinv.r5
          have hargs : evalArgs w st [slotAddr 2 r, .reg 5] = some [framePtr + r * L, L] :=
            evalArgs_cons hr_eval (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))
          have hr_end : framePtr + r * L + L < 2 ^ w := by omega
          have hpre : (mwZeroContract w).pre [framePtr + r * L, L] st.mem :=
            ⟨framePtr + r * L, L, rfl, hb.hw1, hr_end⟩
          have hfr_w := hb.hframe_w
          have hL_w := hb.hL_w
          obtain ⟨st', c, _, hcall, hpost, _, hother, hc⟩ :=
            runs_call_of_meetsContract (r := 8) (mwZero_of_arithModule hArith) hargs
              (by
                intro a ha
                simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
                rcases ha with rfl | rfl <;> omega)
              hpre ω
          rcases hpost with ⟨_, _, heq, _, hzero_list, hfr⟩
          simp only [List.cons.injEq, and_true] at heq
          rcases heq with ⟨rfl, rfl⟩
          have hinv' := (hinv.of_mem_scratch_and_reg (fun r' _ hd => hother r' hd)
            (fun q _ hqr => hfr q hqr) hr_rb (Nat.two_pow_pos _)
            (limbsAt_zero_iff.mpr hzero_list)).congr_gst_pos (pos' := gst.pos + w')
          have hhp_eq : st'.mem (ctrl + 1) = st.mem (ctrl + 1) :=
            hfr (ctrl + 1) (Or.inl (by omega))
          have hctrl_eq : st'.mem ctrl = st.mem ctrl :=
            hfr ctrl (Or.inl (by omega))
          have hin_eq : ∀ q, InTrie st'.mem L h L (st'.mem ctrl) q ↔
              InTrie st.mem L h L (st.mem ctrl) q := by
            rw [hctrl_eq]
            exact inTrie_congr_mem L (st.mem ctrl) fun q hq => by
              rcases (hinv.inTrie_disj q hq).2.2 with hlt | hge
              · exact hfr q (Or.inl (by omega))
              · exact hfr q (Or.inr (by omega))
          refine ⟨.normal, st', c, hcall, ?_, by rw [hhp_eq], by rw [hhp_eq]; exact Nat.le_add_right _ _,
            fun r' _ hd => hother r' hd, fun q hq => Or.inl ((hin_eq q).mp hq), ?_, rfl, hinv'⟩
          · dsimp only [mwZeroContract] at hc
            simp only [slotAddr, Expr.size, argsSize] at hc
            have h35 : 14 * L + 20 ≤ 35 * L * w' := mul_Lw'_bound hL1 hw'1 (by omega)
            have hS' : 35 * L * w' ≤ simScale Q * L * w' :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
            omega
          · intro q _ _ _ _ _ hqf
            rcases hqf with hlt | hge
            · exact hfr q (Or.inl (by omega))
            · exact hfr q (Or.inr (by omega))
        | seq s₁ s₂ =>
          simp only [exec] at h_exec
          cases hs1 : exec w' Q (fun _ => false) fuel s₁ gst with
          | none => simp [hs1] at h_exec
          | some res₁ =>
            rcases res₁ with ⟨o₁, gst₁, c₁⟩
            have hc1_pos : 1 ≤ c₁ := exec_cost_pos hs1
            have hs1_rb : s₁.regBound ≤ Q.regBound := by simp [Stmt.regBound] at hs_rb; omega
            have hs2_rb : s₂.regBound ≤ Q.regBound := by simp [Stmt.regBound] at hs_rb; omega
            have hs1_td : stmtTempDepth s₁ ≤ programTempBound Q := by
              simp [stmtTempDepth] at hs_td; omega
            have hs2_td : stmtTempDepth s₂ ≤ programTempBound Q := by
              simp [stmtTempDepth] at hs_td; omega
            cases o₁ with
            | returned u =>
              simp only [hs1, Option.some.injEq, Prod.mk.injEq] at h_exec
              rcases h_exec with ⟨rfl, rfl, rfl⟩
              obtain ⟨o_H1, st₁, c_H1, hr₁, hc₁, hhp1_lo, hhp1_hi, hreg₁, hin1_sub, hfr₁, hout₁⟩ :=
                ih fuel (Nat.lt_succ_self fuel) s₁ depth ctrl framePtr retDst st gst (.returned u)
                  gst₁ c₁ hs1 hs1_rb hs1_td hinv (by
                    have := Nat.mul_le_mul_left (simScale Q * L * 2 ^ h) (by omega : c₁ ≤ c₁ + 1)
                    omega)
              rcases hout₁ with ⟨rfl, hu_lt, hlim₁, htrie₁, hin1_disj, hmem1_lt⟩
              refine ⟨.returned 0, st₁, c_H1 + 1, runs_seq_iff.mpr (Or.inl ⟨0, c_H1, hr₁, rfl, rfl⟩),
                ?_, hhp1_lo, ?_, hreg₁, hin1_sub, hfr₁, rfl, hu_lt, hlim₁, htrie₁, hin1_disj, hmem1_lt⟩
              · have hdist : simScale Q * L * w' * (c₁ + 1) =
                    simScale Q * L * w' * c₁ + simScale Q * L * w' := by ring
                omega
              · have := Nat.mul_le_mul_left (simScale Q * L * 2 ^ h) (by omega : c₁ ≤ c₁ + 1)
                omega
            | normal =>
              simp only [hs1] at h_exec
              cases hs2 : exec w' Q (fun _ => false) fuel s₂ gst₁ with
              | none => simp [hs2] at h_exec
              | some res₂ =>
                rcases res₂ with ⟨o₂, gst₂, c₂⟩
                simp only [hs2, Option.some.injEq, Prod.mk.injEq] at h_exec
                rcases h_exec with ⟨rfl, rfl, rfl⟩
                have hc2_pos : 1 ≤ c₂ := exec_cost_pos hs2
                obtain ⟨o_H1, st₁, c_H1, hr₁, hc₁, hhp1_lo, hhp1_hi, hreg₁, hin1_sub, hfr₁, rfl, hinv₁⟩ :=
                  ih fuel (Nat.lt_succ_self fuel) s₁ depth ctrl framePtr retDst st gst .normal
                    gst₁ c₁ hs1 hs1_rb hs1_td hinv (by
                      have := Nat.mul_le_mul_left (simScale Q * L * 2 ^ h) (by omega : c₁ ≤ c₁ + c₂ + 1)
                      omega)
                have hheap₁ : st₁.mem (ctrl + 1) + simScale Q * L * 2 ^ h * c₂ < 2 ^ w := by
                  have hdist : simScale Q * L * 2 ^ h * (c₁ + c₂ + 1) =
                      simScale Q * L * 2 ^ h * c₁ + simScale Q * L * 2 ^ h * c₂ +
                      simScale Q * L * 2 ^ h := by ring
                  omega
                obtain ⟨o_H2, st₂, c_H2, hr₂, hc₂, hhp2_lo, hhp2_hi, hreg₂, hin2_sub, hfr₂, hout₂⟩ :=
                  ih fuel (Nat.lt_succ_self fuel) s₂ depth ctrl framePtr retDst st₁ gst₁ o₂
                    gst₂ c₂ hs2 hs2_rb hs2_td hinv₁ hheap₁
                refine ⟨o_H2, st₂, c_H1 + c_H2 + 1,
                  runs_seq_iff.mpr (Or.inr ⟨st₁, c_H1, c_H2, hr₁, hr₂, rfl⟩), ?_, by omega, ?_,
                  fun r hr hd => (hreg₂ r hr hd).trans (hreg₁ r hr hd), ?_, ?_, hout₂⟩
                · have hdist : simScale Q * L * w' * (c₁ + c₂ + 1) =
                      simScale Q * L * w' * c₁ + simScale Q * L * w' * c₂ +
                      simScale Q * L * w' := by ring
                  omega
                · have hdist : simScale Q * L * 2 ^ h * (c₁ + c₂ + 1) =
                      simScale Q * L * 2 ^ h * c₁ + simScale Q * L * 2 ^ h * c₂ +
                      simScale Q * L * 2 ^ h := by ring
                  omega
                · intro q hq
                  rcases hin2_sub q hq with hq1 | ⟨hlo, hhi⟩
                  · rcases hin1_sub q hq1 with hq0 | ⟨hlo0, hhi0⟩
                    · exact Or.inl hq0
                    · exact Or.inr ⟨hlo0, by omega⟩
                  · exact Or.inr ⟨by omega, hhi⟩
                · intro q hq hqc0 hqc1 hqi hqr hqf
                  have hqi1 : ¬ InTrie st₁.mem L h L (st₁.mem ctrl) q := by
                    intro hqt
                    rcases hin1_sub q hqt with hqt0 | ⟨hlo, _⟩
                    · exact hqi hqt0
                    · omega
                  rw [hfr₂ q (by omega) hqc0 hqc1 hqi1 hqr hqf]
                  exact hfr₁ q hq hqc0 hqc1 hqi hqr hqf
        | cond e s₁ s₂ =>
          simp only [exec] at h_exec
          cases he : e.eval w' gst with
          | none => simp [he] at h_exec
          | some v =>
            simp only [he] at h_exec
            cases hbr : exec w' Q (fun _ => false) fuel (if v = 0 then s₂ else s₁) gst with
            | none => simp [hbr] at h_exec
            | some res =>
              rcases res with ⟨o₁, gst₁, c₁⟩
              simp only [hbr, Option.some.injEq, Prod.mk.injEq] at h_exec
              rcases h_exec with ⟨rfl, rfl, rfl⟩
              have hc1_pos : 1 ≤ c₁ := exec_cost_pos hbr
              have he_rb : e.regBound ≤ Q.regBound := by simp [Stmt.regBound] at hs_rb; omega
              have hbr_rb : (if v = 0 then s₂ else s₁).regBound ≤ Q.regBound := by
                simp only [Stmt.regBound] at hs_rb; split_ifs <;> omega
              have he_td : exprTempDepth e + 1 ≤ max 1 (programTempBound Q) := by
                simp [stmtTempDepth] at hs_td; omega
              have hbr_td : stmtTempDepth (if v = 0 then s₂ else s₁) ≤ programTempBound Q := by
                simp only [stmtTempDepth] at hs_td; split_ifs <;> omega
              have he_heap : st.mem (ctrl + 1) + simScale Q * L * 2 ^ h * (e.size + 1) < 2 ^ w := by
                have := Nat.mul_le_mul_left (simScale Q * L * 2 ^ h) (by omega : e.size + 1 ≤ e.size + c₁ + 1)
                omega
              obtain ⟨st₂, c_iz, hr_iz, hreg₂, hr8_2, hinv₂, hmem_fr, hc_iz⟩ :=
                evalExprAndIsZero_runs (ω := ω) hComp hL1 hh hw2 hw'1 hw'_lh hinv he_heap he he_rb he_td
              have hhp₂_eq : st₂.mem (ctrl + 1) = st.mem (ctrl + 1) :=
                hmem_fr (ctrl + 1) (Or.inl (by omega))
              have hctrl₂_eq : st₂.mem ctrl = st.mem ctrl :=
                hmem_fr ctrl (Or.inl (by omega))
              have hin_eq : ∀ q, InTrie st₂.mem L h L (st₂.mem ctrl) q ↔
                  InTrie st.mem L h L (st.mem ctrl) q := by
                rw [hctrl₂_eq]
                exact inTrie_congr_mem L (st.mem ctrl) fun q hq => by
                  rcases (hinv.inTrie_disj q hq).2.2 with hlt | hge
                  · exact hmem_fr q (Or.inl (by omega))
                  · exact hmem_fr q (Or.inr hge)
              have hheap₂ : st₂.mem (ctrl + 1) + simScale Q * L * 2 ^ h * c₁ < 2 ^ w := by
                have := Nat.mul_le_mul_left (simScale Q * L * 2 ^ h) (by omega : c₁ ≤ e.size + c₁ + 1)
                rw [hhp₂_eq]; omega
              obtain ⟨o_H, st₃, c_br, hr_br, hc_br, hhp3_lo, hhp3_hi, hreg₃, hin3_sub, hfr₃, hout₃⟩ :=
                ih fuel (Nat.lt_succ_self fuel) (if v = 0 then s₂ else s₁) depth ctrl framePtr retDst
                  st₂ gst o₁ gst₁ c₁ hbr hbr_rb hbr_td hinv₂ hheap₂
              have hr_branch : Runs w p ω
                  (if (if v = 0 then 1 else 0) = 0
                   then compileStmt Q (base + 1) (base + 19) (base + 21) depth s₁
                   else compileStmt Q (base + 1) (base + 19) (base + 21) depth s₂)
                  st₂ o_H st₃ c_br := by
                by_cases hv0 : v = 0 <;> simp [hv0] at hr_br ⊢ <;> exact hr_br
              have hr_cond : Runs w p ω
                  (.cond (.reg 8)
                    (compileStmt Q (base + 1) (base + 19) (base + 21) depth s₂)
                    (compileStmt Q (base + 1) (base + 19) (base + 21) depth s₁))
                  st₂ o_H st₃ (1 + c_br + 1) :=
                runs_cond_iff.mpr ⟨if v = 0 then 1 else 0, c_br,
                  by simp [Expr.eval, hr8_2], hr_branch, rfl⟩
              rcases runs_seq_iff.mp hr_iz with ⟨_, _, _, hno, _⟩ | ⟨st₁, c_e, c_iz1, hr_e, hcall_iz, rfl⟩
              · cases hno
              · have hr_all : Runs w p ω
                    (compileStmt Q (base + 1) (base + 19) (base + 21) depth (.cond e s₁ s₂))
                    st o_H st₃ (c_e + (c_iz1 + (1 + c_br + 1) + 1) + 1) :=
                  runs_seq_iff.mpr (Or.inr ⟨st₁, c_e, _, hr_e,
                    runs_seq_iff.mpr (Or.inr ⟨st₂, c_iz1, _, hcall_iz, hr_cond, rfl⟩), rfl⟩)
                refine ⟨o_H, st₃, _, hr_all, ?_, by omega, ?_,
                  fun r hr hd => (hreg₃ r hr hd).trans (hreg₂ r hd), ?_, ?_, hout₃⟩
                · have h50 : 16 * L + 34 ≤ 50 * L * w' := mul_Lw'_bound hL1 hw'1 (by omega)
                  have h800 : 800 * L * w' * e.size ≤ simScale Q * L * w' * e.size :=
                    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega)))
                  have h50S : 50 * L * w' ≤ simScale Q * L * w' :=
                    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
                  have hdist : simScale Q * L * w' * (e.size + c₁ + 1) =
                      simScale Q * L * w' * e.size + simScale Q * L * w' * c₁ +
                      simScale Q * L * w' := by ring
                  omega
                · have := Nat.mul_le_mul_left (simScale Q * L * 2 ^ h) (by omega : c₁ ≤ e.size + c₁ + 1)
                  omega
                · intro q hq
                  rcases hin3_sub q hq with hq2 | ⟨hlo, hhi⟩
                  · rw [hin_eq] at hq2; exact Or.inl hq2
                  · rw [hhp₂_eq] at hlo; exact Or.inr ⟨hlo, hhi⟩
                · intro q hq hqc0 hqc1 hqi hqr hqf
                  have hqi2 : ¬ InTrie st₂.mem L h L (st₂.mem ctrl) q := by
                    rw [hin_eq]; exact hqi
                  rw [hfr₃ q (by rw [hhp₂_eq]; exact hq) hqc0 hqc1 hqi2 hqr hqf]
                  rcases hqf with hlt | hge
                  · exact hmem_fr q (Or.inl (by omega))
                  · exact hmem_fr q (Or.inr hge)
        | loop e body =>
          have h_exec_orig := h_exec
          simp only [exec] at h_exec
          cases he : e.eval w' gst with
          | none => simp [he] at h_exec
          | some v =>
            have he_rb : e.regBound ≤ Q.regBound := by simp [Stmt.regBound] at hs_rb; omega
            have hbody_rb : body.regBound ≤ Q.regBound := by simp [Stmt.regBound] at hs_rb; omega
            have he_td : exprTempDepth e + 1 ≤ max 1 (programTempBound Q) := by
              simp [stmtTempDepth] at hs_td; omega
            have hbody_td : stmtTempDepth body ≤ programTempBound Q := by
              simp [stmtTempDepth] at hs_td; omega
            have he_heap : st.mem (ctrl + 1) + simScale Q * L * 2 ^ h * (e.size + 1) < 2 ^ w := by
              have hle : e.size + 1 ≤ c_G := by
                simp only [he] at h_exec
                by_cases hv0 : v = 0
                · simp only [hv0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h_exec; omega
                · simp only [hv0, ↓reduceIte] at h_exec
                  cases hbe : exec w' Q (fun _ => false) fuel body gst with
                  | none => simp [hbe] at h_exec
                  | some rb =>
                    rcases rb with ⟨ob, gstb, cb⟩
                    cases ob with
                    | returned ub => simp only [hbe, Option.some.injEq, Prod.mk.injEq] at h_exec; omega
                    | normal =>
                      simp only [hbe] at h_exec
                      cases hle' : exec w' Q (fun _ => false) fuel (.loop e body) gstb with
                      | none => simp [hle'] at h_exec
                      | some rl =>
                        rcases rl with ⟨ol, gstl, cl⟩
                        simp only [hle', Option.some.injEq, Prod.mk.injEq] at h_exec; omega
              have := Nat.mul_le_mul_left (simScale Q * L * 2 ^ h) hle
              omega
            obtain ⟨st₁, c_ev, hr_ev, hreg_ev, hrFlag, hinv₁, hmem_ev, hc_ev⟩ :=
              evalE_runs (ω := ω) (depth := depth) hComp hL1 hh hw2 hw'1 hw'_lh hinv he_heap he he_rb he_td
            have hhp₁_eq : st₁.mem (ctrl + 1) = st.mem (ctrl + 1) :=
              hmem_ev (ctrl + 1) (Or.inl (by omega))
            have hctrl₁_eq : st₁.mem ctrl = st.mem ctrl :=
              hmem_ev ctrl (Or.inl (by omega))
            have hin_eq : ∀ q, InTrie st₁.mem L h L (st₁.mem ctrl) q ↔
                InTrie st.mem L h L (st.mem ctrl) q := by
              rw [hctrl₁_eq]
              exact inTrie_congr_mem L (st.mem ctrl) fun q hq => by
                rcases (hinv.inTrie_disj q hq).2.2 with hlt | hge
                · exact hmem_ev q (Or.inl (by omega))
                · exact hmem_ev q (Or.inr hge)
            obtain ⟨o_H, st₂, c_L, hrL, hcL, hhp₂_lo, hhp₂_hi, hreg₂, hin₂_sub, hfr₂, hout₂⟩ :=
              compileLoop_runs hComp hL1 hh hw2 hw'1 hw'_lh (fuel + 1) ih e body depth
                ctrl framePtr retDst st₁ gst o_G gst' c_G v h_exec_orig he he_rb hbody_rb
                he_td hbody_td hinv₁ hrFlag (by rw [hhp₁_eq]; exact hheap)
            refine ⟨o_H, st₂, c_ev + c_L + 1, runs_seq3_assoc hr_ev hrL, ?_,
              by omega, by omega,
              fun r hr hd => (hreg₂ r hr hd).trans (hreg_ev r hr hd), ?_, ?_, hout₂⟩
            · have h55_60 : 55 * L * w' + 1 ≤ 60 * L * w' := by
                have h5 : 1 ≤ 5 * (L * w') := by omega
                have h55' : 55 * (L * w') = 55 * L * w' := by ring
                have h60' : 60 * (L * w') = 60 * L * w' := by ring
                omega
              omega
            · intro q hq
              rcases hin₂_sub q hq with hq1 | ⟨hlo, hhi⟩
              · rw [hin_eq] at hq1; exact Or.inl hq1
              · rw [hhp₁_eq] at hlo; exact Or.inr ⟨hlo, hhi⟩
            · intro q hq hqc0 hqc1 hqi hqr hqf
              have hqi1 : ¬ InTrie st₁.mem L h L (st₁.mem ctrl) q := by
                rw [hin_eq]; exact hqi
              rw [hfr₂ q (by rw [hhp₁_eq]; exact hq) hqc0 hqc1 hqi1 hqr hqf]
              rcases hqf with hlt | hge
              · exact hmem_ev q (Or.inl (by omega))
              · exact hmem_ev q (Or.inr hge)
        | call r f args =>
          simp only [exec] at h_exec
          cases hargs_g : evalArgs w' gst args with
          | none => simp [hargs_g] at h_exec
          | some vs =>
            cases hf_proc : Q.procs[f]? with
            | none => simp [hargs_g, hf_proc] at h_exec
            | some body =>
              simp only [hargs_g, hf_proc] at h_exec
              change (match exec w' Q (fun _ => false) fuel body (startState vs gst.mem gst.pos) with
                | none => none
                | some (o, st', c) => some (.normal, { st' with regs := Function.update gst.regs r o.value },
                    argsSize args + c + 1)) = some (o_G, gst', c_G) at h_exec
              cases hbody_g : exec w' Q (fun _ => false) fuel body (startState vs gst.mem gst.pos) with
              | none => simp [hbody_g] at h_exec
              | some res =>
                rcases res with ⟨o₁, gst₁, c_body⟩
                simp only [hbody_g, Option.some.injEq, Prod.mk.injEq] at h_exec
                rcases h_exec with ⟨rfl, rfl, rfl⟩
                have hc_body_pos : 1 ≤ c_body := exec_cost_pos hbody_g
                have hbody_mem : body ∈ Q.procs := List.mem_of_getElem? hf_proc
                have hbody_rb : body.regBound ≤ Q.regBound := stmt_regBound_le_program hbody_mem
                have hbody_td : stmtTempDepth body ≤ programTempBound Q := le_programTempBound hbody_mem
                have hr_rb : r < Q.regBound := by simp [Stmt.regBound] at hs_rb; omega
                have hargs_len : args.length ≤ Q.regBound := by simp [Stmt.regBound] at hs_rb; omega
                have hargs_rb : argsRegBound args ≤ Q.regBound := by simp [Stmt.regBound] at hs_rb; omega
                have hargs_td : argsTempDepth args + 1 ≤ frameSlots Q - Q.regBound := by
                  simp only [stmtTempDepth, frameSlots] at hs_td ⊢; omega
                have hvs_len : vs.length = args.length := by
                  have aux : ∀ (as : List Expr) (xs : List ℕ),
                      evalArgs w' gst as = some xs → xs.length = as.length := by
                    intro as
                    induction as with
                    | nil => intro xs hx; simp [evalArgs] at hx; subst hx; rfl
                    | cons a as iha =>
                      intro xs hx
                      simp only [evalArgs] at hx
                      cases ha' : a.eval w' gst <;> cases has' : evalArgs w' gst as <;>
                        simp [ha', has'] at hx
                      subst hx; simp [iha _ has']
                  exact aux args vs hargs_g
                have hr_slots : r < frameSlots Q := by omega
                have hr_end_fr : r * L + L ≤ frameSlots Q * L := slot_end_le_frame hr_slots
                set rCallee := 16 + depth
                set hp_old := st.mem (ctrl + 1)
                set st₁ : State := { st with regs := Function.update st.regs rCallee hp_old }
                have ha_rc : Runs w p ω (.assign rCallee (.load (.reg 4))) st .normal st₁ 3 :=
                  runs_assign_iff.mpr ⟨hp_old,
                    Expr.eval_load_of_eq (by simp [Expr.eval, hinv.r4]) rfl, rfl, rfl, rfl⟩
                have hrC_1 : st₁.regs rCallee = hp_old := by simp [st₁]
                have hr4_1 : st₁.regs 4 = ctrl + 1 := by
                  simp only [st₁]; rw [Function.update_of_ne (by omega), hinv.r4]
                have hr5_1 : st₁.regs 5 = L := by
                  simp only [st₁]; rw [Function.update_of_ne (by omega), hinv.r5]
                set hp_new := hp_old + frameSlots Q * L
                have hhp_new_lt : hp_new + simScale Q * L * 2 ^ h * c_body < 2 ^ w := by
                  have hSL : frameSlots Q * L ≤ simScale Q * L * 2 ^ h * 1 := by
                    have h2h : 1 ≤ 2 ^ h := Nat.one_le_pow h 2 (by norm_num)
                    have hsl := frameSlots_lt_simScale Q
                    calc frameSlots Q * L ≤ simScale Q * L := Nat.mul_le_mul_right L (le_of_lt hsl)
                      _ = simScale Q * L * 1 * 1 := by ring
                      _ ≤ simScale Q * L * 2 ^ h * 1 :=
                        Nat.mul_le_mul_right 1 (Nat.mul_le_mul_left _ h2h)
                  have hdist : simScale Q * L * 2 ^ h * (argsSize args + c_body + 1) =
                      simScale Q * L * 2 ^ h * argsSize args +
                      simScale Q * L * 2 ^ h * c_body + simScale Q * L * 2 ^ h * 1 := by ring
                  omega
                have hmul_slots : frameSlots Q * L < 2 ^ w := by omega
                have hhp_new_w : hp_new < 2 ^ w := by omega
                set st₂ : State :=
                  { st₁ with mem := Function.update st₁.mem (ctrl + 1) hp_new }
                have hs_hp : Runs w p ω
                    (.store (.reg 4) (.bin .add (.reg rCallee) (.bin .mul (.const (frameSlots Q)) (.reg 5))))
                    st₁ .normal st₂ 7 :=
                  runs_store_iff.mpr ⟨ctrl + 1, hp_new, by simp [Expr.eval, hr4_1],
                    Expr.eval_add (by simp [Expr.eval, hrC_1])
                      (Expr.eval_mul (by simp [Expr.eval, hb.hslots_w])
                        (by simp [Expr.eval, hr5_1]) hmul_slots) hhp_new_w,
                    rfl, rfl, rfl⟩
                have hctrl_ne1 : ctrl ≠ ctrl + 1 := by omega
                have hst2_ctrl : st₂.mem ctrl = st.mem ctrl := by
                  simp only [st₂, st₁]; rw [Function.update_of_ne hctrl_ne1]
                have hst2_inTrie_eq : ∀ q, InTrie st.mem L h L (st.mem ctrl) q → st₂.mem q = st.mem q := by
                  intro q hq
                  have hc1 := (hinv.inTrie_disj q hq).1
                  simp only [st₂, st₁]
                  rw [Function.update_of_ne (by rcases hc1 with h | h <;> omega)]
                have hst2_sub : Subtrie st₂.mem L h hp_old L (st₂.mem ctrl) gst.mem := by
                  rw [hst2_ctrl]; exact subtrie_congr_mem hst2_inTrie_eq hinv.trie.2.1
                have hst2_disj : ∀ q, InTrie st₂.mem L h L (st₂.mem ctrl) q →
                    (q < framePtr ∨ framePtr + frameSlots Q * L ≤ q) ∧
                    (q < hp_old ∨ hp_old + frameSlots Q * L ≤ q) := by
                  intro q hq
                  rw [hst2_ctrl, inTrie_congr_mem L (st.mem ctrl) hst2_inTrie_eq q] at hq
                  exact ⟨(hinv.inTrie_disj q hq).2.2, Or.inl (inTrie_bounds hinv.trie.2.1 q hq).2⟩
                have hst2_reg_lim : ∀ r' < Q.regBound, LimbsAt st₂.mem (framePtr + r' * L) L h (gst.regs r') := by
                  intro r' hr'
                  refine (hinv.reg_limbs r' hr').congr fun q hq1 hq2 => ?_
                  simp only [st₂, st₁]; rw [Function.update_of_ne (by omega)]
                have hr2_2 : st₂.regs 2 = framePtr := by
                  simp only [st₂, st₁]; rw [Function.update_of_ne (by omega), hinv.r2]
                have hr3_2 : st₂.regs 3 = ctrl := by
                  simp only [st₂, st₁]; rw [Function.update_of_ne (by omega), hinv.r3]
                have hr5_2 : st₂.regs 5 = L := hr5_1
                have hr6_2 : st₂.regs 6 = h := by
                  simp only [st₂, st₁]; rw [Function.update_of_ne (by omega), hinv.r6]
                have hr7_2 : st₂.regs 7 = 2 ^ h := by
                  simp only [st₂, st₁]; rw [Function.update_of_ne (by omega), hinv.r7]
                have hrC_2 : st₂.regs rCallee = hp_old := hrC_1
                obtain ⟨st₃, c_ca, hr_ca, hreg_ca, hlim_args, hfr_ca, hc_ca⟩ :=
                  compileCallArgs_runs (ω := ω) hArith hTrie hL1 hh hw2 hw'1 hw'_lh hb.hLh hb.hslots_w
                    hb.hL_w hb.hH_w hb.hH2_w hb.hhp_w (by omega) hfw hhp_new_w hfh (by omega)
                    (by omega) args 0 vs st₂ gst hargs_g hargs_rb hargs_td (by omega)
                    hr2_2 hr3_2 hr5_2 hr6_2 hr7_2 hrC_2 rfl hst2_sub hst2_disj
                    hinv.reg_lt hst2_reg_lim hinv.mem_lt
                have hst3_below_hp : ∀ q, q < hp_old →
                    (q < framePtr + Q.regBound * L ∨ framePtr + frameSlots Q * L ≤ q) →
                    st₃.mem q = st₂.mem q := fun q hq hqf =>
                  hfr_ca q hqf (Or.inl (by omega))
                have hst3_above_args : ∀ q, hp_old + args.length * L ≤ q → st₃.mem q = st₂.mem q := fun q hq =>
                  hfr_ca q (Or.inr (by omega)) (Or.inr (by simpa using hq))
                have hst3_hm1 : st₃.mem (ctrl + 1) = hp_new := by
                  rw [hst3_below_hp (ctrl + 1) (by omega) (Or.inl (by omega))]; simp [st₂, st₁]
                have hst3_hm2 : st₃.mem (ctrl + 2) = L := by
                  rw [hst3_below_hp (ctrl + 2) (by omega) (Or.inl (by omega))]
                  simp [st₂, st₁, hinv.mem2]
                have hst3_hm3 : st₃.mem (ctrl + 3) = h := by
                  rw [hst3_below_hp (ctrl + 3) (by omega) (Or.inl (by omega))]
                  simp [st₂, st₁, hinv.mem3]
                have hst3_hm4 : st₃.mem (ctrl + 4) = 2 ^ h := by
                  rw [hst3_below_hp (ctrl + 4) (by omega) (Or.inl (by omega))]
                  simp [st₂, st₁, hinv.mem4]
                have hst3_inTrie_eq : ∀ q, InTrie st.mem L h L (st.mem ctrl) q → st₃.mem q = st.mem q := by
                  intro q hq
                  have h1 := (inTrie_bounds hinv.trie.2.1 q hq).2
                  have h2 := (hinv.inTrie_disj q hq).2.2
                  rw [hst3_below_hp q h1 (by rcases h2 with h | h <;> [exact Or.inl (by omega); exact Or.inr h])]
                  exact hst2_inTrie_eq q hq
                have hst3_ctrl : st₃.mem ctrl = st.mem ctrl := by
                  rw [hst3_below_hp ctrl (by omega) (Or.inl (by omega)), hst2_ctrl]
                have hst3_sub : Subtrie st₃.mem L h hp_new L (st₃.mem ctrl) gst.mem := by
                  rw [hst3_ctrl]
                  exact subtrie_mono_hp (by omega : hp_old ≤ hp_new) (subtrie_congr_mem hst3_inTrie_eq hinv.trie.2.1)
                have hst3_zero : ZeroFrom st₃.mem hp_new := by
                  intro q hq
                  have h1 : hp_old + args.length * L ≤ q := by
                    have := slot_mul_le_mul (by omega : args.length ≤ frameSlots Q) (L := L); omega
                  rw [hst3_above_args q h1]
                  simp only [st₂, st₁]; rw [Function.update_of_ne (by omega)]
                  exact hinv.trie.2.2 q (by omega)
                have hst3_inTrie_disj : ∀ q, InTrie st₃.mem L h L (st₃.mem ctrl) q →
                    (q < ctrl ∨ ctrl + 5 ≤ q) ∧ (q < framePtr + r * L ∨ framePtr + r * L + L ≤ q) ∧
                    (q < hp_old ∨ hp_old + frameSlots Q * L ≤ q) := by
                  intro q hq
                  rw [hst3_ctrl, inTrie_congr_mem L (st.mem ctrl) hst3_inTrie_eq q] at hq
                  have hd := hinv.inTrie_disj q hq
                  have hbnd := inTrie_bounds hinv.trie.2.1 q hq
                  refine ⟨hd.1, ?_, Or.inl hbnd.2⟩
                  rcases hd.2.2 with hlt | hge
                  · exact Or.inl (by omega)
                  · exact Or.inr (by omega)
                have hvs_lt : ∀ v' ∈ vs, v' < 2 ^ w' := evalArgs_lt_two_pow
                  (fun r' hr' => hinv.reg_lt r' (lt_of_lt_of_le hr' hargs_rb)) hinv.mem_lt hargs_g
                have hcal_reg_lt : ∀ k < Q.regBound, (startState vs gst.mem gst.pos).regs k < 2 ^ w' := by
                  intro k _
                  simp only [startState]
                  by_cases hk : k < vs.length
                  · rw [List.getD_eq_getElem _ _ hk]; exact hvs_lt _ (List.getElem_mem hk)
                  · rw [List.getD_eq_default _ _ (Nat.not_lt.mp hk)]; exact Nat.two_pow_pos _
                have hcal_reg_lim : ∀ k < Q.regBound,
                    LimbsAt st₃.mem (hp_old + k * L) L h ((startState vs gst.mem gst.pos).regs k) := by
                  intro k _
                  simp only [startState]
                  by_cases hk : k < vs.length
                  · rw [List.getD_eq_getElem _ _ hk]; simpa using hlim_args k hk
                  · rw [List.getD_eq_default _ _ (Nat.not_lt.mp hk)]
                    refine limbsAt_zero_iff.mpr (WordRAM.listAt_replicate.mpr fun i hi => ?_)
                    have hq1 : hp_old + args.length * L ≤ hp_old + k * L + i := by
                      have := slot_mul_le_mul (by omega : args.length ≤ k) (L := L); omega
                    rw [hst3_above_args _ hq1]
                    simp only [st₂, st₁]; rw [Function.update_of_ne (by omega)]
                    exact hinv.trie.2.2 _ (by omega)
                have hbody_stmt : ∀ hinvC : SimFrameInv w w' L h Q ctrl hp_old (framePtr + r * L)
                    { mem := st₃.mem, regs := procEntryRegs ctrl (framePtr + r * L) hp_old L h, pos := st₃.pos }
                    (startState vs gst.mem gst.pos),
                    CompileStmtPost w w' L h base p Q ω 0 body ctrl hp_old (framePtr + r * L)
                    { mem := st₃.mem, regs := procEntryRegs ctrl (framePtr + r * L) hp_old L h, pos := st₃.pos }
                    o₁ gst₁ c_body :=
                  fun hinvC => ih fuel (Nat.lt_succ_self fuel) body 0 ctrl hp_old (framePtr + r * L)
                    { mem := st₃.mem, regs := procEntryRegs ctrl (framePtr + r * L) hp_old L h, pos := st₃.pos }
                    (startState vs gst.mem gst.pos) o₁ gst₁ c_body hbody_g hbody_rb hbody_td hinvC
                    (by dsimp only; rw [hst3_hm1]; exact hhp_new_lt)
                obtain ⟨st₄, c_proc, hr_proc, hc_proc, hhp4_lo, hhp4_hi, hlim_ret, ho1_lt, htrie₄,
                    hin4_sub, hin4_disj, hmem4_lt, hfr₄⟩ :=
                  compileProc_from_stmt (pos₀ := st₃.pos) (mem₀ := st₃.mem) hComp hL1 hh hw2 hw'1
                    hst3_hm2 hst3_hm3 hst3_hm4 (by omega) (by omega) (Or.inr (by omega)) (by omega)
                    ⟨by rw [hst3_hm1]; have := hinv.trie.1; omega, by rw [hst3_hm1]; exact hst3_sub,
                      by rw [hst3_hm1]; exact hst3_zero⟩
                    hst3_inTrie_disj hcal_reg_lt hcal_reg_lim hinv.mem_lt hc_body_pos
                    (by rw [hst3_hm1]; exact hhp_new_lt) hbody_stmt
                rw [hst3_hm1] at hhp4_lo hhp4_hi hfr₄
                have r0_3 : st₃.regs 0 = ctrl := by
                  rw [hreg_ca 0 (by omega)]; simp only [st₂, st₁]
                  rw [Function.update_of_ne (by omega), hinv.r0]
                have r2_3 : st₃.regs 2 = framePtr := by
                  rw [hreg_ca 2 (by omega)]; simp only [st₂, st₁]
                  rw [Function.update_of_ne (by omega), hinv.r2]
                have r5_3 : st₃.regs 5 = L := by
                  rw [hreg_ca 5 (by omega)]; simp only [st₂, st₁]
                  rw [Function.update_of_ne (by omega), hinv.r5]
                have hrC_3 : st₃.regs rCallee = hp_old := by rw [hreg_ca rCallee (by omega), hrC_2]
                have hr_eval_3 : (slotAddr 2 r).eval w st₃ = some (framePtr + r * L) :=
                  eval_slotAddr r2_3 r5_3 hr_slots hb.hslots_w hb.hL_w hfw
                have hcall_args : evalArgs w st₃ [.reg 0, slotAddr 2 r, .reg rCallee] =
                    some [ctrl, framePtr + r * L, hp_old] :=
                  evalArgs_cons (by eval_expr) (evalArgs_cons hr_eval_3
                    (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))
                have hproc_at := compileProc_procs_at hComp hf_proc
                set st₅ : State := { st₄ with regs := Function.update st₃.regs 8 0 }
                have hr_call : Runs w p ω (.call 8 (base + 21 + f) [.reg 0, slotAddr 2 r, .reg rCallee])
                    st₃ .normal st₅ (argsSize [.reg 0, slotAddr 2 r, .reg rCallee] + c_proc + 1) :=
                  runs_call_iff.mpr ⟨[ctrl, framePtr + r * L, hp_old],
                    compileProc Q (base + 1) (base + 19) (base + 21) body, .returned 0, st₄, c_proc,
                    hcall_args, hproc_at, hr_proc, rfl, rfl, rfl⟩
                have hr_comb : Runs w p ω
                    (compileStmt Q (base + 1) (base + 19) (base + 21) depth (.call r f args))
                    st .normal st₅ (3 + (7 + (c_ca + _ + 1) + 1) + 1) :=
                  runs_seq_iff.mpr (Or.inr ⟨st₁, 3, _, ha_rc,
                    runs_seq_iff.mpr (Or.inr ⟨st₂, 7, _, hs_hp,
                      runs_seq_iff.mpr (Or.inr ⟨st₃, c_ca, _, hr_ca, hr_call, rfl⟩), rfl⟩), rfl⟩)
                have hregs₅ : ∀ r' < 16 + depth, r' ≠ 8 → st₅.regs r' = st.regs r' := fun r' hr' hd => by
                  dsimp only [st₅]; rw [Function.update_of_ne hd, hreg_ca r' hd]
                  simp only [st₂, st₁]; rw [Function.update_of_ne (by omega)]
                have hin5_sub : ∀ q, InTrie st₅.mem L h L (st₅.mem ctrl) q →
                    InTrie st.mem L h L (st.mem ctrl) q ∨
                    (st.mem (ctrl + 1) ≤ q ∧ q < st₅.mem (ctrl + 1)) := by
                  intro q hq
                  dsimp only [st₅] at hq ⊢
                  rcases hin4_sub q hq with hq3 | ⟨hlo, hhi⟩
                  · rw [hst3_ctrl, inTrie_congr_mem L (st.mem ctrl) hst3_inTrie_eq q] at hq3
                    exact Or.inl hq3
                  · exact Or.inr ⟨by omega, hhi⟩
                have hin5_disj : ∀ q, InTrie st₅.mem L h L (st₅.mem ctrl) q →
                    (q < ctrl ∨ ctrl + 5 ≤ q) ∧ (q < retDst ∨ retDst + L ≤ q) ∧
                    (q < framePtr ∨ framePtr + frameSlots Q * L ≤ q) := by
                  intro q hq
                  rcases hin5_sub q hq with hq0 | ⟨hlo, _⟩
                  · exact hinv.inTrie_disj q hq0
                  · omega
                have hfr5 : ∀ q, q < st.mem (ctrl + 1) → q ≠ ctrl → q ≠ ctrl + 1 →
                    ¬ InTrie st.mem L h L (st.mem ctrl) q →
                    (q < retDst ∨ retDst + L ≤ q) →
                    (q < framePtr ∨ framePtr + frameSlots Q * L ≤ q) →
                    st₅.mem q = st.mem q := by
                  intro q hq hqc0 hqc1 hqi hqr hqf
                  have hqi3 : ¬ InTrie st₃.mem L h L (st₃.mem ctrl) q := by
                    rw [hst3_ctrl, inTrie_congr_mem L (st.mem ctrl) hst3_inTrie_eq q]; exact hqi
                  have hqr_c : q < framePtr + r * L ∨ framePtr + r * L + L ≤ q := by
                    rcases hqf with hlt | hge
                    · exact Or.inl (by omega)
                    · exact Or.inr (by omega)
                  have hq_c : q < hp_old ∨ hp_old + frameSlots Q * L ≤ q := Or.inl hq
                  dsimp only [st₅]
                  rw [hfr₄ q (by omega) hqc0 hqc1 hqi3 hqr_c hq_c]
                  rw [hst3_below_hp q hq (by rcases hqf with hlt | hge <;> [exact Or.inl (by omega); exact Or.inr hge])]
                  simp only [st₂, st₁]; rw [Function.update_of_ne hqc1]
                have hinv₅ : SimFrameInv w w' L h Q ctrl framePtr retDst st₅
                    { gst₁ with regs := Function.update gst.regs r o₁.value } :=
                  ⟨by rw [hregs₅ 0 (by omega) (by omega), hinv.r0],
                   by rw [hregs₅ 1 (by omega) (by omega), hinv.r1],
                   by rw [hregs₅ 2 (by omega) (by omega), hinv.r2],
                   by rw [hregs₅ 3 (by omega) (by omega), hinv.r3],
                   by rw [hregs₅ 4 (by omega) (by omega), hinv.r4],
                   by rw [hregs₅ 5 (by omega) (by omega), hinv.r5],
                   by rw [hregs₅ 6 (by omega) (by omega), hinv.r6],
                   by rw [hregs₅ 7 (by omega) (by omega), hinv.r7],
                   by rw [hinv.ctrl_mem_eq_of_frame (by omega) (by omega) hfr5, hinv.mem2],
                   by rw [hinv.ctrl_mem_eq_of_frame (by omega) (by omega) hfr5, hinv.mem3],
                   by rw [hinv.ctrl_mem_eq_of_frame (by omega) (by omega) hfr5, hinv.mem4],
                   hcf, hrf, hinv.ret_disj_ctrl,
                   by dsimp only [st₅]; omega,
                   htrie₄, hin5_disj,
                   fun r' hr' => by
                     dsimp only
                     by_cases hre : r' = r
                     · subst hre; rw [Function.update_self]; exact ho1_lt
                     · rw [Function.update_of_ne hre]; exact hinv.reg_lt r' hr',
                   fun r' hr' => by
                     dsimp only
                     by_cases hre : r' = r
                     · subst hre; rw [Function.update_self]; exact hlim_ret
                     · rw [Function.update_of_ne hre]
                       refine (hinv.reg_limbs r' hr').congr fun q hq1 hq2 => ?_
                       have hq_lt : q < framePtr + Q.regBound * L := by
                         have := slot_end_le_frame hr' (L := L); omega
                       have hq_hp : q < hp_old := by
                         have := slot_end_le_frame (by omega : r' < frameSlots Q) (L := L); omega
                       have hq_c : q ≠ ctrl ∧ q ≠ ctrl + 1 := by omega
                       have hq_in3 : ¬ InTrie st₃.mem L h L (st₃.mem ctrl) q := by
                         rw [hst3_ctrl, inTrie_congr_mem L (st.mem ctrl) hst3_inTrie_eq q]
                         intro hin
                         rcases (hinv.inTrie_disj q hin).2.2 with h | h
                         · omega
                         · have := slot_end_le_frame (by omega : r' < frameSlots Q) (L := L); omega
                       have hq_ret_c : q < framePtr + r * L ∨ framePtr + r * L + L ≤ q := by
                         rcases lt_or_gt_of_ne hre with hlt | hgt
                         · exact Or.inl (by have := slot_end_le_frame hlt (L := L); omega)
                         · exact Or.inr (by have := slot_end_le_frame hgt (L := L); omega)
                       dsimp only [st₅]
                       rw [hfr₄ q (by omega) hq_c.1 hq_c.2 hq_in3 hq_ret_c (Or.inl hq_hp)]
                       rw [hst3_below_hp q hq_hp (Or.inl hq_lt)]
                       simp only [st₂, st₁]; rw [Function.update_of_ne hq_c.2],
                   hmem4_lt⟩
                refine ⟨.normal, st₅, _, hr_comb, ?_, by dsimp only [st₅]; omega, ?_,
                  hregs₅, hin5_sub, hfr5, rfl, hinv₅⟩
                · simp only [slotAddr, Expr.size, argsSize]
                  have h850 : 850 * L * w' * argsSize args ≤ simScale Q * L * w' * argsSize args :=
                    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega)))
                  have h100 : 100 + 80 * L * w' ≤ simScale Q * L * w' := by
                    have : 180 * (L * w') ≤ simScale Q * (L * w') := Nat.mul_le_mul_right _ (by omega)
                    have : 100 ≤ 100 * (L * w') := Nat.le_mul_of_pos_right 100 h1w'
                    have hS' : simScale Q * (L * w') = simScale Q * L * w' := by ring
                    have h80' : 80 * (L * w') = 80 * L * w' := by ring
                    omega
                  have hdist : simScale Q * L * w' * (argsSize args + c_body + 1) =
                      simScale Q * L * w' * argsSize args + simScale Q * L * w' * c_body +
                      simScale Q * L * w' := by ring
                  omega
                · have hSL : frameSlots Q * L ≤ simScale Q * L * 2 ^ h * 1 := by
                    have h2h : 1 ≤ 2 ^ h := Nat.one_le_pow h 2 (by norm_num)
                    have hsl := frameSlots_lt_simScale Q
                    calc frameSlots Q * L ≤ simScale Q * L := Nat.mul_le_mul_right L (le_of_lt hsl)
                      _ = simScale Q * L * 1 * 1 := by ring
                      _ ≤ simScale Q * L * 2 ^ h * 1 :=
                        Nat.mul_le_mul_right 1 (Nat.mul_le_mul_left _ h2h)
                  have hdist : simScale Q * L * 2 ^ h * (argsSize args + c_body + 1) =
                      simScale Q * L * 2 ^ h * argsSize args +
                      simScale Q * L * 2 ^ h * c_body + simScale Q * L * 2 ^ h * 1 := by ring
                  dsimp only [st₅]; omega
        | ret e =>
          simp only [exec] at h_exec
          cases he : e.eval w' gst with
          | none => simp [he] at h_exec
          | some u =>
            simp only [he, Option.some.injEq, Prod.mk.injEq] at h_exec
            rcases h_exec with ⟨rfl, rfl, rfl⟩
            have he_rb : e.regBound ≤ Q.regBound := by simp [Stmt.regBound] at hs_rb; omega
            have he_td : Q.regBound + 1 + exprTempDepth e ≤ frameSlots Q := by
              simp only [stmtTempDepth, frameSlots] at hs_td ⊢; omega
            have hu_lt : u < 2 ^ w' := expr_eval_lt_two_pow
              (fun r hr => hinv.reg_lt r (lt_of_lt_of_le hr he_rb)) hinv.mem_lt he
            obtain ⟨st₁, c₁, hr₁, hreg₁, hlim₁, hfr₁, hc₁⟩ :=
              compileExpr_runs (ω := ω) hArith hTrie hL1 hh hw2 hw'1 hw'_lh hb.hLh hb.hslots_w
                hb.hL_w hb.hH_w hb.hH2_w hb.hhp_w (by omega) hfw e Q.regBound
                (Q.regBound + 1) u st gst he he_rb (le_refl _) (by omega) he_td
                hinv.r2 hinv.r3 hinv.r5 hinv.r6 hinv.r7 rfl hinv.trie.2.1
                (fun q hq => (hinv.inTrie_disj q hq).2.2) hinv.reg_lt hinv.reg_limbs hinv.mem_lt
            have r1_1 : st₁.regs 1 = retDst := by rw [hreg₁ 1 (by omega), hinv.r1]
            have r2_1 : st₁.regs 2 = framePtr := by rw [hreg₁ 2 (by omega), hinv.r2]
            have r5_1 : st₁.regs 5 = L := by rw [hreg₁ 5 (by omega), hinv.r5]
            have hsrc_eval : (slotAddr 2 Q.regBound).eval w st₁ = some (framePtr + Q.regBound * L) :=
              eval_slotAddr r2_1 r5_1 hQ_slots hb.hslots_w hb.hL_w hfw
            have hargs_cp : evalArgs w st₁ [slotAddr 2 Q.regBound, .reg 1, .reg 5] =
                some [framePtr + Q.regBound * L, retDst, L] :=
              evalArgs_cons hsrc_eval (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))
            have hsrc_end : framePtr + Q.regBound * L + L < 2 ^ w := by
              have := slot_end_le_frame hQ_slots (L := L); omega
            have hpre_cp : (mwCopyContract w).pre [framePtr + Q.regBound * L, retDst, L] st₁.mem :=
              ⟨framePtr + Q.regBound * L, retDst, L, rfl, hb.hw1, hsrc_end, hb.hret_w,
                Or.inl (by omega)⟩
            obtain ⟨st₂, c₂, _, hcall, hpost₂, _, hother₂, hc₂⟩ :=
              runs_call_of_meetsContract (r := 8) (mwCopy_of_arithModule hArith) hargs_cp
                (by
                  intro a ha
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
                  rcases ha with rfl | rfl | rfl <;> omega)
                hpre_cp ω
            rcases hpost₂ with ⟨_, _, _, heq₂, _, hcp₂, hfr₂⟩
            simp only [List.cons.injEq, and_true] at heq₂
            rcases heq₂ with ⟨rfl, rfl, rfl⟩
            have hret_stmt : Runs w p ω (.ret (.const 0)) st₂ (.returned 0) st₂ 2 :=
              runs_ret_iff.mpr ⟨0, by simp [Expr.eval], rfl, rfl, rfl⟩
            have hr_comb : Runs w p ω
                (compileStmt Q (base + 1) (base + 19) (base + 21) depth (.ret e))
                st (.returned 0) st₂ (c₁ + (c₂ + 2 + 1) + 1) :=
              runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂ + 2 + 1, hr₁,
                runs_seq_iff.mpr (Or.inr ⟨st₂, c₂, 2, hcall, hret_stmt, rfl⟩), rfl⟩)
            have hmem_fr : ∀ q, (q < framePtr + Q.regBound * L ∨ framePtr + frameSlots Q * L ≤ q) →
                (q < retDst ∨ retDst + L ≤ q) → st₂.mem q = st.mem q := by
              intro q hqb hqr
              rw [hfr₂ q hqr]
              rcases hqb with hlt | hge
              · exact hfr₁ q (Or.inl hlt) (Or.inl (by
                  have := slot_mul_le_mul (by omega : Q.regBound ≤ Q.regBound + 1) (L := L); omega))
              · have h1 : framePtr + Q.regBound * L + L ≤ framePtr + frameSlots Q * L := by
                  have := slot_end_le_frame hQ_slots (L := L); omega
                have h2 : framePtr + (Q.regBound + 1 + exprTempDepth e) * L ≤ framePtr + frameSlots Q * L := by
                  have := slot_mul_le_mul he_td (L := L); omega
                exact hfr₁ q (Or.inr (by omega)) (Or.inr (by omega))
            have hhp₂_eq : st₂.mem (ctrl + 1) = st.mem (ctrl + 1) := by
              refine hmem_fr (ctrl + 1) (Or.inl (by omega)) ?_
              rcases hinv.ret_disj_ctrl with h | h <;> [exact Or.inr (by omega); exact Or.inl (by omega)]
            have hctrl₂_eq : st₂.mem ctrl = st.mem ctrl := by
              refine hmem_fr ctrl (Or.inl (by omega)) ?_
              rcases hinv.ret_disj_ctrl with h | h <;> [exact Or.inr (by omega); exact Or.inl (by omega)]
            have hno_above : ∀ q, st.mem (ctrl + 1) ≤ q → st₂.mem q = st.mem q := fun q hq =>
              hmem_fr q (Or.inr (by omega)) (Or.inr (by omega))
            have hno_inTrie : ∀ q, InTrie st.mem L h L (st.mem ctrl) q → st₂.mem q = st.mem q := by
              intro q hq
              have hd := hinv.inTrie_disj q hq
              refine hmem_fr q ?_ hd.2.1
              rcases hd.2.2 with hlt | hge
              · exact Or.inl (by omega)
              · exact Or.inr hge
            have htrie₂ : TrieRep st₂.mem L h (st₂.mem (ctrl + 1)) (st₂.mem ctrl) gst.mem :=
              ⟨by rw [hhp₂_eq]; exact hinv.trie.1,
                by rw [hctrl₂_eq, hhp₂_eq]; exact subtrie_congr_mem hno_inTrie hinv.trie.2.1,
                by rw [hhp₂_eq]; intro q hq; rw [hno_above q hq]; exact hinv.trie.2.2 q hq⟩
            have hin_eq : ∀ q, InTrie st₂.mem L h L (st₂.mem ctrl) q ↔
                InTrie st.mem L h L (st.mem ctrl) q := by
              rw [hctrl₂_eq]; exact inTrie_congr_mem L (st.mem ctrl) hno_inTrie
            refine ⟨.returned 0, st₂, _, hr_comb, ?_, by rw [hhp₂_eq],
              by rw [hhp₂_eq]; exact Nat.le_add_right _ _,
              fun r' _ hd => (hother₂ r' hd).trans (hreg₁ r' hd),
              fun q hq => Or.inl ((hin_eq q).mp hq), ?_,
              rfl, hu_lt,
              limbsAt_iff_pointwise.mpr ⟨hlim₁.lt_pow, fun i hi => by
                rw [hcp₂ i hi]; exact hlim₁.getElem hi⟩,
              htrie₂, fun q hq => hinv.inTrie_disj q ((hin_eq q).mp hq), hinv.mem_lt⟩
            · dsimp only [mwCopyContract] at hc₂
              simp only [slotAddr, Expr.size, argsSize] at hc₂
              have h50 : 17 * L + 25 ≤ 50 * L * w' := mul_Lw'_bound hL1 hw'1 (by omega)
              have h800 : 800 * L * w' * e.size ≤ simScale Q * L * w' * e.size :=
                Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega)))
              have h50S : 50 * L * w' ≤ simScale Q * L * w' :=
                Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
              have hdist : simScale Q * L * w' * (e.size + 1) =
                  simScale Q * L * w' * e.size + simScale Q * L * w' := by ring
              omega
            · intro q _ _ _ _ hqr hqf
              rcases hqf with hlt | hge
              · exact hmem_fr q (Or.inl (by omega)) hqr
              · exact hmem_fr q (Or.inr hge) hqr
  exact fun fuel => hMain fuel

end MinCostFlow.WideWord
