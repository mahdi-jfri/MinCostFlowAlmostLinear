module

public import MinCostFlow.Spanner.ProgTask2StepsMiddleBounds

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## Word-RAM `writeVerts` `forRange` loop spec for `t2MiddleEdgeBody` -/

lemma t2Middle_writeVerts_forRange {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {inp : Task2Input} {mem₀ : ℕ → ℕ} (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx)
    {g₀ : T2Ghost impl.pathDS} {ci hCurNew arena0 cVertsPtr u_loc v_loc : ℕ} {P_sub : Walk}
    (hci : ci < ctx.wd.comps.length)
    (hcw_sub : P_sub.IsWalk (ctx.wd.comps[ci]'hci).J_sub u_loc v_loc)
    (hPsub_nd : P_sub.verts.Nodup)
    (hy_sub : ∀ y ∈ P_sub.verts, y < (ctx.wd.comps[ci]'hci).J_sub.n)
    (mem : ℕ → ℕ)
    (hwk : WalkAt mem g₀.hCur P_sub) (hz : WordRAM.ZeroFrom mem hCurNew)
    (hCur_le : g₀.hCur ≤ hCurNew) (hCur_hi : hCurNew ≤ Task2Input.maxHeapEnd impl inp)
    (hMax_w : Task2Input.maxHeapEnd impl inp + 3 ≤ Task2Input.maxWordBound impl inp)
    (hmwb : Task2Input.maxWordBound impl inp < 2 ^ w) (hw1 : 1 < 2 ^ w)
    (hcV_list : ListAt mem cVertsPtr (ctx.wd.comps[ci]'hci).verts)
    (hcV_lt : cVertsPtr + (ctx.wd.comps[ci]'hci).verts.length ≤ ctx.wInp.prep.hEnd)
    (hEnd_lo : ctx.wInp.prep.hEnd ≤ stc.nodesEnd)
    (har_lo : stc.nodesEnd ≤ arena0)
    (har_hi : arena0 + 2 + P_sub.verts.length + P_sub.edges.length ≤ stc.dsBaseAddr)
    (hds_hCur : stc.dsBaseAddr ≤ g₀.hCur)
    (hds_hi : stc.dsBaseAddr ≤ Task2Input.maxHeapEnd impl inp)
    (hr_init : ℕ → ℕ)
    (hr8 : hr_init 8 = cVertsPtr) (hr17 : hr_init 17 = g₀.hCur)
    (hr18 : hr_init 18 = arena0) (hr19 : hr_init 19 = P_sub.verts.length)
    (pos₀ : ℕ) (ω : ℕ → Bool) :
    let c := ctx.wd.comps[ci]'hci
    let P_J := liftJSubWalk c P_sub
    let body :=
      Stmt.assign 23 (t2Ld (.reg 17) (t2Add (.const 1) (.reg 22))) ;;
      t2St (.reg 18) (t2Add (.const 1) (.reg 22)) (t2Ld (.reg 8) (.reg 23))
    ∃ st' c_run,
      Runs w p ω (forRange 22 (.const 0) (.reg 19) body) ⟨mem, hr_init, pos₀⟩ .normal st' c_run ∧
      (∀ r ≤ 21, st'.regs r = hr_init r) ∧
      (∀ a, ¬(arena0 + 1 ≤ a ∧ a < arena0 + 1 + P_sub.verts.length) → st'.mem a = mem a) ∧
      (∀ j < P_sub.verts.length, st'.mem (arena0 + 1 + j) = P_J.verts.getD j 0) ∧
      c_run ≤ P_sub.verts.length * 27 + 7 := by
  intro c P_J body
  have hwk_bd := t2_walkAt_add_le hcw_sub hPsub_nd hwk hz hCur_le
  have hprops := ctx.hw_okW.comp_props ci hci
  rcases hprops with ⟨_, _, _, _, hverts_c, hc_Jn, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  have hc_vlen : c.verts.length = c.J_sub.n := by
    rw [hverts_c, vertsOf, Finset.length_sort, ← hc_Jn]
  have hlen_w : P_sub.verts.length < 2 ^ w := by omega
  let P0 : State → Prop := fun st =>
    (∀ r ≤ 21, st.regs r = hr_init r) ∧
    (∀ a, ¬(arena0 + 1 ≤ a ∧ a < arena0 + 1 + P_sub.verts.length) → st.mem a = mem a)
  let Inv : ℕ → State → Prop := fun j st =>
    (∀ r ≤ 21, st.regs r = hr_init r) ∧ st.regs 22 = j ∧
    (∀ a, ¬(arena0 + 1 ≤ a ∧ a < arena0 + 1 + P_sub.verts.length) → st.mem a = mem a) ∧
    (∀ k < j, st.mem (arena0 + 1 + k) = P_J.verts.getD k 0)
  have htrip : Triple w p P0 (forRange 22 (.const 0) (.reg 19) body)
      (normalPost (Inv P_sub.verts.length)) (fun _ => P_sub.verts.length * 27 + 7) := by
    have hfor := Triple.forRange_const (w := w) (p := p) (P := P0) (r := 22) (lo := .const 0)
      (hi := .reg 19) (body := body) (Inv := Inv) (stepBound := 18) (loVal := 0)
      (hiVal := P_sub.verts.length) (Nat.zero_le _) hw1 (fun _ => hlen_w)
      (fun st hP0 => by
        refine ⟨Expr.eval_const (by omega), ?_⟩
        rcases hP0 with ⟨hr, hagr⟩
        refine ⟨fun r hr_le => ?_, by simp, hagr, fun _ hk => by omega⟩
        dsimp only; rw [Function.update_of_ne (by omega)]; exact hr r hr_le)
      (fun j _ _ _ hI => hI.2.1)
      (fun j st _ _ hI => Expr.eval_reg_of_eq ((hI.1 19 (by omega)).trans hr19))
      fun j _ hj => by
        have hv_pos : P_sub.verts.length ≥ 1 := by omega
        have hsrc_lt : g₀.hCur + 1 + j < hCurNew := (hwk_bd.2.2.1 hv_pos).2 j hj
        have hsrc_w : g₀.hCur + (1 + j) < 2 ^ w := by omega
        set y := P_sub.verts[j]'hj
        have hy_lt : y < c.J_sub.n := hy_sub y (List.getElem_mem hj)
        have hy_vlen : y < (ctx.wd.comps[ci]'hci).verts.length := by
          dsimp only [c] at hy_lt hc_vlen; exact hc_vlen.symm ▸ hy_lt
        have hy_w : y < 2 ^ w := by
          have : (ctx.wd.comps[ci]'hci).verts.length ≤ ctx.wInp.prep.hEnd := by omega
          have : ctx.wInp.prep.hEnd ≤ stc.dsBaseAddr := by omega
          omega
        have hy_src : ∀ st : State, Inv j st → st.mem (g₀.hCur + (1 + j)) = y := fun st hI => by
          rw [hI.2.2.1 _ (by omega), show g₀.hCur + (1 + j) = g₀.hCur + 1 + j by omega]
          exact hwk.verts_listAt j hj
        have hs1 := Triple.assign (w := w) (p := p) (P := Inv j) (r := 23)
          (e := t2Ld (.reg 17) (t2Add (.const 1) (.reg 22))) (val := fun _ => y)
          (Q := fun st₁ => Inv j st₁ ∧ st₁.regs 23 = y)
          (fun st hI => by
            have ha1 := Expr.eval_add (w := w) (Expr.eval_const hw1) (Expr.eval_reg_of_eq hI.2.1) (by omega)
            have ha2 := Expr.eval_add (w := w) (Expr.eval_reg_of_eq ((hI.1 17 (by omega)).trans hr17)) ha1 hsrc_w
            simpa only [t2Ld, hy_src st hI] using Expr.eval_load ha2)
          (fun st hI => by
            rcases hI with ⟨hr, hr22, hagr, hdone⟩
            refine ⟨⟨fun r hr_le => ?_, ?_, hagr, hdone⟩, by simp⟩
            · dsimp only; rw [Function.update_of_ne (by omega)]; exact hr r hr_le
            · dsimp only; rw [Function.update_of_ne (by omega)]; exact hr22)
        have hv_eq : P_J.verts.getD j 0 = c.verts[y]'hy_vlen := by
          have hj_PJ : j < P_J.verts.length := by simpa [P_J, liftJSubWalk] using hj
          rw [List.getD_eq_getElem _ _ hj_PJ]
          simp only [P_J, liftJSubWalk, List.getElem_map]
          exact List.getD_eq_getElem _ _ hy_vlen
        have hcV_src : ∀ st₁ : State, Inv j st₁ ∧ st₁.regs 23 = y →
            st₁.mem (cVertsPtr + y) = c.verts[y]'hy_vlen := fun st₁ ⟨hI, _⟩ => by
          rw [hI.2.2.1 _ (by omega)]
          exact hcV_list y hy_vlen
        have hs2 := Triple.store (w := w) (p := p)
          (P := fun st₁ => Inv j st₁ ∧ st₁.regs 23 = y)
          (a := t2Add (.reg 18) (t2Add (.const 1) (.reg 22)))
          (e := t2Ld (.reg 8) (.reg 23))
          (addr := fun _ => arena0 + (1 + j))
          (val := fun _ => c.verts[y]'hy_vlen)
          (Q := fun st₂ =>
            Inv (j + 1) { st₂ with regs := Function.update st₂.regs 22 (j + 1) } ∧ st₂.regs 22 = j)
          (fun st₁ ⟨hI, _⟩ =>
            Expr.eval_add (w := w) (Expr.eval_reg_of_eq ((hI.1 18 (by omega)).trans hr18))
              (Expr.eval_add (w := w) (Expr.eval_const hw1) (Expr.eval_reg_of_eq hI.2.1) (by omega))
              (by omega))
          (fun st₁ ⟨hI, hr23⟩ => by
            have ha := Expr.eval_add (w := w) (Expr.eval_reg_of_eq ((hI.1 8 (by omega)).trans hr8))
              (Expr.eval_reg_of_eq hr23) (by omega)
            simpa only [t2Ld, hcV_src st₁ ⟨hI, hr23⟩] using Expr.eval_load ha)
          (fun st₁ ⟨hI, _⟩ => by
            rcases hI with ⟨hr, hr22, hagr, hdone⟩
            refine ⟨⟨fun r hr_le => ?_, by simp, fun a ha => ?_, fun k hk => ?_⟩, hr22⟩
            · dsimp only; rw [Function.update_of_ne (by omega)]; exact hr r hr_le
            · dsimp only; rw [Function.update_of_ne (by omega)]; exact hagr a ha
            · dsimp only
              by_cases hkj : k = j
              · subst hkj; rw [show arena0 + 1 + k = arena0 + (1 + k) by omega, Function.update_self, hv_eq]
              · rw [Function.update_of_ne (by omega)]; exact hdone k (by omega))
        exact Triple.seq_normal (T := fun _ => 18) hs1 hs2 fun _ _ _ _ => by
          simp only [Expr.size]; omega
    exact hfor.mono_cost fun _ _ => by simp only [Nat.sub_zero, Expr.size]; omega
  obtain ⟨o, st', c_run, hr, hq, hc⟩ := htrip ⟨mem, hr_init, pos₀⟩ ω ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  cases o with
  | returned _ => exact False.elim hq
  | normal =>
    rcases hq with ⟨hregs, _, hagr, hdone⟩
    exact ⟨st', c_run, hr, hregs, hagr, hdone, by omega⟩

end MinCostFlow.Spanner
