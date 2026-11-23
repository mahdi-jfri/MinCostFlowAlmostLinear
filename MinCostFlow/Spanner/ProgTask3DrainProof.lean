module

public import MinCostFlow.Spanner.ProgTask3StepsBase

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM Cited

/-!
# Verification of `t3DrainQueue` (`selfBase + 2`)

Proves `t3InnerStamp_ptriple`, `t3DrainStep_ptriple`, and `t3DrainQueue_ptriple`.
-/

private lemma T3DrainQueueAt.with_regs {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} {ctx : T3Ctx impl inp mem₀ w} {lay : T3Layout} {rCur : ℕ}
    {Q : List ℕ} {g1 del0 eUpd1 : ℕ} {emb1 : ℕ → Option Walk} {nextU qi : ℕ}
    {d : T3RoundData impl.pathDS} {st : State} {Φ : ℕ} {r' : ℕ → ℕ}
    (h : T3DrainQueueAt ctx lay rCur Q g1 del0 eUpd1 emb1 nextU qi d st Φ) :
    T3DrainQueueAt ctx lay rCur Q g1 del0 eUpd1 emb1 nextU qi d { st with regs := r' } Φ :=
  ⟨h.rCur_pos, h.rCur_le, h.qi_le, h.Q_nd, h.Q_len_le, h.g1_le, h.del_le_eUpd,
    h.eUpd_bound, h.eUpd_W, h.queue_list, h.Q_valid, h.d_emb, h.d_g, h.d_del, h.d_eUpd,
    h.d_nextU, h.staticMem, h.dsArr, h.hCur_lo, h.hCur_bd, h.zero_from, h.eta2_eq, h.getPath_eq,
    h.del_eq, h.econgUpd_eq, h.hCur_eq, h.nextU_eq, h.nextU_bin, h.emb_part, h.emb_j0_cov,
    h.emb_nodup, h.emb_len_W, h.emb_len_real, h.emb_mem, h.econg_cnt_eq, h.econg_le_round,
    h.econg_j0_le, h.wdel_j0, h.wdel_comp, h.wdel_thresh, h.wdel_lt_econg, h.econgUpd_sum,
    h.getPath_cnt_le, h.del_iff_drop, h.vhat_stmp_eq, h.vhat_stmp_le, h.phi_eq⟩

private lemma t3InnerStamp_ptriple {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (hlay : lay = T3Layout.ofCtx ctx)
    {p : Program} {rCur hOld ci : ℕ} (hci : ci < ctx.wd.comps.length)
    {sOldVhat sNewVhat : Finset ℕ} {L : List ℕ} (memInit regsInit : ℕ → ℕ)
    (hsub_old : sOldVhat ⊆ sNewVhat) (_hL_nd : L.Nodup) (hL_fin : L.toFinset = sNewVhat \ sOldVhat)
    (hsub_new : sNewVhat ⊆ Finset.range ctx.wd.comps[ci].W_sub.n) :
    let innerStmt := t3ForRange 17 (.const 0) (.reg 15)
      (Stmt.seq (.assign 18 (t3Ld (.reg 12) (t3Add (.const 1) (.reg 17))))
        (.store (t3Add (.reg 7) (t3Add (.reg 16) (.reg 18))) (.reg 1)))
    let Pre := fun (st : State) (Φ : ℕ) =>
      st.mem = memInit ∧ (∀ r ≤ 16, st.regs r = regsInit r) ∧
      st.regs 1 = rCur ∧ st.regs 7 = lay.vhatStampAddr ∧ st.regs 12 = hOld ∧
      st.regs 15 = L.length ∧ st.regs 16 = vhatBaseW ctx.wd ci ∧
      lay.staticEnd ≤ hOld ∧ hOld + 1 + L.length < 2 ^ w ∧
      WordRAM.SeqAt st.mem hOld L ∧
      (∀ v < ctx.wd.comps[ci].W_sub.n,
        (st.mem (lay.vhatStampAddr + vhatBaseW ctx.wd ci + v) = rCur ↔ v ∈ sOldVhat)) ∧
      (∀ v < ctx.wd.comps[ci].W_sub.n,
        st.mem (lay.vhatStampAddr + vhatBaseW ctx.wd ci + v) ≤ rCur)
    let Post := fun (st : State) (_Φ : ℕ) =>
      (∀ r ≤ 16, st.regs r = regsInit r) ∧
      (∀ a, (a < lay.vhatStampAddr + vhatBaseW ctx.wd ci ∨
          lay.vhatStampAddr + vhatBaseW ctx.wd ci + ctx.wd.comps[ci].W_sub.n ≤ a) →
        st.mem a = memInit a) ∧
      (∀ v < ctx.wd.comps[ci].W_sub.n,
        (st.mem (lay.vhatStampAddr + vhatBaseW ctx.wd ci + v) = rCur ↔ v ∈ sNewVhat)) ∧
      (∀ v < ctx.wd.comps[ci].W_sub.n,
        st.mem (lay.vhatStampAddr + vhatBaseW ctx.wd ci + v) ≤ rCur)
    ∀ st₀ Φ₀ ω, Pre st₀ Φ₀ →
      ∃ o st' c Φ', Runs w p ω innerStmt st₀ o st' c ∧
        pNormalPost Post o st' Φ' ∧ c + Φ' ≤ (L.length * 24 + 7) + Φ₀ := by
  intro innerStmt Pre Post st₀ Φ₀ ω hP0
  have hb := T3Layout.bounds ctx
  have hw1 : 1 < 2 ^ w := ctx.hwokW.1
  have hbase_le_end : lay.vhatStampAddr + vhatBaseW ctx.wd ci + ctx.wd.comps[ci].W_sub.n ≤
      lay.staticEnd := by
    have ha := vhatBaseW_add_le hci
    have hs := vhatBaseW_le_sum (wd := ctx.wd) (ci := ci + 1)
    subst hlay; omega
  let LoopInv : ℕ → State → ℕ → Prop := fun j st Φ =>
    Φ = Φ₀ ∧ (∀ r ≤ 16, st.regs r = regsInit r) ∧
    st.regs 1 = rCur ∧ st.regs 7 = lay.vhatStampAddr ∧ st.regs 12 = hOld ∧
    st.regs 15 = L.length ∧ st.regs 16 = vhatBaseW ctx.wd ci ∧ st.regs 17 = j ∧
    (∀ a, (a < lay.vhatStampAddr + vhatBaseW ctx.wd ci ∨
        lay.vhatStampAddr + vhatBaseW ctx.wd ci + ctx.wd.comps[ci].W_sub.n ≤ a) →
      st.mem a = memInit a) ∧
    (∀ v < ctx.wd.comps[ci].W_sub.n,
      (st.mem (lay.vhatStampAddr + vhatBaseW ctx.wd ci + v) = rCur ↔
        v ∈ sOldVhat ∨ (v ∈ sNewVhat ∧ ∃ t < j, L.getD t 0 = v))) ∧
    (∀ v < ctx.wd.comps[ci].W_sub.n,
      st.mem (lay.vhatStampAddr + vhatBaseW ctx.wd ci + v) ≤ rCur)
  have hL_w : L.length < 2 ^ w := by have := hP0.2.2.2.2.2.2.2.2.1; omega
  have hloop := PTriple.forRange_const (w := w) (p := p) (P := fun st Φ => Pre st Φ ∧ Φ = Φ₀)
    (r := 17) (lo := .const 0) (hi := .reg 15)
    (body := Stmt.seq (.assign 18 (t3Ld (.reg 12) (t3Add (.const 1) (.reg 17))))
      (.store (t3Add (.reg 7) (t3Add (.reg 16) (.reg 18))) (.reg 1)))
    (Inv := LoopInv) 15 0 L.length (Nat.zero_le _) hw1 (fun _ => hL_w)
    (fun st Φ ⟨hP, hΦ⟩ => by
      have hr16 : ∀ r ≤ 16, Function.update st.regs 17 0 r = regsInit r := fun r hr => by
        rw [Function.update_of_ne (by omega)]; exact hP.2.1 r hr
      refine ⟨Expr.eval_const (by omega : 0 < 2 ^ w), hΦ, hr16, ?_, ?_, ?_, ?_, ?_,
        by simp, fun _ _ => hP.1 ▸ rfl, ?_, hP.2.2.2.2.2.2.2.2.2.2.2⟩
      · dsimp only; rw [Function.update_of_ne (by omega)]; exact hP.2.2.1
      · dsimp only; rw [Function.update_of_ne (by omega)]; exact hP.2.2.2.1
      · dsimp only; rw [Function.update_of_ne (by omega)]; exact hP.2.2.2.2.1
      · dsimp only; rw [Function.update_of_ne (by omega)]; exact hP.2.2.2.2.2.1
      · dsimp only; rw [Function.update_of_ne (by omega)]; exact hP.2.2.2.2.2.2.1
      · intro v hv
        rw [hP.2.2.2.2.2.2.2.2.2.2.1 v hv]
        exact ⟨Or.inl, fun h => h.elim id fun ⟨_, t, ht, _⟩ => by omega⟩)
    (fun i st Φ _ _ h => h.2.2.2.2.2.2.2.1)
    (fun i st Φ _ _ h => Expr.eval_reg_of_eq h.2.2.2.2.2.1)
    (fun i hi0 hiL st Φ ω hI => by
      rcases hI with ⟨hΦ, hr16, hr1, hr7, hr12, hr15, hr16v, hr17, hfr, hveq, hvle⟩
      have hj_seq : st.mem (hOld + 1 + i) = L[i]'hiL := by
        have hlt_seq : lay.vhatStampAddr + vhatBaseW ctx.wd ci + ctx.wd.comps[ci].W_sub.n ≤
            hOld + 1 + i := by
          have := hP0.2.2.2.2.2.2.2.1; omega
        rw [hfr _ (Or.inr hlt_seq), ← hP0.1]
        rw [← listAt_getElem hP0.2.2.2.2.2.2.2.2.2.1.2 hiL]
      have hu_mem : (L[i]'hiL) ∈ L.toFinset := List.mem_toFinset.mpr (List.getElem_mem hiL)
      have hu_diff : (L[i]'hiL) ∈ sNewVhat \ sOldVhat := hL_fin ▸ hu_mem
      have hu_n : L[i]'hiL < ctx.wd.comps[ci].W_sub.n :=
        Finset.mem_range.mp (hsub_new (Finset.mem_sdiff.mp hu_diff).1)
      have hhi_ok : 1 + i < 2 ^ w := by have := hP0.2.2.2.2.2.2.2.2.1; omega
      have hadd1 : hOld + (1 + i) < 2 ^ w := by have := hP0.2.2.2.2.2.2.2.2.1; omega
      have hadd2 : vhatBaseW ctx.wd ci + (L[i]'hiL) < 2 ^ w := by subst hlay; omega
      have hadd3 : lay.vhatStampAddr + (vhatBaseW ctx.wd ci + (L[i]'hiL)) < 2 ^ w := by subst hlay; omega
      apply t3_ptriple_of_cps
      refine t3_assign_cps (r := 18)
        (Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq hr12)
          (Expr.eval_add (Expr.eval_const hw1) (Expr.eval_reg_of_eq hr17) hhi_ok) hadd1)) ?_
      rw [show hOld + (1 + i) = hOld + 1 + i by omega, hj_seq]
      let regs1 := Function.update st.regs 18 (L[i]'hiL)
      have hr1_1 : regs1 1 = rCur := by simp [regs1, hr1]
      have hr7_1 : regs1 7 = lay.vhatStampAddr := by simp [regs1, hr7]
      have hr16v_1 : regs1 16 = vhatBaseW ctx.wd ci := by simp [regs1, hr16v]
      have hr18_1 : regs1 18 = L[i]'hiL := Function.update_self _ _ _
      have hev_ea : (t3Add (.reg 7) (t3Add (.reg 16) (.reg 18))).eval w ⟨st.mem, regs1, st.pos⟩ =
          some (lay.vhatStampAddr + (vhatBaseW ctx.wd ci + (L[i]'hiL))) :=
        Expr.eval_add (Expr.eval_reg_of_eq hr7_1)
          (Expr.eval_add (Expr.eval_reg_of_eq hr16v_1) (Expr.eval_reg_of_eq hr18_1) hadd2) hadd3
      have hev_val : (Expr.reg 1).eval w ⟨st.mem, regs1, st.pos⟩ = some rCur :=
        Expr.eval_reg_of_eq hr1_1
      refine ⟨.normal, ⟨Function.update st.mem (lay.vhatStampAddr + (vhatBaseW ctx.wd ci + (L[i]'hiL))) rCur,
        regs1, st.pos⟩, 7, Φ, runs_store_iff.mpr ⟨_, rCur, hev_ea, hev_val, rfl, rfl, rfl⟩,
        ⟨?_, by simp [regs1, hr17]⟩, by simp [Expr.size, t3Ld, t3Add]⟩
      have hr16_2 : ∀ r ≤ 16, Function.update regs1 17 (i + 1) r = regsInit r := fun r hr => by
        dsimp only [regs1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hr16 r hr
      refine ⟨hΦ, hr16_2, ?_, ?_, ?_, ?_, ?_, by simp, ?_, ?_, ?_⟩
      · exact (hr16_2 1 (by omega)).trans ((hP0.2.1 1 (by omega)).symm.trans hP0.2.2.1)
      · exact (hr16_2 7 (by omega)).trans ((hP0.2.1 7 (by omega)).symm.trans hP0.2.2.2.1)
      · exact (hr16_2 12 (by omega)).trans ((hP0.2.1 12 (by omega)).symm.trans hP0.2.2.2.2.1)
      · exact (hr16_2 15 (by omega)).trans ((hP0.2.1 15 (by omega)).symm.trans hP0.2.2.2.2.2.1)
      · exact (hr16_2 16 (by omega)).trans ((hP0.2.1 16 (by omega)).symm.trans hP0.2.2.2.2.2.2.1)
      · intro a ha
        have hne : a ≠ lay.vhatStampAddr + (vhatBaseW ctx.wd ci + (L[i]'hiL)) := by omega
        dsimp only; rw [Function.update_of_ne hne]
        exact hfr a ha
      · intro v hv
        dsimp only
        by_cases hvi : v = L[i]'hiL
        · subst hvi
          rw [show lay.vhatStampAddr + vhatBaseW ctx.wd ci + L[i] =
            lay.vhatStampAddr + (vhatBaseW ctx.wd ci + L[i]) by omega, Function.update_self]
          exact ⟨fun _ => Or.inr ⟨(Finset.mem_sdiff.mp hu_diff).1, i, by omega,
            by rw [List.getD_eq_getElem _ _ hiL]⟩, fun _ => rfl⟩
        · have hne : lay.vhatStampAddr + vhatBaseW ctx.wd ci + v ≠
              lay.vhatStampAddr + (vhatBaseW ctx.wd ci + L[i]) := by omega
          rw [Function.update_of_ne hne, hveq v hv]
          constructor
          · rintro (h | ⟨hs, t, ht, hget⟩)
            · exact Or.inl h
            · exact Or.inr ⟨hs, t, by omega, hget⟩
          · rintro (h | ⟨hs, t, ht, hget⟩)
            · exact Or.inl h
            · right; refine ⟨hs, t, ?_, hget⟩
              by_cases hti : t = i
              · subst hti; rw [List.getD_eq_getElem _ _ hiL] at hget; exact absurd hget.symm hvi
              · omega
      · intro v hv
        dsimp only
        by_cases hvi : v = L[i]'hiL
        · subst hvi
          rw [show lay.vhatStampAddr + vhatBaseW ctx.wd ci + L[i] =
            lay.vhatStampAddr + (vhatBaseW ctx.wd ci + L[i]) by omega, Function.update_self]
        · have hne : lay.vhatStampAddr + vhatBaseW ctx.wd ci + v ≠
              lay.vhatStampAddr + (vhatBaseW ctx.wd ci + L[i]) := by omega
          rw [Function.update_of_ne hne]
          exact hvle v hv)
  obtain ⟨o, st', c, Φ', hr, hq, hc⟩ := hloop st₀ Φ₀ ω ⟨hP0, rfl⟩
  refine ⟨o, st', c, Φ', hr, ?_, ?_⟩
  · cases o with
    | returned _ => exact False.elim hq
    | normal =>
      rcases hq with ⟨_, hr16, _, _, _, _, _, _, hfr, hveq, hvle⟩
      refine ⟨hr16, hfr, fun v hv => ?_, hvle⟩
      rw [hveq v hv]
      constructor
      · rintro (h | ⟨hs, _⟩)
        · exact hsub_old h
        · exact hs
      · intro hv_new
        by_cases hv_old : v ∈ sOldVhat
        · exact Or.inl hv_old
        · right
          refine ⟨hv_new, ?_⟩
          have hv_L : v ∈ L := by
            rw [← List.mem_toFinset, hL_fin, Finset.mem_sdiff]; exact ⟨hv_new, hv_old⟩
          rcases List.mem_iff_getElem.mp hv_L with ⟨t, ht, hgt⟩
          exact ⟨t, ht, by rw [List.getD_eq_getElem _ _ ht]; exact hgt⟩
  · dsimp only at hc
    simpa [Expr.size] using hc

private lemma t3DrainStep_addr_bounds {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (hlay : lay = T3Layout.ofCtx ctx)
    {qi ci : ℕ} (hqi_lt : qi < ctx.wd.W.m) (hci : ci < ctx.wd.comps.length) :
    lay.base + t3OffHCur < lay.vhatStampAddr + vhatBaseW ctx.wd ci ∧
    lay.base + t3OffDel < lay.vhatStampAddr + vhatBaseW ctx.wd ci ∧
    lay.vhatOffsetAddr + ci ≠ lay.base + t3OffDel ∧
    lay.vhatOffsetAddr + ci ≠ lay.base + t3OffHCur ∧
    lay.vhatOffsetAddr + ci < lay.staticEnd ∧
    lay.vhatOffsetAddr + ci < 2 ^ w ∧
    lay.queueAddr + qi < 2 ^ w ∧
    lay.dsHandlesAddr + ci < 2 ^ w ∧
    lay.base + t3OffHCur < 2 ^ w ∧
    lay.base + t3OffDel < 2 ^ w ∧
    lay.base + t3OffDel < lay.staticEnd ∧
    lay.base + t3OffHCur < lay.staticEnd ∧
    lay.dsHandlesAddr + ctx.wd.comps.length ≤ lay.staticEnd ∧
    (∀ v < ctx.wd.comps[ci].W_sub.n,
      lay.vhatStampAddr + vhatBaseW ctx.wd ci + v < lay.staticEnd ∧
      lay.vhatStampAddr + vhatBaseW ctx.wd ci + v ≠ lay.base + t3OffDel ∧
      lay.vhatStampAddr + vhatBaseW ctx.wd ci + v ≠ lay.base + t3OffHCur) := by
  have hb := T3Layout.bounds ctx
  have ha := vhatBaseW_add_le hci
  have hs := vhatBaseW_le_sum (wd := ctx.wd) (ci := ci + 1)
  have hlt_w : (T3Layout.ofCtx ctx).staticEnd + 3 < 2 ^ w := hb.2.2.2.2.2.2.2.2.2.2.2
  subst hlay
  unfold t3OffHCur t3OffDel t3HdrSize at *
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, fun v hv => ⟨by omega, by omega, by omega⟩⟩

private lemma t3DrainStep_cost_arith (prod ds0 ds1 v0 v1 Llen c_del c_in kDelG : ℕ)
    (h1 : c_del + ds1 ≤ kDelG + ds0) (h2 : v0 = v1 + Llen) (h3 : c_in ≤ Llen * 24 + 7) :
    0 + (1 + 1 + 1 + 1) + 2 + (1 + (1 + 1 + 1 + 1 + 1) + 1 + 1) + 2 +
      (1 + (1 + 1 + 1 + 1 + 1) + 1 + 1) + 2 + (1 + 1 + 1 + 1) + 2 + (1 + 1 + 1 + 1) + 2 +
      (3 + c_del + 1) + 1 + (1 + 1 + 1) + 1 + 2 + (1 + 1 + 1) + (1 + 1 + 1 + 1 + 1 + 1) + 2 +
      (1 + 1) + 2 + (1 + 1 + 1 + 1) + 2 + c_in + (prod + ds1 + 25 * v1) ≤
      (kDelG + 77) + (prod + ds0 + 25 * v0) := by
  omega

private lemma t3DrainStep_ptriple {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (hlay : lay = T3Layout.ofCtx ctx)
    {p : Program} {dsBase rCur : ℕ} {Q : List ℕ} {g1 del0 eUpd1 : ℕ}
    {emb1 : ℕ → Option Walk} {nextU qi : ℕ} {V0 : ℕ → Finset ℕ}
    (hSpec : impl.pathDS.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure impl.pathDS.params w))
    (hqi : qi < Q.length) :
    let drainStep :=
      Stmt.seq (.assign 9 (.load (t3Add (.reg 5) (.reg 8))))
        (Stmt.seq (.assign 10 (t3Ld (.reg 3) (t3Add (t3Mul (.const 3) (.reg 9)) (.const 1))))
          (Stmt.seq (.assign 11 (t3Ld (.reg 3) (t3Add (t3Mul (.const 3) (.reg 9)) (.const 2))))
            (Stmt.seq (.assign 12 (t3Ld (.reg 0) (.const t3OffHCur)))
              (Stmt.seq (.assign 13 (.load (t3Add (.reg 4) (.reg 10))))
                (Stmt.seq (.call 14 (dsBase + 1) [.reg 13, .reg 11, .reg 12])
                  (Stmt.seq (t3St (.reg 0) (.const t3OffHCur) (.reg 14))
                    (Stmt.seq (t3St (.reg 0) (.const t3OffDel) (t3Add (t3Ld (.reg 0) (.const t3OffDel)) (.const 1)))
                      (Stmt.seq (.assign 15 (.load (.reg 12)))
                        (Stmt.seq (.assign 16 (.load (t3Add (.reg 6) (.reg 10))))
                          (t3ForRange 17 (.const 0) (.reg 15)
                            (Stmt.seq (.assign 18 (t3Ld (.reg 12) (t3Add (.const 1) (.reg 17))))
                              (.store (t3Add (.reg 7) (t3Add (.reg 16) (.reg 18))) (.reg 1)))))))))))))
    let Pre := fun (st : State) (Φ : ℕ) =>
      ∃ d, T3DrainQueueAt ctx lay rCur Q g1 del0 eUpd1 emb1 nextU qi d st Φ ∧
        (∀ cj < ctx.wd.comps.length, V0 cj ⊆ (d.states cj).Vhat) ∧
        st.regs 0 = lay.base ∧ st.regs 1 = rCur ∧ st.regs 2 = Q.length ∧
        st.regs 3 = ctx.memT1 (ctx.wInp.h + 15) ∧ st.regs 4 = lay.dsHandlesAddr ∧
        st.regs 5 = lay.queueAddr ∧ st.regs 6 = lay.vhatOffsetAddr ∧
        st.regs 7 = lay.vhatStampAddr ∧ st.regs 8 = qi
    let Post := fun (st : State) (Φ : ℕ) =>
      ∃ d', T3DrainQueueAt ctx lay rCur Q g1 del0 eUpd1 emb1 nextU (qi + 1) d' st Φ ∧
        (∀ cj < ctx.wd.comps.length, V0 cj ⊆ (d'.states cj).Vhat) ∧
        st.regs 0 = lay.base ∧ st.regs 1 = rCur ∧ st.regs 2 = Q.length ∧
        st.regs 3 = ctx.memT1 (ctx.wInp.h + 15) ∧ st.regs 4 = lay.dsHandlesAddr ∧
        st.regs 5 = lay.queueAddr ∧ st.regs 6 = lay.vhatOffsetAddr ∧
        st.regs 7 = lay.vhatStampAddr ∧ st.regs 8 = qi
    PTriple w p Pre drainStep (pNormalPost Post)
      (fun _ => ⌈impl.pathDS.params.K_del *
        (impl.pathDS.params.gQuery (WitnessCoreInput.dWInt impl.constructExpander)
          (Task1Input.mwCap impl inp.J) : ℝ)⌉₊ + 77) := by
  intro drainStep Pre Post st Φ ω ⟨d, hD, hV0, hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8⟩
  have hw1 : 1 < 2 ^ w := ctx.hwokW.1
  have hwb : Task3Input.maxWordBound impl inp < 2 ^ w := ctx.hwokW.2.2
  have hmw : ctx.wd.W.m ≤ Task1Input.mwCap impl inp.J := ctx.hmW_le
  set eW := Q[qi]'hqi
  have heW_mem : eW ∈ Q := List.getElem_mem hqi
  have heW_val := hD.Q_valid eW heW_mem
  have heW_lt_Wm : eW < ctx.wd.W.m := heW_val.2.1
  have hmeW : st.mem (lay.queueAddr + qi) = eW := listAt_getElem hD.queue_list hqi
  obtain ⟨ci, hci, eL, heL, hStart, hws_len, hws_eq⟩ := wSources_comp_of_Ico ctx heW_val.1 heW_val.2.1
  have hro := ctx.read_out_fields (mem := st.mem) hD.staticMem.1
  rcases hro with ⟨_, _, _, _, _, _, _, _, _, _, hwSrc_eq, _, _, _, _, _, hws_at, _, _, _, _, _, hws_off, hv1_eq⟩
  have heW_ws_lt : eW < ctx.wd.wSources.length := by rw [hws_len]; exact heW_lt_Wm
  have hws_eW := hws_at eW heW_ws_lt
  rw [hws_eq] at hws_eW
  have hQ_le_Wm : Q.length ≤ ctx.wd.W.m := by
    have hsub : Q.toFinset ⊆ Finset.range ctx.wd.W.m := fun x hx =>
      Finset.mem_range.mpr (hD.Q_valid x (List.mem_toFinset.mp hx)).2.1
    simpa [List.toFinset_card_of_nodup hD.Q_nd] using Finset.card_le_card hsub
  have hab := t3DrainStep_addr_bounds ctx lay hlay (lt_of_lt_of_le hqi hQ_le_Wm) hci
  rcases hab with ⟨hlt_vs_5, hlt_vs_3, hne_voff_3, hne_voff_5, hvoff_lt_s, hvoff_w,
    hq_add_w, hhdl_w, hhdr5_w, hhdr3_w, hdel_lt_s, hhcur_lt_s, hhdl_le_s, hvs_all⟩
  have hlay_end_le_max : lay.staticEnd ≤ Task3Input.maxHeapEnd impl inp := by
    have hb := T3Layout.bounds ctx; subst hlay; exact le_trans hb.2.2.2.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2.2.2.2.1
  have hv1_le_end : ctx.v1 ≤ lay.staticEnd := le_trans ctx.hv1_le (by have hb := T3Layout.bounds ctx; subst hlay; omega)
  have hwSrc_bd : ctx.memT1 (ctx.wInp.h + 15) + 3 * ctx.wd.W.m ≤ ctx.v1 := by omega
  have h3w_bd : 3 * Task1Input.mwCap impl inp.J + 2 * inp.J.m + 4 ≤ Task3Input.maxWordBound impl inp := by
    unfold Task3Input.maxWordBound
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hheap_bd : Task3Input.maxHeapEnd impl inp + 3 ≤ Task3Input.maxWordBound impl inp :=
    le_max_left _ _
  have hstatic_w : lay.staticEnd + 3 < 2 ^ w := by omega
  have hrCur_w : rCur < 2 ^ w := lt_of_le_of_lt (le_trans hD.rCur_le (eta2Bound_le_maxHeapEnd impl inp)) (by omega)
  have h3e_w : 3 * eW < 2 ^ w := by omega
  have h3e1_w : 3 * eW + 1 < 2 ^ w := by omega
  have h3e2_w : 3 * eW + 2 < 2 ^ w := by omega
  have hwSrc1_w : ctx.memT1 (ctx.wInp.h + 15) + (3 * eW + 1) < 2 ^ w := by omega
  have hwSrc2_w : ctx.memT1 (ctx.wInp.h + 15) + (3 * eW + 2) < 2 ^ w := by omega
  have hm_ci : st.mem (ctx.memT1 (ctx.wInp.h + 15) + (3 * eW + 1)) = ci := by
    rw [← Nat.add_assoc]; exact hws_eW.2.1
  have hm_eL : st.mem (ctx.memT1 (ctx.wInp.h + 15) + (3 * eW + 2)) = eL := by
    rw [← Nat.add_assoc]; exact hws_eW.2.2
  have heL_ndel : eL ∉ (d.states ci).deleted := by
    intro hmem
    have hiff := (hD.del_iff_drop ci hci eL heL).mp hmem
    have hdrop := List.drop_eq_getElem_cons hqi
    have hq_in : Q[qi]'hqi ∈ Q.drop qi := by rw [hdrop]; exact List.mem_cons_self
    rw [hStart] at hiff
    exact hiff.2 hq_in
  have hds_b := ctx.hds_bounds
  have hds_ci := hds_b.1 ci hci
  set γW := impl.pathDS.params.gExp (WitnessCoreInput.dWInt impl.constructExpander)
    (Task1Input.mwCap impl inp.J)
  have hds_ge1 : 1 ≤ Task3Input.dsOneW impl inp.J := by
    unfold Task3Input.dsOneW
    have hc := impl.pathDS.params.hC_space
    have hp : 1 ≤ impl.constructExpander.phiDen + 4 * Task1Input.mwCap impl inp.J + γW + 2 := by omega
    exact Nat.le_trans hc (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega)))
  have hOld_max : d.hCur + Task3Input.dsOneW impl inp.J ≤ Task3Input.maxHeapEnd impl inp := by
    have h1 := hD.hCur_bd
    have h2 : rCur ≤ eta2Bound inp.J := hD.rCur_le
    have h3 : g1 ≤ inp.J.m := hD.g1_le
    have h4 : del0 + qi + 1 ≤ inp.J.m * γW :=
      le_trans (by omega : del0 + qi + 1 ≤ del0 + Q.length)
        (le_trans hD.del_le_eUpd (le_trans hD.eUpd_W (Nat.mul_le_mul_right _ h3)))
    have h5 : (rCur * inp.J.m + g1 + (del0 + qi) + 1) ≤ eta2Bound inp.J * inp.J.m + inp.J.m + inp.J.m * γW := by
      have hm1 : rCur * inp.J.m ≤ eta2Bound inp.J * inp.J.m := Nat.mul_le_mul_right _ h2
      omega
    have hmul : (rCur * inp.J.m + g1 + (del0 + qi) + 1) * Task3Input.dsOneW impl inp.J ≤
        (eta2Bound inp.J * inp.J.m + inp.J.m + inp.J.m * γW) * Task3Input.dsOneW impl inp.J :=
      Nat.mul_le_mul_right _ h5
    have hmul2 : g1 * (2 * γW + 3) ≤ inp.J.m * (2 * γW + 3) := Nat.mul_le_mul_right _ h3
    unfold Task3Input.maxHeapEnd
    linarith [show (rCur * inp.J.m + g1 + (del0 + qi)) * Task3Input.dsOneW impl inp.J +
        Task3Input.dsOneW impl inp.J =
        (rCur * inp.J.m + g1 + (del0 + qi) + 1) * Task3Input.dsOneW impl inp.J by ring]
  have hOld_w : d.hCur < 2 ^ w := by
    have : d.hCur ≤ Task3Input.maxHeapEnd impl inp := le_trans (Nat.le_add_right _ _) hOld_max
    omega
  have heL_w : eL < 2 ^ w := by
    have hcm : ctx.wd.comps[ci].W_sub.m ≤ ctx.wd.W.m := by
      have hpr := ctx.hw_okW.W_m_eq
      have hm := List.single_le_sum (fun _ _ => Nat.zero_le _) _
        (List.mem_map_of_mem (f := fun c => c.W_sub.m) (List.getElem_mem hci))
      omega
    omega
  have hSpace_w : d.hCur + impl.pathDS.params.delSpace impl.constructExpander.phiNum
      impl.constructExpander.phiDen ctx.wd.comps[ci].W_sub.n ctx.wd.comps[ci].W_sub.m ctx.wd.M_W < 2 ^ w := by
    have := hds_ci.2.1; omega
  have hdel_next_w : del0 + qi + 1 < 2 ^ w := by
    have h1 : del0 + qi + 1 ≤ del0 + Q.length := by omega
    have h2 : del0 + Q.length ≤ eUpd1 := hD.del_le_eUpd
    have h3 : eUpd1 ≤ g1 * γW := hD.eUpd_W
    have h4 : g1 * γW ≤ inp.J.m * γW := Nat.mul_le_mul_right _ hD.g1_le
    have h5 : inp.J.m * γW ≤ inp.J.m * γW * Task3Input.dsOneW impl inp.J :=
      Nat.le_mul_of_pos_right _ (by omega)
    have h6 : inp.J.m * γW * Task3Input.dsOneW impl inp.J ≤ Task3Input.maxHeapEnd impl inp := by
      unfold Task3Input.maxHeapEnd
      linarith [Nat.mul_le_mul_right (Task3Input.dsOneW impl inp.J)
        (show inp.J.m * γW ≤ eta2Bound inp.J * inp.J.m + inp.J.m + inp.J.m * γW by omega)]
    omega
  have h3off_w : t3OffHCur < 2 ^ w ∧ t3OffDel < 2 ^ w ∧ 2 < 2 ^ w := by
    unfold t3OffHCur t3OffDel
    have hb_ge := hlay_end_le_max
    have : 32 ≤ lay.staticEnd := by have hb := T3Layout.bounds ctx; subst hlay; unfold t3HdrSize at *; omega
    omega
  obtain ⟨body, o, st₁, c_del, s', x', L, hproc, hruns_del, hNext_lo, hNext_sp,
      hDS_below, hDS_pres, hDS_foot_new, hs'_G, _, _, _, hs'_del, hVhat_sub, hSeqDS, hL_nd, hL_fin,
      hdsArr', hcost_del⟩ :=
    hD.dsArr.call_delete (ω := ω) (pos := st.pos) hSpec hci (le_refl _) hhdl_le_s
      (by rw [List.getD_eq_getElem _ _ hci]; exact heL) heL_ndel hOld_w heL_w
      (by rw [List.getD_eq_getElem _ _ hci]; exact hds_ci.2.2.2.1)
      (by rw [List.getD_eq_getElem _ _ hci]; exact hSpace_w)
  have hs'_G' : s'.G = (d.states ci).G := hs'_G
  have hNext_bd : o.value ≤ d.hCur + Task3Input.dsOneW impl inp.J := by
    rw [List.getD_eq_getElem _ _ hci] at hNext_sp
    exact le_trans hNext_sp (Nat.add_le_add_left hds_ci.2.1 _)
  have hNext_max : o.value ≤ Task3Input.maxHeapEnd impl inp := le_trans hNext_bd hOld_max
  have hs'_vhat_sub : s'.Vhat ⊆ Finset.range ctx.wd.comps[ci].W_sub.n := by
    rcases hdsArr'.at_ci ci hci with ⟨_, _, _, _, hg, _, _, _, hval⟩
    rw [Function.update_self] at hval hg
    rw [List.getD_eq_getElem _ _ hci] at hg
    simpa [Graph.verts, hg] using hval.2.2.2.2.2.2.2.1
  have hL_bd_w : d.hCur + 1 + L.length < 2 ^ w := by
    have := t3_seqAt_nodup_add_le hL_nd hSeqDS hdsArr'.zero_from hNext_lo
    omega
  let mem₁ := Function.update st₁.mem (lay.base + t3OffHCur) o.value
  let mem₂ := Function.update mem₁ (lay.base + t3OffDel) (del0 + qi + 1)
  let r1 := Function.update st.regs 9 eW
  let r2 := Function.update r1 10 ci
  let r3 := Function.update r2 11 eL
  let r4 := Function.update r3 12 d.hCur
  let r5 := Function.update r4 13 (st.mem (lay.dsHandlesAddr + ci))
  let r6 := Function.update r5 14 o.value
  let r7 := Function.update r6 15 L.length
  let r8 := Function.update r7 16 (vhatBaseW ctx.wd ci)
  obtain ⟨r8', hr8'_def⟩ : ∃ x, x = r8 := ⟨_, rfl⟩
  have hne_del_hcur : lay.base + t3OffDel ≠ lay.base + t3OffHCur := by
    unfold t3OffDel t3OffHCur; omega
  have hvoff_ci : st.mem (lay.vhatOffsetAddr + ci) = vhatBaseW ctx.wd ci :=
    hD.staticMem.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ci hci
  have hmem₁_del : mem₁ (lay.base + t3OffDel) = del0 + qi := by
    dsimp only [mem₁]
    rw [Function.update_of_ne hne_del_hcur, hDS_below _ hdel_lt_s, hD.del_eq]
  have hmem₂_seq : WordRAM.SeqAt mem₂ d.hCur L := by
    have hagr : ∀ a, d.hCur ≤ a → mem₂ a = st₁.mem a := fun a ha => by
      have hlo := hD.hCur_lo
      have hne1 : a ≠ lay.base + t3OffDel := by omega
      have hne2 : a ≠ lay.base + t3OffHCur := by omega
      dsimp only [mem₂, mem₁]
      rw [Function.update_of_ne hne1, Function.update_of_ne hne2]
    exact ⟨(hagr d.hCur (le_refl _)).trans hSeqDS.1, fun i hi =>
      (hagr _ (by omega)).trans (hSeqDS.2 i hi)⟩
  have hmem₂_voff : mem₂ (lay.vhatOffsetAddr + ci) = vhatBaseW ctx.wd ci := by
    dsimp only [mem₂, mem₁]
    rw [Function.update_of_ne hne_voff_3, Function.update_of_ne hne_voff_5, hDS_below _ hvoff_lt_s]
    exact hvoff_ci
  have hmem₂_vs_eq : ∀ v < ctx.wd.comps[ci].W_sub.n,
      (mem₂ (lay.vhatStampAddr + vhatBaseW ctx.wd ci + v) = rCur ↔ v ∈ (d.states ci).Vhat) := fun v hv => by
    have hv_b := hvs_all v hv
    dsimp only [mem₂, mem₁]
    rw [Function.update_of_ne hv_b.2.1, Function.update_of_ne hv_b.2.2, hDS_below _ hv_b.1]
    exact hD.vhat_stmp_eq ci hci v hv
  have hmem₂_vs_le : ∀ v < ctx.wd.comps[ci].W_sub.n,
      mem₂ (lay.vhatStampAddr + vhatBaseW ctx.wd ci + v) ≤ rCur := fun v hv => by
    have hv_b := hvs_all v hv
    dsimp only [mem₂, mem₁]
    rw [Function.update_of_ne hv_b.2.1, Function.update_of_ne hv_b.2.2, hDS_below _ hv_b.1]
    exact hD.vhat_stmp_le ci hci v hv
  have hr5_lt9 : ∀ k < 9, r5 k = st.regs k := fun k hk => by
    dsimp only [r5, r4, r3, r2, r1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
  have hr5_0 : r5 0 = lay.base := (hr5_lt9 0 (by decide)).trans hr0
  have hr5_1 : r5 1 = rCur := (hr5_lt9 1 (by decide)).trans hr1
  have hr5_2 : r5 2 = Q.length := (hr5_lt9 2 (by decide)).trans hr2
  have hr5_3 : r5 3 = ctx.memT1 (ctx.wInp.h + 15) := (hr5_lt9 3 (by decide)).trans hr3
  have hr5_4 : r5 4 = lay.dsHandlesAddr := (hr5_lt9 4 (by decide)).trans hr4
  have hr5_5 : r5 5 = lay.queueAddr := (hr5_lt9 5 (by decide)).trans hr5
  have hr5_6 : r5 6 = lay.vhatOffsetAddr := (hr5_lt9 6 (by decide)).trans hr6
  have hr5_7 : r5 7 = lay.vhatStampAddr := (hr5_lt9 7 (by decide)).trans hr7
  have hr5_8 : r5 8 = qi := (hr5_lt9 8 (by decide)).trans hr8
  have hr5_10 : r5 10 = ci := by
    dsimp only [r5, r4, r3, r2]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_self]
  have hr5_11 : r5 11 = eL := by
    dsimp only [r5, r4, r3]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]
  have hr5_12 : r5 12 = d.hCur := by
    dsimp only [r5, r4]; rw [Function.update_of_ne (by decide), Function.update_self]
  have hr5_13 : r5 13 = st.mem (lay.dsHandlesAddr + ci) := Function.update_self _ _ _
  have hr8_lt14 : ∀ k < 14, r8 k = r5 k := fun k hk => by
    dsimp only [r8, r7, r6]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hr8_eq : ∀ r ≤ 16, r8' r = r8 r := fun _ _ => hr8'_def ▸ rfl
  have hr8_1 : r8 1 = rCur := (hr8_lt14 1 (by decide)).trans hr5_1
  have hr8_7 : r8 7 = lay.vhatStampAddr := (hr8_lt14 7 (by decide)).trans hr5_7
  have hr8_12 : r8 12 = d.hCur := (hr8_lt14 12 (by decide)).trans hr5_12
  have hr8_15 : r8 15 = L.length := by
    dsimp only [r8, r7]; rw [Function.update_of_ne (by decide), Function.update_self]
  have hr8_16 : r8 16 = vhatBaseW ctx.wd ci := Function.update_self _ _ _
  obtain ⟨o_in, stF, c_in, Φ_in, hr_in, hq_in, hc_in⟩ :=
    t3InnerStamp_ptriple ctx lay hlay hci mem₂ r8' hVhat_sub hL_nd hL_fin hs'_vhat_sub
      ⟨mem₂, r8', st₁.pos⟩ 0 ω
      ⟨rfl, fun _ _ => rfl,
        show r8' 1 = rCur by rw [hr8'_def]; exact hr8_1,
        show r8' 7 = lay.vhatStampAddr by rw [hr8'_def]; exact hr8_7,
        show r8' 12 = d.hCur by rw [hr8'_def]; exact hr8_12,
        show r8' 15 = L.length by rw [hr8'_def]; exact hr8_15,
        show r8' 16 = vhatBaseW ctx.wd ci by rw [hr8'_def]; exact hr8_16,
        hD.hCur_lo, hL_bd_w, hmem₂_seq, hmem₂_vs_eq, hmem₂_vs_le⟩
  cases o_in with
  | returned _ => exact False.elim hq_in
  | normal =>
    rcases hq_in with ⟨hFr_regs, hFr_mem, hV_eq, hV_le⟩
    have hupd := T3DrainQueueAt.step_update hlay hD hqi hci heL hStart hNext_lo hNext_bd
      hSpec.1 st₁.mem hDS_below hDS_pres hDS_foot_new hs'_G' hs'_del hVhat_sub hL_nd hL_fin hdsArr'
      (by
        rw [hFr_mem _ (Or.inl hlt_vs_5)]
        dsimp only [mem₂, mem₁]
        rw [Function.update_of_ne hne_del_hcur.symm, Function.update_self])
      (by
        rw [hFr_mem _ (Or.inl hlt_vs_3)]
        dsimp only [mem₂]
        exact Function.update_self _ _ _)
      (fun a hne5 hne3 hdisj => by
        rw [hFr_mem a hdisj]
        dsimp only [mem₂, mem₁]
        rw [Function.update_of_ne hne3, Function.update_of_ne hne5])
      hV_eq hV_le
    rcases hupd with ⟨hD', hdsPhi_F, hecPhi_F, hvhat_drop⟩
    have hcost_ds : c_del + dsTotalPhi impl.pathDS lay.dsHandlesAddr ctx.wd.comps.length
        (Function.update d.reps ci x') stF.mem ≤
        ⌈impl.pathDS.params.K_del * (impl.pathDS.params.gQuery (WitnessCoreInput.dWInt impl.constructExpander) (Task1Input.mwCap impl inp.J) : ℝ)⌉₊ +
          dsTotalPhi impl.pathDS lay.dsHandlesAddr ctx.wd.comps.length d.reps st.mem := by
      rw [hdsPhi_F]
      exact le_trans hcost_del (Nat.add_le_add_right hds_b.2.1 _)
    have h3_w : 3 < 2 ^ w := by omega
    have hr1_3 : r1 3 = ctx.memT1 (ctx.wInp.h + 15) := by
      dsimp only [r1]; rw [Function.update_of_ne (by decide), hr3]
    have hr1_9 : r1 9 = eW := Function.update_self _ _ _
    have hev10 : (t3Ld (.reg 3) (t3Add (t3Mul (.const 3) (.reg 9)) (.const 1))).eval w
        ⟨st.mem, r1, st.pos⟩ = some ci :=
      hm_ci ▸ Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq hr1_3)
        (Expr.eval_add (Expr.eval_mul (Expr.eval_const h3_w) (Expr.eval_reg_of_eq hr1_9) h3e_w)
          (Expr.eval_const hw1) h3e1_w) hwSrc1_w)
    have hr2_3 : r2 3 = ctx.memT1 (ctx.wInp.h + 15) := by
      dsimp only [r2]; rw [Function.update_of_ne (by decide), hr1_3]
    have hr2_9 : r2 9 = eW := by
      dsimp only [r2]; rw [Function.update_of_ne (by decide), hr1_9]
    have hev11 : (t3Ld (.reg 3) (t3Add (t3Mul (.const 3) (.reg 9)) (.const 2))).eval w
        ⟨st.mem, r2, st.pos⟩ = some eL :=
      hm_eL ▸ Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq hr2_3)
        (Expr.eval_add (Expr.eval_mul (Expr.eval_const h3_w) (Expr.eval_reg_of_eq hr2_9) h3e_w)
          (Expr.eval_const h3off_w.2.2) h3e2_w) hwSrc2_w)
    have hr3_0 : r3 0 = lay.base := by
      dsimp only [r3, r2, r1]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), hr0]
    have hr4_4 : r4 4 = lay.dsHandlesAddr := by
      dsimp only [r4, r3, r2, r1]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr4]
    have hr4_10 : r4 10 = ci := by
      dsimp only [r4, r3, r2]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]
    have hr6_0 : r6 0 = lay.base := by
      dsimp only [r6]; rw [Function.update_of_ne (by decide), hr5_0]
    have hr6_12 : r6 12 = d.hCur := by
      dsimp only [r6]; rw [Function.update_of_ne (by decide), hr5_12]
    have hr7_6 : r7 6 = lay.vhatOffsetAddr := by
      dsimp only [r7, r6]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr5_6]
    have hr7_10 : r7 10 = ci := by
      dsimp only [r7, r6]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr5_10]
    apply t3_ptriple_of_cps
    refine t3_assign_cps (r := 9) (Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq hr5) (Expr.eval_reg_of_eq hr8) hq_add_w)) ?_
    rw [hmeW]
    refine t3_assign_cps (r := 10) hev10 ?_
    refine t3_assign_cps (r := 11) hev11 ?_
    refine t3_ld_cps hr3_0 h3off_w.1 hhdr5_w (hD.hCur_eq : st.mem (lay.base + t3OffHCur) = d.hCur) ?_
    refine t3_assign_cps (r := 13)
      (Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq hr4_4) (Expr.eval_reg_of_eq hr4_10) hhdl_w)) ?_
    have hargs : evalArgs w ⟨st.mem, r5, st.pos⟩ [.reg 13, .reg 11, .reg 12] =
        some [st.mem (lay.dsHandlesAddr + ci), eL, d.hCur] := by
      simp only [evalArgs, Expr.eval, hr5_13, hr5_11, hr5_12]
    have hcall : Runs w p ω (.call 14 (dsBase + 1) [.reg 13, .reg 11, .reg 12])
        ⟨st.mem, r5, st.pos⟩ .normal ⟨st₁.mem, r6, st₁.pos⟩ (3 + c_del + 1) :=
      runs_call_iff.mpr ⟨_, body, o, st₁, c_del, hargs, hproc, hruns_del, rfl, rfl, by simp [argsSize, Expr.size]⟩
    refine t3_seq_stmt_cps hcall (le_refl _) ?_
    refine t3_st_cps hr6_0 h3off_w.1 hhdr5_w (Function.update_self _ _ _ : r6 14 = o.value) ?_
    have hev_del : (t3Add (t3Ld (.reg 0) (.const t3OffDel)) (.const 1)).eval w ⟨mem₁, r6, st₁.pos⟩ =
        some (del0 + qi + 1) :=
      Expr.eval_add (hmem₁_del ▸ Expr.eval_load (Expr.eval_add
        (Expr.eval_reg_of_eq hr6_0)
        (Expr.eval_const h3off_w.2.1) hhdr3_w))
        (Expr.eval_const hw1) hdel_next_w
    refine t3_store_cps
      (Expr.eval_add (Expr.eval_reg_of_eq hr6_0) (Expr.eval_const h3off_w.2.1) hhdr3_w)
      hev_del ?_
    have hm_Llen : mem₂ d.hCur = L.length := hmem₂_seq.1
    have hev15 : (Expr.load (.reg 12)).eval w ⟨mem₂, r6, st₁.pos⟩ = some L.length :=
      hm_Llen ▸ Expr.eval_load (Expr.eval_reg_of_eq hr6_12)
    have hev16 : (Expr.load (t3Add (.reg 6) (.reg 10))).eval w ⟨mem₂, r7, st₁.pos⟩ =
        some (vhatBaseW ctx.wd ci) :=
      hmem₂_voff ▸ Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq hr7_6) (Expr.eval_reg_of_eq hr7_10) hvoff_w)
    refine t3_assign_cps (r := 15) hev15 ?_
    refine t3_assign_cps (r := 16) hev16 ?_
    refine ⟨.normal, stF, c_in, t3RoundPhi ctx lay _ stF.mem,
      (by change Runs w p ω _ ⟨mem₂, r8, st₁.pos⟩ _ _ _; exact hr8'_def ▸ hr_in),
      ⟨_, hD', fun cj hcj => by
          by_cases h : cj = ci
          · subst h; simpa [Function.update_self] using (hV0 cj hcj).trans hVhat_sub
          · simpa [Function.update_of_ne h] using hV0 cj hcj,
        (hFr_regs 0 (by omega)).trans ((hr8_eq 0 (by omega)).trans ((hr8_lt14 0 (by decide)).trans hr5_0)),
        (hFr_regs 1 (by omega)).trans ((hr8_eq 1 (by omega)).trans ((hr8_lt14 1 (by decide)).trans hr5_1)),
        (hFr_regs 2 (by omega)).trans ((hr8_eq 2 (by omega)).trans ((hr8_lt14 2 (by decide)).trans hr5_2)),
        (hFr_regs 3 (by omega)).trans ((hr8_eq 3 (by omega)).trans ((hr8_lt14 3 (by decide)).trans hr5_3)),
        (hFr_regs 4 (by omega)).trans ((hr8_eq 4 (by omega)).trans ((hr8_lt14 4 (by decide)).trans hr5_4)),
        (hFr_regs 5 (by omega)).trans ((hr8_eq 5 (by omega)).trans ((hr8_lt14 5 (by decide)).trans hr5_5)),
        (hFr_regs 6 (by omega)).trans ((hr8_eq 6 (by omega)).trans ((hr8_lt14 6 (by decide)).trans hr5_6)),
        (hFr_regs 7 (by omega)).trans ((hr8_eq 7 (by omega)).trans ((hr8_lt14 7 (by decide)).trans hr5_7)),
        (hFr_regs 8 (by omega)).trans ((hr8_eq 8 (by omega)).trans ((hr8_lt14 8 (by decide)).trans hr5_8))⟩,
      ?_⟩
    have hphi_src : Φ = t3RoundPhi ctx lay d st.mem := hD.phi_eq
    dsimp only [t3RoundPhi, t3KdelCost] at hphi_src ⊢
    rw [hphi_src, hecPhi_F]
    simp only [Expr.size, t3Ld, t3Add, t3Mul, t3OffHCur, t3OffDel]
    exact t3DrainStep_cost_arith _ _ _ _ _ L.length c_del c_in _ hcost_ds hvhat_drop (by omega)

theorem t3DrainQueue_ptriple {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (hlay : lay = T3Layout.ofCtx ctx)
    {p : Program} {selfBase dsBase : ℕ}
    (hSpec : impl.pathDS.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure impl.pathDS.params w))
    (_hDrain : p.procs[selfBase + 2]? = some (t3DrainQueueBody dsBase))
    {rCur : ℕ} {Q : List ℕ} {g1 del0 eUpd1 : ℕ} {emb1 : ℕ → Option Walk} {nextU : ℕ}
    {V0 : ℕ → Finset ℕ} :
    let Pre := fun (st : State) (Φ : ℕ) =>
      ∃ d, T3DrainQueueAt ctx lay rCur Q g1 del0 eUpd1 emb1 nextU 0 d st Φ ∧
        (∀ cj < ctx.wd.comps.length, V0 cj ⊆ (d.states cj).Vhat) ∧
        st.regs 0 = lay.base ∧ st.regs 1 = rCur ∧ st.regs 2 = Q.length
    let Post := fun (_o : Outcome) (st : State) (Φ : ℕ) =>
      ∃ d', T3DrainQueueAt ctx lay rCur Q g1 del0 eUpd1 emb1 nextU Q.length d' st Φ ∧
        (∀ cj < ctx.wd.comps.length, V0 cj ⊆ (d'.states cj).Vhat)
    PTriple w p Pre (t3DrainQueueBody dsBase) Post
      (fun _ => Q.length * (⌈impl.pathDS.params.K_del *
        (impl.pathDS.params.gQuery (WitnessCoreInput.dWInt impl.constructExpander)
          (Task1Input.mwCap impl inp.J) : ℝ)⌉₊ + 86) + 40) := by
  intro Pre Post st Φ ω ⟨d, hD, hV0, hr0, hr1, hr2⟩
  have hb := T3Layout.bounds ctx
  unfold t3HdrSize at hb
  have hw1 : 1 < 2 ^ w := ctx.hwokW.1
  have hQ_le_Wm : Q.length ≤ ctx.wd.W.m := by
    have hsub : Q.toFinset ⊆ Finset.range ctx.wd.W.m := fun x hx =>
      Finset.mem_range.mpr (hD.Q_valid x (List.mem_toFinset.mp hx)).2.1
    simpa [List.toFinset_card_of_nodup hD.Q_nd] using Finset.card_le_card hsub
  have hQ_w : Q.length < 2 ^ w := by
    have := ctx.hmW_le; have := ctx.hwokW.2.2
    have : Task3Input.maxHeapEnd impl inp + 3 ≤ Task3Input.maxWordBound impl inp := le_max_left _ _
    omega
  have hro := ctx.read_out_fields (mem := st.mem) hD.staticMem.1
  rcases hro with ⟨_, _, _, _, _, _, _, _, _, _, hwSrc_eq, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  have hh3_w : lay.base + t3OffWSrc < 2 ^ w := by unfold t3OffWSrc; subst hlay; omega
  have hh4_w : lay.base + t3OffDsHdl < 2 ^ w := by unfold t3OffDsHdl; subst hlay; omega
  have hh5_w : lay.base + t3OffQueue < 2 ^ w := by unfold t3OffQueue; subst hlay; omega
  have hh6_w : lay.base + t3OffVOff < 2 ^ w := by unfold t3OffVOff; subst hlay; omega
  have hh7_w : lay.base + t3OffVStmp < 2 ^ w := by unfold t3OffVStmp; subst hlay; omega
  let LoopInv : ℕ → State → ℕ → Prop := fun qi st' Φ' =>
    ∃ d', T3DrainQueueAt ctx lay rCur Q g1 del0 eUpd1 emb1 nextU qi d' st' Φ' ∧
      (∀ cj < ctx.wd.comps.length, V0 cj ⊆ (d'.states cj).Vhat) ∧
      st'.regs 0 = lay.base ∧ st'.regs 1 = rCur ∧ st'.regs 2 = Q.length ∧
      st'.regs 3 = ctx.memT1 (ctx.wInp.h + 15) ∧ st'.regs 4 = lay.dsHandlesAddr ∧
      st'.regs 5 = lay.queueAddr ∧ st'.regs 6 = lay.vhatOffsetAddr ∧
      st'.regs 7 = lay.vhatStampAddr ∧ st'.regs 8 = qi
  let P0 : State → ℕ → Prop := fun st' Φ' =>
    ∃ d', T3DrainQueueAt ctx lay rCur Q g1 del0 eUpd1 emb1 nextU 0 d' st' Φ' ∧
      (∀ cj < ctx.wd.comps.length, V0 cj ⊆ (d'.states cj).Vhat) ∧
      st'.regs 0 = lay.base ∧ st'.regs 1 = rCur ∧ st'.regs 2 = Q.length ∧
      st'.regs 3 = ctx.memT1 (ctx.wInp.h + 15) ∧ st'.regs 4 = lay.dsHandlesAddr ∧
      st'.regs 5 = lay.queueAddr ∧ st'.regs 6 = lay.vhatOffsetAddr ∧
      st'.regs 7 = lay.vhatStampAddr
  let drainStep :=
    Stmt.seq (.assign 9 (.load (t3Add (.reg 5) (.reg 8))))
      (Stmt.seq (.assign 10 (t3Ld (.reg 3) (t3Add (t3Mul (.const 3) (.reg 9)) (.const 1))))
        (Stmt.seq (.assign 11 (t3Ld (.reg 3) (t3Add (t3Mul (.const 3) (.reg 9)) (.const 2))))
          (Stmt.seq (.assign 12 (t3Ld (.reg 0) (.const t3OffHCur)))
            (Stmt.seq (.assign 13 (.load (t3Add (.reg 4) (.reg 10))))
              (Stmt.seq (.call 14 (dsBase + 1) [.reg 13, .reg 11, .reg 12])
                (Stmt.seq (t3St (.reg 0) (.const t3OffHCur) (.reg 14))
                  (Stmt.seq (t3St (.reg 0) (.const t3OffDel) (t3Add (t3Ld (.reg 0) (.const t3OffDel)) (.const 1)))
                    (Stmt.seq (.assign 15 (.load (.reg 12)))
                      (Stmt.seq (.assign 16 (.load (t3Add (.reg 6) (.reg 10))))
                        (t3ForRange 17 (.const 0) (.reg 15)
                          (Stmt.seq (.assign 18 (t3Ld (.reg 12) (t3Add (.const 1) (.reg 17))))
                            (.store (t3Add (.reg 7) (t3Add (.reg 16) (.reg 18))) (.reg 1)))))))))))))
  have hloop := PTriple.forRange_const (w := w) (p := p) (P := P0)
    (r := 8) (lo := .const 0) (hi := .reg 2) (body := drainStep) (Inv := LoopInv)
    (⌈impl.pathDS.params.K_del *
      (impl.pathDS.params.gQuery (WitnessCoreInput.dWInt impl.constructExpander)
        (Task1Input.mwCap impl inp.J) : ℝ)⌉₊ + 77)
    0 Q.length (Nat.zero_le _) hw1 (fun _ => hQ_w)
    (fun st' Φ' ⟨d', hD', hV, s0, s1, s2, s3, s4, s5, s6, s7⟩ => by
      refine ⟨Expr.eval_const (by omega : 0 < 2 ^ w), d', hD'.with_regs, hV, by simp [s0], by simp [s1], by simp [s2],
        by simp [s3], by simp [s4], by simp [s5], by simp [s6], by simp [s7], by simp⟩)
    (fun _ _ _ _ _ h => h.choose_spec.2.2.2.2.2.2.2.2.2.2)
    (fun _ _ _ _ _ h => Expr.eval_reg_of_eq h.choose_spec.2.2.2.2.1)
    (fun qi _ hqi st' Φ' ω hI => by
      have hstep := t3DrainStep_ptriple (V0 := V0) ctx lay hlay hSpec hqi st' Φ' ω hI
      obtain ⟨o, st'', c, Φ'', hr, hq, hc⟩ := hstep
      cases o with
      | returned _ => exact False.elim hq
      | normal =>
        rcases hq with ⟨d'', hD'', hV', a0, a1, a2, a3, a4, a5, a6, a7, a8⟩
        refine ⟨.normal, st'', c, Φ'', hr, ⟨⟨d'', hD''.with_regs, hV',
          by simp [a0], by simp [a1], by simp [a2], by simp [a3], by simp [a4],
          by simp [a5], by simp [a6], by simp [a7], by simp⟩, a8⟩, hc⟩)
  apply t3_ptriple_of_cps
  refine t3_ld_cps hr0 (show t3OffWSrc < 2 ^ w by omega) hh3_w
    (hD.staticMem.2.2.2.2.2.2.2.2.2.2.2.2.2.1 : st.mem (lay.base + t3OffWSrc) = ctx.memT1 (ctx.wInp.h + 15)) ?_
  refine t3_ld_cps (by simp [hr0] : Function.update st.regs 3 (ctx.memT1 (ctx.wInp.h + 15)) 0 = lay.base)
    (show t3OffDsHdl < 2 ^ w by omega) hh4_w hD.staticMem.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
  refine t3_ld_cps (by simp [hr0] : Function.update (Function.update st.regs 3 _) 4 lay.dsHandlesAddr 0 = lay.base)
    (show t3OffQueue < 2 ^ w by omega) hh5_w hD.staticMem.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
  refine t3_ld_cps (by simp [hr0]) (show t3OffVOff < 2 ^ w by omega) hh6_w
    hD.staticMem.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
  refine t3_ld_cps (by simp [hr0]) (show t3OffVStmp < 2 ^ w by omega) hh7_w
    hD.staticMem.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
  refine t3_normal_ptriple_cps hloop ⟨d, hD.with_regs, hV0, by simp [hr0], by simp [hr1], by simp [hr2],
    by simp, by simp, by simp, by simp, by simp⟩
    (b₁ := Q.length * (⌈impl.pathDS.params.K_del *
      (impl.pathDS.params.gQuery (WitnessCoreInput.dWInt impl.constructExpander)
        (Task1Input.mwCap impl inp.J) : ℝ)⌉₊ + 86) + 7)
    (by simp only [Expr.size, Nat.sub_zero, Nat.add_assoc]; exact le_refl _) ?_
  intro st₁ Φ₁ ⟨d', hD', hV', _⟩
  exact t3_end_ret_cps (Expr.eval_const (by omega : 0 < 2 ^ w)) ⟨d', hD', hV'⟩ (by
    simp only [Expr.size, t3Ld, t3Add]
    omega)

end MinCostFlow.Spanner
