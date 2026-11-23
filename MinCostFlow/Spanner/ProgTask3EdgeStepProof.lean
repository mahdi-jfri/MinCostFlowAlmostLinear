module

public import MinCostFlow.Spanner.ProgTask3CopyVertProof

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM Cited

/-!
# Edge-Lifting Loop Verification (`t3EdgeStep`) for `t3MiddleEdge` (`selfBase + 3`)

Proves `t3EdgeStep_ptriple` maintaining `T3EdgeStepInv` across all edges of the
local path returned by `PathDS.getPath`.
-/

private lemma t3EdgeStep_mem3_props {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (hlay : lay = T3Layout.ofCtx ctx)
    {hMid pv pe eW k u c : ℕ} (mem : ℕ → ℕ)
    (hPe_le : pe ≤ ctx.wd.W.m) (hk : k < pe) (heW : eW < ctx.wd.W.m) (hMid_lo : lay.staticEnd ≤ hMid) :
    let hBase := hMid + 2 + pv
    let mem1 := Function.update mem (hBase + k) eW
    let mem2 := Function.update mem1 (lay.base + t3OffEcongUpd) u
    let mem3 := Function.update mem2 (lay.econgCountAddr + eW) c
    (∀ eW' < ctx.wd.W.m, eW' ≠ eW → mem3 (lay.econgCountAddr + eW') = mem (lay.econgCountAddr + eW')) ∧
    (∀ eW' < ctx.wd.W.m, mem3 (lay.wDelStampAddr + eW') = mem (lay.wDelStampAddr + eW')) ∧
    (∀ i < k, mem3 (lay.queueAddr + i) = mem (lay.queueAddr + i)) ∧
    (∀ cj < ctx.wd.comps.length, mem3 (lay.dsHandlesAddr + cj) = mem (lay.dsHandlesAddr + cj)) ∧
    (∀ a, lay.staticEnd ≤ a → a ≠ hBase + k → mem3 a = mem a) ∧
    (∀ i < k, mem3 (hBase + i) = mem (hBase + i)) ∧
    mem3 (hBase + k) = eW ∧
    mem3 (lay.base + t3OffEcongUpd) = u ∧
    mem3 (lay.econgCountAddr + eW) = c ∧
    mem2 (lay.econgCountAddr + eW) = mem (lay.econgCountAddr + eW) ∧
    mem1 (lay.base + t3OffEcongUpd) = mem (lay.base + t3OffEcongUpd) ∧
    (∀ a, a ≠ lay.base + t3OffEcongUpd →
      ¬ (lay.econgCountAddr ≤ a ∧ a < lay.econgCountAddr + ctx.wd.W.m) →
      ¬ (lay.wDelStampAddr ≤ a ∧ a < lay.wDelStampAddr + ctx.wd.W.m) →
      ¬ (lay.queueAddr ≤ a ∧ a < lay.queueAddr + pe) →
      ¬ (hBase ≤ a ∧ a < hBase + pe) → mem3 a = mem a) := by
  have hb := T3Layout.bounds ctx
  subst hlay
  unfold t3OffEcongUpd t3HdrSize at *
  intro hBase mem1 mem2 mem3
  refine ⟨fun eW' _ hne => ?_, fun eW' _ => ?_, fun i _ => ?_, fun cj hcj => ?_,
    fun a ha hne => ?_, fun i _ => ?_, ?_, ?_, ?_, ?_, ?_, fun a h1 h2 _ _ h5 => ?_⟩
  · dsimp only [mem3, mem2, mem1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · dsimp only [mem3, mem2, mem1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · dsimp only [mem3, mem2, mem1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · dsimp only [mem3, mem2, mem1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · dsimp only [mem3, mem2, mem1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne hne]
  · dsimp only [mem3, mem2, mem1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · dsimp only [mem3, mem2, mem1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
  · dsimp only [mem3, mem2]
    rw [Function.update_of_ne (by omega), Function.update_self]
  · exact Function.update_self _ _ _
  · dsimp only [mem2, mem1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · dsimp only [mem1]
    rw [Function.update_of_ne (by omega)]
  · dsimp only [mem3, mem2, mem1]
    rw [Function.update_of_ne (fun heq => h2 (by omega)), Function.update_of_ne h1,
      Function.update_of_ne (fun heq => h5 (by omega))]

private lemma t3EdgeStep_static_lt_addr {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (hlay : lay = T3Layout.ofCtx ctx)
    {eW : ℕ} (heW : eW < ctx.wd.W.m) :
    ctx.memT1 (ctx.wInp.h + 14) + eW < lay.base ∧
    lay.base + t3OffEcongUpd < lay.econgCountAddr ∧
    lay.base + t3HdrSize ≤ lay.econgCountAddr ∧
    lay.econgCountAddr + eW < lay.wDelStampAddr ∧
    lay.wDelStampAddr + eW < lay.queueAddr ∧
    lay.queueAddr + ctx.wd.W.m ≤ lay.staticEnd ∧
    lay.base + t3HdrSize ≤ lay.dsHandlesAddr ∧
    lay.dsHandlesAddr + ctx.wd.comps.length = lay.econgCountAddr ∧
    lay.staticEnd + 3 < 2 ^ w := by
  have hb := T3Layout.bounds ctx
  have ho := ctx.outAt
  rcases ho with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, halo, haw, hwn, hws_eq, hjs_eq, hv1_eq, _⟩
  have hlt1 := ctx.lt_v1_of_t1
  have hv1 := ctx.hv1_le
  have hvm : ctx.wInp.prep.J.m = inp.J.m := by rw [ctx.hWInpJ]
  subst hlay; unfold t3OffEcongUpd t3HdrSize at *
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, rfl, by omega⟩

theorem t3EdgeStep_ptriple {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (hlay : lay = T3Layout.ofCtx ctx)
    {p : Program} {rCur eJ ci hOld hMid : ℕ} {P : Walk}
    (hLoc : impl.pathDS.R.Local)
    (d0 : T3RoundData impl.pathDS) (reps1 : ℕ → impl.pathDS.R.τ) (memStart regsInit : ℕ → ℕ)
    (heJ : eJ < inp.J.m) (hci : ci < ctx.wd.comps.length)
    (_hrCur_pos : 1 ≤ rCur) (hrCur_le : rCur ≤ eta2Bound inp.J) (hunemb : d0.emb eJ = none)
    (hOld_lo : lay.staticEnd ≤ hOld) (hle_hm : hOld + (1 + P.verts.length + P.edges.length) ≤ hMid)
    {uL vL : ℕ} (hP_wk : P.IsWalk ctx.wd.comps[ci].W_sub uL vL) (hP_nd : P.verts.Nodup)
    (hP_ndel : ∀ e ∈ P.edges, e ∉ (d0.states ci).deleted)
    (_hP_lenW : P.edges.length ≤ impl.pathDS.params.gExp (WitnessCoreInput.dWInt impl.constructExpander)
      (Task1Input.mwCap impl inp.J))
    (heUpd_W : d0.econgUpd ≤ d0.getPathCnt * impl.pathDS.params.gExp (WitnessCoreInput.dWInt impl.constructExpander)
      (Task1Input.mwCap impl inp.J))
    (hgp_le : d0.getPathCnt ≤ inp.J.m - (unembeddedSet2Pure inp.J d0.emb).card)
    (hH_end_w : hMid + 2 + P.verts.length + P.edges.length < 2 ^ w)
    (hWalk_st : WalkAt memStart hOld P) (hStatic_st : T3StaticMem ctx lay memStart)
    (hDS_foot : ∀ cj < ctx.wd.comps.length, ∀ a,
      impl.pathDS.R.foot (memStart (lay.dsHandlesAddr + cj)) (reps1 cj) a →
      lay.staticEnd ≤ a ∧ a < hMid)
    (hECnt_d0 : ∀ eW < ctx.wd.W.m, memStart (lay.econgCountAddr + eW) =
      {j ∈ Finset.range inp.J.m | eW ∈ (partialToWalk d0.emb j).edges}.card)
    (hEc_rnd : ∀ eW < ctx.wd.W.m,
      econgAt inp.J (fun _ => 1) ctx.wd.wW (partialToWalk d0.emb) eW ≤ ((rCur : ℝ) + 1 / 2) * ctx.wd.τ₂)
    (hWdel_c : ∀ eW ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m,
      memStart (lay.wDelStampAddr + eW) ≤ rCur ∧
      memStart (lay.wDelStampAddr + eW) ≤ memStart (lay.econgCountAddr + eW))
    (hWdel_t : ∀ eW ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m,
      memStart (lay.wDelStampAddr + eW) = rCur →
      (rCur : ℝ) * ctx.wd.τ₂ ≤ econgAt inp.J (fun _ => 1) ctx.wd.wW (partialToWalk d0.emb) eW)
    (hWdel_lt : ∀ eW ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m,
      memStart (lay.wDelStampAddr + eW) < rCur →
      econgAt inp.J (fun _ => 1) ctx.wd.wW (partialToWalk d0.emb) eW ≤ (rCur : ℝ) * ctx.wd.τ₂)
    (hUpd_sum : d0.econgUpd = ∑ eW ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m,
      memStart (lay.econgCountAddr + eW))
    (hDel_iff : ∀ (cj : ℕ) (hcj : cj < ctx.wd.comps.length) (eL : ℕ), eL < ctx.wd.comps[cj].W_sub.m →
      (eL ∈ (d0.states cj).deleted ↔
        memStart (lay.wDelStampAddr + (ctx.wd.comps[cj].wStart + eL)) = rCur))
    (hECnt_eq_mem : memStart (lay.base + t3OffEcongUpd) = d0.econgUpd)
    (hregsInit : regsInit 0 = lay.base ∧ regsInit 1 = rCur ∧ regsInit 11 = hOld ∧
      regsInit 13 = hMid ∧ regsInit 14 = P.verts.length ∧ regsInit 15 = P.edges.length ∧
      regsInit 17 = ctx.wd.comps[ci].wStart ∧ regsInit 18 = 0 ∧
      regsInit 19 = ctx.memT1 (ctx.wInp.h + 14) ∧ regsInit 20 = ctx.wInp.prep.phiDen_dec ∧
      regsInit 21 = rCur * ctx.wInp.tau2Int impl.constructExpander impl.pathDS.params ∧
      regsInit 22 = lay.econgCountAddr ∧ regsInit 23 = lay.wDelStampAddr ∧ regsInit 24 = lay.queueAddr) :
    let edgeStep :=
      Stmt.seq (.assign 26 (t3Ld (.reg 11) (t3Add (t3Add (.const 2) (.reg 14)) (.reg 25))))
        (Stmt.seq (.assign 27 (t3Add (.reg 17) (.reg 26)))
          (Stmt.seq (t3St (.reg 13) (t3Add (t3Add (.const 2) (.reg 14)) (.reg 25)) (.reg 27))
            (Stmt.seq (t3St (.reg 0) (.const t3OffEcongUpd) (t3Add (t3Ld (.reg 0) (.const t3OffEcongUpd)) (.const 1)))
              (Stmt.seq (.assign 28 (t3Add (.load (t3Add (.reg 22) (.reg 27))) (.const 1)))
                (Stmt.seq (.store (t3Add (.reg 22) (.reg 27)) (.reg 28))
                  (Stmt.seq (.assign 29 (t3Mul (.reg 21) (.load (t3Add (.reg 19) (.reg 27)))))
                    (Stmt.seq (.assign 30 (t3Mul (.reg 28) (.reg 20)))
                      (.cond (t3Lt (.reg 30) (.reg 29))
                        .nop
                        (.cond (t3Lt (.load (t3Add (.reg 23) (.reg 27))) (.reg 1))
                          (Stmt.seq (.store (t3Add (.reg 23) (.reg 27)) (.reg 1))
                            (Stmt.seq (.store (t3Add (.reg 24) (.reg 18)) (.reg 27))
                              (.assign 18 (t3Add (.reg 18) (.const 1)))))
                          .nop)))))))))
    let stmt := t3ForRange 25 (.const 0) (.reg 15) edgeStep
    let Pre := fun (st : State) (Φ : ℕ) =>
      st.mem = memStart ∧ st.regs = regsInit ∧
      Φ = t3KdelCost impl inp.J * (t3EcongPhi ctx lay memStart + P.edges.length) +
        dsTotalPhi impl.pathDS lay.dsHandlesAddr ctx.wd.comps.length reps1 memStart +
        25 * t3VhatRem ctx.wd d0.states
    let Post := fun (st : State) (Φ : ℕ) =>
      T3EdgeStepInv ctx lay rCur eJ ci hci hOld hMid P d0 reps1 memStart regsInit P.edges.length st Φ
    PTriple w p Pre stmt (pNormalPost Post) (fun _ => P.edges.length * 115 + 7) := by
  intro edgeStep stmt Pre Post
  have hw1 : 1 < 2 ^ w := ctx.hwokW.1
  have hwb : Task3Input.maxWordBound impl inp < 2 ^ w := ctx.hwokW.2.2
  have hw2_w : 2 < 2 ^ w := by
    have h1 : 3 ≤ Task3Input.maxHeapEnd impl inp + 3 := by omega
    have h2 : Task3Input.maxHeapEnd impl inp + 3 ≤ Task3Input.maxWordBound impl inp := le_max_left _ _
    omega
  have hPl_w := mkW_isWalk_liftWSubWalk ctx.hw_okW ctx.hws hci hP_wk
  have hPl_nd : (liftWSubWalk ctx.wd.comps[ci] P).edges.Nodup := hPl_w.2.2.1 hP_nd
  have hPe_le_Wm : P.edges.length ≤ ctx.wd.W.m := by
    have hsub : (liftWSubWalk ctx.wd.comps[ci] P).edges.toFinset ⊆ Finset.range ctx.wd.W.m := by
      intro x hx; exact Finset.mem_range.mpr (hPl_w.2.2.2 x (List.mem_toFinset.mp hx)).2
    have hc := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hPl_nd, Finset.card_range] at hc
    have hlen_eq : (liftWSubWalk ctx.wd.comps[ci] P).edges.length = P.edges.length := hPl_w.2.1
    exact hlen_eq ▸ hc
  have hPe_w : P.edges.length < 2 ^ w := by
    have := ctx.hmW_le
    have hbd : 3 * Task1Input.mwCap impl inp.J + 2 * inp.J.m + 4 ≤ Task3Input.maxWordBound impl inp := by
      unfold Task3Input.maxWordBound
      exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
    omega
  have hMid_lo : lay.staticEnd ≤ hMid := le_trans hOld_lo (le_trans (Nat.le_add_right _ _) hle_hm)
  have hOff_eUpd : lay.base + t3OffEcongUpd < lay.base + t3HdrSize := by
    unfold t3OffEcongUpd t3HdrSize; omega
  let hInv : ℕ → State → ℕ → Prop := fun k st Φ =>
    T3EdgeStepInv ctx lay rCur eJ ci hci hOld hMid P d0 reps1 memStart regsInit k st Φ
  have hloop := PTriple.forRange_const (w := w) (p := p) (P := Pre)
    (r := 25) (lo := .const 0) (hi := .reg 15) (body := edgeStep) (Inv := hInv)
    106 0 P.edges.length (Nat.zero_le _) hw1 (fun _ => hPe_w)
    (fun s Φ' ⟨hmem, hregs, hΦ⟩ => by
      subst hmem
      refine ⟨Expr.eval_const (by omega), Nat.zero_le _,
        fun r hr hne => by
          show Function.update s.regs 25 0 r = regsInit r
          rw [Function.update_of_ne (by omega), hregs],
        by show Function.update s.regs 25 0 25 = 0; exact Function.update_self _ _ _,
        fun _ _ _ _ _ _ => rfl, fun _ _ => rfl, hECnt_eq_mem,
        fun _ hi _ => absurd hi (Nat.not_lt_zero _), [], ?_⟩
      simp only [List.length_nil, List.take_zero, add_zero, tsub_zero]
      refine ⟨by show Function.update s.regs 25 0 18 = 0; rw [Function.update_of_ne (by decide), hregs]; exact hregsInit.2.2.2.2.2.2.2.1,
        Nat.zero_le _, List.nodup_nil, listAt_nil _ _,
        fun _ h => by simp at h,
        fun eW heW => (hECnt_d0 eW heW).trans (t3_econg_eq_take_zero hunemb eW).symm,
        fun eW heW => by
          have h1 := hEc_rnd eW heW
          have hcn := t3_econg_eq_take_zero (J := inp.J) (verts := (liftWSubWalk ctx.wd.comps[ci] P).verts) hunemb eW
          dsimp only [econgAt] at h1 ⊢; simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h1 ⊢; rwa [hcn],
        hWdel_c,
        fun eW heW hs => by
          have h1 := hWdel_t eW heW hs
          have hcn := t3_econg_eq_take_zero (J := inp.J) (verts := (liftWSubWalk ctx.wd.comps[ci] P).verts) hunemb eW
          dsimp only [econgAt] at h1 ⊢; simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h1 ⊢; rwa [hcn],
        fun eW heW hlt => by
          have h1 := hWdel_lt eW heW hlt
          have hcn := t3_econg_eq_take_zero (J := inp.J) (verts := (liftWSubWalk ctx.wd.comps[ci] P).verts) hunemb eW
          dsimp only [econgAt] at h1 ⊢; simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h1 ⊢; rwa [hcn],
        hUpd_sum,
        fun cj hcj eL heL => by simp [hDel_iff cj hcj eL heL],
        by simpa using hΦ⟩)
    (fun _ _ _ _ _ h => h.reg_25)
    (fun _ _ _ _ _ h => Expr.eval_reg_of_eq ((h.regs_hi 15 (by decide) (by decide)).trans hregsInit.2.2.2.2.2.1))
    (fun k _ hk s Φ' ω' hIk => by
      rcases hIk with ⟨_, hr_hi, hr25, hma, hwdel_j0, heUpd, hwe, Q, hr18, hQk, hQnd, hQL, hQval,
        hCnt_eq, hEc_r, hWdc, hWdt, hWdlt, hUsum, hDQ, hΦ⟩
      let P_lift := liftWSubWalk ctx.wd.comps[ci] P
      have hPl_len : k < P_lift.edges.length := by simpa [P_lift, liftWSubWalk] using hk
      let eL := P.edges[k]'hk
      let eW := ctx.wd.comps[ci].wStart + eL
      have heW_eq : P_lift.edges[k]'hPl_len = eW := by simp [P_lift, liftWSubWalk, eL, eW]
      have heW_mem : eW ∈ P_lift.edges := heW_eq ▸ List.getElem_mem hPl_len
      have heW_Ico : eW ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m :=
        Finset.mem_Ico.mpr (hPl_w.2.2.2 _ heW_mem)
      have heW_lo : ctx.wd.j0Edges.length ≤ eW := (Finset.mem_Ico.mp heW_Ico).1
      have heW_hi : eW < ctx.wd.W.m := (Finset.mem_Ico.mp heW_Ico).2
      have hst := t3EdgeStep_static_lt_addr ctx lay hlay heW_hi
      have hm_eL : s.mem (hOld + (2 + P.verts.length + k)) = eL := by
        have hlt_mid : hOld + (2 + P.verts.length + k) < hMid + 2 + P.verts.length := by omega
        have hst_le : lay.staticEnd ≤ hOld + (2 + P.verts.length + k) := by omega
        have hagr : s.mem (hOld + (2 + P.verts.length + k)) = memStart (hOld + (2 + P.verts.length + k)) :=
          hma _ (fun h => by omega) (fun h => by omega) (fun h => by omega) (fun h => by omega) (fun h => by omega)
        rw [hagr]
        simpa [Nat.add_assoc] using listAt_getElem (walkAt_iff.mp hWalk_st).2.2.2 hk
      have hr0 : s.regs 0 = lay.base := (hr_hi 0 (by decide) (by decide)).trans hregsInit.1
      have hr1 : s.regs 1 = rCur := (hr_hi 1 (by decide) (by decide)).trans hregsInit.2.1
      have hr11 : s.regs 11 = hOld := (hr_hi 11 (by decide) (by decide)).trans hregsInit.2.2.1
      have hr13 : s.regs 13 = hMid := (hr_hi 13 (by decide) (by decide)).trans hregsInit.2.2.2.1
      have hr14 : s.regs 14 = P.verts.length := (hr_hi 14 (by decide) (by decide)).trans hregsInit.2.2.2.2.1
      have hr17 : s.regs 17 = ctx.wd.comps[ci].wStart := (hr_hi 17 (by decide) (by decide)).trans hregsInit.2.2.2.2.2.2.1
      have hr19 : s.regs 19 = ctx.memT1 (ctx.wInp.h + 14) := (hr_hi 19 (by decide) (by decide)).trans hregsInit.2.2.2.2.2.2.2.2.1
      have hr20 : s.regs 20 = ctx.wInp.prep.phiDen_dec := (hr_hi 20 (by decide) (by decide)).trans hregsInit.2.2.2.2.2.2.2.2.2.1
      have hr21 : s.regs 21 = rCur * ctx.wInp.tau2Int impl.constructExpander impl.pathDS.params := (hr_hi 21 (by decide) (by decide)).trans hregsInit.2.2.2.2.2.2.2.2.2.2.1
      have hr22 : s.regs 22 = lay.econgCountAddr := (hr_hi 22 (by decide) (by decide)).trans hregsInit.2.2.2.2.2.2.2.2.2.2.2.1
      have hr23 : s.regs 23 = lay.wDelStampAddr := (hr_hi 23 (by decide) (by decide)).trans hregsInit.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hr24 : s.regs 24 = lay.queueAddr := (hr_hi 24 (by decide) (by decide)).trans hregsInit.2.2.2.2.2.2.2.2.2.2.2.2.2
      have heW_w : eW < 2 ^ w := by
        have := ctx.hmW_le; have : 3 * Task1Input.mwCap impl inp.J + 2 * inp.J.m + 4 ≤ Task3Input.maxWordBound impl inp := by
          unfold Task3Input.maxWordBound; exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
        omega
      have hBase_w : hMid + 2 + P.verts.length + k < 2 ^ w := by omega
      have hOld_addr_w : hOld + (2 + P.verts.length + k) < 2 ^ w := by omega
      have h2v_w : 2 + P.verts.length < 2 ^ w := by omega
      have h2vk_w : 2 + P.verts.length + k < 2 ^ w := by omega
      have hhdl_eUpd_w : lay.base + t3OffEcongUpd < 2 ^ w := by omega
      have hOff_lt_w : t3OffEcongUpd < 2 ^ w := by omega
      have heUpd_next_w : d0.econgUpd + k + 1 < 2 ^ w := by
        have h1 := heUpd_W
        have h2 : d0.getPathCnt < inp.J.m := by
          have hmem : eJ ∈ unembeddedSet2Pure inp.J d0.emb := by simp [unembeddedSet2Pure, heJ, hunemb]
          have hc := Finset.card_pos.mpr ⟨eJ, hmem⟩
          omega
        set γW := impl.pathDS.params.gExp (WitnessCoreInput.dWInt impl.constructExpander) (Task1Input.mwCap impl inp.J)
        have hm := Nat.mul_le_mul_right γW (show d0.getPathCnt + 1 ≤ inp.J.m by omega)
        have hds1 : 1 ≤ Task3Input.dsOneW impl inp.J := by
          unfold Task3Input.dsOneW
          have hc := impl.pathDS.params.hC_space
          exact Nat.le_trans hc (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega)))
        have hm2 : inp.J.m * γW ≤ inp.J.m * γW * Task3Input.dsOneW impl inp.J := Nat.le_mul_of_pos_right _ hds1
        have hm3 : inp.J.m * γW * Task3Input.dsOneW impl inp.J ≤ Task3Input.maxHeapEnd impl inp := by
          unfold Task3Input.maxHeapEnd
          dsimp only [γW]
          linarith [Nat.mul_le_mul_right (Task3Input.dsOneW impl inp.J)
            (show inp.J.m * impl.pathDS.params.gExp (WitnessCoreInput.dWInt impl.constructExpander) (Task1Input.mwCap impl inp.J) ≤
              eta2Bound inp.J * inp.J.m + inp.J.m +
              inp.J.m * impl.pathDS.params.gExp (WitnessCoreInput.dWInt impl.constructExpander) (Task1Input.mwCap impl inp.J) by omega)]
        have hle1 : d0.econgUpd + P.edges.length ≤ inp.J.m * γW := by
          have : (d0.getPathCnt + 1) * γW = d0.getPathCnt * γW + γW := by ring
          omega
        have : Task3Input.maxHeapEnd impl inp + 3 ≤ Task3Input.maxWordBound impl inp := le_max_left _ _
        omega
      have hphi_pd : ctx.wInp.prep.phiDen_dec ≤ Task1Input.phiDenCap impl inp.J := by
        unfold Task1Input.phiDenCap
        rw [← ctx.hWInpJ, ← ctx.hStat.2.2.1]
        exact ctx.hφ_max
      have hcnt_new_w : s.mem (lay.econgCountAddr + eW) + 1 < 2 ^ w := by
        have hcnt_old : s.mem (lay.econgCountAddr + eW) ≤ inp.J.m := by
          rw [hCnt_eq eW heW_hi]
          exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp [Finset.card_range])
        have h2 : inp.J.m * Task1Input.phiDenCap impl inp.J + 2 ≤ Task3Input.maxWordBound impl inp := by
          unfold Task3Input.maxWordBound
          exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
        have h3 : 1 ≤ Task1Input.phiDenCap impl inp.J := by
          have := ctx.hStat.2.2.2.2.2.2.2.2.1
          have := ctx.hStat.2.2.2.2.2.2.2.2.2.1
          omega
        have h4 : inp.J.m ≤ inp.J.m * Task1Input.phiDenCap impl inp.J := Nat.le_mul_of_pos_right _ h3
        omega
      have hro := ctx.read_out_fields (mem := memStart) hStatic_st.1
      have hwW_props := hro.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 eW heW_hi
      have hwW_agree : s.mem (ctx.memT1 (ctx.wInp.h + 14) + eW) = memStart (ctx.memT1 (ctx.wInp.h + 14) + eW) :=
        hma _ (by omega) (by omega) (by omega) (by omega) (by omega)
      let wWNum := s.mem (ctx.memT1 (ctx.wInp.h + 14) + eW)
      have hwW_div : (wWNum : ℝ) / (ctx.wInp.prep.phiDen_dec : ℝ) = ctx.wd.wW eW := by
        dsimp only [wWNum]; rw [hwW_agree]; exact hwW_props.1
      have hwW_bd : 1 ≤ wWNum ∧ wWNum ≤ maxDeg inp.J * ctx.wInp.prep.phiDen_dec := by
        dsimp only [wWNum]; rw [hwW_agree]; exact hwW_props.2
      have htau_bd : ctx.wInp.tau2Int impl.constructExpander impl.pathDS.params ≤ Task1Input.tau2Cap impl inp.J :=
        ctx.htau2_le_cap
      have hprod_L : (rCur * ctx.wInp.tau2Int impl.constructExpander impl.pathDS.params) * wWNum < 2 ^ w := by
        have hm1 : rCur * ctx.wInp.tau2Int impl.constructExpander impl.pathDS.params ≤
            eta2Bound inp.J * Task1Input.tau2Cap impl inp.J := Nat.mul_le_mul hrCur_le htau_bd
        have hm2 : wWNum ≤ maxDeg inp.J * Task1Input.phiDenCap impl inp.J :=
          le_trans hwW_bd.2 (Nat.mul_le_mul_left _ hphi_pd)
        have hmul := Nat.mul_le_mul hm1 hm2
        have hmw : eta2Bound inp.J * Task1Input.tau2Cap impl inp.J * maxDeg inp.J * Task1Input.phiDenCap impl inp.J + 2 ≤
            Task3Input.maxWordBound impl inp := by
          unfold Task3Input.maxWordBound
          exact le_trans (le_max_left _ _) (le_max_right _ _)
        have hassoc : (eta2Bound inp.J * Task1Input.tau2Cap impl inp.J) * (maxDeg inp.J * Task1Input.phiDenCap impl inp.J) =
            eta2Bound inp.J * Task1Input.tau2Cap impl inp.J * maxDeg inp.J * Task1Input.phiDenCap impl inp.J := by
          ring
        omega
      let cntNew := s.mem (lay.econgCountAddr + eW) + 1
      have hcntNew_le_Jm : cntNew ≤ inp.J.m := by
        dsimp only [cntNew]
        have hecn := t3_econg_eq_take_step heJ hunemb hPl_nd hPl_len
        rw [heW_eq] at hecn
        have hle_j : {j ∈ Finset.range inp.J.m | eW ∈ (partialToWalk
            (Function.update d0.emb eJ (some ⟨P_lift.verts, P_lift.edges.take (k + 1)⟩)) j).edges}.card ≤ inp.J.m :=
          (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp [Finset.card_range])
        rw [hCnt_eq eW heW_hi, ← hecn.1]
        exact hle_j
      have hprod_R : cntNew * ctx.wInp.prep.phiDen_dec < 2 ^ w := by
        have hm := Nat.mul_le_mul hcntNew_le_Jm hphi_pd
        have hmw : inp.J.m * Task1Input.phiDenCap impl inp.J + 2 ≤ Task3Input.maxWordBound impl inp := by
          unfold Task3Input.maxWordBound
          exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
        omega
      have heW_not_Q : eW ∉ Q := by
        intro hmem
        obtain ⟨j, _, hjP, hje⟩ := (hQval eW hmem).1
        have hinj := (List.nodup_iff_injective_getElem.mp hPl_nd) (a₁ := ⟨j, hjP⟩) (a₂ := ⟨k, hPl_len⟩) (hje.trans heW_eq.symm)
        simp at hinj; omega
      have heW_lt_r : s.mem (lay.wDelStampAddr + eW) < rCur := by
        have hc := (hWdc eW heW_Ico).1
        have hnd := hP_ndel eL (List.getElem_mem hk)
        have hiff := hDQ ci hci eL (by
          rcases hP_wk with ⟨_, _, ⟨_, hee, _⟩ | ⟨_, _, _, _, hlt, _⟩⟩
          · rw [hee] at hk; simp at hk
          · exact hlt eL (List.getElem_mem hk))
        have hne_r : s.mem (lay.wDelStampAddr + eW) ≠ rCur := by
          intro heq
          exact hnd (hiff.mpr ⟨by simpa [eW, eL] using heq, heW_not_Q⟩)
        omega
      let r26 := Function.update s.regs 26 eL
      let r27 := Function.update r26 27 eW
      let mem1 := Function.update s.mem (hMid + 2 + P.verts.length + k) eW
      let mem2 := Function.update mem1 (lay.base + t3OffEcongUpd) (d0.econgUpd + k + 1)
      let r28 := Function.update r27 28 cntNew
      let mem3 := Function.update mem2 (lay.econgCountAddr + eW) cntNew
      let r29 := Function.update r28 29 ((rCur * ctx.wInp.tau2Int impl.constructExpander impl.pathDS.params) * wWNum)
      let r30 := Function.update r29 30 (cntNew * ctx.wInp.prep.phiDen_dec)
      have hm3p := t3EdgeStep_mem3_props ctx lay hlay (pv := P.verts.length)
        (u := d0.econgUpd + k + 1) (c := cntNew) s.mem hPe_le_Wm hk heW_hi hMid_lo
      have hm3_cnt : ∀ eW' < ctx.wd.W.m, eW' ≠ eW → mem3 (lay.econgCountAddr + eW') = s.mem (lay.econgCountAddr + eW') := hm3p.1
      have hm3_wdel : ∀ eW' < ctx.wd.W.m, mem3 (lay.wDelStampAddr + eW') = s.mem (lay.wDelStampAddr + eW') := hm3p.2.1
      have hm3_q : ∀ i < k, mem3 (lay.queueAddr + i) = s.mem (lay.queueAddr + i) := hm3p.2.2.1
      have hm3_eUpd : mem3 (lay.base + t3OffEcongUpd) = d0.econgUpd + k + 1 := hm3p.2.2.2.2.2.2.2.1
      have hm3_eW : mem3 (lay.econgCountAddr + eW) = cntNew := hm3p.2.2.2.2.2.2.2.2.1
      have hwW_m3 : mem3 (ctx.memT1 (ctx.wInp.h + 14) + eW) = wWNum :=
        hm3p.2.2.2.2.2.2.2.2.2.2.2 _ (by omega) (by omega) (by omega) (by omega) (by omega)
      have hwdel_m3 : mem3 (lay.wDelStampAddr + eW) = s.mem (lay.wDelStampAddr + eW) := hm3_wdel eW heW_hi
      have hecnt_add_w : lay.econgCountAddr + eW < 2 ^ w := by omega
      have hwdel_add_w : lay.wDelStampAddr + eW < 2 ^ w := by omega
      have hq_add_w : lay.queueAddr + Q.length < 2 ^ w := by omega
      have hwW_add_w : ctx.memT1 (ctx.wInp.h + 14) + eW < 2 ^ w := by omega
      have hev26 : (t3Ld (.reg 11) (t3Add (t3Add (.const 2) (.reg 14)) (.reg 25))).eval w s = some eL :=
        hm_eL ▸ Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq hr11)
          (Expr.eval_add (Expr.eval_add (Expr.eval_const hw2_w) (Expr.eval_reg_of_eq hr14) h2v_w)
            (Expr.eval_reg_of_eq hr25) h2vk_w) hOld_addr_w)
      have hev_eUpd : (t3Add (t3Ld (.reg 0) (.const t3OffEcongUpd)) (.const 1)).eval w
          ⟨mem1, r27, s.pos⟩ = some (d0.econgUpd + k + 1) := by
        have hr27_0 : r27 0 = lay.base := by dsimp only [r27, r26]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr0]
        exact Expr.eval_add ((hm3p.2.2.2.2.2.2.2.2.2.2.1.trans heUpd) ▸ Expr.eval_load (Expr.eval_add
          (Expr.eval_reg_of_eq hr27_0) (Expr.eval_const hOff_lt_w) hhdl_eUpd_w))
          (Expr.eval_const hw1) heUpd_next_w
      have hr27_22 : r27 22 = lay.econgCountAddr := by dsimp only [r27, r26]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr22]
      have hr27_27 : r27 27 = eW := Function.update_self _ _ _
      have hev28 : (t3Add (.load (t3Add (.reg 22) (.reg 27))) (.const 1)).eval w ⟨mem2, r27, s.pos⟩ = some cntNew :=
        Expr.eval_add (hm3p.2.2.2.2.2.2.2.2.2.1 ▸ Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq hr27_22) (Expr.eval_reg_of_eq hr27_27) hecnt_add_w)) (Expr.eval_const hw1) hcnt_new_w
      have hr28_22 : r28 22 = lay.econgCountAddr := by dsimp only [r28]; rw [Function.update_of_ne (by decide), hr27_22]
      have hr28_27 : r28 27 = eW := by dsimp only [r28]; rw [Function.update_of_ne (by decide), hr27_27]
      have hr28_28 : r28 28 = cntNew := Function.update_self _ _ _
      have hr28_21 : r28 21 = rCur * ctx.wInp.tau2Int impl.constructExpander impl.pathDS.params := by dsimp only [r28, r27, r26]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr21]
      have hr28_19 : r28 19 = ctx.memT1 (ctx.wInp.h + 14) := by dsimp only [r28, r27, r26]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr19]
      have hr29_28 : r29 28 = cntNew := by dsimp only [r29]; rw [Function.update_of_ne (by decide), hr28_28]
      have hr29_20 : r29 20 = ctx.wInp.prep.phiDen_dec := by dsimp only [r29, r28, r27, r26]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr20]
      have hev29 : (t3Mul (.reg 21) (.load (t3Add (.reg 19) (.reg 27)))).eval w ⟨mem3, r28, s.pos⟩ =
          some ((rCur * ctx.wInp.tau2Int impl.constructExpander impl.pathDS.params) * wWNum) :=
        Expr.eval_mul (Expr.eval_reg_of_eq hr28_21) (hwW_m3 ▸ Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq hr28_19) (Expr.eval_reg_of_eq hr28_27) hwW_add_w)) hprod_L
      have hev30 : (t3Mul (.reg 28) (.reg 20)).eval w ⟨mem3, r29, s.pos⟩ = some (cntNew * ctx.wInp.prep.phiDen_dec) :=
        Expr.eval_mul (Expr.eval_reg_of_eq hr29_28) (Expr.eval_reg_of_eq hr29_20) hprod_R
      have hr30_lt25 : ∀ r ≤ 25, r ≠ 18 → r30 r = s.regs r := fun r hr h18 => by
        dsimp only [r30, r29, r28, r27, r26]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      have hr30_18 : r30 18 = Q.length := by dsimp only [r30, r29, r28, r27, r26]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr18]
      have hemb_step := t3_econg_eq_take_step heJ hunemb hPl_nd hPl_len
      rw [heW_eq] at hemb_step
      have hcnt3_eq : ∀ eW' < ctx.wd.W.m, mem3 (lay.econgCountAddr + eW') =
          {j ∈ Finset.range inp.J.m | eW' ∈ (partialToWalk
            (Function.update d0.emb eJ (some ⟨P_lift.verts, P_lift.edges.take (k + 1)⟩)) j).edges}.card := by
        intro eW' heW'
        by_cases heq : eW' = eW
        · have hm_self : mem3 (lay.econgCountAddr + eW) = cntNew := hm3p.2.2.2.2.2.2.2.2.1
          rw [heq]; refine hm_self.trans ?_
          dsimp only [cntNew]; rw [hCnt_eq eW heW_hi, hemb_step.1]
        · exact (hm3p.1 eW' heW' heq).trans ((hCnt_eq eW' heW').trans (hemb_step.2 eW' heq).symm)
      have hecong_new_eq : ∀ eW' < ctx.wd.W.m, eW' ≠ eW →
          econgAt inp.J (fun _ => 1) ctx.wd.wW
            (partialToWalk (Function.update d0.emb eJ (some ⟨P_lift.verts, P_lift.edges.take (k + 1)⟩))) eW' =
          econgAt inp.J (fun _ => 1) ctx.wd.wW
            (partialToWalk (Function.update d0.emb eJ (some ⟨P_lift.verts, P_lift.edges.take k⟩))) eW' := fun eW' _ hne => by
        simp only [econgAt, Finset.sum_const, nsmul_eq_mul, mul_one, P_lift]
        have h2 := hemb_step.2 eW' hne
        dsimp only at h2
        rw [h2]
      have hds_phi_fn : ∀ (mA : ℕ → ℕ),
          (∀ a, lay.staticEnd ≤ a → a ≠ hMid + 2 + P.verts.length + k → mA a = s.mem a) →
          (∀ cj < ctx.wd.comps.length, mA (lay.dsHandlesAddr + cj) = s.mem (lay.dsHandlesAddr + cj)) →
          dsTotalPhi impl.pathDS lay.dsHandlesAddr ctx.wd.comps.length reps1 mA =
          dsTotalPhi impl.pathDS lay.dsHandlesAddr ctx.wd.comps.length reps1 s.mem := fun mA hmA hmH => by
        unfold dsTotalPhi
        refine Finset.sum_congr rfl fun cj hcj => ?_
        have hcj' := Finset.mem_range.mp hcj
        have hds_c : s.mem (lay.dsHandlesAddr + cj) = memStart (lay.dsHandlesAddr + cj) :=
          hma _ (by omega) (by omega) (by omega) (by omega) (by omega)
        rw [hmH cj hcj']
        refine (hLoc (s.mem (lay.dsHandlesAddr + cj)) (d0.states cj) (reps1 cj) s.mem mA fun a ha => ?_).2.symm
        rw [hds_c] at ha
        have hab := hDS_foot cj hcj' a ha
        exact (hmA a hab.1 (by omega)).symm
      have hds_m3 := hds_phi_fn mem3 hm3p.2.2.2.2.1 hm3p.2.2.2.1
      have hUsum3 : d0.econgUpd + (k + 1) =
          ∑ x ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m, mem3 (lay.econgCountAddr + x) := by
        rw [← Finset.add_sum_erase _ _ heW_Ico] at hUsum
        rw [← Finset.add_sum_erase _ _ heW_Ico]
        have hrest : ∑ x ∈ (Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m).erase eW, mem3 (lay.econgCountAddr + x) =
            ∑ x ∈ (Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m).erase eW, s.mem (lay.econgCountAddr + x) := by
          refine Finset.sum_congr rfl fun x hx => ?_
          rcases Finset.mem_erase.mp hx with ⟨hne, hmem⟩
          exact hm3p.1 x (Finset.mem_Ico.mp hmem).2 hne
        have hm3_eW : mem3 (lay.econgCountAddr + eW) = cntNew := hm3p.2.2.2.2.2.2.2.2.1
        rw [hrest, hm3_eW]; dsimp only [cntNew]; omega
      have hc_cond : ∃ o stF c_c Φ'',
          Runs w p ω' (.cond (t3Lt (.reg 30) (.reg 29)) .nop
            (.cond (t3Lt (.load (t3Add (.reg 23) (.reg 27))) (.reg 1))
              (Stmt.seq (.store (t3Add (.reg 23) (.reg 27)) (.reg 1))
                (Stmt.seq (.store (t3Add (.reg 24) (.reg 18)) (.reg 27))
                  (.assign 18 (t3Add (.reg 18) (.const 1)))))
              .nop)) ⟨mem3, r30, s.pos⟩ o stF c_c ∧
          (o = .normal ∧ T3EdgeStepInv ctx lay rCur eJ ci hci hOld hMid P d0 reps1 memStart regsInit (k + 1)
            { stF with regs := Function.update stF.regs 25 (k + 1) } Φ'' ∧ stF.regs 25 = k) ∧
          c_c + Φ'' ≤ 31 + Φ' := by
        have hr30_30 : r30 30 = cntNew * ctx.wInp.prep.phiDen_dec := Function.update_self _ _ _
        have hr30_29 : r30 29 = (rCur * ctx.wInp.tau2Int impl.constructExpander impl.pathDS.params) * wWNum := by
          dsimp only [r30]; rw [Function.update_of_ne (by decide)]; exact Function.update_self _ _ _
        have hev_cond : (t3Lt (.reg 30) (.reg 29)).eval w ⟨mem3, r30, s.pos⟩ =
            some (if cntNew * ctx.wInp.prep.phiDen_dec <
              (rCur * ctx.wInp.tau2Int impl.constructExpander impl.pathDS.params) * wWNum then 1 else 0) :=
          Expr.eval_lt_op (Expr.eval_reg_of_eq hr30_30) (Expr.eval_reg_of_eq hr30_29) hw1
        have hm3_eW' : mem3 (lay.econgCountAddr + eW) = cntNew := hm3p.2.2.2.2.2.2.2.2.1
        have hw_okWInp : ∀ {N_max : ℕ} {W_max : ℝ} (t : LocalSpannerTools N_max W_max),
            WitnessOK t ctx.wInp.H' ctx.wInp.prep.J ctx.wInp.embJH ctx.wd := by
          intro N_max W_max t; have h := ctx.hw_ok t; rw [← ctx.hWInpJ] at h
          exact ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12, h.13,
            h.14, h.15, h.16, h.17, h.18, h.19, h.20, h.21, h.22⟩
        have hthresh_iff := t3_thresh_le_econg_iff
          (emb := partialToWalk (Function.update d0.emb eJ (some ⟨P_lift.verts, P_lift.edges.take (k + 1)⟩)))
          (hok := hw_okWInp) ctx.hws (eW := eW) (r := rCur) (cnt := cntNew) (wWNum := wWNum)
          heW_hi (by have := ctx.hStat.2.2.2.2.2.2.2.2.1; have := ctx.hStat.2.2.2.2.2.2.2.2.2.1; omega)
          hwW_div ctx.hds_bounds.2.2.2.2.2.2 (by
            dsimp only [econgAt]
            rw [Finset.sum_const, nsmul_eq_mul, mul_one, ctx.hWInpJ, ← hcnt3_eq eW heW_hi, hm3_eW'])
        rw [ctx.hWInpJ] at hthresh_iff
        have hm_new_rnd : econgAt inp.J (fun _ => 1) ctx.wd.wW (partialToWalk
            (Function.update d0.emb eJ (some ⟨P_lift.verts, P_lift.edges.take (k + 1)⟩))) eW ≤
            ((rCur : ℝ) + 1 / 2) * ctx.wd.τ₂ := by
          have hold_lt := hWdlt eW heW_Ico heW_lt_r
          have hc_old := hCnt_eq eW heW_hi
          dsimp only [econgAt] at hold_lt ⊢
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one, P_lift] at hold_lt hc_old ⊢
          have hres := t3_edgeStep_econg_le_round hw_okWInp ctx.hws (rCur := rCur)
            (cntOld := s.mem (lay.econgCountAddr + eW)) heW_lo heW_hi (by rw [hc_old]; exact hold_lt)
          have hc3 := hcnt3_eq eW heW_hi
          dsimp only [P_lift] at hc3
          rw [← hc3, hm3_eW]; exact hres
        by_cases hlt : cntNew * ctx.wInp.prep.phiDen_dec <
            (rCur * ctx.wInp.tau2Int impl.constructExpander impl.pathDS.params) * wWNum
        · have hc_eq : (if cntNew * ctx.wInp.prep.phiDen_dec <
              (rCur * ctx.wInp.tau2Int impl.constructExpander impl.pathDS.params) * wWNum then 1 else 0) = 1 :=
            ite_eq_left_iff.mpr fun h => absurd hlt h
          have hnot_le : ¬ (rCur : ℝ) * ctx.wd.τ₂ ≤
              econgAt inp.J (fun _ => 1) ctx.wd.wW (partialToWalk
                (Function.update d0.emb eJ (some ⟨P_lift.verts, P_lift.edges.take (k + 1)⟩))) eW := by
            dsimp only [P_lift]; intro h; exact Nat.not_le_of_lt hlt (hthresh_iff.mpr h)
          have hePhi3 : t3EcongPhi ctx lay mem3 = t3EcongPhi ctx lay s.mem + 1 :=
            t3_econgPhi_step_inc ctx lay heW_Ico hm3p.2.2.2.2.2.2.2.2.1
              (fun eW' heW' hne => hm3p.1 eW' (Finset.mem_Ico.mp heW').2 hne)
              (hm3p.2.1 eW heW_hi) (fun eW' heW' _ => hm3p.2.1 eW' (Finset.mem_Ico.mp heW').2)
              (hWdc eW heW_Ico).2
          refine ⟨.normal, ⟨mem3, r30, s.pos⟩, 5, Φ',
            runs_cond_iff.mpr ⟨1, 1, hc_eq ▸ hev_cond, runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by simp [Expr.size, t3Lt]⟩,
            ⟨rfl, ⟨hk,
              fun r hr h18 => by show Function.update r30 25 (k + 1) r = regsInit r; rw [Function.update_of_ne (by omega)]; exact (hr30_lt25 r (by omega) h18).trans (hr_hi r hr h18),
              by show Function.update r30 25 (k + 1) 25 = k + 1; exact Function.update_self _ _ _,
              fun a h1 h2 h3 h4 h5 => (hm3p.2.2.2.2.2.2.2.2.2.2.2 a h1 h2 h3 h4 h5).trans (hma a h1 h2 h3 h4 h5),
              fun eW' heW' => (hm3_wdel eW' (by omega)).trans (hwdel_j0 eW' heW'),
              hm3_eUpd,
              fun i hi1 hi2 => by
                by_cases hik : i = k
                · subst hik; exact hm3p.2.2.2.2.2.2.1
                · exact (hm3p.2.2.2.2.2.1 i (by omega)).trans (hwe i (by omega) hi2),
              Q, by show Function.update r30 25 (k + 1) 18 = Q.length; rw [Function.update_of_ne (by decide), hr30_18],
              by omega, hQnd, fun i hi => (hm3_q i (by omega)).trans (hQL i hi),
              fun e' he' => by
                have hq := hQval e' he'; rcases hq.1 with ⟨j, hj1, hj2, hj3⟩
                exact ⟨⟨j, by omega, hj2, hj3⟩, hq.2.1, hq.2.2.1, (hm3_wdel e' hq.2.2.1).trans hq.2.2.2⟩,
              hcnt3_eq,
              fun eW' heW' => by
                by_cases h : eW' = eW
                · subst h; exact hm_new_rnd
                · rw [hecong_new_eq eW' heW' h]; exact hEc_r eW' heW',
              fun eW' heW' => by
                have hwc := hWdc eW' heW'
                dsimp only; rw [hm3_wdel eW' (Finset.mem_Ico.mp heW').2]; refine ⟨hwc.1, ?_⟩
                by_cases h : eW' = eW
                · subst h; rw [hm3_eW]; exact Nat.le_trans hwc.2 (Nat.le_succ _)
                · rw [hm3_cnt eW' (Finset.mem_Ico.mp heW').2 h]; exact hwc.2,
              fun eW' heW' hs => by
                dsimp only at hs; rw [hm3_wdel eW' (Finset.mem_Ico.mp heW').2] at hs
                by_cases h : eW' = eW
                · subst h; exact absurd hs (ne_of_lt heW_lt_r)
                · rw [hecong_new_eq eW' (Finset.mem_Ico.mp heW').2 h]; exact hWdt eW' heW' hs,
              fun eW' heW' hlt' => by
                dsimp only at hlt'; rw [hm3_wdel eW' (Finset.mem_Ico.mp heW').2] at hlt'
                by_cases h : eW' = eW
                · subst h; exact le_of_lt (lt_of_not_ge hnot_le)
                · rw [hecong_new_eq eW' (Finset.mem_Ico.mp heW').2 h]; exact hWdlt eW' heW' hlt',
              hUsum3,
              fun cj hcj eL' heL' => by
                have hc_b := (ctx.hw_okW.comp_props cj hcj).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
                dsimp only; rw [hm3_wdel _ (Nat.lt_of_lt_of_le (Nat.add_lt_add_left heL' _) hc_b.2)]; exact hDQ cj hcj eL' heL',
              by rw [hePhi3, hds_m3, hΦ]; congr 1; congr 1; congr 1; exact Nat.sub_add_cancel (Nat.le_of_lt hk) |> fun h => by omega⟩, (hr30_lt25 25 (le_refl _) (by decide)).trans hr25⟩,
            by omega⟩
        · have hc_eq : (if cntNew * ctx.wInp.prep.phiDen_dec <
              (rCur * ctx.wInp.tau2Int impl.constructExpander impl.pathDS.params) * wWNum then 1 else 0) = 0 :=
            ite_eq_right_iff.mpr fun h => absurd h hlt
          have hge_thresh : (rCur : ℝ) * ctx.wd.τ₂ ≤
              econgAt inp.J (fun _ => 1) ctx.wd.wW (partialToWalk
                (Function.update d0.emb eJ (some ⟨P_lift.verts, P_lift.edges.take (k + 1)⟩))) eW := by
            dsimp only [P_lift]; exact hthresh_iff.mp (Nat.not_lt.mp hlt)
          have hr_le_cnt : rCur ≤ cntNew := by
            have hc3 := hcnt3_eq eW heW_hi
            dsimp only [econgAt, P_lift] at hge_thresh hc3
            simp only [Finset.sum_const, nsmul_eq_mul, mul_one, ← hc3, hm3_eW] at hge_thresh
            exact t3_edgeStep_rCur_le_cnt hw_okWInp ctx.hws heW_lo heW_hi hge_thresh
          exact t3EdgeStep_push_branch ctx lay hlay hci d0 reps1 memStart regsInit s.mem mem3 r30
            Q hk hPe_le_Wm hPl_len hMid_lo hP_wk hP_ndel hw1 hwdel_add_w hq_add_w (by omega) hQk hQnd hQL hQval
            heW_lo heW_hi heW_not_Q heW_lt_r (fun r hr h18 => (hr30_lt25 r (by omega) h18).trans (hr_hi r hr h18))
            ((hr30_lt25 25 (le_refl _) (by decide)).trans hr25) ((hr30_lt25 1 (by decide) (by decide)).trans hr1)
            hr30_18 ((hr30_lt25 23 (by decide) (by decide)).trans hr23) ((hr30_lt25 24 (by decide) (by decide)).trans hr24)
            (by dsimp only [r30, r29, r28, r27]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self])
            (hc_eq ▸ hev_cond)
            (fun a h1 h2 h3 h4 h5 => (hm3p.2.2.2.2.2.2.2.2.2.2.2 a h1 h2 h3 h4 h5).trans (hma a h1 h2 h3 h4 h5))
            hwdel_j0 hm3_eUpd
            (fun i hi1 hi2 => by
              by_cases hik : i = k
              · subst hik; exact hm3p.2.2.2.2.2.2.1
              · exact (hm3p.2.2.2.2.2.1 i (by omega)).trans (hwe i (by omega) hi2))
            hm3_q hm3_wdel hm3_cnt hm3_eW hm3_eW
            hcnt3_eq hecong_new_eq hm_new_rnd hge_thresh hr_le_cnt hEc_r hWdc hWdt hWdlt hUsum3 hDQ
            (fun mA hmA hmH => hds_phi_fn mA (fun a ha hne => (hmA a ha).trans (hm3p.2.2.2.2.1 a ha hne))
              (fun cj hcj => (hmH cj hcj).trans (hm3p.2.2.2.1 cj hcj))) hΦ
      rcases hc_cond with ⟨o, stF, c_c, Φ'', hr_c, ⟨rfl, hInv', hreg25_k⟩, hc_c⟩
      have hr26_17 : r26 17 = ctx.wd.comps[ci].wStart := by dsimp only [r26]; rw [Function.update_of_ne (by decide), hr17]
      have hr26_26 : r26 26 = eL := Function.update_self _ _ _
      have hr27_13 : r27 13 = hMid := by dsimp only [r27, r26]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr13]
      have hr27_14 : r27 14 = P.verts.length := by dsimp only [r27, r26]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr14]
      have hr27_25 : r27 25 = k := by dsimp only [r27, r26]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr25]
      have hr27_0 : r27 0 = lay.base := by dsimp only [r27, r26]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr0]
      apply t3_ptriple_of_cps
      refine t3_assign_cps (r := 26) hev26 (t3_assign_cps (r := 27) (Expr.eval_add (Expr.eval_reg_of_eq hr26_17) (Expr.eval_reg_of_eq hr26_26) heW_w) ?_)
      have hassoc_m1 : hMid + (2 + P.verts.length + k) = hMid + 2 + P.verts.length + k := by ring
      refine t3_store_cps (Expr.eval_add (Expr.eval_reg_of_eq hr27_13) (Expr.eval_add (Expr.eval_add (Expr.eval_const hw2_w) (Expr.eval_reg_of_eq hr27_14) h2v_w) (Expr.eval_reg_of_eq hr27_25) h2vk_w) (hassoc_m1.symm ▸ hBase_w)) (Expr.eval_reg_of_eq hr27_27) ?_
      rw [hassoc_m1]
      exact t3_store_cps (Expr.eval_add (Expr.eval_reg_of_eq hr27_0) (Expr.eval_const hOff_lt_w) hhdl_eUpd_w) hev_eUpd
        (t3_assign_cps (r := 28) hev28
          (t3_store_cps (Expr.eval_add (Expr.eval_reg_of_eq hr28_22) (Expr.eval_reg_of_eq hr28_27) hecnt_add_w) (Expr.eval_reg_of_eq hr28_28)
            (t3_assign_cps (r := 29) hev29
              (t3_assign_cps (r := 30) hev30
                ⟨.normal, stF, c_c, Φ'', hr_c, ⟨hInv', hreg25_k⟩, by simp only [Expr.size, t3Ld, t3Add, t3Mul]; omega⟩)))))
  exact PTriple.conseq hloop (fun _ _ h => h) (fun o st' Φ' hq => by cases o with | returned _ => exact False.elim hq | normal => exact hq)
    (fun _ => by simp only [Expr.size, Nat.sub_zero]; omega)

end MinCostFlow.Spanner
