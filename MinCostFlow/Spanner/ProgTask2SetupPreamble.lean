module

public import MinCostFlow.Spanner.ProgTask2StepsMiddle

/-!
# Word-RAM Task 2 setup proof (`task2Body` preamble through `t2InitJ0`)

This module proves the setup phase of `task2Body`:
1. Writing the 32-word Task 2 control header at `[v1, v1 + 32)`,
2. Calling `t2BuildIncBody` (`selfBase + 1`) to build `vHead` linked lists and `stc : T2StaticData ctx`,
3. Calling `t2InitJ0Body` (`selfBase + 2`) to embed `J₀` and initialize `vcongNum`,
4. Loading loop constants (`r31..r40`) and `r19 := 1`, producing `T2LoopState ctx stc 0 ... stL`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## Accumulating CPS sequencing helpers and outer-loop state predicate -/

lemma runs_seq_assign_cps {w : ℕ} {p : Program} {ω : ℕ → Bool} {r : ℕ} {e : Expr}
    {s : Stmt} {mem regs : ℕ → ℕ} {pos v k T : ℕ} {Q : Outcome → State → ℕ → Prop}
    (he : e.eval w ⟨mem, regs, pos⟩ = some v)
    (hrest : ∃ o stF c_s, Runs w p ω s ⟨mem, Function.update regs r v, pos⟩ o stF c_s ∧
      ∃ c_cont, Q o stF c_cont ∧ (k + e.size + 2) + c_s ≤ c_cont + T) :
    ∃ o stF c_tot, Runs w p ω (.seq (.assign r e) s) ⟨mem, regs, pos⟩ o stF c_tot ∧
      ∃ c_cont, Q o stF c_cont ∧ k + c_tot ≤ c_cont + T := by
  obtain ⟨o, stF, c_s, hr_s, c_cont, hq, hc⟩ := hrest
  refine ⟨o, stF, (e.size + 1) + c_s + 1, ?_, c_cont, hq, by omega⟩
  exact runs_seq_iff.mpr (Or.inr ⟨_, e.size + 1, c_s,
    runs_assign_iff.mpr ⟨v, he, rfl, rfl, rfl⟩, hr_s, rfl⟩)

lemma runs_seq_store_cps {w : ℕ} {p : Program} {ω : ℕ → Bool} {ea ev : Expr}
    {s : Stmt} {mem regs : ℕ → ℕ} {pos addr v k T : ℕ} {Q : Outcome → State → ℕ → Prop}
    (ha : ea.eval w ⟨mem, regs, pos⟩ = some addr) (he : ev.eval w ⟨mem, regs, pos⟩ = some v)
    (hrest : ∃ o stF c_s, Runs w p ω s ⟨Function.update mem addr v, regs, pos⟩ o stF c_s ∧
      ∃ c_cont, Q o stF c_cont ∧ (k + ea.size + ev.size + 2) + c_s ≤ c_cont + T) :
    ∃ o stF c_tot, Runs w p ω (.seq (.store ea ev) s) ⟨mem, regs, pos⟩ o stF c_tot ∧
      ∃ c_cont, Q o stF c_cont ∧ k + c_tot ≤ c_cont + T := by
  obtain ⟨o, stF, c_s, hr_s, c_cont, hq, hc⟩ := hrest
  refine ⟨o, stF, (ea.size + ev.size + 1) + c_s + 1, ?_, c_cont, hq, by omega⟩
  exact runs_seq_iff.mpr (Or.inr ⟨_, ea.size + ev.size + 1, c_s,
    runs_store_iff.mpr ⟨addr, v, ha, he, rfl, rfl, rfl⟩, hr_s, rfl⟩)

lemma runs_seq_ld_cps {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem regs : ℕ → ℕ} {pos rd rs off base v k T : ℕ} {s : Stmt}
    {Q : Outcome → State → ℕ → Prop}
    (hr : regs rs = base) (hoff : off < 2 ^ w) (hadd : base + off < 2 ^ w)
    (hm : mem (base + off) = v)
    (hrest : ∃ o stF c_s, Runs w p ω s ⟨mem, Function.update regs rd v, pos⟩ o stF c_s ∧
      ∃ c_cont, Q o stF c_cont ∧ (k + (t2Ld (.reg rs) (.const off)).size + 2) + c_s ≤ c_cont + T) :
    ∃ o stF c_tot, Runs w p ω (.seq (.assign rd (t2Ld (.reg rs) (.const off))) s)
      ⟨mem, regs, pos⟩ o stF c_tot ∧ ∃ c_cont, Q o stF c_cont ∧ k + c_tot ≤ c_cont + T :=
  runs_seq_assign_cps (hm ▸ Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq hr) (Expr.eval_const hoff) hadd)) hrest

lemma runs_seq_ld0_cps {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem regs : ℕ → ℕ} {pos rd rs base v k T : ℕ} {s : Stmt}
    {Q : Outcome → State → ℕ → Prop}
    (hr : regs rs = base) (hm : mem base = v)
    (hrest : ∃ o stF c_s, Runs w p ω s ⟨mem, Function.update regs rd v, pos⟩ o stF c_s ∧
      ∃ c_cont, Q o stF c_cont ∧ (k + (Expr.load (.reg rs)).size + 2) + c_s ≤ c_cont + T) :
    ∃ o stF c_tot, Runs w p ω (.seq (.assign rd (.load (.reg rs))) s) ⟨mem, regs, pos⟩ o stF c_tot ∧
      ∃ c_cont, Q o stF c_cont ∧ k + c_tot ≤ c_cont + T :=
  runs_seq_assign_cps (hm ▸ Expr.eval_load (Expr.eval_reg_of_eq hr)) hrest

lemma runs_seq_add_cps {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem regs : ℕ → ℕ} {pos rd ra rb va vb k T : ℕ} {s : Stmt}
    {Q : Outcome → State → ℕ → Prop}
    (hra : regs ra = va) (hrb : regs rb = vb) (hadd : va + vb < 2 ^ w)
    (hrest : ∃ o stF c_s, Runs w p ω s ⟨mem, Function.update regs rd (va + vb), pos⟩ o stF c_s ∧
      ∃ c_cont, Q o stF c_cont ∧ (k + (t2Add (.reg ra) (.reg rb)).size + 2) + c_s ≤ c_cont + T) :
    ∃ o stF c_tot, Runs w p ω (.seq (.assign rd (t2Add (.reg ra) (.reg rb))) s) ⟨mem, regs, pos⟩ o stF c_tot ∧
      ∃ c_cont, Q o stF c_cont ∧ k + c_tot ≤ c_cont + T :=
  runs_seq_assign_cps (Expr.eval_add (Expr.eval_reg_of_eq hra) (Expr.eval_reg_of_eq hrb) hadd) hrest

lemma runs_seq_st_cps {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem regs : ℕ → ℕ} {pos rs off rv base val k T : ℕ} {s : Stmt}
    {Q : Outcome → State → ℕ → Prop}
    (hrs : regs rs = base) (hoff : off < 2 ^ w) (hadd : base + off < 2 ^ w)
    (hrv : regs rv = val)
    (hrest : ∃ o stF c_s, Runs w p ω s ⟨Function.update mem (base + off) val, regs, pos⟩ o stF c_s ∧
      ∃ c_cont, Q o stF c_cont ∧ (k + (t2Add (.reg rs) (.const off)).size + (Expr.reg rv).size + 2) + c_s ≤ c_cont + T) :
    ∃ o stF c_tot, Runs w p ω (.seq (t2St (.reg rs) (.const off) (.reg rv)) s) ⟨mem, regs, pos⟩ o stF c_tot ∧
      ∃ c_cont, Q o stF c_cont ∧ k + c_tot ≤ c_cont + T :=
  runs_seq_store_cps (Expr.eval_add (Expr.eval_reg_of_eq hrs) (Expr.eval_const hoff) hadd)
    (Expr.eval_reg_of_eq hrv) hrest

lemma runs_seq_end_cps {w : ℕ} {p : Program} {ω : ℕ → Bool} {s : Stmt} {st : State}
    {k T : ℕ} {Q : Outcome → State → ℕ → Prop}
    (hcall : ∃ o stF c_cont, Runs w p ω s st o stF c_cont ∧ Q o stF c_cont) (hk : k ≤ T) :
    ∃ o stF c_tot, Runs w p ω s st o stF c_tot ∧
      ∃ c_cont, Q o stF c_cont ∧ k + c_tot ≤ c_cont + T :=
  let ⟨o, stF, c_cont, hr_c, hq_c⟩ := hcall
  ⟨o, stF, c_cont, hr_c, c_cont, hq_c, by omega⟩

/-- Ghost + machine state held at the `Stmt.loop (.reg 19)` header in `task2Body`.
`r_done = 0` holds before round 1 (`η₁ = 0`); `r_done ≥ 1` holds after each completed round. -/
structure T2LoopState {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx) (r_done : ℕ)
    (emb_prev emb : ℕ → Option Walk) (hCur arenaPtr deleteCountJ vcongUpdates innerIters1 : ℕ)
    (st : State) : Prop where
  hr4 : st.regs 4 = inp.v1
  hr10 : st.regs 10 = ctx.wd.comps.length
  hr12 : st.regs 12 = ctx.wd.W.m
  hr18 : st.regs 18 = hCur
  hr19 : st.regs 19 = if r_done = 0 then 1 else (unembeddedSetPure ctx.wd emb).card
  hr31 : st.regs 31 = ctx.wInp.prep.aComps
  hr32 : st.regs 32 = st.mem (ctx.wInp.h + 12)
  hr33 : st.regs 33 = ctx.wInp.prep.phiNum_dec
  hr34 : st.regs 34 = ctx.wInp.prep.phiDen_dec
  hr35 : st.regs 35 = ctx.wd.J0_strip.m
  hr36 : st.regs 36 = inp.dsHandlesAddr ctx.wd.W.m
  hr37 : st.regs 37 = inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length
  hr38 : st.regs 38 = inp.embWJAddr
  hr39 : st.regs 39 = inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length
  hr40 : st.regs 40 = ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params *
    ctx.wInp.prep.phiDen_dec
  agr_pre : ∀ a < inp.v1, st.mem a = mem₀ a
  h_v1_slots : st.mem inp.v1 = inp.embWJAddr ∧
    st.mem (inp.v1 + 1) = r_done ∧
    st.mem (inp.v1 + 2) = r_done * ctx.wd.comps.length ∧
    st.mem (inp.v1 + 3) = r_done * (ctx.wd.comps.map fun c => c.J_sub.m).sum ∧
    st.mem (inp.v1 + 4) = (ctx.wd.W.m - ctx.wd.j0Edges.length) - (unembeddedSetPure ctx.wd emb).card ∧
    st.mem (inp.v1 + 5) = deleteCountJ ∧
    st.mem (inp.v1 + 6) = vcongUpdates ∧
    st.mem (inp.v1 + 7) = innerIters1 ∧
    st.mem (inp.v1 + 8) = ctx.wd.W.m ∧
    st.mem (inp.v1 + 9) = inp.H'.n ∧
    st.mem (inp.v1 + 10) = ctx.wd.comps.length ∧
    st.mem (inp.v1 + 12) = inp.embJHAddr ∧
    st.mem (inp.v1 + 13) = ctx.wInp.prep.h ∧
    st.mem (inp.v1 + 14) = ctx.wInp.h ∧
    st.mem (inp.v1 + 15) = inp.dsHandlesAddr ctx.wd.W.m ∧
    st.mem (inp.v1 + 16) = inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length ∧
    st.mem (inp.v1 + 17) = inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length ∧
    st.mem (inp.v1 + 18) = inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length ∧
    st.mem (inp.v1 + 19) = inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length ∧
    st.mem (inp.v1 + 20) = inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length ∧
    st.mem (inp.v1 + 21) = inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length ∧
    st.mem (inp.v1 + 22) = inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length ∧
    st.mem (inp.v1 + 23) = inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length ∧
    st.mem (inp.v1 + 24) = inp.queueAddr ctx.wd.W.m ctx.wd.comps.length ∧
    st.mem (inp.v1 + 25) = arenaPtr ∧
    st.mem (inp.v1 + 26) = ctx.wd.j0Edges.length +
      ((ctx.wd.W.m - ctx.wd.j0Edges.length) - (unembeddedSetPure ctx.wd emb).card) ∧
    st.mem (inp.v1 + 27) = 0 ∧
    st.mem (inp.v1 + 28) = r_done * ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params *
      ctx.wInp.prep.phiDen_dec ∧
    st.mem (inp.v1 + 29) = ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params *
      ctx.wInp.prep.phiDen_dec ∧
    st.mem (inp.v1 + 30) = (unembeddedSetPure ctx.wd emb).card ∧
    st.mem (inp.v1 + 31) = ctx.wInp.prep.phiDen_dec
  hCeb : ∀ ci < ctx.wd.comps.length,
    st.mem (inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length + ci) = compEdgeBase ctx.wd ci
  hVho : ∀ ci < ctx.wd.comps.length,
    st.mem (inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length + ci) = vhatBase ctx.wd ci
  hDelR_le : ∀ ci (hci : ci < ctx.wd.comps.length) b, b < (ctx.wd.comps[ci]'hci).J_sub.m →
    st.mem (inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length + compEdgeBase ctx.wd ci + b) ≤ r_done
  hVhatS_le : ∀ ci (hci : ci < ctx.wd.comps.length) y, y < (ctx.wd.comps[ci]'hci).J_sub.n →
    st.mem (inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length + vhatBase ctx.wd ci + y) ≤ r_done
  hProcS_le : ∀ x < inp.H'.n,
    st.mem (inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length + x) ≤ r_done
  hInc : ∀ x < inp.H'.n,
    IncChainBound st.mem (inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length) stc.nodesEnd
      (st.mem (inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length + x)) (stc.L_inc x) ∧
    (∀ p ∈ stc.L_inc x, ∃ (hp : p.1 < ctx.wd.comps.length),
      p.2 < (ctx.wd.comps[p.1]'hp).J_sub.m ∧
      x ∈ (inp.embJH ((ctx.wd.comps[p.1]'hp).jSubOrigEdges.getD p.2 0)).verts) ∧
    (∀ (ci : ℕ) (hci : ci < ctx.wd.comps.length) (b : ℕ), b < (ctx.wd.comps[ci]'hci).J_sub.m →
      x ∈ (inp.embJH ((ctx.wd.comps[ci]'hci).jSubOrigEdges.getD b 0)).verts → (ci, b) ∈ stc.L_inc x)
  hVc : ∀ x < inp.H'.n,
    st.mem (inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + x) =
      vcongNumPure ctx.wd inp.J inp.embJH (fun i => mem₀ (mem₀ (ctx.wInp.h + 14) + i)) emb x
  hEwSt : ∀ x < inp.H'.n,
    st.mem (inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + x) ≤
      ctx.wd.j0Edges.length + ((ctx.wd.W.m - ctx.wd.j0Edges.length) - (unembeddedSetPure ctx.wd emb).card)
  hEmb : EmbInv st.mem inp.embWJAddr ctx.wd.W.m stc.nodesEnd arenaPtr emb
  hAr_lo : stc.nodesEnd ≤ arenaPtr
  hAr_le : arenaPtr ≤ stc.nodesEnd +
    (ctx.wd.j0Edges.length + ((ctx.wd.W.m - ctx.wd.j0Edges.length) - (unembeddedSetPure ctx.wd emb).card)) *
      (2 * ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params + 5)
  hGet_le : (unembeddedSetPure ctx.wd emb).card ≤ ctx.wd.W.m - ctx.wd.j0Edges.length
  hPart : IsPartialEmbedding ctx.wd.W inp.J emb
  hj0 : ∀ eW < ctx.wd.j0Edges.length, (emb eW).isSome = true
  hELen : ∀ eW < ctx.wd.W.m, ((partialToWalk emb eW).edges.length : ℝ) ≤ ctx.wd.γ_ExpPath
  hVc_cur : ∀ x < inp.H'.n,
    vcongAt ctx.wd.W ctx.wd.wW (compose inp.J inp.embJH (partialToWalk emb)) x ≤
      ((r_done : ℝ) + 1 / 2) * ctx.wd.τ₁
  hVol_cur : volWRemPure ctx.wd emb ≤
    (2 * ctx.wd.c_deg / (2 * ctx.wd.c_deg + 1)) ^ r_done * (ctx.wd.c_deg * (inp.J.m : ℝ))
  hPrev_bd : r_done = 0 → emb = emb_prev ∧ vcongUpdates = 0 ∧ innerIters1 = 0 ∧ deleteCountJ = 0
  hDel_le : deleteCountJ ≤ r_done * inp.J.m
  hVcU_le : (vcongUpdates : ℝ) ≤
    (((ctx.wd.W.m - ctx.wd.j0Edges.length) - (unembeddedSetPure ctx.wd emb).card : ℕ) : ℝ) *
      (ctx.wd.γ_ExpPath * ((length inp.J inp.embJH : ℝ) + 1))
  hInn_le : (innerIters1 : ℝ) ≤
    (((ctx.wd.W.m - ctx.wd.j0Edges.length) - (unembeddedSetPure ctx.wd emb).card : ℕ) : ℝ) *
      (ctx.wd.γ_ExpPath * ((length inp.J inp.embJH : ℝ) + 1))
  hCur_lo : stc.dsBaseAddr ≤ hCur
  hCur_le : hCur ≤ stc.dsBaseAddr +
    (r_done * ctx.wd.comps.length + deleteCountJ +
      ((ctx.wd.W.m - ctx.wd.j0Edges.length) - (unembeddedSetPure ctx.wd emb).card)) *
      t2DsOne impl inp.J
  hzf : WordRAM.ZeroFrom st.mem hCur

lemma t2SetupHdr_word_bounds {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) :
    let mW := ctx.wd.W.m
    let K := ctx.wd.comps.length
    let wH := ctx.wInp.h
    let wAddr := mem₀ (wH + 13)
    inp.hAddr < 2 ^ w ∧ inp.jAddr + 1 < 2 ^ w ∧ inp.t1OutAddr + 6 ≤ inp.v1 ∧
    ctx.wInp.prep.h + 2 < 2 ^ w ∧ wH + 20 ≤ inp.v1 ∧ wAddr + 1 < 2 ^ w ∧
    inp.nodesAddr mW K + 3 * inp.embVertSum < 2 ^ w ∧
    inp.v1 + 32 < 2 ^ w ∧
    ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params * ctx.wInp.prep.phiDen_dec < 2 ^ w ∧
    ctx.wd.j0Edges.length ≤ mW ∧
    mW - ctx.wd.j0Edges.length < 2 ^ w := by
  intro mW K wH wAddr
  rcases t2_prep_chain_bounds ctx with ⟨hc1, hc2, hc3, hc4⟩
  rcases ctx.staticOutAt_init with ⟨_, _, _, _, hs4, hs5, _, _, _, _, _, ha1, ha2, ha3, ha_le, _, hgw, _⟩
  have hn_lt := lt_of_le_of_lt (t2_nodesEnd_le_maxWord ctx) ctx.hww.2.2
  have hmW : mW ≤ Task1Input.mwCap impl inp.J := ctx.hmW_le
  have hK : K ≤ inp.J.m := ctx.hK_le
  rcases t2_v1_le_compEdgeBase ctx with ⟨hd1, hd2, hd3, hd4, hd5, hd6, hd7⟩
  have hj0 : ctx.wd.j0Edges.length ≤ mW := by
    dsimp only [mW]; rw [ctx.hw_okW.W_m_eq]; exact Nat.le_add_right _ _
  have hpd_le : ctx.wInp.prep.phiDen_dec ≤ Task1Input.phiDenCap impl inp.J :=
    ctx.hWInpJ ▸ task2_phiDen_le_cap ctx.hstat ctx.hφ_cap
  have htau : ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params *
      ctx.wInp.prep.phiDen_dec ≤ Task2Input.maxWordBound impl inp := by
    have ht1 := ctx.tau1Int_le_cap
    have hm1 := Nat.mul_le_mul ht1 hpd_le
    have hη_pos : 1 ≤ Task2Input.eta1Cap impl inp.J := by
      dsimp only [Task2Input.eta1Cap]; omega
    have hm2 : ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params * ctx.wInp.prep.phiDen_dec ≤
        1 * (2 * Task2Input.gammaExpCap impl inp.J *
            max (impl.pathDS.params.gDel (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m)
              (impl.pathDS.params.gDel (WitnessCoreInput.dWInt impl.constructExpander)
                (Task1Input.mwCap impl inp.J)) *
            max (impl.pathDS.params.phiOutDen (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m)
              (impl.pathDS.params.phiOutDen (WitnessCoreInput.dWInt impl.constructExpander)
                (Task1Input.mwCap impl inp.J)) *
            (length inp.J inp.embJH + 1) *
            (vcongNat inp.J inp.H' inp.embJH + maxDeg inp.J + 1)) *
          Task1Input.phiDenCap impl inp.J := by
      rw [one_mul]; exact hm1
    have hmul_rhs := le_trans hm2 (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hη_pos))
    unfold Task2Input.maxWordBound
    exact le_trans hmul_rhs
      (le_trans (le_trans (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) (le_max_left _ _))
        (le_max_right _ _))
  have _ := ctx.hH'_le
  have _ := ctx.hJ_le
  have _ := graph_encode_length inp.H'
  have _ := graph_encode_length inp.J
  have _ := graph_encode_length ctx.wd.W
  dsimp only [wH, wAddr] at *
  have hwAddr_lt : mem₀ (ctx.wInp.h + 13) + 1 < 2 ^ w := by
    have ha3' : mem₀ (ctx.wInp.h + 14) = mem₀ (ctx.wInp.h + 13) + (2 + 2 * ctx.wd.W.m) := ha3
    omega
  have hprep_lt : ctx.wInp.prep.h + 2 < 2 ^ w := by omega
  exact ⟨by omega, by omega, by omega, hprep_lt, ctx.hv20, hwAddr_lt, hn_lt, by omega,
    lt_of_le_of_lt htau ctx.hww.2.2, hj0, by omega⟩

/-- Updates applied to `[v1, v1 + 32)` by the header stores in `task2Body`. -/
def t2SetupHdrMem (mem₀ : ℕ → ℕ) (v1 embWJAddr mW nH K embJHAddr prepH wH
    dsH cebAddr vhoAddr delAddr vhsAddr vHeadAddr vcAddr psAddr ewsAddr qAddr
    tau1Prod rem0 phiDen : ℕ) : ℕ → ℕ :=
  let m := Function.update mem₀ v1 embWJAddr
  let m := Function.update m (v1 + 8) mW
  let m := Function.update m (v1 + 9) nH
  let m := Function.update m (v1 + 10) K
  let m := Function.update m (v1 + 12) embJHAddr
  let m := Function.update m (v1 + 13) prepH
  let m := Function.update m (v1 + 14) wH
  let m := Function.update m (v1 + 15) dsH
  let m := Function.update m (v1 + 16) cebAddr
  let m := Function.update m (v1 + 17) vhoAddr
  let m := Function.update m (v1 + 18) delAddr
  let m := Function.update m (v1 + 19) vhsAddr
  let m := Function.update m (v1 + 20) vHeadAddr
  let m := Function.update m (v1 + 21) vcAddr
  let m := Function.update m (v1 + 22) psAddr
  let m := Function.update m (v1 + 23) ewsAddr
  let m := Function.update m (v1 + 24) qAddr
  let m := Function.update m (v1 + 29) tau1Prod
  let m := Function.update m (v1 + 30) rem0
  Function.update m (v1 + 31) phiDen

lemma t2SetupHdrMem_outside {mem₀ : ℕ → ℕ}
    {v1 e0 e8 e9 e10 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e29 e30 e31 : ℕ}
    {a : ℕ} (ha : a < v1 ∨ v1 + 32 ≤ a) :
    t2SetupHdrMem mem₀ v1 e0 e8 e9 e10 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24
      e29 e30 e31 a = mem₀ a := by
  dsimp only [t2SetupHdrMem]
  repeat rw [Function.update_of_ne (by omega)]

lemma t2SetupHdrMem_zero_slots {mem₀ : ℕ → ℕ}
    {v1 e0 e8 e9 e10 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e29 e30 e31 : ℕ}
    {k : ℕ} (hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨
      k = 11 ∨ k = 25 ∨ k = 26 ∨ k = 27 ∨ k = 28) :
    t2SetupHdrMem mem₀ v1 e0 e8 e9 e10 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24
      e29 e30 e31 (v1 + k) = mem₀ (v1 + k) := by
  dsimp only [t2SetupHdrMem]
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    repeat rw [Function.update_of_ne (by omega)]

lemma t2SetupHdrMem_slots {mem₀ : ℕ → ℕ}
    {v1 e0 e8 e9 e10 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e29 e30 e31 : ℕ} :
    let m := t2SetupHdrMem mem₀ v1 e0 e8 e9 e10 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22
      e23 e24 e29 e30 e31
    m v1 = e0 ∧ m (v1 + 8) = e8 ∧ m (v1 + 9) = e9 ∧ m (v1 + 10) = e10 ∧
    m (v1 + 12) = e12 ∧ m (v1 + 13) = e13 ∧ m (v1 + 14) = e14 ∧ m (v1 + 15) = e15 ∧
    m (v1 + 16) = e16 ∧ m (v1 + 17) = e17 ∧ m (v1 + 18) = e18 ∧ m (v1 + 19) = e19 ∧
    m (v1 + 20) = e20 ∧ m (v1 + 21) = e21 ∧ m (v1 + 22) = e22 ∧ m (v1 + 23) = e23 ∧
    m (v1 + 24) = e24 ∧ m (v1 + 29) = e29 ∧ m (v1 + 30) = e30 ∧ m (v1 + 31) = e31 := by
  dsimp only [t2SetupHdrMem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    repeat first | exact Function.update_self _ _ _ | rw [Function.update_of_ne (by omega)]

@[reducible] def t2PreambleReadsStmt (cont : Stmt) : Stmt :=
  Stmt.assign 5 (t2Ld (.reg 3) (.const 4)) ;;
  Stmt.assign 6 (t2Ld (.reg 3) (.const 5)) ;;
  Stmt.assign 7 (.load (.reg 0)) ;;
  Stmt.assign 8 (t2Ld (.reg 1) (.const 1)) ;;
  Stmt.assign 9 (.load (.reg 5)) ;;
  Stmt.assign 10 (t2Ld (.reg 5) (.const 2)) ;;
  Stmt.assign 11 (t2Ld (.reg 6) (.const 13)) ;;
  Stmt.assign 12 (t2Ld (.reg 11) (.const 1)) ;;
  Stmt.assign 13 (t2Ld (.reg 6) (.const 8)) ;;
  Stmt.assign 14 (t2Ld (.reg 6) (.const 10)) ;;
  Stmt.assign 15 (t2Ld (.reg 6) (.const 18)) ;;
  Stmt.assign 16 (t2Add (.reg 4) (.const 32)) ;;
  cont

@[reducible] def t2PreambleWritesStmt (cont : Stmt) : Stmt :=
  Stmt.store (.reg 4) (.reg 16) ;;
  t2St (.reg 4) (.const 8) (.reg 12) ;;
  t2St (.reg 4) (.const 9) (.reg 7) ;;
  t2St (.reg 4) (.const 10) (.reg 10) ;;
  t2St (.reg 4) (.const 12) (.reg 2) ;;
  t2St (.reg 4) (.const 13) (.reg 5) ;;
  t2St (.reg 4) (.const 14) (.reg 6) ;;
  Stmt.assign 16 (t2Add (.reg 16) (.reg 12)) ;;
  t2St (.reg 4) (.const 15) (.reg 16) ;;
  Stmt.assign 16 (t2Add (.reg 16) (.reg 10)) ;;
  t2St (.reg 4) (.const 16) (.reg 16) ;;
  Stmt.assign 16 (t2Add (.reg 16) (.reg 10)) ;;
  t2St (.reg 4) (.const 17) (.reg 16) ;;
  Stmt.assign 16 (t2Add (.reg 16) (.reg 10)) ;;
  t2St (.reg 4) (.const 18) (.reg 16) ;;
  Stmt.assign 16 (t2Add (.reg 16) (.reg 8)) ;;
  t2St (.reg 4) (.const 19) (.reg 16) ;;
  Stmt.assign 16 (t2Add (.reg 16) (t2Mul (.const 2) (.reg 8))) ;;
  t2St (.reg 4) (.const 20) (.reg 16) ;;
  Stmt.assign 16 (t2Add (.reg 16) (.reg 7)) ;;
  t2St (.reg 4) (.const 21) (.reg 16) ;;
  Stmt.assign 16 (t2Add (.reg 16) (.reg 7)) ;;
  t2St (.reg 4) (.const 22) (.reg 16) ;;
  Stmt.assign 16 (t2Add (.reg 16) (.reg 7)) ;;
  t2St (.reg 4) (.const 23) (.reg 16) ;;
  Stmt.assign 16 (t2Add (.reg 16) (.reg 7)) ;;
  t2St (.reg 4) (.const 24) (.reg 16) ;;
  Stmt.assign 17 (t2Add (.reg 16) (.reg 7)) ;;
  t2St (.reg 4) (.const 29) (t2Mul (.reg 14) (.reg 15)) ;;
  t2St (.reg 4) (.const 30) (t2Sub (.reg 12) (.reg 9)) ;;
  t2St (.reg 4) (.const 31) (.reg 15) ;;
  cont

@[reducible] def t2PreambleStmt (cont : Stmt) : Stmt :=
  t2PreambleReadsStmt (t2PreambleWritesStmt cont)

@[reducible] def t2TailSetupStmt (cont : Stmt) : Stmt :=
  Stmt.assign 31 (t2Ld (.reg 5) (.const 3)) ;;
  Stmt.assign 32 (t2Ld (.reg 6) (.const 12)) ;;
  Stmt.assign 33 (t2Ld (.reg 6) (.const 17)) ;;
  Stmt.assign 34 (.reg 15) ;;
  Stmt.assign 35 (t2Ld (.reg 6) (.const 19)) ;;
  Stmt.assign 36 (t2Ld (.reg 4) (.const 15)) ;;
  Stmt.assign 37 (t2Ld (.reg 4) (.const 17)) ;;
  Stmt.assign 38 (.load (.reg 4)) ;;
  Stmt.assign 39 (t2Ld (.reg 4) (.const 19)) ;;
  Stmt.assign 40 (t2Ld (.reg 4) (.const 29)) ;;
  Stmt.assign 19 (.const 1) ;;
  cont

local macro "t2_reg" : tactic =>
  `(tactic| (first | assumption | (simp (disch := decide) only [Function.update_self, Function.update_of_ne]; try assumption)))

private lemma t2_preamble_reads_runs {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {inp : Task2Input} {mem₀ : ℕ → ℕ} (ctx : T2Ctx impl inp mem₀ w)
    (st : State) (ω : ℕ → Bool)
    (hm : st.mem = mem₀)
    (hr0 : st.regs 0 = inp.hAddr) (hr1 : st.regs 1 = inp.jAddr)
    (hr2 : st.regs 2 = inp.embJHAddr) (hr3 : st.regs 3 = inp.t1OutAddr) (hr4 : st.regs 4 = inp.v1)
    (cont : Stmt) (Q : Outcome → State → ℕ → Prop)
    (hcont : ∀ st_r : State,
      st_r.mem = mem₀ → st_r.pos = st.pos →
      st_r.regs 1 = inp.jAddr → st_r.regs 2 = inp.embJHAddr → st_r.regs 4 = inp.v1 →
      st_r.regs 5 = ctx.wInp.prep.h → st_r.regs 6 = ctx.wInp.h →
      st_r.regs 7 = inp.H'.n → st_r.regs 8 = inp.J.m →
      st_r.regs 9 = ctx.wd.j0Edges.length → st_r.regs 10 = ctx.wd.comps.length →
      st_r.regs 12 = ctx.wd.W.m →
      st_r.regs 13 = ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params →
      st_r.regs 14 = ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params →
      st_r.regs 15 = ctx.wInp.prep.phiDen_dec →
      st_r.regs 16 = inp.embWJAddr →
      ∃ o stF c_cont, Runs w p ω cont st_r o stF c_cont ∧ Q o stF c_cont) :
    ∃ o stF c_tot, Runs w p ω (t2PreambleReadsStmt cont) st o stF c_tot ∧
      ∃ c_cont, Q o stF c_cont ∧ c_tot ≤ c_cont + 70 := by
  suffices h : ∃ o stF c_tot, Runs w p ω (t2PreambleReadsStmt cont) st o stF c_tot ∧
      ∃ c_cont, Q o stF c_cont ∧ 0 + c_tot ≤ c_cont + 70 by
    simpa only [Nat.zero_add] using h
  rcases t2SetupHdr_word_bounds ctx with
    ⟨_, hj1_w, ht1_v1, hph_w, hw20, hwa1_w, _, hv1_w, _, _, _⟩
  rcases ctx.staticOutAt_init with
    ⟨_, _, _, _, hs4, hs5, hs8, hs10, _, hs18, _, _, _, _, _, _, hgw, _⟩
  have hk_len : ctx.wd.comps.length = ctx.wInp.prep.rawComps.length :=
    ctx.wInp.buildCompsFrom_length ctx.wInp.prep.j0Edges.length
      ctx.wInp.prep.rawComps ctx.WSubs ctx.hws.1
  have hmem_h : mem₀ inp.hAddr = inp.H'.n :=
    congrArg Graph.n (graphAt_iff_readGraph.mp ctx.hgH')
  have hmem_j1 : mem₀ (inp.jAddr + 1) = inp.J.m := by
    simpa [Graph.m, Cited.readGraph] using congrArg Graph.m (graphAt_iff_readGraph.mp ctx.hgJ)
  have hmem_w1 : mem₀ (mem₀ (ctx.wInp.h + 13) + 1) = ctx.wd.W.m := by
    simpa [Graph.m, Cited.readGraph] using congrArg Graph.m (graphAt_iff_readGraph.mp hgw)
  have hm_j0 : mem₀ ctx.wInp.prep.h = ctx.wd.j0Edges.length := ctx.hpst.2.1
  have hm_K : mem₀ (ctx.wInp.prep.h + 2) = ctx.wd.comps.length := hk_len ▸ ctx.hpst.2.2.2.1
  have hm_w1_lt : mem₀ (ctx.wInp.h + 13) < 2 ^ w := by omega
  rcases st with ⟨smem, sregs, spos⟩
  dsimp only at hm hr0 hr1 hr2 hr3 hr4
  subst hm
  refine runs_seq_ld_cps hr3 (by omega) (by omega) hs4 ?_
  refine runs_seq_ld_cps (base := inp.t1OutAddr) (by t2_reg) (by omega) (by omega) hs5 ?_
  refine runs_seq_ld0_cps (base := inp.hAddr) (by t2_reg) hmem_h ?_
  refine runs_seq_ld_cps (base := inp.jAddr) (by t2_reg) (by omega) (by omega) hmem_j1 ?_
  refine runs_seq_ld0_cps (base := ctx.wInp.prep.h) (by t2_reg) hm_j0 ?_
  refine runs_seq_ld_cps (base := ctx.wInp.prep.h) (by t2_reg) (by omega) (by omega) hm_K ?_
  refine runs_seq_ld_cps (base := ctx.wInp.h) (by t2_reg) (by omega) (by omega) rfl ?_
  refine runs_seq_ld_cps (base := smem (ctx.wInp.h + 13)) (by t2_reg) (by omega) (by omega) hmem_w1 ?_
  refine runs_seq_ld_cps (base := ctx.wInp.h) (by t2_reg) (by omega) (by omega) hs8 ?_
  refine runs_seq_ld_cps (base := ctx.wInp.h) (by t2_reg) (by omega) (by omega) hs10 ?_
  refine runs_seq_ld_cps (base := ctx.wInp.h) (by t2_reg) (by omega) (by omega) hs18 ?_
  refine runs_seq_assign_cps (Expr.eval_add (w := w) (Expr.eval_reg_of_eq (v := inp.v1) (by t2_reg))
    (Expr.eval_const (by omega : 32 < 2 ^ w)) (by omega)) ?_
  refine runs_seq_end_cps ?_ (by simp only [Expr.size]; omega)
  refine hcont _ rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> (t2_reg; try rfl)

private lemma t2_preamble_writes_runs {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {inp : Task2Input} {mem₀ : ℕ → ℕ} (ctx : T2Ctx impl inp mem₀ w)
    (st : State) (ω : ℕ → Bool)
    (hm : st.mem = mem₀)
    (hr1 : st.regs 1 = inp.jAddr) (hr2 : st.regs 2 = inp.embJHAddr) (hr4 : st.regs 4 = inp.v1)
    (hr5 : st.regs 5 = ctx.wInp.prep.h) (hr6 : st.regs 6 = ctx.wInp.h)
    (hr7 : st.regs 7 = inp.H'.n) (hr8 : st.regs 8 = inp.J.m)
    (hr9 : st.regs 9 = ctx.wd.j0Edges.length) (hr10 : st.regs 10 = ctx.wd.comps.length)
    (hr12 : st.regs 12 = ctx.wd.W.m)
    (hr13 : st.regs 13 = ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params)
    (hr14 : st.regs 14 = ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params)
    (hr15 : st.regs 15 = ctx.wInp.prep.phiDen_dec)
    (hr16 : st.regs 16 = inp.embWJAddr)
    (cont : Stmt) (Q : Outcome → State → ℕ → Prop)
    (hcont : ∀ st_p : State,
      st_p.mem = t2SetupHdrMem mem₀ inp.v1 inp.embWJAddr ctx.wd.W.m inp.H'.n ctx.wd.comps.length
        inp.embJHAddr ctx.wInp.prep.h ctx.wInp.h (inp.dsHandlesAddr ctx.wd.W.m)
        (inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length)
        (inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length)
        (inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length)
        (inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length)
        (inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length)
        (inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length)
        (inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length)
        (inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length)
        (inp.queueAddr ctx.wd.W.m ctx.wd.comps.length)
        (ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params * ctx.wInp.prep.phiDen_dec)
        (ctx.wd.W.m - ctx.wd.j0Edges.length) ctx.wInp.prep.phiDen_dec →
      st_p.regs 1 = inp.jAddr → st_p.regs 4 = inp.v1 →
      st_p.regs 5 = ctx.wInp.prep.h → st_p.regs 6 = ctx.wInp.h →
      st_p.regs 10 = ctx.wd.comps.length → st_p.regs 12 = ctx.wd.W.m →
      st_p.regs 13 = ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params →
      st_p.regs 15 = ctx.wInp.prep.phiDen_dec →
      st_p.regs 17 = inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length →
      st_p.pos = st.pos →
      ∃ o stF c_cont, Runs w p ω cont st_p o stF c_cont ∧ Q o stF c_cont) :
    ∃ o stF c_tot, Runs w p ω (t2PreambleWritesStmt cont) st o stF c_tot ∧
      ∃ c_cont, Q o stF c_cont ∧ c_tot ≤ c_cont + 190 := by
  suffices h : ∃ o stF c_tot, Runs w p ω (t2PreambleWritesStmt cont) st o stF c_tot ∧
      ∃ c_cont, Q o stF c_cont ∧ 0 + c_tot ≤ c_cont + 190 by
    simpa only [Nat.zero_add] using h
  rcases t2SetupHdr_word_bounds ctx with
    ⟨_, _, _, _, _, _, hn_w, hv1_w, htau_w, hj0_mW, hrem_w⟩
  have hn_w_exp : inp.v1 + 32 + ctx.wd.W.m + ctx.wd.comps.length + ctx.wd.comps.length +
      ctx.wd.comps.length + inp.J.m + 2 * inp.J.m + inp.H'.n + inp.H'.n + inp.H'.n +
      inp.H'.n + inp.H'.n + 3 * inp.embVertSum < 2 ^ w := by
    simpa only [Task2Input.nodesAddr, Task2Input.queueAddr, Task2Input.eWVertStampAddr,
      Task2Input.procStampAddr, Task2Input.vcongNumAddr, Task2Input.vHeadAddr,
      Task2Input.vhatStampAddr, Task2Input.compEdgeDelRoundAddr, Task2Input.vhatOffsetAddr,
      Task2Input.compEdgeBaseAddr, Task2Input.dsHandlesAddr, Task2Input.embWJAddr] using hn_w
  have hv1_emb : inp.embWJAddr = inp.v1 + 32 := rfl
  rcases st with ⟨smem, sregs, spos⟩
  dsimp only at hm hr1 hr2 hr4 hr5 hr6 hr7 hr8 hr9 hr10 hr12 hr13 hr14 hr15 hr16
  subst hm
  refine runs_seq_store_cps (Expr.eval_reg_of_eq hr4) (Expr.eval_reg_of_eq hr16) ?_
  refine runs_seq_st_cps (base := inp.v1) (val := ctx.wd.W.m) (by t2_reg) (by omega) (by omega) (by t2_reg) ?_
  refine runs_seq_st_cps (base := inp.v1) (val := inp.H'.n) (by t2_reg) (by omega) (by omega) (by t2_reg) ?_
  refine runs_seq_st_cps (base := inp.v1) (val := ctx.wd.comps.length) (by t2_reg) (by omega) (by omega) (by t2_reg) ?_
  refine runs_seq_st_cps (base := inp.v1) (val := inp.embJHAddr) (by t2_reg) (by omega) (by omega) (by t2_reg) ?_
  refine runs_seq_st_cps (base := inp.v1) (val := ctx.wInp.prep.h) (by t2_reg) (by omega) (by omega) (by t2_reg) ?_
  refine runs_seq_st_cps (base := inp.v1) (val := ctx.wInp.h) (by t2_reg) (by omega) (by omega) (by t2_reg) ?_
  refine runs_seq_add_cps (va := inp.v1 + 32) (vb := ctx.wd.W.m) (by t2_reg) (by t2_reg) (by omega) ?_
  refine runs_seq_st_cps (base := inp.v1) (val := inp.v1 + 32 + ctx.wd.W.m) (by t2_reg) (by omega) (by omega) (by t2_reg) ?_
  refine runs_seq_add_cps (va := inp.v1 + 32 + ctx.wd.W.m) (vb := ctx.wd.comps.length) (by t2_reg) (by t2_reg) (by omega) ?_
  refine runs_seq_st_cps (base := inp.v1) (val := inp.v1 + 32 + ctx.wd.W.m + ctx.wd.comps.length)
    (by t2_reg) (by omega) (by omega) (by t2_reg) ?_
  refine runs_seq_add_cps (va := inp.v1 + 32 + ctx.wd.W.m + ctx.wd.comps.length) (vb := ctx.wd.comps.length)
    (by t2_reg) (by t2_reg) (by omega) ?_
  refine runs_seq_st_cps (base := inp.v1) (val := inp.v1 + 32 + ctx.wd.W.m + ctx.wd.comps.length + ctx.wd.comps.length)
    (by t2_reg) (by omega) (by omega) (by t2_reg) ?_
  refine runs_seq_add_cps (va := inp.v1 + 32 + ctx.wd.W.m + ctx.wd.comps.length + ctx.wd.comps.length)
    (vb := ctx.wd.comps.length) (by t2_reg) (by t2_reg) (by omega) ?_
  refine runs_seq_st_cps (base := inp.v1)
    (val := inp.v1 + 32 + ctx.wd.W.m + ctx.wd.comps.length + ctx.wd.comps.length + ctx.wd.comps.length)
    (by t2_reg) (by omega) (by omega) (by t2_reg) ?_
  refine runs_seq_add_cps
    (va := inp.v1 + 32 + ctx.wd.W.m + ctx.wd.comps.length + ctx.wd.comps.length + ctx.wd.comps.length)
    (vb := inp.J.m) (by t2_reg) (by t2_reg) (by omega) ?_
  refine runs_seq_st_cps (base := inp.v1)
    (val := inp.v1 + 32 + ctx.wd.W.m + ctx.wd.comps.length + ctx.wd.comps.length + ctx.wd.comps.length + inp.J.m)
    (by t2_reg) (by omega) (by omega) (by t2_reg) ?_
  refine runs_seq_assign_cps (Expr.eval_add (w := w)
    (Expr.eval_reg_of_eq (v := inp.v1 + 32 + ctx.wd.W.m + ctx.wd.comps.length + ctx.wd.comps.length +
      ctx.wd.comps.length + inp.J.m) (by t2_reg))
    (Expr.eval_mul (Expr.eval_const (by omega : 2 < 2 ^ w))
      (Expr.eval_reg_of_eq (v := inp.J.m) (by t2_reg)) (by omega)) (by omega)) ?_
  refine runs_seq_st_cps (base := inp.v1)
    (val := inp.v1 + 32 + ctx.wd.W.m + ctx.wd.comps.length + ctx.wd.comps.length + ctx.wd.comps.length +
      inp.J.m + 2 * inp.J.m)
    (by t2_reg) (by omega) (by omega) (by t2_reg) ?_
  refine runs_seq_add_cps
    (va := inp.v1 + 32 + ctx.wd.W.m + ctx.wd.comps.length + ctx.wd.comps.length + ctx.wd.comps.length +
      inp.J.m + 2 * inp.J.m)
    (vb := inp.H'.n) (by t2_reg) (by t2_reg) (by omega) ?_
  refine runs_seq_st_cps (base := inp.v1)
    (val := inp.v1 + 32 + ctx.wd.W.m + ctx.wd.comps.length + ctx.wd.comps.length + ctx.wd.comps.length +
      inp.J.m + 2 * inp.J.m + inp.H'.n)
    (by t2_reg) (by omega) (by omega) (by t2_reg) ?_
  refine runs_seq_add_cps
    (va := inp.v1 + 32 + ctx.wd.W.m + ctx.wd.comps.length + ctx.wd.comps.length + ctx.wd.comps.length +
      inp.J.m + 2 * inp.J.m + inp.H'.n)
    (vb := inp.H'.n) (by t2_reg) (by t2_reg) (by omega) ?_
  refine runs_seq_st_cps (base := inp.v1)
    (val := inp.v1 + 32 + ctx.wd.W.m + ctx.wd.comps.length + ctx.wd.comps.length + ctx.wd.comps.length +
      inp.J.m + 2 * inp.J.m + inp.H'.n + inp.H'.n)
    (by t2_reg) (by omega) (by omega) (by t2_reg) ?_
  refine runs_seq_add_cps
    (va := inp.v1 + 32 + ctx.wd.W.m + ctx.wd.comps.length + ctx.wd.comps.length + ctx.wd.comps.length +
      inp.J.m + 2 * inp.J.m + inp.H'.n + inp.H'.n)
    (vb := inp.H'.n) (by t2_reg) (by t2_reg) (by omega) ?_
  refine runs_seq_st_cps (base := inp.v1)
    (val := inp.v1 + 32 + ctx.wd.W.m + ctx.wd.comps.length + ctx.wd.comps.length + ctx.wd.comps.length +
      inp.J.m + 2 * inp.J.m + inp.H'.n + inp.H'.n + inp.H'.n)
    (by t2_reg) (by omega) (by omega) (by t2_reg) ?_
  refine runs_seq_add_cps
    (va := inp.v1 + 32 + ctx.wd.W.m + ctx.wd.comps.length + ctx.wd.comps.length + ctx.wd.comps.length +
      inp.J.m + 2 * inp.J.m + inp.H'.n + inp.H'.n + inp.H'.n)
    (vb := inp.H'.n) (by t2_reg) (by t2_reg) (by omega) ?_
  refine runs_seq_st_cps (base := inp.v1)
    (val := inp.v1 + 32 + ctx.wd.W.m + ctx.wd.comps.length + ctx.wd.comps.length + ctx.wd.comps.length +
      inp.J.m + 2 * inp.J.m + inp.H'.n + inp.H'.n + inp.H'.n + inp.H'.n)
    (by t2_reg) (by omega) (by omega) (by t2_reg) ?_
  refine runs_seq_add_cps
    (va := inp.v1 + 32 + ctx.wd.W.m + ctx.wd.comps.length + ctx.wd.comps.length + ctx.wd.comps.length +
      inp.J.m + 2 * inp.J.m + inp.H'.n + inp.H'.n + inp.H'.n + inp.H'.n)
    (vb := inp.H'.n) (by t2_reg) (by t2_reg) (by omega) ?_
  refine runs_seq_store_cps
    (Expr.eval_add (w := w) (Expr.eval_reg_of_eq (v := inp.v1) (by t2_reg))
      (Expr.eval_const (by omega : 29 < 2 ^ w)) (by omega))
    (Expr.eval_mul (Expr.eval_reg_of_eq (v := ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params) (by t2_reg))
      (Expr.eval_reg_of_eq (v := ctx.wInp.prep.phiDen_dec) (by t2_reg)) htau_w) ?_
  refine runs_seq_store_cps
    (Expr.eval_add (w := w) (Expr.eval_reg_of_eq (v := inp.v1) (by t2_reg))
      (Expr.eval_const (by omega : 30 < 2 ^ w)) (by omega))
    (Expr.eval_sub (Expr.eval_reg_of_eq (v := ctx.wd.W.m) (by t2_reg))
      (Expr.eval_reg_of_eq (v := ctx.wd.j0Edges.length) (by t2_reg)) (by omega)) ?_
  refine runs_seq_st_cps (base := inp.v1) (val := ctx.wInp.prep.phiDen_dec) (by t2_reg) (by omega) (by omega) (by t2_reg) ?_
  refine runs_seq_end_cps ?_ (by simp only [Expr.size]; omega)
  refine hcont _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl <;> (t2_reg; try rfl)

lemma t2_setup_preamble_runs {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {inp : Task2Input} {mem₀ : ℕ → ℕ} (ctx : T2Ctx impl inp mem₀ w)
    (st : State) (ω : ℕ → Bool)
    (hm : st.mem = mem₀)
    (hr0 : st.regs 0 = inp.hAddr) (hr1 : st.regs 1 = inp.jAddr)
    (hr2 : st.regs 2 = inp.embJHAddr) (hr3 : st.regs 3 = inp.t1OutAddr) (hr4 : st.regs 4 = inp.v1)
    (cont : Stmt) (Q : Outcome → State → ℕ → Prop)
    (hcont : ∀ st_p : State,
      st_p.mem = t2SetupHdrMem mem₀ inp.v1 inp.embWJAddr ctx.wd.W.m inp.H'.n ctx.wd.comps.length
        inp.embJHAddr ctx.wInp.prep.h ctx.wInp.h (inp.dsHandlesAddr ctx.wd.W.m)
        (inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length)
        (inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length)
        (inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length)
        (inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length)
        (inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length)
        (inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length)
        (inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length)
        (inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length)
        (inp.queueAddr ctx.wd.W.m ctx.wd.comps.length)
        (ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params * ctx.wInp.prep.phiDen_dec)
        (ctx.wd.W.m - ctx.wd.j0Edges.length) ctx.wInp.prep.phiDen_dec →
      st_p.regs 1 = inp.jAddr → st_p.regs 4 = inp.v1 →
      st_p.regs 5 = ctx.wInp.prep.h → st_p.regs 6 = ctx.wInp.h →
      st_p.regs 10 = ctx.wd.comps.length → st_p.regs 12 = ctx.wd.W.m →
      st_p.regs 13 = ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params →
      st_p.regs 15 = ctx.wInp.prep.phiDen_dec →
      st_p.regs 17 = inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length →
      st_p.pos = st.pos →
      ∃ o stF c_cont, Runs w p ω cont st_p o stF c_cont ∧ Q o stF c_cont) :
    ∃ o stF c_tot, Runs w p ω (t2PreambleStmt cont) st o stF c_tot ∧
      ∃ c_cont, Q o stF c_cont ∧ c_tot ≤ c_cont + 260 := by
  obtain ⟨o, stF, c_r, hr_r, c_w, ⟨c_cont, hq, hcw⟩, hcr⟩ :=
    t2_preamble_reads_runs ctx st ω hm hr0 hr1 hr2 hr3 hr4 (t2PreambleWritesStmt cont)
      (fun o stF c => ∃ c_cont, Q o stF c_cont ∧ c ≤ c_cont + 190)
      (fun st_r hm_r hp_r hr1_r hr2_r hr4_r hr5_r hr6_r hr7_r hr8_r hr9_r hr10_r
          hr12_r hr13_r hr14_r hr15_r hr16_r => by
        obtain ⟨o, stF, c_w, hr_w, c_cont, hq, hcw⟩ :=
          t2_preamble_writes_runs ctx st_r ω hm_r hr1_r hr2_r hr4_r hr5_r hr6_r
            hr7_r hr8_r hr9_r hr10_r hr12_r hr13_r hr14_r hr15_r hr16_r cont Q
            (fun st_p hmem_p h1 h4 h5 h6 h10 h12 h13 h15 h17 hpos_p =>
              hcont st_p hmem_p h1 h4 h5 h6 h10 h12 h13 h15 h17 (hpos_p.trans hp_r))
        exact ⟨o, stF, c_w, hr_w, c_cont, hq, hcw⟩)
  exact ⟨o, stF, c_r, hr_r, c_cont, hq, by omega⟩

lemma task2_tail_setup_runs {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {inp : Task2Input} {mem₀ : ℕ → ℕ} (ctx : T2Ctx impl inp mem₀ w)
    (st : State) (ω : ℕ → Bool)
    (hStat : ctx.StaticOutAt st.mem) (hPrep : PrepStaticState ctx.wInp.prep st.mem st.mem)
    (h0 : st.mem inp.v1 = inp.embWJAddr)
    (h15 : st.mem (inp.v1 + 15) = inp.dsHandlesAddr ctx.wd.W.m)
    (h17 : st.mem (inp.v1 + 17) = inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length)
    (h19 : st.mem (inp.v1 + 19) = inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length)
    (h29 : st.mem (inp.v1 + 29) = ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params *
      ctx.wInp.prep.phiDen_dec)
    (hr4 : st.regs 4 = inp.v1) (hr5 : st.regs 5 = ctx.wInp.prep.h)
    (hr6 : st.regs 6 = ctx.wInp.h) (hr15 : st.regs 15 = ctx.wInp.prep.phiDen_dec)
    (cont : Stmt) (Q : Outcome → State → ℕ → Prop)
    (hcont : ∀ st_t : State,
      st_t.mem = st.mem → st_t.pos = st.pos →
      (∀ r ≤ 20, r ≠ 19 → st_t.regs r = st.regs r) →
      st_t.regs 19 = 1 →
      st_t.regs 31 = ctx.wInp.prep.aComps →
      st_t.regs 32 = st.mem (ctx.wInp.h + 12) →
      st_t.regs 33 = ctx.wInp.prep.phiNum_dec →
      st_t.regs 34 = ctx.wInp.prep.phiDen_dec →
      st_t.regs 35 = ctx.wd.J0_strip.m →
      st_t.regs 36 = inp.dsHandlesAddr ctx.wd.W.m →
      st_t.regs 37 = inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length →
      st_t.regs 38 = inp.embWJAddr →
      st_t.regs 39 = inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length →
      st_t.regs 40 = ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params *
        ctx.wInp.prep.phiDen_dec →
      ∃ o stF c_cont, Runs w p ω cont st_t o stF c_cont ∧ Q o stF c_cont) :
    ∃ o stF c_tot, Runs w p ω (t2TailSetupStmt cont) st o stF c_tot ∧
      ∃ c_cont, Q o stF c_cont ∧ c_tot ≤ c_cont + 65 := by
  suffices h : ∃ o stF c_tot, Runs w p ω (t2TailSetupStmt cont) st o stF c_tot ∧
      ∃ c_cont, Q o stF c_cont ∧ 0 + c_tot ≤ c_cont + 65 by
    simpa only [Nat.zero_add] using h
  rcases t2SetupHdr_word_bounds ctx with
    ⟨_, _, ht1_v1, _, hw20, _, _, hv1_w, htau_w, _, _⟩
  rcases t2_prep_chain_bounds ctx with ⟨hc1, hc2, hc3, hc4⟩
  rcases hStat with ⟨_, _, _, _, _, _, _, _, ha33, _, ha35, ha1, ha2, ha3, ha_le, _⟩
  have hW : 1 < 2 ^ w := ctx.hww.1
  rcases t2_v1_le_compEdgeBase ctx with ⟨hd1, hd2, hd3, hd4, hd5, hd6, hd7⟩
  have h12 : st.mem (ctx.wInp.h + 12) < 2 ^ w := by omega
  have ha31 : st.mem (ctx.wInp.prep.h + 3) = ctx.wInp.prep.aComps := hPrep.2.2.2.2.1
  have ha_aComps_w : ctx.wInp.prep.aComps < 2 ^ w := by omega
  have hpow_w : inp.J.n + (stripLoops inp.J).m + Task1Input.phiDenCap impl inp.J +
      (stripLoops inp.J).m + impl.pathDS.params.gExp (Task1Input.dJCap impl inp.J)
      (stripLoops inp.J).m + 2 < 2 ^ w := by
    have hpw := ctx.hww.2.1
    have hlog_le : Nat.log 2 (inp.J.n + (stripLoops inp.J).m + Task1Input.phiDenCap impl inp.J +
        (stripLoops inp.J).m + impl.pathDS.params.gExp (Task1Input.dJCap impl inp.J)
        (stripLoops inp.J).m + 2) + 1 ≤ w :=
      le_trans (Nat.le_mul_of_pos_left _ impl.pathDS.params.hcw_pos) hpw
    have hpow : inp.J.n + (stripLoops inp.J).m + Task1Input.phiDenCap impl inp.J +
        (stripLoops inp.J).m + impl.pathDS.params.gExp (Task1Input.dJCap impl inp.J)
        (stripLoops inp.J).m + 2 <
        2 ^ (Nat.log 2 (inp.J.n + (stripLoops inp.J).m + Task1Input.phiDenCap impl inp.J +
          (stripLoops inp.J).m + impl.pathDS.params.gExp (Task1Input.dJCap impl inp.J)
          (stripLoops inp.J).m + 2) + 1) :=
      Nat.lt_pow_succ_log_self (by omega : 1 < 2) _
    exact lt_of_lt_of_le hpow (Nat.pow_le_pow_right (by omega) hlog_le)
  have ha_phiNum_w : ctx.wInp.prep.phiNum_dec < 2 ^ w := by
    have h1 := ctx.ds_bounds.2.2.2.2.1
    have h2 := ctx.ds_bounds.2.2.2.2.2.1
    have h3 : ctx.wInp.prep.phiDen_dec ≤ Task1Input.phiDenCap impl inp.J :=
      ctx.hWInpJ ▸ task2_phiDen_le_cap ctx.hstat ctx.hφ_cap
    omega
  have ha_m0_w : ctx.wd.J0_strip.m < 2 ^ w := by
    have h0 := ctx.ds_bounds.2.2.2.1
    omega
  rcases st with ⟨smem, sregs, spos⟩
  dsimp only at h0 h15 h17 h19 h29 hr4 hr5 hr6 hr15 h12 ha31
  refine runs_seq_ld_cps hr5 (by omega) (by omega) ha31 ?_
  refine runs_seq_ld_cps (base := ctx.wInp.h) (by t2_reg) (by omega) (by omega) rfl ?_
  refine runs_seq_ld_cps (base := ctx.wInp.h) (by t2_reg) (by omega) (by omega) ha33 ?_
  refine runs_seq_assign_cps (Expr.eval_reg_of_eq (v := ctx.wInp.prep.phiDen_dec) (by t2_reg)) ?_
  refine runs_seq_ld_cps (base := ctx.wInp.h) (by t2_reg) (by omega) (by omega) ha35 ?_
  refine runs_seq_ld_cps (base := inp.v1) (by t2_reg) (by omega) (by omega) h15 ?_
  refine runs_seq_ld_cps (base := inp.v1) (by t2_reg) (by omega) (by omega) h17 ?_
  refine runs_seq_ld0_cps (base := inp.v1) (by t2_reg) h0 ?_
  refine runs_seq_ld_cps (base := inp.v1) (by t2_reg) (by omega) (by omega) h19 ?_
  refine runs_seq_ld_cps (base := inp.v1) (by t2_reg) (by omega) (by omega) h29 ?_
  refine runs_seq_assign_cps (Expr.eval_const (by omega : 1 < 2 ^ w)) ?_
  refine runs_seq_end_cps ?_ (by simp only [Expr.size]; omega)
  refine hcont _ rfl rfl
    (fun r hr hr19 => by
      simp (disch := first | exact hr19 | omega) only [Function.update_of_ne])
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> (t2_reg; try rfl)


end MinCostFlow.Spanner
