module

public import MinCostFlow.Spanner.ProgTask3MiddleHelpers

/-!
# Verification of `t3MiddleEdge` (`selfBase + 3`)

This file proves `t3MiddleEdge_ptriple`: one middle step of Task 3 on an unembedded edge of `J`
whose source is a component (`inComp`). The step calls `GetPath` of the path data structure,
writes the returned walk to the heap, updates the congestion counters, and drains the queue of
overloaded edges. The proof runs the statements one by one and uses the helper lemmas of
`ProgTask3MiddleHelpers.lean` for memory frames, heap bounds and costs.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM Cited

private lemma t3_prep_h_le_hEnd (q : PrepInput) : q.h ≤ q.hEnd := by
  have h0 := q.hBlocksStart_eq
  have h1 := q.cJSubPtr_le_hEnd (Nat.zero_le _)
  have h2 := q.cJSubPtr_zero
  unfold PrepInput.aVLoc PrepInput.aVComp PrepInput.aComps PrepInput.aJ0Out
    PrepInput.aEdgeNext PrepInput.aLvlHead at h0
  omega

/-- `t3_normal_ptriple_cps` for a first statement whose triple starts from potential `0`, with
an extra potential `F` carried past it unchanged. -/
private lemma t3_normal_ptriple_cps_frame {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {s₁ s₂ : Stmt} {st : State} {b₁ k T F : ℕ}
    {P : State → ℕ → Prop} {Inv : State → ℕ → Prop} {cost : State → ℕ}
    {Q : Outcome → State → ℕ → Prop}
    (ht : PTriple w p P s₁ (pNormalPost Inv) cost)
    (hp : P st 0) (hc : cost st ≤ b₁)
    (hrest : ∀ st₁ Φ₁, Inv st₁ Φ₁ → ∃ o stF c₂ Φ',
      Runs w p ω s₂ st₁ o stF c₂ ∧ Q o stF Φ' ∧ (k + b₁ + 1) + c₂ + Φ' ≤ T + (Φ₁ + F)) :
    ∃ o stF c_tot Φ', Runs w p ω (.seq s₁ s₂) st o stF c_tot ∧
      Q o stF Φ' ∧ k + c_tot + Φ' ≤ T + F := by
  obtain ⟨o₁, st₁, c₁, Φ₁, hr₁, hq₁, hc₁⟩ := ht st 0 ω hp
  cases o₁ with
  | returned _ => exact False.elim hq₁
  | normal =>
    obtain ⟨o, stF, c₂, Φ', hr₂, hq, hc₂⟩ := hrest st₁ Φ₁ hq₁
    exact ⟨o, stF, c₁ + c₂ + 1, Φ',
      runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, hr₁, hr₂, rfl⟩), hq, by omega⟩

/-- Weakening of the cost bound in a continuation goal. -/
private lemma t3_cps_weaken {w : ℕ} {p : Program} {ω : ℕ → Bool} {s : Stmt} {st : State}
    {k B₁ B₂ : ℕ} {Q : Outcome → State → ℕ → Prop}
    (h : ∃ o stF c Φ', Runs w p ω s st o stF c ∧ Q o stF Φ' ∧ k + c + Φ' ≤ B₁) (hB : B₁ ≤ B₂) :
    ∃ o stF c Φ', Runs w p ω s st o stF c ∧ Q o stF Φ' ∧ k + c + Φ' ≤ B₂ := by
  obtain ⟨o, stF, c, Φ', hr, hq, hc⟩ := h
  exact ⟨o, stF, c, Φ', hr, hq, le_trans hc hB⟩

set_option maxHeartbeats 1000000 in
theorem t3MiddleEdge_ptriple {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (hlay : lay = T3Layout.ofCtx ctx)
    {p : Program} {selfBase dsBase rCur eJ ci jL : ℕ}
    (hSpec : impl.pathDS.R.Implements w p dsBase (fun i => dsBase + 1 + i) (pathDSDataStructure impl.pathDS.params w))
    (hdrain : p.procs[selfBase + 2]? = some (t3DrainQueueBody dsBase))
    {d0 : T3RoundData impl.pathDS} (heJ : eJ < inp.J.m) (hunemb : d0.emb eJ = none)
    (hsrc : ctx.wd.jSources.getD eJ JEdgeSource.isLoop = JEdgeSource.inComp ci jL)
    (hu_nv : ∀ hci : ci < ctx.wd.comps.length, ((ctx.wd.comps[ci]'hci).J_sub.edges.getD jL (0, 0)).1 ∉ (d0.states ci).Vhat)
    (hv_nv : ∀ hci : ci < ctx.wd.comps.length, ((ctx.wd.comps[ci]'hci).J_sub.edges.getD jL (0, 0)).2 ∉ (d0.states ci).Vhat) :
    let γW := impl.pathDS.params.gExp (WitnessCoreInput.dWInt impl.constructExpander) (Task1Input.mwCap impl inp.J)
    let Pre := fun (st : State) (Φ : ℕ) =>
      T3RoundAt ctx lay rCur d0 st Φ ∧ st.regs 0 = lay.base ∧ st.regs 1 = rCur ∧ st.regs 2 = eJ ∧ st.regs 3 = ci ∧ st.regs 4 = jL
    let Post := fun (o : Outcome) (st : State) (Φ : ℕ) =>
      o = .returned 0 ∧ ∃ d', T3RoundAt ctx lay rCur d' st Φ ∧ d'.getPathCnt = d0.getPathCnt + 1 ∧
        d'.econgUpd = d0.econgUpd + (partialToWalk d'.emb eJ).edges.length ∧
        (∀ cj < ctx.wd.comps.length, (d0.states cj).Vhat ⊆ (d'.states cj).Vhat) ∧
        (∀ e' < inp.J.m, e' ≠ eJ → d'.emb e' = d0.emb e') ∧ (d'.emb eJ).isSome = true ∧ d'.nextHasUnemb = d0.nextHasUnemb
    PTriple w p Pre (t3MiddleEdgeBody dsBase (selfBase + 2)) Post
      (fun _ => ⌈impl.pathDS.params.K_query * (impl.pathDS.params.gQuery (WitnessCoreInput.dWInt impl.constructExpander) (Task1Input.mwCap impl inp.J) : ℝ)⌉₊ + γW * (⌈impl.pathDS.params.K_del * (impl.pathDS.params.gQuery (WitnessCoreInput.dWInt impl.constructExpander) (Task1Input.mwCap impl inp.J) : ℝ)⌉₊ + 300) + 380) := by
  intro γW Pre Post st Φ ω ⟨hR, hr0, hr1, hr2, hr3, hr4⟩
  have hLoc : impl.pathDS.R.Local := hSpec.1
  obtain ⟨hci, hjL, hu_lt, hv_lt, hne, _, hJ_edge⟩ := t3_inComp_ne ctx heJ hsrc
  let uL := ((ctx.wd.comps[ci]'hci).J_sub.edges.getD jL (0, 0)).1
  let vL := ((ctx.wd.comps[ci]'hci).J_sub.edges.getD jL (0, 0)).2
  have hb := T3Layout.bounds ctx; dsimp only at hb; rw [← hlay] at hb; unfold t3HdrSize at hb
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12⟩ := hb
  have hj0_le_Wm : ctx.wd.j0Edges.length ≤ ctx.wd.W.m := by simp [T3Ctx.wd, WitnessCoreInput.mkWitnessData, Graph.m]
  have hw1 : 1 < 2 ^ w := ctx.hwokW.1; have hwb : Task3Input.maxWordBound impl inp < 2 ^ w := ctx.hwokW.2.2
  have hro := ctx.read_out_fields hR.staticMem.1
  rcases hro with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hce_at, _, hww_bd, _, _, _, _, _, _, _, _⟩
  have hcp := ctx.read_comp_prep hR.staticMem.1 hci
  rcases hcp with ⟨haC_v, haC_j, hVerts_at, hJSub_at, hComps_bd, hVerts_bd, hJSub_bd⟩
  simp [Cited.Graph.encode] at hJSub_bd
  have hjL_len : jL < ctx.wd.comps[ci].J_sub.edges.length := hjL
  have hcur_lo : lay.staticEnd ≤ d0.hCur := hR.hCur_lo
  have hu_at := graphAt_edge_fst hJSub_at hjL; have hv_at := graphAt_edge_snd hJSub_at hjL
  have hcExt := hce_at ci hci; have hprep_le_v1 : ctx.wInp.prep.hEnd ≤ ctx.v1 := le_trans ctx.hPrepEnd (by omega)
  have hv1_le_v2 : ctx.v1 ≤ lay.base := by rw [hb1]; exact ctx.hv1_le
  have hGpc_succ : d0.getPathCnt + 1 ≤ inp.J.m :=
    let _ : eJ ∈ unembeddedSet2Pure inp.J d0.emb := by simp [unembeddedSet2Pure, heJ, hunemb]
    by have := Finset.card_pos.mpr ⟨eJ, ‹_›⟩; have := hR.getPath_cnt_le; omega
  have hOld_le_max : d0.hCur + Task3Input.dsOneW impl inp.J ≤ Task3Input.maxHeapEnd impl inp := by
    unfold Task3Input.maxHeapEnd
    have hr_bd := Nat.mul_le_mul_right inp.J.m hR.rCur_le
    have hdel_bd := le_trans hR.del_le_econgUpd (le_trans hR.econgUpd_W (Nat.mul_le_mul_right γW (by omega : d0.getPathCnt ≤ inp.J.m)))
    have hm1 := Nat.mul_le_mul_right (Task3Input.dsOneW impl inp.J)
      (show rCur * inp.J.m + d0.getPathCnt + d0.delCnt + 1 ≤ eta2Bound inp.J * inp.J.m + inp.J.m + inp.J.m * γW by omega)
    have hm2 := Nat.mul_le_mul_right (2 * γW + 3) (by omega : d0.getPathCnt ≤ inp.J.m)
    have hds_add : (rCur * inp.J.m + d0.getPathCnt + d0.delCnt) * Task3Input.dsOneW impl inp.J + Task3Input.dsOneW impl inp.J =
        (rCur * inp.J.m + d0.getPathCnt + d0.delCnt + 1) * Task3Input.dsOneW impl inp.J := by ring
    have hh0 := hR.hCur_bd; dsimp only [γW] at *; omega
  have hmax_lt_w : Task3Input.maxHeapEnd impl inp + 3 ≤ Task3Input.maxWordBound impl inp := le_max_left _ _
  have hlay_max : lay.staticEnd ≤ Task3Input.maxHeapEnd impl inp := hb10.trans hb11
  have hu_mem : uL ∈ (d0.states ci).G.verts \ (d0.states ci).Vhat := by
    have hG := (hR.dsArr.at_ci ci hci).2.2.2.2.1; rw [List.getD_eq_getElem _ _ hci] at hG
    exact Finset.mem_sdiff.mpr ⟨hG ▸ Finset.mem_range.mpr hu_lt, hu_nv hci⟩
  have hv_mem : vL ∈ (d0.states ci).G.verts \ (d0.states ci).Vhat := by
    have hG := (hR.dsArr.at_ci ci hci).2.2.2.2.1; rw [List.getD_eq_getElem _ _ hci] at hG
    exact Finset.mem_sdiff.mpr ⟨hG ▸ Finset.mem_range.mpr hv_lt, hv_nv hci⟩
  have hds_ci := ctx.hds_bounds.1 ci hci
  have hVn_bd : ctx.wd.comps[ci].W_sub.n ≤ 2 * inp.J.m := by
    have h1 : ctx.wd.comps[ci].W_sub.n ≤ (ctx.wd.comps.map fun c => c.W_sub.n).sum :=
      List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem (List.getElem_mem hci))
    have := ctx.hvhatSum_le; omega
  have h3w_bd : 3 * Task1Input.mwCap impl inp.J + 2 * inp.J.m + 4 ≤ Task3Input.maxWordBound impl inp := by
    unfold Task3Input.maxWordBound; exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  obtain ⟨body_gp, o_gp, st_gp, c_gp, x', P, hproc_gp, hruns_gp, hle_h, hle_sp,
      hpres_below, hpres_gp, hft_new, hWalk_gp, hP_wk_d, hP_nd, hP_ndel, _, hP_len_gp, hArr_gp, hcost_gp⟩ :=
    hR.dsArr.call_getPath (pos := st.pos) (ω := ω) hSpec hci (le_refl _) (by omega) hu_mem hv_mem (by omega) (by omega) (by omega)
      (by have h := hds_ci.2.2.2.1; rw [← List.getD_eq_getElem ctx.wd.comps defaultCompInfo hci] at h
          simpa [show ctx.wd.φ_Const = (impl.constructExpander.phiNum : ℝ) / impl.constructExpander.phiDen from rfl] using h)
      (by have h := hds_ci.2.2.1; rw [← List.getD_eq_getElem ctx.wd.comps defaultCompInfo hci] at h; omega)
  have hP_wk : P.IsWalk ctx.wd.comps[ci].W_sub uL vL := (List.getD_eq_getElem ctx.wd.comps defaultCompInfo hci) ▸ hP_wk_d
  let hMid := o_gp.value; let mem_gp := st_gp.mem; let reps1 := Function.update d0.reps ci x'
  have hMid_le_h0 : hMid ≤ d0.hCur + Task3Input.dsOneW impl inp.J := by
    rw [List.getD_eq_getElem _ _ hci] at hle_sp; exact le_trans hle_sp (Nat.add_le_add_left hds_ci.2.2.1 _)
  have hle_hm : d0.hCur + (1 + P.verts.length + P.edges.length) ≤ hMid :=
    t3_walkAt_zeroFrom_le hWalk_gp hP_wk hne hP_nd hArr_gp.zero_from hle_h
  have hP_len_gp' : (P.edges.length : ℝ) ≤ impl.pathDS.params.γ_ExpPath ctx.wd.φ_Const ctx.wd.M_W := hP_len_gp
  have hP_edges_le : P.edges.length ≤ γW :=
    le_trans (by simpa only [Nat.ceil_natCast] using (Nat.ceil_le (n := ⌈impl.pathDS.params.γ_ExpPath ctx.wd.φ_Const ctx.wd.M_W⌉₊)).mpr (le_trans hP_len_gp' (Nat.le_ceil _))) ctx.hds_bounds.2.2.2.1
  have hP_len_ctx : (P.edges.length : ℝ) ≤ ctx.wd.γ_ExpPath :=
    le_trans hP_len_gp' ctx.hds_bounds.2.2.2.2.1
  have hPv_le : P.verts.length ≤ P.edges.length + 1 := by
    rcases hP_wk with ⟨_, _, ⟨hPv, hPe, _⟩ | ⟨_, hlen, _⟩⟩
    · rw [hPv, hPe]; simp
    · omega
  have hEnd_lt_w : hMid + (2 + P.verts.length + P.edges.length) < 2 ^ w := by
    have hNext_b := t3_middle_next_bd (pv := P.verts.length) (pe := P.edges.length) hR.hCur_bd hMid_le_h0 (by omega)
    have hr_bd := Nat.mul_le_mul_right inp.J.m hR.rCur_le
    have hdel_bd := le_trans hR.del_le_econgUpd (le_trans hR.econgUpd_W (Nat.mul_le_mul_right γW (by omega : d0.getPathCnt ≤ inp.J.m)))
    have hEta := Nat.mul_le_mul_right (Task3Input.dsOneW impl inp.J) (show rCur * inp.J.m + (d0.getPathCnt + 1) + d0.delCnt ≤ eta2Bound inp.J * inp.J.m + inp.J.m + inp.J.m * γW by omega)
    have hGpc_m := Nat.mul_le_mul_right (2 * γW + 3) hGpc_succ
    have hMax_def : Task3Input.maxHeapEnd impl inp = Task3Input.staticEndCap impl inp + 5 * inp.J.m + (eta2Bound inp.J * inp.J.m + inp.J.m + inp.J.m * γW) * Task3Input.dsOneW impl inp.J + inp.J.m * (2 * γW + 3) := rfl
    dsimp only [γW] at hEta hGpc_m hMax_def; omega
  have hOld_mem_gp : ∀ e' < inp.J.m, match d0.emb e' with
      | none => mem_gp (lay.embJWAddr + e') = 0
      | some P' => lay.staticEnd ≤ mem_gp (lay.embJWAddr + e') ∧ mem_gp (lay.embJWAddr + e') + P'.encode.length ≤ hMid ∧
          WalkAt mem_gp (mem_gp (lay.embJWAddr + e')) P' ∧
          ∀ a, mem_gp (lay.embJWAddr + e') ≤ a → a < mem_gp (lay.embJWAddr + e') + P'.encode.length →
            ∀ cj < ctx.wd.comps.length, ¬ impl.pathDS.R.foot (mem_gp (lay.dsHandlesAddr + cj)) (reps1 cj) a := fun e' he' => by
    have hom := hR.emb_mem e' he'; dsimp only [mem_gp]; rw [hpres_below _ (by omega)]
    cases hde : d0.emb e' with
    | none => rw [hde] at hom; exact hom
    | some P' =>
      rw [hde] at hom
      refine ⟨hom.1, by omega, t3_walkAt_of_agree hom.2.2.1 fun a ha1 ha2 => hpres_gp a (by omega) fun hft => hom.2.2.2 a ha1 (by omega) ci hci hft,
        fun a ha1 ha2 cj hcj => ?_⟩
      rw [hpres_below _ (by omega)]
      by_cases hcj_eq : cj = ci
      · subst hcj_eq; dsimp only [reps1]; rw [Function.update_self]; intro hft
        rcases hft_new a ((hpres_below (lay.dsHandlesAddr + cj) (by omega)) ▸ hft) with hf | ⟨hl, _⟩
        · exact hom.2.2.2 a ha1 ha2 cj hcj hf
        · omega
      · dsimp only [reps1]; rw [Function.update_of_ne hcj_eq]; exact hom.2.2.2 a ha1 ha2 cj hcj
  apply t3_ptriple_of_cps; dsimp only [t3MiddleEdgeBody]
  have hOff_w : t3OffAComps < 2 ^ w ∧ t3OffACompExt < 2 ^ w ∧ t3OffDsHdl < 2 ^ w ∧ t3OffHCur < 2 ^ w ∧ t3OffGetPath < 2 ^ w ∧
      t3OffWWNum < 2 ^ w ∧ t3OffPhiDen < 2 ^ w ∧ t3OffTau2 < 2 ^ w ∧ t3OffECnt < 2 ^ w ∧ t3OffWDel < 2 ^ w ∧ t3OffQueue < 2 ^ w := by
    unfold t3OffAComps t3OffACompExt t3OffDsHdl t3OffHCur t3OffGetPath t3OffWWNum t3OffPhiDen t3OffTau2 t3OffECnt t3OffWDel t3OffQueue; omega
  have hbase_lt : lay.base + 32 < 2 ^ w := by omega
  refine t3_ld_cps hr0 hOff_w.1 (by unfold t3OffAComps; omega) hR.staticMem.2.2.2.2.2.2.2.2.2.1 ?_
  refine t3_ld_cps (by simp [hr0]) hOff_w.2.1 (by unfold t3OffACompExt; omega) hR.staticMem.2.2.2.2.2.2.2.2.2.2.1 ?_
  refine t3_ld_cps (by simp [hr0]) hOff_w.2.2.1 (by unfold t3OffDsHdl; omega) hR.staticMem.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
  let r7 := Function.update (Function.update (Function.update st.regs 5 ctx.wInp.prep.aComps) 6 (ctx.memT1 (ctx.wInp.h + 12))) 7 lay.dsHandlesAddr
  refine t3_assign_cps (show Expr.eval w ⟨st.mem, r7, st.pos⟩
      (t3Ld (.reg 5) (t3Add (t3Mul (.const 7) (.reg 3)) (.const 3))) = some (ctx.wInp.prep.cJSubPtr ci) from
    (by simpa [Nat.add_assoc] using haC_j : st.mem (ctx.wInp.prep.aComps + (7 * ci + 3)) = ctx.wInp.prep.cJSubPtr ci) ▸
      Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq (show r7 5 = ctx.wInp.prep.aComps by simp [r7]))
        (Expr.eval_add (Expr.eval_mul (Expr.eval_const (by omega : 7 < 2 ^ w)) (Expr.eval_reg_of_eq (show r7 3 = ci by simp [r7, hr3])) (by omega))
          (Expr.eval_const (by omega : 3 < 2 ^ w)) (by omega)) (by omega))) ?_
  let r8 := Function.update r7 8 (ctx.wInp.prep.cJSubPtr ci)
  refine t3_assign_cps (show Expr.eval w ⟨st.mem, r8, st.pos⟩
      (t3Ld (.reg 8) (t3Add (.const 2) (t3Mul (.const 2) (.reg 4)))) = some uL from
    (by simpa [uL, Nat.add_assoc, List.getD_eq_getElem?, List.getElem?_eq_getElem hjL] using hu_at :
        st.mem (ctx.wInp.prep.cJSubPtr ci + (2 + 2 * jL)) = uL) ▸
      Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq (show r8 8 = ctx.wInp.prep.cJSubPtr ci by simp [r8]))
        (Expr.eval_add (Expr.eval_const (by omega : 2 < 2 ^ w)) (Expr.eval_mul (Expr.eval_const (by omega : 2 < 2 ^ w))
          (Expr.eval_reg_of_eq (show r8 4 = jL by simp [r8, r7, hr4])) (by omega)) (by omega)) (by omega))) ?_
  let r9 := Function.update r8 9 uL
  refine t3_assign_cps (show Expr.eval w ⟨st.mem, r9, st.pos⟩
      (t3Ld (.reg 8) (t3Add (.const 3) (t3Mul (.const 2) (.reg 4)))) = some vL from
    (by simpa [vL, Nat.add_assoc, List.getD_eq_getElem?, List.getElem?_eq_getElem hjL] using hv_at :
        st.mem (ctx.wInp.prep.cJSubPtr ci + (3 + 2 * jL)) = vL) ▸
      Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq (show r9 8 = ctx.wInp.prep.cJSubPtr ci by simp [r9, r8]))
        (Expr.eval_add (Expr.eval_const (by omega : 3 < 2 ^ w)) (Expr.eval_mul (Expr.eval_const (by omega : 2 < 2 ^ w))
          (Expr.eval_reg_of_eq (show r9 4 = jL by simp [r9, r8, r7, hr4])) (by omega)) (by omega)) (by omega))) ?_
  refine t3_ld_cps (by simp [hr0]) hOff_w.2.2.2.1 (by unfold t3OffHCur; omega) hR.hCur_eq ?_
  let r11 := Function.update (Function.update r9 10 vL) 11 d0.hCur
  refine t3_assign_cps (show Expr.eval w ⟨st.mem, r11, st.pos⟩ (t3Ld (.reg 7) (.reg 3)) = some (st.mem (lay.dsHandlesAddr + ci)) from
    Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq (show r11 7 = lay.dsHandlesAddr by simp [r11, r9, r8, r7]))
      (Expr.eval_reg_of_eq (show r11 3 = ci by simp [r11, r9, r8, r7, hr3])) (by omega))) ?_
  let r12 := Function.update r11 12 (st.mem (lay.dsHandlesAddr + ci))
  have hcall_gp : Runs w p ω (.call 13 (dsBase + 2) [.reg 12, .reg 9, .reg 10, .reg 11])
      ⟨st.mem, r12, st.pos⟩ .normal ⟨mem_gp, Function.update r12 13 hMid, st_gp.pos⟩ (4 + c_gp + 1) :=
    runs_call_iff.mpr ⟨_, body_gp, o_gp, st_gp, c_gp, by simp [evalArgs, r12, r11, r9, Expr.eval], hproc_gp, hruns_gp, rfl, rfl, by simp [argsSize]⟩
  let r13 := Function.update r12 13 hMid
  let mem_g := Function.update mem_gp (lay.base + t3OffGetPath) (d0.getPathCnt + 1)
  have hWalk_g : WalkAt mem_g d0.hCur P := t3_walkAt_of_agree hWalk_gp fun a ha1 _ => by
    dsimp only [mem_g]; exact Function.update_of_ne (by unfold t3OffGetPath; omega) _ _
  have hr13_0 : r13 0 = lay.base := by simp [r13, r12, r11, r9, r8, r7, hr0]
  have hr13_3 : r13 3 = ci := by simp [r13, r12, r11, r9, r8, r7, hr3]
  have hr13_11 : r13 11 = d0.hCur := by simp [r13, r12, r11]
  have hWm_pos : 0 < ctx.wd.W.m := by have h1 := (ctx.hw_okW.comp_props ci hci).2.2.2.2.2.2.2.2.2.2.2.2.2.1; have h2 := (ctx.hw_okW.comp_props ci hci).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2; omega
  have htau2_prod_w : rCur * ctx.wInp.tau2Int impl.constructExpander impl.pathDS.params < 2 ^ w := by
    have ⟨_, hww1, hww2⟩ := hww_bd 0 hWm_pos
    have hmaxDeg_pos : 1 ≤ maxDeg inp.J := by by_contra h0; have hz : maxDeg inp.J = 0 := (by omega); rw [hz, Nat.zero_mul] at hww2; omega
    have hphiDen_pos : 1 ≤ ctx.wInp.prep.phiDen_dec := by have := ctx.hStat.2.2.2.2.2.2.2.2.1; have := ctx.hStat.2.2.2.2.2.2.2.2.2.1; omega
    have hphiDen_cap := ctx.hWInpJ ▸ task2_phiDen_le_cap ctx.hStat ctx.hφ_max
    have hm2 := le_trans (Nat.mul_le_mul hR.rCur_le ctx.htau2_le_cap) (Nat.le_mul_of_pos_right _ (Nat.mul_pos hmaxDeg_pos (show 0 < Task1Input.phiDenCap impl inp.J by omega)))
    have hmw : eta2Bound inp.J * Task1Input.tau2Cap impl inp.J * maxDeg inp.J * Task1Input.phiDenCap impl inp.J + 2 ≤ Task3Input.maxWordBound impl inp := by
      unfold Task3Input.maxWordBound; exact le_trans (le_max_left _ _) (le_max_right _ _)
    rw [Nat.mul_assoc (eta2Bound inp.J * Task1Input.tau2Cap impl inp.J)] at hmw; omega
  let Φ_post_gp := t3KdelCost impl inp.J * t3EcongPhi ctx lay st.mem + dsTotalPhi impl.pathDS lay.dsHandlesAddr ctx.wd.comps.length reps1 mem_gp + 25 * t3VhatRem ctx.wd d0.states
  have hgp_phi_bd : c_gp + Φ_post_gp ≤ ⌈impl.pathDS.params.K_query * (impl.pathDS.params.gQuery (WitnessCoreInput.dWInt impl.constructExpander) (Task1Input.mwCap impl inp.J) : ℝ)⌉₊ + Φ := by
    have hq := hR.phi_eq; dsimp only [t3RoundPhi] at hq
    have hc : c_gp + dsTotalPhi impl.pathDS lay.dsHandlesAddr ctx.wd.comps.length reps1 mem_gp ≤
        ⌈impl.pathDS.params.K_query * impl.pathDS.params.γ_query ctx.wd.φ_Const ctx.wd.M_W⌉₊ + dsTotalPhi impl.pathDS lay.dsHandlesAddr ctx.wd.comps.length d0.reps st.mem := hcost_gp
    have hk := ctx.hds_bounds.2.2.1; dsimp only [Φ_post_gp, γW] at hk ⊢; omega
  refine t3_seq_normal_cps (C := P.verts.length * 31 + P.edges.length * 115 +
      t3KdelCost impl inp.J * P.edges.length + 180 + Φ_post_gp) hcall_gp ?_ (by
    simp only [Expr.size, t3Ld, t3Add, t3Mul, t3OffAComps, t3OffACompExt, t3OffDsHdl, t3OffHCur]
    unfold t3KdelCost; exact t3_middle_cost_arith (by omega) hPv_le hP_edges_le hgp_phi_bd)
  · have hbase_se : lay.base < lay.staticEnd := by
      rw [hb9, hb8, hb7, hb6, hb5, hb4, hb3, hb2]; simp only [Nat.add_assoc]
      exact Nat.lt_add_of_pos_right (Nat.add_pos_left (by norm_num) _)
    have hAC_lt_base : ctx.wInp.prep.aComps + (7 * ci + 2) < lay.base := by
      have h7 : 7 * ci + 2 < 7 * ctx.wd.comps.length := by omega
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left h7 _)
        (le_trans hComps_bd (le_trans hprep_le_v1 hv1_le_v2))
    have hAC_lt : ctx.wInp.prep.aComps + (7 * ci + 2) < lay.staticEnd := lt_trans hAC_lt_base hbase_se
    have hAC_ne : ctx.wInp.prep.aComps + (7 * ci + 2) ≠ lay.base + t3OffGetPath :=
      Nat.ne_of_lt (Nat.lt_of_lt_of_le hAC_lt_base (Nat.le_add_right _ _))
    have hCE_lt_base : ctx.memT1 (ctx.wInp.h + 12) + 6 * ci < lay.base := by omega
    have hCE_lt : ctx.memT1 (ctx.wInp.h + 12) + 6 * ci < lay.staticEnd := lt_trans hCE_lt_base hbase_se
    have hCE_ne : ctx.memT1 (ctx.wInp.h + 12) + 6 * ci ≠ lay.base + t3OffGetPath :=
      Nat.ne_of_lt (Nat.lt_of_lt_of_le hCE_lt_base (Nat.le_add_right _ _))
    have hbase_w : lay.base < 2 ^ w := by omega
    have hbase32_se : lay.base + 32 ≤ lay.staticEnd := by
      rw [hb9, hb8, hb7, hb6, hb5, hb4, hb3, hb2]; simp only [Nat.add_assoc]; exact Nat.add_le_add_left (Nat.le_add_right _ _) _
    have h7ci2_w : 7 * ci + 2 < 2 ^ w := lt_of_le_of_lt (Nat.le_add_left _ _) (lt_trans hAC_lt_base hbase_w)
    have h7ci_w : 7 * ci < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right _ _) h7ci2_w
    have h6ci_w : 6 * ci < 2 ^ w := lt_of_le_of_lt (Nat.le_add_left _ _) (lt_trans hCE_lt_base hbase_w)
    have hv1_w : 1 + P.verts.length < 2 ^ w := by omega
    have hcv1_w : d0.hCur + (1 + P.verts.length) < 2 ^ w := by omega
    have hev_gpc_addr : (t3Add (.reg 0) (.const t3OffGetPath)).eval w ⟨mem_gp, r13, st_gp.pos⟩ = some (lay.base + t3OffGetPath) :=
      Expr.eval_add (Expr.eval_reg_of_eq hr13_0) (Expr.eval_const hOff_w.2.2.2.2.1) (by unfold t3OffGetPath; omega)
    have hev_gpc_val : (t3Add (t3Ld (.reg 0) (.const t3OffGetPath)) (.const 1)).eval w ⟨mem_gp, r13, st_gp.pos⟩ = some (d0.getPathCnt + 1) :=
      Expr.eval_add (((hpres_below _ (by unfold t3OffGetPath; omega)).trans hR.getPath_eq) ▸ Expr.eval_load hev_gpc_addr) (Expr.eval_const hw1) (by omega)
    refine t3_store_cps hev_gpc_addr hev_gpc_val ?_
    refine t3_assign_cps (show Expr.eval w ⟨mem_g, r13, st_gp.pos⟩ (.load (.reg 11)) = some P.verts.length from
      (walkAt_iff.mp hWalk_g).1 ▸ Expr.eval_load (Expr.eval_reg_of_eq hr13_11)) ?_
    let r14 := Function.update r13 14 P.verts.length
    refine t3_assign_cps (show Expr.eval w ⟨mem_g, r14, st_gp.pos⟩ (t3Ld (.reg 11) (t3Add (.const 1) (.reg 14))) = some P.edges.length from
      (by simpa [Nat.add_assoc] using (walkAt_iff.mp hWalk_g).2.2.1 : mem_g (d0.hCur + (1 + P.verts.length)) = P.edges.length) ▸
        Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq (show r14 11 = d0.hCur by simp [r14, hr13_11]))
          (Expr.eval_add (Expr.eval_const hw1) (Expr.eval_reg_of_eq (show r14 14 = P.verts.length by simp [r14])) hv1_w) hcv1_w)) ?_
    let r15 := Function.update r14 15 P.edges.length
    refine t3_assign_cps (show Expr.eval w ⟨mem_g, r15, st_gp.pos⟩ (t3Ld (.reg 5) (t3Add (t3Mul (.const 7) (.reg 3)) (.const 2))) =
        some (ctx.wInp.prep.cVertsPtr ci) from
      Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (show r15 5 = ctx.wInp.prep.aComps by simp [r15, r14, r13, r12, r11, r9, r8, r7]))
          (Expr.eval_add (Expr.eval_mul (Expr.eval_const (by omega : 7 < 2 ^ w)) (Expr.eval_reg_of_eq (show r15 3 = ci by simp [r15, r14, hr13_3])) h7ci_w)
            (Expr.eval_const (by omega : 2 < 2 ^ w)) h7ci2_w) (lt_trans hAC_lt_base hbase_w))
        ((Function.update_of_ne hAC_ne _ _).trans ((hpres_below _ hAC_lt).trans
          (by simpa [Nat.add_assoc] using haC_v)))) ?_
    let r16 := Function.update r15 16 (ctx.wInp.prep.cVertsPtr ci)
    refine t3_assign_cps (show Expr.eval w ⟨mem_g, r16, st_gp.pos⟩ (t3Ld (.reg 6) (t3Mul (.const 6) (.reg 3))) = some ctx.wd.comps[ci].wStart from
      Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (show r16 6 = ctx.memT1 (ctx.wInp.h + 12) by simp [r16, r15, r14, r13, r12, r11, r9, r8, r7]))
          (Expr.eval_mul (Expr.eval_const (by omega : 6 < 2 ^ w)) (Expr.eval_reg_of_eq (show r16 3 = ci by simp [r16, r15, r14, hr13_3])) h6ci_w)
          (lt_trans hCE_lt_base hbase_w))
        ((Function.update_of_ne hCE_ne _ _).trans ((hpres_below _ hCE_lt).trans hcExt.1))) ?_
    let r17 := Function.update r16 17 ctx.wd.comps[ci].wStart
    let mem_cv0 := Function.update mem_g (hMid + 1 + P.verts.length) P.edges.length
    refine t3_store_cps (by
        have hr17_13 : r17 13 = hMid := by simp [r17, r16, r15, r14, r13]
        have hr17_14 : r17 14 = P.verts.length := by simp [r17, r16, r15, r14]
        have h := Expr.eval_add (st := ⟨mem_g, r17, st_gp.pos⟩) (Expr.eval_reg_of_eq (r := 13) hr17_13)
          (Expr.eval_add (Expr.eval_const hw1) (Expr.eval_reg_of_eq (r := 14) hr17_14) hv1_w)
          (show hMid + (1 + P.verts.length) < 2 ^ w by omega)
        rwa [← Nat.add_assoc] at h) (Expr.eval_reg_of_eq (show r17 15 = P.edges.length by simp [r17, r16, r15])) ?_
    have hcv0_lt_hm : ∀ a < hMid + 1, mem_cv0 a = mem_g a := fun a ha => Function.update_of_ne (by omega) _ _
    have hP_verts_bd : ∀ v ∈ P.verts, v < ctx.wd.comps[ci].verts.length := fun v hv => by
      have hc := ctx.hw_okW.comp_props ci hci; have hlen : ctx.wd.comps[ci].verts.length = ctx.wd.comps[ci].X.card := by rw [hc.2.2.2.2.1]; exact vertsOf_length _
      have hlt := Walk.isWalk_verts_lt hc.2.2.2.2.2.2.2.2.2.2.2.2.1 hP_wk v hv; have := hc.2.2.2.2.2.2.2.2.2.2.2.1; omega
    have hVb : ctx.wInp.prep.cVertsPtr ci + ctx.wd.comps[ci].verts.length ≤ lay.base :=
      le_trans hVerts_bd (le_trans (t3_prep_h_le_hEnd _) (le_trans hprep_le_v1 hv1_le_v2))
    have hVb_hm : ctx.wInp.prep.cVertsPtr ci + ctx.wd.comps[ci].verts.length ≤ hMid := by omega
    have hCopy := t3CopyVert_ptriple (w := w) (p := p) (hOld := d0.hCur) (hMid := hMid) (vertsPtr := ctx.wInp.prep.cVertsPtr ci)
      (P := P) (verts := ctx.wd.comps[ci].verts) mem_cv0 r17 hw1 (by omega) (by omega) (lt_of_le_of_lt hVb hbase_w) hle_hm hVb_hm
      (ListAt.congr hVerts_at fun k _ hk => (hcv0_lt_hm k (by omega)).trans
        ((Function.update_of_ne (show k ≠ lay.base + t3OffGetPath by omega) _ _).trans (hpres_below k (by omega))))
      (t3_walkAt_of_agree hWalk_g fun a _ ha2 => hcv0_lt_hm a (by have := walk_encode_length P; omega)) hP_verts_bd (by omega)
    refine t3_normal_ptriple_cps_frame hCopy ⟨rfl, rfl, by simp [r12, r11], by simp,
        by simp, by simp, fun _ _ => rfl, fun _ _ => rfl⟩ (le_refl (P.verts.length * 31 + 7)) ?_
    intro st_cv Φ_cv ⟨hΦ_cv, hr_cv, hm_cv_verts, hm_cv_lt, hm_cv_ge⟩; subst hΦ_cv
    have hcv_below_gp1 : ∀ a < hMid + 1, a ≠ lay.base + t3OffGetPath → st_cv.mem a = mem_gp a := fun a ha hne => (hm_cv_lt a ha).trans ((hcv0_lt_hm a ha).trans (Function.update_of_ne hne _ _))
    have hcv_below_gp : ∀ a < hMid, a ≠ lay.base + t3OffGetPath → st_cv.mem a = mem_gp a := fun a ha => hcv_below_gp1 a (by omega)
    have hcv_below_st : ∀ a < lay.staticEnd, a ≠ lay.base + t3OffGetPath → st_cv.mem a = st.mem a := fun a ha hne => (hcv_below_gp a (by omega) hne).trans (hpres_below a ha)
    have hcv_st : T3StaticMem ctx lay st_cv.mem := hR.staticMem.mono (fun x hx => hcv_below_st x (by omega) (by unfold t3OffGetPath; omega))
      (fun i hi _ h2 _ _ _ _ _ => hcv_below_st _ (by unfold t3HdrSize at *; omega) (by omega)) (fun cj hcj => hcv_below_st _ (by omega) (by unfold t3OffGetPath; omega))
    have hr_cv_0 : st_cv.regs 0 = lay.base := (hr_cv 0 (by decide)).trans (by simp [r17, r16, r15, r14, hr13_0])
    have hr_cv_1 : st_cv.regs 1 = rCur := (hr_cv 1 (by decide)).trans (by simp [r17, r16, r15, r14, r13, r12, r11, r9, r8, r7, hr1])
    refine t3_assign_cps (Expr.eval_const (by omega : 0 < 2 ^ w)) ?_
    refine t3_ld_cps (by simp [hr_cv_0]) hOff_w.2.2.2.2.2.1 (by unfold t3OffWWNum; omega) hcv_st.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    refine t3_ld_cps (by simp [hr_cv_0]) hOff_w.2.2.2.2.2.2.1 (by unfold t3OffPhiDen; omega) hcv_st.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    let r20 := Function.update (Function.update (Function.update st_cv.regs 18 0) 19 (ctx.memT1 (ctx.wInp.h + 14))) 20 ctx.wInp.prep.phiDen_dec
    have hev_tau2 : (t3Ld (.reg 0) (.const t3OffTau2)).eval w ⟨st_cv.mem, r20, st_cv.pos⟩ =
        some (ctx.wInp.tau2Int impl.constructExpander impl.pathDS.params) :=
      hcv_st.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ▸ Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq (show r20 0 = lay.base by simp [r20, hr_cv_0]))
        (Expr.eval_const hOff_w.2.2.2.2.2.2.2.1) (by unfold t3OffTau2; omega))
    refine t3_assign_cps (Expr.eval_mul (Expr.eval_reg_of_eq (show r20 1 = rCur by simp [r20, hr_cv_1])) hev_tau2 htau2_prod_w) ?_
    refine t3_ld_cps (by simp [hr_cv_0]) hOff_w.2.2.2.2.2.2.2.2.1 (by unfold t3OffECnt; omega) hcv_st.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    refine t3_ld_cps (by simp [hr_cv_0]) hOff_w.2.2.2.2.2.2.2.2.2.1 (by unfold t3OffWDel; omega) hcv_st.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    refine t3_ld_cps (by simp [hr_cv_0]) hOff_w.2.2.2.2.2.2.2.2.2.2 (by unfold t3OffQueue; omega) hcv_st.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    let regs24 := Function.update (Function.update (Function.update (Function.update r20
      21 (rCur * ctx.wInp.tau2Int impl.constructExpander impl.pathDS.params)) 22 lay.econgCountAddr) 23 lay.wDelStampAddr) 24 lay.queueAddr
    have hes_pt := t3EdgeStep_ptriple (p := p) ctx lay hlay hLoc d0 reps1 st_cv.mem regs24 heJ hci
      hR.rCur_pos hR.rCur_le hunemb hR.hCur_lo hle_hm hP_wk hP_nd hP_ndel hP_edges_le hR.econgUpd_W
      hR.getPath_cnt_le (by omega)
      (t3_walkAt_of_agree hWalk_gp fun a _ ha2 => hcv_below_gp1 a (by have := walk_encode_length P; omega) (by unfold t3OffGetPath; omega))
      hcv_st (fun cj hcj a ha => by rw [hcv_below_gp _ (by omega) (by unfold t3OffGetPath; omega)] at ha; exact (hArr_gp.at_ci cj hcj).2.2.2.1 a ha)
      (fun eW heW => (hcv_below_st _ (by omega) (by unfold t3OffGetPath; omega)).trans (hR.econg_cnt_eq eW heW))
      hR.econg_le_round
      (fun eW heW => by have := Finset.mem_Ico.mp heW; rw [hcv_below_st _ (by omega) (by unfold t3OffGetPath; omega), hcv_below_st _ (by omega) (by unfold t3OffGetPath; omega)]; exact hR.wdel_comp eW heW)
      (fun eW heW hst => by have := Finset.mem_Ico.mp heW; rw [hcv_below_st _ (by omega) (by unfold t3OffGetPath; omega)] at hst; exact hR.wdel_thresh eW heW hst)
      (fun eW heW hlt => by have := Finset.mem_Ico.mp heW; rw [hcv_below_st _ (by omega) (by unfold t3OffGetPath; omega)] at hlt; exact hR.wdel_lt_econg eW heW hlt)
      (by rw [hR.econgUpd_sum]; exact Finset.sum_congr rfl fun eW heW => (hcv_below_st _ (by have := (Finset.mem_Ico.mp heW).2; omega) (by unfold t3OffGetPath; omega)).symm)
      (fun cj hcj eL heL => by have hc_b := (ctx.hw_okW.comp_props cj hcj).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2; rw [hcv_below_st _ (by omega) (by unfold t3OffGetPath; omega)]; exact hR.del_iff cj hcj eL heL)
      (hcv_below_st _ (by unfold t3OffEcongUpd; omega) (by unfold t3OffGetPath t3OffEcongUpd; omega) |>.trans hR.econgUpd_eq)
      ⟨hr_cv_0, hr_cv_1, (hr_cv 11 (by decide)).trans (by simp [r17, r16, r15, r14, hr13_11]), (hr_cv 13 (by decide)).trans (by simp [r17, r16, r15, r14, r13]),
        (hr_cv 14 (by decide)).trans (by simp [r17, r16, r15, r14]), (hr_cv 15 (by decide)).trans (by simp [r17, r16, r15]),
        (hr_cv 17 (by decide)).trans (by simp [r17]), rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hes_ecPhi : t3EcongPhi ctx lay st_cv.mem = t3EcongPhi ctx lay st.mem :=
      t3EcongPhi_frame ctx lay
        (fun eW heW => by have := Finset.mem_Ico.mp heW; exact hcv_below_st _ (by omega) (by unfold t3OffGetPath; omega))
        (fun eW heW => by have := Finset.mem_Ico.mp heW; exact hcv_below_st _ (by omega) (by unfold t3OffGetPath; omega))
    have hes_dsPhi : dsTotalPhi impl.pathDS lay.dsHandlesAddr ctx.wd.comps.length reps1 st_cv.mem = dsTotalPhi impl.pathDS lay.dsHandlesAddr ctx.wd.comps.length reps1 mem_gp := by
      unfold dsTotalPhi; refine Finset.sum_congr rfl fun cj hcj => ?_; have hcj' := Finset.mem_range.mp hcj
      rw [hcv_below_gp (lay.dsHandlesAddr + cj) (by omega) (by unfold t3OffGetPath; omega)]
      refine (hLoc _ (d0.states cj) (reps1 cj) mem_gp st_cv.mem fun a ha => (hcv_below_gp a ((hArr_gp.at_ci cj hcj').2.2.2.1 a ha).2 (by have := ((hArr_gp.at_ci cj hcj').2.2.2.1 a ha).1; unfold t3OffGetPath; omega)).symm).2.symm
    refine t3_cps_weaken (t3_normal_ptriple_cps (T := P.verts.length * 31 + P.edges.length * 115 + 180)
      hes_pt ⟨rfl, rfl, rfl⟩ (le_refl (P.edges.length * 115 + 7)) ?_) ?_
    swap
    · rw [hes_ecPhi, hes_dsPhi, Nat.mul_add]; dsimp only [Φ_post_gp]; omega
    intro st_es Φ_es hES
    have hcv_getPath : st_cv.mem (lay.base + t3OffGetPath) = d0.getPathCnt + 1 :=
      (hm_cv_lt _ (by unfold t3OffGetPath; omega)).trans ((hcv0_lt_hm _ (by unfold t3OffGetPath; omega)).trans
        (Function.update_self _ _ _))
    have hcv_eta2 : st_cv.mem (lay.base + t3OffEta2) + 1 = rCur := by
      rw [hcv_below_st (lay.base + t3OffEta2) (by unfold t3OffEta2; omega) (by unfold t3OffGetPath t3OffEta2; omega)]
      exact hR.eta2_eq
    have hcv_del : st_cv.mem (lay.base + t3OffDel) = d0.delCnt :=
      (hcv_below_st (lay.base + t3OffDel) (by unfold t3OffDel; omega) (by unfold t3OffGetPath t3OffDel; omega)).trans hR.del_eq
    have hcv_nextU : st_cv.mem (lay.base + t3OffNextU) = d0.nextHasUnemb :=
      (hcv_below_st (lay.base + t3OffNextU) (by unfold t3OffNextU; omega) (by unfold t3OffGetPath t3OffNextU; omega)).trans hR.nextU_eq
    have hcv_r13 : st_cv.regs 13 = hMid := (hr_cv 13 (by decide)).trans (by simp [r17, r16, r15, r14, r13])
    have hcv_r14 : st_cv.regs 14 = P.verts.length := (hr_cv 14 (by decide)).trans (by simp [r17, r16, r15, r14])
    have hcv_r15 : st_cv.regs 15 = P.edges.length := (hr_cv 15 (by decide)).trans (by simp [r17, r16, r15])
    obtain ⟨o_p, stF, c_p, Φ', hr_p, hq_p, hc_p⟩ := t3_middle_post_cps ctx lay hlay hci d0 reps1 st_cv.mem regs24
      hSpec hdrain hLoc heJ hunemb hR hR.hCur_lo hle_hm hMid_le_h0 hP_edges_le hP_len_ctx hP_wk hP_nd hJ_edge hArr_gp hOld_mem_gp hES hcv_below_gp hcv_st
      ⟨hcv_eta2, hcv_getPath, hcv_del, hcv_nextU⟩
      hm_cv_verts ((hm_cv_ge _ (le_refl _)).trans (Function.update_self _ _ _))
      (fun a ha => (hm_cv_ge a (by omega)).trans ((Function.update_of_ne (show a ≠ hMid + 1 + P.verts.length by omega) _ _).trans
        ((Function.update_of_ne (show a ≠ lay.base + t3OffGetPath by unfold t3OffGetPath; omega) _ _).trans (hArr_gp.zero_from a (by omega)))))
      (fun eW heW => hcv_below_st (lay.wDelStampAddr + eW) (by have := hj0_le_Wm; omega) (by unfold t3OffGetPath; omega) |>.trans (hR.wdel_j0 eW heW))
      ⟨fun cj hcj v hv => by
          have := vhatBaseW_add_le hcj; have := vhatBaseW_le_sum (wd := ctx.wd) (ci := cj + 1)
          rw [hcv_below_st (lay.vhatStampAddr + vhatBaseW ctx.wd cj + v) (by omega) (by unfold t3OffGetPath; omega)]
          exact hR.vhat_stmp_eq cj hcj v hv,
        fun cj hcj v hv => by
          have := vhatBaseW_add_le hcj; have := vhatBaseW_le_sum (wd := ctx.wd) (ci := cj + 1)
          rw [hcv_below_st (lay.vhatStampAddr + vhatBaseW ctx.wd cj + v) (by omega) (by unfold t3OffGetPath; omega)]
          exact hR.vhat_stmp_le cj hcj v hv⟩
      ⟨(hES.regs_hi 0 (by decide) (by decide)).trans hr_cv_0, (hES.regs_hi 1 (by decide) (by decide)).trans hr_cv_1,
        (hES.regs_hi 2 (by decide) (by decide)).trans ((hr_cv 2 (by decide)).trans (by simp [r17, r16, r15, r14, r13, r12, r11, r9, r8, r7, hr2])),
        (hES.regs_hi 13 (by decide) (by decide)).trans (by simp [regs24, r20, hcv_r13]),
        (hES.regs_hi 14 (by decide) (by decide)).trans (by simp [regs24, r20, hcv_r14]),
        (hES.regs_hi 15 (by decide) (by decide)).trans (by simp [regs24, r20, hcv_r15])⟩
    rcases hq_p with ⟨rfl, d', hRnd', hg', heu', hV', hemb', heJ_eq, hnu'⟩
    have hpe_len : (partialToWalk d'.emb eJ).edges.length = P.edges.length := by
      simp only [partialToWalk, heJ_eq]; exact (mkW_isWalk_liftWSubWalk ctx.hw_okW ctx.hws hci hP_wk).2.1
    refine ⟨.returned 0, stF, c_p, Φ', hr_p, ⟨rfl, d', hRnd', hg', hpe_len ▸ heu', hV', hemb', by simp [heJ_eq], hnu'⟩, ?_⟩
    simp only [Expr.size, t3Ld, t3Add, t3Mul, t3OffWWNum, t3OffPhiDen, t3OffTau2, t3OffECnt, t3OffWDel, t3OffQueue, t3OffGetPath] at hc_p ⊢
    omega

end MinCostFlow.Spanner
