module

public import MinCostFlow.Spanner.ProgTask3RoundInit
public import MinCostFlow.Spanner.ProgTask3RoundScan

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM Cited

/-!
# One Task 3 Round (Procedure 4)

A round of Task 3 (`t3RoundBody`) does three things. It builds a fresh `PathDS` on each
component expander (`t3InitLoop_ptriple`), it scans the edges of `J` and embeds those it can
(`t3ScanLoop_ptriple`), and it commits the new round number and the flag `cont` to the header.

This file proves what the commit needs. First, `t3_round_geom` shows that the number of
unembedded edges shrinks by the factor `2/3` in the round. It uses the pure round lemma
`t3Round_math_spec`; the hypotheses of that lemma come from the scan invariant and from the
`PathDS` validity. Then `t3_outer_of_scan` turns the end state of the scan into the outer
invariant `T3OuterAt` for the next round number.
-/

/-- `T3OuterAt` reads only the memory and the first three registers. -/
lemma T3OuterAt.of_mem_eq {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    {ctx : T3Ctx impl inp mem₀ w} {lay : T3Layout} {η : ℕ} {d : T3OuterData}
    {st st' : State} {Φ : ℕ} (h : T3OuterAt ctx lay η d st Φ) (hm : st'.mem = st.mem)
    (h0 : st'.regs 0 = inp.jAddr) (h1 : st'.regs 1 = inp.t1OutAddr) (h2 : st'.regs 2 = inp.v2) :
    T3OuterAt ctx lay η d st' Φ := by
  obtain ⟨m, r, p⟩ := st
  obtain ⟨m', r', p'⟩ := st'
  simp only at hm h0 h1 h2
  subst hm
  exact ⟨h0, h1, h2, h.staticMem, h.hCur_lo, h.hCur_bd, h.zero_from, h.eta2_eq, h.getPath_eq,
    h.del_eq, h.econgUpd_eq, h.hCur_eq, h.cont_eq, h.emb_part, h.emb_j0_cov, h.emb_nodup,
    h.emb_len_W, h.emb_len_real, h.emb_mem, h.econg_cnt_eq, h.econg_le_round, h.econg_j0_le,
    h.wdel_j0, h.wdel_comp, h.vhat_stmp_le, h.getPath_cnt_le, h.econgUpd_sum, h.econgUpd_bound,
    h.econgUpd_W, h.del_le_econgUpd, h.geom, h.phi_eq⟩

/-- The volume bound of a valid `PathDS` on a component expander, in the constants of the
witness data. The `PathDS` bound uses `γ_del` and `φ_out` at the conductance `phiNum / phiDen`
of the tool, and the witness data takes the maximum of `γ_del` and the minimum of `φ_out` over
the two kinds of `PathDS`. -/
lemma t3_vhat_vol_le {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) {s : PathDSAbsState} (hV : s.Valid impl.pathDS.params)
    (hn : s.phiNum = impl.constructExpander.phiNum) (hd : s.phiDen = impl.constructExpander.phiDen)
    (hM : s.M = ctx.wd.M_W) :
    (s.G.vol s.Vhat : ℝ) ≤ ctx.wd.γ_del * (s.deleted.card : ℝ) / ctx.wd.φ_ds := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hvol⟩ := hV
  have hφin : s.φ_in = impl.constructExpander.φ_Const := by
    simp only [PathDSAbsState.φ_in, ConstructExpanderImpl.φ_Const, hn, hd]
  rw [hφin, hM] at hvol
  have hround : ⌈1 / roundPhi impl.constructExpander.φ_Const⌉₊ =
      ⌈1 / impl.constructExpander.φ_Const⌉₊ := by
    unfold roundPhi; rw [one_div_one_div]; exact Nat.ceil_natCast _
  have hγ : impl.pathDS.params.γ_del impl.constructExpander.φ_Const ctx.wd.M_W ≤ ctx.wd.γ_del := by
    change _ ≤ max (impl.pathDS.params.γ_del (roundPhi _) _)
      (impl.pathDS.params.γ_del (roundPhi impl.constructExpander.φ_Const) ctx.wd.M_W)
    refine le_trans ?_ (le_max_right _ _)
    simp only [PathDSParams.γ_del, hround]; exact le_refl _
  have hφ : ctx.wd.φ_ds ≤ impl.pathDS.params.φ_out impl.constructExpander.φ_Const ctx.wd.M_W := by
    change min (impl.pathDS.params.φ_out (roundPhi _) _)
      (impl.pathDS.params.φ_out (roundPhi impl.constructExpander.φ_Const) ctx.wd.M_W) ≤ _
    refine le_trans (min_le_right _ _) ?_
    simp only [PathDSParams.φ_out, hround]; exact le_refl _
  have hφds_pos : 0 < ctx.wd.φ_ds := ctx.hw_okW.φ_ds_pos
  have hγ_ge : 1 ≤ ctx.wd.γ_del := ctx.hw_okW.γ_del_ge
  have hφo_pos := impl.pathDS.params.hφ_out_pos impl.constructExpander.φ_Const ctx.wd.M_W
    impl.constructExpander.hφ_Const_pos
  calc (s.G.vol s.Vhat : ℝ)
      ≤ impl.pathDS.params.γ_del impl.constructExpander.φ_Const ctx.wd.M_W *
          (s.deleted.card : ℝ) /
        impl.pathDS.params.φ_out impl.constructExpander.φ_Const ctx.wd.M_W := hvol
    _ ≤ ctx.wd.γ_del * (s.deleted.card : ℝ) /
        impl.pathDS.params.φ_out impl.constructExpander.φ_Const ctx.wd.M_W := by gcongr
    _ ≤ ctx.wd.γ_del * (s.deleted.card : ℝ) / ctx.wd.φ_ds := by
        apply div_le_div_of_nonneg_left (by positivity) hφds_pos hφ

/-- The number of unembedded edges shrinks by `2/3` in a round. At the end of the scan of round
`η + 1`, the outer bound `3^η · |U| ≤ 2^η · m` of round `η` becomes the bound for `η + 1`. -/
lemma t3_round_geom {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout)
    {η : ℕ} {d0 : T3OuterData} {stO : State} {ΦO : ℕ} (hO : T3OuterAt ctx lay η d0 stO ΦO)
    {d : T3RoundData impl.pathDS} {Φr : ℕ} {st : State} {Φ : ℕ}
    (hS : T3ScanAt ctx lay (η + 1) d0.emb inp.J.m d Φr st Φ) :
    3 ^ (η + 1) * (unembeddedSet2Pure inp.J d.emb).card ≤ 2 ^ (η + 1) * inp.J.m := by
  have hR := hS.round
  have hok : ∀ {N_max : ℕ} {W_max : ℝ} (tools : LocalSpannerTools N_max W_max),
      WitnessOK tools ctx.wInp.H' ctx.wInp.prep.J ctx.wInp.embJH ctx.wd := by
    intro N_max W_max tools
    have h := ctx.hw_ok tools
    rw [ctx.hWInpH', ctx.hWInpJ]
    rcases h with ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17,
      f18, f19, f20, f21, f22⟩
    exact ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19,
      f20, f21, f22⟩
  -- The facts on each `PathDS` that the round lemma needs.
  have hds : ∀ (ci : ℕ) (hci : ci < ctx.wd.comps.length),
      (d.states ci).G = ctx.wd.comps[ci].W_sub ∧ (d.states ci).Valid impl.pathDS.params ∧
      (d.states ci).phiNum = impl.constructExpander.phiNum ∧
      (d.states ci).phiDen = impl.constructExpander.phiDen ∧ (d.states ci).M = ctx.wd.M_W := by
    intro ci hci
    obtain ⟨-, -, -, -, hG, hn, hd, hM, hval⟩ := hR.dsArr.at_ci ci hci
    rw [List.getD_eq_getElem _ _ hci] at hG
    exact ⟨hG, hval, hn, hd, hM⟩
  have hdel : ∀ (ci : ℕ) (hci : ci < ctx.wd.comps.length), ∀ eL ∈ (d.states ci).deleted,
      eL < ctx.wd.comps[ci].W_sub.m ∧
        ((η + 1 : ℕ) : ℝ) * ctx.wd.τ₂ ≤ econgAt inp.J (fun _ => 1) ctx.wd.wW
          (partialToWalk d.emb) (ctx.wd.comps[ci].wStart + eL) := by
    intro ci hci eL heL
    obtain ⟨hG, hval, -, -, -⟩ := hds ci hci
    obtain ⟨-, -, -, -, -, -, -, -, hDsub, -⟩ := hval
    have hlt : eL < ctx.wd.comps[ci].W_sub.m := by
      have := Finset.mem_range.mp (hDsub heL); rwa [hG] at this
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hj0, hWm⟩ :=
      ctx.hw_okW.comp_props ci hci
    have hst := (hR.del_iff ci hci eL hlt).mp heL
    exact ⟨hlt, hR.wdel_thresh _ (Finset.mem_Ico.mpr ⟨by omega, by omega⟩) hst⟩
  have hvsub : ∀ (ci : ℕ) (hci : ci < ctx.wd.comps.length),
      (d.states ci).Vhat ⊆ ctx.wd.comps[ci].W_sub.verts := by
    intro ci hci
    obtain ⟨hG, hval, -, -, -⟩ := hds ci hci
    obtain ⟨-, -, -, -, -, -, -, hVsub, -, -⟩ := hval
    rwa [hG] at hVsub
  have hvvol : ∀ (ci : ℕ) (hci : ci < ctx.wd.comps.length),
      (ctx.wd.comps[ci].W_sub.vol (d.states ci).Vhat : ℝ) ≤
        ctx.wd.γ_del * ((d.states ci).deleted.card : ℝ) / ctx.wd.φ_ds := by
    intro ci hci
    obtain ⟨hG, hval, hn, hd, hM⟩ := hds ci hci
    have := t3_vhat_vol_le ctx hval hn hd hM
    rwa [hG] at this
  have hunemb : ∀ eJ < inp.J.m, (d.emb eJ).isNone = true → T3Skipped ctx d.states eJ :=
    fun eJ heJ h => hS.skipped eJ heJ (Option.isNone_iff_eq_none.mp h)
  obtain ⟨-, h3, -, -⟩ := t3Round_math_spec (inp := ctx.wInp) (ce := impl.constructExpander)
    (pds := impl.pathDS.params) (WSubs := ctx.WSubs) (η_prev := η) (emb₀ := d0.emb)
    (emb₁ := d.emb) (delW := fun ci => (d.states ci).deleted)
    (vhatW := fun ci => (d.states ci).Vhat) hok ctx.hws
    (by rw [ctx.hWInpJ]; exact hS.mono) (by rw [ctx.hWInpJ]; exact hR.emb_len_real)
    (by rw [ctx.hWInpJ]; exact hO.econg_le_round) (by rw [ctx.hWInpJ]; exact hdel) hvsub hvvol
    (by rw [ctx.hWInpJ]; exact hunemb) (by rw [ctx.hWInpJ]; exact ctx.jSubOrig_of_inComp)
  rw [ctx.hWInpJ] at h3
  have hg := hO.geom
  calc 3 ^ (η + 1) * (unembeddedSet2Pure inp.J d.emb).card
      = 3 ^ η * (3 * (unembeddedSet2Pure inp.J d.emb).card) := by ring
    _ ≤ 3 ^ η * (2 * (unembeddedSet2Pure inp.J d0.emb).card) := Nat.mul_le_mul_left _ h3
    _ = 2 * (3 ^ η * (unembeddedSet2Pure inp.J d0.emb).card) := by ring
    _ ≤ 2 * (2 ^ η * inp.J.m) := Nat.mul_le_mul_left _ hg
    _ = 2 ^ (η + 1) * inp.J.m := by ring

/-- The commit of a round. After the scan of round `η + 1`, the program writes `η + 1` to the
round counter and the flag `nextHasUnemb` to `cont`. The result satisfies the outer invariant
for `η + 1`, with the potential `t3KdelCost · t3EcongPhi` only. -/
lemma t3_outer_of_scan {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (hlay : lay = T3Layout.ofCtx ctx)
    {η : ℕ} {emb0 : ℕ → Option Walk} {d : T3RoundData impl.pathDS} {Φr : ℕ} {st : State} {Φ : ℕ}
    (hS : T3ScanAt ctx lay (η + 1) emb0 inp.J.m d Φr st Φ)
    (hgeom : 3 ^ (η + 1) * (unembeddedSet2Pure inp.J d.emb).card ≤ 2 ^ (η + 1) * inp.J.m)
    {st' : State}
    (hm : st'.mem = Function.update (Function.update st.mem (lay.base + t3OffEta2) (η + 1))
      (lay.base + t3OffCont) d.nextHasUnemb)
    (h0 : st'.regs 0 = inp.jAddr) (h1 : st'.regs 1 = inp.t1OutAddr) (h2 : st'.regs 2 = inp.v2) :
    T3OuterAt ctx lay (η + 1) d.toOuter st' (t3KdelCost impl inp.J * t3EcongPhi ctx lay st'.mem) := by
  have hR := hS.round
  have hb := T3Layout.bounds ctx; dsimp only at hb; rw [← hlay] at hb; unfold t3HdrSize at hb
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12⟩ := hb
  set mem' := Function.update (Function.update st.mem (lay.base + t3OffEta2) (η + 1))
      (lay.base + t3OffCont) d.nextHasUnemb with hmem'
  have hne : ∀ x, x ≠ lay.base + t3OffEta2 → x ≠ lay.base + t3OffCont → mem' x = st.mem x :=
    fun x h1 h2 => by rw [hmem', Function.update_of_ne h2, Function.update_of_ne h1]
  have hfar : ∀ x, lay.embJWAddr ≤ x → mem' x = st.mem x := fun x hx =>
    hne x (by unfold t3OffEta2; omega) (by unfold t3OffCont; omega)
  have hhdr : ∀ i, i ≠ t3OffEta2 → i ≠ t3OffCont →
      mem' (lay.base + i) = st.mem (lay.base + i) := fun i h1 h2 =>
    hne _ (by omega) (by omega)
  have hlo := hR.hCur_lo
  obtain ⟨m', r', p'⟩ := st'
  simp only at hm h0 h1 h2
  subst hm
  have hcont : d.nextHasUnemb =
      if (unembeddedSet2Pure inp.J d.emb).Nonempty then 1 else 0 := by
    rcases hR.nextU_bin with h | h
    · have hne : ¬ (unembeddedSet2Pure inp.J d.emb).Nonempty := by
        rintro ⟨eJ, heJ⟩
        simp only [unembeddedSet2Pure, Finset.mem_filter, Finset.mem_range,
          Option.isNone_iff_eq_none] at heJ
        have := hS.nextU.mpr ⟨eJ, heJ.1, heJ.2⟩
        omega
      simp [hne, h]
    · obtain ⟨eJ, heJ, hn⟩ := hS.nextU.mp h
      have hmem : eJ ∈ unembeddedSet2Pure inp.J d.emb := by
        simp only [unembeddedSet2Pure, Finset.mem_filter, Finset.mem_range,
          Option.isNone_iff_eq_none]
        exact ⟨heJ, hn⟩
      simp [h, show (unembeddedSet2Pure inp.J d.emb).Nonempty from ⟨eJ, hmem⟩]
  exact
    { reg0 := h0
      reg1 := h1
      reg2 := h2
      staticMem := hR.staticMem.mono (fun x hx => hne x (by unfold t3OffEta2; omega)
          (by unfold t3OffCont; omega))
        (fun i _ hE _ _ _ _ _ hC => hhdr i hE hC) (fun ci _ => hfar _ (by omega))
      hCur_lo := hR.hCur_lo
      hCur_bd := hR.hCur_bd
      zero_from := fun x hx => by
        dsimp only [T3RoundData.toOuter] at hx ⊢; rw [hfar x (by omega)]; exact hR.zero_from x hx
      eta2_eq := by
        dsimp only
        rw [hmem', Function.update_of_ne (by unfold t3OffEta2 t3OffCont; omega),
          Function.update_self]
      getPath_eq := by dsimp only; rw [hhdr t3OffGetPath (by decide) (by decide)]; exact hR.getPath_eq
      del_eq := by dsimp only; rw [hhdr t3OffDel (by decide) (by decide)]; exact hR.del_eq
      econgUpd_eq := by
        dsimp only; rw [hhdr t3OffEcongUpd (by decide) (by decide)]; exact hR.econgUpd_eq
      hCur_eq := by dsimp only; rw [hhdr t3OffHCur (by decide) (by decide)]; exact hR.hCur_eq
      cont_eq := by
        dsimp only [T3RoundData.toOuter]
        rw [hmem', Function.update_self]
        exact hcont
      emb_part := hR.emb_part
      emb_j0_cov := hR.emb_j0_cov
      emb_nodup := hR.emb_nodup
      emb_len_W := hR.emb_len_W
      emb_len_real := hR.emb_len_real
      emb_mem := fun eJ heJ => by
        have hm := hR.emb_mem eJ heJ
        have hslot := hfar (lay.embJWAddr + eJ) (by omega)
        dsimp only [T3RoundData.toOuter]
        rw [hslot]
        rcases hE : d.emb eJ with _ | P
        · rw [hE] at hm; exact hm
        · rw [hE] at hm
          obtain ⟨h1, h2, h3, -⟩ := hm
          exact ⟨h1, h2, t3_walkAt_of_agree h3 fun x hx1 _ => hfar x (by omega)⟩
      econg_cnt_eq := fun eW heW => by
        dsimp only; rw [hfar _ (by omega)]; exact hR.econg_cnt_eq eW heW
      econg_le_round := hR.econg_le_round
      econg_j0_le := hR.econg_j0_le
      wdel_j0 := fun eW heW => by
        have : ctx.wd.j0Edges.length ≤ ctx.wd.W.m := by
          simp [T3Ctx.wd, WitnessCoreInput.mkWitnessData, Graph.m]
        dsimp only; rw [hfar _ (by omega)]; exact hR.wdel_j0 eW heW
      wdel_comp := fun eW heW => by
        dsimp only
        rw [hfar _ (by omega), hfar (lay.econgCountAddr + eW) (by omega)]
        exact hR.wdel_comp eW heW
      vhat_stmp_le := fun ci hci v hv => by
        dsimp only; rw [hfar _ (by omega)]; exact hR.vhat_stmp_le ci hci v hv
      getPath_cnt_le := hR.getPath_cnt_le
      econgUpd_sum := hR.econgUpd_sum.trans
        (Finset.sum_congr rfl fun eW _ => (hfar _ (by omega)).symm)
      econgUpd_bound := hR.econgUpd_bound
      econgUpd_W := hR.econgUpd_W
      del_le_econgUpd := hR.del_le_econgUpd
      geom := hgeom
      phi_eq := rfl }

end MinCostFlow.Spanner
