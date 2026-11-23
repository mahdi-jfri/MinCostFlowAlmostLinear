module

public import MinCostFlow.Spanner.ProgTask3MiddleProof

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM Cited

/-!
# The Edge Scan of a Task 3 Round

After the init loop, a Task 3 round (`t3RoundBody`) scans the edges `eJ < J.m` once. An edge
that is already embedded is skipped. For an unembedded edge `eJ`, the program reads its
component `ci` and local index `jL`, and the two endpoints in `W_sub`. If an endpoint is already
in `Vhat` (its stamp equals the round number), the edge waits for a later round and the program
sets `nextHasUnemb := 1`. Otherwise it embeds the edge with procedure 3 (`t3MiddleEdge_ptriple`).

Embedding an edge costs a `GetPath` query, which `task3Cost` charges once per edge over the whole
run, not once per round. So the scan carries the potential `E · |unembedded|`, where `E` is the
cost of procedure 3, and each call is paid by the drop of this potential.

The invariant is `T3ScanAt` and the main result is `t3ScanLoop_ptriple`.
-/

/-- One step of the edge scan of `t3RoundBody` (edge index in register 14). -/
def t3ScanStep (middleBase : ℕ) : Stmt :=
  Stmt.seq (.assign 15 (.load (t3Add (.reg 9) (.reg 14))))
    (.cond (t3Eq (.reg 15) (.const 0))
      (Stmt.seq (.assign 16 (t3Ld (.reg 10) (t3Add (t3Mul (.const 3) (.reg 14)) (.const 1))))
        (Stmt.seq (.assign 17 (t3Ld (.reg 10) (t3Add (t3Mul (.const 3) (.reg 14)) (.const 2))))
          (Stmt.seq (.assign 18 (t3Ld (.reg 11) (t3Add (t3Mul (.const 7) (.reg 16)) (.const 3))))
            (Stmt.seq (.assign 19 (t3Ld (.reg 18) (t3Add (.const 2) (t3Mul (.const 2) (.reg 17)))))
              (Stmt.seq (.assign 20 (t3Ld (.reg 18) (t3Add (.const 3) (t3Mul (.const 2) (.reg 17)))))
                (Stmt.seq (.assign 21 (.load (t3Add (.reg 12) (.reg 16))))
                  (Stmt.seq (.assign 22 (.load (t3Add (.reg 13) (t3Add (.reg 21) (.reg 19)))))
                    (Stmt.seq (.assign 23 (.load (t3Add (.reg 13) (t3Add (.reg 21) (.reg 20)))))
                      (.cond (t3Eq (t3Or (t3Eq (.reg 22) (.reg 1)) (t3Eq (.reg 23) (.reg 1)))
                          (.const 1))
                        (t3St (.reg 0) (.const t3OffNextU) (.const 1))
                        (.call 22 middleBase [.reg 0, .reg 1, .reg 14, .reg 16, .reg 17]))))))))))
      .nop)

/-- Cost of procedure 3 (`t3MiddleEdge_ptriple`), paid once per embedded edge. -/
noncomputable def t3MiddleCost (impl : SpannerToolImpl) (J : Graph) : ℕ :=
  ⌈impl.pathDS.params.K_query * (impl.pathDS.params.gQuery
      (WitnessCoreInput.dWInt impl.constructExpander) (Task1Input.mwCap impl J) : ℝ)⌉₊ +
    impl.pathDS.params.gExp (WitnessCoreInput.dWInt impl.constructExpander)
      (Task1Input.mwCap impl J) *
      (⌈impl.pathDS.params.K_del * (impl.pathDS.params.gQuery
        (WitnessCoreInput.dWInt impl.constructExpander) (Task1Input.mwCap impl J) : ℝ)⌉₊ + 300) +
    380

/-- An unembedded edge `eJ` that the scan skipped: it lies in a component whose `Vhat` already
holds one of its endpoints. -/
def T3Skipped {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (states : ℕ → PathDSAbsState) (eJ : ℕ) : Prop :=
  ∃ (ci : ℕ) (hci : ci < ctx.wd.comps.length) (jL : ℕ),
    jL < ctx.wd.comps[ci].J_sub.m ∧
    ctx.wd.jSources.getD eJ JEdgeSource.isLoop = JEdgeSource.inComp ci jL ∧
    ((ctx.wd.comps[ci].J_sub.edges.getD jL (0, 0)).1 ∈ (states ci).Vhat ∨
     (ctx.wd.comps[ci].J_sub.edges.getD jL (0, 0)).2 ∈ (states ci).Vhat)

lemma T3Skipped.mono {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    {ctx : T3Ctx impl inp mem₀ w} {s₁ s₂ : ℕ → PathDSAbsState} {eJ : ℕ}
    (h : T3Skipped ctx s₁ eJ) (hsub : ∀ ci < ctx.wd.comps.length, (s₁ ci).Vhat ⊆ (s₂ ci).Vhat) :
    T3Skipped ctx s₂ eJ := by
  obtain ⟨ci, hci, jL, hjL, hsrc, hin⟩ := h
  exact ⟨ci, hci, jL, hjL, hsrc, hin.imp (fun h => hsub ci hci h) (fun h => hsub ci hci h)⟩

/-- Invariant of the edge scan after the edges `eJ < e`. The round ghost data is `d` with round
potential `Φr`. The emb at the start of the round is `emb0`. -/
structure T3ScanAt {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (rCur : ℕ) (emb0 : ℕ → Option Walk) (e : ℕ)
    (d : T3RoundData impl.pathDS) (Φr : ℕ) (st : State) (Φ : ℕ) : Prop where
  round : T3RoundAt ctx lay rCur d st Φr
  phi : Φ = Φr + t3MiddleCost impl inp.J * (unembeddedSet2Pure inp.J d.emb).card
  r0 : st.regs 0 = lay.base
  r1 : st.regs 1 = rCur
  r8 : st.regs 8 = inp.J.m
  r9 : st.regs 9 = lay.embJWAddr
  r10 : st.regs 10 = ctx.memT1 (ctx.wInp.h + 16)
  r11 : st.regs 11 = ctx.wInp.prep.aComps
  r12 : st.regs 12 = lay.vhatOffsetAddr
  r13 : st.regs 13 = lay.vhatStampAddr
  r14 : st.regs 14 = e
  mono : ∀ eJ < inp.J.m, emb0 eJ = none ∨ d.emb eJ = emb0 eJ
  skipped : ∀ eJ < e, d.emb eJ = none → T3Skipped ctx d.states eJ
  nextU : d.nextHasUnemb = 1 ↔ ∃ eJ < e, d.emb eJ = none

/-- `T3ScanAt` with the ghost data hidden. -/
def T3ScanInv {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (rCur : ℕ) (emb0 : ℕ → Option Walk) (e : ℕ)
    (st : State) (Φ : ℕ) : Prop :=
  ∃ d Φr, T3ScanAt ctx lay rCur emb0 e d Φr st Φ

/-- `T3RoundAt` reads only the memory, so it moves to any state with the same memory. -/
lemma T3RoundAt.of_mem_eq {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    {ctx : T3Ctx impl inp mem₀ w} {lay : T3Layout} {rCur : ℕ} {d : T3RoundData impl.pathDS}
    {st st' : State} {Φ : ℕ} (h : T3RoundAt ctx lay rCur d st Φ) (hm : st'.mem = st.mem) :
    T3RoundAt ctx lay rCur d st' Φ := by
  obtain ⟨m, r, p⟩ := st
  obtain ⟨m', r', p'⟩ := st'
  simp only at hm
  subst hm
  exact ⟨h.rCur_pos, h.rCur_le, h.staticMem, h.dsArr, h.hCur_lo, h.hCur_bd, h.zero_from,
    h.eta2_eq, h.getPath_eq, h.del_eq, h.econgUpd_eq, h.hCur_eq, h.nextU_eq, h.nextU_bin,
    h.emb_part, h.emb_j0_cov, h.emb_nodup, h.emb_len_W, h.emb_len_real, h.emb_mem,
    h.econg_cnt_eq, h.econg_le_round, h.econg_j0_le, h.wdel_j0, h.wdel_comp, h.wdel_thresh,
    h.wdel_lt_econg, h.getPath_cnt_le, h.econgUpd_sum, h.econgUpd_bound, h.econgUpd_W,
    h.del_le_econgUpd, h.del_iff, h.vhat_stmp_eq, h.vhat_stmp_le, h.phi_eq⟩

/-- Embedding one edge `e` removes exactly `e` from the set of unembedded edges. -/
lemma t3_unemb_card_embed {J : Graph} {emb emb' : ℕ → Option Walk} {e : ℕ} (he : e < J.m)
    (hnone : emb e = none) (hsome : (emb' e).isSome = true)
    (hsame : ∀ e' < J.m, e' ≠ e → emb' e' = emb e') :
    (unembeddedSet2Pure J emb).card = (unembeddedSet2Pure J emb').card + 1 := by
  have hset : unembeddedSet2Pure J emb = insert e (unembeddedSet2Pure J emb') := by
    ext x
    simp only [unembeddedSet2Pure, Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    constructor
    · rintro ⟨hx, hn⟩
      by_cases hxe : x = e
      · exact Or.inl hxe
      · exact Or.inr ⟨hx, by rw [hsame x hx hxe]; exact hn⟩
    · rintro (rfl | ⟨hx, hn⟩)
      · exact ⟨he, by simp [hnone]⟩
      · by_cases hxe : x = e
        · subst hxe
          simp [Option.isNone_iff_eq_none] at hn
          simp [hn] at hsome
        · exact ⟨hx, by rw [← hsame x hx hxe]; exact hn⟩
  rw [hset, Finset.card_insert_of_notMem]
  simp [unembeddedSet2Pure, Option.isNone_iff_eq_none, Option.isSome_iff_ne_none.mp hsome]

/-- Continuation form of `Stmt.cond`. -/
lemma t3_cond_cps {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s t : Stmt} {st : State}
    {v k T : ℕ} {Q : Outcome → State → ℕ → Prop} (he : e.eval w st = some v)
    (hrest : ∃ o stF c Φ', Runs w p ω (if v = 0 then t else s) st o stF c ∧ Q o stF Φ' ∧
      (k + e.size + 1) + c + Φ' ≤ T) :
    ∃ o stF c Φ', Runs w p ω (.cond e s t) st o stF c ∧ Q o stF Φ' ∧ k + c + Φ' ≤ T := by
  obtain ⟨o, stF, c, Φ', hr, hq, hc⟩ := hrest
  exact ⟨o, stF, e.size + c + 1, Φ', runs_cond_iff.mpr ⟨v, c, he, hr, rfl⟩, hq, by omega⟩

/-! ## Continuation forms of the loads used by the scan -/

lemma t3_ldMul_cps {w : ℕ} {p : Program} {ω : ℕ → Bool} {mem regs : ℕ → ℕ}
    {pos rd rs ri c k b i v k0 T : ℕ} {s : Stmt} {Q : Outcome → State → ℕ → Prop}
    (hr : regs rs = b) (hi : regs ri = i) (hc : c < 2 ^ w) (hk : k < 2 ^ w)
    (hci : c * i < 2 ^ w) (hcik : c * i + k < 2 ^ w) (hadd : b + (c * i + k) < 2 ^ w)
    (hm : mem (b + (c * i + k)) = v)
    (hrest : ∃ o stF c_s Φ', Runs w p ω s ⟨mem, Function.update regs rd v, pos⟩ o stF c_s ∧
      Q o stF Φ' ∧ (k0 + 10) + c_s + Φ' ≤ T) :
    ∃ o stF c_tot Φ', Runs w p ω
      (.seq (.assign rd (t3Ld (.reg rs) (t3Add (t3Mul (.const c) (.reg ri)) (.const k)))) s)
      ⟨mem, regs, pos⟩ o stF c_tot ∧ Q o stF Φ' ∧ k0 + c_tot + Φ' ≤ T :=
  t3_assign_cps (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr)
    (Expr.eval_add (Expr.eval_mul (Expr.eval_const hc) (Expr.eval_reg_of_eq hi) hci)
      (Expr.eval_const hk) hcik) hadd) hm) (by simpa [Expr.size, t3Ld, t3Add, t3Mul] using hrest)

lemma t3_ldAddMul_cps {w : ℕ} {p : Program} {ω : ℕ → Bool} {mem regs : ℕ → ℕ}
    {pos rd rs ri c k b i v k0 T : ℕ} {s : Stmt} {Q : Outcome → State → ℕ → Prop}
    (hr : regs rs = b) (hi : regs ri = i) (hc : c < 2 ^ w) (hk : k < 2 ^ w)
    (hci : c * i < 2 ^ w) (hcik : k + c * i < 2 ^ w) (hadd : b + (k + c * i) < 2 ^ w)
    (hm : mem (b + (k + c * i)) = v)
    (hrest : ∃ o stF c_s Φ', Runs w p ω s ⟨mem, Function.update regs rd v, pos⟩ o stF c_s ∧
      Q o stF Φ' ∧ (k0 + 10) + c_s + Φ' ≤ T) :
    ∃ o stF c_tot Φ', Runs w p ω
      (.seq (.assign rd (t3Ld (.reg rs) (t3Add (.const k) (t3Mul (.const c) (.reg ri))))) s)
      ⟨mem, regs, pos⟩ o stF c_tot ∧ Q o stF Φ' ∧ k0 + c_tot + Φ' ≤ T :=
  t3_assign_cps (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr)
    (Expr.eval_add (Expr.eval_const hk) (Expr.eval_mul (Expr.eval_const hc) (Expr.eval_reg_of_eq hi) hci)
      hcik) hadd) hm) (by simpa [Expr.size, t3Ld, t3Add, t3Mul] using hrest)

lemma t3_ldRR_cps {w : ℕ} {p : Program} {ω : ℕ → Bool} {mem regs : ℕ → ℕ}
    {pos rd ra rb a b v k0 T : ℕ} {s : Stmt} {Q : Outcome → State → ℕ → Prop}
    (ha : regs ra = a) (hb : regs rb = b) (hadd : a + b < 2 ^ w) (hm : mem (a + b) = v)
    (hrest : ∃ o stF c_s Φ', Runs w p ω s ⟨mem, Function.update regs rd v, pos⟩ o stF c_s ∧
      Q o stF Φ' ∧ (k0 + 6) + c_s + Φ' ≤ T) :
    ∃ o stF c_tot Φ', Runs w p ω (.seq (.assign rd (.load (t3Add (.reg ra) (.reg rb)))) s)
      ⟨mem, regs, pos⟩ o stF c_tot ∧ Q o stF Φ' ∧ k0 + c_tot + Φ' ≤ T :=
  t3_assign_cps (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq ha)
    (Expr.eval_reg_of_eq hb) hadd) hm) (by simpa [Expr.size, t3Add] using hrest)

lemma t3_ldRRR_cps {w : ℕ} {p : Program} {ω : ℕ → Bool} {mem regs : ℕ → ℕ}
    {pos rd ra rb rc a b c v k0 T : ℕ} {s : Stmt} {Q : Outcome → State → ℕ → Prop}
    (ha : regs ra = a) (hb : regs rb = b) (hc : regs rc = c) (hbc : b + c < 2 ^ w)
    (hadd : a + (b + c) < 2 ^ w) (hm : mem (a + (b + c)) = v)
    (hrest : ∃ o stF c_s Φ', Runs w p ω s ⟨mem, Function.update regs rd v, pos⟩ o stF c_s ∧
      Q o stF Φ' ∧ (k0 + 8) + c_s + Φ' ≤ T) :
    ∃ o stF c_tot Φ', Runs w p ω
      (.seq (.assign rd (.load (t3Add (.reg ra) (t3Add (.reg rb) (.reg rc))))) s)
      ⟨mem, regs, pos⟩ o stF c_tot ∧ Q o stF Φ' ∧ k0 + c_tot + Φ' ≤ T :=
  t3_assign_cps (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq ha)
    (Expr.eval_add (Expr.eval_reg_of_eq hb) (Expr.eval_reg_of_eq hc) hbc) hadd) hm)
    (by simpa [Expr.size, t3Add] using hrest)

/-- Writing `nextHasUnemb := 1` keeps the round invariant. -/
lemma T3RoundAt.set_nextU {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    {ctx : T3Ctx impl inp mem₀ w} {lay : T3Layout} (hlay : lay = T3Layout.ofCtx ctx)
    (hLoc : impl.pathDS.R.Local) {rCur : ℕ} {d : T3RoundData impl.pathDS} {st : State} {Φ : ℕ}
    (hR : T3RoundAt ctx lay rCur d st Φ) :
    T3RoundAt ctx lay rCur { d with nextHasUnemb := 1 }
      { st with mem := Function.update st.mem (lay.base + t3OffNextU) 1 } Φ := by
  have hb := T3Layout.bounds ctx; dsimp only at hb; rw [← hlay] at hb; unfold t3HdrSize at hb
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12⟩ := hb
  set mem' := Function.update st.mem (lay.base + t3OffNextU) 1
  have hne : ∀ x, x ≠ lay.base + t3OffNextU → mem' x = st.mem x := fun x hx =>
    Function.update_of_ne hx _ _
  have hfar : ∀ x, lay.embJWAddr ≤ x → mem' x = st.mem x := fun x hx =>
    hne x (by unfold t3OffNextU; omega)
  have hlo := hR.hCur_lo
  have hDS := hR.dsArr.frame_range hLoc (mem' := mem') (fun ci _ => hfar _ (by omega))
    (fun a ha _ => hfar a (by omega))
    (fun a ha => by rw [hfar a (by omega)]; exact hR.dsArr.zero_from a ha)
  have hhdr : ∀ i, i ≠ t3OffNextU → mem' (lay.base + i) = st.mem (lay.base + i) := fun i hi =>
    hne _ (by omega)
  exact
    { rCur_pos := hR.rCur_pos
      rCur_le := hR.rCur_le
      staticMem := hR.staticMem.mono (fun x hx => hne x (by unfold t3OffNextU; omega))
        (fun i _ _ _ _ _ _ hN _ => hhdr i hN) (fun ci _ => hfar _ (by omega))
      dsArr := hDS.1
      hCur_lo := hR.hCur_lo
      hCur_bd := hR.hCur_bd
      zero_from := fun x hx => by dsimp only at hx ⊢; rw [hfar x (by omega)]; exact hR.zero_from x hx
      eta2_eq := by dsimp only; rw [hhdr t3OffEta2 (by decide)]; exact hR.eta2_eq
      getPath_eq := by dsimp only; rw [hhdr t3OffGetPath (by decide)]; exact hR.getPath_eq
      del_eq := by dsimp only; rw [hhdr t3OffDel (by decide)]; exact hR.del_eq
      econgUpd_eq := by dsimp only; rw [hhdr t3OffEcongUpd (by decide)]; exact hR.econgUpd_eq
      hCur_eq := by dsimp only; rw [hhdr t3OffHCur (by decide)]; exact hR.hCur_eq
      nextU_eq := Function.update_self _ _ _
      nextU_bin := Or.inr rfl
      emb_part := hR.emb_part
      emb_j0_cov := hR.emb_j0_cov
      emb_nodup := hR.emb_nodup
      emb_len_W := hR.emb_len_W
      emb_len_real := hR.emb_len_real
      emb_mem := fun eJ heJ => by
        have hm := hR.emb_mem eJ heJ
        have hslot := hfar (lay.embJWAddr + eJ) (by omega)
        dsimp only
        rw [hslot]
        rcases hE : d.emb eJ with _ | P
        · rw [hE] at hm; exact hm
        · rw [hE] at hm
          obtain ⟨h1, h2, h3, h4⟩ := hm
          refine ⟨h1, h2, t3_walkAt_of_agree h3 fun x hx1 _ => hfar x (by omega), ?_⟩
          intro a ha1 ha2 cj hcj
          rw [hfar _ (by omega)]
          exact h4 a ha1 ha2 cj hcj
      econg_cnt_eq := fun eW heW => by dsimp only; rw [hfar _ (by omega)]; exact hR.econg_cnt_eq eW heW
      econg_le_round := hR.econg_le_round
      econg_j0_le := hR.econg_j0_le
      wdel_j0 := fun eW heW => by
        have : ctx.wd.j0Edges.length ≤ ctx.wd.W.m := by
          simp [T3Ctx.wd, WitnessCoreInput.mkWitnessData, Graph.m]
        dsimp only; rw [hfar _ (by omega)]; exact hR.wdel_j0 eW heW
      wdel_comp := fun eW heW => by
        dsimp only; rw [hfar _ (by omega), hfar (lay.econgCountAddr + eW) (by omega)]; exact hR.wdel_comp eW heW
      wdel_thresh := fun eW heW h => by
        dsimp only at h ⊢; rw [hfar _ (by omega)] at h; exact hR.wdel_thresh eW heW h
      wdel_lt_econg := fun eW heW h => by
        dsimp only at h ⊢; rw [hfar _ (by omega)] at h; exact hR.wdel_lt_econg eW heW h
      getPath_cnt_le := hR.getPath_cnt_le
      econgUpd_sum := hR.econgUpd_sum.trans (Finset.sum_congr rfl fun eW _ => (hfar _ (by omega)).symm)
      econgUpd_bound := hR.econgUpd_bound
      econgUpd_W := hR.econgUpd_W
      del_le_econgUpd := hR.del_le_econgUpd
      del_iff := fun ci hci eL heL => by
        dsimp only; rw [hfar _ (by omega)]; exact hR.del_iff ci hci eL heL
      vhat_stmp_eq := fun ci hci v hv => by
        dsimp only; rw [hfar _ (by omega)]; exact hR.vhat_stmp_eq ci hci v hv
      vhat_stmp_le := fun ci hci v hv => by
        dsimp only; rw [hfar _ (by omega)]; exact hR.vhat_stmp_le ci hci v hv
      phi_eq := by
        rw [hR.phi_eq]
        unfold t3RoundPhi
        rw [t3EcongPhi_frame ctx lay (fun eW _ => hfar _ (by omega)) (fun eW _ => hfar _ (by omega)),
          hDS.2] }

/-- The value of the hit test `(stamp u = rCur) or (stamp v = rCur)`, compared with `1`. -/
private lemma t3_hit_eval {w : ℕ} {st : State} {su sv rCur : ℕ} (hw : 1 < 2 ^ w)
    (h22 : st.regs 22 = su) (h23 : st.regs 23 = sv) (h1 : st.regs 1 = rCur) :
    (t3Eq (t3Or (t3Eq (.reg 22) (.reg 1)) (t3Eq (.reg 23) (.reg 1))) (.const 1)).eval w st =
      some (if su = rCur ∨ sv = rCur then 1 else 0) := by
  have e1 := Expr.eval_eq_op (Expr.eval_reg_of_eq h22) (Expr.eval_reg_of_eq h1) hw
  have e2 := Expr.eval_eq_op (Expr.eval_reg_of_eq h23) (Expr.eval_reg_of_eq h1) hw
  have e3 := Expr.eval_or e1 e2 (by split_ifs <;> omega) (by split_ifs <;> omega)
  have e4 := Expr.eval_eq_op e3 (Expr.eval_const (by omega : 1 < 2 ^ w)) hw
  unfold t3Eq t3Or
  rw [e4]
  by_cases hu : su = rCur <;> by_cases hv : sv = rCur <;> simp [hu, hv]

set_option maxHeartbeats 1000000 in
/-- One step of the edge scan. An embedded edge is skipped. An unembedded edge either waits
(an endpoint is in `Vhat`, and `nextHasUnemb` becomes `1`) or is embedded by procedure 3, whose
cost is paid by the drop of `t3MiddleCost · |unembedded|`. -/
theorem t3ScanStep_ptriple {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (hlay : lay = T3Layout.ofCtx ctx)
    {p : Program} {selfBase dsBase : ℕ}
    (hSpec : impl.pathDS.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure impl.pathDS.params w))
    (hdrain : p.procs[selfBase + 2]? = some (t3DrainQueueBody dsBase))
    (hmidP : p.procs[selfBase + 3]? = some (t3MiddleEdgeBody dsBase (selfBase + 2)))
    {rCur : ℕ} {emb0 : ℕ → Option Walk} {e : ℕ} (he : e < inp.J.m) :
    PTriple w p (T3ScanInv ctx lay rCur emb0 e) (t3ScanStep (selfBase + 3))
      (pNormalPost fun st₁ Φ₁ =>
        T3ScanInv ctx lay rCur emb0 (e + 1)
          { st₁ with regs := Function.update st₁.regs 14 (e + 1) } Φ₁ ∧ st₁.regs 14 = e)
      (fun _ => 120) := by
  intro st Φ ω ⟨d, Φr, hI⟩
  obtain ⟨mem, regs, pos⟩ := st
  have hR := hI.round
  have hr0 : regs 0 = lay.base := hI.r0
  have hr1 : regs 1 = rCur := hI.r1
  have hr8 : regs 8 = inp.J.m := hI.r8
  have hr9 : regs 9 = lay.embJWAddr := hI.r9
  have hr10 : regs 10 = ctx.memT1 (ctx.wInp.h + 16) := hI.r10
  have hr11 : regs 11 = ctx.wInp.prep.aComps := hI.r11
  have hr12 : regs 12 = lay.vhatOffsetAddr := hI.r12
  have hr13 : regs 13 = lay.vhatStampAddr := hI.r13
  have hr14 : regs 14 = e := hI.r14
  have hLoc : impl.pathDS.R.Local := hSpec.1
  have hb := T3Layout.bounds ctx; dsimp only at hb; rw [← hlay] at hb; unfold t3HdrSize at hb
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12⟩ := hb
  have hw1 : 1 < 2 ^ w := ctx.hwokW.1
  have hK_le := ctx.hK_le
  have hv1_le_v2 : ctx.v1 ≤ lay.base := by rw [hb1]; exact ctx.hv1_le
  have hslot_ev : (Expr.load (t3Add (.reg 9) (.reg 14))).eval w ⟨mem, regs, pos⟩ =
      some (mem (lay.embJWAddr + e)) :=
    Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq hI.r9) (Expr.eval_reg_of_eq hI.r14)
      (by omega))
  refine t3_ptriple_of_cps (t3_assign_cps hslot_ev ?_)
  rcases hE : d.emb e with _ | P
  · -- The edge `e` is not embedded yet.
    have hslot0 : mem (lay.embJWAddr + e) = 0 := by
      have h := hR.emb_mem e he; rw [hE] at h; exact h
    have hc_ev : (t3Eq (.reg 15) (.const 0)).eval w
        ⟨mem, Function.update regs 15 (mem (lay.embJWAddr + e)), pos⟩ = some 1 :=
      Expr.eval_eq_true (Expr.eval_reg_of_eq (by simp [hslot0])) (Expr.eval_const (by omega))
        rfl hw1
    refine t3_cond_cps hc_ev ?_
    simp only [one_ne_zero, ↓reduceIte]
    have hcov := hR.emb_j0_cov e he
    rcases hsrc : ctx.wd.jSources.getD e JEdgeSource.isLoop with _ | eW | ⟨ci, jL⟩
    · exact absurd (hcov (Or.inl hsrc)) (by simp [hE])
    · exact absurd (hcov (Or.inr ⟨eW, hsrc⟩)) (by simp [hE])
    obtain ⟨hci, hjL, hu_lt, hv_lt, _, _, _⟩ := t3_inComp_ne ctx he hsrc
    have hro := ctx.read_out_fields hR.staticMem.1
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hjs_at, haExt_lo, haExt_hi, hwW,
      hwS, hjS, hv1⟩ := hro
    have hjSrc_len : ctx.wd.jSources.length = inp.J.m := by
      have hs := mkW_jSources_spec ctx.hStat ctx.hw_okW ctx.hws (by rw [ctx.hWInpJ]; exact he)
      exact hs.1.trans (congrArg Graph.m ctx.hWInpJ)
    have hj_eq := List.getD_eq_getElem ctx.wd.jSources JEdgeSource.isLoop
      (by rw [hjSrc_len]; exact he)
    have hjAt := hjs_at e (by rw [hjSrc_len]; exact he)
    rw [← hj_eq, hsrc] at hjAt
    obtain ⟨_, hjci, hjjL⟩ := hjAt
    have hcp := ctx.read_comp_prep hR.staticMem.1 hci
    obtain ⟨_, hJptr, _, hJSub_at, hComps_bd, _, hJSub_bd⟩ := hcp
    have hprep_le : ctx.wInp.prep.hEnd ≤ ctx.wInp.h := ctx.hPrepEnd
    have hJlen : (ctx.wd.comps[ci]).J_sub.encode.length = 2 + 2 * (ctx.wd.comps[ci]).J_sub.m :=
      graph_encode_length _
    have hvoff : mem (lay.vhatOffsetAddr + ci) = vhatBaseW ctx.wd ci :=
      hR.staticMem.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ci hci
    have hvb1 := vhatBaseW_add_le hci
    have hvb2 := vhatBaseW_le_sum (wd := ctx.wd) (ci := ci + 1)
    set jSrc := ctx.memT1 (ctx.wInp.h + 16)
    set ptr := ctx.wInp.prep.cJSubPtr ci
    set uL := ((ctx.wd.comps[ci]).J_sub.edges.getD jL (0, 0)).1
    set vL := ((ctx.wd.comps[ci]).J_sub.edges.getD jL (0, 0)).2
    set su := mem (lay.vhatStampAddr + (vhatBaseW ctx.wd ci + uL))
    set sv := mem (lay.vhatStampAddr + (vhatBaseW ctx.wd ci + vL))
    have hsu_iff : su = rCur ↔ uL ∈ (d.states ci).Vhat := by
      rw [← hR.vhat_stmp_eq ci hci uL hu_lt, Nat.add_assoc]
    have hsv_iff : sv = rCur ↔ vL ∈ (d.states ci).Vhat := by
      rw [← hR.vhat_stmp_eq ci hci vL hv_lt, Nat.add_assoc]
    refine t3_ldMul_cps (rs := 10) (ri := 14) (b := jSrc) (i := e) (v := ci)
      (by simp [hr10]) (by simp [hr14]) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by rw [← Nat.add_assoc]; exact hjci) ?_
    refine t3_ldMul_cps (rs := 10) (ri := 14) (b := jSrc) (i := e) (v := jL)
      (by simp [hr10]) (by simp [hr14]) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by rw [← Nat.add_assoc]; exact hjjL) ?_
    refine t3_ldMul_cps (rs := 11) (ri := 16) (b := ctx.wInp.prep.aComps) (i := ci) (v := ptr)
      (by simp [hr11]) (by simp) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by rw [← Nat.add_assoc]; exact hJptr) ?_
    refine t3_ldAddMul_cps (rs := 18) (ri := 17) (b := ptr) (i := jL) (v := uL)
      (by simp) (by simp) (by omega) (by omega) (by omega) (by omega)
      (by omega) (graphAt_edge_fst_getD hJSub_at hjL) ?_
    refine t3_ldAddMul_cps (rs := 18) (ri := 17) (b := ptr) (i := jL) (v := vL)
      (by simp) (by simp) (by omega) (by omega) (by omega) (by omega)
      (by omega) (graphAt_edge_snd_getD hJSub_at hjL) ?_
    refine t3_ldRR_cps (ra := 12) (rb := 16) (a := lay.vhatOffsetAddr) (b := ci)
      (v := vhatBaseW ctx.wd ci) (by simp [hr12]) (by simp) (by omega) hvoff ?_
    refine t3_ldRRR_cps (ra := 13) (rb := 21) (rc := 19) (a := lay.vhatStampAddr)
      (b := vhatBaseW ctx.wd ci) (c := uL) (v := su) (by simp [hr13]) (by simp) (by simp)
      (by omega) (by omega) rfl ?_
    refine t3_ldRRR_cps (ra := 13) (rb := 21) (rc := 20) (a := lay.vhatStampAddr)
      (b := vhatBaseW ctx.wd ci) (c := vL) (v := sv) (by simp [hr13]) (by simp) (by simp)
      (by omega) (by omega) rfl ?_
    refine t3_cond_cps (t3_hit_eval (su := su) (sv := sv) (rCur := rCur) hw1 (by simp) (by simp)
      (by simp [hr1])) ?_
    by_cases hhit : su = rCur ∨ sv = rCur
    · -- An endpoint is in `Vhat`: the edge waits and `nextHasUnemb := 1`.
      simp only [hhit, one_ne_zero, ↓reduceIte]
      refine ⟨.normal, _, _, Φ, runs_store_iff.mpr ⟨_, _, Expr.eval_add
        (Expr.eval_reg_of_eq (v := lay.base) (by simp [hr0]))
          (Expr.eval_const (k := t3OffNextU) (by unfold t3OffNextU; omega))
          (by unfold t3OffNextU; omega), Expr.eval_const (by omega), rfl, rfl, rfl⟩, ⟨?_, ?_⟩, ?_⟩
      · refine ⟨{ d with nextHasUnemb := 1 }, Φr, ?_⟩
        exact
          { round := (hR.set_nextU hlay hLoc).of_mem_eq rfl
            phi := hI.phi
            r0 := by simp [hr0]
            r1 := by simp [hr1]
            r8 := by simp [hr8]
            r9 := by simp [hr9]
            r10 := by simp [hr10, jSrc]
            r11 := by simp [hr11]
            r12 := by simp [hr12]
            r13 := by simp [hr13]
            r14 := by simp
            mono := hI.mono
            skipped := fun eJ heJ hn => by
              rcases Nat.lt_succ_iff_lt_or_eq.mp heJ with h | rfl
              · exact hI.skipped eJ h hn
              · exact ⟨ci, hci, jL, hjL, hsrc, hhit.imp hsu_iff.mp hsv_iff.mp⟩
            nextU := ⟨fun _ => ⟨e, Nat.lt_succ_self e, hE⟩, fun _ => rfl⟩ }
      · simp [hr14]
      · simp only [Expr.size, t3Add, t3Eq, t3Or]
        rw [hI.phi]
        omega
    · -- No endpoint is in `Vhat`: procedure 3 embeds the edge.
      simp only [hhit, ↓reduceIte]
      have hu_nv : ∀ hci' : ci < ctx.wd.comps.length,
          ((ctx.wd.comps[ci]'hci').J_sub.edges.getD jL (0, 0)).1 ∉ (d.states ci).Vhat :=
        fun _ hu => hhit (Or.inl (hsu_iff.mpr hu))
      have hv_nv : ∀ hci' : ci < ctx.wd.comps.length,
          ((ctx.wd.comps[ci]'hci').J_sub.edges.getD jL (0, 0)).2 ∉ (d.states ci).Vhat :=
        fun _ hv => hhit (Or.inr (hsv_iff.mpr hv))
      have hmid := t3MiddleEdge_ptriple ctx lay hlay (selfBase := selfBase) (rCur := rCur) hSpec
        hdrain he hE hsrc hu_nv hv_nv
      obtain ⟨o₁, st₁, c₁, Φ₁, hr₁, hpost, hc₁⟩ :=
        hmid (startState [lay.base, rCur, e, ci, jL] mem pos) Φr ω
          ⟨hR.of_mem_eq rfl, by simp [startState], by simp [startState], by simp [startState],
            by simp [startState], by simp [startState]⟩
      obtain ⟨ho₁, d', hR', _, _, hVsub, hsame, hsome, hnU⟩ := hpost
      have hcard := t3_unemb_card_embed he hE hsome hsame
      have hc₁' : c₁ + Φ₁ ≤ t3MiddleCost impl inp.J + Φr := hc₁
      have hmul : t3MiddleCost impl inp.J * (unembeddedSet2Pure inp.J d.emb).card =
          t3MiddleCost impl inp.J * (unembeddedSet2Pure inp.J d'.emb).card +
            t3MiddleCost impl inp.J := by
        rw [hcard, Nat.mul_succ]
      refine ⟨.normal, _, _, Φ₁ + t3MiddleCost impl inp.J * (unembeddedSet2Pure inp.J d'.emb).card,
        runs_call_iff.mpr ⟨[lay.base, rCur, e, ci, jL], _, o₁, st₁, c₁,
          by simp [evalArgs, Expr.eval_reg, hr0, hr1, hr14], hmidP, hr₁, rfl, rfl, rfl⟩, ⟨?_, ?_⟩, ?_⟩
      · refine ⟨d', Φ₁, ?_⟩
        exact
          { round := hR'.of_mem_eq rfl
            phi := rfl
            r0 := by simp [hr0]
            r1 := by simp [hr1]
            r8 := by simp [hr8]
            r9 := by simp [hr9]
            r10 := by simp [hr10, jSrc]
            r11 := by simp [hr11]
            r12 := by simp [hr12]
            r13 := by simp [hr13]
            r14 := by simp
            mono := fun eJ heJ => by
              by_cases hx : eJ = e
              · subst hx
                rcases hI.mono eJ heJ with h | h
                · exact Or.inl h
                · exact Or.inl (h ▸ hE)
              · rw [hsame eJ heJ hx]; exact hI.mono eJ heJ
            skipped := fun eJ heJ hn => by
              rcases Nat.lt_succ_iff_lt_or_eq.mp heJ with h | rfl
              · have hx : eJ ≠ e := by omega
                rw [hsame eJ (by omega) hx] at hn
                exact (hI.skipped eJ h hn).mono hVsub
              · simp [hn] at hsome
            nextU := by
              rw [hnU, hI.nextU]
              constructor
              · rintro ⟨eJ, h, hn⟩
                exact ⟨eJ, Nat.lt_succ_of_lt h, by rw [hsame eJ (by omega) (by omega)]; exact hn⟩
              · rintro ⟨eJ, h, hn⟩
                rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | rfl
                · exact ⟨eJ, h', by rw [← hsame eJ (by omega) (by omega)]; exact hn⟩
                · simp [hn] at hsome }
      · simp [hr14]
      · simp only [Expr.size, t3Add, t3Eq, t3Or, argsSize]
        rw [hI.phi]
        omega
  · -- The edge `e` is already embedded: skip it.
    have hslot_pos : 0 < mem (lay.embJWAddr + e) := by
      have h := hR.emb_mem e he; rw [hE] at h; have h1 : lay.staticEnd ≤ mem (lay.embJWAddr + e) := h.1
      omega
    have hc_ev : (t3Eq (.reg 15) (.const 0)).eval w
        ⟨mem, Function.update regs 15 (mem (lay.embJWAddr + e)), pos⟩ = some 0 :=
      Expr.eval_eq_false (Expr.eval_reg_of_eq (v := mem (lay.embJWAddr + e)) (by simp))
        (Expr.eval_const (by omega))
        (by omega) hw1
    refine t3_cond_cps hc_ev ?_
    simp only [↓reduceIte]
    refine ⟨.normal, _, 1, Φ, runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, ⟨⟨d, Φr, ?_⟩, by simp [hr14]⟩, ?_⟩
    · exact
        { round := hR.of_mem_eq rfl
          phi := hI.phi
          r0 := by simp [hr0]
          r1 := by simp [hr1]
          r8 := by simp [hr8]
          r9 := by simp [hr9]
          r10 := by simp [hr10]
          r11 := by simp [hr11]
          r12 := by simp [hr12]
          r13 := by simp [hr13]
          r14 := by simp
          mono := hI.mono
          skipped := fun eJ heJ hn => by
            rcases Nat.lt_succ_iff_lt_or_eq.mp heJ with h | rfl
            · exact hI.skipped eJ h hn
            · simp [hE] at hn
          nextU := by
            rw [hI.nextU]
            constructor
            · rintro ⟨eJ, h, hn⟩; exact ⟨eJ, Nat.lt_succ_of_lt h, hn⟩
            · rintro ⟨eJ, h, hn⟩
              rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | rfl
              · exact ⟨eJ, h', hn⟩
              · simp [hE] at hn }
    · simp only [Expr.size, t3Add, t3Eq]
      omega

/-- The edge scan of `t3RoundBody`. It starts with `nextHasUnemb = 0` and the round emb `emb0`,
and ends with every unembedded edge skipped for a reason (`T3Skipped`) and `nextHasUnemb = 1`
exactly when some edge is still unembedded. -/
theorem t3ScanLoop_ptriple {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (hlay : lay = T3Layout.ofCtx ctx)
    {p : Program} {selfBase dsBase : ℕ}
    (hSpec : impl.pathDS.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure impl.pathDS.params w))
    (hdrain : p.procs[selfBase + 2]? = some (t3DrainQueueBody dsBase))
    (hmidP : p.procs[selfBase + 3]? = some (t3MiddleEdgeBody dsBase (selfBase + 2)))
    (rCur : ℕ) (emb0 : ℕ → Option Walk) :
    PTriple w p
      (fun st Φ => ∃ d Φr, T3RoundAt ctx lay rCur d st Φr ∧
        Φ = Φr + t3MiddleCost impl inp.J * (unembeddedSet2Pure inp.J d.emb).card ∧
        d.emb = emb0 ∧ d.nextHasUnemb = 0 ∧
        st.regs 0 = lay.base ∧ st.regs 1 = rCur ∧ st.regs 8 = inp.J.m ∧
        st.regs 9 = lay.embJWAddr ∧ st.regs 10 = ctx.memT1 (ctx.wInp.h + 16) ∧
        st.regs 11 = ctx.wInp.prep.aComps ∧ st.regs 12 = lay.vhatOffsetAddr ∧
        st.regs 13 = lay.vhatStampAddr)
      (t3ForRange 14 (.const 0) (.reg 8) (t3ScanStep (selfBase + 3)))
      (pNormalPost (T3ScanInv ctx lay rCur emb0 inp.J.m))
      (fun _ => 129 * inp.J.m + 7) := by
  have hb := T3Layout.bounds ctx; dsimp only at hb; rw [← hlay] at hb; unfold t3HdrSize at hb
  have hm_w : inp.J.m < 2 ^ w := by omega
  have hfor := PTriple.forRange_const (w := w) (p := p)
    (P := fun st Φ => ∃ d Φr, T3RoundAt ctx lay rCur d st Φr ∧
        Φ = Φr + t3MiddleCost impl inp.J * (unembeddedSet2Pure inp.J d.emb).card ∧
        d.emb = emb0 ∧ d.nextHasUnemb = 0 ∧
        st.regs 0 = lay.base ∧ st.regs 1 = rCur ∧ st.regs 8 = inp.J.m ∧
        st.regs 9 = lay.embJWAddr ∧ st.regs 10 = ctx.memT1 (ctx.wInp.h + 16) ∧
        st.regs 11 = ctx.wInp.prep.aComps ∧ st.regs 12 = lay.vhatOffsetAddr ∧
        st.regs 13 = lay.vhatStampAddr)
    (r := 14) (lo := .const 0) (hi := .reg 8) (body := t3ScanStep (selfBase + 3))
    (Inv := T3ScanInv ctx lay rCur emb0) 120 0 inp.J.m (Nat.zero_le _) ctx.hwokW.1 (fun _ => hm_w)
    (fun st Φ ⟨d, Φr, hR, hΦ, hemb, hnU, h0, h1, h8, h9, h10, h11, h12, h13⟩ => by
      refine ⟨Expr.eval_const (by omega), d, Φr, ?_⟩
      exact
        { round := hR.of_mem_eq rfl
          phi := hΦ
          r0 := by simpa using h0
          r1 := by simpa using h1
          r8 := by simpa using h8
          r9 := by simpa using h9
          r10 := by simpa using h10
          r11 := by simpa using h11
          r12 := by simpa using h12
          r13 := by simpa using h13
          r14 := by simp
          mono := fun eJ _ => Or.inr (by rw [hemb])
          skipped := fun _ h => absurd h (Nat.not_lt_zero _)
          nextU := by
            rw [hnU]
            exact ⟨fun h => absurd h (by decide), fun ⟨_, h, _⟩ => absurd h (Nat.not_lt_zero _)⟩ })
    (fun _ _ _ _ _ hI => by obtain ⟨_, _, hI⟩ := hI; exact hI.r14)
    (fun _ _ _ _ _ hI => by obtain ⟨_, _, hI⟩ := hI; exact Expr.eval_reg_of_eq hI.r8)
    (fun i _ hi => t3ScanStep_ptriple ctx lay hlay hSpec hdrain hmidP hi)
  refine PTriple.conseq hfor (fun _ _ h => h) (fun _ _ _ h => h) fun _ _ _ => ?_
  simp only [Expr.size, Nat.sub_zero]
  omega

end MinCostFlow.Spanner
