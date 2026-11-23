module

public import MinCostFlow.Spanner.ProgTask3RoundProof

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM Cited

/-!
# Procedure 4 of Task 3: One Round

This file puts the pieces of a round together. The round reads the round counter `η` and works
with `η + 1`. It resets `nextHasUnemb`, loads the constants it needs, runs the init loop
(`t3InitLoop_ptriple`), loads the scan registers, runs the edge scan (`t3ScanLoop_ptriple`),
and commits `η + 1` and `cont` to the header (`t3_outer_of_scan`).

The potential before the round is the outer potential plus `t3MiddleCost` per unembedded edge.
The init loop needs `25` more units per vertex of the component expanders, for the `Vhat` term of
the round potential. These units are paid from the round cost. The main result is
`t3Round_ptriple`.
-/

/-- Cost of one round of Task 3, without the calls of procedure 3, which the potential pays. -/
noncomputable def t3RoundCost (impl : SpannerToolImpl) (J : Graph) : ℕ :=
  Task1Input.mwCap impl J * ⌈impl.pathDS.params.K_init *
    (impl.pathDS.params.gExp (WitnessCoreInput.dWInt impl.constructExpander)
      (Task1Input.mwCap impl J) : ℝ)⌉₊ + 228 * J.m + 300

/-- `t3RoundBody` written with the two loop bodies `t3InitStep` and `t3ScanStep`. -/
lemma t3RoundBody_eq (dsBase middleBase : ℕ) : t3RoundBody dsBase middleBase =
    Stmt.seq (.assign 1 (t3Add (t3Ld (.reg 0) (.const t3OffEta2)) (.const 1)))
    (Stmt.seq (t3St (.reg 0) (.const t3OffNextU) (.const 0))
    (Stmt.seq (.assign 2 (t3Ld (.reg 0) (.const t3OffK)))
    (Stmt.seq (.assign 3 (t3Ld (.reg 0) (.const t3OffACompExt)))
    (Stmt.seq (.assign 4 (t3Ld (.reg 0) (.const t3OffDsHdl)))
    (Stmt.seq (.assign 5 (t3Ld (.reg 0) (.const t3OffPhiNumC)))
    (Stmt.seq (.assign 6 (t3Ld (.reg 0) (.const t3OffPhiDenC)))
    (Stmt.seq (.assign 7 (t3Ld (.reg 0) (.const t3OffMw)))
    (Stmt.seq (t3ForRange 8 (.const 0) (.reg 2) (t3InitStep dsBase))
    (Stmt.seq (.assign 8 (t3Ld (.reg 0) (.const t3OffJm)))
    (Stmt.seq (.assign 9 (t3Ld (.reg 0) (.const t3OffEmbJW)))
    (Stmt.seq (.assign 10 (t3Ld (.reg 0) (.const t3OffJSrc)))
    (Stmt.seq (.assign 11 (t3Ld (.reg 0) (.const t3OffAComps)))
    (Stmt.seq (.assign 12 (t3Ld (.reg 0) (.const t3OffVOff)))
    (Stmt.seq (.assign 13 (t3Ld (.reg 0) (.const t3OffVStmp)))
    (Stmt.seq (t3ForRange 14 (.const 0) (.reg 8) (t3ScanStep middleBase))
    (Stmt.seq (t3St (.reg 0) (.const t3OffEta2) (.reg 1))
    (Stmt.seq (t3St (.reg 0) (.const t3OffCont) (t3Ld (.reg 0) (.const t3OffNextU)))
      (.ret (.reg 1))))))))))))))))))) := rfl

/-- Run a loop whose triple fixes its potential `Φa`, while a part `F` of the potential stays
outside the loop. -/
lemma t3_frame_cps {w : ℕ} {p : Program} {ω : ℕ → Bool} {s₁ s₂ : Stmt} {st : State}
    {b₁ Φa F k T T₀ : ℕ} {P : State → ℕ → Prop} {Inv : State → ℕ → Prop} {cost : State → ℕ}
    {Q : Outcome → State → ℕ → Prop}
    (ht : PTriple w p P s₁ (pNormalPost Inv) cost) (hp : P st Φa) (hc : cost st ≤ b₁)
    (hT : T + (Φa + F) ≤ T₀)
    (hrest : ∀ st₁ Φ₁, Inv st₁ Φ₁ → ∃ o stF c₂ Φ',
      Runs w p ω s₂ st₁ o stF c₂ ∧ Q o stF Φ' ∧ (k + b₁ + 1) + c₂ + Φ' ≤ T + (Φ₁ + F)) :
    ∃ o stF c_tot Φ', Runs w p ω (.seq s₁ s₂) st o stF c_tot ∧ Q o stF Φ' ∧
      k + c_tot + Φ' ≤ T₀ := by
  obtain ⟨o, stF, c, Φ', h1, h2, h3⟩ := t3_normal_ptriple_cps (T := T + F) (k := k) ht hp hc
    (fun st₁ Φ₁ hI => by
      obtain ⟨o, stF, c₂, Φ', a, b, hc⟩ := hrest st₁ Φ₁ hI
      exact ⟨o, stF, c₂, Φ', a, b, by omega⟩)
  exact ⟨o, stF, c, Φ', h1, h2, by omega⟩

/-- The registers that the caller of a round keeps: `jAddr`, `t1OutAddr` and `v2`. -/
def t3OuterRegs (inp : Task3Input) : ℕ → ℕ := fun i => [inp.jAddr, inp.t1OutAddr, inp.v2].getD i 0

/-- Post of one round: it returns `η + 1`, and the memory satisfies the outer invariant for
`η + 1` with a new emb that extends the old one. The potential is the outer potential plus
`t3MiddleCost` per unembedded edge. -/
def T3RoundPost {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (η : ℕ) (emb0 : ℕ → Option Walk)
    (o : Outcome) (st : State) (Φ : ℕ) : Prop :=
  o = .returned (η + 1) ∧ ∃ d1 : T3OuterData,
    T3OuterAt ctx lay (η + 1) d1 ⟨st.mem, t3OuterRegs inp, 0⟩
      (t3KdelCost impl inp.J * t3EcongPhi ctx lay st.mem) ∧
    Φ = t3KdelCost impl inp.J * t3EcongPhi ctx lay st.mem +
      t3MiddleCost impl inp.J * (unembeddedSet2Pure inp.J d1.emb).card ∧
    (∀ eJ < inp.J.m, emb0 eJ = none ∨ d1.emb eJ = emb0 eJ)

/-- The commit of a round, as a continuation: two stores and the return. -/
lemma t3Round_commit_cps {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (hlay : lay = T3Layout.ofCtx ctx)
    {p : Program} {ω : ℕ → Bool}
    {η : ℕ} {d0 : T3OuterData} {stO : State} {ΦO : ℕ} (hO : T3OuterAt ctx lay η d0 stO ΦO)
    {d : T3RoundData impl.pathDS} {Φr : ℕ} {mem2 regs2 : ℕ → ℕ} {pos2 Φ₂ k T : ℕ}
    (hSc : T3ScanAt ctx lay (η + 1) d0.emb inp.J.m d Φr ⟨mem2, regs2, pos2⟩ Φ₂)
    (hk : k + 20 + Φ₂ ≤ T) :
    ∃ o stF c Φ', Runs w p ω
      (Stmt.seq (t3St (.reg 0) (.const t3OffEta2) (.reg 1))
        (Stmt.seq (t3St (.reg 0) (.const t3OffCont) (t3Ld (.reg 0) (.const t3OffNextU)))
          (.ret (.reg 1)))) ⟨mem2, regs2, pos2⟩ o stF c ∧
      T3RoundPost ctx lay η d0.emb o stF Φ' ∧ k + c + Φ' ≤ T := by
  have hb := T3Layout.bounds ctx; dsimp only at hb; rw [← hlay] at hb; unfold t3HdrSize at hb
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12⟩ := hb
  have hoff : ∀ i < 32, i < 2 ^ w ∧ lay.base + i < 2 ^ w := fun i hi => by omega
  have h2r0 : regs2 0 = lay.base := hSc.r0
  have h2r1 : regs2 1 = η + 1 := hSc.r1
  have hR2 := hSc.round
  have hNU : mem2 (lay.base + t3OffNextU) = d.nextHasUnemb := hR2.nextU_eq
  have hEtaNe : lay.base + t3OffNextU ≠ lay.base + t3OffEta2 := by
    unfold t3OffNextU t3OffEta2; omega
  have hfar : ∀ x, lay.embJWAddr ≤ x →
      Function.update (Function.update mem2 (lay.base + t3OffEta2) (η + 1))
        (lay.base + t3OffCont) d.nextHasUnemb x = mem2 x := fun x hx => by
    rw [Function.update_of_ne (by unfold t3OffCont; omega),
      Function.update_of_ne (by unfold t3OffEta2; omega)]
  have hEF : t3EcongPhi ctx lay (Function.update (Function.update mem2 (lay.base + t3OffEta2)
      (η + 1)) (lay.base + t3OffCont) d.nextHasUnemb) = t3EcongPhi ctx lay mem2 :=
    t3EcongPhi_frame ctx lay (fun eW _ => hfar _ (by omega)) (fun eW _ => hfar _ (by omega))
  have hOut := t3_outer_of_scan ctx lay hlay hSc (t3_round_geom ctx lay hO hSc)
    (st' := ⟨Function.update (Function.update mem2 (lay.base + t3OffEta2) (η + 1))
      (lay.base + t3OffCont) d.nextHasUnemb, t3OuterRegs inp, 0⟩) rfl rfl rfl rfl
  have hΦ2 : Φ₂ = t3RoundPhi ctx lay d mem2 +
      t3MiddleCost impl inp.J * (unembeddedSet2Pure inp.J d.emb).card := by
    rw [hSc.phi, hR2.phi_eq]
  have hle : t3KdelCost impl inp.J * t3EcongPhi ctx lay mem2 ≤ t3RoundPhi ctx lay d mem2 := by
    unfold t3RoundPhi; omega
  refine t3_st_cps (base := lay.base) (val := η + 1) h2r0 (hoff t3OffEta2 (by decide)).1
    (hoff t3OffEta2 (by decide)).2 h2r1 ?_
  refine t3_store_cps (addr := lay.base + t3OffCont) (v := d.nextHasUnemb)
    (Expr.eval_add (Expr.eval_reg_of_eq h2r0) (Expr.eval_const (hoff t3OffCont (by decide)).1)
      (hoff t3OffCont (by decide)).2)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq h2r0)
      (Expr.eval_const (k := t3OffNextU) (hoff t3OffNextU (by decide)).1)
      (hoff t3OffNextU (by decide)).2)
      (by dsimp only; rw [Function.update_of_ne hEtaNe]; exact hNU)) ?_
  refine t3_end_ret_cps (v := η + 1) (Φ' := t3KdelCost impl inp.J * t3EcongPhi ctx lay
      (Function.update (Function.update mem2 (lay.base + t3OffEta2) (η + 1))
        (lay.base + t3OffCont) d.nextHasUnemb) +
      t3MiddleCost impl inp.J * (unembeddedSet2Pure inp.J d.emb).card)
    (Expr.eval_reg_of_eq h2r1) ⟨rfl, d.toOuter, hOut, rfl, hSc.mono⟩ ?_
  rw [hEF]
  rw [hΦ2] at hk
  simp only [Expr.size, t3Ld, t3Add]
  omega

set_option maxHeartbeats 1000000 in
/-- The second half of a round, as a continuation: the loads of the scan registers, the edge
scan and the commit. It starts from the round invariant after the init loop. -/
lemma t3Round_scan_cps {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (hlay : lay = T3Layout.ofCtx ctx)
    {p : Program} {ω : ℕ → Bool} {selfBase dsBase : ℕ}
    (hSpec : impl.pathDS.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure impl.pathDS.params w))
    (hdrain : p.procs[selfBase + 2]? = some (t3DrainQueueBody dsBase))
    (hmidP : p.procs[selfBase + 3]? = some (t3MiddleEdgeBody dsBase (selfBase + 2)))
    {η : ℕ} {d0 : T3OuterData} {stO : State} {ΦO : ℕ} (hO : T3OuterAt ctx lay η d0 stO ΦO)
    {d1 : T3RoundData impl.pathDS} {mem1 regs1 : ℕ → ℕ} {pos1 Φ₁ k T : ℕ}
    (hR : T3RoundAt ctx lay (η + 1) d1 ⟨mem1, regs1, pos1⟩ Φ₁)
    (hemb : d1.emb = d0.emb) (hnu : d1.nextHasUnemb = 0)
    (h1r0 : regs1 0 = lay.base) (h1r1 : regs1 1 = η + 1)
    (hk : k + 129 * inp.J.m + 80 + Φ₁ +
      t3MiddleCost impl inp.J * (unembeddedSet2Pure inp.J d0.emb).card ≤ T) :
    ∃ o stF c Φ', Runs w p ω
      (Stmt.seq (.assign 8 (t3Ld (.reg 0) (.const t3OffJm)))
      (Stmt.seq (.assign 9 (t3Ld (.reg 0) (.const t3OffEmbJW)))
      (Stmt.seq (.assign 10 (t3Ld (.reg 0) (.const t3OffJSrc)))
      (Stmt.seq (.assign 11 (t3Ld (.reg 0) (.const t3OffAComps)))
      (Stmt.seq (.assign 12 (t3Ld (.reg 0) (.const t3OffVOff)))
      (Stmt.seq (.assign 13 (t3Ld (.reg 0) (.const t3OffVStmp)))
      (Stmt.seq (t3ForRange 14 (.const 0) (.reg 8) (t3ScanStep (selfBase + 3)))
      (Stmt.seq (t3St (.reg 0) (.const t3OffEta2) (.reg 1))
      (Stmt.seq (t3St (.reg 0) (.const t3OffCont) (t3Ld (.reg 0) (.const t3OffNextU)))
        (.ret (.reg 1)))))))))))
      ⟨mem1, regs1, pos1⟩ o stF c ∧
      T3RoundPost ctx lay η d0.emb o stF Φ' ∧ k + c + Φ' ≤ T := by
  have hb := T3Layout.bounds ctx; dsimp only at hb; rw [← hlay] at hb; unfold t3HdrSize at hb
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12⟩ := hb
  have hoff : ∀ i < 32, i < 2 ^ w ∧ lay.base + i < 2 ^ w := fun i hi => by omega
  obtain ⟨_, hEJ, _, _, hJm, _, _, _, _, hAC, _, _, _, _, hJS, _, _, _, _, _, _, _, _, _, hVO,
    hVS, _⟩ := hR.staticMem
  set F := t3MiddleCost impl inp.J * (unembeddedSet2Pure inp.J d0.emb).card with hF
  refine t3_ld_cps (base := lay.base) (v := inp.J.m) h1r0
    (hoff t3OffJm (by decide)).1 (hoff t3OffJm (by decide)).2 hJm ?_
  refine t3_ld_cps (base := lay.base) (v := lay.embJWAddr) (by simp [h1r0])
    (hoff t3OffEmbJW (by decide)).1 (hoff t3OffEmbJW (by decide)).2 hEJ ?_
  refine t3_ld_cps (base := lay.base) (v := ctx.memT1 (ctx.wInp.h + 16)) (by simp [h1r0])
    (hoff t3OffJSrc (by decide)).1 (hoff t3OffJSrc (by decide)).2 hJS ?_
  refine t3_ld_cps (base := lay.base) (v := ctx.wInp.prep.aComps) (by simp [h1r0])
    (hoff t3OffAComps (by decide)).1 (hoff t3OffAComps (by decide)).2 hAC ?_
  refine t3_ld_cps (base := lay.base) (v := lay.vhatOffsetAddr) (by simp [h1r0])
    (hoff t3OffVOff (by decide)).1 (hoff t3OffVOff (by decide)).2 hVO ?_
  refine t3_ld_cps (base := lay.base) (v := lay.vhatStampAddr) (by simp [h1r0])
    (hoff t3OffVStmp (by decide)).1 (hoff t3OffVStmp (by decide)).2 hVS ?_
  refine t3_frame_cps (T := T - (Φ₁ + F)) (Φa := Φ₁ + F) (F := 0) (b₁ := 129 * inp.J.m + 7)
    (t3ScanLoop_ptriple ctx lay hlay hSpec hdrain hmidP (η + 1) d0.emb)
    ?_ (le_refl _) ?_ ?_
  · exact ⟨d1, Φ₁, hR.of_mem_eq rfl, by rw [hemb], hemb, hnu, by simp [h1r0], by simp [h1r1],
      by simp, by simp, by simp, by simp, by simp, by simp⟩
  · omega
  · intro st₂ Φ₂ ⟨d, Φr, hSc⟩
    obtain ⟨mem2, regs2, pos2⟩ := st₂
    refine t3Round_commit_cps ctx lay hlay hO hSc ?_
    simp only [Expr.size, t3Ld, t3Add] at hk ⊢
    omega

set_option maxHeartbeats 1000000 in
/-- One round of Task 3 (procedure 4, `t3RoundBody`). It starts from the outer invariant for `η`
with some edge still unembedded, and ends with the outer invariant for `η + 1`. -/
theorem t3Round_ptriple {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (hlay : lay = T3Layout.ofCtx ctx)
    {p : Program} {selfBase dsBase : ℕ}
    (hSpec : impl.pathDS.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure impl.pathDS.params w))
    (hdrain : p.procs[selfBase + 2]? = some (t3DrainQueueBody dsBase))
    (hmidP : p.procs[selfBase + 3]? = some (t3MiddleEdgeBody dsBase (selfBase + 2)))
    (η : ℕ) (d0 : T3OuterData) :
    PTriple w p
      (fun st Φ => ∃ stO ΦO, T3OuterAt ctx lay η d0 stO ΦO ∧ st.mem = stO.mem ∧
        st.regs 0 = lay.base ∧ (unembeddedSet2Pure inp.J d0.emb).Nonempty ∧
        Φ = ΦO + t3MiddleCost impl inp.J * (unembeddedSet2Pure inp.J d0.emb).card)
      (t3RoundBody dsBase (selfBase + 3))
      (T3RoundPost ctx lay η d0.emb)
      (fun _ => t3RoundCost impl inp.J) := by
  intro st Φ ω ⟨stO, ΦO, hO, hmem, hr0, hne, hΦ⟩
  obtain ⟨mem, regs, pos⟩ := st
  simp only at hmem hr0
  subst hmem
  have hb := T3Layout.bounds ctx; dsimp only at hb; rw [← hlay] at hb; unfold t3HdrSize at hb
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12⟩ := hb
  have hw1 : 1 < 2 ^ w := ctx.hwokW.1
  have hwb : Task3Input.maxWordBound impl inp < 2 ^ w := ctx.hwokW.2.2
  have hmax_lt_w : Task3Input.maxHeapEnd impl inp + 3 ≤ Task3Input.maxWordBound impl inp :=
    le_max_left _ _
  have hEta : η + 1 ≤ eta2Bound inp.J :=
    le_of_lt (t3Round_bound_of_unembedded hne hO.geom)
  have hEta_w : η + 1 < 2 ^ w :=
    lt_of_le_of_lt (le_trans hEta (eta2Bound_le_maxHeapEnd impl inp)) (by omega)
  have hoff : ∀ i < 32, i < 2 ^ w ∧ lay.base + i < 2 ^ w := fun i hi => by omega
  have hlo := hO.hCur_lo
  have hsumN := ctx.hvhatSum_le
  set γW := impl.pathDS.params.gExp (WitnessCoreInput.dWInt impl.constructExpander)
    (Task1Input.mwCap impl inp.J) with hγW
  -- The heap cursor leaves room for one `PathDS` per edge.
  have hc0_max : d0.hCur + inp.J.m * Task3Input.dsOneW impl inp.J ≤
      Task3Input.maxHeapEnd impl inp := by
    rw [show Task3Input.maxHeapEnd impl inp = Task3Input.staticEndCap impl inp + 5 * inp.J.m +
      (eta2Bound inp.J * inp.J.m + inp.J.m + inp.J.m * γW) * Task3Input.dsOneW impl inp.J +
      inp.J.m * (2 * γW + 3) from rfl]
    have hg : d0.getPathCnt ≤ inp.J.m := le_trans hO.getPath_cnt_le (Nat.sub_le _ _)
    have hr_bd : η * inp.J.m + inp.J.m ≤ eta2Bound inp.J * inp.J.m := by
      have := Nat.mul_le_mul_right inp.J.m hEta; rw [Nat.add_mul, Nat.one_mul] at this; exact this
    have hdel_bd := le_trans hO.del_le_econgUpd
      (le_trans hO.econgUpd_W (Nat.mul_le_mul_right γW hg))
    have hm1 := Nat.mul_le_mul_right (Task3Input.dsOneW impl inp.J)
      (show η * inp.J.m + d0.getPathCnt + d0.delCnt + inp.J.m ≤
        eta2Bound inp.J * inp.J.m + inp.J.m + inp.J.m * γW by omega)
    have hm2 := Nat.mul_le_mul_right (2 * γW + 3) hg
    have hds_add : (η * inp.J.m + d0.getPathCnt + d0.delCnt) * Task3Input.dsOneW impl inp.J +
        inp.J.m * Task3Input.dsOneW impl inp.J =
        (η * inp.J.m + d0.getPathCnt + d0.delCnt + inp.J.m) * Task3Input.dsOneW impl inp.J := by
      ring
    have hh0 : d0.hCur ≤ Task3Input.staticEndCap impl inp + 5 * inp.J.m +
        (η * inp.J.m + d0.getPathCnt + d0.delCnt) * Task3Input.dsOneW impl inp.J +
        d0.getPathCnt * (2 * γW + 3) := hO.hCur_bd
    omega
  have hc0_w : d0.hCur + inp.J.m * Task3Input.dsOneW impl inp.J < 2 ^ w := by omega
  -- The memory after `nextHasUnemb := 0`.
  set memS := Function.update stO.mem (lay.base + t3OffNextU) 0 with hmemS
  have hSne : ∀ x, x ≠ lay.base + t3OffNextU → memS x = stO.mem x := fun x hx =>
    Function.update_of_ne hx _ _
  have hS : T3StaticMem ctx lay memS :=
    hO.staticMem.mono (fun x hx => hSne x (by unfold t3OffNextU; omega))
      (fun i _ _ _ _ _ _ hN _ => hSne _ (by omega)) (fun ci _ => hSne _ (by unfold t3OffNextU; omega))
  obtain ⟨_, _, _, _, _, _, hK, _, _, _, hACE, _, _, _, _, _, _, hMw, hPN, hPD, hDH, _, _, _, _,
    _, _⟩ := id hS
  have hHC : memS (lay.base + t3OffHCur) = d0.hCur := by
    rw [hSne _ (by unfold t3OffHCur t3OffNextU; omega)]; exact hO.hCur_eq
  have hZ : ZeroFrom memS d0.hCur := fun x hx => by
    rw [hSne x (by unfold t3OffNextU; omega)]; exact hO.zero_from x hx
  have hEtaM : stO.mem (lay.base + t3OffEta2) = η := hO.eta2_eq
  set F := t3MiddleCost impl inp.J * (unembeddedSet2Pure inp.J d0.emb).card with hF
  set E0 := t3EcongPhi ctx lay stO.mem with hE0
  set sumN := (ctx.wd.comps.map fun c => c.W_sub.n).sum with hsumN_def
  set Kd := t3KdelCost impl inp.J with hKd
  have hΦO : ΦO = Kd * E0 := hO.phi_eq
  set bInit := Task1Input.mwCap impl inp.J * ⌈impl.pathDS.params.K_init * (γW : ℝ)⌉₊ +
    49 * inp.J.m + 7 with hbInit
  set Tm := t3RoundCost impl inp.J - 25 * sumN with hTm
  have hcost : t3RoundCost impl inp.J = bInit + 179 * inp.J.m + 293 := by
    simp only [t3RoundCost, hbInit, hγW]; ring
  rw [t3RoundBody_eq]
  apply t3_ptriple_of_cps
  -- `r1 := η + 1`.
  refine t3_assign_cps (v := η + 1) (Expr.eval_add (Expr.eval_load_of_eq
    (Expr.eval_add (Expr.eval_reg_of_eq hr0) (Expr.eval_const (k := t3OffEta2) (hoff t3OffEta2 (by decide)).1)
      (hoff t3OffEta2 (by decide)).2) hEtaM) (Expr.eval_const (k := 1) hw1) hEta_w) ?_
  -- `nextHasUnemb := 0`.
  refine t3_st_const_cps (base := lay.base) (by simp [hr0]) (hoff t3OffNextU (by decide)).1
    (hoff t3OffNextU (by decide)).2 (Nat.two_pow_pos w) ?_
  -- Loads of `K`, `aCompExt`, the handle array, `phiNum`, `phiDen` and `M_W`.
  refine t3_ld_cps (base := lay.base) (v := ctx.wd.comps.length) (by simp [hr0])
    (hoff t3OffK (by decide)).1 (hoff t3OffK (by decide)).2 hK ?_
  refine t3_ld_cps (base := lay.base) (v := ctx.memT1 (ctx.wInp.h + 12)) (by simp [hr0])
    (hoff t3OffACompExt (by decide)).1 (hoff t3OffACompExt (by decide)).2 hACE ?_
  refine t3_ld_cps (base := lay.base) (v := lay.dsHandlesAddr) (by simp [hr0])
    (hoff t3OffDsHdl (by decide)).1 (hoff t3OffDsHdl (by decide)).2 hDH ?_
  refine t3_ld_cps (base := lay.base) (v := impl.constructExpander.phiNum) (by simp [hr0])
    (hoff t3OffPhiNumC (by decide)).1 (hoff t3OffPhiNumC (by decide)).2 hPN ?_
  refine t3_ld_cps (base := lay.base) (v := impl.constructExpander.phiDen) (by simp [hr0])
    (hoff t3OffPhiDenC (by decide)).1 (hoff t3OffPhiDenC (by decide)).2 hPD ?_
  refine t3_ld_cps (base := lay.base) (v := ctx.wd.M_W) (by simp [hr0])
    (hoff t3OffMw (by decide)).1 (hoff t3OffMw (by decide)).2 hMw ?_
  -- The init loop, with the potential `F` kept outside.
  refine t3_frame_cps (Φa := Kd * E0 + 25 * sumN) (F := F) (T := Tm) (b₁ := bInit)
    (t3InitLoop_ptriple ctx lay hlay hSpec (rCur := η + 1) (Φ0 := Kd * E0 + 25 * sumN)
      hS hlo hc0_w hHC hZ)
    ⟨rfl, rfl, by simp [hr0], by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩
    (le_refl _) (by beta_reduce; rw [hΦ, hΦO]; omega) ?_
  intro st₁ Φ₁ ⟨hCur, states, reps, hI⟩
  have hR := t3_roundAt_of_init ctx lay hlay hO hEta hI rfl
  obtain ⟨mem1, regs1, pos1⟩ := st₁
  refine t3Round_scan_cps ctx lay hlay hSpec hdrain hmidP hO hR rfl rfl hI.r0 hI.r1 ?_
  simp only [Expr.size, t3Ld, t3Add]
  omega

end MinCostFlow.Spanner
