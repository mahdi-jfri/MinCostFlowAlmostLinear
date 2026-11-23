module

public import MinCostFlow.Spanner.ProgTask3Final
public import MinCostFlow.Spanner.ProgTask3StartProof

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM Cited

/-!
# Task 3 Meets Its Contract

`task3Body` runs the setup (`t3Setup_cps`, which ends with procedure 1), then calls the round
procedure while the header flag `cont` is `1`, and returns the heap cursor.

The round loop keeps the outer invariant `T3OuterAt` with the potential
`t3KdelCost · t3EcongPhi + t3MiddleCost · |unembedded|` (`T3LoopInv`). Each round raises the
round counter `η` by one, and `t3Round_bound_of_unembedded` keeps `η` below `eta2Bound`, so
the loop runs at most `eta2Bound` rounds. When it stops, every edge is embedded, and
`t3_outAt_of_final` gives the output condition. The main result is `task3_meetsContract`.
-/

/-- Invariant of the round loop of `task3Body` before round `η + 1`. -/
def T3LoopInv {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (η : ℕ) (st : State) (Φ : ℕ) : Prop :=
  η ≤ eta2Bound inp.J ∧ ∃ d : T3OuterData,
    T3OuterAt ctx lay η d st (t3KdelCost impl inp.J * t3EcongPhi ctx lay st.mem) ∧
    Φ = t3KdelCost impl inp.J * t3EcongPhi ctx lay st.mem +
      t3MiddleCost impl inp.J * (unembeddedSet2Pure inp.J d.emb).card

/-- The state after the round loop: every edge is embedded. -/
def T3LoopDone {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (st : State) (_Φ : ℕ) : Prop :=
  ∃ η d, η ≤ eta2Bound inp.J ∧
    T3OuterAt ctx lay η d st (t3KdelCost impl inp.J * t3EcongPhi ctx lay st.mem) ∧
    ¬ (unembeddedSet2Pure inp.J d.emb).Nonempty

/-- Cost left for the round loop before round `η + 1`. -/
noncomputable def t3LoopRem (impl : SpannerToolImpl) (J : Graph) (η : ℕ) : ℕ :=
  (eta2Bound J - η) * (t3RoundCost impl J + 20) + 10

/-- The round loop of `task3Body`. -/
theorem t3Loop_ptriple {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (hlay : lay = T3Layout.ofCtx ctx)
    {p : Program} {selfBase dsBase : ℕ}
    (hSpec : impl.pathDS.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure impl.pathDS.params w))
    (hdrain : p.procs[selfBase + 2]? = some (t3DrainQueueBody dsBase))
    (hmidP : p.procs[selfBase + 3]? = some (t3MiddleEdgeBody dsBase (selfBase + 2)))
    (hround : p.procs[selfBase + 4]? = some (t3RoundBody dsBase (selfBase + 3))) :
    PTriple w p (T3LoopInv ctx lay 0)
      (.loop (t3Eq (t3Ld (.reg 2) (.const t3OffCont)) (.const 1)) (.call 15 (selfBase + 4) [.reg 2]))
      (pNormalPost (T3LoopDone ctx lay)) (fun _ => t3LoopRem impl inp.J 0) := by
  have hb := T3Layout.bounds ctx; dsimp only at hb; rw [← hlay] at hb; unfold t3HdrSize at hb
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12⟩ := hb
  have hw1 : 1 < 2 ^ w := ctx.hwokW.1
  have h31 : t3OffCont < 2 ^ w := by unfold t3OffCont; omega
  have h31a : inp.v2 + t3OffCont < 2 ^ w := by unfold t3OffCont; omega
  refine PTriple.loop_pot (Inv := T3LoopInv ctx lay) (m := fun η => eta2Bound inp.J - η)
    (rem := t3LoopRem impl inp.J)
    (condVal := fun st => if st.mem (inp.v2 + t3OffCont) = 1 then 1 else 0) ?_ ?_ ?_ 0
  · intro η st Φ ⟨_, d, hO, _⟩
    exact Expr.eval_eq_op (Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq hO.reg2)
      (Expr.eval_const h31) h31a)) (Expr.eval_const hw1) hw1
  · intro η st Φ ⟨hη, d, hO, _⟩ hc
    refine ⟨⟨η, d, hη, hO, fun hne => ?_⟩, ?_⟩
    · have hcont := hO.cont_eq
      rw [hb1] at hcont
      simp [hcont, hne] at hc
    · simp only [Expr.size, t3Eq, t3Ld, t3Add, t3LoopRem]; omega
  · intro η st Φ ω ⟨hη, d, hO, hΦ⟩ hc
    have hne : (unembeddedSet2Pure inp.J d.emb).Nonempty := by
      by_contra hne
      have hcont := hO.cont_eq
      rw [hb1] at hcont
      simp [hcont, hne] at hc
    have hlt := t3Round_bound_of_unembedded hne hO.geom
    obtain ⟨o, st', c, Φ', hr, ⟨ho, d1, hO1, hΦ1, -⟩, hc'⟩ :=
      t3Round_ptriple ctx lay hlay hSpec hdrain hmidP η d (startState [inp.v2] st.mem st.pos) Φ ω
        ⟨st, _, hO, rfl, by simp [startState, hb1], hne, hΦ⟩
    have hargs : evalArgs w st [.reg 2] = some [inp.v2] := by
      simp [evalArgs, Expr.eval, hO.reg2]
    refine ⟨.normal, { st' with regs := Function.update st.regs 15 o.value },
      argsSize [.reg 2] + c + 1, Φ',
      runs_call_iff.mpr ⟨[inp.v2], _, o, st', c, hargs, hround, hr, rfl, rfl, rfl⟩,
      η + 1, ⟨by omega, d1, hO1.of_mem_eq rfl (by simp [hO.reg0]) (by simp [hO.reg1])
        (by simp [hO.reg2]), hΦ1⟩, by omega, ?_⟩
    have hrem : t3LoopRem impl inp.J η =
        t3LoopRem impl inp.J (η + 1) + (t3RoundCost impl inp.J + 20) := by
      unfold t3LoopRem
      rw [show eta2Bound inp.J - η = eta2Bound inp.J - (η + 1) + 1 by omega, Nat.add_mul,
        Nat.one_mul]
      ring
    have hc2 : c + Φ' ≤ t3RoundCost impl inp.J + Φ := hc'
    rw [hrem]
    simp only [Expr.size, t3Eq, t3Ld, t3Add, argsSize]
    omega

/-- The constants of `task3Cost` pay for the setup, the first potential and all rounds. -/
lemma t3_task3Cost_le (impl : SpannerToolImpl) (J : Graph) :
    140 * J.m + 400 + t3LoopRem impl J 0 + t3MiddleCost impl J * J.m ≤ task3Cost impl J := by
  unfold t3LoopRem t3RoundCost t3MiddleCost task3Cost
  dsimp only
  set mw := Task1Input.mwCap impl J
  set X := ⌈impl.pathDS.params.K_init *
    (impl.pathDS.params.gExp (WitnessCoreInput.dWInt impl.constructExpander) mw : ℝ)⌉₊
  set A := ⌈impl.pathDS.params.K_query * (impl.pathDS.params.gQuery
      (WitnessCoreInput.dWInt impl.constructExpander) mw : ℝ)⌉₊ +
    impl.pathDS.params.gExp (WitnessCoreInput.dWInt impl.constructExpander) mw *
      (⌈impl.pathDS.params.K_del * (impl.pathDS.params.gQuery
        (WitnessCoreInput.dWInt impl.constructExpander) mw : ℝ)⌉₊ + 300)
  have h1 : (eta2Bound J - 0) * (mw * X + 228 * J.m + 300 + 20) ≤
      eta2Bound J * (mw * X + 80 * mw + 300 * J.m + 400) := by
    rw [Nat.sub_zero]; exact Nat.mul_le_mul_left _ (by omega)
  have h2 : (A + 380) * J.m + 140 * J.m ≤ J.m * (A + 600) := by nlinarith
  have h3 : ⌈impl.pathDS.params.K_query * (impl.pathDS.params.gQuery
      (WitnessCoreInput.dWInt impl.constructExpander) mw : ℝ)⌉₊ +
    impl.pathDS.params.gExp (WitnessCoreInput.dWInt impl.constructExpander) mw *
      (⌈impl.pathDS.params.K_del * (impl.pathDS.params.gQuery
        (WitnessCoreInput.dWInt impl.constructExpander) mw : ℝ)⌉₊ + 300) + 600 = A + 600 := rfl
  omega

/-- A run of `task3Body` from a valid input ends with the output condition, within
`task3Cost`. -/
theorem task3Body_runs {w : ℕ} {p : Program} {impl : SpannerToolImpl} {selfBase dsBase : ℕ}
    (hprog : p.HasAt selfBase (task3Module impl.constructExpander.phiNum
      impl.constructExpander.phiDen selfBase dsBase))
    (hSpec : impl.pathDS.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure impl.pathDS.params w))
    (inp : Task3Input) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) (hv : inp.Valid impl mem w) :
    ∃ o st' c,
      Runs w p ω (task3Body impl.constructExpander.phiNum impl.constructExpander.phiDen selfBase)
        (startState [inp.jAddr, inp.t1OutAddr, inp.v2] mem pos) o st' c ∧
      Task3OutAt impl inp mem st'.mem o.value w ∧ c ≤ task3Cost impl inp.J := by
  let ctx := t3CtxOfValid hv
  let lay := T3Layout.ofCtx ctx
  have hb := T3Layout.bounds ctx; dsimp only at hb; unfold t3HdrSize at hb
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12⟩ := hb
  have hdrain : p.procs[selfBase + 2]? = some (t3DrainQueueBody dsBase) := by
    simpa [task3Module] using hprog.get (i := 2) (by dsimp [task3Module]; decide)
  have hmidP : p.procs[selfBase + 3]? = some (t3MiddleEdgeBody dsBase (selfBase + 2)) := by
    simpa [task3Module] using hprog.get (i := 3) (by dsimp [task3Module]; decide)
  have hround : p.procs[selfBase + 4]? = some (t3RoundBody dsBase (selfBase + 3)) := by
    simpa [task3Module] using hprog.get (i := 4) (by dsimp [task3Module]; decide)
  have hcost := t3_task3Cost_le impl inp.J
  obtain ⟨o, stF, c, Φ', hr, hq, hc⟩ := t3Setup_cps (ω := ω) (Q := fun o st _ =>
      Task3OutAt impl inp mem st.mem o.value w) ctx lay rfl selfBase dsBase
    impl.constructExpander.phiNum impl.constructExpander.phiDen hprog rfl rfl mem
    (fun i => [inp.jAddr, inp.t1OutAddr, inp.v2].getD i 0) pos 0 (task3Cost impl inp.J)
    (fun _ _ => rfl) ctx.hz2 rfl rfl rfl (fun st₁ ⟨d, hO⟩ => by
      have hE : t3KdelCost impl inp.J * t3EcongPhi ctx lay st₁.mem = 0 := hO.phi_eq.symm
      have hUle : t3MiddleCost impl inp.J * (unembeddedSet2Pure inp.J d.emb).card ≤
          t3MiddleCost impl inp.J * inp.J.m := by
        refine Nat.mul_le_mul_left _ ?_
        exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
      refine t3_frame_cps (F := 0)
        (Φa := t3MiddleCost impl inp.J * (unembeddedSet2Pure inp.J d.emb).card)
        (T := task3Cost impl inp.J - t3MiddleCost impl inp.J * (unembeddedSet2Pure inp.J d.emb).card)
        (t3Loop_ptriple ctx lay rfl hSpec hdrain hmidP hround)
        ⟨Nat.zero_le _, d, by rw [hE]; exact hO, by rw [hE, Nat.zero_add]⟩ (le_refl _)
        (by omega) ?_
      intro st₂ Φ₂ ⟨η, d2, hη, hO2, hU2⟩
      obtain ⟨mem2, regs2, pos2⟩ := st₂
      have h5 : inp.v2 + t3OffHCur < 2 ^ w := by rw [← hb1]; unfold t3OffHCur; omega
      refine t3_end_ret_cps (v := d2.hCur) (Φ' := 0)
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hO2.reg2)
          (Expr.eval_const (k := t3OffHCur) (lt_of_le_of_lt (Nat.le_add_left _ _) h5)) h5)
          (by rw [← hb1]; exact hO2.hCur_eq))
        (t3_outAt_of_final ctx lay rfl hO2 hη hU2) ?_
      simp only [Expr.size, t3Ld, t3Add]
      omega)
  exact ⟨o, stF, c, hr, hq, by omega⟩

/-- `task3Module` meets `task3Contract`. -/
theorem task3_meetsContract {w : ℕ} {p : Program} {impl : SpannerToolImpl} {selfBase dsBase : ℕ}
    (hprog : p.HasAt selfBase (task3Module impl.constructExpander.phiNum
      impl.constructExpander.phiDen selfBase dsBase))
    (hSpec : impl.pathDS.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure impl.pathDS.params w)) :
    MeetsContract w p selfBase (task3Contract impl w) := by
  intro args mem pos ω _ hpre
  rcases hpre with ⟨inp₀, rfl, hv₀⟩
  have hbody : p.procs[selfBase]? = some (task3Body impl.constructExpander.phiNum
      impl.constructExpander.phiDen selfBase) := by
    simpa [task3Module] using hprog.get (i := 0) (by dsimp [task3Module]; decide)
  obtain ⟨o, st', c, hr, hout, hc⟩ := task3Body_runs hprog hSpec inp₀ mem pos ω hv₀
  refine ⟨_, hbody, o, st', c, hr, ?_, ?_⟩
  · -- The run is unique, so the output condition holds for every valid input with these
    -- arguments.
    intro inp' hargs' hv'
    obtain ⟨o', st'', c', hr', hout', -⟩ := task3Body_runs hprog hSpec inp' mem pos ω hv'
    rw [← hargs'] at hr'
    obtain ⟨ho, hst, -⟩ := Runs.det hr hr'
    rw [ho, hst]
    exact hout'
  · have h_ex : ∃ inp : Task3Input,
        [inp₀.jAddr, inp₀.t1OutAddr, inp₀.v2] = [inp.jAddr, inp.t1OutAddr, inp.v2] ∧
        inp.Valid impl mem w := ⟨inp₀, rfl, hv₀⟩
    dsimp only [task3Contract]
    simp only [h_ex, ↓reduceDIte]
    obtain ⟨hargs, hvc⟩ := Classical.choose_spec h_ex
    have hj : inp₀.jAddr = (Classical.choose h_ex).jAddr := (List.cons_eq_cons.mp hargs).1
    have hJ : inp₀.J = (Classical.choose h_ex).J := by
      have g1 := graphAt_iff_readGraph.mp hv₀.2.1
      have g2 := graphAt_iff_readGraph.mp hvc.2.1
      rw [← g1, ← g2]
      exact congrArg (readGraph mem) hj
    rw [← hJ]
    exact hc

end MinCostFlow.Spanner
